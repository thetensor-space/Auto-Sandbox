/* 
    Copyright 2018--2019 Peter Brooksbank, Joshua Maglione, James B. Wilson.
    Distributed under GNU GPLv3.
*/

/* 
  Given the densor and the repeat paritition, the function returns BoolElt and
  sometimes SetEnum{RngIntElt}. True means to just write down the autotopism 
  group from the normalizer by scaling some coordinate(s), given by the returned
  set. False just means to return through Magma's stabilizer computation.

  There doesn't seem to be a way to adjust by a scalar on a set of fused coords
  containing 0, that isn't just {0} itself. So at the start, we remove the set
  containing 0. If there are no other sets in repeats, return false.

  We are checking the following things.
    1. If dimension of densor is greater than 1, then do stabilizer comp.
    2. If there exists {a} in repeats, then write the fix on that coordinate.
    3. If there S in repeats with gcd(#S, K^\times) = 1, then we can construct
       #S-roots, so we can fix the scalars.
    4. Otherwise, do stabilizer comp.
*/
__decision_time := function(densor, repeats)
  assert exists(S){S : S in repeats | 0 in S};
  if #S ne 1 then
    Exclude(~repeats, S);
  end if;
  
  if Dimension(densor) gt 1 or #repeats eq 0 then 
    return false, _;
  end if;

  ord_by_size := [PowerSet(PowerSet(IntegerRing())) | {} : k in 
      [1..Maximum([#S : S in repeats])]];
  for S in repeats do
    ord_by_size[#S] join:= {S};
  end for;

  if #ord_by_size[1] gt 0 then
    return true, Random(ord_by_size[1]);
  end if;

  K := BaseRing(densor);
  unit_grp_ord := #K-1;
  needed_roots := {i : i in [1..#ord_by_size] | #ord_by_size[i] gt 0};
  if exists(k){k : k in needed_roots | GCD(k, unit_grp_ord) eq 1} then
    return true, Random(ord_by_size[k]);    
  else
    return false, _;
  end if;
end function;


// Constructs an nth root of a in K
__nth_root := function(K, n, a)
  P<x> := PolynomialRing(K);
  f := x^n - a;
  fact := Factorization(f);
  assert exists(T){t : t in fact | Degree(t[1]) eq 1};
  root := -Evaluate(T[1], 0);
  assert K!(root^n) eq K!a;
  return root;
end function;


__der_densor := function(s) 
  K := BaseRing(s);
  v := Valence(s);

  // Remove radicals. Once we integrate James' code, we'll remove this.
  t := FullyNondegenerateTensor(s);
  if [Dimension(X) : X in Frame(s)] ne [Dimension(X) : X in Frame(t)] then
    printf "Nontrivial radical. Need a fix from James, but continuing with the";
    printf " nondegenerate part.\n";
  else
    t := s;
  end if;

  // Stop if anything is trivial already
  if exists{X : X in Frame(t) | Dimension(X) eq 0} then
    printf "Tensor is 0-dimensional and should be handled completely by the radical fix.\n";
    return false;
  end if;


  // Construct the derivation algebra first.
  printf "Computing derivation algebra.\n";
  D := DerivationAlgebra(t);
  printf "\tdim(Der) = %o\n", Dimension(D);


  // The derivation algebra is trivial... do something else.   
  if forall{a : a in [0..v-1] | forall{X : X in 
      Generators(Codomain(Induce(D, a))) | IsScalar(X)}} then
    printf "Trivial derivation algebra. Aborting.\nThis is not an error.\n";
    return false;
  end if;


  // Construct the densor subspace
  printf "Computing the densor subspace.\n";
  densor := DerivationClosure(Parent(t), t); // MAIN BOTTLENECK
  printf "\tdim(densor) = %o\n", Dimension(densor);


  // Write down partition for GLNormalizer
  coords_rep := D`DerivedFrom`RepCoords;
  Fr := Frame(t);
  dims_rep := [Dimension(Fr[i]) : i in Sort([v-a : a in coords_rep])];


  // Check derivation algebra.
  printf "Computing the Levi decomposition.\n";
  try
    hasLevi, L := HasLeviSubalgebra(D);
    if not hasLevi then
      printf "Cannot find a Levi decomposition. Aborting.\n;";
      printf "HasLeviSubalgebra returned false.\n";
      return false;
    end if;
  catch err
    printf "Something happened when constructing a Levi decomposition.\n";
    printf "\n==== Error Printout ";
    printf "===========================================================\n";
    printf "%o%o", err`Position, err`Object;
    printf &cat["=" : i in [1..79]] cat "\n\n";
    return false;
  end try;

  // Abort if the Levi is trivial.
  if Dimension(L) eq 0 then
    printf "The Levi subalgebra is trivial, so there's nothing to do here.\n";
    return false;
  end if;
  
  // Got the correct dimensions of blocks.
  assert Degree(L) eq &+(dims_rep); 

  // Display Levi info
  printf "\tdim(Levi) = %o\n", Dimension(L);
  try
    printf "Levi semisimple type: %o\n", SemisimpleType(L);
  catch err
    "Could not determine the semisimple structure of Levi.";
    "Here is the error:";
    printf "\n==== Error Printout ";
    printf "===========================================================\n";
    printf "%o%o", err`Position, err`Object;
    printf &cat["=" : i in [1..79]] cat "\n\n";
  end try;


  // Construct the normalizer.
  printf "Computing the normalizer of the derivation algebra.\n";
  printf "\tPARTITION : %o\n", dims_rep;
  printf "\n==== Output from GLNormalizer ";
  printf "=================================================\n";
  old_verb := GetVerbose("MatrixAlgebras");
  SetVerbose("MatrixAlgebras", 1);
  N := GLNormalizer(L : PARTITION := dims_rep);
  SetVerbose("MatrixAlgebras", old_verb);
  printf &cat["=" : i in [1..79]] cat "\n\n";

  if Type(N) eq BoolElt then
    printf "GLNormalizer returned false.\n";
    return false;
  end if; 

  // Gives us a way to break up block structure easily via 'Induce'
  DerivedFrom(~N, t, {0..v-1}, coords_rep); 
  projs := [*Induce(N, a) : a in [v-1..0 by -1]*];


  // Decide how to proceed
  // Added in later: if N does not normalize the solvable radical, then the 
  // autotopism group is strictly smaller than the normalizer. 
  R := SolvableRadical(D);
  if exists{X : X in Generators(R) | exists{Y : Y in Generators(N) | 
      not IsCoercible(R, X^Y)}} then
    // The radical is not normalized 
    printf "The radical of Der is not normalized. Unsure how to proceed.\n";
    return false;
  end if;

  // In this case, the radical is normalized
  fused := RepeatPartition(TensorCategory(t));
  write_it, S := __decision_time(densor, fused);
  AntiChmtp := TensorCategory([-1 : a in [1..v-1]] cat [1], fused);

  if write_it then

    // Write down the autotopism group straight from the generators of N(Der).
    printf "Lifting derivation normalizer to autotopisms.\n";
    gens := [];
    assert exists(non_zero_ind){k : k in [1..#Eltseq(t)] | Eltseq(t)[k] ne 0};

    for X in Generators(N) do

      // Find the scalar that we are off by 
      Maps_X := [*(X @ projs[i])^-1 : i in [1..v-1]*] cat [*X @ projs[v]*]; 
      H_X := Homotopism(Maps_X, AntiChmtp);
      t_X := t @ H_X; 
      k := Eltseq(t)[non_zero_ind]^-1 * Eltseq(t_X)[non_zero_ind];
      if k*t ne t_X then
        printf "Expected tensors to be scalar multiples, but they are not.\n";
        printf "Please report this bug to your local authorities.\n";
        return false;
      end if;

      // Scale one map by k^-1 or #S maps by the inverse of the #S-root of k.
      if #S eq 1 then
        a := Random(S);
        Maps_X[v-a] := k^-1*Matrix(Maps_X[v-a]);
      else
        for a in S do
          Maps_X[v-a] := __nth_root(K, #S, k)^-1*Matrix(Maps_X[v-a]);
        end for;
      end if;

      Append(~gens, <Y^-1 : Y in Maps_X[1..v-1]> cat <Maps_X[v]>);

    end for;

  else

    // Get action of N(Der) on the densor. 
    printf "Constructing the action of the normalizer on the densor.\n";
    gens_N := [x : x in Generators(N)];
    gens_action := [];
    V := densor`Mod;

    for X in gens_N do
      mat := [];
      for b in Basis(densor) do
        Maps_X := [*(X @ projs[i])^-1 : i in [1..v-1]*] cat [*X @ projs[v]*];
        H_X := Homotopism(Maps_X, AntiChmtp);
        b_X := b @ H_X;
        if b_X notin densor then
          printf "Expected the tensor to be contained in the densor subspace.\n";
          printf "Please report this bug to your local authorities.\n";
          return false;
        end if;
        /*Forms := [(X @ projs[1])^-1*F*Transpose(X @ projs[2])^-1 : 
          F in SystemOfForms(densor!Eltseq(b @ densor`UniMap))];
        Forms := [&+[(X @ projs[3])[i][j]*Forms[i] : i in [1..#Forms]] : 
          j in [1..#Forms]];
        b_X := Tensor(Forms, 2, 1, t`Cat);*/
        Append(~mat, Coordinates(V, V!Eltseq(b_X)));
      end for;
      Append(~gens_action, Matrix(mat));
    end for;

    N_action := sub< GL(Dimension(densor), K) | gens_action >;


    // Compute stabilizer of the tensor
    printf "Computing the stabilizer of the tensor in the densor.\n";
    t_vector := VectorSpace(K, Dimension(densor))!Coordinates(V, V!Eltseq(t));
    St := Stabilizer(N_action, t_vector);
    phi := hom< N -> Generic(N_action) | [<gens_N[i], gens_action[i]> : 
      i in [1..#gens_N]] >;
    Stab := St @@ phi;
    gens := [<X @ projs[1], X @ projs[2], X @ projs[3]> : 
      X in Generators(Stab)];

  end if;


  // Trim the gens down by fused
  not_reps := {@a : a in [v-1..0 by -1] | exists{S : S in fused | a in S and
      a ne Maximum(S)}@};
  reps := IndexedSet([v-1..0 by -1]) diff not_reps;
  reps := Sort([v-a : a in reps]);
  gens_trim := [DiagonalJoin(<T[i] : i in reps>) : T in gens];  


  // Put everything together
  over_grp := GL(Nrows(gens_trim[1]), K);
  autotop := sub< over_grp | gens_trim >;
  DerivedFrom(~autotop, t, D`DerivedFrom`Coords, D`DerivedFrom`RepCoords);


  // Sanity check
  printf "Sanity check.\n";
  projs := [*Induce(autotop, a) : a in [v-1..0 by -1]*];
  for X in Generators(autotop) do 
    if not IsHomotopism(t, t, [*X @ pi : pi in projs*], HomotopismCategory(v)) then
      printf "Expected maps to induce a homotopism, but they did not.\n";
      printf "Please report this bug to your local authorities.\n";
      return false;
    end if;
  end for;


  return autotop;
end function;

// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//                                  Intrinsics
// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

intrinsic DDAutotopismGroup( t::TenSpcElt ) -> GrpMat
{Given a tensor t, apply the derivation-densor method to compute the autotopism 
group of t.}
  require ISA(Type(BaseRing(t)), FldFin) : 
      "Base ring of tensor must be a finite field.";
  require Valence(t) eq 3 : 
      "Densor computations require 3-tensors at the moment.";
  return __der_densor(t);
end intrinsic;

intrinsic DDAutoclinismGroup( G::GrpPC ) -> GrpAuto
{Given a class 2 p-group G, apply the derivation-densor method to compute the 
automorphism group of G.}
  require IsPrimePower(#G) : "Group must be a p-group.";
  require NilpotencyClass(G) eq 2 : "Group must be class 2.";
  require IsOdd(#G) : "Group must have odd order.";
  t, maps := pCentralTensor(G);
  Aut := __der_densor(t);
  return Aut;
end intrinsic;
