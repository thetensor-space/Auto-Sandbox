/* 
    Copyright 2018, Peter Brooksbank, Joshua Maglione, James B. Wilson.
    Distributed under GNU GPLv3.
*/

import "isom-test.m" : __IsIsometric_ND;


__der_densor := function(s) 
  // Step 1: Remove radicals. 
  printf "Removing the radicals.\n";
  R := [*r : r in Radical(s)*];
  printf "\tdim(Rad_U) = %o\n", Dimension(R[1]);
  printf "\tdim(Rad_V) = %o\n", Dimension(R[2]);
  C := [*Complement(Domain(s)[i], R[i]) : i in [1..2]*];
  T := [*Matrix(Basis(C[i]) cat Basis(R[i])) : i in [1..2]*];
  C cat:= [*Image(s)*];
  R cat:= [*Complement(Codomain(s), C[3])*];
  printf "\tdim(Rad_W) = %o\n", Dimension(R[3]);
  T cat:= [*Matrix(Basis(C[3]) cat Basis(R[3]))*];
  F := SystemOfForms(s);
  if &or[Dimension(r) gt 0 : r in R] then
    Forms := [T[1]*X*Transpose(T[2]) : X in F];
    Forms := [&+[T[3][i][j]*Forms[i] : i in [1..#Forms]] : j in [1..#Forms]];
    Forms := [ExtractBlock(X, 1, 1, Dimension(C[1]), Dimension(C[2])) : 
      X in Forms][1..Dimension(C[3])];
    t := Tensor(Forms, 2, 1, s`Cat);
  else
    t := s; // This keeps all the previous calculations saved.
  end if;
  K := BaseRing(t);

  // Step 2: Get the densor subspace.
  printf "Computing derivation algebra.\n";
  D := DerivationAlgebra(t);
  printf "\tdim(Der) = %o\n", Dimension(D);
  if Dimension(D) eq 2 then
    printf "Trivial derivation algebra. Aborting.\n";
    return 0;
  end if;
  printf "Computing the densor subspace.\n";
  densor := UniversalDensorSubspace(t); // MAIN BOTTLENECK
  printf "\tdim(densor) = %o\n", Dimension(densor);

  // Step 3a: Get derivation algebra only on relevant coordinates.
  rp := RepeatPartition(TensorCategory(t));
  if rp ne {{0}, {1}, {2}} then
    dims := [];
    indices := [];
    for S in rp do
      m := Maximum(S);
      Append(~dims, Dimension(Frame(t)[3-m]));
      Append(~indices, 3-m);
    end for;
    projs := [**];
    for i in indices do
      _, pi := Induce(D, 3-i);
      Append(~projs, pi);
    end for;
    Sort(~indices);
    D := sub< MatrixLieAlgebra(K, &+(dims)) | 
      [DiagonalJoin(<X @ pi : pi in projs>) : X in Generators(D)] >;
  else 
    indices := [1..3];
  end if;

  // Step 3b: Check derivation algebra.
  R := SolvableRadical(D); 
  SS := D/R;
  if Dimension(SS) eq 0 then
    printf "Solvable Lie algebra. ";
    printf "Code for this case hasn't been implemented yet. Aborting.\n";
    return 0;
  end if;
  try
    type := SemisimpleType(SS);
  catch err
    printf "Cannot recognize the semi-simple structure of derivation algebra.";
    printf "Aborting.\n";
    return 0;
  end try;

  printf "Computing a Chevalley basis.\n";
  try
    E, F, H := ChevalleyBasis(D);
  catch err
    printf "Something happened when computing a Chevalley basis.\n";
    printf "Here is the error:\n%o\n", err`Object;
    return 0;
  end try;

  printf "Computing the Levi decomposition.\n";
  try
    hasLevi, L := HasLeviSubalgebra(D);
    if not hasLevi then
      printf "Cannot find a Levi decomposition. Aborting.\n";
      return 0;
    end if;
  catch err
    printf "Something happened when constructing a Levi decomposition.\n";
    printf "Here is the error:\n%o\n", err`Object;
    return 0;
  end try;

  // Step 3c: Get the derivation normalizer.
  if {2, 1} notin rp and {2, 1, 0} notin rp then
    printf "Code only works for tensors with frame U2 x U2 >-> U0. Aborting.\n";
    return 0;
  end if;
  printf "Computing the normalizer of the derivation algebra.\n";
  printf "==== Output from SimilaritiesOfSimpleLieModule ";
  printf "================================\n";
  N := SimilaritiesOfSemisimpleLieModule(L, Dimension(Domain(t)[1]) : 
    E := E, F := F, H := H);
  printf &cat["=" : i in [1..79]] cat "\n";
  N`DerivedFrom := <t, indices>; // enables application of 'Induce'. 
  projs := [**];
  for i in Reverse([0..2]) do
    _, pi := Induce(N, i);
    Append(~projs, pi);
  end for;

  // Step 4a: If densor is 1-dimensional, we're done!
  if Dimension(densor) eq 1 then
    printf "Lifting derivation normalizer to autotopisms.\n";
    gens := [];
    assert exists(ind){k : k in [1..#Eltseq(t)] | IsInvertible(k)};
    for X in Generators(N) do
      Forms := [(X @ projs[1])*F*Transpose(X @ projs[2]) : 
        F in SystemOfForms(t)];
      Forms := [&+[(X @ projs[3])[i][j]*F[i] : i in [1..#Forms]] : 
        j in [1..#Forms]];
      t_X := Tensor(Forms, 2, 1, t`Cat);
      k := Eltseq(t_X)[ind]^-1*Eltseq(t)[ind]^-1;
      Append(gens, <X @ projs[1], X @ projs[2], k*Matrix(X @ projs[3])>);
    end for;
  else
    printf "Densor is not 1-dimenisonal; code is not yet implemented. ";
    printf "Aborting.\n";
    return 0;

    // Step 4b: Get action of N on the densor. 

    // Step 5: Compute stabilizer of densor space.

  end if;

  // Step 6: Include isometries. (These might already be include???)
  printf "Constructing the isometry group.\n";
  try
    I := IsometryGroup(SystemOfForms(t) : DisplayStructure := false); 
    isom := [<X, X, GL(t`Codomain)!1> : X in Generators(I)];
  catch err
    I := PrincipalIsotopismGroup(t);
    projs := [];
    for i in [1..3] do
      _, pi := Induce(I, 3-i);
      Append(~projs, pi);
    end for;
    isom := [<X @ projs[i] : i in [1..3]> : X in Generators(I)];
  end try;

  // Step 7: Deal with any radicals.
  if &or[Dimension(r) gt 0 : r in R] then
    rads := [<DiagonalJoin(GL(C[1])!1, x)*T[1]^-1, GL(s`Domain[2]), 
      GL(s`Codomain)!1> : x in Generators(GL(R[1]))];
    rads cat:= [<GL(s`Domain[1]), DiagonalJoin(GL(C[2])!1, x)*T[2]^-1,
      GL(s`Codomain)!1> : x in Generators(GL(R[2]))];
    rads cat:= [<GL(s`Domain[1])!1, GL(s`Domain[2])!1, 
      T[3]^-1*DiagonalJoin(GL(C[3])!1, x)> : x in Generators(GL(R[3]))]; 
    gens := [<DiagonalJoin(x[1], GL(R[1])!1)*T[1]^-1, 
      DiagonalJoin(x[2], GL(R[2])!1)*T[2]^-1, 
      T[3]^-1*DiagonalJoin(x[3], GL(R[3])!1)> : x in gens];
    isom := [<DiagonalJoin(x[1], GL(R[1])!1)*T[1]^-1, 
      DiagonalJoin(x[2], GL(R[2])!1)*T[2]^-1, 
      T[3]^-1*DiagonalJoin(x[3], GL(R[3])!1)> : x in isom];
    unip := []; // ADD THESE
    printf "WARNING: Unipotent not added yet.";
    pi_gens := gens cat isom cat rads;
  else
    pi_gens := gens cat isom;
  end if;

  // Step 8: Put everything together
  over_grp := GL(&+[Degree(pi_gens[1][i]) : i in [1..3]], K);
  pseudo_isom := sub< over_grp | [DiagonalJoin(x) : x in pi_gens] >;
  pseudo_isom`DerivedFrom := <s, [1..3]>;

  // Sanity check
  printf "Sanity check.\n";
  for i in [1..10] do
    X := Random(pseudo_isom);
    _, pi2 := Induce(pseudo_isom, 2);
    _, pi1 := Induce(pseudo_isom, 1);
    _, pi0 := Induce(pseudo_isom, 0);
    if not IsHomotopism(s, s, [*X @ pi2, X @ pi1, X @ pi0*]) then
      printf "\tWARNING: did not pass sanity test! Something is wrong.\n";
      break;
    end if;
  end for;

  return pseudo_isom;
end function;

// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//                                  Intrinsics
// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

intrinsic DDAutotopismGroup( t::TenSpcElt ) -> GrpMat
{Given a tensor t, apply the derivation-densor method to compute the autotopism
  group of t.}
  require ISA(Type(BaseRing(t)), FldFin) : 
    "Base ring of tensor must be a finite field.";
  return __der_densor(t);
end intrinsic;

intrinsic DDAutoclinismGroup( G::GrpPC ) -> GrpAuto
{Given a class 2, exponent p p-group G, apply the derivation-densor method to
   compute the automorphism group of G.}
  require IsPrimePower(#G) : "Group must be a p-group.";
  require NilpotencyClass(G) eq 2 : "Group must be class 2.";
  t, maps := pCentralTensor(G);
  Aut := __der_densor(t);
  return Aut;
end intrinsic;
