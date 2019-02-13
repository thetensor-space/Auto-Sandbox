__der_densor := function(s) 

  // Step 1: Remove radicals. 
  t := FullyNondegenerateTensor(s);
  if [Dimension(X) : X in Frame(s)] ne [Dimension(X) : X in Frame(t)] then
    printf "Nontrivial radical. Need a fix from James, but continuing with the";
    printf " nondegenerate part.\n";
  else
    t := s;
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

  // Get PARTITION for Pete
  partition := RepeatPartition(TensorCategory(t));
  v := Valence(t);
  // James' data structure fix would improve this...
  dims_rep := []; 
  for a in Reverse([0..v-1]) do
    assert exists(S){S : S in partition | a in S};
    if a eq Maximum(S) then
      Append(~dims_rep, Dimension(Frame(t)[v-a]));
    end if;
  end for;

  // Step 3: Check derivation algebra.
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
  assert Degree(L) eq &+(dims_rep); // Got the correct dimensions of blocks.
  // TODO: eventually check that the part outside the Levi is harmless.


  // Step 4: Construct the normalizer.
  printf "Computing the normalizer of the derivation algebra.\n";
  printf "==== Output from GLNormalizer ";
  printf "================================\n";
  old_verb := GetVerbose("MatrixAlgebras");
  SetVerbose("MatrixAlgebras", 1);
  N := GLNormalizer(L : PARTITION := dims_rep);
  SetVerbose("MatrixAlgebras", old_verb);
  printf &cat["=" : i in [1..79]] cat "\n";
  // Gives us a way to break up block structure easily
  DerivedFrom(~N, t, {0..2}, {Maximum(S) : S in partition}); 
  projs := [**];
  for a in Reverse([0..2]) do
    pi := Induce(N, a);
    Append(~projs, pi);
  end for;


  if Dimension(densor) eq 1 then

    // Step 5a: If densor is 1-dimensional, we're done!
    printf "Lifting derivation normalizer to autotopisms.\n";
    gens := [];
    assert exists(ind){k : k in [1..#Eltseq(t)] | IsInvertible(Eltseq(t)[k])};
    for X in Generators(N) do
      Forms := [(X @ projs[1])^-1*F*Transpose(X @ projs[2])^-1 : 
        F in SystemOfForms(t)];
      Forms := [&+[(X @ projs[3])[i][j]*Forms[i] : i in [1..#Forms]] : 
        j in [1..#Forms]];
      t_X := Tensor(Forms, 2, 1, t`Cat);
      k := Eltseq(t_X)[ind]^-1*Eltseq(t)[ind]^-1;
      assert t eq k*t_X; // slow
      Append(~gens, <X @ projs[1], X @ projs[2], k*Matrix(X @ projs[3])>);
    end for;

  else

    // Step 5b: Get action of N on the densor. 
    printf "Constructing the action of the normalizer on the densor.\n";
    gens_N := [x : x in Generators(N)];
    gens_action := [];
    V := densor`Mod;
    for X in gens_N do
      mat := [];
      for b in Basis(V) do
        Forms := [(X @ projs[1])^-1*F*Transpose(X @ projs[2])^-1 : 
          F in SystemOfForms(densor!Eltseq(b @ densor`UniMap))];
        Forms := [&+[(X @ projs[3])[i][j]*Forms[i] : i in [1..#Forms]] : 
          j in [1..#Forms]];
        b_X := Tensor(Forms, 2, 1, t`Cat);
        Append(~mat, Coordinates(V, V!Eltseq(b_X)));
      end for;
      Append(~gens_action, Matrix(mat));
    end for;
    N_action := sub< GL(Dimension(densor), K) | gens_action >;

    // Step 5c: Compute stabilizer of densor space.
    printf "Computing the stabilizer of the tensor in the densor.\n";
    t_vector := VectorSpace(K, Dimension(densor))!Coordinates(V, V!Eltseq(t));
    St := Stabilizer(N_action, t_vector);
    phi := hom< N -> N_action | [<gens_N[i], gens_action[i]> : 
      i in [1..#gens_N]] >;
    Stab := St @@ phi;
    gens := [<X @ projs[1], X @ projs[2], X @ projs[3]> : 
      X in Generators(Stab)];

  end if;


  // Step 6: Include isometries. (These might already be included???)
/*  printf "Constructing the isometry group.\n";
  try
    I := IsometryGroup(SystemOfForms(t) : DisplayStructure := false); 
    isom := [<X, X, GL(t`Codomain)!1> : X in Generators(I)];
  catch err
    I := PrincipalIsotopismGroup(t);
    projs := [];
    for i in [1..3] do
      pi := Induce(I, 3-i);
      Append(~projs, pi);
    end for;
    isom := [<X @ projs[i] : i in [1..3]> : X in Generators(I)];
  end try;*/
  isom := [];


  // Step 7: Deal with any radicals. James will fix this with HOF
/*  if &or[Dimension(r) gt 0 : r in R] then
    Id := [*IdentityMatrix(K, Dimension(C[i])) : i in [1..3]*];
    rads :=[];
    if Dimension(R[1]) gt 0 then
      rads cat:= [<DiagonalJoin(Id[1], x)*T[1]^-1, GL(s`Domain[2]), 
        GL(s`Codomain)!1> : x in Generators(GL(R[1]))];
    end if;
    if Dimension(R[2]) gt 0 then
      rads cat:= [<GL(s`Domain[1]), DiagonalJoin(Id[2], x)*T[2]^-1,
        GL(s`Codomain)!1> : x in Generators(GL(R[2]))];
    end if;
    if Dimension(R[3]) gt 0 then
      rads cat:= [<GL(s`Domain[1])!1, GL(s`Domain[2])!1, 
        T[3]^-1*DiagonalJoin(GL(C[3])!1, x)> : x in Generators(GL(R[3]))]; 
    end if;
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
  end if;*/
  pi_gens := gens cat isom;


  // Step 8: Put everything together
  over_grp := GL(&+[Nrows(pi_gens[1][i]) : i in [1..3]], K);
  pseudo_isom := sub< over_grp | [DiagonalJoin(x) : x in pi_gens] >;
  DerivedFrom(~pseudo_isom, s, {0..2}, {0..2} : Fused := false);


  // Sanity check
  printf "Sanity check.\n";
  Forms := SystemOfForms(t);
  for i in [1..10] do
    X := Random(pseudo_isom);
    pi2 := Induce(pseudo_isom, 2);
    pi1 := Induce(pseudo_isom, 1);
    pi0 := Induce(pseudo_isom, 0);
    assert [(X @ pi2)*F*Transpose(X @ pi1) : F in Forms] eq 
        [&+[(X @ pi0)[i][j]*Forms[i] : i in [1..#Forms]] : j in [1..#Forms]];
    //if not IsHomotopism(t, t, [*X @ pi2, X @ pi1, X @ pi0*]) then
    //  printf "\tWARNING: did not pass sanity test! Something is wrong.\n";
    //  break;
    //end if;
  end for;

  return pseudo_isom;
end function;
