/* 
    Copyright 2018, Peter Brooksbank, Joshua Maglione, James B. Wilson.
    Distributed under GNU GPLv3.
*/

__der_densor := function(s) 
  // Step 1: Remove radicals. 
  printf "Removing the radicals.\n";
  R2 := Radical(s, 2);
  printf "\tdim(Rad_V) = %o\n", Dimension(R2);
  C2 := Complement(Domain(s)[1], R2);
  T2 := Matrix(Basis(C2) cat Basis(R2));
  C0 := Image(s);
  R0 := Complement(Codomain(s), C0);
  printf "\tdim(Rad_W) = %o\n", Dimension(R0);
  T0 := Matrix(Basis(C0) cat Basis(R0));
  F := SystemOfForms(s);
  Forms := [T2*X*Transpose(T2) : X in F];
  Forms := [&+[T0[i][j]*Forms[i] : i in [1..#Forms]] : j in [1..#Forms]];
  t := Tensor(Forms, 2, 1, s`Cat);

  // Step 2: Get the densor subspace.
  printf "Computing derivation algebra.\n";
  D := DerivationAlgebra(t);
  printf "\tdim(Der) = %o\n", Dimension(D);
  if Dimension(D) eq 2 then
    printf "Trivial derivation algebra. Aborting.\n";
    return 0;
  end if;
  D_V := Induce(D, 2);
  D_W := Induce(D, 0);
  printf "Computing the densor subspace.\n";
  densor := DerivationClosure(Parent(t), t);
  printf "\tdim(densor) = %o\n", Dimension(densor);

  // Step 3a: Check derivation algebra.
  R := SolvableRadical(D_W); // guaranteed dim >= 1.
  SS := D_W/R;
  try
    type := SemisimpleType(SS);
  catch err
    printf "Cannot recognize the semi-simple structure of derivation algebra. ";
    printf "Aborting.\n";
    return 0;
  end try;
  if not IsSimple(SS) then
    printf "Semi-simple part is not simple. Code not implemented. Aborting.\n";
    return 0;
  end if;

  // Step 3b: Pre-condition D_W for normalizer computation. 

  // Step 3c: Get the derivation normalizer.

  // Step 4: Compute stabilizer of densor space.

  return 0;
end function;

// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//                                  Intrinsics
// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

intrinsic DDAutotopismGroup( t::TenSpcElt ) -> GrpMat
{Given an alternating tensor t, apply the derivation-densor method to compute 
  the autotopism group of t.}
  require ISA(Type(BaseRing(t)), FldFin) : 
    "Base ring of tensor must be a finite field.";
  require IsAlternating(t) : "Tensor must be alternating.";
  Cat := TensorCategory([1, 1, 1], {{2, 1}, {0}});
  if TensorCategory(t) ne Cat then
    t := ChangeTensorCategory(t, Cat);
  end if;
  return __der_densor(t);
end intrinsic;

intrinsic DDAutomorphismGroup( G::GrpPC ) -> GrpAuto
{Given a class 2, exponent p p-group G, apply the derivation-densor method to
   compute the automorphism group of G.}
  require IsPrimePower(#G) : "Group must be a p-group.";
  require IsPrime(Exponent(G)) : "Group must have exponent p.";
  require NilpotencyClass(G) eq 2 : "Group must be class 2.";
  t, maps := pCentralTensor(G);
  Aut := __der_densor(t);
  return Aut;
end intrinsic;
