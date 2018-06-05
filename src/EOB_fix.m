/* 
  Responding to a request by Eamonn, here is a temporary fix 
  to handle groups that produce degenerate tensors. This needs
  to be systematically incorporated into the main function at
  some stage. (PAB on 10/26/2017)
*/

MyPseudoIsometryGroup := function (T)
  
  K := BaseRing (T);
  R := Radical (T);
  assert #R eq 2;
  assert R[1] eq R[2];   // assuming T is alternating (or symmetric)
  if Dimension (R[1]) eq 0 then
      return PseudoIsometryGroup (T);
  end if;
  
  // if T has a radical, factor it out
  V := Domain (T)[1];
  d := Dimension (V);
  R := R[1];
  r := Dimension (R);
  C := Complement (V, R);
  COB := GL (d, K)!Matrix (Basis (C) cat Basis (R));
  S := SystemOfForms (T);
  SS := [ COB * S[i] * Transpose (COB) : i in [1..#S] ];
  n := d - r;
  SSND := [ ExtractBlock (SS[i], 1, 1, n, n) : i in [1..#SS] ];
  TTND := Tensor (SSND, 2, 1);
  e := Dimension (Codomain (TTND));
  
  // compute pseudo-isometries of non-degenerate tensor
  UUND, LLND := PseudoIsometryGroup (TTND);
  UUND_gens := [ ExtractBlock (UUND.i, 1, 1, n, n) : i in [1..Ngens (UUND)] ];
  LLND_gens := [ ExtractBlock (LLND.i, 1, 1, n, n) : i in [1..Ngens (LLND)] ];
  LLND_out := [ ExtractBlock (LLND.i, n+1, n+1, e, e) : i in [1..Ngens (LLND)] ];
// sanity check:
"pseudo-isometries?", forall { i : i in [1..Ngens (LLND)] | 
           IsPseudoIsometry (TTND, LLND_gens[i], LLND_out[i]) };
  
  // now frame and conjugate back
  MS := KMatrixSpace (BaseRing (T), n, r);
  MA := MatrixAlgebra (K, d);
  gens := [ GL (d, K)!InsertBlock (Identity (MA), Matrix (Basis (MS)[i]), 1, n+1) : 
                     i in [1..Dimension (MS)] ];
  gens cat:= [ GL (d, K)!InsertBlock (Identity (MA), GL (r, K).i, n+1, n+1) :
                     i in [1..Ngens (GL (r, K))] ];
  UUgens := gens cat [ GL (d, K)!InsertBlock (Identity (MA), UUND_gens[i], 1, 1) :
                     i in [1..Ngens (UUND)] ];
  LLgens := gens cat [ GL (d, K)!InsertBlock (Identity (MA), LLND_gens[i], 1, 1) :
                     i in [1..Ngens (LLND)] ];
  Ugens := [ COB^-1 * UUgens[i] * COB : i in [1..#UUgens] ];
  Lgens := [ COB^-1 * LLgens[i] * COB : i in [1..#LLgens] ];
  U := sub < GL (d, K) | Ugens >;
  L := sub < GL (d, K) | Lgens >;
  
return U, L;
end function;

