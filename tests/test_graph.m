// testing the new graph function

__rank_label := function (z, t)
  F := SystemOfForms (t);
return Dimension ( Nullspace (&+ [ (z.1)[i] * F[i] : i in [1..#F] ]));
end function;

__slope_label := function (m, t)
  F := SystemOfForms (t);
  k := BaseRing (m);
  f1 := &+ [ (m.1)[i] * F[i] : i in [1..#F] ]; 
  f2 := &+ [ (m.2)[i] * F[i] : i in [1..#F] ];
  r := Nrows (f1);
  c := Ncols (f1);
  if (r ne c) or not ((f1 eq -Transpose (f1)) and (f2 eq -Transpose (f2))) then
       // if f1 and f2 are not alternating make an alternating pair from them
       d := r + c;
       df1 := MatrixAlgebra (k, d)!0;
       InsertBlock (~df1, f1, 1, 1 + r);
       InsertBlock (~df1, -Transpose (f1), 1 + r, 1);   
       df2 := MatrixAlgebra (k, d)!0;
       InsertBlock (~df2, f2, 1, 1 + r);
       InsertBlock (~df2, -Transpose (f2), 1 + r, 1);
       MS := KMatrixSpace (k, d, d);
       ms := KMatrixSpaceWithBasis ([MS!df1, MS!df2]);
  else
       d := r;
       MS := KMatrixSpace (k, d, d);
       ms := KMatrixSpaceWithBasis ([MS!f1, MS!f2]);
  end if;
  sloped := exists (T){ S : S in ms | Rank (S) eq Nrows (S) };
  if not sloped then
       MA := MatrixAlgebra (k, d);
       dim := Dimension (Nullspace (ms.1) meet Nullspace (ms.2)) gt 0; 
       sig := dim;
       return sig;
  else
       assert exists (X){ S : S in ms | sub < ms | S, T > eq ms };
       slope := X * T^-1;
       J, C, info := JordanForm (slope);
       facs := { info[i][1] : i in [1..#info] };
       sig := [ ];
       for p in facs do
             Append (~sig, < Degree (p) , [ x[2] : x in info | x[1] eq p ] >);
       end for;
  end if;      
return Multiset (sig);
end function;

__genus2_label := function (m, t)
  F := SystemOfForms (t);
  s := Tensor ([ &+ [ (m.1)[i] * F[i] : i in [1..#F] ], 
                 &+ [ (m.2)[i] * F[i] : i in [1..#F] ] ], 2, 1); 
return Genus2Signature (s);
end function;


// a test with a group list provided by JM 
load "~/MagmaGit/Auto-Sandbox/examples/sesGroups.m";

// given a p-group H, returns the orders of U computed with graph method
// using Genus2 and Slope labels, respectively.
__Genus2_Versus_Slope := function (H)
  t := pCentralTensor (H);
  W := Codomain (t);
  U, part := LabelledProjectiveSpace (t, W, __rank_label, __genus2_label);
  UU := LabelledProjectiveSpace (t, W, __rank_label, __slope_label);
  // ensure slope and genus 2 give consistent answers
  assert U subset UU;
return #U, #UU;
end function;

// ensures, by brute force check, that U returned by graph method
// really does contain all isotopisms / pseudi-isometries
__RealityCheck := function (H : LAB := __genus2_label)
  t := pCentralTensor (H);
  W := Codomain (t);
  ttt := Cputime ();
  U, part := LabelledProjectiveSpace (t, W, __rank_label, __genus2_label);
  "   constructed labelled graph in time", Cputime (ttt);
  "   |U| =", #U;
  // lift U to pseudo-isometries of t
  ttt := Cputime ();
  ULIFT := { h : h in U | LiftPseudoIsometry (t, t, h) };
  "   computed U lift in time", Cputime (ttt);
  // lift all of GL(W) to pseudo-isometries
  ttt := Cputime ();
  LIFT := { h : h in Generic (U) | LiftPseudoIsometry (t, t, h) };
  "   computed brute force lift in time", Cputime (ttt);
  "   |LIFT| =", #LIFT;
return LIFT eq ULIFT;
end function;

// produces a random bimap k^b x k^c >--> k^e and does the same check as previous fn
__RandomBimapTest := function (k, b, c, e : LAB := __slope_label)
  t := Tensor ([ Matrix (Random (KMatrixSpace (k, b, c))) : i in [1..e] ], 2, 1);
  ttt := Cputime ();
  U := LabelledProjectiveSpace (t, W, __rank_label, LAB);
  ULIFT := { h : h in U | LiftIsotopism (t, t, h) };
  "   computed U via graphs and lifts in time", Cputime (ttt);
  ttt := Cputime ();
  LIFT := { h : h in Generic (U) | LiftIsotopism (t, t, h) };
  "   computed brute force lift in time", Cputime (ttt);
  "   |LIFT| =", #LIFT;
return LIFT eq ULIFT;
end function;  

// Brahana tests
load "examples/brahana/programs.m";
load "examples/brahana/present.m";
load "examples/dual.m";
p := 7;
B := BrahanaList (p);
__BrahanaTest := function (B, i : LAB := __slope_label)
  H := DualGroup (B[i]);
  t := pCentralTensor (H);
  W := Codomain (t);
return LabelledProjectiveSpace (t, W, __rank_label, LAB);
end function;
  


