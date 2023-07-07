// testing the new graph function

// load the labelling functions
load "~/Documents/GitHub/MAGMA/Auto-Sandbox/src/bimap_labels.m";

// a test with a group list provided by JM 
load "~/Documents/GitHub/MAGMA/Auto-Sandbox/examples/sesGroups.m";

// given a p-group H, returns the orders of U computed with graph method
// using Genus2 and Slope labels, respectively.
__Genus2_Versus_Slope := function (H)
  t := pCentralTensor (H);
  W := Codomain (t);
  U, part := LabelledProjectiveSpace (t, W, RANK_LABEL, GENUS2_LABEL);
  UU := LabelledProjectiveSpace (t, W, RANK_LABEL, SLOPE_LABEL);
  // ensure slope and genus 2 give consistent answers
  assert U subset UU;
return #U, #UU;
end function;

// ensures, by brute force check, that U returned by graph method
// really does contain all isotopisms / pseudi-isometries
__RealityCheck := function (H : LAB := GENUS2_LABEL)
  t := pCentralTensor (H);
  W := Codomain (t);
  ttt := Cputime ();
  U, part := LabelledProjectiveSpace (t, W, RANK_LABEL, GENUS2_LABEL);
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
__RandomBimapTest := function (k, b, c, e : LAB := SLOPE_LABEL)
  t := Tensor ([ Matrix (Random (KMatrixSpace (k, b, c))) : i in [1..e] ], 2, 1);
  W := Codomain (t);
  ttt := Cputime ();
  U := LabelledProjectiveSpace (t, W, RANK_LABEL, LAB);
  ULIFT := { h : h in U | LiftIsotopism (t, t, h) };
  "   computed U via graphs and lifts in time", Cputime (ttt);
  ttt := Cputime ();
  LIFT := { h : h in Generic (U) | LiftIsotopism (t, t, h) };
  "   computed brute force lift in time", Cputime (ttt);
  "   |LIFT| =", #LIFT;
return LIFT eq ULIFT;
end function;  

// Brahana tests
load "~/Documents/GitHub/MAGMA/Auto-Sandbox/examples/brahana/programs.m";
load "~/Documents/GitHub/MAGMA/Auto-Sandbox/examples/brahana/present.m";
load "~/Documents/GitHub/MAGMA/Auto-Sandbox/examples/dual.m";
p := 5;
B := BrahanaList (p);
__BrahanaTest := function (i : LAB := SLOPE_LABEL)
  H := DualGroup (B[i]);
  t := pCentralTensor (H);
  W := Codomain (t);
return LabelledProjectiveSpace (t, W, RANK_LABEL, LAB : TIMER := false);
end function;
  


