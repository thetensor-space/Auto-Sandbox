/* tests for graded algebra iso paper */

// parameters
d := 10; p := 5; e := 5; g := 4; num := 10;

// twisted Heisenberg quotient test
twisted_heisenberg_test := function (p, e, g : SANITY := false, LIFT := true)
  for i in [1..num] do
  "performing trial i =", i, "out of", num, "for (p,e,g) =", [p,e,g];
      H := TwistedHeisenbergGroup (p, e);
      U := RandomQuoByGenus (H, g);
      T := pCentralTensor (U);
//   "tensor:", T;
      O1, p1, l1, pi, lambda := ActionOnCodomain (T);
   "we are labeling", pi, "points, and", lambda, "lines";
   "using SLOPE, there are", p1, "point labels, and", l1, "line labels";
      O2, p2, l2 := ActionOnCodomain (T : LineLabel := "Genus2Sig");
   "using GENUS2, there are", p2, "point labels, and", l2, "line labels";
   "using GENUS2, the working overgroup has order", #O2;
      if LIFT then
          PIO2 := [ ];
          for h in O2 do
              isit, x := LiftPseudoIsometry (T, T, h);
              if isit then
                  Append (~PIO2, h);
              end if;
          end for;
          "of these elements,", #PIO2, "lift to pseudo-isometries";
      end if;
      if SANITY then
          O := GL (g, p);
          PI := [ ];
          for h in O do
              isit, x := LiftPseudoIsometry (T, T, h);
              if isit then
                  Append (~PI, h);
              end if;
          end for;
          "    SANITY CHECK ... ", Set (PI) eq Set (PIO2);
      end if; 
      "----------"; 
  end for;
return true; 
end function;


random_test := function (d, p, e : SANITY := false, LIFT := true)
"d =", d, "   p =", p, "   e =", e;
"==============================";
  for i in [1..num] do
      S0 := [ Random (MatrixAlgebra (GF (p), d)) : j in [1..e] ];
      S := [ S0[j] - Transpose (S0[j]) : j in [1..e] ];
      T := Tensor (S, 2, 1);
      O, np, nl, pi, lambda := ActionOnCodomain (T);
   "we are labeling", pi, "points, and", lambda, "lines";
   "there are", np, "point labels, and", nl, "line labels";
   "the overgroup has order", #O;
     if LIFT then
          PIO := [ ];
          for h in O do
              isit, x := LiftPseudoIsometry (T, T, h);
              if isit then
                  Append (~PIO, h);
              end if;
          end for;
          "of these elements,", #PIO, "lift to pseudo-isometries";
      end if;
      if SANITY then
          OO := GL (g, p);
          PI := [ ];
          for h in OO do
              isit, x := LiftPseudoIsometry (T, T, h);
              if isit then
                  Append (~PI, h);
              end if;
          end for;
          "    SANITY CHECK ... ", Set (PI) eq Set (PIO);
      end if; 
      "----------";
  end for;
return true;
end function;


