/* functions that use labels on graphs (or projective) geometries to cut down searches */

intrinsic ProjectiveAction (G::GrpMat, n::RngIntElt : TIMER := false) 
          -> GrpMat , Map , SeqEnum
  { Compute the action of G on n-subspaces of its natural module. }
  
  k := BaseRing (G);
  d := Degree (G);
  V := VectorSpace (k, d);
  
  require n le d : "n must not exceed the degree of G";
  
  require n in [1,2] : "this is all we need for now";
  
  tt := Cputime ();
  P := { sub < V | v > : v in V | v ne 0 };
  if n eq 1 then
       X := P;
  else
       X := { x + y : x in P , y in P | x ne y };
  end if;
  X := [ x : x in X ];
  if TIMER then "    time to build all",n,"-spaces:", Cputime (tt); end if;
 
  // compute permutation action of the generators of G
  tt := Cputime ();
  gens := [ ];
  S := SymmetricGroup (#X);
  for i in [1..Ngens (G)]  do
      perm := [ ];
      for x in X do
          Append (~perm, Position (X, sub<V| [ (x.j) * (G.i) : j in [1..n] ]>));
      end for;
      Append (~gens, S!perm);
  end for;
  if TIMER then "    time to construct permutation group:", Cputime (tt); end if;
  
  tt := Cputime ();
  H := sub < S | gens >;
  RandomSchreier (H);
  RandomSchreier (G);
  f := hom < G -> H | gens >;
  if TIMER then "    time to construct homomorphism:", Cputime (tt); end if;
  
return H, f, X;

end intrinsic;

// a general procedure to partition S using the labeling function
__partition := function (S, X, labfn)
  part := [ [ S[1] ] ];
  labels := [ labfn (S[1], X) ];
  for i in [2..#S] do
       l := labfn (S[i], X);
       if exists (j){ a : a in [1..#labels] | l eq labels[a] } then
            Append (~part[j], S[i]);
       else
            Append (~part, [ S[i] ]);
            Append (~labels, l);
       end if;
  end for;
return part;
end function;



/*
  Developer's note: February 8, 2019.
  
  The idea is that this intrinsic will eventually be rather general. At present,
  it has only been worked out for tensors, but I will describe it in the generality
  for which it is intended.
  
  INPUT:
     (1) An object X, e.g. a group, tensor, algebra.
     (2) A vector space W that is known to be an Aut(X)-module, although the
         group A = Aut(X) has yet to be determined.
     (3) A function that produces A-invariant labels on points (1-spaces) of PG(W).
         We anticipate this function takes in just the object X and a 1-space and
         outputs a label of some sort. In principle this can be just an integer,
         although it may be more convenient to have greater flexibility.
     (4) An analogous function that labels lines (2-spaces) of PG(W).
     
  IMPORTANT: The user is responsible for providing labeling functions that
         accept the described input and produce Aut(X)-invariant labels.
     
  OPTIONAL INPUT:
     (5) UPPER, a known overgroup of the restriction of Aut(X) to W; 
         this will default to GL(W) if it is not specified.
         
  OUTPUT:
     (a) A group U satisfying Aut(X)_W < U < UPPER < GL(W).
         We know where U lies in this chain because it is built as a subgroup of
         upper and it stabilizes an Aut(X)-invariant partition of PG_0(W)
     (b) The U-orbits on PG_0(W).
*/
intrinsic LabelledProjectiveSpace (
     t::TenSpcElt, W::ModTupFld, point_label::UserProgram, line_label::UserProgram : 
            UPPER := false, TIMER := false
                                  ) -> GrpMat, SeqEnum
  { Use labels on PG(W) to construct an overgroup of Aut(t)|_W. }
  
  e := Dimension (W);
  k := BaseRing (W);
  G := GL (e, k);
   
  // set up U
  if Type (UPPER) eq BoolElt then
       U := G;
  else
       require (Type (UPPER) eq GrpMat) and (Degree (UPPER) eq e) and (BaseRing (UPPER) eq k) :
            "optional argument UPPER must be a subgroup of GL(W)";
       // change the action of U to be consistant with our interpretation of points
       U := sub < G | [ Transpose (UPPER.i) : i in [1..Ngens (UPPER)] ] >;
  end if;
  
  vprint Autotopism, 2 : "initially, |U| =", #U;
  
  // induce U on the points P of PG(W) and then label P using the labeling function
  UP, fP, P := ProjectiveAction (U, 1 : TIMER := TIMER);
  tt := Cputime ();
  oP := Orbits (UP);
  if TIMER then "time to compute UP-orbits:", Cputime (tt); end if;
  partP := [ [ P[i] : i in oP[j] ] : j in [1..#oP] ];
	  vprint Autotopism, 2 : "the initial point partition has", #partP, "part(s)";
  tt := Cputime ();
  partP := &cat [ __partition (Q, t, point_label) : Q in partP ];
  if TIMER then "time to compute labels on points:", Cputime (tt); end if;
      vprint Autotopism, 2 : "after labeling, point partition has", #partP, "part(s)";
  oP := [ { Position (P, x[i]) : i in [1..#x] } : x in partP ];
  tt := Cputime ();
  UP := Stabiliser (UP, oP);
  UP := ReduceGenerators (UP);
  if TIMER then "time to compute stabiliser of point partition:", Cputime (tt); end if;
      vprint Autotopism, 2 : "UP has", Ngens (UP), "generators";
  tt := Cputime ();
  U := UP @@ fP;
  if TIMER then "time to compute pullback of U:", Cputime (tt); end if;
  
  vprint Autotopism, 2 : "now that U stabilizes point partition, |U| =", #U;
  vprint Autotopism, 2 : "  ";
  
  // induce U on the lines M of PG(W) and then label L using its labeling function
  UM, fM, M := ProjectiveAction (U, 2 : TIMER := TIMER);
  tt := Cputime ();
  oM := Orbits (UM);
  if TIMER then "time to compute UM-orbits:", Cputime (tt); end if;
  partM := [ [ M[i] : i in oM[j] ] : j in [1..#oM] ];
	  vprint Autotopism, 2 : "the initial line partition has", #partM, "part(s)";
  tt := Cputime ();
  partM := &cat [ __partition (Q, t, line_label) : Q in partM ];
  if TIMER then "time to compute labels on lines:", Cputime (tt); end if;
      vprint Autotopism, 2 : "after labeling, LINE partition has", #partM, "part(s)";
  oM := [ { Position (M, x[i]) : i in [1..#x] } : x in partM ];
  tt := Cputime ();
  UM := Stabiliser (UM, oM);
  UM := ReduceGenerators (UM);
  if TIMER then "time to compute stabiliser of line partition:", Cputime (tt); end if;
  tt := Cputime ();
  U := UM @@ fM;
  if TIMER then "time to compute pullback of U:", Cputime (tt); end if;
  
  vprint Autotopism, 2 : "now that U stabilizes the line partition, |U| =", #U;
  
  // induce U on points again, compute orbits, recalculate partP
  UP := U @ fP;
  tt := Cputime ();
  oP := Orbits (UP);
  if TIMER then "time to re-compute UP-orbits:", Cputime (tt); end if;
  partP := [ [ P[i] : i in oP[j] ] : j in [1..#oP] ];
	  vprint Autotopism, 2 : "the final point partition has", #partP, "part(s)";
  
  // convert U back to the correct action
  U := sub < Generic (U) | [ Transpose (U.i) : i in [1..Ngens (U)] ] >;
     
return U, partP; 
  
end intrinsic;





       /*----- some labeling functions for bimaps -------*/

// a label for points that uses the dimension of the radical of the corresponding form       
__rank_label := function (z, t)
  F := SystemOfForms (t);
return Dimension ( Nullspace (&+ [ (z.1)[i] * F[i] : i in [1..#F] ]));
end function;

// the quick and dirty way to label lines using the slope invariant
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

// the best possible label for lines
__genus2_label := function (m, t)
  F := SystemOfForms (t);
  s := Tensor ([ &+ [ (m.1)[i] * F[i] : i in [1..#F] ], 
                 &+ [ (m.2)[i] * F[i] : i in [1..#F] ] ], 2, 1); 
return Genus2Signature (s);
end function;
