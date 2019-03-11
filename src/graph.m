/* functions that use labels on graphs (or projective) geometries to cut down searches */
/* 2019 */

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
  // X := [ x : x in X ];
  // EOB -- use indexed set, not sequence 
  X := {@ x: x in X @};
  if TIMER then "    time to build all",n,"-spaces:", Cputime (tt); end if;
 
  // compute permutation action of the generators of G
  tt := Cputime ();
  gens := [ ];
  S := SymmetricGroup (#X);
  tt := Cputime ();
  for i in [1..Ngens (G)]  do
      perm := [ ];
      for x in X do
          Append (~perm, Position (X, sub<V| [ (x.j) * (G.i) : j in [1..n] ]>));
      end for;
      Append (~gens, S!perm);
  end for;

  vprint Autotopism, 2 : "   [ ProjectiveAction: time to build permutation gens:", Cputime (tt),"]";

  if TIMER then "    time to construct permutation group:", Cputime (tt); end if;

  
  tt := Cputime ();
  H := sub < S | gens >;
  RandomSchreier (H);
  RandomSchreier (G);
  f := hom < G -> H | gens >;

  vprint Autotopism, 2 : "   [ ProjectiveAction: time to build homomorphism:", Cputime (tt),"]";

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

                /*--- procedures for fingerprinting on bimaps ---*/
     
     // a basic fingerprint that distinguishes by dimensions of left- and right-radicals
     procedure __basic_fingerprint (~part, s)
          
          F := SystemOfForms (s);
          vprint Autotopism, 2 : 
               "\tPartition entered __basic_fingerprinting with", #part, "parts";
          
          npart := [ ];
          for a in [1..#part] do
               Q := part[a];
               // try to refine Q
               QUV := [* *];
               for b in [1..#Q] do
                    z := Q[b];
                    zU := Nullspace (&+ [ (z.1)[i] * F[i] : i in [1..#F] ]);
                    zV := Nullspace (&+ [ Transpose ((z.1)[i] * F[i]) : i in [1..#F] ]);
                    Append (~QUV, < zU , zV >); 
               end for;
               dims := [ [ Dimension (QUV[i][j]) : j in [1,2] ] : i in [1..#QUV] ];
               refQ := [ [ Q[b] : b in [1..#Q] | dims[b] eq pair ] : pair in Set (dims) ];
               npart cat:= refQ;
          end for;
          
          part := npart;
          vprint Autotopism, 2 : 
               "\tAfter basic_fingerprinting it has", #part, "parts";
     
     end procedure;
     
     
     // a more refined fingerprint that uses subspace arrangements 
     procedure __advanced_fingerprint (~part, s)
          
          F := SystemOfForms (s);
          vprint Autotopism, 2 : 
               "\tPartition entered __advanced_fingerprinting with", #part, "parts";
          
          // first, a basic fingerprint
          npart := [ ];
          UV := [ ];
          Uspaces := [*  *];
          Vspaces := [*  *];
          for a in [1..#part] do
               Q := part[a];
               // try to refine Q
               QUV := [* *];
               for b in [1..#Q] do
                    z := Q[b];
                    zU := Nullspace (&+ [ (z.1)[i] * F[i] : i in [1..#F] ]);
                    Append (~Uspaces, zU);
                    zV := Nullspace (&+ [ Transpose ((z.1)[i] * F[i]) : i in [1..#F] ]);
                    Append (~Vspaces, zV);
                    Append (~QUV, < zU , zV >); 
               end for;
               dims := [ [ Dimension (QUV[i][j]) : j in [1,2] ] : i in [1..#QUV] ];
               refQ := [ [ Q[b] : b in [1..#Q] | dims[b] eq pair ] : pair in Set (dims) ];
               refUV := [ [* QUV[b] : b in [1..#Q] | dims[b] eq pair *] : pair in Set (dims) ];
               npart cat:= refQ;
               UV cat:= refUV;
          end for;
        
          part := npart;
          vprint Autotopism, 2 : 
               "\tAfter basic_fingerprinting it has", #part, "parts";
                
          // next, refine the partition using the arrangement of subspaces in U 
          Usums := { X + Y : X in Uspaces, Y in Uspaces | X ne Y }; 
          npart := [ ];
          for a in [1..#part] do
               Q := part[a];
               D := [ ];   // distinct labels
               colours := [ 0 : q in Q ];   // remember to spell colour correctly
               for b in [1..#Q] do
                    // signature counts incidences with joins of subspaces 
                    sig := #{ Z : Z in Usums | (UV[a][b])[1] subset Z };
                    flag := exists (c){ d : d in [1..#D] | sig eq D[d] };
                    if flag then    // we have seen sig before
                         colours[b] := c;
                    else      // new sig, new colour
                         Append (~D, sig);
                         colours[b] := #D;
                    end if;
               end for;
               // decompose Q into color classes
               newQ := [ [ Q[i] : i in [1..#Q] | colours[i] eq c ] : c in [1..#D] ];
               npart cat:= newQ;
          end for;
          
          part := npart;
          vprint Autotopism, 2 : 
               "\tAfter fingerprinting with (left) subspace arrangement it has", #part, "parts";
               
          // if we act differently on the left and right domain spaces, we repeat for V ...
                
     end procedure;



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
     
  OPTIONAL INPUT:
     (5) OVERGROUP -- a known overgroup of the restriction of Aut(X) to W; 
         this will default to GL(W) if it is not specified.
     (6) FINGER_LEVEL -- indicates the level of fingerprinting we choose to
         preprocess with: 0 = none, 1 = basic, 2 = advanced
         Further options can perhaps be added.
         
  IMPORTANT: 
     (*) The user is responsible for providing labeling functions that
         accept the described input and produce Aut(X)-invariant labels.
     (*) Unless we have a better point_label function than the one we currently
         have that labels by rank, the basic point labelling is superseded by
         fingerprinting (even at the basic level). 
         
  OUTPUT:
     (a) A group U satisfying Aut(X)_W < U < UPPER < GL(W).
         We know where U lies in this chain because it is built as a subgroup of
         upper and it stabilizes an Aut(X)-invariant partition of PG_0(W)
     (b) The U-orbits on PG_0(W).
*/

intrinsic LabelledProjectiveSpace (
     t::TenSpcElt, W::ModTupFld, point_label::UserProgram, line_label::UserProgram : 
            OVERGROUP := false, 
            FINGER_LEVEL := 2,
            TIMER := false    // this will eventually be turned off
                                  ) -> GrpMat, SeqEnum
                                  
  { Use labels on PG(W) to construct an overgroup of Aut(t)|_W. }
  
  e := Dimension (W);
  k := BaseRing (W);
  G := GL (e, k);
   
  // set up U
  if Type (OVERGROUP) eq BoolElt then
       U := G;
  else
       require (Type (OVERGROUP) eq GrpMat) and (Degree (OVERGROUP) eq e) and 
               (BaseRing (OVERGROUP) eq k) :
            "optional argument UPPER must be a subgroup of GL(W)";
       // change the action of U to be consistant with our interpretation of points
       U := sub < G | [ Transpose (OVERGROUP.i) : i in [1..Ngens (OVERGROUP)] ] >;
  end if;
  
  vprint Autotopism, 2 : "\tInitially, |U| has ", Ceiling (Log (2, #U )),"bits.";
  
  // induce U on the points P of PG(W) 
  UP, fP, P := ProjectiveAction (U, 1 : TIMER := TIMER);
  
  tt := Cputime ();
  oP := Orbits (UP);
  if TIMER then "\tTime to compute UP-orbits:", Cputime (tt); end if;
  
  partP := [ [ P[i] : i in oP[j] ] : j in [1..#oP] ];
	  vprint Autotopism, 2 : "\tThe initial point partition has", #partP, "part(s)";
	  
  // carry out fingerprinting to the specified level
  tt := Cputime ();
  if FINGER_LEVEL eq 1 then
       __basic_fingerprint (~partP, t);
  elif FINGER_LEVEL eq 2 then
       __advanced_fingerprint (~partP, t);
  else
       assert FINGER_LEVEL eq 0;
  end if;
  if TIMER then "\tTime for level", FINGER_LEVEL, "fingerprinting:", Cputime (tt); end if;	  
  
  // replace UP with the stabilizer of the new partition and pull back to GL(W)
  oP := [ { Position (P, x[i]) : i in [1..#x] } : x in partP ];
  
  tt := Cputime ();
  UP := Stabiliser (UP, oP);
  UP := ReduceGenerators (UP);
  if TIMER then "\tTime to compute stabiliser of point partition:", Cputime (tt); end if;
  
  tt := Cputime ();
  U := UP @@ fP;
  if TIMER then "\tTime to compute pullback of U:", Cputime (tt); end if;	
	   
  tt := Cputime ();
  npartP := &cat [ __partition (Q, t, point_label) : Q in partP ];
  if TIMER then "\tTime to compute labels on points:", Cputime (tt); end if;
  
            // verify claim made in the developer's note that 
            // this adds nothing new to fingerprinting
            assert npartP eq partP;
  
  vprint Autotopism, 2 : "\tNow that U stabilizes point partition, |U| has ", Ceiling (Log (2, #U)),"bits.";
  
  
  // induce U on the lines M of PG(W) and then label L using its labeling function
  UM, fM, M := ProjectiveAction (U, 2 : TIMER := TIMER);
  
  tt := Cputime ();
  oM := Orbits (UM);
  if TIMER then "\tTime to compute UM-orbits:", Cputime (tt); end if;
  
  partM := [ [ M[i] : i in oM[j] ] : j in [1..#oM] ];
	  vprint Autotopism, 2 : "\tThe initial line partition has", #partM, "part(s)";
	  
  tt := Cputime ();
  partM := &cat [ __partition (Q, t, line_label) : Q in partM ];
  if TIMER then "\tTime to compute labels on lines:", Cputime (tt); end if;
  
      vprint Autotopism, 2 : "\tAfter labeling, line partition has", #partM, "part(s)";
      
  oM := [ { Position (M, x[i]) : i in [1..#x] } : x in partM ];
  
  tt := Cputime ();
  UM := Stabiliser (UM, oM);
  UM := ReduceGenerators (UM);
  if TIMER then "\tTime to compute stabiliser of line partition:", Cputime (tt); end if;
  
  tt := Cputime ();
  U := UM @@ fM;
  if TIMER then "time to compute pullback of U:", Cputime (tt); end if;
  
  vprint Autotopism, 2 : "\tNow that U stabilizes the line partition, |U| has (", Ceiling (Log (2, #U)),"bits )";
  
  // induce U on points again, compute orbits, recalculate partP
  UP := U @ fP;
  oP := Orbits (UP);
  partP := [ [ P[i] : i in oP[j] ] : j in [1..#oP] ];
	  vprint Autotopism, 2 : "\tThe final point partition has", #partP, "part(s)";
  
  // convert U back to the correct action
  U := sub < Generic (U) | [ Transpose (U.i) : i in [1..Ngens (U)] ] >;
     
return U, partP; 
  
end intrinsic;





             
