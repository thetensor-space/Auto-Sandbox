import "GlobalVars.m" : __SANITY_CHECK;

/* functions to find char. subgroups using projective geometry */

/* To do: include interface from Blackburn data to get first partition of points */ 

/* To do: allow the possibility of permuting the bimap variables */

//AttachSpec ("~/Dropbox/MagmaPackages/StarAlg/star.spec");
//AttachSpec ("~/Dropbox/MagmaPackages/Filters/Filters.spec");
//AttachSpec ("~/Dropbox/MagmaPackages/Multilinear/Multi.spec");
//AttachSpec ("~/Dropbox/MagmaPackages/SmallGenus/Small.spec");

// pull out the canonical labeling of points
// see if there are Magma functions for projective geometries.


/*
  Sets up the basic data structure.

  Given S, a list of e linearly independent matrices over k, 
  compute the action of GL(e,k) on points and lines of PG(e,k),
  where we identify k^e with k-matrix space spanned by S. 
  
  The output is:
  
  (1) The action of PGL(e,k) on points.
  (2) The action of PGL(e,k) on lines.
  (3) An isomorphism between these actions.
  (4) The set of points as 1-spaces of matrices.
  (5) The set of lines as 2-spaces of matrices.
  (6) Map from GL(e, k) to PGL(e, k)
*/

ActionOnProjectiveSpace := function (S : points := [])
  k := BaseRing (S[1]);
  c := Nrows (S[1]);
  d := Ncols (S[1]);
  e := #S;
  W := KMatrixSpaceWithBasis ([ KMatrixSpace (k, c, d)!(S[i]) : i in [1..e] ]);
  V := VectorSpace (k, e);
  H := GL (e, k);
  if points eq [] then // these have not been precomputed and passed
      points := { sub < W | w > : w in W | not w eq 0 };
      points := [ p : p in points ];
  end if;
  lines := { p + q : p in points, q in points | p ne q };
  lines := [ l : l in lines ];
  pgens := [ ];
  lgens := [ ];  
  for i in [1..Ngens (H)] do
    x := H.i;  
    // first the permutation of points
    image := [ ];
    for j in [1..#points] do
       p := points[j];
       v := (V!Coordinates (W, p.1)) * x;
       q := sub < W | &+ [ v[l] * W.l : l in [1..e] ] >;
       assert exists (imj){ r : r in [1..#points] | q eq points[r] };
       Append (~image, imj);
    end for;
    Append (~pgens, SymmetricGroup (#points)!image);  
    // next the permutation of lines
    image := [ ];         
    for j in [1..#lines] do         
       l := lines[j];
       v1 := (V!Coordinates (W, l.1)) * x;
       v2 := (V!Coordinates (W, l.2)) * x;
       m := sub < W | &+ [ v1[b] * W.b : b in [1..e] ] ,
                             &+ [ v2[b] * W.b : b in [1..e] ] >;
       assert exists (imj){ r : r in [1..#lines] | m eq lines[r] };
       Append (~image, imj);         
    end for;         
    Append (~lgens, SymmetricGroup (#lines)!image);    
  end for;
  HP := sub < SymmetricGroup (#points) | pgens >;
  HL := sub < SymmetricGroup (#lines) | lgens >;
  RandomSchreier (HP);
  RandomSchreier (HL);
  f := hom < HP -> HL | lgens >;
  tau := hom < H -> HP | pgens>; 
return HP, HL, f, points, lines, tau, W;
end function;


/* ------ signature functions for labeling lines ------ */

   /*
     This is a quick and dirty function that will handle "most"
     situations. When it fails, turn to more sophisticated labeling.
   */
   SlopeSignature := function (l)
      // if l does not consist of alternating forms, then double for now
      // eventually we'll replace this with something more refined
      if Nrows (l.1) ne Ncols (l.1) then
          d := Nrows (l.1) + Ncols (l.1);
          bas := [ ];
          for i in [1,2] do
            mat := MatrixAlgebra (BaseRing (l), d)!0;
            InsertBlock (~mat, l.i, 1, 1 + Nrows (l.i));
            InsertBlock (~mat, -Transpose (l.i), 1 + Nrows (l.i), 1);
            Append (~bas, mat);
          end for;
          MS := KMatrixSpace (BaseRing (l), d, d);
          m := KMatrixSpaceWithBasis ([MS!(bas[i]) : i in [1,2]]);
      elif not forall { i : i in [1,2] | l.i eq - Transpose (l.i) } then
          d := Nrows (l.1) + Ncols (l.1);
          bas := [ ];
          for i in [1,2] do
            mat := MatrixAlgebra (BaseRing (l), d)!0;
            InsertBlock (~mat, l.i, 1, 1 + Nrows (l.i));
            InsertBlock (~mat, -Transpose (l.i), 1 + Nrows (l.i), 1);
            Append (~bas, mat);
          end for;
          MS := KMatrixSpace (BaseRing (l), d, d);
          m := KMatrixSpaceWithBasis ([MS!(bas[i]) : i in [1,2]]);
      else
          m := l;
      end if;
      sloped := exists (T){ S : S in m | Rank (S) eq Nrows (S) };
      if not sloped then
          MA := MatrixAlgebra (BaseRing (m), Nrows (m.1));
          dim := Dimension (Nullspace (m.1) meet Nullspace (m.2)) gt 0; 
          sig := dim;
          return sig;
      else
          assert exists (X){ S : S in m | sub < m | S, T > eq m };
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

   /* 
     This function produces the "perfect" labels. Two lines get the same
     label if, and only if, the associated genus 2 bimaps are pseudo-isometric.
   */
   Genus2Sig := function (m)
      F1 := Matrix (m.1);
      F2 := Matrix (m.2);
   return Genus2Signature (Tensor ([F1, F2], 2, 1));
   end function;


   BasicSigEq := function (sigA, sigB)
   return sigA eq sigB;
   end function;
   
/* ------ partition creation and refinement functions for points and lines ------ */

/* 
  Finds a partition of points using basic fingerprinting ideas.
  
  We will look into upgrading this function. 
*/
ElementaryPointPartition := function (points : FullPartition := false)

  pre_points := [ Nullspace (Matrix (points[i].1)) : i in [1..#points] ];
  dims := { Dimension (pre_points[i]) : i in [1..#pre_points] };
  if #dims eq 1 then
    partition := [ {1..#points} ];
  else  
    partition := [ ];
    for r in dims do
      Pr := { i : i in [1..#points] | Dimension (pre_points[i]) eq r };
      Append (~partition, Pr);
    end for;
  end if;
  
  // use sums of pre_points to (further) refine partition
  if FullPartition then
    lines := { E + F : E in pre_points , F in pre_points | E ne F };
    refined_partition := [ ];
    for X in partition do
      D := [ ];
      Y := [ x : x in X ];
      colours := [ 0 : y in Y ];
      for i in [1..#Y] do
        sig := #{ l : l in lines | pre_points[Y[i]] subset l };
        flag := exists (t){ u : u in [1..#D] | sig eq D[u] };
        if flag then
          colours[i] := t;
        else
          Append (~D, sig);
          colours[i] := #D;
        end if;
      end for;
      newY := [ { Y[j] : j in [1..#Y] | colours[j] eq u } : u in [1..#D] ];
      refined_partition cat:= newY;
    end for;
    partition := refined_partition;
  end if;
  
return partition;

end function;


/*
  Given a partition of the lines of the geometry, refine the partition using
  your preferred choice of line labeling mechanisms.
*/
RefineLinePartition := function (line_partition, lines, LineSignature, LineSigEquals)
  new_line_partition := [ ];  
  for X in line_partition do
    DLS := < >;
    Y := [ x : x in X ];
    colours := [ 0 : y in Y ];
    for i in [1..#Y] do
      l := lines[Y[i]];
      sig := LineSignature (l);
      flag := exists (t){ u : u in [1..#DLS] | LineSigEquals (sig, DLS[u]) };
      if flag then
          colours[i] := t;
      else
          Append (~DLS, sig);
          colours[i] := #DLS;
      end if;
    end for;
    newY := [ { Y[j] : j in [1..#Y] | colours[j] eq u } : u in [1..#DLS] ];
    new_line_partition cat:= newY;
  end for;
return new_line_partition;
end function;


/* ------ the main function ------ */


/*
  <CharacteristicSubgroups>

  Given a p-group G of p-class 2, return all proper characteristic 
  subgroups of G that we can find, other than the obvious one.
  
  This is done by finding partitions on points, lines, and possibly
  planes of one of various natural projective geometries associated
  with G.
  
  The <Special> version is used with the usual commutation bimap 
  
     [ , ] : V x V >--> W.
  
  Here, one can bring to bear on the problem refined techniques for 
  labeling groups of genus 1 and genus 2.
  
  The <General> version is used on permutations of the bimap that are
  not alternating. It has, at present, only quite weak labeling 
  options, but there are situations where we see advantage to using
  this instead of the <Special> version. One would be when <W> has
  a large dimension relative to <V>. Another might be when <V> has
  odd dimension and <W> has even dimension.
  
  Finally, the general version can be used -- as the name suggests --
  in more general settings. For instance when working maps
  U x V >--> W. For that reason the <General> version takes as input
  a bimap rather than a group.
*/

/* some internal functions */

// given a partition of points, see which parts span proper subspaces
__proper_subspaces := function (points, partition, e)
  spaces := < >;
//  "   ... partition =", partition;
  for X in partition do
    WX := &+ [ points[x] : x in X ];
    if (Dimension (WX) lt e) and (not exists { Z : Z in spaces | Z eq WX }) then
      Append (~spaces, WX);   
    end if;
  end for;
return spaces;
end function;

// given a proper subspace of the space of matrices, convert to char. subgroup
__subspace_to_subgroup := function (B, U, X)
  h := B`Coerce[3];
  W := VectorSpace (BaseRing (U), Dimension (U));
  N := W;
  for i in [1..Ngens (X)] do
    N meet:= Nullspace (Transpose (Matrix (W!(Coordinates (U, X.i)))));
  end for;
return N @@ h;
end function;




/*
  Plug in option to specify a partition of points coming
  from some mechanism (e.g. fingerprinting, Blackburn labeling).  
*/

InvariantSpaces_Special := function (B : 
                     LineSigFn := Genus2Sig, 
                     LineSigEqFn := BasicSigEq,
                     FullPartition := false,
                     FullGraph := false
                               )

  S := SystemOfForms (B);
"dim(W) =", Dimension (Codomain (B));
  MS := KMatrixSpace( BaseRing(B), Nrows(S[1]), Ncols(S[1]));
  U := KMatrixSpaceWithBasis ([MS!T : T in S]);
  
  // find the groups acting on points and lines
  Hp, Hl, f, points, lines, tau := ActionOnProjectiveSpace (S);
"|points| =", #points;
"|lines| =", #lines;
"|Hp| =", #Hp;
"|Hl| =", #Hl;
"------------";

//  "#points =", #points;
//  "#lines =", #lines;
  
  point_part := ElementaryPointPartition (points : FullPartition := FullPartition);
//  "elementary point partition:", [#P : P in point_part];
  "elementary point partition has", #point_part, "parts";
  
  if #point_part gt 1 then    // replace with smaller group
      Hp := Stabiliser (Hp, point_part);
      Hl := Hp @ f;
  end if;
"|Hp| =", #Hp;
"|Hl| =", #Hl;
"--------------";
  
  // compute orbits under Hp and see if this gives a break
  orbits := Orbits (Hp);
  point_part := [ { i : i in orbits[j] } : j in [1..#orbits] ];
  "after computing orbits, point partition has", #point_part, "parts";
  
  spaces := __proper_subspaces (points, point_part, #S);
  if (#spaces gt 0) and (not FullGraph) then
      return spaces, _;
  end if;
  
  // compute orbits under Hl and use them as the basic line partition
  orbits := Orbits (Hl);
  line_part := [ { i : i in orbits[j] } : j in [1..#orbits] ];
  "first line partition has", #line_part, "parts";
Hl := Stabiliser (Hl, line_part);
Hp := Hl @@ f;
"|Hp| =", #Hp;
"|Hl| =", #Hl;
  
  // refine the line partition
  ref_line_part := RefineLinePartition (line_part, lines, LineSigFn, LineSigEqFn);
  "refined line partition has", #ref_line_part, "parts";
  if #ref_line_part gt #line_part then   // cut down group and recompute orbits
    line_part := ref_line_part;
    Hl := Stabiliser (Hl, line_part);
    Hp := Hl @@ f;
"|Hp| =", #Hp;
"|Hl| =", #Hl;
    orbits := Orbits (Hp);
    point_part := [ { i : i in orbits[j] } : j in [1..#orbits] ];
//    "resulting point partition has", #point_part, "parts";
    spaces := __proper_subspaces (points, point_part, #S);
        
  end if;
  
// addition to return stabiliser as matrices in GL(e, k)
P := Hp @@ tau;

return spaces, P;

end function;




intrinsic CharacteristicSubgroups (B::TenSpcElt : 
	             LineSigFn := Genus2Sig, 
	             LineSigEqFn := BasicSigEq,
	             FullPartition := false,
	             FullGraph := true
                                  ) -> SeqEnum, SeqEnum, Grp
{Locate characteristic subgroups and constrain the possible automorphisms.}
                                   
  I, P := InvariantSpaces_Special (B : LineSigFn := LineSigFn,
                                    LineSigEqFn := BasicSigEq,
                                    FullPartition := FullPartition,
                                    FullGraph := FullGraph);

"order of final group to list:", #P;
                                    
return I;
 
/*
// commented out by PAB on 5/13/2017 ... testing examples in paper                                    
  S := AsMatrices(B,2,1);
  MS := KMatrixSpace(BaseRing(B), Nrows(S[1]), Ncols(S[1]));
  U := KMatrixSpaceWithBasis ([MS!T : T in S]);
  if #I gt 0 then
      return [ __subspace_to_subgroup (B, U, X) : X in I ], I, P;
  end if;  
return [ ], _, P;
*/
    
end intrinsic;

/*
  New function included by PAB on 06/25/2016.
  
  The objective has now changed from producing lists of 
  characteristic subgroup to explicitly finding an 
  overgroup for the action of Aut(G) on Z(G). This
  new function also corrects the discrepancy 
  encountered by JBW and EAO between the restricted
  action produced by the local labeling and the action
  by Aut(G) on Z(G) (computed directly for small examples).
  
  The input is a p-group, G.
  
  The output is a subgroup, O, of GL(\phi_1(G) / \phi_2(G)).
  In the case of a group of p-class 2, this is an overgroup
  of the restriction of Aut(G) to Z(G). 
  
  An optional argument if the function used to label lines
  of the projective geometry. By default is uses the slope
  labels for speed. The other option is to use
  
  Genus2Sig
  
  This function will usually cut down the possible lifts
  to feed into the isometry test algorithm of Ivanyos & Qiao.
*/

intrinsic ActionOnCenter (T::TenSpcElt : LineLabel := "SlopeSignature",
                                   ChangeBasis := false) -> GrpMat
  { Compute the best estimate, from local information, of the action of Aut(G) on Z(G) }


	 LineLabel2 :=  LineLabel eq "Genus2Sig" select Genus2Sig else SlopeSignature;
	
  DomT := Domain (T);
  assert #DomT eq 2;
  V := DomT[1];
  d := Dimension (V);
  
  S0 := SystemOfForms (T);
  
  // adjust the system of forms to align with the map associated to T
// if ChangeBasis then
//   assert Type (G) eq GrpPC;
//    e := Ngens (Centre (G));
//    COB := Transpose (Matrix ([ G.i @ h : i in [d+1..d+e] ]))^-1;
//    S := [ ];
//    for i in [1..e] do
//      F := &+ [ COB[i][j] * S0 [j] : j in [1..e] ];
//      Append (~S, F);
//    end for;
//  else
    S := S0;
//  end if;
  
  // find the groups acting on points and lines
  Hp, Hl, f, points, lines, tau := ActionOnProjectiveSpace (S);
  
  // compute a first partition of points
  point_part := ElementaryPointPartition (points : FullPartition := true);
		vprint Autotopism, 1 : "|point_part| =", #point_part;
  
  if #point_part gt 1 then    // replace Hp and Hl with smaller groups
      Hp := Stabiliser (Hp, point_part);
      Hl := Hp @ f;
  end if;
  
  // compute orbits under Hl and use them as the basic line partition
  orbits := Orbits (Hl);
  line_part := [ { i : i in orbits[j] } : j in [1..#orbits] ];
	vprint Autotopism, 1 : "|line_part| =", #line_part;
  
  // refine the line partition
  ref_line_part := RefineLinePartition (line_part, lines, LineLabel2, BasicSigEq);
		vprint Autotopism, 1 : "|ref_line_part| =", #ref_line_part;
  if #ref_line_part gt #line_part then   // cut down group and recompute orbits
    line_part := ref_line_part;
    Hl := Stabiliser (Hl, line_part);
    Hp := Hl @@ f;
  end if;
  
  // lift to GL(e,k)
  if #Hp gt 1 then
    O := Hp @@ tau;
  else
    O := sub < Generic (O) | Identity (Generic (O)) >;
  end if;
  
  // adjust the action
  O := sub < Generic (O) | [ Transpose (O.i) : i in [1..Ngens (O)] ] >;

return O;

end intrinsic;



/*
  ADDED BY PAB ON 29 MAY, 2017
  
  Given T : V x V >--> W, use local invariants to return best 
  possible overgroup of PseudoIsometryGroup(T) restricted to W.
*/

intrinsic ActionOnCodomain (T::TenSpcElt : 
                                 LineLabel := "SlopeSignature",
                                 FullPartition := false
                            ) -> GrpMat
                            
  { Compute the best estimate, from local information, of the action of 
    pseudo-isometry group of T : V x V >--> W acting on its codomain W. }

  LineLabel2 :=  LineLabel eq "Genus2Sig" select Genus2Sig else SlopeSignature;
	
  K := BaseRing (T);	
  assert #Domain (T) eq 2;
  e := Dimension (Codomain (T));  
  S := SystemOfForms (T);
  assert #S eq e;
  
  // find the groups acting on points and lines
  Hp, Hl, f, points, lines, tau, W := ActionOnProjectiveSpace (S);
        vprint Autotopism, 1 : "|points| =", #points;
        vprint Autotopism, 1 : "|lines| =", #lines;
  
  // compute a first partition of points
  point_part := ElementaryPointPartition (points : FullPartition := true);
		vprint Autotopism, 1 : "|point_part| =", #point_part;
  
  if #point_part gt 1 then    // replace Hp and Hl with smaller groups
      Hp := Stabiliser (Hp, point_part);
      Hl := Hp @ f;
  end if;
  
  // compute orbits under Hl and use them as the basic line partition
  orbits := Orbits (Hl);
  line_part := [ { i : i in orbits[j] } : j in [1..#orbits] ];
	vprint Autotopism, 1 : "|line_part| =", #line_part;
  
  // refine the line partition
  ref_line_part := RefineLinePartition (line_part, lines, LineLabel2, BasicSigEq);
		vprint Autotopism, 1 : "|ref_line_part| =", #ref_line_part;
  if #ref_line_part gt #line_part then   // cut down group and recompute orbits
    line_part := ref_line_part;
    Hl := Stabiliser (Hl, line_part);
    Hp := Hl @@ f;
  end if;
  
  // lift to GL(e,k)
  if #Hp gt 1 then
    O := Hp @@ tau;
  else
    O := sub < GL (e, K) | Identity (GL (e, K)) >;
  end if;
  
  // adjust the action
  O := sub < Generic (O) | [ Transpose (O.i) : i in [1..Ngens (O)] ] >;
  
  pp := [ [ points[y] : y in x ] : x in point_part ];
  pp := [ [ Coordinates (W, y.1) : y in x ] : x in pp ];
  lp := [ [ lines[y] : y in x ] : x in line_part ];
  lp := [ [ < Coordinates (W, y.1) , Coordinates (W, y.2) > : y in x ] : x in lp ];

return O, #point_part, #line_part, #points, #lines;

end intrinsic;




