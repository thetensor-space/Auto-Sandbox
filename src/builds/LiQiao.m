/*
  Developer's note. This file contains functions based on the method of Li-Qiao
  to find an autotopism (or pseudo-isometry) between two given bimaps.
*/

import "../Util.m" : Adj2;

EXHAUST_LIMIT := 10^9;
ADJOINT_LIMIT := 10^5;
INTERNAL_LIMIT := 20;

     // this is O(q^m)
     __PartitionOnRank := function (S)
       m := #S;
       k := BaseRing (Parent (S[1]));
       V := VectorSpace (k, m);
       LC := [ v : v in V | v ne 0 ];
       ranks := { Rank (&+ [ v[j] * S[j] : j in [1..m] ]) : v in LC };
       ranks := [ r : r in ranks ];
       I := [1..#ranks];
       part := [ [ v : v in LC | Rank (&+ [ v[j] * S[j] : j in [1..m] ]) eq r ] : 
                  r in ranks ];
       Sort (~I, func<x,y|#part[x]-#part[y]>);
       ranks := [ ranks[i] : i in I ];
       part := [ part[i] : i in I ];
     return ranks, part;
     end function;

     /*
       This function will require some tweaking.
       
       Here's the idea. We want ideally to choose a constant c 
       and a basis for a c-dimensional subspace of <S> in such
       a way that the number of possible images of this basis
       is minimized. But also, insofar as we can, we also wish
       to minimize the order of the isometry group of the bimap
       defined by these basis elements.
       
       For the time being, let's assume that we're only going
       to use c = 2 or c = 3. We'll do a bit of preconditioning
       with both to try to determine the best option.
     */
     
     __Prec := function (S, c, ranks, part, CAT, flag, LIMIT)      
           
       k := BaseRing (Parent (S[1]));
       m := #S;
       V := VectorSpace (k, m);  
       
            // find enough of part to span a c-space
       dims := [ Dimension (sub<V|part[i]>) : i in [1..#part] ];
       coord_sets := [ ];
       for i in [1..#dims] do
            coord_sets cat:= [ i : j in [1..dims[i]] ];
       end for;
       coord_sets := [ coord_sets[i] : i in [1..c] ];
       work := &* [ #part[i] : i in coord_sets ];
          
            // search for forms with small isometry group
       tensors := [ ];
       isoms := [ ];
       for i in [1..LIMIT] do
            repeat
                 vecs := [ Random (part[i]) : i in coord_sets ];
            until Dimension (sub<V|vecs>) eq c;
            T := [ &+ [ vecs[a][j] * S[j] : j in [1..m] ] : a in [1..#vecs] ];
            t := Tensor (T, 2, 1, CAT);
            Append (~tensors, t);
            if flag then
                 Append (~isoms, IsometryGroup (t));
            else
                 Append (~isoms, PrincipalIsotopismGroup (t));
            end if;
       end for;   
         
       min, i := Minimum ([ #I : I in isoms ]);
       work *:= #isoms[i];
       
     return tensors[i], isoms[i], coord_sets, work;
     end function;
    

     // this is the old preconditioning function that we'll keep around for now
/*
     __Precondition := function (S, c, flag, LIMIT)
       inds := [ ];
       dims := [ ];
       c_sets := Subsets ({1..#S}, c);
       for j in [1..LIMIT] do
            I := Random (c_sets);
            Append (~inds, I);
            T := [ S[i] : i in I ];
            t := Tensor (T, 2, 1);
            if { Dimension (Radical (t)[i]) : i in [1..#Radical (t)] } eq {0} then
                 if flag then
                      Append (~dims, Dimension (AdjointAlgebra (t)));
                 else
                      Append (~dims, Dimension (Adj2 (T, T)));
                 end if;
            end if;
       end for;
       d := Minimum (dims);
       j := Position (dims, d);
       I := inds[j];
     return I;
     end function;
*/
     


// Eventually the output of the following function should be a homotopism;
// for now it is a pair of a trip of maps

intrinsic LiQiao (s1::TenSpcElt, s2::TenSpcElt : MINC := 3 ) -> BoolElt, Tup
  
  { Use exhaustion over partial maps to find an autotopism (or pseudo-isometry) from s1 to s2. }
  
  R := RepeatPartition (TensorCategory (s1));
  require R eq RepeatPartition (TensorCategory (s2)) : "s1 and s2 are incomparable";
  
  CAT := TensorCategory (s1);
  
  if R eq {{0},{1},{2}} then
       PI := false;   // pseudo-isometry flag
       vprint Autotopism, 2 : "equivalence is AUTOTOPISM";
  elif R eq {{0},{1,2}} then
       PI := true;
       vprint Autotopism, 2 : "equivalence is PSEUDO-ISOMETRY";
  else
       vprint Autotopism, 2 : "tensors do not have valence 2 (they are not bimaps)";
       return false, _;
  end if;
  
  k := BaseRing (s1);     q := #k;
  
  S1 := SystemOfForms (s1);
  S2 := SystemOfForms (s2);
  m := #S1;
  if #S2 ne m then
       vprint Autotopism, 2 : "NOT EQUIVALENT: different codomains";
       return false, _;
  end if;
  
  if m lt 3 then
       vprint Autotopism, 2 : "INAPPROPRIATE INPUT: genus at most 2";
       return false, _;
  end if;
  
  // compare global adjoint algebras
  if PI then
       A1 := AdjointAlgebra (s1);
       A2 := AdjointAlgebra (s2);
  else
       A1 := Adj2 (S1, S1);
       A2 := Adj2 (S2, S2);
       a := Nrows (S1[1]);
       b := Ncols (S1[1]);
  end if;
       // could insert something more subtle here, but dimension if fine for now
  if Dimension (A1) ne Dimension (A2) then
       vprint Autotopism, 2 : "NOT EQUIVALENT: adjoint algebras have different dimensions";
       return false, _;
  end if;
  
  // make sure these adjoint algebras are not too large
  if #A1 gt ADJOINT_LIMIT then     // we should use a different method
       vprint Autotopism, 2 : "FAIL: (global) adjoint algebras are already too large", #A1;
       return false, _;
  end if;
  
  // compute rank information for the two tensors
  ranks1, part1 := __PartitionOnRank (S1);
  ranks2, part2 := __PartitionOnRank (S2);
  if ((ranks1 ne ranks2) or ([ #p : p in part1 ] ne [ #p : p in part2 ])) then
       vprint Autotopism, 2 : "NOT EQUIVALENT: different rank data";
       return false, _;
  end if;
  
  vprint Autotopism, 2 : "the set of possible ranks is", ranks1;
  
  // before we precondition based on points, ensure this is even feasible ...
  if (#k)^m gt EXHAUST_LIMIT then
       vprint Autotopism, 2 : "FAIL: there are already too many points to precondition";
       return false, _;
  end if;

  // compare the worst-case work with c = 2 and c = 3 and take the smaller
  t2, ISOM2, coords2, work2 := __Prec (S1, 2, ranks1, part1, CAT, PI, INTERNAL_LIMIT);
  vprint Autotopism, 1 : "using c = 2, the amount of work needed is", 
     Floor (Log(2,work2)), "bits";
  vprint Autotopism, 1 : "   brute force for c = 2 requires", 
     Floor (Log(2,(#k)^(2*m) * #ISOM2)), "bits";
  
  t3, ISOM3, coords3, work3 := __Prec (S1, 3, ranks1, part1, CAT, PI, INTERNAL_LIMIT);
  vprint Autotopism, 1 : "using c = 3, the amount of work needed is", 
     Floor (Log(2,work3)), "bits";
  vprint Autotopism, 1 : "   brute force for c = 3 requires", 
     Floor (Log(2,(#k)^(3*m) * #ISOM3)), "bits";
  
  if work2 le work3 then
       c := 2;
       t1 := t2;
       ISOM := ISOM2;
       work := work2;
       coord_sets := coords2;
  else
       c := 3;
       t1 := t3;
       ISOM := ISOM3;
       work := work3;
       coord_sets := coords3;
  end if;
  
  assert #coord_sets eq c;
  vprint Autotopism, 2 : "using c =", c;
           
       if work le EXHAUST_LIMIT then
       
            ISOM := [ x : x in ISOM ];  
            
            // build all possible images
            L := < part2[coord_sets[i]] : i in [1..c] >; 
            ctups := CartesianProduct (L); 
                  
            for X in ctups do
            
                 T2 := [ &+ [ X[i][j] * S2[j] : j in [1..m] ] : i in [1..c] ];
                 t2 := Tensor (T2, 2, 1, CAT);
                 if PI then
                      isit, g := IsIsometric (t1, t2);
                      if isit then
                           // see if something in g . ISOM lifts to a pseudo-isometry
                           for x in ISOM do
                                isit, h := InducePseudoIsometry (s1, s2, g * x);
                                if isit then
                                     return true, < g * x , h >;
                                end if;
                           end for;
                      end if;
                 else
                      isit, f, g := IsPrincipallyIsotopic (t1, t2);
                      if isit then
                           // see if something in (f,g) . ISOM lifts to an autotopism
                           for x in ISOM do
                                xa := GL (a, k)!ExtractBlock (x, 1, 1, a, a);
                                xb := GL (b, k)!ExtractBlock (x, a+1, a+1, b, b); 
                                isit, h := InduceIsotopism (s1, s2, < f * xa , g * xb >);
                                if isit then
                                     return true, < f * xa , g * xb , h >;
                                end if;
                           end for;
                      end if;
                 end if;
                 
            end for;
            
       else
  
            vprint Autotopism, 2 : "FAIL: it's just too hard a problem";
            
            return false, _;
  
       end if;
   
  vprint Autotopism, 2 : "NOT EQUIVALENT: exhausted all possible lifts"; 
   
return false, _; 

end intrinsic;


/*

d:=8;e:=4;p:=3; TS := KTensorSpace(GF(p),[d,d,e]);
t := Random(TS);
s := Random(TS);
time LiQiao(t,s);

*/