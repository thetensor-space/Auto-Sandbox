/*
  DEVELOPER'S NOTE 
  
  This file contains functions based on the method of Li-Qiao to find an 
  isotopism (or pseudo-isometry) between two given bimaps s1 and s2.
  
  Here's how it works.
  
  We may assume the vitals of s1 and s2 align (frames, adjoint algebras, etc).
  If the (global) ring of adjoints Adj(s1) is too large––which decide by setting
  the global variable ADJOINT_LIMIT––then this method will not be appropriate.
  In this case we should bounce and do something else.
  
  Identify s1 and s2 with their systems of bilinear forms S1 and S2.
  
  We first perform processing on S1, selecting c forms, say T1, in matrix space 
  spanned by S1. Next we consider all tuples T2 in the matrix space spanned by
  S2 which there *could* be an isometry (or principal isotopism) from T1 to T2.
  If there is, one then only has to check if there is an element of the isometry
  group of T1 that modifies this to a pseudo-isometry (or isotopism) from S1 to S2.
  
  The point is that if s1 and s2 are pseudo-isometric (or isotopic) then such
  will always be found this way. 
  
  Before embarking on the search, the main function first calculate how much work
  will be required (in the worst case) to decide the question. If this is too great,
  which we assess the a global variable EXHAUST_LIMIT, then we bounce before we start.
  
  If the RANDOM flag is turned on, however, the function tries to find an isotopism
  (or pseudo-isometry) by random search. This gives rise to a 1-sided Monte Carlo
  test: if true is returned, then we also have a confirmed isotopism; if false is 
  returned, we only know that we failed to find such. 
*/

import "../Util.m" : Adj2;

// global variables
EXHAUST_LIMIT := 10^9;
RANDOM_LIMIT := 10^5;
ADJOINT_LIMIT := 10^5;
INTERNAL_LIMIT := 20;

     // this is O(q^|S|)
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
     
          // subroutine to see if tuple X extends to a pseudo-isometry
          __ExtendToPseudoIsometry := function (s1, s2, t1, X, S2, CAT, ISO)
               T2 := [ &+ [ X[i][j] * S2[j] : j in [1..#S2] ] : i in [1..#X] ];
               t2 := Tensor (T2, 2, 1, CAT);
               isit, g := IsIsometric (t1, t2);
               if isit then
                    // see if something in g . ISO lifts to a pseudo-isometry
                    for x in ISO do
                         isit, h := InducePseudoIsometry (s1, s2, g * x);
                         if isit then
                              return true, < g * x , h >;
                         end if;
                    end for;
               end if;
               return false, _;
          end function;

          // subroutine to see if tuple X extends to an isotopism
          __ExtendToIsotopism := function (s1, s2, t1, X, S2, CAT, ISO, a, b)
               k := BaseRing (s1);
               T2 := [ &+ [ X[i][j] * S2[j] : j in [1..#S2] ] : i in [1..#X] ];
               t2 := Tensor (T2, 2, 1, CAT);
               isit, f, g := IsPrincipallyIsotopic (t1, t2);
               if isit then
                    // see if something in (f,g) . ISO lifts to an isotopism
                    for x in ISO do
                         xa := GL (a, k)!ExtractBlock (x, 1, 1, a, a);
                         xb := GL (b, k)!ExtractBlock (x, a+1, a+1, b, b); 
                         isit, h := InduceIsotopism (s1, s2, < f * xa , g * xb >);
                         if isit then
                              return true, < f * xa , g * xb , h >;
                         end if;
                    end for;
               end if; 
               return false, _; 
          end function;
     

// Eventually the output of the following function should be a homotopism;
// for now it is a pair of a trip of maps

intrinsic LiQiao (s1::TenSpcElt, s2::TenSpcElt : RANDOM := false) -> BoolElt, Tup
  
  { Use exhaustion over partial maps to find an autotopism (or pseudo-isometry) from s1 to s2. }
  
  // decide if the equivalence is pseudo-isometry or isotopism
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
  t2, ISO2, coords2, work2 := __Prec (S1, 2, ranks1, part1, CAT, PI, INTERNAL_LIMIT);
  vprint Autotopism, 1 : "using c = 2, the amount of work needed is", 
     Floor (Log(2,work2)), "bits";
  vprint Autotopism, 1 : "   brute force for c = 2 requires", 
     Floor (Log(2,(#k)^(2*m) * #ISO2)), "bits";
  
  t3, ISO3, coords3, work3 := __Prec (S1, 3, ranks1, part1, CAT, PI, INTERNAL_LIMIT);
  vprint Autotopism, 1 : "using c = 3, the amount of work needed is", 
     Floor (Log(2,work3)), "bits";
  vprint Autotopism, 1 : "   brute force for c = 3 requires", 
     Floor (Log(2,(#k)^(3*m) * #ISO3)), "bits";
  
  if work2 le work3 then
       c := 2;
       t1 := t2;
       ISO := ISO2;
       work := work2;
       coord_sets := coords2;
  else
       c := 3;
       t1 := t3;
       ISO := ISO3;
       work := work3;
       coord_sets := coords3;
  end if;
  
  assert #coord_sets eq c;
  vprint Autotopism, 2 : "decided to use c =", c;
  
       ISO := [ x : x in ISO ];   // the listed isometry or principal isotopism group
       // build all possible images
       L := < part2[coord_sets[i]] : i in [1..c] >; 
       ctups := CartesianProduct (L); 
           
       if work le EXHAUST_LIMIT then     // loop through ctups   
                    
            vprint Autotopism, 2 : "... looping through all possible image tuples";         
            for X in ctups do
                 if PI then
                      flag, tup := __ExtendToPseudoIsometry (s1, s2, t1, X, S2, CAT, ISO);
                 else 
                      flag, tup := __ExtendToIsotopism (s1, s2, t1, X, S2, CAT, ISO, a, b);
                 end if;
                 if flag then
                      return flag, tup;
                 end if;
            end for;
            vprint Autotopism, 2 : "NOT EQUIVALENT: exhausted all possible image tuples"; 
            return false, _;
            
       elif RANDOM then    // try RANDOM_LIMIT choices to find
       
            vprint Autotopism, 2 : "... testing up to", RANDOM_LIMIT, "possible image tuples";
            found := false;
            i := 0;
            while (not found) and (i lt RANDOM_LIMIT) do
                 i +:= 1;
                 X := Random (ctups);
                 if PI then
                      found, tup := __ExtendToPseudoIsometry (s1, s2, t1, X, S2, CAT, ISO);
                 else 
                      found, tup := __ExtendToIsotopism (s1, s2, t1, X, S2, CAT, ISO, a, b);
                 end if;
            end while;
            if found then 
                 return true, tup;
            else
                 vprint Autotopism, 2 : 
                    "FAIL: after a random search, no isotopism / pseudo-isometry was found";
                 return false, _; 
            end if;
             
       else
  
            vprint Autotopism, 2 : 
               "FAIL: work exceeds exhaust limit; you can set the RANDOM flag to <true> and try again";      
            return false, _;
  
       end if;
    

end intrinsic;


/*

d:=8;e:=4;p:=3; TS := KTensorSpace(GF(p),[d,d,e]);
t := Random(TS);
s := Random(TS);
time LiQiao(t,s);

*/