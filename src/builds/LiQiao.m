/*
  Developer's note. This file contains functions based on the method of Li-Qiao
  to find an autotopism (or pseudo-isometry) between two given bimaps.
*/

import "../Util.m" : Adj2;

ADJOINT_LIMIT := 10^5;
EXHAUST_LIMIT := 10^8;

     // chooses a c-subset of S whose adjoints are small
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


// Eventually the output of the following function should be a homotopism;
// for now it is a pair of a trip of maps

intrinsic LiQiao (s1::TenSpcElt, s2::TenSpcElt : MINC := 3 ) -> BoolElt, Tup
  
  { Use exhaustion over partial maps to find an autotopism (or pseudo-isometry) from s1 to s2. }
  
  R := RepeatPartition (TensorCategory (s1));
  require R eq RepeatPartition (TensorCategory (s2)) : "s1 and s2 are incomparable";
  
  CAT := TensorCategory (s1);
  
  if R eq {{0},{1},{2}} then
       PI := false;   // pseudo-isometry flag
  elif R eq {{0},{1,2}} then
       PI := true;
  else
       vprint Autotopism, 2 : "tensors do not have valence 2 (they are not bimaps)";
       return false, _;
  end if;
  
  k := BaseRing (s1);     q := #k;
  
  S1 := SystemOfForms (s1);
  S2 := SystemOfForms (s2);
  m := #S1;
  if #S2 ne m then
       vprint Autotopism, 2 : "the bimaps have different codomains";
       return false, _;
  end if;
  
  if m lt 3 then
       vprint Autotopism, 2 : "bimaps have genus at most 2 ... please go away";
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
       vprint Autotopism, 2 : "bimaps have adjoint algebras of differing dimensions";
       return false, _;
  end if;
  
  // make sure these adjoint algebras are not too large
  if #A1 gt ADJOINT_LIMIT then
       vprint Autotopism, 2 : "the (global) adjoint algebras are already too large";
       return false, _;
  end if;

  // find the values of c we can hope to deal with
  CONSTANTS := [ c : c in [MINC..m] | q ^ (c * m) le EXHAUST_LIMIT ];
  
  

  for c in CONSTANTS do     // probably c = 3 is best, but we might get away with c = 2
  
       vprint Autotopism, 1 : "(q = ", q, ", m = ", m, ", c = ", c, 
          " q^m = ", q^m, " q^(cm) = ", q^(c*m), ")";
       
       
       I := __Precondition (S1, c, PI, 10);
       t1 := Tensor ([ S1[i] : i in I ], 2, 1, CAT);
       if PI then
            ISOM := IsometryGroup (t1);
       else
            ISOM := PrincipalIsotopismGroup (t1);
       end if;
       vprint Autotopism, 1 : "Isom(t1) has order", #ISOM;
       vprint Autotopism, 1 : "\tNumber of rounds ", q^(c*m), " (Bits ", 
          Ceiling(Log(2,q^(c*m))), ")";
       vprint Autotopism, 1 : "\tMin work if nonisomorphic: ", 
          q^(c*m)*#ISOM, 
          "(Bits ", Ceiling(Log(2,q^(c*m)*#ISOM)), ")";

       if #ISOM le ADJOINT_LIMIT then
       
            ISOM := [ x : x in ISOM ];     // seems sensible to list this once
       
            // build all possible images
            MS := KMatrixSpace (k, c, m);     // < EXHAUST_LIMIT
            for X in MS do
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
               vprint Autotopism, 1 : "GO AWAY!";
       end if;
  
  end for;
   
  vprint Autotopism, 1 : "looped through all possible images and failed to lift"; 
   
return false, _; 

end intrinsic;


/*

d:=8;e:=4;p:=3; TS := KTensorSpace(GF(p),[d,d,e]);
t := Random(TS);
s := Random(TS);
time LiQiao(t,s);

*/