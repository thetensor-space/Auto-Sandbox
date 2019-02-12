        /*----- some labeling functions for bimaps -------*/

// a label for points that uses the dimension of the radical of the corresponding form       
RANK_LABEL := function (z, t)
  F := SystemOfForms (t);
return Dimension ( Nullspace (&+ [ (z.1)[i] * F[i] : i in [1..#F] ]));
end function;

// the quick and dirty way to label lines using the slope invariant
SLOPE_LABEL := function (m, t)
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
GENUS2_LABEL := function (m, t)
  F := SystemOfForms (t);
  s := Tensor ([ &+ [ (m.1)[i] * F[i] : i in [1..#F] ], 
                 &+ [ (m.2)[i] * F[i] : i in [1..#F] ] ], 2, 1); 
return Genus2Signature (s);
end function;
