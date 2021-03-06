/* 
  p-group constructor functions taken from the paper
  "Duality between p-groups with three characteristic subgroups
     and semisimple anti-commutative algebras," 
  by S.P.Glasby, A.M.Ribeiro, and C.Schneider
*/

IACAlgebraToUCSGroup := function (p, r, SC)
assert #SC eq Binomial (r, 2);
     F := FreeGroup (2*r);
     R := [ F.i^p = F.(r+i) : i in [1..r] ];
     R cat:= [ F.(r+i)^p = 1 : i in [1..r] ];
     R cat:= [ F.(r+i)^(F.j) = F.(r+i) : i in [1..r], j in [1..2*r] | j lt (r+i) ];
     pos := 1;
     for i in [1..r] do
         for j in [i+1..r] do
             cij := SC[pos];
             wij := &* [ F.(r+k)^(cij[k]) : k in [1..r] ];
             Append (~R, F.j^F.i = F.j * wij);
             pos +:= 1;
         end for;
     end for;
     G := quo < GrpGPC : F | R >;
return PCGroup (G);
end function; 

Hypothesis_6_1 := function (b)
     D := Divisors (b^2 + b - 1);
     n := Random ({ d : d in D | d ne 1 });
     r := Modorder (b, n);
     // find prime q such that n divides q-1
     assert exists (q){ p : p in PrimesUpTo (10^4) | (p-1) mod n eq 0 };
     Fq := GF (q);
     xi := PrimitiveElement (Fq);
     Z := Matrix (Fq, r, r, [0 : i in [1..r^2]]);
     A := InsertBlock (Z, Identity (MatrixAlgebra (Fq, r-1)), 1, 2);
     A[r][1] := 1;
     B := DiagonalMatrix ([ xi^(b^i) : i in [0..r-1] ]);
     H := sub < GL (r, Fq) | A , B >;
     // build algebra in Corollary 6.3.
     V := VectorSpace (Fq, r);
     SC := [ V.r ] cat [ V!0 : i in [3..r-1] ] cat [ -V.(r-1) ];
     for j in [2..r-1] do
         SC cat:= ([ V.(j-1) ] cat [ V!0 : i in [j+2..r] ]);
     end for;
assert #SC eq Binomial (r, 2);
     SC := [ [ Integers ()!(w[i]) : i in [1..r] ] : w in SC ];
     G := IACAlgebraToUCSGroup (q, r, SC);
return H, G;
end function; 












