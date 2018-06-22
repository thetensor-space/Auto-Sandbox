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


r := 4;
p := 13;
k := GF (p);
V := VectorSpace (k, r);
SC_Theorem_5_3 := [
  V![1,1,5,3],
  V![-4,-4,0,-2],
  V![2,4,-4,-2],
  V![-3,-1,1,3],
  V![2,0,4,4],
  V![-3,-5,-1,-1]
     ];
SC_Theorem_5_3 := [ [ Integers ()!(w[i]) : i in [1..r] ] : w in SC_Theorem_5_3 ];
G := IACAlgebraToUCSGroup (p, r, SC_Theorem_5_3);
T := pCentralTensor (G);
D, DW := Der (T);
A := AdjointAlgebra (T);
"dimension of Der(G) =", Dimension (D);
"dimension of Der(G)|_W =", Dimension (DW);
"dimension of Adj(G) =", Dimension (A);
isit, L := HasLeviSubalgebra (D);
"dimension of Levi subalgebra =", Dimension (L);
E, F, H := ChevalleyBasis (L);
"|E| =", #E, "    |H| =", #H;
LVW := sub < MatrixLieAlgebra (k, 8) | [ ExtractBlock (L.i, 5, 5, 8, 8) : i in 
[1..Ngens(L)] ] >;
N := SimilaritiesOfSemisimpleLieModule (LVW, 4);



// example of block matrix Lie algebras to test code with
/*
k := GF (5);
Vblocks := [ 2 , 2 , 2 ];
d := &+ Vblocks;
Wblocks := [ 3 , 3 ];
e := &+ Wblocks;
gens := [ ];
ML := MatrixLieAlgebra (k, d+e);
for i in [1,2] do
  x := DiagonalJoin(< Random (MatrixAlgebra (k, a)) : a in Vblocks >);
  y := DiagonalJoin(< Random (MatrixAlgebra (k, b)) : b in Wblocks >);
  Append (~gens, ML!DiagonalJoin (x, y));
end for;
A := sub < ML | gens >;
RA := NilRadical (A);
"dim(A) =", Dimension (A);
"dim(RA) =", Dimension (RA);
isit, L0 := HasLeviSubalgebra (A);
"dim(L0) =", Dimension (L0);
RL0 := NilRadical (L0);
"dim(RL0) =", Dimension (RL0);

// scramble
g := Random (GL (d, k));   h := Random (GL (e, k));
x := DiagonalJoin (g, h);
L := sub < Generic (L0) | [ x * Matrix (L0.i) * x^-1 : i in [1..Ngens (L0)] ] >;
*/






