// examples from Oberwolfach
/*
G1 := PCGroup(\[ 12, -5, 5, 5, 5, 5, 5, 5, 5, 5, -5, 5, 5, 2203125121, 4148438402, 
225000194, 4406256003, 1875001215, 442500267, 2507820016, 562501528, 5625340, 
10125225005, 1209420017, 433134029, 138376841, 23400413, 19360687506, 
1804950018, 656302530, 141760542, 13652154, 262986, 11070000007, 3301500019, 
37800031, 69060043, 32112055, 182467, 168559, 16706250008, 1738125020, 
668250032, 174150044, 405056, 3726068, 70280, 68132 ]);
*/

// a smallish group that Josh and I should look at with our code
/*
G2 := PCGroup(\[ 9, -5, 5, 5, 5, 5, -5, 5, 5, 5, 56341, 422552, 2109521, 2817003, 
140881 ]);
*/

/*----- some constructions for testing Lie algebra normalizer code ----*/

__KMatrixSpaceToLieAlgebra := function (X)
  k := BaseRing (X);
  d := Nrows (X.1);
  ML := MatrixLieAlgebra (k, d);
return sub < ML | [ Matrix (X.i) : i in [1..Ngens (X)] ] >;
end function;                           


MyNaturalRep := function (name, k : SCRAMBLE := false, CHEVALLEY := false)

     L0 := LieAlgebra (name, k);
     stan := StandardRepresentation (L0);
     n := Degree (Image (stan));
     G := GL (n, k); 
         
     if SCRAMBLE then 
          g := Random (G); 
     else 
          g := Identity (G); 
     end if;
     
     nat_gens := [ g * Matrix (L0.i @ stan) * g^-1 : i in [1..Ngens (L0)] ];
     L := sub < MatrixLieAlgebra (k, n) | nat_gens >;
     
     if CHEVALLEY then
          E, F, H := ChevalleyBasis (L0);
          E := [ g * Matrix (E[i] @ stan) * g^-1 : i in [1..#E] ];
          F := [ g * Matrix (F[i] @ stan) * g^-1 : i in [1..#F] ];
          return L, E, F;
     end if;
     
return L, _, _;

end function;


MyAdjointRep := function (name, k : SCRAMBLE := false, CHEVALLEY := false)

     L0 := LieAlgebra (name, k);
     ad := AdjointRepresentation (L0);
     n := Degree (Image (ad));
     G := GL (n, k); 
         
     if SCRAMBLE then 
          g := Random (G); 
     else 
          g := Identity (G); 
     end if;
     
     adL_gens := [ g * Matrix (L0.i @ ad) * g^-1 : i in [1..Ngens (L0)] ];
     adL := sub < MatrixLieAlgebra (k, n) | adL_gens >;
     
     if CHEVALLEY then
          E, F, H := ChevalleyBasis (L0);
          adE := [ g * Matrix (E[i] @ ad) * g^-1 : i in [1..#E] ];
          adF := [ g * Matrix (F[i] @ ad) * g^-1 : i in [1..#F] ];
          return adL, adE, adF;
     end if;
     
return adL, _, _;

end function;

/* TO DO: make a generic symmetric square function */
sl3_example := function (k)
     MS := KMatrixSpace (k, 3, 3);
     S1 := MS![1,0,0,0,0,0,0,0,0];
     S2 := MS![0,0,0,0,1,0,0,0,0];
     S3 := MS![0,0,0,0,0,0,0,0,1];
     S4 := MS![0,1,0,1,0,0,0,0,0];
     S5 := MS![0,0,1,0,0,0,1,0,0];
     S6 := MS![0,0,0,0,0,1,0,1,0];
     M := KMatrixSpaceWithBasis ([S1, S2, S3, S4, S5, S6]);
     L0 := LieAlgebra ("A2", k);
     f := StandardRepresentation (L0);
     E0, F0, H0 := ChevalleyBasis (L0);
     stan := Image (f);
     stE0 := [ Matrix (E0[i] @ f) : i in [1..#E0] ];
     stF0 := [ Matrix (F0[i] @ f) : i in [1..#F0] ];
     X := [ Matrix (stan.i) : i in [1..Ngens (stan)] ];
     gens := [ ];
     for i in [1..Ngens (stan)] do
          Append (~gens, 
            Matrix ([ Coordinates (M, X[i] * M.j + M.j * Transpose (X[i])) :
                         j in [1..6] ])
                 );
     end for;
     mat := MatrixLieAlgebra (k, 6);
     L := sub < mat | gens >;
     E := [ ];  F := [ ];
     for i in [1..#stE0] do
          Append (~E, 
            Matrix ([ Coordinates (M, stE0[i] * M.j + M.j * Transpose (stE0[i])) :
                         j in [1..6] ])
                 );
          Append (~F, 
            Matrix ([ Coordinates (M, stF0[i] * M.j + M.j * Transpose (stF0[i])) :
                         j in [1..6] ])
                 );
     end for;    
return L, E, F; 
end function;



// The following functions were all ported over by PAB from "simple-mods.m" on 6/5/2018


// Natural module for Chevalley Lie algberas
__KMatrixSpaceToLieAlgebra := function (X)
  k := BaseRing (X);
  d := Nrows (X.1);
  ML := MatrixLieAlgebra (k, d);
return sub < ML | [ Matrix (X.i) : i in [1..Ngens (X)] ] >;
end function;

NaturalModule := function(Name, q)
  return MatrixLieAlgebra(Name, GF(q));
end function;

// Adjoint representation for Chevalley Lie algebras
AdjointModule := function(Name, q)
  L := LieAlgebra(Name, GF(q));
  t := Tensor(L);
  D := DerivationAlgebra(t);
  Der := Induce(D, 0);
  assert SemisimpleType(Der) eq Name;
  return Der;
end function;

// 7-dimensional G2 module
G2Module := function(q)
  Oct := OctonionAlgebra(GF(q), -1, -1, -1);
  t := Tensor(Oct);
  D := DerivationAlgebra(t);
  Der := Induce(D, 0);
  assert SemisimpleType(Der) eq "G2";
  M := RModule (Der);
  assert not IsIrreducible (M);
  assert exists (N){ X : X in Submodules (M) | Dimension (X) eq 7 };
  ML := MatrixLieAlgebra (GF (q), 7);
  L := sub < ML | [ ActionGenerator (N, i) : i in [1..#ActionGenerators (N)] ] >;
  return L;
end function;


// 28-dimensional D4 module
D4Module := function(q)
  Oct := OctonionAlgebra(GF(q), -1, -1, -1);
  t := Tensor(Oct);
  ChangeTensorCategory(~t, HomotopismCategory(3));
  D := DerivationAlgebra(t);
  Der := Induce(D, 0);
  L := Der/SolvableRadical(Der);
  t := Tensor(L);
  D := DerivationAlgebra(t);
  Der := Induce(D, 0);
  assert SemisimpleType(Der) eq "D4";
  return Der;
end function;

// sp(2n, q). Returned as a vector space.
SpModule := function(n, q)
  MS := KMatrixSpace(GF(q), n, n);
  B1 := [DiagonalJoin(x, -Transpose(x)) : x in Basis(MS)];
  upt := {x : x in Basis(MS) | IsUpperTriangular(x)};
  diag := {x : x in upt | IsDiagonal(x)};
  sym := diag join {x + Transpose(x) : x in upt diff diag};
  B2 := [InsertBlock(ZeroMatrix(GF(q), 2*n, 2*n), x, 1, n+1) : x in sym];
  B3 := [InsertBlock(ZeroMatrix(GF(q), 2*n, 2*n), x, n+1, 1) : x in sym];
  MS := KMatrixSpace(GF(q), 2*n, 2*n);
  S := sub< MS | B1, B2, B3 >;
  L := __KMatrixSpaceToLieAlgebra (S);
  return L;
end function;

// o(2n, q). Returned as a vector space.
EvenOModule := function(n, q)
  MS := KMatrixSpace(GF(q), n, n);
  B1 := [DiagonalJoin(x, -Transpose(x)) : x in Basis(MS)];
  upt := {x : x in Basis(MS) | IsUpperTriangular(x) and not IsDiagonal(x)};
  alt := {x + Transpose(x) : x in upt};
  B2 := [InsertBlock(ZeroMatrix(GF(q), 2*n, 2*n), x, 1, n+1) : x in alt];
  B3 := [InsertBlock(ZeroMatrix(GF(q), 2*n, 2*n), x, n+1, 1) : x in alt];
  MS := KMatrixSpace(GF(q), 2*n, 2*n);
  S := sub< MS | B1, B2, B3 >;
  L := __KMatrixSpaceToLieAlgebra (S);
  return L;
end function;

// o(2n+1, q). Returned as a vector space.
OddOModule := function(n, q)
  MS := KMatrixSpace(GF(q), n, n);
  B1 := [DiagonalJoin(<ZeroMatrix(GF(q), 1, 1), x, -Transpose(x)>) : 
    x in Basis(MS)];
  upt := {x : x in Basis(MS) | IsUpperTriangular(x) and not IsDiagonal(x)};
  alt := {x + Transpose(x) : x in upt};
  B2 := [InsertBlock(ZeroMatrix(GF(q), 2*n+1, 2*n+1), x, 2, n+2) : x in alt];
  B3 := [InsertBlock(ZeroMatrix(GF(q), 2*n+1, 2*n+1), x, n+2, 2) : x in alt];
  MS := KMatrixSpace(GF(q), 2*n+1, 2*n+1);
  X := [MS.i - Transpose(MS.(i+n)) : i in [2..n+1]];
  Y := [MS.(n+i) - Transpose(MS.i) : i in [2..n+1]];
  S := sub< MS | B1, B2, B3, X, Y >;
  L := __KMatrixSpaceToLieAlgebra (S);
  return L;
end function;

// 27-dimensional F4 module
F4Module := function(q)
  A := ExceptionalJordanCSA (GF(q));
  t := Tensor(A);
  D := DerivationAlgebra(t);
  Der := Induce(D, 0);
  assert SemisimpleType(Der) eq "F4";
  return Der;
end function;









