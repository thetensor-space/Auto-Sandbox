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
