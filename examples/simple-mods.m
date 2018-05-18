// Natural module for Chevalley Lie algberas
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

// 8-dimensional G2 module
G2Module := function(q)
  Oct := OctonionAlgebra(GF(q), -1, -1, -1);
  t := Tensor(Oct);
  D := DerivationAlgebra(t);
  Der := Induce(D, 0);
  assert SemisimpleType(Der) eq "G2";
  return Der;
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
  L := sub< MS | B1, B2, B3 >;
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
  L := sub< MS | B1, B2, B3 >;
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
  L := sub< MS | B1, B2, B3, X, Y >;
  return L;
end function;
