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

SmallestG2Module := function(q)
  L := G2Module(q);
  CT := ExteriorCotensorSpace(VectorSpace(GF(q), 7), 2);
  t := AsTensor(CT);
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

// Returns a tensor from the Heisenberg group over the local algebra 
// A = K[x]/(a(x)^c), where a is irreducible in K[x] and c > 1. 
// Here g is the codimension of the central factor in A. 
LocalHeisenberg := function(g, a, c)
  P := Parent(a); 
  I := ideal< P | a^c >;
  t := Tensor(P/I);
  F := SystemOfForms(t);
  Forms := F[#F-g+1..#F];
  return Tensor(Forms, 2, 1);
end function;

MySemisimpleMatrixAlgebra := function (k, stypes, rtypes : SCRAMBLE := false)  
  // calculate the degree of the representation and the number of generators
  n := 0;
  m := 0;
  for i in [1..#stypes] do
      L := LieAlgebra (stypes[i], k);
      r := rtypes[i];
      m +:= Ngens (L);
      n +:= r[1] * Degree (Image (StandardRepresentation (L)));
      n +:= r[2] * Degree (Image (AdjointRepresentation (L)));
  end for;  
  MLie := MatrixLieAlgebra (k, n);
  gens := [ MLie!0 : i in [1..m] ];
  pos := 1;
  g := 0;
  for i in [1..#stypes] do
      J := LieAlgebra (stypes[i], k);
      r := rtypes[i];
          if r[1] gt 0 then
              Jrep := StandardRepresentation (J);
              d := Degree (Image (Jrep));
              for s in [1..r[1]] do
                  for j in [1..Ngens (J)] do
                      InsertBlock (~gens[g+j], J.j @ Jrep, pos, pos);
                  end for;
                  pos +:= d;
              end for;
          end if;
          if r[2] gt 0 then
              Jrep := AdjointRepresentation (J);
              d := Degree (Image (Jrep));
              for s in [1..r[2]] do
                  for j in [1..Ngens (J)] do
                      InsertBlock (~gens[g+j], J.j @ Jrep, pos, pos);
                  end for;
                  pos +:= d;
              end for;
          end if; 
      g +:= Ngens (J);
  end for;  
  L := sub < MLie | gens >;
  if SCRAMBLE then
       G := GL (n, k);
       g := Random (G);
       L := sub < MLie | [ g * Matrix (gens[i]) * g^-1 : i in [1..#gens] ] >;
  end if;
return L;
end function; 


/*
  Given irreducible representations of L1 and L2, return their tensor
  product––an irreducible representation of L1 + L2.
*/
MyTensorProduct := function (L1, L2)
  n1 := Degree (L1);
  n2 := Degree (L2);
  k := BaseRing (L1);   assert k eq BaseRing (L2);
  MLie := MatrixLieAlgebra (BaseRing (L1), n1 * n2);
  f1 := hom < Generic (L1) -> MLie | 
         x :-> MLie!(KroneckerProduct (x, Identity (MatrixAlgebra (k, n2)))) >;
  f2 := hom < Generic (L2) -> MLie | 
         x :-> MLie!(KroneckerProduct (Identity (MatrixAlgebra (k, n1)), x)) >;
  J1 := sub < MLie | [ L1.i @ f1 : i in [1..Ngens (L1)] ] >;
  J2 := sub < MLie | [ L2.i @ f2 : i in [1..Ngens (L2)] ] >;
  L := J1 + J2;
return L, f1, f2;
end function;


/*
  Designed to test conjugacy function for semisimple algebras.
    * TYPE1 and TYPE2 are the iso types of the two minimal ideals of L.
    * L < gl(V) is represented as U1 + U1 + U3, where:
      U1 is the natural module for TYPE1
      U2 is the natural module for TYPE2
      U3 is the tensor product of these ... irreducible for TYPE1 + TYPE2
  Function produces two scrambled copies of an algebra with this structure.
*/
SS_Construction1 := function (k, TYPE1, TYPE2)
  X1 := MatrixLieAlgebra (TYPE1, k);
  X2 := MatrixLieAlgebra (TYPE2, k);
  n1 := Degree (X1);
  n2 := Degree (X2);
  Y, f1, f2 := MyTensorProduct (X1, X2);
  n3 := Degree (Y);
  MLie := MatrixLieAlgebra (k, n1 + n2 + n3);
  L := sub < MLie |
        [ DiagonalJoin (X1.i, DiagonalJoin (X2!0, X1.i @ f1)) : i in [1..Ngens (X1)] ] cat
        [ DiagonalJoin (X1!0, DiagonalJoin (X2.i, X2.i @ f2)) : i in [1..Ngens (X2)] ]
           >;
  G := GL (n1 + n2 + n3, k);
  g1 := Random (G);
  g2 := Random (G);
  L1 := sub < MLie | [ g1 * Matrix(L.i) * g1^-1 : i in [1..Ngens (L)] ] >;
  L2 := sub < MLie | [ g2 * Matrix(L.i) * g2^-1 : i in [1..Ngens (L)] ] >;
return L1, L2;
end function;




// block simple
/*
k := GF (5);
type := "A2";
L0 := LieAlgebra (type, k);
NAT := 1; AD := 0;
rho_nat := StandardRepresentation (L0);
rho_ad := AdjointRepresentation (L0);
n := NAT * Degree (Image (rho_nat)) + AD * Degree (Image (rho_ad));
MLie := MatrixLieAlgebra (k, n);
gens := [ MLie!0 : i in [1..Ngens (L0)] ];
pos := 1;
for i in [1..NAT] do
    for j in [1..Ngens (L0)] do
        InsertBlock (~gens[j], L0.j @ rho_nat, pos, pos);
    end for;
    pos +:= Degree (Image (rho_nat));
end for;
for i in [1..AD] do
    for j in [1..Ngens (L0)] do
        InsertBlock (~gens[j], L0.j @ rho_ad, pos, pos);
    end for;
    pos +:= Degree (Image (rho_ad));
end for;
L := sub < MLie | gens >;
// scrambled copies
g1 := Random (GL (n, k));   g2 := Random (GL (n, k));
L1 := sub < MLie | [ g1 * Matrix (L.i) * g1^-1 : i in [1..Ngens (L)] ] >;
L2 := sub < MLie | [ g2 * Matrix (L.i) * g2^-1 : i in [1..Ngens (L)] ] >;
*/







