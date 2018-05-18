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

MyAdjointRep := function (name, k : Scramble := false)
     L := LieAlgebra (name, k);
     E, F, H := ChevalleyBasis (L);
     ad := AdjointRepresentation (L);
     n := Degree (Image (ad));
     G := GL (n, k);     
     if Scramble then 
          g := Random (G); 
     else 
          g := Identity (G); 
     end if;
     
     adE := [ g * Matrix (E[i] @ ad) * g^-1 : i in [1..#E] ];
     adF := [ g * Matrix (F[i] @ ad) * g^-1 : i in [1..#F] ];
     adL_gens := [ g * Matrix (L.i @ ad) * g^-1 : i in [1..Ngens (L)] ];
     adL := sub < MatrixLieAlgebra (k, n) | adL_gens >;     
return adL, adE, adF;
end function;


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



