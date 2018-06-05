/* 
   some constructor functions for 3-step groups: 
   split extensions of class 2 p-groups by (semi)
   simple groups defined in characteristic p.
*/

// returns H = O_p(H) : Omega, where R = O_p(H) is class 2 exponent p,
// constructed as block upper unitriangular matrices, and Omega = SL(2,p)
// is embedded at various random locations along the leading diagonal.
basic_SL2 := function (p, l, m, n : BLOCK := [ ])

     k := GF (p);
     d := 2 * l + 2 * m + n;
     G := GL (d, k);
     
     // SL(2,p) blocks can be specified in the input if desired
     if #BLOCK eq 0 then
          BLOCK := [1] cat [ Random ([0,1]) : i in [2..l+m] ];
     else
          assert (#BLOCK eq (l + m) and exists { i : i in [1..l+m] | BLOCK[i] eq 1 });
     end if;
     
     // first build generators for SL(2,p)
     S := SL (2, p);
     gens := [ Identity (G) : i in [1..Ngens (S)] ];
     for t in [1..l+m] do
          // populate diagonal 2 x 2 blocks randomly with SL(2,p) generators
          if BLOCK[t] eq 1 then
               for i in [1..#gens] do
                    InsertBlock (~gens[i], S.i, 1+2*t, 1+2*t);
               end for;
          end if;
     end for;
     Omega := sub < G | gens >;
     
     // next create a class 2 group as the p-core of H
     M2 := MatrixAlgebra (k, 2);
     L := [ [i, j, Random ([0,1])] : i in [1..l], j in [1..m] ];
     X := Matrix (k, 2*l, 2*m, [0 : i in [1..4*l*m]]);  
     for trip in L do
          if trip[3] eq 1 then
               InsertBlock (~X, Random (M2), 1 + 2*(trip[1]-1), 1 + 2*(trip[2]-1));
          end if;
     end for;
     u1 := InsertBlock (Identity (G), X, 1, 1+2*l);    
     Append (~gens, u1);
     
     M2m := KMatrixSpace (k, 2, m);
     L := [ Random ([0,1]) : i in [1..m] ];
     Y := Matrix (k, 2*m, n, [0 : i in [1..2*m*n]]);
     for i in [1..m] do
          if i eq 1 then
               InsertBlock (~Y, Matrix (Random (M2m)), 1+2*(i-1), 1);
          end if;
     end for;
     u2 := InsertBlock (Identity (G), Y, 1+2*l, 1+2*(l+m));          
     Append (~gens, u2);
     
     U := sub < G | u1, u2 >;
     H := sub < G | gens >;
     R := NormalClosure (H, U);
       
return H, Omega, R;
end function;

// given H = R : Omega, as above, compute the representations on V = R/[R,R]
// and on W = [R,R].
__get_representation_info := function (Omega, R)

  W := DerivedSubgroup (R);
  assert IsElementaryAbelian (W);
  AW, fW := AbelianGroup (W);
  Wbas := [ AW.i @@ fW : i in [1..Ngens (AW)] ];
  GW := GL (#Wbas, BaseRing (R));
  OmegaW_gens := [ ];
  for j in [1..Ngens (Omega)] do
    omega := Omega.j;
    ims := [ Eltseq ((omega^-1 * Wbas[i] * omega) @ fW) : i in [1..#Wbas] ];
    omega_W := GW!Matrix (ims);
    Append (~OmegaW_gens, omega_W);
  end for;

  OmegaW := sub < GW | OmegaW_gens >;
  beta := hom < Omega -> OmegaW | OmegaW_gens >;

  V, pi := R / W;
  assert IsElementaryAbelian (V);
  "computing isomorphism of R/[R,R] with abelian group ...";
ttt := Cputime ();
  AV, fV := AbelianGroup (V);
  "... done in time", Cputime (ttt);
  Vbas := [ AV.i @@ fV : i in [1..Ngens (AV)] ];
  GV := GL (#Vbas, BaseRing (R));
  OmegaV_gens := [ ];
  for j in [1..Ngens (Omega)] do
    omega := Omega.j;
    ims := [ Eltseq (((omega^-1 * (Vbas[i] @@ pi) * omega) @ pi) @ fV) : i in [1..#Vbas] ];
    omega_V := GV!Matrix (ims);
    Append (~OmegaV_gens, omega_V);
  end for;

  OmegaV := sub < GV | OmegaV_gens >;
  tau := hom < Omega -> OmegaV | OmegaV_gens >;

/*
AN EXPERIMENT WORKING JUST WITH THE NONTRIVIAL ACTION OF OMEGA on R
....
  "R has order", Factorization (#R), "and", Ngens (R), "generators";
  R := CommutatorSubgroup (Omega, R);
  "[Omega, R] has order", Factorization (#R), "and", Ngens (R), "generators";
  W := DerivedSubgroup (R);
time  assert IsElementaryAbelian (W);
time  AW, fW := AbelianGroup (W);
  Wbas := [ AW.i @@ fW : i in [1..Ngens (AW)] ];
  GW := GL (#Wbas, BaseRing (R));
  OmegaW_gens := [ ];
  for j in [1..Ngens (Omega)] do
    omega := Omega.j;
    ims := [ Eltseq ((omega^-1 * Wbas[i] * omega) @ fW) : i in [1..#Wbas] ];
    omega_W := GW!Matrix (ims);
    Append (~OmegaW_gens, omega_W);
  end for;

  OmegaW := sub < GW | OmegaW_gens >;
  beta := hom < Omega -> OmegaW | OmegaW_gens >;

time  V, pi := R / W;
time  assert IsElementaryAbelian (V);
  "computing isomorphism of R/[R,R] with abelian group ...";
ttt := Cputime ();
  AV, fV := AbelianGroup (V);
  "... done in time", Cputime (ttt);
  Vbas := [ AV.i @@ fV : i in [1..Ngens (AV)] ];
  GV := GL (#Vbas, BaseRing (R));
  OmegaV_gens := [ ];
  for j in [1..Ngens (Omega)] do
    omega := Omega.j;
    ims := [ Eltseq (((omega^-1 * (Vbas[i] @@ pi) * omega) @ pi) @ fV) : i in [1..#Vbas] ];
    omega_V := GV!Matrix (ims);
    Append (~OmegaV_gens, omega_V);
  end for;

  OmegaV := sub < GV | OmegaV_gens >;
  tau := hom < Omega -> OmegaV | OmegaV_gens >;
*/

return tau, beta;
end function;



