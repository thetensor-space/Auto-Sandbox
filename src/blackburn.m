// code to computeBlackburn invariants for  
// p-groups with derived group of order p 
// J. Algebra 1999

/* map from P/Z to Z/Z^p */
PowerMap := function (P, Z, Zp)
   n := NPCgens (P);
   c := NPCgens (Z);
   zp := NPCgens (Zp);
   if [Z.i : i in [c - zp + 1..c]] ne [Zp.i: i in [1..zp]] then
      error "Assumption on ordering of generators for Z and Z^p incorrect";
   end if;
   
   p := FactoredOrder (P)[1][1];
   A := [];
   Q, phi := quo<P | Z>;
   gens := [Q.i @@ phi : i in [1..NPCgens (Q)]];
   for g in gens do 
      assert not (g in Z);
      w := Z!(g^p);
      w := Eltseq (w);
      w := [w[l]: l in [1..c - zp]];
      Append (~A, w);
   end for;

   n := #A; m := c - zp;
   MA := KMatrixSpace (GF (p), n, m);
   return true, MA! &cat (A);
end function;

/* S is a subspace of W; compute preimage of S under linear map t */
LinearPreimage := function (W, S, t)
   Q, phi := quo <W | S>;
   K := KMatrixSpace (BaseRing (W), Degree (W), Degree (Q));
   W := Basis (W);
   M := K ! &cat ([Eltseq (phi (W[i])): i in [1..#W]]);
   return NullSpace (t * M);
end function;

// Z centre, Zp = Agemo (Z, 1)  
// D derived group
UpperOmega := function (Z, Zp, D, e)
    c := NPCgens (Z);
    p := FactoredOrder (Z)[1][1];
    L := [Omega (Z, i): i in [0..e - 1]];

    // A := {z: z in Z | z^(p^(e - 1)) in D};
    Q, phi := quo <Z | D>;
    B := Omega (Q, e - 1);
    A := B @@ phi;
    Append (~L, A); 

    L cat:= [Omega (Z, i - 1): i in [e + 1 .. c + 1]];
    Q, phi := quo <Z | Zp>;
    Y := [phi (l): l in L];
    return Y, L;
end function;

SetupSpaces := function (Y)
   G := Y[#Y];
   d := NPCgens (G); p := FactoredOrder (G)[1][1];
   V := VectorSpace (GF (p), d);
   S := [* sub< V | > *];
   for i in [2..#Y] do
      H := Y[i]; 
      U := sub< V | [Eltseq (G!H.i): i in [1..NPCgens (H)]]>;
      Append (~S, U);
   end for;
   return S;
end function;

ParametersForGroup := function (P) 
   p := FactoredOrder (P)[1][1];
   n := NPCgens (P);
   
   Z := Centre (P);
   IA := AbelianInvariants (Z);
   IA := [Ilog (p, a): a in IA];
   
   c := NPCgens (Z);
   assert c eq &+IA;
   assert c lt n; assert IsEven (n - c);
   
   Zp := Agemo (Z, 1); cp := NPCgens (Zp);
   
   // ranks := [0, NPCgens (P) - c, NPCgens (P) - cp];
   // power := PowerMap (P, ranks, 1);

   flag, power := PowerMap (P, Z, Zp);
   if not flag then return false, _, _, _, _; end if;
   
   D := DerivedGroup (P);
   e_vals := [i : i in Set (IA) | D subset Agemo (Z, i - 1)];
   e := Maximum (e_vals);
   assert e in IA;
   
   Y, L := UpperOmega (Z, Zp, D, e);
   S := SetupSpaces (Y);
   W := S[#S];
   V := [LinearPreimage (W, S[i], power): i in [1..#S]];
   W := V[#V]; 
   assert Dimension (W) eq n - c;
   V := [sub<W | >] cat V;
   return true, [IA, [e], [Dimension (U): U in V] ], V, Y, L;
end function;

SetupForm := function (P)
   p := FactoredOrder (P)[1][1];
   D := DerivedGroup (P);
   Z := Centre (P);
   n := NPCgens (P);
   c := NPCgens (Z);
   d := n - c;
   MA := MatrixAlgebra (GF (p), d);
   form := Zero (MA);
   Q, phi := quo<P | Z>;
   gens := [Q.i @@ phi : i in [1..NPCgens (Q)]];
   assert #gens eq d;
   for i in [1..d] do
      for j in [i + 1..d] do
         x := (gens[i], gens[j]);
         k := Eltseq (D!x);
         form[i][j] := k;
       end for;
   end for;
   return form - Transpose (form);
end function;

/* <form> is a bilinear form, <bas> is the basis of a subspace;
  return restriction of <form> to subspace relative to basis */
RestrictForm := function (form, bas)
   d := #bas;
   F := BaseRing (form);
   k := Degree (F);
   p := Characteristic (F);
   res := MatrixAlgebra (F, d)!0;
   for i in [1..d] do
      for j in [1..d] do
         res[i][j] := InnerProduct (bas[i] * form, bas[j]);
      end for;
   end for;
   return res;
end function;

RadicalOfInducedForm := function (form, space)
   sM := RestrictForm (form, Basis (space));
   srad := Nullspace (sM);
   bas := [&+[ Basis (srad)[i][j] * Basis (space)[j] :
           j in [1..Dimension (space)]] : i in [1..Dimension (srad)]];
   return sub <space | bas>, sM;
end function;

SetupAlpha := function (V, R, n, c)
   T := [<i, j>: j in [i + 1..c + 2], i in [1..c + 2]] cat 
        [<i, i>: i in [1..c + 2]]; 

   MA := MatrixAlgebra (Rationals (), c + 2);
   // MA := MatrixAlgebra (Integers (), c + 2);
   Alpha := Zero (MA);
   Alpha := MA![-1: i in [1..(c + 2)^2]];
   A := {};
   total := 0;
   for t in T do
      i := t[1]; j := t[2];
      if i lt j then
         Alpha[i, j] := Dimension ((R[i + 1] meet R[j]) + V[i]) - 
                        Dimension ((R[i + 1] meet R[j + 1]) + V[i]);
      else 
         s1 := i gt 1 select &+[Alpha[k,i]: k in [1..i - 1]] else 0;
         s2 := c + 2 ge i + 1 select &+[Alpha[i,k]: k in [i + 1..c + 2]] else 0;
         Alpha[i, j] := (Dimension (V[i+1]) - Dimension (V[i]) - s1 - s2) / 2;
      end if;
      total +:= Alpha[i, j];
      Include (~A, Alpha[i, j]);
   end for;
   assert total eq (n - c) div 2;
   return A, Alpha;
end function;

CheckAlpha := function (Alpha, e, c, m)
   for k in [2..c + 2] do 
      if k le e then a := m[k - 1];
      elif k eq e + 1 then a := 1;
      elif k eq e + 2 then a := m[e] - 1;
      elif k gt e + 2 then a := m[k - 2];
      end if;
      s1 := &+[Alpha[i, k]: i in [1..k]];
      s2 := &+[Alpha[k, j]: j in [k..c + 2]];
      assert s1 + s2 le a;
   end for;
   return true;
end function;

Invariants := function (P)
   n := NPCgens (P);
   Z := Centre (P);
   c := NPCgens (Z);
   flag, L, V, Y, X:=ParametersForGroup (P);
   assert flag;
   form := SetupForm (P);
   R := [RadicalOfInducedForm (form, V[i]): i in [1..#V]];
   A, Alpha := SetupAlpha (V, R, n, c);
   e := L[2][1];
   I := [L[1], L[2], Eltseq (Alpha)];
   M := Multiset (L[1]);
   m := [Multiplicity (M, s): s in [1..c + 2]];
   f := CheckAlpha (Alpha, e, c, m);
   assert f;
   return I;
end function;

// main function: investigate non-abelian quotients of G by maximal subgroups 
// of Frattini subgroup; record Blacburn invariants of each 
BlackburnInvariants := function (G)
   P := FrattiniSubgroup (G);
   M:=MaximalSubgroups (P);
   M := [M[i]`subgroup: i in [1..#M]];
   Q := [quo< G | M[i]>: i in [1..#M]];
   I := [Invariants (Q[i]): i in [1..#Q] | IsAbelian (Q[i]) eq false];
   results := [[i : i in [1..#I] | s eq I[i]] : s in Set (I)];
   if #results gt 1 then 
      S := [&meet[M[i]: i in results[j]]: j in [1..#results]];
      S := [x : x in S | #x gt 1];
   else
      S := [sub<P |>];
   end if;
   results := [#r: r in results];
   // if #I gt 0 then assert &+results eq #I; end if;
   return S, results, I, Q, M;
end function;

/* 
R := [];
d := 5; p := 5; k := 5;
G:= RandomGroup (d, p, k);
r, I, Q := ExamineGroup (G);
"partition is ", r;
Append (~R, r);
#I eq #Q;
id := [IdentifyGroup (x): x in Q];
nmr := [#[x : x in id| x eq i]: i in Set (id)];
Sort (r) eq Sort (nmr);

*/


/* 
p := 5; m := 7; R := [];
nmr := 0;
X := SmallGroups (p^m);
for i in [1..#X] do
G:=X[i];
R[i]:=ExamineGroup (G);
i, #R[i];
if #R[i] gt 1 then nmr +:= 1; end if;
end for;

for d in [2,3,4,5,6] do 
I:=[i : i in [1..#X] | FrattiniQuotientRank (X[i]) eq d];
d, #I, #[ i : i in I | #R[i] gt 1], #{R[i]: i in I | #R[i] gt 1};
end for;
*/

/* 
for p in [3,5,7] do 
   for k in [3..6] do 
      X := SmallGroups (p^k);
      "\n\n *** p = ", p, "n  = ", k;
      GP := [x: x in X | #DerivedGroup (x) eq p];
      AA := [* *];
      Invars := [];
      for i in [1..#GP] do 
         P := GP[i];
         I := Invariants (P);
         Append (~Invars, I);
      end for;
      assert #Invars eq #Set (Invars);
      assert #Invars eq #Set (Invars);
      assert #Invars eq #GP;
   end for;
end for;
*/
