MypRanks := function (P)
   ranks := pRanks (P);
   return [ranks[1]] cat [ranks[i + 1] - ranks[i]: i in [1..#ranks - 1]];
end function;

/* vector to integer sequence */

VectorToInt := function (v)
   r := Eltseq (v);
   ChangeUniverse (~r, Integers ());
   return r;
end function;

/* convert matrix A in GL(d, p) describing action on Frattini quotient
   of d-generator p-group G into automorphism of G */

MatrixToAutomorphism := function (P, A)
   p := FactoredOrder (P)[1][1];
   d := FrattiniQuotientRank (P);
   m := Nrows (A);
   error if m lt d, "Must define action on at least Frattini quotient";
   zeros := [0: i in [1..NPCgens (P) - m]];
   Images := [<P.i, P!(VectorToInt (A[i]) cat zeros)> : i in [1..m]];
   return hom <P -> P | Images : Check := false >;
end function;

// convert automorphism alpha to matrix acting on char section 
// spanned by  pc-generators start .. last 
AutomorphismToMatrix := function (P, alpha: start := 1, last := NPCgens (P))
   p := FactoredOrder (P)[1][1];
   if start eq 1 and last eq NPCgens (P) then 
      return GL(last, p) ! &cat[Eltseq (alpha (P.i)): i in [1..last]];
   else
      L := [];
      for i in [start..last] do
         e := Eltseq (alpha (P.i));
         e := [e[j]: j in [start..last]];
         Append (~L, e);
      end for;
      return GL(last - start + 1, p) ! &cat (L);
   end if;
   return L;
end function;

// p-multiplicator of p-group P 
Multiplicator := function (P)
   c := pClass (P);
   return sub < P | [P.i : i in [1..NPCgens (P)] | WeightClass (P.i) eq c]>;
end function;

// P is p-covering group of G; return nucleus of G
Nucleus := function (P, G)
   defns := pQuotientDefinitions (P);
   N := sub < P | >;
   q := NPCgens (P);
   n := NPCgens (G);
   class := pClass (G);
   for i in [n + 1..q] do
       defn := defns[i];
       u := defn[1]; v := defn[2]; wt := 0;
       if u gt 0 and v gt 0 then
          wt := PCClass (G.u) + PCClass (G.v);
       elif u gt 0 and v eq 0 then
           wt := PCClass (G.u) + 1;
       end if;
       if wt gt class then N := sub <P | N, P.i>; end if;
   end for;
   return N;
end function;

// S/N is characteristic section of P 
// return action of automorphisms Auts on S/N as elements of corresponding GL
ActionOnFactor := function (P, S, N, Auts)
   if #Auts eq 0 then return []; end if;

   Q, phi := quo <S | N >;
   T := [Q.i @@ phi : i in [1..NPCGenerators (Q)]];

   p := FactoredOrder (P)[1][1]; 
   q := NPCgens (Q);
   gl := GL (q, p);

   result := [];
   for alpha in Auts do
      temp := [];
      for i in [1..q] do
         temp cat:= Eltseq (phi (alpha (T[i])));
      end for;
      Append (~result, gl!temp);
   end for;

   return result, phi;
end function;

// S is char subgroup of P 
// return action of Auts on S as elements of corresponding GL 

ActionOnSubgroup := function (P, S, Auts)
   if #Auts eq 0 then return []; end if;

   p := FactoredOrder (P)[1][1]; 
   q := NPCgens (S);
   start := Minimum ([Depth (P!S.i): i in [1..NPCgens (S)]]);

   gl := GL (q, p);

   result := [];
   for alpha in Auts do
      temp := [];
      for i in [1..q] do
         e := alpha (S.i);
         e := Eltseq (e);
         e := [e[j] : j in [start .. start - 1 + q]];
         temp cat:= e;
      end for;
      Append (~result, gl!temp);
   end for;

   return result;
end function;
