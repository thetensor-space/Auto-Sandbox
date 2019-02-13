
// assumes you are running from within the same folder as this file.
// load "../examples/brahana/programs.m";
// load "../examples/dual.m";



/* 010117
programs to help study groups given via Brahana spaces for magma 2.8

functions:

Presentation
R - first quadratic irreducible - non-square x^2 - r
S - a cubic irreducible x^3 + r*x - 1
T - second cubic irreducible
U - second quadratic irreducible (x^2 + R(p) * r^2 - 1) 
W - quintic irreducible x^5 + r*x + 1
SubspaceToSubgroups 
Subgroups
SubgroupInvariants (G, k, f) -- partition the subgroups of 
   codimension k according to value of f which may be defined as follows:
   f := function (X, G)
      return some numerical invariant which takes values between [0..p^n];
   end function;
   
InvariantsHH (G, k)
InvariantsHG (G, k)
InvariantsCentraliser (G, k)

here k is the codimension 

*/

Z := Integers ();

Presentation := function (p, V)

   F := FreeGroup (5);
   P := pQuotient (F, p, 2: Print := 0, Exponent := p);                         
   rels := [];
   for v in V do 
      rel := 
      (P.1, P.2)^v[1] * (P.1, P.3)^v[2] * (P.1, P.4)^v[3] * (P.1, P.5)^v[4] * 
      (P.2, P.3)^v[5] * (P.2, P.4)^v[6] * (P.2, P.5)^v[7] * (P.3, P.4)^v[8] * 
      (P.3, P.5)^v[9] * (P.4, P.5)^v[10];
      Append (~rels, rel);
   end for;

   return quo < P | rels >; 

end function;

// for #21,#22,#24 and #39 (is this correct?)
R := function (p) //quadratic irreducible - non-square
 
   Z := Integers ();
   F := GF (p);
   P<x> := PolynomialRing (F);
   for r in F do 
     if IsIrreducible (x^2 - r) then
        return Z ! r;
     end if;
   end for;
end function;     

// for #36 and #43 
S := function (p) //first cubic irreducible
 
   Z := Integers ();
   F := GF (p);
   P<x> := PolynomialRing (F);
   for r in F do 
     if IsIrreducible (x^3 + r * x - 1) then
        return Z ! r;
     end if;
  end for; 
end function;     

// for #48 
T := function (p) //second cubic irreducible
   Z := Integers ();
   F := GF (p);
   P<x> := PolynomialRing (F);
   for r in F do 
      if IsIrreducible (x^3 + x^2 - r^2) then
        return Z ! r;
      end if;
  end for; 
end function;     

// for #52
U := function (p) //second quadratic irreducible
   Z := Integers ();
   F := GF (p);
   P<x> := PolynomialRing (F);
   for r in F do
      if IsIrreducible (x^2 + R(p) * r^2 - 1) then
        return Z ! r;
      end if;
  end for;
end function;              

// for #54
W := function (p) //quintic irreducible 
 
   Z := Integers ();
   F := GF (p);
   P<x> := PolynomialRing (F);
   for r in F do 
     if IsIrreducible (x^5 + r*x + 1) then
        return Z ! r;
     end if;
   end for;
end function;     

SubspaceToSubgroup := function (G, S, C)

 E := [];
 zero := [0:i in [1..NPCgens (C)]];
 for i in [1..Nrows (S)] do 
    v := Eltseq (S[i]) cat zero;
    v := [Z| x : x in v];
    Append (~E, G!v);
 end for;
 return sub < G | E, C >;

end function;

/* partition subgroups of codimension k in G 
   according to order of centraliser; return 
   lengths of parts in partition + parts */

PartitionSubgroups := function (G, k)

   p := FactoredOrder (G)[1][1];
   d := #Generators (G);
   H := sub < GL(d, p) | >;
   O := OrbitsOfSpaces (H, d - k);
   C := sub < G | [G.i: i in [6..NPCgens (G)]]>;
 
   parts := [];
   Values := [];
   A := [];
   for i in [1..#O] do
      M := SubspaceToSubgroup (G, O[i][2], C);
      v := #Centraliser (G, M);
      pos := Position (Values, v);
      if pos eq 0 then
         Append (~parts, {i});
         Append (~Values, v);
      else
         Include (~parts[pos], i);
      end if;
   end for;
 
   return {#part: part in parts}, parts; 
 
end function;                  

/* list subgroups of codimension k in G */

Subgroups := function (G, k: Abelian := false)

   p := FactoredOrder (G)[1][1];
   d := #Generators (G);
   H := sub < GL(d, p) | >;
   O := OrbitsOfSpaces (H, d - k);
   C := sub < G | [G.i: i in [6..NPCgens (G)]]>;
//   "Number of subgroups = ", #O;
   A := [];
   for i in [1..#O] do
     X := SubspaceToSubgroup (G, O[i][2], C);
//     if i mod 1000 eq 0 then "process i = ", i; end if;
     if Abelian eq true then 
        if not IsAbelian (X) then continue; end if; 
     end if;
     Append (~A, X);
   end for;
   return A;
end function;

/* f is a function specifying a particular computation for a subgroup 
   of codimension k; return those subgroups of order p^order */

SubgroupInvariants := function (G, k, f: order := -1)

   if Type (order) eq RngIntElt then order := [order]; end if;

   p := FactoredOrder (G)[1][1];
   d := #Generators (G);
   H := sub < GL(d, p) | >;
   O := OrbitsOfSpaces (H, d - k);
   C := sub < G | [G.i: i in [6..NPCgens (G)]]>;
   // "Number of subgroups = ", #O;
   n := NPCgens (G);
   Part := [];
   Seq := [ 0 : i in [1..n + 1]];
   for i in [1..#O] do
      // if i mod 1000 eq 0 then process i = ", i; end if;
      X := SubspaceToSubgroup (G, O[i][2], C);
      o := FactoredOrder (f (X, G));
      if #o eq 0 then 
         Seq[1] +:= 1; 
         if 0 in order then Append (~Part, X); end if; 
      else
        Seq[o[1][2]+1] := Seq[o[1][2]+1]+1;
        if o[1][2] in order then Append (~Part, X); end if; 
      end if;   
   end for;

   return Seq, Part;

end function;


/* typical filter
      if Order(DerivedSubgroup(X)) eq p^3 
           or Order(DerivedSubgroup(X)) eq p^4 then
        Append(~Grps, X);
      end if;

      if Order(DerivedSubgroup(X)) eq  1 then
        Append(~Grps, X);
      end if;
*/

InvariantsHG := function (G, k: order := -1)
   f := function (X, G)
      return CommutatorSubgroup (X, G);
   end function;
   return SubgroupInvariants (G, k, f: order := order);
end function;

InvariantsHH := function (G, k: order := -1)
   f := function (X, G)
      return DerivedSubgroup (X);
   end function;
   return SubgroupInvariants (G, k, f: order := order);
end function;

InvariantsCentraliser := function (G, k: order := -1) 
   f := function (X, G)
      return Centraliser (G, X);
   end function;
   return SubgroupInvariants (G, k, f: order := order);
end function;

EasyInvariants := function (G) 
   L := [];
   /* codimension 1 for maximals */
   for k in [1] do
     Seq := InvariantsHH (G,k);
     Append (~L, Seq);
   end for;
 
   /* codimension k = 4 for minimals */
   k := 4;
   a, b := InvariantsCentraliser (G, k);
   Append (~L, a);
   return L;

end function;

Investigate := function (p, V)

   G := Presentation (p, V);
   G,_, defs := pQuotient (G, p, 2);
   G`definitions := defs;
   H := pQuotient(FreeGroup (5), p, 1);
   P,defs := pCoveringGroup (H:Exponent := p);
   P`definitions := defs;
   A, phi, S := AllowableSubgroup (P, G);
   T := Subgroups (S, 1);
   Q := [quo < P | T[i]> : i in [1..#T]];
   I := [EasyInvariants (X): X in Q];

   return I, Q;

end function;


BrahanaList := function (p)

Labels := ["#0","#1","#2","#3","#4","#5","#6","#7","#8","#9","#9'",
"#10","#11","#12","#13","#14","#15","#16","#17","#18","#19", 
"#20","#20'","#20\"","#21","#21'",
"#22","#23","#24","#25","#26","#27","#28","#29",
"#30","#31","#32","#33","#34","#35","#36","#37","#38","#39", 
"#40","#41","#42","#43","#44","#45","#46","#47","#48","#49", 
"#50","#51","#52","#53","#54", "#55"];

V := [
// #0 Brahana p.660
[
[1,0,0,0,0,0,0,0,0,0],
[0,1,0,0,0,0,0,0,0,0],
[0,0,1,0,0,0,0,0,0,0],
[0,0,0,1,0,0,0,0,0,0]
],
// #1 p.661
[
[1,0,0,0,0,0,0,0,0,0],
[0,0,0,0,0,0,0,1,0,0],
[0,0,1,0,0,0,0,0,0,0],
[0,0,0,0,1,0,0,0,0,0]
],
// #2
[
[1,0,0,0,0,0,0,1,0,0],
[0,1,0,0,0,R(p),0,0,0,0],
[0,0,1,0,0,0,0,0,0,0],
[0,0,0,0,1,0,0,0,0,0]
],
// #3
[
[1,0,0,0,0,0,0,0,0,0],
[0,1,0,0,0,1,0,0,0,0],
[0,0,0,0,0,0,0,1,0,0],
[0,0,1,0,0,0,0,0,0,0]
],
// #4
[
[0,0,0,0,1,0,0,0,0,0],
[0,0,0,0,0,0,0,0,0,1],
[0,0,0,0,0,1,0,0,1,0],
[1,1,0,0,0,0,0,0,0,0]
],
// #5
[
[1,0,0,0,0,0,0,1,0,0],
[0,1,0,0,0,0,1,0,0,0],
[0,0,1,0,0,0,0,0,0,0],
[0,1,0,0,1,1,0,1,0,0]
],
// #6
[
[0,0,0,0,1,0,0,0,0,0],
[0,0,0,0,0,0,0,0,0,1],
[0,0,0,0,0,1,0,0,1,0],
[1,0,0,0,0,0,0,1,0,0]
],
// #7 p.665
[
[1,0,0,0,0,0,0,0,0,0],
[0,1,0,0,0,0,0,0,0,0],
[0,0,1,0,0,0,0,0,0,0],
[0,0,0,0,1,0,0,0,0,0]
],
// #8
[
[1,0,0,0,0,0,0,0,0,0],
[0,1,0,0,0,0,0,0,0,0],
[0,0,1,0,0,0,0,0,0,0],
[0,0,0,0,0,0,1,0,0,0]
],
// #9
[
[1,0,0,0,0,0,0,0,0,0],
[0,1,0,0,0,0,0,0,0,0],
[0,0,1,0,0,0,0,0,0,0],
[0,0,0,0,1,0,0,0,0,1]
],
// #9'
[
[1,0,0,0,0,0,0,0,0,0],
[0,1,0,0,0,0,0,0,0,0],
[0,0,1,0,0,0,0,0,0,0],
[0,0,0,1,1,0,0,0,0,0]
],
// #10
[
[1,0,0,0,0,0,0,0,0,0],
[0,1,0,0,0,0,0,0,0,0],
[0,0,0,0,1,0,0,0,0,0],
[0,0,0,0,0,0,0,0,0,1]
],
// #11
[
[1,0,0,0,0,0,0,0,0,0],
[0,1,0,0,0,0,0,0,0,0],
[0,0,0,0,1,0,0,0,0,0],
[0,0,0,0,0,1,0,0,1,0]
],
// #12 p. 667
[
[1,0,0,0,0,0,0,0,0,0],
[0,1,0,0,0,0,0,0,0,0],
[0,0,0,0,0,1,0,0,0,0],
[0,0,0,0,0,0,0,0,0,1]
],
// #13
[
[1,0,0,0,0,0,0,0,0,0],
[0,1,0,0,0,0,0,0,0,0],
[0,0,0,0,0,1,0,0,0,0],
[0,0,0,1,0,0,1,0,0,0]
],
// #14
[
[1,0,0,0,0,0,0,0,0,0],
[0,1,0,0,0,0,0,0,0,0],
[0,0,0,0,0,1,0,0,0,0],
[0,0,0,0,0,0,0,0,1,1]
],
// #15
[
[1,0,0,0,0,0,0,0,0,0],
[0,1,0,0,0,0,0,0,0,0],
[0,0,0,0,0,1,0,0,0,0],
[0,0,0,1,0,0,0,1,0,0]
],
// #16
[
[1,0,0,0,0,0,0,0,0,0],
[0,1,0,0,0,0,0,0,0,0],
[0,0,0,0,0,1,0,0,0,0],
[0,0,0,1,0,0,1,1,0,0]
],
// #17
[
[1,0,0,0,0,0,0,0,0,0],
[0,1,0,0,0,0,0,0,0,0],
[0,0,0,0,0,1,0,0,0,0],
[0,0,0,0,1,0,0,0,0,1]
],
// #18
[
[1,0,0,0,0,0,0,0,0,0],
[0,1,0,0,0,0,0,0,0,0],
[0,0,0,0,0,1,0,0,0,0],
[0,0,0,1,1,0,0,0,0,0]
],
// #19 p. 670 - slightly different order for vectors for this batch
[
[1,0,0,0,0,0,0,0,0,0],
[0,0,0,1,0,0,0,0,1,0],
[0,0,0,0,0,0,1,0,0,1],
[0,0,0,0,0,0,0,1,0,0]
],
// #20
[
[1,0,0,0,0,0,0,0,0,0],
[0,1,0,0,0,0,0,0,0,0],
[0,0,0,0,0,1,0,0,1,0],
[0,0,0,0,0,0,0,0,0,1]
],
// #20'
[
[1,0,0,0,0,0,0,0,0,0],
[0,1,0,0,0,0,0,0,0,0],
[0,0,0,1,1,0,0,0,0,0],
[0,0,0,0,0,0,0,0,0,1]
],
// #20" 
[
[1,0,0,0,0,0,0,0,0,0],
[0,1,0,0,0,0,0,0,0,0],
[0,0,0,1,1,1,0,0,0,0],
[0,0,0,0,0,0,0,0,0,1]
],
// #21
[
[1,0,0,0,0,0,0,0,0,0],
[0,1,0,0,0,0,0,0,0,0],
[0,0,1,0,0,0,1,0,0,0],
[0,0,0,1,0,R(p),0,0,0,0]
],
// #21'
[
[1,0,0,0,0,0,0,0,0,0],
[0,1,0,0,0,0,0,0,0,0],
[0,0,1,0,1,0,0,0,0,0],
[0,0,0,1,0,1,0,0,0,0]
],
// #22
[
[1,0,0,0,0,0,0,0,0,0],
[0,1,0,0,0,0,0,0,0,0],
[0,0,0,0,0,1,0,0,R(p),0],
[0,0,0,0,0,0,1,1,0,0]
],
// #23
[
[1,0,0,0,0,0,0,0,0,0],
[0,1,0,0,0,0,0,0,0,0],
[0,0,1,0,1,0,0,0,0,0],
[0,0,0,0,0,0,1,1,0,0]
],
// #24
[
[1,0,0,0,0,0,0,0,0,0],
[0,1,0,0,0,0,0,0,0,0],
[0,0,0,0,1,0,0,0,0,-R(p)],
[0,0,0,0,0,0,1,1,0,0]
],
// #25
[
[1,0,0,0,0,0,0,0,0,0],
[0,1,0,0,0,0,0,0,0,0],
[0,0,1,0,0,0,0,0,1,0],
[0,0,0,0,1,0,0,0,0,1]
],
// #26
[
[1,0,0,0,0,0,0,0,0,0],
[0,1,0,0,0,0,0,0,0,0],
[0,0,1,0,0,0,0,0,1,0],
[0,0,0,0,0,0,1,1,0,0]
],
// #27
[
[1,0,0,0,0,0,0,0,0,0],
[0,1,0,0,0,0,0,0,0,0],
[0,0,1,0,0,0,1,0,0,0],
[0,0,0,1,0,0,0,1,0,0]
] ,
// #28 p. 680
[
[1,1,0,0,0,0,0,0,0,0],
[0,0,0,0,0,0,1,0,0,0],
[0,0,0,0,0,0,0,1,0,0],
[1,0,0,0,0,1,0,0,1,0]
],
// #29
[
[1,1,0,0,0,0,0,0,0,0],
[0,0,0,0,0,0,1,0,0,0],
[0,0,0,0,0,0,0,1,0,0],
[0,0,1,-1,-1,0,0,0,0,1]
],
// #30
[
[1,1,0,0,0,0,0,0,0,0],
[0,0,0,0,0,0,1,0,0,0],
[0,0,0,0,0,0,0,1,0,0],
[0,0,1,-1,0,0,0,0,0,1]
],
// #31
[
[1,1,0,0,0,0,0,0,0,0],
[0,0,0,0,0,0,1,0,0,0],
[0,0,0,0,0,0,0,1,0,0],
[0,0,1,1,0,0,0,1,1,1]
],
// #32
[
[1,1,0,0,0,0,0,0,0,0],
[0,0,0,0,0,0,1,0,0,0],
[0,0,0,0,0,0,0,1,0,0],
[0,0,1,-1,-R(p),0,0,0,0,1]
],
// #33
[
[1,1,0,0,0,0,0,0,0,0],
[0,0,0,0,0,0,1,0,0,0],
[0,0,0,0,0,0,0,1,0,0],
[0,0,0,1,1,0,0,0,0,1]
],
// #34
[
[1,1,0,0,0,0,0,0,0,0],
[0,0,0,0,0,0,1,0,0,0],
[0,0,0,0,0,0,0,1,0,0],
[0,0,0,1,0,1,0,0,0,0]
],
// #35
[
[1,1,0,0,0,0,0,0,0,0],
[0,0,0,0,0,0,1,0,0,0],
[0,0,0,0,0,0,0,1,0,0],
[0,0,1,1,1,1,0,0,0,1]
],
// #36  p. 684
[
[1,0,0,0,0,0,0,1,0,0],
[0,1,0,0,0,0,1,0,0,0],
[0,0,0,0,0,1,0,S(p),1,0],
[1,0,1,0,0,0,0,0,0,0]
],
// #37
[
[1,0,0,0,0,0,0,0,0,0],
[0,1,0,0,0,0,1,0,0,0],
[0,0,0,0,0,0,0,1,0,0],
[0,0,0,R(p),1,0,0,0,0,1]
],
// #38
[
[1,0,0,0,0,0,0,0,0,0],
[0,1,0,0,0,0,1,0,0,0],
[0,0,0,0,0,0,0,1,0,0],
[0,0,0,0,1,0,0,0,0,1]
],
// #39 
[
[1,0,0,0,0,0,0,0,0,0],
[0,1,0,0,0,0,1,0,0,0],
[0,0,0,0,0,0,0,1,0,0],
[0,0,0,1,R(p),0,0,0,0,0] 
],
// #40
[
[1,0,0,0,0,0,0,0,0,0],
[0,1,0,0,0,0,1,0,0,0],
[0,0,0,0,0,0,0,1,0,0],
[0,0,0,1,0,1,0,0,1,0]
],
// #41
[
[1,0,0,0,0,0,0,0,0,0],
[0,1,0,0,0,0,1,0,0,0],
[0,0,0,0,0,0,0,1,0,0],
[0,0,1,1,-1,0,0,0,0,0]
],
// #42
[
[1,0,0,0,0,0,0,0,0,0],
[0,1,0,0,0,0,1,0,0,0],
[0,0,0,0,0,0,0,1,0,0],
[0,0,1,1,-R(p),0,0,0,0,0]
],
[ 
// #43 p. 690
  [1,0,0,0,0,0,0,1,0,0],
  [0,1,0,0,0,0,1,0,0,0],
  [0,0,0,0,0,1,0,S(p),1,0],
  [0,0,0,0,1,0,0,0,0,0]
],

[ 
// #44
  [1,0,0,0,0,0,0,1,0,0],
  [0,1,0,0,0,0,1,0,0,0],
  [0,0,0,0,1,0,0,0,0,0],
  [0,0,0,1,0,1,0,0,0,0]
],

[ 
// #45
  [1,0,0,0,0,0,0,1,0,0],
  [0,1,0,0,0,0,1,0,0,0],
  [0,0,0,0,0,1,0,0,0,0],
  [0,0,1,0,-R(p),0,0,0,0,0]
],

[ 
// #46
  [1,0,0,0,0,0,0,1,0,0],
  [0,1,0,0,0,0,1,0,0,0],
  [0,0,0,0,0,1,0,0,0,0],
  [0,0,0,R(p),1,0,0,0,0,0]
],

[ 
// #47
  [1,0,0,0,0,0,0,1,0,0],
  [0,1,0,0,0,0,1,0,0,0],
  [0,0,0,0,0,1,0,0,0,0],
  [0,0,1,0,0,0,0,0,1,0]
],

[ 
// #48 
  [1,0,0,0,0,0,0,1,0,0],
  [0,1,0,0,0,0,1,0,0,0],
  [0,0,1,0,0,0,0,0,0,0],
  [1,0,0,0,0,T(p),0,0,1,0]
],

[ 
// #49
  [1,0,0,0,0,0,0,1,0,0],
  [0,1,0,0,0,0,1,0,0,0],
  [0,0,0,0,0,1,-R(p),0,0,0],
  [0,0,1,0,0,0,0,0,1,0]
],

[ 
// #50
  [1,0,0,0,0,0,0,1,0,0],
  [0,1,0,0,0,0,1,0,0,0],
  [0,0,0,0,0,1,-R(p),0,0,0],
  [0,0,0,R(p),1,0,0,0,0,0]
],

[ 
// #51
  [1,0,0,0,0,0,0,1,0,0],
  [0,1,0,0,0,0,1,0,0,0],
  [0,0,0,0,0,0,0,0,0,1],
  [0,0,1,-R(p),1,0,0,0,0,0]
],

[ 
// #52 
  [1,0,0,0,0,0,0,1,0,0],
  [0,1,0,0,0,0,1,0,0,0],
  [0,0,0,0,0,0,0,0,0,1],
  [0,0,1,R(p),1,U(p),0,0,0,0]
],

[ 
// #53 p. 697
  [1,0,0,0,0,0,0,1,0,0],
  [0,1,0,0,0,0,1,0,0,0],
  [0,0,1,0,-R(p),0,0,0,0,0],
  [0,0,0,0,0,1,0,S(p),1,0]
],

[ 
// #54 
  [1,0,0,0,0,0,0,1,0,0],
  [0,1,0,0,0,0,1,0,0,0],
  [0,0,0,0,1,0,0,0,0,1],
  [0,0,0,1,-W(p),1,0,0,0,0]
],
// #55 new rep 
[
[1,0,0,0,0,0,0,1,0,0],
[0,0,0,0,0,0,1,0,0,0],
[0,0,0,0,0,0,0,0,1,0],
[0,1,0,1,0,R(p),0,0,0,0]
]      
];

P := [Presentation(p, V[i]): i in [1..#V]];
return P, V;

end function;

/* return dual space of U */
DualSpace := function (U)
   F := BaseRing (U);
   d := Degree (U);
   B := Basis (U);
   n := #B;
   K := KMatrixSpace (F, n, d);
   S := K!&cat[Eltseq (B[i]): i in [1..n]];
   return NullSpace (Transpose (S));
end function;

DualGroup := function (G)

d := FrattiniQuotientRank (G);
p := FactoredOrder (G)[1][1];
F := FreeGroup (d);
H:=pQuotient (F, p, 1);
H:=pCoveringGroup (H: Exponent := p);
M :=sub< H | [H.i: i in [d + 1..NPCgens (H)]]>;

Z := Integers ();

U := AllowableSubgroup (H, G);
U := DualSpace (U);
gens := [];
for i in [1..Dimension (U)] do
v := Eltseq (U.i);
v:=[Z!x: x in v];
g := &*[M.i^v[i]: i in [1..NPCgens (M)]];
Append (~gens, g);
end for;
s := sub< M | gens>;
D := quo < H | s>;
return D;
end function;

BrahanaTest := function(p)
	B := BrahanaList(p);
	orders := [0 : i in [1..#B]];
	times := [* *];
	failed := 0;
	for i in [1..#B] do
		print "";
		print "i=", i, "====================================================================";
		print "";
		D := DualGroup(B[i]);
		t := Cputime();
	try
		U,L := AutomorphismGroupByInvariants(D);
		s := Cputime(t);
		Append(~times, s  );
		if ISA(Type(L),GrpMat) and not( LMGOrder(U) eq LMGOrder(L) ) then
			print "Gap in order", LMGOrder(U), ":", LMGOrder(L);
	 	end if;
		orders[i] := LMGOrder(U);
		print i, " took time ", times[i], " and gave order ", orders[i];
		print "";
	catch e
		print i, " FAILED ", e;		
		Append(~times, -1);
		orders[i] := -1;
		failed +:= 1;
	end try;
	end for;
	print "Total failures: ", failed;
	return orders, times;
end function;

