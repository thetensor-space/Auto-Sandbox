 /*
  See if you can distinguish these pairs. I can parition these groups as follows
  { G1, H1 }, { G2, H2, G4, H4 }, { G3, H3 }
  using info from filters. Therefore, I know G1 is not isomorphic to G2 for example.
  Can you distinguish { G2, H2 } from { G4, H4 }? A more important question, can you
  distinguish Gi from Hi? I hope that Gi is isomorphic to Hi, but I wouldn't be 
  surprised if that was not the case. Thanks!
*/

G1 := PCGroup(\[ 9, -3, 3, 3, 3, 3, 3, -3, 3, 3, 13177, 19775, 237171, 219036, 75945, 
758164, 187123, 44167, 20821, 997277, 266828, 23351, 20930, 8951 ]);

B := pCentralBimap (G1, 1, 1);
S := SystemOfForms (B);



H1 := PCGroup(\[ 9, -3, 3, 3, 3, 3, 3, -3, 3, 3, 13177, 59294, 59141, 525855, 44076, 
73029, 102064, 62392, 12316, 1036643, 227462, 84587, 6350, 5063 ]);

G2 := PCGroup(\[ 9, -3, 3, 3, 3, 3, 3, -3, 3, 3, 13177, 59294, 59141, 315903, 35328, 
35121, 528529, 44167, 25681, 406787, 148730, 58343, 32594, 1175 ]);

H2 := PCGroup(\[ 9, -3, 3, 3, 3, 3, 3, -3, 3, 3, 13177, 59294, 52580, 79707, 79068, 
38037, 298894, 274603, 62392, 12316, 761081, 56876, 27725, 36968, 8465 ]);

G3 := PCGroup(\[ 9, -3, 3, 3, 3, 3, 3, -3, 3, 3, 19928, 19775, 105951, 79068, 52617, 
331699, 208993, 91552, 14746, 131225, 109364, 110831, 36968, 12839 ]);

H3 := PCGroup(\[ 9, -3, 3, 3, 3, 3, 3, -3, 3, 3, 13177, 59294, 59141, 420879, 96564, 
5961, 36454, 44968, 22297, 14746, 879179, 201218, 31136, 689 ]);

G4 := PCGroup(\[ 9, -3, 3, 3, 3, 3, 3, -3, 3, 3, 13177, 59294, 59141, 552099, 87816, 
3045, 134869, 274603, 40522, 28111, 288689, 319316, 88961, 16556, 689 ]);

H4 := PCGroup(\[ 9, -3, 3, 3, 3, 3, 3, -3, 3, 3, 13177, 59294, 59141, 683319, 44076, 
32205, 626944, 252733, 62392, 28111, 288689, 319316, 23351, 38426, 6035 ]);


//grps := [* G1, H1, G2, H2, G3, H3, G4, H4 *];
//flts := [* pCentralFilter(X) : X in grps *];
//refs := [* *];
//locs := [* *];
//for F in flts do
//  FF,L := Refine(F);
//  Append(~refs,FF);
//  Append(~locs,L);
//end for;
//lens := [* #F : F in refs *];
//coms := [* CommutatorSubgroup( Image(F)[1], Image(F)[2] ) : F in refs *];


B1 := pCentralBimap (G1, 1, 1);
e := Dimension (Codomain (B1));
p := Characteristic (BaseRing (B1));
n := &+ [ p^i : i in [0..e-1] ];
subsG1 := CharSubgroupsSpecial (G1 : FullGraph := true, LineSigFn := Genus2Sig);
subsH1 := CharSubgroupsSpecial (H1 : FullGraph := true);
subsG2 := CharSubgroupsSpecial (G2 : FullGraph := true);
subsH2 := CharSubgroupsSpecial (H2 : FullGraph := true);
subsG3 := CharSubgroupsSpecial (G3 : FullGraph := true);
subsH3 := CharSubgroupsSpecial (H3 : FullGraph := true);
subsG4 := CharSubgroupsSpecial (G4 : FullGraph := true);
subsH4 := CharSubgroupsSpecial (H4 : FullGraph := true);


/* 
X1, incl1, proj1 := DirectProduct (G1, H1);
X2, incl2, proj2 := DirectProduct (G2, H2);
X3, incl3, proj3 := DirectProduct (G3, H3);
X4, incl4, proj4 := DirectProduct (G4, H4);
subsX1 := CharSubgroupsSpecial (X1 : FullGraph := true);
subsX2 := CharSubgroupsSpecial (X2 : FullGraph := true);
subsX3 := CharSubgroupsSpecial (X3 : FullGraph := true);
subsX4 := CharSubgroupsSpecial (X4 : FullGraph := true);
ordsX1 := [ #L : L in subsX1 ];
ordsX2 := [ #L : L in subsX2 ];
ordsX3 := [ #L : L in subsX3 ];
ordsX4 := [ #L : L in subsX4 ];
projX1 := [ [ #(L @ proj1[1]) , #(L @ proj1[2]) ] : L in subsX1 ];
projX2 := [ [ #(L @ proj2[1]) , #(L @ proj2[2]) ] : L in subsX2 ];
projX3 := [ [ #(L @ proj3[1]) , #(L @ proj3[2]) ] : L in subsX3 ];
projX4 := [ [ #(L @ proj4[1]) , #(L @ proj4[2]) ] : L in subsX4 ];
*/

/*
Y, i, p := DirectProduct (G2, G3);
subsY := CharSubgroupsSpecial (Y : FullGraph := true);
ordsY := [ #L : L in subsY ];
*/

PIsomG := sub< Generic(GL(9,3)) | GL(9,3)!DiagonalJoin(
    Matrix([[2,0,1,1,2,1],[0,2,2,2,1,2],[0,2,0,2,1,1],[0,2,0,1,0,1],[0,1,1,1,0,2],[0,0,2,2,1,1]]),
    Matrix([[1,2,1],[1,0,2],[1,1,1]])), GL(9,3)!DiagonalJoin(
    Matrix([[0,0,0,0,1,0],[0,1,2,1,1,2],[1,1,1,1,2,1],[0,1,0,2,0,1],[1,0,0,0,0,0],[0,0,1,2,2,2]]),
    Matrix([[2,0,0],[0,2,0],[0,0,2]])) >;
    
IsPseudoIsometry := function (g, S)
MS := KMatrixSpaceWithBasis (S);
return forall { F : F in S | g * F * Transpose (g) in MS };
end function;

g := ExtractBlock (PIsomG.1, 1, 1, 6, 6);
assert IsPseudoIsometry (g, S);
U := KMatrixSpaceWithBasis (S);
l := sub < U | [ S[1] , S[2] ] >;
m := sub < U | [ g*S[1]*Transpose(g) , g*S[2]*Transpose(g) ] >;
ls := Genus2Sig (l);
lm := Genus2Sig (m);


// Here are a couple of examples, where the genus 2 labeling tells you more
// than the slope labeling, but doesn't produce characteristic subgroups.
// Note, the Derivation algebra only acts as scalars on W here!
// The first is a quotient of a Heisenberg group, and the send a quotient
// of a twisted Heisenberg group.

bad1 := PCGroup(\[ 14, -3, 3, 3, 3, 3, 3, 3, 3, 3, 3, -3, 3, 3, 3, 248026217, 1660195, 
1655673, 3307547, 1653685, 5858250, 5810636, 11581576, 5789496, 5073326, 
20085415, 39762597, 19867715, 17400145, 411327, 67788260, 134198716, 40599504, 
1959602, 1112518, 225960849, 196567583, 4898917, 7450431, 3708245 ]);

bad2 := PCGroup(\[ 14, -3, 3, 3, 3, 3, 3, 3, 3, 3, 3, -3, 3, 3, 3, 252986333, 1660195, 
1655673, 3307547, 1653685, 5858250, 5810636, 11581576, 5789496, 4787558, 
20085415, 39762597, 19867715, 16420369, 411327, 67788260, 134198716, 43906248, 
1959602, 1112518, 225960849, 185545103, 4898917, 7450431, 3708245 ]);

