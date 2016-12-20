/* James' examples for foxing standard approaches */

p := 3; e := 5; 
H := HeisenbergGroup (p, e);

SystemOfForms (pCentralBimap (H, 1, 1));

G1 := RandomQuoByGenus (H, 4);

subsG1a := CharacteristicSubgroups (G1);
subsG1b := CharacteristicSubgroups (G1 : LineSigFn := Genus2Sig);
subsG1c := CharacteristicSubgroups (G1 : FullPartition := true);
subsG1d := CharacteristicSubgroups (G1 : FullPartition := true,
                                         LineSigFn := Genus2Sig);
[ #subsG1a , #subsG1b , #subsG1c , #subsG1d ];

T := TwistedHeisenbergGroup (p, e);
G2 := RandomQuoByGenus (T, 4);

subsG2a := CharacteristicSubgroups (G2);
subsG2b := CharacteristicSubgroups (G2 : LineSigFn := Genus2Sig);
subsG2c := CharacteristicSubgroups (G2 : FullPartition := true);
subsG2d := CharacteristicSubgroups (G2 : FullPartition := true,
                                         LineSigFn := Genus2Sig);
[ #subsG2a , #subsG2b , #subsG2c , #subsG2d ];



