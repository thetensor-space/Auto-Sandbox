intrinsic ProduceFilter (G:: GrpPC: S := []) -> [], [], []
{produce filter; return filter, char subgroups, associated spaces;
 S can be used to pass in known characteristic subgroups}
   F := pCentralFilter (G);
   Q := Refine (F);
   I := Image (Q);
   if #S eq 0 then 
      S, U := VerbalChar (G);
   end if;
   for i in [1..#S] do 
      H := S[i];
      if not (H in I) then 
        "process i = ", i;
        gens := [G!H.j: j in [1..NPCgens (H)]]; 
        Q := ConstructFilter (Q, gens);
        I := Image (Q);
      end if; 
   end for;
   T := I cat S;
   T := Set (T);
   T := [x : x in T];
   return I, T, U;
end intrinsic;

/* 
G := 
PCGroup(\[ 7, -11, 11, 11, 11, -11, 11, 11, 1127357, 205129, 11366748, 307701, 
2154784, 410273, 40988 ]);

I, C, U := ProduceFilter (G);

U := [x[1] : x in U | x[2] eq 1];
S := StabiliserOfSpaces (U);

*/
