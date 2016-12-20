/* 

  Main procedure to find characteristic subgroups (other than the
  Frattini subgroup) of a p-group G that we assume has p-class 2.

  The plan is to proceed sequentially through the following steps,
  where B = B(G) is the bimap associated to G, only moving to the next 
  step if we failed to find characteristic subgroups/ideals at that step.

  Step 1. See if B has a characteristic ideals arising from derivations.
  
  Step 2. See if B has a characteristic ideals arising from Omega, etc.
  
  Step 3. See if B has a characteristic ideals arising from breadth.
  
  Step 4. See if fingerprinting finds characteristic ideals of B.
  
  Step 5. See if characteristic subgroups can be found in G using
          Blackburn's classification on the quotients G/M, as M runs
          through maximal subgroups of the Frattini subgroup.
          
  Step 6. See if local data from one of various projective spaces can be 
          leveraged to produce characteristic ideals of B.
          
  Need to put in safety mechanisms between steps to avoid computations that
  will be overly expensive.
  
*/


CharacteristicSubgroups := function (G)

     B := PGroupToBimap (G);

     // Step 1. Characteristic ideals from derivations. 
     
     
     // Step 2. Characteristic ideals from Omega, etc.


     // Step 3. Characteristic ideals from breadth.
     
     
     // Step 4. Characteristic ideals/subgroups from fingerprinting.
     
     
     // Step 5. Characteristic ideals/subgroups from projective points.
     
        // first, Blackburn ...
        chars := BlackburnInvariants (G);
        if #chars gt 0 then
             return chars;
        end if;
     
     
     // Step 6. Characteristic ideals/subgroups from projectives lines.
     




end function;


// needed: conversion from char. ideal of bimap to char. subgroup of group