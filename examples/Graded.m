
UpperTriangularLie := function (d, p)
  G := ClassicalSylow (GL (d,p), p);
  U := PCPresentation (UnipotentMatrixGroup (G));
  F := pCentralFilter (U);
  L := LieAlgebra (F);
  return L;
end function;


/*
   Here are some examples we can use to test the Ruth-N functions
     (added by PAB on 3/30/2022)
*/

__random_subspace := function (W, s)
assert s lt Dimension (W);
     bas := [];
	 while #bas le s do
          w := Random (W);
		  if Dimension (sub < W | bas >) lt Dimension (sub < W | bas , w >) then 
		       Append (~bas, w);
		  end if;
	 end while;
return sub < W | bas >;
end function;

// first a construction for graded Lie algebras
SubspaceConfigurationLie := function (d, p, m)    // m is the total number of subspaces

     L := UpperTriangularLie (d, p);
     comps, projs := HomogeneousComponents (L);
     dims := [ Dimension (X) : X in comps ];
	 assert dims eq [d-i : i in [1..d-1] ];
	 config := [* *];
     for i in [1..m] do
          j := Random ([1..#comps]);
		  if dims[j] gt 1 then
               s := Random ([1..dims[j]-1]);   // proper subspace
		  end if;
		  Append (~config, __random_subspace (comps[j], s));
	 end for;

return config, L, projs;
end function;

// associative examples
__RUT_pos := function (n)
     i := Random ([1..n-1]);
     j := Random ([i+1..n]);
return i, j;
end function;

__RUT_matrix := function (K, n)
     f := Floor (n/2);
     m := Random ([n-f..n+f]);
     x := MatrixAlgebra (K, n)!0;
     for s in [1..m] do
          i, j := __RUT_pos (n);
          x[i][j] := Random (K);
     end for;
return x;
end function;

RandomUpperTriangular := function (K, d : num_gens := 3)
     MA := MatrixAlgebra (K, d);
     gens := [ __RUT_matrix (K, d) : i in [1..num_gens] ];
     T := sub < MA | gens >;
return T;
end function;