
UpperTriangularLie := function(d,p)
  G := ClassicalSylow(GL(d,p),p);
  U := PCPresentation( UnipotentMatrixGroup(G));
  F := pCentralFilter(U);
  L := LieAlgebra(F);
  return L;
end function;
