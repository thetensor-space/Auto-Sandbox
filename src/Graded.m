

Search := function( U, L, Member )
  T := [1];
  uOrder := LMGOrder(U);
  lOrder := LMGOrder(L);
  
  p := Characteristic(BaseRing(U));
  Syl := LMGSylowSubgroup(U,p);

  g := Random(U);
  Tra := Syl^g;  // Almost a transversal
  
  C := Set(LMGRightTransversal(U, S));

  vprint Autotopism, 1 : "Orderly search.";
  t2 := Cputime();
  C := Set(LMGRightTransversal(U, L));
  while #C gt 0 do
	//Grab a random coset.
	h := Random(C);
	Exclude(~C,h);
	
	//Test if h lifts.
	if Member(h) then
	  L := sub<U | Generators(L) join {h} >;

	new, Subgroup := __test_pseudo_extension(T,Supergroup,Subgroup,h);
	if new then
	  LW := Subgroup @ piW;
	  olw := LMGOrder(LW);
	  if #C gt (ouw div olw) then 
		  C := Set(LMGRightTransversal(UW,LW));
		  __THE_INDEX,__THE_V_INDEX,__THE_W_INDEX := __report(Supergroup, Subgroup, piV,piW);
	  end if;
	end if;
	if (#C mod 500) eq 0 then 
		vprint Autotopism, 2 : "Still left to search ", #C;
	end if;
	
  end while;
  t2 := Cputime(t2);
  vprint Autotopism, 1 : "Small set search time ", t2;
  // Here we can certify the subgroup is the whole group.
  return Subgroup, Subgroup, t+t2;

  for c
  while uOrder div lOrder gt |T| do
    
  end while;

  return L;
end function;


intrinsic IsGradedIsomorphic( A::., B::. ) -> BoolElt, .
{Test isomorphism of graded algebras; if isomorphic also return an isomorphism.}

  dims := [ Dimension(Domain(A[s])[2]) : T in A ];

  


  return false, _;
end intrinsic;