/*
==========================================================================================
 Developer's note (James Wilson, June 1, 2016).

 This is a straight-forward test, clouded by error checking, routing, and reporting.  
 We build all algorithms on top of the Tensor package of Maglione-Wilson, 2016, 
 based on the pre-print 
 
 First-Maglione-Wilson, "Polynomial identity tensors and their invariants".
 
 The algorithm takes in a symmetric or alternating tensor T and groups U, L where 
 
	  L < PIsom(T) < U.
 
 The defaults are L = 1 x 1 and U = GL(V) x GL(W).

 Next it adds to L the subgroups proven to exists in 

 Wilson, "On automorphisms of groups, rings, and algebras", Comm. Alg., 2016.

 These include Isom(T) and its left-right generalization.  It uses the algorithm of

 Brooksbank-Wilson, "Isometry groups of Hermitian maps", TAMS, 2012.

 This would improve by adopting Ivanyos for Wedderburn decomposition and 
 Wilson for Gram-Schmidt.  It would also help to develop the over groups by the
 method of Norm-* (adapted to the exact sequences of Wilson 2016 above) along
 the lines of the algorithms of
 
 Brooksbank-Wilson "Groups acting on tensor products", JPAA, 2014.

 It also compute exp(Der(T)).  It uses Lie algebra recognition of Willem de Graaf, 
 Chevalley bases by Taylor.	 This may improve by adopting Ryba's theorems.


 Next it compares [U|_V : L|_V] to [U|_W : L|_W], choosing the smaller and enter
 a loop with the following loop invariant:
 
		L <= PIsom(T) <= U.
 
 Working in the smallest index representation, it picks a random coset xL|_v, 
 or respectively xL|_W.	 Critically it chooses from the induced representation 
 because otherwise the perhaps massive size of the kernel makes for sampling
 from a much larger set.
 
  - In the case the restriction is to V, then induce x on W by applying
	xTx: <u,v> :-> <ux,vx>@T
  Test if this induces a pseudo-isometry (test given directly).
  
  - In the case the restriction is to W, then induce
	T^x: <u,v> :-> <u,v>@T*x
  Use the (unpublished) algorithm of Ivanyos-Qiao 2016, as implemented 
  by Brooksbank-Wilson, to test if T and T^x are isometric, and if so, find
  y such that (y,x) is a Pseudo-isometry of T.
  
 If the test pass, then the discovered pseudo-isometry is added to L.  At this
 stage the cosets are re-computed, the smallest cosets selected, and the process
 begins again.
 
 If the test fails then repeat the random sampling until one of following events occurs:

  (a) we exceed a limit set in GlobalVars.m __LIMIT;
  (b) we have randomly sampled a quantity proportional to the number of cosets
  without change; or
  (c) the number of cosets is below a threshold in GlobalVars.m __SMALL.
 
 If the loop exits and L is not equal to U then if the number of cosets exceeds
 the limit then we quit, returning L and U and report the failure.
 
 If the loop exits with (U/L)|_V or (U/L)|_W below the limit, then we continue
 with the identical loop but now we enumerate the cosets rather than proceeding
 randomly.	Keep note, even within this deterministic loop if L is increased then
 new cosets representatives are computed and the loop is tightened.	 This loop
 exits when:
 
	L = PIsom(T) = U.
 
==========================================================================================
*/

import "GlobalVars.m" : __SANITY_CHECK, __LIMIT, __SMALL;
import "Util.m" : Adj2, __vector_to_matrix;
//import "DerAuto.m" : ExponentiateDerivations;

/**

  Given tensors $S$ and $T$ into a common vector space, 
  decides if they are isometric.
  
  The algorithm decides if $S$ and $T$ are isotopic by
  principal isotopism by computing $Adj(S,T)$ and identifying
  an invertible element.  Selection of an invertible element $t$
  of $Adj(S,T)$ follows Brooksbank-Luks.
  
  Next, the algorithm solve for $a\in Adj(T)$ with $t^*t=N(a)$.
  Such an $a$ exists if, and only if, $ta$ is an isometry $S->T$.
  
  */
intrinsic IsIsometric( S::TenSpcElt, T::TenSpcElt) -> Mtrx
{Decides if given tensors are isometric.}

  require IsAlternating(S) or IsSymmetric(S) : 
	"First argument is not alternating or symmetric.";
  require IsAlternating(T) or IsSymmetric(T) : 
	"Second argument is not alternating or symmetric.";
  
  e := Dimension(Codomain(S));
  d := Dimension(Domain(S)[1]);
  if not (e eq Dimension(Codomain(T)) and d eq Dimension(Domain(T)[1])) then
	return false, _;
  end if;
  if e*d eq 0 then return true, ZeroMatrix(BaseRing(S),0,0); end if;

  SF := SystemOfForms(S);
  TF := SystemOfForms(T);
	 
  /* find U, V of full rank with U * S[i] = T[i] * V^t */
  space := Adj2(SF, TF);
  if Dimension (space) eq 0 then return false, _; end if;

  //  TBD: This part can surely be made deterministic, a la Brooksbank-Luks
  LIMIT := 20;
  i := 0;
  found := false;
  while (i lt LIMIT) and (not found) do
	i +:= 1;
	U,V := __vector_to_matrix(Random (space), d,d);
	if __SANITY_CHECK then
	  assert forall { i : i in [1..e] | U * SF[i] eq TF[i] * Transpose (V) };
	end if;
	if (Rank (U) eq d) and (Rank (V) eq d) then
	  found := true;
	end if;
  end while;
  if (not found) then
	// This is Monte Carlo!	 Will need to change.
	vprint Autotopism, 2 : "Monte carlo test of invertible failed.";
	return false, _;
  end if;
	 
  /* solve the adjoint algebra problem */
  A := AdjointAlgebra (T); // Call it on T so it can retrieve pre-computed adj.
	 
  s := (U * V)^-1;
  if __SANITY_CHECK then
	assert s in A;
	assert s eq (s @ A`Star);
  end if;
  isit, a := InverseNorm (A, s);
  if not isit then return false, _; end if;
  
  g := a * U;

  if __SANITY_CHECK then  
	assert forall { i : i in [1..e] | g * SF[i] * Transpose (g) eq TF[i] };
  end if;	
  return true, g;
end intrinsic;


//-------------------- PSEUDO-ISOMETRIES--------------------------------------------------

intrinsic IsPseudoIsometry(T::TenSpcElt, X::Mtrx, Y::Mtrx) -> BoolElt
{Decides if the given pair of matrices a pseudo-isometry.}
// TBD: add require flags.

  S := SystemOfForms(T);
  LHS := [ X*S[i]*Transpose(X) : i in [1..#S] ];
  RHS := [ &+[ Y[i][j]*S[i] : i in [1..#S] ] : j in [1..Ncols(Y)] ];
  return LHS eq RHS;
  
end intrinsic;

__test_pseudo_extension := function(T, Supergroup, Subgroup, h)
  if h eq Parent(h)!1 then return false, Subgroup; end if;
	
  // Use Ivanyos-Qiao 2016 to test extension of h to pseudo-isometry.
  // Developer's note.	T will not change, and its adjoints can be computed once.
  // The IsIsometric test will need to compute Adj(S,T) as well as Adj(T).
  // So make S the one from h, i.e, by h^(-1).
  Txinv := Tensor(Frame(T),func<u| (u@T)*h^(-1)>);
  isit, finv := IsIsometric(Txinv,T); 
  if not isit then return false, Subgroup; end if;
	
  if __SANITY_CHECK then
	assert IsPseudoIsometry(T,finv^(-1),h^(-1));
  end if;
  z := DiagonalJoin( finv^(-1), h^(-1) );
  if z in Subgroup then return false, Subgroup; end if;
	  
  assert z in Supergroup;
  return true, sub<Supergroup| Subgroup,z>;
end function;

__report := function(U,L, piV,piW)
  // This is for developing the tool, it profiles what is changing.
  // Some of this is not worth computing so should be turned off after testing.
  
  __THE_INDEX := ISA(Type(L), BoolElt) select LMGOrder(U) else LMGIndex(U,L);
  bits := Ceiling(Log(2,__THE_INDEX));
  p := Characteristic(BaseRing(U));
//  vprint Autotopism, 1 : "INDEX:\t\t\t\t",	__THE_INDEX,
//  "(",bits, "bits)";
  
  UV := U @ piV;
  LV := L @ piV;
  __THE_V_INDEX := LMGIndex(UV,LV);
  bits := Ceiling(Log(2,__THE_V_INDEX));
  d := Degree(UV);
  vprint Autotopism, 1 : "\tINDEX ON V:\t\t\t", bits,"/", Ceiling(d^2*Log(2,p)), "bits";

  UW := U @ piW;
  LW := L @ piW;
  __THE_W_INDEX := LMGIndex(UW,LW);
  bits := Ceiling(Log(2,__THE_W_INDEX));
  e := Degree(UW);
    vprint Autotopism, 1 : "\tINDEX ON W:\t\t\t", bits,"/", Ceiling(e^2*Log(2,p)), "bits.";

  return __THE_INDEX, __THE_V_INDEX, __THE_W_INDEX;
end function;

__SearchCosetsW := function(T, Supergroup, Subgroup, piV, piW, __THE_W_INDEX, MAX )
    vprint Autotopism, 1 : 
	"Randomly searching cosets testing pseudo-isometry by Ivanyos-Qiao algorithm.";

  UW := Supergroup @ piW;
  LW := Subgroup @ piW;
  t := Cputime();
  count := 0; 
  Stop := Min(MAX, __THE_W_INDEX div 2); // quit if you have searched half the space.
  while (count lt Stop) and (__THE_W_INDEX gt __SMALL) do
	h := Random(Supergroup@piW);
	new, Subgroup := __test_pseudo_extension(T,Supergroup, Subgroup, h);
	if new then
	  vprint Autotopism, 2 : "Found pseudo-isometry by Ivanyos-Qiao algorithm.";
	  UW := Supergroup @ piW;
	  LW := Subgroup @ piW;
	  ouw := LMGOrder(UW);
	  olw := LMGOrder(LW);
	  __THE_W_INDEX := ouw div olw;
	  // Adapt how long you will search at random if it starts to get small.
	  // Use a birthday-paradox bound multiplied by slower cost of full test.
	  Stop := Min(MAX, __THE_W_INDEX div 2);//Min(MAX-count, 2*SquareRoot(ou div ol))+count; 
	  vprint Autotopism, 1 : "INDEX ON W:...........................",
	  	ouw div olw;
	end if;
	count +:= 1;
	if (count mod 1000) eq 0 then
	  vprint Autotopism, 1 : 
		"Still randomly searching ", __THE_W_INDEX, " cosets.";
	end if;
  end while;
  vprint Autotopism, 1 : "Random search exceeded ", count, " quiting.";
  t := Cputime(t);
  vprint Autotopism, 1 : "Random set search time ", t;
  
  if __THE_W_INDEX gt MAX then 
	print "Search exceeded limit of ", MAX, 
		"\n\t returning Super- and Sub-group containing actual.";
	 __THE_INDEX,__THE_V_INDEX,__THE_W_INDEX := __report(Supergroup, Subgroup, piV,piW);
	return Supergroup, Subgroup;
  end if;

  
  __THE_INDEX,__THE_V_INDEX,__THE_W_INDEX := __report(Supergroup, Subgroup, piV,piW);

  // End of the line, only a small coset space search it all.
  //------------------------------------------------------------------------------------
  // Caution: the # of cosets is small, but the action of Supergroup
  // on V wedge V is still potentially quit large. Need a secondary
  // test to know if that would be profitable, here we continue working
  // on the cosets.
  //------------------------------------------------------------------------------------
  vprint Autotopism, 1 : "Now searching orderly.";
  t2 := Cputime();
  C := Set(LMGRightTransversal(UW, LW));
  if __SANITY_CHECK then
  	assert #C eq __THE_W_INDEX;
  end if;
  ouw := LMGOrder(Supergroup@piW);
  while #C gt 0 do
	//Grab a random coset.
	h := Random(C);
	Exclude(~C,h);
	
	//Test if h lifts.
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
end function;

intrinsic PseudoIsometryGroup(T::TenSpcElt :  // Symmetric or alternating tensor.
  Supergroup:=false,			  // Group containing pseudo-isometry group.
  Subgroup:=false,				// Group contained in pseudo-isometry group.
  MAX := __LIMIT,				// Maximum search permitted.
  UseGraph := true				// Use the graph methods.
) -> GrpMat, GrpMat				  // Reduced super-, sub- group pair
{Computes generators for the group of pseudo-isometries of a tensor.}

  /* reduce to the nondegenerate case */
  if not IsFullyNondegenerate(T) then
  	vprint Autotopism, 1 : "Degenerate case not yet implemented.";
  	return Supergroup, Subgroup;
/*  	
  	rad := Radical(T)[1];
  	V := Domain(T)[1];
  	C := Complement(V,rad);
  	
  	W := Codomain(T);
  	I,iota := Image(T);
  	D := Complement(W,I);
  	
  	T0 := Subtensor(T,[* C,C, I *]);

	Supergroup0 := Supergroup;
	for h in Generators(R) do
		Supergroup0 := Stabilizer(Supergroup0,h);
	end for;
	// Now this is 1 on R so C can restrict to C.
	
	U0, L0 := PseudoIsometryGroup(T0 : Supergroup:=Supergroup0);
	
	// Add back the full maps on R->V.
  	return Supergroup,  Subgroup;
*/
  end if;

  require IsAlternating(T) or IsSymmetric(T) :
	"First argument should be alternating or symmetric.";
  
  K := BaseRing(T);
  d := Dimension(Domain(T)[1]);
  e := Dimension(Codomain(T));
  V := Domain(T)[1];
  W := Codomain(T);

  iotaV := hom<GL(d,K)->GL(d+e,K) | x:->DiagonalJoin(x,IdentityMatrix(K,e))>;
  iotaW := hom<GL(e,K)->GL(d+e,K) | x:->DiagonalJoin(IdentityMatrix(K,d), x)>;
  piV := hom<GL(d+e,K)->GL(d,K) | x:->ExtractBlock(x,1,1,d,d)>;
  piW := hom<GL(d+e,K)->GL(e,K) | x:->ExtractBlock(x,d+1,d+1,e,e)>;
  
  // Decide on appropriate super- and sub-groups.
  if ISA(Type(Supergroup), GrpMat) then
	require Supergroup subset GL(d+e,K) :
	  "Supergroup should be contained in GL(V+W).";
  else
	// By default GL(d,K) x GL(e,K)
	GV:=sub<GL(d+e,K)|[DiagonalJoin(g,IdentityMatrix(K,e)):g in Generators(GL(d,K))]>;
	GW:=sub<GL(d+e,K)|[DiagonalJoin(IdentityMatrix(K,d),g):g in Generators(GL(e,K))]>;
	Supergroup := sub<GL(d+e,K) | GV, GW >;
  end if;
  if ISA(Type(Subgroup), GrpMat) then
	require Subgroup subset Supergroup :
	  "Subgroup should be contained in supergroup.";
  else
	Subgroup := sub<Supergroup|[]>;
  end if;

  __THE_INDEX,__THE_V_INDEX,__THE_W_INDEX := __report(Supergroup, Subgroup, piV,piW);
  
  // Use Brooksbank-Wilson TAMS 2012 to add isometries.-----------------------------------
  vprint Autotopism, 1 : "Adding isometries by Brooksbank-Wilson algorithm.";
  I := IsometryGroup(SystemOfForms(T));
  Subgroup := sub<Supergroup | Subgroup, I @ iotaV >;
  __THE_INDEX,__THE_V_INDEX,__THE_W_INDEX := __report(Supergroup, Subgroup, piV,piW);
  
  // PENDING: add (L+R)^# 
  
  // Add exp(L) where Der(T)=L+N a Levi decomposition.------------------------------------
  vprint Autotopism, 1 : "Adding exponential of derivations by Brooksbank-Maglione-Wilson.";
  Subgroup := ExponentiateDerivations(T);
//  D := DerivationAlgebra(T);  // Should check that the category has 1,2 fused.
  // PENDING: add the nilradical.
//  doesit, L := HasLeviSubalgebra(D);
//  if doesit then
//	A := ExponentiateLieAlgebraSS(L);
	// Temporary issue, the return is on U,V,W, should be on V,W
//	gensVW := [ExtractBlock(g,1+d,1+d,d+e,d+e) : g in Generators(A)];
//	Subgroup := sub<Supergroup| Subgroup, gensVW>;
//  end if;
  __THE_INDEX,__THE_V_INDEX,__THE_W_INDEX := __report(Supergroup, Subgroup, piV,piW);

// NOW LOWER THE SUPER GROUP--------------------------------------------------------------
  	if UseGraph and Log(2,__THE_W_INDEX) gt (2*(e-2)) then
		vprint Autotopism, 1 : "Entering graph cut down....";
		// PENDING: we should very much like to pass GW to CharSubs here so we don't throw
		// out what we have already found.
		//	subs, inv, GW2 := CharacteristicSubgroups(G: FullGraph:=FullGraph);
		GV := Supergroup @ piV;
		GW := Supergroup @ piW;
		GW2 := ActionOnCenter(T);
		if LMGOrder(GW) gt LMGOrder(GW2) then
			vprint Autotopism, 1 : "Using graph";
			GW := GW2;
			Supergroup := sub<GL(d+e,K) | [x@iotaW : x in Generators(GW)] cat [x@iotaV: x in Generators(GV)]>;
		else
			vprint Autotopism, 1 : "Relabeling graph with full signatures.";
			GW2 := ActionOnCenter(T : LineLabel := "Genus2Sig" );
			if LMGOrder(GW) gt LMGOrder(GW2) then
				vprint Autotopism, 1 : "Using graph";
				GW := GW2;
				Supergroup := sub<GL(d+e,K) | [x@iotaW : x in Generators(GW)] cat [x@iotaV: x in Generators(GV)]>;
			else
				vprint Autotopism, 1 : "Graph did not help.";
			end if;
		end if;
	end if;
    __THE_INDEX,__THE_V_INDEX,__THE_W_INDEX := __report(Supergroup, Subgroup, piV,piW);

	

  // FUTURE: consider N^* methods.--------------------------------------------------------
/*
  vprint Autotopism, 1 : "Comparing over group by Brooksbank-Wilson N^* algorithm.";
  WA := NucleusClosure(Parent(T),T,2,1);
  vprint Autotopism, 1 : "Adjoint tensor has dimension ", Dimension(WA),
  	"max search space ", Ceiling(Dimension(WA)^2*Log(2,Characteristic(K))), "bits.";
  
  Nstar := NormStar(SystemOfForms(T));
  ons := LMGOrder(Nstar);
  olv := LMGOrder(Subgroup@piV);
  vprint Autotopism, 1 : "Estimated N^* index ", Ceiling(Log(2,ons div olv)), " bits.";
    
  if ons lt LMGOrder(Supergroup) then
  	// PENDING: this step will need some testing, for now unimplemented, so skipping.
  	// Supergroup := NStar; // really want intersect Supergroup, but that costs a lot.
  	// WA, tau := NucleusClosure(Parent(T),T,2,1);  
  	// piW := piW * tau;
  	
  	vprint Autotopism, 1 : "TBD: Add N^* as over group and replace W with adjoint-tensor.";
  end if;
  __THE_INDEX,__THE_V_INDEX,__THE_W_INDEX := __report(Supergroup, Subgroup, piV,piW);
*/

  // Work down the cosets, randomly-------------------------------------------------------
  if __THE_W_INDEX lt MAX then
	  Supergroup, Subgroup, t := __SearchCosetsW(T, Supergroup,Subgroup,piV, piW, __THE_W_INDEX, MAX);
	  vprint Autotopism, 1 : "Total time ", t;
	else
		vprint Autotopism, 1 : "Aborting, index too large.";
   end if;
 

  // Guaranteed that the subgroup is right.
  return Supergroup, Subgroup;
end intrinsic;

intrinsic ProfileTensor( T::TenSpcElt )
{}
	rad := Radical(T);
	print "Radical of dimension ", Dimension(rad[1]);
	
	print "Adjoint algebra.";
	A := AdjointAlgebra(T);
	can := RecogniseStarAlgebra(A);
	J, T := TaftDecomposition(A);
	print "\tAdjoint algebra of dimension ", Dimension(A);
	c := 1;
	N := J;
	while Dimension(N) gt 0 do N:=N*J; end while;
	print "\tJacobson radical dimension ", Dimension(J), " and nilpotence class ", c;
	
	D := DerivationAlgebra(T);
	
	
end intrinsic;