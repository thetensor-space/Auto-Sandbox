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

import "bimap_labels.m": RANK_LABEL, SLOPE_LABEL, GENUS2_LABEL;

// EOB -- use new or old graph method? Also decide label functions
NEW := true;
point_label := RANK_LABEL;
line_label := GENUS2_LABEL;
line_label := SLOPE_LABEL;

import "GlobalVars.m" : __SANITY_CHECK, __LIMIT, __SMALL;
import "Util.m" : Adj2, __vector_to_matrix;

__EXHAUSTIVE_SEARCH_LIMIT := 10^8;

// NEEDS TO BE EXPANDED ... JUST SYMMETRIC AND ALTERNATING RIGHT NOW
intrinsic IsHermitianBimap (T::TenSpcElt) -> BoolElt
  {Decides if the given tensor is an Hermitian bimap.}
return IsAlternating (T) or IsSymmetric (T);
end intrinsic;


// some version might be an intrinsic at some stage
__nondegenerate_tensor := function (T)
  D := Domain (T);
  U := D[1];
  V := D[2];
  RAD := Radical (T);
  RU := RAD[1];
  RV := RAD[2];
  if (Dimension (RU) eq 0) and (Dimension (RV) eq 0) then  // T already nondegenerate
      return Identity (GL (Dimension (U), BaseRing (U))), 
             Identity (GL (Dimension (V), BaseRing (V))),
             T;
  end if;
  U0 := Complement (U, RU);
  V0 := Complement (V, RV);
  f := GL (Dimension (U), BaseRing (U))!Matrix (Basis (U0) cat Basis (RU));
  if IsHermitianBimap (T) then
      g := f;
  else
      g := GL (Dimension (V), BaseRing (V))!Matrix (Basis (V0) cat Basis (RV));
  end if;
  TT := IsotopicImage (T, <f,g,Identity (GL (Dimension (Codomain (T)), BaseRing (T)))>);
  SS := SystemOfForms (TT);
  S0 := [ ExtractBlock (SS[i], 1, 1, Dimension (U0), Dimension (V0)) : i in [1..#SS] ];
  T0 := Tensor (S0, 2, 1);
return f, g, T0;
end function;



/*

  Given tensors $S$ and $T$ into a common vector space, 
  decides if they are isometric.
  
  The algorithm decides if $S$ and $T$ are isotopic by
  principal isotopism by computing $Adj(S,T)$ and identifying
  an invertible element.  Selection of an invertible element $t$
  of $Adj(S,T)$ follows Brooksbank-Luks.
  
  Next, the algorithm solve for $a\in Adj(T)$ with $t^*t=N(a)$.
  Such an $a$ exists if, and only if, $ta$ is an isometry $S->T$.
  
*/
__IsIsometric_ND := function (S, T) 
  
  e := Dimension (Codomain (S));
  d := Dimension (Domain (S)[1]);
  if not (e eq Dimension (Codomain (T)) and d eq Dimension (Domain (T)[1])) then
	return false, _;
  end if;
  if e*d eq 0 then return true, ZeroMatrix (BaseRing (S),0,0); end if;

  SF := SystemOfForms (S);
  TF := SystemOfForms (T);
	 
  /* find U, V of full rank with U * S[i] = T[i] * V^t */
  space := Adj2 (SF, TF);
  
  if Dimension (space) eq 0 then return false, _; end if;

  //  TBD: This part can surely be made deterministic, a la Brooksbank-Luks
  N := NullSpace (__vector_to_matrix(space.1, d, d));
  for i in [2..Ngens (space)] do
	  N := N meet NullSpace (__vector_to_matrix(space.i, d, d));
	  if Dimension (N) eq 0 then
	  	break;
	  end if;
  end for;
  if Dimension (N) gt 0 then 
	  return false, _;
  end if;
	
  LIMIT := 20 * Dimension (space);
  i := 0;
  found := false;
  while (i lt LIMIT) and (not found) do
		i +:= 1;
		U, V := __vector_to_matrix(Random (space), d, d);
		if __SANITY_CHECK then
	  	   assert forall { i : i in [1..e] | U * SF[i] eq TF[i] * Transpose (V) };
		end if;
		if (Rank (U) eq d) and (Rank (V) eq d) then
	  	   found := true;
		end if;
  end while;
  if (not found) then
		// This is Monte Carlo!	 Will need to change.
		vprint Autotopism, 3 : "\t[WARNING] : Monte carlo test of invertible failed.";
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
  	
return true, GL (Nrows (g), BaseRing (Parent (g)))!g;

end function;




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

  // EOB replace next 3 line 
  // if z in Subgroup then return false, Subgroup; end if;
  //
  // assert z in Supergroup;
  // return true, sub<Supergroup| Subgroup,z>;
  
  z := Generic(Supergroup) ! z;
  if LMGIsIn (Subgroup, z) then return false, Subgroup; end if;
  assert LMGIsIn (Supergroup, z);
  return true, sub<Generic (Supergroup)| Subgroup,z>;
end function;

__report := function(U,L, piV,piW)
  // This is for developing the tool, it profiles what is changing.
  // Some of this is not worth computing so should be turned off after testing.
  
  __THE_INDEX := ISA(Type(L), BoolElt) select LMGOrder(U) else LMGOrder(U) div LMGOrder(L);
   // EOB -- bug in Index when L is trivial 
   //  __THE_INDEX := ISA(Type(L), BoolElt) select LMGOrder(U) else LMGIndex(U,L);
  bits := Ceiling(Log(2,__THE_INDEX));
  p := Characteristic(BaseRing(U));
  vprint Autotopism, 1 : "INDEX:\t\t\t\t",	__THE_INDEX, "(",bits, "bits)";
  
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
  ouw := LMGOrder(UW);
  LW := Subgroup @ piW;
  t := Cputime();
  count := 0; 
  My_Search_Limit := 2^20;
  Stop := Min(My_Search_Limit, __THE_W_INDEX div 2); // quit if you have searched half the space.
  while (count lt Stop) and (__THE_W_INDEX gt __SMALL) do
	h := Random(UW);
	new, Subgroup := __test_pseudo_extension(T, Supergroup, Subgroup, h);
	if new then
	  vprint Autotopism, 2 : "Found pseudo-isometry by Ivanyos-Qiao algorithm.";
	  LW := Subgroup @ piW;
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
  // on V wedge V is still potentially quite large. Need a secondary
  // test to know if that would be profitable, here we continue working
  // on the cosets.
  //------------------------------------------------------------------------------------
  vprint Autotopism, 1 : "Orderly search.";
  t2 := Cputime();
  vprint Autotopism, 1: "First call to LMGRightTransversal";
time  C := Set(LMGRightTransversal(UW, LW));
  if __SANITY_CHECK then
  	assert #C eq __THE_W_INDEX;
  end if;
  Exclude (~C, Rep (C)^0);
  // ouw := LMGOrder(Supergroup@piW);
  olw := LMGOrder (LW);
  while #C gt 0 and ouw gt olw do
	//Grab a random coset.
	h := Random(C);
	Exclude(~C,h);
	
	//Test if h lifts.
	new, Subgroup := __test_pseudo_extension(T,Supergroup,Subgroup,h);
	if new then
	  LW := Subgroup @ piW;
	  olw := LMGOrder(LW);
	  if #C gt (ouw div olw) then 
		time  C := Set(LMGRightTransversal(UW,LW));
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
		for h in Generators(DirectSum(rad,W)) do
			Supergroup0 := Stabilizer(Supergroup0,h);
		end for;
		
		// Now Subgroups0 is 1 on rad so T0 can restrict to C.
		U0, L0 := PseudoIsometryGroup(T0 : Supergroup:=Supergroup0);
	
		// Add back the full maps on R->V.
		
  	return Supergroup,  Subgroup;
*/
  end if;

  require IsAlternating(T) or IsSymmetric(T) :
		"First argument should be alternating or symmetric.";
  
  K := BaseRing(T);
  d0 := Dimension(Domain(T)[1]);
  d := Degree(Domain(T)[1]);
  e0 := Dimension(Codomain(T));
  e := Degree(Codomain(T));
  
  V := Parent(Domain(T)[1]);
  W := Parent(Codomain(T));

  iotaV := hom<GL(d,K)->GL(d+e,K) | x:->DiagonalJoin(x,IdentityMatrix(K,e))>;
  iota0V := hom<GL(d0,K)->GL(d+e,K) | x:->DiagonalJoin(x,IdentityMatrix(K,(d-d0)+e))>;
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
  if GetVerbose("Autotopism") gt 0 then
    I := IsometryGroup(SystemOfForms(T));
  else
    I := IsometryGroup(SystemOfForms(T) : DisplayStructure:=false);
  end if;
  Subgroup := sub<Supergroup | Subgroup, I @ iota0V >;
  __THE_INDEX,__THE_V_INDEX,__THE_W_INDEX := __report(Supergroup, Subgroup, piV,piW);
  
  // PENDING: add (L+R)^# 
  
  // Add exp(L) where Der(T)=L+N a Levi decomposition.------------------------------------
  try
	  vprint Autotopism, 1 : "Adding exponential of derivations by Brooksbank-Maglione-Wilson.";
//  	Subgroup := ExponentiateDerivations(T);
    Subgroup := IsometryGroup(T); // No more ExponentiateDerivations. I Put this in as filler. -Josh
  catch e
  	vprint Autotopism, 1 : "Lie algebra methods not fully supported for this tensor";//, e;
  end try;
	__THE_INDEX,__THE_V_INDEX,__THE_W_INDEX := __report(Supergroup, Subgroup, piV,piW);

// NOW LOWER THE SUPER GROUP--------------------------------------------------------------
  	if UseGraph and Log(2,__THE_W_INDEX) gt (2*(e-2)) then
		vprint Autotopism, 1 : "Entering graph cut down....";
		// PENDING: we should very much like to pass GW to CharSubs here so we don't throw
		// out what we have already found.
		//	subs, inv, GW2 := CharacteristicSubgroups(G: FullGraph:=FullGraph);
		GV := Supergroup @ piV;
		GW := Supergroup @ piW;
if NEW then 
                W := Codomain (T);
                GW := LabelledProjectiveSpace (T, W, point_label, line_label: OVERGROUP := GW);
		Supergroup := sub<GL(d+e,K) | [x@iotaW : x in Generators(GW)] cat [x@iotaV: x in Generators(GV)]>;
else 
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
  // EOB -- initiate search for lifting 
   Supergroup, Subgroup, t := __SearchCosetsW(T, Supergroup,Subgroup,piV, piW, __THE_W_INDEX, MAX);
   vprint Autotopism, 1 : "Total time ", t;

  /* if __THE_W_INDEX lt MAX then
	  Supergroup, Subgroup, t := __SearchCosetsW(T, Supergroup,Subgroup,piV, piW, __THE_W_INDEX, MAX);
	  vprint Autotopism, 1 : "Total time ", t;
	else
		vprint Autotopism, 1 : "Aborting, index too large.";
    end if;
   */
 

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

/* ----------------------------------------------------------------------------- */
/* --- James, I'm putting these additional functions here for the time being --- */
/* ----------------------------------------------------------------------------- */

// JAMES SAYS PUT in eMAG --- BUT IN SEPARATE FOLDERS & FILES, e.g. "test", "lift", etc


/* ---------------------------------------------------------------- */
// this is a temporary intrinsic for what will become an action (exponent)
intrinsic IsotopicImage (T::TenSpcElt, L::Tup) -> TenSpcElt
  {Computes the image of a tensor under the action of a triple of matrices.}
  
  require (#L eq 3) and forall { i : i in [1..3] | Type (L[i]) eq GrpMatElt } :
     "Argument 3 must be a triple of matrix group elements.";
  
  D := Domain (T);
  C := Codomain (T);
  
  require (#D eq 2) : 
     "Argument 1 must be a bimap.";
     
  c := Dimension (D[1]);
  d := Dimension (D[2]);
  e := Dimension (C);
        
  require [ Degree (Parent (L[i])) : i in [1,2,3] ] eq [c,d,e] :
     "Degrees of operators are incompatible with domain and codomain of bimaps.";
  
  f := L[1];
  g := L[2];
  hinv := L[3];
  h := hinv^-1;
  S := SystemOfForms (T);
  Sfg := [ f * S[i] * Transpose (g) : i in [1..#S] ];
  Sfgh := [ &+[ h[i][j] * Sfg[i] : i in [1..#Sfg] ] : j in [1..Ncols (h)] ];
  Tfgh := Tensor (Sfgh, 2, 1);

return Tfgh;
  
end intrinsic;


          /* ----- verification functions ----- */
          

intrinsic IsBalancedBimap (T::TenSpcElt) -> BoolElt
  {Decides if the given tensor is a balanced bimap.}
  D := Domain (T);
return (#D eq 2) and (Dimension (D[1]) eq Dimension (D[2]));
end intrinsic;


intrinsic IsIsotopism (T1::TenSpcElt, T2::TenSpcElt, L::Tup) -> BoolElt

  {Decides if the given triple of matrices is an isotopism between given tensors.}
  
  require (#L eq 3) and forall { i : i in [1..3] | Type (L[i]) eq GrpMatElt } :
     "Argument 3 must be a triple of matrix group elements.";
  
  D1 := Domain (T1);
  D2 := Domain (T2);
  
  require (#D1 eq 2) and (#D2 eq 2) : 
     "Arguments 1 and 2 must be bimaps.";
     
  c := Dimension (D1[1]);
  d := Dimension (D1[2]);

  require (c eq Dimension (D2[1])) and (d eq Dimension (D2[2])) :
     "Arguments 1 and 2 must have domains of equal dimension.";
  
  C1 := Codomain (T1);
  C2 := Codomain (T2);
  e := Dimension (C1);
  
  require (e eq Dimension (C2)) :
     "Arguments 1 and 2 must have codomains of equal dimension";
       
  require [ Degree (Parent (L[i])) : i in [1,2,3] ] eq [c,d,e] :
     "Degrees of operators are incompatible with domain and codomain of bimaps.";
  
  f := L[1];
  g := L[2];
  h := L[3];
  S1 := SystemOfForms (T1);
  S1g := [ f * S1[i] * Transpose (g) : i in [1..#S1] ];
  S2 := SystemOfForms (T2);
  S2h := [ &+[ h[i][j] * S2[i] : i in [1..#S2] ] : j in [1..Ncols (h)] ];
  
return S1g eq S2h;

end intrinsic;


intrinsic IsIsometry (T1::TenSpcElt, T2::TenSpcElt, g::GrpMatElt) -> BoolElt

  {Decides if the given matrix is an isometry between given tensors.}
  
  require IsBalancedBimap (T1) : 
		"First argument is not a balanced bimap.";
		
  require IsBalancedBimap (T2) : 
		"Second argument is not a balanced bimap.";
		
  k := BaseRing (T1);
  e := Dimension (Codomain (T1));
		
return IsIsotopism (T1, T2, < g , g , Identity (GL (e, k)) >);

end intrinsic;


intrinsic IsPseudoIsometry (T1::TenSpcElt, T2::TenSpcElt, L::Tup) 
  -> BoolElt

  {Decides if the given pair of matrices is a pseudo-isometry between given tensors.}
  
  require (#L eq 2) and forall { i : i in [1,2] | Type (L[i]) eq GrpMatElt } :
     "Argument 3 must be a pair of matrix group elements.";
  
  require IsBalancedBimap (T1) : 
		"First argument is not a balanced bimap.";
		
  require IsBalancedBimap (T2) : 
		"Second argument is not a balanced bimap.";
		
return IsIsotopism (T1, T2, < L[1] , L[1] , L[2] >);
  
end intrinsic;



intrinsic IsPrincipalIsotopism (T1::TenSpcElt, T2::TenSpcElt, L::Tup) 
    -> BoolElt

  {Decides if the given pair of matrices is a principal isotopism between given tensors.}
  
  require (#L eq 2) and forall { i : i in [1,2] | Type (L[i]) eq GrpMatElt } :
     "Argument 3 must be a pair of matrix group elements.";
		
  k := BaseRing (T1);
  e := Dimension (Codomain (T1));
  
return IsIsotopism (T1, T2, < L[1] , L[2] , Identity (GL (e, k)) >);
   
end intrinsic;



             /* ----- induce functions ----- */
          
          
intrinsic InduceIsotopism (T1::TenSpcElt, T2::TenSpcElt, L::Tup) 
    -> BoolElt, GrpMatElt
    
  {Decides if the given pair is the inner part of an isotopism between given
   tensors and, if so, finds the corresponding outer part.}
	
  require (#L eq 2) and forall { i : i in [1,2] | Type (L[i]) eq GrpMatElt } :
     "Argument 3 must be a pair of matrix group elements.";	
     
  D1 := Domain (T1);
  D2 := Domain (T2);
  
  require (#D1 eq 2) and (#D2 eq 2) : 
     "Arguments 1 and 2 must be bimaps.";
     
  c := Dimension (D1[1]);
  d := Dimension (D1[2]);

  require (c eq Dimension (D2[1])) and (d eq Dimension (D2[2])) :
     "Arguments 1 and 2 must have domains of equal dimension.";
  
  C1 := Codomain (T1);
  C2 := Codomain (T2);
  e := Dimension (C1);
  
  require (e eq Dimension (C2)) :
     "Arguments 1 and 2 must have codomains of equal dimension";
       
  require [ Degree (Parent (L[i])) : i in [1,2] ] eq [c,d] :
     "Degrees of operators are incompatible with domains of bimaps.";
  
  f := L[1];
  g := L[2];

  S1 := SystemOfForms (T1);
  S2 := SystemOfForms (T2);
  assert (#S1 eq e) and (#S2 eq e);
  
  k := BaseRing (T1);
  MS := KMatrixSpace (k, c, d);
  
  U1 := KMatrixSpaceWithBasis ([ MS!(f * S1[i] * Transpose (g)) : i in [1..e] ]);
  U2 := KMatrixSpaceWithBasis ([ MS!(S2[i]) : i in [1..e] ]);
  if U1 ne U2 then 
    return false, _;
  end if;
     
  mat := Matrix ([ Coordinates (U2, U1.i) : i in [1..e] ]);
  h := GL (e, k)!Transpose (mat);
  assert IsIsotopism (T1, T2, < f, g, h >);

return true, h;
   
end intrinsic;
          


intrinsic InducePseudoIsometry (T1::TenSpcElt, T2::TenSpcElt, g::GrpMatElt) 
  -> BoolElt, GrpMat

  {Decides if the given matrix is the inner part of a pseudo-isometry 
   between given tensors and, if so, finds the corresponding outer part.}
  
  require IsBalancedBimap (T1) : 
		"First argument is not a balanced bimap.";
		
  require IsBalancedBimap (T2) : 
		"Second argument is not a balanced bimap.";
		
return InduceIsotopism (T1, T2, < g, g >);

end intrinsic;



       /* --------------- test functions -------------- */


intrinsic IsIsometric (T1::TenSpcElt, T2::TenSpcElt) -> BoolElt, GrpMatElt
  {Decides if given tensors are isometric.}

  require IsHermitianBimap (T1) : 
		"First argument is not an Hermitian bimap.";
  require IsHermitianBimap (T2) : 
		"Second argument is not an Hermitian bimap.";
		
  f01, g01, T01 := __nondegenerate_tensor (T1); // EXISTS IN TENSOR PACKAGE
  f02, g02, T02 := __nondegenerate_tensor (T2); // USE THAT INSTEAD
  assert g01 eq f01;
  assert g02 eq f02;
  
  if Degree (Parent (f01)) ne Degree (Parent (f02)) then
      return false, _;
  end if;
  
  // now T01 and T02 are nondegenerate tensors
  isit, g0 := __IsIsometric_ND (T01, T02); 
  if not isit then
      return false, _;
  end if;
  
  e := Degree (Parent (f01)) - Degree (Parent (g0));
  if e gt 0 then
      g0 := DiagonalJoin (g0, Identity (GL (e, BaseRing (T1))));
      g0 := GL (Degree (Parent (f01)), BaseRing (T1))!g0;
  end if;
  
  g := f02^-1 * g0 * f01;
  assert IsIsometry (T1, T2, g);
		
return true, g;
		
end intrinsic;


intrinsic IsPrincipallyIsotopic (T1::TenSpcElt, T2::TenSpcElt) 
   -> BoolElt, GrpMatElt, GrpMatElt

  {Decides if there is a principal isotopism between given tensors and, 
   if there is, finds one.}
   
  D1 := Domain (T1);
  c := Dimension (D1[1]);
  d := Dimension (D1[2]);
  e := Dimension (Codomain (T1));
   
  S1 := SystemOfForms (T1);
  S2 := SystemOfForms (T2);
   
  space := Adj2 (S1, S2);  // MAKE INTRINSIC ... CHECK WITH JOSH
  
  if Dimension (space) eq 0 then return false, _, _; end if;

  //  TBD: This part can surely be made deterministic, a la Brooksbank-Luks
  X, Y := __vector_to_matrix(space.1, c, d);
  NU := Nullspace (X);
  NV := Nullspace (Y);
  for i in [2..Ngens (space)] do
      X, Y := __vector_to_matrix(space.i, c, d);
      NU meet:= Nullspace (X);
      NV meet:= Nullspace (Y);
	  if (Dimension (NU) eq 0) and (Dimension (NV) eq 0) then
	  	break;
	  end if;
  end for;
  if (Dimension (NU) gt 0) or (Dimension (NV) gt 0) then 
	  return false, _, _;
  end if;
	
  LIMIT := 20 * Dimension (space);
  i := 0;
  found := false;
  while (i lt LIMIT) and (not found) do
		i +:= 1;
		X, Y := __vector_to_matrix(Random (space), c, d);
		if __SANITY_CHECK then
	  	   assert forall { i : i in [1..e] | X * S1[i] eq S2[i] * Transpose (Y) };
		end if;
		if (Rank (X) eq c) and (Rank (Y) eq d) then
	  	   found := true;
		end if;
  end while;
  if (not found) then
		// This is Monte Carlo!	 Will need to change.
		return false, _, _;
  end if;
  
  f := GL (c, BaseRing (space))!X;
  ginv := GL (d, BaseRing (space))!Y;
  g := ginv^-1;
  assert IsPrincipalIsotopism (T1, T2, < f, g >);

return true, f, g;
   
end intrinsic;



     /* ---------------- lift functions ------------------ */


intrinsic LiftPseudoIsometry (T1::TenSpcElt, T2::TenSpcElt, h::GrpMatElt) 
   -> BoolElt, GrpMatElt

  {Decides if the given matrix is the outer part of a pseudo-isometry between 
   given tensors and, if so, finds a suitable lift.}
  
  require IsBalancedBimap (T1) : 
		"First argument is not a balanced bimap.";
		
  require IsBalancedBimap (T2) : 
		"Second argument is not a balanced bimap.";
        
  require Degree (Parent (h)) eq Dimension (Codomain (T2)) :
        "Argument 3 has incompatible degree with tensor codomain.";
  
  S2 := SystemOfForms (T2);
  S2h := [ &+[ h[i][j] * S2[i] : i in [1..#S2] ] : j in [1..Ncols (h)] ];
  T2h := Tensor (S2h, 2, 1);

return IsIsometric (T1, T2h);

end intrinsic;


intrinsic LiftIsotopism (T1::TenSpcElt, T2::TenSpcElt, h::Mtrx) 
   -> BoolElt, GrpMatElt, GrpMatElt

  {Decides if the given matrix is the outer part of an isotopism between 
   given tensors and, if so, finds a suitable lift.}
   
  S2 := SystemOfForms (T2);
  S2h := [ &+[ h[i][j] * S2[i] : i in [1..#S2] ] : j in [1..Ncols (h)] ];
  T2h := Tensor (S2h, 2, 1);

return IsPrincipallyIsotopic (T1, T2h);

end intrinsic;



      /* ------------- group constructors ----------------- */
      
intrinsic IsometryGroup (T::TenSpcElt) -> GrpMat

  {Compute the group of isometries of the given tensor.}
  
  // need some requirements here
  
return IsometryGroup (SystemOfForms (T));
  
end intrinsic;


intrinsic PrincipalIsotopismGroup (T::TenSpcElt) -> GrpMat

  {Compute the group of principal isotopisms of the given tensor.}
  
  c := Dimension (Domain (T)[1]);
  d := Dimension (Domain (T)[2]);
  e := Dimension (Codomain (T));
  S := SystemOfForms (T);
  
  space := Adj2 (S, S);
  
  gens := [ ];
  for i in [1..Ngens (space)] do
      X, Y := __vector_to_matrix (space.i, c, d);
      if __SANITY_CHECK then
	  	   assert forall { i : i in [1..#S] | X * S[i] eq S[i] * Transpose (Y) };
	  end if;
      Append (~gens, DiagonalJoin (X, Transpose (Y)));
  end for;
  
  A := sub < MatrixAlgebra (BaseRing (T), c + d) | gens >;
  isit, U := UnitGroup (A);
  assert isit;
  gens := [ ];
  for i in [1..Ngens (U)] do
      f := GL (c, BaseRing (T))!ExtractBlock (U.i, 1, 1, c, c);
      ginv := GL (d, BaseRing (T))!ExtractBlock (U.i, c+1, c+1, d, d);
      g := Transpose (ginv^-1);
      assert IsPrincipalIsotopism (T, T, <f,g>);
      Append (~gens, DiagonalJoin (<f, g, Identity (GL (e, BaseRing (T)))>));
  end for;
  
  PRIN := sub < GL (c + d + e, BaseRing (T)) | gens >;

  // Added by JM to enable 'Induce' on PRIN
  PRIN`DerivedFrom := <T, [1..3]>;
  
return PRIN;
  
end intrinsic;



// very basic version: needs various enhancements a la pseudo-isometry
// group construction above
intrinsic AutotopismGroup (T::TenSpcElt) -> GrpMat

  {Compute the group of autotopisms of the given tensor.}
  
  c := Dimension (Domain (T)[1]);
  d := Dimension (Domain (T)[2]);
  e := Dimension (Codomain (T));
  k := BaseRing (T);
  
  OVER := GL (e, k);   // this can be refined on input
  UNDER := sub < GL (e, k) | Identity (GL (e, k)) >;   // possibly this can too
  INDEX := LMGOrder (OVER) div LMGOrder (UNDER);
"INDEX =", INDEX, 
"   (", Ceiling (Log (2, INDEX)),"bits )";
"LIMIT =", __EXHAUSTIVE_SEARCH_LIMIT;

  done := false;
  gens := [ ];
  
  // find generators for the principal isotopism group.
  PRIN := PrincipalIsotopismGroup (T);
"order of principal isotopism group of T:", LMGOrder (PRIN), 
"   (", Ceiling (Log (2, LMGOrder (PRIN))),"bits )";
  
  while (not done) do
  
      if (INDEX le __EXHAUSTIVE_SEARCH_LIMIT) then   // proceed exhaustively
   
//"computing transversal for INDEX =", INDEX, "   ( |OVER| =", #OVER, "   |UNDER| =", #UNDER,")";          
          tran, f := Transversal (OVER, UNDER);
//"done";
          assert tran[1] eq Identity (OVER);
          i := 1;
          stop := false;
          while (i lt #tran) and (not stop) do
              i +:= 1;
              // try to lift tran[i]
              h := tran[i];
              isit, f, g := LiftIsotopism (T, T, h);
              if isit then
                  assert IsIsotopism (T, T, <f, g, h>);
                  stop := true;
              end if;
          end while;
          
          if stop then
              Append (~gens, DiagonalJoin (<f, g, h>));
              UNDER := sub < Generic (UNDER) | [ UNDER.i : i in [1..Ngens (UNDER)] ]
                                               cat [ h ] >;
              INDEX := LMGOrder (OVER) div LMGOrder (UNDER);
          else
              assert i eq #tran;
              done := true;
          end if;
          
      else   // try random process
"searching at random for group elements that lift to isotopisms";       
          i := 1;
          stop := false;
          while (i lt __EXHAUSTIVE_SEARCH_LIMIT) and (not stop) do
              i +:= 1;
if (i mod 10^4 eq 2) then "   i =", i; end if;
              h := Random (OVER);
              if not (h in UNDER) then
                  isit, f, g := LiftIsotopism (T, T, h);
                  if isit then
                  "success!";
                      assert IsIsotopism (T, T, <f, g, h>);
                      stop := true;
                  end if;
              end if; 
          end while;
          
          if stop then
              Append (~gens, DiagonalJoin (<f, g, h>));
              UNDER := sub < Generic (UNDER) | [ UNDER.i : i in [1..Ngens (UNDER)] ]
                                               cat [ h ] >;
              INDEX := LMGOrder (OVER) div LMGOrder (UNDER);
          else
              assert i eq __EXHAUSTIVE_SEARCH_LIMIT;
              done := true;
          end if;
  
      end if;
      
  end while;
  
  OUTER := UNDER;   // if we took deterministic route this will be accurate;
                    // if we searched at random, OUTER could still be a subgroup
                    // of the projection of the target gp of isotopisms on W.
  
  gens cat:= [ PRIN.i : i in [1..Ngens (PRIN)] ];  
  H := sub < GL (c + d + e, k) | gens >;

  //sanity checks
  for i in [1..Ngens (H)] do
      assert IsIsotopism (T, T, <GL (c, k)!ExtractBlock (H.i, 1, 1, c, c), 
                           GL (d, k)!ExtractBlock (H.i, c+1, c+1, d, d),
                           GL (e, k)!ExtractBlock (H.i, c+d+1, c+d+1, e, e)>);
  end for;
  
  assert LMGOrder (PRIN) * LMGOrder (OUTER) eq LMGOrder (H);
  
return H;

end intrinsic;
   


