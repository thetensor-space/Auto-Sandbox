
__exp := function(z)
	// Convert to associative product if necessary.
	if ISA(Type(z),AlgMatLieElt) then 
		P := Parent(z);
		MA := MatrixAlgebra(BaseRing(P),Degree(P));
		z := MA!z;
	end if;
	
	u := z^0;
	i := 1;
	v := z;
	while not (v eq 0) do
		u +:= v/Factorial(i);
		i +:=1;
		v *:= z;
	end while;
	return u;
end function;

intrinsic ExponentiateLieAlgebraSS(L::AlgMatLie) -> GrpMat
{Return the connected algebraic group of the semisimple Lie algebra of Chevalley type.}
	// require the L be semisimple for now.
	G := GL(Degree(L),BaseRing(L));
	if Dimension(L) eq 0 then return sub<G|[]>; end if;	
	
	gens := [];
	Factors := DirectSumDecomposition(L);
	for M in Factors do
		vprint Autotopism, 1 : "Computing Chevalley Basis of simple factor by Taylor algorithm.";
		try
			E,F,H := ChevalleyBasis(M);
			gens cat:= [G!__exp(e) : e in E];
			gens cat:= [G!__exp(f) : f in F];
		catch e
			// Ignore, Magma only supports some characteristics.
			vprint Autotopism, 1 : e`Object;
			vprint Autotopism, 1 : "Chevalley basis could not be computed for factor, skipping";
		end try;
	end for;
	
	return sub<G|gens>;
end intrinsic;


intrinsic ExtendByNormalizer(H::GrpMat,U::ModTup) -> GrpMat
{}
	vprint Autotopism, 1 : "Computing normalizer of connected component.";
	N := GLNormaliser(H);
	f,NmodH := LMGCosetAction(N,H);
	vprint Autotopism, 1 : "Searching through ", Order(NmodH), " cosets";
	EI := [<i @@ f, ExteriorSquare(i @@ f)> : i in NmodH ];
	V := VectorSpace(BaseRing(H), Binomial(Degree(H),2));
	W := sub<V|U>;
	Stab := { x[1] : x in EI | W^x[2] eq W };
	return sub<N | Generators(H) join Stab>;
end intrinsic;

OuterCentralAutomorphisms := function(P,U)
	T := pCentralTensor(P,1,1);
print "Computing derivations.";
	D := DerivationAlgebra(T);
	H := ExponentiateLieAlgebraSS(D);
	d := Dimension(Domain(T)[1]);
	F := BaseRing(T);
	hreps := [ExtractBlock(h,1,1,d,d) : h in Generators(H)];
	H1 := sub<GL(d,F) | hreps>;
	G := ExtendByNormalizer(H1,U);
	return G;
end function;
