
import "GlobalVars.m" : __SANITY_CHECK;


intrinsic BreadthScheme(T::TenSpcElt, r::RngIntElt ) -> Sch
{Retrieve the scheme identifying the domain vectors of breadth at most r.}

	K := BaseRing(T);
	d2 := Dimension(Domain(T)[2]);
	d1 := Dimension(Domain(T)[1]);
	d0 := Dimension(Domain(T)[0]);
	
	mats := AsMatrices(T,1,0);
	P := PolynomialRing(K,d2);
	MS := RMatrixSpace(P,d1,d0);

	M := &+[MS | P.i*MS!mats[i] : i in [1..d2]];

    Is := Subsets({1..d1},r); Js := Subsets({1..d0},r);
	polys := [P| Determinant(Matrix(P,r,r,[M[i[1]][i[2]] : i in IJ])) 
        : IJ in CartesianProduct(Is,Js) ];
	
//    polys := [P|];
//    for I in Subsets({1..d1},r) do
//		for J in Subsets({1..d0},r) do
//			S := Matrix(P,r,r,[M[i][j] : i in I, j in J]);
//			Append(~polys,Determinant(S));
//		end for;
//	end for;

	I := ideal<P|polys>;
	S := Scheme(ProjectiveSpace(K,d2-1),Basis(I));
	
	return S;
end intrinsic;

/*
	Property 1: degree(Sch) divides r
	Property
	Property 2: x on Sch => x@T = 0
 */
BreadthPropertyTest := function()
    return _;
end function;

intrinsic KBreadthScheme(K::Fld, T::TenSpcElt, r::RngIntElt ) -> Sch
{The scheme identifying the domain vectors of breadth at most r over extension of degree d.}
	d := Dimension(Domain(T)[1]);
	e := Dimension(Codomain(T));
	Te := Tensor(K,[d,d,e], Eltseq(T));
	return BreadthScheme(Te,r);
end intrinsic;

intrinsic KBreadthSubspace(K::Fld, T::TenSpcElt, r::RngIntElt) -> ModTup
{Decide if a breadth factor of rank r over K form a proper subspace.}

	// Extend tensor.
	
	d := Dimension(Domain(T)[1]);
	e := Dimension(Codomain(T));
	Te := Tensor(K,[d,d,e], Eltseq(T));

	sh := BreadthScheme(Te,r);
	
	vprint Autotopism, 1 : "Computation rational points.  This may take a while. ",
		"Use SetVerbose( ''GrobnerBasis'', 1) to track progress.";
	pts := RationalPoints(sh);
	// In the future one could hack into this and start the span and stop when it gets full.

	V := VectorSpace(K,d);
	return sub<V | [ V!Eltseq(p) : p in pts ] >;
end intrinsic;


BreadthSubspace := function( forms )
	V := KMatrixSpace( BaseRing( forms[1] ), 1, Nrows(forms[1]) );
	count :=[0 : i in [0..#forms] ];
	m := Minimum( Nrows(forms[1]), Ncols(forms[1]) );
	gens := [[] : i in [1..m]];
	for v in V do
		mat := Matrix( [ v*F : F in forms ] );
		br := Rank( mat );
		if (br lt m ) then
			Append(~gens[br+1], v);
		end if;
	end for;
	return [ Dimension( sub<V|X> ) : X in gens ];
end function;

