
__pete_forms := function( bimap )
	K := BaseRing(bimap);
	d := Dimension( bimap`Domain[1]);
	forms := SystemOfForms( bimap);
	MA := MatrixAlgebra( K, d );
	return [ MA!x : x in forms];
end function;


//AttachSpec( "../MultilinearAlgebra-current/Multi.spec" );
//AttachSpec( "../Filters-current/Filters.spec" );

// EOB -- restored these to work with tests.m
MyHeisenbergGroup := function( p, e ) 
	k := GF(p^e);
        G := GL(3,k);
	M, U, f := LMGFittingSubgroup( ClassicalSylow( G, Characteristic(k)) );
	return U;
end function;

//RandomQuoByGenus := function( H, genus )
//	HH := CommutatorSubgroup( H, H);
//	d := FactoredOrder( HH)[1][2];
//	N := sub< H | [ Random(HH) : i in [1..(d-genus)] ] >;
//	return H/N;
//end function;

RandomQuoByGenus := function( H, genus )
	HH := CommutatorSubgroup( H, H);
	d := FactoredOrder( HH)[1][2];
	rels := [];
	while #rels lt (d-genus) do
		x := Random(HH);
		if not( x eq x^0) then
			Append(~rels, x );
		end if;
	end while;
	N := sub< H | rels >;
	return H/N;
end function;


__find_albert_params := function( p, e )
	// 
	K := GF(p^e);
	x := PrimitiveElement(K);
	params := [];
	for s in [1..(e-1)] do
		if (Order( x^(p^GCD(s,e)-1)) mod 2) eq 0 then continue; end if;
		for t in [1..(e-1)] do
			if (Order( x^(p^GCD(t,e)-1)) mod 2) eq 1 then 
				Append(~params, [s,t] );
			end if;
		end for;
	end for;
	return params;
end function;

RandomAlbertSemifield := function( p, e : s := 0, t:= 0, a:= -1 )
	if s*t eq 0 then 
		params := __find_albert_params( p, e);
		if #params eq 0 then 
			print "No albert algebra on GF(", p, "^", e, ")"; 
			return []; 
		else
			param := Random( params );
			s := param[1];
			t := param[2];
		end if;
	end if;
	MS := KMatrixSpace( GF(p), e,e );
	X := CompanionMatrix( RandomIrreduciblePolynomial( GF(p), e ) );
	basis := [ MS!X^i : i in [0..(e-1)] ];
	V := KMatrixSpaceWithBasis( basis );
	forms := [ ZeroMatrix( GF(p), e,e ) : i in [1..e] ];
	// work out X^i*X^j = X^i.X^j-a (X^i)^(p^s) (X^j)^(p^t)
	for i in [0..(e-1)] do
		A := X^i;
		for j in [0..(e-1)] do
			B := X^j;
			C := MS!(A*B - (a)* A^(p^s) * B^(p^t));
			v := Coordinates( V, C );
			for k in [1..e] do
				forms[k][i+1][j+1] := v[k];
			end for;
		end for;
	end for;
	return Tensor( forms, 2,1 );	
end function;


// Same as S:=Singularity( forms, {1}); #(RationalPoints(S)) eq 0;
IsNonsingular:= function( forms )
	K := BaseRing( forms[1] );
	U := KMatrixSpace( K, 1, Nrows(forms[1]));
	V := KMatrixSpace( K, Ncols(forms[1]), 1);
	W := KSpace( K, #forms );
	for u in U do
		if u eq U!0 then continue; end if;
		for v in V do
			if v eq V!0 then continue; end if;
			w := W![ (u*F*v)[1][1] : F in forms ];
			if w eq W!0 then 
				print u;
				print v;
				return false;
			end if;
		end for;
	end for;
	return true;
end function;




TwistedHeisenbergGroup := function( p, e  )
	m := RandomAlbertSemifield( p, e );
	C := Centroid(m);
	while ( Dimension(C) eq e ) do
		m := RandomAlbertSemifield( p, e );
		C := Centroid(m);
	end while;
	return HeisenbergGroup(m);
end function;

Verardi1 := function( )
	K := GF(3);
	MS6 := KMatrixSpace( K, 6,6);
	MS3 := KMatrixSpace( K, 3,3);
	
	T1 := ZeroMatrix( K, 6,6 );
	T11 := MS3![0,1,1,  1,0,0,  0,1,0];
	InsertBlock(~T1, T11, 1,4);
	InsertBlock(~T1, -Transpose(T11), 4,1);

	T2 := ZeroMatrix( K, 6, 6 );
	T12 := MS3![0,1,0,  0,0,1,  1,0,2];
	InsertBlock(~T2, T12, 1,4);
	InsertBlock(~T2, -Transpose(T12), 4,1);
	
	T3 := MS6![\
		0,0,0,1,2,2,\
		0,0,1,1,0,0,\
		0,2,0,0,0,0,\
		2,2,0,0,0,0,\
		1,0,0,0,0,1,\
		1,0,0,0,2,0];
	m := Tensor( [T1,T2,T3], 2,1 );
	print Dimension(DerivationAlgebra(m));
	print Dimension(Centroid(m));
	print Dimension(AdjointAlgebra(m));
	return HeisenbergGroup(m), m;
end function;

