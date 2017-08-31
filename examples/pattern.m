
Panel := function(K,d,e)
	MS := KMatrixSpace(K,d,e);
	L := [MS|];
	for i in [1..(e-1)] do
		X := MS!0;
		X[i][i+1] := K!1;
		X[d-e+i+1][i] := -(K!1);
		Append(~L,X);
	end for;
	return Tensor(L,2,1);
end function;

BabyGiant := function(p,d1,d2)
	d:=d1+2*d2;
	G := GL(d,p);
	gens := [G|];
	for i in [1..(d1-1)] do
		X := IdentityMatrix(GF(p),d);
		X[i][i+1] := GF(p)!1;
		Append(~gens, X);
	end for;

	for x in [1..d2] do
		X := IdentityMatrix(GF(p),d);
		X[d1][d1+x] := GF(p)!1;
		Append(~gens,X);
		for y in [1..d2] do 
			X := IdentityMatrix(GF(p),d);
			X[d1+x][d1+d2+y] := GF(p)!1;
			Append(~gens,X);
		end for;
	end for;
	
	return sub<G|gens>;
end function;

RandomSubBabyGiant := function(p,d1,d2 : frac:=0.5)
	U := BabyGiant(p,d1,d2);
	x := Round(frac*(d1+3*d2^2)+1);
	gens := [U| Random(U) : i in [1..x]];
	return sub<U|gens>;
end function;

ProcessBG := function(U)
	U := PCPresentation(UnipotentMatrixGroup(U));
	fo := FactoredOrder(U)[1];
	print "|U|=", fo;
	c := #pCentralSeries(U,fo[1]);
	T := pCentralTensor(U,1,1);
	K := BaseRing(T);
	d := (Dimension(Domain(T)[2]));
	print "Naive bits of work = ", d^2;
	
	minwork := d^2;
	maxwork := d^2;
	minindex := 1;
	maxindex := 1;
	for i in [1..(c-2)] do
		print "-----------", i;
		T := pCentralTensor(U,1,i);
		w := Dimension(Codomain(T));
		print "Bits of work autotopism stage: ", w^2;
		M := Nucleus(T,2,1);
		m := Dimension(M);
//		print "Dim nucleus=", m;
		L := Nucleus(T,2,0);
		d2 := Dimension(Domain(T)[2]);
		d1 := Dimension(Domain(T)[1]);
		LW := sub<MatrixAlgebra(K,w)| [ExtractBlock(X,d2+1,d2+1,w,w) : X in Basis(L)]>;
		l := Dimension(LW);
		R := Nucleus(T,1,0);
		d1 := Dimension(Domain(T)[1]);
		RW := sub<MatrixAlgebra(K,w)| [ExtractBlock(X,d1+1,d1+1,w,w) : X in Basis(L)]>;
		r := Dimension(RW);
		print "Min bits of work:  ", l + r + m;
		print "Max bits of work:  ", w^2 + m;
		if (w^2+m) lt maxwork then maxwork := w^2+m; maxindex := i; end if;
		if Maximum(w^2,(l+m+r)) lt minwork then minwork := Maximum(w^2,l+m+r); minindex := i; end if;
		print "";
	end for;
	print "Best index: ", maxindex, "\t Max bits of work: (", maxwork, "/", d^2, ":", d, ":", fo[2], ")";
	print "Best index: ", minindex, "\t Min bits of work: (", minwork, "/", d^2, ":", d, ":", fo[2],  ")";
	return U;	
end function;
