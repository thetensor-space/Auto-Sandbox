BrahanaTest := function(p)
	B := BrahanaList(p);
	orders := [0 : i in [1..#B]];
	times := [];
	for i in [1..#B] do
		print "";
		print "i=", i, "====================================================================";
		print "";
		D := DualGroup(B[i]);
		t := Cputime();
		U,L := AutomorphismGroupByInvariants(D);
		Append( times, Cputime(t) );
		if ISA(Type(L),GrpMat) then assert LMGOrder(U) eq LMGOrder(L); end if;
		orders[i] := LMGOrder(U);
		print i, " took time ", times[i], " and gave order ", orders[i];
		print "";
	end for;
	return orders, times;
end function;

