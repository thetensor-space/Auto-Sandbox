
// assumes you are running from within the same folder as this file.
load "../examples/brahana/programs.m";
load "../examples/brahana/present.m";
load "../examples/dual.m";


BrahanaTest := function(p)
	B := BrahanaList(p);
	orders := [0 : i in [1..#B]];
	times := [* *];
	failed := 0;
	for i in [1..#B] do
		print "";
		print "i=", i, "====================================================================";
		print "";
		D := DualGroup(B[i]);
		t := Cputime();
	try
		U,L := AutomorphismGroupByInvariants(D);
		s := Cputime(t);
		Append(~times, s  );
		if ISA(Type(L),GrpMat) and not( LMGOrder(U) eq LMGOrder(L) ) then
			print "Gap in order", LMGOrder(U), ":", LMGOrder(L);
	 	end if;
		orders[i] := LMGOrder(U);
		print i, " took time ", times[i], " and gave order ", orders[i];
		print "";
	catch e
		print i, " FAILED ", e;		
		Append(~times, -1);
		orders[i] := -1;
		failed +:= 1;
	end try;
	end for;
	print "Total failures: ", failed;
	return orders, times;
end function;

