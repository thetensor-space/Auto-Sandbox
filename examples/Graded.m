
RandomGraded := function(K,dims)
	ddims := func<i | (i le #dims) select dims[i] else 0 >;
	rand := func< i,j | 
			(i eq j ) select 
				Random(AlternatingSpace(KTensorSpace(K,[dims[i],dims[i],ddims(i+i)]))) 
			else
				Random(KTensorSpace(K,[dims[i],dims[j],ddims(i+j)])) >;
	return [* [* rand(i,j) : j in [i..#dims] *] : i in [1..#dims] *];
end function;

