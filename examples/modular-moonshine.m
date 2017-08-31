p:=23; a:=-12;
four := function(p,a)
	A1 := Matrix(GF(p), 4,4, [[1,a,a,a],\
													  [a,0,0,0],\
													  [a,0,0,0],\
													  [a,0,0,0]]);
	A2 := Matrix(GF(p), 4,4, [[0,a,0,0],\
													  [a,1,a,a],\
													  [0,a,0,0],\
													  [0,a,0,0]]);
	A3 := Matrix(GF(p), 4,4, [[0,0,a,0],\
													  [0,0,a,0],\
													  [a,a,1,a],\
													  [0,0,a,0]]);
	A4 := Matrix(GF(p), 4,4, [[0,0,0,a],\
													  [0,0,0,a],\
													  [0,0,0,a],\
													  [a,a,a,1]]);
			return Tensor([A1,A2,A3,A4],2,1);
end function;

p:=23; a:=-(p+1)/2;
three:=function(p,a)
	B:=[Matrix(GF(p), 3,3, [[1,a,a],\
											  [a,0,0],\
											  [a,0,0]]),
		Matrix(GF(p), 3,3, [[0,a,0],\
		 									  [a,1,a],\
										 	  [0,a,0]]),
		Matrix(GF(p), 3,3, [[0,0,a],\
												[0,0,a],\
												[a,a,1]])];
	return Tensor(B,2,1);
end function;
D:=DerivationAlgebra(t);
Dimension(D);
