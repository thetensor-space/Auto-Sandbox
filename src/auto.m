
import "GlobalVars.m" : __SANITY_CHECK;

/*
intrinsic ProduceFilter (G::GrpPC: S := [], CharSpacesFunc:=false) -> [], [], []
{produce filter}
   F:= pCentralFilter(G);
   Q:=Refine (F);
   I:=Image (Q);
   if #S eq 0 and not ISA(Type(CharSpacesFunc),BoolElt) then 
      S:=CharSpacesFunc (G);
   end if;
   for i in [1..#S] do 
      H := S[i];
      if not (H in I) then 
        vprint Autotopism, 2 : "\tFilter process %o", i;
        gens := [G!H.j: j in [1..NPCgens (H)]]; 
        Q := ConstructFilter (Q, gens);
        I := Image (Q);
      end if; 
   end for;
   
   T := I cat S;
   T := Set (T);
   T := [x : x in T];
   return T, I, S;
end intrinsic;
*/
__ReduceActionOnVW := function (G)
	vprint Autotopism, 1 : 
		"\tSearching for characteristic subgroups by Maglione-Wilson filters.";
   A := ProduceFilter(G);
  vprintf Autotopism, 1 :
    "\t\tFound %o new characteristic subgroups.", #A-2; // don't count G and 1.


   F := FrattiniSubgroup (G);
   T, maps :=pCentralTensor (G);
   f := maps[1];
   g := maps[2];
   h := maps[3];
   W :=Codomain (T);
   I := [i: i in [1..#A] | A[i] subset F];
   S := [sub<W | [A[i].j @ h: j in [1..NPCgens (A[i])]]>: i in I];
   GW := StabiliserOfSpaces (S);
 
   V := Domain(T)[1];
   I := [i: i in [1..#A] | F subset A[i]];
   S := [sub<V | [A[i].j @ f: j in [1..NPCgens (A[i])]]>: i in I];
   GV := StabiliserOfSpaces (S);

	B := MyCharSpaces (G: Known := A);
   I := [i: i in [1..#B] | F subset B[i] ];
   S2 := [sub<V | [B[i].j @ f: j in [1..NPCgens (B[i])]]>: i in I];
   GV2 := StabiliserOfSpaces (S2);
assert GV2 subset GV;

	vprint Autotopism, 1 : 
		"\tSearching for characteristic subgroups by Eick--Leedham-Green--O'Brien.";



	// MY CHAR SPACE IS NOT RIGHT!!!
//   B, C := MyCharSpaces (G: Known := A);
//   C := {x[1] : x in C | x[2] eq 1};
//   C := [x  : x in C]; 
//   GV := StabiliserOfSpaces (C);
//	GV := GL(4,3); /// HACK
//"test", LMGOrder(GV) eq LMGOrder(GL(4,3));
  return GW, GV2;
end function;

__report := function( GV, GW)
	__THE_INDEX_V := LMGOrder(GV);
	__THE_INDEX_W := LMGOrder(GW);
	bits := Minimum([Ceiling(Log(2,__THE_INDEX_V)), Ceiling(Log(2,__THE_INDEX_W))]);
  	vprint Autotopism, 1 : 
	  	"BITS OF WORK:............................................", bits;
  	
  	return bits;
end function;

intrinsic AutomorphismGroupByInvariants(
	G::Grp : 
	UseGraph := true,
	UseFilters := true
) -> Grp
{Compute the automorphism group using structural invaraiants.}

	if IsAbelian(G) then 
		vprint Autotopism, 1 :
			"Group is abelian, using default magma automorphism function.";
		return AutomorphismGroup(G); 
	end if;

	I := G;	
	p := FactoredOrder (G)[1][1];
	G, gamma := pQuotient (I, p, pClass (G));
	
	T := pCentralTensor(G,1,1);
	d := Dimension(Domain(T)[1]);
	e := Dimension(Codomain(T));
	p := Characteristic(BaseRing(T));

	if e lt 3 then 
			vprint Autotopism, 1 :
			"Group is small genus, using small genus package.";
			return TGPseudoIsometryGroup(T); 
	end if;

 	GV := GL(d,p);
 	GW := GL(e,p);

	if UseFilters then
		vprint Autotopism, 1 : "Reducing action ....";
		GW, GV := __ReduceActionOnVW(G);
	end if;
	iotaV := hom<GL(d,p)->GL(d+e,p)| x:->DiagonalJoin(x,IdentityMatrix(GF(p),e))>;
	iotaW := hom<GL(e,p)->GL(d+e,p)| x:->DiagonalJoin(IdentityMatrix(GF(p),d),x)>;
	U := sub<GL(d+e,p) | [x@iotaW : x in Generators(GW)] cat [x@iotaV: x in Generators(GV)]>;
	WORK := __report( GV, GW );

	vprint Autotopism, 1 : "Entering pseudo-isometry group....";
	U,L := PseudoIsometryGroup(T : Supergroup := U, MAX := 2^30 );

	return U,L;
end intrinsic;


intrinsic AutomorphismGroupAsIsotopisms(A::Grp, G::Grp, i::RngIntElt, j::RngIntElt) -> Grp, Map
{Homomorphism to the action as isotopisms on the associated tensor.}
	
	T := pCentralTensor(G,i,j);
	fs := T`Coerce;
	fU := fs[1];
	fV := fs[2];
	fW := fs[3];
	U := Domain(T)[1];
	V := Domain(T)[2];
	W := Codomain(T);
	dU := Dimension(U);
	dV := Dimension(V);
	dW := Dimension(W);
	
	p := Characteristic(BaseRing(T));
	
	toU := func<a|Matrix(GF(p),dU,dU,[Eltseq( ((U.i @@ fU )@a )@ fU): i in [1..Ngens(U)]])>;
	toV := func<a|Matrix(GF(p),dV,dV,[Eltseq( ((V.i @@ fV )@a )@ fV): i in [1..Ngens(V)]])>;
	toW := func<a|Matrix(GF(p),dW,dW,[Eltseq( ((W.i @@ fW )@a )@ fW): i in [1..Ngens(W)]])>;
	if not (i eq j) then
		imUVW := sub<GL(dU+dV+dW,p)| [DiagonalJoin(<toU(a),toV(a),toW(a)>): a in Generators(A)]>;
		f := hom<A->imUVW | x:->DiagonalJoin(<toU(x),toV(x),toW(x)>)>;
		return imUVW, f;
	else
		imUW := sub<GL(dU+dW,p)| [DiagonalJoin(toU(a),toW(a)): a in Generators(A)]>;
		f := hom<A->imUW | x:->DiagonalJoin(toU(x),toW(x))>;
		return imUW, f;
	end if;
end intrinsic;

