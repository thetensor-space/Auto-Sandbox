  /*
    -----------------------------------------------------------------
    An implementation based on techniques developed in     
    Groups acting on densors, Brooksbank, Maglione, Wilson (preprint)
    The overarching goals are automorphism group functions and
    isomorphism tests for certain p-groups.
    -----------------------------------------------------------------
  */
 
/* -------------------- subroutines ------------------ */
 
__exp := function (z)
	// Convert to associative product if necessary.
	if ISA (Type(z), AlgMatLieElt) then 
		P := Parent (z);
		MA := MatrixAlgebra (BaseRing (P), Degree (P));
		z := MA!z;
	end if;
	u := z^0;
	i := 1;
	v := z;
	while not (v eq 0) do
		u +:= v / Factorial (i);
		i +:= 1;
		v *:= z;
	end while;
return u;
end function;


__preimage := function (ms, MS, y)
    // WHAT DOES IT DO?
    k := BaseRing (ms);
    c := Coordinates (MS, MS!y);
    coords := [];
    for a in c do
         coords cat:= Eltseq (a, k);
    end for;
return &+[ coords[i] * ms.i : i in [1..Ngens (ms)] ];
end function;


__ReduceToBasis := function (X)
    // X contains a basis of the matrix space it spans
    k := BaseRing (Parent (X[1]));
    m := Nrows (X[1]);
    n := Ncols (X[1]);
    ms := KMatrixSpace (k, m , n);
    U := sub < ms | [ ms!(X[i]) : i in [1..#X] ] >;
    d := Dimension (U);
    if d eq #X then
         return [1..d];
    else
         J := [ Min ({ i : i in [1..#X] | X[i] ne 0 }) ];
         j := J[1];
         W := sub < ms | [ ms!(X[j]) : j in J ] >;
         while Dimension (W) lt d do
              j +:= 1;
              x := ms!(X[j]);
              if not x in W then
                   Append (~J, j);
                   W := sub < ms | [ ms!(X[j]) : j in J ] >;
              end if;
         end while;
         return J;
    end if;
end function;


__CentralAutos := function (p, d, e)
    // constructs generators for the central automorphisms
    gens := [];
    I := IdentityMatrix (GF (p), d + e);
    for i in [1..d] do
         for j in [1..e] do
              A := I;
              A[i][d+j] := 1;
              Append (~gens, A);
         end for;
    end for;
    G := GL (d + e, p);
return [ G!A : A in gens ];
end function;

__GraphAutos := function (type, r)
    // constructs generators for group of permutations of the positive
    // fundamental roots induced by the graph automorphisms of the simple
    // Lie algebra of the given type.
    S := SymmetricGroup (r);
    if type eq "A" then
         return sub < S | S![r + 1 - i : i in [1..r] ] >;
    else
         error "not implemented yet";
    end if;
end function; 


/*
    INPUT:
      (1) A, a k-algebra (e.g. Lie or associative) of matrices.
      (2) S, a set of invertible linear transformations of the 
          underlying k-algebra.
    
    OUTPUT: true if, and only  if, L^S = L
*/
NormalizesMatrixAlgebra := function (A, S)  
     k := BaseRing (A);
     n := Degree (A);
     MS := KMatrixSpace (k, n, n);
     X := KMatrixSpaceWithBasis ([ MS!Matrix (x) : x in Basis (A) ]);    
return forall { s : s in S | 
          forall { i : i in [1..Ngens (X)] |
              s^-1 * X.i * s in X
                 }
              };             
end function;


// Convert GrpAuto of a p-class 2 group to a matrix group.
// Returns the restriction of Aut(G) on W along with Aut(G).
AutoToMat := function (A)
     G := A`Group;
     assert pClass (G) eq 2;
     d := Ngens(G); // number of minimal generators
     ord := Factorization (#G);
     e := ord[1][2]-d;
     p := ord[1][1];
     // basis will be G.1, G.2, ..., G.n.
     Over := GL (d+e, p);
     gens := [];
     for a in Generators (A) do
         M := [ Eltseq (G.i @ a) : i in [1..d+e] ];
         Append (~gens, Over!M);
     end for;
     Aut_Mat := sub< Over | gens >;
     Aut_W := sub< GL (e, p) | [ ExtractBlock (x, d+1, d+1, e, e) : x in gens ] >;
return Aut_W, Aut_Mat;
end function;


// Moved from "exponentiate.m" by PAB on 6/5/2018
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



/* -------------------- intrinsics ------------------ */

// not sure where this should go, but I could not find it in Magma
intrinsic ElementaryMatrix (K::FldFin, m::RngIntElt, n::RngIntElt, 
                  i::RngIntElt, j::RngIntElt) -> ModMatFldElt
  { The (i,j) elementary m x n matrix over the field K }
  Eij := KMatrixSpace (K, m, n)!0;
  Eij[i][j] := 1;
return Eij;
end intrinsic;


intrinsic ExponentiateLieAlgebraSS (L::AlgMatLie) -> GrpMat
{Return the connected algebraic group of the semisimple Lie algebra of Chevalley type.}
	// require the L be semisimple for now.
     G := GL (Degree (L), BaseRing (L));
	 if Dimension (L) eq 0 then 
	     return sub<G|[]>; 
	 end if;		 
   	 gens := [];
	 Factors := DirectSumDecomposition (L);
	 for M in Factors do
		 vprint Autotopism, 1 : "Computing Chevalley Basis of simple factor by Taylor algorithm.";
		 try
			E,F,H := ChevalleyBasis (M);
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

// Josh had this as an intrinsic in "exponentiate.m"
// Transferred here by PAB on 6/5/2018
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


/* 
    INPUT:
      (1) L, an irreducible representation of a simple Lie algebra.
      (2) E, the part of a Chevalley basis corresponding to the
          positive fundamental roots of L. In particular, the 
          length of E is the Lie rank r of L.
      (3) F, the opposite fundamental roots.
      
    OUTPUT:
      (1) a transition matrix to a crystal basis.
      (2) a crystal basis data structure, which is a list whose
          members are tuples with the following information:
           * a vector v
           * a label for v: a word in [ F[1] ... F[r] ]
           * labelled pointers to v from previous basis elements
*/ 
intrinsic CrystalBasis (L::AlgMatLie, E::SeqEnum, F::SeqEnum) -> 
              AlgMatElt, SeqEnum
  {Finds a transition matrix to a highest weight basis for L relative to E and F.}
     
     k := BaseRing (L);
     n := Degree (L);
     r := #E;
     
     // find unique highest weight vector corresponding to E
     HW := &meet [ Nullspace (x) : x in E ];
     assert Dimension (HW) eq 1;
     lambda := HW.1;
     
     // spin up the basis using elements of F, keeping track of words as we go
     V := VectorSpace (k, n);
     B := [ V!lambda ];
     A := [* < V!lambda , [ ] , [ ]  > *];
     B_old := B;
     while #B lt n do
          P := { [i, j] : i in [1..#B_old], j in [1..r] |                     
                              B_old[i] * F[j] ne 0 };
          B_new := [ ];
          for p in P do
               b := B_old[p[1]] * F[p[2]];
               if (b * E[p[2]] ne 0) and (b * E[p[2]] in sub < V | B_old[p[1]] >) 
                  and not b in sub < V | B cat B_new > then
                    Append (~B_new, b);   
                    labs := [ [ i , j ] : i in [1..#B] , j in [1..r] | 
                        (B[i] * F[j] ne 0) and (B[i] * F[j] in sub < V | b >) and
                        (b * E[j] ne 0) and (b * E[j] in sub < V | B[i] >)
                        ];
                    labs cat:= [ [ i + #B, j ] : i in [1..#B_new] , j in [1..r] |
                        (B_new[i] * F[j] ne 0) and (B_new[i] * F[j] in sub < V | b >) and
                        (b * E[j] ne 0) and (b * E[j] in sub < V | B_new[i] >)
                        ];
                    w := Append (A[labs[1][1]][2], labs[1][2]);
                    Append (~A, < b , w , labs >);
               end if;
          end for;
          B cat:= B_new;
          B_old := B_new;
     end while;
     
     C := Matrix (B);
     
return C, A;

end intrinsic;


/*
   INPUT: 
      (1) name of the acting Lie algebra 
      (2) an irreducible representation L of the simple Lie algebra
          of type A and Lie rank d
      (3) the subset E of a Chevalley basis of L corresponding to
          the positive fundamental roots; we assume these have been
          obtained somehow (e.g. Ryba's algorithms in theory; whatever
          is in Magma in practice).
      (4) the opposite part of F of the Chevalley basis
   
   OUTPUT: the group of similarities of the simple Lie algebra rep, which
           is also the normalizer of L in its ambient group of linear 
           transformations. 
   
   ***** AT PRESENT THIS IS ONLY IMPLEMENTED FOR TYPE A LIE ALGEBRAS *****
*/

intrinsic SimilaritiesOfSimpleLieModule (name::MonStgElt, L::AlgMatLie :
                    E := [ ] , F := [ ] 
                                        ) -> GrpMat
  { Construct the group of similarites of the given representation.}

     k := BaseRing (L);
     r := Rank (GroupOfLieType (name, k));
      /* TO DO---insert graph auto perm for "name" */
     
     G := GL (Degree (L), k);
     if #E eq 0 then
          E, F := ChevalleyBasis (L);
     end if;
     assert #E ge r;
       /* TO DO---make sure the first r elements correspond to fundamental roots */
     E := [ E[i] : i in [1..r] ];
     F := [ F[i] : i in [1..r] ];
     C, crys := CrystalBasis (L, E, F);
     
     // compute the connected component of the similarity group by exponentiation
     X := [G!__exp (a) : a in E];
     Y := [G!__exp (a) : a in F];
     gens := X cat Y;
assert NormalizesMatrixAlgebra (L, gens); // sanity check
   
     // build the diagonal automorphism
     D0 := [ k!1 ];
     xi := PrimitiveElement (k);
     S := [ xi ] cat [ k!1 : i in [1..r] ];
     for i in [2..#crys] do
          word := crys[i][2];  // the word labelling the i-th node 
          Append (~D0, &*[ S[word[j]] / S[1+word[j]] : j in [1..#word] ]);
     end for;
     D0 := DiagonalMatrix (D0);
     D := C^-1 * D0 * C;
assert NormalizesMatrixAlgebra (L, [D]);  // sanity check
     Append (~gens, D);
     
     // build the graph automorphism
     B := [ Vector (C[i]) : i in [1..Nrows (C)] ];

     V := VectorSpaceWithBasis (B);
     gens0 := [ ];
     type := "A";  // TO DO: consider other types
     for s in Generators (__GraphAutos (type, r)) do
          g0 := [ ];
          for i in [1..#crys] do
               word := crys[i][2];
               gword := [ word[j]^s : j in [1..#word] ];           
               vec := V.1;
               for j in [1..#gword] do  
                    vec := vec * F[gword[j]];
               end for;
               Append (~g0, Coordinates (V, vec));
          end for;
          g0 := Matrix (g0);
          Append (~gens0, g0);
     end for;
     
     for g0 in gens0 do
          if Rank (g0) lt Rank (C) then
               "graph automorphism did not lift at all";
          else
               g := C^-1 * G!g0 * C;
               if NormalizesMatrixAlgebra (L, [g]) then
                    Append (~gens, g);
                    "added a graph automorphism";
               else
                    "graph automorphism did not normalize L";
               end if;
          end if;
     end for;

     Z := [ xi : i in [1..Degree (G)] ];
     Z := G!DiagonalMatrix (Z);
     Append (~gens, Z);

     N := sub < GL (Degree (L), k) | gens >;
    
assert NormalizesMatrixAlgebra (L, [N.i : i in [1..Ngens (N)]]); // final sanity check

return N;

end intrinsic;





