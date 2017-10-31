//freeze;

// EOB Oct 2016: this is a copy of the file unipotent.m distributed 
// in GrpPC/pgps directory 
// We include it here to avoid path import problems 


/* !WARNING! Several functions in this file are being used by
      package/Group/GrpMat/CompTree/classical/rewriting/unipotent.m
    & package/Group/GrpMat/CompTree/classical/rewriting/MatrixPGroup.m
   so if you make any changes here, check whether you need to make
   any changes there! */
// modified by Csaba Schneider to make it compatible with rewriting
/* Algorithm to construct stabiliser of subspace under unipotent group.
   Original algorithm described in thesis of Ruth Schwingel, QMUL, 2000.
   This general implementation prepared by Elliot Costi, with input
   from Leedham-Green and O'Brien; August 2007.
*/

/* We redefine depth to cope with non prime fields. The Depth Plus of a
   vector consists of a pair. The first entry is the vector's depth in the
   magma sense. If you consider an element of the prime field as a
   polynomial with the primitive element (w) as the indeterminant, then
   the field can be considered as a vector space of the prime field; the
   coefficients of the powers of w being the entries in the vector. For
   example, in the field 5^3, the element 2 + 4w + 3w^2 would map to the
   vector (2 4 3). If the depth of the vector v is i, then the second
   entry in Depths Plus is the depth of v[i] considered as a vector in
   this way. For example, the vector over the field of 125 elements
   [0 0 w 1] has Depth Plus of [3, 2] as 3 is the depth in the old sense
   and w corresponds to the vector (0 1 0), which has depth 2. */
DepthPlus:= function(v)
   d := Depth(v);
   if d eq 0 then return [0, 1]; end if;
   F := BaseRing(v);
   V := VectorSpace(F, Degree(F));
   return [d, Depth(V!Eltseq(v[d]))];
end function;

/* depths is list containing depth of vectors in UU; w is vector; UU is
   a subspace of the original space where each basis element is in canonical
   form; return depth of w wrt {w, UU}. This is different to the depth of a
   vector in the above sense. Here, the depth of w may be d but the
   echelonization process using the vectors in UU may kill the d-th
   entry of w. Hence, the SubspaceDepth might be greater than d. */
SubspaceDepth:= function (depths, w, UU)
   n := #depths - Dimension (UU);

   /* depths will be of the same length as the dimension of the input
      subspace. The first n entries of depths are as yet undefined.
      They become defined as further basis elements of the input subspace
      are canonised. */

   U := Basis (UU);
   temp := [];
   for i in [n+1..#depths] do
      temp[i] := depths[i][1];
   end for;
   depths := temp;

   dw := DepthPlus(w);
   while dw[1] in depths do
      pos := Position (depths, dw[1]) - n;

      /* pos is the position in the defined portion of the depths vector
         with depth equal to that of w. */

       w := w - w[dw[1]] / U[pos][dw[1]] * U[pos];

      /* in the above, w[dw[1]] is the first non zero entry in w and
         U[pos][dw[1]] is the first non zero entry in U[pos] since both
         have the same depth. Hence this process kills the dw[1]-th
         position in w. */

      dw := DepthPlus(w);
   end while;

   if dw ne [0, 1] then return dw; else return [Degree(w) + 1, 1]; end if;

   /* second bit is the zero vector case */
end function;

/* echelonise v wrt UU. UU and depths as above. It takes the vector v, and
   kills as many places as it can within the vector by subtracting suitable
   multiples of the other basis vectors of UU from it. */
EcheloniseVector := function (v, depths, UU)
    U := Basis (UU);
    j := 0;
    for i in [1..#depths] do
       if IsDefined (depths, i) then
          j +:= 1;
          k := depths[i][1];
          alpha := v[k];
          if alpha ne 0 then
             v := v - (alpha / U[j][k]) * U[j];
          end if;
       end if;
    end for;

    return v;

end function;

/* find increasing chain of subspaces of V fixed under X */
PInvariantFlag := function (V, X)
    
   F := BaseRing (X);
   q := #F;
   d := Degree (X);
   MA := MatrixAlgebra (F, d);
   t := Ngens (X);
   Y := [MA!X.j : j in [1..t]];

   /* clumsy handling of trivial case */
   if t eq 0 then
      B := Basis (V);
      d := #B;
      W := [sub < V | [B[j] : j in [i..d]]> : i in [1..d]];

      /* take the set of subspaces to be those generated by
         the last (d-i) vectors of V */

      Append (~W, sub < V | >);
   else
      W := [V]; // W starts a list containing just the whole space
      k := 1;
      I := Identity (MA);    
      while Dimension (W[k]) ne 0 do
         k +:= 1;
         W[k] := &+[W[k-1] * (Y[j] - I): j in [1..t]];
         /* this forms the next term in the sequence by taking the
            previous space and multiplying it by all the generators of the
            p-group minus the identity */

      end while;   
   end if;

   flag := []; 

   for i in [1..#W - 1] do
       F, phi := quo < W[i] | W[i + 1] >;

      /* F is the quotient space and phi is the natural map. For example in
         the trivial case, we go from a subspace with n vectors over a
         subspace with n-1 vectors to the full vector space of dimension 1. */

      BF := Basis (F);        
      FB := [BF[j] @@ phi : j in [1..Dimension (F)]];

      /* the pre-image of each basis vector back up in W[i] */
      flag cat:= FB; // adds FB to flag
   end for;

   /* the collection of spaces made up of the last j vectors in flag. */
        
   // change by csaba     
   //Spaces := [sub < V | >] cat
   //   [sub <V | [flag[i]: i in [#flag..j by -1]]>: j in [#flag..1 by -1]];

   /* reverses the order so that the full space is first and the empty space
      is last. */
   // change by csaba                    
   //Reverse (~Spaces);

   /* taking the vectors of flag and turning them into a matrix. E.g. [1, 0]
      and [0, 1] becomes the 2 by 2 identity matrix. */
   CB := (GL (d, q) ! &cat[Eltseq (f): f in flag])^-1;
   
   // changes by csaba
   //  return flag, CB, Spaces;
     return flag, CB;
end function;

GetPFlagWithCache := function(V, K)
	if assigned K`CB then return K`CB; end if;
	_, K`CB := PInvariantFlag(V, K);
	return K`CB;
end function;


/* return generating set which determines (decreasing) chief series
   subs for matrix group K generated by X.

   Init is the same as for InternalPChiefSeriesGenerators, but coded
   with strings instead of integers.
   "none" = 0 = no init
   "X"    = 1 = init based on X
   "XB"   = 2 = init based on X & B
*/
PChiefSeriesGeneratorsWithCache := function (K, X, XSLP, InitStr)

	/* Convert InitStr to integer */
	case InitStr :
		when "none": Init := 0;
		when "X"   : Init := 1;
		when "XB"  : Init := 2;
		else       : error "Unsupported InitStr";
	end case;

	/* Check whether result is cached for identical or "better"
	   init */
	if (assigned K`XInit) and (K`XInit ge Init) then
		return K`X, K`XSLP;
	end if;

	/* Otherwise make a call to the regular function */
	if IsNull(X) then X := [K | ]; end if;
	if IsNull(XSLP) then XSLP := [SLPGroup(Ngens(K)) | ]; end if;
	K`X, K`XSLP := InternalPChiefSeriesGenerators(X, XSLP, Init);
	K`XInit := Init;

	return K`X, K`XSLP;

end function;


/* Given a matrix M, and an integer j, take the jth diagonal above the
   leading diagonal of M and return it as a vector */

VectorExtract := function(j, M)
	n := Degree(M);
	F := BaseRing(M);
	v := [M[i, i+j] : i in [1..n-j]];
	v := VectorSpace(F, n-j)!v;
	return v;
end function;

/* depth of u - u * g. If zero vector, [Degree(u)+1, 1] is returned */

RelativeVectorDepth := function (u, g)
    d := DepthPlus(u - u * g);
    return d[1] eq 0 select [Degree(u) + 1, 1] else d;
end function;

/* depth of u - u * g */

ShadowRelativeVectorDepth := function (u, g)
   d := Depth (u - u * g);
   return d eq 0 select Degree (u) + 1 else d;
end function;

/* F is the ground field, u is a vector that we are canonising,
   i is a pair representing the depth of u-u*h, h is the generator
   of the p-group with minimal weight with respect to u, k is some other
   generator of the p-group with weight greater than that of h.  Return
   the integer that makes u-u*k*h^alpha have greater depth than u-u*k. */

FindMultiple := function (F, u, i, k, h)
    v0 := (u - u*k*h) - (u - u*k);
    a := Eltseq(v0[i[1]])[i[2]];
    b := Eltseq((u - u*k)[i[1]])[i[2]];
    beta := -b/a;
    if beta notin PrimeField(F) then error "error in FindMultiple"; end if;
    return IntegerRing()!beta;
end function;

/* depths is the list of depths of basis vectors for U, F is the
   ground field, u is the vector we are canonising, i is a pair
   telling you the weight of u with respect to h, h is the generator of the
   p-group of least weight with respect to u, k is some other generator of
   the p-group, U is the subspace of the original subspace consisting of
   just the so-far-canonised basis vectors. This function finds the integer
   alpha that makes u-u*(k * h^alpha) have greater depth that u-u*k. */

BFindMultiple := function (depths, F, u, i, k, h, U)

   n := #depths - Dimension (U);
   w := u - u*k*h;

   depths2 := depths;
   temp := [];
   for i in [n+1..#depths] do
      temp[i] := depths[i][1];
   end for;
   depths := temp;

   BU := Basis(U);

   dw := DepthPlus(w);
   while dw[1] in depths do

      /* pos is the position in the defined portion of the depths
         vector with depth equal to that of w.*/
      pos := Position (depths, dw[1]) - n;

      /* w[dw[1]] is the first non zero entry in w
         and U[pos][dw[1]] is the first non zero entry in U[pos] since
         both have the same depth. Hence this process kills the dw[1]-th
         position in w. */

      w := w - w[dw[1]] / BU[pos][dw[1]] * BU[pos];

      dw := DepthPlus(w);
   end while;

   v1 := u - u*k;
   v1 := EcheloniseVector(v1, depths2, U);
   v0 := w - v1;
   a := Eltseq(v0[i[1]])[i[2]];
   b := Eltseq(v1[i[1]])[i[2]];
   beta := -b/a;

   if beta notin PrimeField(F) then error "error in BFindMultiple"; end if;
   return IntegerRing()!beta;
end function;

/* F is the ground field, u is the vector that you wish to kill an
   entry in, h is the generator of the p-group that you will use to kill
   the entry in u and a i is a pair consisting of the depth of u-u*h */

VectorMultiple := function (F, u, h, i)
    v0 := u*h - u;
    a := Eltseq(v0[i[1]])[i[2]];
    b := Eltseq(u[i[1]])[i[2]];
    beta := -b/a;

    if beta notin PrimeField(F) then error "error in VectorMultiple"; end if;
    beta := IntegerRing()!beta;
    u := u*(h^beta);

    return beta, u;

end function;

/* This function finds the power of a matrix h (a generator of the p-group)
   that kills the (i[2]-1)-th power of the i[1]-th entry of the input vector u.
   The other inputs: F is the ground field, depths is a list of
   depths of the basis vectors of the full subspace we are canonising, i is a
   pair consisting of the weight of h with respect to u (and is minimal amongst
   all elements of X). */

SpaceMultiple := function (F, u, depths, subU, h, i)

   u := EcheloniseVector (u, depths, subU);
   u0 := EcheloniseVector (u*h, depths, subU) - u;
   a := Eltseq(u0[i[1]])[i[2]];
   b := Eltseq(u[i[1]])[i[2]];
   beta := -b/a;

   if beta notin PrimeField(F) then error "error in SpaceMultiple"; end if;
   beta := IntegerRing()!beta;
   u := u*h^beta;
   u := EcheloniseVector (u, depths, subU);

   /* return the required power of h that kills the
      required entry in u and the vector u as deformed by h. */
   return beta, u;

end function;

/* return canonical v for the input vector u, an element x in the p-group
   such that u * x = v, and the stabiliser in the p-group of v.
   X is generators of the p-group in upper uni-triangular form.

   The InitStr parameter is passed into PChiefSeriesGeneratorsWithCache
 */

VectorCF := function (X, XSLP, u: ComputeBase := true, InitStr := "none")

   d := Degree (u); F := BaseRing (Parent (u));
   if #X eq 0 then
      return u, Identity (GL(d, F)), Identity(SLPGroup(0)), X;
   end if; // the trivial case

   /* calculate weight of each generator of the p-group with respect to v */
   v := u;
   depth := [RelativeVectorDepth (v, g) : g in X];

   /* calculate the minimum entry in the above vector */
   depth1 := [depth[x, 1] : x in [1..#depth]];
   j0 := Minimum (depth1);
   depth2 := [];
   for x in [1..#X] do
      if depth[x, 1] eq j0 then
         Append(~depth2, depth[x, 2]);
      end if;
   end for;
   j1 := Minimum (depth2);

   /* setup word sequence for reordering of X later */
   if j0 eq d + 1 then
      word := [i : i in [1..#X]];
   else
      word := [];
   end if;

   x := X[1]^0;
   xslp := Identity(Parent(XSLP[1]));
   Y := X;
   YSLP := XSLP;

   /* The following loop starts with the generator g in X of minimum
      weight ([j0, j1]) with respect to the vector that we wish to canonise.
      We find a power of this matrix g that kills the coefficient of the
      (j1-1)-th power of w (the primitive element) in the j0-th position of
      v. We then consider every other element of X. If the element x in X
      has depth [j0, j1], then x is replaced by a power of g times x such
      that the new x has a depth greater than [j0, j1]. g is then removed
      from X and the process is repeated until every element of X has depth
      [d+1, 1] or X becomes empty. */

   while (j0 lt d + 1) do
      pos := Position (depth, [j0, j1]);
      g := X[pos];
      gslp := XSLP[pos];

      /* find the power alpha of g that kills the [j0, j1] position
         of v and performing this process on v. */
      alpha, v := VectorMultiple (F, v, g, [j0, j1]);

      /* keep track of the element that satisfies u * x = v */
      x := x * g^alpha;
      xslp := xslp * gslp^alpha;

      Y := [];
      /* keep track of all the adjusted elements of X */
      YSLP := [];

      last := pos;
      for i in [1..#X] do
         h := X[i];
         if i eq pos then continue; end if;
         if RelativeVectorDepth (v, h) eq [j0, j1] then
            beta := FindMultiple (F, v, [j0, j1], h, g);
            /* find power of g that will adjust h to give it higher depth */
            hh := h * g^beta; 
            hhslp := XSLP[i] * gslp^beta;
            /* setting letter for word */
            letter := Minimum(i, last); last := i;
            g := X[last]; gslp := XSLP[last];
         else
            hh := h;
            /* those elements of X already of a higher depth than g. */
            hhslp := XSLP[i];
            letter := i;
         end if;
         Append (~Y, hh);
         Append (~YSLP, hhslp);
         Append (~word, letter);
      end for;

      /* tests from shadow.m version of ShadowNextSubspaceCF */
      assert #word eq #Y;
      assert #Set(word) eq #word;

      word1 := word;
      ParallelSort (~word, ~Y);
      ParallelSort (~word1, ~YSLP);

      X := Y;
      XSLP := YSLP;

      word := [];

      /* if we are not assuming that X forms the required chief series,
         we must fix up the chief series for X */
      if ComputeBase then
         X, XSLP := PChiefSeriesGeneratorsWithCache(sub<GL(d,F)|X>, X, XSLP, InitStr);
      end if;

      if #X eq 0 then break; end if;
      depth := [RelativeVectorDepth (v, g) : g in X];
      /* recalculate the weights of each element of X with respect to v. */
      depth1 := [depth[x, 1] : x in [1..#depth]];
      j0 := Minimum (depth1);
      depth2 := [];
      for x in [1..#X] do
         if depth[x, 1] eq j0 then
            Append(~depth2, depth[x, 2]);
         end if;
      end for;
      j1 := Minimum (depth2);

   end while;

   /* return the canonised vector, the element that maps the input vector
      to the canonised one (and its slp equivalent) and the stabiliser of v
      in the p-group (and its slp equivalent) */

   return v, x, xslp, X, XSLP;

end function;

/* The one dimensional subspace of U consisting of just the one canonised
   vector is U_t. The following function has as input the full subspace UU
   so-far-canonised, the full vector space V, the stabiliser X of U_i+1, the
   depths of the so far canonised basis vectors in U and the index where
   U_index+1 has been fully canonised and U_index is to be canonised.

   Init parameter as per PChiefSeriesGeneratorsWithCache
*/

NextSubspaceCF := function (X, XSLP, V, UU, depths, index:
                            ComputeBase := true, InitStr := "none")
   U := Basis (UU);
   /* set U to be the unique echelonised basis of UU */
   d := Degree (UU);

   /* the length of the vectors in UU */
   F := BaseRing(UU);
   t := #U;

   /* vector to be canonised with respect to the other basis elements */
   v := U[index];

   /* a subspace of U consisting of the so-far-canonised vectors. */
   subU := sub < V | [U[i] : i in [index + 1..t]]>;

   /* subspace weight of v with respect to each g in X. */
   depth := [SubspaceDepth (depths, v - v * g, subU) : g in X];

   /* determine the minimum entry in the above depth vector */
   depth1 := [depth[x, 1] : x in [1..#depth]];
   j0 := Minimum (depth1);
   depth2 := [];
   for x in [1..#depth] do
      if depth[x, 1] eq j0 then
         Append(~depth2, depth[x, 2]);
      end if;
   end for;
   j1 := Minimum (depth2);

   /* setup word sequence for reordering of X later */
   if j0 eq d + 1 then
      word := [i : i in [1..#X]];
   else
   word := [];
   end if;

   x := X[1]^0; /* we start with the identity element */
   xslp := Identity(Parent(XSLP[1]));

   /* as we will be altering X for the short term, we will store it
      in Y for now and alter Y instead. */
   Y := X;
   YSLP := XSLP;

   while (j0 lt d + 1) do
      pos := Position (depth, [j0, j1]);
      g := X[pos];
      gslp := XSLP[pos];
      v := EcheloniseVector (v, depths, subU);
      alpha, v := SpaceMultiple (F, v, depths, subU, g, [j0, j1]);
      x := x * g^alpha; /* keep a note of what's been done in x */
      xslp := xslp * gslp^alpha;
      Y := [];
      /* we will now multiply each element of X by a power of g
         such that each element now has weight with respect to v greater
         than that of g. */
      YSLP := [];
      last := pos;
      for i in [1..#X] do
         h := X[i];
         /* alteration to match shadow.m:ShadowNextSubspaceCF */
         if i eq pos then continue; end if;
         if SubspaceDepth (depths, v - v * h, subU) eq [j0, j1] then
            beta := BFindMultiple (depths, F, v, [j0, j1], h, g, subU);
            hh := h * g^beta;
            hhslp := XSLP[i] * gslp^beta;
            /* setting letter for word */
            letter := Minimum(i, last); last := i;
            g := X[last]; gslp := XSLP[last];
         else
            hh := h;
            hhslp := XSLP[i];
            /* setting letter for word */
            letter := i;
         end if;
         Append (~Y, hh);
         Append (~YSLP, hhslp);
         Append (~word, letter);
      end for;

      /* tests from shadow.m version of ShadowNextSubspaceCF*/
      assert #word eq #Y;
      assert #Set(word) eq #word;

      word1 := word;
      ParallelSort (~word, ~Y);
      ParallelSort (~word1, ~YSLP);

      X := Y;
      XSLP := YSLP;
      word := [];

      if ComputeBase then
         X, XSLP := PChiefSeriesGeneratorsWithCache(sub<GL(d,F)|X>, X, XSLP, InitStr);
      end if;

      /* if X is now empty, we are done */
      if #X eq 0 then break; end if;

      depth := [SubspaceDepth (depths, v - v * g, subU) : g in X];
      depth1 := [depth[x, 1] : x in [1..#depth]];
      j0 := Minimum (depth1);
      depth2 := [];
      for x in [1..#depth] do
        if depth[x, 1] eq j0 then
          Append(~depth2, depth[x, 2]);
        end if;
      end for;
      j1 := Minimum (depth2);

   end while;

   /* modify the full subspace by the matrix that
      canonises the vector that you wished to canonise. */
   UU := UU * x;

   /* add the depth of the canonised vector to depths */
   depths[index] := DepthPlus(v);

   /*printf "NextSubspaceCF : %o\n%o\n%o\n%o\n", x, UU, depths, X;*/

   /* return the element that maps the old U to the new U, the new U,
      the list of depths of the basis vectors of U and the stabiliser
      of U in the p-group. */
   return x, xslp, UU, depths, X, XSLP;
end function;

/* determine canonical form for U under action of X; return canonical
   form UC, element trans where U^trans = UC, and stabiliser in X of UC.
   The X supplied here is the upper-unitriangularized generating
   set for the original p-group and U is the similarly altered version
   of the original subspace.

	Init parameter as per PChiefSeriesGeneratorsWithCache.
*/
SubspaceCF := function (X, XSLP, U: ComputeBase := true, InitStr := "none")
   d := Degree (U); F := BaseRing (U);

   /* the trivial cases */
   if #X eq 0 then
      return U, Identity (GL(d, F)), Identity(SLPGroup(0)), X, XSLP;
   end if;
   if Dimension(U) eq 0 then
      return U, Identity (GL(d, F)), Identity(Parent(XSLP[1])), X, XSLP;
   end if;

   UB := Basis (U);
   t := #UB; 
   CF, trans, transslp, X, XSLP := VectorCF(X, XSLP, UB[t]:
                                   ComputeBase := ComputeBase, InitStr := InitStr);

   /* finds the canonical form for the last basis vector of U and reduces
      X to the stabilizer of this vector in U. */
   U := U * trans;

   /* multiply by trans to canonize the last basis vector */
   UB := Basis (U);
   depths := [];

   /* we now construct a list of the depths of the canonised basis vectors.
      Not yet canonised implies that corresponding entry is undefined. */

   depths[t] := DepthPlus (UB[t]);
   /* setting the last entry of the depths vector to the depth of the
      canonised basis vector. So it looks like this:
      [undef, undef, ..., undef, DepthsPlus(UB[t])]. */

   /* The one dimensional subspace of U consisting of just the one
      canonised vector is U_t. The following loop, at each iteration, inputs
      the full subspace U so-far-canonised, the full vector space V, the
      stabiliser X of U_i+1, the depths of the so far canonised basis vectors
      in U and the index i where U_i+1 has been fully canonised and U_i is to
      be canonised. */

   V := VectorSpace (F, d);
   for i in [t - 1..1 by -1] do
      if #X eq 0 then break; end if;
      temp, tempslp, U, depths, X, XSLP := NextSubspaceCF(X, XSLP, V, U,
                                   depths, i: ComputeBase := ComputeBase, InitStr := InitStr);

      /* the output here is the full vector space U with one extra basis
         vector canonised, the depth of the newly canonised basis vector has
         been added to depths, X is the stabiliser of the so-far-canonised U
         in the p-group */

      trans *:= temp;

      /* the matrix that sends the original U to the canonised-so-far U */
      transslp *:= tempslp;
   end for;

   return U, trans, transslp, X, XSLP;
end function;

/* S is a p-group; U is a subspace of natural module; return canonical
   form UC for U, matrix trans where U^trans = UC, and generators for
   stabiliser in S of UC; if ComputeBase is false, we assume that the
   generators of S are a decreasing chief series for S

   InitStrs is a pair passed into PChiefSeriesGeneratorsWithCache via
   two different routes: The first immediately (provided ComputeBase
   is true), the second via SubspaceCF.

 */

/* Modified version of PGroupStabiliser.  Alterations: S should be SeqEnum[GrpMatElt],
   returns YSLP. */
PGroupStabiliser_ := function (S, U, W: ComputeBase := true, InitStrs := <"X","none">)
   d := Degree (U); F := BaseRing (U);

   K := sub < GL (d, F) | S >;

   XSLP := [ W.j : j in [1..Ngens(W)] ];

   /* trivial case */
   if #S eq 0 or Ngens (K) eq 0 then
      return U, Identity (K), Identity(W), S, XSLP, 1;
   end if;

   V := VectorSpace (F, d);
   CB := GetPFlagWithCache(V, K);

   /* CB is a change of basis matrix that maps each element of S to
      one in upper unitriangular form */

   /* make S upper unitriangular */
   S := [s^CB : s in S ];

   if ComputeBase then 
      S, XSLP := PChiefSeriesGeneratorsWithCache(K, S, XSLP, InitStrs[1]);
   end if;

   CBinv := CB^-1;

   U := U^CB; 
   UC, trans, transslp, Y, YSLP := SubspaceCF (S, XSLP, U:
       ComputeBase := ComputeBase, InitStr := InitStrs[2]);

   /* input p-group and the subspace, return canonicalized subspace,
      the element that maps U to UC and the generators of the
      stabilizer of U in S. */
   p := #F; length := p^(#S - #Y);
   Trans := CB * trans; TransInv := Trans^-1;

   /* prepare inverse of transslp to update YSLP */
   transslp_inv := transslp^-1;

   return UC^CBinv, Trans * CBinv, transslp,
      [Y[i]^TransInv : i in [1..#Y]], [transslp * YSLP[i] * transslp_inv : i in [1..#YSLP]], length;

   /* CBinv to un-upper-unitriangular everything; the third return value
      is the stabiliser of U in the p-group; apply trans^-1 to obtain
      generators to get the stabiliser of the original U. */
end function;

/* Calls PGroupStabiliser_ and returns values expected for UnipotentStabiliser.
   In particular: converts S to SeqEnum[GrpMatElt], discards XSLP and returns
   X as a subgroup of GL(d, F). */
PGroupStabiliser := function (S, U, W : ComputeBase := true, InitStrs := <"X","none">)
    /* Calls PGroupStabiliser_, which requires S to be SeqEnum[GrpMatElt] */
    UC, trans, transslp, X, XSLP, length := PGroupStabiliser_ ([S.i : i in [1..Ngens(S)]], U, W : ComputeBase := ComputeBase,
        InitStrs := InitStrs);

    d := Degree (U); F := BaseRing (U);

    /* Discard the XSLP argument for UnipotentStabiliser call and return X as subgroup of GL(d, F) */
    return UC, trans, transslp, sub < GL(d, F) | X >, length;
end function;

/* From the old shadow.m code */
ShadowPGroupStabiliser := function (G, A, S, U : ComputeBase := false)
    /* Note that S is an SeqEnum[GrpMatElt], not GrpMat */
    W := SLPGroup(#S);

    /* Call PGroupStabiliser_ */
    UC, trans, transslp, X, XSLP, length := PGroupStabiliser_ (S, U, W : ComputeBase := ComputeBase);

    /* Construct automorphism group for evaluating slp elts */
    A := AutomorphismGroup(G, [ G.i : i in [1..NPCgens(G)] ],
      [ [ G.i @ a`map : i in [1..NPCgens(G)] ] : a in A ]);

    /* Evaluate XSLP in A */
    B := Evaluate(XSLP, A);

    /* Evalute transslp in A */
    aut := Evaluate(transslp, A);

    return UC, trans, X, B, aut, length;
end function;


/* A word of warning: Some code in the CompTree package uses a function
   called UnipotentStabiliser that is equivalent to this intrinsic, save
   for some parameters. It may be found in
     package/Group/GrpMat/CompTree/unipotent.m
*/
intrinsic UnipotentStabiliser (G:: GrpMat, U:: ModTupFld : 
         ComputeBase := true, 
         InitStrs := <"X","none"> )
         -> GrpMat, ModTupFld, GrpMatElt, GrpSLPElt
{G is a p-subgroup of GL(d, q) where GF(q) has characteristic p;
 U is a subspace of the natural vector space for G.
 Compute the stabiliser of U in G, a canonical element C of the orbit
 of U under G, an element x of G such that U^x = C, and the SLP for x
 as element of the word group of G}

   // require IsUnipotent (G): "Group must be unipotent";

   W := WordGroup(G);
   cf, trans, transslp, stab := PGroupStabiliser (G, U, W:
                                ComputeBase := ComputeBase,
                                InitStrs := InitStrs );

   return stab, cf, trans, transslp;

end intrinsic;

/* return generating set which determines (decreasing) chief series
   subs for unipotent group G. If Words is set to true, an SLP
   for each new generator in terms of the input generators is also
   returned. */
UnipotentChiefSeries := function (G: Words := false)
   if Ngens(G) eq 0 then
      if Words then return G, []; else return G; end if;
   end if;

   F := BaseRing(G);
   W := WordGroup(G);
   d := Dimension(G);
   identity := Id(G);
   flag, CB := PInvariantFlag (VectorSpace(F, d), G);
   X := [G.i^CB : i in [1..Ngens (G)]];

   B := [];
   BSLP := [];
   p := Characteristic(F);

   depth := [InternalMatrixWeight(g) : g in X];
   Y := [<X[i], depth[i]> : i in [1..#X]];
   YSLP := [W.i : i in [1..#X]];
   XSLP := YSLP;

   depth1 := [depth[x, 1] : x in [1..#depth]];
   j0 := Minimum (depth1);
   depth2 := [];
   for x in [1..#X] do
      if depth[x, 1] eq j0 then
         Append(~depth2, depth[x, 2]);
      end if;
   end for;
   j1 := Minimum (depth2);
   depth3 := [];
   for x in [1..#X] do
      if (depth[x, 1] eq j0) and (depth[x, 2] eq j1) then
         Append(~depth3, depth[x, 3]);
      end if;
   end for;
   j2 := Minimum (depth3);

   while #Y ne 0 do
      pos := Position (depth, [j0, j1, j2]);
      g := Y[pos];
      gslp := YSLP[pos];
      Append(~B, g[1]);
      Append(~BSLP, gslp);

     InternalIncreaseDepthPair(pos, ~Y, ~YSLP, j0, j1, j2);

      v := g[1]^p;
      if v ne identity then
         Append(~Y, <v, InternalMatrixWeight(v)>);
         Append(~YSLP, gslp^p);
      end if;
      for i in [1..#X] do
         x := X[i];
         v := (g[1], x);
         if v ne identity then
            Append(~Y, <v, InternalMatrixWeight(v)>);
            xslp := XSLP[i];
            Append(~YSLP, (gslp, xslp));
         end if;
      end for;

      if #Y eq 0 then break; end if;

      depth := [Y[j, 2] : j in [1..#Y]];
      depth1 := [depth[x, 1] : x in [1..#depth]];
      j0 := Minimum (depth1);
      depth2 := [];
      for x in [1..#Y] do
         if depth[x, 1] eq j0 then
            Append(~depth2, depth[x, 2]);
         end if;
      end for;
      j1 := Minimum (depth2);
      depth3 := [];
      for x in [1..#Y] do
         if (depth[x, 1] eq j0) and (depth[x, 2] eq j1) then
            Append(~depth3, depth[x, 3]);
         end if;
      end for;
      j2 := Minimum (depth3);

   end while;

   B := [B[i]^(CB^-1) : i in [1..#B]];

   Reverse (~B);
   P := GL (d, F);
   C := [sub<P|>] cat [sub <P | [B[i]: i in [1..j]]>: j in [1..#B]];
   Reverse (~C);

   if Words then
      return C, Reverse (BSLP);
   else
      return C, _;
   end if;
end function;
