

import "GlobalVars.m" : __SANITY_CHECK;


/*
  Given a STANDARD COPY, STAN, of a *-simple 
  algebra and a self-adjoint element, s, of STAN,
  find a in STAN with (a^*)a = s
*/
__InverseNormSimple := function (STAN, s)

	assert assigned STAN`StarSimpleInfo;
	name := STAN`StarSimpleInfo`simpleParameters[1];
	if name eq "exchange" then
	  a := STAN!1;
	  m := Degree(STAN) div 2; 
	  InsertBlock(~a, ExtractBlock(s,1,1,m,m), 1,1);
	  return (a @ STAN`Star) * a eq s, a;
	end if;
	 
    assert s in STAN;
	assert s eq s @ STAN`Star;
	
	/* deal with degree 1 first */
	if Nrows (s) eq 1 then 
	
	   assert not ((name eq "symplectic") or (name eq "exchange"));
	   K := BaseRing (STAN);
	
	   if name eq "unitary" then
         f := Degree (K); assert f mod 2 eq 0;
         k := GF (Characteristic (K)^(f div 2));
         ss := s[1][1];
         assert ss in k;
         isit, aa := NormEquation (K, k!ss);
         assert isit;
         return true, STAN![aa];         
      else  // orthogonal ... put in the square root again
         ss := k!(s[1][1]);
         isit, aa := IsSquare (ss);
         if not isit then
           "(orthogonal degree 1: entry has no square root in ground field)";
         end if;
         return true, STAN![aa];
      end if;
      
	end if;
	 
// Question (PAB, 07-31-2016): this now works for unitary type too?
	try 
 		F0 := STAN`StarSimpleInfo`reflexiveForm;
	 	F := s * F0;
	 	b := TransformForm (F, name);
	 	assert b in STAN;
	 	a := b @ STAN`Star;
	 	return (a @ STAN`Star) * a eq s, a;
	catch e
		print STAN;
		print STAN`StarSimpleInfo;
		error ("no form");
	end try;
	 
//return a;

end function;


/* 
  Given a (recognized) semisimple *-algebra, T, and 
  self-adjoint s in T, find a in T	with (a^*)a = s.
*/

__InverseNormSemisimple := function (T, s)

	 assert assigned T`StarAlgebraInfo;
	 assert s in T;
	 assert s eq s @ T`Star;

	 C := T`StarAlgebraInfo`transitionMatrix;
	 Cinv := C^-1;
	 C := Matrix (C);
	 Cinv := Matrix (Cinv);
	 simples := T`StarAlgebraInfo`srComponents;
	 degrees := T`StarAlgebraInfo`srDegrees;

	 sc := C * s * Cinv;
	 pos := 1;
	 ac := T!0;
	 for i in [1..#simples] do
		 Si := simples[i];
		 assert assigned Si`StarSimpleInfo;
		 sci := ExtractBlock (sc, pos, pos, degrees[i], degrees[i]);
		 assert sci in Si;
		 STANi := Si`StarSimpleInfo`standardSimple;
		 fi := Si`StarSimpleInfo`standardIsomorphism;
		 gi := Si`StarSimpleInfo`standardInverse;
		 im_sci := sci @ fi; 
		 isit, im_aci := __InverseNormSimple (STANi, im_sci);
		 if not isit then
		  return false, _;
		 end if;
		 aci := im_aci @ gi;
		 InsertBlock (~ac, aci, pos, pos);	  
		 pos +:= degrees[i];
	 end for;
	 
	 a := Cinv * ac * C;
	 
	 assert a in T;
	 assert (a @ T`Star) * a eq s;
	 
return true, a;

end function;


/**

  Given an algebra $A$ with involution $*$, and a Hermitian element
  $s=s^*$, determine if $s=N(a)=a^* a$ for some $a\in A$.  
  
  This follows the (unpublished) algorithm of Ivanyos-Qiao, 2016.
  
  Note that the group 
	$$ A^{\#} = \{ a \in A : N(a)=1 \}$$
  Is computed by the command IsometryGroup following the algorithm of [BW12].
  Solutions to $s=N(a)$ form a coset $tA^{\#}$.

 */
intrinsic InverseNorm (A::Alg, s::AlgElt) -> BoolElt, AlgElt
  {Solve for a where s = N(a) = a^* a.}

  assert RecogniseStarAlgebra (A);
  J := A`StarAlgebraInfo`jacobsonRadical;
  T := A`StarAlgebraInfo`taftComplement;

  if (Dimension (J) eq 0) or (s in T) then
	return __InverseNormSemisimple (T, s);
  end if;	
  
  /* first solve in A/J */
  Tbas := Basis (T);
  Jbas := Basis (J);
  k := BaseRing(A);
  MS := KMatrixSpace (k, Degree (A), Degree (A));
  MS := KMatrixSpaceWithBasis ([MS!x : x in Tbas cat Jbas]);
  coords := Coordinates (MS, MS!Matrix (s));
  s_proj := &+ [ coords[i] * Tbas[i] : i in [1..#Tbas] ];
  if __SANITY_CHECK then
	assert s_proj in T;
	assert s_proj eq s_proj @ T`Star;
  end if;
		
  isit, a := __InverseNormSemisimple (T, s_proj);
  if not isit then	return false, _; end if;
	 
  /* now refine approximation through radical */
  while not ((a @ A`Star)*a eq s) do
	a := a + (a @ A`Star)^-1 * (s - (a @ A`Star) * a) / 2;
  end while;

  if __SANITY_CHECK then	 
	 assert (a @ A`Star) * a eq s;
	 "win";
  end if;
  
return true, a;

end intrinsic;
