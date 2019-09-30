newPackage(
    "MaximalRankProperties",
    Authors => {
	{
	    Name => "Lisa Nicklasson",
	    Email => "lisan@math.su.se"}
	},
    Headline => "a package for investigating the Lefschetz properties, the maximal rank property, and the Fröberg conjecture",
    DebuggingMode => false
    )
    
export{
    "checkWLP",
    "checkSLP",
    "checkMRP",
    "hasMaxRank",
    "hasFrobergProp"
    };





















--hvec: gives the coefficients of a polynomial as a list
hvec=(p)->(
    d:=(degree p)#0;
    T:= first gens ring p;
    return for i from 0 to d list coefficient(T^i,p))

--trunc: Mata med en lista av tal och få en trunkerad lista. Trunkeras vid första icke-negativa elementet.
trunc=(v)->(
    a:=v#0;
    i:=0;
    l:={};
    while a>0 do(
	l=l|{a};
	i=i+1;
	if i> length v-1 then return l;
	a=v#i;
	);
    return l;
    )



--compareHilb: jämför en hilbertserie med den förväntade för maximal rang.
--input: hilbs: hilbertserien, i form av en lista
--    	  exps: den förväntade serien för maximal rang, i form av en lista
--output: true om lika
--    	  {i, dim, failtype} om ej lika, där i är första stället de skiljer sig åt
--    	      failtype = inj / sur
--    	      dim = differensen = dim av kärnan om ej inj, codim av bilden om ej surj.
compareHilb=(hilbs,exps)->(
    lh:=length hilbs;
    le:=length exps;
    for i to le-1 do if hilbs#i!=exps#i then return {i, hilbs#i-exps#i,"inj"};
    if lh>le then return {le, hilbs#le, "sur"};
    return true;
    )




--toZZT: tar ett element i en DegreesRing, och skickar till ZZ[T]
toZZT=(p)->(
    DR:=ring p;
    T:=first gens DR;
    F:=map(ZZ[T],DR);
    return F(p);
    )

--isArtinian: Kollar om en ring är artinsk.
isArtinian=(R)->( dim(R)==0)



   

--hasMaxRank: Tar ett element f och kollar om multiplikation med f har maximal rang i alla grader.
hasMaxRank=method()
hasMaxRank(RingElement):=(f)->(
    S:=ring f;
    if not isQuotientOf(PolynomialRing,S) then error "The argument must be an element of a quotient of a polynomial ring.";
    if not isArtinian(S) then error "The argument must be an element of an Artinian ring.";
    if ((not isHomogeneous(f)) or isConstant(f)) then error "The argument must be a non-constant homogeneous element.";
    d:=(degree f)#0;
    p:=numerator reduceHilbert hilbertSeries S;
    p=toZZT(p);
    T:=first gens ring p;
    h:=trunc hvec ((1-T^d)*p);
    v:=hvec numerator reduceHilbert hilbertSeries (S/ideal{f});
    result:=compareHilb(v,h);
    if result===true then return true;
    faildeg:=(result#0)-d;
    if result#2=="inj" then return ("Multiplication by " | toString(f) | " fails to be injective in degree " | toString(faildeg) | ". The kernel has dimension " | result#1 | ".");
    if result#2=="sur" then return ("Multiplication by " | toString(f) | " fails to be surjective in degree " | toString(faildeg) | ". The image has codimension " | result#1 | ".");
    )




--checkMRP: Kollar om en artinsk ring har MRP.
checkMRP=method()
checkMRP(QuotientRing):=(R)->(
    if not isQuotientOf(PolynomialRing,R) then error "The argument must be a quotient of a polynomial ring.";
    if not isArtinian(R) then error "The argument must be an Artinian ring.";
    p:=numerator reduceHilbert hilbertSeries R;
    p=toZZT(p);
    T:=first gens ring p;
    t:=(degree p)#0;
    H:=for j from 1 to t list trunc hvec((1-T^j)*p);
    canFindMREl:=(d)->(
	faildeg:=-1;
	failtype:="";
	faildim:=0;
	for i to 4 do(
	    f:=random(d,R);
            v:=hvec numerator reduceHilbert hilbertSeries (R/ideal{f});
	    result:=compareHilb(v,H#(d-1));
	    if result===true then return true;
	    if (result#0)-d>faildeg then (
		faildeg=(result#0)-d;
		faildim=result#1;
		failtype=result#2;
		);	    
	    );
	return {faildeg,faildim, failtype};
	);
    for d from 1 to t do(
	result:=canFindMREl(d);
	if not result===true then (
	    if result#2=="inj" then return ("Could not find an element of degree " | d | " such that multiplication is injective in degree " | result#0| ". The kernel has dimension " | result#1 | ".");
	    if result#2=="sur" then return ("Could not find an element of degree " | d | " such that multiplication is surjective in degree " | result#0 | ". The image has codimension " | result#1 | ".");
	    );
	);
    return true;
    )
    
    


--checkWLP: Kollar om en artinsk ring har WLP.
checkWLP=method()
checkWLP(QuotientRing):=(S)->(
    I:=trim ideal(S);
     if not isQuotientOf(PolynomialRing,S) then error "The argument must be a quotient of a polynomial ring.";
     if not isHomogeneous(I) then error "The defining ideal must be homogeneous";
     if not isArtinian(S) then error "The argument must be an Artinian ring.";
     f:=sum gens S;
     faildeg:=-1;
     faildim:=0;
     failtype:="";
     p:=numerator reduceHilbert hilbertSeries S;
     p=toZZT(p);
     T:=first gens ring p;
     h:=trunc hvec((1-T)*p);
     isWLEl:=(f)->(
	 v:=hvec numerator reduceHilbert hilbertSeries(S/ideal(f));
	 return compareHilb(v,h);
	 );
     if isMonomialIdeal I then (
	 result:=isWLEl(f);
	 if result===true then return true;
	 if result#2=="inj" then return ("Multiplication by any linear form is not injective in degree " | (result#0)-1 | ". The dimension of the kernel is " | result#1 | ".");
	 if result#2=="sur" then return ("Multiplication by any linear form is not surjective in degree " | (result#0)-1 | ". The codimension of the image is " | result#1 | ".");
	 );
     for i to 4 do (
	 result:=isWLEl(f);
    	 if result===true then return true;
	 if (result#0)-1>faildeg then (
	     faildeg=(result#0)-1;
	     faildim=result#1;
	     failtype=result#2;
	     );
	 f=random(1,S);
	);
    if failtype=="inj" then return ("Could not find a linear form such that multiplication is injective in degree "| faildeg | ". The kernel has dimension " | faildim | ".");
    if failtype=="sur" then return ("Could not find a linear form such that multiplication is surjective in degree "| faildeg | ". The image has codimension " | faildim | ".");
    )


--checkSLP: Kollar om en artinsk ring har SLP.
checkSLP=method()
checkSLP(QuotientRing):=(S)->(
    I:=trim ideal(S);
    if not isQuotientOf(PolynomialRing,S) then error "The argument must be a quotient of a polynomial ring.";
    if not isHomogeneous(I) then error "The defining ideal must be homogeneous.";
    if not isArtinian(S) then error "The argument must be an Artinian ring.";
    p:=numerator reduceHilbert hilbertSeries S;
    p=toZZT(p);
    T:= first gens ring p;
    t:=(degree p)#0;
    H:=for j from 1 to t list trunc hvec((1-T^j)*p);
    failpow:=-1;
    faildeg:=-1;
    faildim:=0;
    failtype:="";
    isSLEl:=(f)->(
    	for j from 1 to t do (
    	    v:=hvec numerator reduceHilbert hilbertSeries (S/ideal{f^j});
	    h:=H#(j-1);
	    result:=compareHilb(v,h);
    	    if not result===true then return ({j}| result);
    	    );
    	return true;);
    f:=sum gens S;
    if isMonomialIdeal(I) then (
	 result:=isSLEl(f);
	 if result===true then return true;
	 if result#3=="inj" then return ("Multiplication by the " | result#0 | "'th power of any linear form is not injective in degree " | (result#1)-(result#0) | ". The dimension of the kernel is " | result#2 | ".");
	 if result#3=="sur" then return ("Multiplication by the " | result#0 | "'th power of any linear form is not surjective in degree " | (result#1)-(result#0) | ". The codimension of the image is " | result#2 | ".");
	);
    for i to 4 do (
	result:=isSLEl(f);
	if result===true then return true;
	if result#1>failpow+faildeg then (
	    failpow=result#0;
	    faildeg=result#1-failpow;
	    faildim=result#2;
	    failtype=result#3;
	    );
       	f=random(1,S););
     if failtype=="inj" then return ("Could not find a linear form such that multiplication by its " | failpow | "'th power is injective in degree "| faildeg | ". The kernel has dimension " | faildim | ".");
    if failtype=="sur" then return ("Could not find a linear form such that multiplication by its " | failpow | "'th power is surjective in degree "| faildeg | ". The image has codimension " | faildim | ".");
     )
 
 

--hasFrobergProp: Tar en lista F med homogena polynom och kollar om de uppfyller Fröbergs förmodan. 
hasFrobergProp=method()
hasFrobergProp(List):=F->(
   if not same(apply(F,ring)) then error "The argument must be a list of elements of the same ring.";
   S:=ring F#0;
   if not isPolynomialRing(S) then error "The argument must be a list of elements of a polynomial ring.";
   J:=ideal F;
   if not isHomogeneous(J) then error "The argument must be a list of homogeneous polynomials.";
   deglist:=apply(F,f->(degree f)#0);
   n:=dim(S);
   A:=S/J;
   if not isArtinian(A) then (
       if length F >= n then return false;   
       p:= numerator hilbertSeries A;
       p=toZZT(p);
       T:=first gens ring p;
       return (p==product apply(deglist,d->(1-T^d)));
       );
   p=numerator reduceHilbert hilbertSeries A;
   p=toZZT(p);
   soc:=first degree p;
   I:=ideal apply(gens S, x->x^(soc+1));
   q:=numerator reduceHilbert hilbertSeries (S/I);
   q=toZZT(q);
   T=first gens ring q;
   h:=trunc hvec (product(apply(deglist,d->(1-T^d)))*q);
   v:=hvec p;
   return compareHilb(v,h)===true;
   )










beginDocumentation()
document { 
    Key => MaximalRankProperties,
    Headline => "A package for investigating the Lefschetz properties, the Maximal rank
    	property, and the Fröberg conjecture."	
	}
    
 document { 
     Key => {hasMaxRank, (hasMaxRank, RingElement)},
     Headline => "determines whether multiplication by a given homogeneous element has maximal rank in every
                  degree",
     Usage => "hasMaxRank f",
     Inputs => {
	 "f" => RingElement => "a homogeneous element in a graded artinian ring"},
     Outputs => { 
	 Boolean => {TT "true", " if multiplication by f has maximal rank in every degree"},
	 String => "giving the first degree in which multiplication by f fails to have maximal rank"
	 },
        EXAMPLE {
	 "R=QQ[x,y,z];",
	 "I=ideal(x^5,y^5,z^5,x*(y^2+z^2))",
	 "A=R/I;",
	 "hasMaxRank(x)",
	 "hasMaxRank(x+y+z)",
	 "hasMaxRank(x+2*y+z)"
	 }
	}

document { 
     Key => {checkWLP, (checkWLP, QuotientRing)},
     Headline => "determines whether an artinian algebra has the weak Lefschetz property",
     Usage => "checkWLP A",
     Inputs => {
	 "A" => QuotientRing => "an artinian quotient of a polynomial ring and a homogeneous ideal"},
     Outputs => { 
	 Boolean => {TT "true", " if a weak Lefschetz element was found"},
	 String => "giving the first degree in which it failed to find an element with maximal rank"
	 },
     {"The function looks for a weak Lefschetz element. If A is a monomial algebra it tries the linear form with all coefficients equal to 1. For monomial algebras, it is sufficient to try this element. If A is not a monomial algebra, it also tries four random linear forms. If it finds a weak Lefschetz element, it returns ", TT "true", ". If not, it returns a description of where it failed. Notice that this is not a proof that the algebra does not have the WLP, when A is not a monomial algebra."},
      EXAMPLE {
	 "R=ZZ/101[x,y,z]",
	 "I=ideal(x^5,y^5,z^5,x*y*z)",
	 "J=ideal(x^5,y^5,z^5)",
	 "checkWLP(R/I)",
	 "checkWLP(R/J)"
	 },
     EXAMPLE {
	 "R=QQ[x,y,z,w]",
	 "I=ideal( for i to 4 list (random(1,R))^3);",
	 "checkWLP(R/I)"
	 }
	}

document { 
     Key => {checkSLP, (checkSLP, QuotientRing)},
     Headline => "determines whether an artinian algebra has the strong Lefschetz property",
     Usage => "checkSLP A",
     Inputs => {
	 "A" => QuotientRing => "an artinian quotient of a polynomial ring and a homogeneous ideal"},
     Outputs => { 
	 Boolean => {TT "true", " if a strong Lefschetz element was found"},
	 String => "giving the first degree in which it failed to find an element with maximal rank"
	 },
     {"The function looks for a strong Lefschetz element. If A is a monomial algebra it tries the linear form with all coefficients equal to 1. For monomial algebras, it is sufficient to try this element. If A is not a monomial algebra, it also tries four random linear forms. If it finds a strong Lefschetz element, it returns ", TT "true", ". If not, it returns a description of where it failed. Notice that this is not a proof that the algebra does not have the SLP, when A is not a monomial algebra." },
       EXAMPLE {
	 "R=QQ[x,y,z];",
	 "I=ideal(x^5,y^5,z^5,x*y*z)",
	 "J=ideal(x^5,y^5,z^5)",
	 "checkSLP(R/I)",
	 "checkSLP(R/J)"
	 }
	}


document { 
     Key => {checkMRP, (checkMRP, QuotientRing)},
     Headline => "determines whether an artinian algebra has the Maximal rank property",
     Usage => "checkMRP A",
     Inputs => {
	 "A" => QuotientRing => "an artinian quotient of a polynomial ring and a homogeneous ideal"},
     Outputs => { 
	 Boolean => {TT "true", " if an element with maximal rank was found in every degree"},
	 String => "giving the first degree in which it failed to find an element with maximal rank"
	 },
    { "The function returns ", TT "true", " if it can find an element with maximal rank, in every degree. It tries five random forms in each degree.  If such elements can not be found, it returns a description of where it failed. Notice that this is not a proof that the algebra does not have the MRP."},
       EXAMPLE {
	 "R=QQ[x,y,z];",
	 "I=ideal(x^5,y^5,z^5,x*y*z)",
	 "J=ideal(x^5,y^5,z^5)",
	 "checkMRP(R/I)",
	 "checkMRP(R/J)"
	 }
	}

document {
    Key => {hasFrobergProp, (hasFrobergProp, List)},
    Headline => "determines whether a list of homogeneous polynomials satisfies the Fröberg conjecture",
    Usage => "hasFrobergProp L",
    Inputs => {
	"L" => List => "a list of homogeneous polynomials" },
    {"We say that a list L, of homogeneous polynomials, has the Fröberg property if the quotient of the polynomial ring and the ideal generated by the elements in L satisfied the Fröberg conjecture. The function returns ", TT "true", " if L has the Fröberg property, and ", TT "false", " otherwise. "},
    EXAMPLE {
	 "R=QQ[x,y,z];",
	 "L={(random(1,R))^3, (random(1,R))^3, (random(1,R))^4, (random(1,R))^4, (random(1,R))^4};",
	 "M={random(3,R), random(3,R), random(4,R), random(4,R), random(4,R)};",
	 "hasFrobergProp(L)",
	 "hasFrobergProp(M)"
	 }
     }
 
	
    

end 






