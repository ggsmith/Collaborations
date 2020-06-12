-- -*- coding: utf-8 -*-
------------------------------------------------------------------------------
-- Simplicial Complexes CODE
------------------------------------------------------------------------------
-- Copyright 2006--2020 Sorin Popescu, Gregory G. Smith, and Mike Stillman
--
-- This program is free software: you can redistribute it and/or modify it
-- under the terms of the GNU General Public License as published by the Free
-- Software Foundation, either version 3 of the License, or (at your option)
-- any later version.
-- This program is distributed in the hope that it will be useful, but WITHOUT
-- ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
-- FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
-- more details.
--
-- You should have received a copy of the GNU General Public License along
-- with this program.  If not, see <http://www.gnu.org/licenses/>.
------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- Basic features of the simplicial complex datatype
------------------------------------------------------------------------------
SimplicialComplex = new Type of HashTable
SimplicialComplex.synonym = "abstract simplicial complex"

-- 'facets' method defined in Polyhedra
facets SimplicialComplex := Matrix => D -> D.facets
-- older version of facets had an option 'useFaceClass'
-- TODO: how should we handle backwards compatiblity?

expression SimplicialComplex := D -> expression facets D
net SimplicialComplex := net @@ expression

ideal SimplicialComplex := Ideal => D -> ideal D.monomialIdeal
monomialIdeal SimplicialComplex := MonomialIdeal => D -> D.monomialIdeal
ring SimplicialComplex := PolynomialRing => D -> D.ring
coefficientRing SimplicialComplex := Ring => D -> coefficientRing ring D

dim SimplicialComplex := ZZ => (cacheValue symbol dim) (
    D -> max apply(first entries facets D, s -> # support(s)) - 1
    )
   
simplicialComplex = method()   
simplicialComplex List := SimplicialComplex => L -> (
    facetsList := select(L, r -> r =!= 0);
    -- need at least one facet to determine the ring   
    if # facetsList === 0 then 
        error "-- expected at least one facet";
    if not same apply(facetsList, class) then 
	error "-- expect all elements in the list to have same type";
    if class L#0 === Face then 
	facetsList = apply(facetsList, j -> product vertices j);
    S := ring (facetsList#0);
    G := matrix {{product gens S}};
    -- the monomialIdeal constructor verifies that the elements all lie in the
    -- same commutative polynomial ring
    I := monomialIdeal contract (matrix{facetsList}, G);
    -- remove any non-maximal faces from 'facetsList'
    I = monomialIdeal mingens I;
    -- contracting with G complements the support of the monomials
    F := sort contract (gens I, G);
    -- Alexander duality for monomial ideals in part of the 'Core'
    --   the dual method checks that I is squarefree
    I = dual I;
    new SimplicialComplex from {
	symbol ring           => S,
	symbol monomialIdeal  => I,
	symbol facets         => F,
	symbol cache          => new CacheTable
	}
    )
simplicialComplex MonomialIdeal := SimplicialComplex => I -> (
    S := ring I;
    -- Alexander duality for monomial ideals in part of the 'Core'
    --   the dual method checks that I is squarefree    
    J := dual I;
    -- the void complex is the special case that has no facets
    if J == 0 then (
	return new SimplicialComplex from {
	    symbol ring           => S,
	    symbol monomialIdeal  => monomialIdeal 1_S,
	    symbol facets         => map(S^1, S^0, 0),
	    symbol cache          => new CacheTable
	    }
	);    
    G := matrix {{product gens S}};
    -- contracting with G complements the support of the monomials    
    F := sort contract (gens J, G);
    new SimplicialComplex from {
	symbol ring           => S,
	symbol monomialIdeal  => I,
	symbol facets         => F,
	symbol cache          => new CacheTable
	}       
    )

isWellDefined SimplicialComplex := Boolean => D -> (
    -- CHECK DATA STRUCTURE
    -- check keys
    K := keys D;
    expectedKeys := set {symbol ring, symbol monomialIdeal, symbol facets, symbol cache};
    if set K =!= expectedKeys then (
	if debugLevel > 0 then (
	    added := toList (K - expectedKeys);
	    missing := toList (expectedKeys - K);
	    if # added > 0 then 
	        << "-- unexpected key(s): " << toString added << endl;
	    if # missing > 0 then 
	        << "-- missing key(s): " << toString missing << endl;
	    );
	return false
	);
    -- check types
    if not instance (D.ring, PolynomialRing) then (
	if debugLevel > 0 then 
	    << "-- expected `.ring' to be a PolynomialRing" << endl;
	return false
	);
    if not instance (D.monomialIdeal, MonomialIdeal) then (
	if debugLevel > 0 then 
	    << "-- expected `.monomialIdeal' to be a MonomialIdeal" << endl;
	return false
	);
    if ring D.monomialIdeal =!= D.ring then (
	if debugLevel > 0 then 
	    << "-- expected the ring of `.monomialIdeal' to be `.ring'" << endl;
	return false
	);     
    if not instance (D.facets, Matrix) then (
	if debugLevel > 0 then 
	    << "-- expected `.facets' to be a Matrix" << endl;
	return false
	);        
    if ring D.facets =!= D.ring then (
	if debugLevel > 0 then 
	    << "-- expected the ring of `.facets' to be `.ring'" << endl;
	return false
	); 
    if not instance (D.cache, CacheTable) then (
    	if debugLevel > 0 then 
	    << "-- expected `.cache' to be a CacheTable" << endl;
    	return false
	);     
    -- CHECK MATHEMATICAL STRUCTURE
    -- check whether the monomialIdeal is square free
    if not isSquareFree D.monomialIdeal then (
	if debugLevel > 0 then 
	    << "-- expected `.monomialIdeal' to be square free" << endl;
	return false
	);   
    -- check whether the facets correspond to the monomialIdeal
    S := ring D;
    G := matrix {{product gens S}};
    if D.facets =!= sort contract (gens dual monomialIdeal D, G) then (
	if debugLevel > 0 then
	    << "-- expected '.facets' to list the facets corresponding to `.monomialIdeal' << "endl;
    	return false
	);	    
    true
    )


------------------------------------------------------------------------------
-- constructors for classic examples
------------------------------------------------------------------------------
bartnetteSphereComplex = method()
bartnetteSphereComplex PolynomialRing := SimplicialComplex => S -> (
    if numgens S < 8 then 
	error "-- expected a polynomial ring with at least 8 generators";
    simplicialComplex {S_0*S_1*S_2*S_6, S_0*S_1*S_2*S_7, S_0*S_1*S_3*S_4,
      S_0*S_1*S_3*S_6, S_0*S_1*S_4*S_7, S_0*S_2*S_3*S_5, S_0*S_3*S_4*S_7,
      S_0*S_3*S_5*S_6, S_1*S_2*S_4*S_5, S_1*S_2*S_4*S_6, S_1*S_2*S_5*S_7,
      S_1*S_3*S_4*S_6, S_1*S_4*S_5*S_7, S_0*S_2*S_3*S_7, S_0*S_2*S_5*S_6,
      S_2*S_4*S_5*S_6, S_2*S_3*S_5*S_7, S_3*S_4*S_5*S_6, S_3*S_4*S_5*S_7}
    )

simplexComplex = method()
simplexComplex (ZZ, PolynomialRing) := SimplicialComplex => (n, S) -> (
    if n === -1 then 
	return simplicialComplex {1_S};
    if n < -1 then 
        error "-- expected integer greater than -1";
    if numgens S < n + 1 then 
	error "-- expected a polynomial ring with at least " << n+1 << " generators";
    simplicialComplex {product(n+1, i -> S_i)}
    )

---- inspired by Sage math 
--   https://doc.sagemath.org/html/en/reference/homology/sage/homology/examples.html
-- TODO: add brucknerGrunbaumComplex
-- TODO: add chessboardComplex
-- TODO: add dunceHatComplex
-- TODO: add kleinBottleComplex
-- TODO: add realProjectiveSpaceComplex (ZZ == dimension)
-- TODO: add surfaceComplex (ZZ == genus)


------------------------------------------------------------------------------
-- more advanced constructors 
------------------------------------------------------------------------------
dual SimplicialComplex := SimplicialComplex => {} >> opts -> D -> (
    -- Alexander duality for monomial ideals in part of the 'Core'    
    simplicialComplex dual monomialIdeal D)


link = method()
link (SimplicialComplex, RingElement) := SimplicialComplex => (D,f) -> (
     simplicialComplex monomialIdeal((ideal support f) + ((ideal D) : f)))



lcmMonomials = (L) -> (
     R := ring L#0;
     x := max \ transpose apply(L, i -> first exponents i);
     R_x)

lcmM = (L) -> (
-- lcmM finds the lcm of a list of monomials; the quickest method Sorin knows
    m := intersect toSequence (L/(i -> monomialIdeal(i)));
    m_0)




---------------------------------------
-- frame procedure for original "faces" now renamed
-- (unchanged) to facesM, which has the option
-- to return also a list of Faces
-- added by Janko

--faces = method(Options=>{useFaceClass=>false})

-- 'faces' method defined in Polyhedra
faces (ZZ, SimplicialComplex) := Matrix => (r, D) -> (
    -*
    if opt.useFaceClass then (
   	matrixToFaces(facesM(r,D))
	) 
    *-
    facesM(r,D)
    )

-- list of list of all faces
faces SimplicialComplex := HashTable => D -> (
    j := 0;
    f := j -> faces(j, D);
    new HashTable from toList apply(-1..dim D,j->j=>f j))


-------------------------------------------------
-- convert Matrix with Monomials to List of Faces
-- added by Janko

matrixToFaces = method()
matrixToFaces Matrix := M -> (
    if M == 0 then return {};
    apply ((entries M)#0, face)
    )


facesM = method()
facesM (ZZ, SimplicialComplex) := (r,D) -> (
    R := ring D;
    if not D.cache.?faces then (
	D.cache.faces = new MutableHashTable;
	B := (coefficientRing R) (monoid [gens R, SkewCommutative=>true]);
	D.cache.faces.ideal = substitute(ideal D,B);
	);
    if r < -1 or r > dim D then matrix(R, {{}})
    else (
	if not D.cache.faces#?r then (
	    J := D.cache.faces.ideal;
	    D.cache.faces#r = substitute(matrix basis(r+1,coker gens J), vars R));
	D.cache.faces#r
     	)
    )


--- kludge to access parts of the 'Core'
raw = value Core#"private dictionary"#"raw";
rawIndices = value Core#"private dictionary"#"rawIndices";
rawKoszulMonomials = value Core#"private dictionary"#"rawKoszulMonomials";



boundary = method()
boundary (ZZ,SimplicialComplex) := (r,D) -> (
     R := ring D;
     if D.cache.?labels then (
	  m1 := D.cache.labels#r;
	  m2 := D.cache.labels#(r-1);
	  Sext := D.cache.labels.ring;
     	  ones := D.cache.labels.ones;
	  S := target ones;
	  F := source map(S^1,, ones m2);
	  bd := ones map(Sext, rawKoszulMonomials(numgens Sext, raw m2,raw m1));
	  bd = map(F,,bd);
	  bd
	  )
     else (
     	  b1 := faces(r,D);
     	  b2 := faces(r-1,D);
     	  ones = map(coefficientRing R,R, toList(numgens R:1));
     	  ones map(R, rawKoszulMonomials(numgens R,raw b2,raw b1))
     	  )
     )

chainComplex SimplicialComplex := (D) -> (
    d := dim D;
    C := if d < -1 then (ring D)^0[-1]
    else if d === -1 then (ring D)^1
    else chainComplex apply(0..d, r -> boundary(r,D));
    if D.cache.?labels then C[0] else C[1]
    )

-------- Labelled code ---------------------
makeLabels = (D,L,i) -> (
    -- D is a simplicial complex
    -- L is a list of monomials 
    -- i is an integer
    F := first entries faces(i,D);
    Sext := D.cache.labels.ring;
    if #F == 0 
    then matrix{{1_Sext}} 
    else
    matrix {apply(F, m -> (
		s := rawIndices raw m;
		lcmM L_s
		))}
     )

L=null	  						    -- used as a key below

label = method()
label (SimplicialComplex, List) := (D,L) -> (
    if #L === 0 then 
    	remove(D.cache, symbol labels)
    else (    
	D.cache.labels = new MutableHashTable;
	S := ring(L#0);
	M := monoid [Variables=>#L]; 
	Sext := S M;
	D.cache.labels.ring = Sext;
	L = apply(#L, i -> L_i * Sext_i);
	D.cache.labels.L = L;
	D.cache.labels.ones = map(S, Sext, toList(#L:1_S));
	D.cache.labels#-1 = matrix{{1_Sext}};
	for i from 0 to dim D do
	    D.cache.labels#i = makeLabels(D,L,i);
	)
    )

simplicialChainComplex = method()
simplicialChainComplex (List,SimplicialComplex) := (L, D) -> (
     label(D,L);
     d := dim D;
     C := chainComplex(apply(0..d, r -> boundary(r,L,D)));
     -- label(D,{}) -- removes cached labels
     C
     )

homology(ZZ,SimplicialComplex,Ring) := Module => opts -> (i,Delta,R) -> (
     homology(i, chainComplex Delta ** R))
homology(ZZ,SimplicialComplex) := Module => opts -> (i,Delta) -> (
     homology(i, chainComplex Delta))
homology(Nothing,SimplicialComplex,Ring) :=
homology(SimplicialComplex,Ring) := GradedModule => opts -> (Delta,R) -> (
     homology(chainComplex Delta ** R))
homology(Nothing,SimplicialComplex) :=
homology(SimplicialComplex) := GradedModule => opts -> Delta -> (
     homology(chainComplex Delta))

------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-- 20/07/2018 Lorenzo: some changes

-- Fixed fVector to make it work also when the underlying ring is  multigraded.
-- Added the option Flag to return the finer f-vector for the multigraded case.

-- fVector = method(TypicalValue => List, Options => {Flag => false})
fVector SimplicialComplex := D -> (
    I := ideal D;
    -*
    if not opts.Flag then (
	S := newRing(ring D, Degrees => {#(gens ring D):1});
	maptoS := map(S, ring D);
	I = maptoS(I);
     );
     *-	   
     N := poincare cokernel generators I;
     -*
     if opts.Flag then (
     	 if not isBalanced(D) then (
             stderr << "-- the grading does not correspond to a proper d-coloring." << endl;
             return new HashTable from {}
     	     );
     	 R := newRing(ring N, Degrees => apply(gens ring N, g -> apply(gens ring N, f -> if index(f) == index(g) then 1 else 0)));
         maptoR := map(R, ring N);
         N = maptoR(N);
     	 );
     *-	   
     if N == 0 then (
         new HashTable from {-1 => 0}
     )
     else (
         d := dim D + 1;
         apply(gens ring N, t -> while 0 == substitute(N, t => 1) do N = N // (1-t));
         supp := apply(flatten entries monomials(N), m -> degree m);
         allsubsets := apply(subsets(#(gens ring N)), s -> apply(toList(0..#(gens ring N)-1), l -> if member(l,s) then 1 else 0));
         flagh := L -> coefficient((flatten entries monomials part(L, N))#0, part(L, N));
     	 flagf := M -> sum(supp, m -> if all(m,M, (i,j) -> j >= i) then flagh(m) else 0);
     	 h := j -> sum(supp, s -> if sum(s)==j then flagh(s) else 0);
     	 f := j -> sum(0..j+1, i -> binomial(d-i, d-j-1)*h(i));
	 -*
     	 if opts.Flag then (
             new HashTable from apply(allsubsets, j -> j => flagf(j))
     	     )
	 else
	 *-
     	 new HashTable from prepend(-1=>1, apply(toList(0..d-1), j -> j => f(j)))
     	 )
     )

-- Check if the grading on the ring defines a proper (dim(D)+1)-coloring on
-- D. Used by fVector. Not exported.
isBalanced = (D) -> (
     d := dim D +1;
     m := true;
     if not d == #(degree first gens ring D) then (
         m = false;
     );
     apply(flatten entries faces(1,D), f -> if max(degree f) > 1 then m = false);
     return m;
     );

-- helper functions for algebraicShifting. Not exported.
shiftMonomial = (m) -> (
    variables := flatten entries vars ring m;
    D := unique degrees ring m;
    P := apply(D, d -> flatten entries basis(d, ring m));
    f := (Q, v) -> {position(Q, q -> member(v, q)), position(Q_(position(Q, q -> member(v,q))), b -> b == v)};
    multisupp := MultiSupp(m);
    deg := degree(m);
    auxlist := flatten apply(deg, d -> toList(0..d-1));
    sm := 1;
    apply(auxlist, multisupp, (i, j) -> sm = sm * (P_((f(P, j))_0))_((f(P, j))_1+i) );
    return sm
    );

MultiSupp = (m) -> (
    multisupp := {};
    while m != 1 do (multisupp = append(multisupp, (support(m))_0);
        m=m//((support(m))_0););
    return multisupp
    );


shift = (I) -> (
    shiftgens := apply( I_*, g -> shiftMonomial(g));
    return ideal shiftgens
    );


-- Compute the algebraic shifting of a simplicial complex and the colored shifting if the ring is multigraded.
algebraicShifting = method (Options => {Multigrading => false})
algebraicShifting SimplicialComplex := opts -> S -> (
    if not opts.Multigrading then (
    R := newRing(ring S, Degrees => {#(gens ring S):1});
    f := map(R, ring S);
    g := map(ring S, R);
    J := g(shift(gin(f(ideal S), Multigraded => opts.Multigrading)));
    return simplicialComplex monomialIdeal J
    )
    else (
        sI := monomialIdeal shift(gin(ideal S, Multigraded => opts.Multigrading));
    return simplicialComplex sI
    )
    )
-- Compute the i-th skeleton of a simplicial complex
--skeleton = method ()
-- method defined in the Polyhedra package
skeleton (ZZ, SimplicialComplex) := SimplicialComplex => (n, S) -> (
     simplicialComplex(flatten entries faces(n,S))
     )

-- Compute the star w.r.t. a face
star = method ()
star (SimplicialComplex, RingElement) := (S, f) -> (simplicialComplex(monomialIdeal(S):monomialIdeal(f)))

-- The simplicial join of two simplicial complexes defined over different rings
joinSimplicial = method ()
joinSimplicial (SimplicialComplex, SimplicialComplex) := (A, B) -> (
     T := tensor(ring A, ring B);
     f := map(T, ring A);
     g := map(T, ring B);
     return simplicialComplex(monomialIdeal(f(ideal(A))+g(ideal(B))));
     )

SimplicialComplex * SimplicialComplex := joinSimplicial


boundary SimplicialComplex := (D) -> (
     F := first entries facets D;
     L := flatten apply(F, m -> apply(support m, x -> m//x));
     if #L === 0 then 
         simplicialComplex monomialIdeal (1_(ring D))
     else
     	 simplicialComplex L
     )


-- method defined in the Polyhedra package
isPure SimplicialComplex := Boolean => (D) -> (
     F := first entries facets D;
     L := unique apply(F, m -> # support m);
     #L <= 1
     )


--------------------------------------------------------------------------
-- Buchberger complex of a monomial ideal (aka improved Taylor complex) --
-- (see Eisenbud-Hosten-Popescu)          
--------------------------------------------------------------------------

lcmMRed = method()
lcmMRed (List) := (L) -> (
-- lcmMRed finds the reduced lcm of a list of monomials
    m := intersect toSequence (L/(i -> monomialIdeal(i)));
    m_0//(product support m_0))

faceBuchberger = (m, L) -> (
-- true iff the monomial m (in #L vars) is in the Buchberger complex
     x := rawIndices raw m;
     mon := lcmMRed(L_x);
     all(L, n -> mon//n == 0))

buchbergerComplex = method()
buchbergerComplex(List,Ring) := (L,R) -> (
     P := ideal apply(gens R, x -> x^2);
     nonfaces := {};
     d := 1;
     while (L1 := flatten entries basis(d,coker gens P); #L1 > 0) do (
	  L1 = select(L1, m -> not faceBuchberger(m,L));
	  << "new nonfaces in degree " << d << ": " << L1 << endl;	  
	  nonfaces = join(nonfaces,L1);
	  if #nonfaces > 0 then
	      P = P + ideal nonfaces;
	  d = d+1;
          );
     simplicialComplex monomialIdeal matrix(R, {nonfaces})
     )

buchbergerComplex(MonomialIdeal) := (I) -> (
     buchbergerComplex(flatten entries gens I, ring I))

--------------------------------------------------------------------------
-- Lyubeznik/Superficial type resolutions                               --
-- (see Eisenbud-Hosten-Popescu)                                        --
--------------------------------------------------------------------------

isSuperficial = method()
isSuperficial List := (L) -> (
-- isSuperficial cheks if a list of monomials is already superficially oredred
-- that is every monomial in the list does not strictly divide the lcm of the previous ones
     R := ring(L_0);
     all(1..#L-1, i-> (previous:=lcmMonomials(take(L,i)); 
	       (previous//product(support previous))//(L_i) == 0))
     )

faceLyubeznik = (m,L) -> (
-- true iff the monomial m (in #L vars) defines a face in the Lyubeznik complex
     x := rawIndices raw m;
     all(0..#L-1, i -> (L1:=L_(select(x, j->j>i));
	       if (#L1==0) then true else lcmMonomials(L1)//L_i == 0)))

lyubeznikComplex = method()
lyubeznikComplex(List,Ring) := (L,R) -> (
     if not isSuperficial(L) then error "expected a superficially ordered list of monomials";
     P := ideal apply(gens R, x -> x^2);
     nonfaces := {};
     d := 1;
     while (L1 := flatten entries basis(d,coker gens P); #L1 > 0) do (
	  L1 = select(L1, m -> not faceLyubeznik(m,L));
	  << "new nonfaces in degree " << d << ": " << L1 << endl;	  
	  nonfaces = join(nonfaces,L1);
	  if #nonfaces > 0 then
	      P = P + ideal nonfaces;
	  d = d+1;
          );
     simplicialComplex monomialIdeal matrix(R, {nonfaces})
     )

lyubeznikComplex(MonomialIdeal) := (I) -> (
     lyubeznikComplex(flatten entries gens I, ring I))


faceSuperficial = (m,L) -> (
-- true iff the monomial m (in #L vars) defines a face in the Superficial complex
     x := rawIndices raw m;
     R := ring(L_0);
     all(0..#L-1, n -> (smallerMons := L_(select(x, j->j<n+1)); 
	                largerMons := L_(select(x, j->j>n));
	                smallerLcmRed := if (#smallerMons==0) then 1_R else lcmMRed(smallerMons);
			lcmMonomials(join({smallerLcmRed}, largerMons))//L_n==0)))
   


superficialComplex = method()
superficialComplex(List, Ring) := (L,R) -> (
     if not isSuperficial(L) then error "expected a superficially ordered list of monomials";
     P := ideal apply(gens R, x -> x^2);
     nonfaces := {};
     d := 1;
     while (L1 := flatten entries basis(d,coker gens P); #L1 > 0) do (
	  L1 = select(L1, m -> not faceSuperficial(m,L));
	  << "new nonfaces in degree " << d << ": " << L1 << endl;	  
	  nonfaces = join(nonfaces,L1);
	  if #nonfaces > 0 then
	      P = P + ideal nonfaces;
	  d = d+1;
          );
     simplicialComplex monomialIdeal nonfaces
     )

superficialComplex(MonomialIdeal) := (I) -> (
     superficialComplex(flatten entries gens I, ring I))


-----------------------------------------------------------------------
-- Defining a class Face
-- to be used in other package in particular in the KustinMiller package
-- additions by Janko

Face = new Type of MutableHashTable

-- vertices of a face
-- vertices=method()

-- 'vertices' method defined in 'Polyhedra" package
vertices Face := F -> F.vertices

-- pretty print
net Face := (f)-> (
v:=vertices(f);
if #v==0 then return(net({}));
horizontalJoin(apply(v,j->net(j)|net(" "))))

-- after print
Face#{Standard,AfterPrint} = m -> (
  n:=#vertices(m);
  if n==0 then vstr:="empty face";
  if n==1 then vstr="face with "|n|" vertex";
  if n>1 then vstr="face with "|n|" vertices";
      << endl;
      << concatenate(interpreterDepth:"o") << lineNumber << " : "
      << vstr|" in "|net(ring m)
      << endl;)

-- dimension
dim Face := F->-1+#(vertices F)

-- ring of a face
ring Face :=F->F.ring;

-- construct a face from a List of vertices
face=method()
face(List):= (L)-> new Face from {symbol vertices => L, symbol ring=> ring L#0}
face(List,PolynomialRing):= (L,R)-> new Face from {symbol vertices => L, symbol ring=>R}

-- construct a face from a monomial
face(RingElement):= (m)-> face(support m,ring m)

-- compare two faces
Face == Face := (F,G)->(
(#(vertices F))==(#(vertices G)) and set vertices F === set vertices G)

-- test if a face is a subface of another
isSubface=method()
isSubface(Face,Face):=(F,G)->(
isSubset(set vertices F,set vertices G))

-- test if a face is a face of a complex
isFaceOf = method()
isFaceOf (Face,SimplicialComplex) := (F,C) -> (
    fc := facets(C);    
    #(select(1,fc, G -> isSubface(F,G)))>0
    )


-- substitute a face to another ring
substitute(Face,PolynomialRing):=(F,R)->(
v:=vertices(F);
face(apply(v,j->sub(j,R)),R))

-- substitute a complex to another ring
substitute(SimplicialComplex,PolynomialRing):=(C,R)->(
simplicialComplex((entries sub(C.facets,R)))#0)


-*
installPackage "SimplicialComplexes"
R = QQ[a..e]
D = simplicialComplex monomialIdeal(a*b*c*d*e)
substitute(D,R)
F=(faces(1,D,useFaceClass=>true))#0
isFaceOf(F,D)
*-
