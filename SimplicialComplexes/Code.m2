-- -*- coding: utf-8 -*-
------------------------------------------------------------------------------
-- Simplicial Complexes CODE
------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- Basic features of the simplicial complex datatype
------------------------------------------------------------------------------
SimplicialComplex = new Type of HashTable
SimplicialComplex.synonym = "abstract simplicial complex"

-- 'facets' method defined in Polyhedra
facets SimplicialComplex := Matrix => D -> D.facets

expression SimplicialComplex := D -> (expression simplicialComplex) expression facets D
net SimplicialComplex := net @@ expression
texMath SimplicialComplex := D -> texMath expression D

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
simplicialComplex Matrix := SimplicialComplex => f -> (
    if numrows f =!= 1 then error "-- expected a matrix with 1 row";
    simplicialComplex first entries f
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
simplexComplex = method()
simplexComplex (ZZ, PolynomialRing) := SimplicialComplex => (n, S) -> (
    if n === -1 then 
	return simplicialComplex {1_S};
    if n < -1 then 
        error "-- expected integer greater than -1";
    if numgens S < n + 1 then 
	error concatenate("-- expected a polynomial ring with at least ", 
	    toString(n+1), " generators");
    simplicialComplex {product(n+1, i -> S_i)}
    )


-- Masahiro Hachimori created a library of interesting simplicial complexes; see
--   http://infoshako.sk.tsukuba.ac.jp/~hachi/math/library/index_eng.html
hachimoriFile := currentFileDirectory | "hachimoriLibrary.txt"
hachimoriTable := hashTable apply (lines get hachimoriFile, x -> (
    	if notify then stderr << "--loading file " << hachimoriFile << endl;
    	value x
	)
    )

bartnetteSphereComplex = method()
bartnetteSphereComplex PolynomialRing := SimplicialComplex => S -> (
    if numgens S < 8 then 
	error "-- expected a polynomial ring with at least 8 generators";
    simplicialComplex apply(hachimoriTable#-1, f -> product(f, i -> S_i))
    )

poincareSphereComplex = method()
poincareSphereComplex PolynomialRing := SimplicialComplex => S -> (
    if numgens S < 16 then
        error "-- expected a polynomial ring with at least 16 generators";    
    simplicialComplex apply(hachimoriTable#0, f -> product(f, i -> S_i))
    )

nonPiecewiseLinearSphereComplex = method()
nonPiecewiseLinearSphereComplex PolynomialRing := SimplicialComplex => S -> (
    if numgens S < 18 then
        error "-- expected a polynomial ring with at least 18 generators";    
    simplicialComplex apply(hachimoriTable#1, f -> product(f, i -> S_i))
    )

rudinBallComplex = method()
rudinBallComplex PolynomialRing := SimplicialComplex => S -> (
    if numgens S < 14 then
        error "-- expected a polynomial ring with at least 14 generators";    
    simplicialComplex apply(hachimoriTable#5, f -> product(f, i -> S_i))
    )

grunbaumBallComplex = method()
grunbaumBallComplex PolynomialRing := SimplicialComplex => S -> (
    if numgens S < 14 then
        error "-- expected a polynomial ring with at least 14 generators";    
    simplicialComplex apply(hachimoriTable#6, f -> product(f, i -> S_i))
    )

zieglerBallComplex = method()
zieglerBallComplex PolynomialRing := SimplicialComplex => S -> (
    if numgens S < 10 then
        error "-- expected a polynomial ring with at least 10 generators";    
    simplicialComplex apply(hachimoriTable#7, f -> product(f, i -> S_i))
    )

dunceHatComplex = method()
dunceHatComplex PolynomialRing := SimplicialComplex => S -> (
    if numgens S < 8 then
        error "-- expected a polynomial ring with at least 8 generators";    
    simplicialComplex apply(hachimoriTable#12, f -> product(f, i -> S_i))
    )

bjornerComplex = method()
bjornerComplex PolynomialRing := SimplicialComplex => S -> (
    if numgens S < 6 then
        error "-- expected a polynomial ring with at least 6 generators";    
    simplicialComplex apply(hachimoriTable#13, f -> product(f, i -> S_i))
    )



-- Frank Lutz has enumerated all 2 and 3-manifolds with less than 10 vertices;
-- see http://page.math.tu-berlin.de/~lutz/stellar/3-manifolds.html
small2ManifoldsFile := currentFileDirectory | "small2ManifoldsLibrary.txt"
small210ManifoldsFile := currentFileDirectory | "small210ManifoldsLibrary.txt"
small3ManifoldsFile := currentFileDirectory | "small3ManifoldsLibrary.txt"
smallManifoldsTable := memoize((d,v) -> (
	local manifoldsFile;
	if (d === 2 and v < 10) then manifoldsFile = small2ManifoldsFile
	else if (d === 2 and v === 10) then manifoldsFile = small210ManifoldsFile
	else if d === 3 then manifoldsFile = small3ManifoldsFile;
	if notify then stderr << "--loading file " << manifoldsFile << endl;
	hashTable apply( lines get manifoldsFile, x -> (
		x = value x;
        	(x#0,x#1) => x#2
		)
	    )
	)
    );
smallManifold = method()
smallManifold (ZZ,ZZ,ZZ,PolynomialRing) := SimplicialComplex => (d,v,i,S) -> (
    if d < 2 or d > 3 then
    	error "-- expected dimension two or three";
    if v < 4 or i < 0 then
        error "-- expected at least four vertices or nonnegative index";
    if d === 2 and v === 4 and i > 0 then
    	error "-- there is only one 2-manifold with four vertices.";
    if d === 2 and v === 5 and i > 0 then
    	error "-- there is only one 2-manifold with five vertices.";
    if d === 2 and v === 6 and i > 2 then
    	error "-- there are only three 2-manifolds with six vertices.";
    if d === 2 and v === 7 and i > 8 then
    	error "-- there are only nine 2-manifolds with seven vertices.";
    if d === 2 and v === 8 and i > 42 then
    	error "-- there are only 43 2-manifolds with eight vertices.";
    if d === 2 and v === 9 and i > 654 then
    	error "-- there are only 655 2-manifolds with nine vertices.";
    if d === 2 and v === 10 and i > 42425 then
    	error "-- there are only 42426 2-manifolds with ten vertices.";
    if d === 3 and v === 5 and i > 0 then
    	error "-- there is only one 3-manifold with five vertices.";
    if d === 3 and v === 6 and i > 1 then
    	error "-- there are only two 3-manifolds with six vertices.";
    if d === 3 and v === 7 and i > 4 then
    	error "-- there are only five 3-manifolds with seven vertices.";
    if d === 3 and v === 8 and i > 38 then
    	error "-- there are only 39 3-manifolds with eight vertices.";
    if d === 3 and v === 9 and i > 1296 then
    	error "-- there are only 1297 3-manifolds with nine vertices.";
    if d === 3 and v === 10 then
    	error "-- the database for 3-manifolds with ten vertices hasn't been included yet.";
    if v > 10 then 
        error "-- database doesn't include manifolds with more than ten vertices";
    if numgens S < v then 
        error ("-- expected a polynomial ring with at least " | toString v | " generators");
    -- Since Frank Lutz starts counting at 1 instead of 0, there is
    -- some appropriate index shifting.
    simplicialComplex apply((smallManifoldsTable(d,v))#(v,i+1), f -> product(f, i -> S_(i-1)))
    )


---- inspired by Sage math 
--   https://doc.sagemath.org/html/en/reference/homology/sage/homology/examples.html
-- TODO: add brucknerGrunbaumComplex
-- TODO: add chessboardComplex
-- TODO: add kleinBottleComplex
-- TODO: add realProjectiveSpaceComplex (ZZ == dimension)
-- TODO: add surfaceComplex (ZZ == genus)



------------------------------------------------------------------------------
-- more advanced constructors 
------------------------------------------------------------------------------
prune SimplicialComplex := SimplicialComplex => opts -> D -> (
    V := vertices D;
    if gens ring D === V then return D;
    R := (coefficientRing D)(monoid[V]);
    if dim D < -1 then return simplicialComplex monomialIdeal(1_R);
    if dim D === 1 then return simplicialComplex {1_R};
    simplicialComplex for x in first entries facets D list (
	if sum first exponents x =!= 1 then substitute(x, R) else continue)
    )

inducedSubcomplex = method()
inducedSubcomplex (SimplicialComplex,List) := SimplicialComplex => (D, V) -> (
    if any(V, v -> not member(v, vertices D)) then 
	error "expected verticies of the simplicial complex";
    S := ring D;
    phi := map(S, S, for x in gens S list if member(x, V) then x else 1_S);
    -- although map(D, phi) is not a well-defined simplicial map, its image is
    -- nevertheless the induced complex
    image map(D, phi)
    )

dual SimplicialComplex := SimplicialComplex => {} >> opts -> D -> (
    -- Alexander duality for monomial ideals in part of the 'Core'    
    simplicialComplex dual monomialIdeal D)

link = method()
link (SimplicialComplex, RingElement) := SimplicialComplex => (D, f) -> (
    if isUnit f then return D;
    simplicialComplex ((monomialIdeal support f) + (monomialIdeal D : monomialIdeal f))
    )

-- 'skeleton' method defined in the `Polyhedra' package
skeleton (ZZ, SimplicialComplex) := SimplicialComplex => (n, D) -> (
    S := ring D;
    if n < -1 then return simplicialComplex monomialIdeal 1_S;
    if n === -1 then return simplicialComplex {1_S};
    if n >= dim D then return D;
    simplicialComplex matrix {apply(toList(0..n), i -> faces(i,D))}
    )

star = method ()
star (SimplicialComplex, RingElement) := (S, f) -> (simplicialComplex(monomialIdeal(S):monomialIdeal(f)))

-- The simplicial join of two simplicial complexes defined over different rings 
SimplicialComplex * SimplicialComplex := (D, D') -> (
     S := ring D ** ring D';
     fromD := map(S, ring D);
     fromD' := map(S, ring D');
     simplicialComplex monomialIdeal(fromD ideal D + fromD' ideal D')
     )

wedge = method(Options => true);
wedge (SimplicialComplex, SimplicialComplex, RingElement, RingElement) := SimplicialComplex => {Variables => {}} >> opts -> (D,E,u,v) -> (
    if not coefficientRing D === coefficientRing E then 
        error "expected the simplicial complexes to have the same coefficient rings";
    if not member(u, vertices D) or not member(v,vertices E) then 
        error ("expected " | toString u | " to be a vertex in " | toString D);
    if not member(u, vertices D) or not member(v,vertices E) then 
        error ("expected " | toString v | " to be a vertex in " | toString E);  
    RD := ring D;
    nD := numgens RD;
    RE := ring E;  
    nE := numgens RE;
    RW := if # opts.Variables > 0 then (
	      n := nD + nE - 1;
	      if # opts.Variables < n then
	          error ("expected the optional list to have at least " | toString n | " variables");
              (coefficientRing RD)(monoid[opts.Variables])
	      ) 
    	  else (coefficientRing RD)(monoid[join(gens RD, delete(v, gens RE))]);
    uIndex := position(gens RD, x -> x == u);
    vIndex := position(gens RE, y -> y == v);
    includeD := map(RW, RD, (gens RW)_{0..nD-1});
    includeE := map(RW, ring E, for i to nE - 1 list (
	            if i < vIndex then RW_(nD + i)
	            else if i == vIndex then RW_uIndex
	            else RW_(nD + i - 1))
		);
    facetsD := first entries includeD facets D;
    facetsE := first entries includeE facets E;
    simplicialComplex(facetsD | facetsE)
    )

------------------------------------------------------------------------------
-- basic properties and invariants
------------------------------------------------------------------------------

-- 'vertices' method is defined in 'Polyhedra" package
vertices SimplicialComplex := D -> (
    if dim D < 0 then {}
    else support product first entries facets D
    )
-- vertices Face := F -> F.vertices


-- 'faces' method defined in Polyhedra
faces (ZZ, SimplicialComplex) := Matrix => (i, D) -> (
    S := ring D;
    if not D.cache.?faces then (
	D.cache.faces = new MutableHashTable;
	E := (coefficientRing S)(monoid[gens S, SkewCommutative => true]);
	phi := map(E, S, gens E);
	J := phi(ideal D);
	D.cache.faces.ring = E/J;
	);
    if not D.cache.faces#?i then (
    	D.cache.faces#i = if dim D < -1 or i < -1 or i > dim D then 
	    matrix(S, {{}})
    	else if i === -1 then matrix {{1_S}}
    	else (
	    R := D.cache.faces.ring;
	    sub(matrix basis(i+1, R), vars S)
	    )
	);
    D.cache.faces#i
    )
faces SimplicialComplex := HashTable => D -> (
    hashTable apply(toList(-1..dim D), i -> i => faces(i, D))
    )

-- method defined in the Polyhedra package
isPure SimplicialComplex := Boolean => D -> (
     F := first entries facets D;
     L := unique apply(F, m -> # support m);
     #L <= 1
     )

-- 'fVector' method defined in Polyhedra
fVector SimplicialComplex := List => D -> (
    -- the `faces' methods creates the face ring as a quotient of the exterior algebra
    if not D.cache.?faces then faces(-1,D);
    d := dim D;
    -- the void complex is exceptional
    if d < -1 then return {0};
    apply(toList(0..1+dim D), i -> hilbertFunction(i, D.cache.faces.ring))
    )
    
-*   
    I := ideal D;
    if not opts.Flag then (
	S := newRing(ring D, Degrees => {#(gens ring D):1});
	maptoS := map(S, ring D);
	I = maptoS(I);
     );
     N := poincare cokernel generators I;
     if opts.Flag then (
     	 if not isBalanced(D) then (
             stderr << "-- the grading does not correspond to a proper d-coloring." << endl;
             return new HashTable from {}
     	     );
     	 R := newRing(ring N, Degrees => apply(gens ring N, g -> apply(gens ring N, f -> if index(f) == index(g) then 1 else 0)));
         maptoR := map(R, ring N);
         N = maptoR(N);
     	 );
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
     	 if opts.Flag then (
             new HashTable from apply(allsubsets, j -> j => flagf(j))
     	     )
	 else
     	 new HashTable from prepend(-1=>1, apply(toList(0..d-1), j -> j => f(j)))
     	 )
     )
*-

-- Check if the grading on the ring defines a proper (dim(D)+1)-coloring on
-- D. Used by fVector. Not exported.
-*
isBalanced = (D) -> (
     d := dim D +1;
     m := true;
     if not d == #(degree first gens ring D) then (
         m = false;
     );
     apply(flatten entries faces(1,D), f -> if max(degree f) > 1 then m = false);
     return m;
     );
*-





lcmMonomials = (L) -> (
     R := ring L#0;
     x := max \ transpose apply(L, i -> first exponents i);
     R_x)

lcmM = (L) -> (
-- lcmM finds the lcm of a list of monomials; the quickest method Sorin knows
    m := intersect toList (L/(i -> monomialIdeal(i)));
    m_0)





--- kludge to access parts of the 'Core'
raw = value Core#"private dictionary"#"raw";
rawIndices = value Core#"private dictionary"#"rawIndices";
rawKoszulMonomials = value Core#"private dictionary"#"rawKoszulMonomials";

makeLabels = (D,L,i,Sext) -> (
    -- D is a simplicial complex
    -- L is a list of monomials 
    -- i is an integer
    -- Sext is a ring
    Vertices := vertices D;
    F := flatten entries faces(i,D);
    if #F == 0 
    then matrix{{1_Sext}} 
    else
    matrix {apply(F, m -> (
		s := rawIndices raw m;
		lcmM L_(apply(s,i -> position(Vertices, j -> index j == i)))
		))}
    )

boundaryMap = method(Options => {Labels => {}})
boundaryMap (ZZ,SimplicialComplex) := opts -> (r,D) -> (
    L := opts.Labels;
    if not L == {} then (
	Vertices := vertices D;
	if not #L == #Vertices 
	then error "-- expected number of labels to equal the number of vertices.";
	if not all(L, m -> size m === 1)
	then error "-- expected Labels to be a list of monomials";
	S := ring L#0;
	M := monoid [Variables=>#L];
	Sext := S M;
	L = apply(#L, i -> L_i*Sext_i);
	ones := map(S, Sext, toList(#L:1_S));
	m1 := makeLabels(D,L,r,Sext);
	m2 := matrix{{1_Sext}};
	if not r == 0  then m2 = makeLabels(D,L,r-1,Sext);
	F := source map(S^1,, ones m2);
	bd := ones map(Sext, rawKoszulMonomials(numgens Sext, raw m2,raw m1));
	bd = map(F,,bd);
	bd
	)
    else (
    	R := ring D;	
	b1 := faces(r,D);
	b2 := faces(r-1,D);
	ones = map(coefficientRing R,R, toList(numgens R:1));
	ones map(R, rawKoszulMonomials(numgens R,raw b2,raw b1))
	)
    )

chainComplex SimplicialComplex := ChainComplex => {Labels => {}} >> opts -> (
    cacheValue(symbol chainComplex => opts)) (D -> (
    	Vertices := vertices D;
    	if not opts.Labels == {} then(
    	    if not #opts.Labels == #Vertices 
	    then error "-- expected number of labels to equal the number of vertices.";
	    if not all(opts.Labels, m -> size m === 1)
	    then error "-- expected Labels to be a list of monomials"
	    );
    	d := dim D;
    	C := if d < -1 then (coefficientRing(ring D))^0[-1]
    	else if d === -1 then (coefficientRing(ring D))^1
    	else chainComplex apply(0..d, r -> boundaryMap(r,D,Labels => opts.Labels));
    	if opts.Labels == {} then C[1] else C[0]
    	)
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

-- TODO: Should there be a cohomology method?

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


-- Compute the algebraic shifting of a simplicial complex and the
-- colored shifting if the ring is multigraded.
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





--------------------------------------------------------------------------
-- Buchberger complex of a monomial ideal (aka improved Taylor complex) --
-- (see Eisenbud-Hosten-Popescu)          
--------------------------------------------------------------------------

-- lcmMRed and faceBuchberger are specific to buchbergerComplex

lcmMRed = method()
lcmMRed (List) := (L) -> (
-- lcmMRed finds the lcm of a list of monomial and drops the
-- exponent on each variable by one (if that exponent in nonzero).
    m := intersect toSequence apply(L, i-> monomialIdeal(i));
    m_0//(product support m_0)
    )

faceBuchberger = (m, L) -> (
-- true iff the monomial m defines a face in the Buchberger complex.
-- if x has a variable with index greather than #L-1, then this
-- code produces an error
     x := rawIndices raw m;
     mon := lcmMRed(L_x);
     all(L, n -> mon//n == 0)
     )

-- requires numgens R == #L. I dislike this. Currently not exported.
buchbergerComplex = method()
buchbergerComplex(List,Ring) := (L,R) -> (
    P := ideal apply(gens R, x -> x^2);
    nonfaces := {};
    d := 1;
    while (L1 := flatten entries basis(d,coker gens P); #L1 > 0) do (
	L1 = select(L1, m -> not faceBuchberger(m,L));
	-- I do not like this output to the screen
	-- << "new nonfaces in degree " << d << ": " << L1 << endl;	  
	nonfaces = join(nonfaces,L1);
	if #nonfaces > 0 then
	P = P + ideal nonfaces;
	d = d+1;
	);
    simplicialComplex monomialIdeal matrix(R, {nonfaces})
    )

buchbergerSimplicialComplex = method()
buchbergerSimplicialComplex(List, Ring) := (L,R) -> (
    if numgens R < #L 
    then error concatenate("expect ring to have at least ",toString(#L)," generators");
    -- trim squares and excess variables for quicker basis computations later on
    P := ideal join(apply(#L, i -> R_i^2),apply(#L..numgens R-1, i -> R_i));
    -- excess variables in R are always nonfaces
    nonfaces := toList apply(#L..numgens R-1, i -> R_i);
    d := 2;
    -- We find the nonfaces in each degree
    while (L1 := flatten entries basis(d,coker gens P); #L1 > 0) do (
	L1 = select(L1, m -> not faceBuchberger(m,L));
	nonfaces = join(nonfaces,L1);
	if #nonfaces > 0 then
	P = P + ideal nonfaces;
	d = d+1;
	);    
    simplicialComplex monomialIdeal matrix(R, {nonfaces})
    )

buchbergerSimplicialComplex(MonomialIdeal, Ring) := (I,R) -> (
    buchbergerSimplicialComplex(flatten entries mingens I, R)
    )

buchbergerResolution = method()
buchbergerResolution List := ChainComplex => M -> (
    -- handle degenerate cases first
    if monomialIdeal M == 0
    then return (ring(monomialIdeal M))^1[0];
    -- Construct the buchbergerSimplicial Complex and homogenize
    R := ZZ(monoid[vars(0..#M-1)]);
    B := buchbergerSimplicialComplex(M,R);
    chainComplex(B,Labels=>M)
    )

buchbergerResolution MonomialIdeal := ChainComplex => M -> (
    if M == 0
    then (ring M)^1[0]
    else buchbergerResolution(first entries mingens M)
    )

taylorResolution = method();
taylorResolution List := ChainComplex => M -> (
    -- The Taylor resolution is the homogenization of the
    -- (numgens M - 1)-simplex. The implementation is
    -- straightforward once we've dealt with degenerate
    -- cases.
    if monomialIdeal M == 0
    then return (ring(monomialIdeal M))^1[0];
    if not all(M, m -> size m == 1) then 
    error "-- expected a list of monomials";
    if not all(M, m -> member(m,flatten entries mingens ideal M)) then 
    error "-- expected minimal generators of a monomial ideal";
    R := ZZ(monoid[vars(0..#M-1)]);
    Simplex := simplexComplex(#M-1,R);
    chainComplex(Simplex,Labels=>M)
    )

taylorResolution MonomialIdeal := ChainComplex => M -> (
    if M == 0
    then (ring M)^1[0]
    else taylorResolution(first entries mingens M)
    )


hasRoot = (F,L) -> (
    faceLabel := lcm L_(indices F);
    root := position(L,m -> faceLabel % m == 0);    
    member(root,indices F)
    )

lyubeznikSimplicialComplex = method(Options => {MonomialOrder => {}})
lyubeznikSimplicialComplex (List,Ring) := opts -> (M,A) -> (
    -- Deal with degenerate case first
    if M == {}
    then return simplicialComplex({1_A});
    -- Straightforward error checks
    if not all(M, m -> size m == 1) then 
    error "-- expected a list of monomials";
    if not all(M, m -> member(m,flatten entries mingens ideal M)) then 
    error "-- expected minimal generators of a monomial ideal";
    if not class A === PolynomialRing then
    error"-- expected a polynomial ring";
    L := M;
    if not opts.MonomialOrder == {} 
    then(
	if not sort opts.MonomialOrder == toList(0..#M-1) then
	error concatenate("-- MonomialOrder should be a permutation of {0,...,",toString(#M-1),"}");
 	L = M_(opts.MonomialOrder)
	);
    P := ideal join(apply(#L, i -> A_i^2),apply(#L..numgens A-1, i -> A_i));
    -- excess variables in A are always nonfaces
    nonfaces := toList apply(#L..numgens A-1, i -> A_i);
    d := 2;
    -- We look for nonrooted faces. The nonfaces also define the simplicial 
    -- complex and adding the nonfaces to P and taking the basis mod P, we
    -- reduce the number of faces we need to check for rootedness.
    while (dBasis := flatten entries basis(d, coker gens P); #dBasis > 0) do (
	newNonfaces := select(dBasis, F -> not hasRoot(F,L));
	nonfaces = join(nonfaces, newNonfaces);
	if #nonfaces > 0 then P = P + ideal(nonfaces);
	d = d+1;
	);
    simplicialComplex monomialIdeal matrix(A,{nonfaces})
    )

-- Natural implementation for a monomial ideal.
lyubeznikSimplicialComplex(MonomialIdeal,Ring) := opts -> (I,R) -> (
    minGens := first entries mingens I;
    lyubeznikSimplicialComplex(minGens, R, MonomialOrder => opts.MonomialOrder)
    )

-- We can construct the lyubeznik Resolution by first building the
-- lyubeznikSimplicialComplex and then homogenizing. The MonomialOrder
-- option seems silly, as lists are implicitly ordered, but this 
-- option is needed when we give a method for the MonomialIdeal class.
lyubeznikResolution = method(Options => {MonomialOrder => {}})
lyubeznikResolution List := opts -> L -> (
    MO := opts.MonomialOrder;
    R := QQ(monoid[vars(0..#L-1)]);
    if opts.MonomialOrder == {}
    then chainComplex(lyubeznikSimplicialComplex(L,R),Labels=>L)
    else chainComplex(lyubeznikSimplicialComplex(L,R),Labels=>L_MO)
    )

lyubeznikResolution MonomialIdeal := opts -> I -> (
    -- if I == monomialIdeal(0), then the set of mingens in empty
    -- and M2 doesn't know what ring to use when constructing the 
    -- resolution. Otherwise straightforward.
    if numgens I == 0 
    then return ((ring I)^1)[0];
    MinGens := flatten entries mingens I; 
    MO := opts.MonomialOrder;
    R := QQ(monoid[vars(0..#(mingens I)-1)]);
    if opts.MonomialOrder == {}
    then return(
	chainComplex(lyubeznikSimplicialComplex(I,R,MonomialOrder=>MO),Labels=>MinGens)
	)
    else return(
	 chainComplex(lyubeznikSimplicialComplex(I,R,MonomialOrder=>MO),Labels=>MinGens_MO)
	 )
     )

scarfSimplicialComplex = method()
scarfSimplicialComplex (List,Ring) := (L,A) -> (
    -- The scarfSimplicialComplex is the subcomplex of the (#L-1)-simplex
    -- whose faces have unique multidegrees. These unique multidegrees
    -- are called Scarf multidegrees.
    faceList := remove(subsets L, 0);
    faceLabels := for F in faceList list lcm F;
    scarfMultidegrees := for m in faceLabels list(
    	if #positions(faceLabels, k -> k == m) > 1
    	then continue
    	else m
    	);
    scarfFaces := for F in faceList list(
    	if member(lcm F, scarfMultidegrees)
    	then F
    	else continue
    	);
    simplicialComplex(for F in scarfFaces list(
	    vertexLabel := m -> position(L,k -> k == m);
	    product(for m in F list A_(vertexLabel m))
	    )
    	)
    )

-- natural functionality for a MonomialIdeal
scarfSimplicialComplex (MonomialIdeal,Ring) := (I,A) -> (
    if numgens I == 0 
    then return ((coefficientRing(ring I))^1)[0];
    scarfSimplicialComplex(first entries mingens I,A)
    )

-- The scarfChainComplex is the homogenization of the scarfSimplicial
-- complex.
scarfChainComplex = method()
scarfChainComplex List := L ->(
    A := QQ(monoid[vars(0..#L-1)]);
    chainComplex(scarfSimplicialComplex(L,A), Labels=>L)
    )

scarfChainComplex MonomialIdeal := I -> (
    if numgens I == 0 
    then return ((ring I)^1)[0];
    A := QQ(monoid[vars(0..#(mingens I)-1)]);
    chainComplex(scarfSimplicialComplex(I,A), Labels=>(first entries mingens I))
    )

-----------------------------------------------------------------------
-- Defining a class Face
-- to be used in other package in particular in the KustinMiller package
-- additions by Janko

Face = new Type of MutableHashTable
viewHelp
-- vertices of a face
-- vertices=method()



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
substitute(SimplicialComplex,PolynomialRing):=(D,R)->(
    n := numgens ring D;
    simplicialComplex first entries sub(facets D, (vars R)_{0..n-1})
    )


-*
installPackage "SimplicialComplexes"
R = QQ[a..e]
D = simplicialComplex monomialIdeal(a*b*c*d*e)
substitute(D,R)
F=(faces(1,D,useFaceClass=>true))#0
isFaceOf(F,D)
*-


------------------------------------------------------------------------------
-- Simplicial Maps
------------------------------------------------------------------------------
SimplicialMap = new Type of HashTable
SimplicialMap.synonym = "map of abstract simplicial complexes"
source SimplicialMap := SimplicialComplex => f -> f.source
target SimplicialMap := SimplicialComplex => f -> f.target
map SimplicialMap := RingMap => opts -> f -> f.map
matrix SimplicialMap := Matrix => opts -> f -> matrix map f

expression SimplicialMap := f -> (expression map) (expression (target f, source f, first entries matrix f))
toString SimplicialMap := f -> toString expression f
net SimplicialMap := f ->  net matrix f
texMath SimplicialMap := f -> texMath expression f

SimplicialMap#{Standard,AfterPrint} = SimplicialMap#{Standard,AfterNoPrint} = f -> (
    << endl;	-- double space
    << concatenate(interpreterDepth:"o") << lineNumber << " : SimplicialMap ";
    << net target f << " <--- " << net source f << endl;
    )

map(SimplicialComplex, SimplicialComplex, Matrix) := SimplicialMap => opts -> (E, D, A) -> (
    if ring A =!= ring E then 
        error "-- expected a matrix over the ring of the target";
    if rank target A =!= 1 then 
        error "-- expected the matrix to have 1 row"; 
    n := numgens ring D; 
    if rank source A =!= n then 
        error("-- expected the matrix to have " | n | " columns");	
    if coefficientRing D =!= coefficientRing E then
        error("-- expected the source and target to have the same coefficient ring");
    new SimplicialMap from {
    	symbol source => D,
    	symbol target => E,
    	symbol map => map(ring E, ring D, A),
    	symbol cache => new CacheTable}
    )

map(SimplicialComplex, SimplicialComplex, List) := SimplicialMap => opts -> (E, D, A) -> (
    map(E, D, matrix {A})
    )

map(SimplicialComplex, SimplicialComplex, RingMap) := SimplicialMap => opts -> (E,D,phi) -> (
    map(E, D, matrix phi)
    )

map(SimplicialComplex, Matrix) := SimplicialMap => opts -> (D,A) -> (
    Facets := first entries facets D;
    phi := map(ring D, A);
    Image := simplicialComplex(for F in Facets list phi(F));
    map(Image,D,A)
    )

map(SimplicialComplex, List) := SimplicialMap => opts -> (D,A) -> (
    map(D, matrix A)
    )

map(SimplicialComplex, RingMap) := SimplicialMap => opts -> (D,phi) -> (
    map(D,matrix phi)
    )

SimplicialComplex#id = D -> map(D, D, vars ring D)

isWellDefined SimplicialMap := Boolean => f -> (
    -- CHECK DATA STRUCTURE
    -- check keys
    K := keys f;
    expectedKeys := set{symbol source, symbol target, symbol map, symbol cache};
    if set K =!= expectedKeys then (
	if debugLevel > 0 then (
	    added := toList(K - expectedKeys);
	    missing := toList(expectedKeys - K);
	    if #added > 0 then 
	        << "-- unexpected key(s): " << toString added << endl;
	    if #missing > 0 then 
	        << "-- missing keys(s): " << toString missing << endl);
    	return false
	);
    --Check types
    if not instance(f.source, SimplicialComplex) then (
	if debugLevel > 0 then (
	    << "-- expected the source to be a SimplicialComplex" << endl);
	return false	);
    if not instance(f.target, SimplicialComplex) then (
	if debugLevel > 0 then (
	    << "-- expected the target to be a SimplicialComplex" << endl);
	return false
	);
    if not instance(f.map, RingMap) then (
	if debugLevel > 0 then (
	    << "-- expected the map to be a RingMap" << endl);
	return false
	);
    if not instance(f.cache, CacheTable) then (
    	if debugLevel > 0 then (
	    << "-- expected cache to be a CacheTable" << endl);
    	return false
	);    
    --Check mathematical structure
    D := source f;
    E := target f;
    g := map f;
    -- check ring map
    if source g =!= ring D then (
    	if debugLevel > 0 then (
	    << "-- expected source of the underlying ring map to be the ring of the source");
	return false	
	);
    if target g =!= ring E then (
    	if debugLevel > 0 then (
	    << "-- expected target of the underlying ring map to be the ring of the target");
	return false	
	);
    -- check that coefficient rings agree
    if coefficientRing ring D =!= coefficientRing ring E then (
	if debugLevel > 0 then (
	    << "-- expected the coefficient rings of the Stanley-Reisner rings to be equal");
	return false
	);
    -- check that vertices map to vertices
    if not all(vertices D, m -> member (g m, vertices E)) then (
    	if debugLevel > 0 then (
	    << "-- expected image of a vertex to be a vertex");
	return false	
	);
    -- check that the image of a face is a face
    if not all(first entries facets D, 
	m -> any(first entries facets E, 
	    e -> e % (product support g m) == 0)) 
    then (
    	if debugLevel > 0 then (
	    << "-- expected image of a face to be a face");
	return false
	);
    true    
    )

chainComplex SimplicialMap := ChainComplexMap => f -> (
    D := source f;
    E := target f;
    CD := chainComplex D;
    CE := chainComplex E;
    kk := coefficientRing D;
    EE := kk(monoid[gens ring E, SkewCommutative => true]);
    ED := kk(monoid[gens ring D, SkewCommutative => true]);
    coefEE := map(kk,EE, for i in gens EE list 1);
    phi := map f;
    psi := map(EE,ED,sub(matrix f,EE));
    g := i -> (
	if i === -1 then map(CE_(-1), CD_(-1), 1) else (
	    map(CE_i, CD_i, matrix table(first entries faces(i, E), first entries faces(i, D),
		    (n,m) -> (
			if phi m == n
			then coefEE(psi(sub(m,ED)))
			else 0
			)
		    )     
		)
	    )
	);
    map(CE, CD, g)
    )

--TODO: If we have constructed the barycentric subdivision, but want to change rings,
-- can we access some cached data here to make the computation faster?
barycentricSubdivision = method();
barycentricSubdivision (SimplicialComplex, Ring) := SimplicialComplex => (D,S) -> (
    if dim D == -infinity then return simplicialComplex(monomialIdeal(1_S));
    if numgens S < numFaces D - 1
    then error(" -- expected the ring to have at least " | numFaces D - 1 | " generators");
    faceList := first entries matrix{apply(dim D + 1, i-> faces(i, D))};
    baryFacets := flatten for F in first entries facets D list(
	for vertexList in permutations(support F) list(
	    L := apply(#vertexList, i -> product vertexList_{0..i});
    	    if L === {} then 1_S
	    else product apply(L, l -> S_(position(faceList, j -> j == l)))
	    )
	);
    simplicialComplex baryFacets
    )


-- TODO: Unexported? I forgot if that's intended
numFaces = method()
numFaces SimplicialComplex := ZZ => D -> (
    sum(-1 .. dim D, i -> numColumns faces(i,D))
    )

--TODO: I think that the roles of R and S should swap in this code, so that
-- the syntax better matches the syntaxs for maps.
--TODO: Are we using cached data to construct the barycentric subdivisions
-- for the source and target?
barycentricSubdivision (SimplicialMap, Ring, Ring) := SimplicialMap => (f,R,S) -> (
    D := source f;
    E := target f;
    faceListSource := first entries matrix{apply(dim D + 1, i -> faces(i,D))};
    faceListTarget := first entries matrix{apply(dim E + 1, i -> faces(i,E))};
    variableList := for F in faceListSource list(
       	S_(position(faceListTarget, G -> G == product support (map f)(F)))
	);
    map(barycentricSubdivision(target f, S), barycentricSubdivision(source f, R), 
	variableList | toList(numgens R - #variableList : 1_S)
	)
    )

isInjective SimplicialMap := Boolean => f -> (
    #vertices(source f) == #unique for x in vertices source f list (map f)(x)
    )

image SimplicialMap := SimplicialComplex => f -> (
    simplicialComplex(for F in first entries facets(source f) list (
	    sub(product support (map f)(F), ring target f)
	    )
	)
    )

isSurjective SimplicialMap := Boolean => f -> (
    facets image f == facets target f    
    )

homology(ZZ, SimplicialComplex, SimplicialComplex) := Module => opts -> (i,D,E) -> (
    inclusion := map(D,E, gens ring D);
    C := coker chainComplex inclusion;
    homology(i,C)
    )

homology(SimplicialComplex,SimplicialComplex) := ChainComplex => opts -> (D,E) -> (
    inclusion := map(D,E, gens ring D);
    C := coker chainComplex inclusion;
    homology C
    )

homology(ZZ, SimplicialMap) := Matrix => opts -> (i,f) -> (
    homology(i, chainComplex f)
    )

homology SimplicialMap := GradedModuleMap => opts -> f -> (
    homology(chainComplex f)
    )

elementaryCollapse = method();
elementaryCollapse (SimplicialComplex,RingElement) := SimplicialComplex => (D,F) -> (
    if not size F == 1 then error "The second argument should be a monomial representing a face";
    facetsContainingF := {};
    for G in first entries facets D do(
	if G % F == 0 then facetsContainingF = append(facetsContainingF,G)
	);
    if #facetsContainingF === 0 then error "this face does not belong to the simplicial complex";
    if #facetsContainingF > 1 then error "cannont collapse by this face";
    G := first facetsContainingF;
    if first degree F =!= first degree G - 1 then error "this face is not a maximal proper subface of a facet";
    newFacetList := delete(G,first entries facets D);
    for m in subsets(support G, first degree G - 1) do (
	if product m =!= F 
	then newFacetList = append(newFacetList, product m)
	else continue
	);
    simplicialComplex newFacetList
    )


