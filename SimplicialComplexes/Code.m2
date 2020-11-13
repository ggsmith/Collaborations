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
simplicialComplex Matrix := SimplicialComplex => f -> (
    if numrows f =!= 1 then error "-- expected a matrix with 1 row";
    simplicialComplex first entries f
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
	error concatenate("-- expected a polynomial ring with at least ",toString(n+1)," generators");
    simplicialComplex {product(n+1, i -> S_i)}
    )

-- Frank Lutz has enumerated all 2 and 3-manifolds with less than 10 vertices;
-- see http://page.math.tu-berlin.de/~lutz/stellar/3-manifolds.html
small2ManifoldsFile := currentFileDirectory | "small2ManifoldsLibrary.txt"
small210ManifoldsFile := currentFileDirectory | "small210ManifoldsLibrary.txt"
small3ManifoldsFile := currentFileDirectory | "small3ManifoldsLibrary.txt"
-- Do we want separate methods for the two dimensions? (there are two more files
-- consisting of 2/3-manifolds with ten vertices. There are around 42000/120000
-- of each respectively)
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
    if numgens S < 14 then
        error "-- expected a polynomial ring with at least 14 generators";    
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
dual SimplicialComplex := SimplicialComplex => {} >> opts -> D -> (
    -- Alexander duality for monomial ideals in part of the 'Core'    
    simplicialComplex dual monomialIdeal D)

link = method()
link (SimplicialComplex, RingElement) := SimplicialComplex => (D, f) -> (
    if isUnit f then return D;
    simplicialComplex ((monomialIdeal support f) + (monomialIdeal D : f))
    )

--boundary = method()
--boundary SimplicialComplex := D -> (
--     F := first entries facets D;
--     L := flatten apply (F, m -> apply (support m, x -> m // x));
--     if #L === 0 then 
--         return simplicialComplex monomialIdeal (1_(ring D));
--     simplicialComplex L
--     )

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
	D.cache.faces.ideal = (map(B,ring(ideal D),gens B))(ideal D);
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

makeLabels = (D,L,i,Sext) -> (
    -- D is a simplicial complex
    -- L is a list of monomials 
    -- i is an integer
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

chainComplex SimplicialComplex := {Labels => {}} >> opts -> (cacheValue(symbol chainComplex => opts)) (D -> (
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

taylorResolution = method();
taylorResolution List := ChainComplex => M -> (
    if monomialIdeal M == 0
    then return (ring(monomialIdeal M))^1[0];
    if not all(M, m -> size m == 1) then 
    error "-- expected a list of monomials";
    if not all(M, m -> member(m,flatten entries mingens ideal M)) then 
    error "-- expected minimal generators of a monomial ideal";
    r := #M;
    R := ZZ(monoid[vars(0..#M-1)]);
    Simplex := simplexComplex(r-1,R);
    chainComplex(Simplex,Labels=>M)
    )

taylorResolution MonomialIdeal := ChainComplex => M -> (
    if M == 0
    then (ring M)^1[0]
    else taylorResolution(first entries mingens M)
    )

lyubeznikSimplicialComplex = method(Options => {MonomialOrder => {}})
lyubeznikSimplicialComplex (List,Ring) := opts -> (M,A) -> (
    if M == {}
    then return simplicialComplex({1_A});
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
    Facets := for m in L list {m};
    FacetsNew := Facets;
    for i from 2 to #L do(
    	for F in subsets(L,i) do(
    	    rootF := position(L,m -> product F % m == 0);    
    	    if not all(subsets(F,i-1), G -> member(G,Facets))
    	    then continue
    	    else if not member(L#(rootF),F)
    	    then continue
    	    else FacetsNew = append(select(FacetsNew, G -> not all(G, m -> member(m,F))),F);
    	    );
    	Facets = FacetsNew;
    	);    
    D := simplicialComplex(for F in Facets list(
	    vertexLabel := m -> position(L,k -> k ==m);
	    product(for m in F list A_(vertexLabel(m)))
	    )
    	);
    D
    )

lyubeznikSimplicialComplex(MonomialIdeal,Ring) := opts -> (I,R) -> (
    MinGens := first entries mingens I;
    lyubeznikSimplicialComplex(MinGens, R, MonomialOrder => opts.MonomialOrder)
    )

lyubeznikResolution = method(Options => {MonomialOrder => {}})
lyubeznikResolution List := opts -> L -> (
    MO := opts.MonomialOrder;
    R := QQ(monoid[vars(0..#L-1)]);
    if opts.MonomialOrder == {}
    then return chainComplex(lyubeznikSimplicialComplex(L,R),Labels=>L)
    else return chainComplex(lyubeznikSimplicialComplex(L,R),Labels=>L_MO)
    )

lyubeznikResolution MonomialIdeal := opts -> I -> (
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
    LcmLattice := for F in remove(subsets L,0) list lcm F;
    ScarfMultidegrees := for m in LcmLattice list(
    	if #positions(LcmLattice,k -> k == m) > 1
    	then continue
    	else m
    	);
    ScarfFaces := for F in remove(subsets L, 0) list(
    	if member(lcm F, ScarfMultidegrees)
    	then F
    	else continue
    	);
    D := simplicialComplex(for F in ScarfFaces list(
	    vertexLabel := m -> position(L,k -> k ==m);
	    product(for m in F list A_(vertexLabel(m)))
	    )
    	);
    D
    )

scarfSimplicialComplex (MonomialIdeal,Ring) := (I,A) -> (
    if numgens I == 0 
    then return ((coefficientRing(ring I))^1)[0];
    scarfSimplicialComplex(first entries mingens I,A)
    )

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

-- 'vertices' method defined in 'Polyhedra" package
vertices Face := F -> F.vertices
vertices SimplicialComplex := D -> (
    if product first entries facets D == 1 
    then {}
    else support product(first entries facets D)
    )

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
net SimplicialMap := f ->  net first entries matrix f
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
    simplicialComplex(for F in first entries facets(source f) list (map f)(F))
    )

isSurjective SimplicialMap := Boolean => f -> (
    facets image f == facets target f    
    )

numFaces = method()
numFaces SimplicialComplex := ZZ => D -> (
    sum(-1 .. dim D, i -> numColumns faces(i,D))
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

-*
S = ZZ[y_0..y_5]
Circle = simplicialComplex(for i to 5 list y_i*y_((i+1)%6))
Irrelevant = simplicialComplex{1_S}
OnePoint = simplicialComplex{S_0}
TwoPoints = simplicialComplex{S_0, S_2}

for i from -1 to 1 list(
    prune homology(i, Circle,Irrelevant)
    )
prune homology(Circle, Irrelevant)

for i from -1 to 1 list(
    prune homology(i, Circle, OnePoint)
    )
prune homology(Circle, OnePoint)

for i from -1 to 1 list(
    prune homology(i, Circle, TwoPoints)
    )
prune homology(Circle, TwoPoints)

*-

-*
restart
needsPackage"SimplicialComplexes"
R = ZZ/101[x_0..x_10]
T = ZZ/101[y_0..y_15]
S = ZZ/101[z_0..z_24]
D = simplicialComplex{x_3*x_4*x_5}
E = barycentricSubdivision(D,T)
BE = barycentricSubdivision(E,S)
facets E
f = map(E,D,{1,1,1,y_2,y_5,y_6,1,1,1,1,1})
isWellDefined f
g = map(barycentricSubdivision(id_D, T, T))
isWellDefined g

bf = barycentricSubdivision(f,T,S)
isWellDefined bf


------

D = simplicialComplex{x_0*x_1*x_2, x_1*x_2*x_3}
faces D
E = barycentricSubdivision(D,S)
first entries facets E


D = simplicialComplex{R_1*R_2,R_2*R_3}
E = simplicialComplex{R_0*R_1}
f = map(E,D,{1_R, R_0, R_1, R_1, 1_R, 1_R, 1_R, 1_R, 1_R, 1_R, 1_R})
isWellDefined f

g = barycentricSubdivision(f, S, T)
isWellDefined g
faces target f
faces source f
faces target g
faces source g
map g

irrelevant = simplicialComplex{1_R}
numFaces irrelevant
bIrrelevant = barycentricSubdivision(irrelevant, R)
irrelevant === bIrrelevant



void = simplicialComplex(monomialIdeal 1_R)
numFaces void
barycentricSubdivision(void, ring void)

voidToIrrelevant = map (irrelevant, void, gens R)
isWellDefined voidToIrrelevant

DToIrrelevant = map(irrelevant, D, gens R)
isWellDefined DToIrrelevant



-----------------
bD = barycentricSubdivision(D, ZZ/101[x_0..x_(numFaces D - 1)])
ring oo

*-

-- Todo: test the void complex and see how it interacts with maps
-- Todo: find more nice examples of simplicial maps
-- Todo: does the join of complexes induce maps? link?
-- Todo: relative homology: take subcomplex of complex and map to contraction of the subcomplex.
-- also want to get the long exact sequence of relative homology
-- is there a reasonable notion of what a random map is? could we implement this?
-- TODO: Documentation

-*
matrix table(first entries faces(i,E), first entries faces(i,D), 
			(u,v) -> if phi(v) == u then 1_kk else 0_kk
			)
faces E


-- Sasha's path stuff
restart
path = prepend("../",path)
needsPackage "SimplicialComplexes"

R = QQ[a,b,c,d,e,f]
D = simplicialComplex({a*b*c, b*c*d, d*e*f})
D' = simplicialComplex({a*b*c, c*d, d*e*f})
phi = map(D, D', {a,b,c,d,e,f})
assert isWellDefined phi
Phi = chainComplex phi
Phi * (source Phi).dd == (target Phi).dd * Phi
(source Phi) === (chainComplex D')
(target Phi) === (chainComplex D)

S = QQ[w,x,y,z];
D = simplexComplex(3, S)
R = QQ[s,t];
E = simplexComplex(1,R)
f = map(E, D, matrix {{s,t,t,s}})
assert isWellDefined f
h = map(E, D, {s,t,t,s})
assert (h === f)

g = chainComplex(f)

CD = source g;
CE = target g;
for i to 3 list (g_(i-1)*CD.dd_i == CE.dd_i*g_i)

describe f

f.map
kk = coefficientRing(D)
M = matrix table(vertices E, vertices D, (u,v) -> if f.map(v) == u then 1_kk else 0_kk)

vertices E
vertices D

(chainComplex source f).dd
(chainComplex target f).dd

g1 = map((chainComplex E)_(-1), (chainComplex D)_(-1),1)
g2 = map((chainComplex E)_(0), (chainComplex D)_(0),M)

CE = chainComplex E
CD = chainComplex D

g1 * (CD).dd_0 == (CE).dd_0 * g2

S = QQ[a..e];
D = simplicialComplex {e, c*d, b*d, a*b*c}
E = simplicialComplex {e, c*d, a*b*c}
f = map(E, D, vars ring E)
debugLevel = 1
assert not isWellDefined f
g = map(D, E, vars ring E)
assert isWellDefined g

*-

map(SimplicialComplex, Matrix) := SimplicialComplex => opts -> (D,A) -> (
    Facets := first entries facets D;
    phi := map(ring D, A);
    Image := simplicialComplex(for F in Facets list phi(F));
    map(Image,D,A)
    )

map(SimplicialComplex, RingMap) := SimplicialComplex => opts -> (D,phi) -> (
    map(D,matrix phi)
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

wedge = method(Options => {AmbientRing => null});
wedge (SimplicialComplex,SimplicialComplex, RingElement, RingElement) := SimplicialComplex => opts -> (D,E,u,v) -> (
    if not coefficientRing D === coefficientRing E then error "expected the rings of the simplicial complexes to have the same coefficient ring";
    if not member(u, vertices D) or not member(v,vertices E) then error "expected vertices";
    R := null;
    if opts.AmbientRing =!= null
    then (
	R = opts.AmbientRing;
	if coefficientRing R =!= coefficientRing D then error "expected AmbientRing to have the same coefficient ring"
    	)
    else R = (coefficientRing D)(monoid[join(gens ring D, delete(v,gens ring E))]);
    uIndex := position(gens ring D, x -> x == u);
    vIndex := position(gens ring E, y -> y == v);
    includeD := map(R,ring D, for i to numgens ring D - 1 list R_i);
    includeE := map(R,ring E, for i to numgens ring E - 1 list (
	    if i < vIndex then R_(numgens ring D + i)
	    else if i == vIndex then R_uIndex
	    else R_(numgens ring D + i - 1)
	    )
	);
    FacetsD := first entries facets D;
    FacetsE := first entries facets E;
    simplicialComplex(join(for F in FacetsD list includeD(F), for F in FacetsE list includeE(F)))
    )

prune SimplicialComplex := SimplicialComplex => opts -> (D -> (
	R := (coefficientRing D)(monoid[]);
	if facets D == 0 then return simplicialComplex(monomialIdeal(1_R));
	if facets D == matrix{{1_(ring D)}} then return simplicialComplex{1_R}; 
	if gens ring D === vertices D then return D;
    	R = (coefficientRing D)(monoid[vertices D]);
    	Projection := matrix{for x in gens ring D list(
	    	if member(x, vertices D)
	    	then R_(position(vertices D, v -> v == x))
	    	else 0
	    	)
	    };
    	target map(D,Projection)
    	)
    )

-*


TODO: prune will set the ambient ring for the irrelevant and void complex to be the 
      polynomial ring with no variables, which seems like the approprate choice to me.
      However, this prodcues and error when we call faces. The functionality of one
      or these methods needs to change. The error can be backtraced to the facesM method.
needsPackage"SimplicialComplexes"
R = QQ[x_0..x_4];
D = simplexComplex(4,R)
gens ring D === vertices D
prune D

void = simplicialComplex(monomialIdeal(1_R))
ring void
prune void
faces prune void
ring prune void

irrelevant = simplicialComplex{1_R}
ring irrelevant
faces prune irrelevant
ring prune irrelevant

*-
