-- -*- coding: utf-8 -*-
------------------------------------------------------------------------------
-- Copyright 2020--2020 Mike Roth, Gregory G. Smith, Alexandre Zotine
--
-- This program is free software: you can redistribute it and/or modify it
-- under the terms of the GNU General Public License as published by the Free
-- Software Foundation, either version 3 of the License, or (at your option)
-- any later version.
--
-- This program is distributed in the hope that it will be useful, but WITHOUT
-- ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
-- FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
-- more details.
--
-- You should have received a copy of the GNU General Public License along
-- with this program.  If not, see <http://www.gnu.org/licenses/>.
------------------------------------------------------------------------------
newPackage(
    "ToricHigherDirectImages",
    Version => "0.1", 
    Date => "17 July 2020",
    Authors => {
	{Name     => "Alexandre Zotine", 
	 Email    => "18az45@queensu.ca"}
	},
    Headline => "wonk",
    DebuggingMode => true,
    PackageExports => {"NormalToricVarieties"}
    )

export {
    -- types
    -- methods
    "conePreimages",
    "computeIntersections",
    "orderMatrices",
    "hdiComplex"
    -- symbol
    }


------------------------------------------------------------------------------
-- CODE
------------------------------------------------------------------------------
path = prepend("../",path)
needsPackage "NormalToricVarieties"
needsPackage "FourierMotzkin"
needsPackage "Complexes"
-- Non-exported method from NormalToricVarieties.
-- Computes the outer normals for a cone.
outerNormals = method()
outerNormals (NormalToricVariety, List) := List => (X, sigma) -> (
    if not X.cache.?outerNormals then (
    	X.cache.outerNormals = new MutableHashTable);
    if not X.cache.outerNormals#?sigma then (
    	V := transpose matrix rays X;
	(H0, H1) := fourierMotzkin V_sigma;
    	X.cache.outerNormals#sigma = {H0, H1};
	);
    X.cache.outerNormals#sigma
    )
-- Modification of isRelativeInterior in NormalToricVarieties.
-- This checks if a vector lies in the cone, not necessarily the interior.
-- There is a type called Fan which also has "contains," could be useful.
isContainedInCone = method();
isContainedInCone (NormalToricVariety, List, Matrix) := Boolean => (X, sigma, v) -> (
    H := outerNormals(X, sigma);
    H0 := transpose H#0;
    H1 := transpose H#1;
    all (flatten entries (H0 * v), i -> i <= 0) and 
	all (flatten entries(H1 * v), i -> i === 0)
    )
-- Manually intersects a list of lists.
manualIntersect = method();
manualIntersect List := L -> (
    if L == {} then L else (
    	if length L == 1 then L_0
    	else (
       	    ints := set L_0;
       	    for piece in L do ints = ints * set piece;
       	    toList ints
	    )
       	)
    )
-- Creates the polyhedral complex for a fan.
polyComplex = method();
polyComplex NormalToricVariety := X -> (
    cones := max X;
    d := dim X;
    verts := for i to #cones - 1 list i;
    for i from 1 to #verts - 1 list (
	print ("i is", i);
	coneseen := {};
    	faceseen := {};
	for face in subsets(verts,i) do (
    	    int := manualIntersect cones_face;
	    print ("int is", int);
	    if #int > d - i then (
		pos := position(coneseen, x -> x == int);
		print ("pos", pos);
		if pos === null then (
		    print ("null pos, here's face", face);
		    coneseen = append(coneseen,int);
		    faceseen = append(faceseen,face);
		    face
		    )
		else (
		    newface := toList(set (faceseen_pos) + set face);
		    print ("some pos, newface", newface);
		    faceseen = drop(faceseen, pos);
		    faceseen = insert(pos, newface, faceseen);
		    )
		)
	    else continue
	    );
	faceseen
	)
    )
-- Computes the preimages of all codimension-k cones via a toric map,
-- together with their intersections.
conePreimages = method();
conePreimages (ToricMap,ZZ) := (phi,k) -> (
    X := source phi;
    n := dim X;
    Y := target phi;
    M := matrix phi;
    -- Returns a hash table
    hashTable ( 
	-- indexed by codimension-k cones in the target.
	for tau in orbits(Y,k) list (
	    tau => flatten (
		-- Start searching through the lowest codimension cones
		-- first. If we find one of lower codimension, we don't
		-- need to check the higher codimension cones.
		i := -1;
		flag := true;
		while(i < k and flag) list (
		    i = i + 1;
		    -- For each cone in the source, check if its interior
		    -- maps into the target cone.
		    preimages := for sigma in orbits(X,i) list (
			sigmainterior := ((transpose matrix rays X)_sigma) *
			(transpose matrix {for j to #sigma - 1 list 1});
			if isContainedInCone(Y,tau,M*sigmainterior) then (
			    sigma
			    )
			else continue
			);
		    if preimages == {} then continue
		    else (
			flag = false;
			preimages
			)
		    )
		)
	    )
	)
    )
computeIntersections = method();
computeIntersections (ZZ, List) := (n, L) -> (
    if L == {} then {}
    else (
	d := length L_0;
	ambientSet := for i to n list i;
	intersections := set {ambientSet};
	for l in L do (
	    moreIntersections := set for t in toList intersections list toList((set t) * (set l));
	    intersections = intersections + moreIntersections;
	    );
	for i to d list (
	    sort for l in toList intersections list (
		if length l == d-i then sort l
		else continue
		)
	    )
	)
    )
orderMatrices List := 
-- This method forms the C0, C1 complexes and the vertical map between them.
hdiComplex = method();
hdiComplex ToricMap := phi -> (
    X := source phi;
    Y := target phi;
    n := numgens ring X;
    -- Creating a fine graded version of ring X.
    R := QQ (monoid [gens ring X, Degrees => entries id_(ZZ^n), MonomialOrder => Lex]);
    XtoR := map(R, ring X, gens R);
    preimages := {conePreimages(phi,0),conePreimages(phi,1)};
    (C0, C1) := toSequence for k to 1 list (
	D := directSum (
	    for tau in orbits(Y,k) list (
	    	subfanrays := unique flatten preimages_k#tau;
	    	tau => (
		    I := ideal (for sigma in preimages_k#tau list (
			    if sigma == subfanrays then 1_R
			    else product(toList (set subfanrays - sigma), i -> R_i)
			    )
		    	);
		    C := freeResolution (R^1/I);
		    if length C === 1 then C = complex C_1
		    else C = complex apply (length C - 1, i -> C.dd_(i+2));
		    Hom(C,R^1)
		    )
		)
	    )
	);
    -- Actually all of the maps are blocks of the resolution of
    -- the irrelevant ideal of X. We can extract the vertical maps
    -- this way.
    C := freeResolution (R^1/(XtoR ideal X));
    -- Remove the 0-th term.
    C = complex apply (length C - 1, i -> C.dd_(i+2));
    C = Hom(C, R^1);
    -- We extract them by picking out the right blocks.
    ints := for k to 1 list (
	hashTable ( 
	    for sigma in orbits(Y,k) list sigma => computeIntersections(#rays X, preimages_k#sigma)
	    )
	);
    coneindex := for i to 1 list (
	for j to dim X - i list (
	    L := sort flatten for sigma in orbits(Y,i) list ((ints_i)#sigma)_j;
	    if L == {} then continue else L
	    )
	);
    f := i -> (
        rows := for sigma in coneindex_1_-i list position(rsort orbits(X,-i+1),tau -> tau == sigma);
        cols := ofor sigma in coneindex_0_-i list position(rsort orbits(X,-i),tau -> tau == sigma);
	-- The matrix has the correct entries, but we force the
	-- source and target to be precisely the correct modules.
	map(C1_i, C0_i, (C.dd_i)_cols^rows)
	);
    map(C1,C0,f)
    )
-- klein-schmidt varieties (have picard rank 2) (projective bundles over P^1 probably)
-- small fano varieties are implemented in macaulay2 and have natural maps
-*
restart
load "ToricHigherDirectImages3.m2"
needsPackage "Complexes"

X = smoothFanoToricVariety(3,14); Y = hirzebruchSurface(1, Variable => y); phi = map(Y, X, matrix {{1,0,0},{0,1,0}}); 
gamma = hdiComplex phi
gamma.dd
H = orderMatrices phi

L = H_1_0;
mat = for i to #L - 1 list for j to #L - 1 list if i == j then 1 else 0
actualmat = matrix sort(mat, f) 

X = hirzebruchSurface(1); Y = toricProjectiveSpace(2, Variable => y); phi = map(Y, X, matrix {{0,-1},{1,0}});
gamma = hdiComplex(phi);

X = hirzebruchSurface(1); Y = toricProjectiveSpace(1, Variable => y); phi = map(Y, X, matrix {{1,0}});
gamma = hdiComplex phi;
(gamma_0).dd
gamma_2_0_0
gamma_2_0_1

X = smoothFanoToricVariety(3,14); Y = hirzebruchSurface(1, Variable => y); phi = map(Y, X, matrix {{1,0,0},{0,1,0}}); 
gamma = hdiComplex(phi);
C0 = gamma_0
C1 = gamma_1
C0.dd
gamma_2_0_1
gamma_2_0_2

-- F1 to P1
X = hirzebruchSurface(1); Y = toricProjectiveSpace(1, Variable => y); phi = map(Y, X, matrix {{1,0}});
gamma = hdiComplex(phi); 
C0 = source gamma; 
C1 = target gamma;
C'map = HH gamma
R = prune kernel C'map
R^0
R^1

-- F1 to P2
X2 = hirzebruchSurface(1); Y2 = toricProjectiveSpace(2, Variable => y); phi2 = map(Y2, X2, matrix {{0,-1},{1,0}});
gamma2 = hdiComplex(phi2); 
C02 = source gamma2; 
C12 = target gamma2;
C'map2 = HH gamma2
R2 = prune kernel C'map2;
R2^0
R2^1
rays X2

-- P1 to P1 x P1
X3 = toricProjectiveSpace(1); Y3 = hirzebruchSurface(0, Variable => y); phi3 = map(Y3, X3, matrix {{1},{0}});
gamma3 = hdiComplex(phi3); 
C03 = source gamma3; 
C13 = target gamma3;
C'map3 = HH gamma3
prune kernel C'map3

-- Blowup of F1 to P2
X4 = normalToricVariety({{1,0},{1,1},{0,1},{-1,1},{0,-1}},{{0,1},{1,2},{2,3},{3,4},{4,0}}); Y4 = toricProjectiveSpace(2, Variable => y); phi4 = map(Y4, X4, matrix {{0,-1},{1,0}});
gamma4 = hdiComplex(phi4); 
C04 = source gamma4; 
C14 = target gamma4;
C'map4 = HH gamma4
prune kernel C'map4

-- Fano(4,13) to P2
X5 = smoothFanoToricVariety(4,13); Y5 = toricProjectiveSpace(2, Variable => y); phi5 = map(Y5, X5, matrix {{1,0,0,0},{0,1,0,0}});
gamma5 = hdiComplex(phi5); 
C05 = source gamma5; 
C15 = target gamma5;
C05.dd_(-1) * C05.dd_0
-- TODO: Something is wrong with the way the matrix is picked.
C'map5 = HH gamma5
R5 = prune kernel C'map5;
R5^0
R5^1
R5^2

-- Fano(3,14) to F1
X6 = smoothFanoToricVariety(3,14); Y6 = hirzebruchSurface(1, Variable => y); phi6 = map(Y6, X6, matrix {{1,0,0},{0,1,0}});
gamma6 = hdiComplex(phi6); 
C06 = source gamma6; 
C16 = target gamma6;
isCommutative gamma6
C'map6 = HH gamma6
R6 = prune kernel C'map6;
R6^0
R6^1
R6^2

M = orderMatrices phi6

gettMatrix = method();
gettMatrix Matrix := M -> (
    matrix ( for i to numRows M - 1 list (
    	    for j to numColumns M - 1 list (
	    	M_j_i
	    	)
	    )
    	)
    )

gamma0 = gettMatrix gamma6_0
gamma1 = gettMatrix gamma6_-1
d00 = gettMatrix C06.dd_0
d10 = gettMatrix C16.dd_0

netList {gamma1,d00, gamma1*d00, d10, gamma0, d10*gamma0}

gamma1 * d00 
d10 * gamma0

ngamma1 = M_1_1 * gamma1
nd00 = M_0_1 * d00 * M_0_0
ngamma0 = M_1_0 * gamma0
nd10 = M_1_1* d10 * M_1_0

ngamma1 * nd00
nd10 * ngamma0

R = ZZ[x_0..x_6]

gamma0 = matrix {{-x_1,0,x_4,0,0,0,0,0,0,0},
    	    	 {0,-x_1,0,x_4,0,0,0,0,0,0},
		 {-x_0,0,0,0,x_6,0,0,0,0,0},
		 {0,-x_0,0,0,0,x_6,0,0,0,0},
		 {0,0,0,0,-x_1,0,0,x_5,0,0},
		 {0,0,0,0,0,-x_1,0,0,0,x_5},
		 {0,0,-x_0,0,0,0,x_5,0,0,0},
		 {0,0,0,-x_0,0,0,0,0,x_5,0}}
gamma1 = matrix {{x_1,-x_4,0,0,0,0,0},
                 {x_0,0,-x_6,0,0,0,0},
		 {0,0,x_1,0,0,-x_5,0},
		 {0,x_0,0,0,-x_5,0,0}}
d00 = matrix {{-x_2,x_3,0,0,0,0,0,0,0,0},
              {0,0,-x_2,x_3,0,0,0,0,0,0},
	      {0,0,0,0,-x_2,x_3,0,0,0,0},
	      {0,0,0,0,0,0,-x_4,x_6,0,0},
	      {0,0,0,0,0,0,-x_2,0,x_3,0},
	      {0,0,0,0,0,0,0,-x_2,0,x_3},
	      {0,0,0,0,0,0,0,0,-x_4,x_6}}
d10 = matrix {{-x_2,x_3,0,0,0,0,0,0},
              {0,0,-x_2,x_3,0,0,0,0},
	      {0,0,0,0,-x_2,x_3,0,0},
	      {0,0,0,0,0,0,-x_2,x_3}}
	  



isCommutative gamma6

-- Fano(4,27) to F1
X7 = smoothFanoToricVariety(4,103); Y7 = hirzebruchSurface(1, Variable => y); phi7 = map(Y7, X7, matrix {{1,0,0,0},{0,1,0,0}});
gamma7 = hdiComplex(phi7); 
C07 = source gamma7; 
C17 = target gamma7;
-- TODO: Something is wrong with the way the matrix is picked.
C'map7 = HH gamma7
R7 = prune kernel C'map7;
R7^0
R7^1
R7^2

debugLevel = 1;

isCommutative gamma
isCommutative gamma2
isCommutative gamma3
isCommutative gamma4
isCommutative gamma4
isCommutative gamma5
isCommutative gamma6
isCommutative gamma7

isWellDefined gamma
isWellDefined gamma2
isWellDefined gamma3
isWellDefined gamma4
isWellDefined gamma5
isWellDefined gamma6
isWellDefined gamma7


gamma7_(-2)
C07.dd_(-1)
gamma7_(-2) * C07.dd_(-1)
C17.dd_(-1) * gamma7_(-1)

gamma7_(-1)
C07.dd_0
gamma7_(-1) * C07.dd_(0)
C17.dd_(0) * gamma7_(0)



-- for f1 to p1, how can we extract the right vector spaces for the graded pieces?
-- for the fano example, try to determine if the code is computing the higher direct images correctly.
-- topological models

-- searching for surjective map from something to picard rank 2
matset = for pair in subsets({{1,0,0,0},{0,1,0,0},{0,0,1,0},{0,0,0,1}},2) list (
    matrix{pair_0,pair_1}
    )
FanoToPic2 = flatten for i to 123 list (
    flatten for j to 1 list (
	Y = hirzebruchSurface(j);
    	for mat in matset list (
	    X = smoothFanoToricVariety(4,i);
	    phi = map(Y, X, mat);
	    if isWellDefined phi then (
		(isWellDefined phi,i,j,mat)
		)
	    else (
		continue
		)
	    )
	)
    )
netList FanoToPic2
X = smoothFanoToricVariety(4,111)
matset2 = for pair in subsets({{1,0,0},{0,1,0},{0,0,1}},2) list (
    matrix{pair_0,pair_1}
    )
FanoToPic2 = flatten for i to 17 list (
    flatten for j to 1 list (
	Y = hirzebruchSurface(j);
    	for mat in matset2 list (
	    X = smoothFanoToricVariety(3,i);
	    phi = map(Y, X, mat);
	    if isWellDefined phi then (
		(isWellDefined phi,i,j,mat)
		)
	    else (
		continue
		)
	    )
	)
    )
netList FanoToPic2


---------------

-- old method for creating horizontal maps
    (C0, C1) := toSequence for k to 1 list (
	D := directSum (
	    for tau in orbits(Y,k) list (
	    	subfanrays := unique flatten (preimages_k#tau)_0;
	    	tau => (
		    I := ideal (for sigma in (preimages_k#tau)_0 list (
			    if sigma == subfanrays then 1_R
			    else product(toList (set subfanrays - sigma), i -> R_i)
			    )
		    	);
		    C := freeResolution (R^1/I);
		    if length C === 1 then C = complex C_1
		    else C = complex apply (length C - 1, i -> C.dd_(i+2));
		    Hom(C,R^1)
		    )
		)
	    )
	);
    -- Since I need to check one term further, I append a 0.
    c0ranks := (for i to length C0 list ( rank C0_(-i) )) | {0};
    c1ranks := for i to length C1 list ( rank C1_(-i) );
    S := QQ (monoid [gens ring X | gens ring Y, Degrees => entries id_(ZZ^(n+m))]);
    -- This map removes the y variables.
    simplifymap := map(R, S, gens R | (for i to m - 1 list 1_R));
    Yrays := for j to m-1 list j;
    Xrays := for j to n-1 list j;
    J := ideal ( flatten ( for tau in max Y list (
	    	subfanrays := unique flatten preimages_0#tau;
       	    	for sigma in preimages_0#tau list (
		    product(toList (set Yrays - tau), j -> S_(n+j)) * 
		    product(toList (set Xrays - sigma), j -> S_j)
		    )	 
	    	)
	    )
	);
    -- This complex miraculously has the correct vertical maps.
    C := freeResolution (S^1/J);
    -- But we need to remove the 0-th term.
    C = complex apply (length C - 1, i -> C.dd_(i+2));
    C = Hom(C, S^1);
    -- We extract them by picking out the right blocks.
    f := i -> (
        rows := for j to c0ranks_(-i) - 1 list j;
	cols := for j to c1ranks_(-i) - 1 list j + c0ranks_(-i+1);
	-- The matrix has the correct entries, but we force the
	-- source and target to be precisely the correct modules.
	map(C1_i, C0_i, simplifymap (C.dd_i)_rows^cols)
	);

--------

    -- Initial vertical map.
    M := matrix flatten (
        i := 1; 
	for tau in orbits(Y,1) list (
	    for epre in preimages_1#tau list (
		flatten for sigma in orbits(Y,0) list (
		    for vpre in preimages_0#sigma list (
			if isSubset(epre,vpre) then (
			    i = i*(-1);
			    i*product(toList (set vpre - epre), i -> R_i)
			    )
			else (
			    0
			    )
			)
		    )
		)
	    )
	);
    {C0, C1, M}
    
------------

    -- (this is hacky. i was originally going to construct the first map 
    -- manually and then extend, but realized i could reuse my old
    -- defective code to construct it since i was getting some ordering
    -- issues.. so i construct my special complex and only take the first
    -- map from it, then extend it. bad. very bad. ugly. gross.)
    rows := for j to c0ranks_0 - 1 list j;
    cols := for j to c1ranks_0 - 1 list j + c0ranks_1;
    -- The matrix has the correct entries, but we force the
    -- source and target to be precisely the correct modules.
    M := simplifymap (C.dd_0)_rows^cols;
    f := extend(C1, C0, map(C1_0, C0_0, M));
    map(C1,C0,f)

-- Compute vertical maps.
    f := i -> (map(C1_i,C0_i, matrix flatten (
            	j := 1;
	    	for tau in orbits(Y,1) list (
	    	    for epre in (preimages_1#tau)_(-i) list (
		    	flatten for sigma in orbits(Y,0) list (
		    	    for vpre in (preimages_0#sigma)_(-i) list (
			        if isSubset(epre, vpre) and isSubset(tau, sigma) then (
			    	    j = j*(-1);
				    j*product(toList (set vpre - epre), k -> R_k)
			    	    )
			    	else (
			    	    0_R
				    )
				)
			    )
			)
		    )
		)
	    )
	);
    map(C1,C0,f)

*-
------------------------------------------------------------------------------
-- DOCUMENTATION
------------------------------------------------------------------------------
--beginDocumentation()

------------------------------------------------------------------------------
-- TESTS
------------------------------------------------------------------------------


end
---------------------------------------------------------------------------
