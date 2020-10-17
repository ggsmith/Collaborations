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
    "coneComplex",
    "verticalMaps",
    "mixedMaps"
    -- symbol
    }


------------------------------------------------------------------------------
-- CODE
------------------------------------------------------------------------------
path = prepend("../",path)
needsPackage "NormalToricVarieties"
needsPackage "FourierMotzkin"
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
isContainedInCone = method();
isContainedInCone (NormalToricVariety, List, Matrix) := Boolean => (X, sigma, v) -> (
    H := outerNormals(X, sigma);
    H0 := transpose H#0;
    H1 := transpose H#1;
    all (flatten entries (H0 * v), i -> i <= 0) and 
	all (flatten entries(H1 * v), i -> i === 0)
    )
-- Computes the preimages of all codimension-k cones via a toric map.
-- TODO: I tried to remove the while loop. how do i return something and then break?
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
-- This creates the C^0, C^1 complexes.
coneComplex = method();
coneComplex (ToricMap,ZZ) := (phi,k) -> (
    X := source phi;
    Y := target phi;
    S := ring X;
    n := numgens S;
    fineDeg := entries id_(ZZ^n);
    R := QQ (monoid [gens S, Degrees => fineDeg]);
    RfromS := map (R, S, gens R);
    preimages := conePreimages(phi,k);
    directSum (
	for tau in orbits(Y,k) list (
	    subfanrays := unique flatten preimages#tau;
	    tau => (
		I := ideal (for sigma in preimages#tau list (
			if sigma == subfanrays then 1_S
			else product(toList (set subfanrays - sigma), i -> S_i)
			)
		    );
		B := RfromS I;
		Hom(res (R^1/B), R^1)
		)
	    )
	)
    )
-- This method manually computes codimension k faces. It assumes that the list of cones are
-- equidimensional.
manualOrbits = method();
manualOrbits (List, ZZ) := (cones,k) -> (
    unique for sets in subsets(cones,k+1) list (
	if sets == {} then continue else (
	    intersection := sets_0;
	    n := #intersection;
	    flatten ( for A in sets do (
		    intersection = select(A, i -> member(i,intersection));
		    );
	    	if #intersection < n-k then continue else intersection
		)
	    )
	)
    )
-- This computes the vertical maps between C0 and C1 manually.
-- Note: I am recomputing conePreimages a lot. I think I should
-- just bundle verticalMaps together with coneComplex later.
verticalMaps = method();
verticalMaps ToricMap := phi -> (
    X := source phi;
    Y := target phi;
    S := ring X;
    n := numgens S;
    fineDeg := entries id_(ZZ^n);
    R := QQ (monoid [gens S, Degrees => fineDeg]);
    vpreimages := conePreimages(phi,0);
    epreimages := conePreimages(phi,1);
    C0 := coneComplex(phi,0);
    C1 := coneComplex(phi,1);
    clength := max({length C0, length C1});
    -- todo: signs...
    hashTable (
        for i to clength-1 list (
	    i => transpose matrix ( for sigma in orbits(Y,0) list (
		    if binomial(#vpreimages#sigma,i+1) == 0 then continue
		    else (
			for tau in orbits(Y,1) list ( matrix (
			        for sigma' in manualOrbits(vpreimages#sigma,i) list (
				    for tau' in manualOrbits(epreimages#tau,i) list (
				        if not(isSubset(tau',sigma') and isSubset(tau,sigma)) then 0_R
				    	else (
					    if sigma' == tau' then 1_R
					    else (
					        R_((toList(set sigma' - tau'))_0)
					    	)
					    )
					)
				    )
				)	     
			    )
			)
		    )
		)
	    )
	)
    )
-- WIP: computes some kind of mix of vertical and horizontal maps.
mixedMaps = method();
mixedMaps ToricMap := phi -> (
    X := source phi;
    Y := target phi;
    n := numgens ring X;
    m := numgens ring Y;
    S := ring X;
    S' := S ** ring Y;
    R := QQ (monoid [gens S, Degrees => entries id_(ZZ^n)]);
    R' := QQ (monoid [gens S', Degrees => entries id_(ZZ^(n+m))]);
    RfromS := map (R, S, gens R);
    R'fromS' := map(R', S', gens R');
    RfromR' := map(R, S', gens R | (for i to m-1 list 1_R));
    preimages := conePreimages(phi,0);
    Yrays := for j to m-1 list j;
    Xrays := for j to n-1 list j;
    I := ideal ( flatten ( for tau in max Y list (
	    	subfanrays := unique flatten preimages#tau;
       	    	for sigma in preimages#tau list (
		    product(toList (set Yrays - tau), j -> S'_(n+j)) * 
		    product(toList (set Xrays - sigma), j -> S'_j)
		    )	 
	    	)
	    )
	);
    B := R'fromS' I;
    C := Hom(res (R'^1/B), R'^1)
    )
-*
-- klein-schmidt varieties (have picard rank 2) (projective bundles over P^1 probably)
-- small fano varieties are implemented in macaulay2 and have natural maps

restart
load "ToricHigherDirectImages.m2"

-- F1 to P1
X = hirzebruchSurface(1); Y = toricProjectiveSpace(1, Variable => y); phi = map(Y, X, matrix {{1,0}});
conePreimages(phi, 0)
conePreimages(phi, 1)
C0 = coneComplex(phi,0); C0.dd
C1 = coneComplex(phi,1); C1.dd
verticalMaps(phi)
C = mixedMaps(phi); R = ring C; C.dd

-- F1 to P2
X2 = hirzebruchSurface(1); Y2 = toricProjectiveSpace(2, Variable => y); phi2 = map(Y2, X2, matrix {{0,-1},{1,0}});
conePreimages(phi2, 0)
conePreimages(phi2, 1)
C02 = coneComplex(phi2, 0)
C12 = coneComplex(phi2, 1)
verticalMaps(phi2)
C2 = mixedMaps(phi2); R2 = ring C2; C2.dd

-- P1 to P1 x P1
X3 = toricProjectiveSpace(1); Y3 = toricProjectiveSpace(1, Variable => y) ** toricProjectiveSpace(1, Variable => y); phi3 = map(Y3, X3, matrix {{1},{0}});
assert isWellDefined(phi3);
conePreimages(phi3, 0)
conePreimages(phi3, 1)
C03 = coneComplex(phi3, 0)
C13 = coneComplex(phi3, 1)
verticalMaps(phi3)
C3 = mixedMaps(phi3); R3 = ring C3; C3.dd

-- Blowup of F1 to P2
X4 = normalToricVariety({{1,0},{1,1},{0,1},{-1,1},{0,-1}},
    {{0,1},{1,2},{2,3},{3,4},{4,0}});
Y4 = toricProjectiveSpace(2, Variable => y);
phi4 = map(Y4, X4, matrix {{0,-1},{1,0}});
conePreimages(phi4, 0)
conePreimages(phi4, 1)
C04 = coneComplex(phi4, 0)
C14 = coneComplex(phi4, 1)
verticalMaps(phi4)
C4 = mixedMaps(phi4); R4 = ring C4; C4.dd

-- Fano(4,13) to P2
X5 = smoothFanoToricVariety(4,13)
Y5 = toricProjectiveSpace(2, Variable => y)
phi5 = map(Y5, X5, matrix {{1,0,0,0},{0,1,0,0}})
isWellDefined phi5
conePreimages(phi5,0)
conePreimages(phi5,1)
C05 = coneComplex(phi5,0); R05 = ring C05; C05.dd
C15 = coneComplex(phi5,1); R15 = ring C15; C15.dd
verticalMaps(phi5)
C5 = mixedMaps(phi5); R5 = ring C5; C5.dd


-- WIP

coneComplex2 = method();
coneComplex2 ToricMap := phi -> (
    X := source phi;
    Y := target phi;
    n := numgens ring X;
    m := numgens ring Y;
    S := ring X;
    S' := S ** ring Y;
    R := QQ (monoid [gens S, Degrees => entries id_(ZZ^n)]);
    R' := QQ (monoid [gens S', Degrees => entries id_(ZZ^(n+m))]);
    RfromS := map (R, S, gens R);
    R'fromS' := map(R', S', gens R');
    RfromR' := map(R, S', gens R | (for i to m-1 list 1_R));
    preimages := conePreimages(phi,0);
    Yrays := for j to m-1 list j;
    Xrays := for j to n-1 list j;
    I := ideal ( flatten ( for tau in max Y list (
	    	subfanrays := unique flatten preimages#tau;
       	    	for sigma in preimages#tau list (
		    print {toList (set Yrays - tau), n};
		    product(toList (set Yrays - tau), j -> S'_(n+j)) * 
		    product(toList (set Xrays - sigma), j -> S'_j)
		    )	 
	    	)
	    )
	);
    B := R'fromS' I;
    C := Hom(res (R'^1/B), R'^1);
    {d0,d1,f} := (0,0,0);
    currdim := #(max X);
    for i to length C do (
	
	)
    )


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