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
    "coneComplex"
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
conePreimages = method();
conePreimages (ToricMap,ZZ) := (phi,k) -> (
    X := source phi;
    n := dim X;
    Y := target phi;
    M := matrix phi;
    sigmainterior := 0;
    i := 0;
    flag := true;
    -- Returns a hash table
    hashTable ( 
	-- indexed by codimension-k cones in the target.
	for tau in orbits(Y,k) list (
	    tau => flatten (
		flag = true;
		i = -1;
		-- Start searching through the lowest codimension cones
		-- first. If we find one of lower codimension, we don't
		-- need to check the higher codimension cones.
		while(flag and i < k) list (
		    i = i+1;
		    -- For each cone in the source, check if its interior
		    -- maps into the target cone.
	    	    for sigma in orbits(X,i) list (
			-- This is to make matrix composition work.
			if sigma == {} or n - i - 1 < 0 then (
			    sigmainterior = matrix {for j to n - 1 list 0}
			    )
		    	else (
			    sigmainterior = ((transpose matrix rays X)_sigma) *
			    (transpose matrix {for j to n - i - 1 list 1})
			    );
			if isContainedInCone(Y,tau,M*sigmainterior) then (
			    flag = false;
			    sigma
			    )
			else continue
			)
		    )
	    	)
	    )
	)
    )
-- This creates the C^0, C^1 complexes. For other methods, we want
-- this data stored as a hash table first, but it can easily be
-- converted into a chainComplex by summing the entries of the table.
coneComplex = method();
coneComplex (ToricMap,ZZ) := (phi,k) -> (
    X := source phi;
    Y := target phi;
    S := ring X;
    n := numgens S;
    h := toList (n:1);
    fineDeg := entries id_(ZZ^n);
    R := QQ (monoid [gens S, Degrees => fineDeg, Heft => h]);
    RfromS := map (R, S, gens R);
    I := 0;
    B := 0;
    preimages := conePreimages(phi,k);
    subfanrays := 0;
    hashTable (
	for tau in orbits(Y,k) list (
	    subfanrays = unique flatten preimages#tau;
	    tau => (
		I = ideal (for sigma in preimages#tau list (
			if sigma == subfanrays then 1_S
			else product(toList (set subfanrays - sigma), i -> S_i)
			)
		    );
		B = RfromS I;
		Hom(res (R^1/B), R^1)
		)
	    )
	)
    )
-- This computes the vertical maps between C0 and C1 manually.
verticalMaps = method();
verticalMaps (ToricMap, ZZ) := (phi,k) -> (
    
    )
-*
restart
load "ToricHigherDirectImages.m2"

X = hirzebruchSurface(1);
Y = toricProjectiveSpace(1);
phi = map(Y, X, matrix {{1,0}});
assert isWellDefined(phi);
conePreimages(phi, 0)
conePreimages(phi, 1)
C = coneComplex(phi, 0);
R = ring (C#{0})_0;
C' = coneComplex(phi, 1);
(C#{0}).dd
(C'#{}).dd

X2 = hirzebruchSurface(1);
Y2 = toricProjectiveSpace(2);
phi2 = map(Y2, X2, matrix {{0,-1},{1,0}});
assert isWellDefined(phi2);
conePreimages(phi2, 0)
conePreimages(phi2, 1)
C = coneComplex(phi2, 0)

X3 = toricProjectiveSpace(1);
Y3 = toricProjectiveSpace(1) ** toricProjectiveSpace(1);
phi3 = map(Y3, X3, matrix {{1},{0}});
assert isWellDefined(phi3);
conePreimages(phi3, 0)
conePreimages(phi3, 1)

X4 = normalToricVariety({{1,0},{1,1},{0,1},{-1,1},{0,-1}},
    {{0,1},{1,2},{2,3},{3,4},{4,0}});
Y4 = toricProjectiveSpace(2);
phi4 = map(Y4, X4, matrix {{0,-1},{1,0}});
assert isWellDefined(phi4);
conePreimages(phi4, 0)
conePreimages(phi4, 1)
C = coneComplex(phi4, 0)
R = ring (C#{0,1})_0
(C#{0,2}).dd
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