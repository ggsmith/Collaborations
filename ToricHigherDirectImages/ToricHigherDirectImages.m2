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
-- This method forms the C0, C1 complexes and the vertical map between them.
coneComplex = method();
coneComplex ToricMap := phi -> (
    X := source phi;
    Y := target phi;
    n := numgens ring X;
    m := numgens ring Y;
    -- Creating a fine graded version of ring X.
    R := QQ (monoid [gens ring X, Degrees => entries id_(ZZ^n)]);
    preimages := {conePreimages(phi,0),conePreimages(phi,1)};
    -- Create the C0, C1 complexes.
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
		    Hom(freeResolution module I, R^1)
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
    C := Hom(freeResolution module J, S^1);
    -- We extract them by picking out the right blocks.
    f := i -> (
        rows := for j to c0ranks_(-i) - 1 list j;
	cols := for j to c1ranks_(-i) - 1 list j + c0ranks_(-i+1);
	-- The matrix has the correct entries, but we force the
	-- source and target to be precisely the correct modules.
	map(C1_i, C0_i, simplifymap (C.dd_i)_rows^cols)
	);
    map(C1,C0,f)
    )
-- klein-schmidt varieties (have picard rank 2) (projective bundles over P^1 probably)
-- small fano varieties are implemented in macaulay2 and have natural maps
-*
restart
load "ToricHigherDirectImages.m2"

-- F1 to P1
X = hirzebruchSurface(1); Y = toricProjectiveSpace(1, Variable => y); phi = map(Y, X, matrix {{1,0}});
Cmap = coneComplex(phi); 
C0 = source Cmap; 
C1 = target Cmap;
C'map = HH Cmap
prune kernel C'map

-- F1 to P2
X2 = hirzebruchSurface(1); Y2 = toricProjectiveSpace(2, Variable => y); phi2 = map(Y2, X2, matrix {{0,-1},{1,0}});
Cmap2 = coneComplex(phi2); 
C02 = source Cmap2; 
C12 = target Cmap2;
C'map2 = HH Cmap2
prune kernel C'map2

-- P1 to P1 x P1
X3 = toricProjectiveSpace(1); Y3 = toricProjectiveSpace(1, Variable => y) ** toricProjectiveSpace(1, Variable => y); phi3 = map(Y3, X3, matrix {{1},{0}});
Cmap3 = coneComplex(phi3); 
C03 = source Cmap3; 
C13 = target Cmap3;
C'map3 = HH Cmap3
prune kernel C'map3

-- Blowup of F1 to P2
X4 = normalToricVariety({{1,0},{1,1},{0,1},{-1,1},{0,-1}},
    {{0,1},{1,2},{2,3},{3,4},{4,0}});
Y4 = toricProjectiveSpace(2, Variable => y);
phi4 = map(Y4, X4, matrix {{0,-1},{1,0}});
Cmap4 = coneComplex(phi4); 
C04 = source Cmap4; 
C14 = target Cmap4;
C'map4 = HH Cmap4
prune kernel C'map4

-- Fano(4,13) to P2
X5 = smoothFanoToricVariety(4,13)
Y5 = toricProjectiveSpace(2, Variable => y)
phi5 = map(Y5, X5, matrix {{1,0,0,0},{0,1,0,0}})
Cmap5 = coneComplex(phi5); 
C05 = source Cmap5; 
C15 = target Cmap5;
-- TODO: Something is wrong with the way the matrix is picked.
C'map5 = HH Cmap5
prune kernel C'map5

Cmap5

-- old method for creating each complex
-- one solution is to cache the rings.

-- use res module(I) instead
-- This creates the C^0, C^1 complexes.
coneComplex = method();
coneComplex (ToricMap,ZZ) := (phi,k) -> (
    X := source phi;
    Y := target phi;
    -- Create a fine graded version of the ring of X.
    n := numgens ring X;
    R := QQ (monoid [gens ring X, Degrees => entries id_(ZZ^n)]);
    preimages := conePreimages(phi,k);
    -- Take the direct sum of resolutions of irrelevant ideals.
    -- The irrelevant ideals selected correspond to the subfans
    -- given by the preimages of maximal cones in the target.
    directSum (
	for tau in orbits(Y,k) list (
	    subfanrays := unique flatten preimages#tau;
	    tau => (
		I := ideal (for sigma in preimages#tau list (
			if sigma == subfanrays then 1_R
			else product(toList (set subfanrays - sigma), i -> R_i)
			)
		    );
		Hom(res (R^1/I), R^1)
		)
	    )
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
