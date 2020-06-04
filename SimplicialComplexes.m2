-- -*- coding: utf-8 -*-
------------------------------------------------------------------------------
-- Copyright 2006--2020 Sorin Popescu, Gregory G. Smith, and Mike Stillman
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
	"SimplicialComplexes",
	AuxiliaryFiles => true,
    	Version => "1.3", 
    	Date => "4 June 2020",
    	Authors => {
	     {Name => "Sorin Popescu", 
		 Email => "sorin@math.sunysb.edu", 
		 HomePage => "http://www.math.sunysb.edu/~sorin/"},
	     {Name => "Gregory G. Smith", 
		 Email => "ggsmith@mast.queensu.ca", 
		 HomePage => "http://www.mast.queensu.ca/~ggsmith"},
	     {Name => "Mike Stillman", 
		 Email => "mike@math.cornell.edu", 
		 HomePage => "http://www.math.cornell.edu/~mike"}
	     },
    	Headline => "simplicial complexes",
    	DebuggingMode => true,
    	PackageExports => {"GenericInitialIdeal"}
    	)

export {
    "SimplicialComplex",
    "simplicialComplex",
    "boundary",
    "fVector",
    "isPure",
    "label",
    "faces",
    "facets",
    "link",
    "simplicialChainComplex",
    "buchbergerComplex",
    "lyubeznikComplex",
    "superficialComplex",
    "faceIdeal",
    "Face",
    "vertices",
    "face",
    "useFaceClass",
    "isSubface",
    "isFaceOf",
    "skeleton",
    "Flag",
    "algebraicShifting",
    "Multigrading",
    "star",
    "joinSimplicial"
    }

------------------------------------------------------------------------------
-- CODE
------------------------------------------------------------------------------
load "SimplicialComplexes/Code.m2"

------------------------------------------------------------------------------
-- DOCUMENTATION
------------------------------------------------------------------------------
beginDocumentation()
load "SimplicialComplexes/Documentation.m2"

------------------------------------------------------------------------------
-- TESTS
------------------------------------------------------------------------------
load "SimplicialComplexes/Tests.m2"

end---------------------------------------------------------------------------     

------------------------------------------------------------------------------
-- SCRATCH SPACE
------------------------------------------------------------------------------

-- XXX
uninstallPackage "SimplicialComplexes";
restart
installPackage "SimplicialComplexes"
check SimplicialComplexes

needsPackage "SimplicialComplexes";
