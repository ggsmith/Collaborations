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
    Version => "2.0", 
    Date => "27 August 2020",
    Authors => {
	{Name     => "Gregory G. Smith", 
	 Email    => "ggsmith@mast.queensu.ca", 
	 HomePage => "http://www.mast.queensu.ca/~ggsmith"}
	},
    Headline => "exploring abstract simplicial complexes within commutative algebra",
    DebuggingMode => true,
    PackageExports => {"Polyhedra", "GenericInitialIdeal"}
    )

export {
    -- types
    "Face",    
    "SimplicialComplex",
    "SimplicialMap",
    -- methods
    "algebraicShifting",    
    "bartnetteSphereComplex",
    "bjornerComplex",
--    "boundary",
    "boundaryMap",    
    "buchbergerComplex",
    "dunceHatComplex",
    "face",  
    "grunbaumBallComplex",
    "isFaceOf",    
    "isSubface", 
    "link",
    "lyubeznikSimplicialComplex", 
    "lyubeznikResolution",
    "scarfSimplicialComplex",
    "scarfChainComplex",
    "nonPiecewiseLinearSphereComplex",
    "poincareSphereComplex", 
    "rudinBallComplex", 
    "star",	
    "simplexComplex",
    "simplicialComplex",
    "smallManifold",
    "taylorResolution",
    "zieglerBallComplex",
    -- symbol
    "Multigrading",
    "Labels"    
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

