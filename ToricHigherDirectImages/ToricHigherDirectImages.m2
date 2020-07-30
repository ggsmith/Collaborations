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
    Headline => "dink",
    DebuggingMode => true,
    PackageExports => {"NormalToricVarieties"}
    )

export {
    -- types
    -- methods
    conePreimages
    -- symbol
    }


------------------------------------------------------------------------------
-- CODE
------------------------------------------------------------------------------
needsPackage("NormalToricVarieties")

conePreimages = method();
conePreimages ToricMap := phi -> (
    -- Need to check if the map is toric and proper --
    if not(isWellDefined(phi)) then error("not toric");
    if not(isProper(phi)) then error("not proper");
    X := source(phi);
    Y := target(phi);
    M := matrix(phi);
    preimages = hashTable (
	for tau in max(Y) list (
    	    tau => for sigma in max(X) list (
		-- use inRelativeInterior method from ToricMaps --
	    	taucone := coneFromVData((transpose matrix rays(Y))_tau);
	        sigmainterior := ((transpose matrix rays(X))_sigma)*(transpose matrix {for i to dim X - 1 list 1});
	        if contains(taucone,M*sigmainterior) then sigma
	        else continue
		)
	    )
	)
    )

------------------------------------------------------------------------------
-- DOCUMENTATION
------------------------------------------------------------------------------
beginDocumentation()
load "ToricHigherDirectImages/Documentation.m2"

------------------------------------------------------------------------------
-- TESTS
------------------------------------------------------------------------------
load "ToricHigherDirectImages/Tests.m2"

end---------------------------------------------------------------------------