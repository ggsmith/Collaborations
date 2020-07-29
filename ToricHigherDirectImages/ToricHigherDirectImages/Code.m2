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
end