restart
needsPackage"SimplicialComplexes"


-------------------------------RUDIN BALL-----------------------------------

---------------------------- General Setup ---------------------------------

S = QQ[x_0..x_13]
Δ = rudinBallComplex S
d = dim Δ

-- ideal and Stanley-Riesner ring of Δ
IΔ = ideal Δ
kΔ = S/IΔ

------------------------- f-vector And h-vector ----------------------------

fΔ = fVector Δ

-- computing h-vector
hΔ = for j to d list(
    sum for i to j list (-1)^(j-i)*binomial(d+1-i,j-i)*(fΔ#(i-1))
    )

-- Here is another formula for computing the h-vector from the f vector. The
-- coefficients of t^k is the kth entry in the h-vector
R = QQ[t]
sum for i to d+1 list fΔ#(i-1)*t^i*(1-t)^(d+1-i)

-- We can compare to the numerator of the hilbert series of kΔ
reduceHilbert(hilbertSeries kΔ)

------------------------- Euler characteristic -----------------------------

sum for i to d list (-1)^i*(fΔ#(i))

----------------- Cohen-Macaulay And Shellability -------------------------

-- Δ is Cohen-Macaulay but not shellable.

-- depth kdim(S^1/IΔ) is the left-hand side, given by the Auslander-Buchsbaum
-- formula. dim kΔ is the right-hand side.

dim S - pdim(S^1/IΔ) == dim(S^1/IΔ)

-- We show Δ is not shellable by showing that there is a subcomplex of Δ that
-- is not pure. Stanley, chapter 3 prop 3.1

all(subsets(gens S), A -> isPure inducedSubcomplex(Δ,A))

-- Here is an specific instance of the failure of an induced subcomplex to be
-- pure.
inducedSubcomplex(Δ, {S_0,S_1,S_2})


--------------------------- Ziegler BALL ----------------------------------

-------------------------- h-vector ---------------------------------------

S = QQ[x_0..x_9]
Δ = zieglerBallComplex S
IΔ = ideal Δ
kΔ = S/IΔ
fΔ = fVector Δ
d = dim Δ

R = QQ[t]
hΔ = sum for i to d+1 list fΔ#(i-1)*t^i*(1-t)^(d+1-i)
reduceHilbert(hilbertSeries kΔ)

--------------------- Euler characteristic ---------------------------------

sum for i to d list (-1)^i*(fΔ#(i))

---------------- Cohen-Macaulay and Shellability ---------------------------

-- The Zeigler ball is also Cohen-Macaulay, but not shellable. We compute
-- the Cohen-Macaulay property a different way, using B.H 5.3.9

faceList = flatten flatten for i from -1 to dim Δ list entries (faces Δ)#i

totalHomologyRankForLink = (Δ,F) -> (
    linkF := link(Δ, F);
    dL := dim linkF;
    sum for i from -1 to dL-1 list rank (homology link(Δ,F))#i
    ) 

all(faceList, F -> totalHomologyRankForLink(Δ,F) == 0)

------------- Projective Plane In Characteristic 2-------------------------

-------------------------- h-vector ---------------------------------------

S = ZZ/2[x_0..x_5]
Δ = simplicialComplex{ S_0*S_1*S_4, S_0*S_1*S_5, S_0*S_2*S_5, S_0*S_3*S_3,
                       S_0*S_3*S_4, S_1*S_2*S_3, S_1*S_2*S_4, S_1*S_3*S_5, 
		       S_2*S_4*S_5, S_3*S_4*S_5 }
IΔ = ideal Δ
kΔ = S/IΔ
fΔ = fVector Δ
d = dim Δ

R = QQ[t]
hΔ = sum for i to d+1 list fΔ#(i-1)*t^i*(1-t)^(d+1-i)
reduceHilbert(hilbertSeries kΔ)

--------------------- Euler characteristic ---------------------------------

sum for i to d list (-1)^i*(fΔ#(i))

---------------- Cohen-Macaulay and Shellability ---------------------------

-- The Zeigler ball is also Cohen-Macaulay, but not shellable. We compute
-- the Cohen-Macaulay property a different way, using B.H 5.3.9

faceList = flatten flatten for i from -1 to dim Δ list entries (faces Δ)#i

totalHomologyRankForLink = (Δ,F) -> (
    linkF := link(Δ, F);
    dL := dim linkF;
    sum for i from -1 to dL-1 list rank (homology link(Δ,F))#i
    ) 

all(faceList, F -> totalHomologyRankForLink(Δ,F) == 0)

-- If not Cohen-Macaulay, find the specific face where this condition fails
for F in faceList do(
    print"--";
    print(F, link(Δ,F), totalHomologyRankForLink(Δ,F))
    )

--------------- Small 2 Manifolds Database -----------------

-- Frank Lutz classified all 2 and 3-manifolds up to 10 vertices. We
-- included his database in the package, which allows for a nice
-- testbed of examples.

-- There are exactly 29 non-shellable 3-manifolds with 9 vertices.
R = ZZ/101[x_0..x_8];
Δ = smallManifold(3,9,18,R)
-- todo demonstrate this using one of the techniques above.

-- We can use databases like this to find examples of maps
S = ZZ/101[y_0..y_6]
Γ = smallManifold(2,7,3,S)
maplist = flatten for i to 4 list (
    for j in subsets(toList(x_0..x_8),7) list (
    	phi := map(smallManifold(3,9,i,R),Γ,j);
    	if isWellDefined phi then phi else continue
    	)
    );
isInjective\maplist

-- Since we have inclusions, we can compute relative homology
-- for these manifolds.
H = homology(target maplist_0, image maplist_0)
prune H

-- Some homology computations.
-- Klein Bottle
-- This triangulation is taken from Theorem 6.3 of Munkres.
T = ZZ[a..k]
KleinBottle = simplicialComplex {a*b*f, a*d*f, d*e*f, e*f*h,
    a*e*h, a*b*h, b*c*f, c*f*g, f*g*j, f*h*j, g*i*j, h*i*j,
    b*h*i, b*c*i, a*c*g, a*e*g, e*g*i, d*e*i, a*d*i, a*c*i}
isWellDefined KleinBottle
prune homology KleinBottle
-- The Klein Bottle can be found in the small manifold database
-- (many times. The smallest example is (2,8,13).


-- Real Projective Space
-- This triangulation comes from Theorem 6.4 of Munkres.
RP2 = simplicialComplex {a*b*g, a*f*g, e*f*g, e*g*i, d*e*i,
    c*d*i, b*c*g, c*g*h, g*h*k, g*i*k, h*j*k, i*j*k, c*i*j,
    b*c*j, c*d*h, d*e*h, e*h*j, e*f*j, a*f*j, a*b*j}
isWellDefined P2
prune homology P2
