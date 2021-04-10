restart
needsPackage"SimplicialComplexes"

------------------------ STANLEY RIESNER THEORY ----------------------------

-- Can jettison either the Rudin ball or the Ziegler ball example.
-- Everything I can think to show is covered by one of these together
-- with the projective plane example

-------------------------------RUDIN BALL-----------------------------------

---------------------------- General Setup ---------------------------------

S = QQ[x_0..x_13]
Δ = rudinBallComplex S
d = dim Δ

-- Stanley-Riesenr ideal and Stanley-Riesner ring of Δ
IΔ = ideal Δ
kΔ = S/IΔ

------------------------- f-vector And h-vector ----------------------------

fΔ = fVector Δ

-- computing h-vector
hΔ = for j to d+1 list(
    sum for i to j list (-1)^(j-i)*binomial(d+1-i,j-i)*(fΔ#(i))
    )

-- Here is another formula for computing the h-vector from the f vector. The
-- coefficients of t^k is the kth entry in the h-vector
R = QQ[t]
sum for i to d+1 list fΔ#(i)*t^i*(1-t)^(d+1-i)

-- We can compare to the numerator of the hilbert series of kΔ
reduceHilbert(hilbertSeries kΔ)

------------------------- Euler characteristic -----------------------------

sum for i to d list (-1)^i*(fΔ#(i+1))

----------------- Cohen-Macaulay And Shellability -------------------------

-- Δ is Cohen-Macaulay but not shellable.

-- depth kdim(S^1/IΔ) is the left-hand side, given by the Auslander-Buchsbaum
-- formula. dim kΔ is the right-hand side.

dim S - pdim(S^1/IΔ) == dim(S^1/IΔ)

-- This is not shellable because ???

facetsList = (first entries facets Δ)
F = facetsList#3
L = delete(F,facetsList)
Γ = simplicialComplex L
prune homology Γ
sum for i to d list rank (prune homology Γ)#i

-- There is an alogrithm implemented  in the SimplicialDecomposability 
-- package that determines if a simplicial complex is shellable.
-- However, determining if a simplicial complex is shellable is an 
-- NP-hard problem, and therefore this algorithm is inherently slow. 
-- There is a topological proof outlined in the paper by rudin, which 
-- uses homeomorphisms of toplogical space.    

-- needsPackage"SimplicialDecomposability"


--------------------------- ZIEGLER BALL ----------------------------------

-------------------------- h-vector ---------------------------------------

S = QQ[x_0..x_9]
Δ = zieglerBallComplex S
IΔ = ideal Δ
kΔ = S/IΔ
fΔ = fVector Δ
d = dim Δ

R = QQ[t]
hΔ = sum for i to d+1 list fΔ#(i) * t^i * (1-t)^(d+1-i)
reduceHilbert(hilbertSeries kΔ)

--------------------- Euler characteristic ---------------------------------

sum for i to d list (-1)^i*(fΔ#(i+1))

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

------------- PROJECTIVE PLANE IN CHARACTERISTIC 2-------------------------

-------------------------- h-vector ---------------------------------------

S = ZZ/2[x_0..x_5]
Δ = simplicialComplex{ S_0*S_1*S_4, S_0*S_1*S_5, S_0*S_2*S_3, S_0*S_2*S_5,
                       S_0*S_3*S_4, S_1*S_2*S_3, S_1*S_2*S_4, S_1*S_3*S_5, 
		       S_2*S_4*S_5, S_3*S_4*S_5 }

IΔ = ideal Δ
kΔ = S/IΔ
fΔ = fVector Δ
d = dim Δ

R = QQ[t]
hΔ = sum for i to d+1 list fΔ#(i) * t^i * (1-t)^(d+1-i)
reduceHilbert(hilbertSeries kΔ)

--------------------- Euler characteristic ---------------------------------

sum for i to d list (-1)^i*(fΔ#(i+1))

---------------- Cohen-Macaulay and Shellability ---------------------------

-- This complex is not Cohen-Macaulay over a field of characteristic 2. We
-- show this using Bruns-Herzog 5.3.9

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

----------- HOMONGENIZATION AND RESOLUTIONS OF MONOMIAL IDEALS -------------
restart
needsPackage"SimplicialComplexes"

----------------Homogenization Of A Simplicial Complex ---------------------

-- We homogenize a simplicial complex Δ by labelling the vertices
-- with monomials.

-- All simplicial complexes are defined over S and all monomial ideals 
-- are defined over R.
S = ZZ/101[x_0..x_13]
R = QQ[y_0..y_3]

Δ = simplicialComplex{S_0*S_1*S_2, S_2*S_3}
I = monomialIdeal(R_0*R_1, R_0*R_2, R_0*R_3, R_1*R_2*R_3)

M = first entries mingens I
chainComplex(Δ, Labels => M)

(res I).dd == (chainComplex(Δ, Labels => M_{2,1,0,3})).dd

prune homology chainComplex(Δ, Labels => M)
prune homology chainComplex(Δ, Labels => reverse M)

------------------------- Known Constructors ------------------------------

------------------------- Taylor Resolution -------------------------------

I = monomialIdeal(R_0*R_1, R_0*R_2, R_0*R_3, R_1*R_2*R_3)

T = taylorResolution I
T == chainComplex(simplexComplex(numgens I - 1, S), Labels => M)
prune homology T

------------------------- The Scarf Compex ---------------------------------

-- We define a 1-dimensional simplicial complex homeomorphic to a
-- "figure 8"
S = ZZ/101[x_0..x_13]
Δ = simplicialComplex{S_0*S_1, S_0*S_2, S_1*S_2, S_2*S_3, S_2*S_4, S_3*S_4}

-- The nearly Scarf ideal of a simplicial complex is constructed in a
-- ring where the number of variables is the number of faces of Δ.

faceList = flatten for i to dim Δ list first entries (faces Δ)#i
numFaces = #faceList
R = QQ[y_0 .. y_(numFaces-1)]

-- For each variable v in Δ we determine a squarefree monomial where 
-- the variables that appear correspond to faces that do not contain
-- the vertex v.
nearlyScarfΔ = monomialIdeal(for v in first entries(faces Δ)#0 list(
    	product for F in faceList list(
	    if F%v == 0
	    then continue
	    else R_(position(faceList, G -> G == F))
    	    )
    	)
    )

-- The scarf complex, or scarf simplicial complex of nearlyScarfΔ
-- is Δ. To see this, We reorder the generators of our ideal to
-- correspond to the the order of the vertices of Δ.
M = first entries mingens nearlyScarfΔ
Γ = scarfSimplicialComplex(M_{1,2,0,3,4}, S)
facets Γ == facets Δ

-- The scarfChainComplex of an ideal I is the homogenization of
-- scarfSimplicialComplex by the generators of I.
(scarfChainComplex(nearlyScarfΔ)).dd
prune homology scarfChainComplex(nearlyScarfΔ)

-- Verifying the the Scarf complex is a homogenization.
(scarfChainComplex(nearlyScarfΔ)
    == chainComplex(scarfSimplicialComplex(nearlyScarfΔ, S), Labels => M))

------------------------ Buchberber Complex -------------------------------

-- If I is a square-free monomial ideal, then the Buchberger resolution is
-- the taylor resolution.
R = QQ[y_0..y_3]
I = monomialIdeal(R_0*R_1, R_0*R_2, R_0*R_3, R_1*R_2*R_3)

taylorResolution I == buchbergerResolution I

J = monomialIdeal(R_0^2, R_1^2, R_2^2, R_0*R_2, R_1*R_3)
buchbergerSimplicialComplex(J,S)
buchbergerResolution J
prune homology buchbergerResolution J

----------------------- Lyubeznik Resolution ------------------------------

I = monomialIdeal(R_0^2, R_0*R_1, R_1^3)
for P in permutations 3 do(
    print "--";
    print lyubeznikSimplicialComplex(I, S, MonomialOrder => P)
    )

(lyubeznikResolution({R_0^2, R_0*R_1, R_1^3})).dd
(lyubeznikResolution({R_0*R_1, R_0^2, R_1^3})).dd

----------------------------------------------------------------------------------------------------

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


---------------------- SCRAP WORK -----------------------------
restart
needsPackage"SimplicialComplexes"

S = QQ[x_0..x_10]
Δ = smallManifold(3,9,17,S)
d = dim Δ

-- ideal and Stanley-Riesner ring of Δ
IΔ = ideal Δ
kΔ = S/IΔ

------------------------- f-vector And h-vector ----------------------------

fΔ = fVector Δ

-- computing h-vector
hΔ = for j to d+1 list(
    sum for i to j list (-1)^(j-i)*binomial(d+1-i,j-i)*(fΔ#(i))
    )

-- Here is another formula for computing the h-vector from the f vector. The
-- coefficients of t^k is the kth entry in the h-vector
R = QQ[t]
sum for i to d+1 list fΔ#(i)*t^i*(1-t)^(d+1-i)

-- We can compare to the numerator of the hilbert series of kΔ
reduceHilbert(hilbertSeries kΔ)



----------------------------------------------------------------------------

