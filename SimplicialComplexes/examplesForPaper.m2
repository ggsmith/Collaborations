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

-- In the paper, swap the roles of R and S for all the examples.

-- We homogenize a simplicial complex Δ by labelling the vertices
-- with monomials.

-- All simplicial complexes are defined over S and all monomial ideals 
-- are defined over R.
S = ZZ/101[x_0..x_13]
R = QQ[y_0..y_3]

-- Give a simplicial complex Δ and a monomial ideal I where the number of
-- minimial generators of I is the same as the number of vertices of
-- Δ, we can construct construct a chain complex of R-modules, by
-- I-homogenization of C(Δ,F).

Δ = simplicialComplex{S_0*S_1*S_2, S_2*S_3}
I = monomialIdeal(R_0*R_1, R_0*R_2, R_0*R_3, R_1*R_2*R_3)
M = first entries mingens I
chainComplex(Δ, Labels => M)

-- In this example, Δ supports the minimal free resolution of I. We can
-- verify computationally,

(res I) == (chainComplex(Δ, Labels => M_{2,1,0,3}))

-- However, the fact that the res method choose the same basis when
-- it constructs the minimal free resolution is a stroke of luck.
-- In general, if you wanted to verify that chaincomplex(Δ, Labels => M)
-- is the minimal free resolution, you can compute the
-- homology of the complex or show that the entries in the differential
-- matrices are all contained in (R_0,...,R_3). Alternatively, you can
-- show that for every monomial m in the LCM-lattice of I, the induced
-- subcomplex on the vertices whose label divides m is an acyclic
-- simplicial complex.

lcmLattice = unique sort apply(remove(subsets M, 0), m -> lcm m)

for m in lcmLattice list(
    vertexList := for i to #(vertices Δ)-1 list(
	if m % M_i == 0 then S_i else continue
	);
    prune homology inducedSubcomplex(Δ,vertexList)
    )

-- The homogenization process is sensitive to how you label the vertices,
-- and therefore sensitive to the ordering of the list monomials you 
-- inpute as labels.

prune homology chainComplex(Δ, Labels => M)
prune homology chainComplex(Δ, Labels => reverse M)

------------------------- Known Constructors ------------------------------

------------------------- Taylor Resolution -------------------------------

-- Because every induced subcomplex of a simplex is acyclic, every 
-- I-homogeniztion of a simplex returns a free resolution, which is known
-- as the Taylor resolution of I. This resolution is often not minimal. 

-- Same ideal as previous example.

I = monomialIdeal(R_0*R_1, R_0*R_2, R_0*R_3, R_1*R_2*R_3)
T = taylorResolution I

-- This method is already implemented in the chain complex extras package.
-- The version of taylorResolution in ChainComplex extras is that it
-- is computing the Koszul complex on the minimal generators of I, 
-- where as our method is I-homogenizing a simplex. They typically wont 
-- have the same output as our method used mingens I and the
-- ChainComplexExtras version uses gens I. This can result in
-- two different orderings of the generators of I.

-- I think that while these two functions are the same, it is worth
-- keeping our version of the same method (currently it has the same name,
-- and I don't plan to change it), since it is build upon the idea of
-- homogenization, and therefore, the output is completely predictable to
-- the user.

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

-- The situation for the scarfChainComplex is the same as the Taylor
-- resolution, in that it is implemented in ChainComplexExtras
-- (although ChainComplexExtras does not compute the scarf chain complex),
-- but now we have different naming conventions. However,
-- I feel that our implementation is better, because it is
-- constructed as the homogenization of the scarf simplicial complex,
-- and the output is predictable to the user. Meaning if you compute
-- the scarf simplicial complex by hand and homogenize, the choice of
-- basis in the m2 computation is the same as the "by hand" computation.
-- It is unclear to me how the ChainComplexExtras version computes the
-- basis for the chain complex.

(scarfChainComplex(nearlyScarfΔ)
    == chainComplex(scarfSimplicialComplex(nearlyScarfΔ, S), Labels => M))

------------------------ Buchberber Complex -------------------------------

-- If I is a square-free monomial ideal, then the Buchberger resolution is
-- the taylor resolution.
R = QQ[y_0..y_3]
I = monomialIdeal(R_0*R_1, R_0*R_2, R_0*R_3, R_1*R_2*R_3)
taylorResolution I == buchbergerResolution I

-- Otherwise, the buchberger produces a subcomplex of the Taylor resolution
-- where you only keep faces in which no monomial generator "properly"
-- divides the label of that face.

J = monomialIdeal(R_0^2, R_1^2, R_2^2, R_0*R_2, R_1*R_3)
buchbergerSimplicialComplex(J,S)
buchbergerResolution J
prune homology buchbergerResolution J

-- When the BuchbergerResolution is a minimal free resolution, then
-- the scarf simplicial complex and buchberger simplicial complex coincide

facets scarfSimplicialComplex(J,S) == facets buchbergerSimplicialComplex(J, S)
scarfChainComplex J == buchbergerResolution J

----------------------- Lyubeznik Resolution ------------------------------

-- The Lyubeznik resolution is one where you are given a monomial ideal I
-- and a total ordering on the generators (any total ordering works). You
-- then use a divisibility condition to find all of the "rooted faces" of
-- the Taylor resolution. Keeping just the rooted faces returns a simplicial
-- complex that supports a resolution of I. The resolution you get is dependent
-- on the total ordering you use to begin with. We deal with the total ording
-- by either using an ordered list as input, or by inputing the ideal and 
-- an option MonomialOrder which takes a list and reorders the set mingens I.

-- The default ordering convention for lyubeznikSimplicial Complex is
I = monomialIdeal(R_0^2, R_0*R_1, R_1^3)
(facets lyubeznikSimplicialComplex(I,S) 
    === facets lyubeznikSimplicialComplex(first entries mingens I, S))

-- We can compute all of the Lyubeznik simplicial Complexes, to see how
-- many unique resolutions we construct. 
for P in permutations 3 do(
    print "--";
    print lyubeznikSimplicialComplex(I, S, MonomialOrder => P)
    )

-- We see that there are two, and they correspond to the following
-- orderings of mingens I. The first returns the Taylor resolution
-- of I and the latter returns the scarfChainComplex I
(lyubeznikResolution({R_0^2, R_0*R_1, R_1^3})).dd
(lyubeznikResolution({R_0*R_1, R_0^2, R_1^3})).dd

lyubeznikResolution({R_0^2, R_0*R_1, R_1^3}) == taylorResolution {R_0^2, R_0*R_1, R_1^3}
lyubeznikResolution({R_0*R_1, R_0^2, R_1^3}) == scarfChainComplex I

----------------------------------------------------------------------------------------------------

--------------- Small 2 Manifolds Database -----------------

-- Frank Lutz classified all 2 and 3-manifolds up to 10 vertices. We
-- included his database in the package, which allows for a nice
-- testbed of examples.

-- We can use databases like this to find examples of maps
S = ZZ[y_0..y_8]
Γ = smallManifold(3,9,1,S)
maplist = flatten for i to 4 list (
    for j in subsets(toList(x_0..x_8),7) list (
    	phi := map(smallManifold(3,9,i,R),Γ,j);
    	if isWellDefined phi then phi else continue
    	)
    );
netList maplist
-- By our construction, these should be inclusions.
isInjective\maplist
-- Since we have inclusions, we can compute relative homology between
-- these manifolds.
relhoms = for i to length maplist - 1 list prune homology(target maplist_i, image maplist_i);
netList relhoms

-- Some homology computations.
-- The Klein Bottle can be found in the small manifold database
-- (many times. The smallest example is (2,8,13).
KleinBottle = smallManifold(2, 8, 12, R)
prune homology KleinBottle
-- And real projective space:
RP2 = smallManifold(2, 6, 1, R)
prune homology RP2
-- Theorem 6.3 and 6.4 from Munkres confirm that these are
-- the correct homology groups.

-- Perhaps not useful anymore:
-- This triangulation of the Klein bottle is taken from 
-- Theorem 6.3 of Munkres.
T = ZZ[a..k]
KleinBottle = simplicialComplex {a*b*f, a*d*f, d*e*f, e*f*h,
    a*e*h, a*b*h, b*c*f, c*f*g, f*g*j, f*h*j, g*i*j, h*i*j,
    b*h*i, b*c*i, a*c*g, a*e*g, e*g*i, d*e*i, a*d*i, a*c*i}
isWellDefined KleinBottle
prune homology KleinBottle

-- This triangulation of real projective space comes from 
-- Theorem 6.4 of Munkres.
RP2 = simplicialComplex {a*b*g, a*f*g, e*f*g, e*g*i, d*e*i,
    c*d*i, b*c*g, c*g*h, g*h*k, g*i*k, h*j*k, i*j*k, c*i*j,
    b*c*j, c*d*h, d*e*h, e*h*j, e*f*j, a*f*j, a*b*j}
isWellDefined RP2
prune homology RP2


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

S = QQ[x_0..x_4]
Δ = simplicialComplex{S_0*S_1, S_0*S_2, S_1*S_2, S_2*S_3, S_2*S_4, S_3*S_4}
IΔ = ideal Δ
res IΔ
betti res IΔ
betti res dual(monomialIdeal IΔ)

M = first entries mingens IΔ
lcmLattice = unique sort apply(remove(subsets M, 0), m -> lcm m)

hochster = (i, m) -> (
    barF := product select(vertices Δ, v -> not member(v, support m));
    rank (homology link(dual Δ, barF_S))_i
    )

matrix for i from -1  to length res IΔ - 2 list(
    for m in lcmLattice list(
	hochster(i,m)
	)
    )



F = lcmLattice#-2
barF = product select(vertices Δ, v -> not member(v, support F))
facets dual Δ

link(dual Δ, barF_S)
prune homology link(dual Δ, barF)

---------------------hopf----------------------------------
restart
needsPackage"SimplicialComplexes"

S = ZZ[a_0, a_1, a_2, b_0, b_1, b_2, c_0, c_1 ,c_2, d_0, d_1, d_2]
R = ZZ[w,x,y,z]

threeSphere = simplicialComplex{
    a_0*b_0*c_0*c_2, a_0*a_2*b_0*c_2, a_2*b_0*b_2*c_2, a_2*b_1*b_2*c_2, a_2*b_1*c_1*c_2, 
    a_1*a_2*b_1*c_1, a_0*a_1*b_1*c_1, a_0*b_0*b_1*c_1, a_0*b_0*c_0*c_1,  
    b_1*c_2*d_0*d_1, a_0*c_2*d_0*d_1, a_0*b_1*d_0*d_1, b_1*c_1*c_2*d_1, a_2*c_1*c_2*d_1,
    a_0*a_2*c_2*d_1, b_0*b_1*c_1*d_1, a_0*b_0*b_1*d_1, a_0*a_2*b_0*d_1,
    b_0*c_1*d_1*d_2, a_2*c_1*d_1*d_2, a_2*b_0*d_1*d_2, b_1*c_2*d_0*d_2, a_0*c_2*d_0*d_2,
    a_0*b_1*d_0*d_2, b_0*c_0*c_2*d_2, a_0*c_0*c_2*d_2, b_1*b_2*c_2*d_2, b_0*b_2*c_2*d_2,
    b_0*c_0*c_1*d_2, a_0*c_0*c_1*d_2, a_1*a_2*c_1*d_2, a_0*a_1*c_1*d_2, a_2*b_1*b_2*d_2,
    a_2*b_0*b_2*d_2, a_1*a_2*b_1*d_2, a_0*a_1*b_1*d_2
    }

prune homology threeSphere

twoSphere = simplicialComplex{w*x*y, w*x*z, w*y*z, x*y*z}
p = map(R,S,{w,w,w,x,x,x,y,y,y,z,z,z})
hopfFibration = map(twoSphere, threeSphere, p)
prune homology hopfFibration
circle = simplicialComplex{w*x, x*y, y*w}
i = map(S,R,{a_0, a_1, a_2, 0})
fibre = map(threeSphere,circle,i)




methods homology
