
------------------------ STANLEY RIESNER THEORY ----------------------------

-- Can jettison either the Rudin ball or the Ziegler ball example.
-- Everything I can think to show is covered by one of these together
-- with the projective plane example

-------------------- DUALS, LINKS, HOCHSTER's FORMULA-----------------------
printWidth = 60

restart
needsPackage"SimplicialComplexes"
options SimplicialComplexes

--IΔ = monomialIdeal(x_0*x_3, x_1*x_3, x_0*x_4, x_1*x_4 );

R = QQ[x_0..x_4];
⧓ = simplicialComplex{x_0*x_1*x_2, x_2*x_3*x_4}
I⧓ = ideal ⧓
⧓' = simplicialComplex I⧓;
⧓ === ⧓'
I⧓ == ideal ⧓
dual ⧓
dual(monomialIdeal ⧓) == monomialIdeal dual ⧓
link(dual ⧓, x_2)
link(dual ⧓, x_2) === inducedSubcomplex(dual ⧓, {x_0,x_1,x_3,x_4})

R = QQ[a..j];
zieglerBallComplex R



S = QQ[x_0..x_4];
⋈ = simplicialComplex{x_3*x_4, x_2*x_4, x_2*x_3, x_1*x_2, x_0*x_2, x_0*x_1}
I⋈ = ideal ⋈
⋈' = simplicialComplex I⋈;
⋈ === ⋈'
I⋈ == ideal ⋈

dual ⋈
dual(monomialIdeal ⋈) == monomialIdeal dual ⋈

facets dual ⋈

link(dual ⋈, x_2)
inducedSubcomplex(dual ⋈, {x_0,x_1,x_3,x_4})
dual ⋈

dual simplicialComplex{x_0*x_2*x_3, x_0*x_2*x_4, x_1*x_2*x_3, x_1*x_2*x_4}



ideal ⋈
-- Exhibiting the relation bewtween the Alexander dual of the 
-- Stanley-Reisner and the Alexander dual of the corresponding
-- simplicial complex.

dual Δ
dualFacets = facets dual Δ
sort first entries gens IΔ == sort for F in dualFacets list(
    product for v in vertices Δ list(
	if member(v, support F) then continue else v
	)
    ) 
dual(monomialIdeal Δ) == monomialIdeal dual Δ

-- Simplicial version of Alexander duality and homology.

netList for i from -1 to 5 list{
    prune HH^(3-i)(dual chainComplex Δ), prune HH_(i-1) dual Δ
    }

all(-1..5, i -> prune HH^(3-i)(dual chainComplex Δ) == prune HH_(i-1) dual Δ)

all(-1..5, i -> prune HH^(3-i) Δ == prune HH_(i-1) dual Δ)

-- Computing link in the bowtie complex

netList for i to #vertices dual Δ - 1 list{x_i, link(dual Δ, x_i)}
link(dual Δ, x_2)

-- Hochster's Formula (dual version)

M = first entries mingens IΔ
lcmLattice = unique sort apply(remove(subsets M, 0), m -> lcm m)

hochster = (i, F) -> (
    G := product select(vertices Δ, v -> not member(v, support F));
    rank (homology link(dual Δ, G_S))_i
    )
V = vertices Δ;
squarefreeMonomials = unique sort apply(remove(subsets V, 0), m -> lcm m);
matrix for i to length res IΔ - 1 list (
    for F in squarefreeMonomials list hochster(i-1,F)
    )

hochster(1, S_0^3*S_1*S_2*S_3*S_4)

res IΔ

betti res IΔ
betti res dual(monomialIdeal IΔ)

F = lcmLattice#-2
barF = product select(vertices Δ, v -> not member(v, support F))
facets dual Δ

link(dual Δ, barF_S)
prune homology link(dual Δ, barF)

d = dim Δ
fΔ = fVector Δ
hΔ = for j to d+1 list(
    sum for i to j list (-1)^(j-i)*binomial(d+1-i,j-i)*(fΔ#(i))
    )

-- There is a criterion for an h-vector to be the h-vector of some
-- Cohen-Macaulay complex. We can use this to verify that a simplicial
-- complex is not Cohen-Macaulay. In particual, if the h-vector has a
-- negative entry, the complex cannot be Cohen-Macaulay.
needsPackage"LexIdeals"
netList for i from 1 to length hΔ - 2 list{hΔ_i, hΔ_(i+1), macaulayBound(hΔ_i,i)}

restart
needsPackage"SimplicialComplexes"
S = QQ[x_0..x_4];

I⧓ = monomialIdeal(x_0*x_3, x_1*x_3, x_0*x_4, x_1*x_4 );
⧓ = simplicialComplex I⧓;
k⧓ = S/I⧓;
d = dim ⧓;
f⧓ = fVector ⧓
h⧓ = for j to d+1 list(
    sum for i to j list (-1)^(j-i)*binomial(d+1-i,j-i)*(f⧓#(i))
    )


R = QQ[t]
hΔ = sum for i to d+1 list fΔ#(i) * t^i * (1-t)^(d+1-i)
reduceHilbert(hilbertSeries kΔ)


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

sum for i from 1 to d+1 list (-1)^(i+1)*(fΔ#i)
1 + sum for i to d list (-1)^i*(rank homology(i,Δ))

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

sum for i from 1 to d+1 list (-1)^(i+1)*(fΔ#i)
1 + sum for i to d list (-1)^i*(rank homology(i,Δ))

---------------- Cohen-Macaulay and Shellability ---------------------------

-- The Zeigler ball is also Cohen-Macaulay, but not shellable. We compute
-- the Cohen-Macaulay property a different way, using B.H 5.3.9

faceList = flatten for i from -1 to dim Δ list (faces Δ)#i
all(faceList, F -> all(0..dim(link(Δ,F))-1, i -> HH_i link(Δ,F) == 0))

homologyRankForLink = (Δ,F,i) -> (
    linkF := link(Δ, F);
    dL := dim linkF;
    sum for i from -1 to dL-1 list rank (homology link(Δ,F))#i
    ) 

HH_2(link(Δ,x_2))

all(faceList, F -> totalHomologyRankForLink(Δ,F) == 0)



-- needsPackage"SimplicialDecomposability"

------------- PROJECTIVE PLANE IN CHARACTERISTIC 2-------------------------

-------------------------- h-vector ---------------------------------------

S = ZZ/2[x_0..x_5]
-- RP2 is in the small manifolds database.
Δ = smallManifold(2,6,1,S);

IΔ = ideal Δ
kΔ = S/IΔ
fΔ = fVector Δ
d = dim Δ

R = QQ[t]
hΔ = sum for i to d+1 list fΔ#(i) * t^i * (1-t)^(d+1-i)
reduceHilbert(hilbertSeries kΔ)

hΔ = for j to d+1 list(
          sum for i to j list (-1)^(j-i)*binomial(d+1-i,j-i)*(fΔ#(i))
          )

needsPackage"LexIdeals"
netList for i to 2 list{hΔ_(i+1), macaulayBound(hΔ_i,i)}

viewHelp macaulayBound

--------------------- Euler characteristic ---------------------------------

sum for i from 1 to d+1 list (-1)^(i+1)*(fΔ#i)
1 + sum for i to d list (-1)^i*(rank homology(i,Δ))


---------------- Cohen-Macaulay and Shellability ---------------------------

-- This complex is not Cohen-Macaulay over a field of characteristic 2. We
-- show this using Bruns-Herzog 5.3.9

faceList = flatten flatten for i from -1 to dim Δ list entries (faces Δ)#i

totalHomologyRankForLink = (Δ,F) -> (
    linkF := link(Δ, F);
    sum for i from -1 to dim(linkF) - 1 list rank (homology link(Δ,F))#i
    ) 

all(faceList, F -> totalHomologyRankForLink(Δ,F) == 0)

-- If not Cohen-Macaulay, find the specific face where this condition fails
for F in faceList do(
    print"--";
    print(F, link(Δ,F), totalHomologyRankForLink(Δ,F))
    )

----------------- Computing the Poincare Series of P1 x P1 -----------------

-- We can obtain P1 x P1 by considering the corresponding toric variety
-- to a square with vertices (0,0), (1,0), (0,1), and (1,1).
-- TODO

----------- HOMONGENIZATION AND RESOLUTIONS OF MONOMIAL IDEALS -------------
restart
needsPackage"SimplicialComplexes"

----------------Homogenization Of A Simplicial Complex ---------------------

R = ZZ/101[y_0..y_13];
S = QQ[x_0..x_3];
Δ = simplicialComplex{R_0*R_1*R_2, R_2*R_3};
I = ideal(x_0*x_1,x_0*x_2,x_0*x_3,x_1*x_2*x_3);
C = chainComplex Δ
G = chainComplex(Δ, Labels => {x_0*x_1,x_0*x_2,x_0*x_3,x_1*x_2*x_3});
G.dd
(res (S^1/I)) == G


G' = chainComplex(Δ, Labels => {x_1*x_2*x_3,x_0*x_2,x_0*x_3,x_0*x_1});
prune homology G'




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

------------------------- The Scarf Complex --------------------------------

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

------------------------ Buchberger Complex -------------------------------

restart
needsPackage"SimplicialComplexes"

-- If I is a square-free monomial ideal, then the Buchberger resolution is
-- the taylor resolution.
R = QQ[a,b,c,d,e];
S = QQ[x_0..x_3];
J = monomialIdeal(S_1*S_3, S_2^2,  S_0*S_2, S_1^2, S_0^2);
T = taylorResolution J
T == chainComplex(simplexComplex(4,R),Labels => first entries mingens J)
buchbergerSimplicialComplex(J,R)
B = buchbergerResolution J
prune homology B
betti B === betti(res J)
lyubeznikSimplicialComplex(J,R)
lyubeznikResolution(J) == taylorResolution(J)
lyubeznikSimplicialComplex(J, R, MonomialOrder => {2,1,0,3,4})
L = lyubeznikResolution(J,MonomialOrder => {2,1,0,3,4})
betti L == betti B
scarfSimplicialComplex(J,R)
scarfChainComplex J == buchbergerResolution J







buchbergerSimplicialComplex(J,R) === lyubeznikSimplicialComplex(J, R, MonomialOrder => {2,1,0,3,4})

for P in permutations 5 do(
    print "------------------";
    print P;
    print "--";
    print(lyubeznikSimplicialComplex(J, R, MonomialOrder => P))
    )


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
-- TODO: the homology in these is boring. maybe keep searching for something
-- better?
restart
needsPackage "SimplicialComplexes"
R = ZZ[a..i];
S = ZZ[x_0..x_6];
Γ = smallManifold(2,7,1,S);
maplist = for j in subsets(toList(a..i),7) list (
    phi := map(smallManifold(3,9,1,R),Γ,j);
    if isWellDefined phi then phi else continue
    );
netList maplist
-- By our construction, these should be inclusions.
isInjective\maplist

-- Some homology computations.
-- The torus, Klein Bottle, and real projective plane can be found 
-- in the small manifold database (many times). The smallest example is (2,8,13)).
Torus = smallManifold(2, 7, 6, R);
matrix {facets Torus}
KleinBottle = smallManifold(2, 8, 12, R);
RP2 = smallManifold(2, 6, 1, R);
-- Theorems 6.2, 6.3, and 6.4 from Munkres confirm that these are
-- the correct homology groups.
for i to 2 list prune HH_i Torus
for i to 2 list prune HH_i KleinBottle
for i to 2 list prune HH_i RP2

-- To see the generators for the
-- H^1 of the torus, we embed circles into this minimal triangulation.

T = ZZ[y_0..y_2];
Circle = skeleton(1, simplexComplex(2,T));

-- Corresponds to one of the generators of H^1
f1 = map(Torus,Circle,matrix{{d,g,f}});
prune homology(1, f1)
-- prune homology(1, Torus, image f1)
-- faces(1,Circle),(chainComplex f1)_1,transpose faces(1,Torus)

-- Corresponds to the Other generator of H^1
f2 = map(Torus,Circle,matrix{{d,a,c}});
prune homology(1, f2)
-- prune homology(1, Torus, image f2)
-- faces(1,Circle),(chainComplex f2)_1,transpose faces(1,Torus)

h = map(Torus,Circle,matrix{{S_3,S_1,S_1,S_4,S_4,S_3}})
chainComplex h
prune homology h
image h
prune homology(Torus, image h)
--faces(1,Circle),(chainComplex h)_1,transpose faces(1,Torus)

g = map(Torus,Circle,matrix{{S_3,S_1,S_4,S_3,S_0,S_2}})
chainComplex g
prune homology g
image g
prune homology(Torus, image g)
-- faces(1,Circle),(chainComplex g)_1,transpose faces(1,Torus)

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
prune homology fibre


  
viewHelp


L = {{ 1, 2, 4 }, { 1, 2, 7 }, { 1, 2, 8 }, { 1, 3, 4 }, { 1, 3, 5 },
    { 1, 3, 6 }, { 1, 5, 6 }, { 1, 7, 8 }, { 2, 3, 5 }, { 2, 3, 7 }, { 2, 3, 8 }, 
    { 2, 4, 5 }, { 3, 4, 8 }, { 3, 6, 7 }, { 4, 5, 6 }, { 4, 6, 8 }, { 6, 7, 8 }
    }

for F in L list(
    product for v in F list S_(v-1)
    )

viewHelp

