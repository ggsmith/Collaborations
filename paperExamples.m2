printWidth=60
restart
needsPackage "SimplicialComplexes";
S = QQ[v..z];
⧓ = simplicialComplex {v*w*x, x*y*z}
I = monomialIdeal ⧓
⧑ = simplicialComplex I
assert(⧓ === ⧑)
ℙ = realProjectiveSpaceComplex(2, R = ZZ[a..h])
for j from 0 to 2 list prune HH_j ℙ
for j from 0 to 2 list prune HH_j kleinBottleComplex R
tally for j from 0 to 1296 list fVector smallManifold(3, 9, j, ZZ[vars(1..9)])
T = smallManifold(2, 7, 1, R = ZZ[a..i])
gens monomialIdeal T
for j from 0 to 2 list prune HH_j T
mapList = for j from 0 to 1296 list (
    phi := map(smallManifold(3, 9, j, R), T, gens R);
    if not isWellDefined phi then continue else phi);
assert(# mapList === 319 and all(mapList, phi -> isInjective phi))
dual ⧓
assert(dual dual ⧓ === ⧓ and dual monomialIdeal ⧓ === monomialIdeal dual ⧓)
monomialIdeal dual ⧓ 
irreducibleDecomposition monomialIdeal ⧓
n = numgens ring ⧓
assert all(-1..n-1, j -> prune HH^(n-j-3) dual ⧓ == prune HH_j ⧓)
L = link(⧓, x)
prune HH_0 L
assert(HH_0 L != 0)
assert(dim(S^1/monomialIdeal ⧓) =!= n - pdim(S^1/monomialIdeal ⧓))
⋈ = skeleton(1, ⧓)
faceList = rsort flatten values faces ⋈
assert all(faceList, F -> (L := link(⋈, F); all(dim L, j -> HH_j L == 0)))
assert(dim(S^1/monomialIdeal ⋈) === n - pdim(S^1/monomialIdeal ⋈))
d = dim ⧓
faces ⧓
fVec = fVector ⧓
hVec = for j from 0 to d list 
    sum(j+1, k -> (-1)^(j-k) * binomial(d+1-k, j-k) * fVec#k)
hilbertSeries(S^1/monomialIdeal ⧓, Reduce => true)
x = getSymbol "x"; S = ZZ[x_0..x_3];
Δ = simplicialComplex{x_0*x_1*x_2, x_2*x_3}
chainComplex Δ
y = getSymbol "y"; R = QQ[y_0..y_3, DegreeRank => 4];
J = ideal(y_0*y_1, y_0*y_2, y_0*y_3, y_1*y_2*y_3)
C = chainComplex(Δ, Labels => J_*)
C.dd
assert(res(R^1/J) == C)
C' = chainComplex(Δ, Labels => reverse J_*)
prune homology C'
J' = monomialIdeal(y_1*y_3, y_2^2, y_0*y_2, y_1^2, y_0^2);
T = taylorResolution J'
gensJ' = first entries mingens J'
S = ZZ[x_0..x_4];
assert(T == chainComplex(simplexComplex(4, S), Labels => first entries mingens J'))
assert(lyubeznikSimplicialComplex(J', S) === simplexComplex(4, S))
Γ = buchbergerSimplicialComplex(J',S)
B = buchbergerResolution J'
assert all(3, i -> HH_(i+1) B == 0) 
assert(betti B == betti res J')
assert(B == chainComplex(Γ, Labels => first entries mingens J'))
assert(Γ === lyubeznikSimplicialComplex(J', S, MonomialOrder => {2,1,0,3,4}))
assert(Γ === scarfSimplicialComplex(J', S))


