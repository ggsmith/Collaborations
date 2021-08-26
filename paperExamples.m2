printWidth=60
restart
needsPackage "SimplicialComplexes";
S = QQ[x_0..x_4];
⧓ = simplicialComplex {x_0*x_1*x_2, x_2*x_3*x_4}
I = monomialIdeal ⧓
⧓' = simplicialComplex I
assert(⧓ === ⧓')
--
ℙ = realProjectiveSpaceComplex(2, R = ZZ[a..h])
for j from 0 to 2 list prune HH_j ℙ
for j from 0 to 2 list prune HH_j kleinBottleComplex R
--
tally for j from 0 to 1296 list 
    fVector smallManifold(3, 9, j, ZZ[vars(1..9)])
--
T = smallManifold(2, 7, 1, R = ZZ[a..i])
gens monomialIdeal T
for j from 0 to 2 list prune HH_j T
mapList = for j from 0 to 1296 list (
    phi := map(smallManifold(3, 9, j, R), T, gens R);
    if not isWellDefined phi then continue else phi);
# mapList
assert all(mapList, phi -> isInjective phi)
--
dual ⧓
assert(dual dual ⧓ === ⧓)
assert(dual monomialIdeal ⧓ === monomialIdeal dual ⧓)
monomialIdeal dual ⧓ 
irreducibleDecomposition monomialIdeal ⧓
n = numgens ring ⧓;
assert all(-1..n-1, j -> prune HH^(n-j-3) dual ⧓ == prune HH_j ⧓)
--
L = link(⧓, x_2)
prune HH_0 L
--
dim L
facets L
--
assert(HH_0 L != 0)
assert(dim(S^1/monomialIdeal ⧓) =!= n - pdim(S^1/monomialIdeal ⧓))
⋈ = skeleton(1, ⧓)
faceList = rsort flatten values faces ⋈
assert all(faceList, F -> (L := link(⋈, F); all(dim L, j -> HH_j L == 0)))
assert(dim(S^1/monomialIdeal ⋈) === n - pdim(S^1/monomialIdeal ⋈))
--
d = dim ⧓
faces ⧓
fVec = fVector ⧓
hVec = for j from 0 to d list 
    sum(j+1, k -> (-1)^(j-k) * binomial(d+1-k, j-k) * fVec#k)
hilbertSeries(S^1/monomialIdeal ⧓, Reduce => true)

