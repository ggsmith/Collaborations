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

--
for j to d list(
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
sum for i to d+1 list fΔ#(i-1)*t^i*(1-t)^(d+1-i)
reduceHilbert(hilbertSeries kΔ)

--------------------- Euler characteristic ---------------------------------

sum for i to d list (-1)^i*(fΔ#(i))

---------------- Cohen-Macaulay and Shellability ---------------------------

-- The Zeigler ball is also Cohen-Macaulay, but not shellable. We compute
-- the Cohen-Macaulay property a different way, using B.H 5.3.9


faceList = flatten flatten for i to dim Δ list entries (faces Δ)#i

homologyRankForLink = (Δ,F) -> (
    linkF := link(Δ, F);
    dL := dim linkF;
    dF := #support F;
    sum for i from -1 to dL-dF-2 list rank (homology link(Δ,F))#i
    ) 

all(faceList, F -> homologyRankForLink(Δ,F) == 0)

