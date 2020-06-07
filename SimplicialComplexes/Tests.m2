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
-- Simplicial Complexes Tests
------------------------------------------------------------------------------
TEST ///
S = QQ[x_{1,1}..x_{2,4}, Degrees => {{1,0,0,0},{0,1,0,0},{0,0,1,0},{0,0,0,1},{1,0,0,0},{0,1,0,0},{0,0,1,0},{0,0,0,1}}]
I = monomialIdeal(x_{1,1}*x_{2,1},x_{1,2}*x_{2,2},x_{1,3}*x_{2,3},x_{1,4}*x_{2,4})
D = simplicialComplex(I)
assert( (fVector(D))#2 == 32)
-- assert( (fVector(D, Flag => true))#{1,1,0,0} == 4)
///

------------------------------------------------------------------------------
-- Test
TEST ///
R1 = QQ[x,y,z]
S1 = simplicialComplex {x*y*z}
R2 = QQ[a,b]
S2 = simplicialComplex {a,b}
J = S1 * S2
T = ring J
assert((fVector(S1 * S2))#1 == (fVector(S1))#1 + (fVector(S1))#0*(fVector(S2))#0)
assert(star(J, x*y*z) === J)
assert(#(flatten entries facets(star(J, a))) == 1)
///

------------------------------------------------------------------------------
-- Real Projective plane
TEST ///
R = ZZ[a..f]
RP2 = simplicialComplex monomialIdeal(a*b*c,a*b*f,a*c*e,a*d*e,a*d*f,b*c*d,b*d*e,b*e*f,c*d*f,c*e*f)
skel = skeleton(1, RP2)
-- removing facets creates holes captured by HH_1
assert(rank HH_1 skel == (fVector(RP2))#2)
assert(dim skel == 1)
S = ZZ[v]
v = simplicialComplex {v}
-- the cone is contractible
conewrtv = joinSimplicial(v, RP2)
assert(prune HH_1 conewrtv == 0)
///

------------------------------------------------------------------------------
-- Example from Betti numbers of strongly color-stable ideals and
-- squarefree strongly color-stable ideals
-- Satoshi Murai
TEST ///
x = getSymbol "x"
grading = {{1,0,0},{1,0,0},{1,0,0},{0,1,0},{0,0,1}}
R = QQ[x_{1,1},x_{1,2},x_{1,3},x_{2,1},x_{3,1}, Degrees => grading]
delta = simplicialComplex({x_{1,3}*x_{2,1}*x_{3,1},x_{1,1}*x_{2,1},x_{1,2}*x_{3,1}})
shifted = algebraicShifting(delta, Multigrading => true)
assert((fVector(delta))#0 == (fVector(shifted))#0)
assert((fVector(delta))#1 == (fVector(shifted))#1)
assert((fVector(delta))#2 == (fVector(shifted))#2)
assert(prune homology delta != prune homology shifted)
///


------------------------------------------------------------------------------
-- Boundary of the 4-Cross-Polytope
TEST ///
grading = {{1,0,0,0},{0,1,0,0},{0,0,1,0},{0,0,0,1},{1,0,0,0},{0,1,0,0},{0,0,1,0},{0,0,0,1}}
S = QQ[x_{1,1}..x_{2,4}, Degrees => grading]
I = monomialIdeal(x_{1,1}*x_{2,1},x_{1,2}*x_{2,2},x_{1,3}*x_{2,3},x_{1,4}*x_{2,4})
cross = simplicialComplex(I)
assert( (fVector(cross))#2 == 32)
-- assert( (fVector(cross, Flag => true))#{1,1,0,0} == 4)
assert(dim skeleton(2,cross) == 2)
-- assert((fVector(skeleton(2,cross)))#1 == (fVector(cross))#1)
multishifted = algebraicShifting(cross, Multigrading => true)
stdshifted = algebraicShifting(cross)
assert (cross === multishifted)
assert (cross =!= stdshifted)
///


------------------------------------------------------------------------------
-- Cartwright-Sturmfels ideals associated to graphs and linear spaces 
-- Aldo Conca, Emanuela De Negri, Elisa Gorla    Ex. 1.10
TEST ///
row_grading = {{1,0},{1,0},{1,0},{0,1},{0,1},{0,1}}
S=QQ[x_{1,1}..x_{2,3}, Degrees => row_grading]
I = ideal(x_{1,1}*x_{2,1},x_{1,2}*x_{2,2},x_{1,3}*x_{2,2},x_{1,2}*x_{2,3},x_{1,3}*x_{2,3})
multigin = ideal(x_{1,1}^2*x_{2,3},x_{1,1}*x_{1,2}*x_{2,3},x_{1,1}*x_{2,1},x_{1,2}*x_{2,1},x_{1,3}*x_{2,1},x_{1,1}*x_{2,2},x_{1,2}*x_{2,2})
stdgin = ideal(x_{1,1}^2,x_{1,1}*x_{1,2},x_{1,2}^2,x_{1,1}*x_{1,3},x_{1,2}*x_{1,3},x_{1,3}^3,x_{1,3}^2*x_{2,1})
assert(gin(I, AttemptCount => 10, Multigraded => true) == multigin)
assert(gin(I, AttemptCount => 10) == stdgin)
///

------------------------------------------------------------------------------
-- Stacked 3-sphere on 7 vertices
TEST ///
S = QQ[x_1..x_7]
I = monomialIdeal(x_2*x_3*x_4*x_5,x_3*x_4*x_5*x_6,x_1*x_6,x_1*x_7,x_2*x_7)
st73 = simplicialComplex I
shifted = algebraicShifting (st73)
assert( (fVector(st73))#3 == (fVector(shifted))#3)
assert(prune homology st73 == prune homology shifted)
assert(not member(x_1*x_2*x_3*x_4, flatten entries facets(shifted)))
///


------------------------------------------------------------------------------
-- Test
TEST///
S = QQ[a..f]
D = simplicialComplex({a*b*c,b*c*d,d*e*f})
stD = star(D, d)
assert(star(D, d) === simplicialComplex({d*e*f,b*c*d}))
v = getSymbol "v"
T = QQ[v]
conev = stD * simplicialComplex({v})
assert( (fVector(conev))#0 == 6 )
assert( (fVector(conev))#1 == 11 )
assert( (fVector(conev))#2 == 8 )
///


------------------------------------------------------------------------------
TEST ///
R = ZZ[x]
void = simplicialComplex monomialIdeal(1_R)
assert isPure void
assert(dim void == -infinity)
assert(faces(0,void) == 0)
assert(faces(-1,void) == 0)
dual void
C = chainComplex void
assert( C.dd^2 == 0 )
assert(HH_0(void) == 0)
assert(HH_-1(void) == 0)
fVector void
assert(boundary void  === void)
irrelevant = simplicialComplex monomialIdeal gens R
assert isPure irrelevant
assert(dim irrelevant === -1)
assert(faces(0,irrelevant) == 0)
assert(numgens source faces(-1,irrelevant) === 1)
assert(irrelevant === dual irrelevant)
C = chainComplex irrelevant
assert( C.dd^2 == 0 )
assert(HH_0(irrelevant) == 0)
assert(HH_-1(irrelevant) == R^1)
assert(fVector irrelevant === new HashTable from {-1=>1})
assert(boundary irrelevant  === void)
D5 = simplicialComplex {1_R}
D5 === irrelevant
///


------------------------------------------------------------------------------
TEST ///
R = ZZ[x_1..x_4]
D6 = simplicialComplex monomialIdeal gens R
time A6 = dual D6
time C = chainComplex A6;
assert( C.dd^2 == 0 )
C
time prune HH(C)
fVector D6

D7 = simplicialComplex monomialIdeal 1_R
dual D7
fVector D7
///


------------------------------------------------------------------------------
-- Miller and Sturmfels, example 1.8 
TEST ///
R = ZZ[a..e]
D = simplicialComplex monomialIdeal(a*d, a*e, b*c*d, d*e, c*e, b*e)
assert not isPure D
fVector D
ideal dual D == monomialIdeal (a*b*c*d, a*b*e, a*c*e, d*e)
fVector boundary D
boundary D
S = ZZ/32003[u,v,w,x,y]
label(D, {u,v,w,x,y})
C = chainComplex D
assert( C.dd^2 == 0 )
prune HH(C)
label(D,{})
///


------------------------------------------------------------------------------
-- torus  : Munkres page 15 example 3 
TEST ///
R = QQ[a..j]
D = simplicialComplex{a*b*i, a*e*i, i*b*j, j*c*b, j*c*a, j*a*e,
     e*i*f, i*h*f, i*h*j, j*e*d, j*g*d, j*h*g, g*h*f, f*e*d,
     d*f*a, f*b*a, f*g*c, f*b*c, g*c*a, g*d*a}
assert isPure D
C = chainComplex D
assert( C.dd^2 == 0 )
prune HH(C)
D' = dual D
C' = chainComplex D'
assert( C'.dd^2 == 0 )
prune HH(C')
fVector D
boundary D
fVector boundary D
///

------------------------------------------------------------------------------
-- Klein bottle : Munkres page 18 example 5 
TEST ///
kk = ZZ/2
R = kk[a..j]
D = simplicialComplex {a*b*i, a*e*i, b*i*j, b*c*j, a*c*j, 
     a*d*j, e*f*i, f*h*i, h*i*j, d*e*j, e*g*j, g*h*j, 
     f*g*h, d*e*f, a*d*f, a*b*f, c*f*g, b*c*f, a*c*g, a*e*g}
isPure D
C = chainComplex D
assert( C.dd^2 == 0 )
prune HH(C)
fVector D
///


------------------------------------------------------------------------------
-- Degenerations of Abelian surfaces 
-- Gross and Popescu, math.AG/9609001
TEST ///
abelian = (n) -> (
     R := QQ[local x_0..local x_(n-1)];
     L1 = toList apply(0..n-1, i -> x_i * x_((i+3)%n) * x_((i+4)%n));
     L2 = toList apply(0..n-1, i -> x_i * x_((i+1)%n) * x_((i+4)%n));
    join(L1,L2))

D = simplicialComplex abelian 8
numgens source faces(0,D)
numgens source faces(1,D)
numgens source faces(2,D)
numgens source faces(3,D)
C = chainComplex D
assert( C.dd^2 == 0 )
prune HH(C)
transpose gens ideal D     
fVector D
///


------------------------------------------------------------------------------
-- Simplex with labelling 
TEST ///
R = ZZ[a..e]
D = simplicialComplex monomialIdeal product gens R
D = dual simplicialComplex monomialIdeal gens R
S = ZZ/32003[u,v,x,y,z]
L = {x^2, x*y, x*z, y^2, y*z}
label(D,L)
C = chainComplex D
assert( C.dd^2 == 0 )
///


------------------------------------------------------------------------------
-- testing the chain complexes
TEST ///
R = ZZ/101[a..e]
D = simplicialComplex monomialIdeal product gens R
boundary(0,D)
boundary(1,D)
boundary(2,D)
boundary(3,D)
boundary(4,D)
C = chainComplex D
assert( C.dd^2 == 0 )
HH_3(C)
HH_2(C)
prune oo
///


------------------------------------------------------------------------------
TEST ///
kk = ZZ
R = kk[a..h]
I = monomialIdeal(a*b*c*d,e*f*g*h)
D = simplicialComplex I
fVector D
chainComplex D
E = simplicialComplex{a*b*c*d, e*f*g*h}
dual D
dual E
faces(2,D)
faces(3,D)
faces(4,D)
faces(5,D)
faces(6,D)
faces(7,D)
faces(-1,D)
faces(-2,D)
faces(0,D)
assert try (simplicialComplex {};false) else true
///


------------------------------------------------------------------------------
TEST ///
R = ZZ/101[symbol x_0 .. symbol x_3]
D = simplicialComplex {x_0 * x_1 * x_2, x_1 * x_2 * x_3}
facets D
dual D
faces(0,D)
chainComplex D
dual D
///

------------------------------------------------------------------------------
-- link of a face
TEST ///
R = ZZ[a..e]
D = simplicialComplex {b*c,c*a,a*e,a*d,c*d,d*e}
I = ideal D
assert(link(D,a) === simplicialComplex{c,d,e})

D = simplicialComplex {b*c,c*a,a*e,a*d,c*d,d*e,a*c*d,a*d*e}
assert(link(D,a) === simplicialComplex{c*d,d*e})
assert(link(D,a*d) === simplicialComplex{c,e})
assert(link(D,c*d) === simplicialComplex{a})
///


------------------------------------------------------------------------------
-- Buchberger/Lyubeznik/Superficial complexes of a monomial ideal
TEST ///
S=ZZ/32003[x,y,z]
L={x^3,x*y,x*z,y^2,y*z,z^2}
R = ZZ/32003[a..f]
D = buchbergerComplex(L,R)
label(D,L)
-- peek D.cache.labels
boundary(0,D)
boundary(1,D)
C = chainComplex D
assert(C.dd^2 == 0)
prune(HH C)
scan(0..dim D, i -> assert(HH_(i+1)(C) == 0))
assert(HH_0(C) == S^1/(ideal L))
assert isHomogeneous C
C.dd
----
E = lyubeznikComplex(L,R)
label(E,L)
B = chainComplex E
assert(B.dd^2 == 0)
betti B
prune(HH B)
scan(0..dim E, i -> assert(HH_(i+1)(B) == 0))
assert(HH_0(B) == S^1/(ideal L))
assert isHomogeneous B
----
F = superficialComplex(L,R)
label(F,L)
A = chainComplex F
betti A
prune(HH A)
scan(0..dim F, i -> assert(HH_(i+1)(A) == 0))
assert(HH_0(A) == S^1/(ideal L))
assert isHomogeneous A
///


------------------------------------------------------------------------------
-- A generic monomial ideal (Buchberger complex supports the minimal resolution)
TEST ///
S=ZZ/32003[x,y,z]
L={y*z,x^2*z^2,x^2*y^2}
R = ZZ/32003[a..c]
D = buchbergerComplex(L,R)
label(D,L)
C = chainComplex D
assert(C.dd^2 == 0)
betti C
prune(HH C)
E = superficialComplex(L,R)
label(E,L)
betti chainComplex E
///


------------------------------------------------------------------------------
TEST ///
-- This had been a bug around 0.9.95...
x = getSymbol "x"
S = QQ[x_1..x_5];
Delta = simplicialComplex {x_1*x_2*x_3, x_2*x_4, x_3*x_4, x_5};
C = chainComplex Delta
C.dd
assert(C.dd_0 * C.dd_1 == 0)
assert(C.dd_1 * C.dd_2 == 0)
///


------------------------------------------------------------------------------
-- tests added by Janko
TEST ///
R = QQ[x_0..x_4]
D1 = simplicialComplex monomialIdeal(x_0*x_1*x_2*x_3*x_4)
S = QQ[x_0..x_4,T]
D2 = simplicialComplex monomialIdeal(x_0*x_1*x_2*x_3*x_4,T)
assert(substitute(D1,S) === D2)
///


------------------------------------------------------------------------------
TEST ///
R = QQ[x_0..x_4]
D1 = simplicialComplex monomialIdeal(x_0*x_1*x_2*x_3*x_4)
-- F1=(faces(1,D1,useFaceClass=>true))#0
S = QQ[x_0..x_4,T]
D2 = simplicialComplex monomialIdeal(x_0*x_1*x_2*x_3*x_4,T)
-- F2=(faces(1,D2,useFaceClass=>true))#0
-- assert(substitute(F1,S)==F2)
///


------------------------------------------------------------------------------
TEST ///
R = QQ[x_0..x_4]
D = simplicialComplex monomialIdeal(x_0*x_1*x_2*x_3*x_4)
-- F=(faces(1,D,useFaceClass=>true))#0
-- assert(isFaceOf(F,D))
///


------------------------------------------------------------------------------
TEST ///
R = QQ[x_0..x_4]
D = simplicialComplex monomialIdeal(x_0*x_1,x_2*x_3*x_4)
-- fc=faces(D,useFaceClass=>true)
-- assert(apply(-1..2,j->#fc#j)==(1,5,9,6))
///


------------------------------------------------------------------------------
TEST ///
R = QQ[x_0..x_4]
F = face (x_0*x_1)
G = face (x_0*x_1*x_2)
assert(isSubface(F,G))
assert(dim(F)==1);
assert(dim(G)==2);
assert(ring(F)===R)
///


------------------------------------------------------------------------------
TEST ///
R = QQ[x_0..x_4]
F = face (x_0*x_1)
assert(set vertices(F) === set {x_0,x_1})
///


------------------------------------------------------------------------------
TEST ///
R = QQ[x_0..x_4]
F = face (x_0*x_1)
assert(set vertices(F) === set {x_0,x_1})
///


------------------------------------------------------------------------------
TEST ///
R = QQ[a..e]
D = simplicialComplex monomialIdeal(a*b*c*d*e)
-- assert(D==simplicialComplex facets(D,useFaceClass =>true))
///
