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
-- Simplicial Complexes Documentation
------------------------------------------------------------------------------
undocumented {
    (expression, SimplicialComplex),
    Labels,
    AmbientRing
    }

-- Labels is a documented symbol in chainComplex(SimplicialComplex) and
-- boundaryMap.
-- AmbientRing is a documented symbol in wedge

doc ///  
    Key
        SimplicialComplexes
    Headline 
        exploring abstract simplicial complexes within commutative algebra
    Description
        Text
	    An @HREF("https://en.wikipedia.org/wiki/Abstract_simplicial_complex", 
		    "abstract simplicial complex")@  
	    is a family of finite sets closed under the operation of
	    taking subsets.
	Text
	    In this package, the finite set consists of variables in a
	    @TO2(PolynomialRing, "polynomial ring")@ and each subset is
	    represented as a product of the corresponding variables.  In other
	    words, we exploit the natural bijection between abstract
	    simplicial complexes and 
	     @HREF("https://en.wikipedia.org/wiki/Stanley–Reisner_ring",
	    "Stanley-Reisner ideals")@.
     	Text
	    This package is designed to explore applications of abstract
	    simplicial complexes within combinatorial commutative algebra.
     	    Introductions to this theory can be found in the following
     	    textbooks:	    
    	Text
	    @UL {
	    	{"Winfried Bruns and Jürgen Herzog, ",
		HREF("https://www.cambridge.org/core/books/cohenmacaulay-rings/938BC2204D8A7C99E2CEBA1695A692A4",
		    "Cohen-Macaulay rings"), 
		", Cambridge Studies in Advanced Mathematics 39,", 
		"Cambridge University Press, Cambridge, 1993. ",
		"ISBN: 0-521-41068-1" },
	    	{"Ezra Miller and Bernd Sturmfels, ",
		HREF("https://www.springer.com/gp/book/9780387223568",
		    "Combinatorial commutative algebra"),
		", Graduate Texts in Mathematics 227, ",
		"Springer-Verlag, New York, 2005. ",
		"ISBN: 0-387-22356-8" }, 
		{"Richard Stanley, ",
		HREF("https://www.springer.com/gp/book/9780817643690", 
		    "Combinatorics and commutative algebra"),
		", Progress in Mathematics 41, ",
		"Birkhäuser Boston, Inc., Boston, MA, 1983. ",
		"ISBN: 0-8176-3112-7" }
	    }@	
	Text
            @SUBSECTION "Contributors"@
	Text
	    The following people have generously contributed code, improved existing code, or 
	    enhanced the documentation:  
	    @HREF("https://www.mathematik.uni-kl.de/~boehm/", "Janko Böhm")@,
	    @HREF("https://www.math.stonybrook.edu/~sorin/", "Sorin Popescu")@,
	    @HREF("http://www.math.cornell.edu/~mike/","Mike Stillman")@, and
	    @HREF("https://www.mis.mpg.de/nlalg/nlalg-people/lorenzo-venturello.html", "Lorenzo Venturello")@.
    Caveat
    	This package is not intended to handle abstract simplicial complexes
	with a large number of vertices, because computations in a polynomial
	ring with large number of variables are typically prohibitive.
    SeeAlso
        "making an abstract simplicial complex"
	"finding attributes and properties"
	"working with simplicial maps"
///
 
 
------------------------------------------------------------------------------
-- Basic features of the simplicial complex datatype
------------------------------------------------------------------------------
doc ///
    Key 
        "making an abstract simplicial complex"
    Headline
        information about the basic constructors
    Description
        Text
	    An {\em abstract simplicial complex} on a finite set is a family
	    of subsets that is closed under taking subsets.  The elements in
	    the abstract simplicial complex are called its {\em faces}.  The
	    faces having cardinality 1 are its {\em vertices} and the
	    maximal faces (order by inclusion) are its {\em facets}.
	Text 
	    In this package, an abstract simplicial complex is represented by
	    its @HREF("https://en.wikipedia.org/wiki/Stanley–Reisner_ring",
	    "Stanley-Reisner ideal")@ in the polynomial ring.  More precisely,
	    the vertices are identified with a subset of the variables in a
	    fixed polynomial ring and each face is identify with the product
	    of the corresponding variables. A {\em nonface} is any subset of
	    the variables that does not belong to the abstract simplicial
	    complex—we also identify each nonface with a product of variables.
	    The Stanley-Reisner ideal of an abstract simplicial complex is
	    generated by monomials corresponding to its nonfaces.
    	Text
    	    @SUBSECTION "Basic constuctors for abstract simplicial complexes"@
	Text
    	    @UL {
                TO (simplicialComplex, List),		
                TO (simplicialComplex, MonomialIdeal),
        	TO SimplicialComplex,
		TO (isWellDefined, SimplicialComplex)
    	    }@
    	Text
    	    @SUBSECTION "Classic examples of abstract simplicial complexes"@
	Text
    	    @UL {
		TO (simplexComplex, ZZ, PolynomialRing),		
		TO (bartnetteSphereComplex, PolynomialRing),
		TO (bjornerComplex, PolynomialRing),
		TO (dunceHatComplex, PolynomialRing),		
		TO (poincareSphereComplex, PolynomialRing),
		TO (nonPiecewiseLinearSphereComplex, PolynomialRing),
		TO (rudinBallComplex, PolynomialRing),
		TO (grunbaumBallComplex, PolynomialRing),
		TO (zieglerBallComplex, PolynomialRing)				
    	    }@
    	Text
    	    @SUBSECTION "Basic operations producing abstract simplicial complexes"@
	Text
    	    @UL {
		TO (dual, SimplicialComplex),
		TO (boundaryMap,ZZ, SimplicialComplex),
		TO (link, SimplicialComplex, RingElement),
		TO (skeleton, ZZ, SimplicialComplex),
		TO (star, SimplicialComplex, RingElement),
		TO (symbol *, SimplicialComplex, SimplicialComplex)
    	    }@		
    SeeAlso
        "finding attributes and properties"
///

       
doc ///
    Key 
        SimplicialComplex
    Headline 
        the class of all abstract simplicial complexes
    Description
        Text
	    An {\em abstract simplicial complex} on a finite set is a family
	    of subsets that is closed under taking subsets.  The elements in
	    the abstract simplicial complex are called its {\em faces}.  The
	    faces having cardinality 1 are its {\em vertices} and the
	    maximal faces (order by inclusion) are its {\em facets}.
	Text 
	    In this package, an abstract simplicial complex is represented by
	    its @HREF("https://en.wikipedia.org/wiki/Stanley–Reisner_ring",
	    "Stanley-Reisner ideal")@ in a polynomial ring.  More precisely,
	    the vertices are identified with a subset of the variables in a
	    fixed polynomial ring and each face is identify with the product
	    of the corresponding variables. A {\em nonface} is any subset of
	    the variables that does not belong to the abstract simplicial
	    complex—we also identify each nonface with a product of variables.
	    The Stanley-Reisner ideal of an abstract simplicial complex is
	    generated by monomials corresponding to its nonfaces.
    SeeAlso
        "making an abstract simplicial complex"
	"finding attributes and properties"	
///


doc ///
    Key
        (facets, SimplicialComplex)
    Headline
        get the matrix of maximal faces 
    Usage
        facets D
    Inputs
	D : SimplicialComplex
    Outputs
	: Matrix 
	    that has one row whose entries are the squarefree monomials
	    representing the facets in {\tt D}
    Description
        Text
	    In this package, an abstract simplicial complex is constructed as
            squarefree monomial ideal in a 
	    @TO2((ring, SimplicialComplex), "polynomial ring")@.  The vertices
	    in the abstract simplicial complex are identified with a subset of
	    the variables in the polynomial ring and each face is identified
	    with the product of the corresponding variables.  This method
	    returns a matrix whose entries are the squarefree monomials
	    representing the maximal faces in the abstract simplicial complex.
	Text
	    The matrix has one row and the order of the columns is determined
	    by the @TO2(MonomialOrder, "monomial order")@ on the underlying
	    polynomial ring.  The facets of an abstract simplicial complex are
	    used when outputing or printing; see @TO (net, SimplicialComplex)@.
	Text
     	    The @HREF("https://en.wikipedia.org/wiki/5-cell", "4-simplex")@
     	    is a simplicial sphere with 5 vertices, 5 tetrahedral facets, and 
	    a minimal nonface that corresponds to the interior of the sphere.
    	Example
	    S = ZZ[a..e];
	    D = simplicialComplex monomialIdeal (a*b*c*d*e)
	    facets D
	    assert (facets D == matrix{{b*c*d*e, a*c*d*e, a*b*d*e, a*b*c*e, a*b*c*d}}
		and isPure D and dim D === 3)
    	Text
	    The abstract simplicial complex from Example 1.8 of
            Miller-Sturmfels' {\em Combinatorial Commutative Algebra} consists
            of a triangle (on vertices {\tt a, b, c}), two edges (connecting
            {\tt c} to {\tt d} and {\tt b} to {\tt d}), and an isolated
            vertex (namely {\tt e}).  It has six minimal nonfaces.
    	Example
	    D' = simplicialComplex {e, c*d, b*d, a*b*c}
	    facets D'
	    assert (facets D' == matrix {{e, c*d, b*d, a*b*c}} and 
		ideal D' == ideal (a*d, b*c*d, a*e, b*e, c*e, d*e) and 
		not isPure D' and dim D' === 2)
	Text
	    The irrelevant complex has the empty set as a facet whereas the
	    void complex has no facets.
	Example
	    irrelevant = simplicialComplex {1_S}
	    facets irrelevant
	    void = simplicialComplex monomialIdeal 1_S
	    facets void	    
	    assert (facets irrelevant == matrix{{1_S}} and facets void == 0)
    	Text
	    The matrix of facets is part of the defining data of an
	    abstract simplicial complex, so this method does no computation.
    SeeAlso 
        "finding attributes and properties"
	(net, SimplicialComplex)
	(ring, SimplicialComplex)
	(dim, SimplicialComplex)	
	(isPure, SimplicialComplex)	
	(faces, SimplicialComplex)
///


doc ///
    Key
        (net, SimplicialComplex)
    Headline
        make a symbolic representation of an abstract simplicial complex
    Usage
        net D
    Inputs
        D : SimplicialComplex
    Outputs
        : Net
	    a symbolic representation used for printing
    Description
        Text
	    The net of an abstract simplicial complex is a matrix with one row
	    where the entries are the monomials representing the facets (also
	    known as maximal faces).  This function is the primary function
	    called upon by @TO (symbol <<, File, Thing)@ to format for printing.
        Example
            S = ZZ[a..f];
	    Octahedron = simplicialComplex monomialIdeal(a*f, b*d, c*e)
    	    net Octahedron
	Text
	    The void complex has no facets whereas the irrelevant complex has
	    the empty set as a facet.
	Example
	    void = simplicialComplex monomialIdeal 1_S
	    net void
	    irrelevant = simplicialComplex {1_S};
	    net irrelevant
    SeeAlso
        "finding attributes and properties"
        (facets, SimplicialComplex)
///


doc /// 
    Key
        (ideal, SimplicialComplex)
    Headline 
        get the Stanley-Reisner ideal 
    Usage
        ideal D
    Inputs
	D : SimplicialComplex
    Outputs 
        : Ideal 
	    that is generated by the monomials representing the minimal
	    nonfaces in {\tt D}
    Description
        Text
            In this package, an abstract simplicial complex is constructed as
            squarefree monomial ideal in a 
	    @TO2((ring, SimplicialComplex), "polynomial ring")@.  This method
            returns the defining ideal.
	Text
     	    The @HREF("https://en.wikipedia.org/wiki/5-cell", "4-simplex")@ is
     	    a simplicial sphere with 5 vertices, 5 tetrahedral facets, and a
     	    minimal nonface that corresponds to the interior of the sphere.
    	Example
	    S = ZZ[a..e];
	    D = simplicialComplex {b*c*d*e, a*c*d*e, a*b*d*e, a*b*c*e, a*b*c*d}
	    I = ideal D
	    dim D
	    assert (I == ideal a*b*c*d*e and instance(I, Ideal) and 
		numgens I === 1 and dim D === 3)
    	Text
	    The abstract simplicial complex from Example 1.8 of
            Miller-Sturmfels' {\em Combinatorial Commutative Algebra} consists
            of a triangle (on vertices {\tt a, b, c}), two edges (connecting
            {\tt c} to {\tt d} and {\tt b} to {\tt d}), and an isolated
            vertex (namely {\tt e}).  It has six minimal nonfaces.
    	Example
	    D' = simplicialComplex {e, c*d, b*d, a*b*c}
	    I' = ideal D'
	    assert (I' == ideal (a*d, b*c*d, a*e, b*e, c*e, d*e) and
		dim D' === 2 and instance(I', Ideal))	    
	Text
	    The irrelevant complex has the empty set as a facet whereas the
	    void complex has no facets.
	Example
	    irrelevant = simplicialComplex {1_S};
	    M = ideal irrelevant
	    void = simplicialComplex monomialIdeal 1_S
	    M' = ideal void	    
	    assert (M == ideal gens S and instance(M, Ideal) and 
		M' == ideal 1_S and instance (M', Ideal))
    	Text
	    This routine is identical to 
	    @TO (monomialIdeal, SimplicialComplex)@ except for the
	    @TO2(Type,"type")@ of the output.
	Example
	    printWidth = 250;
	    code (ideal, SimplicialComplex)	    	
	    code (monomialIdeal, SimplicialComplex)	    
    	Text
	    As the Stanley-Reisner ideal is part the defining data of an
	    abstract simplicial complex, so this method does no computation.
    SeeAlso 
        "finding attributes and properties"
	(simplicialComplex, MonomialIdeal)
	(monomialIdeal, SimplicialComplex)	
	(facets, SimplicialComplex)
	(ring, SimplicialComplex)
///


doc /// 
    Key
        (monomialIdeal, SimplicialComplex)
	"Stanley-Reisner ideal"	
    Headline 
        get the Stanley-Reisner monomial ideal 
    Usage
        monomialIdeal D
    Inputs
	D : SimplicialComplex
    Outputs 
        : MonomialIdeal 
	    that is generated by the monomials representing the minimal
	    nonfaces in {\tt D}
    Description
        Text
	    In this package, an abstract simplicial complex is constructed as
            squarefree monomial ideal in a @TO2((ring, SimplicialComplex),
            "polynomial ring")@.  This method returns the defining monomial
            ideal.
	Text
     	    The @HREF("https://en.wikipedia.org/wiki/5-cell", "4-simplex")@ is
     	    a simplicial sphere with 5 vertices, 5 tetrahedral facets, and a
     	    minimal nonface that corresponds to the interior of the sphere.
    	Example
	    S = ZZ[a..e];
	    D = simplicialComplex {b*c*d*e, a*c*d*e, a*b*d*e, a*b*c*e, a*b*c*d}
	    I = monomialIdeal D
	    dim D
	    assert (I == monomialIdeal a*b*c*d*e and numgens I === 1 and
		instance(I, MonomialIdeal) and dim D === 3)
    	Text
	    The abstract simplicial complex from Example 1.8 of
            Miller-Sturmfels' {\em Combinatorial Commutative Algebra} consists
            of a triangle (on vertices {\tt a, b, c}), two edges (connecting
            {\tt c} to {\tt d} and {\tt b} to {\tt d}), and an isolated
            vertex (namely {\tt e}).  It has six minimal nonfaces.
    	Example
	    D' = simplicialComplex {e, c*d, b*d, a*b*c}
	    I' = monomialIdeal D'
 	    assert (I' == monomialIdeal (a*d, b*c*d, a*e, b*e, c*e, d*e) and
		dim D' === 2 and instance(I', MonomialIdeal))	    
	Text
	    The irrelevant complex has the empty set as a facet whereas the
	    void complex has no facets.
	Example
	    irrelevant = simplicialComplex {1_S};
	    M = monomialIdeal irrelevant
	    void = simplicialComplex monomialIdeal 1_S
	    M' = monomialIdeal void	    
	    assert (M == monomialIdeal gens S and instance(M, MonomialIdeal) 
		and M' == monomialIdeal 1_S and instance (M', MonomialIdeal))
    	Text
	    This routine is identical to @TO (ideal, SimplicialComplex)@
	    except for the @TO2(Type,"type")@ of the output.
	Example
	    printWidth = 250;
	    code (ideal, SimplicialComplex)	    	
	    code (monomialIdeal, SimplicialComplex)	    
    	Text
	    As the Stanley-Reisner ideal is part the defining data of an
	    abstract simplicial complex, so this method does no computation.
    SeeAlso 
        "finding attributes and properties"    
	(simplicialComplex, MonomialIdeal)
	(ideal, SimplicialComplex)
	(facets, SimplicialComplex)	
	(ring, SimplicialComplex)
///


doc ///
    Key
        (ring, SimplicialComplex)
    Headline
    	get the polynomial ring of its Stanley-Reisner ideal
    Usage
        ring D
    Inputs
        D : SimplicialComplex
    Outputs
        : PolynomialRing 
    Description
        Text
	    In this package, an abstract simplicial complex is constructed as
            squarefree monomial ideal in a @TO2((ring, SimplicialComplex),
            "polynomial ring")@.  In particular, the vertices of an abstract
            simplicial complex are a subset of variables in the polynomial
            ring.  This method returns the defining polynomial ring.
	Text
     	    The @HREF("https://en.wikipedia.org/wiki/5-cell", "4-simplex")@ is
     	    a simplicial sphere with 5 vertices, 5 tetrahedral facets, and a
     	    minimal nonface that corresponds to the interior of the sphere.	    
    	Example
	    S = ZZ[a..e];
	    D = simplicialComplex {b*c*d*e, a*c*d*e, a*b*d*e, a*b*c*e, a*b*c*d}
	    ring D
	    coefficientRing D
	    dim D
	    assert (ring D === S and coefficientRing D === ZZ)
    	Text
	    The abstract simplicial complex from Example 1.8 of
            Miller-Sturmfels' {\em Combinatorial Commutative Algebra} consists
            of a triangle (on vertices {\tt a, b, c}), two edges (connecting
            {\tt c} to {\tt d} and {\tt b} to {\tt d}), and an isolated
            vertex (namely {\tt e}).  It has six minimal nonfaces.
    	Example
	    S' = ZZ/101[a..e];
	    D' = simplicialComplex {e, c*d, b*d, a*b*c}
	    ring D'
	    assert (ring D' === S' and coefficientRing D' === ZZ/101)	    
	Text
	    The irrelevant complex has the empty set as a facet whereas the
	    void complex has no facets.	
	Example
	    irrelevant = simplicialComplex {1_S'};
    	    ring irrelevant
	    void = simplicialComplex monomialIdeal 1_S
    	    ring void	    
	    assert (ring irrelevant === S' and ring void === S)
    	Text
	    As the Stanley-Reisner ideal is part the defining data of an
	    abstract simplicial complex, so this method does no computation.
    Caveat 
	Although an abstract simplicial complex can be represented by a
	Stanley-Reisner ideal in any polynomial ring with a sufficiently large
	number of variables, some operations in this package do depend of the
	choice of the polynomial ring (or its coefficient ring).  For example,
	the @TO2((chainComplex, SimplicialComplex), "chain complex")@ of an
	abstract simplicial complex is typically constructed over the
	coefficient ring of this polynomial ring.
    SeeAlso
        "finding attributes and properties"
	(simplicialComplex, MonomialIdeal)	
	(monomialIdeal, SimplicialComplex)
        (coefficientRing, SimplicialComplex)	
///


doc ///
    Key
        (coefficientRing, SimplicialComplex)
    Headline
        get the coefficient ring of the underlying polynomial ring
    Usage
        coefficientRing D
    Inputs
        D : SimplicialComplex
    Outputs
        : Ring
	    that is the coefficient ring of the polynomial ring that contains
	    the defining Stanley-Reisner ideal	    
    Description
        Text
	    In this package, an abstract simplicial complex is constructed as
            squarefree monomial ideal in a @TO2((ring, SimplicialComplex),
            "polynomial ring")@.  This method returns the
            @TO2(coefficientRing, "coefficient ring")@ of this polynomial
            ring.
	Text
     	    The @HREF("https://en.wikipedia.org/wiki/5-cell", "4-simplex")@ is
     	    a simplicial sphere with 5 vertices, 5 tetrahedral facets, and a
     	    minimal nonface that corresponds to the interior of the sphere.
     	    We construct this abstract simplicial complex using three
     	    different polynomial rings.
    	Example
	    S = ZZ[a..e];
	    D = simplicialComplex {b*c*d*e, a*c*d*e, a*b*d*e, a*b*c*e, a*b*c*d}
	    ring D
	    monomialIdeal D
	    coefficientRing D
	    assert (ring D === S and coefficientRing D === ZZ and 
		numgens ideal D === 1 )	    
    	Example
	    S' = QQ[a..e];
	    D' = simplicialComplex {b*c*d*e, a*c*d*e, a*b*d*e, a*b*c*e, a*b*c*d}
	    ring D'
	    monomialIdeal D'
	    coefficientRing D'
	    assert (ring D' === S' and coefficientRing D' === QQ and
		numgens ideal D' === 1)
    	Example
	    S'' = ZZ/101[a..f];
	    D'' = simplicialComplex {b*c*d*e, a*c*d*e, a*b*d*e, a*b*c*e, a*b*c*d}
	    ring D''
	    monomialIdeal D''
	    coefficientRing D''
	    assert (ring D'' === S'' and coefficientRing D'' === ZZ/101 and
		numgens ideal D'' === 2)
    	Text
	    As the Stanley-Reisner ideal is part the defining data of an
	    abstract simplicial complex, so this method does no computation.	
    	Text
	    Although an abstract simplicial complex can be represented by a
	    Stanley-Reisner ideal in any polynomial ring with a sufficiently
	    large number of variables, some operations in this package do
	    depend of the choice of the polynomial ring (or its coefficient ring).
	    For example, the @TO2((chainComplex, SimplicialComplex), "chain
	    complex")@ of an abstract simplicial complex is typically
	    constructed over the coefficient ring of this polynomial ring.
	Example
    	    C = chainComplex D
	    C' = chainComplex D'
	    C'' = chainComplex D''
	    assert (C' == C ** QQ and C'' == C ** (ZZ/101))
    SeeAlso
        "finding attributes and properties"    
        (ring, SimplicialComplex)
        (chainComplex, SimplicialComplex)
///

 
doc ///
    Key
        (dim, SimplicialComplex)
    Headline
        find the dimension of an abstract simplicial complex
    Usage
        dim D
    Inputs
        D : SimplicialComplex
    Outputs
        : ZZ
	    one less than the maximum number of vertices in a face
    Description
    	Text
	    A face $F$ in an abstract simplicial complex $D$ of cardinality
	    $|F| = i + 1$ has {\em dimension} $i$.  The dimension of $D$ is
	    the maximum of the dimensions of its faces or it is 
	    {\tt - infinity} if $D$ is the void complex which has no faces.
	Text
     	    The @HREF("https://en.wikipedia.org/wiki/5-cell", "4-simplex")@ is
     	    a simplicial sphere with 5 vertices, 5 tetrahedral facets, and a
     	    minimal nonface that corresponds to the interior of the sphere.
    	Example
	    S = ZZ[a..e];
	    D = simplicialComplex {b*c*d*e, a*c*d*e, a*b*d*e, a*b*c*e, a*b*c*d}
	    monomialIdeal D
	    dim D
	    assert (dim D === 3 and numgens ideal D === 1 and isPure D)
    	Example
	    S' = ZZ/101[a..f];
	    D' = simplicialComplex {b*c*d*e, a*c*d*e, a*b*d*e, a*b*c*e, a*b*c*d}
	    monomialIdeal D'
	    dim D'
	    assert (dim D' === 3 and numgens ideal D' === 2 and isPure D)	    
    	Text
	    The abstract simplicial complex from Example 1.8 of
            Miller-Sturmfels' {\em Combinatorial Commutative Algebra} consists
            of a triangle (on vertices {\tt a, b, c}), two edges (connecting
            {\tt c} to {\tt d} and {\tt b} to {\tt d}), and an isolated
            vertex (namely {\tt e}).  It has six minimal nonfaces.
    	Example
	    S'' = QQ[a..e];
	    D'' = simplicialComplex {e, c*d, b*d, a*b*c}
	    monomialIdeal D''
	    dim D''
	    assert (dim D'' === 2 and not isPure D'')	    
	Text
	    The irrelevant complex has the empty set as a facet whereas the
	    void complex has no facets.  The irrelevant complex has dimension
	    -1 while the void complex has dimension {\tt - infinity}.
	Example
	    irrelevant = simplicialComplex {1_S'};
    	    dim irrelevant
	    void = simplicialComplex monomialIdeal 1_S
    	    dim void	    
	    assert (dim irrelevant === -1 and dim void === -infinity)
	Text
	    To avoid repeating a computation, the package caches the result in
	    the @TO CacheTable@ of the abstract simplicial complex.
    SeeAlso
        "finding attributes and properties"    
    	(facets, SimplicialComplex)
	(isPure, SimplicialComplex)
///


doc ///
    Key 
        (simplicialComplex, List) 
	(simplicialComplex, Matrix) 	   
        simplicialComplex
    Headline
        make a simplicial complex from a list of faces 
    Usage
        simplicialComplex L
    Inputs
        L : List
	   whose entries are monomials in a ring corresponding to faces
	   or a @TO Matrix@ with one row and monomial entries
    Outputs
        : SimplicialComplex
	    that is generated by the given faces
    Description
        Text
	    An {\em abstract simplicial complex} on the finite set is a family
	    of subsets that is closed under taking subsets.  The elements in
	    the abstract simplicial complex are called its {\em faces}.  The
	    faces having cardinality 1 are its {\em vertices} and the
	    maximal faces (order by inclusion) are its {\em facets}.
	Text 
	    In this package, an abstract simplicial complex is represented by
	    its @HREF("https://en.wikipedia.org/wiki/Stanley–Reisner_ring",
	    "Stanley-Reisner ideal")@ in a polynomial ring.  More precisely,
	    the vertices are identified with a subset of the variables in a
	    fixed polynomial ring and each face is identify with the product
	    of the corresponding variables.  Given a list of monomials in a
	    polynomial ring, this method returns the smallest abstract
	    simplicial complex containing these faces.  Hence, the list
	    typically contains the monomials corresponding to the facets of
	    the simplicial complex.
	Text
     	    The @HREF("https://en.wikipedia.org/wiki/5-cell", "4-simplex")@ is
     	    a simplicial sphere with 5 vertices, 5 tetrahedral facets, and a
     	    minimal nonface that corresponds to the interior of the sphere.	
    	Example
	    S = ZZ[a..e];
	    D = simplicialComplex {a*b*d*e, b*c*d*e, a*b*c*e, a*b*c*d, a*c*d*e}
	    facets D	    
	    monomialIdeal D
	    dim D	    
	    assert (dim D === 3 and numgens ideal D === 1 and isPure D)
	    assert (D === simplicialComplex facets D)
	Text
	    Although the list of faces may include non-facets, an abstract
	    simplicial complex is displayed by listing its facets.  The order
	    of faces in the list is unimportant.
    	Example
	    D' = simplicialComplex {a*b*d*e, b*c, a*b*c*d,  a*c*d*e, a*c*d,  b*c*d*e, d, a*b*c*e}
	    monomialIdeal D'
	    assert (D' === D)
	    assert (D' === simplicialComplex facets D')
    	Text
	    The abstract simplicial complex from Example 1.8 of
            Miller-Sturmfels' {\em Combinatorial Commutative Algebra} consists
            of a triangle (on vertices {\tt a, b, c}), two edges (connecting
            {\tt c} to {\tt d} and {\tt b} to {\tt d}), and an isolated
            vertex (namely {\tt e}).  It has six minimal nonfaces.
    	Example
	    S'' = ZZ/101[a..e];
	    D'' = simplicialComplex {e, c*d, b*d, a*b*c}
	    monomialIdeal D''
	    facets D''
	    dim D''
	    assert (dim D'' === 2 and not isPure D'')
	    assert (D'' === simplicialComplex facets D'')	    
	Text
	    There are two "trivial" simplicial complexes: The irrelevant
	    complex has the empty set as a facet whereas the void complex has
	    no facets.  Since every abstract simplicial complex in this
	    package is equipped with a chosen polynomial ring, the void
	    complex cannot be constructed by just listing its facets.
	Example
	    irrelevant = simplicialComplex {1_S''};
    	    dim irrelevant
	    void = simplicialComplex monomialIdeal 1_S
    	    dim void	    
	    assert (dim irrelevant === -1 and dim void === -infinity)
	    assert (irrelevant === simplicialComplex facets irrelevant)
    	Text
	    Although an abstract simplicial complex can be represented by a
	    Stanley-Reisner ideal in any polynomial ring with a sufficiently
	    large number of variables, some operations in this package do
	    depend of the choice of the polynomial ring (or its coefficient ring).
	    For example, the @TO2((chainComplex, SimplicialComplex), "chain
	    complex")@ of an abstract simplicial complex is typically
	    constructed over the coefficient ring of this polynomial ring.
	Example
    	    C   = chainComplex D
	    C'  = chainComplex D'
	    C'' = chainComplex D''
    SeeAlso
        "making an abstract simplicial complex"    
        (simplicialComplex, MonomialIdeal)
	(facets, SimplicialComplex)
///


doc ///
    Key 
        (simplicialComplex, MonomialIdeal)   	
    Headline
        make a simplicial complex from its Stanley-Reisner ideal
    Usage
        simplicialComplex I
    Inputs
        I : MonomialIdeal
    Outputs
        : SimplicialComplex
	    whose minimal nonfaces correspond to the generators of {\tt I}
    Description
        Text
	    An {\em abstract simplicial complex} on a finite set is a family
	    of subsets that is closed under taking subsets.  The elements in
	    the abstract simplicial complex are called its {\em faces}.  The
	    faces having cardinality 1 are its {\em vertices} and the
	    maximal faces (order by inclusion) are its {\em facets}.
	Text 
	    In this package, an abstract simplicial complex is represented by
	    its @HREF("https://en.wikipedia.org/wiki/Stanley–Reisner_ring",
	    "Stanley-Reisner ideal")@ in a polynomial ring.  More precisely,
	    the vertices are identified with a subset of the variables in a
	    fixed polynomial ring and each face is identify with the product
	    of the corresponding variables.  A {\em nonface} is any subset of
	    the variables that does not belong to the abstract simplicial
	    complex—we also identify each nonface with a product of variables.
	    The Stanley-Reisner ideal of an abstract simplicial complex is
	    generated by monomials corresponding to its nonfaces.  Given a
	    squarefree monomial ideal, this method constructs the
	    corresponding abstract simplicial complex.
	Text
     	    The @HREF("https://en.wikipedia.org/wiki/5-cell", "4-simplex")@ is
     	    a simplicial sphere with 5 vertices, 5 tetrahedral facets, and a
     	    minimal nonface that corresponds to the interior of the sphere.
    	Example
	    S = ZZ[a..e];
	    D = simplicialComplex monomialIdeal (a*b*c*d*e)
	    monomialIdeal D
	    facets D	    	    
	    dim D	    
	    assert (dim D === 3 and numgens ideal D === 1 and isPure D)
	Text
	    An isomorphic abstract simplicial complex may be constructed in a
	    larger polynomial ring.
    	Example
	    S' = QQ[a..f];
	    D' = simplicialComplex monomialIdeal (a*b*c*d*e, f)
	    monomialIdeal D'
	    facets D'
	    assert (sub(facets D',S) === facets D)
    	Text
	    The abstract simplicial complex from Example 1.8 of
            Miller-Sturmfels' {\em Combinatorial Commutative Algebra} consists
            of a triangle (on vertices {\tt a, b, c}), two edges (connecting
            {\tt c} to {\tt d} and {\tt b} to {\tt d}), and an isolated
            vertex (namely {\tt e}).  It has six minimal nonfaces.
    	Example
	    S'' = ZZ/101[a..e];
	    D'' = simplicialComplex monomialIdeal (a*d, b*c*d, a*e, b*e, c*e, d*e)
	    monomialIdeal D''
	    facets D''
	    dim D''
	    assert (dim D'' === 2 and not isPure D'')	    
	Text
	    There are two "trivial" simplicial complexes: The irrelevant
	    complex has the empty set as a facet whereas the void complex has
	    no facets.  Since every abstract simplicial complex in this
	    package is equipped with a chosen polynomial ring, the void
	    complex cannot be constructed by just listing its facets.
	Example
	    irrelevant = simplicialComplex monomialIdeal gens S
	    monomialIdeal irrelevant
	    facets irrelevant
	    void = simplicialComplex monomialIdeal 1_S'
	    monomialIdeal void
	    facets void
	    assert (facets irrelevant === matrix{{1_S}} and 
		facets void === map(S'^1, S'^0, 0))
    	Text
	    Although an abstract simplicial complex can be represented by a
	    Stanley-Reisner ideal in any polynomial ring with a sufficiently
	    large number of variables, some operations in this package do
	    depend of the choice of the polynomial ring (or its coefficient ring).
	    For example, the @TO2((chainComplex, SimplicialComplex), "chain
	    complex")@ of an abstract simplicial complex is typically
	    constructed over the coefficient ring of this polynomial ring.
	Example
    	    C = chainComplex D
	    C' = chainComplex D'
	    C'' = chainComplex D''
    SeeAlso
        "making an abstract simplicial complex"    
        (simplicialComplex, List)
	(facets, SimplicialComplex)
///

doc ///
    Key
        (chainComplex, SimplicialComplex)
	[(chainComplex, SimplicialComplex), Labels]
    Headline
        create the chain complex associated to a simplicial complex.
    Usage
    	chainComplex D
    Inputs
    	D : SimplicialComplex
	Labels => List	  
	    L of monomials in a polynomial ring, one for each vertex of D.
    Outputs
    	C : ChainComplex	 
    Description
    	Text
	    When no labels are given, this function returns C, the reduced simplicial
	    chain complex associated to D with coefficents in k, where k is the 
	    coefficient ring of D (see @TO(coefficientRing,SimplicialComplex)@). When 
	    labels are given, this function returns the homogenization of C we get by 
	    labelling the i^{th} vertex of D by the i^{th} monomial in L. More 
	    information about homogenization of chain complexes by monomial ideals can be
	    found in Irena Peeva, @HREF("https://www.springer.com/gp/book/9780857291769", 
	    "Graded Syzygies")@, Algebra and Application 14, Springer-Verlag, London, 2011.
	Example
	    A = QQ[x_0..x_3];
	    D = simplicialComplex{A_0*A_1*A_2,A_1*A_3,A_2*A_3}
	    C = chainComplex D
	    prune homology C
	Text
	    We can view the attaching maps for C. Notice that the sign changes when we use 
	    @TO(boundaryMap,ZZ,SimplicialComplex)@ to compute the attaching map. This will 
	    alway be the case for unlabelled simplicial comlexes, while the sign will 
	    agree when we use a labelling.
	Example
	    C.dd
    	    all(0..2,i -> C.dd_i == -boundaryMap(i,D))
        Text
	    Using the Lables option, we can homogenize a simplicial chain complex to 
	    construct a resolutions of the monomial ideal (x_0x_1,x_1x_2,x_0x_2,x_3).
	Example
	    A = QQ[x_0..x_3];
	    D = simplicialComplex{A_0*A_1*A_2,A_1*A_2*A_3};
	    S = QQ[x_0..x_3];
	    F = chainComplex(D,Labels => {S_0*S_1,S_3,S_1*S_2,S_0*S_2})
	    prune homology F
    	Text
	    Observe that C begins in homolgical degree -1, while F Begins in homological degree 0.
	    Similar to the first example, we can also also view the differential for F.
	Example
	   F.dd
	   all(0..2, i -> F.dd_(i+1) == boundaryMap(i,D,Labels => {S_0*S_1,S_3,S_1*S_2,S_0*S_2}))
	Text
    	    The order of the monomial labels will have an effect on what the output is.
	    For example, after swapping the first two labels in the example above, we 
	    will no longer get a resolution.	
	Example
	    G = chainComplex(D,Labels => {S_3,S_0*S_1,S_1*S_2,S_0*S_2})
	    G.dd
    	    prune HH G
    SeeAlso
    	"making an abstract simplicial complex"
	(coefficientRing,SimplicialComplex)
	(ChainComplexMap)
	(boundaryMap,ZZ,SimplicialComplex)
	(resolution, Ideal)
	(homology,ChainComplex)
///

doc ///
    Key 
        (isWellDefined, SimplicialComplex)    
    Headline
        whether underlying data is uncontradictory
    Usage
        isWellDefined D
    Inputs
        D : SimplicialComplex
    Outputs
        : Boolean
	    that is @TO true@ if underlying data unambiguously defines an
	    abstract simplicial complex
    Description
	Text 
	    In this package, an abstract simplicial complex is represented by
	    its @HREF("https://en.wikipedia.org/wiki/Stanley–Reisner_ring",
	    "Stanley-Reisner ideal")@ in a polynomial ring.  More precisely,
	    the vertices are identified with a subset of the variables in a
	    fixed polynomial ring and each face is identify with the product
	    of the corresponding variables.  A {\em nonface} is any subset of
	    the variables that does not belong to the abstract simplicial
	    complex—we also identify each nonface with a product of variables.
	    The Stanley-Reisner ideal of an abstract simplicial complex is
	    generated by monomials corresponding to its nonfaces.  
	Text
	    This method determines whether the underlying data correctly
	    defines an abstract simplicial complex.  In particular, it
	    verifies that the monomial ideal is @TO2(isSquareFree,
	    "squarefee")@ and that the matrix of facets are the maximal faces
	    in the abstract simplicial complex.
	Text
     	    The @HREF("https://en.wikipedia.org/wiki/5-cell", "4-simplex")@ is
     	    a simplicial 3-sphere with 5 vertices, 5 facets, and a
     	    minimal nonface that corresponds to the interior of the sphere.
    	Example
	    S = ZZ[a..e];
	    D = simplicialComplex monomialIdeal (a*b*c*d*e)
    	    isWellDefined D
    	Text
            This method also checks the following aspects of the data structure:
	Text
    	    @UL {
		{"the underlying ", TO HashTable, " has the expected keys,
	    	    namely ", TT "ring", ", ", TT "monomialIdeal", ", ", 
		    TT "facets", ", and ", TT "cache", ","},
       	        {"the value of the ", TT "ring", " key is a ", 
		    TO PolynomialRing, ","},
       	        {"the value of the ", TT "monomialIdeal", " key is a ", 
		    TO MonomialIdeal, ","},
      	        {"the ring of the ", TT "monomialIdeal", " value equals the
		    value of the ", TT "ring", " key,"},
       	        {"the value of the ", TT "facets", " key is a ", 
		    TO Matrix, ","},				
     	        {"the ring of the ", TT "facets", " value equals the
		    value of the ", TT "ring", " key,"},		
                {"the value of the ", TT "cache", " key is a ", TO CacheTable,
                    "."}
	    }@	 
	Text
	    Abstract simplicial complexes created using the constructors in
	    this package will automatically be well-defined.  The primary
	    purpose of this method is to document the underlying data
	    structure for developers.
    SeeAlso
        "making an abstract simplicial complex"    
        (simplicialComplex, List)
        (simplicialComplex, MonomialIdeal)	
///

------------------------------------------------------------------------------
-- more advanced constructors
------------------------------------------------------------------------------
doc ///
    Key
        (dual, SimplicialComplex)
    Headline
        make the Alexander dual of an abstract simplicial complex
    Usage
        dual D
    Inputs
	D : SimplicialComplex
    Outputs
        : SimplicialComplex
	    that is the Alexander dual of {\tt D}
    Description
        Text
            The Alexander dual of an abstract simplicial complex $D$ is the
            abstract simplicial complex whose faces are the complements of the
            nonfaces in $D$.  
	Text
	    The Alexander dual of a square is the disjoint union of two edges.
    	Example
	    S = ZZ[a..d];
	    D = simplicialComplex {a*b, b*c, c*d, a*d}
	    dual D  
	    assert (dual D === simplicialComplex {a*c, b*d} and dual dual D === D)
    	Text
            The Alexander dual is homotopy equivalent to the complement of $D$
     	    in the sphere generated by all of the variables in the 
	    @TO2((ring, SimplicialComplex), "polynomial ring")@ of $D$.  In
     	    particular, it depends on the number of variables.
     	Example
	    S' = ZZ[a..e];
	    D' = simplicialComplex {a*b, b*c, c*d, a*d}
	    dual D'
     	    assert (dual D' === simplicialComplex {b*d*e, a*c*e, a*b*c*d} and 
		dual dual D' === D')
	Text
	    The projective dimension of the Stanley-Reisner ring of $D$ equals
     	    the regularity of the Stanley-Reisner ideal of the Alexander dual
     	    of $D$; see Theorem 5.59 in Miller-Sturmfels' 
	    {\em Combinatorial Commutative Algebra}.
    	Example     
     	    S'' = QQ[a..h];
	    D'' =  bartnetteSphereComplex S'' 
	    dual D''
	    pdim comodule ideal D''
	    regularity ideal dual D''
	    assert (pdim comodule ideal D'' === regularity ideal dual D'')
	Text
            Alexander duality interchanges extremal Betti numbers of the
     	    Stanley-Reisner ideals.  Following Example 3.2 in
     	    Bayer-Charalambous-Popescu's
     	    @HREF("https://arxiv.org/abs/math/9804052", "Extremal betti
     	    numbers and applications to monomial ideals")@ we have the
     	    following.
    	Example
	    S = QQ[x_0 .. x_6];
	    D = simplicialComplex {x_0*x_1*x_3, x_1*x_3*x_4, x_1*x_2*x_4,
	        x_2*x_4*x_5, x_2*x_3*x_5, x_3*x_5*x_6, x_3*x_4*x_6,
	        x_0*x_4*x_6, x_0*x_4*x_5, x_0*x_1*x_5, x_1*x_5*x_6,
	        x_1*x_2*x_6, x_0*x_2*x_6, x_0*x_2*x_3}
	    I = ideal D
	    J = ideal dual D
	    betti res I
	    betti res J
    SeeAlso 
        "making an abstract simplicial complex"        
        (dual, MonomialIdeal)
	(pdim, Module)
	(regularity, Module)
	(betti, GradedModule)
///


doc ///
    Key
        (simplexComplex, ZZ, PolynomialRing)
	simplexComplex
    Headline
        make the simplex as an abstract simplicial complex
    Usage
        simplexComplex (d, S)
    Inputs
    	d : ZZ
	    that is the dimension of the simplex
        S : PolynomialRing
	    that has at least $d+1$ generators
    Outputs
        : SimplicialComplex
	    that has a unique facet of dimension $d$
    Description
    	Text
	    A simplex is a generalization of the notion of a triangle or
	    tetrahedron to arbitrary dimensions.  For example, a 0-simplex is
	    a point, a 1-simplex is a line segment, a 2-simplex is a triangle,
	    and a 3-simplex is a tetrahedron.  The {\em $d$-simplex} is the
	    unique $d$-dimensional abstract simplicial complex having one
	    facet.
    	Example
	    S = ZZ[a..e];
	    irrelevant = simplexComplex (-1, S)
	    monomialIdeal irrelevant
	    dim irrelevant
	    F = fVector irrelevant
	    assert (facets irrelevant === matrix {{1_S}} and dim irrelevant === -1 and F#-1 === 1)
    	Example
	    D0 = simplexComplex (0, S)
	    monomialIdeal D0
	    dim D0
	    F0 = fVector D0
	    assert (facets D0 === matrix {{a}} and dim D0 === 0 and 
		all(-1..0, i -> F0#i === binomial(0+1,i+1)))
    	Example
	    D1 = simplexComplex (1, S)
	    monomialIdeal D1
	    dim D1
	    F1 = fVector D1
	    assert (facets D1 === matrix {{a*b}} and dim D1 === 1 and
		all(-1..1, i -> F1#i === binomial(1+1,i+1)))	    	    
    	Example
	    D2 = simplexComplex (2, S)
	    monomialIdeal D2
	    dim D2
	    F2 = fVector D2	    
	    assert (facets D2 === matrix {{a*b*c}} and dim D2 === 2 and
		all(-1..2, i -> F2#i === binomial(2+1,i+1)))	 
    	Example
	    D3 = simplexComplex (3, S)
	    monomialIdeal D3
	    dim D3
	    F3 = fVector D3
	    assert (facets D3 === matrix {{a*b*c*d}} and dim D3 === 3 and
		all(-1..3, i -> F3#i === binomial(3+1,i+1)))	 
    	Example
	    D4 = simplexComplex (4, S)
	    monomialIdeal D4
	    dim D4
	    F4 = fVector D4
	    assert (facets D4 === matrix {{a*b*c*d*e}} and dim D4 === 4 and
		all(-1..4, i -> F4#i === binomial(4+1,i+1)))
	Text
	    The vertices in the $d$-simplex are the first $d+1$ variables in
	    the given polynomial ring.	    
    SeeAlso
        "making an abstract simplicial complex"            
    	(fVector, SimplicialComplex)
///


doc ///
    Key
        (bartnetteSphereComplex, PolynomialRing)
	bartnetteSphereComplex
    Headline
        make a non-polytopal 3-sphere with 8 vertices
    Usage
        bartnetteSphereComplex S
    Inputs
        S : PolynomialRing
	    that has at least 8 generators
    Outputs
        : SimplicialComplex
    Description
    	Text
	    First described by David Barnette's "Diagrams and Schlegel
    	    diagrams" appearing in Combinatorial Structures and their
    	    Applications, (Proc. Calgary Internat. Conf. 1969, pp 1-4), Gordon
    	    and Breach, New York, 1970, this method returns a pure abstract
    	    simplicial complex of dimension 3 with 8 vertices and 19
    	    facets.  It is smallest possible non-polytopal simplicial 3-sphere.
    	Example
	    S = ZZ[a..h];
	    D = bartnetteSphereComplex S
	    dim D 
	    fVector D
	    assert (dim D === 3 and isPure D and 
		ideal D === ideal(b*c*d, a*c*e, c*d*e, a*b*f, b*d*f, a*e*f,
		    c*d*g, a*e*g, b*f*g, b*d*h, c*e*h, a*f*h, g*h) and
		apply(-1..3, i -> (fVector D)#i) === (1,8,27,38,19))
	Text
	    The vertices in the Bartnette sphere are the first 8 variables in
	    the given polynomial ring.
	Example
	    S' = QQ[x_0..x_10];
	    D' = bartnetteSphereComplex S'
	    monomialIdeal D'
    	    assert (dim D' === 3 and isPure D')	    
    	Text
	    Our enumeration of the vertices follows Example 9.5.23 in Jesús A
            De Loera, Jörg Rambau, and Francisco Santos, 
	    @HREF("https://www.springer.com/gp/book/9783642129704", 
	    "Triangulations, structures for algorithms and applications")@,
	    Algorithms and Computation in Mathematics 25, Springer-Verlag,
	    Berlin, 2010.	    
    SeeAlso
        "making an abstract simplicial complex"            
    	(isPure, SimplicialComplex)
	(poincareSphereComplex, PolynomialRing)	
///


doc ///
    Key
        (poincareSphereComplex, PolynomialRing)
	poincareSphereComplex
    Headline
        make a homology 3-sphere with 16 vertices
    Usage
        poincareSphereComplex S
    Inputs
        S : PolynomialRing
	    that has at least 16 generators
    Outputs
        : SimplicialComplex
    Description
    	Text
	    The Poincaré
	    @HREF("https://en.wikipedia.org/wiki/Homology_sphere", "homology
	    sphere")@ is a homology 3-sphere; it has the same homology groups
	    as a 3-sphere.  Following Theorem 5 in Anders Björner and Frank
	    H. Lutz's "Simplicial manifolds, bistellar flips and a 16-vertex
	    triangulation of the Poincaré homology 3-sphere", Experimental
	    Mathematics {\bf 9} (2000) 275–289, this method returns a Poincaré
	    homology sphere with 16 vertices.
    	Example
	    S = ZZ/101[a..q];
	    D = poincareSphereComplex S
	    dim D 
	    fVector D
	    assert (dim D === 3 and isPure D and 
		apply(-1..3, i -> (fVector D)#i) === (1,16,106,180,90))
	    prune HH chainComplex D
	Text
	    This abstract simplicial complex is Cohen-Macaulay.
	Text
	    Our enumeration of the vertices also follows the {\tt poincare}
	    example in Masahiro Hachimori's
	    @HREF("http://infoshako.sk.tsukuba.ac.jp/~hachi/math/library/index_eng.html",
	    "simplicial complex libary")@.	
    SeeAlso
        "making an abstract simplicial complex"  
    	(isPure, SimplicialComplex)
	nonPiecewiseLinearSphereComplex
///


doc ///
    Key
        (nonPiecewiseLinearSphereComplex, PolynomialRing)
	nonPiecewiseLinearSphereComplex
    Headline
        make a non-piecewise-linear 5-sphere with 18 vertices
    Usage
        nonPiecewiseLinearSphereComplex S
    Inputs
        S : PolynomialRing
	    that has at least 18 generators
    Outputs
        : SimplicialComplex
    Description
    	Text
	    A @HREF("https://en.wikipedia.org/wiki/Piecewise_linear_manifold",
	    "piecewise linear (PL)")@ sphere is a manifold which is PL
	    homeomorphic to the boundary of a simplex. All the spheres in
	    dimensions less than or equal to 3 are PL, but there are non-PL
	    spheres in dimensions larger than or equal to 5.
	Text
	    As described in Theorem 7 in Anders Björner and Frank H. Lutz's
	    "Simplicial manifolds, bistellar flips and a 16-vertex
	    triangulation of the Poincaré homology 3-sphere", Experimental
	    Mathematics {\bf 9} (2000) 275–289, this method returns a non-PL
	    5-sphere constructed from the @TO2(poincareSphereComplex,
	    "Björner–Lutz homology sphere")@ by taking a double suspension.
    	Example
	    S = ZZ/101[a..s];
	    D = nonPiecewiseLinearSphereComplex S
	    dim D 
	    fVector D
	    assert (dim D === 5 and isPure D and 
		apply(-1..5, i -> (fVector D)#i) === (1,18,141,515,930,807,269))
	Text
	    This abstract simplicial complex is Cohen-Macaulay.
	Text
	    Our enumeration of the vertices follows the {\tt nonplsphere}
	    example in Masahiro Hachimori's
	    @HREF("http://infoshako.sk.tsukuba.ac.jp/~hachi/math/library/index_eng.html",
	    "simplicial complex libary")@.
    SeeAlso
        "making an abstract simplicial complex"  
	poincareSphereComplex
    	(isPure, SimplicialComplex)	         	
///


doc ///
    Key
        (rudinBallComplex, PolynomialRing)
	rudinBallComplex
    Headline
        make a nonshellable 3-ball with 14 vertices and 41 facets
    Usage
        rudinBallComplex S
    Inputs
        S : PolynomialRing
	    that has at least 14 generators
    Outputs
        : SimplicialComplex
    Description
    	Text
    	    As described in Mary Ellen Rudin's
    	    @HREF("https://www.ams.org/journals/bull/1958-64-03/S0002-9904-1958-10168-8/S0002-9904-1958-10168-8.pdf",
    	    "\"An unshellable triangulation of a tetrahedron\"")@, Bulletin of
    	    the American Mathematical Society {\bf 64} (1958) 90–91, this
    	    method returns triangulation of a 3-ball with 14 vertices and 41
    	    facets that is not
    	    @HREF("https://en.wikipedia.org/wiki/Shelling_(topology)",
    	    "shellable")@.  This abstract simplicial complex has a convex realization.
    	Example
	    S = ZZ/101[a..s];
	    D = rudinBallComplex S
	    dim D 
	    fVector D
	    assert (dim D === 3 and isPure D and 
		apply(-1..3, i -> (fVector D)#i) === (1,14,66,94,41))
	Text
	    Our enumeration of the vertices follows the {\tt rudin}
	    example in Masahiro Hachimori's
	    @HREF("http://infoshako.sk.tsukuba.ac.jp/~hachi/math/library/index_eng.html",
	    "simplicial complex libary")@.
    SeeAlso
        "making an abstract simplicial complex"  
	grunbaumBallComplex
	zieglerBallComplex	
    	(isPure, SimplicialComplex)	         	
///


doc ///
    Key
        (grunbaumBallComplex, PolynomialRing)
	grunbaumBallComplex
    Headline
        make a nonshellable 3-ball with 14 vertices and 29 facets
    Usage
        grunbaumBallComplex S
    Inputs
        S : PolynomialRing
	    that has at least 14 generators
    Outputs
        : SimplicialComplex
    Description
    	Text
	    Attributed to F. Alberto Grünbaum, this method returns a
    	    triangulation of a 3-ball with 14 vertices and 29 facets that is
    	    not @HREF("https://en.wikipedia.org/wiki/Shelling_(topology)",
    	    "shellable")@.
    	Example
	    S = ZZ/101[a..s];
	    D = grunbaumBallComplex S
	    dim D 
	    fVector D
	    assert (dim D === 3 and isPure D and 
		apply(-1..3, i -> (fVector D)#i) === (1,14,54,70,29))
	Text
	    Our enumeration of the vertices follows the {\tt gruenbaum}
	    example in Masahiro Hachimori's
	    @HREF("http://infoshako.sk.tsukuba.ac.jp/~hachi/math/library/index_eng.html",
	    "simplicial complex libary")@.
    SeeAlso
        "making an abstract simplicial complex"  
	rudinBallComplex
	zieglerBallComplex
    	(isPure, SimplicialComplex)	         	
///


doc ///
    Key
        (zieglerBallComplex, PolynomialRing)
	zieglerBallComplex
    Headline
        make a nonshellable 3-ball with 10 vertices and 21 facets
    Usage
        zieglerBallComplex S
    Inputs
        S : PolynomialRing
	    that has at least 10 generators
    Outputs
        : SimplicialComplex
    Description
    	Text
	    As appears on page 167 of Günter M. Ziegler's "Shelling polyhedral
	    3-balls and 4-polytopes", Discrete & Computational Geometry {\bf
	    19} (1998) 159–174, this method returns a
	    @HREF("https://en.wikipedia.org/wiki/Shelling_(topology)",
	    "non-shellable ")@ 3-ball with 10 vertices and 21 facets.
    	Example
	    S = ZZ/101[a..n];
	    D = zieglerBallComplex S
	    dim D 
	    fVector D
	    assert (dim D === 3 and isPure D and 
		apply(-1..3, i -> (fVector D)#i) === (1,10,38,50,21))
	Text
	    Our enumeration of the vertices follows the {\tt ziegler}
	    example in Masahiro Hachimori's
	    @HREF("http://infoshako.sk.tsukuba.ac.jp/~hachi/math/library/index_eng.html",
	    "simplicial complex libary")@.
    SeeAlso
        "making an abstract simplicial complex"  
	rudinBallComplex
	grunbaumBallComplex
    	(isPure, SimplicialComplex)	         	
///


doc ///
    Key
        (dunceHatComplex, PolynomialRing)
	dunceHatComplex
    Headline
        make a realization of the dunce hat with 8 vertices
    Usage
        dunceHatComplex S
    Inputs
        S : PolynomialRing
	    that has at least 8 generators
    Outputs
        : SimplicialComplex
    Description
    	Text
	    The @HREF("https://en.wikipedia.org/wiki/Dunce_hat_(topology)",
	    "dunce hat")@ is a compact topological space formed by taking a
	    solid triangle and gluing all three sides together, with the
	    orientation of one side reversed. Simply gluing two sides oriented
	    in the same direction would yield a cone much like the dunce cap,
	    but the gluing of the third side results in identifying the base
	    of the cap with a line joining the base to the point.
    	Text	
	    Following Erik Christopher Zeeman's "On the dunce hat", Topology
	    {\bf 2} (1964) 341–358, this method returns
	    @HREF("https://en.wikipedia.org/wiki/Collapse_(topology)",
	    "non-collapsible")@ but
	    @HREF("https://en.wikipedia.org/wiki/Contractible_space",
	    "contractible")@ example of an abstract simplicial complex.
    	Example
	    S = ZZ/101[a..h];
	    D = dunceHatComplex S
	    dim D 
	    fVector D
	    assert (dim D === 2 and isPure D and 
		apply(-1..2, i -> (fVector D)#i) === (1,8,24,17))
	Text
	    Our enumeration of the vertices follows the {\tt dunce hat}
	    example in Masahiro Hachimori's
	    @HREF("http://infoshako.sk.tsukuba.ac.jp/~hachi/math/library/index_eng.html",
	    "simplicial complex libary")@.
    SeeAlso
        "making an abstract simplicial complex"  
	rudinBallComplex
	grunbaumBallComplex
    	(isPure, SimplicialComplex)	         	
///


doc ///
    Key
        (bjornerComplex, PolynomialRing)
	bjornerComplex
    Headline
        make a shellable 2-polyhedron with 6 vertices 
    Usage
        bjornerComplex S
    Inputs
        S : PolynomialRing
	    that has at least 6 generators
    Outputs
        : SimplicialComplex
    Description
    	Text
	    Attributed to
	    @HREF("https://en.wikipedia.org/wiki/Anders_Björner", "Anders
	    Björner")@, this method return a
	    @HREF("https://en.wikipedia.org/wiki/Shelling_(topology)",
	    "shellable")@ abstract simplicial complex which has non-zero
	    homology.
    	Example
	    S = ZZ/101[a..f];
	    D = bjornerComplex S
	    dim D 
	    fVector D
	    assert (dim D === 2 and isPure D and 
		apply(-1..2, i -> (fVector D)#i) === (1,6,15,11))
	    prune HH chainComplex D
	Text
	    A shellable abstract simplicial complex $D$ is {\em extendably
	    shellable} if any shelling of a subcomplex can be extended to a
	    shelling of $D$.  The bjorner complex is not extendably shellable.
	Text
	    Our enumeration of the vertices follows the {\tt bjorner}
	    example in Masahiro Hachimori's
	    @HREF("http://infoshako.sk.tsukuba.ac.jp/~hachi/math/library/index_eng.html",
	    "simplicial complex libary")@.
    SeeAlso
        "making an abstract simplicial complex"  
	rudinBallComplex
	grunbaumBallComplex
    	(isPure, SimplicialComplex)	         	
///

doc /// 
    Key 
        (smallManifold, ZZ, ZZ, ZZ, PolynomialRing)
    	smallManifold
    Headline 
        get a small manifold from Frank Lutz' database
    Usage 
        smoothFanoToricVariety (d,v,i,R)
    Inputs
        d : ZZ 
	    equal to dimension of the manifold
	v : ZZ
	    equal to the number of vertices
        i : ZZ 
	    indexing a small d-manifold in the database
        R : PolynomialRing 
	    that specifies the base ring of the complex	    
    Outputs 
        : SimplicialComplex
	    a complex corresponding to a triangulation of a d-manifold
    Description
        Text
            This function accesses a database of all small triangulated 
	    2 or 3-manifolds with at most ten vertices. The classifications
	    of these triangulations are due to many authors; a survey of these
	    results was written by Frank Lutz ( "Triangulated Manifolds with 
	    Few Vertices: Combinatorial Manifolds", @HREF("https://arxiv.org/abs/math/0506372", 
	    "arXiv:math/0506372v1")@. 
	Text
	    Up to isomorphism, there is one 2-manifold with four vertices, 
	    one with five vertices, three with six, nine with seven, 43 with eight,
	    655 with nine, and 42426 with ten. For 3-manifolds, there is one with 
	    five vertices, two with six, five with seven, 39 with eight, and 1297 
	    with nine.
        Example
            R = ZZ[a..j];
	    M = smallManifold(2,9,100,R)
	Text
	    @SUBSECTION "Acknowledgements"@
    	Text
            Thanks to @HREF("http://page.math.tu-berlin.de/~lutz/",
            "Frank Lutz")@ for his database found at @HREF("http://www.grdb.co.uk",
            "Small Manifolds Databases")@.
    Caveat
    	The database for 2-manifolds with ten vertices is rather large, and so loading
	the file takes several seconds.
    SeeAlso
        "making an abstract simplicial complex"
        SimplicialComplex
///

doc /// 
    Key 
        (wedge,SimplicialComplex,SimplicialComplex,RingElement,RingElement)
	[wedge, AmbientRing]
	wedge
    Headline 
        create the wedge product of two simplicial complexes
    Usage 
        wedge (D,E,u,v)
    Inputs
        D : SimplicialComplex  
	E : SimplicialComplex
        u : RingElement 
	    a vertex of {\tt D}
        v : RingElement
	    a vertex of {\tt E}
	AmbientRing => PolynomialRing
    Outputs 
        : SimplicialComplex
	    The wedge product of {\tt D} and {\tt E} obtained by identifying {\tt u}
	    and {\tt v}
    Description
        Text
	    If {\tt D} and {\tt E} are abstract simplicial complexes with distinguished
       	    vertices {\tt u} and {\tt v} respectively, the wedge product of {\tt D}
	    and {\tt E} is the simplicial complex obtained by takingthe disjoint union
	    of {\tt D} and {\tt E} and identifying {\tt u} with {\tt v}.
	Text
	    We construct the bowtie complex by taking the wedge of two 2-simplicies
    	Example
            R = QQ[x_0,x_1,x_2];
	    S = QQ[y_0,y_1,y_2];
	    D = simplicialComplex{R_0*R_1*R_2}
	    E = simplicialComplex{S_0*S_1*S_2}
	    W = wedge(D,E,R_0,S_0)
	    ring W
	Text
	    If the optional argument AmbientRing is used, and given a polynomial ring
	    {\tt R} as its value, then the wedge is constructed as a simplcial complex
	    over the ring {\tt R}. The variables of {\tt ring D} are sent to the first
	    {\tt numgens ring D} elements of {\tt R} and the variables of {\tt ring E}
	    are sent to the next {\tt numgens ring E - 1} variables of {\tt R}, with 
	    {\tt v} being send to the same variable as {\tt u}. This is useful if the
	    complexes you are using are defined over the same ring, or on different
	    rings whose variable names clash with one another.
	Example
	    W = wedge(D,D,R_0,R_2)
	    ring W
	    W = wedge(D,D,R_0,R_2, AmbientRing => QQ[x_0..x_4])
	    ring W
    SeeAlso
        "making an abstract simplicial complex"
        SimplicialComplex
	elementaryCollapse
///

doc ///
    Key 
        (elementaryCollapse, SimplicialComplex, RingElement)
	elementaryCollapse
    Headline 
        construct the elementary collapse of a free frace in a simplicial complex
    Usage 
        elementaryCollapse(D,F)
    Inputs
        D : SimplicialComplex  
	F : RingElement
	    Corresponding to a free face of {\tt D}
    Outputs 
        : SimplicialComplex
	    the simplicial complex where the face {\tt F} and the unique facet
	    containing F are removed
    Description
        Text
	    A free face of a simplicial complex is a face that is a proper maximal
	    subface of exactly one facet. The elementary collapse is the simplicial
	    collapse obtained by removing the free face, and the facet containing it,
	    from the simplicial complex. A simplicial Complex that and be collapsed
	    to a single vertex is called collapsible. Every collapsible simplicial
	    complex is contractible, but the converse is not true.
        Example
       	    R = ZZ/103[x_0..x_3];
       	    D = simplicialComplex{R_0*R_1*R_2,R_0*R_2*R_3,R_0*R_1*R_3}
       	    C1 = elementaryCollapse(D,R_1*R_2)
	    C2 = elementaryCollapse(C1,R_2*R_3)
	    C3 = elementaryCollapse(C2,R_1*R_3)
	    C4 = elementaryCollapse(C3,R_1)	   
	    C5 = elementaryCollapse(C4,R_2)
	    C6 = elementaryCollapse(C5,R_3)   
    SeeAlso
        "making an abstract simplicial complex"
        SimplicialComplex
///
 
------------------------------------------------------------------------------
-- basic properties and invariants
------------------------------------------------------------------------------
doc ///
    Key 
        "finding attributes and properties"
    Headline
        information about accessing features of an abstract simplicial complex
    Description
        Text
            Having made a @TO SimplicialComplex@, one can access its basic
            invariants or test for some elementary properties by using the
            following methods:
    	Text
	    @SUBSECTION "Determining attributes and properties of simplicial complexes"@
	Text
            @UL {
        	TO (facets, SimplicialComplex),
        	TO (ideal, SimplicialComplex),		
        	TO (monomialIdeal, SimplicialComplex),
        	TO (ring, SimplicialComplex),		
        	TO (coefficientRing, SimplicialComplex),		
        	TO (dim, SimplicialComplex)
	    }@
    SeeAlso
        "making an abstract simplicial complex"
///
 
 
doc /// 
    Key 
        (link, SimplicialComplex, RingElement)
	link
    Headline
        make the link of a face in an abstract simplicial complex
    Usage
        link(D, f)
    Inputs
        D : SimplicialComplex
	f : RingElement
	    that is a monomial representing a face of {\tt D}
    Outputs
        : SimplicialComplex
	   the link of {\tt f} in {\tt D}
    Description
        Text
    	    The link of a face $F$ inside the abstract simplicial complex $D$
    	    is the set of faces that are disjoint from $F$ but whose unions
    	    with $F$ lie in $D$.
	Text
	    Following Example 1.39 in Miller-Sturmfels' {\em Combinatorial
	    Commutative Algebra}, we consider a simplicial complex with 6
	    facet.  The link of the vertex $a$ consists of the vertex $e$
	    along with the proper faces of the triangle $b*c*d$.  The link of
	    the vertex $c$ is pure of dimension $1$; its four facets being the
	    three edges of the triangle $a*b*d$ plus the extra edge $b*e$.
	    The link of $e$ consists of the vertex $a$ along with the edge
	    $b*c$.  The link of the edge $b*c$ consists of the three remaining
	    vertices.  Finally, the link of the edge $a*e$ is the irrelevant
	    complex.	    
	Example
	    S = QQ[a..e];
	    D = simplicialComplex monomialIdeal (d*e, a*b*e, a*c*e, a*b*c*d)
	    link (D, a)
	    link (D, c)
	    link (D, e)
	    link (D, b*c)
	    link (D, a*e)
	    assert (facets link (D, a) === matrix {{e, c*d, b*d, b*c}} and 
		facets link (D, c) === matrix {{b*e, b*d, a*d, a*b}} and 
		facets link (D, e) === matrix {{a, b*c}} and
		facets link (D, b*c) === matrix {{e,d,a}} and 
		facets link (D, a*e) === matrix {{1_S}} and 
		isPure link (D, c) and dim link (D, a*e) === -1)
	Text
	    The link of the empty face equals the original simplicial complex.
	Example
	    link(D, 1_S)
	    void = simplicialComplex monomialIdeal 1_S
	    link (void, 1_S)
	    assert (link (D, 1_S) === D and link(void, 1_S) === void)
	Text
	    If $G$ is a face in the link of some face $F$, then $F$ is a face
	    in the link of $G$.
	Example
	    S' = ZZ/101[a..g];
	    hexagon = simplicialComplex {a*b*c, a*c*d, a*d*e, a*e*f, a*f*g, a*b*g}  
	    link (hexagon, a*b)  
	    link (hexagon, g)
	    link (hexagon, c)	
	Text
	    The dual version of Hochster's formula (see Corollary 1.40 in
	    Miller-Sturmfels) relates the Betti numbers of a Stanley-Reisner
	    ideal with the reduced homology of a link in the Alexander dual
	    simplicial complex.
	Example
	    betti res ideal D
	    R = QQ[a..e, DegreeRank => 5];
	    C = simplicialComplex monomialIdeal (d*e, a*b*e, a*c*e, a*b*c*d)  
	    prune Tor_0(R^1/gens R,ideal C)  	    
	    hilbertFunction({1,1,1,1,0}, Tor_0(R^1/gens R, ideal C)) === rank HH_(-1) (link (dual C, e))
	    hilbertFunction({1,1,0,0,1}, Tor_0(R^1/gens R, ideal C)) === rank HH_(-1) (link (dual C, c*d))
	    hilbertFunction({1,0,1,0,1}, Tor_0(R^1/gens R, ideal C)) === rank HH_(-1) (link (dual C, b*d))
	    hilbertFunction({0,0,0,1,1}, Tor_0(R^1/gens R, ideal C)) === rank HH_(-1) (link (dual C, a*b*c))
	    prune Tor_1(R^1/gens R, ideal C)
	    hilbertFunction({1,1,1,0,1}, Tor_1(R^1/gens R, ideal C)) === rank HH_0 (link (dual C, d))	    	    	    
	    hilbertFunction({1,1,0,1,1}, Tor_1(R^1/gens R, ideal C)) === rank HH_0 (link (dual C, c)) 		    
	    hilbertFunction({1,0,1,1,1}, Tor_1(R^1/gens R, ideal C)) === rank HH_0 (link (dual C, b))	    	    	    
	    hilbertFunction({1,1,1,1,1}, Tor_1(R^1/gens R, ideal C)) === rank HH_0 (link (dual C, 1_R)) 		    
	    prune Tor_2(R^1/gens R, ideal C)
	    hilbertFunction({1,1,1,1,1}, Tor_2(R^1/gens R, ideal C)) === rank HH_1 (link (dual C, 1_R))	    	    	    
	Text
    	    The Reisner criterion for the Cohen-Macaulay property of the
    	    Stanley-Reisner ring involves links, see Theorem 5.53 in
    	    Miller-Sturmfels.  Specifically, an abstract simplicial complex
    	    {\tt D} is Cohen-Macaulay if and only if, for all faces {\tt F} in
    	    {\tt D} and all {\tt i} such that {\tt i < dim link(D, F)}, the
    	    {\tt i}-th reduced homology of {\tt link(D, F)} vanishes.
	Example 
	    S'' = QQ[a..h];
	    B = bartnetteSphereComplex S''
	    pdim comodule ideal B === codim ideal B  -- B is Cohen-Macaulay
    	    -- directly verify the Reisner criterion
	    all (flatten apply(-1..2, i -> first entries (faces B)#i), f -> (
		     L := link (B, f);
		     all (-1..dim L - 1, j -> HH_j(L) == 0)))
    SeeAlso
        "making an abstract simplicial complex"
	(dual, SimplicialComplex)
	(star, SimplicialComplex, RingElement)
	bartnetteSphereComplex     
	(pdim, Module)
	(codim, Ideal)
///
 

/// 
    Key 
        (boundary, SimplicialComplex)
    Headline 
        make a new simplicial complex generated by the non-maximal faces
    Usage
     	boundary D
    Inputs
     	D : SimplicialComplex
    Outputs
     	: SimplicialComplex
	     whose faces are the non-maximal faces in {\tt D}
    Description
     	Text
     	    The boundary of an abstract simplicial complex $D$ is the
	    subcomplex consisting of all nonmaximal faces of
	    $D$. Equivalently, it is the subcomplex consisting of all
	    non-facets of $D$.
	Text
	    The boundary of the 3-simplex is the 2-sphere.
	Example
	    S = ZZ[a..d];
	    D = simplicialComplex {a*b*c*d}
	    sphere = boundary D
	    fVector sphere
	    fVector D
	    assert (ideal sphere === ideal (a*b*c*d) and dim sphere === dim D - 1)
	Text
	    The facets of $D$ need not be of the same dimension, which means
	    the boundary facets will not be of the same dimension.
	Example
	    S' = QQ[a..g];
	    D' = simplicialComplex {e, f*g, c*g, d*f, a*d, a*b*c}
	    D'' = boundary D'
	    fVector D'
	    fVector D''
	    assert (dim D'' === dim D' - 1) 
	Text
	    The boundary of the irrelevant complex is the void complex.
	Example
	    irrelevant = simplicialComplex {1_S}
	    boundary irrelevant
	    assert (dim boundary irrelevant === - infinity)
    SeeAlso
	"making an abstract simplicial complex"
        (facets, SimplicialComplex)
	(isPure, SimplicialComplex)
        (fVector, SimplicialComplex)
///


doc ///
    Key 
        (skeleton, ZZ, SimplicialComplex)
    Headline
        make a new simplicial complex generated by all faces of a bounded dimension
    Usage
        skeleton(n, D)
    Inputs
        k : ZZ
	    that bounds the dimension of the faces
        D : SimplicialComplex
    Outputs
        : SimplicialComplex
	    that is generated by all the faces in {\tt D} of dimension less
	    than or equal to {\tt k}
    Description
        Text
	    The $k$-skeleton of an abstract simplcial complex is the
	    subcomplex consisting of all of the faces of dimension at most
	    $k$.  When the abstract simplicial complex is 
	    @TO2((isPure, SimplicialComplex), "pure")@ its $k$-skeleton is
	    simply generated by its $k$-dimensional faces.	    
	Text
     	    The @HREF("https://en.wikipedia.org/wiki/5-cell", "4-simplex")@ is
     	    a simplicial 3-sphere with 5 vertices, 5 facets, and a
     	    minimal nonface that corresponds to the interior of the sphere.
    	Example
	    S = ZZ[a..e];
	    D = simplicialComplex monomialIdeal (a*b*c*d*e)
	    skeleton (-2, D)
	    skeleton (-1, D)	    
	    skeleton (0, D)	    	    
	    skeleton (1, D)	    	    	    
	    skeleton (2, D)	    	    	    	    
	    skeleton (3, D)
	    fVector D
	    assert (skeleton (-2, D) === simplicialComplex monomialIdeal 1_S and
		skeleton (-1, D) === simplicialComplex {1_S} and
		skeleton (0, D) === simplicialComplex gens S and
		skeleton (1, D) === simplicialComplex apply (subsets (gens S, 2), product) and
		skeleton (2, D) === simplicialComplex apply (subsets (gens S, 3), product) and	
		skeleton (3, D) === D)	
    	Text
	    The abstract simplicial complex from Example 1.8 of
            Miller-Sturmfels' {\em Combinatorial Commutative Algebra} consists
            of a triangle (on vertices {\tt a, b, c}), two edges (connecting
            {\tt c} to {\tt d} and {\tt b} to {\tt d}), and an isolated
            vertex (namely {\tt e}).  It has six minimal nonfaces.  Moreover,
	    its 1-skeleton and 2-skeleton are not pure.
    	Example
	    S' = ZZ/101[a..f];
	    D' = simplicialComplex {e, c*d, b*d, a*b*c}
	    skeleton (-7, D')
	    skeleton (-1, D')	    
	    skeleton (0, D')	    	    
	    skeleton (1, D')	    	    	    
	    skeleton (2, D')	    	    	    	    
	    assert (skeleton (-7, D') === simplicialComplex monomialIdeal 1_S' and
		skeleton (-1, D') === simplicialComplex {1_S'} and
		skeleton (0, D') === simplicialComplex {a, b, c, d, e} and
		skeleton (1, D') === simplicialComplex {e, c*d, b*d, b*c, a*c, a*b} and
		skeleton (2, D') === D')
    SeeAlso
	"making an abstract simplicial complex"
        (faces, SimplicialComplex)
	(fVector, SimplicialComplex)    
///



doc ///
    Key 
        (star, SimplicialComplex, RingElement)
	star
    Headline
        make the star of a face 
    Usage
        star(D, f)
    Inputs
        D : SimplicialComplex
        f : RingElement
	    a monomial representing a subset of the vertices in {\tt D} 
    Outputs
        : SimplicialComplex
	    that consists of all faces in {\tt D} whose union with {\tt f} is
	    also a face in {\tt D}
    Description
        Text
    	    Given a subset $f$ of the vertices in an abstract simplicial
	    complex $D$, the {\em star} of $f$ is the set of faces $g$ in $D$
	    such that the union of $g$ and $f$ is also a face in $D$.  This
	    set forms a subcomplex of $D$.  When the subset $f$ is not face in
	    $D$, the star of $f$ is a void complex (having no facets).	    
    	Text
	    In the "bowtie" complex, we see that a star may the entire
	    complex, a proper subcomplex, or the void complex.
	Example
	    S = ZZ[a..e];
	    bowtie = simplicialComplex {a*b*c, c*d*e}	    
    	    star (bowtie, c)
	    star (bowtie, a*b)
	    star (bowtie, a*d)
	    assert (star (bowtie, c) === bowtie and 
		star (bowtie, a*b) === simplicialComplex {a*b*c} and
		star (bowtie, a*d) === simplicialComplex monomialIdeal 1_S)
    SeeAlso
	"making an abstract simplicial complex"    
    	(faces, SimplicialComplex)
	(link, SimplicialComplex, RingElement)
///


doc ///
    Key 
        (symbol *, SimplicialComplex, SimplicialComplex)
        "join of two abstract simplicial complexes"
    Headline
        make the join 
    Usage
        J = D * E
    Inputs
        D : SimplicialComplex  
        E : SimplicialComplex
    Outputs
        J : SimplicialComplex
            that is the join of {\tt D} and {\tt E}
    Description
        Text
            The join of two simplicial complexes $D$ and $E$ is a new
            simplicial complex whose faces are disjoint unions of a face in
            $D$ and a face in $E$.
        Text
            If $E$ is the simplicial complex consisting of a single vertex,
            then the join $D*E$ is the
            @HREF("https://en.wikipedia.org/wiki/Cone_(topology)", "cone")@
            over $D$.  For example, the cone over a bow-tie complex.
     	Example
            R = QQ[a..e];
            bowtie = simplicialComplex {a*b*c, c*d*e}
            S = QQ[f];
            singleton = simplicialComplex {f};
	    C = bowtie * singleton
	    assert (dim C === dim bowtie + 1)
	Text
	    If $E$ is a 1-sphere (consisting of two isolated vertices), then
            the join $D * E$ is the
            @HREF("https://en.wikipedia.org/wiki/Suspension_(topology)",
            "suspension")@ of $D$.  For example, the octahedron is the
            suspension of a square.
        Example
	    R = QQ[a..d];
            square = simplicialComplex {a*b, b*c, c*d, a*d}
            S = QQ[e,f];
            oneSphere = simplicialComplex {e, f}
	    octahedron = square * oneSphere
	    faces octahedron
	    assert (dim octahedron === dim square + 1)
        Text
            The join of a hexagon and a pentagon is a 3-sphere.
        Example
            R = ZZ[a..f];
            hexagon = simplicialComplex {a*b, b*c, c*d, d*e, e*f, a*f}
            S = ZZ[g..k];
            pentagon = simplicialComplex {g*h, h*i, i*j, j*k, g*k}
            threeSphere = hexagon * pentagon
	    prune HH threeSphere
	    assert (dim threeSphere === 3)
    Caveat
        If the variables in the ring of $D$ and the ring of $E$ are not
        disjoint, then names of vertices in the join may not be
        understandable.
    SeeAlso
	"making an abstract simplicial complex"      
        (faces, SimplicialComplex)
///


///
-- need another example for star; to be added when suspension is completed?
   	Text
	    Given any face $G$ in the link of a face $F$, the link of $F$ in
	    the star of $G$ is the suspension of $G$ and the link of $F$ in
	    the link $G$.
	Example
	    S' = ZZ/101[a..g];
	    hexagon = simplicialComplex {a*b*c, a*c*d, a*d*e, a*e*f, a*f*g, a*b*g}  
	    link (hexagon, a*b)  
	    link (hexagon, g)
	    link(star(hexagon, g), a*b)
	    (simplicialComplex {g}) * link(link(hexagon,g), a*b)
	    link (hexagon, c)
	    link 
    	    star(hexagon, g)
	    link(star(hexagon, g), a*b)	
///

doc ///
    Key
	boundaryMap
	(boundaryMap, ZZ, SimplicialComplex)        
	[boundaryMap, Labels]
    Headline
        make a boundary map between oriented faces
    Usage 
        boundaryMap(i, D)
    Inputs
        i : ZZ
	    which gives the dimension of faces in the source of the map
	D : SimplicialComplex
	Labels => List
	          of monomials in a polynomial ring {\tt S}.
    Outputs 
	: Matrix
	    that represents the boundary map from {\tt i}-faces to {\tt
	    (i-1)}-faces of {\tt D}
    Description
    	Text
    	    The boundary maps, up to sign, form the differential in the
    	    augmented oriented chain complex associated to an abstract
    	    simplicial complex. If the {\tt Labels} option is used, then
	    the output is the ({\tt i}+1)^{st} differential map of the
	    complex of free {\tt S}-modules obtained from homogenizing {\tt D},
	    with respect to the given labelling (see @TO([(chainComplex,
	    SimplicialComplex),Labels])@ for more details.
        Text
            The columns of the output matrix are indexed by the $i$-faces of
     	    the abstract simplicial complex $D$ and the rows are indexed by
     	    the $(i-1)$-faces, in the order given by 
	    @TO2((faces, ZZ, SimplicialComplex), "faces")@ method.  The
	    entries in this matrix are $-1$, $0$, $1$ depending on whether the
	    row index is an oriented face of the column index, but the
	    underlying ring of this matrix is the @TO2((coefficientRing,
	    SimplicialComplex), "coefficient ring")@ of $D$.
	Text
	    The boundary maps for the standard 3-simplex, defined over 
	    @TO ZZ@, are:
    	Example
	    R = ZZ[a..d];
	    D = simplicialComplex {a*b*c*d}
	    boundaryMap (0, D)
	    boundaryMap (1, D)
	    boundaryMap (2, D)
	    boundaryMap (3, D)	    
    	    fVector D	    	    	    
    	    C = chainComplex D	    
	    assert (C.dd_0 == - boundaryMap (0, D) and
	    	C.dd_1 == - boundaryMap (1, D) and
	    	C.dd_2 == - boundaryMap (2, D) and	   
		C.dd_3 == - boundaryMap (3, D)) 
	Text
	    If we have a monomial ideal {\tt M} with 4 generators in a polynomial
	    ring {\tt S}, then the homogenization of {\tt D} by {\tt M} will give 
	    the Taylor resolution of {\tt R/M}. The differential maps for this 
	    resolution can be constructed using the {\tt Labels} option.
	Example
	    S = ZZ/101[x_0,x_1];
	    M = monomialIdeal(x_0^3,x_0^2*x_1,x_0*x_1^2,x_1^3);
    	    T = chainComplex(D, Labels => first entries mingens M);
	    T.dd
	    all(1..length T, i -> T.dd_i == boundaryMap(i-1,D,Labels => first entries mingens M))
	    boundaryMap(2,D,Labels=>first entries mingens M)
    	Text
            The boundary maps may depend on the coefficient ring as the
            following examples illustrate.
    	Example     
	    S = QQ[a..f];
	    D = simplicialComplex monomialIdeal(a*b*c, a*b*f, a*c*e, a*d*e, a*d*f, b*c*d, b*d*e, b*e*f, c*d*f, c*e*f);
	    boundaryMap (1, D)
	    S' = ZZ/2[a..f];
	    D' = simplicialComplex monomialIdeal(a*b*c, a*b*f, a*c*e, a*d*e, a*d*f, b*c*d, b*d*e, b*e*f, c*d*f, c*e*f);
	    boundaryMap (1, D')
    SeeAlso
        (chainComplex,SimplicialComplex)
///


document { 
     Key => {buchbergerComplex, (buchbergerComplex,List,Ring), (buchbergerComplex,MonomialIdeal)},
     Headline => "Buchberger complex of a monomial ideal",
     Usage => "buchbergerComplex(L,R)\nbuchbergerComplex I",
     -- Inputs => {
     --      },
     -- Outputs => {
     --      },
     -- Consequences => {
     --      },     
     -- "description",
     -- EXAMPLE {
     --      },
     -- Caveat => {},
 
     SeeAlso => {SimplicialComplexes}
     }

doc ///
     Key
         taylorResolution
	 (taylorResolution,List)
	 (taylorResolution,MonomialIdeal)
     Headline
         create the Taylor resolution of a monomial ideal
     Usage
         taylorResolution L
	 taylorResolution M
     Inputs
         L : List
	     of monomials in a polynomial ring, that minimally generate a monomial
	     ideal.
	 M : MonomialIdeal
     Outputs
         : ChainComplex
     Description
        Text
	    If {\tt M} is a monomial ideal, minimall generated by {\tt L}, then
	    the Taylor resolution of {\tt M} is the resolution of {\tt M} obtained
	    by homogenizing the ({\tt #L - 1})-simplex.
	Example
	    S = QQ[vars(0..3)]
	    M = monomialIdeal(a*b,c^3,c*d,b^2*c)
	    T = taylorResolution M
	    T.dd
	Text
	    If {\tt M} is generated by a regular sequence {\tt L}, then the Taylor
	    resolution is the Koszul complex on {\tt L}.
	Example
	    L = gens S
	    T = taylorResolution L;
	    K = koszul matrix{L};
	    T.dd
	    K.dd
    SeeAlso 
	 lyubeznikResolution
	 scarfChainComplex
	 koszul
///

doc ///
     Key
         lyubeznikSimplicialComplex 
	 [lyubeznikSimplicialComplex,MonomialOrder]
         (lyubeznikSimplicialComplex,List,Ring)
	 (lyubeznikSimplicialComplex,MonomialIdeal,Ring)
     Headline
         create a simplicial complex supporting a Lyubeznik resolution of a monomial ideal
     Usage
         lyubeznikSimplicialComplex(L,R)
	 lyubeznikSimplicialComplex(M,R)
     Inputs
         L : List
	     of monomials in a polynomial ring, that minimally generate a monomial
	     ideal.
	 M : MonomialIdeal
	 R : PolynomialRing
	     the ambient ring used in constructing the lyubeznik simplicial complex.
	 MonomialOrder => List
     Outputs
         D : SimplicialComplex
     Description
        Text
	    The Lyubeznik simplicial complex is the simplicial complex that
	    supports the @TO2(lyubeznikResolution, "Lyubeznik resolution")@ of 
	    an ordered set of monomials. This function is sensitive to the 
	    order in which the monomials in {\tt L} appear. If you are using a 
	    monomial ideal {\tt M} as your input, then the order of the
	    monomials is given by {\tt first entries mingens M}.
	Example
	    S = QQ[x,y];
	    R = QQ[a,b,c];
	    M = monomialIdeal{x*y,x^2,y^3};
	    D = lyubeznikSimplicialComplex(M,R)
	Text
	    The lyubeznik resolution of {\tt M} is the homogenization of
	    {\tt D} by {\tt M} (See @TO([(chainComplex, SimplicialComplex),Labels])@).
        Example
	    L = lyubeznikResolution(M);
	    L.dd
            L' = chainComplex(D,Labels=>(first entries mingens M));
	    L'.dd
	Text
	    Changing the order of the generators may change the output.
	    We can do this by manually entering the permuted list of generators,
	    or by using the optional {\tt MonomialOrder} argument.
	Example
	    first entries mingens M
	    D' = lyubeznikSimplicialComplex(M,R,MonomialOrder=>{1,2,0})
	    D' = lyubeznikSimplicialComplex({x^2,y^3,x*y},R)
	    (lyubeznikResolution(M,MonomialOrder=>{1,2,0})).dd
    SeeAlso 
         SimplicialComplexes
	 lyubeznikResolution
	 scarfSimplicialComplex
///

doc ///
    Key 
        lyubeznikResolution
	[lyubeznikResolution,MonomialOrder]
        (lyubeznikResolution,List)
	(lyubeznikResolution,MonomialIdeal)
    Headline
        create the lyubeznik resolution of an ordered set of monomials.
    Usage
        lyubeznikResolution L
	lyubeznikResolution M
    Inputs
        L : List
	    of monomials in a polynomial ring, that minimally generate a monomial 
	    ideal.
	M : MonomialIdeal
	MonomialOrder => List
    Outputs
        : ChainComplex
	  the Lyubeznik resolution of {\tt S/M}.
    Description
        Text
            For a monomial ideal {\tt M} in a polynomial ring {\tt S}, minimally
	    generated by {\tt L}, the Lyubeznik resolution is a resolution of
	    {\tt S/M} determined by a total ordering of the minimal generators
	    of {\tt M}. It is the subcomplex of the Taylor resolution of {\tt M}
	    induced on the rooted faces. If {\tt L} is used as input, the ordering is the
	    order in which the monomials appear in {\tt L}. If {\tt M} is used as
	    the input, the ordering is obtained from {\tt first mingens entries M}.
	    For more details on Lyubeznik resolutions and their construction, see
	    Jeff Mermin 
	    @HREF("https://www.degruyter.com/view/book/9783110250404/10.1515/9783110250404.127.xml", 
		"Three Simplicial Resoltuions")@, (English summary) Progress in
	     commutative algebra 1, 127–141, de Gruyter, Berlin, 2012.
        Example
	    S = QQ[x,y];
	    M = monomialIdeal{x*y,x^2,y^3};
	    F = lyubeznikResolution M;
	    F.dd
        Text
	    Changing the order of the generators may change the output.
	    We can do this by manually entering the permuted list of generators,
	    or by using the optional {\tt MonomialOrder} argument.
        Example
	    first entries mingens M
	    F' = lyubeznikResolution({x^2,y^3,x*y});
	    F'.dd
	    F' = lyubeznikResolution(M,MonomialOrder=>{1,2,0});
	    F'.dd
    SeeAlso 
        SimplicialComplexes
	lyubeznikResolution
	taylorResolution
///

doc///
    Key 
        scarfSimplicialComplex
	(scarfSimplicialComplex,List,Ring)
	(scarfSimplicialComplex,MonomialIdeal,Ring)
    Headline
        create the scarf simplicial complex for a list of monomials
    Usage
        scarfSimplicialComplex(L,R)
	scarfSimplicialComplex(M,R)
    Inputs
        L : List
	    of monomials in a polynomial ring, that minimally generate
	    a monomial ideal
	M : MonomialIdeal
	R : Ring
	    the ambient ring used to construct the Scarf simplicial complex.
    Outputs
        D : SimplicialComplex
    Description
        Text
	    The scarf simplicial complex is the simplicial complex that supports
	    the scarf complex of a monomial ideal. The scarf complex does not need
	    to be an acyclic simplicial complex. In fact, every simplicial complex
	    that is not the boundary of a simplex is the scarf complex for some
	    monomial ideal. For more information
	    on the Scarf simplicial complex and its construction, see Bayer, Dave; Peeva, 
	    Irena; Sturmfels, Bernd 
	    @HREF("https://www.intlpress.com/site/pub/files/_fulltext/journals/mrl/1998/0005/0001/MRL-1998-0005-0001-a003.pdf","Monomial Resolutions")@.
	    Math. Res. Lett. 5 (1998), no. 1-2, 31–46, and Jeff Mermin 
	    @HREF("https://www.degruyter.com/view/book/9783110250404/10.1515/9783110250404.127.xml", 
		"Three Simplicial Resolutions")@, (English summary) Progress in
	     commutative algebra 1, 127–141, de Gruyter, Berlin, 2012.
	Example
	    R = ZZ[a,b,c,d];
	    S = ZZ/17[x_0..x_3];
	    M  = monomialIdeal(x_0*x_1,x_1*x_2,x_2*x_3)
	    D = scarfSimplicialComplex(M,R)
	    prune homology D
	    M' = monomialIdeal(x_0*x_1,x_0*x_3,x_1*x_2,x_2*x_3)
	    D' = scarfSimplicialComplex(M',R)
	    prune homology D'
    SeeAlso
        SimplicialComplexes
        scarfChainComplex
	lyubeznikSimplicialComplex
///

doc///
    Key 
        scarfChainComplex
	(scarfChainComplex,List)
	(scarfChainComplex,MonomialIdeal)
    Headline
        create the scarf chain complex for a list of monomials.
    Usage
        scarfChainComplex L
	scarfChainComplex M
    Inputs
        L : List
	    of monomials in a polynomial ring, that minimally generate
	    a monomial ideal.
	M : MonomialIdeal
    Outputs
        C : ChainComplex
    Description
        Text
	    For a monomial ideal {\tt M}, minimall generated by {\tt L},
	    in a polynomial ring {\tt S}, the Scarf complex is the 
	    subcomplex of the Taylor resolution of {\tt S/M} that is
	    induced on the multihomogeneous basis elements with unique
	    multidegrees. If the Scarf Complex is a resolution, then it 
	    is the minimal free resolution of {\tt S/M}. For more information
	    on the Scarf complex and its construction, see Bayer, Dave; Peeva, 
	    Irena; Sturmfels, Bernd 
	    @HREF("https://www.intlpress.com/site/pub/files/_fulltext/journals/mrl/1998/0005/0001/MRL-1998-0005-0001-a003.pdf","Monomial Resolutions")@.
	    Math. Res. Lett. 5 (1998), no. 1-2, 31–46, and Jeff Mermin 
	    @HREF("https://www.degruyter.com/view/book/9783110250404/10.1515/9783110250404.127.xml", 
		"Three Simplicial Resolutions")@, (English summary) Progress in
	    commutative algebra 1, 127–141, de Gruyter, Berlin, 2012.
	Example
	    S = QQ[x_0..x_3,Degrees=>{{1,0,0,0},{0,1,0,0},{0,0,1,0},{0,0,0,1}}];
	    M = monomialIdeal(x_0*x_1,x_0*x_3,x_1*x_2,x_2*x_3);
	    T = taylorResolution M;
	    C = scarfChainComplex M;
	    T.dd
	    C.dd
	    flatten for i to length C list degrees C_i
	    prune homology C
	    T' = taylorResolution{x_0*x_1,x_0*x_2,x_0*x_3};
	    C' = scarfChainComplex{x_0*x_1,x_0*x_2,x_0*x_3};
	    T'.dd
	    C'.dd
	    prune homology C'
	    flatten for i to length C list degrees C'_i
    SeeAlso
    	scarfSimplicialComplex
	taylorResolution
	lyubeznikSimplicialComplex
///

doc /// 
    Key
        (isPure,SimplicialComplex)
    Headline
        returns whether the facets are equidimensional
    Usage
        isPure D
    Inputs
        D : SimplicialComplex
    Outputs
        : Boolean
	    which is true if the facets of {\tt D} are of the same dimension,
	    and false otherwise.
    Description
        Text
	    The simplicial complex below is a triangulated fish.
        Example
            R = ZZ[a..f];
	    D = simplicialComplex {a*b*c, a*b*d, d*e*f};
	    isPure D
	Text
	    By removing an edge of one of the triangles, we obtain a 
	    simplicial complex with a lower dimensional facet.
        Example
	    D' = simplicialComplex {a*b*c, b*d, d*e*f}
	    isPure D'
    SeeAlso
        SimplicialComplexes 
	(dim,SimplicialComplex)
	facets
///
 
///
-- Greg and Mike were working on this when Greg had to go home
-- 7/13/05  Good example though!
     "Hochster gives a formula relating the homology of the Alexander dual 
     to the betti numbers of the Stanley-Reisner ideal, see e.g., 
     Corollary 1.40 in
     Miller-Sturmfels, Combinatorial Commutative Algebra. ",
     EXAMPLE {
	  --R = QQ[a..f];
	  R = QQ[a..f, Degrees => {
                          {1, 1, 0, 0, 0, 0, 0}, 
                          {1, 0, 1, 0, 0, 0, 0}, 
                          {1, 0, 0, 1, 0, 0, 0}, 
			  {1, 0, 0, 0, 1, 0, 0}, 
			  {1, 0, 0, 0, 0, 1, 0}, 
			  {1, 0, 0, 0, 0, 0, 1}}]
	  oct = simplicialComplex monomialIdeal(a*b,c*d,e*f)
	  cube = dual oct
	  lk = (D,m) -> simplicialComplex monomialIdeal(ideal support m + ((ideal D):m));
	  F = link(oct,a)
	  rank HH_1(F)
	  C = res ideal cube
	  tally degrees C_3
	  checkHochster = (D,face) -> (
	       R := ring D;
	       face' := (product gens R) // face;
	       D' := dual D;
	       h := apply(0..dim D', i -> (
     	           rank HH_(i-1)(link(D',face'))));
	       C := res ideal D;
	       b := apply(0..dim D', i -> (
			 d := tally degrees C_(i+1);
			 if d#?(degree face) then d#(degree face) else 0));
	       (b,h))
          checkHochster(cube,b*d*e*f)
	  checkHochster(oct,a*c)
	  checkHochster(oct,a*b)
	  checkHochster(oct,c*d*e*f)
	  checkHochster(cube,a*b*c*d*e)
	  },
///

document { 
     Key => {(faces,ZZ,SimplicialComplex)},
     Headline => "the i-faces of a simplicial complex ",
     Usage => "faces(i,D)",
     Inputs => {
	  "i" => ZZ => "the dimension of the faces",
	  "D" => SimplicialComplex
          },
     Outputs => {
	  Matrix => {"with one row, whose entries are squarefree
	       monomials representing the faces of dimension ", 
	       TT "i", " of ", TT "D"}
          },
     "In Macaulay2, every ", TO2(SimplicialComplex, "simplicial complex"),
     " is equipped with a polynomial ring, and the matrix of i-faces
     is defined over this ring.",
     PARA {
     	  "This triangulation of the real projective plane has 6
     	  vertices, 15 edges and 10 triangles."
	  },
     EXAMPLE {
	  "R = ZZ[a..f]",
	  "D = simplicialComplex monomialIdeal(a*b*c,a*b*f,a*c*e,a*d*e,a*d*f,
	                                      b*c*d,b*d*e,b*e*f,c*d*f,c*e*f)",
          "faces(-1,D)",
	  "faces(0,D)",
	  "faces(1,D)",
	  "faces(2,D)",
	  "fVector D"
          },
     PARA{},
     "To avoid repeated computation, 
     the matrix of ", TT "i", "-faces is cached at ", 
     TT "D.cache.faces#i", ".
     This function will use this value if it has already been 
     computed.",
     SeeAlso => {SimplicialComplexes,
	  facets,
	  boundaryMap,
	  fVector
	  }
     }




-------------------------------------------------------------
-------------------------------------------------------------
-- 20/07/2018 Lorenzo: new/modified documentation

doc ///
    Key
        (fVector,SimplicialComplex)
    Headline
        the f-vector of a simplicial complex
    Usage
        f = fVector D
    Inputs
        D : SimplicialComplex
    Outputs
        f : List
	    where the {\tt i}-th entry is the number of faces
	    in {\tt D} of dimension {\tt i} for {\tt -1 <= i <= dim D},
	    or of squarefree degree {\tt i}.
    Description
        Text
            The pentagonal bipyramid has 7 vertices, 15 edges
            and 10 triangles.
	Example
            R = ZZ[a..g];
            biPyramid = simplicialComplex monomialIdeal(a*g, b*d, b*e, c*e, c*f, d*f);
            fVector biPyramid
	Text
            Every simplicial complex other than the void
            complex has a unique face of dimension -1.
        Example
            void = simplicialComplex monomialIdeal 1_R;
            fVector void
	Text
            For a larger example we consider the polarization
            of an Artinian monomial ideal from section 3.2 in
            Miller-Sturmfels, Combinatorial Commutative Algebra.
        Example
            S = ZZ[x_1..x_4, y_1..y_4, z_1..z_4];
            I = monomialIdeal(x_1*x_2*x_3*x_4, y_1*y_2*y_3*y_4, z_1*z_2*z_3*z_4, x_1*x_2*x_3*y_1*y_2*z_1, x_1*y_1*y_2*y_3*z_1*z_2, x_1*x_2*y_1*z_1*z_2*z_3);
	    D = simplicialComplex I;
	    fVector D
    SeeAlso
        SimplicialComplexes
        faces
///

-*


    Caveat
        The f-vector is computed using the Hilbert series
        of the Stanley-Reisner ideal. For example, see
        Hosten and Smith's chapter Monomial Ideals, in 
	@HREF("https://www.springer.com/gp/book/9783540422303", 
	"Computations in Algebraic Geometry with Macaulay2")@,
	Springer 2001.
    Sasha: As far as I'm aware, the flag functionality isn't currently implemented. 
    When/if it is, this example should be added to the documentation above.
	Text
	    The option {\tt Flag}, checks if the multigrading corresponds to
	    a proper d-coloring of {\tt D}, where d is the dimension of {\tt D}
	    plus one. If that is not the case, then the output is an empty HashTable.
	Text
            The boundary of the 3-dimensional cross-polytope is
            3-colorable. If we define this simplicial complex over
            a {\tt Z^3}-graded ring, we can ask for its flag
            f-vector.
        Example
            grading = {{1,0,0},{1,0,0},{0,1,0},{0,1,0},{0,0,1},{0,0,1}};
            S = ZZ[x_1..x_6, Degrees => grading];
            I = monomialIdeal(x_1*x_2,x_3*x_4,x_5*x_6);
            fVector(simplicialComplex I, Flag => true)
*-

document {
     Key => {algebraicShifting,(algebraicShifting,SimplicialComplex),[algebraicShifting,Multigrading]},
     Headline => "the algebraic shifting of a simplicial complex",
     Usage => "A = algebraicShifting D",
     Inputs => {
     "D" => SimplicialComplex,
     Multigrading => Boolean => "If true it returns the colored algebraic shifting w.r.t. the multigrading of the underlying ring."
          },
     Outputs => {
     "A" => {"The algebraic shifting of the simplicial complex ", TT "D", ". If ", TT "Multigrading => true", " then it returns the so called colored shifted complex."}
          },
     "The boundary of the stacked 4-polytope on 6 vertices. Algebraic shifting preserves the f-vector.",
     EXAMPLE {
      "R=QQ[x_1..x_6];",
      "I=monomialIdeal(x_2*x_3*x_4*x_5,x_1*x_6);",
      "stacked = simplicialComplex(I)",
      "shifted = algebraicShifting(stacked)",
      "fVector stacked",
      "fVector shifted"
          },
     "An empty triangle is a shifted complex.",
     EXAMPLE {
     "R=QQ[a,b,c];",
     "triangle = simplicialComplex{a*b,b*c,a*c};",
     "algebraicShifting(triangle) === triangle "
     },
     "The multigraded algebraic shifting does not preserve the Betti numbers.",
     EXAMPLE {
      "grading = {{1,0,0},{1,0,0},{1,0,0},{0,1,0},{0,0,1}};",
      "R=QQ[x_{1,1},x_{1,2},x_{1,3},x_{2,1},x_{3,1}, Degrees=>grading];",
      "delta = simplicialComplex({x_{1,3}*x_{2,1}*x_{3,1},x_{1,1}*x_{2,1},x_{1,2}*x_{3,1}})",
      "shifted = algebraicShifting(delta, Multigrading => true)",
      "prune (homology(delta))_1",
      "prune (homology(shifted))_1"
     },
     "References:",
     PARA {},
     "G. Kalai, Algebraic Shifting, Computational Commutative Algebra and Combinatorics, 2001;",
      PARA {},
     "S. Murai, Betti numbers of strongly color-stable ideals and squarefree strongly color-stable ideals, Journal of Algebraic Combinatorics."
     }

--These are documented in the above node.
undocumented { "Multigrading" }


doc ///
  Key
    Face
  Headline
   The class of faces of simplicial complexes.
  Description
   Text
        The class of faces of simplicial complexes on the variables of a polynomial ring.
        The faces are @TO MutableHashTable@s F with two @TO keys@
        
        F.vertices is a @TO List@ of vertices in the @TO PolynomialRing@ F.ring

   Example
     R=QQ[x_0..x_4];
     F=face {x_0,x_2}
     F.vertices
     I=monomialIdeal(x_0*x_1,x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_0);
     D=simplicialComplex I
     fc=faces(1,D)
     -- select(fc,j->j==F)
  SeeAlso
     SimplicialComplex
     faces
     facets
///

doc ///
  Key
    (symbol ==,Face,Face)
  Headline
   Compare two faces.
  Usage
    F==G
  Inputs
    F:Face
    G:Face
  Outputs
    :Boolean
  Description
   Text
        Checks whether F and G are equal.

   Example
     K=QQ;
     R=K[x_0..x_4];
     F=face {x_0,x_1}
     G1=face {x_1,x_0}
     G2=face {x_1,x_2}
     F==G1
     F==G2
  SeeAlso
     Face
     face
///


doc ///
  Key
    face
    (face,List)
    (face,List,PolynomialRing)
    (face,RingElement)
  Headline
    Generate a face.
  Usage
    face(L)
    face(L,R)
    face(m)
  Inputs
    L:List
    R:PolynomialRing
    m:RingElement
        a monomial
  Outputs
    :Face
  Description
   Text
        Generates a face out of a list L or a squarefree monomial.
        If L is not empty or a monomial the argument R is not required.

   Example
     K=QQ;
     R=K[x_0..x_4];
     F=face {x_0,x_1}
  SeeAlso
     SimplicialComplex
     faces
     facets
///

doc ///
  Key
    (dim,Face)
  Headline
    The dimension of a face.
  Usage
    dimension(F)
  Inputs
    F:Face
  Outputs
    :ZZ
      bigger or equal to -1
  Description
   Text
        Returns the dimension of a @TO Face@, i.e., the number of @TO vertices@ F minus 1.

   Example
     K=QQ;
     R=K[x_0..x_4];
     I=monomialIdeal(x_0*x_1,x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_0);
     D=simplicialComplex I
     fc = faces(D)
     -- apply(-1..1, j->apply(fc#j,dim))
  SeeAlso
     face
     facets
     faces
///

doc ///
  Key
    (vertices,Face)
  Headline
    The vertices of a face of a simplicial complex.
  Usage
    vertices(F)
  Inputs
    F:Face
  Outputs
    :List
  Description
   Text
        Returns a @TO List@ with the vertices of a @TO Face@ of a simplicial complex.
   Example
     R = QQ[x_0..x_4];
     I = monomialIdeal(x_0*x_1,x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_0);
     D = simplicialComplex I
     fc = facets(D)
     (faces D)#(1)
     --vertices fc#1
  SeeAlso
     face
     (facets,SimplicialComplex)
     (faces, SimplicialComplex)
///

doc ///
  Key
      (vertices, SimplicialComplex)
  Headline
      list the vertices of a simplicial complex.
  Usage
      vertices(D)
  Inputs
      D : SimplicialComplex
  Outputs
      :List
  Description
   Text
        Returns a @TO List@ with the vertices of a
        @TO2("SimplicialComplex","simplicial complex")@.
   Example
       R = QQ[x_0..x_4];
       vertices simplexComplex(2,R)
       I = monomialIdeal(x_0, x_1*x_2, x_2*x_3, x_3*x_4);
       D = simplicialComplex I
       vertices D
  SeeAlso
      face
      (facets,SimplicialComplex)
      (faces, SimplicialComplex)
///

doc ///
  Key
    isSubface
    (isSubface,Face,Face)
  Headline
    Test whether a face is a subface of another face.
  Usage
    isSubface(F,G)
  Inputs
    F:Face
    G:Face
  Outputs
    :Boolean
  Description
   Text
        Test whether F is a subface of G.

   Example
     K=QQ;
     R=K[x_0..x_4];
     G=face {x_0,x_1,x_2}
     F1=face {x_0,x_2}
     F2=face {x_0,x_3}
     isSubface(F1,G)
     isSubface(F2,G)
///

doc ///
  Key
    (substitute,Face,PolynomialRing)
  Headline
    Substitute a face to a different ring.
  Usage
    substituteFace(F,R)
  Inputs
    F:Face
    R:PolynomialRing
  Outputs
    :Face
  Description
   Text
        Substitute a face to a different ring.

   Example
     K=QQ;
     R=K[x_0..x_4];
     F=face {x_0,x_1,x_2}
     S=R**K[y]
     substitute(F,S)
///

doc ///
  Key
    (ring,Face)
  Headline
    Ring of a face.
  Usage
    ring(F)
  Inputs
    F:Face
  Outputs
    :Ring
  Description
   Text
        Ring of a face.

   Example
     K=QQ;
     R=K[x_0..x_4];
     F=face {x_0,x_1,x_2}
     ring F
///


doc ///
  Key
    (substitute,SimplicialComplex,PolynomialRing)
  Headline
    Substitute a simplicial complex to a different ring.
  Usage
    substitute(C,R)
  Inputs
    C:SimplicialComplex
    R:PolynomialRing
  Outputs
    :SimplicialComplex
  Description
   Text
        Substitute a simplicial complex to a different ring. R should contain the variables of the @TO ring@ of C.

   Example
     K=QQ;
     R=K[x_0..x_4];
     I=monomialIdeal(x_0*x_1,x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_0);
     C=simplicialComplex I
     S=R**K[y]
     C1=substitute(C,S)
     ring C1
  SeeAlso
     (substitute,Face,PolynomialRing)
///

doc ///
  Key
    isFaceOf
    (isFaceOf,Face,SimplicialComplex)
  Headline
    Substitute a face to a different ring.
  Usage
    substitute(F,R)
  Inputs
    F:Face
    R:PolynomialRing
  Outputs
    :Face
  Description
   Text
        Substitute a face to a different ring.

   Example
     R = QQ[x_1..x_5];
     C = simplicialComplex monomialIdeal (x_1*x_2,x_3*x_4*x_5)
     F1 = face {x_1,x_2}
     F2 = face {x_1,x_3}
     -- isFaceOf(F1,C)
     -- isFaceOf(F2,C)
///

doc ///
  Key
    (net,Face)
  Headline
    Printing a face.
  Usage
    net(F)
  Inputs
    F:Face
  Outputs
    :Net
  Description
   Text
        Prints a face. The vertices are printed without any brackets and with one space between them. Also prints the polynomial ring which contains the vertices.

   Example
     K=QQ;
     R=K[x_0..x_4];
     face {x_0,x_1}
///

///
  Key
    useFaceClass
    [faces,useFaceClass]
    [facets,useFaceClass]
  Headline
    Option to return faces in the class Face
  Description
   Text
    @TO Boolean@ @TO Option@ to return in the methods @TO faces@ and @TO facets@ a @TO List@ of @TO Face@s instead of a @TO Matrix@.
///

doc ///
  Key
    (faces,SimplicialComplex)
  Headline
    Compute all faces of a simplicial complex.
  Usage
    faces(C)
  Inputs
    C : SimplicialComplex
  Outputs
    : HashTable
  Description
   Text
        Return a list of lists of the faces of a simplicial complex.

   Example
    R = QQ[x_1..x_5];
    C = simplicialComplex monomialIdeal (x_1*x_2,x_3*x_4*x_5)
    fc = faces(C)
    fc#2
 ///


-------------------------------------------------------------------
-- some previously missing documentation


///
  Key
    (symbol ==,SimplicialComplex,SimplicialComplex)
  Headline
   Compare two simplicial complexes.
  Usage
    C1==C2
  Inputs
    C1:SimplicialComplex
    C2:SimplicialComplex
  Outputs
    :Boolean
  Description
   Text
        Checks whether C1 and C2 are equal.

   Example
    K=QQ;
    R=K[x_1..x_3];
    C1=simplicialComplex monomialIdeal (x_1*x_2*x_3)
    C2=simplicialComplex {face {x_1,x_2},face {x_2,x_3},face {x_3,x_1}}
    C1==C2
///





doc ///
  Key    
    (homology,ZZ,SimplicialComplex)
  Headline
    Compute the homology of a simplicial complex.
  Usage
    homology(j,C)
  Inputs
    j:ZZ
    C:SimplicialComplex
  Outputs
    :Module
  Description
   Text
     Compute the j-th reduced homology of C with coefficients in @TO (coefficientRing,SimplicialComplex)@ C.

   Example
    R=ZZ[x_0..x_5];
    D=simplicialComplex apply({{x_0, x_1, x_2}, {x_1, x_2, x_3}, {x_0, x_1, x_4}, {x_0, x_3, x_4}, {x_2, x_3, x_4}, {x_0, x_2, x_5}, {x_0, x_3, x_5}, {x_1, x_3, x_5}, {x_1, x_4, x_5}, {x_2, x_4, x_5}},face)
    prune homology(1,D)
  SeeAlso
    (homology,ZZ,SimplicialComplex,Ring)
   boundaryMap
   (chainComplex,SimplicialComplex)
///

doc ///
  Key    
    (homology,ZZ,SimplicialComplex,Ring)
  Headline
    Compute the homology of a simplicial complex.
  Usage
    homology(j,C,R)
  Inputs
    j:ZZ
    C:SimplicialComplex
    R:Ring
  Outputs
    :Module
  Description
   Text
     Compute the j-th reduced homology of C with coefficients in R.

   Example
    R=ZZ[x_0..x_5];
    D=simplicialComplex apply({{x_0, x_1, x_2}, {x_1, x_2, x_3}, {x_0, x_1, x_4}, {x_0, x_3, x_4}, {x_2, x_3, x_4}, {x_0, x_2, x_5}, {x_0, x_3, x_5}, {x_1, x_3, x_5}, {x_1, x_4, x_5}, {x_2, x_4, x_5}},face)
    prune homology(1,D,ZZ)
    prune homology(1,D,QQ)
    prune homology(1,D,ZZ/2)
  SeeAlso
    (homology,ZZ,SimplicialComplex)
   boundaryMap
   (chainComplex,SimplicialComplex)
///

doc ///
  Key    
    (homology,SimplicialComplex,Ring)
    (homology,Nothing,SimplicialComplex,Ring)
  Headline
    Compute the homology of a simplicial complex.
  Usage
    homology(C,R)
  Inputs
    C:SimplicialComplex
    R:Ring
  Outputs
    :GradedModule
  Description
   Text
     The graded module of reduced homologies of C with coefficients in R.

   Example
    R=ZZ[x_0..x_5];
    D=simplicialComplex apply({{x_0, x_1, x_2}, {x_1, x_2, x_3}, {x_0, x_1, x_4}, {x_0, x_3, x_4}, {x_2, x_3, x_4}, {x_0, x_2, x_5}, {x_0, x_3, x_5}, {x_1, x_3, x_5}, {x_1, x_4, x_5}, {x_2, x_4, x_5}},face)
    homology(D)
    homology(D,QQ)
    homology(D,ZZ/2)
  SeeAlso
    (homology,SimplicialComplex)
    (homology,ZZ,SimplicialComplex)
    (homology,ZZ,SimplicialComplex,Ring)
///

doc ///
  Key    
    (homology,SimplicialComplex)
    (homology,Nothing,SimplicialComplex)
  Headline
    Compute the homology of a simplicial complex.
  Usage
    homology C
  Inputs
    C:SimplicialComplex
  Outputs
    :GradedModule
  Description
   Text
     The graded module of reduced homologies of C with coefficients in R.

   Example
    R=ZZ[x_0..x_5];
    D=simplicialComplex apply({{x_0, x_1, x_2}, {x_1, x_2, x_3}, {x_0, x_1, x_4}, {x_0, x_3, x_4}, {x_2, x_3, x_4}, {x_0, x_2, x_5}, {x_0, x_3, x_5}, {x_1, x_3, x_5}, {x_1, x_4, x_5}, {x_2, x_4, x_5}},face)
    homology D
  SeeAlso
    (homology,SimplicialComplex,Ring)
    (homology,ZZ,SimplicialComplex)
    (homology,ZZ,SimplicialComplex,Ring)
///

------------------------------------------------------------------------------
-- simplicial maps
------------------------------------------------------------------------------
doc ///
    Key 
        "working with simplicial maps"
    Headline
        information about simplicial maps and the induced operations
    Description
	Text
	    Let $C$ and $D$ be simplicial complexes. A simplicial map is a
	    map $f : C \to D$ such that for any face $F \subset C$, we have
	    that $f(F)$ is contained in a face of $D$.
        Text
            Although the primary method for creating a simplicial map is
	    @TO (map, SimplicialComplex, SimplicialComplex, Matrix)@, there
	    are a few other constructors.
    	Text
    	    @SUBSECTION "Making simplicial maps"@
	Text
    	    @UL {
                TO (map, SimplicialComplex, SimplicialComplex, Matrix),
        	TO (id, SimplicialComplex),			
        	TO SimplicialMap,
        	TO (isWellDefined, SimplicialMap),
    	    }@
	Text
	    Having made a @TO2(SimplicialMap, "simplicial map")@, one can access its
	    basic invariants or test for some elementary properties by using
	    the following methods.
	    Having made a 
	    @TO2(SimplicialMap, "map of abstract simplicial complexes")@, one
	    can access its basic invariants or test for some elementary
	    properties by using the following methods.
    	Text
    	    @SUBSECTION "Determining attributes and properties of simplicial maps"@
	Text
    	    @UL {
        	TO (source, SimplicialMap),		
        	TO (target, SimplicialMap),				
        	TO (matrix, SimplicialMap),
    	    }@
    SeeAlso
        SimplicialComplex
///


doc ///
    Key
        SimplicialMap
    Headline
        the class of all maps between simplicial complexes
    Description
        Text
	    Let $C$ and $D$ be simplicial complexes. A simplicial map is a
	    map $f : C \to D$ such that for any face $F \subset C$, we have
	    that $f(F)$ is contained in a face of $D$.
        Text
	    To specify a map of simplicial complexes, the target and source
	    complexes need to be specificied as well as a matrix which
	    determines a map between the complexes' corresponding rings.
	Text
	    The primary constructor of a toric map is
	    @TO (map, SimplicialComplex, SimplicialComplex, Matrix)@.
    SeeAlso
    	"working with simplicial maps"
        SimplicialComplex
	(id, SimplicialComplex)
	(isWellDefined, SimplicialMap)
///


doc ///
    Key
        (source, SimplicialMap)
    Headline
        get the source of the map
    Usage
    	X = source f
    Inputs
    	f : SimplicialMap
    Outputs
    	X : SimplicialComplex
    	    that is the source of the map f
    Description
        Text
	    Given a simplicial map $f : C \to D$, this method returns the 
	    abstract simplicial complex $C$.
       	Text
	    todo need example
    SeeAlso
        "working with simplicial maps"
        (target, SimplicialMap)    
        (matrix, SimplicialMap)    		
	(isWellDefined, SimplicialMap)
        (map, SimplicialComplex, SimplicialComplex, Matrix)	
///


doc ///
    Key
	(target, SimplicialMap)
    Headline 
    	get the target of the map
    Usage
    	Y = target f
    Inputs
    	f : SimplicialMap
    Outputs
    	Y : SimplicialComplex
    	    that is the target of the map f	
    Description	    
        Text
	    Given a toric map $f : C \to D$, this method returns the
	    abstract simplicial complex $C$.
       	Text
	    todo need example	    
    SeeAlso
        "working with simplicial maps"    
        (source, SimplicialMap)    
        (matrix, SimplicialMap)    		
	(isWellDefined, SimplicialMap)
        (map, SimplicialComplex, SimplicialComplex, Matrix)
///	  

doc ///
    Key
	(matrix, SimplicialMap)
    Headline 
    	get the underlying map of rings
    Usage
    	g = matrix f
    Inputs
    	f : SimplicialMap
	Degree =>
	    unused
    Outputs
    	g : Matrix
    Description	    
        Text
	    todo
    SeeAlso
        "working with simplicial maps"    
        (source, SimplicialMap)    
        (target, SimplicialMap)    		
	(isWellDefined, SimplicialMap)
        (map, SimplicialComplex, SimplicialComplex, Matrix)
///	         

doc ///
    Key
        (id, SimplicialComplex)
    Headline
    	make the identity map from a SimplicialVariety to itself
    Usage 
        id_D
    Inputs 
        D : SimplicialComplex
    Outputs 
        : SimplicialMap
    Description
        Text	    
    	    The identity map on the underlying vertex set of an abstract
    	    simplicial complex induces the identity map on the entire complex.
	Example
	    S = ZZ[a..e];
	    D = simplexComplex(4,S)
	    f = id_D
	    assert (isWellDefined f and source f === D and
		target f === D and matrix f === vars S)
    SeeAlso
        "working with simplical maps" 
	(map, SimplicialComplex, SimplicialComplex, Matrix)	   
	id 
///    




