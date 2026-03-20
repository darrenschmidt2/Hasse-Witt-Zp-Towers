# Hasse-Witt-Zp-Towers
The file h1dr.m computes the matrices of the Frobenius and Cartier Operators on H1 de Rham Cohomology of a Z_p tower of curves over P1 totally ramified at infinity.

First let p be a prime and construct a polynomial ring A<t> := PolynomialRing(GF(p^r))

Then call F,V := computeH1dR(p,r,n,f) for GF(p^r) where p is prime,  n is the level of the tower, and f(t) is a polynomial such that y1^p-y1 = f

This returns the Frobenius operator F and Cartier operator V
