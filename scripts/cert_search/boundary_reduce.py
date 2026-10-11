#!/usr/bin/env python3
"""Boundary polynomial of certs/m3a2950_cert.json at diagonal A, reduced to a quartic.

At a boundary point we may rotate so that p = e_3 and A = diag(x0, x1, l) with
x0 + x1 + l = 0, x0^2 + x1^2 + l^2 = 1 and l < 0. This script writes the boundary
polynomial S of the m = 3 certificate (coefficients of U and M copied from
certs/m3a2950_cert.json) at such a point, and checks with a Groebner basis over QQ that

    S(diag(x0, x1, l), e_3) - Sq(-l)  lies in the ideal (x0 + x1 + l, x0^2 + x1^2 + l^2 - 1),

where Sq(s) = 351/1000 s^4 + 789/500 s^3 - 267/400 s^2 - 211/250 s + 779/2000. It prints the
expanded polynomial, the remainder (expected 0) and the two quotients. This is the
computation behind Gen.boundaryPolyThree_diag3 in
OnePhaseDimension/LowDim/CertificateThree/Boundary.lean (where it is re-proved in Lean).

Usage: python boundary_reduce.py
"""
from sympy import *
x0,x1,l,s=symbols('x0 x1 l s')
R=Rational
a=[x0,x1,l]; b=[l*x0-x0**2,l*x1-x1**2,1]
c1=R(197,1000)-R(27,200)*l+R(429,1000)*l**2
c2=R(527,1000)-R(173,500)*l-R(1,1000)
c3=R(49,250)-R(17,40)
P=-l+c1+sum(c2*a[i]*b[i]+c3*a[i]**2*b[i] for i in range(3))+R(39,500)+R(69,500)*l
P=expand(P)
print(P)
S=R(351,1000)*s**4+R(789,500)*s**3-R(267,400)*s**2-R(211,250)*s+R(779,2000)
D=expand(P-S.subs(s,-l))
# reduce modulo ideal: x1 = -x0-l, then x0^2 via x0^2 = (1 - l^2 - x1^2) ...
G=groebner([x0+x1+l, x0**2+x1**2+l**2-1],x0,x1,l,order='lex',domain=QQ)
q,r=G.reduce(D); print('rem',r); print(q)
