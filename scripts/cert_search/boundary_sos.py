#!/usr/bin/env python3
"""Numerical Positivstellensatz search for the quartic boundary inequality (m = 3).

With Sq(s) the quartic of boundary_reduce.py (s = -l in (0, sqrt(2/3)]), solve in floating
point (cvxpy) for

    Sq(s) - 1/100 = sigma0(s) + s sigma1(s) + (2/3 - s^2) sigma2(s) + c s (2/3 - s^2),

with sigma0, sigma1, sigma2 sums of squares (Gram matrices in the bases [1, s, s^2], [1, s],
[1, s]) and c >= 0, maximizing the smallest eigenvalue of the Gram matrix of sigma0. It
prints that eigenvalue, the three Gram matrices and c. The numbers were rounded by hand to
the exact certificate stated and checked in Gen.boundaryQuartic_ge
(OnePhaseDimension/LowDim/CertificateThree/Boundary.lean); this script is exploratory and
nothing depends on its output. exact_check.py checks the same inequality independently by
exact Sturm counting.

Usage: python boundary_sos.py
"""
import cvxpy as cp, numpy as np
from sympy import *
s=symbols('s'); R=Rational
S=R(351,1000)*s**4+R(789,500)*s**3-R(267,400)*s**2-R(211,250)*s+R(779,2000)-R(1,100)
tgt=[float(c) for c in Poly(S,s).all_coeffs()[::-1]]  # c0..c4
Q0=cp.Variable((3,3),PSD=True); Q1=cp.Variable((2,2),PSD=True); Q2=cp.Variable((2,2),PSD=True); c=cp.Variable(nonneg=True)
t=cp.Variable()
# coefficient expressions
def coef(k):
  e=0
  for i in range(3):
    for j in range(3):
      if i+j==k: e=e+Q0[i,j]
  for i in range(2):
    for j in range(2):
      if i+j+1==k: e=e+Q1[i,j]
      if i+j==k: e=e+R(2,3).__float__()*Q2[i,j]
      if i+j+2==k: e=e-Q2[i,j]
  if k==1: e=e+2/3*c
  if k==3: e=e-c
  return e
cons=[coef(k)==tgt[k] for k in range(5)]
cons+=[Q0>>t*np.eye(3)]
cp.Problem(cp.Maximize(t),cons).solve()
print(t.value); print(Q0.value);print(Q1.value);print(Q2.value);print(c.value)
