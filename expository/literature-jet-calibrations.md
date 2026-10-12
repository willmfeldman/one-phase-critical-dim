# Calibrations in jet space: a short history

> **Note.** This is an AI-written summary of a literature search. It has not yet been carefully
> verified by a human. Citations, dates and attributions should be checked against the original
> sources before use. Items tagged **[unverified]** were not checked against any source during the
> search; the others were checked only by fetching the link listed, which is not the same as reading
> the paper.

This is a companion to the expository note *The critical dimension for one-phase Bernoulli
minimizers*. It traces where the ideas behind the note's certificate come from. It uses the note's
vocabulary: *base*, *fiber*, *calibration in jet space*, *flux form*, *certificate* and
*obstruction*.

## The running example

The note starts from a one-dimensional model. To prove Wirtinger's inequality
$\int_0^L y'^2 \ge \mu \int_0^L y^2$ for $y(0)=y(L)=0$ and $\mu < (\pi/L)^2$, we look for a function
$F(x,y)$ with $F(x,0)=0$ such that

$$\eta^2 - \mu y^2 \;\ge\; F_x(x,y) + F_y(x,y)\,\eta \qquad \text{for all } (x,y,\eta).$$

Integrating along the jet $x \mapsto (x, y(x), y'(x))$ turns the right side into an exact derivative,
which integrates to zero. The point $(x,y)$ is the *base*. The slope $\eta$ is the *fiber*: the base
does not determine it, so the inequality must hold for every value of it, and $\eta$ enters the
derivative linearly. With $F = \rho(x)y^2$, completing the square in $\eta$ reduces the condition to
the Riccati inequality $\rho' + \rho^2 + \mu \le 0$, which $\rho = \omega\cot(\omega(x+x_0))$ solves
when $\mu = \omega^2$ and $\omega L < \pi$. Two features of the example matter for what follows. The
condition is *linear* in the unknown $F$, so the search for $F$ is convex. And above the threshold, the
function $y_* = \sin(\pi x/L)$ is an *obstruction*: integrating the pointwise inequality along $y_*$
would give something false, so no $F$ exists.

The Bernoulli certificate keeps this structure and changes three things. The base becomes the
normalized two-jet $(A,p,g)$ of an unknown cone. The unknowns become coefficient functions
$f, U, C, M, P$ on that base. Feasibility is settled by a semidefinite search followed by exact
rounding. Each change has its own history, and the three histories barely meet.

## 1. Adding an exact derivative

### Why one would do it

A quadratic functional such as $\int (y'^2 - \mu y^2)$ is not pointwise nonnegative: its integrand
changes sign. Adding a term that integrates to zero leaves the integral unchanged but can make the
integrand nonnegative, and then the integral inequality is obvious. The hard part is choosing the
term. The idea of the whole tradition is to let the term be the derivative of an unknown function and
to impose pointwise nonnegativity. That condition is linear in the unknown.

### Legendre, Jacobi, Picone **[unverified]**

The search notes credit the running example to Legendre's 1786 analysis of the second variation:
add $\frac{d}{dx}(w y^2)$ and complete the square, which leads to the Riccati equation for $w$.
Jacobi (1837) linearized that equation to the accessory equation. In the running example this is the
substitution $\rho = v'/v$, with $v = \sin(\omega(x+x_0))$. In this language Jacobi's conjugate points
are the obstruction: past the first conjugate point no smooth $\rho$ exists, and $\sin(\pi x/L)$ is the
corresponding counterexample. Picone's identity (1910) gives the same completion of the square for a
pair of Sturm–Liouville equations. All three dates and attributions come from memory and were not
checked against primary sources. The 1910 date for Picone also appears on a secondary web source.

### Field theory: Weierstrass, Hilbert, Carathéodory

The Riccati trick is quadratic. Field theory removes that restriction. In Carathéodory's
formulation, in *Variationsrechnung und partielle Differentialgleichungen erster Ordnung* (Teubner,
1935), sometimes called the "royal road" **[unverified]**, one subtracts the exact differential $dS$
of a function $S(x,y)$. The curve is then minimal if

$$L(x,y,y') - S_x - S_y\, y' \ge 0 \quad \text{for all slopes } y'.$$

This is the running example's condition with a general Lagrangian: a pointwise inequality on the
base that must hold for all fiber values and is linear in the unknown $S$.

### Null Lagrangians

Which terms may be added at all? Ball, Currie and Olver (1981) characterize the null Lagrangians of
higher-order jets. These are exactly the expressions whose integrals depend only on boundary data,
so they are the exact terms available when the test functions see higher derivatives. In the note,
the flux $Z$ plays this role: $\operatorname{div} Z$ is the exact term, and the boundary term
$N\cdot Z$ is what it leaves behind.

### Ground states and vector-field Hardy proofs

In several variables the unknown becomes a vector field and the exact term a divergence. The
Allegretto–Piepenbrink positivity principle (both 1974) says that a quadratic form of Schrödinger
type is nonnegative if and only if a positive supersolution exists. Its proof is the ground-state
substitution. In the note, this is the step from a flux proportional to $h\nabla h$ to a general flux
$Z$. Barbatis, Filippas and Tertikas (2004) prove Hardy inequalities with best constants from a
vector field $T$ satisfying

$$\operatorname{div} T - (p-1)|T|^{p/(p-1)} \ge V,$$

which is again a pointwise inequality whose integral gives the global one.

### Calibrations

Geometric measure theory names the same idea a *calibration*. In Harvey and Lawson (1982), a closed
form that bounds the area integrand pointwise, with equality on a given submanifold, proves that the
submanifold minimizes area. Alberti, Bouchitté and Dal Maso (2003) carry calibrations over to
Mumford–Shah and other free-discontinuity problems, which combine bulk and surface terms. Their
calibration condition is linear and convex in the field. A functional with bulk and surface parts is
the closest classical analogue of the note's pair of interior and boundary inequalities.

The note's own term, *calibration in jet space*, refers to this line: a function on a base whose
derivative along every jet bounds the integrand, for every value of the fiber.

## 2. Test functions given by universal formulas in the jet

### Why one would need them

In the tradition above, the object being calibrated is known: a curve, a submanifold, a fixed
operator. A stable cone that one hopes to rule out is unknown, so no particular test function can be
written down for it. What one can do is write the test function as a *universal formula* in the
local jet of the unknown solution, and use identities that every solution satisfies. The note makes
this precise: the half-space must not be declared unstable, so $h$ must vanish where the spherical
Hessian $T$ vanishes, and the natural building block is $w = |T|$.

### Simons and Schoen–Simon–Yau

The prototype is Simons (1968). For minimal cones, the norm $|A|$ of the second fundamental form
satisfies the Simons identity, a Bochner-type formula, and using $|A|$ as a test function in the
stability inequality shows that stable minimal cones are flat in low dimensions. Schoen, Simon and
Yau (1975) use test functions $|A|^{1+q}\varphi$ together with an improved Kato inequality, and the
admissible range of $q$ depends on the dimension. The improved Kato inequalities were later
systematized by Calderbank, Gauduchon and Herzlich (2000) as pointwise algebraic inequalities on
jets. The note's certificate on $\mathbb{R}^5$ uses one of them, $|q|^2 \le (5/7)|X|^2$.

### Bernoulli cones: Caffarelli–Jerison–Kenig and Jerison–Savin

For the one-phase problem, Caffarelli, Jerison and Kenig (2004) rule out nonflat cones in
$\mathbb{R}^3$ using a subsolution built from the norm of the Hessian, and conjecture flatness up to
$n = 6$. Jerison and Savin (2015) reach $\mathbb{R}^4$ with a hand-built test function in the jet.
Theirs is the direct predecessor of the note's richer ansatz $h = w^a\sqrt{f(A,p,g)}$ with a
general flux. The obstruction on the other side is the De Silva–Jerison cone in $\mathbb{R}^7$ (2009).
The search notes record only its role as the obstruction. How De Silva and Jerison prove that it
minimizes was not re-checked and is not described here.

### Feasibility by hand

In all of these works the free parameters (exponents, constants) are tuned by hand. The extreme case
comes from recent work on stable minimal hypersurfaces in $\mathbb{R}^4$, $\mathbb{R}^5$ and
$\mathbb{R}^6$: Chodosh–Li, Chodosh–Li–Minter–Stryker, and Mazet. These are not jet-formula proofs.
Still, Mazet tunes rational parameters by hand and checks $2\times 2$ and $3\times 3$ quadratic forms
exactly. That is a feasibility problem of the kind the note poses, solved without a computer search.



## 3. Searching for the exact term by convex optimization

### Why one would do it

Because the pointwise condition is linear in the unknowns, finding a certificate is a convex
feasibility problem. When the condition is polynomial nonnegativity, sums of squares turn it into a
semidefinite program. This line developed mainly in control theory and fluid dynamics, not in
geometric analysis.

### Sums of squares and Lyapunov functions

Parrilo's thesis (2000) reduces sum-of-squares conditions to semidefinite programs and uses
Positivstellensatz multipliers for constraints. In the note's certificate, the multiplier is the
gradient-bound function $\chi = 1 - |p|^2 - g^2$. Papachristodoulou and Prajna (2002) search for
Lyapunov functions this way. The analogy is exact: $\dot V$ is linear in $V$, just as
$F_x + F_y\eta$ is linear in $F$.

### Occupation measures: the dual side

Lasserre, Henrion, Prieur and Trélat (2008), and Henrion and Korda (2014), formulate optimal control
problems over occupation measures. On the dual side the unknowns are Hamilton–Jacobi subsolutions,
which is Carathéodory's field method made computational.

### Auxiliary functions, duality and obstruction

For bounds on time averages, Chernyshenko, Goulart, Huang and Papachristodoulou (2014) and Fantuzzi,
Goluskin, Huang and Chernyshenko (2016) introduced auxiliary functions. One adds the derivative of an
unknown function along trajectories, which averages to zero, and asks for pointwise nonnegativity.
Chernyshenko (2017) shows that the background method is the quadratic special case. Tobasco,
Goluskin and Doering prove strong duality: extremal trajectories obstruct better bounds. This is the model for the note's sharpness statement. A certificate on
$\mathbb{R}^6$ would exclude the De Silva–Jerison cone, so none exists. The cone obstructs every
certificate as $\sin(\pi x/L)$ obstructs every $F$.

### Exact rounding

A numerical solution is not a proof. Goluskin (arXiv 1610.05335) rounds numerical SDP output to
rigorous bounds. Goluskin and Fantuzzi (arXiv 1802.08240), working on Kuramoto–Sivashinsky, find
bounds saturated by steady states. The note's procedure is the same: round to rationals, write an
exact Gram identity, and bound the small remainder crudely on the compact base.

### Integral inequalities in jet variables

The closest technical precedents treat integral, not dynamical, inequalities.

- Valmorbida, Ahmadi and Papachristodoulou (2016), with Ahmadi, Valmorbida and Papachristodoulou
  (2016), require an integrand plus $\frac{d}{dx}$ of a polynomial in the jet variables to be a sum of
  squares. This is the running example's condition with polynomial unknowns.
- Fantuzzi, Wynn, Goulart and Papachristodoulou (2017, QUINOPT) treat quadratic integral
  inequalities.
- Chernyavsky, Bramburger, Fantuzzi and Goluskin (2023) are the best abstract match. They add
  divergence and null-Lagrangian terms, impose a pointwise inequality in $(x,u,\nabla u)$, relax it to
  sums of squares, and obtain sharp bounds for Sturm–Liouville and Poincaré constants. This is the
  running example in general form.

Bettiol, Kummer and Mendes (2021) use semidefinite programming for pointwise positivity of curvature
operators. This is another algebraic condition on jets settled by SDP.

### The sharpness caveat

Fantuzzi and Tobasco (arXiv 2207.13570) compare this pointwise relaxation with its occupation-measure
dual. Under a coercivity hypothesis the two give the same bound. That bound equals the true minimum
for one-dimensional, scalar-valued, or convex multidimensional problems, but generically it does not:
occupation measures ignore nonlinear constraints on gradient fields. Their non-sharp examples include
a one-dimensional scalar problem with a non-convex constraint (see also Fantuzzi, arXiv 2201.00362).
This matters for the note. The Bernoulli problem is multidimensional and non-convex, so there is no
general reason for a jet-space calibration to reach the true threshold. Here it happens to come
close: certificates exist on $\mathbb{R}^2$, $\mathbb{R}^3$ and $\mathbb{R}^5$, and the obstruction rules out
$\mathbb{R}^6$.

## What appears new in the Bernoulli argument

Each ingredient above has a long history. What we did not find is their combination. The search
looked for SOS/SDP methods together with stable cones, the Simons identity, Bochner/Weitzenböck
formulas, and computer-assisted free-boundary work. **We found no earlier instance** of a
convex-optimization search, with exact rounding, over test functions that are universal formulas in
the jet of an *unknown* solution, used to classify cones or solutions of a geometric PDE. The nearest
cases fall short in different ways:

- Chernyavsky et al. (2023) and Valmorbida et al. (2016) calibrate a *given* problem, not an unknown
  solution.
- Mazet (2024) solves a feasibility problem of this shape by hand.
- Jerison–Savin (2015) and its predecessors use universal jet formulas but tune them by hand.

The note's formulation adds features that we did not see in the convex-optimization literature. The
fiber includes undetermined higher derivatives of the solution, and they must cancel. This forces
the structure $\Gamma_{lijk} = \delta_{li}U_{jk} + C_{lijk}$ of the flux. A boundary inequality must
hold on every free-boundary shape. And sharpness comes from a geometric obstruction, the
De Silva–Jerison cone. This assessment rests on a single literature search. It should be read as
"not found", not as "does not exist".

## References

**Classical and calibration methods**

- Legendre, second-variation memoir, 1786. [unverified]
- Jacobi, on the second variation, 1837. [unverified]
- Picone, comparison identity, 1910. [unverified]
- Carathéodory, *Variationsrechnung und partielle Differentialgleichungen erster Ordnung*,
  Teubner, Leipzig–Berlin, 1935.
- Ball, Currie, Olver, "Null Lagrangians, weak continuity, and variational problems
  of arbitrary order", *J. Funct. Anal.* 41 (1981) 135–174.
  https://www-users.cse.umn.edu/~olver/e_/bco.pdf
- Allegretto, *Pacific J. Math.* 55 (1974) 319–328. https://msp.org/pjm/1974/55-2/p01.xhtml
- Piepenbrink, *J. Differential Equations* 15 (1974) 541–550.
- Barbatis, Filippas, Tertikas, *Trans. Amer. Math. Soc.* 356 (2004) 2169–2196.
  arXiv:math/0302326.
- Harvey, Lawson, "Calibrated geometries", *Acta Math.* 148 (1982) 47–157.
  DOI 10.1007/BF02392726.
- Alberti, Bouchitté, Dal Maso, "The calibration method for the Mumford–Shah functional and
  free-discontinuity problems", *Calc. Var. PDE* 16 (2003) 299–333. DOI 10.1007/s005260100152.

**Jet test functions, cones and free boundaries**

- Simons, *Ann. of Math.* 88 (1968) 62–105. DOI 10.2307/1970556.
- Schoen, Simon, Yau, *Acta Math.* 134 (1975) 275–288. DOI 10.1007/BF02392104.
- Calderbank, Gauduchon, Herzlich, *J. Funct. Anal.* 173 (2000) 214–255.
  arXiv:math/9909116.
- Caffarelli, Jerison, Kenig, *Contemp. Math.* 350 (2004) 83–97. DOI 10.1090/conm/350/06339.
- De Silva, Jerison, *J. reine angew. Math.* 635 (2009) 1–22.
- Jerison, Savin, *Geom. Funct. Anal.* 25 (2015) 1240–1257. arXiv:1410.7463.
- Chodosh, Li, arXiv:2108.11462.
- Chodosh, Li, Minter, Stryker, arXiv:2401.01492.
- Mazet, arXiv:2405.14676.
- Firester, Tsiamis, Wang, arXiv:2601.16966.
- Karakhanyan, Sanz-Perela, arXiv:2403.13059.
- Savin, Yu, arXiv:2502.18192 (not read).

**Convex optimization, auxiliary functions and SOS**

- Parrilo, PhD thesis, Caltech, 2000. DOI 10.7907/2K6Y-CH43.
- Papachristodoulou, Prajna, CDC 2002. https://users.ox.ac.uk/~engs0587/CDC02_1.pdf
- Lasserre, Henrion, Prieur, Trélat, *SIAM J. Control Optim.* 47 (2008) 1649–1666.
  arXiv:math/0703377.
- Henrion, Korda, *IEEE Trans. Automat. Control* 59 (2014) 297–312.
- Chernyshenko, Goulart, Huang, Papachristodoulou, *Phil. Trans. R. Soc. A* 372 (2014)
  20130350.
- Fantuzzi, Goluskin, Huang, Chernyshenko, *SIAM J. Appl. Dyn. Syst.* 15 (2016)
  1962–1988.
- Tobasco, Goluskin, Doering, arXiv:1705.07096.
- Chernyshenko, arXiv:1704.02475.
- Goluskin, "Bounding averages rigorously using semidefinite programming: mean moments of the
  Lorenz system", arXiv:1610.05335 (venue not confirmed).
- Goluskin, Fantuzzi, "Bounds on mean energy in the Kuramoto–Sivashinsky equation computed
  using semidefinite programming", arXiv:1802.08240 (venue not confirmed).
- Valmorbida, Ahmadi, Papachristodoulou, *IEEE Trans. Automat. Control* 61 (2016)
  1649–1654.
- Ahmadi, Valmorbida, Papachristodoulou, *Automatica* 66 (2016) 163–171.
- Fantuzzi, Wynn, Goulart, Papachristodoulou, *IEEE Trans. Automat. Control* 62 (2017)
  6221–6236 (QUINOPT). arXiv:1607.04210.
- Chernyavsky, Bramburger, Fantuzzi, Goluskin, "Convex relaxations of integral
  variational problems: pointwise dual relaxation and sum-of-squares optimization", *SIAM J. Optim.*
  33 (2023) 481–512. DOI 10.1137/21M1455127. arXiv:2110.03079.
- Fantuzzi, Tobasco, arXiv:2207.13570.
- Fantuzzi, arXiv:2201.00362.
- Bettiol, Kummer, Mendes, "Convex algebraic geometry of curvature operators",
  *SIAM J. Appl. Algebra Geom.* 5 (2021), no. 2 (page range unresolved). arXiv:1908.03713.

## Open checks

- Primary sources for Legendre (1786), Jacobi (1837) and Picone (1910), and the "royal road"
  characterization of Carathéodory's method.
- Venues for Goluskin (arXiv 1610.05335) and Goluskin–Fantuzzi (arXiv 1802.08240), and the page
  range of Bettiol–Kummer–Mendes.
- Not searched or not verified: Schoen–Uhlenbeck, Allen–Cahn, Bombieri–De Giorgi–Giusti,
  Gahlawat–Peet, Olver (GTM 107), Agmon.
- Searches for SOS methods applied to $\Gamma_2$ calculus, and for SDP-computed Hardy constants, found
  nothing relevant. They could be repeated with other terms.
- The central "not found" claim (a convex search over universal jet formulas for an unknown solution
  of a geometric PDE) should be re-checked before it is stated in print.
