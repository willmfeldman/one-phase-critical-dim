// The critical dimension of the one-phase Bernoulli problem: an expository account.

#set document(
  title: [The critical dimension of the one-phase Bernoulli problem: an expository account],
)
#set page(paper: "us-letter", margin: (x: 1.2in, top: 1.1in, bottom: 1.1in), numbering: "1")
#set text(font: "New Computer Modern", size: 11pt, lang: "en")
#set par(justify: true, leading: 0.62em, spacing: 0.9em, first-line-indent: 1.2em)
#set heading(numbering: "1.1")
#show heading: set block(above: 1.5em, below: 0.9em)
#show heading.where(level: 1): set text(size: 13pt)
#show heading.where(level: 2): set text(size: 11.5pt)
#set math.equation(numbering: n => {
  let h = counter(heading).get().first()
  numbering("(1.1)", h, n)
})
#set math.equation(supplement: none)
#show math.equation.where(block: true): it => {
  if it.has("label") { it } else {
    counter(math.equation).update(v => v - 1)
    [#math.equation(it.body, block: true, numbering: none)<eq-nonum>]
  }
}
#set enum(indent: 1em)
#set list(indent: 1em)
#show link: set text(fill: rgb("#1f3f7a"))
#show ref: set text(fill: rgb("#1f3f7a"))

// ---------- theorem-like environments ----------
#let thmcounter = counter(figure.where(kind: "thm"))
#show heading.where(level: 1): it => {
  thmcounter.update(0)
  counter(math.equation).update(0)
  it
}
#show figure.where(kind: "thm"): set block(breakable: true)
#show figure.where(kind: "thm"): it => {
  let name = if it.caption != none { [ (#it.caption.body)] } else { [] }
  block(width: 100%, above: 1.1em, below: 1.1em, align(left)[
    #set par(first-line-indent: 0em)
    *#it.supplement #it.counter.display(it.numbering)*#name*.* #it.body
  ])
}
#let thmnum = (..n) => numbering("1.1", counter(heading).get().first(), ..n)
#let mkenv(sup, italic: true) = (body, name: none) => figure(
  kind: "thm",
  supplement: sup,
  numbering: thmnum,
  caption: name,
  outlined: false,
  {
    if italic { set text(style: "italic"); body } else { body }
  },
)
#let theorem = mkenv([Theorem])
#let proposition = mkenv([Proposition])
#let lemma = mkenv([Lemma])
#let corollary = mkenv([Corollary])
#let definition = mkenv([Definition], italic: false)
#let remark = mkenv([Remark], italic: false)
#let example = mkenv([Example], italic: false)
#let question = mkenv([Question], italic: true)
#let proof(body, title: [Proof]) = block(width: 100%, above: 0.8em, below: 1.1em)[
  #set par(first-line-indent: 0em)
  _#title._ #body #h(1fr) $square$
]

// ---------- math operators ----------
#let dv = math.op("div")
#let Id = math.op("Id")
#let STF = math.op("STF")
#let Sing = math.op("Sing")
#let ip(a, b) = $lr(chevron.l #a, #b chevron.r)$


// ---------- title ----------
#align(center)[
  #v(0.4em)
  #text(size: 16.5pt, weight: "bold")[The critical dimension of the one-phase Bernoulli problem]
  #v(0.3em)
  #text(size: 12.5pt)[An expository account of the flatness of minimizing cones in dimensions at most six]
  #v(0.8em)
]

#block(inset: (x: 2.2em))[
  #set par(first-line-indent: 0em)
  #set text(size: 10pt)
  *Abstract.* A nonflat one-homogeneous global minimizer of the one-phase Bernoulli energy exists
  in $RR^7$ (De Silva and Jerison), and none exists in dimensions at most four (Caffarelli, Jerison
  and Kenig; Jerison and Savin). A recent preprint closes the remaining gap: there are no nonflat
  minimizing cones in dimensions five and six, so the critical dimension is seven. This note explains
  how that proof works and why it is organized as it is. After the standard reduction to a cone with
  a smooth link, the argument is an instability proof: one exhibits a test function for which the
  second variation of the energy is negative. The test function and an auxiliary vector field are
  built from the normalized Hessian of the cone, and the pointwise inequalities they must satisfy
  are inequalities between finitely many tensor variables. These are settled by an explicit algebraic
  certificate, verified in exact arithmetic. We motivate each step: what the classical
  Jacobi-subsolution strategy asks for, how "calibrations in jet space" turn it into a
  finite-dimensional positivity question, why plain powers of the Hessian norm work for cones in
  $RR^3$ but fail from $RR^4$ on, how a richer ansatz repairs this, and how the singular set of the
  test function is removed. The same method, with very small certificates, also reproves the
  classification in dimensions three and four.
]

#v(0.6em)
#block(inset: (x: 2.2em))[
  #set text(size: 10pt)
  #outline(depth: 1, indent: 1.2em, title: [Contents])
]

= Introduction <sec:intro>

== The problem

For a ball $B subset RR^n$ and a nonnegative $v in H^1(B)$, the _one-phase Bernoulli energy_ is
$ J(v; B) = integral_B (|nabla v|^2 + bb(1)_({v > 0})) dif x. $ <eq:energy>
It balances the Dirichlet energy of $v$ against the volume of its positive set. A nonnegative
$u in H^1_"loc" (RR^n)$ is a _global minimizer_ if $J(u;B) <= J(v;B)$ for every ball $B$ and every
nonnegative $v in H^1(B)$ with $v - u in H^1_0(B)$. Allowing sign-changing competitors changes
nothing, because replacing $v$ by its positive part $v_+$ keeps the boundary values and does not
increase the energy. Minimizers are harmonic in the open set ${u>0}$, and on the _free boundary_
$partial{u > 0}$ they satisfy, in a weak sense, the Bernoulli condition $|nabla u| = 1$.

A function is _one-homogeneous_ if $u(r x) = r u(x)$ for $r > 0$. The basic examples are the
_flat_ solutions $u(x) = (x dot e)_+$ with $|e| = 1$, and one-homogeneous minimizers are called
_minimizing cones_. Let $n_*$ denote the least dimension in which a nonzero, nonflat, one-homogeneous
global minimizer exists.

#theorem(name: [Critical dimension @OpenAI2026])[
  Every nonzero one-homogeneous global minimizer of @eq:energy in $RR^n$, $1 <= n <= 6$, is flat.
  There is a nonflat one-homogeneous global minimizer in $RR^7$. Consequently $n_* = 7$.
] <thm:main>

The second sentence is the theorem of De Silva and Jerison @DeSilvaJerison2009. The content of
@thm:main is the first sentence in dimensions five and six; dimensions at most four were known
@AltCaffarelli1981 @CaffarelliJerisonKenig2004 @JerisonSavin2015, and we shall see that the same method
reproves them.

Minimizing cones govern the singularities of general minimizers. For a local minimizer $u$ in an
open set $cal(O) subset RR^n$ (the same comparison on balls compactly contained in $cal(O)$), a free boundary
point $x_0$ is _regular_ if some blowup $lim u(x_0 + r x) \/ r$ along $r -> 0$ is a flat solution,
and _singular_ otherwise; $Sing(u)$ is the set of singular points.

#corollary(name: [Singular set])[
  Let $u$ be a nonnegative local minimizer of @eq:energy in an open set $cal(O) subset RR^n$. Its free
  boundary is smooth near every regular point. The singular set is empty if $n <= 6$, locally finite
  if $n = 7$, and $dim_cal(H) Sing(u) <= n - 7$ for $n >= 7$. For every $n >= 7$ this bound is attained.
] <cor:sing>

== Context

The variational theory begins with Alt and Caffarelli @AltCaffarelli1981, who proved existence,
Lipschitz regularity and nondegeneracy of minimizers, and the regularity of flat free boundaries.
Caffarelli's Harnack-inequality approach @Caffarelli1987 and De Silva's improvement of flatness
@DeSilva2011 give $C^(1,alpha)$ regularity near regular points; higher regularity goes back to
Kinderlehrer and Nirenberg @KinderlehrerNirenberg1977, and in the generality needed here is due to De
Silva, Ferrari and Salsa @DeSilvaFerrariSalsa2014 @DeSilvaFerrariSalsa2019. Weiss's monotonicity
formula @Weiss1999 shows that blowups are minimizing cones, and his dimension reduction converts a
classification of cones into the bound of @cor:sing. A modern account of all of this is
Velichkov's book @Velichkov2023.

Thus everything hinges on $n_*$. It is classical that $n_* >= 3$ (Alt and Caffarelli). Caffarelli,
Jerison and Kenig @CaffarelliJerisonKenig2004 proved that there are no nonflat minimizing cones in
$RR^3$, and Jerison and Savin @JerisonSavin2015 proved that stable homogeneous solutions with smooth
cross-section are flat in dimensions at most four, giving $n_* >= 5$. In the other direction De Silva
and Jerison @DeSilvaJerison2009 constructed a nonflat minimizing cone in $RR^7$, so $n_* <= 7$. Further
symmetric minimizing cones, including a second example in $RR^7$, were constructed by Firester, Tsiamis
and Wang @FiresterTsiamisWang2026Capillary, who also showed @FiresterTsiamisWang2026 that their
cohomogeneity-one cones with $O(n - k) times O(k)$ symmetry are unstable for $n <= 6$ and strictly
stable for $n >= 7$. The result discussed here assumes no symmetry. It concerns cones; rigidity of
arbitrary entire stable solutions is a different question, settled in dimension four by
Fernández-Real and Serra @FernandezRealSerra2026. For generic boundary data, Fernández-Real and Yu
@FernandezRealYu2025 obtained regularity through dimension six by a different route.

The analogy with minimal surfaces is close. There the critical dimension is eight: Simons
@Simons1968 proved that stable minimal cones with smooth link are flat in dimensions at most seven, by
testing the stability inequality with a power of the norm of the second fundamental form, and the
Simons cone in $RR^8$ is minimizing. Jerison and Savin developed the Bernoulli analogue, with the
Hessian of the cone in the role of the second fundamental form, and explained why powers of the Hessian
norm do not give a uniform instability criterion in dimensions four through six
@JerisonSavin2015[Section 3.2]; their four-dimensional argument uses a more refined function of the
Hessian eigenvalues. The proof discussed here replaces the single test function by a test function
together with a vector field, both built from the jet of the cone, and verifies the resulting pointwise
inequalities by a finite algebraic certificate.

== The shape of the proof

The argument has four layers, summarized in @fig:architecture.

+ *Reduction* (@sec:reduction). If all minimizing cones in $RR^(n-1)$ are flat, a nonflat minimizing
  cone in $RR^n$ is smooth away from the origin, and some component of its positive set has a
  nonvanishing Hessian. Its link is a smooth domain on the sphere carrying a solution of an
  overdetermined eigenvalue problem.
+ *What must be produced* (@sec:stability). Minimality implies a stability inequality on the link. To
  contradict it one needs a nonnegative "Jacobi subsolution", or more flexibly a test function together
  with a vector field whose divergence controls the energy of the test function and whose boundary flux
  has the right sign.
+ *How to find it* (@sec:calibration to @sec:certificate). Since the cone is unknown, the test function and
  the field must be universal formulas in the local jet of the cone; the required inequalities then become
  pointwise inequalities on the space of jets. The simplest choice, a power of the Hessian norm, works
  only for cones in $RR^3$. A richer ansatz, dictated by the way the simple one fails, leads to polynomial
  inequalities in finitely many tensor variables, which are proved by an exact algebraic certificate.
+ *Integration* (@sec:integration). The fields are singular where the Hessian vanishes. A weighted
  Bochner estimate shows that this set is invisible to the energy, and integration yields a
  contradiction. Dimension five is reduced to dimension six by a suspension (@sec:suspension).

#figure(
  {
    set text(size: 9pt)
    let bx(body) = box(stroke: 0.6pt, inset: 6pt, radius: 3pt, width: 100%, align(center, body))
    let arr(body) = align(center, block(inset: (y: 1pt))[$arrow.b$ #h(0.4em) #text(style: "italic", body)])
    block(width: 72%, stack(
      spacing: 3pt,
      bx[nonflat minimizing cone in $RR^n$; all minimizing cones in $RR^(n-1)$ flat],
      arr[dimension reduction (@sec:reduction)],
      bx[smooth link $Omega subset S^(n-1)$ with nonzero Hessian],
      arr[second variation and Hardy constant (@sec:stability)],
      bx[stability inequality on $Omega$; need a test function and a flux],
      arr[jet-space calibration and ansatz (@sec:calibration to @sec:flux) #h(0.3em) $arrow.l.double$ #h(0.3em) certificate (@sec:certificate)],
      bx[pointwise inequalities where the Hessian is nonzero],
      arr[cutoffs and weighted Bochner estimate (@sec:integration)],
      bx[contradiction],
    ))
  },
  caption: [The logical structure of the exclusion of nonflat minimizing cones.],
) <fig:architecture>

Throughout, the proof is organized as an induction on the dimension: flatness of cones in $RR^(n-1)$
is the input that makes cones in $RR^n$ smooth away from the vertex. Dimension one is elementary, and
dimensions two through six are obtained one at a time. The flatness statement of @thm:main for $n <= 6$
has been formally verified in the Lean proof assistant, including the algebraic certificates, which are
checked in exact arithmetic; the verification takes the Lipschitz regularity of minimizers and the
smoothness of free boundaries near flat blowups as cited inputs.

== Conventions

On a domain $Omega subset S^m$ we use the round metric, covariant derivatives $nabla$, the
Laplace--Beltrami operator $Delta$, and orthonormal frames in which repeated indices are summed. $N$
denotes the unit normal to $partial Omega$ pointing _into_ $Omega$ (into the positive phase). For a
symmetric tensor, _trace-free_ means that every contraction of two slots vanishes, and $STF^r (RR^m)$
is the space of symmetric trace-free $r$-tensors. Mean curvatures are sums of principal curvatures, not
divided by the dimension. The letter $n$ always denotes the ambient dimension of a cone and $m = n - 1$
the dimension of its link.

= From minimizers to cones with smooth links <sec:reduction>

The instability argument at the heart of the proof needs a smooth object to work on: a domain on the
sphere with smooth boundary, carrying a function that solves an explicit boundary value problem. A
general minimizing cone has no such structure a priori; its free boundary could be singular away from
the vertex. The purpose of this section is to show that, if all minimizing cones in one dimension lower
are flat, then a nonflat minimizing cone does have this structure. This is the only place where the
regularity theory of minimizers enters, and it is what makes the proof an induction on the dimension.

== Regularity inputs

Two questions must be answered about a minimizing cone: what do its blowups at points of the free boundary
look like, and when is the free boundary smooth? Regularity theory answers both. We use the following
standard facts for a nonnegative local minimizer $u$ in an open subset of $RR^n$, $n >= 2$
@AltCaffarelli1981 @Velichkov2023.

+ $u$ has a locally Lipschitz representative, harmonic in ${u > 0}$.
+ At a free boundary point $x_0$, every sequence $r_j -> 0$ has a subsequence along which
  $u(x_0 + r_j x) \/ r_j$ converges locally uniformly; every such limit is a nonzero one-homogeneous
  global minimizer (nondegeneracy, compactness, and Weiss monotonicity @Weiss1999).
+ If one such limit is flat, then near $x_0$ the free boundary is a smooth hypersurface, ${u > 0}$ is
  one of its sides, $u$ is smooth up to it from that side, and $u = 0$, $nabla u = N$ on it
  @DeSilva2011 @DeSilvaFerrariSalsa2019 @KinderlehrerNirenberg1977 @GilbargTrudinger2001.
  Equivalently, $u = max{F, 0}$ near $x_0$ for a smooth $F$ with $|nabla F| = 1$ on ${F = 0}$ and
  $Delta F = 0$ on ${F > 0}$ (extend $u$ across the free boundary by Seeley's theorem @Seeley1964).

== Dimension reduction

By item 3, a free boundary point is smooth as soon as _one_ blowup there is flat. So to show that a cone
$u$ in $RR^n$ is smooth away from its vertex, it suffices to show that its blowups at points $x_0 != 0$ are
flat. The key observation is that such blowups are effectively lower-dimensional, so that the inductive
hypothesis applies to them.

Let $x_0 != 0$ be a free boundary point of the cone $u$. Homogeneity gives an exact identity between
rescalings at $x_0$ at two nearby scales and a translate along $x_0$; passing to the limit, every blowup
$U$ at $x_0$ is invariant under translation in the direction $x_0$. So $U$ depends only on the $n - 1$
coordinates orthogonal to $x_0$: $U = u_1 compose pi$, where $pi$ is the orthogonal projection onto $x_0^perp$. To
use the inductive hypothesis on $u_1$ we need to know that $u_1$ is itself a minimizer.

#lemma(name: [Factors])[
  If $u_1$ is a function on $RR^(n-1)$ and $(x', x_n) |-> u_1 (x')$ is a global minimizer on $RR^n$, then $u_1$
  is a global minimizer on $RR^(n-1)$.
] <lem:products>

#proof(title: [Idea])[
  A competitor that improves $u_1$ by a fixed amount on a ball $B subset RR^(n-1)$ is extended to $B times [-L, L]$
  and cut off linearly in $x_n$ on two unit intervals. The gain is proportional to $L$, while the cost of the
  two transition regions is bounded, so for $L$ large the competitor beats $u_1 compose pi$.
]

So $u_1$ is a nonzero, one-homogeneous global minimizer in $RR^(n-1)$. If all such minimizers are flat, then
$u_1$ is a half-space solution, hence so is $U$, and by item 3 the point $x_0$ is regular. Thus, under the
inductive hypothesis, every free boundary point of $u$ other than the origin is regular, with a smooth
one-sided chart. (The same mechanism, applied to blowups at singular points of an arbitrary minimizer, is
Weiss's dimension reduction behind @cor:sing.)

Regularity alone is not enough: the half-space solution is a smooth cone too. The induction needs a
component of the positive set on which the cone is genuinely curved, that is, on which its Euclidean
Hessian $nabla^2 u$ does not vanish identically.

#definition(name: [Cones with an isolated singularity])[
  A _nonflat minimizing cone with an isolated singularity_ in $RR^n$ is a pair $(u, D)$, where $u$ is a
  continuous, nonnegative, one-homogeneous global minimizer in $RR^n$ and $D$ is a connected component
  of ${u > 0}$, such that every point of $overline(D) without {0}$ has a smooth one-sided chart as in
  item 3 above with positive side contained in $D$, and $nabla^2 u equiv.not 0$ on $D$.
] <def:cone>

#proposition(name: [Reduction])[
  Let $n >= 2$, and suppose that every nonzero minimizing cone in $RR^(n-1)$ is flat. If $u$ is a nonzero
  nonflat minimizing cone in $RR^n$, then $(u, D)$ is a nonflat minimizing cone with an isolated
  singularity for a suitable component $D$.
] <prop:reduction>

#proof(title: [Idea])[
  Charts at points of $overline(D) without {0}$ come from the previous paragraph; the positive side of a
  chart is connected and so lies in a single component, which gives local separation of components.
  If $nabla^2 u$ vanished on every component, each component would be a half-space on which $u$ is linear.
  Two disjoint half-spaces through the origin would share boundary points other than the origin,
  contradicting local separation; so there is a single half-space component, and the Bernoulli condition
  forces the slope to be one. Then $u$ is flat.
]

For a cone with an isolated singularity, write $u(r y) = r g(y)$ for $y in S^m$, and let
$Omega = D inter S^m$ be the _link_. It is a domain with smooth boundary, and the polar form of the
Laplacian and the Bernoulli condition give the overdetermined problem
$ Delta g = -m g, quad g > 0 quad "in" Omega, wide g = 0, quad nabla g = N quad "on" partial Omega. $ <eq:link>
At $r y$ the Euclidean Hessian $nabla^2 u$ vanishes in the radial direction and, on the tangent space of
$S^m$, equals $r^(-1) T(y)$, where
$ T = nabla^2 g + g Id $
is the _spherical Hessian of the cone_. Nonflatness means $T equiv.not 0$ on $Omega$. The rest of the proof
shows that no such $(Omega, g)$ exists for $n <= 6$.

= Stability: what has to be produced <sec:stability>

This section turns minimality into a usable inequality on the link and identifies precisely what object
would contradict it. The answer, a positive Jacobi subsolution or more generally a test function paired with
a vector field, is the target of everything that follows. Throughout, $(u, D)$ is a nonflat minimizing cone
with an isolated singularity in $RR^n$, with link $Omega subset S^m$.

== The second variation

Minimality says that every admissible perturbation increases the energy. The natural perturbations are
smooth deformations of $u$ near the free boundary. Let $phi$ be a smooth function on $overline(D)$ with compact
support away from the origin. Extend $u$ across $partial D$ by the smooth function $F$ of a chart and compare $u$
with $(F + tau phi)_+$ for small $tau$ of either sign. The energy changes in two ways: on the fixed domain $D$
the Dirichlet energy changes by $2 tau integral_D nabla u dot nabla phi + tau^2 integral_D |nabla phi|^2$, and near $partial D$
the positive set moves. Expanding the moving-boundary contribution in a boundary layer, the linear terms
cancel by the Bernoulli condition $|nabla u| = 1$, the terms involving the normal derivative of $phi$ cancel
as well, and what remains is the curvature of the free boundary:
$ J(u_tau) - J(u) = tau^2 (integral_D |nabla phi|^2 dif x - integral_(partial D) H_D phi^2) + o(tau^2), wide H_D = -nabla^2 u(N, N), $
where $H_D$ is the mean curvature of the free boundary. Minimality gives the _stability inequality_
$integral_(partial D) H_D phi^2 <= integral_D |nabla phi|^2$ for all such $phi$, with arbitrary boundary values.

== Separation of variables and the Hardy constant

Since the cone is invariant under dilations, it is natural to test with separated functions and to
transfer the inequality to the link. Take $phi(r y) = zeta(r) v(y)$. On the cone, $H_D (r y) = r^(-1) H(y)$
with $H = -T(N, N)$ the mean curvature of $partial Omega$ in $S^m$, the volume element is $r^m dif r dif V$ and the
boundary element is $r^(m-1) dif r dif sigma$. The stability inequality separates into
$ (integral_0^oo r^(m-2) zeta^2) integral_(partial Omega) H v^2 <= (integral_0^oo r^(m-2) zeta^2) integral_Omega |nabla v|^2 + (integral_0^oo r^m zeta'^2) integral_Omega v^2. $
The ratio $integral r^m zeta'^2 \/ integral r^(m-2) zeta^2$ can be brought arbitrarily close to the sharp
radial Hardy constant $((m-1)\/2)^2$, using $zeta(r) = r^(-(m-1)\/2) psi((log r)\/L)$ for a fixed bump $psi$ and
letting $L -> oo$. With $beta_m = (m - 1)\/2$ we obtain the _spherical stability inequality_
$ integral_(partial Omega) H v^2 <= integral_Omega (|nabla v|^2 + beta_m^2 v^2) $ <eq:sph-stab>
for all smooth $v$ on $overline(Omega)$. For links in $S^5$, $beta_5^2 = 4$. The Hardy constant is the first
place where the dimension enters: it grows quadratically in $m$.

== Jacobi subsolutions and fluxes

#question[What would contradict @eq:sph-stab?]

Integrating by parts with the inward normal,
$ integral_Omega (|nabla h|^2 + beta_m^2 h^2) - integral_(partial Omega) H h^2 = - integral_Omega h (Delta h - beta_m^2 h) - integral_(partial Omega) h (partial_N h + H h). $ <eq:Q>
So the cone is unstable as soon as there is a nonnegative $h$, not identically zero, with
$ Delta h >= beta_m^2 h "in" Omega, wide partial_N h + H h >= 0 "on" partial Omega, $ <eq:jacobi-sub>
strictly somewhere: a positive _Jacobi subsolution_.

The boundary condition in @eq:jacobi-sub ties the flux through $partial Omega$ rigidly to $h$: it involves
$partial_N h$, which is determined by $h$. We shall see in @sec:toys that this boundary condition is exactly where
the simplest candidates fail. It is therefore worth separating the two roles of $h$. The identity @eq:Q uses
the field $h nabla h$, for which $dv(h nabla h) - |nabla h|^2 - beta_m^2 h^2 = h(Delta h - beta_m^2 h)$; replacing $h nabla h$ by an
arbitrary field gives the following form of the stability inequality.

#lemma(name: [Stability in flux form])[
  Let $v$ be a smooth function and $Y$ a smooth vector field on $overline(Omega)$ with $N dot Y + H v^2 >= 0$ on
  $partial Omega$. Then
  $ integral_Omega dv Y <= integral_Omega (|nabla v|^2 + beta_m^2 v^2). $
] <lem:stab-flux>

#proof[
  By the divergence theorem (the outward normal is $-N$) and the boundary condition,
  $integral_Omega dv Y = -integral_(partial Omega) N dot Y <= integral_(partial Omega) H v^2$, and @eq:sph-stab bounds the right side.
]

Consequently a cone is unstable as soon as there are a function $h$ and a field $Z$ on $overline(Omega)$ with
$ dv Z >= |nabla h|^2 + beta_m^2 h^2 "in" Omega, wide N dot Z + H h^2 >= 0 "on" partial Omega, $ <eq:target>
the first inequality strict on a set of positive measure: apply @lem:stab-flux with $v = h$ and $Y = Z$. Now
the boundary flux $N dot Z$ is free. The difficulty is plain: one must produce such a pair $(h, Z)$ for an
_unknown_ cone, about which one knows only that it solves @eq:link and is nonflat. (In practice $h$ and $Z$
will be singular where $T$ vanishes, and @lem:stab-flux will be applied to cut-off versions; see
@sec:integration.)

= How to look for $h$: calibrations in jet space <sec:calibration>

Since the cone is unknown, $h$ and $Z$ cannot be written down by hand; they will have to be built by a
universal formula from the local behavior of the cone. To see why this is a reasonable hope, and what it
leads to, we first look at a one-dimensional example in which the same strategy proves a classical
inequality.

#example(name: [A Riccati proof of Wirtinger's inequality])[
  We prove $integral_0^L y'^2 >= mu integral_0^L y^2$ for $y(0) = y(L) = 0$ and $mu < (pi\/L)^2$. For a function
  $F(x, y)$, the derivative of $F(x, y(x))$ is $F_x + F_y thin y'$: it depends on the point $(x, y(x))$ and,
  linearly, on the value $eta = y'(x)$, about which the point says nothing. So if
  $ eta^2 - mu y^2 >= F_x (x, y) + F_y (x, y) thin eta quad "for all" (x, y, eta), $ <eq:star>
  and $F(x, 0) = 0$, integrating along $x |-> (x, y(x), y'(x))$ gives the inequality. The integrand is
  quadratic, so try $F = rho(x) y^2$. Then @eq:star reads
  $ (eta - rho y)^2 - (rho' + rho^2 + mu) y^2 >= 0 quad "for all" y, eta, $
  which holds if and only if $rho' + rho^2 + mu <= 0$: a Riccati inequality. For $mu = omega^2$ with
  $omega L < pi$, the function $rho = omega cot(omega(x + x_0))$, with small $x_0 > 0$, solves it with equality and is
  smooth on $[0, L]$.
] <ex:wirtinger>

In this example $(x, y)$ is the _base_: the data on which the unknown $F$ is allowed to depend. The
derivative $eta = y'$ is the _fiber_: it appears only after differentiating, it is not determined by the base,
so the pointwise inequality must hold for all of its values; and differentiation is linear in it. A
function on the base whose derivative along every jet bounds the integrand, for every value of the fiber,
is what we call a _calibration in jet space_.

The Bernoulli problem differs in direction. Wirtinger's inequality is a _stability_ statement, proved
for all $y$. For cones we want _instability_: $h$ and $Z$ are built from the jet of the cone itself, and
the pointwise inequality @eq:target, integrated along that one jet, makes the stability form negative. The
mechanism is the same: functions on a base whose derivatives are controlled for every value of the free
fiber.

Two further features of the example will recur.

_Linearity._ Condition @eq:star is linear in the unknown $F$. Finding a calibration is therefore a convex
problem, which is what will make a computer search possible (@sec:certificate).

_Threshold and obstruction._ For $mu > (pi\/L)^2$ no admissible $F$ exists, because integrating
@eq:star along $y_* = sin(pi x\/L)$ would give $integral (y_*'^2 - mu y_*^2) >= 0$, which is false. Actual
functions violating the inequality obstruct every calibration. In the Bernoulli problem the De Silva--Jerison
cone in $RR^7$ will play the role of $y_*$ (@sec:end).

To carry this out for cones we must decide what the base and the fiber are, and what shape $h$ and $Z$
should have. The next section makes these choices.

= The ansatz <sec:ansatz>

We now decide what $h$ is built from and what form it takes. Two principles guide the choices: the test
must see the nonflatness of the cone, and it must respect the scaling of the problem. Identities satisfied
by cones are not needed yet; they enter in @sec:toys, when a concrete choice is tested.

== Which quantity should $h$ be built from?

Suppose $h$ is given by a universal formula in the jet of the cone, and the pointwise inequalities
@eq:target hold, strictly, at every jet where $h != 0$. Apply this to the half-space solution, whose link is a
hemisphere with $T equiv 0$: if $h$ did not vanish at such jets, integration would show that the half-space
solution is unstable, which is absurd. So $h$ must vanish where $T = 0$, and the natural quantity to build it
from is the spherical Hessian $T$ of @sec:reduction and its size
$ w = |T|. $
This is the Bernoulli counterpart of Simons's use of the second fundamental form for minimal cones.

== Scaling, base and fiber

The inequalities @eq:target are homogeneous in $h$ and $Z$, and multiplying the cone by a constant
multiplies $T$ by the same constant. It is therefore natural to separate the size $w$ of the Hessian from
its shape
$ A = T \/ w, $
which is a unit symmetric trace-free matrix wherever $w > 0$ (trace-free because $tr T = Delta g + m g = 0$
by @eq:link). Besides $A$, the lower-order data available at a point are the values $p = nabla g$ and $g$. We take
these as the base and let $h$ be a power of $w$ times an unknown function of the base:
$ h = w^a sqrt(f(A, p, g)), wide a > 0, quad f > 0. $ <eq:h-ansatz>
The square root is there because the inequalities involve $h^2 = w^(2a) f$, which is then linear in the
unknown $f$; as in @ex:wirtinger, linearity in the unknowns keeps the search convex. The fiber consists of
what appears only after differentiating: the third derivatives of $g$ (that is, $nabla T$), and $w$ itself,
which has been scaled out of the base. The flux $Z$ will be chosen in the same spirit. Its simplest choice
is a multiple of $h nabla h$, as in @eq:Q, and the simplest instance of @eq:h-ansatz is $f = 1$. We try this
first.

= The simplest instance: plain powers <sec:toys>

The first case of the ansatz is $f = 1$, so $h = w^a$, the analogue of Simons's test function. Testing it
will tell us which properties of cones the method needs, and exactly where the dimension enters.

#question[Does $h = w^a$, with $Z$ a multiple of $h nabla h$, satisfy @eq:target?]

Fix $a > 0$ and $c > 0$ and set
$ h = w^a, wide Z = (c\/a) h nabla h = c w^(2a - 1) nabla w. $
For $c = a$ this is $Z = h nabla h$ and @eq:target is the subsolution property @eq:jacobi-sub. Since we need strict
inequality somewhere, and since $h^2 = w^(2a)$, the natural form of the requirement is
$ dv Z - |nabla h|^2 - beta_m^2 h^2 >= epsilon w^(2a) $ <eq:margin>
for some $epsilon > 0$. Computing $dv Z = c w^(2a-2) (w Delta w + (2a - 1)|nabla w|^2)$ requires $Delta w$: a second
derivative of $T$, that is, a fourth derivative of $g$. Before going further we need to know what the
equation says about it.

== What the equation says about $Delta T$

#proposition(name: [Bochner identity])[
  On $Omega$, $T$ is symmetric and trace-free, $nabla T$ is fully symmetric and trace-free, and
  $ Delta T = m T, wide Delta w^2 = 2 m w^2 + 2|nabla T|^2. $
] <prop:interior>

Trace-freeness is the equation $Delta g = -m g$. Full symmetry of $nabla T$ is the Codazzi property of $T$:
on the round sphere the curvature terms in $nabla_i nabla_j nabla_k g - nabla_j nabla_i nabla_k g$ cancel against the derivatives of
$g Id$. Then $Delta T_(j k) = nabla_i nabla_j T_(i k)$, and commuting $nabla_i$ past $nabla_j$ produces curvature terms of $S^m$
which combine with $tr T = 0$ to give $m T$. The second identity is the product rule,
$Delta |T|^2 = 2 ip(T, Delta T) + 2|nabla T|^2$; it is the Bernoulli analogue of Simons's identity.

Normalize the fiber as we did the base: where $w > 0$ put
$ X = nabla T \/ w in STF^3 (RR^m), wide q = nabla log w, quad "so that" q_l = X_(l j k) A_(j k), $
and $|nabla T|^2 = w^2 |X|^2$. Then $w Delta w = m w^2 + |nabla T|^2 - |nabla w|^2$ gives
$ w^(-2a) (dv Z - |nabla h|^2 - beta_m^2 h^2) = underbrace(m c - beta_m^2, "base only") + underbrace(c |X|^2 - ((2 - 2a) c + a^2) |q|^2, "quadratic in the fiber" X). $ <eq:plain-interior>
As in @ex:wirtinger, this must be at least $epsilon$ for all fiber values $X in STF^3$, since nothing we know
about cones restricts $nabla T$ beyond symmetry and trace-freeness. Bounding $|q|$ in terms of $|X|$ is an algebraic
form of the improved Kato inequality; on $RR^2$ one has exactly $|q|^2 = |X|^2 \/ 2$.

== What happens at the boundary

The boundary inequality involves $N dot Z + H h^2 = c w^(2a-1) partial_N w + H w^(2a)$, so we need to know $H$,
$partial_N w$, and that $w$ does not vanish there. The overdetermined conditions $g = 0$, $nabla g = N$ give this
through a maximum principle argument applied to $|nabla u|^2 = g^2 + |p|^2$.

#lemma(name: [Gradient bound and boundary signs])[
  On the link of a cone with an isolated singularity, $chi := 1 - g^2 - |p|^2 > 0$ in $Omega$, and on $partial Omega$
  one has $H = -T(N, N) > 0$, $N$ is an eigenvector of $T$, and $w > 0$. In particular the zero set of $w$ is a
  compact subset of $Omega$.
] <lem:signs>

Indeed $g^2 + |p|^2$ satisfies $Delta (g^2 + |p|^2) = 2 w^2 >= 0$ and $nabla (g^2 + |p|^2) = 2 T p$; it equals one on
$partial Omega$ and is not constant since $T equiv.not 0$. The strong maximum principle and Hopf's lemma give
$chi > 0$ inside and $2 T(N, N) = partial_N (g^2 + |p|^2) < 0$ on $partial Omega$, and tangential differentiation of
$g^2 + |p|^2 = 1$ gives $T(N, tau) = 0$ for tangent vectors $tau$.

Let $kappa = H\/w > 0$ be the _normalized mean curvature_; then $A N = -kappa N$. Differentiating $T(N, tau) = 0$
and the trace condition along $partial Omega$ shows that every component of $nabla T$ with an odd number of normal
slots is determined by $T$:
$ nabla_N T_(alpha beta) = -w^2 (kappa A + A^2)_(alpha beta), quad nabla_N T_(N N) = w^2, $ <eq:odd-jets>
for tangential $alpha, beta$, while the components with an even number of normal slots involve tangential
derivatives of the curvature of $partial Omega$ and are not determined. Since $T$ has no mixed normal-tangential
components, $partial_N w = T_(j k) nabla_N T_(j k) \/ w$ only involves the determined ones:
$ partial_N w = -w^2 (2 kappa + tr A^3). $ <eq:dNw>
Hence
$ w^(-2a-1) (N dot Z + H h^2) = kappa (1 - 2c) - c tr A^3. $ <eq:plain-boundary>
At the boundary no fiber is left: this depends only on the _boundary shape_ of $A$, that is, on $kappa > 0$ and
the $m - 1$ tangential eigenvalues $x_1, dots, x_(m-1)$, with $sum x_i = kappa$ and $sum x_i^2 + kappa^2 = 1$.
Nothing we know about cones excludes any such shape, so a universal formula must handle all of them.

== The window, dimension by dimension

#example(name: [Links in $S^2$: the window is open])[
  For $m = 2$, $beta_2^2 = 1\/4$ and a unit trace-free $2 times 2$ matrix has eigenvalues $plus.minus 1\/sqrt(2)$.
  Hence $tr A^3 = 0$, $kappa = 1\/sqrt(2)$, and @eq:plain-boundary equals $(1 - 2c)\/sqrt(2)$. The interior
  form @eq:plain-interior is $2c - 1\/4 + (a c - a^2\/2)|X|^2$, using $|q|^2 = |X|^2\/2$. So both inequalities hold,
  with a positive margin in the interior, whenever
  $ max{1/8, a/2} < c < 1/2. $
  This is nonempty for every $a < 1$. With $a = 29\/50$ and $c = 2\/5$ one gets precisely the
  certificate used to exclude nonflat cones in $RR^3$ (@sec:low).
] <ex:m2>

#example(name: [Links in $S^3$: the window closes])[
  For $m = 3$, $beta_3^2 = 1$. Taking $X = 0$ in @eq:plain-interior shows that a positive interior margin
  requires $c > 1\/3$. At the boundary, $kappa in (0, sqrt(2\/3)]$, and the tangential eigenvalues
  satisfy $x_1 + x_2 = kappa$ and $x_1 x_2 = kappa^2 - 1\/2$, so $tr A^3 = (3\/2) kappa (1 - 2 kappa^2)$ and
  $ kappa (1 - 2c) - c tr A^3 = kappa (1 - 7c\/2 + 3 c kappa^2). $
  For small $kappa$ this is negative unless $c <= 2\/7$. Since $2\/7 < 1\/3$, no choice of $a$ and $c$ works. The
  bad shapes have small $kappa$, that is, boundary mean curvature small compared with the Hessian, with
  principal curvatures close to $plus.minus w \/ sqrt(2)$.
] <ex:m3>

#example(name: [Links in $S^m$, $m >= 4$])[
  Now the interior needs $c > beta_m^2\/m = (m - 1)^2\/(4m)$, which is $9\/16$ for $m = 4$ and $4\/5$ for
  $m = 5$. The boundary fails for every $c > 0$: as $kappa -> 0$ the tangential eigenvalues can approach
  any unit trace-free configuration of $m - 1 >= 3$ numbers, for instance $(2, -1, -1, 0, dots)\/sqrt(6)$,
  for which $tr A^3 > 0$, and then @eq:plain-boundary tends to $-c tr A^3 < 0$.
] <ex:m4>

These examples are the concrete form of the incompatibility described by Jerison and Savin
@JerisonSavin2015[Section 3.2]: the interior wants a large coefficient to beat the Hardy constant, while
the boundary wants a small one, and their worst cases come from different Hessian shapes. The failure is
pointwise, at particular shapes, and at the boundary it is exactly the rigid link between $N dot Z$ and $h$
that @lem:stab-flux was designed to loosen.

= The general ansatz <sec:flux>

This section returns to the ansatz of @sec:ansatz and enriches it exactly where the plain power fails, and
then turns @eq:target into polynomial inequalities in finitely many variables.

#question[What extra freedom could repair the plain power?]

Two kinds. First, the weight $f$ in @eq:h-ansatz, which can be small on bad boundary shapes and large
elsewhere. Second, a flux $Z$ that is no longer a multiple of $nabla (h^2)$, so that $N dot Z$ decouples from
$partial_N h$ and can be adjusted on the bad shapes. (The certificate on $RR^3$ in @sec:low uses only the second
freedom: $f = 1$, with extra flux terms. This is where the real gain lies.)

== Letting the weight see $p$ and $g$

The interior and the boundary differ in the values of $(p, g)$: by @lem:signs, $chi > 0$ in $Omega$, while
$g = 0$ and $|p| = 1$ on $partial Omega$. A weight $f(A, p, g)$ can therefore behave differently at the boundary and in
the interior. The base is the compact set
$ cal(K)_m = {(A, p, g) : A in STF^2(RR^m), |A| = 1, chi = 1 - |p|^2 - g^2 >= 0}, $
and the gradient bound enters the algebra as the single constraint $chi >= 0$.

To differentiate functions on the base along the cone we use the chain rule and
$ nabla_l A_(i j) = X_(l i j) - q_l A_(i j), quad nabla_l p_i = w A_(l i) - g delta_(l i), quad nabla_l g = p_l, quad nabla_l w = w q_l, $ <eq:generator>
which follow from the definitions. For a function $phi(A, p, g)$, $nabla_l phi$ is thus a polynomial in the base and
fiber variables, linear in the fiber, exactly as $F_x + F_y eta$ was in @ex:wirtinger. From now on we treat $w$
and $X$ as free variables in this expression; $w$ enters only linearly, so forgetting that $w = |T|$ is a harmless
relaxation.

== The general flux

#question[What is the most general flux built from the jet that we can hope to control?]

$Z$ should have the same homogeneity as $h nabla h$, namely $w^(2a)$ times terms of degree at most one in the
fiber variables $X$ and $w$. So
$ Z_l = w^(2a) (Gamma_(l i j k) X_(i j k) + w M_l + P_l), $
with coefficients $Gamma$, $M$, $P$ depending on the base and equivariant under rotations. For the plain power,
$Gamma_(l i j k) = c delta_(l i) A_(j k)$ and $M = P = 0$. But $dv Z$ now contains $nabla X$, that is, all fourth
derivatives of $g$, and we must ask what the equation says about them.

A lower-order model shows what to expect. In the plane, let $u$ be harmonic, and consider a field $Y(u, nabla u)$
built from the one-jet. Then $dv Y = partial_u Y_i thin partial_i u + partial_(p_j) Y_i thin partial_i partial_j u$. The trace-free part of the
Hessian is not determined by the one-jet and enters linearly, so a lower bound independent of it requires
the symmetric part of $partial_p Y$ to be a multiple of the identity; the antisymmetric part of $partial_p Y$ pairs to zero
with the symmetric Hessian and is unrestricted.

For cones, at a point $nabla_l nabla_i T_(j k)$ is symmetric in $(i, j, k)$, and beyond that only two combinations are
determined: the trace in $(l, i)$, which is $Delta T = m T$ by @prop:interior, and the antisymmetric part in
$(l, i)$, which is the curvature of the sphere acting on $T$:
$ nabla_l nabla_i T_(j k) - nabla_i nabla_l T_(j k) = delta_(l j) T_(i k) + delta_(l k) T_(i j) - delta_(i j) T_(l k) - delta_(i k) T_(l j). $ <eq:commutator>
The remaining, symmetric trace-free, part is free and would enter $dv Z$ linearly; a term linear in a free
variable destroys any lower bound. So, as in the planar model, the coefficient $Gamma$ should see only the trace
and the antisymmetric part: after symmetrizing in $(i, j, k)$, which does not change $Gamma_(l i j k) X_(i j k)$, we may
take
$ Gamma_(l i j k) = delta_(l i) U_(j k) + C_(l i j k), wide C_(l i j k) = -C_(i l j k), $
with unknown tensors $U$ and $C$. Then
$ Z_l = w^(2a) (U_(j k) X_(l j k) + C_(l i j k) X_(i j k) + w M_l + P_l), $ <eq:ansatz>
and the fourth derivatives enter $dv Z$ only through
$ (U_(j k) nabla_l nabla_l T_(j k) + C_(l i j k) nabla_l nabla_i T_(j k)) \/ w = m U_(j k) A_(j k) + C_(l i j k)(delta_(l j) A_(i k) + delta_(l k) A_(i j)), $ <eq:fourth>
using $Delta T = m T$ and, since $C$ is antisymmetric, $C_(l i j k) nabla_l nabla_i T_(j k) = (1\/2) C_(l i j k)(nabla_l nabla_i - nabla_i nabla_l) T_(j k)$.

The boundary raises the same question one order lower. There $N dot Z$ contains $p_l U_(j k) X_(l j k) + p_l C_(l i j k)
X_(i j k)$, and the even-normal components of $nabla T$ are undetermined by @eq:odd-jets. If $U$ and $C$ are even
functions of $p$, then at a boundary point the three-tensor $p_l Gamma_(l i j k)$ is odd under the reflection in $p^perp$,
which fixes $A$ (as $p$ is an eigenvector) and reverses $p$. A tensor odd under this reflection has no
components with an even number of normal slots, so the undetermined part drops out. Finally, $p dot P$ would
contribute to $N dot Z$ at order $w^(2a)$, below the order $w^(2a+1)$ of every other boundary term; to keep the
boundary inequality homogeneous in $w$ we require $P = 0$ when $g = 0$. To summarize: the unknowns are
$f, U, C, M, P$, functions on the base, equivariant under rotations, with $U$ and $C$ even in $p$, $C$
antisymmetric in its first two slots, and $P = 0$ at $g = 0$.

== From the target inequalities to two polynomials

#question[How do we turn @eq:target for this ansatz into something checkable?]

_The divergence._ By @eq:generator, $nabla_l w^(2a) = 2a w^(2a) q_l$ and $nabla_l X_(i j k) = nabla_l nabla_i T_(j k) \/ w - q_l
X_(i j k)$. Applying the product rule to @eq:ansatz and using @eq:fourth,
$ w^(-2a) dv Z = & m U_(j k) A_(j k) + C_(l i j k)(delta_(l j) A_(i k) + delta_(l k) A_(i j)) + (nabla_l U_(j k) + (2a - 1) q_l U_(j k)) X_(l j k) \
  & + (nabla_l C_(l i j k) + (2a - 1) q_l C_(l i j k)) X_(i j k) + w (nabla_l M_l + (2a + 1) q_l M_l) + nabla_l P_l + 2a q_l P_l, $
where $nabla_l$ of a coefficient is computed by the chain rule from @eq:generator. This is a polynomial in the base and
fiber variables.

_The test function._ $|nabla h|^2 = h^2 |nabla log h|^2$ is rational in $f$, since $nabla log h = a q + nabla f \/ (2f)$. A free
vector $ell$ linearizes it, exactly as the square $(eta - rho y)^2$ did in @ex:wirtinger: for every $ell$,
$ f |ell|^2 - 2 f ell dot nabla log h = f |ell - nabla log h|^2 - f |nabla log h|^2, $
with equality at $ell = nabla log h$, and $2 f nabla log h = nabla f + 2a q f$.

_The margin._ As in @eq:margin we ask for $epsilon w^(2a)$, the natural size of $h^2 = w^(2a) f$. The margin is needed
twice: for the contradiction, and to absorb the errors of the cutoffs in @sec:integration.

Before stating the result, here are all the variables that occur, with the only information about the cone
that will be used.

#align(center, {
  set text(size: 9.5pt)
  table(
    columns: (auto, auto, auto),
    align: (center, left, left),
    stroke: none,
    inset: (x: 7pt, y: 4pt),
    table.hline(stroke: 0.8pt),
    table.header([*variable*], [*geometric value*], [*constraint used*]),
    table.hline(stroke: 0.5pt),
    [$A$], [$T \/ w$], [$A in STF^2 (RR^m)$, $|A| = 1$],
    [$p, g$], [$nabla g$, $g$], [$chi = 1 - |p|^2 - g^2 >= 0$],
    [$X$], [$nabla T \/ w$], [$X in STF^3 (RR^m)$, otherwise free],
    [$w$], [$|T|$], [free],
    [$ell$], [$nabla log h$], [free],
    [$q$], [$nabla log w$], [derived: $q_l = X_(l j k) A_(j k)$],
    table.hline(stroke: 0.8pt),
  )
})

#definition(name: [Interior and boundary polynomials])[
  The _interior polynomial_ $cal(I)_m$ is the right side of the formula for $w^(-2a) dv Z$ above, minus
  $beta_m^2 f$, plus $f |ell|^2 - (nabla_l f + 2a q_l f) ell_l$. The _boundary polynomial_ is
  $ cal(B)_m = kappa f + p_l U_(j k) V_(l j k) + p_l C_(l i j k) V_(i j k) + p_l M_l, $
  evaluated at $g = 0$, $|p| = 1$, $A p = -kappa p$, where $V$ is the three-tensor whose components with an odd number
  of slots equal to $p$ are those of $nabla T \/ w^2$ given by @eq:odd-jets, and whose other components vanish.
] <def:polys>

By construction one has the exact identities
$ cal(I)_m = w^(-2a) (dv Z - beta_m^2 h^2 - |nabla h|^2) + f |ell - nabla log h|^2, \ N dot Z + H h^2 = w^(2a + 1) cal(B)_m . $ <eq:identities>
For the plain power, $cal(I)_m$ minimized over $ell$ is @eq:plain-interior, and $cal(B)_m$ is @eq:plain-boundary.

== The certificate

#question[What exactly must the coefficients satisfy?]

By @eq:identities, it suffices that $cal(I)_m >= epsilon$ and $cal(B)_m >= 0$ for every value of the variables that a cone could
produce. Since we cannot say more about these values than the table does, we ask for this on the whole
table.

#definition(name: [Certificate on $RR^m$])[
  Fix $a in (1\/2, 1)$. A _certificate on_ $RR^m$ consists of smooth (in practice polynomial) maps
  $f, U, C, M, P$ on the base with the symmetries above and $f > 0$, and a constant $epsilon > 0$, such that
  + $cal(I)_m >= epsilon (1 + |ell|^2)$ for all $(A, p, g) in cal(K)_m$, all $X in STF^3(RR^m)$, all $w in RR$ and $ell in RR^m$;
  + $cal(B)_m >= 0$ for all unit trace-free $A$ and unit $p$ with $A p = -kappa p$, $kappa > 0$.
] <def:cert>

The range of $a$ is explained later: $a > 1\/2$ makes $h$ have finite energy near zeros of $w$
(@sec:integration), and $a < 1$ is used for the suspension (@sec:suspension). A certificate yields, wherever
$w > 0$, $dv Z >= |nabla h|^2 + beta_m^2 h^2 + epsilon w^(2a)$ in $Omega$ (take $ell = nabla log h$) and $N dot Z + H h^2 >= 0$ on $partial Omega$,
which is @eq:target with a margin. The definition no longer mentions any cone: it is a statement about
polynomials on a compact set of tensors.

#theorem(name: [Certificates])[
  With $a = 29\/50$, certificates exist on $RR^2$, on $RR^3$ and on $RR^5$.
] <thm:certs>

The certificate on $RR^5$ is the main contribution of @OpenAI2026; those on $RR^2$ and $RR^3$ are much
smaller and are described in @sec:low. The following table recapitulates the analogy with
@ex:wirtinger.

#figure(
  {
    set text(size: 9.5pt)
    table(
      columns: (auto, auto),
      align: (left, left),
      stroke: none,
      inset: (x: 6pt, y: 4pt),
      table.hline(stroke: 0.8pt),
      table.header([*Riccati toy model*], [*Bernoulli cones*]),
      table.hline(stroke: 0.5pt),
      [base $(x, y)$], [normalized two-jet $(A, p, g)$],
      [fiber $eta = y'$, free], [$X = nabla T\/w$ and $w$ (free), auxiliary $ell$],
      [unknown $F = rho(x) y^2$], [unknown coefficients $f, U, C, M, P$],
      [derivative $F_x + F_y eta$], [chain rule with @eq:generator],
      [@eq:star for every $eta$], [$cal(I)_m >= epsilon(1 + |ell|^2)$ for every $(w, ell, X)$],
      [completing the square in $eta$], [completing the square in $ell$],
      [boundary term $F(L, 0) - F(0, 0)$], [$cal(B)_m >= 0$ on boundary shapes],
      [threshold $omega = pi \/ L$], [link dimension five versus six],
      [obstruction $sin(pi x\/L)$], [the De Silva--Jerison cone in $RR^7$],
      table.hline(stroke: 0.8pt),
    )
  },
  caption: [A dictionary between the toy calibration and the Bernoulli certificate.],
) <fig:dictionary>

= Finding and verifying a certificate <sec:certificate>

This section explains why the existence of a certificate is a question that a computer can settle, how
one searches for one, and what the certificate on $RR^5$ looks like. It can be skipped on a first reading:
the rest of the argument uses only @def:cert.

#question[Why should a finite computation suffice, and why is exact arithmetic the natural tool?]

Everything in @def:cert is algebraic. The base $cal(K)_m$ is compact, and the unknowns $f, U, C, M, P$ enter
_linearly_: $cal(I)_m$ is linear in them and their derivatives, and $cal(B)_m$ in their values. One more step puts the
interior condition in a standard form. $cal(I)_m$ has terms of degree zero, one and two in the fiber variables
$(w, ell, X)$. Introducing an auxiliary variable $z$ and multiplying each term by the power of $z$ that brings its
degree to two turns $cal(I)_m$ into a quadratic form in $(w, z, ell, X)$ whose coefficients are polynomials on the
base, and by scaling, condition (1) is equivalent to this form being at least $epsilon(z^2 + |ell|^2)$. So, as in the
Riccati example, the existence of a certificate is a convex feasibility problem: find coefficients such
that a family of quadratic forms, parametrized by a compact semialgebraic set, is uniformly positive in the
relevant directions. Two consequences shape the proof.

First, the problem can be attacked by semidefinite programming. Choose a finite basis of equivariant
polynomial coefficients (contractions of $A$, $p$, $g$ and the identity), and look for nonnegativity proofs in
the form of sums of squares: Gram matrices that exhibit the quadratic form, up to a controlled remainder, as a
sum of squares of polynomials, possibly multiplied by the nonnegative function $chi$ that encodes the gradient
bound @Parrilo2003. The unknown coefficients and the Gram matrices enter linearly, so both can be searched for
at once. This is how certificates of this kind are found numerically.

Second, a numerical solution is not a proof, but a strict one is robust. Because the desired inequalities
have a positive margin, one can round the numerical output to rational numbers, write the inequality as an
_exact_ identity: the quadratic form equals a sum of manifestly nonnegative Gram terms, plus reserved
positive multiples of $w^2, z^2, |ell|^2, |X|^2$, minus a remainder with small rational coefficients. The
remainder is then bounded crudely, term by term, using only elementary inequalities valid on the compact
base. All the arithmetic is with integers and rationals, and the result is a finite list of checks.

== The certificate on $RR^5$

Having seen why a certificate is a finite object, one may ask what the one on $RR^5$ actually consists of. We
describe its structure without its numbers; each ingredient corresponds to one of the steps just outlined.

_The ansatz._ The coefficients $f, U, C, M, P$ are rational linear combinations of a few hundred tensor
monomials in $A$, $p$, $g$ and $tr A^3$: contracted products of powers of $A$ and copies of $p$. Equivariance is
automatic for such contractions, and parity in $p$ is visible from the number of copies of $p$.

_The interior._ The nonnegative part consists of blocks, each a sum of squared norms of tensors that are
linear in the fiber, possibly after projecting onto the antisymmetric, the symmetric trace-free, or a mixed
symmetry type, and possibly weighted by $chi$. After subtracting these blocks and the reserved diagonal terms,
the remainder is a sum of scalar contractions of degree two in the fiber. Each is bounded by elementary
estimates on the base, such as $norm(A)_"op"^2 <= 4\/5$, $|tr A^3| <= 3\/sqrt(20)$, and the improved Kato bound
$|q|^2 <= (5\/7)|X|^2$, and a weighted Young inequality shows that the reserved terms absorb the total with
room to spare. (The bound on $tr A^3$ has a one-line proof: with $c_* = sqrt(4\/5)$ bounding the eigenvalues
$alpha_i$, one has $sum_i (alpha_i - c_*) (alpha_i + 1\/(5 c_*))^2 <= 0$, which expands to $tr A^3 <= c_* - 1\/(5 c_*) = 3\/sqrt(20)$.)

_The boundary._ By equivariance one may take $p$ to be the last basis vector and $A$ diagonal, with
tangential eigenvalues $x_1, dots, x_4$. Then $cal(B)_5$ becomes a symmetric polynomial in $x_1, dots, x_4$ on the set
$sum x_i^2 + (sum x_i)^2 = 1$, $sum x_i = kappa > 0$. It is written as a sum of squares, one block weighted by
$kappa$, plus a positive constant, minus a remainder whose finitely many coefficients are summed in absolute
value. This gives $cal(B)_5$ bounded below by an explicit positive rational.

#remark(name: [What the certificate proves])[
  The certificate is stronger than what the geometry needs: $w$ is treated as a free real variable rather
  than $|T|$, $X$ as an arbitrary trace-free tensor unrelated to the base, and only $chi >= 0$ is used of the
  strict gradient bound. This is what makes it a finite statement.
]

= From pointwise to global: Hessian zeros <sec:integration>

A certificate gives the pointwise inequalities only where $w > 0$: the fields $h$ and $Z$ are built from
$A = T\/w$ and $X = nabla T\/w$, and are singular where the Hessian vanishes. To apply @lem:stab-flux we must
integrate across this zero set, about which nothing is known. This section shows that it is invisible to
the energy. The argument multiplies by cutoffs and shows that the errors vanish in the limit.

== The weighted Bochner estimate

#question[Why must the exponent $a$ be larger than $1/2$?]

Near a zero of $w$ the test function $h approx w^a$ has $|nabla h|^2 approx a^2 w^(2a-2) |nabla w|^2 <= a^2
w^(2a - 2) |nabla T|^2$. So $h$ has finite energy, and the cutoff errors are integrable, if $w^(2a-2)|nabla T|^2$ is
integrable. Nothing is known about the zero set of $w$ (its size, regularity or dimension), but the Bochner
identity of @prop:interior, together with $|nabla w^2|^2 <= 4 w^2 |nabla T|^2$, gives exactly this integrability when
$a > 1\/2$.

#lemma(name: [Weighted Bochner estimate])[
  Let $Omega$ be the link of a cone with an isolated singularity and $1\/2 < a <= 1$. Then
  $integral_(Omega inter {w > 0}) w^(2a - 2) |nabla T|^2 < oo$.
] <lem:bochner>

#proof[
  Put $W = w^2 + gamma$ with $gamma > 0$, which is smooth. Since $Delta W >= 2|nabla T|^2$ and $|nabla W|^2 <= 4 w^2
  |nabla T|^2 <= 4 W |nabla T|^2$,
  $ Delta (W^a) = a W^(a-1) Delta W - a(1-a) W^(a-2) |nabla W|^2 >= a (4a - 2) W^(a-1) |nabla T|^2. $
  Multiply by a cutoff $zeta$ that equals one near the zero set of $w$ (which is compact in $Omega$ by
  @lem:signs) and integrate by parts twice: $a(4a - 2) integral zeta W^(a-1) |nabla T|^2 <= integral |Delta zeta| W^a$, uniformly in
  $gamma$. Let $gamma -> 0$; away from the zero set the integrand is bounded.
]

== Cutoffs and the contradiction

With integrability in hand, we can run the argument of @lem:stab-flux on the region where $w > 0$, cutting off
near the zero set and checking that nothing is lost in the limit. Let $theta.alt$ be a smooth profile with
$theta.alt = 0$ on $[0, 1]$ and $theta.alt = 1$ on $[2, oo)$, and take $xi_j = theta.alt(j w)$, which vanishes near the zero set of
$w$. Apply @lem:stab-flux to $v = xi_j h$ and $Y = xi_j^2 Z$, whose boundary flux satisfies
$N dot (xi_j^2 Z) + H (xi_j h)^2 = xi_j^2(N dot Z + H h^2) >= 0$. After expanding $|nabla(xi_j h)|^2$ and $dv(xi_j^2 Z)$, the
terms $dv Z - |nabla h|^2 - beta_m^2 h^2$ appear multiplied by $xi_j^2$, and the interior inequality gives
$ epsilon integral_Omega xi_j^2 w^(2a) <= integral_Omega (h^2 |nabla xi_j|^2 + 2 xi_j h nabla h dot nabla xi_j - 2 xi_j Z dot nabla xi_j). $ <eq:errors>

Since $|nabla w| <= |nabla T|$, one has $|nabla xi_j| <= C |nabla T|\/w$ on the transition region, and the bounds $|h| <= C w^a$,
$|nabla h| + |Z| w^(-a) <= C w^a (1 + w + |nabla T|\/w)$, which follow from the compactness of the base, show that
every error is dominated by $C w^(2a)(1 + |nabla T|\/w)^2$, integrable by @lem:bochner. Each error vanishes
pointwise for large $j$, so the right side of @eq:errors tends to zero by dominated convergence, while the
left side tends to $epsilon integral_Omega w^(2a) > 0$ because $T equiv.not 0$. This is a contradiction.

#theorem(name: [Exclusion from a certificate])[
  Let $n >= 3$. If a certificate on $RR^(n-1)$ exists, there is no nonflat minimizing cone with an
  isolated singularity in $RR^n$.
] <thm:exclusion>

This step uses only $a > 1\/2$; the upper bound $a < 1$ enters in @sec:suspension.

= Low dimensions <sec:low>

@thm:exclusion reduces the classification in a given dimension to the construction of a certificate. In
low dimensions the certificates are small enough to describe completely, and they show the method at work.
Each step of the induction uses @prop:reduction and an exclusion of cones with an isolated singularity.

_Dimension one._ A one-homogeneous function on $RR$ is $b_1 x_+ + b_2 (-x)_+$. If both slopes are positive,
adding a small bump at the origin lowers the energy at first order, since the positive set does not change
while the Dirichlet energy decreases. So $u = b x_+$, and comparing with the translates
$b (x - t)_+ \/ (1 - t)$ on $(-1, 1)$, whose energy $b^2 \/ (1 - t) + (1 - t)$ must be minimal at $t = 0$, forces
$b = 1$.

_Dimension two._ The link lies in $S^1$, so $T$ is a trace-free $1 times 1$ matrix and vanishes. A cone with an
isolated singularity in $RR^2$ would have $nabla^2 u equiv 0$ on $D$, which @def:cone excludes.

_Dimension three._ The certificate on $RR^2$ is the plain power of @ex:m2: $f = 1$, $U = (2\/5) A$, $C = M = P =
0$, with $a = 29\/50$. Its verification is a completed square. Since $|X|^2 = 2 |q|^2$ for trace-free tensors on
$RR^2$,
$ cal(I)_2 - 1/10 (1 + |ell|^2) = 9/20 + 9/10 |ell - 29/45 q|^2 + 203/2250 |q|^2 >= 0, $
and $cal(B)_2 = kappa\/5 = sqrt(2)\/10$. With @thm:exclusion this excludes nonflat cones in $RR^3$, recovering the
theorem of Caffarelli, Jerison and Kenig @CaffarelliJerisonKenig2004.

_Dimension four._ By @ex:m3 the plain power fails on $RR^3$, so the certificate must use the extra freedom.
A small one suffices, and it uses only the flux: $f = 1$ and $C = P = 0$, with $U$ a combination of five
equivariant terms ($p times.o p$, $p times.o A p$, $A p times.o A p$, $A$ and $A^2$; the coefficient of $A$ depends on $p dot A p$ and
$|p|^2$, that of $A^2$ on $|p|^2$) and $M$ a combination of $p$ and $A p$. The flux is no longer a multiple of
$nabla (h^2)$: the terms in $p$ and the vector $M$ give the boundary flux the flexibility that the bad shapes of
@ex:m3 require. Both inequalities reduce, by equivariance, to diagonal $A$. At the boundary the polynomial
becomes a quartic in $kappa$ on $(0, sqrt(2\/3)]$, bounded below by an explicit Positivstellensatz identity. In the
interior one obtains a quadratic form in twelve fiber coordinates (the seven independent entries of $X$,
and $w$, $z$, $ell$) with coefficients polynomial in six base coordinates; it is bounded below by a
sum-of-squares identity with multipliers $1$ and $chi$, the constraint $|A| = 1$ entering through a polynomial
multiple, and a small residual absorbed by a reserved multiple of the fiber norm. With @thm:exclusion this
excludes nonflat cones in $RR^4$, recovering in this setting the theorem of Jerison and Savin
@JerisonSavin2015.

= Dimension five: the suspension <sec:suspension>

@thm:exclusion with the certificate on $RR^5$ excludes cones in $RR^6$. For cones in $RR^5$ one would need a
certificate on $RR^4$, which has not been constructed. This section explains the device that avoids it: a
cone in $RR^5$ is turned into a cone in $RR^6$, at the price of two singular points on the link, which must
then be removed in the integration.

== The suspended cone

#lemma(name: [Products])[
  If $u_1$ is a global minimizer on $RR^(n-1)$, then $(x', x_n) |-> u_1(x')$ is a global minimizer on $RR^n$.
] <lem:products2>

#proof(title: [Idea])[
  Slice a competitor on a ball of $RR^n$ by the hyperplanes ${x_n = "const"}$; almost every slice is an
  admissible competitor for $u_1$, and the term $|partial_(x_n) V|^2$ only adds energy.
]

Let $(u_o, D_o)$ be a nonflat minimizing cone with an isolated singularity in $RR^5$, with link $Omega_o subset S^4$,
restriction $g_o$ and Hessian norm $w_o$. By @lem:products2, $tilde(u)(x', x_6) = u_o (x')$ is a minimizing cone in
$RR^6$. Its singular set is the axis ${0} times RR$, which meets $S^5$ in two points, the _tips_. In coordinates
$(t, y) |-> (sin t thin y, cos t)$, $0 < t < pi$, $y in Omega_o$, the link of $D_o times RR$ is
$ Omega = {(sin t thin y, cos t) : y in Omega_o}, quad tilde(g) = sin t thin g_o (y), $
with the metric $dif t^2$ plus $sin^2 t$ times the round metric of $S^4$.
It is smooth away from the two tips, and all the local facts of @sec:toys and @sec:flux hold there with $m = 5$.
The stability inequality @eq:sph-stab holds for tests supported away from the tips, with $beta_5^2 = 4$. The
gradient bound and boundary signs carry over from $Omega_o$: $tilde(g)^2 + |nabla tilde(g)|^2 = g_o^2 + |nabla g_o|^2$,
$tilde(w) = w_o \/ sin t$ and $tilde(H) = H_o \/ sin t$. So a certificate on $RR^5$ gives the pointwise inequalities on the
suspended link wherever $tilde(w) > 0$, that is, away from the tips and the suspended zero set of $w_o$.

== Why the tips cost nothing

Use the product cutoff $xi_j = theta.alt(j w_o (y)) theta.alt(j sin t)$, which vanishes near the zero set of $w_o$ and near both
tips. On the suspension, $tilde(w) = w_o \/ sin t$, $|nabla xi_j| lt.tilde (1 + |nabla T_o|\/w_o) \/ sin t$, and the volume
element is $sin^4 t dif t dif V_o$. Each error in @eq:errors is therefore bounded by a constant times
$ (sin t)^(4 - 2 - 2a) thin w_o^(2a) (1 + |nabla T_o|\/w_o)^2, $
and the exponent $2 - 2a$ is positive because $a < 1$. The tips have codimension five in the link, and the
weight $tilde(w)^(2a) tilde (sin t)^(-2a)$ is far too mild to see them. The weighted Bochner estimate on $Omega_o$ makes
the $y$-integral finite, the same dominated convergence argument applies, and the left side of @eq:errors
converges to $epsilon integral_0^pi (sin t)^(4 - 2a) dif t thin integral_(Omega_o) w_o^(2a) > 0$.

#theorem(name: [Exclusion in dimension five])[
  If a certificate on $RR^5$ exists, there is no nonflat minimizing cone with an isolated singularity in
  $RR^5$.
] <thm:exclusion5>

= Proof of the main theorem and consequences <sec:assembly>

We can now assemble the induction. Write $"Flat"(n)$ for the statement that every nonzero minimizing cone in
$RR^n$ is flat. By @prop:reduction, $"Flat"(n - 1)$ together with the nonexistence of nonflat minimizing cones
with an isolated singularity in $RR^n$ implies $"Flat"(n)$. Hence
$ "Flat"(1) ==>^(S^1) "Flat"(2) ==>^(RR^2) "Flat"(3) ==>^(RR^3) "Flat"(4) ==>^(RR^5, "suspension") "Flat"(5) ==>^(RR^5) "Flat"(6), $
where the label indicates the trace-free $1 times 1$ argument or the certificate used in @thm:exclusion
(@thm:exclusion5 for the step to $"Flat"(5)$). This proves the first sentence of @thm:main; the second is
@DeSilvaJerison2009.

_The singular set._ @cor:sing follows from Weiss's dimension reduction @Weiss1999 (see
@Velichkov2023[Theorem 1.4 and Chapter 10]): blowups at singular points are nonflat minimizing cones,
blowups of those away from the origin split off lines, and the absence of nonflat cones below dimension seven
gives $Sing(u) = emptyset$ for $n <= 6$, local finiteness for $n = 7$, and $dim_cal(H) Sing(u) <= n - 7$ in
general. For sharpness, let $U$ be the De Silva--Jerison cone and consider $(x, y) |-> U(x)$ on $RR^7 times RR^(n-7)$. By
@lem:products2 it is a minimizer, every point of ${0} times RR^(n-7)$ is singular since every rescaling there is
the function itself, and this set has dimension $n - 7$.

= Where the dimension enters <sec:end>

The proof shows that dimension seven is sharp not only for the problem but for the method, within the class
of certificates of @def:cert (any coefficients, any exponent $a in (1\/2, 1)$). A certificate on $RR^6$ would, by
@thm:exclusion with $n = 7$, exclude all nonflat minimizing cones with an isolated singularity in $RR^7$. Since
all cones in $RR^6$ are flat, every minimizing cone in $RR^7$, in particular the cone of De Silva and Jerison,
has an isolated singularity (@prop:reduction). Hence no certificate on $RR^6$ exists: for every choice of
coefficients, the interior or the boundary inequality fails somewhere on the finite-dimensional space of
jets. This is the analogue of the obstruction $sin(pi x\/L)$ in @ex:wirtinger.

Where exactly the dimension enters is visible in the structure of the inequalities. The interior polynomial
contains $m U_(j k) A_(j k)$, from $Delta T = m T$, against $beta_m^2 f = ((m-1)\/2)^2 f$ from the Hardy inequality: a
term linear in $m$ against one quadratic in $m$. The improved Kato constant, $m\/(m+2)$ in general, deteriorates
with $m$. And the set of boundary shapes grows, admitting from $m = 4$ on configurations with $kappa$ near $0$ and
$tr A^3 > 0$ on which plain powers fail. The examples of @sec:toys show the window closing for the simplest
ansatz already at $m = 3$. The certificates show that a richer ansatz reopens it at $m = 2$, $3$ and $5$ ($m = 4$
being bypassed by the suspension), and the De Silva--Jerison cone shows that nothing reopens it at $m = 6$.

#v(1em)
#bibliography("refs.bib", title: [References], style: "springer-mathphys")
