//**** init-ting
#import "@preview/physica:0.9.7": *
#import "chpt-temp.typ": *

#show: thmrules.with(qed-symbol: $square$)
#show: chpt-note.with()

= Coupling to gravity
We recall the Lagrangian for a real scalar field
$
  cal(L) = 1/2 eta^(mu nu) phi.alt_(, mu) phi.alt_(, nu) - V(phi.alt)
$
this is Poincaré-invariant. To make this guys generally covariant we replace
$
     eta_(mu nu) & -> g_(mu nu) \
  phi.alt_(, mu) & -> phi.alt_(; mu) \
        dd(x, 4) & -> sqrt(-g) dd(x, 4)
$
so we find the generally covariant action
$
  S = integral dd(x, 4) sqrt(-g) [1/2 g^(mu nu) phi.alt_(, mu) phi.alt_(, nu) - V(phi.alt)]
$
this is called _minimal coupling_ to gravity.

We could also write
$
  S = integral dd(x, 4) sqrt(-g) [1/2 g^(mu nu) phi.alt_(, mu) phi.alt_(, nu) - V(phi.alt) - underbracket(xi/2 R phi.alt^2, tilde "mass")]
$
this is called _conformal coupling_. Taking $xi = 1\/6$ this action is invariant under conformal transformations
$
  g_(mu nu) -> tilde(g)_(mu nu) = Omega^2 (x) g_(mu nu)
$
where $Omega^2 (x)$ is an arbitrary non-vanishing function of spacetime. A metric is _conformally flat_ if $g_(mu nu) = Omega^2 (x) eta_(mu nu)$. These spacetimes can be mapped to Minkowski spacetime by a conformal transformation. So if a field theory is conformally invariant the action would reduce to that of a field in Minkwoski spacetime! A conformal field in a conformally flat spacetime is essentially decoupled from gravity.

The equation of motion is easily found
$
  (sqrt(-g) g^(alpha beta) phi.alt_(, beta))_(, alpha) + pdv(V, phi.alt) + xi R phi.alt sqrt(-g) = 0
$
in the minimally coupled case $xi = 0$.
