//**** init-ting
#import "@preview/physica:0.9.7": *
#import "chpt-temp.typ": *
#import "@preview/wicked:0.1.1": *

#show: thmrules.with(qed-symbol: $square$)
#show: chpt-note.with()


#let feyn(body) = math.cancel(angle: 15deg, body)

= Interacting fields
== Perturbation theory
To describe reality we need to include interactions between particles. This is done by including non-linear terms in the Lagrangian. We allow interactions at the same spacetime point meaning interactions of the form
$
  H_"int" = integral dd(x, 3) cal(H)_"int" [phi.alt (x)] = - integral dd(x, 3) cal(L)_"int" [phi.alt(x)]
$
we consider $cal(H)_"int"$ with terms only depending on the fields.

We will consider two types of interacting field theories. The first is the _phi-fourth_ theory. This is the simplest interacting field theory with Lagrangian
$
  cal(L) = 1/2 partial_mu phi.alt partial^mu phi.alt - 1/2 m^2 phi.alt^2 - lambda/4! phi.alt^4
$
where $lambda$ is some coupling. The second is the Yukawa theory with Lagrangian
$
  cal(L)_"Yukawa" = cal(L)_"Dirac" + cal(L)_"Klein-Gordon" - g overline(psi) psi phi.alt
$
this can be treated as a simple version of quantum electrodynamics where
$
  cal(L)_"QED" & = cal(L)_"Dirac" + cal(L)_"Maxwell" + cal(L)_"int" \
               & = overline(psi) (i feyn(D) - m) psi - 1/4 F_(mu nu) F^(mu nu)
$
with
$
  D_mu equiv partial_mu + i e A_mu (x)
$
being the gauge covariant derivative. The equations of motion are
$
   (i feyn(D) - m) psi & = 0 \
  partial_mu F^(mu nu) & = e overline(psi) gamma^nu psi = e j^nu
$
the first is the minimally coupled Dirac equation where we take $partial -> D$, and the second are the inhomogeneous Maxwell equations with current density $j^nu$. We consider quantum electrodynamics after discussing path integrals.

We can consider which interactions are allowed if we want our theory to be renormalizable. We claim that a coupling can not have negative mass dimension. This greatly limits our possible interactions. For a scalar field $phi.alt$ this means we have two possible interactions
$
  mu phi.alt^3 " and " lambda phi.alt^4
$
with $[mu] = 1$ and $[lambda] = 0$ since $[cal(L)] =^! 4$. For spinor fields the only allowed term is the Yukawa coupling
$
  g overline(psi) psi phi.alt
$
since $[psi] = 3\/2$. With vector fields $A_mu$ many more terms become possible.

So we in principle just need to measure the couplings and masses of all particles and then we are done. But with these we would still need to solve a quantum field theory to make measureable predictions. As expected this is much easier said than done. We instead attempt a perturbative approach.

== Correlation functions
Consider the two-point correlation function
$
  braket(Omega, T phi.alt(x) phi.alt(y), Omega)
$
we want to compute this in $phi.alt^4$ theory. We introduce $ket(Omega)$ as the ground state of the interacting theory, which is typically different from $ket(0)$ being the ground state of the free theory. We already computed this guy in the free theory
$
  braket(0, T phi.alt (x) phi.alt (y), 0)_"free" &= D_F (x-y) \
  &= integral dd(p, 4)/(2 pi)^4 (i e^(-i p dot (x-y)))/(p^2-m^2 + i epsilon)
$
we want to see how this changes for the interacting theory.

We write
$
  H & = H_0 + H_"int" \
    & = H_"Klein-Gordon" + lambda/4! integral dd(x, 3) phi.alt^4 (bold(x))
$
$H_"int"$ appears in both $ket(Omega)$ and $phi.alt (x)$ through
$
  phi.alt(x) = e^(i H t) phi.alt (bold(x)) e^(-i H t)
$
we want to express both in terms of the free fields and $ket(0)$.

We write
$
  phi.alt (t, bold(x)) = e^(i H (t-t_0)) phi.alt (t_0, bold(x)) e^(-i H (t-t_0))
$
for $lambda = 0$ we have $H = H_0$ and
$
  phi.alt_I (t, bold(x)) equiv e^(i H_0 (t-t_0)) phi.alt (t_0,bold(x)) e^(-i H_0 (t-t_0))
$
this is the _interaction picture_ field. We already have an expansion for this guy
$
  phi.alt_I (t,bold(x)) = integral dd(p, 3)/(2 pi)^3 1/sqrt(2 E_bold(p)) evaluated((a_bold(p) e^(-i p dot x) + a_bold(p)^dagger e^(i p dot x)))_(x^0 = t-t_0)
$
Then we can write
$
  phi.alt (t,bold(x)) &= e^(i H (t-t_0)) e^(-i H_0 (t-t_0)) phi.alt_I (t,bold(x)) e^(i H_0 (t-t_0)) e^(-i H (t-t_0)) \
  &equiv U^dagger (t,t_0) phi.alt_I (t,bold(x)) U(t,t_0)
$
where we define
$
  U(t,t_0) equiv e^(i H_0 (t-t_0)) e^(-i H (t-t_0))
$
which is the time-evolution operator.

We want an expression for $U(t,t_0)$. We have $U(t_0,t_0) = 1$ and
$
  i pdv(, t) U(t,t_0) = H_I (t) U(t,t_0)
$
with
$
  H_I (t) = e^(i H_0 (t-t_0)) H_"int" e^(-i H_0 (t-t_0)) = lambda/4! integral dd(x, 3) phi.alt_I^4
$
the solution is the familiar Dyson series
$
  U(t,t_0) = 1 + (-i) integral_(t_0)^t dd(t_1) H_I (t_1) + (-1)^2 integral_(t_0)^t dd(t_1) integral_(t_0)^(t_1) dd(t_2) H_I (t_1) H_I (t_2) + dots
$
or compactly as
$
  U(t,t_0) &= 1 +(-i) integral_(t_0)^t dd(t_1) H_I (t_1) + (-i)^2/2! integral_(t_0)^t dd(t_1, t_2) T{H_I (t_1) H_I (t_2)} + dots \
  &equiv T {exp[-i integral_(t_0)^t dd(t') H_I (t')]}
$
with $T$ meaning we time-order each term. Typically we only keep the smallest non-vanishing term.

Usually this is written as
$
  U(t,t') equiv T {exp[-i integral_(t')^t dd(t'') H_I (t'')]} #h(2em) (t >= t')
$
with $U(t',t') = 1$.

For $ket(Omega)$ consider
$
  e^(-i H T) ket(0) &= sum_n e^(-i E_n T) ket(n) braket(n, 0) \
  &= e^(-i E_0 T) ket(Omega) braket(Omega, 0) + sum_(n eq.not 0) e^(-i E_n T) ket(n) braket(n, 0)
$
we assume $braket(Omega, 0) eq.not 0$ and $E_0 = braket(Omega, H, Omega)$ while $H_0 ket(0) = 0$. Since $E_n > E_0$ for all $n eq.not 0$ we can send $T -> oo (1-i epsilon)$ to kill all $n eq.not 0$ terms. We obtain
$
  ket(Omega) = lim_(T -> oo (1- i epsilon)) [e^(-i E_0 T) braket(Omega, 0)]^(-1) e^(-i H T) ket(0)
$
Since $T$ is large we can shift $T -> T + t_0$ giving
$
  ket(Omega) &= lim_(T -> oo (1-i epsilon)) [e^(-i E_0 (t_0 - (-T))) braket(Omega, 0)]^(-1) U(t_0,-T) ket(0)
$
we use $H_0 ket(0) = 0$ to find the above. Similarly we find
$
  bra(Omega) = lim_(T -> oo (1-i epsilon)) bra(0) U(T,t_0) [e^(-i E_0 (T-t_0)) braket(0, Omega)]^(-1)
$
Assuming $x^0 > y^0 > t_0$ we find
$
  braket(Omega, phi.alt(x) phi.alt(y), Omega) &= lim_(T -> oo (1-i epsilon)) [abs(braket(0, Omega))^2 e^(-i E_0 (2 T))]^(-1) \
  &#h(2em) times braket(0, U(T,x^0) phi.alt_I (x) U(x^0,y^0) phi.alt_I (y) U(y^0, -T), 0)
$
we divide by $1 = braket(Omega, Omega)$ giving
$
  braket(Omega, phi.alt (x) phi.alt(y), Omega) = lim_(T -> oo (1-i epsilon)) braket(0, U(T,x^0) phi.alt_I (x) U(x^0,y^0) phi.alt_I (y) U(y^0, -T), 0)/braket(0, U(T,-T), 0)
$
Combining with the $y^0 > x^0$ case we find
$
  braket(Omega, T {phi.alt (x) phi.alt (y)}, Omega) = lim_(T -> oo (1 - i epsilon)) braket(0, T{phi.alt_I (x) phi.alt_I (y) exp[-i integral_(-T)^T dd(t) H_I (t)]}, 0)/braket(0, T {exp[-i integral_(-T)^T dd(t) H_I (t)]}, 0)
$
as similar expression holds for higher correlation functions.

== Wick's theorem
We need to compute expressions of the form
$
  braket(0, T {phi.alt_I (x_1) phi.alt_I (x_2) dots phi.alt_I (x_n)}, 0)
$
for $n = 2$ this is just the Feynman propagator. For higher $n$ we use a trick.

Consider $braket(0, T {phi.alt_I (x) phi.alt_I (y)}, 0)$. We write
$
  phi.alt_I (x) = phi.alt_I^+ (x) + phi.alt_I^- (x)
$
with $phi.alt_I^+ tilde a_bold(p)$ and $phi.alt_I^- tilde a_bold(p)^dagger$. This is useful since
$
  phi.alt_I^+ ket(0) = 0 " and " bra(0) phi.alt_I^- = 0
$
