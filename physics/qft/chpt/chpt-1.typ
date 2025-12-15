//**** init-ting
#import "@preview/physica:0.9.5": *
#import "chpt-temp.typ": *

#show: thmrules.with(qed-symbol: $square$)
#show: chpt-note.with()

= Classical field theory
== Lagrangian Field Theory
The fundamental object of interest is the action $S$, which is simply the time-integral of the Lagrangian $L$. Given the field theory is local we can write the Lagrangian in terms of a Lagrangian density $cal(L)$ which is a function of one or more fields $phi.alt(x)$ and their derivatives $partial_mu phi.alt$. So we have
$
  S = integral dd(x, 4) cal(L) (phi.alt, partial_mu phi.alt)
$
we refer to $cal(L)$ as the Lagrangian moving forward. We care about this object since
$
  dd(S, d: delta) &= integral dd(x, 4) [pdv(cal(L), phi.alt) dd(phi.alt, d: delta) + pdv(cal(L), (partial_mu phi.alt)) dd((partial_mu phi.alt), d: delta)] \
  &=^"i.b.p" integral dd(x, 4) [pdv(cal(L), phi.alt) - partial_mu (pdv(cal(L), (partial_mu phi.alt)))] dd(phi.alt, d: delta) +partial_mu (pdv(cal(L), (partial_mu phi.alt)) dd(phi.alt, d: delta))
$
the last term vanishes for any $dd(phi.alt, d: delta)$ which decays at infinity and obeys $dd(phi.alt (bold(x),t_1), d: delta) = dd(phi.alt (bold(x),t_2), d: delta) = 0$. By the principle of least action $dd(S, d: delta) = 0$ for all paths, so we obtain the Euler-Lagrange equations of motion

$
  partial_mu (pdv(cal(L), (partial_mu phi.alt))) - pdv(cal(L), phi.alt) = 0
$
which should be familiar.

For a relativistic theory $cal(L)$ can contain powers of $phi.alt$ and $partial_mu phi.alt partial^mu phi.alt$. This leads us to write
$
  cal(L) = 1/2 partial_mu phi.alt partial^mu phi.alt - V(phi.alt) + O(phi.alt^n (partial phi.alt)^m)
$
with
$
  1/2 partial_mu phi.alt partial^mu phi.alt = 1/2 dot(phi.alt)^2 - 1/2 (nabla phi.alt)^2
$
The potential $V(phi.alt)$ can generally be expanded as
$
  V(phi.alt) = a + b phi.alt + c phi.alt^2 + dots
$
we take this potential to have a global minimum $phi.alt(x) = phi.alt_0 (x)$ where
$
  evaluated(pdv(V(phi.alt), phi.alt))_(phi.alt=phi.alt_0) = 0,"     " V(phi.alt_0) = V_0
$
Then by redefinition we can ensure $phi.alt_0 (x) equiv 0$ and expand $V(phi.alt)$ about this minima
$
  V(phi.alt) = V_0 + 1/2 m^2 phi.alt^2 + O(phi.alt^3)
$
note that the above implies $m^2 > 0$.

As is typical we start with the simplest case
$
  cal(L) = 1/2 partial_mu phi.alt partial^mu phi.alt - 1/2 m^2 phi.alt^2
$
which is the theory for a free real scalar field. Using the Euler-Lagrange equations we find
$
  (partial_mu partial^mu + m^2) phi.alt (x) = 0
$
which is the Klein-Gordon equation. We will return to this guy in shortly.

== Hamiltonian Field Theory
The Lagrangian formulation as described above is evidently nice when doing relativistic dynamics since the Lorentz invariance is very explicit. But since we start quantum field theory with canonical quantization it is much easier to work with the Hamiltonian formulation.

We define
$
  p(bold(x)) &equiv pdv(L, dot(phi.alt) (bold(x))) \
  &= pdv(, dot(phi.alt)(bold(x))) integral dd(y, 3) cal(L) (phi.alt (bold(y)), dot(phi.alt)(bold(y))) \
  &tilde pdv(, dot(phi.alt)(bold(x))) dd(y, 3) sum_bold(y) cal(L)(phi.alt(bold(y)),dot(phi.alt)(bold(y))) \
  &= pi(bold(x)) dd(x, 3)
$
where
$
  pi(bold(x)) equiv pdv(cal(L), dot(phi.alt)(bold(x)))
$
is the _momentum density_ conjugate to $phi.alt (bold(x))$. Then we can write the Hamiltonian as
$
  H = integral dd(x, 3) [pi(bold(x)) dot(phi.alt)(bold(x))-cal(L)] equiv integral dd(x, 3) cal(H)
$
with $cal(H)$ being the Hamiltonian density.

For the Lagrangian we had before
$
  cal(L) = 1/2 partial_mu phi.alt partial^mu phi.alt - 1/2 m^2 phi.alt^2
$
we compute $pi(x) = dot(phi.alt)(x)$ so the Hamiltonian is
$
  H = integral dd(x, 3) [1/2 pi^2 + 1/2 (nabla phi.alt)^2 + 1/2 m^2 phi.alt^2]
$

== Noether's Theorem
Symmetries and conservation laws are closely connected. This is typically summarized by Noether's theorem.

We consider continuous transformations on $phi.alt$. An infinitesimal transformation can be written as
$
  phi.alt (x) |-> phi.alt' (x) = phi.alt (x) + alpha dd(phi.alt, d: delta) (x)
$
we call the transformation a symmetry if it leaves the action invariant. For this to hold we allow the Lagrangian to change by a total derivative
$
  cal(L) (x) |-> cal(L)(x) + underbrace(alpha partial_mu cal(T)^mu (x), alpha dd(cal(L), d: delta))
$
for some $cal(T)^mu$. We compare this to
$
  alpha dd(cal(L), d: delta) &= pdv(cal(L), phi.alt) (alpha dd(phi.alt, d: delta)) + (pdv(cal(L), (partial_mu phi.alt), d: delta)) partial_mu (alpha dd(phi.alt, d: delta)) \
  &= alpha partial_mu (pdv(cal(L), (partial_mu phi.alt)) dd(phi.alt, d: delta)) + alpha [pdv(cal(L), phi.alt) - partial_mu (pdv(cal(L), (partial_mu phi.alt)))] dd(phi.alt, d: delta) \
  &=^"by E.L" alpha partial_mu (pdv(cal(L), (partial_mu phi.alt)) dd(phi.alt, d: delta))
$
and find
$
  partial_mu j^mu (x) = 0 "  for  " j^mu (x) equiv pdv(cal(L), (partial_mu phi.alt)) dd(phi.alt, d: delta) - cal(T)^mu
$
so for each symmetry we have a conserved $j^mu$. We can also express this by saying the charge
$
  Q equiv integral j^0 dd(x, 3)
$
is time-independent.

As an example consider spacetime translations. The transformation
$
  x^mu |-> x^mu - a^mu
$
can be written alternatively as a transformation of the fields
$
  phi.alt(x) |-> phi.alt (x+a) = phi.alt (x) + a^mu underbrace(partial_mu phi.alt(x), dd(phi.alt, d: delta))
$
the Lagrangian is a scalar so
$
  cal(L) |-> cal(L) + a^mu partial_mu cal(L) = cal(L) + a^nu partial_mu underbrace((tensor(delta, mu, -nu) cal(L)), cal(T)^mu)
$
We find four separately conserved currents
$
  tensor(T, mu, -nu) equiv pdv(cal(L), (partial_mu phi.alt)) partial_nu phi.alt - cal(L) tensor(delta, mu, -nu)
$
this is the energy-momentum tensor of the field $phi.alt$! The conserved charges related to this are
$
    H & = integral T^00 dd(x, 3) = integral cal(H) dd(x, 3) \
  P^i & = integral T^(0 i) dd(x, 3) = - integral pi partial_i phi.alt dd(x, 3)
$
