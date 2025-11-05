//**** init-ting
#import "@preview/physica:0.9.5": *
#import "chpt-temp.typ": *
#import "@preview/mannot:0.3.0": *

#show: thmrules.with(qed-symbol: $square$)
#show: chpt-note.with()

= Classical field theory
A field is a quantity defined at every point $(bold(x),t)$. We are interested in the dynamics of these fields $phi.alt_a (bold(x),t) equiv phi.alt_a (x^mu) equiv phi.alt_a (x)$ where $a$ and $bold(x)$ are both considered labels---so we have infinite degrees of freedom, as opposed to classical particle mechanics where we deal with a finite number of generalized coordinates $q_a (t)$---position is now just a label. A familiar example of a field would be the four-potential $A^mu (bold(x),t)$ in electrodynamics.

For now we consider a real scalar field $phi.alt_a (x) = phi.alt^*_a (x)$, we will see that such fields describe spin-zero particles.

== Lagrangian formalism
The dynamics of the field is determined by a Lagrangian of the form
$
  L(t) = integral dd(x, 3) cal(L) (phi.alt_a, partial_mu phi.alt_a)
$
with $cal(L)$ being the Lagrangian density or just Lagrangian. The action is
$
  S = integral dd(x, 4) cal(L) (phi.alt_a, partial_mu phi.alt_a)
$
and using the principle of least action gives the equations of motion for $phi.alt_a$
$
  dd(S, d: delta) &= integral dd(x, 4) [pdv(cal(L), phi.alt_a) dd(phi.alt_a, d: delta) + pdv(cal(L), (partial_mu phi.alt_a)) dd((partial_mu phi.alt_a), d: delta)] \
  &=^"i.b.p" integral dd(x, 4) [pdv(cal(L), phi.alt_a) - partial_mu (pdv(cal(L), (partial_mu phi.alt_a)))] dd(phi.alt_a, d: delta) +partial_mu (pdv(cal(L), (partial_mu phi.alt_a)) dd(phi.alt_a, d: delta))
$
the last term vanishes for any $dd(phi.alt_a (x), d: delta)$ which decays at infinity and obeys $dd(phi.alt_a (bold(x),t_1), d: delta) = dd(phi.alt_a (bold(x),t_2), d: delta) = 0$. We require that $dd(S, d: delta) = 0$ for all paths so we immediately obtain the Euler-Lagrange equations

$
  markrect(
    partial_mu (pdv(cal(L), (partial_mu phi.alt_a))) - pdv(cal(L), phi.alt_a) = 0, outset: #.3em
  )
$
Now we want to find the Lagrangian: in a relativistic theory $cal(L)$ can contain powers of $phi.alt$ and $partial_mu phi.alt partial^mu phi.alt equiv eta^(mu nu) partial_mu phi.alt partial_nu phi.alt$ (the simplest scalar we can build from $partial_mu phi.alt$). This leads us to write
$
  S = integral dd(x, 4) (1/2 partial_mu phi.alt partial^mu phi.alt - V(phi.alt) + O(phi.alt^n (partial phi.alt)^m))
$
with
$
  1/2 partial_mu phi.alt partial^mu phi.alt = 1/2 dot(phi.alt)^2 - 1/2 (nabla phi.alt)^2
$
and $V(phi.alt(x))$ has the general form
$
  V(phi.alt(x)) = a + b phi.alt(x) + c phi.alt^2 (x) + dots
$
we assume this potential has a global minimum $phi.alt(x) = phi.alt_0 (x)$ where
$
  evaluated(pdv(V(phi.alt), phi.alt))_(phi.alt=phi.alt_0) = 0,"     " V(phi.alt_0) = V_0
$
we can by redefinition ensure $phi.alt_0 (x) equiv 0$ and expand $V(phi.alt(x))$ about this minimum
$
  V(phi.alt(x)) = V_0 + 1/2 m^2 phi.alt^2 (x) + O(phi.alt^3 (x))
$
where we have used that the linear terms vanish at the extremum, that we expand around a minimum further implies $m^2 > 0$.  The constant $V_0$ is the vacuum energy, we let $V_0 = 0$ for now, but in principle it is arbitrary. The action becomes
$
  S = integral dd(x, 4) (1/2 (partial phi.alt)^2 - 1/2 m^2 phi.alt^2 + dots)
$
we will see later that $m^2$ is related to the mass of the particles, and the omitted higher powers of $phi.alt$ as well as the terms $O(phi.alt^n (partial phi.alt)^m)$ give rise to interactions between particles.

As is typical we start with the simplest case and ignore interaction terms giving us the action of the free real scalar field theory
$
  markrect(S = integral dd(x, 4) (1/2 (partial phi.alt)^2 - 1/2 m^2 phi.alt^2)",    " phi.alt = phi.alt^*, outset: #.3em)
$
using the Euler-Lagrange equations we find
$
  markrect((partial_mu partial^mu + m^2) phi.alt (x) = 0, outset: #.3em)
$
which is the Klein-Gordon equation. This is a relativistic wave equation solved by
$
  e^(plus.minus i p x);"   " p equiv p^mu
$
substitution gives the dispersion relation
$
  -p^2 + m^2 = 0 => p^0 = plus.minus sqrt(bold(p)^2 + m^2)
$
we define
$
  E_bold(p) := sqrt(bold(p)^2 + m^2) equiv E_p
$
so we write the general solution as
$
  phi.alt (x) = integral dd(p, 3)/(2 pi)^3 1/sqrt(2 E_p) (f(bold(p)) e^(-i p x) + g(bold(p))e^(i p x))
$
for real $phi.alt$: $f^* = g$, and $p x equiv p dot x = p^mu x_mu$.

== Noether's Theorem
We consider a Lagrangian $cal(L) (phi.alt, partial_mu phi.alt)$. A symmetry is defined as a field transformation by which $cal(L)$ changes at most by a total derivative leaving the action invariant---ensuring the equations of motion are invariant. Symmetries and conservation laws are related by Noether's theorem:
#thm[
  Every continuous symmetry gives rise to a Noether current $j^mu (x)$ such that (on-shell)
  $
    partial_mu j^mu = 0
  $
]

#proof[
  For a continuous symmetry we can write
  $
    phi.alt -> phi.alt + epsilon dd(phi.alt, d: delta) + O (epsilon^2)
  $
  with $dd(phi.alt, d: delta) = X (phi.alt, partial_mu phi.alt)$. We know
  $
    cal(L) -> cal(L) + epsilon dd(cal(L), d: delta) + O(epsilon^2)
  $
  with $dd(cal(L), d: delta) = partial_mu F^mu$ for some $F^mu$. Under some arbitrary $phi.alt -> phi.alt + epsilon dd(phi.alt, d: delta)$ we have
  $
    dd(cal(L), d: delta) &= pdv(cal(L), phi.alt) dd(phi.alt, d: delta) + pdv(cal(L), (partial_mu phi.alt)) dd((partial_mu phi.alt), d: delta) \
    &= partial_mu (pdv(cal(L), (partial_mu phi.alt)) dd(phi.alt, d: delta)) + (pdv(cal(L), phi.alt) - partial_mu pdv(cal(L), (partial_mu phi.alt))) dd(phi.alt, d: delta)
  $
  If $dd(phi.alt, d: delta) = X$ is a symmetry then $dd(cal(L), d: delta) = partial_mu F^mu$. Defining
  $
    markrect(j^mu equiv pdv(cal(L), (partial_mu phi.alt)) X - F^mu, outset: #.3em)
  $
  we have
  $
    partial_mu j^mu = - (pdv(cal(L), phi.alt) - partial_mu pdv(cal(L), (partial_mu phi.alt))) X =^"E.L" 0
  $
]
#lemma[
  Every continuous symmetry whose Noether current satisfies $j^i (t, bold(x)) -> 0$ sufficiently fast for $abs(bold(x)) -> oo$ gives rise to a conserved charge $Q$ with
  $
    markrect(dot(Q) = 0, outset: #.3em)
  $
]
#proof[
  Take
  $
    Q = integral_(RR^3) dd(x, 3) j^0 (t, bold(x))
  $
  then
  $
    dot(Q) & = integral_(RR^3) dd(x, 3) pdv(, t) j^0 \
           & =^(partial_mu j^mu = 0) - integral_(RR^3) dd(x, 3) partial_i j^i = 0
  $
]
the assumption that $j^i -> 0$ for $abs(bold(x)) -> oo$ is essentially the assumption that the fields vanish at spatial infinity which is usually valid.

We now consider a global transformation $x^mu -> x^mu + epsilon^mu$, a scalar field $phi.alt(x^mu)$ transforms like
$
  phi.alt(x^mu) -> phi.alt(x^mu-epsilon^mu) = phi.alt(x^mu) - epsilon^nu underbrace(partial_nu phi.alt(x^mu), equiv X_nu (phi.alt)) + O(epsilon^2)
$
and $cal(L)$ transforms as
$
  cal(L) -> cal(L) - epsilon^nu partial_nu cal(L) &= cal(L) - tensor(eta, mu, -nu) epsilon^nu partial_mu cal(L) \
  &= cal(L) - epsilon^nu partial_mu underbrace(tensor(eta, mu, -nu) cal(L), equiv (F^mu)_nu)
$
so for each $nu$ we have a conserved current $(j^mu)_nu$
$
  (j^mu)_nu = pdv(cal(L), (partial_mu phi.alt)) partial_nu phi.alt - tensor(eta, mu, -nu) cal(L)
$
with both up we get the canonical energy-momentum tensor
$
  markrect(T^(mu nu) = pdv(cal(L), (partial_mu phi.alt)) partial^nu phi.alt - eta^(mu nu) cal(L)" with " partial_mu T^(mu nu) =^"on-shell" 0, outset: #.3em)
$
the conserved charges are the energy $E = integral dd(x, 3) T^(00)$ associated with time translation invariance, and the spatial momentum $P^i = integral dd(x, 3) T^(0i)$ associated with spatial translation invariance. These can be combined
$
  P^nu = integral dd(x, 3) T^(0 nu)" with "dot(P)^nu = 0
$


