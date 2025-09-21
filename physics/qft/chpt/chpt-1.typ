//**** init-ting
#import "@preview/physica:0.9.5": *
#import "chpt-temp.typ": *

#show: thmrules.with(qed-symbol: $square$)
#show: chpt-note.with()

= Classical Field Theory
== Dynamics of Fields
A field is a quantity defined at every point $(arrow(x),t)$. We are interested in the dynamics of these fields $phi.alt_a (arrow(x),t)$ where $a$ and $arrow(x)$ are both considered labels---so we have infinite degrees of freedom, as opposed to classical particle mechanics where we deal with a finite number of generalized coordinates $q_a (t)$---position is now just a label. A familiar example of a field would be the four-potential $A^mu (arrow(x),t)$ in electrodynamics.

=== Euler-Lagrange equations
The dynamics of the field is determined by a Lagrangian of the form
$
  L(t) = integral dd(x, 3) cal(L) (phi.alt_a, partial_mu phi.alt_a)
$
with $cal(L)$ being the Lagrangian density or just Lagrangian. The action is then
$
  S = integral_(t_1)^(t_2) dd(t) L = integral dd(x, 4) cal(L)
$
We only consider $cal(L)$ that depend on $phi.alt$, $dot(phi.alt)$ and $nabla phi.alt$---in principle it could depend on higher order derivatives and explicitely on $x^mu$ but we won't consider these. The principle of least action then gives the equations of motion for $phi.alt_a$---by
$
  dd(S, d: delta) &= integral dd(x, 4) [pdv(cal(L), phi.alt_a) dd(phi.alt_a, d: delta) + pdv(cal(L), (partial_mu phi.alt_a)) dd((partial_mu phi.alt_a), d: delta)] \
  &=^"i.b.p" integral dd(x, 4) [pdv(cal(L), phi.alt_a) - partial_mu (pdv(cal(L), (partial_mu phi.alt_a)))] dd(phi.alt_a, d: delta) +partial_mu (pdv(cal(L), (partial_mu phi.alt_a)) dd(phi.alt_a, d: delta))
$
the last term vanishes for any $dd(phi.alt_a (arrow(x),t), d: delta)$ which decays at infinity and obeys $dd(phi.alt_a (arrow(x),t_1), d: delta) = dd(phi.alt_a (arrow(x),t_2), d: delta) = 0$. We require that $dd(S, d: delta) = 0$ for all paths so we immediately find the Euler-Lagrange equations
$
  partial_mu (pdv(cal(L), (partial_mu phi.alt_a))) - pdv(cal(L), phi.alt_a) = 0
$
=== Examples
The simplest example of a Lagrangian for a real scalar field $phi.alt (arrow(x),t)$ is
$
  cal(L) &= 1/2 eta^(mu nu) partial_mu phi.alt partial_nu phi.alt-1/2 m^2 phi.alt^2 \
  &= 1/2 dot(phi.alt)^2 - 1/2 (nabla phi.alt)^2 - 1/2 m^2 phi.alt^2
$
since it should be a scalar quantity to ensure Lorentz invariance---note we use $eta^(mu nu) = eta_(mu nu) = diag(1, -1, -1, -1)$. We use the Euler-Lagrange equations
$
  pdv(cal(L), phi.alt) = - m^2 phi.alt",  " pdv(cal(L), (partial_mu phi.alt)) = partial^mu phi.alt equiv vecrow(dot(phi.alt), - nabla phi.alt)
$
so we obtain
$
  square phi.alt +m^2 phi.alt = 0
$
This is the Klein-Gordon equation---where $square = partial_mu partial^mu$.

Another example is the Maxwell Lagrangian
$
  cal(L) = - 1/2 (partial_mu A_nu) (partial^mu A^nu) + 1/2 (partial_mu A^mu)^2 =^tilde -1/4 F_(mu nu)F^(mu nu)
$
note that
$
  pdv(cal(L), A_mu) = 0
$
and
$
  pdv(, (partial_alpha A_beta)) (-1/2 (partial_mu A_nu)(partial^mu A^nu)) &= -1/2 (delta_mu^alpha delta_nu^beta partial^mu A^nu + partial_mu A_nu eta^(mu alpha) eta^(nu beta)) \
  &= - partial^alpha A^beta \
  pdv(, (partial_alpha A_beta)) (1/2 (partial_mu A^mu)^2) &= partial_mu A^mu pdv((partial_mu A_nu eta^(nu mu)), (partial_alpha A_beta)) \
  &= partial_mu A^mu eta^(alpha beta)
$
so
$
  pdv(cal(L), (partial_mu A_nu)) = - partial^mu A^nu + (partial_rho A^rho) eta^(mu nu)
$
and we obtain
$
  partial_mu (pdv(cal(L), (partial_mu A_nu))) &= - partial_mu partial^mu A^nu + partial^nu (partial_rho A^rho) \
  &= -partial_mu (partial^mu A^nu -partial^nu A^mu) equiv - partial_mu F^(mu nu) = 0
$

Both these examples are local since there are no terms in the Lagrangian coupling $phi.alt(arrow(x), t)$ with $phi.alt(arrow(y), t)$ for $arrow(x) eq.not arrow(y)$. We see coupling for different $mu$, but the closest we get for the other case is $phi.alt(arrow(x))$ coupled with $phi.alt(arrow(x)+dd(arrow(x), d: delta))$ through the gradient. This locality seems to be a key feature of all theories we have---and is a reason why we introduce fields---for this reason we only consider local Lagrangians.

== Lorentz Invariance
We want our physical laws to be relativistic---this is why we develop quantum field theory---we want space and time to be equal, and we want our theories to be invariant under Lorentz transformations $x^mu -> x'^mu = tensor(Lambda, mu, -nu) x^nu$ with $tensor(Lambda, mu, -sigma) eta^(sigma tau) tensor(Lambda, nu, -tau) = eta^(mu nu)$---these form a Lie group.

The Lorentz transformation have a representation on the fields---take the scalar field which transforms as
$
  phi.alt(x) -> phi.alt'(x) = phi.alt (Lambda^(-1) x)
$
since it is an active transformation---we move the field itself---and we want to know what the point $x$ looks like after, which is why the inverse appears. Alternatively we have
$
  phi.alt'(x') = phi.alt (x)
$
but $x' = Lambda x => Lambda^(-1) x' = x$ so $phi.alt' (x')=phi.alt (Lambda^(-1)x')$ with $x' -> x$ we get the result.

A theory is then Lorentz invariant if $phi.alt(x)$ solving the equations of motion imply that $phi.alt(Lambda^(-1)x)$ also solves the equations of motion---this is true when the action is Lorentz invariant.

=== Examples
We again look at the Klein-Gordon equation. We have $phi.alt (x) -> phi.alt' (x) = phi.alt (Lambda^(-1) x)$---the derivative of the scalar field transforms like a vector
$
  (partial_mu phi.alt) (x) -> tensor(Lambda, -nu, mu) (partial_nu phi.alt) (y)
$
with $y = Lambda^(-1) x$. The first part of the Lagrangian transforms as
$
  cal(L)(x) = partial_mu phi.alt (x) partial_nu phi.alt(x) eta^(mu nu) &-> tensor(Lambda, -rho, mu) (partial_rho phi.alt) (y) tensor(Lambda, -sigma, nu) (partial_sigma phi.alt) (y) eta^(mu nu) \
  &= (partial_rho phi.alt) (y) (partial_sigma phi.alt) (y) eta^(rho sigma) \
  &= cal(L) (y)
$
the potential term transforms with $phi.alt^2 (x) -> phi.alt^2 (y)$ so we find
$
  S = integral dd(x, 4) cal(L) (x) -> integral dd(x, 4) cal(L)(y) = integral dd(y, 4) cal(L) (y) = S
$
since changing variables doesn't add a factor due to the Jacobian since $det Lambda=1$.

This is trivial in practice, since we just need to make sure all indices are contracted---giving scalars that by definition don't transform. So the Maxwell Lagrangian is immediately invariant since all indices contract---as we'd expect since this is what led to Lorentz invariance in the first place.

== Symmetries
All physics is basically symmetries. This is primarily due to Noether's theorem.
=== Noether's Theorem
Every continuous symmetry of the Lagrangian gives rise to a conserved current $j^mu (x)$ such that
$
  partial_mu j^mu = 0
$
notably this implies charge is locally conserved---define
$
  Q_V &= integral_V dd(x, 3) j^0 \
  &=> dv(Q_V, t) = - integral_V dd(x, 3) div arrow(j) = - integral_A arrow(j) dot dd(arrow(S))
$
with some finite volume $V$. This implies that any charge leaving $V$ must be accompanied by a flow of $arrow(j)$ out of the volume---this local conservation of charge holds in any local field theory.

#proof[of Noether's theorem][

  We say the transformation $dd(phi.alt_a (x), d: delta) = X_a (phi.alt)$ is a symmetry if $dd(cal(L), d: delta)=partial_mu F^mu$ for some set of $F^mu (phi.alt)$---in this case $dd(S, d: delta) = 0$ since it adds a boundary term we assume $-> 0$. We consider some arbitrary transformation of the fields $dd(phi.alt_a, d: delta)$
  $
    dd(cal(L), d: delta) &= pdv(cal(L), phi.alt_a) dd(phi.alt_a, d: delta) + pdv(cal(L), (partial_mu phi.alt_a)) partial_mu (dd(phi.alt_a, d: delta)) \
    &= [pdv(cal(L), phi.alt_a) - partial_mu pdv(cal(L), (partial_mu phi.alt_a))] dd(phi.alt_a, d: delta) + partial_mu (pdv(cal(L), (partial_mu phi.alt_a)) dd(phi.alt_a, d: delta))
  $
  if the Euler-Lagrange equations are satisfied then the first term vanishes. So
  $
    dd(cal(L), d: delta) = partial_mu (pdv(cal(L), (partial_mu phi.alt_a)) dd(phi.alt_a, d: delta))
  $
  so for the symmetry transformation $dd(phi.alt_a, d: delta) = X_a (phi.alt)$ we find
  $
    partial_mu j^mu = 0 "with" j^mu = pdv(cal(L), (partial_mu phi.alt_a)) X_a (phi.alt) - F^mu (phi.alt)
  $
  note we sum over the $a$.
]

=== Examples
Consider a infinitesimal translation
$
  x^nu -> x^nu - epsilon^nu => phi.alt_a (x) -> phi.alt_a (x+epsilon) = phi.alt_a (x) + epsilon^nu partial_nu phi.alt_a (x)
$
similarly
$
  cal(L) (x) -> cal(L) (x) + epsilon^nu partial_nu cal(L) (x) => dd(cal(L), d: delta) = epsilon^nu partial_nu cal(L)(x)
$
and we can use Noether's theorem with $X_a (x) = epsilon^nu partial_nu phi.alt_a (x)$ and $F^mu = epsilon^mu cal(L)(x)$ giving
$
  j^mu &= epsilon^nu pdv(cal(L), (partial_mu phi.alt_a)) partial_nu phi.alt_a - epsilon^mu cal(L) \
  &= epsilon^nu pdv(cal(L), (partial_mu phi.alt_a)) partial_nu phi.alt_a - epsilon^nu delta_nu^mu cal(L) \
  &= epsilon^nu (pdv(cal(L), (partial_mu phi.alt_a)) partial_nu phi.alt_a - delta_nu^mu cal(L))
$
we define
$
  (j^mu)_nu = pdv(cal(L), (partial_mu phi.alt_a)) partial_nu phi.alt_a - delta_nu^mu cal(L) equiv tensor(T, mu, -nu)
$
so $j^mu = epsilon^nu tensor(T, mu, -nu)$---the energy-momentum tensor satisfies $partial_mu tensor(T, mu, -nu) = 0$ since
$
  partial_mu tensor(T, mu, -nu) &= partial_mu (pdv(cal(L), (partial_mu phi.alt_a)) partial_nu phi.alt_a - delta_nu^mu cal(L) ) \
  &= partial_mu (pdv(cal(L), (partial_mu phi.alt_a))) partial_nu phi.alt_a + pdv(cal(L), (partial_mu phi.alt_a)) partial_mu partial_nu phi.alt_a - partial_nu cal(L) \
  &= pdv(cal(L), phi.alt_a) partial_nu phi.alt_a + pdv(cal(L), (partial_mu phi.alt_a)) partial_mu partial_nu phi.alt_a - pdv(cal(L), phi.alt_a) partial_nu phi.alt_a - pdv(cal(L), (partial_rho phi.alt_a)) partial_nu partial_rho phi.alt_a \
  &= 0
$
as an example consider the simplest Lagrangian
$
  cal(L) = 1/2 eta^(mu nu) partial_mu phi.alt partial_nu phi.alt - 1/2 m^2 phi.alt^2
$
then
$
  tensor(T, mu nu) &= tensor(T, mu, -sigma) eta^(sigma nu)\
  &= eta^(sigma nu) pdv(cal(L), (partial_mu phi.alt)) partial_sigma phi.alt - eta^(sigma nu) delta_sigma^mu cal(L) \
  &= pdv(, (partial_mu phi.alt)) (1/2 eta^(sigma rho) partial_sigma phi.alt partial_rho phi.alt - 1/2 m^2 phi.alt^2 ) partial^nu phi.alt - eta^(mu nu) cal(L) \
  &= (1/2 eta^(sigma rho) [delta_rho^mu partial_sigma phi.alt + delta_sigma^mu partial_rho phi.alt]) partial^nu phi.alt - eta^(mu nu) cal(L) \
  &= (1/2 eta^(sigma mu) partial_sigma phi.alt + 1/2 eta^(mu rho) partial_rho phi.alt ) partial^nu phi.alt - eta^(mu nu) cal(L) \
  &= partial^mu phi.alt partial^nu phi.alt - eta^(mu nu) cal(L)
$
in this case $T^(mu nu) = T^(nu mu)$---this is not generally true.

An internal symmetry only involves a transformation of the fields and acts the same at every point in spacetime. The simplest occurs for the complex scalar field $psi (x) = (phi.alt_1 (x) + i phi.alt_2 (x))\/sqrt(2)$ a real Lagrangian can be constructed
$
  cal(L) = partial_mu psi^* partial^mu psi - V(abs(psi)^2)
$
we could vary $phi.alt_1$ and $phi.alt_2$ but this is annoying, so we just treat $psi$ and $psi^*$ as variables. Varying with respect to $psi^*$ gives
$
  partial_mu partial^mu psi + pdv(V(psi^* psi), psi^*) = 0
$
this has a continuous symmetry by $psi -> e^(i alpha) psi$ or $dd(psi, d: delta) = i alpha psi$ and $dd(psi^*, d: delta) = - i alpha psi^*$ with $dd(cal(L), d: delta) = 0$. The conserved current is
$
  j^mu = i (partial^mu psi^*)psi - i psi^* (partial^mu psi)
$
we drop the common $alpha$.

This generalizes for any internal symmetry $dd(phi.alt, d: delta) = alpha phi.alt$ where $alpha in RR$ with $dd(cal(L), d: delta)=0$. Consider $alpha = alpha(x)$, then the action is no longer invariant, but the change must have the form
$
  dd(cal(L), d: delta) = (partial_mu alpha) h^(mu (phi.alt))
$
since for constant $alpha$ it must vanish. The change in the action is then
$
  dd(S, d: delta) = integral dd(x, 4) dd(cal(L), d: delta) =^"i.b.p" - integral dd(x, 4) alpha(x) partial_mu h^mu
$
so when our equations of motion are satisfied we have $partial_mu h^mu = 0$ which means we can identify $h^mu = j^mu$.

== Hamiltonian Formalism
We define the momentum $pi^a (x)$ conjugate to $phi.alt_a (x)$
as
$
  pi^a (x) = pdv(cal(L), dot(phi.alt)_a)
$
the Hamiltonian density is then
$
  cal(H) = pi^a (x) dot(phi.alt)_a (x) - cal(L) (x)
$
and we eliminate $dot(phi.alt)_a (x)$ in favour of $pi^a (x)$ everywhere. The Hamiltonian is then
$
  H = integral dd(x, 3) cal(H)
$
In the Lagrangian formalism Lorentz invariance is obvious since the action is invariant. The Hamiltonian formalism is not manifestly Lorentz invariant. The equations of motion for $phi.alt(x) = phi.alt (arrow(x),t)$ are given by Hamilton's equations
$
  dot(phi.alt) (arrow(x),t) = pdv(H, pi (arrow(x),t))",  " dot(pi)(arrow(x),t) = - pdv(H, phi.alt (arrow(x),t))
$
these don't look Lorentz invariant, but the physics must remain unchanged---so if we start form a relativistic theory then all results should be Lorentz invariant even if it's not manifest at all steps.
