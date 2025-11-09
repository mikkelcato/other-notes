//**** init-ting
#import "@preview/physica:0.9.5": *
#import "chpt-temp.typ": *
#import "@preview/mannot:0.3.0": *

#show: thmrules.with(qed-symbol: $square$)
#show: chpt-note.with()

= The free scalar field
== Quantization à la Schrödinger
In classical mechanics the momentum conjugate to $q_i (t)$ is
$
  p_i (t) = pdv(L, dot(q)_i (t))
$
and the Hamiltonian is the Legendre transform of the Lagrangian
$
  H = sum_i p_i (t) dot(q)_i (t) - L
$
to quantize in the Schrödinger picture we promote $q_i$ and $p_i$ to self-adjoint operators without time-dependence such that the fundamental commutation relation
$
  [q_i, p_j] = i delta_(i j)
$
holds.

In field theory we mimick this by defining the momentum $pi^a (x)$ conjugate to $phi.alt_a (x)$
as
$
  pi^a (x) = pdv(cal(L), dot(phi.alt)_a)
$
The Hamiltonian is then
$
  H = integral dd(x, 3) cal(H) = integral dd(x, 3) (pi(x) dot(phi.alt)(x)-cal(L))
$
with the Hamiltonian density being
$
  cal(H) = pi^a (x) dot(phi.alt)_a (x) - cal(L) (x)
$
For the scalar field action we find $pi(x) = dot(phi.alt)(x)$ so
$
  H &= integral dd(x, 3) (dot(phi.alt)^2 (x) - 1/2 partial_mu phi.alt partial^mu phi.alt + 1/2 m^2 phi.alt^2 (x)) \
  &= integral dd(x, 3) (1/2 dot(phi.alt)^2 (x) + 1/2 (grad phi.alt (x))^2 + 1/2 m^2 phi.alt^2 (x)) \
  &= integral dd(x, 3) (1/2 pi^2 (x) + 1/2 (grad phi.alt)^2 + 1/2 m^2 phi.alt^2 (x))
$
now we quantize in the Schrödinger picutre by dropping the time-dependence of $phi.alt$ and $pi$ and promoting them to operators $phi.alt^((s)) (bold(x))$ and $pi^((s)) (bold(x))$. For real scalar fields they are self-adjoint with canonical commutation relations
$
  markrect([phi.alt (bold(x)),pi (bold(y))] = i delta^((3)) (bold(x)-bold(y))",  " [phi.alt(bold(x)),phi.alt(bold(y))] = 0 = [pi(bold(x)),pi(bold(y))], outset: #.3em)
$
this approach to quantum field theory is called canonical quantization.

== The Fourier expansion
We Fourier transform our fields as
$
  phi.alt (bold(x)) &= integral dd(p, 3)/(2pi)^3 tilde(phi.alt)(bold(p)) e^(i bold(p) dot bold(x)) \
  pi (bold(x)) &= integral dd(p, 3)/(2pi)^3 tilde(pi) (bold(p)) e^(i bold(p) dot bold(x))
$
with $tilde(phi.alt)^dagger (bold(p)) = tilde(phi.alt) (- bold(p))$ to ensure $phi.alt(bold(x))$ is self-adjoint---we plug these into our Hamiltonian. Using
$
  integral dd(x, 3) e^(i (bold(p)+bold(q)) dot bold(x)) = (2 pi)^3 delta^((3)) (bold(p) + bold(q))
$
eventually yields
$
  markrect(H = integral dd(p, 3)/(2 pi)^3 (1/2 abs(tilde(pi)(bold(p)))^2 + 1/2 omega_p^2 abs(tilde(phi.alt)(bold(p)))^2), outset: #.3em)
$
where $omega_p = sqrt(bold(p)^2 + m^2)$. This is a collection of decoupled harmonic oscillators of frequency $omega_p$!---and the Hamiltonian has become diagonal which is helpful.

To solve the oscillators we follow the quantum mechanical treatment of the Hamiltonian
$
  H = 1/2 pi^2 + omega^2 q^2
$
where we define ladder operators $a$ and $a^dagger$ such that
$
  q = 1/sqrt(2 omega) (a + a^dagger)";  " pi = - sqrt(omega/2) i (a- a^dagger)
$
with $[a,a^dagger] = 1$. We generalize these using $tilde(phi.alt)(bold(p)) = tilde(phi.alt)^dagger (-bold(p))$ and $tilde(pi)(bold(p)) = tilde(pi)^dagger (- bold(p))$ to define
$
  a(bold(p)) &= 1/2 (sqrt(2 omega_p) tilde(phi.alt)(bold(p))+i sqrt(2/omega_p) tilde(pi) (bold(p)) ) \
  a^dagger (bold(p)) &= 1/2 (sqrt(2 omega_p) tilde(phi.alt) (- bold(p))-i sqrt(2/omega_p) tilde(pi) (- bold(p)))
$
we can solve for $tilde(phi.alt) (bold(p))$ and $tilde(pi)(bold(p))$
$
  tilde(phi.alt) (bold(p)) &= 1/sqrt(2 omega_p) (a(bold(p)) + a^dagger (-bold(p))) \
  tilde(pi) (bold(p)) &= - sqrt(omega_p/2)i ( a(bold(p))-a^dagger (- bold(p)))
$
using these it follows that
$
  & markrect(
      phi.alt (bold(x)) = integral dd(p, 3)/(2pi)^3 1/sqrt(2 omega_p) (a(bold(p)) e^(i bold(p)dot bold(x))+a^dagger (bold(p)) e^(- i bold(p) dot bold(x))), outset: #.3em
    ) \
  \
  & markrect(
      pi(bold(x)) = integral dd(p, 3)/(2pi)^3 (-i) sqrt(omega_p/2) (a(bold(p))e^(i bold(p)dot bold(x))-a^dagger (bold(p))e^(- i bold(p) dot bold(x)))
      , outset: #.3em,
    )
$

the main trick used is relabeling $bold(p) -> -bold(p)$ under which $omega_p = omega_(-p)$ and $dd(p, 3) = dd((-p), 3)$. We can also find the commutation relations (from the Fourier expansions)
$
  [tilde(phi.alt) (bold(p)),tilde(pi) (bold(q))] = integral dd(x, y, 3) e^(- bold(p)dot bold(x)) e^(- i bold(q) dot bold(y)) underbrace([phi.alt (bold(x)),pi(bold(y))], = i delta^((3)) (bold(x)-bold(y))) = (2pi)^3 i delta^((3)) (bold(p) + bold(q))
$
and
$
  [tilde(phi.alt) (bold(p)), tilde(phi.alt)(bold(q))] = 0 = [tilde(pi) (bold(p)), tilde(pi)(bold(q))]
$
it follows that the ladder operators obey the commutation relations
$
  markrect([a(bold(p)),a^dagger (bold(q))] = (2 pi)^3 delta^((3)) (bold(p)-bold(q))";  " [a^dagger (bold(p)),a^dagger (bold(q))] = 0 = [a(bold(p)),a(bold(q))], outset: #.3em)
$
The Hamiltonian can be written as
$
  H &= integral dd(p, 3)/(2 pi)^3 [1/2 (i sqrt(omega_p/2))^2 (a(bold(p))-a^dagger (- bold(p)))(a(-bold(p))-a^dagger (bold(p))) \
    &#h(1em)+ omega_p^2/2 1/(2 omega_p) (a(bold(p))+a^dagger (-bold(p)))(a(-bold(p))+a^dagger (bold(p)))] \
  &=^"cross terms survive" integral dd(p, 3)/(2 pi)^3 omega_p/2 [a(bold(p))a^dagger (bold(p))+a^dagger (-bold(p))a(- bold(p))] \
  &=^([a(bold(p)),a^dagger (bold(p))]) integral dd(p, 3)/(2 pi)^3 omega_p/2 [a^dagger (bold(p)) a(bold(p)) + (2pi)^3 delta^((3)) (bold(p)-bold(p))+a^dagger (-bold(p))a(- bold(p))]
$
relabeling the $- bold(p) -> bold(p)$ in the last term we get
$
  markrect(H = integral dd(p, 3)/(2 pi)^3 omega_p a^dagger (bold(p)) a(bold(p)) + Delta_H, outset: #.3em)
$
with
$
  Delta_H = 1/2 integral dd(p, 3) omega_p delta^((3)) (0)
$
which is divergent. By computation we find
$
  markrect([H,a(bold(p))] = - omega_p a(bold(p))";   "[H,a^dagger (bold(p))] = omega_p a^dagger (bold(p)), outset: #.3em)
$
by using $T^(mu nu)$ we can also compute the spatial momentum operator
$
  P^i &= integral dd(x, 3) dot(phi.alt) (bold(x)) partial^i phi.alt(bold(x)) \
  &= integral dd(p, 3)/(2 pi)^3 p^i a^dagger (bold(p)) a (bold(p)) + Delta_(p^i)
$
with
$
  Delta_(p^i) = 1/2 integral dd(p, 3) p^i delta^((3)) (0) equiv 0
$
we can then combine $H$ and $P$ (as we'd expect since both come from $T^(mu nu)$) into
$
  markrect(P^mu = integral dd(p, 3)/(2pi)^3 p^mu a^dagger (bold(p)) a(bold(p)) + Delta_(p^mu), outset: #.3em)
$
with $p^mu = (p^0, bold(p))=(omega_p, bold(p))$. It has the following commutation relations
$
  markrect([P^mu, a^dagger (bold(p))] = p^mu a^dagger (bold(p))";   " [P^mu, a(bold(p))] = - p^mu a(bold(p)), outset: #.3em)
$

== The Fock space
We seek the space that $P^mu$ acts on. Since $P^mu$ is self-adjoint it has eigenstates $ket(k^mu)$ with real eigenvalues $k^mu$,
$
  P^mu ket(k^mu) = k^mu ket(k^mu)
$
then
$
  P^mu a^dagger (bold(q)) ket(k^mu) &= a^dagger (bold(q)) P^mu ket(k^mu) + q^mu a^dagger (bold(q)) ket(k^mu) \
  &= (k^mu + q^mu) a^dagger (bold(q)) ket(k^mu)
$
and
$
  P^mu a(bold(q)) ket(k^mu) = (k^mu - q^mu) a(bold(q)) ket(k^mu)
$
so $a(bold(q))$ and $a^dagger (bold(q))$ are actually ladder operators which add or remove $q^mu$ to or from $ket(k^mu)$. Next note that $braket(psi, H, psi) >= 0$ for all states $ket(psi)$, then there must exist some state $ket(0)$ (the vacuum of the theory) such that
$
  a(bold(q)) ket(0) = 0
$
for all $bold(q)$. Otherwise successive application of $a(bold(q))$ would give negative eigenvalues of $H$. The vacuum has four-momentum
$
  P^mu ket(0) = Delta_(p^mu) ket(0) = cases(Delta_H",  " mu=0, 0",     " mu=i)
$
leading to the interpretation that $Delta_H$ is the vacuum energy. We remove this additive constant by redefining
$
  tilde(P)^mu := P^mu - Delta_(p^mu) = integral dd(p, 3)/(2pi)^3 p^mu a^dagger (bold(p)) a (bold(p))
$
so now $tilde(P)^mu ket(0) = 0$ (now we drop the tilde $tilde(P)^mu -> P^mu$). Then the state $a^dagger (bold(p)) ket(0)$ has four-momentum $p^mu$,
$
  P^mu a^dagger (bold(p)) ket(0) = p^mu a^dagger (bold(p)) ket(0)
$
with $p^mu = (E_p, bold(p))$ and $E_p = sqrt(bold(p)^2 + m^2)$. This is the relativistic dispersion relation for a particle of mass $m$, so we interpret $a^dagger (bold(p)) ket(0)$ as a one-particle state with energy $E_p$ and momentum $bold(p)$ (which is why we call $a^dagger$ the creation operator). In general an $N$-particle state with $E = E_(p_1) + dots + E_(p_N)$ and $bold(p) = bold(p)_1+dots +bold(p)_N$ is given by (a Fock state)
$
  a^dagger (bold(p)_1) dots a^dagger (bold(p)_N) ket(0)
$
which is nice.

So we started by asserting that spacetime is filled with a real scalar field $phi.alt(bold(x))$, which we took to be a free field with the Lagrangian $cal(L) = 1/2 partial_mu phi.alt partial^mu phi.alt - 1/2 m^2 phi.alt^2$. We then interpreted this field as a field operator, i.e. at every point $bold(x)$: $phi.alt(bold(x))$ represents a self-adjoint operator. We've seen the existence of a lowest energy state, the vacuum $ket(0)$. Which corresponds to the absence of excitations of the field $phi.alt(bold(x))$. If the dispersion relation $E_p = sqrt(bold(p)^2 + m^2)$ is satisfied in some region of spacetime then a particle $a^dagger (bold(p)) ket(0)$ is created as an excitation of $phi.alt(bold(x))$---and in the free theory $m$ is interpreted as the mass of the particle. Since the underlying field $phi.alt(bold(x))$ is a scalar field, we call the associated particle a scalar particle.

This naturally leads to a multi-particle theory, since the particles are just excitations of the field. We can immediately prove part of the spin-statistics theorem: _scalar particles obey Bose statistics_. We just need to show that the $N$-particle state is symmetric under permutation, which follows from the commutation relations
$
  ket(bold(p)_1 dots bold(p)_i dots bold(p)_j dots bold(p)_N) &prop a^dagger (bold(p)_1) dots a^dagger (bold(p)_i) dots a^dagger (bold(p)_j) dots a^dagger (bold(p)_N) ket(0) \
  &= a^dagger (bold(p)_1) dots a^dagger (bold(p)_j) dots a^dagger (bold(p)_i) dots a^dagger (bold(p)_N) ket(0) \
  &prop ket(bold(p)_1 dots bold(p)_j dots bold(p)_i dots bold(p)_N)
$

=== Technicalities
We normalize the one-particle momentum eigenstates as $ket(bold(p)) equiv sqrt(2 E_p) a^dagger (bold(p)) ket(0)$---we'll see why in a bit. Then
$
  braket(bold(q), bold(p)) = 2 sqrt(E_p E_q) braket(0, a(bold(q)) a^dagger (bold(p)), 0)
$
using the commutation relations we move all $a^dagger$ to the left, this lets us abuse $a(bold(q)) ket(0) = 0 = bra(0)a^dagger (bold(p))$ and is a common _trick_. We obtain
$
  markrect(braket(bold(q), bold(p)) = (2 pi)^3 2 E_p delta^((3)) (bold(p)-bold(q)), outset: #.3em)
$
obviously these aren't strictly normalizable due to the $delta$-function---but we can form wavepackets as usual.

With this normalization the identity operator is
$
  markrect(bb(1)_"one-particle" = integral dd(p, 3)/(2pi)^3 1/(2 E_p) ketbra(bold(p)), outset: #.3em)
$
this can be seen by acting on some arbitrary state
$
  ket(psi) = integral dd(q, 3) psi(bold(q)) ket(bold(q))
$
note that the measure
$
  integral dd(p, 3)/(2pi)^3 1/(2 E_p)
$
is Lorentz invariant, which is why it has been all over these notes.

In quantum mechanics recall
$
  ket(x) = integral dd(p)/(2pi) e^(i p x) ket(p)
$
with $braket(x, p) = e^(i p x)$. With our normalization this becomes
$
  markrect(ket(bold(x)) = integral dd(p, 3)/(2pi)^3 1/(2 E_p) e^(- i bold(p) dot bold(x)) ket(bold(p)), outset: #.3em)
$
since then
$
  braket(bold(x), bold(p)) = integral dd(q, 3)/(2pi)^3 1/(2 E_p) e^(i bold(q) dot bold(x)) underbrace(braket(bold(q), bold(p)), prop delta^((3))(bold(p)-bold(q))) = e^(i bold(p) dot bold(x))
$
note that
$
  ket(bold(x)) = integral dd(p, 3)/(2pi)^3 1/sqrt(2 E_p) (e^(-i bold(p) dot bold(x)) a^dagger (bold(p))+e^(i bold(p) dot bold(x)) a(bold(p))) ket(0) = phi.alt (bold(x)) ket(0)
$


== The complex scalar field
We extend what we've done so far to a complex scalar field: $phi.alt(x) eq.not phi.alt^* (x)$. A nice way to do this is by writing
$
  phi.alt(x) = 1/sqrt(2) (phi.alt_1 (x) + i phi.alt_2 (x))
$
where $phi.alt_1$ and $phi.alt_2$ are independent real scalar fields of mass $m$ (with the complex field also having mass $m$). If we take the Lagrangian
$
  cal(L) = partial_mu phi.alt^dagger (x) partial^mu phi.alt(x) - m^2 phi.alt^dagger (x) phi.alt(x)
$
then $phi.alt_1$ and $phi.alt_2$ are canonically normalized---i.e. the Lagrangian decouples. Then we can quantize $phi.alt_1$ and $phi.alt_2$ as before and rewriting everything in terms of $phi.alt (x)$---simply forgetting $phi.alt_1$ and $phi.alt_2$ at the end.

The fields $phi.alt (x)$ and $phi.alt^dagger (x)$ describe independent degrees of freedom with
$
         pi (x) & = pdv(cal(L), dot(phi.alt) (x)) = dot(phi.alt)^dagger (x) \
  pi^dagger (x) & = pdv(cal(L), dot(phi.alt)^dagger (x)) = dot(phi.alt) (x)
$
so the Hamiltonian becomes
$
  H &= integral dd(x, 3) (pi^dagger (bold(x)) dot(phi.alt)^dagger (bold(x))+ pi(bold(x)) dot(phi.alt)(bold(x))-cal(L)) \
  &= integral dd(x, 3) (pi^dagger (bold(x)) pi (bold(x))+ nabla phi.alt^dagger (bold(x)) nabla phi.alt(bold(x)) + m^2 phi.alt^dagger (bold(x)) phi.alt (bold(x)))
$

The fields are promoted to operators with commutation relations
$
  markrect([phi.alt (bold(x)),pi(bold(y))] = i delta^((3)) (bold(x)-bold(y)) = [phi.alt^dagger (bold(x)),pi^dagger (bold(y))], outset: #.3em)
$
with all others vanishing.

The Fourier expansions become
$
  phi.alt (bold(x)) &= integral dd(p, 3)/(2pi)^3 1/sqrt(2 E_p) (a (bold(p)) e^(i bold(p) dot bold(x))+ b^dagger (bold(p))e^(- i bold(p) dot bold(x))) \
  phi.alt^dagger (bold(x)) &= integral dd(p, 3)/(2pi)^3 1/sqrt(2 E_p) (b(bold(p)) e^(i bold(p) dot bold(x))+ a^dagger (bold(p)) e^(- i bold(p) dot bold(x)))
$
with $a$ and $b$ being independent operators. This can be seen by substituting the expansions for $phi.alt_1$ and $phi.alt_2$ into $phi.alt$ giving the identification
$
         a & = 1/sqrt(2) (a_1 + i a_2) \
  b^dagger & = 1/sqrt(2) (a_1^dagger + i a_2^dagger)
$
implying
$
  [a(bold(p)),a^dagger (bold(q))] = (2pi)^3 delta^((3)) (bold(p)- bold(q)) = [b (bold(p)),b^dagger (bold(q))]
$
while other commutaters vanish.

The expansion of the four-momentum operator is
$
  P^mu = integral dd(p, 3)/(2pi)^3 p^mu (a^dagger (bold(p)) a (bold(p))+ b^dagger (bold(p)) b (bold(p)))
$
note that his has two types of eigenstates
$
  a^dagger (bold(p)) ket(0) "and" b^dagger (bold(p)) ket(0)
$
both with energy $E_p$, so both have the same mass $m$---but they differ in their $"U"(1)$ charge. The Lagrangian is invariant under the global continuous $"U"(1)$ symmetry
$
  phi.alt (x) -> e^(i alpha) phi.alt (x)
$
with $alpha in RR$, and $e^(i alpha) in "U"(1)$. By Noether's theorem there is a conserved current
$
  markrect(j^mu = - i (phi.alt^dagger partial^mu phi.alt - partial^mu phi.alt^dagger phi.alt), outset: #.3em)
$
and related charge
$
  Q = integral dd(x, 3) j^0 = - integral dd(p, 3)/(2pi)^3 (a^dagger (bold(p)) a (bold(p))-b^dagger (bold(p)) b(bold(p)))
$
this acts on a particle with momentum $bold(p)$ as
$
  Q a^dagger (bold(p)) ket(0) & = - a^dagger (bold(p)) ket(0): "charge" -1 \
  Q b^dagger (bold(p)) ket(0) & = + b^dagger (bold(p)) ket(0): "charge" +1
$
so these guys are fundamentally different---in fact we interpret $a^dagger (bold(p)) ket(0)$ as a particle of mass $m$ and charge $-1$ and $b^dagger (bold(p)) ket(0)$ as a particle with the same mass $m$ but charge $+1$, i.e. its anti-particle. We'll see later that this abstract charge coincides with the physical charge we are used to in physics.

== Quantization à la Heisenberg
Recall in the Heisenberg picture:
$
  A^((H)) (t) = e^(i H^((S))(t-t_0)) A^((S)) e^(- i H^((S))(t-t_0))
$
at $t=t_0$ this coincides with the Schrödinger picture $A^((H))(t_0) = A^((S))$. We'll use $t_0 equiv 0$. The definition implies $H^((H)) (t) = H^((S))$ and one can show that the time-evolution of the operators is determined by
$
  dv(, t) A^((H)) (t) = i [H,A^((H)) (t)]
$
and the Schrödinger picture commutators become equal time commutators e.g:
$
  [q_i^((H)) (t), p_j^((H)) (t)] = i delta_(i j)
$
In field theory we similarly define the Heisenberg fields:
$
  phi.alt^((H)) (t, bold(x)) equiv phi.alt(x) &= e^(i H^((S)) t) phi.alt^((S)) (bold(x)) e^(-i H^((S)) t) \
  pi (x) &= e^(i H^((S)) t) pi^((S)) (bold(x)) e^(-i H^((S)) t) \
  cal(H) (x) &= e^(i H^((S)) t) cal(H)^((S)) (bold(x)) e^(- i H^((S)) t)
$
these obey equal time commutation relations
$
  markrect([phi.alt(x), pi(y)] &= i delta^((3)) (bold(x)-bold(y))";   " [phi.alt(x),phi.alt(y)] = 0 = [pi(x),pi(y)], outset: #.3em)
$
the Heisenberg equation of motion for $phi.alt (x)$ becomes
$
  pdv(, t) phi.alt(x) = i [H,phi.alt(x)] =^("pick" H "at" t) i integral dd(y, 3) [cal(H) (y),phi.alt(x)]
$
with
$
  cal(H) (y) = 1/2 pi^2 (y) + 1/2 (nabla phi.alt(y))^2 + 1/2 m^2 phi.alt^2 (y)
$
for a real scalar field. The only non-zero term is
$
  1/2 [pi^2 (y),phi.alt (x)] = -i pi(y) delta^((3)) (bold(x)-bold(y))
$
giving
$
  pdv(, t) phi.alt(x) = pi(x)
$
similarly
$
  pdv(, t) pi(x) = i[H,pi(y)] = nabla^2 phi.alt (x) - m^2 phi.alt (x)
$
combining these gives the Klein-Gordon equation,
$
  markrect((partial_mu partial^mu + m^2) phi.alt (x) = 0, outset: #.3em)
$
so the Klein-Gordon equation is an operator equation!

Recall from quantum mechanics that for any continuous symmetry generated by $G$:
$
  A -> A' = e^(i epsilon G) A e^(- i epsilon G)
$
we can write
$
  dv(A, epsilon) = i [G,A]
$
for some infinitesimal $epsilon$---this is why the Heisenberg equation describes how operators change under infinitesimal time translations. We can write the generalization of the Heisenberg equation for $phi.alt(x)$ as
$
  partial^mu phi.alt(x) = i [P^mu, phi.alt(x)]
$
and as a consequence for finite spacetime translations:
$
  phi.alt(x^mu + a^mu) = e^(i a^mu P_mu) phi.alt (x) e^(-i a^mu P_mu)
$
so $P^mu$ generate spacetime translations.

We now find the expansions for the Heisenberg field:
$
  phi.alt (x) = integral dd(p, 3)/(2pi)^3 1/sqrt(2 E_p) (e^(i H t) a(bold(p))e^(-i H t) e^(i bold(p)dot bold(x))+e^(i H t) a^dagger (bold(p))e^(-i H t) e^(-i bold(p)dot bold(x)))
$
since $[H,a(bold(p))] = - a(bold(p)) E_p$ we find
$
  H^n a(bold(p)) = a(bold(p)) (H-E_p)^n
$
so
$
  e^(i H t) a(bold(p)) = a(bold(p)) e^(i (H-E_p) t)
$
giving
$
  markrect(phi.alt (x) = integral dd(p, 3)/(2 pi)^3 1/sqrt(2 E_p) (a(bold(p))e^(-i p dot x) + a^dagger (bold(p))e^(i p dot x)), outset: #.3em)
$
with $p dot x equiv p_mu x^mu$---using $pi(x) = dot(phi.alt) (x)$ these can be inverted (by Fourier's trick) to find the expansions of the annihilation and creation operators.

== Causality & Propagators
=== Causality
For causality to hold we need that measurements at spacelike distances commute,
$
  [cal(O)_1 (x), cal(O)_2 (y)] =^! 0 " for " (x-y)^2 < 0
$
so the task lies in computing
$
  Delta(x-y) equiv [phi.alt (x),phi.alt (y)]
$
for general times---plugging in the expansions gives:
$
  markrect(Delta (x-y) = integral dd(p, 3)/(2pi)^3 1/(2 E_p) (e^(-i p dot (x-y))-e^(-i p dot (y-x))), outset: #.3em)
$
now we assume $(x-y)^2 < 0$. Given the measure is Lorentz invariant we can apply a Lorentz transformation such that $(x^0-y^0) = 0$---always possible for spacelike seperated points. Then
$
  evaluated(Delta (x-y))_((x-y)^2 < 0) = integral dd(p, 3)/(2pi)^3 1/(2 E_p) (e^(i bold(p) dot (bold(x)-bold(y)))-e^(-i bold(p) dot (bold(x)-bold(y))))
$
which is zero upon changing $bold(p) -> - bold(p)$ in the second term. It follows that all commutators of the form
$
  [partial_(x^mu) phi.alt (x),phi.alt (y)] = partial_(x^mu) [phi.alt (x),phi.alt (y)] = 0 " for " (x-y)^2 < 0
$
so for all local operators $ [cal(O)_i (x), cal(O)_j (y)] = 0 "if" (x-y)^2 <0 $ and causality is maintained. The above is only possible since we are working in a free theory---for more complicated theories one takes this as an axiom of quantum field theory.

=== Propagators
The probability amplitude for a particle emitted at $y$ to propagate to $x$ is given by the propagator
$
  D(x-y) equiv braket(x, y) = braket(0, phi.alt(x) phi.alt(y), 0)
$
by a mode expansion
$
  D(x-y) &= integral.double dd(p, 3)/(2pi)^3 1/sqrt(2 E_p) dd(q, 3)/(2pi)^3 1/sqrt(2 E_q) bra(0) (a(bold(q)) e^(-i q dot x) + a^dagger (bold(q)) e^(i q dot x)) \
  & #h(13.5em) times (a(bold(p)) e^(-i p dot y) + a^dagger (bold(p))e^(i p dot y)) ket(0)
$
from $a(bold(p)) ket(0) = 0 = bra(0) a^dagger (bold(q))$ the only surviving term is
$
  e^(-i q dot x) e^(i p dot x) braket(0, a(bold(q)) a^dagger (bold(p)), 0) = e^(-i q dot x) e^(i p dot x) (2pi)^3 delta^((3)) (bold(q)-bold(p))
$
the $delta^((3))$ eats the $q$-integral giving
$
  markrect(D(x-y) = integral dd(p, 3)/(2 pi)^3 1/(2 E_p) e^(-i p (x-y)), outset: #.3em)
$
leading us to write
$
  [phi.alt (x),phi.alt (y)] = underbrace(D(x-y), "particle" y -> x) - underbrace(D(y-x), "particle" x -> y)
$
so the commutator can be interpreted as two physical processes, whose probability amplitudes seemingly cancel for spacelike distances.

Similarly for a complex scalar field we have operators like
$
         phi.alt (x) & tilde a(bold(p)) + b^dagger (bold(p)) \
  phi.alt^dagger (x) & tilde a^dagger (bold(p)) + b (bold(p))
$
in this case $[phi.alt (x), phi.alt (y)] = 0$ for all $x,y$. But the commutator
$
  [phi.alt (x), phi.alt^dagger (y)] = underbrace(braket(0, phi.alt(x) phi.alt^dagger (y), 0), "particle" y -> x) - underbrace(braket(0, phi.alt^dagger (y) phi.alt (x), 0), "anti-particle" x -> y)
$
so for $(x-y)^2 < 0$ the probability of the particle propagating from $y -> x$ is cancelled by the probability that its anti-particle propagates from $x -> y$!

Now we define the most important object in quantum field theory, the Feynman propagator:
$
  markrect(D_F (x-y) equiv braket(0, T phi.alt(x) phi.alt(y), 0), outset: #.3em)
$
where we define the time-ordering operator $T$:
$
  T phi.alt (x) phi.alt (y) = cases(phi.alt (x) phi.alt (y)"   if" x^0 >= y^0, phi.alt(y) phi.alt(x)"   if" y^0 > x^0)
$
the Feynman propagator can be written as
$
  D_F (x-y) &= Theta(x^0-y^0) underbrace(braket(0, phi.alt(x) phi.alt(y), 0), D(x-y)) + Theta(y^0 - x^0) underbrace(braket(0, phi.alt(y) phi.alt(x), 0), D(y-x)) \
  &= Theta (x^0-y^0) evaluated(integral dd(p, 3)/(2pi)^3 1/(2 E_p) e^(-i p dot (x-y)))_(p^0 = E_p) \
  &#h(1em) + Theta(y^0-x^0) evaluated(integral dd(p, 3)/(2pi)^3 1/(2 E_p) e^(i p dot (x-y)))_(p^0 = E_p) \
  &=^(bold(p)->-bold(p) "in 2nd term") integral dd(p, 3)/(2pi)^3 e^(i bold(p) dot (bold(x)-bold(y))) [Theta(x^0-y^0) 1/(2 E_p) e^(-i E_p (x^0-y^0))\ &#h(14em)+Theta(y^0-x^0) 1/(2 E_p) e^(i E_p (x^0 - y^0))]
$
the bracketed term can be written as a contour integral. We can write
$
  Theta(x^0-y^0) 1/(2 E_p) e^(-i E_p (x^0-y^0)) = underbrace(-, "cw-cont") Theta(x^0-y^0) underbrace(1/(2 pi i) integral.cont_C_1 dd(p^0) e^(-i p^0 (x^0-y^0))/((p^0-E_p)(p^0+E_p)), display(-2 pi i underbracket([e^(-i E_p (x^0-y^0))/(2 E_p)], "residue")))
$
where $C_1$ is closed in the lower half-plane and clockwise with $epsilon$-surrounding to avoid the poles at $p^0 = plus.minus E_p$. We go above the pole at $+E_p$ and below the pole at $- E_p$, thereby picking up the residue at $p^0 = + E_p$. Similarly the second term in bracket can be written as
$
  Theta(y^0-x^0) 1/(2 E_p) e^(i E_p (x^0-y^0)) = - Theta(y^0-x^0) 1/(2 pi i) integral.cont_C_2 dd(p^0) e^(-i p^0 (x^0-y^0))/((p^0-E_p)(p^0+E_p))
$
with $C_2$ running counterclockwise and picking up the pole at $p_0 = - E_p$ (i.e. same contour along $RR$ but closed in the upper half-plane).

Both of these are valid for any $R > E_p$, but if $R -> oo$ then the integrals in the lower/upper half-plane each vanish. So at $R -> oo$ we can add them (since only the parts along $RR$ and the small $epsilon$-surroundings contribute), and using $Theta(x^0-y^0)+Theta(y^0-x^0) = 1$ we get
$
  D_F (x-y) = integral.cont_C dd(p, 4)/(2pi)^4 i/(p^2 -m^2) e^(-i p dot (x-y))
$
where we've used $(p^0-E-p)(p^0+E_p) = p^2 - m^2$. For a contour integral the relative position of the contour and the poles is the only thing that matters. Therefore we can instead pick $C = RR$ and then shift our poles by $plus.minus i tilde(epsilon)\/E_p$ with $tilde(epsilon)->0$. This gives
$
  p^0 = minus.plus E_p plus.minus (i tilde(epsilon))/E_p
$
then
$
  (p^0-(E_p - i tilde(epsilon)\/E_p))(p^0+(E_p-i tilde(epsilon)\/E_p)) = (p^0)^2-E_p^2 + 2 i tilde(epsilon) + epsilon^2\/E_p^2 = p^2 - m^2 + i epsilon
$
with $epsilon = 2 i tilde(epsilon) - i tilde(epsilon)\/E_p -> 0$, then the Feynman propagator becomes
$
  markrect(D_F (x-y) = integral dd(p, 4)/(2pi)^4 i/(p^2 - m^2 + i epsilon) e^(-i p dot (x-y)), outset: #.3em)
$
with $p^0$ integrated along $RR$ and with the limit $epsilon -> 0$ being applied after integrating.

=== As Green's functions
By computation one can show that the Feynman propagator is a Green's function for the Klein-Gordon equation:
$
  (square_x + m^2) D_F (x-y) = -i delta^((4)) (x-y)
$
Now consider the general solution to
$
  (square + m^2) Delta (x) = -i delta^((4)) (x)
$
this is found by a Fourier transform
$
  Delta (x) = integral dd(p, 4)/(2pi)^4 tilde(Delta)(p) e^(-i p dot x)";  " delta^((4)) (x) = integral dd(p, 4)/(2pi)^4 e^(-i p dot x)
$
and
$
  (-p^2 + m^2) tilde(Delta)(p) = -i => tilde(Delta)(p) = i/(p^2-m^2)
$
this has two poles at $p^0 = plus.minus sqrt(E^2_bold(p))$ there are four contours to avoid these---we've already seen the Feynman propagator result at one of these. Avoiding both poles along a contour in the upper half-plane gives the retarded Green's function
$
  D_R (x-y) & = Theta(x^0-y^0) [D(x-y)-D(y-x)] \
            & equiv Theta(x^0-y^0) braket(0, [phi.alt(x),phi.alt(y)], 0)
$
doing the same but in the lower half-plane gives the advanced Green's function
$
  D_A (x-y) = Theta(y^0-x^0) [D(x-y)-D(y-x)]
$
