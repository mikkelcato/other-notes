//**** init-ting
#import "@preview/physica:0.9.5": *
#import "chpt-temp.typ": *

#show: thmrules.with(qed-symbol: $square$)
#show: chpt-note.with()

= Free Fields
== Canonical Quantization
Canonical quantization is the procedure to go from the Hamiltonian formalism of classical dynamics to the quantum theory. The idea is to take our generalized coordinates $q_a$ and the conjugate momenta $p^a$ and promote them to operators---with Poisson brackets becoming commutators---so
$
  [q_a,q_b] & = [p^a,p^b] = 0 \
  [q_a,p^b] & = i delta_a^b
$
in field theory we do the same, now we just promote the fields $phi.alt_a (arrow(x))$ and its momentum conjugate $pi^b (arrow(x))$---so a quantum field is an operator valued function obeying
$
  [phi.alt_a (arrow(x)),phi.alt_b (arrow(y))] &= [pi^a (arrow(x)), pi^b (arrow(y))] = 0\
  [phi.alt_a (arrow(x)), pi^b (arrow(y))] &= i delta^(3) (arrow(x)-arrow(y)) delta_a^b
$
note that we are working in the Schrödinger picture---so all time-dependence lies in $ket(psi)$ with the operators $phi.alt_a (arrow(x))$ and $pi^a (arrow(x))$ being time-independent. The state evolve by the usual
$
  i dv(ket(psi), t) = H ket(psi)
$
so this is the exact same formalism as usual just with fields---as usual we'd like the spectrum of the Hamiltonian $H$. This is rough since we have infinite degrees of freedom.

For free theories however we can do dynamics such that each degree of freedom evolves independently---these typically have Lagrangians which are quadratic in the fields $->$ linear equations of motion. The simplest relativistic free theory is the classical Klein-Gordon equation
$
  partial_mu partial^mu phi.alt + m^2 phi.alt = 0
$
the degrees of freedom decouple if we take the Fourier transform
$
  phi.alt (arrow(x),t) = integral dd(p, 3)/(2pi)^3 e^(i arrow(p) dot arrow(x)) phi.alt (arrow(p),t)
$
then
$
  0 &= square phi.alt + m^2 phi.alt \
  0 &= (pdv(, t, 2)- nabla^2 ) phi.alt + m^2 phi.alt \
  0 &= (pdv(, t, 2)- nabla^2 + m^2) integral dd(p, 3)/(2 pi)^3 e^(i arrow(p)dot arrow(x)) phi.alt(arrow(p), t) \
  0 &= integral dd(p, 3)/(2pi)^3 e^(i arrow(p) dot arrow(x)) [pdv(, t, 2) phi.alt + m^2 phi.alt - (i arrow(p))^2 phi.alt] \
  &=> [pdv(, t, 2) + (arrow(p)^2 + m^2)] phi.alt (arrow(p),t) = 0
$
this is just the equation for a harmonic oscillator with frequency
$
  w_arrow(p) = + sqrt(arrow(p)^2+m^2)
$
so the general solution to the Klein-Gordon equation is a linear superposition of simple harmonic oscillators vibrating at different frequencies and amplitudes. To quantize this guy we just need to quantize this infinite number of harmonic oscillators.

=== The Simple Harmonic Oscillator
The quantum Hamiltonian is
$
  H = 1/2 p^2 + 1/2 omega^2 q^2
$
with $[q,p] = i$. We define the creation and annihilation operators
$
  a = sqrt(omega/2) q + i/sqrt(2 omega) p",  " a^dagger = sqrt(omega/2) q - i/sqrt(2 omega) p
$
or inverting
$
  q = 1/sqrt(2 omega) (a + a^dagger)",  " p = -i sqrt(omega/2) (a - a^dagger)
$
we can find $[a,a^dagger] = 1$ and
$
  H = omega (a^dagger a + 1/2)
$
with $[H,a^dagger] = omega a^dagger$ and $[H,a] = - omega a$. Let $ket(E)$ be an eigenstate with energy $E$ then
$
  H a^dagger ket(E) = (E+ omega) a^dagger ket(E)",  " H a ket(E) = (E-omega)a ket(E)
$
so we get a ladder of states with energies $dots, E - omega, E, E + omega, dots$. If the energy is bounded below then we have some $ket(0)$ with $a ket(0) = 0$ and ground state energy---zero point energy---given by
$
  H ket(0) = 1/2 omega ket(0)
$
the excited states are then obtained by repetition of $a^dagger$
$
  ket(n) = (a^dagger)^n ket(0)",  " H ket(n) = (n+1/2) omega ket(n)
$
ignoring normalization of $ket(n)$.

== The Free Scalar Field
We apply the quantization of the harmonic oscillator the the free scalar field---we write $phi.alt$ and $pi$ as a sum of an infinite number of creation and annihilation operators $a^dagger_arrow(p)$ and $a_arrow(p)$
$
  phi.alt (arrow(x)) &= integral dd(p, 3)/(2pi)^3 1/sqrt(2 omega_arrow(p)) [a_arrow(p) e^(i arrow(p) dot arrow(x))+a^dagger_arrow(p) e^(- i arrow(p) dot arrow(x))] \
  pi (arrow(x)) &=integral dd(p, 3)/(2pi)^3 (-i) sqrt(omega_arrow(p)/2) [a_arrow(p) e^(i arrow(p) dot arrow(x))-a^dagger_arrow(p) e^(- i arrow(p) dot arrow(x))]
$
so each momentum mode of the field is a simple harmonic oscillator. We claim that
$
  [phi.alt (arrow(x)), phi.alt (arrow(y))] = [pi (arrow(x)),pi(arrow(y))] &= 0",  " [phi.alt (arrow(x)),pi (arrow(y))] = i delta^3 (arrow(x)-arrow(y)) \
  <=> [a_arrow(p),a_arrow(q)] = [a^dagger_arrow(p),a^dagger_arrow(q)] &= 0",  " [a_arrow(p),a^dagger_arrow(q)] = (2pi)^3 delta^3 (arrow(p)-arrow(q))
$

#proof[
  Assume $[a_arrow(p),a^dagger_arrow(q)] = (2pi)^3 delta^3 (arrow(p)-arrow(q))$.
  $
    [phi.alt (arrow(x)),pi (arrow(y))] &= integral (dd(p, 3) dd(q, 3))/(2 pi)^6 (-i)/2 sqrt(omega_arrow(q)/omega_arrow(p)) {- [a_arrow(p),a^dagger_arrow(q)] e^(i arrow(p) dot arrow(x) - i arrow(q) dot arrow(y))+[a^dagger_arrow(p),a_arrow(q)] e^(- i arrow(p) dot arrow(x) + i arrow(q) dot arrow(y))} \
    &=^(integral dd(q, 3)) integral dd(p, 3)/(2pi)^3 (-i)/2 (-e^(i arrow(p) dot (arrow(x)-arrow(y)))-e^(i arrow(p) dot (arrow(y)-arrow(x)))) \
    &= i delta^3 (arrow(x)-arrow(y))
  $
  for the other direction we need to invert $phi.alt (arrow(x))$ and $pi (arrow(x))$ this is basically just an inverse Fourier transform take
  $
    integral dd(x, 3) phi.alt (arrow(x)) e^(-i arrow(p) dot arrow(x)) &= integral dd(x, 3) e^(- i arrow(p) dot arrow(x)) integral dd(q, 3)/(2pi)^3 1/sqrt(2 omega_arrow(q)) [a_arrow(q) e^(i arrow(q) dot arrow(x)) + a^dagger_arrow(q) e^(-i arrow(q) dot arrow(x))] \
    &= integral dd(q, 3) 1/sqrt(2 omega_arrow(q)) [a_arrow(q) ( delta^3 (arrow(q)-arrow(p)) + a^dagger_arrow(q) delta^3 (arrow(q)+arrow(p))] \
    &= 1/sqrt(2 omega_arrow(p)) a_arrow(p) + 1/sqrt(2 omega_(- arrow(p))) a^dagger_(-arrow(p)) \
    &= 1/sqrt(2 omega_arrow(p)) (a_arrow(p) + a^dagger_(-arrow(p))) \
    sqrt(2 omega_arrow(p)) integral dd(x, 3) e^(-i arrow(p) dot arrow(x)) phi.alt (arrow(x)) &= a_arrow(p) + a^dagger_(-arrow(p))
  $
  similarly
  $
    integral dd(x, 3) e^(-i arrow(p) dot arrow(x)) pi(arrow(x)) &= i sqrt(omega_arrow(p)/2) (- a_arrow(p) + a^dagger_(-arrow(p))) \
    i sqrt(2/omega_arrow(p)) integral dd(x, 3) e^(-i arrow(p) dot arrow(x)) pi(arrow(x)) &= a_arrow(p) - a^dagger_(-arrow(p))
  $
  so we find
  $
    a_arrow(p) &= 1/2 integral dd(x, 3) sqrt(2 omega_arrow(p)) e^(-i arrow(p) dot arrow(x)) phi.alt (arrow(x)) + i sqrt(2/omega_arrow(p)) e^(-i arrow(p) dot arrow(x)) pi(arrow(x)) \
    &= 1/sqrt(2 omega_arrow(p)) integral dd(x, 3) e^(- i arrow(p) dot arrow(x)) (omega_arrow(p) phi.alt(arrow(x))+i pi(arrow(x)))
  $
  and
  $
    a^dagger_arrow(p) = 1/sqrt(2 omega_arrow(p)) integral dd(x, 3) e^(i arrow(p) dot arrow(x)) (omega_arrow(p) phi.alt(arrow(x)) - i pi(arrow(x)))
  $
  now
  $
    [a_arrow(p),a^dagger_arrow(q)] &= 1/(2 sqrt(omega_arrow(p) omega_arrow(q))) integral dd(x, y, 3) e^(- i arrow(p) dot arrow(x) + arrow(q) dot arrow(y)) [(omega_arrow(p) phi.alt(arrow(x)) + i pi(arrow(x))),(omega_arrow(q) phi.alt(arrow(y))-i pi (arrow(y)))] \
    &= 1/(2 sqrt(omega_arrow(p) omega_arrow(q))) integral dd(x, y, 3) e^(i arrow(q) dot arrow(y) -i arrow(p) dot arrow(x) ) {- i omega_arrow(p) [phi.alt(arrow(x)),pi(arrow(y)))] + i omega_arrow(q) [pi(arrow(x)),phi.alt(arrow(y))] } \
    &= 1/(2 sqrt(omega_arrow(p) omega_arrow(q))) integral dd(x, y, 3) e^(i arrow(q) dot arrow(y) -i arrow(p) dot arrow(x) ) { omega_arrow(p) delta^3 (arrow(x)-arrow(y)) + omega_arrow(q) delta^3(arrow(y)-arrow(x)) } \
    &= 1/(2 sqrt(omega_arrow(p) omega_arrow(q))) integral dd(x, 3) e^(i (arrow(q)-arrow(p)) dot arrow(x)) (omega_arrow(p) + omega_arrow(q)) \
    &= 1/(2 sqrt(omega_arrow(p) omega_arrow(q))) (omega_arrow(p)+omega_arrow(q)) (2 pi)^3 delta^3 (arrow(q)-arrow(p)) \
    &= (2 pi)^3 delta^3 (arrow(p)-arrow(q))
  $
  this is a bit loose but it works.
]

We can also find the Hamiltonian
$
  H &= 1/2 integral dd(x, 3) pi^2 + (grad phi.alt)^2 + m^2 phi.alt^2 \
  &= 1/2 integral (dd(x, p, q, 3))/(2pi)^6 [- sqrt(omega_arrow(p) omega_arrow(q))/2 (a_arrow(p) e^(i arrow(p) dot arrow(x))-a^dagger_arrow(p) e^(- i arrow(p) dot arrow(x)))(a_arrow(q) e^(i arrow(q) dot arrow(x))-a^dagger_arrow(q) e^(- i arrow(q) dot arrow(x))) \
    &+ 1/(2 sqrt(omega_arrow(p) omega_arrow(q))) (i arrow(p) a_arrow(p) e^(i arrow(p) dot arrow(x))-i arrow(p) a^dagger_arrow(p) e^(- i arrow(p) dot arrow(x)))(i arrow(q) a_arrow(q) e^(i arrow(q) dot arrow(x))-i arrow(q) a^dagger_arrow(q) e^(- i arrow(q) dot arrow(x))) \
    &+ m^2/(2 sqrt(omega_arrow(p) omega_arrow(q)))( a_arrow(p)e^(i arrow(p) dot arrow(x))+a^dagger_arrow(p) e^(- i arrow(p) dot arrow(x)) )(a_arrow(q) e^(i arrow(q) dot arrow(x))+a^dagger_arrow(q) e^(- i arrow(q) dot arrow(x)) )] \
  &=^(integral dd(x, q, 3)) 1/4 integral dd(p, 3)/(2 pi)^3 1/omega_arrow(p) [(-omega_arrow(p)^2 + arrow(p)^2 + m^2)(a_arrow(p) a_(-arrow(p)) + a^dagger_arrow(p) a^dagger_(-arrow(p)))+(omega_arrow(p)^2 + arrow(p)^2 + m^2)(a_arrow(p)a^dagger_arrow(p) + a^dagger_arrow(p) a_arrow(p))]
$
this is a mess, however since $omega_arrow(p)^2 = arrow(p)^2+m^2$ the first term vanishes and we obtain
$
  H &= 1/2 integral dd(p, 3)/(2pi)^3 omega_arrow(p) [a_arrow(p) a^dagger_arrow(p) + a^dagger_arrow(p) a_arrow(p)] \
  &= integral dd(p, 3)/(2pi)^3 omega_arrow(p) [a^dagger_arrow(p) a_arrow(p) + 1/2 (2 pi)^3 delta^3 (0)]
$
where we add and subtract $a^dagger_arrow(p) a_arrow(p)$ two get the equality---this result is weird since our Hamiltonian apparently has an infinite spike at $0$.

== Vacuum
We define vacuum $ket(0)$ by requiring that it is annihilated by all $a_arrow(p)$
$
  a_arrow(p) ket(0) = 0 "for all" arrow(p)
$
with this the energy of the ground state comes from the second term of the Hamiltonian
$
  H ket(0) equiv E_0 ket(0) = (integral dd(p, 3) 1/2 omega_arrow(p) delta^3 (0)) ket(0) = oo ket(0)
$
infinities pop up all over the place in quantum field theory.  In this expression we have an infinity due to space being infinite---infra-red divergence---to solve this problem we put our theory inside a box of length $L$ and impose periodic boundaries. Then
$
  (2pi)^3 delta^3 (0) = lim_(L -> oo) integral_(-L\/2)^(L\/2) dd(x, 3) evaluated(e^(i arrow(x) dot arrow(p)))_(arrow(p)=0) = lim_(L -> oo) integral_(-L\/2)^(L\/2) dd(x, 3) = V
$
so $delta(0)$ is a problem because we are calculating total energy, we could instead calculate energy density
$
  cal(E)_0 = E_0/V = integral dd(p, 3)/(2 pi)^3 1/2 omega_arrow(p)
$
but this is still infinite, since $cal(E)_0 -> oo$ when $abs(arrow(p)) -> oo$ in the limit---ultra-violet divergence (short distance). This happens since we assume our theory is valid for arbitrary scales.

A simpler way to deal with the infinity is by redefining our Hamiltonian by subtracting it off---since we just care about energy differences anyway
$
  H = integral dd(p, 3)/(2pi)^3 omega_arrow(p) a^dagger_arrow(p) a_arrow(p)
$
so we remove the zero-point energy---and now $H ket(0) = 0$. In fact the difference between our two Hamiltonians is ordering ambiguity---we could have defined $ H = 1/2 (omega q - i p)(omega q + i p) $
which would be the same classically, and upon quantization we'd find $H = omega a^dagger a$. This method is called normal ordering, written as
$
  : phi.alt_1 (arrow(x)_1) dots phi.alt_n (arrow(x)_n) :
$
where it is defined as the usual product but with all annihilation operators $a_arrow(p)$ placed to the right so $:a a^dagger: = a^dagger a$ this makes
$
  :H: = integral dd(p, 3)/(2 pi)^3 omega_arrow(p) a^dagger_arrow(p) a_arrow(p)
$
\*Casimir force.

== Particles
We can now handle excitations of the field. We start by showing
$
  [H,a^dagger_arrow(p)] = omega_arrow(p) a^dagger_arrow(p)",  " [H,a_arrow(p)] = - omega_arrow(p) a_arrow(p)
$
#proof[
  The first
  $
    [H, a_arrow(q)^dagger] &= integral dd(p, 3)/(2 pi)^3 omega_arrow(p) [a_arrow(p)^dagger a_arrow(p),a^dagger_arrow(q)] \
    &= integral dd(p, 3)/(2pi)^3 omega_arrow(p) a^dagger_arrow(p) [a_arrow(p),a^dagger_arrow(q)] \
    &= omega_arrow(q) a^dagger_arrow(q)
  $
  the second
  $
    [H, a_arrow(q)] &= integral dd(p, 3)/(2 pi)^3 omega_arrow(p) [a_arrow(p)^dagger a_arrow(p),a_arrow(q)] \
    &= integral dd(p, 3)/(2pi)^3 omega_arrow(p) a_arrow(p) [a_arrow(p)^dagger,a_arrow(q)] \
    &= -omega_arrow(q) a_arrow(q)
  $
]
so similarly to the harmonic oscillator we can construct energy eigenstates by acting on $ket(0)$ with $a^dagger_arrow(p)$
$
  ket(arrow(p)) = a^dagger_arrow(p) ket(0)
$
this state has energy
$
  H ket(arrow(p)) = omega_arrow(p) ket(arrow(p))",  " omega_arrow(p)^2 = arrow(p)^2 + m^2
$
#proof[
  $
    H ket(arrow(p)) &= integral dd(q, 3)/(2pi)^3 omega_arrow(q) a^dagger_arrow(q) a_arrow(q) a^dagger_arrow(p) ket(0) \
    &= integral dd(q, 3)/(2pi)^3 omega_arrow(q) a^dagger_arrow(q) {[a_arrow(q),a^dagger_arrow(p)]+a^dagger_arrow(p) a_arrow(q)}ket(0) \
    &=^(a_arrow(q) ket(0) = 0) integral dd(q, 3)/(2pi)^3 omega_arrow(q) a_arrow(q)^dagger (2pi)^3 delta^3 (arrow(q)-arrow(p)) ket(0) \
    &= omega_arrow(p) a^dagger_arrow(p) ket(0) = omega_arrow(p) ket(arrow(p))
  $
]
and we recognize the relativistic dispersion relation for a particle of mass $m$ with momentum $arrow(p)$
$
  E_arrow(p)^2 = arrow(p)^2 + m^2
$
so we interpret $ket(arrow(p))$ as the momentum eigenstate of a single particle of mass $m$---further we'll write $E_arrow(p)$ instead of $omega_arrow(p)$ from now on.

We can consider other operators, e.g. the classical momentum $arrow(P)$ which after normal ordering can be written as
$
  arrow(P) = - integral dd(x, 3) pi grad phi.alt = integral dd(p, 3)/(2 pi)^3 arrow(p) a^dagger_arrow(p) a_arrow(p)
$
this form is similar to the Hamiltonian so it is obvious that
$
  arrow(P) ket(arrow(p)) = arrow(p) ket(arrow(p))
$
as we'd expect. We can also look at the angular momentum
$
  J^i = epsilon^(i j k) integral dd(x, 3) (cal(J)^0)^(j k)
$
one can show that $J^i ket(arrow(p)=0) = 0$---so the particle has no internal angular momentum, i.e. quantizing a scalar field gives rise to a spin 0 particle.

By acting with multiple $a^dagger$ we can create multi-particle states---we say the state where $n$ $a^dagger$ act on the vacuum as an $n$-particle state
$
  ket(arrow(p)_1","dots","arrow(p)_n) = a^dagger_(arrow(p)_1) dots a^dagger_(arrow(p)_n) ket(0)
$
all $a^dagger$ commute with themselves, so this state is fully symmetric under exchange meaning the particles are bosons. The full Hilbert space---the Fock space---is spanned by acting on vacuum with all possible combinations of $a^dagger$
$
  ket(0)",  " a_arrow(p)^dagger ket(0)",  " a^dagger_arrow(p) a^dagger_arrow(q) ket(0) dots
$
this space is just the sum of the $n$-particle Hilbert spaces. The number operator $N$ counts the number of particles in a given state in the Fock space
$
  N = integral dd(p, 3)/(2pi)^3 a^dagger_(arrow(p)) a_arrow(p)
$
it satisfies $N ket(arrow(p)_1"," dots"," arrow(p)_n) = n ket(arrow(p)_1"," dots"," arrow(p)_n)$. This is because
$
  a^dagger_arrow(p) a_arrow(p) ket(arrow(p)_1","dots","arrow(p)_n) = sum_(j=1)^n (2pi)^3 delta^3 (arrow(p)-arrow(p)_j) ket(arrow(p)_1","dots","arrow(p)_n)
$
then the integral would just return the sum giving $n$. It also commutes with the Hamiltonian $[N,H]=0$ so particle number is conserved---this is a property of free theories since interactions are what destroy or create particles.

Similarly to quantum mechanics the states $ket(arrow(p))$ are bad since we can't normalize them---we have
$
  braket(0, a_arrow(p) a_arrow(p)^dagger, 0) &= braket(arrow(p)) = (2pi)^3 delta(0) \
  braket(0, phi.alt(arrow(x)) phi.alt (arrow(x)), 0) &= braket(arrow(x)) = delta(0)
$
so the operators $a_arrow(p)$ and $phi(arrow(x))$ are not good operators---$braket(arrow(p))$ becomes a operator valued distribution. We can construct well-defined operators by smearing the distributions---e.g. using a wavepacket
$
  ket(phi) = integral dd(p, 3)/(2pi)^3 e^(-i arrow(p) dot arrow(x)) phi(arrow(p)) ket(arrow(p))
$
a typical state could be described by a Gaussian
$
  phi(arrow(p)) = exp[-(arrow(p)^2)/(2 m^2)]
$

=== Relativistic Normalization
We normalize $braket(0) = 1$. Then $ket(arrow(p)) = a^dagger_arrow(p) ket(0)$ satisfies
$
  braket(arrow(p), arrow(q)) = (2pi)^3 delta^3 (arrow(p)-arrow(q))
$
#proof[
  $
    braket(arrow(p), arrow(q)) & = braket(0, a_arrow(p) a^dagger_arrow(q), 0) \
                               & = braket(0, [a_arrow(p),a^dagger_arrow(q)], 0) \
                               & = (2pi)^3 delta^3(arrow(p)-arrow(q)) braket(0) \
                               & = (2pi)^3 delta^3(arrow(p)-arrow(q))
  $
]
we'd like to know if this is Lorentz invariant. We know the identity operator is Lorentz invariant
$
  1 = integral dd(p, 3)/(2pi)^3 ketbra(arrow(p))
$
however neither part is Lorentz invariant by itself. We claim that
$
  integral dd(p, 3)/(2 E_arrow(p))
$
is invariant.

#proof[
  $integral dd(p, 4)$ is Lorentz invariant, and so is
  $
    p_mu p^mu = m^2 => p_0^2 = E_arrow(p)^2 = arrow(p)^2 + m^2
  $
  both branches of $p_0 = plus.minus E_arrow(p)$ are also invariant. So
  $
    evaluated(integral dd(p, 4) dd((p_0^2-arrow(p)^2-m^2), d: delta))_(p_0 > 0) = integral dd(p, 3)/(2 p_0) = integral dd(p, 3)/(2 E_arrow(p))
  $
  is Lorentz invariant---note we use
  $
    delta (p_0^2 - E^2_arrow(p)) = 1/(2 E_arrow(p)) (delta(p_0 - E_arrow(p))+delta(p_0 + E_arrow(p)))
  $
  to do the $integral dd(p_0)$ only picking the positive energies.
]

From this we find the Lorentz invariant $delta$-function
$
  2 E_arrow(p) delta^3 (arrow(p)-arrow(q)) => integral dots = 1
$
so the relativistically normalized momentum states are given by
$
  ket(p) = sqrt(2 E_arrow(p)) ket(arrow(p)) = sqrt(2 E_arrow(p)) a^dagger_arrow(p) ket(0)
$
now
$
  braket(p, q) = (2 pi)^3 2 E_arrow(p) delta^3 (arrow(p)-arrow(q))
$
and
$
  1 = integral dd(p, 3)/(2 pi)^3 1/(2 E_arrow(p)) ketbra(p)
$
some places define
$
  a^dagger (p) = sqrt(2 E_arrow(p)) a_arrow(p)^dagger
$
we don't care.

\*Complex Scalar Fields

== The Heisenberg Picture
$dots$
