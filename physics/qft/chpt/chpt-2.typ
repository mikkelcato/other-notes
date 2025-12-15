//**** init-ting
#import "@preview/physica:0.9.5": *
#import "chpt-temp.typ": *

#show: thmrules.with(qed-symbol: $square$)
#show: chpt-note.with()

= The Klein-Gordon Field
Much of the following analysis does what is typically done when we want to quantize a field, namely promote the dynamical variables to operators and impose suitable commutation relations. As in _normal_ quantum mechanics everything will follow from these.

== Quantizing in the Schrödinger picture
We promote $phi.alt$ and $pi$ to operators, and impose the _continuous_ generalization of the usual canonical commutation relations
$
       [phi.alt (bold(x)), pi (bold(y))] & = i delta^((3)) (bold(x)-bold(y)) \
  [phi.alt (bold(x)), phi.alt (bold(y))] & = [pi (bold(x)),pi(bold(y))] = 0
$
for now $phi.alt$ and $pi$ are time-independent.

As is typical we now want the spectrum of our Hamiltonian. How we proceed is in no way obvious. We try writing the Klein-Gordon equation in Fourier space by expanding the classical Klein-Gordon field as
$
  phi.alt (bold(x),t) = integral dd(p, 3)/(2pi)^3 e^(i bold(p) dot bold(x)) phi.alt (bold(p),t)
$
with $phi.alt(bold(p))^* = phi.alt(-bold(p))$. Then the Klein-Gordon equation becomes
$
  [pdv(, t, 2) +(bold(p)^2 + m^2)] phi.alt (bold(p),t) = 0
$
this is the equation of motion for a harmonic oscillator with frequency
$
  omega_bold(p) = sqrt(bold(p)^2 + m^2)
$
This is nice because we know how to find the spectrum of the harmonic oscillator.

Recall the Hamiltonian
$
  H = 1/2 p^2 + 1/2 omega^2 phi.alt^2
$
we solve this by writing $phi.alt$ and $p$ in terms of the ladder operators
$
  phi.alt = 1/sqrt(2omega) (a + a^dagger)";  " p = -i sqrt(omega/2) (a-a^dagger)
$
from which everything follows.

We do the same trick, but treating each Fourier mode of the field as an independent oscillator. Then we can write
$
  phi.alt (bold(x)) &= integral dd(p, 3)/(2 pi)^3 1/sqrt(2 omega_bold(p)) (a_bold(p) e^(i bold(p) dot bold(x))+a_bold(p)^dagger e^(-i bold(p) dot bold(x))) \
  pi (bold(x)) &= integral dd(p, 3)/(2 pi)^3 (-i) sqrt(omega_bold(p)/2) (a_bold(p) e^(i bold(p) dot bold(x)) - a_bold(p)^dagger e^(-i bold(p) dot bold(x)))
$
in principle the inverse relations could now be derived. We could also write these as
$
  phi.alt (bold(x)) &= integral dd(p, 3)/(2 pi)^3 1/sqrt(2 omega_bold(p)) (a_bold(p) + a_(-bold(p))^dagger )e^(i bold(p) dot bold(x)) \
  pi(bold(x)) &= integral dd(p, 3)/(2pi)^3 (-i) sqrt(omega_bold(p)/2) (a_bold(p) - a_(-bold(p))^dagger) e^(i bold(p) dot bold(x))
$
The typical commutation relation for the ladder operators becomes
$
  [a_bold(p), a_bold(p)'^dagger] = (2 pi)^3 delta^((3)) (bold(p)-bold(p)')
$
from which
$
  [phi.alt (bold(x)), pi (bold(x)')] = i delta^((3)) (bold(x)-bold(x)')
$
follows.

We are now ready to write the Hamiltonian which becomes
$
  H &= integral dd(x, 3) integral dd(p, p', 3)/(2pi)^6 e^(i (bold(p)+bold(p)') dot bold(x)) {- sqrt(omega_bold(p) omega_bold(p)')/4 (a_bold(p)-a_(-bold(p))^dagger)(a_bold(p)' - a_(-bold(p)')^dagger) \
    &#h(15em) + (- bold(p) dot bold(p)' + m^2)/(4 sqrt(omega_bold(p) omega_bold(p)')) (a_bold(p) + a_(-bold(p))^dagger)(a_bold(p)' + a_(-bold(p)')^dagger) } \
  &= integral dd(p, 3)/(2 pi)^3 omega_bold(p) (a_bold(p)^dagger a_bold(p) + 1/2 [a_bold(p),a_bold(p)^dagger])
$
here the second term is disturbing since it is proportional to $delta(0)$ and therefore infinite. This is the zero-point energy so we expect it to appear and we will ignore it going forward.

Using this we can compute
$
  [H,a_bold(p)^dagger] = omega_bold(p) a_bold(p)^dagger";  " [H,a_bold(p)] = - omega_bold(p) a_bold(p)
$
We define the vacuum $ket(0)$ such that $a_bold(p) ket(0) = 0$ for all $bold(p)$. This state has energy $E = 0$ (after dropping the infinity). Any other energy eigenstate can be built by acting with creation operators on $ket(0)$. The state $a_bold(p)^dagger a_bold(q)^dagger dots ket(0)$ is an eigenstate of $H$ with energy $omega_bold(p) + omega_bold(q) + dots$. To see this consider
$
  H (a_bold(p)^dagger ket(0)) = omega_bold(p) a_bold(p)^dagger ket(0) + underbrace(a_bold(p)^dagger H ket(0), 0)
$

We can also find the total momentum operator
$
  bold(P) = - integral dd(x, 3) pi (bold(x)) nabla phi.alt (bold(x)) = integral dd(p, 3)/(2 pi)^3 bold(p) a_bold(p)^dagger a_bold(p)
$
then by an argument similar to the above the state $a_bold(p)^dagger ket(0)$ has momentum $bold(p)$. So $a_bold(p)^dagger$ creates momentum $bold(p)$ and energy $omega_bold(p) = sqrt(bold(p)^2 + m^2)$. Since these excitations are discrete it is natural to call them particles. We see that $omega_bold(p)$ is the energy of these particles, so moving forward we denote $omega_bold(p) = E_bold(p)$.

Consider the state
$
  a_bold(p)^dagger a_bold(q)^dagger ket(0)
$
since $a_bold(p)^dagger$ and $a_bold(q)^dagger$ commute this state is identical to the state
$
  a_bold(q)^dagger a_bold(p)^dagger ket(0)
$
so the states are symmetric under particle exchange. We can also have arbitrarily many particles in a single mode $bold(p)$. This tells us that Klein-Gordon particles are bosons.

We normalize vacuum such that $braket(0, 0) = 1$ and we normalize the one-particle states such that
$
  ket(bold(p)) = sqrt(2 E_bold(p)) a_bold(p)^dagger ket(0)
$
meaning
$
  braket(bold(p), bold(q)) = 2 E_bold(p) (2pi)^3 delta^((3)) (bold(p)-bold(q))
$
and ensuring Lorentz invariance. Given this normalization we must divide by $2 E_bold(p)$ in other places. As an example take the completeness relation for the one-particle states
$
  (bb(1))_"one-particle" = integral dd(p, 3)/(2 pi)^3 ket(bold(p)) 1/(2 E_bold(p)) bra(bold(p))
$
The measure
$
  integral dd(p, 3)/(2 pi)^3 1/(2 E_bold(p))
$
is Lorentz invariant and as a result we will see it everywhere. As an example take the state $phi.alt (bold(x)) ket(0)$
$
  phi.alt (bold(x)) ket(0) = integral dd(p, 3)/(2 pi)^3 1/(2 E_bold(p)) e^(-i bold(p) dot bold(x)) ket(bold(p))
$
we interpret this as a particle at position $bold(x)$. We can convince ourselves of this by computing
$
  braket(0, phi.alt (bold(x)), bold(p)) &= bra(0) integral dd(p', 3)/(2 pi)^3 1/sqrt(2 E_bold(p)') (a_bold(p)' e^(i bold(p)' dot bold(x)) + a_bold(p)'^dagger e^(-i bold(p)' dot bold(x))) sqrt(2 E_bold(p)) a_bold(p)^dagger ket(0) \
  &= e^(i bold(p) dot bold(x))
$
which we recognize as the position-space representation of the single-particle momentum state $ket(bold(p))$. We find $braket(bold(x), bold(p)) prop e^(i bold(p) dot bold(x))$ as we are used to.

== Quantizing in the Heisenberg picture
We proceed in the usual way making $phi.alt$ and $pi$ time-dependent by
$
  phi.alt (x) = e^(i H t) phi.alt (bold(x)) e^(-i H t)
$
and similarly for $pi (x)$.

The time dependence of these follows from the Heisenberg equation of motion
$
  pdv(, t) cal(O) = -i [cal(O),H]
$
we compute
$
  pdv(, t) phi.alt (x) &= - i [phi.alt (x), integral dd(x', 3) {1/2 pi^2 (bold(x)',t) + 1/2 (nabla phi.alt (bold(x)',t))^2 + 1/2 m^2 phi.alt^2 (bold(x)',t)} ] \
  &= - i/2 integral dd(x', 3) [phi.alt (x), pi^2 (bold(x)',t)] \
  &= -i/2 integral dd(x', 3) {i delta^((3)) (bold(x)-bold(x)') pi (bold(x)',t) + pi(bold(x)', t) i delta^((3)) (bold(x)-bold(x)')} \
  &= pi (x) \
  pdv(, t) pi (x) &= [pi (x) , integral dd(x', 3) {1/2 pi^2 (bold(x)',t) + underbrace(1/2 phi.alt (bold(x)',t) (- nabla^2 + m^2) phi.alt (bold(x)',t), "integration by parts")}] \
  &= (nabla^2 -m^2) phi.alt (x)
$
combining them we find
$
  pdv(, t, 2) phi.alt = (nabla^2 - m^2) phi.alt
$
which is the Klein-Gordon equation!

We would like to write these in terms of ladder operators. We have
$
    H a_bold(p) & = a_bold(p) (H- E_bold(p)) \
  H^n a_bold(p) & = a_bold(p) (H - E_bold(p))^n
$
for any $n$. A similar thing holds for $a_bold(p)^dagger$ giving
$
  e^(i H t) a_bold(p) e^(-i H t) = a_bold(p) e^(-i E_bold(p) t)";  " e^(i H t) a_bold(p)^dagger e^(-i H t) = a_bold(p)^dagger e^(i E_bold(p) t)
$
with these we find
$
  phi.alt (x) &= integral dd(p, 3)/(2 pi)^3 1/sqrt(2 E_bold(p)) (a_bold(p) e^(-i p dot x) + a_bold(p)^dagger e^(i p dot x)) \
  pi (x) &= pdv(, t) phi.alt (x)
$
where $p^0 = E_bold(p)$. These are quite nice and also satisfy the canonical commutation relations (same-time).

== Propagators and Causality
We define the propagator as
$
  D(x-y) equiv braket(0, phi.alt(x) phi.alt(y), 0)
$
with the reason for the name being obvious. To compute this we note that the only surviving term has $braket(0, a_bold(p) a_bold(q)^dagger, 0) = (2pi)^3 delta^((3)) (bold(p)-bold(q))$. We find
$
  D(x-y) &= integral dd(p, q, 3)/(2pi)^6 1/(2 sqrt(E_bold(p) E_bold(q))) e^(-i p dot x) e^(i q dot y) braket(0, a_bold(p) a_bold(q)^dagger, 0) \
  &= integral dd(p, q, 3)/(2pi)^3 1/(2 sqrt(E_bold(p) E_bold(q))) e^(-i (p dot x - q dot y)) delta^((3)) (bold(p)-bold(q)) \
  &= integral dd(p, 3)/(2pi)^3 1/(2 E_bold(p)) e^(-i p dot (x-y))
$
First consider $(x-y)^2 > 0$ (timelike). We can  take $x^0-y^0 = t$ and $bold(x)-bold(y) = 0$ for simplicity. Then
$
  D(x-y) &= (4 pi)/(2pi)^3 integral_0^oo dd(p) p^2/(2 sqrt(p^2+m^2)) e^(- i sqrt(p^2+m^2)t) \
  &= 1/(4 pi^2) integral_m^oo dd(E) sqrt(E^2-m^2) e^(-i E t) \
  &tilde^(t -> oo) e^(-i m t)
$
Now consider $(x-y)^2 < 0$ (spacelike). We can take $x^0 - y^0 = 0$ and $bold(x)-bold(y) = bold(r)$. Then
$
  D(x-y) &= integral dd(p, 3)/(2pi)^3 1/(2 E_bold(p)) e^(i bold(p) dot bold(r)) \
  &= 1/(2 pi)^2 integral_0^oo dd(p) p^2/(2 E_bold(p)) (e^(i p r) - e^(-i p r))/(i p r) \
  &= (-i)/(2 (2pi)^2 r) integral_(-oo)^oo dd(p) (p e^(i p r))/sqrt(p^2+m^2)
$
here we use
$
  integral dd(Omega) e^(i p r cos theta) = 4 pi (sin p r)/(p r)
$
This guy has branch cuts starting at $p = plus.minus i m$. We use a push contour in the upper-half plane with $rho = - i p$ giving
$
  D(x-y) & = 1/(4 pi^2 r) integral_m^oo dd(rho) (rho e^(- rho r))/sqrt(rho^2-m^2) \
         & tilde^(r -> oo) e^(-m r)
$
so both exponentially decay outside the lightcone.

For causality we care about the commutator
$
  [phi.alt (x), phi.alt (y)]
$
we compute
$
  [phi.alt (x), phi.alt (y)] &= integral dd(p, 3)/(2 pi)^3 1/(2 E_bold(p)) (e^(-i p dot (x-y)) - e^(i p dot (x-y))) \
  &= D(x-y) - D(y-x)
$
For $(x-y)^2 < 0$ they cancel since as above we can take $x^0 - y^0 = 0$ giving
$
  [phi.alt(x),phi.alt(y)] &= integral dd(p, 3)/(2pi)^3 1/(2 E_bold(p)) (e^(i bold(p) dot bold(r))-e^(-i bold(p) dot bold(r)))
$
now we simply flip $bold(p) -> - bold(p)$ in the second integral. Then since this guy is Lorentz invariant it is true for all $(x-y)^2 < 0$. This also immediately follows from the canonical commutation relations.

We find that causality is satisfied. By the above computation we see that the amplitude for a particle to propagate from $x -> y$ is cancelled by the amplitude for the same particle to propagate from $y -> x$. If we had a complex-valued scalar field we would find distinct particle and anti-particle excitations. In this case one would find that the amplitude for a particle to propagate from $x -> y$ is cancelled by the amplitude for the anti-particle to propagate from $y -> x$!

Since the commutator is a c-number we can write (assuming $x^0 > y^0$)
$
  braket(0, [phi.alt(x),phi.alt(y)], 0) &= integral dd(p, 3)/(2pi)^3 1/(2 E_bold(p)) (e^(-i p dot (x-y))- e^(i p dot (x-y))) \
  &= integral dd(p, 3)/(2 pi)^3 {1/(2 E_bold(p)) evaluated(e^(-i p dot (x-y)))_(p^0 = E_bold(p)) + 1/(-2 E_bold(p)) evaluated(e^(-i p dot (x-y)))_(p^0 = - E_bold(p))} \
  &=^(x^0 > y^0) integral dd(p, 3)/(2 pi)^3 integral dd(p^0)/(2 pi i) (-1)/(p^2 - m^2) e^(- i p dot (x-y))
$
in the last step we apply the residue theorem in reverse. To do the $p^0$ integral we avoid the poles at $p^0 = plus.minus E_bold(p)$ by small $epsilon$-semicircles in the upper-half plane. The final contour is achieved by closing in the lower-half plane which ensures $e^(-i p dot (x-y)) -> 0$ as $p^0 -> -i oo$, picking up both poles. So going backwards we have
$
  1/(p^2-m^2) = 1/((p^0-E_bold(p))(p^0+E_bold(p)))
$
the residues are
$
  p^0 = plus.minus E_bold(p) -> plus.minus 1/(2 E_bold(p))
$
so the $p^0$ integral gives
$
  I = (-2 pi i) 1/(2pi i) {underbrace((-e^(-i E_bold(p) (x^0-y^0) + i bold(p) dot bold(r)))/(2 E_bold(p)), p^0 = +E_bold(p)) + underbrace((-e^(+i E_bold(p) (x^0-y^0) + i bold(p) dot bold(r)))/(-2 E_bold(p)), p^0 = - E_bold(p))}
$
so the entire integral is
$
  integral dd(p, 3)/(2pi)^3 {1/(2 E_bold(p)) evaluated(e^(- i p dot (x-y)))_(p^0 = E_bold(p)) + 1/(-2E_bold(p)) evaluated(e^(-i p dot (x-y)))_(p^0 = - E_bold(p))}
$
so everything check out. For $x^0 < y^0$ we instead close the contour in the upper-half plane picking up no poles, so the integral vanishes. All in all with this contour we have
$
  D_R (x-y) equiv Theta (x^0-y^0) braket(0, [phi.alt(x),phi.alt(y)], 0)
$
one can show this is the Green's function for the Klein-Gordon equation
$
  (partial_mu partial^mu + m^2) D_R (x-y) = -i delta^((4)) (x-y)
$
since $x^0 < y^0$ this is called the retarded Green's function. Due to this we could have found the previous expression by writing
$
  D_R (x-y) = integral dd(p, 4)/(2 pi)^4 e^(-i p dot (x-y)) tilde(D)_R (p)
$
giving the equation
$
  (-p^2 + m^2) tilde(D)_R (p) = - i
$
which rearranges to the wanted expression.

As should be clear we can compute the $p^0$ integral using four different contours (giving all Green's functions). The most useful is obtained by avoiding the pole at $- E_bold(p)$ by an $epsilon$-semicircle in the lower-half plane, and avoiding the pole at $+ E_bold(p)$ by an $epsilon$-semicircle in the upper-half plane. This gives what we call the Feynman propagator
$
  D_F (x-y) equiv integral dd(p, 4)/(2 pi)^4 i/(p^2-m^2 + i epsilon) e^(-i p dot (x-y))
$
since the  contour is equivalent to displacing the poles as $p^0 = plus.minus (E_bold(p) - i epsilon)$. For $x^0 > y^0$ the $p^0$ integral can be closed in the upper-half plane giving exactly $D(x-y)$, while for $x^0 < y^0$ it can be closed in the lower-half plane giving $D(y-x)$. So
$
  D_F (x-y) &= cases(D(x-y) " for" x^0 > y^0, D(y-x) " for" x^0 < y^0) \
  &= Theta(x^0-y^0) braket(0, phi.alt(x) phi.alt(y), 0) + Theta(y^0-x^0) braket(0, phi.alt(y) phi.alt(x), 0) \
  &equiv braket(0, T phi.alt(x) phi.alt (y), 0)
$
with $T$ being the time-ordering operator.

We now quickly show that this prescription gives the desired propagators. Consider $x^0 > y^0$ then
$
  1/((p^0 - E_bold(p))(p^0+E_bold(p)))
$
in this case we close our contour in the lower-half plane, picking up just the pole at $p^0 = + E_bold(p)$. So
$
  I & = integral dd(p^0)/(2 pi i) (-1)/(p^2 - m^2) e^(-i p dot (x-y)) \
    & = (-2 pi i) (-1)/(2pi i) [1/(2 E_bold(p)) e^(-i p dot (x-y))] \
    & = e^(-i p dot (x-y))/(2 E_bold(p))
$
giving
$
  I & = integral dd(p, 3)/(2 pi)^3 1/(2 E_bold(p)) e^(-i p dot (x-y)) \
    & = D(x-y)
$
For $x^0 < y^0$ we close above picking up the pole at $p^0 = - E_bold(p)$ giving
$
  I &= integral dd(p, 3)/(2 pi)^3 1/(2 E_bold(p)) e^(i E_bold(p) (x^0-y^0) + i bold(p) dot bold(r)) \
  &= integral dd(p, 3)/(2 pi)^3 1/(2 E_bold(p)) e^(-i E_bold(p) (y^0-x^0) - i bold(p) dot (bold(y)-bold(x))) \
  &=^(bold(p)->-bold(p)) integral dd(p, 3)/(2pi)^3 1/(2 E_bold(p)) e^(-i E_bold(p) (y^0-x^0) + i bold(p) dot (bold(y)-bold(x))) \
  &= D(y-x)
$
which is nice. We will get very intimate with $D_F (x-y)$ later.

For completeness we show that
$
  D(x-y) = integral dd(p, 3)/(2 pi)^3 1/(2 E_bold(p)) e^(-i p dot (x-y))
$
for spacelike $(x-y)$ with $(x-y)^2 = -r^2$ can be written in terms of Bessel functions. We can write
$
  D(bold(r)) &= integral dd(p, 3)/(2 pi)^3 1/(2 E_bold(p)) e^(i bold(p) dot bold(r)) \
  &= (4 pi)/(2 pi)^3 integral_0^oo dd(p) 1/(2 sqrt(p^2 + m^2)) p^2 (sin p r)/(p r) \
  &= 1/(4 pi^2 r) integral_0^oo dd(p) (p sin p r)/(sqrt(p^2 + m^2)) \
  &= m/(4 pi^2 r) K_1 (m r)
$
