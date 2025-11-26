//**** init-ting
#import "@preview/physica:0.9.5": *
#import "chpt-temp.typ": *
#import "@preview/mannot:0.3.0": *

#show: thmrules.with(qed-symbol: $square$)
#show: chpt-note.with()

= Interacting scalar theory
Thus far we have considered a free scalar theory:
$
  cal(L)_0 = 1/2 partial_mu phi.alt partial^mu phi.alt - V_0 (phi.alt)
$
with $V_0 (phi.alt) = 1/2 m_0^2 phi.alt^2$. It is necessarily a _boring_ theory in the sense that there are no interactions between particles. In QFT interactions are described by potentials $V(phi.alt)$ with higher order terms, formally
$
  V(phi.alt) = underbrace(1/2 m_0^2 phi.alt^2, V_0) + underbrace(1/3! g phi.alt^3 + 1/4! lambda phi.alt^4 + dots, V_"int")
$
leading us to write $cal(L)=cal(L)_0 + cal(L)_"int"$ with $cal(L)_"int" = - V_"int"$ and similarly $H=H_0 + H_"int"$. These additional terms have many consequences. First of all it changes our Hilbert space in multiple ways: The ground state $ket(Omega)$ of $H$ is different from the ground state $ket(0)$ of $H_0$---so our vacuum is different. The mass of the momentum eigenstates of $H$ is no longer the mass $m_0$ in $cal(L)_0$. And bound states may exists. Aside from this the additional terms lead to interactions.

The holy grail in QFT is to solve these non-free theories exactly---but this has only been possible for theories with sufficient symmetry. For this reason we typically resort to pertubation theory, given the couplings $g$ and $lambda$ are small allowing us to ignore higher order terms.

== Källén-Lehmann
We saw before how $P^mu$ generate spacetime translations, so if we have Lorentz invariance then $[P^mu,P^nu] = 0$ implying $[H, bold(p)] = 0$. As a consequence we can find a simultaneous eigenstates $ket(lambda_bold(p))$ such that
$
  H ket(lambda_(bold(p))) = E_p (lambda) ket(lambda_bold(p))";   " bold(P) ket(lambda_(bold(p))) = bold(p) ket(lambda_bold(p))
$
with $ket(lambda_bold(p)) ->^"Lorentz" overbrace(ket(lambda_0), "at rest")$. These states can be one-particle states $ket(1_bold(p))$ with $E_p = sqrt(bold(p)^2+m^2)$, bound states, or $N$-particle states made from one-particle or bound states. In this case $bold(p)$ is the center of mass momentum---with any of these being created from vacuum $ket(Omega)$. The difference being now
$
  (partial_mu partial^mu + m^2) phi.alt = underbrace(j, "current") eq.not 0
$
so we cannot simply expand $phi.alt(x)$ as a superposition of Fourier modes.

We will use completeness
$
  bb(1) = ketbra(Omega) + underbrace(sum_lambda, "all types of state") overbrace(integral dd(p, 3)/(2pi)^3 1/(2 E_p (lambda)), "c.o.m momentum of state") ketbra(lambda_bold(p))
$
to try and compute the Feynmann-propagator
$
  braket(Omega, T phi.alt(x) phi.alt(y), Omega)
$
first note (since $P^mu ket(Omega) = 0$)
$
  phi.alt(x) = e^(i x^mu P_mu) phi.alt(0) e^(-i x^mu P_mu) => braket(Omega, phi.alt(x), Omega)=overbrace(braket(Omega, phi.alt(0), Omega), "if" braket(Omega, phi.alt(0), Omega)=c "let" phi.alt -> phi.alt-c) = 0
$
now we compute
$
  braket(Omega, phi.alt(x) bb(1) phi.alt(y), Omega) &= sum_lambda integral dd(p, 3)/(2pi)^3 1/(2 E_p (lambda)) braket(Omega, phi.alt(x), lambda_bold(p)) braket(lambda_bold(p), phi.alt(y), Omega) \
  &= sum_lambda integral dd(p, 3)/(2pi)^3 1/(2 E_p (lambda)) underbrace(bra(Omega) e^(i P dot x), = bra(Omega)) phi.alt(0) underbrace(e^(- i P dot x) ket(lambda_bold(p)), ket(lambda_bold(p))e^(-i p dot x)) bra(lambda_bold(p)) e^(i P dot y) phi.alt(0) e^(-i P dot y) ket(Omega) \
  &= sum_lambda integral dd(p, 3)/(2pi)^3 1/(2 E_p (lambda)) e^(-i p dot (x - y)) abs(braket(Omega, phi.alt(0), lambda_bold(p)))^2
$
now we want to relate $ket(lambda_bold(p))$ to $ket(lambda_0)$.

#nte[

  Consider a scalar field transforming under a Lorentz transformation
  $
    x -> x' = Lambda x
  $
  the action of the Lorentz group can be represented in terms of some unitary operator $U(Lambda)$ such that
  $
    ket(alpha) -> ket(alpha') = U(Lambda) ket(alpha)
  $
  the scalar field then transforms like
  $
    phi.alt(x) -> phi.alt' (x') = phi.alt(x(x'))
  $
  with $phi.alt' (x') = U^(-1) (Lambda) phi.alt(x') U(Lambda)$ giving
  $
    U^(-1) (Lambda) phi.alt(x') U(Lambda) = phi.alt(x)
  $
  alternatively this is what we get from
  $
    underbrace(braket(alpha', phi.alt(x'), beta'), braket(alpha, U^(-1) phi.alt(x') U, beta)) = braket(alpha, phi.alt(x), beta)
  $
]

Then defining a boost such that $ket(lambda_bold(p)) = U^(-1) ket(lambda_0)$
$
  braket(Omega, phi.alt(0), lambda_bold(p)) &= underbrace(bra(Omega) U^(-1), bra(Omega)) underbrace(U phi.alt(0) U^(-1), phi.alt(0)) underbrace(U ket(lambda_bold(p)), ket(lambda_0))
$
giving
$
  braket(Omega, phi.alt(x)phi.alt(y), Omega) = sum_lambda integral dd(p, 3)/(2pi)^3 1/(2 E_p (lambda)) e^(-i p dot (x-y)) abs(braket(Omega, phi.alt(0), lambda_0))^2
$
comparing with the free scalar theory result we can obtain the time-ordered expression:
$
  markrect(braket(Omega, T phi.alt(x) phi.alt(y), Omega) = sum_lambda integral dd(p, 4)/(2pi)^4 i/(p^2-m_lambda^2 + i epsilon) e^(-i p dot (x-y)) abs(braket(Omega, phi.alt(0), lambda_0))^2, outset: #.3em)
$
or defining
$
  D_F (x-y\;M^2) &equiv integral dd(p, 4)/(2pi)^4 i/(p^2 - M^2 + i epsilon) e^(-i p dot (x-y)) \
  rho(M^2) &equiv sum_lambda 2 pi delta(M^2-m_lambda^2) abs(braket(Omega, phi.alt(0), lambda_0))^2
$
we can write
$
  braket(Omega, T phi.alt(x) phi.alt(y), Omega) = integral_0^oo dd(M^2)/(2 pi) rho(M^2) D_F (x-y\;M^2)
$
For a one-particle state it is clear that the spectral function $rho(M^2)$ is a single isolated $delta$-function at $M^2 = m^2$. So below $M^2 tilde (2m)^2$ or $M^2 tilde m_"bound"^2$ it takes the form
$
  rho(M^2) = 2 pi delta(M^2 - m^2) Z",   "Z equiv abs(braket(Omega, phi.alt(0), 1_0))^2
$
in particular consider the Fourier transformation
$
  integral dd(x, 4) e^(i p dot (x-y)) braket(Omega, T phi.alt(x) phi.alt(y), Omega)&= integral_0^oo dd(M^2)/(2 pi) rho(M^2) i/(p^2-M^2+ i epsilon) \
  &= underbrace((i Z)/(p^2 - m^2 + i epsilon), "one-particle state" #linebreak() "is first pole at" m^2) + integral_(m^2_"bound")^oo dd(M^2)/(2 pi) rho(M^2) i/(p^2-M^2+ i epsilon)
$
bound states then occur at higher isolated poles and $N$-particle states lead to a branch cut at $p^2 = 4 m^2$.

In the free theory $Z = 1$ since $phi.alt(0)$ creates a free particle from vacuum. In an interacting theory
$
  abs(braket(Omega, phi.alt(0), 1_0)) = sqrt(Z) < 1
$
since $phi.alt$ does not only create a one-particle state leading to a smaller overlap. One can formally prove that $Z= 1$ if and only if the theory is free.

== The S-matrix
We consider scattering of some incoming states $ket(i)$ to outgoing states $ket(f)$, with the aim being computing the probability amplitude for scattering of $ket(i)$ to $ket(f)$.

We assume that the initial and final states are asymptotically free. So at $t = -oo$ the states $ket(i", in")$ are described by the free theory---as they approach each other they interact, and scatter into $ket(f)$. Later at $t = oo$ they are again described by the free theory. This notion is formalised by $phi.alt_"in"$ and $phi.alt_"out"$.

The in-state $ket(i", in")$ is made from the asymptotic vacuum $ket("vac, in")$ using $phi.alt_"in"$ as $t->-oo$. We will find that $ket("vac, in") = ket(Omega)$. The state $ket(i", in")$ has energy $E= sqrt(p^2+m^2)$ with $m$ being the value of the one-particle pole in the Feynmann-propagator of the full theory. So $m eq.not m_0$ meaning $phi.alt_"in"$ is a free field satisfying
$
  (partial_mu partial^mu + m^2) phi.alt_"in" = 0
$
so we can expand $phi.alt_"in"$ as
$
  phi.alt_"in" (x) = integral dd(p, 3)/(2pi)^3 1/sqrt(2 E_p) (a_"in" (bold(p)) e^(-i p dot x) + a_"in"^dagger (bold(p))e^(i p dot x))
$
where $p^0 = sqrt(bold(p)^2+m^2)$.

As $t-> - oo$ we identify $phi.alt_"in" tilde phi.alt$ like the following: $phi.alt -> C phi.alt_"in"$ leading to $ braket(alpha, phi.alt, beta) -> sqrt(Z) braket(alpha, phi.alt_"in", beta)"  weakly" $ meaning this does not hold for powers of $phi.alt$---if it did one would have $Z = 1$. As $t -> +oo$ $phi.alt_"out"$ has analogous properties. So the fields $phi.alt_"out"$ and $phi.alt_"in"$ are free fields with the mass $m$ of the full theory. At $t -> minus.plus oo$ we only have self-interactions of the field, leading to $m eq.not m_0$ and $Z eq.not 1$.

Since $ket(i", in") tilde.equiv ket(i", out")$ there exists some operator $S: cal(H)_"out" -> cal(H)_"in"$ such that
$
  ket(i", in") = S ket(i", out")
$
this operator has many nice properties:
$
  S^dagger &= S^(-1) \
  phi.alt_"in" (x) &= S phi.alt_"out" (x) S^(-1) \
  ket("vac, in") &= ket("vac, out") = ket(Omega)";  " S ket(Omega) = ket(Omega)
$
we want to compute the transition amplitude
$
  braket(f", out", i", in") = braket(f", in", S, i", in")
$

== LSZ reduction formula
We want to compute the matrix element
$
  braket(p_1\, dots\, p_n", out", q_1\, dots\, q_r", in")
$
recall
$
  phi.alt_"in" (x) = integral dd(k, 3)/(2pi)^3 1/sqrt(2 E_k) (a_"in" (bold(k)) e^(-i k dot x) + a_"in"^dagger (bold(k))e^(i k dot x))
$
then by definition
$
  ket(q_i", in") = sqrt(2 E_q_i) a_"in"^dagger (q_i) ket(Omega)
$
we can invert the above to find expansions for $a_"in"$ and $a_"in"^dagger$ giving
$
  a_"in" (bold(q)) = i/sqrt(2 E_q) evaluated(integral dd(x, 3) e^(i q dot x) arrow.l.r(partial_0) phi.alt_"in" (x))_(x^0=t)
$
with the integral being evaluated at arbitrary time $t$. Then we can write
$
  braket(p_1\, dots\, p_n", out", q_1\,dots\,q_r", in") &= sqrt(2 E_q_1) braket(p_1\,dots\,p_n", out", a_"in"^dagger (bold(q)_1), q_2\,dots\,q_r", in") \
  &= 1/i evaluated(integral dd(x, 3) e^(-i q_1 dot x) arrow.r.l(partial_0) braket(p_1\,dots\,p_n", out", phi.alt_"in" (t,bold(x)), q_2\,dots\,q_r", in"))_(x^0=t)
$
taking $t -> - oo$ and using
$
  lim_(t->-oo) braket(1_bold(p), phi.alt_"in" (t,bold(x)), Omega) = lim_(t -> - oo) 1/sqrt(Z) braket(1_bold(p), phi.alt(t, bold(x)), Omega)
$
(which generalizes) we obtain
$
  & braket(p_1\,dots\,p_n", out", q_1\,dots\,q_r", in") \ &= lim_(t-> - oo) 1/sqrt(Z) underbrace(1/i integral dd(x, 3) e^(-i q_1 dot x) arrow.r.l(partial_0) braket(p_1\,dots\,p_n", out", phi.alt(x), q_2\,dots\,q_r", in"), equiv integral dd(x, 3) f(t,bold(x)))
$
now note
$
  &(lim_(t -> oo) - lim_(t-> - oo)) integral dd(x, 3) f(t,bold(x)) = underbrace(lim_(t_f -> oo) integral_(t_i -> -oo)^(t_f) dd(t) pdv(, t) integral dd(x, 3) f(t,bold(x)), equiv integral dd(x, 4) partial_0 f(x)) \
  &=> lim_(t-> -oo) integral dd(x, 3) f(t,bold(x)) = lim_(t-> + oo) integral dd(x, 3) f(t,bold(x)) - integral dd(x, 4) partial_0 f(x)
$
so defining
$
  B & equiv integral dd(x, 4) 1/sqrt(Z) partial_0 [e^(-i q_1 dot x) 1/i arrow.r.l(partial_0) braket(p_1\,dots\,p_n", out", phi.alt(x), q_2\,dots\,q_r", in")] \
  A & equiv lim_(t-> oo) integral dd(x, 3) 1/i e^(-i q_1 dot x) arrow.r.l(partial_0) underbrace(1/sqrt(Z) braket(p_1\,dots\,p_n", out", phi.alt(x), q_2\,dots\,q_r", in"), "for" t-> oo": " braket(p_1\,dots\,p_n", out", phi.alt_"out" (x), q_2\,dots\,q_r", in")) \
  &= braket(p_1\,dots\,p_n", out", a_"out"^dagger (bold(q)_1), q_2\,dots\,q_r", in") sqrt(2 E_q_1)
$
we can write $ braket(p_1\,dots\,p_n", out", q_1\,dots\,q_r", in") = A-B $

The $A$ term can be written as
$
  A = sum_(k=1)^n 2 E_p_k (2pi)^3 delta^((3)) (bold(p)_k-bold(q)_1) braket(p_1\,dots underbrace(\, hat(p)_k\,, "without")dots\,p_n", out", q_2\,dots\,q_r", in") \
$
to get this we commute $a_"out"^dagger$ past all $a_"out"$ giving $n$ terms with a respective $delta$-function (this describes a process where one of the ingoing and outgoing states are identical and do not scatter---a disconnected diagram). The $B$ term can be written as
$
  B &= i integral dd(x, 4) 1/sqrt(Z) partial_0 [e^(-i q_1 dot x) partial_0 expval(dots)- (partial_0 e^(-i q_1 dot x)) expval(dots)] \
  &=^"cross terms cancel" i integral dd(x, 4) 1/sqrt(Z) [e^(-i q_1 dot x) partial_0^2 expval(dots)-(partial_0^2 e^(-i q_1 dot x) expval(dots))]
$
now
$
  -partial_0^2 e^(-i q_1 dot x) = (q_1^0)^2 e^(-i q_1 dot x) = (q_1^2 + bold(q)_1^2) e^(-i q_1 dot x) = (m^2 - nabla^2) e^(-i q_1 dot x)
$
we integrate by parts twice (and using that boundary terms vanish at $plus.minus oo$)
$
  integral dd(x, 4) (m^2 - nabla^2) e^(-i q_1 dot x) expval(dots) =^"i.b.p" integral dd(x, 4) e^(-i q_1 dot x) (m^2 - nabla^2) expval(dots)
$
so we find
$
  B = - i 1/sqrt(Z) integral dd(x_1, 4) e^(-i q_1 dot x_1) (square_1 + m^2) braket(p_1\,dots\,p_n", out", phi.alt(x_1), q_2\,dots\,q_r", in")
$
We can write the $expval(dots)$ as
$
  expval(dots) &= sqrt(2 E_p_1) braket(p_2\, dots\, p_n\, "out", a_"out" (p_1) phi.alt (x_1), q_2\, dots\, q_r\, "in") \
  &= lim_(y_1^0 -> oo) i 1/sqrt(Z) integral dd(y_1, 3) e^(i p_1 dot y_1) arrow.l.r(partial)_(y_1^0) braket(p_2\, dots\, p_n\, "out", phi.alt(y_1) phi.alt(x_1), q_2\, dots\, q_r\, "in")
$
Now consider
$
  & lim_(t_f -> oo #linebreak() t_i -> - oo) integral_(t_i)^(t_f) dd(y_1^0) [pdv(, y_1^0) i 1/sqrt(Z) integral dd(y_1, 3) e^(i p_1 dot y_1) arrow.l.r(partial)_(y_1^0) braket(p_2\, dots\, p_n\, "out", T phi.alt(y_1) phi.alt(x_1), q_2\, dots\, q_r\, "in")] \
  &#h(1em) = lim_(y_1^0 -> oo) [i 1/sqrt(Z) integral dd(y_1, 3) e^(i p_1 dot y_1) arrow.l.r(partial)_(y_1^0) braket(p_2\, dots\, p_n\, "out", phi.alt(y_1) phi.alt(x_1), q_2\, dots\, q_r\, "in")] \
  &#h(1em) - underbracket(lim_(y_1^0 -> - oo) [i 1/sqrt(Z) integral dd(y_1, 3) e^(i p_1 dot y_1) arrow.l.r(partial)_(y_1^0) braket(p_2\, dots\, p_n\, "out", phi.alt(x_1) phi.alt(y_1), q_2\, dots\, q_r\, "in")], = sqrt(2 E_p_1) braket(p_2\, dots "out", phi.alt(x_1) a_"in" (bold(p)_1), q_2 \, dots "in"))
$
the last term is disconnected! The term on the LHS is the same as
$
  i 1/sqrt(Z) integral dd(y_1, 4) e^(i p_1 dot y_1) (square_(y_1)+m^2) braket(p_2\, dots\, p_n\, "out", T phi.alt(y_1) phi.alt(x_1), q_2\, dots\, q_r\, "in")
$
so we have found
$
  expval(dots) & = "disconnected" + i 1/sqrt(Z) integral dd(y_1, 4) (dots)
$
This can be repeated to until our in and out states become vacuum giving the Lehmann-Symanzik-Zimmermann reduction formula
$
  braket(p_1\, dots\,p_n\, "out", q_1\, dots\, q_r\, "in") &equiv braket(p_1\, dots\, p_n\, "in", S, q_1\, dots\, q_r\, "in") \
  &= (Sigma "disconnected terms") \ &+ (i/sqrt(Z))^(n+r) integral dd(y_1, 4) dots dd(y_n, 4) integral dd(x_1, 4) dots dd(x_r, 4) \
  &times exp[i(sum_(k=1)^n p_k dot y_k - sum_(l=1)^r q_l dot x_l)] \
  &times (square_(y_1) + m^2) dots (square_(x_1) + m^2) dots braket(Omega, T phi.alt(y_1) dots phi.alt (y_n) phi.alt(x_1) dots phi.alt (x_r), Omega)
$
