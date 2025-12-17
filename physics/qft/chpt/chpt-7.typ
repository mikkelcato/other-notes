//**** init-ting
#import "@preview/physica:0.9.7": *
#import "chpt-temp.typ": *
#import "@preview/wicked:0.1.1": *

#show: thmrules.with(qed-symbol: $square$)
#show: chpt-note.with()


#let feyn(body) = math.cancel(angle: 15deg, body)

= Functional methods
== in Quantum mechanics
Consider the Hamiltonian
$
  H = p^2/(2 m) + V(x)
$
We want to compute the amplitude
$
  U(x_a, x_b; T) = braket(x_b, exp(- (i H T)/hbar), x_a)
$
We write this as
$
  U(x_a,x_b;T) & = sum_"all paths" e^(i dot ("phase")) \
  & = underbracket(integral dd(x(t), d: cal(D)), "short-hand") e^(i dot ("phase"))
$
so we write the amplitude of any given path as a pure phase. Any function $x(t)$ specifies a path $x_a -> x_b$. The integrand maps $x(t)$ to an amplitude so it is a functional.

We now need to find the phase. Taking the classical limit $hbar -> 0$ we should be able to determine the phase by requiring it is stationary
$
  dv(, x(t), d: delta) e^(i dot ("phase")) = 0 => dv(, x(t), d: delta) evaluated(("phase"[x(t)]))_x_"cl" = 0
$
since rapidly oscillating phases cancel. Then by the principle of least action we know
$
  dv(, x(t), d: delta) evaluated((S[x(t)]))_x_"cl" = 0
$
motivating the identification $("phase") tilde S$. This makes us write
$
  braket(x_b, exp(- (i H T)/hbar), x_a) = integral dd(x(t), d: cal(D)) e^(i S[x(t)]\/hbar)
$
which is quite nice! This is a heuristic argument, now we want to define $integral dd(x(t), cal(D))$.

Consider a general system described by coordinates $q^i$ and conjugate momenta $p^i$ with the Hamiltonian $H (q,p)$. We want to compute ($hbar = 1$)
$
  U(q_a,q_b;T) = braket(q_b, e^(-i H T), q_a)
$
We write
$
  e^(-i H T) = underbracket(e^(-i H epsilon.alt) e^(-i H epsilon.alt) dots e^(-i H epsilon.alt), N "factors")
$
and insert
$
  bb(1) = (product_i integral dd(q_k^i)) ketbra(q_k)
$
between each factor. Then we get factors of the form
$
  braket(q_(k+1), e^(-i H epsilon.alt), q_k) -->_(epsilon.alt -> 0) braket(q_(k+1), (1- i H epsilon.alt + dots), q_k)
$
We define $q_0 = q_a$ and $q_N = q_b$.

We now consider which terms $H$ can contain. The simplest terms are of the form $f(q)$ giving
$
  braket(q_(k+1), f(q), q_k) &= f(q_k) product_i delta (q_k^i - q_(k+1)^i) \
  &=^"rewriting" f((q_(k+1) + q_k)/2) (product_i integral dd(p_k^i)/(2 pi)) exp[i sum_i p_k^i (q_(k+1)^i - q_k^i)]
$
Consider a term of the form $f(p)$. We insert a set of momentum eigenstates to find
$
  braket(q_(k+1), f(p), q_k) = (product_i integral dd(p_k^i)/(2 pi)) f(p_k) exp[i sum_i p_k^i (q_(k+1)^i - q_k^i)]
$
Then if $H$ only contains these types of terms we can write
$
  braket(q_(k+1), H(q,p), q_k) = (product_i integral dd(p_k^i)/(2 pi)) H((q_(k+1) + q_k)/2, p_k) exp[i sum_i p_k^i (q_(k+1)^i -q_k^i)]
$
This would be nice if it were true for all $H(q,p)$ but since operator order matters we need to be careful. We assume the Hamiltonian is _Weyl-ordered_ meaning symmetric in $q$ and $p$. As an example consider
$
  braket(q_(k+1), 1/4 (q^2 p^2 + 2 q p^2 q + p^2 q^2), q_k) = ((q_(k+1)+q_k)/2)^2 braket(q_(k+1), p^2, q_k)
$
so the order turns out to not be important! Any Hamiltonian can be written in this form through commutation relations. This will however introduce additional terms.

For a Weyl-ordered Hamiltonian we have
$
  braket(q_(k+1), e^(-i epsilon.alt H), q_k) &= (product_i integral dd(p_k^i)/(2 pi)) exp[-i epsilon.alt H ((q_(k+1) + q_k)/2, p_k)] \
  &#h(6.3em) times exp[i sum_i p_k^i (q_(k+1)^i - q_k^i)]
$
Then we multiply $N$ of these factors and integrate over $q_k$
$
  U(q_0,q_N;T) &= (product_(i, k) integral dd(q_k^i) integral dd(p_k^i)/(2 pi)) \
  & times exp[i sum_k {sum_i p_k^i (q_(k+1)^i - q_k^i) - epsilon.alt H((q_(k+1) + q_k)/2,p_k)}]
$
This is the discretized form of
$
  U(q_a,q_b;T) = (product_i integral dd(q(t), p(t), d: cal(D))) exp[i integral_0^T dd(t) (sum_i p^i dot(q)^i - H(q,p))]
$
which is the functional integral! Here the $q(t)$ are fixed at the endpoints and the measure is just
$
  product_i integral dd(q^i, p^i)/(2 pi hbar)
$

== Functional quantization of a scalar field
We apply the above to a real scalar field $phi.alt (x)$. The expression above holds for any quantum system so it should also apply to a quantum field theory.

The $q^i$ are $phi.alt (bold(x))$ and the Hamiltonian is
$
  H = integral dd(x, 3) [1/2 pi^2 + 1/2 (nabla phi.alt)^2 + V(phi.alt)]
$
so we find
$
  braket(phi.alt_b (bold(x)), e^(-i H T), phi.alt_a (bold(x))) = integral dd(phi.alt, pi, d: cal(D)) exp[i integral_0^T dd(x, 4) (pi dot(phi.alt) - 1/2 pi^2 - 1/2 (nabla phi.alt)^2 - V(phi.alt))]
$
where $x^0 = 0$ for $phi.alt_a$ and $x^0 = T$ for $phi.alt_b$. We can complete the square and evaluate $integral dd(pi, d: cal(D))$ giving
$
  braket(phi.alt_b, e^(-i H T), phi.alt_a) = integral dd(phi.alt, d: cal(D)) exp[i integral_0^T dd(x, 4) cal(L)]
$
where
$
  cal(L) = 1/2 partial_mu phi.alt partial^mu phi.alt - V(phi.alt)
$
We see that any explicit symmetries of the Lagrangian are preserved by the functional integral! These are very important to physics so we take the Lagrangian as the central object and the above as the defining equation for the Hamiltonian. We will find that the Hamiltonian formulation becomes irrelevant.

Consider the object
$
  integral dd(phi.alt(x), d: cal(D)) phi.alt (x_1) phi.alt (x_2) exp[i integral_(-T)^T dd(x, 4) cal(L) (phi.alt)]
$
with $phi.alt(-T, bold(x)) = phi.alt_a (bold(x))$ and $phi.alt(T, bold(x)) = phi.alt_b (bold(x))$. We break up the integral as
$
  integral dd(phi.alt (x), d: cal(D)) = integral dd(phi.alt_1 (bold(x)), d: cal(D)) integral dd(phi.alt_2 (bold(x)), d: cal(D)) integral_(phi.alt(x_1^0, bold(x)) = phi.alt_1 (bold(x)) #linebreak() phi.alt(x_2^0, bold(x))=phi.alt_2 (bold(x))) dd(phi.alt(x), d: cal(D))
$
Then we obtain for $x_1^0 < x_2^0$
$
  &integral dd(phi.alt_1 (bold(x)), d: cal(D)) integral dd(phi.alt_2 (bold(x)), d: cal(D)) phi.alt_1 (bold(x)_1) phi.alt_2 (bold(x)_2) braket(phi.alt_b, e^(-i H (T-x_2^0)), phi.alt_2) \
  &#h(7em) times braket(phi.alt_2, e^(-i H (x_2^0-x_1^0)), phi.alt_1) braket(phi.alt_1, e^(-i H (x_1^0+ T)), phi.alt_a)
$
We now use $phi.alt_S (bold(x)_1) ket(phi.alt_1) = phi.alt_1 (bold(x)_1) ket(phi.alt_1)$ and $integral dd(phi.alt_1, d: cal(D)) ketbra(phi.alt_1) = bb(1)$ to obtain
$
  braket(phi.alt_b, e^(-i H (T-x_2^0)) phi.alt_S (bold(x)_2) e^(-i H (x_2^0-x_1^0)) phi.alt_S (bold(x)_1) e^(-i H (x_1^0+T)), phi.alt_a)
$
The $phi.alt_S$ combine to give $phi.alt_H$ and for $x_1^0 > x_2^0$ the order swaps so
$
  braket(phi.alt_b, e^(-i H T) T{phi.alt_H (x_1) phi.alt_H (x_2)} e^(-i H T), phi.alt_a)
$
As we did originally we take the limit $T -> oo (1- i epsilon.alt)$ projecting out $ket(Omega)$ and we find doing the same manipulations
$
  braket(Omega, T phi.alt_H (x_1) phi.alt_H (x_2), Omega) = lim_(T -> oo (1- i epsilon.alt)) (integral dd(phi.alt, d: cal(D)) phi.alt (x_1) phi.alt (x_2) exp[i integral_(-T)^T dd(x, 4) cal(L)])/(integral dd(phi.alt, d: cal(D)) exp[i integral_(-T)^T dd(x, 4) cal(L)])
$
which is very similar to what we found before!

== Generating functional
We define the _functional derivative_ $delta\/dd(J(x), d: delta)$ by
$
  dv(, J(x), d: delta) J(y) = delta^((4)) (x-y)";   " dv(, J(x), d: delta) integral dd(y, 4) J(y) phi.alt (y) = phi.alt (x)
$
to take functional derivative we simply apply normal derivative rules. As an example
$
  dv(, J(x), d: delta) exp[i integral dd(y, 4) J(y) phi.alt (y)] = i phi.alt (x) exp[i integral dd(y, 4) J(y) phi.alt (y)]
$
where we use the chain rule and the second defintion. When the functional depends on derivatives of $J$ we need to integrate by parts before applying the functional derivative
$
  dv(, J(x), d: delta) integral dd(y, 4) partial_mu J(y) V^mu (y) = - partial_mu V^mu (x)
$
The basic object we care about is the _generating functional_ $Z[J]$. For a scalar field theory this guy is defined as
$
  Z[J] equiv integral dd(phi.alt, d: cal(D)) exp[i integral dd(x, 4) {cal(L)+J(x) phi.alt (x)}]
$
this is the path integral with an additional source term
$
  cal(L) tilde cal(L)_0 + J phi.alt
$
Then we can compute correlation functions by
$
  braket(0, T phi.alt (x_1) phi.alt (x_2), 0) = 1/Z_0 evaluated((-i dv(, J(x_1), d: delta)) (-i dv(, J(x_2), d: delta)) Z[J])_(J = 0)
$
where $Z_0 = Z[J=0]$.

Consider
$
  integral dd(x, 4) {cal(L)_0 (phi.alt) + J phi.alt} = integral dd(x, 4) {1/2 phi.alt (- partial^2 - m^2 + i epsilon.alt) phi.alt + J phi.alt}
$
we shift $phi.alt$ by
$
  phi.alt' (x) equiv phi.alt (x) - i integral dd(y, 4) D_F (x-y) J(y)
$
Then
$
  integral dd(x, 4) {cal(L)_0 (phi.alt) + J phi.alt} &= integral dd(x, 4) {1/2 phi.alt' (-partial^2 - m^2 + i epsilon.alt) phi.alt'} \ & - integral dd(x, y, 4) 1/2 J(x) {-i D_F (x-y)} J(y)
$
meaning
$
  Z[J] &= integral dd(phi.alt', d: cal(D)) exp[i integral dd(x, 4) cal(L)_0 (phi.alt')] exp[-i integral dd(x, y, 4) 1/2 J(x) {-i D_F (x-y)} J(y)] \
  &equiv Z_0 exp[-1/2 integral dd(x, y, 4) J(x) D_F (x-y) J(y)]
$
which is quite nice!

As an example consider
$
  braket(0, T phi.alt (x_1) phi.alt (x_2), 0) &= - dv(, J(x_1), d: delta) dv(, J(x_2), d: delta) evaluated(exp[-1/2 integral dd(x, y, 4) J(x) D_F (x-y) J(y)])_(J = 0) \
  &= - dv(, J(x_1), d: delta) [-1/2 integral dd(y, 4) D_F (x_2-y) J(y) - 1/2 integral dd(x, 4) J(x) D_F (x-x_2)] evaluated(Z(J)/Z_0)_(J=0) \
  &= D_F (x_1-x_2)
$
And
$
  braket(0, T phi.alt_1 phi.alt_2 phi.alt_3 phi.alt_4, 0) &= dv(, J_1, d: delta) dv(, J_2, d: delta) dv(, J_3, d: delta) [- J_x D_(x 4)] evaluated(e^(-1/2 J_x D_(x y) J_y))_(J=0) \
  &= dv(, J_1, d: delta) dv(, J_2, d: delta) (- D_34 + J_x D_(x 4) J_y D_(y 3)) evaluated(e^(-1/2 J_x D_(x y) J_y))_(J=0) \
  &= dv(, J_1, d: delta) [D_34 J_x D_(x 2) + D_24 J_y D_(y 3) + J_x D_(x 4) + D_23] evaluated(e^(-1/2 J_x D_(x y) J_y))_(J=0) \
  &= D_34 D_12 + D_24 D_13 + D_14 D_23
$
where we integrate over repeated indices.

== Statistical mechanics
There is an important correspondence between statistical mechanics and the funtional approach we have developed.

Above we found
$
  Z[J] = integral dd(phi.alt, d: cal(D)) exp[i integral dd(x, 4) {cal(L)+ J phi.alt}]
$
which gives correlation functions by taking functional derivatives.

We do a _Wick rotation_ taking $t -> - i x^0$ meaning
$
  x^2 -> - abs(x_E)^2
$
then
$
  Z[J] = integral dd(phi.alt, d: cal(D)) exp[- integral dd(x_E, 4) {cal(L)_E - J phi.alt}] tilde "partition function"
$
so it is a partition function!
