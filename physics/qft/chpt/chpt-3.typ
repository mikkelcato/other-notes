//**** init-ting
#import "@preview/physica:0.9.7": *
#import "chpt-temp.typ": *
#import "@preview/wicked:0.1.1": *

#show: thmrules.with(qed-symbol: $square$)
#show: chpt-note.with()

= The Dirac Field
Now that we have looked at the simplest possible field theory we move on to the next simplest: the Dirac field.

== The Lorentz algebra
So far we have only considered scalar fields which under a Lorentz transformation $ x^mu -> (x')^mu = tensor(Lambda, mu, -nu) x^mu $ transform as
$
  phi.alt (x) -> phi.alt' (x) = phi.alt (Lambda^(-1) x)
$
in a sense they transform trivially. Naturally we invoke new physics by considering fields that transform non-trivially under the Lorentz group.

A familiar example which transforms non-trivially under the Lorentz group is the vector field $A^mu (x)$ of electromagnetism
$
  A^mu (x) -> tensor(Lambda, mu, -nu) A^nu (Lambda^(-1) x)
$
using this guy we can construct the invariant Lagrangian
$
  cal(L)_"Maxwell" = - 1/4 F_(mu nu) F^(mu nu)
$
which is invariant due to all indices contracting. A family of similar invariant Lagrangians can also be constructed in this manner.

We would like to find all possible invariant expressions. This necessarily requires a method to figure out how different fields transform under the Lorentz group. This amounts to finding different representations of the Lorentz group. Generally a field transforms as
$
  phi.alt^alpha (x) -> tensor(D[Lambda], alpha, -beta) phi.alt^beta (Lambda^(-1) x)
$
with the matrices $D[Lambda]$ forming a representation of the Lorentz group, meaning
$
  D[Lambda_1] D[Lambda_2] & = D[Lambda_1 Lambda_2] " with " D[Lambda^(-1)] = D[Lambda]^(-1)",  "D[bb(1)] = bb(1)
$
So the matrices $D[Lambda]$ respect the group structure of the Lorentz group, i.e. they are a group homomorphism.

To find the representations we typically consider infinitesimal transformations of the Lorentz group and the corresponding Lie algebras. We write
$
  tensor(Lambda, mu, -nu) = tensor(delta, mu, -nu) + tensor(theta, mu, -nu)
$
for infinitesimal $theta$. By the defining condition $tensor(Lambda, mu, -sigma) tensor(Lambda, nu, -rho) eta^(sigma rho) = eta^(mu nu)$ we find that $theta$ must be anti-symmetric
$
  theta^(mu nu) + theta^(nu mu) =^! 0
$
Since $theta$ has six independent components (due to being a $4 times 4$ anti-symmetric matrix) we introduce the basis $tensor((M^(rho sigma)), mu, -nu)$ with  $rho, sigma = 0, dots 3$ and $[rho sigma]$ being anti-symmetric. With this notation we can write
$
  (M^(rho sigma))^(mu nu) = eta^(rho mu) eta^(sigma nu) - eta^(sigma mu) eta^(rho nu)
$
where $[rho sigma]$ indicating which basis matrix we are dealing with and $[mu nu]$ are those of the $4 times 4$ matrix. Typically we need one index lowered giving
$
  tensor((M^(rho sigma)), mu, -nu) = eta^(rho mu) tensor(delta, sigma, -nu) - eta^(sigma mu) tensor(delta, rho, -nu)
$
Now any $tensor(theta, mu, -nu)$ can be expanded as
$
  tensor(theta, mu, -nu) = 1/2 omega_(rho sigma) tensor((M^(rho sigma)), mu, -nu)
$
where $omega_(rho sigma)$ are six anti-symmetric numbers telling us which Lorentz transformation we  are doing. The basis matrices $M^(rho sigma)$ are called the _generators_ of the Lorentz transformations. The generators obey the Lorentz Lie algebra
$
  [M^(rho sigma), M^(tau nu)] = eta^(sigma tau) M^(rho nu) - eta^(rho tau) M^(sigma nu) + eta^(rho nu) M^(sigma tau) - eta^(sigma nu) M^(rho tau)
$
Any finite Lorentz transformation can then be written as the exponential
$
  Lambda = exp(1/2 omega_(rho sigma) M^(rho sigma))
$
in Peskin & Schroeder they make the generators Hermitian by defining $J^(mu nu) = i M^(mu nu)$. Giving
$
  Lambda = exp(-i/2 omega_(rho sigma) J^(rho sigma))
$
this naturally also flips the signs in the Lie algebra and a factor of $i$.

== The spinor representation
We would now like to find other matrices satisfying the Lorentz algebra. We will construct the spinor representation. We start by considering the Clifford (or Dirac) algebra
$
  {gamma^mu, gamma^nu} equiv gamma^mu gamma^nu + gamma^nu gamma^mu = 2 eta^(mu nu) bb(1)_(n times n)
$
where $gamma^mu$ are four $n times n$ matrices. We see immediately that
$
  gamma^mu gamma^nu = - gamma^nu gamma^mu " when " mu eq.not nu
$
and
$
  (gamma^0)^2 & = 1 \
  (gamma^i)^2 & = - 1
$
The simplest representation of the Clifford algebra is in terms of $4 times 4$ matrices. There are many such examples, but all are unitarily equivalent. For this reason we pick the very convenient representation
$
  gamma^0 = mat(0, 1; 1, 0)";  " gamma^i = mat(0, sigma^i; -sigma^i, 0)
$
this is the Weyl or _chiral_ representation and the $sigma^i$ are as usual the Pauli matrices satisfying ${sigma^i, sigma^j} = 2 delta^(i j)$.

Now consider
$
  S^(mu nu) & = i/4 [gamma^mu, gamma^nu] = i/2 ( gamma^mu gamma^nu - eta^(mu nu))
$
then
$
  [S^(mu nu), gamma^rho] &=^(mu eq.not nu) i/2 [gamma^mu gamma^nu, gamma^rho] = i/2 gamma^mu gamma^nu gamma^rho - i/2 gamma^rho gamma^mu gamma^nu \
  &= i/2 gamma^mu {gamma^nu, gamma^rho} - i/2 gamma^mu gamma^rho gamma^nu - i/2 {gamma^rho,gamma^mu} gamma^nu + i/2 gamma^mu gamma^rho gamma^nu \
  &= i (gamma^mu eta^(nu rho) - gamma^nu eta^(rho mu)) \
  &=^? - tensor((J^(mu nu)), rho, -sigma) gamma^sigma
$
and importantly the matrices $S^(mu nu)$ form a representation of the Lorentz algebra, meaning
$
  [S^(mu nu), S^(rho sigma)] &=^(rho eq.not sigma) i/2 [S^(mu nu), gamma^rho gamma^sigma] \
  &= i/2 [S^(mu nu), gamma^rho] gamma^sigma + i/2 gamma^rho [S^(mu nu), gamma^sigma] \
  &= -1/2 gamma^mu gamma^sigma eta^(nu rho) + 1/2 gamma^nu gamma^sigma eta^(rho mu) - 1/2 gamma^rho gamma^mu eta^(nu sigma) + 1/2 gamma^rho gamma^nu eta^(sigma mu)
$
now using $gamma^mu gamma^sigma = -2i S^(mu sigma) + eta^(mu sigma)$ gives
$
  [S^(mu nu), S^(rho sigma)] &= -1/2 (-2 i S^(mu sigma)+eta^(mu sigma)) eta^(nu rho) +1/2 (-2 i S^(nu sigma) + eta^(nu sigma)) eta^(rho mu) \ &#h(1em)- 1/2 (-2 i S^(rho mu) + eta^(rho mu)) eta^(nu sigma) + 1/2 (-2i S^(rho nu) + eta^(rho nu)) eta^(sigma mu) \
  &= i (eta^(nu rho) S^(mu sigma) - eta^(mu rho) S^(nu sigma) - eta^(nu sigma) S^(mu rho) + eta^(mu sigma) S^(nu rho))
$
which is the Lorentz algebra.

Now we just need the field that $tensor((S^(mu nu)), alpha, -beta)$ acts on. We introduce the Dirac _spinor_ $psi^alpha (x)$, an object with four complex components denoted by $alpha = 1,dots 4$. Under Lorentz transformations we then have
$
  psi^alpha (x) -> tensor(S[Lambda], alpha, -beta) psi^beta (Lambda^(-1) psi)
$
with
$
     Lambda & = exp(-i/2 omega_(rho sigma) J^(rho sigma)) \
  S[Lambda] & = exp(-i/2 omega_(rho sigma) S^(rho sigma))equiv Lambda_(1\/2)
$
note we use the same $omega_(rho sigma)$ to specify the specific transformation.

We quickly show
$
  S[Lambda]^(-1) gamma^mu S[Lambda] & = tensor(Lambda, mu, -nu) gamma^nu
$
the LHS is
$
  S[Lambda]^(-1) gamma^mu S[Lambda] & = (1+i/2 omega_(rho sigma) S^(rho sigma) ) gamma^mu (1-i/2 omega_(rho sigma) S^(rho sigma)) \
  &= gamma^mu + i/2 omega_(rho sigma) S^(rho sigma) gamma^mu - i/2 omega_(rho sigma) gamma^mu S^(rho sigma) + dots \
  &= gamma^mu + i/2 omega_(rho sigma) [S^(rho sigma), gamma^mu]
$
and the RHS is
$
  gamma^mu-i/2 omega_(rho sigma) J^(rho sigma) gamma^mu + dots
$
so we must have
$
  [S^(rho sigma), gamma^mu] = - J^(rho sigma) gamma^mu
$
this is exactly what we showed previously.

== The Dirac equation
We want to find an invariant equation of motion for the Dirac spinor $psi$. We do this by constructing an invariant action. We define the adjoint $psi^dagger (x) = (psi^*)^TT (x)$. Under a Lorentz transformation
$
          psi(x) & -> S[Lambda] psi(Lambda^(-1) x) \
  psi^dagger (x) & -> psi^dagger (Lambda^(-1) x) S[Lambda]^dagger
$
in the Dirac representation we also have $(gamma^0)^dagger = gamma^0$ and $(gamma^i)^dagger = - gamma^i$. Then
$
  gamma^0 gamma^mu gamma^0 = (gamma^mu)^dagger
$
since $gamma^i gamma^0 = - gamma^0 gamma^i$. This means
$
  (S^(mu nu))^dagger & = -i/4 [(gamma^nu)^dagger, (gamma^mu)^dagger] \
                     & = -i/4 gamma^0 [gamma^nu,gamma^mu] gamma^0 \
                     & = -gamma^0 S^(mu nu) gamma^0
$
so
$
  S[Lambda]^dagger = exp(i/2 omega_(rho sigma) (S^(rho sigma))^dagger) = gamma^0 S[Lambda]^(-1) gamma^0
$
to apply this we define the Dirac adjoint
$
  overline(psi) = psi^dagger gamma^0
$
Then $overline(psi) psi$ is a scalar since
$
  overline(psi) (x) psi (x) &= psi^dagger (x) gamma^0 psi (x) \
  &-> psi^dagger (Lambda^(-1) x) S[Lambda]^dagger gamma^0 S[Lambda] psi(Lambda^(-1) x) \
  &= psi^dagger (Lambda^(-1) x) gamma^0 psi(Lambda^(-1) x) \
  &= overline(psi) (Lambda^(-1)x) psi(Lambda^(-1) x)
$
And $overline(psi) gamma^mu psi$ is a vector since
$
  overline(psi) (x) gamma^mu psi(x) &= psi^dagger (x) gamma^0 gamma^mu psi(x) \
  &-> psi^dagger (Lambda^(-1) x) S[Lambda]^dagger gamma^0 gamma^mu S[Lambda] psi(Lambda^(-1) x)\
  &= psi^dagger (Lambda^(-1) x) gamma^0 S[Lambda]^(-1) gamma^mu S[Lambda] psi(Lambda^(-1) x) \
  &= tensor(Lambda, mu, -nu) overline(psi) (Lambda^(-1) x) gamma^nu psi(Lambda^(-1) x)
$
using these we can construct the non-trivial Dirac action
$
  S = integral dd(x, 4) overline(psi) (i gamma^mu partial_mu - m) psi
$
with
$
  cal(L)_"Dirac" = overline(psi) (i gamma^mu partial_mu - m) psi
$
being the Dirac Lagrangian. Varying the action with respect to $overline(psi)$ gives the Dirac equation
$
  (i gamma^mu partial_mu - m) psi = 0
$
this is nice! And this guy implies the Klein-Gordon equation
$
  0 & = (i gamma^nu partial_nu + m)(i gamma^mu partial_mu -m) psi \
    & = - (gamma^mu gamma^nu partial_mu partial_nu + m^2) psi \
    & = -(partial_mu partial_mu + m^2) psi
$
this hints at the meaning of $m$ and justifies the inclusion of $i$.

#let feyn(body) = math.cancel(angle: 15deg, body)

As a point of notation one usually writes
$
  A_mu gamma^mu = feyn(A)
$
so the Dirac equation is written as
$
  (i feyn(partial) - m) psi = 0
$

== Weyl spinors
With our representation we can write
$
  S^(0 i) = - i/2 mat(sigma^i, 0; 0, -sigma^i)";  " S^(i j) = 1/2 epsilon^(i j k) mat(sigma^k, 0; 0, sigma^k)
$
these generate boosts and rotations.

The rotation matrix becomes (with $omega_(i j) = - epsilon_(i j k) phi^k$)
$
  S[Lambda] &= exp[i/4 phi^k underbracket(epsilon_(i j k) epsilon^(i j m), 2 tensor(delta, -k, m)) mat(sigma^m, 0; 0, sigma^m)] \
  &= mat(exp(i bold(phi) dot bold(sigma)\/2), 0; 0, exp(i bold(phi) dot bold(sigma)\/2))
$
As an example consider a rotation by $2 pi$ about the $x^3$-axis. Then $bold(phi) = vecrow(0, 0, 2 pi)$ giving
$
  S[Lambda_"rotation"] = mat(exp(i pi sigma^3), 0; 0, exp(i pi sigma^3)) = - 1
$
meaning $psi^alpha -> - psi^alpha$!

The boost matrix becomes (with $omega_(i 0) = - omega_(0 i) = chi_i$)
$
  S[Lambda_"boost"] &= exp[-i/2 (omega_(0 i) S^(0 i) + omega_(i 0) S^(i 0))] = exp[i chi_i S^(0 i)] \
  &= mat(exp(bold(chi) dot bold(sigma)\/2), 0; 0, exp(- bold(chi) dot bold(sigma)\/2))
$
both are block diagonal meaning the Dirac spinor representation of the Lorentz group is _reducible_. We decompose it into two irreducible representations acting on $u_plus.minus$ defined by
$
  psi = vec(u_+, u_-)
$
the two-component objects $u_plus.minus$ are called _Weyl spinors_. They transform similarly under rotations
$
  u_plus.minus -> exp(i bold(phi) dot bold(sigma)\/2) u_plus.minus
$
but oppositely under boosts
$
  u_plus.minus -> exp(plus.minus bold(chi) dot bold(sigma)\/2) u_plus.minus
$
We can write the Lagrangian in terms of these
$
  cal(L) &= overline(psi) (i feyn(partial) - m) psi \
  &= i u_-^dagger sigma^mu partial_mu u_- + i u^dagger_+ overline(sigma)^mu partial_mu u_+ - m (u_+^dagger u_- + u_-^dagger u_+)
$
where we define
$
  sigma^mu equiv vecrow(1, sigma^i)";  " overline(sigma)^mu equiv vecrow(1, -sigma^i)
$
then
$
  gamma^mu = mat(0, sigma^mu; overline(sigma)^mu, 0)
$
We see that for $m eq.not 0$ the $u_plus.minus$ couple which makes everything more complicated. For a massless fermion $m = 0$ we find
$
  i overline(sigma)^mu partial_mu u_+ & = 0 \
            i sigma^mu partial_mu u_- & = 0
$
these are the _Weyl equations_.

== Dirac field bilinears
We introduce a fifth gamma matrix
$
  gamma^5 &equiv - i gamma^0 gamma^1 gamma^2 gamma^3 \
  &= - i/4! epsilon^(mu nu rho sigma) gamma_mu gamma_nu gamma_rho gamma_sigma
$
$gamma^5$ has the following properties
$
  (gamma^5)^dagger & = gamma^5";  " (gamma^5)^2 & = 1";  " {gamma^5,gamma^mu} &= 0
$
implying $[gamma^5, S^(mu nu)] = 0$.

We can construct projection operators
$
  P_plus.minus = 1/2 (1 plus.minus gamma^5)
$
with $P_plus.minus^2 = P_plus.minus$ and $P_+ P_- = 0$. With the Dirac representation
$
  gamma^5 = mat(1, 0; 0, -1)
$
meaning $P_plus.minus$ project onto the Weyl spinors $u_plus.minus$. This also shows the Dirac representation is reducible. We can then define $ psi_plus.minus = P_plus.minus psi $ which form the irreducible representations of the Lorentz group.

We have seen that $overline(psi) psi$ is a scalar and that $overline(psi) gamma^mu psi$ is a vector. We can similarly construct the anti-symmetric tensor $ gamma^(mu nu) = 1/2 [gamma^mu,gamma^nu] equiv - i sigma^(mu nu) $
which transforms as
$
  overline(psi) gamma^(mu nu) psi &-> (overline(psi) Lambda_(1\/2)^(-1)) (1/2 [gamma^mu, gamma^mu]) (Lambda_(1\/2) psi) \
  & = 1/2 overline(psi) (Lambda_(1\/2)^(-1) gamma^mu Lambda_(1\/2) Lambda_(1\/2)^(-1) gamma^(nu) Lambda_(1\/2) - [mu <--> nu]) psi \
  & = tensor(Lambda, mu, -alpha) tensor(Lambda, nu, -beta) overline(psi) gamma^(alpha beta) psi
$
as claimed.

With $gamma^5$ we can construct the pseudo-vector $overline(psi) gamma^mu gamma^5 psi$ and pseudo-scalar $overline(psi) gamma^5 psi$ with _pseudo_ referring to how they transform under parity. We will see this later. We could now extend $cal(L)$ by the addition of new terms combining the above.

Using the bilinears we can construct the currents
$
  j^mu = overline(psi) gamma^mu psi";  " j^(mu 5) = overline(psi) gamma^mu gamma^5 psi
$
Consider $j^mu$
$
  partial_mu j^mu &= (partial_mu overline(psi)) gamma^mu psi + overline(psi) gamma^mu partial_mu psi = i m overline(psi) psi - overline(psi) i m psi \
  &= 0
$
where we use
$
  (i partial_mu gamma^mu - m) psi = 0";  " overline(psi) (i arrow.l(partial)_mu gamma^mu + m) = 0
$
so $j^mu$ is conserved! This is expected since it is the Noether current corresponding to the $"U"(1)$ symmetry of $cal(L)$. Consider
$
  psi -> e^(i alpha) psi
$
for an infinitesimal transformation
$
  psi -> psi underbracket(+ i alpha psi, dd(psi, d: delta))";  " overline(psi) -> overline(psi) underbracket(- i alpha overline(psi), dd(overline(psi), d: delta))
$
we find
$
  dd(cal(L), d: delta) &= dd(overline(psi), d: delta) ( i gamma^mu partial_mu -m) psi + overline(psi) (i gamma^mu partial_mu - m) dd(psi, d: delta) \
  &= - partial_mu alpha underbracket(overline(psi) gamma^mu psi, j^mu)
$
then
$
  dd(S, d: delta) = - integral dd(x, 4) (partial_mu alpha) j^mu = integral dd(x, 4) alpha (partial_mu j^mu) + "boundary"
$
since $alpha$ is arbitrary we find $partial_mu j^mu = 0$ on shell!

For $j^(mu 5)$ we find
$
  partial_mu j^(mu 5) = 2 i m overline(psi) gamma^5 psi
$
so for $m = 0$ it is conserved! This is the Noether current corresponding to the _chiral symmetry_ $psi -> e^(i alpha gamma^5) psi$.

For spacetime translations we consider the canonical energy-momentum tensor. Since $cal(L)$ only depends on $partial_mu psi$ we find
$
  tensor(T, mu, -nu) &= pdv(cal(L), (partial_mu psi)) partial_nu psi - cal(L) tensor(delta, mu, -nu) \
  &= i overline(psi) gamma^mu partial_nu psi - cal(L) tensor(delta, mu, -nu) =^"on shell" i overline(psi) gamma^mu partial_nu psi
$
which is nice and simple.

== Plane wave solutions
We seek solutions to the Dirac equation
$
  (i feyn(partial)-m) psi = 0
$
we make the ansatz
$
  psi = u(bold(p)) e^(-i p dot x) #h(2em) ("positive frequency")
$
then the Dirac equation becomes
$
  (gamma^mu p_mu - m) u (bold(p)) = mat(-m, p_mu sigma^mu; p_mu overline(sigma)^mu, -m) u(bold(p)) = 0
$
We claim the solution is
$
  u(bold(p)) = vec(sqrt(p dot sigma) xi, sqrt(p dot overline(sigma)) xi)
$
for any two-component spinor $xi$ normalized to $xi^dagger xi = 1$. We find later that $xi$ determine the spin. To see this let $u^TT = vecrow(u_1, u_2)$ then the Dirac equation says
$
  (p dot sigma) u_2 = m u_1 " and " (p dot overline(sigma)) u_1 = m u_2
$
note that these imply eachother since $(p dot sigma) (p dot overline(sigma)) = p_mu p^mu = m^2$. We try $u_1 = (p dot sigma) xi'$ for some spinor $xi'$. Then
$
  u (bold(p)) = A vec((p dot sigma) xi', m xi')
$
with $A$ being some constant. We pick $A = m^(-1)$ and $xi' = sqrt(p dot overline(sigma)) xi$. Then $u_1 = m sqrt(p dot sigma) xi$ and we are done.

We find other solutions using the ansatz
$
  psi = v (bold(p)) e^(i p dot x) #h(2em) ("negative frequency")
$
The Dirac equation becomes
$
  (gamma^mu p_mu + m) v (bold(p)) = mat(m, p_mu sigma^mu; p_mu overline(sigma)^mu, m) v(bold(p)) = 0
$
with solution
$
  v(bold(p)) = vec(sqrt(p dot sigma) eta, - sqrt(p dot overline(sigma)) eta)
$
for any two-component spinor $eta$ normalized to $eta^dagger eta = 1$.

We introduce a basis $xi^s$ and $eta^s$ with $s = 1, 2$ such that
$
  xi^(r dagger) xi^s = delta^(r s) " and " eta^(r dagger) eta^s = delta^(r s)
$
Then we can write the positive frequency solutions as
$
  u^s (bold(p)) = vec(sqrt(p dot sigma) xi^s, sqrt(p dot overline(sigma)) xi^s)
$
We now compute some identities we will need
$
  u^(r dagger) (bold(p)) dot u^s (bold(p)) &= vecrow(xi^(r dagger) sqrt(p dot sigma), xi^(r dagger) sqrt(p dot overline(sigma))) vec(sqrt(p dot sigma) xi^s, sqrt(p dot overline(sigma))xi^s) \
  &= xi^(r dagger) p dot sigma xi^s + xi^(r dagger) p dot overline(sigma) xi^s = 2 E_bold(p) delta^(r s)
$
similarly
$
  overline(u)^r (bold(p)) dot u^s (bold(p)) = 2 m delta^(r s)
$
Analogously we can write the negative frequency solutions as
$
  v^s (bold(p)) = vec(sqrt(p dot sigma) eta^s, - sqrt(p dot overline(sigma)) eta^s)
$
where we have
$
   v^(r dagger) (bold(p)) dot v^s (bold(p)) & = 2 E_bold(p) delta^(r s) \
  overline(v)^r (bold(p)) dot v^s (bold(p)) & = -2m delta^(r s)
$
We can also try to mix $u^s (bold(p))$ and $v^s (bold(p))$. We can find
$
   overline(u)^r (bold(p)) dot v^s (bold(p)) & = 0 \
   overline(v)^r (bold(p)) dot u^s (bold(p)) & = 0 \
  u^(r dagger) (bold(p)) dot v^s (- bold(p)) & = 0 \
   v^(r dagger) (bold(p)) dot u^s (-bold(p)) & = 0
$
We also have the completion relations
$
  sum_s u^s (bold(p)) overline(u)^s (bold(p)) & = feyn(p) + m \
  sum_s v^s (bold(p)) overline(v)^s (bold(p)) & = feyn(p) - m
$
these follow immediately from $sum_s xi^s xi^(s dagger) = bb(1)$ and $sum_s eta^s eta^(s dagger) = bb(1)$.

== Quantizing the Dirac field
We start with the Lagrangian
$
  cal(L) = overline(psi) (i feyn(partial) - m) psi
$
we find the canonical momentum conjugate to $psi$ by
$
  pi = pdv(cal(L), dot(psi)) = i overline(psi) gamma^0 = i psi^dagger
$
The Hamiltonian is then
$
  cal(H) = pi dot(psi) - cal(L) = overline(psi) (-i gamma^i partial_i + m) psi
$
We try to quantize $psi$ by imposing
$
  [psi_alpha (bold(x)), psi_beta^dagger (bold(y))] = delta^((3)) (bold(x)-bold(y)) delta_(alpha beta)
$
this leads to multiple problems. We expand $psi$ as
$
  psi (bold(x)) = sum_s integral dd(p, 3)/(2 pi)^3 1/sqrt(2 E_bold(p)) [a_bold(p)^s u^s (bold(p)) e^(i bold(p) dot bold(x)) + b_bold(p)^(s) v^s (bold(p)) e^(-i bold(p) dot bold(x))]
$
and claim the commutation relations
$
  [a_bold(p)^r, a_(bold(q))^(s dagger)] = [b_bold(p)^r, b_bold(q)^(s dagger)] = (2 pi)^3 delta^((3)) (bold(p)-bold(q)) delta^(r s)
$
imply the imposed ones.

#proof[see any book.]

Then we can write the Hamiltonian in terms of $a$ and $b$ by
$
  H = integral dd(p, 3)/(2 pi)^3 sum_s (E_bold(p) a_bold(p)^(s dagger) a_bold(p)^s - E_bold(p) b_bold(p)^(s dagger) b_bold(p)^s)
$
this is problematic. Consider
$
  [H, b_bold(p)^(s dagger)] &= integral dd(q, 3)/(2 pi)^3 sum_s E_bold(q) [b_bold(p)^(s dagger), b_bold(q)^(r dagger) b_(bold(q))^r] = integral dd(q, 3)/(2 pi)^3 sum_s E_bold(q) b_bold(q)^(r dagger) [b_bold(p)^(s dagger), b_bold(q)^r] \
  &=- integral dd(q, 3)/(2pi)^3 sum_s E_bold(q) b_(bold(q))^(r dagger) (2 pi)^3 delta^((3)) (bold(q)-bold(p)) delta^(r s) = - E_bold(p) b_bold(p)^(s dagger)
$
so creating particles with $b^dagger$ can lower the energy forever.

The solution to this problem is imposing the anticommutation relations
$
  {psi_a (bold(x)), psi_b^dagger (bold(y))} &= delta^((3)) (bold(x)-bold(y)) delta_(a b) \
  {psi_a (bold(x)), psi_b (bold(y))} &= {psi_a^dagger (bold(x)), psi_b^dagger (bold(y))} = 0
$
Then the creation and annihilation operators must satisfy
$
  {a_bold(p)^r, a_bold(q)^(s dagger)} = {b_bold(p)^r, b_bold(q)^(s dagger)} = (2 pi)^3 delta^((3)) (bold(p)-bold(q)) delta^(r s)
$
and one finds the same Hamiltonian
$
  H = integral dd(p, 3)/(2 pi)^3 sum_s (E_bold(p) a_bold(p)^(s dagger) a_bold(p)^s - E_bold(p) b_bold(p)^(s dagger) b_bold(p)^s)
$
but we can now avoid the negative energies by redefining $b <--> b^dagger$. Then
$
  -E_bold(p) b_bold(p)^(s dagger) b_bold(p)^s -> + E_bold(p) b_bold(p)^(s dagger) b_bold(p)^s - "const"
$
and since the anticommutation relation is symmetric it does not change. So we find
$
  H = integral dd(p, 3)/(2 pi)^3 sum_s (E_bold(p) a_bold(p)^(s dagger) a_bold(p)^s + E_bold(p) b_bold(p)^(s dagger) b_bold(p)^s - (2 pi)^3 delta^((3)) (0))
$
with the field expanded as
$
  psi (bold(x)) = sum_s integral dd(p, 3)/(2 pi)^3 1/sqrt(2 E_bold(p)) [a_bold(p)^s u^s (bold(p)) e^(i bold(p) dot bold(x)) + b_bold(p)^(s dagger) v^s (bold(p)) e^(-i bold(p) dot bold(x))]
$
We define vacuum by $a_bold(p)^s ket(0) = b_bold(p)^s ket(0) = 0$ and as before $a_bold(p)^(s dagger)$ and $b_bold(p)^(s dagger)$ create particles. Consider a two-particle state $a_bold(p)^dagger a_bold(q)^dagger ket(0)$. We have
$
  a_bold(p)^dagger a_bold(q)^dagger ket(0) = - a_bold(q)^dagger a_bold(p)^dagger ket(0) =^(bold(p)=bold(q)) 0
$
so the state is anti-symmetric under exchange and multiple particles can not exist in the same mode! We conclude that if the ladder operators obey anticommutation relations then they obey Fermi-Dirac statistic. As opposed to the scalar field where they obey Bose-Einstein statistics.

Before proceeding we switch to the Heisenberg picture. This is done using
$
  e^(i H t) a_bold(p)^s e^(-i H t) = a_bold(p)^s e^(-i E_bold(p) t)";  " e^(i H t) b_bold(p)^s e^(-i H t) = b_bold(p)^s e^(i E_bold(p) t)
$
which gives
$
  psi(x) &= integral dd(p, 3)/(2 pi)^3 1/sqrt(2 E_bold(p)) sum_s (a_bold(p)^s u^s (p) e^(-i p dot x) + b_bold(p)^(s dagger) v^s (p) e^(i p dot x)) \
  overline(psi)(x) &= integral dd(p, 3)/(2 pi)^3 1/sqrt(2 E_bold(p)) sum_s (b_bold(p)^s overline(v)^s (p) e^(-i p dot x) + a_bold(p)^(s dagger) overline(u)^s (p) e^(i p dot x))
$
we write the Hamiltonian and momentum operators as
$
  H &= integral dd(p, 3)/(2 pi)^3 sum_s E_bold(p) (a_bold(p)^(s dagger) a_bold(p)^s + b_bold(p)^(s dagger) b_bold(p)^s) \
  bold(P) &= integral dd(x, 3) psi^dagger (-i grad) psi = integral dd(p, 3)/(2 pi)^3 sum_s bold(p) (a_bold(p)^(s dagger) a_bold(p)^s + b_bold(p)^(s dagger) b_bold(p)^s)
$
Then both $a_bold(p)^(s dagger)$ and $b_bold(p)^(s dagger)$ create particles with energy $E_bold(p)$ and momentum $bold(p)$. We refer to particles created by $a_bold(p)^(s dagger)$ as fermions and particles created by $b_bold(p)^(s dagger)$ as antifermions.

== Spin and charge
We want to find the spin of a Dirac particle. We consider a rotation under which $psi$ transforms as
$
  psi (x) -> Lambda_(1\/2) psi(Lambda^(-1) x)
$
we want to use Noether's theorem so we need $dd(psi, d: delta)$
$
  dd(psi, d: delta) = Lambda_(1\/2) psi (Lambda^(-1) x) - psi(x)
$
by $omega_12 = - omega_21 = theta$ we find
$
  Lambda_(1\/2) tilde.eq 1 - i/2 omega_(mu nu) S^(mu nu) = 1 - i/2 theta mat(sigma^3, 0; 0, sigma^3) equiv 1 - i/2 theta Sigma^3
$
so
$
  dd(psi, d: delta) &= (1 - i/2 theta Sigma^3) psi(t, x+theta y, y-theta x, z) - psi(x) \
  &= -theta (x partial_y - y partial_x + i/2 Sigma^3) psi (x) equiv theta Delta psi
$
then
$
  j^0 = pdv(cal(L), (partial_0 psi)) Delta psi = - i overline(psi) gamma^0 (x partial_y - y partial_x + i/2 Sigma^3) psi
$
similarly for rotations about $x$ and $y$ so we find
$
  bold(J) = integral dd(x, 3) psi^dagger (bold(x) times (-i grad) + underbracket(1/2 bold(Sigma), tilde "spin")) psi
$
the second term is related to the spin angular momentum for non-relativistic fermions. For relativistic fermions it is more complicated, luckily we only need to consider fermions at rest. We apply $J-z$ to $a_0^(s dagger) ket(0)$. Since $J_z ket(0)$ we can find $[J_z,a_0^(s dagger)] ket(0)$. This commutator is non-vanishing for terms in $J_z$ that have annihilations operators at $bold(p) = 0$. The orbital part of $J_z$ vanishes for these. We can then expand the spin part as
$
  J_z &= integral dd(x, 3) integral dd(p, p', 3)/(2pi)^6 1/sqrt(2 E_bold(p) 2 E_bold(p)') e^(-i bold(p)'dot bold(x)) e^(i bold(p) dot bold(x)) \
  &times sum_(r') [a_bold(p)'^(r' dagger) u^(r' dagger) (bold(p)') + b_(-bold(p)')^(r') v^(r' dagger) (- bold(p)')] Sigma^3/2 sum_r [a_bold(p)^r u^r (bold(p)) + b_(-bold(p))^(r dagger) v^r (-bold(p))]
$
the only surviving term when taking the commutator has the form
$
  [a_bold(p)^(r dagger) a_bold(p)^r, a_0^(s dagger)] = (2pi)^3 delta^((3)) (bold(p)) a_0^(r dagger) delta^(r s)
$
others vanish or kill vacuum. We find
$
  J_z a_0^(s dagger) ket(0) &= 1/(2 m) sum_r [u^(s dagger) (0) Sigma^3/2 u^r (0)] a_0^(r dagger) ket(0) \
  &= sum_r (xi^(s dagger) sigma^3/2 xi^r) a_0^(r dagger) ket(0)
$
taking $xi^(s TT) = vecrow(1, 0)$ we find the eigenvalue $+ 1/2$ and taking $xi^(s TT) = vecrow(0, 1)$ we find $- 1/2$. Doing a similar computation for an antifermion state yields an extra $-$ sign meaning the spins reverse.

We conclude
$
  J_z a_0^(s dagger) ket(0) = plus.minus 1/2 a_0^(s dagger) ket(0)";  " J_z b_0^(s dagger) ket(0) = minus.plus b_0^(s dagger) ket(0)
$
for $xi^(s TT) = vecrow(1, 0)$ and $xi^(s TT) = vecrow(0, 1)$ respectively.

Recall the conserved current
$
  j^mu = overline(psi) gamma^mu psi
$
the corresponding charge is
$
  Q &= integral dd(x, 3) psi^dagger psi \
  &= integral dd(p, 3)/(2 pi)^3 sum_s (a_bold(p)^(s dagger) a_bold(p)^s - b_bold(p)^(s dagger) b_bold(p)^s + "const")
$
so fermions have charge $+1$ while antifermions have charge $-1$.

== Propagators
We define the _fermionic propagator_
$
  S_(alpha beta) &= {psi_alpha (x), overline(psi)_beta (y)} equiv S(x-y) \
  &= integral dd(p, q, 3)/(2pi)^6 1/sqrt(4 E_bold(p) E_bold(q)) [{a_bold(p)^s, a_bold(q)^(r dagger)} u^s (p) overline(u)^r (q) e^(-i (p dot x-q dot y)) \ &#h(12em)+ {b_bold(p)^(s dagger), b_bold(q)^r} v^s (p) overline(v)^r (q) e^(i (p dot x - q dot y))] \
  &= integral dd(p, 3)/(2pi)^3 1/(2 E_bold(p)) [u^s (p) overline(u)^s (p) e^(- i p dot (x-y)) + v^s (p) overline(v)^r (p) e^(i p dot (x-y)) ] \
  &= integral dd(p, 3)/(2pi)^3 1/(2 E_bold(p)) [(feyn(p)+m) e^(-i p dot (x-y)) + (feyn(p)-m) e^(i p dot (x-y))] \
  &= (i feyn(partial)_x + m) integral dd(p, 3)/(2 pi)^3 1/(2 E_bold(p)) (e^(-i p dot (x-y))- e^(i p dot (x-y))) \
  &= (i feyn(partial)_x + m) [phi.alt (x), phi.alt (y)]
$
where
$
  [phi.alt(x), phi.alt(y)] = D(x-y) - D(y-x)
$
Similarly we can find
$
  braket(0, psi_alpha (x) overline(psi)_beta (y), 0) &= (i feyn(partial)_x + m)_(alpha beta) integral dd(p, 3)/(2 pi)^3 1/(2 E_bold(p)) e^(-i p dot (x-y)) \
  braket(0, overline(psi)_beta (y) psi_alpha (x), 0) &= - (i feyn(partial)_x +m)_(alpha beta) integral dd(p, 3)/(2 pi)^3 1/(2 E_bold(p)) e^(-i p dot (y-x))
$
and define the Feynman propagator
$
  S_F (x-y) &equiv braket(0, T psi(x) overline(psi)(y), 0) \
  &= cases(braket(0, psi(x) overline(psi)(y), 0) " for " x^0 > y^0, -braket(0, overline(psi)(y) psi(x), 0) " for " x^0 < y^0)
$
with the $-$ sign arising due to exchanging $psi$ and $overline(psi)$. We can write this as
$
  S_F (x-y) = integral dd(p, 4)/(2 pi)^4 (i (feyn(p) +m))/(p^2-m^2 + i epsilon) e^(-i p dot (x-y))
$
which is a Green's function of the Dirac equation
$
  (i feyn(partial)_x - m) S_F (x-y) = i delta^((4)) (x-y)
$
