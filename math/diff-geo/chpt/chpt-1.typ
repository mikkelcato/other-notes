//**** init-ting
#import "@preview/physica:0.9.5": *
#import "chpt-temp.typ": *
#import "@preview/mannot:0.3.0": *
#import "@preview/cetz:0.4.1" // drawings

#show: thmrules.with(qed-symbol: $square$)
#show: chpt-note.with()

#set enum(indent: 2em)

= Differential geometry
== Manifolds
A manifold is in general a topological space which is locally homeomorphic to $RR^m$. This enables us to give each point in a manifold a set of $m$ numbers, the local coordinate. If the manifold is not homeomorphic to $RR^m$ globally, then we have to introduce multiple coordinates, meaning in some cases any point can have multiple coordinates. We require that manifolds behave nicely, so we want the transition between coordinates to be _smooth_, this will let us do calculus on manifolds using tools we are already familiar with. This notion is made concrete by the actual definition:

#def[Manifold][
  $M$ is an $m$-dimensional differentiable manifold if

  1. $M$ is a topological space.

  2. $M$ is provided with a family of pairs ${(U_i, phi_i)}$.

  3. ${U_i}$ is a family of open sets which covers $M$, meaning $union.big_i U_i = M$. And $phi_i$ is a homeomorphism from $U_i$ onto an open subset $U'_i$ of $RR^m$.

  4. Given $U_i$ and $U_j$ with $U_i inter U_j eq.not emptyset$, the map $psi_(i j) = phi_i compose phi_j^(-1)$ from $phi_j (U_i inter U_j)$ to $phi_i (U_i inter U_j)$ is infinitely differentiable or smooth.
]

We call the pair $(U_i, phi_i)$ a chart with the family of charts being an atlas. The subset $U_i$ is called the coordinate neighbourhood while $phi_i$ is the coordinate. The homeomorphism $phi_i$ is represented by $m$ functions ${x^1 (p), dots, x^m (p)}$ with $p in U_i$. Any point $p in M$ exists independently of the coordinate representation we choose to ascribe it. So in each coordinate neighbourhood $U_i$ the manifold $M$ looks like an open subset of $RR^m$ with elements ${x^1, dots, x^m}$ (locally Euclidean).

In the case that $U_i$ and $U_j$ overlap, two coordinate representations are assigned to any point $p in U_i inter U_j$. The fourth axiom ensures the transition between these is smooth. The map $phi_i$ assigns $m$ coordinate values $x^mu$ to $p$ while $phi_j$ assigns $m$ different coordinate values $y^nu$ to $p$. The transition between these $x^mu = x^mu (y)$ is given by $m$ functions of $m$ variables. This function $x^mu = x^mu (y)$ is the explicit form of $psi_(j i) = phi_j compose phi_i^(-1)$. Differentiability is then defined as usual with the transformation being smooth if each $x^mu (y)$ is smooth with respect to all $y^nu$.

We already know many manifolds: $RR^n$, $D^n$, $S^n$ and $T^n$.

=== Smoothness
Let $f : M -> N$ so any point $p in M$ is mapped to $f(p) in N$. Take a chart $(U,phi)$ on $M$ and a chart $(V,psi)$ on $N$ with $p in U$ and $f(p) in V$. Then $f$ has the presentation
$
  psi compose f compose phi^(-1) : RR^m -> RR^n
$
if $phi(p) = {x^mu}$ and $psi(f(p)) = {y^alpha}$ then the above is just $y = psi compose f compose phi^(-1) (x)$. This is sometimes written as $y = f(x)$ or $y^alpha = f^alpha (x^mu)$. Given $y^alpha = f^alpha (x^mu)$ is smooth then $f$ is called differentiable at $p$ or $x = phi (p)$.

#proposition[Smoothness of $f$ is chart-independent in $M$ and $N$.]
#proof[
  We first show it is independent of the chart in $M$. Let $(U_1, phi_1)$ and $(U_2,phi_2)$ be two charts in $M$ and pick $p in U_1 inter U_2$. The coordinates by $phi_1$ are ${x_1^mu}$ and the coordinates by $phi_2$ are ${x_2^mu}$. In terms of ${x_1^mu}$ we have
  $
    F_1 = psi compose f compose phi_1^(-1)
  $
  and in terms of ${x_2^mu}$ we have
  $
    F_2 = psi compose f compose phi_2^(-1) = psi compose f compose phi_1^(-1) compose underbrace((phi_1 compose phi_2^(-1)), psi_(1 2)) = F_1 compose psi_12
  $
  By definition $psi_12$ is smooth so if $F_1$ is smooth then  $F_2$ is smooth.

  Similarly let $(V_1, psi_1)$ and $(V_2, psi_2)$ be two charts in $N$. Then by $psi_1$ we have
  $
    F_1 = psi_1 compose f compose phi^(-1)
  $
  and by $psi_2$ we have
  $
    F_2 = psi_2 compose f compose phi^(-1) = underbrace((psi_2 compose psi_1^(-1)), psi_12^(-1)) compose psi_1 compose f compose phi^(-1) = psi_12^(-1) compose F_1
  $
  By definition $psi_12^(-1)$ is smooth and we are done.
]

#def[Diffeomorphism][
  Let $f : M -> N$ be a homeomorphism and $psi$ and $phi$ be coordinate functions as above.

  If $psi compose f compose phi^(-1)$ is invertible and both $y = psi compose f compose phi^(-1) (x)$ and $x = phi compose f^(-1) compose psi^(-1) (y)$ are smooth then $f$ is a diffeomorphism. In this case $M$ and $N$ are diffeomorphic $M equiv N$.
]

Two diffeomorphic spaces are regarded as equivalent since all diffeomorphic spaces can be smoothly deformed into each other.

We denote the set of all diffeomorphisms $f : M -> M$ by $"Diff"(M)$, this is a group. Let $p$ be a point in a chart $(U,phi)$ such that $phi(p) = x^mu (p)$. Under $f in "Diff"(M)$ the point $p$ is mapped to $f(p)$ with coordinate $phi(f(p)) = y^mu (f(p))$ under the assumption that $f(p) in U$. The function $y$ is differentiable. This is what we call an active coordinate transformation. We could also consider two charts $(U,phi)$ and $(V,psi)$ with $U inter V eq.not emptyset$. Then we have two sets of coordinate values $x^mu = phi(p)$ and $y^mu = psi(p)$ for $p in U inter V$. The map $x |-> y$ is differentiable due to the smoothness of the manifold. This reparametrization is what we call a passive transformation. The group of all reparametrizations is $"Diff"(M)$.

#pagebreak()
== Tangent vectors
We are primarily interested in two mappings: curves and functions. An open curve is a map $c : (a,b) -> M$ with $a < 0 < b$, if it is closed it is the map $c: S^1 -> M$. On a chart $(U,phi)$ a curve $c(t)$ has the presentation $x = phi compose c : RR -> RR^m$. A function $f$ on $M$ is a smooth map $f: M -> RR$. On a chart $(U,phi)$ the presentation is $f(p) = f compose phi^(-1) : RR^m -> RR$. The set of smooth functions on $M$ is denoted by $cal(F) (M)$.

Let $c: (a,b) -> M$ be a curve with $c(0) = p$. For any smooth $f : M -> RR$ with $t = 0 in (a,b)$,
$
  evaluated(dv(f(c(t)), t))_(t=0) &=^("local" #linebreak() "coordinate") evaluated(pdv((f compose phi^(-1) (x)), x^mu))_(x = phi(p)) evaluated(dv(x^mu (c(t)), t))_(t=0) \
  &= pdv(f, x^mu) evaluated(dv(x^mu (c(t)), t))_(t=0)
$
where $phi$ is a chart with coordinates $x^mu$. Define
$
  X^mu equiv evaluated(dv(x^mu (c(t)), t))_(t=0)
$
then
$
  evaluated(dv(f(c(t)), t))_(t=0) = X^mu pdv(f, x^mu) equiv X [f]
$
we call $X$ the tangent vector to $M$ at $p = c(0)$.

As an example take the coordinate functions $phi(c(t)) = x^mu (t)$,
$
  X[x^mu] & = X^mu pdv(x^mu, x^nu) = X^nu delta_nu^mu = X^mu
$
this is the $mu$th component of the velocity vector if $t tilde "time"$.

If two curves $c_1 (t)$ and $c_2 (t)$ satisfy

$
  c_1 (0) = c_2 (0) = p " and " evaluated(dv(x^mu (c_1 (t)), t))_(t = 0) = evaluated(dv(x^mu (c_2 (t)), t))_(t=0)
$
then they give the same $X$. We define this to be an equivalence relation $c_1 (t) tilde c_2 (t)$. And we identify $X$ with the equivalence class $[c(t)]$. All equivalence classes at $p in M$ form a vector space, the tangent space denoted by $T_p M$.

Clearly $e_mu = partial\/dd(x^mu, d: partial)$ are basis vectors of $T_p M$ and $dim T_p M = dim M$. The basis $\{e_mu\}$ is called the coordinate basis, and any vector $V in T_p M$ can be written as $V = V^mu e_mu$ with $V^mu$ being the components. By definition any vector $X$ exists without specifying coordinates, but this is convenient to do. Then we should also be able to figure out how the components transform. Let $p in U_i inter U_j$ and $x = phi_i (p)$, $y = phi_j (p)$ then for any $X in T_p M$ we can write
$
  X = X^mu pdv(, x^mu) = tilde(X)^mu = pdv(, y^mu)
$
so the components are related by
$
  tilde(X)^mu = X^nu pdv(y^mu, x^nu)
$
this ensures the vector is invariant.

#pagebreak()
== One-forms
Since $T_p M$ is a vector space it has a dual vector space with elements being maps $omega:T_p M -> RR$. We call this the cotangent space at $p$ and denote it by $T_p^*M$. Any $omega in T_p^* M$ is called a cotangent vector (covector) or one-form.

The simplest example is the differential $dd(f)$ with $f in cal(F) (M)$. The action of a vector $V$ on $f$ is $V[f] = V^mu dd(f, d: partial)\/dd(x^mu, d: partial) in RR$. Then the action of $dd(f) in T_p^* M$ on $V in T_p M$ is defined by
$
  innerproduct(dd(f), V) equiv V[f] = V^mu pdv(f, x^mu) in RR
$
This is $RR$-linear in $V$ and $f$.

Consider $f = x^mu$ and $V = partial\/dd(x^mu, d: partial)$ then
$
  innerproduct(dd(x^mu), pdv(, x^nu)) = pdv(x^mu, x^nu) = delta_nu^mu
$
so $f^mu = dd(x^mu)$ provides a basis for $T_p^* M$, and any one-form can be written as $omega = omega_mu dd(x^mu)$. In this basis we can write
$
  dd(f) = pdv(f, x^mu) dd(x^mu)
$
since
$
  innerproduct(dd(f), V) = innerproduct(pdv(f, x^mu) dd(x^mu), V^nu pdv(, x^nu)) = pdv(f, x^mu) V^nu innerproduct(dd(x^mu), pdv(, x^nu)) = V^mu pdv(f, x^mu) = V[f]
$
Similarly given a vector $V = V^mu partial_mu$ and a one-form $omega = omega_mu dd(x^mu)$ we define the inner product $innerproduct(dot, dot) : T_p^* M times T_p M -> RR$ by
$
  innerproduct(omega, V) = omega_mu V^nu innerproduct(dd(x^mu), partial_nu) = omega_mu V^nu delta_nu^mu = omega_mu V^mu
$
which is familiar.

Let $p in U_i inter U_j$ then
$
  omega = omega_mu dd(x^mu) = tilde(omega)_nu dd(y^nu)
$
with $x = phi_i (p)$ and $y = phi_j (p)$. From $dd(y^nu) = (dd(y^nu, d: partial)\/dd(x^mu, d: partial)) dd(x^mu)$ we find
$
  tilde(omega)_nu = omega_mu pdv(x^mu, y^nu)
$
which is nice.

#pagebreak()
== Tensors
A tensor of type $(q,r)$ is a multi-linear object which maps $q$ elements of $T_p^* M$ and $r$ elements of $T_p M$ to a real number. The set of type $(q,r)$ tensors at $p in M$ is denoted by $cal(T)^q_(r,p) (M)$. Any element of $cal(T)^q_(r,p) (M)$ can be written in terms of the bases mentioned above,
$
  T = tensor(T, mu_1 dots mu_q, -nu_1 dots nu_r) partial_mu_1 dots partial_mu_q dd(x^(nu_1)) dots dd(x^(nu_r))
$
clearly this is a linear function $ T: times.circle^q T_p^* M times.circle^r T_p M -> RR $ Defining $V_i equiv V_i^mu partial_mu$ and $omega_i = omega_(i mu) dd(x^mu)$ then the action of $T$ gives a number
$
  T (omega_1, dots, omega_q; V_1, dots, V_r) = tensor(T, mu_1 dots mu_q, -nu_1 dots nu_r) omega_(1 mu_1) dots omega_(q mu_q) V_1^(nu_1) dots V_r^(nu_r)
$
Given a basis $\{e_mu}$ and its dual $\{f^mu}$ we can then extract the components by
$
  tensor(T, mu_1 dots mu_q, -nu_1 dots nu_r) = T(f^(mu_1), dots, f^(mu_q);e_(nu_1), dots, e_(nu_r))
$
As a simple example consider a type $(2,1)$ tensor
$
  T(omega, eta, X) = T(omega_mu f^mu, eta_nu f^nu, X^rho e_rho) = omega_mu eta_nu X^rho T(f^mu,f^nu,e_rho) = tensor(T, mu nu, -rho) omega_mu eta_nu X^rho
$
Every manifold also has a natural type $(1,1)$ tensor called $delta$. This takes a one-form $omega$ and a tangent vector $X$ and gives a real number
$
  delta (omega, X) = omega (X) => delta(f^mu, e_nu) = f^mu (e_nu) = delta_nu^mu
$
which is just the Kronecker delta.

Consider two bases $\{e_mu}$ and $\{tilde(e)_mu}$ related by
$
  tilde(e)_nu = tensor(A, mu, -nu) e_mu
$
with $A$ invertible. Let $\{f^mu}$ and $\{tilde(f)^mu}$ be the respective dual bases related by
$
  tilde(f)^rho = tensor(B, rho, -sigma) f^sigma
$
then we require
$
  tilde(f)^rho (tilde(e)_nu) = tensor(B, rho, -sigma) tensor(A, mu, -nu) f^sigma (e_mu) = tensor(A, mu, -nu) tensor(B, rho, -mu) =^! delta^rho_nu => tensor(B, rho, -mu) = tensor((A^(-1)), rho, -mu)
$
so lower components transform using $A$ while upper components transform using $B = A^(-1)$. As an example take a type $(1,2)$ tensor
$
  tensor(tilde(T), mu, - rho nu) = tensor(B, mu, -sigma) tensor(A, tau, -rho) tensor(A, lambda, -nu) tensor(T, sigma, -tau lambda)
$

If a vector is assigned smoothly to every point in $M$ we call it a vector field over $M$. So $V$ is a vector field if $V[f] in cal(F) (M)$ for all $f in cal(F) (M)$. The set of all such vector fields is denoted by $cal(X) (M)$. A vector field $X$ at $p in M$ is denoted by $evaluated(X)_p$ and is an element of $T_p M$. Similarly we define a tensor field of type $(q,r)$ if an element of $cal(T)^q_(r, p) (M)$ is smoothly assigned to each $p in M$. The set of such tensor fields is denoted by $cal(T)^q_r (M)$. So $cal(T)_1^0 (M) = Omega^1 (M)$ is the set of dual vector fields.

#pagebreak()
== The differential map
A smooth map $f : M -> N$ induces a map $f_*$ called the differential map (or pushforward)
$
  f_* : T_p M -> T_(f(p)) N
$
Let $g in cal(F) (N)$ then $g compose f in cal(F) (M)$. A vector $V in T_p M$ acts on $g compose f$ to give a number $V[g compose f]$. We define $f_* V in T_(f(p)) N$ by
$
  (f_* V) [g] equiv V[g compose f]
$
in terms of charts $(U, phi)$ on $M$ and $(V,psi)$ on $N$
$
  (f_* V)[g compose psi^(-1)(y)] equiv V[g compose f compose phi^(-1) (x)]
$
with $x = phi(p)$ and $y = psi(f(p))$. Let $ V = V^mu pdv(, x^mu) " and " f_* V = W^alpha pdv(, y^alpha) $
then
$
  W^alpha pdv(, y^alpha) [g compose psi^(-1) (y)] = V^mu pdv(, x^mu) [g compose f compose phi^(-1) (x)]
$
if $g = y^alpha$ we find
$
  W^alpha = V^mu underbrace(pdv(, x^mu) y^alpha (x), "Jacobian of" #linebreak() f: M -> N)
$
so we can write
$
  f_* V = V^mu pdv(y^alpha, x^mu) pdv(, y^alpha)
$
Let $f : M -> N$ and $g : N -> P$ then the differential map of $g compose f: M -> P$ is
$
  (g compose f)_* = g_* compose f_*
$
To see this we use $x^mu$ on $M$, $y^alpha$ on $N$ and $z^i$ on $P$. Then $g_* compose f_*$ is
$
  g_* (f_* V) & = V^mu pdv(y^alpha, x^mu) g_* (pdv(, y^alpha)) \
              & = V^mu pdv(y^alpha, x^mu) (pdv(z^i, y^alpha) pdv(, z^i)) \
              & = V^mu pdv(z^i, x^mu) pdv(, z^i) \
              & = (g compose f)_* V
$
and we are done.

Any map $f : M -> N$ also induces the map
$
  f^* : T_(f(p))^* N -> T_p^* M
$
which we call the pullback. Taking $V in T_p M$ and $omega in T_(f(p))^* N$ the pullback of $omega$ by $f^*$ is defined by
$
  innerproduct(f^* omega, V) = innerproduct(omega, f_* V)
$
To find the coordinate expression let $omega = omega_alpha dd(y^alpha) in T_(f(p))^* N$. Then
$
  innerproduct(omega_alpha dd(y^alpha), f_* V) &= omega_alpha V^mu pdv(y^alpha, x^mu) innerproduct(dd(y^alpha), pdv(, y^alpha)) \
  &= omega_alpha V^mu pdv(y^alpha, x^mu)
$
if $f^* omega = xi_mu dd(x^mu) in T_p^* M$ then
$
  innerproduct(f^* omega, V) & = xi_mu V^mu innerproduct(dd(x^mu), pdv(, x^mu)) \
                             & = xi_mu V^mu
$
so by comparison
$
  xi_mu = omega_alpha pdv(y^alpha, x^mu)
$

Let $f: M-> N$ and $g : N->P$ as above. Then the pullback for $g compose f : M -> P$ is
$
  (g compose f)^* = g^* compose f^*
$
As above we use $x^mu$ on $M$, $y^alpha$ on $N$ and $z^i$ on $P$. Let $eta = eta_i dd(z^i)$ be a one-form on $P$. Then
$
  innerproduct((g compose f)^* eta, V) &= innerproduct(eta, (g compose f)_* V) \
  &= innerproduct(eta, g_* (f_* V)) \
  &= innerproduct(g^* eta, f_* V) \
  &= innerproduct((f^* compose g^* ) eta, V)
$
where we use $(g compose f)_* = g_* compose f_*$.

Consider a type $(1,1)$ tensor on $M$
$
  tensor(T, mu, -nu) pdv(, x^mu) times.circle dd(x^nu)
$
Let $f : M -> N$ be a diffeomorphism. Then
$
  f_* (tensor(T, mu, -nu) pdv(, x^mu) times.circle dd(x^nu)) &= tensor(T, mu, -nu) f_* (pdv(, x^mu)) times.circle dd(x^nu) \
  &= tensor(T, mu, -nu) pdv(y^alpha, x^mu) pdv(, y^alpha) times.circle underbrace(pdv(x^nu, y^alpha) dd(y^alpha), "change of basis") \
  &= tensor(T, mu, -nu) pdv(y^alpha, x^mu) pdv(x^nu, y^alpha) pdv(, y^alpha) times.circle dd(y^alpha)
$
note that here $f_*$ only acts on vectors, for the one-forms we always just use the inverse Jacobian.

#pagebreak()
== Flows
Let $X$ be a vector field in $M$. An integral curve $x(t)$ of $X$ is a curve in $M$ whose tangent vector at $x(t)$ is $evaluated(X)_x$---so the curve $x(t)$ is tangent to $X$ at every point. For a chart $(U,phi)$ this means
$
  dv(x^mu, t) = X^mu (x(t))
$
with $x^mu (t)$ being the $mu$th component of $phi(x(t))$ and $X = X^mu partial\/dd(x^mu, d: partial)$. This is a system of differential equations which can be solved uniquely.

Let $sigma (t, x_0)$ be an integral curve of $X$ which passes a point $x_0$ at $t=0$ and denote the coordinate by $sigma^mu (t,x_0)$. Then the above becomes
$
  dv(, t) sigma^mu (t,x_0) = X^mu (sigma(t, x_0))
$
with $sigma^mu (0,x_0) = x_0^mu$. The map $sigma: RR times M -> M$ is called the _flow_ generated by $X in cal(X) (M)$. The flow is the collection of all integral curves of $X$, so for each $x_0$ in $M$ $sigma(t, x_0)$ is the integral curve with $sigma(0, x_0) = x_0$. A flow satisfies
$
  sigma(t, sigma^mu (s,x_0)) = sigma(t+s, x_0)
$
To see this note
$
  dv(, t) sigma^mu (t, sigma^mu (s,x_0)) & = X^mu (sigma(t, sigma^mu (s,x_0))) \
                 sigma(0, sigma(s, x_0)) & = sigma(s, x_0)
$
and
$
  dv(, t) sigma^mu (t+s,x_0) &= dv(, (t+s)) sigma^mu (t+s,x_0) = X^mu (sigma(t+s, x_0)) \
  sigma(0+s, x_0) &= sigma(s, x_0)
$
then by uniqueness it follows.

We have just found:
#thm[
  For any point $x in M$ there exists a differentiable map $sigma: RR times M -> M$ such that

  1. $sigma(0, x)=x$.

  2. $t |-> sigma(t, x)$ is a solution to the above.

  3. $sigma(t, sigma^mu (s,x)) = sigma(t+s, x)$
]

We can treat $sigma(t, x)$ as where a particle placed at $x$ for $t = 0$ will be at time $t$.

For fixed $t in RR$ the flow $sigma(t, x)$ is a diffeomorphism from $M$ to $M$ denoted by $sigma_t : M-> M$. Importantly $sigma_t$ is an Abelian group with

1. $sigma_t (sigma_s (x)) = sigma_(t+s) (x)$ or $sigma_t compose sigma_s = sigma_(t+s)$.

2. $sigma_0$ is the identity map.

3. $sigma_(-t) = (sigma_t)^(-1)$.

This group is called the one-parameter group of transformations.

Consider $sigma_epsilon$ for infinitesimal $epsilon$. We find that a point $x$ with coordinate $x^mu$ is mapped to
$
  sigma_epsilon^mu (x) = sigma^mu (epsilon,x) = sigma^mu (0,x) + epsilon evaluated(dv(sigma^mu, epsilon))_(epsilon=0) = x^mu + epsilon X^mu (x)
$
to linear order in $epsilon$. In this case we call the vector field $X$ the infinitesimal generator of $sigma_t$.

Given a vector field $X$ the corresponding flow $sigma$ is called the exponentiation of $X$ since
$
  sigma^mu (t,x) = e^(t X) x^mu
$
This is because we can write
$
  sigma^mu (t,x) &= x^mu + t evaluated(dv(, s) sigma^mu (s,x))_(s=0) + t^2/2! evaluated((dv(, s))^2 sigma^mu (s,x))_(s=0) + dots \
  &= evaluated([1+t dv(, s) + t^2/2! (dv(, s))^2 + dots] sigma^mu (s,x))_(s=0) \
  &equiv evaluated(exp(t dv(, s)) sigma^mu (s,x))_(s=0) = e^(t X) x^mu
$
The flow then satisfies

1. $sigma(0, x) = x = e^(0 X) x$.

2. $display(dv(sigma(t, x), t) = X e^(t X) x = dv(, t) (e^(t X) x))$.

3. $sigma(t, sigma(s, x)) = sigma(t, e^(s X) x) = e^(t X) e^(s X) x = e^((t+s)X) x = sigma(t+s, x)$.

#pagebreak()
== The Lie derivative
Let $sigma(t, x)$ and $tau(t, x)$ be two flows generated by $X$ and $Y$.
$
  dv(sigma^mu (s,x), s) & = X^mu (sigma(s, x)) \
    dv(tau^mu (t,x), t) & = Y^mu (tau(t, x))
$
we want to find the change of $Y$ along $sigma(s, x)$. To do this we need to compare the vector $Y$ at a point $x$ with $Y$ at a point $x' = sigma_epsilon (x)$. The issue is that these vectors belong to different tangent spaces $T_x M$ and $T_(sigma_epsilon (x)) M$. To solve this issue we map $evaluated(Y)_(sigma_epsilon (x))$ to $T_x M$ by the pushforward $(sigma_(-epsilon))_* : T_(sigma_epsilon (x)) M -> T_x M$. Then we can take the difference between $(sigma_(-epsilon))_* evaluated(Y)_(sigma_epsilon (x))$ and $evaluated(Y)_x$. The Lie derivative of a vector field $Y$ along the flow $sigma$ of $X$ is exactly this
$
  cal(L)_X Y = lim_(epsilon -> 0) ( (sigma_(-epsilon))_* evaluated(Y)_(sigma_epsilon (x)) - evaluated(Y)_x )/epsilon
$
as should be clear this pushing or pulling can be done in different ways
$
  cal(L)_X Y &= lim_(epsilon -> 0) ( evaluated(Y)_x - (sigma_epsilon)_* evaluated(Y)_(sigma_(-epsilon) (x)) )/epsilon \
  &= lim_(epsilon -> 0) (evaluated(Y)_(sigma_epsilon (x))-(sigma_epsilon)_* evaluated(Y)_x)/epsilon
$

Let $(U,phi)$ be a chart with coordinates $x$ and let $X = X^mu partial\/dd(x^mu, d: partial)$ and $Y =Y^mu partial\/dd(x^mu, d: partial)$ be vector fields on $U$. Then $sigma_epsilon (x)$ has coordinates $x^mu + epsilon X^mu (x)$ and
$
  evaluated(Y)_(sigma_epsilon (x)) &= Y^mu (x^nu + epsilon X^nu (x)) evaluated(e_mu)_(x+epsilon X) \
  &tilde.eq [Y^mu (x) + epsilon X^nu (x) partial_nu Y^mu (x)] evaluated(e_mu)_(x+epsilon X)
$
if we use $(sigma_(-epsilon))_*$ to map this vector to $x$ we obtain (with coordinates $x^mu - epsilon X^mu (x)$)
$
  & underbrace([Y^mu (x) + epsilon X^lambda (x) partial_lambda Y^mu (x)], V^mu) underbrace(partial_mu [x^nu - epsilon X^nu (x)], partial_mu y^alpha) evaluated(e_nu)_x \
  &= [Y^mu (x) + epsilon X^lambda (x) partial_lambda Y^mu (x)][delta_mu^nu - epsilon partial_mu X^nu (x)] evaluated(e_nu)_x \
  &= Y^mu (x) evaluated(e_mu)_x + epsilon [X^mu (x) partial_mu Y^nu (x) - Y^mu (x) partial_mu X^nu (x)] evaluated(e_nu)_x + cal(O)(epsilon^2)
$
giving
$
  cal(L)_X Y = (X^mu partial_mu Y^nu - Y^mu partial_mu X^nu) e_nu
$

Let $X = X^mu partial_mu$ and $Y = Y^mu partial_mu$ be vector fields in $M$. Then we define the Lie bracket $[X,Y]$ by
$
  [X,Y] f = X [Y[f]] - Y[X[f]]
$
with $f in cal(F) (M)$. Consider
$
  X [Y[f]] & = X^mu pdv(Y[f], x^mu) \
           & = X^mu pdv(, x^mu) (Y^nu pdv(f, x^nu))
$
so
$
  [X,Y] f =[ X^mu pdv(Y^nu, x^mu) - Y^mu pdv(X^nu, x^mu) ] underbrace(pdv(f, x^nu), e_nu f)
$
so we can write
$
  cal(L)_X Y = [X,Y]
$
which is quite nice!

One  can also show that the Lie bracket satisfies

1. bilinearity:
$
     [X,c_1 Y_1+c_2 Y_2] & = c_1 [X,Y_1] + c_2 [X,Y_2] \
  [c_1 X_1 + c_2 C_2, Y] & = c_1 [X_1, Y] + c_2 [X_2, Y]
$

2. skew-symmetry:
$
  [X,Y] = - [Y,X]
$

3. the Jacobi identity:
$
  [[X,Y],Z] + [[Z,X],Y] + [[Y,Z],X] = 0
$

Then we can show
$
  cal(L)_(f X) Y & = f [X,Y] - Y [f] X \
  cal(L)_X (f Y) & = f[X,Y] + X [f] Y
$

#proof[
  Consider
  $
    [f X, Y] (g) &= underbrace((f X) (Y(g)), f X (Y(g))) - underbrace(Y ((f X) (g)), Y (f X(g))) \
    &=^"Leibniz' rule" f X(Y(g)) - f Y(X(g)) - Y(f) X(g) \
    &= f [X,Y] (g) - Y(f)X(g)
  $
  where the Leibniz' rule follows from the product rule for partial derivatives. The second identity is similarly proved.

]

Consider
$
  f_* [X,Y] (g) & = [X,Y] (g compose f) \
                & = X[Y(g compose f)] - Y[X (g compose f)]
$
and
$
  [f_* X, f_* Y] (g) & = f_* X (Y(g compose f)) - f_* Y (X(g compose f)) \
  &=^"already pushforwarded" X [Y(g compose f)] - Y[X(g compose f)]
$
so
$
  f_* [X,Y] = [f_* X, f_* Y]
$

We can also define the Lie derivative of a one-form $omega in Omega^1 (M)$ along $X in cal(X) (M)$ by
$
  cal(L)_X omega equiv lim_(epsilon -> 0) ((sigma_epsilon)^* evaluated(omega)_(sigma_epsilon (x))-evaluated(omega)_x)/epsilon
$
with $evaluated(omega)_x in T_x^* M$. Letting $omega = omega_mu dd(x^mu)$ we do as before finding
$
  (sigma_epsilon)^* evaluated(omega)_(omega_epsilon (x)) = omega_mu (x) dd(x^mu) + epsilon [X^nu (x) partial_nu omega_mu (x) + partial_mu X^nu (x) omega_nu (x)] dd(x^mu)
$
so
$
  cal(L)_X omega = (X^nu partial_nu omega_mu + partial_mu X^nu omega_nu) dd(x^mu)
$

The Lie derivative of $f in cal(F) (M)$ along $sigma_s$ generated by $X$ is
$
  cal(L)_X f & equiv lim_(epsilon -> 0) (f(sigma_epsilon (x))-f(x))/epsilon \
             & = lim_(epsilon -> 0) (f(x^mu + epsilon X^mu (x))-f(x^mu))/epsilon \
             & = X^mu (x) pdv(f, x^mu) = X[f]
$
which is just the directional derivative!

To get the Lie derivative for a general tensor we use the following:
#proposition[
  The Lie derivative satisfies

  $ cal(L)_X (t_1+t_2) = cal(L)_X t_1 + cal(L)_X t_2 $

  with $t_1$ and $t_2$ being tensor fields of the same type and
  $
    cal(L)_X (t_1 times.circle t_2) = (cal(L)_X t_1) times.circle t_2 + t_1 times.circle (cal(L)_X t_2)
  $
  with $t_1$ and $t_2$ being arbitrary tensor fields.
]

#proof[
  The first is obvious.

  For the second consider just $Y in cal(X) (M)$ and $omega in Omega^1 (M)$. We construct $Y times.circle omega$. Then $evaluated(Y times.circle omega)_(sigma_epsilon (x))$ is mapped to $x$ by $(sigma_(-epsilon))_* times.circle (sigma_epsilon)^*$,
  $
    [(sigma_(-epsilon))_* times.circle (sigma_epsilon)^*] evaluated((Y times.circle omega))_(sigma_epsilon (x)) = evaluated([(sigma_(-epsilon))_* Y times.circle (sigma_epsilon)^* omega])_x
  $
  Then it follows that
  $
    cal(L)_X (Y times.circle omega) & = lim_(epsilon -> 0) {evaluated([(sigma_(-epsilon))_* Y times.circle (sigma_epsilon)^* omega])_x - evaluated((Y times.circle omega))_x}/epsilon \
    &= lim_(epsilon -> 0) {(sigma_(-epsilon))_* Y times.circle [(sigma_epsilon)^* omega - omega] + [(sigma_(-epsilon))_* Y - Y] times.circle omega }/epsilon \
    &= Y times.circle (cal(L)_X omega) + (cal(L)_X Y) times.circle omega
  $
  this obviously generalizes to more complicated tensors.
  This is the Leibniz rule.

]

From the Leibniz rule and Jacobi identity it then follows that
$
  cal(L)_([X,Y]) t = cal(L)_X cal(L)_Y t - cal(L)_Y cal(L)_X t
$

#pagebreak()
== Differential forms
We begin by looking at symmetry operations. Considera tensor $omega in cal(T)^0_(r,p) (M)$ then the symmetry operation is defined by
$
  P omega(V_1, dots, V_r) equiv omega(V_(P(1)), dots, V_(P(r)))
$
with $V_i in T_p M$ and $P in S_r$ (the symmetric group), meaning each $P$ is a permutation.

For $omega in cal(T)^0_(r,p) (M)$ we define the symmetrizer $cal(S)$ by
$
  cal(S) omega = 1/r! sum_(P in S_r) P omega
$
with the anti-symmetrizer $cal(A)$ being
$
  cal(A) omega = 1/r! sum_(P in S_r) sgn(P) P omega
$
as their names imply the symmetrizer is totally symmetric ($P cal(S) omega = cal(S) omega$), while the anti-symmetrizer is totally anti-symmetric ($P cal(A) omega = sgn(P) cal(A) omega$).

These are the usual $(dots)$ and $[dots]$ we have used before just with different notation.

#def[Differential form][
  A differential form of order $r$ or an $r$-form is a totally anti-symmetric tensor of type $(0,r)$.
]

We also define the wedge product $and$ of $r$ one-forms by the totally anti-symmetric tensor product:
$
  dd(x^(mu_1)) and dd(x^(mu_2)) and dots and dd(x^(mu_r)) = sum_(P in S_r) sgn(P) dd(x^(mu_(P(1)))) times.circle dd(x^(mu_(P(2)))) times.circle dots times.circle dd(x^(mu_(P(r))))
$
These look like
$
  dd(x^mu) and dd(x^nu) &= dd(x^mu) times.circle dd(x^nu) - dd(x^nu) times.circle dd(x^mu) \
  dd(x^lambda) and dd(x^mu) and dd(x^nu) &= dd(x^lambda) times.circle dd(x^mu) times.circle dd(x^nu) + dd(x^nu) times.circle dd(x^lambda) times.circle dd(x^mu) + dd(x^mu) times.circle dd(x^nu) times.circle dd(x^lambda) \
  &#h(1em)- dd(x^lambda) times.circle dd(x^nu) times.circle dd(x^mu) - dd(x^nu) times.circle dd(x^mu) times.circle dd(x^lambda) - dd(x^mu) times.circle dd(x^lambda) times.circle dd(x^nu)
$

The wedge product has the following properties:

1. $dd(x^(mu_1)) and dots and dd(x^(mu_r)) = 0$ if any index is repeated (this follows from total anti-symmetry).

2. $dd(x^mu_1) and dots and dd(x^mu_r)= sgn(P) dd(x^(mu_(P(1)))) and dots and dd(x^(mu_P(r)))$ (since swapping two indices pick up a $minus$)

3. $dd(x^mu_1) and dots and dd(x^mu_r)$ is linear in each $dd(x^mu)$ (since the tensor product is multi-linear).

So it is a multi-linear totally anti-symmetric map.

Consider the vector space of $r$-forms at $p in M$ which we denote by $Omega^r_p (M)$, then the $r$-forms form a basis. Any $omega in Omega_p^r (M)$ can then be written as
$
  omega = 1/r! omega_(mu_1 dots mu_r) dd(x^mu_1) and dots and dd(x^mu_r)
$
where the $omega_(mu_1 dots mu_r)$ are totally anti-symmetric. To see why consider the components of a type $(0,2)$ tensor $omega_(mu nu)$. These can be decomposed into a symmetric part $sigma_(mu nu)$ and anti-symmetric part $alpha_(mu nu)$ by
$
  sigma_(mu nu) & = omega_((mu nu)) equiv 1/2 (omega_(mu nu) + omega_(nu mu)) \
  alpha_(mu nu) & = omega_([mu nu]) equiv 1/2 (omega_(mu nu)- omega_(nu mu))
$
But $sigma_(mu nu) dd(x^mu) and dd(x^nu) = 0$ while $alpha_(mu nu) dd(x^mu) and dd(x^nu) = omega_(mu nu) dd(x^mu) and dd(x^nu)$.

We define $Omega_r^0 (M) = RR$ while clearly $Omega_r^1 (M) = T_p^* M$. The dimension of $Omega_p^r (M)$ is
$
  binom(m, r) = m!/((m-r)! r!)
$
And if $r > m$ then the wedge product is zero since some index must appear more than once. The equality $binom(m, r) = binom(m, m-r)$ implies $dim Omega_p^r (M) = dim Omega_p^(m-r) (M)$, meaning they must be isomorphic.

#pagebreak()
== The exterior product
We now define the exterior product of a $q$-form and $r$-form $and : Omega_p^q (M) times Omega_p^r (M) -> Omega_p^(q+r) (M)$. Let $omega in Omega_p^q (M)$ and $xi in Omega_p^r (M)$. Then the action of $(omega and xi)$ on $q+r$ vectors is defined by
$
  (omega and xi) (V_1, dots, V_(q+r)) = 1/(q! r!) sum_(P in S_(q+r)) sgn(P) omega(V_(P(1)), dots, V_(P(q))) xi (V_(P(q+1)), dots, V_(P(q+r)))
$
with $V_i in T_p M$ (as before if $q + r > m$ this vanishes). We can then define an algebra
$
  Omega_p^* (M) equiv Omega_p^0 (M) plus.circle Omega_p^1 (M) plus.circle dots plus.circle Omega_p^m (M)
$
with $Omega^*_p (M)$ being the space of all differential forms at $p$, this guy is closed under the exterior product.

Letting $xi in Omega_p^q (M)$, $eta in Omega_p^r (M)$ and $omega in Omega_p^s (M)$ the exterior product satisfies:

1. $xi and eta = (-1)^(q r) eta and xi$ (since all $r$ $dd(x^mu)$ of $eta$ need to move past $q$ $dd(x^nu)$ of $xi$) so $eta and eta = 0$ for $q$ odd.

2. $(xi and eta) and omega = xi and (eta and omega)$ (follows from associativity of the tensor product).

To each point on a manifold $M$ we can smoothly assign an $r$-form. The space of smooth $r$-forms on $M$ is denoted by $Omega^r (M)$.

#def[Exterior derivative][
  The exterior derivative $dif_r$ is a map $Omega^r (M) -> Omega^(r+1) (M)$ which act on an $r$-form as
  $
    dif_r omega = 1/r! (pdv(, x^nu) omega_(mu_1 dots mu_r)) dd(x^nu) and dd(x^(mu_1)) and dots and dd(x^(mu_r))
  $
  typically this is just written as $dif omega$.
]

As an example consider the $r$-forms in three-dimensional space:

1. $omega_0 = f(x,y,z)$.

2. $omega_1 = omega_x dd(x) + omega_y dd(y) + omega_z dd(z)$.

3. $omega_2 = omega_(x y) dd(x) and dd(y) + omega_(y z) dd(y) and dd(z) + omega_(z x) dd(z) and dd(x)$.

4. $omega_3 = omega_(x y z) dd(x) and dd(y) and dd(z)$.

The exterior derivative acts on each as:

1. $display(dif omega_0 = pdv(f, x) dd(x)+pdv(f, y) dd(y) + pdv(f, z) dd(z))$ (gradient).

2. $display(dif omega_1 = (pdv(omega_y, x)-pdv(omega_x, y)) dd(x) and dd(y) + (pdv(omega_z, y)-pdv(omega_y, z)) dd(y) and dd(z) + (pdv(omega_x, z) - pdv(omega_z, x)) dd(z) and dd(x))$ (curl).

3. $display(dif omega_2 = (pdv(omega_(y z), x) + pdv(omega_(z x), y) + pdv(omega_(x y), z)) dd(x) and dd(y) and dd(z))$ (divergence).

4. $dif omega_3 = 0$.

We can show that for $xi in Omega^q (M)$ and $omega in Omega^r (M)$ (the Leibniz rule)
$
  dif (xi and omega) = dif xi and omega + (-1)^q xi and dif omega
$
to see this consider
$
  dif (xi and omega) &= sum dif (xi_(mu_1 dots mu_q) omega_(nu_1 dots nu_r)) and underbrace(dd(x^(mu_1)) and dots and dd(x^(mu_q)), xi) and underbrace(dd(x^(nu_1)) and dots and dd(x^(nu_r)), omega) \
  &= sum (dif xi_dots omega_dots + xi_dots dif omega_dots) and dd(x^(mu_1)) and dots and dd(x^(mu_q)) and dd(x^(nu_1)) and dots and dd(x^(nu_r)) \
  &= dif xi and omega + (-1)^q xi and dif omega
$
where the factor $(-1)^q$ appears since we need to move $dif omega$ past $q$ $dd(x^(mu_i))$.

Another useful identity is
$
  dif^2 = 0
$
which is easily shown by taking
$
  omega = 1/r! omega_(mu_1 dots mu_r) dd(x^(mu_1)) and dots and dd(x^(mu_r)) in Omega^r (M)
$
then
$
  dif^2 omega = 1/r! pdv(omega_(mu_1 dots mu_r), x^lambda, x^nu) dd(x^lambda) and dd(x^nu) and dd(x^(mu_1)) and dots dd(x^(mu_r)) = 0
$
this vanishes since $partial^2$ is symmetric with respect to $lambda$ and $nu$ while $dd(x^lambda) and dd(x^nu)$ is anti-symmetric.

As an example from physics consider the four-potential $A = (phi.alt, A)$. This is a one-form $A = A_mu dd(x^mu)$. The Faraday tensor is defined as $F= dd(A)$. Then the two homogeneous Maxwell equations can be written compactly as $dd(F) = dd((dd(A))) = 0$ which we call the Bianchi identity.

We have seen that a map $f : M -> N$ induces a pullback $f^* : T^*_(f(p)) N -> T_p^* M$ and $f^*$ is naturally extended to tensors of type $(0,r)$. Since $r$-forms are exactly such tensors this applies equally well. Let $omega in Omega^r (N)$ and let $f$ be a map $M -> N$. At each $f(p) in N$ the map $f$ induces a pullback $f^* : Omega^r_(f(p)) N -> Omega^r_p M$ by
$
  (f^* omega) (X_1, dots, X_r) equiv omega(f_* X_1, dots, f_* X_r)
$
with $X_i in T_p M$ and $f_*$ being the differential map $T_p M -> T_(f(p)) N$. One can show given $xi, omega in Omega^r (N)$ with $f : M -> N$ we have
$
     dd((f^* omega)) & = f^* (dd(omega)) \
  f^* (xi and omega) & = (f^* xi) and (f^* omega)
$
#proof[
  Let
  $
    omega = 1/r! omega_(mu_1 dots mu_r) (y) dd(y^(mu_1)) and dots and dd(y^(mu_r))
  $
  the pullback is
  $
    f^* omega &= 1/r! (omega_(mu_1 dots mu_r) compose f) f^* (dd(y^(mu_1))) and dots and f^* (dd(y^(mu_r))) \
    &= 1/r! (omega_(mu_1 dots mu_r) compose f) pdv(y^(mu_1), x^(i_1)) dd(x^(i_1)) and dots and pdv(y^(mu_r), x^(i_r)) dd(x^(i_r))
  $
  the exterior derivative is then
  $
    dd((f^* omega)) = 1/r! underbrace(pdv((omega_(mu_1 dots mu_r) compose f), x^j) dd(x^j), display(pdv((omega_(mu_1 dots mu_r) compose f), y^nu) pdv(y^nu, x^j) dd(x^j))) and pdv(y^(mu_1), x^(i_1)) dd(x^(i_1)) and dots and pdv(y^(mu_r), x^(i_r)) dd(x^(i_r))
  $
  this is clearly the same as
  $
    f^* (dd(omega)) &= f^* (1/r! pdv(omega_(mu_1 dots mu_r), y^nu)) dd(y^nu) and dd(y^(mu_1)) and dots and dd(y^(mu_r)) \
    &= 1/r! pdv(omega_(mu_1 dots mu_r), y^nu) pdv(y^nu, x^j) dd(x^j) and dots and pdv(y^(mu_r), x^(i_r)) dd(x^(i_r))
  $
  For the other one we have
  $
    (f^* xi) and (f^* omega) &= 1/(q! r!) (xi_(mu_1 dots mu_q) compose f) (omega_(nu_1 dots nu_r) compose f) f^* (dd(y^(mu_1))) and dots \ & #h(3em) dots and f^* (dd(y^(mu_q))) and f^* (dd(y^(nu_1))) and dots and f^* (dd(y^(nu_r)))
  $
  and
  $
    f^* (xi and omega) &= f^* (1/(q! r!) xi_(mu_1 dots mu_q) omega_(nu_1 dots nu_r) dd(y^(mu_1)) and dots dd(y^(nu_r)) )
  $
  which are the same.
]

The exterior derivative induces
$
  0 ->^i Omega^0 (M) ->^(dif_0) Omega^1 (M) ->^(dif_1) dots ->^(dif_(m-2)) Omega^(m-1) (M) ->^(dif_(m-1)) Omega^m (M) ->^(dif_m) 0
$
this is called the de Rham complex. Since $dif^2 = 0$ we have by definition $im dif_r subset ker dif_(r+1)$. An element of $ker dif_(r)$ is called a closed $r$-form while an element of $im dif_(r-1)$ is called an exact $r$-form. So $omega in Omega^r (M)$ is closed if $dd(omega) = 0$ and exact if there exists a ($r-1$)-form $psi$ such that $omega = dd(psi)$. The quotient space $ker dif_r \/ im dif_(r-1)$ is called the $r$th de Rham cohomology group.

#pagebreak()
== The interior product
The other important operation is the interior product $i_X : Omega^r (M) -> Omega^(r-1) (M)$ with $X in cal(X) (M)$. For $omega in Omega^r (M)$ define
$
  i_X omega (X_1,dots,X_(r-1)) equiv omega (X,X_1,dots,X_(r-1))
$
with $X = X^mu partial\/dd(x^mu, d: partial)$ and $omega = (1\/r!) omega_(mu_1 dots mu_r) dd(x^(mu_1)) and dots dd(x^(mu_r))$ we have
$
  i_X omega &= 1/(r-1)! X^nu omega_(nu mu_2 dots mu_r) dd(x^(mu_2)) and dots and dd(x^(mu_r)) \
  &= 1/r! sum_(s=1)^r X^(mu_s) omega_(mu_1 dots mu_s dots mu_r) (-1)^(s-1) dd(x^(mu_1)) and dots and underbrace(overline(dd(x^(mu_s))), "entry omitted") and dots and dd(x^(mu_r))
$
As an example take $(x,y,z)$ to be coordinates of $RR^3$. Then
$
  i_(e_x) (dd(x) and dd(y)) = dd(y)";  " i_(e_x) (dd(y) and dd(z)) = 0";  " i_(e_x) (dd(z) and dd(x)) = - dd(z)
$

The Lie derivative can be written neatly in terms of the interior product. Let $omega = omega_mu dd(x^mu)$ be a one-form and consider
$
  (dif i_X + i_X dif) omega &= dif (X^mu omega_mu) + i_X [1/2 (partial_mu omega_nu - partial_nu omega_mu) dd(x^mu) and dd(x^nu)] \
  &= (omega_mu partial_nu X^mu + X^mu partial_nu omega_mu) dd(x^nu) + X^mu (partial_mu omega_nu - partial_nu omega_mu) dd(x^nu) \
  &= (omega_mu partial_nu X^mu + X^mu partial_mu omega_nu) dd(x^nu) \
  &eq cal(L)_X omega
$
so we obtain
$
  cal(L)_X omega = (dif i_X + i_X dif) omega
$
which is referred to as Cartan's magic formula. This also holds for a general $r$-form.

#proof[

  For a general $r$-form $omega = (1\/r!) omega_(mu_1 dots mu_r) dd(x^(mu_1)) and dots and dd(x^(mu_r))$ we have
  $
    cal(L)_X omega &= lim_(epsilon -> 0) ( (sigma_epsilon)^* evaluated(omega)_(sigma_epsilon (x)) - evaluated(omega)_x )/epsilon \
    &= X^nu 1/r! partial_nu omega_(mu_1 dots mu_r) dd(x^(mu_1)) and dots and dd(x^(mu_r)) + sum_(s=1)^r partial_(mu_s) X^nu 1/r! omega_(mu_1 dots underbracket(nu, s) dots mu_r) dd(x^(mu_1)) and dots and dd(x^(mu_r))
  $
  and
  $
    (dif i_X + i_X dif) omega &= 1/r! sum_(s=1)^r (partial_nu X^(mu_s) omega_(mu_1 dots mu_s dots mu_r) + X^(mu_s) partial_nu omega_(mu_1 dots mu_s dots mu_r)) \
    &#h(1em) times (-1)^(s-1) dd(x^nu) and dd(x^(mu_1)) and dots and overline(dd(x^(mu_s))) and dd(x^(mu_r)) \
    &#h(1em) + 1/r! [X^mu partial_nu omega_(mu_1 dots mu_r) dd(x^(mu_1))and dots and dd(x^(mu_r)) \
      &#h(1em) + sum_(s=1)^r X^(mu_s) omega_(mu_1 dots mu_s dots mu_r) (-1)^(s-1) dd(x^(nu)) and dd(x^(mu_1)) and dots and overline(dd(x^(mu_s))) and dots and dd(x^(mu_r))] \
    &= 1/r! sum_(s=1)^r [partial_nu X^(mu_s) omega_(mu_1 dots mu_s dots mu_r) (-1)^(s-1) dd(x^nu) and dd(x^(mu_1)) and dots and overline(dd(x^(mu_s)))and dots and dd(x^(mu_r)) \
      &#h(1em) + 1/r! X^(nu) partial_nu omega_(mu_1 dots mu_r) dd(x^(mu_1) and dots and dd(x^(mu_r))) ]
  $
  interchanging the roles of $mu_s$ and $nu$ shows that
  $
    (dif i_X + i_X dif) omega = cal(L)_X omega
  $
]

Let $X,Y in cal(X) (M)$ and $omega in Omega^r (M)$ then
$
  i_[X,Y] omega = X (i_Y omega) - Y (i_X omega)
$
and
$
  i_X (omega and eta) = i_X omega and eta + (-1)^r omega and i_X eta
$
which is proved in the same way as the Leibniz rule for $dif(dot and dot)$, and
$
  i_X^2 = 0
$
this follows immediately by anti-symmetry since two indices will be the same. This can be used to show
$
  [cal(L)_X,i_X] = 0
$
which generalizes to
$
  [cal(L)_X,i_Y] = i_[X,Y]
$

#proof[

  For
  $
    i_[X,Y] omega = X(i_Y omega) - Y (i_X omega)
  $
  consider
  $
    X(i_Y omega) &= X omega(Y, Z_1, dots) \
    &= (cal(L)_X omega) (Y,Z_1,dots) + sum_(j=0)^(r-1) omega(Z_0, dots, cal(L)_X Z_j, dots)
  $
  here we use (essentially product rule)
  $
    cal(L)_X (omega(Y, Z_1, dots)) = X (omega(Y, Z_1, dots)) - sum_(j=0)^(r-1) omega(Z_0, dots, cal(L)_X Z_j, dots)
  $
  so
  $
    X omega(Y, dots) - Y omega(X, dots) &= omega(underbrace(cal(L)_X Y- cal(L)_Y X, [X,Y]), Z_1, dots, Z_(r-1)) \
    &= i_[X,Y] omega(dots)
  $

  The proof for
  $
    [cal(L)_X, i_Y] = i_[X,Y]
  $
  is very similar.
]

#pagebreak()
== Integration
\* Tong


