//**** init-ting
#import "@preview/physica:0.9.5": *
#import "chpt-temp.typ": *
#import "@preview/mannot:0.3.0": *
#import "@preview/cetz:0.4.1" // drawings

#show: thmrules.with(qed-symbol: $square$)
#show: chpt-note.with()

= Manifolds
The space we work in is what we call a manifold---generally it can be thought of as a curved, $n$-dimensional space, where any singular patch looks locally like $RR^n$. We will slowly begin associating various mathematical objects to this space.

As a physicist the end goal is to understand spacetime as a manifold and the various structures living on it.

== Topological spaces
As with many other mathematical definitions there is usually a lot of backstory needed for completeness. Here we recall the definition of a topological space:

#def[Topological space][
  A topological space $M$ is a set of points with a topology $cal(T)$. This is a collection of open subsets ${cal(O)_a subset M}$ obeying:

  1. Both the set $M$ and the empty set $emptyset$ are open subsets, $M in cal(T)$ and $emptyset in cal(T)$.

  2. The intersection of a finite number of open sets also an open set. So if $cal(O)_1 in cal(T)$ and $cal(O)_2 in cal(T)$ then $cal(O)_1 inter cal(O)_2 in cal(T)$.

  3. The union on any number of open sets is also an open set: So if $cal(O)_gamma in cal(T)$ then $union_gamma cal(O)_gamma in cal(T)$.
]

Given a point $p in M$ we call $cal(O) in cal(T)$ a neighbourhood of $p$ if $p in cal(O)$. Since we want nice topological spaces we require they are Hausdorff: for any $p, q in M$ with $p eq.not q$ there exists $cal(O)_1, cal(O)_2 in cal(T)$ such that $p in cal(O)_1$ and $q in cal(O)_2$ and $cal(O)_1 inter cal(O)_2 = emptyset$---meaning it is possible to always separate any two points $p, q in M$ using two disjoint open subsets.

#def[Homeomorphism][
  A homeomorphism between topological spaces $(M,cal(T))$ and $(tilde(M),tilde(cal(T)))$ is a map $f: M -> tilde(M)$ which is

  1. Injective: for $p eq.not q$, $f(p) eq.not f(q)$.

  2. Surjective: $f(M) = tilde(M)$ meaning for each $tilde(p) in tilde(M)$ there exists a $p in M$ such that $f(p) = tilde(p)$.

  3. Bicontinuous. Meaning $f$ and $f^(-1)$ are both continuous. We define continuity as usual: $f$ is continous if for all $tilde(cal(O)) in tilde(cal(T))$, $f^(-1) (tilde(cal(O))) in cal(T)$.

]

== Differentiable manifolds
This is what we care about.

#def[Differentiable manifold][
  An $n$-dimensional differentiable manifold is a Hausdorff topological space $M$ such that

  1. $M$ is locally homeomorphic to $RR^n$. Meaning for each $p in M$ there is an open set $cal(O)$ such that $p in cal(O)$ (neighbourhood) and a homeomorphism $phi.alt : cal(O) -> U$ with $U$ an open subset of $RR^n$.

  2. Take two open subsets $cal(O)_alpha$ and $cal(O)_beta$ that overlap: $cal(O)_alpha inter cal(O)_beta eq.not emptyset$. We require that the maps $phi.alt_alpha: cal(O)_alpha -> U_alpha$ and $phi.alt_beta : cal(O)_beta -> U_beta$ are compatible, meaning that $phi.alt_beta compose phi.alt_alpha^(-1) : phi.alt_alpha (cal(O)_alpha inter cal(O)_beta) -> phi.alt_beta (cal(O)_alpha inter cal(O)_beta)$ is smooth (i.e. infinitely differentiable on $C^oo$), as is its inverse.
]

We call the maps $phi.alt_alpha$ charts and the collection of charts an atlas. Each chart can be thought of as providing a coordinate system to label $cal(O)_alpha$ of $M$. The coordinate associated to $p in cal(O)_alpha$ is
$
  phi.alt_alpha (p) = (x^1 (p), dots, x^n (p)) = x^mu (p)
$
the maps $phi.alt_beta compose phi.alt_alpha^(-1)$ then take us between different coordinate systems and is why we call them transition functions. The compatibily condition ensures there is no inconsistency between the various coordinate systems.

=== Diffeomorphism
The reason why we might want to locally map a manifold to $RR^n$ is because we know $RR^n$.

For example we say a map $f: M -> RR$ is smooth if the map $f compose phi.alt^(-1) : U -> RR$ is smooth for all $phi.alt$. Similarly a map $f : M -> N$ is smoth if the map $psi compose f compose phi.alt^(-1): U->V$ is smooth for all $phi.alt : M -> U subset RR^M$ and $psi: N -> V subset RR^N$.

A diffeomorphism is a smooth homeomorphism $f : M -> N$---so an invertible, smooth map between manifolds $M$ and $N$ that has a smooth inverse. If such a map exists $M$ and $N$ are said to be diffeomorphic.

#pagebreak()
= Tangent spaces
Now we want to understand how to do calculus on manifolds, starting with differentiation. Consider a function $f : M -> RR$. To differentiate this at some point $p$ we introduce the chart $phi.alt = (x^1, dots, x^n)$ in a neighbourhood of $p$. Then we can construct $f compose phi.alt^(-1) : U -> RR$ with $U subset RR^n$. Since we know how to differentiate on $RR^n$ we then get a way to differentiate on $M$:
$
  evaluated(dv(f, x^mu))_p equiv evaluated(dv((f compose phi.alt^(-1)), x^mu))_(phi.alt(p))
$
we would prefer this be coordinate independent.

== Tangent vectors
We consider smooth functions over a manifold $M$ and we denote the set of all smooth functions by $C^oo (M)$.

#def[Tangent vector][
  A tangent vector $X_p$ is an object that differentiates functions at a point $p in M$. In particular $X_p : C^oo (M) -> RR$ obeying:

  1. Linearity: $X_p (f+g) = X_p (f) + X_p (g)$ for all $f, g in C^oo (M)$.

  2. $X_p (f) = 0$ when $f$ is the constant function.

  3. Leibnizarity (the product rule): $X_p (f g) = f(p) X_p (g) + X_p (f) g(p)$ for all $f, g in C^oo (M)$.

]

2. and 3. combine giving: $X_p (a f) = a X_p (f)$ for $a in RR$. Tangent vectors tell us how things change in a given directions---by differentiating.

An example of a tangent vector is
$
  evaluated(partial_mu)_p equiv evaluated(pdv(, x^mu))_p
$
which acts on functions as above.

#proof[
  For 1:
  $
    evaluated(partial_mu (f + g))_p &= evaluated(pdv(, x^mu) ((f + g)compose phi.alt^(-1)))_(phi.alt(p)) \
    &= evaluated(pdv(, x^mu) (f compose phi.alt^(-1)))_phi.alt(p) + evaluated(pdv(, x^mu) (g compose phi.alt^(-1)))_phi.alt(p) \
    &= evaluated(partial_mu f)_p + evaluated(partial_mu g)_p
  $
  and 2:
  $
    evaluated(partial_mu c)_p &= evaluated(pdv(, x^mu) overbrace((c compose phi.alt^(-1)), "still constant"))_phi.alt(p) \
    &= 0
  $
  and 3:
  $
    evaluated(partial_mu (f g))_p &= evaluated(pdv(, x^mu) ((f g) compose phi.alt^(-1)))_phi.alt(p) \
    &= evaluated(pdv(, x^mu) (f compose phi.alt^(-1))(g compose phi.alt^(-1)))_phi.alt(p) \
    &= evaluated(pdv((f compose phi.alt^(-1)), x^mu))_phi.alt(p) (g compose phi.alt^(-1)) (phi.alt (p)) + (f compose phi.alt^(-1)) (phi.alt(p)) evaluated(pdv((g compose phi.alt^(-1)), x^mu))_phi.alt(p) \
    &= evaluated(partial_mu f)_p g(p) + f(p) evaluated(partial_mu g)_p
  $
  so $evaluated(partial_mu)_p$ is a tangent vector.
]

#thm[
  The set of all tangent vectors at a point $p$ form an $n$-dimensional vector space. We call this the tangent space $T_p (M)$. The tangent vectors $evaluated(partial_mu)_p$ provide a basis for $T_p (M)$, meaning we can write any tangent vector as
  $
    X_p = X^mu evaluated(partial_mu)_p "with" X^mu = X_p (x^mu)
  $
]

#proof[
  We being by defining $F = f compose phi.alt^(-1) : U -> RR$ with $phi.alt = (x^1, dots, x^n)$ a chart on a neighbourhood of $p$. Then in some neighbourhood of $p$ we can always write
  $
    F(x) = F(x^mu (p)) + (x^mu - x^mu (p)) F_mu (x)
  $
  where we introduce $n$ new functions $F_mu (x)$ (basically Taylor expansion). Acting with $partial_mu$ on both sides and evaluating at $x^mu = x^mu (p)$ we find
  $
    evaluated(pdv(F, x^mu))_x(p) = F_mu (x(p))
  $
  Now we define $n$ functions on $M$ by $f_mu = F_mu compose phi.alt$. Then for any $q in M$ the above becomes
  $
    f compose underbrace(phi.alt^(-1) (x^mu (q)), q) = f compose underbrace(phi.alt^(-1) (x^mu (p)), p) + (x^mu (q) - x^mu (p)) [f_mu compose underbrace(phi.alt^(-1) (x^mu (q)), q)]
  $
  so in the neighbourhood of $p$ we can write
  $
    f(q) = f(p) + (x^mu (q) - x^mu (p)) f_mu (q)
  $
  and at $q = p$:
  $
    f_mu (p) = F_mu compose phi.alt(p) = F_mu (x(p)) = evaluated(pdv(F, x^mu))_x(p) = evaluated(pdv(f, x^mu))_p
  $
  the tangent vecotr $X_p$ acts on $f$ as
  $
    X_p (f) &= X_p (f(p)+(x^mu - x^mu (p))f_mu) \
    &= X_p underbrace((f(p)), "constant") + X_p (x^mu-underbrace(x^mu (p), "constant")) f_mu (p) + underbrace((x^mu (p)-x^mu (p)), 0)X_p (f_mu) \
    &= X_p (x^mu) evaluated(pdv(f, x^mu))_p
  $
  meaning the tangent vector can be written as
  $
    X_p = X^mu evaluated(pdv(, x^mu))_p
  $
  these are a basis for $T_p (M)$ since they span the space, and are linearly independent---suppose we have $alpha = evaluated(alpha_mu partial_mu)_p = 0$ then acting on $f = x^nu$ gives $a(x^nu) = a_mu evaluated(partial_mu x^nu)_p = alpha_nu = 0$

]

A given tangent vector $X_p$ exists independent of coordinate choice, but the basis above: ${evaluated(partial_mu)_p}$ clearly depends on our choice of coordinates through $phi.alt$ and $x^mu$. Any such basis is called a coordinate basis. Other bases ${e_mu}$ are not defined like this, and a therefore called non-coordinate bases.

=== Change of basis
We could pick some other $tilde(phi.alt)$ with $tilde(x)^mu$ then
$
  X_p = X^mu evaluated(pdv(, x^mu))_p = tilde(X)^mu evaluated(pdv(, tilde(x)^mu))_p
$
by the chain rule we can write
$
  X_p (f) = X^mu evaluated(pdv(f, x^mu))_p = X^mu evaluated(pdv(tilde(x)^nu, x^mu))_phi.alt(p) evaluated(pdv(f, tilde(x)^nu))_p
$
this can be considered a change in the basis vectors by
$
  evaluated(pdv(, x^mu))_p = evaluated(pdv(tilde(x)^nu, x^mu))_phi.alt(p) evaluated(pdv(, tilde(x)^nu))_p
$
or as a change in the components of the vector by
$
  tilde(X)^nu = X^mu evaluated(pdv(tilde(x)^nu, x^mu))_phi.alt(p)
$
components that transform like this are called contravariant.

== Vector fields
A vector field $X$ is defined to be a smooth assignment of a tangent vector $X_p$ to each point $p in M$---so giving a function to a vector field gives back the differentiation of this function. Meaning $X:C^oo (M) -> C^oo (M)$ defined by
$
  (X(f))(p)=X_p (f)
$
the space of all vector fields on $M$ is denoted $cal(X)(M)$.

We can write the vector field as
$
  X = X^mu pdv(, x^mu)
$
with $X^mu$ being smooth functions on $M$.

=== Commutator
Consider two vector fields $X, Y in cal(X) (M)$. Then
$
  X Y (f g) & = X (f Y(g) + Y(f) g) \
            & = X(f) Y(g) + f X Y (g) + g X Y (f) + X (g) Y (f) \
            & eq.not f X Y (g) + g X Y (f)
$
so $X Y$ is not a vector field. But we can take the commutator
$
  [X,Y] (f) = X(Y(f))-Y(X(f))
$
or Lie bracket and this is a vector field. It can be written as
$
  [X,Y] (f) &= X^mu pdv(, x^mu) (Y^nu pdv(f, x^nu)) - Y^mu pdv(, x^mu) (X^nu pdv(f, x^nu)) \
  &= (X^mu pdv(Y^nu, x^mu)- Y^mu pdv(X^nu, x^mu)) pdv(f, x^nu)
$
for all $f in C^oo (M)$ so we can write
$
  [X,Y] = (X^mu pdv(Y^nu, x^mu) - Y^mu pdv(X^nu, x^mu)) pdv(, x^nu)
$
and one can check that the Jacobi identity is satisfied
$
  [X,[Y,Z]]+[Y,[Z,X]]+[Z,[X,Y]]=0
$
which ensures that the set of all vector fields on a manifold $M$ is a Lie algebra.

== Lie derivative
Above we saw how to differentiate a function by introducing the vector field $X$, and treating $X(f)$ as the derivative of $f$ along the direction of $X$. We would like to know how to differentiate a vector field. So how can we differentiate a vector field $Y$ in the direction of $X$?

=== Push-forward and pull-back
Suppose we have a diffeomorphism $phi : M -> N$ between two manifolds $M$ and $N$. Then we can import structures between the manifolds.

Take a function $f : N -> RR$ then we can construct a new function $(phi^* f) : M -> RR$ where
$
  (phi^* f) (p) = f compose phi.alt (p) = f(phi.alt(p)) \
$
and
$
  phi^* : T_phi(p) (M) -> T_p (M)
$
so we drag objects defined on $N$ onto $M$ and denote this map by the pull-back. Introducing $x^mu$ on $M$ and $y^alpha$ on $N$, then $phi (x) = y^alpha (x)$ and
$
  (phi^* f)(x) = f(y(x))
$

Analogously we can go the other way: given a vector field $Y$ on $M$, we can define a new vector field ($phi_* Y$) on $N$. If we have a function $f:N -> RR$ then the vector field $(phi_* Y)$ on $N$ acts as
$
  (phi_* Y) (f) = Y(phi^* f)
$
and
$
  phi_* : T_p (M) -> T_phi(p) (M)
$
using the map to push objects on $M$ onto $N$ is called the push-forward---the push-forward is the action of $Y$ on the pull-back of $f$.

With $Y = Y^mu partial\/partial x^mu$ being the vector field on $M$ we can write the vector field on $N$ as
$
  (phi_* Y) (f) = Y^mu pdv(f(y(x)), x^mu) = Y^mu pdv(y^alpha, x^mu) pdv(f(y), y^alpha)
$
or componentwise
$
  (phi_* Y)^alpha = Y^mu pdv(y^alpha, x^mu)
$

=== The Lie derivative
Diffeomorphisms and coordinate transformations turn out to be two sides of the same coin. Consider a manifold $M$ with $x^mu : M -> RR$, to change coordinates we can introduce new functions $y^alpha : M -> RR$ or we could introduce a diffeomorphism $phi : M -> M$, after which the coordinates would be the pull-backs $(phi^* x)^mu : M -> RR^n$.

This is useful because it allows us to compare tangent vectors at different points (from different tangent spaces). By forming the difference between the tangent vector  at some point $p$ and the pull-back---the value at $phi (p)$ pulled back to $p$. This leads to the construction of a new differential operator: the Lie derivative. To do this we consider a one-parameter family of diffeomorphisms $sigma_t: RR times M -> M$ such that for each $t in RR$ the $sigma_t$ is a diffeomorphism and $sigma_s compose sigma_t = sigma_(s + t)$. These arise naturally from vector fields. If we consider what happens to a point $p$ under all $sigma_t$ then we get a curve in $M$, and this happens for every point $p in M$. Then we can define a vector field $X$ to be the set of tangent vectors to each of these curves at every point, for $t = 0$. We can also reverse this to define a family of diffeomorphisms from any vector field. We define the curves of the vector field to be those that solve
$
  dv(x^mu (sigma_t), t) = X^mu (x) =>^"infinitesimal" x^mu (t) = x^mu (0) + t X^mu (x) + cal(O)(t^2)
$
we refer to $sigma_t$ as the _flow_ since $x^mu (t) = x^mu (sigma_t (p))$ and $X$ as the _generator_. Then we can consider how fast a tangent vector changes along these curves. We can define this change by
$
  Delta_t Y_p = ((sigma_(-t))_* Y_(sigma_t (p)))_p - Y_p
$

#figure(
  image("liederiv.png", width: 60%),
  caption: [Construction of the Lie derivative---taken from Tong.],
)

We now define the Lie derivative of $Y$ along $X$ as
$
  cal(L)_X Y = lim_(t -> 0) (Delta_t Y_p)/t
$
where $X = X^mu partial_mu$ and $Y = Y^mu partial_mu$ are vector fields on $M$. The flow of $X$ is $sigma_t : M -> M$ which moves points along curves of $X$. Before tackling this guy consider a normal function, in this case
$
  cal(L)_X f = lim_(t -> 0) (f(sigma_t (x))- f(x))/t = evaluated(dv(f(sigma_t (x)), t))_(t = 0) = pdv(f, x^mu) evaluated(dv(x^mu, t))_(t=0) = X^mu (x) pdv(f, x^mu) = X(f)
$
so $cal(L)_X f = X (f)$! Now for a vector field $Y$ we have
$
  cal(L)_X Y & = cal(L)_X (Y^mu partial_mu) \
             & = (cal(L)_X Y^mu) partial_mu + Y^mu (cal(L)_X partial_mu)
$
we just found the first term since $Y^mu$ is a function. We still need the second
$
  cal(L)_X partial_mu = lim_(t-> 0) ((sigma_(-t))_* partial_mu - partial_mu)/t
$
we compute (for $y^alpha -> x^mu (t)$ where $x^mu (t)$ is the infinitesimal coordinate change induced by $sigma_(-t) => x^mu (t) = x^mu (0) - t X^mu + cal(O)(t^2)$)
$
  (sigma_(-t))_* partial_mu &= underbrace((delta_mu^nu - t pdv(X^nu, x^mu)+ dots), "Jacobian") partial_nu \
  &= partial_mu - t pdv(X^nu, x^mu) partial_nu + dots
$
giving
$
  cal(L)_X partial_mu = - pdv(X^nu, x^mu) partial_nu
$
so
$
  cal(L)_X Y & = X^nu pdv(Y^mu, x^nu) partial_mu -Y^mu pdv(X^nu, x^mu) partial_nu \
             & = [X,Y]
$
so the Lie derivative acting on vector fields is the commutator! By the Jacobi identity it follows
$
  cal(L)_X cal(L)_Y Z - cal(L)_Y cal(L)_X Z = cal(L)_([X,Y]) Z
$

#pagebreak()
= Tensors
For any vector space $V$, the dual vector space $V^*$ is the space of all linear maps from $V$ to $RR$. A typical example is the Hilbert space $cal(H) = V$ with $ket(psi) in cal(H)$. The dual to this is the Hilbert space with bras $bra(phi) in cal(H)^*$, where the map $bra(phi): cal(H) -> RR$ is defined by the braket $braket(phi, psi)$.

In general suppose we have a basis ${e_mu\, mu=1\, dots\, n}$ of $V$. Then we introduce a dual basis ${f^mu\, mu = 1\, dots\, n}$ for $V^*$ defined by
$
  f^nu (e_mu) = delta_mu^nu
$
then any vector in $V$ can be written as $X = X^mu e_mu$ and $f^nu (X) = X^mu f^nu (e_mu) = X^nu$. Given any basis this construction provides an isomorphism between $V$ and $V^*$ by $e_mu -> f^mu$ (dependent on the basis). We can repeat this construction to find $(V^*)^*$ but this space is naturally isomorphic to $V$ meaning the isomorphism is independent of how we choose our basis. To see this consider $X in V$ and $omega in V^*$ then $omega(X) in RR$. But we can also consider $X in (V^*)^*$ and define $X(omega) equiv omega(X) in RR$. In this sense $(V^*)^* = V$.

== One-forms
To every point $p in M$ we have a vector space $T_p (M)$. The dual to the space $T_p^* (M)$ is the cotangent space at $p$ and we call its elements for cotangent vectors or covectors. Given a basis ${e_mu}$ of $T_p (M)$ we introduce the dual basis ${f^mu}$ for $T_p^* (M)$ and write any covector as $omega = omega_mu f^mu$.

We can contruct fields of covectors by picking a member of $T_p^* (M)$ for each point $p$ smoothly---similarly as to how we did for vectors by assigning members of $T_p (M)$ to each point. These cotangent fields are called one-forms. At each $p in M$ a one-form $omega$ assigns to each $X_p in T_p (M)$ a real number $omega_p (X_p)$ smoothly. The set of all such one-forms on $M$ are denoted by $Lambda^1 (M)$.

There is a simple way to construct such one-forms: consider a function $f in C^oo (M)$ and define $dd(f) in Lambda^1 (M)$
$
  dd(f) (X) = X (f)
$
so it is a map taking $X_p in T_p (M)$ and returning the derivative of $f$ in the $X_p$ direction, a number $in RR$. We can use this to build a basis for $Lambda^1 (M)$. We introduce coordinates $x^mu$ on $M$ with the basis $e_mu = partial\/dd(x^mu, d: partial) equiv partial_mu$ of vector fields. Then we take functions $f = x^mu$ giving
$
  dd(x^mu) (partial_nu) = partial_nu (x^mu) = delta_nu^mu
$
so $f^mu = dd(x^mu)$ is a basis for $Lambda^1 (M)$ by definition, dual to the coordinate basis $partial_mu$. So any arbitrary one-form $omega in Lambda^1 (M)$ can be written as
$
  omega = omega_mu dd(x^mu)
$
in this basis the one-form $dd(f)$ takes the form
$
  dd(f) = pdv(f, x^mu) dd(x^mu)
$
since
$
  dd(f) (X) = pdv(f, x^mu) dd(x^mu) (X^nu partial_nu) =^"linearity" pdv(f, x^mu) X^nu underbrace(dd(x^mu) (partial_nu), delta_nu^mu) = X^mu pdv(f, x^mu) = X (f)
$
this is nice!

What happens now when we switch coordinates. Given two charts $phi.alt = (x^1\, dots\, x^n)$ and $tilde(phi.alt) = (tilde(x)^1\, dots\, tilde(x)^n)$ we know the basis for the vector fields changes as
$
  pdv(, tilde(x)^mu) = pdv(x^nu, tilde(x)^mu) pdv(, x^nu)
$
the basis of one-forms should transform inversely of this
$
  dd(tilde(x)^mu) = pdv(tilde(x)^mu, x^nu) dd(x^nu)
$
then
$
  dd(tilde(x)^mu) (pdv(, tilde(x)^nu)) &= pdv(tilde(x)^mu, x^rho) dd(x^rho) (pdv(x^sigma, tilde(x)^nu) pdv(, x^sigma)) \
  &= pdv(tilde(x)^mu, x^rho) pdv(x^sigma, tilde(x)^nu) dd(x^rho) (pdv(, x^sigma)) \
  &= pdv(tilde(x)^mu, x^rho) pdv(x^sigma, tilde(x)^nu) delta_sigma^rho \
  &= delta_nu^mu
$
as we would expect. Then we can write
$
  omega = omega_mu dd(x^mu) = tilde(omega)_mu dd(tilde(x)^mu) "with" tilde(omega)_mu = pdv(x^nu, tilde(x)^mu) omega_nu
$
components transforming in this way are covariant---previously we saw that components of tangent vectors transform contravariantly:
$
  tilde(X)^nu = pdv(tilde(x)^nu, x^mu) X^mu
$
it should be clear that these transform oppositely---and note that these are essentially the simplest things we are allowed to write.

=== Lie derivative
Under a map $phi : M -> N$ we saw that a vector field $X$ on $M$ can be push-forwarded to a vector field $phi_* X$ on $N$. One-forms go the other way: given a one-form $omega$ on $N$ we can pull-back this to a one-form $phi^* omega$ on $M$, defined by
$
  (phi^* omega) (X) = omega (phi_* X)
$
introducing $x^mu$ on $M$ and $y^alpha$ on $N$ then
$
  (phi^* omega)_mu = omega_alpha pdv(y^alpha, x^mu)
$
we now define the Lie derivative $cal(L)_X$ acting on one-forms. Again $X$ generates a flow $sigma_t : M -> M$, and using the pull-back allows us to compare one-forms at different points. We denote the covector $omega(p)$ as $omega_p$. Then the Lie derivative is defined as
$
  cal(L)_X omega = lim_(t -> 0) ((sigma_t^* omega)_p - omega_p)/t
$
the infinitesimal map $sigma_t$ acts on coordinates as $x^mu (t) = x^mu (0) + t X^mu + cal(O) (t^2)$ (this is the coordinate change) so the pull-back of a basis vector $dd(x^mu)$ is
$
  sigma_t^* dd(x^mu) = underbrace((delta_nu^mu + t pdv(X^mu, x^nu) + dots), "Jacobian") dd(x^nu)
$
then we have
$
  cal(L)_X (dd(x^mu)) = pdv(X^mu, x^nu) dd(x^nu)
$
and for a general one-form
$
  cal(L)_X omega &= (cal(L)_X omega_mu) dd(x^mu) + omega_nu cal(L)_X (dd(x^nu)) \
  &= X^nu partial_nu omega_mu + omega_nu partial_mu X^nu) dd(x^mu)
$

== Tensor fields
A tensor of rank $(r,s)$ at a point $p in M$ is defined to be a multi-linear map
$
  T: underbrace(T_p^* (M) times dots times T_p^* (M), r "times") times underbrace(T_p (M) times dots times T_p (M), s "times") -> RR
$
it has total rank $r+s$.

Evidently a covector in $T_p^* (M)$ is a tensor of rank $(0, 1)$ while a tangent vector in $T_p (M)$ is a tensor of rank $(1,0)$.

As before we define a tensor field to be a smooth assignment of an $(r,s)$ tensor to every point $p in M$: $p |->^"smooth" T_p$.

With a basis ${e_mu}$ for vector fields and a dual basis ${f^mu}$ for one-forms, the components of a tensor are defined to be
$
  tensor(T, mu_1 dots mu_r, -nu_1 dots nu_s) = T (f^(mu_1), dots , f^(mu_r), e_(nu_1), dots, e_(nu_s))
$
on a manifold of dimension $n$ there are $n^(r+s)$ components---for a tensor field each of these is a function over $M$.

Take a rank $(2,1)$ tensor as an example. This takes two one-forms $omega$ and $eta$ together with a vector field $X$, eventually spitting out a real number. This is
$
  T(omega, eta, X) = T(omega_mu f^mu, eta_nu f^nu, X^rho e_rho) =^"multi-linear" omega_mu eta_nu X^rho T(f^mu, f^nu, e_rho) = tensor(T, mu nu, -rho) omega_mu eta_nu X^rho
$
every manifold comes with a natural $(1,1)$ tensor called $delta$. This takes a one-form $omega$ and a vector field $X$ giving a real number. In components:
$
  delta(omega, X) = omega(X) => delta(f^mu, e_nu) = f^mu (e_nu) = delta_nu^mu
$
which is just the Kronecker delta.

We can again consider how these objects transform (how their components transform). Consider two bases for the vector fields ${e_mu}$ and ${tilde(e)_mu}$ related by
$
  tilde(e)_nu = tensor(A, mu, -nu) e_mu
$
for some invertible matrix $A$. The dual bases ${f^mu}$ and $tilde(f)^mu}$ are then related by
$
  tilde(f)^rho = tensor(B, rho, -sigma) f^sigma
$
such that
$
  tilde(f)^rho (tilde(e)_nu) = tensor(A, mu, -nu) tensor(B, rho, -sigma) f^sigma (e_mu) = tensor(A, mu, -nu) tensor(B, rho, -mu) =^! delta_nu^rho => tensor(B, rho, -mu) = tensor((A^(-1)), rho, -mu)
$
so the lower components transform by multiplying with $A$, and the upper components transform by multiplying with $B = A^(-1)$. So a rank $(1,2)$ tensor would transform as
$
  tensor(tilde(T), mu, -rho nu) = tensor(B, mu, -sigma) tensor(A, tau, -rho) tensor(A, lambda, -nu) tensor(T, sigma, -tau lambda)
$
Changing between coordinate bases we have
$
  underbrace(tensor(A, mu, -nu) = pdv(x^mu, tilde(x)^nu), "covariant") "and" underbrace(tensor(B, mu, -nu) = tensor((A^(-1)), mu, -nu) = pdv(tilde(x)^mu, x^nu), "contravariant")
$
which is what we found previously.

=== Operations on tensor fields
We can do stuff on tensor fields to generate new tensors.

We can add and subtract tensor fields, or multiply them by functions. This is what it means when we say the set of tensors at a point $p in M$ forms a vector space. We can also multiply tensors to give different types of tensors. Given a tensor $S$ of rank $(p,q)$ and a tensor $T$ of rank $(r,s)$ we can form the tensor product $S times.circle T$ which is a new tensor of rank $(p+r,q+s)$ defined by:
$
  S times.circle T (omega_1, dots, omega_p, eta_1, dots, eta_r, X_1, dots, X_q, Y_1,dots, Y_s) \
  #h(10em)= S (omega_1, dots, omega_p, X_1, dots, X_q) T(eta_1,dots,eta_r,Y_1,dots,Y_s)
$
so it obviously inherits multi-linearity---in terms of components:
$
  tensor((S times.circle T), mu_1 dots mu_p nu_1 dots nu_r, -rho_1 dots rho_q sigma_1 dots sigma_s) = tensor(S, mu_1 dots mu_p, -rho_1 dots rho_q) tensor(T, nu_1 dots nu_r, -sigma_1 dots sigma_s)
$

We can also construct a tensor of lower rank $(r-1,s-1)$ by contraction. To do this we replace any $T_p^* (M)$ entry with $f^mu$ and the corresponding $T_p (M)$ entry with $e_mu$ and then sum over $mu$. So we can construct a rank $(1,0)$ tensor $S$ from a rank $(2,1)$ tensor $T$ by
$
  S(omega) = T(omega, f^mu, e_mu)
$
alternatively we can contract the other component giving a typically different rank $(1,0)$ tensor $S' (omega) = T(f^mu,omega, e_mu)$. In terms of components we equate an upper and lower index and then sum over them:
$
  S^mu = tensor(T, mu nu, -nu) "and" S'^mu = tensor(T, nu mu, -nu)
$
We can also symmetrize or anti-symmetrize tensors, take for example a rank $(0,2)$ tensor $T$
$
  T_((mu nu)) = S_(mu nu) = 1/2 (T_(mu nu) + T_(nu mu)) " and " T_([mu nu])=A_(mu nu) = 1/2 (T_(mu nu) -T_(nu mu))
$
this idea generalizes to other tensors:
$
  tensor(T, (mu nu) rho, -sigma) = 1/2 (tensor(T, mu nu rho, -sigma) + tensor(T, nu mu rho, -sigma))
$
or we can symmetrize and anti-symmetrize over more indices (provided they are all upper or lower indices):
$
  tensor(T, mu, -(nu rho sigma)) &= 1/3! (tensor(T, mu, -nu rho sigma) + tensor(T, mu, -rho nu sigma) + tensor(T, mu, -rho sigma nu) + tensor(T, mu, -sigma rho nu) + tensor(T, mu, -sigma nu rho) + tensor(T, mu, -nu sigma rho)) \
  tensor(T, mu, -[nu rho sigma]) &= 1/3! (tensor(T, mu, -nu rho sigma) - tensor(T, mu, -rho nu sigma) + tensor(T, mu, -rho sigma nu) - tensor(T, mu, -sigma rho nu) + tensor(T, mu, -sigma nu rho) - tensor(T, mu, -nu sigma rho))
$
Given any smooth tensor field $T$ we can also always take the Lie derivative with respect to a vector field $X$. We saw above how under a map $phi:M -> N$ vector fields are pushed forwards while one-forms are pulled back. In general for a mixed tensor this leaves confusion about which way to go. But if $phi$ is a diffeomorphism we also have $phi^(-1) : N -> M$ allowing us to define the push-forward of a tensor $T$ from $M -> N$. This acts on one-forms $omega in Lambda^1 (N)$ and vector fields $X in cal(X) (N)$ and is given by
$
  (phi_* T) (omega_1, dots, omega_r, X_1, dots, X_s) = T(phi^* omega_1, dots, phi^* omega_r, (phi_*^(-1) X_1), dots, (phi_*^(-1) X_s))
$
the $phi^* omega$ are pull-backs of $omega$ from $N$ to $M$, and $phi_*^(-1) X$ are push-forwards of $X$ from $N$ to $M$. The Lie derivative is then defined:
$
  cal(L)_X T = lim_(t->0) (((sigma_(-t))_* T)_p-T_p)/t
$
with $sigma_t$ being the flow generated by $X$---note that this coincides with the previous definitions.

#pagebreak()
= Differential forms

