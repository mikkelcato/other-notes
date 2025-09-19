#import "@preview/physica:0.9.5": *
#import "temp.typ": *


#show: thmrules.with(qed-symbol: $square$)
#show: note.with(
  title: [
    *complex analysis*
  ],
  authors: (
    (
      name: "mikkelius_",
    ),
  ),
  abstract: [
    notes on _Complex Analysis_ by Ahlfors -- skipping some parts.
  ],
)


//****

= Complex functions
\* chpt. 2
== Analytic functions
_$z$ and $w$ will always denote complex variables, $x$ and $y$ can be either complex or real, but $t$ will be restricted to real values._

=== Limits and continuity
The usual limit and continuity definitions from real analysis are obvious. However there are some fundamental differences -- let $f(z)$ be a real function of a complex variable whose derivative exists at $z=a$, then $f'(a)$ is real as it is the limit of $ (f(a+h)-f(a))/h $ as $h arrow 0$ through real values, but it is also the limit of $ (f(a+i h) - f(a))/(i h) $ and thus imaginary. So $f'(a) =^! 0$ if the derivative exists. Similar logic applies to complex functions of a real variable $ z(t)=x(t)+i y(t) => z'(t)=x'(t)+i y'(t) $ so $z'(t)$ exists if both $x'(t)$ and $y'(t)$ exists.

=== Analyticity
Analytic (_Holomorphic_) functions are essentially complex functions of a complex variable with a derivative everywhere the function is defined -- these are very nice, and thus have nice properties i.e. products/quotients preserve analyticity.
From the definition we have
$
  f'(z) = lim_(h arrow 0) (f(z+h)-f(z))/h
$
note that this implies $f(z)$ is continuous, and if we let $f(z)=u(z)+i v(z)$ then it follows that both $u(z)$ and $v(z)$ are continuous. The limit must be the same regardless of how we let $h arrow 0$. Choosing real values for $h$ then the imaginary part of $z = x+ i y$ is constant, and the derivative becomes a partial derivative
$
  f'(z) = pdv(f, x) = pdv(u, x)+i pdv(v, x)
$
similarly for imaginary $h = i k$
$
  f'(z) = 1/i pdv(f, y) = - i pdv(u, y)+pdv(v, y)
$
thus $f(z)$ must satisfy
$
  pdv(f, x)=-i pdv(f, y)
$
this resolves to the Cauchy-Riemann equations:
#thm[Cauchy-Riemann equations][
  The Cauchy-Riemann equations are:
  $
    pdv(u, x)=pdv(v, y)",   " pdv(u, y)= - pdv(v, x)
  $
  These must be satisfied by the real and imaginary part of any analytic function $ f(z)=u(z)+i v(z) $
]
note that the partials exists if $f'(z)$ exists -- the relation goes both ways essentially, if $f'(z)$ exists, or $f(z)$ is analytic, then the CR-eq. are satisfied, and vice versa. To see why the derivatives exists consider
$
  abs(f'(z))^2 = (pdv(u, x))^2+(pdv(u, y))^2=(pdv(u, x))^2+(pdv(v, x))^2=pdv(u, x)pdv(v, y)-pdv(u, y)pdv(v, x)
$
where the last expression is just the Jacobian. Also note that we have
$
  nabla^2 u = pdv(u, x, 2)+pdv(u, y, 2)=0
$
and similarly for $v$, i.e. they satisfy the Laplace equation and are thus harmonic. (with $v$ being the conjugate harmonic function of $u$)

=== Polynomials and Rationals
All constant functions are analytic with derivative $0$, the simplest non-constant analytic function is $z$ whose derivative is $1$. It follows that every polynomial $ P(z) = a_0 + a_1 z + dots + a_n z^n $ is also analytic, with derivative
$
  P'(z) = a_1 + 2a_2 z + dots + n a_n z^(n-1)
$
we know that we can factorize any polynomial
$
  P(z) = a_n (z-alpha_1)(z-alpha_2) dots (z-alpha_n)
$
with $alpha_i$ being the roots of $P(z)$, these need not be distinct. If $h$ of the $alpha_j$ coincide we say this value of $alpha$ is a zero of $P(z)$ of order $h$. Thus the sum of all $h$ equal the order of the polynomial -- a degree $n$ polynomial has $n$ zeros. We can also consider derivatives. Letting $z = alpha$ be a zero of order $h$ then we can write $P(z)=(z-alpha)^h P_h (z)$ with $P_h(alpha) eq.not 0$. Differentiating yields $P(alpha)=P'(alpha)=dots=P^((h-1))(alpha)=0$, while $P^((h)) (alpha) eq.not 0$. So the order of a zero is the order of the first nonvanishing derivative. If $P(alpha)=0$ and $P'(alpha) eq.not 0$ then we call the zero simple. Now consider $ R(z) = P(z)/Q(z) $ we'll assume that $P(z)$ and $Q(z)$ have no common factors, and thus no common zeros. We'll give $R(z)$ the value $oo$ at the zeros of $Q(z)$, thus it is a function with values in the extended plane, and thus continuous. These zeros are usually called poles of $R(z)$, and the order of the pole is the order of the corresponding zero of $Q(z)$. Note that $R'(z)$ has the same poles, but with the order of each being increased by one. [_see pg. 30 in Ahlfors for more_]
Noteworthy is the fact that any $R(z)$ of order $p$ has $p$ zeros and $p$ poles, and every $R(z)=a$ has $p$ roots.

#pagebreak()
== Power series
Sequences and series (partial sums) are defined as usual -- note the Cauchy-criterion. Likewise pointwise and uniform convergence are defined as usual.

_Recall uniform convergence: The sequence ${f_n (x)}$ converges uniformly to $f(x)$ on the set $E$ if for every $epsilon > 0$ there exists an $n_0$ such that $abs(f_n (x)-f(x)) < epsilon$ for all $n >= n_0$ and for all $x in E$._

Uniform convergence is nice because continuity etc. is "preserved".

_Recall the Cauchy-criterion: ${f_n (x)}$ converges uniformly on $E$, if and only if for every $epsilon > 0$ there exists an $n_0$ such that $abs(f_m (x)- f_n (x)) < epsilon$ for all $m,n >= n_0$ and all $x in E$._

Now we can begin with power series of the form:
$
  a_0 + a_1 z + a_2 z^2 + dots + a_n z^n + dots
$
or more generally:
$
  sum_(n=0)^oo a_n (z-z_0)^n
$
the simplest example is the geometric series:
$
  1 + z +z^2+dots +z^n + dots
$
whose partial sums can be written in the form:
$
  1 + z + dots + z^(n-1) = (1-z^n)/(1-z)
$
since $z^n arrow 0$ for $abs(z)<1$ and $abs(z^n)>=1$ for $abs(z) >= 1$ it is clear that the series converges to $1\/(1-z)$ for $abs(z)<1$ and diverges for $abs(z)>=1$ -- this is very typical, i.e. convergence inside a circle and divergence outside it. To make this more concrete we have the following theorem:
#thm[Abel's theorem][
  For every power series there is a number $0 <= R <= oo$ called the radius of convergence, with the following properties:
  1. The series converges absoulutely for all $z$ with $abs(z)<R$. If $0 <= rho < R$ the convergence is uniform for $abs(z) <= rho$.
  2. If $abs(z) > R$ the terms of the series are unbounded, and the series is thus divergent.
  3. In $abs(z) < R$ the sum of the series is an analytic function. The derivative can be found by termwise differentiation and has the same radius of convergence.
]
We'll show the properties are true if $R$ is chosen as (_Hadamard's formula_):
$ 1/R = lim_(n arrow oo) sup root(n, abs(a_n)) $

#proof[
  If $abs(z) < R$ we can find $rho$ such that $abs(z) < rho < R$. Then $1\/rho > 1\/R$ and by definition of the $lim sup$ there exists an $n_0$ such that for all $n >= n_0$ we have $root(n, abs(a_n)) < 1\/rho => abs(a_n) < 1\/ rho^n$. It follows that $abs(a_n z^n) < (abs(z)\/rho)^n$ for large $n$, and thus the power series converges, since $abs(z)< rho$.

  To prove uniform convergence for $abs(z)<= rho < R$ we pick $rho'$ such that $rho < rho' < R$ and find $abs(a_n z^n) <= (rho \/rho')^n$ for $n >= n_0$. Again the majorant is convergent and since it has constant terms we use Weierstrass' M-test to conclude uniform convergence.

  If $abs(z) > R$ we pick $rho$ such that $R < rho < abs(z)$, since $1\/rho < 1\/R$ there are large $n$ such that $root(n, abs(a_n)) > 1\/rho => abs(a_n) > 1\/rho^n$. Thus $abs(a_n z^n) > (abs(z)\/rho)^n$ for infinitely many $n$, and the terms are unbounded.

  The derived series $sum_1^oo n a_n z^(n-1)$ has the same $R$ because $root(n, n) arrow 1$. To prove this we let $root(n, n) = 1 + delta_n$. Then $delta_n > 0$ and by the binomial theorem $n = (1+ delta_n)^n > 1 + 1/2 n(n-1) delta_n^2$ or $2\/n > delta_n^2$ and thus $delta_n arrow 0$.

  For $abs(z) < R$ we write:
  $ f(z) = sum_0^oo a_n z^n = s_n (z) + R_n (z) = sum_0^(n-1) a_k z^k + sum_(k=n)^oo a_k z^k $ and $ f_1 (z) = sum_1^oo n a_n z^(n-1) = lim_(n arrow oo) s'_n (z) $ we want to show that $f'(z)=f_1 (z)$. Consider:
  $
    (f(z)-f(z_0))/(z-z_0) - f_1 (z_0) = ((s_n (z)-s_n (z_0))/(z-z_0) - s'_n (z_0)) &+ (s'_n (z_0) - f_1 (z_0)) \
    &+ ((R_n (z) - R_n (z_0))/(z-z_0))
  $
  with $z eq.not z_0$ and $abs(z), abs(z_0) < rho < R$. The last term can be written as:
  $
    sum_(k=n)^oo a_k (z^(k-1) + z^(k-2)z_0 + dots + z z_0^(k-2) + z_0^(k-1))
  $
  which lets us say:
  $
    abs((R_n (z)-R_n (z_0))/(z-z_0)) <= sum_(k=n)^oo k abs(a_k) rho^(k-1)
  $
  the RHS is just the remainder term in a convergent series, thus we can find $n_0$ such that for all $n>=n_0$:
  $
    abs((R_n (z)-R_n (z_0))/(z-z_0)) <=epsilon/3
  $
  By definition we also have an $n_1$ such that for all $n >= n_1$: $abs(s'_n (z_0) - f_1 (z_0)) < epsilon\/3$. Pick $n >= n_0, n_1$, also by definition of the derivative we can find $delta > 0$ such that $0 < abs(z-z_0) < delta$ implies:
  $
    abs((s_n (z)- s_n (z_0))/(z-z_0)- s'_n (z_0)) < epsilon/3
  $
  combining everything we find:
  $
    abs((f(z)-f(z_0))/(z-z_0)-f_1 (z_0)) < epsilon
  $
  when $0 < abs(z-z_0) < delta$, thus $f'(z_0)$ exists and is equal to $f_1 (z_0)$.
]
This reasoning can be repeated, leading us to conclude that a power series with positive radius of convergence has derivatives of all orders, the $k$'th derivative is given as:
$
  f^((k)) (z) = k! a_k + ((k+1)!)/1! a_(k+1) z + ((k+2)!)/2! a_(k+2) z^2 + dots
$
giving $a_k = f^((k))(0) \/k!$, thus we can write our power series as:
$
  f(z) = f(0) + f'(0) z + (f''(0))/2! z^2 + dots + (f^((n))(0))/n! z^n + dots
$
which is just the Taylor-Maclaurin development.

=== The exponential and trigonometric functions
We define $e^x$ as the solution to $f'(z) = f(z)$ with initial value $f(0)=1$. This gives:
$
  e^z = 1 + z/1! + z^2/2! + dots + z^n/n! + dots
$
this series converges in the entire plane since $root(n, n!) arrow oo$.

We define the trigonometric functions by:
$
  cos z = (e^(i z) + e^(- i z))/2",   " sin z = (e^(i z)-e^(-i z))/(2i)
$
their series developments are obvious. From these definitions we also get Euler's formula:
$
  e^(i z) = cos z + i sin z
$
and:
$
  cos^2 z + sin^2 z = 1
$
likewise the usual derivatives follow, i.e. $dd(cos z) = - sin z$ and $dd(sin z) = cos z$ -- all other usual identities similarly follow from these definitions. Notably all trigonometric functions are rational functions of $e^(i z)$.

Functions are periodic with period $c$ if $f(z+c)=f(z)$, thus for the exponential $e^z e^c = e^z$ or $e^c = 1$. This implies $c = i omega$ with real $omega$. The smallest positive period is with $omega = 2 pi$. Further $e^(pi i \/2) = i$ and $e^(pi i) = -1$. Thus $w = e^(i y)$ describes the unit circle with $abs(w) = 1$ -- i.e. this is a homomorphism between the additive group of reals and the multiplicative group of complex numbers with absolute value $1$, with the kernel being all integral multiples $2pi n$.

We define the logarithm as the inverse of the exponential function, so by definition $z = log w$ is a root of $e^z = w$. Since $e^z eq.not 0$ the number $0$ has no logarithm. For $w eq.not 0$ then $e^(x+i y) = w$ implies $e^x = abs(w)$ and $e^(i y) = w \/ abs(w)$. The first equation has a unique solution $x = log abs(w)$ while the RHS of the second equation is a complex number of magnitude $1$, thus it has one solution in $0 <= y < 2 pi$, and is also satisfied by all $y$ that differ by an integer multiple of $2 pi$. So every complex number $eq.not 0$ has infinitely many logarithms which differ by multiples of $2 pi i$. The imaginary part of $log w$ is the argument of $w$ and is geometrically interpreted as the angle. With this definition $ log w = log abs(w) + i arg w $
or with $abs(z) = r$ and $arg z = theta$ then $z = r e^(i theta)$.

Lastly we'll find the inverse cosine. This is obtained by solving:
$
  cos z = (e^(i z) + e^(- i z))/2 = w
$
this can be written as a quadratic in $e^(i z)$ which gives the roots as:
$
  e^(i z) = w plus.minus sqrt(w^2 - 1) => z = arccos w = - i log(w plus.minus sqrt(w^2 -1))= plus.minus i log(w + sqrt(w^2-1))
$
the inverse sine is then easily defined by $ arcsin w = pi/2 - arccos w $
notably everything can be expressed in terms of $e^z$ and its inverse. Thus there is essentially only one elementary transcendental function.

#pagebreak()
= Complex integration
== Line integrals
\* chpt. 4

If $f(t) = u(t) + i v(t)$ is continuous and defined on $(a,b)$ then:
$
  integral_a^b f(t) dd(t) = integral_a^b u(t) dd(t) + i integral_a^b v(t) dd(t)
$
to generalize we use a line integral, consider a piecewise differentiable arc $gamma$ with $z = z(t)$ for $a <= t <= b$. Then given $f(z)$ is defined and continuous on $gamma$ then we can set:
$
  integral_gamma f(z) dd(z) = integral_a^b f(z(t)) z'(t) dd(t)
$
this is the complex line integral of $f(z)$ over $gamma$. Note that this integral is invariant under change of parameter, i.e. if $t = t(tau)$ is a change of parameter. Then:
$
  integral_a^b f(z(t))z'(t) dd(t) = integral_alpha^beta f(z(t(tau)))z'(t(tau))t'(tau) dd(tau)
$
but $z'(t) = z'(t(tau))t'(tau)$ so our integral is independent of how we parameterize $gamma$ which should hold. We define the opposite arc $-gamma$ by $z = z(-t)$ for $-b <= t <= - a$, thus:
$
  integral_(- gamma) f(z) dd(z) = integral_(-b)^(-a) f(z(-t))(-z'(-t))dd(t) = - integral_gamma f(z) dd(z)
$
if we subdivide our $gamma = gamma_1 + gamma_2 + dots + gamma_n$ then obviously:
$
  integral_gamma f dd(z) = integral_(gamma_1) f dd(z) + dots + integral_(gamma_n) f dd(z)
$
we can define:
$
  integral_gamma f overline(dd(z)) = overline(integral_gamma overline(f) dd(z))
$
and using this:
$
  integral_gamma f dd(x) = 1/2 { integral_gamma f dd(z) + integral_gamma f overline(dd(z)) }
$
similarly for the integral with respect to $y$. We could've also defined the integral as:
$
  integral_gamma (u dd(x) - v dd(y)) + i integral_gamma (u dd(y) + v dd(x))
$
which seperates the real and imaginary parts. An entirely different line integral can be obtained by integrating with respect to the arc length:
$
  integral_gamma f dd(s) = integral_gamma f abs(dd(z)) = integral_gamma f(z(t)) abs(z'(t)) dd(t)
$
this is also independent of choice of parameter, but now:
$
  integral_(- gamma) f abs(dd(z)) = integral_gamma f abs(dd(z))
$
note that for $f=1$ this integral just gives the length of $gamma$. The length can also be defined as the following limit:
$
  integral_gamma f dd(s) = lim sum_(k=1)^n f(z(t_k)) abs(z(t_k)-z(t_(k-1)))
$
if this is finite (with $f=1$) the arc is rectifiable, i.e. if we can find the length by splitting it up into small pieces, and finding the length of each piece.

A general line integral can be written in the form:
$
  integral_gamma p dd(x) + q dd(y)
$
often we treat this integral as dependent on $gamma$, thus as a functional. One type of such integrals are characterized by only depending on the end points of the arc. If two arcs have the same initial point and end point then we require:
$
  integral_(gamma_1) = integral_(gamma_2)
$
if $gamma$ is closed then $-gamma$ shares its end points thus we obtain:
$
  integral_gamma = integral_(- gamma) = - integral_gamma = 0
$
likewise if $gamma_1$ and $gamma_2$ share end points then $gamma_1 - gamma_2$ is a closed curve, and it follows that $ integral_(gamma_1) = integral_(gamma_2) $
but when does a line integral only depend on the end points?

#thm[
  The line integral $integral_gamma p dd(x)+q dd(y)$ in $Omega$ depends only on the end points of $gamma$ if and only if there is a function $U(x,y)$ in $Omega$ with partial derivatives $partial_x U = p$ and $partial_y U = q$.
]
#proof[
  Consider:
  $
    integral_gamma p dd(x) + q dd(y) = integral_a^b (pdv(U, x)x'(t) + pdv(U, y) y'(t))dd(t)=integral_a^b dv(U(x(t),y(t)), t) dd(t) = U(a)-U(b)
  $
  thus the integral only depends on the end points. To prove the other direction choose a point $(x_0, y_0) in Omega$ and join it to $(x,y)$ by a polygon $gamma$, contained in $Omega$, whose sides are parallel to the coordinate axes. And define a function $ U(x,y) = integral_gamma p dd(x) + q dd(y) $ This obviously only depends on the end points, so it is well-defined. If we now pick the last segment of $gamma$ horizontal, then we can keep $y$ constant and let $x$ vary without changing the other segments. So on the last segment we can write:
  $
    U (x,y) = integral^x p(x,y) dd(x) + "const"
  $
  where it immediately follows that $partial_x U = p$. If we let the last segment be vertical we'd get $partial_y U = q$. In other words we have:
  $
    dd(U) = pdv(U, x) dd(x) + pdv(U, y) dd(y)
  $
  or the integrand is an exact differential.
]
So when is $f(z) dd(z) = f(z) dd(x) + i f(z) dd(y)$ an exact differential? By definition for this to be the case we must have some $F(z)$ in $Omega$ with:
$
  pdv(F(z), x) & = f(z) \
  pdv(F(z), y) & = i f(z) \
               & => pdv(F, x) = - i pdv(F, y)
$
which is the CR-eq! Thus the integral $integral_gamma f dd(z)$, with continuous $f$ depends only on the end points of $gamma$ if and only if $f$ is the derivative of an analytic function in $Omega$. ($f$ itself is then also analytic.)

This is very powerful and lets us calculate some integrals without thinking.

#ex[
  $ integral_gamma (z-a)^n dd(z) = 0 $ for all closed $gamma$ if $n >= 0$. For negative $n eq.not 1$ the same holds for all closed curves which do not pass through $a$. For $n = -1$ this isn't true, consider a circle with center $a$: $z=a+rho e^(i t)$ for $0 <= t <= 2 pi$, doing the integral we obtain:
  $
    integral_C dd(z)/(z-a) = integral_0^(2 pi) i dd(t) = 2 pi i
  $
]
#ex[
  $ integral_(abs(z)=2) dd(z)/(z^2-1) $ we parameterize $z=2 e^(i t) => z'(t) = 2i e^(i t)$ giving:
  $
    integral_0^(2 pi) (2i e^(i t) dd(t))/(4e^(2 i t)-1)
  $
  consider:
  $
    f(t) = (2 i e^(i t))/(4 e^(2 i t)-1) => f(t+pi) = (2 i e^(i (t + pi)))/(4 e^(2 i(t+pi))-1) = (-2i e^(i t))/(4e^(2 i t)-1) = - f(t)
  $
  thus we can write:
  $
    integral_0^(2pi) f(t) dd(t) = integral_0^pi f(t) dd(t)+integral_pi^(2 pi) f(t) dd(t)
  $
  letting $t arrow t+pi$ in the first:
  $
    integral_pi^(2 pi) f(t+pi) dd(t) +integral_pi^(2 pi) f(t) dd(t) = 0
  $
  by the previous. Even though we have poles at $plus.minus 1$ the integral is zero due to symmetry.
]

#ex[
  $ integral_(abs(z)=1) abs(z-1) abs(dd(z)) $ we let $z = e^(i t) => dd(z) = i e^(i t) dd(t)$:
  $
    integral_0^(2 pi) abs(e^(i t) -1) dd(t)
  $
  now:
  $
    abs(e^(i t)-1)^2 = abs(cos t - 1 + i sin t)^2 = cos^2 t - 2 cos t +1 + sin^2 t = 2(1-cos t)
  $
  so:
  $
    sqrt(2) integral_0^(2 pi) sqrt(1-cos t) dd(t) &= 2 integral_0^(2 pi) abs(sin (t/2)) dd(t) \
    &= 4 integral_0^pi sin theta dd(theta) \
    &= 8
  $
]

#pagebreak()
== Cauchy's Theorem
We'll start by looking at a rectangle $R$ defined by $a <= x <= b$ and $c <= y <= d$. Its perimeter is a simple closed curve consisting of four line segments whose direction we choose such that $R$ lies to the left of the directed segments. This curve is referred to as the boundary curve or contour of $R$, and we denote it by $dd(R, d: partial)$ -- note that $R$ is a closed point set, and thus not a region, in the theorem we consider a function which is analytic on $R$, i.e. it is defined and analytic in an open set containing $R$.

#thm["Cauchy's Theorem"][
  If the function $f(z)$ is analytic on $R$, then:
  $
    integral_(dd(R, d: partial)) f(z) dd(z) = 0
  $
]

#proof[due to Goursat][
  We denote:
  $
    eta (R) = integral_(dd(R, d: partial)) f(z) dd(z)
  $
  and we proceed by bijection, dividing our rectangle into four congruent rectangles $R^((1)), R^((2)), R^((3))", and" R^((4))$, giving:
  $
    eta(R) = eta(R^((1))) + eta(R^((2)))+ eta(R^((3))) + eta(R^((4)))
  $
  since the integrals over the common sides obviously cancel. It follows that at least one rectangle must satisfy: $ abs(eta(R^((k)))) >= 1/4 abs(eta(R)) $ we let this rectangle be $R_1$, this can be repeated ad infinitum giving a sequence of nested rectangles $R supset R_1 supset R_2 supset dots supset R_n supset dots$ with:
  $
    abs(eta(R_n)) >= 4^(-n)abs(eta(R))
  $
  these converge to some $z^* in R$, or $R_n$ will be contained in some neighborhood $abs(z-z^*) < delta$ for large enough $n$. We pick $delta$ small enough such that $f(z)$ is defined and analytic in $abs(z-z^*) < delta$. Then given $epsilon > 0$ we can also pick $delta$ such that:
  $
    abs((f(z)-f(z^*))/(z-z^*)-f'(z^*)) < epsilon
  $
  or
  $
    abs(f(z)-f(z^*)-(z-z^*)f'(z^*)) < epsilon abs(z-z^*)
  $
  for $abs(z-z^*) < delta$. We assume $delta$ satisfies everything mentioned and that $R_n$ is contained in $abs(z-z^*) < delta$. We make the observation:
  $
    integral_(dd(R_n, d: partial)) dd(z) = integral_(dd(R_n, d: partial)) z dd(z) = 0
  $
  these are just special cases of our theorem that we have already proved since these are derivatives of $z$ and $z^2\/2$ respectively. These let us write:
  $
    eta (R_n) &= integral_(dd(R_n, d: partial)) f(z) dd(z) \
    &= integral_(dd(R_n, d: partial)) f(z)-f(z^*)-(z-z^*)f'(z^*) dd(z) \
    abs(eta(R_n))&<=epsilon integral_(dd(R_n, d: partial)) abs(z-z^*) abs(dd(z))
  $
  now $abs(z-z^*)$ is at most the length of the diagonal $d_n$ of $R_n$. If $L_n$ is the perimeter of $R_n$, then the integral is $<= d_n L_n$. If these are corresponding to the quantities of $R$ then $d_n = 2^(-n) d$ and $L_n = 2^(-n) L$, thus we get:
  $
    abs(eta(R_n)) <= 4^(-n) d L epsilon => abs(eta (R)) <= d L epsilon
  $
  $epsilon$ is arbritrary so $eta(R) =^! 0$. And we are done.
]

We can do better by weakening our hypothesis:
#thm[
  Let $f(z)$ be analytic on the set $R'$ obtained from $R$ by removing a finite number of interier points $zeta_j$. If for all $j$:
  $
    lim_(z arrow zeta_j) (z-zeta_j) f(z) = 0
  $
  then:
  $
    integral_(dd(R, d: partial)) f(z) dd(z) = 0
  $
]

#proof[
  To prove this we consider just one exceptional point $zeta$, since $R$ can be subdivided till each smaller rectangle contains at most one such point. Now we divide our $R$ into nine smaller rectangles with $zeta$ being in the middle rectangle, we call this rectangle $R_0$. Now we apply the previous theorem to every rectangle but $R_0$ to get:
  $
    integral_(dd(R, d: partial)) f dd(z) = integral_(dd(R_0, d: partial)) f dd(z)
  $
  given $epsilon > 0$ we can choose $R_0$ small enough such that:
  $
    lim_(z arrow zeta) (z- zeta)f(z) = 0 => abs(f(z)) <= epsilon/abs(z-zeta)
  $
  on $dd(R_0, d: partial)$. Then we have:
  $
    abs(integral_(dd(R, d: partial)) f dd(z)) <= epsilon integral_(dd(R_0, d: partial)) abs(dd(z))/abs(z - zeta)
  $
  if we assume that $R_0$ is a square with center $zeta$ then:
  $
    integral_(dd(R_0, d: partial)) abs(dd(z))/abs(z-zeta) < 8 => abs(integral_(dd(R, d: partial)) f dd(z)) < 8 epsilon
  $
  with arbitrary $epsilon$ the result follows. The hypothesis is fulfilled if $f(z)$ is analytic and bounded on $R'$.
]

We've seen that the integral of an analytic function over a closed curve doesn't always vanish, e.g:
$
  integral_C dd(z)/(z-a) = 2 pi i
$
to make sure it vanishes we need to make assumptions with respect to the region $Omega$ on which $f(z)$ is analytic. In the following we assume that $Omega$ is an open disk $abs(z-z_0) < rho$, which we denote by $Delta$.

#thm[
  If $f(z)$ is analytic in an open disk $Delta$, then:
  $
    integral_gamma f(z) dd(z) = 0
  $
  for every closed curve $gamma$ in $Delta$.
]

#proof[
  We define $F(z) = integral_sigma f dd(z)$ with $sigma$ being the horizontal line segment from $(x_0, y_0) arrow (x, y_0)$ and the vertical segment from $(x, y_0) arrow (x,y)$, it is then obvious that $partial_y F = i f(z)$, if we flip the zig-zag then we get $partial_x F = f(z)$. Then $F(z)$ is analytic in $Delta$ with derivative $f(z)$ and $f(z) dd(z)$ is an exact differential. We essentially construct rectangles within $Delta$ and then apply the previous theorems. This holds for regions which are somewhat symmetric, namely rectangles, circles, ellipsis, half planes, etc. We need the region to contain the rectangle made from opposite vertices $z$ and $z_0$.
]

For the reason stated the weaked hypothesis is also all thats needed in this case:

#thm[
  Let $f(z)$ be analytic in $Delta'$ obtained by removing a finite number of $zeta_j$ from an open disk $Delta$. If $f(z)$ satisfies $lim_(z arrow zeta_j) (z-zeta_j) f(z) = 0$ for all $j$, then $ integral_gamma f(z) dd(z) = 0 $ for any closed curve $gamma$ in $Delta'$.
]

#proof[(sketch)][
  Essentially the same proof, but we can't let $sigma$ pass through the points $zeta_j$. It is always possible to avoid these by using more lines.
]

#pagebreak()
== Cauchy's Integral Formula
As a preliminary we need to define the index of a point with respect to a closed curve. This is based on the following lemma:

#lemma[
  If the piecewise differentiable closed curve $gamma$ does not pass through the point $a$ then the value of the integral:
  $
    integral_gamma dd(z)/(z-a)
  $
  is a multiple of $2 pi i$.
]

#proof[
  One simple way to prove this is to just compute it. Let $gamma$ be parametrized by $z = z(t)$ for $alpha <= t <= beta$ and consider:
  $
    h(t) = integral_alpha^t (z'(t))/(z(t)-a) dd(t) => h'(t) = (z'(t))/(z(t)-a)
  $
  this is continuous and defined on $[alpha, beta]$ when $z'(t)$ is continuous. Now consider:
  $
    dv(, t) e^(- h(t)) (z(t)-a) = z'(t) e^(-h(t)) - (z(t)-a)e^(- h(t)) h'(t) = 0
  $
  except for points where $z(t)=a$. Thus this function must be constant, so we have, from $e^(-h(t)) (z(t)-a) = "const"$:
  $
    e^(h(t)) = (z(t)-a)/(z(alpha)-a)
  $
  given that $z(beta) = z(alpha)$ we get $e^(h(beta)) = 1$ so $h(beta)$ must be a multiple of $2 pi i$.
]
Now we can define the index (or winding number) as:
$
  n(gamma, a) = 1/(2 pi i) integral_gamma dd(z)/(z-a)
$
evidently $n(-gamma, a) = - n(gamma, a)$. Obviously if $gamma$ lies in a circle then $n(gamma, a) = 0$ for all points $a$ outside the same circle -- this is a consequence of Cauchy's theorem. Note that $gamma$ is closed and bounded, meaning its complement is open and can be represented as a union of disjoint regions. In a nutshell $gamma$ determines these regions. Considering the extended plane exactly one of these would hold the point at infinity. So $gamma$ determines one and only one unbounded region. The index $n(gamma, a)$ as a function of $a$ is constant in each region determined by $gamma$ and zero in the unbounded region. So for any two points $a$ and $b$ in the same region determined by $gamma$ have the same index, i.e. $n(gamma, a)=n(gamma, b)$. The case $n(gamma, a)=1$ is important, for simplicity we have the following lemma with $a=0$:

#lemma[
  Let $z_1, z_2$ be two points on a closed curve $gamma$, which does not pass through the origin. Denote the subarc from $z_1 arrow z_2$ by $gamma_1$ and the subarc from $z_2 arrow z_1$ by $gamma_2$. Assume that $z_1$ lies in the lower half plane, and $z_2$ in the upper half plane. If $gamma_1$ does not meet the negative real axis and $gamma_2$ does not meet the positive real axis, then $n(gamma, 0) = 1$.
]

#proof[
  The idea is to draw half-lines $L_1$ and $L_2$ from respectively $z_1$ and $z_2$ to the origin. Let $zeta_1$ and $zeta_2$ be points where $L_1$ and $L_2$ intersect a circle $C$ around the origin. The arc $C_1$ from $zeta_1 arrow zeta_2$ does not intersect the negative axis, and likewise $C_2$ does not intersect the positive axis. Denote the segments $z_1 arrow zeta_1$ by $delta_1$ and similarly for $delta_2$. Now we introduce the curves $sigma_1 = gamma_1 + delta_2 - C_1 - delta_1$ and $sigma_2 = gamma_2 + delta_1 - C_2 - delta_2$, both being closed. From these we can find:
  $
    gamma = gamma_1 + gamma_2 = sigma_1 + sigma_2 + C => n(gamma, 0) = n(sigma_1, 0) + n(sigma_2, 0) + n(C,0)
  $
  $sigma_1$ does not meet the negative axis, so the origin belongs to the unbounded region determined by $sigma_1$, and thus $n(sigma_1 , 0) = 0$, similarly $n(sigma_2, 0)=0$. So $n(gamma,0)=n(C,0)=1$.
]

Now let $f(z)$ be analytic in an open disk $Delta$. Consider a closed $gamma$ in $Delta$ and a point $a in Delta$ not on $gamma$. We'll apply Cauchy's theorem to:
$
  F(z) = (f(z)-f(a))/(z-a)
$
this function is analytic for all $z eq.not a$. For $z=a$ it is not defined, however it still satisfies $lim_(z arrow a) F(z)(z-a) = lim_(z arrow a) (f(z)-f(a))=0$, so the theorem still applies. Thus:
$
  integral_gamma (f(z)-f(a))/(z-a) dd(z) = 0
$
which can be written as:
$
  integral_gamma (f(z) dd(z))/(z-a) = f(a) integral_gamma dd(z)/(z-a) = 2 pi i n(gamma, a) f(a)
$

#thm[
  Cauchy's Integral Formula][
  Let $f(z)$ be analytic on $Delta$ and let $gamma$ be a closed curve in $Delta$. For any $a$ not on $gamma$:
  $
    n(gamma, a) dot f(a) = 1/(2 pi i) integral.cont_gamma (f(z) dd(z))/(z-a)
  $
  if $a in.not Delta$ then obviously both sides are zero.
]
commonly we have $n(gamma, a) = 1$ giving the representation formula:
$
  f(a) = 1/(2 pi i) integral_gamma (f(z) dd(z))/(z-a)
$
if we treat $a$ like a variable (but keeping same index, i.e. making sure the order is constant) then we can conveniently write:
$
  f(z) = 1/(2 pi i) integral_gamma (f(zeta) dd(zeta))/(zeta - z)
$
this is Cauchy's integral formula. Which here is valid for $n(gamma, z) = 1$, when $f(z)$ is analytic in a disk. This representation is very nice and easily lets us determine some local properties of analytic functions, e.g. derivatives. Let $f(z)$ be a function which is analytic in some arbitrary region $Omega$, at a point $a in Omega$ we determine a $delta$-neighborhood $Delta$ contained in $Omega$, and in $Delta$ a circle $C$ about $a$. We can then apply the previous theorem to $f(z)$ in $Delta$. Since $n(C,a) = 1$ we have $n(C,z) = 1$ for all $z in C$. For these $z$ we obtain:
$
  f(z) = 1/(2 pi i) integral_C (f(zeta) dd(zeta))/(zeta - z)
$
if we can differentiate under the integral sign then:
$
  f'(z) = 1/(2 pi i) integral_C (f(zeta) dd(zeta))/(zeta-z)^2
$
this can be done forever:
$
  f^((n)) (z) = n!/(2 pi i) integral_C (f(zeta) dd(zeta))/(zeta-z)^(n+1)
$
If we can justify the differentiations then all derivatives exists at the points in $C$. Since all points in $Omega$ is inside some circle then the derivatives exist in all of $Omega$. To justify these we'll use the following:
#lemma[
  Suppose $phi(zeta)$ is continuous on the arc $gamma$. Then the function:
  $
    F_n (z) = integral_gamma (phi(zeta) dd(zeta))/(zeta-z)^n
  $
  is analytic in each of the regions determined by $gamma$, and its derivative is $F'_n (z) = n F_(n+1) (z)$.
]

#proof[
  First we prove $F_1 (z)$ is continuous. We let $z_0$ be a point not on $gamma$ and choose some neighborhood $abs(z-z_0) < delta$ such that it does not meet $gamma$. Restricting $z$ to a smaller neighborhood $abs(z-z_0) < delta\/2$ then we obtain that $abs(zeta - z) > delta \/2$ for all $zeta in gamma$. Consider:
  $
    F_1 (z) - F_1 (z_0) = (z- z_0) integral_gamma (phi(zeta) dd(zeta))/((zeta-z)(zeta-z_0))
  $
  giving:
  $
    abs(F_1 (z) - F_1 ( z_0)) < abs(z-z_0) 2/delta^2 integral_gamma abs(phi) abs(dd(zeta))
  $
  since $delta$ is arbitrary this proves continuity of $F_1$ at $z_0$. Now consider the difference quotient:
  $
    (F_1 (z) - F_1 (z_0))/(z-z_0) = integral_gamma (phi(zeta)dd(zeta))/((zeta-z)(zeta-z_0))
  $
  by defintion the RHS tends to $F_2 (z_0)$ as $z arrow z_0$, thus $F'_1 (z) = F_2 (z)$. The general case follows from induction. We assume $F'_(n-1) (z) = (n-1) F_n (z)$ and use:
  $
    F_n (z) - F_n (z_0) &= integral_gamma (phi dd(zeta))/((zeta-z)^(n-1)(zeta-z_0)) - integral_gamma (phi dd(zeta))/(zeta-z_0)^n \
    &+ (z-z_0) integral_gamma (phi dd(zeta))/((zeta-z)^n (zeta-z_0))
  $
  by the induction hypothesis the first term two terms cancel as $z arrow z_0$, and in the last term the factor $z-z_0$ is bounded in some neighborhood of $z_0$, thus $F_n$ is continuous. Now if we divide the identity by $z-z_0$ and let $z arrow z_0$ we get:
  $
    F'_n (z_0) =(n-1) F_(n+1) (z_0) + F_(n+1) (z_0) = n F_(n+1) (z_0)
  $
  this is just the induction hypothesis applied to $phi(zeta)\/(zeta-z_0)$. Consider the function:
  $
    G(z) = integral_gamma (phi dd(zeta))/((zeta-z)^(n-1)(zeta-z_0)) tilde F_(n-1)
  $
  the first term is the derivative of this, thus by the induction hypothesis:
  $
    dv(, z) F_(n-1) = (n-1) F_n
  $
  and in the limit $z arrow z_0$ this becomes $(n-1)F_(n+1)$.
]

Thus any analytic function has derivatives of all orders and can be represented by the previous integral formula. This has some nice consequences:

#thm[Morera's theorem][
  If $f(z)$ is defined and continuous in a region $Omega$, and if $integral_gamma f dd(z) = 0$ for all closed curves $gamma$ in $Omega$, then $f(z)$ is analytic in $Omega$.
]

#proof[
  The hypothesis implies that $f(z)$ is the derivative of an analytic function, which then by what we just found implies that $f(z)$ itself is analytic.
]

#thm[Liouville's theorem][
  A function which is analytic and bounded in the whole plane must reduce to a constant.
]
#proof[
  We make use of Cauchy's estimate, letting the radius of $C$ be $r$, and assuming that $abs(f(zeta)) <= M$ on $C$, then letting $z = a$ we have:
  $
         f^((n))(a) & = n!/(2 pi i) integral_C (f(zeta) dd(zeta))/(zeta-a)^(n+1) \
    abs(f^((n))(a)) & <= n! M/(2 pi) integral_C abs(dd(zeta))/abs(zeta-a)^(n+1) \
                    & <= n! M/(2 pi) 1/r^(n+1) integral_C abs(dd(zeta)) \
                    & <= (M n!)/(2 pi) (2 pi r)/r^(n+1) \
    abs(f^((n))(a)) & <= M n! r^(- n)
  $
  for Liouville's theorem we just need $n=1$. The hypothesis means that $abs(f(zeta)) <= M$ on all circles (since it's bounded and analytic), now we can let $r arrow oo$, and Cauchy's estimate then immediately gives $f'(a) = 0$, i.e. the function is constant.
]
As a sidenote this lets us easily prove the fundamental theorem of algebra. Let $P(z)$ be a polynomial of degree $>0$. If $P(z)$ is never zero, then $1\/P(z)$ would be analytic in the whole plane, and since $P(z) arrow oo$ for $z arrow oo$ then $1\/P(z) arrow 0$, this implies boundedness. Then by Liouville's theorem it should be a constant, which it is not, and thus $P(z)=0$ and it must have a root. Note that Cauchy's estimate shows that derivatives of analytic functions are not arbitrary, there must be an $M$ and $r$ such that it is fulfilled. To use it effectively we want to pick a nice $r$, with the purpose being to minimize $M(r) r^(-n)$, with $M(r)$ being the maximum og $abs(f)$ on $abs(zeta-a)=r$.

#pagebreak()
== Local properties of Analytic functions
=== Removable singularities and Taylor's theorem
Before we introduced these exceptional points, which gave us a weaker condition under which Cauchy's theorem would still hold, similarly Cauchy's integral formula remains valid at these points, as long as they don't coincide with $a$. Cauchy's formula gives us a representation of $f(z)$ where the dependence on $z$ is the same as at the exceptional points -- i.e. these points are only exceptional because they lack information, not due to some intrinsic property. These points are called removable singularities.

#thm[
  Let $f(z)$ be analytic in $Omega'$ obtained by omitting a point $a$ from $Omega$. A necessary and sufficient condition that there exist an analytic function in $Omega$ which coincides with $f(z)$ in $Omega'$ is that $lim_(z arrow a) (z-a) f(z) = 0$. This extended function is unique.
]

#proof[
  Necessity and uniqueness follow since the extended function must be continuous at $a$ (i.e. $lim_(z arrow a) (z-a) F(z)=0$, near $a$ $F(z)$ is bounded,). To prove sufficiency we draw a circle $C$ at $a$ such that $C$ and everything inside it is contained in $Omega$. Cauchy's formula holds:
  $
    f(z) = 1/(2 pi i) integral_C (f(zeta)dd(zeta))/(zeta-z)
  $
  for all $z eq.not a$ inside $C$. The integral represents an analytic function of $z$ inside $C$, thus the function which is equal to $f(z)$ for $z eq.not a$ and which has the value:
  $
    1/(2pi i) integral_C (f(zeta)dd(zeta))/(zeta-a)
  $
  for $z=a$ is analytic in $Omega$. Naturally we denote the extended function by $f(z)$ and the value of the previous by $f(a)$.
]

Let's apply this to:
$
  F(z) = (f(z)-f(a))/(z-a)
$
this is not defined for $z=a$ but satisfies $lim_(z arrow a) (z-a) F(z) = 0$. The limit of $F(z)$ as $z arrow a$ is $f'(a)$. Thus there exists an analytic function which is equal to $F(z)$ for $z eq.not a$ and $f'(a)$ for $z = a$. Let's denote this function by $f_1 (z)$. We repeat this for:
$
  (f_1 (z) - f_1 (a))/(z-a)
$
giving us $f_2 (z)$ which is $f'_1(a)$ for $z = a$, etc. This recursive scheme can be written as:
$
         f(z) & = f(a) + (z-a) f_1 (z) \
      f_1 (z) & = f_1 (a) + (z-a) f_2 (z) \
              & dots \
  f_(n-1) (z) & = f_(n-1) (a) + (z-a) f_n (z)
$
these are trivially valid for $z = a$, and we obtain:
$
  f(z) = f(a) + (z-a) f_1 (a) + (z-a)^2 f_2 (a) + dots + (z-a)^(n-1) f_(n-1) (a) + (z-a)^n f_n (z)
$
differentiating $n$ times and letting $z=a$ gives:
$
  f^((n)) (a) = n! f_n (a)
$
this determines all coefficients $f_n (a)$, and we obtain the following form of Taylor's theorem:

#thm[
  If $f(z)$ is analytic in a region $Omega$, containing $a$, it is possible to write:
  $
    f(z) = f(a) + f'(a) (z-a) &+ (f'' (a))/2 (z-a)^2 + dots \
    &+ (f^(n-1) (a))/(n-1)! (z-a)^(n-1) + f_n (z) (z-a)^n
  $
  where $f_n (z)$ is analytic in $Omega$.
]

note that this finite development is distinct from the infinite Taylor series. This development is however sometimes more useful for describing local properties of $f(z)$. This is in part due to us being able to write:
$
  f_n (z) = 1/(2 pi i) integral_C (f_n (zeta) dd(zeta))/(zeta-z)
$
if we were to substitute the finite development for $f_n (zeta)$ then we'd get one main term with $f(zeta)$ the rest would be of the form:
$
  F_nu (a) = integral_C (dd(zeta))/((zeta-a)^nu (zeta-z))
$
and
$
  F_1 (a) = 1/(z-a) integral_C (1/(zeta-z) - 1/(zeta- a)) dd(zeta) = 0
$
for all $a$ inside $C$ $(2 pi i - 2 pi i)$. From a previous lemma we have $F_(nu +1) (a) = F_1^((nu)) (a) \/nu!$ and thus $F_nu (a) = 0$ for all $nu >= 1$. So we get:
$
  f_n (z) = 1/(2pi i) integral_C (f(zeta) dd(zeta))/((zeta-a)^n (zeta-z))
$
which is valid inside $C$.

=== Zeros and poles
Assume $f(a)$ and all $f^((nu)) (a)$ vanish, then we can write:
$
  f(z) = f_n (z) (z-a)^n
$
we can estimate $f_n (z)$ using the previous integral. The disk with circumference $C$ has to be contained in $Omega$ wherein $f(z)$ is defined and analytic. $abs(f(z))$ has a maximum $M$ on $C$, and if the radius of $C$ is denoted by $R$, we find:
$
       f_n (z) & = 1/(2 pi i) integral_C (f(zeta) dd(zeta))/((zeta-a)^n (zeta-z)) \
  abs(f_n (z)) & <= M/(2 pi) 1/R^n 1/(R - abs(z-a)) 2 pi R \
  abs(f_n (z)) & <= (M)/(R^(n-1)(R-abs(z-a)))
$
for $abs(z-a) < R$. Thus:
$
  abs(f(z)) <= (abs(z-a)/R)^n (M R)/(R - abs(z-a))
$
since $abs(z-a) < R$ this goes to $0$ as $n arrow oo$. Thus $f(z) = 0$ inside $C$. Is this also true for all of $Omega$? We let $E_1$ be the set on which $f(z)$ and all derivatives vanish, and $E_2$ the set on which the function or one of the derivatives is different from zero. $E_1$ is open by the above and $E_2$ is open since the function and all derivatives are continuous. So one of them must be empty. If $E_2$ is empty then the function is identically $0$, and if $E_1$ is empty then $f(z)$ can never vanish with all its derivatives.

We assume $f(z)$ is not identically zero. Then if $f(a) = 0$ there exists a first derivative $f^((h)) (a)$ which is nonzero. This makes $a$ a zero of order $h$. By the above we have just argued that there are no zeros of infinite order. This makes analytic functions similar to polynomials, and like with polynomials we can write $f(z) = (z-a)^h f_h (z)$ where $f_h (z)$ is analytic and $f_n (a) eq.not 0$. Also since $f_h (z)$ is continuous we have $f_h (z) eq.not 0$ in a neighborhood of $a$ and $z=a$ is the only zero of $f(z)$ is this neighborhood. The zeros of an analytic function which does not vanish identically are isolated.

This gives a uniqueness theorem: If $f(z)$ and $g(z)$ are analytic in $Omega$ and if $f(z) = g(z)$ on a set which has an accumulation point in $Omega$, then $f(z)$ is identically equal to $g(z)$. This follows from the difference $f(z) - g(z)$. Let $a$ be the accumulation point and define $h(z) = f(z)- g(z)$ this function is analytic, consider $h(a)$ and all the derivatives. At the accumulation point $h(a)$ and all derivatives vanish, since the only power series that can describe the function at that point is the zero-series. Thust $h(z) equiv 0 => f(z) equiv g(z)$.

This means that if $f(z)$ is identically zero in a subregion of $Omega$, then it is identically zero in $Omega$, similarly if it vanished on an arc which does not reduce to a point. This also means that an analytic function is uniquely determined by its values on any set with an accumulation point, in the region where its analytic.

Consider some $f(z)$ analtyic in a neighborhood of $a$, except at $a$ itself, i.e. in the region $0 < abs(z-a) < delta$. $a$ is an isolated singularity. The case of a removable singularity we have already talked about, here we can just define $f(a)$ such that $f(z)$ becomes analytic in $abs(z-a) < delta$. If $lim_(z arrow a) f(z) = oo$ we call $a$ a pole of $f(z)$, and we set $f(a) = oo$. There exists a $delta' <= delta$ such that $f(z) eq.not 0$ for $0 < abs(z-a) < delta'$ within this region $g(z) = 1\/f(z)$ is defined and analytic but the singularity of $g(z)$ at $a$ is removable, and $g(z)$ has an analytic extension with $g(a) = 0$. Since $g(z)$ does not vanish identically, given that $f(z)$ just has a pole, the zero at $a$ is of finite order, and we can write $g(z) = (z-a)^h g_h (z)$ with $g_h (a) eq.not 0$. $h$ is called the order of the pole, and $f(z)$ can be written as $f(z) = (z-a)^(-h) f_h (z)$ with $f_h (z) = 1\/g_h (z)$ being analytic and nonzero in a neighborhood of $a$.

A function which is analytic in a region $Omega$ except for poles is meromorphic in $Omega$. Or for all $a in Omega$ there is a neighborhood $abs(z-a) < delta subset Omega$ where $f(z)$ is analytic everywhere, or just analytic for $0 < abs(z-a) < delta$, with the isolated singularity being a pole, note that these are isolated by definition. The quotient $f(z)\/g(z)$ of two analytic functions in $Omega$ is a meromorphic function, given that $g(z)$ is not identically zero, the possible poles are the zeros of $g(z)$, but a common zero of $f(z)$ and $g(z)$ could be a removable singularity. Generally the sum, product etc. of meromorphic functions is also meromorphic.

Consider: $ lim_(z arrow a) abs(z-a)^alpha abs(f(z)) & =0 \
lim_(z arrow a) abs(z-a)^alpha abs(f(z)) & =oo $ for real $alpha$. If the first holds for some $alpha$, then obviously it'll hold for all bigger $alpha$, and some integer $m$. In this case $(z-a)^m f(z)$ has a removable singularity and vanishes for $z = a$. If $f(z)$ is identically zero, then its true for all $alpha$, otherwise $(z-a)^m f(z)$ has a zero of finite order $k$---in this case its true for all $alpha > h = m-k$, while the second will hold for all $alpha < h$. If the second holds for some $alpha$ then its true for all smaller $alpha$, and some integer $n$. Then $(z-a)^n f(z)$ has a pole of finite order $l$, and letting $h = n + l$, we again have that the first holds for $alpha > h$ and the second holds for $a < h$. Thus either $f(z)$ vansishes identically, which is boring, or there is some integer $h$ such that the first condition holds for $alpha > h$, and the second condition holds for $alpha < h$, or lastly neither holds for any $alpha$.

In the second case we call $h$ the algebraic order of $f(z)$---positive for poles, negative for zeros, and zero if $f(z)$ is analytic but $eq.not 0$ at $a$. Notably this number is always an integer. In the case of a pole of order $h$, we expand the analytic function $(z-a)^h f(z)$:
$
  (z-a)^h f(z) = B_h + B_(h-1) (z-a) + dots + B_1 (z-a)^(h-1) + phi(z) (z-a)^h
$
with $phi(z)$ analytic at $z = a$. For $z eq.not a$ we divide by $(z-a)^h$:
$
  f(z) = B_h (z-a)^(-h) + B_(h-1) (z-a)^(-h +1) + dots + B_1 (z-a)^(-1) + phi(z)
$
everything apart from $phi(z)$ is the singular part of $f(z)$. Every pole thus have a well-defined singular part. The difference of two functions with the same singular part is analytic.

In the third case, namely that neither holds for any $alpha$, then $a$ is an essential isolated singularity. In this case our function is both unbounded and comes arbitrarily close to zero---this is due to Weierstrass:
#thm[
  An analytic function comes arbitrarily close to any complex value in every neighborhood of an essential singularity.
]
#proof[
  If this was false we could find a number $A$ and a $delta > 0$ such that: $abs(f(z)-A) > delta$ in a neighborhood of $a$. Then for any $alpha < 0$: $lim_(z arrow a) abs(z-a)^alpha abs(f(z)-A) = oo$, and thus $a$ is not an essential singularity of $f(z)-A$. Then there is some $beta>0$ such that $lim_(z arrow a) abs(z-a)^beta abs(f(z)-A) = 0$. In this case $lim_(z arrow a) abs(z-a)^beta abs(A) = 0 => lim_(z arrow a) abs(z-a)^beta abs(f(z)) = 0$, and thus $a$ would not be an essential singularity. By contradiction we are done.
]

Consider a function $f(z)$ being analytic and not identically zero in an open disk $Delta$. Let $gamma$ be a closed curve in $Delta$ such that $f(z) eq.not 0$ on $gamma$. Assume that $f(z)$ has a finite number of zeros in $Delta$, and denote them by $z_1, z_2, dots, z_n$ where each zero is repeated as many times as its order. We can write $f(z) = (z-z_1)(z-z_2) dots (z-z_n) g(z)$, where $g(z)$ is analytic and nonzero in $Delta$. Further we can write:
$
  (f'(z))/(f(z)) = 1/(z-z_1) + 1/(z-z_2) + dots + 1/(z-z_n) + (g'(z))/(g(z))
$
for $z eq.not z_j$ and on $gamma$. Since $g(z) eq.not 0$ in $Delta$, we have by Cauchy's theorem:
$
  integral_gamma (g'(z))/(g(z)) dd(z) = 0
$
By definition of the index:
$
  n(gamma, z_1) + n(gamma,z_2) + dots + n(gamma,z_n) = 1/(2pi i) integral_gamma (f'(z))/(f(z)) dd(z)
$
$gamma$ is contained in a smaller concentric disk $Delta' subset Delta$. $f(z)$ could have infinitely many zeros in $Delta$, but it only has a finite number of zeros in $Delta'$. Thus we can apply this to $Delta'$, with the zeros outside satisfying $n(gamma,z_j)=0$. We have just proved:
#thm[
  Let $z_j$ be zeros of an analytic $f(z)$ in $Delta$, which does not vanish identically, each zero being counted as many times as its order. For every closed $gamma$ in $Delta$ which does not pass through a zero:
  $
    sum_j n(gamma, z_j) = 1/(2 pi i) integral_gamma (f'(z))/(f(z)) dd(z)
  $
  where the sum has a finite number of terms $eq.not 0$.
]

We can rewrite this by $w = f(z)$ which maps $gamma$ onto a closed $Gamma$ in the $w$-plane:
$
  integral_Gamma dd(w)/w = integral_gamma (f'(z))/(f(z)) dd(z)
$
the theorem can then be restated as:
$
  n(Gamma,0) = sum_j n(gamma, z_j)
$
If we know that every $n(gamma, z_j)$ is either $1$ or $0$ then the theorem immediately gives us the total number of zeros enclosed by $gamma$---this is the case for $gamma = C$.

Let $a in CC$ and apply the theorem to $f(z)-a$, the zeros will be the roots of $f(z)=a$, and we'll denote them by $z_j (a)$.
$
  sum_j n(gamma, z_j (a)) = 1/(2 pi i) integral_gamma (f'(z))/(f(z)-a) dd(z)
$
or, assuming $f(z) eq.not a$ on $gamma$:
$
  n(Gamma, a) = sum_j n(gamma, z_j (a))
$
if $a$ and $b$ are both in the region determined by $Gamma$ then $n(Gamma, a) =n(Gamma,b) => sum_j n(gamma, z_j (a)) = sum_j n(gamma, z_j (b))$. If $gamma = C$ it follows that $f(z)$ takes the values $a$ and $b$ equally many times inside $gamma$---note that in this section we use a circle for simplicity, any simple closed curve would do, we just require that every $n(gamma, z_j)$ is $1$ or $0$.

#thm[
  Let $f(z)$ be analytic at $z_0$, $f(z_0) = w_0$, and assume $f(z)-w_0$ has a zero of order $n$ at $z_0$. If $epsilon > 0$ is small enough, then there exists a corresponding $delta > 0$ such that for all $a$ with $abs(a-w_0) < delta$ the equation $f(z)=a$ has exactly $n$ roots in the disk $abs(z-z_0) < epsilon$.
]
#proof[
  We can pick $epsilon$ such that $f(z)$ is defined and analytic for $abs(z-z_0) <= epsilon$---and so that $z_0$ is the only zero of $f(z)-w_0$ in this disk. Let $gamma$ be the circle $abs(z-z_0) = epsilon$ and $Gamma$ its image under $w = f(z)$. Since $w_0$ belongs to the complement of the closed set $Gamma$, then there exists a neighborhood $abs(w-w_0) < delta$ which does not intersect $Gamma$. It follows that all $a$ in this neighborhood are the same number of times inside of $gamma$. $f(z)=w_0$ has $n$ coinciding roots within $gamma$, so every $a$ is taken $n$ times. If $epsilon$ is small enough then every root of $f(z)=a$ will be simple for $a eq.not w_0$---we just need to pick $epsilon$ so that $f'(z)$ does not vanish for $0 < abs(z-z_0) < epsilon$
]

So this theorem essentially says that values near a zero of order $n$ are taken $n$ times in a small disk.

#corollary[
  A nonconstant analytic function maps open sets onto open sets.
]
#proof[
  This is just saying that every small enough disk $abs(z-z_0) < epsilon$ contains a neighborhood $abs(w-w_0) < delta$.
]

For $n=1$ we have a one-to-one correspondence between the disk $abs(w-w_0) < delta$ and an open subset $Delta$ of $abs(z-z_0) < epsilon$. Since open sets in the $z$-plane correspond to open sets in the $w$-plane the inverse of $f(z)$ is continuous, and the mapping is topological. This mapping can be restricted to a neighborhood of $z_0$ in $Delta$, and we get:
#corollary[
  If $f(z)$ is analytic at $z_0$ with $f'(z_0) eq.not 0$, it maps a neighborhood of $z_0$ conformally and topologically onto a region.
]
It also follows that the inverse function is analytic, and hence the inverse is also conformal.  Similarly if the local mapping is one-to-one, then the previous theorem can hold only with $n=1$, and then $f'(z_0)$ must be different from zero.

With $n>1$ this can still be described precisely. We can write:
$
  f(z) - w_0 = (z-z_0)^n g(z)
$
with $g(z)$ analytic at $z_0$ and $g(z_0) eq.not 0$. Let $epsilon > 0$ such that $abs(g(z)-g(z_0)) < abs(g(z_0))$ for $abs(z-z_0) < epsilon$. In this neighborhood we can define a single-valued analytic branch of $root(n, g(z)) = h(z)$. So we have:
$
  f(z)-w_0 & = zeta(z)^n \
   zeta(z) & = (z-z_0) h(z)
$
since $zeta'(z_0) = h(z_0) eq.not 0$ the mapping $zeta=zeta(z)$ is topological in a neighborhood of $z_0$. In the other direction we have the mapping $w = w_0 + zeta^n$ which determines $n$ equally spaced values $zeta$ for each $w$.

#pagebreak()
=== The Maximum Principle
#thm[The maximum principle][
  If $f(z)$ is analytic and non-constant in a region $Omega$, then its absolute value $abs(f(z))$ has no maximum in $Omega$.
]
#proof[
  This uses corollary 1. If $w_0 = f(z_0)$ is any value in $Omega$, then there exists some neighborhood $abs(w-w_0) < epsilon$ contained in the image of $Omega$. In this neighborhood there are points of modulus $> abs(w_0)$, hence $abs(f(z_0))$ is not the maximum of $abs(f(z))$.
]
The same theorem can be stated as:
#thm[
  If $f(z)$ is defined and continuous on a closed bounded set $E$ and analytic on the interior of $E$, then the maximum of $abs(f(z))$ on $E$ is assumed on the boundary of $E$.
]
#proof[
  $E$ is compact, so $abs(f(z))$ has a maximum on $E$. Assume this is at $z_0$---if $z_0$ is on the boundary we are done. If $z_0$ is an interior point, then $abs(f(z_0))$ is also the maximum of $abs(f(z))$ in a disk $abs(z-z_0) < delta$ contained in $E$. This is only possible if $f(z)$ is constant in the part of the interior of $E$ containing $z_0$---by the Maximum principle. By continuity $abs(f(z))$ is equal to its maximum on the whole boundary of that component---this boundary is not empty and is contained in the boundary of $E$. Thus the maximum is always assumed at a boundary point.
]

_[Remark]_

We can also prove this as a consequence of Cauchy's integral formula. If we let $gamma$ be a circle with center $z_0$ and radius $r$, we can write $zeta = z_0 + r e^(i theta)$, $dd(zeta) = i r e^(i theta) dd(theta)$ on $gamma$ and for $z = z_0$ we get:
$
  f(z_0) = 1/(2pi) integral_0^(2 pi) f(z_0 + r e^(i theta)) dd(theta)
$
so the value of an analytic function at the center of a circle is the artihmetic mean of values on the circle, given that $abs(z-z_0) <= r$ is within the region on analyticity. We get the following inequality:
$
  abs(f(z_0)) <= 1/(2 pi) integral_0^(2 pi) abs(f(z_0+r e^(i theta))) dd(theta)
$
Now let $abs(f(z_0))$ be a maximum, then $abs(f(z_0 + r e^(i theta))) <= abs(f(z_0))$. If the strict inequality holds for one value of $theta$, then by continuity it holds on an entire arc. But then the mean of $abs(f(z_0+r e^(i theta)))$ would be stricly smaller then $abs(f(z_0))$, giving the contradiction $abs(f(z_0)) < abs(f(z_0))$. So $abs(f(z))$ must be equal to $abs(f(z_0))$ on all sufficiently small circles $abs(z-z_0) = r$, and thus in a neighborhood of $z_0$. It follows that $f(z)$ must reduce to a constant. We prefer the first proof, since it shows that the maximum principle follows from the topology of the mappings  by analytic functions. _[\\Remark]_

Consider now an analytic $f(z)$ on the open disk $abs(z) < R$ and which is continuous on the closed disk $abs(z) <= R$. We know that if $abs(f(z)) <= M$ on $abs(z) = R$ then $abs(f(z)) <= M$ on the whole disk. With equality if and only if $f(z)$ is constant with absolute value $M$. This also means that $f(z)$ takes some value of modulus $< M$, we'd like to better estimate this. Theorems that do this are very useful, and the following is an example:
#thm[Lemma of Schwarz][
  If $f(z)$ is analytic for $abs(z) < 1$ and satisfies $abs(f(z)) <= 1$ and $f(0)=0$, then $abs(f(z)) <= abs(z)$ and $abs(f'(0)) <= 1$.
  If $abs(f(z)) = abs(z)$ for some $z eq.not 0$, or if $abs(f'(0)) = 1$, then $f(z) = c z$ with $abs(c) = 1$.
]
#proof[
  We apply the maximum principle to $f_1 (z)$ which is $f(z)\/z$ for $z eq.not 0$ and $f'(0)$ for $z = 0$. On $abs(z) = r < 1$ it is by assumption of absolute value $<= 1\/r$, hence $abs(f_1 (z)) <= 1\/r$ for $abs(z) <= r$. In the limit $r arrow 1$ we find $abs(f_1 (z)) <= 1$ for all $z$, and this is what the theorem states. If the equality holds at any point, then $abs(f_1 (z))$ attains its maximum, and then $f_1 (z)$ must reduce to a constant.
]

Note that the assumptions are essentially just a result of a normalization, even though they seem quite specialized. However, if we know the conditions hold on a disk of radius $R$, then we can apply the theorem to $f(R z)$, for which we obtain $abs(f(R z)) <= abs(z)$, which can be written as $abs(f(z)) <= abs(z)\/R$---similarly if the upper bound of the modulus is $M$, we apply the theorem to $f(z)\/M$, or more generally $f(R z)\/M$, giving the inequality $abs(f(z))<= M abs(z)\/R$. We can also make $f(0)=0$ more arbitrary with $f(z_0)=w_0$ with $abs(z_0) < R$ and $abs(w_0) < M$. We define two linear transformations $T$ and $S$, with $zeta = T z$ mapping $abs(z) < R$ onto $abs(zeta) < 1$ with $z_0$ going to the origin, and $S w$ making $S w_0 = 0$ and mapping $abs(w) < M$ onto $abs(S w) < 1$. Now the function $S f(T^(-1) zeta)$ satisfies the hypothesis giving the inequality $abs(S f(z)) <= abs(T z)$, explicitely this can be written as:
$
  abs((M ( f(z)-w_0))/(M^2 - overline(w)_0 f(z))) <= abs((R(z-z_0))/(R^2 - overline(z)_0 z))
$
#pagebreak()
== Cauchy's Theorem revisited
Previously only the case of a circular region was considered, which worked well for studying local properties, but we'd like to generalize this. We can either try to characterize the regions where it holds, or we can consider some arbitrary region and then look for curves $gamma$ for which it holds.

First we generalize the line integral:
$
  integral_(gamma_1 + gamma_2 + dots + gamma_n) f dd(z) = integral_gamma_1 f dd(z) + dots + integral_gamma_n f dd(z)
$
this is valid when $gamma_1, gamma_2, dots, gamma_n$ subdivides the arc $gamma$. The RHS has meaning for any finite collection, so nothing prevents us from considering an arbitrary formal sum $gamma_1 + dots + gamma_n$, which doesn't have to be an arc, if we define the integral like this---these formal sums of arcs are called chains, and we want to consider integrals over arbitrary chains. Different formal sums can represent the same chain, so two chains are identical if they yield the same line integral for all functions $f$---so permuting two arcs, subdiving an arc, fusion of subarcs, reparametrization of an arc, and cancellation of opposite arcs all don't change the chain. The sum of two chains is defined as one would expect, and for identical chains we denote the sum as a multiple. Using this every chain can be written as:
$
  gamma = a_1 gamma_1 + a_2 gamma_2 + dots + a_n gamma_n
$
with all $gamma_i$ different and all $a_i$ positive. For opposite arcs we can write $a (- gamma) = - a gamma$ letting us cancel opposite $gamma_i$. Similarly we can add arcs with $a_i = 0$.

A chain is a cycle if it can be written as a sum of closed curves---this means that a chain is a cycle if in any representation the initial and end points of the arcs are identical in pairs. This could either be as a single loop or as multiple and distinct loops.

We'll consider chains contained in a given open set $Omega$. So our chains will only be represented by arcs in $Omega$. All theorems we have formulated so far for closed curves in a region are also valid for arbitrary cycles in a region---in particular the integral of an exact differential over any cycle is zero. Note that the index is defined exactly as before, now just with an obvious additive law:
$
  n ( gamma_1 + gamma_2, a) = n(gamma_1, a) + n(gamma_2, a)
$
It turns out that Cauchy's theorem is valid for simply connected regions, by which we mean regions without holes.
#def[
  A region is simply connected if its complement with respect to the extended plane is connected.
]
Since if our region had a hole, then the complement would be disconnected---note that this definition is not usually accepted for more than two real dimensions. This definition is equivalent to the more usual definition that any closed curve can be contracted to a point, but for our purposes the previous gives us the essential results faster.

Some easy examples of simply connected regions are the disk, half plane, and a parallel strip. The last of which shows why we take the complement with respect to the extended plane, else this wouldn't be simply connected---one could treat the point at infinity as a bridge between two otherwise disconnected regions in the finite plane. One could use regions on the Riemann sphere, but we'll only treat regions in the finite plane. With this convention something like everything outside a circle wouldn't be simply connected, since the complement consisting of a disk and the point of infinity would not be connected.

#thm[
  A region $Omega$ is simply connected if and only if $n(gamma, a) = 0$ for all cycles $gamma$ in $Omega$ and all points $a$ which do not belong to $Omega$.
]

So any curve in $Omega$ can't wind around a point not in $Omega$. For the necessity let $gamma$ be any cycle in $Omega$. If the complement of $Omega$ is connected, then it must be contained in one of the regions determined by $gamma$---and as $oo$ belongs to the complement, then this must be the unbounded region. Therefore $n(gamma, a) = 0$, for all finite points in the complement.

For the other direction we need a construction, and we prove the contrapositive. We assume that the complement of $Omega$ can be written as a union $A union B$ of two disjoint closed sets. One of these contain $oo$, and the other is then bounded---let the bounded set be $A$. The sets $A$ and $B$ have a shortest distance $delta > 0$. Cover the whole plane with a mesh of squares $Q$ with sides $< delta \/ sqrt(2)$. We can do this such that a point $a in A$ lies at the center of a square. Denote the boundary of $Q$ by $dd(Q, d: partial)$, and we assume that the squares are closed, and that the interior of $Q$ lies to the left of the directed line segments making up $dd(Q, d: partial)$. Consider the cycle $gamma = sum_j dd(Q_j, d: partial)$, with the sum ranging over all $Q_j$ having a point in common with $A$. Since $a$ is contained in only one square, we have $n(gamma, a) = 1$, furthermore $gamma$ never meets $B$. Similarly if we do the proper cancellations then $gamma$ also never meets $A$. Therefore $gamma$ is contained in $Omega$, and we are done.

Note that Cauchy's theorem is not valid for regions which not simply connected. If we have a cycle $gamma$ in $Omega$ with $n(gamma, a) eq.not 0$ for some $a$ outside $Omega$, then $1\/(z-a)$ would be analytic in $Omega$ while the integral:
$
  integral_gamma dd(z)/(z-a) = 2 pi i n(gamma, a) eq.not 0
$

=== Homology
#def[
  A cycle $gamma$ in an open set $Omega$ is homologous to zero with respect to $Omega$ if $n(gamma, a) = 0$ for all points $a$ in the complement of $Omega$.
]
This is essentially the important property that all cycles need to have for our region to be simply connected. We write $gamma tilde 0 " "(mod Omega)$, when it is clear what set we are referring to we can just write $gamma tilde 0$. We also sometimes write $gamma_1 tilde gamma_2$ meaning $gamma_1-gamma_2 tilde 0$. Homologies add and subtract, and $gamma tilde 0 " " (mod Omega)$ implies $gamma tilde 0 " " (mod Omega')$ for all $Omega' supset Omega$---so if a cylce is homologous to zero in a smaller region then it's naturally also homologous to zero in a larger region containing the smaller region.

=== Cauchy's Theorem
Now we can state Cauchy's theorem proper:
#thm[Cauchy's Theorem][
  If $f(z)$ is analytic in $Omega$, then:
  $
    integral_gamma f(z) dd(z) = 0
  $
  for every cycle $gamma$ which is homologous to zero in $Omega$.
]

Alternatively if $gamma$ is such that the integral holds for analytic functions of the form $1\/(z-a)$ with $a$ not in $Omega$, then it holds for all analytic functions in $Omega$. With the previous theorem about simple connectivity we immedaiately get the following:
#corollary[
  If $f(z)$ is analytic in a simply connected region $Omega$, then:
  $
    integral_gamma f(z) dd(z) = 0
  $
  for all cycles $gamma$ in $Omega$.
]

Since all cycles in a simply connected region are by definition homologous to zero.

The validity of:
$
  integral_gamma f(z) dd(z) = 0
$
for all closed curves $gamma$ in some region means that the integral is path-independent, or that $f dd(z)$ is an exact differential, implying that there is some analytic function $F(z)$ with $F'(z) = f(z)$---thus every analytic function is a derivative in a simply connected region. This path-independence is of course also quite nice when we want to solve integrals, since we can essentially pick our path or contour such that the integral becomes as easy as possible.
#corollary[
  If $f(z)$ is analytic and $eq.not 0$ in a simply connected region $Omega$ then it is possible to define single-valued analytic branches of $log f(z)$ and $root(n, f(z))$ in $Omega$.
]
Actually we know that some analytic $F(z)$ exists in $Omega$ with $F'(z) = f'(z) \/ f(z)$. The function $f(z) e^(- F(z))$ has derivative zero and is therefore constant. Choosing some $z_0 in Omega$ and one of the many values of $log f(z_0)$ we find:
$
  e^(F(z) - F(z_0) + log f(z_0)) = f(z)
$
so consequently we can set $log f(z) = F(z)-F(z_0) + log f(z_0)$. To define $root(n, f(z))$ we can write it in the form $exp ((1\/n) log f(z))$.

#proof[of Cauchy's theorem][
  We make a construction, similar to before. Assume that $Omega$ is bounded, and otherwise arbitrary. Given $delta > 0$ we cover the plane by a mesh of squares with side $delta$, and denote them by $Q_j$ with $j in J$, the closed squares contained in $Omega$, and since $Omega$ is bounded the set $J$ is finite---given that $delta$ is small enough this set will be non-empty. The union on $Q_j$ with $j in J$ consists of closed regions whose oriented boundaries make up the cycle:
  $
    Gamma_delta = sum_(j in J) dd(Q_j, d: partial)
  $
  evidently $Gamma_delta$ is a sum of oriented line segments which are sides of exactly one $Q_j$. Denote the interior of the union $union_(j in J) Q_j$ by $Omega_delta$.

  Let $gamma$ be a cycle homologous to zero in $Omega$, we pick $delta$ so small that $gamma$ is contained in $Omega_delta$. Consider a point $zeta in Omega-Omega_delta$---it belongs to at least one $Q$ which is not a $Q_j$. There is a point $zeta_0 in Q$ not in $Omega$. We can join $zeta$ and $zeta_0$ by a line segment which lies in $Q$ and therefore doesn't meet $Omega_delta$.  Since $gamma$ is contained in $Omega_delta$ it follows that $n(gamma, zeta) = n(gamma,zeta_0) = 0$, in particular $n(gamma,zeta)=0$ for all points $zeta$ on $Gamma_delta$.

  Now let's say that $f$ is analytic in $Omega$. If $z$ lies in the interior of $Q_j_0$ then:
  $
    1/(2 pi i) integral_dd(Q_j, d: partial) (f(zeta)dd(zeta))/(zeta-z) = cases(f(z) #h(10pt) &"if" j = j_0, 0 &"if" j eq.not j_0)
  $
  then:
  $
    f(z) = 1/(2 pi i) integral_Gamma_delta (f(zeta)dd(zeta))/(zeta-z)
  $
  both sides are continuous functions of $z$, and thus this will hold for all $z in Omega_delta$. We obtain:
  $
    integral_gamma f(z) dd(z) = integral_gamma (1/(2 pi i) integral_Gamma_delta (f(zeta) dd(zeta))/(zeta-z)) dd(z)
  $
  the integrand is nice and continuous with respect to both $Gamma_delta$ and $gamma$ so we can reverse the order of integration:
  $
    integral_gamma f(z) dd(z) = integral_Gamma_delta (1/(2 pi i) integral_gamma dd(z)/(zeta-z)) f(zeta) dd(zeta)
  $
  the inside integral is just $-n(gamma, zeta) = 0$. Thus we are done for bounded $Omega$.

  If $Omega$ is unbounded, we replace it by its intersection $Omega'$ with a disk $abs(z) < R$ large enough to contain $gamma$. Any point $a$ in the complement of $Omega'$ is either in the complement of $Omega$ of lies outside the disk. In either case $n(gamma, a) = 0$ so $gamma tilde 0 " " (mod Omega')$. Then the proof is applicable to $Omega'$, and thus the theorem is valid for arbitrary $Omega$.
]

=== Multiply Connected Regions
Any region which is not simply connected is  called multiply connected. A region $Omega$ has finite connectivity $n$ if the complement of $Omega$ has $n$ components---and infinite connectivity if the complement has infintely many components. So punching $n$ holes in the Riemann sphere gives a region of connectivity $n$.

Let $A_1, dots, A_n$ be the components of the complement of $Omega$, assuming that $oo in A_n$. Let $gamma$ be an arbitrary cycle in $Omega$, if we vary $a$ over any of the components $A_i$ then $n(gamma,a)$ is constant, and in $A_n$ $n(gamma,a) = 0$. We can find cycles $gamma_i$ with $i = 1, dots, n-1$ with $n(gamma_i,a) = 1$ for $a in A_i$ and $n(gamma_i,a) = 0$ for all other points outside of $Omega$---i.e. we can find cycles $gamma_i$ that fully circle $A_i$.

Given a cycle $gamma$ in $Omega$, let $c_i$ be the constant value of $n(gamma,a)$ for $a in A_i$. Any point outside $Omega$ has the index zero with respect to the cycle $gamma-c_1 gamma_1-dots - c_(n-1) gamma_(n-1)$, or:
$
  gamma tilde c_1 gamma_1 + c_2 gamma_2 + dots + c_(n-1) gamma_(n-1)
$
so every cycle is homologous to a linear combination of the cycles $gamma_1, gamma_2, dots, gamma_(n-1)$. This linear combination is unique, since if two linear combinations were homologous to the same cycle their difference, another linear combination, would be homologous to zero. It is clear however that the cycle $c_1 gamma_1 + dots + c_(n-1) gamma_(n-1)$ winds $c_i$ times around the points in $A_i$, thus it can't be homologous to zero unless all $c_i$ vanish.

We call the cycles $gamma_1, gamma_2, dots, gamma_(n-1)$ the homology basis for $Omega$. Every region with a finite basis has finite connectivity, with $n-1$ basis elements. Now for any analytic function $f(z)$ in $Omega$ we have:
$
  integral_gamma f dd(z) = c_1 integral_gamma_1 f dd(z) + dots + c_(n-1) integral_gamma_(n-1) f dd(z)
$
each $ P_i = integral_gamma_i f dd(z) $ depend only on the function, and are called modules of periodicity of $f dd(z)$.

#pagebreak()
== Residue Calculus
What we've just found is that line integrals of analytic functions essentially just depends on the periods---thus if we can find a way to calculate these efficiently, then that would be very beneficial.

Now we'll do a review of some previous results, given the proper Cauchy's theorem. Clearly all results dervied from Cauchy's theorem for a disk remain valid in arbitrary regions for all cycles homologous to zero, one example is Cauchy's integral formula:
#thm[Cauchy's integral formula][
  If $f(z)$ is analytic in a region $Omega$, then:
  $
    n(gamma, a) f(a) = 1/(2 pi i) integral_gamma (f(z) dd(z))/(z-a)
  $
]
#proof[
  Omitted, since it's just a repetition of what we've done before.
]

Note that we essentially ignore removable singularities when talking about Cauchy's theorem, since they don't change local behaviour.

Now we turn to a function $f(z)$ which is analytic in a region $Omega$ except for isolated singularities. We start by assuming only a finite number of singular points, $a_1, a_2, dots, a_n$. The region obtained by excluding these we denote by $Omega'$. For each $a_j$ there is some $delta_j > 0$ such that the doubly connected region $0 < abs(z-a_j) < delta_j$ is contained in $Omega'$. Draw a circle $C_j$ about $a_j$ with radius $< delta_j$, and let:
$
  P_j = integral_C_j f(z) dd(z)
$
The function $1\/(z-a_j)$ has period $2 pi i$. So if we define $R_j = P_j \/2 pi i$ the function:
$
  f(z)-R_j/(z-a_j)
$
has a vanishing period. The constant $R_j$ is called the residue of $f(z)$ at $a_j$.

#def[
  The residue of $f(z)$ at an isolated singularity $a$ is the unique complex number $R$ which makes $f(z) - R\/(z-a)$ the derivative of a single-valued analytic function in an annulus $0<abs(z-a)<delta$---i.e vanishing period.
]

Commonly we denote $R = "Res"_(z=a) f(z)$. Let $gamma$ be a cycle in $Omega'$ which is homologous to zero with respect to $Omega$, then:
$
  gamma tilde sum_j n(gamma, a_j) C_j
$
with respect to $Omega'$. Then:
$
  integral_gamma f dd(z) = sum_j n(gamma, a_j) P_j
$
with $P_j = 2 pi i R_j$:
$
  1/(2pi i) integral_gamma f dd(z) = sum_j n(gamma, a_j) R_j
$
this is the residue theorem, for a finite number of singularities---in the general case we just have to show that $n(gamma, a_j)=0$, except for some finite number of points.

#thm[Residue Theorem][
  Let $f(z)$ be analytic except for isolated singularities $a_j$ in a region $Omega$. Then
  $
    1/(2pi i) integral_gamma f(z) dd(z) = sum_j n(gamma, a_j) "Res"_(z=a_j) f(z)
  $
  for any cycle $gamma$ which is homologous to zero in $Omega$ and that does not pass through any of the points $a_j$.
]

Commonly $n(gamma, a_j) = {0, 1}$:
$
  1/(2pi i) integral_gamma f(z) dd(z) = sum_j "Res"_(z = a_j) f(z)
$
where the sum is over all singularities enclosed by $gamma$. Now we just need some easy way to find the residues. For essential singularities this is not easy, so the theorem isn't used in this case. For poles however, we look at the expansion:
$
  f(z) = B_h (z-a)^(-h) + dots + B_1 (z-a)^(-1) + phi(z)
$
and recognize that $B_1$ is the residue---since $f(z)-B_1 (z-a)^(-1)$ is a derivative. Thus if we can find the principal part at a pole we get the residue. For simple poles this is even easier since the residue is just the value of $(z-a) f(z)$ at $z=a$.
#ex[
  Consider
  $
    e^z/((z-a)(z-b))
  $
  this has poles $a$ and $b eq.not a$. The residue at $a$ is $e^a \/(a-b)$ and the residue at $b$ is $e^b \/(b-a)$. In the case that $a = b$, then we need to expand $e^z$ by Taylor's theorem
  $
    e^z = e^a + e^a (z-a) + f_2 (z) (z-a)^2
  $
  dividing by $(z-a)^2$ the residue at $z=a$ is $e^a$.
]

== The Argument principle
Cauchy's integral formula is just the residue theorem applied to the function $f(z) \/(z-a)$, which has a simple pole at $z = a$ with residue $f(a)$.

We also used it when determining the number of zeros of an analytic function. We can write, for a zero of order $h$, $f(z) = (z-a)^h f_h (z)$ with $f_h (a) eq.not 0$ and obtain
$
  f'(z) = h(z-a)^(h-1) f_h (z) + (z-a)^h f_h (z)
$
then
$
  (f'(z))/f(z) = h/(z-a) + (f'_h (z))/(f(z))
$
so $f'\/f$ has a simple pole with residue $h$. We can then generalize the previous theorem to the case of a meromorphic function. Given $f$ has a pole of order $h$, we find by the above with $-h$ instead of $h$, that $f'\/f$ has residue $-h$.

#thm[The Argument Principle][
  If $f(z)$ is meromorphic in $Omega$ with zeros $a_j$ and poles $b_k$, then:
  $
    1/(2pi i) integral_gamma (f'(z))/(f(z)) dd(z) = sum_j n(gamma, a_j) - sum_k n(gamma, b_k)
  $
  for every cycle $gamma$ which is homologous to zero in $Omega$ and does not pass through any zeros or poles.
]
The LHS can be interpreted as $n (Gamma, 0)$ where $Gamma$ is the image cycle of $gamma$. If $Gamma$ lies in a disk not containing the origin, then $n(Gamma,0)=0$---this is essentially Rouché's theorem:
#corollary[Rouché's theorem][
  Let $gamma$ be homologous to zero in $Omega$ and such that $n(gamma, z) = {0,1}$ for any $z$ not on $gamma$. If $f(z)$ and $g(z)$ are analytic on $Omega$ and satisfy $abs(f(z)-g(z)) < abs(f(z))$ on $gamma$, then $f(z)$ and $g(z)$ have the same number of zeros enclosed by $gamma$.
]
#proof[
  By assumption $f(z)$ and $g(z)$ are zero-free on $gamma$, and they satisfy:
  $
    abs((g(z))/(f(z))-1) < 1
  $
  on $gamma$. So $F(z) = g\/f$ on $gamma$ are in the open disk of center $1$ and radius $1$. So by the argument principle $n(Gamma, 0) = 0$, and we are done.
]

We can generalize the argument principle. If $g(z)$ is analytic in $Omega$, then $g(z) f'(z)\/f(z)$ has the residue $h g(a)$ at a zero $a$ of order $h$ and the resiude $-h g(a)$ at a pole. Thus:
$
  1/(2 pi i) integral_gamma g(z) (f'(z))/(f(z)) dd(z) = sum_j n(gamma,a_j) g(a_j)- sum_k n(gamma, b_k) g(b_k)
$
we can apply this to $f(z) - w$ with $abs(w-w_0) < delta$, this has $n$ roots $z_j (w)$ in the disk $abs(z-z_0) < epsilon$. With $g(z) = z$ we get:
$
  sum_(j=1)^n z_j (w) = 1/(2pi i) integral_(abs(z-z_0)=epsilon) (f'(z))/(f(z)-w) z dd(z)
$
for $n=1$ the inverse $f^(-1) (w)$ can then be written explicitely as:
$
  f^(-1) (w) = 1/(2pi i) integral_(abs(z-z_0) = epsilon) (f'(z))/(f(z)-w) z dd(z)
$
#pagebreak()
== Some Integrals
\* note ML- and Jordan's lemma.

We want to solve some real definite integrals using the techniques we have derived. Our problem is that all these techniques require us using closed curves, which when integrating along the real line obviously isn't the case. However, in many cases this can be worked around.

Consider integrals of the form:
$
  integral_0^(2pi) R(cos theta, sin theta) dd(theta)
$
i.e. where the integrand is a rational function of $cos theta$ and $sin theta$---these can typically be calculated using residues. Let's make the substitution $z = e^(i theta)$ giving:
$
  - i integral_(abs(z)=1) R[1/2 (z+1/z), 1/(2 i) (z-1/z)] dd(z)/z
$
now we just need to determine the residues which correspond to the poles of the integrand inside the unit circle.
#ex[
  Consider:
  $
    integral_0^pi dd(theta)/(a + cos theta)
  $
  with $a > 1$. We can extend the bounds:
  $
    1/2 integral_0^(2pi) dd(theta)/(a + cos theta) &= integral_0^(2 pi) dd(theta)/(2a + e^(i theta)+e^(- i theta)) \
    &= -i integral_(abs(z)=1) dd(z) /(2a z + z^2 + 1) \
    &= -i integral_(abs(z)=1) dd(z) /((z - alpha)(z+ beta))
  $
  with:
  $
    alpha & = -a + sqrt(a^2-1) \
     beta & = -a - sqrt(a^2-1)
  $
  note that $abs(alpha) < 1$ and $abs(beta) > 1$, so we only care about the residue at $alpha$ which is $1\/(alpha - beta)$ so:
  $
    integral_0^pi dd(theta)/(a + cos theta) = pi/(sqrt(a^2-1))
  $
]

Consider integrals of the form:
$
  integral_(- oo)^(oo) R(x) dd(x)
$
this converges if in $R(x)$ the degree of the denominator is at least two unit higher than the degree of the numerator, and if no pole lies on the real axis. The typical procedure is to integrate the complex function $R(z)$ over a closed curve contained the line $(-rho, rho)$ and a semicircle from $rho arrow -rho$ in the upper half plane. Then the integral would be $2pi i$ times the sum of the residues in the upper half plane. As $rho arrow oo$ the integral over the semicircle $arrow 0$ (by ML-lemma) so we obtain:
$
  integral_(- oo)^oo R(x) dd(x) = 2 pi i sum_(y > 0) "Res" R(z)
$

Similarly can be done for integrals of the form
$
  integral_(- oo)^oo R(x) e^(i x) dd(x)
$
whose real and imaginary parts correspond to the important integrals:
$
  integral_(- oo)^oo R(x) cos x dd(x) \
  integral_(-oo)^oo R(x) sin x dd(x)
$
since $abs(e^(i x)) = e^(-y)$ is bounded in the upper half plane, we can again conclude that the integral over the semicircle tends to zero, provided that $R(z)$ has a zero of at least order two at infinity. We obtain:
$
  integral_(- oo)^oo R(x) e^(i x) dd(x) = 2 pi i sum_(y > 0) "Res" R(z) e^(i z)
$
this also holds if we only have $R(oo) = 0$, i.e. a simple zero at infinity---see pg. 156-157 in Ahlfors.

Here we've assumed that $R(z)$ has no poles on the real axis, since then the integral wouldn't exist. However we could have some integrand where the poles of $R(z)$ line up with the zeros of $sin x$ or $cos x$---e.g. if $R(z)$ has a simple pole at $z=0$, then the $sin x$ integral would have meaning. Here we use a contour which makes a semicircle around the pole at $z=0$, and denoting the residue at zero by $B$ we can write $R(z) e^(i z) = B\/z + R_0 (z)$ with $R_0 (z)$ analytic at the origin. The integral of the first term over the semicircle is $pi i B$, while the second term $arrow 0$ as $delta arrow 0$. Thus we get:
$
  lim_(delta arrow 0) integral_(- oo)^(- delta) + integral_delta^oo R(x) e^(i x) dd(x) = 2 pi i [sum_(y>0) "Res" R(z)e^(i z) + 1/2 B]
$
the LHS limit is called the Cauchy principal value---note that half the residue at zero has been included, as if half the residue lies in the upper-half plane. In the general case we have:
$
  "pr.v." integral_(- oo)^oo R(x) e^(i x) dd(x) = 2pi i sum_(y > 0) "Res" R(z)e^(i z) + pi i sum_(y = 0) "Res" R(z)e^(i z)
$
we require all poles on the real axis are simple, and we assume that $R(oo) = 0$.
#ex[
  Consider:
  $
    "pr.v." integral_(- oo)^oo e^(i x)/x dd(x) = pi i
  $
  since the only pole is at $x = 0$, this pole is simple and has residue $1$. Taking the imaginary part we find:
  $
    "pr.v." integral_(-oo)^oo (sin x)/x dd(x) = 2 integral_0^oo (sin x)/x dd(x) = pi
  $
  where pr.v. isn't needed since we never cross $x=0$ in the integral.
]

Note that many more general integrals can be rewritten to be solved like this:
$
  integral_(-oo)^oo R(x) e^(i m x) dd(x) = 1/m integral_(-oo)^oo R(x/m) e^(i x) dd(x)
$
where we can pretty much always rewrite $sin m x$ and $cos m x$ to $e^(i m x)$.

Consider integrals of the form:
$
  integral_0^oo x^alpha R(x) dd(x)
$
with $0 < alpha < 1$. For convergence $R(z)$ must have a zero of at least order two at $oo$, and at most a simple pole at the origin---note that with this integrand $R(z)z^alpha$ is not single-valued.

We proceed by subbing $x = t^2$ giving:
$
  2 integral_0^oo t^(2 alpha +1) R(t^2) dd(t)
$
for the function $z^(2 alpha)$ we can pick the branch with argument between $- pi alpha$ and $3 pi alpha$, ignoring the negative imaginary axis then this function is analytic. We can then apply the residue theorem to $z^(2 alpha+1) R(z^2)$, with what is essentially half a keyhole contour, i.e. two semicircles connected on the real line. Under our assumptions then the integrals over the semicircles vanish. So we get:
$
  integral_(-oo)^oo z^(2 alpha +1) R(z^2) dd(z) = integral_0^oo (z^(2 alpha + 1) + (-z)^(2 alpha +1)) R(z^2)
$
or rewriting:
$
  (1 - e^(2 pi i alpha)) integral_0^oo z^(2 alpha +1) R(z^2) dd(z)
$
to which we can apply the residue theorem---i.e. we need to determine the residues of $z^(2 alpha+1) R(z^2)$ in the upper half plane. These turn out to be the same as the residues of $z^alpha R(z)$ in the whole plane, in this case we use the branch of $z^alpha$ with argument between $0$ and $2 pi alpha$---however this doesn't conform to the hypotheses of the residue theorem, but the justification is trivial.

Finally we'll calculate the integral:
$
  integral_0^pi log sin theta dd(theta)
$
consider the function:
$
  1 - e^(2 i z) = - 2 i e^(i z) sin z = 1 - e^(- 2 y) (cos 2 x + i sin 2 x)
$
this function is real and negative for $x = n pi$, $y <= 0$. In the region derived by omitting these half lines the principal branch of $log (1 - e^(2 i z))$ is single-valued and analytic. We now apply Cauchy's theorem to the rectangle whose vertices are $0, pi, pi + i Y$ and $i Y$, but the points $0$ and $pi$ have to be avoided, we do this by small circular quadrants with radius $delta$. By periodicity the integrals over the vertical sides cancel with eachother. The integral over the upper horizontal tends to $0$ as $Y arrow oo$. The integrals over the quadrant likewise tend to $0$ as $delta arrow 0$. the imaginary part of the logarithm is bounded, so we can see this by just considering the real part. Given that $abs(1- e^(2 i z)) \/abs(z) arrow 2$ for $z arrow 0$ we get that $log abs(1-e^(2 i z))$ becomes infinite like $log delta$ and since $delta log delta arrow 0$, then the integral over the quadrant near the origin will tend to zero. Similarly applies near the $pi$ vertex, so we obtain by Cauchy's theorem:
$
  integral_gamma log(-2 i e^(i x) sin x) dd(x) = integral_0^pi log(-2 i e^(i x) sin x) dd(x) = 0
$
letting $log e^(i x) = i x$, then the imaginary part lies between $0$ and $pi$. To obtain the principal branch with imaginary part between $-pi$ and $pi$ we must pick $log (-i) = - pi i \/2$. We can write:
$
  integral_0^pi log(- 2 i e^(i x) sin x) dd(x) &= integral_0^pi log(- i)+ log 2 + log(e^(i x)) + log sin x dd(x) \
  &= pi log 2 - pi^2/2 i + pi^2/2 i + integral_0^pi log sin x dd(x) = 0 \
  => integral_0^pi log sin x dd(x) &= - pi log 2
$

#pagebreak()
= Series and product developments
\* parts of chpt. 5

We'll focus on Taylor- and Laurent-series and the Weierstrass factorization theorem. But first we go through some general properties of power series expansions.

== Power series expansions
The most essential theorem we'll prove states that a uniformly convergent sequence of analytic functions is itself analytic. To be more precise we are considering a sequence ${f_n (z)}$ where each $f_n$ is defined and analytic in a region $Omega_n$. The limit function $f$ must be considered in some region $Omega$, and clearly if this function should be defined nicely, then every point of $Omega$ should belong to all $Omega_n$ for some $n >= n_0$---generally this $n_0$ will not be the same across the region, for this reason it does not make sense to require that the convergence is uniform in $Omega$. Typically these $Omega_n$ form an increasing sequence $Omega_1 subset Omega_2 subset dots subset Omega_n subset dots$, and $Omega$ is the union of all $Omega_n$. In this case no $f_n$ is defined in all of $Omega$, but the limit $f$ may exist at every point in $Omega$, but the convergence can not be uniform. What we require instead is that ${f_n}$ converges uniformly to $f$ on every compact subset of $Omega$.

#thm[
  Assume $f_n$ is analytic in $Omega_n$, and that ${f_n}$ converges to a limit function $f(z)$ in a region $Omega$, uniformly on every compact subset of $Omega$. Then $f(z)$ is analytic in $Omega$. Further $f'_n$ converges uniformly to $f'$ on every compact subset of $Omega$.
]

#proof[
  We use Morera's theorem. Let $abs(z-a) <= r$ be a closed disk contained in $Omega$, the assumption implies that this disk lies in $Omega_n$ for all $n > n_0$. Let $gamma$ be any closed curve in $abs(z-a) < r$, we have:
  $
    integral_gamma f_n dd(z) = 0
  $
  for $n > n_0$, by Cauchy's theorem. By uniform convergence on $gamma$ we obtain:
  $
    integral_gamma f dd(z) = lim_(n arrow oo) integral_gamma f_n dd(z) = 0
  $
  so by Morera's theorem it follows that $f$ is analytic in $abs(z-a)<r$. Consequenctly $f$ is analytic in the whole region $Omega$---since it is analytic on every small open disk.

  Alternatively we can use the integral formula
  $
    f_n = 1/(2pi i) integral_C (f_n (zeta) dd(zeta))/(zeta- z)
  $
  with $C$ being the circle $abs(zeta-a) = r$ and $abs(z-a) < r$. By uniform convergence:
  $
    f = 1/(2 pi i) integral_C (f(zeta) dd(zeta))/(zeta -z)
  $
  so $f(z)$ is analytic in the disk. Using
  $
    f'_n = 1/(2 pi i) integral_C (f_n (zeta) dd(zeta))/(zeta-z)^2
  $
  a similar reasoning shows:
  $
    lim_(n arrow oo) f'_n = f'
  $
  with uniform convergence for $abs(z-a) <= rho < r$. Any compact subset of $Omega$ can be covered by a finite number of closed disks, and therefore the convergence is uniform on every compact subset.

  By repeated application we obviously get that $f^((k))_n arrow.triple f^((k))$ on every compact subset of $Omega$.
]

Originally due to Weierstrass this theorem can be stated as:
#thm[
  If a series with analytic terms
  $
    f(z) = f_1 (z) + f_2 (z)+ dots + f_n (z)+ dots
  $
  converges uniformly on every compact subset of a region $Omega$, then the sum $f(z)$ is analytic in $Omega$, and the series can be differentiated term by term.
]

#thm[
  If the functions $f_n (z)$ are analytic and $eq.not 0$ in a region $Omega$, and if $f_n (z)$ converges to $f(z)$, uniformly on every compact subset of $Omega$, then $f(z)$ is either identically zero or never equal to zero in $Omega$.
]

#proof[
  Assume $f(z)$ is not identically zero. In this case the zeros are isolated. For any $z_0 in Omega$ there is a number $r > 0$ such that $f(z)$ is defined and $eq.not 0$ for $0 < abs(z-z_0) <= r$. Particularly, $abs(f(z))$ has a positive minimum on the circle $abs(z-z_0) = r$, which denote by $C$. It follows that $1\/f_n (z)$ converges uniformly to $1\/ f(z)$ on $C$. We can conclude that:
  $
    lim_(n arrow oo) 1/(2 pi i) integral_C (f'_n (z))/(f_n (z)) dd(z) = 1/(2pi i) integral_C (f'(z))/(f (z)) dd(z)
  $
  all the LHS integrals are zero, since they give the number of roots of $f_n = 0$ inside $C$. Therefore the RHS integral must also be zero, and consequently $f(z_0) eq.not 0$. Since $z_0$ was arbitrary, the theorem follows.
]

Now we show that all analytic functions can be written as a Taylor series. According to a previous theorem if $f(z)$ is analytic in a region $Omega$ containing $z_0$ we can write:
$
  f(z) = f(z_0) + f' (z_0) (z-z_0) + dots + (f^((n)) (z_0))/n! (z-z_0)^n + f_(n+1) (z) (z-z_0)^(n+1)
$
with:
$
  f_(n+1) (z) = 1/(2 pi i) integral_C (f(zeta) dd(zeta))/((zeta-z_0)^(n+1) (zeta-z))
$
where $C$ is any circle $abs(z-z_0)=rho$ such that $abs(z-z_0)<= rho$ is contained in $Omega$. Let $M$ be the maximum of $abs(f(z))$ on $C$, then:
$
  abs(f_(n+1) (z)(z-z_0)^(n+1)) <= (M abs(z-z_0)^(n+1))/(rho^n (rho - abs(z-z_0)) )
$
so the remainder term tends uniformly to zero in every disk $abs(z-z_0) <= r < rho$. However, $rho$ can be chosed arbitrarily close to the shortest distance from $z_0$ to the boundary of $Omega$. We have proved:
#thm[
  If $f(z)$ is analytic in the region $Omega$, constaining $z_0$, then the representation:
  $
    f(z) = f(z_0) + f'(z_0) (z-z_0) + dots + (f^((n)) (z_0))/n! (z-z_0)^n + dots
  $
  is valid in the largest open disk of center $z_0$ contained in $Omega$.
]

So the radius of convergence of the Taylor series is at least the shortest distance from $z_0$ to the boundary of $Omega$.

We can also consider series like:
$
  b_0+b_1 z^(-1) + dots + b_n z^(-n) + dots
$
which can be considered an ordinary power series in $1\/z$. It will therefore converge outside some circle $abs(z) = R$, unless $R = oo$. This convergence is uniform in every region $abs(z) >= rho > R$, and the series is therefore analytic in the region $abs(z)>R$. We can combine this series with a normal power series to get:
$
  sum_(n=-oo)^oo a_n z^n
$
which converges when the parts consisting of negative and positive powers are seperately convergent. Given the first part converges for $abs(z) < R_2$ and the second for $abs(z) > R_1$, then there is a common region if $R_1 < R_2$, and the series is analytic in the annulus $R_1 < abs(z) < R_2$.

Likewise we can show that any analytic $f(z)$ whose region of definition contains an annulus $R_1 < abs(z-a) < R_2$ can be written as:
$
  f(z) = sum_(n=-oo)^oo A_n (z-a)^n
$
to prove this we just have to show that $f = f_1 + f_2$, where $f_1$ is analytic for $abs(z-a) < R_2$ and $f_2$ is analytic for $abs(z-a) > R_1$ with a removable singularity at $oo$. Given this $f_1$ can be developed in nonnegative powers of $z-a$, and $f_2$ can be developed in nonnegative powers of $1\/(z-a)$. Define $f_1$ by
$
  f_1 (z) = 1/(2 pi i) integral_(abs(zeta-a)=r) (f(zeta) dd(zeta))/(zeta-z)
$
for $abs(z-a) < r < R_2$, and $f_2$ by
$
  f_2 (z) = - 1/(2 pi i) integral_(abs(zeta-a)=r) (f(zeta)dd(zeta))/(zeta-z)
$
for $R_1 < r < abs(z-a)$. The value of $r$ does not matter as long as the inequalities are fulfilled, since by Cauchy's theorem the value of the integral does not change. Given this $f_1$ and $f_2$ are uniquely defined and represent analytic functions in $abs(z-a) < R_2$ and $abs(z-a) > R_1$.

The Taylor development for $f_1$ is:
$
  f_1 (z) = sum_(n = 0)^oo A_n (z-a)^n
$
with
$
  A_n = 1/(2 pi i) integral_(abs(zeta-a)=r) (f(zeta) dd(zeta))/(zeta-a)^(n+1)
$
which comes from the integral representation of derivatives. To find the development for $f_2$ we do $zeta = a + 1\/zeta', z=a+1\/z'$. This carries $abs(zeta-a)=r arrow abs(zeta') = 1\/r$ with negative orientation, and we obtain:
$
  f_2 (a+1/z') = 1/(2pi i) integral_(abs(zeta')=1/r) z'/zeta' (f(a+1/zeta') dd(zeta'))/(zeta' - z')=sum_(n=1)^oo B_n z'^n
$
with
$
  B_n = 1/(2 pi i) integral_(abs(zeta')=1/r) (f(a+1/zeta') dd(zeta'))/(zeta'^(n+1)) = 1/(2pi i) integral_(abs(zeta-a)=r) f(zeta) (zeta-a)^(n-1) dd(zeta)
$
which shows that we can write:
$
  f(z) = sum_(n=-oo)^(+oo) A_n (z-a)^n
$
where the integral gives $A_n$, and notably this does not depend on $r$ if $R_1 < r < R_2$. If $R_1 = 0$, then $a$ is an isolated singularity and $A_(-1) = B_1$ is the residue at $a$, for then $f(z)-A_(-1) (z-a)^(-1)$ is the derivative of a single-valued function in $0 < abs(z-a) < R_2$. Note that this is also how we defined residues previously
$
  "Res"_(z=a) f(z) = 1/(2pi i) integral_C f(z) dd(z)
$
from the expansion it also follows that for a pole of order $m >= 1$ we have:
$
  a_(-1) = 1/(m-1!) lim_(z arrow a) dv(, z, m-1) [(z-a)^m f(z)]
$
which for a simple pole $m=1$ reduces to:
$
  a_(-1) = lim_(z arrow a) (z-a) f(z)
$

== Partial Fractions and Factorization
=== Partial fractions
Given a function $f(z)$ which is meromorphic in a region $Omega$ one thing we can do is write
$
  f(z) = sum_nu P_nu (1/(z - b_nu)) + g(z)
$
where $g(z)$ is analytic in $Omega$, and $b_nu$ are poles---and $P_nu$ corresponds to the Laurent development containing negative powers of $z-b_nu$. The problem with this is that the sum might might be infinite, and there is no way to guarantee convergence. So we need to modify our approach, which is done by the following theorem:
#thm[Mittag-Leffler][
  Let ${b_nu}$ be a sequence of complex numbers with $lim_(nu arrow oo) b_nu = oo$, and let $P_nu (zeta)$ be polynomials without a constant term. Then there are functions which are meromorphic in the whole plane with poles at the points $b_nu$ and the corresponding singular parts $P_nu (1\/(z-b_nu))$. Moreover, the most general meromorphic function of this kind can be written in the form
  $
    f(z) = sum_nu [P_nu (1/(z-b_nu)) - p_nu (z)] + g(z)
  $
  where $p_nu (z)$ are suitably chosen polynomials and $g(z)$ is analytic in the whole plane.
]
#proof[sketch][
  Assume $b_nu eq.not 0$ for all $nu$. The function $P_nu (1\/(z-b_nu))$ is analytic for $abs(z)<abs(b_nu)$ and can be expanded in a Taylor-series about the origin. We pick $p_nu (z)$ as a partial sum of this series, ending with the term of degree $n_nu$. We can now estimate $P_nu - p_nu$, taking the maximum of $abs(P_nu)$ for $abs(z) <= abs(b_nu)\/2 = R_nu$ be $M_nu$ we get
  $
    abs(P_nu (1\/(z-b_nu)) - p_nu (z)) <= 2 M_nu ((2 abs(z))/(abs(b_nu)))^(n_nu +1)
  $
  for all $abs(z) <= abs(b_nu) \/4 = R_nu \/2$. This estimate comes from:
  $
    P_nu - p_nu &= z^(n_nu + 1)/(2 pi i) integral_(abs(zeta)=b_nu/2) (P_nu (zeta) dd(zeta))/(zeta^(n_nu+1) (zeta-z)) \
    abs(P_nu - p_nu) &<= M_nu abs(z)^(n_nu + 1)/(2 pi) integral_(abs(zeta)=b_nu/2) dd(zeta)/(abs(zeta)^(n_nu +1) abs(zeta-z)) \
    &<= M_nu (abs(z)^(n_nu +1))/(2 pi) (2/abs(b_nu))^(n_nu + 1) integral_(abs(zeta)=b_nu/2) dd(zeta)/abs(zeta-z)
  $
  now $abs(zeta-z) >= abs(zeta) - abs(z) := delta > 0$ for $abs(z) < R_nu\/2$ we get $delta >= R_nu\/2$. So
  $
    abs(P_nu - p_nu) &<= M_nu (abs(z)^(n_nu +1))/(2 pi) (2 /abs(b_nu))^(n_nu +1) 2/R_nu 2 pi R_nu \
    & <= 2 M_nu ((2 abs(z))/abs(b_nu))^(n_nu +1)
  $
  importantly this means that we can force the series to converge if we take large enough $n_nu$. Since most generously
  $
    abs(P_nu - p_nu) <= M_nu 1/2^(n_nu)
  $
  so we can pick $n$ large enough such that $2^(n_nu) >= M_nu 2^nu$, meaning the series is majorized by $2^(- nu)$ for all large enough $nu$.

  Further the estimate holds uniformly in any closed disk $abs(z) <= R$, so the convergence is uniform provided we omit terms with $abs(b_nu) <= R$. By Weierstass' theorem the remaining series represents an analytic function in $abs(z) <= R$, and it follows that the full series is meromorphic in the whole plane with the singular parts $P_nu (1\/(z-b_nu))$.
]

#ex[
  Consider
  $
    pi^2/(sin^2 pi z)
  $
  this has double poles at $z = n$ for $n in ZZ$. The singular part at the origin is $1\/z^2$, and since $sin^2 pi(z-n) = sin^2 pi z$, then the singular part at $z = n$ is $1\/(z-n)^2$. The series
  $
    sum_(n = -oo)^oo 1/(z-n)^2
  $
  is convergent for $z eq.not n$, as can be seen by comparison with $sum_1^oo 1\/n^2$. It is uniformly convergent on any compact set after omitting terms which become infinite on the set, therefore we can write:
  $
    pi^2/(sin^2 pi z) = sum_(n=-oo)^oo 1/(z-n)^2 + g(z)
  $
  with $g(z)$ analytic everywhere. We want to show that $g(z)$ is identically zero.

  We start by noting that the RHS and the series are both periodic with period $1$, so $g(z)$ must have the same period. We also have
  $
    abs(sin pi z)^2 = cosh^2 pi y - cos^2 pi x
  $
  so $pi^2\/sin^2 pi z arrow.triple 0$ as $abs(y) arrow oo$---likewise the series shares this property. Then we must have $g(z) arrow.triple 0$ for $abs(y) arrow oo$. So $abs(g(z))$ is bounded in a period strip $0 <= x <= 1$, and from periodicity $abs(g(z))$ will be bounded everywhere. By Liouville's theorem $g(z)$ must be a constant, and since the limit is $0$ it must vanish. So we have:
  $
    pi^2/(sin^2 pi z) = sum_(n=-oo)^oo 1/(z-n)^2
  $
]

Consider integrating the $sin^2 pi z$ series, the LHS is the derivative of $- pi cot pi z$, and the terms on the right are derivatives of $-1\/(z-n)$. The series with $1\/(z-n)$ diverges, so we must subtract a partial sum of the Taylor series from every term with $n eq.not 0$. It turns out to be sufficient to just subtract the constant terms, since the series
$
  sum_(n eq.not 0) (1/(z-n) + 1/n) = sum_(eq.not z/(n (z-n)))
$
is comparable with $sum_1^oo 1\/n^2$ and therefore convergent. The convergence is uniform of every compact set, if we omit infinite terms, so termwise differentiation is allowed, and we obtain:
$
  pi cot pi z = 1/z + sum_(n eq.not 0) (1/(z-n) + 1/n)
$
we can also write:
$
  pi cot pi z = lim_(m arrow oo) sum_(n=-m)^m 1/(z-n) = 1/z + sum_(n=1)^oo (2 z)/(z^2 - n^2)
$
which comes from bracketing terms with $n$ and $-n$, here it is obvious that both are odd functions of $z$, and for this reason the integration constant which we should include vanishes.

We can do this procedure in reverse, consider
$
  lim_(m arrow oo) sum_(-m)^m ((-1)^n)/(z-n) = 1/z + sum_1^oo (-1)^n (2 z)/(z^2-n^2)
$
we can write
$
  sum_(-(2k+1))^(2k+1) ((-1)^n)/(z-n) = sum_(n=-k)^k 1/(z-2n) - sum_(n=-k-1)^k 1/(z-1-2n)
$
taking the limit we find
$
  lim_(m arrow oo) sum_(-m)^m ((-1)^n)/(z-n) &= pi/2 cot pi/2 z - pi/2 cot (pi(z-1))/2 \
  &= pi/(sin pi z)
$
so
$
  pi/(sin pi z) = lim_(m arrow oo) sum_(-m)^m (-1)^n/(z-n)
$
#ex[
  Consider:
  $
    pi cot pi z &= 1/z + sum_(n eq.not 0) (1/(z-n) + 1/n) = 1/z + sum_(n=1)^oo (1/(z-n) + 1/(z+n)) \
    &= 1/z + sum_(n=1)^oo (2 z)/(z^2-n^2) = 1/z - sum_(n=1)^oo (2 z)/(n^2 (1 - z^2/n^2)) \
    &= 1/z - sum_(n=1)^oo (2 z)/(n^2) 1/(1- z^2/n^2) = 1/z - sum_(n=1)^oo (2 z)/n^2 sum_(k=0)^oo (z/n)^(2k) \
    &= 1/z - 2 sum_(n=1)^oo sum_(k=0)^oo (z^(2k+1))/(n^(2(k+1))) = 1/z - 2 sum_(k=0)^oo z^(2k+1) sum_(n=1)^oo 1/n^(2(k+1)) \
    &= 1/z - 2 sum_(k=0)^oo zeta(2k+2) z^(2k+1)
  $
  we also have the Laurent expansion
  $
    pi cot pi z &= 1/z - sum_(n=1)^oo ((2pi)^(2n) B_(2n))/(2n)! z^(2n-1) \
    &= 1/z - sum_(n=0)^oo ((2pi)^(2(n+1)) B_(2(n+1)))/(2(n+1)!) z^(2n + 1)
  $
  matching terms then gives
  $
    2 zeta(2n+2) = ((2pi)^(2(n+1)) B_(2(n+1)))/(2(n+1)!)
  $
  letting $k = n+1$
  $
    2 zeta(2k) = ((2 pi)^(2 k) B_(2 k))/(2k!)
  $
  so
  $
    zeta(2 k) = 2^(2k-1) B_(2k)/(2 k!) pi^(2 k)
  $
  for example taking $k = 1$
  $
    zeta(2) = 2/2! B_2 pi^2 = pi^2/6
  $
  note that all Bernoulli numbers are taken as positive. So $B_4 = 1\/30 eq.not - 1\/30$, giving for $k=2$:
  $
    zeta(4) = 2^3/4! 1/30 pi^4 = 1/3 1/30 pi^4 = pi^4/90
  $
]

=== Infinite products
The infinite product
$
  product_(n=1)^oo p_n = p_1 p_2 dots p_n dots
$
is evaluated by taking the limit of partial products $P_n = p_1 p_2 dots p_n$. This is said to converge if the limit exists and is non-zero---since any single factor being zero would make the sequence converge, however this is in some cases too strict. Instead we say the infinite product converges if at most a finite number of the factors are ero, and if the partial products formed by the nonvanishing factors tend to a finite limit, which is nonzero.

In a convergent product the general factor $arrow 1$, which is clear by $p_n = P_n\/P_(n-1)$, excluding zeros. For this reason it is beneficial to write all infinite products in the form
$
  product_(n=1)^oo (1 + a_n)
$
such that $a_n arrow 0$ to ensure convergence. If every factor is nonzero, then is is natural to compare this product with
$
  sum_(n=1)^oo log (1 + a_n)
$
the $a_n$ are complex, so we need to agree on a branch of the logarithms, and we pick the principal branch in each term. Denoting the partial sums of the above series by $S_n$ we have $P_n = e^(S_n)$, and if $S_n arrow S$ then $P=e^S eq.not 0$. So the convergence of the sum is a sufficient condition for the product to converge.

To prove necessity, assume $P_n arrow P eq.not 0$. In general the infinite series with principal values, does not converge to the principal value of $log P$, what we want is to show that it converges to some value of $log P$. We denote the principal value of log by $"Log"$ and its imaginary part by $"Arg"$.

Since $P_n\/P arrow 1$ we have $"Log" (P_n\/P) arrow 0$ for $n arrow oo$. There is some integer $h_n$ such that $"Log" (P_n\/P) = S_n - "Log"P + h_n 2 pi i$. We obtain from this
$
  (h_(n+1)-h_n) 2 pi i & = "Log"(P_(n+1)\/P) - "Log"(P_n\/P) - "Log"(1+a_n) \
    (h_(n+1)-h_n) 2 pi & = "Arg"(P_(n+1)\/P) - "Arg"(P_n\/P) - "Arg"(1+a_n)
$
by definition $abs("Arg"(1+a_n)) <= pi$, and $"Arg"(P_(n+1)\/P) - "Arg"(P_n\/P) arrow 0$. The previous is then only valid if $h_(n+1)=h_n$, meaning that $h_n = h$, some fixed integer. It follows that
$
  "Log"(P_n\/P) = S_n - "Log"P+h 2 pi i => S_n arrow "Log"P - h 2 pi i
$

#thm[
  The infinite product $product_1^oo (1+ a_n)$ with $1+a_n eq.not 0$ converges simultaneously with the series $sum_1^oo log(1+a_n)$ whose terms represent the values of the principal branch of the logarithm.
]
#proof[
  see previous paragraph.
]

This is very nice, since we can determine the convergence of a product, by checking the convergence of a series. Further it can be seen that the series converges absolutely in tandem with the series $sum abs(a_n)$, this follows from
$
  lim_(z arrow 0) log(1+z)/z = 1
$
if either of these converge we have $a_n arrow 0$, and for any $epsilon > 0$ we have
$
                abs(log(1+a_n)/a_n - 1) & < epsilon \
  (1-epsilon)abs(a_n) < abs(log(1+a_n)) & < (1+epsilon) abs(a_n)
$
for big enough $n$. It follows that they are simultaneously absolutely convergent---basically the squeeze theorem. An infinite product is said to converge absolutely if the corresponding series converges absolutely.

#thm[
  A necessary and sufficient condition for the absolute convergence of the product $product_(1)^oo (1+a_n)$ is the convergence of the series $sum_1^oo abs(a_n)$.
]

A function which is analytic in the whole plane is entire. If $g(z)$ is entire, then $f(z) = e^(g(z))$ is entire and $eq.not 0$. Likewise if $f(z)$ is entire and $eq.not 0$, then we can show that $f(z)$ is of the form $e^(g(z))$. Consider $f'(z) \/f(z)$, which is entire, and is the derivative of an entire function $g(z)$. By computation $f(z) e^(- g(z))$ has derivative zero, so $f(z)$ is a constant multiple of $e^(g(z))$.

With this we can also find the most general entire function with a finite number of zeros. Assuming $f(z)$ has $m$ zeros at the origin, and other zeros denoted by $a_1, a_2, dots, a_N$. Then we can write
$
  f(z) = z^m e^(g(z)) product_1^N (1 - z/a_n)
$
where we just factor out every zero, leaving an entire, non-zero function $e^(g(z))$. For infinitely many zeros this generalizes to
$
  f(z) = z^m e^(g(z)) product_1^oo (1 - z/a_n)
$
which is valid if the infinite product converges uniformly on every compact set. This converges absolutely if and only if $sum_1^oo 1\/abs(a_n)$ is convergent. In this case the convergence is also uniform in every closed disk $abs(z)<= R$. Under this special condition we can obtain a product representation of the above form.

In the general case we need to introduce other factors. We consider an arbitrary sequence of complex numbers $a_n eq.not 0$ with $lim_(n arrow oo) a_n = oo$, and want to prove that polynomials $p_n (z)$ exist such that
$
  product_1^oo (1 - z/a_n) e^(p_n (z))
$
converges to an entire function. This converges along with the series having terms like
$
  r_n (z) = log(1-z/a_n) + p_n (z)
$
where the branch is chosen so the imaginary part of $r_n$ is in $(-pi, pi]$. For a given $R$ we consider terms with $abs(a_n) > R$. In the disk $abs(z) <= R$ we can develop the Taylor-series
$
  log(1-z/a_n) = - z/a_n - 1/2 (z/a_n)^2 - 1/3 (z/a_n)^3 - dots
$
we reverse the signs to define $p_n$ as the partial sum
$
  p_n (z) = z/a_n + 1/2 (z/a_n)^2 + dots + 1/m_n (z/a_n)^(m_n)
$
then $r_n$ becomes
$
  r_n (z) = -1/(m_n + 1) (z/a_n)^(m_n +1) - 1/(m_n + 2) (z/a_n)^(m_n+2) - dots
$
the following estimate follows
$
  abs(r_n) &<= 1/(m_n+1) (R/abs(a_n))^(m_n + 1) (1+R/abs(a_n) +(R/abs(a_n))^2 + dots) \
  &<= 1/(m_n+1) (R/abs(a_n))^(m_n+1) (1-R/abs(a_n))^(-1)
$
suppose now that
$
  sum_(n=1)^oo 1/(m_n+1) (R/abs(a_n))^(m_n+1)
$
converges, then by the estimate $r_n (z) arrow 0$, and therefore $r_n$ has an imaginary part between $-pi$ and $pi$ given that $n$ is large enough. Moreover the estimate shows that $sum r_n$ is absolutely and uniformly convergent for $abs(z) <= R$, therefore the product represents an analytic function in $abs(z) < R$.

Now we just need to show that the sum can be made convergent for all $R$. This is obvious since for $m_n = n$ it has a majorant geometric series with ratio $< 1$ for any $R$.

#thm[Weierstrass factorization theorem][
  There exists an entire function with arbitrarily prescribed zeros $a_n$ provided that, in the case of infinitely many zeros, $a_n arrow oo$. Every entire function with these and no other zeros can be written in the form
  $
    f(z) = z^m e^(g(z)) product_(n=1)^oo (1- z/a_n) e^(z/a_n + 1/2 (z/a_n)^2 + dots + 1/m_n (z/a_n)^(m_n))
  $
  with the product being taken over all $a_n eq.not 0$, the $m_n$ are certain integers, and $g(z)$ is an entire function.

  In this representation the product handles all zeros away from the origin (and ensures convergence), $z^m$ at the origin, and then $e^(g(z))$ gives the most general form.
]

#corollary[
  Every function which is meromorphic in the whole plane is the quotient of two entire functions.
]

If $F(z)$ is meromorphic in the plane, then we can find an entire $g(z)$ with the poles of $F(z)$ for zeros. Then $F(z) g(z) = f(z)$ is entire, and thus $F(z) = f(z) \/ g(z)$.

It would be nicer if we could choose all $m_n$ to be equal. What we have shown is that
$
  product_1^oo (1-z/a_n) e^(z/a_n + 1/2 (z/a_n)^2 + dots + 1/h (z/a_n)^h)
$
converges and represents an entire function provided that
$
  sum_(n=1)^oo (R/abs(a_n))^(h+1)/(h+1)
$
converges for all $R$---this happens if $sum 1\/abs(a_n)^(h+1) < oo$. Assume that $h$ is the smallest integer for which this series converges, then the product is the canonical product associated with the sequence ${a_n}$, and $h$ is the genus of the canonical product. Whenever possible we'll use the canonical product in the full representation of $f(z)$. If $g(z)$ reduces to a polynomial then $f(z)$ has finite genus, and the genus of $f(z)$ is by definition the degree of this polynomial or the genus of the canonical product, depending on which is larger.

#ex[
  An entire function of genus zero is of the form
  $
    C z^m product_1^oo (1-z/a_n)
  $
  with $sum 1\/abs(a_n) < oo$. The canonical representation of genus $1$ is either of the form
  $
    C z^m e^(alpha z) product_1^oo (1- z/a_n) e^(z/a_n)
  $
  with $sum 1\/abs(a_n)^2 < oo, sum 1\/abs(a_n) = oo$, or
  $
    C z^m e^(alpha z) product_1^oo (1- z/a_n)
  $
  with $sum 1\/abs(a_n) < oo$, $alpha eq.not 0$.
]

Consider $sin pi z$, which has zeros at $z = plus.minus n$, since $sum 1\/n$ diverges and $sum 1\/n^2$ converges, we must take $h = 1$ and obtain:
$
  sin pi z = z e^(g (z)) product_(n eq.not 0) (1 - z/n) e^(z/n)
$
to find $g(z)$ we take the logarithmic derivative on both sides
$
  pi cot pi z = 1/z + g'(z) + sum_(n eq.not 0) (1/(z-n) + 1/n)
$
by comparison with the known partial fraction expansion for $cot pi z$ we see that $g'(z) = 0$, so $g(z)$ is a constant. Further since $lim_(z arrow 0) sin pi z \/ z = pi$ we must have $e^(g(z)) = pi$, so we find
$
  sin pi z = pi z product_(n eq.not 0) (1 - z/n) e^(z/n) = pi z product_1^oo (1 - z^2/n^2)
$
where the last equality follows by bracketing factors corresponding to $-n$ and $n$ together. It follows that $sin pi z$ is an entire function of genus $1$.

$sin pi z$ is the simplest function which has all integer zeros, now we introduce functions with only positive or negative integer zeros. Take example the negative integer zeros, this corresponds to the canonical product
$
  G(z) = product_1^oo (1 + z/n) e^(- z/n)
$
then $G(-z)$ has positive integer zeros, and by comparison we can find
$
  z G(z) G(-z) = (sin pi z)/pi
$
note that $G(z-1)$ has the same zeros as $G(z)$, and additionally a zero at the origin. So we can write
$
  G(z-1) = z e^(gamma(z)) G(z)
$
with $gamma(z)$ being an entire function. Taking the logarithmic derivative gives
$
  sum_(n=1)^oo (1/(z-1+n) - 1/n) = 1/z + gamma'(z) + sum_(n=1)^oo (1/(z+n)-1/n)
$
the LHS can be rewritten
$
  sum_(n=1)^oo (1/(z-1+n) - 1/n) &= 1/z - 1 + sum_(n=1)^oo (1/(z+n) - 1/(n+1)) \
  &= 1/z - 1 + sum_(n=1)^oo (1/(z+n) - 1/n) + sum_(n=1)^oo (1/n - 1/(n+1)) \
  &= 1/z + sum_(n=1)^oo (1/(z+n) - 1/n)
$
so $gamma'(z) = 0$, so $gamma$ is a constant. So $G(z)$ has the property $G(z-1) = e^gamma z G(z)$ or defining $H(z) = G(z) e^(gamma z)$ we find $H(z-1) = z H(z)$. Taking $z = 1$ we can determine $gamma$,
$
  1 = G(0) = e^gamma G(1) => e^(- gamma) = product_(n=1)^oo (1 + 1/n) e^(-1/n)
$
from this
$
  ((n+1)/n) arrow (2/1)(3/2)(4/3) dots (n/(n-1)) ((n+1)/n)
$
so the partial product can be written as
$
  (n+1) e^(-(1+1/2+1/3+dots+1/n))
$
giving
$
  gamma = lim_(n arrow oo) (1 + 1/2 + 1/3 + dots + 1/n - log n)
$
this is the Euler-Mascheroni constant. If $H(z-1)=z H(z)$ then we can define $Gamma(z) = 1\/(z H(z))$ which satisfies $ Gamma(z+1)=z Gamma(z) $
this turns out to be more useful and $Gamma(z)$ is Euler's gamma function, and is commonly treated as an elementary function because of its importance.

From our definition we get the explicit representation:
$
  Gamma(z) = (e^(-gamma z))/z product_(n=1)^oo (1 + z/n)^(-1) e^(z/n)
$
and
$
  Gamma(z) Gamma(1-z) = pi/(sin pi z)
$
we see that $Gamma(z)$ is meromorphic with poles at $z=0,-1,-2,dots$ but no zeros. Further $Gamma(1) = 1$ giving all other integer values by the recursive relation, which generally gives $Gamma(n) = (n-1)!$. We can also consider the logarithmic derivative
$
  dv(, z) ((Gamma'(z))/Gamma(z)) = sum_(n=0)^oo 1/(z+n)^2
$
using this with $Gamma(z) Gamma(z+1/2)$ and $Gamma(2 z)$ one can find the duplication formula due to Legendre
$
  sqrt(pi) Gamma(2 z) = 2^(2 z -1) Gamma(z) Gamma(z + 1/2)
$
this follows from the fact that the $Gamma(z) Gamma(z+1/2)$ and $Gamma(2 z)$ share poles, so we have
$
  Gamma(z) Gamma(z + 1/2) = e^(a z + b) Gamma(2 z)
$
which upon using known values gives the duplication formula.

=== Stirling's formula
Stirling's formula is essentially an asymptotic development for $Gamma(z)$ which is of great use for large values of $z$. We follow Ahlfors' derivation, which follows Lindelöf's derivation using residue calculus. Our starting point is
$
  dv(, z) (Gamma'(z))/Gamma(z) = sum_(n=0)^oo 1/(z+n)^2
$
we want to describe partial sums of the RHS by a nice line integral. We need a function with residues $1\/(z+v)^2$ at integer points $v$, one choice is
$
  phi(zeta) = (pi cot pi zeta)/(z+zeta)^2
$
we'll fix $z = x + i y$ with $x > 0$.

We apply the residue formula to the rectangle whose vertical sides lie on $xi = 0$ and $xi = n +1/2$ and with horizontal sides $eta = plus.minus Y$. First we'll let $Y arrow oo$ and then $n arrow oo$. We denote this contour by $K$, and it passes through the pole at $0$, so we need to take the pr.v. of the integral and include half the residue at the origin. We then get
$
  "pr.v." 1/(2pi i) integral_K phi(zeta) dd(zeta) = - 1/(2 z^2) + sum_(v=0)^n 1/(z+v)^2
$
on the horizontal sides of our rectangle $cot pi zeta$ tends uniformly to $plus.minus i$ for $Y arrow oo$. The factor $1\/(z+zeta)^2$ tends to zero, so the corresponding integrals also have limit zero. So now we just have two integrals over infinite vertical lines. On each line $xi = n +1/2$, $cot pi zeta$ is bounded, and due to periodicity this is independent of $n$. The integral over $xi = n + 1/2$ is then less than a constant times
$
  integral_(xi = n +1/2) dd(zeta)/(abs(zeta+z)^2)
$
on the line we have $overline(zeta) = 2 n + 1 - zeta$ so
$
  1/i integral dd(zeta)/abs(zeta+z)^2 = 1/i integral dd(zeta)/((zeta+z)(2n + 1 - zeta + overline(z))) = (2 pi)/(2 n +1 + 2x)
$
by considering the residues of
$
  f(zeta) = 1/((zeta+z)(2n+1-zeta + overline(z)))
$
this has poles at $zeta = -z$ and $zeta = 2 n + 1 + overline(z)$, the second is obviously outside the contour since $x > 0$. So the residue is
$
  lim_(zeta arrow - z) (zeta + z) f(zeta) = 1/(2 n +1 + z + overline(z))
$
giving the result. In the limit $n arrow oo$ the integral is therefore zero. The principal value of the integral over the imaginary axis $-i oo arrow +i oo$ can be written as
$
  1/2 integral_0^oo cot pi i eta [1/(i eta + z)^2 - 1/(i eta -z)^2] dd(eta) = - integral_0^oo coth pi eta (2 eta z)/(eta^2 + z^2)^2 dd(eta)
$
this comes from $zeta = i eta$, splitting the integral, and dividing by $2 pi i$. We end up having
$
  dv(, z) (Gamma'(z))/Gamma(z) = 1/(2 z^2) + integral_0^oo coth pi eta (2 eta z)/(eta^2 + z^2)^2 dd(eta)
$
writing
$
  coth pi eta = 1 + 2/(e^(2 pi eta)-1)
$
the first integral becomes $1/z$---just by u-sub. So
$
  dv(, z) (Gamma' (z))/Gamma(z) = 1/z + 1/(2 z^2) + integral_0^oo (4 eta z)/(eta^2 +z^2)^2 dd(eta)/(e^(2 pi eta)-1)
$
this integral is clearly strongly convergent. For $z$ restricted to the right half plane this can be integrated to give
$
  (Gamma'(z))/Gamma(z) = C + log z - 1/(2 z) - integral_0^oo (2 eta)/(eta^2 +z^2) dd(eta)/(e^(2 pi eta)-1)
$
to justify this we need to be able to differentiate the last term under the integral sign, this is allowed since the previous integral converges uniformly. We wish to integrate this expression again. This would however introduce $atan z/eta$ which is not preferable, since we like to avoid multi-valued functions. To proceed we instead first do partial integration
$
  integral_0^oo (2 eta)/(eta^2 + z^2) dd(eta)/(e^(2 pi eta)-1) = 1/pi integral_0^oo (z^2-eta^2)/(eta^2+z^2)^2 log(1 - e^(-2 pi eta)) dd(eta)
$
where we have $dd(v) = (2 eta)/(eta^2 + z^2) dd(eta)$ and $u = log (1 - e^(-2 pi eta))$. Now we can integrate
$
  log Gamma(z) = C' + C z + (z - 1/2) log z + 1/pi integral_0^oo z/(eta^2 +z^2) log 1/(1 - e^(- 2 pi eta)) dd(eta)
$
to determine $C$ and $C'$ consider the integral
$
  J(z) = 1/pi integral_0^oo z/(eta^2 +z^2) log 1/(1-e^(-2 pi eta)) dd(eta)
$
clearly $J(z) arrow 0$ as $z arrow oo$, given that $z$ stays away from the imaginary axis---let's suppose that $z$ is restricted to $x >= c > 0$. We can write
$
  J(z) = integral_0^(abs(z)/2) + integral_(abs(z)/2)^oo = J_1 + J_2
$
in the first integral $abs(eta^2+z^2) >= abs(z)^2 - abs(z\/2)^2 = 3 abs(z)^2 \/4$ (reverse $triangle$-inequality) so
$
  abs(J_1) <= 4/(3 pi abs(z)) integral_0^oo log 1/(1 - e^(-2 pi eta)) dd(eta)
$
in the second integral $abs(eta^2 + z^2) = abs(z-i eta) dot abs(z+i eta) > c abs(z)$ so
$
  abs(J_2) < 1/(pi c) integral_(abs(z)/2)^oo log 1/(1-e^(-2 pi eta)) dd(eta)
$
since $log (1 - e^(- 2 pi eta))$ is convergent both tend to $0$ as $z arrow oo$.

Using $log Gamma(z+1) = log z + log Gamma(z)$ we find
$
  C = - (z + 1/2) log(1 + 1/z) + J(z) - J(z+1)
$
as $z arrow oo$ we find $C=-1$. To find $C'$ we use $Gamma(z) Gamma(1-z) = pi\/ sin pi z$ with $z = 1/2 + i y$. As $y arrow oo$ both $J(1/2 + i y)$ and $J(1/2 - i y) arrow 0$. We can Taylor expand
$
  i y log (1/2 + i y)/(1/2 - i y) = i y ( pi i + log (1 + 1/(2 i y))/(1 - 1/(2i y)) ) = - pi y + 1 + epsilon_1 (y)
$
and
$
  log cosh pi y = pi y - log 2 + epsilon_2 (y)
$
with $epsilon_1$ and $epsilon_2$ both tending to $0$. This gives
$
  C' = 1/2 log 2 pi
$
we have just proved
$
  log Gamma(z) = 1/2 log 2 pi - z + (z - 1/2) log z + J(z)
$
or
$
  Gamma(z) = sqrt(2 pi) z^(z -1/2) e^(-z) e^(J(z))
$
we know that $J(z) arrow 0$ as $z arrow oo$ in a half plane $x >= c > 0$.

We can further develop $J(z)$ in powers of $1\/z$
$
  J(z) = C_1/z + C_2/z^3 + dots + C_k/z^(2k-1) + J_k (z)
$
with
$
  C_v = (-1)^(v-1) 1/pi integral_0^oo eta^(2 v - 2) log 1/(1-e^(2 pi eta)) dd(eta)
$
and
$
  J_k (z) = (-1)^k/(z^(2k+1)) 1/pi integral_0^oo eta^(2k)/(1+(eta/z)^2) log 1/(1-e^(-2 pi eta)) dd(eta)
$
one can prove that
$
  C_v = (-1)^(v-1) 1/((2v-1)2v) B_v
$

Lastly Stirling's formula can be used to prove
$
  Gamma(z) = integral_0^oo e^(-t) t^(z-1) dd(t) = F(z)
$
integration by parts immediately gives
$
  F(z+1) = z F(z)
$
so we have
$
  (F(z))/Gamma(z) = (F(z+1))/(Gamma(z+1))
$
so $F\/Gamma$ is periodic with the period $1$. We want to prove that this is constant, we want to estimate $abs(F\/Gamma)$ is a period strip, e.g. $1 <= x <= 2$. We have
$
  abs(F(z)) <= integral_0^oo e^(-t) t^(x-1) dd(t) = F(x)
$
so $F(z)$ is bounded. From Stirling's formula
$
  log abs(Gamma(z)) = 1/2 log 2 pi - x + (x-1/2) log abs(z) - y arg z + Re J(z)
$
the term $- y arg z$ becomes negatively infinite, being comparable to $- pi abs(y)\/2$. So $abs(F\/Gamma)$ does not grow much more rapidly than $e^(pi abs(y)\/2)$. This is enough to conclude that the ratio is a constant. And the fact that $F(1)=Gamma(1)=1$ shows that $F(z) = Gamma(z)$---see Ahlfors pg. 206.
