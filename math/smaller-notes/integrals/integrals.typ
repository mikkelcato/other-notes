#import "@preview/physica:0.9.5": *
#import "temp.typ": *


#show: thmrules.with(qed-symbol: $square$)
#show: note.with(
  title: [
    *some integrals and identities*
  ],
  authors: (
    (
      name: "mikkelius_",
    ),
  ),
  abstract: [
    some nice integrals and similar identities involving $e$, $pi$, $gamma$ and $G$.
  ],
)

= $Gamma(z)$ and Friends
Along with $e$ and $pi$, we are interested in the Euler-Mascheroni constant $gamma$ and Catalan's constant $G$---these can be defined as
$
  gamma & = lim_(n arrow oo) (sum_(k=1)^n 1/k - ln n) \
      G & = beta(2)= sum_(n=0)^oo (-1)^n /(2 n + 1)^2
$
with $beta$ being the Dirichlet beta function:
$
  beta(s) = sum_(n=0)^oo (-1)^n /(2 n +1)^s
$
these are of great importance since they turn up everywhere, with many, many different integrals or series equaling them.

Next we'll quickly define the $Gamma$ function and the digamma function $psi$:
$
  Gamma(z) = integral_0^oo x^(z-1) e^(-x) dd(x)
$
this has a nice recursive property that can be proven with integration by parts:
$
  Gamma(z+1) = z Gamma(z) => Gamma(z) = (z-1)!
$
To make our lives a bit easier we define the $Beta$ function:
$
  Beta(z_1, z_2) = integral_0^1 x^(z_1-1) (1-x)^(z_2 - 1) dd(x)
$
which is related to the $Gamma$ function by:
$
  Beta(z_1, z_2) = (Gamma(z_1)Gamma(z_2))/(Gamma(z_1 + z_2))
$
#proof[
  $
    Gamma(z_1)Gamma(z_2) = integral_0^oo integral_0^oo x^(z_1-1)y^(z_2-1) e^(-(x+y)) dd(y, x)
  $
  now let $x = u v$ and $y = u(1-v)$:
  $
    Gamma(z_1) Gamma(z_2) &= integral_0^1 integral_0^oo u^(z_1+z_2-1) v^(z_1-1) (1-v)^(z_2-1) e^(- u) dd(u, v) \
    &= integral_0^1 v^(z_1-1) (1-v)^(z_2-1) dd(v) integral_0^oo u^(z_1+z_2-1) e^(-u) dd(u) \
    &= Beta(z_1, z_2) Gamma(z_1+z_2)
  $
]
We'll also need a more useful form of the $Beta$ function:
$
  B(z_1,z_2) = 2 integral_0^(pi/2) (sin theta)^(2 z_1 - 1) (cos theta)^(2 z_2 - 1) dd(theta)
$
#proof[
  We use the substitution $x = sin^2 theta => dd(x) = 2 sin theta cos theta dd(theta)$:
  $
    Beta(z_1, z_2) &= integral_0^1 x^(z_1-1) (1-x)^(z_2 -1) dd(x) \
    &= 2 integral_0^(pi/2) (sin theta)^(2 z_1 - 2) (cos theta)^(2 z_2 - 2) sin theta cos theta dd(theta) \
    &= 2 integral_0^(pi/2) (sin theta)^(2 z_1 - 1) (cos theta)^(2 z_2 - 1) dd(theta)
  $
]
Returning to the $Gamma$ function we have the reflection formula, due to Euler:
$
  Gamma(z)Gamma(1-z) = pi/(sin pi z)
$
#proof[
  We find $Beta(z, 1-z)$:
  $
    Gamma(z) Gamma(z-1) & = Beta(z, 1-z) \
                        & = integral_0^1 x^(z-1) (1-x)^(-z) dd(x) \
                        & = integral_0^oo (t/(t+1))^(z-1) (t+1)^(z) dd(t)/(t+1)^2 \
                        & = integral_0^oo t^(z-1)/(t+1) dd(t) \
                        & = pi/(sin pi z)
  $
  we used the substitution $x = t/(t+1) => dd(x) = dd(t)/(t+1)^2$. The last identity used can be proved using residue calculus---another approach entirely is to use the Euler product for the $Gamma$ function and then use:
  $
    z product_(n=1)^oo (1 - z^2/n^2) = (sin pi z)/pi
  $
]
this gives values like:
$
  Gamma(1/2) = sqrt(pi)
$
which turns out to be the Gaussian integral. Lastly we have the duplication formula, due to Legendre:
$
  Gamma(z) Gamma(z + 1/2) = 2^(1-2 z) sqrt(pi) Gamma(2 z)
$
#proof[
  We let $z_1=z_2=z$ in the $Beta$ function:
  $
    Beta(z, z) & = (Gamma^2 (z))/(Gamma(2 z)) \
               & = integral_0^1 x^(z-1) (1-x)^(z-1) dd(x) \
               & = 1/2^(2z-1) integral_(-1)^1 (1-u^2)^(z-1) dd(u)
  $
  with $t = (1+u)/2$, the integrand is even so:
  $
    2^(2z-1) Gamma^2 (z) & = 2 Gamma(2 z) integral_0^1 (1- u^2)^(z-1) dd(u)
  $
  now consider $Beta(1/2, z)$, with $x = u^2$:
  $
    Beta(1/2, z) & = integral_0^1 x^(1/2-1) (1-x)^(z-1) dd(x) \
                 & = 2 integral_0^1 (1 - u^2)^(z-1) dd(u) \
                 & = (sqrt(pi) Gamma(z))/(Gamma(z+1/2))
  $
  so finally:
  $
    Gamma(z) Gamma(z+1/2) = 2^(1-2z) sqrt(pi) Gamma(2 z)
  $
]
these enable us to quickly solve many integrals, since many integrals can be written as a $Gamma$ function or $Beta$ function.

We can write the $Gamma$ function as, due to Euler:
$
  Gamma(z) = 1/z product_(n=1)^oo (1 + 1/n)^z /(1 + z/n)
$
#proof[
  Consider the limit:
  $
    lim_(n arrow oo) (n! (n+1)^z)/(n+z)! = 1
  $
  with $Gamma(z) = (z-1)! = z!\/z$ we can find:
  $
    Gamma(z) &= lim_(n arrow oo) (n! (n+1)^z z!\/z)/(n+z)! \
    &= 1/z lim_(n arrow oo) n! (n+1)^z z!/(n+z)! \
    &= 1/z lim_(n arrow oo) (1 dot 2 dots dot n) 1/((1+z)dots (n+z)) (2/1 dot 3/2 dots n/(n-1) dot (n+1)/n)^z
  $
  thus each factor is of the form:
  $
    n/(n+z) ((n+1)/n)^z => Gamma(z) = 1/z product_(n=1)^oo (1 + 1/n)^z/(1+z/n)
  $
]
a often more useful form is due to Weierstrass, which also introduces $gamma$:
$
  Gamma(z) = e^(- gamma z)/z product_(n=1)^oo (1 + z/n)^(-1) e^(z/n)
$
#proof[
  We prove that this is equivalent to the limit used to derive the Euler product:
  $
    Gamma(z) &= e^(- gamma z)/z product_(n=1)^oo (1 + z/n)^(-1) e^(z/n) \
    &= 1/z lim_(n arrow oo) e^(z (log(n+1) -1-1/2 dots - 1/n)) e^(z(1+1/2+dots + 1/n))/((1+z)(1+z/2)dots (1+z/n)) \
    &= 1/z lim_(n arrow oo) e^(z log (n+1))/((1+z)(1+z/2)dots (1+z/n)) \
    &= lim_(n arrow oo) (n! (n+1)^z)/(z (z+1)dots(z+n))
  $
]
These are the two most useful product representations of the $Gamma$ function. The digamma function $psi$ is defined as the logarithmic derivative of $Gamma$:
$
  psi(z) = dv(, z) ln Gamma(z) = (Gamma' (z) )/(Gamma (z) )
$
using the $Gamma$ integral we can write:
$
  psi(z) & = 1/Gamma(z) dv(, z) integral_0^oo x^(z-1) e^(-x) dd(x) \
         & = 1/Gamma(z) integral_0^oo x^(z-1) ln x e^(-x) dd(x) \
$
consider:
$
  psi(1) & = integral_0^oo ln x e^(-x) dd(x) \
$
We can get a nice series representation for $psi(z)$ using the Weierstrass form of $Gamma(z)$:
$
  psi(z) & = dv(, z) ln Gamma(z) \
         & = dv(, z) ln ( e^(- gamma z)/z product_(n=1)^oo (1+z/n)^(-1) e^(z/n) ) \
         & = dv(, z) { - gamma z - ln z + sum_(n=1)^oo [ z/n - ln (1 + z/n) ] } \
         & = - gamma - 1/z + sum_(n=1)^oo {1/n - 1/(n+z)} \
         & = - gamma + sum_(n=0)^oo {1/(n+1) - 1/(n+z)}
$
by comparing terms these  are equivalent. Now we can try to determine some nice values:
$
  psi(1) = Gamma'(1) = - gamma
$
so by the integral we have:
$
  integral_0^oo ln x e^(-x) dd(x) = - gamma
$
we can also differentiate easily now:
$
  psi'(z) = sum_(n=0)^oo 1/(n+z)^2
$
which gives us the really nice result:
$
  psi'(1) = sum_(n=0)^oo 1/(n+1)^2 = sum_(n=1)^oo 1/n^2 = pi^2/6
$
this is just the Basel problem! Another nice result is $Gamma''(1)$:
$
     Gamma''(z) & = dv(, z) Gamma(z) psi(z) \
                & = Gamma'(z) psi(z) + psi'(z) Gamma(z) \
                & = psi^2 (z) Gamma(z) + psi'(z) Gamma(z) \
  => Gamma''(1) & = psi^2 (1) + psi'(1) \
                & = gamma^2 + pi^2/6
$
now consider:
$
  dv(, z, 2) Gamma(z) = integral_0^oo x^(z-1) ln^2 x e^(-x) dd(x)
$
giving:
$
  integral_0^oo ln^2 x e^(-x) dd(x) = gamma^2 + pi^2/6
$ <gammadotdot>
which nicely relates $e$, $pi$ and $gamma$!

We'll make a short detour to prove the Bose integral:
$
  integral_0^oo (x^(s-1) dd(x))/(e^x - 1) = zeta(s) Gamma(s)
$
with the Riemann-$zeta$ function:
$
  zeta(s) = sum_(n=1)^oo 1/n^s
$
#proof[
  $
    integral_0^oo (x^(s-1) dd(x))/(e^x - 1) &= integral_0^oo x^(s-1) e^(-x) 1/(1 - e^(-x)) dd(x) \
    &= integral_0^oo x^(s-1) e^(-x) sum_(k=0)^oo (e^(-x))^k dd(x) \
    &= sum_(k=0)^oo integral_0^oo x^(s-1) e^(-(k+1)x) dd(x) \
    &= sum_(k=0)^oo 1/(k+1)^s integral_0^oo u^(s-1) e^(-u) dd(u) \
    &= sum_(k=1)^oo 1/k^s integral_0^oo u^(s-1) e^(-u) dd(u) \
    &= zeta(s) Gamma(s)
  $
]
We can make a quick generalization:
$
  integral_0^oo (x^(s-1) dd(x))/(e^x\/z - 1) &= integral_0^oo x^(s-1) z e^(-x) 1/(1 - e^(-x) z) dd(x) \
  &= integral_0^oo x^(s-1) z e^(-x) sum_(k=0)^oo (e^(-x)z)^k dd(x) \
  &= sum_(k=0)^oo integral_0^oo x^(s-1) z^(k+1) e^(- (k+1)x) dd(x) \
  &= sum_(k=0)^oo (z^(k+1))/(k+1)^s integral_0^oo u^(s-1)e^(-u) dd(u) \
  &= sum_(k=1)^oo z^k/k^s integral_0^oo u^(s-1) e^(-u) dd(u) \
  &= "Li"_s (z) Gamma(s)
$
with the polylogarithm defined as:
$
  "Li"_s (z) = sum_(k=1)^oo z^k/k^s
$
note that $"Li"_s (1) = zeta(s)$---besides this really interesting and quite easy integral the polylogarithm has some other nice properties, e.g:
$
  "Li"_(s+1) (z) = integral_0^z ("Li"_s (t))/t dd(t)
$
which gives the function its name.
#proof[
  $
    ("Li"_s (t) )/ t = sum_(k=1)^oo t^(k-1) / k^s
  $
  integrating gives:
  $
    integral_0^z sum_(k=1)^oo t^(k-1) /k^s dd(t) & = sum_(k=1)^oo z^k /(k^(s+1)) \
                                                 & = "Li"_(s+1) (z)
  $
]
And from the definition we have $"Li"_1 (z) = - ln(1-z)$, thus we can get every other $s$ using the recursive nature. We also have relations like:
$
  "Li"_s (-z) + "Li"_s (z) = 2^(1-s) "Li"_s (z^2)
$
#proof[
  $
    "Li"_s (-z) + "Li"_s (z) &= sum_(k=1)^oo (-1)^k z^k / k^s + sum_(k=1)^oo z^k /k^s \
    &= 2 sum_(k=1)^oo z^(2k)/((2k)^s) \
    &= 2^(1-s) sum_(k=1)^oo (z^2)^k / k^s \
    &= 2^(1-s) "Li"_s (z^2)
  $
  since we get all the even terms twice, with the odd terms cancelling.
]

Before moving on to Catalan's constant, we'll prove the functional equation for $zeta(s)$---since it's pretty cool:
$
  zeta(s) = 2^s pi^(s-1) sin((pi s)/2) Gamma(1-s) zeta(1-s)
$
#proof[
  By the definition of $Gamma$ we find:
  $
    integral_0^oo x^(s/2 - 1) e^(- n^2 pi x) dd(x) = (Gamma(s/2))/(n^s pi^(s/2))
  $
  so for $s > 1$:
  $
    (Gamma(s/2) zeta(s))/pi^(s/2) = integral_0^oo x^(s/2-1) sum_(n=1)^oo e^(-n^2 pi x) dd(x)
  $
  define:
  $
    psi (x) = sum_(n=1)^oo e^(- n^2 pi x)
  $
  since $cal(f) (psi(x)) = 1/sqrt(x) e^(-(n^2 pi)/x)$ we have by Poisson's summation formula:
  $
    sum_(n=-oo)^(n=oo) e^(-n^2 pi x) = 1/sqrt(x) sum_(n=-oo)^(n=oo) e^(- (n^2 pi)/x)
  $
  or:
  $
    2 psi(x) +1 = 1/sqrt(x) (2 psi(1/x) +1)
  $
  the integral can be written as:
  $
    pi^(- s/2) Gamma(s/2) zeta(s) &= integral_0^1 x^(s/2-1) psi(x) dd(x) + integral_1^oo x^(s/2-1) psi(x) dd(x) \
    &= integral_0^1 x^(s/2-1) (1/sqrt(x) psi(1/x) + 1/(2 sqrt(x)) -1/2) dd(x) + integral_1^oo x^(s/2-1) psi(x) dd(x) \
    &= 1/(s-1) -1/s +integral_0^1 x^(s/2-3/2) psi(1/x) dd(x) + integral_1^oo x^(s/2-1) psi(x) dd(x) \
    &= 1/(s(s-1)) + integral_1^oo (x^(-s/2 -1/2) + x^(s/2-1)) psi(x) dd(x)
  $
  letting $s arrow 1-s$ the RHS is unchanged, so:
  $
    (Gamma(s/2) zeta(s))/(pi^(s/2)) = (Gamma(1/2-s/2) zeta(1-s))/(pi^(1/2-s/2))
  $
  this is the original by Riemann. But we can do better:
  $
    Gamma(s/2) zeta(s) &= Gamma(1/2-s/2) zeta(1-s) pi^(s-1/2) \
    Gamma(1-s/2)Gamma(s/2)zeta(s) &= Gamma(1-s/2)Gamma(1/2-s/2)zeta(1-s)pi^(s-1/2) \
    zeta(s) &= sin((pi s)/2) Gamma(1-s/2) Gamma(1/2-s/2) zeta(1-s) pi^(s-3/2)
  $
  where we've used the reflection formula. Using the duplication formula with $z = 1/2-s/2$ gives:
  $
    zeta(s) & = sin((pi s)/2) 2^(1-1+s) sqrt(pi) Gamma(1-s) zeta(1-s) pi^(s-3/2) \
    zeta(s) & = sin((pi s)/2) 2^s Gamma(1-s) zeta(1-s) pi^(s-1)
  $
]

#pagebreak()
= Catalan's Constant $G$
As mentioned we define Catalan's constant as
$
  G = beta(2) = sum_(n=0)^oo (-1)^n/(2n+1)^2
$
as with a lot of these guys we have a million different representations, one of the nicest is
$
  G = integral_0^1 atan(x)/x dd(x)
$
#proof[
  We just Taylor expand arctan:
  $
    atan(x) = sum_(n=0)^oo (-1)^n/(2n+1) x^(2n+1)
  $
  and then plug and chug:
  $
    integral_0^1 sum_(n=0)^oo (-1)^n/(2 n +1) x^(2 n) dd(x) &= sum_(n=0)^oo (-1)^n/(2 n +1) [x^(2n+1)/(2n + 1)]_0^1 \
    &= sum_(n=0)^oo (-1)^n/(2n+1)^2 \
    &= G
  $
]
now we can get many more, e.g. by using:
$
  atan u - atan v = atan((u-v)/(1+u v))
$
with $u = 1, v = x$ this can give
$
  G = 2 integral_0^1 (pi/4 - atan(x)) dd(x)/(1-x^2)
$

#proof[
  we have
  $
    2 integral_0^1 (pi/4 - atan(x)) dd(x)/(1-x^2) &= 2 integral_0^1 atan((1-x)/(1+x)) dd(x)/(1-x^2)
  $
  letting $ u = (1-x)/(1+x) => dd(u) & = (-2)/(1+x)^2 dd(x) \
           x = (1-u)/(1+u) & => (1+x)^2 = 4/(1+u)^2 \
                           & => 1-x^2 = (4u)/(1+u)^2 $
  and $u(0) = 1$, $u(1) = 0$, so we get
  $
    2 integral_0^1 atan((1-x)/(1+x)) dd(x)/(1-x^2) &= -2 integral_1^0 atan(u) (dd(u))/(2) 4/(1+u)^2 (1+u)^2/(4 u) \
    &= integral_0^1 atan(u)/u dd(u) \
    &= G
  $
]
