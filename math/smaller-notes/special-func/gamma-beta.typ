#import "@preview/physica:0.9.5": *
#import "temp.typ": *


#show: thmrules.with(qed-symbol: $square$)
#show: note.with(
  title: [
    The $Gamma$ and $Beta$ functions.
  ],
  authors: (
    (
      name: "mikkelius_",
    ),
  ),
  abstract: [
    notes on the $Gamma$ and $Beta$ functions.
  ],
)

= $Gamma$ function

#def[$Gamma$ function][
  We define $ Gamma(z) = integral_0^oo t^(z-1) e^(-t) dd(t) $
  or if we're pedantic (explicit Haar measure) $ Gamma(z)=integral_0^oo t^z e^(-t) dd(t)/t $
]

#thm[Recursion formula][
  We have $ Gamma(z+1)=z Gamma(z) $ in particular for positive integers $ Gamma(n) = (n-1)! $
]
#proof[
  This is easily proven using integration by parts.
]

#lemma[Sine infinite product][
  We'll need $ sin(pi z) = pi z product_(k=1)^oo (1- z^2/k^2) $ in a bit
]
#proof[
  Consider $ sin (x) & =(e^(i x)- e^(-i x))/(2 i) \
          & = -i/(2) lim_(n arrow oo) [(1+(i x)/n)^n - (1- (i x)/n)^n] $
  now we apply $ (1 + (i x)/n)^n &= 1+n (i x)/n + (n(n-1))/2! ((i x)/n)^2 + dots = sum_(k=0)^n binom(n, k) ((i x)/n)^k \
  (1 - (i x)/n)^n &= 1 - n (i x)/n + (n(n-1))/2! ((i x)/n)^2 - dots = sum_(k=0)^n (-1)^k binom(n, k) ((i x)/n)^k $
  subbing these in all the real terms (even powers of $x$) die, and taking a common factor of $2 i x$ out of the remaining terms we get $ sin(x) = x lim_(n arrow oo) sum_(k=0)^((n-1)\/2) (-1)^k binom(n, 2k+1) x^(2k)/n^(2k+1) $ now we'll factor the polynomial into the trigonometric form. Note that the sum is a polynomial in $x^2$, any such polynomial can be factored as $ P_n (x^2) = product_(k=1)^((n-1)\/2) (1-x^2/r_k^2) $ with $r_k^2$ being the roots. We write $ (1+i x/n)^n = sum_(k=0)^n binom(n, k)(i x/n)^k = sum_(k=0)^n binom(n, k)i^k x^k/n^k $ taking the imaginary part $ Im((1+i x/n)^n) = sum_(k=0)^((n-1)\/2) binom(n, 2k+1)(-1)^k x^(2k+1)/n^(2k+1) $ so our polynomial becomes $ S_n =1/x Im((1+i x/n)^n) $ we want the roots $S_n = 0$, this means that $ n arg(1+i x/n)=m pi => n atan(x/n)=m pi $ so we get $ x = n tan((m pi)/n) $ now $S_n$ is naturally a polynomial in $x^2$ so we want the squared roots $ r_m^2 = n^2 tan^2 ((m pi)/n) $ giving our representation
  $
    sin(x)
    &= x lim_(n arrow oo) product_(k=1)^((n-1)\/2) (1-x^2/(n^2 tan^2 (k pi\/n))) \
    &= x lim_(n arrow oo) product_(k=1)^((n-1)\/2) [1-x^2/(k^2 pi^2) ((k pi\/n)/(tan(k pi\/n)))^2] \
    &= x product_(k=1)^oo (1-x^2/(k^2 pi^2))
  $
  or $ sin(pi z) = pi z product_(k=1)^oo (1- z^2/k^2) $
]


#thm[Euler's reflection formula][
  We have $ Gamma(z)Gamma(1-z) = pi/sin(pi z) $
]
#proof[
  We use $ e^(-t) = lim_(n arrow oo) (1- t/n)^n $ in $ Gamma(z)=lim_(n arrow oo) integral_0^n t^(z-1) (1-t/n)^n dd(t) $
  integrating by parts $ integral_0^n t^(z-1)(1-t/n)^n dd(t) = n/(n z) integral_0^n t^z (1-t/n)^(n-1) dd(t) $ doing this $n$ times $ Gamma(z) &= lim_(n arrow oo) n/(n z) (n-1)/(n(z+1)) (n-2)/(n(z+2)) dots 1/(n(z+n-1)) integral_0^n t^(z+n-1) dd(t) \
  &= lim_(n arrow oo) n!/(n^n product_(k=0)^(n-1) (z+k) ) n^(z+n)/(z+n) = lim_(n arrow oo) n^z/z product_(k=1)^n k/(z+k) $ where we've pulled the $k=0$ term out and $n!\/z+n$ acts as the $n$'th term. Now we apply this to $Gamma(1-z)$ $ Gamma(z) Gamma(1-z) &= Gamma(z) (-z) Gamma(-z) \ &= -z (lim_(n arrow oo) n^z/z product_(k=1)^n k/(z+k))(lim_(n arrow oo) n^(-z)/(-z) product_(k=1)^n k/(-z+k)) \
  &= lim_(n arrow oo) 1/z product_(k=1)^n k^2/(k^2-z^2) \
  &= 1/z product_(k=1)^oo k^2/(k^2-z^2) $
  note the infinite product expansion for sine $ sin(pi z) = pi z product_(k=1)^oo (1- z^2/k^2) = pi z product_(k=1)^oo (k^2-z^2)/k^2 $ this is the reciprocal of what we got before so $ Gamma(z)Gamma(1-z)=pi/(sin(pi z)) $
]

== $Beta$ function
#def[$Beta$ function][
  We have $ Beta(x, y)=integral_0^1 t^(x-1)(1-t)^(y-1) dd(t) $ it is obvious that $ Beta(x, y)=Beta(y, x) $
]

#thm[Connection between $Gamma$ and $Beta$][
  We have $ Beta(x, y) = (Gamma(x)Gamma(y))/Gamma(x+y) $
]

#proof[
  Take $ Gamma(x)Gamma(y) = integral_0^oo integral_0^oo u^(x-1)v^(y-1) e^(-u-v) dd(u, v) $ now we substitute $s = u+v$ as $v = s- u$, note that $v = s - u > 0$, so $u$ is less than $s$, thus $u in (0,s)$ for the bounds $ Gamma(x)Gamma(y) &= integral_0^oo integral_0^s u^(x-1)(s-u)^(y-1)e^(-s)dd(u, s) \
  &= integral_0^oo integral_0^s u^(x-1)(1-u/s)^(y-1) s^(y-1)e^(-s)dd(u, s) $ next we let $t = u/s arrow u=s t$ with $dd(u)=s dd(t)$ $ Gamma(x)Gamma(y) &= integral_0^oo integral_0^1 (s t)^(x-1) (1-t)^(y-1) s^(y-1)e^(-s) s dd(t, s) \
  &=integral_0^oo s^(x+y-1)e^(-s)dd(s) integral_0^1 t^(x-1)(1-t)^(y-1) dd(t) = Gamma(x+y) Beta(x, y) $
]

#thm[Trigonometric representation of $Beta$][
  We have $ Beta(x, y)=2 integral_0^(pi/2) (cos theta)^(2x-1)(sin theta)^(2y-1) dd(theta) $
]

#proof[
  Again take $ Gamma(x)Gamma(y) = integral_0^oo integral_0^oo u^(x-1)v^(y-1)e^(-u-v)dd(u, v) $ make the substitution $u=s^2$ and $v=t^2$ $ Gamma(x)Gamma(y) &= integral_0^oo integral_0^oo (s^2)^(x-1)(t^2)^(y-1)e^(-s^2-t^2)2s 2t dd(s, t) \
  &= 4 integral_0^oo integral_0^oo s^(2x-1) t^(2y-1) e^(-(s^2+t^2))dd(s, t) $ now we go to polar coordinates with $s = r cos theta$ and $t = r sin theta$ and $dd(s, t)=r dd(r, theta)$
  $
    Gamma(x)Gamma(y) &= 4 integral_0^(pi/2)integral_0^oo (r cos theta)^(2x-1) (r sin theta)^(2y-1) e^(-r^2)r dd(r, theta) \
    &= 4 integral_0^(pi/2) (cos theta)^(2x-1) (sin theta)^(2y-1) dd(theta) integral_0^oo r^(2x+2y-1) e^(-r^2) dd(r)
  $
  the $r$-integral can be evaluated to give $1/2 Gamma(x+y)$ $ integral_0^(pi/2) (cos theta)^(2x-1)(sin theta)^(2y-1) dd(theta) = (Gamma(x)Gamma(y))/(2Gamma(x+y))=1/2 Beta(x, y) $
]

#thm[Legendre's duplication formula][
  We have $ Gamma(z)Gamma(z+1/2)=2^(1-2z) sqrt(pi) Gamma(2 z) $
]
#proof[
  Letting $z_1=z_2=z$ we have $ Gamma(z)^2/Gamma(2 z) &= integral_0^1 u^(z-1)(1-u)^(z-1)dd(u) \
  &= 1/2 integral_(-1)^(1) ((1+x)/2)^(z-1) ((1-x)/2)^(z-1) dd(x) \
  &= 1/(2^(2z-1)) integral_(-1)^1 (1-x^2)^(z-1) dd(x) $
  so $ 2^(2z-1) Gamma(z)^2 = 2 Gamma(2 z) integral_0^1 (1-x^2)^(z-1)dd(x) $ now let $u=x^2$ in $Beta(z_1, z_2)$ $ Beta(z_1, z_2) = integral_0^1 x^(2z_1-2) (1-x^2)^(z_2-1) 2x dd(x) $ let $z_1=1/2$ and $z_2 = z$ giving $ B(1/2,z)=2 integral_0^1 (1-x^2)^(z-1) dd(x) $ combining results $ 2^(2z-1)Gamma(z)^2 = Gamma(2z) Beta(1/2, z) = Gamma(2z) (Gamma(1/2)Gamma(z))/Gamma(z+1/2) $ or with $Gamma(1/2)= sqrt(pi)$ we get $ Gamma(z)Gamma(z+1/2) = 2^(1-2z) sqrt(pi) Gamma(2z) $
]
