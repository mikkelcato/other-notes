//**** init-ting
#import "@preview/physica:0.9.5": *
#import "temp.typ": *


#show: thmrules.with(qed-symbol: $square$)
#show: note.with(
  title: [
    *the Mellin transform*
  ],
  authors: (
    (
      name: "mikkelius_",
    ),
  ),
  abstract: [
    notes on the Mellin transform --- based on https://hal.science/hal-03152634v1/file/MELLIN.pdf by J. Bertand et al.
  ],
)


//****

= The Transformation
== Definition
#def[Mellin transform][
  Let $f(t)$ be defined on $0 < t < oo$. $cal(M)$ is the Mellin transformation mapping $f arrow F$ defined on the complex plane by: $ cal(M) [f;s] equiv F(s) = integral_0^oo f(t) t^(s-1) dd(t) $ with $F(s)$ being the transform of $f$.
]

In general this integral exists for complex values $s = a + i b$ where $a_1 < a < a_2$ and $a_1, a_2$ depend on $f(t)$ $arrow.long$ strip of definition $S(a_1,a_2)$, this would be the whole plane if $a_1 = - oo "and" a_2 = + oo$.

#ex[
  Given $ f(t) = H(t-t_0) t^z $ then $ cal(M)[f;s] = - t_0^(z+s)/(z+s) $
]

#ex[
  Given $ f(t) = e^(- p t)"  " p > 0 $ then $ cal(M)[f;s]=p^(-s) Gamma(s) $ by definition of the gamma function.
]

#ex[
  Consider $ f(t) = (1+t)^(-1) $ we let $ t + 1 = 1/(1-x) arrow x = t/(t+1) -> dd(x)=dd(t)/(t+1)^2 $ then $ cal(M) [f;s] & = integral_0^1 (1-x) ((x)/(1-x))^(s-1) dd(x)/(1-x)^2  \
               & =integral_0^1 x^(s-1) (1-x)^(-s) dd(x) = Beta(s, 1-s) $
  so $ cal(M)[f;s] & = Beta(s, 1-s)      \
              & =Gamma(s)Gamma(1-s) \
              & = pi/(sin pi s) $
  from the Euler reflection formula.
]

== Related transforms
If we do change of variables by $ t = e^(-x) arrow dd(t) = -e^(-x) dd(x) $
then $ F(s) = integral_(-oo)^oo f(e^(-x))e^(-s x) dd(x) $ letting $g(x) equiv f(e^(-x))$ this is the two-sided Laplace transform $cal(L)$ of $g$, defined by:
$ cal(L)[g;s] = integral_(-oo)^oo g(x) e^(-s x) dd(x) $
or symbolically $ cal(M)[f(t);s] = cal(L)[f(e^(-x));s] $ to get the Fourier transform we let $s = a + 2 pi i beta$ giving:
$ F(s) = integral_(- oo)^oo f(e^(-x)) e^(- a x) e^(-2 pi i beta x) dd(x) $ or $ cal(M)[f(t);a+2pi i beta] = cal(F)[f(e^(-x))e^(-a x); beta] $ with $cal(F)$ being the Fourier transformation defined by:
$ cal(F)[f;beta] = integral_(-oo)^oo f(x)e^(-2 pi i beta x) dd(x) $

= Inversion formula
We proceed by considering the Fourier transformation, in particular given $hat(f) = cal(F)[f;beta]$ then $ f(x)=integral_(-oo)^oo hat(f)(beta) e^(2 pi i beta x) dd(beta) $ with $s = a+2pi i beta$ we apply this to the previous giving:
$ f(e^(-x))e^(-a x) = integral_(-oo)^oo F(s) e^(2pi i beta x) dd(beta) $ recall $t = e^(-x)$:
$
  f(t) & = t^(-a) integral_(-oo)^oo F(s) t^(-2pi i beta) dd(beta) \
       & = 1/(2 pi i) integral_(a-i oo)^(a+i oo) F(s)t^(-s) dd(s)
$
note that the Mellin transform is both the function $F(s)$ and a strip of holomorphy $S(a_1,a_2)$. A unique $F(s)$ with several disjoint strips of holomorphy will generally have different inverses.
