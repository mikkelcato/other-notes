#import "@preview/physica:0.9.5": *
#import "temp.typ": *


#show: thmrules.with(qed-symbol: $square$)
#show: note.with(
  title: [
    *point-set topology notes*
  ],
  authors: (
    (
      name: "mikkelius_",
    ),
  ),
  abstract: [
    notes on basic topology and some metric stuff.
  ],
)

= Metric spaces
== Definitions
If we have a space we'd like to have a way to define distance between points in the space, this is done with a metric.

#def[Metric space][
  A metric space is a pair $(X,d_X)$ where $X$ is a set and $d_X$ is a function $d_X : X times X arrow RR$, such that for all $x, y, z in X$,
  $
    d_X (x,y) & >= 0 \
    d_X (x,y) & = 0 <==> x = y \
    d_X (x,y) & = d_X (y,x) \
    d_X (x,z) & <= d_X (x,y) + d_X (y,z)
  $
]

This matches was we'd expect for a distance, it's symmetric, positive, etc.

#ex[Euclidean metric][
  Let $X = RR^n$. Let
  $
    d(bold(v),bold(w)) = abs(bold(v)-bold(w)) = sqrt(sum_(i=1)^n (v_i - w_i)^2)
  $
  this is what we usually think of when talking distance in $RR^n$. The first three axioms are trivially satsified, and the fourth follows from the Cauchy-Schwarz inequality.
  $
    d(bold(x),bold(z)) & = abs(bold(x)-bold(z)) \
                       & = abs(bold(x)-bold(y)+bold(y)-bold(z)) \
                       & <= abs(bold(x)-bold(y))+abs(bold(y)-bold(z)) \
                       & <= d(bold(x),bold(y))+d(bold(y),bold(z))
  $
]
#ex[Discrete metric][
  Let $X$ be any set and
  $
    d_X (x,y) := cases(
      1 #h(10pt) x eq.not y,
      0 #h(10pt) x eq y
    )
  $
  The first three axioms are trivially satisfied. The fourth can be shown by exhaustion. To do this note that the LHS is ${0, 1}$ and the RHS is ${0, 1, 2}$, we want $"LHS" <= "RHS"$. So for it to fail $"RHS" < "LHS"$, meaning the RHS is zero, i.e. $x=y=z$, but then the LHS is also zero.
]

As with most other structures we have a notion of subspace.
#def[Metric subspace][
  Let $(X,d_X)$ be a metric space, and $Y subset.eq X$. Then $(Y,d_Y)$ is a metric space, where $d_Y (a,b) = d_X (a,b)$, and is a subspace of $X$.
]

#ex[
  $S^n = {bold(v) in RR^(n+1) : abs(bold(v)) = 1}$, the $n$-dimensional sphere, is a subspace of $RR^(n+1)$.
]

We can also define convergence and continuity using the metric.

#def[Convergent sequence][
  Let $(x_n)$ be a sequence in a metric space $(X,d_X)$. We say $(x_n)$ converges to $x in X$, $x_n arrow x$, if $d(x_n, x) arrow 0$.

  So for all $epsilon > 0$ there exists some $N$ such that for all $n > N$ we have $d(x_n , x) < epsilon$.
]

#ex[
  Let $(bold(v)_n)$ be a sequence in $RR^k$ with the Euclidean metric. With $bold(v)_n = (v^1_n, dots, v_n^k)$ and $bold(v)=(v^1,dots,v^k) in RR^k$. Then $bold(v)_n arrow bold(v)$ if for all $i$: $(v^i_n) arrow v^i$.
]
#ex[
  Let $X$ have the discrete metric, and assume $x_n arrow x$. Let $epsilon = 1/2$, then there is some $N$ such that $d(x_n,x) < 1/2$ when $n > N$. Then $d(x_n,x) = 0$ by definition of the metric, so $x_n = x$. So if $x_n arrow x$, then eventually all $x_n = x$.
]
Limits are of course unique.
#proposition[
  If $(X,d)$ is a metric space, and $(x_n)$ is a sequence in $X$ with $x_n arrow x$ and $x_n arrow x'$, then $x=x'$.
]
#proof[
  For $epsilon > 0$, there is an $N$ such that $d(x_n,x) < epsilon\/2$ for $n > N$. Similarly there is an $N'$ such that $d(x_n, x') < epsilon\/2$ for $n > N'$.

  So if $n > max(N, N')$ then
  $
    0 & <= d(x,x') \
      & <= d(x,x_n) + d(x_n, x') \
      & = d(x_n, x)+d(x_n,x') \
      & <= epsilon
  $
  so $0 <= d(x,x') <= epsilon$ for all $epsilon > 0$. So $d(x,x') = 0 <==> x = x'$.
]

For continuity we can use many definitions, here we use the sequence definition---we show later that this is equivalent to the $epsilon$-$delta$ definition, and many others.

#def[Continuous function][
  Let $(X,d_X)$ and $(Y,d_Y)$ be metric spaces, and $f : X arrow Y$. We say $f$ is continuous if $f(x_n) arrow f(x)$ in $Y$, whenever $x_n arrow x$ in $X$.
]

#ex[
  Let $X=RR$ with the Euclidean metric and $Y=RR$ with the discrete metric. Then $f: X arrow Y$ by $f(x) = x$ is not continuous. Since $1\/n arrow 0$ in the Euclidean metric, but not in the discrete metric---since $1\/n eq.not 0$ or since it never becomes constant.

  But $g : Y arrow X$ by $g(x) = x$ is continuous. Since a sequence converging in $Y$ is eventually constant. The discrete metric is very strict with respect to convergence, since only sequences that becomes constant converge, and these types of sequences converge in all metrics.
]

#ex[Uniform metric][
  Let $X = C[0,1]$ be the set of all continuous functions on $[0,1]$, then define
  $
    d(f,g) = max_(x in [0,1]) abs(f(x)-g(x))
  $
  the maximum always exists since continuous functions on $[0,1]$ are bounded.

  Let $F:C[0,1] arrow RR$ be defined by $F(f)=f(1\/2)$. This is continuous with respect to the uniform metric on $C[0,1]$ and the usual metric on $RR$.

  Let $f_n arrow f$ in the uniform metric. Then we need to show that $F(f_n) arrow F(f)$, i.e. that $f_n (1\/2) arrow f(1\/2)$. We have
  $
    0 <= abs(F(f_n) - F(f)) = abs(f_n (1\/2) - f(1\/2)) <= max abs(f_n (x)-f(x)) arrow 0
  $
  so $abs(f_n (1\/2) - f(1\/2)) arrow 0$.
]

== Norm and inner product
The norm can be interpreted as the length of a vector in a vector space.

#def[Norm][
  Let $V$ be a real vector space. A norm on $V$ is a function $norm(dot): V arrow RR$ such that
  $
            norm(bold(v)) & >= 0 "for all" bold(v)in V \
            norm(bold(v)) & = 0 "if and only if" bold(v) = bold(0) \
     norm(lambda bold(v)) & = abs(lambda)norm(bold(v)) \
    norm(bold(v)+bold(w)) & <= norm(bold(v))+norm(bold(w))
  $
]
#ex[
  Let $V = RR^n$. We can define many norms
  $
    norm(bold(v))_1 & = sum_(i=1)^n abs(v_i) \
    norm(bold(v))_p & = (sum_(i=1)^n abs(v_i)^p)^(1\/p) \
  $
  which holds for any $1 <= p <= oo$, and in the limit $p arrow oo$
  $
    norm(bold(v))_oo = max {abs(v_i):1 <= i <= n} = max_i abs(v_i)
  $
  so we why consider
  $
    norm(bold(v))_p & = (sum_(i=1)^n abs(v_i)^p)^(1\/p) \
                    & = (M^p sum_(i=1)^n (abs(v_i)/M)^p)^(1\/p) \
                    & = M (sum_(i=1)^n (abs(v_i)/M)^p)^(1\/p)
  $
  where $M = max_i abs(v_i)$. We have $abs(v_i)\/M <= 1$ for all $i$, and for all terms with $abs(v_i)\/M < 1$ taking them to a power $p arrow oo$ makes the terms vanish. The only surviving term is the only with $abs(v_i)\/M = 1$ which is unchanged. Thus
  $
    lim_(p arrow oo) norm(bold(v))_p = norm(bold(v))_oo = max_i abs(v_i)
  $
]
Every norm naturally induces a metric on $V$:
#lemma[
  If $norm(dot)$ is a norm on $V$, then
  $
    d(bold(v),bold(w)) = norm(bold(v)-bold(w))
  $
  defines a metric on $V$.
]
#proof[
  $
    d(bold(v),bold(w)) &= norm(bold(v)-bold(w)) >= 0 \
    d(bold(v),bold(w)) &= 0 <=> norm(bold(v)-bold(w)) = 0 <=> bold(v)-bold(w) = bold(0) <=> bold(v)=bold(w) \
    d(bold(w),bold(v)) &= norm(bold(w)-bold(v)) = abs(-1)norm(bold(v)-bold(w))=d(bold(v),bold(w)) \
    d(bold(u),bold(v)) + d(bold(v),bold(w)) &= norm(bold(u)-bold(v))+norm(bold(v)-bold(w)) >= norm(bold(u)-bold(w)) = d(bold(u),bold(w))
  $
  thus all the metric axioms are satisfied, and there is a one-to-one between the axioms.

]
#ex[
  On $C[0,1]$ we have the following norms
  $
     norm(f)_1 & = integral_0^1 abs(f(x)) dd(x) \
     norm(f)_2 & = sqrt(integral_0^1 f(x)^2 dd(x)) \
    norm(f)_oo & = max_(x in [0,1]] abs(f(x)))
  $
  the first two are the $L^1$ and $L^2$ norms---the last is the uniform norm, since it induces the uniform metric.
]

The tricky part of showing that these are norms is that $norm(f) = 0$ if and only if $f = 0$.
#lemma[
  Let $f in C[0,1]$ satisfy $f(x) >= 0$ for all $x in [0,1]$. If $f(x)$ is not equivalently $0$ then $integral_0^1 f(x) dd(x) > 0$.
]
#proof[
  Choose $x_0 in [0,1]$ with $f(x_0) = a > 0$. Then since $f$ is continuous, there is a $delta$ such that $abs(f(x)-f(x_0)) < a\/2$ if $abs(x-x_0) < delta$. So $abs(f(x)) > a\/2$ in this region.

  Take $ g(x) = cases(
    a\/2 #h(15pt) & abs(x-x_0) < delta,
    0 & "otherwise"
  ) $
  then $f(x) >= g(x)$ for all $x in [0,1]$. So
  $
    integral_0^1 f(x) dd(x) >= integral_0^1 g(x) dd(x) = a/2 (2 delta) = delta a > 0
  $
]
So for the integral to vanish, and hence the norm, we must have $f=0$ constantly.

#ex[
  Let $X = C[0,1]$ and let
  $
    d_1 (f,g) = norm(f-g)_1 = integral_0^1 abs(f(x)-g(x)) dd(x)
  $
  define the sequence
  $
    f_n = cases(
      1 - n x #h(15pt) & x in [0,1\/n],
      0 & x >= 1\/n
    )
  $
  then
  $
    norm(f_n)_1 = 1/(2n) arrow 0
  $
  as $n arrow oo$, so $f_n arrow 0$ in $(X,d_1)$ where $0(x)=0$

  Also $norm(f_n)_oo = max_(x in [0,1]) abs(f_n) = 1$. So $f_n$ does not converge to $0$ in the uniform metric. Hence the function $(C[0,1],d_1) arrow (C[0,1],d_oo)$ mapping $f |-> f$ is not continuous.
]

Now we'll define the inner product, which just generalizes the dot product.
#def[Inner product][
  Let $V$ be a real vector space. An inner product on $V$ is a function $innerproduct(dot, dot) : V times V arrow RR$ such that
  $
    innerproduct(bold(v), bold(v)) &>= 0 "for all" bold(v) in V \
    innerproduct(bold(v), bold(v)) &= 0 "if and only if" bold(v)=bold(0) \
    innerproduct(bold(v), bold(w)) &= innerproduct(bold(w), bold(v)) \
    innerproduct(bold(v)_1 + lambda bold(v)_2, bold(w)) &= innerproduct(bold(v)_1, bold(w)) + lambda innerproduct(bold(v)_2, bold(w))
  $
]
#ex[
  Let $V = RR^n$ then
  $
    innerproduct(bold(v), bold(w)) = sum_(i=1)^n v_i w_i
  $
  is an inner product.

  Let $V = C[0,1]$ then
  $
    innerproduct(f, g) = integral_0^1 f(x) g(x) dd(x)
  $
  is an inner product.
]
We wan't to prove that inner products also induce metrics. To do this we need the Cauchy-Schwarz inequality
#thm[Cauchy-Schwarz inequality][
  If $innerproduct(dot, dot)$ is an inner product, then
  $
    innerproduct(bold(v), bold(w))^2 <= innerproduct(bold(v), bold(v)) innerproduct(bold(w), bold(w))
  $
]
#proof[
  For any $x$,
  $
    innerproduct(bold(v)+x bold(w), bold(v)+x bold(w)) = innerproduct(bold(v), bold(v))+2 x innerproduct(bold(v), bold(w)) + x^2 innerproduct(bold(w), bold(w)) >= 0
  $
  this is a quadratic in $x$, and since it's always positive it can have at most one real root. So the determinant gives
  $
    4 innerproduct(bold(v), bold(w))^2 - 4 innerproduct(bold(v), bold(v))innerproduct(bold(w), bold(w)) <= 0
  $
  and the result follows.
]
Now we can show that inner products induce norms, and therefore metrics.
#lemma[
  If $innerproduct(dot, dot)$ is an inner product on $V$, then
  $
    norm(bold(v)) = sqrt(innerproduct(bold(v), bold(v)))
  $
  is a norm.
]
#proof[
  $
    norm(bold(v)) &= sqrt(innerproduct(bold(v), bold(v))) >= 0 \
    norm(bold(v)) &= 0 <=> innerproduct(bold(v), bold(v)) = 0 <=> bold(v) = bold(0) \
    norm(lambda bold(v)) &= sqrt(innerproduct(lambda bold(v), lambda bold(v))) = sqrt(lambda^2 innerproduct(bold(v), bold(v))) = abs(lambda)norm(bold(v)) \
    (norm(bold(v)) + norm(bold(w)))^2 &= norm(bold(v))^2 + 2 norm(bold(v))norm(bold(w)) + norm(bold(w))^2 \
    &>= innerproduct(bold(v), bold(v)) + 2 innerproduct(bold(v), bold(w)) + innerproduct(bold(w), bold(w)) \
    &= norm(bold(v)+bold(w))^2
  $
]

== Open & closed subsets
We'll see that everything can essentially be defined in terms of open and closed subsets of metric spaces. To define these we need to know about balls.

#def[Open & closed balls][
  Let $(X,d)$ be a metric space. For any $x in X$ and $r in RR$ we define the open ball centered at $x$:
  $
    B_r (x) = {y in X : d(y,x) < r}
  $
  so it's all points with distance to $x$ less than $r$---and the closed ball centered at $x$:
  $
    overline(B)_r (x) = {y in X : d(y,x) <= r}
  $
  so the closed ball includes the boundary.
]

#ex[
  Let $X = RR$, then $B_r (x) = (x-r,x+r)$ and $overline(B)_r (x) = [x-r,x+r]$

  Let $X = RR^2$. If $d$ is induced by $norm(bold(v))_1 = abs(v_1) + abs(v_2)$, then the open ball is a rotated square---since if $abs(v_1) = r$ then $abs(v_2) = 0$, $abs(v_1) = r\/2$ then $abs(v_2) = r\/2$, etc. Of course the boundary is not included. If $d$ is induced by $norm(bold(v))_2 = sqrt(v_1^2+v_2^2)$ then we get an actual disk. If $d$ is induced by $norm(bold(v))_oo = max {abs(v_1), abs(v_2)}$ then we get a square, since the only requirement is that no element is $> r$.
]

#def[Open subset][
  $U subset.eq X$ is an open subset if for every $x in U$, there exists some $delta > 0$ such that $B_delta (x) subset.eq U$.

  $C subset.eq X$ is a closed subset if $X \\ C subset.eq X$ is open.
]

This is a very important definition, and to see that it makes sense we prove the open ball is open.
#lemma[
  The open ball $B_r (x) subset.eq X$ is an open subset, and the closed ball $overline(B)_r (x) subset.eq X$ is a closed subset.
]
#proof[
  Given $y in B_r (x)$ we need to find a $delta > 0$ with $B_delta (y) subset.eq B_r (x)$.

  Since $y in B_r (x)$, we have $a = d(y,x) < r$. Let $delta = r-a > 0$. Then if $z in B_delta (y)$, we have $d(z,y) < r-a$,
  $
    d(z,x) <= d(z,y)+d(y,x) < (r-a)+a = r
  $
  so $z in B_r (x)$. So $B_delta (y) subset.eq B_r (x)$, and hence $B_r (x)$ is open.

  The second statement says that $X \\ overline(B)_r (x) = {y in X : d(y,x) > r}$ is open. Given $y in X\\overline(B)_r (x)$ we need to find a $delta > 0$ with $B_delta (y) subset.eq X\\overline(B)_r (x)$. Since $y in X\\overline(B)_r (x)$ we have $a = d(y,x) > r$. Let $delta = a - r > 0$. Then if $z in B_delta (y)$, we have $d(z,y) < a-r => r < a - d(z,y)$,
  $
    d(x,z) >= d(x,y)-d(z,y) > r
  $
  so $z in X \\ overline(B)_r (x)$. So $B_delta (y) subset.eq X\\overline(B)_r (x)$, and hence $overline(B)_r (x)$ is closed.
]

Evidently openness is only a property of subsets, since $A subset.eq X$ being open depends on both $A$ and $X$.

#ex[
  $(0,1) subset.eq RR$ is open, $[0,1] subset.eq RR$ is closed.

  $QQ subset.eq RR$ is neither, since any open interval has rationals and irrationals. So any open interval cannot be a subset of $QQ$ or $RR\\QQ$.

  Let $X = [-1,1] \\ {0}$ with the Euclidean metric. Let $A = [-1,0) subset.eq X$. Then $A$ is open since it is equal to $B_1 (-1)$. $A$ is also closed since it is equal to $overline(B)_(1\/2) (- 1\/2)$---since $B_1 (-1) inter X = A$, same for the closed case.
]

As a shorthand we introduce the neighborhood.
#def[Open neighborhood][
  If $x in X$, an open neighborhood of $x$ is an open $U subset.eq X$ with $x in U$---so an open neighborhood of $x$ is just an open subset containing $x$.
]

#lemma[
  If $U$ is an open neighborhood of $x$ and $x_n arrow x$, then there exists an $N$ such that $x_n in U$ for all $n > N$.
]
#proof[
  Given that $U$ is open, there is some $delta > 0$ such that $B_delta (x) subset.eq U$. Since $x_n arrow x$, there is some $N$ such that $d(x_n,x) < delta$ for all $n > N$. This implies $x_n in B_delta (x)$ for all $n > N$. So $x_n in U$ for all $n > N$.
]

#def[Limit point][
  Let $A subset.eq X$. Then $x in X$ is a limit point of $A$ if there is a sequence $x_n arrow x$ such that $x_n in A$ for all $n$---some definitions include the restriction that $x_n eq.not x$, we don't.
]

So limit points are the points we can get arbritrarily close to---so $x$ is a limit point if at least one sequence entirely within $A$ converges to it.

#ex[
  If $a in A$, then it is a limit point of $A$, just take $a, a, a, dots$---according to the usual definition this would not be allowed.
]
#ex[
  If $A = (0,1) subset.eq RR$, then $0$ is a limit point of $A$, for example take $x_n = 1\/n$.
]

Closed subsets can be characterized using these limit points---this is often nicer then showing the complement is open.

#proposition[
  $C subset.eq X$ is a closed subset if and only if every limit point of $C$ is an element of $C$---so closed subsets contain their limit points.
]
#proof[
  $(=>)$ Let $C$ be closed and $x_n arrow x$, $x_n in C$. We need to show that $x in C$.

  Given $C$ is closed, the complement $A = X\\C subset.eq X$ is open. Assume that $x in.not C$, then $x in A$---so $A$ is an open neighborhood of $x$. By the previous lemma then there is some $N$ such that $x_n in A$ for all $n >= N$. So $x_N in A$, but by assumption $x_N in C$---contradiction, so we must have $x in C$.

  $(arrow.double.l)$ Assume $C$ contains all its limit points, and for contradiction assume it's not closed. Since $C$ is not closed, $A$ is not open. So there is some $x in A$ such that the open ball $B_delta (x)$ is not contained in $A$ for all $delta > 0$. This implies that $B_delta (x) inter C eq.not emptyset$ for all $delta > 0$.

  For every $n in NN$, choose $x_n in B_(1\/n) (x) inter C$. Then $x_n in C$ and $d(x_n,x) < 1\/n arrow 0$. So $x_n arrow x$. So $x$ is a limit point of $C$, but $x in.not C$, contradicting that $C$ contains all its limit points. Thus $C$ is closed.
]
Now we can prove the important result about metrics and continuity---namely showing that metrics are useless.
#proposition[Characterization of continuity][
  Let $(X, d_X)$ and $(Y,d_Y)$ be metric spaces, and $f : X arrow Y$. The following are equivalent,
  $
    (1)" "&f "is continuous." \
    (2)" "&"If" x_n arrow x", then" f(x_n) arrow f(x). \
    (3)" "&"For any closed subset" C subset.eq Y", "f^(-1) (C) "is closed in" X. \
    (4)" "&"For any open subset" U subset.eq Y", "f^(-1) (U) "is open in" X. \
    (5)" "&"For any" x in X" and" epsilon > 0", there is some" delta > 0 "such that" f(B_delta (x)) subset.eq B_epsilon (f(x)). \
    &"  Alternatively" d_X (x,z) < delta => d_Y (f(x),f(z)) < epsilon.
  $
]
#proof[
  $(1) <=> (2)$ by definition.

  $(2) => (3)$. Let $C subset.eq Y$ be closed. We want to show that the preimage $f^(-1) (C)$ is closed. Let $x_n arrow x$, where $x_n in f^(-1) (C)$. We need to show all the limit points are also in $f^(-1) (C)$.

  We know $f(x_n) arrow f(x)$ by $(2)$ and $f(x_n) in C$. So $f(x)$ is a limit point of $C$ and since $C$ is closed $f(x) in C$. This implies that $x in f^(-1) (C)$, so every limit point of $f^(-1) (C)$ is in $f^(-1) (C)$. So $f^(-1) (C)$ is closed.

  $(3) => (4)$. If $U subset.eq Y$ is open, then $Y \\ U$ is closed in $Y$. So $f^(-1) (Y\\U) = X \\ f^(-1) (U)$ is closed in $X$ by $(3)$---the equality follows since the preimage respects set operations. So $f^(-1) (U) subset.eq X$ is open.

  $(4) => (5)$. Given $x in X$ and $epsilon > 0$ then $B_epsilon (f(x))$ is open in $Y$. By $(4)$ then $f^(-1) (B_epsilon (f(x))) = A$ is open in $X$. We know $f(x) in B_epsilon (f(x))$ so $x in A$. This means there is a $delta > 0$ with $B_delta (x) subset.eq A$. So,
  $
    f(B_delta (x)) subset.eq f(A) = f(f^(-1) (B_epsilon (f(x)))) = B_epsilon (f(x))
  $
  to see this is equivalent to the $epsilon$-$delta$ definition. Let $z in B_delta (x)$, then $z in f^(-1) (B_epsilon (f(x)))$. So $f(z) in B_epsilon (f(x))$,
  $
    d_X (x, z) < delta => d_Y (f(x),f(z)) < epsilon
  $

  $(5) => (2)$. Assume $x_n arrow x$. Let $epsilon > 0$, then there exists some $delta > 0$ such that $f(B_delta (x)) subset.eq B_epsilon (f(x))$ by $(5)$. Since $x_n arrow x$, there is some $N$ such that $x_n in B_delta (x)$ for all $n > N$, by the previous lemma. Then
  $
    f(x_n) in f(B_delta (x)) subset.eq B_epsilon (f(x))
  $
  for all $n > N$. So $f(x_n) arrow f(x)$.
]
Before we begin topology proper we'll prove some properties of open sets.

#lemma[
  $(1)$. $emptyset$ and $X$ are open subsets of $X$.

  $(2)$. Suppose $V_alpha subset.eq X$ is open for all $alpha in A$. Then $U = union.big_(alpha in A) V_alpha$ is open in $X$---note that we can take infinite unions.

  $(3)$. If $V_1, dots, V_n subset.eq X$ are open, then $V = inter.big_(i=1)^n V_i$ is open---note that we can only take finite intersections.
]
#proof[
  $(1)$. $emptyset$ satisfies the definition vacously, and $X$ is open since for any $x$, every ball $B_r (x)$ is contained in $X$.

  $(2)$. If $x in U$, then $x in V_alpha$ for some $alpha$. Since $V_alpha$ is open, there is some $delta > 0$ such that $B_delta (x) subset.eq V_alpha$. So $B_delta (x) subset.eq union.big_(alpha in A) V_alpha = U$. So $U$ is open.

  $(3)$. If $x in V$, then $x in V_i$ for all $i = 1, dots, n$. So there is some $delta_i > 0$ with $B_delta_i (x) subset.eq V_i$. Choose $delta = min {delta_1, dots, delta_n}$. So $B_delta (x) subset.eq V_i$ for all $i$. So $B_delta (x) subset.eq V$. So $V$ is open.

]

To see why infinite intersections aren't valid consider the intersection of all $(-1\/n, 1\/n)$ which is ${0}$, which is not open.


#pagebreak()
= Topological spaces
We have seen that open sets are nice and the metric is relatively less nice. So we define the topology of a space, which is basically just all the open sets of the space.

== Definitions
#def[Topological space][
  A topological space is a set $X$---the space---together with a set $cal(U) subset.eq PP(X)$---the topology---such that,
  $
    (1).& emptyset, X in cal(U) \
    (2).& "If" V_alpha in cal(U) "for all" alpha in A "then" union.big_(alpha in A) V_alpha in cal(U) \
    (3).& "If" V_1,dots,V_n in cal(U) "then" inter.big_(i=1)^n V_i in cal(U)
  $
  the elements of $X$ are the points, and the elements of $cal(U)$ are the open subsets of $X$---so a topological space is just a space and all its open subsets combined in a single structure.
]

#def[Induced topology][
  Let $(X,d)$ be a metric space. The topology induced by $d$ is the set of all open sets of $X$ under $d$.
]

#ex[Same topology][
  Let $X = RR^n$ and $d_1 (bold(x),bold(y)) = norm(bold(x)-bold(y))_1$ and $d_oo (bold(x),bold(y)) = norm(bold(x)-bold(y))_oo$. These induce the same topology, to see this recall
  $
    norm(bold(v))_1 = sum_(i=1)^n abs(v_i)", " norm(bold(v))_oo = max_(1 <= i <= n) abs(v_i)
  $
  this implies
  $
    norm(bold(v))_oo <= norm(bold(v))_1 <= n norm(bold(v))_oo
  $
  the first inequality implies
  $
    norm(bold(y)-bold(x))_oo <= norm(bold(y)-bold(x))_1 <= r
  $
  so if $y in B_r^1 (x) => y in B_r^oo (x)$, so $B_r^1 (x) subset.eq B_r^oo (x)$. The second inequality implies
  $
    norm(bold(y)-bold(x))_oo <= r/n => norm(bold(y)-bold(x))_1 <= n norm(bold(y)-bold(x))_oo <= r
  $
  so if $y in B_(r\/n)^oo (x) => y in B_r^1 (x)$, so $B_(r\/n)^oo (x) subset.eq B_r^1 (x)$
  chaining them
  $
    B_(r\/n)^oo (x) subset.eq B_r^1 (x) subset.eq B_r^oo (x)
  $
  now if they induce the same topology, then if $U$ is open with respect to $d_1$, then we need to show it is also open with respect to $d_oo$.

  Let $x in U$, then there is some $delta > 0$ such that $B_delta^1 (x) subset.eq U$. So $B_(delta\/n)^oo (x) subset.eq B_delta^1 (x) subset.eq U$---so $U$ is open under $d_oo$. For the other direction we do exactly the same, just using the other inequality.
]

#ex[Other topologies][
  Let $X$ be any set.

  $(1)$. $cal(U) = {emptyset, X}$ is the coarse topology on $X$.

  $(2)$. $cal(U) = PP(X)$ is the discrete topology on $X$---since it is induced by the discrete metric.

  $(3)$. $cal(U) = {A subset.eq X : X\\A "is finite or" A = emptyset}$ is the cofinite topology on $X$.

  Let $X = RR$, and $cal(U) = {(a,oo) : a in RR}$ is the right order topology on $RR$.
]

Now we can define continuity in terms of the topology.
#def[Continuous function][
  Let $f : X arrow Y$ be a map of topological spaces. Then $f$ is continuous if $f^(-1) (U)$ is open in $X$ whenever $U$ is open in $Y$.
]
Note that if the topology is induced by a metric, then this coincides with the metric definition.
#ex[
  Any $f : X arrow Y$ is continuous if $X$ has the discrete topology.

  Any $f : X arrow Y$ is continuous if $Y$ has the coarse topology.
]

#lemma[
  If $f : X arrow Y$ and $g : Y arrow Z$ are continuous, then so is $g compose f : X arrow Z$.
]
#proof[
  If $U subset.eq Z$ is open, $g$ is continuous, then $g^(-1) (U)$ is open in $Y$. Since $f$ is continuous, so $f^(-1) (g^(-1) (U))=(g compose f)^(-1) (U)$ is open in $X$---so $g compose f$ is continuous.
]

As with other structures in math we have the idea that different things are essentially the same, i.e. isomorphic groups. For topological spaces we have homeomorphisms, and homeomorphic spaces are considered the same.
#def[Homeomorphism][
  $f : X arrow Y$ is a homeomorphism if

  $(1)$. $f$ is a bijection.

  $(2)$. Both $f$ and $f^(-1)$ are continuous.

  Equivalently $f$ is a bijection and $U subset.eq X$ is open if and only if $f(U) subset.eq Y$ is open.
]
Two spaces are homeomorphic if a homeomorphism between them exists, we write $X tilde.eq Y$. Here we require both $f$ and $f^(-1)$ are continuous, unlike in group theory where a bijective homomorphism automatically has an inverse.

#lemma[
  Homeomorphism is an equivalence relation.
]
#proof[

  $(1)$. The identity map $I_X : X arrow X$ is always a homeomorphism. So $X tilde.eq X$.

  $(2)$. If $f : X arrow Y$ is a homeomorphism, then so is $f^(-1) : Y arrow X$. So $X tilde.eq Y => Y tilde.eq X$.

  $(3)$. If $f : X arrow Y$ and $g : Y arrow Z$ are homeomorphisms, then $g compose f : X arrow Z$ is a homeomorphism. So $X tilde.eq Y$ and $Y tilde.eq Z$ implies $X tilde.eq Z$.
]
#ex[

  $(1)$. Under the normal topology, we have $(0,1) tilde.eq (a,b)$ for all $a,b in RR$ using $x |-> a + (b-a)x$---since $tilde.eq$ is an equivalence relation this implies that all open intervals in $RR$ are homeomorphic.

  $(2)$. $(-1,1) tilde.eq RR$ by $x |-> tan (pi x)/2$.

  $(3)$. $RR tilde.eq (0,oo)$ by $x |-> e^x$.

  $(4)$. $(a, oo) tilde.eq (b, oo)$ by $x |-> x + (b-a)$
]

So it is easy to show that two spaces are homeomorphic, since we just need to write a homeomorphism. However, it is much harder to prove that two spaces are not homeomorphic. To do this we need to define topological properties, which homeomorphic spaces share---e.g. connectivity and compactness, these will be described later.

== Sequences
We recall open neighborhoods,
#def[Open neighborhood][
  An open neighborhood of $x in X$ is an open set $U subset.eq X$ with $x in U$.
]
we use this to define convergence
#def[Convergent sequence][
  A sequence $x_n -> x$ if for every open neighborhood $U$ of $x$ there is an $N$ such that $x_n in U$ for all $n > N$.
]
#ex[
  If $X$ has the coarse topology, then any sequence $x_n$ converges to every $x in X$ since there is only one open neighborhood of $x$, namely $X$ itself.
]
#ex[
  If $X$ has the cofinite topology, then no two $x_n$ are the same, then $x_n -> x$ for every $x in X$ since every open set can only have finitely many $x_n$ not inside it.
]

This in no way ensures unique limits, which we would like.

#def[Hausdorff space][
  A topological space $X$ is Hausdorff if for all $x_1, x_2 in X$ with $x_1 eq.not x_2$ there exist open neighborhoods $U_1$ of $x_1$ and $U_2$ of $x_2$ such that $U_1 inter U_2 = emptyset$.
]

#lemma[
  If $X$ is Hausdorff, $x_n$ is a sequence in $X$ with $x_n -> x$ and $x_n -> x'$, then $x = x'$.

  So limits are unique in a Hausdorff space.
]

#proof[
  Suppose for contradiction $x eq.not x'$. Then by definition there are open neighborhoods $U, U'$ of $x, x'$ with $U inter U' = emptyset$.

  Since $x_n arrow x$ then $U$ is a neighborhood of $x$, so by definition there is some $N$ such that for $n > N$ we have $x_n in U$. Similarly since $x_n arrow x'$ then $U'$ is a neighborhood of $x'$, so by definition there is some $N'$ such that for $n > N'$ we have $x_n in U'$.

  Let $n > max(N, N')$ then $x_n in U$ and $x_n in U'$. But $U inter U' = emptyset$, so contradiction. So $x = x'$.
]

#ex[
  If $X$ has more than $1$ element, then the coarse topology on $X$ is not Hausdorff.
]
#ex[
  The discrete topology is always Hausdorff.
]
#ex[
  If $(X,d)$ is a metric space, the topology induced by $d$ is Hausdorff---for $x_1 eq.not x_2$, let $r = d(x_1, x_2) > 0$, then take $U_i = B_(r\/2) (x_i) => U_1 inter U_2 = emptyset$.
]

== Closed sets
#def[Closed sets][
  $C subset.eq X$ is closed if $X \\ C$ is an open subset of $X$.
]
#lemma[
  $(1)$ If $C_alpha$ is a closed subset of $X$ for all $alpha in A$, then $inter.big_(alpha in A) C_alpha$ is closed in $X$.

  $(2)$ If $C_1, dots, C_n$ are closed in $X$, then so is $union.big_(i=1)^n C_i$.
]
#proof[
  $(1)$ $C_alpha$ is closed in $X$ so $X\\C_alpha$ is open in $X$. So $union.big_(alpha in A) (X\\C_alpha) = X\\inter.big_(alpha in A) C_alpha$ is open. So $inter.big_(alpha in A) C_alpha$ is closed.

  $(2)$ If $C_i$ is closed in $X$, then $X\\C_i$ is open. So $inter.big_(i=1)^n (X\\C_i) = X\\union.big_(i=1)^n C_i$ is open. So $union.big_(i=1)^n C_i$ is closed.
]
Here we can take finite unions, and infinite intersections, which is opposite to what we had for open sets. Note that the topology could just as well be defined as the collection of closed sets.

#corollary[
  If $X$ is Hausdorff and $x in X$, then ${x}$ is closed in $X$---so all singletons are closed.
]
#proof[
  For all $y in X$, there exist open subsets $U_y, V_y$ with $y in U_y, x in V_y$ and $U_y inter V_y = emptyset$.

  Let $C_y = X\\U_y$. Then $C_y$ is closed, $y in.not C_y, x in C_y$. So ${x} = inter.big_(y eq.not x) C_y$ is closed since it is an intersection of closed subsets.
]

== Closure & Interior
=== Closure
Given a subset $A subset.eq X$ we'd like to find the smallest closed subset containing $A$---this is the closure of $A$.

#def[Closure][
  Let $X$ be a topological space and $A subset.eq X$. Define
  $
    cal(C)_A = {C subset.eq X : A subset.eq C "and" C "is closed in" X}
  $
  then the closure of $A$ in $X$ is
  $
    overline(A) = inter.big_(C in cal(C)_A) C
  $
]
So we take the intersection of all closed subsets of $X$ containing $A$---since $overline(A)$ is an intersection of closed subsets, then it is also closed. If $C in cal(C)_A$ then $A subset.eq C$, for every $C$. So $A subset.eq inter.big_(C in cal(C)_A) C = overline(A)$.

#proposition[
  $overline(A)$ is the smallest closed subset of $X$ containing $A$.
]
#proof[
  Let $K subset.eq X$ be a closed set containing $A$. Then $K in cal(C)_A$. So $overline(A) = inter.big_(C in cal(C)_A) C subset.eq K$. So $overline(A) subset.eq K$.
]

The closure is essentially defined to satisfy this property. But the closure is difficult to compute.

#def[Limit point][
  A limit point of $A$ is an $x in X$ such that there is a sequence $x_n -> x$ with $x_n in A$ for all $n$.
]

Let
$
  L (A) = {x in X : x "is a limit point of" A}
$
i.e. the set of all limit points of $A$.
#lemma[
  If $C subset.eq X$ is closed then $L(C) = C$.
]
#proof[
  same as for metric spaces.

  Assume $x_n -> x$, we need to show that $x in C$. Given $C$ is closed, the complement $A = X\\C subset.eq X$ is open. Assume that $x in.not C$, then $x in A$---so $A$ is an open neighborhood of $x$. Then there is some $N$ such that $x_n in A$ for all $n >= N$. So $x_N in A$, but by assumption $x_N in C$---contradiction, so we must have $x in C$.

]
For metric spaces we also proved the other direction, this is not true in general for topological spaces. The thing we can say is
#proposition[
  $L(A) subset.eq overline(A)$.
]
#proof[
  If $A subset.eq C$, then $L(A) subset.eq L(C)$. If $C$ is closed, then $L(C) = C$. So $C in cal(C)_A => L(A) subset.eq C$. So $L(A) subset.eq inter.big_(C in cal(C)_A) C = overline(A)$---since $L(A)$ is in every $C in cal(C)_A$.
]

This implies the previous lemma, since for any $A$, we have $A subset.eq L(A) subset.eq overline(A)$, and when $A$ is closed $A = overline(A)$, meaning $L(A) = A$ when $A$ is closed.

#corollary[
  Given a subset $A subset.eq X$, if we can find some closed $C$ such that $A subset.eq C subset.eq L(A)$, then we have $C = overline(A)$.
]
#proof[
  $C subset.eq L(A) subset.eq overline(A) subset.eq C$, since $overline(A)$ is the smallest closed subset containing $A$---so $C = L(A) = overline(A)$.
]

#ex[
  Let $(a,b) subset.eq RR$ then $overline((a,b)) = [a,b]$.

  Let $QQ subset.eq RR$. Then $overline(QQ) = RR$.

  $overline(RR\\QQ) = RR$.

  In $RR^n$ with Euclidean metric, $overline(B_r (x)) = overline(B)_r (x)$. In general $overline(B_r (x)) subset.eq overline(B)_r (x)$ since $overline(B)_r (x)$ is closed and $B_r (x) subset.eq overline(B)_r (x)$---e.g. if $X$ has discrete metric, then $B_1 (x) = {x} = overline(B_1 (x))$, but $overline(B)_1 (x) = X$.
]

#def[Dense subset][
  $A subset.eq X$ is dense in $X$ if $overline(A) = X$---e.g both $QQ$ and $RR\\QQ$ are dense in $RR$ with the usual topology, as seen in the above example.
]
=== Interior
The interior is just the largest open subset contained in $A$.

#def[Interior][
  Let $A subset.eq X$, and define
  $
    cal(O)_A = {U subset.eq X : U subset.eq A, U "is open in" X}
  $
  i.e. all open subsets of $X$ contained in $A$, then interior of $A$ is
  $
    "Int"(A) = union.big_(U in cal(O)_A) U
  $
]
#proposition[
  $"Int"(A)$ is the largest open subset of $X$ contained in $A$.
]
#proof[
  Let $K subset.eq X$ be a open subset contained in $A$. Then $K in cal(O)_A$. So $K subset.eq union.big_(U in cal(O)_A) U = "Int"(A)$.
]
#proposition[
  $X\\"Int"(A) = overline(X\\A)$
]
#proof[
  $U subset.eq A <=> (X\\U) supset.eq (X\\A)$. And $U$ is open in $X$ $<=> X\\U$ is closed in $X$.

  So the complement of the largest open subset of $X$ contained in $A$ will be the smallest closed subset containing $X\\A$---i.e. $X\\"Int"(A) = overline(X\\A)$.
]

#ex[
  $"Int"(QQ) = "Int"(RR\\QQ) = emptyset$.
]

== Derived Topologies
=== Subspace topology
#def[Subspace topology][
  Let $X$ be a topological space and $Y subset.eq X$. The subspace topology on $Y$ is given by: $V$ is an open subset of $Y$ if there is some $U$ open in $X$ such that $V = Y inter U$---so $V$ is the part of $U$ that is in $Y$.
]

When writing $Y subset.eq X$ the subspace topology is assumed.
#proposition[
  The subspace topology is a topology.
]
#proof[
  $(1)$ Since $emptyset$ is open in $X$, $emptyset = Y inter emptyset$ is open in $Y$.

  Since $X$ is open in $X$, $Y = Y inter X$ is open in $Y$.

  $(2)$ If $V_alpha$ is open in $Y$, then $V_alpha = Y inter U_alpha$ for some $U_alpha$ open in $X$. Then
  $
    union.big_(alpha in A) V_alpha = union.big_(alpha in A) (Y inter U_alpha) = Y inter (union.big_(alpha in A) U_alpha)
  $
  since $union.big U_alpha$ is open in $X$, so $union.big V_alpha$ is open in $Y$.

  $(3)$ If $V_i$ is open in $Y$, then $V_i = Y inter U_i$ for some open $U_i subset.eq X$. Then
  $
    inter.big_(i=1)^n V_i = inter.big_(i=1)^n (Y inter U_i) = Y inter (inter.big_(i=1)^n U_i)
  $
  since $inter.big U_i$ is open, $inter.big V_i$ is open.
]

If $Y subset.eq X$ there is an inclusion function $cal(i) : Y -> X$ that sends $y |-> y$.

#proposition[
  If $Y$ has the subspace topology, $f : Z -> Y$ is continuous if and only if $cal(i) compose f : Z -> X$ is continuous.
]
#proof[
  $(=>)$ If $U subset.eq X$ is open, then $cal(i)^(-1) (U) = Y inter U$ is open in $Y$. So $cal(i)$ is continuous. So if $f$ is continuous, so is $cal(i) compose f$.

  $(arrow.double.l)$ Suppose $cal(i) compose f$ is continuous. Given $V subset.eq Y$ is open, we know that $V = Y inter U = cal(i)^(-1) (U)$. So $f^(-1) (V) = f^(-1) (cal(i)^(-1) (U))) = (cal(i) compose f)^(-1) (U)$ is open since $cal(i) compose f$ is continuous. So $f$ is continuous.
]

This can be used as the defining property---$Y$ is a subspace of $X$ if there exists some function $cal(i) : Y -> X$ such that for any $f$, $f$ is continuous if and only if $cal(i) compose f$ is continuous.

=== Product topology
If $X$ and $Y$ are sets, the product is defined as
$
  X times Y = {(x,y) : x in X, y in Y}
$
We have the projection functions $pi_1 : X times Y -> X$, $pi_2 : X times Y -> Y$ given by
$
  pi_1 (x,y) = x,"  " pi_2 (x,y) = y
$
if $A subset.eq X$, $B subset.eq Y$, then $A times B subset.eq X times Y$.

Given topological spaces $X$ and $Y$ we can define
#def[Product topology][
  Let $X$ and $Y$ be topological spaces. The product topology on $X times Y$ is given by:

  $U subset.eq X times Y$ is open if, for every $(x, y) in U$ there exist open neighborhoods of $x$ and $y$: $V_x subset.eq X$, $W_y subset.eq Y$ such that $V_x times W_y subset.eq U$.

  So we can always find $V_x times W_y$---an open rectangle---with $(x,y) in V_x times W_y$ and $V_x times W_y subset.eq U$. Taking the union of every open rectangle gives $U$,
  $
    U = union.big_((x,y) in U) V_x times W_y
  $
]

#ex[
  If $V subset.eq X$ and $W subset.eq Y$ are open, then $V times W subset.eq X times Y$ is open---take $V_x = V$ and $W_y = W$.

  $(0,1) times (0,1) times dots times (0,1) subset.eq RR^n$ is the open $n$-dimensional cube in $RR^n$, since $(0,1) tilde.eq RR$, we have $(0,1)^n tilde.eq RR^n tilde.eq "Int"(D^n)$.

  Let $A subset.eq {(r,z) : r > 0} subset.eq RR^2$, $R(A)$ be the set obtained by rotation $A$ around the $z$ axis. Then $R(A) tilde.eq S times A$ by
  $
    (x,y,z) = (bold(v),z) |-> (hat(bold(v)),(abs(bold(v)),z))
  $
  in particular if $A$ is a circle, then $R(A) tilde.eq S^1 times S^1 = T^2$ is the two-dimensional torus.
]

The defining property is that $f : Z -> X times Y$ is continuous if and only if $pi_1 compose f$ and $pi_2 compose f$ are continuous.

If $U subset.eq X times Y$ is open, then
$
  U = union.big_((x,y) in U) V_x times W_y
$
so $U subset.eq X times Y$ is open if and only if it is a union of members of our special class of subsets---$V times W$---this is a basis.
#def[Basis][
  Let $cal(U)$ be a topology on $X$. A subset $cal(B) subset.eq cal(U)$ is a basis if: $U in cal(U)$ if and only if $U$ is a union of sets in $cal(B)$---i.e. every $U in cal(U)$ is made from the basis.
]

#ex[
  ${V times W: V subset.eq X, W subset.eq Y "are open"}$ is a basis for the product topology for $X times Y$.

  If $(X,d)$ is a metric space, then
  $
    {B_(1\/n) (x) : n in NN^+ , x in X}
  $
  is a basis for the topology induced by $d$.
]

=== Quotient topology
If $X$ is a set and $tilde$ is an equivalence relation on $X$, then the quotient $X\/tilde$ is the set of equivalence classes. The projection $X -> X\/tilde$ is defined as $pi(x) = [x]$---the equivalence class containing $x$.

#def[Quotient topology][
  If $X$ is a topological space, the quotient topology on $X\/ tilde$ is given by: $U$ is open in $X\/tilde$ if $pi^(-1) (U)$ is open in $X$.

  We can treat the quotient as gluing together points identified by $tilde$ together. The defining property is $f : X\/tilde -> Y$ is continuous if and only if $f compose pi : X -> Y$ is continuous.
]

#ex[
  Let $X = RR$, $x tilde y$ if and only if $x - y = n in ZZ$---so if two numbers differ by an integer they are the same $[x] = {x + n: n in ZZ}$. Then $X\/tilde = RR\/ZZ tilde.eq S^1$, given by $[x] |-> (cos 2 pi x, sin 2 pi x)$---since the set of equivalence classes is just the interval $[0,1)$, and if $x-y=n => 2pi (x-y) = 2pi n$ then $cos 2 pi x = cos 2 pi y$.

  Let $X = RR^2$, then $bold(v) tilde bold(w)$ if and only if $bold(v)-bold(w) in ZZ^2$. Then $X\/tilde = RR^2 \/ZZ^2 = (RR\/ZZ) times (RR\/ZZ) tilde.eq S^1 times S^1 = T^2$.  Similarly $RR^n\/ZZ^n = T^n = S^1 times S^1 times dots times S^1$.
]
#ex[
  If $A subset.eq X$, define $tilde$ by $x tilde y$ if and only if $x = y$ or $x, y in A$. This glues everything in $A$ together and leaves everything else alone. This is typically written as $X\/A$, which is non consistent with the previous notation.

  Let $X = [0,1]$ and $A = {0,1}$, then $X\/A tilde.eq S^1$ by, e.g. $t |-> (cos 2 pi t, sin 2 pi t)$. The equivalence relation says that the end points $0$ and $1$ are _the same_, so we join the ends together giving us a circle.
  Let $X = D^n$ and $A = S^(n-1)$, then $X\/A tilde.eq S^n$---e.g. disk becomes sphere, so $D^2\/S^1 tilde.eq S^2$.
]
#ex[
  Let $X = [0,1] times [0,1]$ with $tilde$ given by $(0, y) tilde (1, y)$ and $(x, 0) tilde (x, 1)$, then $X\/tilde tilde.eq S^1 times S^2 = T^2$, by, e.g
  $
    (x, y) |-> ((cos 2 pi x, sin 2 pi x), (cos 2 pi y, sin 2 pi y))
  $
  in this case everything on the top and bottom side of our closed square would be glued together---giving a cylinder---and similarly for the left and right sides---giving a torus.
  Likewise $T^3 = [0,1]^3 \/tilde$ with an analogous equivalence relation.
]

#pagebreak()
= Connectivity
== _normal_ Connectivity
#def[
  A topological space $X$ is disconnected if $X$ can be written as $A union B$, where $A$ and $B$ are disjoint, non-empty open subsets of $X$---$A$ and $B$ disconnect $X$.

  A space is connected if it is not disconnected.
]

Notably this is a property of the space $X$---and is a topological property meaning if $X tilde.eq Y$ then $X$ being (dis)connected implies $Y$ is (dis)connected. This follows by considering the homeomorphism $f: X -> Y$, by definition $A$ is open in $X$ if and only if $f(A)$ is open in $Y$. So $A$ and $B$ disconnect $X$ if and only if $f(A)$ and $f(B)$ disconnect $Y$.

#ex[

  Let $X subset.eq RR$, if there exists some $alpha in RR\\X$ such that for some $a,b in X$ we have $a < alpha < b$, then $X$ is disconnected. Explicitly $X inter (-oo,alpha)$ and $X inter (alpha,oo)$ disconnect $X$.
]

#proposition[
  $X$ is disconnected if and only if there exists a continuous surjective $f: X -> {0,1}$ with the discrete topology.

  Alternatively $X$ is connected if and only if any continuous map $f : X -> {0,1}$ is constant.
]
#proof[
  ($=>$) Assume $A$ and $B$ disconnect $X$, define
  $
    f(x) = cases(0",  "x in A, 1",  "x in B)
  $
  then $f^(-1) (emptyset) = emptyset$, $f^(-1)({0,1}) = X$, $f^(-1)({0})=A$ and $f^(-1)({1})=B$ are all open. So $f$ is continuous. Also since $A$ and $B$ are non-empty then $f$ is surjective.

  ($arrow.double.l$) Assume $f : X |-> {0,1}$ surjective and continuous, define $A = f^(-1) ({0})$ and $B = f^(-1) ({1})$. Then $A$ and $B$ disconnect $X$.
]

#thm[
  $[0,1]$ is connected.
]

Recall that in $RR$ every non-empty $A subset.eq [0,1]$ has a supremum.

#proof[
  Assume $A$ and $B$ disconnect $[0,1]$, and let $1 in B$. Since $A$ is non-empty $alpha = sup A$ exists. Then we have two options:

  1. $alpha in A$. Then $alpha < 1$ given $1 in B$. Since $A$ is open there is some $epsilon > 0$ with $B_epsilon (alpha) subset.eq A$. So $alpha + epsilon\/2 in A$, and thus $alpha$ is not a supremum of $A$.

  2. $alpha in.not A$, then $alpha in B$. Since $B$ is open there is some $epsilon > 0$ with $B_epsilon (alpha) subset.eq B$. Then $a <= alpha - epsilon$ for all $a in A$, and thus $alpha$ is not a least upper bound of $A$.

  Either way we find a contradiction, so $A$ and $B$ can't exist and $[0,1]$ is connected.

]

#proposition[
  If $f:X->Y$ is continuous and $X$ is connected, then $im f$ is also connected.
]
#proof[
  Assume $A$ and $B$ disconnect $im f$. We claim that $f^(-1) (A)$ and $f^(-1) (B)$ disconnect $X$.

  $A "and" B subset.eq im f$ are open, so $A = im f inter A'$ and $B = im f inter B'$ for some $A' "and" B'$ open in $Y$. Then $f^(-1) (A) = f^(-1) (A')$ and $f^(-1) (B) = f^(-1) (B')$ are open in $X$.

  $A "and" B$ are non-empty so $f^(-1) (A) "and" f^(-1) (B)$ are non-empty---and $f^(-1) (A) inter f^(-1) (B) = f^(-1) (A inter B) = f^(-1) (emptyset) = emptyset$. Now $A union B = im f$, and $f^(-1) (A) union f^(-1) (B) = f^(-1) (A union B) = X$.
]

Using this guy we can prove the intermediate value theorem.

#thm[Intermediate Value Theorem][
  Suppose $f: X -> RR$ is continuous and $X$ is connected. If there exists $x_0, x_1 in X$ such that $f(x_0) < 0 < f(x_1)$, then there exists some $x in X$ with $f(x)=0$.
]

#proof[
  Assume no such $x$ exists. Then $0 in.not im f$ while $0 > f(x_0) in im f$ and $0 < f(x_1) in im f$. Then $im f$ is disconnected---contradicting that $X$ is connected (contrapositive).
]

#corollary[
  If $f:[0,1] -> RR$ is continuous with $f(0) < 0 < f(1)$ then there exists some $x in [0,1]$ with $f(x) = 0$.
]

== Path Connectivity
#def[Path][
  Let $X$ be a topological space, and $x_0,x_1 in X$. Then a path from $x_0$ to $x_1$ is a continuous function $gamma: [0,1] |-> X$ such that $gamma(0) = x_0$ and $gamma(1) = x_1$.
]
We say a space is path connected if we can join any two points with a path.
#def[Path connectivity][
  A topological space $X$ is path connected if for all points $x_0,x_1 in X$ there is a path from $x_0$ to $x_1$.
]

#ex[

  1. $(a,b),[a,b),(a,b],RR$ are all path connected.

  2. $RR^n$ is path connected.

  3. $RR^n \\ {0}$ is path connected for $n > 1$, in this case we can _bend_ around the hole at $0$.
]

Importantly this is a stronger condition then normal connectivity.

#proposition[
  It $X$ is path connected, then $X$ is connected.
]

#proof[
  Let $X$ be path connected, and let $X -> {0,1}$ be a continuous function. We want to show that $f$ is constant.

  Let $x,y in X$. Then there is a map $gamma : [0,1] -> X$ with $gamma(0) = x$ and $gamma(1) = y$. By composition $f compose gamma:[0,1]->{0,1}$, and $[0,1]$ is connected so this map must be constant. In particular $f(gamma(0)) = f(gamma(1)) => f(x)=f(y)$. Given our choice of $x, y$ was arbitrary $f$ must be constant.

]

== Components
A disconnected space can be divided up into components, with each component being _maximally_ connected.

=== Path components
Path components are components with respect to path connectivity, we use the following lemma.
#lemma[
  Define $x tilde y$ if there is a path from $x$ to $y$ in $X$. Then $tilde$ is an equivalence relation.
]
#proof[

  1. For any $x in X$ let $gamma_x : [0,1] -> X$ be $gamma(t) = x$, i.e. the constant path. Then there is a path from $x$ to $x$ so $x tilde x$.

  2. If $gamma : [0,1] -> X$ is a path from $x$ to $y$ then $overline(gamma) : [0,1] -> X$ by $t |-> gamma(1-t)$ is a path from $y$ to $x$---i.e. the path in the opposite direction. So $x tilde y => y tilde x$.

  3. If $gamma_1$ is path from $x$ to $y$ and $gamma_2$ is a path from $y$ to $z$, then $gamma_2 * gamma_1$ defined by
  $
    t|-> cases(gamma_1 (2t) #h(35pt) & t in [0,1\/2], gamma_2 (2t -1) & t in [1\/2,1])
  $
  is a path from $x$ to $z$. So $x tilde y, y tilde z => x tilde z$.
]

Now we can define path components.
#def[Path components][
  Equivalence classes of the relation $x tilde y$ if there is a path from $x$ to $y$ are path components of $X$.
]

=== Connected components
Connected components are components with respect to _normal_ connectivity, we use the following.
#proposition[
  Suppose $Y_alpha subset.eq X$ is connected for all $alpha in T$ and that $inter.big_(alpha in T) Y_a eq.not emptyset$. Then $Y = union.big_(alpha in T) Y_alpha$ is connected.
]
#proof[
  Suppose $A$ and $B$ disconnect $Y$. Then $A$ and $B$ are open in $Y$. So $A = Y inter A'$ and $B = Y inter B'$ with $A'$ and $B'$ open in $Y$. For any $alpha$ let
  $
    A_alpha = Y_alpha inter A = Y_alpha inter A'",  " B_alpha = Y_alpha inter B = Y_alpha inter B'
  $
  then they are open in $Y_alpha$. Since $Y = A union B$ we have
  $
    Y_alpha = Y inter Y_alpha = (A union B) inter Y_alpha = A_alpha union B_alpha
  $
  since $A inter B = emptyset$ we have
  $
    A_alpha inter B_alpha = Y_alpha inter (A inter B) = emptyset
  $
  so $A_alpha$ and $B_alpha$ are disjoint. So $Y_alpha$ is connected, but also the disjoint union of open subsets $A_alpha$ and $B_alpha$. By definition of connectivity we require $A_alpha = emptyset$ or $B_alpha = emptyset$. By assumption $inter.big_(alpha in T) Y_alpha eq.not emptyset$ so pick $y in inter.big_(alpha in T) Y_alpha$. So $y in Y$ meaning either $y in A$ or $y in B$. Assume $y in A$, then $y in Y_alpha$ for all $alpha$ implies $y in A_alpha$ for all $alpha$. So $A_alpha$ is non-empty for all $alpha$. So $B_alpha$ is empty for all $alpha$. So $B = emptyset$.

  Then $A$ and $B$ don't disconnect $Y$---contradiction.
]

#def[Connected component][
  If $x in X$ define
  $
    cal(C) (x) = {A subset.eq X : x in A "and" A "is connected"}
  $
  then $C(x) = union.big_(A in cal(C) (x)) A$ is the connected component of $x$.
]

$C(x)$ is the largest connected subset of $X$
containing $x$. Note that ${x} in cal(C) (x)$ so $x in C(x)$, to see it is connected note that $x in inter.big_(A in cal(C) (x)) A$, so $inter.big_(A in cal(C) (x)) A$ is non-empty. By the previous proposition then it is also connected.

#lemma[
  If $y in C(x)$ then $C(y) = C(x)$.
]
#proof[
  Since $y in C(x)$ and $C(x)$ is connected $C(x) subset.eq C(y)$. So $x in C(y)$ then $C(y) subset.eq C(x)$. So $C(x)=C(y)$.
]

It follows that $x tilde y$ if $x in C(y)$ is an equivalence relation and the connected components of $X$ are the equivalence classes.

#proposition[
  If $U subset.eq RR^n$ is open and connected, then it is path-connected.
]

#proof[
  Let $A$ be a path component of $U$---we show it is open. Let $a in A$. Since $U$ is open there exists some $epsilon > 0$ such that $B_epsilon (a) subset.eq U$. We know that $B_epsilon (a) tilde.eq "Int"(D^n)$ is path-connected. Since $A$ is a path component and $a in A$ we must have $B_epsilon (a) subset.eq A$. So $A$ is an open subset of $U$.

  Assume $b in U\\A$ then since $U$ is open there exists some $epsilon > 0$ such that $B_epsilon (b) subset.eq U$. Since $B_epsilon (b)$ is path-connected, then if $B_epsilon (b) inter A eq.not emptyset$, then $B_epsilon (b) subset.eq A$. This implies $b in A$, which is a contradiction, so $B_epsilon (b) inter A = emptyset$. So $B_epsilon (b) subset.eq U \\A$. Then $U\\A$ is open.

  So $A$ and $U\\A$ are open disjoint subsets of $U$. Since $U$ is connected, we must have $U\\A$ empty, so $U = A$ is path-connected.
]

#pagebreak()
= Compactness
== Compactness
#def[Open cover][
  Let $cal(U) subset.eq PP(X)$ be a topology on $X$. An open cover of $X$ is a subset $cal(V) subset.eq cal(U)$ such that
  $
    union.big_(V in cal(V)) V = X
  $
  we say $cal(V)$ covers $X$.
]

If $cal(V)' subset.eq cal(V)$ and $cal(V)'$ covers $X$ we call $cal(V)'$ a subcover of $cal(V)$.

#def[Compact space][
  A topological space $X$ is compact if every open cover of $cal(V)$ of $X$ has a finite subcover $cal(V)' = {V_1, dots, V_n} subset.eq cal(V)$.
]

#ex[

  1. If $X$ is finite, then $PP(X)$ is finite. So any open cover of $X$ is finite. So $X$ is compact.

  2. Let $X = RR$ and $cal(V) = {(-R,R):R in R, R>0}$. Then this is an open cover with not finite subcover. So $RR$ is not compact. Hence all open intervals are not compact since they are homeomorphic to $RR$.

]

#thm[
  $[0,1]$ is compact.
]
#proof[
  Assume $cal(V)$ is an open cover of $[0,1]$. Let
  $
    A = {a in [0,1]:[0,a] "has a finite subcover of" cal(V)}
  $
  We first show that $A$ is non-empty. Since $cal(V)$ covers $[0,1]$ then there is some $V_0$ containing $0$. So ${0}$ has a finite subcover $V_0$, so $0 in A$. Note by definition if $0 <= b <= a$ and $a in A$, then $b in A$. Let $alpha = sup A$, and assume $alpha < 1$ then $alpha in [0,1]$.  Since $cal(V)$ covers $X$ let $alpha in V_alpha$. Since $V_alpha$ is open there is some $epsilon$ such that $B_epsilon (a) subset.eq V_alpha$. By definition of $alpha$ we have $alpha - epsilon\/2 in A$. So $[0,alpha-epsilon\/2]$ has a finite subcover. Add $V_alpha$ to that subcover to get a finite subcover of $[0,alpha+epsilon\/2]$. This is a contradiction---to be proper it will be a subcover of $[0,eta]$ with $eta = min(alpha+epsilon\/2, 1)$. Then we must have $alpha = sup A = 1$.

  Similarly there exists some $V_1 in cal(V)$ such that $1 in V_1$ and there exists some $epsilon > 0$ with $(1-epsilon,1] subset.eq V_1$. Since $1-epsilon in A$ there exists a finite $cal(V)' subset.eq cal(V)$ which covers $[0,1-epsilon\/2]$. Then $cal(W) = cal(V)' union {V_1}$ is a finite subcover of $cal(V)$.
]

#proposition[
  If $X$ is compact and $C$ is a closed subset of $X$, then $C$ is also compact.
]
#proof[
  We need to show that given an open cover of $C$ we can find a finite subcover. What we do is add $X\\C$ which is open. Then we can find a finite subcover of this since $X$ is compact, which can then be turned into a finite subcover of $C$.

  Assume $cal(V)$ is an open cover of $C$. Let $cal(V) = {V_alpha: alpha in T}$. For each $alpha$ since $V_alpha$ is open in $C$, $V_alpha = C inter V'_alpha$ for some $V'_alpha$ open in $X$. Also since $union.big_(alpha in T) V_a = C$, we have $C subset.eq union.big_(alpha in T) V'_alpha$.

  Since $C$ is closed $U=X\\C$ is open in $X$. So $cal(W) = {V'_alpha : alpha in T} union {U}$ is an open cover of $X$. Since $X$ is compact $cal(W)$ has a finite subcover $cal(W)' = {V'_alpha_1, dots V'_alpha_n,U}$. Now $U inter C = emptyset$. So ${V_alpha_1,dots,V_alpha_n}$ is a finite subcover of $C$.
]

#proposition[
  Let $X$ be Hausdorff. If $C subset.eq X$ is compact, then $C$ is closed in $X$.
]

=== Products & Quotients
== Sequential Compactness
== Completeness
