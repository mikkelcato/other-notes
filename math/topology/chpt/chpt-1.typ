//**** init-ting
#import "@preview/physica:0.9.5": *
#import "chpt-temp.typ": *
#import "@preview/mannot:0.3.0": *
#import "@preview/cetz:0.4.1" // drawings

#show: thmrules.with(qed-symbol: $square$)
#show: chpt-note.with()

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



