//**** init-ting
#import "@preview/physica:0.9.5": *
#import "chpt-temp.typ": *
#import "@preview/mannot:0.3.0": *
#import "@preview/cetz:0.4.1" // drawings

#show: thmrules.with(qed-symbol: $square$)
#show: chpt-note.with()

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
