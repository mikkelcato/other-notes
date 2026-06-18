//**** init-ting
#import "@preview/physica:0.9.5": *
#import "chpt-temp.typ": *
#import "@preview/mannot:0.3.0": *
#import "@preview/cetz:0.4.1" // drawings

#show: thmrules.with(qed-symbol: $square$)
#show: chpt-note.with()

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


