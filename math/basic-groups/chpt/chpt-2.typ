//**** init-ting
#import "@preview/physica:0.9.5": *
#import "chpt-temp.typ": *
#import "@preview/mannot:0.3.0": *
#import "@preview/cetz:0.4.1" // drawings

#show: thmrules.with(qed-symbol: $square$)
#show: chpt-note.with()

#pagebreak()
= Quotient groups
== Normal subgroups
#def[Normal subgroup][
  A subgroup $K$ of $G$ is normal if for all $a in G$ and all $k in K$ we have $ a k a^(-1) in K $ we write $K lt.tri G$. This is equivalent to
  1. For all $a in G$ we have $a K = K a$.

  2. For all $a in G$ we have $a K a^(-1) = K$
]

Note that ${e} "and" G$ are always normal.

#lemma[
  1. Every subgroup of index $2$ is normal.

  2. Any subgroup of an Abelian group is normal.
]

#proof[
  1. If $K <= G$ has index $2$, then we have two distinct left cosets. One must be $K$ itself, with the other being $g K$ for some $g in.not K$. Similarly for the right cosets we have $K$ and $K g$. So we have $ {K, g K} = {K, K g} => g K = K g $ for all $g in G$.

  2. If $G$ Abelian then for any $a in G$ and $k in K$ we have $ a k a^(-1) = a a^(-1)k = k in K $
]

#thm[
  Every kernel is a normal subgroup.
]

#proof[
  Given $f: G arrow H$ and some $a in G$, for all $k in "ker"f$ we have $ f(a k a^(-1))=f(a)f(k)f(a)^(-1) = e => a k a^(-1) in "ker"f $ we also proved this when introducing the kernel.
]

#thm[
  A group of order $6$ is either cyclic or dihedral, i.e. $tilde.equiv C_6 "or" D_6$.
]

#proof[
  Let $|G| = 6$. By Lagrange's theorem the possible element orders are $1,2,3 "and" 6$. If we have some $a in G$ of order $6$ then $G = angle.l a angle.r tilde.equiv C_6$. Otherwise we only have elements of orders $2$ and $3$ other than $e$. Suppose every element has order $2$. We'll now show that such a group must have order $2^n$. Consider the minimal generating set of such a group $ S = {g_1,g_2,...g_n} "with" g_i^2=e $ since this is the minimal generating set any element of the set can be written as $g_1^(i_1)g_2^(i_2)dots g_n^(i_n)$ with $i_j = {0,1}$ since $g_i^2 = g_i^0=e "and" g_i^1 = g_i$. Thus the possible number of elements given this generating set is $2^n$. Since $|G| = 6$ which is not a power of $2$ then every element can't have order $2$. So some element $r$ must have order $3$, and further $angle.l r angle.r lt.tri G$ since it will have index $2$. And since the order of $|G|$ is even then it must have an element $s$ of order $2$. To see this let $|G|=2n$, consider the set $S$ of all elements $g in G$ with $g eq.not g^(-1)$, this set clearly has an even amount of elements---since every element pairs up with its inverse. Now consider all other elements, i.e. all $g in G$ with $g^2 = e$, we know this contains the identity. Now since $|G| "and" |S|$ are both even, then the rest must also be even, i.e. there must be at least one non-identity element satisfying $g^2=e$, i.e. one element of order $2$. $angle.l r angle.r$ is normal so $s r s^(-1) in angle.l r angle.r$. If $s r s^(-1) =e$ then $r = e$, which is not true. If $s r s^(-1) = r => s r = r s$, and $s r$ has order $6$ ($3 times 2$), which is not possible. Lastly if $s r s^(-1) = r^2 = r^(-1)$ then $G$ is dihedral by definition.

]

== Quotient groups
#thm[
  Let $K lt.tri G$, then the set of cosets of $K$ in $G$ is a group under the operation $a K * b K = (a b)K$.
]
#proof[
  We first show that the operation is well-defined. If $a K = a' K$ and $b K = b' K$ then we should have $a K * b K = a'K*b'K$. We know $a' = a k_1$ and $b' = b k_2$ for some $k_1, k_2 in K$. Then $a' b' = a k_1 b k_2$. We know $b^(-1)k_1 b in K$, so let $b^(-1)k_1 b = k_3 => k_1 b = b k_3$ giving $a'b' = a b k_3 k_2 in (a b)K$. So picking a different representative of the coset gives the same product, and thus the operation is well-defined. Now we prove the group axioms.

  0. If $a K, b K$ are cosets, then $(a b)K$ is also a coset.

  1. The identity is just $e K = K$.

  2. The inverse of $a K$ is just $a^(-1)K$.

  3. Associativity is inherited from $G$.
]

#def[Quotient group][
  Given $G$ and a normal subgroup $K$, the quotient or factor group of $G$ by $K$, written as $G\/K$, is the set of cosets of $K$ in $G$ under the operation $a K * b K = (a b)K$.
]
Note that the operation is not well-defined if $K$ is not normal.

#ex[
  1. Let $G = ZZ$ and $K = n ZZ$, which must be normal since $G$ is Abelian. The cosets are $k + n ZZ$ for $0 <= k < n$. The quotient group is $ZZ_n$ so we write $ZZ\/(n ZZ) tilde.equiv ZZ_n$. In fact these are the only quotient groups of $ZZ$, since $n ZZ$ are the only subgroups. To see why this is the case, note that we get $n$ cosets ${n ZZ, 1+ n ZZ, 2 + n ZZ,... (n-1) + n ZZ}$, under the group operation we would do e.g. $(2 + n ZZ) * ((n-1)+n ZZ) = (2 + (n-1))+n ZZ = (n+1)+n ZZ = 1+ n ZZ$, this is equivalent to addition mod $n$, so $ZZ\/(n ZZ) tilde.equiv ZZ_n$. Note that if $G$ is Abelian then $G\/K$ is automatically Abelian.

  2. Let $K = angle.l r angle.r lt.tri D_6$. We have get two cosets $K$ and $s K$. So $D_6 \/K$ has order $2$ and is $tilde.equiv C_2$.

  3. Take $K = angle.l r^2 angle.r lt.tri D_8$. From Lagrange's theorem we have $|G:K|=|G\/K|=(|G|)/(|K|)$, $K$ has order $2$ since $r^4 = e$ on $D_8$ and of course $|G|=8$ so $|G\/K|=4$. These are $ G\/K = {K, r K=r^3 K, s K = s r^2 K, s r K = s r^3 K} $ all elements except the identity have order $2$ so $G\/K tilde.equiv C_2 times C_2$, since it can't be cyclic.
  Note that quotient groups are not subgroups of $G$. And contain very different kinds of elements. Just in the first example $ZZ$ and $n ZZ$ are both infinite, but clearly $ZZ_n$ is finite.
]
For a non-example consider $D_6$ with $H = angle.l s angle.r$. This is not a normal subgroup. So we get $r H * r^2 H = r^3 H = H$, but also $r H = r s H$ and $r^2 H = s r H$ so $r s H*s r H = r^2 eq.not H$. Thus the operation is not well-defined.

#lemma[
  Given $K lt.tri G$ the quotient map $q:G arrow G\/K$ with $g |-> g K$ is a surjective group homomorphism.
]
#proof[
  $q(a b) = (a b)K = a K b K =q(a)q(b)$. So it is a homomorphism. And for all $a K in G\/K$, $q(a) = a K$ so it is surjective.
]

Note that the kernel of the quotient map is $K$, and thus any normal subgroup is a kernel of some homomorphism.

#thm[
  The quotient of a cyclic group is cyclic.
]

#proof[
  Let $G = C_n$ with $H <= C_n$, we know that $H$ is also cyclic. Say $C_n = angle.l c angle.r$ and $H = angle.l c^k angle.r tilde.equiv C_l$ with $k l = n$. We get $C_n \/ H = {H, c H, c^2 H, ... c^(k-1)H} = angle.l c H angle.r tilde.equiv C_k$.
]

== The Isomorphism Theorems
#thm[First Isomorphism Theorem][
  Let $f: G arrow H$ be a group homomorphism with kernel $K$. Then $K lt.tri G$ and $ G\/K tilde.equiv "im"f $ or $ G\/ker f tilde.equiv im f $
]

#proof[
  We have already proved that every kernel is a normal subgroup so $K lt.tri G$. Now we define a homomorphism $theta : G\/K arrow "im"f$ by $theta(a K)=f(a)$. We need to check that this guy is well-defined. If $a_1 K = a_2 K$ then $a_2^(-1)a_1 in K$. So $ f(a_2)^(-1)f(a_1)=f(a_2^(-1)a_1)=e => f(a_1)=f(a_2) => theta(a_1 K) = theta(a_2 K) $ Now we check that it is a homomorphism $ theta(a K b K) = theta(a b K) = f(a b) = f(a)f(b) = theta(a K)theta(b K) $ Now we want to show that it is bijective. To show it is injective suppose $theta(a K)=theta(b K) => f(a)=f(b) => f(b)^(-1)f(a)=e$ so $b^(-1)a in K$ so $a K = b K$. By definition it is surjective since $"im"theta = "im"f$, thus $theta$ is an isomorphism and $G\/K tilde.equiv "im"f <= H$.
]

If $f$ is injective, then we know the kernel is just ${e}$, so $G\/K tilde.equiv G$, and from the theorem we then have that $G$ is isomorphic to a subgroup of $H$, $G\/{e} tilde.equiv "im"f <= H$. If $f$ is surjective, then $"im"f = H$, so $G\/K tilde.equiv H$ by the theorem.

#ex[
  1. Let $f : "GL"_n (RR) arrow RR^*$ with $A|->"det"A$. Here $"ker"f = "SL"_n (RR)$. We have $"im"f = RR^*$ since for any $lambda in RR^*$ $"det"diagonalmatrix(lambda, 1, dots.down, 1) = lambda$. So by the isomorphism theorem we get $"GL"_n(RR)\/"SL"_n (RR) tilde.equiv RR^*$.

  2. Let $theta: (RR,+) arrow (CC^*,times)$ with $r |-> exp(2 pi i r)$. This is a homomorphism since $theta(r + s) = exp(2 pi i(r+ s))=exp(2 pi i r)exp(2 pi i s)=theta(r)theta(s)$. Clearly the kernel is $ZZ lt.tri RR$ and the image is the unit circle $(S_1, times)$. So by the isomorphism theorem $RR\/ZZ tilde.equiv (S_1,times)$.

  3. Let $G = (ZZ_p^*,times)$ for prime $p eq.not 2$.  We have $f : G arrow G$ with $a |-> a^2$. This is a homomorphism since $(a b)^2 = a^2 b^2$, due to $ZZ_p^*$ being Abelian. The kernel is ${plus.minus 1}={1,p-1}$ (remember we work in mod $p$), i.e. of order $2$. So by the isomorphism theorem we know $"im"f tilde.equiv G\/"ker"f$ with order $(p-1)/2$, these are known as quadratic residues.

  4. Since $A_n lt.tri S_n$ we find
  $
    S_n \/ A_n tilde.equiv im sgn = {plus.minus 1}
  $
  except for $n=1$, so $A_n$ has index $2$.
]

#lemma[
  Any cyclic group is isomorphic to either $ZZ$ or $ZZ\/(n ZZ)$ for some $n in NN$.
]

#proof[
  Let $G = angle.l c angle.r$. Define $f:ZZ arrow G$ with $m |-> c^m$. This is a homomorphism since $c^(m_1 + m_2)=c^(m_1)c^(m_2)$. $f$ is surjective since $G$ by definition is all $c^m$ for all $m$. We know that $"ker"f lt.tri ZZ$ (always the case). Three cases

  1. $"ker"f = {e}$, then $f$ is injective and thus bijective, so $G tilde.equiv ZZ$.

  2. $"ker"f = ZZ$, then $G tilde.equiv ZZ\/ZZ = {e} = C_1$

  3. $"ker"f = n ZZ$, since these are the only proper subgroups of $ZZ$, then $G tilde.equiv ZZ\/(n ZZ)$.
]

#thm[Second Isomorphism Theorem][
  Let $H <= G$ and $K lt.tri G$. Then $H K = {h dot k: h in H, k in K}$ is a subgroup of $G$, and $H inter K lt.tri H$. Moreover,
  $
    (H K) / K tilde.equiv H / (H inter K)
  $
]
#proof[
  First we prove $H K$ is a subgroup of $G$. Let $h k, h' k' in H K$, then
  $
    h' k' (h k)^(-1) = h' k' k^(-1) h^(-1) = (h' h^(-1))(h k' k^(-1) h^(-1))
  $
  the first term is in $H$, and the second is $k' k^(-1) in K$ conjugated by $h$, which is also in $K$ since it is a normal subgroup. So we have something in $H$ times something in $K$, so it is in $H K$. $H K$ also contains $e$, so it is non-empty and therefore a subgroup.

  Now we prove $H inter K lt.tri H$. Let $x in H inter K$ and $h in H$. Consider $h^(-1) x h$. Since $x in K$ normality of $K$ implies $h^(-1) x h in K$. Since $x, h in H$ closure implies $h^(-1) x h in H$, so $h^(-1) x h in H inter K$---note that any intersection of subgroups is trivially a subgroup, since in this case $a, b in H inter K => a, b in H, a, b in K => a b in H, a b in K => a b in H inter K$, and $a in H inter K => a in H, a in K => a^(-1) in H, a^(-1) in K => a^(-1) in H inter K$.

  Now we prove the theorem proper. We do this using the first isomorphism theorem, first define
  $
    phi : H & arrow G\/K \
          h & |-> h K
  $
  this is a homomorphism,
  $
    phi(h dot h') & = (h dot h' ) K \
                  & = h K h' K \
                  & = phi(h) phi(h')
  $
  We apply the first isomorphism theorem to this homomorphism. The image is all cosets $h K$ with $h in H$. So the $K$-cosets form a quotient group made from the group of all elements $h k in H K$, i.e.
  $
    im phi = (H K)/K
  $
  and the kernel is
  $
    ker phi = {h in H: h K = e K} = {h in H: h in K} = H inter K
  $
  so by the first isomorphism theorem
  $
    H/(H inter K) tilde.equiv (H K)/K
  $
]

This shows that we didn't really need to show that $H inter K$ is normal, since it must be a normal subgroup because it is a kernel.

#thm[Correspondence Theorem][
  If $K lt.tri G$ then there is a bijection between subgroups of $G\/K$ and subgroups of $G$ containing $K$, given by the quotient map $pi : G arrow G\/K, g |-> g K$:
  $
    {"subgroups of" G\/K} & <--> {"subgroups of" G "which contain" K} \
                 X <= G/K & --> {g in G : g K in X} \
               L/K <= G/K & <-- K lt.tri L <= G
  $
  this also works for normal subgroups
  $
    {"normal subgroups of" G\/K} <--> {"normal subgroups of" G "which contain" K}
  $
  with the same bijection.]
#proof[
  Let $X <= G\/K$. $X$ is a subgroup so it contains the identity $e K = K$, so $K = pi^(-1) ({K}) <= pi^(-1) (X)$. We check $pi^(-1) (X)$ is a subgroup. Let $a, b in pi^(-1) (X)$, then $pi(a) = a K in X, pi(b) = b K in X$. $X$ is a subgroup so $a K b K = (a b) K in X$, so $a b in pi^(-1) (X)$. Similarly $a K in X => (a K)^(-1) = a^(-1) K in X$ so $a^(-1) in pi^(-1) (X)$. Therefore $pi^(-1) (X) <= G$. So $pi^(-1) (X)$ is a subgroup of $G$ which contains $K$.

  Let $L <= G$ with $K lt.tri L$ then $L\/K = {g K : g in L} subset.eq G\/K$.
  $L\/K$ contains the identity $K$ since $e in L$. And is closed, and has inverses since $g K, h K in L\/K => (g K)(h K) = (g h) K in L\/K$ and $(g K)^(-1) = g^(-1) K in L\/K$, so $L\/K <= G\/K$.

  We want to show these are inverses. Let $X <= G\/K$ then
  $
    pi^(-1)(X) \/K = {g K : g in pi^(-1) (X)} = X
  $
  since by definition $g in pi^(-1) (X) <=> g K in X$. Let $L <= G$, $K lt.tri L$. Then
  $
    pi^(-1) (L\/K) = {g in G : g K in L\/K} = {g in G : g K = l K, l in L}
  $
  since $g K = l K$, this implies $l^(-1) g in K subset.eq L$, so
  $
    g = l(l^(-1) g) in L
  $
  so $pi^(-1) (L\/K) = L$
]

#thm[Third Isomorphism Theorem][
  Let $K <= L <= G$ be normal subgroups of $G$. Then
  $
    G/K \/ L/K tilde.equiv G/L
  $
]
#proof[
  Define the homomorphism
  $
    phi: G\/K & -> G\/L \
          g K & |-> g L
  $
  we check this is well-defined. If $g K = g' K$, then $g^(-1) g' in K subset.eq L$, so $g L = g' L$. It is a homomorphism since
  $
    phi (g K g' K) = phi (g g' K) = g g' L = g L g' L = phi(g K) phi(g' K)
  $
  this is surjective since any coset $g L$ is the image $phi (g K)$. This also makes the image $G\/L$. The kernel is
  $
    ker phi = {g K : g L = L} = {g K : g in L} = L\/K
  $
  then the theorem follows by the first isomorphism theorem.

]

#def[Simple group][
  A group is simple if it has no non-trivial proper normal subgroups, i.e. only ${e} "and" G$ are normal subgroups.
]

The simple groups are typically very annoying and complicated.
#ex[
  $C_p$ for prime $p$ are simple groups since it has no proper subgroups, and then by obviousness no normal ones.
]
The finite simple groups are what make up all finite groups, and all of these have been classified. If $K lt.tri G$ with $K eq.not G "or" {e}$ then we can quotient out $G$ into $G\/K$, if $G\/K$ is not simple, then just repeat. Then $G$ can be written as an inverse quotient of simple groups.

Since all Abelian groups have normal subgroups, these are only simple if they have no non-trivial subgroups at all.

#lemma[
  An Abelian group is simple if and only if it is isomorphic to the cyclic group $C_p$ for some prime $p$.
]
#proof[
  By Lagrange's theorem, any subgroup of $C_p$ has order dividing $|C_p| = p$. So if $p$ prime, then it has no divisors, and any subgroup must have order $1$ or $p$, i.e. it is either ${e}$ or $C_p$. So any normal subgroup must be ${e}$ or $C_p$---so it is simple.

  Now let $G$ be Abelian and simple. Let $e eq.not g in G$ be a non-trivial element, and consider $H = {dots, g^(-2), g^(-1), e, g, g^2, dots}$. Since $G$ Abelian, conjugation does nothing and every subgroup is normal. So $H$ is a normal subgroups. As $G$ is simple, $H = {e}$ or $H = {G}$. Since it contains $g eq.not e$ it is non-trivial. So we must have $H = G$. So $G$ is cyclic.

  If $G$ is infinite cyclic, then it is isomorphic to $ZZ$, but $ZZ$ is not simple, since $2 ZZ lt.tri ZZ$. So $G$ is a finite cyclic group, i.e. $G tilde.equiv C_m$ for some finite $m$. If $n$ divides $m$ then $g^(m\/n)$ generates a subgroup of $G$ of order $n$. This is a normal subgroup, so $n = {1, m}$. Hence $G$ cannot be simple unless $m$ has no divisors except $1$ and $m$, i.e. $m = p$.
]

#thm[
  Let $G$ be any finite group. Then there are subgroups
  $
    G = H_1 gt.tri H_2 gt.tri dots gt.tri H_n = {e}
  $
  such that $H_i \/ H_(i+1)$ is simple.
]

#proof[
  If $G$ simple, let $H_2 = {e}$ and we are done.

  If $G$ not simple, let $H_2$ be a maximal proper normal subgroup of $G$---we claim that $G \/ H_2$ is simple.

  If $G\/H_2$ not simple, then it has a non-trivial normal subgroup $L lt.tri G \/ H_2$ with $L eq.not {e}, G\/H_2$. But there is a correspondence between normal subgroups of $G\/H_2$ and normal subgroups of $G$ containing $H_2$, so $L$ must be $K\/H_2$ for some $K lt.tri G$ such that $K >= H_2$. Since $L$ is non-trivial and not $G\/H_2$, we know $K$ is not $G$ or $H_2$. So $K$ is a larger normal subgroup---this is a contradiction, thus $G\/H_2$ is simple.

  We can iterate this on $H_2$ to prove the theorem. This stops eventually since $H_(i+1) < H_i => |H_(i+1)| < |H_i|$ and all numbers are finite.
]
This theorem essentially says that we can always reduce a group into something simple.

#pagebreak()
= Group actions
== Definition
If $G <= "Sym"X$, then every $g in G$ should give us a permutation of $X$, in some consistent manner. We say that $G$ acts on $X$---this can be defined in multiple equivalent ways.
#def[Group action][
  An action of a group $(G, dot)$ on a set $X$ is a function
  $
    * : G times X arrow X
  $
  such that
  1. For all $x in X$ then $e * x =x$

  2. For all $g_1, g_2 in G$ and $x in X$ then $g_1 * (g_2 * x) = (g_1 dot g_2) * x$.
]

#lemma[
  An action of $G$ on $X$ is equivalent to a homomorphism $phi : G arrow "Sym"X$.
]
#proof[
  Let $* : G times X arrow X$ be an action. Define $phi : G arrow "Sym"X$ by sending $g$ to the function $phi(g) = (g * dot: X arrow X)$. This is a permutation, $g^(-1) * dot$ is an inverse
  $
    phi(g^(-1))(phi(g)(x)) = g^(-1) * (g * x) = (g^(-1) dot g) * x = e * x = x
  $
  similarly shows $phi(g) compose phi(g^(-1)) = "id"_X$, so $phi$ is well-defined.

  To show it is a homomorphism
  $
    phi(g_1)(phi(g_2)(x)) = g_1 * (g_2 * x) = (g_1 dot g_2) * x = phi(g_1 dot g_2)(x)
  $
  this is true for all $x in X$, so $phi(g_1) compose phi(g_2) = phi(g_1 dot g_2)$. And $phi(e)(x) = e * x = x$, so $phi(e)$ is the identity.

  Now we do the same backwards, given a homomorphism $phi : G arrow "Sym"X$, define $g*x = phi(g)(x)$. We check it is a group action. We know
  $
    g_1 * (g_2 * x) = phi(g_1)(phi(g_2)(x)) = (phi(g_1) compose phi(g_2))(x) = phi(g_1 dot g_2)(x) = (g_1 dot g_2) * x
  $
  and
  $
    e*x = phi(e)(x) = "id"_X (x) = x
  $
  so this homomorphism gives a group action.
]
This gives us the representation:
#def[Permutation representation][
  Let $X$ be a set and $G$ be a group. A permutation representation of $G$ is a homomorphism $phi:G arrow "Sym"X$.
]

We might write $G^X = im phi$ and $G_X = ker phi$, thus by the first isomorphism theorem:
#corollary[
  $G_X lt.tri G$ and $G\/G_X tilde.equiv G^X$.

  In particular if $G_X = {e}$ then $G tilde.equiv G^X <= "Sym"X$
]

#ex[
  1. Trivial action; for any $G$ acting on $X$ we can have $phi(g)=1_X$ for all $g in G$. So $G$ does nothing.

  2. $S_n$ acts on ${1,dots n}$ by permutation.

  3. $D_(2n)$ acts on the vertices of a regular $n"-gon"$

  4. The rotations of a cube act on the faces/vertices/diagonals/axes of the cube.

  Note that different groups can act on the same sets, and the same group can act on different sets.
]

#def[Kernel of action][
  The kernel of an action $G$ on $X$ is the kernel of $phi$, i.e. all $g$ such that $phi(g)=1_X$.
]

#ex[
  1. $D_(2n)$ acting on ${1,2 dots n}$ gives $phi:D_(2n) arrow S_n$ with kernel ${e}$. (since $S_n$ are the symmetries of ${1,2 dots n}$). Each element in $D_(2n)$ can be thought of as inducing a permutation of ${1,2,dots n}$, the collection of which is $S_n$, so some $g in D_(2n)$ gets mapped to a $g' in S_n$, though not necessarily all elements in $S_n$ have something mapped to them. The only $g in D_(2n)$ which doesn't permute any ${1,2 dots n}$ is $e$ so the kernel is ${e}$.

  2. Let $G$ be the rotations of a cube and let it act on the three axes $x,y,z$ through the faces. We have $phi: G arrow S_3$. Any rotation by $pi$ doesn't change the axes and thus act as the identity. So the kernel of the action has at least $4$ elements, $e$ and three $pi$ rotations. (each rotation induces a permutation in the axes, i.e. we permute ${x,y,z}$ or equivalently ${1,2,3}$ the set of all is then $S_3$). Considering the same $G$ instead acting on the faces, we get $phi:G arrow S_6$, with kernel ${e}$, since the only rotation that fixes all faces is the trivial rotation. Thus dependent on our chosen action we can study different properties of $G$, and how it changes different stuff.
]

#def[Faithful action][
  An action is faithful if the kernel is just ${e}$.
]

== Orbits and Stabilizers
#def[Orbit of action][
  Given an action $G$ on $X$, the orbit of an element $x in X$ is $ "orb"(x) = G(x) = G dot x = {g(x)=g*x in X:g in G} $ i.e. it is all the elements $g*x in X$ that $x$ can be sent to with the action $G$.
]
#def[Stabilizer of action][
  The stabilizer of $x$ is $ "stab"(x) = G_x = {g in G:g(x)=g*x=x} subset.eq G $ i.e. it is all elements in $G$ that leave $x$ alone.
]
#lemma[
  $"stab"(x) <= G$
]
#proof[
  By definition $e(x)=x$, so $"stab"(x) eq.not emptyset$. Now let $g, h in "stab"(x)$ then $g h^(-1)(x)=g(h^(-1)(x))=g(x)=x in "stab"(x)$, so $"stab"(x)$ is a subgroup.
]

#ex[
  1. Consider $D_8$ acting on the corners of the square $X = {1,2,3,4}$. Then $"orb"(1)=X$, since $1$ can be sent anywhere under rotations. And $"stab"(1)={e, "reflection in the line through "1}$.

  2. Consider the rotations of a cube acting on the $x,y,z$ axes. Then $"orb"(x)$ is everything, and $"stab"(x)={e, pi"-rotations and rotations about the" x"-axis."}$.
]

#def[Transitive action][
  An action $G$ on $X$ is transitive if for all $x$, $"orb"(x)=X$, i.e. every element can be sent to any element.
]

#lemma[
  The orbits of an action partition $X$.
]

#proof[
  For any $x$ we have $e(x)=x => x in "orb"(x) eq.not emptyset$. Now let $z in "orb"(x) "and" z in "orb"(y)$, then we need to show $"orb"(x)="orb"(y)$. We have $z = g_1(x) "and" z = g_2(y)$ for some $g_1,g_2$. Then $g_1(x)=g_2(y) => y = g_2^(-1)g_1(x)$. For any $w = g_3(y) in "orb"(y)$ we have $w = g_3 g_2^(-1)g_1(x)$ so $w in "orb"(x)$ and $"orb"(y) subset.eq "orb"(x)$, similarly $"orb"(x) subset.eq "orb"(y)$. So $"orb"(x)="orb"(y)$.
]

Consider a group $G$ acting on $X$, we fix some $x in X$. Then by definition given any $g in G$ we have $g(x) in "orb"(x)$. So every $g in G$ gives us a member of $"orb"(x)$. Likewise every object in $"orb"(x)$ arises this way by definition. But different elements in $G$ can give the same orbit. Consider $g in "stab"(x)$, then $h g$ and $h$ give the same object in $"orb"(x)$ since $h g(x) = h(g(x))=h(x)$. So we have a correspondence between things in $"orb"(x)$ and members of $G$ _up to_ $"stab"(x)$.

#thm[Orbit-stabilizer theorem][
  Let $G$ act on $X$, then there is a bijection between $"orb"(x)$ and cosets of $"stab"(x)$ in $G$. In particular if $G$ is finite then $ |"orb"(x)||"stab"(x)| = |G| $
]

#proof[
  We biject the cosets of $"stab"(x)$ with elements in the orbit of $x$. We call $G\/"stab"(x)$ the set of cosets of $"stab"(x)$ (not quotient group in this context). We define $ theta:(G\/"stab"(x)) & arrow "orb"(x) \
           g "stab"(x) & |-> g(x) $ this is well-defined, if $g "stab"(x)=h "stab"(x)$ then $h = g k$ for some $k in "stab"(x)$. So $h(x)=g(k(x))=g(x)$. This map is surjective since for any $y in "orb"(x)$ there is some $g in G$ such that $g(x)=y$, by definition. Then $theta(g "stab"(x))=y$. It is injective since if $g(x)=h(x)$ then $h^(-1)g(x)=x$, so $h^(-1)g in "stab"(x)$. So $g "stab(x)"=h"stab"(x)$. Thus it is a bijection. Since it is a bijection the number of cosets is $|"orb"(x)|$, and obviously the size of each coset is $|"stab"(x)|$. Then by Lagrange's theorem we immediately get the desired result.
]

This theorem is quite useful, and can be especially nice for determining group sizes, since we just need the orbit and stabilizer sizes for a single element.

#ex[
  1. Consider $D_(2n)$. $D_(2n)$ acts on ${1,2,3,dots,n}$ transitively so $|"orb"(1)|=n$. And $"stab"(1)={e, "reflection in the line through "1}$, so $|D_(2n)|=2 n$. Note that if the action is transitive as in this case then all orbits have size $|X|$ implying that all stabilizers have the same size.

  2. Let $angle.l (1 2) angle.r$ act on ${1,2,3}$. Then $"orb"(1)={1,2}$ and $"stab"(1)={e}$. And $"orb"(3)={3}$ with $"stab"(3)=angle.l (1 2) angle.r$.

  3. Consider $S_4$ acting on ${1,2,3,4}$. We know that $"orb"(1)=X$ and $|S_4|=4!=24$. So $|"stab"(1)|=24/4=6$, this makes our job easier if we want to find $"stab"(1)$. Obviously $S_{2,3,4} tilde.equiv S_3$ fix 1, so $S_{2,3,4} <= "stab"(1)$. However $|S_3|=6=|"stab"(1)|$, so this is the entire stabilizer.
]

== Important actions and conjugacy
#lemma[Left regular action][
  Any group $G$ acts on itself by left multiplication. This action is faithful and transitive.
]
#proof[
  We have
  1. For all $g in G$ and $x in G$ $g(x) = g dot x in G$ by definition of a group.
  2. For all $x in G$ $e dot x = x$.

  3. $g(h x) = (g h)x$ by associativity.

  So it is an action. It is faithful since the identity $g=e in G$ is unique. To show transitivity, for all $x,y in G$ then $(y x^(-1))(x) =y$, so all $x$ can be sent to any $y$.
]

#thm[Cayley's theorem][
  Every group is isomorphic to some subgroup of some symmetric group.
]
#proof[
  Take the left regular action of $G$ on itself, this give the homomorphism $phi : G arrow "Sym"G$ with $"ker"phi = {e}$, since this action is faithful. Then by the first isomorphism theorem $G tilde.equiv "im"phi <= "Sym"G$.
]

#lemma[Left coset action][
  Let $H <= G$, then $G$ acts on the left cosets of $H$ by left multiplication transitively---i.e. $X = G\/H$.
]

#proof[
  We show it is an action
  1. $g(a H) = (g a)H$ is a coset of $H$.
  2. $e( a H) = (e a)H = a H$.
  3. $g_1(g_2(a H)) = g_1((g_2 a)H) = (g_1 g_2 a)H = (g_1g_2)(a H)$
  Now given $a H$ and $b H$ we know $(b a^(-1))(a H) = b H$, so any $a H$ can be mapped to $b H$, and it is transitive.
]
Note that his reduces to the left regular action if $H = {e}$ since $G\/{e} tilde.equiv G$.

Consider $G_X = ker phi$ for the left coset action. If $g in G_X$, then for every $g_1 in G$, we have $g*g_1 H = g_1 H$ so $g_1^(-1) g g_1 in H$, or $g in g_1 H g_1^(-1)$. This is true for all $g_1 in G$ so
$
  G_X subset.eq inter.big_(g_1 in G) g_1 H g_1^(-1)
$
this is also reversible i.e. if $g in inter_(g_1 in G) g_1 H g_1^(-1)$ then for each $g_1 in G$ we have
$
  g_1^(-1) g g_1 in H => g g_1 H = g_1 H => g * g_1 H = g_1 H => g in G_X
$
so we get
$
  ker phi = G_X = inter.big_(g_1 in G) g_1 H g_1^(-1)
$
given this is a kernel it is also a normal subgroup of $G$ and is contained in $H$. Thus given any subgroup $H$, we can generate a normal subgroup, and this will be the biggest normal subgroup of $G$ in $H$.

#thm[
  Let $G$ be a finite group, and $H <= G$ a subgroup of index $n$. Then there is a normal subgroup $K lt.tri G$ with $K <= H$ such that $G\/K$ is isomorphic to a subgroup of $S_n$. Hence $|G\/K| | n!$ and $|G\/K| >= n$.
]
#proof[
  Using the previous we get $phi : G arrow "Sym" G\/H$, and let $K$ be the kernel of $phi$. We know $K <= H$, then by the first isomorphism theorem
  $
    G\/K tilde.equiv im phi <= "Sym" G\/H tilde.equiv S_n
  $
  with Lagrange's theorem giving us $|G\/K| | |S_n| = n!$, and $|G\/K| >= |G\/H| = n$
]
#corollary[
  Let $G$ be a non-Abelian simple group, let $H <= G$ be a proper subgroup of index $n$. Then $G$ is isomorphic to a subgroup of $A_n$. And we must have $n >= 5$, i.e. $G$ cannot have a subgroup of index less than $5$.
]
#proof[
  The actionn of $G$ on $X = G\/H$ gives a $phi : G arrow "Sym"X$. Then $"ker" phi lt.tri G$. Since $G$ is simple, the kernel is either ${e}$ or $G$.

  If it were $G$ then every element acts trivially on $X=G\/H$, but if $g in G\\H$, which exists, since the index of $H$ is not $1$, then $g * H = g H eq.not H$. So the kernel must be ${e}$.

  Then by the first isomorphism theorem we get
  $
    G tilde.equiv im phi <= "Sym"X tilde.equiv S_n
  $
  now we show it is a subgroup of $A_n$.

  We know $A_n lt.tri S_n$. So $im phi inter A_n lt.tri im phi tilde.equiv G$. Since $G$ simple, $im phi inter A_n$ is ${e}$ or $G = im phi$. If $im phi inter A_n = {e}$, then by the second isomorphism theorem
  $
    im phi tilde.equiv (im phi)/(im phi inter A_n) tilde.equiv (im phi A_n)/A_n <= S_n/A_n tilde.equiv C_2
  $
  so $G tilde.equiv im phi$ is a subgroup of $C_2$, i.e. ${e}$ or $C_2$. Both of these are Abelian, so this can not happen. Therefore $im phi inter A_n = im phi$, i.e. $im phi <= A_n$.

  The last part follows since $S_1, S_2, S_3$ and $S_4$ have no non-Abelian simple subgroups.
]

#def[Conjugation of element][
  The conjugation of $a in G$ by $b in G$ is $b a b^(-1) in G$. Given any $a$ and $c$, if there exists some $b$ such that $c = b a b^(-1)$. Then $a$ and $c$ are conjugate.
]
Conjugate elements can in some way be treated as the same.

#lemma[Conjugation action][
  Any group acts on itself by conjugation, $g(x) = g x g^(-1)$.
]

#proof[
  We have
  1. $g(x)=g x g^(-1) in G$ for all $g,x in G$.

  2. $e(x)=e x e^(-1) = x$.
  3. $g(h(x)) = g h x h^(-1) g^(-1) = (g h) x (g h)^(-1) = (g h)(x)$
]

These types of actions have corresponding isomorphisms from a group $G$ to itself, this natually leads to the automorphism group, which we'll just define here:
#def[Automorphism group][
  The automorphism group of $G$ is
  $
    "Aut"G = {f: G arrow G: f "is a group isomorphism"}
  $
  this is a group under composition, with the identity map as the identity.
]
This is of course a subgroup of $"Sym"G$ and $phi : G arrow "Sym"G$ by conjugation lands in $"Aut"G$.

#def[Conjugacy classes and centralizers][
  The conjugacy class of $g in G$ is the orbit of $g$ under the conjugation action
  $ "ccl"_G (g) = {h g h^(-1) : h in G} $
  and the centralizers are the stabilizers of the conjugation action, or all elements that commute with some $g$
  $ C_G (g) = {h in G : h g h^(-1) =g} = {h in G: h g = g h} $
]
For the whole group we can define
#def[Center of group][
  The center of $G$ is the elements that commute with all other elements
  $
    Z(G) = {h in G : h g h^(-1) = g "for all" g in G} = inter.big_(g in G) C_G (g) = "ker"phi
  $
]
#thm[
  Let $G$ be a finite group. Then
  $
    |"ccl"(x)| = |G : C_G (x)| = |G|\/|C_G (x)|
  $
]
#proof[
  By the orbit-stabilizer theorem, for each $x in G$ we have a bijection $"ccl" (x) <-> G\/C_G (x)$.
]

#lemma[
  Let $K lt.tri G$. Then $G$ acts by conjugation on $K$.
]
#proof[
  Pretty much everything is inherited by the conjugation action. We just need to show closure, which follows from the definition of a normal subgroup. For every $g in G$ and $k in K$ we have $g k g^(-1) in K$.
]

#thm[
  Normal subgroups are exactly those subgroups which are unions of conjugacy classes.
]
#proof[
  Let $K lt.tri G$. If $k in K$, then for every $g in G$ we have $g k g^(-1) in K$. So $"ccl"(k) subset.eq K$. So $K$ is the union of the conjugacy classes of all its elements.

  Likewise if $K$ is a union of conjugacy classes and a subgroup of $G$, then for all $k in K$ and $g in G$ we have $g k g^(-1) in K$. So $K$ is normal.
]

#lemma[
  Let $X$ be the set of subgroups of $G$, then $G$ acts by conjugation on $X$.
]
#proof[
  We have
  1. If $H <= G$ then we need to show that $g H g^(-1)$ is also a subgroup. If $e in H$ so $g e g^(-1) = e in g H g^(-1)$, so $g H g^(-1) eq.not emptyset$. For any two elements $g a g^(-1) "and" g b g^(-1) in g H g^(-1)$ we have $ (g a g^(-1))(g b g^(-1))^(-1) = g (a b^(-1))g^(-1) in g H g^(-1) $ so $g H g^(-1)$ is a subgroup.

  2. $e H e^(-1) = H$.

  3. $g_1(g_2 H g_2^(-1))g_1^(-1) = (g_1 g_2) H (g_1 g_2)^(-1)$.

  Thus it is an action. Note that the orbit is $ "orb"(H) = {g H g^(-1) : g in G} $ in the case of normal subgroups we have $H = g H g^(-1)$, so these are singleton $"orb"(H)={H}$.
]

#def[Normalizer of subgroup][
  The normalizer of a subgroup is the stabilizer of the conjugation action $ N_G (H) = {g in G : g H g^(-1) = H} $ we have $H subset.eq N_G (H)$. One can show that $N_G (H)$ is the largest subgroup of $G$ in which $H$ is a normal subgroup.
]
#proof[
  Want to show $N_G (H) <= G$. For $e in G$ we have $e H e^(-1) = H$ so $e in N_G (H) eq.not emptyset$. Let $a, b in N_G (H)$ then $(a b^(-1))H(a b^(-1))^(-1) = a b^(-1) H b a^(-1) = a H a^(-1) = H$ so $a b^(-1) in N_G (H)$, thus $N_G (H) <= G$.

  Want to show $H subset.eq N_G (H)$. Let $h in H$, we have $h H h^(-1) = H$, so $h in N_G (H)$, or $H subset.eq N_G (H)$.

  Want to show $H lt.tri N_G (H)$. We have just proved $H subset.eq N_G (H) <= G$, so $H <= N_G (H)$. $H$ is normal if $n h n^(-1) in H$ for all $n in N_G (H)$ and $h in H$. By definition we have $n H n^(-1) = H$, from which $n h n^(-1) in H$ follows. So $H lt.tri N_G (H)$. To show its the biggest subgroup with $H$ normal consider $K <= G$ with $H lt.tri K$ then for all $k in K$ we have $k H k^(-1) = H$, so $K subset.eq N_G (H)$. So $N_G (H)$ is the biggest subgroup of $G$ with $H$ normal.
]

#lemma[
  Stabilizers of the elements in the same orbit are conjugate. Let $G$ act on $X$ and $g in G$, $x in X$, then $"stab"(g(x))=g "stab"(x)g^(-1)$
]

#proof[
  Let $a in "stab"(g(x))$ then $         a (g(x)) & =g(x) \
          (a g)(x) & = g(x) \
  ( g^(-1)a g )(x) & = x $
  so $g^(-1) a g in "stab"(x) => a in g "stab"(x) g^(-1)$ so $"stab"(g(x)) subset.eq g "stab"(x) g^(-1)$, similarly one can show the other direction by letting $b = g a g^(-1)$ with $a in "stab"(x)$
  $ b(g(x)) =(g a g^(-1) g) (x) = (g a)(x) = g(x) $ so $b in "stab"(g(x))$ immediately giving $"stab"(x) subset.eq g^(-1)"stab"(g(x))g => g"stab"(x)g^(-1) subset.eq "stab"(g(x))$.
]
/*
== Applications
#ex[
  Let $G$ be a finite simple group of order greater than $2$, and $H <= G$ have index $n eq.not 1$. Then $|G| <= n!/2$
]
#proof[
  Consider the left coset action of $G$ on $H$. We get a homomorphism $phi : G arrow S_n$, since there are $n$ cosets of $H$. $H eq.not G$ so $phi$ is not trivial and $"ker"phi eq.not G$. Now $"ker"phi lt.tri G$, and since $G$ is simple $"ker"phi = {e}$. So $G tilde.equiv "im"phi subset.eq S_n$, meaning $|G| <= |S_n| = n!$.

  To get the $1/2$ we consider $"sgn" compose phi:G arrow {plus.minus 1}$. The kernel of this is normal in $G$, so $K = "ker"("sgn" compose phi) = {e}$ or $G$. Now $G\/K tilde.equiv "im"("sgn"compose phi)$, and $|G|\/|K| = 1 "or" 2$ since the image has at most two elements. For $|G|>2$ we can't have $K={e}$, else $|G|\/|K| > 2$, so we must have $K = G$, $"sgn"(phi(g))=1$ for all $g$ and $"im"phi <= A_n$. Giving $|G| <= n!/2$.

]

#thm[Cauchy's Theorem][
  Let $G$ be a finite group and prime $p$ dividing $|G|$. Then $G$ has an element of order $p$.
]
#proof[
  Let $G "and" p$ be fixed. Consider $G^p = G times G times dots times G$, the set of $p$-tuples. Let $X subset.eq G^p$ be $X = {(a_1,a_2,dots,a_p) in G^p : a_1a_2 dots a_p = e}$. Notice that if an element $b$ has order $p$ then $(b,b,dots,b) in X$, in fact if $b eq.not e$ and $(b,b,dots,b) in X$, then $b$ necessarily has order $p$. Now let $H = angle.l h : h^p = e angle.r tilde.equiv C_p$ be a cyclic group of order $p$ with generator $h$. Let $H$ act on $X$ by rotation
  $ h(a_1,a_2,dots,a_p) = (a_2,a_3,dots,a_p,a_1) $
  This is an action
  1. If $a_1 dots a_p = e$ then $a_1^(-1) =a_2 dots a_p$. So $a_2 dots a_p a_1 = a_1^(-1)a_1 = e$, and $(a_2,a_3,dots,a_p,a_1) in X$.

  2. $e$ acts an an identity by construction.

  3. Associativity also follows by construction.

  Orbits partition $X$, so the sum of all orbit sizes must be $|X|$. We have $|X| = |G|^(p-1)$, since we can freely chose the first $p-1$ entries, and the last will be their inverse. Since $p$ divides $|G|$ it also divides $|X|$. We have $|"orb"(a_1,dots,a_p)||"stab"_H (a_1,dots,a_p)| = |H|=p$. So all orbits have size $1$ or $p$, and they must sum to $|X| = "some number" times p$. We know one orbit of size $1$ $(e,e,dots,e)$. So at least $p-1$ other orbits of size $1$ must exist for the sum to be divisible by $p$. For this to be the case they must look like $(a,a,dots,a)$ for some $a in G$ which has order $p$.
]
*/
/*
#pagebreak()
= Symmetric groups cont.
We'll treat conjugacy classes of $S_n "and" A_n$.

== Conjugacy classes in $S_n$
Recall $sigma, tau in S_n$ are conjugate if there exists some $rho in S_n$ such that $rho sigma rho^(-1) = tau$.

#thm[
  If $(a_1 a_2 dots a_k)$ is a $k$-cycle and $rho in S_n$, then $rho (a_1 a_2 dots a_k) rho^(-1)$ is the $k$-cycle $(rho(a_1) rho(a_2) dots rho(a_3))$.
]

#proof[
  Consider any $rho(a_1)$ acted on by $rho (a_1 dots a_k) rho^(-1)$. It clearly gets sent to $ rho(a_1) |-> a_1 |-> a_2 |-> rho(a_2) $ likewise for other $a_i$. Since $rho$ is bijective, any $b$ can be written as $rho(a)$ for some $a$. So the result is the desired $k$-cycle.
]

#corollary[
  Two elements in $S_n$ are conjugate iff they have the same cycle type.
]

#proof[
  Let $sigma = sigma_1 sigma_2 dots sigma_l$ with $sigma_i$ being disjoint cycles. Then $rho sigma rho^(-1) = rho sigma_1 rho^(-1) rho sigma_2 rho^(-1) dots rho sigma_l rho^(-1)$, conjugation conserves cycle length so $rho sigma rho^(-1)$ has the same cycle type as $sigma$.

  Conversely if $sigma$ and $tau$ have the same cycle type,
  $ sigma = (a_1 a_2 dots a_k) (a_(k+1) dots a_(k + l)) "and" tau = (b_1 b_2 dots b_k)(b_(k+1)dots b_(k+l)) $ then letting $rho(a_i)=b_i$ gives $rho sigma rho^(-1) = tau$, by the previous.

]

This is quite powerful, now we can easily list all the conjugacy classes of $S_4$ for example
#align(center)[#table(
    columns: 5,
    stroke: 0pt,
    align: (left, center, center, center, left),
    table.hline(start: 0, stroke: 0.9pt),
    [Cycle type], [e.g element], [Size of ccl], [Size of centralizer], [Sign],
    table.hline(start: 0, stroke: 0.6pt),
    [$(1,1,1,1)$], [$e$], [$1$], [$24$], [$+1$],
    [$(2,1,1)$], [$(1 2)$], [$6$], [$4$], [$-1$],
    [$(2,2)$], [$(1 2)(3 4)$], [$3$], [$8$], [$+1$],
    [$(3,1)$], [$(1 2 3)$], [$8$], [$3$], [$+1$],
    [$(4)$], [$(1 2 3 4)$], [$6$], [$4$], [$-1$],
    table.hline(start: 0, stroke: 0.9pt),
  )]
We know that normal subgroups are unions of conjugacy classes, so we can find all normal subgroups by finding possible unions whose cardinality divides $24 = |S|_4$, as required by Lagrange's theorem, further they must contain $e$. This gives
+ Order $1$: ${e}$
+ Order $4$: ${e, (12)(34),(13)(24),(14)(23)} tilde.equiv C_2 times C_2 = V_4$.
+ Order $12$: $A_4$, which we know is normal since it's the kernel of $"sgn"$ or since it has index $2$.
+ Order $24$: $S_4$.

This also gives us the quotients: $S_4\/{e} tilde.equiv S_4$, $S_4\/V_4 tilde.equiv S_3 tilde.equiv D_6$, $S_4\/A_4 tilde.equiv C_2$ and $S_4\/S_4 = {e}$.

== Conjugacy classes in $A_n$
We know $|S_n| = 2 |A_n|$. We have
$
  "ccl"_(S_n)(sigma) &= {tau in S_n: exists rho in S_n, tau = rho sigma rho^(-1) } \
  "ccl"_(A_n)(sigma) &= {tau in A_n: exists rho in A_n, tau = rho sigma rho^(-1)}
$
clearly $"ccl"_(A_n) subset.eq "ccl"_(S_n)$, but the opposite is false, since the conjugation needed to map $sigma arrow tau$ might be odd, which would not be in $A_n$ (all even permutations). Instead we use orbit-stabilizer
$
  |S_n| & = |"ccl"_(S_n) (sigma)||C_(S_n) (sigma)| \
  |A_n| & = |"ccl"_(A_n) (sigma)||C_(A_n) (sigma)|
$
we have two options $"ccl"_(S_n) = "ccl"_(A_n)$ with $|C_(S_n)| = 1/2 |C_(A_n)|$ or $C_(A_n) = C_(S_n)$ with $1/2|"ccl"_(S_n)|=|"ccl"_(A_n)|$ or if we define
#def[Splitting of conjugacy classes][
  When $|"ccl"_(A_n) (sigma)| = 1/2 |"ccl"_(S_n) (sigma)|$, we say that the conjugacy class of $sigma$ splits in $A_n$
]
So the conjugacy classes are retained or split.

#thm[
  For $sigma in A_n$ the conjugacy class of $sigma$ splits in $A_n$ iff no odd permutation commutes with $sigma$.
]

#proof[
  We have conjugacy classes splitting iff the centralizer does not. So we check instead whether this happens. We have $C_(A_n) (sigma) = C_(S_n) (sigma) inter A_n$. If some odd permutation $tau$ commutes with $sigma$ then $tau in C_(S_n)(sigma)$, but $tau in.not A_n$ so the centralizer splits. Thus if there are no odd permutations, then the centralizer doesn't split, meaning the conjugacy class has to split.
]

So now it's simply a matter of finding the conjugacy classes for $S_n$, taking all the even ones, and then checking whether there is an odd element in $C_(S_4)$. If no odd elements then $"ccl"_(A_4)$ splits, e.g. $8 arrow 4,4$, otherwise it is the same as $"ccl"_(S_4)$. If $|C_(S_4)|$ is odd, then it can't split, since we can't have half elements -- in these cases the conjugacy class must split.

#lemma[
  $sigma = (1 2 3 4 5) in S_5$ has $C_(S_5) (sigma) = angle.l sigma angle.r$
]
#proof[
  $|"ccl"_(S_n) (sigma)| = 24$ and $|S_5| = 120$, so $|C_(S_5) (sigma)| = 5$. Clearly $angle.l sigma angle.r subset.eq C_(S_5) (sigma)$, and since they have the same size $C_(S_5) (sigma) = angle.l sigma angle.r$.
]

#thm[
  $A_5$ is simple.
]
#proof[
  Normal subgroups must be unions of conjugacy classes, and must contain $e$. Since $|A_5| = 60$, their order must divide $60$. The possible orders are thus $1,2,3,4,5,6,10,12,15,20,30$. The conjugacy classes have order $1,15,20,12,12$, these can't add up to any orders expect from $1$ and $60$, thus we only have trivial normal subgroups -- meaning $A_5$ is simple.

]
This turns out to be true for all $A_n$ with $n >= 5$, but the proof is ass---might add later\*.
*/

#pagebreak()
= Quaternions
Now we'll begin looking at some important groups.

#def[Quaternions][
  The quaternions is the following set of matrices
  $
    {mat(1, 0; 0, 1),mat(i, 0; 0, -i),mat(0, 1; -1, 0),mat(0, i; i, 0),mat(-1, 0; 0, -1),mat(-i, 0; 0, i),mat(0, -1; 1, 0),mat(0, -i; -i, 0)}
  $
  which is a subgroup of $"GL"_2 (CC)$.
]

We can write
$ Q_8 = angle.l a, b : a^4 = e, b^2 = a^2, b a b^(-1) = a^(-1) angle.r $
or
$ Q_8 = {1,-1,i,-i,j,-j,k,-k} $
with the usual rules for multiplying quaternions (e.g. $i j = k, i^2 =1, j i = -k$). These correspond to matrices as
$
  1 &= mat(1, 0; 0, 1), i = mat(i, 0; 0, -i), j=mat(0, 1; -1, 0), k = mat(0, i; i, 0) \
  -1 &= mat(-1, 0; 0, -1), -i = mat(-i, 0; 0, i), -j = mat(0, -1; 1, 0), -k=mat(0, -i; -i, 0)
$

#lemma[
  If $G$ has order $8$, then either $G$ Abelian ($tilde.equiv C_8, C_4 times C_2 "or" C_2 times C_2 times C_2$) or $G$ is not Abelian and isomorphic to $D_8$ or $Q_8$.
]
#proof[
  We consider every case

  + If $G$ contains an element of order $8$ then $G tilde.equiv C_8$

  + If all non-identity elements have order $2$, then $G$ is Abelian. Let $a eq.not b in G \\ {e}$. By the direct product theorem, $innerproduct(a, b) = angle.l a angle.r times angle.l b angle.r$. Take $c in.not innerproduct(a, b)$. By direct product theorem $angle.l a,b,c angle.r = angle.l a angle.r times angle.l b angle.r times angle.l c angle.r = C_2 times C_2 times C_2$. Since $angle.l a,b,c angle.r subset.eq G$ and $|angle.l a,b,c angle.r| = |G|$ then $G tilde.equiv C_2 times C_2 times C_2$.

  + $G$ has no element of order $8$ but has an order $4$ element $a in G$. Let $H = angle.l a angle.r$. Since $H$ has index $2$, it is normal in $G$. So $G \/ H tilde.equiv C_2$ since $|G \/ H| = 2$. For any $b in.not H$, $b H$ generates $G \/ H$. Then $(b H)^2 = b^2 H = H$, so $b^2 in H$. Since $b^2 in angle.l a angle.r$ and $angle.l a angle.r$ is cyclic then $b^2$ commutes with $a$. If $b^2 = a$ or $a^3$ then $b$ has order $8$, which is a contradiction, so $b^2 = e$ or $a^2$. We know $H$ is normal, so $b a b^(-1) in H$. Let $b a b^(-1) = a^l$. Since $a$ and $b^2$ commute we have $a = b^2 a b^(-2) = b ( b a b^(-1))b^(-1) = b a^l b^(-1) = (b a b^(-1))^l = a^(l^2)$. So $l^2 equiv 1 "(mod" 4)$ since $|angle.l a angle.r| = 4$. Then $l equiv plus.minus 1 "(mod" 4)$.

    + If $l equiv 1$ then $b a b^(-1) = a$, so $G$ is Abelian.

      - If $b^2 = e$, then $G = angle.l a,b angle.r tilde.equiv angle.l a angle.r times angle.l b angle.r tilde.equiv C_4 times C_2$

      - If $b^2 = a^2$, then $(b a^(-1))^2 = e$ so $G = angle.l a, b a^(-1) angle.r tilde.equiv C_4 times C_2$

    + If $l equiv -1$ then $b a b^(-1) = a^(-1)$.

      - If $b^2 = e$ then $G = angle.l a,b : a^4 = e = b^2, b a b^(-1) = a^(-1) angle.r$. So $G tilde.equiv D_8$

      - If $b^2 = a^2$ then $G tilde.equiv Q_8$.

    By exhaustion we are done.
]

#pagebreak()
= Matrix groups
== General and special linear groups
#def[General linear group $"GL"_n (F)$][
  $ "GL"_n (F) = {A in M_(n times n)(F):A "invertible"} $
  is the general linear group, i.e. all invertible matrices. (else no inverses)
]
#proof[
  Identity is just $I$ which is in $"GL"_n (F)$ by definition. Composition of invertible matrices is invertible so our group is closed, matrix multiplication is associative, and inverses exist by definition. So all group axioms are fulfilled.
]

#thm[
  $"det": "GL"_n (F) arrow F\\{0}$ is a surjective group homomorphism.
]

#proof[
  $"det"A B = "det"A "det"B$, and if $A$ invertible then $"det"A eq.not 0$, so $"det"A in F \\ {0}$. To show it is surjective take any $x in F\\{0}$, and replace $I_(11)$ with $x$ in the identity matrix. Then the determinant is $x$, so it is surjective.
]

#def[Special linear group $"SL"_n (F)$][
  The special linear group $"SL"_n (F)$ is the kernel of the determinant, i.e. (all invertible matrices with determinant $1$)
  $ "SL"_n (F) = {A in "GL"_n (F) : "det"A = 1} $
  so $"SL"_n (F) lt.tri "GL"_n (F)$ as it is a kernel. Note that $Q_8 <= "SL"_2 (CC)$.
]

== Actions of $"GL"_n (CC)$
#thm[
  $"GL"_n (CC)$ acts faithfully on $CC^n$ by left multiplication to the vector, with two orbits, $bold(0)$ and everything else.
]
#proof[
  We first show it is an action

  1. If $A in "GL"_n (CC)$ and $bold(v) in CC^n$ then $A bold(v) in CC^n$, so closure is satisfied.

  2. $I bold(v) = bold(v)$ for all $bold(v) in CC^n$.

  3. $A(B bold(v)) = (A B)bold(v)$.

  Now we prove that it is faithful. All linear maps are determined by what they do to the basis, so we take the standard basis $bold(e)_1 = (1,0,dots,0), dots bold(e)_n = (0,dots,1)$. Any matrix mapping every $bold(e)_k$ to itself must be $I$, since the columns of any matrix are the images of the basis vectors. Thus the kernel of the action is just the identity ${I}$.

  To show that there are two orbits, we know that $A bold(0) = bold(0)$ for all $A$, and because $A$ is invertible $A bold(v) = bold(0) <=> bold(v) = bold(0)$. So $bold(0)$ is a singleton orbit. Then given $bold(v) eq.not bold(w) in CC^n \\ {0}$, there is a matrix $A in "GL"_n (CC)$ such that $A bold(v) = bold(w)$, so everything else forms an orbit.

]
Similarly $"GL"_n (RR)$ acts on $RR^n$.

#thm[
  $"GL"_n (CC)$ acts on $M_(n times n) (CC)$ by conjugation.
]
#proof[
  This follows from properties of matrix multiplication.

  1. Let $A in "GL"_n (CC)$ and $B in M_(n times n) (CC)$. Then $A B A^(-1) in M_(n times n)$.

  2. $I B I^(-1) = B$.

  3. Let $C in "GL"_n (CC)$ then $C A B A^(-1) C^(-1) = (C A) B (C A)^(-1)$, with $C A in "GL"_n (CC)$, so its associative (compatible).
]

This action represents a "change of basis". Two matrices are conjugate if they represent the same map but with respect to different bases. $A$ is conjugate to a matrices of the forms
1. $mat(lambda, 0; 0, mu)$ with $lambda eq.not mu$.
2. $mat(lambda, 0; 0, lambda)$ repeated eigenvalue with $2$-dimensional eigenspace.
3. $mat(lambda, 1; 0, lambda)$ repeated eigenvalue with $1$-dimensional eigenspace.

== Orthogonal groups
$A$ is orthogonal if $A^(-1)=A^TT$, note we only care about $RR^n$. This can also be written as $A A^TT = I <=> a_(i k)a_(j k) = delta_(i j)$. These are notably isometries of $RR^n$.

#lemma[
  For any orthogonal $A$ and $x,y in RR^n$ we have
  1. $(A x) dot (A y) = x dot y$
  2. $|A x| = |x|$
]
#proof[
  We have $ (A x) dot (A y) = (A x)^TT (A y) = x^TT A^TT A y = x^TT y = x dot y $ and using this $|A x|^2 = (A x) dot (A x) = x dot x = |x|^2$, both are positive so $|A x|=|x|$.
]
Note that all isometries are orthogonal, but not all isometries are orthogonal. However all linear isometries can be represented by orthogonal matrices.

#def[Orthogonal group $"O"(n)$][
  The orthogonal group is $ "O"(n)="O"_n="O"_n (RR) = {A in "GL"_n (RR): A^TT A = I} $
  i.e. the group of orthogonal matrices.
]

#lemma[
  $"O"_n$ is a group.
]

#proof[
  We check that is a subgroup of $"GL"_n (RR)$. It is non-empty since $I in "O"_n$. Let $A, B in "O"_n$, then $(A B^(-1))(A B^(-1))^TT = A B^(-1) (B^(-1))^TT A^TT = A B^(-1) B A^TT = I$, so $A B^(-1) in "O"_n$. So we have $"O"_n <= "GL"_n (RR)$.
]

#thm[
  $"det": "O"_n arrow {plus.minus 1}$ is a surjective group homomorphism.
]
#proof[
  Let $A in "O"_n$ we know $A^TT A = I$. So $"det" A^TT A = ("det"A)^2 = 1$. So $"det"A=plus.minus 1$. Since $"det"(A B)="det"A "det"B$ it is a homomorphism. We have $ "det"I = 1",  " "det"dmat(-1, 1, dots.down, 1) = -1 $
  so it is surjective.
]

#def[Special orthogonal group $"SO"_n$][
  The special orthogonal group is the kernel of $"det": "O"_n arrow {plus.minus 1}$. So all orthogonal matrices with determinant $1$. $ "SO"(n)="SO"_n = "SO"_n (RR) = {A in "O"(n) : "det"A = 1} $
]
By the isomorphism theorem $"O"_n \/ "SO"_n tilde.equiv C_2$. Matrices with determinant $-1$ that we might want to avoid are reflections.

#lemma[
  $ "O"_n = "SO"_n union dmat(-1, 1, dots.down, 1) "SO"_n $
]
#proof[
  Cosets partition the group, so the union of the two cosets is just the group.
]

== Rotations and reflections in $RR^2$ and $RR^3$
#lemma[
  $"SO"(2)$ consists of all rotations of $RR^2$ around $0$.
]

#proof[
  Let $A in "SO"(2)$. So $A^TT A = I$ and $"det"A = 1$. Let $A = mat(a, b; c, d)$. Then $A^(-1) = mat(d, -b; -c, a)$. So $A^TT = A^(-1)$ implies $a d - b c = 1$ and $c=-b, d=a$. Combining these give $a^2 +c^2 = 1$ letting $a = cos theta = d "and" c = sin theta = - b$. These satisfy everything so $ A = mat(cos theta, - sin theta; sin theta, cos theta) $
  $A$ maps $(1,0)$ to $(cos theta, sin theta)$ and $(0,1) = (- sin theta, cos theta)$, which are rotations by $theta$ counterclockwise. So $A$ represents a rotation by $theta$.
]

#corollary[
  Any matrix in $"O"(2)$ is either a rotation around $0$ or a reflection in a line through $0$.
]

#proof[
  If $A in "SO"(2)$ then this a rotation. Otherwise $ A=mat(1, 0; 0, -1)(cos theta, - sin theta; sin theta, cos theta) = mat(cos theta, -sin theta; - sin theta, - cos theta) $ since $"O"(2) = "SO"(2) union mat(1, 0; 0, -1) "SO"(2)$. This has eigenvalues $1, -1$, so it is a reflection in the line of the eigenspace $E_1$. The line goes through $bold(0)$ since the eigenspace is a subspace which must include $bold(0)$.
]

#lemma[
  Every matrix in $"SO"(3)$ is a rotation around some axis.
]

#proof[
  Let $A in "SO"(3)$. We know $"det"A = 1$, and $A$ is an isometry. The eigenvalues must have $|lambda|=1$, and should multiply to $"det"A = 1$. We work in $RR$ so complex eigenvalues come in conjugate pairs, $lambda overline(lambda) = |lambda|^2 = 1$, the third eigenvalue must be $1$. If all are real, then we have $1,1,1 "or" -1,-1,1$. We pick an eigenvector for $lambda = 1$ as the third basis vector. Then in some orthonormal basis $ A = mat(a, b, 0; c, d, 0; 0, 0, 1) $ Since the third column is the image of the third basis vector, and by orthogonality the third row is $0,0,1$. Now let $ A' = mat(a, b; c, d) in "GL"_2 (RR) $ with $"det"A'=1$. $A'$ is still orthogonal so $A' in "SO"(2)$. Thus $A'$ is a rotation and $ A = mat(cos theta, - sin theta, 0; sin theta, cos theta, 0; 0, 0, 1) $
  in some basis. This is exactly a rotation about some axis.
]

#lemma[
  Every matrix in $"O"(3)$ is the product of at most three reflections in planes through $0$.
]

Two reflections correspond to a rotation, so all matrices in $"O"(3)$ is a reflection, a rotation or a product of a reflection and a rotation.

#proof[
  Recall $"O"(3) = "SO"(3) union dmat(1, 1, -1) "SO"(3)$ so if $A in "SO"(3)$ then $ A = mat(cos theta, - sin theta, 0; sin theta, cos theta, 0; 0, 0, 1) $ in some basis, which is a composite of two reflections $ A = dmat(1, -1, 1)mat(cos theta, sin theta, 0; sin theta, - cos theta, 0; 0, 0, 1) $ so if $A in dmat(1, 1, -1)"SO"(3)$ then it is automatically a product of three reflections.
]

== Unitary groups
We extend the previous to complex matrices. We define the hermitian conjugate $ A^dagger = (A^*)^TT $ a matrix is unitary if $A^dagger = A^(-1)$.

#def[Unitary group $"U"(n)$][
  The unitary group is $ "U"(n) = "U"_n = {A in "GL"_n(CC): A^dagger A = I} $
]

#lemma[
  $"det": "U"(n) arrow S^1$, with $S^1$ the unit circle in the complex plane, is a surjective homomorphism.
]

#proof[
  We know $1 = "det"I = "det"(A^dagger A) = |"det"A|^2$. So $|"det"|A=1$ (unit circle). Since $"det"(A B) = "det"A "det"B$, it is a homomorphism. Given $lambda in S_1$ we have $dmat(lambda, 1, dots.down, 1) in "U"(n)$ so it is surjective.
]

#def[Special unitary group $"SU"(n)$][
  The special unitary group $"SU"(n)="SU"_n$ is the kernel of $"det""U"_n arrow S_1$, i.e. all matrices with determinant $1$.
]

Unitary matrices preserve the complex dot product. $( A x) dot (A y) = x dot y$.

/*
#pagebreak()
= Regular polyhedra
== Symmetries of the cube
We have $|G^+| = 24$ rotations by the orbit-stabilizer theorem.

#thm[
  $G^+ tilde.equiv S_4$ where $G^+$ is the group of all rotations of the cube.
]

#proof[
  Consider $G^+$ acting on the diagonals. This gives $phi : G^+ arrow S_4$. We have $(1 2 3 4) in "im"phi$ by rotation around the axis through the top and bottom face. Also $(12) in "im"phi$ by rotation around the axis through the mid-point of the edge connecting $1$ and $2$. These generate $S_4$ so $"im"phi = S_4$, i.e. $phi$ is surjective. Since $|S_4|=|G^+|$ then $phi$ must be an isomorphism.
]

Other than rotations we can also do reflections in the mid-point of the cube. This commutes with all other symmetries.

#thm[
  $G tilde.equiv S_4 times C_2$ where $G$ is the group of all symmetries of the cube.
]

#proof[
  Let $tau$ be reflection. We have to show that $G = G^+ angle.l tau angle.r$. $G^+$ and $tau$ only intersect at $e$, so by the direct product theorem we get an injective homomorphism $G^+ times angle.l tau angle.r arrow G$. Both sides have the same size, so it must be surjective. Thus $G tilde.equiv G^+ times angle.l tau angle.r tilde.equiv S_4 times C_2$.
]

== Symmetries of tetrahedron \*
By orbit-stabilizer it's trivial to find $|G^+| = 4 dot 3 = 12$, by acting with $G^+$ on the vertices. The action gives a homomorphism $phi:G^+ arrow S_4$. $"ker"phi = {e}$ so $G^+ <= S_4$ and $G^+$ has size $12$. The only subgroup of $S_4$ with order $12$ is $A_4$. So $G^+ tilde.equiv A_4$, so no rotation just swaps two vertices.

We have some additional symmetries in the form of reflections, this ends up giving $G tilde.equiv S_4$ (stab $arrow 6$; orb $arrow 4$), since we can essentially permute all vertices while still being a tetrahedron.
*/
/*
#pagebreak()
= Möbius group
== Möbius maps
We study maps $f : CC arrow CC$ of the form $f(z) = (a z + b)/(c z + d)$ with $a,b,c,d in CC$ and $a d - b c eq.not 0$ (else it's boring). If $c eq.not 0$ then $f(-d/c)$ has division by $0$, to get around this we add $oo$ to $CC$ giving the Riemann sphere $CC union {oo} = CC_oo$. We then define $f(-d/c) = oo$. $C_oo$ is a one-point compactification.

#def[Möbius map][
  A Möbius map is a map from $C_oo arrow C_oo$ of the form $ f(z) = (a z+ b)/(c z + d) $
  with $a,b,c,d in CC$ and $a d - b c eq.not 0$. If $c eq.not 0$ then $f(-d/c)=oo "and" f(oo) = a/c$, if $c = 0$ then $f(oo) = oo$.
]

#lemma[
  The Möbius maps are bijections $C_oo arrow C_oo$.
]
#proof[
  The inverse is $ g(z)=(d z-b)/(-c z + a) $ which is easily checked by composition.
]
#thm[
  The Möbius maps form a group $M$ under composition.
]
#proof[
  0. If $f_1 = (a_1 z + b_1)/(c_1 z + d_1) "and" f_2 = (a_2 z + b_2)/(c_2 z+ d_2)$ then $ f_2 compose f_1 = ((a_1a_2+b_2c_1)z+(a_2b_1+b_2d_1)z)/((c_2a_1+d_2c_1)z+(c_2b_1+d_1d_2)z) in M $ (we have to check $a b - b c eq.not 0$ etc. but this stinks)

  1. The identity is $1(z) = (1 z + 0)/(0 +1)$.

  2. We know $f^(-1) = (d z - b)/(-c z + a)$ with $d a - b c eq.not 0$.

  3. Composition is associative.
]

$M$ is not abelian. $oo$ is not special on the Riemann sphere, but from our definition we typically have to treat these cases differently.

#thm[
  The map $theta: "GL"_2 (CC) arrow M$ sending $mat(a, b; c, d) |-> (a z+b)/(c z + d)$ is a surjective homomorphism.
]

#proof[
  This works because the determinant $a d-b c eq.not 0$ for all $A in "GL"_2 (CC)$, so it is surjective. And we showed before that $theta(A_2) compose theta(A_1) = theta(A_2 A_1)$ so it is a homomorphism.

]

The kernel of $theta$ is
$ "ker"theta = {A in "GL"_2 (CC): "for all" z, z = (a z + b)/(c z + d)} $
or $ "ker"theta = Z = {lambda I: lambda in CC, lambda eq.not 0} $
with $Z$ the center of $"GL"_2 (CC)$ by the isomorphism theorem $ M tilde.equiv "GL"_2(CC) \/ Z $

#def[Projective general linear group $"PGL"_2(CC)$][
  The projective general linear group is $ "PGL"_2(CC) = "GL"_2(CC)\/Z $
]

We have $f_A = f_B$ iff $B = lambda A$, if we restrict $theta$ to $"SL"_2 (CC)$ we have $theta|_("SL"_2 (CC)):"SL"_2(CC) arrow M$, is also surjective with kernel ${plus.minus I}$. So $ M tilde.equiv "SL"_2 (CC) \/ {plus.minus I} = "PSL"_2(CC) $ from which we get $"PSL"_2 (CC) tilde.equiv "PGL"_2 (CC)$, since both are isomorphic to $M$.

Note the Möbius map can be composed from simple elementary maps, but this is quite boring so won't be noted.

== Fixed points of Möbius maps
#def[Fixed point][
  A fixed point of $f$ is a $z$ such that $f(z)=z$.
]

Any map with $c = 0$ fixes $oo$.

#thm[
  Any Möbius map with at least three fixed points must be the identity.
]

#proof[
  $f(z) = z => c z^2 + (d - a)z - b = 0$. A quadratic has at most two roots, unless $c = b = 0$ and $d = a$, in which case $f$ is just the identity.
]
*/

