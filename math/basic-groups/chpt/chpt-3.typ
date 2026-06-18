//**** init-ting
#import "@preview/physica:0.9.5": *
#import "chpt-temp.typ": *
#import "@preview/mannot:0.3.0": *
#import "@preview/cetz:0.4.1" // drawings

#show: thmrules.with(qed-symbol: $square$)
#show: chpt-note.with()


#pagebreak()
= Finite p-groups, Abelian-groups and Sylow Theorems
== p-groups
#def[$p$-group][
  A finite group $G$ is a $p$-group if $|G|=p^n$ for some prime $p$ and $n >= 1$.
]
#thm[
  If $G$ is a $p$-group, then $Z(G) = {x in G : x g = g x "for all" g in G}$ is non-trivial.
]
This basically tells us that for $n >= 2$ a $p$-group is never simple---since the center is normal.
#proof[
  Let $G$ act on itself by conjugation. The orbits of this action---the conjugacy classes---have order dividing $|G|=p^n$, by the orbit-stabilizer theorem. So it is either a singleton, or its size is divisible by $p$.

  The conjugacy classes partition $G$, so the total size of the conjugacy classes is $|G|$. In particular
  $
    |G| = \#"ccl with size" 1 + sum "order of all other ccl"
  $
  the second term is divisible by $p$, as we have already established. Also $|G|=p^n$ is divisible by $p$, so the number of conjugacy classes of size $1$ must also be divisible by $p$. We know ${e}$ is a conjugacy class of size $1$, so there is at least $p$ conjugacy classes of size $1$. The smallest $p = 2$, so there is a conjugacy class ${x} eq.not {e}$.

  If ${x}$ is a conjugacy class, then by definition $g^(-1) x g = x$ for all $g in G$, i.e. $x g = g x$ for all $g in G$---so $x in Z(G)$, i.e. $Z(G)$ is non-trivial.
]

#lemma[
  For any group $G$, if $G\/Z(G)$ is cyclic, then $G$ is Abelian.

  ---If $G\/Z(G)$ is cyclic then it is trivial, since the center of an Abelian group is the Abelian group itself.
]
#proof[
  Let $g in Z(G)$ be the generator of the cyclic group $G\/Z(G)$, then every coset of $Z(G)$ is of the form $g^r Z(G)$. Then every $x in G$ must be of the form $g^r z$ for some $z in Z(G)$ and $r in ZZ$. Let $overline(x) = g^overline(r) overline(z)$ be another element, with $overline(z) in Z(G), overline(r) in ZZ$. $z$ and $overline(z)$ both commute with everything, so
  $
    x overline(x) = g^r z g^overline(r) overline(z) = g^r g^overline(r) overline(z) z =g^overline(r) g^r overline(z) z = g^overline(r) overline(z) g^r z = overline(x) x
  $
  they commute---so $G$ is Abelian, and it follows that $Z(G) = G$.
]

#corollary[
  If $p$ prime and $|G|=p^2$, then $G$ Abelian.
]
#proof[
  Since $Z(G) <= G$ its order is $1, p$ or $p^2$. It is not trivial, per a previous theorem, so it is $p$ or $p^2$. If it has order $p^2$ then it is the whole group, and the group is Abelian---else $G\/Z(G)$ has order $p^2\/p=p$, but then it is cyclic, and thus $G$ is Abelian.
]

#thm[
  Let $G$ be a group of order $p^a$---then it has a subgroup of order $p^b$ for any $0 <= b <= a$.
]
#proof[
  We induct on $a$---if $a = 1$, then ${e}, G$ give subgroups of order $p^0$ and $p^1$.

  Suppose $a > 1$, and we want to construct a subgroup of order $p^b$---if $b=0$ this is trivial, ${e} <= G$ has order $p^0$. Otherwise $Z(G)$ is non-trivial, so let $x eq.not e in Z(G)$. Since $"ord"(x) | |G|$, its order is a power of $p$. If it has order $p^c$, then $x^p^(c-1)$ has order $p$. By renaming we then have $x$ with order $p$. So we have a subgroup $expval(x)$ of order $p$. And since $x$ is in the center, then $expval(x)$ commutes with everything in $G$. So $expval(x)$ is a normal subgroup of $G$---so $G\/expval(x)$ has order $p^(a-1)$, which is a strictly smaller group. If follows by induction that $G\/expval(x)$ has a subgroup of any order. In particular $G\/expval(x)$ has a subgroup of order $p^(b-1)$, let $H\/expval(x)$ denote this subgroup. Then $H$ is a subgroup of order $|expval(x)||H\/expval(x)|=p^b$.
]

== Abelian groups
These are essentially very nice and easy to classify---the proof will be presented later when we get to rings and modules.

#thm[Classification of finite Abelian groups][
  Let $G$ be a finite Abelian group. Then there is some $d_1, dots, d_r$ such that
  $
    G tilde.equiv C_d_1 times C_d_2 times dots times C_d_r
  $
  and we can pick $d_i$ such that $d_(i+1) | d_i$ for all $i$, and this is unique.
]

#ex[
  The Abelian groups of order $8$ are $C_8, C_4 times C_2, C_2 times C_2 times C_2$.
]

#lemma[Chinese remainder theorem][
  If $n$ and $m$ are coprime, then $C_(m n) tilde.equiv C_m times C_n$.
]
#proof[
  We have to find an element of order $n m$ in $C_m times C_n$---since it must be cyclic if this is the case.

  Let $g in C_m$ have order $m$ and $h in C_n$ have order $n$, and consider $(g,h) in C_m times C_n$. Let the order of $(g, h)$ be $k$. Then $(g, h)^k = (e, e) => (g^k, h^k) = (e, e)$. So the order of $g$ and $h$ divide $k$, and since they are coprime we must have $m n | k$.

  Since $k = "ord"((g,h))$ and $(g,h) in C_m times C_n$ is a group of order $m n$, we must have $k | n m$, so $k = n m$.
]

#corollary[
  For any finite Abelian group $G$, we have
  $
    G tilde.equiv C_d_1 times C_d_2 times dots times C_d_r
  $
  where each $d_i$ is some prime power.
]
#proof[
  Follows from the classification theorem and the chinese remainder theorem---breaking up each factor into prime powers.
]

== Sylow theorems
#thm[Sylow theorems][
  Let $G$ be a finite group of order $p^a dot m$, with $p$ prime, and $p$ coprime to $m$. Then

  1. the set of Sylow $p$-subgroups of $G$, given by
  $
    "Syl"_p (G) = {P <= G : |P|=p^a}
  $
  is non-empty---so $G$ has a subgroup of order $p^a$.

  2. All elements of $"Syl"_p (G)$ are conjugate in $G$.

  3. The number of Sylow $p$-subgroups $n_p = |"Syl"_p (G)|$ satisfies $n_p equiv 1 "(mod "p)$ and $n_p$ divides $|G|$---in particular $n_p$ divides $m$, since $p$ is not a factor of $n_p$.
]
Before proving these, we go through some applications.
#lemma[
  If $n_p = 1$ then the Sylow $p$-subgroup is normal in $G$.
]
#proof[
  Let the unique Sylow $p$-subgroup be $P$ and let $g in G$. Consider $g^(-1) P g$, this is isomorphic to $P$, since $phi(x) = g^(-1) x g$ is an isomorphism, so $abs(g^(-1) P g) = p^a$---i.e. it is a Sylow $p$-subgroup. Since $n_p=1$ it follows that $P = g^(-1) P g$. This also shows that for every Sylow $p$-subgroup, $g^(-1) P g$ is also a Sylow $p$-subgroup.
]

#corollary[
  Let $G$ be non-Abelian and simple. Then $abs(G)$ divides $n_p !\/2$ for every prime $p$ that divides $abs(G)$.
]
#proof[
  $G$ acts on $"Syl"_p (G)$ by conjugation. So it gives a permutation representation $phi: G arrow "Sym" ("Syl"_p (G)) tilde.equiv S_n_p$. We know $ker phi lt.tri G$, but $G$ is simple so $ker phi = {e}$ or $G$.

  If $ker phi = G$, then $g^(-1) P g = P$ for all $g in G$---so $P$ is normal, and since $G$ is simple we have $P={e}$ or $G$. $P$ can't be trivial since $p$ divides $abs(G)$. And if $G=P$ then $G$ is a $p$-group, and by a previous theorem it then has a non-trivial center, meaning it is not non-Abelian and simple---so we have $ker phi = {e}$.

  Then by the first isomorphism theorem $G tilde.equiv im phi <= S_n_p$. This is basically the theorem, to get the $1\/2$ we need to show $im phi <= A_n_p$. Consider the composition
  $
    G arrow.long^phi S_n_p arrow.long^"sgn" {plus.minus 1}
  $
  if this is surjective, then $ker("sgn" compose phi) lt.tri G$ (always) and has index $2$, it is then not the whole of $G$---i.e. $G$ is not simple. So the kernel must be $G$, and $"sgn" compose phi$ is the trivial map---so $"sgn" (phi(g)) = +1$, meaning $phi(g) in A_n_p$. We have
  $
    G tilde.equiv im phi <= A_n_p
  $
  and given that $abs(A_n_p) = n_p !\/2$ the theorem follows.
]

#ex[
  Consider $abs(G)=1000$, then $G$ is not simple. We can write $abs(G) = 2^3 dot 5^3$. Let $p = 5$, then $n_5 equiv 1 "(mod "5)$ and $n_5 divides 2^3 = 8$, per the third theorem. The only number satisfying both of these is $n_5 = 1$. So the Sylow $5$-subgroup is normal, hence $G$ is not simple.
]

#ex[
  Consider $abs(G) = 132 = 2^2 dot 3 dot 11$. Assume this is simple. Let $p = 11$, then $n_11 equiv 1 "(mod "11)$, and $n_11 divides 12$, as $G$ is simple we must have $n_11 = 12$, if $n_11 = 1$, then $G$ would not be simple.

  Let $p = 3$, then $n_3 equiv 1 "(mod "3)$ and $n_3 divides 44$, so the possible values are $n_3 = {4, 22}$. If $n_3 = 4$ then the previous corollary says $abs(G) divides 4!/2 = 12$, which is nonsense, so $n_3 = 22$.

  Now we count elements of each order---this is especially nice if $p divides abs(G)$ and $p divides.not abs(G)$, since then the Sylow $p$-subgroups would be cyclic. All Sylow $11$-subgroups are disjoint, apart from ${e}$, so there are $12 dot (11-1) = 120$ elements of order $11$. Similarly for the Sylow $3$-subgroups, here we need $22 dot (3-1) = 44$ elements of order $3$. This is more than the group has---so $G$ is not simple.
]

Now we prove the theorems.
#proof[
  Let $G$ be a finite group with $abs(G) = p^a m$ and $p divides.not m$.

  $(1)$. We need to show that $"Syl"_p (G) eq.not emptyset$, so we need to find some subgroup of order $p^a$. We let
  $
    Omega = {X subset.eq G : abs(X) = p^a}
  $
  so it's all subsets of $G$ with $p^a$ elements. We let $G$ act on $Omega$ by
  $
    g * {g_1, g_2, dots, g_(p^a)} = {g g_1, g g_2, dots, g g_(p^a)}
  $
  Let $Sigma <= Omega$ be an orbit. Note that if ${g_1, dots, g_(p^a)} in Sigma$, then for every $g in G$,
  $
    g g_1^(-1) * {g_1, dots, g_(p^a)} = (g, g g_1^(-1)g_2, dots, g g_1^(-1) g_(p^a)) in Sigma
  $
  by definition of the orbit---importantly this set contains $g$. So for every $g$, $Sigma$ contains at least one set $X$ with $g in X$. Each $X$ has size $p^a$, so to cover $G$ we must have
  $
    abs(Sigma) >= abs(G)/p^a = m
  $
  Assume $abs(Sigma) = m$. Then by the orbit-stabilizer theorem the stabilizer $H$ of any ${g_1, dots, g_(p^a)} in Sigma$ has index $m$, hence $abs(H) = p^a$, and thus $H in "Syl"_p (G)$.

  We need to show that not every orbit $Sigma$ can have size $>m$. Again by the orbit-stabilizer theorem the size of any orbit divides the order of the group, $abs(G) = p^a m$. So if $abs(Sigma) > m$, then $p divides abs(Sigma)$. Assume that $p divides.not Omega$, then not every orbit $Sigma$ can have size $> m$, since $Omega$ is the disjoint union of all orbits.

  So we need to show $p divides.not abs(Omega)$. We have
  $
    abs(Omega) = binom(abs(G), p^a) = binom(p^a m, p^a) = product_(j=0)^(p^a -1) = (p^a m - j)/(p^a - j)
  $
  the largest power of $p$ dividng $p^a m - j$ is the largest power of $p$ dividing $j$. Similarly for $p^a - j$. So the largest power of $p$ cancels. And the product is not divisible by $p$.

  $(2)$. We prove: if $Q <= G$ is a $p$-subgroup, so $abs(Q) = p^b$, and $P <= G$ is a Sylow $p$-subgroup, then there is a $g in G$ such that $g^(-1) Q g <= P$. Applying this to when $Q$ is another Sylow $p$-subgroup says there is a $g$ such that $g^(-1) G g <= P$, but since $abs(g^(-1) Q g) = abs(P)$ they must be the same group.

  We let $Q$ act on the set of cosets of $G\/P$ with
  $
    q * g P = q g P
  $
  the orbits of this action have size dividing $abs(Q)$, by the orbit-stabilizer theorem, so $1$ or divisible by $p$. They can't all be divisible by $p$, since $abs(G\/P)$ is coprime to $p$. So one of them must have size $1$, say ${g P}$. So for every $q in Q$, we have $q g P = g P$, meaning $g^(-1) q g in P$, for every $q$---so we just found a $g$ such that $g^(-1) Q g <= P$.

  $(3)$. We need to show $n_p equiv 1 "(mod "p)$ and $n_p divides abs(G)$, where $n_p = abs("Syl"_p (G))$.

  The second part is easiest. By the second Sylow theorem, the action of $G$ on $"Syl"_p (G)$ by conjugation has one orbit. Hence by the orbit-stabilizer theorem, the size of the orbit, which is $n_p = abs("Syl"_p (G))$, divides $abs(G)$.

  For the first part, let $P in "Syl"_p (G)$. Consider the action by conjugation of $P$ on $"Syl"_p (G)$. By the orbit-stabilizer theorem, the orbits have size $1$ or are divisible by $p$. We know one orbit with size $1$, namely ${P}$ itself. So show $n_p = abs("Syl"_p (G)) equiv 1 "(mod "p)$, it is enough to show there are no other orbits of size $1$. This is because the orbits partition $"Syl"_p (G)$ meaning
  $
    n_p = \#"orbits size "1 + \#"orbits"divides p
  $
  the second term vanishes when taking $"(mod "p)$, so
  $
    n_p equiv \#"orbits size "1 "(mod "p)
  $
  Assume ${Q}$ is an orbit of size $1$. Then for every $p in P$, we have
  $
    p^(-1) Q p = Q
  $
  or $P <= N_G (Q)$. Now the normalizer $N_G (Q)$ is itself a group, and we can consider its Sylow $p$-subgroups. We know $Q <= N_G (Q) <= G$. So $p^a divides abs(N_G (Q)) divides p^a m$. So $p^a$ is the biggest power of $p$ that divides $abs(N_G (Q))$, so $Q$ is a Sylow $p$-subgroup of $N_G (Q)$.

  We know $P <= N_G (Q)$ is also a Sylow $p$-subgroup of $N_G (Q)$. By the second theorem, they must be conjugate in $N_G (Q)$. But conjugating anything in $Q$ by something in $N_G (Q)$ does nothing, by definition of the normalizer. So $P = Q$. The only orbit of size $1$ is ${P}$ itself. And we are done.
]
