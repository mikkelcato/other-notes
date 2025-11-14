//**** init-ting
#import "@preview/physica:0.9.5": *
#import "chpt-temp.typ": *
#import "@preview/mannot:0.3.0": *
#import "@preview/cetz:0.4.1" // drawings

#show: thmrules.with(qed-symbol: $square$)
#show: chpt-note.with()

#pagebreak()
= Groups and Homomorphisms
== Groups
#def[Binary operation][

  A binary operation is a way of combining two elements to get a new element. Formally, it is a map $* : A times A ->A$]

#def[Group][
  A group is a set $G$ with a binary operation $*$ satisfying
  + There is some $e in G$ such that for all $a in G$
    $ a * e = e*a=a $

  + For all $a in G$ there is some $a^(-1) in G$ such that
    $ a*a^(-1)=a^(-1)*a=e $

  + For all $a,b,c in G$ we have
    $ a*(b*c)=(a*b)*c $

  Some include the closure axiom, (but this follows since $*$ is a binary operation.)

  0. For all $a,b in G$ we have $a*b in G$
]
#def[Order of group][
  The order of a group $G$ denoted $|G|$ is the number of elements in $G$. A group is finite if $|G|$ is finite.
]

#def[Abelian group][
  A group $G$ is Abelian if it is commutative, i.e for all $a,b in G$.
  $ a * b = b * a $
]
Many groups turn out to be Abelian, in the following we'll denote groups as $(A,*)$, with $A$ the set and $*$ the binary operation.
#ex[
  The following are Abelian groups
  + $(ZZ, +)$

  + $(QQ, +)$
  + $(ZZ_n,+_n)$, integers $"mod" n$
  + $(QQ,times)$
  + $({-1,1},times)$
  The following are non-Abelian groups
  + $(D_(2n), "composition")$

  + $("GL"_2(RR), "matrix"times)$
  + symmetries of 3D objects.
]

Now we'll state and prove our first theorems.
#thm[
  Let $(G,*)$ be a group. Then
  + The identity is unique.

  + Inverses are unique.
]

#proof[
  + Let $e "and" e'$ be identities. Then $e e' = e'$ and $e e' = e$ so immediately $e' = e$.

  + Let $a^(-1) "and" b$ be inverses for some $a in G$. Then $ b=b e = b ( a a^(-1)) = (b a)a^(-1) = e a^(-1) = a^(-1) $
    so $b = a^(-1).$
]

#thm[
  Let $(G,*)$ be a group and $a,b in G$. Then
  + $(a^(-1))^(-1) = a$

  + $(a b)^(-1) = b^(-1)a^(-1)$
]

#proof[
  + Given $a^(-1)$, then both $a "and" (a^(-1))^(-1)$ satisfy $ x a^(-1) = a^(-1)x = e $
    then since inverses are unique we immediately get $(a^(-1))^(-1)=a$

  + We have $ a b (b^(-1)a^(-1)) & = a (b b^(-1))a^(-1) \
                       & = a e a^(-1) \
                       & = a a^(-1) \
                       & = e $
    doing the same we can find $(b^(-1)a^(-1))a b = e$, so $b^(-1)a^(-1)$ is an inverse of $a b$. By uniqueness it is the only inverse so $(a b)^(-1) = b^(-1)a^(-1)$
]

We like to derive things from other things, so naturally we want to be able to derive groups from other groups. This gives us the concept of subgroups.

#def[Subgroup][
  A $H$ is a subgroup of $G$, written $H <= G$ if $H subset.eq G$ and $H$ with the operation $*$ inherited from $G$ is also a group.
]

#ex[
  + $(ZZ,+) <= (QQ,+) <= (RR,+) <= (CC,+)$

  + $(e, *) <= (G,*)$ referred to as the trivial subgroup

  + $G <= G$

  + $({plus.minus 1}, times) <= (QQ,times)$
]

Proving that $H$ is actually a subgroup of $G$ is annoying using our definition. But we can deduce simple criteria to decide if $H$ is a subgroup.

#lemma[Subgroup criteria 1][
  Let $(G, *)$ be a group and $H subset.eq G$. $H <= G$ iff for all $a, b in H$
  + $e in H$

  + $a b in H$

  + $a^(-1) in H$
]

#proof[
  The group axioms are satisfied as follows
  0. Closure follows from 2.

  1. Existence of an identity follows from 1. Further $H "and" G$ have the same identity. Let $e_H "and" e_G$ be identities of $H "and" G$. Then $e_H e_H = e_H$. Now, $e_H$ has an inverse in $G$ by definition, so $ e_H e_H e_H^(-1) & =e_H e_H^(-1) \
             e_H e_G & = e_G \
                 e_H & = e_G $

  2. Existence of inverses follow from 3.
]

This can be made even simpler.

#lemma[Subgroup criteria 2][
  A subset $H subset.eq G$ is a subgroup of $G$ iff for all $a, b in H$
  + $H$ is non-empty

  + $a b^(-1) in H$
]

#proof[
  Both 1. and 2. are immediately implied by the previous theorem. To prove the other direction we have

  + $H$ has at least one element $a$. Then $a a^(-1) = e in H$.

  + $e, a in H$ so $e a^(-1) = a^(-1) in H$

  + $a, b^(-1) in H$ so $a(b^(-1))^(-1) = a b in H$
]

To end this section we'll prove a cool fact.

#thm[
  The subgroups of $(ZZ,+)$ are exactly $n ZZ$ for $n in NN$.
]

#proof[
  It's easy to show that for any $n in NN$, $n ZZ$ is a subgroup. We'll show that these are the only subgroups. Let $H <= ZZ$, we know $0 in H$. If there are no other elements in $H$, then let $H = 0 ZZ$, else pick the smallest positive integer $n$, then $H = n ZZ$. Now we'll proceed by contradiction. Suppose that there exists some $a in H$ with $n divides.not a$. Then we can write $a = p n + q$ with $0 < q < n$. Now since $a in H$ we have $a - p n = q in H$. But $q < n$, so $n$ is not the smallest member of $H$, this is a contradiction. So every $a in H$ is divisible by $n$. Then by closure we must have $H = n ZZ$.
]

== Homomorphisms
We want to define functions between groups.

#def[Function][
  Given sets $X "and" Y$, a function $f:X arrow Y$ sends each $x in X$ to a particular $f(x) in Y$. $X$ is the domain of $f$, and $Y$ is the co-domain.
]

#ex[
  - Identity function: for any $X$, $1_X:X arrow X$ with $1_X (x)=x$ is a function. Also written as $"id"_X$.

  - Inclusion map: $cal(i):ZZ arrow QQ$ with $cal(i)(n)=n$, this is not the same as $"id"_Z$, since the domain and codomain are different.

  - $f_1:ZZ arrow ZZ$ with $f_1(x)=x+1$

  - $f_2: ZZ arrow ZZ$ with $f_2(x)=2x$

  - $f_3: ZZ arrow ZZ$ with $f_3(x)=x^2$

  - For $g:{0,1,2,3,4} arrow {0,1,2,3,4}$, we have
    - $g_1(x)=x+1$ if $x < 4$ and $g_1(4)=4$

    - $g_2(x)=x+1$ if $x < 4$ and $g_2(4)=0$
]

#def[Composition][
  The composition of two functions is a function we get by applying one after another. If $f:X arrow Y$ and $g:Y arrow Z$ then $g circle.tiny f:X arrow Z$ with $g circle.tiny f(x)= g(f(x))$
]

#ex[
  $f_2 circle.tiny f_1(x) = 2x+2$, and $f_1 circle.tiny f_2(x) = 2x+1$. Evidently not commutative.
]

#def[Injective][
  A function $f$ is injective if it hits everything at most once, i.e for all $x,y in X$
  $ f(x)=f(y) => x = y $
]

#def[Surjective][
  A function $f$ is surjective if it hits everything at least once, i.e for all $y in Y$ there is some $x in X$ such that
  $ f(x)=y $
]

#def[Bijective][
  A function is bijective if it is injective and surjective. A function has an inverse iff it is bijective.
]

#ex[
  $cal(i) "and" f_2$ are injective. $f_3 "and" g_1$ are neither. $1_X, f_1 "and" g_2$ are bijective.
]

#lemma[
  The composition of two bijective functions is bijective.
]

#proof[
  _obvious_

]

If we are talking about sets, functions can get very weird. But in group theory we are interested in functions that preserve group structure or at least respect it. These we call homomorphisms.

#def[Homomorphism][
  Let $(G,*) "and" (H,times)$ be groups. A function $f: G arrow H$ is a group homomorphism iff for all $g_1, g_2 in G$
  $ f(g_1)times f(g_2)=f(g_1*g_2) $
  or preferably
  $ f(g_1 * g_2)=f(g_1) times f(g_2) $
  this shows how homomorphisms preserve group structure. Doing the operation and then transforming, or first transforming each element and then performing the new group operation gives the same thing.
]

#ex[
  Consider $f:(RR^+,times) arrow (RR,+)$ given by $f = log(x)$. We have for $x_1,x_2 in (RR^+,times)$
  $ log(x_1 times x_2)=log(x_1)+ log(x_2) $
  which follows from the laws of exponentials. Also consider $f: (RR,+) arrow (RR^+,times)$ given by $f=e^x$. For $x_1,x_2 in (RR,+)$ we have
  $ e^(x_1 + x_2)=e^(x_1) times e^(x_2) $
]

#def[Isomorphism][
  Isomorphisms are just bijective homomorphisms, e.g. those in the previous example. If one exists between two groups they are isomorphic and we write $G tilde.equiv H$
]

We'll treat isomorphic groups as the same group, since we only really care about the structure not the specific elements. Now we'll prove some theorems.

#thm[
  Let $f:G arrow H$ be a homomorphism. Then
  + $f(e_G) = e_H$

  + $f(a^(-1))=f(a)^(-1)$

  + The composite of two group homomorphisms is a group homomorphism.

  + The inverse of an isomorphism is an isomorphism.
]

#proof[
  1. $
                 f(e_G) & = f(e_G^2) = f(e_G)^2 \
      f(e_G)^(-1)f(e_G) & = f(e_G)^(-1) f(e_G)^2 \
                    e_H & = f(e_G)
    $

  2. $ e_H = f(e_G) = f(a a^(-1)) = f(a) f(a^(-1)) $
    since inverses are unique we then have $f(a)^(-1) = f(a^(-1))$

  3. Let $f:G_1 arrow G_2$ and $g: G_2 arrow G_3$. Then $ g(f(a b)) = g(f(a)f(b)) = g(f(a))g(f(b)) $

  4. Let $f: G arrow H$ be an isomorphism. Then $ f^(-1)(a b) & = f^(-1){f(f^(-1)(a))f(f^(-1)(b))} \
                & = f^(-1) {f(f^(-1)(a)f^(-1)(b))} \
                & = f^(-1)(a)f^(-1)(b) $
    so $f^(-1)$ is a homomorphism, and since it is bijective, then it is an isomorphism.
]

#def[Image of homomorphism][
  If $f:G arrow H$ is a homomorphism, then the image of $f$ is
  $ "im"f = f(G)={f(g):g in G} $
]
#def[Kernel][
  The kernel of $f$ is every $g in G$ that gets sent to the identity $e_H$
  $ "ker"f = f^(-1)({e_H}) = {g in G: f(g) = e_H} $
]

#thm[
  The image and kernel are subgroups of their respective groups, i.e. $"im"f <= H$ and $"ker"f <= G$.
]

#proof[
  We have $e_H = f(e_G) in "im"f$ and $e_G in "ker"f$, so both are non-empty.
  Let $b_1,b_2 in "im"f$, then there exists $a_1, a_2 in G$ such that $f(a_1)=b_1 "and" f(a_2)=b_2$. Then $ b_1 b_2^(-1) = f(a_1)f(a_2^(-1)) =f(a_1 a_2^(-1)) in "im"f $
  since $a_1 a_2^(-1) in G$, so $"im"f <= H$. Now pick $b_1, b_2 in "ker"f$ then $ f(b_1 b_2^(-1)) = f(b_1)f(b_2)^(-1) =e^2 = e $
  so $b_1 b_2^(-1) in "ker"f$, so $"ker"f <= G$.

]

An important type of subgroup are normal subgroups, these are related to the following, but we'll talk about these later.

#thm[
  Given any $f:G arrow H$ and any $a in G$, then for all $k in "ker"f$ we have $a k a^(-1) in "ker"f$
]

#proof[
  $ f(a k a^(-1))=f(a)f(k)f(a)^(-1) =f(a)f(a)^(-1)=e $
  so $a k a^(-1) in "ker"f$
]

#thm[
  For all $f:G arrow H$, $f$ is
  1. surjective iff $"im"f = H$

  2. injective iff $"ker"f = {e}$
]

#proof[
  1. This is simply the definition of being surjective.

  2. We know $f(e)=e$. If $f$ is injective then by definition we have $"ker"f = {e}$. If $"ker"f = {e}$ then pick $a,b$ such that $f(a)=f(b)$. Then $ f(a b^(-1)) = f(a)f(b)^(-1)=e $ so $a b^(-1) in "ker"f = {e}$. So $a b^(-1) = e => a = b$. So $f(a)=f(b) => a = b$, and $f$ is injective.
]

These definitions will prove useful later on.

== Cyclic groups
These are the simplest groups.
#def[Cyclic group $C_n$][
  A group $G$ is cyclic if there is an $a in G$ for all $b in G$ and there exists some $n in ZZ$ such that
  $ b = a^n $
  i.e. all $b in G$ can be written as a power of a single $a in G$. This $a$ is called the generator.
]
We write $C_n$ for the cyclic group of order $n$.

#ex[
  1. $(ZZ,+)$ is cyclic with generator $1 "or" -1$. This is the infinite cyclic group.

  2. $({plus.minus 1},times)$ is cyclic with generator $-1$.

  3. $(ZZ_n, +)$ is cyclic with all numbers being coprime to $n$ as generators.
]

Given a group $G$ and $a in G$ we often just write $expval(a)$ for the cyclic group generated by $a$. This is the smallest subgroup containing $a$.

#def[Order of element][
  The order of an element $a$ is the smalles $n in ZZ$ such that $a^n = e$. If $n$ does not exist then $a$ has infinite order. We write $"ord"(a)$.
]

The following lemma relates our different definitions of order.

#lemma[
  For $a in G$ $ "ord"(a) = |expval(a)| $
]

#proof[
  If $"ord"(a) = oo$ then $a^n eq.not a^m$ for all $n eq.not m$, else $a^(m-n)=e$. Thus $|expval(a)|=oo="ord"(a)$.

  If $"ord"(a)=k$ then $a^k = e$, we claim $expval(a)={e,a^1,a^2,...a^(k-1)}$ since $a^k = e$, and higher powers will loop back. Lastly there are no repeating elements since $a^m = a^n => a^(m-n)=e$. Thus we are done and $|expval(a)|=k$.
]

#thm[
  Cyclic groups are Abelian.
]

#proof[
  Let $a in G$ be a generator for $expval(a)$. Take $a^m, a^n in expval(a)$ for some $m, n in ZZ$. Then $a^m a^n = a^(m+n) = a^(n+m)=a^n a^m$.
]

#def[Exponent of group][
  The exponent of a group $G$ is the smallest $n in ZZ$ such that $a^n = e$ for all $a in G$.
]

== Dihedral groups
#def[Dihedral groups $D_(2n)$][
  Dihedral groups are the symmetries of a regular $n"-gon"$. It has $n$ rotations, including the identity and $n$ reflections, i.e. $2n$ elements. We write $D_(2n)$ with $2n$ being the order.
]

How can we represent this group? All rotations are generated by $r = (2pi)/n$, with $"ord"(r)=n$. Any reflection has order 2, let $s$ be our favorite, then any other can be written as a product of $r^m "and" s$ for some $m$. We also have $s r s = r^(-1)$. Thus we can write
$
  D_(2n) & = angle.l r, s bar r^n = s^2 = e, s r s=r^(-1) angle.r \
         & = {e, r, r^2, ... r^(n-1), s, r s, r^2 s,...r^(n-1)s}
$
so it is generated by $r "and" s$ with the extra "conditions" $r^n=s^2=e "and" s r s^(-1) = s r s = r^(-1)$.

== Direct products of groups
For sets we have $X times Y = {(x,y):x in X, y in Y}$. For groups we do the same.

#def[Direct product of groups][
  Given $(G, circle.tiny)$ and $(H, circle.filled.tiny)$ we define $G times H = {(g,h): g in G, h in H}$ and the operation $(a_1,a_2) * (b_1,b_2) = (a_1 circle.tiny b_1, a_2 circle.filled.tiny b_2)$. This forms a group.
]
Why do this? Imagine if we have one system with symmetries and want to combine it with another independent system then this is how we'd do it.

#ex[
  Two triangles would give the group $D_6 times D_6$.

  $
    C_2 times C_2 & = {(0,0),(0,1),(1,0),(1,1)} \
                  & = {e, x, y, x y} \
                  & = angle.l x, y bar x^2 = y^2 = e, x y = y x angle.r
  $
]

#thm[
  $C_n times C_m tilde.equiv C_(n m)$ iff $"hcf"(m,n)=1$.
]

#proof[
  Suppose $"hcf"(m,n) = 1$. Let $C_n = angle.l a angle.r "and" C_m = angle.l b angle.r$. Let $k$ be the order of $(a,b)$ such that $(a,b)^k = (a^k,b^k)=e$, so $k$ must be a common multiple of $m$ and $n$. $k$ is also the smallest such value, so $k = "lcm"(m,n) = (n m)/("hcf"(m,n)) = n m$. Now consider $angle.l (a,b) angle.r <= C_n times C_m$, $(a,b)$ has order $n m$ so $angle.l (a,b) angle.r$ has $n m$ elements. Since $C_n times C_m$ also has $n m$ elements, then $angle.l (a,b) angle.r$ must be the whole $C_n times C_m$. And we have $angle.l (a,b) angle.r tilde.equiv C_(n m)$ so $C_n times C_m tilde.equiv C_(n m)$.
  For the other direction assume that $"hcf"(m,n) eq.not 1$. Then $k = "lcm"(m,n) eq.not m n$. So for any $(a,b) in C_n times C_m$  we have $(a,b)^k=(a^k,b^k) = e$, so the order is at most $k < n m$, so no element has order $n m$ and thus $C_n times C_m$ is not a cyclic group of order $n m$.

]

It is sometimes useful to write complicated groups as products of other groups.

#thm[Direct product theorem][
  Let $H_1, H_2 <= G$, suppose the following are true
  1. $H_1 inter H_2 = {e}$.

  2. For all $a_i in H_i$: $a_1 a_2 = a_2 a_1$.

  3. For all $a in G$ there exists some $a_i in H_i$ such that $a = a_1 a_2$, or $G = H_1H_2$.
  Then $G tilde.equiv H_1 times H_2$.
]

#proof[
  Let $f: H_1 times H_2 arrow G$ be $f(a_1,a_2) = a_1 a_2$. This is a homomorphism since $ f((a_1,a_2)*(b_1,b_2)) & = f(a_1 b_1, a_2 b_2) \
                         & = a_1 b_1a_2b_2 \
                         & = a_1 a_2 b_1 b_2 \
                         & = f(a_1,a_2)f(b_1,b_2) $
  Now we want to show that this is bijective. Surjectivity follows from 3. We can show injectivity by showing $"ker"f = {e}$. If $f(a_1,a_2) = e$ then $a_1a_2=e$ so $a_1 =a_2^(-1)$. Now $a_1 in H_1$ and $a_2^(-1) in H_2$ so $a_1=a_2^(-1) in H_1 inter H_2 = {e}$. So $a_1 = a_2 = e$, and then $"ker"f = {e}$

]

#pagebreak()
= Symmetric group
When we talk about symmetries we mean bijections. Any arbitrary bijection $X arrow X$ is a symmetry of $X$. The set of all bijections form a group, namely the symmetric group.

#def[Permutation][
  A permutation of $X$ is a bijection $X arrow X$. The set of all permutations on $X$ is $"Sym"X$.
]
#thm[
  $"Sym"X$ with composition forms a group.
]
#proof[
  This is trivial.

  0. If $sigma: X arrow X$ and $tau: X arrow X$ then $sigma circle.tiny tau:X arrow X$. If both are bijections, then the composite is also bijective. So if $sigma, tau in "Sym"X$ then $sigma circle.tiny tau in "Sym"X$.

  1. $1_X : X arrow X$ is a permutation and is our identity.

  2. All bijective functions have bijective inverses. So if $sigma in "Sym"X$ then $sigma^(-1) in "Sym"X$.

  3. Composition of functions is associative.
]

#def[Symmetric group $S_n$][
  If $X$ is finite, $|X| = n$ and typically $X = {1,2,...,n}$, we let $"Sym"X = S_n$. This is the symmetric group of degree $n$.
]

#def[Permutation group][
  A group $G$ is a permutation group if it is a subgroup of $"Sym"X$ for some $X$. We say $G$ is of order $n$ if $|X|=n$.

  Pretty much all groups turn out to be isomorphic to some permutation group.
]

Note that degree and order of $S_n$ aren't the same thing, since the order would refer to the number of permutations and not the order of $X$, in general $S_n$ would have order $n!$.

/*
We can write permutations in a couple of ways. One way is two row notation
$ mat(1, 2, 3, dots, n; sigma(1), sigma(2), sigma(3), ..., sigma(n)) $
#ex[
  For small $n$
  1. $n=1$, $S_n = {mat(1; 1)} = {e} tilde.equiv C_1$.

  2. $n=2$, $S_n = {mat(1, 2; 1, 2),mat(1, 2; 2, 1)} tilde.equiv C_2$

  3. $n=3$, $S_n = {mat(1, 2, 3; 1, 2, 3),mat(1, 2, 3; 2, 3, 1),mat(1, 2, 3; 3, 1, 2),mat(1, 2, 3; 2, 1, 3),mat(1, 2, 3; 3, 2, 1),mat(1, 2, 3; 1, 3, 2)} tilde.equiv D_6$
  note that $S_3$ is not Abelian which implies that $S_n$ is not Abelian for $n => 3$ since $S_3$ can be treated as a subgroup of $S_n$ by fixing $4,5,6,dots,n$.
]
In general $D_(2n) <= S_n$ since each symmetry is a permutation of corners. Another notation is cycle notation written as $(1 2 3)$, $(1 2)(3)=(1 2)$, $(12)(34)$, $(123)^(-1)=(321)=(132)$, $(1234)(14)$, since composition is from right to left, etc.

#def[$k$-cycles and transpositions][
  We call $(a_1 a_2 a_3 dots a_k)$ a $k$-cycle. $2$-cycles are transpositions, and two cycles are disjoint if no number appears in both.
]

#lemma[
  Disjoint cycles commute.
]

#proof[
  Let $sigma$, $tau in S_n$ be disjoint. Want to show $sigma(tau(a))=tau(sigma(a))$. If $a$ is not in $sigma$ and $tau$ then $sigma(tau(a))=tau(sigma(a))=a$. Else assume $a$ is in $tau$ and not in $sigma$. Then $tau(a) in tau$ and $tau(a) in.not sigma$. So $sigma(a)=a$ and $sigma(tau(a))=tau(a)$, also $tau(sigma(a))=tau(a)$ thus $sigma(tau(a))=tau(sigma(a))$.

]

#thm[
  Any permutation in $S_n$ can be written uniquely as a product of disjoint cycles. (up to re-ordering)
]
#proof[
  Let $sigma in S_n$. We start with $(1 sigma(1) sigma^2(1) sigma^3(1) dots)$. The set ${1,2,3,dots n}$ is finite so for some $k$ we must have $sigma^k (1)$ already in our list. If $sigma^k (1)=sigma^l (1)$ with $l<k$ then $sigma^(k-l)(1)=1$. So all $sigma^i (1)$ are distinct until looping back to $1$. This gives the first cycle $(1 sigma(1) sigma^2(1) sigma^3(1) dots sigma^(k-1) (1))$. Now we choose smallest number $j$ not in a cycle and repeat this to obtain $(j sigma(j) sigma^2(j) sigma^3(j)dots sigma^(l-1)(j))$. Nothing will be repeated since $sigma$ is a bijection. We repeat until all ${1,2,3, dots n}$ are used.
]

#def[Cycle type][
  The cycle type is the list of cycle lengths, e.g $(12)$ has cycle type 2, while $(12)(34)$ has cycle type 2,2.
]

#lemma[
  For $sigma in S_n$ the order of $sigma$ is the least common multiple of cycle lengths in disjoint cycle notation.
]

#proof[
  Since disjoint cycles commute we can easily take powers $ sigma^m = tau_1^m tau_2^m dots tau_l^m $ if $tau_i$ has length $k_i$ then $tau_i^(k_i)=e$ and $tau_i^m=e$ iff $k_i$ divides $m$. For $sigma^m=e$ we need all $k_i$ to divide $m$ so the order is the smallest such $m$, i.e. the order is the least common multiple of $k_i$.
]
#pagebreak()
== Sign of permutations
#thm[
  Every permutation is a product of transpositions.
]
#proof[
  All permutations are products of disjoint cycles, so we just need to prove that each cycle is a product of transpositions. Consider $(a_1 a_2 a_3 dots a_k)$, this is the same as $(a_1 a_2)(a_2 a_3)dots (a_(k-1) a_k)$, so a $k$-cycle can be written as a product of $k-1$ transpositions.

]
#thm[
  We can write $sigma in S_n$ as a product of transpositions in many ways, but $sigma$ is always composed of an odd or even number of transpositions.
]
#proof[
  We write $hash(sigma)$ for the number of cycles in disjoint cycle notation, including singletons, e.g $hash(e)=n "and" hash((12))=n-1$. Now, when we multiply $sigma$ by a transposition $tau = (c d)$ assuming $c < d$
  1. if $c,d$ are in the same cycle then our cycle splits giving $hash(sigma tau) = hash(sigma)+1$.

  2. if $c,d$ are in different cycles then our cycle gets glued together giving $hash(sigma tau)=hash(sigma)-1$.
  So any $tau$ gives $hash(sigma tau)=hash(sigma)+1 "(mod "2)$. Now let $sigma = tau_1 dots tau_l = tau_1' dots tau_k'$, since disjoint cycle notation is unique, $hash(sigma)$ is uniquely determined by $sigma$. Now we can construct $sigma$ by starting with $e$ and multiplying by transpositions one by one. Each time we increase $hash(sigma)$ by $1 "(mod "2)$. So $hash(sigma) = hash(e)+l "(mod "2)$. And $hash(sigma) = hash(e)+k "(mod "2)$, so $l equiv k "(mod "2)$.
]
*/
#def[Sign of permutation][
  Given $sigma=tau_1 dots tau_l in S_n$ we define $"sgn"(sigma)=(-1)^l$. If $"sgn"(sigma)=1$ then we say $sigma$ is even. If $"sgn"(sigma)=-1$ then $sigma$ is odd.
]
/*

#thm[
  For $n >= 2$ $"sgn":S_n arrow {plus.minus 1}$ is a surjective group homomorphism.
]

#proof[
  Let $sigma_1=tau_1 dots tau_(l_1)$ and $sigma_2 = tau_1' dots tau_(l_2)$. Then $ "sgn"(sigma_1sigma_2)=(-1)^(l_1 + l_2) = (-1)^(l_1)(-1)^(l_2) = "sgn"(sigma_1)"sgn"(sigma_2) $ so it is a homomorphism. Since $"sgn"(e)=1 "and" "sgn"((12))=-1$ then it is surjective.
]

#lemma[
  $sigma$ is an even permutation iff the number of cycles of even length is even.
]
#proof[
  A $k$-cycle can be written as $k-1$ transpositions, so an even-length cycle is odd. $"sgn"$ is a homomorphism so $ sigma = sigma_1 sigma_2 dots sigma_l arrow "sgn"(sigma)="sgn"(sigma_1)dots"sgn"(sigma_l) $ if $m$ even-length cycles and $n$ odd-length cycles, then $"sgn"(sigma)=(-1)^m 1^n$. So $"sgn"(sigma) = 1$ iff $(-1)^m = 1$, i.e. $m$ is even.
]
*/
#def[Alternating group $A_n$][
  The alternating group $A_n$ is $"ker"("sgn")$, i.e. the even permutations. Also since $A_n$ is a kernel then $A_n <= S_n$.
]
/*

#thm[
  Any subgroup of $S_n$ contains no odd permutations or exactly half.
]
#proof[
  If $S_n$ has at least one odd permutation $tau$ then there exists a bijection between odd and even permutations by $sigma |-> sigma tau$, so there must be as many odd permutations as even permutations.
]
*/
#pagebreak()

= Lagrange's Theorem
#def[Cosets][
  Let $H <= G$ and $a in G$. Then the set $a H = {a h : h in H}$ is the left coset of $H$ and $H a = {h a: h in H}$ is the right coset of $H$
]
We will try to think of stuff in the same coset as the same thing, so $a$ is equivalent to its coset $a H$---it's worth mentioning that for any $g in G$ we always have $g in g H$, since $e in H$.
#ex[
  1. Let $2 ZZ <= ZZ$ then $6 + 2 ZZ = {"all even numbers"} = 0 + 2ZZ$ and $1 + 2 ZZ = {"all odd numbers"} = 17 + 2 ZZ$.

  2. Let $G = S_3$ and $H = angle.l (1 2) angle.r = {e,(1 2)}$. The left cosets are $     e H = (12)H & = {e, (1 2)} \
    (1 3)H = (123)H & = {(13),(123)} \
    (2 3)H = (132)H & = {(23),(132)} $
]
#thm[
  $a H = b H$ iff $b^(-1)a in H$
]
#proof[
  Since $a in a H, a in b H$ so $a = b h$ for some $h in H$ so $b^(-1)a = h in H$.

  For the other direction let $b^(-1)a=h_0$ so $a=b h_0$ then for all $a h in a H$ we have $a h = b (h_0 h) in b H$ so $a H subset.eq b H$ and $b h = a (h_0^(-1)h) in a H$ so $b H subset.eq a H$ and thus $a H = b H$.
]
#def[Partition][
  Let $X$ be a set, with subsets $X_1,dots X_n$. The $X_i$ are a partition of $X$ if $union.big X_i = X$ and $X_i inter X_j = emptyset$ for $i eq.not j$.
]
#lemma[
  The left cosets of a subgroup $H <= G$ partition $G$, and every coset has the same size.
]
#proof[
  For any $a in G$, $a in a H$, so the union of all cosets gives $G$. Now we want to show that for all $a,b in G$ the cosets $a H$ and $b H$ are either the same or disjoint. Assume that $a H$ and $b H$ are not disjoint. Let $a h_1 = b h_2 in a H inter b H$, then immediately $b^(-1)a = h_2 h_1^(-1) in H$, and by the previous theorem $a H = b H$. To show that each coset has the same size, note that $f:H arrow a H$ with $f(h) = a h$ is invertible with $f^(-1)(h)=a^(-1)h$. Thus a bijection exists, and they must have the same size, or all cosets have the same size as $H$ the "trivial" coset.
]
#def[Index of a subgroup][
  The index of $H$ in $G$, written $|G : H|$ is the number of left cosets of $H$ in $G$.
]
#thm[Lagrange's theorem][
  If $G$ is a finite group and $H$ is a subgroup of $G$, then $|H|$ divides $|G|$, in particular $ |H| |G:H|=|G| $
]
#proof[
  This follows immediately from the previous theorems (that the left cosets partition $G$ and have same size), since the cosets of size $|H|$ partition $G$, and we have $|G:H|$ cosets so the total number of elements in $G$ is $ |G|=|H| |G:H| $
]

Now we get a bunch of free corollaries.
#corollary[
  The order of an element divides the order of the group, i.e for any $a in G$ $"ord"(a)$ divides $|G|$.
]
#proof[
  Consider the subgroup generated by $a in G$, this has size $"ord"(a)$, by Lagrange's theorem the result immediately follows.
]
#corollary[
  The exponent of a group divides the order of the group, i.e. for any $G$ and $a in G$ we have $a^(|G|)=e$
]
#proof[
  We have $|G|=k "ord"(a)$ for some $k in NN$. So $a^(|G|)=(a^("ord"(a)))^k = e^k=e$
]
#corollary[
  Groups of prime order are cyclic and are generated by every non-identity element.
]
#proof[
  Let $|G|=p$. If $a in G$ is not the identity, then the subgroup it generates has to be $p$ since it must divide $p$. Thus the subgroup generated by $a$ has the same size as $G$ and they must then be equal. Then $G$ must be cyclic since the subgroup generated by $a$ is cyclic by construction.
]

Now we'll shift our focus to equivalence classes.
#def[Equivalence relation][
  An equivalence relation $tilde$ is a relation that is reflexive, symmetric and transitive
  1. For all $x$, $x tilde x$
  2. For all $x,y$, $x tilde y => y tilde x$

  3. For all $x,y,z$, $x tilde y$ and $y tilde z$ implies $x tilde z$
]
#def[Equivalence class][
  Given a $tilde$ on $A$, then the equivalence class of $a$ is
  $ [a]_tilde = [a] = {b in A: a tilde b} $
  i.e. all elements in $A$ that are equivalent to $a$ form the equivalence class $[a]$.
]
#thm[
  The equivalence classes form a partition of $A$.
]
#proof[
  By definition we have $a in [a]$. So equivalence classes trivially cover the set. Now we need to show that for all $a,b in A$ either $[a]=[b]$ or $[a] inter [b] = emptyset$. Assume $[a] inter [b] eq.not emptyset$, then there exists some $c in [a] inter [b]$, so $a tilde c$ and $b tilde c$, then by symmetry and transitivity we have $a tilde b$. Further for all $b' in [b]$ we have $b tilde b'$ and for all $a' in [a]$ we have $a tilde a'$. So we have both $[b] subset.eq [a]$ and $[a] subset.eq [b]$ so $[a] = [b]$.
]
#lemma[
  Given a group $G$ and a subgroup $H$, we define a equivalence relation on $G$ with $a tilde b$ iff $b^(-1)a in H$, i.e. if $a H = b H$. So the equivalence classes are the left cosets of $H$.
]
#proof[
  First we show that this is a valid equivalence relation.
  1. Since $a a^(-1) = e in H$, then $a tilde a$

  2. $a tilde b$ implies $b^(-1)a in H$ so $a^(-1)b in H$ meaning $b tilde a$.

  3. If $a tilde b$ and $b tilde c$ then $b^(-1)a,c^(-1)b in H$ so $c^(-1)b b^(-1)a = c^(-1)a in H$. So $a tilde c$.
  Now to show that the equivalence classes are the cosets we have $a tilde b$ iff $b^(-1)a in H$ iff $a H = b H$, by a previous theorem.
]
#ex[
  Consider $(ZZ,+)$ and take the subgroup $n ZZ$ (fixed $n$). The cosets are $0 + H, 1+H,...(n-1)+H$. These can be written as $[0],[1],...[n]$. We can perform arithmetic $"(mod "n)$ as $[a]+[b]=[a+b]$, and $[a][b]=[a b]$. This is well defined, i.e. whichever $a_i$ we pick we get the same result.
]
We'll let $U_n = {[a]:(a,n)=1}$ (units), only allowing elements with inverses, where $(a,n) = gcd(a, n)$.

#def[Euler totient function][
  $phi(n)$ counts the number of integers $1 <= a <= n$ such that $(a,n)=1$. Each $a$ gives an equivalence class $[a]$ or unit. Thus the number of units $|U_n|$ is $phi(n)$
  $ phi(n)=|U_n| $
]
#ex[
  If $p$ prime then $phi(p)=p-1$, since every integer has $gcd(a, p) = 1$, except $gcd(p, p) eq.not 1$.
]
#thm[
  $U_n$ is a group under multiplication $"mod" n$
]
#proof[
  0. If $a,b$ are coprime to $n$, then $a b$ is also coprime to $n$. So $[a],[b] in U_n$ implies $[a][b]=[a b] in U_n$.

  1. [1] is the identity.

  2. Let $[a] in U_n$. Consider the map $U_n arrow U_n$ with $[c] |-> [a c]$. This is injective, if $[a c_1] = [a c_2]$ then $n$ divides $a(c_1 - c_2)$. Since $a$ is coprime to $n$, $n$ divides $c_1 - c_2$ so $[c_1] = [c_2]$. Since $U_n$ is finite then any injection from $U_n arrow U_n$ is also a surjection, and thus a bijection. So there exists some $c$ such that $[a c] = [a][c] = 1$. So $[c] = [a]^(-1)$.

  3. Associativity (and commutativity) is inherited from $ZZ$.
]
#thm[Fermat-Euler Theorem][
  Let $n in NN$ and $a in ZZ$ coprime to $n$. Then
  $ a^(phi(n))equiv 1 "(mod "n) $
  in particular (Fermat's Little Theorem), if $n = p$ is prime, then for any $a$ not a multiple of $p$
  $ a^(p-1) equiv 1 "(mod "p) $
]
#proof[
  Since $a$ is coprime with $n$, $[a] in U_n$. Then $[a]^(|U_n|)=[1]$, which is just $a^(phi(n))equiv 1 "(mod "n)$. Where we've used that the order of any element divides the order of the group (Lagrange's theorem), and then simply picked the largest possible order which is $|U_n|$.
]

== Small groups
Lagrange's theorem lets us find subgroups. Consider $D_(10)$, we know the subgroups must have size $1,2,5 "or" 10$.
1. This is just ${e}$.

2. This will be all the subgroups generated by reflections of order $2$.

5. This group must be cyclic, since it is prime order, and will be generated by an element of order $5$ i.e. $angle.l r angle.r$.

10. This is just $D_10$.

similarly can be done for all other groups in principle.

#thm[
  Any group of order $4$ is either isomorphic to $C_4$ or $C_2 times C_2$.
]

#proof[
  Let $|G| = 4$. By Lagranges theorem the possible element orders are $1, 2 "and" 4$. If an element $a in G$ has order $4$ then $G = angle.l a angle.r tilde.equiv C_4$. Otherwise all non-identity elements have order $2$, and thus $G$ must be Abelian. Since for any $a,b in G$ we'll have $ (a b)^2 = 1 => a b = (a b)^(-1) => a b = b^(-1)a^(-1) = b a $ Now pick any two elements of order $2$, e.g. $b,c in G$. Then $angle.l b angle.r = {e, b}$ and $angle.l c angle.r = {e, c}$. So $angle.l b angle.r inter angle.l c angle.r = {e}$. $G$ is Abelian so $angle.l b angle.r$ and $angle.l c angle.r$ commute. And we know $b c = c b$ has order $2$ as well, and must be the only element left ($G = {e, b, c, b c}$). So $G tilde.equiv angle.l b angle.r times angle.l c angle.r tilde.equiv C_2 times C_2$ by the direct product theorem.

]

_note: Left and right cosets have the same size $|a H| = |H| = |H a|$, but are not necessarily the same._


