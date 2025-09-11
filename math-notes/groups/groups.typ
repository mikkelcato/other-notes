#import "@preview/physica:0.9.5": *
#import "temp.typ": *


#show: thmrules.with(qed-symbol: $square$)
#show: note.with(
  title: [
    *group theory*
  ],
  authors: (
    (
      name: "mikkelius_",
    ),
  ),
  abstract: [
    notes on group theory, inspired heavily by Dexter Chua's Cambridge notes---essentially just these rewritten in Typst with some stuff added/removed. I have commented out some of the parts that became less relevant to me over time, otherwise these notes would be very bloated---e.g. some alternating group and Möbius group stuff.
  ],
)

= Introduction to Groups
Group theory is what we would call an algebra. An algebra is some structure with operations, defined through a set of axioms. Group theory can be described as the study of symmetries, since the axioms are essentially defined such that symmetries follow them -- or such that sets of symmetries are groups. What rules should this set of symmetries follow? The symmetry of doing nothing is a symmetry, so we should have some identity leaving our object unchanged. Every symmetry should also have a reverse symmetry or inverse, and lastly symmetries should be associative. A group is any set with these properties.

_Note that many parts have been commented out to save space_

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
