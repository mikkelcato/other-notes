//**** init-ting
#import "@preview/physica:0.9.5": *
#import "chpt-temp.typ": *
#import "@preview/mannot:0.3.0": *
#import "@preview/cetz:0.4.1" // drawings

#show: thmrules.with(qed-symbol: $square$)
#show: chpt-note.with()

#pagebreak()
= Definitions
#def[Ring][
  A ring is a quintuple $(R, +, dot, 0_R, 1_R)$ where $0_R, 1_R in R$, and $+, dot : R times R arrow R$ are binary operations such that

  $(1)$ $(R, +, 0_R)$ is an abelian group.

  $(2)$ The operation $dot : R times R arrow R$ satisfies
  $
    a dot (b dot c) & = (a dot b) dot c \
          1_R dot r & = r dot 1_R = r
  $
  i.e. associativity and identity.

  $(3)$ Multiplication distributes over addition,
  $
    r_1 dot (r_2 + r_3) & = (r_1 dot r_2) + (r_1 dot r_3) \
    (r_1 + r_2) dot r_3 & = (r_1 dot r_3) + (r_2 dot r_3)
  $
]

If $R$ is a ring and $r in R$, we write $-r$ for the inverse to $r$ in $(R, +, 0_R)$. This satisfies $r + (-r) = 0_R$. We write $r - s = r + (-s)$.

Also note that some people don't insist on the existence of $1_R$, but we do---so we only consider what some would call rings with $1$ or unital rings.

By induction we can add and multiply any finite number of elements. Note that the notion of an infinite sum or product are undefined.

#def[Commutative ring][
  We say a ring $R$ is commutative if $a dot b = b dot a$ for all $a, b in R$---and all rings we'll consider will be commutative.
]

As with groups and subgroups we also have subrings.

#def[Subring][
  Let $(R, +, dot, 0_R, 1_R)$ be a ring, and $S subset.eq R$ be a subset.

  Then $S$ is a subring of $R$ if $0_R, 1_R in S$ and the operations $+, dot$ make $S$ into a ring. In this case $S <= R$.
]

#ex[
  The usual number systems are all rings, $ZZ <= QQ <= RR <= CC$, under the normal $0, 1, +, dot$.
]

#ex[
  The set $ZZ[i] = {a + i b:a, b in ZZ} <= CC$ is the Gaussian integers, which is a ring. We also have the ring $QQ[sqrt(2)] = {a + b sqrt(2) : a,b in QQ} <= RR$.

  The $[dot]$ notation is used often, and will be defined properly later.
]

Generally elements in a ring don't have inverses, something like $ZZ$ only has two invertible elements, namely ${1, -1}$. These are called units.

#def[Unit][
  An element $u in R$ is a unit if there is another element $v in R$ with $u dot v = 1_R$.
]

Note that this depends on $R$, since $2 in ZZ$ has no inverse, but $2 in QQ$ does. When everything except $0_R$ is a unit then we have a field.

#def[Field][
  A field is a non-zero ring where every $u eq.not 0_R in R$ is a unit.
]

#ex[
  Let $R$ be a ring. Then $0_R + 0_R = 0_R$, since this is true in $(R,+,0_R)$. Then for any $r in R$,
  $
        r dot (0_R + 0_R) & = r dot 0_R \
    r dot 0_R + r dot 0_R & = r dot 0_R \
                r dot 0_R & = 0_R
  $
  where we add $(-r dot 0_R)$. This is true for any $r in RR$. It follows that if $R eq.not {0}$, then $1_R eq.not 0_R$. If they were then take $r eq.not 0_R$, so
  $
    r = r dot 1_R = r dot 0_R = 0_R
  $
  which is a contradiction.
]

Note that ${0}$ does form a ring---with the only possible operations and identities---though the zero ring might be boring it is often a nice counterexample.

#def[Product of rings][
  Let $R, S$ be rings. Then the product $R times S$ is a ring with
  $
     (r, s) + (r', s') & = (r + r', s + s') \
    (r, s) dot (r',s') & = (r dot r', s dot s')
  $
  and with zero $(0_R, 0_S)$ and one $(1_R, 1_S)$. That this is a ring should be somewhat obvious.
]

#def[Polynomial][
  Let $R$ be a ring. Then a polynomial with coefficients in $R$ is,
  $
    f = a_0 + a_1 X + a_2 X^2 + dots + a_n X^n
  $
  with $a_i in R$. The $X^i$ are formal symbols.
]

We say $f$ and $f + 0_R dot X^(n+1)$ is the same thing.

#def[Degree of polynomial][
  The degree of a polynomial $f$ is the largest $m$ such that $a_m eq.not 0$.
]
#def[Monic polynomial][
  Let $f$ have degree $m$. If $a_m = 1$, then $f$ is monic.
]
#def[Polynomial ring][
  We write $R[X]$ for the set of all polynomials with coefficients in $R$. The operations are performed as one would expect, i.e. given polynomials $f = a_0 + a_1 X + dots + a_n X^n$ and $g = b_0 + b_1 X + dots + b_k X^k$ then
  $
    f+g = sum_(r = 0)^(max {n, k}) (a_i + b_i) X^i
  $
  and
  $
    f dot g = sum_(i=0)^(n+k) (sum_(j=0)^i a_j b_(i-j)) X^i
  $
  where the middle sum handles the coefficients. We identify $R$ with the constant polynomials, i.e. polynomials $sum a_i X^i$ with $a_i = 0$ for $i > 0$. In particular $0_R in R$ and $1_R in R$ are the zero and one of $R[X]$.
]

This is a ring. Note that a polynomial is literally just a sequence of numbers, where we interpret them as coefficients of some formal symbols $X^i$. It does induce a function in the way one would obviously expect, but we don't identify the polynomial with this function, since different polynomials can give rise to the same function. For example take $ZZ\/2ZZ [X]$, here $f = X^2 + X$ is not the zero polynomial, since the coefficients are non-zero. But $f(0) = f(1) = 0$, in fact as a function this is zero everywhere. So $f eq.not 0$ as a polynomial but $f=0$ as a function.

#def[Power series][
  We write $R[[X]]$ for the ring of power series on $R$, i.e.
  $
    f = a_0 + a_1 X + a_2 X^2 + dots
  $
  where $a_i in R$. This has addition and multiplication similarly to polynomials, but without upper limits.
]

This is not a function, and we don't talk about whether the sum converges or not, because it is not a sum.

#ex[
  Is $1 - X in R[X]$ a unit? For every $g = a_0 + dots + a_n X^n$ we get
  $
    (1 - X) g = "stuff" + dots - a_n X^(n+1)
  $
  which is not $1$. So $g$ cannot be the inverse of $1-X$, so it is not a unit.

  But $1-X in R[[X]]$ is a unit, since
  $
    (1-X)(1+X+X^2+X^3+dots) = 1
  $
]

#def[Laurent polynomials][
  The Laurent polynomials on $R$ is the set $R[X,X^(-1)]$, so each element is of the form
  $
    f = sum_(i in ZZ) a_i X^i
  $
  where $a_i in R$ and only finitely many $a_i$ are non-zero. The operations are obvious.
]

We can also define Laurent series, but we can only allow finitely many negative coefficients, else we could end up with an infinite sum when multiplying, which is undefined.

#ex[
  Let $X$ be a set, and $R$ a ring. The set of all functions $f: X arrow R$ is a ring with operations
  $
    (f+ g) (x) = f(x) +g(x)
  $
  and
  $
    (f dot g) (x) = f(x) dot g(x)
  $
  zero is the constant function $0$ and one is the constant function $1$. Typically we look a subrings, e.g. all continuous functions $RR arrow RR$.
]

#pagebreak()
= Homomorphisms, ideals, quotients and isomorphisms
As with groups we have analogues of homomorphisms, normal subgroups (ideals for rings) and quotients.

#def[Homomorphism of rings][
  Let $R, S$ be rings. A function $phi : R arrow S$ is a ring homomorphism if it preserves everything, i.e.

  $(1)$ $phi(r_1+r_2) = phi(r_1) + phi(r_2)$

  $(2)$ $phi(0_R) = 0_S$

  $(3)$ $phi(r_1 dot r_2) = phi(r_1) dot phi(r_2)$

  $(4)$ $phi(1_R) = 1_S$
]

#def[Isomorphism of rings][
  If a homomorphism $phi : R arrow S$ is a bijection, then it is an isomorphism.
]

#def[Kernel][
  The kernel of a homomorphism $phi : R arrow S$ is
  $
    ker phi = {r in R : phi(r) = 0_S}
  $
]
#def[Image][
  The image of $phi : R arrow S$ is
  $
    im phi = {s in S: s = phi (r) "for some" r in R}
  $
]

#lemma[
  A homomorphism $phi : R arrow S$ is injective if and only if $ker phi = {0_R}$.
]

#proof[
  A ring homomorphism is in particular a group homomorphism $phi : (R, plus, 0_R) arrow (S, plus, 0_S)$ of abelian  groups. So this follows from the case of groups.
]

The special subsets of a ring that act like normal subgroups are ideals.
#def[Ideal][
  A subset $I subset.eq R$ is an ideal, written $I lt.tri R$ if

  $(1)$ It is an additive subgroup of $(R, plus, 0_R)$, so it is closed under addition and additive inverses---additive closure.

  $(2)$ If $a in I$ and $b in R$, then $a dot b in I$---strong closure.
]
We say $I$ is a proper ideal if $I eq.not R$.

Note that multiplicative closure (strong closure) is stronger then what we require for subring---for these we just required that it is closed under multiplication by its own elements, for ideals we require it be closed under multiplication by the whole ring. Similar in spirit to how normal subgroups have to be closed under internal multiplication, and also by conjugation with every element of the whole group.

#lemma[
  If $phi : R arrow S$ is a homomorphism, then $ker phi lt.tri R$.
]
#proof[
  Since $phi : (R, +, 0_R) arrow (S, +, 0_S)$ is a group homomorphism, the kernel is a subgroup of $(R, +, 0_R)$.

  Now let $a in ker phi$ and take $b in R$. We need to show that their product is in the kernel,
  $
    phi(a dot b) = phi(a) dot phi(b) = 0 dot phi(b) = 0
  $
  so $a dot b in ker phi$.
]

#ex[
  Suppose $I lt.tri R$ is an ideal, and $1_R in I$. Then for any $r in R$ we have $1_R dot r in I$, but $1_R dot r = r$ so $I = R$.

  So no proper ideal contains $1$. In particular, every proper ideal is not a subring, since a subring must contain $1$---according to our definition. This is unlike with groups, where the normal subgroup is always a subgroup.
]
#ex[
  Suppose $I lt.tri R$ and $u in I$ is a unit, so we have some $v in R$ such that $u dot v = 1_R$, then by strong closure $1_R = u dot v in I$. So $I=R$. So proper ideals can't contain any unit at all.
]
#ex[
  Consider the ring $ZZ$. Then every ideal is of the form
  $
    n ZZ = {dots, - 2n, -n, 0, n, 2n, dots} subset.eq ZZ
  $
  this is easy to see since the factor $n$ will always stay. To show these are all the ideals, let $I lt.tri ZZ$. If $I = {0}$ then $I = 0 ZZ$. Else let $n in NN$ be the smallest positive element of $I$. We want to show that $I = n ZZ$, certainly by strong closure $n ZZ subset.eq I$.

  Let $m in I$, by the Euclidean algorithm we can write $m = q dot n + r$ with $0 <= r < n$. Now $n, m in I$, so by strong clousre $m, q dot n in I$. So $r = m - q dot n in I$. As $n$ is the smallest positive element of $I$, and $r < n$, we must have $r = 0$. So $m = q dot n in n ZZ$. So $I subset.eq n ZZ$. So $I = n ZZ$.
]

This extends to any ring $R$ where we can _do the Euclidean algorithm_. In which every ideal would be of the form $a R = {a dot r : r in R}$, for some $a in R$.

#def[Generator of ideal][
  For an element $a in R$, we write
  $
    (a) = a R = {a dot r : r in R} lt.tri R
  $
  this is the ideal generated by $a$.

  In general, let $a_1, a_2, dots, a_k in R$, we write
  $
    (a_1,a_2,dots,a_k) = {a_1 r_1 + dots + a_k r_k : r_1, dots, r_k in R}
  $
  this is the ideal generated by $a_1, dots, a_k$.
]
#def[Generator of ideal II][
  For $A subset.eq R$ a subset, the ideal generated by $A$ is
  $
    (A) = {sum_(a in A) r_a dot a : r_a in R}
  $
  with finitely many non-zero.
]

These turn out to have nice properties.
#def[Principal ideal][
  An ideal $I$ is a principal ideal if $I = (a)$ for some $a in R$.
]
So we've just shown that all ideals of $ZZ$ are principal ideals.

As mentioned these ideals are like normal subgroups, and as with those we can also divide by ideals.
#def[Quotient ring][
  Let $I lt.tri R$. The quotient ring $R\/ I$ consists of the (additive) cosets $r+I$ with the zero and one as $0_R+I$ and $1_R+I$, and the operations,
  $
         (r_1+I)+(r_2+I) & = (r_1+r_2) + I \
    (r_1+I)dot (r_2 + I) & = r_1 dot r_2 + I
  $
]
This is exactly like quotient groups, just with the $1_R$ tagging along.

#proposition[
  The quotient ring is a ring, and the function
  $
    R & ->R\/I \
    r & |->r+I
  $
  is a ring homomorphism.
]

This is true because the ideals are defined such that it is true. For the multiplication to be well-defined we need strong closure. Similarly to how normal subgroups are defined such that multiplication is well-defined for the quotient group.

#proof[
  We know the group $(R\/I,+, 0_(R\/I))$ is well-defined, since $I$ is a (normal) subgroup of $R$. So we just need to check if multiplication is well-defined.

  Suppose $r_1 + I = r'_1 + I$ and $r_2 + I = r'_2 + I$. Then $r'_1 -r_1 = a_1 in I$ and $r'_2 -r_2 = a_2 in I$. So
  $
    r'_1 r'_2 = (r_1 + a_1) (r_2 + a_2) = r_1 r_2 + r_1 a_2 +r_2 a_2 + a_1 a_2
  $
  by strong closure the last three are in $I$, so $r'_1 r'_2 + I = r_1 r_2 + I$.

  It is easy to check that $0_R + I$ and $1_R + I$ are the zero and one. And the function is clearly a homomorphism,
  $
    phi(r_1 + r_2) = (r_1 + r_2) + I = (r_1 + I) + (r_2 + I) = phi(r_1) + phi(r_2)
  $
  and likewise for multiplication.
]

#ex[
  We have ideals $n ZZ lt.tri ZZ$. So we have quotient rings $ZZ \/n ZZ$. The element are of the form $m + n ZZ$, so they are just,
  $
    0 + n ZZ, 1 + n ZZ, 2 + n ZZ, dots, (n-1) + n ZZ
  $
  with addition and multiplication clearly being modulo $n$.
]

Ideals are nice because we can generate them very easily, since any random element gives us one.

#ex[
  Consider $(X) lt.tri CC[X]$. What is $CC[X]\/(X)$? Every element looks like
  $
    a_0 + a_1 X + dots + a_n X^n + (X)
  $
  everything expect $a_0$ is in $(X)$---since it contains everything with $X$ as a factor---so we can just write $a_0 + (X)$. So $CC[X]\/(X) tilde.equiv CC$ with the bijection $a_0 + (X) <-> a_0$.
]

This depends on us believing that the representation is unique.

#proposition[Euclidean algorithm for polynomials][
  Let $FF$ be a field and $f, g in FF[X]$. Then there is some $r, q in FF[X]$ such that
  $
    f = g q + r
  $
  with $deg r < deg g$
]
#proof[
  Let $deg f = n$. So
  $
    f = sum_(i=0)^n a_i X^i
  $
  and $a_n eq.not 0$. Similarly if $deg g = m$,
  $
    g = sum_(i=0)^m b_i X^i
  $
  with $b_m eq.not 0$. If $n < m$, we let $q = 0$ and $r = f$---so done.

  Otherwise assume $n >= m$, and proceed by induction on $n$. We let
  $
    f_1 = f - a_n b_m^(-1) X^(n-m) g
  $
  which is possible since $b_m eq.not 0$ and $FF$ is a field.
  By construction the coefficients of $X^n$ cancel. So $deg f_1 < n$.

  If $n = m$ then $deg f_1 < n = m$, so we can write
  $
    f = (a_n b_m^(-1) X^(n-m)) g + f_1
  $
  and $deg f_1 < deg f$---so done.

  Otherwise $n > m$, then as $deg f_1 < n$, by induction we can find $r_1, q_1$ with
  $
    f_1 = g q_1 + r_1
  $
  and $deg r_1 < deg g = m$. Then
  $
    f = a_n b_m^(-1) X^(n-m) g + q_1 g + r_1 = (a_n b_m^(-1) X^(n-m) + q_1)g + r_1
  $
  and we are done.
]

Now we can show that every ideal of $FF[X]$ is generated by one polynomial. Later we'll show that in general, in every ring where the Euclidean algorithm is possible, all ideals are principal---implying that all ideals are generated by one thing.

#ex[
  Consider $RR[X]$, and the principal ideal $(X^2 + 1) lt.tri RR[X]$. We let $R = RR[X]\/(X^2 + 1)$. Element of $R$ are polynomials
  $
    a_0 + a_1 X + a_2 X^2 +dots + a_n X^n + (X^2 + 1) = f + (X^2 + 1)
  $
  by the Euclidean algorithm
  $
    f = q (X^2 + 1) + r
  $
  where $deg r < 2$, so $r = b_0 + b_1 X$. Then $f + (X^2 + 1) = r + (X^2 + 1)$, since $q (X^2 + 1)$ gets eaten by $(X^2 + 1)$. So every element of $RR[X]\/(X^2 + 1)$ can be represented as $a + b X$ for some $a, b in RR$.

  Is this unique? Take $a + b X + (X^2 + 1) = a' + b' X + (X^2 + 1)$, then $(a - a') + (b- b') X in (X^2 + 1)$, so it is $(X^2 + 1) q$ for some $q$. This is only possible if $q = 0$, since $(X^2 + 1) q$ has degree at least $2$. So we need $(a-a')+(b-b') X = 0$. So $a + b X = a' + b' X$. So it is unique.

  So we have that every element of $R$ is of the form $a + b X$, and $X^2 + 1 = 0 => X^2 = - 1$. This is very much like complex numbers. We define
  $
    phi : RR[X]\/(X^2 +1) & -> CC \
      a + b X + (X^2 + 1) & |-> a + b i
  $
  this is clearly a bijection, and it is additive. So we just want to prove it is an isomorphism, meaning we need to show it is multiplicative. We have
  $
    & phi((a + b X + (X^2 +1))(c +d X + (X^2 + 1))) \
    & = phi(a c + (a d + b c) X + b d X^2 + (X^2 + 1)) \
    & = phi((a c - b d) + (a d + b c) X + (X^2 + 1)) \
    & = (a c - b d) + (a d + b c) i \
    & = (a + b i)(c + d i) \
    & = phi(a + b X + (X^2 + 1)) phi(c + d X + (X^2 +1))
  $
]

As with groups we also have isomorphism theorems, these are exactly the same.

#thm[First isomorphism theorem][
  Let $phi : R arrow S$ be a ring homomorphism. Then $ker phi lt.tri R$, and
  $
    R/(ker phi) tilde.equiv im phi <= S
  $
]
#proof[
  We already know $ker phi lt.tri R$. Now define
  $
    Phi : R\/ker phi & -> im phi \
         r + ker phi & |-> phi (r)
  $
  this is well-defined, $r + ker phi = r' + ker phi => r - r' in ker phi => phi(r - r') = 0 => phi(r) = phi(r')$.

  We don't need to check that this is bijective and additive, since this follows from the theorem for groups. We just need to show it is multiplicative. We have
  $
    Phi ((r + ker phi)(t + ker phi)) & = Phi (r t + ker phi) \
                                     & = phi (r t) \
                                     & = phi (r) phi (t) \
                                     & = Phi (r + ker phi) Phi (t +ker phi)
  $
]

#thm[Second isomorphism theorem][
  Let $R <= S$ and $J lt.tri S$. Then $J inter R lt.tri R$, and
  $
    (R + J) / J = {r + J : r in R} <= S/J
  $
  is a subring, and
  $
    R/(R inter J) tilde.equiv (R + J) / J
  $
]
#proof[
  Define
  $
    phi : R & -> S\/J \
          r & |->r + J
  $
  this is the quotient map, so it is a ring homomorphism. The kernel is
  $
    ker phi = {r in R : r + J = 0 => r in J} = R inter J
  $
  the image is the quotient ring
  $
    im phi = {r + J : r in R} = (R + J)/J
  $
  then by the first isomorphism theorem, we know $R inter J lt.tri R$, and $(R + J)\/J <= S$, so
  $
    R/(R inter J) tilde.equiv (R + J)/J
  $
]

As with groups we also have a correspondence between rings. For $I lt.tri R$
$
  {"subrings of" R\/I} & <--> {"subrings of" R "which contain" I} \
              L <= R/I & --> {x in R : x + I in L} \
            S/I <= R/I & <-- I lt.tri S <= R
$
similarly for ideals
$
  {"ideals of" R\/I} <--> {"ideals of" R "which contain" I}
$
note that when we did quotienting for groups the purpose generally was to simplify our group. For rings we typically take quotients to get more interesting rings.

#thm[Third isomorphism theorem][
  Let $I lt.tri R$ and $J lt.tri R$, and $I subset.eq J$. Then $J\/I lt.tri R\/I$ and
  $
    (R\/I)/(J\/I) tilde.equiv R/J
  $
]
#proof[
  We define
  $
    phi : R\/I & -> R\/J \
         r + I & |-> r +J
  $
  this is well-defined and surjective. It is also a ring homomorphism, since multiplication in $R\/I$ and $R\/J$ is the same. The kernel is
  $
    ker phi = {r + I in R\/I : r + J = 0 => r in J} = J\/I
  $
  and the result follows from the first isomorphism theorem.
]

For any ring $R$, there is a unique ring homomorphism $ZZ -> R$, given by
$
  cal(i) : ZZ & -> R \
       n >= 0 & |-> 1_R+1_R+dots+1_R " "n "times." \
       n <= 0 & |-> -(1_R + 1_R + dots + 1_R) " "n "times."
$
Any homomorphism $ZZ -> R$ is given by this, since it must send $1_ZZ |-> 1_R$, $phi(1_ZZ = 1) = 1_R$. What we have is something like
$
  phi(n) = phi(1+1+1+1+dots) = phi(1)+dots = 1_R + dots = n dot 1_R
$

We say that $ZZ$ is the initial object in the category of rings.

We then know $ker cal(i) lt.tri ZZ$. So $ker cal(i) = n ZZ$ for some $n$.

#def[Characteristic of ring][
  Let $R$ be a ring, and $cal(i) : ZZ -> R$ be the unique such map. The characteristic of $R$ is the unique non-negative $n$ such that $ker cal(i) = n ZZ$.
]

#ex[
  The rings $ZZ, QQ, RR, CC$ all have characteristic $0$. The ring $ZZ\/ n ZZ$ has characteristic $n$. So all natural numbers can be characteristics.
]

#pagebreak()
= Integral domains, field of fractions, maximal and prime ideals

#def[Integral domain][
  A non-zero ring $R$ is an integral domain if for all $a,b in R$, if $a dot b = 0_R$, then $a = 0_R$ or $b = 0_R$.
]

We will work with mostly integral domains, e.g. $ZZ$. An element which violates this property is known as a zero divisor.

#def[Zero divisor][
  An element $x in R$ is a zero divisor if $x eq.not 0$ and there is a $y eq.not 0$ such that $x dot y = 0 in R$.
]

So a ring is an integral domain if it has no zero divisors.
#ex[
  All fields are integral domains, since if $a dot b = 0$ and $b eq.not 0$, then $a = a dot (b dot b^(-1)) = 0$, similarly if $a eq.not 0 => b = 0$.
]
#ex[
  A subring of an integral domain is an integral domain, since a zero divisor in the small ring would also be a zero divisor in the big ring.
]
#ex[
  We know $ZZ, QQ, RR, CC$ are integral domains, since $CC$ is a field, and the others are subrings of it. Also, $ZZ[i] <= CC$ is an integral domain.
]

Integral domains turn out to be nice rings.

#lemma[
  Let $R$ be a finite ring which is an integral domain. Then $R$ is a field.
]
#proof[
  Let $a in R$ be non-zero, and consider the homomorphism,
  $
    a dot - : R & -> R \
              b & |-> a dot b
  $
  we want to show this is injective, meaning we have to show that the kernel is trivial. If $r in ker(a dot -)$ then $a dot r = 0$. So $r = 0$ since $R$ is an integral domain. So the kernel is trivial.

  Since $R$ is finite, $a dot -$ must also be surjective. In particular, there is an element $b in R$ such that $a dot b = 1_R$. So $a$ has an inverse, and since $a$ was arbitrary $R$ is a field.
]

#lemma[
  Let $R$ be an integral domain. Then $R[X]$ is also an integral domain.
]
#proof[
  We need to show the product of two non-zero elements is non-zero.

  Let $f, g in R[X]$ be non-zero,
  $
    f & = a_0 + a_1 X + dots + a_n X^n in R[X] \
    g & = b_0 + b_1 X + dots + b_m X^m in R[X]
  $
  with $a_n, b_m eq.not 0$. Then the coefficient of $X^(n+m)$ in $f g$ is $a_n b_m$. This is non-zero since $R$ is an integral domain. So $f g$ is non-zero. So $R[X]$ is an integral domain.
]



