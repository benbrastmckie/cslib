<!-- Source: Zakharyaschev, Wolter & Chagrov (2001). Advanced Modal Logic. Section 1: Unimodal Logics — lattice NExtK, completeness, definability, canonical formulas. -->

We begin by considering normal modal logics with one necessity operator,
which were introduced in Section 6 of Basic Modal Logic. Recall that each
such logic is a set of modal formulas (in the language with the primitive
connectives ^, _, !, ?, 2) containing all classical tautologies, the modal
axiom 2(p ! q) ! (2p ! 2q), and closed under substitution, modus
ponens and necessitation '=2'.

1.1 The lattice NExtK

First let us have a look at the class of normal modal logics from a purely
syntactic point of view. Given a normal modal logic L0 , we denote by
NExtL0 the family of its normal extensions. NExtK is thus the class of all
normal modal logics. Each logic L in NExtL0 can be obtained by adding
to L0 a set of modal formulas ; and taking the closure under the inference
rules mentioned above in symbols this is denoted by
L = L0  ;:
Formulas in ; are called additional (or extra) axioms of L over L0 . Formulas
' and  are said to be deductively equivalent in NExtL0 if L0  ' = L0  .
For instance, 2p ! p and p ! 3p are deductively equivalent in NExtK,
both axiomatizing T, however (2p ! p) $ (p ! 3p) 62 K. (For more information on the relation between these formulas see Chellas and Segerberg
1994] and Williamson 1994].)
We distinguish between two kinds of derivations from assumptions in a
logic L 2 NExtK. For a formula ' and a set of formulas ;, we write ; `L '
if there is a derivation of ' from formulas in L and ; with the help of only
modus ponens. In this case the standard deduction theorem|;  `L ' i
; `L  ! '|holds. The fact of derivability of ' from ; in L using both
modus ponens and necessitation is denoted by ; `L ' in such a case we
say that ' is globally derivable3 from ; in L. For this kind of derivation
we have the following variant of the deduction theorem which is proved by
induction on the length of derivations in the same manner as for classical
logic.
THEOREM 1.1 (Deduction) For every logic L 2 NExtK, all formulas '
and , and all sets of formulas ;,
;  `L ' i 9m 0 ; `L 2m  ! '
where 2m  = 20  ^ : : : ^ 2m  and 2n  is  prexed by n boxes.
3 This name is motivated by the semantical characterization of ` to be given in
L
Theorem 1.19.

6

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

It is to be noted that in general no upper bound for m can be computed
even for a decidable L (see Theorem 4.2). However, if the formula
tran = 2n p ! 2n+1 p
is in L|such L is called n-transitive|then we can clearly take m = n. In
particular, for every L 2 NExtK4, ;  `L ' i ; `L 2+  ! ', where
2+  =  ^ 2. Moreover, a sort of conversion of this observation holds.
THEOREM 1.2 The following conditions are equivalent for every logic L in
NExtK:
(i) L is n-transitive, for some n < !
(ii) there exists a formula (p q) such that, for any ',  and ;,
;  `L ' i ; `L ( '):
Proof The implication (i) ) (ii) is clear. To prove the converse, observe
rst that (p q) `L (p q) and so (p q) p `L q. By Theorem 1.1, we
then have (p q) `L 2n p ! q, for some n. Let q = 2n+1 p. Then
(p 2n+1 p) `L 2n p ! 2n+1 p. And since p `L 2n+1 p, (p 2n+1 p) 2 L.
Consequently, tran 2 L.
2
Remark: Note also that (i) is equivalent to the algebraic condition: the
variety of modal algebras for L has equationally denable principal congruences. For more information on this and close results consult Blok and
Pigozzi 1982].
The sum L1  L2 and intersection L1 \ L2 of logics L1  L2 2 NExtL0 are
clearly logics in NExtL0 as well. The former can be axiomatized simply by
joining the axioms of L1 and L2 . To axiomatize the latter we require the
following denition. Given two formulas '(p1  : : :  pn ) and (p1  : : :  pm)
(whose variables are in the lists p1  : : :  pn and p1  : : :  pm , respectively),
denote by '_ the formula '(p1  : : :  pn ) _ (pn+1  : : :  pn+m ).
THEOREM 1.3 Let L1 = L0  f'i : i 2 I g and L2 = L0  fj : j 2 J g.
Then
L1 \ L2 = L0  f2m 'i _ 2n j : i 2 I j 2 J m n 0g:
Proof Denote by L the logic in the right-hand side of the equality to be
established and suppose that  2 L1 \ L2 . Then for some m n 0 and some
nite I 0 and J 0 such that all '0i and j0 , for i 2 I 0 , j 2 J 0 , are substitution
instances of some 'i and j , for i0 2 I , j 0 2 J , we have

^
^
2 m ' !2L  2 n  !2L 
0

0



0

i 2I

0

i

0



0

j 2J

0

j

0

ADVANCED MODAL LOGIC

7

^ (2k ' _ 2l ) !  2 L

from which

0

i I j J
kl m n

2 0 2 0
0  +

0

i

j

0

and so  2 L because 2k '0i _ 2l j0 is a substitution instance of 2k 'i _2l j .
Thus, L1 \ L2 L. The converse inclusion is obvious.
2
0

0

Although the sum of logics di ers in general from their union, these two
operations have a few common important properties.
THEOREM 1.4 The operation  is idempotent, commutative, associative
and distributes over \ the operation \ distributes over (innite) sums, i.e.,

L\

M Li = M(L \ Li):
i2I

i2I

It follows that hNExtL0  \i is a complete distributive lattice, with L0
and the inconsistent logic, i.e., the set For of all modal formulas, being its
zero and unit elements, respectively, and the set-theoretic its corresponding lattice order. Note, however, that  does not in general distribute over
innite intersections of logics. For otherwise we would have
(K  :2?) 

\ (K  2n?) = \ (K  :2?  2n?)

1n<!

1n<!

which is a contradiction, since the logic in the left-hand side is consistent
(D, to be more precise), while that in the right-hand side is not.
If we are interested in nding a simple (in one sense or another) syntactic
representation of a logic L 2 NExtL0 , we can distinguish nite, recursive
and independent axiomatizations of L over L0. The former two notions
mean that L = L0  ;, for some nite or, respectively, recursive ;, and
a set of axioms ; is independent over L0 if L 6= L0  for any proper
subset of ;. In the case when L0 is K or any other nitely axiomatizable
over K logic, we may omit mentioning L0 and say simply that L is nitely
(recursively, independently) axiomatizable.
It is fairly easy to see that L is not nitely axiomatizable over L0 i
there is an innite sequence of logics L1  L2  : : : in NExtL0 such that
L = i>0 Li . This observation is known as Tarski's criterion. (It is worth
noting that nite axiomatizability is not preserved under \. For example,
using Tarski's criterion, one can show that D \ (K  2p _ 2:p) is not
nitely axiomatizable.) The recursive axiomatizability of a logic L, as was
observed by Craig 1953], is equivalent to the recursive enumerability of L.
As for independent axiomatizability, an interesting necessary condition can
be derived from Kleyman 1984]. Suppose a normal modal logic L1 has an

L

8

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

independent axiomatization. Then, for every nitely axiomatizable normal
modal logic L2  L1, the interval of logics
L2  L1] = fL 2 NExtK : L2 L L1 g
contains an immediate predecessor of L1 . Using this condition Chagrov and
Zakharyaschev 1995a] constructed various logics in NExtK4, NExtS4 and
NExtGrz without independent axiomatizations.
To understand the structure of the lattice NExtL0 it may be useful to
look for a set ; of formulas which is complete in the sense that its formulas
are able to axiomatize all logics in the class, and independent in the sense
that it contains no complete proper subsets. Such a set (if it exists) may be
called an axiomatic basis of NExtL0 . The existence of an axiomatic basis
depends on whether every logic in the class can be represented as the sum
of \indecomposable" logics. A logic L 2 NExtL0 is said to be {irreducible
in NExtL0 if for any family fLi : i 2 I g of logics in NExtL0, L = i2I Li
implies L = Li for some i 2 I . L is {prime if for any family fLi : i 2 I g,
L
i2I Li only if there is i 2 I such that L Li . It is not hard to
see (using Theorem 1.4) that a logic is {irreducible i it is {prime.
This does not hold, however, for the dual notions of {irreducible and {
prime logics. We have only one implication in general: if L is {prime (i.e.,
i2I Li L only if Li L, for some i 2 I ) then it is {irreducible (i.e.,
L = i2I Li only if L = Li , for some i 2 I ). A formula ' is said to be
prime in NExtL0 if L0  ' is {prime in NExtL0.
PROPOSITION 1.5 Suppose a set of formulas ; is complete for NExtL0
and contains no distinct deductively equivalent in NExtL0 formulas. Then
; is an axiomatic basis for NExtL0 i every formula in ; is prime.
Although the denitions above seem to be quite simple, in practice it
is not so easy to understand whether a given logic is { or {prime, at
least at the syntactical level. However, these notions turn out to be closely
related to the following lattice-theoretic concept of splitting for which in the
next section we shall provide a semantic characterization.
A pair (L1  L2 ) of logics in NExtL0 is called a splitting pair in NExtL0
if it divides the lattice NExtL0 into two disjoint parts: the lter NExtL2
and the ideal L0  L1]. In this case we also say that L1 splits and L2 cosplits
NExtL0 .
THEOREM 1.6 A logic L1 splits NExtL0 i it is {prime in NExtL0 , and
L2 cosplits NExtL0 i it is {prime in NExtL0 . Moreover, the following
conditions are equivalent:
(i) (L1  L2 ) is a splitting pair in NExtL0
(ii) L1 is {prime in NExtL0 and L2 = fL 2 NExtL0 : L 6 L1 g
(iii) L2 is {prime in NExtL0 and L1 = fL 2 NExtL0 : L 6 L2 g.

L

L

T

T

L

L

T

L

T

T

L T

T

L

T
L

T
L

L

L

T

ADVANCED MODAL LOGIC

9

Splittings were rst introduced in lattice theory by Whitman 1943] and
McKenzie 1972] (see also Day 1977], Jipsen and Rose 1993]). Jankov
1963, 1968b, 1969], Blok 1976] and Rautenberg 1977] started using splittings in non-classical logic.
A few standard normal modal logics are listed in Table 1. Note that
our notations are somewhat di erent from those used in Basic Modal logic.
(A was introduced by Artemov see Shavrukov 1991]. The formulas Bn
bounding depth of frames are dened in Section 15 of Basic Modal Logic.)

1.2 Semantics

The algebraic counterpart of a logic L 2 NExtK is the variety of modal
algebras validating L (for denitions consult Section 10 of Basic Modal
Logic). Conversely, each variety (equationally denable class) V of modal
algebras determines the normal modal logic LogV = f' : 8A 2 V A j= 'g.
Thus we arrive at a dual isomorphism between the lattice NExtK and the
lattice of varieties of modal algebras, which makes it possible to exploit the
apparatus of universal algebra for studying modal logics.
It is often more convenient, however, to deal not with modal algebras
directly but with their relational representations discovered by Jonsson and
Tarski 1951] and now known as general frames. Each general frame F =
hW R P i is a hybrid of the usual Kripke frame hW Ri and the modal algebra
F+ = hP  W ; \  2 3i in which the operations 2 and 3 are uniquely
determined by the accessibility relation R: for every X 2 P 2W ,

2X = fx 2 W : 8y (xRy ! y 2 X )g 3X = ;2 ; X:
So, using general frames we can take advantage of both relational and algebraic semantics. To simplify notation, we denote general frames of the form
F = W R 2W by F = hW Ri. Such frames will be called Kripke frames.
Given a class of frames C , we write LogC to denote the logic determined by
C , i.e., the set of formulas that are valid in all frames in C  it is called the
logic of C . If C consists of a single frame F, we write simply LogF.
Basic facts about duality between frames and algebras can be found in the
chapters Basic Modal Logic and Correspondence Theory. Here we remind
the reader of the denitions that will be important in what follows.
A frame G = hV S Qi is said to be a generated subframe of a frame
F = hW R P i if V W is upward closed in F, i.e., x 2 V and xRy imply
y 2 V , S = R V and Q = fX \ V : X 2 P g. The smallest generated
subframe G of F containing a set X W is called the subframe generated
by X . A frame F is rooted if there is x 2 W |a root of F|such that the
subframe of F generated by fxg is F itself.





10

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

D
T
KB
K4
K5
Altn
D4
S4
GL
Grz
K4:1
K4:2
K4:3
S4:1
S4:2
S4:3
Triv
Verum
S5
K4B
A
Dum
K4BWn
K4BDn
K4nm

=
=
=
=
=
=
=
=
=
=
=
=
=
=
=
=
=
=
=
=
=
=
=
=
=

K  2p ! 3p
K  2p ! p
K  p ! 23p
K  2p ! 22p
K  32p ! 2p
K  2p1 _ 2(p1 ! p2) _ : : : _ 2(p1 ^ : : : ^ pn ! pn+1)
K4  3>
K4  2p ! p
K4  2(2p ! p) ! 2p
K  2(2(p ! 2p) ! p) ! p
K4  23p ! 32p
K4  3(p ^ 2q) ! 2(p _ 3q)
K4  2(2+ p ! q) _ 2(2+ q ! p)
S4  23p ! 32p
S4  32p ! 23p
S4  2(2p ! q) _ 2(2q ! p)
K4  2p $ p
K4  2p
S4  p ! 23p
K4  p ! 23p
GL  22p ! 2(2+ p ! q) _ 2(2+ q ! p)
S4  2V(2(p ! 2p)W! p) ! (32p ! p)
K4  ni=0 3pi ! 0i6=jn 3(pi ^ (pj _ 3pj ))
K4  Bn
K4  2n p ! 2mp for 1  m < n

Table 1. A list of standard normal modal logics.

ADVANCED MODAL LOGIC

11

A map f from W onto V is a reduction (or p-morphism) of a frame
F = hW R P i to G = hV S Qi if the following three conditions are satised
for all x y 2 W and X 2 Q
(R1)
xRy implies f (x)Sf (y)
(R2)
f (x)Sf (y) implies 9z 2 W (xRz ^ f (z ) = f (y))
(R3)
f ;1 (X ) 2 P .
The operations of reduction and generating subframes are relational counterparts of the algebraic operations of forming subalgebras and homomorphic images, respectively, and so preserve validity.
A frame F = hW R P i is dierentiated if, for any x y 2 W ,
x = y i 8X 2 P (x 2 X $ y 2 X ):
F is tight if
xRy i 8X 2 P (x 2 2X ! y 2 X ):
Those frames that are both di erentiated and tight are called rened. A
frame F is said to be compactTif every subset X of P with the nite intersection property (i.e., with X 0 =
6  for any nite subset X 0 of X ) has
non-empty intersection. Finally, rened and compact frames are called descriptive. A characteristic property of a descriptive F is that it is isomorphic
to its bidual (F+ )+ . The classes of all di erentiated, tight, rened and descriptive frames will be denoted by DF , T , R and D, respectively.
When representing frames in the form of diagrams,
we denote by  ir
reexive points, by  reexive ones, and by  two-point clusters. An arrow
from x to y means that y is accessible from x. If the accessibility relation
is transitive, we draw arrows only to the immediate successors of x.
EXAMPLE 1.7 (Van Benthem 1979) Let F = hW R P i be the frame whose
underlying Kripke frame is shown in Fig. 1 (! + 1 sees only ! and the
subframe generated by ! is transitive) and X W is in P i either X is
nite and ! 2= X or X is conite in W and ! 2 X . It is easy to see that
P is closed under \, ; and 3. Clearly, F is rened. Suppose X is a subset
of P with Tthe nite intersection property. If X contains a nite set Tthen
obviously X =
6 . And if X consists of only innite sets then ! 2 X .
Thus, F is descriptive.
A frame F is said to be {-generated, { a cardinal, if its dual F+ is
a {-generated algebra.4 Each modal logic L is determined by the free
nitely generated algebras in the corresponding variety, i.e., by the Tarski{
Lindenbaum (or canonical) algebras AL(n) for L in the language with n <
4 An algebra is said to be { -generated if it contains a set X of cardinality  { such
that the closure of X under the algebra's operations coincides with its universe.

12

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

nontransitive

transitive

! + 1-!   2 -1 -0
Figure 1.

! variables. Their duals are denoted by FL(n) = hWL (n) RL (n) PL (n)i
and called the universal frames of rank n for L. Analogous notation and
terminology will be used for the free algebras AL({) with { generators.
Note that hWL ({) RL ({)i is (isomorphic to) the canonical Kripke frame
for L with { variables (dened in Section 11 of Basic Modal Logic) and
PL ({) is the collection of the truth-sets of formulas in the corresponding

canonical model. Unless otherwise stated, we will assume in what follows
that the language of the logics under consideration contains ! variables.
An important property of the universal frame of rank { for L is that
every descriptive {0 -generated frame for L, {0  {, is a generated subframe
of FL ({). Thus, the more information about universal frames for L we have,
the deeper our knowledge about the structure of arbitrary frames for L and
thereby about L itself.
Although in general universal frames for modal logics are very complicated, considerable progress was made in clarifying the structure of the
upper part (points of nite depth) of the universal frames of nite rank
for logics in NExtK4. The studies in this direction were started actually
by Segerberg 1971]. Shehtman 1978a] presented a general method of constructing the universal frames of nite rank for logics in NExtS4 with the
nite model property. Later similar results were obtained by other authors
see e.g. Bellissima 1985]. The structure of free nitely generated algebras
for S4 was investigated by Blok 1976].
Let us try to understand rst the constitution of an arbitrary transitive
rened frame F = hW R P i with n generators G1  : : :  Gn 2 P . Dene V
to be the valuation of the set of variables # = fp1 : : :  pn g in F such that
x j= pi i x 2 Gi . Say that points x and y are #-equivalent, x  y in
symbols, if the same variables in # are true at them for X Y W we
write X  Y if every point in X is #-equivalent to some point in Y and
vice versa. Let d(F) denote the depth5 of F if F is of innite depth, we
write d(F) = 1. For d < d(F), W =d and W >d are the sets of all points in F
of depth d and > d, respectively W <d , W d, etc. are dened analogously.
Fd is the subframe of F generated by W d . The set of all successors
(predecessors) of points in a set X W is denoted by X " (respectively,
5

In Section 15 of Basic Modal Logic d(F) was called the rank of F.

ADVANCED MODAL LOGIC

13

X #) in the transitive case X " = X "  X and X # = X #  X are then the
upward and downward closure operations. A set X is said to be a cover for
a set Y in F if Y X #. A point x is called an atom in F if fxg 2 P .
THEOREM 1.8 Suppose F = hW R P i is a transitive rened n-generated
frame, for some n < !. Then
(i) each cluster in F contains  2n points
(ii) for every nite d  d(F), W =d is a cover for W d and contains at
most cn (d) distinct clusters, where
cn (1) = 2n + 22n ; 1 cn (m + 1) = cn (1)  2cn(1)+:::+cn (m) 
(iii) every point of nite depth in F is an atom.
Proof (i) follows from the di erentiatedness of F and the obvious fact that
precisely the same formulas (in p1  : : :  pn ) are true under V at #-equivalent
points in the same cluster.
The proof of (ii) proceeds by induction on d. Let x 2 W >d. Since F is
transitive and W d is nite (by the induction hypothesis), there exists a
non-empty upward closed in W >d set X (i.e., X = X " \ W >d) such that
x 2 X #, points in X see exactly the same points of depth  d and either
8u v 2 X 9w 2 u" \ X w  v
(1)

or

8u v 2 X (u  v ^ :uRv):
(2)
Such a set X is called d-cyclic it is nondegenerate if (1) holds and degenerate
otherwise. One can readily show that the same formulas are true at #equivalent points in X . Since F is rened, X is then a cluster of depth
d + 1. Thus, W >d W =d+1 #. The upper bound for the number of distinct
clusters of depth d + 1 follows from the di erentiatedness of F and the
denition of d-cyclic sets.
To establish (iii), for every point x of depth d + 1 one can construct
by induction on d a formula (expressing the denition of the d-cyclic set
containing x) which is true in F under V only at x. For details consult
Chagrov and Zakharyaschev 1997].
2

It is fairly easy now to construct the (generated) subframe F<K41 (n) of the
universal frame of rank n for K4 consisting of nite depth points. Indeed,
FK4 (n) is n-generated, rened and so has the form as described in Theorem 1.8. On the other hand, it is universal and contains any n-generated
descriptive frame as a generated subframe, which means roughly that it contains all possible points of nite depth that can exist in n-generated rened
frames.

14

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

p1

FS42 (1)

P
H
~
a
PP
a
Q
P
bH

P
Q
c
c
# AC
aP
bH
P
;
Q
Q
PP ##


C
S
@
;

S
@

A
c

#

a
c

b
;
aP
 CAS@Q
P
 S@Q

  CA
c P
#;
P
a
cH
#
bH
P
P
a
P
a
  C AS@Q
P
PPS@Q
bHH 
;  C A
cQ
#
c
# ;
Q
bH
P
;Q
@P
CA
aP
cQ

C A S@
#c
   aP
SP
P
;  
b #H
a
P
Q
P
P
#;
a
c
b H 
@
P
C A
 
C A#S;@
cQ

S
a
P
Q
Q

P
b
c Q
#a
H H
P
a
c
#
P

;
A

@
P
C
Q
 
C

S
@

S
;
P
b
c
P
caP
#
HHC AA
b
QP
 # a
PP
A S @
P
 
C 
 cQ
b
# ;
PP
Q
Q # S;@ caa
P
H
P
P
C HA
Qbb
 ~ # ~; C A~ S @c~#Q; S @~ c a
~P

p1

p1

p1

p1

p1

Figure 2.
More precisely, assuming that each point is assigned the set of variables
in # that are true at it, we begin constructing a frame GK4 (n) nby putting
at depth 1 in it 2n non-#-equivalent degenerate clusters and 22 ; 1 non#-equivalent non-degenerate clusters with  2n non-#-equivalent points.
Suppose that GK4d (n) is already constructed. Then for every antichain a of
clusters in GK4d (n) containing at least one cluster of depth d and di erent
from a singleton
with a non-degenerate cluster, we add to GK4d (n) copies
n
n
2
of all 2 + 2 ; 1 clusters of depth 1 so that they would be inaccessible
from each other and could see only the clusters in a and their successors.
And for every singleton a = fC g with a non-degenerate cluster C , we add
to GK4d (n) copies of those clusters of depth 1 which are not #-equivalent to
any subset of C (otherwise the frame will not be rened) so that again they
would be mutually inaccessible and could see only C and its successors in
GK4d (n).
Let NK4 (n) = hGK4 (n) UK4 (n)i be the resulting model (the relational
component of GK4 (n) is completely determined by the construction and its
set of possible values is the collection of the truth-sets of formulas in GK4 (n)
under UK4 (n)). It is not hard to show that GK4 (n) is atomic. Moreover, for
every point x in this frame one can construct a formula '(p1  : : :  pn ) such
that x 6j= ' and, for any frame F, F 6j= ' i there is a generated subframe of F
reducible to the subframe of GK4 (n) generated by x. It follows in particular
that GK4 (n) is rened. Thus, every GK4d (n) is a generated subframe of
FK4 (n). On the other hand, by Theorem 1.8, FK4 (n) contains no clusters
of depth  d di erent from those in GK4d (n) and so F<K41 (n) is isomorphic to
GK4 (n). It worth noting also that, since K4 has the nite model property,
it is characterized by F<K41 (n), and so FK4 (n) is isomorphic to the bidual of
F<K41 (n).
The universal frame FL(n) for an arbitrary consistent logic L in NExtK4
is a generated subframe of FK4 (n). It can be constructed by removing

ADVANCED MODAL LOGIC

15

from FK4 (n) those points at which some formulas in L are refuted (under
VK4 (n)). For example, F<S41(n) is obtained by removing from F<K41 (n)
all irreexive points and their predecessors. In other words, F<S41 (n) can
be constructed in the same way as F<K41 (n) but using only non-degenerate
clusters. FS42 (1) (the corresponding model, to be more exact) is shown in
Fig. 2, where ~ denotes the cluster with two points at one of which p1 is
1 (n) and F<1 (n), we take only simple clusters and
true. To construct F<Grz
GL
degenerate clusters, respectively.
In general, this method of constructing universal frames does not work
for logics with nontransitive frames. However, using the fact that K is
characterized by the class of nite intransitive irreexive trees (see Section
13 of Basic Modal Logic), in the same manner as above one can construct
an intransitive irreexive model characterizing K and such that FK (n) is
isomorphic to the bidual of the frame associated with this model.
Let us consider now the semantical meaning of splittings. In view of the
following observation we focus attention only on splittings by the logics of
nite rooted frames.
THEOREM 1.9 If L1 splits NExtL0 and L0 has the nite model property
then L1 = LogF, for some nite rooted frame F validating L0.
Proof Since L2 in the splitting pair (L1 L2) is a proper extension of L0,
there is a nite frame G such that G j= L0 and G 6j= L2 . It follows that
LogG L1 . As we shall see later (Corollary 1.86), every extension of a
tabular logic is also tabular. So L1 = LogF for some nite F j= L0. And
since L1 is {prime, F must be rooted.
2
We say that a frame F splits NExtL0 if LogF splits NExtL0. The logic L2
of the splitting pair (LogF L2 ) is denoted by L0 =F and called the splitting
of NExtL0 by F. This notation reects the fact that L2 is the smallest logic
in NExtL0 which is not validated by F.
EXAMPLE 1.10 We show that D = K=. Recall that D = K  3> is
characterized by the class of serial frames (in which every point has a successor). So if  j= L then L Log otherwise no frame for L has a dead
end, which means that 3> 2 L and D L. The inconsistent logic For can
be represented as D=.
To illustrate some applications of splittings we require a few denitions.
Given L 2 NExtL0 , we say that the axiomatization problem for L above
L0 is decidable if the set f' : L0  ' = Lg is recursive. L is strictly
Kripke complete above L0 if no other logic in NExtL0 has exactly the same
Kripke frames as L. If all frames in a set F split NExtL0, we call the logic
fL0 =F : F 2 Fg the union-splitting of NExtL0 and denote it by L0 =F .

T

L

16

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

EXAMPLE 1.11 Grz is not a splitting of NExtS4. However, it is a union
6


splitting: Grz = S4=f   g. S4:1 = S4= . A frame may split the
lattice NExtL0=F but not NExtL0 : e.g.  splits NExtK= but does not
split NExtK.
THEOREM 1.12 Suppose L 2 NExtL0 and L = (: : : (L0 =F1 )= : : :)=Fn , for
a sequence F1  : : :  Fn of sets of nite rooted frames.
(i) If F = ni=1 Fi is nite and L is decidable then the axiomatization
problem for L above L0 is decidable. More precisely,
f' : L0  ' = Lg = f' 2 L : 8F 2 F F 6j= 'g:
(ii) If L is Kripke complete then L is strictly Kripke complete above L0 .
(iii) The immediate predecessors of L in NExtL0 are precisely the logics
L \ LogF, for F 2 F such that F is not a reduct of a generated subframe of
another frame in F .
Proof (i) is left to the reader as an easy exercise.
(ii) Let L0 be a logic in NExtL0 with the same Kripke frames as L. Then
obviously L0 L. On the other hand, the frames in F do not validate L0
and so L L0.
(iii) If L0 is an immediate predecessor of L in NExtL0 then F j= L0 , for
some F 2 F . Therefore, L0 L \ LogF  L and so L0 = L \ LogF. Suppose
now that F is not a reduct of a generated subframe of another frame in F
and L \ LogF L0  L. Then L0 LogF0 for some F0 2 F , and hence
F0 = F, L0 = L \ LogF.
2
As follows from Theorem 1.12 and Example 1.10, For has exactly two
immediate predecessors Verum = Log and Triv = Log (and each consistent normal modal logic is contained in one of them). This result is known
as Makinson's 1971] Theorem. Moreover, the axiomatization problem for
For is decidable, i.e., there is an algorithm which decides, given a formula
' whether K  ' is consistent. Likewise, since D = K  3> is decidable,
there is an algorithm recognizing, given ', whether D = K  '. We shall
see later in Section 4.4 that in fact not so many properties of logics are
decidable (e.g. the axiomatization problem for K  :3> is undecidable
see Theorem 4.15) and that Theorem 1.12 (i) provides the main method for
proving decidability results of this type.
To determine whether a nite rooted frame F = hW Ri splits NExtL0,
we need the formulas dened below:
F = fpx ! 3py : x y 2 W xRyg 
fpx ! :3py : x y 2 W :xRyg 
fpx ! :py : x y 2 W x 6= yg

S

ADVANCED MODAL LOGIC

^

_

17

F=
F  F = F ^ fpx : x 2 W g:
The meaning of F is explained by the following lemma, in which

2<! ' = f2n ' : n < !g:
LEMMA 1.13 For any nite F with root r, the set of formulas fpr g 2<! F
is satisable in a frame G i there is a generated subframe H of G reducible
to F. Moreover, if F is cycle free (i.e., contains no path from a point to
itself) then ! can be replaced by n = d(F) + 1.

Proof ()) Suppose fpr g  2<! F is satised at a point u in G. It is not

hard to check that the map f dened by f (v) = x i v j= px is a reduction of
the subframe H of G generated by u to F. If F is cycle free and fpr g 2<! F
is satised at u then d(H) = d(F). For otherwise an ascending chain of n +1
points starts from u and so F must contain a cycle.
(() Let f be a reduction of H to F. Dene a valuation in G so that
v j= px i v 2 f ;1 (x). The reader can readily verify that under this
valuation fpr g  2<! F is true at any point in f ;1 (r).
2
LEMMA 1.14 For every logic L 2 NExtK and every nite rooted frame F,
F j= L i 8n < ! 2n F ! :pr 62 L.

Proof The implication ()) follows from Lemma 1.13. Suppose now that

2n F ! :pr 62 L, for every n < !. Then the set fpr g  2<! F is Lconsistent and so it is satised in a frame G for L. By Lemma 1.13, a
generated subframe of G is reducible to F, and hence F j= L.
2
We are now in a position to characterize nite frames that split NExtL0

and to axiomatize splittings.

THEOREM 1.15 Suppose F is a nite frame with root r and L0 2 NExtK.
Then F splits NExtL0 i there is n < ! such that, for every frame G j= L0 ,
2n F ^ pr is satisable in G only if 2m F ^ pr is satisable in G for every
m > n. In this case L0 =F = L0  2n F ! :pr .

Proof ()) Suppose otherwise and consider a sequence fGn : n < !g of

frames for L0 such that 2n F ^ pr is satisable in Gn but 2m F ^ pr is
not satised, for some m > n. By Lemma 1.14, the former condition implies
n<! LogGn LogF, while the latter means that F 6j= LogGn , for every
n < !, contrary to LogF being {prime.
(() We show that L0 =F = L0  2n F ! :pr . Suppose L 6 LogF.
Then, by Lemma 1.14, there is m < ! such that 2m F ! :pr 2 L. It
follows that 2n F ! :pr 2 L and so L0  2n F ! :pr L.
2

T

T

18

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

For more general versions of this criterion consult Kracht 1990] and
Wolter 1993].
COROLLARY 1.16 (Rautenberg 1980) Suppose that L0 2 NExt(Ktran ),
for some n < !. Then every nite rooted frame F for L0 splits NExtL0 and
L0 =F = L0  2n F ! :pr .
In particular, every transitive nite rooted frame splits NExtK4. This
result may also be obtained using the fact that all nite subdirectly irreducible algebras split the lattice of subvarieties of a variety with equationally
denable principal congruences (see Blok and Pigozzi 1982]). However, not
every frame splits NExtK.
THEOREM 1.17 (Blok 1978) A nite rooted frame F splits NExtK i it is
cycle free. In this case K=F = K  2n F ! :pr , where n = d(F).

Proof That frames with cycles do not split NExtK follows from the fact
that K is characterized by cycle free nite rooted frames. And the converse
is an immediate consequence of Lemma 1.13 and Theorem 1.15.

2

An element x 6= 0 of a complete lattice L is called an atom in L if the zero
element 0 in L is the immediate predecessor of x, i.e., there is no y such that
0 < y < x. Splittings turn out to be closely related to the existence of atoms
in nitely generated free algebras see Blok 1976], Bellissima 1984, 1991]
and Wolter 1997c]. We demonstrate the use of splittings by the following
THEOREM 1.18 (Blok 1980a) The lattice NExtK has no atoms.

Proof If a logic L is an atom in NExtK, it is L{prime. It follows that
L cosplits NExtK and the logic L0 = LogF in the splitting pair (L0  L)
has no proper predecessor that splits NExtK. Add a new irreexive root
to F. By Theorem 1.17, the resulting frame G splits NExtK, and clearly
LogG  LogF, which is a contradiction.

2

A logic is linked with its semantics via completeness theorems. The most
general completeness theorem states that every consistent normal modal
logic is characterized by the class of (descriptive) frames validating it. Or,
if we want to characterize the consequence relations `L and `L, we can use
the following
THEOREM 1.19 (i) For L 2 NExtK, ; `L ' i for any model M based on
a frame for L and any point x in M, x j= ; implies x j= '.
(ii) For L 2 NExtK, ; `L ' i for any model M based on a frame for
L, M j= ; implies M j= '.

ADVANCED MODAL LOGIC

19

However, usually more specic completeness results are required. What
is the \geometry" of frames for a given logic? Are Kripke or even nite
frames enough to characterize it? Questions of this sort will be addressed
in the next several sections.

1.3 Persistence
The structure of Kripke frames for many standard modal logics can be
described by rather simple conditions on the accessibility relation which
are expressed in the rst order language with equality and a binary (accessibility) predicate R. (This observation was actually the starting point
of investigations in Correspondence Theory studying the relation between
modal and rst (or higher) order languages see Chapter 4 of this volume.)
Moreover, in many cases it turns out that the universal frame FL(!) for such
a logic L also satises the corresponding rst order condition . Since says
nothing about sets of possible values in PL (!), it follows immediately that
the canonical (Kripke) frame FL (!) also satises and so characterizes
L. Thus we obtain a completeness theorem of the form:

' 2 L i F j= ' for every Kripke frame F satisfying .
This method of establishing Kripke completeness, known as the method
of canonical models, is based essentially upon two facts: rst, that L is
characterized by its universal frame FL(!) and second, that L is \persistent"
under the transition from FL(!) to its underlying Kripke frame. Of course,
instead of FL(!) we can take any other class of frames C with respect to
which L is complete and try to show that L is C {persistent in the sense
that, for every F = hW R P i in C , if F j= L then F = hW Ri validates L
as well.
PROPOSITION 1.20 If a logic is both C {complete and C {persistent, then it
is complete with respect to the class f F : F 2 Cg of Kripke frames.
It follows in particular that L is Kripke complete whenever it is DF {,
or R{, or D{persistent. Since every descriptive frame for L is a generated
subframe of a suitable universal frame for L, L is D{persistent i it is
persistent with respect to the class of its universal frames. It is an open
problem, however, whether canonicity, i.e., FL (!){persistence, implies D{
persistence. Here are two simple examples.
THEOREM 1.21 (van Benthem 1983) A logic is persistent with respect to
the class of all general frames i it is axiomatizable by a set of variable free
formulas.

20

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

It is easily checked that a Kripke frame validates Altn i no point in it
has more than n distinct successors (see Segerberg 1971]).
THEOREM 1.22 (Bellissima 1988) Every L 2 NExtAltn is DF {persistent,
for any n < !.
Proof The proof is based on the fact that, for any di erentiated frame
F = hW R P i, any nite X W , and any y 2 X , there is Y 2 P such
that X \ Y = fyg. It follows that at most n distinct points are accessible
from every point in a di erentiated frame for L in particular, Altn is DF {
persistent. Suppose now that a formula ' 2 L is refuted at a point x under a
valuation V in F, F a di erentiated frame for L. Let X be the set of points
accessible from x in  md(') steps.6 Since X is nite, there is a valuation
U in F such that U(p) \ X = V(p), for every variable p. Consequently, ' is
false in F at x under U, which is a contradiction.
2
The proof of Fine's 1974c] Theorem that all logics of nite width, i.e.,
logics in NExtK4BWn , for n < !, are Kripke complete (a sketch can be
found in Section 18 of Basic Modal Logic) may also be regarded as a proof
of persistence. Recall that a point x in a transitive frame F = hW R P i
is called non-eliminable (relative to R) if there is X 2 P such that x 2 X
but no proper successor of x is in X (in other words, x is maximal in
X ) in this case we write x 2 maxR X . Denote by Wr the set of all noneliminable points in F and put Fr = hWr  Rr  Pr i, where Rr = R Wr ,
Pr = fX \ Wr : X 2 P g. (Fine called the frame Fr reduced.)
THEOREM 1.23 (Fine 1985) Let F = hW R P i be a transitive descriptive
frame and x 2 X 2 P . Then (i) there exists a point y 2 maxR X \ x" and
(ii) Fr is a rened frame whose dual F+r is isomorphic to F+ .
Proof (i) Suppose otherwise, i.e., there is no maximal point in X \ x".
Let Y be a maximal chain of points in X \ x" (that it exists follows from
Zorn's Lemma) and X = fZ 2 P : 9y 2 Y y " \ Y Z g. Clearly, X is
non-empty and has the nite intersection property (because X \ x" has no
maximal point). By compactness, we then have a point z in X which, by
tightness, is maximal in Y , contrary to X \ x" having no maximal point.
(ii) is a consequence of (i).
2
It follows that to establish the Kripke completeness of a logic L 2 NExtK4
it is enough to show that it is persistent with respect to the class
RE = fFr : F a nitely generated descriptive frameg:
That is what Fine 1974c] actually did for logics of nite width.

T

6 Here md('), the modal degree of ', is the length of the longest chain of nested modal
operators in '.

ADVANCED MODAL LOGIC

21

THEOREM 1.24 (Fine 1974c) All logics of nite width are RE {persistent
and so Kripke complete.
Let us return, however, to the method of canonical models. Having tried
it for a number of standard systems, Lemmon and Scott 1977] found a
rather general sucient condition for its applicability and put forward a
conjecture concerning a further extension (which was proved by Goldblatt
1976b]). This direction of completeness (and correspondence) theory culminated in the theorem of Sahlqvist 1975] who proved an optimal (in a sense)
generalization of the condition of Lemmon and Scott 1977]. To formulate it
we require the following denition. Say that a formula is positive (negative )
if it is constructed from variables (negated variables) and the constants >,
? using ^, _, 3 and 2.
THEOREM 1.25 (Sahlqvist 1975) Suppose ' is a formula which is equivalent in K to a formula of the form 2k ( ! ), where k 0,  is positive
and  is constructed from variables and their negations, ? and > with the
help of ^, _, 2 and 3 in such a way that no 's subformula of the form
1 _ 2 or 31, containing an occurrence of a variable without :, is in the
scope of some 2. Then one can eectively construct a rst order formula
(x) in R and = having x as its only free variable and such that, for every
descriptive or Kripke frame F and every point a in F,
(F a) j= ' i F j= (x)a]:
(Here (F a) j= ' means that ' is true at a in F under any valuation.)

Proof We present a sketch of the proof found by Sambin and Vaccaro

1989]. Given a formula '(p1  : : :  pn ), a frame F = hW R P i and sets
X1  : : :  Xn 2 P , denote by '(X1  : : :  Xn ) the set of points in F at which '
is true under the valuation V dened by V(pi ) = Xi , i.e., '(X1  : : :  Xn ) =
V('). Using this notation, we can say that
(F x) j= '(p1  : : :  pn ) i 8X1 : : :  Xn 2 P x 2 '(X1  : : :  Xn ):
EXAMPLE 1.26 Let us consider the formula 2p ! p and try to extract
a rst order equivalent for it in the class of tight frames directly from the
equivalence above and the condition of tightness. For every tight frame
F = hW R P i we have:
(F x) j= 2p ! p i
i
i

8X 2 P x 2 (2X ! X )
8X 2 P (x 2 2X ! x 2 X )
8X 2 P (x" X ! x 2 X ):

22

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

To eliminate the variable X ranging over P , we can use two simple observations. The rst one is purely set-theoretic:
8X 2 P (Y X ! x 2 X ) i x 2 fX 2 P : Y X g:
(3)
And the second one is just a reformulation of the characteristic property of
tight frames:
fX 2 P : x" X g = x":
(4)
With the help of (3) and (4) we can continue the chain of equivalences above
with two more lines:
(F x) j= 2p ! p i : : :
i x 2 fX 2 P : x" X g
i x 2 x":
Thus, F j= 2p ! p i 8x x 2 x" i 8x xRx.
The proof of Sahlqvist's Theorem is a (by no means trivial) generalization
of this argument. Dene by induction x"0 = fxg, x"n+1 = (x"n )", and notice
that in (4) we can replace x" by any term of the form x1"n1  : : :  xk"nk ,
thus obtaining the equality
fX 2 P : x1"n1  : : :  xk"nk X g = x1"n1  : : :  xk"nk
(5)

\

\

T

\

which holds for every tight frame F = hW R P i, all x1  : : :  xk 2 W and all
n1  : : :  nk 0.
A frame-theoretic term x1"n1  : : :  xk"nk with (not necessarily distinct)
world variables x1  : : :  xk will be called an R-term. It is not hard to see
that for any R-term T , the relation x 2 T on F = hW R P i is rst order
expressible in R and =. Consequently, we obtain
LEMMA 1.27 Suppose '(p1  : : :  pn ) is a modal formula and T1 : : :  Tn are
R-terms. Then the relation x 2 '(T1  : : :  Tn ) is expressible by a rst order
formula (in R and =) having x as its only free variable.
Syntactically, R-terms with a single world variable correspond to modal
formulas of the form 2m1 p1 ^ : : : ^ 2mk pk with not necessarily distinct
propositional variables p1  : : :  pk . Such formulas are called strongly positive.
By induction on the construction of ', one can prove the following
LEMMA 1.28 Suppose '(p1  : : :  pn ) is a strongly positive formula containing all the variables p1  : : :  pn and F = hW R P i is a frame. Then one
can eectively construct R-terms T1  : : :  Tn (of one variable x) such that
for any x 2 W and any X1  : : :  Xn 2 P ,
x 2 '(X1  : : :  Xn ) i T1 X1 ^ : : : ^ Tn Xn :

ADVANCED MODAL LOGIC

23

Now, trying to extend the method of Example 1.26 to a wider class of
formulas, we see that it still works if we replace the antecedent 2p in 2p ! p
with an arbitrary strongly positive formula . As to generalizations of the
consequent, let us take rst an arbitrary formula  instead of p and see
what properties it should satisfy to be handled by our method.
Thus, for a modal formula ( ! )(p1  : : :  pn ) with strongly positive 
and a tight frame F = hW R P i, we have:
(F x) j=  !  i 8X1 : : :  Xn 2 P (x 2 (X1  : : :  Xn ) !
x 2 (X1  : : :  Xn ))
i 8X1 : : :  Xn 2 P (T1 X1 ^ : : : ^ Tn Xn !
x 2 (X1  : : :  Xn ))
i 8X1 : : :  Xn;1 2 P (T1 X1 ^ : : : ^ Tn;1 Xn;1 !
8Xn 2 P (Tn Xn ! x 2 (X1  : : :  Xn ))):
(3) does not help us here, but we can readily generalize it to
8X 2 P (Y X ! x 2 (: : :  X : : :)) i
x 2 f(: : :  X : : :) : Y X 2 P g:
(6)

\

So
(F x) j=  !  i 8X1 : : :  Xn;1 2 P (T1 X1 ^ : : : ^ Tn;1 Xn;1 !
x 2 f(X1  : : :  Xn ) : Tn Xn 2 P g):

\

But now (4) and (5) are useless. In fact, what we need is the equality

\f(: : :  X : : :) : T X 2 P g =
\
(: : :  fX 2 P : T X g : : :)

(7)

which, with the help of (5), would give us

\f(: : :  X : : :) : T X 2 P g = (: : :  T : : :):

(8)

Of course, (7) is too good to hold for an arbitrary , but suppose for a
moment that our  satises it. Then we can eliminate step by step all the
variables X1  : : :  Xn like this:
(F x) j=  !  i 8X1 : : :  Xn;1 2 P (T1 X1 ^ : : : ^ Tn;1 Xn;1 !
x 2 (X1  : : :  Xn;1  Tn))
i : : : (by the same argument)
i x 2 (T1  : : :  Tn):

24

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

And the last relation can be e ectively rewritten in the form of a rst order
formula (x) in R and = having x as its only free variable. So, nally we
shall have F j=  !  i 8x (x).
Now, to satisfy (7),  should have the property that all its operators
distribute over intersections. Clearly, ! and : are not suitable for this goal.
But all the other operators turn out to be good enough at least in descriptive
and Kripke frames. So we can take as  any positive modal formula. The
main property of a positive formula '(: : :  p : : :) is its monotonicity in every
variable p which means that, for all sets X , Y of worlds in a frame, X Y
implies '(: : :  X : : :) '(: : :  Y : : :).
To prove that all positive formulas satisfy (7) in Kripke frames and descriptive frames, recall that 2 distributes over arbitrary intersections in
any frame. As to 3, we have the following lemma in which a family X of
non-empty subsets of some space W is called downward directed if for all
X Y 2 X there is Z 2 X such that Z X \ Y .
LEMMA 1.29 (Esakia 1974) Suppose F = hW R P i is a descriptive frame.
Then for every downward directed family X P ,

3

\ X = \ 3X:

X 2X

X 2X

Using Esakia's Lemma, by induction on the construction of ' one can
prove
LEMMA 1.30 Suppose that F = hW R P i is a Kripke or descriptive frame
and '(p : : :  q : : :  r) is a positive formula. Then for every Y W and all
U : : :  V 2 P ,

\f'(U : : :  X : : :  V ) : Y

X 2 Pg =
\
'(U : : :  fX 2 P : Y

X g : : :  V ):

(9)

It follows from this lemma and considerations above that Sahlqvist's Theorem holds for formulas ' =  !  with strongly positive  and positive
. The remaining part of the proof is purely syntactic manipulations with
modal and rst order formulas.
Notice that using the monotonicity of positive formulas, equivalence (6)
can be generalized to the following one: for every F = hW R P i, every
positive i (: : :  p : : :) and every xi 2 W ,
8X 2 P (Y

_ xi 2 i(: : :  X : : :)) i
_i xni 2 \fi(: : :  X : : :) : Y

X!



in

X 2 P g:

(10)

ADVANCED MODAL LOGIC

25

Say that a modal formula  is untied if it can be constructed from negative
formulas and strongly positive ones using only ^ and 3. If (p1  : : :  pn ) is
negative then : (p1  : : :  pn ) is clearly equivalent in K to a positive formula
we denote it by (:p1  : : :  :pn ).
LEMMA 1.31 Let (p1  : : :  pn ) be an untied formula and F = hW R P i a
frame. Then for every x 2 W and all X1  : : :  Xn 2 P ,

x 2 (X1  : : :  Xn ) i 9y1  : : :  yl (# ^

^ Ti Xi ^ ^ zj 2 j (X  : : :  Xn))

in

1

j m

where the formula in the right-hand side, eectively constructed from , has
only one free individual variable x, # is a conjunction of formulas of the form
uRv, Ti are suitable R-terms and j (p1  : : :  pn ) are negative formulas.

We are ready now to prove Sahlqvist's Theorem. To construct a rst order
equivalent for 2k ( ! ) supplied by the formulation of our theorem, we
observe rst that one can equivalently reduce  to a disjunction 1 _ : : : _ m
of untied formulas, and hence 2k ( ! ) is equivalent in K to the formula
2k (1 ! ) ^ : : : ^ 2k (m ! ). So all we need is to nd a rst order
equivalent for an arbitrary formula 2k ( ! ) with untied  and positive .
Let p1  : : : pn be all the variables in  and  and F = hW R P i a descriptive
or Kripke frame. Then, for any x 2 W , we have:
(F x) j= 2k ( ! ) i 8X1  : : :  Xn 2 P x 2 2k ( ! )(X1  : : :  Xn )
(by Lemma 1.31) i 8X1  : : :  Xn 2 P 8y (xRk y ! (9y1  : : :  yl (# ^
Ti Xi ^ zj 2 j (X1  : : :  Xn )) !

^

^

in

j m

y 2 (X1  : : :  Xn )))
^
i 8X1  : : :  Xn 2 P 8y y1 : : :  yl (#0 ^ Ti Xi ^

^ zj 2 j (X  : : :  Xn) ! y 2 (X i :n: :  Xn))


j m

1

1

where #0 = xRk y ^ #. Let j (p1  : : :  pn) = j (:p1  : : :  :pn ). We continue
this chain of equivalences as follows:
i

8y y1 : : :  yl (#0 ! 8X1 : : :  Xn 2 P (

_ zj 2 j (X  : : :  Xn)))

j m+1

1

^ Ti Xi !

in

26

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

(where m+1 (p1  : : :  pn ) = (p1  : : :  pn ) and zm+1 = y)
i

8y y1 : : :  yl (#0 !

_ zj 2 j (T  : : :  Tn))

j m+1

1

as follows from (10), Lemma 1.30 and equality (5). It remains to use
Lemma 1.27.
2
The formulas ' dened in the formulation of Theorem 1.25 are called
Sahlqvist formulas. It follows from this theorem that if L is a D{persistent
logic and ; a set of Sahlqvist formulas then L  ; is also D{persistent.
Moreover, L  ; is elementary (in the sense that the class of Kripke frames
for it coincides with the class of all models for some set of rst order formulas
in R and =) whenever L is so.
Other proofs of Sahlqvist's Theorem were found by Kracht 1993] and
Jonsson 1994] (the latter is based upon the algebraic technique developed in
Jonsson and Tarski 1951]). Venema 1991] extended Sahlqvist's Theorem to
logics with non-standard inference rules, like Gabbay's 1981a] irreexivity
rule. In Chagrov and Zakharyaschev 1995b] it is shown that there is a
continuum of Sahlqvist logics above S4 and that not all of them have the
nite model property (above T such a logic was constructed by Hughes
and Cresswell 1984]). As we shall see later in this chapter, there are even
undecidable nitely axiomatizable Sahlqvist logics in NExtK. It would be
of interest to nd out whether such logics exist above K4 or S4.
Kracht 1993] described syntactically the set of rst order equivalents of
Sahlqvist formulas. To formulate his criterion we require the fragment S of
rst order logic dened inductively as follows. Formulas of the form xRm y
are in S for all variables x y and every m < ! besides, if  0 are in S then
the formulas
8x 2 y"m  9x 2 y"m  ^ 0  and _ 0

are also in S . For simplicity we assume that all occurrences of quantiers
in a formula bind pairwise distinct variables. Call a variable y in a formula
2 S inherently universal if either all occurences of y are free in or
contains a subformula 8y 2 x"m 0 which is not in the scope of 9.
THEOREM 1.32 (Kracht 1993) For every rst order formula (x) (in R
and =) of one free variable x, the following conditions are equivalent:
(i) (x) is classically equivalent to a formula 0 (x) 2 S such that any subformula of the form yRm z of 0 (x) contains at least one inherently universal
variable
(ii) (x) corresponds to a Sahlqvist formula in the sense of Theorem 1.25.

ADVANCED MODAL LOGIC

27

Condition (i) is satised, for example, by the formula
8u 2 x" 8v 2 x" 9z 2 u" vRz
which corresponds to 32p ! 23p. On the other hand,
(x) = 9y 2 x" 8z 2 y" zR0y
does not satisfy (i). In fact, even relative to S4 the condition expressed by
(x) does not correspond to any Sahlqvist formula. Notice, however, that
S4  23p ! 32p is a D-persistent logic whose frames are precisely the
transitive and reexive frames validating 8x (x).
We conclude this section by mentioning two more important results connecting persistence and elementarity (the idea of the proof was discussed in
Section 22 of Basic Modal Logic.)
THEOREM 1.33 (i) (Fine 1975b, van Benthem 1980) If a logic L is characterized by a rst order denable class of Kripke frames then L is D{
persistent.
(ii) (Fine 1975b) If L is R-persistent then the class of Kripke frames for
L is rst order denable.
It is an open problem whether every D{persistent logic is determined by
a rst order denable class of Kripke frames for more information about
this and related problems consult Goldblatt 1995].

1.4 The degree of Kripke incompleteness
All known logics in NExtK of \natural origin" are complete with respect

to Kripke semantics. On the other hand, there are many examples of \articial" logics that cannot be characterized by any class of Kripke frames
(see Sections 19, 20 of Basic Modal Logic or the examples below). To understand the phenomenon of Kripke incompleteness Fine 1974b] proposed
to investigate how many logics may share the same Kripke frames with a
given logic L. The number of them is called the degree of Kripke incompleteness of L. Of course, this number depends on the lattice of logics under
consideration. The degree of Kripke incompleteness of logics in NExtK was
comprehensively studied by Blok 1978]. In this section we present the main
results of that paper following Chagrov and Zakharyaschev 1997].
By Theorem 1.12, all Kripke complete union-splittings of NExtK have
degree of incompleteness 1. And it turns out that no other union-splitting
exists.
THEOREM 1.34 (Blok 1978) Every union-splitting of NExtK has the nite
model property.

28

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

nontransitive

x1 -x11


6

xk;1 xk

     1 - 1

x1 -x2


6

x

x1

x1

x1

xk

xk

xk

     n - 1 - 2    n    1 - 2    n

(a)

(b)
Figure 3.

Proof Let F be a class of nite rooted cycle free frames. We prove that
L = K=F has the nite model property using a variant of ltration, which

is applied to an n-generated rened frame F = hW R P i for L refuting a
formula '(p1  : : :  pn ) under a valuation V.
Since F is di erentiated, for every m 1 there are only nitely many
points x in F such that x j= 2m ? ^ :2m;1 ? we shall call them points of
type m. Given
Sub', Sub' the set of all subformulas in ', we put
m = m if m is the minimal number such that a point in F is of type  m
whenever x j= and the formulas in Sub' ; are false at x (under V) if
no such m exists, we put m = 0. Let
k = maxfm :
Sub'g ; = Sub(' ^ 2k ?):
Now we divide F into two parts: W1 consisting of points of type  k and
W2 = W ; W1 . For x y 2 W , put x  y if either x y 2 W1 and x = y
or x y 2 W2 and exactly the same formulas in ; are true at x and y. Let
N = hG Ui be the smallest ltration (see Section 12 of Basic Modal Logic)
of M = hF Vi through ; with respect to . Since W1 is nite, G is also
nite and, by the Filtration Theorem, (M x) j=  i (N x]) j= , for every
 2 ;. So it remains to show that G j= L. Notice that x] in G is of type
m  k i x has type m in F. Moreover, there is no x] of type l > k. For
otherwise x 6j= 2k ? and m = 0 for = f 2 Sub' : x j= g, which
means that arbitrary long chains (of not necessarily distinct points) start
from x], contrary to x] being of type l. Thus G consists of two parts:
points of type  k, which form the generated subframe hW1  R W1 i of F,
and points involved in cycles. Since F j= L and frames in F are cycle free,
it follows from Lemma 1.13 and Theorem 1.17 that G j= L.
2
THEOREM 1.35 (Blok 1978) If a logic L is inconsistent or a union-splitting
of NExtK, then L is strictly Kripke complete. Otherwise L has degree of
Kripke incompleteness 2@0 in NExtK.

Proof That For is strictly complete follows from Example 1.10 and Theorem 1.12. Suppose now that a consistent L is not a union-splitting and L0

ADVANCED MODAL LOGIC

29

is the greatest union-splitting contained in L. Since L0 has the nite model
property, there is a nite rooted frame F = hW Ri for L0 refuting some
' 2 L and such that every proper generated subframe of F validates L.
Clearly, F is not cycle free. Let x1 Rx2 R : : : Rxn Rx1 be the shortest cycle
in F and k = md(') + 1. We construct a new frame F0 by extending the
cycle x1  : : :  xn  x1 as is shown in Fig. 3 ((a) for n = 1 and (b) for n > 1).
More precisely, we add to F copies x1i  : : :  xki of xi for each i 2 f1 : : : ng,
organize them into the nontransitive cycle shown in Fig. 3 and draw an
arrow from xji to y 2 W ;fx1  : : :  xn g i xi Ry. Denote the resulting frame
by F0 = hW 0  R0 i and let x0 = xkn . By the construction, F is a reduct of F0 .
Therefore, for every models M = hF Vi and M0 = hF0  V0 i such that

V0 (p) = V(p)  fxji : xi 2 V(p) j < kg

and for every x 2 W ,  2 Sub', we have (M x) j=  i (M0  x) j= . So we
can hook some other model on x0 , and points in W will not feel its presence
by means of ''s subformulas. The frame to be hooked on x0 depends on
whether  j= L or  j= L. We consider only the former alternative.
Fix some m > jW 0 j. For each I ! ; f0g, let FI = hWI  RI  PI i be the
frame whose diagram is shown in Fig. 4 (d0 sees the root of F0 , all points
ei and e0j and is seen from x0  the subframes in dashed boxes are transitive,
e0i 2 WI i i 2 I , and PI consists of sets of the form X  Y such that X
is a nite or conite subset of WI ; fb ai : i < !g and Y is either a nite
subset of fai : i < !g or is of the form fbg Y 0 , where Y 0 is a conite subset
of fai : i < !g. It is not hard to see that the points ai , c, ei and e0i are
characterized by the variable free formulas

0 = 3( m ^ 3( m;1 ^ : : : ^ 3 0) : : :) ^ :32( m ^ 3( m;1 ^ : : : ^ 3 0) : : :)
i+1 = 3i ^ :32 i   = 320 ^ :30
0 = 3 i+1 = 3i ^ :32i  0i+1 = 3i ^ :3+i+1 
(in the sense that x j= i i x = ai , etc.), where
0

= 32? 1 = 3 0 ^ : 0  2 = 3 1 ^ : 1 ^ :3+ 0 
k+1 = 3 k ^ : k ^ :3+ k;1 ^ : : : ^ :3+ 0 :

Dene LI to be the logic determined by the class of frames for L and FI ,
i.e., LI = L \ LogFI . Since :(0i ^ 3m+6:') 2 LJ ; LI for i 2 I ; J (' is
refuted at the root of F0 ), jfLI : I ! ; f0ggj = 2@0 .
Let us show now that LI has the same Kripke frames as L. Since LI L,
we must prove that every Kripke frame for LI validates L. Suppose there
is a rooted Kripke frame G such that G j= LI but G 6j= , for some  2 L.

30

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

nontransitive

F0

x
H
transitive
6H
H
c -b
a
a a d d d  d

     -i -    1 -0 -m   1 -0  -;1
6

e

0

e    
1

I
@
@

transitive

e

j ;

0

  9



@;0

ej

Figure 4.
Since  is in L, it is valid in all frames for L, in particular,  j= . And
since  62 LI ,  is refuted in FI . Moreover, by the construction of FI , it
is refuted at a point from which the root of F0 can be reached by a nite
number of steps. Therefore, the following formulas are valid in FI and so
belong to LI and are valid in G:

_l 3i

(11)

^l 2i( ! 2(2 (2 p ! p) ! p))

(12)

: !
: !

i=0

i=0

0

0

where p does not occur in  and l is a suciently big number so that
any point in FI is accessible by  l steps from every point in the selected
cycle and every point at which  may be false, and 20  = 2(30 ! ).
According to (11), G contains a point at which  is true. By the construction
of  , this point has a successor y at which, by (12), 20 (20 p ! p) ! p is
true under any valuation in G and y j= 30. Dene a valuation U in G
by taking U(p) = y ". Then y j= 20 (20 p ! p), from which y j= p and so
y 2 y ". Now dene another valuation U0 so that U0(p) = y " ;fyg. Since
y is reexive, we again have y j= 20 (20 p ! p), whence y j= p, which is a
contradiction.
2
This construction can be used to obtain one more important result.
THEOREM 1.36 (Blok 1978) Every union-splitting K=F has {  @0 immediate predecessors in NExtK, where { is the number of frames in F which
are not reducts of generated subframes of other frames in F . Every consistent logic dierent from union-splittings has 2@0 immediate predecessors in
NExtK. (For has 2 immediate predecessors in NExtK.)

ADVANCED MODAL LOGIC

31

Proof The former claim follows from Theorem 1.12. To establish the

latter, we continue the proof of Theorem 1.35. One can show that L is
nitely axiomatizable over LI (the proof is rather technical, and we omit it
here). Then, by Zorn's Lemma, NExtLI contains an immediate predecessor
L0I of L. Besides, LI  LJ = L whenever I 6= J . Indeed,

LI  LJ = (L \ LogFI )  (L \ LogFJ ) = L \ (LogFI  LogFJ )
and if i 2 I ; J then, for every  2 L and a suciently big l,
:

_l 3k !  2 LogFI  : 2 LogFJ 
0

k=0

i

0

i

from which  2 LogFI  LogFJ and so L LogFI  LogFJ . It follows that
L0I 6= L0J whenever I 6= J .
2

It is worth noting that tabular logics, proper extensions of D and extensions of K4 are not union-splittings in NExtK. Similar results hold for
the lattices NExtD and NExtT, where every consistent logic has degree of
incompleteness 2@0 (see Blok 1978, 1980b]). It would be of interest to describe the behavior of this function in NExtK4, NExtS4, NExtGrz (where
Theorem 1.34 does not hold and where every tabular logic has nitely many
immediate predecessors) and other lattices of logics to be considered later
in this chapter.

1.5 Stronger forms of Kripke completeness

In the two preceding sections we were considering the problem of characterizing logics L 2 NExtK by classes of Kripke frames. The same problem
arises in connection with the two consequence relations `L and `L as well.
Theorem 1.19 shows the way of introducing the corresponding concepts of
completeness.
With each Kripke frame F let us associate a consequence relation j=F by
putting, for any formula ' and any set ; of formulas, ; j=F ' i (M x) j= ;
implies (M x) j= ' for every model M based on F and every point x in F.
Clearly, a modal logic L is Kripke complete i , for any nite set of formulas
; and any formula ', ; 6`L ' only if there is a Kripke frame F for L such
that ; 6j=F '. Now, let us call L strongly Kripke complete7 if this implication
holds for arbitrary sets ;. In other words, L is strongly complete if every Lconsistent set of formulas holds at some point in a model based on a Kripke
frame for L. Another reformulation: L is strongly complete i L is Kripke
7 Fine 1974c] calls such logics compact, which does not agree with the use of this term
by Thomason 1972].

32

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

T

complete and the relation fj=F: F is a Kripke frame for Lg is nitary. It
follows from the construction of the canonical models that every canonical
(in particular, D{persistent) logic is strongly complete, which provides us
with many examples of such logics in NExtK.
By Theorem 1.33, all logics characterized by rst order denable classes
of Kripke frames are strongly complete. The converse does not hold: there
exist strongly complete logics which are not canonical. The simplest is the
bimodal logic of the frame hR < >i  see Example 2.39 below. By applying
the Thomason simulation (to be introduced in Section 2.3) to this logic
we obtain a logic in NExtK with the same properties see Theorem 2.18.
Moreover, in contrast to D{persistence, strong Kripke completeness is not
preserved under nite sums of logics (see Wolter 1996c]). It is an open
problem, however, whether such logics exist in NExtK4.
Perhaps the simplest examples of Kripke complete logics which are not
strongly complete are GL and Grz (use Theorem 1.58 and the fact that
these logics are not elementary see Correspondence Theory). It is much
more dicult to prove that the McKinsey logic K  23p ! 32p is not
strongly complete the proof can be found in Wang 1992]. For other examples of modal logics that are not strongly complete see Section 3.4. It
is worth noting also that, as was shown in Fine 1974c], every nite width
logic in a nite language turns out to be strongly Kripke complete, though
this is not the case for logics in an innite language, witness
GL:3 = GL  2(2+p ! q) _ 2(2+q ! p):
For the consequence relation `L, we should take the \global" version j=F
of j=F . Namely, we put ; j=F ' if M j= ; implies M j= ' for any model M
based on F. A modal logic L is called globally Kripke complete if for any
nite set of formulas ; and any formula ', ; 6`L ' only if there is a frame
F for L such that ; 6j=F '. L is strongly globally complete if this holds for
arbitrary (not only nite) ;. We also say that L has the global nite model
property if for every nite ; and every ', ; 6`L ' only if there is a nite
frame F for L such that ; 6j=F '.
The global nite model property (FMP, for short) of many standard logics
can be proved by ltration. Say that a logic L strongly admits ltration if for
every generated submodel M of the canonical model ML and every nite set
of formulas # closed under subformulas, there is a ltration of M through
# based on a frame for L.
PROPOSITION 1.37 (Goranko and Passy 1992) If L strongly admits ltration then L has global FMP.
Proof Suppose that ; 6`L ', ; nite. Then 2<! ; 6`L ' and so the
set = 2<! ;  f:'g is L-consistent. It remains to ltrate through

V

V

ADVANCED MODAL LOGIC

33

Sub;  Sub' the submodel of ML generated by a maximal L-consistent
2

set containing .

It follows in particular that K, T, D, KB have global FMP.
PROPOSITION 1.38 Suppose L is globally complete (has global FMP) and
; is a nite set of variable free formulas. Then L  ; is globally complete
(has global FMP) as well.

Proof Let L0 = L  ; and 6`L ', nite. Then ;  6`L ' and so
0

there exists a (nite) Kripke frame F for L such that ;  6j=G '. Since ;
contains no variables, F j= L0 .
2

For n-transitive logics L the global consequence relation `L is reducible to
the \local" `L and so L is Kripke complete (has FMP, is strongly complete)
i L is globally complete (has global FMP, is strongly globally complete). In
general the global properties are stronger than the \local" ones. Although
L is globally complete (has global FMP) only if L is complete (has FMP),
the converse does not hold (see Wolter 1994a] and Kracht 1996]).
EXAMPLE 1.39 Let L = Alt3  p ! 23p  (2p ^ :p) ! :(3q ^ 3:q). A
Kripke frame F validates L i no point in F has more than three successors,
F is symmetric, and irreexive points in it have at most one successor. By
Proposition 1.22, L is Kripke complete. The class of Kripke frames for L is
closed under (not necessarily generated) subframes. So, by Proposition 1.59
to be proved below, L has FMP. We show now that it does not have global
FMP. To this end we require the formulas:

1 = q1 ^ :q2 ^ :q3  2 = :q1 ^ q2 ^ :q3  3 = :q1 ^ :q2 ^ q3 

^

' = 2p ^ :p ^ 1   = fi ! 3i+1 : i = 1 2g ^ 3 ! 31:
Let F = hW Ri, where W = ! and
R = fhm mi : m > 0g  fhm m + 1i : m < !g  fhm m ; 1i : m > 0g:
We then have  6j=F :'. In fact, ' is true at 0 and  is true everywhere
under the valuation V dened by V(p) = W ; f0g and V(qi ) = f3n + i :
n < !g. Clearly, F j= L and so  6`L :'. Suppose now that (N x0 ) j= '
and N j= , for a model N based on a Kripke frame G = hV S i for L. Then
we can nd a sequence xj , j < !, such that xj Sxj+1 and x3j+i j= i+1 , for
j < ! and i = 1 2 3. The reader can verify that all points xj are distinct.
Let us consider now the algebraic meaning of the notions introduced
above. A logic L is Kripke complete i the variety AlgL of modal algebras

34

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

for L is generated by the class KrL = fF+ : F is a Kripke frame for Lg. By
Birkho 's Theorem (see e.g. Mal'cev 1973]), this means that
AlgL = HSPKrL
(i.e., AlgL is obtained by taking the closure of KrL under direct products, then the closure of the result under (isomorphic copies of) subalgebras
and nally under homomorphic images). Clearly, L is globally complete i
precisely the same quasi-identities hold in KrL and AlgL. And since the
quasi-variety generated by a class of algebras C is SPPU C (where PU denotes
the closure under ultraproducts see Mal'cev 1973]), L is globally complete
i
AlgL = SPPU KrL:
Goldblatt 1989] calls the variety AlgL complexif AlgL = SKrL, or, equivalently, if AlgL = SPKrL (this follows from the fact that the dual of the
disjoint union of a family of Kripke frames fFi : i 2 I g is isomorphic to the
product i2I F+i ). We say a logic L is {-complex, { a cardinal, if every
modal algebra for L with  { generators is a subalgebra of F+ for some
Kripke frame F j= L. As was shown in Wolter 1993], this notion turns
out to be the algebraic counterpart of both strong completeness and strong
global completeness of logics in innite languages with { variables.

Q

THEOREM 1.40 For every normal modal logic L in an innite language
with { variables the following conditions are equivalent:
(i) L is strongly Kripke complete
(ii) L is globally strongly complete
(iii) L is {-complex.
Proof (i) ) (iii) Suppose the cardinality of A 2 AlgL does not exceed {.
Denote by L the algebra of modal formulas over { propositional variables
and take some homomorphism h from L onto A. For each ultralter r in
A, the set h;1 (r) is maximal L-consistent. Since L is strongly complete,
there is a model Mr = hFr  Vr i with root xr based on a Kripke frame
Fr for L and such that (Mr  xr ) j= h;1 (r). Without loss of generality we
may assume that the frames Fr for distinct r are disjoint. Let F be the
disjoint union of all of them. Dene a homomorphism V from L into F+ by
taking
V(p) = fVr (p) : r is an ultralter in Ag:
Then V(L) is a subalgebra of F+ 2 AlgL isomorphic to A.
The implication (iii) ) (ii) is trivial. To prove (ii) ) (i), consider an
L-consistent set of formulas ; of cardinality  { and put
= fpg  f2n(p ! ') : n < ! ' 2 ;g



ADVANCED MODAL LOGIC

35

where the variable p does not occur in formulas from ;. It is easily checked
that all nite subsets of are L-consistent, so is L-consistent too. It
follows that fp ! ' : ' 2 ;g 6`L :p. And since L is globally strongly
complete, there exists a model M based on a Kripke frame for L such that
M j= fp ! ' : ' 2 ;g and (M x) j= p, for some x. But then (M x) j= ;.

2

1.6 Canonical formulas
The main problem of completeness theory in modal logic is not only to nd
a suciently simple class of frames with respect to which a given logic L is
complete but also to characterize the constitution of frames for L (in this
class). The rst order approach to the characterization problem, discussed
in Section 1.3 in connection with Sahlqvist's Theorem, comes across two
obstacles. First, there are formulas whose Kripke frames cannot be described in the rst order language with R and =. The best known example
is probably the Lob axiom

la = 2(2p ! p) ! 2p:
F j= la i F is transitive, irreexive (i.e., a strict partial order) and Noetherian in the sense that it contains no innite ascending chain of distinct
points. And as is well known, the condition of Noetherianness is not a rst
order one. The second obstacle is that this approach deals only with logics that are Kripke complete it does not take into account sets of possible
values.
There is another, purely frame-theoretic method of characterizing the
structure of frames. For instance, a frame G validates K=F i G does
not contain a generated subframe reducible to F. It was shown in Zakharyaschev 1984, 1988, 1992] that in a similar manner one can describe
transitive frames validating an arbitrary modal formula. It is not clear
whether characterizations of this sort can be extended to the class of all
frames (an important step in this direction would be a generalization to
n-transitive frames). That is why all frames in this section are assumed to
be transitive. First we illustrate this method by a simple example.
EXAMPLE 1.41 Suppose a frame F = hW R P i refutes la under some
valuation. Then the set V = fx 2 W : x 6j= lag is in P and V V #. It
follows from the former that G = hV R V fX \ V : X 2 P gi is a frame|
we call it the subframe of F induced by V . And the latter condition means
that G is reducible to the single reexive point  which is the simplest
refutation frame for la. Moreover, one can readily check that the converse
also holds: if there is a subframe G of F reducible to  then F 6j= la.

36

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

This example motivates the following denitions. Given frames F =
hW R P i and G = hV S Qi, a partial (i.e., not completely dened, in
general) map f from W onto V is called a subreduction of F to G if it
satises the reduction conditions (R1){(R3) for all x and y in the domain
of f and all X 2 Q. The domain of f will be denoted by domf . In other
words, an f -subreduct of F is a reduct of the subframe of F induced by
domf . A frame G = hV S Qi is a subframe of F = hW R P i if V W and
the identity map on V is a subreduction of F to G, i.e., if S = R V and
Q P . Note that a generated subframe G of F is not in general a subframe
of F, since V may be not in P .
Thus, the result of Example 1.41 can be reformulated like this: F 6j= la
i F is subreducible to .
A subreduction f of F to G is called conal if
domf " domf #:
This important notion can be motivated by the following observation: F
refutes 3> i F is conally subreducible to  (a plain subreduction is not
enough).
THEOREM 1.42 Every refutation frame F = hW R P i for '(p1  : : :  pn ) is
conally subreducible to a nite rooted refutation frame for ' containing at
most c' = 2n  (cn (1) + : : : + cn (2jSub'j)) points.8

Proof Suppose ' is refuted in F under a valuation V. Without loss

of generality we can assume F to be generated by V(p1 ) : : :  V(pn ). Let
X1  : : :  Xm be all distinct maximal 0-cyclic sets in F. Clearly, m  cn (1)
but unlike Theorem 1.8, F is not in general rened and so these sets are
not necessarily clusters of depth 1. However, they can be easily reduced
to such clusters. Dene an equivalence relation  on W by putting x  y
i x = y or x y 2 Xi , for some i 2 f1 : : : mg, and x  y (as before
# = fp1  : : :  pn g). Let x] be the equivalence class under  generated by
x and X ] = fx] : x 2 X g, for X 2 P . By the denition of cyclic sets,
xRy i x] y] #. So the map x 7! x] is a reduction of F to the frame
F01 = hW10  R10  P10 i which results from F by \folding up" the 0-cyclic sets Xi
into clusters of depth 1 and leaving the other points untouched: W10 = W ],
x]R10 y] i x] y] # and P10 = fX ] : X 2 P g. (Roughly, we rene that
part of F which gives points of depth 1.) Put V01 (pi ) = V(pi )]. Then by
the Reduction (or P-morphism) Theorem, we have x j=  i x] j= , for
every  2 Sub'.
Let X be the set of all points in F01 of depth > 1 having Sub'-equivalent
successors of depth 1. It is not hard to see that X 2 P10 . Denote by
8

The function cn (m) was dened in Section 1.2.

ADVANCED MODAL LOGIC

37

F1 = hW1  R1  P1 i the subframe of F01 induced by W10 ; X and let V1 be the
restriction of V01 to F1 . By induction on the construction of  2 Sub' one
can readily show that  has the same truth-values at common points in F01
and F1 (under V01 and V1 , respectively) and so F1 6j= '. The partial map
x 7! x], for x] 2 W1 , is a conal subreduction of F to F1 .
Then we take the maximal 1-cyclic sets in F1 , \fold" them up into clusters
of depth 2 and remove those points of depth > 2 that have Sub'-equivalent
successors of depth 2. The resulting frame F2 will be a conal subreduct of
F1 and so of F as well. After that we form clusters of depth 3, and so forth.
In at most 2jSub'j steps of that sort we shall construct a conal subreduct
of F refuting ' and containing  c' points. It remains to select in it a
suitable rooted generated subframe.
2
For the majority of standard modal axioms the converse also holds.
However, not for all. The simplest counterexample is the density axiom
den = 22p ! 2p. It is refuted by the chain H of two irreexive points but
becomes valid if we insert between them a reexive one. In fact, F 6j= den
i there is a subreduction f of F to H such that f (x") = fag, for no point
x in domf ";domf , where a is the nal point in H.
Loosely, every refutation frame for formulas like la can be constructed by
adding new points to a frame G that is reducible to some nite refutation
frame of xed size. For formulas like 3> we have to take into account the
conality condition and do not put new points \above" G. And formulas
like den impose another restriction: some places inside G may be \closed"
for inserting new points. These \closed domains" can be singled out in the
following way.
Suppose N = hH Ui is a model and a an antichain in H. Say that a is
an open domain in N relativeVto a formula
if there is a pair ta = (;a  a )
W a 62' K4
such that ;a  a = Sub', ;a !
and
 2 2 ;a implies  2 ;a ,
 2 2 ;a i a j= 2+  for all a 2 a.
Otherwise a is called a closed domain in N relative to '. A reexive singleton
a = fag is always open: just take ta = (f 2 Sub' : a j= g f 2 Sub' :
a 6j= g). It is easy to see also that antichains consisting of points from the
same clusters are open or closed simultaneously we shall not distinguish
between such antichains.
For a frame H and a (possibly empty) set D of antichains in H, we say a
subreduction f of F to H satises the closed domain condition for D if
(CDC) :9x 2 domf "; domf 9d 2 D f (x") = d".
Notice that the conal subreduction f of F to the resulting nite rooted
frame H in the proof of Theorem 1.42 satises (CDC) for the set D of

38

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

closed domains in the corresponding model N on H refuting '. Indeed,
every x 2 domf " ; domf has a Sub'-equivalent successor y 2 domf ,
and so an antichain d such that f (x ") = d" is open, since we can take
td = (f 2 Sub' : y j= g f 2 Sub' : y 6j= g). On the other hand, we
have
PROPOSITION 1.43 Suppose N = hH Ui is a nite countermodel for '
and D the set of all closed domains in N relative to '. Then F 6j= '
whenever there is a conal subreduction f of F to H satisfying (CDC) for
D. Moreover, if ' is negation free (i.e., contains no ?, :, 3) then a plain
subreduction satisfying (CDC) for D is enough.
Proof If f is conal and F = hW R P i then we can assume domf " = W .
Dene a valuation V in F as follows. If x 2 domf then we take x j= p i
f (x) j= p, for every variable p in '. If x 62 domf then f (x") 6= , since f is
conal. Let a be an antichain in H such that a" = f (x"). By (CDC), a is
an open domain in N, and we put y j= p i p 2 ;a, for every y 62 domf such
that f (y ") = f (x"). One can show that V is really a valuation in F and,
for every  2 Sub', x j=  i f (x) j=  in the case x 2 domf , and x j= 
i  2 ;a , where a is the open domain in N associated with x, in the case
x 62 domf .
If ' is negation free and f is a plain subreduction then f (x ") may be
empty. In such a case we just put x j= p, for all variables p.
2
Now let us summarize what we have got. Given an arbitrary formula
', we can e ectively construct a nite collection of nite rooted frames
F1  : : :  Fn (underlying all possible rooted countermodels for ' with  c'
points) and select in them sets D1  : : :  Dn of antichains (open domains in
those countermodels) such that, for any frame F, F 6j= ' i there is a conal
subreduction of F to Fi , for some i, satisfying (CDC) for Di . If ' is negation
free then a plain subreduction satisfying (CDC) is enough.
This general characterization of the constitution of refutation transitive
frames can be presented in a more convenient form if with every nite rooted
frame F = hW Ri and a set D of antichains in F we associate formulas
(F D ?) and (F D) such that G 6j= (F D ?) (G 6j= (F D)) i there is
a conal (respectively, plain) subreduction of G to F satisfying (CDC) for
D. For instance, one can take

(F D ?) =

^ 'ij ^ ^n 'i ^ ^ 'd ^ ' ! p

d2D
where a0  : : :  an are all points in F and a0 is its root,
ai Raj

i=0

'ij = 2+ (2pj ! pi )

?

0

ADVANCED MODAL LOGIC

'i = 2+ ((

^ 2pk ^ ^n pj ! pi) ! pi

:ai Rak

39

j =0j 6=i

^ 2pj ^ ^n pi ! _ 2pj )
'd = 2 (
+

'?

i=0
ai 2W ;d"
n
= 2+ ( 2+ pi ! ?):
i=0

^

aj 2d

(F D) results from (F D ?) by deleting the conjunct '? . (F D ?) and
(F D) are called the canonical and negation free canonical formulas for F
and D, respectively. It is not hard to check that if (F D ?) is refuted in
G = hV S Qi under some valuation then the partial map dened by x 7! ai
if the premise of (F D ?) is true at x and pi false is a conal subreduction
of G to F satisfying (CDC) for D and conversely, if f is such a subreduction
then the valuation U dened by U(pi ) = V ; f ;1 (ai ) refutes (F D ?) at
any point in f ;1 (a0 ).
THEOREM 1.44 There is an algorithm which, given a formula ', returns
canonical formulas (F1  D1  ?) : : :  (Fn  Dn  ?) such that
K4  ' = K4  (F1 D1  ?)  : : :  (Fn  Dn ?):
So the set of canonical formulas is complete for the class NExtK4. If ' is
negation free then one can use negation free canonical formulas.

It is not hard to see that K4  ' is a splitting of NExtK4 i ' is deductively equivalent in NExtK4 to a formula of the form (F D]  ?), where D]
is the set of all antichains in F (in this case K4=F = K4  (F D]  ?)). Such
formulas are known as Jankov formulas (Jankov 1963] introduced them for
intuitionistic logic), or frame formulas (cf. Fine 1974a]), or Jankov{Fine
formulas. Since GL is not a union-splitting of NExtK4, this class of logics
has no axiomatic basis.
We conclude this section by showing in Table 2 canonical axiomatizations
of some standard modal logics in the eld of K4. For brevity we write
(F ?) instead of (F  ?) and ] (F ?) instead of (F D]  ?). Each in
the table is to be replaced by both  and .
For more information about the canonical formulas the reader is referred
to Zakharyaschev 1992, 1997b].

1.7 Decidability via the nite model property

Although, for cardinality reason, there are \much more" undecidable logics
than decidable ones, almost all \natural" propositional systems close to

40

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

D4
S4
GL
Grz
K4:1

=
=
=
=
=

Triv
Verum
S5
K4B
A
K4:2
K4:3
Dum

K4  ( ?)
K4  ()
K4  ()

K4  ()  ( ) 
K4  ( ?)  (  ?)
 
= K4  ()  ( )  ( 6)


= K4  ()  ( 6)

= S4  ( 6)

= K4  ( 6) (4 axioms)
1 2
K 
A

= GL  ( A  ff1g f1 2gg)

6

K 
A

6
= K4  (   ?)  ( 6 ?)  ( A   ?) (8 axioms)
K 
A


= K4  ( A ) (6 axioms)

 
6
= S4  ( AK )  ( )

z n}|  {
+1

I

;
@;
K4BWn = K4  ( @
) (2n + 4 axioms)

n

K4BDn
K4nm

..6
.
1
= K4  ( 60 ) (2n+1 axioms)
m
..6
.
1
= K4  ( 60  D] )

Table 2. Canonical axioms of standard modal logics

ADVANCED MODAL LOGIC

41

those we deal with in this chapter turn out to be decidable. Relevant and
linear logics are probably the best known among very few exceptions (see
Urquhart 1984], Lincoln et al. 1992]).
The majority of decidability results in modal logic was obtained by means
of establishing the nite model property. FMP by itself does not ensure yet
decidability (there is a continuum of logics with FMP) some additional conditions are required to be satised. For instance, to prove the decidability
of S4 McKinsey 1941] used two such conditions: that the logic under consideration is characterized by an e ective class of nite frames (or algebras,
matrices, models, etc.) and that there is an e ective (exponential in the case
of S4) upper bound for the size of minimal refutation frames. Under these
conditions, a formula belongs to the logic i it is validated by (nite) frames
in a nite family which can be e ectively constructed. Another sucient
condition of decidability is provided by the following well known
THEOREM 1.45 (Harrop 1958) Every nitely axiomatizable logic with FMP
is decidable.
Here we need not to know a priori anything about the structure of frames
for a given logic. This information is replaced by checking the validity of its
axioms in nite frames, and the restriction of the size of refutation frames
is replaced by constructing all possible derivations: in a nite number of
steps we either separate a tested formula from the logic or derive it. Note
that unlike the previous case now we cannot estimate the time required to
complete this algorithm.
The condition of nite axiomatizability in Harrop's Theorem cannot be
weakened to that of recursive axiomatizability. For there is a logic of depth
3 in NExtK4 (i.e., a logic in NExtK4BD3 ) with an innite set of independent axioms so the logic of depth 3 axiomatizable by some recursively
enumerable but not recursive sequence of formulas in this set is undecidable and has FMP. On the other hand there are examples of undecidable
logics characterized by decidable classes of nite frames (see e.g. Chagrov
and Zakharyaschev 1997]). Yet one can generalize Harrop's Theorem in
the following way. A logic is decidable i it is recursively enumerable and
characterized by a recursive class of recursive algebras. However, this criterion is absolutely useless in its generality. In this connection we note two
open problems posed by Kuznetsov 1979]. Is every nitely axiomatizable
logic characterized by recursive algebras? Is every nitely axiomatizable
logic, characterized by recursive algebras, decidable? (That nite axiomatizability is essential here is explained by the following fact: if a lattice
of logics contains a logic with a continuum of immediate predecessors then
there is no countable sequence of algebras such that every logic in the lattice
is characterized by one of its subsequences. For details see Chagrov and
Zakharyaschev 1997].)

42

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

FMP of almost all standard systems was proved using various forms of
ltration (consult Section 12 Basic Modal Logic and Gabbay 1976]). However, the method of ltration is rather capricious one needs a special craft
to apply it in each particular case (for instance, to nd a suitable \lter").
In this and two subsequent sections we discuss other methods of proving
FMP which are applicable to families of logics and provide in fact sucient
conditions of FMP. (It is to be noted that the families of Kripke complete
logics considered in Section 1.3 contain logics without FMP.) A pair of such
conditions was already presented in Basic Modal Logic:
THEOREM 1.46 (Segerberg 1971) Each logic in NExtK4 characterized by
a frame of nite depth (or, which is equivalent, containing K4BDn , for
some n < !) has FMP.
THEOREM 1.47 (Bull 1966b, Fine 1971) Each logic in NExtS4:3 has FMP
and is nitely axiomatizable (and so decidable).
The former result, covering a continuum of logics, follows immediately
from the description of nitely generated rened frames for K4 in Section 1.2
and the latter is a consequence of Theorem 1.52 and Example 1.54 below.
It is worth noting also that since FL(n) is nite for every logic L 2 NExtK4
of nite depth and every n < !, there are only nitely many pairwise nonequivalent in L formulas of n variables. Logics with this property are called
locally tabular (or locally nite). Moreover, as was observed by Maksimova
1975a], the converse is also true: if L 2 NExtK4 has frames of any depth
< ! then the formulas in the sequence '1 = p, 'n+1 = p _ 2(p ! 2'n )
are not equivalent in L. Thus, a logic in NExtK4 is locally tabular i it
is of nite depth. For L 2 NExtS4 this criterion can be reformulated in
the following way: L is not locally tabular i L Grz:3, where Grz:3 =
S4:3  Grz. Likewise, L 2 NExtGL is not locally tabular i L GL:3.
Nagle and Thomason 1985] showed that all normal extensions of K5 are
locally tabular.

Uniform logics Fine 1975a] used a modal analog of the full disjunctive
normal form for constructing nite models and proving FMP of a family
of logics in NExtD (containing in particular the McKinsey system K 
23p ! 32p which had resisted all attempts to prove its completeness by

the method of canonical models and ltration). Let us notice rst that every
formula '(p1  : : :  pm) is equivalent in K either to ? or to a disjunction
of normal forms (in the variables p1  : : :  pm) of degree md('), which are
dened inductively in the following way. NF0 , the set of normal forms of
degree 0, contains all formulas of the form :1 p1 ^ : : : ^ :m pm , where each

ADVANCED MODAL LOGIC

43

:i is either blank or :. NFn+1 , the set of normal forms of degree n + 1,
consists of formulas of the form

 ^ :1 31 ^ : : : ^ :k 3k 
where S2 NF0 and 1  : : :  k are all distinct
normal forms in NFn . Put
NF = n<! NFn . Using the fact that Wf3 :  2 NFng 2 D it is not
hard to see also that in D every formula ' with md(')  n is equivalent
either to ? or to a disjunction of normal forms of degree n such that at
least one of :1  : : :  :k in the inductive step of the denition above is blank.
Such normal forms are called D-suitable.
It should be clear that, for any distinct 0  00 2 NFn , :(0 ^ 00 ) 2 K.
Consequently, for every  2 NFn and every '(p1  : : :  pm ) with md(')  n,
we have either  ! ' 2 K or  ! :' 2 K.
With each D-suitable normal form  we associate a model M = hF  V i
on a frame F = hW  R i by taking

W = f>g  f0 2 NF : 0 <n  for some n 0g
0 < 00 i 30 is a conjunct of 00 
0 R 00 i either 0 > 00 or md(0 ) = 0 and 00 = >
V (p) = f0 2 W : p is a conjunct of 0 g:
According to the denition, > is the reexive last point in F and so F is
serial. By a straightforward induction on the degree of 0 2 W one can
readily show that (M  0 ) j= 0 . It follows immediately that D has FMP.
Indeed, given ' 62 D, we reduce :' to a disjunction of D-suitable normal
forms with at least one disjunct , and then (M  ) j= .

It turns out that in the same way we can prove FMP of all logics in
NExtD axiomatizable by uniform formulas, which are dened as follows.
Every ' without modal operators is a uniform formula of degree 0 and if
' = (#1 1  : : :  #m m ), where #i 2 f2 3g, md((p1  : : :  pm)) = 0 and
1  : : :  m are uniform formulas of degree n, then ' is a uniform formula
of degree n + 1. A remarkable property of uniform formulas is the following
PROPOSITION 1.48 Suppose ' is a uniform formula of degree n and M,
N are models based upon the same frame and such that, for some point x,
(M y) j= p i (N y) j= p for every y 2 x"n and every variable p in '. Then
(M x) j= ' i (N x) j= '.
Given a logic L, we call a normal form  L-suitable if F j= L.
THEOREM 1.49 (Fine 1975a) Every logic L 2 NExtD axiomatizable by
uniform formulas has FMP.

44

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

Proof It suces to prove that each formula ' with md(')  n is equivalent in L either to ? or to a disjunction of L-suitable normal forms of degree
n. And this fact will be established if we show that every D-suitable normal
form  such that  ! ? 62 L is L-suitable. Suppose otherwise. Let  be an
L-consistent and D-suitable normal form of the least possible degree under

which it is not L-suitable. Then there are a uniform formula  2 L of some
degree m and a model M = hF  Vi such that (M ) 6j= .
For every variable p in , let ;p = f0 2  "m: (M 0 ) j= pg and let
p = ;p (if ;p =  then p = ?). Observe that for every 0 2 "m we have
(M  0 ) j= p i 0 2 ;p i (M 0 ) j= p. Therefore, by Proposition 1.48,
the formula 0 which results from  by replacing each p with p is false
at  in M . Now, if md(0 ) > n then m > n and so p = ? for every p
in , i.e., 0 is variable free. But then 0 is equivalent in D to > or ?,
contrary to F 6j= 0 and L being consistent. And if md(0 )  n then either
 ! 0 2 K, which is impossible, since (M  ) 6j=  ! 0 , or  ! :0 2 K,
from which 0 ! : 2 K and so : 2 L, contrary to  being L-consistent.

W

2

Logics with 23-axioms Another result, connecting FMP of logics with
the distribution of 2 and 3 over their axioms, is based on the following

LEMMA 1.50 For any ' and , 3' $ 3 2 S5 i 23' $ 23 2 K4.

Proof Suppose 23' ! 23 62 K4. Then there is a nite model M,

based on a transitive frame, and a point x in it such that x j= 23' and
x 6j= 23. It follows from the former that every nal cluster accessible
from x, if any, is non-degenerate and contains a point where ' is true. The
latter means that x sees a nal cluster C at all points of which  is false.
Now, taking the generated submodel of M based on C , we obtain a model
for S5 refuting 3' ! 3. The rest is obvious, since 3p $ 32p is in S5
and K4 S5.
2
Formulas in which every occurrence of a variable is in the scope of a
modality 23 will be called 23-formulas.
THEOREM 1.51 (Rybakov 1978) If a logic L 2 NExtK4 is decidable (or
has FMP) and  is a 23-formula then L   is also decidable (has FMP).

Proof Let  = 0(231 : : :  23n), for some formula 0(q1  : : :  qn). If

'(p1  : : :  pm ) 2 L   then there exists a derivation of ' in L   in which
substitution instances of  contain no variables di erent from p1  : : :  pm.
Each of these instances has the form 0 (2301  : : :  230n), where every 0i is
some substitution instance of i containing only p1  : : :  pm . By Lemma 1.50
and in view of the local tabularity of S5 (it is of depth 1), there are nitely

ADVANCED MODAL LOGIC

45

many pairwise non-equivalent in K4 substitution instances of 23i of that
sort (the reader can easily estimate the number of them). So there exist
only nitely many pairwise non-equivalent in K4 substitution instances of
 containing p1  : : :  pm, say 1  : : :  k , and we can e ectively construct
them. Then, by the Deduction Theorem,

' 2 L   i 1  : : :  k `L ' i 2+ (1 ^ : : : ^ k ) ! ' 2 L
and so L   is decidable (or has FMP) whenever L is decidable (has FMP).
2
It should be noted that by adding to L with FMP innitely many 23formulas we can construct an incomplete logic. For a concrete example see
Rybakov 1977]. By adding a variable free formula to a logic in NExtK with
FMP one can get a logic without FMP. However, K  ', ' variable free,
has FMP, as can be easily shown by the standard ltration through the set
Sub'  Sub, where  62 K  '. Innitely many variable free formulas can
axiomatize a normal extension of K4 without FMP (for a concrete example
see Chagrov and Zakharyaschev 1997]).

1.8 Subframe and conal subframe logics

A very useful source of information for investigating various properties of
logics in NExtK4 is their canonical axioms. Notice, for instance, that the
canonical axioms of all logics in Table 2, save A and K4nm , contain no
closed domains. Canonical and negation free canonical formulas of the form
(F) and (F ?) are called subframe and conal subframe formulas, respectively, and logics in NExtK4 axiomatizable by them are called subframe and
conal subframe logics. The classes of such logics will be denoted by SF
and CSF . Subframe and conal subframe logics in NExtK4 were studied
by Fine 1985] and Zakharyaschev 1984, 1988, 1996].
THEOREM 1.52 All logics in SF and CSF have FMP.

Proof Suppose L = K4 f(Fi ?) : i 2 I g and ' 62 L. By Theorem 1.44,

without loss of generality we may assume that ' is a canonical formula,
say, (F D ?). Now consider two cases. (1) For no i 2 I , F is conally
subreducible to Fi . Then F j= L, F 6j= (F D ?), and we are done. (2) F
is conally subreducible to (Fi  ?), for some i 2 I . In this case we have
(F D ?) 2 K4  (Fi  ?) L, which is a contradiction. Indeed, suppose
G 6j= (F D ?). Then there is a conal subreduction of G to F. And since
the composition of (conal) subreductions is again a (conal) subreduction,
G is conally subreducible to Fi , which means that G 6j= (Fi  ?). Subframe
logics are treated analogously.
2

46

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

The names \subframe logic" and \conal subframe logic" are explained
by the following frame-theoretic characterization of these logics. A subframe
G = hV S Qi of a frame F is called conal if V " V # in F. Say that a class
C of frames is closed under (conal) subframes if every (conal) subframe
of F is in C whenever F 2 C .
THEOREM 1.53 L 2 NExtK4 is a (conal) subframe logic i it is characterized by a class of frames that is closed under (conal) subframes.

Proof Suppose L 2 CSF . We show that the class of all frames for L is

closed under conal subframes. Let G j= L and H be a conal subframe
of G. If H 6j= (F ?), for some (F ?) 2 L, then (since G is conally
subreducible to H) G 6j= (F ?), which is a contradiction. So H j= L.
Now suppose that L is characterized by some class of frames C closed
under conal subframes. We show that L = L0 , where

L0 = K4  f(F ?) : F 6j= Lg:
If F is a nite rooted frame and F 6j= L then (F ?) 2 L, for otherwise
G 6j= (F ?) for some G 2 C , and hence there is a conal subframe H of
G which is reducible to F but H 2 C and so, by the Reduction Theorem,
F is a frame for L, which is a contradiction. Thus, L0 L. To prove the
converse, suppose (F D ?) 2 L. Then F 6j= L, and hence (F ?) 2 L0,
from which (F D ?) 2 L0 .
Subframe logics are considered in the same way.
2
It follows in particular that SF  CSF (K4:1 and K4:2 are conal
subframe logics but not subframe ones). One can easily show also that
CSF is a complete sublattice of NExtK4 and SF a complete sublattice of
CSF .

EXAMPLE 1.54 Every normal extension of S4:3 is axiomatizable by canonical formulas which are based on chains of non-degenerate clusters and so
have no closed domains. Therefore, NExtS4:3  CSF .
The classes SF and CSF ; SF contain a continuum of logics. And
yet, unlike NExtK or NExtK4, their structure and their logics are not so
complex. For instance, it is not hard to see that every logic in CSF is
uniquely axiomatizable by an independent set of conal subframe formulas
and so these formulas form an axiomatic basis for CSF .
The concept of subframe logic was extended in Wolter 1993] to the class
NExtK by taking the frame-theoretic characterization of Theorem 1.53 as
the denition. Namely, we say that L 2 NExtK is a subframe logic if the
class of frames for L is closed under subframes. In other words, subframe

ADVANCED MODAL LOGIC

47

logics are precisely those logics whose axioms \do not force the existence of
points". For example, K, KB, K5, T, and Altn are subframe logics. To
give a syntactic characterization of subframe logics we require the following
formulas.
For a formula ' and a variable p not occurring in ', dene a formula 'p
inductively by taking

qp
= q ^ p q an atom
( $ )p = p $ p  for $ 2 f^ _ !g
(2)p
= 2(p ! p ) ^ p
and put 'sf = p ! 'p .
LEMMA 1.55 For any frame F, F j= 'sf i ' is valid in all subframes of
F.

Proof It suces to notice that if M is a model based on F, M0 a model
based on the subframe of F induced by fy : (M y) j= pg and (M x) j= q i
(M0  x) j= q, for all variables q, then (M x) j= 'p i (M0  x) j= '.
2

PROPOSITION 1.56 The following conditions are equivalent for any modal
logic L:
(i) L is a subframe logic
(ii) L = K  f'sf : ' 2 ;g, for some set of formulas ;
(iii) L is characterized by a class of frames closed under subframes.

Proof The implication (i) ) (iii) is trivial (iii) ) (ii) and (ii) ) (i) are
consequences of Lemma 1.55.

2

It follows that the class of subframe logics forms a complete sublattice of
NExtK. However, not all of them have FMP and even are Kripke complete.
EXAMPLE 1.57 Let L be the logic of the frame F constructed in Example 1.7. Since every rooted subframe G of F is isomorphic to a generated
subframe of F, L is a subframe logic. We show that L has the same Kripke
frames as GL:3. Suppose G is a rooted Kripke frame for GL:3 refuting
' 2 L. Then clearly G contains a nite subframe H refuting '. Since H is
a nite chain of irreexive points, it is isomorphic to a generated subframe
of F, contrary to F 6j= '. Thus G j= L. Conversely, suppose G is a Kripke
frame for L. Then G is irreexive. For otherwise G refutes the formula
' = 22 (2p ! p) ^ 2(2p ! p) ! 2p, which is valid in F. Let us show
now that G is transitive. Suppose otherwise. Then G refutes the formula
2p ! 2(2p _ (2q ! q)), which is valid in F because ! is a reexive point.
Finally, since G j= ', G is Noetherian and since F is of width 1, we may

48

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

conclude that G j= GL:3. It follows that the subframe logic L is Kripke
incomplete. Indeed, it shares the same class of Kripke frames with GL:3
but 2p ! 22p 2 GL:3 ; L.
The following theorem provides a frame-theoretic characterization of those
complete subframe logics in NExtK that are elementary, D{persistent and
strongly complete. Say that a logic L has the nite embedding property if
a Kripke frame F validates L whenever all nite subframes of F are frames
for L.
THEOREM 1.58 (Fine 1985) For each Kripke complete subframe logic L
the following conditions are equivalent:
(i) L is universal9
(ii) L is elementary
(iii) L is D{persistent
(iv) L is strongly Kripke complete
(v) L has the nite embedding property.

Proof The implications (i) ) (ii) and (iii) ) (iv) are trivial (ii) ) (iii)

follows from Fine's 1975b] Theorem formulated in Section 1.3 and (v) )
(i) from Tarski 1954]. Thus it remains to show that (iv) ) (v). Suppose
F is a Kripke frame with root r such that F 6j= L but all nite subframes
of F validate L. Then it is readily checked that all nite subsets of ; =
fpr g  2<! F are L-consistent. Hence the whole set ; is L-consistent. On
the other hand, similarly to the proof of Lemma 1.13 one can show that ; is
satisable in a Kripke frame i the frame is subreducible to F. So ; cannot
be satised in a Kripke frame for L and L is not strongly complete.
2
A similar criterion for the conal subframe logics in NExtK4 can be
found in Zakharyaschev 1996]. Note, however, that they are not in general
universal and certainly do not have the nite embedding property, but (ii),
(iii) and (iv) are still equivalent.
PROPOSITION 1.59 Every subframe logic L 2 NExtAltn has FMP.

Proof Suppose ' 62 L. By Theorem 1.22, there is a Kripke frame F for L

refuting ' at a point x. Denote by X the set of points in F accessible from
x by  md(') steps. Clearly, X is nite and the subframe of F induced by
X validates L and refutes '.
2
To understand the place of incomplete logics in the lattice of subframe
logics we call a subframe logic L strictly sf-complete if it is Kripke complete
9 I.e., universal is the class of Kripke frames for L considered as models of the rst
order language with R and =.

ADVANCED MODAL LOGIC

49



6

2



1

.
..
G 
(b)

6

6

6

F 0
(a)

Figure 5.
and no other subframe logic has the same Kripke frames as L. Example 1.57
shows that GL:3 is not strictly sf-complete. However, the logics T, S4 and
Grz turn out to be strictly sf-complete. The following result claries the
situation. It is proved by applying the splitting technique to lattices of
subframe logics.
THEOREM 1.60 A subframe logic L containing K4 is strictly sf-complete
i L 6 GL:3. All subframe logics in NExtAltn are strictly sf-complete.
A subframe logic is tabular i there are only nitely many subframe logics
containing it.

1.9 More su cient conditions of FMP
As follows from Theorem 1.52, a logic in NExtK4 does not have FMP only
if at least one of its canonical axioms contains closed domains. We illustrate
their role by a simple example.

EXAMPLE 1.61 Consider the logic L = K4:3  ] (F ?) and the formula
(F ?), where F is the frame depicted in Fig. 5 (a). The frame G in
Fig. 5 (b) separates (F ?) from L. Indeed, F is a conal subframe of G
and so G 6j= (F ?). To show that G j= ] (F ?), suppose f is a conal
subreduction of G to F. Then f ;1(1) contains only one point, say x f ;1(0)
also contains only one point, namely the root of G. So the innite set of
points between x and the root is outside domf , which means that f does
not satisfy (CDC) for ff1gg. On the other hand, if H is a nite refutation
frame of width 1 for (F ?) then H contains a generated subframe reducible
to F, from which H 6j= L. Thus, L fails to have FMP. In the same manner
the reader can prove that A in Table 2 does not have FMP either.
We show now two methods developed in Zakharyaschev 1997a] for establishing FMP of logics whose canonical axioms contain closed domains.
One of them uses the following lemma, which is an immediate consequence
of the refutability criterion for the canonical formulas.

50

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

LEMMA 1.62 Suppose (F D) and (G E) ((F D ?) and (G E ?))
are canonical formulas such that there is a (conal) subreduction f of G
to F satisfying (CDC) for D and an antichain e domf " is in E whenever
f (e") = d" for some d 2 D. Then (G E) 2 K4  (F D) (respectively,
(G E ?) 2 K4  (F D ?)).
THEOREM 1.63 L = K4  f(Fi  Di  ?) : i 2 I g  f(Fj  Dj ) : j 2 J g has
FMP provided that either all frames Fi , for i 2 I  J , are irreexive or all
of them are reexive.

Proof Suppose all Fi are irreexive and (G E ?) is an arbitrary canonical formula. We construct from G a new nite frame H by inserting into it
new reexive points. Namely, suppose e is an antichain in G such that e 62 E.
Suppose also that C1  : : :  Cn are all clusters in G such that e Ci " and
e \ Ci = , for i = 1 : : :  n, but no successor of Ci possesses this property.
Then we insert in G new reexive points x1  : : :  xn so that each xi could
see only the points in e and their successors and could be seen only from the
points in Ci and their predecessors. The same we simultaneously do for all
antichains e in G of that sort. The resulting frame is denoted by H. Since
no new point was inserted just below an antichain in E, H 6j= (G E ?).
Suppose now that (G E ?) 62 L and show that H j= L. If this is not so
then either H 6j= (Fi  Di  ?), for some i 2 I , or H 6j= (Fj  Dj ), for some
j 2 J . We consider only the former case, since the latter one is treated
similarly. Thus, we have a conal subreduction f of H to Fi satisfying
(CDC) for Di . Since Fi is irreexive, no point that was added to G is in
domf . So f may be regarded as a conal subreduction of G to Fi satisfying
(CDC) for Di . We clearly may assume also that the subframe of G generated
by domf is rooted. Let e be an antichain in G belonging to domf " and such
that f (e") = d" for some d 2 Di . If e 62 E then there is a reexive point
x in H such that x 2 domf " and x sees only e" and, of course, itself. But
then f (x") = f (e") = d" and so, by (CDC), x 2 domf , which is impossible.
Therefore, e 2 E and so, by Lemma 1.62, (G E ?) 2 L, contrary to our
assumption.
In the case of reexive frames irreexive points are inserted.
2
EXAMPLE 1.64 According to Theorem 1.63, the logic
1 2
K 
A

L = K4  ( A  ff1g f1 2gg)
has FMP. However, Artemov's logic A = L  GL does not enjoy this
property. So FMP is not in general preserved under sums of logics.

ADVANCED MODAL LOGIC

51

The scope of the method of inserting points is not bounded only by canonical axioms associated with homogeneous (irreexive or reexive) frames. It
can be applied, for instance, to normal extensions of K4 with modal reduction principles, i.e., formulas of the form M p ! N p, where M and N are
strings of 2 and 3 (for rst order equivalents of modal reduction principles
see van Benthem 1976]). One can show that each such logic is either of
nite depth, or can be axiomatized by 23-formulas and canonical formulas
based upon almost homogeneous frames (containing at most one reexive
point), for which the method works as well. So we have
THEOREM 1.65 All logics in NExtK4 axiomatizable by modal reduction
principles have FMP and are decidable.
One of the most interesting open problems in completeness theory of
modal logic is to prove an analogous theorem for logics in NExtK or to
construct a counter-example. It is unknown, in particular, whether the
logics K  2m p ! 2n p have FMP the same concerns the logics K  tran .
The second method of proving FMP uses the more conventional technique
of removing points. Suppose that L = K4  f(Gi  Di  ?) : i 2 I g and
 = (H E ?) 62 L. Then there exists a frame F for L such that F 6j= ,
i.e., there is a conal subreduction h of F to H satisfying (CDC) for E.
Construct the countermodel M = hF Vi for  as it was done in Section 1.6.
Without loss of generality we may assume that domh" = domh# = F and
that F is generated by the sets V(pi ), pi a variable in .
Actually, the step-wise renement procedure with deleting points having
Sub-equivalent successors, used in the proof of Theorem 1.42, establishes
FMP of L when all Di are empty, i.e., L is a conal subframe logic. To
tune it for L with non-empty Di , we should follow a subtler strategy of
deleting points, preserving those that are \responsible" for validating the
axioms of L. Suppose we have already constructed a model M0n = hF0n  V0n i
by \folding up" n ; 1-cyclic sets into clusters of depth n (we use the same
notations as in the proof of Theorem 1.42). Now we throw away points of
two sorts.
First, for every proper cluster C of depth n such that some x 2 C has
a Sub-equivalent successor of depth < n, we remove from C all points
except x. Second, call a point x of depth > n redundant in M0n if it has
a Sub-equivalent successor of depth  n and, for every i 2 I and every
conal subreduction g of (F0n )n to the subframe of Gi generated by some
d 2 Di such that d g(x") and g satises (CDC) for Di , there is a point
y 2 x " of depth  n such that g(y ") = d". Let X be the maximal
set of redundant points in M0n which is upward closed in (Wn0 )>n . We
dene Mn+1 = hFn+1  Vn+1 i as the submodel of M0n resulting from it by
removing all points in X as well. Since all deleted points have Subequivalent successors, Mn+1 6j= . And since we keep in Fn+1 points which

52

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

violate (CDC) for Di of possible conal subreductions to Gi , Fn+1 j= L.
So FMP of L will be established if we manage to prove that this process
eventually terminates.
2
1 6
 
K 
A

EXAMPLE 1.66 Let L = S4  (G ff1 2gg ?), where G is A , and
assume that our \algorithm", when being applied to F,  and L, works
innitely long. Then the frame F! = hW!  R! i, where

W! =

 W i R! =  R i Fi = hWi Ri Pii 


0<i<!

i



0<i<!

i

is of innite depth. By Konig's Lemma, there is an innite descending
chain : : : xi R! xi;1 : : : R! x2 R! x1 in F! such that xi is of depth i. Since
there are only nitely many pairwise non-Sub-equivalent points, there
must be some n > 0 such that, for every k n, each point in C (xk ) has a
1
Sub-equivalent successor in F<k
k . And since F1 is nite, there is m n
starting from which all xi see the same points of depth 1. Let us consider
now Fm and ask why points in the m-cyclic set X , folded at step m + 1
into C (xm+1 ), were not removed at step m. X is upward closed in Wm>m
and every point in it has a Sub-equivalent successor in Fmm . So the only
reason for keeping some x 2 X is that Fmm is conally subreducible to G1 ,
x sees inverse images of both points in G1 but none of its successors in
Fmm does. By the conality condition, these inverse images can be taken
from F1 1 . But then they are also seen from xm , which is a contradiction.
Thus sooner or later our algorithm will construct a nite frame separating
L from , which proves that L has FMP.
The reason why we succeeded in this example is that inverse images of
points in the closed domain f1 2g can be found at a xed nite depth in
F! , and so points violating (CDC) for it can also be found at nite depth
(that was not the case in Example 1.61). The following denitions describe
a big family of frames and closed domains of that sort.
A point x in a frame G is called a focus of an antichain a in G if x 62 a
and x" = fxg  a". Suppose G is a nite frame and D a set of antichains
in G. Dene by induction on n notions of n-stable point in G (relative to
D) and n-stable antichain in D. A point x is 1-stable in G i either x is of
depth 1 in G or the cluster C (x) is proper. A point x is n + 1-stable in G
(relative to D) i it is not m-stable, for any m  n, and either there is an
n-stable point in G (relative to D) which is not seen from x or x is a focus
of an antichain in D containing an n ; 1-stable point and no n-stable point.
And we say an antichain d in D is n-stable i it contains an n-stable point

ADVANCED MODAL LOGIC

1

1

6
K ;
A
6
A
;
3  A 2
6
K ;
A
6
A AA
;
5  A 4
6
KA ;
A

A 6
;
A
7  A 6



(a)

1

1

6
AK  6
A 
2  A  2
6
AK A 6
A 
3  A A 3
6
AKA A 6

4  A A 4



(b)

1 1

53

1

6
I
@
@
;
I;
6
@;
;
@
;
2  2  @ 2
6
I
@
@
;
I;
6
@;
;@ ;@
3  3  3
6
I
@
@
;
I;
6
@;
;
@
;
4  4  @ 4



(c)

1

1

6
I
@
6
;
@;
;
3  @ 3
6
I
@
6
;
@;
;
5  @ 5
6
I
@
6
;
@;
;
7  @ 7



(d)

Figure 6.
in the subframe G0 of G generated by d (relative to D) and no m-stable
point in G0 (relative to D), for m > n. A point or an antichain is stable if
it is n-stable for some n. It should be clear that if a point in an antichain
is stable then the rest points in the antichain are also stable.
EXAMPLE 1.67 (1) Suppose G is a nite rooted generated subframe of one
of the frames shown in Fig. 6 (a){(c). Then, regardless of D, each point
in G di erent from its root is n-stable, where n is the number located near
the point. Every antichain d in G, containing at least two points, is also
n-stable, with n being the maximal degree of stability of points in d.
(2) If G is a rooted generated subframe of the frame depicted in Fig. 6
(d) and D is the set of all two-point antichains in G then every point in G is
n-stable (relative to D), where n stays near the point. However, for D = 
no point in G, save those of depth 1, is stable.
(3) If G is a nite tree of clusters then every antichain in G, di erent from
a non-nal singleton, is either 1- or 2-stable in G regardless of D. Every
antichain containing a point x with proper C (x) is 1- or 2-stable as well,
whatever G and D are.
(4) Every antichain is stable in every irreexive frame G relative to the
set D] of all antichains in G. However, this is not so if G contains reexive
points (for reexive singletons are open domains and do not belong to D] ).
The sucient condition of FMP below is proved by arguments that are
similar to those we used in Example 1.66.
THEOREM 1.68 If L = K4 f(Gi  Di  ?) : i 2 I g and there is d > 0 such
that, for any i 2 I , every closed domain d 2 Di is n-stable in Gi (relative
to Di ), for some n  d, then L has FMP.
Example 1.67 shows many applications of this condition. Moreover, using
it one can prove the following

54

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

THEOREM 1.69 Every normal extension of S4 with a formula in one variable has FMP and is decidable.
Note that, as was shown by Shehtman 1980], a formula in two variables
or an innite set of one-variable formulas can axiomatize logics in NExtS4
without FMP (and even Kripke incomplete).

1.10 The reduction method
That a logic does not have FMP (or is Kripke incomplete) is not yet an
evidence of its undecidability: it is enough to recall that the majority of
decidability results for classical theories was proved without using any analogues of the nite model property (see e.g. Rabin 1977], Ershov 1980]).
The rst example of a decidable nitely axiomatizable modal logic without
FMP was constructed by Gabbay 1971].
It seems unlikely that the methods of classical model theory can be applied directly for proving the decidability of propositional modal logics.
However, sometimes it is possible to reduce the decision problem for a given
modal logic L to that for a knowingly decidable rst or higher order theory
whose language is expressive enough for describing the structure of frames
characterizing L. The most popular tools used for this purpose are Buchi's
1962] Theorem on the decidability of the weak monadic second order theory
of the successor function on natural numbers and Rabin's 1969] Tree Theorem. Below we illustrate the use of Rabin's Theorem following Gabbay
1975] and Cresswell 1984].
Let ! be the set of all nite sequences of natural numbers and % the
lexicographic order on it. For x 2 ! and i < !, put ri (x) = x i, where
denotes the usual concatenation operation. Besides, dene the following
predicates <i on ! , for 0  i  2,

x <i y i y = x (3n + i) for some n < !:
It follows from Rabin 1969] that the monadic second order theory S!S
of the model h!  fri : i < !g f<i: 0  i  2g % i ( denotes the empty
sequence) is decidable.
The theory S!S has a very strong expressive power which makes it possible to e ectively describe semantical denitions of many modal (as well as
some other) logics and thereby prove their decidability. In this way Gabbay
1975] established the decidability of, for instance,

K  2m3p ! 3p K  3m2p ! 2p
K  2mp ! 3np K  3mp ! 2np:

ADVANCED MODAL LOGIC

55

By Sahlqvist's Theorem, all these logics are Kripke complete however, we
do not know whether they have FMP. General frames can also be described
by means of S!S.
EXAMPLE 1.70 The frame F = hW R P i constructed in Example 1.7 can
be represented in the language of S!S as follows. Let us encode each n < !
by the sequence h3ni, while ! and ! + 1 by r1 () and r2 (), respectively.
Then we have
x 2 W i  <0 x _ x = r1 () _ x = r2 ()
xRy i ( <0 x ^  <0 y ^ y % x ^ x 6= y) _
(x = r1 () ^  <0 y) _ x = y = r1 () _
(x = r2 () ^ y = r1 ())
X 2 P i 8x (x 2 X ! x 2 W ) ^ ((Fin(X ) ^ r1 () 2= X ) _
8Y (8y (y 2 Y $ (y 2 W ^ y 2= X )) ! Fin(Y ) ^ r1 () 2= Y ))
where x = y means x % y ^ y % x and
Fin(X ) = 9x8y (y 2 X ! y % x):
It follows that the logic LogF is decidable. Indeed, for every formula
'(p1  : : :  pn ), we have ' 2 LogF i the second order formula
8x8X1 : : :  Xn (X1 2 P ^ : : : ^ Xn 2 P ^ x 2 W ! ST ('(X1  : : :  Xn )))
belongs to S!S. Here ST ('(X1  : : :  Xn )), the standard translation of ', is
dened inductively in the following way (see also Correspondence Theory):
ST (X ) = x 2 X ST (?) = ?
ST (X $ Y ) = ST (X ) $ ST (Y ) for $ 2 f^ _ !g
ST (2X ) = 8y (xRy ! ST (X )fy=xg):
Recall that, as was shown in Example 1.57, LogF is Kripke incomplete.
Also, it is not hard to nd examples of applications of this technique
for proving the decidability of nitely axiomatizable quasi-normal unimodal
and normal polymodal (in particular, tense) logics which do not have Kripke
frames at all perhaps, the simplest one is Solovay's logic S.
Sobolev 1977a] found another way of proving decidability by applying
methods of automata theory on innite sequences. Using the results of
Buchi and Siefkes 1973] he showed that all nitely axiomatizable superintuitionistic logics of nite width (see Section 3.4) containing the formula
(((p ! q) ! p) ! p) _ (((q ! p) ! q) ! q):

56

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

are decidable. By the preservation theorem of Section 3.3, this result can
be transferred to the corresponding extensions of S4.
If a logic is known to be complete with respect to a suitable class of
frames, the methods discussed above are usually applicable to it in a rather
straightforward manner. A relative disadvantage of this approach is that the
resulting decision algorithms inherit the extremely high complexity of the
decision algorithms for S!S or other \rich theories" used to prove decidability. On the other hand, the logic S, for instance, turns out to be decidable
by an algorithm of the same complexity as that for GL (see Example 1.75),
in particular, the derivability problem in S is PSPACE -complete. The
logic of the frame F in Example 1.7 is \almost trivial"|it is polynomially
equivalent to classical propositional logic, which follows from the fact that
every formula ' refutable by F can be also refuted in F under a valuation giving the same truth-value to all variables in ' at all points i such
that jSub'j < i < ! (see Section 4.6). Actually, this sort of decidability
proofs (ignoring \inessential" parts of innite frames) was used already by
Kuznetsov and Gerchiu 1970] for studying some superintuitionistic logics.
Recently more general semantical methods of obtaining decidability results without turning to \rich theories" have been developed. We demonstrate them in the next section by establishing the decidability of all nitely
axiomatizable logics in NExtK4:3, which according to Example 1.61 do not
in general have FMP. We show, however, that those logics are complete
with respect to recursively enumerable classes of recursive frames in which
the validity of formulas can be e ectively checked|it was this rather than
the niteness of frames that we used in the proof of Harrop's Theorem. In
Section 2.5 this result will be extended to linear tense logics which in general
are not even Kripke complete. Our presentation follows Zakharyaschev and
Alekseev 1995].

1.11 Logics containing K4:3
Each logic in L 2 NExtK4:3 is represented in the form
L = K4:3  f(Fi  Di  ?) : i 2 I g
where all Fi are chains of clusters. So our decidability problem reduces to
nding an algorithm which, given such a representation with nite I and
a canonical formula (F D ?) built on a chain of clusters F, could decide
whether (F D ?) 2 L. Recall also that, by Fine's 1974c] Theorem, logics
of width 1 are characterized by Kripke frames having the form of Noetherian
chains of clusters.

ADVANCED MODAL LOGIC

57

LEMMA 1.71 For any Noetherian chain of clusters G and any canonical
formula (F D ?), G 6j= (F D ?) i there is an injective10 conal subreduction g of G to F satisfying (CDC) for D.

Proof If G 6j= (F D ?) then there is a conal subreduction f of G to

F satisfying (CDC) for D. Clearly, f ;1(x) is a singleton if x is irreexive.
Suppose now that x is a reexive point in F. Since G contains no innite
ascending chains, f ;1 (x) has a nite cover and so there is a reexive point
ux 2 f ;1 (x) such that f ;1 (x) ux#. Fix such a ux for each reexive x and
dene a partial map g by taking
8< f (y) if either f (y) is irreexive or
g(y) = :
f (y) is reexive and y = uf (y)
undened otherwise.
One can readily check that g is the injective conal subreduction we need.
The converse is trivial.
2
Roughly, every Noetherian chain of clusters refuting (F D ?) results
from F by inserting some Noetherian chains of clusters just below clusters
C (x) in F such that fxg 62 D. We show now that if (F D ?) is not in
L 2 NExtK4:3 then it can be separated from L by a frame constructed
from F by inserting in open domains between its adjacent clusters either
nite descending chains of irreexive points possibly ending with a reexive
one or innite descending chains of irreexive points.
Let C (x0 ) : : :  C (xn ) be all distinct clusters in F ordered in such a way
that C (x0 )  C (x1 )#  : : :  C (xn )#. Say that an n-tuple t = h1  : : :  n i
is a type for (F D ?) if either i = m or i = m+, for some m < !, or
i = !, with i = 0 if fxi g 2 D. Given a type t = h1  : : :  n i for (F D ?),
we dene the t-extension of F to be the frame G that is obtained from F
by inserting between each pair C (xi;1 ), C (xi ) either a descending chain of
m irreexive points, if i = m < !, or a descending chain of m + 1 points
of which only the last (lowest) one is reexive, if i = m+, or an innite
descending chain of irreexive points, if i = !. It should be clear that
G 6j= (F D ?).
LEMMA 1.72 If L 2 NExtK4:3 and (F D ?) 62 L then (F D ?) is
separated from L by the t-extension of F, for some type t for (F D ?).
Proof By Lemma 1.71, we have a Noetherian chain of clusters G for L
and an injective conal subreduction f of G to F satisfying (CDC) for D.
By the Generation Theorem, we may assume that f maps the root of G to
the root of F. Let G0 be the subframe of G obtained by removing from G
10

That is g(x) 6= g(y), for every distinct x y 2 domg.

58

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

all those points that are not in domf but belong to clusters containing some
points in domf . The very same map f is an injective conal subreduction
of G0 to F satisfying (CDC) for D, and so G0 6j= (F D ?). Since G0 is a
reduct of G, G0 j= L.
Let C (x0 ) : : :  C (xn ) be all distinct clusters in G0 such that
n

domf = C (xi ) C (x )  C (x )#  : : :  C (xn )#:
i=0

0

1

By induction on i we dene a sequence of frames G0  : : :  Gn such that
(a) f is an injective conal subreduction of Gi to F satisfying (CDC) for
D, (b) between C (xi;1 ) and C (xi ) the frame Gi contains either a nite
descending chain of irreexive points possibly ending with a reexive one
or an innite descending chain of irreexive points, and (c) Gi j= L.
Suppose Gi;1 has been already constructed and Ci is the chain of clusters
located between C (xi;1 ) and C (xi ). Three cases are possible. (1) Ci is a
nite chain of irreexive points. Then we put Gi = Gi;1 . (2) Ci contains
a non-degenerate cluster C (x) having nitely many distinct successors in
Ci and all of them are irreexive. Then Gi results from Gi;1 by removing
from Ci all points save x and those successors. Gi is a reduct of Gi;1
and so conditions (a){(c) are satised. (3) Suppose (1) and (2) do not
hold. Then Ci contains an innite descending chain Y of irreexive points
accessible from all other points in Ci . In this case Gi is obtained from Gi;1
by removing all points in Ci save those in Y . Clearly, Gi satises (a) and
(b). To prove (c) suppose Gi 6j= (H E ?) for some (H E ?) 2 L. Then
there is an injective conal subreduction g of Gi to H satisfying (CDC) for
E. Consider g as a conal subreduction of Gi;1 to H and show that it also
satises (CDC) for E. Indeed, (CDC) could be violated only by a point in
z 2 Ci ; Y such that g(z ") = w", for some fwg 2 E. Since g;1 (w) is a
singleton and Y z", there is y 2 Y such that g(y") = w" and y 62 domg,
contrary to g satisfying (CDC) for E as a subreduction of Gi to H.
2
Thus, a frame separating (F D ?) 62 L from L 2 NExtK4:3 can be
found in the recursively enumerable class of t-extensions of F, t being a
type for (F D ?). Moreover, given a formula (H E ?) and a type t
for (F D ?), one can e ectively check whether (H E ?) is valid in the
t-extension of F. Indeed, let k be the number of irreexive points in H,
t = h1  : : :  n i, and G the t-extension of F. Construct a conal subframe
Gk of G by \cutting o " the innite descending chains inserted in F (if any)
just below their k + 1th points, and let X be the set of all these k + 1th
points. Clearly, Gk is nite. It is now an easy exercise to prove the following
LEMMA 1.73 G 6j= (H E ?) i there is an injective conal subreduction
f of Gk to H satisfying (CDC) for E and such that X \ domf = .

ADVANCED MODAL LOGIC

59

0

6

1



 
F

6

1

2
..
.
G !


;
;
I
@
@;

0

Figure 7.
As a consequence we obtain
THEOREM 1.74 All nitely axiomatizable normal extensions of K4:3 are
decidable.

1.12 Quasi-normal modal logics
All logics we have considered so far were normal, i.e., closed under the rule
of necessitation '=2'. McKinsey and Tarski 1948] noticed, however, that
by adding to S4 the McKinsey axiom ma = 23p ! 32p and taking
the closure under modus ponens and substitution we obtain a logic|let us
denote it by S4:10 |which is not normal in that sense. To understand why
this is so, consider the frame F shown in Fig. 7. One can easily construct
a model on F such that 0 6j= 2ma (0 sees a nal proper cluster). On the
other hand, ma and all its substitution instances are true at 0 (0 sees a
nal simple cluster), from which S4:10 f' : 0 j= 'g and so 2ma 62 S4:10 .
A set of modal formulas containing K and closed under modus ponens
and substitution was called by Segerberg 1971] a quasi-normal logic. The
minimal quasi-normal extension of a logic L with formulas 'i , i 2 I , will be
denoted by L + f'i : i 2 I g (i.e., the operation + presupposes taking the
closure under modus ponens and substitution only). ExtL is the class of all
quasi-normal logics above L. It is easy to see that a quasi-normal logic is
normal i it is closed under the congruence rule p $ q=2p $ 2q.
Quasi-normal logics, introduced originally as some abstract (though natural) generalization of normal ones, attracted modal logicians' attention
after Solovay 1976] constructed his provability logics GL and S. The former one treats 2 as \it is provable in Peano Arithmetic" and describes
those properties of Godel's provability predicate that are provable in PA it
is normal. The latter characterizes the properties of the provability predicate that are true in the standard arithmetic model, and in view of Godel's
Incompleteness Theorem it cannot be normal. (For a detailed discussion of
provability logic consult Modal Logic and Self-reference.) Solovay showed

60

in fact that

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

S = GL + 2p ! p:

At rst sight S may appear to be inconsistent: Lob's axiom requires frames
to be irreexive, while 2p ! p is refuted in them. And indeed, no Kripke
frame validates both these axioms (in particular no consistent extension of
S is normal).
Having the algebraic semantics for normal modal logics, it is fairly easy to
construct an adequate algebraic semantics for a consistent L 2 ExtK. Let
M be a normal logic contained in L (for instance the greatest one, which is
called the kernel of L) and AM its Tarski{Lindenbaum algebra (in Section
11 of Basic Modal Logic it was called the canonical modal algebra for M ).
The set
r = f']M : ' 2 Lg
is clearly a lter in AM . By the well known properties of the Tarski{
Lindenbaum algebras, we then obtain the following completeness result:
' 2 L i under every valuation in AM the value of ' belongs to r. Structures of the form hA ri, where A is a modal algebra and r a lter in A, are
known as modal matrices. Thus, every quasi-normal logic is characterized
by a suitable class of modal matrices. It is not hard to see that L is normal
i it is characterized by a class of modal matrices with unit lters.
Now, going over to the dual (Stone{Jonsson{Tarski representation) A+
of A in a modal matrix hA ri and taking r+ to be the set of ultralters in
A containing r, we arrive at the general frame A+ with the set of distinguished points (or actual worlds) r+ . A formula ' is regarded to be valid
in hA+  r+ i i under any valuation in A+ , ' is true at all points in r+ .
Taking into account the Generation Theorem, we can conclude that every quasi-normal modal logic is characterized by a suitable class of rooted
general frames in which the root is regarded to be the only actual world.
It follows in particular that, as was rst observed by McKinsey and Tarski
1948],
K4 + f2'i : i 2 I g = K4  f2'i : i 2 I g:
However, one cannot replace here K4 by K or T. Note also that as was
shown by Segerberg 1971], K, T and some other standard normal logics
are not nitely axiomatizable with modus ponens and substitution as the
only postulated inference rules. Duality theory between modal matrices and
frames with distinguished points can be developed along with duality theory
for normal logics (for details see Chagrov and Zakharyaschev 1997]). Kripke
frames with distinguished points were used for studying quasi-normal logics
by Segerberg 1971]. Modal matrices were considered by Blok and Kohler
1983] (under the name of ltered algebras), Chagrov 1985b], and Shum
1985].

ADVANCED MODAL LOGIC

61

EXAMPLE 1.75 Consider the (transitive) frame G = hV S Qi whose underlying Kripke frame is shown in Fig. 7 and Q consists of , V , all nite sets of natural numbers and the complements to them in the space
V (so ! 2 X 2 Q i there is n < ! such that m 2 X for all m n).
Since G is irreexive and Noetherian, it validates GL. Moreover, we have
hG !i j= 2p ! p for if under some valuation ! j= 2p then p must be true
at every point. It follows that G with actual world ! validates S. (The
reader can check that by making ! reexive we again obtain a frame for S.)
By inserting the \tail" G as in Fig. 7 into nite rooted frames for GL
below their roots and using the fact that GL has FMP, one can readily
show that, for every formula ',
'2Si
(2 ! ) ! ' 2 GL:

^

22Sub'

It follows in particular that S is decidable.
This example shows that the concepts of Kripke completeness and FMP
do not play so important role in the quasi-normal case: even simple logics
require innite general frames. One possible way to cope with them at
least in the transitive case is to extend the frame-theoretic language of the
canonical formulas to the class ExtK4.
Notice rst that the canonical formulas, introduced in Section 1.6, cannot
axiomatize all logics in ExtK4. Indeed, hG wi 6j= (F D ?) i there is a
conal subreduction f of G to F satisfying (CDC) for D and the following
actual world condition as well:
(AWC) f (w) is the root of F.
Now, consider the frame hG !i constructed in Example 1.75. Since each set
X 2 Q containing ! is innite and has a dead end, it is impossible to reduce
X to  or , and so hG !i validates all normal canonical formulas. On the
other hand, we clearly have hG !i 6j= Bn for every n 1. So the logics
K4BDn cannot be axiomatized by normal canonical formulas without the
postulated necessitation.
To get over this obstacle we have to modify the denition of subreduction
so that such sets as X above may be \reduced" at least to irreexive roots
of frames. Given a frame G = hV S Qi with an irreexive root u and a
frame F = hW R P i, we say a partial map f from W onto V is a quasisubreduction of F to G if it satises (R1) for all x y 2 domf such that
f (x) 6= u or f (y) 6= u, (R2) and (R3).11 Thus, we may map all points in
the frame G in Fig. 7 to , and this map will be a quasi-reduction of G to
 satisfying (AWC). Actually, every frame is quasi-reducible to .
11 Another possibility is to allow \reductions" of X to reexive points by relaxing (R2)
cf. Section 2.6.

62

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

Now, given a nite frame F with an irreexive root a0 and a set D of
antichains in F, we dene the quasi-normal canonical formula  (F D ?)
as the result of deleting 2p0 from '0 in (F D ?) (which says that a0 is not
self-accessible) the quasi-normal negation free canonical formula  (F D)
is dened in exactly the same way, starting from (F D). It is not hard
to see that  (F D ?) (or  (F D)) is refuted in a frame hG wi i there
is a conal (respectively, plain) quasi-subreduction of G to F satisfying
(CDC) for D and (AWC). The following result is obtained by an obvious
generalization of the proof of Theorem 1.44 to frames with distinguished
points (for details see Zakharyaschev 1992]).
THEOREM 1.76 There is an algorithm which, given a modal (negation
free) formula ', constructs a nite set of normal and quasi-normal (negation free) canonical formulas such that K4 + ' = K4 + .
For example, S = K4 + () + (). Since frames for S4 are reexive,
we have
COROLLARY 1.77 There is an algorithm which, given a modal formula
', constructs a nite set of normal canonical formulas built on reexive
frames such that S4 + ' = S4 + .
As a consequence we obtain
THEOREM 1.78 (Segerberg 1975) ExtS4:3 = NExtS4:3.
Proof We must show that every logic L 2 ExtS4:3 is normal, i.e., ' 2 L
only if 2' 2 L, for every '. Suppose otherwise. Then by Corollary 1.77,
there exists (F D ?) 2 L such that 2(F D ?) 62 L. Let hG wi be a
frame validating L and refuting 2(F D ?). Since G j= S4:3, G is a chain
of non-degenerate clusters. And since it refutes (F D ?) there is a conal
subreduction f of G to F. It follows, in particular, that F is also a chain
of non-degenerate clusters and so D = . Let a be the root of F. Dene a
map g by taking
f (x)
if x 2 domf
g(x) = a
if x 2 f ;1(a)#; domf
undened otherwise.
It should be clear that g conally subreduces G to F and g(w) = a. Consequently, hG wi 6j= (F ?), which is a contradiction.
2
Let us now briey consider quasi-normal analogues of subframe and conal subframe logics in NExtK4. Those logics that can be represented in
the form
(K4  f(Fi ) : i 2 I g) + f(Fj ) : j 2 J g + f (Fk ) : k 2 K g

8<
:

ADVANCED MODAL LOGIC
A

A

A 
Fr1 A0

A


A

A 
F Au

A
A




A 

Fir A0
6
. 1
..
 ;2
6
 ;1

63
A
A



A 
Fir(!+1)A0
6

. 1
..
!

Figure 8.
are called (quasi-normal) subframe logics and those of the form
(K4  f(Fi  ?) : i 2 I g) + f(Fj  ?) : j 2 J g + f (Fk  ?) : k 2 K g
are called (quasi-normal) conal subframe logics. The classes of quasinormal subframe and conal subframe logics are denoted by QSF and
QCSF , respectively. The example of S shows that Theorem 1.52 cannot
be extended to QSF and QCSF . Yet one can show that all nitely axiomatizable logics in QSF and QCSF are decidable. We omit almost all proofs
and conne ourselves mainly to formulations of relevant results. For details
the reader is referred to Zakharyaschev 1996].
We use the following notation. For a frame F = hW Ri with irreexive
root u and 0 <  < !, Fir and Fr denote the frames obtained from F
by replacing u with the descending chains 0 : : :   ; 1 of irreexive and
reexive points, respectively Fir(!+1) = W(!+1)  R(ir!+1)  P(!+1) is the
frame that results from F by replacing u with the innite descending chain
0 1 : : : of irreexive points and then adding irreexive root !, with P(!+1)
containing all subsets of W ; fug, all nite subsets of natural numbers
f0 1 : : :g, all (nite) unions of these sets and all complements to them in
the space W(!+1) (see Fig. 8). Note that F is a quasi-reduct of every frame
of the form Fir , Fr or Fir(!+1) .
The following theorem characterizes the canonical formulas belonging to
logics in QSF and QCSF .
THEOREM 1.79 Suppose L is a subframe or conal subframe quasi-normal
logic. Then
(i) for every nite frame F with root u, (F D ?) 2 L i hF ui 6j= L
(ii) for every nite frame F with irreexive root u,  (F D ?) 2 L i
hF ui 6j= L, hFr1  0i 6j= L and Fir(!+1)  ! 6j= L.

D









E







D

E



Proof We prove only (() of (ii). Let G = hV S Qi refute  (F D ?) at

its root w and show that hG wi 6j= L. We have a conal quasi-subreduction

64

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

f of G to F such that f (w) = u. Consider the set U = f ;1 (u) 2 Q. Without
loss of generality we may assume that U = U #. There are three possible

cases.
Case 1. The point w is irreexive and fwg 2 Q. Then the restriction of
f to domf ; (U ;fwg) is a conal subreduction of G to F satisfying (AWC)
and so hG wi 6j= L.
Case 2. There is X U such that w 2 X 2 Q and, for every x 2 X ,
there exists y 2 X \ x". Then the restriction of f to domf ; (U ; X ) is a
conal subreduction of G to Fr1 satisfying (AWC) and so again hG wi 6j= L.
Case 3. If neither of the preceding cases holds then, for every X U
such that w 2 X 2 Q, the set DX = X ; X # of dead ends in X is a cover
for X , i.e., X DX #, and w 2 X ; DX 2 Q. Put
X0 = DU  : : :  Xn+1 = DU ;(X0 ::: Xn )  : : :  X! = U ; X :



<!

S

Each of these sets, save possibly X! , is an antichain of irreexive points
and belongs to Q. Besides, X  Xn# = n< ! X for every n <   !.
Therefore, the map g dened by
g(x) = f (x) ifif xx 22 VX ; U0    !
is a conal quasi-subreduction of G to Fir(!+1) satisfying (AWC).
Now using the fact that Fir(!+1)  ! 6j= L and that the composition of
(conal) (quasi-) subreductions is again a (conal) (quasi-) subreduction, it
is not hard to see that hG wi 6j= L.
2
COROLLARY 1.80 All subframe and conal subframe quasi-normal logics
above S4 have FMP.
EXAMPLE 1.81 As an illustration let us use Theorem 1.79 to characterize
those normal and quasi-normal canonical formulas that belong to S. Clearly,
either () or () is refuted at the root of every rooted Kripke frame. So all
normal canonical formulas are in S. Every quasi-normal formula  (F D ?)
associated with F containing a reexive point is also in S, since 2() is
refuted at the roots of F, Fr1 and Fir(!+1) . But no quasi-normal formula
 (F D ?) built on irreexive F belongs to S, because Fir(!+1) j= () and
Fir(!+1)  ! j= (), since f!g 62 P(!+1) . Notice that incidentally we have
proved the following completeness theorem for S.
THEOREM 1.82 S is characterized by the class

D

E





D



E







D

E

f Fir(!+1)  ! : F is a nite rooted irreexive frameg:


ADVANCED MODAL LOGIC

65

Theorem 1.79 reduces the decision problem for a logic L in QSF or
QCSF to the problem of verifying, given a nite frame F with root u,
whether hF ui, hFr1  0i and Fir(!+1)  ! refute an axiom of L. The two
former frames present no diculties: they are nite. As to the latter, it is
not hard to see that, for instance, Fir(!+1)  ! 6j=  (G ?) i Fir   ; 1 ,
for some   jGj, is conally quasi-subreducible to G. Thus we obtain

D

D

E

E



D

E



THEOREM 1.83 All nitely axiomatizable subframe and conal subframe
quasi-normal logics are decidable.
One can also give a frame-theoretic characterization of the classes QSF
and QCSF similar to Theorem 1.53. Let us say that a frame F with actual
world u is a (conal) subframe of a frame G with actual world w if F is a
(conal) subframe of G and u = w.
THEOREM 1.84 L is a (conal) subframe quasi-normal logic i L is characterized by a class of frames with actual worlds that is closed under (conal)
subframes.

1.13 Tabular logics

Every logic L having the nite model property can be represented as the intersection of some tabular logics, that is logics characterized by nite frames
(or models, algebras, matrices, etc.):

\

L = fLogF : F is a nite frame for Lg:
(It follows in particular that every fragment of L containing only those
formulas whose length does not exceed some xed n < ! is determined
by a nite frame for that reason logics with FMP are also called nitely
approximable.) In many respects tabular logics are very easy to deal with.
For instance, the key problem of recognizing whether a formula ' belongs
to a tabular L is trivially decided by the direct inspection of all possible
valuations of ''s variables in the nite frame characterizing L. That is
why the question \is it tabular?" is one of the rst items in the standard
\questionnaire" for every new logical system.
First results concerning the tabularity of modal logics were obtained by
Godel 1932] and Dugundji 1940] who showed that intuitionistic propositional logic and all Lewis' modal systems S1{S5 are not tabular. (Note that
using the same method Drabbe 1967] proved that the three non-normal
Lewis' systems S1{S3 cannot be characterized by a matrix with a nite
number of distinguished elements). For arbitrary logics in ExtK one can

66

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

easily prove the following syntactical criterion of tabularity, which uses the
formulas
n = :('1 ^ 3('2 ^ 3('3 ^ : : : ^ 3'n) : : :))

n =

^ :3m(3' ^ : : : ^ 3'n)

n;1

m=0

1

tabn = n ^ n

where 'i = p1 ^ : : : ^ pi;1 ^ :pi ^ pi+1 ^ : : : ^ pn .
THEOREM 1.85 L 2 ExtK is tabular i tabn 2 L, for some n < !.

Proof A frame F = hW Ri refutes n at a point x1 i a chain of length n

starts from x1 , and F refutes n at x1 i there is a chain x1 Rx2 R : : : Rxm
of length m < n such that xm is of branching n, i.e., xm Ry1  : : :  xm Ryn
for some distinct y1  : : :  yn . It follows that every rooted generated (by an
actual world) subframe of the canonical frame for L containing tabn has at
most 1 + (n ; 1) + : : : + (n ; 1)n;2 points.
2
As a consequence we immediately obtain

COROLLARY 1.86 Every tabular modal logic has nitely many extensions
and all of them are also tabular.
The next theorem follows from general algebraic results of Blok and
Kohler 1983] equally easy it can be proved using the characterization above.
THEOREM 1.87 Every tabular logic L 2 ExtK is nitely axiomatizable.

Proof According to Theorem 1.85, L is an extension of K + tabn, for some
n < !. By Corollary 1.86, we have a chain

K + tabn = L1  L2  : : :  Lk;1  Lk = L
of quasi-normal logics such that fL0 2 ExtK : Li  L0  Li+1 g = , for

every i = 1 : : :  k ;1. It remains to notice that if L0 is nitely axiomatizable,
L0  L00 and there is no logic located properly between L0 and L00 then L00
is also nitely axiomatizable (e.g. L00 = L0 + ', for any ' 2 L00 ; L0).
2
Theorem 1.12 provides us in fact with an algorithm to decide, given a
tabular logic L 2 NExtK4 and an arbitrary formula ', whether K4' = L.
Indeed, notice rst that we have

ADVANCED MODAL LOGIC

67

THEOREM 1.88 Each nitely axiomatizable logic L 2 NExtK4 of nite
depth is a nite union-splitting, i.e., can be represented in the form

L = K4  f] (Fi  ?) : i 2 I g
with nite I .

Proof Let L = K4  ' be a logic of depth n and let m be the number of
variables in '. We show that L coincides with the logic

L0 = K4  f] (G ?) : jGj 

X 2mcm(i) G 6j= 'g

n+1
i=1

(cm (i) was dened in Section 1.2). The inclusion L  L0 is obvious. Suppose
' 62 L0 . Then there is a rooted rened m-generated frame F for L0 refuting
'. Clearly, F is of depth  n, since otherwise ] (G ?) is an axiom of L0
for every rooted generated subframe G of F of depth n + 1 and so F 6j= L0,
which is a contradiction. But then ] (F ?) is an axiom of L0 , contrary to
our assumption.
2
Thus, all tabular logics in NExtK4 are nite union-splittings and so, by
Theorem 1.12, we obtain the following
THEOREM 1.89 Let L be a tabular logic in NExtK4.
(i) (Blok 1980c) L has nitely many immediate predecessors and they are
also tabular.
(ii) The axiomatizability problem for L above K4 is decidable.
For logics in NExtK this is not the case, witness Theorems 1.36 and 4.13.
The tabularity criterion of Theorem 1.85 is not e ective. Moreover, as
we shall see in Section 4.4, no e ective tabularity criterion exists in general.
However, if we restrict attention to suciently strong logics, e.g. to the
class NExtS4, the tabularity problem turns out to be decidable. The key
idea, proposed by Kuznetsov 1971], is to consider the so called pretabular
logics.
A logic L 2 (N)ExtL0 is said to be pretabular in the lattice (N)ExtL0 , if
L is not tabular but every proper extension of L in (N)ExtL0 is tabular. In
other words, a pretabular logic in (N)ExtL0 is a maximal non-tabular logic
in (N)ExtL0 .
THEOREM 1.90 In the lattices ExtK and NExtK every non-tabular logic
is contained in a pretabular one.

68

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

1

6



6



6

.
..

G!

. 2
..
mP
H
i
P
Y
HP

I HP
@
6
P

P
n . @ H 
3   

..  ;


1  ;;

6

;
G!mn

a0 
6
a1 @
YH
H
I
6
HH
a2  b@
1  b2    
 ;

6
a3  ;;
6
a4 ;
G!22

Figure 9.

Proof By Theorem 1.85, a logic is non-tabular i it does not contain the

formula tabn , for any n < !. It follows that the union of an ascending
chain of non-tabular logics is a non-tabular logic as well. The standard use
of Zorn's Lemma completes the proof.
2
If there is a simple description of all pretabular logics in a lattice, we
obtain an e ective (modulo the description) tabularity criterion for the lattice. Indeed, take for deniteness the lattice NExtK4. How to determine,
given a formula ', whether K4  ' is tabular? We may launch two parallel
processes: one of them generates all derivations in K4  ' and stops after
nding a derivation of tabn , for some n < ! another process checks if '
belongs to a pretabular logic in NExtK4 and stops if this is the case. The
termination of the rst process means that K4  ' is tabular, while that of
the second one shows that it is not tabular.
Unfortunately, it is impossible to describe in an e ective way all pretabular logics in (N)ExtK and even (N)ExtK4: Blok 1980c] and Chagrov
1989] constructed a continuum of them. However, for smaller lattices like
NExtS4 or NExtGL such descriptions were found by Maksimova 1975b],
Esakia and Meskhi 1977] and Blok 1980c]. The ve pretabular logics in
NExtS4 were presented in Section 17 of Basic Modal Logic. In NExtGL
the picture is much more complicated.
THEOREM 1.91 (Blok 1980c, Chagrov 1989) The set of pretabular logics
in NExtGL is denumerable. It consists of the logics GL:3 = LogG! and
LogG!mn, for m 0, n 1, where G! and G!mn are the frames depicted in
Fig. 9. If hm ni 6= hk li then LogG!mn 6= LogG!kl .

Using this semantic description of pretabular logics in NExtGL, it is not

ADVANCED MODAL LOGIC

69

hard to nd nite sets of formulas axiomatizing them. Moreover, all of them
turn out to be decidable. For we have
THEOREM 1.92 Every non-tabular logic L 2 NExtK4 has a non-tabular
extension with FMP, and so every pretabular logic in NExtK4 has FMP.
Proof Since L is non-tabular and characterized by the class of its rooted
nitely generated rened frames, we have either a sequence Fi , i = 1 2 : : :,
of rooted nite frames for L of depth i, or a sequence Fi of rooted nite
frames for L of width i. In both cases the logic LogfFi : i < !g  L is
non-tabular and has FMP.
2
So we obtain the following result on the decidability of tabularity.
THEOREM 1.93 The property of tabularity is decidable in NExtS4, ExtS4,
NExtGL, ExtGL.
Since a logic in ExtK4 is locally tabular i it is determined by a frame
of nite depth, the property of local tabularity is decidable in the lattices
mentioned in Theorem 1.93 as well. However, this is not the case for ExtK4
itself.

1.14 Interpolation

One of the fundamental properties of logics is their capability to provide
explicit denitions of implicitly denable terms, which is known as the Beth
property (Beth 1953] proved it for classical logic). In the modal case we
say a logic L has the Beth property if, for any formula '(p1  : : :  pn  pn+1 )
and variables p and q di erent from p1  : : :  pn ,
'(p1  : : :  pn  p) ^ '(p1  : : : pn  q) ! (p $ q) 2 L
only if there is a formula (p1  : : : pn ) such that
'(p1  : : :  pn  p) ! (p $ (p1  : : : pn )) 2 L:
The Beth property turns out to be closely related to the interpolation property which was introduced by Craig 1957] for classical logic. Namely, we
say that a logic L has the interpolation property if, for every implication
 !  2 L, there exists a formula  , called an interpolant for  !  in L,
such that  !  2 L,  !  2 L and every variable in  , if any, occurs in
both  and  . While in abstract model theory interpolation is weaker than
Beth denability, for modal logics we have
THEOREM 1.94 (Maksimova 1992) A normal modal logic has interpolation i it has the Beth property.

70

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

Say also that a normal modal logic L has the interpolation property for
the consequence relation `L , ` -interpolation for short, if every time when
 `L  , there is a formula  such that  `L  ,  `L  and Var
Var \ Var. (Here Var' is the set of all variables in '.) It should be
clear that interpolation implies ` -interpolation.
By the end of the 1970s interpolation had been established for a good
many standard modal systems. The semantical proofs, sometimes rather
sophisticated, resemble the Henkin construction of the canonical models.
Here are two examples of such proofs (which are due to Maksimova 1982b]
and Smorynski 1978]).
THEOREM 1.95 (Gabbay 1972) The logics K, K4, T, S4 have the interpolation property.

Proof We consider only S4 for the other logics the proofs are similar.
Suppose  !  62 S4 and  !  62 S4 for any  whose variables occur in
both  and  , and show that in this case  !  62 S4.
Let t = (; ) be a pair of sets of formulas such that Var' Var if
' 2 ; and Var' Var if ' 2 . Say that t is inseparable if there are
no
'i 2 ;, j 2W and  with Var Var \ Var such that
Vni=1formulas
'i !  2 S4,  ! mi=1 i 2 S4. The pair t is called complete if for
every ' and  with Var' Var and Var Var , one of the formulas
' and :' is in ; and one of  and : is in .

LEMMA 1.96 Every inseparable pair t0 = (;0 
complete inseparable pair.

0

) can be extended to a

Proof Let '1 '2  : : : and 1  2 : : : be enumerations of all formulas whose

variables occur in  and  , respectively. Dene pairs t0n = (;0n  0n ) and
tn+1 = (;n+1  n+1 ) inductively by taking

t0n =

(;n  f'n g n ) if this pair is inseparable
(;n  f:'n g n ) otherwise,

(;0n  0n  fn g) if this pair is inseparable
(;0n  0n  f:n g) otherwise
and put t = (;  ), where ; = n<! ;n ,
= n<! n . Clearly
t is complete. Suppose it is separable, i.e., for some '1  : : :  'n 2 ; ,
1  : : :  m 2 and somen  containing only those variables
that occur in
both  and  , we have i=1 'i !  2 S4 and  ! m

i
i=1 2 S4. Then
there is k < ! such that '1  : : :  'n 2 ;k and 1  : : :  m 2 k , which means
that tk is separable. So it remains to show that if t = (; ) is inseparable,
Var' Var and Var Var then

tn+1 =

S

V

S

W

ADVANCED MODAL LOGIC

71

 one of the pairs (;  f'g ) or (;  f:'g ) is inseparable and
 one of the pairs (;  fg) or (;  f:g) is inseparable.
We prove only the former claim. Suppose, on the contrary, that both pairs
are separable, i.e., there are formulas 1 , 2 in variables occurring in both
 and  such that, for some '1  : : :  'n 2 ;, 1  : : :  m 2 , we have

'1 ^ : : : ^ 'n ^ ' ! 1 2 S4 1 ! 1 _ : : : _ m 2 S4
'1 ^ : : : ^ 'n ^ :' ! 2 2 S4 2 ! 1 _ : : : _ m 2 S4:
Then we obtain ('1 ^ : : : ^ 'n ^ ') _ ('1 ^ : : : ^ 'n ^ :') ! 1 _ 2 2 S4,
1 _ 2 ! 1 _ : : : _ m 2 S4, from which
'1 ^ : : : ^ 'n ! 1 _ 2 2 S4 1 _ 2 ! 1 _ : : : _ m 2 S4
contrary to t being inseparable.
2
Now we dene a frame F = hW Ri by taking W to be the set of all
complete and inseparable pairs and, for t1 = (;1  1 ), t2 = (;2  2 ) in W ,
t1 Rt2 i 2' 2 ;1 implies ' 2 ;2 . Using the axioms 2p ! p and 2p ! 22p
of S4, one can readily check that R is a quasi-order on W , i.e., F j= S4.
Dene a valuation V in F by taking for every variable p 2 Var( !  ),
V(p) = f(; ) 2 W : either p 2 ; or p 2 Var and p 62 g. Put
M = hF Vi. By induction on the construction of formulas ' and  with
Var' Var, Var Var one can show that for every t = (; ) in F
(M t) j= ' i ' 2 ; (M t) 6j=  i  2 :
Indeed, the basis of induction follows from the denition of V and the
completeness and inseparability of t. The cases of the Boolean connectives
present no diculty. So suppose ' = 2'1 . If t j= 2'1 then, for every
t0 = (;0  0 ) 2 t", we have t0 j= '1 and so '1 2 ;0 . Suppose 2'1 62 ;. Then
:2'1 2 ;. Consider the pair t0 = (;0  0 ), where
;0 = f:'1 g  f : 2 2 ;g 0 = f: : :2 2 g
and show that it is inseparable. Assume otherwise. Then there is  with
Var Var \ Var such that, for some formulas 21 : : :  2n 2 ;,
:2n+1  : : :  :2m 2 ,
:'1 ^ 1 ^ : : : ^ n !  2 S4  ! :n+1 _ : : : _ :m 2 S4:
It follows that
:2'1 ^ 21 ^ : : : ^ 2n ! 3 2 S4

72

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

3 ! :2n+1 _ : : : _ :2m 2 S4
contrary to t being inseparable. Let t0 = (;0  0 ) be a complete inseparable
extension of t0 . By the denition of t0 , we have tRt0 and so '1 2 ;0 , contrary
to :'1 2 ;0 ;0 and t0 being inseparable.
Suppose now that 2'1 2 ;. Then for every t0 = (;0  0 ) such that tRt0,
we have '1 2 ; and so t0 j= '1 . Consequently, t j= 2'1 . The formula  is
treated in the dual way.
To complete the proof it remains to observe that M 6j=  !  .
2
This proof does not always go through for di erent kinds of logics. However, sometimes suitable modications are possible.
THEOREM 1.97 GL has the interpolation property.
Proof Suppose  !  has no interpolant in GL. Our goal is to construct
a nite irreexive transitive frame refuting  !  .
This time we consider nite pairs t = (; ) such that all formulas in ;
and are constructed from variables and their negations using ^, _, 2, 3.
Without loss of generality we will assume  and  to be formulas of that
sort. Say that t is separable if there is a formula  with Var Var\Var
such that ; !  2 GL and  !
2 GL. It should be clear that if
t = (; ) is a nite inseparable pair then in the same way as in the proof
of Theorem 1.95 but taking only subformulas of  and  we can obtain
a nite inseparable pair t? = (;?  ? ) satisfying the conditions: for every
' 2 Sub and  2 Sub , one of the formulas ' and :' (an equivalent
formula of the form under consideration, to be more precise) is in ;? and
one of  and : is in ? .
Now we construct by induction a nite rooted model for GL refuting
 !  . As its root we take (fg?  f g? ). If we have already put in our
model a pair t = (; ) and it has not been considered yet, then for every
3' 2 ; and every 2 2 , we add to the model the pairs
t1 = (f 2 2:' ' : 2 2 ;g?  f 3 : 3 2 g? )
t2 = f 2 : 2 2 ;g? f 3 3:  : 3 2 g?):
One can readily show that if t is inseparable then t1 and t2 are also inseparable. Put tR0 t1 and tR0 t2 . The process of adding new pairs must
eventually terminate, since each step reduces the number of formulas of the
form 3' and 2 in the left and right parts of pairs. Let W be the set of
all pairs constructed in this way and R the transitive closure of R0 . Clearly,
the resulting frame F = hW Ri validates GL. Dene a valuation V in F by
taking, for each variable p,
V(p) = f(; ) 2 W : p 2 ;g:

V

W

ADVANCED MODAL LOGIC

73

As in the proof of Theorem 1.95, it is easily shown that  !  is refuted in
F under V.
2
To clarify the algebraic meaning of interpolation we require the following
well known proposition.
PROPOSITION 1.98 If r is a normal lter12 in a modal algebra A then
the relation r , dened by a r b i a $ b 2 r, is a congruence relation.
The map r 7! r is an isomorphism from the lattice of normal lters in A
onto the lattice of congruences in A.
Denote by A=r the quotient algebra A= r and let kakr = fb : a r bg.
Say that a class C of algebras is amalgamable if for all algebras A0 , A1,
A2 in C such that A0 is embedded in A1 and A2 by isomorphisms f1 and f2,
respectively, there exist A 2 C and isomorphisms g1 and g2 of A1 and A2
into A with g1 (f1 (x)) = g2 (f2 (x)), for any x in A0. If in addition we have
gi (x)  gj (y) implies 9z 2 A0 (x i fi (z ) and fj (z ) j y)
for all x 2 Ai , y 2 Aj such that fi j g = f1 2g, then C is called superamalgamable. Here Ai is the universe of Ai and i its lattice order.
THEOREM 1.99 (Maksimova 1979) L has the interpolation property i the
variety AlgL of modal algebras for L is superamalgamable. L has the ` interpolation property i AlgL is amalgamable.
Proof We prove only the former claim. ()) Suppose L has the interpolation property and A0 , A1, A2 are modal algebras for L such that A0 is
a subalgebra of both A1 and A2 . With each element a 2 Ai , i = 0 1 2,
we associate a variable pia in such a way that, for a 2 A0 , p0a = p1a = p2a.
Denote by Li the language with the variables pia , for a 2 Ai , i = 0 1 2, and
let L = L1  L2 . We will assume that L is the language of L.
Fix the valuation Vi of Li in Ai , dened by Vi (pia ) = a, and put
#i = f' 2 ForLi : Vi (') = >g:
Let # be the closure of #1  #2  L under modus ponens. We show that,
for every ' 2 ForLi ,  2 ForLj such that fi j g = f1 2g,
' !  2 # i 9 2 ForL0 (' !  2 #i and  !  2 #j ): (13)
Suppose ' !  2 #. Then there exist nite sets ;i #i and ;j #j such
that
;i ^ ' ! ( ;j ! ) 2 L:

^

^

12 A lter r is normal (or open, as in Section 10 of Basic Modal Logic) if 2a 2 r
whenever a 2 r.

74

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

Since L has interpolation, there is a formula  2 ForL0 such that

^ ;i ^ ' !  2 L ^ ;j ! ( ! ) 2 L

from which ' !  2 #i and  !  2 #j . The converse implication is
obvious.
Now construct an algebra A by taking the set fk'k : ' 2 #g as its
universe, where k'k = f : ' $  2 #g, k'k ^ kk = k' ^ k and
$k'k = k $ 'k, for $ 2 f: 2g. One can readily prove that A 2 AlgL.
Dene maps gi from Ai into A by taking gi (a) = kpiak. It is not dicult to
show that gi is an embedding of Ai in A. And for a 2 A0 , we have

g1 (a) = kp0a k = g2 (a):
It remains to check the condition for superamalgamability: Suppose a 2 Ai ,
b 2 Aj , fi j g = f1 2g, and gi (a)  gj (b). Then gi (a) ! gj (b) = > and
so kpia ! pjb k = >, i.e., pia ! pjb 2 #. By (13), we have  2 ForL0 with
V() = c such that a i c j b.
(() Assuming AlgL to be superamalgamable, we show that L has the
interpolation property. To this end we require
LEMMA 1.100 Suppose A0 is a subalgebra of modal algebras A1 and A2 ,
a 2 A1 , b 2 A2 and there is no c 2 A0 such that a 1 c 2 b. Then
there are ultralters r1 in A1 and r2 in A2 such that a 2 r1 , b 62 r2 and
r1 \ A0 = r2 \ A0 .
Suppose '(p1  : : :  pm  q1  : : :  qn ) and (q1  : : :  qn  r1  : : :  rl ) are formulas for which there is no (q1  : : :  qn ) such that ' !  2 L and  !  2 L.
We show that in this case there exists an algebra A 2 VarL refuting ' ! .
Let A00 , A01 and A02 be the free algebras in AlgL generated by the sets
fc1  : : :  cn g, fa1  : : :  am  c1  : : :  cn g and fc1  : : :  cn  b1  : : :  bl g, respectively.
According to this denition, A00 is a subalgebra of both A01 and A02 . By
Lemma 1.100, there are ultralters r1 in A01 and r2 in A02 such that we
have '(a1  : : :  am c1  : : :  cn ) 2 r1 and (c1  : : :  cn  b1  : : :  bl ) 62 r2 . Dene normal lters
ri = fa 2 A0i : 8m < ! 2m a 2 ri g

and put A1 = A01 =r1 , A2 = A02 =r2 . Construct an algebra A0 by taking
A0 = fkakr1 : a 2 A00 g. By the denition, A0 is a subalgebra of A1 , i.e., is
embedded in A1 by the map f1 (x) = x. One can show that A0 is embedded
in A2 by the map f2 (kxkr1 ) = kxkr2 . Then there are an algebra A for L
and isomorphisms g1 and g2 of A1 and A2 into A satisfying the conditions
of superamalgamability. Dene a valuation V in A by taking V(pi ) =




ADVANCED MODAL LOGIC

75


H
Y

H 
H
H
;  H H H
;
H
I 
@
;
Y
H
;

H
@ 
 H H H ; ; @
I  
@

@

@



@
@ 

;

;

H
Y

H



Figure 10.

g1 (kai kr1 ), V(qj ) = g1 (kcj kr1 ) = g2 (kcj kr2 ) and V(rk ) = g2(kbk kr2 ).
Then V(') 6 V() because otherwise there would exist fi j g = f1 2g and
z 2 A0 such that V(') i fi (z ) and fj (z ) j V(). Thus, A 6j= ' !  and
so ' !  62 L.
2
Using this theorem Maksimova 1979] discovered a surprising fact: there
are only nitely many logics in NExtS4 with the interpolation property
(not more than 38, to be more exact) and all of them turned out to be
union-splittings. By Theorem 1.12, we obtain then
THEOREM 1.101 (Maksimova 1979) There is an algorithm which, given a
modal formula ', decides whether S4  ' has interpolation.
We illustrate this result by considering a much simpler class of logics.
THEOREM 1.102 Only four logics in NExtS5 have the interpolation property: S5 itself, the logic of the two-point cluster, Triv and For.

Proof We have already demonstrated how to prove that a logic has interpolation. So now we show only that no logic L in NExtS5 di erent from

those mentioned in the formulation has the interpolation property. Suppose
on the contrary that L has interpolation. We use the amalgamability of the
variety of modal algebras for L to show that an arbitrary big nite cluster
is a frame for L, from which it will follow that L = S5.

76

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

Figure 10 demonstrates two ways of reducing the three-point cluster to
the two-point one. By the amalgamation property, there must exist a cluster reducible to the two depicted copies of the two-point cluster, with the
reductions satisfying the amalgamation condition. It should be clear from
Fig. 10 that such a cluster contains at least four points. By the same scheme
one can prove now that every n-point cluster validates L.
2
It would be naive to expect that such a simple picture can be extended
to classes like NExtK4 or NExtK. Even in NExtGL the situation is quite
di erent from that in NExtS4: Maksimova 1989] discovered that there is
a continuum of logics in NExtGL having the interpolation property. This
result is based upon the following observation. For L 2 NExtK4, we call a
formula (p) conservative in NExtL if

2+ ((?) ^ (p) ^ (q)) ! (p ! q) ^ (2p) 2 L:
For example, in NExtS4 conservative are 23p ! 32p, 23p $ 32p, and
2p $ 3p.
THEOREM 1.103 (Maksimova 1987) If L 2 NExtK4 has the interpolation
property and formulas i , for i 2 I , are conservative in NExtL, then the
logic L  fi : i 2 I g also has the interpolation property.
Proof Suppose ' !  2 L fi : i 2 I g. Then there is a nite J I , say
J = f1 : : : lg, such that ' !  2 L  fi : i 2 J g and so, as follows from

the denition of conservative formulas and the Deduction Theorem for K4,

2+

^l (j (?) ^ j (p ) ^ : : : ^ j (pn)) ! (' ! ) 2 L
1

j =1

where p1  : : :  pm  pm+1  : : :  pk and pm+1 : : :  pk  pk+1  : : :  pn are all the
variables in ' and , respectively. Consequently

2+

^l (j (?) ^ j (p ) ^ : : : ^ j (pk )) ^ ' !
1

j =1

(2+

^l (j (pm ) ^ : : : ^ j (pn)) ! ) 2 L:

j =1

+1

Since L has the interpolation property, there is (pm+1  : : :  pk ) such that
l
^
2 (j (?) ^ j (p ) ^ : : : ^ j (pk )) ^ ' !  2 L
+

j =1

1

ADVANCED MODAL LOGIC

2+

77

^l (j (pm ) ^ : : : ^ j (pn)) ! ( ! ) 2 L:

j =1

+1

Then we obtain ' !  2 L  fi : i 2 I g and  !  2 L  fi : i 2 I g,
i.e.,  is an interpolant for ' !  in L  fi : i 2 I g.
2
Using the formulas

i = 2+ (3i+1 > ^ 2i+2 ? ! 2i+1 p _ 2i+1 :p)

which are conservative in NExtGL, one can readily construct a continuum
of logics in this class with the interpolation property. The set of logics in
NExtGL without interpolation is also continual.
In general, an interpolant  for an implication  !  2 L depends on
both  and  . Say that a logic L has uniform interpolation if, for any
nite set of variables $ and any formula , there exists a formula  such
that Var $ and  !  2 L,  !  2 L whenever Var \ Var $
and  !  2 L. In this case  is called a post-interpolant for  and
$. Roughly speaking, a logic has uniform interpolation if we can choose
an interpolant for  !  2 L independly from the actual shape of  .
Uniform interpolation was rst investigated by Pitts 1992] who proved that
intuitionistic logic enjoys it. It is fairly easy to nd multiple examples
of modal logics with uniform interpolation by observing that any locally
tabular logic with interpolation has uniform interpolation as well. Indeed,
for every formula  and every set of variables $, we can dene a postinterpolant  as the conjunction of a maximal set of pairwise non-equivalent
in L formulas  0 such that Var 0 $ and  !  0 2 L (which is nite in view
of the local tabularity of L). It follows, for instance, that S5 has uniform
interpolation. In general, however, interpolation does not imply uniform
interpolation: Ghilardi and Zawadowski 1995] showed that S4 does not
enjoy the latter, witness the following formula without a post-interpolant
for frg in S4

p ^ 2(p ! 3q) ^ 2(q ! 3p) ^ 2(p ! r) ^ 2(q ! :r):
Only a few positive results on the uniform interpolation of modal logics
are known: Shavrukov 1993] proved it for GL, Ghilardi 1995] for K, and
Visser 1996] for Grz.
A property closely related to interpolation is so called Hallden completeness. A logic L is said to be Hallden complete if ' _  2 L and
Var' \ Var =  imply ' 2 L or  2 L. Since every variable free formula is equivalent in D either to > or to ?, L 2 ExtD is Hallden complete
whenever it has interpolation. K, K4, GL are examples of Hallden incomplete logics with interpolation: each of them contains 3> _ :3> but not

78

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

3> and :3>. On the other hand, S4:3 is a Hallden complete logic (see

van Benthem and Humberstone 1983]) without interpolation (see Maksimova 1982a]). Actually, there is a continuum of Hallden complete logics in
NExtS4 (see Chagrov and Zakharyaschev 1993]).
Hallden completeness has an interesting lattice-theoretic characterization.
THEOREM 1.104 (Lemmon 1966c) A logic L 2 ExtK is Hallden complete
i it is -irreducible in ExtL.
Since the lattice ExtS5 is linearly ordered by inclusion, all logics above
S5 are Hallden complete. There are various semantic criteria for Hallden
completeness (see e.g. Maksimova 1995]). Here we note only the following
generalization of the result of van Benthem and Humberstone 1983].

T

THEOREM 1.105 Suppose a logic L 2 ExtK is characterized by a class
C of descriptive rooted frames with distinguished roots. Then L is Hallden
complete i, for all frames hF1  d1 i and hF2  d2 i in C , there is a frame hF di
for L reducible13 to both hF1  d1 i and hF2  d2 i.
For more results and references on Hallden completeness consult Chagrov
and Zakharyaschev 1991].
2 POLYMODAL LOGICS
