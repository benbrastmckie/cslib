<!-- Source: Zakharyaschev, Wolter & Chagrov (2001). Advanced Modal Logic. Section 3: Superintuitionistic Logics — extensions of Int, modal companions. -->

Although C.I. Lewis constructed his rst modal calculus S3 in 1918, it
was Godel's 1933] two page note that attracted serious attention of mathematical logicians to modal systems. While Lewis 1918] used an abstract
necessity operator to avoid paradoxes of material implication, Godel 1933]
and earlier Orlov 1928]16 treated 2 as \it is provable" to give a classical interpretation of intuitionistic propositional logic Int by means of embedding
it into a modal \provability" system which turned out to be equivalent to
Lewis' S4.
Approximately at the same time Godel 1932] observed that there are
innitely many logics located between Int and classical logic Cl, which|
together with the creation of constructive (proper) extensions of Int by
Kleene 1945] and Rose 1953] (realizability logic), Medvedev 1962] (logic
of nite problems), Kreisel and Putnam 1957]|gave an impetus to studying the class of logics intermediate between Int and Cl, started by Umezawa
1955, 1959]. Godel's embedding of Int into S4, presented in an algebraic
form by McKinsey and Tarski 1948] and extended to all intermediate logics
by Dummett and Lemmon 1959], made it possible to develop the theories
of modal and intermediate logics in parallel ways. And the structural results
of Blok 1976] and Esakia 1979a,b], establishing an isomorphism between
the lattices ExtInt and NExtGrz, along with preservation results of Maksimova and Rybakov 1974] and Zakharyaschev 1991], transferring various
properties from modal to intermediate logics and back, showed that in many
respects the theory of intermediate logics is reducible to the theory of logics
in NExtS4.
16 Orlov's paper remained unnoticed till the end of the 1980s. It is remarkable also for
constructing the rst system of relevant logic.

ADVANCED MODAL LOGIC

For
Cl
SmL
KC
LC
SL
KP
BDn

=
=
=
=
=
=
=
=

Int + p
Int + p _ :p
Int + (:q ! p) ! (((p ! q) ! p) ! p)
Int + :p _ ::p
Int + (p ! q) _ (q ! p)
Int + ((::p ! p) ! :p _ p) ! :p _ ::p
Int + (:p ! q _ r) ! (:p ! q) _ (:p ! r)
Int + bdn, where

BWn
BTWn
Tn
Bn
NLn

=
=
=
=
=

Int + Vni=0(pi ! j6=i pj )
Wni=0(:pi ! Wj6=i :pj )
Int + V0i<jn :(W:pi ^ :pj ) !
Int + Vni=0((pi ! Wi6=j pj ) ! WWi6=j pj ) ! Wni=0 pi
Int + ni=0(:pi $ i6=j pj ) ! ni=0 pi
Int + nf n, where

111

bd1 = Wp1 _ :p1  bdWn+1 = pn+1 _ (pn+1 ! bdn)

nf 0 = ?, nf 1 = p, nf 2 = :p, nf ! = >
nf 2m+3 = nf 2m+1 _ nf 2m+2,
nf 2m+4 = nf 2m+3 ! nf 2m+1

Table 5. A list of standard superintuitionistic logics
To demonstrate this as well as some features of intermediate logics is
the main aim of this part. We will use the same system of notations as
in the modal case. In particular, ExtInt is the lattice of all logics of the
form Int + ; (where ; is an arbitrary set of formulas in the language of
Int and + as before means taking the closure under modus ponens and
substitution) we call them superintuitionistic logics or si-logics for short.
Basic facts about the syntax and semantics of Int and relevant references
can be found in Intuitionistic Logic. A list of some \standard" si-logics is
given in Table 5.

3.1 Intuitionistic frames
As in the case of modal logics, the adequate relational semantics for si-logics
can be constructed on the base of the Stone representation of the algebraic
\models" for Int, known as Heyting (or pseudo-Boolean) algebras. It is hard
to trace now who was the rst to introduce intuitionistic general frames|the
earliest references we know are Esakia 1974] and Rautenberg 1979]|but in
any case, having at hand Jonsson and Tarski 1951] and Goldblatt 1976a],
the construction must have been clear.

112

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

An intuitionistic (general) frame is a triple F = hW R P i in which R is a
partial order on W 6=  and P , the set of possible values in F, is a collection
of upward closed subsets (cones) in W containing  and closed under the
Boolean \, , and the operation ( (for !) dened by

X ( Y = fx 2 W : 8y 2 x" (y 2 X ! y 2 Y )g:
If P contains all upward closed subsets in W then we call F a Kripke frame
and denote it by F = hW Ri. An important feature of intuitionistic models
M = hF Vi (V, a valuation in F, maps propositional variables to sets in P )
is that V('), the truth-value of a formula ', is always upward closed.
Every intuitionistic frame F = hW R P i gives rise to the Heyting algebra
F+ = hP \  ( i called the dual of F. Conversely, given a Heyting algebra
A = hA ^ _ ! ?i, we construct its relational representation A+ = hW Ri
by taking W to be the set of all prime lters in A (a lter r is prime if it
is proper and a _ b 2 r implies a 2 r or b 2 r), R to be the set-theoretic
inclusion and
P = ffr 2 W : a 2 rg : a 2 Ag:
It is readily checked that A+ , the dual of A, is an intuitionistic frame,
A
= (A+ )+ and A+ is di erentiated, tight in the sense that

xRy i 8X 2 P (x 2 X ! y 2 X )
and compact, i.e., for any families X

P and Y fW ; X : X 2 P g,

\(X  Y ) = fx 2 W : 8X 2 X 8Y 2 Y (x 2 X ^ x 2 Y )g 6= 
T
whenever (X  Y ) 6=  for every nite subfamilies X
X, Y

Y.
Frames with these three properties (actually di erentiatedness follows from
tightness) are called descriptive. In the same way as in the modal case
one can prove that F is descriptive i F 
= (F+ )+ . Duality between the
basic truth-preserving operations on algebras and descriptive frames (the
denitions of generated subframes, reductions and disjoint unions do not
change) is also established by the same technique.
Since every consistent si-logic L is characterized by its Tarski{Lindenbaum algebra AL, we conclude that L is characterized also by a class of intuitionistic frames, say by the dual of AL.
Rened nitely generated frames for Int look similarly to those for K4:
the only di erence is that now all clusters are simple and the truth-sets must
be upward closed. Fig. 13 showing (a) the free 1-generated Heyting algebra
AInt (1) and (b) its dual FInt(1) will help the reader to restore the details.
AInt (1) was rst constructed by Rieger 1949] and Nishimura 1960] it is
called the Rieger{Nishimura lattice. The formulas nf n dened in Table 5
0

0

0

0

ADVANCED MODAL LOGIC

113

>

:::







 nf
 9

nf 10@
I
@
;
I
@
;
@
@
;
@ nf
nf 7 
8

;
I
@

;
; @
;
@;
nf 5
nf 6 ;
I
@
@
;
I
@
;
@
@
;
@ nf
nf 3 
4
nf

2

I
@
6
@

4

@ * 3
I
@
6
6
@ @@
6  @ * 5
I
@
6
6
@ @
@
8  @ * 7
I@ @ 6
@
6
10 @ @ 9

@
;
I

;
;
@
;
;
@
;
 1
2
I
@

;
@
;
@;
A
?

nf

(a)

p

* 1
6

F<Int1 (1)

Int (1)



(b)

Figure 13.
and used for the construction are known as Nishimura formulas (see also
Section 3 of Intuitionistic Logic).
At the algebraic level the connection between Int and S4 discovered by
Godel is reected by the fact, established in Mckinsey and Tarski 1946],
that the algebra of open elements (i.e., elements a such that 2a = a) of
every modal algebra for S4 (known as a topological Boolean algebra see
Rasiowa and Sikorski 1963]) is a Heyting algebra and conversely, every
Heyting algebra is isomorphic to the algebra of open elements of a suitable
algebra for S4. We explain this result in the frame-theoretic language.
Given a frame F = hW R P i for S4 (which means that R is a quasiorder on W ), we denote by W the set of clusters in F|more generally,
X = fC (x) : x 2 X g|and put C (x)C (y) i xRy,
P = fX : X 2 P ^ X = 2X g = fX : X 2 P ^ X = X"g:
It is readily checked that the structure F = hW R P i is an intuitionistic frame (for instance, (X ) ( (Y ) = (2(;X  Y ))) we call it the
skeleton of F. The skeleton of a model M = hF Vi for S4 is the intuitionistic
model M = hF Vi, where V(p) = V(2p).
Denote by T the Godel translation prexing 2 to all subformulas of a
given intuitionistic formula.17 By induction on the construction of ' one
17

The translation dened in Godel 1933] does not prex 2 to conjunctions and dis-

114

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

can easily prove the following
LEMMA 3.1 (Skeleton) For every model M for S4, every intuitionistic formula ' and every point x in M,
(M C (x)) j= ' i (M x) j= T ('):
It follows that ' 2 Int implies T (') 2 S4. To prove the converse we
should be able to convert intuitionistic frames F into modal ones with the
skeleton (isomorphic to) F. This is trivial if F is a Kripke frame|we can
just regard it to be a frame for S4, which in view of the Kripke completeness
of both Int and S4, shows that T really embeds the former into the latter,
i.e.,
' 2 Int i T (') 2 S4:
In general, the most obvious way of constructing a modal frame from an
intuitionistic frame F = hW R P i is to take the closure P of P under the
Boolean operations \,  and !. It is well known in the theory of Boolean
algebras (see Rasiowa and Sikorski 1963]) that for every X W , X is in
P i
X = (;X1  Y1 ) \ : : : \ (;Xn  Yn )
for some X1  Y1  : : :  Xn Yn 2 P and n 1. It follows that if X 2 P then
2X = (X1 ( Y1 ) \ : : : \ (Xn ( Yn ) 2 P P
and so P is closed under 2 in hW Ri and P coincides with the set of
upward closed sets in P . Thus, hW R P i is a partially ordered modal
frame we shall denote it by F. Moreover, we clearly have F 
= F. If
M = hF Vi is an intuitionistic model then M = h F Vi is a modal model
having M as its skeleton. So by the Skeleton Lemma,
(M x) j= ' i (M x) j= T (')
for every intuitionistic formula ' and every point x in F.
It is worth noting that if F = hW Ri is a nite intuitionistic Kripke frame
then F is also a Kripke frame. However, for an innite F, F is not in
general a Kripke frame, witness h! i.
The operator  is not the only one which, given an intuitionistic frame F,
returns a modal frame whose skeleton is isomorphic to F. As an example, we
dene now an innite class of such operators. For Kripke frames F = hW Ri
and G = hV S i, denote by F ' G the direct product of F and G, i.e., the frame
hW ' V R ' S i in which the relation R ' S is dened component-wise:
hx1  y1 i (R ' S ) hx2  y2 i i x1 Rx2 and y1 Sy2 :
junctions. However this dierence is of no importance as far as embeddings into logics
in NExtS4 are concerned.

ADVANCED MODAL LOGIC

115

Let 0 < k  !. We will regard k to be the set f0 : : :  k ; 1g if k < ! and
f0 1 : : :g if k = !. Denote by  k an operator which, given an intuitionistic
frame F = hW R P i, returns a modal frame  k F = hkW kR kP i such that
(i) hkW kRi is the direct product of the k-point cluster k k2 and hW Ri
(in other words, hkW kRi is obtained from hW Ri by replacing its every
point with a k-point cluster)
(ii)  k F 
= F
(iii) I ' X 2 kP , for every I k and X 2 P .
For instance, we can take kP to be the Boolean closure of the set
fI ' X : I k X 2 P g:
For a Kripke frame F = hW R UpW i we can, of course, take kP = 2kW
and then  k F = kW kR 2kW .

 





3.2 Canonical formulas

The language of canonical formulas, axiomatizing all si-logics and characterizing the structure of their frames, can be easily developed following
the scheme of constructing the canonical formulas for K4 outlined in Section 1.6 and using the connection between modal and intuitionistic frames
established above. We conne ourselves here only to pointing out the differences from the modal case and some interesting peculiarities details can
be found in Zakharyaschev 1983, 1989] and Chagrov and Zakharyaschev
1997].
Actually, there are two important di erences. First, in the denition of
subreduction of F = hW R P i to G the condition (R3) does not correspond
to the fact that all sets in P are upward closed. We replace it by the
following condition
(R30 )
8X 2 Q f ;1(X )# 2 P ,
where Q = fV ; X : X 2 Qg and P = fW ; X : X 2 P g. For a
completely dened f satisfying (R1) and (R2) the condition (R30 ) is clearly
equivalent to (R3) and so every reduction is also a subreduction. If G is a
nite Kripke frame then (R3') is equivalent to 8z 2 V f ;1 (z )# 2 P . G is
a subframe of F if G is a subframe of F and the identity map on V is a
subreduction of F to G. It is of interest to note that in the intuitionistic case
(conal) subreductions are dual to IC(N)-subalgebras of Heyting algebras
which preserve only implication, conjunction (and negation or ?) but do
not necessarily preserve disjunction.
Second, we have to change the denition of open domains. Now we say
an antichain a (of at least two points) is an open domain in an intuitionistic
model N relative to a formula ' if there ia a pair ta = (;a  a ) such that
;a  a = Sub', ;a !
a 62 Int and

V

W

116

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

:p 1 :q

q

I
@
@

G

:p 2 :r

3

p  :p

r 6

@
@


;
;

;
;

@

;

p ! :q
:p ! :q _ :r @;:
:
0 p ! :r
Figure 14.
  2 ;a i a j=  for all a 2 a.

It is worth noting that in any intuitionistic model every antichain a is open
relative to every disjunction free formula '. Indeed, let ;a be dened by
condition above and a = Sub' ; ;a . It should be clear that  ^  2 ;a
i  2 ;a and  2 ;a . And if  !  2 ;a ,  2 ;a but  2 a then a j= 
for every a 2 a and b 6j=  for some b 2 a, whence b 6j=  ! , which is a
contradiction. It follows that ;a !
a 62 Int.
EXAMPLE 3.2 Let us try to characterize the class of intuitionistic refutation frames for the Weak Kreisel{Putnam Formula

V

W

wkp = (:p ! :q _ :r) ! (:p ! :q) _ (:p ! :r):
First we construct its simplest countermodel it is depicted in Fig. 14, where
by putting a formula to the left (right) of a point we mean that it is true
(not true) at the point. Then we observe that every frame F refuting wkp
is conally subreducible to the frame G underlying this countermodel by
the map f dened as follows:

8> 0
if x j= :p ! :q _ :r, x 6j= (:p ! :q) _ (:p ! :r)
>< 1
if x j= :p ! :q _ :r, x j= :p and x j= q
if x j= :p ! :q _ :r, x j= :p and x j= r
f (x) = > 2
if x j= p or x j= :p ^ :q ^ :r
>: 3
undened otherwise.

However, the conal subreducibility to G is only a necessary condition for
F 6j= wkp, witness the frame having the form of the three-dimensional
Boolean cube with the top point deleted. The reason for this is that the
antichain f1 2g is a closed domain in N: it is impossible to insert a point
a between 0 and f1 2g and extend to it consistently the truth-sets for the
depicted formulas. Indeed, otherwise we would have a j= :p ! :q _ :r,
a 6j= :q _ :r and so a 6j= :p, i.e., there must be a point x 2 a" such that

ADVANCED MODAL LOGIC

117

x j= p, but such a point does not exist. In fact, F 6j= wkp i there is a
conal subreduction of F to G satisfying (CDC) for ff1 2gg.
Now, as in the modal case, with every nite rooted intuitionistic frame
F = hW Ri and a set D of antichains in it we can associate two formulas
 (F D ?) and  (F D), called the canonical and negation free canonical
formulas, respectively, so that G 6j=  (F D ?) (G 6j=  (F D)) i there is a
(conal) subreduction of G to F satisfying (CDC) for D. For instance, if
a0  : : :  an are all points in F and a0 is its root, then one can take
^ ij ^ ^ d ^ ? ! p0
 (F D ?) =
ai Raj

where

ij = (

:

d =
?

d2D

^ pk ! pj ) ! pi
aj Rak
^ ( ^ pk ! pi) ! _ pj 

ai 2W ;d" :ai Rak
n
=
(
pk ! pi ) ! ?:
i=0 :ai Rak

^ ^

aj 2d

 (F D) is obtained from  (F D ?) by deleting the conjunct ? .
THEOREM 3.3 There is an algorithm which, given an intuitionistic ', returns canonical formulas  (F1  D1  ?) : : :   (Fn  Dn  ?) such that
Int + ' = Int + (F1  D1 ?) + : : : + (Fn  Dn ?):
So the set of intuitionistic canonical formulas is complete for ExtInt. If
' is negation free then one can use only negation free canonical formulas.
And if ' is disjunction free then all Di are empty.
Table 6 and Theorem 3.4 show canonical axiomatizations of the si-logics
in Table 5. Using this \geometrical" representation it is not hard to see, for
instance, that SmL, known as the Smetanich logic, is the greatest consistent
extension of Int di erent from Cl it is the logic of the two-point rooted
frame. KC, the logic of the Weak Law of the Excluded Middle, is characterized by the class of directed frames. It is the greatest si-logic containing the
same negation free formulas as Int (see Jankov 1968a]). LC, the Dummett
or chain logic, is characterized by the class of linear frames (see Dummett 1959]). BDn and BWn are the minimal logics of depth n and width
n, respectively (see Hosoi 1967] and Smorynski 1973]). Finite frames for
BTWn contain  n top points Smorynski 1973] and nite frames for Tn
are of branching  n, i.e., no point has more than n immediate successors.

118

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

For

= Int +  ()

= Int +  ( 6)

 
6
KA 
A

= Int +  (  ) +  ( 6)
 
K 
A

= Int +  ( A  ?)
 
K 
A

= Int +  ( A )

6
 
K 
A

= Int +  ] ( A  ?)

Cl
SmL
KC
LC
SL



A

K
1 A2 
I
@

;
@6
;

BDn

1 2 
I 6
@

;
= Int +  ( @;  ff1 2gg ?) +  (
n
..6
.
1
= Int +  ( 60 )

BWn

= Int +  ( @; )

KP



 ff1 2gg ?)

z n}|  {
+1

I ;
@


z n}|  {
+1

I

;
@;
 ?)
BTWn = Int + ( @

z n}|  {
+1

I ;
@


Tn

= Int +  ] ( @; )

Bn

= Int +  ] ( @;  ?)

z n}|  {
+1

I ;
@


Table 6. Canonical axioms of standard superintuitionistic logics

ADVANCED MODAL LOGIC

119

THEOREM 3.4 (Nishimura 1960, Anderson 1972) Every extension L of Int
by formulas in one variable can be represented either as
L = Int + nf 2n = Int +  ] (Hn  ?)
or as
L = Int + nf 2n;1 = Int +  ] (Hn+1  ?) +  ] (Hn+2  ?)
where Hn , Hn+1 , Hn+2 are the subframes of the frame in Fig. 13 generated
by the points n, n +1 and n +2, respectively, and  ] (F ?) is an abbreviation
for  (F D]  ?), D] the set of all antichains in F.
Jankov 1969] proved in fact that logics of the form Int +  ] (F ?) and
only them are splittings of ExtInt. However, not every si-logic is a unionsplitting of ExtInt which means that this class has no axiomatic basis.

3.3 Modal companions and preservation theorems
The fact that the Godel translation T embeds Int into S4 and the relationship between intuitionistic and modal frames established in Section 3.1 can
be used to reduce various problems concerning Int (e.g. proving completeness or FMP) to those for S4 and vice versa. Moreover, it turns out that
each logic in ExtInt is embedded by T into some logics in NExtS4, and for
each logic in NExtS4 there is one in ExtInt embeddable in it.
We say a modal logic M 2 NExtS4 is a modal companion of a si-logic L

if L is embedded in M by T , i.e., if for every intuitionistic formula ',
' 2 L i T (') 2 M:
If M is a modal companion of L then L is called the si-fragment of M
and denoted by M . The reason for denoting the operator \modal logic
7 its si-fragment" by the same symbol we used for the skeleton operator is
!
explained by the following
THEOREM 3.5 For every M 2 NExtS4, M = f' : T (') 2 M g. Moreover, if M is characterized by a class C of modal frames then M is characterized by the class C = fF : F 2 Cg of intuitionistic frames.
Proof It suces to show that f' : T (') 2 M g = LogC . Suppose that
T (') 2 M . Then F j= T (') and so, by the Skeleton Lemma, F j= ' for
every F 2 C , i.e., ' 2 LogC . Conversely, if F j= ' for all F 2 C then, by
the same lemma, T (') is valid in all frames in C and so T (') 2 M .
2
Thus,  maps NExtS4 into ExtInt. The following simple observation
shows that actually  is a surjection. Given a logic L 2 ExtInt, we put
 L = S4  fT (') : ' 2 Lg:

120

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

THEOREM 3.6 (Dummett and Lemmon 1959) For every si-logic L,  L is
a modal companion of L.

Proof Clearly, L  L. To prove the converse inclusion, suppose ' 62 L,
i.e., there is a frame F for L refuting '. Since F 
= F, by the Skeleton
Lemma we have F j=  L and F 6j= T ('). Therefore, T (') 62  L and so
' 62  L.
2
Now we use the language of canonical formulas to obtain a general characterization of all modal companions of a given si-logic L. Our presentation
follows Zakharyaschev 1989, 1991]. Notice rst that for every modal frame
G and every intuitionistic canonical formula  (F D ?), G j= (F D ?) i
G j= (F D ?) and so S4  T ((F D ?)) = S4  (F D ?). The same
concern, of course, the negation free canonical formulas.
THEOREM 3.7 A logic M 2 NExtS4 is a modal companion of a si-logic
L = Int + f (Fi  Di  ?) : i 2 I g i M can be represented in the form

M = S4  f(Fi  Di  ?) : i 2 I g  f(Fj  Dj  ?) : j 2 J g
where every frame Fj , for j 2 J , contains a proper cluster.

Proof (() We must show that for every intuitionistic formula ', ' 2 L

i T (') 2 M . Suppose that ' 62 L and F = hW R P i is a frame separating
' from L. We prove that F separates T (') from M . As was observed
above, F 6j= T (') and F j= (Fi  Di  ?) for any i 2 I . So it remains to
show that F j= (Fj  Dj  ?) for every j 2 J .
Suppose otherwise. Then, for some j 2 J , we have a subreduction f of
to the same proper
F to Fj . Let a1 and a2 be distinct points belonging
cluster in Fj . By the denition of subreduction, f ;1 (a1 ) f ;1(a2 )# and
f ;1 (a2 ) f ;1 (a1 )#, and so there is an innite chain x1 Ry1 Rx2 Ry2 R : : : in
F such that fx1 x2 : : :g f ;1(a1 ) and fy1 y2 : : :g f ;1(a2). And since
R is a partial order, all the points xi and yi are distinct.
Since f ;1 (a1 ) 2 P , there are Xi  Yi 2 P such that

f ;1(a1 ) = (;X1  Y1 ) \ : : : \ (;Xn  Yn ):
And since f ;1 (a1 ) \ f ;1 (a2 ) = , for every point yi there is some number ni
such that yi 2 Xni and yi 62 Yni . But then, for some distinct l and m, the
numbers nl and nm must coincide, and so if, say, yl Rym then xm 62 Ynm and
xm 2 Xnl (for yl Rxm Rym , Xi = Xi ", Yi = Yi "). Therefore, xm 62 f ;1 (a1 ),
which is a contradiction.
The rest of the proof presents no diculties.
2

ADVANCED MODAL LOGIC

121

This proof does not touch upon the conality condition. So along with
canonical formulas in Theorem 3.7 we can use negation free canonical formulas. Thus, we have:

S4 = S4:1 = Dum = Grz = Int
S4:2 = (S4:2  Grz) = KC
S4:3 = (S4:3  Grz) = LC
S5 = (S5  Grz) = Cl:
COROLLARY 3.8 The set of modal companions of every consistent si-logic
L forms the interval



;1 (L) =  L  L  ( )] = fM 2 NExtS4 :  L M  L  Grzg
and contains an innite descending chain of logics.

Proof Notice rst that (F D ?) and (F D) are in Grz i F contains
a proper cluster. So ;1 (L)  L,  L  ( )]. On the other hand, the
si-fragments of all logics inthe interval are the same, namely L. Therefore,
;1(L) =  L  L  ( )]. Now, if L is consistent then () 62 L and so
we have

 L  : : :   L  (Cn)  : : :   L  (C2 )   L  (C1 ) = For
where Ci is the non-degenerate cluster with i points.

2

This result is due to Maksimova and Rybakov 1974], Blok 1976] and
Esakia 1979b].
Thus, all modal companions of every si-logic L are contained
 between the
least companion  L and the greatest one, viz.,  L  ( ), which will be
denoted by L. Using Theorems 3.7 and 1.44, we obtain
COROLLARY 3.9 There is an algorithm which, given a modal formula ',
returns an intuitionistic formula  such that (S4  ') = Int + .
The following theorem, which is also a consequence of Theorem 3.7, describes lattice-theoretic properties of the maps ,  and . Items (i), (ii)
and (iv) in it were rst proved by Maksimova and Rybakov 1974], and (iii)
is due to Blok 1976] and Esakia 1979b] and known as the Blok{Esakia
Theorem.

122

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

THEOREM 3.10 (i) The map  is a homomorphism of the lattice NExtS4
onto the lattice ExtInt.
(ii) The map  is an isomorphism of ExtInt into NExtS4.
(iii) The map  is an isomorphism of ExtInt onto NExtGrz.
(iv) All these maps preserve innite sums and intersections of logics.
Now we give frame-theoretic characterizations of the operators  and .
Note rst that the following evident relations between frames for si-logics
and their modal companions hold:

F j= M i F j= M F j= L i F j= L
F j= L i F j=  L F j= L i  k F j=  L:
THEOREM 3.11 (Maksimova and Rybakov 1974) A si-logic L is characterized by a class C of intuitionistic frames i L is characterized by the
class C = fF : F 2 Cg.
Proof ()) It suces to show that any canonical formula (F D ?) 62 L
is refuted by some frame in C . Since F is partially ordered,  (F D ?) 62 L,
i.e., there is F 2 C refuting  (F D ?) and so F 6j= (F D ?). (() is
straightforward.
2
To characterize  we require
LEMMA 3.12 For any canonical formula (F D ?) built on a quasi-ordered
frame F, (F D ?) 2 S4  (F D ?), where D = fd : d 2 Dg and
d = fC (x) : x 2 dg.
Proof Let G be a quasi-ordered frame refuting (F D ?). Then there is
a conal subreduction f of G to F satisfying (CDC) for D. The map h from
F onto F dened by h(x) = C (x), for every x in F, is clearly a reduction
of F to F. So the composition hf is a conal subreduction of G to F, and
it is easy to verify that it satises (CDC) for D.
2
THEOREM 3.13 A si-logic LSis characterized by a class C of frames i  L
is characterized by the class 0<k<!  k C , where  k C = f k F : F 2 Cg.
Proof ()) As was noted above, if F is a frame for L then  k F is a frame for
 L. So suppose that a formula (F D ?), built on a quasi-ordered frame
F =ShW Ri, does not belong to  L and show that it is refuted by some frame
in 0<k<!  k C . By Lemma 3.12, (F D ?) 62  L and so  (F D ?) 62
L. Hence there is a frame G = hV S Qi in C which refutes  (F D ?).
But then G j=  L and G 6j= (F D ?). Let f be a subreduction
of G to F satisfying (CDC) for D and let k = maxfjC (x)j : x 2 W g.

ADVANCED MODAL LOGIC

123

Dene a partial map h from  k G = hkV kS kQi onto F as follows: if x 2 V ,
y0 2 W , f (x) = C (y0 ) and C (y0 ) = fy0  : : :  yn g then we put h(hi xi) = yi ,
for i = 0 : : :  n. By the denition of  k , for any i 2 f0 : : :  ng we have
h;1 (yi ) = fhi xi : x 2 f ;1 (C (y0 ))g = fig ' f ;1(C (y0 )) 2 kQ:
Now, one can readily prove that h is a conal subreduction of  k G to F
satisfying (CDC) for D. So  k G 6j= (F D ?). (() is obvious.
2
It is worth noting that this proof will not change if we put in it k = !.
COROLLARY 3.14 A logic L 2 ExtInt is characterized by a class C of
frames i  L is characterized by the class  ! C .
The following theorem provides a deductive characterization of the maps
 and .
THEOREM 3.15 For every si-logic L and every modal canonical formula
(F D ?) built on a quasi-ordered frame F,
(i) (F D ?) 2  L i  (F D ?) 2 L
(ii) (F D ?) 2 L i either F is partially ordered and  (F D ?) 2 L
or F contains a proper cluster.
Proof (i) The implication ()) was actually established in the proof of
Theorem 3.13, and the converse one follows from Lemma 3.12.
(ii) Suppose (F D ?) 2 L. Then either F is partially ordered, and so
 (F D ?) 2 L, or F contains a proper cluster. The converse implication
follows from (i) and the fact that (F D ?) 2 Grz for every frame F with
a proper cluster.
2
The results obtained in this section not only establish some structural
correspondences between logics in ExtInt and NExtS4 and their frames,
but may be also used for transferring various properties of modal logics
to their si-fragments and back. A few results of that sort are collected in
Table 7 we shall cite them as the Preservation Theorem. The preservation
of decidability follows from the denition of  and Theorem 3.15. That
 preserves Kripke completeness, FMP and tabularity is a consequence of
Theorem 3.5. The map  preserves Kripke completeness and FMP, since
we can dene  k in Theorem 3.13 so that  k hW Ri = hkW kRi however,
 does not in general preserve the tabularity, because  Cl = S5 is not
tabular. The preservation of FMP and tabularity under  follows from
Theorem 3.11. On the other hand, Shehtman 1980] proved that  does not
preserve Kripke completeness (since  preserves it and Grz is complete,
this means in particular that Kripke completeness is not preserved under
sums of logics in NExtS4). Some other preservation results in Table 7 will
be discussed later. For references see Chagrov and Zakharyaschev 1992,
1997].

124

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

Property of logics

Preserved under

Decidability
Kripke completeness
Strong completeness
Finite model property
Tabularity
Pretabularity
D-persistence
Local tabularity
Disjunction property
Hallden completeness
Interpolation property
Elementarity
Independent axiomatizability

Yes
Yes
Yes
Yes
Yes
Yes
Yes
Yes
Yes
Yes
Yes
Yes
No





Yes
Yes
Yes
Yes
No
No
Yes
No
Yes
No
No
Yes
Yes



Yes
No
No
Yes
Yes
Yes
No
No
Yes
No
No
No
Yes

Table 7. Preservation Theorem

3.4 Completeness
In this section we briey discuss the most important results concerning
completeness of si-logics with respect to various classes of Kripke frames.

Kripke completeness That not all si-logics are complete with respect

to Kripke frames was discovered by Shehtman 1977], who found a way
to adjust Fine's 1974b] idea to the intuitionistic case (which was not so
easy because intuitionistic formulas do not \feel" innite ascending chains
essential in Fine's construction see Section 20 of Basic Modal Logic). Note
however that Kuznetsov's 1975] question whether all si-logics are complete
with respect to the topological semantics (see Intuitionistic Logic) is still
open.
As to general positive results, notice rst that the Preservation Theorem
yields the following translation of Fine's 1974c] Theorem on nite width
logics (si-logics of nite width were studied by Sobolev 1977a]).
THEOREM 3.16 Every si-logic of width n (i.e., a logic in ExtBWn  see
Table 5) is characterized by a class of Noetherian Kripke frames of width
 n.
The translation of Sahlqvist's Theorem gives nothing interesting for silogics. A sort of intuitionistic analog of this theorem has been recently

ADVANCED MODAL LOGIC

125

proved by Ghilardi and Meloni 1997]. Here is a somewhat simplied variant
of their result in which p, q, r, s denote tuples of propositional variables
and ,  tuples of formulas of the same length as r and s, respectively.
THEOREM 3.17 (Ghilardi and Meloni 1997) Suppose '(p q r s) is an intuitionistic formula in which the variables r occur positively and the variables s occur negatively, and which does not contain any !, except for
negations and double negations of atoms, in the premise of a subformula of
the form '0 ! '00 . Assume also that (p q) and (p q) are formulas such
that p occur positively in  and negatively in , while q occur negatively in
 and positively in . Then the logic

Int + '(p q (p q) (p q))
is canonical.

The preservation of D-persistence under  (see Zakharyaschev 1996])
and the fact (discovered by Chagrova 1990]) that  L is characterized by an
elementary class of Kripke frames whenever L is determined by such a class
provide us with an intuitionistic variant of the Fine{van Benthem Theorem.
THEOREM 3.18 If a si-logic is characterized by an elementary class of
Kripke frames then it is D-persistent.
As in the modal case, it is unknown whether the converse of this theorem holds. All known non-elementary si-logics, for instance the Scott logic
SL and the logics Tn of nite n-ary trees (see Rodenburg 1986]) are not
canonical and even strongly complete either, as was shown by Shimura
1995]. (Actually he proved that no logic in the intervals SL SL + bd3 ] and
Int T2 ], save of course Int, is strongly complete.)
As far as we know, there are no examples of si-logics separating canonicity,
D-persistence and strong completeness. (Ghilardi, Meloni and Miglioli have
recently showed that SL in any language with nitely many variables is
canonical). Theorem 1.40 which holds in the intuitionistic case as well gives
an algebraic counterpart of strong Kripke completeness.

The nite model property The rst example of an innitely axiomatizable si-logic without FMP was constructed by Jankov 1968b]|that was in
fact the starting point of a long series of \negative" results in modal logic.
A nitely axiomatizable logic without FMP appeared two years later in
Kuznetsov and Gerchiu 1970]. The reader can get some impression about

126

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

this and other examples of that sort by proving (it is really not hard) that


12 6
12 6


IBM ;
@

I
@

BMB;
;
@
' =  (  ) 2= L = Int + bw4 +  ( @B;  ff1 2gg)

but no nite frame can separate ' from L. (Notice by the way that  L
is axiomatizable by Sahlqvist formulas see Chagrov and Zakharyaschev
1995b].)
FMP of a good many si-logics was proved using various forms of ltration
see e.g. Gabbay 1970], Ono 1972], Smorynski 1973], Ferrari and Miglioli
1993]. As an illustration of a rather sophisticated selective ltration we
present here the following
THEOREM 3.19 (Gabbay and de Jongh 1974) The logic Tn (see Table 5)
is characterized by the class of nite n-ary trees.

Proof First we prove that Tn is characterized by the class of nite frames
of branching  n. Suppose ' 62 Tn and M = hF Vi is a model for Tn
refuting '. Without loss of generality we may assume that F = hW Ri is a
tree. Let # = Sub' and ;x = f 2 # : x j= g, for every point x in F.

Given x in F, put rg(x) = fy] : y 2 x"g and say that x is of minimal range
if rg(x) = rg(y) for every y 2 x] \ x". Since there are only nitely many
distinct #-equivalence classes in M, every y 2 x] sees a point z 2 x] of
minimal range. Now we extract from M a nite refutation frame G = hV S i
for ' of branching  n. To begin with, we select some point x of minimal
range at which ' is refuted and put V0 = fxg.
Suppose Vk has already been dened. If jrg(x)j = 1 for every x 2 Vk , then
we put G = hV S i, where V = ki=0 Vk and S is the restriction of R to V .
Otherwise, for each x 2 Vk with jrg(x)j > 1 and each y] 2 rg(x) di erent
from x] and such that ;z  ;y for no z ] 2 rg(x) ; fx]g, we select a point
u 2 y] \ x" of minimal range. Let Ux be the set of all selected points for x
and Vk+1 = x Ux. It should be clear that ;x  ;u (and rg(x) ( rg(u)), for
every u 2 Ux , and so the inductive process must terminate. Consequently
G 6j= '.
It remains to establish that G j= Tn , i.e., G is of branching  n. Suppose
otherwise. Then there is a point x in G with m n +1 immediate successors
x0  : : :  xm , which are evidently in Ux because F is a tree. We are going to
construct a substitution instance of Tn 's axiom bbn which is refuted at x
in M.
Denote by i the conjunction of the formulas in ;xi . Since all of them
are true at xi in M, we have xi j= i  and since ;i ;j for no distinct i and

S

S

ADVANCED MODAL LOGIC

127

j , we have xj 6j= i if i 6= j . Put i = i , for 0  i < n, n = n _ : : : _ m
and consider the truth-value of the formula  = bbn f0 =p0 : : :  n =pn g at
x in M.
W
Since
xRx
for every
i
= 0 : :W
:

m
, we have x 6j= ni=0 i . Suppose
i
W that
V
W
x 6j= W ni=0 ((i ! i=6 j j ) ! i6=j j ). Then y j= i ! i6=j j and
y 6j= i6=j j , for some yW2 x" and some i 2 f0 : : : ng, and hence y 6j= i .
Since xi j= i and xi 6j= i6=j j , y sees no point in xi ] and so y 6 x (for
otherwise x would not be of minimal range). Therefore, ;xj ;y for some
j 2 f0 : : : mg, and then y j= j if j < n and y j= n if j n, which is a

V

W

W

contradiction.
It follows that x j= ni=0 ((i ! i6=j j ) ! i6=j j ), from which x 6j= ,
contrary to M being a model for bbn . It remains to notice that every nite
frame of branching  n is a reduct of a nite n-ary tree, which clearly
validates Tn .
2
Another way of obtaining general results on FMP of si-logics is to translate the corresponding results in modal logic with the help of the Preservation Theorem.
THEOREM 3.20 Every si-logic of nite depth (i.e., every logic in ExtBDn ,
for n < !) is locally tabular.
Note, however, that unlike NExtK4, the converse does not hold: the
Dummett logic LC, characterized by the class of nite chains (or by the
innite ascending chain), is locally tabular. As we saw in Section 1.7, every
non-locally tabular in NExtS4 logic is contained in Grz.3, the only prelocally tabular logic in NExtS4. But in ExtInt this way of determining
local tabularity does not work:
THEOREM 3.21 (Mardaev 1984) There is a continuum of pre-locally tabular logics in ExtInt.
Besides, it is not clear whether every locally tabular logic in ExtInt (or
NExtK4) is contained in a pre-locally tabular one.
An intuitionistic formula is said to be essentially negative if every occurrence of a variable in it is in the scope of some :. If ' is essentially negative
then T (') is a 23-formula, which yields
THEOREM 3.22 (McKay 1971, Rybakov 1978) If a si-logic L is decidable
(or has FMP) and ' is an essentially negative formula then L+' is decidable
(has FMP).
Originally this result was proved with the help of Glivenko's Theorem
(see Section 7 in Intuitionistic Logic). Say that an occurrence of a variable

128

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

in a formula is essential if it is not in the scope of any :. A formula
' is mild if every two essential occurrences of the same variable in ' are
either both positive or both negative. Kuznetsov 1972] claimed (we have
not seen the proof) that all si-logics whose extra axioms do not contain
negative occurrences of essential variables have FMP. And Wronski 1989]
announced that if L is a decidable si-logic and ' a mild formula then L + '
is also decidable.
Subframe and conal subframe si-logics|that is logics axiomatizable by
canonical formulas of the form  (F) and  (F ?), respectively|can be characterized both syntactically and semantically (see Zakharyaschev 1996]).
THEOREM 3.23 The following conditions are equivalent for every si-logic
L:
(i) L is a (conal) subframe logic
(ii) L is axiomatizable by implicative (respectively, disjunction free) formulas
(iii) L is characterized by a class of nite frames closed under the formation of (conal) subframes.
That all si-logics with disjunction free axioms have FMP was rst proved
by McKay 1968] with the help of Diego's 1966] Theorem according to which
there are only nitely many pairwise non-equivalent in Int disjunction free
formulas in variables p1  : : :  pn (see also Urquhart 1974]).
Since frames for Int contain no clusters, Theorem 1.58 and its analog
for conal subframe logics reduce in the intuitionistic case to the following
result which is due to Chagrova 1986], Rodenburg 1986], Shimura 1993]
and Zakharyaschev 1996].
THEOREM 3.24 All si-logics with disjunction free axioms are elementary
(denable by 89-sentences) and D-persistent.
Theorem 1.68 is translated into the intuitionistic case simply by replacing

K4 with Int,  with + and  with . As a consequence we obtain, for
instance, that Ono's 1972] Bn and all other logics whose canonical axioms
are built on trees have FMP. Moreover, we also have

THEOREM 3.25 (Sobolev 1977b, Nishimura 1960) All si-logics with extra
axioms in one variable have FMP and are decidable.
In fact Sobolev 1977b] proved a more general (but rather complicated)
syntactical sucient condition of FMP and constructed a formula in two
variables axiomatizing a si-logic without FMP (Shehtman's 1977] incomplete si-logic has also axioms in two variables).

ADVANCED MODAL LOGIC

129

Tabularity By the Blok{Esakia and Preservation Theorems, the situation
with tabular logics in ExtInt is the same as in NExtGrz. In particular,
L 2 ExtInt is tabular i BDn + BWn L for some n < ! i L is not a
sublogic of one of the three pretabular logics in ExtInt, namely LC, BD2
and KC + bd3 . (The pretabular si-logics were described by Maksimova
1972].) The tabularity problem is decidable in ExtInt.
3.5 Disjunction property

One of the aims of studying extensions of Int, which may be of interest
for applications in computer science, is to describe the class of constructive
si-logics. At the propositional level a logic L 2 ExtInt is regarded to be
constructive if it has the disjunction property (DP, for short) which means
that for all formulas ' and ,
' _  2 L implies ' 2 L or  2 L.
That intuitionistic logic itself is constructive in this sense was proved in a
syntactic way by Gentzen 1934{1935]. However, L( ukasiewicz (1952) conjectured that no proper consistent extension of Int has DP.
A similar property was introduced for modal logics (see e.g. Lemmon
and Scott 1977]): L 2 NExtK has the (modal) disjunction property if, for
every n 1 and all formulas '1  : : :  'n ,
2'1 _ : : : _ 2'n 2 L implies 'i 2 L, for some i 2 f1 : : :  ng:
The following theorem (in a somewhat di erent form it was proved in
Hughes and Cresswell 1984] and Maksimova 1986]) provides a semantic
criterion of DP.
THEOREM 3.26 Suppose a modal or si-logic L is characterized by a class C
of descriptive rooted frames closed under the formation of rooted generated
subframes. Then L has DP i, for every n 1 and all F1  : : :  Fn 2 C with
roots x1  : : :  xn , there is a frame F for L with root x such that the disjoint
union F1 + : : : + Fn is a generated subframe of F with fx1  : : :  xn g x".
Proof We consider only the modal case. ()) Let FL = hWL RL PLi be
a universal frame for L, big enough to contain F1 + : : : + Fn as its generated
subframe. Assuming that FL is associated with a suitable canonical model
for L, we show that there is a point x in FL such that x" = WL . The set
0 = f:2' : 9y 2 W y 6j= 'g
L
is L-consistent (for otherwise 2'1 _ : : : _ 2'n 2 L for some '1  : : :  'n 62 L).
Let be a maximal L-consistent extension of 0 and x the point in FL
where is true. Then xRL y, for every y 2 WL .

130

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

(() Suppose otherwise. Then there are formulas '1  : : :  'n 62 L such
that 2'1 _ : : : _ 2'n 2 L. Take frames F1  : : :  Fn 2 C refuting '1  : : :  'n
at their roots, respectively, and let F be a rooted frame for L containing
F1 + : : : + Fn as a generated subframe and such that its root x sees the roots
of F1  : : :  Fn . Then all the formulas 2'1  : : :  2'n are refuted at x and so
2'1 _ : : : _ 2'n 62 L, which is a contradiction.
2
It should be clear that if we use only the sucient condition of Theorem 3.26, the requirement that frames in C are descriptive is redundant.
Furthermore, it is easy to see that for L 2 NExtK4 we may assume n  2.
And clearly a logic L 2 NExtS4 has DP i , for all ' and , 2' _ 2 2 L
implies 2' 2 L or 2 2 L.
As a direct consequence of the proof above we obtain
COROLLARY 3.27 A modal or si-logic L has DP i the canonical frame
FL = hWL  RLi contains a point x such that x" = WL .
Using the semantic criterion above it is not hard to show that DP is
preserved under ,  and . It is also a good tool for proving and disproving
DP of logics with transparent semantics.
EXAMPLE 3.28 (i) Let F1  : : :  Fn be serial rooted Kripke frames. Then
the frame obtained by adding a root to F1 + : : : + Fn is also serial. Therefore,
D has DP. In the same way one can show that K, K4, T, S4, Grz, GL
and many other modal logics have DP.
(ii) Since no rooted symmetrical frame can contain a proper generated
subframe, no consistent logic in NExtKB has DP.
The rst proper extensions of Int with DP were constructed by Kreisel
and Putnam 1957]: these were KP (now called the Kreisel{Putnam logic
and SL (known as the Scott logic). We present here Gabbay's 1970] proof
that KP has DP.
THEOREM 3.29 (Kreisel and Putnam 1957) KP has DP.

Proof Using ltration one can show that KP is characterized by the class
of nite rooted frames F = hW Ri satisfying the condition

8x y z (xRy ^ xRz ^ :yRz ^ :zRy ! 9u (xRu ^ uRy ^ uRz ^
8v (uRv ! 9w (vRw ^ (yRw _ zRw))))):
(15)

If F is such a frame then for each non-empty X W 1 , the generated
subframe of F based on the set W ; (W 1 ; X )# is rooted we denote its
root by r(X ).

ADVANCED MODAL LOGIC

131

Let F1 = hW1  R1 i and F2 = hW2  R2 i be nite rooted frames satisfying
(15). We construct from them a frame F = hW Ri by taking

W = W1  W2  U
where U = fX1  X2 : X1 W11  X2 W21  X1  X2 6= g, and
xRy i (x y 2 Wi ^ xRi y) _ (x y 2 U ^ x  y) _
(x = X1  X2 2 U ^ y 2 Wi ^ r(Xi )Ri y):
It follows from the given denition that F1 + F2 is a generated subframe of
F, W1  W2 is a cover for F and W11  W21 is its root. So our theorem

will be proved if we show that (15) holds.
Suppose x y z 2 W satisfy the premise of (15). Since (15) holds for F1
and F2 , we can assume that x = X1  X2 2 U . Let Y1  Y2 and Z1  Z2 be
the sets of nal points in y" and z", respectively, with Yi  Zi Wi . By the
denition of R, we have Yi  Zi Xi . Consider u = (Y1  Z1 )  (Y2  Z2 ).
Clearly, xRu, uRy and uRz . Suppose now that v 2 u". Let w be any nal
point in v ". Then v 2 (Y1  Z1 )  (Y2  Z2 ) and so either yRw or zRw.

2

Other examples of constructive si-logics were constructed by Ono 1972]
and Gabbay and de Jongh 1974], namely, Bn and Tn . Anderson 1972]
proved that among the consistent si-logics with extra axioms in one variable
only those of the form Int + nf 2n+2 , for n 5, have DP (for n = 6 the
proof was found by Wronski 1974] see also Sasaki 1992]). Finally, Wronski
1973] showed that there is a continuum of si-logics with DP.
The additional axioms of logics in all these examples contained occurrences of _ on the other hand, known examples of si-logics with disjunction
free extra axioms, say LC, KC, Cl, BWn or BDn , were not constructive.
This observation led Hosoi and Ono 1973] to the conjecture that the disjunction free fragment of every consistent si-logic with DP coincides with
that of Int. We present a proof of this conjecture following Zakharyaschev
1987].
First we describe the conal subframe logics in NExtS4 with DP, assuming that every such logic L is represented by its independent canonical
axiomatization
L = S4  f(Fi  ?) : i 2 I g:
(16)
All frames in the rest of this section are assumed to be quasi-ordered.
Say that a nite rooted frame F with 2 points is simple if its root cluster
and at least one of the nal clusters are simple. Suppose F = hW Ri is a
simple frame, a0  a1  : : :  am am+1  : : :  an are all its points, with a0 being
the root, C (a1 ) : : :  C (am ) all the distinct immediate cluster-successors of

132

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

a0 , and an a nal point with simple C (an ). For every k = 1 : : :  n, dene a
formula k by taking
k =

^ 'ij ^ ^n 'i ^ ' ! pk

ai Raj i6=0

i=1

0
?

V

where 'ij , 'i were dened in Section 3.2 and '0? = 2( ni=1 2pi ! ?).
Now we associate with F the formula  (F) = 2p0 _ 21 if m = 1, and the
formula  (F) = 21 _ : : : _ 2m if m > 1.
LEMMA 3.30 For every simple frame F,  (F) 2 S4  (F ?).

Proof It is enough to show that G 6j=  (F) implies G 6j= (F ?), for any

nite G. So suppose  (F) is refuted in a nite frame G under some valuation.
Dene a partial map f from G onto F by taking
a0
if x 6j=  (F)
if x 6j= i , 1  i  n
f (x) = ai
undened otherwise.
One can readily check that f is a subreduction of G to F. However it is not
necessarily conal. So we extend f by putting f (x) = an , for every x of
depth 1 in G such that f (x#) = fa0g. Clearly, the improved map is still a
subreduction of G to F, and '0? ensures its conality.
2

8<
:

Using the semantical properties of the canonical formulas it is a matter
of routine to prove the following
LEMMA 3.31 Suppose i 2 f1 : : :  mg and G is the subframe of F generated
by ai . Then (G ?) 2 S4  i .
We are in a position now to prove a criterion of DP for the conal subframe logics in NExtS4.
THEOREM 3.32 A consistent conal subframe logic L 2 NExtS4 has the
disjunction property i no frame Fi in its independent axiomatization (16)
is simple, for i 2 I .

Proof ()) Suppose, on the contrary, that Fi is simple, for some i 2 I .

Since the axiomatization (16) is independent, every proper generated subframe of Fi validates L. By Lemma 3.30,  (Fi ) 2 L and so either p0 2 L or
j 2 L. However, both alternatives are impossible: the former means that
L is inconsistent, while the latter, by Lemma 3.31, implies (G ?) 2 L,
where G is the subframe of Fi generated by an immediate successor of Fi 's
root.

ADVANCED MODAL LOGIC

133

A

G  AA G2 
A 1
A 
A 
A
 y A
I
@

6 ;
@
;
@;

x

Figure 15.
(() Given two nite rooted frames G1 and G2 for L, we construct the
frame F as shown in Fig. 15 and prove that F j= L. Suppose otherwise, i.e.,
there exists a conal subreduction f of F to Fi , for some i 2 I . Let xi be the
root of Fi . Since G1 and G2 are not conally subreducible to Fi and since
L is consistent, f ;1 (xi ) = fxg. By the conality condition, it follows in
particular that y 2 domf . But then Fi is simple, which is a contradiction.
2
Thus, by Theorem 3.26, L has DP.
Note that in fact the proof of ()) shows that if L 2 NExtS4, F is
a simple frame, (F ?) 2 L and (G ?) 62 L for any proper generated
subframe G of F then L does not have DP. Transferring this observation to
the intuitionistic case, we obtain
THEOREM 3.33 (Minari 1986, Zakharyaschev 1987) If a si-logic is consistent and has DP then the disjunction free fragments of L and Int are the
same.
Sucient conditions of DP in terms of canonical formulas can be found
in Chagrov and Zakharyaschev 1993, 1997].
Since classical logic is not constructive, it is of interest to nd maximal
consistent si-logics with DP. That they exist follows from Zorn's Lemma.
Here is a concrete example of such a logic.
Trying to formalize the proof interpretation of intuitionistic logic, Medvedev (1962) proposed to treat intuitionistic formulas as nite problems.
Formally, a nite problem is a pair hX Y i of nite sets such that Y X
and X 6=  elements in X are called possible solutions and elements in Y
solutions to the problem. The operations on nite problems, corresponding
to the logical connectives, are dened as follows:
hX1  Y1 i ^ hX2  Y2 i = hX1 ' X2  Y1 ' Y2 i 
hX1  Y1 i _ hX2  Y2 i = hX1 t X2  Y1 t Y2 i 

134

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV






I
@
@



@;


;
;





I
@
@
;
I
6
;
6
@;
@;
; @; @

;
I
@
@ 6;
@;


1

1

1



6
@
6
;
I
@

;
I
6
;
I
@
;


@

;
@
;
@
 


;



;
@
;
@
@

 
1

1

1




I
@

;
I
@

;
I
@

;
6
6 @

 6;
@; @
;






;
@
;
@
@;

 
1


 
;
I
@
@ 6;


@;

Figure 16.

D

hX1  Y1 i ! hX2  Y2 i = X2X1  ff 2 X2X1 : f (Y1 )

E

Y2 g 

? = hX i :
Here X t Y = (X ' f1g)  (Y ' f2g) and X Y is the set of all functions from
X into Y . Note that in the denition of ? the set X is xed, but arbitrary
for deniteness one can take X = fg.
Now we can interpret formulas by nite problems. Namely, given a formula ', we replace its variables by arbitrary nite problems and perform
the operations corresponding to the connectives in '. If the result is a
problem with a non-empty set of solutions no matter what nite problems
are substituted for the variables in ', then ' is called nitely valid. One
can show that the set of all nitely valid formulas is a si-logic it is called
Medvedev's logic and denoted by ML.
In fact, ML can be dened semantically. Medvedev (1966) showed that
ML coincides with the set of formulas that are valid in all frames Bn having
the form of the n-ary Boolean cubes with the topmost point deleted for
n = 1 2 3 4, the Medvedev frames are shown in Fig. 16. Since Bn + Bm is
a generated subframe of Bn+m , ML has DP. Moreover, Levin 1969] proved
that it has no proper consistent extension with DP. The following proof of
this result is due to Maksimova 1986].

THEOREM 3.34 (Levin 1969) ML is a maximal si-logic with DP.

Proof Suppose, on the contrary, that there exists a proper consistent extension L of ML having DP. Then we have a formula ' 2 L ; ML. We
show rst that there is an essentially negative substitution instance ' of
' such that ' 62 ML. Since '(p1  : : :  pn ) 62 ML, there is a Medvedev

frame Bm refuting ' under some valuation V. With every point x in Bm
we associate a new variable qx and extend V to these variables by taking
V(qx ) to be the set of nal points in Bm that are not accessible from x. By

ADVANCED MODAL LOGIC

135

the construction of Bm , we have y j= :qx i y 2 x", from which

V(

_ :qx) = V(pi):

x2V(pi )

W
W
Let ' = '( x V p :qx  : : :  x V p :qx ). It follows that V(' ) = V(')
2 ( 1)

2 ( n)

and so ' 62 ML.
Thus, we may assume that ' is an essentially negative formula. Since
KP ML, ML contains the formulas

ndk = (:p ! :q1 _ : : : _ :qk ) ! (:p ! :q1) _ : : : _ (:p ! :qk )

which, as is easy to see, belong to KP. Let us consider the logic

ND = Int + fndk : k 1g:

Using the fact that the outermost ! in ndk can be replaced with $ and that
(:p ! :q) $ :(:p ^ q) 2 Int, one can readily show that every essentially
negative formula is equivalent in ND to the conjunction of formulas of the
form :1 _: : :_:l . So L;ML contains a formula of the form :1 _: : :_:l .
Since L has DP, :i 2 L for some i. But then, by Glivenko's Theorem,
:i 2 ML, which is a contradiction.
2

Remark. ML is not nitely axiomatizable, as was shown by Maksimova

et al. 1979]. Nobody knows whether it is decidable.
It turns out, however, that ML is not the unique maximal logic with DP
in ExtInt. Kirk 1982] noted that there is no greatest consistent si-logic
with DP. Maksimova 1984] showed that there are innitely many maximal
constructive si-logics, and Chagrov 1992a] proved that in fact there are
a continuum of them see also Ferrari and Miglioli 1993, 1995a, 1995b].
Galanter 1990] claims that each si-logic characterized by the class of frames
of the form
hfW : W

f1 : : :  ng W 6=  jW j 62 N g i 

where n = 1 2 : : : and N is some xed innite set of natural numbers, is a
maximal si-logic with DP.

3.6 Intuitionistic Modal Logics

All modal logics we have dealt with so far were constructed on the classical
non-modal basis. It can be replaced by logics of other types. For instance,
one can consider modal logics based on relevant logic (see e.g. Fuhrmann
1989]) or many-valued logics (see e.g. Segerberg 1967], Morikawa 1989],

136

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

Ostermann 1988]), and many others. In this section we briey discuss
modal logics with the intuitionistic basis.
Unlike the classical case, the intuitionistic 2 and 3 are not supposed to
be dual, which provides more possibilities for dening intuitionistic modal
logics. For a non-empty set M of modal operators, let LM be the standard propositional language augmented by the connectives in M. By an
intuitionistic modal logic in the language LM we understand any subset of
LM containing Int and closed under modus ponens, substitution and the
regularity rule ' ! = # ' ! #, for every # 2 M.
There are three ways of dening intuitionistic analogues of (classical)
normal modal logics. First, one can take the family of logics extending the
basic system IntK2 in the language L2 which is axiomatized by adding to
Int the standard axioms of K

2(p ^ q) $ 2p ^ 2q and 2>:
An example of a logic in this family is Kuznetsov's 1985] intuitionistic
provability logic I4 (Kuznetsov used 4 instead of 2), the intuitionistic
analog of the provability logic GL. It can be obtained by adding to IntK2
(and even to Int) the axioms

p ! 2p (2p ! p) ! p ((p ! q) ! p) ! (2q ! p):
A model theory for logics in NExtIntK2 was developed by Ono 1977],
Bo)zic and Do)sen 1984], Do)sen 1985a], Sotirov 1984] and Wolter and Zakharyaschev 1997a,b] we discuss it below. Font 1984, 1986] considered
these logics from the algebraic point of view, and Luppi 1996] investigated
their interpolation property by proving, in particular, that the superamalgamability of the corresponding varieties of algebras is equivalent to interpolation.
A possibility operator 3 in logics of this sort can be dened in the classical
way by taking 3' = :2:'. Note, however, that in general this 3 does not
distribute over disjunction and that the connection via negation between 2
and 3 is too strong from the intuitionistic standpoint (actually, the situation
here is similar to that in intuitionistic predicate logic where 9 and 8 are not
dual.)
Another family of \normal" intuitionistic modal logics can be dened in
the language L3 by taking as the basic system the smallest logic in L3 to
contain the axioms

3(p _ q) $ 3p _ 3q and :3?
it will be denoted by IntK3 . Logics in NExtIntK3 were studied by Bo)zic
and Do)sen 1984], Do)sen 1985a], Sotirov 1984] and Wolter 1997c].

ADVANCED MODAL LOGIC

137

Finally, we can dene intuitionistic modal logics with independent 2 and
3. These are extensions of IntK23 , the smallest logic in the language L23

containing both IntK2 and IntK3 . Fischer Servi 1980, 1984] constructed a
logic in NExtIntK23 by imposing a weak connection between the necessity
and possibility operators:

FS = IntK23  3(p ! q) ! (2p ! 3q)  (3p ! 2q) ! 2(p ! q):
A remarkable feature of FS is that the standard translation ST of modal
formulas into rst order ones (see Correspondence Theory) not only embeds
K into classical predicate logic but also FS into intuitionistic rst order

logic: ' belongs to the former i ST (') is a theorem of the latter. According
to Simpson 1994], this result was proved by C. Stirling see also Grefe 1997].
Various extensions of FS were studied by Bull 1966a], Ono 1977], Fischer
Servi 1977, 1980, 1984], Amati and Pirri 1994], Ewald 1986], Wolter and
Zakharyaschev 1997b], Wolter 1997c]. The best known one is probably the
logic

MIPC = FS  2p ! p  2p ! 22p  3p ! 23p 
p ! 3p  33p ! 3p  32p ! 2p

introduced by Prior 1957]. Bull 1966a] noticed that the translation dened by
(pi ) = Pi (x), ? = ?,
( $ ) =  $  , for $ 2 f^ _ !g,
(2) = 8x  , (3) = 9x 
is an embedding of MIPC into the monadic fragment of intuitionistic predicate logic. Ono 1977], Ono and Suzuki 1988], Suzuki 1990], and Bezhanishvili 1997] investigated the relations between logics in NExtMIPC and
superintuitionistic predicate logics induced by that translation.
In what follows we restrict attention only to the classes of intuitionistic
modal logics introduced above. An interesting example of a system not
covered here was constructed by Wijesekera 1990]. A general model theory
for such logics is developed by Sotirov 1984] and Wolter and Zakharyaschev
1997b].
Let us consider rst the algebraic and relational semantics for the logics
introduced above. All the semantical concepts to be dened below turn
out to be natural combinations of the corresponding notions developed for
classical modal and si-logics. For details and proofs we refer the reader to
Wolter and Zakharyaschev 1997a,b].
From the algebraic point of view, every logic L 2 NExtIntKM , for M
f2 3g, corresponds to the variety of Heyting algebras with one or two

138

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

operators validating L. The variety of algebras for IntKM will be called the
variety of M-algebras.
To construct the relational representations of M-algebras, we dene a 2frame to be a structure of the form hW R R2  P i in which hW R P i is an
intuitionistic frame, R2 a binary relation on W such that

R  R2  R = R2
and P is closed under the operation

2X = fx 2 W : 8y 2 W (xR2 y ! y 2 X )g:
A 3-frame has the form hW R R3  P i, where hW R P i is again an intuitionistic frame, R3 a binary relation on W satisfying the condition
R;1  R3  R;1 = R3
and P is closed under
3X = fx 2 W : 9y 2 X xR3 yg:
Finally, a 23-frame is a structure hW R R2 R3  P i the unimodal reducts
hW R R2  P i and hW R R3  P i of which are 2- and 3-frames, respec-

tively. (To see why the intuitionistic and modal accessibility relations are
connected by the conditions above the reader can construct in the standard
way the canonical models for the logics under consideration. The important
point here is that we take the Leibnizean denition of the truth-relation for
the modal operators. Other denitions may impose di erent connecting
conditions see below.)
Given a 23-frame F = hW R R2 R3  P i, it is easy to check that its dual

F+ = hP \  !  2 3i
is a 23-algebra. Conversely, for each 23-algebra A = hA ^ _ ! ? 2 3i
we can dene the dual frame

A+ = hW R R2 R3  P i
by taking hW R P i to be the dual of the Heyting algebra hA ^ _ ! ?i
and putting
r1 R2 r2 i 8a 2 A (2a 2 r1 ! a 2 r2 )
r1 R3 r2 i 8a 2 A (a 2 r2 ! 3a 2 r1 ):
A+ is a 23-frame and, moreover, A 
= (A+ )+ . Using the standard technique
of the model theory for classical modal and si-logics, one can show that a

ADVANCED MODAL LOGIC

139

23-frame F is isomorphic to its bidual (F+ )+ i F = hW R R2 R3  P i is
descriptive, i.e., hW R P i is a descriptive intuitionistic frame and, for all
x y 2 W ,
xR2 y i 8X 2 P (x 2 2X ! y 2 X )
xR3 y i 8X 2 P (y 2 X ! x 2 3X ):
Thus we get the following completeness theorem.

THEOREM 3.35 Every logic L 2 NExtIntK23 is characterized by a suitable class of (descriptive) 23-frames, e.g. by the class fA+ : A j= Lg.
Similar results hold for logics in NExtIntK2 and NExtIntK3 .
As usual, by a Kripke frame we understand a frame hW R R2  R3  P i
in which P consists of all R-cones in this case we omit P . An intuitionistic modal logic L is D-persistent if the underlying Kripke frame of each
descriptive frame for L validates L. For example, FS as well as the logics

L(k l m n) = IntK23  3k 2l p ! 2m 3np for k l m n 0
are D-persistent and so Kripke complete (see Wolter and Zakharyaschev
1997b]). Descriptive frames validating FS satisfy the conditions

xR3 y ! 9z (yRz ^ xR2 z ^ xR3 z )
xR2 y ! 9z (xRz ^ zR2y ^ zR3y)
and those for L(k l m n) satisfy
xR3k y ^ xR2m y ! 9u (yR2l u ^ zR3n u):

It follows, in particular, that MIPC is D-persistent its Kripke frames have
the properties: R2 is a quasi-order, R3 = R2;1 and R2 = R  (R2 \ R3 ). On
the contrary, I4 is not D-persistent, although it is complete with respect to
the class of Kripke frames hW R R2i such that hW R2 i is a frame for GL
and R the reexive closure of R2 .
The next step in constructing duality theory of M-algebras and M-frames
is to nd relational counterparts of the algebraic operations of forming homomorphisms, subalgebras and direct products. Let F = hW R R2  R3  P i
be a 23-frame and V a non-empty subset of W such that
8x 2 V 8y 2 W (xR2 y _ xRy ! y 2 V )

8x 2 V 8y 2 W (xR3 y ! 9z 2 V (xR3 z ^ yRz )):
Then G = hV R V R2 V R3 V fX \ V : X 2 P gi is also a 23-frame
which is called the subframe of F generated by V . The former of the two

140

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

z

y R -z
K
A






R3A R3

F Ax

6

R3

G x

Figure 17.
0


1 R3 4



R

R3A R

K
A

6


2

F

01 S3 4



I S3; 6
@
S 6;
@
S S




3

A

; S @
G 2 33

3

Figure 18.
conditions above is standard: it requires V to be upward closed with respect
to both R and R2. However, the latter one does not imply that V is upward
closed with respect to R3 : the frame G in Fig. 17 is a generated subframe
of F, although the set fx z g is not an R3 -cone in F. This is one di erence
from the standard (classical modal or intuitionistic) case. Another one arises
when we dene the relational analog of subalgebras.
Given 23-frames F = hW R R2  R3  P i and G = hV S S2  S3  Qi, we
say a map f from W onto V is a reduction of F to G if f ;1 (X ) 2 P for
every X 2 Q and, for all x y 2 W and u 2 V ,
xRy implies f (x)Sf (y),
xR y implies f (x)S f (y), for # 2 f2 3g,
f (x)Su implies 9z 2 f ;1(u) xRz ,
f (x)S2 u implies 9z 2 f ;1(u) xR2 z ,
f (x)S3 u implies 9z 2 W (xR3 z ^ uSf (z )),
Again, the last condition di ers from the standard one: given f (x)S3 f (y),
in general we do not have a point z such that xR3 z and f (y) = f (z ), witness
the map gluing 0 and 1 in the frame F in Fig. 18 and reducing it to G.
Note that both these concepts coincide with the standard ones in classical
modal frames, where R and S are the diagonals. The relational counterpart
of direct products|disjoint unions of frames|is dened as usual.
THEOREM 3.36 (i) If G is the subframe of a 23-frame F generated by V
then the map h dened by h(X ) = X \ V , for X an element in F+, is a

ADVANCED MODAL LOGIC

141

homomorphism from F+ onto G+ .
(ii) If h is a homomorphism from a 23-algebra A onto a 23-algebra B
then the map h+ dened by h+ (r) = h;1 (r), r a prime lter in B, is an
isomorphism from B+ onto a generated subframe of A+ .
(iii) If f is a reduction of a 23-frame F to a 23-frame G then the map
f + dened by f +(X ) = f ;1(X ), X an element in G+ , is an embedding of
G+ into F+ .
(iv) If B is a subalgebra of a 23-algebra A then the map f dened by
f (r) = r\ B , r a prime lter in A and B the universe of B, is a reduction
of A+ to B+ .

This duality can be used for proving various results on modal denability.
For instance, a class C of 23-frames is of the form C = fF : F j= ;g, for some
set ; of L23 -formulas, i C is closed under the formation of generated subframes, reducts, disjoint unions, and both C and its complement are closed
under the operation F 7! (F+ )+ (see Wolter and Zakharyaschev 1997b]).
Moreover, one can extend Fine's Theorem connecting the rst order denability and D-persistence of classical modal logics to the intuitionistic modal
case:
THEOREM 3.37 If a logic L 2 NExtIntK23 is characterized by an elementary class of Kripke frames then L is D-persistent.
These results may be regarded as a justication for the relational semantics introduced in this section. However, it is not the only possible one. For
example, Bo)zic and Do)sen 1984] impose a weaker condition on the connection between R and R2 in 2-frames. Fisher Servi 1980] interprets FS
in birelational Kripke frames of the form hW R S i in which R is a partial
order, R  S S  R, and

xRy ^ xSz ! 9u (ySu ^ zRu):
The intuitionistic connectives are interpreted by R and the truth-conditions
for 2 and 3 are dened as follows
2X = fx 2 W : 8y z (xRySz ! z 2 X g
3X = fx 2 W : 9y 2 X xSyg:
In birelational frames for MIPC S is an equivalence relation and
xSyRz ! 9u xRuSz:
These frames were independently introduced by L. Esakia who also established duality between them and \monadic Heyting algebras".

142

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

There are two ways of investigating various properties of intuitionistic
modal logics. One is to continue extending the classical methods to logics
in NExtIntKM . Another one uses those methods indirectly via embeddings
of intuitionistic modal logics into classical ones. That such embeddings
are possible was noticed by Shehtman 1979], Fischer Servi 1980, 1984],
and Sotirov 1984]. Our exposition here follows Wolter and Zakharyaschev
1997a,b]. For simplicity we conne ourselves only to considering the class
NExtIntK2 and refer the reader to the cited papers for information about
more general embeddings.
Let T be the translation of L2 into L2I 2 prexing 2I to every subformula of a given L2 -formula. Thus, we are trying to embed intuitionistic
modal logics in NExtIntK2 into classical bimodal logics with the necessity
operators 2I (of S4) and 2. Say that T embeds L 2 NExtIntK2 into
M 2 NExt(S4 & K) (S4 in L2I and K in L2 ) if, for every ' 2 L2 ,

' 2 L i T (') 2 M:
In this case M is called a bimodal (or BM-) companion of L.
For every logic M 2 NExt(S4 & K) put

M = f' 2 L2 : T (') 2 M g

and let  be the map from NExtIntK2 into NExt(S4 & K) dened by

(IntK2  ;) = (Grz & K)  mix  T (;)
where ; L2 and mix = 2I 22I p $ 2p. (The axiom mix reects the

condition R  R2  R = R2 of 2-frames.) Then we have the following
extension of the embedding results of Maksimova and Rybakov 1974], Blok
1976] and Esakia 1979a,b]:
THEOREM 3.38 (i) The map  is a lattice homomorphism from the lattice
NExt(S4 & K) onto NExtIntK2 preserving decidability, Kripke completeness, tabularity and the nite model property.
(ii) Each logic IntK2  ; is embedded by T into any logic M in the
interval
(S4 & K)  T (;) M

(Grz & K)  mix  T (;):

(iii) The map  is an isomorphism from the lattice NExtIntK2 onto the
lattice NExt(Grz & K)  mix preserving FMP and tabularity.
Note that Fischer Servi 1980] used another generalization of the Godel
translation. She dened
T (3') = 3T (')

ADVANCED MODAL LOGIC

143

T (2') = 2I 2T (')

and showed that this translation embeds FS into the logic

(S4 & K)  32I p ! 2I 3p  33I p ! 3I 3p:

It is not clear, however, whether all extensions of FS can be embedded into
classical bimodal logics via this translation.
Let us turn now to completeness theory of intuitionistic modal logics. As
to the standard systems I4, FS, and MIPC, their FMP can be proved
by using (sometimes rather involved) ltration arguments see Muravitskij 1981], Simpson 1994] and Grefe 1997], and Ono 1977], respectively.
Further results based on the ltration method were obtained by Sotirov
1984] and Ono 1977]. However, in contrast to classical modal logic, only a
few general completeness results covering interesting classes of intuitionistic
modal logics are known. The proofs of the following two theorems are based
on the translation into classical bimodal logics discussed above.
THEOREM 3.39 Suppose that a si-logic Int + ; has one of the properties:
decidability, Kripke completeness, FMP. Then the logics IntK2  ; and
IntK2  ;  2p ! p also have the same property.

Proof It suces to show that there is a BM-companion of each of these
systems satisfying the corresponding property. Notice that

((S4  T (;)) & K) = IntK2  ;

((S4  T (;)) & (K  2p ! p)) = IntK2  ;  2p ! p:

So it remains to use the fact that if Int + ; has one of the properties
under consideration then its smallest modal companion S4  T (;) has this
property as well (Table 7), and if L1 , L2 are unimodal logics having one
of those properties then the fusion L1 & L2 also enjoys the same property
(Theorem 2.6).
2
Such a simple reduction to known results in classical modal logic is not
available for logics containing IntK42 = IntK2  2p ! 22p. However,
by extending Fine's 1974] method of maximal points to bimodal companions of extensions of IntK42 Wolter and Zakharyaschev 1997a] proved the
following:
THEOREM 3.40 Suppose L  IntK42 has a D-persistent BM-companion
M  (S4 & K4)  mix whose Kripke frames are closed under the formation
of substructures. Then
(i) for every set ; of intuitionistic negation and disjunction free formulas,
L  ; has FMP

144

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

(ii) for every set ; of intuitionistic disjunction free formulas and every

n 1,

L;

_n (pi ! _ pj )

i=0

j 6=i

has the nite model property.
One can use this result to show that the following (and many other)
intuitionistic modal logics enjoy FMP:
(1) IntK42
(2) IntS42 = IntK42  2p ! p (R2 is reexive)
(3) IntS4:32 = IntS42  2(2p ! q) _ 2(2q ! p) (R2 is reexive and
connected)
(4) IntK42  p _ 2:2p (R2 is symmetrical)
(5) IntK42  2p _ 2:2p (R2 is Euclidean)
(6) IntK42  2p _ :2p (xRy ^ xR2 z ! yR2z )
We conclude this section with some remarks on lattices of intuitionistic modal logics. Wolter 1997c] uses duality theory to study splittings of
lattices of intuitionistic modal logics. For example, he showed that each
nite rooted frame splits NExt(L  2n p ! 2n+1 p), for L = IntK2 and
L = FS, and each R2 -cycle free nite rooted frame splits the lattices of
extensions of IntK2 and FS. No positive results are known, however, for
the lattice NExtIntK3 . In fact, the behavior of 3-frames is quite di erent
from that of frames for FS. For instance, in classical modal logic we have
RGF = GRF , for each class of frames (or even 2-frames) F , where G and R
are the operations of forming generated subframes and reducts, respectively.
But this does not hold for 3-frames. More precisely, there exists a nite
3-frame G such that RGfGg 6 GRfGg. In other terms, the variety of modal
algebras for K has the congruence extension property (i.e., each congruence
of a subalgebra of a modal algebra can be extended to a congruence of the
algebra itself) but this is not the case for the variety of 3-algebras.
Vakarelov 1981, 1985] and Wolter 1997c] investigate how logics having
Int as their non-modal fragment are located in the lattices of intuitionistic
modal logics. It turns out, for instance, that in NExtIntK3 the inconsistent
logic has a continuum of immediate predecessors all of which have Int as
their non-modal fragment, but no such logic exists in the lattice of extensions
of IntK2 .

4 ALGORITHMIC PROBLEMS
All algorithmic results considered in the previous sections were positive:
we presented concrete procedures for deciding whether an arbitrary given

ADVANCED MODAL LOGIC

145

formula belongs to a given logic in some class or whether it axiomatizes
a logic with a certain property. What is the complexity of those decision
algorithms? Do there exist undecidable calculi18 and properties? These are
the main questions we address in this chapter.

4.1 Undecidable calculi

The rst undecidable modal and si-calculi were constructed by Thomason
1975c] (polymodal and unimodal), Isard 1977] (unimodal) and Shehtman
1978b] (superintuitionistic). However, we begin with the very simple example of Shehtman 1982] which is a modal reformulation of the undecidable
associative calculus T of Tseitin 1958]. The axioms of T are
ac = ca
ad = da
bc = cb
bd = db
edb = be
eca = ae
abac = abacc:
The reader will notice immediately an analogy between them and the axioms
of the following modal calculus with ve necessity operators:
L = K5  21 23 p $ 23 21 p  21 24 p $ 24 21 p 
22 23 p $ 23 22 p  22 24 p $ 24 22 p 
25 24 22 p $ 22 25 p  25 23 21 p $ 21 25 p 
21 22 21 23 p $ 21 22 21 23 23 p:
Moreover, it is not hard to see that words x, y in the alphabet fa b c d eg
are equivalent in T 19 i f (x)p $ f (y)p 2 K5 , where f is the natural
one-to-one correspondence between such words and modalities in language
f21  : : :  25 g under which, for instance, f (cadedb) = 23 21 24 25 24 22 . It
follows immediately that L is undecidable. Using the undecidable associative calculus of Matiyasevich 1967], one can construct in the same way an
undecidable bimodal calculus having three reductions of modalities as its
axioms. It is unknown whether there is an undecidable unimodal calculus
axiomatizable by reductions of modalities.
Thomason's simulation and the undecidable polymodal calculi mentioned
above provide us with examples of undecidable calculi in NExtK. However,
to nd axioms of undecidable unimodal calculi with transitive frames, as
well as undecidable si-calculi, a more sophisticated construction is required.
18 By a calculus we mean a logic with nitely many axioms (inference rules in our case
are xed).
19 I.e., they can be obtained from each other by a nite number of transformations of
the form w1 ww2 ! w1 vw2 , where w = v or v = w is an axiom of T .

146

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

b X
yXX d
X

X
yXX

a

X
yXX d1
XX
yXX d2
XX
X



yXX g1


I XX
g@
yXX g2
@a0 @
X

0 I@ 1 
I 
6
a0 @
@a2
6
0
 a01
 a11
6a21
.6a02
.6a12
.6a22
..
..
..
 a0t;1  a1k;1  a2l;1
.6a0t
.6a1k *.6a2l
..J]
..
..

J 
. . .J. . .
e(t k l)
6




Figure 19.
Instead of associative calculi, let us use now Minsky machines with two
tapes (or register machines with two registers). A Minsky machine is a
nite set (program) of instructions for transforming triples hs m ni of natural numbers, called congurations. The intended meaning of the current
conguration hs m ni is as follows: s is the number (label) of the current
machine state and m, n represent the current state of information. Each
instruction has one of the four possible forms:

s ! ht 1 0i  s ! ht 0 1i 
s ! ht ;1 0i (ht0  0 0i) s ! ht 0 ;1i (ht0  0 0i):
The last of them, for instance, means: transform hs m ni into ht m n ; 1i
if n > 0 and into ht0  m ni if n = 0. For a Minsky machine P , we shall
write P : hs m ni ! ht k li if starting with hs m ni and applying the

instructions in P , in nitely many steps (possibly, in 0 steps) we can reach
ht k li.
We shall use the well known fact (see e.g. Mal'cev 1970]) that the following conguration problem is undecidable: given a program P and congurations hs m ni, ht k li, determine whether P : hs m ni ! ht k li.
With every program P and conguration hs m ni we associate the transitive frame F depicted in Fig. 19. Its points e(t k l) represent congurations
ht k li such that P : hs m ni ! ht k li e(t k l) sees the points a0t , a1k , a2l

ADVANCED MODAL LOGIC

147

representing the components of ht k li. The following variable free formulas
characterize points in F in the sense that each of these formulas, denoted by
Greek letters with subscripts and/or superscripts, is true in F only at the
point denoted by the corresponding Roman letter with the same subscript
and/or superscript:

 = 3> ^ 23>  = 2?  = 3 ^ 3 ^ :32
= : ^ 3 ^ :32 1 = 3 ^ :32  2 = 3 1 ^ :32 1 
1 = 3 ^ :32 ^ :3  2 = 31 ^ :321 ^ :3 
00 = 3 ^ 3 ^ :32  ^ :32 
10 = 31 ^ 3 1 ^ :321 ^ :32 1 
20 = 32 ^ 3 2 ^ :322 ^ :32 2 
^
ij+1 = 3ij ^ :32ij ^ :30k 
i6=k

where i 2 f0 1 2g, j 0. The formulas characterizing e(t k l) are denoted
by (t 1k  2l ), where

(t ' ) =

^t 3 ^ :3
0

i=0

i

0
t+1

^ 3' ^ :32' ^ 3 ^ :32:

We require also formulas characterizing not only xed but arbitrary congurations:
1 = (310 _ 10 ) ^ :300 ^ :320 ^ p1 ^ :3p1
2 = 310 ^ :300 ^ :320 ^ 3p1 ^ :32 p1 
1 = (320 _ 20 ) ^ :300 ^ :310 ^ p2 ^ :3p2 
2 = 320 ^ :300 ^ :310 ^ 3p2 ^ :32p2 :
Now we are fully equipped to simulate the behavior of Minsky machines by
means of modal formulas. Let us consider for simplicity only tense logics
and observe that F satises the condition
8x8y9z (xRzR;1y _ xR;1 zRy _ xRy _ xR;1 y _ x = y):

So, for every valuation in F, a formula ' is true at some point in F i the
formula
#' = 33;1' _ 3;13' _ 3' _ 3;1' _ '
is true at all points in F, i.e., the modal operator # can be understood
as \omniscience". Let  be a formula which is refuted in F and does not

148

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

contain p1 and p2 . With each instruction I in P we associate a formula
AxI by taking:

AxI = : ^ #(t 1  1 ) ! : ^ #(t0  2  1 )
if I has the form t ! ht0  1 0i,

AxI = : ^ #(t 1  1 ) ! : ^ #(t0  1  2 )
if I is t ! ht0  0 1i,

AxI = (: ^ #(t 2  1 ) ! : ^ #(t0  1  1 )) ^
(: ^ #3(t 10 1 ) ! : ^ #(t00  10  1 ))
if I is t ! ht0  ;1 0i (ht00  0 0i),

AxI = (: ^ #(t 1  2 ) ! : ^ #(t0  1  1 )) ^
(: ^ #(t 1  20 ) ! : ^ #(t00  1  20 ))
if I is t ! ht0  0 ;1i (ht00  0 0i). The formula simulating P as a whole is

AxP =

^ AxI:

I 2P

Now, by induction on the length of computations and using the frame F in
Fig. 19 one can show that for every program P and congurations hs m ni,
ht k li, we have P : hs m ni ! ht k li i
: ^ #(s 1m  2n ) ! : ^ #(t 1k  2l ) 2 K4:t  AxP:

Thus, if the conguration problem is undecidable for P then the tense
calculus K4:t  AxP is undecidable too. In the same manner (but using
somewhat more complicated frames and formulas) one can construct undecidable calculi in NExtK4 and even ExtInt for details consult Chagrova
1991] and Chagrov and Zakharyaschev 1997]. The following table presents
some "quantitative characteristics" of known undecidable calculi in various
classes of logics. Its rst line, for instance, means that there is an undecidable si-calculus with axioms in 4 variables and the derivability problem in
it is undecidable in the class of formulas in 2 variables = means that the
number of variables is optimal, and  indicates that the optimal number is
still unknown.

ADVANCED MODAL LOGIC

149

The number of variables in
Class of logics undecidable calculi separated formulas
ExtInt
 4 2
=2
NExtS4
 3 2
=1
ExtS4
3
=1
NExtGL
=1
=1
ExtGL
=1
=1
ExtS
=1
=1
NExtK4
=1
=0
ExtK4
=1
=0
These observations follow from Anderson 1972], Chagrov 1994], Sobolev
1977b], and Zakharyaschev 1997a]. Say that a formula  is undecidable in
(N)ExtL if no algorithm can determine for an arbitrary given ' whether
 2 L + ' (respectively,  2 L  '). For example, formulas in one variable,
the axioms of BWn and BDn are decidable in ExtInt. On the other hand,
there are purely implicative undecidable formulas in ExtInt, and
:(p ^ q) _ :(:p ^ q) _ :(p ^ :q) _ :(:p ^ :q)
is the shortest known undecidable formula in this class. Here are some modal
examples: the formula 2(22 ? ! 2p _ 2:p) is undecidable in NExtGL,
2+ :2+ p _ 2+ :2+ :2+ p in ExtS, ? in ExtK4 and NExtK4:t in NExtK
and NExtK4:t undecidable is the conjunction of axioms of any consistent
tabular logic in these classes. However, no non-trivial criteria are known for
a formula to be decidable it is unclear also whether one can e ectively
recognize the decidability of formulas in the classes ExtInt, (N)ExtS4,
(N)ExtGL, ExtS, (N)ExtK4.

4.2 Admissibility and derivability of inference rules

Another interesting algorithmic problem for a logic L is to determine whether
an arbitrary given inference rule '1  : : :  'n =' is derivable in L, i.e., ' is
derivable in L from the assumptions '1  : : :  'n , and whether it is admissible in L, i.e., for every substitution s, 's 2 L whenever '1 s : : :  'n s 2 L.
(Note that derivability depends on the postulated inference rules in L,
while admissibility depends only on the set of formulas in L.) Admissible
and derivable rules are used for simplifying the construction of derivations.
Derivable rules, like the well known rule of syllogism
' !   !  
'!
may replace some fragments of xed length in derivations, thereby shortening them linearly. Admissible rules in principle may reduce derivations

150

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

more drastically. Since ' 2 L i the rule >=' is derivable (or admissible)
in L, the derivability and admissibility problems for inference rules may be
regarded as generalizations of the decidability problem.
If the only postulated rules in L are substitution and modus ponens, the
Deduction Theorem reduces the derivability problem for inference rules in
L to its decidability:

'1  : : :  'n is derivable in L i ' ^ : : : ^ ' !  2 L:
1
n

However, if the rule of necessitation '=2' is also postulated in L, we have
only
'1  : : :  'n is derivable in L i '  : : :  ' ` :
1
n L

For n-transitive L this is equivalent to 2n ('1 ^ : : : ^ 'n ) !  2 L, and so
the derivability problem for inference rules in n-transitive logics is decidable

i the logics themselves are decidable. In general, in view of the existential
quantier in Theorem 1.1, the situation is much more complicated.
Notice rst that similarly to Harrop's Theorem, a sucient condition for
the derivability problem to be decidable in a calculus is its global FMP (see
Section 1.5). Thus we have
THEOREM 4.1 The derivability problem for inference rules in K, T, D,
KB is decidable.

Moreover, sometimes we can obtain an upper bound for the parameter m
in the Deduction Theorem, which also ensures the decidability of the derivability problem for inference rules. One can prove, for instance, that for K
it is enough to take m = 2jSub' Subj . In general, however, the derivability
problem for inference rules in a logic L turns out to be more complex than
the decidability problem for L. (Recall, by the way, that there are logics
with FMP but not global FMP.)
THEOREM 4.2 (Spaan 1993) There is a decidable calculus in NExtK the
derivability problem for inference rules in which is undecidable.
Spaan proves this result by simulating in `L , L a decidable logic dened
below, the following undecidable tiling problem: given a nite set of tiles
T , can T tile N ' N ? The logic L is surprisingly simple:

L = Alt2 

^ 33pi ! _ 33(pi ^ pj ):

1i4

1i<j 4

It is a subframe logic, so it is D-persistent and has FMP (because Alt2 L
see Theorem 1.22 and Proposition 1.59). Note also that the bimodal logic

ADVANCED MODAL LOGIC

151

Lu (see Section 2.2) is a complete and elementary subframe logic which

is undecidable because `L is undecidable. Using this observation one can
construct a unimodal subframe logic in NExtK with the same properties.
Let us turn now to the admissibility problem. It is not hard to see that
the rules
(::p ! p) ! p _ :p and
:p ! q _ r
:p _ ::p
(:p ! q) _ (:p ! r)
are admissible but not derivable in Int and 3p ^ 3:p=? is admissible but
not derivable in any extension of S4.3 save those containing 23p ! 32p,
in which it is derivable. (Recall that a logic L is said to be structurally
complete if every admissible inference rule in L is derivable in L. We have
just seen that Int as well as S4.3 are not structurally complete. For more
information on structural completeness see e.g. Tsytkin 1978, 1987] and
Rybakov 1995].) The following result strengthens Fine's 1971] Theorem
according to which all logics in ExtS4.3 are decidable.
THEOREM 4.3 (Rybakov 1984a) The admissibility problem for inference
rules is decidable in every logic containing S4.3.
An impetus for investigations of admissible inference rules in various
logics was given by Friedman's 1975] problem 40 asking whether one can
e ectively recognize admissible rules in Int. This problem turned out to be
closely connected to the admissibility problem in suitable modal logics. We
demonstrate this below for the logic GL following Rybakov 1987, 1989].
First we show that dealing with logics in NExtK, it is sucient to consider
inference rules of a rather special form. Let '(q1  : : :  q2n+2 ) be a formula
containing no 2 and 3 and represented in the full disjunctive normal form.
Say that an inference rule is reduced if it has the form
'(p0  : : :  pn 3p0 : : :  3pn)=p0 :
THEOREM 4.4 For every rule '= one can eectively construct a reduced
rule '0 =0 such that '= is admissible in a logic L 2 NExtK i '0 =0 is
admissible in L.
Proof Observe rst that if ' and  do not contain p then '= is admissible
in L i ' ^ ( $ p)=p is admissible in L. So we can consider only rules of
the form '=p0 . Besides, without loss of generality we may assume that '
does not contain 2. With every non-atomic subformula  of ' we associate
the new variable p . For convenience we also put p = pi if  = pi and
p = ? if  = ?. We show now that the rule
p' ^ fp $ p1 $ p2 :  = 1 $ 2 2 Sub' $ 2 f^ _ !gg ^
fp $ 3p1 :  = 31 2 Sub'g=p0

^

^

152

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

is admissible in L i '=p0 is admissible in L. For brevity we denote the
antecedent of that rule by '00 .
()) Since every substitution instance of '00 =p0 is admissible in L, the
rule ' ^ 2 Sub' ( $ )=p0 and so '=p0 are also admissible in L.
(() Suppose '=p0 is admissible in L and '00 s is in L, for some substitution s = f =p :  2 Sub'g. By induction on the construction of 
one can readily show that  $ s 2 L. Therefore, ' $ 's 2 L. Since
'00 s 2 L, we must have p's = ' 2 L, from which 's 2 L and so p0 s 2 L.
Thus '00 =p0 is admissible in L.
The rule '00 =p0 is not reduced, but it is easy to make it so simply by
representing '00 in its full disjunctive normal form '0 , treating subformulas
3pi as variables.
2

V

W

From now on we will deal with only reduced rules di erent from ?=p0
(which is clearly admissible in any logic). Let j 'j =p0 be a reduced rule
in which every disjunct 'j is the conjunction of the form
:0 p0 ^ : : : ^ :m pm ^ :0 3p0 ^ : : : ^ :m 3pm

(17)

where each :i and :j is either blank or :. We will identify such conjunctions with the sets of their conjuncts. Now, given a non-empty set W of
conjunctions of the form (17), we dene a frame F = hW Ri and a model
M = hF Vi by taking

'i R'j i

8k 2 f0 : : :  mg(:3pk 2 'i ! :3pk 2 'j ^ :pk 2 'j ) ^
9k 2 f0 : : :  mg(:3pk 2 'j ^ 3pk 2 'i )

V(pk ) = f'i 2 W : pk 2 'i g:
It should be clear that F is nite, transitive and irreexive.
W
THEOREM 4.5 A reduced rule j 'j =p0 is not admissible in GL i there
is a model M = hF Vi dened as above on a set W of conjunctions of the

form (17) and such that
(i) :p0 2 'i for some 'i 2 W 
(ii) 'i j= 'i for every 'i 2 W 
(iii) for every antichain a in F there is 'j 2 W such that, for every
k 2 f0 : : :  mg, 'j j= 3pk i 'i j= 3+pk for some 'i 2 a.

Proof ()) We are given
W that there are formulas 0 : : :  m in variables
q1  : : :  qn such that j 'j 2 GL and p0 62 GL, where by W we de-

W

note f0 =p0 : : :  m =pmg. This is equivalent to MGL (n) j= j 'j and
MGL (n) 6j= p0 . Dene W to be the set of those disjuncts 'j in j 'j whose
substitution instances 'j are satised in MGL (n). Clearly W 6= . Let us
check (i) { (iii).

ADVANCED MODAL LOGIC

153

a point x in MGL (n) at which p is false. Since MGL (n) j=
Wj(i)'j ,Take
we must have x j= 'i for some i. One of the formulas p or :p is a
0

0

0

conjunct of 'i . Clearly it is not p0 . Therefore, :p0 2 'i .
(ii) It suces to show that, for all 'i 2 W and k 2 f0 : : :  mg, 'i j= 3pk
i 3pk 2 'i . Suppose 'i j= 3pk . Then there is 'j 2 W such that 'i R'j
and 'j j= pk . By the denition of V and R, this means that pk 2 'j
and 3pk 2 'i . Conversely, suppose 3pk 2 'i . Then x j= 'i and in
particular x j= 3pk for some x in MGL (n). Let y be a nal point in the set
fz 2 x": z j= pk g. Since MGL (n) is irreexive, we have y j= pk , y 6j= 3pk
and y j= 'j for some 'j 2 W . It follows that 'i R'j and 'j j= pk , from
which 'i j= 3pk .
(iii) Let a be an antichain in F. For every 'i 2 a, let xi be a nal point
in the set fy 2 WGL (n) : y j= 'i g. It should be clear that the points
fxi : 'i 2 ag form an antichain b in FGL (n) and so, by the construction of
FGL (n), there is a point y in FGL(n) such that y" = b". Then the formula
'j 2 W we are looking for is any one satisfying the condition y j= 'j , as
can be easily checked by a straightforward inspection.
(() The proof in this direction is rather technical we conne ourselves
to just a few remarks. Let M be a model satisfying (i){(iii). To prove that
j 'j =p0 is not admissible in GL we require once again the n-universal
model MGL (n), but this time we take n to be the number of symbols in the
rule. By induction on the depth of points in M one can show that M is a
generated submodel of MGL (n).
Our aim is to nd formulas 0  : : :  m such that MGL (n) j= j 'j and
MGL (n) 6j= p0 (here again  = f0 =p0  : : :  m =pm g). Loosely, we need
to extend the properties of M to the whole model MGL (n). To this end
we can take the sets f'i g in FGL(n) and augment them inductively in such
a way that we could embrace all points in FGL (n). At the induction step
we use the condition (iii), and the required 0  : : :  m are constructed with
the help of (i) and (ii) roughly, they describe in MGL (n) the analogues of
the truth-sets in M of the variables in our rule.
2

W

W

A remarkable feature of this criterion is that it can be e ectively checked.
Thus we have
THEOREM 4.6 There is an algorithm which, given an inference rule, can
decide whether it is admissible in GL.
In a similar way one can prove
THEOREM 4.7 (Rybakov 1987) The admissibility problem in Grz is decidable.

154

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

We show now that the admissibility problem in Int can be reduced to
the same problem in Grz and so is also decidable. To this end we require
the following
THEOREM 4.8 (Rybakov 1984b) A rule '= is admissible in Int i the
rule T (')=T () is admissible in Grz.
As a consequence of Theorems 4.7 and 4.8 we obtain
THEOREM 4.9 (Rybakov 1984b) The admissibility problem in Int is decidable.
Although there are many other examples of logics in which the admissibility problem is decidable and the scheme of establishing decidability is
quite similar to the argument presented above, proofs are rather dicult
and only in few cases they work for big families of logics as in Rybakov
1994]. Besides, all these results hold only for extensions of K4 and Int.
For logics with non-transitive frames, even for K, the admissibility problem
is still waiting for a solution. The same concerns polymodal, in particular
tense logics. Chagrov 1992b] constructed a decidable innitely axiomatizable logic in NExtK4 for which the admissibility problem is undecidable.
It would be of interest to nd modal and si-calculi of that sort.
A close algorithmic problem for a logic L is to determine, given an arbitrary formula '(p1  : : :  pn ), whether there exist formulas 1 ,. . . , n such
that '(1  : : :  n ) 2 L. Note that an "equation" '(p1  : : :  pn) has a solution in L i the rule '(p1  : : :  pn )=? is not admissible in L. This observation and Theorem 4.3 provide us with examples of logics in which the
substitution problem is decidable (see e.g. Rybakov 1993]). We do not
know, however, if there is a logic such that the substitution problem in it is
decidable, while the admissibility one is not.
The inference rules we have dealt with so far were structural in the sense
that they were \closed" under substitution. An interesting example of a
nonstructural rule was considered by Gabbay 1981a]:

' _ (2p ! p) where p 62 Sub' :
'
It is readily seen that this rule holds in a frame F (in the sense that for every
formula ' and every variable p not occurring in ', ' is valid in F whenever
(2p ! p) _ ' is valid in F) i F is irreexive and that K is closed under
it (since K is characterized by the class of irreexive frames). We refer the
reader to Venema 1991] for more information about rules of this type.

ADVANCED MODAL LOGIC

155

4.3 Properties of recursively axiomatizable logics

Dealing with innite classes of logics, we can regard questions like \Is a
logic L decidable?", \Does L have FMP?", etc., as mass algorithmic problems. But to formulate such problems properly we should decide rst how
to represent the input data of algorithms recognizing properties of logics.
One can, for instance, consider the class of recursively axiomatizable logics (which, by Craig's 1953] Theorem, coincides with that of recursively
enumerable ones) and represent them as programs generating their axioms.
However, this approach turns out to be too general because the following
analog of the Rice{Uspenskij Theorem holds.
THEOREM 4.10 (Kuznetsov) No nontrivial property of recursively axiomatizable si-logics is decidable.
Of course, nothing will change if we take some other family of logics, say
NExtK4. The proof of this theorem (Kuznetsov left it unpublished) is very
simple we give it even in a more general form than required.
PROPOSITION 4.11 Suppose L1 and L2 are logics in some family L, L1
is recursively axiomatizable, L1  L2 , L2 is nitely axiomatizable (say, by
a formula  ), and a property P holds for only one of L1 , L2 . Then no
algorithm can recognize P , given a program enumerating axioms of a logic
in L.

Proof Let 0 1  : : : be a recursive sequence of axioms for L1. Given an
arbitrary (Turing, Minsky, Pascal, etc.) program P having natural numbers
as its input, we dene the following recursive sequence of formulas (where
(n)1 and (n)2 are the rst and second components of the pair of natural
numbers with code n under some xed e ective encoding):

n if P does not come to a stop on input (n)1 in (n)2 steps
 otherwise.
This sequence axiomatizes L1 if P does not come to a stop on any input and
L2 otherwise. It is well known in recursion theory that the halting problem
is undecidable, and so the property P is undecidable in L as well.
2
n =

The reader must have already noticed that this proof has nothing to
do with modal and si-logics it is rather about e ective computations. To
avoid this unpleasant situation let us conne ourselves to the smaller class
of nitely axiomatizable modal and si-logics and try to nd algorithms recognizing properties of the corresponding calculi. However, even in this case
we should be very careful. If arbitrary nite axiomatizations are allowed
then we come across the following

156

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

THEOREM 4.12 (Kuznetsov 1963) For every nitely axiomatizable si-logic
L (in particular, Int, Cl, inconsistent logic), there is no algorithm which,
given an arbitrary nite list of formulas, can determine whether its closure
under substitution and modus ponens coincides with L.
Needless to say that the same holds for (normal) modal logics as well.
Fortunately, the situation is not so hopeless if we consider nite axiomatizations over some basic logics. For instance, by Makinson's Theorem,
one can e ectively recognize, given a formula ', whether the logic K  '
is consistent. Other examples of decidable properties in various lattices of
modal logics were presented in Theorems 1.89, 1.93, 1.101, and 2.37. In the
next section we consider those properties that turn out to be undecidable
in various classes of modal and si-calculi.

4.4 Undecidable properties of calculi
The rst \negative" algorithmic results concerning properties of modal calculi were obtained by Thomason 1982] who showed that FMP and Kripke
completeness are undecidable in NExtK, and consistency is undecidable in
NExtK:t. Later Thomason's discovery has been extended to other properties and narrower classes of logics. In fact, a good many standard properties
of modal and si-calculi (in reasonably big classes) proved to be undecidable
decidable ones are rather exceptional.
In this section we present three known schemes of proving such kind of
undecidability results. Each of them has its advantages (as well as disadvantages) and can be adjusted for various applications. The rst one is due
to Thomason 1982].
Let L(n) be a recursive sequence of normal bimodal calculi such that no
algorithm can decide, given n, whether L(n) is consistent. Such sequences,
as we shall see a bit later, exist even in NExtK4:t. Suppose also that L is
a normal unimodal calculus which does not have some property, say, FMP,
decidability or Kripke completeness. Consider now the recursive sequence of
logics L(n) & L with three necessity operators. If L(n) is inconsistent then
the fusion L(n) & L is inconsistent too and so has the properties mentioned
above. And if L(n) is consistent then, in accordance with Proposition 2.5,
L(n) & L is a conservative extension of both L(n) and L , which means
that it is Kripke incomplete, undecidable and does not have FMP whenever
L is so. Consequently, the three properties under consideration cannot be
decidable in the class NExtK3 , for otherwise the consistency of L(n) would
be decidable. By Theorem 2.18, these properties are undecidable in NExtK
as well. Note however that, since Thomason's simulation embeds polymodal
logics only into \non-transitive" unimodal ones, this very simple scheme

ADVANCED MODAL LOGIC

157

does not work if we want to investigate algorithmic aspects of properties of
calculi in NExtK4 and ExtInt.
To illustrate the second scheme let us recall the construction of the undecidable calculus in NExtK4:t discussed in Section 4.1. First, we choose a
Minsky program P and a conguration a = hs m ni so that no algorithm
can decide, given a conguration b, whether P : a ! b. (That they exist is
shown in Chagrov 1990b].) Then we put  = ? and add to K4:t  AxP
one more axiom
(: ^ #(s 1m  2n ) ! : ^ #(t 1k  2l )) ! 
where c = ht k li is an arbitrary xed conguration. The resulting calculus
is denoted by L(c). Suppose that P : a 6! c. Then one can readily check
that the new axiom is valid in the frame F shown in Fig. 19 and prove that
P : hs m ni ! ht0 k0 l0i i
: ^ #(s 1m  2n ) ! : ^ #(t0  1k  2l ) 2 L(c):
Therefore, L(c) is undecidable, consistent and does not have FMP. And if
P : a ! c then L(c) is clearly inconsistent. It follows by the choice of P and
a that consistency, decidability and FMP are undecidable in NExtK4:t. In
fact, the argument will change very little if we take as  the axiom of some
tabular logic in NExtK4:t. So we obtain
THEOREM 4.13 The properties of tabularity and coincidence with an arbitrary xed tabular logic (in particular, inconsistent) are undecidable in
NExtK4:t
Moreover, these results (except the consistency problem, of course) can
be transferred to logics in NExtK. We demonstrate this by an example
complete proofs can be found in Chagrov 1996].
We require the frame which results from that in Fig. 19 by adding to it
a reexive point c0 and an irreexive one c1 so that c1 sees all other points
save a and b and is seen itself only from a and b. As before, we denote the
frame by F.
PROPOSITION 4.14 Let  be a formula refutable at some point in F different from c0 and 3> 2 K  . Then the problem of deciding, for an
arbitrary formula ', whether K  ' = K   is undecidable.
Proof It should be clear that  contains at least one variable, say r, and
there are points in F at which r has distinct truth-values (under the valuation refuting ) c0 and c1 are then the only points in F where the formulas
3
3
0 = 2 r _ 2 :r and
2
2
1 = 3 0 ^ (r _ 3r _ 3 r ) ^ (:r _ 3:r _ 3 :r )
0

0

158

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

are true, respectively. Observe that from every point in F save c0 we can
reach all points in F by  3 steps. So we can take # = 33. The formulas
 and  should be replaced with  = 3 1 ^ 32 1 ,  = 3 1 ^ :32 1 which
(under the valuation refuting ) are true only at a and b, respectively. Now
consider the logic

L(c) = K  AxP  (: ^ #(s 1m  2n ) ! : ^ #(t 1k  2l )) ! :

If P : a ! c then L(c) = K  . And if P : a 6! c then, using the fact that
the set of points in F where  is refutable coincides with the set of points
from which every point of the form e(x y z ) is accessible by three steps,
one can show that F j= L(c) and so L(c) 6= K  .
2
Putting, for instance,  = 2p $ p, we obtain then that the problem of
coincidence with Log is undecidable in NExtK. Likewise one can prove the
following
THEOREM 4.15 (i) If a consistent nitely axiomatizable logic L is not a
union-splitting of NExtK then the axiomatization problem for L above K is
undecidable.
(ii) The properties of tabularity and coincidence with an arbitrary xed
consistent tabular logic are undecidable in NExtK.
(iii) The problem of coincidence with an arbitrary xed consistent calculus
in NExtD4 or in NExtGL is undecidable in NExtK.
(iv) The properties of tabularity and coincidence with an arbitrary xed
tabular (in particular, inconsistent) logic are undecidable in ExtK4.
Of the algorithmic problems concerning tabularity that remain open the
most intriguing are undoubtedly the tabularity and local tabularity problems in NExtK4. Note that a positive solution to the former implies a
positive solution to the latter.
Now we present the second scheme in a more general form used in Chagrov 1990b] and Chagrov and Zakharyaschev 1993]. Assume again that the
second conguration problem is undecidable for P and a, and let  be a
formula such that L0   has some property P , where L0 is the minimal logic
in the class under consideration. Associate with P , a and a conguration
b formulas AxP and (a b) such that (a b) 2 L0  AxP i P : a ! b.
Besides,  and AxP are chosen so that AxP 2 L0  . Now consider the
calculus
L(b) = L0  AxP  (a b) !   
where  is some formula such that  2 L0  . If P : a ! b then we clearly
have L(b) = L0   and so L(b) has P  but if P : a 6! b then the fact
that L(b) does not have P must be ensured by an appropriate choice of  .

ADVANCED MODAL LOGIC

159

(In the considerations above we did not need  , i.e., it was sucient to put
 = >). With the help of this scheme one can prove the following
THEOREM 4.16 (i) The properties of decidability, Kripke completeness as
well as FMP are undecidable in the classes ExtInt, (N)ExtGrz, (N)ExtGL.
(ii) The interpolation property is undecidable in (N)ExtGL.
(iii) Hallden completeness is undecidable in ExtInt, (N)ExtGrz, ExtS.
These and some other results of that sort can be found in Chagrov
1990b,c, 1994, 1996], Chagrova 1991], Chagrov and Zakharyaschev 1993,
1995b].
The third scheme was developed in Chagrova 1989, 1991] and Chagrov
and Chagrova 1995] for establishing the undecidability of certain rst order
properties of modal calculi (or formulas). The di erence of this scheme from
the previous one is that now we use calculi of the form
L(b) = L0  AxP  (a b) _ 
where AxP satises one more condition besides those mentioned above:
it must be rst order denable on Kripke frames for L0. If P : a ! b
then the formula AxP ^ ((a b) _  ) is equivalent to AxP in the class of
Kripke frames for L0 and so is rst order denable on that class or its any
subclass. And if P : a 6! b then by choosing an appropriate  one can
show that AxP ^ ((a b) _  ) is not rst order denable on, say, countable
Kripke frames for L0 , as in Chagrova 1989], or on nite frames for L0, as in
Chagrov and Chagrova 1995]. In this way the following theorem is proved:
THEOREM 4.17 (i) No algorithm is able to recognize the rst order denability of modal formulas on the class of Kripke frames for S4 and even the
rst order denability on countable (nite) Kripke frames for S4. The properties of rst order denability and denability on countable (nite) Kripke
frames of intuitionistic formulas are undecidable as well.
(ii) The set of modal or intuitionistic formulas that are rst order denable on countable (nite) frames but are not rst order denable on the
class of all (respectively, countable) Kripke frames mentioned in (i) is undecidable.
We conclude this section with two remarks. First, all undecidability
results above can be formulated in the stronger form of recursive inseparability. For instance, the set of inconsistent calculi in NExtK4:t and the
set of calculi without FMP are recursively inseparable. And second, some
properties are not only undecidable but the families of calculi having them
are not recursively enumerable for example, the set of consistent calculi in
NExtK4:t is not enumerable. However, for the majority of other properties
the problem of enumerability of the corresponding calculi is open.

160

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

4.5 Semantical consequence

So far we have dealt with only syntactical formalizations of logical entailment. However, sometimes a semantical approach is preferable. Say that a
formula ' is a semantical consequence of a formula  in a class of frames
C if ' is valid in all frames in C validating . (One can consider also the
local, i.e., point-wise variant of this relation.) Note that ' is a consequence
of  in the class of, say, Kripke frames for S4 i ' is a consequence of
(2p ! 22 p) ^ (2p ! p) ^  in the class of all Kripke frames. But the
consequence relation on nite frames is not expressible by modal formulas
(as was shown in Chagrov 1995], if (2p ! 22 p) ^ ' is valid in arbitrarily
large nite rooted frames then it is valid in some innite rooted frame as
well).
In parallel with constructing and proving the undecidability of modal and
si-calculi we can obtain the following
THEOREM 4.18 The semantical consequence relation in the class of all
(K4-, S4-, Int-) Kripke frames is undecidable. Moreover, if j= denotes one
of these relations then there is a formula  (a formula ') such that the set
f' :  j= 'g is undecidable.
In a sense, formulas  and ', for which f' :  j= 'g is undecidable are
analogous to undecidable calculi and formulas, respectively. However, this
analogy is far from being perfect: for every formula , the sets f' :  ` 'g
and f' :  ` 'g are recursively enumerable, which contrasts with
THEOREM 4.19 (Thomason 1975a) There exists a formula  such that
f' :  j= 'g is a complete +11 set.
Unfortunately, Thomason's 1974b, 1975b, 1975c] results have not been
transferred so far to transitive frames, although this does not seem to be
absolutely impossible.
Chagrov 1990a] (see also Chagrov and Chagrova 1995]) developed a technique for proving the analog of Theorem 4.18 for the consequence relation
on all (K4-, S4-, GL-, Int-) nite frames. Moreover, since this relation is
clearly enumerable, instead of \undecidable" one can use \not enumerable".

4.6 Complexity problems

Having proved that a given logic is decidable, we are facing the problem of
nding an optimal (in one sense or another) decision algorithm for it. The
complexity of decision algorithms for many standard modal and si-logics is
determined by the size of minimal frames separating formulas from those
logics. For instance, as was shown by Jaskowski (1936) and McKinsey

ADVANCED MODAL LOGIC

161

(1941), for every ' 62 S4 (or ' 62 Int) there is a frame F j= S4 with
 2jSub'j points such that F 6j= '. The same upper bound is usually
obtained by the standard ltration. Is it possible to reduce the exponential
upper bound to the polynomial one? This question was raised by Kuznetsov
1975] for Int. It turned out, however, that it concerns not only Int. First,
Kuznetsov observed (for the proof see Kuznetsov 1979]) that if the answer
to his question is positive, i.e., Int has polynomial FMP, then the problem
\Are Int and Cl polynomially equivalent?" has a positive solution as well.
(Logics L1 and L2 are polynomially equivalent if there are polynomial time
transformations f and g of formulas such that ' 2 L1 i f (') 2 L2 and
' 2 L2 i g(') 2 L1 .) Then Statman 1979] showed that the problem \' 2
Int?" is PSPACE -complete and so Kuznetsov's problem is equivalent to
one of the \hopeless" complexity problems, namely \NP = PSPACE ?".
Complexity function
For a logic L with FMP, we introduce the complexity function

fL(n) = lmax
min jFj 
(') n F =L


j

'62L F6j='

where l('), the length of ', is the number of subformulas in ' and jFj the
number of points in F. If there is a constant c such that

fL (n)  2cn (or fL (n)  nc or fL(n)  c  n)
L is said to have the exponential (respectively, polynomial or linear) nite
model property. The following result shows that Int does not have polynomial FMP.
THEOREM 4.20 (Zakharyaschev and Popov 1979) log2 fInt(n) * n.

Proof The exponential upper bound is well known and to establish the
lower one it is sucient to use the formulas

n =

^ ((:pi ! qi ) _ (pi ! qi ) ! qi) ! (:p ! q ) _ (p ! q ):

n;1
i=1

+1

+1

+1

+1

1

1

1

1

It is not hard to see that n 2= Int and every refutation frame for n contains
the full binary tree of depth n as a subframe.
2
Likewise the same result can be proved for many other standard superintuitionistic and modal logics whose FMP is established by the usual ltration and whose frames contain full binary trees of arbitrary nite depth.
Such are, for instance, KC, SL, K4, S4, GL. In the case of K the length of

162

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

formulas that play the role ofpn is not a linear but a square function of n,
which means that fK (n) 2 cn , for some constant c > 0, and so K does
not have polynomial FMP either. As was shown in Zakharyaschev 1996],
all conal subframe modal and si-logics have exponential FMP. It seems
plausible that log2 fL(n) * n for every consistent si-logic L di erent from
Cl and axiomatizable by formulas in one variable.
The construction of Theorem 4.20 does not work for logics whose frames
do not contain arbitrarily large full binary trees. Such are, for instance,
logics of nite width or of nite depth, and the following was proved in
Chagrov 1983].
THEOREM 4.21 (i) The minimal logics of width n < ! in NExtK4, NExtS4,
NExtGrz, NExtGL, ExtInt have polynomial FMP.
(ii) Lin and all logics containing S4.3 have linear FMP.
(iii) The minimal logics of depth n in NExtGrz, NExtGL, ExtInt have
polynomial FMP, with the power of the corresponding polynomial  n ; 1.
(iv) The minimal logics of depth n in NExtK4, NExtS4 have polynomial
FMP, with the power of the corresponding polynomial  n.
Proof (i) is proved by two ltrations. First, with the help of the standard
ltration one constructs a nite frame separating a formula ' from the given
logic L and then, using the selective ltration, extracts from it a polynomial
separation frame: it suces to take a point refuting ' and all maximal
points at which  is false, for some 2 2 Sub' (in the intuitionistic case
 !  2 Sub' should be considered). (ii) is proved analogously.
To illustrate the proof of (iii) and (iv), we consider the minimal logic L of
depth 3 in NExtGL. Suppose ' 2= L. Then there is a transitive irreexive
model M of depth  3 refuting ' at its root r. Let 2i , for 1  i  m, be
all \boxed" subformulas of '. For every i 2 f1 : : :  mg, we choose a point
refuting i , if it exists. And then we do the same in the set x", for every
chosen point x. Let M0 be the submodel formed by the selected points and
r. Clearly, it contains at most 1 + m + m2 points. And by induction on the
construction of formulas in Sub' one can easily show that M0 refutes ' at
r.
To prove the lower bound one can use the formulas
n
n
^
^
n = :( 2(pi ! pi ) ^ 2(qi ! qi ) ^
i=1

+1

i=1

+1

^n 3(3> ^ 2 (:pi ^ pi)) ^ 2(3? ! ^n 3(:qi ^ qi)))
+

i=1

+1

i=1

+1

which are not in L and every separation frame for which contains the full
n-ary tree of depth 3, i.e., at least 1 + n + n2 points.
2

ADVANCED MODAL LOGIC

a1


a2

-

a3

-   

an


-

b1

-

163

b2

-   

bf (n)


Figure 20.
However, even if frames for a logic with FMP do not contain full nite
binary trees its complexity function can grow very fast, witness the following
result of Chagrov 1985a].
THEOREM 4.22 For every arithmetic function f (n), there are logics L of
width 1 in NExtK4 and of width 2 in ExtInt, NExtGrz, NExtGL having
FMP and such that fL (n) f (n).
Proof We construct a logic L 2 NExtK4:3 whose complexity function
grows faster than a given increasing arithmetic function f (n). Dene L to
be the logic of all frames of the form shown in Fig. 20. To see that L satises
the property we need, consider the sequence of formulas
1 = p1 _ 2(2p1 ! (2(2p ! p) ! p))
i+1 = pi+1 _ 2(2pi+1 ! i ):
Since these formulas are refuted at points of the form aj in suciently large
frames depicted in Fig. 20, they are not in L. And since L contains the
formulas
:n ! 3(3f (n);1> ^ 2f (n) ?)
n cannot be separated from L by a frame with  f (n) points.
2
For logics of nite depth this theorem does not hold, since according
to the description of nitely generated universal frames in Section 1.2, for
every L 2 NExtK4BDk (k 3), we have

fL (n)  22





2c n



k;2

for some constant c > 0. And as was shown in Chagrov 1985a], one cannot
in general reduce this upper bound.
THEOREM 4.23 For every k 3, there are logics L of depth k in NExtGrz,
NExtGL, ExtInt such that

fL(n) 22





2n



k;2 :

164

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

Proof We illustrate the proof for k = 3 in NExtGL. Let L be the logic
characterized by the class of rooted frames Fm for GL of depth 3 dened

as follows. Fm contains m dead ends, every non-empty set of them has a
focus, i.e., a point that sees precisely the dead ends in this set, and besides
the root there are no other points in Fm. It should be clear that L does not
contain the formulas

m =

^n 2(pi ! pi) ! ^n 22(pi ! pi ):
+1

i=1

+1

i=1

On the other hand n is not refutable in a frame for L with < 2m points
because the following formulas are in L:
:m !

^

X f1:::mgX 6=

3(

^ 3 i^ ^

i2X

where i = p1 ^ : : : ^ pi ^ :pi+1 ^ : : : ^ :pm+1 .

i62X1im

:3 i)

2

Note, however, that the logics constructed in the proofs of the last two
theorems are not nitely axiomatizable. We know of only one \very complex" calculus with FMP.
THEOREM 4.24 log2 log2 fKP (n) * n.
For the proof see Chagrov and Zakharyaschev 1997], where the reader
can nd also some other results in this direction.
Relation to complexity classes
Let us return to the original problem of optimizing decision algorithms for
the logics under consideration. First of all, it is to be noted that there is
a natural lower bound for decision algorithms which cannot be reduced|
we mean the complexity of decision procedures for Cl. This is clear for
(consistent) modal logics on the classical base and by Glivenko's Theorem,
every si-logic \contains" Cl in the form of the negated formulas. Thus,
if we manage to construct an e ective decision procedure for some of our
logics then Cl can be decided by an equally e ective algorithm. (We remind
the reader that all existing decision algorithms for Cl require exponential
time (of the number of variables in the tested formulas). On the other
hand, only polynomial time algorithms are regarded to be acceptable in
complexity theory.)
So, when analyzing the complexity of decision algorithms for modal and
si-logics, it is reasonable to compare them with decision algorithms for Cl.
For example, if a logic L is polynomially equivalent to Cl then we can regard

ADVANCED MODAL LOGIC

165

these two logics to be of the same complexity. Moreover, provided that
somebody nds a polynomial time decision procedure for Cl, a polynomial
time decision algorithm can be constructed for L as well. The following
theorem lists results obtained by Ladner 1977], Ono and Nakamura 1980],
Chagrov 1983], and Spaan 1993].
THEOREM 4.25 All logics mentioned in the formulation of Theorem 4.21
are polynomially equivalent to Cl.

Proof We illustrate the proof only for the minimal logic L of depth 3 in
NExtGL using the method of Kuznetsov 1979]. Suppose ' is a formula
of length n. By Theorem 4.21, the condition ' 62 L means that M 6j= ',
for some model M = hF Vi based on a frame F for GL of depth  3 and

cardinality  c  n2 . We describe this observation by means of classical
formulas, understanding their variables as follows. Let x, y, z be names
(numbers) of points in F, for 1  x y z  c  n2 . With every pair hx yi of
points in F we associate a variable pxy whose meaning is \x sees y". And
with every  2 Sub' and every x we associate a variable qx which means
\ is true at x". Denote by  the conjunction
q1' ^ q2' ^ : : : ^ qc'n2 :

It means that ' is true in M. And let  be the conjunction of the following
formulas under all possible values of their subscripts:
:pxx  pxy ^ pyz ! pxz  qx: $ :qx 

qx^ $ qx ^ qx 

qx_ $ qx _ qx 

qx2 $

^ (pxy ! q ):

cn2

y=1

y

(The rst two formulas say that R is irreexive and transitive and the rest
simulate the truth-relation in M.) Finally, we dene a formula saying that
our frame is of depth  3:

=

^

1xyzucn2

:(pxy ^ pyz ^ pzu ):

The formula  ^ ^: is of length  50(cn2)5 and can be clearly constructed
by an algorithm working at most linear time of the length of '. It is readily
seen that ' 62 L i  ^  ^: is satisable in Cl. Thus we have polynomially
reduced the derivability problem in L to that in Cl. Since the converse
reduction is trivial, L and Cl are polynomially equivalent.
2
The reader must have noticed that Theorem 4.25 lists almost all logics
known to have polynomial FMP. Kuznetsov 1975] conjectured that every

166

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

calculus having polynomial FMP is polynomially equivalent to Cl. This
conjecture is closely related to some problems in the complexity theory of
algorithms. We remind the reader that NP is the class of problems that
can be solved by polynomial time algorithms on nondeterministic (Turing)
machines. An NP -complete problem is a problem in NP to which all other
problems in NP are polynomially reducible. (For more detailed denitions
consult Garey and Johnson 1979].) The most popular NP -complete problem is the satisability problem for Boolean formulas, i.e., the nonderivability problem for Cl. So the nonderivability problem for all logics listed
Theorem 4.25 is NP -complete and Kuznetsov's conjecture is equivalent to
a positive solution to the problem whether the nonderivability problem for
every calculus with polynomial FMP is NP -complete.
Note that if coNP = NP (for the denition of the class coNP see
Garey and Johnson 1979] we just mention that the derivability problem
in Cl is coNP -complete) then Kuznetsov's conjecture does hold. But
since \coNP = NP ?" belongs to the list of \unsolvable" problems under the current state of knowledge, it may be of interest to nd out whether
Kuznetsov's conjecture implies coNP = NP .
Another complexity class we consider here is the class PSPACE of
problems that can be solved by polynomial space algorithms. A typical
example of a PSPACE -complete problem is the truth problem for quantied Boolean formulas. The following theorem (which summarizes results
obtained by Ladner 1977], Statman 1979], Chagrov 1985a], Halpern and
Moses 1992] and Spaan 1993]) lists some PSPACE -complete logics.
THEOREM 4.26 The nonderivability problem (and so the derivability problem) in the following logics is PSPACE -complete: Int, KC, K, K & K,
S4, S4 & S4, S5 & S5, GL, Grz, K:t and K4:t.
It follows in particular that complexity is not preserved under the formation of fusions of logics (under the assumption NP 6= PSPACE ),
since nonderivability in S5 is NP -complete. For more information on the
preservation of complexity under fusions consult Spaan 1993].
Finally we note that the nonderivability problem in logics with the universal modality or common knowledge operator is mostly even EXPTIME complete, witness Ku Spaan 1993] and S4EC2 Halpern and Moses 1992].
5 APPENDIX
We conclude this chapter with a (by no means complete) list of references for
those directions of research in modal logic that were not considered above:
 Congruential logics. These are modal logics that do not necessarily contain the distribution axiom 2(p ! q) ! (2p ! 2q) but are

ADVANCED MODAL LOGIC

167

closed under modus ponens and the congruence rule p $ q=2p $ 2q.
Segerberg 1971] and Chellas 1980] dene a semantics for these logics
Lewis 1974] proves FMP of all congruential non-iterative logics and
Surendonk 1996] shows that they are canonical. Do)sen 1988] considers duality between algebras and neighbourhood frames and Kracht
and Wolter 1997a] study embeddings into normal bimodal logics.
 Modal logics with graded modalities. The truth-relation for their possibility operators 3n is dened as follows: x j= 3np i there exist at
least n points accessible from x at which p holds. An early reference
is Fine 1972] more recent are van der Hoek 1992] (applications to
epistemic logic) and Cerrato 1994] (FMP and decidability).
 Modal logics with the dierence operator or with nominals (or names).
The semantics of nominals is similar to that of propositional variables
the di erence is that a nominal is true at exactly one point in a frame.
For the di erence operator 6=], we have x j= 6=]p i p is true everywhere except x. De Rijke 1993], Blackburn 1993] and Goranko and
Gargov 1993] study the completeness and expressive power of systems
of that sort. Closely related to the di erence operator is the modal
operator i] for inaccessible worlds: x j= i]p i p is true in all worlds
which are not accessible from x, see Humberstone 1983] and Goranko
1990a].
 Modal logics with dyadic or even polyadic operators. For duality theory
in this case see Goldblatt 1989]. An extensive study of Sahlqvisttype theorems with applications to polyadic logics is Venema 1991].
For connections with the theory of relational algebras see Mikulas
1995] and Marx 1995]. In those dissertations the reader can nd also
recent results on arrow logic, i.e., a certain type of polyadic logic which
is interpreted in Kripke frames built from arrows. An embedding
of polyadic logics into polymodal logics is discussed in Kracht and
Wolter 1997b].
 Bisimulations. Bisimulations were introduced in modal logic by van
Benthem 1983] to characterize its expressive power see also de Rijke
1996]. Visser 1996] used bisimulations to prove uniform interpolation.
Recently, bisimulations have attracted attention because they form a
common tool in modal logic and process theory. We refer the reader
to collection Ponse et al. 1996] for information on this subject.
 Modal logics with xed point operators, i.e., modal logics enriched by
operators forming the least and greatest xed points of monotone
formulas. These systems are also called modal -calculi. Under this

168

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

name they were introduced and studied by Kozen 1983, 1988] see
also Walukiewicz 1993, 1996] and Bosangue and Kwiatkowska 1996].
 Proof theory. Early references to studies of sequent calculi and natural
deduction systems for a few modal logics can be found in Basic Modal
Logic. More recently, (non-standard) sequent calculi for modal logics have been considered by Do)sen 1985b], Masini 1992] and Avron
1996] see also collection Wansing 1996] and the chapter Sequent
systems for modal logics in this Handbook. For natural deduction
systems see Borghuis 1993] tableau systems for modal and tense
logics were constructed in Fitting 1983], Rautenberg 1983], Gore
1994] and Kashima 1994]. Orlowska 1996] develops relational proof
systems. Display calculi for modal logics were introduced by Belnap
1982] see also Wansing 1994] and collection Wansing 1996].

REFERENCES
Amati and Pirri, 1994] G. Amati and F. Pirri. A uniform tableau method for intuitionistic modal logics I. Studia Logica, 53:29{60, 1994.
Anderson, 1972] J.G. Anderson. Superconstructive propositional calculi with extra axiom schemes containing one variable. Zeitschrift fur Mathematische Logik und Grundlagen der Mathematik, 18:113{130, 1972.
Avron, 1996] A. Avron. The method of hypersequents in the proof therory of propositional non-classical logics. In W. Hodges, M. Hyland, C. Steinhorn, and J. Truss,
editors, Logic: from Foundations to Applications, pages 1{32. Clarendon Press, Oxford, 1996.
Barwise and Moss, 1996] J. Barwise and L. Moss. Vicious Circles. CSLI Publications,
Stanford, 1996.
Beklemishev, 1994] L.D. Beklemishev. On bimodal logics of provability. Annals of Pure
and Applied Logic, 68:115{159, 1994.
Beklemishev, 1996] L.D. Beklemishev. Bimodal logics for extensions of arithmetical
theories. Journal of Symbolic Logic, 61:91{124, 1996.
Bellissima, 1984] F. Bellissima. Atoms in modal algebras. Zeitschrift fur Mathematische
Logik und Grundlagen der Mathematik, 30:303{312, 1984.
Bellissima, 1985] F. Bellissima. An eective representation for nitely generated free
interior algebras. Algebra Universalis, 20:302{317, 1985.
Bellissima, 1988] F. Bellissima. On the lattice of extensions of the modal logic K:Altn .
Archive of Mathematical Logic, 27:107{114, 1988.
Bellissima, 1991] F. Bellissima. Atoms of tense algebras. Algebra Universalis, 28:52{78,
1991.
Belnap, 1982] N.D. Belnap. Display logic. Journal of Philosophical Logic, 11:375{417,
1982.
Beth, 1953] E.W. Beth. On Padua's method in the theory of denitions. Indagationes
Mathematicae, 15:330{339, 1953.
Bezhanishvili, 1997] G. Bezhanishvili. Modal intuitionistic logics and superintuitionistic
predicate logics: correspondence theory. Manuscript, 1997.
Blackburn, 1993] P. Blackburn. Nominal tense logic. Notre Dame Journal of Formal
Logic, 34:56{83, 1993.
Blok and Kohler, 1983] W.J. Blok and P. Kohler. Algebraic semantics for quasi-classical
modal logics. Journal of Symbolic Logic, 48:941{964, 1983.

ADVANCED MODAL LOGIC

169

Blok and Pigozzi, 1982] W. Blok and D. Pigozzi. On the structure of varieties with
equationally denable principal congruences I. Algebra Universalis, 15:195{227, 1982.
Blok, 1976] W.J. Blok. Varieties of interior algebras. PhD thesis, University of Amsterdam, 1976.
Blok, 1978] W.J. Blok. On the degree of incompleteness in modal logics and the covering relation in the lattice of modal logics. Technical Report 78-07, Department of
Mathematics, University of Amsterdam, 1978.
Blok, 1980a] W.J. Blok. The lattice of modal algebras is not strongly atomic. Algebra
Universalis, 11:285{294, 1980.
Blok, 1980b] W.J. Blok. The lattice of modal logics: an algebraic investigation. Journal
of Symbolic Logic, 45:221{236, 1980.
Blok, 1980c] W.J. Blok. Pretabular varieties of modal algebras. Studia Logica, 39:101{
124, 1980.
Boolos, 1993] G. Boolos. The Logic of Provability. Cambridge University Press, 1993.
Borghuis, 1993] T. Borghuis. Interpreting modal natural deduction in type theory. In
M. de Rijke, editor, Diamonds and Defaults, pages 67{102. Kluwer Academic Publishers, 1993.
Bosangue and Kwiatkowska, 1996] M. Bosangue and M. Kwiatkowska. Re-interpreting
the modal -calculus. In A. Ponse, M. de Rijke, and Y. Venema, editors, Modal Logic
and Process Algebra, pages 65{83. CSLI publications, Stanford, 1996.
Bozic and Dosen, 1984] M. Bozic and K. Dosen. Models for normal intuitionistic logics.
Studia Logica, 43:217{245, 1984.
Buchi and Siefkes, 1973] J.R. Buchi and D. Siefkes. The monadic second order theory
of all countable ordinals. Number 328 in Lecture Notes in Mathematics. Springer,
1973.
Buchi, 1962] J.R. Buchi. On a decision method in restricted second order arithmetic. In
Logic, Methodology and Philosophy of Science: Proceedings of the 1960 International
Congress, pages 1{11. Stanford University Press, 1962.
Bull, 1966a] R.A. Bull. MIPC as the formalization of an intuitionistic concept of
modality. Journal of Symbolic Logic, 31:609{616, 1966.
Bull, 1966b] R.A. Bull. That all normal extensions of S 4:3 have the nite model property. Zeitschrift fur Mathematische Logik und Grundlagen der Mathematik, 12:341{
344, 1966.
Bull, 1968] R.A. Bull. An algebraic study of tense logic with linear time. Journal of
Symbolic Logic, 33:27{38, 1968.
Cerrato, 1994] C. Cerrato. Decidability by ltrations for graded normal logics. Studia
Logica, 53:61{73, 1994.
Chagrov and Chagrova, 1995] A.V. Chagrov and L.A. Chagrova. Algorithmic problems
concerning rst order denability of modal formulas on the class of all nite frames.
Studia Logica, 55:421{448, 1995.
Chagrov and Zakharyaschev, 1991] A.V. Chagrov and M.V. Zakharyaschev. The disjunction property of intermediate propositional logics. Studia Logica, 50:63{75, 1991.
Chagrov and Zakharyaschev, 1992] A.V. Chagrov and M.V. Zakharyaschev. Modal
companions of intermediate propositional logics. Studia Logica, 51:49{82, 1992.
Chagrov and Zakharyaschev, 1993] A.V. Chagrov and M.V. Zakharyaschev. The undecidability of the disjunction property of propositional logics and other related problems. Journal of Symbolic Logic, 58:49{82, 1993.
Chagrov and Zakharyaschev, 1995a] A.V. Chagrov and M.V. Zakharyaschev. On the
independent axiomatizability of modal and intermediate logics. Journal of Logic and
Computation, 5:287{302, 1995.
Chagrov and Zakharyaschev, 1995b] A.V. Chagrov and M.V. Zakharyaschev. Sahlqvist
formulas are not so elementary even above S 4. In L. Csirmaz, D.M. Gabbay, and
M. de Rijke, editors, Logic Colloquium'92, pages 61{73. CSLI Publications, Stanford,
1995.
Chagrov and Zakharyaschev, 1997] A.V. Chagrov and M.V. Zakharyaschev. Modal
Logic. Oxford University Press, 1997.

170

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

Chagrov, 1983] A.V. Chagrov. On the polynomial approximability of modal and superintuitionistic logics. In Mathematical Logic, Mathematical Linguistics and Algorithm
Theory, pages 75{83. Kalinin State University, Kalinin, 1983. (Russian).
Chagrov, 1985a] A.V. Chagrov. On the complexity of propositional logics. In Complexity Problems in Mathematical Logic, pages 80{90. Kalinin State University, Kalinin,
1985. (Russian).
Chagrov, 1985b] A.V. Chagrov. Varieties of logical matrices. Algebra and Logic, 24:278{
325, 1985.
Chagrov, 1989] A.V. Chagrov. Nontabularity|pretabularity, antitabularity, coantitabularity. In Algebraic and Logical Constructions, pages 105{111. Kalinin State
University, Kalinin, 1989. (Russian).
Chagrov, 1990a] A.V. Chagrov. Undecidability of the nitary semantical consequence.
In Proceedings of the XXth USSR Conference on Mathematica Logic, Alma-Ata, page
162, 1990. (Russian).
Chagrov, 1990b] A.V. Chagrov. Undecidable properties of extensions of provability
logic. I. Algebra and Logic, 29:231{243, 1990.
Chagrov, 1990c] A.V. Chagrov. Undecidable properties of extensions of provability
logic. II. Algebra and Logic, 29:406{413, 1990.
Chagrov, 1992a] A.V. Chagrov. Continuality of the set of maximal superintuitionistic
logics with the disjunction property. Mathematical Notes, 51:188{193, 1992.
Chagrov, 1992b] A.V. Chagrov. A decidable modal logic with the undecidable admissibility problem for inference rules. Algebra and Logic, 31:53{55, 1992.
Chagrov, 1994] A.V. Chagrov. Undecidable properties of superintuitionistic logics. In
S.V. Jablonskij, editor, Mathematical Problems of Cybernetics, volume 5, pages 67{
108. Physmatlit, Moscow, 1994. (Russian).
Chagrov, 1995] A.V. Chagrov. One more rst-order eect in Kripke semantics. In
Proceedings of the 10th International Congress of Logic, Methodology and Philosophy
of Science, page 124, Florence, Italy, 1995.
Chagrov, 1996] A.V. Chagrov. Tabular modal logics: algorithmic problems.
Manuscript, 1996.
Chagrova, 1986] L.A. Chagrova. On the rst order denability of intuitionistic formulas with restrictions on occurrences of the connectives. In M.I. Kanovich, editor,
Logical Methods for Constructing E ective Algorithms, pages 135{136. Kalinin State
University, Kalinin, 1986. (Russian).
Chagrova, 1989] L.A. Chagrova. On the problem of de nability of propositional formulas of intuitionistic logic by formulas of classical rst order logic. PhD thesis, Kalinin
State University, 1989. (Russian).
Chagrova, 1990] L.A. Chagrova. On the preservation of rst order properties under the
embedding of intermediate logics into modal logics. In Proceedings of the Xth USSR
Conference for Mathematical Logic, page 163, 1990. (Russian).
Chagrova, 1991] L.A. Chagrova. An undecidable problem in correspondence theory.
Journal of Symbolic Logic, 56:1261{1272, 1991.
Chellas and Segerberg, 1994] B. Chellas and K. Segerberg. Modal logics with the
MacIntosh-rule. Journal of Philosophical Logic, 23:67{86, 1994.
Chellas, 1980] B.F. Chellas. Modal Logic: An Introduction. Cambridge University
Press, 1980.
Craig, 1953] W. Craig. On axiomatizability within a system. Journal of Symbolic Logic,
18:30{32, 1953.
Craig, 1957] W. Craig. Three uses of the Herbrandt{Gentzen theorem in relating model
theory and proof theory. Journal of Symbolic Logic, 22:269{285, 1957.
Cresswell, 1984] M.J. Cresswell. An incomplete decidable modal logic. Journal of Symbolic Logic, 49:520{527, 1984.
Day, 1977] A. Day. Splitting lattices generate all lattices. Algebra Universalis, 7:163{
170, 1977.
de Rijke, 1993] M. de Rijke. Extending Modal Logic. PhD thesis, Universiteit van
Amsterdam, 1993.

ADVANCED MODAL LOGIC

171

de Rijke, 1996] M. de Rijke. A Lindstrom theorem for modal logic. In A. Ponse,
M. de Rijke, and Y. Venema, editors, Modal Logic and Process Algebra, pages 217{230.
CSLI Publications, Stanford, 1996.
Diego, 1966] A. Diego. Sur les algebres de Hilbert. Gauthier-Villars, Paris, 1966.
Doets, 1987] K. Doets. Completeness and de nability. PhD thesis, Universiteit van
Amsterdam, 1987.
Dosen, 1985a] K. Dosen. Models for stronger normal intuitionistic modal logics. Studia
Logica, 44:39{70, 1985.
Dosen, 1985b] K. Dosen. Sequent-systems for modal logic. Journal of Symbolic Logic,
50:149{159, 1985.
Dosen, 1988] K. Dosen. Duality between modal algebras and neighbourhood frames.
Studia Logica, 48:219{234, 1988.
Drabbe, 1967] J. Drabbe. Une propriete des matrices caracteristiques des systemes S 1,
S 2, et S 3. Comptes Rendus de l'Academie des Sciences, Paris, 265:A1, 1967.
Dugundji, 1940] J. Dugundji. Note on a property of matrices for Lewis and Langford's
calculi of propositions. Journal of Symbolic Logic, 5:150{151, 1940.
Dummett and Lemmon, 1959] M.A.E. Dummett and E.J. Lemmon. Modal logics between S 4 and S 5. Zeitschrift fur Mathematische Logik und Grundlagen der Mathematik, 5:250{264, 1959.
Dummett, 1959] M.A.E. Dummett. A propositional calculus with denumerable matrix.
Journal of Symbolic Logic, 24:97{106, 1959.
Ershov, 1980] Yu.L. Ershov. Decision problems and constructive models. Nauka,
Moscow, 1980. (Russian).
Esakia and Meskhi, 1977] L.L. Esakia and V.Yu. Meskhi. Five critical systems. Theoria, 40:52{60, 1977.
Esakia, 1974] L.L. Esakia. Topological Kripke models. Soviet Mathematics Doklady,
15:147{151, 1974.
Esakia, 1979a] L.L. Esakia. On varieties of Grzegorczyk algebras. In A. I. Mikhailov, editor, Studies in Non-classical Logics and Set Theory, pages 257{287. Moscow, Nauka,
1979. (Russian).
Esakia, 1979b] L.L. Esakia. To the theory of modal and superintuitionistic systems. In
V.A. Smirnov, editor, Logical Inference. Proceedings of the USSR Symposium on the
Theory of Logical Inference, pages 147{172. Nauka, Moscow, 1979. (Russian).
Ewald, 1986] W.B. Ewald. Intuitionistic tense and modal logic. Journal of Symbolic
Logic, 51:166{179, 1986.
Ferrari and Miglioli, 1993] M. Ferrari and P. Miglioli. Counting the maximal intermediate constructive logics. Journal of Symbolic Logic, 58:1365{1408, 1993.
Ferrari and Miglioli, 1995a] M. Ferrari and P. Miglioli. A method to single out maximal
propositional logics with the disjunction property. I. Annals of Pure and Applied Logic,
76:1{46, 1995.
Ferrari and Miglioli, 1995b] M. Ferrari and P. Miglioli. A method to single out maximal
propositional logics with the disjunction property. II. Annals of Pure and Applied
Logic, 76:117{168, 1995.
Fine and Schurz, 1996] K. Fine and G. Schurz. Transfer theorems for stratied modal
logics. In J. Copeland, editor, Logic and Reality, Essays in Pure and Applied Logic.
In memory of Arthur Prior, pages 169{213. Oxford University Press, 1996.
Fine, 1971] K. Fine. The logics containing S 4:3. Zeitschrift fur Mathematische Logik
und Grundlagen der Mathematik, 17:371{376, 1971.
Fine, 1972] K. Fine. In so many possible worlds. Notre Dame Journal of Formal Logic,
13:516{520, 1972.
Fine, 1974a] K. Fine. An ascending chain of S 4 logics. Theoria, 40:110{116, 1974.
Fine, 1974b] K. Fine. An incomplete logic containing S 4. Theoria, 40:23{29, 1974.
Fine, 1974c] K. Fine. Logics containing K 4, part I. Journal of Symbolic Logic, 39:229{
237, 1974.
Fine, 1975a] K. Fine. Normal forms in modal logic. Notre Dame Journal of Formal
Logic, 16:31{42, 1975.

172

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

Fine, 1975b] K. Fine. Some connections between elementary and modal logic. In
S. Kanger, editor, Proceedings of the Third Scandinavian Logic Symposium, pages
15{31. North-Holland, Amsterdam, 1975.
Fine, 1985] K. Fine. Logics containing K 4, part II. Journal of Symbolic Logic, 50:619{
651, 1985.
Fischer-Servi, 1977] G. Fischer-Servi. On modal logics with an intuitionistic base. Studia Logica, 36:141{149, 1977.
Fischer-Servi, 1980] G. Fischer-Servi. Semantics for a class of intuitionistic modal calculi. In M. L. Dalla Chiara, editor, Italian Studies in the Philosophy of Science, pages
59{72. Reidel, Dordrecht, 1980.
Fischer-Servi, 1984] G. Fischer-Servi. Axiomatizations for some intuitionistic modal
logics. Rend. Sem. Mat. Univers. Polit., 42:179{194, 1984.
Fitting, 1983] M. Fitting. Proof Methods for Modal and Intuitionistic Logics. Reidel,
Dordrecht, 1983.
Font, 1984] J. Font. Implication and deduction in some intuitionistic modal logics.
Reports on Mathematical logic, 17:27{38, 1984.
Font, 1986] J. Font. Modality and possibility in some intuitionistic modal logics. Notre
Dame Journal of Formal Logic, 27:533{546, 1986.
Friedman, 1975] H. Friedman. One hundred and two problems in mathematical logic.
Journal of Symbolic Logic, 40:113{130, 1975.
Fuhrmann, 1989] A. Fuhrmann. Models for relevant modal logics. Studia Logica,
49:502{514, 1989.
Gabbay and de Jongh, 1974] D.M. Gabbay and D.H.J. de Jongh. A sequence of decidable nitely axiomatizable intermediate logics with the disjunction property. Journal
of Symbolic Logic, 39:67{78, 1974.
Gabbay et al., 1994] D. Gabbay, I. Hodkinson, and M. Reynolds. Temporal Logic:
Mathematical Foundations and Computational Aspects, Volume 1. Oxford University Press, 1994.
Gabbay, 1970] D.M. Gabbay. The decidability of the Kreisel{Putnam system. Journal
of Symbolic Logic, 35:431{436, 1970.
Gabbay, 1971] D.M. Gabbay. On decidable, nitely axiomatizable modal and tense
logics without the nite model property. I, II. Israel Journal of Mathematics, 10:478{
495, 496{503, 1971.
Gabbay, 1972] D.M. Gabbay. Craig's interpolation theorem for modal logics. In
W. Hodges, editor, Proceedings of logic conference, London 1970, volume 255 of Lecture Notes in Mathematics, pages 111{127. Springer-Verlag, Berlin, 1972.
Gabbay, 1975] D.M. Gabbay. Decidability results in non-classical logics. Annals of
Mathematical Logic, 8:237{295, 1975.
Gabbay, 1976] D.M. Gabbay. Investigations into Modal and Tense Logics, with Applications to Problems in Linguistics and Philosophy. Reidel, Dordrecht, 1976.
Gabbay, 1981a] D.M. Gabbay. An irreexivity lemma with application to axiomatizations of conditions on linear frames. In U. Monnich, editor, Aspects of Philosophical
Logic, pages 67{89. Reidel, Dordrecht, 1981.
Gabbay, 1981b] D.M. Gabbay. Semantical Investigations in Heyting's Intuitionistic
Logic. Reidel, Dordrecht, 1981.
Galanter, 1990] G.I. Galanter. A continuum of intermediate logics which are maximal
among the logics having the intuitionistic disjunctionless fragment. In Proceedings of
10th USSR Conference for Mathematical Logic, page 41, Alma{Ata, 1990. (Russian).
Garey and Johnson, 1979] M.R. Garey and D.S. Johnson. Computers and intractability. A guide to the theory of NP-completeness. Freemann, San Franzisco, 1979.
Gargov and Passy, 1990] G. Gargov and S. Passy. A note on Boolean modal logic. In
P. Petkov, editor, Mathematical Logic, pages 299{309. Plenum Press, 1990.
Gargov et al., 1987] G. Gargov, S. Passy, and T. Tinchev. Modal environment for
Boolean speculations. In D. Skordev, editor, Mathematical Logic and its Applications,
pages 253{263. Plenum Press, 1987.

ADVANCED MODAL LOGIC

173

Gentzen, 1934{35] G. Gentzen. Untersuchungen uber das logische Schliessen. Mathematische Zeitschrift, 39:176{210, 405{431, 1934{35.
Ghilardi and Meloni, 1997] S. Ghilardi and G. Meloni. Constructive canonicity in nonclassical logics. Annals of Pure and Applied Logic, 1997. To appear.
Ghilardi and Zawadowski, 1995] S. Ghilardi and M. Zawadowski. Undenability of
propositional quantiers in modal system S 4. Studia Logica, 55:259{271, 1995.
Ghilardi, 1995] S. Ghilardi. An algebraic theory of normal forms. Annals of Pure and
Applied Logic, 71:189{245, 1995.
Godel, 1932] K. Godel. Zum intuitionistischen Aussagenkalkul. Anzeiger der Akademie
der Wissenschaften in Wien, 69:65{66, 1932.
Godel, 1933] K. Godel. Eine Interpretation des intuitionistischen Aussagenkalkuls.
Ergebnisse eines mathematischen Kolloquiums, 4:39{40, 1933.
Goldblatt and Thomason, 1974] R.I. Goldblatt and S.K. Thomason. Axiomatic classes
in propositional modal logic. In J. Crossley, editor, Algebraic Logic, Lecture Notes in
Mathematics vol. 450, pages 163{173. Springer, Berlin, 1974.
Goldblatt, 1976a] R.I. Goldblatt. Metamathematics of modal logic, Part I. Reports on
Mathematical Logic, 6:41{78, 1976.
Goldblatt, 1976b] R.I. Goldblatt. Metamathematics of modal logic, Part II. Reports
on Mathematical Logic, 7:21{52, 1976.
Goldblatt, 1987] R.I. Goldblatt. Logics of Time and Computation. Number 7 in CSLI
Lecture Notes, Stanford. CSLI, 1987.
Goldblatt, 1989] R.I. Goldblatt. Varieties of complex algebras. Annals of Pure and
Applied Logic, 38:173{241, 1989.
Goldblatt, 1995] R.I. Goldblatt. Elementary generation and canonicity for varieties of
boolean algebras with operators. Algebra Universalis, 34:551{607, 1995.
Goranko and Gargov, 1993] V. Goranko and G. Gargov. Modal logic with names. Journal of Philosophical Logic, 22:607{636, 1993.
Goranko and Passy, 1992] V. Goranko and S. Passy. Using the universal modality:
Gains and questions. Journal of Logic and Computation, 2:5{30, 1992.
Goranko, 1990a] V. Goranko. Completeness and incompleteness in the bimodal base
L(R ;R). In P. Petkov, editor, Mathematical Logic, pages 311{326. Plenum Press,
1990.
Goranko, 1990b] V. Goranko. Modal denability in enriched languages. Notre Dame
Journal of Formal Logic, 31:81{105, 1990.
Gore, 1994] R. Gore. Cut-free sequent and tableau systems for propositional Diodorian
modal logics. Studia Logica, 53:433{458, 1994.
Grefe, 1994] C. Grefe. Modale Logiken funktionaler Frames. Master's thesis, Department of Mathematics, Freie Universitat Berlin, 1994.
Grefe, 1997] C. Grefe. Fischer Servi's intuitionistic modal logic has the nite model
property. In M. Kracht, M. De Rijke, H. Wansing, and M. Zakharyaschev, editors,
Advances in Modal Logic. CSLI, Stanford, 1997.
Halpern and Moses, 1992] J. Halpern and Yo. Moses. A guide to completeness and
complexity for modal logics of knowledge and belief. Arti cial Intelligence, 54:319{
379, 1992.
Harrop, 1958] R. Harrop. On the existence of nite models and decision procedures for
propositional calculi. Proceedings of the Cambridge Philosophical Society, 54:1{13,
1958.
Hemaspaandra, 1996] E. Hemaspaandra. The price of universality. Notre Dame Journal
of Formal Logic, 37:174{203, 1996.
Hosoi and Ono, 1973] T. Hosoi and H. Ono. Intermediate propositional logics (A survey). Journal of Tsuda College, 5:67{82, 1973.
Hosoi, 1967] T. Hosoi. On intermediate logics. Journal of the Faculty of Science,
University of Tokyo, 14:293{312, 1967.
Hughes and Cresswell, 1984] G.E. Hughes and M.J. Cresswell. A Companion to Modal
Logic. Methuen, London, 1984.

174

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

Humberstone, 1983] I.L. Humberstone. Inaccessible worlds. Notre Dame Journal of
Formal Logic, 24:346{352, 1983.
Isard, 1977] S. Isard. A nitely axiomatizable undecidable extension of K . Theoria,
43:195{202, 1977.
Janiczak, 1953] A. Janiczak. Undecidability of some simple formalized theories. Fundamenta Mathematicae, 40:131{139, 1953.
Jankov, 1963] V.A. Jankov. The relationship between deducibility in the intuitionistic
propositional calculus and nite implicational structures. Soviet Mathematics Doklady, 4:1203{1204, 1963.
Jankov, 1968a] V.A. Jankov. The calculus of the weak \law of excluded middle". Mathematics of the USSR, Izvestiya, 2:997{1004, 1968.
Jankov, 1968b] V.A. Jankov. The construction of a sequence of strongly independent superintuitionistic propositional calculi. Soviet Mathematics Doklady, 9:806{807, 1968.
Jankov, 1969] V.A. Jankov. Conjunctively indecomposable formulas in propositional
calculi. Mathematics of the USSR, Izvestiya, 3:17{35, 1969.
Jaskowski, 1936] S. Jaskowski. Recherches sur le systeme de la logique intuitioniste. In
Actes Du Congres Intern. De Phil. Scienti que. VI. Phil. Des Mathematiques, Act.
Sc. Et Ind 393, Paris, pages 58{61, 1936.
Jipsen and Rose, 1993] P. Jipsen and H. Rose. Varieties of Lattices. 1993.
Jonsson and Tarski, 1951] B. Jonsson and A. Tarski. Boolean algebras with operators.
I. American Journal of Mathematics, 73:891{939, 1951.
Jonsson, 1994] B. Jonsson. On the canonicity of Sahlqvist identities. Studia Logica,
53:473{491, 1994.
Kashima, 1994] R. Kashima. Cut-free sequent calculi for some tense logics. Studia
Logica, 53:119{136, 1994.
Kirk, 1982] R.E. Kirk. A result on propositional logics having the disjunction property.
Notre Dame Journal of Formal Logic, 23:71{74, 1982.
Kleene, 1945] S. Kleene. On the interpretation of intuitionistic number theory. Journal
of Symbolic Logic, 10:109{124, 1945.
Kleyman, 1984] Yu.G. Kleyman. Some questions in the theory of varieties of groups.
Mathematics of the USSR, Izvestiya, 22:33{65, 1984.
Koppelberg, 1988] S. Koppelberg. General theory of Boolean algebras. In J. Monk,
editor, Handbook of Boolean Algebras, volume 1. North-Holland, Amsterdam, 1988.
Kozen, 1983] D. Kozen. Results on the propositional -calculus. Theoretical Computer
Science, 27:333{354, 1983.
Kozen, 1988] D. Kozen. A nite model theorem for the propositional -calculus. Studia
Logica, 47:234{241, 1988.
Kracht and Wolter, 1991] M. Kracht and F. Wolter. Properties of independently axiomatizable bimodal logics. Journal of Symbolic Logic, 56:1469{1485, 1991.
Kracht and Wolter, 1997a] M. Kracht and F. Wolter. Normal monomodal logics can
simulate all others. Journal of Symbolic Logic, 1997. To appear.
Kracht and Wolter, 1997b] M. Kracht and F. Wolter. Simulation and transfer results
in modal logic: A survey. Studia Logica, 1997. To appear.
Kracht, 1990] M. Kracht. An almost general splitting theorem for modal logic. Studia
Logica, 49:455{470, 1990.
Kracht, 1992] M. Kracht. Even more about the lattice of tense logics. Archive of
Mathematical Logic, 31:243{357, 1992.
Kracht, 1993] M. Kracht. How completeness and correspondence theory got married.
In M. de Rijke, editor, Diamonds and Defaults, pages 175{214. Kluwer Academic
Publishers, 1993.
Kracht, 1996] M. Kracht. Tools and techniques in modal logic. Habilitationsschrift, FU
Berlin, 1996.
Kreisel and Putnam, 1957] G. Kreisel and H. Putnam. Eine Unableitbarkeitsbeweismethode fur den intuitionistischen Aussagenkalkul. Zeitschrift fur Mathematische
Logik und Grundlagen der Mathematik, 3:74{78, 1957.

ADVANCED MODAL LOGIC

175

Kruskal, 1960] J. B. Kruskal. Well-quasi-ordering, the tree theorem and Vazsonyi's
conjecture. Transactions of the American Mathematical Society, 95:210{225, 1960.
Kuznetsov and Gerchiu, 1970] A.V. Kuznetsov and V.Ya. Gerchiu. Superintuitionistic
logics and the nite approximability. Soviet Mathematics Doklady, 11:1614{1619,
1970.
Kuznetsov, 1963] A.V. Kuznetsov. Undecidability of general problems of completeness,
decidability and equivalence for propositional calculi. Algebra and Logic, 2:47{66,
1963. (Russian).
Kuznetsov, 1971] A.V. Kuznetsov. Some properties of the structure of varieties of
pseudo-Boolean algebras. In Proceedings of the XIth USSR Algebraic Colloquium,
pages 255{256, Kishinev, 1971. (Russian).
Kuznetsov, 1972] A.V. Kuznetsov. The decidability of certain superintuitionistic calculi. In Proceedings of the IInd USSR Conference on Mathematical Logic, Moscow,
1972. (Russian).
Kuznetsov, 1975] A.V. Kuznetsov. On superintuitionistic logics. In Proceedings of the
International Congress of Mathematicians, pages 243{249, Vancouver, 1975.
Kuznetsov, 1979] A.V. Kuznetsov. Tools for detecting non-derivability or nonexpressibility. In V.A. Smirnov, editor, Logical Inference. Proceedings of the USSR
Symposium on the Theory of Logical Inference, pages 5{23. Nauka, Moscow, 1979.
(Russian).
Kuznetsov, 1985] A.V. Kuznetsov. Proof-intuitionistic propositional calculus. Doklady
Academii Nauk SSSR, 283:27{30, 1985. (Russian).
Ladner, 1977] R.E. Ladner. The computational complexity of provability in systems of
modal logic. SIAM Journal on Computing, 6:467{480, 1977.
Lemmon and Scott, 1977] E.J. Lemmon and D.S. Scott. An Introduction to Modal
Logic. Oxford, Blackwell, 1977.
Lemmon, 1966a] E.J. Lemmon. Algebraic semantics for modal logic. I. Journal of
Symbolic Logic, 31:46{65, 1966.
Lemmon, 1966b] E.J. Lemmon. Algebraic semantics for modal logic. II. Journal of
Symbolic Logic, 31:191{218, 1966.
Lemmon, 1966c] E.J. Lemmon. A note on Hallden-incompleteness. Notre Dame Journal
of Formal Logic, 7:296{300, 1966.
Levin, 1969] V.A. Levin. Some syntactic theorems on the calculus of nite problems of
Yu.T. Medvedev. Soviet Mathematics Doklady, 10:288{290, 1969.
Lewis, 1918] C.I. Lewis. A Survey of Symbolic Logic. University of California Press,
Berkeley, 1918.
Lewis, 1974] D. Lewis. Intensional logics without iterative axioms. Journal of Philosophical logic, 3:457{466, 1974.
Lincoln et al., 1992] P.D. Lincoln, J. Mitchell, A. Scedrov, and N. Shankar. Decision
problems for propositional linear logic. Annals of Pure and Applied Logic, 56:239{311,
1992.
Lukasiewicz, 1952] J. Lukasiewicz. On the intuitionistic theory of deduction. Indagationes Mathematicae, 14:202{212, 1952.
Luppi, 1996] C. Luppi. On the interpolation property of some intuitionistic modal
logics. Archive for Mathematical Logic, 35:173{189, 1996.
Makinson, 1971] D.C. Makinson. Some embedding theorems for modal logic. Notre
Dame Journal of Formal Logic, 12:252{254, 1971.
Maksimova and Rybakov, 1974] L.L. Maksimova and V.V. Rybakov. Lattices of modal
logics. Algebra and Logic, 13:105{122, 1974.
Maksimova et al., 1979] L.L. Maksimova, V.B. Shehtman, and D.P. Skvortsov. The
impossibility of a nite axiomatization of Medvedev's logic of nitary problems. Soviet
Mathematics Doklady, 20:394{398, 1979.
Maksimova, 1972] L.L. Maksimova. Pretabular superintuitionistic logics. Algebra and
Logic, 11:308{314, 1972.
Maksimova, 1975a] L.L. Maksimova. Modal logics of nite slices. Algebra and Logic,
14:188{197, 1975.

176

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

Maksimova, 1975b] L.L. Maksimova. Pretabular extensions of Lewis S 4. Algebra and
Logic, 14:16{33, 1975.
Maksimova, 1979] L.L. Maksimova. Interpolation theorems in modal logic and amalgamable varieties of topological Boolean algebras. Algebra and Logic, 18:348{370,
1979.
Maksimova, 1982a] L.L. Maksimova. Failure of the interpolation property in modal
companions of Dummett's logic. Algebra and Logic, 21:690{694, 1982.
Maksimova, 1982b] L.L. Maksimova. Lyndon's interpolation theorem in modal logics.
In Mathematical Logic and Algorithm Theory, pages 45{55. Institute of Mathematics,
Novosibirsk, 1982. (Russian).
Maksimova, 1984] L.L. Maksimova. On the number of maximal intermediate logics
having the disjunction property. In Proceedings of the 7th USSR Conference for
Mathematical Logic, page 95. Institute of Mathematics, Novosibirsk, 1984. (Russian).
Maksimova, 1986] L.L. Maksimova. On maximal intermediate logics with the disjunction property. Studia Logica, 45:69{75, 1986.
Maksimova, 1987] L.L. Maksimova. On the interpolation in normal modal logics. Nonclassical Logics, Studies in Mathematics, 98:40{56, 1987. (Russian).
Maksimova, 1989] L.L. Maksimova. A continuum of normal extensions of the modal
provability logic with the interpolation property. Sibirskij Matematiceskij Zurnal,
30:122{131, 1989. (Russian).
Maksimova, 1992] L.L. Maksimova. Denability and interpolation in classical modal
logics. Contemporary Mathematics, 131:583{599, 1992.
Maksimova, 1995] L.L. Maksimova. On variable separation in modal and superintuitionistic logics. Studia Logica, 55:99{112, 1995.
Mal'cev, 1970] A.I. Mal'cev. Algorithms and Recursive Functions. Wolters-Noordho,
Groningen, 1970.
Mal'cev, 1973] A.I. Mal'cev. Algebraic Systems. Springer-Verlag, Berlin-Heidelberg,
1973.
Mardaev, 1984] S.I. Mardaev. The number of prelocally tabular superintuitionistic
propositional logics. Algebra and Logic, 23:56{66, 1984.
Marx, 1995] M. Marx. Algebraic relativization and arrow logic. PhD thesis, University
of Amsterdam, 1995.
Masini, 1992] A. Masini. 2-sequent calculus: a proof theory of modality. Annals of
Pure and Applied Logic, 58:229{246, 1992.
Matiyasevich, 1967] Y.V. Matiyasevich. Simple examples of undecidable associative
calculi. Soviet Mathematics Doklady, 8:555{557, 1967.
McKay, 1968] C.G. McKay. The decidability of certain intermediate logics. Journal of
Symbolic Logic, 33:258{264, 1968.
McKay, 1971] C.G. McKay. A class of decidable intermediate propositional logics. Journal of Symbolic Logic, 36:127{128, 1971.
McKenzie, 1972] R. McKenzie. Equational bases and non-modular lattice varieties.
Transactions of the American Mathematical Society, 174:1{43, 1972.
McKinsey and Tarski, 1946] J.C.C. McKinsey and A. Tarski. On closed elements in
closure algebras. Annals of Mathematics, 47:122{162, 1946.
McKinsey and Tarski, 1948] J.C.C. McKinsey and A. Tarski. Some theorems about the
sentential calculi of Lewis and Heyting. Journal of Symbolic Logic, 13:1{15, 1948.
McKinsey, 1941] J.C.C. McKinsey. A solution of the decision problem for the Lewis
systems S 2 and S 4, with an application to topology. Journal of Symbolic Logic,
6:117{134, 1941.
Medvedev, 1962] Yu.T. Medvedev. Finite problems. Soviet Mathematics Doklady,
3:227{230, 1962.
Medvedev, 1966] Yu.T. Medvedev. Interpretation of logical formulas by means of nite
problems. Soviet Mathematics Doklady, 7:857{860, 1966.
Meyer and van der Hoek, 1995] J. Meyer and W. van der Hoek. Epistemic Logic for
AI and Computer Science. Cambridge University Press, 1995.
Mikulas, 1995] S. Mikulas. Taming Logics. PhD thesis, University of Amsterdam, 1995.

ADVANCED MODAL LOGIC

177

Minari, 1986] P. Minari. Intermediate logics with the same disjunctionless fragment as
intuitionistic logic. Studia Logica, 45:207{222, 1986.
Montagna, 1987] F. Montagna. Provability in nite subtheories of PA and relative
interpretability: a modal investigation. Journal of Symbolic Logic, 52:494{511, 1987.
Morikawa, 1989] O. Morikawa. Some modal logics based on three-valued logic. Notre
Dame Journal of Formal Logic, 30:130{137, 1989.
Muravitskij, 1981] A.Yu. Muravitskij. On nite approximability of the calculus I 4 and
non-modelability of some of its extensions. Mathematical Notes, 29:907{916, 1981.
Nagle and Thomason, 1985] M.C. Nagle and S.K. Thomason. The extensions of the
modal logic K 5. Journal of Symbolic Logic, 50:102{108, 1985.
Nishimura, 1960] I. Nishimura. On formulas of one variable in intuitionistic propositional calculus. Journal of Symbolic Logic, 25:327{331, 1960.
Ono and Nakamura, 1980] H. Ono and A. Nakamura. On the size of refutation Kripke
models for some linear modal and tense logics. Studia Logica, 39:325{333, 1980.
Ono and Suzuki, 1988] H. Ono and N. Suzuki. Relations between intuitionistic modal
logics and intermediate predicate logics. Reports on Mathematical Logic, 22:65{87,
1988.
Ono, 1972] H. Ono. Some results on the intermediate logics. Publications of the Research Institute for Mathematical Science, Kyoto University, 8:117{130, 1972.
Ono, 1977] H. Ono. On some intuitionistic modal logics. Publications of the Research
Institute for Mathematical Science, Kyoto University, 13:55{67, 1977.
Orlov, 1928] I.E. Orlov. The calculus of compatibility of propositions. Mathematics of
the USSR, Sbornik, 35:263{286, 1928. (Russian).
Ostermann, 1988] P. Ostermann. Many-valued modal propositional calculi. Zeitschrift
fur mathematische Logik und Grundlagen der Mathematik, 34:343{354, 1988.
Pigozzi, 1974] D. Pigozzi. The join of equational theories. Colloquium Mathematicum,
30:15{25, 1974.
Pitts, 1992] A.M. Pitts. On an interpretation of second order quantication in rst
order intuitionistic propositional logic. Journal of Symbolic Logic, 57:33{52, 1992.
Ponse et al., 1996] A. Ponse, M. de Rijke, and Y. Venema. Modal Logic and Process
Algebra. CSLI Publications, Stanford, 1996.
Prior, 1957] A. Prior. Time and Modality. Clarendon Press, Oxford, 1957.
Rabin, 1969] M.O. Rabin. Decidability of second order theories and automata on innite trees. Transactions of the American Mathematical Society, 141:1{35, 1969.
Rabin, 1977] M.O. Rabin. Decidable theories. In J. Barwise, editor, Handbook of Mathematical Logic, pages 595{630. Elsevier, North-Holland, 1977.
Rasiowa and Sikorski, 1963] H. Rasiowa and R. Sikorski. The Mathematics of Metamathematics. Polish Scientic Publishers, 1963.
Rautenberg, 1977] W. Rautenberg. Der Verband der normalen verzweigten Modallogiken. Mathematische Zeitschrift, 156:123{140, 1977.
Rautenberg, 1979] W. Rautenberg. Klassische und nichtklassische Aussagenlogik.
Vieweg, Braunschweig{Wiesbaden, 1979.
Rautenberg, 1980] W. Rautenberg. Splitting lattices of logics. Archiv fur Mathematische Logik, 20:155{159, 1980.
Rautenberg, 1983] W. Rautenberg. Modal tableau calculi and interpolation. Journal
of Philosophical Logic, 12:403{423, 1983.
Rieger, 1949] L. Rieger. On the lattice of Brouwerian propositional logics. Acta Universitatis Carolinae. Mathematica et Physica, 189, 1949.
Rodenburg, 1986] P.H. Rodenburg. Intuitionistic correspondence theory. PhD thesis,
University of Amsterdam, 1986.
Rose, 1953] G.F. Rose. Propositional calculus and realizability. Transactions of the
American Mathematical Society, 75:1{19, 1953.
Rybakov, 1977] V.V. Rybakov. Noncompact extensions of the logic S 4. Algebra and
Logic, 16:321{334, 1977.
Rybakov, 1978] V.V. Rybakov. Modal logics with LM-axioms. Algebra and Logic,
17:302{310, 1978.

178

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

Rybakov, 1984a] V.V. Rybakov. Admissible rules for logics containing S 4:3. Siberian
Mathematical Journal, 25:795{798, 1984.
Rybakov, 1984b] V.V. Rybakov. A criterion for admissibility of rules in the modal
system S 4 and intuitionistic logic. Algebra and Logic, 23:369{384, 1984.
Rybakov, 1987] V.V. Rybakov. The decidability of admissibility of inference rules in
the modal system Grz and intuitionistic logic. Mathematics of the USSR, Izvestiya,
28:589{608, 1987.
Rybakov, 1989] V.V. Rybakov. Admissibility of inference rules in the modal system G.
Mathematical Logic and Algorithmical Problems, Mathematical Institute, Novosibirsk,
12:120{138, 1989. (Russian).
Rybakov, 1993] V.V. Rybakov. Rules of inference with parameters for intuitionistic
logic. Journal of Symbolic Logic, 58:1803{1834, 1993.
Rybakov, 1994] V.V. Rybakov. Criteria for admissibility of inference rules. Modal and
intermediate logics with the branching property. Studia Logica, 53:203{226, 1994.
Rybakov, 1995] V.V. Rybakov. Hereditarily structurally complete modal logics. Journal
of Symbolic Logic, 60:266{288, 1995.
Sahlqvist, 1975] H. Sahlqvist. Completeness and correspondence in the rst and second order semantics for modal logic. In S. Kanger, editor, Proceedings of the Third
Scandinavian Logic Symposium, pages 110{143. North-Holland, Amsterdam, 1975.
Sambin and Vaccaro, 1989] G. Sambin and V. Vaccaro. A topological proof of
Sahlqvist's theorem. Journal of Symbolic Logic, 54:992{999, 1989.
Sasaki, 1992] K. Sasaki. The disjunction property of the logics with axioms of only one
variable. Bulletin of the Section of Logic, 21:40{46, 1992.
Scroggs, 1951] S.J. Scroggs. Extensions of the Lewis system S 5. Journal of Symbolic
Logic, 16:112{120, 1951.
Segerberg, 1967] K. Segerberg. Some modal logics based on three valued logic. Theoria,
33:53{71, 1967.
Segerberg, 1970] K. Segerberg. Modal logics with linear alternative relations. Theoria,
36:301{322, 1970.
Segerberg, 1971] K. Segerberg. An essay in classical modal logic. Philosophical Studies,
Uppsala, 13, 1971.
Segerberg, 1975] K. Segerberg. That all extensions of S 4:3 are normal. In S. Kanger, editor, Proceedings of the Third Scandinavian Logic Symposium, pages 194{196. NorthHolland, Amsterdam, 1975.
Segerberg, 1986] K. Segerberg. Modal logics with functional alternative relations. Notre
Dame Journal of Formal Logic, 27:504{522, 1986.
Segerberg, 1989] K. Segerberg. Von Wright's tense logic. In P. Schilpp and L. Hahn,
editors, The Philosophy of Georg Henrik von Wright, pages 603{635. La Salle, IL:
Open Court, 1989.
Shavrukov, 1991] V.Yu. Shavrukov. On two extensions of the provability logic GL.
Mathematics of the USSR, Sbornik, 69:255{270, 1991.
Shavrukov, 1993] V.Yu. Shavrukov. Subalgebras of diagonalizable algebras of theories
containing arithmetic. Dissertationes Mathematicae (Rozprawy Matematyczne, Polska Akademia Nauk, Instytut Matematyczny), Warszawa, 323, 1993.
Shehtman, 1977] V.B. Shehtman. On incomplete propositional logics. Soviet Mathematics Doklady, 18:985{989, 1977.
Shehtman, 1978a] V.B. Shehtman. Rieger{Nishimura lattices. Soviet Mathematics
Doklady, 19:1014{1018, 1978.
Shehtman, 1978b] V.B. Shehtman. An undecidable superintuitionistic propositional
calculus. Soviet Mathematics Doklady, 19:656{660, 1978.
Shehtman, 1979] V.B. Shehtman. Kripke type semantics for propositional modal logics
with the intuitionistic base. In V.A. Smirnov, editor, Modal and Tense Logics, pages
108{112. Institute of Philosophy, USSR Academy of Sciences, 1979. (Russian).
Shehtman, 1980] V.B. Shehtman. Topological models of propositional logics. Semiotics
and Information Science, 15:74{98, 1980. (Russian).

ADVANCED MODAL LOGIC

179

Shehtman, 1982] V.B. Shehtman. Undecidable propositional calculi. In Problems of
Cybernetics. Nonclassical logics and their application, volume 75, pages 74{116. USSR
Academy of Sciences, 1982. (Russian).
Shimura, 1993] T. Shimura. Kripke completeness of some intermediate predicate logics
with the axiom of constant domain and a variant of canonical formulas. Studia Logica,
52:23{40, 1993.
Shimura, 1995] T. Shimura. On completeness of intermediate predicate logics with
respect to Kripke semantics. Bulletin of the Section of Logic, 24:41{45, 1995.
Shum, 1985] A.A. Shum. Relative varieties of algebraic systems, and propositional
calculi. Soviet Mathematics Doklady, 31:492{495, 1985.
Simpson, 1994] A.K. Simpson. The proof theory and semantics of intuitionistic modal
logic. PhD thesis, University of Edinburgh, 1994.
Smorynski, 1973] C. Smorynski. Investigations of Intuitionistic Formal Systems by
means of Kripke Frames. PhD thesis, University of Illinois, 1973.
Smorynski, 1978] C. Smorynski. Beth's theorem and self-referential sentences. In Logic
Colloquium 77, pages 253{261. North-Holland, Amsterdam, 1978.
Smorynski, 1985] C. Smorynski. Self-reference and Modal Logic. Springer Verlag, Heidelberg & New York, 1985.
Sobolev, 1977a] S.K. Sobolev. On nite-dimensional superintuitionistic logics. Mathematics of the USSR, Izvestiya, 11:909{935, 1977.
Sobolev, 1977b] S.K. Sobolev. On the nite approximability of superintuitionistic logics.
Mathematics of the USSR, Sbornik, 31:257{268, 1977.
Solovay, 1976] R. Solovay. Provability interpretations of modal logic. Israel Journal of
Mathematics, 25:287{304, 1976.
Sotirov, 1984] V.H. Sotirov. Modal theories with intuitionistic logic. In Proceedings
of the Conference on Mathematical Logic, So a, 1980, pages 139{171. Bulgarian
Academy of Sciences, 1984.
Spaan, 1993] E. Spaan. Complexity of Modal Logics. PhD thesis, Department of Mathematics and Computer Science, University of Amsterdam, 1993.
Statman, 1979] R. Statman. Intuitionistic propositional logic is polynomial-space complete. Theoretical Computer Science, 9:67{72, 1979.
Surendonk, 1996] T. Surendonk. Canonicity of intensional logics without iterative axioms. Journal of Philosophical Logic, 1996. To appear.
Suzuki, 1990] N. Suzuki. An algebraic approach to intuitionistic modal logics in connection with intermediate predicate logics. Studia Logica, 48:141{155, 1990.
Tarski, 1954] A. Tarski. Contributions to the theory of models I, II. Indagationes
Mathematicae, 16:572{588, 1954.
Thomason, 1972] S. K. Thomason. Noncompactness in propositional modal logic. Journal of Symbolic Logic, 37:716{720, 1972.
Thomason, 1974a] S. K. Thomason. An incompleteness theorem in modal logic. Theoria, 40:30{34, 1974.
Thomason, 1974b] S. K. Thomason. Reduction of tense logic to modal logic I. Journal
of Symbolic Logic, 39:549{551, 1974.
Thomason, 1975a] S. K. Thomason. The logical consequence relation of propositional
tense logic. Zeitschrift fur mathematische Logik und Grundlagen der Mathematik,
21:29{40, 1975.
Thomason, 1975b] S. K. Thomason. Reduction of second-order logic to modal logic.
Zeitschrift fur mathematische Logik und Grundlagen der Mathematik, 21:107{114,
1975.
Thomason, 1975c] S. K. Thomason. Reduction of tense logic to modal logic II. Theoria,
41:154{169, 1975.
Thomason, 1980] S. K. Thomason. Independent propositional modal logics. Studia
Logica, 39:143{144, 1980.
Thomason, 1982] S. K. Thomason. Undecidability of the completeness problem of
modal logic. In Universal Algebra and Applications, Banach Center Publications,
volume 9, pages 341{345, Warsaw, 1982. PNW{Polish Scientic Publishers.

180

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

Tseitin, 1958] G.S. Tseitin. Associative calculus with unsolvable equivalence problem.
Proceedings of the Mathematical Steklov Institute of the USSR Academy of Sciences,
52:172{189, 1958. Translation: American Mathematical Society. Translations. Series
2. 94:73{92.
Tsytkin, 1978] A.I. Tsytkin. On structurally complete superintuitionistic logics. Soviet
Mathematics Doklady, 19:816{819, 1978.
Tsytkin, 1987] A.I. Tsytkin. Structurally complete superintuitionistic logics and primitive varieties of pseudo-Boolean algebras. Mathematical Studies, 98:134{151, 1987.
(Russian).
Umezawa, 1955] T. Umezawa. U ber die Zwischensysteme der Aussagenlogik. Nagoya
Mathematical Journal, 9:181{189, 1955.
Umezawa, 1959] T. Umezawa. On intermediate propositional logics. Journal of Symbolic Logic, 24:20{36, 1959.
Urquhart, 1974] A. Urquhart. Implicational formulas in intuitionistic logic. Journal of
Symbolic Logic, 39:661{664, 1974.
Urquhart, 1984] A. Urquhart. The undecidability of entailment and relevant implication. Journal of Symobolic Logic, 49:1059{1073, 1984.
Vakarelov, 1981] D. Vakarelov. Intuitionistic modal logics incompatible with the law of
excluded middle. Studia Logica, 40:103{111, 1981.
Vakarelov, 1985] D. Vakarelov. An application of the Rieger{Nishimura formulas to the
intuitionistic modal logics. Studia Logica, 44:79{85, 1985.
van Benthem and Blok, 1978] J.A.F.K. van Benthem and W.J. Blok. Transitivity follows from Dummett's axiom. Theoria, 44:117{118, 1978.
van Benthem and Humberstone, 1983] J.A.F.K. van Benthem and I.L. Humberstone.
Hallden-completeness by gluing Kripke frames. Notre Dame Journal of Formal Logic,
24:426{430, 1983.
van Benthem, 1976] J.A.F.K. van Benthem. Modal reduction principles. Journal of
Symbolic Logic, 41:301{312, 1976.
van Benthem, 1979] J.A.F.K. van Benthem. Syntactic aspects of modal incompleteness
theorems. Theoria, 45:63{77, 1979.
van Benthem, 1980] J.A.F.K. van Benthem. Some kinds of modal completeness. Studia
Logica, 39:125{141, 1980.
van Benthem, 1983] J.A.F.K. van Benthem. Modal Logic and Classical Logic. Bibliopolis, Napoli, 1983.
van der Hoek, 1992] W. van der Hoek. Modalities for Reasoning about Knowledge and
Quantities. PhD thesis, University of Amsterdam, 1992.
Venema, 1991] Y. Venema. Many-Dimensional Modal Logics. PhD thesis, Universiteit
van Amsterdam, 1991.
Visser, 1995] A. Visser. A course in bimodal provability logic. Annals of Pure and
Applied Logic, 73:115{142, 1995.
Visser, 1996] A. Visser. Uniform interpolation and layered bisimulation. In P. Hayek,
editor, Godel'96, pages 139{164. Springer Verlag, 1996.
Walukiewicz, 1993] I. Walukiewicz. A Complete Deduction system for the -calculus.
PhD thesis, Warsaw, 1993.
Walukiewicz, 1996] I. Walukiewicz. A note on the completeness of Kozen's axiomatization of the propositional -calculus. Bulletin of Symbolic Logic, 2:349{366, 1996.
Wang, 1992] X. Wang. The McKinsey axiom is not compact. Journal of Symbolic
Logic, 57:1230{1238, 1992.
Wansing, 1994] H. Wansing. Sequent calculi for normal modal propositional logics.
Journal of Logic and Computation, 4:125{142, 1994.
Wansing, 1996] H. Wansing. Proof Theory of Modal Logic. Kluwer Academic Publishers, 1996.
Whitman, 1943] P. Whitman. Splittings of a lattice. American Journal of Mathematics,
65:179{196, 1943.
Wijesekera, 1990] D. Wijesekera. Constructive modal logic I. Annals of Pure and
Applied Logic, 50:271{301, 1990.

ADVANCED MODAL LOGIC

181

Williamson, 1994] T. Williamson. Non-genuine MacIntosh logics. Journal of Philosophical Logic, 23:87{101, 1994.
Wolter and Zakharyaschev, 1997a] F. Wolter and M. Zakharyaschev. Intuitionistic
modal logics as fragments of classical bimodal logics. In E. Orlowska, editor, Logic at
Work. Kluwer Academic Publishers, 1997. In print.
Wolter and Zakharyaschev, 1997b] F. Wolter and M. Zakharyaschev. On the relation
between intuitionistic and classical modal logics. Algebra and Logic, 1997. To appear.
Wolter, 1993] F. Wolter. Lattices of Modal Logics. PhD thesis, Freie Universitat Berlin,
1993. Parts of this paper will appear in Annals of Pure and Applied Logic under the
title \The structure of lattices of subframe logics".
Wolter, 1994a] F. Wolter. Solution to a problem of Goranko and Passy. Journal of
Logic and Computation, 4:21{22, 1994.
Wolter, 1994b] F. Wolter. What is the upper part of the lattice of bimodal logics?
Studia Logica, 53:235{242, 1994.
Wolter, 1995] F. Wolter. The nite model property in tense logic. Journal of Symbolic
Logic, 60:757{774, 1995.
Wolter, 1996a] F. Wolter. Completeness and decidability of tense logics closely related
to logics containing K 4. Journal of Symbolic Logic, 1996. To appear.
Wolter, 1996b] F. Wolter. A counterexample in tense logic. Notre Dame Journal of
Formal Logic, 37:167{173, 1996.
Wolter, 1996c] F. Wolter. Properties of tense logics. Mathematical Logic Quarterly,
42:481{500, 1996.
Wolter, 1996d] F. Wolter. Tense logics without tense operators. Mathematical Logic
Quarterly, 42:145{171, 1996.
Wolter, 1997a] F. Wolter. All nitely axiomatizable subframe logics containing CSM
are decidable. Archive for Mathematical Logic, 1997. To appear.
Wolter, 1997b] F. Wolter. Fusions of modal logics revisited. In M. Kracht, M. De
Rijke, H. Wansing, and M. Zakharyaschev, editors, Advances in Modal Logic. CSLI,
Stanford, 1997.
Wolter, 1997c] F. Wolter. A note on atoms in polymodal algebras. Algebra Universalis,
1997. To appear.
Wolter, 1997d] F. Wolter. A note on the interpolation property in tense logic. Journal
of Philosophical Logic, 1997. To appear.
Wolter, 1997e] F. Wolter. Superintuitionistic companions of classical modal logics. Studia Logica, 58:229{259, 1997.
Wronski, 1973] A. Wronski. Intermediate logics and the disjunction property. Reports
on Mathematical Logic, 1:39{51, 1973.
Wronski, 1974] A. Wronski. Remarks on intermediate logics with axioms containing
only one variable. Reports on Mathematical Logic, 2:63{75, 1974.
Wronski, 1989] A. Wronski. Su#cient condition of decidability for intermediate propositional logics. In ASL Logic Colloquium, Berlin'89, 1989.
Zakharyaschev and Alekseev, 1995] M. Zakharyaschev and A. Alekseev. All nitely
axiomatizable normal extensions of K 4:3 are decidable. Mathematical Logic Quarterly,
41:15{23, 1995.
Zakharyaschev and Popov, 1979] M.V. Zakharyaschev and S.V. Popov. On the complexity of Kripke countermodels in intuitionistic propositional calculus. In Proceedings
of the 2nd Soviet{Finland Logic Colloquium, pages 32{36, 1979. (Russian).
Zakharyaschev, 1983] M.V. Zakharyaschev. On intermediate logics. Soviet Mathematics
Doklady, 27:274{277, 1983.
Zakharyaschev, 1984] M.V. Zakharyaschev. Normal modal logics containing S 4. Soviet
Mathematics Doklady, 28:252{255, 1984.
Zakharyaschev, 1987] M.V. Zakharyaschev. On the disjunction property of superintuitionistic and modal logics. Mathematical Notes, 42:901{905, 1987.
Zakharyaschev, 1988] M.V. Zakharyaschev. Syntax and semantics of modal logics containing S 4. Algebra and Logic, 27:408{428, 1988.

182

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

Zakharyaschev, 1989] M.V. Zakharyaschev. Syntax and semantics of intermediate logics. Algebra and Logic, 28:262{282, 1989.
Zakharyaschev, 1991] M.V. Zakharyaschev. Modal companions of superintuitionistic
logics: syntax, semantics and preservation theorems. Mathematics of the USSR,
Sbornik, 68:277{289, 1991.
Zakharyaschev, 1992] M.V. Zakharyaschev. Canonical formulas for K 4. Part I: Basic
results. Journal of Symbolic Logic, 57:1377{1402, 1992.
Zakharyaschev, 1994] M.V. Zakharyaschev. A new solution to a problem of Hosoi and
Ono. Notre Dame Journal of Formal Logic, 35:450{457, 1994.
Zakharyaschev, 1996] M.V. Zakharyaschev. Canonical formulas for K 4. Part II: Conal
subframe logics. Journal of Symbolic Logic, 61:421{449, 1996.
Zakharyaschev, 1997a] M.V. Zakharyaschev. Canonical formulas for K 4. Part III: the
nite model property. Journal of Symbolic Logic, 62, 1997. To appear.
Zakharyaschev, 1997b] M.V. Zakharyaschev. Canonical formulas for modal and superintuitionistic logics: a short outline. In M. de Rijke, editor, Advances in Intensional
Logic, pages 191{243. Kluwer Academic Publishers, 1997.

Index
23
L -formula, 44

compactness, 31
complete set of formulas, 8
complex variety, 34
complexity function, 161
conguration problem, 146
congruential logic, 166
conservative formula, 76
cover, 13
cycle free frame, 17, 81

L

{prime logic, 8
-irreducible logic, 8
{-complex logic, 34
{-generated frame, 11, 81
n-transitive logic, 6, 81
actual world, 60
actual world condition, 61
amalgamability, 73
atom, 13, 18
axiomatic basis, 8
axiomatization
nite, 7
independent, 7
problem, 15
recursive, 7

d-cyclic set, 13
deduction theorem, 5
deductively equivalent formulas, 5
degree of incompleteness, 27
depth of a frame, 12
descriptive frame, 11, 81
di erence operator, 167
di erentiated frame, 11, 81
disjunction property, 129
modal, 129
distinguished point, 60
downward directness, 24
Dummett logic, 117

Beth property, 69
bimodal companion, 142
bisimulation, 167
canonical formula, 39
intuitionistic, 117
quasi-normal, 62
canonicity, 19
CDC, 37
closed domain, 37
closed domain condition, 37
cluster assignment, 97
conal subframe formula, 45
conal subframe logic, 45
quasi-normal, 63
compact frame, 11

elementary logic, 26
essentially negative formula, 127
nite embedding property, 48
nite model property
exponential, 161
global, 32
polynomial, 161
xed point operator, 167
focus, 52
183

184

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

frame formula, 39
fusion, 83
Godel translation, 113
global derivability, 5
global Kripke completeness, 32
graded modality, 167
Hallden completeness, 77
Heyting algebra, 111
inaccessible world, 80
independent set of formulas, 8
inference rule
admissible, 149
derivable, 149
interpolant, 69
post-, 77
interpolation property, 69
for a consequence relation, 70
intersection of logics, 6
intuitionistic frame, 112
intuitionistic modal frame, 138
intuitionistic modal logic, 136
Jankov formula, 39
Kreisel{Putnam logic, 130
Kripke frame, 9
Lob axiom, 35
linear tense logic, 98
local tabularity, 42
logic of a class of frames, 9
Medvedev's logic, 134
minimal tense extension, 93
Minsky machine, 146
modal companion, 119
modal degree, 20
modal matrix, 60
negative formula, 21
Nishimura formula, 113

Noetherian frame, 35
nominal, 167
non-eliminability, 20
non-iterative logic, 82
normal lter, 73
normal form, 42
open domain, 37, 115
p-morphism, 11
persistence, 19
polymodal frame, 81
polymodal logic, 80
polynomially equivalent logics, 161
positive formula, 21
pretabularity, 67
prime lter, 112
prime formula, 8
pseudo-Boolean algebra, 111
quasi-normal logic, 59
reduced frame, 20
reduction, 11, 81
weak, 106
rened frame, 11
rened rened, 81
replacement function, 95
Rieger{Nishimura lattice, 112
root, 9, 81
rooted frame, 9
Sahlqvist formula, 26, 82
Scott logic, 130
semantical consequence, 160
si-fragment, 119
si-logic, 111
simulation of a frame, 90
simulation of a logic, 90
skeleton, 113
skeleton lemma, 114
Smetanich logic, 117
splitting, 15

ADVANCED MODAL LOGIC

union-, 15
splitting pair, 8
standard translation, 55
strict Kripke completeness, 15
strict sf-completeness, 48
strong global completeness, 32
strong Kripke completeness, 31
strongly positive formula, 22
structural completeness, 151
subframe, 35, 36, 65, 81, 115
conal, 46, 65
generated, 9, 81
subframe formula, 45
subframe logic, 45, 46
quasi-normal, 63
subreduction, 36
conal, 36
quasi-, 61
weak, 107
sum of logics, 6
superamalgamability, 73
superintuitionistic logic, 111
surrogate, 84
surrogate frame, 106
t-line logic, 102
tabularity, 65
Tarski's criterion, 7
tense frame, 93
tense logic, 93
tight frame, 11
time-line, 102
topological Boolean algebra, 113
undecidable formula, 149
uniform formula, 43
uniform interpolation, 77
universal frame of rank n, 12
universal modality, 87
untied formula, 25
upward closed set, 9
weak Kreisel{Putnam formula, 116

185

