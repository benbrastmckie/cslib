<!-- Source: Zakharyaschev, Wolter & Chagrov (2001). Advanced Modal Logic. Section 2: Polymodal Logics — multi-modal logics, products, fusion. -->

So far we have conned ourselves to considering modal logics with only one
necessity operator. From a theoretical point of view this restriction is not
such a great loss as it may seem at rst sight. In fact, really important
concepts of modal logic do not depend on the number of boxes and can
be introduced and investigated on the basis of just one. We shall give a
precise meaning to this claim in Section 2.3 below where it is shown that
polymodal logic is reduced in a natural way to unimodal logic. However,
there are at least two reasons for a detailed discussion of polymodal logic
in this chapter.
First, a number of interesting phenomena are easily missed in unimodal
logic and actually appear in a representative form only in the polymodal
case. For example, with the exception of NExtK4.3 and QCSF all known
general decidability results in unimodal logic have been obtained by proving
the nite model property. In fact, nearly all natural classes of logics in
NExtK turned out to be describable by their nite frames. The situation
drastically changes with the addition of just one more box. Even in the
case of linear tense logics or bimodal provability logics one has to start with
13

By reductions that map d to di .

ADVANCED MODAL LOGIC

79

a thorough investigation of their innite frames: FMP becomes a rather
rare guest. While the result on NExtK4.3 indicated the need for general
methods of establishing decidability without FMP, this need becomes of
vital importance only in the context of polymodal logic.
The second reason is that various applications of modal logic require
polymodal languages. For example, in tense logic we have two necessitylike operators 21 and 22 . One of them, say the former, is interpreted as \it
will always be true" and the other as \it was always true". Kripke frames for
tense logics are structures hW R1  R2 i with two binary relations R1 and R2
such that R2 coincides with the converse R1;1 of R1 (which reects the fact
that a moment x is earlier than y i y is later than x). The characteristic
axioms connecting the two tense operators are
p ! 21 32p and p ! 22 31p:
For more information about tense systems consult Basic Tense Logic.
Another example is basic temporal logic in which we have two necessitylike operators: one of them|usually called Next|is interpreted by the
successor relation in ! and the other by its transitive and reexive closure. Details can be found in Segerberg 1989]. Propositional dynamic logic
PDL and its extensions, like deterministic PDL, can also be regarded as
polymodal logics (see Dynamic Logic).
A number of provability logics use two or more modal operators see e.g.
Boolos 1993]. In GLB, for instance, we have one operator 21 understood
as provability in PA and another operator 22 interpreted as !-provability
in PA. The unimodal fragments of GLB coincide with GL. The axioms
connecting 21 and 22 are
21 p ! 22 p and 31p ! 22 31p:
In epistemic logics we need an operator 2i for each agent i 2i ' is interpreted as \agent i believes (or knows) '". One possible way to axiomatize
the logic of knowledge with m agents is to take the axioms of S5 for each
agent without any principles connecting di erent 2i and 2j . We denote
m
the resultant logic by m
i=1 S5. Often i=1 S5 is extended by the common
knowledge operator C with the intended meaning
C' = E' ^ E2 ' ^ : : : ^ En' ^ : : :  where E' = m
i=1 2i '
(see e.g. Halpern and Moses 1992] and Meyer and van der Hoek 1995]).
The reader will nd more items for this list in other chapters of the
Handbook.
From the semantical point of view, many standard polymodal logics
can be obtained by applying Boolean or various natural closure operators to the accessibility relations of Kripke frames. For instance, in frames

N

N

V

80

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

hW R1  : : :  Rn i for epistemic logic the common knowledge operator is interpreted by the transitive closure of R1  : : :  Rn . Tense frames result
from usual hW Ri by adding the converse of R. Humberstone 1983] and
Goranko 1990a] study the bimodal logic of inaccessible worlds determined
by frames of the form W R W 2 ; R . This list of examples can be continued for a general approach and related topics consult Goranko 1990b],
Gargov et al. 1987], Gargov and Passy 1990].
Let us see now how polymodal logics in general t into the theory developed so far. We begin by demonstrating how the concepts introduced in
the unimodal case transfer to polymodal logic and showing that a few general results|like Sahlqvist's and Blok's Theorems|have natural analogues
in polymodal logic. We hope to convince the reader that up to this point
no new diculties arise when one switches from the unimodal language to
the polymodal one. After that, in Section 2.2, we start considering subtler
features of polymodal logics.





2.1 From unimodal to polymodal

Let LI be the propositional language with a nite number of necessity operators 2i , i 2 I . A normal polymodal logic in LI is a set of LI -formulas
containing all classical tautologies, the axioms 2i (p ! q) ! (2i p ! 2i q)
for all i 2 I , and closed under substitution, modus ponens and the rule of
necessitation '=2i ' for every i 2 I . If the language is clear from the context, we call these logics just (normal) modal logics and denote by NExtL
the family of all normal extensions of L (in the language LI ). The smallest
normal modal logic with n necessity operators is denoted by Kn (K = K1 ,
of course).
Given a logic L0 in LI and a set of LI -formulas ;, we again denote by
L0  ; the smallest normal logic (in LI ) containing L0  ;. A number
of other notions and results also transfer in a rather straightforward way,
e.g. Theorems 1.4 and 1.6, Proposition 1.5 and all concepts involved in their
formulations. More care has to be taken to generalize Theorems 1.1, 1.2 and
1.3. Denote by M I the set of non-empty strings (words) over f2i : i 2 I g
which do not contain any 2i twice and put

^

^

2I ' = fM ' : M 2 M I g 2I m ' = f2nI ' : n  mg:
In the language LI the operator 2I serves as a sort of surrogate for 2 in

K. For example, the following polymodal version of Theorem 1.1 holds.

THEOREM 2.1 (Deduction) For every modal logic L in LI , every set of
LI -formulas ;, and all LI -formulas ' and ,
;  `L ' i 9m 0 ; `L 2I m  ! ':

ADVANCED MODAL LOGIC

81

Theorems 1.2 and 1.3 can be reformulated analogously by replacing 2
with 2I (a logic L in LI is n-transitive if it contains 2I n p ! 2nI +1 p).
Basic semantic concepts are lifted to the polymodal case in a straightforward manner. The algebraic counterpart of L 2 NExtKn is the variety of Boolean algebras with n unary operators validating L. A structure
F = hW hRi : i 2 I i P i is called a (general polymodal) frame whenever
every hW Ri  P i, for i 2 I , is a unimodal frame. We then put

2i X = fx 2 W : 8y (xRi y ! y 2 X )g:
Dierentiated, rened and descriptive frames and the truth-preserving operations can also be dened in the same component-wise way. For instance,
a frame F = hW hRi : i 2 I i P i is di erentiated if all the unimodal frames
hW Ri  P i, for i 2 I , are di erentiated. F = hW hRi : i 2 I i P i is a (generated) subframe of G = hV hSi : i 2 I i Qi if all hW Ri  P i are (generated)
subframes of hV Si  Qi, and f is a reduction of F to G if f is a reduction of
hW Ri  P i to hV Si  Qi, for every i 2 I .
There are some exceptions to this rule. A point r is called a root of F if it
is a root of the unimodal frame hW i2I Ri i. This does not mean that r is a
root of all unimodal reducts of F. Another important exception: as before,
a polymodal frame is {-generated if the algebra F+ is {-generated however,
this does not mean that the unimodal reducts of F are {-generated.

S

Splittings and the degree of Kripke incompleteness The semantic

criterion of splittings by nite frames given in Theorem 1.15 transfers to
polymodal logics by replacing 2 with 2I . Again, all nite rooted frames
split NExtL0 , if L0 is an n-transitive logic in LI . Notice, however, that
n-transitivity is a rather strong condition in the polymodal case. For example, it is easily checked that the fusion S5 & S5 as well as the minimal
tense logic K4:t containing K4 are not n-transitive, for any n < ! (see
Sections 2.2 and 2.4 for precise denitions). In fact, only  splits the lattice
NExt(S5 & S5) and only  splits NExtK4:t (see Wolter 1993] and Kracht
1992], respectively).
Call a frame hW hRi : i 2 I ii cycle free if the unimodal frame hW i2I Ri i
is cycle free. Kracht 1990] showed that precisely the nite cycle free frames
split NExtKn .
It is not dicult now to extend Blok's result on the degree of Kripke
incompleteness to the polymodal case. Note, however, that the degree of
incompleteness of For in NExtKn is 2@0 whenever n 2. So, we do not have
a polymodal analog of Makinson's Theorem. (An example of an incomplete
maximal consistent logic in NExtK2 is the logic determined by the tense
frame C(0 ) introduced in Section 2.5).

S

82

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

THEOREM 2.2 Let n > 1. If L is a union-splitting of NExtKn , then L is
strictly Kripke complete. Otherwise L has degree of Kripke incompleteness
2@0 in NExtKn .

Sahlqvist's Theorem and persistence The proof of the following poly-

modal version of Sahlqvist's Theorem is a straightforward extension of the
proof in the unimodal case. Say that ' is a Sahlqvist formula (in LI ) if the
result of replacing all 2i and 3i , i 2 I , in ' with 2 and 3, respectively, is
a unimodal Sahlqvist formula.
THEOREM 2.3 Suppose that ' is equivalent in NExtKn to a Sahlqvist formula. Then Kn  ' is D-persistent, and one can eectively construct a rst
order formula (x) in R1  : : :  Rn and = such that, for every descriptive or
Kripke frame F and every point a in F, (F a) j= ' i F j= (x)a].

N

Bellissima's result on the DF -persistence of all logics in NExtAltn has
a polymodal analog as well. Denote by i2I Altn the smallest polymodal
logic in LI containing Altn in all its unimodal fragments. It is easy to see
that every L 2 NExt i2I Altn is DF -persistent and so Kripke complete.
However, in contrast to the lattice NExtAlt1 |which is countable and all
logics in which have FMP (see Segerberg 1986] and Bellissima 1988])|
the lattice NExt(Alt1 & Alt1 ) is rather complex: as was shown by Grefe
1994], it contains logics without FMP (even without nite frames at all)
and uncountably many maximal consistent logics.

N

Some FMP results Fine's Theorem on uniform logics can be extended

to a suitable class of polymodal logics in LI , namely those logics that contain 3i>, for all i 2 I , and are axiomatizable by formulas ' in which all
maximal sequences of nested modal operators coincide with respect to the
distribution of the indices i of 2i and 3i , i 2 I .
Now consider a result of Lewis 1974] which we have not proved in its
unimodal formulation. Call a normal polymodal logic non-iterative if it is
axiomatizable by formulas without nested modalities. Examples of noniterative logics are T = K  2p ! p, Altm & Altn and K2  22 p ! 21 p.
THEOREM 2.4 (Lewis 1974) All non-iterative normal logics have FMP.

Proof Suppose the axioms of L = Kn  ; have no nested modal operators and ' 62 L. By a '-description we mean any set of subformulas of
' together with the negations of the remaining formulas in Sub'. For

each L-consistent '-description % select a maximal L-consistent set 
containing %. Denote by W the (nite) set of the selected  and dene

ADVANCED MODAL LOGIC

83

F = hW hRi : i 2 I ii and M = hF Vi by taking


Ri  i 3 i

^& 2



and V(p) = f  2 W : p 2  g. It is easily proved that (M  ) j=  i
 2  , for all subformulas  of ' and  2 W . Hence F 6j= '. It is also
easy to see that for all truth-functional compounds  of subformulas in ',
(M



) j= 3i  i 3i 2



:

(14)

Consider now a model M0 = hF V0 i and  2 ;. For each variable p put

p =

_ n^ % :



o

2 V(p)

and denote by 0 the result of substituting p for p, for each p in . Then
M0 j=  i M j= 0 . In view of (14), we have M j= 0 because 0 has no
2
nested modalities. Therefore, F j=  and so F j= L.

Tabular Logics Needless to say that all polymodal tabular logics are

nitely axiomatizable and have only nitely many extensions. (The proof is
the same as in the unimodal case.) A more interesting observation concerns
the complexity of polymodal logics whose unimodal fragments are tabular
or pretabular. In fact, it is not dicult to construct two tabular unimodal
logics L1 and L2 such that their fusion L1 & L2 has uncountably many
normal extensions (see e.g. Grefe 1994]). However, those logics are DF persistent and so Kripke complete. Wolter 1994b] showed that the lattice

NExtT can be embedded into the lattice NExt(Log 6& S5) in such a way
that properties like FMP, decidability and Kripke completeness are reected
under this embedding. It follows that almost all \negative" phenomena of
modal logic are exhibited by bimodal logics one unimodal fragment of which
is tabular and the other pretabular.

2.2 Fusions

The simplest way of constructing polymodal logics from unimodal ones is
to form the fusions (alias independent joins) of them. Namely, given two
unimodal logics L1 and L2 in languages with the same set of variables and
distinct modal operators 21 and 22 , respectively, the fusion L1 & L2 of
L1 and L2 is the smallest bimodal logic to contain L1  L2. If ;1 and
;2 axiomatize L1 and L2, then L1 & L2 is axiomatized by ;1  ;2 , i.e.,
L1 & L2 = K2  ;1  ;2 . So the fusions are precisely those bimodal logics
that are axiomatizable by sets of formulas each of which contains only one

84

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

of 21 , 22 . From the model-theoretic point of view this means that a frame
hW R1  R2  P i validates L1 & L2 i hW Ri  P i j= Li for i = 1 2.
PROPOSITION 2.5 (Thomason 1980) If logics L1 and L2 are consistent,
then L1 & L2 is a conservative extension of both L1 and L2 .

Proof Suppose for deniteness that ' 62 L1, for some formula ' in the
language of L1 , and consider the Tarski{Lindenbaum algebras









AL1 (!) = A ^A  :A  21 and AL2 (!) = B ^B  :B  22 :
The Boolean reducts of them are countably innite atomless Boolean algebras which are known to be isomorphic (see e.g. Koppelberg 1988]). So
we
assume that
A = B , ^A = ^B , :A = :B . Since AL1 (!) refutes ',
Amay

A
A
2
^  :  21  22 is then an algebra for L1 & L2 refuting '.
Having constructed the fusion of logics, it is natural to ask which of
their properties it inherits. For example, the rst order theory of a single
equivalence relation has the nite model property and is decidable, but the
theory of two equivalence relations is undecidable and so does not have the
nite model property (see Janiczak 1953]). So neither decidability nor the
nite model property is preserved under joins of rst order theories. On
the other hand, as was shown by Pigozzi 1974], decidability is preserved
under fusions of equational theories in languages with mutually disjoint sets
of operation symbols.
For modal logics we have:
THEOREM 2.6 Suppose L1 and L2 are normal unimodal consistent logics
and P is one of the following properties: FMP, (strong) Kripke completeness, decidability, Hallden completeness, interpolation, uniform interpolation. Then L = L1 & L2 has P i both L1 and L2 have P .

Proof We outline proofs of some claims in this theorem the reader can

consult Fine and Schurz 1996], Kracht and Wolter 1991], and Wolter
1997b] for more details.
The implication ()) presents no diculties. So let us concentrate on
((). With each formula ' of the form 2i  we associate a new variable
q' which will be called the surrogate of '. For a formula ' containing
no surrogate variables, denote by '1 the formula that results from ' by
replacing all occurrences of formulas 22 , which are not within the scope
of another 22 , with their surrogate variables q22  . So '1 is a unimodal
formula containing only 21 . Denote by %1 (') the set of variables in '
together with all subformulas of 22  2 Sub'. The formula '2 and the set
%2(') are dened symmetrically.

ADVANCED MODAL LOGIC

85

Suppose now that both L1 and L2 are Kripke complete and ' 62 L. To
prove the completeness of L we construct a Kripke frame for L refuting
'. Since we know only how to build refutation frames for the unimodal
fragments of L, the frame is constructed by steps alternating between 21
and 22 . First, since L1 is complete, there is a unimodal model M based
on a Kripke frame for L1 and refuting '1 at its root r. Our aim now is
to ensure that the formulas of the form 22  have the same truth-values as
their surrogates q22  . To do this, with each point x in M we can associate
the formula

^

^

'x = f 2 %1(') : (M x) j= 1 g ^ f: :  2 %1(') (M x) 6j= 1 g
construct a model Mx based on a frame for L2 and satisfying '2x at its
root y, and then hook Mx to M by identifying x and y. After that we can
switch to 21 and in the same manner ensure that formulas 21  have the
same truth-values as q21  at all points in every Mx . And so forth.
However, to realize this quite obvious scheme we must be sure that 'x
is really satisable in a frame for L2 , which may impose some restrictions
on the models we choose. First, one can show that in the construction
above it is enough to deal with points x accessible from r by at most m =
md(') steps. Let X be the set of all such points. Now, a sucient and
necessary condition for 'x to be L- (and so L2-) consistent can be formulated
as follows. Call a %1 (')-description the conjunction of formulas in any
maximal L-consistent subset of %1 (')  f: :  2 %1(')g. It should be
clear that 'x is L-consistent i it is a %1 (')-description. Denote by #1 (')
the set of all %1 (')-descriptions. It follows that all 'x , for x 2 X , are
L-consistent i (M r) j= 21 m ( #1 ('))1 . In other words, we should start
with a model M satisfying '1 ^ 21 m ( #1 ('))1 at its root r. Of course,
the subsequent models Mx , for x 2 X , must satisfy '2x ^ 22 m ( #2 ('x ))2 ,
where #2 ('x ) is the set of all %2('x )-descriptions, etc.
In this way we can prove that Kripke completeness is preserved under
fusions. The preservation of strong completeness and FMP can be established in a similar manner. The following lemma plays the key role in the
proof of the preservation of the four remaining properties.

W

W

W

LEMMA 2.7 The following conditions are equivalent for every ':
(i) ' 2 L1 & L2 
(ii) 21 m ( #1 ('))1 ! '1 2 L1 , where m = md(')
(iii) 22 m ( #2 ('))2 ! '2 2 L2 .

W
W

For Kripke complete L1 and L2 this lemma was rst proved by Fine and
Schurz 1996] and Kracht and Wolter 1991] actually, it is an immediate
consequence of the consideration above. The proof for the arbitrary case is

86

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

also based upon a similar construction combined with the algebraic proof
of Proposition 2.5 for details see Wolter 1997b].
Now we show how one can use this lemma to prove the preservation
of the remaining properties. Dene a1 (') to be the length of the longest
sequence 22  21  22  : : : of boxes starting with 22 such that a subformula
of the form 22 (: : : 21 (: : : 22 (: : : : : :))) occurs in '. The function a2 (') is
dened analogously by exchanging 21 and 22 , and a(') = a1 (') + a2 (').
It is easy to see that

_

_

a(') > a( #1 (')) or a(') > a( #2 (')):
The preservation of decidability, Hallden completeness, interpolation, and
uniform interpolation can be proved by induction on a(') with the help
of Lemma 2.7. We illustrate the method only for Hallden completeness.
Notice rst that, modulo the Boolean equivalence, we have

_ # (' _ ) = _ # (') ^ _ # () ^ ^ (' )
1

1

1

where
(' ) = f1 ! :2 : 1 2 #1 (') 2 2 #1 () 1 ! :2 2 Lg:
Suppose both L1 and L2 are Hallden complete. By induction on n = a('_)
we prove that ' _  2 L implies ' 2 L or  2 L whenever ' and  have no
common variables. The basis of induction is trivial. So suppose a(' _ ) =
n > 0 and ' _  2 L. We may also assume that a(' _ ) > a( #1 (' _ )):
By the induction hypothesis, it follows that (' ) = . Hence, up to the
Boolean equivalence, #1 (' _ ) = #1 (') ^ #1 () and, by Lemma 2.7,

W

W

W
W
_
_
2 m ( # ('))1 ^ 2 m ( # ())1 ! (' _ )1 2 L 

1

1

for m = md(' _ ). Then

_


1

1

1

_

(21 m ( #1 ('))1 ! '1 ) _ (21 m ( #1 ())1 ! 1 ) 2 L1
and, by the Hallden completeness of L1 , one of the disjuncts in this formula
belongs to L1 . By Lemma 2.7, this means that ' 2 L or  2 L.
2

Remark. This theorem can be generalized to fusions of polymodal logics
with polyadic modalities.
Note that in languages with nitely many variables both GL:3 and K
are strongly complete but GL:3 & K is not strongly complete even in the
language with one variable (see Kracht and Wolter 1991]).

ADVANCED MODAL LOGIC

87

It is natural now to ask whether there exist interesting axioms ' containing both 21 and 22 and such that (L1 & L2 )  ' inherits basic properties of
L1  L2 2 NExtK. Let us start with the observation that even such a simple
axiom as 21 p $ 22 p destroys almost all \good" properties because (i) we
can identify (L1 & L2 )  21 p $ 22 p with the sum of the translation of L1
and L2 into a common unimodal language and (ii) such properties as FMP,
decidability, and Kripke completeness are not preserved under sums of unimodal logics (see Example 1.64 and Chagrov and Zakharyaschev 1997]).
Even for the simpler formula 22 p ! 21 p no general results are available.
To demonstrate this we consider the following way of constructing a bimodal
logic Lu for a given L 2 NExtK:

Lu = (L & S5)  22 p ! 21 p:
The modal operator 22 in Lu is called the universal modality. Its meaning
is explained by the following lemma:
LEMMA 2.8 (Goranko and Passy 1992) For every normal unimodal logic L
and all unimodal formulas ' and ,

' `L  i `Lu 22 ' ! :

Proof Follows immediately from Theorem 1.19 (ii), since
hW R P i j= L i hW R W ' W P i j= Lu

for every frame hW R P i and every unimodal logic L.

2

The universal modality is used to express those properties of frames F =
hW R W ' W i that cannot be expressed in the unimodal language. For
example, F validates 22 (p ! 31p) ! :p i it contains no innite Rchains. Recall that there is no corresponding unimodal axiom, since K is
determined by the class of frames without innite R-chains. We refer the
reader to Goranko and Passy 1992] for more information on this matter.
THEOREM 2.9 (Goranko and Passy 1992) For any L 2 NExtK,
(i) L is globally Kripke complete i Lu is Kripke complete
(ii) L has global FMP i Lu has FMP.

Proof We prove only (i). Suppose that Lu is Kripke complete and ' 6`L .

Then by Lemma 2.8, 22 ' !  62 Lu and so 22 ' !  is refuted in a Kripke
frame F = hW R1  R2 i for Lu . We may assume that R2 = W ' W . But
then ' `L  is refuted in hW R1 i. Conversely, suppose that L is globally
Kripke complete and ' 62 Lu , for a (possibly bimodal) formula '. Using

88

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

the properties of S5 it is readily checked that ' is (e ectively) equivalent
in Ku to a formula '0 which is a conjunction of formulas  of the form
 = 0 _ 321 _ 22 2 _ 22 3 _ : : : _ 22 n
such that 0  : : :  n are unimodal formulas in the language with 21 . Let
 be a conjunct of '0 such that  62 Lu . Then :1 6`L i , for every
i 2 f0 2 3 : : : ng. Since L is globally complete, we have Kripke frames
hWi  Ri i for L refuting :1 `L i , for i 2 f0 2 : : : ng. Denote by hW Ri
the disjoint union of those frames. Then hW R W ' W i is a Kripke frame
for Lu refuting '.
2
We have seen in Section 1.5 that there are Kripke complete logics (logics
with FMP) which do not enjoy the corresponding global property. In view
of Theorem 2.9, we conclude that neither FMP nor Kripke completeness is
preserved under the map L 7! Lu .
Another interesting way of adding to fusions new axioms mixing the
necessity operators is to use the so called inductive (or Segerberg's) axioms.
First, we extend the language LI with m necessity operators by introducing
the operators E and C and then let
ind = fEp $ 2ip Cp ! ECp C(p ! Ep) ! (p ! Cp)g:

^

i2I
Now, given L 2 NExtKm , we put

LECm = (L & KE & S4C )  ind

where KE and S4C are just K and S4 in the languages with E and C, respectively. The following proposition explains the meaning of the inductive
axioms.
PROPOSITION 2.10 A frame hW R1  : : :  Rm  RE  RC i validates LECm
i hW R1  : : :  Rm i j= L, RE = R1  : : :  Rm and RC is the transitive
reexive closure of RE .
EXAMPLE 2.11 The logic (Alt1  D)EC1 is determined by the frame
h! S i in which S is the successor relation in !. (Here we omit writing RE because RE = S .) For details consult Segerberg 1989].14
No general results are known about the preservation properties of the
map L 7! LECm . In fact, it is easy to extend the counter-examples for the
map L 7! Lu to the present case (see Hemaspaandra 1996]). However, at
least in some cases|especially those that are of importance for epistemic
logic|the logic LECm enjoys a number of desirable properties.
14 Krister Segerberg kindly informed us that this result was independently obtained by
D. Scott, H. Kamp, K. Fine and himself.

ADVANCED MODAL LOGIC

N

N

89

N

THEOREM 2.12 (Halpern and Moses 1992) For every m 1, the logics
m
m
( m
i=1 K)ECm , ( i=1 S4)ECm and ( i=1 S5)ECm have FMP.

Proof We consider only L = (Nmi=1 S5)ECm. The proof is by ltration

and so the main diculty is to nd a suitable \lter". Suppose that ' 62 L
and let M = hhW R1  : : :  Rm  RE  RC i  Ui be the canonical model for L.
Denote by ;: the closure of a set of formulas ; under negations and dene
a lter ' = ':1  ':2  ':3 , where '1 = Sub', '2 = f2i  : E 2 ':1 g
and '3 = fEC 2i C : C 2 ':1 g. Certainly, ' is nite and closed under
subformulas. Now, we lter M through ', i.e., put W = fx] : x 2 W g,
where x] consists of all points that validate the same formulas in ' as x,
and
x]Ri y] i 82i  2 ' ((M x) j= 2i  ! (M y) j= 2i )
RE = R1  : : :  Rm 
and RC is the transitive and reexive closure of RE . A rather tedious
inductive proof shows that hW  R1  : : :  Rm  RE  RC i refutes ' under the
valuation U (p) = fx] : x j= pg, p a variable in '. For details we refer the
reader to Halpern and Moses 1992] and Meyer and van der Hoek 1995].

2

It would be of interest to look for big classes of logics L for which LECm
inherits basic properties of L.

2.3 Simulation

In the preceding section we saw how results concerning logics in NExtK can
be extended to a certain class of polymodal logics. More generally, we may
ask whether|at least theoretically|polymodal logics are reducible to unimodal ones. The rst to attack this problem was Thomason 1974b, 1975c]
who proved that each polymodal logic L can be embedded into a unimodal
logic Ls in such a way that L inherits almost all interesting properties of
Ls . Using this result one can construct unimodal logics with various \negative" properties by presenting rst polymodal logics with the corresponding
properties, which is often much easier. It was in this way that Thomason
1975c] constructed Kripke incomplete and undecidable unimodal calculi.
Kracht 1996] strengthened Thomason's result by showing that his embedding not only reects but also (i) preserves almost all important properties
and (ii) induces an isomorphism from the lattice NExtK2 onto the interval
Sim K  2?], for some normal unimodal logic Sim. Thus indeed, in many
respects polymodal logics turn out to be reducible to unimodal ones.
Below we outline Thomason's construction following Kracht 1996] and
Kracht and Wolter 1997a]. To dene the unimodal \simulation" Ls of a

90

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

1


R1 6R2

F ?

I
@
K
A
A@ -
A 6
A -?Fs

Figure 11.
bimodal logic L, let us rst transform each bimodal frame into a unimodal
one.
So suppose F = hW R1  R2  P i is a bimodal frame. Construct a unimodal
frame Fs = hW s  Rs  P s i|the simulation of F|by taking
W s = W ' f1 2g  f1g
Rs = fhhx 1i  hx 2ii : x 2 W g 
fhhx 2i  hx 1ii : x 2 W g 
fhhx 1i  1i : x 2 W g 
fhhx 1i  hy 1ii : x y 2 W xR1 yg 
fhhx 2i  hy 2ii : x y 2 W xR2 yg
P s = f(X ' f2g)  (Y ' f1g)  Z : X Y 2 P Z f1gg:
This construction is illustrated by Fig. 11. One can easily prove that Fs is a
Kripke (di erentiated, rened, descriptive) frame whenever F is so. Notice
also that if W =  then Fs 
= . Now, given a bimodal logic L, dene the
simulation Ls of L to be the unimodal logic
LogfFs : F j= Lg:
To formulate the translation which embeds L into Ls we require the following formulas and notations:
 = 2?
2 ' = 2( ! ')
 = 32?
2 ' = 2( ! ')
 = : ^ :3
2 ' = 2( ! '):
3 , 3 and 3 are dened dually. Observe that the formula  is true in
Fs only at 1,  is true precisely at the points in the set fhx 1i : x 2 W g,
and  is true at the points fhx 2i : x 2 W g and only at them. Put
ps
= p
(:')s
=  ^ :'s 
s
(' ^  ) = ' s ^  s 
(21 ')s = 2 's 
(22 ')s = 2 2 2 's :
By an easy induction on the construction of ' one can prove

ADVANCED MODAL LOGIC

91

LEMMA 2.13 Let M = hF Vi be a bimodal model, X = fx : x j= g and
let Ms = hFs  Vs i be a model such that Vs (p) \ X = V(p) ' f1g, for all
variables p. Then for every bimodal formula ',
(M x) j= ' i (Ms  hx 1i) j= 's 
M j= ' i Ms j=  ! 's 
F j= ' i Fs j=  ! 's :
Using this lemma, both consequence relations `L and `L can be reduced to
the corresponding consequence relations for Ls .
PROPOSITION 2.14 Let L be a bimodal logic,
and ' a bimodal formula. Then

a set of bimodal formulas

`L ' i  ! s `Ls  ! 's 
`L ' i  ! s `Ls  ! 's 

where  ! s = f ! : 2 s g.

To axiomatize Ls , given an axiomatization of L, we require the following
formulas:
(a)  ! (3 p $ 2 p)  ^ 3 p ! 2 3 p
(b)  ! (3 p $ 2 p)
(c)  ! (3 p $ 2 p)
(d)  ^ p ! 2 2 p  ^ p ! 2 2 p
(e)  ^ 3 p ! 2 2 2 3 p:
Let Sim = K  f(a) : : :  (e)g. Obviously, Fs is a frame for Sim whenever
F is a bimodal frame. Consider now a di erentiated frame F = hW R P i
for Sim which contains only one point where  is true. (Actually, every
rooted di erentiated frame for Sim satises this condition.) Construct a
bimodal frame Fs = hV R1  R2  Qi, called the unsimulation of F, in the
following way. Put V = fx 2 W : x j= g, V = fx 2 W : x j=  g and
U = fx 2 W : x j=  g. Since  _  _  2 K, we have W = V  V  U . It
is not hard to verify using (b) and (c) (and the di erentiatedness of F) that
for every x 2 V there exists a unique x 2 V such that xRx , and for every
y 2 V there exists y 2 V such that yRy . By (d), x = x  . Finally, we
put R1 = R \ V 2 , R2 = fhx yi 2 V 2 : x Ry g and Q = fX \ V : X 2 P g.
It is easily proved that Fs is a bimodal frame. The name unsimulation is
justied by the following lemma.
LEMMA 2.15 For every dierentiated bimodal frame F, (Fs )s 
= F.
Now we have:

92

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

THEOREM 2.16 For every bimodal logic L = K2  ,
Ls = Sim   ! s :
Proof Clearly, Sim   ! s Ls. Assume that the converse inclusion
does not hold. Then there exists a rooted di erentiated F such that F 6j= Ls
but F j= Sim   ! s . By Lemma 2.15, (Fs )s 6j= Ls . By the denition
of Ls , we then conclude that Fs 6j= L. And by Proposition 2.14, we have
(Fs )s 6j=  ! s , from which F 6j=  ! s .
2
s
Given L 2 Sim K  2?], the logic Ls = f' :  ! ' 2 Lg is called the
unsimulation of L.
LEMMA 2.17 If L is determined by a class C of frames in which  is true
only at one point then Ls = LogfFs : F 2 Cg.
We are in a position now to formulate the main result of this section.
THEOREM 2.18 (Kracht 1996) The map L 7! Ls is an isomorphism from
the lattice NExtK2 onto the interval Sim K1  2?]. The inverse map
is L 7! Ls . Both these maps preserve tabularity, (global) FMP, (global)
Kripke completeness, decidability, interpolation, strong completeness, Rand D-persistence, elementarity.
Proof To prove the rst claim it suces to show that (Ls)s = L for every
L 2 Sim K  2?]. That L (Ls )s is clear. Consider the set C of all
di erentiated frames Fs such that F j= L and  is true only at one point in
F. By Lemma 2.17, C characterizes Ls . It is not dicult to show now that
the class fF+s : F 2 Cg is closed under subalgebras, homomorphic images
and direct products so it is a variety. Consequently, C is (up to isomorphic
copies) the class of all di erentiated frames for Ls .
Take a di erentiated frame F for (Ls )s . Then Fs j= Ls . So there exists
Gs 2 C which is isomorphic to Fs . Hence (Fs )s 
= (Gs )s and F j= L, since
G j= L. It follows that Ls is determined by fFs : F 2 Cg whenever L is
determined by C .
The preservation of tabularity, (global) FMP, (global) Kripke completeness, and strong completeness under both maps is proved with the help of
Lemma 2.17 and the observation above. It is also clear that L is decidable
whenever Ls is decidable. For the remaining (rather technical) part of the
proof the reader is referred to Kracht 1996] and Kracht and Wolter 1997a].

2

Besides its theoretical signicance, this theorem can be used to transfer
rather subtle counter-examples from polymodal logic to unimodal logic. For
instance, Kracht 1996] constructs a polymodal logic which has FMP and is
globally Kripke incomplete. By Theorem 2.18, we obtain a unimodal logic
with the same properties.

ADVANCED MODAL LOGIC

93

2.4 Minimal tense extensions
Now let us turn to tense logics which may be regarded as normal bimodal
logics containing the axioms p ! 21 32p and p ! 22 31p. Usually studies
in Tense Logic concern some special systems representing various models of
time, like cyclic time, discrete or dense linear time, branching time, relativistic time, etc. Such systems are discussed in Basic Tense Logic (see also
Gabbay et al. 1994] and Goldblatt 1987]). However, as before our concern
is general methods which make it possible to obtain results not only for this
or that particular system but for wide classes of logics. This direction of
studies in Tense Logic is quite new and actually not so many general results
are available. In this and the next section we consider two natural families
of tense logics|the minimal tense extensions of unimodal logics and tense
logics of linear frames. Our aim is to nd out to what extent the theory
developed for unimodal logics in NExtK and especially NExtK4 can be
\lifted" to these families.
The smallest tense logic K:t is determined by the class of bimodal Kripke
frames hW R R;1i in which R is the accessibility relation for 21 and R;1
for 22 . Frames of this type are known as tense Kripke frames general frames
of the form hW R R;1  P i will be called just tense frames. Notice that not
all unimodal general frames hW R P i can be converted into tense frames
hW R R;1  P i because P is not necessarily closed under the operation

32X = fx 2 W : 9y 2 X xR;1 yg:
For instance, in the frame F of Example 1.7 we have 32f! + 1g = f!g 62 P .
Each normal unimodal logic L = K  ; in the language with 21 gives rise
to its minimal tense extension L:t = K:t  ;. From the semantical point of
view L:t is the logic determined by the class of tense frames hW R R;1  P i
such that hW R P i j= L. The formation of the minimal tense extensions
is the simplest way of constructing tense logics from unimodal ones. Of
\natural" tense logics, minimal tense extensions are, for instance, the logics
of (converse) transitive trees, (converse) well-founded frames, (converse)
transitive directed frames, etc. The main aim of this section is to describe
conditions under which various properties of L are inherited by L:t.
Notice rst that unlike fusions, L:t is not in general a conservative extension of L, witness L = LogF where F is again the frame constructed in
Example 1.7: one can easily check that K4:t L:t. However, if L is Kripke
complete then L:t is a conservative extension of L and so L0 :t = L:t implies
L0 L. This example may appear to be accidental (as the rst examples of
Kripke incomplete logics in NExtK). However, we can repeat (with a slight
modication) Blok's construction of Theorem 1.35 and prove the following

94

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

THEOREM 2.19 If L is a union-splitting of NExtK or L = For, then
L0 :t = L:t implies L0 = L. Otherwise there is a continuum of logics in
NExtK having the same minimal tense extension as L.
It is not known whether there exists L 2 NExtK4 such that L:t is not a
conservative extension of L.
Theorem 2.19 leaves us little hope to obtain general positive results for
the whole family of minimal tense extensions. As in the case of unimodal
logics we can try our luck by considering logics with transitive frames. So in
the rest of this section it is assumed that the unimodal and tense logics we
deal with contain K4 and K4:t, respectively, and that frames are transitive.
But even in this case we do not have general preservation results: Wolter
1996b] constructed a logic L 2 NExtK4 having FMP and such that L:t is
not Kripke complete. However, the situation turns out to be not so hopeless
if we restrict attention to the well-behaved classes of logics in NExtK4,
namely logics of nite width, nite depth and conal subframe logics. First,
we have the following results of Wolter 1996a].
THEOREM 2.20 If L 2 NExtK4 is a logic of nite depth then L:t has
FMP. If L 2 NExtK4 is a logic of nite width then L:t is Kripke complete.
It is to be noted that tense logics of nite depth are much more complex
than their unimodal counterparts. For example, there exists an undecidable
nitely axiomatizable logic containing K4:t  21 21 ? (for details see Kracht
and Wolter 1997a]).
The minimal tense extensions of conal subframe logics were investigated
in Wolter 1995, 1996a].
THEOREM 2.21 If L 2 NExtK4 is a conal subframe logic then
(i) L:t is Kripke complete
(ii) L:t has FMP i L is canonical
(iii) L:t is decidable whenever L is nitely axiomatizable.
Before outlining the idea of the proof we note some immediate consequences for a few standard tense logics.
EXAMPLE 2.22 (i) The logic of the converse well-founded tense frames is
GL:t it does not have FMP but is decidable. (ii) The logic of the converse
transitive trees is K4:3:t it has FMP and is decidable. (iii) The logic of
the converse well-founded directed tense frames is GL:t  K4:2:t it does
not have FMP and is decidable.

Proof The proof of the negative part, i.e., that L:t does not have FMP if

L is not canonical, is rather technical it is based on the characterization of

ADVANCED MODAL LOGIC

95

the canonical conal subframe logics of Zakharyaschev 1996]. The reader
can get some intuition from the following example: neither Grz:t nor GL:t
has FMP. Indeed, the Grzegorczyk axiom

22 (22 (p ! 22 p) ! p) ! p
is refuted in h!  i and so does not belong to Grz:t however, it is valid
in all nite partial orders. The argument for GL:t is similar: take the Lob
axiom in 22 and the frame h! > <i.
We sketch now the proof of the positive part. For a tense Kripke frame
F = hW R R;1 i, let rp be a partial function associating with some clusters
in F one of the frames
h! > <i or h!  i:

We call it a replacement function for F and dene Frp to be the result of
replacing in F all clusters C in the domain of rp by (disjoint copies of) rpC .
Our rst observation is that for each conal subframe logic L, L:t is determined by a set of frames of the form Frp such that F is of nite depth.
Indeed, suppose ' 62 L:t and consider a countermodel M = hF Vi for '
based on a descriptive nitely generated tense frame F = hW R R;1  P i for
L:t. Say that a point x 2 W is non-eliminable (relative to ') if there are a
subformula  of ' and S 2 fR R;1g such that x 2 maxS fy 2 W : y j= g
or x 2 maxS fy 2 W : y j= :g. Denote by We the set of non-eliminable
points in W and construct a new model Me on the frame Fe = hWe  R
We  R;1 We i by taking Ve (p) = V(p) \ We for all variables p in '. Clearly,
the Kripke frame Fe is of nite depth (d(Fe )  2l('), to be more precise). Besides, using Theorem 1.23 one can easily show that (Me  y) j=  i
(M y) j= , for all  2 Sub' and y 2 We . (Note that Theorem 1.23 is applicable in this case, since hW R P i is descriptive whenever W R R;1  P
is descriptive.) Moreover, the R-reduct hWe  R We i of Fe is a conal subframe of the R-reduct hW Ri of the underlying Kripke frame of F. So Fe is
a frame for L:t whenever L is canonical (= D-persistent). However, this is
not so if L is not canonical.





EXAMPLE 2.23 Consider the frame F = hW R R;1  P i, where hW Ri is
the reexive point 1 followed by the chain h! >i and P consists of all
conite sets containing 1 and their complements. Then F j= GL:t but (for
an arbitrary ') Fe contains 1 and so Fe 6j= GL:t.
A rather tedious proof (see Wolter 1996a]) shows, however, that there
exists a replacement function rp for Fe such that Frp
e validates L:t and all
points in clusters from domrp are eliminable relative to R in F. (In the
example above we put rpf1g = h! > <i and 1 is eliminable relative to

96

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

R.) So let us assume that such rp is given and that its domain is empty if
rp rp
L is canonical. Dene a model Mrp
e = (Fe  V ) as follows. First we put
rp
y 2 V (p) whenever y 2 Ve (p) and y 2= domrp. Consider now a cluster
C = fa0 : : :  am;1 g in domrp. Vrp is dened in rpC by unravelling C into
the chain rpC  more precisely, we put
Vrp (p) \ rpC = fmj + i : j < ! ai 2 V(p)g:
Using the fact that domrp contains only R-eliminable points, one can show
by induction that, for every  2 Sub', (Me  y) j=  i (Mrp
e  y ) j=  , if
C (y) does not belong to domrp, and
fn 2 rpC : (Mrp
e  n) j=  g = fmj + i : j < ! (Me  ai ) j=  g

if a cluster C = fa0  : : :  am;1 g is in domrp. Thus Frp
e refutes ', which
proves that L:t is Kripke complete.
To show that all canonical logics L:t do have FMP we reduce Frp
e once
again. Dene an equivalence relation  on We by induction on the R-depth
dR (x) of a point x in Fe . Suppose that dR (x) = dR (y) and  is already
dened for all points of R-depth < dR (x) and put x  y if the following
conditions are satised: (a) x j=  i y j= , for all  2 Sub' (x ' y, for
short), (b) if z is an R-successor of y and C (z ) 6= C (y) then there exists an
R-successor z 0 of x with C (z 0 ) 6= C (x) such that z  z 0 and vice versa, (c)
the cluster C (x) is degenerate i C (y) is degenerate, (d) rpC (x) = rpC (y),
(e) for each z 2 C (x) there exists z 0 2 C (y) such that z ' z 0 and vice
versa.
Let x] denote the equivalence class generated by x. Dene a frame
G = hV S S ;1 i by taking V = fx] : x 2 We g, and x]S y] i there are
x0 2 x] and y0 2 y] such that x0 Ry0 . Since Fe is of nite depth, V is
nite. Moreover, the map x 7! x] is a reduction of the unimodal frame
hWe  R We i to hV S i. It follows that G is a frame for L:t whenever L is
canonical. Dene a valuation in G by putting x] j= p i x j= p, for all
x 2 We and all variables p in '. Then one can show that x] j=  i x j= ,
for all  2 Sub'. So G 6j= ', as required, which means that L:t has FMP.
To prove the decidability of a nitely axiomatizable L:t we rst show its
completeness with respect to a rather simple class of frames.
Dene a replacement function rf for G as follows. For each cluster C in
Fe the set C ] = fx] : x 2 C g is a cluster in G, and moreover, every cluster
in G can be presented in this way. So we put rf C ] = rpC , for all clusters
C ] in G. Notice that by (d), rf is well-dened. It is easily shown now that
rf
rf
the R-reduct of Frp
e is reducible to the R-reduct of G and that G refutes
'. Thus we obtain

ADVANCED MODAL LOGIC

97

LEMMA 2.24 For each conal subframe logic L,

L:t = LogfGrp : Grp j= L:t G nite, rp a replacement function for Gg:
So, to establish the decidability of a nitely axiomatizable L:t it is enough
now to present an algorithm which is capable of deciding, given an rp for a
nite G and ', whether Grp j= '. To this end we require the notion of a
cluster assignment t = ht1  t2 i in a tense frame G, which is any function from
the set of clusters in G into the set fm jg'fm jg such that tC = (m m) if C
is degenerate (here m and j are just two symbols m stands for \maximal"
and j for \joker"). A valuation V in G is called '-good for (G t) if the
following conditions hold:
 if t1 C = j then C \ maxR (V()) = , for all  2 Sub'
 if t2 C = j then C \ maxR 1 (V()) = , for all  2 Sub' .
;

EXAMPLE 2.25 Let F be the frame constructed in Example 2.23 and suppose that tf1g = (j m). Then each valuation V in F is '-good for (G t)
no matter what ' is, because 1 is eliminable relative to R. The point 1
is not R;1 -eliminable, since 1 2 maxR 1 (>).
;

Given a formula ', a nite frame F and a replacement function rp for
F, we construct a nite frame G = hV S S ;1 i with a cluster assignment
t as follows. Let k be the number of variables in '. Then G is obtained
from Frp by replacing every rpC = h! > <i with a non-degenerate cluster
C 0 of cardinality 2k , S -followed by a chain of 2l(') irreexive points, and
by replacing every rpC = h!  i with a non-degenerate cluster C 0 of
cardinality 2k , S -followed by a chain of 2l(') reexive points. The cluster
assignment t in G is dened by putting tC 0 = (j m), for all new clusters
C 0 of cardinality 2k , and tC 0 = (m m), for all the other clusters. It is
not dicult now to prove that Frp j= ' i (G U) j= ', for all '-good for
(G t) valuations U in G. This equivalence provides an e ective procedure
for deciding whether Frp j= '.
2
Note that a similar technique can be used to prove completeness and
decidability of various tense logics that are not minimal tense extensions.
For instance, all logics of the form L:t  3222 p ! 22 32p, where L is a
conal subframe logic, are complete and decidable if nitely axiomatizable.

2.5 Tense logics of linear frames





One of the most important types of tense logics are logics characterized
by linear tense frames, i.e., transitive frames W R R;1  P such that, for

98

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

all x y 2 W , xRy or xR;1 y or x = y. For example, Bull 1968] and
Segerberg 1970] axiomatized the logics of the frames, hZ < >i, hQ  < >i
and hR < >i (Z, Q and R are the sets of integer, rational and real numbers,
respectively).
Linear tense logics form the lattice NExtLin, where



Lin = K4:t  3132p _ 3231p ! p _ 31p _ 32p



is the tense logic determined by the class of all linearly ordered Kripke
frames W R R;1 . As we saw in Section 1.11, even unimodal logics of
linear orders are rather non-trivial (for instance, they do not always enjoy
FMP). Yet they can be characterized by Kripke frames with a transparent structure, which yields a decision algorithm for those of them that are
nitely axiomatizable. Tense logics of linear frames turn out to be even more
complicated. In fact, one can nd almost all kinds of \monsters" among
them: uncountably many logics without Kripke frames, strongly complete
logics that are not canonical, canonical logics that are not R-persistent,
incomplete subframe logics, etc. Nevertheless, in this section we show that
these logics are quite manageable. Our exposition follows Wolter 1996c,d],
where the reader can nd the omitted details. All frames in this section are
assumed to be linear.
Given a nite sequence F = hFi = hWi  Ri  Pi i : 1  i  ni of disjoint
frames, we denote by F] = F1  : : :  Fn the ordered sum of them, i.e., the
frame W R R;1  P in which




n
n
 (Wi ' Wj )
W = Wi  R = Ri 
i=1

i=1

1i<j n

and P = fX1  : : :  Xn : Xi 2 Pi g. Each nite frame can be represented
then as the ordered sum C1  : : :  Cn of its clusters.
We begin our study by developing a language of \canonical formulas" for
axiomatizing logics in NExtLin and characterizing the constitution of their
frames. It will play the same role as the language of canonical formulas for
K4. With every nite frame F = hW R R;1i = C1  : : :  Cn and a cluster
assignment t = (t1  t2 ) in it we associate the formula

(F t) = (F t) ^ 21 (F t) ^ 22 (F t) ! :pr 
where r is an arbitrary xed point in F and
(F t) =

^fpx ! 3 py : xRy :(yRx)g ^
^fpx ! 3 py : xR y :(xRy)g ^
1
2

;1

ADVANCED MODAL LOGIC

^fpx ! :py : x 6= yg ^ ^fpx ! :3 py : :(xRy)g ^
^fpx ! 3 py : 9i  n (t Ci = m ^ x y 2 Ci ^ xRy)g ^
^fpx ! 3 py : 9i  n (t Ci = m ^ x y 2 Ci ^ xR y)g ^
_fpy : y 2 W g:

99

2

1

1

2

2

;1

To explain the semantical meaning of these formulas, notice rst that if
tC = (m m) for all clusters C then G 6j= (F t) i G is reducible to F so
Lin  (F t) is a splitting of NExtLin. Suppose now that tiC = j for some
i 2 f1 2g and some cluster C in F. In this case G 6j= (F t) i there exist
frames Gi , for 1  i  n, such that G = G1  : : :  Gn and Gi 6j= (Ci  t Ci )
for all 1  i  n. So it suces to examine the situation when G 6j= (C t)
for a cluster C . Assume for simplicity that G is a Kripke frame. Case 1:
tC = (j j). Then G 6j= (C t) i jGj jC j. Case 2: tC = (m j). Then C is
non-degenerate and G 6j= (C t) i either G contains an R-nal cluster of
cardinality jC j or it has no R-nal point at all. Case 3: tC = (j m). This
is the mirror image of Case 2. Case 4: tC = (m m). If C is an irreexive
point then G is an irreexive point as well whenever G 6j= (C t). If C is
non-degenerate and G 6j= (C t) then G satises the conditions of Cases 2
and 3.
EXAMPLE 2.26 Let  = (a-b t) where ta = (m j) and tb = (j m).
Then F 6j=  i there exists a non-empty upward closed set X 2 P such
that 8x 2 X 9y 2 X yRx, W ; X 6=  and 8px 2 W ; X 9y 2 W ; X xRy.
Hence hQ  < >i 6j=  (take X = fy 2 Q : 2 < yg) but hR < >i j= ,
since the real line contains no gaps.
THEOREM 2.27 There is an algorithm which, given a formula ', returns
formulas (F1  t1 ) : : :  (Fn  tn ) such that
Lin  ' = Lin  (F1 t1 )  : : :  (Fn tn ):
Proof Let (Fi  ti), 1  i  n, be the collection of all nite frames with type
assignments such that, for each i, (a) there is a countermodel Mi = hFi  Vi i
for ' in which Vi is '-good for (Fi  ti ), (b) the depth of Fi does not exceed
4l(') + 1, and (c) no cluster in Fi contains more than 2v(') points, where
v(') is the number of variables in '.
Let F refute (Gi  ti ) under a valuation U. By the denition of (Fi  ti ),
the model Mi refutes '. Dene a valuation U0 in F by taking, for all variables
p in ',
U0 (p) = fU(px) : x 2 Vi (p)g:
It is not hard to show by induction that U0 () = fU(px) : x 2 Vi ()g
for all  2 Sub', and so F refutes ' under U0 . Thus F j= ' implies



S

100

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

Ordt = Logfh < >i :  an ordinalg =
Lin  (; ( (j m)))
Et
= Lin  31>  32> =
Lin  (; ( (m m)))  (( (m m)) ;)
On = Logh!n < >i =
Ordt  ((| (m j))  :{z: :  ( (m j)))} (; ( (m m)))

RD
LD
Zt

Dsn
Qt
Rt
Rdt

n+1

= LogfG : 8x(:xRx ! 9y(xRy ^ fz : xRzRyg = ))g =
Lin  (; ( (m m)))  (; ( (m m))  ( (m j)))
= the mirror image of RD
= LoghZ < >i =
RD  LD  (( (j j))  ( (j m)))
(( (m j))  ( (j j)))
= Lin  2n1 +1 p ! 2n1 p =
Lin  (; ( (m m)  : : :  ( (m m)) ;)

|

{z

n+1

= LoghQ  < >i =
Ds1  Et
= LoghR < >i =
Qt  (( (m j))  ( (j m)))
= Logfh  i :  an ordinalg =
Lin  (; (#2  (j m)))

}

Table 3. Axiomatizations of standard tense logics

F j= (Fi  ti ) for every i. The converse direction is rather technical we
refer the reader to Wolter 1996d].
2
\Canonical" axiomatizations of some standard linear tense logics are
shown in Table 3, where we use the following abbreviations. Given a nite frame F = C1  : : :  Cn , we write ((C1  tC1 )  : : :  (Cn  tCn ))
instead of (F t) and (; (C1  tC1 )  : : :  (Cn  tCn )) instead of

((C1  tC1 )  : : :  (Cn  tCn ))  (( (j j))  (C1  tC1 )  : : :  (Cn  tCn )):
((C1  tC1 )  : : :  (Cn  tCn ) ;) is dened analogously.
T
Now we exploit the formulas (F t) to characterize the -irreducible

ADVANCED MODAL LOGIC

101

logics in NExtLin. Recall that every logic L 2 NExtL0 is represented as

\

L = fL0  L : L0 is

\ -irreducibleg:
T

So such a characterization can open the door to a better understanding of
the structure of the lattice NExtLin. The -irreducible logics will be described semantically as the logics determined by certain descriptive frames.
DEFINITION 2.28 (1) Denote by #
k the non-degenerate cluster with k > 0
points.
(2) Let !< (0) be the strictly ascending chain h! < >i of natural numbers, !<(1) the chain h!  i, !< (2) the ascending chain of natural numbers in which precisely the even points are reexive, !< (3) the chain in
which precisely the multiples of 3 are reexive, and so on !> (n) is the
mirror image of !< (n).
(3) C(0 #
1 ) is the mirror image of the frame introduced in Example 2.23,
i.e., C(0 #
1 ) = h! < (0)  #
1  P i, where P consists of all conite sets containing #
1 and their complements. We generalize this construction to chains
!< (n) and clusters #k . Namely, for n < !, k > 1 and #k = fa0  : : :  ak;1 g,
we put
C(n #k ) = h!< (n)  #k  P i
where P is the set of possible values generated by fXi : 0  i  k ; 1g, for
Xi = fai g  fkj + i : j 2 !g, 0  i  k ; 1. C(#k  n) denotes the mirror
image of C(n #
k ).
(4) C(0 #
1  0) = h! < (0)  #
1  ! > (0) P i, where P consists of all conite
sets containing #
1 and their complements.
It is easy to check that the frames dened in (3) and (4) are descriptive
and a singleton fxg is in P i x 62 #
k.
For a class of frames C , we denote by C the class of nite sequences of
frames from C and let C ] = fF] : F 2 C g. The class of nite clusters
and the frames of the form (3) in Denition 2.28 is denoted by B0  put also
B = fC(0 #
1  0)g  B0 .
THEOREM 2.29 Each logic L 2 NExtLin is determined by a set C B ].
If L is nitely axiomatizable then L = LogC for some set C B0 ].
Proof We explain the idea of the proof of the rst claim. Suppose that
M = hF Vi is a countermodel for  = ((C1  tC1 )  : : :  (Cn  tCn )) based
on a descriptive frame F = hW R R;1 P i. We must show that there exists
G 2 B ] refuting  and such that LogG  LogF. Consider the sets

_

Wi = fy 2 W : (M y) j= fpx : x 2 Ci gg:

102

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

One can easily show that Wi are intervals in F and F = F1  : : :  Fn , for
the subframes Fi of F induced by Wi . Moreover, G = G] is as required
if G = hG1  : : :  Gn i is a sequence in B such that LogGi  LogFi , and
Gi 6j= (Ci  tCi ), for 1  i  n. Frames Gi with those properties are
constructed in Wolter96d].
2
EXAMPLE 2.30 The logic Qt is determined by the frames F 2 B ] which
contain no pair of adjacent irreexive points, and Rt is determined by the
frames F 2 B ] which contain neither a pair of adjacent irreexive points
nor a pair of adjacent non-degenerate clusters.

T

It is not dicult to show now that the logics LogF, for F 2 B ], coincide
with the -irreducible logics in NExtLin. Our rst aim is achieved, and
in the remaining part of this section we shall draw consequences of this
result. Using the same sort of arguments as in the proof of Theorem 2.21
and Kruskal's 1960] Tree Theorem one can prove
COROLLARY 2.31 (i) All nitely axiomatizable logics in NExtLin are decidable.
(ii) A logic L is nitely axiomatizable whenever there exists n < ! such
that L 2 NExtDsn .
It follows in particular that all logics in NExtQt and all logics of reexive
frames are nitely axiomatizable and decidable.
Now we formulate two corollaries concerning the Kripke completeness of
linear tense logics. First, it is not hard to see that every logic in NExtLin
characterized by an innite frame in B ] is Kripke incomplete. Using this
observation one can prove
COROLLARY 2.32 Suppose L 2 NExtLin and there is a Kripke frame of
innite depth for L. Then there exists a Kripke incomplete logic in NExtL.
This result means in particular that in Tense Logic we do not have analogues of the unimodal completeness results of Bull 1966b] and Fine 1974c].
However, if a logic is complete then it is determined by a simple class of
frames. Let K be the class frames containing nite clusters and frames of
the form (2) in Denition 2.28.
THEOREM 2.33 Each Kripke complete logic in NExtLin is determined by
a subset of K ].
One of the main types of logics considered in conventional Tense Logic
are logics determined by strict linear orders, known also as time-lines. We
call them t-line logics. All logics in Table 3, save Rdt , are t-line logics.

ADVANCED MODAL LOGIC

103

T-line logics were dened semantically, and now we are going to determine
a necessary syntactic condition for a linear tense logic to be a t-line logic.
Given a frame F, we denote by F the frame that results from F by
replacing its proper clusters with reexive points. Call L 2 NExtLin a
t-axiom logic if L is axiomatizable by a set of formulas of the form (F t)
in which F contains no proper clusters.
PROPOSITION 2.34 The following conditions are equivalent for all logics
L 2 NExtLin:
(i) L is a t-axiom logic
(ii) F j= L implies F j= L, for every F 2 B ].
(iii) (G t) 2 L implies (G  t) 2 L,15 for every nite G.

Proof The implications (i) ) (ii) and (iii) ) (i) are clear. To prove that
(ii) ) (iii), suppose (G  t) 62 L. Then there exists a frame F 2 B ] for L
refuting (G  t). Without loss of generality we may assume that F contains
no proper clusters. By enlarging some clusters in F we can construct a frame
H 2 B ] such that H = F and H 6j= (G t). In view of (ii), H j= L and so
(G t) 62 L.
2
It follows that the t-axiom logics form a complete sublattice of the lattice
NExtLin.
THEOREM 2.35 (i) All nitely axiomatizable t-axiom logics are Kripke
complete.
(ii) All t-line logics are t-axiom logics.

Proof (i) Suppose that L = Lin  f(Gi  ti ) : i 2 I g, for some nite set

I . By Theorem 2.29, L is determined by a subset of B0 ]. For F 2 B0 ],
let kF be the Kripke frame that results from F by replacing all C(n #
k)
<
>
and C(#
k  n) with ! (n) and ! (n), respectively. Then we clearly have
LogkF LogF, and F j= (G  t) i kF j= (G  t). It follows that L is
Kripke complete. (ii) Suppose that L is a t-line logic. By Proposition 2.34
(3), it suces to observe that F j= (G  t) i F j= (G t), for all time-lines
F and all nite G.
2
So the fact that in Table 3 all t-line logics are axiomatized by canonical formulas of the form (G  t) is no accident. Finding and verifying
axiomatizations of t-line logics becomes almost trivial now.
EXAMPLE 2.36 Let us check the axiomatization of Zt in Table 3. Put
L = RD  LD  (( (j j))  ( (j m)))  (( (m j))  ( (j j))):
15 We assume that tC = t whenever  replaces C in G.

104

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

By Theorem 2.35, L is complete. By Theorem 2.33, L is then determined by
a subset of K ]. Clearly this set contains hZ < >i, possibly #
k for k > 0,
and nothing else. But the logic of #
k contains Zt , for all k > 0.
We conclude this section by discussing the decidability of properties of
logics in NExtLin. In Section 4.4 it will be shown that almost all interesting
properties of calculi are undecidable in NExtK and even in NExtS4. In
NExtLin the situation is di erent, as was proved in Wolter 1996d, 1997d].
THEOREM 2.37 (i) There are algorithms which, given a formula ', decide
whether Lin  ' has FMP, interpolation, whether it is Kripke complete,
strongly complete, canonical, R-persistent.
(ii) A linear tense logic is canonical i it is D-persistent i it is complete
and its frames are rst order denable.
(iii) If a logic in NExtLin has a frame of innite depth then it does not
have interpolation.
So NExtLin provides an interesting example of a rather complex lattice
of modal logics for which almost all important properties of calculi are
decidable. We shall not go into details of the proof here but discuss quite
natural criteria for canonicity and strong completeness of logics in NExtLin
required to prove this theorem. Denote by B+ the class of frames containing
B together with frames C(n1  #
k  n2 ) dened as follows. Suppose k > 1,
n1  n2 < ! are such that n1 + n2 > 0 and #k = fa0  : : :  ak;1 g. Then

C(n1  #k  n2 ) = h!< (n1 )  #k  !> (n2 ) P i
where P is the set of possible values generated by fXi : 0  i  k ; 1g, for
Xi = fai g  fkj + i : j 2 !g  fk j + i : j 2 !g
and f0  1  : : :  n  : : :g being the points in !>(n2 ).
Let F be the class of frames of the form
hf0 : : :  n1 g < >i  #
1  hf0 : : :  n2 g < >i or hf0 : : :  ng < >i :
THEOREM 2.38 (i) A logic L 2 NExtLin is canonical i the underlying
Kripke frame of each frame F 2 B+ ] for L validates L as well.
(ii) A logic L 2 NExtLin is strongly complete i for each frame F 2 B+]
validating L, there exists a Kripke frame G for L which results from F by
replacing
 every C(n #
k ) with ! < (n) or ! < (n)  H  #
k , for some H 2 F , and

 every C(#
k  n) with ! > (n) or #
k  H  ! > (n), for some H 2 F , and

ADVANCED MODAL LOGIC

105

 every C(n1  #
k  n2 ) with ! < (n1 )  H  ! > (n2 ), for some H 2 F .

EXAMPLE 2.39 The logic Rt is not canonical because C(2 #
2 ) j= Rt but
!< (2)  #2 6j= Rt . However, Rt is strongly complete, since F j= Rt whenever
G 2 B+] validates Rt and F is obtained from G as in the formulation of
Theorem 2.38 with H =  2 F .
One can also use Theorem 2.38 to construct two strongly complete logics

L1  L2 2 NExtLin whose sum L1  L2 is not strongly complete (see Wolter

1996c]).

2.6 Bimodal provability logics
Bimodal provability logics emerge when combinations of two di erent provability predicates are investigated, for example, if 21 is understood as \it
is provable in PA" and 22 as \it is provable in ZF". In contrast to the
situation in unimodal provability logic, where almost all provability predicates behave like the necessity operator 2 in GL, there exist quite a lot
of di erent types of bimodal provability logics. Various completeness results extending Solovay's completeness theorem for GL to the bimodal case
were established by Smorynski 1985], Montagna 1987], Beklemishev 1994,
1996] and Visser 1995]. Here we will not deal with the interpretation of
modal operators as provability predicates but sketch some results on modal
logics containing the bimodal provability logic

CSM0 = (GL & GL)  21p ! 22 p  22p ! 2122 p
(named so by Visser 1995] after Carlson, Smorynski and Montagna). A
number of provability logics is included in this class, witness the list below.
(As in unimodal provability logic we have quasi-normal logics among them,
i.e., sets of formulas containing K2 and closed under modus ponens and
substitutions (but not necessarily under '=2i '). Recall that we denote by
L + ; the smallest quasi-normal logic containing L and ;.)
 CSM1 = CSM0  22 (21 p ! p). (This is PRLZF in Smorynski
1985] and F in Montagna 1987].)
 NB1 = CSM0  (:21 p ^ 22 p) ! 22 (21 q ! q).

 CSM2 = CSM1 + 21 p ! p. (This is PRLZF + Reection21 in
Smorynski 1985] and F1 in Montagna 1987].)

 CSM3 = CSM2 + 22 p ! p. (This is PRLZF + Reection22 in
Smorynski 1985].)

106

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

 NB2 = NB1 + 22 p ! p + 22 p ! 21 p.

A remarkable feature of CSM0 is that|like in GL|we have uniquely determined denable xed points.
THEOREM 2.40 (Smorynski 1985) Let '(p) be a formula in which every
occurrence of p lies within the scope of some 21 or some 22 . Then
(i) there exists a formula  containing only the propositional variables of
'(p) dierent from p such that  $ '() 2 CSM0 
(ii) 21 ((p $ '(p)) ^ (q $ '(q))) ! (p $ q) 2 CSM0 .
In the remaining part of this section we are concerned with subframe
logics containing CSM0 , the main result stating that those of them that
are nitely axiomatizable are decidable. All the provability logics introduced
above turn out to be subframe logics, so we obtain a uniform proof of their
decidability. An interesting trait of subframe logics in ExtCSM0 is that
(as a rule) they are Kripke incomplete in the list above such are CSMi ,
i = 1 2 3, and NBi , i = 1 2. The proof extends the techniques introduced
by Visser 1995] for details we refer the reader to Wolter 1997a].
First we develop|as was done for NExtK4 and NExtLin|a frame theoretic language for axiomatizing subframe logics in the lattice ExtCSM0 .
A nite frame G = hW R1  R2 i validates CSM0 i both R1 and R2 are
transitive, irreexive, R2 R1 and
8x y z (xR1 y ^ yR2 z ! xR2 z ):

In this section all (not only nite) frames are assumed to satisfy these conditions, save irreexivity.
A nite frame F is called a surrogate frame if it has precisely one root
r and all points di erent from r are R2 -irreexive. Surrogate frames will
provide the language to axiomatize subframe logics in ExtCSM0 . A normal
surrogate frame hW R1  R2 i is a surrogate frame in which the root r is
R1 -irreexive. We write xRip y i xRi y and :yRi x. Given a frame G =
hV S1  S2  Qi for CSM0 and a surrogate frame F = hW R1  R2 i, a map h
from V onto W is called a weak reduction of G to F if for i 2 f1 2g and all
x y 2 V ,
 xSi y implies f (x)Ri f (y),
 f (x)Rip f (y) implies 9z 2 V (xSi z ^ f (z ) = f (y)),
 f ;1(X ) 2 Q for all X W .
(The standard denition of reduction is relaxed here in the second condition.) Each weak reduction to a CSM0 -frames is a usual reduction, since in

ADVANCED MODAL LOGIC

107

this case Rip = Ri . A frame G is said to be weakly subreducible to a surrogate frame F if a subframe of G is weakly reducible to F. To describe weak
subreducibility syntactically, with each surrogate frame F = hW R1  R2 i we
associate the formula
(F) = (F) ^ 21 (F) ! :pr 
where r is the root of F and
(F) =
fpx ! 31py : xR1p y x y 2 W g ^
fpx ! 32py : xR2p y x y 2 W g ^
fpx ! :py : x 6= y x y 2 W g ^
fpx ! :31 py : :(xR1 y) x y 2 W g ^
fpx ! :32 py : :(xR2 y) x y 2 W g:

^
^
^
^
^

LEMMA 2.41 For every surrogate frame F and every CSM0 -frame G, G 6j=
(F) i G is weakly subreducible to F.
It follows immediately that CSM0  (F) and CSM0 + (F) are subframe
logics. Conversely, we have the following completeness result.
THEOREM 2.42 (i) There is an algorithm which, given a formula ' such
that CSM0 + ' is a subframe logic, returns surrogate frames F1  : : :  Fn for
which
CSM0 + ' = CSM0 + (F1) + : : : + (Fn):
(ii) There is an algorithm which, given a formula ' such that CSM0  '
is a subframe logic, returns normal surrogate frames F1  : : :  Fn such that
CSM0  ' = CSM0  (F1)  : : :  (Fn):
Table 4 shows axiomatizations of the logics introduced above by means of
formulas of the form (F). In this section we adopt the convention that in
gures we place the number 1 nearby an arrow from x to y if xR1 y and
:xR2 y. An arrow without a number means that xR2 y (and therefore xR1 y
as well).
The proof of decidability is based on the completeness of subframe logics
in ExtCSM0 with respect to rather simple descriptive frames. With every
surrogate frame F we associate a nite set of frames E(F) = fFA : A 2
SeqFg. Loosely, it is dened as follows. Let us rst assume that the root r
of F is R2 -irreexive. Then the frames in E(F) are the results of inserting an
innite strictly descending R1 -chain, denoted by C (!), between each nondegenerate R1 -cluster C and its R1 -successors. This denes R1 uniquely.

108

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

CSM1
CSM0 + 21p ! p
CSM0 + 22p ! p


= CSM0  ( 6)
= CSM0 + ()

= CSM0 + ( 1 )
1
CSM0 + 22p ! 21 p = CSM0 + ( 61 )
 1-
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
1
1
@
;
@
;
NB1
= CSM0  (  )  (  )
 1-
 -
I
@

;
I ;
@

1
( @; )  ( @;1 )
Table 4. Axiomatizations of provability logics
However, R2 may be dened in di erent ways, since a point R2 -seeing a
point in C need not (but may) R2 -see certain points in the chain C (!).
To be more precise, the set SeqF consists of all sequences A of the form

A = hAx : xR1 x x 2 W i.
where Ax is a subset of fy 2 W ; C : yR2 xg such that for all y and z ,
y 2 Ax and zR1y imply z 2 Ax . For each non-degenerate R1 -cluster C ,
denote by C (!) the set f(n C ) : n 2 !g. Finally, given A 2 SeqF, we
construct FA = hV S0  S1 i as the frame satisfying the following conditions:
 V = W  fC (!) : C a non-degenerate R1 -cluster in Fg
 Ri = Si \ (W ' W ), for i 2 f1 2g
 S1 is dened so that C (!) becomes an innite descending chain between C and its immediate successors
 for every non-degenerate R1 -cluster C ,
{ ((C (!)  C ) ' (C (!)  C )) \ S2 = ,
{ for all y 2 W ; C and x 2 C (!), xS2y i CR2y,
{ for all y 2 W ; C , C = fj : 0  j  m ; 1g and x 2 C (!), yS2x
i 9i 2 !9j  m ; 1 (x = (im + j C ) ^ y 2 Aj ),
{ for all x 2 C (!) and y 2 V ; C , xS2y i CS2y.
We illustrate this technical denition by a simple example.

S

ADVANCED MODAL LOGIC



6



6



6

c 1-d





..
.
 1-







6 6

a

(a)

b

6 6



(b)

109
-
6



6
-
6


..
.
1
-

6 6





(c)

Figure 12.
EXAMPLE 2.43 Construct E(F) for the frame F in Fig. 12 (a). In this
case we have two R1 -reexive points, namely c and d. So, SeqF consists of
pairs hAc  Ad i. There are four di erent pairs and so we have four frames
in E(F): the frame in Fig. 12 (b) is Fhi and that in (c) is Fhfagfbgi.
Fhfbgi is obtained from Fhfagfbgi by omitting the R2 -arrows starting from
a, save the arrow to c, and Fhfagi is obtained from Fhfagfbgi by omitting
the R2 -arrows starting from b, save the arrow to d.
Suppose now that the root r of F = hW R1  R2 i is R2 -reexive. We dene
FA as in the previous case, but this time we also insert an innite strictly
descending R2 -chain C (!) between r and its R1 -successors.
We have dened the relational component of our frames and now turn to
their sets of possible values. Given FA = hV S1  S2 i and a non-degenerate
R1 -cluster C = fj : 0  j  m ; 1g in F, let
PC = ffj g  f(im + j C ) : i 2 !g : j = 0 : : :  m ; 1g
and denote by P the closure of
ffxg : x 2 V :xS1 xg  fPC : C is a non-degenerate R1 -cluster in Fg
under intersections and complements in V . The resultant general frame is
denoted by G(FA ) = hV S1  S2  P i. One can check that it is a descriptive
frame for CSM0 . The following completeness result is proved similarly to
that in Section 2.4.
THEOREM 2.44 (i) Each subframe logic in NExtCSM0 is determined by
a set of frames of the form G(FA ), in which F is a normal surrogate frame
and A 2 SeqF.

110

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV





(ii) Each subframe logic in ExtCSM0 is determined by a set of frames
with distinguished worlds of the form G(FA ) r in which F is a surrogate
frame with root r and A 2 SeqF.
As a consequence of Theorem 2.44 and the fact that, for each surrogate
frame F with root r and each A 2 SeqF, both the logics of G(FA ) and
G(FA ) r are decidable, we obtain
THEOREM 2.45 All nitely axiomatizable subframe logics in ExtCSM0
are decidable.
We conjecture that the method above can be extended to logics without
the GL-axioms, i.e., all nitely axiomatizable subframe logics containing
(K4 & K4)  21 p ! 22 p  22 p ! 21 22 p are decidable.





3 SUPERINTUITIONISTIC LOGICS
