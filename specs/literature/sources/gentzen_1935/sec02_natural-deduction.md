<!-- Source: Gentzen, G. (1935). Untersuchungen über das logische Schließen (Investigations into Logical Deduction). Section II: The Calculus of Natural Deduction (NJ, NK). BibKey: Gentzen1935 -->

0 1. Examples of natural deduction
We wish to set up a formalism that reflects as accurately as possible the
actual logical reasoning involved in mathematical proofs.
By means of a number of examples we shall first of all show what form
deductions tend to take in practice and shall examine, for this purpose,
three 'true formulae' and try to see their truth in the most natural way
possible.
1.1. First example:
( X v  (Y & 2)) =i ( ( X v  Y )  & ( X v  2)) is to be established as a true
formula (H.-A., p. 28, formula 19).
The argument runs as follows: Suppose that either X or Y & Z holds.
We distinguish the two cases: 1. X holds, 2. Y & 2 holds. In the first case
it follows that X v  Y holds, and also X v  Z; hence ( X v  Y )  & ( X v  Z )
also holds. In the second case Y & Z holds, which means that both Y and Z
hold. From Y follows X v Y; from 2 follows X v Z .  Thus ( X  v Y )  & ( X  v Z )
again holds. The latter formula has thus been derived, generally, from
Xv(Y&Z),i.e.,(Xv(Y&Z)) 3 ( ( X v Y ) & ( X v Z ) )  holds.
1.2. Second example:
(3x v y  Fxy) 3
(Vy 3x Fxy).
(H.-A., formula 36, p. 60). The argument runs as follows: Suppose there
is an x such that for all y Fxy holds. Let a be such an x. Then for all y:

---

5 2, CONSTRUCTION OF THE CALCULUS NJ
Fay holds. Now let b be an arbitrary object. Then Fab holds. Thus there is
an x, viz., a, such that Fxb holds. Since b was arbitrary, our result therefore
holds for all objects, i.e., for all y there is an x such that Fxy holds. This
yields our assertion.
1.3. Third example:
(1
3x Fx) 3 (Vy 1
Fy) is to be established as intuitionistically true.
We reason as follows: Assume there is no x for which Fx holds. From
this we wish to infer: For all y ,
Fy holds. Now suppose a is some object
for which Fa holds. It then follows that there is an x for which Fx
holds, viz., a is such an object. This contradicts our hypothesis that
1 3 x  Fx. We have therefore a contradiction, i.e., Fa cannot hold. But
since a was completely arbitrary, it follows that for all y ,
Fy holds.
Q.E.D.
We intend now to integrate proofs of the kind carried out in these three
examples into an exactly defined calculus (in 5 4, we shall show how these
examples are presented in that calculus).
Q 2. Construction of the Calculus NJ
2.1. We intend now to present a calculus for 'natural' intuitionist derivations
of true formulae. The restriction to intuitionist reasoning is only provisional;
we shall explain below (cf. 5 5) our reasons for doing so and shall show in
what way the calculus has to be extended for classical reasoning (by in-
cluding the law of the excluded middle).
Externally, the essential difference between 'NJ-derivations' and deriva-
tions in the systems of Russell, Hilbert, and Heyting is the following:
In the latter systems true formulae are derived from a sequence of 'basic
logical formulae' by means of a few forms of inference. Natural deduction,
however, does not, in general, start from basic logical propositions, but
rather from assumptions (cf. examples in 5 1) to which logical deductions
are applied. By means of a later inference the result is then again made
independent of the assumption.
2.2. After this preliminary remark we define the concept of an NJ-derivation
as follows:
Calculi of the former kind will be referred to as logistic calculi.
(Examples in 4 4.)
An NJ-derivation consists of formulae arranged in tree form (13.3).
(By demanding that the formulae are arranged in tree form we are

---

deviating somewhat from the analogy with actual reasoning. This is so,
since in actual reasoning we necessarily have (1) a linear sequence of
propositions due to the linear ordering of our utterances, and (2) we are
accustomed to applying repeatedly a result once it has been obtained,
whereas the tree form permits only of a single use of a derived formula.
These two deviations permit us to define the concept of a derivation in a
more convenient form and are not essential.)
The initial formulae of the derivation are assumption formulae. Each
of these is adjoined to precisely one D-inference figure (and in fact occurs
'above' (1.3.5) the lower formula of that figure, as will be explained more
fully below).
All formulae occurring below an assumption formula, but still above the
lower formula of the D-inference figure to which that assumption formula
was adjoined, the assumption formula itself included, are said to depend
on that assumption formula. (Thus the inference makes all succeeding
propositions independent of the assumption which is correlated with it.)
According to what we have said the endformula of the derivation depends
on no assumption formula.
2.21. We shall now state the permissible inferenceJigures.
The inference figure schemata below are to be understood in the following
way:
We obtain an NJ-inference figure from one of the schemata by replacing
%, By 6, 5B by arbitrary formulae; and Vx 7&
( 3 ~
Sx) by an arbitrary
formula containing V(3) for its terminal symbol, where F designates the
bound object variable belonging to that terminal symbol; and Sa by the
formula obtained from 3~ by replacing the bound variable F, wherever it
occurs, by the free object variable a.
(For a we may, for instance, take a variable already occurring in 3s.
For the inference figures V-I and 3-E, this possibility will, however, be
excluded by the restrictions on variables which follow below, but it remains
for V-E and 3-1. Nor need b occur at all in Sx,
in which case Sa is, of
course, identical with ST.
- Sa is obviously always a subformula of Vb 31
(3b 3b), according to the definition of a subformula in 1.2.2.)
Symbols written in square brackets have the following meaning: An
arbitrary number (possibly zero) of formulae of this form, all formally
identical, may be adjoined to the inference figure as assumption formulae.
They must then be initial formulae of the derivation and occur, moreover,
in those paths of the proof to which the particular upper formula of the
inference figure belongs. (Le., that upper formula above which the square

---

52, CONSTRUCTION OF THE CALCULUS NJ
77
bracket occurs in the scheme. This formula may itself be an assumption
formula.)
The adjunction of the respective assumption formulae to a D-inference
figure in a derivation must in some way be made explicit such as by appro-
priately numbering these assumption formulae (cf. the examples in $4).
The designations of the various inference figure schemata: &-I, &-E, etc.,
stand for the following: An inference figure formed according to a particular
schema is an 'introduction' ( I )  or an 'elimination' ( E )  of the conjunction
(&), the disjunction (v), the universal quantifier (V), the existential quanti-
fier (3), the implication (x), or of the negation ( l). More about this in Q 5.
The inference figure schemata:
&-I
&-E
v-I
V-E
CKI [%I
!a
%
!av% c$
Q
_ _ _ -
!a&% !a&%
-~
%
%

!a&%
!a
%
% v B  % v %
Q
v-I
V-E
The free object variable of a V-I or 3-E, designated by a in the respective
schema, is called the eigenvariable. (This, of course, presupposes that there
is such a variable, i.e., that the bound object variable designated by z occurs
in the formula designated by &.)
Restrictions on variables:
An NJ-derivation is subject to the following restriction (for the significance
of this restriction cf. Q 3):
The eigenvariable of an V-I must not occur in the formula designated
in the schema by Vz &; nor in any assumption formula upon which that
formula depends.

---

The eigenvariable of an 3-E must not occur in the formula designated
in the schema by 3 x  &; nor in an upper formula designated by G; nor in
any assumption formula upon which that formula depends, with the excep-
tion of the assumption formulae designated by 3 a  in the schema of the
3-E.
This concludes the definition of the 'NJ-derivation'.
8 3. Informal sense of NJ-inference figures
We shall explain the informal sense of a number of inference figure
schemata and thus try to show how the calculus in fact reflects 'actual
reasoning'.
3-Z: Expressed in words, this schema corresponds to the following
inference: If B has been proved by means of assumption 8, we have (this
time without the assumption): from 8 follows B. (Further assumptions
may, of course, have been made and the result still continues to depend
on them.)
v-E ('Distinction of cases'): If 8 v 23 has been proved, we can distinguish
two cases: What we first assume is that 9.X holds and derive, let us say,
G from it. If it is then possible to derive 0. also by assuming that 23 holds,
then G holds generally, i.e., it is now independent of both assumptions
V-Z: If @ has been proved for an 'arbitrary
then Vx & holds. The
presupposition that a is 'completely arbitrary' can be expressed more
precisely as: Sa must not depend on any assumption in which the object
variable a occurs. And this, together with the obvious requirement that
every occurrence of a in @I
must be replaced by an x in @, constitutes
precisely that part of the 'restrictions on variables' which applies to the
schema of the V-Z.
3-E: We have 3~ 3:s.
We say: Suppose a is an object for which 8
holds,
i.e., we assume that 3 a  holds. (It is, of course, obvious that for a we must
take an object variable which does not yet occur in 3x @.) If, on this assump-
tion, we then prove a proposition 0. which no longer contains a and does not
depend on any other assumption containing a, we have proved G indepen-
dently of the assumption %a. We have here stated the part of the 'restrictions
on variables' that concerns the 3-E. (A certain analogy exists between the
3-E and the v-E since the existential quantifier is indeed the generalization
of v, and the universal quantifier the generalization of &.)
signifies a contradiction and as such cannot hold true
(cf.1.I).
1 - E  8 and 1

---

## 8 4, THE THREE EXAMPLES OF 0 1 WRITTEN AS NJ-DERIVATIONS
19
(law of contradiction). This is formally expressed by the inference figure
-vE, where A designates 'the contradiction', 'the false'.
7 - I :  (Reductio ad absurdum.) If we can derive any false proposition
( A )  on an assumption 3, then clx is not true, i.e., -1 (LT holds.
A
The schema -
expresses the fact that if a false proposition holds,
%I
any arbitrary proposition also holds.
straightforward.
The interpretation of the remaining inference figure schemata should be
5 4. The three examples of 5 1 written as NJ-derivations
First example (1.1):
1
1
v-I
X
v-I -
X
x v  Y
xv z &-I
2
xv (Y & z )  (XV Y )  & ( X V  z )
(XV Y )  & (XV Z )
(xv (Y & 2)) 1 ((1"
Y )  & (XV 2))
1
1
Y & Z
Z
-
v-I -
xv Y
x v z
y&z &-E __
Y
(XV Y )  & (XV Z )
1
-I2.
&-E
v-I
&-I
V-El
In this example the tree form must appear somewhat artificial since it
does not bring out the fact that it is after the enunciation of X v  (Y & Z )
that we distinguish the cases X, Y & 2.
Second example (1.2):
1
QyFay \J-E
Fab 3-1
2
3xFxb Q-I
3x Qy Fxy
Qy 3x Fxy
Qy 3x Fxy
(3x Qy Fxy) 3 (Qy 3x Fxy)
3-E,
3 -I2.
If we were using a linear arrangement, then the assumption of the 3-E
would here also follow naturally behind the upper formula on the left,
as was the case in our treatment of that example in 0 1.

---

## 80

Third example (1.3):
2
1
i
3~ FX
2% 3-1
3x Fx
A
1
Fa
VY 1
FY
7 - E
1-I2
v -I
3
-I,.
9 5. Some remarks concerning the calculus NJ. The calculus NK
5.1. The calculus N J  lacks a certain formal elegance. This has to be put
against the following advantages:
5.11. A close affinity to actual reasoning, which had been our fundamental
aim in setting up the calculus. The calculus lends itself in particular to the
formalization of mathematical proofs.
5.12. In most cases the derivations for true formulae are shorter in our
calculus than their counterparts in the logistic calculi. This is so primarily
because in logistic derivations one and the same formula usually occurs a
number of times (as part of other formulae), whereas this happens only very
rarely in the case of NJ-derivations.
5.13. The designations given to the various inference figures (2.21) make it
plain that our calculus is remarkably systematic. To every logical symbol
&, V ,  V, 3, 3,
l, belongs precisely one inference figure which 'introduces'
the symbol - as the terminal symbol of a formula - and one which
'eliminates' it. The fact that the inference figures &-E and v-I each have
two forms constitutes a trivial, purely external deviation and is of no
interest. The introductions represent, as it were, the 'definitions' of the
symbols concerned, and the eliminations are no more, in the final analysis,
than the consequences of these definitions. This fact may be expressed as
follows: In eliminating a symbol, we may use the formula with whose
terminal symbol we are dealing only 'in the sense afforded it by the introduc-
tion of that symbol'. An example may clarify what is meant: We were able to
introduce the formula
3 B when there existed a derivation of B from the
assumption formula 3. If we then wished to use that formula by eliminating
the =-symbol (we could, of course, also use it to form longer formulae,
e.g., (3 3 %) v 6,
v-I), we could do this precisely by inferring % directly,
once 3 has been proved, for what 2 3 23 attests is just the existence of a

---

## 8 1, THE CALCULI w
AND LK
81
derivation of B from %. Note that in saying this we need not go into the
'informal sense' of the 3-symbol.
By making these ideas more precise it should be possible to display the
E-inferences as unique functions of their corresponding I-inferences,
on the basis of certain requirements.
5.2. It is possible to eliminate the negation from our calculus by regarding
A. This is permissible, since by replacing
every
Z by % = A, and thus removing all -,-symbols from an NJ-
derivation, we obtain another NJ-derivation (the inference figures 7-I
and 7-E then become special cases of the 3-I and the 3-E) and vice versa:
If, in an NJ-derivation, we replace every occurrence of % 3 A by 1
%,
another NJ-derivation results.
rll as an abbreviation for %
A
3
The inference figure schema - occupies a special place among the
schemata: It does not belong to a logical symbol, but to the propositional
symbol A.
5.3. The 'law of the excluded middle' and the calculus NK.
From the calculus NJ we obtain a complete classical calculus NK by
including the 'law of the excluded middle' (tertium non datur), i.e.: In
addition to the assumption formulae we now also allow 'basic formulae'
of the form % v
We have thus granted to the law of the excluded middle, in a purely
external way, a special position, and we have done this because we considered
that formulation the 'most natural'. It would be perfectly feasible to
introduce a new inference figure schema, say ~
(a schema analogous
to the one formed by Hilbert and Heyting), in place of the basic formula
schema rll v
%. However, such a schema still falls outside the framework
of the NJ-inference figures, because it represents a new elimination of the
negation whose admissibility does not follow at all from our method of
introducing the l-symbol by the -,-I.
rll, where B stands for any arbitrary formula.
11%
%
SECTION 111. THE DEDUCTIVE CALCULI LJ, LK AND THE
