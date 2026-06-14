# Investigations into Logical Deduction

**Gerhard Gentzen** (1935)

From: *The Collected Papers of Gerhard Gentzen*, edited by M. E. Szabo, Sir George Williams University, Montreal. North-Holland Publishing Company, Amsterdam, 1969.

---

## SYNOPSIS
The investigations that follow concern the domain of predicate logic
(H.-A." call it the 'restricted predicate calculus'). It comprises the types of
inference that are continually used in all parts of mathematics. What
remains to be added to these are axioms and forms of inference that may be
considered as being proper to the particular branches of mathematics, e.g.,
in elementary number theory the axioms of the natural numbers, of addition,
multiplication, and exponentiation, as well as the inference of complete
induction; in geometry the geometric axioms.
In addition to classical logic I shall also deal with intuitionist logic as
formalized, for example, by Heyting".
The present investigations into classical and intuitionist predicate logic
fall essentially into two only loosely connected parts.
1. My starting point was this: The formalization of logical deduction,
especially as it has been developed by Frege, Russell, and Hilbert, is rather
far removed from the forms of deduction used in practice in mathematical
proofs. Considerable formal advantages are achieved in return.
In contrast, I intended first to set up a formal system which comes as
close as possible to actual reasoning. The result was a 'calculus of natural
deduction' ('NJ' for intuitionist, 'NK' for classical predicate logic). This
calculus then turned out to have certain special properties; in particular,
the 'law of the excluded middle', which the intuitionists reject, occupies a
special position.
I shall develop the calculus of natural deduction in section I1 of this
paper together with some remarks concerning it.
2. A closer investigation of the specific properties of the natural calculus
finally led me to a very general theorem which will be referred to below as
the ' Haup tsatz' .

---

The Hauptsatz" says that every purely logical proof can be reduced to
a definite, though not unique, normal form. Perhaps we may express the
essential properties of such a normal proof by saying: it is not roundabout.
No concepts enter into the proof other than those contained in its final
result, and their use was therefore essential to the achievement of that result.
The Hauptsatz holds both for classical and for intuitionist predicate logic.
In order to be able to enunciate and prove the Hauptsatz in a convenient
form, I had to provide a logical calculus especially suited to the purpose.
For this the natural calculus proved unsuitable. For, although it already
contains the properties essential to the validity of the Hauptsatz, it does so
only with respect to its intuitionist form, in view of the fact that the law of
excluded middle, as pointed out earlier, occupies a special position in relation
to these properties.
In section 111 of this paper, therefore, I shall develop a new calculus of
logical deduction possessing all the desired properties in both their intui-
tionist and their classical forms ('LJ' for intuitionist, 'LK' for classical
predicate logic). The Hauptsatz will then be enunciated and proved by
means of that calculus.
The Hauptsatz permits of a variety of applications. To illustrate this
I shall develop a decision procedure (IV, 0 1) for intuitionist propositional
logic in section IVY and shall in addition give a new proof of the consistency
of classical arithmetic without complete induction (IV, 9 3).
Sections 111 and IV may be read independently of section 11.
3. Section I contains the terminology and notations used in this paper.
In section V, I prove the equivalence of the logical calculi NJ, NK, and
LJ, LK, developed in this paper, by means of a calculus modelled on the
formalisms of Russell, Hilbert, and Heyting (and which may easily be
compared with them). ('LHJ' for intuitionist, 'LHK' for classical predicate
logic.)
SECTION I. TERMINOLOGY AND NOTATIONS
To the concepts 'object', 'function', 'predicate', 'proposition', 'theorem',
'axiom', 'proof', 'inference', etc., in logic and mathematics there correspond,
in the formalization of these disciplines, certain symbols or combinations
of symbols. We divide these into:
1. Symbols.

---

2. Expressions, i.e., finite sequences of symbols.
3. Figures, i.e., finite sets of symbols, with some ordering.
as special cases of figures.
following kind:
1. Symbols.
1.1. Constant symbols:
Symbols count as special cases of expressions and figures, expressions
In this paper we shall consider symbols, expressions, and figures of the
These divide into constant symbols and variables.
Symbols for dejnite objects: 1, 2, 3, . . .
Symbols for dejinite functions: + , -, *.
Symbols for definite propositions: V ('the true proposition'), A ('the false
Symbols for dejinite predicates: = , <.
Logical symbols:23 & 'and', v 'or', 3 'if. . . then', 3 t 'is equivalent to',
We shall also use the terms: conjunction symbol, disjunction symbol,
implication symbol, equivalence symbol, negation symbol, universal quanti-
fier, existential quantifier.
Auxiliary symbols: ) , ( , + .
1.2. Variables:
Object variables. These we divide into free object variables: a, b, c, . . . , m
and bound object variables: n, . . . , x, y ,  z.
Propositional variables: A, B, C, . . ..
An arbitrary number of variables will be assumed to be available; if the
alphabet is insufficient, we adjoin numerical subscripts, e.g., a,, C,.
1.3. German and Greek letters serve as 'syntactic variables', i.e., not as
symbols of the logic formalized, but as variables of our deliberations about
that logic. Their meanings are explained as they are used.
2. Expressions.
2.1. The concept of a propositional expression, called a 'formula' for short
(defined inductively):
(The concept of a formula is ordinarily used in a more general sense;
the special case defined below might thus perhaps be described as a 'purely
logical formula'.)
2.11. A symbol for a definite proposition (Le., the symbols V and A) is
a formula.
A propositional variable followed by a number (possibly zero) of free
object variables is a formula, e.g., Abab.
proposition').
'not', V 'for all', 3 'there is'.

---

The object variables are called the arguments of the propositional
Formulae of the two kinds mentioned are also called elementary formulae.
If
and @ are formulae, then % & '$3,
% v By
% 3
@ are formulae.
(We shall not introduce the symbol 3 c into our presentation; it is in
fact superfluous, since 2 3 c III may be regarded as an abbreviation for
2.13. A formula not containing the bound object variable F yields another
formula, if we prefix either VF or 3 ~ .
At the same time we may substitute F
in a number of places for a free object variable occurring in the formula.
2.14. Brackets (or parentheses) are to be used to show the structure of a
formula unambiguously. Example of a formula:
variables.
2.12. If
is a formula, then
is also a formula.
(a 2 @)& (B =i %).
3x (((7
Abxa) v Bx) 3
(VZ ( A  & B)))
By special convention the number of brackets may be reduced, but (with
one exception, vide 2.4) no use will be made of this, since we do not have
to write down many formulae.
2.2. The number of logical symbols occurring in a formula is called the
degree of the formula. (Thus an elementary formula is of degree 0.)
The logical symbol of a nonelementary formula that has been adjoined
last in the construction of the formula according to 2.12 and 2.13, is called
the terminal symbol of the formula.
Formulae that may have arisen in the course of the construction of a
formula according to 2.12 and 2.13, including the formula itself', are called
subformulae.
Example: the subformulae of A & Vx Bxa are A, Vx Bxa, A & Vx Bxa
as well as all formulae of the form Baa, where a represents any free object
variable (this variable may also be a, for example). The degree of
A & Vx Bxa is 2, the terminal symbol is &.
2.3. The concept of a sequent:
the purpose of its introduction becomes clear.)
(This concept will not be used until section 111, and it is only then that
A sequent is an expression of the form
where a1 , . . . , a,,, Bl , . . . , IIIV may represent any formula whatever.
(The -+, like commas, is an auxiliary symbol and not a logical symbol.)
. . . , %,
form the antecedent, and the formulae
The formulae

---

Bl
, . . . , Bv, the succedent of the sequent. Both expressions may be empty.
2.4. The sequent l?I1 , . . . , %I -+ Bl , . . . , Bv
has exactly the same informal
meaning as the formula
(a, &. . . & aJ D (B1 v . . . v 23,).
(By a1 & 212 & 213 we mean (al & a,) & a3, likewise for v.)
If the antecedent is empty, the sequent reduces to the formula
If the succedent is empty, the sequent means the same as the formula
1
(al & . . . & ZI)
or (al & . . . & illp) 3 A.
If both the antecedent and the succedent of the formula are empty, the
sequent means the same as A, i.e., a false proposition.
Conversely, to every formula there corresponds an equivalent sequent,
e.g., the sequent whose antecedent is empty and whose succedent consists
precisely of that formula.
The formulae making up a sequent are called S-formulae (i.e., sequent
formulae). By this we intend to indicate that we are not considering the
formula by itself, but as it appears in the sequent. Thus we say, for example:
'A formula occurs in several places in a sequent as an S-formula', which
may also be expressed as follows:
'Several distinct S-formulae (which shall simply mean: having distinct
occurrences in the sequent) are formally identical'.
3. Figures
We require inference figures and proof figures.
Such figures consist of formulae or sequents, as the case may be. In what
follows (3.1 to 3.3, 3.5) we shall be speaking only of formulae, but whatever
is said applies analogously to sequents; all we need to do is to replace the
word 'formula', wherever it occurs, by the word 'sequent'.
3.1. An inferenceJigure may be written in the following way:
Bl v . . . v 23,.
where illl , . . . , a,,, B are formulae. ill1, . . . , a, are then called the upper
formulae and B the lower formula of the inference figure. (The concepts of
the upper sequents and of the lower sequent of an inference figure consisting
of sequents are to be understood correspondingly.)
We shall have to consider only particular inference figures and they will be
stated for each calculus as they arise.
3.2. A proof Jigure, called a derivation for short, consists of a number of

---

formulae (at least one), which combine to form inference figures in the
following way: Each formula is a lower formula of at most one inference
figure; each formula (with the exception of exactly one: the endformula)
is an upper formula of at least one inference figure; and the system of
inference figures is noncircular, i.e., there is in the derivation no cycle
(no sequence whose last member is again succeeded by its first member)
of formulae such that each member is an upper formula of an inference
figure whose lower formula is the next formula in the sequence.
3.3. The formulae of a derivation that are not lower formulae of an inference
figure are called initial formulae of the derivation.
A derivation is in 'tree form' if each one of its formulae is an upper
formula of at most one inference figure.
Thus all formulae except the endformula are upper formulae of exactly
one inference figure.
We shall have to treat only of derivations in tree form.
The formulae which compose a derivation so defined are called D-
formulae (i.e., derivation formulae). By this we wish to indicate that we are
not considering merely the formula as such, but also its position in the
derivation. In this sense we shall be using, for example, expressions such as:
'A formula occurs in a derivation as a D-formula'. 'Two distinct D-
formulae (i.e., formulae occurring merely in distinct places in the derivation)
are formally identical, viz., identical to the same formula'.
and 23 are not only
formally identical, but occur also in the same place in the derivation. We
shall use the words 'formally identical' to indicate identity of form regardless
of place.
For object variables, however, we shall not introduce a special term that
would associate the variable with a specific place of occurrence in the
formula. Thus we say, e.g.: 'The same object variable occurs in two distinct
D-formulae.'
3.4. The inference figures of the derivation are called D-inference jigures
(i.e., derivation inference figures).
In a derivation consisting of sequents the S-formulae of the D-sequents
are called D-S-formulae (i.e., derivation sequent formulae).
3.5. A path in a derivation is (following Hilbert) a sequence of D-formulae
whose first formula is an initial formula and whose last formula is the
endformula, and of which each formula except the last is an upper formula
of a D-inference figure whose lower formula is the next formula in the path.
We say that 'a D-formula stands above (below) another D-formula'
Thus by 'a is the same D-formula as 123' we mean that

---

if there exists a path in which the former occurs before (after) the latter.
We are here thinking of the fact that a derivation is written in tree form
with the initial formulae above and the endformula below. (Examples may
be found in 11, 4 4.)
Furthermore, we say that 'a D-inference figure occurs above (below) a
D-formula', if all formulae of the inference figure occur above (below) that
D-formula.
A derivation with the endformula
is also called a 'derivation of
The initial formulae of a derivation may be basic formulae or assumption
formulae; more about their nature will have to be said as we reach the
different calculi.
SECTION 11. THE CALCULUS OF NATURAL DEDUCTION
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
HAUPTSATZ
0 1. The calculi LJ and LK (logistic intuitionist and classical calculi)
1.1. Preliminary remarks concerning the construction of the calculi U
and LK.

---

## 82

What we want to do is to formulate a deductive calculus (for predicate
logic) which is 'logistic' on the one hand, i.e., in which the derivations do not,
as in the calculus NJ, contain assumption formulae, but which, on the other
hand, takes over from the calculus NJ the division of the forms of inference
into introductions and eliminations of the various logical symbols.
The most obvious method of converting an NJ-derivation into a logistic
one is this: We replace a D-formula 23, which depends on the assumption
formulae !211 , . . . , !21p, by the new formula (al & . . . & 'illp) 3 23. This
we do with all D-formulae.
We thus obtain formulae which are already true in themselves, i.e., whose
truth is no longer conditional on the truth of certain assumption formulae.
This procedure, however, introduces new logical symbols & and 3,
neces-
sitating additional inference figures for & and 3,
and thus upsets the
systematic character of our method of introducing and eliminating symbols.
For this reason we have introduced the concept of a sequent (1.2.3). Instead
of a formula (a, & . . . & 'illp) 3
23, e.g., we therefore write the sequent
The informal meaning of this sequent is no different from that of the
above formula; the expressions differ merely in their formal structure
(cf. I. 2.4).
Even now new inference figures are required that cannot be integrated
into our system of introductions and eliminations; but we have the advantage
of being able to reserve them special places within our system, since they
no longer refer to logical symbols, but merely to the structure of the sequents.
We therefore call these 'structural inference figures', and the others 'opera-
tional inference figures'.
In the classical calculus NK the law of the excluded middle occupied a
special place among the forms of inference (11.5.3), because it could not be
integrated into our system of introductions and eliminations. In the classical
logistic calculus LK about to be presented, this characteristic is removed.
This is made possible by the admission of sequents with several formulae
in the succedent, whereas the transition from the calculus NJ just described
led only to sequents with one formula in the succedent. (For the informal
meaning of sequents in general cf. 1.2.4.) The symmetry thus obtained is
more suited to classical logic. On the other hand, the restriction to at most
one formula in the succedent will be retained for the intuitionist calculus
LJ. (Cf. below. - An empty succedent means the same as if A stood in the
succedent. )

---

## 8 1, THE CALCULI u
AND LK
We have thus outlined a number of points that underlie the construction
of the calculi that follow. Their form is largely determined, however, by
considerations connected with the 'Hauptsatz' (a 2) whose proof follows
later. That form cannot therefore be justified more fully at this stage.
1.2. We now define the concepts of an 'LK-derivation' and an 'LJ-derivation'
as follows:
An LJ- or LK-derivation consists of sequents arranged in tree form
(1.3.3).
The initial sequents of the derivation are basic sequents of the form
5D + 3,
where 5D may be an arbitrary formula.
Each inferencefigure of the derivation results from one of the schemata
below by a substitution of the following kind (cf. 11.2.21):
Replace a, 23, B, Q by an arbitrary formula; for Vx 3~
( 3 ~
3~)
put an
arbitrary formula having V(3) for its terminal symbol, where
designates
the associated bound object variable; for 3a put that formula which is
obtained from Sx by replacing every occurrence of the bound object
variable g by the free object variable a.
For r, A ,  0, A put arbitrary (possibly empty) sequences of formulae
separated by commas.
The following restriction is furthermore placed on LJ-inference figures
(this is the only respect in which the concepts of an LJ- and an LK-derivation
differ):
'In the succedent of each D-sequent no more than one S-formula may
occur'.
The designations of the various schemata for operational inference figures
&-IS, &-IA, etc., are intended to mean: An inference figure formed
according to the schema is an introduction ( I )  in the succedent (S) or
antecedent ( A )  of the conjunction (&), the disjunction (v), the universal
quantifier (V), the existential quantifier (3), the negation (-I), or the
implication (3).
The inference jgure schemata
1.21. Schemata for structural inference figures:
Thinning:
in the antecedent
in the succedent
r-+@
r-+o .
%,r+o'
r - + 0 , B 7

---

## 84

Contraction:
in the antecedent
in the succedent
sb, sb, r -+ o
r -+ o,~,sb.
%,r-+d r-+o,%
Interchange:
in the antecedent
in the succedent
A ,  9, e, r -+ o
A ,  e, B, r -+ o
r -+ o, e, 9, A .
r -+ o, %,&, A
cut:
r-+o,s B , A - + A
r, 4 -+ o, A
1.22. Schemata for operational inference figures:
@,r-+o
3Zi!iO, r -+ 0
3-IA :
Restrictions on variables: The object variable in the last two schemata,
which is designated by a and is called the eigenvariable of the V-IS (S-IA),
must not occur in the lower sequent of the inference figure (i.e., not in
r, 0, and 3 ~ ) .

---

## 8 2, SOME REMARKS CONCERNING THE CALCULI LJ AND LK
85
r40,9i
l u , r + o
u, r -+ o, B
r + o, u 3 B '
r + o , u
B , A + A
u = , ~ , r , ~ + o , n
1 - I A  :
34s :
3-IA:
1.3. Example of an LJ-derivation (using 11.1.3):
1 - f  A
1
3~ Fx, 3~ FX +
3~ Fx, i
3~ FX +
Fa + Fa
3-1s
Interchange
Fa + 3x Fx
-
Cut
Fa,
3x Fx +
1-IS
3x Fx +
Fa
v-IS
i 3 x  FX + Vy i
F y
=-IS.
+ (7
3x Fx) 3
( V p  Fy)
1.4. Example of an LK-derivation (derivation of the 'law of the excluded
middle'):
A + A
1-1s
A
v-IS
+ A, i
+ A , A v T A
+ A v - - I A , A
+ A V  7
A , A v  --I A
- t A v i A
Interchange
v-I s
Contraction.
0 2. Some remarks concerning the calculi LJ and LK. The Hauptsatz
(We shall make no further use, in this paper, of remarks 2.1 to 2.3.)
2.1. The schemata are not all mutually independent, i.e., certain schemata
could be eliminated with the help of the remaining ones. Yet if they were
left out, the 'Hauptsatz' would no longer be valid.
2.2. In general, we could simplifv the calculi in various respects if we
attached no importance to the Hauptsatz. To indicate this briefly: the

---

## 86

inference figures &-IS, v-ZA, &-ZA, v-IS, V-IA, 3-ZSY 1-ZS, 1-ZA, and
=-ZA
in the calculus LK could be replaced by basic sequents according to
the following schemata:
8,B+8&%
8VB-+8,B 8 & B + 8
% & B + B
8 + % V %
% + 8 V B
Vs8:F + 8 a
8 a  + %8:F
+ 8,
7
8 (law of the excluded middle)
1
8,8
+ (law of contradiction)
%=%,8+B.
These basic sequents and our inference figures may easily be shown
to be equivalent.
The same possibility exists for the calculus LJ, with the exception of the
inference figures v-ZA and l-ZS,
since LJ-D-sequents may not in fact
contain two S-formulae in the succedent (cf. V. 9 5).
2.3. The distinction between intuitionist and classical logic is, externally,
of a quite different type in the calculi L J  and LK from that in the calculi
NJ and NK. In the case of the latter, the distinction is based on the inclusion
or exclusion of the law of the excluded middle, whereas for the calculi L J
and LK the difference is characterized by the restriction on the succedent.
(The fact that both distinctions are equivalent will become evident as a
result of the equivalence proofs in section V for all calculi discussed in this
2.4. If 1-ZS and the 1-ZA are excluded, the calculus LK is dual in the
following sense: If we reverse all sequents of an LK-derivation (in which the
=-symbol
does not occur), i.e., if for
, . . . , 8,,
+ Bl , . . . , Bv
we put
By,.
. . , B1 + a,,,.
. . , g1,
and if we exchange, in inference figures with
two upper sequents, the right- and left-hand upper sequents, including their
derivations, and also replace every occurrence of & by v, V by 3, v by &,
and 3 by V (in the case of & and v we also have to interchange the respective
scopes of the symbols, e.g., for B v 8
we have to put 8
& B), then another
LK-derivation results.
This can be seen at once from the schemata. (Special care was taken to
arrange them in such a way as to bring out their symmetry.) (Cf. H.-A.'s
duality principle, p. 62.)
2.41. In any case, the =-symbol may, in a well-known manner, be eliminated
from the calculus NK, by regarding 8
3 B as an abbreviation for (1
8)
v B.
It may easily be shown that the schemata for the 3-ZS and the Z-ZA
may then be replaced by the schemata for v and l.
paper. 1

---

## 8 2, SOME REMARKS CONCERNING THE CALCULI u
AND LK
The calculus NJ has no corresponding property.
2.5. The most important fact for us with regard to the calculi L J  and LK
is the following:
HAUPTSATZ:
Every LJ- or LK-derivation can be transformed into an LJ-
or LK-derivation with the same endsequent and in which the inference
figure called a 'cut' does not occur.
The proof follows in 0 3.
2.51. In order to give greater clarity to the meaning of the Hauptsatz,
we shall prove a simple corollary (2.513).
For this purpose we introduce a number of expressions (which will be
needed frequently later on) relating to the operational inference figures:
2.511. That S-formula which contains the logical symbol in its schema will
be called the principal formula of an inference figure.
For the &-IS and the &-IA this is simply the S-formula of the form
2l & 23; for the v-IS and the v-IA it is 2l v 23; for the V-IS and the V-IA
it is VF 8s; for the 3-IS and the 3-IA it is 3s 8s; for the ?-IS and the
7 - I A  it is
8;
and for the =-IS and the 3 - I A  it is 2l 1
23.
The S-formulae designated by a, 23, Sa in the schemata will be called
the side formulae of the respective inference figures.
They are always subformulae of the principal formula (according to the
definition of a subformula in 1.2.2).
2.512. We can now easily read off the following facts from the inference
figure schemata:
The principal formula occurs always in the lower sequent and the side
formulae always in the upper sequents of an operational inference figure.
If a formula occurs as an S-formula in an upper sequent of a given
inference figure, and if it is here neither a side formula nor the % of a cut,
then it occurs also as an S-formula in the lower sequent.
These two facts entail the following:
If anywhere in an LJ- or LK-derivation a formula occurs as an S-formula,
and if we trace the path of the derivation from the formula concerned up
to the endsequent, the formula can only vanish from that path if it is the
% of a cut or the side formula of an operational inference figure. In the
latter case, however, there appears, in the next sequent, the principal formula
of the inference figure of which our side formula is a subformula. To that
principal formula we can then, continuing downwards, apply the same
consideration, and so on. Thus we obtain the following corollary:
2.513. COROLLARY
OF THE HAUPTSATZ
(SUBFORMULA PROPERTY): In an LJ- or

---

## 88

LK-derivation without cuts, all occurring D-S-formulae are subformulae of
the S-formulae that occur in the endsequent.
2.514. Intuitively speaking, these properties of derivations without cuts
may be expressed as follows: The S-formulae become longer as we descend
lower down in the derivation, never shorter. The final result is, as it were,
gradually built up from its constituent elements. The proof represented by
the derivation is not roundabout in that it contains only concepts which
recur in the final result (cf. the synopsis at the beginning of this paper).
3 F 3g) 3
(Vg 7
39)
msy be written without a cut as follows:
Example: The derivation given above (1.3) for + (
Fa -+ Fa
Fa -+ 3x Fx 34s
1 - I A
3x Fx, Fa +
Fa,
3x Fx -+
Interchange,
etc., as above.
$3. Proof of the Hauptsatz
The Hauptsatz runs as follows:
Every LJ- or LK-derivation can be transformed into another LJ- or
LK-derivation with the same endsequent, in which no cuts occur.
3.1. Proof of the Hauptsatz for LK-derivations.
We introduce a new inference figure (in order to facilitate the proof)
which constitutes a modified form of the cut, and which we call a mix.
The schema of that figure runs as follows:
In order to obtain an inference figure from this schema, 0 and A must be
replaced by sequences of formulae, separated by commas, in each of which
occurs at least once (as a member of the sequence) a formula of the form D,
called the 'mix formula'; and @* and A* must be replaced by the same
sequences of formulae, save that all formulae of the form '93 occurring as
members of the sequence are omitted. ('93 may be any arbitrary formula.)
r and A must be replaced, as in the other schemata, by arbitrary (possibly
empty) sequences of formulae, separated by commas.

---

## § 3, PROOF OF THE Hauptsatz
Example of a mix:
## 89
A + B y  1 A
B V  C, B, By D, B 4
A , B v C , D + i A
B is the mix formula.
We notice at once that every cut may be transformed into a mix by means
of a number of thinnings and interchanges. (Conversely, every mix may be
transformed into a cut by means of a certain number of preceding inter-
changes and contractions, though we do not use this fact.)
In the following we shall consider only derivations in which no cufs occur,
but which may contain mixes instead.
Since derivations in the old sense may be transformed into derivations
of the new kind, it suffices, for the proof of the Hauptsatz, to show that a
derivation of the new type may be transformed into a derivation with
no mix.
Furthermore, the following lemma is already sufficient:
LEMMA:
A derivation with a mix for its lowest inference figure, and not
containing any other mix, may be transformed into a derivation (with the
same endsequent) in which no mix occurs.
From this the theorem as a whole easily follows:
In an arbitrary derivation consider a mix above whose lower sequent
no further mix occurs. The derivation for this lower sequent is then of the
kind mentioned in the lemma, i.e., it may be transformed in such a way
that it no longer contains a mix. In doing so, the rest of the derivation
remains unchanged. This operation is then repeated until every mix has
systematically been eliminated.
It now remains for us to establish the proof of the lemma. (This proof
extends into 3.2 incl.)
We have to consider a derivation whose lowest inference figure is a mix
and which contains no other mix.
The degree of the mix formula will be called the 'degree of the derivation'
(defined in 1.2.2).
We shall call the rank of the derivation the sum of its rank on the left
and its rank on the right. These two terms are defined as follows:
The left rank is the largest number of consecutive sequents in a path so
that the lowest of these sequents is the left-hand upper sequent of the mix
and each of the sequents contains the mix formula in the succedent.

---

The right rank is (correspondingly) the largest number of consecutive
sequents in a path so that the lowest of these sequents is the right-hand
upper sequent of the mix and each of the sequents contains the mix formala
in the antecedent.
The lowest possible rank is evidently 2.
To prove the lemma we carry out two complete inductions, one on the
degree y, the other on the rank p ,  of the derivation, i.e., we prove the
theorem for a derivation of degree y, assuming it to hold for derivations
of a lower degree (in so far as there are such derivations, i.e., as long as
y is not equal to zero), supposing, therefore, that derivations of lower
degree can already be transformed into derivations with no mix. Further-
more, we shall begin by considering the case where the rank p of the deriva-
tion equals 2 (3.11), and after that the case of p > 2 (3.12), where we
assume that the theorem already holds for derivations of the same degree,
but of a lower rank.
In the following German capital letters will generally serve as syntactic
variables for formulae, and Greek capital letters as syntactic variables for
(possibly empty) sequences of formulae.
In transforming derivations, we shall occasionally meet 'identical inference
figures', i.e., inference figures with identical upper and lower sequents.
Since we have not admitted such figures in our calculus, they must be
eliminated as soon as they occur; we can do this trivially by omitting one of
the two sequents.
The mix formula of the mix that occurs at the end of the derivation is
designated by !JJ?. It is of degree y.
3.10. Redesignating of free object variables in preparation for the trans-
formation of derivations.
3.101. For every V-IS (3-IA) it holds that: Its eigenvariable occurs in the
derivation only in sequents above the lower sequent of the V-IS ( 3 4 4 )
and does not occur as an eigenvariable in any other V-IS (344).
3.102. This is achieved by redesignating free object variables in the follow-
ing way:
We take a V-IS (3-IA) above whose lower sequent either no further
inference figures of this kind occur, or if they do, they have already been
dealt with in a way still to be described.
In all sequents above the lower sequent of this inference figure we replace
the eigenvariable by one and the same free object variable which, so far,
has not yet occurred in the derivation. This obviously leaves the V-IS
We wish to obtain a derivation that has the following properties:

---

5 3, PROOF OF THE Hauptsatr
91
(344) itself correct, as is easily seen. (The eigenvariable did not in fact
occur in its lower sequent.) Furthermore, rest of the derivation remains
correct, as is shown by the lemma to follow shortly.
A systematic application of this method to every single V-IS and 3-IA,
thus leaves the derivation correct throughout and the conclusion ob-
viously has the desired property (3.101). Furthermore, as was essential,
the degree and rank of the derivation, as well as its endsequent, have
remained unaltered.
3.103. Now we give the still outstanding proof of the following lemma.
(It is enunciated in a somewhat more general form than is immediately
necessary, since we shall have to apply it again later on (3.1 13.33))
An LK-basic sequent or inference figure becomes a basic sequent or
inference figure of the same kind, if we replace a free object variable which
is not the eigenvariable of the inference figure in all its occurrences in the
basic sequent or inference figure, by one and the same free object variable,
provided again that this is not the eigenvariable of the inference figure.
This holds trivially except for the V-IS, V-IA, 3-1s and 3 4 4 .  Even here,
however, there is no cause for concern: the restrictions on variables are not
violated, since we may neither substitute nor replace the eigenvariable.
(This is the reason why both restrictions on variables are necessary.)
Furthermore, the formula resulting from %a is again obtained by substituting
a for F in the formula resulting from 3:s.
Having prepared the way (3.10), we now proceed to the actual transforma-
tion of the derivation which serves to eliminate the mix occurring in it.
As already mentioned, we distinguish the two cases: p = 2 (3.11) and
p > 2 (3.12).
3.11. Suppose p = 2.
We distinguish between several individual cases, of which the cases
3.111, 3.112, 3.113.1, 3.113.2 are especially simple in that they allow the
mix to be immediately eliminated. The other cases (3.113.3) are the most
important since their consideration brings out the basic idea behind the
whole transformation. Here we use the induction hypothesis with respect
to y, i.e., we reduce each one of the cases to transformed derivations of a
lower degree.
3.111. Suppose the left-hand upper sequent of the mix at the end of the
derivation is a basic sequent. The mix then reads:
%R+%R
A + A
%R,A*-+A
7

---

which is transformed into:
A - + A
!JX,A*-+A possibly several interchanges and contractions.
That part of the derivation which is above A -+ A remains the same, and
we thus have a derivation without a mix.
3.112. Suppose the right-hand upper sequent of the mix is a basic sequent.
The treatment of this case is symmetric to that of the previous one. We have
only to regard the two schemata as 'duals' (cf. 2.4).
3.113. Suppose that neither the left- nor the right-hand upper sequent of
the mix is a basic sequent. Then both are lower sequents of inferenceJigures
since p = 2, and the right and left rank both equal 1, i.e.: In the sequents
directly above the lef-hand upper sequent of the mix, the mix formula !JX
does not occur in the succedent; in the sequents directly above the right-hand
upper sequent '3n does not occur in the antecedent.
Now the following holds generally: If a formula occurs in the antecedent
(succedent) of the lower sequent of an inference figure, it is either a principal
formula or the 9 of a thinning, or else it also occurs in the antecedent
(succedent) in at least one upper sequent of the inference figure.
This can be seen immediately by looking at the inference figure schemata
If we now consider the hypotheses in the following three cases, we see
at once that they exhaust all the possibilities that exist within case 3.113.
3.113.1. Suppose the left-hand upper sequent of the mix is the lower sequent
of a thinning. Then the conclusion of the derivation runs:
(1.21, 1.22).
r-+o
r + o , n
A + A
r, A* --* 0,
A
This is transformed into:
r + o
possibly several thinnings and interchanges.
r, A* --f 0,
A
That part of the derivation which occurs above A --f A disappears.
3.113.2. Suppose the right-hand upper sequent of the mix is the lower
sequent of a thinning. This case is dealt with symmetrically to the
previous one.
3.113.3. The mix formula % occurs both in the succedent of the left-hand

---

0 3, PROOF OF THE Hauptsatz
93
upper sequent and in the antecedent of the right-hand upper sequent solely
as the principal formula of one of the operational inference figures.
is &, v, V, 3, 1,
1,
we distinguish the cases 3.113.31 to 3.113.36 (a formula without logical
symbols cannot be a principal formula).
3.113.31. Suppose the terminal symbol of YI'l is &. In that case the end of
the derivation runs:
Depending on whether the terminal symbol of
'5
r2 * '2
&-IA
&-IS
rl -+ @,,a rl -+ q , ~
rl,r2
-+
mix
rl -+ @ , , a & ~
a&23,r2-+02
(the other form of the &-IA is treated analogously).
We transform it into:
rl -+ 0, , a
a, r2
-+ o2 mix
rl , r; -+ o;, o2
rl,r2
-+ ol,
o2
possibly several thinnings and interchanges.
We can now apply the induction hypothesis with respect to y to that part
of the derivation whose lowest sequent is rl , rz + O:, 0, , because it has
a lower degree than y. (a obviously contains fewer logical symbols than
8 & 23.) This means that the whole derivation may be transformed into
one with no mix.
3.113.32. Suppose the terminal symbol of )rJt is v. This case is dealt with
symmetrically to the previous one.
3.113.33. Suppose the terminal symbol of )rJt is V. Then the end of the
derivation runs:
This is transformed into:
rl -+ o1 , 8b
?ih rz -, o2 mix
rl,r; -+ o;, o2
rl,r2
-+ 01,02
possibly several thinnings and interchanges.
Above the left-hand upper sequent of the mix, rl 3 0, , %by we write
the same part of the derivation which previously occurred above
rl -+ 0, , %a, yet having replaced every occurrence of the free object
variable a by b. It now follows from lemma 3.103, together with 3.101,

---

that in performing this operation the part of the derivation aboue
rl -+ 0, , Sb has again become a correct part of the derivation. (By virtue
of 3.101 neither a nor b can be the eigenvariable of an inference figure
occurring in that part of the derivation.) The same consideration may be
applied to that part of the derivation which includes the sequent
rl -+ 0, , ?jb, since it too results from rl -+ a,, %a by the substitution
of b for a. It is now in fact clear that by virtue of the restriction on variables
for V-IS, a could have occurred neither in rl and 0, , nor in 8 ~ .
Further-
more, %a results from '& by the substitution a for x, and sb from Sx by the
substitution b for x. This is why sb results from Sa by the substitution b
for a.
The mix formula 86 in the new derivation has a lower degree than y.
Therefore, according to the induction hypothesis, the mix may be eliminated.
3.113.34. Suppose the terminal symbol of Zm is 3. This case is dealt with
symmetrically to the previous one.
3.113.35. Suppose the terminal symbol of Zm is l. Then the end of the
derivation runs:
a,rl
-+ o1
r2 -+ 02, a
7 4 s
7 - I A
rl -+ ol, la
1
a, r2 + 0 2
mix.
rl, r2
-+ o,, o2
This is transformed into:
r2
-+ 02,a %,r1
-+ o, mix
r2,r:
-+ or, o,
rl,r2
-+ ol,
o2
possibly several interchanges and thinnings.
The new mix may be eliminated by virtue of the induction hypothesis.
3.113.36. Suppose the terminal symbol of Zm is 2.
Then the end of the
derivation runs:
r-+o,a B , A - + A
a = BJ, A -+ o, A
=-IS
3-IA
a, rl -+ o,, B
mix.
rl -+ @,,a 3 B
r, , r, A -+ o, , o, A
a , r , - + o l , ~
B , A - + A
This is transformed into:
mix
mix
r+o,a
% J , ,  A* -+ O:, A
r, r:, A** -+ 0*, O:, A
possibly several interchanges and thinnings.
rl , r, A -+ o1 , o, A

---

$ 3 ,  PROOF OF THE Hauptsatz
95
(The asterisks are, of course, intended as follows: A* and @* result from
A and 0,
by the omission of all S-formulae of the form %; r* , A** and @*
result fromr, , A* and 0 by the omission of all S-formulae of the form 8.)
Now we have two mixes, but both mix formulae are of a lower degree than
y. We first apply the induction hypothesis to the upper mix (i.e., to that
part of the derivation whose lowest figure it is). Thus the upper mix may be
eliminated. We can then also eliminate the lower mix.
3.12. Suppose p > 2.
To begin with, we distinguish two main cases: First case: The right rank
is greater than 1 (3.121). Second case: The right rank is equal to 1 and the
left rank is therefore greater than 1 (3.122).
The second case may essentially be dealt with symmetrically to the first.
3.121. Suppose the right rank is greater than 1.
1.e.: The right-hand upper sequent of the mix is the lower sequent of an
inference figure, let us call it Sf, and
occurs in the antecedent of at least
one upper sequent of Sf.
The basic idea behind the transformation procedure is the following:
In the case of p = 2, we generally reduced the derivation to one of a
lower degree. NOW, however, we shall proceed to reduce the derivation to
one of the same degree, but of a lower rank, in order to be able to use the
induction hypothesis with respect to p.
The only exception is the first case, 3.121.1, where the mix may be
eliminated immediately.
In the remaihing cases the reduction to derivations of a lower rank is
achieved in the following way: The mix is, as it were, moved up one level
within the derivation, beyond the inference figure Sf. (Case 3.121.231,
for example, illustrates this point particularly well.) To speak more precisely,
the left-hand upper sequent of the mix (which from now on will be de-
signated by I7 + Z), at present occurring beside the lower sequent of Sf,
is instead written next to the upper sequents of Sf. These now become upper
sequents of new mixes. The lower sequents of these mixes are now used as
upper sequents of a new inference figure that takes the place of Sf. This
new inference figure takes us back either directly, or after having added
further inference figures, to the original endsequent. Each new mix obviously
has a rank smaller than p, since the left rank remains unchanged and the
right rank is diminished by at least 1.
In the strict application of this basic idea special circumstances still arise
which make it necessary to distinguish the corresponding cases and to deal
with them separately.

---

INVESTIoATIONS INTO LOGICAL DEDUCTION
3.121.1. Suppose 9Jl occurs in the antecedent of the left-hand upper sequent
of the mix. The end of the derivation runs:
This is transformed into:
A - t A
possibly several thinnings, contractions and interchanges.
n, A* + z*, A
3.121.2. Suppose
does not occur in the antecedent of the left-hand upper
sequent of the mix.(This hypothesis will be used for the first time in 3.121.222.)
3.121.21. Suppose 8f is a thinning, contraction, or interchange in the
antecedent. Then the end of the derivation runs:
Qf
ly-0
n + z
3 - 0  mix.
n, 8* + z*, 0
This is transformed into:
possibly several interchanges
Y*. n + x*. 0 -
F,
n -+ x*, 0 "
n,5* 4 z*, 0
possibly several interchanges.
The inference figure marked $ is of the same kind as 3f, in so far as the
S-formulae designated in the schema of 8f (in 1.21) by 5D and Q, were not
equal to D. If 5D or Q is equal to B, we have an identical inference figure
(Y* equals S*).
The derivation for the lower sequent of the new mix has the same left
rank as the old derivation, whereas its right rank is lower by 1. Thus the mix
may be completely eliminated by virtue of the induction hypothesis.
3.121.22. Suppose af is an inference figure with one upper sequent, but not
containing a thinning, contraction, or interchange in the antecedent. Then
the end of the derivation runs:
n+x
z,r+tz,
n, %*, r* + z*, n,
mix.

---

## 8 5. PROOF OF THE Hauptsatz
Here we have collected in 1" the same S-formulae that are designated by
r in the schema of the inference figure (1.21, 1.22). Hence Y may be empty
or consist of a side formula of the inference figure, and E may be empty or
consist of the principal formula of the inference figure.
First of all, the end of the derivation is transformed into:
n-+z ~ , r - + a ~
n, Y*, r* -+. c*, 52,
Y ,  r*, n -+ z*, al
8, r*, n -+ c*, 52,
mix
possibly several interchanges and thinnings.
The lowest inference is obviously an inference figure of the same kind as
Sf (taking r*, n as the r of the inference figure and including Z* in the 0
of the inference figure).
We must only be careful not to violate the restrictions on variables
(if 8f is a V-IS or 3 - h ) :  Any such violation is precluded by 3.101, which
entails that an eigenvariable that may have occurred in Sf cannot have
occurred in 17 and Z.
The mix may be eliminated from the new derivation by virtue of the
induction hypothesis.
We therefore obtain a derivation with no mix and which is terminated
by the following inference figure:
Y ,  r*, n -+ z*, 52,
E, r*, n -+ z*, a2 '
In general, the endsequent is not yet of the form aimed at. Hence we
proceed as follows:
3.121.221. Suppose E does not contain '9X.
In that case we perform a number of interchanges, if necessary, and
obtain the endsequent of the original derivation.
3.121.222. Suppose B contains '9X. Then E is the principal formula of sf
and is identical with %. We then adjoin:
n -+ L;
%, r*, n -+ z*, 52,
n, r*, n* .+ z*, c*, sz,
n, r* -+ z*, a,
possibly several contractions and interchanges.
Once again, this is the endsequent of the original derivation. (Above
l7 -+ Z we once more write the derivation associated with it.) Thus we have
another mix in the derivation. The left rank of our derivation is the same

---

as that of the original derivation. The right rank is now equal to 1. This
is so because directly above the right-hand upper sequent occurs the sequent
Y, r*, n -, z*, a,.
m no longer occurs in its antecedent, for r* does not contain 'D, nor
does n, because of 3.121.2; and Y contains at most one side formula of
3f, which cannot be equal to m, since the principal forniula of 3f is equal
to m.
Hence this mix, too, may be eliminated by virtue of the induction hypo-
thesis.
3.121.23. Suppose 3f is an inference figure with two upper sequents, i.e.,
a &-IS, v-IA, or a x-IA.
(In view of the application to intuitionist logic (3.2) we shall deal with
each possibility in greater detail than would be necessary for the classical
case.)
3.121.231. Suppose Sf is a &-IS.
Then the end of the derivation runs:
r-+o,a r-+o,%
&,Is
mix.
u - + z
r - + o , % m
n, r* -+ z*, o, 'LI & %
(m occurs in r.) This is transformed into:
n-+c
r - + o , a m i x  n + z
r-+o,%
mix
n, r* -+ z*, o, 'LI
n, r* -+ z*, 0, %
&-Is.
n, r* -+ z*, o, % & 8
Both mixes may be eliminated by virtue of the induction hypothesis.
Then the end of the derivation runs:
3.121.232. Suppose Sf is a d-IA.
V-IA
%,r-+o %,r-,o
n + c
ixv%,r-+o
mix.
n, (a v %)*, r* -+ c*, o
((a v %)* stands either for
unequal or equal to !lX.)
and the right rank would be equal to 1 contrary to 3.121.)
v % or for nothing according as 'LI v % is
'D certainly occurs in r. (For otherwise !lX would be equal to 'LI v 8,
To begin with, we transform the end of the derivation into:

---

0 3, PROOF OF THE Hauptsatz
99
n 4 z  %,r-+omix
II -+ I: %, r' -+ o mix
a, n, r* -+ z*, 0
r* * '*,
possibly several inter-
changes and thinnings n,
B*9 r*
--f Z*7
@ possibly several inter-
changes and thinnings
8,
n, r* -+ z*, o v-IA.
8 v B, n, r'* -+ z*, o
Both mixes may be eliminated by virtue of the induction hypothesis.
From here on the procedure is the same as that in 3.121.221 and 3.121.222,
i.e., we distinguish two cases according as % v B is unequal or equal to YJl.
In the first case we may have to add several interchanges to obtain the
endsequent of the original derivation; in the second case we add a mix with
Il -+ I: for its left-hand upper sequent, and thus once again obtain the
endsequent of the original derivation by going on to perform a number of
contractions and interchanges, if necessary. The mix concerned may be
eliminated, since the associated right rank equals 1. (All this as in 3.121.222.)
3.121.233. Suppose 3f is a I-IA.
Then the end of the derivation runs:
3.121.233.1. Suppose 2Jl occurs in r and A .
In that case we begin by transforming the derivation into:
I I + Z
B , A - + A m i x
n + ~
r-+0,%
%*, '*
-+ '*,
possibly several inter-
mix
changes and thinnings
I - I A .
n, r* 4 z*, o, %
%, II, A* -+ Z*, A
8 3 8, n, r*, 17, A* + Z*, 0, Z*, A
Both mixes may be eliminated by virtue of the induction hypothesis.
'Then we proceed as in 3.121.221 and 3.121.222. (All that may happen in
the first case is that beside interchanges a number of contractions become
necessary.)
3.121.233.2. Suppose 2Jl does not occur in both r and A simultaneously.
%R must occur in either r or A because of 3.121. Consider the case of YIl
occurring in A but not in r. The second case is treated analogously.
The end of the derivation is transformed into:

---

IZ-+Z
B , A - t A m i x
possibly several interchanges and thinnings
n, B*, A* -, Z*, A
8, n, A* -+ c*, A 3-IA.
r-+B,a
8 3 8, r, n, A* -+ O,,Z*, A
The mix may be eliminated by virtue of the induction hypothesis. We
then proceed as in 3.121.221 and 3.121.222. (In the second case, where
% 3 B is equal to %!, the right rank belonging to the new mix equals 1 as
always, since %! does not occur in By n, A* for the usual reasons, nor does
it occur in r according to the assumption in the case under consideration.)
3.122. Suppose the right rank is equal to 1. In that case the left rank is
greater than 1.
This case is, in essence, treated dually to 3.121. Special attention is required
only for those inference figures with no symmetric counterpart, viz., the
3-ZS and the 3-ZA.
The inference figures 3f with one upper sequent were incorporated, in
3.121.22, in the general schema:
The dual schema runs:
Q, -+ r, Y
n, -+ r,
which also covers the 3-1s without any further change. (r here represents
the formulae designated by 0 in the schemata 1.21, 1.22.)
3.122.1. On the other hand, the case where the inference figure %f is a
I-IA, must be treated separately. Although this treatment will seem very
similar to that in 3.121.233, it is not entirely dual.
Thus the end of the derivation runs:
3.122.11. Suppose
the end of the derivation into:
occurs both in 0 and A. In that case we transform

---

## 8 3, PROOF OF THE Hauptsatz
Both mixes may be eliminated by virtue of the induction hypothesis.
3.122.12. Suppose 93 does not occur in both 0 and A simultaneously.
It must occur in one of them. We consider the case of 93 occurring in A, but
not in 0; the alternative case is completely analogous.
We transform the end of the derivation into:
B , A - + A
Z - I l  mix
r-+@,a B, A, C* + A*, fl
3-IA.
3 B, r, A, Z* --+ 0, A*, Il
The mix may be eliminated by virtue of the induction hypothesis.
3.2. Proof of the Hauptsatz for LJ-derivations.
In order to transform an LJ-derivation into an LJ-derivation without cuts,
we apply exactly the same procedure as for LK-derivations.
Since an LJ-derivation is a special case of an LK-derivation, it is clear
that the transformation can be carried out. We have only to convince
ourselves that with every transformation step an LJ-derivation becomes
another LJ-derivation, i.e., that the D-sequents of the transformed deriva-
tion do not contain more than one S-formula in the succedent, given that
this was the case before.
We therefore examine each step of the transformation from that point
of view.
3.21. Replacement of cuts by mixes. An LJ-cut runs:
r-+b D , A - + A
Y
r , A - + A
where A contains at most one S-formula. We transform this cut into:
r-+b b , d - , n m i x
r, A* -+ A
r , A - + A
This replacement gives us a new LJ-derivation.
possibly several interchanges and thinnings in the antecedent.

---

3.22. By relabelling free object variables (3.10) we trivially get another
LJ-derivation from a previous one.
3.23. The transformation proper (3.1 1 and 3.12).
We have to show for each of the cases 3.11 1 to 3.122.12 that the specified
transformations do not introduce any sequents with more than one S-
formula in the succedent.
3.231. Let us begin with the cases 3.11:
In the cases 3.111, 3.113.1, 3.113.31, 3.113.35 and 3.113.36, only such
formulae occur in each succedent of the sequent of a new derivation as had
already occurred in the succedent of the sequent of the original derivation.
Essentially the same applies in 3.113.33. The only difference is an addi-
tional replacement of free object variables, which does not, of course,
alter the number of succedent formulae of a sequent.
Cases 3.112, 3.113.2,3.113.32, and 3.113.34 were dealt with symmetrically
tocases3.111,3.113.1,3.113.31,and3.113.33,i.e.,inordertogetonecase
from another, we read the schemata from right to left instead of from left
to right (as well as changing logical symbols, a process which is here of no
consequence). Hence in the antecedent of one case we get precisely the
same as in the succedent of another. For the antecedents of cases 3.111,
3.113.1, 3.113.31 and 3.113.33, the same applies as for the succedents, viz.,
in every antecedent of a sequent of the new derivation only such formulae
occur as had already occurred in an antecedent of a sequent of the original
derivation.
This disposes of all dual cases: 3.112, 3.113.2, 3.113.32 and 3.113.34.
3.232. Now let us look at the cases, 3.12:
3.232.1. For the cases 3.121 it holds generally that Z* is empty, since in
l7 -+ Z, ,Z must contain only one formula, and that formula must be equal
to m.
It is now obvious that in every succedent of a sequent only such formulae
occur as had already occurred in the succedent of a sequent of the original
derivation.
3.232.2. In the cases 3.122 it is somewhat more difficult to see that from an
LJ-derivation we always get another LJ-derivation. We must direct our
attention, as was done in our earlier consideration of dual cases, to the
antecedents in the schemata 3.121.
3.232.21. The case which is dual to 3.121.1 is trivial, since in every antecedent
of a sequent of a new derivation (in case 3.121.1) only such formulae occur
as had already occurred in an antecedent of a sequent of the original derivation.
At this point we distinguish two further subcases:

---

0 1, APPLICATIONS OF THE Hauptsatz IN PROPOSITIONAL LOGIC
103
3.232.22. In the cases that are dual to 3.121.2, the mix in the end of the
derivation runs:
a + m
z-kn
a, z* + n
Y
where 17 contains at most one S-formula, and where D +
is the lower
sequent of an LJ-inference figure in which at least one upper sequent
contains 9Jl as a succedent formula.
If we now look at the inference figure schemata 1.21, 1.22, it becomes
easily apparent that such an inference figure can only be a thinning, con-
traction, or interchange in the antecedent, or a v-IA, a &-ZA, a +ZA,
a V-IA, and a 3-ZA. Let us disregard for the moment the v-IA and the
1-U. Then all the possibilities enumerated above fall within the case dual
to 3.121.22, where both Y and Z always remain empty. (r corresponds
to the 0 of the inference figure.) Thus we have the case which is dual to
3.121.221. Furthermore, r is equal to '%, i.e., r* is empty, and n contains
at most one formula. Hence in the new derivation there never in fact occurs
more than one formula in the succedent of a sequent.
The case of a v-IA is dual to 3.121.231. Again, r is equal to '557, I'*
is
empty, and 17 contains at most one formula; all is thus in order.
There now remains the case of a x-IA, i.e., 3.122.1. In an LJ- 3 4 4 ,
the 0 of the schema (1.22) is empty. Thus we have the case set out under
3.122.12. A* is also empty, and n contains at most one formula, which
means that here, too, we again obtain an LJ-derivation from an LJ-deriva-
tion.
SECTION IV. SOME APPLICATIONS OF THE HAUPTSATZ
9 1. Applications of the Hauptsatz in propositional logic
1.1. A trivial consequence of the Hauptsatz is the already known con-
sistency of classical (and intuitionist) predicate logic (cf., e.g., D. Hilbert
and W. Ackermann, Grundziige der theoretischen Logik (Berlin, 1928,
1st edition), p. 65): the sequent + (which is derivable from every contra-
dictory sequent + % &
'%, cf. 3.21) cannot be the lower sequent of any
inference figure other than of a cut and is therefore not derivable.
1.2. Solution of the decision problem for intuitionist propositional logic.
On the basis of the Hauptsatz we can state a simple procedure for deciding
of a formula of propositional logic - i.e., a formula without object variables -

---

whether or not it is classically or intuitionistically true. (For classical
propositional logic a simple solution has actually been known for some
time, cf., e.g., p. 11 of Hilbert-Ackermann.)
First we prove the following lemma:
A sequent in whose antecedent one and the same formula does not occur
more than three times as an S-formula, and in whose succedent, furthermore,
one and the same formula occurs no more than three times as an S-formula,
will be called a 'reduced sequent'. The following lemma now holds:
1.21. Every LJ- or LK-derivation whose endsequent is reduced, may be
transformed into an LJ- or LK-derivation with the same endsequent,
in which all sequents are reduced (and in which no cuts occur if the original
derivation did not contain any).
PROOF
OF THIS LEMMA: If we eliminate from the antecedent of a sequent,
in any places whatever (possibly none), all S-formulae occurring more
than once, and if we do the same independently in the succedent, so that
eventually these formulae occur only once, twice, or three times, we obtain
a sequent that will be called a 'reduction instance of the given sequent'.
From a reduction instance of a sequent we may obviously derive all other
reduction instances of the same sequent by means of thinnings, contractions,
and interchanges such that in the course of these operations only reduced
sequents occur.
After these preliminary remarks we now transform the LJ- or LK-
derivation at hand in the following way:
All basic sequents as well as the endsequent are left intact; they are already
reduced sequents.
The D-sequents which belong to an inference figure are transformed into
reduction instances of these sequents in a way about to be indicated. By
virtue of our preliminary remark it does not matter if a sequent belonging
to two different D-inference figures is in each case replaced by a diferent
reduction instance, since one sequent is derived very simply from the other
by thinnings, contractions, and interchanges so that eventually another
complete derivation results. (The same holds for a sequent whch, while
belonging to an inference figure, is also a basi,c sequent or an endsequent,
since it is of course a reduction instance of itself.)
The transformations of the inference figures are now carried out in the
following way:
If a formula occurs more than once within r, it is eliminated from r,
both from the upper sequents and the lower sequent, as many times (from

---

!j 1, APPLICATIONS OF THE Hauptsatz IN PROPOSITIONAL LOGIC
105
the appropriate places) as is necessary to ensure that finally it occurs in
r no more than once. The same procedure is used for A ,  0,
and A (i-e.,
those sequences of formulae that are designated by these letters in the
schema 111.1.21 and 1.22, of the inference figure concerned).
Having carried out the transformations described, we have now a deriva-
tion consisting only of reduced sequents. (An interchange where %I
is
identical with B may form an exception, yet this figure would be an identical
inference figure and could have been avoided.)
The lemma is thus proved.
Given the Hauptsatz, together with corollary 111. 2.513, and the preceding
lemma (1.21), it now holds that:
1.22. For every correctly reduced sequent, both intuitionist and classical,
there exists an LJ- or LK-derivation resp. without cuts consisting only of
reduced sequents, and whose D-S-formulae are subformulae of the S-
formula of that sequent.
1.23. Consider now a sequent not containing an object variable. We wish
to decide whether or not it is intuitionistically or classically true. We can
begin by taking in its place an equivalent reduced sequent 6q.
The number of all reduced sequents whose S-formulae are subformulae
of the S-formulae of Gq is obviously finite. The decision procedure may
therefore be carried out without further complications in the following way:
We consider the finite system of sequents in question and investigate
first of all, which of these sequents are basic sequents. Then we examine
each of the remaining sequents to determine whether there occurs an
inference figure in which the sequent in question is the lower sequent and in
which there occur as upper sequents one or two of those sequents that have
already been found to be derivable. If this is the case, the sequent is added
to the derivable sequents. (All this is obviously decidable.) We continue in
this way until either the sequent Gq itself turns out to be derivable, or until
the procedure yields no new derivable sequents. In the latter case the sequent
Gq (by virtue of 1.22) is not derivable at all in the calculus under considera-
tion (LJ or LK). We have therefore succeeded in establishing the validity of
that sequent.
1.3. A new proof of the nonderivability of the law of the excluded middle
in intuitionist logic.
Our decision procedure could have been formulated in a way better suited
to the needs of practical application; yet the above presentation (1.2) was
intended only to indicate a possibility in principle.
As an example, we shall prove the nonderivability of the law of the

---

excluded middle in intuitionist logic by a method independent of the decision
procedure described (although this procedure would have to yield the same
result). (This nonderivability has already been proved by HeytingZ4 in a
completely different way.)
A .  Suppose there exists
an LJ-derivation for it. According to the Hauptsatz there then exists sucb a
derivation without cuts. Its lowest inference figure must be a v-IS, for in
all other LJ-inference figures either the antecedent of the lower sequent is
not empty, or a formula occurs in the succedent whose terminal symbol
is not v; there might still be the case of a thinning in the succedent, but the
upper sequent would then be a +, which, by virtue of 1.1, is not derivable.
Hence either + A or + 1
A would have to be already derivable
(without cuts).
(From the same considerations, incidentally, it follows in general:
If '% v B is an intuitionistically true formula, then either % or B is an
intuitionistically true formula. In classical logic this does not hold, as the
example of A v
Now + A cannot be the lower sequent of any LJ-inference figure whatever
(if it is not a cut), unless that figure is another thinning with -+ for its
upper sequent. Furthermore, since + A is not a basic sequent, it is thus not
derivable.
A is derivable only from A +
by a T-ZS figure, and A + is in turn derivable only from A, A +, since A
contains no terminal symbol. Continuing in this way, we always reach only
sequents of the type A, A, . . . , A +, but never a basic sequent.
The sequent in question is of the form + A v
A already shows.)
The same considerations show that +
Hence A v 1
A is not derivable in intuitionist predicate logic.
0 2. A sharpened form of the Hauptsatz for classical predicate logic
2.1. w e  are here concerned with the following SHARPENING OF THE HAUPTSATZ:
Suppose that we have an LK-derivation whose endsequent is of the
following kind:
Each S-formula of this sequent contains V and hymbols at most at the
beginning, and their scope extends over the whole of the remaining formula.
In that case, the given derivation may be transformed into an LK-deriva-
tion with the same endsequent and having the following properties:
1. It contains no cuts.
2. It contains a D-sequent, let us call it the 'midsequent', which is such
that its derivation (and hence the midsequent itself) contains no V and

---

$2, A SHARPENED FORM OF THE Hauptsatz FOR CLASSICAL PREDICATE LOGIC
107
hymbols, and where the only inference figures occurring in the remaining
part of the derivation, the midsequent included, are V-IS, V-IA, 3-IS, 3-IA,
and structural inference figures.
2.11. The midsequent divides the derivation, as it were, into an upper part
beolnging to propositional logic, and a lower part containing only V and
3introductions.
Concerning the form of the transformed derivation, the following may
still be readily concluded: The lower part, from the midsequent to the
endsequent, belongs to only one path since only inference figures with one
upper sequent occur in it. The S-formulae of the midsequent are of the
following kind:
Every S-formula in the antecedent of the midsequent results from an
S-formula in the antecedent of the endsequent by the elimination of the V
and 3-symbols (together with the bound object variables beside them),
and by the replacement of the bound object variables in the rest of the
formula by certain free object variables. The same procedure is followed
in the case of succedents.
2.2. PROOF OF THE THEOREM (2.1)?
2.21. We begin by applying the Hauptsatz (111.2.5): The derivation may
accordingly be transformed into a derivation without cuts.
2.22. Transformation of basic sequents containing a V- or 3-symbol:
By virtue of the properties of subformulae 111.2.513, such sequents can
only have the form VF & --+ V z  3s or 3z 3~
+ 3g SF. They are trans-
formed into (suppose a to be a free object variable not yet occurring in the
derivation):
This follows from the same consideration as in 111.2.512.
The transformation of the derivation is carried out in several steps.
By repeating this procedure sufficiently often we can obviously eliminate
all V- and 3-symbols from every basic sequent of the derivation.
2.23. We now perform a complete induction on the 'order' of the derivation,
which is defined as follows:
Of the operational inference figures we call those belonging to the symbols
&, v, l, and 13 'propositional inference figures', and the rest, i.e., V-IS,
V-IA, ]-IS, 3-IA, 'predicate inference figures'. To each predicate inference
figure in the derivation we assign the following ordinal number:

---

We consider that path of the derivation that extends from the lower sequent
of the inference figure up to the endsequent of the derivation (including the
endsequent) and count the number of lower sequents of the propositional
inference figures occurring in it. Their number is the ordinal number.
The sum of the ordinal numbers of all predicate inference figures in the
derivation is the order of the derivation.
We intend to reduce that order step by step until it becomes zero.
Note that once this has been achieved the rest of the proof of the theorem
(2.1) is easily carried out: (The steps involved (2.232) will be such as to
preserve the properties that were established in 2.21 and 2.22.)
2.231. In order to do so we assume that the derivation has already been
reduced to order zero. From the endsequent we now proceed to the upper
sequent of the inference figure above it. We stop as soon as we encounter
the lower sequent of a propositional inference figure or a basic sequent;
that sequent we call Gq. (It will serve us as 'midsequent', once it has been
transformed in a way about to be indicated.)
The derivation of 6q is now transformed as follows:
We simply omit all D-S-formulae which still contain the symbols V and
3. The above derivation remains correct after the described operation
since, by virtue of 2.22, its basic sequents are not affected. Furthermore,
no principal or side formula of an inference figure has been eliminated,
for if such a formula had contained a symbol V or 3, the principal formula
would certainly have contained that symbol. But no predicate inference
figures occur (if they did, the ordinal number of the inference figure would
be greater than zero), and by virtue of the subformula property (111.2.513)
and the hypothesis of theorem 2.1, the principal formulae of the proposi-
tional inference figures cannot contain a V or 3. Now every inference figure
remains correct if we eliminate, wherever it occurs as an S-formula in the
figure, a formula which occurs neither as a principal nor as a side formula.
This is easily seen from the schemata 111.1.21 and 111.1.22. (At worst, an
identical inference figure may result, which is then eliminated in the usual
manner.)
The sequent Gq*, which has resulted from Gq by this transformation,
differs from Gq in that certain S-formulae may possibly have been elimi-
nated. We follow the transformation up with several thinnings and inter-
changes such that in the end the sequent Gq reappears, and to it we attach
the unaltered lower part of the derivation.
We have now reached our goal: Gq* is the 'midsequent', and it obviously
satisfies all conditions imposed on the latter by theorem (2.1).

---

0 2, A SHAPRENED FORM OF THE Hauptsatz FOR CLASSICAL PREDICATE LOGIC
109
2.232. It now remains for us to carry out the induction step of our proof,
i.e., the order of the derivation is assumed to be greater than zero, and
our task is to diminish it.
2.232.1. We begin by redesignating the free object variables in the same way
as in 111.3.10. As a result of this, the derivation has the following property
(111.3.101):
For every V-IS (or 1-44) it holds that the eigenvariable in the derivation
occurs only in the sequent above the lower sequent of the V-IS (or 3-IA)
and does furthermore not occur in any other V-IS or 3-IA as an eigen-
variable.
The order of the derivation is hereby obviously left unchanged.
2.232.2. We now come to the transformation proper.
To begin with, we observe that in the derivation there occurs a predicate
inference figure - let us call it Sfl - with the following property: If we
follow that path of the inference figure which extends from the lower
sequent to the endsequent, then the first lower sequent of an operational
inference figure reached is the lower sequent of a propositional inference
figure (that inference figure we call 8f2). If there were no such instance, the
order of the derivation would be equal to zero.
Now our aim is to slide the inference figure Sfl lower down in the deriva-
tion beyond 8f2. This is easily done by means of the following schemata:
2.232.21. Suppose that Sf2 has one upper sequent.
2.232.211. Suppose that Sfl is a V-IS. Then that part of the derivation on
which the operation is to be carried out runs as follows:
r+ @,%a
V-IS
8f2, possibly preceded by structural inference figures.
+ 0 , V Z S E
A + A
This we transform into:
r + 0,
Sa
A + Sa, A
possibly several interchanges, as well as a thinning
possibly preceded by structural inference figures
3% Vb ?& inference figures of exactly the same kind as above, i.e., 3f2,
possibly several interchanges
A + 4 S a
V-IS
A + A, vx Sb possibly several interchanges and contractions.
A + A
The elimination of V& 3 g  by contraction in the last step of the trans-
formation is made possible by the fact that in A, Vg 8~ must occur as an

---

S-formula. (For the S-formula VF 3~
could not, in the original derivation,
have been eliminated from the succedent by means of 9f2 and the preceding
structural inference figures, since it can obviously not be a side formula of
3f2, by virtue of the subformula property 111.2.513 and the hypothesis of
theorem 2.1 .)
The restriction on variables is satisfied by the above V-IS (9fl) by virtue
of 2.232.1.
The order of the derivation has obviously been diminished by 1.
2.232.212. The case where 9fl is a 3-IS is dealt with analogously; all we
need do is to replace V by 3.
2.232.213. The cases where 3fl is a V-IA or 3-IA are treated dually to
the two preceding cases.
2.232.22. The case where 9f2 has two upper sequents, i.e., &-IS, v-IA, or
I-IA, can be dealt with quite correspondingly. At most a number of
additional structural inference figures may be required.
2.3. Analogously to theorem 2.1 there are several ways in which the Haupt-
satz may be further strengthened in the sense that certain restrictions can be
placed on the order of occurrence of the operational inference figures in
a derivation. For we can permute the inference figures to a large extent by
sliding them above and beyond each other as was done above (2.232.2).
We shall not pursue this question further.
6 3. Application of the sharpened Hauptsatz (2.1) to a newz6 consistency
proof for arithmetic without complete induction
By arithmetic we mean the (elementary, i.e., employing no analytic
techniques) theory of the natural numbers. Arithmetic may be formalized
by means of our logical calculus LK in the following way:
3.1. In arithmetic it is cubtomary to employ 'functions', e.g., x' (equals
x+ I), x+y, x * y. Since we have not introduced function symbols into our
logical formalism, we shall, in order to be able to apply it to arithmetic
nevertheless, formalize the propositions of arithmetic in such a way that
predicates take the place of functions. In place of the function x', for
example, we shall use the predicate xPry, which reads: x is the predecessor
of y, i.e., y = x+ 1. Furthermore, [x+y = z ]  will be considered a predicate
with three argument places. Thus the symbols + and = have here no
independent meaning. A different predicate is x = y ;  the equality symbol
here has thus no formal connection at all with the equality symbol in the
previous predicate.

---

9 3, APPLICATION OF THE sharpened Hauptsatz TO A CONSISTENCY PROOF
11 1
The number 1, furthermore, will not be written as a symbol for a definite
object, since we have only object variables in our logical formalism and no
symbols for definite objects. We shall overcome this difficulty by saying that
the predicate 'One
means informally the same as 'x is the number 1'.
The sentence 'x+ 1 is the successor of
for example, could be rendered
thus in our formalism:
All other natural numbers can be respresented by the predicates
One x & xPry; One x & xPry & yPrz, etc.
How are we now to integrate into our calculus the predicate symbols just
introduced, having admitted only propositional variables? To do so we
simply stipulate that the predicate symbols are to be treated in exactly the
same way as propositional variables. More precisely: We regard expressions
of the form
One F 7  FPr97 F = 9 7  (F+9 = a),
where any object variables stand for E, 9, g, merely as more easily intelligible
ways of writing the formulae
In this sense the axiom formulae that follow are indeed formulae in accor-
dance with our definition.
(We cannot, of course, regard the number 1 as a way of writing an object
variable, since in our calculus the object variables really function as variables,
which is not so in the case of propositional variables.)
As 'axiom formulae' of our arithmetic we shall initially take the following,
and shall later, once the consistency proof has been carried out (cf. 3.3),
statq general criteria for the formation of further admissible axiom formulae:
Equality :
vx (x = x)
(reflexivity)
VxVyVz((x = y & y  = z) 3 x  = 2)
3x (One x)
VxVy ((One x & Oney) 3 x = y)
VxVy(x = y 3
y = x)
(symmetry)
(transitivity)
(existence of 1)
(uniqueness of 1)
One:
Predecessor:
Vx 3y (xPry)
(existence of successor)

---

Vx Vy (xpry 3 One y)
(1 has no predecessor)
Vx Vy Vz Vu ((xpry & zPru & x = z) 3
y = u) (uniqueness of successor)
Vx Vy Vz Vu ((xPry & zPru & y = u) 3
x = u) (uniqueness of predecessor).
A formula 23 is called derivable in arithmetic without complete induction,
if there is an LK-derivation for a sequent
al, . . .
y a# + 23
in which gl,
. . . Up are axiom formulae of arithmetic.
The fact that this formal system does actually allow us to represent the
types of proof customary in informal arithmetic (as long as they do not use
complete induction) cannot be proved, since for considerations of an in-
formal character no precisely delimited framework exists. We can merely
verify this in the case of individual informal proofs by testing them.
3.2. We shall now prove the consistency of the formal system just presented.
With the help of the sharpened Hauptsatz (2.1) our task is in fact quite
simple.
3.21. A 'contradiction' & 1
% is derivable in our system if and only if
there exists an LK-derivation for a sequent with an empty succedent and
with arithmetic axiom formulae in the antecedent, viz.:
From r + % &
% we obtain r + in the following way:
7 - I A
% + %
&-IA
interchange
contraction
cut.
&-IA
r+
The converse is obtained by carrying out a thinning in the succedent.
Thus, if our arithmetic is inconsistent, there exists an LK-derivation
with the endsequent
a1 Y * - - 9 ap +,
where
. . . %p are arithmetic axiom formulae.
3.22. We now apply the sharpened Hauptsatz (2.1). The arithmetic axiom
formulae fulfil the requirement laid down for the S-formulae of the end-
sequent. Hence there exists an LK-derivation with the same endsequent
which has the following properties:

---

0 3, APPLICATION OF THE sharpened Hauptsatr TO A CONSISTENCY PROOF
113
1. It contains no cuts.
2. It contains a D-sequent. the 'midsequent', whose derivation contains
no V and 3-symbols, and whose endsequent results from a number of
inference figures V-IA, 34A, thinnings, contractions and interchanges in
the antecedent. The midsequent has an empty succedent (2.11).
3.23. We then proceed to redesignate the free object variables as in 111.3.10.
All mentioned properties remain unchanged, and the following property
is added (111.3.101): The eigenvariable of each 3-IA in the derivation occurs
only in sequents above the lower sequent of the 3-IA.
3.24. Then we replace every occurrence of a free object variable by one and
the same natural number in a way to be described presently. In doing so
we are left with a figure which we can no longer call an LK-derivation.
We shall see later to what extent it nevertheless has an informal sense.
The replacement of the free object variables by numbers is carried out
in the following order:
3.241. First we replace all free object variables which do not occur as the
eigenvariable of a 3-IA by the number 1 throughout. (We could also take
another number.)
3.242. Then we take every 3-IA inference figure in the derivation, beginning
with the lowest and taking each figure in turn, and replace each eigenvariable
(wherever it occurs in the 'derivation') by a number. That number is deter-
mined as follows:
The 3-IA can only run:
One a, r + 0
vPra, r -+ 0
or
3x One x ,  r --+ 0
3y vPry,
+ 0
(by virtue of the subformula property 111.2.513; v can be only a number,
by virtue of 3.241 and 3.23). In the first case we replace a by 1, in the second
case by the number that is one greater than v .
3.25. Now we examine the figure which has resulted from the derivation.
We are particularly interested in what the (former) midsequent now looks
like. We can say this about it:
Its succedent is empty, and each of the antecedent S-formulae either has
the form One 1 or vPrv', where a number stands for v, and where a number
one greater than the previous one stands for v'; or it results from an arith-
metic axiom formula that has only V-symbols at the beginning, by the
elimination of the V-symbols (and the bound object variables next to them)
and the substitution of numbers for the bound object variables in the

---

remaining part of the formula. (All this follows from the same consideration
as in 111.2.512, also cf. 2.11.)
Thus, the S-formulae in the antecedent of the midsequent represent
informally true numerical propositions. It further holds for the 'derivation'
of the midsequent that it has resulted from a derivation containing no
V- or 3-symbols, by having all its occurrences of free object variables
replaced by numbers. Informally, such a 'derivation' constitutes in effect a
proof in arithmetic using only forms of inference from propositional logic.
This leads us to the following result:
If our arithmetic is inconsistent, we can derive a contradiction from true
numerical propositions through the mere application of inferences from
propositional logic.
Here 'true numerical propositions' are propositions of the form One 1,
vPrv', as well as all numerical special cases of general propositions occurring
among the axioms such as, e.g., 3 = 3, 4 = 5 3 5 = 4, 3Pr4 3 1
One 4.
It is almost self-evident that from such propositions no contradictions
are derivable by means of propositional logic. A proof for this would hardly
be more than a formal paraphrasing of an informally clear situation of fact.
Such a proof will therefore not be carried out save for indicating briefly
the customary procedure for it:
We determine generally for which numerical values the formulae
One p, p = v, pPrv, p+v = p, etc., are true and for which values they are
false; furthermore, we explain in the customary way (cf., e.g., Hilbert-
Ackermann p. 3) the truth or falsity of 8 & 58, 8 v 23, 1
a, and
3 23,
as functions of the truth or falsity of the subformulae; we then show that all
numerical special cases of axiom formulae are 'true'; and finally, that
inference figures of propositional logic always lead from true formulae
to other true formulae. A contradiction, however, is not a true formula.
3.3. It is easy to see from the remarks made in 3.25 in what way the system
of arithmetic axiom formulae may be extended without making a contra-
diction derivable in it: Quite generally, we can allow the introduction of
axiom formulae that begin with V-symbols spanning the whole formula,
which do not contain any 3-syrnbols, and of which every numerical special
case is informally true. (We could also admit certain formulae containing
hymbols, as long as they can be dealt with in the consistency proof in a
way analogous to that of the two cases occurring above.)
E.g., the following axiom formulae for addition are admissible:
VxVy (xpry =I [x+I = y1)

---

5 1, THE CONCEPT OF EQUIVALENCE
V X V ~ V Z V U V U
((.Pry
& [z+x = u ]  & [z+y = u ] )  =) upru)
v x  vy vz v u  (( [x+y = z ]  & [x+y = u ] )  =) z = u)
v x v y v z  ( [ x + y  = z ]  3 [ y + x  = z l )
etc.
3.4. Arithmetic without complete induction is, however, of little practical
significance, since complete induction is constantly required in number
theory. Yet the consistency of arithmetic with complete induction has not
been conclusively proved to date.
SECTION V. THE EQUIVALENCE OF THE NEW CALCULI NJ, NK,
AND LJ, LK WITH A CALCULUS MODELLED ON THE
FORMALISM OF HILBERT
5 1. The concept of equivalence
1.1. We shall introduce the following concept of equivalence between
formulae and sequents (which is in harmony with what was said in 1.1.1
and 1.2.4, concerning the informal sense of the symbol A and of sequents:
Identical formulae are equivalent.
Identical sequents are equivalent.
Two formulae are equivalent if the replacement of every occurrence of the
A yields the other formula.
The sequents Z1,.
. . , aP + Bl,
. . . , Bv is equivalent to the following
If the 2l's and B's are not empty:
symbol A in one of them by the formula A &
formula:
(al & . . . & aP) 3 (Bv v . . . v B1);
(this version is more convenient for the equivalence proof than that with
Bl v . . . v Bv); if the a's are empty, but the %'s are not:
Bv v.. . v ,823,;
(al & . . . & ap) 3
( A  & 1
A);
if the 23's are empty, but the a's are not:
if the Ws and the 8's are empty:
A & T A .
The equivalence is transitive.

---

INVESTIGATIONS INTO LOQICAL DEDUCTION
1.2. (We could of course give a substantially wider definition of equivalence,
e.g., two formulae are usually called equivalent if one is derivable from the
other. Here we shall content ourselves with the particular definition given,
which is adequate for our proofs of equivalence.)
Two derivations will be called equivalent if the endformula (endsequent)
of one is equivalent to that of the other.
Two calculi will be called equivalent if every derivation in one calculus
can be transformed into an equivalent derivation in the other calculus.
In 0 2 of this section we shall present a calculus (LHJ for intuitionist,
LHK for classical predicate logic) modelled on Hilbert's formalism. In the
remaining paragraphs of this section we shall then demonstrate the equiv-
alence of the calculi LHJ, NJ, and L J  ($0 3-5) as well as the equivalence of
the calculi LHK, NK, and LK (0 6) in the sense just explained. We shall thus
successively prove the following:
Every LHJ-derivation can be transformed into an equivalent NJ-deriva-
tion (8 3); every NJ-derivation can lye transformed into an equivalent
LJ-derivation (0 4); and every LJ-derivation can be transformed into an
equivalent LHJ-derivation (0 5). This obviously proves the equivalence of all
three calculi. The three classical calculi are dealt with analogously in 0 6
(6.1-6.3).
6 2. A logistic calculus according to Hilbert2' and Glivenko28
We shall begin by explaining the intuitionist form of the calculus:
An LHJ-derivation consists of formulae arranged in tree form, where
the initial formulae are basic formulae.
The basic formulae and the inference figures are obtained from the
following schemata by the same rule of replacement as in 11.2.21, i.e.:
For %, '23, B, put any arbitrary formula; for VX & or 3~ '& put any arbitrary
formula with V or 3 for its terminal symbol, where x designates the associated
bound object variable; for g a  put that formula which results from
by
the replacement of every occurrence of the bound object variable
by the
free object variable a.
2.11. cu: 3 cu:
2.12.
2.13.
(% 3 (a
23)) =I (3 3 %)
2.14.
Schemata for basic formulae:
9i 3
(23 3 9i)
(a 3
('23 3 G)) 3 (23 3 ((ZI 3 G))

---

0 3, TRANSFORMATION OF AN LHJ-DERIVATION
117
2.15.
2.21.
2.22.
2.23.
2.31.
2.32.
2.33.
2.41.
2.42.
2.51.
2.52.
((21 3
23) 3 ((23 3 G) = (a = G))
(a&B) 3%
((21&23) 3 23
((21 =J 23) 3
(((21 3 G) 3 ((21 3 (8 & 6)))
%=,(%V%)
B = ((21vB)
(a 3 G) 3 ((23 3 G) = (((21v 23) = G))
(% = 23) = (((21 3 123) = 1
a)
(7
a) = ((21 3 B)
V.si?z
3a
3a = 3 z  3.s.
(Several of the schemata are dispensable, but independence does not
Schemata for inference figures:
concern us here.)
a
( 2 1 3 %
a33a
Ba 3 (21
B
(21 = V z %
( 3 E W  3%.
Restriction on variables: In the inference figures obtained from the last
two schemata, the object variable, designated by a in the schema, must not
occur in the lower formula (hence not in
and 3:~).
(The calculus LHJ is essentially equivalent to that of Heyting".)
By including the basic formula schema
v 7 (21, the calculus LHK
(This latter calculus is essentially equivalent to the calculus presented in
(classical predicate calculus) results.
Hilbert-Ackermann, p. 53.)
8 3. Transformation of an LHJ-derivation into an equivalent NJ-derivation
From an LHJ-derivation (V.2) we obtain an NJ-derivation (11.2) with
the same endformula by transforming the LHJ-derivation in the following
way: (In this transformation all D-formulae of this derivation will reappear
as D-formulae of the NJ-derivation, and they will not depend on any assump-
tion formula. Included further will be other D-formulae dependent on
assumption formulae.)
3.1. The LHJ-basic formulae are replaced by NJ-derivations according to
the following schemata:

---

(2.11)
(2.13)
(2.14)
(2.15)
1

1
(a =) (23 36))
=) (23 3 (a 3 6))
1
3

(2.12)
1
&-E
2.22, 2.31, 2.32, 2.51 and 2.52 are dealt with analogously to 2.21.
1
3

1
2

---

0 3, TRANSFORMATION OF AN LHJ-DERIVATION
119
1
4

1
3
3 - E  '
3 - E
2
a a = %
(2.33)
V-E 1
% V B
Q
Q
rr
1
3

1
2

3 - E
% a3123
3 - E
% %I23
(2.41)
23
1 B
A
~
1-11
1%
(a 3 123) = 7
a
(a = 23) = ((a 3 1
23) 3 1
a)
=-I,
3 - I 3
1
2

(2.42)
a l a
7 - E
A
3-11
(1
a) = (a =) 93)
B
a323
=-I,.
3.2. The LHJ-inferenceJigures are replaced by sections of an NJ-derivation
according to the following schemata:
remains as it is, since it has already the form of a 3-E.
%a323
23
1

---

The restriction on variables for V-I and 3-E is satisfied, as is easily seen,
by virtue of the restriction on variables existing for LHJ-inference figures.
This completes the transformation of an LHJ-derivation into an equiv-
alent NJ-derivation.
5 4. Transformation of an NJ-derivation into an equivalent LJ-derivation
4.1. We proceed as follows: First we replace every D-formula of the NJ-
derivation by the following sequent (cf. 111.1.1): In its succedent only the
formula itself occurs; in its antecedent occur the assumption formulae upon
which the sequent depended, and they occur in the same order from left
to right as they did in the NJ-derivation. (It is presumably clear what is
meant by the order from left to right of the initial formulae of a figure in
tree form.)
We then replace every occurrence of the symbol A by A & 1
A. (The
formula resulting from A in this way will be designated by A*.)
4.2. We thus already have a system of sequents in tree form. The antecedent
of the endsequent is empty (11.2.2); it is obviously equivalent to the end-
sequent of the NJ-derivation. The initial sequents a11 have the form %* --* %*
(11.2.2) and are thus already basic sequents of an LJ-derivation.
The figures formed from NJ-inferencefigures are transformed into sections
of an LJ-derivation according to the following schemata:
4.21. The inference figures v-I, V-I, and 3-1 have become LJ-inference
figures as a result of the substitution performed. (In the case of a V-I,
the LJ-restriction on variables is satisfied by virtue of the NJ-restriction on
variables.)
4.22. A &-I became:
r+8*
A + @ *
r , A + a * & B T '
This is transformed into:

---

5 4, TRANSFORMATION OF AN NJ-DERIVATION
121
r + a* possibly several inter-
r, A + a* changes and contractions r, A + B*
r, A + %* & B*
A + B* possibly several
thinnings
&-IS.
4.23. A =-I became:
rl,
%*, r2,.
. . ,%*, rp + B*
rl, r 2 , .
. . , rp + %* 3 B*
*
This we transform into:
rl
9 %*?
r2
9 * - * 9 a*, r~ + B* possibly several interchanges and
contractions, sometimes a thinning
a*, r,, r,, . . . , r, + B*
I"
- D - l A .
-
-

__ r1,r2,.
. . ,rp
-+ a* 3 B*
4.24. The same procedure applies to a l-I. Finally, we still have to consider
the figure
First we derive A &
A -+ in the calculus LJ as follows:
7 - I A
&-IA
A + A
i A , A +
A & i A , A +
A , A & - I A +
A & i  A , A & T A +
A & 7 A - +
interchange
contraction.
&-IA
By including this sequent, the figure in question is transformed as follows:
% * , r + A & 7 A
A & T A +  cut
1 - I S .
8*,
r +
r+7a*
A
5D
4.25. By substitution (4.1) the NJ-inference figure - became:
This is transformed into:

---

T - t A & T A
A & i A +  cut
r +
r + a*
thinning.
The derivation for A &
written above that sequent.
4.26. A V-E became:
A +, as presented in 4.24, should here still be
r + vx ~ * x
r+S*a
'
This is transformed into:
4.27. The same method is used for &-E.
4.28. A 2-E became:
r+%* A + % *  3 B *
r, A + B*
This is transformed into:
A,r+ B*
r , A + B *
possibly several interchanges.
4.29. A --E
became:
This is transformed into:
1 - I A
r + %*
A + T % *
,%*,r-t
- cut
A,r+
possibly several interchanges
thinning.
r, A -+
r, A -+ A & 7
A

---

5 5, TRANSFORMATION OF AN LJ DERIVATION
123
4.2.10. v-E. Both right-hand upper sequents are followed up, as in the case
of a 3-I and 7-1 (4.23) above, by interchanges, contractions, and thinnings
(wherever necessary) so that in each case the result is a sequent in whose
antecedent occurs a formula of the form %* or B* at the beginning (whereas
the original assumption formulae involved have been absorbed into the rest
of the antecedent). Then follows:
possibly several thinnings
B*, A
Q* possiblyseveralthinnings
23*, r, A -+ 0.
--t
* and interchanges
V-IA
* and interchanges
%*, r, A -, Q
E -, %* v 23*
%* v %*, r, A -, Q* cut.
4.2.11. A 3-E is treated quite similarly: First we move S*
a in the right-hand
upper sequent to the beginning of the antecedent (cf. 4.23); then follows:
E, r, A -+ Q*
b,r -, Q*
The LJ-restriction on variables for 3-IA is satisfied by virtue of the NJ-
This completes the transformation of an NJ-derivation into an equivalent
restriction on variables for 3-E.
LJ-derivation.
§ 5. Transformation of an LJ-derivation into an equivalent LHJ-derivation
This transformation is a little more difficult than the two previous ones.
We shall carry it out in a number of separate steps.
Preliminary remark: Contractions and interchanges in the succedent do
not occur in the calculus LJ, since they require the occurrence of at least
two S-formulae in the succedent.
5.1. We first introduce new basic sequents in place of the figures &-IA,
v-IS, V-IA, %IS, -,-IA, and I-IA; these are to be formed according to
the following schemata (rule of replacement as in 111.1.2 - the same rule
will always apply below; in addition to the letters 8,
23, By and 6 we shall
also, incidentally, use the letters, 6, $, and 3):
2351: M & B + %
2332: % & 2 3 + 2 3
2333: %+Mv23
2334: 23+Mv23
2355: VF 3~ -, %a
23G6: Sa -+ 3~ 3~
2357: 1
M, M -+
2358: M 3
23, % -+ 23.

---

Thus in the LJ-derivation to be considered, we transform the inference
A &-IA becomes :
figures concerned in the following way:
2331
a&%-+%
a,r+o cut.
imB,r+o
The other form of the &-IA is transformed correspondingly, so is every
v-IS and 3-1s are dealt with symmetrically.
A 7-IA becomes:
&-IA.
2337
+ interchange
cut
r + 8  aYl8+
r,-a+
lix,r+
possibly several interchanges.
(The 0 in the schema of - 1 4 4  (111.1.22) must be empty by virtue of the
LJ-restrictions on succedents; the same holds for the 5 I A . )
A z-ZA becomes:
B38
" +
interchange
8
8 , 8 3 b + B c u t
cut
rY8=%-+8
2 3 , A + A
r, 8 3 By
A + A
possibly several
8 3  23, r, A + A
interchanges.
5.2. We now write the formula A &
A in the succedent of all D-formulae
whose succedent is empty.
In doing so the basic sequents of the form 5B + 9, as well as 2331 to
2336 and 2338, also the figures &-IS, V-IS, and =-IS, remain unchanged.
The other basic sequents and inference figures are transformed into new
basic sequents and inference figures according to the following schemata:
2339: a, 7 a + @

---

0 5, TRANSFORMATION OF AN LJ-DERIVATION
125
(For 3f7 the reexists the following restriction on variables: The free object
variable designated by a must not occur in the lower sequent.)
5.3. The inference figure 3f4 is now replaceable by other figures as follows
(this is mainly due to our having kept general the form of the schema 93359):
B62
3f5
BS9
r - + a 1 A
A & ~ A - + ~ A
3f5
r - + T A
i A , A - + %
%Sl
r , A - + %  possibly several
A, r -+ B af5
3 f 5
T + A & l A
A & i A - + A
T + A
r,r+%
1-39
possibly several
and
In a similar way we replace the inference figure 3f8 (wherever it occurs
in the derivation), only this time we use a new inference figure according
to the following schema:
I - , % + A
r , % - + l A
3f9 :
r - + T A
We substitute as follows (in place of Sf8):
23351
m 2
3f5
% , ~ - + A & ~ A
A & ~ A - + ~ A
% , r - + i A
I-,%-+
A
r , % - + T A
3 f 5
~
+
~
s
!
i

Q , ~ - + A & ~ A
A & ~ A - + A
8 , r - A  possibly several
possibly several 3f3's
3j9.
5.4. Now we still introduce two new inferenceJigures schemata, viz.:

---

and its converse:
The two types of inference figures are introduced into the derivation in
order to enable us to replace a number of other inference figures by more
specialized ones (in 5.42 and 5.43).
5.41. To begin with, ='-IS inference figures are now replaceable by means
of 3 f l O :
A =-IS is transformed into:
- 1 -  -
-J
"-I----
"=. ,-.
5.42. The inference figures 3f1, 3f2, 3f3, 3f5, Sf6, and 3f7 are then trans-
formed in the following way:
As an example we take an 3f2, which is transformed into the followdg
figure (suppose r equals S1, . . . , 3,):
3f10
several
Sf13
several
Sf lo's
3fll's.
We proceed quite analogously with all other figures mentioned, i.e.,
using 8 f l O  and Sfll, we replace them by inference figures according to
these schemata:
(For 3f17 there exists a restriction on variables: The free object variable
designated by a must not occur in the lower sequent.)
5.43. In a similar way we also replace the inference figures 3f9, 3f13, and
3f14 by the following (using 8 f l O  and 3fll):

---

5 5, TRANSFORMATION OF AN LJ-DERIVATION
127
+ sb 3
(5D 3 0.)
3f19:
r - - + % = ~
r + % D I A
A + sb 3
(0: 3 0.)
fl + E 3 (sb D 0.)
*
8f18:
r j 7 %
j s b 3 G
8f20 :
The basic sequents 2338 and 2339 may be replaced in the same way by:
% 3
23 + % 3 23, this form falls under the schema sb + 3;
as well as
23310: 1
% + ill 3
@.
5.5. Now comes theJinal step:
Every D-sequent
%I , . . . , %@ + 23
is replaced by the formula
(If the Ws are empty, we mean 23. An empty succedent no longer occurs,
according to 5.2.)
All basic sequents (viz. sb + 9, 2331 to 2336, 23310) are thus transformed
into LHJ-basic sequents.
OF the inference figures, V-IS and 3f17 are also transformed into LHJ-
inference figures. (V-ZS, however, forms an exception if r is empty. In that
case we first derive (in the LHJ-calculus) (A 3
A )  3 Sa from Sa by means
of 2.12, and by then applying the LHJ-inference figure, we finally obtain
VF 3s once again by means of 2.11.)
The figures obtained from the remaining inference figures (which are
&-IS, Sflo, 11, 12, 15, 16, 18, 19, 20) by substitution, are turned into
sections of an LHJ-derivation in the following way:
& . . . &
3
23.
An &-IS has become (suppose first that r is not empty):
G 3 %  6 3 %
This is transformed into:
0.323
(0. 3 %) 3 (0. 3
(% & 23))
G 3(%&%)
If r is empty, we proceed as in the case of V-ZS.
The figures obtained from 8f12, 15, 16, and 19 by substitution are
dealt with quite analogously using basic formulae according to the schemata
2.12, 2.15, 2.33, and 2.13.

---

In a similar way 3f18 and 3f20 are dealt with by means of 2.41 and 2.14
and by the application of 2.15 and 2.14, 2.13.
The only figures now left are those having resulted from 8 f l O  and8f11.
Both are trivial for an empty T,
hence suppose that r is not empty. In that
case we transform these figures into sections of LHJ-derivations as follows:
(3flO): From (Q & %) 13 B we have to derive 0. 3 (a 3 23). Now 2.23
together with 2.11 yields: (Q 3 %) 3 (0: 3 (0. & a)). This together with
(0. & 8)
3 23 and 2.15, 2.14 yields (0. 3
%) 2 (0. 13 %), and from this
formula together with 2.12, 2.15 yields % 13 (0. 3 B), and by 2.14
0. 13 (a 3 '3) results.
(3fll): From B 13 (3 13 23) we derive (Q & a) 13 B in the LHJ-calculus
as follows: 2.21 and 2.22 yield (6 & a) 3 Q and (6 & %) 13 %; and from
this together with Q 3 (% 3 Ti), we obtain (0. & a) 13 23 (by using 2.15,
2.14, 2.15, 2.13).
This completes the transformation of the LJ-derivation into an LHJ-
derivation. Furthermore, the two derivations really are equivalent, since the
endsequent of the LJ-derivation was affected only by the transformations
5.2 and 5.5, and has thus obviously been transformed into a formula
equivalent with it (according to 1.1).
If the results of $0 3-5 are taken together, the equivalence of the three
calculi LHJ, NJ, and L J  is now fully proved.
4 6. The equivalence of the calculi LHR, NK, and LK
Now that the equivalence of the different intuitionist calculi has been
proved, it is fairly easy to deduce that of the classical calculi.
6.1. In order to transform an LHK-derivation into an equivalent NK-
derivation we proceed exactly as in 0 3. The additional basic formulae
according to the schema % v 1
% remain unchanged, and are thus at once
basic formulae of the NK-derivation.
6.2. In order to transform an NK-derivation into an equivalent LK-deriva-
tion we proceed initially as in 0 4. In this way the additional basic formulae
according to the schema
v
% are transformed into sequents of the
form -+ %* & 7 %*. These we then replace by their LK-derivations
(according to 111.1.4). The transformation of an NK-derivation into an
equivalent LK-derivation is thus complete.
6.3. Transformation of an LK-derivation into an LHK-derivation.
following respect:
We introduce an auxiliary calculus differing from the LK-calculus in the

---

0 6, THE EQUIVALENCE OF THE CALCULI LHK, NK AND LK
Inference figures may be formed according to the schemata 111.1.21,
111.1.22, but with the following restrictions: Contractions and interchanges
in the succedent are not permissible; in the remaining schemata no substitu-
tion may be performed on 0 and A; these places thus remain empty.
Furthermore, the following two schemata for inference figures are added
(rule of replacement as usual: 111.1.2):
and its converse:
(Thus, here 0 need not be empty.)
6.31. Transformation of an LK-derivation into a derivation of the auxiliary
calculus:
(The procedure is similar to that in 5.4.)
All inference figures, with the exception of contractions and interchanges
in the succedent, are transformed according to the following rule: The
upper sequents are followed by inference figures Sfl, until all formulae of
0 or A have been negated and brought into the antecedent (to the right of
r or A ) .  Then follows an inference figure of the same kind as the one just
transformed, which is now actually a permissible inference figure in the
auxiliary calculus. (The formulae that have been brought into the antecedent
are treated as part of r or d.) Then follow 3f2 inference figures, and 0
and A are thus brought back into the succedent. (In the case of the =-ZA
and the cut, we may first have to carry out interchanges in the antecedent,
but these are also permissible inference figures in the auxiliary calculus.)
Now we still have to consider contractions - or interchanges - in the
succedent. Here, as in the previous case. the whole succedent is negated and
brought forward into the antecedent. We then carry out interchanges, a
contraction, and further interchanges - or one interchange - in the antece-
dent, and then the negated formulae are brought back into the succedent
(bq means of the inference figures Sf2).
6.32. Transformation of a derivation of the auxiliary calculus into a deriva-
tion of the calculus L J  augmented by the inclusion of the basic sequent
schema -, v
a:
We begin by transforming all D-sequents as follows:
%I 3 . . . , afl
--+ '231 , . . . , '23" becomes

---

U1, . . . ,
+ '23" v . . . v Bl . If the succedent was empty, it remains empty.
Now all basic sequents or inference figures of the auxiliary calculus with
the exception of the figures Sfl and Sf2, have thus already become basic
sequents or inference figures of the calculus LJ. This is so since these
inference figures have resulted from the schemata 111.1.21 , 111.1.22 (with the
exception of the schemata for contraction and interchange in the succedent)
by 0 and A always having remained empty. At most one formula could
therefore occur in the succedent.
Hence we still have to transform the figures which have resulted from the
inference figures 3fl and 3f2 in the course of the above modification.
6.321. First Sfl: If 0 is empty, we replace the inference figure by a l-L4,
followed by interchanges in the antecedent. Suppose, therefore, that 0 is
not empty, where O* designates the formulae belonging to 0, in reverse
order and connected by v.
After the transformation of the succedents, the inference figure in that
case rum as follows:
r - + o * v 8
r, 8- o*
This is transformed into the following section of an LJ-derivation:
% + %
o* + o*
1%,8-+
%,7%+
8, 7 8 + o*
thinning
interchange
1
%, o* + o*
o*, 1 8
-+ o*
r, 8 -+ o*
o* V%, 7 8 + o* cut.
~ .-_I._-
r + o * v 8
1 - I A
interchange
thinning
V-IA
6.322. After the transformation of its succedents, an inference figure 3f2
runs as follows:
r, 4 x - +  o*
r + o * V &
where @* has the same meaning as in the previous case. If 0 is empty,
assume @* to be empty too, and let @* v 8 mean 8.
It is transformed into the following section of a derivation:

---

6, THE EQUIVALENCE OF THE CALCULI LHK, NK AND LK
131
* %possibly several thin- r,
% * @*possibly several
nings and interchanges
* interchanges
la,r-,o
v-IS
v-IS
V-IA
%,r-+%
%,r
-+ @ * v %
%, r -, o* v %
cut.
-,%v-l%
% V
%, r -, o*vt?i
r-,o*v%
It is easy to see that in the case of an empty 0 all is in order.
6.33. The LJ-derivation now obtained, together with the additional basic
sequents of the form + 8 v 1
%, may be transformed, as in 0 5, into an
LHJ-derivation with the inclusion of additional basic formulae of the form
% v 1
% (cf. 5.5), i.e., into an LHK-derivation. This completes the trans-
formation of the LK-derivation into an LHK-derivation. At the same time,
the endsequent has been transformed (in accordance with 6.32,5.2, and 5.5)
into an equivalent formula (according to 1.1).
By combining the results of 6.1, 6.2, and 6.3, we have now also proved
the equivalence of the three classical calculi of predicate logic: LHK, NK,
and LK.