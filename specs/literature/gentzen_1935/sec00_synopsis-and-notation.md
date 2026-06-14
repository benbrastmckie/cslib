<!-- Source: Gentzen, G. (1935). Untersuchungen über das logische Schließen (Investigations into Logical Deduction). Synopsis and Section I: Terminology and Notation. BibKey: Gentzen1935 -->

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
