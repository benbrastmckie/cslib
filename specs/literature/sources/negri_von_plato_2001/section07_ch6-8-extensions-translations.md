# Structural Proof Theory — Chapters 6-8: Extensions, Intermediate Logics, ND-SC Translations (lines 6064-11735)

6.1. F R O M AXIOMS TO RULES

When classical logic is used, all free-variable axioms (purely universal axioms)
can be turned into rules of inference that permit cut elimination. The constructive
case is more complicated, and we shall deal with it first.

(a) The representation of axioms as rules: We shall be using the intuitionistic
multisuccedent sequent calculus G3ipm of Section 5.3. In adding nonlogical rules
representing axioms, we follow

Principle 6.1.1: In nonlogical rules, the premisses and conclusion are sequents
that have atoms as active and principal formulas in the antecedent and an arbi-
trary context in the succedent.
126
                       STRUCTURAL PROOF ANALYSIS                                     127

The most general scheme corresponding to this principle, with shared contexts, is

                         gl r A
                           ' ^, .,/> m ",r,S'I^ A * eg
where F, A are arbitrary multisets, P i , . . . , P m , <2i> • • •» Qn are fixed atoms, and
the number of premisses n can be zero.
   Once we have shown structural rules to be admissible, we can conclude that
a rule admitting several atoms in the antecedents of the premisses reduces to as
many rules with one atom; for example, the rule

                            2i,G2,r=^A            P,F=^A

                                       p, r
reduces to the two rules


                      p, r => A                             p, r =» A
The second and third rule follow from the first by weakening of the left premiss. In
the other direction, weakening R,T =>• A to P, Q2S =>• A, we obtain the con-
clusion P, Q2, F =>• A from Qi* <22, F =>• A by the second rule, and weakening
again P, F =>• A to P, P, F =>• A, we obtain by the third rule P, P, F => A,
which contracts to P, F =>> A. This argument generalizes, so we do not need to
consider premisses with several atoms.
   The full rule-scheme corresponds to the formula Pi & . . . &Pm D Q1 v . . . v Qn.
In order to see what forms of axioms the rule-scheme covers, we write out a few
cases, together with their corresponding axiomatic statements in Hilbert-style
calculus. Omitting the contexts, the rules for axioms of the forms Q&R,        QvR,
and P D Q are
              Q =» A      R ^   A       Q => A      P => A         Q => A


The rules for axioms of the forms Q,~ P and ~ (Pi&P 2 ) are
                       Q ^ A
                        =^ A          P=^A            Pi,P2^A

  We recall the definition of regular sequents and their trace formulas from
Section 3.1: A sequent is regular if it is of the form

                                         Qu...,Qn,±,...,±
where the number of occurrences of _L, m, and n can be 0, and Pt ^ Qj for all
/, j . Regular sequents are grouped into four types, each with a corresponding
128                   STRUCTURAL PROOF THEORY

trace formula:

  1. A & . . . &Pm D Qi V . . . V Qn if m > 0, n > 0,
  2. Qx V ... V Qn if m = 0, n > 0,
  3. ~ ( P i & . . . & P w ) if m > 0,n = 0,
  4. _L if m = 0, n = 0.
Regular sequents are precisely the sequents that correspond to rules (Latin
"regulae") following our rule-scheme. In terms of the rule-scheme, the formation
of trace formulas corresponds to the deletion of all but one of several identical
premisses in a rule when any of the Qj are identical and to the contraction of
repetitions in the antecedent of the conclusion when any of the Pt are identical.
   Given a sequent =>• A, we can perform a root-first decomposition by means
of the rules of G3ipm. If the decomposition terminates, we reach leaves that are
either axioms or conclusions of L_L or regular sequents. Among such leaves,
we distinguish those that are reached from =>• A by "invertible paths," ones that
never pass via a noninvertible rule of G3ipm:

Definition 6.1.2: In a terminating decomposition of a sequent => A in G3ipm,
if a topsequent is reached without passing through the left premiss ofLD or via
an instance ofRD with a nonempty context A in its conclusion, it is an invertible
leaf, and in the contrary case it is a noninvertible leaf.

We now define the class of regular formulas:

Definition 6.1.3: A formula A is regular if it has a decomposition that leads
to invertible leaves that are logical axioms, conclusions of L_L, or regular se-
quents and noninvertible leaves that are logical axioms or conclusions of
L±.

We observe that the invertible leaves in a decomposition of =$• A are independent
of the order of decomposition chosen, since any two rules among L&, RSc, Lv,
Rv, and RD with empty right context A commute with each other, and each of
them commutes with the right premiss of LD. This uniqueness justifies:

Definition 6.1.4: For a regular formula A, its regular decomposition is the set
{A\,..., Ak], where the At are the formula traces of the regular sequents among
the invertible leaves of A. The regular normal form of a regular formula A is


Note that the regular decomposition of a regular formula A is unique, and A is
equivalent to its regular normal form. Thus regular formulas are those that permit
a constructive version of a conjunctive normal form, one in which each conjunct is
an implication of form P\8c... &Pm D Q\ V . . . V Qn, instead of the classically
                       STRUCTURAL PROOF ANALYSIS                                   129

equivalent disjunctive form ~ Pi v . . . v ~ Pm V Q\ V . . . v Qn. The class of
formulas constructively equivalent to usual conjunctive normal form is strictly
smaller than the class of formulas having regular normal form. The following
proposition shows some closure properties of the latter class of formulas:

Proposition 6.1.5:

   (i) If A has no Z>, then A is regular.
   (ii) If A, B are regular, then A&B is regular.
   (iii) If A has no D and B is regular, then A D B is regular.

Proof: (i) By invertibility of the rules for & and V. (ii) Obvious, (iii) Start-
ing with RD, a decomposition of =>• A D B has invertible leaves of the form
P i , . . . , Pm, F =>• A, where Pi,..., Pm are atoms (from the decomposition of A)
and F => A is either a logical axiom or a regular sequent. Thus also
P i , . . . , Pm, F =>• A is either a logical axiom or a regular sequent. QED.

From the two cases of noninvertible rules we see that typical formulas that need
not be regular are disjunctions that contain an implication and implications that
contain an implication in the antecedent. But sometimes even these are regular,
such as the formula (P D Q) D (P D R).
   In the next section we show that the class of regular formulas consists of
formulas the corresponding rules of which commute with the cut rule. The reason
for adopting Principle 6.1.1 will then be clear.

(b) Extension of classical systems with nonlogical rules: For the extension of
classical systems, we use the classical multisuccedent sequent calculus G3c in
which all structural rules are built in. All propositional rules of G3c are invertible,
but instead of analyzing regularity of formulas through decomposability as in
Section 3.1, we can use the existence of conjunctive normal form in classical
propositional logic: Each formula is equivalent to a conjunction of disjunctions of
atoms and negations of atoms. Each conjunct can be converted into the classically
equivalent form P i & . . . &P m D g i v . . . v Qn which is representable as a rule
of inference. As special cases we can have m = 0 or n = 0 as in the four types
of trace formulas. We therefore have

 Proposition 6.1.6: All classical quantifier-free axioms can be represented by
formulas in regular normal form.

Thus, to every classical quantifier-free theory, there is a corresponding sequent
calculus with structural rules admissible.

(c) Conversion of axiom systems into systems with rules: Conversion of a
Hilbert-style axiomatic system into a Gentzen-style sequent system proceeds,
130                       STRUCTURAL PROOF THEORY

after quantifier-elimination, by first finding the regular decomposition of each
axiom and then converting each conjunct into a corresponding rule following
Principle 6.1.1. Right contraction is unproblematic because of the arbitrary con-
text A in the succedents of the rule scheme. In order to handle left contrac-
tion, we have to augment this scheme. So assume that we have a derivation of
A, A, F =>• A, and assume that the last rule is nonlogical. Then the derivation
of A, A, F =>• A can be of three different forms. First, neither occurrence of A
is principal in the rule; second, one is principal; third, both are principal. The
first case is handled by a straightforward induction, and the second case by the
method, familiar from the work of Kleene and exemplified by the LD rule of
G3ip, of repeating the principal formulas of the conclusion in the premisses.
Thus the general rule-scheme becomes

             Q u P i , • • •, Pm, r = » A    ...     Qn, P l 9 • • . , P m , r = > A ^



Here P\,..., Pm in the conclusion are principal in the rule, and P\,..., Pm and
<2i,..., Qn in the premisses are active in the rule. Repetitions in the premisses
will make left contractions commute with rules following the scheme. For the
remaining case, with both occurrences of formula A principal in the last rule,
consider the situation with a Hilbert-style axiomatization. We have some axiom,
say ~(<z < b & b < a) in the theory of strict linear order, and substitution of
b with a produces ~(<z < a & a < a) that we routinely abbreviate to ~a < a,
irreflexivity of strict linear order. This is in fact a contraction. For systems with
rules, the case in which a substitution produces two identical formulas that are
both principal in a nonlogical rule, is taken care of by the

Closure condition 6.1.7: Given a system with nonlogical rules, if it has a rule
where a substitution instance in the atoms produces a rule of the form

 QuPl,...,       Pm-2, P, P, r => A         ...     Qn,PU...,     Pm-2, P, P, F =» A^
                                                                                               eg
                             Pi,...,pw_2,p,p,r=> A

then it also has to contain the rule

      QU PU • • • , Pm-2, P, F => A           ...     Qn,PU...,     Pm-2, P, V => A
                                                                                         Res
                            Pi,...,pm_2,p,r=>A
The condition is unproblematic, since the number of rules to be added to a given
system of nonlogical rules is bounded. Often the closure condition is superfluous;
For example, the rule expressing irreflexivity in the constructive theory of strict
linear order is derivable from the other rules, as will be shown in Section 6.6.
                       STRUCTURAL PROOF ANALYSIS                                    131


6.2.   ADMISSIBILITY OF STRUCTURAL RULES

In this section we shall prove the admissibility of the structural rules of weakening,
contraction, and cut for extensions of logical systems with nonlogical rules of
inference. We shall deal in detail with constructive systems and just note that the
proofs go through for classical systems with inessential modifications.
    We shall denote by G3im* any extension of the system G3im with rules
following our general rule-scheme and satisfying the closure condition. Starting
from the proof of admissibility of structural rules for G3im in Section 5.1, we
then prove admissibility of the structural rules for G3im*.

Theorem 6.2.1: The rules of weakening

                                   -LW                 rRW


are admissible and height-preserving in G3im*.

Proof: For left weakening, since the axioms and all the rules have an arbitrary
context in the antecedent, adding the weakening formula to the antecedent of
each sequent will give a derivation of A, F =>• A. For right weakening, adding
the weakening formula to the succedents of all sequents that are not followed by
an instance of rules RD or Ri will give a derivation of F =^ A, A. QED.

   The proof of admissibility of the contraction rules and the cut rule for G3im
requires the use of inversion lemmas. We observe that all the inversion lemmas of
Section 5.1, holding for G3im, hold for G3im* as well. This is achieved by having
only atomic formulas as principal in nonlogical rules, a property guaranteed by
the restriction given in Principle 6.1.1.

Theorem 6.2.2: The rules of contraction
                       A, A , F => A           F =» A , A, A
                        A , F ^ A LC            F ^ A , A RC

are admissible and height-preserving in G3im*.

Proof: For left contraction, the proof is by induction on the height of the derivation
of the premiss. If it is an axiom or conclusion of L_L, the conclusion also is.
   If A is not principal in the last rule (either logical or nonlogical), apply inductive
hypothesis to the premisses and then apply the rule.
   If A is principal and the last rule is logical, for L& and Lv apply height-
preserving invertibility, inductive hypothesis, and then the rule. For LD apply
inductive hypothesis to the left premiss, invertibility and inductive hypothesis to
the right premiss, and then apply the rule. If the last rule is LV, apply the inductive
132                         STRUCTURAL PROOF THEORY

hypothesis to its premiss, and Li. If the last rule is L3, apply height-preserving
invertibility of L3, the inductive hypothesis, and L3.
   If the last rule is nonlogical, A is an atomic formula P and there are two cases.
In the first case, one occurrence of A belongs to the context, another is principal
in the rule, say, A = Pm(= P). The derivation ends with




and we obtain
  2 i , i , , V i , , ,                     g w , f i , , m i , , ,
                                    Ind
   QUPu• • • , p m - u P , r => A       ... Qn,pu...,pm_up,r        =»                   ApInd
                            Pi,...,pw_1,p,r/=^A                                            "
In the second case both occurrences of A are principal in the rule, say, A —
Pm_1 = Pm = P ; thus the derivation ends with
  <2i,Pi,...,pm-2,p,p,r^A                           ...       al,p1,...,pw_2,p,p,r'=»Aw


a n d w e obtain

                                                              eB,p1,...,pM-2,p,p,r/=»A
                                              I      n    d
   6 1 , P i , . . . , p m - 2 , P , r =• A   Ind
                                                 ...           Q p Qn,pp t,...,p
                                                                             p m_r2,p,' A Jnd

with the last rule given by Closure Condition 6.1.7.
   The proof of admissibility of right contraction in G3im* does not present
any additional difficulty with respect to the proof of admissibility in G3im since
in nonlogical rules the succedent in both the premisses and the conclusion is
an arbitrary multiset A. So in the case in which the last rule in a derivation of
F =^ A, A, A is a nonlogical rule, we simply proceed by applying the inductive
hypothesis to the premisses and then applying the rule. QED.

Theorem 6.2.3: The cut rule

                                                                    -Cut
                                        r, r=> A, A'
is admissible in G3im*.

Proof: The proof is by induction on the length of A with subinduction on the sum
of the heights of the derivations of F =>- A, A and A, F r =^ A'. We consider here
in detail only the cases arising from the addition of nonlogical rules. The other
cases are treated in the corresponding proof for the intuitionistic multisuccedent
calculus G3im, Theorem 5.3.6.
                       STRUCTURAL PROOF ANALYSIS                                   133

1. If the left premiss is a nonlogical axiom (zero-premiss nonlogical rule), then
also the conclusion is, since nonlogical axioms have an arbitrary succedent.
2. If the right premiss is a nonlogical axiom with A not principal in it, the con-
clusion is a nonlogical axiom for the same reason as in case L
3. If the right premiss is a nonlogical axiom with A principal in it, A is atomic
and we consider the left premiss. The case that it is a nonlogical axiom is covered
by case 7. If it is a logical axiom with A not principal, the conclusion is a logical
axiom; else F contains the atom A and the conclusion follows from the right
premiss by weakening. In the remaining cases we consider the last rule in the
derivation of F =>> A, A. Since A is atomic, A is not principal in the rule. Let
us consider the case of a nonlogical rule (the others being dealt with similarly,
except RD and RV, which are covered in case 4). We transform the derivation,
where P m stands for Pi,..., P m ,


                                                           €g
                       P m ,F"=> A, A                           A,T'=»A'
                                                                            Cut
                                       Pm,F',F"^A,A'

into

6 i , P m , r " = > A, A A , T ' = » A'        Qn,Pm,r" => A, A A,F r => A;
                    /                   Cm
       Qu P w , F , F" =» A, A'            ...     Qn, P m , V, F" ^ A, A'R
                                                                              eg
                               pw,r',r"=> A,A'
where the cut has been replaced by n cuts with left premiss with derivation of
lower height.
   Let us now consider the cases in which neither premiss is an axiom.
4. A is not principal in the left premiss. These are dealt with as above, with cut
permuted upward to the premisses of the last rule used in the derivation of the left
premiss (with suitable variable renaming in order to match the variable restrictions
in the cases of quantifier rules), except for RD and RW. By the intuitionistic
restriction in this rule, A does not appear in the premiss, and the conclusion is
obtained without cut by RD or RV and weakening.
5. A is principal in the left premiss only. Then A has to be a compound formula.
Therefore, if the last rule of the right premiss is a nonlogical rule, A cannot be
principal in the rule, because only atomic formulas are principal in nonlogical
rules. In this case cut is permuted to the premisses of the right premiss. If the right
rule is a logical one with A not principal in it, the usual reductions are applied.
6. A is principal in both premisses. This case can involve only logical rules and
is dealt with as in the usual proof for pure logic. QED.
134                    STRUCTURAL PROOF THEORY

The conversions used in the proof of admissibility of cut show why it is neces-
sary to formulate the nonlogical rules so that they have an arbitrary context in
the succedent, both in the premisses and in the conclusion. Besides, as already
observed, active and principal formulas have to be atomic and appear in the
antecedent.

Theorem 6.2.4: The rules of weakening, contraction, and cut are admissible in
G3c*.

Proof: The proof is an extension of the results for the purely logical calcu-
lus in Sections 3.2 and 4.2. The new cases are analogous to the intuitionistic
case. QED.


6.3. FOUR APPROACHES TO EXTENSION BY AXIOMS

We found in Section 1.4 that the addition of axioms A into sequent calculus in
the form of sequents =$> A, by which derivations can start, will lead to failure of
cut elimination. Another way of adding axioms, used by Gentzen (1938, sec. 1.4)
already, is to add "mathematical basic sequents" which are (substitution instances
of) sequents

                           P l , . . . , P w = > Ql   Gn.
Here Pt, Qj are atomic formulas (typically containing free parameters) or _L.
By Gentzen's "Hauptsatz," the use of the cut rule can be pushed into such basic
sequents. A third way of adding axioms, first found in Gentzen's consistency proof
of elementary arithmetic (1934-35, sec. IV.3), is to treat axioms as a context F
and to relativize all theorems into F, thus proving results of the form F ^ C . Now
the sequent calculus derivations have no nonlogical premisses and cut elimination
applies. A fourth way of adding axioms is the one of this chapter.
   We shall specify formally the four different ways of extending logical sequent
systems by axioms and then establish their equivalence. Below, let T) be a finite
set of regular formulas. We define sequent systems of four kinds:

Definition 6.3.1:

(a) An A-system for V is a sequent system with axioms G3ipm+LW+RW+LC+
RC+Cut+AD, where AT) is the set of sequents =>> D obtained from elements D
in T). In derivations of a sequent F =^ A in an A-system, sequents from AT) may
appear as premisses. Derivability is denoted by \~AV F =>• A.
(b) A B -systemfor V is a sequent system with basic sequents, G3ipm+LW+RW+
LC+RC+Cut+Z?P, where BV is the set of regular sequents 1-3 of Definition
6.1.2 that correspond to elements ofT). In derivations of a sequent F =>> A in a
                      STRUCTURAL PROOF ANALYSIS                                             135

B -system, sequents from BV may appear as premisses. Derivability is denoted
by \-BV F =>• A.

(c) A C-system for V is a sequent system with a context. In derivations                     of a
sequent F =>• A in a C-system, instances of formulas in CV are permitted in
the antecedent. Derivability is denoted by \-Cv F =>• A. (We can also write it
as derivability in G3ipm, that is, as hG3 F, 0 =>• A, where 0 is the multiset of
instances of formulas in V used in the derivation.)
(d) An /^-system for V is a sequent system with rules, G3ipm+/?X>, where RV
is the set of rules of inference given by the regular decomposition of the formulas
in V. In derivations of a sequent F ==> A in an R-system, rules from RV are
permitted. Derivability is denoted by \-RV F =>• A.

Theorem 6.3.2: \-AV F =>> A iff \-BV F => A *J h ^ T ^ A #f h ^ F =>• A.

Proof: Axioms and basic sequents are interderivable by cuts, so A- and B-
systems are equivalent. We show equivalence of /^-systems with A-systems and
C-systems. If a regular formula has to be considered, we take it to be the split
formula P D Q v R, as other formulas convertible to rules are special cases or
inessential generalizations of it.

7. Equivalence ofR- and A-systems: The rule

                           g , P => A    R, P =$> A
                                                     Split
                                    P => A

can be derived in the A-system with axiom ==> P D Q V Z? by means of cuts and
contractions:

            p :>Q v R, p ==» P       ,P=> Q VR                Q, P =>• A ^ ,               • A

                   P :    v R, p =a   v R
                                                      T ->

                                                                       G vi?, p =» A
                                                                                       r
=> p    ev R                       p      v R ,P,P^          >A
                                                                  r
                       ^, P ^ //


In the other direction, ^ P D Qw Ris provable in the /^-system with Split.

                                                                  RV
                    Q,P   =^ Qv    R       R,P   =» 2 V R




2. Equivalence of C- and R-systems: Assume that F =>> A was derived in the
7^-system with Split, and show that F =>• A can be derived in the C-system with
136                        STRUCTURAL PROOF THEORY

P D Qv R. We assume that Split is the last rule in the derivation and therefore
r = P, n . By induction, \-Cv Q, P, F' =» A a n d h C p R, P, T => A; thus there
are instances A\,..., Am and A\,..., A!n of the schemes in CV such that
    h G 3 e , P, F', A i , . . . , Am => A     and     h G 3 R, P, r',A'l9...,A'n=>           A
Structural rules can be used, and we have, in G3ipm, a derivation starting with
weakening of the At and A'- into a common context A'[,..., A^ of instances
from CV:


                                        <2, P, V, A'[, ...,A'l=>A       R,P, V, A'(,..., A£ =* A
p D Q V R , P , r f , Af[,...,A£ =» P                  e v/?,p,r,A; ; ,..., A ^ A               LV

                             P D Qv R,P, V, A'{,..., A£ => A
Since the split formula and the A " , . . . , A^ are in C P , we have shown
hCv r =^ A.
   In the other direction, assume \-Cv r =>• A. Suppose for simplicity that only
one axiom occurs in the context, i.e., that h G 3 PD Qv R,F^A.     We have the
derivation in G3ipm+^D+Cut:

                                                      Rv
        Q,P ^      QV R    R,P => QV R
                     P^QVR
                    =>PDQvR                                  P D QV R,F => A
                                                                                        Cut
                                                  r =^ A
By admissibility of cut in G3ipm*, the conclusion follows. QED.

Derivations in A- and 5-systems can have premisses, and therefore cut must be
assumed, whereas C- and /^-systems are cut-free. The strength of /^-systems is
that they permit proofs by induction on rules used in a derivation. This leads
to some surprisingly simple, purely syntactic proofs of properties of elementary
axiom systems.


6.4. PROPERTIES OF CUT-FREE DERIVATIONS

The properties of sequent systems representing axiomatic systems are based on
the subformula property for systems with nonlogical rules:

Theorem 6.4.1: If V ^ A is derivable in G3im* or G3c*, then all formulas in
the derivation are either subformulas of the endsequent or atomic formulas.

Proof: Only nonlogical rules can make formulas disappear in a derivation, and
all such formulas are atomic. QED.
                      STRUCTURAL PROOF ANALYSIS                                  137

The subformula property is weaker than that for purely logical systems, but suffi-
cient for structural proof analysis. Some general consequences are obtained: Con-
sider a theory having as axioms a finite set V of regular formulas. Define V to be
inconsistent if =>• J_ is derivable in the corresponding extension and consistent
if it is not inconsistent. For a theory V, inconsistency surfaces with the axioms
through regular decomposition, with no consideration of the logical rules:

Theorem 6.4.2: Let V be inconsistent. Then

   (i) All rules in the derivation of =>• _L are nonlogical.
   (ii) All sequents in the derivation have _L as succedent.
   (iii) Each branch in the derivation begins with a nonlogical rule of the form



   (iv) The last step in the derivation is a rule of form

                            <gl=»-L      ...    gw=>±


Proof: (i) By Theorem 6.4.1, no logical constants except _L can occur in the
derivation, (ii) If the conclusion of a nonlogical rule has A as succedent, the
premisses of the rule also have. Since the endsequent is => _L, (ii) follows,
(iii) By (ii) and by _L not being atomic, no derivation begins with P, F => P.
Since only atoms can disappear from antecedents in a nonlogical rule, no deriva-
tion begins with _L, F =>• _L. This leaves only zero-premiss nonlogical rules,
(iv) By observing that the endsequent has an empty antecedent. QED.

It follows that if an axiom system is inconsistent, its formula traces contain
negations and atoms or disjunctions. Therefore, if there are neither atoms nor dis-
junctions, the axiom system is consistent, and similarly if there are no negations.
    By our method, the logical structure in axioms as they are usually expressed is
converted into combinatorial properties of derivation trees and completely sep-
arated from steps of logical inference. This is especially clear in the classical
quantifier-free case, in which theorems to be proved can be converted into a finite
number of regular sequents F =>• A. By the subformula property, derivations of
these sequents use only the nonlogical rules and axioms of the corresponding se-
quent calculus, with the succedent remaining the same throughout all derivations.
It becomes possible to use proof theory for syntactic proofs of mutual indepen-
dence of axiom systems, as follows. Let the axiom to be proved independent be
expressed by the logic-free sequent F =>• A. When the rule corresponding to the
axiom is left out of the system of nonlogical rules, underivability of F =>• A is
usually very easily seen. Examples will be given in the last section of this chapter.
138                    STRUCTURAL PROOF THEORY

6.5.   PREDICATE LOGIC WITH EQUALITY

Axiomatic presentations of predicate logic with equality assume a primitive re-
lation a = b with the axiom of reflexivity, a = a, and the replacement scheme,
a = b&A(a/x) D A (b/x). In sequent calculus, the standard way of treating equal-
ity is to add regular sequents with which derivations can start (as in Troelstra
and Schwichtenberg 1996, p. 98). These sequents are of the form =>> a = a and
a = b, P{a/x) => P(b/x), with P atomic, and Gentzen's "extended Hauptsatz"
says that cuts can be reduced to cuts on these equality axioms. For example,
symmetry of equality is derived by letting P be x = a. Then the second ax-
iom gives a = b,a = a =>• b = a, and a cut with the first axiom => a = a gives
a = b =$> b = a. But there is no cut-free derivation of symmetry. Note also that, in
this approach, the rules of weakening and contraction must be assumed, and only
then can cuts be reduced to cuts on axioms. (Weakening could be made admissible
by letting arbitrary contexts appear on both sides of the regular sequents, but not
contraction.)
    By our method, cuts on equality axioms are avoided. We first restrict the re-
placement scheme to atomic predicates P, Q, R,..., and then convert the axioms
into rules:

            a=a,V => A              P(b/x), a = b, P(a/x), T => A
               r => A Ref              a = b,P(a/x),r=>A          ^

There is a separate replacement rule for each predicate P, and a = b, P(a/x)
are repeated in the premiss to obtain admissibility of contraction. By the restric-
tion to atomic predicates, both forms of rules follow the rule-scheme. A case
of duplication is produced in the conclusion of the replacement rule in case P
is x = b. The replacement rule concludes a = b,a = b,T =>• A from the premiss
b = b,a = b,a = b,r^A.            We note that the rule in which both duplications are
contracted is an instance of the reflexivity rule so that the closure condition is
satisfied. Intuitionistic and classical predicate logic with equality is obtained by
adding to G3im and G3c, respectively, rules Ref and Repl.

Theorem 6.5.1: The rules of weakening, contraction, and cut are admissible in
predicate logic with equality.

Next we have to show the replacement rule admissible for arbitrary predicates.

Lemma 6.5.2: The replacement axiom a = b, A(a/x) =>> A(b/x) is derivable for
arbitrary A.

Proof: The proof is by induction on length of A. If A = _L, the sequent follows
by L_L, and if A is an atom, it follows from the replacement rule. If A = BSLC
                     STRUCTURAL PROOF ANALYSIS                                  139

or A = B v C, we apply inductive hypothesis to B and C and then left and right
rules. If A — B D C, we have the derivation
         b = a, B(b/x) => B(a/x)
                                    -w,w
  b = a,a = b,a = a, B(b/x) =>> B(a/x)
     a = b,a = a, B(b/x) =>- B(a/x)
                                  M
         a = b, B(b/x) =^ B(a/x)         _      a = b, C(a/x) =* C(b/x)
a = b, B(a/x) D C(a/x), B(b/x) => B(a/x)    a = b, C(a/x), B(b/x) => C(b/x)
                                                                          L
                 a = b, B(a/x) D C(a/x), B(b/x) =» C(b/x)
                                                               -RD
                 a = b, B(a/x) D C(a/x) =• B(b/x) D C(b/x)
If A = WyB, the sequent a = b,VyB(a/x)^VyB(b/x)                      is derived from
a = b, B(a/x) =>• B(b/x) by applying first LV and then 7?V. Finally, the se-
quent a = b, 3yB(a/x) =>• 3yB(b/x) is derived by applying first /^3 and then
L3. QED.

Theorem 6.5.3: T/z^ replacement rule
                       A(b/x), a = b, A(a/x), V =» A
                                                        Repl


w admissible for arbitrary predicates A.

Proof: By Lemma 6.5.2, a = b, A(a/x) =>• A(b/x) is derivable. A cut with the
premiss of the replacement rule and contractions lead to a = b, A(a/x), T =>• A.
Therefore, by admissibility of contraction and cut in the calculus of predicate
logic with equality, admissibility of the replacement rule follows. QED.

    Our cut- and contraction-free calculus is equivalent to the usual calculi: the
sequents =>> a = a and a = b, P(a/x) => P(b/x) follow at once from the reflex-
ivity rule and the replacement rule. In the other direction, the two rules are easily
derived from ^ a = a and a = b, P(a/x) => P(b/x) by cut and contraction. The
formulation of equality axioms as rules has the advantage of permitting proofs
by induction on height of derivation. The conservativity of predicate logic with
equality over predicate logic illustrates such proofs. In a cut-free derivation of a
sequent F =>• A that contains no equalities, the last nonlogical rule must be Ref.
To prove the conservativity, we show that instances of this rule can be eliminated
from the derivation. Above we noticed that the rule of replacement has an instance
with a duplication, but that the closure condition is satisfied since the instance in
which both duplications are contracted is an instance of reflexivity. For the proof
of conservativity, the closure condition will be satisfied by the addition of the
contracted instance of Repl as a rule Repl*:
140                    STRUCTURAL PROOF THEORY

Lemma 6.5.4: If T =>• A has no equalities and is derivable in G3c+Ref+Repl+
Repl*, no sequents in its derivation have equalities in the succedent.

Proof: Assume that there is an equality in a succedent. Only a logical rule can
move it, but then it is a subformula of the endsequent. QED.

Lemma 6.5.5: If V =>• A has no equalities and is derivable in G3c+Ref+Repl+
Repl*, it is derivable in G3c+Repl+Repl*.

Proof: It is enough to show that a topmost instance of Ref can be eliminated
from a given derivation. The proof is by induction on the height of derivation of
a topmost instance:

                                a=a,V     => A'
                                                Ref
                                    r=»A'
If the premiss is an axiom the conclusion also is, since by Lemma 6.5.4 the
succedent A' contains no equality, and the same if it is a conclusion of L_L. If the
premiss has been concluded by a one-premiss logical rule R, we have


                                a = a,F =^ A' R
                                    r > A ' Ref
and this is transformed into
                                a=aS"     => A"
                                                -Ref

                                    T' =» A'
There is by the inductive hypothesis a derivation of Y" =>• A" without rule Ref.
If a two-premiss logical rule has been applied, the case is similar.
    If the premiss has been concluded by Repl, there are two cases, according
to whether a = a is or is not principal. In the latter case the derivation is, with
n = p(b/x), r",
                   P(c/x), a=a,b = c, P(b/x), T" =» A'
                                                        -Repl
                       a=a,b = c, P(b/x), T" => Af
                                                   -Ref
                           b = c, P(b/x), T" =• A'
By permuting the two rules, the inductive hypothesis can be applied. If a = a is
principal, the derivation is, with Tf = P(a/x), V",
                      P(a/x), a = a, P(a/x), T" =• A'
                                                    Repl
                          a=a, P(a/x), T" =^ A'
                               P(a/x), T" =d> Af -Ref
By height-preserving contraction, there is a derivation of a = a, P(a/x), F" => Af
                       STRUCTURAL PROOF ANALYSIS                                  141

so that the premiss of Ref is obtained by a derivation with lower height. The
inductive hypothesis applies, giving a derivation of r" =>• A' without rule Ref
   Last, if the premiss of Ref has been concluded by Repl*, with a = a not principal,
the derivation is
                          c = c, a = a, b = c, V =>> A'
                             a=a,b = c, r ' = > A'


The rules are permuted and the inductive hypothesis applied. If a = a is principal,
the derivation is
                             a =a,a   =a, Tf =>• A '




and we apply height-preserving contraction and the inductive hypothesis. QED.
Theorem 6.5.6: IfV^A          is derivable in G3c+Ref+Repl+Repl* and if T, A
contain no equality, then T =>• A is derivable in G3c.
Proof: By Lemma 6.5.5, there is a derivation without rule Ref Since the end-
sequent has no equality, Repl and Repl * cannot have been used in this deriva-
tion. QED.
Note that if cuts on atoms had not been eliminated, the proof would not go through.
Also, if the closure condition were satisfied by considering the contracted rule to
be an instance of Ref elimination of contraction could introduce new instances
of Ref above the Ref"to be eliminated in Lemma 6.5.5.


6.6.   APPLICATION TO AXIOMATIC SYSTEMS

All classical systems permitting quantifier-elimination, and most intuitionistic
ones, can be converted into systems of cut-free nonlogical rules of inference. In
the previous section, we gave the first application, predicate logic with equality.
In Section 5.4, we showed how to turn the logical axiom of excluded middle for
atomic formulas into a sequent calculus rule. Also the calculus G3ip-\-Gem-at
can be seen as an intuitionistic calculus to which a rule corresponding to the
decidability of atomic formulas has been added, and, from this point of view, it is
more natural to consider the law of excluded middle as a nonlogical rather than
a logical axiom.
    We shall first give, as a general result for theories with purely universal axioms,
a version of Herbrand's theorem. Then specific examples from elementary intu-
itionistic axiomatics are given: Theories of equality, apartness, and order, as well
as algebraic theories with operations, such as lattices and Heyting algebras, are
142                     STRUCTURAL PROOF THEORY

representable as cut-free intuitionistic systems. On the other hand, the intuition-
istic theory of negative equality does not admit of a good structural proof theory
under the present approach: This theory has a primitive relation a # b, and the
two axioms ~a / a and ~ a / c & ~ i / c D ~a ^ b expressing reflexivity and
transitivity of negative equality.
    As a further application of the methods of this chapter, we give a structural
proof theory of classical plane affine geometry, with a proof of the independence of
Euclid's fifth postulate obtained by proof-theoretical means. Another application
of the fact that logical rules can be dispensed with is proof search. We can start
root-first from a logic-free sequent F =>• A to be derived: The succedent will be
the same throughout in derivations with nonlogical rules, and in typical cases very
few nonlogical rules match the sequent to be derived.

(a) Herbrand's theorem for universal theories: Let T be a theory with a finite
number of purely universal axioms and classical logic. We turn the theory T into
a system of nonlogical rules by first removing the quantifiers from each axiom,
then converting the remaining part into nonlogical rules. The resulting system
will be denoted by G3cT.

Theorem 6.6.1: Herbrand's theorem. If the sequent ^Wx3yi. • - 3 ^ A, with A
quantifier-free, is derivable in G3cT, then there are terms ti} with i ^ n, j ^ k
such that

                              \f     A(th/yu...,tik/yk)

is derivable in G3cT.

Proof: Suppose, to narrow things down, that k = 1. Then the derivation of
=>• Wx3yA ends with

                           => A{z/x,h/y), 3yA(z/x)
                                                          /?3

                                                • /?V
                                       Wx3yA
If the derivation continues, root-first, with a propositional inference, the next pre-
miss i s l ^ =>• Ai, 3yA(z/x), where Pi, AiConsistofsubformulasof A(z/x, t\/y).
(For the sake of simplicity, only a one-premiss rule is considered.) Otherwise R3
was applied, and the premiss is

                     =• A(z/x, tx/y), A(z/x, t2/y), 3yA(z/x)
The derivation can continue up from the second alternative in the same way,
producing possible derivations in which R3 is applied and instances of the formula
                      STRUCTURAL PROOF ANALYSIS                                  143

3yA{z/x) multiplied, but since the derivation cannot grow indefinitely, at some
stage a conclusion must come from an inference that is not R3.
   Every sequent in the derivation is of the form

              r => A, A(z/x, tm/y),...,     A(z/x, tm+l/y), 3yA(z/x)
where F, A consist of subformulas of A(z/x, tt/y)9 with / < m. In particular, the
formula 3 y A(z/x) can occur in only the succedent. Consider the topsequents of the
derivation. If they are axioms or conclusions of L_L, they remain so after deletion
of the formula 3 y A(z/x). If they are conclusions of zero-premiss nonlogical rules,
they remain so after the deletion since the right context in these rules is arbitrary.
After deletion, every topsequent in the derivation is of the form

                    r =^ A, A(z/x, tm/y),...,     A(z/x, tm+l/y)
Making the propositional and nonlogical inferences as before, but without the
formula 3yA(z/x) in the succedent, produces a derivation of

      =• A(z/x, h/y),...,     A(z/x, tm^/y), A(z/x, tm/,..., A(z/x, tn/y)
and repeated application of rule R v now leads to the conclusion. QED.

In the end of Section 4.3(a) we anticipated a simple form of Herbrand's theo-
rem for classical predicate logic as a result that corresponds to the existence pro-
perty of intuitionistic predicate logic: Dropping the universal theory from
Theorem 6.6.1, we have no nonlogical rules to consider and we obtain

Corollary 6.6.2: If =>• 3xA is derivable in G3c, there are terms t\,..., tn such
that =$> A(t\/x) V . . . V A(tn/x) is derivable.

(b) Theories of equality and apartness: The axioms of an apartness relation
were introduced in Section 2.1. We shall turn first the equality axioms and then
the apartness axioms into systems of cut-free rules.

   1. The theory of equality has one basic relation a = b that obeys the following
axioms:
   EQ1.     a=a,
   EQ2. a = b&a = cD b = c.
Symmetry of equality follows by substitution of a for c in EQ2. Note that
the formulation is slightly different from the transitivity of equality as given
in Section 2.1, where we had a = c&b = cDa = b. The change is dictated by
the form of the replacement axiom of Section 6.5: Now transitivity is directly an
instance of the replacement axiom, with A equal to x = c.
144                       STRUCTURAL PROOF THEORY

   Addition of the rules
                a = a,T => A              b = c, a = b, a = c, F =
                                  Rf


where a = b,a = c are repeated in the premiss of rule Trans, gives a calcu-
lus G3im+Ref-\-Trans the rules of which follow the rule-scheme. As noted in
Section 6.5, a duplication in Trans is produced if b is identical to c, but the cor-
responding contracted rule is an instance of rule Ref. The closure condition is
satisfied and the structural rules admissible.
  2. The theory of decidable equality is given by the above axioms EQ1 and
EQ2 and

   DEQ.       a = bv ~a = b.

The corresponding rule is an instance of a multisuccedent version of the scheme
Gem-at\
                          a = b,T => A ~a = b, T => A
                                                               D


Admissibility of structural rules for this rule is proved similarly to the single
succedent version in Section 5.4. For the language of equality, we have
G3im+Gem-at = G3im+Deq, a cut-free calculus. Proof of admissibility of
structural rules is modular for the rules Ref, Trans, and Deq, and it follows that
the intuitionistic theory of decidable equality, which is the same as the classical
theory of equality, is cut-free.
   3. The theory of apartness has the basic relation a / b (a and b are apart,
a and b are distinct), with the axioms

   API.   ~a ^a,
   AP2.   a / ibD a             V b
The rules are
                                a ^ c, a ^ b, F = ^ A   b ^ c, a ^ b, F =^ A
                         href   —-—       —                —       —           Split
      a ^a,     i => A                         a ^b,V   => A
The first, premissless rule represents ^a / a by licensing any inference from
a ^ a; the second has repetition of a / b in the premisses. Both rules follow the
rule-scheme; the closure condition does not arise because there is only one prin-
cipal formula, and therefore structural rules are admissible in G3im+Irref+Split.
   4. Decidability of apartness is expressed by the axiom

   DAP.       a^bv        ~a^b,
                      STRUCTURAL PROOF ANALYSIS                                 145

and the corresponding rule is

                      a*b,   T^ A       ~a^b,    F =^ A
                                                         Dap
                                    T^A
As before, it follows that the calculus G3im+Irref-\-Split+Dap is cut-free.
   5. The intuitionistic theory of negative equality is obtained from the axioms
of apartness, with the second axiom replaced by its constructively weaker con-
traposition:
   NEQ1.       ~a*a,
   NEQ2.     ~a ? c & ~b # c D         ~a^b.
It is not possible to extend G3im into a cut-free theory of negative equality by
the present methods. If a classical calculus such as G3c or G3i+Gem-at is used,
a cut-free system is obtained since NEQ2 becomes equivalent to AP2.
   The elementary theories in 1-4 can also be given in a single succedent formula-
tion based on extension of the calculus G3i, as in Negri (1999). As a consequence
of the admissibility of structural rules in such extensions, we have the following
result for the theory of apartness:

Corollary 6.6.3: Disjunction property for the theory of apartness. If
=>• A V B is derivable in the single succedent calculus for the theory of apartness,
either => A or => B is derivable.

Proof: Consider the last rule in the derivation. The rules for apartness cannot
conclude a sequent with an empty antecedent, and therefore the last rule must be
rule/?vofG3i. QED.

Let us compare the result to the treatment of axiom systems as a context, the
third of the approaches described in Section 6.3. Each derivation uses a finite
number of instances of the universal closures of the two axioms of apartness,
say, P. The assumption becomes that F =>• A v B is derivable in G3i. When-
ever F contains an instance of the "split" axiom, it has a formula with a dis-
junction in the consequent of an implication. Therefore F does not consist of
Harrop formulas only (Definition 2.5.3), so that Corollary 6.6.3 gives a proper
extension of the disjunction property under hypotheses that are Harrop formulas,
Theorem 2.5.4.

(c) Theories of order: We first consider a constructive version of linear order
and, next, partial order. The latter is then extended in 6.6(d) by the addition of
lattice operations and their axioms.
146                      STRUCTURAL PROOF THEORY

   1. Constructive linear order: We have a set with a strict order relation with
the two axioms:
   LO1.    ~(a< b&b< a),
   LO2.    a < bD a< c V c < b.
Contraposition of the second axiom expresses transitivity of weak linear order.
Two rules, denoted by Asym and Split, are uniquely determined from the ax-
ioms. Both rules follow the rule scheme, and the first one has an instance with a
duplication, produced when a and b are identical:
                                                         -Asym
                              a < a, a < a, F =$> A

The contracted sequent a < a, F =>• A is derived by
                                          Asym                            Asym
              a < a, a < a,T     =>> A           a < a, a < a,F =>• A
                                             ^      x—!               s lit
                                                                       P
                                      a < a, r =>• A
We observe that the contracted rule is only admissible, rather than being a rule of
the system. This makes no difference unless height-preserving admissibility of
contraction is required. It is not needed for admissibility of cut.
   2. Partial order: We have a set with an order relation satisfying the two
axioms
   POL       a^a,
   PO2.    a^b&b^cD             a^c.

Equality is defined by a = b = a^b Scb^a.li follows that equality is an equiv-
alence relation. Further, since equality is defined in terms of partial order, the
principle of substitution of equals for the latter is provable. The axioms of partial
order determine by the rule-scheme two rules, the one corresponding to transi-
tivity producing a duplication in case a = b and b = c. The rule in which both the
premiss and conclusion are contracted is an instance of the rule corresponding
to reflexivity, and therefore the structural rules are admissible. The rules corre-
sponding to the two axioms are denoted by Refund Trans:
               a^a,F     => A                          a^c,a^b,b^c,r=>A
                                Ref               —                      Trans
                   T » A                          b b            T ^ A
Derivations of a regular sequent F =^> A in the theory of partial order begin with
logical axioms, followed by applications of the above rules. As is seen from the
rules, these derivations have the following peculiar form: They are all linear and
each step consists in the deletion of one atom from the antecedent. If classical
logic is used, by invertibility of all its rules, every derivation consists of derivations
of regular sequents followed by application of logical rules only.
                      STRUCTURAL PROOF ANALYSIS                                 147

   3. Nondegenerate partial order: We add to the axioms of partial order two
constant 0, 1 satisfying the axiom of nondegeneracy ~ 1 < 0. The corresponding
rule has zero premisses:
                                             - Nondeg
                                u o, r =
Partial order is conservative over nondegenerate partial order:

Theorem 6.6.4: IfF^Ais          derivable in the classical theory of nondegenerate
partial order and F, A are quantifier-free and do not contain 0, 1, then F =>• A
is derivable in the theory of partial order.

Proof: We can assume F =>• A to be a regular sequent. We prove that if a derivation
of F =>> A contains atoms with 0 or 1 the atoms are instances of reflexivity, of
the form 0 ^ 0 or 1 ^ 1. So suppose the derivation contains an atom with 0 or 1
and not of the above form. Its downmost occurrence can only disappear by an
application of rule Trans




where a < c contains 0 or 1 and is not an instance of reflexivity. If a = 0, i.e., a
is syntactically equal to 0, then a ^ b in the conclusion must be an instance of
reflexivity and we have b = 0, therefore also c = 0. But then a < c is an instance
of reflexivity contrary to assumption. The same conclusion follows if a = 1 or
c = 0 or c = 1.
   By the above, the derivation does not contain instances of 1 < 0 and therefore
no instances of rule Nondeg. QED.

   If intuitionistic logic is used, the result follows whenever F =>• A is a regular
sequent.

(d) Lattice theory: We add to partial order the two lattice constructions and their
axioms:

Lattice operations and axioms:

   a/\b the meet of a and b,             avb the join of a and b,
   a/\b < a (Mtl),                       a < avb (Jnl),
   a/\b ^ b (Mtr),                       b ^ avb (Jnr),
   c^a Scc^b D c^ a^b (Unirnt),          a^c Scb^c D avb < c (Unijn).

All of the axioms follow the rule-scheme, and we shall use the above identifiers
148                       STRUCTURAL PROOF THEORY

as names of the nonlogical rules of lattice theory:
      a/\b ^ a, F => A                                    a < avb, F =$> A
                          M                                                        Jf
          r =» A           "                                   r => A              "
          < ft, F => A                   ft                 < avb,   F =>• A
                          Mtr                                  —                   Jnr
           r =^c^a,c^b,
      c ^ flA^,  A              F=^A                      avft ^r c,=»a A
                                                                        ^ c, b ^ c, F =>> A
                      ——                      Unimt                     :          —          Unijn
          c^a,c^b,        F =^ A                               a^c, b^c, F = ^ A
The uniqueness rules for the meet and join constructions can have instances with
a duplication in the premiss and conclusion:

                           c < a/\a,     c < a, c ^ a , F       =$- A
                                                  zz                    Unimt
                                                      T        A

and similarly for join. The rule in which c < a is contracted in both the premiss
and conclusion can be added to the system to meet the closure condition. If
height-preserving contraction is not required, the contracted rule can be proved
admissible: Using admissibility of left weakening, admissibility of the rule ob-
tained from Unimt is proved as follows, starting with the contracted premiss
                     A:
                                              , c ^ a, F =>• A
                                                            LW
                         c ^ dAd,      c ^ a , a ^
                                              a/\a, V =>• A
                                               —            Trans
                             c ^ a , a ^ ciAd, F =>• A
                                                               LW,LW
                      c ^ a, a < ^Afl, a ^ a , a ^ a , F =^ A
                                                   —           Unimt
                            c^a,a^a,a^a,T                     => A
                                                                        Re Re
                                                 ^ 44                       f> f
                                       c<:a,r         =>• A
All structural rules are admissible in the proof-theoretical formulation of lattice
theory. The underivability of =>> _L follows, by Theorem 6.4.2, from the fact that
no axiom of lattice theory is a negation,
   As a consequence of having an equality relation defined through partial order,
substitution of equals in the meet and join operations,

                     b = c D a/\b = a/\c                   b = c D avb = avc

need not be postulated but can instead be derived. For example, we have a/\b ^ a
by Mtl and a/\b ^ c by Mtl, b < c and Trans, so #AZ? < a/\c follows by Unimt.
   Lattice theory is conservative over partial order:

Theorem 6.6.5: If F =>> A is derivable in classical lattice theory and F, A are
quantifier-free and do not contain lattice operations, then F =>> A is derivable in
the theory of partial order.
                       STRUCTURAL PROOF ANALYSIS                                  149

Proof: We can assume that F =>• A is a regular sequent. The topsequent is a
logical axiom of the form a < c, F r =>• A', a < c where A', a < c = A and a, c
contain no lattice operations. We can also assume that the first step removes a ^ c
from the antecedent; if not, the steps and removed atoms before a ^ c can be
deleted.
   If the first rule is Ref, then a = c and a ^ c , F = ^ A i s a logical axiom from
which the conclusion follows by Ref. Else the first rule must be Trans with the
step

                          a^ c, a^ b, b^ c, r" =>• A
                                                       Trans
                                  Z &      Fr     A

The atoms a ^ b, b ^ c are activated in an instance of rule Trans by the removed
atom a < c. They form a chain of two atoms a < b, Z? < c in the topsequent. We
may assume a ^ Z? or Z? < c to be the removed atom in the next step, for otherwise
the step and its removed atom can be deleted. If a ^ b is removed by Trans,
two atoms a^d,d^b          are activated by a < b and similarly if b < c is removed
by Trans. Among the atoms activated so far there is a chain of three atoms
a^d,d^b,b^c         each of which is in the topsequent. Starting with a ^ c, we form
the transitive closure of atoms activated in instances of Trans. Each such instance
will substitute one atom in the chain by two, until we come to the last instance
of Trans with the chain a ^ bo, b0 ^ b\,..., bn < c in the topsequent. If an atom is
not in the chain and is removed by a rule other than Trans, the atom and rule are
deleted. Thus, we only have to show that atoms in the chain with lattice operations
can be removed, and let bk ^ bk+\ be the first such atom. (If there are none, there
is nothing to prove.) If it is removed by Ref we have bk = bk+i and consider the
pair of atoms bk-i^bk,bk^       bk+2, and so on, until both atoms must be removed by
lattice rules. Similarly, let b\ with / > k be the first of the bt that does not contain
lattice operations. (If there are none, consider the last term c in the chain.)
    We claim that in the chain a^bo,bo^bi,...        ,bn^c there is a contiguous pair
of atoms that are removed by rules Unimt, Mt or Jn, Unijn: Start with bk-\ < bk.
If the outermost lattice operation of bk is A, the atom bk-\ < bk has to be removed
by Unimt, for bk_\ does not contain lattice operations. Then bk < bk+\ must be
removed by Jn, Unimt or Mt. In the last case we are done, else we continue
along the chain, analyzing bk+\ ^ bk+2- If the first case had occurred, bk+\ ^ bk+2
is removed by Unijn, Jn, or Unimt; if the second, it is removed by Jn, Unimt, or
Mt. In the last case we have the conclusion. In the other cases, we continue the
case analysis until we have that &/_2 ^ fc/_i is removed by Jn or Unimt. But then
bi^i^biis removed by Unijn or Mt, respectively, since b\ does not contain lattice
operations.
150                     STRUCTURAL PROOF THEORY

   We prove the result in a similar fashion if the outermost lattice operation of
bk is v.
   Let two contiguous atoms b ^ d/\e and d/\e < d be removed by Unimt, Mt. For
Unimt to be applicable, the topsequent has to contain the atoms b ^ d and b ^ e.
Then replace the two atoms b ^ d/\e and d/\e ^ d with the single atom b ^ d, and
continue the derivation as before except for deleting the instances of Trans where
the two atoms were active and the two steps Unimt, Mt. In this way the number
of atoms containing lattice operations is decreased. If there are two contiguous
atoms that are removed by Jn, Unijn, let them be b ^ bvd, bvd ^ e. Then replace
them with the atom b^e that is found in the topsequent and delete the steps where
the two atoms were active. Again, this proof transformation decreases the number
of atoms containing lattice operations. QED.

If F => A is a regular sequent, the result applies also in the intuitionistic theory.
(e) Affine geometry: We have two sets of basic objects, points denoted by
a,b,c,...  and lines denoted by /, m, n,    In order to eliminate all logical struc-
ture from the nonlogical rules, we use a somewhat unusual set of basic concepts,
written as follows:
  a # b,      a and b are distinct points,
  I ^ m,      I and m are distinct lines,
  / ft m,     I and m are convergent lines,
  A(a, I),    point a is outside line /.
The usual concepts of equal points, equal lines, parallel lines, and incidence of a
point with a line, are obtained as negations from the above. These are written as
a = b, I =m,l\\m, and I(a, /), respectively. The axioms, with names added, are
as follows:
I. Axioms for apartness relations:
   ^a ^ a    (Irref),   a^bDa^cVb^c                 (Split),
   ~Z / /    (Irref),   I ^ rn D I ^nV m ^n         (Split),
   ~l I I    (Irref),   I #m D / #n Vm #n            (Split).

These three basic relations are apartness relations, and their negations are equiv-
alence relations.
   Next we have three constructions, two of which have conditions: the con-
necting line ln(a, b) that can be formed if a ^ b has been proved, the inter-
section point pt(l, m) where similarly / ft m is required to be proved, and the
parallel line par (I, a) that can be applied without any conditions uniformly in
/ and a.
   Constructed objects obey incidence and parallelism properties expressed by
the next group of axioms:
                      STRUCTURAL PROOF ANALYSIS                                 151

II. Axioms of incidence and parallelism:
   a ± b D I(a, ln(a, b)) (Inc), a^bD      I(b, ln(a, b)) (Inc),
   I If m D I(pt(l, m), /) (Inc), I jf m D I(pt(l, m), m) (Inc),
   I(a,par(l,a))      (Inc),
   l\\par(l,a)     (Par).

Uniqueness of connecting lines, intersection points, and parallel lines is guaran-
teed by the following axioms:

III. Uniqueness axioms:
   a^bScl   ^ ra D A(a, I) V A(b, I) V A(a, m) V A(b, m)         (Uni),
   I ^m D A(a, I) V A(a, m)v I ftm (Unipar).

The contrapositions of these two principles express usual uniqueness properties.
  Last, we have the substitution axioms:

IV. Substitution axioms:
   A(a,l)D a^bv      A(b, I) (Subst),
   A(a, 1) D I # m V A(a, m) (Subst),
   I im^l    ^nvm^n        (Subst),

Again, the contrapositions of these three axioms give the usual substitution prin-
ciples.
    The above axiom system is equivalent to standard systems, such as Artin's
(1957) axioms. These state the existence and uniqueness of connecting lines and
parallel lines, and existence and properties of intersection points are obtained
through a defined notion of parallels. As is typical in such an informal discourse,
the principles corresponding to our groups I and IV are left implicit. There is
a further axiom stating the existence of at least three noncollinear points, but
as explained in von Plato (1995), we do not use such existential axioms, say
(3JC : Pt)(3y : Pt)x # y and (VJC : Ln)(3y : Pt)A(y,x). We achieve the same
effect by systematically considering only geometric situations containing the
assumptions a : Pt, b : Pt, a ^ b,c : Pt, A(c, ln(a, b)).
    An axiom such as a # b D I (a, ln(a, b)) hides a structure going beyond first-
order logic. Contrary to appearance, it does not consist of two independent for-
mulas a ^ b and I (a, ln(a, b)) and a connective, for the latter is a well-formed
formula only if a / b has been proved. (For a detailed explanation of this structure,
dependent typing, see Section 3 of Appendix B.) As an example of conditions
for well-formed formulas, from our axioms a "triangle axiom"

                          A(c,ln(a,b)) D A(b,ln(c,a))

can be derived, but the conditions a / b and c / a are required for this to be
152                     STRUCTURAL PROOF THEORY

well-formed. Here we can actually prove more, the lemma
                           a ? b & A ( c , l n ( a , b ) ) D c^a
Assume for this a ^ b and A(c, ln(a, b)). By the first substitution axiom,
A(c, ln(a, b)) gives c ^ a V A(a, ln(a, b)). By incidence axioms, I(a, ln(a, b)),
so that c ^ a follows. By the second substitution axiom, A(c, ln(a, b)) gives
ln(a,b) / ln(c,a)vA(c,ln(c,a)),        so that ln(a, b) # ln(c, a) follows. By
the uniqueness axiom, a ± b and ln(a, b) ^ ln(c, a)) give A(a, ln(a, b)) V
A(b, ln(a, b)) V A(a, ln(c, a)) V A(b, ln(c, a)), so the incidence axioms lead to
the conclusion A(b, ln(c, a)).
    Examples of conditions can be found in mathematics whenever first-order logic
is insufficient. A familiar case is field theory, where results involving inverses
x~l, y~l, ... can be expressed only after the conditions x ^ 0, y / 0 , . . . have
been established.
    In a more formal treatment of conditions, they can be made into progressive
contexts in the sense of type theory (see Martin-Lof 1984 and von Plato 1995).
Such contexts can be arbitrarily complex, even if the formulas in them should all be
atomic. For example, the formula ln(pt(l, m), a) / /presupposes that pt(l, m) ^ a
which in turn presupposes that / jf m.
    The reason for having basic concepts different from the traditional ones is not
only that the "apartness" style concepts suit a constructive axiomatization; there
is a reason for the choice of these concepts in classical theories also, namely, if the
conditions a # b and /# m were defined as a = b D ± and /1| m D _L, the natural
logic-free expression of the incidence axioms would be lost.
    All of the axioms of plane affine geometry can be converted into nonlogical
rules, moreover, closure condition 6.1.7 will not lead to any new rules. We con-
clude that the structural rules are admissible in the rule system for plane affine
geometry.
    We first derive a form of Euclid's fifth postulate from the geometrical rules:
Given a point a outside a line /, no point is incident with both / and the parallel
to / through point a. Axiomatically, we may express this by the formula
                       A(aJ)D ~(I(bJ)&I(b,par(l,a)))
The sequent
                         A(a,l)^A(b,l),A(b,par(l,a))
is classically equivalent to the previous one and expresses the same principle
as a logic-free multisuccedent sequent. To derive this sequent, we note that, by
admissibility of structural rules, all rules in its derivation are nonlogical, and
therefore the succedent is always the same, A(b, I), A(b,par(l, a)). Further, no
conditions will appear. With these prescriptions, root-first proof search is very
                      STRUCTURAL PROOF ANALYSIS                                         153

nearly deterministic. Inspecting the sequent to be derived, we find that the last
step has to be a substitution rule in which the second premiss is immediately
derived. In order to fit the derivations in, the principal formulas are not repeated
in the premisses, and the second formula in the succedent is abbreviated by
A = A(b,par(l,a)):
                                                                        Inc
          I *par(l, a) =• A(b, /), A A(a,parQ, a)) => A(b, /), A
                                                                 Subst
                            A(a,l)=>A(b,l),A

The first premiss can be derived by the uniqueness of parallels, and now the rest
is obvious:
                                                                              -Par
    A(b, 1) => A(b, I), A     A^    A(b, /), A    I ftparQ, a) =» A(b, /), A
                                                                               Unipar
                                                  )A
We shall show that when the rule of uniqueness of parallels is left out, the sequent

                         A(a, 1) => A(b, I), A(b,parQ, a))

is not derivable by the rules of affine geometry. We know already that if there is
such a derivation, it must end with one of the two first substitution rules. If it is
the first rule, we have

                  a^b=> A(b, /), A        A(b, 1) =» A(b, I), A
                                                                Subst
                              A(a, I) => A(b, /), A

Then the first premiss must be derivable. It is not an axiom, and unless a — b,
it does not follow by Irref. Split only repeats the problem, leading to an infinite
regress. This leaves only the second substitution rule, and we have

                 / ± m =» A(b, 1), A     A(a, m) => A(b, I), A
                                                                  Sbt


As in the first case, rules for apartness relations will not lead to the first premiss.
Otherwise it could be derived only by uniqueness of parallels, but that is not
available. By theorem 6.3.2, derivability in the system of rules is equivalent to
derivability with axioms, and we conclude the

Theorem 6.6.6: The uniqueness axiom for parallel lines is independent of the
other axioms of plane affine geometry.

   In case of theorems with quantifiers, assuming classical logic, a theorem to
be proved is first converted into prenex form, then the propositional matrix into
the variant of conjunctive normal form used above. Each conjunct corresponds
to a regular sequent, without logical structure, and the overall structure of the
154                    STRUCTURAL PROOF THEORY

derivation is as follows: First the regular sequents are derived by nonlogical rules
only, then the conjuncts by L&, Rv, and RD. Now R& collects all these into
the propositional matrix, and right quantifier rules lead into the theorem. The
nonlogical rules typically contain function constants resulting from quantifier
elimination. In the constructive case, these methods apply to formulas in the
prenex fragment that admits a propositional part in regular normal form.
   An example may illustrate the above structure of derivations: Consider the
formula expressing that, for any two points, if they are distinct, there is a line on
which the points are incident:

                       WxWy(x ^yD        3z(I(x,     z)&I(y,   z)))

In prenex normal form, with the propositional matrix in the implicational variant
of conjunctive normal form, this is equivalent to

              VxVy3z((x * y&A(x, z) D ±)&(x / y&A(y, z) D _L))
In a quantifier-free approach, we have instead the connecting line construction,
with incidence properties expressed by rules in a quantifier-free form:
                                      - Inc             ———-—         ————   — Inc
       a^b,    A(a, ln(a, b)), V => A         a*b,     A(b, ln(a, b)\ T => A

We have the following derivation:

        x ± y, A(x, ln(x, y)) =» _L n°    x ± y, A(y, ln(x, y)) =» _L          nc

                                   -L&                         •      L&
       x ^ y &A(x, ln(x, y)) =$> _L         x ^ y &A(y, ln(x, y)) =>• _L
      =>• x # y &A(x, ln(x, y)) D _L     => x / y &A(y, ln(x, y)) D ±
        =^(x ^y &A(x, ln(x, y)) D J_) &(JC # y &A(y, ln(x, y)) D ± ) ^&
                                                                               nq

           =» 3z((x # y &A(x, z) D ±) &(x # y &A(y, z) D JQ)
        => V;cVy3z((x ^ y &A(JC, z) 3 ± ) &(JC ^ y &A(y, z) D X ) ) ^ ' ^
Derivations with nonlogical rules and all but two of the logical rules of multi-
succedent sequent calculi, RD and RW, do not show whether a system is classical
or constructive. The difference appears only if classical logic is needed in the
conversion of axioms into rules.


NOTES TO CHAPTER 6

Most of the materials of this chapter come from Negri (1999) and Negri and von
Plato (1998). The former work contains a single succedent approach to extension of
contraction- and cut-free calculi with nonlogical rules. These calculi are used for a
proof-theoretical analysis of derivations in theories of apartness and order, leading
to conservativity results which have not been treated here. The latter work uses a
multisuccedent approach. The examples in subsections (b) and (c) of Section 6.6 are
                       STRUCTURAL PROOF ANALYSIS                                   155

treated in detail in Negri (1999). The proof-theoretic treatment of constructive linear
order in subsection (c) is extended in Negri (1999a) to a theory of constructive ordered
fields. The geometrical example in subsection (e) comes from von Plato (1998b).
    Our proof of Theorem 6.6.1 was suggested by the proof in Buss (1998, sec. 2.5.1).
    In Section 6.4, we mentioned some previous attempts at extending cut elimination
to axiomatic systems. The work of Uesu (1984) contains the correct way of presenting
atomic axioms as rules of inference. As to the use of conjunctive normal form in
sequent calculus, we owe it to Ketonen's thesis of 1944, in which the invertible
sequent calculus for classical propositional logic was discovered.
                                          7

                      Intermediate Logical Systems




Intermediate logical systems, or "intermediate logics" as they are often called, are
systems between intuitionistic and classical logic in deductive strength. Axiomatic
versions of intermediate logical systems are obtained by the addition of different,
classically valid axioms to intuitionistic logic. A drawback of this approach is
that the proof-theoretic properties of axiomatic systems are weak.
   In this chapter, we shall study intermediate logical systems by various methods:
One is to translate well-known natural deduction rules into sequent calculus.
Another is to add axioms in the style of the rule of excluded middle of Chapter 5
and the nonlogical rules of Chapter 6. We have seen that failure of the strict
subformula property is no obstacle to structural proof analysis: It is sufficient to
have some limit to the weight of formulas that can disappear in a derivation. A
third approach to intermediate logical systems is to relax the right implication
rule of multisuccedent intuitionistic sequent calculus by permitting formulas of
certain types to appear in the succedent of its premiss, in addition to the single
formula of the intuitionistic rule.
   From a result of Godel (1932) it follows that there is an infinity of nonequivalent
intermediate logical systems. Some of these arise from natural axioms, such as
the law of double negation, the weak law of excluded middle, etc.
   There are approaches to intermediate logical systems, in which some prop-
erty such as validity of an interpolation theorem or some property of algebraic
models is assumed. The general open problem behind these researches concerns
the structure of the implicational lattice of intuitionistic logic (in the first place,
propositional logic). This is the problem of generating inductively all the classes
of equivalent formulas between _L and 1 D 1 , ordered by implication. For for-
mulas in one atom (and _L, of course), this structure, the free Heyting alge-
bra with one generator, is known, but above that only special cases have been
mastered.
   Our aim here is to present a few natural classes of intermediate logical systems
and to study their proof-theoretical properties by elementary means. We shall


156
                    INTERMEDIATE LOGICAL SYSTEMS                                                     157

study, in particular, the following logical systems:

   1. Logic with the weak law of excluded middle        ~Av~~A.
   2. Stable logic, characterized by the law of double-negation ~ ~ ADA.
   3. Dummett logic, characterized by the law (AD B)v (BD A).

We shall consider only the propositional parts of intermediate logical systems in
what follows.


7 . 1 . A SEQUENT CALCULUS FOR THE WEAK LAW OF EXCLUDED MIDDLE

We study the weak law of excluded middle by adding a rule to a single succedent
calculus, analogous to the rule of excluded middle of Section 5.4.
   We add to G3ip a rule of weak excluded middle for atomic formulas P:

                                                                          Wem-at


The weak law of excluded middle for atoms follows. In the other direction, that
law in the form of an axiomatic sequent =>• ~ P v ~ ~ P, together with a cut on
~ P v ~ ~ P, leads to the rule of weak excluded middle.
   In a proof-theoretical analysis of G3ip-\-Wem-at, we first have to establish
inversion lemmas and, with their help, the admissibility of structural rules. Finally,
we have to investigate the admissibility of the rule for arbitrary formulas. Since
this method is by now familiar, we indicate only the main results.
   We prove inversion lemmas by noting that application of the rule commutes
with the inversions of the invertible rules of G3ip. Proofs of admissibility of
weakening, contraction, and cut go through similarly to the corresponding proofs
for the rule of excluded middle in Section 5.4. This is so because the rule has
no principal formula: If an application of the rule is followed by weakening or
contraction, we simply permute the order of application of the rules. With cut,
we show the conversion for the case that the left premiss is derived by the rule,
                                            D T1
                 P , T—1
                     1
                           .    A
                           •? l \   ^*"^*> £* ^ Y
                                                    V
                                                    f
                                                        A
                                                        f\
                                                             Wem-at
                                                                              !
                                                                                        Cut


This is transformed into the derivation with lower cut-height,

                                           - Cut                      _   _       _    —       Cut
                 p, r, r =» c                                ~~ p, r, r =• c
                                                                                      Wem at
                                         r r c                                             -
and similarly if the right premiss has been derived by Wem-at.
158                    STRUCTURAL PROOF THEORY

   Admissibility of the rule

                                                             -Wem


for arbitrary formulas A is proved by induction on weight of A. If A = _L, the
rule is derivable using the left premiss only:


                                           ± , r =>• cCut
                                          c
If A = P, we have the rule Wem-at. For the rest, it is easily shown that if the weak
law of excluded middle holds for A and B, it holds for ASLB, A V B, and AD B
as well.
   A logical system with the weak law of excluded middle Wem-at is well-behaved
proof-theoretically. The subformula property needs to be adjusted into: All formu-
las in derivations are subformulas of the endsequent or of negations of negations
of atoms.


7.2. A SEQUENT CALCULUS FOR STABLE LOGIC
We shall investigate the single succedent sequent calculus corresponding to the
system of natural deduction with a principle of indirect proof for atomic formulas.
Translation of this principle into sequent calculus gives the rule

                                                 Raa-at
                                   r =^ p
The calculus G3i^-\-Raa-at has the same strength as a calculus with the rule
corresponding to stability for atoms:

                                    r =^~~ p
                                      r => p
Rule Raa-at is admissible in G3ip+Gera-atf:

                                   ~ P , T =^ _L          _L =>• P
                         r1                                          CM?
                                             !              Gem at
                     —            p ^ p                         '

The other direction, from Raa-at to Gem-at, does not work:

Theorem 7.2.1: 77&e calculus G3ip+Raa-at w no^ complete for classical propo-
sitional logic.

Proof: Assume there is a (cut-free) derivation of =^ P v ~ P . The last rule
cannot be Raa-at; therefore it is P v , and =>• P or =>• ~ P is derivable. In the
                    INTERMEDIATE LOGICAL SYSTEMS                                   159

first case, =>• P was derived by Raa-at but this is impossible because the premiss
~ P =>• _L would then have to be derivable in G3ip. In the second case, => ~ P
was derived by RD, but this is again impossible since P =>• J_ is not derivable in
G3ip. QED.

The sequent ~ (P V ~ P) =>• _L is easily derived in G3ip. Application of the rule
of indirect proof to P v ~ P would give a derivation of =>• P v ~ P , and we
conclude that the rule of indirect proof for arbitrary formulas is not admissible in
G3ip+Raa-at. This is already obvious from the fact that A v B is not intuition-
istically derivable from ~ ~ ( A V B), ~ ~ A D A and ~ ~ BD B.

Theorem 7.2.2: The structural rules are admissible in G3ip+Raa-at.

Proof: Consider an instance of rule Raa-at in the derivation. Weakening and con-
traction can be permuted up since there is no principal formula in the antecedent
of the conclusion. For cut, if the right premiss has been derived by rule Raa-at, it
can be permuted with cut. If the left premiss has been derived by Raa-at, we have

                                       Raa-at      4      „
                                                p, A =^ c
                                                          cut
                                       ^ c
Consider the right premiss. If it is an axiom, either C is an atom in A and the
conclusion of cut also is an axiom, or C = P and the conclusion of cut follows
by weakening from the premiss T =>• P. If the right premiss has been concluded
by L_L, the conclusion of cut also follows by LJ_. If the right premiss has been
concluded by a logical rule, cut is permuted up to its premisses, for P is an atom
and cannot be principal in the right premiss. QED.

 Theorem 7.2.3: Rule Raa/or arbitrary formulas is admissible in G3ip+Raa-at
for the disjunction-free fragment of propositional logic.

Proof: By adapting the conversions for & and D in the proof of Theorem 5.4.6
to G3ip+Raa-at. QED.

   If to G3ip we add rule Raa for arbitrary formulas, a rule that corresponds
to Gentzen's original rules of natural deduction for classical propositional logic,
we obtain a complete calculus: Application of the rule to the intuitionistically
derivable premiss ~ ( P v ~ P ) =>• _L gives the conclusion => P v ~ P . There-
fore this calculus is also closed with respect to cut, even if it does not permit a cut
elimination procedure. To see the latter, consider the case that the left premiss of
cut has been derived by Raa:

                                        Raa

                                                          CM
160                    STRUCTURAL PROOF THEORY

If A is principal in the right premiss, cut does not permute up. Now, if A is atomic,
it is never principal in the left premiss, and we see why Prawitz had to restrict the
rule of indirect proof to atomic formulas.
    For the structure of derivations in G3ip-\-Raa, we obtain the following: Con-
sider the first application of rule Raa, with premiss ~ A, A => ± . We conclude
instead by RD the sequent A =>• ~ ~ A . Continuing in this way, the derivation
of F =>> C in G3ip+Raa is transformed into a derivation of F* =>• C* in G3ip,
where F* and C* are partial double-negation translations of F and C: Those
parts of F, C that are principal in instances of Raa in the derivation are substituted
by their double negations.
    The first one to suggest a translation from classical to intuitionistic logic was
Kolmogorov (1925) and related translations were found by Godel, Gentzen, and
Bernays in the early 1930s. In Kolmogorov's translation, each subformula of a
given formula A is substituted with its double negation, with the result that the
translated formula A* is intuitionistically derivable if and only if A is classi-
cally derivable. Moreover, A DC A* is classically derivable. The Godel-Gentzen
translations, in turn, make disjunction and existence disappear with a result on
translated formulas analogous to that of Kolmogorov.
    The translation we have defined is not only a coding of classically derivable
formulas into intuitionistically derivable ones, but is produced by the translation
of a classical derivation into an intuitionistic one. Further, as long as we only con-
sider propositional logic, the translation can be simplified: If =>• C is classically
derivable, then =>• ~ ~ C also is, and by Theorem 5.4.9, =>• ~ ~ C is derivable
in G3ip. Here the last rule must be RD, so we have the intuitionistic derivation




If instead of R D we apply rule Raa, we obtain the derivation

                                             -Raa
                                         C
The premiss is derivable in G3ip, so there is only one application of the classical
rule, namely, the last.
  Note that the laws of double-negation and weak excluded middle together are
equivalent to the classical law of excluded middle.


7.3.   SEQUENT CALCULI FOR DUMMETT LOGIC

The classically valid propositional law (A D B) v (B D A) first gained attention
in Dummett's study of logical systems with a linearly ordered set of "truth values."
This law is rather counterintuitive to most people: One instance is that Goldbach's
                    INTERMEDIATE LOGICAL SYSTEMS                                  161

conjecture implies Riemann's hypothesis or Riemann's hypothesis implies
Goldbach's conjecture, but hardly anyone thinks these have much to do with
each other. Any two propositions can be substituted for A and B, and Dummett's
law is valid, not because of derivability of one from the other, but by classical
two-valued semantics: If A is true, B D A is true irrespective of B, and so is
(A D B) V (B D A). If A is false, truth of (ADB)v(BD        A) equally follows. A
somewhat more intuitive formulation of Dummett's law is the equivalent dis-
junction property under hypotheses, (AD B v C)D(AD B)v (AD C).
   Underivability of the law (P D Q) v (Q D P) for atoms P, Q in intuitionistic
logic is easily shown. It is of interest to study the corresponding proof theory
of what is usually called Dummett logic. We look at two approaches to this in-
termediate logical system:

(a) A left rule for Dummett logic: We shall first add to G3ipm a left rule called
Dmt-at:

                                                           Dmt at
                                                              -

The corresponding rule for arbitrary A, B in place of P, Q will make the formula
(A D B) V (B D A) derivable. Inversion lemmas follow as for the rule Wem-at,
and so does admissibility of all the structural rules as there is no principal formula.
Since only atomic implications, i.e., implications in which both antecedent and
consequent are atoms, disappear in derivations, the rule supports a weak subfor-
mula principle: All formulas in a derivation are subformulas of the endsequent or
of atomic implications.
   Admissibility of the left Dummett law for arbitrary formulas can be posed
as the claim that the law for a formula follows intuitionistically from Dummett
law for its components. If one of A and B, say, B, is equal to _L, the Dummett
law (A D 1 ) V ( 1 DA) follows since _L D A is provable. If A is a conjunction or
disjunction, the proofs go through, but if A is an implication C D D, we obtain
((C D D)D B)v (BD(C D D)). Application of Dummett law to the components
brings six cases, two of which, CD B, DD B, DDC and BDC, DD B, DDC,
do not imply the Dummett law. Rule Dmt-at is not sufficient for obtaining
Dummett logic. A formulation as a left rule for arbitrary formulas A, B in place
of the atoms of rule Dmt-at does not give any subformula property, and there is
no satisfactory proof theory under this approach.

(b) Dummett logic through a right implication rule: We can obtain a sequent
calculus for Dummett logic by relaxing the constraint on the succedent of the
premiss of rule RD of G3ipm by permitting any number of implications in the
succedent of the premiss. Following Sonobe (1975), the right implication rule can
introduce simultaneously n implications A\ D B\,..., An D Bn in the succedent
162                    STRUCTURAL PROOF THEORY

of the conclusion. The right contexts A; of the premisses consist of all the impli-
cational formulas of A except At D Bt, and in the succedent of the conclusion A
can contain other formulas that are not implications:
                  Au r => Ai, Bi      ...    An, F =» Aw, Bn


The left implication rule of G3ipm has to be modified by allowing the succedent
A of the conclusion to appear as a context also in the succedent of its left premiss:

                                                          LD
                                 A    7T~^     A



The calculus thus obtained will be called G3LC. Admissibility of all the structural
rules for G3LC can now be proved by inductive means:
Lemma 7.3.1: The rules of left and right weakening are admissible in G3LC.
Proof: Admissibility of left weakening is routinely proved by induction on deriva-
tion height. For right weakening we use induction on formula length and height
of derivation. If A is nonimplicational, we just apply the inductive hypothesis
on the premisses of the last rule (lower derivation height) and then the rule. We
proceed similarly if A is implicational and the last step is not RD.
   If A is an implicational formula C D D and the last step is SR D we obtain from
the n premisses A{, F => A;, Bt the stronger conclusion F => A \ D B\, . . . , An D Bn.
Using admissibility of left weakening and the inductive hypothesis on the lighter
formulas C , D w e obtain


By applying the inductive hypothesis with a lower derivation height we ob-
tain from the n premisses also the derivability of At, F =>> At, Bt,C D D for
I ^ i ^ n. This, together with (1) gives by SRD the conclusion F ^ A . C D D .
QED.

We prove by induction on the length of A the
Lemma 7.3.2: All sequents of the form A =>• A are derivable in G3LC.
Thus, by admissibility of left and right weakening, we obtain
Corollary 7.3.3: All sequents of the form A, F =>• A, A are derivable in G3LC.
Lemma 7.3.4: The rule


                                     c,
is admissible in G3LC.
                    INTERMEDIATE LOGICAL SYSTEMS                                   163

Proof: By induction on derivation height. QED.

Lemma 7.3.5: The rule
                                  r =>      A,BDC
                                   £ , F => A , C

is admissible in G3LC.
Proof: By induction on derivation height. If B D C is not principal in the last
step, use the inductive hypothesis and apply the rule. If it is principal, one of the
premisses is B, F =>> A', C for some A' contained in A. The conclusion is then
obtained by admissibility of right weakening. QED.

Proposition 7.3.6: The rules of left and right contraction are admissible in
G3LC.

Proof: Admissibility for both rules is proved by induction on the length of A with
subinduction on derivation height. We shall consider only those cases in which
the proof differs from the proof already given for the system G3im.
   For left contraction, assume that A is principal and not atomic, the last rule in
the derivation being LD. Thus A = B DC, and the derivation ends with
               BDC,BDC,r    ^ A,B BDC,C,T                   => A
                                                                  LD
                        BDC, BDC, F=^ A
From the left premiss, we obtain by the inductive hypothesis a derivation of the
sequent B D C,T => A, B, and by Lemma 7.3.4 applied to the right premiss we
get a derivation of C, C, F =>• A, and hence, by length induction, a derivation of
C, r =>• A. The conclusion follows by applying LD.
   For right contraction assume that the last step of the derivation is RD, i.e., A
is B DC and the derivation ends with
 B, T => A',C,BDC     fi,T   => Af,C,BDC    {Bt,r   =>•      Ai,BDC,BDC,Ci,}ni=l
                                                                                   SRD
                              r => A,BDC,BDC

ByLemma7.3.5 applied to B, F =>• A ; , C, B D C,weobtain£, B, F =» A7, C, C
and thus, by induction on formula length and left contraction a derivation of
B, F =>> A', C Induction on height of derivation applied to all the n other pre-
misses gives {B(,r => A/, B D C, Q }"=1, and the conclusion follows by applying
5/?D to these n + \ premisses. QED.

Theorem 7.3.7: The rule of cut is admissible in G3LC.

Proof: The proof is by induction on length of the cut formula with subinduction
on the height of cut. The only new case with respect to the proof detailed for the
system G3im is when the cut formula A is an implication B DC that is principal
164                      STRUCTURAL PROOF THEORY

in both premisses. In this case the step
 fl,r=>A",C      {B(,r ^ Ai,Ci,BDC}^=l              5DC,r^A ; ,6         C, T => Af
                                             SRD                                   LD
               F^MDC                                    flDC,r'=>        A'
                                                                           Cut
                                      r,r'=»A,A'
is replaced by one cut of lower height and two cuts on shorter formulas:
 T ^ A,BDC           BDC,r'=>        A', B
                                    Cut
            r,r=> A,A',B                  B, r =» A", C
                                                        Cltf
                    r, r, r = » A, A', A", C                 C,T/=»A/
                                                                   Cut
                                r, r, r , r = » A, A', A7, A" #
                                r, r, r , r=> A, A', A', A W*
                                       —-—-—               —-—-—c*
                                              r,r'=* A, A'
where W* and C* denote possibly repeated applications of left and right weak-
ening and contraction. QED.

NOTES TO CHAPTER 7

For formulas in one atom and ±, the structure of the implicational lattice of in-
tuitionistic logic was determined by Rieger (1949) and Nishimura (1960). Further
partial results can be found reported in the book by Balbes and Dwinger, Distributive
Lattices, of 1974. It is somewhat odd for a logician to find studies of intuitionistic
logic repeated there in an algebraic disguise.
    We have studied only the propositional parts of intermediate logical systems in this
chapter. An intermediate system characterized through a law for quantified formulas
is the "logic of constant domains" (Gornemann 1971, van Dalen 1986).
    Dummett logic was first studied by Dummett (1959), whose idea was to have a
generalized linearly ordered set of truth values such as the unit interval [0, 1], instead
of the two classical values 0 and 1. Linearity is expressed as a condition on valuations:
For any valuation v and any two formulas A and B, either v(A) ^ v(B) or v(B) ^ v(A).
In the former case, v(A D B) = 1, so also v((A D B)v (B D A)) = 1, and similarly
in the latter case v((A D B)v (B D A)) = 1. Thus the Dummett law is validated in a
linearly ordered set of truth values. Sometimes the name of Godel is also mentioned
in this connection. The reason is that in the proof of the result of Godel (1932), the
impossibility of interpreting intuitionistic logic as a many-valued logical system with
a finite number of truth values, a denumerable sequence of formulas is constructed
which, as observed by Dummett, determines as a limit Dummett logic.
    The proof of admissibility of structural rules for the system G3LC presented here is
due to Roy Dyckhoff. A terminating propositional system for Dummett logic, G4LC,
based on the calculus G4ip is given in Dyckhoff (1999).
                                          8

                       Back to Natural Deduction




The derivability relation of single succedent sequent calculus, written F =>• C,
is closely related to the derivability relation of natural deduction, written F h C
in Chapter 1. Usually the latter is intended as: There exists a natural deduction
derivation tree finishing with C and with open assumptions contained in F. Thus
the derivability relation is not a formal but a metamathematical one. As a conse-
quence, weakening is "smuggled in": If C is derivable from F and if each formula
of F is contained in A, then C is derivable from A. If the metamathematical deriv-
ability relation is used, it will be difficult to state in terms of natural deduction
what weakening amounts to. We shall consider only a formal derivability relation
for natural deduction, in which F is precisely the multiset of open assumptions
in a natural deduction derivation.
   One consequence of the use of a formal derivability relation is that not all
sequent calculus derivations have a corresponding natural deduction derivation.
For example, if the last step is a left weakening, it will have no correspondence
in natural deduction and similarly if the last step is a contraction. However, such
steps are artificial additions to a derivation. Equivalence of derivability in natural
deduction and sequent calculus will obtain if no such "useless" weakenings or
contractions are present.
   We shall show in detail that weakening is, in terms of natural deduction, the
same as the vacuous discharge of assumptions and that contraction is the same
as multiple discharge. This explanation was already indicated in Section 1.3.
In the other direction, a logical inference in natural deduction that at the same
time discharges assumptions, vacuously or multiply, consists, in terms of sequent
calculus, of two steps that have been purposely made independent: There is the
logical step in which a formula is active, and there is a preceding weakening or
contraction step in which the formula was principal.
   The availability of weakening and contraction as independent steps of infer-
ence leads in sequent calculus to instances of the cut rule that do not have any
correspondence in natural deduction. We shall call such instances nonprincipal
cuts. Different ways of permuting up a nonprincipal cut can lead to different
                                                                                  165
166                    STRUCTURAL PROOF THEORY

cut-free derivations, where a corresponding natural deduction derivation permits
of just one conversion toward normal form.
    In Section 1.3, we found a way from natural deduction to sequent calculus.
It was essential that the elimination rules for conjunction and implication were
formulated as general elimination rules analogous to disjunction elimination. In
usual systems of natural deduction, only the special elimination rules for con-
junction and implication are available. We shall show that it is these rules and
the rule of universal elimination of predicate logic that are responsible for the
lack of structural correspondence between derivations in natural deduction and
in sequent calculus. With the general rules, the two ways of formalizing logical
inferences are seen to be variants of one and the same thing.
    Gentzen found the rules of natural deduction through an analysis of actual
mathematical proofs, and they have been accepted ever since as "the rules" of
natural deduction. How natural are the general elimination rules in comparison?
In an informal proof, we would use an assumption of form A & B by analyzing it
into A and B and by deriving consequences directly from them, without the two
intermediate logical steps of the usual conjunction elimination rules. Similarly,
we use A D B by decomposing it into A and B, then deriving consequences from
 B, and if at some stage A obtains, those consequences obtain. The same natural
use of logic is found when A V B is split into A and B in a proof by cases.
    A further reason for the general elimination rules is that they follow from a
uniform inversion principle, as in Section 1.2. Semantically, the change to general
elimination rules is neutral as the meaning explanations for the connectives and
quantifiers are given in terms of the introduction rules.


8.1. NATURAL DEDUCTION WITH GENERAL ELIMINATION RULES

In the formalist tradition originating with Hilbert, rules of inference operate on
formulas to produce new formulas as conclusions. In Section 1.2, it was empha-
sized that rules of inference informally act on assertions. On a formal level, they
act on derivations of the premisses to yield a derivation of the conclusion.
   Discharge of assumptions in natural deduction is indicated by the "little num-
bers" written next to the mnemonic sign for the rule of inference. The correspond-
ing discharged assumptions are put in brackets and the number written on top of
them. The way these little numbers are managed has the same importance as the
rules of weakening and contraction in sequent calculus.
   In natural deduction, the number of times an assumption has been made is
well determined, and we shall consider open assumptions in derivations to form
multisets with the same notational conventions as in the previous chapters on
sequent calculi. For each instance of a rule that can discharge assumptions, it
must be uniquely determined what assumptions are discharged, through a label
                       BACK TO NATURAL DEDUCTION                                 167

written next to the sign of the inference rule and on top of the discharged, bracketed
assumptions. We shall refer to these as discharge labels and assumption labels,
respectively, and use the numbers 1, 2, 3 , . . . as labels. Uniqueness of discharge
is achieved by the following

Principle 8.1.1: Unique discharge of assumptions. No two instances of rules
in a derivation can have a common discharge label.

We shall now give an inductive definition of the derivation of a formula A from
open assumptions F. Derivability in natural deduction will then be a relation
between a formula and a multiset. Whenever more than one derivation is assumed
given in the definition, it is also assumed that these derivations do not have
common discharge labels. Similarly, new labels must be chosen fresh.

Definition 8.1.2: A derivation from open assumptions in intuitionistic natural
deduction is defined by the following clauses:
1. A is a derivation of A from the open assumption A.
2. Given derivations
                                      r         A

                                      A         B
of A from open assumptions F and of B from open assumptions A,

                                      r     A

                                      AZ?

is a derivation of A&B from open assumptions F, A.
3. Given derivations

                                      r         A

                                      A         B
with assumptions and conclusions as indicated,
                                r                   A


                              Av B              Av B
are derivations of A V B from open assumptions F and from A, respectively.
168                     STRUCTURAL PROOF THEORY

4. Given a derivation

                                     Am,F

                                       B

as indicated, with m ^ 0,


                                 [Aml F


                                  AD B

is a derivation of A D B from open assumptions V.
5. Given a derivation

                                       r
                                     A(y/x)

of A(y/x)from open assumptions V, ify does not occur free in T, VxA,

                                      r
                                  Aiy/x)
                                     WxA - v/

is a derivation of VxAfrom open assumptions F.
6. Given a derivation




of A(tIx) from open assumptions Y,

                                      r
                                  A(t/x)
                                              3
                                   3xA        '

is a derivation of 3x A from open assumptions I\
                    BACK TO NATURAL DEDUCTION                    169

7. Given derivations
                                  T                Am,Bn,A

                                 A&B                C

as indicated, with m, n ^ 0,

                                 r      [Am], [Bnl A

                             ^B                     C&El2
                                       C
is a derivation of C from open assumptions F, A.
8. Given derivations



                         Av B              C                 C

as indicated, with m, n ^ 0 ,

                             T        [Am], A [Bnl 0




is a derivation of C from open assumptions F, A, 0.
9. Given derivations
                                 F             A        B\ 0

                             AD5               A         C

a.? indicated, with n ^ 0,

                                 r         A       [B"L©



w a derivation of C from open assumptions F, A, 0.
170                  STRUCTURAL PROOF THEORY

10. Given a derivation
                                        F

                                        i
of _L from open assumptions F,
                                    F




is a derivation of C from open assumptions F.
11. Given derivations
                              r             A(t/x)m,A

                            VxA                 C
ofVxAfrom open assumptions F and of C from open assumptions A(t/x)m, A,

                             r     [A(t)xn A

                            ViA             C
                                    c               '"•
is a derivation of C from open assumption F, A.
12. Given derivations
                              r         A(y/x)m, A

                            3xA                 C
of 3x A from open assumptions F a^J of C from open assumptions A(y/x)m, A,
           ot occur free in 3xA, C, A,

                             r     [A(y)'xri A


                                                    - • • •
                                    c

w a derivation of C from open assumption F, A.
In 7 and 8 the labels must be chosen distinct. Note that formulas indicated as
discharged from open assumptions can have other occurrences in the contexts.
                      BACK TO NATURAL DEDUCTION                                  171

The definition makes formal the observation in Section 1.2 that logical rules do not
act on formulas or even assertions, but on derivations. Derivability of a formula
A from open assumptions F naturally means that there is a derivation.
   In the definition, the formula with the connective or quantifier in the elimination
rules is the major premiss of the inference and the antecedent of implication in
DE, the minor premiss. The discharged formulas in elimination rules are often
referred to as "auxiliary" assumptions and the derivations in which they are made
as "auxiliary" derivations. Conjunction and disjunction eliminations have special
cases in which A = B.

Definition 8.1.3:
  (i) The height of a derivation is the greatest number of consecutive rules of
        inference in it.
  (ii) A discharge is vacuous if in Definition 8.1.2 m = 0 or n = 0.
  (iii) A discharge is multiple if in Definition 8.1.2 m > 1 or n > 1.

Theorem 8.1.4: Composition of derivations. If

                                    r         A, A



are derivations of A from F and of C from A, A, respectively, with disjoint dis-
charge labels and with no clashes of free variables, then



                                        A, A

                                          C

is a derivation of C from F, A.

Proof: The proof is by induction on the height of the given derivation of C from
A, A. If it is 0, then C = A and A is empty, so the second derivation is A. The
composition of derivations is the same as the first derivation. In the inductive case,
the proof is according to the last rule used in deriving C from A, F, and there are
12 cases. For each case, the inductive hypothesis is applied to the derivations of
the premisses of the last rule, and then the rule is applied. QED.

In practice, labels and variables are renamed if the conditions regarding them
are not met. The property of derivations stated by the theorem is often referred
to as closure under substitution. When derivations in natural deduction are
written in sequent calculus style, as in the examples of Section 1.2, composition
172                     STRUCTURAL PROOF THEORY

of derivations can be expressed by the rule of substitution:

                              F h A     A, A h C
                                                  - Subst
                                   r, A h-c
This rule resembles cut, but is different in nature: Closure under substitution just
states that substitution through the putting together of derivations produces a cor-
rect derivation. This is seen clearly from the proof of admissibility of substitution.
In natural deduction in sequent calculus style, there are no principal formulas in
the antecedent, and therefore the substitution formula in the right premiss also
appears in at least some premiss of the rule concluding the right premiss. Sub-
stitution is permuted up until the right premiss is an assumption. Elimination of
substitution is very different from the elimination of cut.
    By Theorem 8.1.4, the practice of pasting together derivations in natural deduc-
tion is justified. This is not perhaps clear a priori: Consider the reverse of cutting
a derivation into two pieces at any formula in it. The two parts will not usually
be formal derivations as defined in 8.1.2, because of the nonlocal character of
natural deduction derivations. The contexts F, A , . . . in the rules of natural de-
duction must be arbitrary for the compositionality of derivations to obtain. They
must also be independent: With shared contexts, as in the G3 sequent calculi,
Theorem 8.1.4 would fail.
    Substitution produces a non-normality whenever in A, A h C the formula A
is a major premiss of an elimination rule.
    The multiplicity of open assumptions grows in general exponentially in the
composition of derivations. This is exemplified by the composition of a derivation
of A from F and of C from A m , A, by the application of the composition of
Theorem 8.1.4 m times:



                                   A, ™.x. , A, A

                                          C

The composition gives a derivation of C from F m , A.


8.2.   TRANSLATION FROM SEQUENT CALCULUS TO NATURAL DEDUCTION

We shall give an inductive definition of a translation from cut-free derivations
in the sequent calculus GOi of Section 5.1 to natural deduction derivations with
general elimination rules. As mentioned, it is sometimes thought that natural
deduction would not be able to express the rule of weakening and therefore
derivability in natural deduction is defined as: C is derivable from F if there is
                        BACK TO NATURAL DEDUCTION                                      173

a derivation with open assumptions contained in P. We shall instead consider
the formal derivability relation of natural deduction, Definition 8.1.2, and only
translate sequent calculus derivations in which all formulas principal in weakening
or contraction are used in a logical rule:

Definition 8.2.1: A formula in a sequent calculus derivation is used if it is active
in an antecedent in a logical rule.

Rules that use a formula make it disappear from an antecedent. In natural de-
duction, this corresponds to the discharge of assumptions, and a count of the
assumption labels in the translated derivation will tell if there were weakenings
or contractions in the sequent calculus derivation.

(a) The translation: The translation from cut-free sequent calculus derivations
in GOi will be defined for derivations that contain no unused weakening or con-
traction formulas. The translation starts with the last step and works root-first
step by step until it reaches axioms or instances of L_L. The translation produces
labels whenever formulas are used. We also add square brackets and treat labeled
and bracketed formulas in the same way as other formulas when continuing the
translation. The natural deduction derivation comes out from the translation all
finished. To satisfy Principle 8.1.1, each rule that discharges assumptions must
have fresh discharge labels. Below, in each case of translation, we write the re-
sult of the first step of translation with a rule in natural deduction notation and
the premisses from which the translation continues in sequent calculus notation,
except that formulas in antecedents may appear with brackets and labels.
   In a derivation with no unused weakenings or contractions, the last rule is a
logical one, and we therefore begin with derivations that end with a logical rule:

Translation of logical rules:


            A, B, r =^ c               A&B     [A], [B], V =>C
            A&B, r =>• c L&      ~*                  '              &E,1.,2.


      r =^ A      A^ 5
        i         A&5

A,r=^ C        5, A ^ C                A V B [A], r = > C       [B], A=>C
                          Lv     ~>             ^^       —     —                 v£,l.,2.
   A vZ

       r => A                    =^A          r =^ B                   r => B
                  -.,                  v/i               Rv2   ~>               v/ 2
            AvB                 AvB          V^AvB                      Av B
174                     STRUCTURAL PROOF THEORY


         A    B,A^C                    AD B        V => A            [B], A => C
                                                       C

             A, r =k B                  [A], r =* B
                            RD



                ), r =^ c              VxA [A(^/x)], r =k c
                                                     c

                                                           V/
                                             WxA


         _A(y/x),
             _ _ r_ =*L C3       ^     3xA    [A(y/x)],
                                                  _     F^ C
                                                             3£iI.




             r 4 A(r/x) _            ^ r=                  3/



Translation of weakening:

                    r =^c                :
               n.
                                      r =» c
Translation of contraction:




Translation of axioms and L±:

                                                   - j i        ^^    —



By the assumption of no unused weakening or contraction formulas, the transla-
tion can reach only weakening or contraction formulas indicated as discharged
by square brackets. The topsequents of derivations are axioms or instances of
L_L. If the translation arrives at these sequents and they do not have labels, their
antecedents turn into open assumptions of the natural deduction derivation. When
a formula is used, the translation produces formulas with labels and we can reach
topsequents [A]=4> A and [_L]=^ C with a label in the antecedent. These are
translated into [A] and ^ J - £ , with discharged assumptions. Note that if a labeled
                     BACK TO NATURAL DEDUCTION                                 175

formula gets decomposed further up in the derivation, the labeled formula itself
becomes a major premiss of an elimination rule that has been assumed. The com-
ponents, instead, do not inherit that label but only those indicated in the above
translations. The translation produces derivations in which the major premisses
of elimination rules always are (open or discharged) assumptions:

Definition 8.2.2: A derivation in natural deduction is in full normal form if all
major premisses ofE-rules are assumptions.

We shall refer to such derivations briefly as normal. Note that _L in _L E is counted
as a major premiss of an £-rule.
   The translation from sequent calculus to natural deduction is an algorithm that
works its way up from the endsequent in a local way, reflecting the local character
of sequent calculus rules. It produces syntactically correct derivation trees with
discharges fully formalized. The variable restrictions in rules V/ and 3E follow
from those in rules RV andLB. The translation of derivations with cuts will be
treated in Section 8.4.

(b) The meaning of weakening and contraction: The translation of applica-
tions of the rule of weakening into natural deduction may seem somewhat sur-
prising, but it will lead to a useful insight about the nature of this rule. Natural
deduction rules permit the discharge of formulas that have not occurred in a
derivation. Similarly, natural deduction rules permit the discharge of any num-
ber of occurrences of an assumption, not just the occurrence indicated in the
schematic rule. Unfolding Definition 8.2.1, we have:

Observation 8.2.3: Rule D/ and the elimination rules produce a vacuous
(multiple) discharge whenever one of the following occurs:

   1. In DI concluding A D B, no occurrence (more than one occurrence) of
assumption A was discharged.
   2. In 8LE and vE with major premisses ASLB and Ay B, no occurrence of
A or B (more than one occurrence of A or B, or more than two if A = B) was
discharged.
   3. In DE with major premiss A D B, no (more than one) occurrence ofB was
discharged.
   4. In WE and 3E with major premiss VxA or 3xA, no (more than one) occur-
rence of A(t/x) or A(y/x) was discharged.

A weakening formula (respectively, contraction formula) is a formula A in-
troduced by weakening (contraction) in a derivation. There can be applications
of weakening and contraction that have no correspondence in natural deduction:
Whenever we have a derivation with a weakening or contraction formula A that
176                    STRUCTURAL PROOF THEORY

is not used, the endsequent is of the form A, F =>• C, where A is an inactive
weakening or contraction formula throughout.
   The condition of no inactive weakening or contraction formulas in a sequent
calculus derivation permits a correspondence with the formal derivability relation
of natural deduction:

Theorem 8.2.4: Given a derivation ofT^C        in GOi with no inactive weakening
or contraction formulas, there is a natural deduction derivation of C from open
assumptions F.

Proof: The proof is by induction on the height of the given derivation and uses
the translation from sequent calculus. If F =$> C is an axiom or instance of L_L,
F = C or F = _L and the translation gives the natural deduction derivations C
and ^±E with open assumptions C and J_, respectively. If the last rule is L&, we
have F = ASLB, F', and the translation gives


                        A&B
                                                    &EI2



Ifthere are no inactive weakenings or contractions in the derivation of A, B, F" =>•
C, there is by inductive hypothesis a natural deduction derivation of C from open
assumptions A, B, Ff. Now assume A&B and apply SLE to obtain a derivation
o f C f r o m A & £ , F'.
    If there is an inactive weakening or contraction formula in the derivation of
A, B, V =>> C, it is by assumption not in F", so it is A or B or both. Deleting
the weakenings and contractions with unused formulas, we obtain a derivation of
A m , Bn, F" =>• C, with m, n ^ 0 copies of A and B, respectively. By the induc-
tive hypothesis, there is a corresponding natural deduction derivation with open
assumptions A m , Bn, F'. Application of SLE now gives a derivation of C from
A&B, F r . All the other cases of logical rules are dealt with similarly.
    The last step cannot be weakening or contraction by the assumption about no
inactive weakening or contraction formulas. QED.

By the translation, the natural deduction derivation in Theorem 8.2.4 is normal.
Later we show the converse of the theorem. Equivalence of derivability between
sequent calculus and natural deduction applies only if unused weakenings and
contractions are absent. The usual accounts of translation from sequent calculus to
natural deduction pass silently over such problems, by use of a metamathematical
derivability relation for natural deduction instead of the formal one.

Theorem 8.2.5: Given a derivation ofF=>C in GOi with no inactive weaken-
ing or contraction formulas, if A is a weakening (contraction) formula in the
                     BACK TO NATURAL DEDUCTION                                        177

derivation, then A is vacuously (multiply) discharged in the translation to a nat-
ural deduction derivation.

Proof: Formula A can be used in left rules and ED only. In the translation to
natural deduction, A becomes a labeled formula in the antecedent. It disappears
when a weakening with A is reached and is multiplied when a contraction on A
is reached. QED.

If a derivation of F =$> C contains unused weakenings or contractions, we can
delete them to obtain a derivation of F* => C such that each formula in F* also
occurs in F. Then F* is a multiset reduct of F as defined in 5.2.1. Now the
translation to natural deduction can be applied to F* =>• C.
   Sometimes one sees systems of natural deduction with explicit weakening and
contraction rules. They have the same effect as a metamathematical derivability
relation, and we shall not use them.
   Perhaps the simplest example of a derivation with weakening is, with the
corresponding natural deduction obtained through translation at right,

                             -Wk                      1.
                  A,B   =>> A                  [A&B]                 [A]

                =• A&B D A                       A&B DA                    '

In the natural deduction derivation, B is vacuously discharged. The translation
produces the "ghost" label 3 to which no open assumption corresponds. An inter-
mediate stage of the translation just before the disappearance of the weakening
formula is



                          [A&B]        [A], [B]=> A
                                                           &£,2.,3.
                                             -D/,1.
                                   A&B D A
In Gentzen's original sequent calculus there were two left rules for conjunction:

                                                      , ^ C
                                     • L&,     . „    „     „                  L& 2
                    A&B, F =^ C               A&B, F
These left rules correspond to the usual elimination rules for conjunction, and the
derivation of A&B D A and its translation become
                                                                1.
                        A -K A                             [A&B]
                                   - L&i                              &Ei
                                                            A
                                      —                               -D/,1.
                        A&B D A                      A&B D A
178                    STRUCTURAL PROOF THEORY

Weakening is hidden in Gentzen's left conjunction rules and vacuous discharge
in the special conjunction elimination rules. It is not possible to state fully the
meaning of weakening in terms of natural deduction without using the general
elimination rules.
   The premiss of a contraction step in GOi can arise in three ways: First, the
duplication A, A comes from a rule with two premisses, each having one occur-
rence of A. Second, A is the principal formula of a left rule and a premiss had A
already in the antecedent. Third, weakening is applied to a premiss having A in
the antecedent. Only the first two have a correspondence in natural deduction.
   The simplest example of a multiple discharge should be the derivation of
A D A&A, given here both in GOi with a contraction and in a translation to
natural deduction with a double discharge:


                     A,A=>A&A                           [A] [A]
                                                         A&A "
                     4 A D A&A                         A D A&A

In Definition 8.2.3, the clause about more than two occurrences of the discharged
formula in 8LE and vis, in case of A = B, is exemplified by the derivation of
A v A D A in sequent calculus and its translation:

                    A A^A                          [AvA]  [A] [A]
                                                                  v£,2.,3.
                  AVA^A _                 .              A    . L
                   Aw AD A                            Aw AD A

Here there is no contraction even if two occurrences of A are discharged at vis.
   Often in the literature one sees translations of L& and LD with the "dotted"
inference below the inference line,

                          A&B           A&B         AD B       A
                            A            B             B

                                    C                      C

but these have the effect of confounding different sequent calculus derivations.
When general elimination rules are used, the order of rules in a sequent calculus
derivation is reflected in natural deduction. Consider, for example, the derivations

             A A
            A * An           AV*fl"                    A       A
              '                 '                                       R&
                                              RR
                  A&B, A&B => A&B                                  A&B L&
                                                           A&B =^^ A&B
                         BACK TO NATURAL DEDUCTION                              179

The usual translation does not distinguish between the two derivations, but gives
for both the natural deduction derivation



                                      A&B
We get instead the two translations

         A&B       [A]         A&B    [B]                    [A] [B]
                   — - &E 1            — - &E 2              -——-—-    &/
               A                  B          '      A&B A&B
                         A&B                          A&B
We have defined the translation root-first, rule after rule, and the order of logical
rules in the natural deduction derivation is the same as that in the sequent calculus
derivation.

(c) Translation from sequent calculus in natural deduction style: The above
translation works on derivations in the calculus GOi. A translation from the sequent
calculus in natural deduction style GN to natural deduction is simpler as there are
no structural rules to be translated. The translation differs from the above only
with rules that use assumptions. Rule L& is translated by


          Am,Bn,r=*C                  A&B [Am],[BnlV =>C
           A&B, V^C                          C

where m and n occurrences of A and B, respectively, are turned into discharged
assumptions. The other rules are translated in the same way.
   A translation from G3i to natural deduction is obtained by use of the connection
between G3i and GOi or GN of Section 5.2(c). Proof editor PESCA produces
natural deduction derivations through proof-search in G3i and a translation to
natural deduction, as in the example of Section C.2(a).


8.3. TRANSLATION FROM NATURAL DEDUCTION TO SEQUENT CALCULUS

We first define a translation from natural deduction to the calculus GOi, then
indicate how derivations in GN are obtained through a simplification of the trans-
lation, and last consider the translation of the special elimination rules of natural
deduction.

(a) The translation: Translation from fully normal natural deduction derivations
with unique discharge to the calculus GOi is defined inductively according to the
last rule used:
180                        STRUCTURAL PROOF THEORY

1. The last rule is Scl:

                      r     A                             r A


2. The last rule is &.E: The natural deduction derivation is

                                       [Am], [Bn], T

                                A&B
                                       c            c    &EU2


The translation is by cases according to values of m and n:



                                            r


                                  A,B,T=>C
                                                ^       T; L&



m = 1, n = 1:

                                       A,B,T


                                                         : L&
                                  A&B, F

Note that the closed assumptions have been opened anew by removal of the
discharge labels and brackets. The cases of m = l,n = 0 and m = 0, n = 1 have
one weakening step before the L & inference.

m > l,n   = 0:




                                            C
                                                        ;O,
                                      A,r
                                                         L&
                                           , r => c
                      BACK TO NATURAL DEDUCTION                                        181

Here Ctr* indicates an m-1 fold contraction, and m occurrences of the closed
assumption A have been opened. The rest of the cases for &E are similar.
3. The last rule is v / :

        r                      r                        r                     r

     AvB                   T^AvB                    AvB                   V =» A v B

4. The last rule is vE: The natural deduction derivation is


                                        [A m ], r       [Bnl A


                                            C

and the translation is again by cases according to the values of m and n, as in
2. We shall indicate by Str the appropriate weakening and contraction steps. The
case without any such steps is when m = 1, n = 1:

                                       A,T        B, A

                                        C           C


The closed assumptions [A] and [B] have been opened. The general case is

                               A m ,T                    Bn,A

                                   C                        C
                            —.—^         7^ Str     —           — Str




5. The last rule is DI: The general case is translated by

                       x                                    Am,r
                       m
                     [A ], T                                 :
                        :                                    B
                                                                 Str
                       B                                 A,T ^ B
                     r\ —J D                             1 ^ ^ r\ -J JD


Again closed assumptions have been opened. If m = 1, there is just the RD rule.
182                      STRUCTURAL PROOF THEORY

6. The last rule is DE: The general case is translated as
                                                                             Bn,A




                   C                                         ADB, T,
7. 77ie to? rw/e w V/:
                            r                                  r

                           VJCA                          T


            rw/e w V £ : The general case is translated as
                                                                         m
                                                                         ,r
                                :                                    C

                       c
9. The last rule is 31:
                            r
                         A(t/x)


            rule is 3E: The general case is translated as
                                                               A(y/x)m,Y

                                                                     C
                                                                                - ^
             3xA             C_V£1                  ^        A(y/x), T •.
                       C                   '                       3xA,T=>C
11. The last rule is the rule of assumption:
                                         A ~> A ^ A
12. The last rule is ±E:
                                    _L
                                    — ±E       ^^              L±
                                    c                   ±=>c
                      BACK TO NATURAL DEDUCTION                                183

Note that in a fully normal derivation, the premiss of rule 1_E is an assumption
and nothing remains to be translated in step 72. If in 77 or 72 there are discharges
they are undone.

Theorem 8.3.1: Given a fully normal natural deduction derivation of C from
open assumptions T, there is a derivation ofY^C  in GOi.

Proof: By the translation defined.    QED.

There are no unused weakenings or contractions in the derivation of F =>• C. By
the translation, we obtain the converse of Theorem 8.2.5:

 Theorem 8.3.2: If A is vacuously (multiply) discharged in the derivation of C
from open assumptions T, then A is a weakening (contraction) formula in the
 derivation ofT^C    in GOi.

The usual explanation of contraction runs something like this: "If you can derive a
formula using assumption A twice, you can also derive it using A only once." But
this is just a verbal statement of the rule of contraction. Logical rules of natural
deduction that discharge assumptions vacuously or multiply are reproduced as
weakenings or contractions plus a logical rule in sequent calculus. However, the
weakening and contraction rules in themselves have no proof-theoretical meaning,
as was pointed out by Gentzen (1936, pp. 513-14) already.
   By the translation of a normal derivation in natural deduction to sequent cal-
culus, each formula in the former appears in the latter. We therefore have, by the
subformula property of GOi, a somewhat surprising proof of

Corollary 8.3.3: Subformula property. In a normal derivation of C from open
assumptions F, each formula in the derivation is a subformula of T, C.

   The translation of non-normal derivations will be given in Section 8.4.

(b) Isomorphic translation: The translations we have defined from natural de-
duction to the sequent calculus GOi and the other way around do not quite estab-
lish an isomorphism between the two: It is possible to permute weakenings and
contractions on a formula A as long as A remains inactive so that isomorphism
obtains modulo such permutations. This is a minor point that we could circum-
vent by adding to the requirement of no unused weakening or contraction the
"last-minute" condition that that there must be no other logical rule between a
weakening or contraction and the logical rules in which the weakening or contrac-
tion formula is used. Another way is to translate directly to the calculus GN that
has no explicit weakening or contraction rules. This also dispenses with the cases
on n and m, and vacuous and multiple discharges are turned into vacuous and
multiple uses in perfect reverse to the translation from GN to natural deduction.
184                    STRUCTURAL PROOF THEORY

Normal natural deduction derivations and cut-free sequent calculus derivations
differ only in notation.
   A translation from natural deduction to G3i is obtained by the connection
between G3i and GOi or GN.
(c) Translation of the special elimination rules: The translations of the special
elimination rules of conjunction lead to the following sequent calculus rules:
                                                            L&S
                                                                 2
                   A&B, F = • A             A&B, F => B
These zero-premiss rules are obtained from rule L & as special cases by setting
C = A and C = B, respectively, translating them, and deleting the premisses
A , B, F =» A and A, B, F =» B that are derivable from A =» A and B => B by
weakening.
    Consider the following derivation of (A&B)&C => A with the special rules
L&S:

                   (A&B)&C     => ASLB L&Sl
                                       L&Sl
                                            A&B => A L & *
                                                    CM
                              (A&B)&C => A              '

The conclusion is not an instance of rule L & S , and therefore cut elimination
fails in this case. We can rewrite the corresponding natural deduction derivation
in terms of the general SLE rule and then convert it into normal form, but the
resulting derivation is not of the form of the special rules anymore.
    The sequent calculus rule corresponding to modus ponens is

                                                 LDS
                               A D B,T =>> B
It can be obtained from rule LD by setting C = B and deleting the right premiss
that is derivable. An example of failure of cut elimination when this special rule
is used is given by
                                                       B =>• B
             A P (B D C), A =» B D C             B D C,B => C
                                                              Cm
                       AD(B    D C),A,B         ^C
where the conclusion is not an instance of LDS and cannot be obtained without
cut. Thus we see that the use of special elimination rules in natural deduction
involves "hidden cuts."
   In Gentzen's original work, a translation of natural deduction derivations into
sequent calculus is described (1934-35, sec. V. 4). Each formula C is first replaced
by a sequent F =^ C, where F is a list of open assumptions C depends on, and
then the rules are translated. Rules &/ and v / are translated in the obvious way.
                     BACK TO NATURAL DEDUCTION                                 185

Translations of D/ and vE involve possible weakenings and contractions, corre-
sponding to vacuous and multiple discharges. Whenever in the natural deduction
there are instances of SLE and DE, the first phase of the translation gives steps
such as
                     T =^ AScB        F ^ AD B        A=^A
                       r =» A                r, A =^ #
These are turned into sequent calculus inferences by the following replacements,
in which in the first derivation a left conjunction rule in Gentzen's original for-
mulation occurs:

                     A=>A_TJ^                           A^A            B^B
                                Cut                                      Cut
                                                    f^X^B
With the knowledge that the special elimination rules of natural deduction cor-
respond to hidden cuts, it is to be expected that a normal derivation in the old
sense translates into a sequent calculus derivation with cuts. In Gentzen's work,
the "Hauptsatz" is proved in terms of sequent calculus, and the possibility of a
formulation in terms of a normal form in intuitionistic natural deduction is only
mentioned. No comment is made about the cuts that the translation of normal
derivations to sequent calculus produces.


8.4.   DERIVATIONS WITH CUTS AND NON-NORMAL DERIVATIONS

We first define a translation from sequent calculus with cuts of a suitable kind
to natural deduction. Then a translation taking any non-normal derivation into a
sequent calculus derivation with cuts is defined. The latter, in combination with
cut elimination and translation back to a normal derivation, gives a normalization
algorithm for natural deduction with general elimination rules.

(a) Derivations with cuts: We show that derivations with cuts can be translated
into natural deduction if the cut formula is principal in both premisses or the
right premiss. These detour cuts and permutation cuts are the principal cuts;
the rest are nonprincipal cuts. Principal cuts correspond, in terms of natural
deduction, to instances of rules of elimination in which the major premisses are
not assumptions. We shall call such premisses conversion formulas.
    A sequent calculus derivation has an equivalent in natural deduction only if
it has no unused weakening or contraction formulas. By this criterion, there is
no correspondence in natural deduction for many of the nonprincipal cuts of
sequent calculus. In particular, if the right premiss of cut has been derived by
186                     STRUCTURAL PROOF THEORY

contraction, the contraction formula is not used in the derivation and there is no
corresponding natural deduction derivation. This is precisely the problematic case
that led Gentzen to use the rule of multicut. If cut and contraction are permuted,
the right premiss of a cut becomes derived by another cut and there is likewise
no translation.
   In translating derivations with cuts, if the left premiss is an axiom, the cut
is deleted. There are five detour cuts and another 25 permutation cuts with left
premiss derived by a logical rule to be translated. We also translate principal cuts
on J_ as well as cases in which the left premiss has been derived by a structural
rule, but derivations with other cases of cuts will not be translated. The translation
of rules other than cut have been given in Section 8.2.
   1. Detour cut on A&B, and we have the derivation



                      r, A =^ A&B                  A&B,       0^C
                                          ^          ^              Cut
                                   r,
The translation is


                                              1.
                        A&B               [A], [B], 0 =» C


Translation now continues from the premisses.
  2-5. Detour cuts on A V /?, A D B, WxA, and 3xA. The translations are
analogous to 1, with the left and right rules translated as in Section 8.2.
   6. Permutation cut on C&D with left premiss derived by L&:


                     A B F =>• C&D      C D A =$> E
                     A&B, r => C&D L& C&D, A=> EL&
                                                 CM
                             A&B, V,A^E

The translation is


         A&B      [A], [B], r =» C&D                      3   4       :
                     C&D                      '•'•       [C], [P], A =» E
                       BACK TO NATURAL DEDUCTION                                           187

Permutation cuts on C&D with left premiss derived by L v, LD, LV, and L3 are
translated analogously, and the same when there are permutation cuts on C v D,
C D D, VxC, and 3xC.
   7. We also have permutation cuts on _L E but no detour cuts since ± can never
be principal in the left premiss. The derivation and its translation are, where L
stands for a (one-premiss) left rule and E for an elimination,




                        r => c                                         c
   5. "Structural" cuts with left premiss derived by weakening, contraction, or
cut. For weakening and contraction the translation reaches, by the condition of
no unused weakening or contraction formulas, a conclusion of cut of the form
[A], r , A => C. These are modified as follows and then the translations are
continued:



                -Wk           -                          ;
                •                     cut          r =k> B B , A
                                                                               CUt
            [A], r, A =^ c                              r, A =^ c

   A, A,r =^
                 Ctr          :                     n.       n.        :             ;
                                                                  !
                                      Cut                                                Cut
           [A], r , A => C                                        [A], r , A => C


For left premiss of cut derived by another cut the translation is modular and the
upper cut is handled as above.
(b) Non-normal derivations: In translating non-normal derivations into deriva-
tions in GOi, there are five cases of non-normality in which the major premiss of
an elimination rule has been derived by the corresponding introduction rule:
   1. The conversion formula has been derived by &/ and the derivation is

                         r        A           i.      2.
                          i       i         [A m ], [Bn], 0
                         A        B                 :
188                    STRUCTURAL PROOF THEORY

The translation is by cases according to values of m and n. The general case is

                                              Am,B\®
                               A                 :
                               :                 C         Str
                           A B      _R&   A,B,S^C
                      r , A =» A&ff     A&£, 0 =» C


   2-5. The conversion formula has been derived by v / , D/, V/, or 3 / , and the
translation is analogous.
   If the conversion formula has been derived by an elimination rule, we have
again a number of cases:
   6. If the rule is &E, the derivation with conversion formula C&D is

                          [A-], [Bni r             3. 4.
                                \                 [Ck], [Dl], A


                                                             «.=..,

The translation is by cases according to values of m, n, k, /, with the general case

                        Am,£n,r                   Ck,D\A

                          C&D          c            ^
                                                                 Str
                                         L&
                    A&B, r => C&D      C&D, A =» ^
                                                  CM
                               r, A =^ ^            '
If A&5 in turn is a conversion formula, another cut, on A&B, is inserted after
the L& rule that concludes the left premiss of the cut on C&D.
   There are altogether 25 cases of translations when the major premiss of an
elimination rule has been derived by an elimination rule. All translations are
analogous to the above.
   Consider a typical principal cut, say, on A&B:



                         T =» A&B          A&B,    A^CL&
                                                    Cut
                                   r^^c
                      BACK TO NATURAL DEDUCTION                                   189

We see that the cut is redundant, in the sense that its left premiss is an ax-
iom, precisely when A&B is an assumption in the corresponding natural deduc-
tion derivation. In this case, the cut is not translated but deleted. We have, in
general:

       A non-normal instance of a logical rule in natural deduction is
       represented in sequent calculus by the corresponding left rule and
       a cut.

Let us compare this explanation of cut to the presentation of cut as a combination
of two lemmas F =>• A and A, A =>• C into a theorem F, A =>• C. Consider the
derivation of C from assumptions A, A in natural deduction. Obviously A plays
an essential role only if it is analyzed into components by an elimination rule;
thus A is a major premiss of that elimination rule. If not, it acts just as a parameter
in the derivation. Our explanation of cut makes more precise the idea of cut as a
combination of lemmas: In terms of sequent calculus, the cut formula has to be
principal in a left rule in the derivation of A, A =>• C.
   Given a non-normal derivation, translation to sequent calculus, followed by
cut elimination and translation back to natural deduction, will produce a normal
derivation:

Theorem 8.4.1: Normalization. Given a natural deduction derivation of C from
F, the derivation converts to a normal derivation of C from F* where each formula
in F* is a formula in F.

The normalization procedure will not produce a unique result since cut elimination
has no unique result.


8.5.   T H E STRUCTURE OF NORMAL DERIVATIONS

We consider three different ways in which a natural deduction derivation with
general elimination rules can fail to be normal, depending on how a major premiss
of an elimination rule was derived. Then the subformula structure of normal
derivations is detailed, with a direct proof of the subformula property. Last, we
give a direct proof of normalization.

(a) Detour conversions: The usual definition of a normal derivation in natural
deduction is that no conclusion of an introduction rule must be the major premiss
of an elimination rule. Non-normal derivations are transformed into normal ones
by detour conversions that delete each such pair of introduction and elimination
rule instances, in the way shown in Section 1.2. To keep things simple, only the
190                    STRUCTURAL PROOF THEORY

cases with no vacuous or multiple discharges were considered there. In a fully
general form, a detour convertibility on the formula A&B obtains in a derivation
whenever it has a part of the form


                                           [Aml [Bn]
                            A B
                                &i
                            A&B                       • &E,1.,2.
                                      C


Detour conversion on A&B gives, through simultaneous substitution, the modi-
fied derivation


                              A, ™x. , A B, .nx. ,B

                                            C



A detour convertibility on A V B is quite analogous. For implication, the situation
is more complicated since a vacuous or multiple discharge is possible also in the
introduction of the conversion formula:


                            [Am]
                                                     [B»]

                           AD B              A        C DE,2.
                                      C


Detour conversion on A D B gives the modified derivation


                            A, ^ x . , A          A, f.x. , A

                                 B,        .wx.       ,B

                                            C
                        BACK TO NATURAL DEDUCTION                               191

Detour convertibilities on V* A and 3x A are as follows:

                  :           [A(t)x)m]                :           [A(y)x)m]
               A(y/x)              :                A(f/x)            :
                        - ^       —       V£         5 ^             k _ 3£




In the detour convertibility on VJCA, the variable restriction on y permits the sub-
stitution of x by t in the derivation of A(y/x). The resulting derivation of A(t/x) is
composed m times with the derivation of C from A(t/x)m. In the detour convert-
ibility on 3x A, since in the auxiliary derivation C was derived from A(y/x) for an
arbitrary j , substitution of x by £ produces a derivation of C from A(t/x)m. The
derivation of A(t/x) is composed m times with it. Thus, detour convertibilities
on VJCA and 3xA convert into one and the same derivation:


                                 A(t/x), ^.x. , A(t/x)

                                               C


    In detour conversions, the open assumptions typically get multiplied into mul-
tiset reducts of the original assumptions, in the way shown in the cases of elim-
ination of principal cuts in the calculus GN of Section 5.2. For example, the
derivation

                                      fi            1.
                                          &,
                                 A&B           [A]
                                                   — - &E,l.
                                      A
converts into the derivation A. The same result is obtained through translation to
sequent calculus:


                        A=» A g=?>g                      A,B ^ A
                         A,B^A&B                          A&B^A


Cut elimination produces the derivation
192                    STRUCTURAL PROOF THEORY

Deletion of the unused weakening gives the derivation A =>> A, corresponding to
the result of the detour conversion.

(b) Permutation conversions for general elimination rules: Normal deriva-
tions with the usual natural deduction rules for conjunction and implication and
without disjunctions have a pleasant property: In each step of inference, the for-
mula below is an immediate subformula of a formula above, or the other way
around. With disjunction elimination, this simple subformula structure along all
branches of a normal derivation tree is lost. On the other hand, if the major premiss
of an elimination step is concluded by disjunction elimination, the derivation can
be transformed into a still more direct form through a permutation conversion.
For example, if both steps are disjunction eliminations, we have

                                          2
                            [A]      [B]                        4.
                                                         [C]
                AvB        Cv D    CvD                    :
                           C v D                          E


This derivation can be transformed into

                                     4.                                    6.
                     [A]     [C]    [Z>]                [B]    [C]    [D]

                   CvD                     W
                                              ZT 3 4
                                                       CvD     E           E

         Ay B               E                                        1 9




by permutation of the second elimination up into the auxiliary derivations of the
first elimination. Fresh discharge labels are introduced in accordance with the
unique discharge principle. Consider now the possibility that C v D i n one of
the auxiliary derivations of the unpermuted derivation is concluded by v / . After
the permutation conversion, this occurrence of C v D is both a major premiss
of an elimination rule and a conclusion of an introduction rule. There obtains a
"hidden" detour convertibility that becomes an actual one after the permutation
conversion.
    For predicate logic, there is a permutation conversion for existence elimination.
Permutation conversions for disjunction and existence were found by Prawitz in
1965.
    The above derivations with disjunction elimination are not fully normal in the
sense of Definition 8.2.2. As was shown in the previous section, their translations
                     BACK TO NATURAL DEDUCTION                               193

to sequent calculus are

                  C V D B => C v D                C => E D => E
                                              V
                  Av B = ^ C V D                    Cv D^ E
                                                                  Cut



and

                  C =» E D ^ E                                C ^ E D =>> ^
                               V                                            Lv
  A^Cv/)            CvD=>E       B^CvD                            CvD^



Thus the conversion of the natural deduction derivation into a more direct form
corresponds to a step of cut elimination, where a cut with cut formula principal in
the right premiss only is permuted with L v to move it upward in the derivation.
   T h e general elimination rules for conjunction, implication, and universal
quantification permit the permutation of eliminations u p in the same way as with
disjunction a n d existence elimination. Thus the structural properties of deriva-
tions with the three special elimination rules are quite different from those with
the general elimination rules. To give an example, with the special rules w e have
the derivation

                                    (AScB)ScC
                                       A&B~~
                                         A
With the general rule, this becomes the derivation

                      {ASLB)8LC     [A&B]
                                              &E,1.
                              A&B                     [A]
                                                            &EX
                                          A                                   (1)

Here the major premiss of the second inference is a conclusion of &E, and we
have a permutation conversion into

                                       [A&B]          [A]
                                                       &EX
                          (A&B)&C         A
                                                                               (2)

where the major premisses of both instances of &E are assumptions. With the
special elimination rules, hidden convertibilities remain, in the form of major
premisses of elimination rules that are not assumptions, as is made clear in the
translation from non-normal derivations to sequent calculus derivations with cuts.
194                     STRUCTURAL PROOF THEORY

   The above examples showed how permutation conversion works for disjunc-
tion elimination and general conjunction elimination. As an illustration of full nor-
mal form with general implication elimination, we solve a problem of normal form
of Ekman (1998). Ekman found that a derivation of the formula ~ (P DC ~ P),
in which equivalence is implication in both directions, either is not normal or else
has a subderivation of the form

                                                                                Mp
                          P D ~P                     P
                                                           Mp


The derivation has the redundancy, or is "indirect" in Ekman's terminology, in
that the derivation of the conclusion could be replaced by the derivation of the
first occurrence of ~ P . However, this will produce a non-normal derivation, for
the top occurrence of ~ P is the conclusion of DI and the bottom occurrence is
a major premiss of DE. This problem is solved by use of the general implication
elimination rule:
                                             2       3       1

                                                                 — '   £L , 1                r-   J-J -i   r   j-v   -i   r   .   -i




                                                      DEa
                                                      DEa
                                    TT                            [f3            ~P]   IP]
                                      D/3
                                                                                         DE,6
[(PD~P)&(~P D />)]                           J. &E,7 ,8
                                                 &E,7 ,8




All major premisses of elimination rules in the derivation are assumptions, which
is the characteristic property of normal derivations with general elimination rules.
Further, the conclusion ~ P by DI is not a major premiss of DE.
    The origin of the above problem is in the observation that Russell's paradox
about "the set of all sets that are not members of themselves" can be derived
intuitionistically, without the law of excluded middle. Deleting the last line of our
derivation and reading P as "the set of all sets that are not members of themselves
belongs to itself," we derive a contradiction from ( P D ~ P)&(~ P D P).
(c) Simplification conversions: Other reductions of natural deduction deriva-
tions exist besides detour and permutation conversions. In Prawitz (1971), a
simplification of derivations in natural deduction is suggested, called properly
simplification conversion. The convertibility arises from disjunction elimina-
tion when in at least one of the auxiliary derivations, say, the first one, a disjunct
was not assumed:

                              T          A           [B],&


                                         c                  c_yEX
                      BACK TO NATURAL DEDUCTION                                 195

The elimination step is not needed, for C is already concluded in the first auxiliary
derivation. With general elimination rules for conjunction and implication, we
analogously have

                     r         A                    r           A   ©

                               C                A       B   A         C
                                    &E              ^                     , E



In both inferences, C is already concluded without the elimination rule, and sim-
plification conversion extends to all elimination rules, quantifier rules included.
In terms of sequent calculus GN, Definition 5.2.7, there is in each of these infer-
ences a (hereditarily) vacuous cut with cut formula concluded by a left rule in the
right premiss. For example, translating the disjunction case to GN we have

                                                                     - Lv
                                                                    Cut



which converts to A =>• C, and A is a multiset reduct of the antecedent of conclu-
sion of the original cut. The other elimination rules lead to similar conversions.
In the notion of vacuous cut, we find the systematic origin of simplification con-
versions, extending to all elimination rules. The notion is captured in terms of
natural deduction by

Definition 8.5.1: A simplification convertibility in a derivation is an instance
of an E-rule with no discharged assumptions, or an instance ofvE with no
discharges of at least one disjunct.

A simplification convertibility can prevent the normalization of a derivation, as
is shown by the following:


                         [A]         [B]
                                   D/1    D/,2.
                                   BDB-                 JC]_
                         (A D A)&(B D B )               CDC'
                                                         CDC
                                                                    &E
                                    C~D~C

There is a detour convertibility but the pieces of derivation do not fit together in
the right way to remove it. Instead, a simplification conversion into the derivation


                                          [C]
                                                D/,3.
                                         CDC

will remove the detour convertibility.
196                    STRUCTURAL PROOF THEORY

   It is possible that in a simplification convertibility with vE, both auxiliary as-
sumptions are vacuously discharged. In this case, there are two converted deriva-
tions of the conclusion.

(d) The subformula structure of general elimination rules: With special elim-
ination rules in the v- and 3-free fragment, there is a simple subformula structure
along all branches of a normal derivation, from assumptions to a minor premiss
of rule DE or to the conclusion. In fully normal derivations with general elimina-
tion rules, branches are replaced by threads that jump from major premisses to
their auxiliary assumptions. Contrary to first appearance, a greater uniformity in
the structure of derivations, for the full language of predicate logic, is achieved.
   The subformula property in natural deduction is more complicated than in
sequent calculus because of the nonlocal character of the rules of inference. It is
obtained through the notion of thread where for simplicity we assume that no
simplification convertibilities obtain:

Definition 8.5.2: A thread in a natural deduction derivation of C from open
assumptions F without simplification convertibilities is a sequence of formulas
A\, ..., An such that

   1. An is either C or a minor premiss of DE.
   2. A/_i is either a major premiss with auxiliary assumption At in an E-rule,
      or a minor premiss with A/_i = At in an E-rule, or a premiss with conclu-
      sion At in an I-rule.
   3. A\ is a top formula not discharged by an E-rule.

Threads typically run through a sequence of major premisses of £-rules until the
conclusion of the innermost major premiss is built up by /-rules, and so on. If
vacuous instances of elimination rules are admitted, there can be threads that stop
at the major premiss.
    Threads in a normal derivation, briefly, normal threads, have the following
structure:

                                 E-part




In the £-part, the major premisses follow in succession and Ai+\ is an immediate
subformula of At. In the /-part, either Ai+\ is equal to At or At is an immediate
subformula of A i + 1 .
   We concluded in Corollary 8.3.3 the subformula property of normal derivations
with general elimination rules by a corresponding result that is immediate for the
                     BACK TO NATURAL DEDUCTION                                197

sequent calculus GOi. A more direct proof in terms of natural deduction sheds
some light on the structure of threads:
Direct proof of the subformula property: Each formula A is in at least one
normal thread, and it is a subformula of the topformula or of the endformula of
the thread. In the former case, the topformula is either an open assumption and the
subformula property follows, else it is discharged by DI and A is a subformula
of the endformula of the thread. If the endformula is the conclusion of the whole
derivation, the subformula property follows. If it is the endformula of a minor
thread, it is also a subformula of the corresponding major premiss. The major
premiss is either an open assumption and the subformula property follows. Else
the major premiss is discharged by D/and belongs to some normal thread with the
endformula further down in the derivation. If this endformula is the conclusion
of the derivation, the subformula property follows; if not, by repetition of the
argument, the conclusion is reached. QED.

   In sequent calculus, the rule of falsity elimination is represented by a sequent
_L =>> C by which derivations can start. In standard natural deduction, instead,
falsity elimination can apply at any stage of a derivation. This discrepancy is now
explained as a hidden convertibility. In particular, if the conversion formula is
_L derived by ±E, we have a derivation with two non-normal instances of ±E.
Since _LE has only a major premiss, a permutation conversion just removes one
of these instances:




The first derivation has the translation to sequent calculus



                                                        Cut


and the converted one




Fully normal derivations do not have redundant iterations of ±E. In Prawitz
(1965, p. 20), the effect of the above permutation conversion is achieved by the
ad hoc restriction that in _L E the conclusion be different from _L.
198                    STRUCTURAL PROOF THEORY

   In a typical application of _L E in natural deduction with the special elimination
rules we have, using the modus ponens rule,

                                   A        A
                                    ^>±       MP


With the more general implication elimination rule, the derivation and its permu-
tation conversion are

            ADI       A    [_L]                                 [JL]



Here the premiss _L is converted into a topformula of the derivation. The same
applies in general and we thus obtain

Proposition 8.5.3: A fully normal intuitionistic derivation begins with assump-
tions and instances of the intuitionistic rule _L E, followed by a subderivation in
minimal logic.

This fact will give a natural translation of intuitionistic into minimal logic: Con-
sider an intuitionistic derivation of C in full normal form. The conclusions of
falsity elimination are derivable from falsity eliminations concluding atoms. By
the subformula property, these are atoms of C, and let them be P\,.. .,Pn. Each
step y is replaced by an assumption _L D />•, and Pt is concluded from _L by DE
instead of ±E. Collecting all the new assumptions, we obtain

Theorem 8.5.4: Formula C is intuitionistically derivable if and only if

                          (_L DPi)&...&(_L         DPn)DC
is derivable in minimal logic.

In normal derivations with special elimination rules in the v- and 3-free fragment,
there is a simple subformula structure along all branches from assumptions to a
minor premiss of rule DE or the conclusion. In normal derivations with gen-
eral elimination rules, branches are replaced by threads that jump from major
premisses to their auxiliary assumptions. Contrary to first appearance, a greater
uniformity in the structure of derivations is achieved.

(e) Normalization: Theorem 8.4.1 gave a proof of normalization for intuition-
istic natural deduction with general elimination rules through a translation to
sequent calculus, cut elimination, and translation back to natural deduction. A di-
rect proof of normalization is also possible. To simplify matters, we assume that
                     BACK TO NATURAL DEDUCTION                                 199

no simplification convertibilities are met in normalization. The proof is presented
in its main lines.

Direct proof of normalization: In order to prove normalization, we shall define
an ordering on threads of a derivation depending on their conversion formulas and
a secondary ordering depending on the position of major premisses of elimination
rules in them.
   With each thread is associated a multiset of convertible formulas, giving the
number of convertible formulas of length 0, length 1, length 2 , . . . , of a maximum
length /. These multisets are ordered as follows: Of two multisets, the one with the
shorter formula of maximum length comes first. If both have maximum length /,
the one with a lesser number formulas of that length comes first. If these numbers
are equal, consider formulas of length / — 1, and so on. Multisets of convertible
formulas in threads are ordered so that detour conversions reduce threads in the
ordering.
   The height along a thread of a major premiss At is measured as follows. Let
h\ be the number of steps from the topformula to a first major premiss in the
thread and ht the number of steps from the auxiliary assumption of major premiss
A/_i to major premiss At. The height of At in the thread is the sum h\ + • • • + hi.
Thus, if A\ o B\,... ,Am o Bm are the major premisses of a thread (A,... ,C),
height along the thread can be depicted as follows, where major premisses are
separated by a semicolon from the auxiliary assumptions that follow them:




From the construction of threads it is immediate that each formula in a derivation
is in at least one thread. The height of each major premiss along normal threads
is equal to zero. It is easily seen that the converse also holds. A permutation
conversion on At has the effect of diminishing the height of At by one while
maintaining the heights of major premisses coming before At along the thread.
The threads are ordered lexicographically, according to the height of their first
major premiss, second major premiss, and so on, with the effect that permutation
conversions give threads that are reduced in the ordering.
    Next we control the effect of conversions on threads. Given a non-normal
derivation, its major premisses are the possible conversion formulas and no new
possible conversion formulas are created under conversions:

1. Detour conversion on &: Assume the relevant part of the full derivation to be
as in Section 8.5(a). The convertibility on the formula A&B in a thread such as

                         (..., A, A & f i ; A , . . . , C , C , . . . )
200                     STRUCTURAL PROOF THEORY

disappears, and there is a possible new convertibility on the formula A in the
corresponding thread



so that the multiset of convertible formulas is reduced.
2. Detour conversion on v: This case is identical to the above, save for changing
& into V.
3. Detour conversion on D: Assume that the thread comes from a derivation such
as the one in Section 8.5(a), and assume that the thread includes the discharged
assumption A of D/. Before the conversion, we have a major thread

                       (A

In the conversion, the derivation of A is substituted for the assumption A, which
creates a converted thread

                              (..., A , . . . , £ , . . . , C , . . . )

The addition of a minor thread (..., A) leading to the minor premiss A in the
beginning of the converted thread could add new convertible formulas longer
than any in the original major thread. We instead do the following: In a detour
conversion on implication, the discharged assumptions A in DI are temporarily
replaced by open assumptions A, with threads of type

                                 (A,..., £ , . . . , C,...)

as a result, and a separate derivation of the minor premiss A. Thus the derivation
is cut into parts, and we show that these parts and any subsequent parts that might
turn up normalize, after which the assumptions A can be substituted by their
normal derivations. If this creates new convertibilities, they are on strictly shorter
formulas so that the process terminates.
    We shall next show that permutation conversions reduce the heights of major
premisses along threads without importing new convertible formulas. There are
many cases, but we consider only one of them as the rest act in the same way on
threads.
4. Permutation conversion on & with major premiss C&D derived by &E, the
latter rule having A&B as major premiss: Typical threads before and after con-
version are

    (..., A&B, A, . . . , C&D, C&D; C, . . . , E, E, ...)
                         ~>      (..., A&B; A, . . . , C&D; C,...,        E, E, E, ...)
                      BACK TO NATURAL DEDUCTION                                  201

Height along thread of major premiss CSLD is reduced by one while heights
of major premisses preceding it remain the same. The multiset of convertible
formulas does not increase.
The effect of conversions on threads for the case of quantifiers is analogous to
the above and will not be detailed.
    The cutting into parts of the original derivation whenever a detour convertibility
on implication is met can happen only a bounded number of times, since no new
major premisses of elimination rules are created by any conversions. Each detour
conversion reduces the multiset of convertible formulas and each permutation
conversion does not increase it but reduces the height of a major premiss along
threads. When no convertibilities remain, the assumptions in detour convertibil-
ities on implication are substituted by the derivations of the minor premisses.
Since these formulas are proper subformulas of the original convertible formulas,
also this process terminates, and we have threads with no convertible formulas
and zero heights along threads for major premisses of elimination rules. QED.

The proof of normalization almost establishes strong normalization, that is,
the termination of conversions in any order whatsoever. The only restriction is
that the detour conversions on implication are completed only after all other
convertibilities have been exhausted. This restriction is not essential, as is shown
by the proof of strong normalization and uniqueness of normal form for our system
of natural deduction given by Joachimski and Matthes (2001). Their proof uses a
system of term assignment.
   It would be a redundancy in a normal derivation if it had major premisses of
elimination rules that are derivable formulas:
Definition 8.5.5: A major premiss of an elimination rule is a proper assumption
if it is underivable.
Theorem 8.5.6: Given a derivation, there is a derivation in which all major
premisses of elimination rules are proper assumptions.
Proof: Consider a derivable maj or premiss A. In a normal derivation of A, the last
rule must be an /-rule since an £-rule would leave an open assumption. A substi-
tution of assumption A with a normal derivation creates a detour convertibility.
From the conversion schemes, we observe that no conversion ever produces new
major premisses of £-rules and that detour conversions produce shorter convert-
ible formulas. Therefore the process of substituting derivable major premisses
of E -rules with their derivations and subsequent normalization terminates in a
derivation with proper assumptions. QED.
By the undecidability of predicate logic, the theorem does not give an effective
proof transformation. A translation to sequent calculus gives
202                    STRUCTURAL PROOF THEORY

Corollary 8.5.7: If the sequent T => C is derivable in GOi, it has a derivation
in which all formulas principal in left rules are underivable.

The eliminability of derivable principal formulas in left rules was discovered by
Mints (1993). The formulation in terms of natural deduction makes it clear what
the result means. The result can, of course, be extended to all assumptions.


8.6.   CLASSICAL NATURAL DEDUCTION FOR PROPOSITIONAL LOGIC

We shall add to the sequent calculus GOip the law of excluded middle in the
form of a rule for atomic formulas similar to the one in Section 5.4, but with
independent contexts. We then note that cut remains admissible, and that the
rule itself is admissible for arbitrary propositional formulas. It follows that the
calculus is complete for classical propositional logic. Then the translation from
sequent calculus to natural deduction is extended by the translation of the rule of
excluded middle.

(a) The rule of excluded middle: With P an atom and F, A, C arbitrary, the
rule of excluded middle for atoms is


                                                     Gem0 at
                                                         -

The only difference with respect to the rule of excluded middle added to the
calculus G3ip in Section 5.4 is that now we have independent contexts. Proofs of
all essential results go through without difficulty.

Theorem 8.6.1: The rule of cut is admissible in GOip+GemO-at.

Proof: The proof is a continuation of the proof of cut elimination for the intuition-
istic calculus GOip by induction on the length of cut formula A with subinduction
on the sum of heights of premisses of cut. Cut is permuted upward to cuts on
the same formula but with lower cut-height, entirely analogously to the proof of
Theorem 5.4.4. QED.

Theorem 8.6.2: The rule of excluded middle for arbitrary formulas,

                                                     -GemO
                                  r, A=>C
is admissible in GOip+GemO-at.

Proof: The proof is by induction on formula length. Cut is admissible and can
be used in the proof.
                         BACK TO NATURAL DEDUCTION                                             203

   For A \— JL, we derive the conclusion from the right premiss already by a cut
with the derivable sequent F =^ J_ D _L. For A := P, excluded middle is the rule
GemO-at.
   For A := A&B, we have the premisses A&£, F => C,and~(A&£), A =» C.
Cut of the first by the derivable sequent A, B =>• A&5 gives A, #, F =^ C, and
cut of the second by the derivable sequent ~ A =>• ~ (A&5) gives ~ A, A =>• C.
By inductive hypothesis, the rule GemO applied to A gives B, F, A =^ C. Cut of
the second premiss by the derivable sequent ~ 5 =>~(A&#) gives ~ # , A =>• C,
and rule GemO applied to B now gives F, A, A => C that can be contracted to
r, A => C.
   The cases of disjunction and implication are similar. QED.

Using the rule, we easily derive the sequent =^Av~A. Since cut is admissible
and the law of excluded middle derivable, the calculus is complete for classical
propositional logic.

(b) Translation to natural deduction and back: The rule of excluded middle,
in a notation not indicating possible vacuous or multiple discharges, is given by



                                 C           C
                                                 -Nem-at,l.,2.
                                        c
where the assumptions P and ~ P are discharged at the inference. The common
natural deduction rule in classical logic, concluding an atom P if ~ P leads to
falsity, is a special case, as we shall see.
   The translation from sequent calculus to classical natural deduction is obtained
by the addition of the following to the previous translation in Section 8.2:

p , r > c         P , A > C                      [P],r^c                  [ > ] , A » C
        ——         —          GemO-at   ~>                          —                     Nem-at,\., 2.
        1 , ZA —•? i_^                                              \~s


The converse translation of an instance of the rule Nem-at requires the use of
unique labeling for the m discharged assumptions P and n assumptions ~ P ,
where ~ Pn denotes n copies of formula ~ P:

                              [H,r          [~PW], A


                                c                c
                                        c         — Nem-at,l., 2.
204                    STRUCTURAL PROOF THEORY

The translation is by cases according to the values of m, n. The general case is
                          pm p            ^ pn    A



                            C                 C
                                -—i Str                — Str
                                                      Gem0 at
                                  r,A=>c                       -
The closed assumptions have been opened. If m = n = 1, there is just rule
GemO-at and no weakening or contraction.
   We obtain a sequent calculus closer to classical natural deduction by starting
with the calculus GN and adding to it a rule of excluded middle with weakening
and contraction with P and ~ P built in:


                                      r, A =^c
Translation to natural deduction and back is simplified in the same way as with
the translation of logical rules in Section 8.2(c).
(c) Full normal form for classical propositional logic: We can now conclude
the main results for normal derivations in classical natural deduction from the
corresponding results in the single succedent sequent calculus formulation.
   The usual system of classical natural deduction uses the rule of indirect proof
for atoms, a special case of our rule. The rule of indirect proof is derivable from
Nem-at: Assume that there is a derivation of _L from ~ P\ then use rule ±E to
get the derivation




                                           Nem-at, l.,2.


Contrary to the rule of indirect proof, the premiss ~ P is not discharged after
_L, but one step later. It is possible to convert indirect inferences on disjunc-
tions into their components only if the disjunctions are also major premisses
in a vE'-rule. Thus full normal form fails for this rule (see also Prawitz 1965,
p. 39, and Stalmarck 1991), but this is repaired in natural deduction for classical
propositional logic with general elimination rules and the rule of excluded middle:
Translations into natural deduction of the derivations in the proof of admissibility
of excluded middle for arbitrary formulas, Theorem 5.4.6, give a uniform method
for converting instances of the natural deduction rule of excluded middle for
                       BACK TO NATURAL DEDUCTION                                          205

arbitrary formulas A

                               [Am]        [~A n ]


                                                       -Nem,l.,2.
                                           c
into ones with the rule Nem-at.

Lemma 8.6.3: Application of the rule of natural deduction excluded middle con-
verts to applications of natural deduction excluded middle to atoms.

Proof: Consider the case in which indirect proof is insufficient, that of a disjunc-
tion A v B: We assume given the two derivations

                              AvB                  -(AvB)

                                  C                      C
Derivation of C by Nem applied to Aw B,

                             [AVB]             [-(AvB)]

                                C
                                                         C      M
                                               c                 Nem

is converted into the derivation with Nem applied to A and B,


                                      3.
                                                                [A]         [[~g]
                                                                              ]     [B]
                                                                                    []
                                [AvB]                    JL
                     \A^
          6.
         [B]       L^J
                   AVB                             ~(AVB)
       Ay B VI
         :             C                                     C Nem, 4.,5.
         c                            c
                                      -Nem,    6.,7.

The other cases of conversions of Nem-at are obtained by translating to natural
deduction the rest of the transformations in the proof of Theorem 5.4.6. QED.

Definition 8.6.4: A derivation in intuitionistic natural deduction H-Nem-at is in
full normal form if no instance of Nem-at is followed by a logical rule and
all sub derivations up to instances of Nem-at are fully normal intuitionistic
derivations.
206                    STRUCTURAL PROOF THEORY

Theorem 8.6.5: If a formula C is derivable from open assumptions T in intuition-
istic natural deduction +Nem-at there is a derivation of C from open assumptions
F* in full normal form, where F* is a multiset reduct of T.

Proof: A routine verification shows that rule Nem-at commutes with the logical
rules, modulo possible multiplications of open assumptions. QED.

Thus, if formula C is classically derivable, the corresponding natural deduc-
tion derivation has by the theorem a neat separation of minimal, intuitionistic
and classical parts: It begins with assumptions and instances of the intuitionistic
^±E rule, followed by a minimal subderivation, and ends with purely classical
applications of the rule of excluded middle. As in sequent calculus, these can
further be restricted to atoms of C:

Theorem 8.6.6: In a derivation of C from open assumptions T in intuitionis-
tic natural deduction +Nem-at, instances of Nem-at can be restricted to atoms
ofC.

Proof: Permute down applications of Nem-at so that those on atoms not in C
come right after the intuitionistic subderivation. Let the first of these be on an
atom P:




                                 c          c
                                      c
The first subderivation of C, from P, Ff, is transformed into a derivation of ~ P
from ~ C, F r which is then substituted for the assumption of ~ P in the second
subderivation, followed by an application of Nem to C:


                                          in r
                                            C
                                 1^3            -,E
                                                       T"

                           [C]               C_ •Nem,2.,3.
                                     c
By Lemma 8.6.3, the application of Nem to C converts to atoms of C. The proof
transformation is repeated for the remaining atoms that are not atoms in C. QED.
                      BACK TO NATURAL DEDUCTION                                 207

   Full normal form gives a translation from classical to intuitionistic and minimal
propositional logic:

Proposition 8.6.7: Let P\,...,    Pnbe the atoms ofC. Then C is classically deriv-
able if and only if

                       (PlV~P 1 )&...&(P B V~P B )DC

is intuitionistically derivable. Further, C is classically derivable if and only if

        (± D P0&...&U. D P«)&(PiV ~P!)&...&(PBV - P J 3 C

w derivable in minimal logic.

Proof: In a given classical derivation of C, transform each instance of Nem-at,
at the bottom of the intuitionistic subderivation, into an intuitionistic inference
concluding C by v E through the assumptions Pt v ~ Pt for all atoms Pt of C. Now
collect all these assumptions together and use the translation from intuitionistic
to minimal logic, Theorem 8.5.4. QED.

Given a classical derivation with rule Nem, normalization will give a derivation
with instances of Nem-at. The above translations can be optimized by leaving
out those assumptions P(v ~ Pt for which there is no corresponding instance of
Nem-at in the derivation.

   Next consider the translation of a classical derivation of C into an intuitionistic
derivation of (Pi v ~P\)8c... &(Pnw ~ Pn) D C. If C is already intuitionistically
derivable, the antecedent is empty and we can identify C as the set of its formal
proofs through the Curry-Howard isomorphism. If not, the proof of Proposition
8.6.7 shows how, in terms of natural deduction, the proof of C reduces to the
intuitionistic subderivations. The usual way of applying the formulas-as-types
principle to classical theories is to assume the law of excluded middle for arbi-
trary formulas. In the notation of constructive type theory, this can be done by
the type declaration em : Av ~ A. No one, of course, can in general tell how
such a function em should be evaluated. However, now we can look on the fully
normal classical derivation of Cas an instruction on how to construct the function
that converts decisions on atoms P\,..., Pn into a proof of C. For example,
if we have a set S with a decidable equality Eq : (S)(S)Prop, the declaration
deq : (a,b : S)Or(Eq(a, b), ~Eq(a, b)) will implement a classical logic for the
language of this equality. Sometimes, as with equality for natural numbers, we
can actually define such a function deq.
   By adding proof terms to the rule of excluded middle, a satisfactory formulation
of the Curry-Howard isomorphism for classical propositional logic is obtained,
but we shall not go into the details.
208                     STRUCTURAL PROOF THEORY

NOTES TO CHAPTER 8

In Prawitz' book of 1965, a system of sequent calculus is given with shared contexts
treated as sets and axioms of the form A,T =$> A, thus with weakening built into
the system and no cut rule. A proof of closure with respect to cut is sketched, through
completeness of natural deduction and translation of normal derivations into cut-free
sequent calculus derivations (p. 91). Prawitz uses a sequent calculus with Gentzen's
original L& rules, and therefore the special conjunction elimination rules do not
produce cuts. Uses of modus ponens can also be turned into a cut-free sequent cal-
culus derivation, for a detailed study shows that a cut elimination procedure is infact
contained in its translation.
    In Zucker's paper (1974) on translation from sequent calculus to natural deduction,
it is stated that "one or both of these systems must be modified to some extent," but the
change on natural deduction just concerns discharge of assumptions. In a related paper
by Pottinger (1977) an example demonstrates the failure of isomorphism between
sequent calculus and natural deduction with the usual 8LE rules (p. 350, see also
Zucker, p. 2). No one seems to have followed the idea that it is this system of natural
deduction, not sequent calculus, that lies at the back of the failure of isomorphism
between derivations in the two calculi. In Herbelin (1995) (see also Dyckhoff and
Pinto 1998), a sequent calculus is given that does not distinguish between derivations
obtainable in standard calculi from each other through certain permutations, and a
unique correspondence with natural deduction derivations with special elimination
rules is achieved.
    There is another way of arriving at the general elimination rule for conjunction
than the inversion principle we have used, namely, constructive type theory. The
general rule comes straight out by suppressing the proof objects in the typed rule,
as in Martin-L6f (1984, p. 44). In the other direction, typing our general implication
elimination rule will result in a new selector, generalized application:

                                                  [x : B]

                             c: A P B a: A d : C
                                 gap(c,a,(x)d) : C

A full type-theoretical rule uses the function type (A)B that has no correspondence in
first-order logic. The usual first-order selector ap that corresponds to modus ponens
is defined, for B = C, by ap(c, a) = gap(c, a, (x)x) : B. Normality means that each
selector term has a variable as first argument. A direct proof of strong normalization
for natural deduction with general elimination rules was found by Joachimski and
Matthes (2001), through a term assignment system. (They also suggested the term
generalized application for general implication elimination typed.)
    The solution of Ekman's problem comes from von Plato (2000).
    The natural deduction formulation of the rule of excluded middle was studied al-
ready in Tennant (1978) but has remained relatively unknown even if its first appear-
ance is due to Gentzen (1936). The reason should be that no subformula property
had been proved within a natural deduction approach. However, Tennant proves a
                      BACK TO NATURAL DEDUCTION                                  209

natural deduction version of our Lemma 8.6.3 and the important result that applica-
tions of the rule reduce to applications on atoms.
   In Gordeev (1987), a sequent calculus rule corresponding to Peirce's law is given,
concluding F =$> A from A D B,F =$> A. Admissibility of cut and the subformula
property are proved. This calculus is complete for classical propositional logic, but
cannot be extended with nonlogical rules of inference while maintaining cut elimi-
nation, contrary to our classical calculus.
   Extensions of the sequent calculus G3i by nonlogical rules translate into normal
natural deductions, in which the nonlogical natural deduction rules are obtained from
the translation of the single succedent rule-scheme for sequents:

                                           [Gil [Qn]

                              Py...Pm         C ... C

This is the natural deduction scheme for nonlogical elimination rules. An early work
that uses rules of this form, for equality and apartness, is Van Dalen and Statman
(1979).
   In Hallnas and Schroeder-Heister (1990), regular sequents P i , . . . , Pm =>> Q are
translated, for the purposes of logic programming, into natural deduction rules of the
form


                                          Q
The two kinds of nonlogical natural deduction rules are interderivable. The relation
of these two ways of extending natural deduction is analogous to the situation in
sequent calculus: Extension of sequent systems with regular sequents does not in
general permit cut-free derivations, whereas extension with nonlogical rules does.
This is seen clearly in the example of predicate logic with equality.
                                  CONCLUSION


         Diversity and Unity in Structural Proof Theory




COMPARING SEQUENT CALCULUS AND NATURAL DEDUCTION

Structural proof theory was born in two forms, natural deduction and sequent
calculus. The former has been the more accessible way to proof theory, used in
teaching. The latter, instead, has yielded better to structural proof analysis. For
example, the underivability results for intuitionistic predicate logic in Section 4.3
were obtained for sequent calculus in the early 1950s.
   Even if natural deduction gives the easier access, in the end proofs are easier
to find in sequent calculus. It formalizes the analysis into subgoals of the theo-
rem to be proved, whereas in natural deduction this has to be done intuitively.
Furthermore, the sequent calculi we studied in Chapters 2-4, with their shared
contexts in two-premiss rules, support root-first proof search.
   With independent contexts, we found sequent calculi that come very close to
natural deduction, especially if in the latter general elimination rules are used.
One essential difference, the presence in sequent calculus of explicit rules of
weakening and contraction, was overcome by a suitable change of the logical
rules of sequent calculus to permit implicit weakening and contraction similarly
to natural deduction. Then cut-free proofs in sequent calculus and normal proofs
in natural deduction became mere notational variants of one and the same proof.
Isomorphic translation turned the sequent calculus derivation with its locally
applied rules into a standard nonlocal natural deduction derivation. One difference
between the two types of calculi remained: Where the logical rules of natural
deduction admit of non-normal instances, sequent calculus uses a logical rule and
a cut. It is a cut with the cut formula principal in at least the right premiss. Because
of the presence of an independent rule of cut, transformation of a sequent calculus
derivation into cut-free form is profoundly different from the conversion of a
natural deduction derivation into normal form. There are cuts with nonprincipal
formulas that have no interpretation in terms of natural deduction. Even here the
gap between the two formulations of structural proof theory was narrowed: first,



                                                                                   211
212                                CONCLUSION

by the restriction of cut elimination to the hereditarily principal cuts of Section 5.2,
and secondly, by the implicit treatment of weakening and contraction that does
away with a number of cuts and permutations of cuts to which nothing corresponds
in natural deduction.
    Gentzen's doctoral thesis gave the rules of sequent calculus in two groups,
the structural rules as the first group, and the logical rules as the second. A few
years later he called the rules of weakening, contraction, exchange and change
of bound variable "Strukturanderungen," structural modifications (1936, p. 513).
(Gentzen treated contexts as lists in which the exchange of order was needed,
contrary to multisets.) All of the structural modifications except weakening "do
not change the meaning of a sequent... all these possibilities of modification are
of a purely formal nature. It is only because of special features of the formalism
that these rules must be expressly given." (ibid., pp. 513-14). Weakening can be
justified by admitting that if a proposition is correct under given assumptions, it
should remain correct if arbitrary additional assumptions are made. Despite these
words of Gentzen, a lot of work has been done in structural proof theory in the
search of some ultimate meaning of weakening and contraction in themselves,
independent of a formalism of logical rules. We have shown that the change to
general elimination rules permits the interpretation of weakening and contraction
in terms of natural deduction, as vacuous and multiple discharge of assumptions,
respectively. Here again, as with the rule of cut, the formulation of weakening
and contraction as independent rules brings cases that have no correspondence in
natural deduction.
    There is more work to be done in relating cut elimination to normalization.
The rule of cut has been usually left as something one should not touch; but
going back to the historical origins in Gentzen (in particular, his first paper that
appeared in 1932), we find that he considered various forms of rules, one of which
is the cut rule. It descends from work of Paul Hertz in the 1920s: In Hertz (1929,
p. 462), a rule of "syllogism" is suggested that we can write as




The n formulas A\,...,   An in the rightmost premiss are cut in one step of infer-
ence, so we can call Hertz' rule simultaneous cut. Gentzen's rule of cut is the
special case of n = 1. The rule of multicut of Section 5.1 is a somewhat different
generalization of cut, with just one premiss F => A on the left and all of the At
identical to A, thus with n copies of A in the right premiss deleted in one step.
Gentzen's mix rule in (1934-35, III.3.1) is a cut in which n copies of the cut
formula in the left premiss and m copies in the right one are deleted.
                                    CONCLUSION                                   213

   Another rule relating to cut is the "chain rule" ("Kettenschluss," Gentzen 1936,
p. 543) that we can write as

                                                                    chn
                                f1 1 , r. . . , i „
Looking at the indices, one sees that the idea of the rule comes from the way
recursion on natural numbers works.
    As Gentzen (1932, p. 332) remarks, the rule of simultaneous cut follows by
repeated applications of the rule of cut. However, we should note that once a
series of cuts reproduces the conclusion of a simultaneous cut, these cuts can be
eliminated in any order, typically leading to different cut-free proofs. The rule of
simultaneous cut with all of the premisses Tt =>• At identical corresponds exactly
to the simultaneous substitution created by a detour conversion, as in Section 8.5.
    It seems plausible that one can define a cut elimination procedure that uses
some generalization of cut in intermediate stages, with results analogous to those
of strong normalization and confluence (uniqueness of normal form) in natural
deduction. Moreover, if this can be done for a single succedent intuitionistic
calculus, the calculus GN in the first place, it should be possible for a classical
multisuccedent calculus such as GM as well.
    When sequent calculus and natural deduction are compared, an outstanding
difference is the elegant treatment of classical predicate logic in multisuccedent
sequent calculus. Natural deduction has a satisfactory proof theory of classical
propositional logic, as shown in Section 8.6, but equally satisfactory classical rules
of natural deduction for the full language of predicate logic have not been found.


A UNIFORM LOGICAL CALCULUS
Modifications in sequent calculus can bring it closer to natural deduction, but
one would also like to relate the two approaches to structural proof theory in a
more direct manner. There are some more general ways of viewing proof the-
ory based on semantical considerations. Constructive type theory formalizes the
computational semantics of intuitionistic logic and goes beyond the division of
proof theory into systems of natural deduction and sequent calculus.
   In this last section, we suggest a syntactic approach to unifying proof theory
through a logical calculus, the rules of which contain as particular instances the
rules of sequent calculus and natural deduction. The rules of the logical calculus to
be presented can be described as the obvious formulation of a "multiple conclusion
natural deduction calculus with general logical rules, written in sequent calculus
style." By general logical rules is meant a formulation with general elimination
rules and their dual general introduction rules. As indicated, the rules of natural
214                                   CONCLUSION

deduction in sequent calculus style as well as the rules of sequent calculus itself, in
single succedent and multisuccedent versions, will come out as instances. Further,
the inverses of the sequent calculus rules will be instances.
   In the rules of the uniform calculus, denoted by MG, contexts will be treated
as multisets. Gentzen's original single-arrow notation for the formal derivability
relation is used to distinguish it from the turnstile we have occasionally used when
reasoning about derivations in natural deduction and from the double arrow of
sequent calculus. In the logical rules, the major premiss is the sequent with the
connective. The other premisses are minor premisses. Rules that display multiple
occurrences A m , Bn of formulas have instances for any m, n ^ 0. We show only
the propositional rules.
                                            MG
Rule of assumption:
A^    A
Logical rules:
A&B, r -> A       r - > A', Am                 A",
                                                                  & /
                                  7    r/
             r, r ,r" -> A ,A , , A
                                                 r   —>•          A, A&5                , r r -* A'
                            7    m
                                                                         r,r- -> A , A'
A v 5 , T -> A     r-  -> A ,A
           r,r-   -> A , A'
                                r -+ A , A v i i .Am,    A!    Bn, r" -> A"
                                                          f
                                            r, H, -> A , A , A"
                    Am , r r -•> A
           r, r--> A , A'
                                r -> A , A :                 I          •> A ' , ^      r" -*•   A"

                                               r j r, i                 -^ A , ZV, A"
                                                           1 /7




General introduction rules are formulated in perfect symmetry to the general
elimination rules. From the calculus it is clear that the rule for falsity is a logical
elimination rule, a fact confounded in sequent calculi when _L =^ C is treated as
an axiom on a par with A ^ A.
   The previous definition of normality for natural deduction with general elim-
ination rules is extended to introduction rules also, by requiring that the major
premisses of all rules in a derivation are assumptions. Normalization for the
uniform calculus MG is obtained through a translation to the sequent calculus
GM+Cut: General introduction rules are translated as right rules followed by
                                 CONCLUSION                                 215

a cut and general elimination rules dually as left rules followed by a cut. For
example, rule &/ of the above table is translated as

              n =^ A', Am r" => A", #"
                r\ r" => A', A", A & #         A&#, r ^ A
                              r                         CMf
                          r, r , r " ^ A , A', A"
Other introduction rules have analogous translations. For elimination rules, con-
sider as an example DE. It has the translation

                                  r = > Af,Am     Bn,T" => A"
                                           , F', F" => A', A"
                                                                Cut
                          r, n, r"=^ A, A', A"
Given a derivation in MG, a translation to GM, cut elimination for GM (Corollary
5.2.14), and translation back to MG produces a derivation in which all major
premisses are assumptions. In the translation back, rule i?v, for example, is
translated as follows:

       F=^A,Am,£n        AvB^AvB  r->A,Am,Bn
                   Rv                        W
       V => A,Av B    ~>      F^A,Av5

Other rules are translated similarly, with major premisses in MG rules always
becoming assumptions. We therefore have the

Theorem: A derivation of T —> A in MG can be transformed into a normal
derivation of F* —• A* where F* and A* are multiset reducts of F.

   The uniform calculus is not strongly normalizing, for there are rules that can
be permuted with each other with no end.
   We shall show how to obtain the rules of various logical calculi from the
uniform calculus.

(a) The rules of multisuccedent sequent calculus: To recover the sequent cal-
culus rules, we do the following two things:
1. Find the substitution that makes the major premiss of each rule an assumption.
Thus, for the introduction rules, we set F = 0 and A equal to the principal formula
and the other way around for the elimination rules.
2. Delete the major premiss that has become an assumption, and change the single
arrow to a double one and the introduction rule symbols to right rule symbols and
elimination rule symbols to left rule symbols.
216                               CONCLUSION

The result of the above is the classical multisuccedent sequent calculus GM
of Section 5.2. The standard logical rules of multisuccedent sequent calculus
with independent contexts, the calculus GOc of Section 5.1, are obtained as special
cases, with m, n = 1 in the above rules. Weakening and contraction must be added
as primitive rules.

(b) Single succedent sequent calculus: By restricting in the rules of the uniform
calculus the succedent in each premiss and conclusion to be one formula and
otherwise proceeding as in points 1 and 2 above, we obtain the intuitionistic
sequent calculus GN of Section 5.2. The two right disjunction rules arise quite
naturally from the requirement of a single succedent formula.
    As above, with m, n = 1 and weakening and contraction added, the intuition-
istic single succedent calculus with independent contexts GOi of Section 5.1 is
obtained.

(c) Inverses of sequent calculus rules: The rules of the uniform calculus give
as instances the inverses of the rules of GM, by the following:

1. Find the substitution that makes the minor premisses of each rule assumptions.
2. Delete the minor premisses that have become assumptions, change the single
arrow to a double one, etc.

Introduction rules of MG produce inverses of left rules of GM and elimination
rules inverses of right rules. For obtaining these inverses, the axiom has to be for-
mulated with just one formula and no context. The true reason for our formulation
of the axiom is that it is needed for having uniquely determined first occurrences
of certain formulas in cut elimination procedures, as in Section 5.2. The rule of
falsity elimination has no minor premiss so there is nothing to invert.
   Inverses of GN are obtained by setting the succedent to be empty or just one
formula in the inverses of GM, whichever gives a single succedent rule. Inversions
are produced for all but rule Rv and the first premiss of LD.
   Remarkably, the inverses obtained as instances of the uniform calculus are all
inverses of shared context rules.

(d) Natural deduction: We obtain systems of natural deduction from the uniform
calculus by restricting the succedent in the rules for MG to one formula. Doing just
this will give a system with general introduction and elimination rules, denoted
by NG. Further restrictions lead to systems with general elimination rules only,
and to the usual system in which only disjunction elimination is of the form
of a general rule. The rules of natural deduction with general introduction and
elimination rules are as follows:
                                         CONCLUSION                                               217

                                                    NG
Rule of assumption:
A^       A
Logical rules:
         , r -> c      r7 -
                                                &I
               r, n, r" -> c                    &I
                                                                       r, r -> c
               v 5 , r - > c n-^A v/i                    Av5,r->c              r^#
                                                                                       v/ 2
                    r, n -> c                                  r, n -> c
                                                                             -vE
                                        r, r\ r;/ -^ c
                                                                             A B\ r" -> c
                                        DI
                                        DI                                                        DE
               r, n -* c                                       rr,nn,r"  c c
                                                                     r" -+
                                           r -+ ± ±E
                                           r -* c
The general introduction rules have a more striking look if written in natural
deduction style:
[A&B]                         [A V B]                    [A V B]               [A D B]        [A]

     C         A   B            C         A     T          C       B    r          C          B
                    -&/                       v/i                      V/2                          D/
           c                        c                          c                       c
A comparison with the general elimination rules, as in Section 1.2, displays the
perfect symmetry of general introduction and elimination rules. We can also
express it in words:

          General introduction rules state that if a formula C follows from a
         formula A, then it already follows from the immediate grounds for A;
          general elimination rules state that if C follows from the immediate
          grounds for A, then it already follows from A.
When the major premisses of introduction rules are assumptions and are left un-
written, the usual introduction rules of natural deduction and the general elimina-
tion rules remain. When also the minor premisses of SLE and DE are assumptions
and left unwritten, Gentzen's original rules of natural deduction in sequent calcu-
lus style, a notational variant of the calculus that started structural proof theory,
are obtained.
                                  APPENDIX A


          Simple Type Theory and Categorial Grammar




In this appendix we describe a general framework for functions that are used in
categorial grammars. It is known as simple type theory. Then the grammars for
the languages of propositional and predicate logic are given.


A.I.   SIMPLE TYPE THEORY

We shall use the term type for domains and ranges of functions. Each object
is typed, meaning that it always belongs to some type. There will be some basic
types, upon which the functional hierarchy of simple type theory is built. Arbitrary
types will be denoted by a, /3, y,....    Given two types a and /3, we can form
the type of functions from a to /3, denoted (a)/3. The statement that a is an
object in type a is written as a : a ("declaration of an object a of type a"). To
get started with the formation of types of functions, we declare some basic types.
Given a type of functions (a)P, we can apply a function that is an object of that
type, say / : (a)/3, to obtain as value an object of type /3:

                                  f:(<x)P    a:<*
                                       f(a) : 0                                   (1)
This is the scheme of functional application. (The first premiss looks more
familiar if written in the usual notation in mathematics, / : a -> f3.) In the other
direction, we have a scheme for functional abstraction. It is a way of forming a
function from an expression containing a variable:

                                       [x : a]

                                        b\p
                                    (x)b : (a)P                                  (2)
Assuming an arbitrary object x of type a given, if we are able to construct an object
b of type ft, then (x)b is the functional abstract, an object of type (a)P, where
the parenthesis notation in (x)b indicates the variable over which abstraction is
                                                                                219
220                                APPENDIX A

taken. The square brackets [x : a] are used to indicate that the assumption x : a
is discharged when the functional abstract is formed. A functional abstract is
always applied through substitution: If the value a is given to x, the value of
(x)b applied to a is given by the expression b(a/x), where the notation a/x
indicates substitution of JC by a. Formally, application through substitution is
written as a rule that defines the value of the application of a functional abstract.
A notation expressing definitional equality is needed for this. In general, the
judgment that two objects a and b of a type a are equal is written as a = b : a
("a and b are equal in of"). In /3-conversion, we conclude such an equality from
two premisses:

                                   [x : a]

                                           a:a
                              {(x)b)(a) = b(a/x) : 0                              (3)

Extra parentheses are used to indicate the functional abstract (x)b uniquely; if
merely (x)b(a) is written, it could also be the functional abstract, over JC, of b
applied to a.
   Repeated functional application leads to expressions of the form f{a)... (c)
that we write as f(a,...,   c). Thus functions of several arguments are formally
functions of one argument that have as values other functions.
   Schemes (l)-(3) of functional abstraction, application, and /?-conversion are
the three principles of simple type theory.
   Simple type theory is expressive enough to work as a categorial grammar of
predicate logic. There we have a ground category of individual objects, the
category of propositions, and properties over the category of individual objects,
represented as propositional functions. These take individual objects as argu-
ments and return propositions as values. The category of propositions is denoted
by Prop. "Category" here is a synonym for type.
   Before showing how logical languages are represented through categorial
grammars, we look at propositions that do not have logical structure, namely
those that are atomic propositions from a logical point of view.
   In any discourse, domains of individuals are introduced. In arithmetic, we
have the domain N of natural numbers. Individual objects are introduced by
declarations of the form n : TV; for example, 0 : N introduces the natural number
zero. Next we have propositional functions over N, for example, a function we can
call Even, the category of which is (N)Prop. Thus functional application gives us

                             Even : (N)Prop 12 : N
                                 Even(l2) : Prop
                                   APPENDIX A                                     221

In geometry, we have the two domains Point and Line, and a two-place proposi-
tional function

                            Incident: (Point)(Line)Prop

that gives, by successive application to a : Point and / : Line, the proposition
Incident(a, I) as value. The usual way of expressing this, "point a is incident with
line /," leaves implicit the functional form of the proposition.


A.2.   CATEGORIAL GRAMMAR FOR LOGICAL LANGUAGES

In pure logic, the interest is in logical structure, not in the structure of the basic
building blocks, the atomic propositions. In propositional logic, no structure at
all is given to atomic propositions, but these are introduced just as pure parameters
P, Q, R,..., with the categorizations

                        P : Prop, Q : Prop, R : Prop, . . .

Connectives are functions for forming new propositions out of given ones. We
have the constant function _L, called falsity, for which we simply write _L : Prop.
Next we have negation, with the categorization

                                 Not: (Prop)Prop

The two-place connectives And, Or, and Implies are categorized by

                               And : {Prop)(Prop)Prop
                                 Or : (Prop)(Prop)Prop
                            Implies : (Prop)(Prop)Prop
The use of symbols used to be considered an essential characteristic of logical
languages. We shall need symbols for expressing generality: First we have the
atomic propositions that are denoted symbolically by P, Q, R        Next we have
arbitrary propositions, denoted by A, B, C,      For the rest, the only thing that
matters is the categorization, and symbols serve only to make formulas shorter.
They will be introduced through the following definitional equalities:

                            ~ = Not : (Prop)Prop
                             & = And : (Prop)(Prop)Prop
                              V = Or: (Prop)(Prop)Prop
                          D = Implies : (Prop)(Prop)Prop

Further, the functional structure is hidden by an infix notation and by the dropping
of parentheses, ~ P for ~ ( P ) , A&B for &(A, B), and so on. This will create an
222                                    APPENDIX A

ambiguity not present in the purely functional notation, such as A&B D C that
could be both &(A, D (B, C)) and D (&(A, B), C). We follow the usual con-
vention of writing A&{B D C) for the former and A&B D C for the latter, and in
general, having conjunction and disjunction bind more strongly than implication.
  Equivalence is a defined notion:

                         A DC B = (A D B)&(B D A) : Prop

The definition of negation through implication and falsity is given by

                                   ~ A = A D 1 : Prop

These are somewhat abbreviated notations ("pattern-matching equations").
More formally, if an arbitrary proposition is given by the declaration
A : Prop, functional application of D gives, successively, D (A) : (Prop)Prop and
D (A, _L) : Prop. Negation is the one-place defined connective ~ = (A) D (A, _L) :
(Prop)Prop, where the first A in parentheses indicates functional abstraction over
A in D (A, _L). Then, by ^-conversion, we get for the negation of a proposition B



   Given an arbitrary proposition A, it is either the constant proposition _L, an
atomic proposition, or (the value of) conjunction, disjunction, or implication. The
notation often used in categorial grammar is

                          A := _L | P | A&B | A V B \ A D B

   By the method of functional abstraction, propositions can be presented as
values of constant functions from any type to the type Prop. For example, given a
type a with x : a, we can abstract vacuously over x in ± to obtain (jt)_L : (a)Prop.
The rule of /3-conversion gives trivially the value J_ to applications of the constant
function (JC)_L; we always have ((x)±)(a) = _L : Prop, as there is no place in _L
to substitute a value of x.
   We can put predicate logic into the framework of simple type theory if we
assume for simplicity that we deal with just one domain V. The objects, individ-
ual constants, are denoted by a, b, c,.... Instead of the propositional constants
P, Q, R,..., atomic propositions can be values of propositional functions over
D, thus categorized as P : (V)Prop, Q : (T>)(T>)Prop, and so on. Next we have
individual variables JC, y, z , . . . taking values in V.1 Following the usual cus-
tom, we permit free variables in propositions. Propositions with free variables


    ^n traditional terminology, we can think of the constants as the "given" objects, thought of
as fixed in value, and of the variables as the "sought," as when a and b are assumed given, and
a value is sought for x such that the condition ax + b = 0 is fulfilled.
                                  APPENDIX A                                   223

are understood as propositions under assumptions, say, if A : (V)Prop, then
A(x) : Prop under the assumption x : V. Terms t,u,v,...      are either individual
parameters or variables. The language of predicate logic is obtained by adding to
propositional logic the quantifiers Every and Some, with the categorizations

                             Every : ((V)Prop)Prop
                              Some : ((V)Prop)Prop

These are relative to a given domain V. Thus, for each domain V, a quantifier
over that domain is a function that takes as argument a one-place propositional
function A : (V)Prop and gives as value a proposition, here either Every(A) or
Some(A). The symbolic notation for quantifiers is given in the definitions

                           V = Every : {{V)Prop)Prop
                            3 = Some : ((V)Prop)Prop

The usual way of writing quantified propositions is either Wx A and 3x A or Wx A (x)
and 3xA(x). In the latter, the expression A(x) does not stand for the application
of A to x, but just mentions the quantified variable.
    For greater generality, we can consider the domain a parameter that can be var-
ied. Each domain V is a set, or belongs to the type of sets, formally V : Set. Simple
type theory is not expressive enough for the categorization of bounded quantifiers
that take as first argument a set V that acts as the domain, then a propositional
function A : (V)Prop depending on that set, and give as value a proposition, either
V(£>, A) or 3(X>, A). These propositions have convenient variable-free readings, in
the style of the Aristotelian syllogisms: all D's are A, some Vis A. With bounded
quantifiers, we have in use any number of domains of individuals. The set over
which a quantifier ranges can be indicated by a notation such as (VJC : V)A(x).
We can now write propositions such as (VJC : Line)(3y : Point)Incident(y, x).
    When logical languages are defined through categorial grammars, quantifiers
always apply to one-place propositional functions, but not to arbitrary formu-
las. If we have, say, B : (V){V)Prop and a : V, then B(a) : (V)Prop, and we
get in the usual notation VxB(a) which looks uncommon, instead of the func-
tional notation V(D, B(a)). A writing with free variables displayed would be
B(x, y) : Prop, and functional abstraction over y gives (y)B(x, y) : (D)Prop, so
we have Vx(y)B(x, v). Since we permit free variables in propositions, we can
write WxB(x, y), provided that we have made the assumption y : V.
    In general, from the purely functional notation V(A), where A : (V)Prop, we
see that two quantified propositions must be set equal if they differ only in the
symbol used for the quantified variable. This can be effected in two ways: The
first is to have an explicit rule of a-conversion that permits renaming variables
bound by a quantifier. The second way is to build a-conversion into a logical
224                               APPENDIX A

system by a suitable formulation of the rules of inference for quantifiers, as in
Section 4.1.


NOTES TO APPENDIX A

Functional abstraction, found by Alonzo Church in the 1930s, formalizes the common
notion of a function as an expression with a variable. The application of a function
consists of a substitution, and the computation of values of a function consists of
steps of /?-conversion, until no such conversion applies. None of these concepts,
abstraction, application, and computation of values of a function, is recognized by
the set-theoretical notion of a function. Thus the appreciation of Church's work as
one of the most important contributions to foundations of mathematics has been slow
in coming.
   The early work of Church is found in his (1940) and in the monograph The
Calculi of Lambda-Conversion, 1941. The impact of Church's A-calculus in logic
and computer science is described in Barendregt (1997). The definition of the lan-
guage of predicate logic through type theory and categorial grammar is treated in
detail in Ranta (1994).
                                   APPENDIX B


           Proof Theory and Constructive Type Theory




In this second appendix, we shall first introduce lower-level type theory, and then
show how it can be used for the semantical justification of the rules of natural
deduction. Next we introduce higher-level type theory, then show by an example
how mathematical theories can be represented formally as type systems.


B.I.   LOWER-LEVEL TYPE THEORY

We start with a type of propositions, designated Prop. Propositions are thought of
as their sets of formal proofs, in accordance with the propositions-as-sets princi-
ple. For each kind of proposition, there will be rules of formation, introduction,
elimination, and computation. The rules operate on assertions or, as one often
says, judgments, of which there are four kinds. Prop and Set are considered syn-
onyms, and we use whatever terminology is appropriate in a situation, logical or
set-theoretical:

   A : Prop, A : Set,   A is a proposition, A is a set,
   a : A,               a is a proof of proposition A, a is an element of set A,
   a = b : A,           a and b are equal elements of set A,
   A = B : Set,         A and B are equal sets.

To emphasize the formal character of a proof a of a proposition A, it is often
called a proof-object or also a proof term. We also call them simply objects, a
word that can equally well mean the element of a set. The equality of two objects
in the judgment a = b : A is definitional. There will be two general rules for the
definitional equality of objects:
                                       a = c :A b = c : A
                        a = a :A            a=b: A
The first, premissless rule expresses the reflexivity and the second the transitivity
of the definitional equality of two objects. In these rules, the premisses include that
A : Set, a : A, b : A, etc., but we do not write these out. Let us derive symmetry
                                                                                  225
226                                     APPENDIX B

of definitional equality from the above rules: Assume b — a : A. By reflexivity,
a = a : A, and therefore, by transitivity, a = b : A. Thus definitional equality of
objects in a given set is an equivalence relation in that set.
   Similarly to the equality of objects, there will be general rules for the equality
of sets:
                                           A = C :Set B = C : Set
                      A = A: Set                 A = B : Set

Symmetry follows as in the case of equality of objects.
   Dependent types are families of sets indexed by a set: If B(x) is a set whenever
x : A, we can form the product type (x : A)B. The notation is a generalization
of that of simple type theory. In the latter, with B a constant type, we write
(A)B for the function type. Thus we can also call (x : A)B a dependent function
type. Connected to dependent types, we have hypothetical judgments, or judg-
ments in a context, of all the four forms of judgment of type theory. Contexts
are progressive lists of variable declarations. We now stipulate that A is a set
in the context x\ : A\, x2 : A 2 , . . . , xn : An if A(a,\/x\,..., an/xn) is a set when-
ever a\ : Ai,a2 : A2(ai/xi),...,        an : An(ai/x\,...,      an-\/xn-\).   Similarly, x : A
in the contextx\ : A\, x2 : A 2 , . . . , xn : An \ix(a\,... ,an) : A ( a i / * i , . . . , an/xn)
whenever ax : Ai, a2 : A 2 (fli/*i),..., an : A w (fli/.xi,..., an-\/xn-{).
    In type theory, it is usual to give the rules for forming propositions as explicit
syntactical rules. The rules for propositional logic are

      A : Prop B : Prop             A : Prop B : Prop              A : Prop B : Prop
          AScB : Prop                  A V B : Pro/?                   ADB:

The rules for quantified propositions are

                                    [x : A]                        [x : A]

                     A : Prop B : Prop              A : Prop B : Pro/?
                      (VJC : A)£ : Pro/?             (3* : A)£ : Pro/?

To these we add the zero-premiss rule J_ : Prop.
   For each form of proposition, we have a function constant that gives as values
objects of that set, called the constructor. Then we have selectors, functions that
operate on the set. The constructor for conjunction introduction is a function, to
be called pair, operating on proofs a of A and b of B, to give as value pair(a, b)
a proof of A&B, with the rule notation

                                       a:A         b:B
                                    pair(a,b) : A&B
                                       APPENDIX B                             227

The constructors for disjunction introduction are

                          a: A           T              b :B
                      i(a) : A v B                  j(b) : A v B

The constructors / and j are the "canonical injections" into the "disjoint union"
Av B.
The constructor for implication introduction is

                                        [x : A]

                                         b:B


For conjunction elimination, we have the two rules with selectors

                         c : ASLB                   C:    A&B
                                       &E                         2


The functions p and q are the projections of the "product" AScB.
For disjunction, we have the elimination rule, where (x)d and (y)e are obtained
by functional abstraction as in Appendix A,

                                            [x:A]         [y:B]

                         c: A V B          d:C       e :C         ^
                               VE(C,   (x)d, (y)e) : C

Thus the selector VE is a function that takes as arguments an arbitrary proof c of
A V B, a function (x)J that converts arbitrary proofs of A into proofs of C, and
a function (y)e that converts arbitrary proofs of B into proofs of C. The value of
WE is a proof of C.
For implication, we have

                                c : AD B            a'.   ADE
                                   ap(c, a) : B

The quantifier introduction rules with constructors are

                     [x : A]

                          B                     a : A b : B(a/x)
               (Xx)b : (VJC : A)B              pair(a, b) : (3x :
228                                 APPENDIX B

The corresponding elimination rule for universal quantification is
                               c : Qfx : A)B a : A
                                 ap(c, a) : B(a/x)

For existential quantification, there are two rules:
                     c : (3x : A)B             c : (3JC :
                        p(c) : A 3 £ l       9 (c) : B(p(c)/x)   ^
To the introduction and elimination rules we add a rule corresponding to falsity
elimination:


                                  e/?(c) : C(C/JC)
The rule is more general than the corresponding rule in propositional logic because
of the possible dependence of C on the proof-object of the premiss. The quantifier
rules are almost the same as the rules for implication and conjunction: The only
difference is that, in the latter two, B is a constant proposition. Indeed, the rules for
implication are special cases of the rules for universal quantification and similarly
for conjunction and existence. Thus it is sufficient to have the quantifier rules and
the rules for disjunction and falsity.
    If in the above rules we hide all the proof-objects, we are back to the usual
rules of natural deduction.
    The rules of type theory have judgments or assertions as premisses and as
conclusion. In Chapter 1, we used a turnstile notation \- A for emphasizing that
rules of inference act on assertions, not propositions. The assertion h A is what
remains from a : A when the proof-object is deleted. Lower-level type theory can
be seen as a formalization of the computational semantics of intuitionistic logic,
and we see that the type-theoretical rules make the rules of natural deduction valid
under this semantics.
    In Dummett's constructive semantics, meaning is explained in terms of proof.
A proof of an implication A D B is a function that converts an arbitrary proof of
A into some proof of B. Thus, to explain what a proof of A D B is, we would
have to accept the notion of an arbitrary proof. To avoid the circularity of this
explanation, Dummett (1975) distinguished direct or canonical and indirect or
noncanonical proofs and required that the semantical explanations for the latter
reduce to those for the former. In type theory, a canonical proof-object is one that
is of the form of a constructor, and a noncanonical is one of the form of a selector.
The requirement is, in these terms, that noncanonical objects must always convert
to canonical ones. The conversions are made explicit in computation rules, also
called equality rules, that is, rules that prescribe how the values of selectors are
computed into canonical form:
                                      APPENDIX B                                                                                      229

The computation rules for conjunction are
                  a: A b:B          o                a: A b: B
              p(pair(a, b)) = a : A               q(pair(a, b)) = b : B
The computation rules for disjunction are
                [x:A]        [y:B]                                                     [x : A] [y : B]

       a :A             C     e:C        Veq
                                                           b: B                            d:C                   e:C                  Veq
                                                   /   "   •   /   '   T   \   /   '   \   T   /   '   \   \     / 1   i   \   S~*1
 vE(i(a), (x)d, (y)e) = d(a/x) : C             vE(j(b), (x)d, (y)e) = e(b/y): C
Finally, the computation rule for implication is
                                        [x : A]

                                        b: B
                              ap((Xx)b, a) = b(a/x) : B• Deq
The computation rules for the quantifiers are just like the rules for implication
and conjunction, with a dependent type in place of the constant type B. The
computation of a noncanonical expression proceeds outside-in and corresponds
exactly to the detour conversion of natural deduction derivations as in Section 8.5;
for example, the last computation rule above corresponds to converting an intro-
duction of implication followed by elimination.
   In order to explain the notion of an arbitrary proof, it is essential that the
conversion of a noncanonical expression terminate in a finite number of steps in
a unique canonical form. This was shown by Martin-Lof (1975).
   Similarly to natural deduction with general elimination rules, we can give
general elimination rules for conjunction and implication in type theory:
                            [x:AUy:B]                                                                          [y : B]

          c : A&B        d :C                   c : AD B a: A d : C
           &E(c, (x)(y)d) : C                        gap(c, a, (y)d) : C
The selectors &E and gap are computed by the equalities
                    &E(pair(a, b), (x)(y)d) = d(a/x, b/y) : C
                        gap((Xx)b, a, (y)d) = d(b(a/x)/y)                                      : C
The selectors in the special elimination rules for conjunction can be defined:
           p(c) = &E(c, (x)(y)x) : A              q(c) = &E(C, (x)(y)y) : B
Similarly, the selector corresponding to modus ponens has the definition
                              ap(c, a) = gap(c, a, (y)y) : B
230                               APPENDIX B

The rule of universal elimination has analogous general and special rules in type
theory.


B.2.   HIGHER-LEVEL TYPE THEORY

Simple type theory was briefly presented in Section A.I. Its generalization by
dependent types results in higher-level type theory. A dependent type is a family
of types parametrized by another type. The objects of a dependent type are func-
tions over the parameter type such that the range of the function depends on the
argument. More formally, /3 is a dependent type over a if a is a type and ft is a
type whenever an object x : a is given. The family of dependent types is written
as (x : a)/3. In the case of dependent typing, the notation for typings of functions
has to display the dependency, here the variable x acting as argument, and this
is achieved by generalizing the scheme of functional abstraction of simple type
theory into
                                       [x : a]

                                       b p
                                  (x)b : (x : a)0                                (1)
We write fi(x) for a type in the context x : a. We can consider the notation (a)/3
of simple type theory as an abbreviation of (x : a)fi when /3 is a constant type.
The scheme of functional application becomes
                                f:(x:a)P          a:a
                                    f(a) : p(a/x)                                (2)
Functions formed by abstraction are applied by the rule of ^-conversion:
                                  [x : a]

                                          a:a
                                     = b(a/x) : p(a/x)                           (3)
   In lower-level type theory, we added proof-objects to predicate logic and gave
rules of formation, introduction, elimination, and computation separately for each
logical operation. With higher-level type theory, these rules come out as instances
of the general schemes of functional application and ^-conversion.
   Higher-level type theory works as a general framework for categorial gram-
mars. In the case of logical languages, the connectives are categorized as in sim-
ple type theory, but the categorization of bounded quantifiers requires dependent
typing:

        V : (A : Set)(B : (A)Prop)Prop,     3 : (A : Set)(B : (A)Prop)Prop
                                    APPENDIX B                                    231

The quantifiers are functions that take as arguments a set A, a propositional
function B over A (that is, a property of objects of A), and give as value a
proposition V(A, B) or 3(A, B). Proof-objects for the introduction of universally
quantified propositions have the categorization

                 X : (A : Set)(B : (A)Pwp)((x : A)B(x))V(A,       B)

Here the proof-object for the third argument, of type (x : A)B(x), is left out by
the convention about constant types. Also, since B is a propositional function
over A, it must be written out that it is applied to x : A with the proposition B(x)
as value. By the typing, k is a function that takes as arguments, in turn, a set A, a
propositional function B over A, and a function that transforms any proof a : A
into a proof of B(a), and gives as value a proof of V(A, B). For the special case
of B constant over A, we have

                  A : (A : Pwp)(fl : Prop)((A)B)Implies(A,       B)

Written as a rule, A-abstraction looks very much like the rule for functional
abstraction. The difference is that Implies(A, B) is a set with a constructor A,
whereas {pt)fi is a type that does not need to have a constructor. This is also
reflected in the order of the rules. For ^-abstraction, the rule for the constructor is
given first, and then the selector rule is justified by the conversion rule. In general
functional abstraction, instead, the application rule comes first in conceptual order.
(See Ranta 1994, p. 166, for detailed explanation.)
   For the introduction of the existential quantifier, we have the categorization

                pair : (A : Set)(B : (A)Pwp)(x : A)(B(x))3(A,         B)

It is usual not to write out the type arguments A and B of pair, but to take
it as a function in a context A : Set, B : (A)Prop. Thus the value is written as
pair(a, b) instead of pair(A, B,a,b). Since all objects have to be typed, the first
two arguments in the latter can be read off from a and b.
The selectors have the categorizations

               ap : (A : Set)(B : (A)Prop)(V(A, B))(a : A)B{a)
                p:(A:     Set)(B : (A)Prop)(3(A,     B))A
                 q : (A : Set)(B : (A)Pwp)(3(A,     B))B(p(A,    B, c))

The third argument of p is c : 3(A, B). The categorizations for implication and
conjunction are special cases. For disjunction introduction, we have

                        i : (A : Prop)(B : Pmp)(A)Or(A,     B)
                        j : (A : Prop){B : Prop)(B)Or(A, B)
232                                APPENDIX B

The categorization of the elimination rule has to be written on two lines:

  WE : (A : Prop)(B : Pwp)(C : (Or(A, B))Prop)
         (c : Or(A, B))((a : A)C(i(A, B, a)))((b : B)C(j(A,       B, b)))C(c)

The general elimination rules for universal and existential quantification are typed
analogously.
   The computation rules are definitional equalities showing how selectors act on
constructors. We show only the selectors corresponding to the special elimination
rules. The computation rule for universal quantification concludes the equality

                      ap(A, B, A(A, B, c), a) = c(a) : B(a)
The computation rules for existential quantification give
                        p(A, B,pair(A, B,a,b)) = a : A
                        q(A, B,pair(A, B, a,b)) = b: B
For disjunction, we have two computation rules with the equalities
              VE(A, B, C, i(A, B, a), d, e) = d(a) : C(i(A, B, a))
              VE(A, B, C, j(A, B, b), d, e) = e(b) : C(j(A, B, b))


B.3.   TYPE SYSTEMS

Type theory has a reading as a constructive set theory, with the basic form of
assertion a : A read as: a is an element of the set A. Conjunction corresponds to
the intersection and disjunction to the (disjoint) union of two sets, and universal
quantification to the Cartesian product of a family of sets, existential quantification
to the direct sum of a family of sets.
   Another reading of type theory is that types A, B, C , . . . express problems to be
solved, in particular, specifications of programming problems. Then objects can
be interpreted as programs and the basic form of assertion a : A as the statement
that program a meets the specification A. In traditional programming languages,
there is no formal way of expressing program specifications. In traditional logical
languages, there is no formal way of expressing proofs, but type theory unites
these two. The effect on programming methodology is that the correctness of a
program becomes a formally well-defined property of correct typing.
   Higher-level type theory offers a general framework for defining type systems,
not limited to predicate logic. As a simple example, let us consider a type system
for elementary geometry (compare also the example from Section 6.6(e)). We
declare the basic sets of points and lines by Pt: Set, Ln : Set. Next we declare
the basic relations of distinct points, distinct lines, and apartness of a point from
                                     APPENDIX B                                       233

a line, with some obvious abbreviations to make the declarations fit a line. Also,
since Prop is a constant type, the arguments in x : Pt,... are left out:

        DiPt: (Pt)(Pt)Prop, DiLn : (Ln)(Ln)Prop, Apt:              (Pt)(Ln)Pwp

The reason for using distinct instead of equal points and lines as basic relations
is that the construction of connecting lines and intersection points requires con-
ditions expressed by dependent typing. These two geometrical constructions are
introduced by the declarations

     In: (a: Pt)(b : Pt)(DiPt(a, b))Ln,       pt: (/ : Ln)(m : Ln)(DiLn(l, m))Pt

The usual geometrical axioms are: There is a unique connecting line for any two
distinct points, and the points are incident with the line. There is a unique inter-
section point for any two distinct lines, and the point is incident with both lines,
where incidence is defined as the negation of apartness. The incidences are ex-
pressed by the propositions Inc(a, ln(a, b)), Inc(b, ln(a, b)), Inc(pt(l, m), /), and
Inc(pt(l, m), m) but these are well-formed only if the conditions in the construc-
tions are verified. Thus we have a simple case of dependent typing going beyond
the expressive means of usual predicate logic. Looking at the typings of the two
constructions, we notice that they both have three arguments, the connecting line
construction two points a and b and a proof, say w, of DiPt{a, b). Thus functional
application gives us ln(a, b, w) : Ln in the context a : Pt, b : Pt, w : DiPt(a, b).
   In type theory, the incidence properties of constructed objects are implemented
by declaring function constants that prove these properties:

            inc-lnl : (a : Pt)(b : Pt)(w : DiPt(a, b))Inc(a, ln(a, b, w))
            inc-ln2 : (a : Pt)(b : Pt)(w : DiPt(a, b))Inc(b, ln(a, b, w))

The uniqueness of connecting lines can be formalized by

uni-ln : (a : Pt)(b : Pt)(w : DiPt(a, b))(l : Ln)(Inc(a, l))(Inc(b, l))EqLn(l, ln(a, b, w))

where equality of lines is defined as negation of DiLn. For a complete formaliza-
tion, the axiomatic properties of the basic relations have to be given, as well as
principles that permit the substitution of equal objects in the basic relations, as in
Section 6.6.
   When a theory is formalized as a type system, computer implementations of
type theory, known as proof editors, can be used for the formal development of
proofs. Such proof editors are interactive systems of proof and program develop-
ment, in which each step is checked for correctness through the type-checker,
which is the heart of the computer implementation. A formally verified proof can
be seen as a program that converts whatever is needed to verify the assumptions of
a theorem into what is claimed in the theorem. In terms of programming problems,
234                                 APPENDIX B

a formally verified proof converts the data of a problem into its solution. This
is particularly clear in geometrical problems: Each problem has some "given"
objects with assumed properties, and the solution-program transforms these into
the "sought" objects with required properties. The effect of constructivity is that
such programs are provably terminating.


NOTES TO APPENDIX B

Type theory as understood here was developed by Martin-Lof on the basis of ideas
such as dependent typing and proof-objects (also found in de Bruijn 1970) and the
propositions-as-sets principle or "Curry-Howard isomorphism" in Howard (1969).
An early exposition is Martin-Lof (1975). The lower-level theory is explained in the
booklet Martin-Lof (1984). The rules he gives for propositional equality permit the
conclusion of a definitional equality from propositional equality which turned out to
be erroneous. This is corrected in later expositions of type theory, such as Nordstrom,
Petersson, and Smith (1990) and Ranta (1994).
   The use of type theory as a programming system with the possibility of program
verification was explained in Martin-Lof (1982). Actual computer implementation
benefitted from the introduction of the efficient higher-level notation developed by
Martin-Lof since 1985 on the basis of the calculus of constructions of Coquand and
Huet (1988). A concise exposition, with applications to logic and linguistics, is given
in Ranta (1994). The example of formalization of elementary geometry as a type
system comes from von Plato (1995).
                                   APPENDIX C


         PESCA - A Proof Editor for Sequent Calculus
                                          by
                                  AARNE RANTA
                              aarne@cs.Chalmers.se




PESCA is a program that helps in the construction of proofs in sequent calcu-
lus. It works both as a proof editor and as an automatic theorem prover. Proofs
constructed in PESCA can both be seen on the terminal and printed into ETjnX
files. The user of PESCA can choose among different versions of classical and
intuitionistic propositional and predicate calculi and extend them by systems of
nonlogical axioms. The aim of this appendix is to show what PESCA can be
used for, as well as to give an outline of its implementation, which is written
in the functional programming language Haskell. PESCA is a simple and small
program, and extending it by implementing various calculi and algorithms of this
book can provide instructive student projects on a level more advanced than the
mere use of the editor.


C.I.   INTRODUCTION

It was already realized by Gentzen that sequent calculus is not very natural for
humans actually to write proofs. It carries around a lot of information that humans
tend to keep in their heads rather than to put on paper. Although greatly improving
the performance of machines operating on proofs, this information easily obscures
the human inspection of them, and actually writing sequent calculus proofs in full
detail is tedious and error prone. Thus it is obviously a task for which a machine
can be helpful.
   The domain of sequent calculi allows for indefinitely many variations, which
are not due to disagreements on what should be provable but to different decisions
on the fine structure of proofs. In terms of provability, it is usually enough to tell
whether a calculus is intuitionistic or classical. In the properties of proof structure,
there are many more choices. The very implementation of PESCA precludes most
of them, but it still leaves room for different calculi, only some of which are
included in the basic distribution. These calculi can be characterized as having:

                   Shared multiset contexts, no structural rules.

                                                                                   235
236                               APPENDIX C

However, calculi can have a single formula as well as several formulas in the
succedents of their sequents.
   The fundamental common property of the calculi treated by PESCA is top-
down determinacy:

         Given a conclusion and a rule, the premisses are determined.

This property is essential for our method of top-down proof search. The user of
PESCA starts with a conclusion and then tries to refine it by suggesting a rule.
If the rule is applicable, the proof of the conclusion is completed by the derived
premisses, and the proof search can continue from them. A branch in a proof is
successfully terminated when a rule gives an empty list of premisses. A branch
fails if no rule applies to it. This simple procedure, which has been adopted
from the proof editor ALF (Magnusson 1994) for the much richer formalism
of constructive type theory, is not applicable to calculi that are not top-down
determinate.
    The term top-down runs counter to the standard typographical layout of proof
trees, in which premisses appear above conclusions. The term is frequent in
computer science, where it may come from the standard layout of syntax trees,
in which the root is above the trees. In proof theory, the confusion is usually
avoided by saying "root-first" instead. There will be slight notational differences
as compared to earlier chapters.


C.2. TWO EXAMPLE SESSIONS
(a) A proof in propositional calculus: Let us first construct a proof of the law
of commutativity for disjunction, in the sequent form,

                                Ay B ^          By   A.

Having started PESCA, we see its prompt | -. We then enter a new goal by the
command n followed by the sequent written in ASCII notation:

   |- n A v B      =>   BvA

The reply of PESCA is a new proof tree, consisting of the conclusion alone,
which is the only subgoal of the tree. Subgoals are identified by sequences of
digits starting from the root, as in the following example:
                               111        112
                                        121
                                     11  12 13
                                       1
The command s shows the current subgoals, of which we still have just one,
numbered 1. More interestingly, the command a shows the applicable rules for
                                   APPENDIX C                                    237

a given subgoal. In the situation where we are in our proof, we have

   |- a 1

   r 1 Al SI Lv - - A v B => B v A
   r 1 Al SI Rvl - - A v B => B v A
   r 1 Al SI Rv2 - - A v B => B v A

Any of the displayed r commands (line segments preceding - - ) can be cut and
pasted to a command line, and it gives rise to a refinement of the subgoal, an ex-
tension of the tree that is determined by the chosen rule. For instance, choosing the
first alternative takes us to a proof by the left disjunction rule from two premisses,

   | - r 1 Al SI Lv

   A => B v A        B => B v A

   A v B => B v A

As will be explained below, the part Al S I specifies the active formulas in the
antecedent and the succedent; when the first formulas are chosen, as here, this
part could be omitted, as in the next refinement,

   | - r 11 Rv2

   A => A

   A = > B v A       B => B v A

   A v B => B v A

The left branch 111 can now be refined by rule ax, which does not generate any
more subgoals:

   | - r 111 ax

The right branch 12 can be refined analogously with 11, by Rvl followed by
ax. When the proof is ready, its ASCII appearance is usually not of very good
quality. Now, at last, it is rewarding to use the command

   I- 1
238                               APPENDIX C

to write the current proof into a ET]HX document, which looks like


                                                     BvA
                                                                      Lv

when processed.
  Finally,
   |- d
shows the proof translated into natural deduction:

                                    1                1
                                    A                B
                         ass.           • v/2   T;       7   v/
                                                                  i
                        Av B      By A          Bv A
                                         ;                    v£,U
                                  Bv A
(b) A proof in predicate calculus: In predicate calculus, one more command is
usually needed than in propositional calculus: the command i for instantiating
parameters. Logically, a parameter such as t in the existential introduction rule R3
                                   T =• A(t/x)
                                   T => (3x)A
is just like another premiss, which calls for a construction to be complete. This
logic is made explicit in the H introduction rule of Martin-Lof 's type theory and
simplifies greatly the implementation of inference rules. Here, staying faithful to
the syntax of predicate calculus, we have to treat such parameters as hidden pre-
misses in the rules. Thus a proof that has uninstantiated parameters is incomplete
in the same way as a proof that has open subgoals.
    Let us prove the quantifier switch law;

                                C(jc, y) => (Vx)(3y)C(x, y).
After introducing the goal, we make a couple of ordinary refinements:
   | - n (/Ey)(/Ax)C(x,y) => (/Ax)(/Ey)C(x,y)
   |- r 1 Al SI R/A
   |- r 11 L/E
   |- r 111 Al SI R/E
The last refinement introduces a parameter t, which we instantiate by y:

   |- i t y
                                    APPENDIX C                                  239

Continuing by L/A, x, and ax, we obtain a complete proof, in which we have
afterward marked next to the rule symbols the two instantiations made:


                             (Wx)C(x, y) => C(x, y)
                           (Wx)C(x, y) =» (3y)C(x, y) y
                        (3y)(Vx)C(x, y) =»• (3y)C(x, y) LB
                      (3y)(Vx)C(x, y) =• (Vjt)Oy)C(jc, y ) '


C.3.   SOME COMMANDS

Some PESCA commands were already exemplified in the two sessions of the pre-
vious section. This section will give a synopsis of them, as well as explain a couple
of other commands. For the full set of commands, we refer to the electronically
distributed manual.
    Each command consists of one character followed by zero or more arguments,
some of which may be optional. In the following, as in the on-line help file of
PESCA, the arguments are denoted by words indicating their types. Optional
arguments are enclosed in brackets. Typewriter font is used for terminal symbols.
    To understand the commands fully, one should know that a PESCA session
takes place in an environment which changes as a function of the commands.
The environment consists of a current calculus and a current proof. In the
beginning, the calculus is the intuitionistic predicate calculus G3i, and the proof
is the one consisting of the impossible empty sequent =>>.

   r goal [A int] [S int] rule (refine)

replaces the goal by an application of the rule, if applicable, and leaves the cur-
rent proof unchanged otherwise. The goal is denoted by a sequence of digits, as
explained in the previous section. The options [A int] [S int] reset the active
formulas in the antecedent and the succedent of the goal - by default, the active
formula is number 1, which in the antecedent is the first and in the succedent
the last printed formula. If the number exceeds the length, resetting the active
formula has no effect.

   i parameter term (instantiate)

replaces all occurrences of the parameter in the current proof by the term.

   t goal int (try to refine)

replaces the goal by the first proof that it finds by recursively trying to apply
all rules maximally int times. This is the automatic proof search method of
PESCA, based on brute force but always terminating. With certain calculi, such
240                                APPENDIX C

as G4ip, this method always finds a proof after a predictable number of steps.
With predicate calculus rules that require instantiations, the method usually fails.

   n sequent (new)

replaces the current proof by a proof consisting of the given sequent which there-
by becomes its open subgoal number 1.

   u subtree (undo)

replaces the subtree by a goal consisting of the conclusion of the subtree. Subtrees
are identified by sequences of digits in the same way as subgoals: Subtree n is
the tree, the root node of which is the node n.

   s (show subgoals)

shows all open subgoals. If the system responds by showing nothing, the current
proof is complete.

   a goal (applicable rules)

shows all refinement commands applicable to the goal,

   c calculus (change calculus)

changes the current calculus. The help command ? shows available calculi. As a
calculus is just a set of rules, calculi can be unioned by the operation +. Thus the
command c G3 c + Geq selects classical predicate calculus with equality.

   x file (read axioms)

reads a file with nonlogical axioms, parses it into rules, adds the rules into the
current calculus, and writes the rules into a file.

   1 [file] (print proof in a ETEX file)

prints the current proof in ETjnX format in the indicated file. To process
file, the style file p r o o f . s t y (Tatsuta 1990) is needed.

   d [file] (print proof in natural deduction in a ETjnX file)

prints the current proof in ETjnX format in the indicated file. It works for G3i and
G3ip only.
   All ET]nX-producing commands also call the system to run ETgX and then
create the xdvi image on the background.
                                   APPENDIX C                                    241

C.4.   AXIOM FILES

Certain kinds of formulas can be interpreted as sequent calculus rules that preserve
the possibility of cut elimination and are hence favorable for proof search. These
formulas are implications with conjunctions of atoms on their left-hand sides and
disjunctions of atoms on their right-hand sides. Either side can be empty. An empty
left-hand side is represented by the omission of the implication sign. An empty
right-hand side is represented by the absurdity _L. Alternatively, the negation of a
left-hand side is interpreted as its implication of absurdity. All those variables that
occur on the right-hand side but not on the left-hand side are treated as parameters.
    As an example, consider a set of axioms for the theory of lattices. What the
user of PESCA types into afilelooks as follows:
   - - s t a r t s h e a d e r . Text above header i s sent t o l a t e x
   as such.
   Mtl   (a \wedge b) \leq a
   Mtr   (a \wedge b) \leq b
   Jnl   a \leq (a \vee b)
   Jnr   b \leq (a \vee b)
   Unimt c \leq a & c \leq b -> c \leq (a \wedge b)
   Unijn a \leq c & b \leq c -> (a \vee b) \leq c
   Ref   a \leq a
   Trans a \leq b & b \leq c -> a \leq c

The command x makes PESCA read thefileand construct a set of sequent calculus
rules. These rule are also printed in ETjnX:
                               a Ab < a,Y =>> A
                                                       Mtl
                                        r=^ A
                               a Ab <b,F => A
                                                       Mtr

                               a < aV b, T ^ A
                                                       M
                                 " r^A
                               b < a V b, T =
                                                   - Jnr


                                                                 Unimt
                                          :—
                            c < a,c < b,
                      awb<c, a < c, b < c, T                 A
                                                                 Unijn
                          a <c, b <c,
                                b       TA

                              c , a b , b c , V ^ A
                                  ;—;          =   :         Trans
                            a <b,b <c, T=^A
242                               APPENDIX C

C.5. ON THE IMPLEMENTATION

The full source code of PESCA is approximately 1400 lines of Haskell code,
divided into nine modules.

(a) Abstract syntax. The central module is the one defining an abstract syntax
of sequents, formulas, singular terms, proofs, etc. On the level of abstract syntax,
all these expressions are Haskell data objects, which could also be called syntax
trees. With the exception of the communication with the user, PESCA always
operates on syntax trees. There are lots of operations defined by pattern match-
ing on the basic types of syntax trees: Sequent, Formula, Term, Proof,
AbsRule.
    The definition that expresses the top-down determinacy of PESCA (see Section
C. 1) is the definition of the type of abstract inference rules:

   type AbsRule = Sequent -> Maybe [Either Sequent Ident]

A rule is a function that takes a conclusion sequent as its argument and returns
either a list of premisses or a failure. Returning an empty list of premisses means
that the proof of the conclusion is complete. The premisses can be either se-
quents or parameter identifiers. (It was already argued, in Section C.2 above, that
parameters are really premisses.)
    Sequents are treated as pairs of multisets of formulas. The definition of the
type of sequents is as pairs of lists rather than multisets: The multiset aspect is
implicit in various functions that consider variants of these lists obtained when
one formula in turn is made the active formula. In most cases, this is enough, and
it is not necessary to consider all permutations.
    Some calculi restrict the succedents of sequents to be single formulas. PESCA
does not use a distinct type for these calculi: It simply is the property of certain
calculi, such as G3ip, that the rules never require or produce multisuccedent
sequents.
(b) Parsing and printing. In user input and PESCA output, syntax trees are
represented by strings of characters. The relation between syntax trees and strings
is defined by the parsing and printing. Parsing follows the top-down combinator
method explained in Wadler (1985). The printing functions produce terminal
output for PESCA sessions as well as ETJHX to be written into files.
(c) Predefined calculi. Some intuitionistic and classical calculi are defined di-
rectly as sets of abstract rules. Because abstract rules are functions, they cannot
be read from separate files at runtime, but must be compiled into PESCA. Also
considered was a special syntax that could be used for reading calculi from files,
but finally this was restricted to nonlogical axioms: There is, after all, so much
                                   APPENDIX C                                       243

variation and irregularity in the rules, that the syntax and the operations on it
become complicated and are not guaranteed to cope with "arbitrary sequent cal-
culus rules." However, to experiment with new calculi, it is enough to edit one
file.
(d) Interaction - refinement and proof search. The central proof search func-
tions are refinement, instantiation, undoing, and automatic search. All of these
operations are based on the underlying operation of replacing a subtree by another
tree,
   r e p l a c e : : Proof -> [Int] -> Proof -> Proof
where lists of integers denote subtrees. Another underlying operation is to list all
those rules of a calculus that apply to a given sequent,
   applicableRules :: AbsCalculus -> Sequent ->
                      [((Ident,AbsRule) , [Either Sequent Ident])]

Automatic proving calls this function in performing top-down proof search, fol-
lowing the methods of Wadler (1985), just like parsing.
(e) Natural deduction. This translates proofs in calculi G3i and G3ip into natural
deduction. This would easily extend to G4i and G4ip, but this and the more
demanding other calculi are left as an exercise.
(f) Dialogue and command language. The dialogue is based on monadic input
and output. While commands are executed in an environment of a current calculus
and a current proof, they produce output to the screen and files and change the
environment.


NOTES TO APPENDIX C
PESCA is an experimental system still under development. Contributions and bug
reports are thus welcome.

ELECTRONIC REFERENCES
Haskell home page, h t t p : //www.haskell . o r g /
PESCA home page, h t t p : //www. cs . Chalmers . s e / ~ a a r n e / p e s c a /
M. Tatsuta (1990) proof . s t y (Proof Figure Macros), ErgX style file.
Home page of this book, h t t p : / / p r o o f theory . h e l s i n k i . f i
                                  Bibliography




Artin, E. (1957) Geometric Algebra, Wiley, New York.
Balbes, R. and P. Dwinger (1974) Distributive Lattices, University of Missouri Press,
  Columbia, Missouri.
Barendregt, H. (1997) The impact of the lambda calculus in logic and in computer
   science, The Bulletin of Symbolic Logic, vol. 2, pp. 181-215.
Bernays, P. (1945) Review of Ketonen (1944), The Journal of Symbolic Logic,
  vol. 10, pp. 127-130.
Beth, E. (1959) The Foundations of Mathematics, North-Holland, Amsterdam.
Bishop, E. and D. Bridges (1985) Constructive Analysis, Springer, Berlin,
de Bruijn, N. (1970) The mathematical language AUTOMATH, its usage and some of
  its extensions, as reprinted in R. Nederpelt et al., eds, Selected Papers on Automath,
  pp. 73-100, North-Holland, Amsterdam.
Buss, S. (1998) Introduction to proof theory, in S. Buss, ed, Handbook of Proof
   Theory, pp. 1-78, North-Holland, Amsterdam.
Church, A. (1940) A formulation of the simple theory of types, The Journal of
  Symbolic Logic, vol. 5, pp. 56-68.
Church, A. (1941) The Calculi of Lambda-Conversion, Princeton University Press.
Coquand, T. and G. Huet (1988) The calculus of constructions, Information and
   Computation, vol. 76, pp. 95-120.
Curry, H. (1963) Foundations of Mathematical Logic, as republished by Dover, New
   York, 1977.
van Dalen, D. (1986) Intuitionistic logic, in D. Gabbay and F. Guenthner, eds,
  Handbook of Philosophical Logic, vol. 3, pp. 225-339, Reidel, Dordrecht,
van Dalen, D. (1994) Logic and Structure, Springer, Berlin,
van Dalen, D. and R. Statman (1979) Equality in the presence of apartness, in J.
   Hintikka et al., eds, Essays in Mathematical and Philosophical Logic, pp. 95-116,
   Reidel, Dordrecht.
Dragalin, A. (1988) Mathematical Intuitionism: Introduction to Proof Theory,
   American Mathematical Society, Providence, Rhode Island.
Dummett, M. (1959) A propositional calculus with denumerable matrix, The Journal
   of Symbolic Logic, vol. 24, pp. 96-107.


                                                                                   245
246                              BIBLIOGRAPHY

Dummett, M. (1975) The philosophical basis of intuitionistic logic, as reprinted in
  M. Dummett, Truth & Other Enigmas, pp. 215-247, Duckworth, London, 1978.
Dummett, M. (1977) Elements of Intuitionism, Oxford University Press.
Dyckhoff, R. (1992) Contraction-free sequent calculi for intuitionistic logic, The
  Journal of Symbolic Logic, vol. 57, pp. 795-807.
Dyckhoff, R. (1997) Dragalin's proof of cut-admissibility for the intuitionistic se-
  quent calculi G3i and G3i', Research Report CS/97/8, Computer Science Division,
  St Andrews University.
Dyckhoff, R. (1999) A deterministic terminating sequent calculus for Godel-Dummett
  logic, Logic Journal of the IGPL, vol. 7, pp. 319-326.
Dyckhoff, R. and S. Negri (2000) Admissibility of structural rules in contraction-free
  sequent calculi, The Journal of Symbolic Logic, vol. 65, pp. 1499-1518.
Dyckhoff, R. and S. Negri (2001) Admissibility of structural rules for extensions of
  contraction-free sequent calculi, Logic Journal of the IGPL, in press.
Dyckhoff, R. and L. Pinto (1998) Cut-elimination and a permutation-free sequent
  calculus for intuitionistic logic, Studia Logica, vol. 60, pp. 107-118.
Ekman, J. (1998) Propositions in propositional logic provable only by indirect proofs,
  Mathematical Logic Quarterly, vol. 44, pp. 69-91.
Feferman, S. (2000) Highlights in proof theory, in V. Hendricks et al., eds, Proof
  Theory: History and Philosophical Significance, pp. 11-31, Kluwer, Dordrecht.
Gentzen, G. (1932) Ueber die Existenz unabhangiger Axiomensysteme zu un-
  endlichen Satzsystemen, Mathematische Annalen, vol. 107, pp. 329-350.
Gentzen, G. (1934-35) Untersuchungen iiber das logische Schliessen, Mathematische
  Zeitschrift, vol. 39, pp. 176-210 and 405^31.
Gentzen, G. (1936) Die Widerspruchsfreiheit der reinen Zahlentheorie, Mathemati-
  sche Annalen, vol. 112, pp. 493-565.
Gentzen, G. (1938) Neue Fassung des Widerspruchsfreiheitsbeweises fur die
  reine Zahlentheorie, Forschungen zur Logik und zur Grundlegung der exakten
  Wissenschaften, vol. 4, pp. 19^4.
Gentzen, G. (1969) The Collected Papers of Gerhard Gentzen, M. Szabo, ed, North-
  Holland, Amsterdam.
Girard, J.-Y. (1987) Proof Theory and Logical Complexity, Bibliopolis, Naples.
Godel, K. (1931) On formally undecidable propositions of Principia mathematica
  and related systems I (English translation of German original), in van Heijenoort
  (1967), pp. 596-617.
Godel, K. (1932) Zum intuitionistischen Aussagenkalkiil, as reprinted in Godel's
  Collected Works, vol. 1, pp. 222-225, Oxford University Press 1986.
Godel, K. (1941) In what sense is intuitionistic logic constructive?, a lecture first
  published in Godel's Collected Works, vol. 3, pp. 189-200, Oxford University
  Press 1995.
Gordeev, L. (1987) On cut elimination in the presence of Peirce rule, Archiv fur
  mathematische Logik, vol. 26, pp. 147-164.
Gornemann, S. (1971) A logic stronger than intuitionism, The Journal of Symbolic
  Logic, vol. 36, pp. 249-261.
                                 BIBLIOGRAPHY                                      247

Hallnas, L. and P. Schroeder-Heister (1990) A proof-theoretic approach to logic
  programming. I. Clauses as rules, Journal of Logic and Computation, vol. 1,
  pp. 261-283.
Harrop, R. (1960) Concerning formulas of the type A -> B v C, A -> (Ex)B(x) in
  intuitionistic formal systems, The Journal of Symbolic Logic, vol. 25, pp. 27-32.
van Heijenoort, J., ed, (1967) From Frege to Godel, A Source Book in Mathematical
  Logic, 1879-1931, Harvard University Press.
Herbelin, H. (1995) A A-calculus structure isomorphic to Gentzen-style sequent cal-
  culus structure, Lecture Notes in Computer Science, vol. 933, pp. 61-75.
Hertz, P. (1929) Ueber Axiomensysteme fur Beliebige Satzsysteme, Mathematische
  Annalen, vol. 101, pp. 457-514.
Hilbert, D. (1904) On the foundations of logic and arithmetic (English translation of
  German original), in van Heijenoort (1967), pp. 129-138.
Howard, W. (1969) The formulae-as-types notion of construction, published in 1980
  in J. Seldin and J. Hindley, eds, To H. B. Curry: Essays on Combinatory Logic,
  Lambda Calculus and Formalism, pp. 480-^4-90, Academic Press, New York.
Hudelmaier, J. (1992) Bounds for cut elimination in intuitionistic propositional logic,
  Archive for Mathematical Logic, vol. 31, pp. 331-354.
Joachimski, F. and R. Matthes (2001) Short proofs of normalization for the simply
  typed A-calculus, permutative conversions, and Godel's T, Archive for Mathemat-
  ical Logic, vol. 40, in press.
Ketonen, O. (1941) Predikaattikalkyylin taydellisyydesta (On the completeness of
  predicate calculus), Ajatus, vol. 10, pp. 77-92.
Ketonen, O. (1943) "Luonnollisen paattelyn" kalkyylista (On the calculus of "natural
  deduction"), Ajatus, vol. 12, pp. 128-140.
Ketonen, O. (1944) Untersuchungen zum Prddikatenkalkul (Annales Acad. Sci. Fenn.
  Ser. A.I. 23), Helsinki.
Kleene, S. (1952), Introduction to Metamathematics, North-Holland, Amsterdam.
Kleene, S. (1952a) Permutability of inferences in Gentzen's calculi LK and LJ, Mem-
  oirs of the American Mathematical Society, No. 10, pp. 1-26.
Kleene, S. (1967), Mathematical Logic, Wiley, New York.
Kolmogorov, A. (1925) On the principle of excluded middle (English translation of
  Russian original), in van Heijenoort (1967), pp. 416^-37.
Magnusson, L. (1994) The Implementation ofALF-a Proof Editor Based on Martin-
  Lof's Monomorphic Type Theory With Explicit Substitution, PhD thesis, Depart-
  ment of Computing Science, Chalmers University of Technology, Gothenburg.
Martin-Lof, P. (1975) An intuitionistic theory of types: predicative part, in H. Rose and
  J. Shepherson, eds, Logic Colloquium '73, pp. 73-118, North-Holland, Amsterdam.
Martin-Lof, P. (1982) Constructive mathematics and computer programming, in L.
  Cohen et al., eds, Logic, Methodology and Philosophy of Science IV, pp. 153-175,
  North-Holland, Amsterdam.
Martin-Lof, P. (1984) Intuitionistic Type Theory, Bibliopolis, Naples.
Martin-Lof, P. (1985) On the meanings of the logical constants and the justifications
  of the logical laws, in Atti degli Incontri di Logica Matematica, vol. 2, pp. 203-281,
248                              BIBLIOGRAPHY

  Dipartimento di Matematica, Universita di Siena. Republished in Nordic Journal
  of Philosophical Logic, vol. 1 (1996), pp. 11-60.
Menzler-Trott, E. (2001) Gentzens Problem: Mathematische Logik im nationasozial-
  istischen Deutschland, Birkhauser, Basel.
Mints, G. (1993) A normal form for logical derivation implying one for arithmetic
  derivations, Annals of Pure and Applied Logic, vol. 62, pp. 65-79.
Mostowski, A. (1965) Thirty Years of Foundational Studies, Societas Philosophica
  Fennica, Helsinki. Also in Mostowski's collected works, vol. 1.
Negri, S. (1999) Sequent calculus proof theory of intuitionistic apartness and order
  relations, Archive for Mathematical Logic, vol. 38, pp. 521-547.
Negri, S. (1999a) A sequent calculus for constructive ordered fields, in U. Berger
  et al., eds, Reuniting the Antipodes - Constructive and Nonstandard Views of the
  Continuum, Kluwer, Dordrecht, in press.
Negri, S. (2000) Natural deduction and normal form for intuitionistic linear logic, to
  appear.
Negri, S. and J. von Plato (1998) Cut elimination in the presence of axioms, The
  Bulletin of Symbolic Logic, vol. 4, pp. 418-435.
Negri, S. and J. von Plato (1998a) From Kripke models to algebraic countervaluations,
  in H. de Swart, ed, Automated Reasoning with Analytic Tableaux and Related
  Methods, pp. 247-261 (LNAI, vol. 1397), Springer, Berlin.
Negri, S. and J. von Plato (2001) Sequent calculus in natural deduction style, The
  Journal of Symbolic Logic, vol. 66, in press.
Nishimura, I. (1960) On formulas of one variable in intuitionistic propositional cal-
  culus, The Journal of Symbolic Logic, vol. 25, pp. 327-331.
Nordstrom, B., K. Petersson and J. Smith (1990) Programming in Martin-Lof's Type
  Theory: An Introduction, Oxford University Press,
von Plato, J. (1995) The axioms of constructive geometry, Annals of Pure and Applied
  Logic, vol. 76, pp. 169-200.
von Plato, J. (1998) Natural deduction with general elimination rules, Archive for
  Mathematical Logic, in press.
von Plato, J. (1998a) Proof theory of full classical propositional logic, ms.
von Plato, J. (1998b) A structural proof theory of geometry, ms.
von Plato, J. (2000) A problem of normal form in natural deduction, Mathematical
  Logic Quarterly, vol. 46, pp. 121-124.
von Plato, J. (2001) A proof of Gentzen's Hauptsatz without multicut, Archive for
  Mathematical Logic, vol. 40, pp. 9-18.
Pottinger, G. (1977) Normalization as a homomorphic image of cut-elimination,
  Annals of Mathematical Logic, vol. 12, pp. 323-357.
Prawitz, D. (1965) Natural Deduction: A Proof-Theoretical Study. Almqvist &
  Wicksell, Stockholm.
Prawitz, D. (1971) Ideas and results in proof theory, in J. Fenstad, ed, Proceedings of
  the Second Scandinavian Logic Symposium, pp. 235-308, North-Holland.
Ranta, A. (1994) Type-Theoretical Grammar, Oxford University Press.
                                 BIBLIOGRAPHY                                    249

Rieger, L. (1949) On the lattice theory of Brouwerian propositional logic, Acta Fac-
  ultatis Rerum Nat. Univ. Carol, vol. 189, pp. 1-40.
Schroeder-Heister, P. (1984) A natural extension of natural deduction, The Journal
  of Symbolic Logic, vol. 49, pp. 1284-1300.
Schiitte, K. (1950) Schlussweisen-Kalkiile der Pradikatenlogik, Mathematische
  Annalen, vol. 122, pp. 47-65.
Schiitte, K. (1956) Ein System des verkniipfenden Schliessens, Archivfiir mathema-
  tische Logik und Grundlagenforschung, vol. 2, pp. 55-67.
Sonobe, O. (1975) A Gentzen-type formulation of some intermediate propositional
  logics, Journal of the Tsuda College, vol. 7, pp. 7-13.
Stalmarck, G. (1991) Normalization theorems for full first order classical natural
  deduction, The Journal of Symbolic Logic, vol. 56, pp. 129-149.
Takeuti, G. (1987) Proof Theory, 2nd ed, North-Holland, Amsterdam.
Tennant, N. (1978) Natural Logic, Edinburgh University Press.
Troelstra, A. and D. van Dalen (1988) Constructivism in Mathematics, 2 vols., North-
  Holland, Amsterdam.
Troelstra, A. and H. Schwichtenberg (1996) Basic Proof Theory, Cambridge Univer-
  sity Press.
Uesu, T. (1984) An axiomatization of the apartness fragment of the theory DLO +
  of dense linear order, in Logic Colloquium '84, pp. 453-475 (Lecture Notes in
  Mathematics, vol. 1104), Springer, Berlin.
Ungar, A. (1992) Normalization, Cut Elimination, and the Theory of Proofs, CSLI
  Lecture Notes No. 28.
Vorob'ev, N. (1970) A new algorithm for derivability in the constructive propositional
  calculus, American Mathematical Society Translations, vol. 94, pp. 37-71.
Wadler, P. (1985) How to replace failure by a list of successes, Proceedings of
   Conference on Functional Programming Languages and Computer Architecture,
  pp. 113-128 (Lecture Notes in Computer Science, vol. 201), Springer, Berlin.
Zucker, J. (1974) Cut-elimination and normalization, Annals of Mathematical Logic,
  vol. 7, pp. 1-112.
                                  Author Index




A                                        G
Artin,E. 151                             Gentzen, G. xi, xii, xiii, xv, xvi, 10, 14,
                                           19, 22, 23, 24, 29, 34, 47, 48, 51, 52,
B                                          57, 58, 60, 66, 86, 88, 98, 100, 107,
                                           115, 134, 138, 159, 160, 166, 177, 178,
Balbes, R. 164                             183, 184, 185, 186, 208, 212, 213, 214,
Barendregt, H. 224                         217, 235
Bernays, P. 60, 160                      Girard, J.-Y. 21
Beth, E. 86                              Glivenko, V. xv, xvi, 76, 77,
Bishop, E. 46                              117,119
Bridges, D. 46                           Godel, K. xi, xii, 13n, 22, 156,
de Bruijn, N. 234                          160, 164
Buss, S. 155                             Gordeev, L. 209
                                         Gornemann, S. 164

Church, A. 224                           H
Coquand, T. 234                          Hallnas, L. 209
Curry, H. 60, 207, 234                   Harrop,R. 41, 145
                                         Herbelin, H. 208
D                                        Herbrand, J. 76, 141, 142, 143
                                         Hertz, P 212
van Dalen, D. xiv, 46, 164, 209          Heyting,A. 5, 107, 115
Dragalin, A. xii, 29, 46, 86, 108, 125   Hilbert, D. xi, xii, 22, 24,
Dummett, M. 13n, 23, 24, 43, 157, 160,     57, 166,
  161, 164, 228                          Howard, W. 207, 234
Dyckhoff, R. 46, 122, 123, 124, 125,     Hudelmaier, J. 122, 125
  164, 208                               Huet, G. 234
Dwinger, P. 164

E
                                         Joachimski, F. 201,208
Ekman, J. 194, 208
Euclid, xvii, 142, 152                   K
                                         Ketonen, O. xii, xvi, 19, 29, 60,
                                           86, 155
Feferman, S. 24                          Kleene, S. xii, 14n, 19, 29, 46, 86,
Frege, G. 2, 3                             122, 130

                                                                                  251
252                                  AUTHOR INDEX

Kolmogorov, A. 5, 160
Konig, D. 82, 86
                                           Schroeder-Heister, P. 24, 209
                                           Schiitte, K. 60,61,86
M
                                           Schwichtenberg, H. 24, 46, 86, 138
Magnusson, L. 236                          Smith, J. 234
Martin-Lof, P. 13n, 23, 152, 208, 229,     Sonobe, O. 161
 234, 238                                  Stalmark, G. 204
Matthes,R. 201,208                         Statman, R. 209
Menzler-Trott, E. 24                       Szabo, M. 86
Mints, G. 202
Mostowski, A. 14n
                                           Takeuti, G. 86
N
                                           Tatsuta, M. 240, 243
Nishimura, I. 164                          Tennant, N. 24, 208
Nordstrom, B. 234                          Troelstra, A. xii, 24, 29, 46, 86,

P                                          U
Peano, G. 3                                Uesu, T. 155
Peirce, C. 43, 121, 209                    Ungar, A. 24
Petersson, K. 234
Pinto, L. 208                              V
Poincare, H. 27, 46
                                           Vorob'ev, N. 125
Pottinger, G. 208
Prawitz, D. xvi, 24, 48, 66, 160, 192,     XA7
   194, 197, 204, 208                       W
                                           Wadler, P. 242
R
Rieger, L. 164                              Z
Russell, B. 3, 27, 46, 194                  Zucker, J. 208
                                     Subject Index




Pages containing definitions of concepts are sometimes indicated by italics.

                                                     decidability 60, 141, 144
                                                     proof search for, 50
abstraction, 219, 224, 230
                                                  closure
active formula, 10, 14, 15, 29, 98
                                                  closure condition, 130, 139, 141
admissible rule, 20, 30
                                                     under cut, 18
a-conversion, xvi, 62, 67, 223
                                                     under substitution, 171
analysis, 22, 46
                                                  completeness, 18
apartness, 25, 143, 144, 150, 152, 209
                                                     predicate logic, xvi, 81, 86
   decidable, 144
                                                     propositional, xvi, 58, 60, 119
   disjunction property for, 145
                                                  compulsory discharge, 10
application
                                                  computability, xii, 25
   functional, 219, 224, 230
                                                  computation, 5, 13, 224, 228, 232
   generalized, 208, 229
                                                  computer science, xii, 3, 224
arithmetic, xi, 22, 115, 134                      conditions, 150, 152
assertion, 3, 6, 13, 225, 228                     confluence, 213
assumption, 4, 6, 8, 9, 13, 15, 16, 17, 47,
                                                  conservativity, xvii, 139-141, 147, 148, 154
      99, 166
                                                  consistency, 20, 21, 22, 41, 76, 119, 137, 148
assumption label, 167
                                                  constructive, xv, 25, 27, 66, 146
axiom of parallels, 152, 153
                                                  constructive type theory, xii, 5, 13, 23, 152,
axiomatic proof theory, xi
                                                        208, 213, 225-234, 236
axiomatic systems, xv, 3, 4, 22, 41,
                                                  constructor, 226
      129, 156
                                                  context, 15, 29, 135
                                                     additive, 15n
B                                                    independent, xW, 15, 19, 87-108, 211
basic sequent, 134                                   multiplicative, 15n
^-conversion, 220, 224, 230                          shared, 15, 19, 40, 60
                                                  contraction, xvi, 17, 29, 98, 130, 144, 146,
                                                        165, 175-179, 183, 185, 211, 212
                                                     height-preserving, 33, 53, 71, 75, 109,
canonical, 13, 228                                      116, 121, 124, 131
case, 47                                             meaning of, 18, 98, 165, 175-179,
   empty, 48                                            183,212
categorial grammar, xiv, 1, 23, 221-224, 230      conversion, 7, 8, 9, 13, 65, 66, 99, 224, 228
chain rule, 213                                      detour, 9, 99, 189-192, 229
classical logic, 12, 19, 21, 22, 24, 26, 47-60,      permutation, 192-194
     66, 67, 78, 81, 156, 158, 160, 202-207          simplification, 194-196

                                                                                           253
254                                 SUBJECT INDEX

conversion formula, 185                        excluded middle, xvi, 12, 24, 26, 27, 43, 48,
Curry-Howard, 207, 234                              114-121,160,202-207
cut, 18, 29, 34, 98, 100, 102, 134, 136,         weak, 23, 43, 157, 158, 160
      138, 172, 184, 189,211,212               exercises, xv
  detour, 185                                  existence, 27, 64, 66, 151
  hereditary, 102, 106, 195                    existence property, 76, 143
  meaning of, 189                              extended Hauptsatz, 138
  nonprincipal, 165, 185
  permutation, 185
  principal, 185
  redundant, 101, 189                          falsity, 2, 8, 28, 30, 175, 197, 214,
  shared-context, 40                                 221
  simultaneous, 212                            field theory, 152, 155
  vacuous, 195                                 formal language, 3
cut elimination, 35, 54, 72, 75, 91, 97, 101   formalization, xiii, 4
      102, 105, 110, 117, 121, 124, 132,       formula, 1,27,62
      134, 138, 163, 202, 208                     active, 15, 29
                                                  compound, 1
cut-height, 35
                                                  conversion, 185
                                                  Harrop,41, 145
D                                                 inactive, 176
denotational, xv, 47                              prime, 1
dependent types, 151, 226, 230                    principal, 15, 29
derivability, 4, 5, 14, 47, 48, 165,171           °P e n ' 6 2
derivation, 5, 30,167-170                         regular, 128
   branch, 196                                    trace, 51, 128
   height, 30, 171                                true, 33
                                                  used
   hypothetical, 8                                     ' " ' 173
   non-normal, 172, 187, 189                      weight, 30, 67, 123
   normal 175 183,214                          formulas-as-types, see propositions-as-sets
detour conversion, 9, 99, 189-192, 229         function, xiii, 2, 219, 224, 230
direct proof, 5, 13
discharge, 4, 10, 98, 166, 220                 G
   compulsory, 10                              general elimination rules, xiv, xvi, xvii,
   multiple, 11, 18, 98, 165,171,175, 183               2 3 , 64, 86, 166, 192, 208, 211-213,
   unique 11,167                                         217 229
   vacuous, 11,17, 98, 165,171,175, 183,       g e n e r a l m t r o d u c t i o n rules, 213, 217
      196 2 1 2
         '                                     generalized application, 208, 229
discharge label, 167                           geometry, 22, 150, 232
disjunction property, 20, 22, 41, 43, 145      Glivenko's theorem, xv, xvi, 11, 119
double negation, 26, 43, 48, 66, 160
Dummett logic, 23, 157, 160-164                R

                                               Harrop's theorem, xvi, 41, 145
E
                                               Haskell, xv, 235, 242
equality, 26, 138, 143, 145, 209               height of derivation, 30
  decidable, 144, 207                          height-preserving, 31, 34
  definitional, 220, 225, 232                  Herbrand disjunction, 76
  predicate logic with, xvii, 138-141          Herbrand's theorem, 142
equivalence, 2, 222                            Hey ting algebra, 156
Euclid's fifth postulate, 152, 153             Hey ting arithmetic, 115
exchange rules, 14, 29                         Hilbert's program, 22, 24, 57
                                       SUBJECT INDEX                                          255

I                                                   N
impredicative, 28                                   negation, 2, 29, 52, 221, 222
incompleteness, xi, 22                              noncanonical, 13, 228
inconsistent, 20,137                                nonconstructive, 82
indirect proof, 12, 24, 26, 48, 66, 115, 158,       nonlogical axiom, 133
      160, 204                                      normal form, xvii, 9,175, 183, 192, 197,
infix, 3, 221                                            198, 204, 205, 214
intermediate logic, 22, 156-164                     normal thread, 196
intuitionism, 25, 46                                normalization, 9, 189, 195, 198-201,
intuitionistic logic, xiv, 12, 19, 21, 25-46, 66,        212,214
      67, 76, 78, 156, 160, 164, 198, 206, 207        strong, 201, 208, 213
inversion lemma, 32, 46, 71, 75, 109,
      115,121
inversion principle, xiv, xv, xvi, 6, 24, 65,       O
      86, 166                                       open assumption, 9, 47
invertible rules, 19, 33, 34, 49, 60, 90,           open case, 47
      96, 216                                       operational, 5, 47, 48, 87, 115
                                                    order
                                                      linear, 145, 164
K
                                                      nondegenerate, 147
Konig's lemma, 82                                     partial, 146
                                                    ordinal proof theory, xi


label, 166
lattice theory, 147-150, 241                        Peirce'slaw, 121,208
leaf 127                                            permutation, 34, 98, 100, 102, 165,
linear logic, 125                                        183,208
lists, 14                                           permutation conversion, 192-194
logical axiom, 16                                   permutation cut, 185
logical languages, xiii, 1-3                        PESCA, 179, 235-243
logical systems, 1-5                                predicative, 27, 46
loop, 43, 121                                       prenex form, 78
                                                    program correctness, 232, 234
                                                    program specification, xiii, 232
M                                                   programming languages, xiii, 1, 3, 232
major premiss, 6, 171                               proof editor, xiii, xv, 179, 233, 235
meaning, xiv, 5, 23, 26, 64, 166,                   proof search, xv, 15, 16, 17, 19, 20, 43, 50,
     212, 228                                            60, 121,211,236,239
midsequent, 80                                      proof term, 13, 201, 208, 225
minimal logic, 12, 198, 206, 207                    proof-object, 13, 208, 225-234
minor premiss, 8, 171                               proper assumption, 201
mix rule, xvi, 212                                  proposition, 2, 3, 13
models, 22, 42, 43, 156                             propositional function, 220
modus ponens, 9, 41, 184, 198,                      propositions-as-sets, 13, 28, 207, 225
     208, 229
multicut, xvi, 88, 186,212
multiple conclusion, 47, 213
multiset, 15, 18                                    quantifiers, 64-67, 86, 121, 191, 223, 226,
multiset reduct, 99, 100, 177,                          227,228,230,231
     191, 206                                         second-order, 28
256                                SUBJECT INDEX

R
real numbers, 25-28, 46                         term, 61, 223
reductio, 12, 27                                   closed, 62
reduction tree, 82                                 open, 62
reductive proof theory, xii                     thinning, 17
refutability, 58, 81                            thread, 196
regular                                            normal 196
   formula, 128                                 trace formula, 51, 128
   normal form, 128                             true formula, 33
   sequent, 51, 127,209                         type systems, 13, 232-234
replacement rule, 138                           type theory, xiii
rules of inference, 3-5                            constructive, xii, 5, 13, 23, 152, 208, 213,
   duality of, 49                                     225-234, 236
rule-scheme, 130                                   higher-level, 230-232
Russell's paradox, 27, 194                         lower-level, 225-230
                                                   simple, 219-221, 230
S
second-order logic, 28                          U
selector, 208, 226                              unprovability, xii, xv, 20, 43, 76, 78, 122, 201
set theory, 27, 224, 225, 232                   use, 99, 173
simple type theory, 219-221, 230                  multiple, 100
simplification conversion, 194-196                vacuous, 99
soundness, 59, 81
special elimination rules, 9, 166, 184, 193,
      208, 229
                                                validity, xvi, 58, 60, 81
split, 26, 144, 146, 150
                                                valuation, 58, 81, 164
stable logic, 66, 158-160
                                                variable, 222
strong normalization, 10, 201, 208
                                                  bound, 62
structural rules, 17, 18
                                                  free, 62, 222
   meaning of, 18, 98, 165, 175-179, 183,
                                                  fresh, 62
       189,212
                                                variable restriction, 64, 65, 67, 99
subformula property, xvi, 76, 156
   in natural deduction, 9, 183, 196-197, 206
                                                W
   in sequent calculus, 15, 19, 20, 22, 23,
      40,76,98, 104, 106, 115, 119,             weakening, xvi, 11, 17, 29, 98, 165,
       120, 136                                      175-179,183,211,212
   weak, 20, 22                                   height-preserving, 31, 53, 70, 75, 109,
substitution, 18, 62, 63, 68, 148, 151, 171,         116, 121, 123, 131
       172, 220                                   meaning of, 18, 98, 165, 175-179,
substitution lemma, xvi, 68, 108                     183,212
                          Index of Logical Systems




NOMENCLATURE

The letter G stands for sequent systems (Gentzen systems):
GO-systems have independent contexts in two-premiss rules.
G3-systems have shared contexts in two-premiss rules.
p stands for the propositional part of a system.
i stands for an intuitionistic system.
c stands for a classical system.
m stands for a multisuccedent system.
G4ip is obtained from G3ip by changing the left implication rules.
Extension of a system by Rule is indicated through writing -{-Rule.
A superscript * denotes an arbitrary extension.

The letter N indicates natural deduction style:
GN is a sequent system in natural deduction style.
GM is the corresponding multisuccedent system.
NG is natural deduction in sequent style.
MG is the corresponding multisuccedent system.


TABLES OF RULES

GOi                                                                    89
GOc                                                                    95
G3ip                                                                   28
G3cp                                                                   49
G3i                                                                    67
G3c                                                                    67
G3ipm                                                                 108
G3im                                                                  108
G3LC                                                                  162
G4ip                                                                  122
GN                                                                     99
GM                                                                    106
NG                                                                    217
MG                                                                    214



                                                                      257

