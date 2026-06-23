# Structural Proof Theory — Chapter 2: Intuitionistic Sequent Calculus and Cut Elimination (lines 1553-2599)

2.1. CONSTRUCTIVE REASONING

Intuitionistic logic, and intuitionism more generally, used to be philosophically
motivated, but today the grounds for using intuitionistic logic can be completely
neutral philosophically. Intuitionistic or constructive reasoning, which are the
same thing, systematically supports computability: If the initial data in a problem
or theorem are computable and if one reasons constructively, logic will never
make one committed to an infinite computation. Classical logic, instead, does
not make the distinction between the computable and the noncomputable. We
illustrate these phenomena by an example:
    A mathematical colleague comes with an algorithm for generating a decimal
expansion O.aia2a3..., and also gives a proof that if none of the decimals at is
greater than zero, a contradiction follows. Then you are asked to find the first
decimal ak such that ak > 0. But you are out of luck in this task, for several hours
and days of computation bring forth only 0's
    Given two real numbers a and b, if it happens to be true that they are equal, a
and b would have to be computed to infinite precision to verify a = b. Obviously
the truth of the proposition a = b is not continuous in its two arguments; to see this,
think of a and b as points on the real line, assume that a = b is true, and then
"move" one of the points just a bit. In a constructive approach, we start with
the relation of apartness, or distinctness, of two real numbers, written as a ^ b.
Apartness can be proved by showing that the difference \a — b\ has a positive

                                                                                   25
26                     STRUCTURAL PROOF THEORY

lower bound. This time the proposition is continuous in its arguments: a finite
computation can verify a / b.
   What are the axioms of an apartness relation? First, irreflexivity; call it API:
     API.   ~ a ^ a.
Second, assume a ^ b, and take any third number c. If you are unable to decide
whether a ^ c, it must be the case that b ^ c, and similarly with deciding b / c.
This property, the splitting of the apartness a / b into two cases a ^ c and b / c,
is the second axiom:
     AP2.   a / Z? D a / c v b ^c.
The principle is intuitively very clear if the points a, b, c are depicted geometri-
cally, as points on the real line.
   We now obtain equality as a defined notion:
Definition2.1.1: a = b =        ~a^b.
Thus equality is a negative notion, and an infinitistic one also: To prove a = b, we
have to show how to convert any of the infinitely many a priori possible proofs
of a / b into an impossibility.
   From API we get at once
     EQ1.    a=a,
and from the contraposition of AP2
     EQ2. a = c&b = cD a = b.
Substitution of a for c in AP2 gives a ^ b D a ^ av b ^ a, so by API, b # a
follows from a ^ b. Symmetry of equality is obtained by contraposition. Thus the
negation of an apartness relation is an equivalence relation.
   Let us denote by a the number O.a^as...        of our mathematical colleague.
From the proof that a = 0 leads to a contradiction, ~ a = 0 can be concluded.
However, this proof does not give any lower bound for \a — 0|; thus we have not
concluded a / 0. Logically, the difference is one between ~ ~ a / 0 and a ± 0.
The former says that it is impossible that a is equal to zero, the latter says that a
positively is distinct from zero.
   Classical logic contains the principle of indirect proof: If ~ A leads to a
contradiction, A can be inferred. Axiomatically expressed, this principle is con-
tained in the law of double negation, ~ ~ ADA. The law of excluded middle,
A v ~ A, is a somewhat stronger way of expressing the same principle.
   In constructive logic, the connectives and quantifiers obtain a meaning different
from the one of classical logic in terms of absolute truth. The constructive "BHK
meaning explanations" for propositional logic were given in Section 1.2, and
those for quantifiers will be presented in Section 4.1. One particular feature in
these explanations is that a direct proof of a disjunction consists of a proof of one
of the disjuncts. However, the classical law of excluded middle Av ~ A cannot
           SEQUENT CALCULUS FOR INTUITIONISTIC LOGIC                                 27

be proved in this way, as there is no method of proving any proposition or its
negation. Under the constructive interpretation, the law of excluded middle is not
an empty "tautology," but expresses the decidability of proposition A. Similarly,
a direct proof of an existential proposition 3x A consists of a proof of A for some
a. Classically, we can prove existence indirectly by assuming that there is no x
such that A, then deriving a contradiction, and concluding that such an x exists.
Here the classical law of double negation is used for deriving 3x A from ~ ~ 3x A.
    More generally, the inference pattern, if something leads to a contradiction the
contrary follows, is known as the principle of reductio ad absurdum. Dictionary
definitions of this principle rarely make the distinction into a genuine indirect
proof and a proof of a negative proposition: If A leads to a contradiction, then ~ A
can be inferred. Mathematical and even logical literature are full of examples in
which the latter inference, a special case of a constructive proof of an implication,
is confused with a genuine reductio. A typical example is the proof of irrationality
of a real number x: Assume that x is rational, derive a contradiction, and conclude
that x is irrational. The fallacy in claiming that this is an indirect proof stems from
not realizing that to be an irrational number is a negative property: There do not
exist integers n, m such that x = n/m.
    The effect of constructive reasoning on logic is captured by intuitionistic logic.
From the point of view of classical logic, it is no limitation not to use the law of ex-
cluded middle, or the principle of indirect proof, for the following reason: Given a
formula C, there is a translation giving a formula C* such that C and C* are classi-
cally equivalent and C* is intuitionistically derivable if C is classically derivable.
For example, a disjunction can be translated by (A v #)* = ~ (~ A*& ~ B*). The
translation gives an interpretation of classical logic in intuitionistic logic. Another
intuitionistic interpretation will be given in Chapter 5: For propositional logic, if
a formula C is classically derivable, the formula


where P\,..., Pn are the atoms of C, is intuitionistically derivable. By this trans-
lation, classical propositional logic can be interpreted intuitionistically as a logic
in which the proofs of theorems are relativized to decisions on their atoms.
    The method of interpreting classical logic in intuitionistic logic through a suit-
able translation applies to predicate logic and axiomatic theories formalizable in it,
such as arithmetic. For such theories, constructive reasoning will only apparently
decrease the deductive strength of the theory.
    The essential difference between classical and constructive reasoning concerns
predicativity: The idea, advocated by Poincare and by Russell, is that "anything
involving a totality must not be defined in terms of that totality." Poincare wanted
mathematical objects and structures to be generated from the rock bottom of
natural numbers. In Russell, predicativity was a response to the set-theoretical
paradoxes, particularly Russell's paradox that arises from defining a "set of all
28                       STRUCTURAL PROOF THEORY

sets that are not members of themselves." In this impredicative definition, the
totality of all sets is presupposed. Another traditional example of an impredicative
definition is the definition of the set of real numbers through complete ordered
fields. Impredicativity is met in second-order logic in which quantifiers range
over propositions. With X, Y, Z . . . standing as variables for propositions, we can
form second-order propositions such as (iX)X and (VX)((A D (B D X)) D X).
Assertion of the first proposition means that for any proposition X, it is the case
that X. Then (VX)X must be false in a consistent system, and falsity has a second-
order definition as _L = (WX)X. The rule of falsity elimination becomes a special
case of universal instantiation,



The second example of a second-order proposition defines the proposition A&B,
as can be seen by deriving the rules of conjunction introduction and elimination
from the definition, using only the rules for implication and second-order universal
quantification. Through the propositions-as-sets principle, we see that second-
order quantification amounts to quantification over sets.

2.2.    INTUITIONISTIC SEQUENT CALCULUS

In this section, we present an intuitionistic sequent calculus with the remarkable
property that all structural rules, weakening, contraction, and cut, are admissible
in it. Classical sequent calculi are obtained by removing certain intuitionistic re-
strictions, and admissibility of structural rules carries over to the classical calculi,
as shown in the next chapter. Other extensions of the basic calculus will be studied
in later chapters. Sequents are of the form F =$• C, where F is a finite, possibly
empty, multiset. The rules of the calculus G3ip for intuitionistic propositional
logic are the following:
                                       G3ip
     Logical axiom:
       P, F => P
     Logical rules:

                                                          • /?&
     A&B, F =^                                 A&B
     A i
     /i, r --       ^,      c                      .              r^B       Rv
           A vfl,   r=          T \'
                                       r^Av5      • «Vi    —        •   —    KV2




     AD L?, r =» A       B, F =^ C            A , F => B
           SEQUENT CALCULUS FOR INTUITIONISTIC LOGIC                              29

The axiom is restricted to atomic formulas. It is essential that _L is not considered
an atomic formula, but a zero-place logical operation.
   Each rule has a context designated by F in the above rules, active formulas
designated by A and B, and a principal formula that is introduced on the left or
the right by the rule in question.
   The above calculus differs in three respects from the sequent calculus rules
presented in Section 1.3: Only atoms appear in axioms, and the formula A D B is
repeated in the left premiss of the LD rule. The reason for the latter will become
apparent later, when admissibility of contraction is proved. Third, the rules have
shared contexts.
   The calculus has been developed by Troelstra, as a single succedent variant
of the calculus of Dragalin (1988). None of the usual structural rules of sequent
calculus, weakening, contraction, and cut, need be assumed in it. Exchange rules
are absent because of properties of multisets and the other structural rules; those
of weakening, contraction, and cut will be proved admissible. The structural rules
we consider are

                                   -Wk

                                         A   A , A =>• C
                                                           c«f
                                         r, A =» c
In Gentzen's original calculus of 1934-35, the structural rules were first assumed,
and then it was shown how to eliminate applications of the cut rule. A calculus
for intuitionistic logic of the above type, with no structural rules, was first devel-
oped by Kleene in 1952 for the purpose of proof search. In Gentzen, negation is
primitive, but this does not make a great difference. It has the simplifying effect
that derivations begin with axioms only, not LJ_. Gentzen's calculus maintained
the rule of weakening; therefore axioms were of the form A =^ A, with no con-
text since it could be added by weakening. In the calculus G3ip, weakening is
admissible because it is built into the axiom and the L_L rule.
   The logical rules of the calculus are intuitionistic versions of the rules of
Ketonen (1944); In Gentzen's calculus, there were two left rules for conjunction,
one for each premiss of the form A, F => C and B, F =>• C, and the conclusion
as in the above rule. Further, the left implication rule was as follows:

                               F => A B, A => C
                                AD B,F,A=>C
There are two contexts that are joined in the conclusion, so that the rule has inde-
pendent contexts. In the calculus G3ip, instead, all two-premiss logical rules are
context-sharing, or have the same context. A shared context is needed for hav-
ing a contraction-free calculus. Further, the principal formula in LD is repeated
in the left premiss for the same purpose, a device invented by Kleene in 1952.
30                      STRUCTURAL PROOF THEORY

(He repeated the principal formula in all the left rules, but such repetition is needed
only for noninvertible rules.)


2.3. P R O O F METHODS FOR ADMISSIBILITY

Our task in the next two sections is to establish the admissibility of structural
rules for the calculus G3ip. Proofs of admissibility will use induction on weight
of formulas and height of derivations. Formula weight can be defined in different
ways, depending on what is needed in a proof. For the next few chapters a simple
definition, amounting to the length of a formula, will be sufficient. In Section 5.5,
we shall encounter more complicated formula weights.

Definition 2.3.1: The weight w(A) of a formula A is defined inductively by

 w(±) = 0,
 w(P) = I for atoms P,
 w(A o B) = w(A) + w(B) + I for conjunction, disjunction, and implication.

It follows that tu(~ A) = w(A) + tu(_L) + 1 = w(A) + 1.

Definition 2.3.2: A derivation in G3ip is either an axiom, an instance of LI.,
or an application of a logical rule to derivations concluding its premisses. The
height of a derivation is the greatest number of successive applications of rules
in it, where an axiom and L_L have height 0.

Lemma 2.3.3: The sequent C, F =>> C is derivable for an arbitrary formula C
and arbitrary context F.

Proof: The proof is by induction on weight of C. If w(C) ^ 1, either C = J_
or C = P for some atom P or C = J_ D _L. In the first case, C, F =>• C is an
instance of L_L; in the second it is an axiom. If C = J_ D _L, then C, F =>• C is
derived by

                                                          L±
                                  _L,-L D _ L , r => J_



The inductive hypothesis is that C, F => C is derivable for all formulas C with
w(C) ^ n, and we have to show that D, F =>• D is derivable for formulas D of
weight ^ n + 1. There are three cases:
D = ASLB. By the definition of weight, w(A) < n and w(B) ^ n. Noting that
the context is arbitrary, we have that A, F' => A and 5 , F" =>• 5 are derivable,
           SEQUENT CALCULUS FOR INTUITIONISTIC LOGIC                             31

where Tf = B, F and F" = A, F. We now derive A&B, F => A&B by


                                                              R&
                                 A&B, F => A&£

Z) = A v B. As before w(A) ^ n, w{B) ^ n, and we have the derivation



                                                                 LV
                                Av B,T => Av B

D = A D B. As before w(A) ^ n, w(B) ^ n, and we have the derivation
                        A   A ~") R   V —^ A    R   A   V —^ P



                                AD B,T ^ AD B
Here A , A D 5 , F ^ A and B,V =>• B are derivable by the inductive hypo-
thesis. QED.

  Proof by induction on height of derivation is a usual method, often as a subin-
duction in an inductive proof on formula weight. In the following, the notation



will stand for: the sequent F =>• C in G3ip is derivable with a height of derivation
at most n.
   When proving the admissibility of a rule by induction on height of derivation,
we prove it for subderivations ending in a topmost occurrence of the rule in
question, then generalize by induction on the number of applications of the rule
to arbitrary derivations. Therefore it can be assumed that in a derivation there is
only one instance of the rule in question, the last one.

Theorem 2.3.4: Height-preserving weakening.If \-n F=^C, then \-n D,T=>
C for arbitrary D.

Proof: The proof is by induction on height of derivation. If n = 0, then F =>• C
is an axiom or conclusion of L_L and either C is an atom and a formula in F or _L
is a formula in F. In either case, also D, F =>• C is an axiom or concluded by L_L.
Assume now that height-preserving weakening is admissible up to derivations of
height < ft, and let \-n+x F => C. If the last rule applied is L&, F = A&B, F'
and the last step is


                                   A&B, r^cL&
32                     STRUCTURAL PROOF THEORY

so the premiss A, B, F r => C is derivable in ^ ft steps. By inductive hypothesis,
also D, A, 5 , F' =>• C is derivable in ^ ft steps. Then an application of L& gives
a derivation of D, A&B, F = ^ C i n ^ f t + l steps.
   A similar argument applies to all the other logical rules. QED.

A more direct way of obtaining height-preserving weakening is to transform the
given derivation by adding the weakening formula to the antecedents of all its
sequents. Two-premiss rules of G3ip have the same context in both premisses,
and the conclusion inherits only one copy of these. In the proof transformation
showing admissibility of height-preserving weakening, the weakening formula is
added always into the contexts of axioms or L_L, and therefore no multiplication of
the weakening formula is produced. By repeating weakening, we find weakening
admissible for an arbitrary context F': If \-n F =>• C, then \-n F, F' =>• C.
   For proving the admissibility of contraction, we will need the following
inversion lemma:

Lemma 2.3.5:
  (i) / / \-n ASLB, F =• C, then hn A, B, F => C,
  (ii) If\-nAvB,r=>C,        then \-n A, F => C and \-n B, F => C,
  (iii) If\-nADB,F=>C,        then \-n B, F =>• C.

Proof: By induction on n.
    (i) If A&B, F =>• C is an axiom or conclusion of L_L; then, A&5 not being
atomic or J_, also A, 5 , F =>• C is an axiom or conclusion of L_L.
    Assume height-preserving inversion up to height n, and let h n + i A&B, F =^
C.
    If ASLB is the principal formula, the premiss A, B,F =} C has a derivation of
height ft.
    If ASLB is not principal in the last rule, it has one or two premisses
A&B, Ff => C\ A&B, F" =>• C", of derivation height ^ n; so by inductive hy-
pothesis, \-n A, B, Ff => C" and \-n A, B, F /r ^ C". Now apply the last rule to
these premisses to conclude A, B, F =>> C in at most n + 1 steps.
    (ii) As in (i), if A V 5 , F =>• C is an axiom, also A, F => C and 5 , F = ^ C
are axioms.
    If A v 5 is the principal formula, the two premisses A, F =>• C and 5 , F =>• C
are derivable in n steps.
    If A v B is not principal in the last rule, it has one or two premisses
A v ^ r ' ^ C , A V B, V" =$> C", of derivation height < n, so by inductive
hypothesis, \-n A, F' =^ Cr and h n 5 , F ; =^ C7 and \-n A,T" => C" and
\-n B,Y" ^ C"\ Now apply the last rule to the first and the third to conclude
A, F =>• C and to the second and the fourth to conclude B, F =>• C in at most
ft + 1 steps.
           SEQUENT CALCULUS FOR INTUITIONISTIC LOGIC                             33

   (iii) As above for the case that A D B, F ==> C is an axiom.
   If A D B is the principal formula, the premiss B, F =$> C has a derivation of
heights.
   If A D B is not principal in the last rule, it has one or two premisses
AD B,T' =>C, AD B, F" => C", of derivation height ^ n, so by inductive
hypothesis, \-n B, Ff =» C and \-n B,F" => C": Now apply the last rule to these
premisses to conclude B, F =$• C in at most n + 1 steps. QED.

If a rule is invertible, we often indicate use of the inverse rule by writing Inv at
the inference line. Similarly, if a step is permitted by an inductive hypothesis, we
write Ind next to the inference line.
   The following example shows that LD is not invertible with respect to its first
premiss: The sequent I D l ^ l D l i s derivable in G3ip by
                                                • L±
                                     D _L



If LD were invertible with respect to its first premiss, from the derivability of a
sequent with an implication in the antecedent would follow the derivability of its
first premiss as determined by the LD rule. For the sequent _L D JL =>> _L D _L,
this first premiss would be _L D _L =>• J_. The sequent _L => ± is an instance of
L_L, and RD gives => _L D _L. An application of the cut rule now gives =>±,
which would make the system G3ip inconsistent. (The formula _L D J_ of this
example is the "standard" true formula, abbreviated as T = _L D _L.)


2.4.   ADMISSIBILITY OF CONTRACTION AND CUT

Next we prove the admissibility of the rule of contraction in G3ip:
Theorem 2.4.1: Height-preserving contraction. If \-n D, D, F => C, then
\-n D, F =^ C.
Proof: The proof is by induction on the height of derivation n. If n = 0,
D, D, F =>• C is an axiom or conclusion of L_L and either C is an atom in the
antecedent or the antecedent contains _L. In either case, also D, F =>• C is an
axiom or conclusion of L_L.
   Let contraction be admissible up to derivation height n. We have two cases
according to whether the contraction formula is not principal or is principal in
the last inference step.
   If the contraction formula D is not principal in the last (one-premiss) rule
concluding the premiss of contraction we have
                                  £>, P , T => C
                                   D, D, T = ^ C
34                     STRUCTURAL PROOF THEORY

which has a derivation height ^ n, so by inductive hypothesis we obtain
\-n D, F r =>• Cr and by applying the last rule h n + i D, F =>• C. Two-premiss rules
have two occurrences of D in both premisses and the same argument applies.
    If the contraction formula D is principal in the last rule, we have three cases
according to the form of D:
     D = A&B. Then the last step is L& and we have \-n A, B, A&B, F =^ C. By
Lemma 2.3.5, we obtain \-n A, B, A, B, F =>• C and by inductive hypothesis ap-
plied twice, \-n A, B,F =>• C. Application of L& now gives h n + 1 A&J5, F =>• C.
     D = A v 5 . Then the last step is L v and we have \-n A, A v B, F =>• C and
h n 5 , A v 5 , T = > C . Lemma 2.3.5 gives h n A, A, F =^ C and h n B,B,F =>
C so by inductive hypothesis, h n A, F =>• C and \-n B, V =>• C, so by
Lv, h n + 1 A v 5 , r ^ C .
     D = A D 5 . Then the last step is LD and we have \-n A D B, A D B,F ^
A and h n 5 , A D 5 , F ^ C. By inductive hypothesis, the first gives
\-nADB,V=^A.             By Lemma 2.3.5, the second gives \-n B, B, V =» C
so by inductive hypothesis, h n 5 , F =>• C. Application of LD now gives
h n + i A D f i J ^ C . QED.

Remarkably, the weaker result of admissibility of contraction without preserva-
tion of height is more difficult to prove than admissibility of height-preserving
contraction, for its proof requires a double induction on formula weight with a
subinduction on height of derivation.
   The repetition of the principal formula in the first premiss of rule LD is needed
in order to apply the inductive hypothesis that permits contraction in a derivation
of less height. In classical sequent calculus with shared contexts, all rules are
invertible and there is no need for such repetition. The same is true in G3ip in the
sense that the rule without repetition,


                                  A D B,V =^C

is admissible in G3ip. This follows by the application of weakening with A D B
to the left premiss F =>• A.
   We now come to the main result of this chapter, the admissibility of cut for the
calculus G3ip. Gentzen called his cut elimination theorem the "Hauptsatz," the
main theorem, and this is how cut elimination is often called today also. The proof
uses, explicitly or implicitly, all the preceding lemmas and theorems to show that
cuts can be permuted upward in a derivation until they reach the axioms and
conclusions of L_L the derivation started with. When both premisses of a cut are
axioms or conclusions of L_L, the conclusion also is an axiom or conclusion of
LJ_: If the first premiss is _L, F =^ C, the conclusion has _L in the antecedent,
and if the first premiss is P, F =>• P, the second premiss is P, A =>• C. This is
           SEQUENT CALCULUS FOR INTUITIONISTIC LOGIC                              35

an axiom only if C = P or C is an atom in A, and it is a conclusion of L_L only
if _L is in A. In each case, the conclusion of cut P, F, A =^ C is an axiom or
conclusion of L_L. As a consequence, when cut has reached axioms and instances
of L_L, the derivation can be transformed into one beginning with the conclusion
of the cut, by just deleting the premisses.
    The proof of admissibility of cut for G3ip is by induction on the weight of the
cut formula and a subinduction on the sum of heights of derivations of the two
premisses. This sum is called cut-height:

Definition 2.4.2: Cut-height. The cut-height of an instance of the rule of cut in
a derivation is the sum of heights of derivation of the two premisses of cut.

We give transformations that always reduce the weight of cut formula or cut-
height. Actually, what happens is that cut-height is reduced in all cases in which
the cut formula is not principal in both premisses of cut. In the contrary case, cut
is reduced to formulas of lesser weight. This process terminates since atoms can
never be principal in logical rules.
    Cut-height is not monotone as we go down in a derivation; that is, a cut below
another one can have a lesser cut-height: In the derivation of one of its premisses
there is the first cut, and this derivation has a greater height than either of the
premisses of the first cut. But the other premiss may have a height much shorter
than either premiss of the first cut, making the sum less than the sum in the first
cut. It follows that the permutation of a cut upward does not always reduce cut-
height but can increase it. For this reason, we shall explicitly calculate the height
of each cut in what follows. As with weakening and contraction, we may assume
that there is only one occurrence of the rule of cut, as the last step.

Theorem 2.4.3: The rule of cut,

                             F => D     £>, A => C
                                                    -Cut
                                   r, A => c
is admissible in G3ip.

Proof: The proof is organized as follows: We consider first the case that at least
one premiss in a cut is an axiom or conclusion of L_L and show how cut is
eliminated. For the rest there are three cases: 1. The cut formula is not principal
in either premiss of cut. 2. The cut formula is principal in just one premiss of cut.
3. The cut formula is principal in both premisses of cut.
Cut with an axiom or conclusion of L_L as premiss: If at least one of the
premisses of cut is an axiom or conclusion of LJ_, we distinguish two cases:

1. The left premiss F => D of cut is an axiom or conclusion of L_L. There are
two subcases:
36                     STRUCTURAL PROOF THEORY

1.1. The cut formula D is in F. In this case we derive F, A =^ C from D, A => C
by weakening.
1.2. _L is a formula in F. Then F, A =>> C is a conclusion of L_L.
2. The right premiss D, A =^ C is an axiom or conclusion of L_L. There are
four subcases:
2.1. C is in A. Then F, A =^ C is an axiom.
2.2. C = D. Then the first premiss is F => C and F, A =$• C follows by weakening.
2.3. _L is in A. Then F, A =>- C is a conclusion of L_L.
2.4. D = _L. Then either the first premiss F => _L is an axiom and F, A =^ C
follows as in case 7, or F =^ _L has been derived by a left rule. There are three
cases according to the rule used. These are transformed into derivations with
less cut-height. Since the transformations are special cases of the transformations
3.1-3.3 below, with D = _L, we do not write them out here.
Cut with neither premiss an axiom: We have three cases:
3. Cut formula D is not principal in the left premiss, that is, not derived by
an /?-rule. We have three subcases according to the rule used to derive the left
premiss. In the derivations, it is assumed that the topsequents, from left to right,
have derivation heights n,m,k,
3.1. L&, with F = A&B, F'. The derivation with a cut of cut-height n +         l+m
is

                        A, B, F' =» D
                                        • L&
                       A&B,T'^D    P, A=>C
                                f
                          A&B, V ,A^C
and it is transformed by permuting the order L&,Cut into the order Cut,L&. The
result is the derivation with a cut of cut-height n + m:


                                                         Cut

                                                  • L&



3.2. L v , with V = Av B,Vf.        The derivation with a cut of cut-height
max(n, m) + 1 + k
             SEQUENT CALCULUS FOR INTUITIONISTIC LOGIC                          37

is transformed into the derivation with two cuts of heights n + k and m + k:

             A,F'^D      D, A
                                         Cut




5.3. LD, with r = A D 5 , r ; . The derivation with a cut of cut-height
max(n, m) + 1 + k


                      AD B,Tf => D                  LD
                                                            D,A=>C
                                                                  Cut

                                 A D B,r\          A =>C

is transformed into the derivation with a cut of cut-height m + k:
                                  - Wk                               Cut
               A P ff,T, A =» A                  B,Tf, A ^
                         ADBF\                 A C

We observe that cut-height is reduced in each transformation.
4. Cut formula D is principal in the left premiss only, and the derivation is
transformed into one with a cut of lesser cut-height according to the derivation of
the right premiss. We have six subcases according to the rule used:
4.1. L&, with A = A&B, A\ and the derivation with a cut of cut-height
n -\-m + 1

                                    Z), A,£, A' =^ C
                                                   —        L&

                                               7
                                          , A =» C

is transformed into the derivation with a cut of cut-height n + m:



                                                       L&
                              r, A & # , A7 => c
4.2. Lv, with A = A V 5, A', and the derivation with a cut of cut-height
ft + max{m, k) + I


                  T => D             D,AvB,            A'=^C
                                                            Cut
                           r A 5 A ; C
38                    STRUCTURAL PROOF THEORY

is transformed into the derivation with two cuts of heights n + m and n + k:

          r =» D     D,A,Af=>C                 V^D        D,B,A'^C
                                       Cut                              Cut
                r A A ' c                      T B A ' C
                                                                   LV
                              r , A v £, A' =^ C

4.3. LD, with A = A D 5 , A', and the derivation with a cut of cut-height
n +max(m, k) + 1

                        D,AD B,Af ^ A                 D,B,Af^C
                                                                    LD
              r =» £ > D , A D ^ , A ^ C
                                                             C


is transformed into the derivation with two cuts of heights n + m and n + k\

        F => D     D, A D B, A' => A            r => £>           D,B,A'=>C
                                                      r , g , A / =>c         Cut




       , with C = A&#, and the derivation with a cut of cut-height
n + maxim, k) + 1

                               D, A=^A
                                 7
                                                     D,A^B
                                           J     D       ^
                    r ^> z>          D, A ^
                                                      Cut
                              r, A =• A & B
is transformed into the derivation with two cuts of heights n + m and n + k:

              F^D       D, A^A        T ^ D D,A=>B
                                  c                 c
                    r, A => A       "     r, A => g   "
                              r, A
4.5. Rv, with C = A V B, and the derivations with cuts of cut-heights n + m + 1
a n d n + k + l , respectively,



                                     Cut                                    Cut
                                                     r A ^ A v 5

are transformed into the derivations with cuts of cut-heights n + m and n + k:

             T^D       D,A^A                   V => D            D,A=>B
                                      C                                 C
          SEQUENT CALCULUS FOR INTUITIONISTIC LOGIC                        39

4.6. RD, with C = A D B, and the derivation with a cut of cut-height n + m + 1

                                        Z), A, A =      n-N


                                       D,


is transformed into the derivation with a cut of cut-height n + m\

                           T ^ D        L>, A, A
                                                      -Cut




In each case, cut-height is reduced.
5. Cut formula D is principal in both premisses, and we have three subcases:
5.7. D = A&Z?, and the derivation with a cut of cut-height max(n, m) + 1 +
Jk + l i s

                    T^A   T^B                   A,B,A^C
                      T^AScB                  A8BA^C
                                              A8iB,A^C
                                                              Cut
                                   f^^c
This is transformed into the derivation with two cuts of heights n + k and
m + max(n, k) + 1:

                                T=»A A,B, A=>C
                                              Cut
                      r =>• B      F,B,A^C
                                                      Cut
                                              ctr



Note that cut-height can increase in the transformation, but the cut formula is
reduced.
5.2. D = A V B, and the derivation is either

                    r =>• A            A,A=^C        5 , A =^ C
                                                              -CM?
                                r , A =>• c

with cut-height n + 1 + max(m, k) + 1 or

                                                                     L v
                                                              ;
                                                              -CM?
40                      STRUCTURAL PROOF THEORY

with the same cut-height. These are transformed into derivations with cuts of
cut-heights n +m andn + k,

              r =>A      A,A=^C                  r^B           B,A^C
                                      Cut                          Cut
                    r,A^c                              r,A^c
where both cut-height and weight of cut formula are reduced.
5.3. D = A D B, and the derivation with a cut of cut-height n + 1 +
maxim, k) + 1 is

                A,F=^£             AD5,A^A   £, A => C
               V ^ AD B               AD   B,A^C
                                ^—:         7;             Cut


This is transformed into the derivation with three cuts of heights n + 1 +m,n
and max(n + 1, m) + 1 + max(n, k) + 1


                                                           B   B,A=>C
                                                                      Cut
                                                           T A ^ C


In the first and second cut, cut-height is reduced; in the second and third, weight
of cut formula. QED.

In many of the permutations of cut upward in a derivation, the number of cuts
increases exponentially.
   In contrast to the logical rules, the contexts in the two premisses of the cut rule
are independent. However, by the admissibility of structural rules, we can show
that also the cut rule with a shared context,




is admissible. To see this, first apply the usual cut rule to the two premisses to
derive F, F, =>• C, then contract the duplication of F in its conclusion.


2.5.   SOME CONSEQUENCES OF CUT ELIMINATION

(a) The subformula property: Since structural rules can be dispensed with in
G3ip, we find by inspection of its rules of inference that no formulas disappear
from derivations:

Theorem 2.5.1: If F =>• C has a derivation in G3ip, all formulas in the deriva-
tion are subformulas ofV, C.
           SEQUENT CALCULUS FOR INTUITIONISTIC LOGIC                             41

Similarly, a connective that has once appeared in a derivation cannot disappear.
From this it follows in particular that =>± is not derivable, i.e., the calculus is
syntactically consistent.

Theorem 2.5.2: If =^ A V B is derivable in G3ip, then =>Aor =^B is derivable.

Proof: Only right rules can conclude sequents with an empty antecedent so the
last rule can only be R v. QED.

This theorem establishes the disjunction property of the calculus for intuitionis-
tic propositional logic. That such a property should hold follows from the construc-
tive meaning of disjunction as given in Section 2.1. The result can be strengthened
into a disjunction property under suitable hypotheses:

Definition 2.5.3: The class of Harrop formulas is defined by
   (i) P, <2, R,..., and _L are Harrop formulas,
   (ii) A&B is a Harrop formula whenever A and B are Harrop formulas,
   (iii) A D B is a Harrop formula whenever B is a Harrop formula.
 Theorem 2.5.4: IfV=>AvBis      derivable in G3ip and F consists of Harrop
formulas, then F =>• A or F =$> B is derivable.
Proof: The proof is by induction on the height of derivation. For the base case,
V => Av B is not an axiom, and if it is the conclusion of L_L also F =>> A
is. If the last rule in the derivation of F => A V B is Rv, the premiss is ei-
ther F =>• A or F =» B. If the last rule is L&, then F = C&D, Fr and the pre-
miss is C, D, F' =>• A v B. Since CSLD is a Harrop formula, also C and D are
and the inductive hypothesis applies to the premiss. If the last rule is LD, then
F = C D D, Ff and the inductive hypothesis applies to the right premiss
D , r ; ^ A v 5 . The last rule cannot be Lv. QED.
Proof by induction on the height of derivation in a system with no structural rules
is remarkably simple compared with the original proof of the result in Harrop
(1960).
(b) Hilbert-style systems: We show that, from G3ip, the more traditional Hilbert-
style axiomatic formulation of intuitionistic propositional logic follows. In a
Hilbert-style system, formulas rather than sequents are derived, starting with in-
stances of axioms and using in the propositional case only one rule of inference,
modus ponens. The axioms are given schematically as

1. I D A ,
2. AD(BDA&B),                      3.A&BDA,      4.A&BDB,
5.ADAVB,    6.BDAWB,               7. (ADC)D((BDC)D(Av    BDQ),
8. AD(BDA),                        9. (AD(BDC))D((AD   B)D(ADC)).
42                     STRUCTURAL PROOF THEORY

In Hilbert-style systems, substitution of formulas is done in the schematic axioms
to obtain the top formulas of derivations. These systems are next to impossible to
use for the actual derivation of formulas because of the difficulty of locating the
substitution instances that are needed. A notorious example is the derivation of
A D A by substitutions in axioms 8 and 9:
(A D ((ADA)   D A)) D ((A D (A D A)) D (A D A))     AD ((A D A) D A)
                      (AD (AD A)) D(AD A)                               A D (A D A)
                                                    A~5~A
There seems to be very little relation between the simplicity of the conclusion and
the complexity of its derivation. In order to translate derivations in the Hilbert-
style system into G3ip we shall write axiom schemes as sequents with empty
antecedents and the rule of modus ponens as the sequent calculus rule

                               ^ AD B => A __
                                         — Mp
                                   => B
We show that this translation of derivations in the Hilbert-style system gives
derivations in G3ip:

Theorem 2.5.5: If formula C is derivable in the Hilbert-style system, then =>• C
is derivable in G3ip.

Proof: In a derivation of C, each instance A of an axiom is replaced by a derivation
of the sequent =>• A. All the axiom schemes as sequents with empty antecedents
are easily derived in G3ip, and we show only thefirsttwo:


                                               A,B =» A&B

                     =>±D A                   =>AD(BD ASLB)
Each application of modus ponens in the derivation of C is replaced by its sequent
calculus version. We note that a rule is admissibile in G3ip if it is derivable using
also structural rules. Modus ponens as a sequent calculus rule concluding =^B
from =>> A D B and =^ A is derived by
                                  AD B,A^ A B => B
                                                  LD
                           ^ AD B    AD B,A^ B
                                          ;     ^             Cut

                               =» B
By cut elimination, a derivation of =^ C in G3ip is obtained. QED.

Hilbert-style systems are widely used in model theory and related fields, but in
proof theory they are more of historical interest. It is possible, although very
           SEQUENT CALCULUS FOR INTUITIONISTIC LOGIC                            43

laborious, to prove a converse to Theorem 2.5.5, by the following translations:
Sequents A i , . . . , Am => B are translated into formulas A\&... &Am D B, and
instances of sequent calculus rules, say
                       A i , . . . , Am => A Bu...,Bn^      B
                                      C\,..., Ck => C

into implications

         (Ai& . . . &Am D A)&(Bi& . . . &Bn DB)D(Ci&         . . . &Ck DC).

(c) Underivability results: Certain sequents require for their derivation logical
systems stronger in deductive strength than intuitionistic logic. Examples of such
sequents are
   => A v ~ A, the law of excluded middle,
   =>• ~ A v ~ ~ A, the weak law of excluded middle,
   =>• ~ ~ A D A, the law of double-negation,
   ^ ( A D 5 ) V ( 5 D A), Dummett's law,
   =>> ((A D 5 ) D A) D A, Peirce's law,
   ^ ( A D 5 v C ) D ( A D 5 ) v ( A D C ) , disjunction property under hypoth-
esis,
   => (~ A D 5 V C) D (~ A D B) V (~ A D C), disjunction property under
negative hypothesis.
The underivability of these sequents in intuitionistic logic is usually established
by model-theoretical means. We show their underivability proof-theoretically by
the elementary method of contraction- and cut-free derivability. We note that
if a sequent is underivable for atomic formulas, such as = ^ P v ^ P , then the
corresponding sequent =>A\/~ A with arbitrary formulas is also underivable.
Whenever in a root-first proof search a premiss is found that is equal to some
previous sequent, proof search on that branch is stopped. One says that a loop
obtains in the search tree. Stopping the proof search is justified by the fact that a
continuation from the repeated sequent succeeds if and only if a search from its
first occurrence succeeds.

Theorem 2.5.6: The following sequents are not derivable in G3ip:
   (i) =^Pv~P,
   (ii) ^ ^ p v ~ ^ P ,
   (iii) = » ((/> D Q ) D P ) D P ,
   (iv) =^(P D Qv R)D (P D Q)V(P               D R).
Proof: (i) Assume there is a derivation of =>• P V ~ P. By the disjunction prop-
erty, either =^ P or =^~ P is derivable. No rule concludes =>• P for an atom P,
44                     STRUCTURAL PROOF THEORY

and only RD concludes = ^ ~ P , so by invertibility of RD, P =>• _L is derivable.
But no rule concludes such a sequent.
(ii) For = ^ ~ P v ~ ~ P to be derivable, by proof of (i), =>• ~ ~ P must be deriv-
able. Proceeding root-first, the last three steps must be




Since the left premiss of the uppermost instance of LD is equal to its conclusion,
this proof search does not terminate. Therefore there is no derivation of =>• ~ ~ P .

(iii) With =>((P D Q) D P) D P , the last two steps must be

                     (PDQ)DP^PDQ                   P => P



If we continue by RD we get

                  P,(P D Q)D P ^ P D Q P,P => Q
                                                              - LD




but the right premiss is not derivable by any rule. If we apply LD instead we get


                  (PDQ)DP^PDQ                   P => P D Q


This proof search fails because the sequent P , P =>• 2 is not derivable. Therefore
=>((P D Q)D P)D P is not derivable.
(iv) Derivations of =>• (P D g V R) D (P D Q) V (P D P) must end with PD.
The premiss is P D Qv R => (P D Q)v (P D R), and if the last rule was Rvu
the derivation has either RD or LD. If it is the former, we have the steps


               P,P D Qw
                         P,P D Qv R^ Q
                        PDQVR=>PDQRD
                   P D Qv R^(P D g) V (P D R)RVl
           SEQUENT CALCULUS FOR INTUITIONISTIC LOGIC                              45

But the premiss P, R =>> Q is not derivable. Else the last steps are
          P D Qv R=> P Qv R^ P
                                     LD
                P D Qv R^ P              Qv R^ P D Q
                                                     LD
                          P D Qv R=> P D Q
                     P D Q V R => (P D Q) V (P D R)
Conclusion of LD is repeated in the premiss. If the last rule was R V2, underiv-
ability follows in an entirely similar way. The only remaining possibility is that
the rule was LD, and we have as the last steps
   P D Qv R=> P Qv R^ P
                          LD
        P D Qv R^ P                         Qv R^(P   D Q)V(P D R)
                                                                   LD
                 P D QV R^(P                 D Q)V(P D R)
Again the conclusion of the upper LD was repeated in the premiss. We do not
need to analyze the right premiss, since the proof search fails in any case. QED.

(d) Independence of the intuitionistic connectives: None of the standard in-
terdefinabilities of classical propositional logic obtain in intuitionistic logic. By
arguments similar to those above, it is shown that the following sequents are
underivable:

   (i) ~0~ A& ~ h0 = A V B ,      = > •




   (ii) ~y\DB^   Av
   (iii) ~(.A&L-B)    =   >   •
                                   AD
(e) Decidability of intuitionistic propositional logic: In the above examples,
we were able to survey all possible derivations and found by various arguments
that none turned out to be good. This depended essentially on having all derivations
contraction- and cut-free.

Theorem 2.5.7: Derivability of a sequent T =^ C in the calculus G3ip is decid-
able.

Proof: We generate all possible finite derivation trees with endsequent T => C
and show them to be bounded in number. Starting with F =^ C, we write all
instances of rules that conclude it, then do the same for all the premisses of the
last step. All rules except LD reduce the sequent to be derived into ones with less
weight, where the weight of a sequent is the sum of the weights of its formulas.
If in a proof search we arrive at a sequent that does not reduce by any rule, then
if it is not an axiom or conclusion of L_L, we terminate the proof search. If in a
proof search we have two applications of LD that conclude the same sequent, we
also terminate the proof search. Application of LD root-first can produce only a
bounded number of different sequents as premisses. Therefore each proof search
46                     STRUCTURAL PROOF THEORY

tree terminates. If there is one tree all leaves of which are axioms or conclusions
of LJ_, the endsequent is derivable; if not, it is underivable. QED.
This algorithm of proof search is not very efficient, as one can see by trying, say,
the disjunction property under negative hypothesis. There are sequent calculi for
intuitionistic propositional logic that are much better in this respect. One such
calculus will be studied in Section 5.5.


NOTES TO CHAPTER 2

Constructive real numbers and constructive analysis is treated in Bishop and Bridges
(1985). The two-volume book of Troelstra and van Dalen (1988) is an encyclopedia of
metamathematical studies on constructive logic and formal systems of constructive
mathematics. A discussion of predicativity, with references to original papers by
Poincare and Russell, is found in Kleene (1952, p. 42). The same reference also
discusses the background and development of intuitionism (ibid., p. 46).
   The calculus G3ip is the propositional part of a single succedent version of
Dragalin's (1988) calculus and is presented as such in Troelstra and Schwichtenberg
(1996). The proofs of admissibility of contraction and cut follow the method of
Dragalin, with inversion lemmas and induction on height of derivation. The proof in
Dragalin (1988) is an outline; a detailed presentation is given in Dyckhoff (1997).
               Sequent Calculus for Classical Logic




There are many formulations of sequent calculi. Historically, Gentzen first found
systems of natural deduction for intuitionistic and classical logic, denoted by NJ
and NK, respectively, but was not able to find a normal form for derivations in NK.
To this purpose, he developed the classical sequent calculus LK that had sequences
of formulas also in the succedent part. In our notation, such multisuccedent
sequents are written as F =>> A, where both F and A are multisets of formulas.
Gentzen (1934-35) gives what is now called the denotational interpretation of
multisuccedent sequents: The conjunction of formulas in F implies the disjunction
of formulas in A. But the operational interpretation of single succedent sequents
F =>• C, as expressing that from assumptions F, conclusion C can be derived,
does not extend to multiple succedents.
    Gentzen's somewhat later explanation of the multisuccedent calculus is that it
is a natural representation of the division into cases often found in mathematical
proofs (1938, p. 21). Proofs by cases are met in natural deduction in disjunc-
tion elimination, where a common consequence C of the two disjuncts A and
B is sought, permitting to conclude C from A V B. There is a generalization of
natural deduction into a multiple conclusion calculus that includes this mode
of inference. Gentzen suggests such a multiple conclusion rule for disjunction
(ibid., p. 21):

                                      Ay B
                                      A B
Disjunction elimination corresponds to arriving at the same formula C along both
downward branches.
   Along these lines, we may read a sequent F =>• A as consisting of the open
assumptions F and the open cases A. Logical rules change and combine open
assumptions and cases: L& replaces the open assumptions A, B by the open
assumption A&B, and there will be a dual multisuccedent rule Rv that changes
the open cases A, B into the open case Av B, and so on. If there is just one case,
we have the situation of an ordinary conclusion from open assumptions. Finally,
                                                                                47
48                      STRUCTURAL PROOF THEORY

we can have, as a dual to an empty assumption, an empty case representing
impossibility, with nothing on the right of the sequent arrow.
   In an axiomatic formulation, classical logic is obtained from intuitionistic logic
by the addition of the principle of excluded third to the logical axioms (Gentzen
1934-35, p. 117). In natural deduction, one adds that derivations may start from
instances of the law A v ~ A (Gentzen, ibid., p. 81). Alternatively, one may add ei-
thertherule ^ ^ (Gentzen, ibid.) or the rule of indirect proof (Prawitz 1965,p.20):



                                           _L


In sequent calculus, in the words of Gentzen (ibid., p. 80), "the difference is char-
acterized by the restriction on the succedent," that is, a calculus for intuitionistic
logic is obtained from the classical calculus LK by restricting the succedent to
be one (alternatively, at most one) formula. The essential point here is that the
classical RD rule
                                   A,V => A,ff
                                  V ^      A,AD    B
becomes
                                     A,T    => B
                                    T^AD5
An instance of the former is
                                      A =^ A,_L
                                    =>> A, AD _L
By the multisuccedent Rv rule, the cases A, A D _L can be replaced by the dis-
junction A V (A D J_), a derivation of the law of excluded middle that gets barred
in the intuitionistic calculus.
   It is, however, possible to give an operational interpretation to a restricted
multisuccedent calculus corresponding precisely to intuitionistic derivability, as
will be shown in Chapter 5. Therefore, it is not the feature of having a multiset as
a succedent that leads to classical logic, but the unrestricted RD rule. If only one
formula is permitted in the succedent of its premiss, comma on the right can be
interpreted as an intuitionistic disjunction.


