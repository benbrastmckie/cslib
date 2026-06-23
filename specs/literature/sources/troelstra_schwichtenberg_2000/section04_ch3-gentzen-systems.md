# Basic Proof Theory — Chapter 3: Gentzen Systems (lines 2971-4467)

Chapter 3

Gentzen systems

Gentzen [1935] introduced his calculi LK, LJ as formalisms more amenable to
metamathematical treatment than natural deduction. For these systems he
developed the technique of cut elimination. Even if nowadays normalization
as an "equivalent" technique is widely used, there are still many reasons to
study calculi in the style of LK and LJ (henceforth to be called Gentzen
calculi or Gentzen systems, or simply G-systems):

      Where normal natural deductions are characterized by a restriction on
      the form of the proof more precisely, a restriction on the order in
      which certain rules may succeed each other cutfree Gentzen systems
      are simply characterized by the absence of the Cut rule.
      Certain results are more easily obtained for cutfree proofs in G-systems
      than for normal proofs in N-systems.
      The treatment of classical logic in Gentzen systems is more elegant than
      in N-systems.

The Gentzen systems for M, I and C have many variants. There is no reason
for the reader to get confused by this fact. Firstly, we wish to stress that in
dealing with Gentzen systems, no particular variant is to be preferred over
all the others; one should choose a variant suited to the purpose at hand.
Secondly, there is some method in the apparent confusion.
   As our basic system we present in the first section below a slightly modified
form of Gentzen's original calculi LJ and LK for intuitionistic and classical
logic respectively: the Gl-calculi. In these calculi the roles of the logical rules
and the so-called structural rules are kept distinct.
   It is possible to absorb the structural rules into the logical rules; this leads
to the formulation of the G3-calculi (section 3.5) with the G2-calculi (not very
important in their own right) as an intermediate step. Finally we formulate
(section 3.6) for classical logic the GentzenSchiitte systems (GS-systems),
exploiting the De Morgan dualities. The use of one-sided sequents practically
halves the number of rules. In later chapters we shall encounter the G4-
                                        60
3.1. The G1- and G2-systems                                                             61

and G5-systems, designed for special purposes. Two sections respectively
introduce the Cut rule, and establish deductive equivalence between N- and
G-systems.


3.1      The Gl- and G2-systems
The Gentzen systems G1c, G1i below (for classical and intuitionistic logic)
are almost identical with the original Gentzen calculi LK and LJ respectively.
The systems derive sequents, that is to say expressions r       A, with F, A
finite multisets (not sequences, as for Gentzen's LJ, LK); for the notational
conventions in connection with finite multisets, see 1.1.5.

3.1.1. DEFINITION. (The Gentzen systems Glc,G1m,Gli) Proofs or de-
ductions are labelled finite trees with a single root, with axioms at the top
nodes, and each node-label connected with the labels of the (immediate) suc-
cessor nodes (if any) according to one of the rules. The rules are divided into
left- (L-) and right- (R-) rules. For a logical operator CI say, LC1, RC indicate
the rules where a formula with ® as main operator is introduced on the left
and on the right respectively. The axioms and rules for Glc are:
Axioms

         Ax A           A                           L± J.=
Rules for weakening (W) and contraction (C)
                F       A
         LW                                         RW
              A, I'      A

              AAr                                            A,A,A
         LC
               A,           A
                                                    RC
                                                          FA,A
Rules for the logical operators
                  Ai,           A                            A, A       F        A,B
         LA                             (i = 0,1)   RA
              A c, A                A

              AFL                   B,r                                     (t = 0,1)
                                                                             .
         LV
                      AVB,FA                        RV
                                                          FA,A0VAI.
         L> rA,A                                    R-4    A'rA,B
                      A --+               A                   A --+ B

              A[x       F       A                              A[x y]
         LV                                         RV
62                                                    Chapter 3. Gentzen systems

          L3
               A[xI y],F    A
                                           RA
                                                  r. A, A[x1 t]
                ]xA,F      A                      F       A, 3xA


where ih 1.2, RV, y is not free in the conclusion.
  The variable y in an application a of RV or L3 is called the proper variable
of a. The proper variable of a occurs only above a.
     In the rules the r, A are called the side formulas or the context. In the
conclusion of each rule, the formula not in the context is called the principal
or main formula. In a sequent F          A r is called the antecedent, and A
the succedent. The formula(s) in the premise(s) from which the principal
formula derives (i.e. the formulas not belonging to the context) are the active
formulas. (Gentzen calls such formulas "side formulas", which rather suggests
an element of the context.) In the axiom Ax, both occurrences of A are
principal; in L_L the occurrence of I is principal.
   The intuitionistic system Gli is the subsystem of Glt obtained by re-
stricting all axioms and rules to sequents with at most one formula on the
right, and replacing L--* by

                                FA         B, F       A


Glm, the system for M, is G1i minus LI. Note that, due to the absence
of LI, every sequent derivable in Glm must have a non-empty succedent,
i.e., the succedent consists of a single formula. (This is straightforward by a
simple induction on the depth of deductions.)
   For the possibility of restricting the active formulas in Ax to prime A, see
3.1.9.


3.1.2. DEFINMON. As for N-systems, a convenient global assumption for
deductions is that the proper variables of applications of L3 and RV are kept
distinct; this is called the variable convention.
  If moreover the free and bound variables in a deduction are kept disjoint,
the deduction is said to be a pure-variable deduction.We shall usually assume
our deductions to satisfy the pure-variable condition


3.1.2A. * Show that each deduction may be transformed into a pure-variable
deduction.


3.1.3. EXAMPLES. (Some proofs in Gle,G1m) We have not explicitly in-
dicated the rules used. The following two deductions are in Glm:
3.1. The G1- and G2-systems                                                                                63

                                                                                         B        B
                                                                AA A,BB
          B       B           AA                             AA A,A+BB
        AABB AABA                                                 A, A
                                                                 A-4(A.13)
                                                                               (A + B)
                                                                                       A+B
                                                                                              B
               AABBAA
               (A A B)        (B A A)                            (A --+ (A --+ B))       (A

The fact that more than one formula may occur on the right enters essentially
into certain classical proofs, for example the following two deductions in Glc
(the left deduction derives Peirce's Law, in the right deduction x FV(B)):
                                                         Ax    Ax
              P                                         Ax    Ax,B                       B        B
                                                         Ax, Ax   B                       Ax          B
                                                        Ax,]x(Ax B)                  B     Ax  B
   (P + Q) P P                                      VxAx,3x(Ax --+ B)              B    ]x(Ax + B)
    ((P Q)  P) P                                            (VxAx --+ B)          3x(Ax    B)

It not difficult to see that there are no proofs of the conclusions if we admit
only sequents with at most one formula on the right.
   The use of the contraction rule in the following two deductions (the left
one is a deduction in Glm, the right one is a deduction both in Glc and
G1i) cannot be avoided:
    P     P            1      1
                      P, 1     1
   P,(P V ,P)
   (P V
                       _L     _L

                                                        1    1
                                                                                 PP
                                                                                  P,P
 (P V ,P)        P V LP (P V ,P)                             _L , _L      _L
                                                                                  PA
          (P V P) _L, (P V ,P) > 1
                                                                  LC
                      (P V P)            _L        _L                                                     LC
                       ((P V ,P)              1)        1

3.1.3A. 4 Prove in Glm A                       A for arbitrary A from atomic instances P                   P.

3.1.3B. 4 Give sequent calculus proofs in G1m of
          AAB-4A,                                   A(B(AAB)),
          A > AV B, B               AV B,
          (A V B        C)         ((A        C) A (B         C)),
          A       (B > A),
          (A      (B        C))      ((A           B)       (A         C)),
          VxA         A[xlt], A[x                  3xA.


3.1.3C. 4* Prove in Gli that ( ,.4
64                                                      Chapter 3. Gentzen systems

3.1.3D. 4* Give sequent calculus proofs in Glc of
         (A   3xB)    3x(A          B) (x Ø FV(A))
         3x(Ax    VyAy),
         (A   B) V (B    A).

3.1.4. NOTATION. Some notational conventions in exhibiting deductions in
sequent calculi:

      Double lines indicate some (possibly zero) applications of structural
      rules.

      In prooftrees the union of finite multisets F, F', F", ... of formulas is
      indicated simply by juxtaposition: FF'F", or the multisets are separated
      by commas for greater readability: F, F', F". The union of a multiset F
      with a singleton multiset {A} is written FA or F, A.
      In prooftrees An stands for a multiset consisting of n copies of A; so A°
      is the empty multiset.

3.1.5. REMARK. Context-sharing and contextfree rules. In the two-premise
rules, the contexts in both premises are the same (exception: succedent of in-
tuitionistic L>, because of the restriction to at most one formula in the succe-
dent). Rules with such a treatment of contexts are called context-sharing.
But because of the presence of the structural rules of contraction and weak-
ening, equivalent systems are obtained if some or all of these context-sharing
rules are replaced by context-independent (non-sharing, context-free) versions,
where the contexts of both premises are simply joined together. For example,
the context-independent versions of L-4 and RA are
             F    A, A       F',B            r       A, A      r    B,
                                                            AA B,   A'
To see that the two versions of say RA are equivalent, consider

         FA                    F'     B' W            r AA F BA
       IT'       AAA'
                         W
                             IT'      BAA'             rr (A A B)AA
                 rr      (A A B)AA'                     r (A B)A
   If we replace in Glc the rule L--> by its non-sharing version, the intuition-
istic version may be obtained by simply restricting attention to sequents with
at most one formula on the right everywhere.
   For "non-sharing" and "sharing" sometimes the terms multiplicative and
additive respectively are used. This terminology derives from linear logic,
where the distinction between sharing and non-sharing versions of the rules
3.1. The GA.- and G2-systems                                                 65

is crucial; the terminology was suggested by consideration of a particular type-
theoretic model of linear logic (Girard domains). However, "context-free" and
"context-sharing" as defined above apply to rules with more than one premise
only, whereas "multiplicative" and "additive" also apply to rules with a single
premise (see 9.3.1); hence, in chapter 9 the meaning of "context-free" and
"context-sharing" will be extended and equated with "multiplicative" and
"additive" respectively.


3.1.6. The systems G2[mic]. Due to the weakening rules, we obtain an
equivalent system if we replace the axioms by the more general versions:

                           r,A -A,A        _1_,r,A
This suggests consideration of:


DEFINITION. G2c is the system obtained from Glc by taking the general-
ized axioms and leaving out the weakening rules. The intuitionistic system
G2i is the subsystem of G2c obtained by restricting all axioms and rules to
sequents with at most one formula on the right. G2m is obtained from G2i
by dropping the rule LI.                                                  [E]



As for Glm, all sequents derivable in G2m have a single formula in the
succedent.


3.1.7. PROPOSITION. (Depth-preserving weakening, equivalence of Gl- and
G2-systems) Let us write I-- r A if there is a deduction of depth at most
n. In G2[mic],
                      if hn r     A then 1--n IT'    AS
where IAA'l < 1 for G2[mi]). As a consequence,

                  Gl[mic] H r       A iff G2[mic] h r     A.



PROOF. By induction on the length of derivations. Or, starting at the bottom
conclusion, and working our way upwards, we add In' and A' to the left and
right side of sequents respectively, except when we encounter an application
of intuitionistic L>, where we add l'' in both premises, but A' in the right
premise only.                                                                 E
(Essentially) the same proof works for the other systems we shall consider in
the sequel. The proof of the next lemma is left to the reader.
66                                                      Chapter 3. Gentzen systems

3.1.8. LEMMA. (Elimination of empty succedents) If r            A is provable
in G2[mi], then there is a proof which exclusively contains sequents with a
single formula on the right. If r   is provable, then there is also a proof of
r      A, for any A.
     If r   A is provable in Gli, it is also provable in Gli*, a system obtained
from Gli by replacing the axiom L_L by the set of axioms 1        B. The
formula B may be restricted to being prime (in fact, even to atomic, since
1,r         J.. is an instance of Ax).


3.1.8A. * Carry out the proof of the preceding lemma

3.1.9. PROPOSITION. (Restriction to prime instances of axioms) The A in
the axioms of G[12][mic] may be restricted to prime formulas, while 3.1.7
stays true under this restriction. In the systems G2[mic] the formulas in r, A
in the axioms may also be assumed to be prime, but with these restrictions
proposition 3.1.7 does not hold.                                             El


3.1.9A. 4 Prove the proposition.

3.1.10. REMARK. We can also restrict the wdom Ax to the case that A is
atomic instead of just prime. The special case r, J..    I, A is also an instance
of LJ_ in G2[ic], and is derivable by weakening from LI in G1[ic]. In the
systems for minimal logic, we have to add 1        J_ or r,


3.2         The Cut rule
The systems introduced so far, namely G[12][mic], all obey the subformula
property: in any deduction of a sequent r      A, only subformulas of r and A
occur. A consequence of this fact is the separation property for G[12][mic]: a
proof of a sequent r     A requires logical rules only for the logical operators
(.1_ is regarded as a 0-place operator) actually occurring in this sequent. This
is no longer the case when the so-called Cut rule is added. The Cut rule

                                         A, A   A, r'
                             Cutr         rr,   AA'
expresses a form of transitivity of       The A in the instance exhibited is
called the cutformula; an application of the rule Cut is called a cut. We may
add this rule to our systems, but then the subformula property is no longer
valid; the cutformula A in the premises is not necessarily a subformula of a
formula in rr'AA'.
3.2. The Cut rule                                                                67

 There is also a context-sharing version of the Cut rule, also called additive
Cut (left classical, right intuitionistic):
                 FA AF A                                 FA Ar
         CUtcs
                        F         A
                                                 CUtcs
                                                               r     B
It is easy to see that due to the presence of weakening and contraction the
addition of Cut is equivalent to the addition of Cut.
   Do new formulas become derivable by adding Cut? The answer is: not if we
treat formulas modulo renaming of bound variables. The following example
shows that the possibility of renaming bound variables is essential in predicate
logic: without renaming bound variables, we cannot derive VxVy(Ry A Qx)
Qy (R,Q unary relation variables) in Gic or G2c without Cut. To see this,
note that such a proof, say in G2c, ought to have the following structure:
                                        Qt    Qy
                                      Rs A Qt    Qy
                                  Vy(Ry A Qt)       Qy
                              VxVy(Ry A Qx)          Qy
The top can only be an axiom if t y, but this is a forbidden substitution:
t is not free for x in Vy(Ry A Qx). Note that introducing contractions would

not help in finding a proof. On the other hand, with Cut we can give a proof:
                         Qz    Qz
                       By A Qz    Qz
                     Vy(Ry A Qz)    Qz
                    VxVy(Ry A Qx)    Qz             Qy      Qy
                 VxVy(Ry A Qx)           -VzQz     VzQz      Qy
                                                                   Cut
                             VxVy(Ry A Qx)         Qy
The impossibility of finding a cutfree proof is obviously connected with the
fact that the variables can occur both free and bound in the same sequent.
As will be shown later, if we permit renaming so as to keep bound and free
variables disjoint, the addition of the Cut rule becomes conservative.

3.2.1. THEOREM. (Closure under Cut) Any sequent r            A in which no
variable occurs both free and bound, and which is provable in G[12][mic]
Cut, is also provable in G[12][mic].
The proof will be postponed till section 4.1. We note that we can restrict
attention to so-called pure-variable deductions, defined in 3.1.2.

3.2.1A. 4* We form a calculus m-Gil from G1c by changing                 RV to
                            r,A                           A[x/y]
68                                                        Chapter 3. Gentzen systems

Equivalent to m-Gli is the variant m-Gli' with for               RV
                         F, A      B             F      A[xly]
                             A>B                        VxA
Show that the resulting calculi are equivalent to Gli in the sense that Gil H r
V A iff m-Gli r      A iff m-G1i' r       A (where V denotes iterated disjunction;
the empty disjunction is identified with 1). What restriction on R-->, RV in G2c
produces equivalence to G2i and Gli? Hint. Use closure under Cut for Gli.

3.2.1B. 4 If m-Gli      r       A, IAI > 1, and F does not contain V, then m-Gli
  r   A for some A E A. Prove this fact (Dragalin [1979]).

3.2.1C. 4 As a generalization of the preceding exercise, prove the following. Let
r not contain V,. If m-Gli         r   AA', IAA11 > 1, A containing existential
formulas, then m-Gli H       A for some A E A' or m-Gli           A[xlt] for some
3xA E A (Dragalin [1979]).


3.3      Equivalence of G- and N-systems
In this section we establish the equivalence between the N-systems and the
corresponding G-systems. Let us write N[mic] H r       A iff there is a context
r* a u1: A1, , un: An, such that r              , An, and N[mic] H r*        A
in the sequential notation variant (cf. 2.1.8); in other words, I- r      A in
an N-system if there is a prooftree deriving A using the open assumptions in
r; the multiplicity of a formula B in r is equal to the number of inhabited
assumption classes with distinct labels containing occurrences of B.
   Observe that the N-systems are closed under contraction and weakening;
that is to say, if I- FEB     C then I- rB       C, and if I- r     C then
          C. Contraction is achieved by identifying the labels for two dis-
tinct assumption classes containing the same formula B. Weakening may be
achieved as follows. Let D derive A from assumptions r. Then the deduction
(x a "fresh" label)

                                        A EX
                                        AAB
                                          A

derives A from r, B.

3.3.1. THEOREM. G[12][Mi]              Cut H r       A iff N[mi]      r   A.
PROOF. We give the proof for G2i + Cut, Ni. The result for G2m is
contained in that for G2i. Moreover, G1[mi] is equivalent to G2[mi], and
by the closure under Cut, also G1[mi] + Cut is equivalent to G2[mi] + Cut.
3.3. Equivalence of G- and N-systems                                          69

   For the proof from left *to right we use the fact that a sequent F    A
can always be proved by a deduction where all sequents have exactly one
formula in the succedent. The proof proceeds by induction on the depth of a
deduction in G2i; at each step in the proof we show how to construct from a
G-deduction of F A an N-deduction of F'         A for some with Set(P) C
F.
Basis. The base case starts from axioms F, A A or r,±         A, correspond-
ing to deductions consisting of a single node A and deductions respectively.
Induction step. For the induction step, we have to review all the rules. As
ill, we assume that to each deduction D of r A of depth at most k in G2i
+ Cut a deduction TY of r A, F' C Set(r) has been found. The R-rules
correspond to introduction rules in Ni, for example (on the left the sequent
calculus deduction, on the right the corresponding deduction in Ni)


         FA r
          Do                                   TN;        DI
                                 goes to           A B
          FAAB                                     AAB

                                             [A]

          F, A  B         goes to
         F    A*B
                                           A+B
etc. For the L-rules, we have to replace assumptions at a top node by an
E-rule application deriving the assumption. Examples:

                                           AAB
                                              [A]
           A, F    C          goes to
         AAB,FC                               D*




                                                     A -4 B      A
         FA r,B
          Do
                             C      goes to                [B]
          A* B, r        c

etc. Cut is treated by substitution:
                                                    D;
          Do
               A PA       B        goes to
                                                    [A]

               FF'B
For the direction from right to left, we use induction on the depth of prooftrees
in Ni.
70                                                                     Chapter 3. Gentzen systems

Basis. A corresponds to A A.
Induction step. Let us assume that for deductions in Ni of depth at most k,
corresponding deductions D+ in G2i + Cut have been constructed. Again
the I-rules correspond to R-rules in the sequent calculus, for example


        Do        Di
        A         B         goes to            ro,r, A ro,r,                B
         AAB                                       ro,r, AAB
                                                    (ro,r,)
(ro,r) is short for set(ro,r1). The upper double line indicates some (pos-
sibly zero) weakenings; the lower double line refers to some (possibly zero)
contractions. The elimination rules are translated with help of the corre-
sponding L-rule and the Cut rule:

        _L
        A
                  goes to        riFA
                                    JA
                                    D+
                                                             cut
                                                   D+            AA
                                           FAAB AABA Cut
                                                          FA
        AAB            goes to
         A

                                                                            DjE
             Do        Di                                                         A   1    B
        A+B            A        goes to             ro      A -4 /3        A-4 B,ri       B
                                                                   ro,r,     B                 Cut
                                                                 (ro,r,)      B
etc.

REMARK. The step for translating        in the first half of the proof is not
uniformly "economical" as to the size of the translated proof tree, since D;
may have to be copied a number of times. More economical is the following
translation:
                                  [B]x
                                    Dj".

                                      C        x        A -4 B     A
                                B          C


A similar remark holds for the translation of the Cut rule.

3.3.1A. * Complete the proof of the theorem.
S.S. Equivalence of G- and N-systems                                              71

3.3.2. The classical case
DEFINITION, c-equivalence between sequents is the reflexive, symmetric and
transitive closure of the relation R consisting of the pairs ((F    A, A),
(F,        A)) and ((F, A         A), (r        A, ,A)). Thus sequents
F',     e' and F, A',             F',       e are c-equivalent.
   Sequents of the form                     + A) are called stability axioms; "Stab"
is the set of all stability axioms.                                               El


LEMMA. (Shifting from left to right and vice versa)

      IfS, S' are c-equivalent sequents, then G1c+Cut H S iff Glcd-Cut H S';
      in G1i + Cut we have                      A, r    A if H         +
      and H              if H F         A, and also H F        iff H r, A

PROOF. The proof follows from the following deductions:
                                                    F,
                                                               1_ AA
         FA r,
                    J_
                                                    F                F, A   A
              F,                                               --+ A, r   A


                                               r
                                                         r,A
permitting shift of A from left to right,      from left to right, A from right
to left, and    from right to left respectively.

PROPOSITION. Glc + Cut H r        A iff Gli+ Cut + Stab H F' A', where
     A' is c-equivalent to r    A, and A' contains at most one formula.
Hence Glc + Cut H r     A iff Gli + Cut + Stab H1. A.
PROOF. The direction from right to left is proved by a straightforward in-
duction on the length of deductions. The direction from left to right is also
proved by induction on the length of deductions.
  Note that, whenever we can prove in Gli + Cut + Stab a sequent           A'
which is c-equivalent to I'   A, then we can prove in G1i + Cut + Stab all
sequents r"    A" which are c-equivalent to r     A, by the lemma.
  We illustrate two cases of the induction step.
Case 1. The final inference in the proof of I'   A is L>:
                            r       A, A'           B
72                                                         Chapter 3. Centzen systems

By the induction hypothesis we have deductions in Gli + Cut + Stab of
          A and F', B,       apply L-+ and find r, -'A', A B
Case 2. Let the final inference be RV:
                                    F     A, A
                                F       A V B,
By the induction hypothesis we have in Gli+ Cut +Stab a proof of F,
A, from which we obtain a proof of r,      A V B.

REMARK. Inspection of the proof shows that in transforming a deduction D
in Glc + Cut into a deduction in Gli + Cut + Stab, we need only instances
of               A) for formulas A occurring in D.

3.3.3. THEOREM. G[121C + Cut H r             A       iff      Nc    r    A.

REMARK. The proof and the statement of this theorem also apply to all
X-fragments of C for which {->,       C X C {-+, 1, A, V, V, 3}. For fragments
containing       but not 1, we  must  proceed differently. A method which
applies to these fragments is given in Curry [1950], cf. exercise 3.3.3B below.

3.3.3A. 4 Complete the proof of the proposition and theorem.

3.3.3B. 4* (a) For N-systems, let us write I- r A if A can be deduced from
assumptions in I'. Let Nc' be Nc with 1, replaced by the Peirce rule P, defined
in 2.5.2. Show Nc         A iff Nc' I. A.
   In the following two parts of the exercise we extend the equivalence between
N-systems and G-systems to fragments X such that {-q c X c {->., V, A, V, 3}.
Let G be X-G2c + Cut.
       If S a. I' A, A , then a sequent s* I', A A A is called a 1-equivalent
of S; A      A abbreviates B1 -> A, B2     A, . . , B,-, -> A for A -a B1, B2,
                                                 .                             Bn.
Show that any two 1-equivalents 5*, 5** of a sequent 8 are provably equivalent in
G.
       Show that G H r A iff X-Nc' I- I' A. Hint. For the proof from left to
right, show by induction on the depth of deductions in G, that whenever G H 8,
then for some 1-equivalent S* of 8, Ncl F- 8* (Curry [1950]).

3.3.3C. 4 Prove equivalence of Gli with the Hilbert system Hi directly, that is
to say, not via the equivalence of Gli with natural deduction.

3.3.4. From Gentzen systems to term-labelled calculi
In the discussion of term assignments for intuitionistic sequent calculi, the
versions where empty succedents are possible are less convenient. Hence we
S.S. Equivalence of G- and N-systerns                                                      73

consider slight modifications Gli*, G2i* (these are ad hoc notations), where
all sequents have exactly one formula in the succedent (cf. lemma 3.1.8). In
fact, there are two options. In the case of G2i, we can replace I', 1   A,
(IA1 < 1) by the more restricted F,1    A, or we may instead add a rule
         F=i
         FA
Similarly, we may obtain a system Gli* from G1i by replacing i=- by
axioms i =- A, or by a rule as above. For definiteness, we keep to the first
possibility, the modification in the axioms (instead of the addition of a new
rule).
   It is instructive to describe the assignment of natural deduction proofs
to proofs in the sequent calculus in another way, namely by formulating the
sequent calculus as a calculus with terms; the terms denote the corresponding
natural deduction proofs.
   A term-labelled calculus t-G2i corresponding to G2i* may be formulated
as follows. Consider a term t: B with FV(t) = {ui: A1,      , un: An} as repre-
senting a deduction of A1, , An, F        B for arbitrary F. The assignment
then becomes:
         F, u: P     u: P (axiom)                        r, u: 1         E ( u ) : C (axiom)
                         F      t:C                                         Fs:B
                     t[ui/piw]:c
         w: Ao A A1, r                                    r        p(t, s): A A B
         u:A,Fto:C v:B,F                                       r       t:
          w: Av B, r E\ui,v(w, to, to: C                 r      kit: Ao V Ai
         r    t: A         u: B ,F      s:C               u:A,1"   t:B
          w: A > B,F          s[u wt]: C                 F= Au.t: A > B
             u: A[x y], r       t:C                          F=. s: A[x It]
         w:3xA,r               (w, t): C                 F      p(t, s): 3xA
           u: A[x     I'       s:C                       r         t[xI y]: A[x I y]
         w: VxA, F         s[u wt]: C                                Ax.t: VxA
            u: A, v: A, r t:B
         w: A, r t[u, v Iw , w]: B
The w is always a fresh variable.
  The same assignment works for Gli*, where weakening does not change
the term assignment:
                                           r   t: A
                                      r,z:B       t: A
N.B. The obvious map from t-G2i-derivations to derivations in G2i* with
non-empty succedent is not one-to-one, cf. the following two t-G2i-derivations:
74                                                             Chapter 3. Centzen systems
                   x: A,y: A y: A                       x: A,y: A      y: A
                  y: A    Ax.y:A>A                  x: A       Ay.y: A--+A
                    Ayx.y: A-4(A--+A)                   Axy.y: A-4(A---A)
which map to the same derivation in G2i*.
  Note that if the substitutions in the terms are conceived as a syntactical
operation in the usual way, we cannot, from the variables and the term of the
conclusion alone, read off the sequent calculus proof. Thus, for example, the

                  BB  CC
deductions
                                              B                B C=C
                  B,CBAC                                  B,CBAC
                 B,CADBAC                            AAB,CBAC
               AAB,CADBAC                           AAB,CADBAC
produce the same term assignment.
  If we wish to design a term calculus which corresponds exactly to deductions
in a Gentzen system, we must replace the substitution on the meta-level
which takes place in the term-assignment for the left-rules into operations
from which the rule used may be read off.
   In particular, this will be needed in LA, L-4, LV and contraction. So write
let(t:B,s:A) for the result of the operation of "taking s for w in t" (also
called a "let-construct" and written as "let w be s in t"). letw(t,$) denotes
the same as t[w / s], but is not syntactically equal to t[w/s]. Similarly, we
need contrzyz(t) for the result of replacing x and y by a single variable z in t.
The rules LA, L-4, LV and contraction now read:
                   et,: A, r       t: C                                              s:C
     LA                                            L>
          w: A0 A Ai, r              (t, piw): C         w: A>B, r          ietu(s, wt):C

          LV
                   u: A[x      r     s: C
                                                   LC
                                                           u: A, y: A, I'     s: B
               w: VxA,         letu(s, wt): C           w: A, r     contr(s): B
REMARK. Instead of introducing "let" and "contr", we can also leave LC
implicit, that is to say the effect of a contraction on a deduction represented
by a term t(x, y, 2') is obtained by simply identifying the variables x, y instead
of having an explicit operator; and instead of "let" we can treat substitution
operations WE] as an explicit operation of the calculus, instead of a meta-
mathematical operator. If substitution is an operation of the term calculus,
then, for example, t differs from x[x

3.3.4A. * Check that the two proofs of A A B, CAD -BAC above are indeed
represented by distinct terms if we use "let" and "contr".

3.3.4B. 4* Show for the map N assigning natural deductions to derivations in
G2i with inhabited succedent in 3.3.1 that IN(D)1 < c2IDI (c positive integer). For
the full system we can take e = 2, and c = 1 for the system without I.
3.4. Systems with local rules                                                  75

3.3.4C. 4 The following modification of the term assignment corresponds to the
alternative mentioned in the remark of 3.3.1:
                                 t:A        u:B,F       s:C
                          w: A    B,            (Au.$)(wt): C
Adapt also the other clauses of the term assignment, where necessary, so as to
achieve (for t-G2i, without Cut) s(N(D)) < c(s(D)), c a fixed natural number,
and similarly with depth instead of size; here N(D) is the natural deduction proof
assigned to the sequent calculus proof by the procedure.


3.4      Systems with local rules
The following section contains some quite general definitions, which however
will be primarily used for G-systems.

3.4.1. DEFINITION. Deductions (of LR-systems to be defined below) are
finite trees, with the nodes labelled by deduction elements. (Deduction ele-
ments may be formulas, sequents etc., depending on the type of formalism
considered.)
  An n-premise rule R is a set of sequences So, , Sn_i, S of length n + 1,
where Si, S are deduction elements. An element of R is said to be an instance
or application of R. An instance is usually written
                                 Ss    Si         Sni
                                            S
S is the conclusion, and the Si are the premises of the rule-application. Where
no confusion is to be feared, we often talk loosely about a rule when an
application of the rule is meant. An axiom is a zero-premise rule. Instances
of axioms appear in prooftrees either simply as (labels of) top nodes, or
equivalently as deduction elements with a line over them:



In principle, we shall assume that the premises are always exhibited in a stan-
dard order from left to right (cf. our convention for N-systems that the major
premise is always the leftmost one), so that expressions like "rightmost branch
of a prooftree" become unambiguous. (In exhibiting concrete prooftrees, it is
sometimes convenient to deviate from this.)

3.4.2. DEFINITION. A formal system with local rules, or LR-system, is
specified by a finite set of rules; a deduction tree or prooftree is a finite tree
with deduction elements and (names of) rules assigned to the nodes, such
that if So, , Sn_i are the deduction elements assigned to the immediate
76                                                  Chapter 3. Gentzen systems

successors of node y, and S is assigned to the node u, R is the rule assigned
to y, then So,    ,     S belong to rule R. Clearly, the rules assigned to top
nodes must be axioms. The deduction element assigned to the root of the
tree is said to be deduced by the tree. If we consider also deduction trees
where some top nodes vo,      . . do not have names of axioms assigned to
                                  .



them, we say that the deduction tree derives S from So,Si,..., where S is
the deduction element assigned to the root, and So, Si, ... are the deduction
elements assigned to the top nodes which do not have an axiom assigned to.
them.

REMARKS. The rules of an LR-system are local in the sense that the cor-
rectness of a rule-application at a node v can be decided locally, namely by
looking at the name of the rule assigned to v, and the proof-objects assigned
to v and its immediate successors (i.e., the nodes immediately above it). The
G-systems described above are obviously local. The notion of a pure-variable
proof is not local, but this is used at a meta-level only.
   Not all systems commonly considered are LR-systems. For Hilbert systems
the deduction elements are formulas, for G-systems sequents. If we want to
bring the N-systems also under the preceding definition, we can take as deduc-
tion elements sequents F A, where the F is of the form u1: A1,        , un: An,
i.e. a set of formulas with deduction variables attached. The use of this for-
mat frees us from the reference to discharged assumptions occurring elsewhere
in the prooftree.

3.4.3. NOTATION. We write D l-r, S if a prooftree D derives S and has
depth at most n, and 7, hs<n S if 7, derives S and has size most n. We write
Hn  S7 Hs<n S if for some T, we have T, I-n S, T, 1-s<n S respectively. If we
want to stress the dependence on a system T, we wr-ite HT, HT, etc.

3.4.4. DEFINITION. Let T be an LR-system, the rules specifying the system
we call the (primitive) rules of the system. A rule R is said to be a derivable
rule in T, if for each instance So,     , Sn_i, S there is a deduction of S from

the Si be means of the rules of T. That is to say, in this deduction the Si are
treated as additional axioms.
   A rule R is said to be admissible for T (or T is closed under R), if for all
instances So, ... ,Sn_i, S of R it is the case that

        if for all i <n    Si, then I- S.
R is said to be depth-preserving admissible (dp-admissible) for T (or T is
dp-closed under R) if for all m

        if for all i <n Hm Si, then Hm S.
3.5. Absorbing the structural rules                                                       77

An n-premise rule R of T is said to be i-invertible for T [i-dp-invertible for
TI if the rule

                {(S, Si)   :   (So, .       ,   Sn_i, S) E R}

is admissible [dp-admissible]. R is invertible [dp-invertible] if R is i-invertible
[i-dp-invertible] for all 0 < i < n.
   For two-premise rules, we may also use left-invertible, right-invertible for
0-invertible and 1-invertible respectively.                                      El



3.5      Absorbing the structural rules
We now consider Gentzen systems in which not only weakening but also
contraction has been "absorbed" into the rules and axioms: the family of G3-
systems. This has advantages in an upside down search procedure for proofs
of a given sequent. (See also 4.2.7.)
  A number of results in this section involve the notion of depth of a proof;
but the proofs go through if we use the notion of size of a proof instead.

3.5.1. DEFINITION. (The Gentzen systems G3c, G3m, G3i) The system
G3c is specified by the following axioms and rules:

         Ax P,           A, P (P atomic)                L_L I, 1'     A

                                                                                    A,B
         LA    A'B'r                                    RA
                                                                     FA,AAB
         LV
               A rA                                     RV


         L-4
               rA,A                                     R-4
                                                                Ar      A,B
                    A -4 B,             A

               VxA A[xltb               A                             A[x y]
         LV                                             RV
                  VxA,r         A                                     VxA

               A[x y],          A                                     A[x t], 3xA
         L3                                             R3
                3xA,           A                                         3xA

where in RV, L3 the y is not free in the conclusion.
 The intuitionistic version G3i of G3c has the following form:

         Ax P, r         P (P atomic)                           LI          A
78                                                              Chapter 3. Gentzen systems

           LA
                 ABr-C                                     RA
                                                                 FA             1' =- B
                   '
                A A B,r
                        '
                                C                                    ri4.A./3
                A 1'        C       B,r      C                       FA
           LV
                        AVB,r                              RV
                                                                rA0 vAi (i = 0, 1)

           L+
                 A + B,F            A       B,r   C
                                                           R* r rA -4BB


           LV VxA'
                        A[x/t], r       C                       r     A[x /y]
                       VxA,rC                              RV
                                                                 r     VxA


           L3
                A[x I       r   C                               r    A[x It]
                 ]xA, rC                                   RA
                                                                 r     ]xA

where in L3 and RV the y is not free in the conclusion.
     G3m is G3i with LI left out, and 1, r                 1 added (to compensate for
this missing instance of Ax). Alternatively, one can let the P in Ax range over
prime, instead of atomic formulas; then G3m is simply a restriction of G3i.
Sequents derivable in G3m always have a single formula in the succedent
(just as for Glm and G2m).
  The concepts of principal and active formula occurrence in an inference
are copied from the systems Gl[mic]; but note that in, for example, an
application of LV, only the occurrence of VxA in the conclusion is principal.



3.5.1A. 01 Show that A A is derivable in G3[mic] for arbitrary A. Show that
in Ax, L_L in G3cp all formulas in PA may be taken to be atomic. What goes
wrong for full G3c? And for G3ip?


3.5.1B. 4 Give a proof of Peirce's law ((A            B)        A) > A in the system G3c.


3.5.2. LEMMA. (Substitution of terms) For the systems G[123][mic], if
       r    A, then 7,[x/t] H r[x/t]       A[x/t], provided t is free for x in
r       A and does not contain variables used as proper parameters of L3,
RV. The substitution does not change the size, depth or logical depth of the
proof. Hence, by renaming proper parameters of1,2, RV: if hi,          A then
1,-, r[x/t]  A[x/t] provided t is free for x in r, A.
PROOF. By induction on the depth of proofs.
3.5. Absorbing the structural rules                                                79

3.5.3. LEMMA. (dp-admissibility of weakening) G3[mic] is dosed under
weakening. That is to say, if h is deducibility in G3c, then
         If Hri F        A then
            < 1 for G3[ni].
where IALY1 _
N.B. This lemma is not true if we insist that in Ax, L_L all formulas of F, A
are atomic.

3.5.4. PROPOSITION. (Inversion lemma) Let H be deducibility in G3c.
      If 1-7, A A B, F     A then 1-      B, F
        ITn F      A,A V B then 1-7, F        A,A, B.
      If Hn Ao V A1,rL then Hn Ai, F                A (i E {0, 1}).
      Ifl-n F      A, A0 A A1 then H7, r              (i E {0,1}).
                          B, .6, thenHF,AB,L.
      IfHr,A-BL then I-7, F                   A, A and ka
      1f F,, F      A,VxA then Hn F = 1A[x/y], for any y such that y
      Fv(r, A, A).
      If 1- 2xA,r          A then Hi, A[x I y], r       A, for any y such that y
      Fv(r, A, A).
The properties above, with the exception of (ii) and (vi), also hold for G3 [mi],
under the intuitionistic restriction on sequents. For G3[mi] one half of (vi)
remains provable:

 (vi) If Hr, I', A -> B     C then      F,B      C.

PROOF. The proposition is proved by induction on n. As a typical example,
we prove (vi) for G3c. Assume (vi) to have been proved for n, and all r, A.
Let 1-,i+1 A -> B, F     A by a deduction D. If D is an axiom, then A -> B
is not principal, and r, B    A as well as r     A, A are axioms. If D is not
an axiom and A -4 B is not principal, we apply the IH to the premise(s) and
then use the same rule to obtain deductions of I'    A, A and B, r    A.
   If on the other hand A -4 B is principal, the deduction ends with
         F       A, A      B, r
                 A-* B,r      A
and we can take the immediate subdeduction of premises. Similarly in the
case of G3i, where only the second premise counts, if A -4 B is principal. E
80                                                           Chapter 3. Gentzen systems

3.5.4A. 4 Complete the proof of the inversion lemma.

3.5.5. PROPOSITION. (dp-admissibility of contraction) Let I be deducibility
in G3c. Then we have for all A, r, A
      Him A, A, r        A, then Hn A, r               A.

      If hn F     A, A,A, then F-n r                 A, A.

The first property, under the intuitionistic restriction, also holds for G3 [mi].

PROOF. By induction on n. We consider the first assertion; the second is
treated symmetrically. Let D be a deduction of length n +1 of A, A, r        A.
   If A is not principal in the last rule applied in V, apply IH to the premise.
If A is principal in the last rule applied, we distinguish cases.
 Case I. The last rule applied is LA:
           1r, A,B,A A B,F              A
         F-n+i A A B, A A B, r              A
Apply the inversion lemma to the premise and find a proof of

         hn A, B, A,B, r            A

and use IH twice.
Case 2. The last rule applied is L. Then
         hn r, A[x/y], 3xA          A
         hn+1 r, 3xA,3xA            A
By the inversion lemma, there is a y' such that for some D'
         D' I-7, I', A[x / y], A[x/y1           A,

and y, y' 0 Fv(rA), y' V FV(A[x/y]), y 0 FV(A[x/y1, y # y'. Using the
substitution lemma we may conclude that
         hn r, A[x / z], A[x / z]       A

where z is a fresh variable not occurring free in r, A. Then we apply the
induction hypothesis w.r.t. A[x / z] and find 1-7, r, A[x / z]        A.
Case.3. The last rule applied is LV:
         Hn A, A V B,1"    A     hn B, A V B, r               A
                    Im+1 A V B, AV B, r  A
We use the inversion lemma and apply the induction hypothesis.
3.5. Absorbing the structural rules                                           81

Case 4. The last rule applied is L-4:
            A -> B,r       A, A       I-- A   B,B,       A
                   1-1 A -4 B , A       B,r       A
By the inversion lemma applied to the first premise, I-7, r        A, A, A, and
applied to the second premise I-7, r, B, B        A. We then use the II-I and
obtain 1-, r    A, A and 1--, r, B A, from which F-7,+1 r, A -4 B        A.
  In the case of G3i the treatment is slightly different, but we leave this to
the reader (the occurrence of A      B in the left premise of L--+ makes up for
the missing h-alf of the inversion lemma in this case).
 Case 5. The last rule applied is LV. Immediate.

3.5.6. REMARKS. (i) If A --> B is omitted in the left premise of L-+ of G3i,
the proof of the preceding proposition breaks down at Case 4. A counterex-
ample in the implication fragment is provided by the sequent (P, Q E PV)

         (((P-Q)->Q)- P)-4Q Q-413             Q

We leave it to the reader to check this.
        The inversion lemma may be stated as follows. In G3c, if 1-r, r, A  A
(respectively 1-r, r    A, A) then there is a proof of depth < n + 1 with A as
principal formula, if A is composite, but not of the form VxA' (respectively
composite, but not of the form 3xA'); an appropriate adaptation holds for
G3i.
   It is possible to improve on the result for G3c as follows: we may take
"depth < n" instead of "depth < n + 1", provided we restrict attention to
proofs where all axioms Ax, LI are such that the formulas in r are atomic
or V-formulas, and the formulas in A are atomic or 3-formulas. But we
have to pay a price for this: for this class of proofs, the weakening operation
transforming a proof of r      A into a proof of I', I" A, A' cannot be done
while preserving the depth (a corresponding observation for G[12] [mic] was
made in proposition 3.1.9).
       If we drop the restriction on Ax, that is if we consider G3[mic] + GAx,
where GAx is the axiom schema I', A A, A without restrictions on the A,
we can still formulate a version of the inversion lemma which is sometimes
useful. For example, for G3c + GAx we have the following version of (vi)
of the inversion lemma (3.5.4): if D       l', A -4 B     A and A      ./3 is not
principal in an axiom in D, then hn r       A, A and      r,B A.
3.5.7. PROPOSMON. The dp-admissibility of weakening and contraction,
dp-closure under substitution of terms and the dp-inversion lemma hold for
G3[mic] + Cut.
PROOF. The proof for G3[rnic] readily extends.
82                                                      Chapter 3. Gentzen systems

3.5.7A. 4* Show that the example under (i) of the preceding remarks is indeed
provable in G3i, but unprovable in G3i if A -- B is omitted in the rule L-.

3.5.7B. 4 Show that we can establish the stronger variant of the inversion lemma
under the appropriate restriction on the axioms, as described above.

3.5.8. PROPOSITION. In G3[ic], if H,. F         1, A, then 1-n F      A, A.

PROOF. By induction on n. Let D be a proof of length n of F         1, A. If
D is an axiom, then either I occurs in r, so then r     A, A is an axiom; or
some P occurs in both r and A, and again F A, A is an axiom. If D is not
an axiom, we apply the IH to the premise(s) that the occurrence of 1 derives
from.                                                                           IE



3.5.9. PROPOSITION. (Equivalence) G1c H F               A iff G3c H r      A, and
Gl[mi]H F A iff G3[mi] H F A.
PROOF. Straightforward by closure of G3[ic] under weakening and contrac-
tion. In both directions the proofs proceed by induction on the depth of
deductions.                                                            IE



REMARK. As a corollary to the proof one obtains that

         If Gl[mic] 1-n r        A then G3[mic] 1-n r      A.

But the converse does not hold: for P E PV, P V -,13 has a proof of depth 2
in G3c, but not in Glc. Shortest proofs in Glc, G3c respectively are shown
below:
                           .13    .1D

                          13     P,_L
                            P,P -+ 1_
                                                  P      P, 1
                      .I 3 V -,P, P -> 1_
                                                      P,P -4 1
                                                      PV--,.13
                      PV -,P,PV -,P
                               .13V-iP

3.5.10. Intuitionistic multi-succedent systems
The systems in the following definition are used in 4.1.10 and some of the
exercises only, so the definition may be skipped until needed.

DEFINITION. In 3.2.1A we already encountered a multi-succedent version of
the system G3i. We may also define a multi-succedent version m-G3i of G3i,
in which we keep as close as possible to G3c, permitting whenever possible
3.5. Absorbing the structural rules                                         83

a multiset in the succedent. The system m-G3i is obtained from G3c by
restricting R+ and RV to
                  FA     B
                                      RV
                                           r   A[x/y1
                         B, A              F   VxA, A
where in RV x      Fv(r), y x or y FV(A, F), and L--> is modified into
                  A + B A, A F, B A
         L-4 F'
                       F, A * B       A
The system m-G3m is obtained from m-G3i by omitting the axiom L_L, but
then one has to add F, 1 I, A as an instance of Ax.
  A slight variant of m-G3i, m-G3i', has a left premise in L> of the form
r, A + B     A (no A).                                                       121



  The substitution lemma (3.5.2), the lemma on dp-admissibility of weak-
ening (3.5.3), a suitable version of inversion (3.5.4) and dp-admissibility of
contraction (3.5.5) are valid also for m-G3[mi].
  Intuitionistic multi-succedent systems arise quite naturally in semantical
investigations (cf. 4.9.1).

REMARK. We do not know of a designation of this type of system, that
is completely satisfactory in the sense that it is mnemonically convenient,
consistent, and not cumbersome. The classical systems are always "multi-
succedent" , so there we drop the prefix m-. Also, in a publication where only
multi-succedent G-systems are discussed, the prefix m- is redundant.

3.5.10A. * Check that the substitution lemma, dp-admissibility of wea.kening,
and contraction and a suitable version of inversion are valid for m-G3[mi].

3.5.11. Kleene-style G3-systems
The systems G3[mic] are inspired by Dragalin; the system closest to Dra-
galin's system for intuitionistic logic is m-G3i. Kleene's original systems of
the G3-family differ in one important respect from G3[micl: they are strictly
cumulative, that is to say, if in the classical case r   A is the conclusion of
an application of a rule of the system, then I'      A appears as a subsequent
of the premises of the application; and in the intuitionistic case, if r     A
is the conclusion of a rule-application, then F appears as a sub-multiset of
the antecedents of the premises of the application. In other words, in the
intuitionistic and minimal cases the antecedent can only increase when going
from the conclusion to one of the premises, and in the classical case both the
antecedent and the succedent can only increase.
   Going downwards form premises to conclusion, any formula "introduced"
on the left or on the right (classical case only) is already present in the
84                                                                          Chapter 3. Centzen systems

premises; the active formula(s) in the antecedent and the succedent (in the
classical case) are, so to speak, absorbed into the conclusion.

DEFINITION. (The systems GK[mic]) The rules for GKi are almost the
same as for Kleene's system G3 in Kleene [19524 The subscript i appearing
in some of the rules may be 0 or 1.
     Ax P,F         P (P atomic)                L_L I, r         A

          Ai, Ao A Ahr            C                      A         1'       B
                                           RA
              Ao A Ai, F         C

     LV Aa'Ao v
                    Al, I'        C        Ai, Ao V Ai, F               C                         r        Ai
                             A0vA1,rc                                            RV
                                                                                         1.           Ao V A1

          A--*B,FA                    A         B,B,F        C
                                                                        R-4 A'
                                                                                         I'           B
                           A --+ B, r        c                                                1        B

     LV VxA'
                 A[xlt], r        C
                                           RV
                                                 r       A[xly]
               VxA, r        C                     F      VxA

                                  C               F      A[x It]
     L3 AxA'A[xly],r                        R3
               2xA,r         C                       F    3xA
where in L3 and RV the y is not free in the conclusion. The corresponding
system GKm is obtained by dropping L1_, and adding I, 1"
  The classical system GKc is obtained by extending the cumulativeness of
the rules in a symmetric way to the succedent, and generalizing the axioms
and rules to arbitrary contexts on the right. Thus we have

     RA
          r         Ao, Ao A A,             r    A, Ai, Ao A Ai
                                                                                RV
                                                                                     r            A, Ai, Ao V
                             r            Ao A Al                                        r             Ao V Ai

     R*         F   z,B,A > B                     1.         A[xly], VxA
                    A, A > B
                                            RV
                                                         rz,vxA
etc.
The proof of dp-closure.under contraction for these systems is virtually trivial;
there is no need to appeal to an inversion lemma. But dp-inversion lemmas
for the left rules become trivial (with the exception of left-inversion for L-4),
since each premise is a left-weakening of the conclusion.

3.5.11A. ** Prove the following simple form of Herbrand's theorem for G3[mic]:
if I', A and A are quantifier-free, and 1-n r, VxA  A, then there are     such
that 1-,, r,A[xlti],...,A[xltm]         A. For G3c we also have: if He 1. 3xA
then for suitable t1,     , tm H 1.     A, A[x/ii],  , A[xltm].
3.6. The one-sided systems for C                                              85

3.5.11B. 4 Describe an assignment N of natural deductions to G3i-deductions
in such a way that, for a suitable constant c E IN, IN(D)I < cIDI (cf. exercise
3.3.4C). In fact, we can take c = 8.

3.5.11C. 4 Check that an assignment G of proofs in G3i + Cut to proofs in Ni
can be given such that s(G(D)) < c(s(D)) for some c E IN (in fact we can take
c= 5), and similarly with depth instead of size.

3.5.11D. 4 Prove that m-G3i I- r       A iff G3ii--rvA. (m-G3i was defined
in 3.5.10.)

3.5.11E. 4 Show that if m-G3i H r     A for non-empty A, and r does not
contain V, then for some A E A, m-G3i H r A (m-G3i as in the preceding
exercise).

3.5.11F. 4 Formulate and prove lemmas on dp-invertibility of the rules of the
systems GK[mic].


3.6          The one-sided systems for C
The symmetry present in classical logic permits the formulation of one-sided
Gentzen systems, the Gentzen-Schiitte systems; one may think of the se-
quents of such a calculus as obtained by replacing a two-sided sequent r        A
by a one-sided sequent     -II', A (with intuitive interpretation the disjunction
of the formulas in --,1", A), and if we restrict attention to one-sided sequents
throughout, the symbol        is redundant. Each of the systems G[123]c has
its one-sided counterpart GS[123]. One may also think of "GS" as standing
for "Gentzen-symmetric" , since the symmetries of classical logic given by the
De Morgan duality have been built in.
  In order to achieve this, we need a different treatment of negation. We
shall assume that formulas are constructed from positive literals P, P', P",
R(to,...,tn), R(so,...,s,n) etc., as well as negative literals -,P, --,P', --,P",
           ,t), ... by means of V, A, V, 3. Both types of literals are treated as
primitives.

3.6.1. DEFINMON. Negation -, satisfies --,--,P   P for literals P, and is
defined for compound formulas by De Morgan duality:
       --,(A A B) := (-DA V -13);

       i(A V B) := (-IA A -0);
       -,VxA := 2x--,A;
86                                                              Chapter 3. Gentzen systems

 (iv) -,3xA := Vx---iA.                                                                Z

3.6.2. DEFINITION. The one-sided calculus GS1 (corresponding to Glc)
has the following rules and axioms:

           Ax P,-,13

           RW
                  r             RCr F,A"AA
                 r, A

           RVL
                 F,AVB
                      r A, F,AVB
                             rB
                                rtVR                       RA
                                                                FA     r, B
                                                                'r, A A B
           Rv r, A[x I y]                      A[xI t]
                                      R3 I',
                 r, VxA                   r,3xA
under the obvious restrictions on y and t.
  In the calculus GS2 corresponding to G2c the axiom is generalized to

           r,P, -,P
and the rule W is dropped. Finally, in the calculus GS3, corresponding to
G3c, the axioms are generalized to r, P, --,13 (P atomic), the rules W and C
are dropped and RV, R3 are replaced by

           RV  "
             FAB
            r,AVB
                                      R,3 r'A[x/t]'
                                                r,3xA
                                                         3xA



     The Cut rule takes the form
                     A      A, --,A
           Cut I''
                         r, A                                                          Z
  The letter "R" in the designation of the rules may be omitted, but we have
kept it since all the R-rules of the one-sided calculi are just the R-rules of the
systems G[123]c for sequents of the form        A.

3.6.2A. * Prove an inversion lemma for GS3:
        If 1-n r, A V B then 1-n r, A, B;
        If 1-n r, A A B then 1-n r, A and 1-rt r, B;
        If 1-n r,VxA then 1-n r,A[xly] (y not free in r, and also y az x or y 0 FV(A)).

3.6.2B. * Use the inversion lemma to prove closure of GS3 under contraction.
3.7. Notes                                                                     87

3.7      Notes
3.7.1. General. Some papers covering to some extent the same ground as our
chapters 1-6 are Gallier [1993], Bibel and Eder [1993]. For an introduction
to Gentzen's work, see M. E. Szabo's introduction to Gentzen [1969].


3.7.2. Gentzen systems; the calculi Glc, G1i. Gentzen gave formulations
for classical and intuitionistic logic; but, as already mentioned in the preceding
chapter, Johansson [1937] was the first to give a Gentzen system for minimal
logic.
  Gentzen's original formulation LK differs from the subsystem Glc in the
following respects:
     Instead of a primitive constant 1_, Gentzen uses a negation operator
with rules

              F     A, A
                               It-,
                                       Ar       A
                  F    A              F

       In Gentzen's system, sequences instead of multisets were used; accord-
ingly there were exchange or permutation rules (cf. 1.3.7):

         LE   r" AB
              r, B,A,      A
                                      RE
                                           r        B, A, A'

      For L>, Gentzen used the non-sharing version.
      Gentzen defined his systems so as to include the Cut rule, whereas we
have preferred to take the systems without Cut rule as basic.
  LK is equivalent to Glc which may be seen as follows. If we define I :=
AA     for some fixed A, we can derive I  in Gentzen's system:

                                       AA
                                      A, ,./4
                               AAA,ALA
                                                     LA
                                                     LC
                                  AA-1A

Conversely, defining A := A > I as usual, we obtain in Glc the rules for
    and      as a special case of L--+ and by an application of RW followed by
R> respectively.
  Kleene [19521)] gives the rules for Glc and Gli as in this text. G1[ic]
+ Multicut (where "Multicut" is a generalization of the Cut rule, defined in
4.1.9) is nearly identical with the G2-systems in Kleene [19524
88                                                 Chapter 3. Gentzen systems

3.7.3. The calculi G[23][mic]. As explained in the introduction to this chap-
ter, the calculi G2[mic] serve only as a stepping stone to the more interesting
systems G3[mic].
   The systems G3[mic] as presented here are inspired by Dragalin [1979], but
are not quite identical with Dragalin's systems. The form of the rules LA and
RA was first used in a sequent calculus for classical logic by Ketonen [1944].
   Our G3c corresponds indeed to Dragalin's classical G-system, except that
Dragalin has as an additional primitive. Dragalin's intuitionistic G-system
corresponds most closely to m-G3i, with as an additional primitive. In a
letter to H. A. J. M. Schellinx, dated 22-11-1990, Dragalin points out that
instead of the form of L> in the intuitionistic system proposed in his book,
the following form is preferable:
         A     B, r    A,       B, r    A
                  A + B,r      A
One of the advantages mentioned by Dragalin is dp-invertibility of this rule
with respect to both premises.
   The differences between our systems GK[mic] and the G3-systems formu-
lated in Kleene [1952a] are the following.
      In Kleene's systems, is primitive, not I.
       The rule LA has in Kleene's intuitionistic system the form
                         Ao A Ai   B
        LA   r' Aor: Ai'
                     AoA Ai      B
and similarly for RV and LA in the classical system.
       Kleene wished to interpret these rules so that for every instance of a
rule



any instance



with Set(r) = Set (r), Set(r) = Set(r), Set() = Set() and Set(A) =
Set('), is also an application of the rule.
  In other words, by the convention under (iii) the premises and conclusions
of the rules may be read as finite sets, with rLA short for ruAu {A}, etc.
  It is perhaps worth pointing out that this means for, say, LA that if we
write the premise as A, B, A A B, r with A, B,AAB r, then the conclusion
may be any of the following:

             AAB,r A,AAB,r B,A A                   A,B,A A B,r.
3.7. Notes                                                                   89

(The last possibility is actually redundant, since it results in repetition of
the premise.) Our reason for deviating from Kleene as mentioned under (ii)
above arises from the fact that the version presented here is in the case of
GKi better suited for describing the correspondence between normal natural
deductions and normal sequent calculus proofs, to be discussed later.
   Pfenning [1994] has recently described a computer implementation of cut
elimination for Kleene's G3-systems combined with context-sharing Cut.
   The semantic tableaux of Beth [1955], and the model sets of Hintikka [1955]
are closely connected with G3-systems. See also 4.9.7.
   Hudelmaier [1998, p. 25-50] introduces a generalized version of the notion
of a multi-succedent G3-type system; for the systems falling under this defi-
nition, cut elimination is proved.

3.7.4. Equivalence of G-systems and N-systems. The construction in 3.3.1
of G-deductions with Cut from N-deductions is already found in Gentzen
[1935]. The construction of a normal N-deduction from a cutfree G-deduction
is outlined in Prawitz [1965, App. A, §2]. As to the assignment of cutfree G-
deductions to normal N-deductions, see section 6.3.

3.7.5. Gentzen systems with terms. The assignment of typed terms to the
sequents in a sequent calculus proof is something which might be said to be
already present, for the case of implication logic, in Curry and Feys [1958,
section 9F2], and follows from proofs showing how to construct a natural
deduction from a sequent calculus proof, when combined with the formulas-
as-typ es idea.
  For a bijective correspondence between deductions in a suitable Gentzen
system and a term calculus, less trivial than the one indicated at the end of
3,3.4, see, for example, Herbelin [1995].
  Vestergaard [1998b,1998a] studies implicational G3-systems where the de-
ductions are represented as terms, as in the paper by Herbelin mentioned
above; the Cut rule is interpreted as an explicit substitution operator. The
steps of the cut elimination procedure (the process of cut elimination is dis-
cussed in the first part of the next chapter) recursively evaluate the sub-
stitution operator. Vestergaard's results seem to indicate that -->Gam is
computationally better behaved than -->G3m; for (his version of) the latter
calculus Vestergaard presents an infinite sequence of deductions which (intu-
itively) represent distinct deductions but are mapped to the same deduction
under cut elimination. Recent work by Grabmayer [1999] indicates that the
results are highly sensitive to the precise formulation of the rules and the cut
elimination strategy.

3.7.6. Inversion lemmas. Ketonen [1944] showed the invertibility of the
propositional rules of his Gentzen system (using Cut, without preservation
90                                                   Chapter 3. Gentzen systems

of depth). An inversion lemma of the type used in our text first appears
in Schiitte [1950b], for a calculus with one-sided sequents. Schiitte does not
explicitly state preservation of depth, but this is obvious from his proof, and
in particular, he does not use Cut for showing invertibility. Curry [1963] con-
tains inversion lemmas in practically the same form as considered here, with
explicit reference to preservation of (logical) depth and (logical) size.
   Related to the inversion lemmas is the so-called "inversion principle" for
natural deduction. This principle is formulated by Prawitz [1965] as follows:
the conclusion of an elimination does not state anything more than what
must already have been obtained if the major premise had been obtained by
an introduction. This goes back to Gentzen [1935, §5]: "The introductions [of
M] represent, as it were, the 'definitions' of the symbols concerned, and the
eliminations are no more, in the final analysis, than the consequences of these
definitions." The term "inversion principle" was coined by Lorenzen [1950].

3.7.7. The one-sided systems. Gentzen systems with one-sided sequents for
theories based on classical logic were first used by Schiitte [1950b]. Schiitte
has negation for all formulas as a primitive and writes iterated disjunctions
instead of multisets. The idea of taking negation for compound formulas as
defined is found in Tait [1968]. Tait uses sets of formulas instead of multisets.
Because of these further simplifications some authors call the GS-calculi "Tait
calculi".
  In the paper Rasiowa and Sikorski [1960] a system similar to GS3 is found;
however, negation is a primitive, and there are extra rules for negated state-
ments. For example, --,(A V B) is inferred from -IA and la In addition there
is a rule inferring     from A. The inspiration for this calculus, which is
halfway between the calculi of Schiitte and Tait, derives from the ideas of
Kanger and Beth, in other words, from semantic tableaux.

3.7.8. Varying Gentzen systems. In the literature there is a wide variety of
"enrichments" of the usual Gentzen systems as described in this chapter. We
give some examples.
       Gentzen systems with head formulas. Sequents take the form r; =.
A; A'; the formulas in PA are treated differently form the formulas in riA'.
An example is given in 6.3.5, where sequents of the form II; I'        A with
1111 < 1 are considered. In this example, if 11; r      A has been obtained
by a left rule, 1111 = 1 and the formula in II is principal. See also 9.4 and
Girard [1993].
      Gentzen systems with labelled formulas. Extra information may be
added to the formulas in sequents; the term-labelled calculus described in
3.3.4 is an example.
       Hypersequents are finite sequences of ordinary sequents:
        ri          r2
3.7. Notes                                                                     91

Hypersequents were first introduced in Pottinger [1983] for the proof-theoretic
treatment of certain modal logics, and have been extensively used and studied
in a series of papers by Avron [1991,1996,1998]. They can be used to give cut-
free formulations not only of certain modal logics, but also for substructural
and intermediate logics. (In substructural logics the structural rules of weak-
ening and contraction are not generally valid, intermediate logics are theories
in the language of propositional logic or first-order predicate logic, which are
contained in classical logic and contain intuitionistic logic.) An interesting ex-
ample of an intermediate logic permitting a cutfree hypersequent formulation
is the logic LC, introduced in Dummett [1959]; a Hilbert-type axiomatization
for LC is obtained by adding axioms of the form (A + B) V (B + A) to
Hip.
  The hypersequent formulation CLC of LC (Avron [19911) uses sequents
with a single formula in the succedent, and

        ri       Ai I      I r.    An

is interpreted as

         (A ri          Ai) v     v (A rn    An).

A typical rule of GLC is the "commutation rule" showing interaction between
various sequents in a hypersequent:

         E1Ir1A1E                   E2 I r2    A2 I EI2
             Ei E2 I Pi         A2 E2    Al I E1 Elz

where E1E2, E, E12 are hypersequents. (If E1E27 E, E/2 are empty, r1 a A17
F2     A2, this immediately yields (A1 > A2) V (A2 -4 A1) on the interpreta-
tion.)
        Labelled sequents. Instead of labeling formula occurrences, we may
also label the sequents themselves. An example is Mints [1997], where the
sequents in hypersequents are labelled with finite sequences of natural num-
bers. Mints uses this device for a cutfree formulation of certain propositional
modal logics. The indexing is directly related to the Kripke semantics for the
logics considered.
       Display Logic. This is a very general scheme for Gentzen-like systems,
introduced by Belnap [1982], where the comma in ordinary sequents has been
replaced by a number of structural operations. Mints [1997] relates Display
Logic to his hypersequents of indexed sequents, and Wansing [1998] shows
how formulations based on hypersequents may be translated into formalisms
based on display sequents. See furthermore Belnap [1990], Wansing [1994].
