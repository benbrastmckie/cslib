# Structural Proof Theory — Chapter 5: Variant Sequent Calculi (lines 4314-6063)

5.1. SEQUENT CALCULI WITH INDEPENDENT CONTEXTS

The motivation of the rules of sequent calculus from those of natural deduction
in Section 1.3 produced rules with independent contexts: Two-premiss rules had
                                                                                  87
88                     STRUCTURAL PROOF THEORY

contexts that were added together into the context of the conclusion. In later
chapters we used shared contexts in order to obtain calculi that do not need the
rule of contraction and for purposes of proof search.
   We present two calculi with independent contexts, analogous to Gentzen's
original calculi LJ and LK in that weakening and contraction are primitive rules,
and establish their basic properties.
   A long-standing complication in the proof of cut elimination is removed by
a more detailed analysis of derivations: Gentzen in his 1934-35 proof of the
"Hauptsatz" for sequent calculus, or cut elimination theorem, had to hide con-
traction into one of the cases. If the right premiss of cut is derived by contrac-
tion, the permutation of cut with contraction does not move the cut higher up
in the derivation. The rule of multicut permits eliminating m ^ 1 occurrences
A , . . . , A = Am of the cut formula in the right premiss in one step:
                            V => A              Am,A=>C
                                                       -Cut*
                                    r , A =>• c
The reason for having to make recourse to this rule is the following: Consider the
derivation
                                        A, A, A => C
                                                        Ctr
                            r => A          A, A => c

Permuting cut with contraction, we obtain

                                 r => A A , A , A ^ > C
                                                       -Cut
                      T=^A           A,T, A = ^ C
                                                          Cut
                               r, r, A => c
                                p   A   ^   c    Ctr

Here the second cut is on the same formula A and has a sum of heights of
derivations of the premisses not less than the one in the first derivation. With
multicut, instead, we transform the derivation into

                            r =* A        A2, A =* c
                                                    Cut*
                                    r , A =>• c
Here the height of derivation of the right premiss is diminished by one. A proof
of multicut elimination can be given by induction on the length of the cut formula
and a subinduction on cut-height. The proof consists of permuting multicut up
with the rules used for deriving its premisses, until it reaches logical axioms
the derivation started with, and disappears (see, for example, Takeuti 1987). A
calculus with multicut is equivalent to a calculus with cut, in the sense that the
same sequents are derivable. Ordinary cut is a special case of multicut, so that cut
elimination follows from elimination of multicut.
                      VARIANTS OF SEQUENT CALCULI                               89

   We shall give proofs of cut elimination without multicut for an intuitionistic
single succedent and a classical multisuccedent calculus. These can be consid-
ered standard calculi when contexts in rules with two premisses are treated as
independent.

(a) Cut elimination for the intuitionistic calculus: In the proof of cut elimi-
nation without multicut, the problematic case of contraction is treated by a more
global proof transformation by cases on the derivation of the premiss of contrac-
tion. The proof is given for a sequent calculus with independent contexts, GOi,
with the following rules:

                                      GOi
   Logical axiom:
   A^    A
   Logical rules:

                                                       -/?&
   A&B, r =» c                        r, A =• A&B
   A,r^c      #, A = > C              r => A
                            Lv
     Av5,r,A^c                    r=^Av#* V l
   r^A  5,A^C                       A,r^5
                                                  RD
             ,T,A4C              T ^ AD B
          : L±


   A(t/x), T ^C                   r =>• A(y/x)
                     LV
    V * A , r =^ c                 r > wA RV
         ), r =>. c               r         (/)
          rc                       r 3 A
   Rules of weakening and contraction:



The variable restrictions in RV and L3 are that y is not free in the conclusion. In
the derivations below, Ctr* will indicate repeated contractions.
   To prove the admissibility of cut, formula length and cut-height are defined
as before. The proof of cut elimination is organized as follows: We first con-
sider cases in which one premiss is an axiom of form A =>• A or the left pre-
miss a conclusion of L_L, then cases with either premiss obtained by weakening.
Next we have cases in which the cut formula is principal in both premisses and
cases in which the cut formula is principal in the right premiss only. Then we have
90                     STRUCTURAL PROOF THEORY

the case that both premisses are derived by a logical rule and the cut formula is not
principal in either. The last cases concern contraction. Cut elimination proceeds
by first eliminating cuts that are not preceded by other cuts. The following lemma
will be used in the proof:

Lemma 5.1.1: The following inversions hold in GOi:
  (i) If A&B, F => C is derivable, also A,B,T ^ C is derivable.
  (ii) IfAvB,T^Cis           derivable, also A, F =^ C and B,T => C are deri-
        vable.
  (iii) If A D B, F =>• C is derivable, also B,V => C is derivable.
  (vi) If T =$> VxA is derivable, also F =>• A(t/x) is derivable.
  (v) If 3xA, F =» C w derivable, also A(t/x),F => C is derivable.

Proof: In each case, trace up from the endsequent the occurrence of the formula
in question. If at some stage the formula is principal in contraction, trace up from
the premiss both occurrences. In this way, a number of first occurrences of the
formula are located, (i) If a first occurrence of AScB is obtained by weakening,
weaken with A and with B and continue as before after the weakenings until either
a derivation of A, B, F => C is reached or a step is found in which a contraction
on A&B was done in the given derivation. In the latter case, the transformed
derivation will have A, A, B, B in place of A&B, A&B, and a contraction on
A and on B is done and the derivation continued as before. If a first occurrence
A&B is obtained by an axiom A&B =$> A&B, the axiom is substituted by


                                 A,B^       A&B

and the derivation is continued as before. Otherwise, a first occurrence A&B is
obtained by L&, and deletion of this rule will give a derivation of A, B, F =>• C
as before. For (ii), weakening and axiom are treated similarly as in (i). Otherwise,
the L V rule introducing A v B in the antecedent is


                                A v B, r => C
where F r = F", F r// . Repeated weakening of the premisses gives A, F r =>• C and
2?, F' =>• C , and continuing as before derivations of A, F =^ C and B, F =>• C
are obtained, (iii) is proved similarly to (ii). (iv) If a first occurrence of VxA
is obtained by an axiom, replace it by A(t/x) =>• A(t/x) and then apply LV. If
it is obtained by RV from F r =>• A(y/x), j is not free in F r and, by arguments
similar to the substitution Lemma 4.2.1 for G3i, a substitution of t for x gives a
derivation of F r =>• A(t/x). (v) If 3xA, F =>• C is obtained by L3, the premiss is
A(y/x), F =* C and substitution gives A(t/x), F => C. QED.
                     VARIANTS OF SEQUENT CALCULI                                    91

The lemma gives inversions of the left rules, with shared contexts as in the inver-
sions for the calculus G3i, except that the inversions are not height-preserving.

Theorem 5.1.2: The rule of cut
                              Y => D D, A = » C
                                               -Cut
                                  F, A => C

is admissible in GOi.

Proof: The proof is by induction on length of cut formula with a subinduction on
cut-height. It is sufficient to consider a derivation with just one cut. For all cases,
a transformation is given that either reduces length of cut formula or reduces
cut-height while leaving the cut formula unchanged. We proceed by analyzing
the cut formula and show how to dispense with the cut or replace it by a cut on
shorter formulas. In all the cases in which the cut formula cannot be reduced the
derivations of the premisses of cut are analyzed. There are seven cases according
to the form of the cut formula:

1. The cut formula D is _L. Consider the left premiss of cut Y =>> J_. If it is an
axiom, then the conclusion of cut is the right premiss. If it is a conclusion of LJ_,
then _L is in F and thus the conclusion of cut is also a conclusion of LJ_. Else
F =$> _L is obtained by a rule R with _L not principal in it. If R is a one-premiss
rule the derivation ends with

                             r=»-L
                                                       Cut
                                    r, A
and the rule and cut are permuted into

                                                     -Cut
                                    r , A =• c
                                    r, A =• cR
with reduced cut-height. A similar conversion applies if R is a two-premiss
rule.
2. The cut formula D is an atom P. If the left premiss Y =>• P of cut is an axiom,
then the conclusion of cut is given by the right premiss P , A = ^ C . I f F ^ P i s
a conclusion of L_L, the conclusion of cut is also a conclusion of L_L. If Y =>> P
is derived by a rule, P is not principal in it and cut is permuted with the rule as
incase 1.
  We consider now the cases in which the cut formula is a compound formula.
Observe that if the cut formula is not principal in the last rule used to derive
92                     STRUCTURAL PROOF THEORY

the left premiss, cut can be permuted. If the left premiss is an axiom, the right
premiss gives the conclusion of cut. If the left premiss is a conclusion of L_L, the
conclusion of cut is also a conclusion of L_L. Thus those cases are left in which
the cut formula is principal in the last rule used to derive the left premiss of cut.
3. The cut formula D is AScB. The derivation


                      r, A =* A&B              A&B,     e^c
                                                              Cut
                                  r A 0 c
is transformed by Lemma 5.1.1 into

                                             A&B, 0 =» C
                                                               Inv
                                 A=>£        A,B, 0=»C
                                                              Cut
                      r^A             AA@^C            Cut



Note that cut-height can increase in the transformation, but the cut formula is
reduced.
4. The cut formula D is A V B. The derivation




is transformed by Lemma 5.1.1 into


                                                        /nv
                                           A, A =• c



and similarly if the second Rv rule was used. Length of cut formula is reduced.
  We shall next analyze the case of cut formula 3x A and consider last the cases of
A D B and VA. Because of lack of invertibility, these last cases require a different
analysis.
5. The cut formula D is 3xA. The derivation

                        r => A(t/x)
                                      R3
                                               3xA,A^C
                                                        Cut
                                      ^ ^ c
                    VARIANTS OF SEQUENT CALCULI                                 93

is transformed by Lemma 5.1.1 into
                                         3xA, A =» C
                                                     -Inv
                                              ,A


with length of cut formula reduced.
(5. The cut formula D is A D B. There are three subcases.
6.1. The formula A D J 5 i s not principal in the right premiss, and the last rule
used to derive the right premiss is not a contraction on A D B. In all such cases
cut is permuted with the last rule used to derive the right premiss of cut.
6.2. The formula A D B is principal in the right premiss; thus the derivation is

                    A,T => B          A => A      £,0=^C



and it is transformed into the derivation with two cuts on shorter formulas
                     A=> A A , F =^ B
                                      Cut
                        F,A^B                       B,e^c
                                                             CM
                                   rA@^c
6.3. The right premiss of cut is derived by contraction on A D B. Since LD is
invertible with respect to only its right premiss, we analyze the derivation of the
right premiss of cut. Tracing up this derivation until the rule applied is not a
contraction on A D B, we find a sequent with n copies of formula A D B in the
antecedent:
   If A D 5 is not principal in the rule concluding this sequent, we permute down
the rule through the n — 1 contractions until it concludes the right premiss of cut,
or, if copies of A D B come from two premisses, these are contracted and cut
permuted up with two cuts of reduced cut-height as result.
   If the rule concluding the sequent with n copies of A D B in the antecedent is
weakening with A D B, the weakening step is removed and one contraction less
applied.
   The remaining case is that one occurrence of A D B in the sequent with n
copies of A D B in the antecedent is derived by LD; thus the step concluding the
premiss of the uppermost contraction is
                             A => A    B, & =* C
                                                       -LD


Here (A D B)n~\ 0 = A, 0 ' . The n - 1 copies of formula A D 5 are divided
94                       STRUCTURAL PROOF THEORY

in A and 0 ' with A = (A D B)\ A and & = (A D B)1, 0 " and k + / = n - 1.
Each formula in A and in 0 " is also in 0 . The derivation can now be written,
with Ctrn standing for an n — 1 fold contraction, as

                               (A D B)\ A =» A         5 , (A D £)', 0 " =• C

                      - RD                            ^-^r     —        Or"
                   B                          AD         , ^
                                                               Cut
                               r 0 c
The transformed derivation, with a k — 1 fold contraction before the first cut, is

      A,T ^ B            (A D B)\ A =» A
     r ^ A D / 3         ~A~P £, A =» A Qr*
                                              CM?
                r, A =^ A                              A,r=^#
                                     2
                                    r , A =>• /?                        5 , 0 =>• c
                                                                                      Cut
                                                      r2, A, 0 =» c
                                                                      Or*

where B, 0 =>• C follows by Lemma 5.1.1 from the right premiss of cut. Since
k ^ ft — 1, the first cut has a reduced cut-height. Reduction of k goes on until
k = 0. The other two cuts are on shorter formulas, and finally the contractions in
the end are justified by the fact that each formula of A is a formula of 0 .
7. The cut formula is Vx A. Since RW is not invertible, the derivation of the right
premiss of cut is analyzed.
7.1. The formula Vx A is not principal in the right premiss of cut. As for case 6.1.
7.2. The formula Vx A is principal in the right premiss, and the derivation

                        r=>A(y/x)_             A(;/*),A=>CLV

                                                               Cut


is transformed into
                             r =» A(t/x)     A(t/x), A => C
                                         r, A =>> c
in which the left premiss is obtained by substitution and length of cut formula is
reduced.
7.3. The right premiss of cut is derived by contraction on VxA. As in case 6.3,
we trace up the derivation of the right premiss of cut until a rule that is not a
contraction on WxA is encountered. If the rule is neither LV nor weakening on
VxA, we proceed by permuting the rule down with the contraction steps, thus
                                             VARIANTS OF SEQUENT CALCULI                                                 95

reducing this case to case 7.7. If the rule is weakening on VxA the weakening and
one contraction step are removed and cut-height is diminished. Else the deriva-
tion is

                                                                  A(t/x), (WxA)n~\ A =>C
                                       F =>• A(y/x)                WxA, (WxA)n~\ A =^ C
                                                        -X*               *.     <   ^ ^   c         Ctr"
                                                                                               Cut



This is transformed into the derivation

                                              F => A{y/x)                      A(t/x), Q/xA)n-\ A => C
                                                p       v     A    ^V                                            Or""1
                                                                                                               Cwr
          r =^ A(r/jc)                                            A(t/x), r , A =>• c



in which the premiss F =$> A(t/x) is derivable by Lemma 5.1.1 and the first cut
has a reduced cut-height and the second a reduced cut formula. QED.

(b) Cut elimination for the classical calculus: The rules for the calculus, des-
ignated GOc, are as follows:

                                                                  GOc
   Logical axiom:


   Logical rules:

                                                                    r => A, A r ; ^ A;, 5
                                                                                                        -/?&
   ASLB    ,r          =   >   •       AL"                              r, r=^ A, A;,
   A,F     =   5 , r f => A r
               >   •   A                                                r =^ A , A , 5
                                       7
    A v B, r, F = A, A'
           A, A                            r ' =» A r                   A , F ^ A, 5


                   -L±


   A(f/ac)                         ^A                               F => A, A(y/;c)
    VA;A,r ^                       •   A

   A(y/x,),r ==» A                                                  F =^ A,
96                        STRUCTURAL PROOF THEORY

     Rules of weakening:

               -LW           —   -- L -   -RW
     A,F^A                   F=^A,A
     Rules of contraction:
     A,A,F=^A                F=^A,A,A
                     LC                         RC



The restrictions in the L3 and RW rules are that y must not occur free in the
conclusion.

Lemma 5.1.3: The following inversions hold in GOc:
  (i) If A&B, F =» A is derivable, also A,B,T => Ais derivable.
  (ii) If F =>• A, A&£ w derivable, also F =>• A, A and T => A, B are

     (iii) TjTA V B, F => A w derivable, also A, F =>• A and 5 , F

     (iv) IfT=>A,AvBis          derivable, also V ^ A, A, B is derivable.
     (v) IfADB,r=>Ais           derivable, also B,T =^ Ais derivable.
     (vi) If T => A, AD B is derivable, also A,F ^> A, B is derivable.
     (vii) If F =>• A, VJCA W derivable, also F => A, A(t/x) is derivable.
     (viii) 7/* 3xA, F =>- A w derivable, also A(t/x), F =>> C w derivable.

Proof: (i) Similar to that of Lemma 5.1.1. For (ii), if A&B is obtained by weak-
ening, weaken first with A, then with B. If it is obtained as an axiom, conclude
instead A&B =^ A from A =)> A by weakening with 5 and L&, and similarly
for ASLB => B. If A&# is introduced by /?&, apply repeated weakening instead,
dually to case (ii) of Lemma 5.1.1. (iii) and (iv) are dual to previous, (v) If A D B
in the antecedent is obtained by weakening, weaken with B on left instead. If
A D B is obtained by an axiom A D B =>• AD B, conclude B ^ A D B from
B =>• B by left weakening with A followed by RD. If A D B is obtained by LD,
proof is similar to that of (ii). (vi) If A D B in the succedent is obtained by right
weakening, do left weakening with A and right weakening with B instead. If
A D B is obtained by axiom AD B ^ AD B, conclude A, A D B =>• 5 from
A =>• A and 5 =>• Z? by LD instead. If A D B is concluded by RD, delete the rule.
Proofs for (vii) and (viii) are similar to those above and to those of (iv) and (v) of
Lemma 5.1.1. QED.

With independent contexts, rule LD is invertible with respect to only its right
premiss, in contrast to the previous context-sharing classical calculus G3c that
has all rules invertible. We note that, as with GOi, the inversions of GOc are not
height-preserving.
                       VARIANTS OF SEQUENT CALCULI                                  97

Theorem 5.1.4: The rule of cut
                             r=» A , P D, r=> A',-Cut
                                 r, r=» A, A7
/s admissible in GOc.
Proof: The proof is by induction on length of cut formula and cut-height. All
cases in which the cut formula is not a contraction formula are treated by the
methods used in Theorem 5.1.2. We show the cases in which the cut formula has
been derived by contraction in the right premiss, and the premiss of contraction
is derived by another contraction on the cut formula, until the cut formula is
principal. There are five cases:
1. The derivation is
                                          (A&B)n, T =» A'
                                                              rrn
                                                             Cut


By Lemma 5.1.3, (he sequentsT ==» A, A andT => A, B and A, B, V =» A'are
derivable. The derivation is transformed into one with cuts on shorter formulas,
analogously to case 3.1 of Theorem 5.1.2.
2. The cut formula is A V B. Application of Lemma 5.1.3 followed by cuts on A
or B gives the result, similarly to above.
3. The cut formula is A D B. The derivation is
                         (A D B)k, T" =^ A", A       B,(AD         B)1, T " => A"

                                            AD B,Vf => Af
                                                              Cut


Here (A D B)n~\ V = (A D B)\ T"', (A D fi)z, T /r/ with k + l = n - \ and
A r = A r/ , A //r . All formulas of T r/ and Tm are formulas of Tr and all formulas of
A" are formulas of A 7 .
    By Lemma 5.1.3, the sequents A, V => A , 5 and 5 , F 7 =^ A r are derivable.
We transform the above derivation into
                       (A D B)k, T ;/ =^ A /r , A
 r =» A, A D ^          A D B,r ; / =>      ^\A~WC
                  /r          /r              CM?
             r, r =» A , A , A                     A,r
                         r 2 , r r/ => A 2 , Ar/, g
                                           r2, r, rr/ =^ A 2 , A;, A"
                                                r, r = ^ A, Ar       c
                                                                      *
98                      STRUCTURAL PROOF THEORY

Since k ^ n — 1, the uppermost cut has a reduced cut-height, and the other two
are on shorter formulas. The final left and right contractions C* are allowed by
the inclusion of formulas of F" in F r and A" in A'.
4. The cut formula is VxA. The proof uses Lemma 5.1.3 and is analogous to
case 7.6 of Theorem 5.1.2.
5. The cut formula is 3x A. As for case 4.     QED.


5.2. SEQUENT CALCULI IN NATURAL DEDUCTION STYLE
We give a formulation of sequent calculi "in natural deduction style," with no ex-
plicit rules of weakening or contraction, guided by the following points (compare
also the discussion of weakening and contraction in Section 1.3):

      Discharge in natural deduction corresponds to the application of a
      sequent calculus rule that has an active formula in the antecedent of
      a premiss.
      A vacuous discharge corresponds to an active formula that has been
      obtained by weakening, and a multiple discharge to an active formula
      that has been obtained by contraction.

In an intuitionistic sequent calculus, the rules in question are the left rules and the
right implication rule. Ever since Gentzen, weakening and contraction have been
made into steps independent of the application of these rules. Cut elimination is
much more complicated than normalization, with numerous cases of permutation
of cut that do not have any correspondence in the normalization process. Moreover,
in sequent calculi, because of the mentioned independence, there can be formulas
concluded by weakening or contraction that remain inactive through a whole
derivation. These steps with unused weakenings and contractions do not contribute
anything, and the formulas can either be pruned out (for unused weakening) or
left multiplied (for unused contraction). The calculi we present avoid such steps
with unused formulas altogether.
    In the calculi we give, only those cuts need be eliminated in which the cut
formula is principal in at least the right premiss of cut, or principal somewhere
higher up in the derivation of the right premiss of cut, and the cut is moved up
there in one step. For all other cases of cut, we prove that the cut formula is a
subformula of the conclusion. Therefore the subformula property, Gentzen's orig-
inal aim in the "Hauptsatz," can be concluded by eliminating only those cuts in
which the cut formula is principal in the derivation leading to the right premiss.
The proof of cut elimination uses induction on formula length and the height of
derivation of the left premiss of cut.
                     VARIANTS OF SEQUENT CALCULI                                99

(a) Cut elimination for the intuitionistic calculus: In the detour conversions of
natural deduction, the multiset of assumptions can become changed, in that for-
mulas become multiplied, where zero multiplicity (i.e., deletion) is also possible.
The changed context is called a multiset reduct of the original one:

Definition 5.2.1: If a multiset A is obtained from T by multiplying formulas in
F, where zero multiplicity is also permitted, A is a multiset reduct of Y.

The relation of being a multiset reduct is reflexive and transitive. We also call a
sequent a reduct of another if its antecedent is a multiset reduct. These reducts
are generated by steps of cut elimination in the same way as assumptions are
multiplied in the conversions to normal form in natural deduction.
   The intuitionistic single succedent sequent calculus in natural deduction style
is denoted by GN. As before, multiple occurrence of a formula is denoted by Am.

                                       GN
   Logical axiom:
   A =» A
   Logical rules:

                                            r^A       A > *
    A&£, r => C                               r,
                                              r AA =>> A&B
                                                       A&B
   Am,T^C           g",A=>C
                                  Lv
       A v * r A ^ c
                           T —)                  1             D—)

          B, r, A=>C                        rr=)>ADB
                                              )ADB



   A(t/x)m,r=>c                             r=         ... .
                     LV
    vxA,r^c                                  r       •- • RV
            ,r=^c                           r=
            ^    ^—i3                   —^           _' ' . ' «3


The variable restrictions in RV and L3 are that y is not free in the conclusion.
Rules with exponents have instances for any m, n ^ 0. For example, from L&
with m = 1,ft= 0 we get the first of Gentzen's original left conjunction rules:
                                       A,T =>C
                                                           L&
                                             , r =^ c
We say that formulas A and 5 with exponents are used in the rules of GN.
Whenever m = 0 or n = 0 in an instance, there is a vacuous use, corresponding to
100                      STRUCTURAL PROOF THEORY

weakening, and whenever m > lorn> 1, there is a multiple use, corresponding
to contraction. Since in Gentzen's L& rules m = 0 or n = 0, they contain a hidden
step of weakening.
   The logical rules of the calculus are just like those of GOi, with the exponents in
the rules added. There will be no structural rules. An example shows a derivation
with structural rules in GOi and the corresponding derivation with an implicit
treatment of weakening and contraction in GN:

                   ;Wk
                                       Lv                                 Lv
             Av5,T,A^C                             AvB,F,      A=^C

Many steps of cut elimination lead to a sequent the antecedent of which is a reduct
of the antecedent of the original cut. In usual cut elimination procedures, once the
cut has been permuted up, this original antecedent is restored by weakenings and
contractions following the permuted cut. In our calculus, these are not explicitly
available, but the restriction is not essential. The following proposition shows that
the new antecedent can be left as it is:

Proposition 5.2.2: If in the derivation ofF =>• C in GN+Cut the sequent A =>•
D occurs and if the subderivation down to A => D is substituted by a derivation of
A* =>• D, where A* is a multiset reduct of A, then the derivation can be continued
to conclude F* =>• C, with F* a multiset reduct of F.

Proof: It is sufficient to consider an uppermost cut that we may assume to be the
last step of the whole derivation. First consider the part before the cut, having only
axioms and logical rules. Starting with the derivation of A* =>> D, the derivation
is continued as with A =>• D, save for the steps that use formulas. It is enough
to consider such rules when one premiss is A* =>> D. If in the original derivation
a formula from A was used that does not occur in A*, a vacuous use is made,
and similarly for formulas that occur multiplied with A*, as compared with A, a
multiple use is made.
   It remains to show that the conclusion of cut can be replaced with a
sequent having a multiset reduct as antecedent. Let the original cut concluding
F^Cbe
                             Fi => A        A,F2=>C
                                                    Cut
                                   r r > c
where Fi, F 2 = F, and let the reduced premisses be Fi* =>> A and An, F2* =>- C.
If n = 1, a cut with the reduced premisses will give a conclusion with a multiset
reduct of F as antecedent. If n — 0, the conclusion of cut is replaced by the right
                     VARIANTS OF SEQUENT CALCULI                                  101

premiss. If n > 1, we make n cuts with left premiss I V =>• A in succession and
the conclusion of the last cut has a multiset reduct of F as antecedent. QED.
The proposition shows two things: 1. It is enough to consider derivability in
GN modulo multiset reducts. 2. It is enough to perform cut elimination modulo
multiset reducts.
Definition 5.2.3: A cut with premisses F =>• A and A, A =>• C is redundant in
the following cases:
   (i) r contains A,
   (ii) F or A contains _L,
   (iii) A = C,
   (iv) A contains C,
   (v) The derivation of A, A =>> C contains a sequent with a multiple occur-
         rence of A.
Theorem 5.2.4: Elimination of redundant cuts. Given a derivation of T => C
in GN+Cut there is a derivation with redundant cuts eliminated.
Proof: In case (i) of redundant cut, if F contains A, then A, A is a multiset reduct
of F, A and by Proposition 5.2.2, the cut is deleted and the derivation continued
with A, A =>• C. In case (ii), the conclusion has _L in the antecedent and the
derivation begins with _L =>• C. In case (iii), if A = C, the cut is deleted and the
derivation continued with F =>• C. In case (iv), if A contains C, the derivation
begins with C ^ C.
   Case (v) of redundant cut can obtain in two ways: 1. It can happen that A has
another occurrence in the context A of the right premiss and therefore also in
the conclusion of cut. In this case, the antecedent A, A of the right premiss is
a multiset reduct of F, A and, by Proposition 5.2.2, the cut can be deleted. 2. It
can happen that there was a multiple occurrence of A in some antecedent in the
derivation of the right premiss and all but one occurrence were active in earlier
cuts or logical rules. In the former case, if the right premiss of a cut is A, Af =>> C
and Af contains another occurrence of A, the cut is deleted and the derivation
continued from A' =>• C. In the latter case, using all occurrences of A will give
a derivation of A =>> C. Again, since A is a multiset reduct of the antecedent
of conclusion of cut, the cut can be deleted and the derivation continued from
A =» C. QED.

Redundant cuts (i)-(iv) have as one premiss a sequent from which an axiom or
conclusion of L_L is obtainable as a multiset reduct. In particular, if one premiss
already is an axiom or conclusion of L_L, a special case of redundant cuts (i)-(iv)
obtains.
102                     STRUCTURAL PROOF THEORY

Definition 5.2.5: A cut is hereditarily principal (hereditarily nonprincipal) in a
derivation if its cut formula is principal (is never principal) in some rule in the
derivation of the right premiss of cut.

Proposition 5.2.6: The first occurrence of a hereditarily principal cut formula
in a derivation without redundant cuts is unique.

Proof: Assume there are at least two such occurrences. Then there is a sequent
with a multiple occurrence of the cut formula and the derivation has a redundant
cut as in case (v) of Definition 5.2.3. QED.

A principal cut is the special case of hereditarily principal cut, with the cut formula
principal in the last rule deriving the right premiss. The idea of cut elimination is
to consider only hereditarily principal cuts and to permute them up in one step to
the first occurrence of a cut formula A hereditarily principal in the derivation of
the right premiss.
   It can happen that the instance of a rule concluding a hereditarily principal
cut formula had vacuous or multiple uses of active formulas. These cuts are
hereditarily vacuous and hereditarily multiple, respectively:

Definition 5.2.7: If a hereditarily principal cut formula is concluded by rule L&
andm, n = 0, by rule L v and m = 0 or n = 0, by rule LD, LV, L3 and m = 0,
the cut is hereditarily vacuous. If the formula is concluded by LSL and m > 1 or
n > 1, by L v andm, n > 1, or by LD, LV, L3 and m > 1, a hereditarily multi-
ple cut obtains.

We now prove a cut elimination theorem for hereditarily principal cuts. The proof
is by induction on the length of cut formula, with a subinduction on height of
derivation of the left premiss of cut. Length is defined in the usual way, 0 for _L,
1 for atoms, and sum of lengths of components plus 1 for proper connectives.
Height of derivation is the greatest number of consecutive steps of inference in
it. In the proof, multiplication of every formula occurrence in F to multiplicity m
is written F m .

Theorem 5.2.8: Elimination of hereditarily principal cuts. Given a deriva-
tion ofT^C       with cuts, there is a derivation of F* =>• C with no hereditar-
ily principal cuts, with F* a multiset reduct ofT.

Proof: First remove possible redundant cuts. Then consider the first hereditarily
principal cut in the derivation; we may assume it to be the last step. If the cut
formula is not principal in the left premiss, the cut is permuted in the derivation
of the left premiss, with its height of derivation diminished.
                      VARIANTS OF SEQUENT CALCULI                                  103

   There remain five cases with the cut formula principal in both premisses. In
each case, if a step of cut elimination produces redundant cuts, these are at once
eliminated.
1. Cut formula is ASLB. If m > 0 or n > 0 we have the derivation

                                             Am,Bn,&      => C
                                                                 L&
                                              ASLB, & => C


                       , A => A&B              A&B, ®=>C
                                                              Cut
                                   r A 0 ^ c
We make m cuts with F =>• A, starting with the premiss Am, Bn, 0 ' =>• C", and up
to 5 " , F m , 0 ' =>> C", then continue with n cuts with A =>> 5 , up to the conclusion
F m , A", 0 ' =^ C". Now the derivation is continued as before from where ASLB
was principal, to conclude F m , A n , 0 =>• C, all cuts in the derivation being on
shorter formulas than in the initial derivation.
   If m, n = 0, we have a hereditarily vacuous cut, with 0 r =>• Cr the premiss
of rule L&. It is not a special case of the previous since there is nothing to
cut. Instead, the derivation is continued without rule L& until 0 =>• C is
concluded.
2. Cut formula is A v 5 . With A v B principal in the left premiss, assume that
the rule is RV\ with m > 0:


                                         Av B, Ar , 0 r => C"


                                                               Cut



We make m cuts with F =>• A, starting with the premiss Am , A/ =>• C r , obtain-
ing F m , Ar =>• C r . The derivation is continued as before from where A V B was
principal; where a formula from & was used in the original derivation, there will
be a vacuous use. The derivation ends with F m , A =>• C where A is a multiset
reduct of the context A, 0 of the right premiss of the original cut. All cuts are on
shorter formulas than the initial cut. If in the left premiss the rule was R v 2 and
n > 0, the procedure is similar.
   If m = 0, assuming still that the rule concluding the left premiss is RV\, the
cut is hereditarily vacuous, and, proceeding analogously to case 7, we continue
from the premiss A' =>• C without cuts to a sequent A =>• C where A is by
Proposition 5.2.2 a reduct of F, A, 0 . The other cases of hereditarily vacuous
cuts are handled similarly.
104                    STRUCTURAL PROOF THEORY

3. Cut formula is A D B. With n > 0, the derivation is


                                                                 -LD
                                       A D B, A', ©' => C"




We first cut m times with Af => A, starting with Am, F =>• # , and obtain
r , A /m =>> 5 , then cut with this n times, starting with # w , 0 ' =>> C", to obtain
F n , A /mn , 0 ' =>• C". Continuing, if a formula from A' was used, there will be an
ran-fold use. All cuts are on shorter formulas.
     The case of n = 0 gives a hereditarily vacuous cut handled as in case 1.
4. Cut formula is VJCA. With m > 0 the derivation is

                                         A(t/x)m, A' =>C
                                                   /     7~LW
                                                   :
                     r=>A(y/x)                  ' .
                                                           Cut



In F =>• A(y/x), substitution can be applied as in Lemma 4.1.2 to obtain a deriva-
tion of F =^ A(t/x)\ then m cuts with A(t/x)m, Ar =^ Cr give F m , Ar ^> C The
derivation is continued as before from where WxA was principal.
   If m = 0, the derivation is continued from Af => C\ without LV, to A =>• C.
5. Cut formula is 3xA. With m > 0 the derivation is

                                        A(y/x)m,A'^C


                                                , A =* C
                                                           Cut




In A(y/jc)m, Ar =>• C r , substitution is applied to obtain a derivation of
A(t/x)m ,Af=>C. The rest of the proof is as in case 4. QED.

Corollary 5.2.9: Subformula property. If the derivation ofT^C                has no
hereditarily principal cuts, all formulas in the derivation are subformulas of
r,c.
                     VARIANTS OF SEQUENT CALCULI                                105

Proof: Consider the uppermost hereditarily nonprincipal cut,

                            Ff =» A A, Af => C
                                 T',A'^  C

Since A is never active in the derivation of the right premiss, its first occurrence
is in an axiom A =$> A. By the same, A =$> A can be replaced by the derivation of
the left premiss of cut, F' =>• A, and the derivation continued as before, until the
sequent F', A/ =>• C is reached by the rule originally concluding the right premiss
of cut. Therefore the succedent A is a subformula of F', A! =>• C'. Repeating this
for each nonhereditary cut formula in succession, we conclude that they all are
subformulas of the endsequent. QED.

Theorems 5.2.4 and 5.2.8 and the proof of Corollary 5.2.9 actually give an elim-
ination procedure for all cuts:

Corollary 5.2.10: Given a derivation ofT^C      in GN+Cut, there is a deriva-
tion ofT*^Cin     GN, with F* a multiset redact ofT.

   There are sequents derivable in calculi with explicit weakening and contraction
rules that have no derivation in the calculus GN, for example, A => A&A. The
last rule must be R&, but its application in GN will give only A, A => A&A.
Even if the sequent A =>• A&A is not derivable, the sequent =} A D A&A is, by
a multiple use of A in rule RD.
   The completeness of the calculus GN is easily proved, for example, by de-
riving any standard set of axioms of intuitionistic logic as sequents with empty
antecedents and by noting that modus ponens in the form

                                =^ AD B =• A
                                     =• B

is admissible: Application of LD to A =>• A and B => B gives A D B, A =>• /?,
and cuts with the premisses of modus ponens give =$• B. We also have com-
pleteness in another sense: Sequent calculi with weakening and contraction mod-
ify the derivability relation in an inessential way, for if F =>• C is derivable in
such calculi, obviously there is a derivation of F* =>• C in GN, with F* a multi-
set reduct of F. In particular, if =>• C is derivable in such calculi, it is derivable
inGN.
(b) A multisuccedent calculus: We give a classical multisuccedent version of
the calculus GN, called GM. We obtain it by writing the right rules in perfect
symmetry to the left rules.
106                                                    STRUCTURAL PROOF THEORY

                                                                 GM

  Logical axiom:
   j \    —j?         / \



  Logical rules:
   Am      i    D
                    Tjn      1
                            . 1
                                  1
                                      __>> A     r o
                                                                   F=^A,A m       V =» A', Bn
                                                                                            -R&
         \ &
                #,r
                                       7
                                           A '                         r,r'=» A, Af,
   A m F = > • A B'        Ar
      A V B , r,    > A, A                 r=                         F^A,AVBRV
   F       > A,,V
                7             =^ A'                                Am, T => A, Bn
          A D 5 , r , r ^ A , A ' ~LD                               r^A,ADSD



   A(^/x) m ,F ^ A                                                 F => A,A(j/x) m
    V x A , F ^ A LV                                                F^A,VxA        ^
   A(j/x) m , F =^ A                                               F ^ A, A(^/x)m
    dxA, 1 =>> A                                                     1 =^A,dxA

Compared with the calculus GOc, GM has the exponents in the rules added and
no explicit weakening or contraction.

Proposition 5.2.11: If in the derivation o / F = > A a subderivation of 0 =>• A is
substituted by a derivation of 0* =>• A* wzY/z Z?6tf/z contexts reducts of the original
ones, then there is a derivation o/F* =>> A* wzY/z contexts similarly reduced.

Proof: Similar to proof of Proposition 5.2.2. QED.

A proof of elimination of hereditarily principal cuts and of the subformula pro-
perty is obtained similarly to the results for the single succedent intuitionistic
calculus:

Theorem 5.2.12: Elimination of hereditarily principal cuts. Given a deriva-
tion ofF=^A with cuts, there is a derivation of F* =>> A* with no hereditarily
principal cuts, with F* and A* multiset reducts of F and A.

Theorem 5.2.13: Subformula property. If the derivation of F => A has no
hereditarily principal cuts, allformulas in the derivation are subformulas ofV,A.

Corollary 5.2.14: Given a derivation ofF=>A in GM+Cut, there is a deriva-
tion o/F* =>• A* in GM, with F* and A* multiset reducts ofT and A.
                     VARIANTS OF SEQUENT CALCULI                                107

  The calculus GM is complete for classical logic by the following derivation:

                                                R

                                               -Rv
                                       Av
The instance of RD has m = 1, n = 0, with F empty, A = A, and 2? = _L. More
generally, we obtain the full versions of Gentzen's original left and right negation
rules from LD and RD by suitable choices:
                                       L±
                       A,A     _L =*                 A,T
                                       L



Gentzen had two Rv rules, dually to the two L& rules. We obtain them in GM
by setting m = 1, n = 0 and n = 1, m = 0 in rule /?v, respectively:

                             A, A              r =» A, 5
                    F =* A , A V 5 ^         r =• A , A      Rv

Applications of Gentzen's rules contain, as for the single succedent version, a
"hidden" weakening. It is quite conspicuous in derivations of =>• Av ~ A in his
classical calculus. The last step of the derivation can be only a contraction, doing
away with what the hidden weakenings had brought into the derivation:

                                             -R~
                                                -Rv
                               ==> Av —A,
                                Av ~ A , Av —A
                                   ^ A v A
(c) Correspondence with earlier sequent calculi: By using weakening and con-
traction, derivations in GOi and GOc can be converted into derivations in G3i and
G3c and the other way around. Derivations in GN can be translated into deriva-
tions in GOi by simple local transformations. Only rules that use assumptions
are different, and vacuous uses are replaced by weakenings and multiple uses by
contractions. The translation from GOi to GN consists in deleting the weakening
and contraction steps and in adding the exponents to active formulas in rules that
use formulas from antecedents. If in a derivation of F =>• C in GOi there are no
inactive weakening or contraction formulas, the translation produces a derivation
of F =>• C, and if there are it produces a derivation of F* =>• C, with F* a multiset
reduct of F. The relation between GOc and GM is analogous.
   A direct translation from a derivation of F =>• A in G3c to a derivation in GM is
obtained as follows: First trace all uppermost sequentsofthe forms A, F' =>• A ; , A
and _L, F' => A' and prune the subderivations above each. Next delete F' and A'
from the former and F' from the latter form of sequents, and continue deleting
108                    STRUCTURAL PROOF THEORY

all formulas descending from these contexts. Whenever there is a formula to
be deleted that is used in a rule, a vacuous use is made in GM. The result is
a derivation of F* =>> A* in GM, where F* and A* are multiset reducts of the
original contexts. Similar remarks apply to the single succedent calculi.


5.3.   A N INTUITIONISTIC MULTISUCCEDENT CALCULUS

The propositional part of the intuitionistic multisuccedent calculus G3im is the
same as the classical calculus G3cp, except for the rules of implication. The
left quantifier rules are the same as in G3c, but the right rules are different.
This calculus is due to Dragalin (1988), who called it GHPC (for Gentzen-style
Hey ting predicate calculus). For the propositional part, we show only the two
rules that are different from those of the classical calculus G3c:
                                        G3im
   Rules for implication:
                                               A , F =• B
                                 J —\
                 ,                           T => A,AD B
   Rules for quantifiers:
   A(t/x), VJCA, F => A                        F =• A{y/x)
                          IV                         —       /?V
                                           F ^ A V A
   A(y/x),    r => A                       F =^ A, 3xA, A(t/x)
             T^A                                  T^A3A
The left implication rule has a repetition of the principal formula in the left
premiss; further, its succedent is just A instead of A, A. With the former, the
rules of the single succedent calculus G3i are directly special cases of the rules
of G3im. The rule of right implication has only one formula in the succedent of
its premiss, a feature discussed in the introduction to Chapter 3. However, it is
essential that there be an arbitrary context in the succedent of the conclusion in
order to guarantee admissibility of right weakening.
    The universal quantifier behaves like implication (in a way made exact in type
theory); thus there is a repetition of the principal formula in the premiss of the
left rule and a restriction to one formula in the succedent of the premiss of the
right rule. Variable restrictions are as in the classical calculus.
    To start with the proof theory of the calculus G3im, we need a substitution
lemma:

Lemma 5.3.1: Substitution lemma. IfV=>Ais                derivable in G3im and ift is
free for x in F, A, then T{t/x) =>• A(t/x)      is derivable in G3im, with the same
 derivation height.
                     VARIANTS OF SEQUENT CALCULI                                109

Proof: The proof is analogous to the proof of the substitution lemma for the
calculus G3i, Lemma 4.1.2. QED.

Theorem 5.3.2: Height-preserving weakening for G3im.
  (i) / / \-n F = > A , t h e n \-n D , T ^ A ,
  (ii) / / \-n F =*• A, then hn F =>• A, L>.

Proof: For (i), proceed as in the proof for G3i, Theorems 2.3.4 and 4.2.2. For
(ii) proceed similarly except in the cases in which the last rule is followed by a
rule with a restriction on the succedent of its premiss, i.e., RD or RV. In all such
cases, weakening is absorbed into the downmost occurrence of the rule. QED.

All rules of the intuitionistic single succedent calculus G3i except Rv and R3
are special cases of rules of G3im, and Rv and R3 are easily shown admissible
in G3im through the admissibility of weakening.

Lemma 5.3.3: The sequent C, F =>• A, C is derivable in G3im.

Proof: By right weakening from the corresponding result for G3i, Lemmas 2.3.3
and 4.2.1. QED.

Lemma 5.3.4: Height-preserving inversions. Rules L&, Lv, Rv, L3, and R3
are invertible and height-preserving in G3im. Rule LD is invertible and height-
preserving for the right premiss.

Proof: By induction on the height of derivation. If the principal formula of the
rule to be proved invertible is not principal in the last rule of the derivation and
this last rule is RD or RV, the inductive hypothesis cannot be applied because
of the restriction in the succedent of the premiss. The conclusion is instead ob-
tained by an instance of RD or RV with a matching context in the conclusion.
For instance, we obtain invertibility of Rv in the case that the sequent F =$•
A, A V B,CD D has been derived from C, F =>• D by RD by taking as the con-
text A, A, B instead of A, A v B. For the remaining cases, the proof goes through
for the propositional part as in Lemma 2.3.5 and for invertibility of L3 as in
Lemma 4.2.3. For R3, invertibility follows from height-preserving admissibility
of right weakening. QED.

We remark that RV also is invertible with height preserved, but this property is
not needed below. In the variant of G3im with A, A as succedent in rule LD,
invertibility obtains for its left premiss also.

Theorem 5.3.5: Height-preserving contraction for G3im.
  (i) / / \-n D, D, F => A, then \-n D, F =» A,
  (ii) / / hn F => A, D, D, then hn F =^ A, D.
110                     STRUCTURAL PROOF THEORY

Proof: By induction on n. For (i), proceed, mutatis mutandis, as in the proof of
Theorem4.2.4. For (ii), if \-n T =>> A, D, D is an axiom, then also \-n T ==> A, D
is an axiom. If n > 0, we distinguish the cases in which D is principal and not
principal in the last rule of the derivation. In the latter cases, we apply the inductive
hypothesis to the premisses of the last rule and then the rule, except for RD or
RV. These latter are taken care of by an application of the same rule but with a
suitably modified context. If D is principal and the last rule is R&, Rv, or R3,
the conclusion is obtained by application of height-preserving invertibility to the
premisses of the rule, the inductive hypothesis, and then the rule. If the last rule
is RD or RW, because of the restriction in the succedent, the formula D does not
occur in the premiss and the conclusion is obtained by application of the rule with
the context A in the conclusion. QED.

Theorem 5.3.6: The rule of cut is admissible in G3im.

Proof: The proof is similar to the proof of admissibility of cut for the calculus
G3c, except for those cases involving rules with a restriction in the succedent of
a premiss. Continuing the numbering in the proof of Theorem 3.2.3, we have the
following cases to consider:

3. The cut formula is not principal in the left premiss: There are three new cases
of last rule in the left premiss to consider:

3.3. The last rule in the left premiss is LD. The derivation

                  r"=> A       B,T" => A , C
                                                 LD
                      AD B,r" => A,C                   c,r=»A/
                                                                  Cut
                               AD    s,r", n=> A, A'
is transformed into the derivation

                             -LW    —                              Cut
                 r", r =» A              B,rf, r=> A, A'
                          A D B,V",r'      => A, A'

with a cut of lower cut-height.
3.6. The last rule in the left premiss is RD, with A = A", A D B. The derivation


                                     B
                                            RD
                            A", AD B,C      c, r =» Af
                             r, n =• A", AD B,Af      Cut
                     VARIANTS OF SEQUENT CALCULI                              111

is transformed into the derivation

                                                         RD
                               r => A", A D B, Af
                             r, r'=> A", A D 5, A/Lvy
in which no cut is used.
3.7. The last rule in the left premiss is /?V. The derivation

                           V^Bjy/x)
                      r =» Ar/, VxB, c ™ c, r r =^ A ;
                                                     —        CM?




is transformed into the derivation



                               r, r ; ^ A
in which, as in case 3.6, no cut is used.
4. The cut formula is principal in the left premiss only and the right premiss
is derived by a rule with a restriction in the succedent of the premiss, that is,
LD, RD, or J?V. In these cases, we cannot permute the cut up on the right, but
consider instead the five subcases arising from the derivation of the left premiss:
4.L The last rule is L&, and the derivation

                r => A, A r => A , #
                    r ^> A, A&^        A&^, r
                              r,r=^ A, A;
is transformed into the derivation
                                                A&£, T ; =
                                                               A//WV
                                                                    Cut
                                      , r, T / ^A,A /
                                                      Cut
                            r, r,r=^ A, A, A1
                           —    '     —             LC,RC
                               r, r = ^ A, Ar
4.//. The last rule is Rv, and the derivation
                     r =» A, A,fl
                     r^A,Av^D               A vB,r
                                    r, T / ^A,A /
112                     STRUCTURAL PROOF THEORY

is transformed into

                             A v B, T =» A'
                                                    Inv                f
                                                          A v B,r              => Ar
                                                    f                      /
                  r, r=> A, A7,                             B      r           A /
                                 F, F', r ' = » A, A', A'
                                 —                          LC,RC
                                         r, n=> A, Af
4. Hi. The last rule is RD and the right premiss is derived by LD. The derivation

     A,F=>g       AD B,ED F,T" ^> E F,AD B, F" => A7
   V ^ A,AD BRD             A D B, E D F, F" => A'
                                                 C r
              F, £ D F , F"=^ A, A'                "

is transformed into the derivation with two cuts of lower cut-heights:



                                              Cwf
                      ,r" =^ £                                  r , F , r / r ^ Ar
                                               ;/                                    LD
                                 r, F D F, r =» A'
                             F, E D F, F" =^ A, A'

If the right premiss is derived by RD or RV we proceed similarly: First we
apply RD to the first premiss to derive F ^ A D 5 , then cut with the premiss of
the right premiss, and apply again RD or RW.
4.iv. The last rule is Ri. Instead of concluding F =^ A,VxB, apply RW with A
empty to obtain F =>• Vjcg, then permute the cut up on the left premiss.
4.v. The last rule is R3, and the derivation

                  F =•     A,3xB,B(t/x)
                        F =^ A, 3x5           *3    3JC5,F/=^A/
                                                                               Cut



is transformed into

        F =* A,
                F, F7 =» A, gq/jc), A;          Cm
                                                     B(t/x), rf
                              F, F ; , F ; ^ A, A', Af
                                     —                          LC,RC
                                          r,r ^ A, Af
                      VARIANTS OF SEQUENT CALCULI                                  113

5. The cut formula is principal in both premisses.
5.5. The cut formula is A D B, and the derivation is



                                                                    Cut


This is transformed into
    F =» A, A D ff A D B,r             => A
               r , r = > A, A                A, r => B
                           r, r, r = » A , #
                                       r,r,r',r'=> A, A'
                                                    !
                                           —                         LC,RC
                                               r,r=^ A, A'
with one cut of lesser cut-height and two on shorter formulas.
5.4. The cut formula is WxB. The derivation
                   r => Biy/x)            VxB, B(t/x), T =^ A;
                                   V                    /       /    LV
                                  ^                         A
                               r , r =^ A, A'
is transformed into
         r ^ B(y/x)           r ^ A,
                                                                             Cut
                                                                      CMf
                           r , r , r =» A,A^
                             r , r = ^ A , A ' LC
QED.

   Next we show that the single succedent and multisuccedent intuitionistic cal-
culi are equivalent. In the proof, V A denotes the disjunction of formulas in A,
with \ / A = _L if A is empty. We also write iterated disjunctions as multiple
disjunctions without parentheses:

Theorem 5.3.7: Equivalence of G3i and G3im. The sequent T=$\J /± is deriv-
able in G3i if and only ifV^A          is derivable in G3im.
Proof: Assume that F =>• \ / A is derivable in G3i. Since all rules in the derivation
are also rules in G3im or admissible in G3im, F =>• V ^ ^s derivable in G3im.
By invertibility of Rv, also F =>• A is derivable.
   The other direction is proved by induction on height of derivation of F =^ A.
If F => A is an axiom, F and A have a common atom P. Then F =>• P is an
axiom of G3i and T ^>\/A follows by repeated application of R v. If F =^ A is
a conclusion of L_L, then _L is in F and F =^ V A also is a conclusion of LJ_.
114                     STRUCTURAL PROOF THEORY

   Assume now that F =>• A has been derived in G3im and that A is nonempty
and A = C\,..., Cn. If the last rule is a left rule, we apply the inductive hypothesis
to the premisses and then we apply the rule again. If the last rule is a right rule,
we have five cases according to the form of principal formula; say it is Cn.

1. Cn = A&B.
and the inductive hypothesis gives that F =>• Ci v . . . v Cn_i V A and F =>•
C\ v . . . v Cn-\ v B are derivable in G3i. Now apply R8c, and a cut with the
easily derivable sequent

  (Ci v . . . v Cw_i v A)&(C1 v . . . v Cn-X v B) =^ Cx v . . . v Crt_i v ASLB

gives F => Ci v . . . v Cn-\ v A&B.
2. Cn = A v B. The premiss is F =>• C i , . . . ,C w _i, A, Z? and the inductive hy-
pothesis gives that F =>• Ci v . . . v Cn_i v A v 5 is derivable in G3i.
3. Cn = A D 5 . The premiss is A, F =^ Z? and by the inductive hypothesis
and RD, the sequent F =>> A D B is derivable in G3i. Now apply Rv to derive
r =* Ci v . . . v Cn_i v (A D B).
4. Cn =WxA. First apply the inductive hypothesis and /?V to the premiss and
then Rv.
5. Cn = 3xA. The premiss is F =>• Ci, . . . , C n _i, A(t/x), 3xA, so by the in-
ductive hypothesis, we obtain that F =^ Cx V . . . v Cn_i V A(^/x) V 3xA is
derivable in G3i. By derivability of Cx v . . . v Cn_i V A(f/*) V 3xA =>•
C\ v . . . v Cn_i v 3JCA and admissibility of cut, we have that F =>>
Ci v . . . v Cn_i v 3xA is derivable in G3i.
   If A is empty, the sequent F => can only be a conclusion of L_L. But then
F =>• V ^ ' which is the same as F => _L, also is a conclusion of L_L. QED.

The result shows that the comma on the right in sequents of the calculus G3im
behaves like intuitionistic disjunction.


5.4. A CLASSICAL SINGLE SUCCEDENT CALCULUS

We show that the addition of a rule of excluded middle for atomic formulas to
G3ip gives a complete calculus for classical propositional logic:

   Rule of excluded middle:

                               Gem-at
                       VARIANTS OF SEQUENT CALCULI                                115

The structural rules, weakening, contraction, and cut, are admissible, and, further,
the rule of excluded middle for arbitrary formulas is admissible. Thus we have
the rule

                                                        Gem


An analogous rule for arbitrary formulas, for natural deduction in sequent calculus
style, was considered already in Gentzen (1936, §5. 26). But the subformula
property fails for the rule, and Gentzen used a rule corresponding to the law of
double negation instead. When the rule of excluded middle is restricted to atoms,
the subformula property becomes the following: All formulas in the derivation
of F =>• C are either subformulas of the endsequent or of negations of atoms
(i.e., atoms, negations of atoms, or _L). This principle already is sufficient for
establishing many properties, but we also show that a simple transformation
converts derivations into ones in which the rule of excluded middle is applied
only to atoms that appear in the succedent of the conclusion so that we have a
subformula property of the usual kind.
    In the single succedent sequent calculus, all connectives are present and obey
the rules of intuitionistic logic, excluded middle is applied to atoms only, but still
derivations remain cut-free. A single succedent calculus is immediately trans-
latable into natural deduction: The rule of excluded middle for atoms gives a
generalization of the usual principle of indirect proof for atoms in natural deduc-
tion, and we obtain, in Chapter 8, as a corollary to admissibility of structural rules
and excluded middle for arbitrary formulas a fully normal form for derivations in
full classical propositional logic.
    The main reason for formulating a single succedent calculus is to extend the
operational meaning of sequents to classical propositional logic. The calculus
can equally well be seen as a system of intuitionistic proof theory of decidable
relations. Examples of this point of view will be treated in the next chapter.
    We cannot prove decidability of Vx A or 3x A from decidability of A(t/x) for
arbitrary t\ the addition of quantifiers will not result in classical predicate logic,
but in a logic with a classical propositional part and intuitionistic quantifiers, such
as encountered in, say, Heyting arithmetic.

(a) Admissibility of structural rules: In proving that admissibility of structural
rules in G3ip extends to G3ip+Gem-at, we need the following inversions:

Lemma 5.4.1: The following inversions are admissible in G3ip+Gem-at. Each
conclusion has a derivation of at most the same height as the premiss:
            , r => c    AvB,T ^ c           A v # , r => c     A D B,V = > C
116                     STRUCTURAL PROOF THEORY

Proof: By induction on the height of the derivation of the premiss. If in the first
inversion A&B, F =>• C was derived by Gem-at, we have the derivation

                  p, A&LB, F =» c ~ p, A & # , r =• c
                                                      Gm
                             A & S , r => c              "

and this is transformed into the derivation

                 P,
                 P,A,B,T      ^cInd  ~P,A,B,T                 =>cInd
                                                                Gem at
                                A,z?,r^c                            -
where 7nJ denotes the inductive step. All the other cases of the first rule go through
as in the proof for G3ip, Lemma 2.3.5. The proofs for disjunction and implication
are similar to those for conjunction. QED.

   Structural rules are proved admissible by induction on formula length and
derivation height, extending the proof for G3ip, Theorem 2.3.4.

Theorem 5.4.2: Height-preserving weakening. If \-n r=>C,then \-n A, F=^>
C.

Proof: By adding the formula A to the antecedent of each sequent in the derivation
of r =>• C, we obtain a derivation of A, Y =$> C. QED.

Theorem 5.4.3:      Height-preserving contraction.            If \-n A, A, T =>• C, then
hn A, r =^ c.
Proof: The proof is by induction on height of derivation of A, A, F =^ C. We
consider only the case in which A, A, F =^> C has been derived by Gem-at and
the last step is

                   P, A, A , F = ^ C         ~ P , A, A , F = ^ C


We transform this into


                                       Ind                          lnd
                                                   p A r c


For the rest, the proof goes through as that for G3ip in Theorem 2.4.1. QED.
                    VARIANTS OF SEQUENT CALCULI                                     117

We note that contraction for atoms is not only admissible in G3ip-\-Gem-at, but
is actually derivable by Gem-at:
                               r^ P   P     P __L D          I   P   F —k C




Theorem 5.4.4:
                              r =>> A A , A              -CM?

                                   r, A^C
w admissible in G3ip+Gem-at.

Proof: The proof is by induction on weight of the cut formula with subinduction
on cut-height. If thefirstpremiss in a cut was derived by Gem-at we have

                 P, r = ^ A   ~ P , T=^A
                                               G
                                                   "


and cut is permuted upward to cuts on the same formula but with lower cut-height,

                                      Cut                                     Cut
                                                        p r A c


and similarly if the second premiss was derived by Gem-at. For the remaining
cases, the proof goes through as that for G3ip in Theorem 2.4.3. QED.
(b) Applications: We first show the completeness of the classical single suc-
cedent calculus, then give a proof of Glivenko's theorem through a proof-
transformation, and finally derive a strict subformula property showing that in
the derivation of a sequent T =^> C, the rule of excluded middle can be restricted
to atoms of C.
   To prove the admissibility of excluded middle for arbitrary formulas and
thereby the completeness of the calculus G3i\)+Gem-at, we need the follow-
ing inversion lemma for implication:
Lemma 5.4.5: The inversion
                                A D B,F => C
                                                       Inv


is admissible in G3ip+Gem-at.
118                      STRUCTURAL PROOF THEORY

Proof: A cut of A D B, F =>> C with the easily derivable sequent ~ A ^ AD B
gives the result. QED.

Theorem 5.4.6: The rule of excluded middle for arbitrary formulas
                                                       r y
                           /\ , 1         —f    K^     ^ i\.,    1       ——p' O
                                                                                        Gem
                                                 p           ^

is admissible in G3ip+Gem-at.

Proof: We prove admissibility of excluded middle by induction on formula
length. Structural rules were shown admissible and can be used in the proof.
To narrow down, quite literally, the derivations, we shall indicate routine propo-
sitional derivations in G3ip by vertical dots.
For A := _L, we derive the conclusion from the right premiss already:


                                V^. r^y                 ^N>          I     ^.   (
                           ——r            -i-                 _L, 1      —7^        ^
                                                                                        Cut


For A := P, excluded middle is rule Gem-at.
For A := A8LB, we have the derivation



A,B,V   => CInV            ~A,5,r ^ C                                     C f
                                                                           "            ~ 5 ^       (    )           (    )   ,    ^
                                     M                                                                                                   Cut
                  ^T^c                                                                                   ^ r ^ c Ind

For A := A v B, we have the derivation

                      A v£,r=>C
                        A, T => C                      ~ A , ~B^> - ( A v B) ~ ( A v B),F                                         ^C
                         ^-^              ~Wk                                           ;     ^—=:                                 Cut
                                                                                                              Ind




For A := A D 5 , we have the derivation

                            :                                                                            AD         B,F
                                                D B)         - ( A D ,g), T =» C
                                                                                              Cwr
AD B,V ^ c                                A,~5,r ^ c                                                    -A,-5, r
                  /


QED.

From A =$> Av ~ A and ^ A =>- Av ~ A, we now conclude by Gem that each
                    VARIANTS OF SEQUENT CALCULI                               119

instance of the scheme =>• Av ~ A is derivable. With cut admissible, we have
proved:

Corollary 5.4.7: The calculus G3ip+Gem-at is complete for classical proposi-
tional logic.

   We show that the classical calculus G3i^-\-Gem-at is conservative over the
intuitionistic calculus G3ip for sequents with a negation as succedent.

Lemma 5.4.8: If F =>> C is derivable in G3ip+Gem-at, applications of rule
Gem-at can be permuted last, each concluding a sequent with succedent C.

Proof: Commutation of the rule Gem-at with all the rules of G3ip is readily ver-
ified. Premisses in Gem-at have the same succedent formula as the conclusion.
QED.

   The following result is a sequent calculus formulation of Glivenko's theorem
for propositional logic, proved here by an explicit transformation of a classical
derivation of a negative formula into an intuitionistic one.

Theorem 5.4.9: If F =>> ~ C is derivable in G3ip+Gem-at, it is derivable in
G3ip.

Proof: Using Lemma 5.4.8, permute down the applications of Gem-at, and let
the first one of them be

                                                       Gem-at


The premisses are derivable in G3ip, and we have, by using invertibility of RD and
admissibility of contraction and cut in G3ip, the derivation
                     P, A = ^ ~ C
                                    Inv




Repeating the proof transformation, we obtain a derivation of F => ~ C in
G3ip. QED.

   The admissibility of cut permits a structural analysis of proofs for the sequent
calculus G3ip-\-Gem-at. This is based on the following:

Theorem 5.4.10: All formulas in the derivation ofF^C      in G3ip+Gem-at are
either subformulas of the endsequent or of negations of atoms.
120                     STRUCTURAL PROOF THEORY

Proof: Inspection of the rules in a cut-free derivation shows that only the rule
Gem-at can make formulas disappear in a derivation, and these are atoms or
negations of atoms. QED.
For the usual logical calculi, consistency is a trivial corollary to cut elimination,
but here the argument is not altogether simple:
Corollary 5.4.11: G3ip+Gem-at is consistent.
Proof: Assume that =>• _L is derivable in G3ip+Gem-at. The only rule that can
have an empty antecedent in the conclusion is Gem-at, and therefore the last step
in the derivation is
                                                     Gem-at



The left premiss can have been derived only by Gem-at, but this would lead to an
infinite derivation. Therefore there is no derivation of =>> _L. QED.
Many other standard results for logical sequent calculi extend to the calculus
G3ip+Gem-at.
  An application of the rule of excluded middle to an atom not appearing in the
conclusion should have nothing to do with the derivation, for if such an atom
were effectively used, it would be a subformula of the conclusion.

Theorem 5.4.12: IfT^Cis        derivable in G3ip+Gem-at, it has a derivation
with the rule Gem-at restricted to atoms ofC.
Proof: Permute down applications of Gem-at with atoms P that are not subfor-
mulas of C Let the first such step be
                         P, A=^C            ~P,A=>C
                                              —         Gem-at

                                       A => C
We transform this derivation into
               C,P,
                        -C,P,

                                                             Or*
            C, A => C                       ~ C , A =>• C
                                                            Gem
                             A         7^
                             A   =>•   C

By Theorem 5.4.6, application of the rule of excluded middle to C converts to
atoms of C. The proof transformation is repeated until F => C is concluded, with
Gem-at restricted to atoms of C. QED.
                     VARIANTS OF SEQUENT CALCULI                                 121

The proof gives an effective transformation into a derivation with Gem-at applied
to atoms of C only. A root-first proof search for a sequent F =^ C can begin by a
splitting into P, F =>• C and ~ P, F =>> C for atoms P of C. For example, to de-
rive Peirce's law =^((AD B)DA)DA it is enough to derive (A D 5 ) D A =>• A
and then to apply / O . By the theorem, Peirce's law is derivable with Gem ap-
plied to A only. In writing the derivation, we leave out repetitions of the principal
formula in the left premiss of LD as these are not needed and the rule without
repetition is admissible:

                                                        LD
                                 B
                              A D B RD
      A, (AD B)D A ^ A ~ A , ( A   D B) D A

                         =» ((A D B)D     A)D    A

(c) Quantifier rules: The addition of quantifiers to the single succedent classi-
cal calculus gives a calculus with a classical propositional part and intuitionistic
quantifiers, G3i-\-Gem-at. Proofs of the basic results for systems with quantifiers
are mostly similar to previous proofs.

Lemma 5.4.13: The rule of weakening is admissible and height-preserving in
G3/+Gem-at.

Proof: Similar to that of Theorem 5.4.2. QED.

Lemma 5.4.14: The inversions of Lemmas 5.4.1 and 5.4.5 and the following two
inversions are admissible in G3i+Gem-at.

                                        Inv     ———;—          — Inv
                 A(t/x), VJCA, F =* C           A(y/x), F =* C
Proof: Inversion for LV follows by the admissibility of weakening. For L3, the
proof is by induction on the height of derivation of the premiss. QED.

Theorem 5.4.15: The rules of contraction and cut are admissible in G3i+
Gem-at.

Proof: By induction, analogously to Theorems 5.4.3 and 5.4.4. QED.

    The most natural interpretation of the calculus G3i+Gem-at is that it is a
cut-free intuitionistic system for theories that have decidable atomic formulas.
Illustrations of this point of view will be given in Section 6.6. Note that the proof
of admissibility of excluded middle for arbitrary formulas for the propositional
part cannot be extended to quantified formulas.
122                           STRUCTURAL PROOF THEORY

5.5. A TERMINATING INTUITIONISTIC CALCULUS

In Section 2.5(c), we gave proofs of underivability in an intuitionistic calculus
for propositional logic. In these proofs, it was shown that each possible deriva-
tion tree of a given sequent either begins with at least one sequent of the form
Pi, . . . , Pn => g , where Pt ^ Q for all /, or else produces a loop, a subderiva-
tion that repeats itself to infinity. The latter is produced by the repetition of the
principal formula AD B of rule LD.
   It was discovered in Hudelmaier (1992) and in Dyckhoff (1992) that the left
implication rule of G3ip can be refined into four different rules, according to
the form of the antecedent A of the principal formula, to the effect that proof
search terminates. The refinement gives a calculus, designated as G4ip (not to
be confused with the calculus G4 in Kleene's book of 1967, p. 306), with left
implication rules corresponding to the cases A = P, A = C&D, A = C V D,
A = C D D, respectively:

   Left implication rules of G4ip:

     p,  r                                   CD(D D B) ,r —i.7• E
                                                    D 1
   p,p D   r      =   >   •                   C&D  D . Jr =

   c D B, D D                     E          C,DD B, r : D B, r ^ E
                                        LV
      C V D D B, r =^ E                         (C D D) D r^ E
The rules for conjunction and disjunction and the right implication rule are iden-
tical to the rules of G3ip. The first three left implication rules of G4ip are based
on the intuitionistically provable equivalences

   PSLB   DC P&(P             D   B),
   (C D(DD       B)) DC (C&D D B),
   (C D B)8L(D        D B) DC (C V D D           B).


The fourth rule is not intuitive, but it can be justified as follows: From the
left premiss C, D D B,T =>• D we obtain by RD the sequent D D £, T =>
C D D. A cut with the derivable sequent (CDD)DB^DDB                       gives
(C D D) D B, T => C D D. Now the conclusion of LDD follows by LD only:




Rules LOD, L&D, and LVD are invertible with height of derivation preserved.
Similarly to rule LD of G3ip, rule LDD is invertible with respect to its second
premiss only.
                     VARIANTS OF SEQUENT CALCULI                                 123

   The structural proof theory of G4ip is an example of the subtle organization
of many details in order to obtain admissibility of structural rules in a direct and
purely syntactic way. We shall not give full details that would be too long to be
included here, but just some of the leading ideas. Proofs of all results can be found
in Dy ckhoff and Negri (2000). To start with, the naive definition of formula weight
as corresponding to formula length will be changed so that the active formulas in
rules have a weight that is strictly less than the weight of the principal formula.
Following Dyckhoff (1992), we set

   w(±) = 0,
   w(P) = 1 for atoms P,
   w(A DB) = w(A) + w(B)+l,
   w(A&B) = w(A) + w(B) + 2,
   w(A v B) = w(A) + w(B) + 3.
Other choices are also possible. The rules of G4ip are routinely shown admissible
in G3ip, since structural rules can be used, as in the justification of LDD above.
In the other direction, one has to prove first the admissibility of the left implica-
tion rule without repetition of the principal formula in the antecedent of the left
premiss. By induction on the height of derivation, we easily prove

Proposition 5.5.1: The rule of weakening,

                                              ;Wk


is admissible and height-preserving in G4ip.

Lemma 5.5.2: The sequent A, T =>> A is derivable in G4ip/or any formula A.

Proof: By induction on w{A). If A is an atom or _L, then A, T => A is an ax-
iom or conclusion of L_L. Else A is a compound formula. For conjunction and
disjunction, the claim follows from its validity for the components, obtained by
the inductive hypothesis. For implication, we have to analyze the structure of the
antecedent. If A = _L D B, the sequent ± D B,T ^ ± D B follows from the
axiom _L, ± D B,V ^ Bby RD. For antecedents of the form P, C&D, C V D,
and C D D, application of the inductive hypothesis to lighter formulas combined
with the rules for LD of G4ip and corresponding inversions gives the conclusion.
(For details, see Dyckhoff and Negri 2000.) QED.

   The proof of admissibility of contraction is not a routine matter: The essential
step is given by a lemma in which duplication of a formula in the conclusion is
shown admissible. The lemma shows that if the sequent (C D D) D B, V =>• E
is derivable, also C, D D B, D D B,V =>• E is derivable. The effect of this
124                      STRUCTURAL PROOF THEORY

lemma is to reduce contraction to lighter formulas in the problematic case of
an implication, the antecedent of which is also an implication.

Theorem 5.5.3: The rule of contraction

                                  A,A,V    => E


is admissible in G4ip.

Proof: See Dyckhoff and Negri (2000). QED.

The next step is to prove

Lemma 5.5.4: The rule

                               r =» A     B,F   => E
                                  AD B,F => E

is admissible in G4ip.

Proof: See Dyckhoff and Negri (2000). QED.

Theorem 5.5.5: The rule
                     A D B , T => A B , T :            -LD
                          AD B,F => E
is admissible in G4ip.
Proof: From the right premiss, by admissibility of weakening, we obtain
B, A D B,F ^ E, and from the first premiss, by Lemma 5.5.4, we obtain
ADB,ADB,F=>E.         The conclusion follows by admissibility of contraction.
QED.

The theorem shows that the calculi G3ip and G4ip are equivalent. By admissibility
of cut in G3ip, we can conclude closure with respect to cut for G4ip, but the
stronger result of direct cut elimination is also provable. The proof, in Dyckhoff
and Negri (2000), is quite long and involved.
   Proofs of admissibility of structural rules can also be given to a multisuccedent
version of G4ip and to corresponding systems with quantifier rules. They can also
be given to extensions of these calculi with nonlogical rules, as shown in Dyckhoff
and Negri (2001).


NOTES TO CHAPTER 5

The proofs of cut elimination for GOi and GOc come from von Plato (2001). The
rules of the calculus GN were first found in Negri (2000), in connection with studies
                     VARIANTS OF SEQUENT CALCULI                                   125

on linear logic. The results of Section 5.2 come from Negri and von Plato (2001).
The multisuccedent intuitionistic calculus is presented in Dragalin (1988, Russian
original 1979). Dragalin's proof is given in outline only, and few readers seem to have
worked their way through it. Our detailed proof of cut elimination for this calculus
follows mainly Dyckhoff (1997), who in turn refers to correspondence with Dragalin
on the details of the proof. The classical single succedent calculus is due to von
Plato (1998a). The terminating intuitionistic calculus was discovered by Hudelmaier
(1992) and Dyckhoff (1992), or actually rediscovered, for related ideas were already
presented by Vorob'ev in the early 1950s (see Vorob'ev 1970). The direct proof of
admissibility of structural rules for G4ip and its extensions was found by Dyckhoff
and Negri (2000, 2001).
        Structural Proof Analysis of Axiomatic Theories




In this chapter, we give a method of adding axioms to sequent calculus, in the
form of nonlogical rules of inference. When formulated in a suitable way, cut
elimination will not be lost by such addition. By the conversion of axioms into
rules, it becomes possible to prove properties of systems by induction on the
height of derivations.
   The method of extension by nonlogical rules works uniformly for systems
based on classical logic. For constructive systems, there will be some special forms
of axioms, notably (P D Q) D R, that cannot be treated through cut-free rules.
   In the conversion of axiom systems into systems with nonlogical rules, the
multisuccedent calculi G3im and G3c are most useful. All structural rules will be
admissible in extensions of these calculi, which has profound consequences for the
structure of derivations. The first application is a cut-free system of predicate logic
with equality. In earlier systems, cut was reduced to cuts on atomic formulas in
instances of the equality axioms, but by the method of this chapter, there will be no
cuts anywhere. Other applications of the structural proof analysis of mathematical
theories include elementary theories of equality and apartness, order and lattices,
and elementary geometry.

