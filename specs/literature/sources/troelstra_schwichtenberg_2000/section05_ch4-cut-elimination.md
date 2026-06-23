# Basic Proof Theory — Chapter 4: Cut Elimination with Applications (lines 4468-6868)

Chapter 4

Cut elimination with applications

The "applications of cut elimination" in the title of this chapter may perhaps
be described more appropriately as "applications of cutfree systems", since
the applications are obtained by analyzing the structure of cutfree proofs;
and in order to prove that the various cutfree systems are adequate for our
standard logics all we need to know is that these systems are closed under
Cut (that is to say, Cut is a an admissible rule). Nevertheless there are
good reasons to be interested in the process of cut elimination, as opposed
to semantical proofs of closure under Cut. True, the usual semantical proofs
establish not only closure under Cut, but also completeness for the semantics
considered. On the other hand, the proof of cut elimination for G3c is at
least as efficient as the semantical proof (although G3cp permits a very fast
semantical proof of closure under Cut), and in the case of logics with a more
complicated semantics (such as intuitionistic logic, and the modal logic S4
in chapter 9) often more efficient. For linear logic in section 9.3, so far no
semantical proof of closure under Cut has been published. Other reasons for
being interested in the process of cut elimination will be found in certain
results in sections 5.1 and 6.9, which describe bounds on the increase in size
of deductions under cut elimination and normalization respectively.


4.1      Cut elimination
As mentioned before, "Cut" is the rule
                           r    A, A           A, ri   Al
                                 r, I',
Closure under Cut just says that the Cut rule is admissible: if I- r    AA and
AP      A' in the system considered, then also I- rr        AA'. This in itself
does not give us an algorithm for constructing a deduction of rr        AA' from
given deductions of I'     AA and Ar           A'. In the systems studied here
the deductions are recursively enumerable. So, if we know that the system is
closed under Cut, there exists, trivially, an uninteresting algorithm for finding
                                          92
4.1. Cut elimination                                                        93

a deduction of FF'      AA' given the fact that r      AA and AF'       A' are
deducible: just search through all deductions until one arrives at a deduction
for rr, AA'. For such a trivial algorithm we cannot find a bound on the
depth of the cutfree proof in terms of the depth of the original proof.
  We shall say that cut elim,ination holds, for system S + Cut, if there is
a "non-trivial" algorithm for transforming a deduction in S + Cut into a
deduction with the same conclusion in S. In our proofs such a non-trivial
algorithm is based on certain local transformation steps, such as permuting
rules upward over other rules, or replacing a cut on a compound formula A
by some cuts on (A and) its immediate subformulas, and on certain simple
global transformations on subdeductions, as for example the transformations
implicit in the inversion lemma and closure under Contraction for G3[mic].


4.1.1. DEFINITION. The level of a cut is defined as the sum of the depths of
the deductions of the premises; the rank of a cut on A is IAI +1. The cut rank
of a deduction D, cr(D), is the maximum of the ranks of the cutformulas
occurring in D.


4.1.2. NOTATION. For the deduction D* with conclusion F,                 A, A'
obtained by applying dp-admissible Weakening to D with conclusion F A
we write D[F/ A1]. We say in this case that D has been weakened with
      A'; similarly for individual sequents.
  In intuitionistic and minimal systems with at most one formula in the succe-
dent this is usually weakening with sequents r      (i.e., empty succedent); in
this case D[1" ] may be abbreviated as v[r].



4.1.3. LEMMA. For all systems closed under dp-weakening, prooftrees with
instances of Cut may be transformed in a prooftree with instances of con-
textsharing Cut, defined in 3.2; the transformation preserves depth. Hence
eliminability of Cut is a consequence of eliminability of Cut.
PROOF. If T is a system closed under dp-admissible Weakening, then so is
T + Cut: if we weaken premises and conclusion of an instance of Cut with
the same sequent, the result is again an instance of Cuto.
  Let D be a prooftree containing instances of Cut and Cut; take a top-
most instance a of Cut, conclusion of a subdeduction D', and with premises
F     A, A and r', A A', derived by Do, D1 respectively. Then Do[1.A'1,
7,1[1" -A] have conclusions rr    ALA' and IT/ A     AA' respectively; now
apply Cut to to these deductions to obtain the original conclusion of D';
replace D' by the transformed deduction. Thus we may successively replace
all instances of Cut by instances of Cut.
94                                   Chapter 4. Cut elimination with applications

4.1.4. NOTATION. In this section we adopt as a local convention, that the
deduction(s) of the premise(s) of the conclusion of a prooftree 7, are denoted
by Do (Do, DO; the deductions of the premise(s) of the conclusion of Di are
        etc. The depth of 1, is d, the depth of D21. in is dii...in

4.1.5. THEOREM. Cut elimination holds for G3[mic] + Cut.
PROOF. We shall in fact establish cut elimination for G3[mic] + Cut. Our
strategy will be to successively remove cuts which are topmost among all cuts
with rank equal to the rank of the whole deduction, i.e. topmost maximal-rank
cuts. It suffices to show how to replace a subdeduction D of the form

                            Do              D1
                        F        D D,F
                                                   Cutcs

where cr(Di) < IDI       cr(D) 1 for i E {0, 1}, by a V* with the same
conclusion, such that cr(D*) < IDI. The proof proceeds by a main induction
on the cutrank, with a subinduction on the level of the cut at the bottom of
D.
  We treat the classical and the intuitionistic cases; the treatment for minimal
logic is contained in the discussion of the intuitionistic case. For future use
we shall also verify in the course of the proof the following property:

(*)     d* < do + di for G3c, d* < 2(do + di) for G3[mi].

However, we recommend that initially the proof is read without paying at-
tention to the verification of (*).
  We use closure under Contraction and Weakening all the time. Recall that
we consider only proofs with axioms where the principal formula is atomic.
There are three possibilities we have to consider:

      at least one of Do, D1 is an axiom;

      Do and D1 are not axioms, and in at least one of the premises the
      cutformula is not principal;

      the cutformula is principal on both sides.

Case 1. At least one of Do, 7,1 is an axiom.
Subcase la. Do is an instance of Ax, and D is not principal in Do. Then D
is of the form

                              A,P,D
4.1. Cut elimination                                                             95

The conclusion is an axiom, so we can take the conclusion for our V*. Simi-
larly if Do is an application of Li. The intuitionistic case is similar and the
verification of (*) trivial.
Subcase lb. The premise on the left is an application of Ax and the succedent
principal formula is also a cutformula:



                                     P,F         A

V* is obtained by applying closure under Contraction to D1. The intuition-
istic case proceeds in the same way, and the verification of (*) is trivial.
Subcase lc. The premise on the right is an application of Ax or L_L, and
the antecedent principal formula is not a cutformula. This case is similar to
subcase la.
Subcase ld. The premise on the right is an application of the axiom Ax and
the cutformula is also a principal formula of the axiom. This case is similar
to subcase lb.
Subcase le. The premise on the right is an application of the axiom LI and
the cutformula is also a principal formula of the axiom.

                                Do

                                      r
If Do ends with a rule in which I is principal, r               A, I is of the form
r, I     A, I and hence is an instance of L_L; then r",      A, which is the
same as I'     A, is also an axiom. If Do ends with a rule in which I is not
principal, say a two-premise rule, D is of the form

                   D00
                       A', I   r"     A" I
                           r                     R     r   A
                                                               uutcs
                                             A
This is transformed by permuting and duplicating the cut upwards over R on
the left:
                 V00                             Vol
                                           ry,       p"I Ir"       A" Cutcs
       Cut cs                                         ril
                       P                                  All
                                     r
In this deduction V' we can apply the IH to V'0, V'1. If Do ends with a one-
premise rule, the transformation is similar, but no duplication is needed. The
intuitionistic case is also similar, but slightly simpler.
96                                             Chapter 4. Cut elimination with applications

  Verification of (*) in the classical case: if we replace, using the IH, in D'
the immediate subdeductions D'o, D'i. by (D)*, (D'i)* respectively, the depth
of the resulting deduction D* is
          d* < max(doo + 1, 41 + 1)

which is precisely what we have to prove for (*). Similarly for the intuitionistic
case.
 Case 2. Do and D1 are not axioms, and the cutformula is not principal in
either the antecedent or the succedent. Let us assume that D is not principal
in the succedent, and that Do ends with a two-premise rule R:

                       r
                            V00                 Doi
                              A 'D        r"      A"D             D1
                                  r       AD               R    DF =ZA
                                                  r =- A
This is transformed by permuting the cut upwards over R on the left:
          V00 [F]            7)1[1".61                V01 {F1            7,1[1'"   Au]
¿1
     ut        AA'D        Drri           AA'     rr"          AA"D Drr"           AA" Cut
                 IT'       AA'                                  IT"    AA" R
                                          rr          AA
Call the resulting deduction D'; replacing D'o, D'1 by respectively (D/0)*, (D'1)*
given by the IH produces a deduction A" which after use of closure under
Contraction produces D*. Note that R may in particular be a cut with rank
< D. The intuitionistic case is treated similarly, except where Do ends with
L>; then the cut is permuted upwards over one of the premises only.
  Verification of (*) in the classical case. Note that d" = d*. We have to
show d* < max(doo, doi) + 1 + di.. By the IH,

          (dor < doo + di,         (dir < doi + di,
and so d* < max(doo + di., cloi. + di.) + 1 = max(doo, doi) + 1 + cll.. The intu-
itionistic case is similar.
   If the cutformula is not principal in the antecedent, the treatment is similar
(symmetric in the classical case).
Case S. The cutformula is principal on both sides. We distinguish cases
according to the principal logical operator of D.
Subcase 3a. D Do A D1.
                       Doo                 Vol      pm
                 r         A, Do      rA, Di   Do, Di, r                 A
                       r      A, Do A Di      Do A Di, r                 A
                                         I'  A
becomes
4.1. Cut elimination                                                                                         97

                                             Doo[D].          ]

                            Vol          Dir =- A, Do                   Do, Di, I'         A
                                                                          A
                                                    A
and similarly in the intuitionistic case.
  Verification of (*). We have to show

         d* < max(doo, 41) + 1 + do + 1 = MaX(doo + 1, doi + 1) + dip + 1.

In fact inspection of the constructed D* shows
         d* = max(doi, max(doo, dio) + 1) + 1
             = max(doi, doo + 1, dio + 1) + 1
             < max(doo + 1, doi + 1) + dio + 1.
Subcase 3b. D Do V Di.. The treatment in the classical case is symmetric
to the preceding case; the intuitionistic case is somewhat simpler.
Subcase Sc. D Do + Di.. The deduction in G3c has the form
                                  V00                        Vio                   A.1
                           r,D0D1,L                  r =- Do, A              r,            A
                      r                 Di, A                r,     +                A
                                                        A
This is transformed into a deduction D':
                                                    Doo                      7,11[D0       ]


                           Dio               , D0           D1,z   I', Do, Di                  A
                      r,     Do,                             r, Do     A
                                                    A
The new cut on Do > D1 is of a lower level than the original one, so by the
subinduction hypothesis we can remove this cut. In the intuitionistic case we
have
                                                            D10                        7,11
                      r,D0D1                 r, Do -4 D1                Do        I', Di       A
                  r        Do -4 Di                         r,D0 > Di              A
                                             r          A
which is replaced by
       V00
 rDo         D1                   D10
r                      r,D04Di               Do                     Doo
                  r                                utcs           rDo              Cute,           Dll
                                         r        D1                                                     A Cutc.
98                                       Chapter 4. Cut elirnination with applications

The new cut on Do --+ D1 has a lower level, and can therefore be removed
by the subinduction hypothesis; let D'a, be replaced by (D0)*, the resulting
deduction is D* (and (D*)oo = CrYoo)*)
  Verification of (*). The classical case is similar to subcase 3a, and left to
the reader. We verify the intuitionistic case. We have to show
(1)        d* < 2(doo + 1 + max(dio, did) + 1)
                = max(2d00 + 2d10 + 4, 2d00 + 2d11 + 4).
The deduction (D*)oo satisfies 40 < 2(d00 + 1 +di.0) (using the IH), hence V*
satisfies
           d* < max(max(2d00 + 2dio + 2, doo) + 1, dii) + 1
                = max(2d00 + 2d10 + 4, doo + 2, d11 + 1),
and this is obviously smaller than the right hand side of (1).
Subcase 3d. D VxDo. We transform (y FV(Do, r, A), y                        FV(t))
                           V00                     Vio
                      r      Do[x 1 y]    V xDo , Do[x t], r     A
                      F =. A, VxDo            YxDo, F       A
                                     r      A
into
                              Doo [Do [xlt]
                          Do[xlt],  =.        Do[x ly]               Die
           Doo[ylt]        Do[xlt],F            VxDo     VxDo, Do [x It], r         A
       r        Do[xlt]                         Do[xlt], F   A
                              r      A
The subdeduction D' ending in the cut on VxDo is of lower level, so may be
replaced by the 1H by a deduction (D')*. This produces the required D*.
  Verification of (*) in the classical case. We have to show d* < doo + d10 + 2;
for D* we have
           d*   < max(doo, doo + 1 + dio) + 1
                = max(doo dio + 2, doo + 1)
                = doo + die + 2.
The treatment of the intuitionistic case is completely similar.
Subcase 3e. D      3xD0. The classical case is symmetric to the case of the
universal quantifier; the intuitionistic case is simpler. We leave the verification
to the reader.                                                                   N

4.1.5A. * Supply the missing cases in the preceding proof.
From the proof we obtain the following lemma, which will be used in the next
chapter to obtain an upper bound on the increase of depth of deductions as
a result of cut elimination:
4.1. Cut elimination                                                        99

4.1.6. COROLLARY. (Cut reduction lemma) Let V', D" be two deductions
in G3c + Cut, with cutrank < I DI, and let 7, result by a cut:
                                D'          ly/
                            r    D, A    F, D     A
                                    F    A
Then we can transform 1, into a deduction D* with lower cutrank and the
same conclusion such that ID*1 < 17,1 + 17,"1. A similar result holds for
G3i + Cut,, with 1D*1 < 2(1/Y1+ ID"I)-

4.1.7. REMARK. The cut elimination procedure as described above does not
produce unique results: there is indeterminacy at certain steps. In particular
when both cutformulas are non-principal, we can move a cut upwards on the
right or on the left. By way of illustration, consider the following deduction:
              P' P, Q
                ,         P, R, P'VQ'    P AQ, R, P'    P' , Q' , P
             P', P AQ     P, R, P'VQ'    P AQ, R, P'    P'VQ' , P
                             P', PAQ     P, P'VQ'
The cutformula R is not principal on either side. So we can permute the cut
upwards on the right or on the left. Permuting upwards on the left yields
                                          P, Q, PAQ, R, P'    P' Q' , P
                                                                  ,

        PAQ , P, Q , P'   P, R, P'VQ' P, Q, PAQ, R,P'         P'vQ',P
                          PAQ , P' , P, Q    P, P'VQ'
                          PAQ, P', PAQ P, P'VQ'
Now we have to apply closure under Contraction to get the required conclu-
sion; following the method of transformation of the deductions in the proof
of dp-closure under Contraction (3.5.5) the result is
                                         P,Q , R, P'   P' Q1 P
                                                          ,   ,

              P, Q, P'    P, R, P'VQ1    P, Q, R, P'   P'VQ' , P
                             P' , P,Q    P, P'VQ'
                             P', PAQ     P, P'VQ'
The remaining cut is now simply removed by noting that the conclusion of
the cut is an axiom (subcase la in the proof of 4.1.5):
                             P' , P, Q   P, P'V Q'
                             P',PAQ      P, P'VQ'
If we start, symmetrically, permuting the cut upwards on the right, we end
up with
                             P' PAQ
                                ,        P, P' ,Q'
100                                       Chapter 4. Cut elimination with applications

These two results represent obviously different proofs.
   Another source of indeterminacy in the cut elimination process appears in
case 3, where in the subcases which reduce a cut of degree n + 1 of level k
into two cuts of degree n (and possibly a cut of degree n + 1 and level less
than k); one has to choose an order in which the cuts of degree n are applied.

4.1.8. Variations
The most commonly used strategy in proofs of cut elimination is the removal
of topmost cuts; that is to say, we show how to replace a subdeduction 1, of
the form
                                                   /),
                             rA,D D,r,6,
                                   Do

                                          F    A
where D0,1,1 are cutfree, with a cutfree proof 1,* with the same conclusion.
The preceding proof can almost be copied for this strategy. We have to
distinguish the same main cases, and the same subcases in case 3.
   In permuting cuts upwards, as in subcase le and case 2, permuting over a
cut of lower rank does not occur. In the subcases of case 3, we have to appeal
not only to the subinduction hypothesis, but to the main IH as well. Take
for example the prooftree obtained in subcase 3d after transformation. We
first appeal to the subinduction hypothesis to remove the cut on VxDo, and
then to the 1H to remove all cuts of lower degree.
   In the proof above, we have removed instances of Cut. Under the strat-
egy of removing topmost cuts, we can also directly remove instances of Cut;
the details are rather similar to those presented in the proof above, but the
appeals to closure under Contraction appear at other places. For example, in
the subcase 3d we now have:
                        Doo [Y]                      D10
                    r   A, Do[x I y]      VxDo, Do[x I t], r'    A'
                    r    A, VxDo               VxDo, ri     A'
                                   F,r,
into
                                    Doo[y]
                             r      A, Do[xI y]            Dim
            Doo [0]           I'     A, VxDo      VxDo, Do[x 1 t], r      A'
        r    A, Do[x It]                 Do[x It], r, r' A, A'
                            rrri  AAA'
We remove the cuts by appeal to 1H and sub-IH, and finally have to apply
closure under Contraction. On the other hand, in the treatment of case 2 the
appeal to dp-closure under Contraction is not any longer necessary.
4.1. Cut elimination                                                          101

  The strategy of removal of topmost maximal-rank cuts does not work with
Cut, since we cannot guarantee dp-closure under Contraction for the system
with Cut.

4.1.9. Gentzen's method of cut elimination
There is another method, going back to Gentzen, which applies to G[12][mic],
not directly, but via a slight modification of these systems, and which works
as follows.
  If we try to prove cut elimination directly for G2 [mic], by (essentially) the
same method as used above for G3[mic], we encounter difficulties with the
Contraction rule. We should like to transform a deduction

                                         F', A, A      B
                                                         LC
                               A          F', A       B
                                                        Cut
                                   r,        B
into
                                    TY
                              FA r', A, A                     B
                       FA
                         DI
                                                                  Cut
                                         r,P,A
                                                          Cut
                                                 LC

but this does not give a reduction in the height of the subtrees above the
lowest new cut. The solution is to replace Cut by a derivable generalization
of the Cut rule:
                              A, An        Am, r'        A'
              Multicut                                            (n, m> 0)
                              r,           B, A'
where A", k E IN., stands for k copies of A. Multicut, also called "Mix", can
then be eliminated from this modified calculus in the same way as Cut was
eliminable from the G3-systems.
   Rank and level of a Multicut application (a multicut) are defined as rank
and level of a cut. We can apply either the strategy of removing topmost
cuts, or the strategy of removing topmost maximal-rank cuts.
   Under both strategies we use an induction on the rank of the multicut,
with a subinduction on the level of the multicut, in showing how to get rid
of a multicut of rank k 1 applied to two proofs with cutrank 0 (on the first
strategy) or less than k 1 (on the second strategy). In the example above,
the upper deduction is simply replaced by
                                           DI/
                         FA                         B
                                                        Multicut
102                                          Chapter 4. Cut elimination with applications

Instructive is the following case, the most complicated one: let D be obtained
by a multicut on the following two cutfree deductions:

               Doo                              Dlo                    D11
    rA      B(AB)m                        (A+Br        AA' r (A--+B)B          A'
    F      (AB)m1 A R.>                             l'(A+B)n±1        A'

In the case where m, n > 0 we construct Da,Db,Dc:
                                                      vio                    vil
                            Doo               r/(AB)n          AA'  ri (Aq3)nB
                 FA         B(A)B)rn                        r,(A*Br+1 A'
    D                                               BAA'

                            D00
                 FA      B(A+B)m                      D10
    Db = {
                     r   (AB)m+1A r(A*B)n                      AA'
                              Fri AAA'
                            D00
                 FA      B(A+B)m                      D11
                     F   (A+B)m+1A             (A--+B)'B        A'
    D                               rriB      AA'
In each of these deductions the multicut on A -4 .B has a lower level than
in D. Therefore we can construct by the 1H their transforms D'a, D,D, of
cutrank < IA -4 BI and combine these in
                            Dia
                     rr,A         BAA'              AAA'
                         rrriri          BAAA'A'             rr'.73   AA'
                                           (IT')3     (AAI)3
                                             rr'      AA'
The multicuts are now all of lower rank.

4.1.9A. * Show also for the other cases how to reduce the rank of an application
of Multicut when the cutformula is principal in both premises.

4.1.9B. 46 Argue that Gentzen's cut elimination procedure applies equally well
to the system G2i* mentioned in 3.3.4. (One can save a few cases in the argument
if the A in the axioms r, I A is restricted to be prime.) What happens to this
argument if, instead of the axioms 1-',1  A, we adopt the rule "If F      1, then
F        A"?
4.1. Cut elirnination                                                         103

4.1.10. Cut-elimination for m-G3i
The proofs of cut elimination for G3i can be adapted to m-G3i. We shall
not carry this out in detail, but instead provide a sketch.

LEMMA.

      In m-G3i the following rule is depth-preserving admissible:


                 r      A

      LV, LA, L3, RV, RA, R3 are invertible in m-G3i.
      m-G3i is 'closed under depth-preserving left- and right-contraction.      121




THEOREM. Cut is eliminable from deductions in m-G3i + Cut.
PROOF. We follow the standard strategy of removing topmost cuts; so we
have to show how to remove a cut applied to two cutfree deductions of the
premises. The main case distinctions are:

      one of the premises of the cut is an axiom;
      case 1 does not apply, and the left premise of the cut is obtained by a
      rule application for which the cutformula is not principal;
      cases 1 and 2 do not apply, and the right premise of the cut is obtained
      by an application of rule R for which the cutformula is not principal;
      the cutformula is principal in both premises.

The asymmetry between cases 2 and 3 is caused by the rules R> and RV
which deviate from the general pattern. The only new element, when com-
pared with the proof for G3i, occurs under case 3, in particular where the
rule R is R--+ or RV. For example, if R is R>, the proof ends with
                                            A, I', C   D
                        I'   A, A     A, F'   C > D, A'
                               r     c -> D, A, A'
Since we are in case 3 and cases 1 and 2 do not apply, A is principal on the left.
If the left premise is obtained by R>, or RV, say R-4, with A E A1 > A2,
the proof ends
                                    r, A1      A2
                                I'   A, A
Then we transform the end of the proof simply into
104                                       Chapter 4. Cut elimination with applications
                          F, A1
                              rA,z
                                         A2
                                                  A, ri, C        D
                                     r, F', C          D
                                          C + D,             A'
However, if the left premise has been obtained by one of the invertible rules
RV, RA, R3, we use inversion. For example, let RV be the rule for the left
premise, so the deduction ends with
                         A,A,B                AV B,P,C                D

                                              LY,C
we replace this by
                       A V B,        C        D
                         A, I'', C       D        (Inv)Av B, F', C        D
                                                                              (Inv)
           A, A, B    A, I'   C D,          B, F', C D
           r,ri      A, A', B,C + D       B,ri C + D,
                            FTT AA'A', C + D
Here the dotted line indicates an application of Inversion to transform a
proof with conclusion as above the line into a proof of no greater depth with
conclusion as below the line.

4.1.10A.      Prove the lemma.

4.1.10B.      Adapt the proof of cut elimination for m-G3i to elimination of Cuto.

4.1.10C. A Check that Cut or Cut es is also eliminable from m-G3i' plus Cut or
Cuto.

4.1.11. Semantic motivation for G3cp
In the introduction we described for the case of implication logic a very natural
way of arriving at a cutfree sequent calculus for G3cp. We extend this here
to all of G3cp.
   In testing the truth of a sequent r A, we try to give a valuation such
that A r becomes true and VA becomes false, in other words, the valuation
should make all formulas in r true and all formulas in A false.
   In order to make r      A, A > B false, we try to make r, A true and A, B
false, i.e. we try to find a refuting valuation for the sequent I', A   A, B.
In order to make r, A -4 B        A false, we try to make either I' true and
A, A false, or r,B true and A false. In other words, we try to find a refuting
valuation either for I'   A, A or for r,B
4.2. Applications of cut elimination                                         105

  Thus at each step we reduce the problem of finding a refuting valuation to
corresponding problems for less complex sequents. In the end we arrive at
r A with F A consisting of atomic formulas only. These have refuting
valuations if they are not axioms.
  Our rules for reducing the problem of finding a refuting valuation for a
sequent correspond to the following rules read upside down:



          F,A,B      A                 rA,A rA,B
         F,AKBA
         A,rL            B,Ft          F
              AVB,FA
         FL,A       B,FL                A,F
              F,A*./3A
These rules are precisely the propositional part of G3c. If we start "bot-
tom upwards", the different branches of the refutation search tree represent
different possibilities for finding a refutation. This gives us the following:

THEOREM. (Completeness for G3cp) A sequent r              A is formally derivable
by the rules listed above iff there is no refuting valuation.
This idea may be extended to predicate logic G3c. Since Cut is obviously
valid semantically, one thus finds a proof of closure under Cut by semantical
means; but the proof does not provide a specific algorithm of cut elimination.
See also 4.9.7.


4.2      Applications of cutfree systems
From the existence of cutfree formalizations of predicate logic one easily ob-
tains a number of interesting properties.
  Below, positive and negative occurrences of formulas in r      A are defined
as positive and negative occurrences in the classical sense in A r--> A, where
A is used for iterated conjunction.

4.2.1. PROPOSITION. (Subformula property, preservation of signs in deduc-
tions) Let D be a cutfree deduction of a sequent r   A in G[mic][123].
Then for any sequent       A' in D we have

   (i) the formulas of r occur positively in r, or negatively in A;
106                                   Chapter 4. Cut elimination with applications

      the formulas of A' occur either positively in A, or negatively in F;
      moreover, for Gl[mic],
      if a formula A occurs only positively [negatively] in F =- A, then A is
      introduced in D by a right /left./ rule.
PROOF. Immediate by inspection of the rules.                                      El

An appropriate formulation of the third property for systems G[23ilmic]
requires more care, since formulas may now also enter as context in an axiom.

COROLLARY. (Separation property) Any provable sequent F =- A always has
a proof using only the logical rules and/or axioms for the logical operators
occurring in F =- A.

4.2.1A. 4 Show that the separation property holds for Ni, and that it holds
for Hi in the following form: let X be any subset of {A, v, 1, V, 3} containing
>; show that the X-fragment of Hi can be axiomatized by the axioms and rules
involving operators from X only. Hint. Combine the equivalence proofs of 2.4.2
and 3.3 with the subformula property for G3i.

4.2.1B. 4 Show that the separation property holds for Nc in the form: if r A
is provable in Nc, then it has a proof using only axioms/rules for logical operators
occurring in 1' -4 A, and possibly 1c. Extend the sepaxation theorem to He for
fragments containing at least -4, I. (For the case of >Hc see 4.9.2, 6.2.7C, 2.1.8F.)

4.2.2. THEOREM. (Relation between M and I) Let P be a fixed proposition
letter, not occurring in r, A. For arbitrary B not containing P let B* :=
B[±1.13], and put F* := {B* : B E r}. Then (with the notation of 1.1.6)
                              r Hm A iff r* Hi A*.

PROOF. If F Hm A, then r* Hm A* (since I behaves as an arbitrary propo-
sition letter P in minimal logic), hence r* Hi A*. Conversely, if r* Hi A*,
we can show r*      A* by a cutfree proof in one of the intuitionistic systems;
by the separation property for cutfree systems, the proof does not use the
I-axiom, so F* Hm A*, hence I' hm A.

4.2.3. THEOREM. (Disjunction property under hypotheses) In M and I, if
F does not contain a disjunction as s.p.p. (= strictly positive part, defined in
1.1.4), then, if FHAV B, it follows that F H A or I' H B.
PROOF. Suppose I' Hi A V B, then we have a proof D in G3i of r               A V B,
where r does not contain a disjunction as strictly positive part.
4.2. Applications of cut elimination                                            107

   A sequent F'     A V B in D such that r' clods not contain a s.p.p. which
is disjunctive, and where A V B is not principal, has exactly one premise of
the form          A V B where F" has no disjunctive or existential s.p.p.'s.
(Only LV can cause two premises with A V B in the succedent, but then I'
would contain a disjunction, hence a disjunctive s.p.p.) Therefore there is a
sequence

           Fc,   AVB,Fi
in D such that A V B is principal in the first sequent, ri           A V B is the
premise of ri+,      A V B (0 < i < n) and 17,,      A V B is the conclusion.
  Note that ro         A V B cannot be an axiom (except when 1 E ro, in
which case the matter is trivial), because of the restriction to atomic principal
formulas in axioms. Therefore ro       A V B is preceded by ro      A or ro    B,
say the first; replacing in all ri   A V B the occurrence of A V B by A and
dropping the repetition of ro       A results in a correct deduction.          121


There is a similar theorem for the existential quantifier:

4.2.4. THEOREM. (Explicit definability under hypotheses) In M or I

        if F does not contain an existential s.p.p., and r H 3xA, then there are
        terms t1, t2,. , tr, such that r H A(t1)      v A(t.),
        if r contains neither a disjunctive s.p.p., nor an existential s.p.p., and
        F H 3x A, then there is a term t such that r H A(t).                     N


REMARK. RasiowaHarrop formulas (in the literature also called Harrop
formulas) are formulas for which no s.p.p. is a disjunction or an existential
formula. For r consisting of RasiowaHarrop formulas 4.2.3 and 4.2.4 both
hold.

4.2.4A. * Prove theorem 4.2.4.

4.2.4B. 06 Reformulate the arguments of theorem 4.2.3, 4.2.4 as proofs by induc-
tion on the depth of deductions.


4.2.4C.* (Alternative method for proving the disjunction property) The method
of the "Aczel slash" provides an alternative route to a proof of: if F hi A VB, then
Phi A or r B, for suitable r. We describe the method for propositional logic
only. Let F be a set of sentences; FIA is defined by induction on the depth of A by
      FIP := F F- P for P atomic;
      riA A B := rIA and 11/3;
        rIA V B := rIA or rIB;
108                                   Chapter 4. Cut elimination with applications

 (iv) riA B := (If riA then FIB) and r h A B.
By induction on the depth of A one can prove that, if PIA, then F I- A. By
induction on the length of proofs in Hi one can show that, if one assumes ric for
all C E r and r E- A, then ro. Deduce from this that if ric for all C E F, and
F E- A v B, then F A or r E- B. Show finally that if no formula in F contains
a disjunction as a strictly positive subformula, then Fr for all C E F. Conclude
from this: if hi       B v C, then hi       B or            C.

4.2.5. THEOREM. (Herbrand's theorem) A prenex formula B, say

                      Bm Vx3x/Vy3y/       A(x, z', y, y',   .),

A quantifier-free, is provable in GS1, iff there is a disjunction of substitution
instances of A of the form

                           DV               yi, Si,. .),
                                i=0

such that D is provable propositionally and B can be obtained from the se-
quent A(xo, to, yo,  ...),... , A(xn,tn, yn, sn, ...) by structural and quantifier
rules.
PROOF. For a detailed proof and a more precise statement see 5.3.7. The
idea of the proof is as follows. Suppose B has a proof in GS1, then we can
rearrange the proof in such a way that all quantifier-inferences come below
all propositional inferences. For example, a succession of two rules as on the
left may be rearranged as on the right (x FV(FB)):
                        A,B,F                     A, B, F
                       VxA,B,r                  A, B V C,r
                      VxA,B v c,r             VxA,B V C, F

where, in case x E FV(C), we have to rename the variable x in A in the infer-
ences on the right. Ultimately we find a propositional sequent which is the last
sequent of the propositional part and the first sequent of the quantifier part;
this sequent must then consist of a multiset of formulas A(xi, t, yi, si, . . .).

4.2.5A. 4 Give complete details of the permutation argument in the proof of
Herbrand's theorem.

4.2.6. THEOREM. Ip is decidable.
PROOF. Let 1"      A be a propositional sequent. We can construct a search
tree, for "bottom-up" proof search in the system G3ip.
   More generally, in order to describe the search tree we note that
4.2. Applications of cut elimination                                       109

     Each node of the search tree represents the problem of proving (simul-
taneously) a finite set of sequents F1 A1,. ,         An.
      A predecessor of a problem is obtained by replacing a Fi        Ai by
F'   A' or by a pair F' =- A', I" =- A" such that
                     F' =- A'                           A'        A"
                                            or
                     ri      Ai                         ri   Ai

is a rule application of G3i.
   We regard two problems {r,   Ai,    , rn   An} and {A1       B1,   ,

In An} as equivalent, if to each ri Ai there is a A3 .133 such that
Set(Fi) = Set(L) and Ai B. If along a branch of the search tree we meet
with an axiom, the branch ends there; and if along a branch a repetition
of a problem occurs, that is to say we encounier a problem equivalent to a
problem occurring lower down the branch, the branch is cut off at the repeated
problem.
      Because of the subformula property, there are only finitely many prob-
lems. This puts a bound on the depth of the search tree.

REMARK. The proof that such a decision method works is still easier for
Kleene's original calculus G3, or for GKi, defined in 3.5.11.

4.2.7. EXAMPLE. The following example illustrates the method. In order to
shorten the verifications a bit, we note in advance that sequents of the forms

         r,    > A2, A2            A3, .         An-i   An   Ai -4 An

         r, Ai, Ai        A2, ..   , An, > An           An

are derivable. Below, P, Q, R E PV . We drop -4 to keep formulas short. Let
us now attempt in G3i a backward search for a proof of the sequent

         (QP)R,QR, RP                  P
We add "NA f" to indicate derivability and underivability, respectively. (N.B.
We may conclude underivability if a sequent is obviously classically falsifi-
able.)   "Indifferent" after a sequent indicates that the derivability for this
sequent does not matter since the branch in the search tree breaks off already
for other reasons.
(a) Apply L-4 with principal formula RP; this requires proofs of

         (QP)R,QR, RP                  R,

         (QP)R,QR, P               P        .
110                                     Chapter 4. Cut elimination with applications

Since the second sequent is an axiom, the problem reduces to (2). We continue
the search with (2) first.
(aa) Apply in (2) L-4 with principal formula RP; we find
         (QP)R,QR, RP           R and

         (QP)R,QR, P         R (indifferent),

so this operation is useless, since we are back at (2).
(ab) Apply L--+ with QR principal:

(3)      (QP)R,QR, RP           Q,

         (Q P)R, RP, R       R V.

We continue with (3).
(aba.) Apply L*, with RP principal, to (3):
         (QP)R,QR, RP           R (repetition),

        (QP)R,QR,P           Q (indifferent),

so this track breaks down.
(abb) Apply L>, with QR principal, to (3):
        (QP)R,QR, RP            Q (repetition),

        (QP)R, R, RP         Q t,

so this track also breaks down.
(abc) Apply L-4, with (QP)R principal to (3):
        (QP)R,QR, RP            QP V,

        R,QR, RP         Q t,

again breakdown. We return to (2).
(ac) Apply L-4, with (QP)R principal, to (2):
        (QP)R,QR, RP            QP V,

        QR,RP,R          R/,
so this track leads to a derivation. We have now investigated all possibilities
for (2).
4.2. Applications of cut elirnination                                          111

      Apply L+, with QR principal, to (1):

(4)      (QP)R,QR, RP              Q,

         (QP)R, R, RP          P

(4) is identical with (3), so this track fails.
    Apply L-4, with (QP)R principal, to (1):

         (QP)R,QR, RP              QP V,

         QR, RP, R       QP V,

so this leads to a derivation. All in all, we have found two roads leading to a
deduction, all others failed.

4.2.7A. 4* Show proof-theoretically that I    V x(P V Rx)     P V V xRx (P E PV,
R a unary relation symbol). You may use classical unsatisfiability as a shortcut to
see that a sequent cannot be derivable.

4.2.7B. 4* Apply the decision procedure for Ip to the following sequents:
(P    Q) V (Q  P),     ((P     Q)    P)     P,          V    P , R(P    Q)
Q)         Q, Q P Q (P,Q, R E PV).

4.2.7C. A Prove the following lemma for the calculi Gl[mic]: a provable se-
quent always has a proof in which the multiplicity of any formula in antecedent or
succedent is at most 2. Derive from this a decision method for Ip based on Gli.
   Let Gl[mic]° be the calculi obtained from Gl[mic] by replacing          by the
original version of Gentzen:


                               A        B ,r ,r/
Show that the statement above also holds for Gl[mic]° if we read 'at most 3' for
'at most 2' (Gentzen [1935]).

4.2.7D. 4* Let us call a proof in Gl[mic]° (see the preceding exercise) restricted
if in all applications of L>


                               A        B
A    B does not occur in V. Show that every [cutfree] proof of a sequent r       A
can be transformed into a [cutfree] restricted proof of r A (DoAen [1987]).
112                                   Chapter 4. Cut elimination with applications

4.2.7E. 4 Use the preceding result to show that every sequent        A provable
in G1[mic]°, with multiplicity of formulas in r and in A at most 2, has also a
deduction in which all sequents have multiplicity at most 2 for all formulas in
antecedent and succedent (Dokn [1987]).

4.2.7F. 4* Let C be a formula of I not containing       and let I' = {Ai >
B1,   ,      B}. Prove that if r H C, then r I- A, for some i < n (Prawitz
[1965]).


4.2.7G. 4 Show the decidability of prenex formulas in I for languages without
function symbols and equality.

4.2.7H. 4 Show that the following derived rule holds for intuitionistic logic: If
I F- (A    B)    C V D, then I I- (A      B)     C or I H (A -4 B)         D or
I I- (A B)     A.
  Generalize the preceding rule to: If E      Ai(A,       Bi) and I H E   CV D, then
IHECorIHE>DorIF-E>A,forsomei.

4.3 A more efficient calculus for Ip
The fact that in the calculus G3i in the rule L> the formula A         B in-
troduced in the conclusion has to be present also in the left premise makes
the bottom-up proof search inefficient; the same implication may have to be
treated many times. Splitting L--> into four special cases, such that for a
suitable measure the premises are strictly less complex than the conclusion,
produces a much more efficient decision algorithm.

4.3.1. DEFINITION. The Gentzen system G4ip has the axioms and rules of
G3ip, except that L> is replaced by four special cases (P E PV):

           LO-4
                      PB r
                  P    B,P,      E
                  C    (D     B),1'   E
           LA*

                  C    B,D                E
           LV-4
                      CVD--+B,FE
                  D     B,C,I      D       B,I        E
           L>-4                                                                  El
                        (C    D) -4 B ,      E
Note that all rules are invertible, except L>-->, RV.
4.3. A more efficient calculus for Ip                                         113

4.3.1A. * Observe that we do not have the subformula property in the strict
sense for this new calculus; can you formulate a reasonable substitute?
It is not hard to obtain an upper bound on the length of branches in a
bottom-up search for a deduction, once we define an appropriate measure.

4.3.2. DEFINMON. We assign to propositional formulas A a weight w(A)
as follows:

      w(P) = w(I) := 2 for P e PV,
      w(A A B) := w(A)(1+ w(B)),
      w(A V B) := 1 + w(A) + w(B),
      w(A -- B) := 1 + w(A)w(B).
For sequents F      A we put

                      w(F      A) := Efw(B): B E PA}
where each w(B) occurs as a term in the sum with the multiplicity of B in
rA.                                                                             z
Now observe that for each rule of the calculus G4ip, the weight each of the
premises is lower than the conclusion. So all branches in a bottom-up search
tree for a proof of the sequent 1" =- A have length at most w(r       A). We
now turn to the proof of equivalence between G4ip and G3ip.
   The idea of the proof is to show, by induction on the weight of a sequent,
that if G3ip 1-- r     A, then G4ip h r A. If G3ip h r A and we can
find one or two sequents (S, S' say) from which r      A would follow in G4ip
by an invertible rule, the sequents S, S' are also derivable in G3ip and have
lower weight, so the IH applies.
   If none of the invertible rules of G4ip is applicable, we must look at the
last rule applied in the G3ip-proof. Except for one "awkward" case, we can
then always show in a straightforward way that there are sequents of lower
weight provable in G3ip, which by a rule of G4ip yield r       A. However, by
lemma 4.3.4 we can show that we may restrict attention to proofs in G3ip
in which the awkward case does not arise.

4.3.3. DEFINMON. (Irreducible, awkward, easy) A multiset r is called
irreducible if r neither contains a pair P,P --> B (P E PV), nor J_, nor a
formula C A D, nor a formula C V D. A sequent r              A is irreducible iff r
is irreducible. A proof is awkward if the principal formula of the final step
occurs on the left and is critical, that is to say of the form P -4 B, otherwise
it is easy.                                                                      Z
114                                      Chapter 4. Cut elirnination with applications

4.3.4. LEMMA. A provable irreducible sequent has an easy proof in G3ip.
PROOF. We argue by contradiction. Assume that there are provable irre-
ducible sequents without easy proofs. Among all the awkward proofs of such
sequents, we select a proof 7, of such a sequent with a leftmost branch of
minimal length. Let r           C be the conclusion of that proof. r                c
P     B, r'     C with P       ry, since F is irreducible. Hence 1, has the form
                                   D'
                             P -+ B,F'     P                C
                                   P      B,ri       C
1,' cannot be an axiom since P r'. P B, r' P is also irreducible, and
not all possible deductions of this sequent can be awkward, for then 1," would
be an awkward proof with a leftmost branch shorter than the leftmost branch
of D, which is excluded by assumption. Hence P         B,        P must have
an easy proof T," and end with an application of a left rule; r P --+ B, r'
is irreducible, so the last rule applied must have been L-* with principal
formula D --+ E, D not atomic (since T," was easy), i.e. if we replace 1,' by
D" we get a deduction of the form
                                              1,1
      P   B,D        E, r"  D E,P--+ B,F"  P
                P --+ B, D --+ E,r" P                           B, D       E , r"   C
                                P B, D E , r"                   c
where r D --+ E, r". We permute the application of rules and obtain
                                          vi                               .2)//

                Do                  E,P > B,r"             P B,D> E,r"              C
      P   B,D        E, r"     D                    E, P    B, r"      C
                       P-+ B,D--+ E,r"
The new proof is easy.                                                                  E]


4.3.5. THEOREM. G3ip and G4ip are equivalent.
PROOF. Let     1-* be derivability in G3ip and G4ip respectively. The rules
of G4ip are derivable in G3ip, so G4ip C G3ip.
  For the converse, consider any G3ip-proof of a propositional sequent r
E; we show by induction on the weight of the sequent that we can find a
G4ip-proof of the same sequent.
Case 1. If J..E r we are done.
Case 2. Let r r', A A B E; then also 1- r', A, B                    E, and r', A, B has
lower weight than r, so i* r', A, B E.
Case 3. r A V B, r': similarly.
4.3. A more efficient calculus for Ip                                         115

 Case 4. r           P, P -+ B. Then also H F', P, B         E, so by the IH
    F', P, B   E; apply LO>.
 Case 5. If none of the preceding cases applies, F is irreducible. By the
preceding lemma, F        E has a G3ip-proof, which is either an axiom, or has
a last rule application with principal formula on the right, or has a principal
formula on the left of the form A B, A not atomic.
Subcase 5.1. If the final step is an axiom, we are done.
Subcase 5.2. If the last rule is RV, RA or R-4, we are done since the premises
are lower in weight than the conclusion.
Subcase 5.3. The last rule is L-* with A        B as principal formula, A not
atomic.
   5.3(i) If A C A D, then because of
                            H (C A D    B)     (C   (D --+ B))
also C        (D      B),       E in G3ip, which by IH is provable in G4ip, hence
with LA-->     F    E.
 5.3(ui) Similarly for A    CV D, then H* C        B, D     B, F'    E; apply
LV-4.
 5.3 (iii) Let A C      D; then the last rule application has the form
                      (C      D) --+ B,ri C D                B,F'        E
                                  (C D)    B,           E
In G3m we have generally H r, (A0 > A1) -4 A2     Ao     A1 iff H r, A, -4
A2       Ao                                      A1 (by inversion); hence
                   A1 (exercise) iff F, A, --+ A2, Ao
  (C > D) > B ,          C --+ D iff H D > B, C,       D, and this second
sequent is lower in weight, so H* D -+ B, C,   D; also H* B,       E; now
apply L-4>.
  5.300 Let A       1. Then 1- _1_   B,        E iff [--    E iff H*           E
(III); use admissibility of Weakening to obtain H* A > B, I"     E.

4.3.6. EXAMPLE. The following example illustrates what may be gained in
reducing the possibilities for "backtracking". If we search for a proof of the
purely implicational sequent (writing for brevity XY for X > Y)
                                   (QP)R,QR, RP         P,
we find in G4ip a single possibility:
                   PR, R, P,Q       P
                   PR, RP, Q , R       P °-+        P,QR            P
               PR,QR, RP, Q p LO-4 R,QR, RP                          P
                        (QP)R,QR, RP P
Compare this with the proof search in 4.2.7 for the same sequent.
116                                    Chapter 4. Cut elimination with applications

4.3.6A. ** Test the following formulas for derivability in Ip: A                 P)
      V        A>               P) V (-,P V         and [((P     R)            R) >
((Q   R)           (((P Q) R) R).

4.3.6B. 4 Prove that in G3m       P,(Ao       Ai) > A2      Ao > Ai if F- r,     ->
A2      AO    Al .



4.4          Interpolation and definable functions
The interpolation theorem is a central result in first-order logic; therefore
we have reserved a separate section for it. An important corollary of the
interpolation theorem, historically preceding it, is Beth's definability theorem
(4.4.2B).

4.4.1. NOTATION. In this section we adopt the following notation. Rel±(r),
Rel-(r) are the sets of relation symbols occurring positively, respectively
negatively in F. We put Rel(r) := Rel±(r) U Rel-(r). Con(r) is the set of
individual constants occurring in F.

4.4.2. Interpolation theorem for M, I, C
An interpolant for a derivable implication I- A > ./3 is a formula F such
that I- A > F, F          B, and such that F satisfies certain additional
conditions. For example, for propositional logic, one requires that F contains
propositional variables occurring in both A and B only. For sequents r      A,
the obvious notion of interpolant would be a formula F satisfying additional
conditions such that I- r     F, F         A. However, in order to construct
interpolants by induction on the depth of derivations of sequents, we need a
more general notion of interpolant, as in the following theorem.

THEOREM. Suppose G3[mic]           IT'       AA' (with lAil < 1 and A = 0 for
G3[mi]); then there is an interpolation formula (interpolant) F such that

     (i) G3[mic]     I'   AF, G3[mic] rF          A';
        Reli(F) C             n Reli        A') for i E {m };
        Con(F) C Con(r,       n Con(-r, A');
 (iv) FV(F) c Fv(r,          n FV(-V, A').

PROOF. By induction on the depth of cutfree deductions in G3[mic]. A split
sequent is an expression r;   A; A' such that IT' AA' is a sequent. A
4.4. Interpolation and definable functions                                                   117

formula F is an interpolant of the split sequent F; F'   A; A' if H r                       A, F
and H    F A'. If F is an interpolant of F;          A; A' we write

         r;          F > A; A'

Basis. We show below how the interpolants for an axiom r, P, F'     A, P,
are to be chosen, dependent on the splitting. The second line concerns cases
which can arise in the classical system only.

         1'; PF'            L; A; PA'        FP;       F > A; PA'
         F; PF' -P> AP; A'                   FP; r'        AP; A'

For axioms L_L the interpolants are given by

         FI;              > L;'         F;         ±-3j5- A; LV

Induction step. We show for some cases of the induction step how to construct
interpolants for a splitting of the conclusion from interpolants for suitable
splittings of the premises. We first concentrate on the classical case; for
G3[mi] slight adaptations are needed.
Case I. The last rule is L+. There are two subcases, according to the
position of the principal formula in the splitting:

r'; r         A'; AA       r.B, r'       A; A'        r; r'   1)       A; AA'      r; Br'   A, A'
        r(A         B);                                       r; (A         B)ri

To see that, for example, the case on the left is indeed correct, note that
by the 1H for the premises we have (1) rc         AA, (2) rip      A', (3)
Br D, A, (4) I' CA'. From (1) and (3), by closure under Weakening,
CF      .AD, rBc AD; from this with L-4, r(A --+ B)C DA, and by
     1"(A -4 B)     (C > D)A. Fi(C > D) A' is obtained from (2) and
(4) by a single application of L-4.
  C > D and C A D satisfy the requirements (i)(iv) of the theorem, as is
easily checked.
Case 2. The last rule applied is R-4. There are again two subcases:

                    AF;       c > BA; A'                F;             c>
               F;         c > A -4 B, A; A'           r; r'        >     ;A -4 B,
The first of these cases has no analogue in G3[mi]. To see for the first case
that the interpolant for the premise is also an interpolant for the conclusion,
note that FA       AC implies r     A, A -4 B, C. The checking of the other
properties is left to the reader.
118                                    Chapter 4. Cut elirnination with applications

Case 3. The last rule is Lb. The two subcases are

          r, VxA, A[xlt];ri      > A, A'       F; A[xlt], VxA, F'            >
                                                                 Bigc
            F, VxA;              A; A'              F; VxA, F'          [dig]A, A'

In the first subcase,

             FV(C) \ (FV(FAVxA) n FV(PA')),
             Con(C) \ (Con(FAVxA) n Con(F'A')),

77 a sequence of fresh variables; in the second subcase,

            = FV(C) \ (Fv(rA) n FV(VxA F'A')),
          cr= Con(C) \ (Con(FA) n Con(VxA F'A')),

il a sequence of fresh variables. The case where the last rule is R3 is treated
symmetrically.
Case 4. The last rule is L.

                  FA; F'   C > A; A'           r;         c>
                 F, 3xA;      C > A; A'      F; 3xA, F'           A; A'

where x     FV(IVAA'). To see that the indicated interpolant is correct, note
that C does not contain x free.
  The case where the last rule is RV can be treated symmetrically.
  Let us now consider one of the least boring cases for G3m, namely where
the last rule is L-4. The interesting subcase is

                      r'; A > B, r C > A       r, B; r' D > E
                               r, A > B;     C-4D> E

By the Ill we have A -4 B, c, r A and r, B D, and by weakening also
r, A > B,C D; applying L-4 we find r, A > B,C D, hence with R>
r,A       B C* D.
  By the Ill we also have r     C and r',       E; weakening the first yields
r', c > D     C, and then by a single application of L-4   c --+ D      E. E

4.4.2A. A Complete the proof of the interpolation theorem.

4.4.2B. A (Beth's definability theorem) Let A(X) be a formula with n-ary rela-
tion symbol X in language L. Let R, R' be relation symbols not in L, and assume
   A(R) A A(R')    Ve(Re R'e). Show that there is a formula C in L such that
   A(R) .`91e.(C Re).
4.4. Interpolation and definable functions                                               119

Interpolation with equality and function symbols
We shall now show how the interpolation theorem for logic with equality and
function symbols may be obtained by a reduction to the case of pure predicate
logic.

4.4.3. DEFINITION. We introduce the following notations:
Eqo         Vx(x = x) AV xy(x = y + y = x) AVxy z(x =gAy=z --+ x = z),
Eq( f)                =            = fi'),
Eq (R)                =     A

For a given language let Eq be the set consisting of Ego, Eq(f) for all func-
tion symbols f, and Eq (R) for all relation symbols R of the language. We put
Eq(Ri, ...,R)       Eq(Ri),    ,Eq(Rn), and Eq(fi,... , fn) Eq(f1), ,Eq(fn).
For notational simplicity we shall assume below that our language has only
finitely many relation symbols and function symbols. This permits us to
regard Eq as a finite set, but is not essential to the argument.
   We write Eq(A), Eq(r) for Eq with the function symbols and relation sym-
bols restricted to those occurring in a formula A or a multiset F. Let
            3!y Ay := Ay(Ay A       z(Az + z = y)).

If Fi is a predicate variable of arity p(i) + 1, for 1 < i < n, then

             Fn (Fi) := Vi3!y Fi(xy) A Eq(Fi),
                          ,F) := Fn(Fi),     .   , Fn(Fn)

Let us assume that to each n-ary function symbol A in A there is associated
the n 1-ary relation symbol F, Fi not occurring in A. Then Fn(A) consists
of all Fn(Fi) for the A occurring in A. Similarly for Fn(r), r a multiset.

4.4.4. DEFINITION. Let         . . ,f be a fixed set of function symbols of the
language, and F1, . Fn be a corresponding set of predicate symbols, such
                             ,




that the arity of F, is equal to the arity of A plus one. Relative to this set of
function symbols we define for each term t of the language a predicate t*(x)
(x Ø FV(t)) by the clauses:

         Y*(x) := (x = y);
         fi(ti,   ,   tp)*(x) := Vxj.   xp (tI (xi ) A . .. A tp* (xp)   Fixi   xpx);

         g (ti,   , tp)* (x) := Vxi xp(ti (xi) A... A tp*(xp) > g (xi,          ,   xp) = x),
         for all function symbols g distinct from the A.
We associate, relative to the same set of function symbols, to each formula A
not containing P a formula A*, by the clauses:
120                                      Chapter 4. Cut elimination with applications

      (t1 = t2)* := Vxix2(tI(xi) A t(x2)           x1 = x2);
      (Rti      tp)* := Vxi      xp(tT (xi) A . . . A   t(x)       Rxi   xp);

      * is a homomorphism w.r.t. logical operators.

Finally, for any formula A we let A° be the formula obtained from A by
replacing everywhere subformulas of the form Fiti tpt by fiti       tp = t. El
Note that (I = I')* is equivalent to = I', and that (f())* (y) is equivalent
to F(, y).
   Up till 4.4.12, we may take the discussion to refer to a fixed set    , fn

of function symbols, with corresponding relation symbols F1,. , Fn; we shall
sometimes abbreviate En (P) as En.

4.4.5. LEMMA. In G3[mic] we have
      H Eq, F     A iff F- Eq (FA), r        A, F- r          A;

      if I-- Eq, Fn(P), r       A, then Eq, ro          A°.

Combining (i) and (ii) produces

      if 1- Eq \ Eq(f), Fn(P), r        A, then I-- Eq, ro         A°.

PROOF. The first statement is proved by replacing in the proof of Eq, rA
all occurrences fti...tn of n-ary function symbols f not occurring in 1.
A by t1, which amounts to interpreting f by the first projection function
(from an n-tuple to the first component), and replacing all predicate symbols
not occurring in 1-     A by T      J > I. This makes the corresponding
equality axioms trivially true; the result will be a derivation of a sequent
Eq(FA), E, 1.     A, where E is a set of derivable formulas which may be
removed with Cut.
   The proof of the second statement is easy: if we replace formulas Fit' tnt
by fiti tn = t throughout, Fn(P) becomes provable.

4.4.6. LEMMA. The following sequents are provable in G3m:
         Eq      (x = t)
         Eq      (A 4-÷ A*°),

where t is arbitrary, and does not contain x, and A is any formula not con-
taining         Fn
PROOF. The first assertion is proved by induction on the complexity of t, the
second statement by induction on the logical complexity of A, with the first
assertion used in the basis case.
4.4. Interpolation and definable functions                                                          121

4.4.7. LEMMA. For any term t, G3m                          Eq, Fn(P)         3!x(t* (x)).
PROOF. By induction on the construction of t. We consider the case t
fi(ti, ti,); other cases are similar or simpler. To keep the notation simple,
         ,

let p = 1. By the Ili,
         Eq, Fn, 4(y),     q(z)          y       z, so
         Eq,Fn,t1(y), f;(z),      F(y, u)              F(z, u).

Now t* (z) = Vy(t(y)            Pyz), hence

         Eq, Fn,     (y), F(y, u)            t* (u).

Fn contains Vx3!yFxy, hence

         Eq, Fn,     (y)       3ut* (u).

We can also prove

         Eq,   fl(y),e(z),e(u)               z      u,

which suffices for the statement to be proved.

4.4.8. LEMMA. Let t, s(y) be terms, A(y)* a formula not containing F1, . .
F. Then we can prove in G3m:
         Eq, Fn, t* (x)        s(x)*(z) ++ s(t)* (z),
         Eq, Fn, t* (x)        A(x)*     A(t)* (z).

PROOF. The first statement is proved by induction on the complexity of s,
the second statement by induction on the logical complexity of A, using the
first statement in the basis case.
   As a typical example of the inductive step in the proof of the first state-
ment, let s(x)       g(si(x),   , sp(x)) (g not one of the fi). Then s(t) E
g(si(t), , sp(t)). By the
         Eq, Fn, t(x)*         si(t)* (y) ++ si(x)*(y) (1              i     p).

Assume now t* (x) and

         g (s (t),     ,   sp(t))* (y)        Vyi        Yn (Aisi (t)*(yi)         y = g (yi ,   , yp)).

Using the II-I, the displayed assumption is equivalent to

         Vyi       Yn(Aisi(x)*(Yi)               Y = (Yi          yp)),

i.e. to g(si(x),     , sp(x))* (y).
122                                  Chapter 4. Cut elimination with applications

4.4.9. LEMMA. Let A(x) be a formula not containing a relation symbol
from P. Then we can prove in G3m:

            Eq, Fn(P),VxA(x)*      A(t)*;     H Eq, Fn(P), A(t)*   3xA(x)*   .




PROOF Immediate by lemmas 4.4.7, 4.4.8.

4.4.10. LEMMA. Let r          A not contain relation symbols from P. Then we
have in G3 [mic]:

          if H Eq, F     A then   H Eq,Fn,r.       A*.


Hence, by 4.4.5, if H Eq,    =- A, then h Eq \ Fn(?), Fn (P), r.    A*.

PROOF. The easiest way to establish this result is to use the equivalence of
sequent calculi with Hilbert-type systems; so it suffices to establish for H[mic]
that

          If Eq h A then Eq, Fn h A*.

The proof is by induction on the depth of derivation of Eq h A in the H-
system.
Basis. If A is an element of Eq, other than Eq(fi), the assertion of the theorem
is trivial. If A a Eq(fi), A* becomes equivalent to

                 =           =

which is equivalent to

          Vigi(g =     -4 Vyy'(Figy A FiVy' > y = y')),

which follows from Fn(Fi).
  If A is a propositional axiom, or a quantifier axiom of one of the following
two types (x FV(B), y a x or y FV(A)):

          Vx(B -4 A) -4 (B   VyA[x/y]) or
          Vx(A    B) > (3yA[x/y]    B),

then A* is an axiom of the same form. If A is one of the axioms

          Vx A > A[x        A[x It] -43x A,


the statement of the theorem follows from the lemma 4.4.9.
Induction step. It s readily seen that application of >E or VI permutes with
application of *.
4.4. Interpolation and definable functions                                 123

4.4.11. THEOREM. (Interpolation theorem for languages with functions and
equality) For G[123][mic], if f- Eq, A B, then there is an interpolating
formula C such that

        Eq, A             Eq, C    B;

      all free variables, individual constants, function constants, predicate
      letters (not counting =) in C occur both in A and in B.

PROOF. Assume

           Eq, A      B

then by 4.4.5, (i)

           Eq (A), Eq (B), A      B.

Applying 4.4.10 and 4.4.5(i) we find that

           Eq- (A), Fn(A), Eq-(B), Fn(B), A* r. B*,

where Eq- (A) = Eq(A) \ (f), Eq-(B) = Eq(B) \ (f). Hence

           (AEq- (A) A AFn(A) A A*)          (AEq-(B) A AFn(B)     B*),

hence by the interpolation theorem for predicate logic without function sym-
bols and equality, for some D

           AEq-(A) A AFn(A) A A* D,
           D AEq-(A) A AFn(A) A A* > B*,

that is to say

           Eq- (A), Fn (A), A*      D and H Eq- (B), Fn(B), D     B*.

Then apply the mapping ° and let C           D°, then by 4.4.5:

           Eq(A), A       C,      Eq(B), C     B.

Condition (ii) for C readily follows from the corresponding condition satisfied
by D.
  As a by-product of the preceding arguments (in particular 4.4.10) we obtain
the following theorem on definable functions.
124                                  Chapter 4. Cut elimination with applications

4.4.12. THEOREM. (Conservativity of definable functions) Let T be a first-
order theory in a language L, based on C, I or M. Let T H Vg3!yA(g, y)
of length n). Let f be a new function symbol not in L. Then T+VgA(g, f x)
is conservative over T w.r.t.     (i.e. no new formulas in L become provable
when adding `vt 'A(1, f x) to T).

PROOF. Let F0 be a finite set of non-logical axioms of T, such that ro
VgA!yA(Y, y). Consider the mapping * of 4.4.4 with f for fi,     , fn, and F

for F1, , Fn. If I F1 B  in T, with r, a finite subset of T, F1 in  language
    {f}, B in L, then by 4.4.10 in the original T with F added to the language
H F1, Fn(F)     B (since F1 is not affected by *). But if we substitute A(g, y)
for F, Fn(F) is provable relative to ,C from F0, hence I rori       B in L, i.e.
T B.


REMARK. The result extends to certain theories T axiomatized by axioms
and axiom schemas, in which predicates appear as parameters. Let T H
VgA!yA(g, y), let f be a new function symbol not in the language G of T, and
let T* be T with the axiom schemas extended to predicates in the language
G U {f}. If now the new instances of the axiom schemas translate under
* (substituting A for F) into theorems of T, the result still holds. This
generalization applies, for example, to first-order arithmetic, with induction as
an axiom schema; the translation * transforms induction into other instances
of induction.


Interpolation in many-sorted predicate logic

4.4.13. Many-sorted predicate logic is a straightforward extension of or-
dinary first-order predicate logic. Instead of a single sort of variables, there
is now a collection of sorts J, and for each sort j E J there is a countable
collection of variables of sort j; the logical operators are as before. We think
of the collection of sorts as a collection of domains; variables of sort j range
over a domain D.
   Furthermore the language contains relation symbols, constants, and func-
tion symbols as before. In the standard version, the sorts of the arguments
of an n-ary relation symbol of the language are specified, and the sorts of
arguments and value of the function symbols is specified.
   Only marginally different is a version where for the relation symbols the
sort of the arguments is left open, so that             is a well-formed formula
regardless of the sorts of the terms t1, . ,tn.
   Here we restrict attention to many-sorted languages with relation symbols,
equality and constants, but no function symbeds; the sort of the arguments
of a relation symbol is left open.
4.4. Interpolation and definable functions                                         125

4.4.14. DEFINITION. A quantifier occurrence a in A is essentially universal
[essentially existential], if a is either a positive occurrence of V of [3] or
a negative occurrence of 3 [of V]. A quantifier occurrence a in a sequent
F    A is essentially universal [essentially existential] if the corresponding
occurrence in A F      V .6, is essentially universal [essentially existential].
  Let Un(A) be the collection of sorts such that A contains an essentially
universal quantifier over that sort, and Ex(A) the collection of sorts such that
A contains an essentially existential quantifier over that sort; and similarly
for sequents.
  Inspection of our proof of the interpolation theorem shows that essentially
universal quantifiers in the interpolant derive from essentially universal quan-
tifiers in A =- F and that essentially existential quantifiers derive from es-
sentially existential quantifiers in F'   A'. So an interpolant C to A =- B
contains an essentially universal [existential] quantifier if A [if B] contains an
essentially universal [existential] quantifier.
  This observation straightforwardly extends to many-sorted predicate logic,
so that one obtains

4.4.15. THEOREM. (Interpolation for many-sorted predicate logic without
function symbols) If H A + B, there exists an interpolant C satisfying all
the conditions of theorem 4.4.11 and in addition
         Sort(C) c Sort(A) n Sort(B),
         Un(C) c Un(A), Ex(C) c Ex(B).

PROOF. For many-sorted languages without equality and without function
symbols, we can check by looking at the induction steps of the argument for
theorem 4.4.2 that an interpolant satisfying the conditions of the theorem
may be found; this is then extended to the language with equality by taking
from the argument for 4.4.11 what is needed for equality only. We leave the
details as an exercise.

4.4.15A. 4 Prove the interpolation theorem for many-sorted logic.

4.4.16. Persistence. We sketch an application of the preceding interpolation
theorem to the model theory of classical logic.
   A first-order sentence A is said to be persistent, if the truth of A in a model
is preserved under model-extension. Let us consider, for simplicity, a language
   with a single binary relation symbol R. For variables in .0 we use x, y, z.
Persistence of a sentence A means that for any two models M (D, R) and
M' (D', R') such that
         D c D',       n (D x D) = R,
126                                      Chapter 4. Cut elimination with applications

we have
          If .A4   A then .A4'      A.
This may also be expressed by looking at two-sorted structures satisfying
(*)       M* _= (D, D', R, R') with D c D', R' n (D x D) = R.
We extend ,C to a two-sorted language L' by adding a new sort of variables
x', y', z' and a new predicate symbol R'. In this language the persistence of
A in ,C may be expressed as
          1- Ext AA     A',
where Ext is the formula Vx3y/(x = y') A Vxy(R(x, y) ÷--> R' (x, y)), expressing
the conditions on the two-sorted structure in (*). A' is obtained from A by
replacing quantifiers of L by quantifiers of the new sort, and replacing R by
R'. By interpolation, we can find a formula F such that
          Ext A A --+ F',     F'   A'.
Since Ext is not essentially universal w.r.t. the new sort of variables, F'
contains only variables of the new sort and all quantifiers are essentially ex-
istential. From this we see that for F obtained from F' by replacing R' by R
and new quantifiers by old quantifiers, that f- F E4 A. So A is equivalent to
a formula in which contains only essentially existential quantifiers.
   It is not hard to prove the converse: if all quantifiers in A are essentially
existential, then A is persistent. The obvious proof proceeds by formula
induction, so we need an extension of the notion of persistence to formulas.
A formula A with FV(A) = g is persistent if for all sequences of elements cr
from D of the same length as g we have
          If M A[g Id] then M'              A[g 14.


4.5       Extensions of G1-systems
This section is devoted to some (mild) generalizations of cut elimination, with
some applications.

4.5.1. Systems with axioms
Extra (non-logical) axioms may be viewed as rules without premises; hence
an application of an axiom A in a prooftree may be indicated by a top node
labelled with A with a line over it.
  It is possible to generalize the cut elimination theorem to systems with
wdoms in the form of extra sequents ("non-logical axioms"). In the case of
the systems Gl[mic] we again use Gentzen's method with the derived rule
of Multicut (4.1.9). The statement is as follows:
4.5. Extensions of Gi-systerris                                              127

PROPOSITION. (Reduction to cuts on a.xioms) Let D be any deduction in
Gl[mic] + Cut from a set of axioms closed under substitution (i.e. if r =- A
is an axiom, then so is r[/r1
   Then there is also a deduction containing only cuts with one of the premises
a non-logical axiom.
   If the non-logical axioms consist of atomic formulas only, there is a deduc-
tion where all cuts occur in subdeductions built from non-logical axioms with
Cut. Alternatively, if the non-logical axioms contain atomic formulas only
and are dosed under Cut, we can assert the existence of a cutfree proof.
PROOF. The cut elimination argument works as before, provided we count as
zero the rank of a cut between axioms removing their principal formulas. Z
In particular, when the axioms contain only atoms, and possibly I, we con-
clude that a deduction of F =- A with cuts only in subdeductions constructed
from non-logical axioms and Cut, contains only subformulas of F       A, atoms
occurring in non-logical axiornS, and I (if it occurs in a non-logical axiom).
  Below we present two examples; but in order to present the second example,
we must first define primitive recursive arithmetic.

4.5.1A. * Prove the proposition by carefully checking where Gentzen's proof of
cut elimination (cf. 4.1.9) needs to be adapted.

4.5.2. Primitive recursive arithmetic PRA
 This subsection is needed as background for the second example in the next
subsection, and may be skipped by readers already familiar with one of the
usual formalizations of primitive recursive arithmetic, a formalism first intro-
duced by Skolem [1923]. For more information, see e.g. Troelstra and van
Dalen [1988, 3.2, 3.10.2], where also further references may be found. PRA
is based on Cp, with equality between natural numbers and function sym-
bols for all primitive recursive functions. Specifically, there are the following
equality axioms (in which t, t', t", r, §. are arbitrary (sequences of) terms):
         t = t,
         t = t" A = t" --+ t =
         r=        f() =
for all function symbols f of the language. For the functions we have as
axioms
         0S0, St = Ss -4 t = s,
and defining axioms for all primitive recursive functions. For example, for
addition f + we have axioms (t, s arbitrary terms)
         f +(t, 0) = t,   f +(t, Ss) = S(f_E(t, s)).
128                                    Chapter 4. Cut elimination with applications

Finally, we have a quantifier-free rule of induction:
         If F I- A(0) and        A(x) --+ A(Sx), then          A(t),
for quantifier-free A(x) and r not containing x free.

REMARKS.    (i) If we define I as SO -= 0, the axiom SO     0 becomes re-
dundant: define by recursion a "definition-by-cases" function satisfying
Os° = t, Ots(Sr) = s, then 0 = SO        t =- Ots0 = Ots(S0) = s, i.e.
O = SO -+ t = s, and from this, by induction on 1A1, o = so    A, for
all formulas A.
       The axiom St = Ss -4 t = s is in fact a consequence of the presence
of the primitive recursive predecessor function prd satisfying prd(St) = t,
prd(0) = 0. For if St = Ss, then t = prd(St) = prd(Ss) = s.
       The axioms may be formulated with variables, e.g. x=zAy=z
x -= y, and the induction rule with conclusion r A(x), provided we add a
substitution rule:
         If r(x)    A(x), then r(t)      A(t).
       The equality axioms for the primitive recursive functions are in fact
provable from t = s -4 St = Ss and induction; the proof is long and tedious
and left to the reader.
      If we base PRA on Ip instead of Cp, then decidability of equality,
and hence by formula induction, A V      for all A, is provable (Troelstra and
van Dalen [1988, 3.2]), hence this theory coincides with the theory based on
classical logic.
        PRA can be formulated as a calculus of term equations, without
even propositional logic (the addition of propositional logic is conservative;
references in Troelstra and van Dalen [1988, 3.10.2]).

4.5.3. EXAMPLES. Example I. Logic with equality may be axiomatized by
adding the following sequents as axioms:
            t=t
         t = s, A[x It]     A[x I s] (A atomic)
Example 2. Primitive recursive arithmetic may be axiomatized by adding to
the axiomatic sequents of example 1 the following:
         St =Ss      t = s; 0 = St         ;

            t = s for any defining equation t = s
                          of a primitive recursive function;
         t<           s<t s<St, s=t s<St;
         s < St     s < t, s = t,       s < t, u = t, t < s;
         R(ti,..           fR(ti,     ,tn) = 0;
4.5. Extensions of Gl-systents                                                 129

For any primitive recursive relation P there is among the primitive recursive
functions a function tp, such that tp(y,F) := min[u <y A ,P(Su, 2')], that
is to say, tp(y,,F) is the least u < y such that ,P(Su, 2') if existing, and y
otherwise. tp is characterized by the equations (dropping the parameters 2'
for notational simplicity):

         te(0) := 0,

                            if tp(y) < y,
         tp (Sy) := /tp(y)
                      Stp(y) if tp (y) = y A P(Sy),
                        tp(y) if tp(y)= y A P(Sy).

These equations can easily be brought in the standard form of a primitive
recursive definition. We can express induction w.r.t. P by the sequents:

         P(0,     P(tp(u,               P(u,
         P(0,1, P(Stp(u,           1
To see that the first sequent holds, observe that if P(0,       then either tp(u,)
   u, and then P(tp(u,               .1J(Stp(u, 42.), or tp(u, = u, and
                              2"), while
then P(u, 2'). Also, by the preceding, if P(0,  and P(Stp(u, 2'), 2'), then
tp(u,      u is excluded, hence tp(u, = u and then P(u,2'); this explains
the second sequent.
  We want to show that the following induction rule (x not free in 1') is
derivable: if H r   P(0), H r, Px P(Sx), then H r   Px. By Cut we get
     P(tp(x)), P(x) and 1', P(Stp(x)) P(x). Then

                                       P(tp(x)),P(x)        P(tp(x)) P(Stp(x))
     P(Stp(x))         P(x)                    r, r    P(x),P(Stp(x))
                         r, r, r       P(x),P(x)

and then r      P(x) by closure under Contraction. Application of the gener-
alized cut elimination to the systems of these examples yields the following
proposition (also easily proved model-theoretically).

4.5.4. PROPOSMON.

      Predicate logic with equality is conservative over the propositional part
      of predicate logic with equality;

      PRA with full predicate logic is conservative over PRA with proposi-
      tional logic only.
130                                   Chapter 4. Cut elimination with applications

REMARK. We also obtain an alternative proof of: if F        A is a sequent not
containing =, which is provable in predicate logic with =, then in fact F   A
is also provable without the axiom sequents for equality (cf. 4.7).


4.6      Extensions of G3-systems
Here we shall consider additional non-logical axioms and rules for G3-systems.
We concentrate on the intuitionistic case, that is to say, extensions of G3i.
The case of G3c can be dealt with similarly.
  We consider additional rules of four types

4.6.1. DEFINITION. Let F be an arbitrary multiset, A an arbitrary formula,
       P1, . . . , Pn,      Qi, , Qk-1, Q' atomic formulas. (If k = 0, IQ' is
taken to be empty.) We list four types of rules below, where the formulas in
  , Q' represent active formulas in the premises, and 15, P' are principal in the

conclusion.

        Rui (P , Pi) F, P

        Ru2(P) r,P          A

                       F,P,Qi     A (1<i<k-1)
        Ru3(P; C2)
                                r,P   A


        Ru4(0., (21,     r'c-j P
If we want to deal with extensions of G3c, the treatment of antecedent and
succedent must become symmetric.

REMARK. Addition of Ru2(P ) to G3i + Cut, s is equivalent to addition of
r,     1, as follows by cutting r, P 1 with F, P, 1 A.
   Addition of Ru3(P, ej) to G3i + Cut is equivalent to the addition of

(1)     r,P
To see that (1) justifies Ru3(P; Cj), let D derive r, P,v A from sequents
r, P,Q, A by repeated use of LV. Then the rule is justified by


                                      r:13'"Acutcs
4.6. Extensions of GS-systems                                                             131

Conversely, we obtain (1) by deriving from the axioms r,P,Qi                           Q, by
repeated RV the sequent r, P, Q.       then the rule yields r,P       V (j.
   Ru2 may be seen as a degenerate case of Ru3 where the number of premises
is zero.
  Addition of Ru4(, Q', P) is equivalent to the addition of

(2)         r, A            Q'P.
For if r,      Q' then by LA and R--> we find r                         A 0.    Q', and Cutc,
with (2) yields r P. Conversely,

            r, A            Q',0
                                           (1       < k) RA
                    r, A           Q',(v        A
                                                               F' Q*'          Q/
                                      r,    Ci      crQ.        Ru4(0,q,P)
                                       r, A cJ             P
Finally, the addition of Rui(i", P') is equivalent to the addition of Ru3(./5; P')
by the following one-step deductions:

                    r                  r,P,p/        A              r P P'      P'
            Cutcs
                               r,P         A
                                                              Ru3
                                                                     r,pP'
4.6.1A. * Assuming dp-closure under LC and LW, show that a generalization of
Ru3 to a rule with several active formulas in the premises, for example
            r, P, Qi, (22     A       r,P,Q3,Q4A
                              r, P     A

is equivalent to a finite set of rules of type Ru3.

4.6.2. DEFINITION. A basic cut is a cut with atomic cutformula principal
in the conclusions of instances of Rui (1 < i < 4).                   N

4.6.3. DEFINITION. A set of rules X is closed under substitution, if for every
instance a of a rule from X, the inference obtained by applying a substitution
      to each of the premises and the conclusion of a, is again an instance of
a rule from X.
  A set of rules X is closed under (left-)contraction, if contraction on the
conclusion of an instance of X yields the conclusion of another instance of X.
  A G3i-system is a system of sequents formulated in a first-order language,
containing the axioms and rules of G3i, and in addition (1) a collection
of rules of types Rui (1 < i < 4) which is closed under substitution and
Contraction plus (2) basic context-sharing cuts.
132                                          Chapter 4. Cut elimination with applications

LEMMA. Let S be any G3i-system. Then
      The inversion lemma of G3i extends to S.
      S and S + Cut are dp-closed under left-weakening and left-contraction,
      and under the rule: if 1-,,, r I then f-7, r   A (a variant of right-
      weakening).

PROOF. (i) The proof for G3i also applies to S, since all the principal formulas
in the additional rules are atomic.
   (ii) Routine extension for the proofs for G3i.                             El


4.6.4. THEOREM. (Cut elimination for G3i-systems) Context-sharing cuts,
except possibly basic cuts, may be eliminated from proofs in S + Cut.
PROOF. The proof for G3i extends to G3i-systems, since it remains true that
whenever at least one of the cutformula occurrences (say a) in a cut is not a
principal formula, then either the a belongs to the context of an axiom, and
the whole cut is redundant, or a occurs in the conclusion of a rule, and the
cut may be permuted upwards on that side where a occurs. The new extra
axioms and rules, and the basic cuts, may be dealt with just as the other
rules and axioms. Finally note that the new rules can never participate in a
cut where both cutformula occurrences are principal unless the cut is basic,
since the principal formulas of the logical rules are never atomic.
   Let us check on the slight modifications in some of the cases.
Subcase la. Do is a non-logical axiom, and D is not principal. So D must be
of the form
                                                    Di
                                        D (Ru2)        D,r, 13.   A
                    Cut    r' ./5
                                              r 15
                                                ,      A
Now the conclusion is an instance of the same non-logical axiom.
Subcase lb. Do is a non-logical axiom and D is principal. Then T, is of the
form
                                                      D1
                    r,f3     P' (Rui)
                                                Pi ' r' P   A cute,
                                    r,./5'      A
If PI is context on the right, we can permute the cut upwards on the right.
If P' is also principal on the right, then either D1 is an instance of Ax, so A
is P', and the conclusion coincides with Do, or D1 is a non-logical rule, and
then we have a basic cut.
Subcase lc. Di is a non-logical axiom, and D is not principal in Di. Then
we have
4.6. Extensions of OS-systems                                                   133

                               Do
                        F,13            D        D,    15       P' (Rui)
                                              F,        P'
and the conclusion is again an instance of Rui; similarly if D1 is an instance
of Ruz.
Subcase id. D is a non-logical axiom, say of type Rui, and D is principal in
D1. Let P.        . . .     Then D is of the form
                              Do
                        ,   /5*         P0       P0,F,15*        P' (Rui)
                                             F, P.       P'
We may assume that Do is not an axiom (otherwise one of the earlier subcases
applies); now we may permute the cut upwards on the left. This is routine,
except in the case where Po is principal; but then we have an instance of a
Ru4-rule, and the cut is a basic cut.
Case 2. Neither Do nor D1 is an axiom, and D is not principal either on the
left or on the right. Then we can permute upwards as before, for example
                                    Doi
                    r, P, Qi            D             < i < k)

                                                      r,./3"     A
becomes
                                  Doi                  Di[Qi
                       r,P,Qi                D                        A
                                        r,P,Qi             A
                                                               (0 < i < k)
                                             r,./3"    A
Since we used "economical" thinning in this case, no appeal to closure under
Contraction is needed.
Case 3. This can at most yield basic cuts in the new situations.

COROLLARY. If the additional axioms and rules in S have their principal
formulas on the left only (i.e., are of the types Ruz, Ru3), then cut elimination
results in a cutfree proof (no basic cuts left).

4.6.4A. 4 Show that rules of the four types in 4.6.1 are sufficient to eliminate all
logically compound principal and active quantifier-free formulas from extra axioms.
Hint. A logically compound quantifier-free formula may be replaced by a set of
atomic formulas linked together by suitable axioms; for example, if we have asso-
ciated to B and C the atomic formulas PE and Pc respectively, we can associate
with B C a new atomic formula PE_G, with additional axioms PE_yc, PE Pc,
and PE
134                                    Chapter 4. Cut elirnination with applications

4.6.4B. 01 Formulate an adequate set of rule-types similar to 4.6.1 for the classical
case.


4.6.4C. 4 Give details of the cut elimination proof.


4.7      Logic with equality
4.7.1. DEFINITION. The theory of equality may be axiomatized by adding
to G3[mic] the rules
                         A             t = s, P[x / s], P[x/tbr
         Ref t=t'F               Rep
               F   A                       t = s, P[x /t],F =- A
where P is atomic. Let us call these theories G3[mic]. By the remarks
above, these theories are closed under Cut, Weakening and Contraction, pro-
vided the extra rules are themselves closed under ContraCtion. Duplication
can happen in Rep if P x = s; in this case Rep concludes t = s,t = s, F
A from t = s, t = s, s = s,r A. But if we contract the instances of t -= s
in premise and conclusion, the result is in fact an instance of Ref.
In order to prove equivalence with the extension of Gl[mic] with axiomatic
sequents for equality given before, we prove

4.7.2. LEMMA. In G3[mic] the following rules are admissible for all A:
                                                  t = s, A[x/ s], A[x /t],       A
         (i) H t = s, A[x/t]     A[x/ s]   (ii)
                                                      t= s , A[x/t],         A
PROOF. (i) is proved by induction on the depth of A. The most complicated
induction step is where A(x)     B(x)      C (x). In G3[mi] this case is
handled by the following deduction:
             t = s, Bt =. Bs (IH)
           = t,t = t,t = S, Bt =. BS
                                       Rep
            s = t, t = t, Bt Es
                s = t, Bt Bs Ref            s = t,Cs Ct (IH)
          s = t, Bs > Cs, Bt Bs              s = t,Cs, Bt Ct
                          s = t, Bs > Cs, Bt Ct
                          = t, BS -4 CS    Bt Ct R-4
In G3c= the lower weakening on the left is left out. The other cases are left
to the reader. (ii) is readily derivable from (i) and closure under Cut and
Contraction.

4.7.2A. 4 Supply the missing details in the preceding proof.
4.7. Logic with equality                                                     135

4.7.3. DEFINITION. Let us introduce a name for the following contracted
instance of Rep:
                                  s = t,t = t, F        A
                           Rep*
                                s = t, F   A
This is at the same time an instance of Ref, but in the next lemma we shall
show how to remove Ref from deductions (except possibly Rep*).

LEMMA.

      If r    A is equality-free and derivable in G3[mic]+ Ref + Rep* + Rep,
      all sequents F'    A' in the proof have no equality in A'.
      1fF      is equality-free, and derivable in G3[mic]+ Ref + Rep* + Rep,
      Ref can be eliminated from the proof.
PROOF. (i) If somewhere in the deduction of an equality-free r           A there
appears a F'       A' containing = in a formula A of A', A can only become
active in a logical rule, but will then appear as a subformula of the conclusion.
   (ii) We show how to eliminate a Ref-application appearing as the last in-
ference in a deduction 7, containing no other applications of Ref. The proof
is by induction on the depth of D. Let
                                   s = s,          A'

be the bottom inference of D; if s = s is not principal, we can permute the
application of Ref upwards over the preceding rule and apply the IH. If s = s
is principal, it is principal in Rep or Rep*:
                       s = s, P[x/ s], P[x/ s],             A'
                                                                 Rep
                           s = s, P[x / s], r"      A'
                                  P[x/s]
or
                            s = s, s = s, F' A'
                                                Rep*
                               s = s,       A'
                                    F'
In both cases we can apply dp-closure under Contraction to the derivation of
the topline, apply Ref and apply the IH to the resulting deduction.

4.7.4. THEOREM . G3 [mic]          is conservative over G3 [mic] .
PROOF. Immediate from the preceding lemma: once an equality appears on
the left, in a deduction without Ref, equalities remain present on the left,
whereas the appearance of an equality on the right is excluded by the first
half of the lemma.                                                            N
136                                      Chapter 4. Cut elimination with applications

4.8      The theory of apartness
4.8.1. Apartness is intended as a positive version of inequality. Thus, for
example, in the intuitionistic theory of real numbers, two numbers are apart
if the distance between them exceeds a positive rational number The pure
theory of apartness AP has besides equality a single primitive binary relation,
#; a simple description is to say that it can be formalized on the basis of Ni
with the following axioms added:

REFL Vx(x = x),
SYM      Vxy(x = y      y = x),
TRA      Vxyz(x =y A y=z              x = z),
# EQ Vxyx(x#y A x = x' Ay=y1+ x'
AP1      Vxy(--ix # y + x = y),
AP2      Vx( x # x),
AP3      Vxyz(x#y-->x#zVy#z).
In this theory we can prove that it # s t = s. This permits us to consider
instead of AP an equivalent theory AP', formulated with a single binary
relation #, where equality is simply defined as

         t = s :=    # s.

The only extra axioms are now AP2 and AP3.
   From AP3 one easily proves in AP' the equality azdom # EQ for #. To
see this, note that if x # y, x = x', then by the definition of equality ,(x # x'),
and since by AP3 applied to x # y we find x # x' V x' # y, and the first disjunct
is excluded, we have x' # y, etc.
   We can reformulate AP' as a G3i-system AP-G3i as follows: there are an
extra wdom of type Ru2 and an extra rule of type Ru3:

         #1 r,t#t        A



         #2
              t#s,t#r,r           A      t#s,s#r,r        A
                             t#8,1-         A

We define t = s := # s. As an immediate consequence of the fact that the
principal formulas appear on the left only, we have


4.8.2. THEOREM. Cut es is completely eliminable from AP-G3i (i.e. we need
not even basic cuts).
4.8. The theory of apartness                                                 137

4.8.3. COROLLARY. A cutfree deduction of r                A in AP-G3i contains
only subformulas of F, A and atomic formulas.                                E
We now want to characterize the equality fragment of the theory of apartness.
We introduce "approximations" to apartness as a sequence of inequalities of
ever increasing strength:

         t# °s := -'t= 8;      t #n+1 S := V X(t #n X V 8 #n X).

DEFINITION.         The theory EQAP consists of the pure theory of equality
(REFL, SYM, TRA) with in addition the following axioms for all n E IN:
INEQn    --it #n+1 s      t = s.                                               E
It follows that

         For all n, --it #n s ¡4 t = s.

4.8.4. DEFINITION. We extend the notions of positive and negative context
as follows. A positive seguent-context S+[*[ is of the form F, ./V.  A or of
the form F      P, where A f, P are negative and positive formula contexts
respectively. Similarly for a negative seguent-context S-H, with the roles of
Ar, P interchanged.                                                        E
The proof of the following lemma is immediate.

LEMMA. Let S+[*], S-[*[ be a positive and a negative sequent-context re-
spectively. Then
         if H s+[t #n+1. 8], then I-- S+[t #n s],
         if I-- S[t #n 8], then I-- Sit #n+1 sl.

4.8.5. DEFINITION. Let r      A be a sequent in the language of AP-G3i.
Then (r A)' is obtained from r A by replacing all positive occurrences
of # by 0, and all negative occurrences by #. For (r A)' we also write
rn    An.                                                                      El

By repeated use of the lemma we have that if h (r        A)' then H (F A)'+1,
for all n E IN. Note that if all occurrences of # in I'         A occur under a
negation (i.e., r      A is a statement in equality theory), then (r   A)' holds
in EQAP iff r          A is provable in EQAP, since -it e s i4 t = s -4 --it # 8.

4.8.6. THEOREM. Let I"      A be a sequent in the language of pure equality
which has been proved in AP-G3i by a deduction D. Then we can effectively
transform 7, into a deduction V* in EQAP of          Am for a suitable m.
138                                         Chapter 4. Cut elimination with applications

PRooF. We show by induction on the depth of deductions 7, in AP-G3i with
conclusion r A that we can transform 1, into Ton in EQAP with conclusion
(F    A)" for a suitable n. For definiteness we shall assume EQAP to be
axiomatized with in a system based on G3i with Cut, and logical axioms
with principal formulas of arbitrary complexity. Furthermore below p will
always be max(n, m).
Case 1. 1, is an axiom. For any axiom 1 , , D° is provable in EQAP.
Case 2. V ends with an application of #2 and is of the form
                          Di                    D2
                   t # s,t# r, r A t # ,s, s # r,F A
                                   t # s,r               A
Remember that t #P+1 s = vz(t #P z v 8 #P -= z). Then we can take for the
transformed 1,

            tr 87t#nr7rn
                      DI'
                                   An
                                                            DT
                                                  t #m 8 8 #m r ,rrn         Am
            t#P s,t#P r,FP     AP   t#P s,s#Pr,FP                            AP
                      t#P s,t#PrV s#Pr,FP AP                                      Lv
                     t #P+1 s,t#P r V s #P r,rP                    AP
                                                                        LV
                               t #P+1 s, FP              AP
                            t #P-ki s, rP+1              AP+1
The transitions marked by the dashed lines are justified by the preceding
lemma, since rn'   An' (n' > n) is obtained from rn     An by replacing a
number of negative occurrences of #n by #''.
Case 3. 7, ends with a logical rule, for example a two-premise rule
                                   D1                    D2
                              r1
                                           FA       r2
                                          A1                  A2

Using the induction hypothesis for D1, D2, we see that we can take for the
transform of 1,
                                        7,n
                             r=
                            TY?

                                                   r2n        AT
                             ri;        .i=173'     ri        .4
                                   rP AP
For single-premise rules the transformation is even simpler.                           Z

4.8.7. THEOREM. The equality fragment of APP is EQAP.
PROOF. A formula in the language of equality is expressed in the language
with only # as a formula where all atomic formulas t # s occur negated. Let
F     A be such a statement, derived in APP. By the preceding proposi
we then obtain a proof of rn An for some n in EQAP. But since --it #n s
k--> --it # s, this is in EQAP equivalent to r A.                        El
4.9. Notes                                                                   139

4.9      Notes
4.9.1. The Cut rule. The Cut rule is a special case of a rule considered in
papers by Hertz, e.g. Hertz [1929]; Gentzen [1933b] introduces Cut. The proof
of cut elimination in subsection 4.1.5 follows the pattern of Dragalin [1979].
The calculus in 4.1.11 is precisely the propositional part of the calculus of
Ketonen [1944].
  It was recently shown that the introduction of Multicut in establishing
cut elimination for Gl-systems (4.1.9) can be avoided; see von Plato [1999],
Borisavljevie [1999].
   A detailed proof of cut elimination for m-G3i is found in Dyckhoff [1996].
   In studying the computational behaviour of the cut elimination process, it
makes sense to have both context-free and context-sharing logical rules within
the same system (cf. refconrules), see Joinet et al. [1998], Danos et al. [1999].
   Strong cut elimination means that Cut can be eliminated, regardless of
the order in which the elementary steps of the process are carried out (the
order may be subject to certain restrictions though). Strong cut elimination
is treated in Dragalin [1979], Tahhan Bittar [1999], Grabmayer [1999].
   The considerations in 4.1.11 may be extended to classical predicate logic,
and used to give a perspicuous completeness proof relative to a cutfree sys-
tem, thereby at one stroke establishing completeness and closure under Cut
 (not cut elimination). This was discovered in the fifties by several people
independently: Beth [1955], Hintikka [1955], Schiitte [1956], Kanger [1957].
For more recent expositions see, for example, Kleene [1967], Heindorf [1994],
Socher-Ambrosius [1994]. The ba,sic idea of all these proofs is to attempt,
for any given sequent, to construct systematically cutfree proofs "bottom-
up"; from the failure of the attempts to find a proof a counterexample to the
sequent may be read off. It was Beth who introduced the name "semantic
tableau" for such an upside-down Gentzen system; cf. 4.9.7.
  This idea is also applicable to intuitionistic logic, using Beth models (Beth
[1956,1959]) or Kripke models (Kripke [1965], Fitting [1969]), and to modal
logics, using Kripke's semantics for modal logic (cf. Fitting [1983]). See 4.9.7
below. Beth was probably the first to use multi-succedent systems for intu-
itionistic logic, namely in his semantic researches just mentioned.

4.9.2. Separation theorem. Wajsberg [1938] proved the separation theorem
for Hip; however, Wajsberg's proof is not completely correct; see Bezhan-
ishvili [1987] and the references given there. In exercise 4.2.1B a proof of the
separation property is sketched for all fragments of Hc except for the frag-
ments not containing negation, such as the implicative fragment. In order
to extend the sep_ar_ation theorem to this case, we consider the variant of Hc
with        > A replaced by Peirce's law. Then the axioms k, s (1.3.9) and
Peirce's law axiomatize 41c. This result is due to P. Bernays, and is not
140                                Chapter 4. Cut elimination with applications

hard to prove by a semantical argument. For other axiomatizations of
see Curry [1963, p. 250].
   Below we give a short semantical proof of Bernays' result, communicated
to us by J. F. A. K. van Benthem. The argument consists in the construction
of a Henkin set not containing a given unprovable formula A, i.e. a maximal
consistent set of formulas not containing A; the required properties are proved
with the help of the result of exercise 2.1.8F.
   Suppose 1,L A. Then, using a countable axiom of choice, we can find a
maximal set X of formulas such that X bz A (enumerate all formulas as
Fo,    F2, .. ., put Xo = 0, X7,±3. = X7, if X U {Fr} H A, X7,±1 = X U {Fr,}
otherwise, and let X = UnEIN Xn). It is easy to see that X is deductively
closed, that is to say, if X H B then B E X. For all B,C
(*)                  B + C E X if B%XorCEX.
For the direction from left to right, let B     C E X; if B E X then by
deductive closure C E X. Hence the right hand side of (*) holds. For the
direction from right to left, we argue by contraposition. Case I. Assume
C E X. Then X H B            C, hence X H A; contradiction, hence C ;Z X.
Case 2. Assume B X. Then X,B H A (maximality), hence X I B + A
(deduction theorem); also by the deduction theorem X H (B + C) --+ A.
Hence with 2.1.8F X H A; again contradiction, so B E X.
  By (*) we can now define a valuation vx (propositional model) from X, for
which we can prove for all formulas G: G E X iff v(G) = true.
  We have not found a really simple syntactical proof of the separation the-
orem for -41-1c. A syntactical proof may be obtained from the result in
Curry [1963, p. 227, corollary 2.3]; another syntactical proof is outlined in
exercise 6.2.7C.

4.9.3. Other applications. 4.2.2 was proved in Malmnds and Prawitz [1969],
and 4.2.3, 4.2.4 were proved in Prawitz [1965] (in all three cases by using N-
formalisms). Buss and Mints [1999] study the disjunction property and the
explicit definability property from the viewpoint of complexity theory. The
proof of 4.2.6 corresponds to Kleene's decision method for the system G3 in
Kleene [1952a].
  The notion of a RasiowaHarrop formula was discovered independently by
H. Rasiowa and R.. Harrop (Rasiowa [1954,1955], Harrop [1956,1960]). For
more information on the "Aczel slash" of exercise 4.2.4C (Aczel [1968]) and
similar relations, see the references in Troelstra [1992b].
  Another type of application of cut elimination, not treated here, concerns
certain axiomatization problems for intuitionistic theories, such as the ax-
iomatization of the f-free fragment of the theory of a single Skolem function
with axiom ViR(i,           R a relation symbol, see Mints [1999]. For other
examples, see Motohashi [1984a], Uesu [1984].
4.9. Notes                                                                141

4.9.4. The Gentzen system G4ip. This calculus, with its splitting of 1,4,
was recently discovered independently by Dyckhoff [1992] and Hudelmaier
[1989,1992]. Here we have combined the notion of weight as defined by Hudel-
maier with Dyckhoff's clever proof of equivalence with the ordinary calculus.
Long before these recent publications, a decision algorithm based on the same
or very similar ideas appeared in a paper by Vorob'ev [1964]; but in that pa-
per the present formalism is not immediately recognizable. Remarks on the
history of this calculus may be found in Dyckhoff's paper.
  In Dyckhoff and Negri [1999], a direct proof, without reference to G3i,
of the closure of G4ip under Weakening, Contraction and Cut is presented.
Such a proof is more suitable for generalization to predicate logic and to
systems with extra rules, since induction on the weight of sequents may break
down when rules are added. However, the proof is somewhat longer than the
"quick and dirty" proof presented here.
   A very interesting application of the system G4ip is found in a paper by
Pitts [1992]. In particular, Pitts uses G4ip to show that in Ip there exist
minimal and maximal interpolants (an interpolant M of I A B is said to
be minimal if for all other interpolants C we have h M =- C; similarly for
maximal interpolants). The corresponding property of Cp is trivial. Since
Pitts [1992] several semantical proofs of this result has been given; see for
example Visser [1996].


4.9.5. Interpolation theorem. This was originally proved by Craig [1957a]
for C without function symbols or equality, and in Craig [1957b] extended
to C with equality. Craig's method is proof-theoretic, using a special modifi-
cation of the sequent calculus. The theorem was inspired by the definability
theorem of Beth [1953]. Craig's theorem turned out to have a model-theoretic
counterpart, namely the consistency theorem of A. Robinson [1956].
   The refinement taking into account positive and negative occurrences is
due to Lyndon [1959]; Lyndon's method is algebraicmodel-theoretic. The
example 2x(x = c A --,Rx)     --,Rc shows that we cannot extend the Lyndon
refinement to constants or function symbols in the presence of equality (c
occurs positively on the left, negatively on the right, but has to occur in
every interpolant).
   Schiitte [1962] proved the interpolation theorem for I, using the method
of "split sequents", which he apparently learned from Maehara and Takeuti
[1961], but which according to Takeuti [1987] is originally due to Maehara
[1960].
  Nagashima [1966] extended the interpolation theorem to both C and I with
function symbols, but without equality, using as an intermediate the theories
with equality present. Inspection of his proof shows that with very slight
adaptations it also works for languages with function symbols and equality.
Kleene [1967] also proved interpolation for languages with equality and func-
142                                 Chapter 4. Cut elimination with applications

tion symbols by essentially the same method. Our exposition of interpolation
for languages with functions and equality combines features of both proofs.
Felscher [1976] gives an essentially different proof for languages with func-
tion symbols but without equality (this paper also contains further historical
references).
   Oberschelp [1968] proved, by model-theoretic reasoning, for classical logic
with equality, but without function symbols or constants, interpolation w.r.t.
positive and negative occurrences of relation symbols plus the following con-
dition on occurrences of = in the interpolant: if = has a positive [negative]
occurrence in the interpolant C of I- A =- B (i.e., I- A =- C, F- C   B) then =
has a positive occurrence in A [negative occurrence in B]. As noted by Ober-
schelp, we cannot expect a symmetric interpolation condition for =, as shown
by the sequents x = y =- Rx V -,Ry and Rx A -,Ry          x 0 y. Fujiwara [1978]
extended this to interpolation w.r.t. functions, positive and negative occur-
rences of relations, and the extra condition for =. Motohashi [1984b] gave a
syntactic proof of this result and moreover extended Oberschelp's result (i.e.
without the interpolation condition for functions) to intuitionistic logic.
   Schulte-Mönting [1976] gives a proof of the interpolation theorem which
yields more fine-structure: one can say something about the complexity of
terms and predicates in the interpolant.
   For a model-theoretic proof of interpolation for C with functions and con-
stants, but no =, see, for example, Kreisel and Krivine [1972]. There is an
extensive literature on interpolation for extensions of first-order logic, most
of it using model-theoretic methods.
   The interpolation theorem for many-sorted languages, with the applica-
tion to the characterization of persistent sentences (4.4.13-4.4.16), is due to
Feferman [1968].
   A syntactic proof of the eliminability of symbols for definable functions is
already in Hilbert and Bernays [1934] (elimination of the t-operator). Cf.
also Schiitte [1951], Kleene [1952a]. For our standard logics there are very
easy semantical proofs of these results, using classical or Kripke models.

4.9.6. Generalizations with applications. Perhaps Ketonen [1944] may be
said to be an early analysis of cutfree proofs in Gentzen calculi with axioms;
but he considers the form of cutfree derivations in the pure calculus where
axioms are present in the antecedent of the sequents derived. Schate [1950b]
considers for his one-sided sequent calculus derivations enriched with sequents
of atomic formulas as axioms, and proves a generalized cut elimination the-
orem for such extensions. A proof for a context-free variant of the standard
Gentzen formalism LK is given in Sanchis [1971]. Schfitte and Sanchis require
the axioms to be closed under Cut; whereas Girard [1987b]) does not require
closure of the set of azdoms under Cut.
  The examples of this generalized cut elimination theorem are given as they
4.9. Notes                                                                    143

appear in Girard [1987b].
  The possibility of completely eliminating cuts for G3[mic] extended with
suitable rules was first noticed in Negri [1999] for the intuitionistic theory of
apartness, and is treated in greater generality in Negri and von Plato [1998].
Among the applications are predicate logic with equality, the intuitionistic
theory of apartness just mentioned, and the intuitionistic theory of partial
order.
  The paper Nagashima [1966] axiomatizes intuitionistic and classical logic
with equality by the addition of the two rules
         t = t, F   A       r       A(s)         A(t),F'
             FA                   s = t, r, F'     A, A'
to Gentzen's systems LJ and LK. Nagashima states cut elimination for these
extensions, and a corresponding subformula property: each formula in a cut-
free proof in one of these extensions is either a prime formula or a subformula
of a formula in the conclusion. From this he then derives the conservativity
of the extensions over pure predicate logic without equality. This result is
an essential ingredient of Nagashima's proof of the interpolation theorem for
languages with functions but without equality.
   The proof of this conservativity result presented in 4.7 is due to J. von Plato
and S. Negri.
   The characterization of the equality fragment of the predicate-logical theory
of apartness in 4.8 is due to van Dalen and Statman [1979]. They obtained
this result by normalization of an extension of natural deduction. The present
simpler proof occurred to us after studying Negri [1999].
   The latter paper also contains the interesting result that the propositional
theory of apartness is conservative over the theory of pure equality plus the
stability axiom (i.e.,      =s>t=s; Negri [1999] defines equality as the
negation of apartness, which automatically ensures stability).

4.9.7. Semantic tableaux. Semantic tableaux may be described as a par-
ticular style of presentation of a certain type of Gentzen calculus in fact,
Kleene's G3-calculi mentioned in 3.5.11. In the literature, the details of the
presentation vary.
  The motivation of semantic tableaux, however, is in the semantics, not in
the proof theory in the spirit of the semantic motivation for G3cp in 4.1.11.
They have been widely used in completeness proofs, especially for modal
logics. For classical logic, there is a detailed treatment in Smullyan [1968];
for intuitionistic and modal logics, see Fitting [1969,1983,1988].
  Let us describe a cumulative version of semantic tableaux for Cp, starting
from GK3c. Signs are symbols t, f, and we use s, s',                for arbitrary
signs. Signed formulas are expressions sA, A a formula. We encode a sequent
r    A, with r, A finite sets, as the set of signed formulas tr,
144                                Chapter 4. Cut elimination with applications

  If we turn the rules of GK3c upside down, then, for example, LA, RA take
the form (9 a set of signed formulas):
               e,t(A A B)                         O, f(A A B)
      t A                         fA
            e,t(A A B), tA,tB          e,f(A A B), fA I e,f(A A B), fB

where we have used 1, instead of spacing, to separate the possible "con-
clusions" (originally, in GK3c, premises). In this form the rules generate
downward growing trees, called semantic tableaux (cumulative version). A
tableau with tr, fA at the top node (root) is said to be a tableau for tr, fA.
The semantic reading of the rules is as follovvs (cf. the motivation for G3cp
above): tr, fA represents the problem of finding a valuation making r true
and A false; the problem represented by the premise of a rule application is
solved if one can solve the problem represented by one of the conclusions. A
node of the tableau is closed if it contains either t1 or tA,fA for some A.
So a closed node represents a valuation (satisfiability) problem solved in the
negative, and is in fact nothing but an axiom of the sequent calculus. We
assume that a tableau is not continued beyond a closed node.
  A branch of the tableau is a sequence of consecutive nodes starting at the
root, which either is infinite, or ends in a closed node. A subbranch is an
initial segment of a complete branch. A branch is said to be closed when
ending in a closed node; a tableau is closed if all its branches are closed.
  As an example we give a closed tableau forOmf(AVB-4BVA):
                                       O
                            0,t(A V B),f(B VA)
                        9,t(A V B),f(B V A), fB, fA
      0,t(A V B),f(B V A),fB,fAJA      I
                                           0,t(A V B),f(B V A),fB,fAJB

Obviously, a closed tableau is nothing but a GK3c-derivation, differently
presented. All formulas obtained at a given node are repeated over and over
again at lower nodes in this cumulative version of semantic tableaux; so, in
attempting to construct a tableau by hand, it is more efficient to use a non-
cumulative presentation, as in Beth's original presentation; see, for example,
Smullyan [1968].
   The use of signed formulas, due to R. M. Smullyan, is a convenient nota-
tional device which avoids the (in this setting) awkward distinction between
formulas to the left and to the right of      If we do not want to use signed
formulas, we can take the set r, -IA, corresponding to the sequent r,
instead of 0, fA.
  Another'useful device of Smullyan is the notion of a formula type. In the
tableaux, t(A A B), f(A V B), f(A         B) on the one hand, and f(A A B),
t(A V B), t(A -4 B) on the other hand, show the same type of behaviour.
Let us call formulas of the first group a-formulas, and of the second group 0-
formulas. To these formulas we assign components al, a2 and 03., /32 according
4.9. Notes                                                                      145

to the following tables:
                    ce            az                           01   /32
                t(A A B)  tA tB                 f (A A B)     fA fB
                f (A V B) fA fB                 t(A V B)      tA tB
               f (A    B) tA fB                 t(A        B) fA tB
The rules for the propositional operators may now be very concisely formu-
lated as
                             Fa                   ro
                           faceiaz             roilr,802
The idea of formula types may be extended to predicate logic, by introducing
two further types,
              type -y :   fVxA, t3xA and type          :   tVxA, fAxA.

If we adopt the convention that for -y, b as above, -y(t),b(t) stand for A[x It],
the tableau rules may be summarized by

                 F(t)
                    -y               1'88(y)
                                               ( y a new variable).

The simplification which is the result of the distinction of formula types may
be compared to the simplification obtained by using one-sided sequents in the
GS-calculi. Both devices use the symmetries of classical logic. However, the
distinction of formula types is still useful for intuitionistic logic, whereas there
is no intuitionistic counterpart to the GS-systems (cf. Fitting [1983, chapter
911.
  For intuitionistic logic, the semantic motivation underlying the tableaux is
the construction of suitable valuations in a Kripke model. In the remainder
of this subsection we assume familiarity with the notion of a Kripke model
for Ip.
  A top node tr, LA in a tableau now represents the problem of finding
a Kripke model such that at the root A r is valid and V A invalid. Now
cumulative rules such as tA, fA mentioned above correspond to (in standard
notation for Kripke models)
                 k II- A A B iff (k II- A and k B), and
                 kilL A A B iff (k IlL A or k IlL B)
respectively (the classical truth conditions at each node). However, for k
A -+ B we must have a k' > k with k' II- A, k' IF B. But if kJ C, there is
no guarantee that k' 1L C for k' > k: only formulas forced at k are "carried
over" to k'. Thus, to obtain a rule which reflects the semantic conditions for
k W A -4 B, we take
                                       e f(A-    B)
146                                  Chapter 4. Cut elimination with applications

with et := { tC : tC E 0}. Putting k        tA iff k II- A, k fA iff k IF A,
this rule may be read as: in order to force e,f(A       B) at k, we must find
another node k' > k, k' forcing et, fB, tA. So f--+ is not strictly cumulative
any more. Of course, if we interpret this rule as a rule of a Gentzen system,
we find
                                    F, A   B
                                F     A+ B,
exactly as in the calculi m-Gli in 3.2.1A and m-G3i in 3.5.11D, but for the
fact that r and r, A, etc. are interpreted as sets, not as multisets. Thus we
see that multiple-conclusion Gentzen systems for I appear naturally in the
context of semantic tableaux.
