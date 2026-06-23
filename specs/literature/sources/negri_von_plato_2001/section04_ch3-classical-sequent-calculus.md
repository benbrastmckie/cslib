# Structural Proof Theory — Chapter 3: Classical Propositional Sequent Calculus (lines 2600-3151)

3.1. A N INVERTIBLE CLASSICAL CALCULUS

We give the rules for a calculus G3cp of classical propositional logic and show
that they are all invertible. Then we describe a variant of the calculus with negation
as a primitive connective.
              SEQUENT CALCULUS FOR CLASSICAL LOGIC                                49

(a) The calculus G3cp: Sequents are of the form F =>• A, where F and A are
finite multisets and F and A can be empty. In contrast to the single succedent
calculus, it is possible to have sequents of the form F =>• and even =>>. One of the
admissible structural rules of the multisuccedent calculus will be right weakening,
from which it follows that if F =>• is derivable, then also F =>• JL is derivable.

                                             G3cp

   Logical axiom:
   P, F =• A , P
   Logical rules:

                                                                -R&
   At fc£,F      A^                                 =^ A, A&S
   A, F =*A DD , 1T • A                             A,A,5
       A v B, F =» A
                        1
   F =» A, A      B,T       _\
                            —r•   A          A,r
                                      7 ~)



               •LJ_
   -L,r

The logical rules display the perfect duality of left and right rules for conjunction
and disjunction, of which only the duality Lv-R& could be observed in the
intuitionistic calculus. Here there is only one right disjunction rule, and it is
invertible, and also the left implication rule is invertible, with no need to repeat
the principal formula in the left premiss, which has profound consequences for
the structure of derivations and for proof search.

Theorem 3.1.1: Height-preserving inversion. All rules of G3cp are invertible,
with height-preserving inversion.

Proof: For L&, LV, and the second premiss of LD, the proof goes through as
in Lemma 2.3.5, with A in place of C. We proceed from there with a proof by
induction on height of derivation:
   If the endsequent is A D B, F =>• A with A D B not principal, the last rule
has one or two premisses A D B, F' =>> A/ and A D B, F" =>> A", of deriva-
tion height < ft, so by inductive hypothesis, F r =>• A', A and F" =>• A", A have
derivations of height ^ n: Now apply the last rule to these premisses to conclude
F =>• A, A with height of derivation ^ n + 1.
   If A D B is principal in the last rule, the premiss F =>• A, A has a derivation
of height ^ n.
50                     STRUCTURAL PROOF THEORY

    We now prove invertibility of the right rules:
    If Y =>• A, A&B is an axiom or conclusion of L_L, then, A&B not being
atomic, also F =>• A, A and Y =$> A, B are axioms or conclusions of L J_. Assume
height-preserving inversion up to height n and let \-n+i Y =$> A, A&#. There are
two cases:
    If A&B is not principal in the last rule, it has one or two premisses,
F' =» A', A&B and Y" =» A", A&£, of derivation height ^ n, so by induc-
tive hypothesis, \-n Yf =» A', A and \-n Yf =^ A', 5 and h n r " =^ A", A and
hrt F" =>• A", B. Now apply the last rule to these premisses to conclude
F =>• A, A and F =>> A, B with a height of derivation ^ n + 1.
    If ASLB is principal in the last rule, the premisses Y =^ A, A and F =>• A, 5
have derivations of height ^ n.
    If F =>• A, A V 5 is an axiom or conclusion of L_L, then, Av B not being
atomic, also Y =>• A, A, 5 is an axiom or conclusion of L_L. Assume height-
preserving inversion up to height n and let \-n+\ Y ^ A, Av B. There are again
two cases:
    If Av B is not principal in the last rule, it has one or two premisses
  f
Y ^ A\Av B and F" =>• A", Av B, of derivation height ^ n, so by inductive
hypothesis, \-n F' =* A r , A, 5 and h n r ^ A ' U , ^ Now apply the last rule
to these premisses to conclude Y => A, A, B with a height of derivation ^ n + 1.
    If A v B is principal in the last rule, the premiss F =$> A, A, B has a derivation
of height ^ n.
    If F =>• A, A D 5 is an axiom or conclusion of L_L, then, A D B not being
atomic, also A, F =>• A, 5 is an axiom or conclusion of LJ_. Assume height-
preserving inversion up to height n and let h n + i F =>> A, A D 5 . As above, there
are two cases:
    If A D 5 is not principal in the last rule, it has one or two premisses Yf =>
A', A D B and F" =>• A", A D 5 , of derivation height ^ n, so by inductive
hypothesis, \-n A, Yf => Af, B and \-n A, F /r => A", B. Now apply the last
rule to these premisses to conclude A, F =>• A, 5 with a derivation of height
 ^ n + 1.
    If A D B is principal in the last rule, the premiss A, F =>• A, 5 has a derivation
of height^ n. QED.

   Given a sequent F =$ A, each step of a root-first proof search is a reduction
that removes a connective and it follows that proof search terminates. The leaves
are topsequents of form



where the number of _L's in the antecedent or succedent as well as m or n can
beO.
              SEQUENT CALCULUS FOR CLASSICAL LOGIC                               51

Lemma 3.1.2: The decomposition of a sequent F =>> A into topsequents in G3cp
is unique.

Proof: By noting that successive application of any two logical rules in G3cp
commutes. QED.

   Root-first proof search gives a method for finding a representation of formulas
of propositional logic in a certain normal form: Given a formula C, apply the
decomposition to =$> C, and after having reduced all connectives, remove those
topsequents that are axioms or conclusions of L_L, i.e., those that have the same
atom in the antecedent and succedent or _L in the antecedent.
Definition 3.1.3: A regular sequent is a sequent of the form P\,..., Pm =>•
Qi,..., Qn, _L,..., J_ where Pt ^ Qjy the antecedent is empty if m = 0, and
the succedent is ±ifn = 0. The trace formula of a regular sequent is

  1. P1Sc...&Pm D g i V . . . V Qn form,n        > 0,
  2. Qx V . . . V Qn for m = 0, n > 0,
  3. ~(Pl&...&Pm)form        >0,n = 0,
  4. _L for m, n = 0,

where possible repetitions of the P( or Qj in the regular sequent are deleted.

Regular sequents correspond to Gentzen's (1934-35) "basic mathematical se-
quents," except that Gentzen did not have _L as a primitive. The term "regular"
is explained in Chapter 6. Trace formulas of regular sequents are unique up to
the order in the disjunctions and conjunctions. By the invertibility of the rules of
G3cp, a regular sequent with trace formula C is derivable if and only if the se-
quent =>• C is derivable. It follows that a formula is equivalent to the conjunction
of its trace formulas:

Theorem 3.1.4: A formula C is equivalent to the conjunction of the trace for-
mulas of its decomposition into regular sequents.

Proof: Let the topsequents ofthe decomposition of =>• CbeFi =>> A i , . . . , Tm=$>
A m , with the n first giving the trace formulas C\,..., Cn and the rest, if m > n,
having _L in the antecedent or the same atom in the antecedent and succedent.
We have to show that = ^ C D C C i & . . . &Cn is derivable. We have a deriva-
tion of =>• C from Fi => A\,...,      Tm => Am that uses invertible rules. By adding
the formula C to the antecedent of each sequent in the derivation, we obtain a
derivation of C =» C from C, Fi => A i , . . . , C, F m =>• Am by the same invertible
rules. Therefore each step in each root-first path, from C =>• C to C, F/ =^ Ai9
is admissible. Since C =>• C is derivable, each C, F,- =» A, is derivable. It fol-
lows that, for each trace formula, up to n, the sequent C =^ Ct is derivable.
52                       STRUCTURAL PROOF THEORY

Therefore, by repeated application of R&, C =>• C\ & . . . ScCn is derivable, and by
R D, =» C D C i & . . . &Cn is derivable.
   Conversely, starting from the given derivation of =>• C from topsequents
Fi => A i , . . . , F m =>• A m , add the formulas C i , . . . , Cn to the antecedent of each
sequent in the derivation to obtain a derivation of C\,..., Cn =>• C from new
topsequents of the form C\,..., C n , F; =>• A/. For / > n, such sequents are ax-
ioms since they have _L in the antecedent or the same atom in the antecedent and
succedent. For / ^ n they are derivable since each C\,..., Cn =>• Ct is deriv-
able. Application of L& and RD to C\,..., Cn =>• C now gives a derivation of
=^ C 1 & . . . & G , D C. QED.

As a consequence of Lemma 3.1.2, the representation given by the theorem is
unique up to order in the conjunction and the conjunctions and disjunctions in the
trace formulas. Each trace formula P\SL . . . &Pm D Q\ v . . . v Qn is classically
equivalent to ~ P\ v . . . v ~ Pm V Qi v . . . v Qn\ the representation is in effect
a variant of the conjunctive normal form of formulas of classical propositional
logic.

(b) Negation as a primitive connective: In Gentzen's original classical sequent
calculus LK of 1934-35, negation was a primitive, with two rules that make a
negation appear on the left and the right part of the conclusion, respectively:
                          F =* A, A               A , F => A


Now negation displays the same elegant symmetry of left and right rules as the
other connectives. Some years later, Gentzen commented on this property of the
multisuccedent calculus as follows (1938, p. 25): "The special role of negation,
an annoying exception in the natural deduction calculus, has been completely
removed, in a way approaching magic. I should be permitted to express myself
thus since I was, when putting up the calculus LK for the first time, greatly
surprised that it had such a property."
   Gentzen's rules for negation, with the definition ~ A = A D _L, are admissible
in G3cp, the first one by

                              F => A, A


and the second one by




where RW is right weakening, to be proved admissible in the next section.
              SEQUENT CALCULUS FOR CLASSICAL LOGIC                                53


3.2. ADMISSIBILITY OF STRUCTURAL RULES

We shall prove admissibility of weakening, contraction, and cut for the calcu-
lus G3cp. There will be two weakening rules, a left one for weakening in the
antecedent and a right one for weakening in the succedent, and similarly for
contraction. The rules are as follows:

                          r ^A              , , ^                    ^ , ,
               -LW    —    —     -RW                    LC                 ;—RC

The proofs of admissibility of left and right weakening are similar to the proof of
height-preserving weakening for G3ip in Theorem 2.3.4:

Theorem 3.2.1: Height-preserving weakening. If \-n F =>> A, then \-n A, F =>•
A. / / \-n F =^ A, then hn F =^ A, A.

Proof: The addition of formula A to the antecedent and consequent, respectively,
of each sequent in the derivation of F =>> A will produce derivations of A, F =>• A
and F =^ A, A. QED.

It follows that if a sequent F =>• with an empty succedent is derivable, the sequent
F =>• J_ also is derivable.

Theorem 3.2.2: Height-preserving contraction. If \-n C, C, F =>• A, then
\-n C, r =» A. / / hn F =• A, C, C, */H?W h J ^ A ,       C.

Proof: The proof of admissibility of left and right contraction is done simultane-
ously by induction on height of derivation of the premiss. For n = 0, if the premiss
is an axiom or conclusion of L_L, the conclusion also is an axiom or conclusion of
L_L, whether contraction was applied on the left or right. For the inductive case,
assume height-preserving left and right contraction up to derivations of height n.
As in the proof of contraction for the single succedent calculus, Theorem 2.4.1,
we distinguish two cases: If the contraction formula is not principal in the last
rule applied, we apply the inductive hypothesis to the premisses and then the rule.
If the contraction formula is principal, we have six subcases according to the last
rule applied.
    If the last rule is L& or Lv, the proof proceeds as in Theorem 2.4.1. If the
last rule is R&, the premisses are \-n F =>• A, A&B, Aandh n F =>• A, A&B, B.
By height-preserving invertibility, we obtain \-n F => A, A, A and hn F =>
A, B, B, and the inductive hypothesis gives \-n F =>• A, A and \-n F =>> A, B. The
conclusion h n + i F =>• A, AScB follows by R8L. If the last rule is R V, the premiss
isl-^ F = ^ A , A v Z ? , A , i ? and we apply height-preserving invertibility to con-
clude \-n V ^ A, A, B, A, B, then the inductive hypothesis twice to obtain
\-n F =» A, A, B, and last flv.
54                       STRUCTURAL PROOF THEORY

   If the last rule is RD, the premiss is h n A, F =^ A, ADB, B and we apply
height-preserving invertibility to conclude h n A , A , F = ^ A , Z ? , Z ? , then the in-
ductive hypothesis to conclude \-n A, F =>> A , Z? and t h e n / O . If LD was applied,
we have the derivation of the premiss of contraction,

                    A P ff, F =j> A , A             B,ADB,F=>A
                                                                  LD
                             AD    B,AD     B,T => A
By height-preserving inversion, we have \-n F => A, A, A and h n 5 , 5 , F =>-
A. By the inductive hypothesis, we have \-n F =>> A, A and h n # , F =^ A, and
obtain a derivation of A D # , F =>• A in at most n + 1 steps. QED.
A proof by separate induction on left and right contraction will not go through if
the last rule is LD or RD.
Theorem 3.2.3: The rule of cut,
                                              l
                                                          Cut
                                       r
                                   r, r => A, A'
is admissible in G3cp.
Proof: The proof is organized as that of Theorem 2.4.3, with the same numbering
of cases.
Cut with an axiom or conclusion of L_L as premiss: If at least one of the
premisses of cut is an axiom, we distinguish two cases:
1. The left premiss F =>• A, D of cut is an axiom or conclusion of L_L. There
are three subcases:
1.1. The cut formula D is in F. In this case we derive F, F" =>> A, Af from the
right premiss D, Ff => A' by weakening.
1.2. F and A have a common atom. Then F, F' =>• A, A' is an axiom.
1.3. _L is a formula in F. Then F, F7 => A, A' is a conclusion of L_L.
2. The right premiss D, F r =>• A ; is an axiom or conclusion of L ± . There are
four subcases:
2.1. D is in A'. Then F, F ; =>• A, Ar follows from the first premiss by weakening.
2.2. Ff and A' have a common atom. Then F, F ; =>• A, Ar is an axiom.
2.5. _L is in F'. Then F, Vf =^ A, A' is a conclusion of L_L.
2.4. D = _L. Then either the first premiss is an axiom or conclusion of L_L and
F, Ff =>• A, Af follows as in case 1, or F =» A, _L has been derived. There are six
cases according to the rule used. These are transformed into derivations with cuts
              SEQUENT CALCULUS FOR CLASSICAL LOGIC                                                     55

of lesser cut-height. Since _L is never principal in a rule and the transformations
are special cases of transformations 3.1-3.6 below, with D = _L, they need not
be written out here.
Cut with neither premiss an axiom: We have three cases:

3. Cut formula D is not principal in the left premiss. We have six subcases
according to the rule used to derive the left premiss. For L& and Lv, the trans-
formations are analogous to those of cases 3.1 and 3.2 of Theorem 2.4.3. For
implication, we have
3.3. LD, with T = AD B, F". The derivation
              V" =» A,D,A           B,T"         =>    A,D
                    AD     B,T/f    ^       A,D              LD
                                                                              D,V'=>Af
                                                                                          Cut
                                   A D B,r", r'=» A, A'
is transformed into the derivation
      r"^> A,P,A          P , r = » A/                B, V" ^ A , P                  P , V => Af
             /f                                 Cut
           r , r^A,A\A                          Cut
                                                             B, r", r => A,                        C
                                            /;                        7
                             A D 5,r , r=> A, A
with two cuts of lower cut-height.
3.4. R&, with A = A&B, A". The derivation
              r ^ A\A,D             r=^ A", B,D
                                         p p                      ,           r =» A
                                            r
                                    r, r =^ A 7
is transformed into the derivation with two cuts of lower height
      r => A", A,D p , r = ^ A /     r ^ A \ B, D p,r ^ A'
          r, r r =^ A ;/ , A, Af Cut
                                         r, r r =» A", B, A' Cut

                              r, r => A",
3.5. Rv, with A = A V 5 , A". The derivation
                     r =» A /; , A , £ , P
                    r =» A/r, A V B,DRV                  D, r ^ Ar
                             r, r r =^ Ar/, A V 5 , A '                             Cut



is transformed into the derivation with a cut of lower cut-height:
                         r =^ A ; / , A,g, p           p , r ^ A/
                                        /
                               r, r ^ A",A,B,                 Ar              CM?

                                                                          f
                             r, r => A", A v B, A
56                      STRUCTURAL PROOF THEORY

3.6. RD, with A = AD B, A". The derivation
                       r , A =» A", B, D
                      r => A", AD B,DRD       D, T => Ar
                              r , V => A", AD B,Af
                                   f


is transformed into the derivation with a cut of lower cut-height:

                        r, A =» A", g, p p, r => Af
                               r, r, A => A", B
                            r,r => A",AD B,A'RD
4. Cut formula D is principal in the left premiss only, and the derivation is
transformed in one with a cut of lower cut-height according to derivation of the
right premiss. We have six subcases according to the rule used. Only the cases of
LD and Rv are significantly different from the cases of Theorem 2.4.3:
4.3. LD, with A = AD B, A'. The derivation and its transformation are similar
to those of previous case 3.3.
4.5. Rv, with A = A v B, A". The derivation
                                       D, T' => A,B, A
                                          ;           r, Rv
                       F =>• A , D    D , Ff =>• A V B, A "
                            T,Tr => A,AvB,A"              Cm


is transformed into the derivation with a cut of lower cut-height


                            r, r=> A,AV5,A / ;
5. Cut formula D is principal in both premisses, and we have three subcases,
of which conjunction is very similar to that of case 5.1 of Theorem 2.4.3.
5.2. D = A v B, and the derivation


                                                              -Cut
                              r,r=* A, A7
is transformed into

                                               Cut
                                                        s,r^Af
                               r,r, r=> A, A7, A;                    Cut
                                     :       ;   Ctr
                                     r, r =^ A, A
with two cuts of lower cut-height.
              SEQUENT CALCULUS FOR CLASSICAL LOGIC                                  57

5.5. D = A D B, and the derivation



                                                               Cut


is transformed into the derivation with two cuts of lower cut-heights:

                                                 Cut
                       r, r=»A,A', B              , »
                                                                     Cut
                              r,r, r =» A, A;, A/
                                 r, n=^A,A'
QED.
We obtain, just as for the calculus G3ip, the following subformula property.

 Corollary 3.2.4: Each formula in the derivation of F =>• A m G3cp w a sub-
formula ofT, A.

It follows in particular that the sequent =>> is not derivable. We concluded from
the admissibility of weakening that if F =>• is derivable, then also F =>• _L is
derivable. We now obtain the converse by applying cut to F =>• _L and ± =>•;
thus an empty succedent behaves like _L.
   In intuitionistic logic, all connectives are needed, but in classical logic, negation
and one of &, V, D can express the remaining two. How does the interdefinability
of connectives affect proof analysis? Gentzen says that one could replace some
rules by others in classical sequent calculus, but that if this were done, the cut
elimination theorem would not be provable anymore (1934-35, III. 2.1).
   If we consider, say, the D, J_ fragment of G3cp, the cut elimination theorem
remains valid. Conjunction and disjunction can be defined in terms of implication
and falsity; thus for any formula A there is a translated formula A* in the fragment
classically equivalent to it. Similarly, sequents F =>• A of G3cp have translations
F* =>• A* derivable in the fragment if and only if the original sequent is derivable
in G3cp. By the admissibility of cut, the derivation uses only the logical rules for
implication and falsity.
    Gentzen's statement about losing the cut elimination theorem is probably based
on considerations of the following kind: According to Hilbert's program, logic
and mathematics had to be represented as formal manipulations of concrete
signs. In propositional logic, the signs are the connectives, atomic formulas, and
parentheses. Once these are given, there is no question of defining one sign by
another. However, it is permitted to reduce or change the set of formal axioms
and rules by which the signs are manipulated. Thus one gets along in propo-
sitional logic with just one rule, modus ponens. The axioms for conjunction
58                        STRUCTURAL PROOF THEORY

and disjunction in Hilbert-style, in Section 2.5(b) above, could in classical logic
be replaced by the axioms (~ADB)DAvB,AvBD(^ADB)                                   and
~(AD ~B)DA&B, A&BD ~(AD ~J3). If these axioms are added to the
fragment of G3cp in the same way as in Section 2.5(b), as sequents with empty
antecedents, they can be put to use only by the rule of cut, and it is this phenomenon
that Gentzen seems to have had in mind.
   Later on Gentzen admitted, however, the possibility of "dispensing with the
sign D in the classical calculus LK by considering A D B as an abbreviation for
~ A v B; it is easy to prove that rules RD and LD can be replaced by the rules
for v and ~" (1934-35, III. 2.41).1

3.3. COMPLETENESS

The decomposability of formulas in G3cp can be turned into a proof of com-
pleteness of the calculus. For this purpose, we have to define the basic semantical
concepts of classical propositional logic:
Definition 3.3.1: A valuation is a function v from formulas ofpropositional logic
to the values 0, 1 assumed to be given for all atoms,
   v(P) = 0 or        v(P)=l,
and extended inductively to all formulas,
     v(±) = 0,
     V(ASLB) = min(v(A),
     v(A V B) = max(v(A),
     v(A D B) = max{\ - v(A),
Observe that, by definition of v, v(A D B) = 1 if and only if v(A) ^ v(B).
Valuations are extended to multisets F by taking conjunctions /\(T) and dis-
junctions \f(T) of formulas in F, with / \ ( ) = _L and \ / ( ) = T for the empty
multiset and by setting
     v A ( H = min(v(C)) for formulas C in F,
     v V(r) = max(v(C)) for formulas C in F.
Definition 3.3.2: A sequent F =>• A is refutable if there is a valuation v such that
v /\(T) > v\J(A). Sequent F =>• A is valid if it is not refutable.
It follows that F =5- A is valid if for all valuations v, v /\(T) ^ v \J(A). For
proving the soundness of G3cp, we need the following lemma about valuations:

          text has "NK" (also in the English translation) that is Gentzen's name for classical
natural deduction, but this must be a misprint since he expressly refers to rules of sequent
calculus.
              SEQUENT CALCULUS FOR CLASSICAL LOGIC                                59

Lemma 3.3.3: For a valuation v, min(v(A), v(B)) ^ v(C) if and only if
v(A)^v(B D C).
Proof: If v(A) = 0 the claim trivially holds. Else min(v(A), v(B)) = v(B); thus
min(v(A), u(B)) ^ u(C) if andonly if u(#Ku(C), if andonly if i;(£ D C) = 1,
i.e., v(A) ^ v(B D C). QED.
Corollary 3.3.4: min(v(A D B), v(A)) ^ v(B).
Proof: Immediate by Lemma 3.3.3. QED.

Theorem 3.3.5: Soundness. If a sequent V =>• A is derivable in G3cp, it is valid.

Proof: Assume that F => A is derivable. We prove by induction on height of
derivation that it is valid. If it is an axiom or conclusion of L_L, it is valid since
we always have i; /\(P, V)^v \/(A, P) and v /\(_L, T)^v V(A).
   If the last rule is L&, we have by inductive hypothesis for all valuations
v that u / \ ( A , f l , r ) ^ u \ / ( A ) , and v f\(A&B, T) ^v V(A) follows by
v /\(A&B, F) = v /\(A, B, T). The case for Rv is dual to this. For Lv, we have
v /\(A, V)^v V(A) and v y\(B, F) < u V(A). Then

   v /\(A V 5 , T ) = max(i; y\(A, F), v /\(B, F)) ^ i; V(A).
The case of R& is dual to this. If the last rule is LD, suppose
   v /\(r)^max(v V(A), v(A)) and min(v(B), v /\(T)) ^ u V( A ).
There are two cases: If i; V( A) = 1, then the conclusion is trivial. If v \f( A) = 0,
then v /\(F) ^ v(A) and min(v(B), v A(O) ^ 0- F r o m t h e former follows
   min(v(A D B), v /\(r))^min(min(v(A         D B), v(A)), v /\(T))
and therefore, by using Corollary 3.3.4, we obtain

   min(v(A D B), v /\(T))^min(v(B),        v /\(F)) ^ 0 .
If the last rule is RD, we have

   min(v(A), v /\(F))^max(v       V(A), v(B))
and there are two cases: If v V(A) = 1, then the conclusion is trivial. Otherwise
we have min(v(A), v /\(T)) ^ v(B): hence by Lemma 3.3.3, v /\(T) ^ v(A D B)
and a fortiori v /\(T) ^ max(v V(A), v(A D 5)). QED.
Theorem 3.3.6: Completeness, /f a sequent F =>• A w va//J, /r /.s1 derivable in
G3cp.
60                      STRUCTURAL PROOF THEORY

Proof: Apply root-first the rules of G3cp to the sequent F =^ A, obtaining
leaves that are either axioms, conclusions of L_L, or regular sequents. We prove
that if F => A is valid, then the set of regular sequents is empty, and therefore
F => A is derivable. Suppose that the set of regular sequents consists of Fi =>•
A i , . . . , Vn =$> A n , with n > 0, and let Ct be their corresponding trace formulas.
We have, by Theorem 3.1.4, ^ C X C i & . . . &Cn, where C is y\(F) D \/(A).
Since F =>• A is valid, by definition v(C) = 1 for every valuation v, and since
C => Ci&... &Cn, by soundness v(C)^v(Ci&...&Cn),                which gives v(Q) = 1
for each Ct and every valuation v. No Ct is _L, since no valuation validates it.
No Ct is ~ ( P i & . . . &Pm) since the valuation with v(Pj) = 1 for all j ^m does
not validate it. Finally no Q is Px&... &P m D g,- v . . . V Qr or Qt v . . . v Qr
since it is refuted by the valuation with v(Pj) = 1 for all j ^ m and v{Qk) = 0
f o r a l U ^ r . QED.
Decomposition into regular sequents gives a syntactic decision method for for-
mulas of classical propositional logic: A formula C is valid if and only if no
topsequent is a regular sequent.


NOTES TO CHAPTER 3

The logical rules of the calculus G3cp first appear in Ketonen (1944, p. 14), the
main results of whom were made known through the long review by Bernays (1945).
Negation is a primitive connective, derivations start with axioms of the form A =$> A,
and only cut is eliminated, the proof being similar to that of Gentzen. Invertibility is
proved by structural rules.
    Direct proofs of invertibility were given by Schiitte (1950) and Curry (1963). The
proofs of admissibility of structural rules we give follow the method of Dragalin, sim-
ilarly to the intuitionistic calculus. Normal form by means of decomposition through
invertible rules and the related completeness theorem are due to Ketonen (1944). He
seems to have found his calculus by making systematic the necessity that anyone
trying root-first proof search experiences, namely, that one has to repeat the contexts
of the conclusion in both premisses of two-premiss rules. In an earlier expository
paper, he gives an example of proof search and states that, because of invertibility
of the propositional rules, the making of derivations consists of purely mechanical
decomposition (1943, pp. 138-139).
    The idea of validity as a negative notion, as in Definition 3.3.2, was introduced in
Negri and von Plato (1998a).
                                         4

                                The Quantifiers




In this chapter, we give the language and rules for intuitionistic and classical
predicate logic. Proofs of admissibility of structural rules are extensions of the
previous proofs for the propositional calculi G3ip and G3cp. We then present
some basic consequences of cut elimination, such as the existence property and
the lack of prenex normal form in intuitionistic logic. The invertible rules for the
classical sequent calculus G3c are exploited to give a, possibly nonterminating,
procedure of proof search. This procedure, called construction of the reduction
tree for a given sequent, is the basis of Schtitte's method for proving completeness
of classical predicate logic. We give a completeness proof, using the reduction
tree, but define validity through valuations, as an extension of the definition of
validity of classical propositional logic in Section 3.3.


