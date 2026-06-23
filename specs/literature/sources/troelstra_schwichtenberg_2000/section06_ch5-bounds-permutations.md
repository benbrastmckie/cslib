# Basic Proof Theory — Chapter 5: Bounds and Permutations (lines 6869-8268)

Chapter 5

Bounds and permutations

This chapter is devoted to two topics: the rate of growth of deductions under
the process of cut elimination, and permutation of rules.
  It is not hard to show that there is a hyperexponential upper bound on
the rate of growth of the depth of deductions under cut elimination. For
propositional logic much better bounds are possible, using a clever strategy
for cut elimination. This contrasts with the situation for normalization in the
case of N-systems (chapter 6), where propositional logic is as bad as predicate
logic in this respect.
   In contrast to the case of normalization for N-systems, it is not easy to
extract direct computational content from the process of cut elimination for
G-systems, since as a rule the process is non-deterministic, that is to say the
final result is not a uniquely defined "value" . Recent proof-theoretical studies
concerning linear logic (9.3) lead to a more or less satisfactory analysis of the
computational content in cut elimination for C (and I); in these studies linear
logic serves to impose a "fine structure" on sequent deductions in classical
and linear logic (some references are in 9.6.5).
   We also show that in a GS-system for Cp with Cut there are sequences of
deduction with proofs linearly increasing in size, while the size of their cutfree
proofs has exponentially increasing lower bounds.
   These results indicate that the use of "indirect proof", i.e. deductions that
involve some form of Cut play an essential role in formalized versions of proofs
of theorems from mathematical practice, since otherwise the length of proofs
would readily become unmanageable.
   The second topic of this chapter is the permutation of rules. Permutation
of rules permits further standardization of cutfree deductions, and in par-
ticular one can establish with their help a (version of) Herbrand's theorem.
Permutation arguments also play a role in the theory of logic programming;
see 7.6.3.




                                       147
148                                                  Chapter 5. Bounds and permutations

5.1      Numerical bounds on cut elimination
In this section we refine the analysis of cut elimination by providing numerical
bounds. We analyze the cut elimination procedure according to the proof of
4.1.5. We recall the following corollary to that proof:

5.1.1. LEMMA. (Cut reduction lemma) Let D', D" be two deductions in
G3c + Cut, with cutrank < 'DI, and let D result by a cut:
                                     D'

                                          r
Then we can transform D into a deduction D* with lower cutrank such that
ID*1 < ly'l + D" I. A similar result holds for G3i + Cut, with ID*I <
2(I'D'I+17r1).


REMARKS. (i) Taking Glc,Gli instead of G3c, G3i, and using Gentzen's
method based on the Multicut rule, we can only give a cut reduction lemma
with an estimate in terms of logical depth H II. IIDII is defined as ID except
that applications of W and C do not increase the logical depth. We then find
for both Glc and G1i 117,11 < 2(I Mil I + I ID_ "II), although the proof has to
proceed by induction on ID'I + 17,"1. Let us illustrate the proof by the case
of a multicut on an implication which is principal in both premises. Let TY
be the deduction
                                              Do
                                     FA     B(A->B)mA
                                dr        (Aq3)m+1A
and let Dll be the deduction
                       vi                                     V2
            h di 1 r (A-4 B)          AA'          Id/_1: r (A-4B)n B      A'
                                 :            Br+1

In the case whete m,n > 0 we construct TYTYTY as in section 4.1.9. An
easy computation yields bounds on their logical depth of 2d+ 2d'                   2 in each
case, and then the final deduction has depth 2d + 2d':
           TY3                                TY4

1-2d+2&_2 rriA     BAA'        h2d-E2d1_2              AAA'                  TY5

           Hd+26/1-1 (17)2           B(As)2                        h2d-F2d1-2 rriB     AA'
5.1. Numerical bounds on cut elimination                                          149

etc.
   (ii) In the absence of the -4-rules, we can use the estimate I1D*Il < (11D/11+
117'1). We can also use this estimate in the case of G1c, if we split R+ into

                                             R-41

5.1.2. NOTATION. Let "hyp" be the hyperexponential function defined by
        hyp(x, 0, z) = z, hyp(x, Sy, z) = xhYP(''Y'z)
We abbreviate
        zik  hyp(2,k,i),      2k := hYP(2, lc, 1),
and similarly for 4,4k.

5.1.3. THEOREM. (Hyperexponential bounds on cut elimination) To each 7,
in G3[mic] + Cut of cutrank k there is a cutfree 7,* with the same conclusion,
obtained by eliminating cuts from 1), such that
         ID* < 2 1DI   (for G3c + Cut),     1D*I <4I (for G3[mi] + Cut).
PROOF. We show by induction on IDI that, whenever cr(D) > 0, then there
is a 1,* with cr(D*) < cr(D), ID*1 < 21D1 (for G3c) or ID*1 < 41v1 (for G3i).
   If T, does not end with a cut, or ends with a cut of rank less than cr(D),
we can apply the IH to the immediate subdeduction(s) of the premise(s), and
find (in the case of G3c)

         1V*1 = IVo + 1 <     21D01 +1 < 21vI (1-premise rule),

         1D*I = max(IT41,         + 1 < max(21v01, 211'11) + 1 <
                  21v01 + 21v11 < 2max(11)01,11)11)+1 = 212,1 (2-premise rule).

There remains the case where 7, ends with a cut on A, IAI +1 = cr(D). Then
we can apply the reduction lemma.

5.1.4. The inversion-rule strategy
It follows from known results (see, for example, the remark at the end of
6.11.1) that hyperexponential bounds are unavoidable in the case of predicate
logic, in the sense that no bounded iteration of exponentiation can provide
bounds for cut elimination.
   On the other hand, if we restrict attention to propositional logic, consider-
able improvements in the estimate are possible, by using a different strategy
for eliminating cuts. This points to an essential difference between normaliza-
tion for natural deduction and cut elimination by the inversion-rule strategy.
More about this in 6.9. Before explaining this strategy for the case of classical
implication logic, we first give a definition:
150                                                  Chapter 5. Bounds and permutations

DEFINITION. The cutlength c1(D) of a deduction D is the maximum value of

         E{s(A) : A occurrence of cutformula in o-}

taken over all branches o- of the prooftree.
  The strategy works as follows. We first show how to replace a deduction
ending with a single cut on A (i.e. the deductions of the premises of the
cut are cutfree) by a deduction of the same sequent, such that the cutlength
decreases, i.e the cutlength of the new deductjon is less than s(A).
   If the deduction ends with a cut on a prime formula, we use essentially the
same transformations as in Gentzen's procedure; and if the cutformula is not
atomic, we use inversion lemmas which permit us to replace the cut by cuts
of lower rank. The Cut rule we use is context-sharing (for the reason behind
this choice, see the remarks in the next section).
   Then we define a transformation "Red" on arbitrary deductions by recur-
sion on the construction of the deduction; this operator removes all uppermost
cuts, i.e. all cuts without cuts above them.

NOTATION. Let us write D Hdn F                 A if D proves F      A with depth < n,
cutlength < d.             r     A if such a D exists.

5.1.5.   The rules of >G3c plus context-sharing Cut can be stated as

              r, P         P,        for P atomic, all d and m

            1-`71,2 F, A        B,            F-FA, A          1-'4, r,B   A
                   r       A > B, A                     F, A -4 B      A

In addition we have Cut:

         1-1,2 r       A, A               r, A   A
                       Ld+deg(A) r        A
                       1-m+1

As already noted, the Cut rule is context-sharing. The reason for this is that
with ordinary Cut, the transformations of deductions of I'     A used yield
deductions of sequents         A' where contraction would be needed to get
r A back; and we have depth-preserving closure under contraction for
deductions without Cut, but not when ordinary context-free Cut is present.
By the use of Cute, the need for contraction is avoided (moreover, depth-
preserving contraction is derivable for the system with Cut).
We need the following results:
5.1. Numerical bounds on cut elirnination                                                             151

5.1.6. LEMMA. (Weakening, Contraction, Inversion lemma for --+G3c)
      Iff-1            A then1-1 F, A
      if F1,                  AL'A' then                         AA';
      if 1-1     ,   A --+ B             then 1-1, F =- A, A, F-cn) F,B            A;
      if 1-1 r         A*B,,6, then Pr), r,A                     B, A.
PROOF. This has been established before.

5.1.7. LEMMA. (Cut elimination lemma for --+G3c)
      If       r          P, A and1-1 F,P =- A then1-4., F                        A;

                       A-+ B,A and F-;,' I', A --+ B                      then F-sn(+ts(B) r     A.

PROOF. (i) Let two cutfree deductions
                                         D'
                                   FP,L                          r,P
be given. We prove (i) by induction on n + m.
Basis. n + m = O. V', V" are axioms. If P is not principal in either D' or
V", then also r A is an wdom, so         r A. If P is principal in TY and
D", then r r',P and PP PA, and D" becomes r'PP A. One of the
occurrences of P in D" is not principal, so rip A is also an axiom, hence
again F-8            A.
Induction step. If n +m = k +1, then at least one of D', V" is not an axiom,
say D'. If D' ends with L-4, then r          A-B, and we have deductions
Do F-t_i I"      APA, D1 h1 riB PA; by the inversion lemma, we also
have deductions D2 I-1,       AA, D3 hs, r'PB        A. Combining Do with
D2, D1 with D3, the IH yields               AA,                  A; with L->
it follows that 1-4,7i PA-4B    A. The case where D' ends with R-4 is even
simpler.
  As to (ii), let D'                              A-4B,      and D"     r, A->/3            A. By the
inversion lemma there are Do                         1", A      B, z, D1     r             A, A, D2
r,B A; then
                               Do

            CUtcs         n
                              rA       BA            r       ABA
                                                    BA
                                                                 r
                                    Hsrz(-EA1 r
                                                                         h?'173        A Cutes
                                                     s(A)+s(B)           A

where DI is obtained by weakening all sequents in D1 on the right with B
(weakening lemma).
152                                              Chapter 5. Bounds and permutations

5.1.8. THEOREM. (Numerical bounds on cut elimination, classical case)
       In --*Gl3c + Cut, if F-47., F      A, then P24Fi r     A;
       for each V in +G3c + Cut there is a cutfree I,* with the same
       conclusion, obtained by eliminating cuts from D, such that
                ID*I        + 1)2c1(D);

       for each V in G.3c + Cut there is a cutfree D* with the same
       conclusion, obtained by eliminating cuts from D, such that
                IV* 1   (11,1+ 1)2P1+1)2cr(D).

PROOF. (i) We define a transformation Red on deductions 7, as follows.
    V is an axiom: Red(D) := D.
        V is obtained from cutfree Do, D1 by a cut. By the cut elimination
lemma we construct a new deduction Red(D) with cl(Red(D)) < cl(D). Also
IRed(D)I < 2IDI + 1 which may be seen by inspection (n + 2 < n + (n + 1)
since n > 0).
        7, is obtained from other deductions Do, or from Do, D1, by a logical
rule or a cut which is not a top cut. Then Red(D) is obtained by applying
the same rule to Red(D0), or to Red(D0), Red(DO
   (ii) follows from (i) by iteration. As to (iii), let D r A. Then cl(D)
< p(n +1) where pis the maximum size of cutformulas in D; p < 2(V), hence

         cl(D) < 2"(v)(IDI + 1).

5.1.9. The inversion-rule strategy for intuitionistic implication logic
In principle, the same strategy works for intuitionistic --+GICi + Cut, but
we now have much more work to do since we do not have such strong inversion
properties as in the classical case.

5.1.10. DEFINITION. Let the weight w(A) of a formula A be defined as in
4.3.2. We define the cutweight cw(D) of a deduction D as the maximum of
         E{w(A): A occurrence of cutformula in o-},
o- ranging over the branches of D.
The notion of weight has the property
         w(A    B) + w(B > C) < w((A B) C)
since, if a = w(A), b = w(B), c = w(C), we have 1+ab+1+bc = 2 + (a + c)b
< 2 + abc (since a, b, c > 2) < 1 + c + abc = 1+ (1 + ab)c. Moreover we recall
that
         w(A) < 2'(A) <2211.
5.1. Numerical bounds on cut elimination                                                          153

5.1.11. DEFINITION. We define Hmd r                      A, "r          A is derivable with depth
at most m and cutweight at most d" as follows:

     F- r,pp for P atomic, all d and m

          F- (4, F , A      B             1-`,1nr, A >         A               A --+ B, B         C
      F-ln+,             A>B                                    F, A       B    C


      F-crin r     A            prin r, A     B
                 i_d-Fw(A)
                 nm+1                B
Note that the Cut rule is context-sharing (as in the classical case), and that
moreover we have chosen a variant of L-+ where the principal formula A      B
occurs in the antecedent of both premises (cf. 3.5.11). The reason for the
choice of context-sharing Cut is the same as for the classical case. On the
other hand, we might have used the ordinary L-4 for G3i, but then we
must prove a slightly stronger form of depth-preserving contraction, namely
that depth-preserving contraction is also derivable in the presence of context-
sharing Cut.

5.1.12. LEMMA. (Weakening, Contraction and Inversion for -4G.Ki)

     HE-% r              A, then I--? r,          A;

                 r, A, A        B, then 1-1 l', A        B.

     If                         B, then F-°r,A           B;

     If h% r, A -4 B                C, then I--? r, B         C.

     .1f1-1 r, (A -4 B)               C      D, then          r, A, B      C    D.

PROOF. We use induction on m. Proofs of the first four statements have been
given before (see the end of 3.5.11). As to the last statement, let us consider
two typical cases. Assume (A --F B) --> C to be principal in the final step of
the deduction of 1--% r, (A -4 B)   C D. Then

       r, (A -4 B) -4 C                 A -4 B
                                               Inv
   1--?i I', A, (A-4B)              C      B
             r, A,A,B>CB IH
                 r, A,B>CB                   Leb1               r, (A > B)
                                                                   r, A, B --> C, C
                                                                                    C,C
                                                                                          D
                                                                                              D

                                                                                              L-4
154                                                     Chapter 5. Bounds and permutations

In this "pseudo-prooftree" the dashed lines indicate transformations of de-
ductions given by the lemmas on weakening ("LW"), contraction ("LC") and
inversion ("Inv") as well as the IH.
   If (A     B)     C is not principal, 1-m° r, (A -+ B)    C      D follows
from a one-premise rule or a two-premise rule with (A        B)     C in the
context. We consider the case of the one-premise rule; the case of the two-
premise rule is similar. So let hm° r, (A   B) --+ C     D be obtained from
H1 I'', (A --+ B)     D'. Then
                                   F', (A       B)-+C         D'
                                                                   IH
                              F-?, I'', A, B CD'

5.1.13. LEMMA. (Cut elimination lemma for -+GKi+ Cutcs)
      If F--(n) r   P and F-          P     B, then           r         B.

                    P     B                     --+ B =C, andm <n, then          Pa r
      C.

      If1-1,P=P-->B andl-,?ir,BC and F-,9 r,P--+B=P andm< n
      thenl-Z2+1 r            C.
      If  r             (A > B) --+ C and F-    (A > B) > C                       D, then
      F+m+2 r            D with d = w(A > B)+ w(B --+ C).
PROOF. (i) is proved as before.
  (ii) and (iii) are proved simultaneously by induction on m. The case where
m = 0 we leave to the reader.
Induction step for (ii): Assume F-y,-> B, 7 )I--°mF,P                B    C.
Let us first assume that P   B is principal in the last rule of D. Then we
argue as represented schematically below (first step on the left by (iv) of the
preceding lemma):



                                      F-(71 r       P     B                  B
                                                                                  PIH(iii)
                                                r
If D ends with an application of R-+, say
                                          r, A, P --> B       A'
                               F-1)                           A'

where C in the statement of (ii) is A > A', then
5.1. Numerical bounds on cut elimination                                                                             155


                                                         LW
                                A          P        B                   F, A, P --+ B        A'
                                                                                                  IH(ii)
                                                    w(B)
                                                   F-n+m-1 FA            A'
                                                                               R-+
                                                   F-wn4), F       A     A'

Finally, let FIT,F, P -+ B C follow by L-4, with principal formula A --+ A'
distinct from P -+ B, so F F', A -+ A'. Then

                                F          P-4B
                                                         LW
                      F-cn'   F, A'            P-il3                     r, A' ,P-4B         C
                                                                                                  IH(h)
                                                   1-wP)-1
                                                    n+m    r A'            C

and
                                       r        P-43                   F, P-/3       A
                                                                                         IH(ii)
                                                       i_vv(B)    p    A
                                                         n+m -1

and the conclusions may be combined by

                                                   r         A    i-wnj:2-1 r, A'    C
                                                                                         L-4
                                                         F-,v4 r       c
Induction step for (iii): Suppose I-I., r               P          F, B   C and D
r,P --+ B                     P, m < n. Suppose P > B to have been principal in the last
rule of 7,, then

               Ejni   r                                r, B       c                      B        P
                                                                                                      IH(iii)



From this obviously I-V1 r        C. Now let the final rule of D be L> with
principal formula A --> A' distinct from P --+ B and let F r', A>A1. Then

      F-(7.1          P         B                           B    C
                                       LW
         r, A'            P        B               I-1 I', A', B  C                                        P
                                                                                                                IH(iii)
                                                       F-71 r, A'       C

and

                               F-(n)   r       p         B                     >B    A
                                                                                          MOO
                                                       F-w(B)     r    A
156                                                            Chapter 5. Bounds and permutations

from which                 r        A. Combining these with a final L-4 yield

                                              F-w(B)
                                                n+m -1-1   r    c.

Induction step for (iv). Assume I--,?. r  (A -+ B) -4 C, 1, F-om r, (A --*
B) -4 C D. The proof again proceeds by induction on m. We consider
only the inductive subcase where (A --* B) -* C is principal in the last rule
of D. Then
                                                     1-t_i f, (A -+ B) --* C   A --* B
      1-?, 1-'    (A --* B) -4 C                      I-?n_i f, A, (A > B) -+ C    B Inv
         1--?,,r,A-413       C Inv                         1---1 r, A, A,B>CB          'Mr
                               Inv
            1-,?,, P, B   C                                Im?_]. I', A, B --* C    B LC
          F-0
           n+1 rB->C
                               R--
                                                   F-1 r,B > C                 A   >BR-4
                                                                                     Cut
                                    max(n+2,m+1) r
                                hw(B-4c)
                                                     A>B

and

                                                       1-1 P, (A         B) > C      D
          Flir          (A > B) -4 C                            1--?n_i f, C   D
                                              111v
                 I--?, I', A -- B       C                  1-';'1',A--.13,C         DLW
                                    L..w(C)
                                                                                     Cut
                                    ' max(n+1,m) r7A--3.D

which then may be combined by a final application of Cut with result
                     hnd+m+2 r           D, where d = w(A-4B)-I-w(B-4C).                       N


5.1.13A. 06 Supply proofs for the missing cases in proof of the preceding lemma.


5.1.13B. * Check where changes in the axgument are needed if we replace L-+
of ->GKi by standard L-> of G3i.

5.1.13C. ** Let us write F-2, r t: A, where r is a sequence of typed variables
xi: Ai, ... , xn: An, if there is a deduction D in GKi with I'DI < n, such that under
the obvious standard assignment (cf. 3.3.4) of natural deduction terms to proofs in
GKi, D gets assigned t: A. Show the following
      If F-g r, x: A, y: A    t: B, then I-1 I', x: A t[x,y1x,x]: B.
       If hg r t: A B, then t a- AxA.t' and Fi r, x: A * t': B.
        If I-?., r, u: (A->B)->C * t: D, then there is a t' ../3 t[ul AxA--0 3 .zB4c(xyA)]
such that 1-s, r, y: A, z: B-W t': D.
5.2. Size and cut elimination                                                157

5.1.14. THEOREM. For deductions in --*G3i + Cut as described, we have
      If f-1+1 F =- A then Fin+, F =- A;
      for all D there is a cutfree V* with the same conclusion, obtained by
      eliminating cuts, such that

                1D*1 <          + 1)2ew(1)).

      For all D there is a cutfree D* with the same conclusion, obtained by
      eliminating cuts, such that

                1D*1     (1D1     1)2(11)1+1)22cr(D)


PROOF. It suffices to prove the theorem for               This is because deduc-
tions in          plus context-sharing Cut are easily transformed by dp-closure
under weakening into deductions in GKi plus Cut, preserving depth and the
measure for cuts. On cutfree deductions of the variant we can apply an inverse
transformation with the help of dp-admissible weakening and contraction.
   (i), (ii) are proved as in the classical case: we define an operator Red on
deductions 1, which removes all top cuts from D in such a way that the
cutweight (instead of the cutlength, as in the classical case) is reduced. The
crucial case is the treatment of a top cut; for this we use the cut elimination
lemma, (i), (ii) and (iv).
  As to the proof of (iii),

         IV* < 2cw(D) (ID I + 1) < 2m(ID)I+1) (IV I + 1),

where m is the maximum weight of cutformulas in D, say m = w(A). We
observe that w(A) < 2s(A) < 22`r1v1                                            N


5.2      Size and cut elimination
In this section we present an example of an infinite sequence (Sn),, of sequents,
with deductions in GS3p + Cut of size linear in n, while any cutfree proof
of     in GS3p has size > 2". In fact, the result will be slightly stronger than
just stated, since we shall consider a version of GS3p with the logical wdom
generalized to principal formulas of arbitrary logical complexity:

        F, A,

We call this version GS3p*.
  The result will entail a corresponding result for G3p[mi], also with the ax-
ioms generalized. As an auxiliary system we shall use the following "strictly
158                                              Chapter 5. Bounds and permutations

increasing" system G for classical propositional logic (which combines fea-
tures of GK- and GS-formalisms):

            Ax F, A,

                 FA         AV B       RAr'A A B, A   F,AAB,B
            RV         B'
                    FAV B                         F,AAB

In what follows we use the notations Is<n, HsS<n which have been introduced
in 3.4.3. The following lemma is easily established, and its proof left as an
exercise.


5.2.1. LEMMA. If GS3p* F-s<n r then G Hs<n F.


5.2.2. DEFINITION. We define a sequent Sn for each positive n as follows:

            Sn := Tn) Fn+17 62 n+17

where

                 := A1 A         ,A+1 A B+1;
            F0 := (P V             Fn+1 := (Fn A (Fn+1 V Qn+i));
            An+1 := Fn A 113n+1,       Bn+1 := Fn A 'Qn-0.

For use later on we also define the following abbreviations for i < n:
            Tn,i := Al A Bi,       ,     A Bi], Ai+1 A Bi+i,   , An+1 A Bn+1,
            So := Tn,i,          n+1, Qn+1

It is not hard to see that Sn must be valid for all n: note that Sn+i is equivalent
to ,(A1 A BO A ... A ,(An+1 A Bn+1)         Pn+1 V Qn+i, and that --i(A1 A BO is
equivalent to P1VQ1, ,(AiABi) is equivalent to Ai<k<i(PivQi) --+ Pi+1VQi+1
The validity follows more formally from the arguments below.
   To simplify the proofs of the next few lemmas, we observe that if we can
produce a derivation using instead of RA the more general rule

            r, I'', A      I", r", B
                F, ri,r", A A B

which generalizes both the context-sharing and the context-free versions o
RA, there is a derivation of the same size in GS3p*: simply use the closure
under weakening to transform a proof using the hybrid rule into a proof using
only the context-sharing RA.
5.2. Size and cut elimination                                                  159

5.2.3. LEMMA. In GS3p* there are a cutfree deduction Dk of size 7 of
              Ak+1 A Bk+i, Plc+1)Q1c+1,

and a cutfree deduction £k of size 10 of
        ---Fk, Ak+i A Bk+1, Fk+1.

PROOF. We take for Dk
               Fk      -1Fk, Pk+17           -1Fk, Fk    1-Fkl(2k-1-1)-7Qk+1
                        Ak+11 Pk+1                  1Fk, Bk+1,Q1c+1
                                   Ak+i A Bk+17 Pk-1-1,Qk+1
and for £k we take
                                                  plc
                                         Ak+1 A Bk+1, Pk+1,Q1c+1
                                   -1F,,, Ak+i A B,,+1, Plc+1 V CA-F1
                                       Ak+1 A Bk+1, Fk+1

5.2.4. PROPOSITION. Sn has a deduction in GS3p* + Cut of size lln +10.
PROOF. We first construct a deduction .7; (with cuts) of size lln + 2 of
        Ai A B1, .       , An A Bn, Fn

We use induction on n. The basis case for n =

                                             Fo
has size 2, and once .Fn of size lln + 2 has been obtained, we find .T92+3. as
                          Fn
           Ai A Bi,        ,   An A Bn, Fn         An+1 A Bn+i, Fn+1
                  A1 A
                                                                     Cut
                                   , An A Bn, An+i A Bn+i, Fn+1
which then has size lln + 2 + 10 + 1 = 11(n + 1) + 2. Now take for the
deduction of Sn
                         Fn                               Dn
          Fn, A1 A B1,          , An A Bn    -7Pn, An+i A B+1, Pn+i, Qn-Fi
                                             Sn
with size lln + 2 + 7 + 1 = lln + 10.

5.2.5. DEFINITION. A cutfree deduction D in G is called strict, if along any
branch of 7, no formula is introduced more than once.
In the remainder of this section until the final theorem we consider only
cutfree proofs in G.
160                                        Chapter 5. Bounds and permutations

5.2.6. LEMMA. If D is a [strict] cutfree derivation of I', A, A with s(D) < n,
there is also a [strict] cutfree derivation D' of I', A with s(D') < n.
PROOF. Straightforward by induction on the size of D; since the conclusion
in the rules of G is always contained in the premise(s), we can delete an
occurrence of A throughout the deduction; strictness is not affected by this
operation.

5.2.7. LEMMA. (Inversion in G) Let DI-s<7, I', A, and A not be principal in
an axiom, then
      if A BAC then there are deductions D' 1-s<r, , A and D"         r, B,
       if A BVC then there is a deduction D' 1-5<7,F, A, B.
Strictness is preserved in the construction of V', V" from D.
PROOF. Assume D hs<7, r, A A B, where A A B is not principal in axioms of
D. We use induction on the size of D. If D is an axiom, AA B is not principal,
so I', A and I', B are again axioms. If the last rule in D introduces A AB, D
has immediate subdeductions DA, DB deriving r, A A B, A and I', A A B, B
respectively.
   Apply the induction hypothesis to DA, this yields a proof of r, A, A; then
appeal to closure under contraction, etc.
   If D ends with another rule, not introducing A A B, we apply the induction
hypothesis to the immediate subderivation(s).
   Case (ii) of the lemma is proved similarly.

5.2.8. LEMMA. HD Fr, I', there is a strict D' such that D' 1--s<r,
PROOF. We show how to reduce the number of violations of strictness in D.
If D is not strict, there are a formula A and a branch a in D such that A is
introduced at least twice along u. Let us consider the two lowest introductions
a and f3 of A in u, and assume A BAC (the case A E BVC is similar
but simpler). If a passes through the left premise of the lowest introduction
of a (the case of the right premise is symmetric), D has the form
                  D2                 e2
                B A C, B , B F2, B A C, B C
                       F2, B A C, B
                            D1                           C1
                       Fi,BAC,B                    ri,B c,c
                                      rl,B c
                                          pc,

with a passing through r2, B A C, B and r1, B A C, B, and no introductions
of B A C along a in D1 and Do. By closure under contraction we find from
5.2. Size and cut elimination                                              161

7,2 a A such that
        TY2 F-s<s(D2) F2, B A C, B.

Now replace the subdeduction with conclusion 1'2, B A C,B in D by A.
The resulting proof has fewer violations of strictness and is smaller than D.
Repeating this we finally arrive at a strict proof TY with s(D') < s(D).    E

5.2.9. DEFINITION. If a formula A is not principal in the axioms of a
deduction D, and A is nowhere introduced in D, we say that A is passive. E
The following lemma is immediate.

LEMMA. If D 1,< F, A with A passive in 7,, then D[A]s- s<n r, where
D[A] is the deduction obtained by deleting one occurrence of A from all
sequents in D.
  If a strict D ends with an introduction of A, and A is not principal in any
axiom of D, then A is passive in the immediate subdeductions of D.

5.2.10. LEMMA. In any deduction of Sn, Sn,, the formulas Ak A Bky Aky Pk,
Fk, Pk V Qk cannot occur as principal formula in an axiom.
PROOF. Each of the subformulas listed has only positive occurrences in the
sequent Si,, Sn, which means that everywhere in the deduction they can only
occur positively.                                                         N


5.2.11. LEMMA. Let 1 < i < n. If hs<n Sn+Li then 1s<n Sn
PROOF. The rules and axioms in a cutfree deduction of Sn+i,i can use only
subformulas of Sn+Li. On multisets of subformulas of 5n+1,i we define, for a
fixed i, 1 < i < n + 1, a mapping * which is essentially nothing else but the
erasing of Pi,      Qi everywhere. For the empty multiset A we put
        A* := A,

and for the singleton-multisets, which we identify with formulas, we put
        L* := A if L E {Pi, Qi,        L*       L for other literals L;
        (Pi V Qi)* := A, * is the identity on other disjunctions,
            := Fk for k <i, Fi* := Fi-i, Fr:+1 := PI A (Pk V Qk) for k >
            :=      A Pk, B; := Fi*,`_]. A --1(2k (k i);
        (Ak A Bk)* :=     A BZ (k      i).

Finally, for multisets of arbitrary size we put

        (r, AY := r*, A*.
162                                             Chapter 5. Bounds and permutations

Assume A to be a strict cutfree deduction such that 1,        S,i. We trans-
form 1, into a deduction D*; we do this by defining * on subdeductions of V,
using recursion on the depth of D.
      Any subdeduction with one or more of Pi, Qi,      Pi V Qi in the conclu-
sion is mapped under * to the empty deduction. Observe that introductions
of Pi V Qi, and axioms with Pi, 43, as principal formulas can occur in 1, only
above introductions of F, hence they will be discarded.
       Axioms F not having Pi or Qi as principal formula are translated into
axioms F*.
       Subdeductions of the form

                                   7,2
                             A,F,PvQi are replaced by D[F*]1
                                                                    *
                Fi, Fi_i
                           A, Fi

Note that the whole subdeduction on the right is deleted by the process, in
keeping with the fact that such subdeductions are mapped to the empty de-
duction. In D1 the formula Fi is passive, since D1 is part of a strict deduction
and F., cannot be principal in an axiom (5.2.9). This property is preserved
under *.
  (iv) In all other cases


                                   is translated as

and

                               A/ is translated as pi*
                               A                   A*

The resulting structure is a correct deduction, since axioms, when not dis-
carded, are translated into axioms, and applications of rules are translated
into correct applications of rules. We end up with a deduction of

   A1 A B1, .   , Ai_i A Bii, AL-1 A B:+i,      . .   , An*+2 A Bn* +2, '13n+2, Qn+2.

By renaming propositional variables Pk+i      Pk, Qk+11-4 Qk (k > i), leaving
the rest invariant, we obtain a deduction of size < n of Sn+1.

5.2.12. PROPOSITION. If D is a cutfree derivation of Sn, then s(D) > 271+1
for all n > O.
PROOF. Since So       A1 AB1, P1, Qi is not an axiom, any proof of this sequent
must have size > 2.
5.2. Size and cut elirnination                                                 163

  Assume now the statement of the theorem to have been proved for Sn. Let
To be a strict cutfree proof of 5n+1, i.e. of

        A1 A            , An+2 A Bn+21Pn+2) Qn+2.

  must necessarily end with the introduction of Ai A B, for some i. We
distinguish two cases.
Case I. 1, ends with the introduction of An+2 A Bn+2, so there are D A,D B
such that
        VA 1-s<rn Yn, An+27Pn+2762n-1-2, DB Hs<rn, Tn, Bn+2, Pn+2 Qn+2,
                                                                    7



        s(D)     m      m' +1.
In DA the formula An+2 cannot be principal in an axiom (lemma 5.2.10) hence
by lemma 5.2.7

        Hm Tn, F+1, Pn+2, Qn+2,

        n+2, Qn+2 do occur only once in this sequent, they cannot be principal
Since P+2,
in axioms, hence F-s<rn Tn Fn+i i.e. hs<m Tn, Fn A (Pn+1 V Qn+i); since Fn
and Pn+i V Qn±i cannot be principal in axioms, we find, again by lemma
5.2.7, that there must be a deduction showing Hs<rn Tn, Pn+17Qn+1. Since
Ta, Pn+i, Qn+A. is Sn, we find by induction hypothesis 2n+1 < m, and similarly
we find 2n+1 < MI, so s(D) > 2n+2.
Case 2. 7, ends with the introduction of Ai A Bi, i < n. Then there are
DA,DB such that

        VA Hs<m Tn+1,i) Ai) Pn+2, Qn+2,     DB hs<mi Tn+1,i, Bi, Pn+2, Qn+2,
        s(D)     m + rn' + 1.
Since Ai cannot be principal in an axiom, we find by lemma 5.2.7

        H s<m Tn+1,i,       Pn+2,Qn+2) i.e., hs<rn 8n+1,i

With an appeal to lemma 5.2.11, we see that hs<rn S,, hence 2n+1 < m.
Similarly 2n+' < m' by consideration of DB, hence-again s(1,) > 2n+2.

5.2.13. THEOREM. In GS3p* + Cut there is a sequence (Sn)n with de-
ductions Dn of s(V) linear in n, while any proof of Sn in GS3p* has size
  2n; a corresponding result holds for G3[mi]*, i.e. G3[mi] with the axiom
generalized to A   A for arbitrary A.
PROOF. The statement for the classical system is immediate form what has
been proved before. To prove the statement for the intuitionistic systems,
we use a lemma. Let Ac be the standard translation of A into negation-
normal form, that is to say, we first replace subformulas B    C by    VC
and then push negations inward until they appear in front of prime formulas
164                                          Chapter 5. Bounds and permutations

only; finally we delete occurrences of   For sequents we put (F       Ay :=
       Ac. Then one easily checks by induction on size of deductions that if

(*)         G3m I-5<n F       A then GS3p* Hs<7, (r    A)c.

Now we define

                       Pn+i V Qn+1,

where
               :=    V B1,1     Al1 V B:,+1;
            Fo :=        P), Fn+1 := (Fn A (Pn+i V Qn+i));
            A'n+1 := F --+ Pn+1, B41 := Fn + n+1.

Noting that (S,)c      Sn, we see that the result follows from (*) and the result
for the classical system.

5.2.13A. 4 Prove lemma 5.2.1.

5.2.13B. 4 The deductions in 5.2.4 are easily transformed into deductions in
GS3p (with axioms with atomic principal formulas only). Determine the size of
the deductions of Sn in GS3p.

5.2.13C. 4 Describe cutfree proofs Dn for S, (as defined in 5.2.13) in G3m*
such that the depth of Dn is linearly bounded in n.


5.3         Permutation of rules for classical logic
S. C. Kleene has analyzed in detail for the calculi Glc and Gli when two
successively applied rules of the sequent calculus may be reversed in the order
of their application. A similar analysis applies to GS1. In this section we
want to give the analysis for GS1 and Glc; the next section will deal with
G1i.
  But first of all we need a precise definition of the notion of permutability
of rules.

5.3.1. DEFINITION. (Permutability of rules in Gentzen systems) Let us
call two logical inferences adjacent if they are separated by applications of
structural rules only.
   Rule R is said to be permutable below (or permutable down over) rule R',
if the following holds: for all inferences a E R, ß E R', a adjacent to and
above 0, such that
5.3. Permutation of rules for classical logic                                 165

      the (descendant of the) principal formula of a is not active in
      a has as premises a set of sequents A, the conclusion of a yields after
      some structural inferences a sequent S, [3 takes premises from {S} U B
      (B is possibly empty) and yields a conclusion S',

there is a deduction of S' from A U B in which one or more applications
of R', preceded by (zero or more) structural inferences, occur above and are
adjacent to an application of R, which is followed by (zero or more) structural
inferences.
  In the remainder of this section, "inference" will always mean "logical in-
ference".
  Let us consider an example in Glc. A deduction
            (A A B)n, A, F    A                 (Structural rules transform
       (AA B) F,AABLX LA                        F into ri,C; A into A', D;
                                                and (A A B) , A A B into
       1-",AABCD,A/R">                          AA B.)

can be rearranged as
                              (A A B)n, A, F       A
                         (A A B),     c A', D
                        (A A B)n,A,P   C
                                                           LA
                      (A A B),A A B,r1 C
                             AAB,r1
This shows that LA can always be permuted below R>. On the other hand,
the sequent VxA(x),3x(A(x)    1)    has a derivation with L3 below LV:

                                  Ax    Ax
                                   Ax, Ax >
                                  VxAx , Ax -4 1
                              VxAx,3x(Ax > 1)

but there is no deduction where the application(s) of L3 appear above LV.
  We now turn to the study of permutability for GS1.

5.3.2. LEMMA. (Permutation lemma for GS1) R can always be permuted
below R' except when R = R3, R' = RV.
PROOF. We give the schemas for permutation of R over          Dn for a formula
D means n copies of D. r is the set of active formulas for the rule application
a E R, and A is a set of formulas which after applying some structural
166                                          Chapter 5. Bounds and perrnutations

rules become A', the active formulas of the inference ß E R'. e is a set of
passive formulas changed by structural rules into e'. A double line marks the
application of zero or more structural rules.
One-premise rule over one-premise rule:

                                                     FAnAe
                    rAnAe                            FAnAV
                    AAnAe
                    AA'01
                                   becomes           rAnBe' o
                     ABe'                            AAnBe'
                                                      ABO'

One-premise rule over two-prem,ise rule:

                                               AnFAe           ACe'
           AnFAe                              AAnrBe'        AnAFCe'
           AnAAe                 becomes            An+1F(B A C)8'
            AB&      ACe'
              A(B A C)CY
                                                    An+2(B    C)6' a
                                                     A(B A C)8'

Two-premise rule over one-premise rule:

                                             A(A A B)nA8        B(A A B)nAID
A(A A B)nA8 B(A A B)nA8
                        a                   A(A A B) 'e'        B(A A B)nAICY
       (A A B)n+1,603
                      becomes               A(A A B)nCe'        B(A A B)nCe'
        (A A B)Z1/19'                                                           a
                                                    (A A B)n+1Ce'
           (A A B)Ce'
                                                        (A A B)C8'

Two-premise rule over two-premise rule:

              (A A B)nAAe        (A A B)BAe
                                                a
                        (A A B)+1Ae
                         (A A B)C0'                   (A A B)1316'
                                   (A A B)(C A D)6'

becomes


      (A A B)nAáe        (A A B)De'         (A A B)nBAID         (A A B)DCY
  (A A B)n+1ACCY     (A A B)+i ADei        (A A B)+1 BCe'     (A A B)n+1B De'
          (A A B)n+1A(C A D)8'                  (A A B)n+1B(C A D)8/
                                                                        a
                             (A A B)n+2(C    D)®'
                               (A A /3)(C A D)8'
5.3. Permutation of rules for classical logic                                 167

5.3.3. DEFINITION. (Partitions, order-restriction) Let D be a deduction of
a sequent S. Let           , C be a partition of all occurrences of logical symbols
in S into classes; a class Ci is said to be higher than Ci iff i < j. The partition
is admissible if it satisfies the following two conditions:

      If c is a symbol occurrence within the scope of another symbol occur-
      rence c', then c and c' are either in the same class or c is in a higher
      class than c'.
      If ac, ß are the rules corresponding to occurrences c, e' respectively,
      c' is not within the scope of c, c is an occurrence of ], and e' is an
      occurrence of V, then c is in the same or a higher class than c'.

We shall say that D satisfies the order-restriction (corresponding to the given
admissible partition) if in any branch of D no inference a occurs above an
inference de if a corresponds to a symbol occurrence in a lower class than the
symbol occurrence corresponding to )3.                                        E

5.3.4. LEMMA. (Bottom-violation) Let D be a deduction in which at most
the final logical inference a has an inference [3 above it which belongs to a
lower class than a. Then we can rearrange D to obtain D' with the same
conclusion, without violation of the order-restriction, and with all logical
inferences in D' corresponding to logical inferences in D. If D appears as a
subdeduction of a pure-variable deduction Do, it can be arranged that the
replacement of D by D' results in a D'o with the pure-variable property.
PROOF. Let the grade g(D) of D be the number of inferences )3' above a
violating the order-restriction. Apply induction on the grade. In case g(D) =
0 we are done. So let g(D) = n + 1, and let /5' be the lowest inference violating
the restriction relative to a; then ß must be adjacent to a, and a, ,8 introduce
distinct formulas which do not overlap (i.e. neither is a subformula of the
other). Now we can permute )3 below a. The only situation where this is not
possible is are precisely the ones not causing violation of the order-restriction
(part (b) of the admissibility condition).                                      E

5.3.5. THEOREM. (Ordering theorem for GS1) Let D be a deduction in
GS1 and let an order-restriction relative to a partition of the occurrences of
logical symbols in the conclusion of 7, be given. Then we can transform D
into a deduction of the same sequent satisfying the order-restriction.
PROOF. Let the degree d(D) of D be the number of logical inferences a, such
that there is a logical inference Oci violating the order-restriction. For degree
0 we are done; so let d(D) = n + 1. We look for an uppermost a, with
a violating inference above it; we apply the bottom-violation lemma to the
subdeduction ending with a,. This reduces the degree.
168                                                 Chapter 5. Bounds and permutations

5.3.6. THEOREM. Let A be a prenex formula obtained as the conclusion of
a deduction 7, in GS1. We can rearrange D to obtain a deduction TY such
that all quantifier-inferences come below the propositional inferences in any
branch of V'.
PROOF. We can distribute the symbols in A into two classes: C1 contains
all propositional operators, C2 all quantifiers. This gives rise to an order-
restriction meeting (a) and (b) of the definition.

5.3.7. THEOREM. (Herbrand's theorem) Let us consider predicate logic
without equality. A prenex formula B, say

                     B       Vx]x'VyAy'          A(x,             ...),
with A quantifier-free, is provable in GS1, iff there is a sequent F consisting
of substitution instances of A of the form A(xi, ti, yi, si, ...) such that F is
provable propositionally and B can be obtained from F by structural and
quantifier rules only.
PROOF. A proof was already sketched in 4.2.5. We can now obtain a proof as
a corollary to the ordering theorem. Applying the ordering theorem for GS1,
we can achieve that all quantifier rules are applied below all propositional
rules in the derivation of B. So the final part of the deduction derives the
formula B from the sequent corresponding to the disjunction D using only
RV, R3 and contractions (there is obviously no need for weakenings).       N


REMARK. If the prenex formula B is of the form 2xVyA(x, y), A quantifier-
free, I' may be assumed to have the following form:

                         A(to, Yo),                        , A(tn, Yn)

where the ti are such that Vi i;Z FV(ti) for i > j. This is because the first
logical inference must be RV, to be applied to an A(ti, Vi) such that yi does
not occur in ti for any j. So let us assume i = n. By the ordering theorem,
we may assume without loss of generality that this is followed (if necessary
preceded by some contractions) by R3 on VyA(tn, y), producing 3xVyA. Then
the next step must be RV again, applied to some yi, say yn-1, such that yi
does not occur in any tp for p < n, etc.
  A similar analysis applies to the more complicated case of B E Vx3yVz
A(x, y, z), A quantifier-free; in this case r may be assumed to have the form

(*)               A(xo, to, ZO),      7   A(Xi7 ti7 zi),      A(Xn7 447 zn)1

where z Ø FV(ti) for j < i. Without loss of generality we may assume that
in the tn no variables occur except the xi and the yi.
5.3. Permutation of rules for classical logic                                              169

5.3.7A. 4 Prove that the conditions on F are necessary and sufficient to guarantee
that Vx3yVzA can be derived from (*).


5.3.7B. 4 Let F be the sequent

                    A(to(xi), xo, so Yo), A(t1(x2), x, si(Yo),Y1),
                    .A.(t2(X3), X2, 82(y1)) y2), A(t3, X3, 83(y2), Y3))

with A quantifier-free. All xi, yi occurring in the tk,sk are shown. Derive from r the
prenex formula 3uVx3yVyA(u, x, y, y). (This example shows that the dependence
of the terms on the variables in the Herbrand disjunction can become complicated
for the case of more than two quantifier alternations.)


  We turn now to the formulation of the ordering theorem for Glc. The
proof runs largely parallel to the proof for the one-sided calculus GS1. The
definition of partitions and ordering condition are practically the same as for
GS1, except that the second condition (b) in the definition of admissible
partition has to be adapted:


5.3.8. DEFINITION. (Partitions, order-restriction) The definition runs as
before except that the second restriction in the definition of admissible par-
tition is modified as follows:

 (b) If         are the rules corresponding to occurrences c, c' respectively, c'
      is not within the scope of c, a, is an occurrence of LV or R3, and       is
      an occurrence of L3 or RV, then c is in the same or a higher class than
      e'.                                                                                   N


5.3.9. NOTATION. We may think of a sequent A1,                        ,   An   B1, .   ,

as a multiset of signed formulas tAi, .. , tAn, fBi, , fBn. We write for
sequents simply S, S', T, T', U, U',.... If S := r A, S' :=           A', then
SS' :=        AA'. We write s, s' for arbitrary signs from {t, f}. So sA may
stand for tA or fA.
The use of signs can be avoided in the classical context (e.g. by using one-
sided sequents), but is especially useful in the intuitionistic case.


REMARK. Since in A Ai > V Bi the Ai occur negatively and the B; posi-
tively, it might seem more natural to use +, for f, t. But f, t are customary
(and natural) in semantic tableau theory (4.9.7), and we have adopted the
same notation here.
170                                           Chapter 5. Bounds and perrnutations

5.3.10. LEMMA. (Local permutation lemma for Glc) In the calculus G1c
rule R is always permutable below R' in pure variable deductions except when
         R E {I,V, R3}, R' E {L3, Rb}.

PROOF. In the following general transformation schemas involving two-
premise rules we adopt as notational conventions: sA, s'B are principal in
R, R' respectively; the letter S is reserved for sequents of active formulas in
R, the letter T for sequents of active formulas in R'; the letter U refers to
passive sequents. Indices 1,2 refer to first and second premise; primes serve
to indicate the effect of structural rules, e.g. U' follows from U by structural
rules.
   The schemas are quite similar to the permutation schemas for GS1. The
principal reason for exhibiting them in full is that we want to be able to refer
to them in the case of G1i in the next section.
One-premise rule over one-premise rule:
                                                   S(sA)nTU
               S(sA)nTU
                                                   S(sA)nT'U'
             (sA)(sA)nTU R
                                   becomes        S (s A)n (s' B)U/ R
               (sA)T/U1
                                                (sA)(sA)n (s/ .13)U1 R
             (sA)(s'B)U/ R
                                                   (sA)(s/B)U'
Two-premise rule over one-premise rule:
                                 Si(sA)nTU               S2(sA)nTU
Si(sA)nTU S2 (sA)nTU
                                 Si(sA)nT/U/             S2 (sA)nT'U'
      (sA)(sA)nTU    R
                       becomes Si(sA)n (81.13)U/ Ft' S2(sA)n (s/ .13)U1
         (sA)T'U'
                                          (sA)(sA)n(s/ .13)U'
       (sA)(s'B)U/ R
                                             (sA)(s'B)U'
One-premise rule over two-premise rule:
                                              S(sA)nTiU             (sA)T2U/
  S(sA)nTiU
                                            S(sA)(sA)nTiU/     S(sA)(sA)nT2U/
 (sA)(sA)nTiU R                                                                 R'
                                  becomes          S(sA)(sA)n (s/ .13)U1
   (sA)Ti'U/        (sA)T2U/
                             R'                   (sA)(sA)(sA)n (s/ B)U/ R
          (sA)(s/B)U1
                                                      (sA)(s'B)U/

Two-premise rule over two-premise rule:
                  Si(sA)nTiU S2 (sA)'2TiU
                        (sA)(sA)nTiU      R
                          (sA)T1EP                  (sA)T2Er
                                                               R'
5.4. Permutability of rules for Gil                                       171

becomes

   Si(sA)'TiU          (sA)T2U/             S2(sA)'2T1U      (sA)T2UI
Si(sA)(sA)'2TIU' Si(sA)(sA)'T2U1    S2(sA)(sA)'T1U' S2(sA)(sA)'2T2U/
                                 R'                                  R'
       Si(sA)(sAr (s' B)U'                 S2 (sA)(sAr (s' BP
                            (sA)(sA)(sA)'2 (s1.13)U'
                                  (sA)(s/B)U'

In the case of quantifier rules being involved, we have to check whether the
conditions on variables remain satisfied after transformation. This turns out
to be the case except in the cases listed above. For example, if R = RV, R' =
LV, the variable condition on the given piece of deduction requires that TU
does not contain the proper parameter y of the R-inference free; this remains
correct since new variables introduced by weakening in U' must be distinct
from y in a pure variable deduction. The counterexamples are:
      LV over RV: VxAx    Vx(Ax V B),
      LV over L3: VxAx, 3x(Ax --+ I)   ,

      R3 over LA: 3x(Ax A B)     ]xAx,
      R3 over RV:    3xAx,Vx(Ax + I).
The second example has been discussed before.

5.3.10A. A Show that the counterexamples in the preceding proof are indeed
counterexamples.


REMARK. All these examples are "absolute" , that is to say in each case there
is a deduction of the provable sequent with R over R', but no deduction where
all occurrences of R' are over R, separated by structural rules only. Giving
relative counterexamples, where the given sequent can be derived from some
other given sequents with R over R', but not with R' over R, is easier. The
following describes an application of the permutation theorem for Glc.
  We can now prove a "bottom-violation lemma" and an "ordering theorem"
exactly as for GS1.

5.3.11. THEOREM. The ordering theorem holds for G1c (cf. 5.3.5).            Z


5.4         Permutability of rules for Gli
As in the preceding section, "inference" is short for "logical inference" =
application of a logical rule. Permutability of rules has already been defined
in 5.3.1.
172                                           Chapter 5. Bounds and permutations

5.4.1. LEmmA. (Local permutation lemma) In pure-variable deductions in
Gli, R is permutable below R' except in the following so-called forbidden
cases:
                    LV Lb', R3 L> R+,               RA, RV, RV, R3
               R'   RV  L3    R>                     LV


PROOF. Observe first of all that certain combinations of rules need not be
considered, due to the intuitionistic restriction on sequents. In particular,
permutation of a right rule below another right rule is not possible, since the
definition of permutability of rules will never apply: the principal formulas
concerned are nested. For the rest, the proof in this case follows the general
pattern of the proof in the classical case, but now we have to check the
intuitionistic restriction on the succedent, and moreover must pay special
attention to the L--* rule since the A appears only in the second premise.
   Let us check the intuitionistic restriction for the case of a 2-premise rule over
a 1-premise rule. Let us first observe that in the transformations indicated for
the classical case, the structural rules leading from U to U' may be postponed,
in the transformation, till after the application of R shown.
   Difficulties can arise, if among the structural rules applied below R in the
given deduction there is an application of RW serving to introduce a positive
formula serving as an active formula for the next R'-application. (If the RW
concerns U, the discussion is usually simpler.) If this is the case, sA= A,
(71U)+ = A. This application may become incorrect after transformation if
Si or 82 contains a positive formula, which is only possible if R = L>, when
Si consists of a positive active formula. The following R'-inference can be
RV, R3, RV (for L-4 over R-4 nothing is claimed).
 Let us consider the case of R' = RV. Then we transform as follows.

          FA F,B                                              r,B=-
                                                             r,B
           I'', A *B C
                                  becomes       r A r,B             CVD
         r',A>BCVD                                 r,A>B=-CVD
                                                   ri,A -4B       CVD

A similar analysis applies for a 2-premise rule over a 2-premise rule. Consider
e.g. L--+ over L-4 with an essential RW in between.

                          A

                     I", A    B     C     I'', A --+ B, D    E
                                                     E

becomes
5.4. Permutability of rules for Gli                                         173
                                                       F', A * B,D      E
                FA
                        F', (A * B)2,C      )=- E
                         P,A-413,C>DE
etc.   Counterexamples establishing the exceptions: for (R,R') = (LV,RV),
(LV,L3),(RA,L3) we can use the same examples as in the classical case. For
       (L+,R) take A (A --+ 1) =. A B,
        (L-4,LV) take A V B,A      B     B,
         (RV,LV) take AVB            A,
         (RA,LV) take Ax V Ay     3zAz.
These examples are "absolute" in the sense that the provable sequents exhib-
ited simply have no deductions where all the R'-inferences occur above the
R-inferences. In the following cases we can only give local counterexamples,
that is to say the deduction deduces a sequent from some other sequents, such
that the permutation is impossible. The derivations
       C, A      B                        CA C=B
                       DA+B                  CAAB
                                                    Cv.DAAB
              CVDA--*B
                                   Ax
                             C    VxAx D      VxAx
                                 CV E)     VxAx

give counterexamples for the pairs (R,R') = (R-4,LV), (RA,LV), (RV,LV)
respectively.

5.4.1A.         Show that the counterexamples for (L).,R-0, (L).,LV), (RV,LV),
(R3,LV) are indeed counterexamples.
   The argument concerning possibly awkward cases of RW can also be dealt
with by considering only so-called W-normal deductions in Glii, according
to the next proposition.

5.4.2. PROPOSITION. Let D be a deduction in Gli. D can be transformed
into a deduction TY by moving applications of weakening downward such
that the order of the logical inferences is retained (except that some of them
become redundant and are removed), and such that weakenings occur only

       immediately before the conclusion, or
       to introduce one of the active formulas of an application of L-4, the
       other active formula not being introduced by weakening, or
174                                        Chapter 5. Bounds and permutations

 (iii) for introducing a formula of the context of one the premises of a 2-
       premise rule, the occurrence of the same formula in the context of the
       other premise not being introduced by weakening (but not in the right
       hand context of intuitionistic L-4).
As a result, any formula not just introduced by weakening can be traced to
an axiom.
PROOF. By induction on the depth of D.                                        IE


5.4.2A. 4 Give details of the proof.

DEFINITION. A deduction D satisfying (i)(iii) of the preceding proposition
we call W-normal.                                                        El


5.4.3. DEFINMON. (Partitions, order-restriction) We copy the definition of
an admissible partition from the definition for Glc and GS1 in the preceding
section, but with the following modification:
 (b) Let R, R' be the rules corresponding to occurrences c, c' respectively,
     and let e' not be within the scope of c. In the following cases c is in the
     same or a higher class than c':

                     R LV LV, R3 L> L-4, RV, R3
                     R'   RV     L2     R*         LV                         LEI




5.4.3A. 4 If we relax (ii) in 5.4.2 by replacing "L>" by "L)., LV, L3", we
can achieve that the transformation from D to D' leaves the term denoting a
corresponding assigned natural deduction unchanged. Show that this may fail if
we do not permit LV, L.
The following lemma is easily proved.

5.4.4. LEMMA. Instances of a rule R adjacent to, and above, a rule R', can
be permuted if
      RE {R-4, RA, RV} and R' = LV, and
      over the other premise of the R'-instance (i.e. not the one deriving from
      the R-application) either a weakening or another instance of R intro-
      duces the active formula.                                               El


 "Permuted" is here meant in a slightly more general sense than in the defi-
nition, since in the transformation the rule introducing the active formula in
the second premise is also involved.
5.4. Permutability of rules for Gil                                          175

5.4.4A. 4 Prove the lemma.

5.4.5. LEMMA. (Bottom-violation lemma) Let 7, be a W-normal deduction
in which only the lowest inference violates the order-restriction relative to a
given partition. Then 1, can be rearranged so that the order-restriction is
met, and the resulting deduction is W-normal.
PROOF. Let 1, be given; we assume all instances of the axioms to be atomic,
and 1, W-normal. Let a be the last inference in D; a violates the order-
restriction w.r.t. a partition C1,  , Ck. Then there is an inference ß adjacent

to a violating the order-restriction. As before we let the grade of 1, be the
total number of inferences violating the order-restriction relative to the lowest
inference. We show how to reduce the grade by considering cases.
 Case I. The grade can be reduced by permuting 0 below a according to
the local permutation lemma, except when ß E {R+, RV, RA} and a E LV.
(Note that the other exceptions mentioned in the local perinutation lemma
cannot play a role since these cannot produce a violation by the conditions
on admissible partitions.)
 Case 2.    E RA, RV, R+, a E LV, and the principal formula A of ß in the
other premise of a introduced by weakening; we can then reduce the grade
by applying the special permutation lemma.
 Case 3. ßE RA, RV, R--+, a E LV, and the principal formula A of ß in the
second premise of a not introduced by weakening. We have two subcases.
Subcase 3.1. A is also a principal formula in the second premise of a, and has
therefore been introduced by an inference 0' of the same type as 0, necessarily
belonging to the same class of the partition; then by the special permutation
lemma we can reduce the grade.
Subcase 3.2. A is not a principal formula in the second premise, and the
inference 0' above the second premise adjacent to a must in fact be a left-
rule application. Since A was not introduced by weakening, it follows from
W-normality that there is above /3' an inference of the same rule as the rule
of 0, introducing A in the second premise of a; then -y and ß belong to the
same class and it follows that 0' also violates the order-restriction, since a is
the only inference with respect to which violations occur. But then we can
apply the local permutation lemma w.r.t. /3' and a.                            N
  We now get as before

5.4.6. THEOREM. The ordering theorem with order-restriction as defined
above holds for Gli (cf. 5.3.5).

5.4.6A. A (Herbrand's theorem for negations of prenex formulas in the language
without = and function symbols) Let B be a prenex formula
                      Vg03goVA.N..                   .,   ),
176                                            Chapter 5. Bounds and permutations

A quantifier-free, and assume I I-       Then we can find a finite conjunction C
of substitution instances of A such that I I-    and      is provable from      In
particular, if B    3iVil2E      g , E) with A quantifier-free, the members of the
conjunction are of the form A(gi, Ei), where we may assume the ri to consist of
variables in {go, ... gn, Yo,         (Kreisel [1958]).


5.4.6B. 4 For GU we define two classes of formulas simultaneously:

           gamigAgivxgi3xgli,->g

where At is the set of atomic formulas, excluding I. D is called the set of hereditary
Rasiowa-Harrop formulas. Use the ordering theorem for Gli to show that if a
sequent        G with F c 1), G E g is derivable in Gli, there is a deduction such
that (i) all sequents occurring in the deduction are of of the form          G' with
   c D, G' E g, and (ii) if the succedent formula G' is non-atomic, it is a principal
formula.
   Try to give a simple direct proof of this theorem, not relying on the ordering
theorem. Note that (a) if we add T as a primitive with axioms      T, we can add
a clause ga T        , and that (b) actually the conditions mentioned in the local
permutation lemma already suffice.


5.5        Notes
5.5.1. Bounds on cut elimination. Tait [1968] explicitly states the hyper-
exponential bound on the depth of deductions for a one-sided Gentzen system
for classical logic. Girard [1987b] presents a detailed proof of the hyper-
exponential growth under cut elimination for Gentzen's system; the proof is
also given, with a slight emendation, in Gallier [1993]. Here we have lifted
the argument to G3-systems, thereby removing the need for distinguishing
between "depth" and "logical depth" of deductions.
   Curry's proof (Curry [1963]) of cut elimination for G1i plus Peirce's rule
is analysed in Felscher [1975], who showed that Curry's procedure cannot be
formalized in primitive recursive arithmetic; Gordeev [1987] showed that a
different strategy, using appropriate inversion lemmas for a suitable system
with Peirce's rule, produces the same hyperexponential estimates as in the
case of the standard Gentzen systems. The better bounds for Ip obtained by
the inversion-rule strategy have been found by Hudelmaier [1989,1992]; the
exposition here is indebted to Schwichtenberg [1991], and hence indirectly to
unpublisfied notes by Buchholz. See also Hudelmaier [1993].
  The result in 5.2 is a slightly modified version of the presentation in Fitting
[1996], which in its turn originated in a proof in Statman [1978], as simplified
by S. Buss and G. Takeuti.
5.5. Notes                                                                   177

  An area which we have not touched upon in this book is complexity the-
ory for propositional and predicate logic. For an illuminating survey, see
Urquhart [1995]. From this it will be seen that seemingly slight modifications
in systems, which seem irrelevant from a general theoretical (metamathemat-
ical) point of view, may result in quite different behaviour from the viewpoint
of complexity theory.

5.5.2. Permutation of rules. The results in the sections on permutation of
rules are entirely based on Kleene [1952b]. In our exposition we have at one
point simplified Kleene's argument for the intuitionistic case. Curry [1952b]
discusses permutation of rules in classical Gentzen systems.
   Already the proof of the "verschärfter Hauptsatz" (sharpened Hauptsatz)
in Gentzen [1935] contains a permutation argument. The sharpened Haupt-
satz states that a cutfree deduction in classical logic may always be arranged
in such a way that the propositional inferences precede all quantifier infer-
ences; the quantifier part of the deduction is linear, the last sequent of the
propositional part is called the midsequent, and hence the sharpened Haupt-
satz is also known as the midsequent theorem. Obviously the midsequent
theorem contains a version of Herbrand's theorem; in other respects Her-
brand stated a more general result, not only for formulas in prenex normal
form (cf. the Introductory Note to Herbrand [1930] in van Heijenoort [1967],
where also corrections to Herbrand [1930] are discussed).
   Clearly, a Herbrand disjunction contains more information than the prenex
formula derived from it. This suggests that it might be profitable to look for
Herbrand disjunctions in mathematical proofs; if we are lucky, we can extract
from the terms appearing in the disjunction explicit information, such as
bounds on the size or number of realizations of existential quantifiers. An
example of such a "Herbrand analysis" is given in Luckhardt [1989]. Such
analyses are not applications of Herbrand's theorem as such, since (1) we
want more precise information than is provided by Herbrand's theorem in its
original form, and (2) interesting proofs for analysis will go beyond pure logic.
