# Basic Proof Theory — Chapter 2: N-systems and H-systems (lines 1830-2970)

Chapter 2

N-systems and H-systems

Until we come to chapter 9, we shall concentrate on our three standard logics:
classical logic C, intuitionistic logic I and minimal logic M. The informal in-
terpretation (semantics) for C needs no explanation here. The logic I was
originally motivated by L. E. J. Brouwer's philosophy of mathematics (more
information in Troelstra and van Dalen [1988, chapter 1]); the informal inter-
pretation of the intuitionistic logical operators, in terms of the primitive no-
tions of "construction" and "constructive proof", is known as the "Brouwer-
HeytingKolmogorov interpretation" (see 1.3.1, 2.5.1). Minimal logic M is a
minor variant of I, obtained by rejection of the principle "from a falsehood
follows whatever you like" (Latin: "ex falso sequitur quodlibet", hence the
principle is often elliptically referred to as "ex falso"), so that, in M, the
logical symbol for falsehood J. behaves like some unprovable propositional
constant, not playing a role in the axioms or rules.
   This chapter opens with a precise description of N-systems for the full
first-order language with proofs in the form of deduction trees, assumptions
appearing at top nodes. After that we present in detail the corresponding
term system for the intuitionistic N-system, an extension Of simple type the-
ory. Once a precise formalism has been specified, we are ready for a section on
the GödelGentzen embedding of classical logic into minimal logic. This sec-
tion gives some insight into the relations between C on the one hand and M,
I on the other hand. Finally we introduce Hilbert systems for our standard
logics and prove their deductive equivalence to the corresponding N-systems.


2.1      Natural deduction systems
We use script D, e, possibly sub- and/or superscripted, for deductions,. and
adopt the notational conventions for prooftrees with assumptions and con-
clusion adopted at the beginning of 1.3.2.

2.1.1. DEFINITION. (The systems Nm, Ni, Nc) Assumptions are formula
occurrences always appearing at the top of a branch (assumptions are "leaves"
                                      35
36                                                  Chapter 2. N-systems and H-systems

of the tree), and are supposed to be labelled by markers (e.g. natural numbers,
or variable symbols). The set of assumptions of the same form with the
same marker forms an assumption class. Distinct formulas must have distinct
markers. We permit empty assumption classes!
   Assumptions may be closed; assumption classes are always closed "en bloc",
that is to say, at each inference, either all assumptions in a class are closed,
or they are all left open. Closure is indicated by repeating the marker(s) of
the class(es) at the inference.
   For ease in the exposition, we shall reserve u, y, w for assumption markers,
and x, y, z for individual variables.
   Deductions in the system of natural deduction are generated as follows.
Basis. The single-node tree with label A (i.e. a single occurrence of A) is a
(natural) deduction from the open assumption A; there are no closed assump-
tions.
Inductive step. Let Di, D2, D3 be deductions. A (natural) deduction D may
be constructed according to one of the rules below. The classes [A]u, [B]' ,
[,A]u below contain open assumptions of the deductions of the premises of
the final inference, but are closed in the whole deduction.
   For A, V,     V, 3 we have introduction rules (I-rules) and elimination rules
 (E-rules).

                 D1    D2                     Di             Di
                 A     B                  AAB
                                                   AER
                                                            A A BAEL
                     AAB                      A

                       [A]u
                                                    Di      D2
                                                   A -4 B   A
                                                                 .4E
                                --+I,u
                       A+B


          AB
         Di

        AVB
                 VIR
                              Di

                            AVB
                                    VIL
                                                     Di
                                                    AVB
                                                             [A]u
                                                             D2
                                                              C
                                                                       [B]v
                                                                       D3
                                                                        C vE,u,v


            Di          In VI: y          x or y 0 FV(A),
          A[x I y]      and y not free in any assump-
           VxA V/       tion open in

                                   [A[x I Au         In 3E: y a-- x or y FV(A),
                           Di            D2          and y not free in C nor in any
                        3xA              C 3E5u      assumption open in D2 except
2.1. Natural deduction systems                                               37

 This completes the description of the rules for minimal logic Nm. Note that
1 has not been mentioned in any of the above rules, and therefore it behaves
in minimal logic as an arbitrary unprovable propositional constant.
  To obtain the intuitionistic and classical systems Ni and Nc we add the
intuitionistic absurdity rule _Li and the more general classical absurdity rule
    respectively:




(1, is more general than _Li since [,A]u) may be empty.) In an E-rule ap-
plication, the premise containing the occurrence of the logical operator being
eliminated is called the major premise; the other premise(s) are called the
minor premise(s) of the rule application. As a standard convention in display-
ing prooftrees, we place the major premises of elimination rule applications
in leftmost position.
   To spell out the open and closed assumptions for the rules exhibited above:

      When A is applied, the set [Ar of open assumptions of the form A in
      D becomes closed; when VE is applied, the set [Art of open assumptions
      of the form A in D2 and the set [B]V of open assumptions of the form
      B in D3 become closed; when 3E is applied, the set [A[xI y]]u of open
      assumptions of the form A in D2 becomes closed; when J. is applied,
      the set [--,A]u of open assumptions of the form -IA in D1 becomes closed.
      All other assumptions, not covered by the cases just mentioned, stay
      open.

As to the individual variables which are considered to be free in a deduction,
we stipulate

      The deduction consisting of assumption A only has FV(A) as free vari-
      ables;

      at each rule application, the free individual variables are inherited from
      the immediate subdeductions, except that

      in an application of 3E the occurrences of the free variable y in D2
      become bound, and in an application of VI the occurrences of variable
      y in D1 become bound, and

      in A the variables in FV(A) have to be added in case [Al' is empty, in
      VIR those in FV(B) have to be added, and in VIL those in FV(A) have
      to be added.
38                                          Chapter 2. N-systerns and H-systerns

The individual variable becoming bound in an application a of VI or 3E is
said to be the proper variable of a.
   Instead of closed (assumption) one also finds in the literature the terminol-
ogy eliminated or cancelled or discharged. Because of the correspondence of
closed assumptions with bound variables in the term calculus (to be explained
in detail in the next section) we also sometimes use "bound" for "closed". If
A is among the open assumptions of a deduction D with conclusion B, the
conclusion B in D is said to depend on A in D. From now on we regard
 "assumption of D" and "open assumption of 7," as synonymous.                 E



2.1.2. DEFINITION. A convenient global assumption in the presentation of
a deduction is the variable convention. A deduction is said to satisfy the
variable convention if the proper variables of the applications of 3E and VI
are kept distinct. That is to say, the proper variable of an application a of
3E or VI occurs in the deduction only above a.
   If moreover the bound and free variables are kept distinct, the deduction
is said to be a pure-variable deduction. Henceforth we shall usually assume
that the pure-variable condition is satisfied.



2.1.3. REMARKS. (0 Since in our notation for prooftrees, [A]u refers to
all assumptions A labelled u, it is tacitly understood that in VE the label u
occurs in D2 only, and y in D3 only. Similarly, in 3E the marker u occurs
in D2 only. This restriction may be relaxed, at the expense of a much more
clumsy formulation of 3E and VE.
   (ii) The rules of (extensions of) natural deduction systems are often pre-
sented in a more informal style. Instead of using inductive clauses "If Do,
D1, . . . are correct deductions, then so is D" as we did above, we can also de-
scribe the rules by exhibiting premises and assumptions to be discharged (if
any), where the deductions between assumptions and premises are indicated
by vertical dots. Thus --+E and VE are given by the schemas


                                                 [A]u   [B]v


           A > B A --+E                 AV B      C      CVEu,v



2.1.4. EXAMPLES. The first example is in the classical system Nc:
2.1. Natural deduction systems                                                              39

                                                        A(x)u
                                          axA(x)u     AxA(x) 31
                                                                    *I
                                                        +I7v
                                                ,A(x)
                                                          VI
                                              Vx,A(x)
                                                          *E

                         ,Vx,A(x) + 3xA(x)
The next example is in Ni:

                                                                     Pxt)        Px"' _+E
                                                QYw                        Qy Ii
                                                                            _L

             Px-43yQy          Pxu            Px--+Qy
              3E,w ]YQY                     2y (Px>QY)
                                  Ay(Px--*Qy)
                                                                     2Y(PxQY)2VIE,u,
                                  3Y(PxQY)
                               Vx3y(Px--*Qy)
                                                 VI

                           A       Vx3y(PxQy)
where A     Vx(Px V ,13x) A Vx(Px > 3yQy), and where D, TY are
                       A's'                             A ui
                                 AE                                  AE
                   Vx(PxV-,./3x)                Vx(Px--+3yQy)
                    PxVPx            VE           px_43yQy           VE

We also give two examples of incorrect deductions, violating the conditions
on variables in VI, 3E. The conclusions are obviously incorrect, since they
are not generally valid for the standard semantics for classical logic. We have
marked the incorrect assumption discharges with an exclamation mark.
                                                               py    Qu      pyv
                                                  Pxw                                 >E
                                                                         Q 3E v !
            Pxu VI,!                                                              ,

           VY PY          u
     Px --4Vy Py                                    3x Px > Q
                   VI                                                            A, u
    Vx(Px > Vy Py)                         (Py Q) --+ (3x Px   Q)
                                                                Q)) VI
                                          Vy((Py Q)    (3x P x

2.1.5. DEFINITION. The theories (sets of theorems) generated by Nm, Ni
and Nc are denoted by M (minimal logic), I (intuitionistic logic) and C
(classical logic) respectively.
  r Hs A for S = M, I, C iff A is derivable from the set of assumptions r in
the N-system for S.                                                       IE1
40                                           Chapter 2. N-systerns and H-systems

2.1.6. Identity of proof trees. (i) Prooftrees are completely determined if we
indicate at every node which is not a top node which rule has been applied to
obtain the formula at the node from the formulas at the nodes immediately
above it, plus the assumption classes discharged, if any.
   (ii) From 1.3.6 we recall that two prooftrees are regarded as (essentially) the
same, if (1) the underlying (unlabelled) trees are isomorphic, (2) nodes cor-
responding under the isomorphism get assigned the same formulas, (3) again
modulo the isomorphism, the partitioning of assumptions into assumption
classes is the same, and (4) corresponding assumption classes are discharged
at corresponding nodes. Moreover, under the isomorphism, corresponding
open assumptions should get the same marker.
   Needless to say, in many cases it is not really necessary to indicate the
rule which has been used to arrive at a particular node, since this is already
determined by the form of the formulas at the nodes; but in a few cases
the rule applied cannot be unambiguously reconstructed from the formulas
alone. Nor is it essential to indicate a variable for a discharged assumption
class at a rule application, if the assumption class happens to be empty.
The reason why we insisted, in the definition of deduction above, that in
principle this variable should always be present, is that this convention leads
to the most straightforward correspondence between deductions and terms of
a typed lambda calculus, discussed in the next section.

2.1.7. REMARKS. (0 The absurdity rules J..j and 1, might be called elimi-
nation rules for 1, since they eliminate the constant J_; this suggests the des-
ignations       _LE, for these rules. However, they behave rather differently
from the other E-rules, since neither has the conclusion a direct connection
with the premise, nor is there an assumption directly related to the premise,
as in VE, E. Therefore we have kept the customary designation for these
rules. This anomalous behaviour suggests another possibility: taking Nm as
the basic system, Ni and Nc are regarded as Nm with extra axioms added.
For Ni one adds \g/ '(.1_ -4 A), with a FV(A), and for Nc one adds stability
axioms V(--A -4 A) (see 2.3.6).
  (ii) Sometimes it is more natural to write VE and 3I as two-premise rules,
with the individual term as second premise (a minor premise in case of VE):

                         VxA        t      A[x/t]      t
                           A[x/t]             2xA

This emphasizes the analogies between --+E and VE, and between AI and
 I. The mixing of deduction with term construction might seem strange
at first sight, but becomes less so if one keeps in mind that writing down
a term implicitly entails a proof that by the rules of term construction the
term denotes something which is in the domain of the variables. Such extra
premises become indispensable if we consider logics where terms do not always
2.1. Natural deduction systems                                                 41

denote; see 6.5. This convention is also utilized in chapter 10. If one wants to
stress the relation to type theory, one writes t: D (D domain of individuals)
for the second premise.
        The statement of the rules VI and AE may be simplified somewhat if
we rely on our convention that formulas differing only in the naming of bound
variables are equal. These rules may then be written as:
                                                    [A]u

                        A
                                              Di    D2
                       VxA
                           VI                 3xA    C 3E,u

where in VI x is not free in any assumption open in 1,1, and in 3E x is not
free in C nor in any assumption open in 7,2 except in [A]u.
       In theories based on logic, we may accommodate axioms as rules with-
out premises; so an axiom appears in a prooftree as a top node with a line
over it (in practice we often drop this line).

2.1.8. Natural deductions in sequent style
In the format described above, the assumptions open at any node y in a de-
duction tree 1, are found by looking at the top nodes above zi; the ones bearing
a label not yet discharged between the top node and y are still open at v.
Less economical in writing, but for metamathematical treatment sometimes
more convenient, is a style of presentation where the open assumptions are
carried along and exhibited at each node. We call the set of open assumptions
at a node the context. A context is a set
         u1: A1, u2: A2,.       , un:

where the ui are pairwise distinct; the Ai need not be distinct. The deductions
now become trees where each node is labelled with a sequent of the form
r     B, r a context. Below, when writing a union of contexts such as rA
(short for r U A), it will always be assumed that the union is consistent, that
is to say, again forms a context. In this form the rules and axioms now read
as follows:

         u:A      A (Axiom)
         r[u:          B    T




         rA  A
          rA ,4/\,8
                                B
                                    AI
                                         rAonAi AE
                                          r    Ai

              r   Ai
                           VI
                                    rAvB A [u: A]          C Aqv: B]    C vE
42                                                       Chapter 2. N-systems and H-systems


              FA
         r[x: ---,A]        1     1




                                  --C              FA'
                                                   F    _L
                                                             _Li



         F       A[xly]                             F    VxA
          r       VxA
                             VI
                                                   F    A[xlt]
                                                                   VE


         r       A[x It] 3,                        F    3yA[x/y]           A[u: A]    C
                                                                                          3E
          F       3xA                                                     C

Here [u: C] means that the assumption u: C in the context may be present or
absent. Moreover, in q u: A does not occur in F, in VE u: A and 1): B do
not occur in FA!, in ic u:     does not occur in F, and in 3E u: A does not
occur in F.
  The correspondence is now such that at any node precisely the inhabited
assumption classes which are not yet closed at that node are listed.

2.1.8A. 4 Give proofs in Nm or Ni of
        A > (B -4 A);
            AV B, B                     (AV B);
        (A       C)         [(B         C) > (A V B      C)];
                             AAB>B, A>(B>.AAB);
        1       A;
        VxA          A[x It];         A[x It]   3x A;
        Vx(B -4 A) 44 (B   VyA[x/y]) (x Ø FV(B), y                         x or y 0 FV(A));
        Vx(A    B)    (3yA[xly]  B) (x Ø FV(B), y                          x or y Ø FV(A)).

2.1.8B. 4* Give proofs in Nm of
        A>

          -,(A         B)
              A B)     ( -,.4 A -,-,B);
          (A V B) 44 (-,A A -,B);
           VxA


2.1.8C. 4 Give proofs in Nm of
        (B             > (A > B) > A >                  (b-axioms),
        (A    B         B -4 A >     (c-axioms),
        (A -4 A > B) -4 A    B (w-axioms).


2.1.8D. 4 Prove in Ni                                                   B). Hint. First construct
deductions of           and of             from the assumption -,(A         B).
2.1. Natural deductzon systems                                                43

2.1.8E. 4* Prove in Nc
            AVB                        A ,B),
            3xA
            ((A        B) > A) > A (Peirce's law).

2.1.8F. 4* Construct in 114-n a proof of
            ((A        13)        C)      (A    C)   C

from two instances of Peirce's law as assumptions: ((A      B)     A)     A and
((C     A)        C)         C.

2.1.8G. 4* Derive in q\I'm PA,BAC frOM PA,B and PA,C, where Pxy iS ((X
Y)    X)    X, i.e., Peirce's law for X and Y.

2.1.8H. 4* Let F[*], GH be a positive and negative context respectively. Prove
in Nm that
             Vi(A            B)         (F[A]   F[B]),
            F- VY(A          B)         (G[B]   G[A]),

where   consists of the variables in A    B becoming bound by substitution of A
and B into FH in the first line, and into GH in the second line.

2.1.9. The Complete Discharge Convention
One possibility left open by the definition of deductions in the preceding sec-
tion is to discharge always all open assumptions of the same form, whenever
possible.
   Thus in *I we can take [A]x to represent all assumptions of the form A
which are still open at the premise B of the inference and occur above B; in
an application of VE [A]u, [B]v represent all assumptions of the form A still
open at C in the second subdeduction, and all assumptions of the form B
still open at C in the third subdeduction respectively; in an application of 3E
[A[x 10 represents all assumptions of this form in the second subdeduction
still open at C.
   It is easy to see that a deduction remains correct, if we modify the discharge
of assumptions according to this convention. We call this convention the
 "Complete Discharge Convention", or CDC for short.
   Note that the use of markers, and the repetition of markers at inferences
where assumption classes are being discharged, is redundant if one adopts
CDC (although still convenient as a bookkeeping device).
   From the viewpoint of deducibility, both versions of the notion of deduc-
tion are acceptable; CDC has the advantage of simplicity. But as we shall
44                                          Chapter 2. N-systems and H-systerns

discover, the general notion is much better-behaved when it comes to studying
normalization of deductions. In particular, the so-called "formulas-as-types"
analogy ("isomorphism"), which has strong motivating power and permits us
to transfer techniques from the study of the lambda calculus to the study
of natural deduction, applies only to the general notion of deduction, not to
deductions based on CDC.

2.1.10. Digression: representing CDC natural deduction with sequents
Let No be intuitionistic natural deduction for implication under CDC. No can
be presented as a calculus in sequent notation, N1, in the following (obvious)
way:


           AA                r B                  r    A     B     r
                         r\-(241 -AB                    rur,      B

Here the antecedents are regarded as sets, not multisets.
   Ni-deductions are obtained from No-deductions by replacing the formula
A at node y by the sequent          A, where r is the set of assumptions open
at v.
   At first sight one might think that the following calculus N2 -

           I', A    A

  where the antecedents of the sequents are treated as multisets, represents a
step towards the standard *Ni (without CDC), since it looks as if distinct
occurrences of the same formula in the antecedent might be used to represent
differently labelled assumption classes in No-deductions. But this impression
is mistaken; in fact, if we strip the dummy assumptions from deductions in
N2, there is a one-to-one correspondence with the deductions in Ni.
   Let us write v[ri     for the deduction in N2 obtained from D by replacing
at each node 1, of D the sequent r A at that node with IT' A.
   We show how to associate to each deduction D of I'     A in N2 a deduction
D' of r'      A, r c I' with the same tree structure, such that

  (0 all A E r occur as conclusion of an axiom and r is a set,

       D is TY[(r          that is to say D is obtained from D' by weakening
       the sequents throughout with the same multiset,

       if Di, is the subdeduction of D associated with node y, and we replace
       everywhere in D the conclusion of Dv by the conclusion of (V'), then
       the result is a deduction (/)(D) in Ni.
2.2. Ni as a term calculus                                                            45

The construction is by induction on the depth of D, and the properties just
listed are verified by induction on the depth of D.
Case 1. To an axiom r, A       A we associate the axiom A  A.
Case 2. Let the proof D end with --+I:
                                            Do
                                        I', A  B
                                             A   B
To Do we have already assigned, by 1H, a Dio with conclusion r           B. There
are two cases: A does not occur in P, or r is of the form r", A, A not in r".
In the first case, D' is as on the left, in the second case as on the right below:
                         D'o[A
                       I', A       B                     f", A    B
                     r        A>B                    r"         A  B
Case 3. Let D end with
                                       Do
                                                     r      A
                                                 B
The 1H produces two deductions
                                 D'o
                         ro       A --> B                         A
and we take for TY
                      Ayr, ro)                                   ro
                     rourl                           rour,            A
                                        ro U r
We leave it to the reader to construct a map              from N1 to N2 which is inverse
to 0.

2.1.10A. 04 Define the map /,b mentioned above and show that it is inverse to 0.


2.2      Ni as a term calculus
2.2.1. Extending the term notation for implication logic, described in sec-
tion 1.3, we can also identify the full calculi Ni, Nm with a system of typed
terms in a very natural way. The typed terms serve as an alternative nota-
tion system. In a sense, this makes the use of calligraphic D,E for deductions
in the case of N-systems redundant; we might as well use metavariables for
terms in a type theory (say s, t) for deductions. Nevertheless we shall use
both notations: D,E if we wish to emphasize the prooftrees, and ordinary
term notation if we wish to exploit the formulas-as-types parallel and study
computational aspects.
46                                                      Chapter 2. N-systerns and H-systerns

2.2.2. DEFINITION. (Term, calculus for the full system Ni) The variables
with formula type are distinct from the individual variables occurring in the
types (formulas), and the sets of variables for distinct types are disjoint. We
exhibit the generation of terms in parallel to the rules. To each rule corre-
sponds a specific operator. For example, the first term-labelled rule AI corre-
sponds to a clause: if to: Ao and t1: A1 are terms, then p(t0:A0, ti    Ao A Ai ,
or p(440, 1)A01,nA is a term. Together with the listing of the clauses for the
generation of the terms, we specify variable conditions, the free assum,ption
variables (FVa) and the free individual variables (FVi). As in type theory, we
abbreviate App(t, s) as ts.

 u: A                                         FVi(u) := FV(A), FVa(u) := {u}.



  t: A       s: B AT                          FVi(p(t, s)) :=FV i(t)UFVi(s);
 p(tA, sB): A A B                             FVa(p(t, s)) := FVa(t) U FVa(s).


      t: A0 A Ai                         .,
                                              FVi (Pi (t)   FVi(t);
                         AE (jE{O, 11.)
      (tAonAi ):                              FVa(Pi(t)) := FVa(t)-


           t: A                         FV;(ki(t)) := FVi(t) U FV(Ai_i), and
                            VI UE{0,1}) FVa(ki(t)) := FVa(t).
 ki(tAi): Ao V Ai


                   [u: A]       [v: B]        u 0 FVa(t, s'), y 0 FVa(t, s),
                    Do           Di           FVi(Etv,,v(t, s, s')) := FVi(t,   s');
 t:AV B             s:C     s':C ",           FVa(Ent, s')) :=
     E\u/ ,v(tAv     sc 8/c): c v               FVa(t) U (FVa(s) \ {u}) U (FVa(s') \ {v}).



           [u: A]
                                              FVi(AuA.t) := FV;(t) U FV(A);
       t: B                                   FVa(AuA.t) := FVa(t) \ {u}.
 (ÀatA .tB): A -4 B -41



 t: A B                  s: A                 FV;(ts) := FVi(t) FVi(s);
        tA-4. B      B                        FVa(ts) := FVa(t) U FVa(s).
2.2. Ni as a term calculus                                                   47
                                  y   x or y FV(A), and
 t[xI y]: A[x Iy]                  if uB E FVa(t), then x FV(B);
  Ax.tA :V x A VI                 FV;(Ax.t) :-= FVi(t) \ {x};
                                  FVa(Ax.t) := FVa(t).


     t: VxA                       FV;(ts) :-= FVi(t) U FV(s);
                    VE
 exAs: A[x I s]                   FVa(ts) := FVa(t).


     t: A[xI .5]                  FV;(p(t, s)) := FVi(t),
 p(tA[x/si, s):3xAl               FVa(p(t, s)) := FVa(t).


                                  y mx or y 0 FV(A),
            [u: A[x I y]]           u 0 FVa(t), y 0 FV(C), and
                                    if vB E FVa(8) ful, then y 0 FV(B);
 t:3x A            s: C           FV,(K y(t, s) := FVi(t) U (FV;(s) \ {y});
              sc): C              FVa(EL(t, s) := FVa(t) U (FVa(s) \ {u}).


    t: _L                         FVi(EA-(t)) := FVi(t) U FV(A);
 Ei(t1): A                        FVa(EA-(t)) := FVi(t).

Finally, we put FV(tA) := FVi(tA) U FVa(tA).

REMARKS. (i) Dropping the terms and retaining the formulas in the schemas
above produces ordinary prooftrees, provided we keep assumptions labelled
by variables, and indicate where they are discharged.
       The term assigned to the conclusion describes in fact the complete
prooftree, i.e. the deduction can unambiguously be reconstructed from this
term.
        Since the variables are always supposed to have a definite type (we
could say that individual variables have a type I), it would have been possi-
ble to define FV straight away, instead of FVi and FVa separately, but the
resulting definition would not have been very perspicuous.
       We may assume that proper parameters of applications of 3E and VI are
always kept distinct and are used only in the subdeduction terminating in the
rule application concerned; this would have resulted in slight simplifications
in the stipulations for free variables above. Similarly, assuming that all bound
assumption variables are kept distinct permits slight simplifications.
       The conditions u 0 FVa(t, s'), 'u FVa(t, s) in VE, and the condition
U 0 FVa(t) in 3E may be dropped, but this would introduce an imperfection
48                                          Chapter 2. N-systems and H-systems

in the correlation between deduction trees as described earlier in 2.1.1 and the
term calculus. The conditions just mentioned correspond to the conditions
in 2.1.1 that the u in VE occurs in D2 only etc.
       There is considerable redundancy in the typing of terms and subterms,
and in practice we shall drop types whenever we can do so without creating
confusion.
       Instead of the use of subscripted variables for the operators, we can use
alternative notations, such as E3(t, (y, z)s), Ev(t, (y)s, (z)s'). Here variables
are bound by "( )" , so as not to cause confusion with the A which is associated
with q and VI.
        As noted before, in the rules VE and 3I the term s may appear as
a second premise; in certain situations this is a natural thing to do (analogy
with type theories).
       Extra axioms may be represented by addition Of constants of the ap-
propriate types.

2.2.2A. ** Give proofs in Nm of (A v B            ((A  C) A (B    C)) (A,B,C
arbitrary), and of Vx(Rx .14)      (3xRx     ley) (R, unary relation symbols)
and label the nodes with the appropriate terms; compute E'Va and FIT; for the
terms assigned to the conclusions.


2.3      The relation between C, I and M
In this section we discuss some embeddings of C into M or I, via the so-called
 "negative translation". This translation exists in a number of variants.

2.3.1. DEFINFrION. A formula A in a first-order language is said to belong
to the negative fragment (or "A is negative") if atomic formulas P occur only
negated (i.e. in a context P I) in A, and A does not contain V, 3.

2.3.2. LEMMA. For A negative, M H A i4
PROOF. As seen by inspection of exercise 2.1.8B, the following are all provable
in Nm:
         A                    44 -IA;
               A B)          A
                  B)               -,B),                    44 (A -4
                 -->

Using these implications, we establish the lemma by induction on the depth
of A; A has one of the forms ,13 (P atomic), I, B A C, B -4 C, VxA.
Consider e.g. the case A as B --> C. Then                     C) which implies
(B            and by IH (B      C); this finally yields          C). We leave
the other cases to the reader.                                                El
2.3. The relation between C, I and M                                                 49

2.3.2A. 4 Do the remaining cases.

2.3.3. DEFINITION. For all formulas of predicate logic the (GödelGentzen)
negative translation g is defined inductively by
       Pg         :=       for atomic P;
       1g         :=
(Ho (A A B)g := Ag A Bg;
       (A > B)g := Ag       Bg;
       (VxA)g     := WAg;
       (A V B)g := 1(-1Ag A --Og);
      (3xA)5
   Inessential variants are obtained by dropping clause (ii) and applying the
first clause to 1 as well, or by adding a process of systematically replacing
     by

2.3.4. THEOREM. For all A
  (i) C F- A i4 Ag;
     F I, A <=> Fg hm Ag,

where rg := {Bg : B E rl.
PROOF. The proof shows by induction on the length of deductions in Nc that
whenever I' H A, then Fg I Ag. The rules for V, 2 are in Nc derivable from
the other rules, if we use the classical definitions A V B := n(nA A 0), 3x A
:= NixA. So we may restrict attention to Nc for the language AV>I.
   All applications of rules, except applications of 1,, translate into applica-
tions of the corresponding rules of Nm, e.g.
                            [A]x
                                           translates as
                             B         x
                        A          B
For the translation of I, we need lemma 2.3.2:
                                                                  HAT

                                                                  -X
            [A]x
                                                                  pg
                             translates as            DA
               J_
               A
                    X                                      > Ag   nnAg
                                                             Ag
where DA is a standard proof of ,Ag                    Ag as given by lemma 2.3.2.   El


2.3.5. COROLLARY. For negative A, C I A iff M I A, i.e. C is conservative
over M w.r.t. negative formulas.
50                                           Chapter 2. N-systerns and H-systems

2.3.5A. 4 Derive the rules for defined V, 3 from the other rules in Nc.
In a very similar way we obtain the following:

2.3.6. THEOREM. Let r, A be formulas without V, 3, and let Nc F =- A.
Then there is a proof of M H r, A =- A where A consists of assumptions
               RY), R a relation symbol occurring in F, A. (Such assumptions
are called stability assumptions.)
PROOF. Since V, 3 are classically definable, we may assume that the whole
proof of Nc H F       A is carried out in the language without V, 3. For this
fragment, all instances of 1, are reducible to instances with atomic conclu-
sion relative to the rules of Nm (exercise). For the rest, the proof proceeds
straightforwardly by induction on the length of classical deductions in the
language without V, 3.

2.3.6A. 4 Show that in Ni all instances of _Li are derivable from the instances
of _Li with atomic conclusion. Show that in Nc, for the language without V, 3,
all instances of I, are derivable from instances I, with atomic conclusion. (For a
hint, see 6.1.11.)

2.3.7. Other versions of the negative translation
One of the best known variants is Kolmogorov's negative translation k. Ak
is obtained by simultaneously inserting double negations in front of all sub-
formulas of A, including A itself, but excepting 1, which is left unchanged.
Inductively we may define k by:
          Pk         :=    for P atomic;
          _Lk        ;_
          (A o ß)k :=       o ßk) for o E {A, V, 4;
          (QxA)k := --,(Qx)Ak for Q E {V, 3}.
Another variant Aq (Kuroda's negative translation) ("q" from "quantifier")
is obtained as follows: insert after each occurrence of V, and in front of
the whole formula.

2.3.8. PROPOSITION. M Ag 44 Ak,              I H Ag 44 Aq.

2.3.8A. 4* Prove the proposition.

COROLLARY. For formulas A not containing V, C H              iff I H
PROOF. Let C H -IA, then C H             hence M H       Now (-,A)
and by the proposition I H (_,A)                  But (-,A)q
                                       +-* (--,A)q.                           and
IH
2.4. Hilbert systems                                                       51

2.4      Hilbert systems
Hilbert systems, H-systems for short, are very convenient in proofs of many
metamathematical properties established by induction on lengths of deduc-
tions. But the main theme of this text contains cutfree and normalizable
systems, so we shall not return to Hilbert systems after this section, which
is mainly devoted to a proof of equivalence of Hilbert systems with other
systems studied here.
  By a Hilbert system we mean an axiomatization with axioms and as sole
rules *E and VI; so there are no rules which close hypotheses (= assump-
tions). In a more liberal concept of Hilbert formalism one can permit other
rules besides or instead of +E and VI, provided that no rule closes assump-
tions. (For example, we could allow a rule: from A, B derive A A B.)

2.4.1. DEFINITION. (Hilbert system,s Hc, Hm, Hi for C, M and I) The
axioms for Hm are
        A + (B A), (A + (B C)) -4 ((A * B) * (A * C));
        A*AV B, B-4 AV B;
        (A -4 C)       ((B + C) + (AV B        C));
        AAB*A, AAB+B, A+(B+(AAB));
        V x A > A[x It],A[x   -4 3xA;
        Vx(B > A) --* (B VgA[xly]) (x           FV(B), y    x or y Ø FV(A));
        Vx(A   B)     (3yA[x/y]   B)            FV(B), y    x or y 0 FV(A)).
Hi has in addition the axiom 1 > A, and Hc is Hi plus an additional axiom
schema        + A (law of double negation). Instead of the law of double
negation, one can also take the law of the excluded middle A V
Rules for deductions from a set of assumptions r:
Ass     If A E r, then r A.
>E      If 1" H A * B, rHA, then 1"       B;
VI      If r H A, then r H VyA[x/y], (x        Fv(r), y    x or y Ø FV(A)).
>E is also known as Modus Ponens (MP), and VI as the rule of Generalization
(G).
  Deductions from assumptions r may be exhibited as prooftrees, where ax-
ioms and assumptions from r appear at the top nodes, and lower nodes are
formed either by the single-premise rule VI or by the two-premise rule *E.
As observed already in 1.3.9, quite often the notion of deduction is presented
in linear format, as follows:
   A1,     ,A is said to be a deduction of A from r, if An -= A, and each Ai
is either an element of r, or an instance of a logical axiom, or follows from
A5, j < i, by VI, or follows from A5 and Ak with j and k < i, by 4E.        E
52                                                 Chapter 2. N-systems and H-systems

2.4.2. THEOREM. H[mic] and N[mic] are equivalent, i.e. r I A in H[mic]
iff        A in N[MiC].
PROOF. We concentrate on the intuitionistic case. The direction from left to
right is straightforward: we only have to check that all axioms of Hi are in
fact derivable in Ni (exercise 2.1.8A, example 1.3.3); the rules *E, VI are
also available in Ni.
   Now as to the direction from right to left. First we show how to transform
a deduction in Ni into a deduction in the intermediate system with axioms of
Hi and rules       VI and -4E only, by induction on the height of deductions.
There are as many cases as there are rules. On the left hand side we show
a derivation of height k + 1 terminating in AI, VE, 3E; on the right we
indicate the transformation into a deduction with axioms and         and -->E
only. By induction hypothesis, 7,1, D2 7,3 have already been transformed into
TYI,T,,V1/3 respectively.


1,1D2                             (B   (A A B)) A
                            A
A   B
 AAB                              B    (A A B)
                                           AAB

                                                                   [A]
                                                                          [B]
         [A]      [B]
 Di      D2       V34           (AW),«BrC)>(AVBrC))    A+C
AV B     C        C
                                       (B+C)-4(AVBW)                      B+C
                                                  AV BW                         AvB


                                                      [A[x I y]]
                                                        T;o
       [A[xly]]
 Di      D2             4                            A[xly]+C
3xA       C
                            Vx(AW)(3xA>,C)           Vx(AW)
                                         3xA   C                    3xA


In the second prooftree it is tacitly assumed that x i;Z FV(C); if this is not
the case, we must do some renaming of variables. Alternatively, we may rely
on our convention that formulas and prooftrees are identified if differing only
in the names of. bound variables. The remaining cases are left as an exercise.
   Now we shall show, by induction on the height of a deduction in the in-
termediate system, how to remove all applications of           First we recall
that A > A can be proved in Hi by the standard deduction DA exhibited in
subsection 1.3.9.
  Consider any deduction D with axioms, open hypotheses and the rules *I
and --*E. Suppose D ends with    say D is of the form
2.4. Hilbert systems                                                           53

                                      [Aix
                                      D1
                                         B
                                     A*B
and let TY1 be the result of eliminating a from 7,1 (induction hypothesis).
We have to show how to eliminate the final     from




We do this by showing how to transform each subdeduction Do (with conclu-
sion C say) of IY1 into a deduction


                                     A        C
by induction on the height of Do.
Basis. A top formula occurrence C not in the class indicated by [A]x in VI
is replaced by

             C        (A    C)   C
                       A+C
and the top formula occurrences in [Aix are replaced by DA.
Induction step. Do ends with +E or with VI. We indicate the corresponding
step in the construction of 7); below.

             D3
    D2
                 D     goes to
                                                       A>C A>.13>C
D        C
                                             (A>D)>A     C                 A   D
                                                             A -4 C

and for C            VxB


    D2
                      goes to                            A > B[x y]
B[xly]
 VxB
                                 Vx(A*B)(A >VxB)         Vx(A         B)
                                              A   VxB

By induction hypothesis, TY,D; have already been constructed for V2, V3.
The case for minimal logic is contained in the argument above. The extension
to the classical case we leave as an exercise.
54                                             Chapter 2. N-systerns and H-systerns

REMARKS. (i) This argument may also be read as showing that Hi itself is
closed under +I, i.e. it shows how to construct a proof of F I A > B from
a proof of F, A H B. This is called the deduction theorem for Hi.
      The compactness of term notation is well illustrated by the following
example. Suppose we want to show that the rule VE can be replaced by
instances of the axiom (A-4C) * (B+C) --+ (AV B --+ C). Let so(xA): C,
si(y3):C , t: AV B be given, and let d be a constant for the axiom. Then
d(AxA .4)(4B .si9tAvB:C takes the place of the voluminous prooftree oc-
curring at the relevant place in the argument above.
       If we concentrate on implication logic, we see that the method of
eliminating an open a,ssumption A, in the proof 6f the deduction theorem, is
exactly the same, step for step, as the definition of the abstraction operator
A*xA in combinatory logic (1.2.19). Consider, for example, the induction step
in this construction. By induction hypothesis, we have constructed on the
prooftree side deductions of r I A -4 (C    D), corresponding to a term
A. xA .tC--+D
              and of F H A > C, corresponding to a term A*xA.sc. The
deduction of A * D constructed from this corresponds to
     sA,C,D: (A(CD))((AC)(AD))         A* xA    A(CD)
                     s(A*xA.t):(AC)(AD)                         A*xi t.sc Ac
                                   s(A*x.t)(A*x.$): AD

where > has been dropped, that is to say, EF is short for E + F.

2.4.2A. 4 Do the remaining cases of the transformation of a natural deduction
in the intermediate system.

2.4.2B. 4 Show the equivalence of Hc and Nc.

2.4.2C. 4 Show that Hi with        as primitive operator may be axiomatized by
replacing the axiom schema 1      A by A            B) and (A     B)    (-43 >


2.4.2D. 4* An alternative axiomatization for *Hm is obtained by taking as
rule modus ponens, and as axiom schemas A B       A, (A > A B)                 B
(contraction), (A    B     C)     (B    A    C) (permutation), (A          B)
(C A) > (C        B) (when combined with permutation this is just transitivity of
implication). Prove the equivalence.

2.4.2E. 4 Show that a Hilbert system for V).AM is obtained by taking as the
only rule -4E, and as axioms ViF, where F is a formula of one of the following
forms: A > B -4 A; (A > B          C) > (A       B) A C; A > B > A A B;
Ao AA1 r A (i E 1041); B
2.5. Notes                                                                       55

VxB        VxC (y 0 FV(Vx(B        C)); VxA     A[x/t]. Can you extend this to full
M?

2.4.2F. 01 Show that the following axiom schemas and rules yield a Hilbert system
for Ip: (1) A > A, (2) if A, A   B then B, (3) if A B and B       C then A      C,
(4)AAB-- A,AAB> B, (5)AAVB,BAvB,(6)ifA> C, B                                     C
then AVB       C, (7) if A    B, A     C then A       B AC, (8) if AAB C
then A   (B     C), (9) if A > (B C) then A A B C, (10) 1 A. This is
an example of a Hilbert system for propositional logic with more rules than just
modus ponens. (Spector [1962], Troelstra [1974)


2.5         Notes
2.5.1. The BrouwerHeytingKolmogorov interpretation. This interpreta-
tion (BHK-interpretation for short) of intuitionistic logic explains what it
means to prove a logically compound statement in terms of what it means to
prove its components; the explanations use the notions of construction and
constructive proof as unexplained primitive notions. For atomic formulas the
notion of proof is supposed to be given. For propositional logic the clauses of
BHK are

         p proves A A B iff p is a pair (po, pi) and po proves A, pi proves B,
         p proves A V B iff p is either of the form (0, pi), and pi proves A, or of
         the form (1) and pi proves B,
         p proves A > B iff p is a construction transforming any proof c of A
         into a proof p(c) of B,
         J_ is a proposition without proof.

It will be clear that A V        (that is to say, A V (A --+ ±)) is not generally
valid in this interpretation, since the validity of A V     would mean that for
every proposition A we can either prove A or refute A, that is to say we can
either prove A or give a construction which obtains a contradiction from any
alleged proof of A. (The only way of making A V            generally valid would
be to give "proof" and "construction" a non-standard, obviously unintended
interpretation.) More information on the BHK-interpretation and its history
may be found in Troelstra and van Dalen [1988, 1.3, 1.5.31, Troelstra [1983,
1990].
  For predicate logic we may add clauses:

         p proves (VxED)A if p is a construction such that for all d E D, p(d)
         proves A[x/d],
56                                             Chapter 2. N-systems and H-systems

         p proves (3xED)A if p is of the form (d, p') with d an element of D, and
         p' a proof of A[x I 4

2.5.2. Natural deduction. Gentzen [1935] introduced natural deduction sys-
tems NJ and NK for intuitionistic and classical logic respectively. NJ is like
Ni, except that --, is treated as a primitive with two rules

                                               Di        D2
                                               A         ,A _,E
                                                    J_


which reduce to instances of -->I, -->E if ,A is defined. Gentzen's NK is
obtained from NJ by adding axioms A V ,A. Gentzen was not the first to
introduce this type of formalism; before him, Jagkowski [1934] gave such a
formalism (in linear, not in tree format) for classical logic (cf. Curry [1963, p.
249]).
   Gentzen's examples, and his description of the handling of open and closed
assumptions, may be interpreted as referring to the N-systems as described
here, but are also compatible with CDC. In the latter case, however, Gentzen's
marking of discharged assumptions would be redundant. On the other hand,
Gentzen's examples are all compatible with CDC.
   Subsection 2.1.10 improves the discussion of Troelstra [1999, p. 99], where
the system N3 is misstated; N1 as defined here is the correct version.
  In Curry [1950,1963] natural deduction is treated in the same manner as
done by Gentzen. For classical systems he considers several formulations,
taking as his basic one the intuitionistic system with a rule already considered
by Gentzen:
                                       1-1,4
                                        A
However, in the absence of negation Curry includes for the classical systems
the Peirce rule P:
                                     [A -4 gu
                                         D
                                         _A p,u
                                         A
Beth [1962b,1962a] also considers natural deduction for C with the Peirce
rule. Our Nm, Ni and Nc coincide with the systems for M, I and C in
Prawitz [1965] respectively, except that Prawitz adopts CDC as his standard
convention. The more liberal convention concerning the closure of open as-
sumptions is also described by Prawitz, but actually used by him only in his
discussion of the normalization for a natural deduction system for the modal
logic S4.
2.5. Notes                                                                    57

  Many different presentation styles for systems of natural deduction are
considered in the literature. For example, Ja6kowski [1934] and Smullyan
[1965,1966] present the proofs in linear style, with nested "boxes"; when a
new assumption is introduced, all formulas derived under that assumption
are placed in a rectangular box, which is closed when the assumption is dis-
charged. See also Prawitz [1965, appendix C].
  Although natural deduction systems were not the exclusive discovery of
Gentzen, they certainly became widely known and used as a result of Gentzen
[1935]. However, we have reserved the name "Gentzen system" for the cal-
culi with léft- and right-introduction rules (discussed in the next chapter),
since not only are they exclusively due to Gentzen, but it was also for these
formalisms, not for the N-systems, that Gentzen formulated a basic meta-
mathematical result, namely cut elimination. The words used by Gentzen
in the preamble to Gentzen [1935] indicate that he had something like nor-
malization for NJ, but not for NK; however, he did not present his proof for
NJ.


2.5.3. Hilbert systems. Kleene [1952a] uses the term "Hilbert-type system";
this was apparently suggested by Gentzen [1935], who speaks of "einem dem
Hilbertschen Formalismus angeglichenen Kalkiil". Papers and books such
as Hilbert [1926,1928], Hilbert and Ackermann [1928], Hilbert and Bernays
[1934] have made such formalisms widely known, but they date from long
before Hilbert; already Frege [1879] introduced a formalism of this kind (if
one disregards the enormous notational differences). We have simplified the
term "Hilbert-type system" to "Hilbert system". There is one aspect in which
our system differs from the systems used by Hilbert and Frege: they stated
the axioms, not as schemas, but with proposition variables and/or relation
variables for A, B, C, and added a substitution rule. As far as we know, von
Neumann [1927] was the first to use axiom schemas. Extensive historical
notes may be found in Church [1956, section 29].
   Many different Hilbert systems for I and C appear in the literature. Our
systems are fairly close to the formalisms used in Kleene [1952a]. The axioms
for implication in exercise 2.4.2D are the ones adopted by Hilbert [1928].
  Kolmogorov [1925] gave a Hilbert system for minimal logic for the fragment
      -4, V, 3. The name "minimal calculus" (German: Minimalkalkül) or
 "minimal logic" was coined by Johansson [1937], who was the first to give a
formalization w.r.t. all operators in the form of a Gentzen system.
   Glivenko [1929] contains a partial axiomatization for the intuitionistic logic
of     A, V,   The first (Hilbert-type) axiomatization for the full system I is
in Heyting [1930a,1930b]. Heyting [1930b] attempts unsuccessfully to use a
formal substitution operator, and makes an incompletely realized attempt to
take "partial terms" into account, i.e. terms which need not always denote
something. Heyting's propositional rule "If A, B, then A A B" was shown to
58                                         Chapter 2. N-systerns and H-systerns

be redundant by Bernays (see his letter to Heyting, reproduced in Troelstra
[1990]). Bernays also considered the problem of formalizing intuitionistic
logic, and noted that a suitable formalism could be obtained by dropping
         A from Hilbert's formalism, but these results were not published.
  The deduction theorem, which is crucial to our proof of equivalence of nat-
ural deduction and Hilbert systems, was discovered several times indepen-
dently. The first published proof appears to be the one by Herbrand [1930]
(already announced in Herbrand [1928]). Tarski [1956, p.32, footnote] claims
earlier, unpublished discovery in 1921. For more historical information see
Curry [1963, p.249].

2.5.4. Rule of detachment. Interesting variants of Hilbert systems for propo-
sitional logics are systems based on the so-called Condensed Detachment rule
(CD). These systems are based on axioms and the rule

                                   A*B         C
                              CD
                                   cd(A    B,C)
where cd(A        B, C) is defined as follows. Let PV(F) be the set of proposi-
tional variables in F. If A and C have a common substitution instance, let
D = Acri = Co-2 (cri, a-2 substitutions defined on (part of) the propositional
variables of A and C respectively) be a most general common substitution
instance such that Pv(D) n (Pv(B) Pv(A)) = 0; then take cd(A B, C)
to be Bcri. (There is an algorithm for finding a most general common substi-
tution instance, namely the unification algorithm discussed in 7.2.11, where
    is treated as a binary function constant.) It can be shown that, for exam-
ple, -4-M is complete for the system based on the axioms obtained from the
schemas k, s (1.3.9) and b, c, w (2.1.8C) by choosing distinct propositional
variables P,Q,R for A, B, C, plus the rule CD. For more information on this
see Hindley and Meredith [1990], Hindley [1997, chapter 6].

2.5.5. Negative translation. See Kolmogorov [1925], Gödel [1933b], Gentzen
[1933a], Kuroda [1951]. More on the negative translation and its variants,
as well as stronger conservativity results for C relative to I and M, may be
found in Troelstra and van Dalen [1988, section 2.3].

2.5.6. Formulas-as-types. For intuitionistic implication logic, the idea is
clearly present in Curry and Feys [1958, sections 9EF]; in embryonic form
already in Curry [1942, p. 60, footnote 28]; the first hint is perhaps found
in Curry [1934, p. 588]. The idea was not elaborated and/or exploited by
Curry, possibly for the following two reasons: the parallel presents itself less
forcefully in the setting of type-assignment systems than in the case of type
theories with rigid typing, and, related to this, the parallel did not seem
2.5. Notes                                                                 59

relevant to the problems Curry was working on. In any case it is a fact that
the parallel is not even mentioned in Curry [1963].
   In Howard [1980] (informally circulating since 1969), the parallel is made
explicit for all the logical operators (with some credit to P. Martin-L5f). N.
G. de Bruijn has been developing a language AUTOMATH for the writing
and checking of mathematical proofs since 1967; he independently arrived at
formulas-as-types to deal with logic in his language. The logical community
at large became only slowly aware of this work. There is now an excellent
account in Nederpelt et al. [1994], with an introduction and reproduction
of the more important papers on AUTOMATH, many of which had not been
widely accessible before.
