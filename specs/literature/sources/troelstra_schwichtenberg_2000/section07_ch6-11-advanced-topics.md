# Basic Proof Theory — Chapters 6-11: Normalization, Resolution, Categorical Logic, Modal/Linear, Second-Order (lines 8269-19042)

Chapter 6

Normalization for natural deduction

We now embark on a more thorough study of natural deduction, normaliza-
tion and the structure of normal derivations. We describe a simple normal-
ization strategy w.r.t. a specific set of conversions which transforms every
deduction in Ni into a deduction in normal form; moreover, for 1\im we
prove that deductions are in fact strongly normalizable, i.e. every sequence of
normalization steps terminates in a normal deduction, which is in fact unique.
   As in the case of cut elimination, there is a hyperexponential upper bound
on the rate of growth under normalization. From a suitable example we
also easily obtain a hyperexponential lower bound. This still leaves open
the possibility that each theorem might have at least some cutfree deduction
of "modest" length; but this possibility is excluded by an example, due to
Orevkov, of a sequence of statements Cn, n E IN, with deductions linearly
bounded by n, for which the minimum depth of arbitrary normal proofs has
a hyperexponential lower bound.
  This points to the very important role of indirect proof in mathematical
reasoning: without indirect reasoning, exemplified by non-normal proofs, we
cannot present proofs of manageable size for the C.


6.1      Conversions and normalization
In this and the next section we shall study the process of normalization for
Ni, which corresponds to cut elimination for intuitionistic sequent calculi.
  We shall assume, unless stated otherwise, that applications of          have
atomic conclusions in the deductions we consider.
  As mentioned already in section 1.3.4, normalizations aim at removing local
mwdma of complexity, i.e. formula occurrences which are first introduced and
immediately afterwards eliminated. However, an introduced formula may be
used as a minor premise of an application of VE or 3E, then stay the same
throughout a sequence of applications of these rules, being eliminated at
the end. This also constitutes a local maximum, which we should like to
eliminate; for that we need the so-called permutation conversions. First we
                                     178
6.1. Conversions and normalization                                            179

give a precise definition.

6.1.1. NOTATION. In order to be able to generalize conveniently later on,
we introduce the term del-rule (from "disjunction-elimination-like"): the del-
rules of N[mic] are ]E, VE.                                                  El


6.1.2. DEFINITION. A segment (of length n) in a deduction D of Ni is a
sequence A1,   , An of consecutive occurrences of a formula A in D such

that
      for 1 < n, i < n, Ai is a minor premise of a del-rule application in D,
      with conclusion Ai+1,
      An is not a minor premise of a del-rule application,
      A1 is not the conclusion of a del-rule application.
(Note: An f.o. which is neither a minor premise nor the conclusion of an
application of VE or 3E always belongs to a segment of length 1.) A segment
is maximal, or a cut (segment) if An is the major premise of an E-rule, and
either n > 1, or n = 1 and A1        An is the conclusion of an I-rule. The
cutrank cr(o-) of a maximal segment a with formula A is l AI. The cutrank
cr(D) of a deduction D is the maximum of the cutranks of cuts in D. If there
is no cut, the cutrank of D is zero. A critical cut of D is a cut of maximal
cutrank among all cuts in D. We shall use o, o' for segments.
  We shall say that o- is a subformula of a' if the formula A in o is a subformula
of B in o-'. A deduction without critical cuts is said to be normal.             N

REMARK. The obvious notion for a cut segment of length greater than 1
which comes to mind stipulates that the first formula occurrence of the seg-
ment must be the conclusion of an I-rule; but it turns out we can handle
our more general notion of cut in our normalization process without extra
effort. Note that a formula occurrence can belong to more than one segment
of length greater than 1, due to the ramifications in VE-applications.

6.1.3. EXAMPLE.
                                               Bw
                                              AVB            Cw'
                      Au
                    AV B        B V Cv     (a) (AVB)VC (a1) (AVB)VC
                                                                         w, w'
   AV(BVC)      (v) (AVB)VC                   (b) (AVB)VC
                                                            u, v
                         (c) (AVB)VC
In this deduction (a),(b),(c) and (a!),(b),(c) mark segments of length 3, and
 (131),(c) a segment of length 2. We are now going to define the various con-
version steps we shall consider for the calculus Ni.
180                                            Chapter 6. Normalization for natural deduction

6.1.4. Detour conversions
We first show how to remove cuts of length 1. We write "cony" for "converts
to".
A-conversion:
           D1   D2
           A1   A2                        Di
                            COI1V                    for i E {1, 2}.
           A1 A A2                        Ai
                Ai

V-conversion:



                            CD2cony
                              CVi
                           [AO         [A2r
              Ai           Di                                          [Ai]   for i E {1, 2}.
           Ai V A2                            u, V


>-conversion:
               [A]u

                           T,1         cony
           A          Bu    A

V-conversion:

                A                         D[xlt]
                            cony
          VyA[x/y]                        A[x It]
           A[x I t]

2-conversion:
              D             [A]u
            A[y/t]          y/
                                         cony
           2xA[ylx]          C
                                 u


6.1.5. Permutation, conversions
In order to remove cuts of length > 1, we permute E-rules upwards over minor
premises of VE, 2E.
V-perm conversion:
      D         D1V2                                                            Vi              D2
      VB        C      C                              cony                       C       D'     C    D'
            C                Dl
                                     E-rule
                                                                   AVB               D
6.1. Conversions and normalization                                              181

s-perm conversion:
                     D'                                          D'
            3xA      C                            conv      V    C        7,"
                            Du                             3xA        D
                                 E-rule


6.1.6. Simplification conversions
Applications of VE with major premise A1VA2, where at least one of [Al], [A2]
is empty in the deduction of the first or second minor premise, are redundant;
we accordingly introduce simplifying conversions. Similarly, an application
of 3E with major premise 3xA, where the assumption class [A[x/y]] in the
derivation of the minor premise is empty, is redundant. Redundant applica-
tions of VE or 3E can be removed by the following conversions:
           D         Di    D2
                                                    Di
        Ai V A2      C      C        COI1V



where no assumptions are discharged by VE in Di, and
                D'                   D'
        3xA     C         cony

where no assumptions of TY are discharged at the final rule application.
The simplification for VE introduces a non-deterministic element if both dis-
charged assumption classes [Ai] are empty.

6.1.7. Term notation. In term notation the conversions take the following
compact form:

        PiP(to, t1) conv t (i E {0, 1}),
        E01 (kit, to , t1) cony ti[ui/t],
        (AuA.t)sA cony t[u/s],
        (Ax.t)s conv t[x/s],
        E3uy (p(t, s), t') conv tqu, y/t, s];

        f[E(t, to, ti)] cony            (t, f [t o] f [t
        f [E,4 (t, s)] cony        (t, f [s]) ;


        Euvoui (t, to, t1) cony ti (lij not free in ti),
        Eu3y(t, t') conv t' (u, y not free in t').
182                              Chapter 6. Normalization for natural deduction

The first group expresses the detour conversions, the second group the per-
mutation conversions and the third group the simplification conversions. In
the second group, f is another elimination operator, with [] the argument
corresponding to the main premise.

REMARK. The detour conversions are sometimes simply called 0-conver-
sions, after the typical case of -4-detour conversions.
   Notationally, there is something to be said for reserving a special type (say
"I") for individuals; VI then gives a term Axi .t : VxA.
   The notion of a normal deduction can be defined very compactly, indepen-
dently of the definition of cut segments as redexes, by stipulating that in a
normal deduction each major premise of an E-rule is either an assumption or
a conclusion of an application of an E-rule different from the del-rules.

6.1.8. THEOREM. (Normalization) Each derivation 7, in Ni reduces to a
normal derivation.
PROOF. In applications of E-rules we always assume that the major premise
is to the left of the minor premise(s), if there are any minor premises. We
use a main induction on the cutrank n of D, with a subinduction on m, the
sum of lengths of all critical cuts (= cut segments) in D.
   By a suitable choice of the critical cut to which we apply a conversion we
can achieve that either n decreases (and we can appeal to the main induction
hypothesis), or that n remains constant but m decreases (and we can appeal
to the subinduction hypothesis). Let us call a a t. c.c. (top critical cut) in D
if no critical cut occurs in a branch of 7, above u. Now apply a conversion
to the rightmost t.c.c. of D; then the resulting D' has a lower cutrank (if the
segment treated has length 1, and is the only maximal segment in D), or has
the same cutrank, but a lower value for in.
   To see this in the case of an implication conversion, suppose we apply a
conversion to the rightmost t.c.c. consisting of a formula occurrence A -4 B
                          [A]                       2y/
                           D'                       [A]
                           B      V"      c onv
                        A+B        A
                                                    D'

Then the repeated substitution of V" at each f.o. of [A] cannot increase the
value of m, since 7, does not contain a t.c.c. cut in V" above the minor premise
A of >E (such a cut would have to occur to the right of A > B, contrary to
our assumption). We leave it to the reader to verify the other cases.

REMARK. If we use the term notation for deductions, our strategy may be
described by saying that we look for the rightmost redex of maximal degree
not containing another redex of maximal degree.
6.1. Conversions and normalization                                           183

  It is worth noting that this strategy also produces normal deductions if
we assume that our deductions obey the Complete Discharge Convention (cf.
2.1.9).

6.1.8A. 4 Do the remaining cases of the proof of the theorem.

6.1.8B. 4 If we permit in Ni non-atomic applications of _Li, a local maximum
of complexity may arise if the conclusion of _Li is the major premise of an elim-
ination rule. Devise extra conversions to remove such maxima and extend the
normalization theorem.

6.1.9. REMARK. The term notation also suggests the possibility of a more
general concept of conversion, namely (restricting attention to --+Nm)
          (Aiy.t)gr convo (Àdt[y/r])§..
We call this generalized beta-conversion (0-conversion). Consideration of
this conversion has advantages when computing bounds on the number of
reduction steps needed to reach normal form. For this more general notion
of conversion, essentially the same strategy leads to normal forms (see 6.10).
  It is worth noting that the following theorem holds:

6.1.10. THEOREM. Deductions in Ni are strongly normalizing w.r.t. the
conversions listed, that is all reduction sequences terminate (every strategy
produces normal forms).
  We do not prove this for the full system here; for references, see 6.12.2.
The important case of -4-logic will be treated in section 6.8, with some ex-
tensions indicated in the exercises. Strong normalization also holds w.r.t.
0-conversion, by essentially the same method. See also section 8.3.

6.1.11. REMARK. The system Nc is not as well-behaved w.r.t. to normaliza-
tion as Ni. In particular, no obvious "formulas-as-types" parallel is available.
Nevertheless, as shown by Prawitz, a form of normalization for Nc w.r.t. the
1_AN-language is possible, by observing that le for this language may be
restricted to instances with atomic conclusions. For example, the left tree
below may be transformed into the tree on the right hand side:
                                          (B *C)'     B

                         C)]u                            1_
                                                          + C)] u
                  B
                      I Cu
                                                              w v
                                                     B        C
184                                 Chapter 6. Normalization for natural deduction

6.1.11A. 4 Extend normalization to _LA V-Nc. Hint. Use the preceding remark
and the result of exercise 2.3.6A (Prawitz [1965]).


6.2      The structure of normal derivations
6.2.1. Normal deductions in implication logic
By way of introduction, let us first consider the structure of normal derivations
in *Nm. Let D be a normal derivation in                         A sequence of f.o.'s
A0,      , An such that (1) Ao is a top formula (leaf) of the prooftree, and (2)
for 0 < i < n, Ai+1 is immediately below Ai, and (3) A, is not the minor
premise of an *E-application, is called a track of the deduction tree D. A
track of order 0 ends in the conclusion of D; a track of order n + 1 ends in
the minor premise of an +E-application with major premise belonging to a
track of order n.
   Since by normality E-rules cannot have the conclusion of an +I-application
as their major premise, the E-rules have to precede the I-rules in a track, so the
following is obvious: a track may be divided into an E-part, say A0,            ,

a minimal formula Ai, and an I-part A2+1,            , An. In the E-part all rules are
E-rules; in the I-part all rules are I-rules; A, is the conclusion of an E-rule and,
if i < n, a premise of an I-rule. It is also easy to see that each f.o. of D belongs
to some track. Tracks are pieces of branches of the tree with successive f.o.'s
in the subformula relationship: either Ai+1 is a subformula of Ai or vice versa.
As a result, all formulas in a track Ao,       , An are subformulas of Ao or of An;

and from this, by induction on the order of tracks, we see that every formula
in D is a subformula either of an open assumption or of the conclusion.
                                                  The tree to the left illustrates the
                                                  structure of a normal derivation
                                                  in *Nm. A dotted line connects
                                                a minor premise of *E with its
                                                conclusion; a solid line connects a
                                                (major) premise with the conclu-
                                                sion. The parts of branches made
                                                up of solid lines are the tracks; the
                                                unramified parts are always the I-
                                                part of a track. The tree shown
                                                has tracks of order 0-2. The only
                                                track of order 2 consists of three
                                                nodes.
The notion of track and the analysis given can readily be extended to -4AVI-
Ni. In the WI-fragment there is always a unique track of order 0, but as
soon as A is added to the language, there may be several tracks of order 0 in
a normal derivation.
6.2. The structure of normal derivations                                      185

  However, if we want to generalize this type of analysis to the full system, we
encounter a difficulty with the rules VE, E. The conclusion of an application
of VE or AE is not necessarily a subformula of the major premise. Hence
restricting attention to pieces of branches of the prooftree does not lead to a
satisfactory analysis of the form of normal deductions. The subformulas of a
major premise A V B or AxA of an E-rule application do not appear in the
conclusion, but among the assumptions being discharged by the application.
This suggests the definition of track below.
  The general notion of a track has been devised so as to retain the subformula
property in case one passes through the major premise of an application of a
del-rule. In a track, when arriving at an Ai which is the major premise of an
application a of a del-rule, we take for Ai+1 a hypothesis discharged by a.

6.2.2. DEFINITION. A track of a derivation 1, is a sequence of f.o.'s A0,     ,   An
such that
  (i) Ao is a top f.o. in 1, not discharged by an application of del-rule;
 (ii) A, for i <n is not the minor premise of an instance of +E, and either
             Ai is not the major premise of an instanee of a del-rule and J1.2+1
             is directly below Ai, or
             Ai is the major premise of an instance a of a del-rule and Ai+1 is
             an assumption discharged by a;
 (iii) An is either
             the minor premise of an instance of >E, or
             the conclusion of T,, or
             the major premise of an instance a of a del-rule in case there are
             no assumptions discharged by a.

6.2.3. EXAMPLE. Consider the following derivation:

                                        Vxy(Pxy     Pyx)wi
                                         Vy(Puy      Pyu)
                                            Puv     Pvu VE        Puy° --+E
                             Puy°                      Pvu AI
            Vx3yPxy w                   Puv A Pvu
                        VE                             3I
             3yPuy                      y( uy A Pyu)
                                                       2E w"
                     3y(Puy A Pyu)
                    Vx3y(Pxy A Pyx)
             Vxy(Pxy Pyx)    Vx3y(Pxy A Pyx) -4/
                                                               -41w
186                                   Chapter 6. Normalization for natural deduction

The diagram below represents the tree structure of the derivation, with the
rules and discharged assumption classes as labels. For easy reference we have
also given a number to each node.
                       11w'
                       12 VE

                       13 VE         10w"

              3w"             14 +E
                                                  All nodes are numbered; top
      1w               4A1                        nodes have a variable as assump-
      2 VE             521                        tion label; below the top nodes
                                                  the rule applied is indicated, plus
              62E                                 the label of the discharged as-
                                                  sumption class where applicable.
              7 VI

             8 *I w'                              Tracks: 1-9;
                                                  11-14, 4-9;
             9 *I w                               1, 2, 10.

REMARK. To a deduction D we can associate a labelled tree (D), by induc-
tion on VI, as follows. The labels are formulas, and each node in 7, labelled
with a formula A corresponds to a set of nodes labelled with A in (V). (It
is sometimes convenient to think of the labels in (D) as also containing the
rule used to obtain the formula in the label, and if applicable, the discharged
assumption classes.)
      If D ends with an f.o. A which is the conclusion of a rule R {VE, 3E},
with deductions Di of the premises Ai, then (V) is obtained by putting A
below the disjoint union of the partially ordered (Di);
      If D terminates with a VE, i.e. D ends with
                                         [A]u     [B]v
                                Do          Di.   D2
                               AVE          C      Cu,u

then we insert a copy of (D0) above each formula occurrence in (D1) and (7,2)
corresponding to the occurrences in assumption classes labelled u, v. Below
the resulting disjoint trees we place an occurrence of C. (The notion of cor-
responding occurrence is the obvious one.) Similarly if the final rule applied
in D is 3E. This second clause (b) is the reason that several occurrences of
B in (D) may correspond to a single occurrence B in D. Thus the prooftree
above yields a labelled tree with skeleton indicated below (the numbers are
copied from the numbering of the corresponding occurrences in D.)
61 The structure of normal derivations                                       187

                      11      1   The tracks correspond in this tree to
                                  branches starting at a leaf and terminating
             1        12      2   either in a minor premise of an --+E or in
                      1




                      13     10   the conclusion. If we do not insist on hav-
                              /
             2


                 \/
                                  ing trees, we can also have partial orders as-
             3             14     sociated to prooftrees such that the formula
                                  occurrences of the prooftree are in bijective
                 4
                                  correspondence with occurrences of the same
                 51               formulas in the associated labelled partial or-
                                  der; in the second clause (b) of the descrip-
                 6
                                  tion we then stipulate that a single copy of
                 71               (7,0) is above all occurrences in the classes
                                  labelled w and w' in the ordering of (D). In
                 8                the tree to the left this ordering would be
                 9
                                  obtained by identifying nodes with the same
                                  label (1 and 2 each occur twice).

6.2.4. PROPOSITION. Let D be a normal derivation in I, and let ir
uo,   , 0-7, be a track in D. Then there is a segment o-i in ir, the minimum
segment or minimum part of the track, which separates two (possibly empty)
parts of 7, called the E-part (elimination part) and the I-part (introduction
part) of ir such that:

     for each a in the E-part one has j < i, a is a major premise of an
     E-rule, and cri+i is a strictly positive part of o- and therefore each
     is an s.p.p. of ao;
     for each cri in the I-part one has i < j, and if j n, then cri is a premise
     of an I-rule and an s.p.p. of ci+i, so each a is an s.p.p. of an;
      if i n, o-i is a premise of an I-rule or a premise of _Li (and then of the
      form 1) and is an s.p.p. of o-0.

6.2.5. DEFINITION. A track of order 0, or main track, in a normal derivation
is a track ending in a conclusion of D. A track of order n + 1 is a track ending
in the minor premise of an +E-application, with major premise belonging to
a track of order n.
   A main branch of a derivation is a branch ir in the prooftree such that ir
passes only through premises of I-rules and major premises of E-rules, and ir
begins at a top node and ends in the conclusion of the deduction.        .




   If we do not include simplifications among our conversions, a track of order
0 ends either in the conclusion of the whole deduction or in the major premise
of an application of a del-rule, provided the classes of assumptions discharged
by the application are empty.
188                               Chapter 6. Normalization for natural deduction

REMARK. If we search for a main branch going upwards from the conclusion,
the branch to be followed is unique as long as we do not encounter an AI-
application.

6.2.6. PROPOSITION. In a normal derivation each formula occurrence be-
longs to some track.
PROOF. By induction on the height of normal deductions. For example,
suppose D ends with an VE-application:

                                      [Adu    [A2]v
                            D1         7,2     D3
                          A1 V A1       C       C IL, V


C in D2 belongs to a track ir (induction hypothesis); either this does not start
in [A1]u, and then ir, C is a track in D which ends in the conclusion; or ir
starts in [A1]u, and then there is a track 7r' in D1 (induction hypothesis) such
that        C is a track in D ending in the conclusion. The other cases are left
to the reader.

REMARK. In the case discussed in the proof, we can explicitly describe all
tracks of D, they are of the following four types:

      tracks of order > O in D1, or tracks of order > 0 in Di+1 not beginning
      in [Ai], or

      of the form iri, 72 with 7r1 a track of order 0 in D1 and ir2 a track of
      order > 0 in Di+1 beginning in [Ai], or

      of the form 7r1, 7r2, C with ri is a track of order O in 7,1, 1-2 a track of
      order 0 in Di+i beginning in [Ai], or

      of the form 7ri, C, with 7ri is a track of order 0 in Di+i not beginning in
      [Ai].


6.2.7. THEOREM. (Subformula property) Let D be a normal deduction in I
for r h A. Then each formula in D is a subformula of a formula in I' U {A}.

PROOF. We prove this for tracks of order n, by induction on n.

6.2.7A. 4 Give full details of the proof of the subformula property.
6.3. Normality in G-systerns and N-systerns                                      189

6.2.7B. * For 1AN-Nc (cf. 6.1.11) the following subformula property holds: if
D derives A from r, and D is normal with atomic instances of I, only, then every
formula in D is either a subformula of A, r or the negation of an atomic formula
in A, r. Prove this fact (Prawitz [1965]).

6.2.7C. 4 Prove the separation theorem for >Iic (cf. 4.9.2) via the following
steps.
      If A is an implication formula derivable in He, it is derivable, say by a
deduction D, in LLNc with Ii, I, restricted to atomic conclusions.
       Replace in D the instances of I, by uses of PQ, j_, where Pxy is Peirce's
Law, i.e., ((X > Y)    X) > X, and where Q E PV. The result is a derivation D'
in >iNi of A from PQ,,± (1 < i < n) with Qi E PV.
       Let Pi, , Pm be the conclusions of instances of _Li occurring in D', and let
B A P. Replace I everywhere by B; by interpolating some steps, the instances
of       are transformed into a sequence of AE-applications. The result is a proof V"
in ANm from assumptions Pc?,13 (1 < i < n).
          Use exercise 2.1.8G to transform this into a derivation of A from PQ,,p,
(1 < i < n, 1 < j < m). By the subformula property for Nm, this reduces to
a normal deduction in 1Tm; from this we readily construct a proof in Hm plus
assumptions PQ,,pi, hence a proof in He.

6.2.7D. 4 Prove the following proposition. Let D be a deduction of A in Ni
without open assumptions, which is normal w.r.t. detour conversions. If A is not
atomic, D ends with an I-rule. Hence if Ni I- A V B, it follows that either Ni I- A
or Ni I-- B (Prawitz [1965]). Hint. Consider a main branch in D.

6.2.7E. 4 Prove theorems 4.2.3, 4.2.4 using normalization instead of cut elimi-
nation (Prawitz [1965]).


6.3         Normality in G-systems and N-systems
This section is not needed in the remainder of this chapter and may be
skipped. In this section we study the relationship between normal natu-
ral deductions and cutfree G-proofs. We first present a simple construction
of G-proofs from normal N-proofs; this motivates the study of the class of
so-called normal cutfree G-proofs.
   As noted before (3.3.4), several cutfree G-deductions may correspond to
a single normal N-deduction. However, by imposing the extra condition of
normality plus some less crucial conditions, we can achieve, for the right choice
of G-system, a one-to-one correspondence between normal Ni-deductions and
normal G-deductions. For our G-system we choose a term-labelled version of
GKi.
190                              Chapter 6. Normalization for natural deduction

6.3.1. Constructing normal cutfree G-proofs from normal N-proofs. As a
preliminary warming-up for the more precise results later in the section, we
describe first a simple construction of cutfree G-proofs from normal proofs
in Ni. The argument takes no account of assumption markers, and applies
therefore also to Ni under CDC. On the other hand, the construction is largely
insensitive to the precise G-system for which we want cutfree deductions.
Below we present the argument for Gli; for other systems small adaptations
are necessary.
   Let us write HG F    D if G1i r D, and r FN D if there is a normal
natural deduction proof of D from assumptions in F.


THEOREM. FG r          D iff r HN D.

PROOF. We show by induction on the depth of normal N-deductions that if
F HN D, then HG F       D.
 Case I. Suppose that 7, consists of the assumption A; this is translated as
the axiom A      A.
 Case 2. Let 1, be a normal derivation for F FN D, and suppose that the
final step in D is an I-rule application. Let C be the deduction(s) in the
sequent calculus corresponding by induction hypothesis to the immediate
subdeduction(s) of D; apply to C the corresponding R-rule. For example,
if D ends with

                                       [A]



                                       A+B
we have by induction hypothesis a deduction showing HG 1", A      B (use
weakening on the conclusion of C to introduce A on the left if necessary,
hence by R--+ we have G1il-FA> B.
 Case 3. The conclusion of D is the result of an E-rule application, or of _Li.
We note beforehand, that if a main branch ending with an E-rule contains an
application a of VE or 3E, then a is the sole application of one of these rules
and moreover it is the final rule applied in the main branch; for suppose not,
then D is not normal, since in this case the uppermost occurrence /3 (which
may, or may not coincide with a) of an application of VE or 3E is followed
by an E-rule, and it is possible to apply a permutation conversion.
  Let r be the main branch of D. r is unique, since the I-part of T is empty
(multiple main branches can only occur as a result of AI). T does not contain
a minor premise, hence no assumption can be discharged along r.
  Thus the first f.o. C of T belongs to I' and is a major premise of an E-rule.
Suppose e.g. C C1 > C2. Then D has the form
6.3. Normality in G-systerns and N-systerns                                             191

                                                        D'
                                       C1C2 C2          Ci
                                            (C2)
                                             Du
                                                A
where (C2) refers to a single occurrence in V". The f.o. C1 cannot depend on
other assumptions besides the ones on which A depends, since no assumptions
are discharged in T, which passes through the f.o. C2.
  Thus, if 7, establishes F, C1 --* C2 HN A, then TY establishes F HN C1, and
V" shows F, C2 Im A. By the induction hypothesis,
                       I-G. r         Ci,             F-G F, C2       A.

ana therefore by +L:
                                 HG C1 --+ C2, r              A.
To consider yet another subcase, suppose now that C                        Ci V C2. Then 1,
has the form
                                            [Cdu         [C2]v
                                                7,1       D2
                            CI. V C2            A            A u, V
                                            A
deriving A from C1 V C2, F. Then
                                [C1]                          [C2]
                                7,1         and               7,2
                                 A                             A
are correct normal derivations of smaller depth and therefore by the induction
hypothesis
                     hG r, Ci     A,       1--G r, C2   A
Then the VL rule gives us a deduction showing E-G r, C1 V C2                        A. The
other cases are left to the reader.                                                      Z

REMARK. If we adapt the argument to the construction of proofs in G3i,
then either we have to generalize the axioms to F, A     A for arbitrary A, or
we must in the basis case use standard proofs of the axioms for compound A.
  The argument also yields a quick proof of the subformula property for
normal deductions, requiring a partial analysis of their structure only: the
cutfree Gentzen proof constructed contains formulas from the original N-
deduction only, and for Gentzen proofs the subformula property is immediate.

6.3.1A.* Let D be a normal deduction in Ni, and let G(D) be the corresponding
deduction in GKi constructed in the proof of the theorem above. Then 1G(D)1 <
192                                        Chapter 6. Normalization for natural deduction

6.3.1B. 4 Show that for deductions in G3i + Cut or GKi + Cut (with atomic
A in L_L) we can find a normal proof N(D) in Ni such that IN(D)1 < c2IDI for a
positive integer c. For the full system we can take c = 2, for the system without 1
it suffices to take c =1 (cf. 3.3.4B).

6.3.2. If we analyse the construction in the proof of the preceding theo-
rem, we discover that we do not obtain arbitrary cutfree proofs, but in fact
proofs satisfying an extra property: whenever we encounter an application of
L*, LA or LV, the antecedent active formula in (one of) the premise(s) is
itself principal. We call deductions obeying this condition normal deductions.
The question rises, whether there is perhaps a one-to-one correspondence be-
tween normal natural deductions and normal cutfree G-proofs? Before we
can answer this quewstion however, we first have to be more precise as to
the systems' we want to compare. For the N-systems the choice is canonical:
standard Ni, which is isomorphic to a calculus of typed terms. On the side
of the G-systems, we choose a term-labelled version of GKi.

6.3.3. NOTATION. Below we use u, y for deduction variables (with formula
type), x, y for individual variables. If we wish to emphasize that a term is a
deduction term, we use d, e.

6.3.4. DEFINITION. The system t-GKi with term labels is given by the
following rules (i = 0,1).

   Ax 1         P       u: P            LI r, u: _L         EI(u): A

        r,u:A0 A Ai, v:                t(u, v): B              r       t0: A0       r
   LA
            r, u: Ao A Ai           t(u,piu): B
                                                         RA
                                                                   r     P(to,       Ao A .A.J.


               ,L10A1           s(u): A0          r, u: .i10A1, v: A1           t(u, y): B
   L_> r' u:
                               r, u: A0>A1           t(u, us(u)): B

                   A   t: B
   R> r'u:
         r      Au.t: A-4B

        F u: AoVAi,            Ao      to(u, y):C        r, u: AoVAi, w: A1             ti(u, w):C
   Lv
                          r, u: AcIVAi                (u, to(u, v), ti(u, 0): C

   RV
               r       t: Ai
        F      ki(t): Ao V Ai


   LV
        F u: VxA,        A[x            s(u,      B
                                                          RV
                                                                   r      t: A
6.3. Normality in G-systems and N-systems                                                193

             3xA(x),v: A(y)    s(u, v, y): B                 F      s: A[x t]
  LA F' u:                                          RA
        F, u: xA(x)    EL(u, s(u, y, y)): B              F         p(t, s):]xA

The variable restrictions on the rules are as usual: in RV x ;Z FV(F, VxA), in
LA x Fv(r, AxA, B).
  By dropping all the term-labels from the formulas we obtain the system
GKi.                                                                                      El


6.3.5. DEFINITION. (Normal and pruned deductions) A deduction 1, in GKi
or t-GKi is normal, if the active antecedent formula in any application of LV,
LA, L* is itself principal, and in the applications of L_L only atomic A are
used.
  A deduction 7, of r    t: A in t-GKi is said to be pruned, if all deduction
variables of F actually occur free in t. A deduction of r        A in GKi is
pruned if F is a set (a multiset where every formula has multiplicity 1) and D
cannot be written as DIF'        for inhabited F'. (The notation DIP                     wa,s
explained in 4.1.2.)                                                                      El


The restriction to atomic A in applications of L_L in the definition of normality
is needed because we had a corresponding restriction on I in Ni.
   One easily sees that every deduction in GKi of I'           A or in t-GKi of
F    t: A may be pruned to deductions of F'          A or r t: A respectively,
with I" C 1"; the original deduction is obtained from the pruned deduction by
a global weakening. The two notions of "pruned" do not fully correspond: if
we have in the antecedent of the conclusion of a pruned deduction in t-GKi
X: B, y: B, with x, y distinct, then stripping of the terms produces a deduction
in GKi with in the conclusion multiple occurrences of B in the antecedent,
so some further pruning is then needed.

DEFINITION. The system h-GKi with head formulas is specified as follows.
Sequents are of the form II; F A with III< 1. To improve readability, we
often write for an empty II.

   Ax P;         P                r    A


   LA A'i.A0AA1,FB              RA
                                      IIr      Ao        II;
       Ao A Ai;1"                           II; F    A0 A A1


   L.4 ; r' Ao-4A, A0-4,41;
                     Ao
                            r
                             Ai; F, Ao>A1
                                 B
                                                     B
                                                               R>        "' Ao
                                                                     II; I'


   LV ;      A0VAi, Ao      C     ;F,A0VA1,A1                  C
                                                                    RV
                                                                              IIr   Ai
194                                   Chapter 6. Normalization for natural deduction
        A[xI t]; I', VxA   B                       F     A
  LV                                 RV     II.'
           VxA; F        B                 II; F        VxA


  L3
        A[x/y]; r, 3xA B
                                     R3 H.'
                                               r         A[x/t]
           3xA;F B                          II; F         3xA

  D      A"r
       ; A, F     B

hi RV x FV(IIF), in L3 y 0 FV(F, 3xA, B); P atomic; and i = 0 or i = 1.
The formula in front of the semicolon, if present, is called the head formula.
The names of the rules are given as usual; "D" stands for dereliction (since
A loses its status of head formula).
   We may also formulate a combination ht-GKi in the obvious way.            El

Dropping in a deduction 7, in h-GKi the semicolons, and deleting the repe-
titions resulting from D, results in a normal deduction in GKi. Conversely,
a normal deduction in GKi can straightforwardly be transformed into a de-
duction in h-GKi. The proof that every sequent derivable in GKi also has
a normal proof may be established either by proving closure under Cut of
h-GKi, or via the correspondence, to be established below, of normal deriva-
tions in GKi with normal derivations in Ni.

6.3.6. LEMMA. (Contraction for h-GKi)
       If I-- A; r, A     B thenhr, A; r               B, and
       if I     r, A, A       B then I--       r, A         B.

6.3.7. THEOREM. (Cut elimination for h-GKi) The system with head for-
mulas is closed under the rules of Head-cut (Cuth) and Mid-cut (Cut,):
                              A;r'
      k_iuth
                    II; rr,     B
                                       B
                                                    Cut.;F n;Arri11;1',A
                                                                      B

PROOF. The proof follows the standard proof of Cut elimination for the
system GKi without term labels.

6.3.8. THEOREM. The systems GKi and h-GKi are equivalent:
                                           iff h-GKi ;            A.



PROOF. The direction from right to left is trivial, as observed before. The
other direction is proved by induction on the depth of deductions in GKi,
6.3. Normality in G-systerns and N-systems                                                            195

using closure under Cut of h-GKi. We consider a typical case. Suppose the
proof in GKi ends with
          A-413,r          A          A-4B, B,         C
                                           C
Then by the IH we have deductions in h-GKi of
          ; A-413,r            A and ;                              C.

Then we obtain a proof of ; A*B,                       C with the help of Cut as follows:
              A; A*.13           A
             ; A, A-413           A      B; A, A-413            B


 ; A*B r           A
                                     B
                               A-4.13; A
                           ; A*B , A B
                                                ; (A+B)2, A,
                                                                    ;        C
                                                                                        B,r        c Cut
                                                                                     Cut
                       ; (A-4.13)3 r2             C
where Xn is short for n copies of X. The desired conclusion follows by closure
under contraction. If A or B are not atomic, we have to insert at the top
standard deductions for A; A-4.B A or B, A+B            B respectively.     IE



6.3.9. The correspondence between pruned normal proofs in t-GKi and
normal proofs in Ni. Instead of using the conventional notation Po and pi
for the projections, we find it more convenient for the arguments below to
switch notation and to introduce two constants 0 and 1 such that pot tO,
Pit ti. Then successive application of L>, LA, LV results in a term of the
form uto    tn_i where each ti is either a deduction term or an individual term
or one of 0, 1, corresponding to L-4, LV and LA-applications respectively.
The deduction variable u is called the head-variable.

6.3.10. LEMMA. The term t in a proof in t-GKi of r                                     t: A represents a
normal natural deduction.
PROOF. We only have to check that the applications of rules cannot introduce
terms of the following form:

     13(,                                                                    Eu3,y(P(,
                                                                             )
                                                  E \v/,w(ki,

          Euvo, (( )   ,   ,     ),            ) ; ), Eu", (E,           ,       ,   Eu3a, (E, )
where the    stand for arbitrary terms or 0 or 1 (at least when this makes sense
syntactically). The different occurrences of do not necessarily represent
the same expression. The E stands for a term of the form Ez,v,,, (, ) or
E3u,y(,
  It is straightforward to carry out the check.
196                                    Chapter 6. Normalization for natural deduction

6.3.11. PROPOSITION. To a normal term t, representing a normal deduction
in Ni and deriving A from r, corresponds a unique pruned normal deduction
Di in t-GKi deriving F t: A.
PROOF. By induction on the size of t.
Case I. If t begins with an I-operator, that is to say, if t has one of the
following forms:
                        P(do,          P(s, d), Au.d, Ax.d,
then the last rule applied in t is AI, 31, *I, VI, AI, respectively, and Di ends
with a corresponding application of RA, R3, R*, RV, RA. For example, if t
ends with AI, TY has the form
                                                    Di
                             r do: Ao                d1:A1
                              r p(do,             Ao A Ai

and we can apply the Ill to do and ch.
Case 2. Case 1 does not apply. Then t has one of the following forms:
                     to,        (to,    t2), Ev3,0 (to, ti), EI (to)

where to a UE, and e is a (possibly empty) string so, si... sn_i such that each
si is either a deduction term, or an individual term, or one of 0, 1. u is called
the head-variable of t. Note that the fact that t is normal, and that case 1
does not apply, precludes that to begins with an introduction operator (i.e.,
one of p, Ax, Av, ki), or that t is of the form Etv,,,, (to, ti, t2) or Ev3,y(to, ti),
while to begins with an elimination operator.
Subcase 2a. t u or t E\v/i,(U; ti, t2) or t a EZy(u, ti) or t a- El(u). Then
TY is an axiom Ax, or ends with LV, or ends with L3, or is an axiom LI
respectively, and the Hi may be applied to ti, t2.
Subcase 2b.    If t E to or t Euv,v(to, ti, t2) or t a Ey3,y(to,t1) or t E_i(to),
and to is not a variable, then to a utie. If t a to, put e(v) ye; if t
     (to, ti, t2), let e(v)      (ve, ti, t2), and if t E EL (to, ti), put e(v) a
EL(ve, ti), and if t El(to), put e(v) Ei(ve). Then either
2b.1. t' is 0 or 1, V ends with an LA-application
         u: A0 A Ai, v: Ai, r       e(u, ve): B
              u: Ao A A1,         e(u, uie)
where i stands for 0 or 1, we may apply the IH to e(u, ve); or
2b.2. If t' is a deduction term, Dt ends with a L>-application
         u:A0>A1,r           d' Ao   u: A0>A1 v: Air               e(u , ve): B
                            u: Ao>A1, r e(u, ut'e): B
and we can apply the IH to d', e(u, ve), or
6.4. Extensions with simple rules                                              197

2b.3. If t' is an individual term, TY ends with Lb:
        u: VxA,     A[x/t/]     e(u, ve): B
             u: V x A    e(u, ut' e): B
and we can apply the IH to e(u, vE).

6.3.12. THEOREM. There is a bijective correspondence between pruned
normal deductions in t-GKi and normal deductions in Ni.
PROOF. Immediate from the preceding arguments.
In fact, there is an effective procedure for transforming a non-normal de-
duction into a normal t-GKi-deduction by permuting rules; as shown by
Schwichtenberg, even strong normalization holds for this process. See 3.7.4.
   If we relax the restriction to atomic conclusions on _Li in Ni, then we may
also relax the restriction on L_L in normal proofs.


6.4      Extensions with simple rules
The extensions considered are extensions of N[mi] with rules involving only
atomic premises, conclusions, and discharged assumptions. These extensions
are the counterpart for N-systems of the extensions of G-systems considered
in 4.5.
   We recall that we shall assume restriction of _Li to instances with atomic
conclusions throughout.

6.4.1. DEFINITION. Let N* be any system obtained from N[mi] by adding
rules Rule1(P0, P-i, Q) of Type Ia or Rulei (Po, , P71) -I-) Of Type Ib -
                  Po              Pn 1            resp.       Po          Pn


 or Rulei(Ro,      ,   Rn; Po,      Pn, (2) of Type Ic -
                                    [Rdut


                                         P.
                                                      -1,      Un


 or rules Rule2(Qi,        ,   Qm; P1,        ,   Pn) of type II
                                                  [pitti,,



                         chQm                       c        1.11   tin
198                              Chapter 6. Norrnalization for natural deduction

The Q3 are the major premises, the premises C are the minor premises. The
P2, Qi, Rk are all atomic. The formula C in rules of type II is arbitrary.
  We also require that the set of additional rules is closed under substitution
of terms for individual variables, that is if we make in premises, assumptions
and conclusion of one of the additional rules a substitution PA, then the
result is another rule of the same type.
  In these extended systems the del-rules are the rules VE, 3E and the type-II
rules.




(Qi
REMARKS. Note that addition of a rule of type II is equivalent to the addition
of an axiom
                    Qi A .. A Qv, --+ Pi V ... V Pn
or a rule
                                    A     A Q.
 *)
                                 Pi V ... V Pm
as may be easily checked by the reader.
   Combination of two rules Rulei(P, Q) and Rulei(Q, R) produces a deduc-
tion containing




This corresponds in G-systems to a basic Cut on Q. By our conventions the
occurrence of Q is not counted as a cutformula in N-systems.

6.4.2. Conversions are now extended with permutative conversions and
simplifications involving rules of type II. The notion of a maximal segment
may be defined as before with our new notion of del-rule, and we can prove
normalization.

LEMMA. Each derivation in a system Ni* can be transformed into a normal
derivation with the same conclusion.
PROOF. The proof follows the same strategy as before, namely removing a
cut of maximal complexity which is topmost in the rightmost branch of the
deduction containing such cuts.
The definition of track is as before, but with our new notion of del-rule.
6.5. E-logic and ordinary logic                                                         199

THEOREM. Let D be a normal derivation in N*, and let ir be a track in
D. Then 7r may be divided into three parts: an E-part as,., o-i_i (possibly
empty), a minimal part o-2,       , o-k, and an I-part o-k+i,   . .   , o-n (possibly empty)
such that

      for each o-3 in the E-part one has j < i, a-3 is a major premise of an
      E-rule, and o-3+1 is a strictly positive part of a-3, and therefore each o-3
      is an s.p.p. of ao,

      for each o-3 in the I-part one has k < j, and if j n, then o-3 is a premise
      of an I-rule and an s.p.p. of 0-+i, so each o-3 is an s.p.p. of an,

      for i <j < k the segment o-3 is a premise of a type-I rule or the major
      premise of a type-II rule, and for i < j < k the segment o-3 is the
      conclusion of a type-I rule or an assumption discharged by a type-II
      rule,

      if k    n, crk is also a premise of an I-rule or of J.

LEMMA. In a normal deduction in a system Ni* each f.o. belongs to a track.

THEOREM. Let D be a normal deduction of A from assumptions r in a
system Ni*. Then each formula in D is either a subformula of I', A or an
atomic formula occurring in one of the additional rules.

6.4.2A. * Check the proof of lemma and theorem.


6.5      E-logic and ordinary logic
E-logic is an adaptation of first-order predicate logic which accommodates
possibly empty domains and possible non-denoting (undefined) terms. Such
terms may arise, for example, in the theory of partial functions. This is
achieved by adding a special unary predicate E, the existence predicate. Et
means "t denotes" or "t is defined".
   Two notions of equality play a role: strict equality =, where t = s means
that t and s are both defined and equal, and weak equality       s t means that
s is defined iff t is defined, and if one of these is defined, they are equal. In
this section we want to compare a version of E-logic with modified quantifier
rules with ordinary logic with some special axioms for E added.
   This section makes use of the results of the preceding section on extensions
of N-systems.
200                                          Chapter 6. Normalization for natural deduction

6.5.1. DEFINMON. Let Nie be the system obtained from Ni by adding a
special unary predicate E, and modifying the quantifier rules of Ni as follows:
                                [Ey]u
                                                                 Do        D1
                             A[x I y]                       VE
                                                                 Vx A      Et
                        VI                                            At
                                VxA

                                                                 [A[x I yfiu [Ey]v
                        Do          D1
                    A[x It]         Et                    Do
                           ]xA                         3E 3xA              Cu

with the usual variable restrictions.
  Nie is obtained from Nie by adding a predicate                        for weak equality with
axioms:

          (al) t           t,
                    s   t A A(s)       A(t) (A atomic),
                    (Es V Et        s t)      s    t,
                    E(f ti . . ti,) --+ Et, (1 < i < n),
                                .



                    Rti .t + Et, (1 < i < n)
(R a relation symbol, f a function symbol of the language). The correspond-
ing theory is designated by Te.
  NiE is obtained from Ni by adding a unary predicate E and equality =,
with extra axioms and rules
                                 Et          At     t=s
                                                           (A atomic)
                                t=t               As
                   Rti tn         to = t1     E(ft1 tn)
                      Eti           Eti            Eti
where j E {0, 1}, 1 < i < n, R is a predicate letter and f a function symbol
of the language. The last three rules are called the strictness rules.

6.5.2. DEFINITION. We define the following map from formulas of Nie" to
formulas of NiE:
          (Et)E                     := Et,

          (to       ti)E            := Eto V Eti > to = ti,
          (Rta .t_1)E := Rto
                .
                                tn-17
          (A o B)E     := AE o BE for o
          (V x A)E     := Vx[Ex     AE],
          (2xA)E       := x[Ex A AE].                                                       N
6.5. E-logic and ordinary logic                                                  201

6.5.3. DEFINITION. Let .us call a formula of NiE bounded if all quantified
subformulas of A are of the form Vx(Ex     B) or ]x(Ex A Bx). We define
a mapping * from the bounded formulas of NiE to the formulas of Nie as
follows:'
            (Et)*                 := Et,
            (-L)*                 =1,
            (s = t)*              :=stAEsAEt,
            (Rto           := Rto   tn-i,
            (A o B)*       := A* o B* for o E {A, V, -±},
            (Vx(Ex   A))* :=VxA*,
            (3x(Ex A A))* := 3xA*.                                                   E

6.5.4. LEMMA. Nie" I- A 44 (AE)*.
PROOF. By induction on the complexity of A. The most interesting case is
that of prime formulas to = ti:
            ((to = ti)E)*            (Eto V Eti   to = ti)*
                                     Eto V Eti ---> (toti A Eto A Eti)
                                     (EtoVEti + to t1) A (EtovEt,        EtonEti).
The first half of this conjunction is by axiom (a3) equivalent to to          t1, and
the second part is derivable from to ti with the help of (a2).

6.5.5. LEMMA. If Nie"                 F        A, then NiE   FE    AE.

PROOF. By induction on the depth of proofs in Nie". The more interesting
cases concern the axioms. Let us consider the axiom
            s       t A A[x I s] > A[x I t],

for A atomic. For example, let A                  r   r'. Assume
            A[x I s]E  Er[x I .9] V ErlxI si > r[x I si= rqx I s],
            (s    t)E  Es V Et --+ s = t,
            Er[x/t] V Erlx It].
We have to show r[xlt]= ri[xlt]. Because of the strictness of function sym-
bols, if x actually occurs in r, Er[xlt] V ErIxIt] implies Et. With the second
assumption this yields s = t and Es. By induction on the complexity of r"
one proves for all r":
            s = t ---> r"[x I .5]= r"[xlt],

hence in particular r[x I s] = r[xlt], ri[x I = rqx It], and so by strictness
Er[xI s] V Erqx Isi. Therefore r[x I s] = rqx I 3] (first assumption), so r[xlt]=
lxIt]. The rest of the proof is left to the reader.                             E
202                                   Chapter 6. Normalization for natural deduction

6.5.6. LEMMA. Let F, A consist of bounded formulas. If NiE                     r   A then
        F*     A*.

PROOF. By induction on the IDI, where D is a normal proof of r          A in
NiE, we construct a proof D* of r*        A*. Let us consider the four cases
where the last rule R applied in 7, is a quantifier rule. Observe that due to
the subformula property for normal deductions, quantifiers appear only as
the restricted quantifiers of bounded formulas.
Case I. R = VI. The conclusion of D is of the form Vx(Ex + Ax), and the
conclusion and its premise belong to the I-part of the track to which they
belong, so 7, is of the form shown on the left below. By the IH applied to Do
there exists a deduction D* as shown on the right.
                           [Ex]u                           [Ex]'
                             Do
                        Ex -4 Axu                          A* x
                      Vx(Ex + Ax)                         V xA* x

Case 2. R = I. Then for similar reasons 1, must be of the form on the left
below, while by the IH we can then construct D* as on the right below:
                               pl
                        Et     At
                                                          Et    A*t
                        Et A At
                      3x(Ex A Ax)                          3xA*x

 Case 3. R = VE. Then D is of the form on the left, and we construct, using
the 1H, a deduction as on the right:

                        Do
                  Vx(Ex > Ax)                         VxA*x Et'
                                                         A*t
                      Et > At                             Et -4 A*t
 Case 4. R = E. Then D is of the form on the left, and we construct, using
the IH, a deduction as on the right:
                                                                   Exu     A*xv
                               [Ex A Ax?
                                                                    [Ex A A*x]
                 Do
             3x(Ex A Ax)              C
                                          u          3xA*x               C* u, v
                                                               C*
All other cases are trivial.                                                           N

The following is now immediate by combining the preceding lemmas.

6.5.7. THEOREM. Nie               r       A iffNiE   rE
6.6. Conservativity of predicative classes                                   203

6.5.7A. 4 Complete the proof of lemma 6.5.5.


6.6       Conservativity of predicative classes
6.6.1. We shall now give a proof-theoretic argument for the conservativity
of the addition of predicative classes to intuitionistic first-order theories, as
an application of normalization for natural deduction systems. This is an-
other type of extension of the logical N-systems: we now add second-order
quantifiers, and need a different argument to extend normalization.
   Let T be a first-order theory formalized on the basis of intuitionistic pred-
icate logic, plus some (individual) first-order axioms and a set of axiom
schemas
  Let L be the language of T; we add n-argument predicate variables XI',
   Z' (i E      tO L, the extended language we call L'.
  An axiom schema ..Ti is a formula in the language L', say
          yi(xin(i,1),   xrn((:),r(i))),

where Xi is n(i, j)-ary. Each substitution of predicates of suitable arity de-
finable in T, say
          xl . . .       (xi    , xn(i,i)) (1 <j _< r(i)),
for the X7(ij) yields an axiom of T.

6.6.2. DEFINITION. The weak second-order extension T* (extension by
predicative classes) of T is defined as follows. We add to the language of
T relation variables X", Yn, Z',... for n-ary relations, for each n, and the
corresponding quantifiers VXn, 3Xn. If t1,     , in are individual terms, then
Xnti tn is a prime formula. We add the elementary comprehension schema:
ECA       aXnVxi    xn[Xn(xi, , xn)      A(xi, ,xn)]
for each A of T* not containing bound relation variables. The axiom schemas
   of T are replaced by corresponding axioms


EXAMPLE.        Let HA be the system of intuitionistic first-order arithmetic,
also called Heyting arithmetic, containing symbols for all primitive recursive
functions, with as axioms the equality axioms as in 4.4.3, Vx(0         Sx) (S
successor function), Vxy(Sx = Sy > x = y), defining axioms for all primitive
recursive functions, and all instances of induction: A[x/0] A Vx(A > A[xlSx])
   VxA. The weak second-order extension HA* is defined as indicated above,
with extra axioms VXxy(x = y A Xx            Xy), and the induction schema is
replaced by the induction axiom VX(X0 A Vn(Xn > X (Sn)) -4 VmXm).
For weak second-order extensions we have the following theorem:
204                              Chapter 6. Normalization for natural deduction

6.6.3. THEOREM. T* is a conservative extension of T.
PROOF. We make use of a mild extension of the normalization theorem for
Ni. The axiom schema ECA can be dispensed with at the cost of introducing
second-order quantifier rules of the following forms:
       A[Xn lYn]                     VXn A        .,,
                 V2
         VXnA                     A[Xn1A.B]vw2I

                                             [A[Xn I YIP'

       A[Xn     Y.B]               ]XnA           C     2E
                       321
           ]XnA

Here A[Xn/Axi      xn..13] is the formula obtained from A by replacing each
prime formula of the form Xnt1t2      tn by B[xi,...,xniti,...,t7d
  In V2I, Yn does not occur in assumptions on which the formula occurrence
A(Y) depends; in 32E Yn does not occur free in assumptions on which C
depends, except A[Xn /Yn], nor does Yn occur free in C. B does not contain
bound predicate variables.
  To the conversions we add conversions for the second-order quantifiers, and
permutative conversions for 32E (and if desired simplifications as well).
  The 2-complexity c2 (A) of A is the number of second-order quantifiers in
A. The 2-cutrank of D, cr2(D), is the maximum of the 2-complexities of
formulas in maximal segments. The 1-cutrank of D, crl(D), is the maximum
of IA for all cutformulas with c2(A) = cr2(D). A critical cut is a maximal
segment o- with A E o- and I AI = crl(D), c2(A) = cr2(D). The cutlength of
D, cl(D) is the total number of cutformulas A in critical cuts.
  A t.c.c. (topmost critical cut) is now defined as before. The notion of
subformula is extended by stipulating that A(Aai xn.B) is a subformula of
VXnA(Xn), 3XnA(Xn), for any B not containing bound relation variables.
With this notion of subformula we prove normalization and give an analysis
of the structure of tracks as before, and obtain the subformula property. The
normalization proof uses a nested induction: a main induction on cr2(D),
with a subinduction on crl(D), and a sub-subinduction on cl(D). At each
reduction stej either cr2(D) is lowered, or crl(D) is lowered and cr2(D) stays
the same, or cl(D) is lowered and cri(D) and cr2(D) stay the same.
   Alternatively, one may describe this as an induction on the lexicograph-
ically ordered triples (cr2 (D), crl (D), cl(D)). The induction hypothesis is
then that for all D' with (cr2(D'), crl(D'), cl(V)) < (cr2(D), crl(D), cl(D))
the transformation into a normal deduction has already been achieved.
  Now let A be a formula in the language of T such that T* I A, and let D
be a normal derivation in T* with conclusion A. By the subformula property
6.7. Conservativity for Horn clauses                                                205

all formulas in 1, are subformulas either of A, or of axioms of T*. Each
second-order axiom can only occur at a top node and it cannot appear as
subformula of another formula occurring in D; therefore it occurs as the first
formula of a track followed by V2E-applications, until a first-order formula has
been reached; this first-order formula is then an instance of an axiom schema
in T.                                                                                IE


REMARK. For a reader familiar with ordinals and transfinite induction, the
argument may be described more simply: give formulas A a complexity IAl2
= w . cr2 (A) + IA I, and give deductions D an induction value win+ n, with m
the maximal complexity of formulas in cut segments of D, n the total length
of critical cut segments. Each reduction step then lowers the induction value,
which is an ordinal below w3.

6.6.3A. 4 Let V2E', 321' be the versions of V2E, 321 where for B only a relation
variable may appear. Show that V2E', 321 plus ECA is equivalent to V2E, 321
relative to the other axioms and rules. What would go wrong in the proof of the
theorem if B were completely unrestricted?


6.7         Conservativity for Horn clauses
The results in this section will be used in a proof of the completeness of a gen-
eralization of linear resolution. Throughout his section we restrict attention
to the language without V, 3.

6.7.1. DEFINITION. An expansion of a deduction D in Nm consists in the
replacement of a subdeduction D' by another subdeduction according to one
of the following three rules:
                                              D'
(1)         Di       is replaced by       A -4 B AY            (y not free in D')
        A    ->B                                           y
                                                 A -4B B
                                        TY

(2)     D'         is replaced by
                                       VxA
                                                    (y not free in TY)
        VxA                           A[x I y]
                                       VxA

                                             D'         D'
(3)                 is replaced by       AAB AAB
        A TY
          AB                                 A             B
                                                  AAB
In term notation the expansions correspond to replacing, respectively,
206                                 Chapter 6. Normalization for natural deduction

         tA-4B by MLA .tA-÷B u (u % FV(t)),

      tVxA by Ay.tvxAy (y % FV(t)),

      tAAB by P(Pot, Pit).                                                     El

Cases (1) and (2) are often called 77-expansions; this term is sometimes ex-
tended to case (3). The term "expansion" has been chosen since the inverse
replacements (right hand side replaced by left hand side) are usually called
in the terminology of the A-calculus contractions; in particular the inverses of
(1) and (2) are called 77-contractions (in this book we have used "conversion"
instead of "contraction" however).
   Expansions may create new redexes. Therefore we want to allow them only
in positions where no new redexes are created. We define:

6.7.2. DEFINITION. (Minimal position, long normal form) A formula oc-
currence A is said to be in end position in a deduction D, if A is either the
conclusion of D, or the minor premise of an application of +E. A formula
occurrence A is said to be in minimal position, if either

      A is the conclusion of an E-rule application and a premise of an I-rule
      application or
      A is in end position and the conclusion of an E-rule application.

A deduction is in long normal form if 7, is in normal form and no expansions
at minimal positions are possible.                                         El



REMARKS.      (i) The expansion of an occurrence at a minimal position of a
normal deduction does not create new redexes. Clearly, the minimal part of
a path in a deduction in long normal form always consists of a single atomic
formula. In order to construct, starting from a given deduction, a deduction
in long normal form with the same conclusion, we first normalize, then apply
expansions.
   (ii) A deduction in long normal form is comparable to a sequent calculus
deduction with the axioms I', A   A, A or A    A restricted to atomic A. The
construction of a deduction in -->Nm from a deduction in a Gentzen system,
with atomic instances of the axioms only, as in 3.3 produces a deduction in
long normal form. Conversely, the construction in 6.3 produces a deduction
with atomic instances of the axioms from a deduction in long normal form.

6.7.3.     LEMMA. Let D be a normal deduction.           There is a terminating
sequence of expansions transforming D into a deduction in long normal form.
    6.7. Conservativity for Horn clauses                                                  207

    PROOF. Let ed(D), the expansion degree, of 1, be the sum of the sizes of
    formulas in minimal position. Assume T:t to be normal. Now search for
    an occurrence A of a compound formula in minimal position, such that no
    formula occurrence of this kind occurs above A. Then an expansion of 7, at
    A decreases the expansion degree of the deduction.

    REMARKS.       (i) The depth of the long normal form 1,' of 1, constructed ac-
    cording to the recipe above is at most 31D11-
       (ii) the transition to long normal form corresponds in Gentzen systems to
    the replacement of axioms with non-atomic active formulas by deductions of
    these axioms from axioms with atomic active formulas (cf. 3.1.3A).

    6.7.4. DEFINITION. A generalized Horn formula is a formula of the form
                                  Vi(A° A ... A An_i --+ B)
    where B is atomic and A0,     , An_i are formulas without -4. A generalized
    Horn formula is called definite if B is atomic, not equal to I. If the Ai are
    atomic, we have Horn formulas, definite Horn formulas respectively. A fact
    is a Horn formula with n = 0, that is to say, a fact is of the form VIB.    El


    6.7.5. THEOREM.
           Let Nc H r        1, where r is a set of generalized Horn formulas. Then
           Nm r          1, by a deduction not involving
           Let Nc H r B, where B is atomic, and r is a set of definite general-
           ized Horn formulas. Then Nm r B, by a deduction not involving

           If we drop the "generalized" from the preceding two statements, the
           deduction in Nm may be assumed to contain applications of AI and
           E-rules only.
    PROOF. Given Nc r         1, there is by theorem 2.3.6 a deduction in Nm
    of r, A  1, where A is a set of stability assumptions V(---R i --+ Rg). By
    lemma 6.7.3 we may assume 7, to be in long normal form.
       Closure of assumptions in an Nm-deduction 7, in long normal form of
    r, A A, r a set of generalized Horn formulas, A a set of stability assump-
    tions, A -4-free, can only occur in subdeductions of the following form (the
    double line stands for 0 or more VE-applications):


                                              Rg)
                                        -> Rt_>E
    (1)
                                                    VE
                                                             _L
                                                                  >Lu
                                                 Rt
PDF compression, OCR, web optimization using a watermarked evaluation copy of CVISION PDFCompressor
208                              Chapter 6. Normalization for natural deduction

This fact can be proved by induction on the size of deductions D. Every
formula occurrence in 7, belongs to a main branch or to a subdeduction
ending in a minor premise of >E. A main branch must start in a generalized
Horn formula or in a stability assumption. We note that along the main
branch no +I can occur.
  If the main branch started in a generalized Horn formula, we can apply
the IH to the subdeductions of minor premises (which are implication-free)
of >E along the main branch.
  If the main branch started in a stability assumption, the minor premises of
+E-applications along the main branch are of the form ,---,Rrfor R a relation
symbol of the language. In this case, the subdeduction of the minor premise
must end with an q, since the whole deduction is in long normal form. Now
note that the subdeduction D' of I (as in the prooftree exhibited above)
again may be seen as a deduction of an atomic formula from generalized Horn
formulas, since --,RE is itself a special case of a generalized Horn formula. So
we can apply the IH to D'.
  Next we observe that in the subdeductions D' as above, the assumption
u : --,Rr necessarily appears as the major premise of an instance of *E.
Occurrence as the minor premise of an instance of *E is excluded since it
would conflict with the long normal form. Occurrence as premise of an I-rule
is excluded since this would lead to subformulas of a form not present in the
conclusion and assumptions of the deduction. Hence the elements of Hliflu
appear in a subdeduction of the form
                                            7.,"
(2)                                         Rr
                                        I
                                    --,Rr

 Case 1. Assume there are closed assumptions; then we may look for a sub-
deduction of type (2) in which a closed assumption --Rrappears such that D"
does not contain closed assumptions. Then we may replace the corresponding
subdeduction of type (1) by D" and we have removed an application of a
stability assumption. This may be continued till we arrive at
 Case 2. There are no assumptions closed by *I. If there are no stability
assumptions used, we are done. If there are still stability assumptions, we
look for a subdeduction of type (1) such that D' does not contain stability
assumptions. Then the whole deduction D may be replaced by D'.
   Part (ii) of the theorem for B distinct from 1 is proved in a quite similar
way, but now in case 2 the situation that a subdeduction without stability as-
sumptions' might derive J_ is excluded (conflict with the subformula property
of normal deductions).                                                      E

REMARK. As follows from the preceding result, if r is a set of definite Horn
formulas, the deduction 7, of 1 or an atom from r is something like (double
lines indicating possibly some VE-inferences)
6.7. Conservativity for Horn clauses                                            209

                                       V11   V12                          V21   V22
                       H11             Cu1   C12                          C21   C22
                 Cn A C12 -+           CH A C12         C21 A C22 -* C2   C21 A C22
     Hl                        Cl                                   C2
Ci A C2     C                                Ci A C2

Here Hl, H11, 1112 are definite Horn formulas which in the prooftree above
have been assumed to have the form VY(Ai A A2 --+ B). The formulas C1 A
C2     C etc. are substitution instances of the clauses obtained by repeatedly
applying VE. Vn, V12 V211 V22 are deductions of the same general shape as
the whole D. If some of the Horn formulas are facts, the structure of D is
correspondingly simplified at those places.
   A simplified presentation of such a deduction is an implication tree. The
notion of an implication tree for a formula relative to a set of Horn formulas
F is defined inductively by
     a substitution instance C' of a fact V-iC from r is in itself a single-node
     implication tree for C';
     if A1 A...A An    B (n > 0) is a substitution instance of a Horn formula
     of r, and the Di are implication trees for the Ai, then
                                       D1          pn

      is an implication tree for B.
  The fact that the implication trees give a notion of derivation which is
complete for derivations of atoms from Horn formulas I' is also very easily
proved by the following semantical argument, due to R. Stark.
  We construct a model M for r, such that (1) the domain of M is the
set of all (open or closed) terms of the language; (2) function symbols f are
interpreted by functions 1M given by fm(r):. f(E); and (3) relations R are
interpreted by relations RA4 such that Rio (r) holds in M iff R(E) has an
implication tree.
  Then M is a model for P. If VgB E r is a fact, then every substitution
instance of B' of this fact is in itself an implication tree and hence valid in
M; hence the fact itself is valid in M. If A1 A ... A An --> B is a substitution
instance of an arbitrary H E r, and A1, , An are true in M, then they have
implication trees, but then also B has an implication tree, and so is true in
M; therefore H is true in M.
  If now an atomic A semantically follows from r, then A holds in M, and
hence has an implication tree. Note that this gives us a semantical proof of
the conservativeness of Nc over Nm for formulas of the form A              B (B
atomic), since an implication tree obviously corresponds to a deduction in
minimal logic.
210                                Chapter 6. Normalization for natural deduction

6.8      Strong normalization for -41\IM and A,
Strong normalization is a useful property to have: suppose we have a mapping
0 from a term system S to a term system S' such that a reduction step in S
translates under 0 into one or more reduction steps in S'. Then from strong
normalization for S' we may infer strong normalization for S. Normalization
as a rule is not enough for such a transfer, unless we can indicate for S a
strategy which translates under 0 into a strategy for normalizing in S'. In
preparation for strong normalization of intuitionistic second-order logic, we
prove strong normalization for intuitionistic implication logic.

6.8.1. DEFINITION. SN(t) := t is strongly normalizing.
   A term t is non-introduced if t is not of the form Ax.s. More generally, in
term calculi a term t is non-introduced if the principal operator of t is not an
operator corresponding to an introduction rule for the type of t.
   So if conjunction is added to the type-forming operations, and pairing with
inverses to the constant terms, non-introduced terms are the terms not of
the form Ax.s or pts. In the present case, we might also have used the term
non-abstract for non-introduced.

6.8.2. DEFINITION. For each formula A we define by induction on the depth
of A a "computability" predicate of type A, CompA, applicable to terms of
type A, as follows:

        Compx(t) := SN(t) (X a propositional variable),
        CompA,B(t) := Vs(CompA(s)            CompB(ts)).

6.8.3. LEMMA. The following three properties hold for CompA:r.

 Cl If CompA(t), then SN(t).
 C2 If CompA(t) and t       t', then CompA(t1).
 C3 If t is non-introduced, then        it CompA(e) implies CompA(t).
As a corollary of C3:

 C4 If t is non-introduced and normal, then CompA(t).
PROOF. We establish C1-3 simultaneously by induction on IA I.
Basis. A X. Cl, C2 are immediate. As to C3, for a non-introduced t such
that Vti*t CompA(e), any reduction path starting from t passes through a
t'   t, t' E SN by Cl, so t E SN.
Induction step. A B        C.
6.8. Strong normalization                                                    211

 Cl. Suppose t E CompB,c, and let x be a variable of type B. By C4, as a
consequence of C3 for B, we have x E CompB, hence tx E Compc. Clearly
the reduction tree of t is embedded in the reduction tree for tx, hence SN(t),
since SN(tx) by Cl for C.
 C2. Let t E COMN3c, e t, 5 E CompB. Then ts E COMpc, ts es, so
Compc(es) by C2 for C; s is arbitrary, so t' E COMpgc.
 CS. Let t be non-introduced, and assume Ve        t(CompB,c(e)). Let s E
CompB, then by induction hypothesis SN(s); let h, be the number of nodes
in the reduction tree. We prove ts E Comp with a subinduction on h,. If
ts    t", then either

      t"  e s, t       t'; by assumption for B        C, ComPBc(e), hence
      Compc (t/ s); or

      t"     ,s     s'; by C2 CompB(s/), and he < h,, so by the subinduction
      hypothesis for s',    E CoMpc.

There are no other possibilities, since t is non-introduced; therefore, using
C3 for ts, we find that ts E Compc. This holds for all s E CompB so
t E CompBc.

6.8.4. LEMMA. VS E CompA(CompB(t[x/s])) implies CompA,B(Ax.t).
PROOF. Assume VsECompA(t[x/s] E CompB); we have to show (Ax.t)s E
CompB for all s E CompA. We use induction on h, ht, the sum of the
sizes of the reduction trees of s and t. (Note that ht is well-defined since our
assumptions imply CompB(t), using CompA(x) for variable x, and by Cl of
the preceding lemma SN(t).) (Ax.t)s is non-introduced; if (Ax.t)8        t", then
either

      t"     (Ax.t)s' with s      s', then by C2 s' E Comp and by induction
      hypothesis t" E CompB follows; or

      t"    (Ax.e)s with t   t', then by C2 t' E Comp and by induction
      hypothesis t" E CompB; or

      t" -a t[x / s], and CompB(t") holds by assumption.

Now apply C3.

6.8.5. THEOREM. All terms of A, are strongly computable under substitu-
tion, that is to say if FV(t) C {xi: Ai, , xn: An}, si E Compit (1 < i < n),
t: B then

           CompB(t[xi,      ,x./si,
212                              Chapter 6. Normalization for natural deduction

As a corollary, all terms are computable and therefore strongly normalizable.

PROOF. By induction on the construction of t. Let r* r[xi, , x,,/s1, ,sn]
                                                             .



for all terms r.
Case I. t is a variable: immediate.
Case 2. t      t1t2, Then t*   t74; by induction hypothesis ComPA-4s(tn,
CompA(t;). Then CompB(t*) by definition of ComPA-4s
Case 3. t        AyB.tiC. Let FV(ti) C fy, xi:Ai,   ,xn:Anl, s E ComPB,
si E CompiL Then by induction hypothesis, ti[Y, xi,     , X,/S, s1, ,S,] E
Compc, i.e. tl[y/s] E Compc. By the preceding lemma Ay.tI E ComPB-ci2
We now immediately obtain

6.8.6. THEOREM. All terms of A, (deductions of -4Nm) are strongly nor-
malizable under 0-reduction.
Uniqueness of normal form is either proved directly, or readily follows from
Newman's lemma (1.2.8). Strong normalizability for CL, may be proved
by the same method as used above for A,, or can be reduced to strong
normalization for A, by the obvious embedding of terms of CL, into A,
(cf. the next subsection).

6.8.7. As a simple example of a reduction of strong normalization for a
system of terms S to strong normalization for S' via a mapping of terms
which translates a one-step reduction in S into one or more reduction steps
in S', we take for S the term calculus Av,, and for S' the calculus A,. The
reduction map     is defined on formulas as follows:

        O(Rti     tn) := R* (R* E PV),
         '(A   B)     :=     -4 OB,
        0(VxA)        := (Q -4 Q) -4 A (Q E 'PV distinct from the R*).
R* is a propositional variable assigned to the relation letter R. We extend
to deductions by assigning to a singleton tree "A" the singleton tree "OA",
and extending the definition of as a homomorphism relative to VI, VE, i.e.
          [A]                        [OA]



       A -4 B -41                i,b(A -4 B)
etc. For VI, VE we translate


          A     VI
       VyA[x/y]
6.8. Strong norrnalization                                                      213


         VxA                         (Q-4Q)--0A Q-4Q _+E
        A[x / t]


Checking that this has the desired effect we leave as an exercise.

6.8.7A. 4 Show that the embedding '0 just defined has the required properties
for reducing strong normalization for      to strong normalization for A. The
embedding has the property that if F      A is provable, then so is '0(F) 0(A).
This property is not needed for the reduction; show that 7,/, may be somewhat
simplified if this property is not required.

6.8.7B. 4 Assuming strong normalization for             show how to obtain strong
normalization for A_4ovv3.


6.8.7C. 4* Extend the proof of strong normalization via computability to AA,
the term calculus for intuitionistic +A-logic, putting

         ComPAAB := ComPA(Pot) and ComPB (pit).

The new detour-conversions are of course pi(p(to, ti)) cont t (i = 0,1). Show
that lemma 6.8.3 extends to this case, and prove an extra lemma: if t E CompA,
s E CompB, then pts E CompAAB; then prove the strong normalization theorem.

6.8.7D. * Extend the uniqueness of normal form (modulo the renaming of bound
variables) to the full calculus Ni, relative to detour- and permutative conversions.
Including simplification conversions may spoil uniqueness of normal form; why?


6.8.8. Failure of strong normalization under CDC
The following example, due to R. Statman, shows that strong normalization
fails for natural deduction under the CDC. Let Do(P, Q) be the deduction


                                        Q       Q-413 Q
                             p              Q       P
                         Q


and let Dn+i(Q , P) be


                                   + Q Dri(P,Q)
    214                                     Chapter 6. Normalization for natural deduction

    Note that Dn(P, Q) has conclusion P.
     Let P2n P, Q2n Q, P2n+1 Q, Q2n+1                               P. Dn(P, Q) has the form

                                                 Q                       Q
                                 p          P         Q
                                Q+P

                                            n

    We now start with a deduction E:
                                   Do(po,ce)
                                        p0
                                     Q0 3. p0             Do (Qo, p0)
                                                     p0
    After one reduction step at the cut shown we obtain a deduction containing
    as a subdeduction:
                                  DO (P1 Ql)
                                        pi
                                     Q' *P'               vi(Q1 pl)
                                                     P1
    By induction on n we can prove that after the n-th reduction step we have
    obtained a deduction containing a subdeduction
                                 Dn(Pn ,Qn)
                                       pn             pn+1(Qn Pn)
                                  Qn
                                            pn                 Qn
                                                 pn
    where no assumption open in this subdeduction is cancelled in the remainder
    of the deduction. Applying a normalization step to the Qn         Pn shown
    produces a deduction with as subdeduction
                                                     pn
                        Dn+1(Qn Pn)             Qn        Pn    Dn+1 (Qn Pn)
                           pn     Qn                           pn
                                            Qn
    with no assumption open in this subdeduction discharged in the remainder
    of the deduction. This subdeduction is equal to
                                Dn+1(Qn, Pn)
                                  pn        Qn            Dn+2(pn Qn)
                                                  Qn
PDF compression, OCR, web optimization using a watermarked evaluation copy of CVISION PDFCompressor
6.9. Hyperexponential bounds                                             215

which may be rewritten as
                    Dn+1(pn+1, Qn+1)
                     Qn+1    pn+1
                                         Dn+2(Qn+1, Pn+1)
                                       pn+1

As a result, the sequence of reduction steps indicated produces deductions
forever increasing in size and depth.


6.9     Hyperexponential bounds
6.9.1. Hyperexponential upper bounds on the growth of deductions. It is not
difficult to estimate the growth of the depth of a deduction on normalizing,
by analogy with the result in 5.1. For deductions D in --+Nm, the cutrank
cr(D) of D is simply the maximum of IA for all cutformulas A in D.

LEMMA. Let D be a deduction in +Nm with cutrank < k. Then there is a
deduction D* --< D with cr(D) < k such that 11,1 < 21D1.
PROOF. By induction on IV; the details are left as an exercise.
From this lemma we obtain immediately

THEOREM. To each D in >lTm there is a normal D*         7, with ID*I <2)
(which is equal to hyp(2, cr(D), ID D).

6.9.1A. * Provide details of the proof of the lemma.

6.9.2. Hyperexponential lower bounds on the growth of deductions. We can
easily show, by considering a particular example, that no elementary function
(i.e. a primitive recursive function defined with recursions bounded by some
finitely iterated exponentiation) can give a universal bound on the increase
of the length of a deduction under normalization.

6.9.3. DEFINITION. Let X be a fixed proposition variable, and define the
iterated types by

        OX := X,     (k +1)X := kX > kX.
The Church numerals of type kX are defined by (cf. 1.2.20)
               := AykXAX xkX .yn(x).
        FikX

Below we shall abbreviate hkx as I.
216                                   Chapter 6. Normalization for natural deduction

Recall that, if we put
         tos := Ax.t(s(x)),
then
               o Ir(y) =fl Irn(y),                =13 .1r,        =13 irn     > 0).
The following deduction, logically trivial, represents the Church numeral        A:

                                                 f:A>A x:A
                                   PA-4A              fx:A
                   f:A-4A                    f2x: A
                                f3x: A
                            Ax. f3 x: A     A
                     3: (A       A)       (A --+ A)

Note that the deduction corresponding to TtA has depth n + 2.

6.9.4. THEOREM. We write Drd for the normal form ofD in -+Nm. There
is no fixed k such that we always have 1Dnfl < 2.
PROOF. Consider the following special deduction term r,:
                                      r2,.
         rn := In2 -142-2        =0
  The depth of the left hand side is easily seen to be n +3, while on the right
the depth is 2n + 2.
  However, a still stronger result is possible; in 6.11.1 we shall exhibit a
sequence of formulas (types) Ck with non-normal deductions of a size linear
in k, such that every normal deduction of Ck contains at least 2k nodes.
   From the theorem above plus earlier results, it follows that the "inversion-
rule strategy" of 5.1.9 cannot possibly correspond to normalization. To see
this, we observe:
       A deduction D in >1\im may be transformed into a deduction G(D) in
G3i* + Cut such that
         IG(V)I    01,
for a positive constant c, and the cutrank of G(D) is bounded by the maximum
depth of formulas in D. The proof is the same as for G3i + Cut (3.5.11C).
       For a derivation D in -+ G3i* + Cut we can find a cutfree deduction
D* with bounds on ID*1 as in 5.1.14.
     For a deduction 7, in --+G3i* Cut we can construct a translation to
a proof N(V) in >Nm such that
6.10. A stronger conversion                                                      217

(cf. 6.3.1B). Moreover, if D is cutfree, then N (V) is normal.
       Suppose that we apply (a), (b), (c) successively to the deductions rr, in
the proof of the theorem. The maximal depth of formulas in rr, is easily seen
to be n + 1, hence G(r) has cutrank at most n + 2. It is then readily seen
that I N(G(rn)*)I is bounded by 4+3 for a fixed k.
       We finally observe that the mapping N under (a) is inverse to G under
(c) in the sense that NG(D) and 7, have the same normal form. Therefore,
for sufficiently large n, the normal form of N(G(r,.,)*) cannot coincide with
the normal form of rn.


6.10 A digression: a stronger conversion
6.10.1. The following generalization of [3-conversion, already mentioned in
6.1.9, is more readily suggested by the term notation than by deduction trees:

         (Afiv.t)gr cont (Àolt[v/r])     (63-conversion).

The normal forms w.r.t. this notion of conversion however are the same as for
(3-conversion. For the purposes of illustration, let us also exhibit an instance
of this conversion in tree form:
         [Br [A]u
                                                             D2
           DO                                               [B]V [A?
          t:C                                                 Do
    Av.t:B      C      u                   cont
 Auv.t: A > (B             s: A                          t[v/r]: C    u
                                   D2
       (Auv.t)s: B --+ C          r: B               Au.t[v/r]: A > C           s: A
                 (Auv.t)sr:C                                 (Au.t[v Ir])s: C

This more general notion of reduction permits us to count the complexity of
formulas in a more economical way, namely by the notion of (implication-)
level.

DEFINITION. Let -"<gfi be the reduction relation w.r.t. this more general con-
version. A g-cut is simply a redex w.r.t. the generalized notion of conversion.
  For implication formulas A we define the level lev(A) by

         lev(P) :-= O (P atomic), lev(A      B) := max(lev(A) + 1,1ev(B)).

In a redex (AfivB .t)grB we call B the pre-cut formula. The l-rank (level-rank)
of a redex will be the level of its pre-cut formula plus 1. We write lcr(D) for
the maximum of the 1-ranks of g-cuts (redexes) in D.
  A critical 9-cut (critical redex) of a deduction D is a cut with pre-cut
formula of maximal level among all pre-cut formulas of the deduction.
218                                   Chapter 6. Normalization for natural deduction

  Suppose now we eliminate from a deduction the rightmost redex (in the
term), or equivalently a critical g-cut which is topmost on the rightmost
branch of the prooftree which contains critical g-cuts. Say the redex is
(AuP     AuvB.t)sP snA'rB Then in the result of converting: (AuP
                                  .


AuA..t[v/rDsP         s- the only increase in critical g-cuts could arise from du-
plication of r when substituted in t for v; but this is excluded since r is free
of critical g-cuts, if the original redex chosen was a rightmost redex.
   Substitution of rB in t might create new g-cuts, but necessarily of lower
level, since they will be g-cuts with pre-cut formula B1, B                B2, and
lev(Bi) < lev(B). (Observe that, if n > 0, the converted redex is again
a redex with pre-cut formula A1, but this redex was already present as a
subredex (Au].     un(Av.t)si sn) in the original redex, so this is not a new
critical redex.)
   It is to be noted that, if we restrict attention to ordinary 0-conversion, the
notion of level as a measure for the complexity of (pre-)cuts fails: consider
again our example above, and assume now that A is a pre-cut formula of
maximal level. Reduction would produce




and we have obtained a new g-cut with pre-cut formula B, which may have
the same level as A Summing up, we have

6.10.2. THEOREM. (Normalization for -- gß) There is a standard strategy
for obtaining a normal form w.r.t. gß(as described above).
Virtually the same argument as for ordinary 0-conversion yields:

6.10.3. THEOREM. All terms of A, are strongly normalizable under gfi-
reduction and hence normal forms are unique (cf. 6.8.6).
An upper bound for the number of reduction steps needed to normalize a term
according to our standard strategy, for the extended notion of conversion, is
easily given as a function of the leafsize of the prooftree.

THEOREM. (Upper bound on the number of reduction steps) Let t be a
deduction-term with ls(t) = p. Put

                     sk-Fi(P) := sk(p) + p2""(v)
6.11. Orevkov's result                                                      219

Then 8k (p) is an upper bound on the number of steps needed to lower the
g-cutrank of t by k.

PROOF. Observe that replacing (Agu'.r)gs' by (Aft.r [u7 s1),S' in t can at most
square the leafsize of Assume by III that sk(p) is an upper bound on the
                         t.


number of steps needed to lower the g-cutrank by k. The leafsize of the term
after this normalization is
        _2' k (P)

since each step at most squares the leafsize; hence we find that sk+i(p) as de-
fined above is a bound on the number of steps needed to reduce the g-cutrank
by one more.

REMARK. Replacing (Au.r)s by r[u/s] at most squares the leafsize of a       t,

special case of the observation in the proof above. However, in the case of
ordinary 0-reduction, we work with a cutrank which is in general higher than
the g-cutrank.


6.11       Orevkov's result
6.11.1. We present an example, due to V.P. Orevkov, of formulas Ck such
that each Ck has a non-normal natural deduction of size linear in k, while on
the other hand every normal derivation of Ck has at least hyp(2, k, 1) = 2k
nodes. So this is even worse than our example above, which demonstrated
that normalizing a given sequence of deductions of Ak, which are linear in k,
may produce deductions hyperexponential in k.
  The example is analogous to Gentzen's proof of transfinite induction up to
cok in arithmetic (cf. 10.2.2).
   Let R be a ternary relation symbol for the graph of the function Ayx. (y+2x),
i.e. Ryxz is supposed to express y + 2x = z. We introduce two axioms, which
are in fact Horn formulas, fixing the meaning of R, in a language with a
constant 0 for zero, and unary function symbol S for successor:
        Hypi := VyR(y, 0, Sy),
        Hyp2 := Vyxzzi(Ryxz > Rzxzi          R(y, Sx, z1)).
For Ck we take the formula expressing that hyp(2, k, 1) is defined:
        Ck := 2.4 ... Zo(R004 A ROzkzk-i A ... A ROzizo)
(Actually, our final choice will consist of variants CL of the Ck.) In the short
deductions for Ck we use formulas Ai with parameter x:
        Ao (x) :=Vy3zRyxz,
        Ai+i(x):= Vy(Aiy > 3z(Aiz A Ryxz)).
220                                      Chapter 6. Normalization for natural deduction

To grasp the intuitive significance of A, put

           fo (Yo, x)   := Yo + 2x,
           fn-H. (Yo,       Yn, Yn+i, x) := fn (YO, Y1             Yn, Yn+i      2x)
Using .1, to express "is defined" we can say that Ai+i(x) expresses

           Vyi+i (fi (yo,     ,y,         +         (Yo,       ,        40,
or

           Vyi+1.(fi(Yo,      , Yi,            fi(Yo,      ,         + 2x)-1-)

6.11.2. LEmmA. In Nm for every i Hypi --+ Hyp2 > Ai0, by a proof with
size bounded by a constant (that is to say, not depending on i).
PROOF. We have to show how to construct formal proofs E, of A,O. We leave
the cases of ea, Ei to the reader. We define abbreviations:

           Ao(x, y) := 3zRyxz,
           A1 (x, y) := Ay + Az(Aiz A Ryxz).
We construct deduction g+2:

                            Aiz A Ryxzw                        HyP2
                                                                                       VE(4x)
     Aizi A Rzxziv             Ryxz         Ryxz--Rzxzi-->R(Y,Sx, z1)
          Rzxzi                           Rzxzi>R(y, Sx, 21)
                                R(y, Sx, z1)

We construct deduction ei+2 from g+2:

                                                           Aizi A Rzxziv
                                u     Aiz A Ryxzw               Aizi       e'i+2
Ai+ix u                 Ai+ixz             Aiz                Aizi A R(y, Sx, z1)
                                                _.>E
Ai+ixy Ay u'            3z1(Aizi. A Rzxzi)                   3z(Aiz A R(y, Sx, z))
                                                                                         3E, v
3z(Aiz A Ryxz)                      3z(Aiz A R(y, Sx, z)) 3E, w
                   3z(Aiz A R(y, Sx, z))
                                              q, u'
                Aiy --> 3z(Aiz A R(y, Sx, z))                     Hypi
                                                                           VE
                          Ai+i(Sx)                             R(x, 0, Sx)
                                                                           AI
                                       Ai+i(Sx) A R(x, 0, Sx)
                                         3z(A.iz A Rx0z)
                                                              3I--q, u
                                    Ai+ix --> az(Ai+lz A Rx0z)
                                               A+20                           E
6.11. Orevkov's result                                                                            221

6.11.3. PROPOSITION.
      In Nm Hypi           Hyp2        Ck by a deduction linear in k.
      In AVI-Nm, for every k,                 Hypi + Hyp2                    by a deduction
      linear in k. Here ck is a negative version of Ck:

                         ---,Vzk...zo(ROOzk        ROzkzk_i > ROzizo                I).
PROOF. For the deductions TA of Ck from Hypi, Hyp2 we introduce some
further abbreviations.
         zk+i := 0, R1 := ROzizo,      := ROzi+izi A R (1 < i < k)
         Boz := ROziz, Biz := Ai_iz A ROzi+iz.
For 1 <i < k:
                                   B(z)                                    ek
            Bi(zi)
       :=     Aoz         Di : Ai_iziO             Ei-2
                                                            Dk+1
                                                                          Ak0
                                                                          Ak00
                                                                                           'k_1
                                               A_20                                    Ak_10
            3zBoz                                                                   3zBkz
                                          3z.B2z

              D.o
              1
                      B (zo)
                     ROzizo
                                   7,7 :=
                                              B_1 (z_1)
                                              ROzizi_i
                                                              D2-1
                                                              Rii

Finally we can construct the required deduction D;, as follows:
                                                                       [Biz]]        pro
                                                                        D1           Rk
                                                                       3zBoz         rk3I
                                                    [Bk-2(4-2)1              Ck
                                [Bk-1(4-1)]               Dk-2
                  [Bk(4)]          Dk-1                 32Bk-3Z                 k

                     Dk           aZBk-2Z                         Ck
       Dk+1       3zBk_lZ                          Ck
      3zBkz                       Ck
                    Ck
If we now apply the GödelGentzen negative translation, it is not hard to
see that deductions D in Nm are translated into deductions D' in VA>l-
Nc such that                 for a constant c, provided that the instances of
       > Ag have proofs of fixed depth. This is indeed the case, because the
only critical cases in the deductions above are the applications of 3E in but
these are applied to existential formulas, which are translated as negations,
and for which the property        -4 Ag is indeed provable with fixed depth,
by specializing the standard proof of           0. As an example consider
a deduction terminating with 3E on the left, translated as on the right:
222                                Chapter 6. Normalization for natural deduction
                                                         [Agx]


                 [Ax]                               --MyOgy
        Vi       7,2
       AxAx     3yBy                          Thzi.gx
                                             Vx--,Agx
             3yBy
                                  rnVyBgy         --1-1-1VyOgy +


Here .T is a substitution instance of the standard proof of                >
From this we see that 1,;, translates into a proof of

                 -,vzk   zo(R0Ozk A R044-1 A ... A R0,z1,z0          I).
Finally there is a deduction of C from C linear in k. (The sole reason for
replacing cif by CI', is to get rid of A, facilitating the comparison with the
next proposition.)


6.11.4. PROPOSITION. Any normal derivation in AVI-Nm of Cik from
Hypi, Hyp2 has at least hyp(2, k, 1) = 2k nodes.
PROOF. Let D be a normal derivation of 1 from Hypi, Hyp2 and the hypoth-
esis

             D :=Vzk...zo(R0Ozk    ROzkzk_i >           --+ ROzizo

Without loss of generality we may assume that there are no variables appear-
ing free anywhere in the deduction (unless bound later by VI, a case which
actually does not arise). If there are such variables, we can always replace
them everywhere by O.
  The main branch of the derivation D must begin with D, since (1) Hypi and
Hyp2 do not contain 1, and (2) the main branch ends with an elimination,
so 1 is a subformula of the top formula, which cannot be discharged along
the main branch.
  The main branch starts with a series of VE-applications, followed by --+E-
applications; all minor premises are of the form R0t13-7) (Tc abbreviates SkO, as
before).
  Any normal deduction D' of Rfitiik from Hypi, Hyp2 and D (1) actually
does not use D, (2) has at least 2n occurrences of Hypi, and (3) satisfies
k = m+ 2. (1) is readily proved by induction on the depth of the deduction,
and is left to the reader. (2) and (3) are proved by induction on ñ. For the
induction step, assume that we have shown that any normal derivation of
RrTifik uses > 2n occurrences of Hypi, and satisfies k = m + 2n. Consider a
normal derivation D' of Rrit,(Sii)k. This must be of the form
6.12. Notes                                                                  223

                          D'o
         Rthfift > (Riif-tk --+ Rfi-i(Sfl,)k)   Rthirifi   A
                     Rüñk-+Rth(Sñ)i
                                      Rfit(Sf-t)k

Application of the IH to A, A produces (2), (3) for D'.
 Returning to the derivations of the minor premises along the main branch
of the original 1,, this observation tells us that they derive R0020, R020 21,   ,

RO2k_i 2k. This uses at least 24-1 = 2k times Hypi.


REMARK. The preceding result is transferable to Gentzen systems. From a
cutfree proof Dk of Ck in G3i of depth < 2k_2 we can construct an Nm-proof
of depth < 2k_i (6.3.1B), hence of size < 2k, contradicting the proposition,
so any such Dk necessarily has depth >


6.12          Notes
6.12.1. Concepts concerning natural deduction prooftrees. The notions of
segment, branch, track, track of order n appear in Prawitz [1965], as segment,
thread, path, path of order n respectively. We have replaced thread by path,
as being the more usual terminology for trees in mathematics, and we have
replaced path by track, in order to avoid confusion with the usual notion of a
path in a tree. The notion of maximal segment used here slightly generalizes
the notion in Prawitz [1965], as in Mints [1992a] (in Prawitz [1965] a maximal
segment must be the conclusion of an I-rule). The concept of a main branch
is taken from Martin-Löf [1971a].
   Detour conversions and permutative conversions are from Prawitz [1965];
the simplification conversions from Prawitz [1971]. Prawitz has an extra
simplification conversion in the case of Ni, simplifying




to D, provided no assumptions in D become bound in D'. In Prawitz [1971, p.
254] it is also observed that a derivation in normal form may be expanded to
a derivation in what is here called long normal form.
   An example of a detour conversion is already present in Gentzen [1935]
(end of section 111.2).
224                               Chapter 6. Normalization for natural deduction

6.12.2. Normalization and its applications. The proof of the normalization
theorem follows Prawitz [1965]; this proof is in fact a straightforward exten-
sion of a very early (1942!) unpublished proof by A. M. Turing of normaliza-
tion in simply typed lambda calculus (i.e. implication logic); see Gandy [1980].
The next proof known to us is in Curry and Feys [1958, theorem 9 in section
9F], where normalization is obtained via cut elimination. For normalization
of Nc see Prawitz [1965], Smullyan [1965], Stalmarck [1991], Andou [1995]
and the references given in these papers. In the case of Andou [1995] it is
essential that is a primitive with rules        E.
  Extensions (section 6.4) with rules of type Ja are discussed in Prawitz
[1971]. There is also a brief discussion of extensions of N-systems in Negri
and von Plato [1998]; in that paper rules of type II are introduced.
  The result in 6.5, relating E-logic to ordinary logic with some special ax-
ioms, is due to Scott [1979], who gave a semantic proof, but the idea of the
present proof is due to G. R. Renardel de Lavalette (unpublished). There is
a variant of E-logic where free variables stand for "existing" objects, the do-
mains are always inhabited, but where terms need not be always defined: the
logic of partial terms (LPT), called E±-logic in Troelstra and van Dalen [1988].
  As to the conservative extension of predicative classes (6.6.3), the corre-
sponding result for classical theories is wellknown; a result of this type appears
for example in Takeuti [1978]. A similar result for a theory based on intu-
itionistic logic, namely the conservativeness of Emo r over HA, is proved in
Beeson [1985, p. 322] by means of Kripke models. The present proof is taken
from Troelstra and van Dalen [1988, chapter 10].
   Between 1965 and 1970 there appeared many proofs (cf. Troelstra [1973,
2.2.35]) of the fact that the terms of suitable term calculi for the primitive
recursive functionals of Gödel [1958] could be brought into normal form, and
hence the numerical terms evaluated. Usually these proofs implicitly estab-
lish normalization for A,. There is little or no attention given to strong
normalization; exceptions are Sanchis [1967] (for a theory with combinators)
and Howard [1970] (for lambda abstraction). But in most other cases the
proofs might have been adapted to strong normalization without difficulty.
For example, in Tait [1967], where the method using computability predi-
cates is introduced, normalization for a system of terms with combinators
and recursors is proved, but not strong normalization, although it is easy to
adapt Tait's proof to strong normalization for a system of terms with lambda
abstraction (see, for example, Troelstra [1973, section 2.2]). The proof of
Diller [1970] can also be adapted so as to obtain a proof of strong normal-
ization fqr simple type theory, etc. Strong normalization was firmly put on
the map by Prawitz [1971], who proved strong normalization for a natural-
deduction version of intuitionistic second-order logic, using Girard's extension
of Tait's method. In this text we followed the Tait method, adapted to strong
normalization.
6.12. Notes                                                                 225

  For the proof of strong normalization for the full system, see Prawitz [1971],
For an exposition, one may also look at Troelstra [1973, Chapter 4] (disregard-
ing everything which concerns arithmetic).
  Another method for proving strong normalization, by assigning suitable
functionals to terms or derivations, is introduced in Gandy [1980]. Gandy
did not treat permutative conversions; this step is taken in van de Pol and
Schwichtenberg [1995].
   A new elegant approach to proofs of normalization and strong normaliza-
tion for systems of typed terms or typable terms, especially for A2 and its
extensions, is described in Matthes [1998]. In Joachimski and Matthes [1999]
these methods are applied to a lambda calculus with sumtypes, where per-
mutative conversions are also treated; these methods obviously also apply to
strong normalization for Ni.
   The conservative extension result in 6.7.5 is taken from Schwichtenberg
[1992].
  As to the failure of strong normalization under CDC, see also Leivant [1979].
The result in 6.9.4 and the generalization of 0-conversion are taken from
Schwichtenberg [1991]. The presentation of Orevkov's result in 6.11.1 is a
slight modification of an exposition by Schwichtenberg, which in turn is an
adaptation to N-systems of Orevkov [1979]. Orevkov's result is an adaptation
of a result in Statman [1978] for languages containing function symbols. Other
papers of Orevkov dealing with bounds are Orevkov [1984,1987].

6.12.3. Comparing G-systems with N-systems. (Continued from 3.7.4.) The
natural map N from cutfree G-deductions to normal N-deductions, originally
due to Prawitz [1965], is many-to-one, not one-to-one. Prawitz also described
an inverse, Gd, assigning a cutfree G-proof to a normal N-proof; this is the
argument in 6.3.1 (Prawitz [1965, App.A §3]). The images under Gcf in fact
not only are cutfree, but satisfy some extra conditions; they are so-called
normal G-deductions, as in 6.3.5. This insight, with credit to Curry, is present
in Howard [1980, section 5] which was written in 1969.
   The precise notion of normality differs for the various G-systems, but in any
case the antecedent active formulas in applications of L-4, LA and LV have to
be principal themselves. Zucker [1974] showed that in the negative fragment
of LJ + Cut (that is to say, the fragment of > AV1) two deductions have the
same image under N, if they are interreducible using permutations of rules
and reductions of cuts. Pottinger [1977] extends Zucker's work. Mints [1996]
proves normalization of cutfree proofs by permutation of rules, sharpening
the notion of normality so as to obtain a one-to-one correspondence between
normal natural deductions and normal proofs in a system which is practically
identical with Gli (the treatment needs to be supplemented for contraction).
   Dyckhoff and Pinto [1999] prove a result similar to the result of Zucker
[1974] but for a cutfree calculus. Schwichtenberg [1999] proves strong nor-
226                               Chapter 6. Normalization for natural deduction

malization for the permutations involved. Troelstra [1999] describes a normal-
ization procedure for cutfree G3-deduction in implication logic under CDC.
   The treatment given in this book tries to avoid the complications arising
from contraction and weakening in Mints [1996] and describes the correspon-
dence between normal proofs in GKi and normal proofs in Ni, using the
G-system with privileged "headformulas" as an intermediate. The use of
headformulas is found in Herbelin [1995] and also crops up in the proof the-
ory of linear logic (cf. 9.4).

6.12.4. Generalized elimination rules. In the papers von Plato [1998], Negri
and von Plato [1999] a version of natural deduction is studied with generalized
forms of AE, *E and VE:

          [A]U[13]v                          [13]u                 A[x/t]L


 AAB         C                A    .13   A    C             VxA       C vE*,u


  The usual rules are readily seen to be special cases; for example, to obtain
the usual *E, take for the rightmost subdeduction simply the assumption
B (with B a C). The rule AE* was already considered in Schroeder-Heister
[1984].
  Let us use Ni* as an ad hoc designation for this system. (N.B. In the papers
just mentioned the assumption classes are not treated in quite the same way
as for our Ni, but we shall disregard these differences here.)
  Now all E-rules have the indirect form of VE, 3E in Ni. Extra permutation
conversions may be defined for the new extended rules.
  If we define maximal segments just as before in Ni, namely that a segment
is said to be maximal if it either is of length 1 and is the conclusion of an
I-rule and major premise of an E-rule, or is of length greater than 1 and
major premise of an E-rule, we can prove normalization as before. A normal
deduction may now be defined as a deduction where major premises of E-
rules are assumptions. For otherwise the deduction of some major premise
either ends with an I-rule, and a detour conversion is possible, or ends with
an E-rule and a permutation is possible.
   Normal deductions D in Ni* can be translated in a straightforward way
into cutfree proofs V*. Let us illustrate the idea for implication logic.
   (i) A final application of *I is translated as an application of R-4:

                       [A]'
                                                     Ty(;
                        Do        goes to      r,A
                                                     A>B
6.12. Notes                                                                  227

   (ii) A final application of -*E* with major premise an assumption is trans-
lated as an application of L--+:
                            [Br                                   D*2
                     7,1    7,2       goes to     F   A B , F'           C
              A BA                                A -+ B ,F ,F'         C
(If the major premise had been derived by, say, Do, we would have needed a
Cut to make the translation work.) Conversely, cutfree proofs in a G-system
may readily be translated into normal deductions in Ni*. The important
difference with the correlation between Ni and, say, G3i is that now the
order of the rules corresponds: the normal natural deduction is constructed
from the cutfree proof by looking at each step at the last rule applied in order
to find the last rule for the translated deduction.
   By suitably choosing the N-system on the one hand and the G-system on
the other hand one can easily obtain a one-to-one (bijective) correspondence.
   In Negri and von Plato [1999] one considers for this purpose a G-system
with context-free rules where multiple copies of the active formulas may occur
 (possibly zero); thus, for example, LA becomes
                                  Am ,   , F  C
                                  A A B,F
For the corresponding N-system, written with sequents, one has
                           F .AAB Am, Bn,r            c
                                      F    C
This leads to a smooth correspondence, which may be extended to include
Cut for the G-system and a rule of substitution for the N-system:

                          Sub
                              FA A, A C
                                   1", A    C
For the classical propositional system one may add an atomic rule of the
excluded middle,

                   EM-At    P     c
                                  F, A
                                     C
                                             C (P atomic)

which corresponds on the natural deduction side to
                                    [P]   [-'P]




Summing up, the construction of the correspondence between G-deductions
and a suitable variant of Ni*-deductions makes us understand why in the
correspondence for standard Ni (6.3) the rules LA, LV, L-+ need to be treated
differently from LV and L.
228                                          Chapter 6. Normalization for natural deduction

6.12.5. Multiple-conclusion and sequence-conclusion natural deduction. In
Shoesmith and Smiley [1978] and Ungar [1992], systems are considered where
the inferences produce finite sequences of assertions as conclusions; all for-
mulas in such a conclusion may be used as premises for other inferences,
simultaneously. That is to say a (fragment of a) proof may look like the
following:
                                         A

                                     E              FG
The deductions are therefore no longer trees.
   Technically more manageable are systems with finite multisets or sequences
of formulas as conclusions, one formula of which may be used as the active
formula in a premise of the next inference. Such systems for C are considered
in Bori6ie [1985] and Cellucci [1992]. For example, Bori6ie [1985] has the
following rules for Cp     A multisets):
              [A]x                                                              [A] x



              I;f3        x,>1           F(A       B)      AA
         P(A + B)                                FAB            +E                      x,

             FLA AA
                     FA     E                FA AB AI
                                             ro A B)
                                                                    F(Ao A A1)
                                                                          rA,           AE



                 Ai
             F(A0 V A1)
                        VI
                                     F(A V B)
                                             FAB
                                                     VEl        -
                                                                r
                                                                PA
                                                                     VV
                                                                                 FAA
                                                                                  rA
                                                                                         C

(Actually, BoriCie uses sequences instead of multisets, and hence also has a
rule of exchange.) For predicate logic C one adds
                                                                                        [Aix


         rA                 FVxA                   FA[x/t]                F2xA           B 3E
       FVxA                FA[xIt]   "              F3xA 3/

with the obvious restrictions on x in VI, E. 3E rather spoils the regular
pattern of the rules, so Cellucci [1992] considers a calculus in which 3E has
been replaced by
                                             F3xA
                                                        3 E,E
                                         FA[x/63xA]
where e3xA is an e-term in the sense of Hilbert's e-symbol (cf. Hilbert and
Bernays [1939]), i.e. a term which satisfies 3xA ++ A[x/e3xA]. For these
systems normalization with the usual consequences (subformula property etc.)
is provable.
6.12. Notes                                                                229

6.12.6. Higher-order rules. In Schroeder-Heister [1984] a generalization of
natural deduction is considered, where not only formulas may appear as hy-
potheses, but also rules; a rule of order n + 1 may contain rules of order n as
hypotheses. Ordinary rules are rules of order O.
Chapter 7

Resolution

In this chapter we study another form of inference, which forms the keystone
of logic programming and certain theorem-proving systems. We do not aim at
giving a complete introduction to the theory of logic programming; rather, we
want to show how resolution is connected with other formalisms and to pro-
vide a proof-theoretic road to the completeness theorem for SLD-resolution.
   The first three sections deal with propositional resolution, unification and
resolution in predicate logic. The last two sections illustrate for Cp and Ip
how deductions in a suitably chosen variant of the Gentzen systems can be
directly translated into deductions based on resolution, which often permits
us to lift strategies for proof search in Gentzen systems to resolution-based
systems. The extension of these methods to predicate logic is more or less
straightforward.


7.1      Introduction to resolution
Propositional linear resolution is a "baby example" of resolution methods,
which is not of much interest in itself, but may serve as an introduction to
the subject.
  We consider programs consisting of finitely many sequents (clauses) of the
form r     P, P a propositional variable and r a finite multiset of propositional
variables ("definite clauses" , "Horn clauses" or "Horn sequents"). A goal or
query r is a finite (possibly empty) set of propositional variables, and may be
identified with the sequent r       [Jis the empty goal. The so-called (linear)
resolution rule is in the propositional case just an instance of Cut:
         r, A          ¿A
                r, A
A resolution derivation consists of a sequence of such instances of Cut, where
the right premise is a rule from the given program. A successful derivation,
starting from an initial goal r, is a finite derivation tree ending in the empty
goal. Identifying a program clause 74 A          A with the formula (A A) -4 A,
                                      230
7.1. Introduction to resolution                                             231

and a goal F with A F, we see that a successful derivation derives I from
the initial goal and thus provides in fact a refutation of the initial goal on
the basis of the program clauses. In short, seen as a refutation of the initial
goal, a resolution proof is nothing but a very special type of deduction in a
Gentzen system.

7.1.1. EXAMPLE. Consider atomic propositions ST,i, Sn,W, H (for "Sum-
mer", "Sunny", "Warm", "Happy") with a program of four clauses:
        (1)    S m, W H
        (2)    Sn         W
        (3)    Sn,        W
        (4)               Sn.,

The following are examples of, respectively, a successful and an unsuccessful
derivation from this program:
            H (1)
                                                  H    (1)
              Sm, W      (4)
                                                  Sm,W    (2)
                     W           (3)                Sm, S         (4)
                         Sm             (4)
                                                             Sn
                                  [1

The derivation on the right cannot be continued since there is no clause with
Sr, on the right. The left hand derivation in our example infers H from the
assumptions embodied in the program clauses.
  From the viewpoint of classical logic, refuting --i A r is tantamount to prov-
ing A F. This suggests that it is also possible to look at a resolution proof
as an ordinary deduction of the initial goal constructed "backwards". Let a
resolution proof be given,




with n-th step
                                 rn_i    FA   A    A
                                        rn = FA
and assume that we have already constructed a derivation Dn of P*     A rn,
where P* is the multiset consisting of formulas (A I'') 4 A', one formula
occurrence for each clause F'     A from the program P. We construct a
derivation Dn_i of P*    A rn_i as follows.
   Let V, Dn" be Gentzen-system deductions constructed in a standard way
from Dn, with conclusions 2*           2*   A F respectively, and let D' be
232                                                        Chapter 7. Resolution

                                      AZXALS.AA
                  P*     AA-4i=1
                                1)*,/\AA
From this we construct Dni:

                                    Din              D'
                                               P*,AA
                   P*     Ar              P*     A
                           P*     AFAA

Another point worth noting is the following. Assume we have derived the
empty sequent (goal) from an initial goal ro and a set of program clauses P.
We may regard the program clauses as axioms. Then the generalized form
of the cut elimination theorem (cf. 4.5.1) tells us that an arbitrary classical
Gentzen system deduction can be transformed into a deduction where all cut
formulas occur in an axiom. Hence this may be read as a resolution proof;
i.e. we have obtained a completeness theorem.


7.2      Unification
The present section contains some results on substitution operations needed
in what follows.


7.2.1. NOTATION. A substitution is a mapping, say u, of variables to terms
such that the domain of u, dom(o-) = {x : o-x x}, is finite. We may
therefore represent a substitution by [xi/ti, , xn/tn], with all xi distinct,
and xi 0 ti for 1 < i < n. An equivalent notation is [x1,...,xniti, , tni
e is the identical substitution, with empty domain. In many arguments we
treat [xi/ti, , xn/tn] as a set of ordered pairs {(xi, ti), , (xn, tn)}.
   For a substitution o [xi/ti, , xn/tn], ranv(o-) := FV({ti,       , tn1). (We

do not use "ran" as the abbreviation, since this suggests the range of a func-
tion in the usual sense.) o is said to be a variable substitution if o-x is a
variable for all x.
  For an arbitrary quantifier-free expression e and substitution u, Go- is
obtained by replacing every variable in e by its cr-image. eo- is called an
instance (induced by u) of O.
  If o, T are substitutions, o-r, the composition of o and r, is the substitution
defined by

        x(o-r)= (xo-)r for all variables x.
7.2. Unification                                                            233

REMARK. Note that substitutions do not commute: [x /y][y / z] is distinct
from [y/z][x/y].
  Composition of substitutions may be defined in a more direct way by saying
that if T, a are substitutions given by

        T = [Xilti,       Xnitn]) a =        [Y1/si,   ,   Ymism],

then the substitution TO" is the sequence p found by deleting from

         [xi/tio-,    , Xnitna, Yl/S1,   ,   Ym/Smi

the xi/tio- for which tio- = xi, and the yi/s3 for which yi E {x1,   ,xn}.
  To see this, note that, for each variable x, (xo-)r is the same as xp, where
p is defined as above from a and T. (One considers three cases: x = xi,
x   {xi,    , xn,    , yml, and x = y3 but x {x1, . ,n}.)       .   .




7.2.1A. 4 Elaborate the preceding remark.

7.2.2. LEMMA. Let 0, u, T be substitutions. Then:

      u = r iff tu = tr for all terms t iff xo- = XT for all variables x;

      re = CT = r;

      (tr)o- = t(ro-) for all terms t;

      0(o-r) = (00-)r.

PROOF. (ii) is obvious, (i) and (iii) are proved by a routine induction on
terms, and (iv) is an immediate consequence of (i) and (iii).

REMARK. (iv) permits us to write Bo-r (without parentheses) for the com-
position of 9, u, r.

7.2.2A. 4 Prove (i) and (iii) of the preceding lemma.

7.2.3. DEFINMON. A variable-permutation is a substitution u with inverse
o--1 such that o-o--1 = aa = e. If e is a quantifier-free expression and a is
a variable-permutation, then 6u is called a variant of O.
  u < r iff there is a û such that u = r9. u and r are said to be equivalent
(notationar)ifa<randr<a.
234                                                        Chapter 7. Resolution

7.2.4. LEMMA. For equivalent o-,T there is a permutation 0 such that o-0 =
T, TO-1 =
PROOF. Let Cf,T be equivalent; then there are p, p' such that a = rp, T = o-p',
and hence o-p' p = u, rpp' = T. p' must be injective on A = U{FV(xo-)
x variable}, and map variables to variables, since pi p is the identity on A. It
is now easy to construct a variable-permutation O which coincides with p' on
A.


7.2.4A. 4 Complete the proof of the lemma.

7.2.5. NOTATION. We call the expression t          s an equivalence. We use
E, E', .  for finite multisets of equivalences {t1
           .   .                                      si,         sn}. The
inconsistent multiset of equivalences is

7.2.6. DEFINITION. A substitution a unifies E or a is a unifier of E, if, for
each t s in E, to- E so-. No substitution unifies {1}.
      is a relevant unifier of E, if dom(o-) C FV(E), ranv(o-) C FV(E).
      is called a most general unifier (m.g.u. for short) if a is a unifier of E,
and for every other unifier T of E we have r < u.
                                                      P,t.., , 471),(2(81, , sn)
    o- is a unifier (most general unifier) of two atoms(
if P Q and n m, and a is a unifier (most general unifier) of { t1 Fze
si,     , tm Re, sm}


REMARK. If o, a' are m.g.u.'s of an expression 0, and is t a term in 8, then
to and to-' are variants (since a = ode, a' = o-0', this follows by lemma 7.2.4).

EXAMPLE. {gx         fy} has no unifier. {gx gfy, fy         fgz} has a unifier
[x/fgz,y/gz]; this is an m.g.u., as we shall see.

7.2.7. DEFINITION. A substitution 0 is idempotent if 00 = O.

LEMMA. 0 idempotent iff dom(0) n ranv(0) = O.
PROOF. Let x E dom(0) n ranv(9), and ye = t with x E FV(t), then y(00) =
(y0)0 = te t = ye. Hence BO 0 O.
  Conversely, if dom(0) n ranv(9) = 0, then, for all variables x, FV(x0) n
dom(9) = O. Hence (x0)0 = x0; therefore by (iii) 00 = O.

7.2.8. LEMMA. Let 0 be a unifier of 0. Then 0 is an idempotent m.g.u. iff
o- = 0o- for all unifiers of 8.
PROOF. Let o be unifier of 8. Since O is an m.g.u., we have o = OT for
some substitution T. Hence a = OT = 00r (idempotency) = Bo-. The other
direction is immediate, since 0 itself is one of the u.             El
7.2. Unification                                                                                       235

7.2.9. DEFINITION. Let E >, E' be defined by the following clauses:
      f     xl u E >,{xt} U E if is not a variable; t



      {x    x}U E >,E;
      {f (81,      ,   sn)   f(t1,..., tn)}         u E > {si       ti,           , sn        U E, and
      ff (si,      , sn)     g(ti,      ,   t,n)}   u E DE {1}, if f              g;

            t,   s1R.% t1,...   ,s   Pe' tn}>[x it]
            fsi[x/t]                         sn[x/t]        tn[x/t11,   if x           FV(t), and
            t}   u E >, {_L}, if x E FV(t) and t # x.

7.2.10. LEMMA. Let E >p E'. Then
      If o- unifies E', then po- unifies E.
      If o- unifies E, then o- = po-, and o- also unifies E'.

PROOF. By case distinction according to the definition of E >p E'. The only
interesting case is the first part of (d) of the definition.
      If a' is a unifier of E', then [x/t]o-' is a unifier of E.
       Let o- be a unifier of E. Then xo- = tu, hence [x/t]o- = o- (since both
substitutions agree on all variables), and also si[x/t]o- = SO" = tu = ti[x/t]0-.
Hence u is also a unifier of E'.

7.2.11. THEOREM. (Unification) Let El be a finite multiset of equivalences.
Then a sequence E1 >pi E2 >p2 E3 . . always terminates in an En which is
                                                    .


either the empty set or the inconsistent set. In the first case, p1p2p3... pn is
an idempotent and relevant most general unifier of El; in the second case, a
most general unifier does not exist.
PROOF. (i) The sequence El, E2, E3, . . terminates. To see this, we assign to
                                                        .


a set of equivalences E a triple (ni, n2, n3) where ni is the number of variables
in E, n2 the total number of occurrences of function symbols in E, and n3 the
total number of equations of the form t = x in E, where t is not a variable.
Case (a) of the definition of r>p lowers n3, while n1, n2 remain the same; in
cases (b),(c) n2 is lowered and ni is not increased; in case (d) ni is lowered.
   If the last En+1 = 0, then by (i) of the lemma pi... pn is a unifier of El.
If û is a unifier of E1, then û =        pn0. This is proved by induction on n,
using (ii) of the preceding lemma.
   If En+1 = {I}, E is not unifiable.

EXAMPLE. If we apply the algorithm to E1 = {gx                            ;:z.1   gfy, fy      fgz},    we
obtain E1 >,{xPt; fy, f y     fgz} >, {x    fy,y                               gz} >[./fy] {y r&, gz}
       0, producing an m.g.u. [x,y/fgz,gz].
236                                                       Chapter 7. Resolution

NOTATION. We write mgu(E) for a most general unifier according to the
algorithm.

7.2.11A. 4 Decide whether the following sets of equivalences are unifiable, and
if this is the case, find an m.g.u.: {f (fx) gyz, hx f z}, {f (x,gx) f (y,y)},
If (hx,hv)      f (h(gu),h(fuw)}, {h(x,gx,y)    h(z,u,gu)} (f,g,h function sym-
bols).



7.3      Linear resolution
As in the preceding section, we have a fixed first-order language L which is
kept constant throughout the section.

7.3.1. DEFINITION. A Horn clause is a sequent of the form A1,         , An    B
with the Ai and B atomic; a definite Horn clause is a Horn °clause with B     I.
We use di, possibly sub- or superscripted, for Horn clauses. If 71 (r     B)
is a Horn clause, let 7-tv be a corresponding formula Vi(A r         B) where
   = FV (F   B).
  A definite program consists of a finite set of definite Horn clauses. We use
the letter P for programs. Pv =         : 7-t E Pl.
  A goal or query r is a finite set of atomic formulas A1, , An, Ai I; a
                                                             .

corresponding goal formula is A r       A, A ... A A. We use r, possibly sub-
or superscripted, for goals. The empty goal is denoted by [].

REMARK. If we think of r and the antecedent of a Horn clause as multisets,
the formulas A r and '1-1v are not determined uniquely, but only up to logical
equivalence. This will not affect the discussion below.
  Definite Horn clauses A1,      , An    B are in the logic programming liter-
ature usually written as B:    A1,    ,   A.

7.3.2. DEFINITION. The unrestricted resolution rule Ru derives a goal r,
from a goal r and program P via a substitution 9 (r is derived unrestrictedly
from r and P via 0) if I' a A, A, if there is a variant 71' a A'        B of a
clause 9-1 in P; û is a unifier of A and B, and r    (A, A')O. We can write

         F     71'
                     Ru, 0

or, not specifying the variant 71', we may also write

                 F
7.3. Linear resolution                                                        237

 In a still more precise notation, we may append the clause and/or the pro-
gram. The implication

        A(Fi)       A(FO)

is called the resultant of the Re-inference; if I' is empty, we also identify the
resultant with re.
   The resolution ru/e R is the special case of Ru where the resultant is most
general among all possible resultants of unrestricted resolution with respect
to the same program clause and the same atom occurrence in the goal r,
that is to say, if A r * A ro' is another resultant relative to the same
rule and selected atom occurrence, then there is a substitution a such that
(A r'    A ro)0. = A r' -4 Are'. We use

                F

for a resolution step.

REMARK. It readily follows that r' in a resolution step is unique modulo
equivalence. For a resolution step it is not sufficient to require that we have
an Re-application with O an m.g.u. of A and B, as may be seen from the
following example. Consider a program {Dy          Az} and an instance of Ru:

           Cy, Ax Dy         Az
                                  R.,[z 1 x]
                Cy, Dy

with resultant Cy A Dy > Cy A Ax. A more general resultant is Cy A Du -4
Cy A Ax, obtained from

           Cy, Ax Du         Az
                                  Ru,[z / xi
                Cy, Du

Given the possibility of an unrestricted resolution step w.r.t. a partial goal,
selection of atom in the goal, and rule from the program, a recipe for finding a
resolution step for the same choice of rule and atom is given by the following:

7.3.3. PROPOSMON. Let r, A be a goal, '14 a rule from the program P, and
let there exist an unrestricted resolution step w.r.t. '14 and atom A in the goal.
Then a resolution step for the same goal, and same choice of atom and rule, is
obtained by taking a variable-permutation a such that FV(1-1a)nFv(r) = 0,
and then constructing an m.g.u. O of A and B, where 1-lce = (A B).

7.3.3A. * Prove the proposition.
238                                                                        Chapter 7. Resolution

7.3.4. DEFINITION. An unrestricted resolution derivation from the program
P is a "linear" finite or infinite tree of the form
                             ro        7-to e
                                                0
                                  F1
                                                         ei
                                           r,

                                         rn-i
                                                        rn


with the Fi goals, Ili variants of program clauses, 0, substitutions, and each
rule an application of R. Instead of the tree notation, one usually writes
               r,
          0 >u
            00
               11 ±u I 2 027u
                        01



The resultant of a finite unrestricted derivation
        F0 24. ...                rn
is the implication

        Arn -4 (A F°)M1                         en-1'

7.3.5.     It now seems natural to define a resolution derivation as an un-
restricted resolution derivation where each unrestricted resolution step is in
fact a resolution step. By this we expect to achieve that the resultant of any
finite subderivation is always most general. The following example, however,
shows that the requirement that every step is a resolution step is not quite
enough to achieve this. Consider the program {Py        Rxy, Py}, and the
following derivation:
                         Rxy            Py          Rxy
                                                          e
                                        Py                    Py
                                                                   [ylx]
                                                        [1

Each step is a resolution step, and the computed substitution is [ylx] with
resultant Rxx. This is not a most general resultant, since the derivation
                         Rxy PyRxy e
                                         Py                   Pz
                                                                   [Yizi
                                                        [1

produces the more general resultant Rxz. The difficulty is caused by the fact
that in the first derivation, the variable x, which disappeared at the first step
(was released), was reintroduced at the next by the substitution [ylx], and
therefore occurred in the resultant. This motivates the following:
7.3. Linear resolution                                                       239

7.3.6. DEFINITION. A resolution derivation or SLD-derivation from P is
an unrestricted resolution derivation with all applications of Ru in fact appli-
cations of R, and such that the variant of the clause chosen at each step has
its free variables distinct from the free variables occurring in the resultant so
far.

REMARK. The variable condition will guarantee that among "similar" deriva-
tions the resultant at every step will be most general. Two derivations are
similar if they start from the same goal, and at each step the same clause is
applied in both derivations, to the corresponding atom occurrences. In the
set X of all derivations similar to a given derivation, a derivation 1, with res-
olution (instead of unrestricted resolution) will be most general in the sense
that the resultants of any derivation in X may be obtained by substitution
applied to the resultants of D. This question is treated in greater detail in,
for example, C. [1994]. The variable condition given is sufficient, but not
necessary, for this result.
  The abbreviation "SLD" stands for "Selection-driven Linear resolution for
Definite clauses".

7.3.7. DEFINITION. An (unrestricted) resolution derivation is called (unre-
strictedly) successful if terminating in the empty goal, and (unrestrictedly)
unsuccessful, if terminating in a goal not permitting unification with the con-
clusion of a program clause.
  A successful derivation via Be,   , On_i starting from r    ro using program
P yields a computed answer on PIP of the form 0.              r Fv(ro)

7.3.8. DEFINITION. Let P be a program, r a goal; an answer to the query
rIP ("can goal I' be reached by program P?") is a substitution a with
dom(u) c Fyn; a correct answer to FIP is a a such that Pv (A no-. El
   By the completeness theorem for classical logic r (A r)o- is equivalent
to r (A r)o- where k is the usual semantical consequence relation.

7.3.9. THEOREM. (Soundness for linear resolution) Every computed answer
is a correct answer.
PROOF. For any resolution step relative to a program P
         I'          A


we can obviously prove in minimal logic
240                                                              Chapter 7. Resolution

since A     A E P, and since r and iv must be of the form PB, (rA)0
respectively, with BB = AG. Hence, if we have an unrestricted resolution
derivation of goal rn from ro:
        ro 7to
          r1    G01-ti A
                r2

                 rn._              un-1
                                               en-1
                          rn
we have
          Pv 1-7. A rn
          Pv H. A rni.           (An-2)en-2,

       Pv      A ri --+ (A0)90,
from which it readily follows that for all i, O < i < n,
          2v 1-m A rn -4 (A ri)eiei+i                 en_i.
Hence, if rn is an empty goal,
          'Pv I--, (A ro)90t91         en_i.                                        [2]



7.3.10. The interesting aspect of linear resolution is that more is achieved
than just a refutation: there is also a computed substitution. This permits us
to use linear resolution for computations. Consider e.g. the following program
P+ in the language (sum, 0, S), where "sum" is a ternary relation, 0 a constant,
and S a unary function:
                          sum(x, 0, x)
          sum(x, y, z)    sum(x, Sy, Sz)
Suppose we take as goal sum(x, 3, y) (as usual, the numeral n abbreviates
S(S    (SO)) (n occurrences of S). We get

          sum(x, 3, y) (1/41 sum(x, 2, y)
                                   sum(x, 1, Y)
                                   sum(x, 0, y)
                         Eu/x1
                                   [


with computed answer [y/SSSx]. That is to say, refuting Vxy -isum(x, 3, y)
provides an instantiation of 3xy sum(x, 3, y). A more complicated example is
given by the program P. which is P+ plus
                                                mult(x, 0, 0)
          mult(x, y, u), sum(u, x, z)           mult(x, Sy, z)
7.3. Linear resolution                                                                241

where "mult" is a new ternary relation added to the language. The following
is a derivation from Px
          mult (3, 2, z)                 mult (3, 1, u), sum(u, 3, z)
                                         mult (3, 0, u), sum(u, 3, z), sum(v, 3, u)
                           [v/31
                                         sum(u, 3, z), sum(3, 3, u)
                           [u/Su]
                                     u   sum(Su, 3, z), sum(3, 2, Su)
                           [u/Su]
                           -+ u sum(52u, 3, z), sum(3, 1, S2u)
                           [u/Su]
                                     u   sum(53u, 3, z), sum(3, 0, S3u)
                           [u/01
                                         sum(3, 3, z)
                           [z1Sz]
                                     u   sum(3, 2, z)
                           [z /Sz]
                                     u   sum(3, 1, z)
                           [z /Sz]
                           -+ u sum(3, 0, z)
                           [z/31
                                         sum(3, 0, 3)
                                         [



with computed answer substitution [z/6]. That is to say, we have derived
mult (3, 2, 6).

7.3.10A. * Is the unrestricted derivation above also a SLD-derivation?

7.3.11. THEOREM. (Completeness of SLD-resolution) When Pv            A Fa,
then there exists a successful SLD-deduction of r from P with computed
answer 0, such that there is a substitution -y such that ro- = ro-y.
PROOF. The proof uses the conservative extension result of theorem 6.7.5. If
Pv he A ro-, we have Nc Pv (A r)Cf; the deduction may be transformed
into a deduction in Nm in long normal form. By recursion on k we construct
SLD-derivations for pir, r -a ro of the form


                                                741




                                                         nk-1
                                                                 k -1
                                                   rk
and substitutions -yrc, deductions N, for the atoms in rk-yr, such that

          roc" -= roe()     elc-1-YZ.

For k = 0 we take r a ro,                    u. So by soundness Ark --+ (A ro)00
242                                                            Chapter 7. Resolution

  Suppose we have carried out the construction up to k, and Fk is not empty,
say Fk  PA. By the IH, there is an Nm-deduction 7, of All in long normal
form from Tv in Nm, say with r nodes. The final step in 7, must be of the
form

                    74     Vi(A          B)
                                              VE
                         (A       B)7-             (A A)7.
                                  BT
                                                             +E

where D' contains deductions of all atoms of AT with sum of sizes < r 1
nodes. Without loss of generality we may assume A      B to be such that
            B) is a variant of a clause in P with

(1)      FV(7-4) n (Fv(rk) u Fv(reo           Ok-1)) = O.

If we take

         O := T rFAT (Hk) U 7; r (Fv(rk) u Fv(reo            0 k -1))

it follows that AO = BO. So we may add a step


                                   rk 'Hk
                                     rk+i k
such that a new resolution derivation results. The condition (1) implies that
the recipe of proposition 7.3.3 applies, i.e. that 7-lk can play the role of 7-la
in the proposition. Ok is an m.g.u. of A and B; 0141+1 = 0, for some 741.
Therefore

         rk+17Z+1   =    Ti, A)9k-YZ+1
                    = rovricr+i, At9041 re, At9 =                   AT'
hence reo     ek_leofc+J.  reo ok_le reo Ok_il Po-. We now have
                                   .



deductions in long normal form for the atoms in rk+11+1 with the total sum
of sizes of these deductions less than the size for Fog (these deductions are
encoded in D' above).

7.3.12. REMARKS. (i) Inspection of the proof shows that the choice of
the atom A in rk is irrelevant: the result will always be a successful SLD-
resolution.
  (ii) From the proof we also see that a deduction 7, in long normal form
in Nm of A ro-, for a goal r, in an obvious way encodes an unrestricted
derivation of ro- If A ro- is, say, (A1 A A2)o-, the deduction must end with
7.4. From Gentzen system to resolution                                              243

       VY(A A + B)                             Vg(A Ai --* B')               Ty,
       (A     B)u, VE            (AD'
                                   A)a,        (A A,    B,)u VE
                                                                         (A A')a"
                       Bo'                                    B' o."
                              Bo-' A B' o-"      (A1 A A2)a

Without loss of generality we can assume in il = 0, Aio- = Bo.' , A2o- = B' o-" ,
which translates into the beginning of an unrestricted derivation
                        A1, A2       ¿=B           ,

                              Bo-' , Ao-'      a       A'   B' an


which can be continued using V', D" in the same manner.


7.4      From Gentzen system to resolution
In this section P,Q , R will be positive literals.

7.4.1. At the end of section 7.1 we indicated how in propositional logic
cutfree deductions of an empty goal could be read as resolution derivations,
with "linear resolution", i.e. all program clauses were of the form r       P, r
consisting of proposition letters only, or in one-sided notation     ,1, P. So
the program clauses in linear resolution contain a single positive literal.
  A more general form of propositional resolution is just Cut on literals:
         r,P      A, --,P
               rA
We shall now describe a very simple method of transforming cutfree deduc-
tions of a GentzenSchiltte system GS5p for Cp into a sytem based on gen-
eral resolution. This method applies to program clauses of the form r           A
(or in the form of a one-sided sequent, -ir, A).
   The principal reason for discussing this very simple case is that it can serve
as an introduction to the more complicated case of intuitionistic propositional
logic, to be treated in the next section.

7.4.2. DEFINITION. The axioms and rules of GS5p are
                                    A     A, B
        Ax P, --,13          RA P'
                                 (r, A, A A B)


        Rvi     r'A'
                       B                      r, A                     r,B
                                 RV2
244                                                       Chapter 7. Resolution

Here (I') is the set corresponding to the multiset F. The system is not yet
closed under weakening; if we add weakening

            RW
                 F,
we can always transform deductions such that weakening occurs only imme-
diately before the final conclusion.

7.4.2A. * Show that in GS5p plus RW the applications of RW can always be
moved to the bottom of the deduction. Show that GS5p + RW is equivalent to,
say, GS1p.

7.4.3. DEFINITION. A clause formula is a disjunction of literals (... (L1 V
...) V Ln). We identify clause formulas which differ only in the order of the
literals, and shall assume L1,. , Ln to be a set; this justifies the notation
without parentheses: L1 V ... V Ln. A clause is a finite set {L1, , Ln} of
literals. The number n of elements of the disjunction in a clause formula [the
number of elements in the clause] is called the length of the clause formula
[clause].

We might dispense with the separate syntactical category of clauses; but the
distinction is convenient in discussing the connection between resolution and
Gentzen system deductions in standard notation.

7.4.4. DEFINMON. (The resolution system Rep) In this system clauses are
derived from sets of clauses using the following axiom and rule:

            Axiom P,         RP,F           P,
                                     F, A

As before, "R" is called the resolution rule (but is in fact Cut on proposition
letters).

7.4.5. PROPOSMON. For each formula F constructed from literals using
V, A, there is a set of clause formulas Clause(F) and a proposition letter 1F
such that in'Cp F is derivable iff the sequent Clause(F)    IF is derivable in
a Gentzen system for Cp.
PROOF. Let F be an arbitrary formula constructed from positive and negative
literals by means of V, A. With each subformula A of F we associate a
propositional variable IA, the label of A. For atomic formulas P we assume
P IF. For A a BA C, B V C, ,13 we let A* IB A lc, lBV le',            Then

(1)         lA i4 A*
7.4. From Gentzen systern to resolution                                                             245

for all subformulas A of F guarantees that IA i4 A for all subformulas A of
F. The equivalences (1) may be expressed by a set of clause formulas FF of
length < 3 as follows: for each subformula A let CA C U C,
        CAC := {-'1B V -11C V 1BAC}, GAC                      l'IBAC V 113)-11BAC V 10

        C=BEVC := flBvc V -71B, IBvC V -110,               eBvC := {1B V 1C V -11BVC}

                      :=PP V l,p}
The formulas in C correspond to A*         1A (with positive occurrence of lA),
and the formulas in CA- to lA      A* (with negative occurrence of lA). If we
replace in rF    IF all labels by the corresponding subformulas, all formulas
in F become true, hence F holds if F F      IF holds. The converse is obvious.


NOTATION. If A           A1,... An, we write /A for /Al,             ,   /A
7.4.6. THEOREM. There is a mapping R which transforms any deduction
1, of       Fr, in GS5p into a resolution proof R(D) of 1F1,... ,lF from C
:= U{Cla(Fi) : 1 < i < n}, where Cla(F) is the set of clauses corresponding
to Clause(F).
PROOF. The deduction in GS5p has at its nodes (multi)sets of subformulas
of F1,   , F. We show by induction on the depth of the deduction that if the

multiset A has been derived, then in the resolution calculus we can derive lb,
from the clauses in C as axioms.
 Case 1. An axiom P,,.13 translates into
         /_,p, /p (input)          /p, dp
                    1P   7   LP
where "(input)" means that the clause is an axiom clause from C.
Case 2. If the final rule in 1, is RVi, as on the left, we add to the derivation
in Rp existing by IH the part shown on the right:
                                                           /AvB,--dA (input)               (ir, /A, /B)
                                  1 AvB, 413 (input)                (iAvn, 1B     7   lr
      (r, A V B)                               (lAvB lAVB )1r)
                                                       7




The cases of RV2, RV3 are simpler and left to the reader.
Case 3. Similarly if the last rule is RA:
                                        1AAB,,1A, 11B (input)            1r, IA
        r,A A,B                                  (1)1ABI-11B,ir)                      la, IB
       (1',A,A AB)                                            (1AAB, ir, la)
246                                                           Chapter 7. Resolution

7.4.6A. 4 What goes wrong in the argument above if GS5p has RVi, but not
RV2,RV3? What is the reason behind the choice of a context-free version of RA?

7.4.7. COROLLARY. The calculus Rcp is complete for Cp (in the sense that
there is a transformation of a formula F into a problem of deriving a letter
1F from a set of clauses, such that the the latter deduction is possible in Rcp
iff F was derivable in Cp).

7.4.8. REMARK. In dealing with predicate logic, a standard procedure is
to use "Skolemization": formulas are brought into prenex form, and existen-
tial quantifiers are eliminated by the introduction of new function symbols
("Skolem functions" ). But there is also a method, due to N. Zamov, which
avoids the process of prenexing and Skolemizing, and which is briefly sketched
here.
   In predicate logic, literals are atomic formulas or their negations, and initial
clauses are disjunctions of literals L1 V ... V Ln (n > 2), or existentially
quantified disjunctions of literals Ay(Li V ... V Ln) (n > 2). Clauses are
simply disjunctions of literals (n arbitrary). (We make no distinction between
clauses and clause formulas in this description.)
   In the spirit of proposition 7.4.5 one can show that there is a finite set ClaF
of initial clauses such that a formula F holds if the universal closure of ClaF
is inconsistent.
   Resolution appears in two versions, namely as ordinary resolution

        RLVC(C V C9o-

with o an m.g.u. of the literals L,    ,   and 3-resolution
              3y(L V C)    --11 V C'
        .n3
                    (C V Clo-
where o is an m.g.u. of L, L' not containing the assignment y/t, and such
that (C V C')o- does not contain y.


7.5      Resolution for Ip
In this section P,Q,R.EPV.

7.5.1. We now apply the ideas of the preceding section in the more compli-
cated context of Ip. We start by introducing yet another variant of the intu-
itionistic Gentzen system, the system G5ip. The antecedents of sequents are
multisets. There is no weakening rule, but weakening has been built into some
7.5. Resolution for Ip                                                         247

of the logical rules. There is also no separate contraction rule, but most of the
rules have contraction built explicitly into the conclusion. This is indicated by
putting parentheses around the multiset of the antecedent; thus in the conclu-
sions of the rules below, an expression like (F, F',    , A, A', ...) indicates the

multiset obtained by taking the multiset union of r,          , {A}, {A}, ... and

contracting whenever possible, i.e. all formulas in the union are contracted to
multiplicity one. In other words, (r) will be Set (F). Note that sets are repre-
sentable as multisets in which every formula has multiplicity one. The rules
below are such that in a deduction every multiset occurring in the antecedent
of a sequent is in fact a set.

DEFINITION. (The Gentzen systems G5ip, G5i) The system G5ip is given
by axioms and rules:
Axiom,s

          Ax A         A                          LJ_ _L =- A

Rules for the logical operators

                           A        C                       F,       C
          Lni
                               oF

                       '                          LA2
                 (r, Ao A AO             C              (r, Ao A Ai)   C

                   r,A0,A1C                             FA A B
          LA3
                 (r,A0 A A1)             C        RA(r, A)            AAB

                A,rC B,AC Rvi
          LV(A v B, F, A)                    C          rAovAi (i=0,1)
                 FA                 B,        C               B
                                                  R1 rA'1' A--+B      r B
          L-4
                  (1", A, A -4 B)            C
                                                                 n-42
                                                                       AB
The system can be extended to a system G5i for predicate logic by adding

                A[x It], r          B                       A[x Iy]
          LV                                      RV
                (VxA,r)             B                   r    VxA

                A[xly],r                                r
                                                        rxA
                                    B                       A[xlt]
          1,3                                     R3
                (3xA,r)             B

where in L3, RV y 0 FV(F, A), and also y x or y FV(A). However, we
shall not discuss predicate logic in the remainder of this section.
  G5i has the following property.
248                                                       Chapter 7. Resolution

7.5.2. PROPOSITION. If we add the Weakening rule
               F   B
         LW
              A, F  B
then any derivation in G5i + LW can be transformed into a derivation where
the only application of weakening appears just before the conclusion; the
ordering of the subtree of the prooftree consisting only of nodes where a
logical rule is applied, with the names of the rules attached to these nodes as
/abels, remains the same under this transformation.
PROOF. The proof is straightforward, by "pushing down" applications of LW.
The fact that there are several variants of certain rules, such as R> and LA,
which incorporate an element of weakening, makes this possible.

7.5.3. PROPOSITION. The system G5ip is equivalent to the system Glpi
in the following sense: if F =- A is provable in G5ip, then it is also provable
in Glpi, and if r A is provable in Glpi, then r A is provable in G5ip
for some r' c F.

7.5.4. DEFINITION. An intuitignistic clause is a sequent of one of the fol-
                   P, treated as a set):
lowing forms (P1, . .

         (P > Q)        R,   P    (Q V R),         , Pn    Q

(P,Q,R,P1, .. ,P atomic). A clause is initial if it is of the first, second or
third type with n < 2. n = 0 is possible for clauses.
   An intuitionistic clause formula is of the form

         (P       Q)    R,   P >(Q V R),          (P2     . .   .(P,,--*Q)   .   .   .).

In the third case there corresponds more than one clause formula to a clause
(because of permutations of the Pi).

7.5.5. THEOREM. Let F be an arbitrary propositional formula, and suppose
that we have associated with each subformula A of F a propositional variable
1 A (the label of A). Then there is a set Clause(F) of initial clause formulas
involving only labels of subformulas of F such that

              F   iff Clause(F)    1F

PROOF. For atomic formulas A we may take IA A. For compound A of the
forms B V C, BA C, B > C we let A* be 1/3 V 1c, 1B A lc, 1B lc respectively.
The set of equivalences of the form

         1 A <4 A*
7.5. Resolution for Ip                                                                        249

fixes the relationship between the formulas and their labels, and entails

           IA ++ A

for all subformula,s A of F. We express A* --+ IA (where the label of A appears
positively) by a set of clause formulas C-Af-, and lA -+ A* (where IA appears
negatively) by a set of clause formulas C.

           cIAD          {/13,113    1BAD}                   CB- AD   = {1BAD -+ 1B, 1BAD -+ 1D}
           CiF3vD   = {1B -+ 1BVD, 1D               1BVD}    CB-VD = {1BVD     1B V 1D}
           CD {(1B -+ 1D)                      1   B D}      C B-+D = {1B-s D -+ (1B -+ D)}

Now take for Clause(F) the collection

           U{C-IA: U CA-        : A non-atomic subformula of F}.

Then we have: if Clause(F)     lF, then   F, for if we substitute A for the
IA everywhere, all the formulas of Clause(F) become true and lF becomes
F. Conversely, if    F, the Clause(F) entails F      1F, so Clause(F)     lF
follows.


REMARK. The theorem can be extended to sequents A                                 F in a straight-
forward way.


7.5.6. DEFINITION. (The resolution calculus Rip)
Axioms

           P        P,              P (A atomic).
Inference rules

                r   (P       Q)     R                        Q
           -+
                                    A          R
([11 indicates that P may be present or not).

           Vr
                    PQVR                 CS,        P                        A",RS
                                                   (AA'A")       S

                    A       P       P,              Q
           Res
                            (AA')        Q

with P, Q, R, S propositional variables.
250                                                                        Chapter 7. Resolution

7.5.7. THEOREM. For any 7, : F           F in G5ip we may construct a deriva-
tion R(D) : A HRpi 1r        1F where lr     1E31, ,ln if F B1,. Bn, and                    ,




A consists of all initial clauses corresponding to the initial clause formulas
constructed in 7.5.5.
PROOF. By induction on the length of D.
Basis. D is an axiom A   A or I A. Then R(D) is the corresponding
axiom /A         /A, I       1A
Induction step.  We show below on the left the last rule application in D,
and on the right the corresponding final steps in R(D); if we have on the left
premises r A, A         B etc. Then /r 1A, la       IB are clauses derived by
the induction hypothesis.

                                                    1AAB       lA    1A,1B,lr         113
           A, B, F       D                                                                  Res
         (A A B, F)       D          1AAB   IB             (1AAB,1B,1r)       -1D
                                                                                      Res
                                                  (1AAB,11')    1D




       FA B,AD                         1r    /A
                                                     1A-B,1A1B
                                                           (1A-03,111,11)
                                                                           1B, la
                                                                                                Res
       (A +       F,             D                                                    Res
                                                      /71AsB)         1D




  A,r#.D          B, A       D    1Ava#.1A V 1B     1AvB#'1AvB       1A, /r     11,    1B, l#. in
       (AvB,r,A)         D                            (1Avs,lr,16,)#.1D

etc. The other cases are left to the reader.

7.5.8.       THEOREM. Clause(F) HRip 1F iff G5ip                     F.                               z

7.5.9. LEMMA. Let D : r         F in G1pi or G5ip. Then for any sequent
A1,.   A,,    B in D, the A, are negative subformulas of F or positive sub-
formulas of r, and B is a positive subformula of F or a negative subformula
of F.
PROOF. By inspection of the rules.                                                                    z

7.5.10.  COROLLARY. (Refinement) For anyt             F, /et Clause*(A     F) be
the set of initial clauses containing only the CA for A occurring positively in r
or negatively in F, and the CI for A occurring negatively in I' and positively
in F. If G5ip A F, then Clause*(A F)                     la 1F
PROOF. By inspection of the proof of 7.5.7 and the preceding lemma.
7.5. Resolution for Ip                                                                    251

7.5.11. EXAMPLE. We demonstrate the transformation of theorem 7.5.7 by
an example. Since in this example only --+ is involved as operator, we write
simply AB for A --* B. The purely implicational sequent (QP)R,QR, RP
   P has the following deduction in G5ip:
                   Q       QR        R
                       Q,QR       R            P-P
                             Q, QR, RP   P      R -RP P
                             QR, RP QP           R, RP P
                                    (QP)R, QR, RP P

By theorem 7.5.7, we can construct a deduction of

           1(Qp)R,1QR,1Rp           P
from clauses

           lqp,l(Qp)R        R
           1QR,Q       R
           1Rp,R       P
           Q --* P         lQp

The proof gives the following deduction in Rpi:
                                    1QR,Q          RR        R
                       Q     Q             lQR, Q       R          lRp,R      PP      P
                                  1QR,Q        R                       lRp,R      P
    Q -4 P     1Qp                                  1QR,1Rp,Q        P
                            1QR,1Rp        1Qp                                            1)
                                                   1(Qp)R,1Rp,1QR        P

where D is the deduction
                                                         R,1Rp     PP         P
                                           P       P         R,1Rp        P
               l(Qp)R,lQp              R               R,lRp ZZP
                             1(Qp)R,1Qp,1Rp            P

This can be simplified to

                       1QR,Q           R   1Rp, R        P
Q      P      1Qp                lQR,1RP,Q         P         1(Qp)R,1Qp       R   R,lRp        P
               lQR,lRp           1Qp                               1(Qp)R,1Qp,1Rp     P
                                           1(Qp)R,1Rp,1QR        P
252                                                        Chapter 7. Resolution

7.5.12. Permutability of rules
We recall the definition 5.3.1 of the permutability of rules in Gentzen systems.

LEMMA. In G5ip the following permutation properties hold:

       R+ permutes over LV, L-4;
       LV permutes over L+,          LV;

       L--* permutes over L-4,

PROOF. By checking the various cases.
From now on, we consider deductions in G5ip with atomic instances of the
axioms only.

7.5.13. LEMMA. Let D be a (cutfree) deduction in G5ip of a sequent of
the form F P, P atomic, r a set of initial clause formulas. Then D can be
transformed into a deduction TY such that the following three conditions are
met.

       An f.o. P   Q is principal in the succedent if it is at the same time an
       active formula of an L> application.
       An f.o. P --+ Q y R is principal in the antecedent, and the active occur-
       rence of Q V R in one of the premises is itself principal.
       An fo. P      (Q --+ R) is principal in the antecedent, and the active
       occurrence of Q     R is itself principal.

PROOF. We note that because of the subformula property, every succedent
formula must be of the form Q or Q > R, and an antecedent formula has
one of the following forms: Q, Q      R, Q V R, Q     (R     8), (Q --+ R)   S,
Q > R y S; formulas of the last three forms belong to F.
  We now extensively use permutability of rules, as follows.
Step 1. We permute any application of           introducing a formula Q      R
downward over LV, L> until we reach an             application with Q      R as
active formula. fi is easy to see that each permutation of this kind decreases
the number of occurrences of implications in the succedents of the deduction.
Note that premises of applications of L> with Q          it or Q V R as active
formula on the left will have an atomic formula as succedent.
Step 2. If the deduction does not yet meet the second or third condition,
there will be applications of L> with an active formula occurrence of the
form Q     R or Q V R on the left such that this active occurrence is not the
principal formula of an application of L-4 or LV. Such an occurrence and
7.5. Resolution for Ip                                                               253

its ancestors we call "offending occurrences" . We apply induction w.r.t. the
number of offending occurrences of Q > R or Q V R. We search for a topmost
application of this kind, and permute it upwards over the preceding two rules
(L-4, L--* or LV,        or R>, L-4) corresponding to an application of L+
meeting condition (i), (ii) or       The number of offending occurrences of
the offending active formula Q V R or Q     R will diminish by this procedure.
The final result will be a deduction meeting all requirements.

7.5.13A. 4 Check the cases of Step 2 in detail.

7.5.14. THEOREM. G5ip F- r*        P iff r F-Rpi P.
PROOF. The direction from right to left is straightforward. Conversely, let
us assume G5ip F*         P. We may assume this to have been proved by
a cutfree deduction D in standard form according to the preceding lemma.
Each sequent occurring in D will be of the form

        E, A     A

where E c F. We prove by induction on the depth of D that l                         IA is
derivable in Rip from r.
Case I. D is an axiom; trivial.
Case 2. Suppose the deduction ends with L> introducing (P                     Q)     RE
r. Then the final part of the deduction has the form
                          E,   [P]         Q
                          E, A   P         Q    R, A', E'    P'
                          ((P > Q)         R, E, E'A, A')    P'

with (P + Q)       R E r. By III we have resolution proofs of

                          1r,[13]     Q,           R,       P'.
We construct a resolution proof terminating in
         P>Q          lpQ        1A,[13]       Q
                     IA                                     R

                                                    (1,l)         P'

Case 3. The deduction ends with L-4, introducing P                     (Q   R) E r*; then
the final part of the deduction has the form
                                    E', A'    Q E", A",
                  E, A       P      (E', E", A', A", Q)
254                                                                                      Chapter 7. Resolution

By 1H we have resolution proofs of



We construct from these a resolution proof terminating in:
                 P,
                        (Q , 1 a)          R         1 a,           Q
                                    (1la,)          R                       1       ,R      P'
                                                                 lpil           P
Case 4. The deduction ends with LV introducing P                                          (Q V R) E r*. The
final part of the deduction has the form
                              A', E', Q     P' A", E", R P'
                      E       P  (A', A", E', E", Q V R) P'
                  (A, A', A", E, E', E", P --+ (Q + R))  P'
By DI we have resolution proofs of

                   /A        P,            la, Q             ,



We construct from these a resolution proof by application of the V-rule:
             PQVR                      la P                                                      P'
                                        (la, ls,,                   P'
Case 5. The deduction ends with introduction of P                                        Q E r* on the left:
                              A, E     P      A',  Q                         R
                               (A, A', E, E', P   Q)                        R
By Ifl we have resolution proofs of

                                 /E        P,            1E, , Q            R.

We construct a resolution proof terminating in
                            lE        PP             Q
                                      /E        Q                       Q        R
                                                (1E , 1E,)          R

etc.

7.5.14A. * Show by a direct argument that for the resolution calculus Rpi there
is a decision procedure for sequents.
7.6. Notes                                                                   255

7.5.14B. 4 Give deductions in Rpi of (P V Q       R)    (P    R) A (Q    R) and
(P (P Q))         (P (2).


7.6      Notes
There is a very extensive literature on resolution methods, theorem proving
and logic programming. Some good general sources are Lloyd [1987], Apt
[1990], Eisinger and Ohlbach [1993], Hodges [1993], C. [1994] and Jä.ger and
Stärk [1994]. For the older literature see Chang and Lee [1973]. For the
connection with Maslov's so-called "inverse method" , see Lifschitz [1989].
   There are many important aspects of logic programming which have not
even been mentioned in this chapter. For example, there is an extensive
literature on the correct interpretation and handling of negation in logic pro-
gramming. (For a first orientation, see C. [1994].) Another example of a
neglected topic is the peculiarities of the search mechanism of languages such
as PROLOG, which are not reflected in the deduction systems considered in
this chapter. As to the possibility of expressing the search mechanism of
PROLOG and related languages in a deduction system, see, for example, Kals-
beek [1994,1995].

7.6.1. Unification. The first to give an algorithm for unification together
with an explicit proof of its completeness was J. A. Robinson [1965]. The idea
for the unification algorithm presented here goes back to Herbrand [1930, sec-
tion 2.4], where such an algorithm is sketched in a few lines. A full description
together with a proof of the termination and correctness of this algorithm is
first given in Martelli and Montanari [1982]; this proof has been followed
here. Cf. also C. [1994, 3.10]. More on unification may be found in Baader
and Siekmann [1994].

7.6.2. Resolution. The first to study resolution as a proof method in predi-
cate logic was J. A. Robinson [1965]. One of the earliest references for SLD-
resolution is Kowalski [1974]; around the same time PROLOG was developed
by a group around A. Colmerauer. The concise proof of completeness for
linear resolution given here is essentially due to Stärk [1990]; combination of
Stärk's proof with the proof of the conservative extension result in Schwicht-
enberg [1992] transforms it into a proof-theoretic reduction of completeness
for resolution to completeness for other systems.
   The material in the last two sections is based on papers by Mints, in par-
ticular Mints [1990,1994b].

7.6.3. Languages suitable for logic programming. In the literature a good
deal of attention has been given to discovering languages suitable for logic
256                                                         Chapter 7. Resolution

programming, and of greater expressive power than is provided by programs
consisting of definite clauses and goals which are conjunctions of atoms.
  Generalization is possible in several ways. For example, one may enlarge
the classes of formulas which are used as goals and clauses of programs,
while keeping the notion of derivability standard, that is to say, classical.
A further generalization consists in considering also intuitionistic or minimal
derivability. A more radical move is the consideration of logical languages
with more or different logical operators, such as the languages of higher-order
logic and of linear logic.
   A good example of such an investigation is Miller et al. [1991]. The idea in
this paper is to look for logical languages for which the "operational seman-
tics" (which provides the computational meaning and which is similar to the
BHK-interpretation of intuitionistic logic (2.5.1)) coincides with provability.
   Let G be a goal formula, F be a program, specified as a finite set of formulas,
and let F H0 G express that our search mechanism succeeds with program F
for goal G. Then one requires for ho: F H0 T, r H0 G1 A G2 iff r Ho G1 and
rH0G2,rH0GivG2iffrH0GiorrH0G2,FH0D                          Giffru{D}H0G,
F H0]xA iff r A[xlt] for some term t, r Ho VxA iff r H0 A[xly] for some
variable y, not free in r or VxA, and free for x in A. As a formalization of
Ho one can take the notion of uniform provability in a Gentzen system. A
deduction is said to be uniform if, whenever in the course of the deduction
      G is proved for a non-atomic goal G, the last step of the deduction
consists in the application of the right-introduction rule for the principal
operator in G.
  One now looks for triples (T, G, I-) with V, F formula classes, and I- a
notion of derivability in a Gentzen system such that for r c F, G E g one
has r H0 G iff there is a uniform deduction of r   G iff r       G. Such
triples are called abstract programming languages in Miller et al. [1991].
   A simple example is obtained by taking for H classical provability (say in
Glc), for G the class inductively characterized by

                       gaTIAtIGAGIGVG1 3xg,
where At is the class of atomic formulas, and for F the class characterized by

                       D = Atig> At I         A    I VxT.

  The proof that this triple is an abstract programming language involves
showing that whenever a sequent of the right form is provable, it has a uniform
deduction; the argument uses the permutability of certain rules in the Gentzen
system (cf. 5.4.6B). Permutation arguments are also an important ingredient
of the papers mentioned below.
  In Harland [1994], Hodas and Miller [1994], Miller [1994], and Pym and
Harland [1994] suitable (fragments of) linear logic are used as formalisms for
7.6. Notes                                                            257

logic programming (references to related work in Hodas and Miller [1994]).
For examples of programming in such languages see Andreoli and Pareschi
[1991] and Hodas and Miller [1994].
   Andreoli [1992] shows how by choosing an appropriate formalization of
linear logic one can greatly restrict the search space for deductions.
Chapter 8

Categorical logic

For this chapter preliminary knowledge of some basic notions of category
theory (as may be found, for example, in Mac Lane [1971], Blyth [1986],
McLarty [1992], Poigné [1992]) will facilitate understanding, but is not nec-
essary, since our treatment is self-contained. Familiarity with chapter 6 is
assumed.
  In this chapter we introduce another type of formal system, inspired by
notions from category theory. The proofs in formalisms of this type may
be denoted by terms; the introduction of a suitable equivalence relation be-
tween these terms makes it possible to interpret them as arrows in a suitable
category.
  In particular, we shall consider a system for minimal --+AT-logic connected
with a special cartesian closed category, namely the free cartesian closed
category over a countable discrete graph, to be denoted by CCC(PV). In
this category we have a decision problem: when are two arrows from A to B
the same?
   This problem will be solved by establishing a correspondence between the
arrows of CCC(PV) and the terms of the extensional typed lambda calculus.
For this calculus we can prove strong normalization, and the decision problem
is thereby reduced to computing and comparing normal forms of terms of the
lambda calculus.
   Another interesting application of this correspondence will be a proof of
a certain "coherence theorem" for CCC(PV). (A coherence theorem is a
theorem of the form: "between two objects satisfying certain conditions there
is at most one arrow".) The correspondence between lambda terms modulo
ßi-equality and arrows in CCC('PV) will enable us to use proof-theoretic
methods.
  In this chapter P, P', P", Q, R E PV.




                                     258
8.1. Deduction graphs                                                          259

8.1      Deduction graphs
Deduction systems ("deduction graphs") inspired by category theory manip-
ulate 1-sequents. A 1-sequent is a sequent of the form A     B. A sequent
   B is interpreted as a sequent T B. Below we shall describe deduction
graphs for intuitionistic --+AT-logic.

8.1.1. DEFINITION. A deduction graph consists of a directed graph A =
(.40,A1) consisting of a set of objects (vertices, nodes) Ao and a set of arrows
(directed edges) A1 such that (writing f: A      B or A 4. B for an arrow from
A to B)
      If f:A       B, g:B          C, then there is an arrow g o f:A       C, the
      composition of f and g;
      For each A E Ao there is an identity arrow idA: A         A.

A is the domain of f: A     B, and B is the codomain of f: A        B. For the
set of arrows from A to B we also write Ai(A, B).
   A tci-deduction graph or positive deduction graph ("tci" from "truth, con-
junction, implication") is a deduction graph A = (Ao, Ai.) with a special
object T E A0 (truth or the terminal object) and with the objects closed un-
der binary operations A,    that is to say, if A,B E .40, then also AAB E Ao
 (the product or conjunction of A and B), and A + B E Ao (the implication,
 exponent or function object from A to B). There are some extra arrows and
arrow-constructors:
      trA: A      T (the truth arrow);
      71-61'B: A A B      A, riA'B: A A B  B, and if f C A, g: C           B , then
      (f,g):C          A A B. We shall sometimes use p(f, g) for (f, g);
  (IT) evA,B: (A > B)AA      B, and if h: CAB     A then cur(h): C     B > A.
      ("cur" is called the currying operator, "ev" is called evaluation.)
We shall frequently drop type superscripts, whenever we can do so without
danger of confusion. Instead of x: A, t: A we also write xA,tA.        N

8.1.2. EXAMPLES. (a) We obtain a deductive system for minimal TA-4-
logic by taking as objects all formulas built from proposition variables and T
by means of A,      and as arrows all arrows constructed from idA, trA, roA'B,
71-j.LB, eVA'B by closing under o, ( , ) and cur. The construction tree of an
arrow corresponds to a deduction tree, or alternatively, the expressions for
the arrows form a term system for deductions with axioms and rules:
         idA: A        A; trA: A     T
260                                                              Chapter 8. Categorical logic
         t: A     B        s: B       C
                s o t: A      C
          A,B
                :.AAB      -A; 71'
                               AB
                                   :AABB
         t:C      A        s:C        B
              (t,$):CAAB
         evA'B: (A --+ B) A A             B

              t:AABC
         cur (t): A        B+C

A formula A is said to be derivable in this system if we can deduce a sequent
T    A.
  An example of a deduction, establishing associativity of conjunction (ab-
breviating "A AB" as "AB", and leaving out the terms 70 and and 7r1 for the
axioms to save space):

                                          (DE)F         DE DE =E
      (DE)F      DE DE            D             71070: (DE)F       E           (DE)F   F
         irooro: (DE)F       D                         Orioro,         (DE)F    EF
                                          (DE)F         D(EF)

where
                            ceD,E,F           (70070, (71070, 71).))

Adding constants c: A B amounts to the addition of extra axioms. Note
that there may be different c for the same 1-sequent. Adding more than
one constant for the same 1-sequent may arise quite naturally: a particular
sequent may be assumed as axioms for different reasons, so to speak. Thus we
obtain T    T both as tri- and as icIr. Adding "variable arrows" x: A B
corresponds to reasoning from assumptions A        B. See also example (c)
below.
       Given a directed graph A (A0, A1) we may construct a free deductive
graph FG(A) over A by taking as objects Ao, and as arrows the expressions
generated from elements of A1 and idA by means of composition; the elements
of A1 are treated as constants. Two arrows given by expressions are the same
iff they are literally identical as expressions.
       The free tci-deduction graph D(A) over a directed graph A is ob-
tained similarly; objects are obtained from T and elements of Ao by clos-
ing under A, >. The arrows are obtained by adding to the arrows of A1
trA, idA 4,B,inB evA,B and closing under o, ( , ) and cur. If we take PV for
A, we are back at our first example.
8.1. Deduction graphs                                                        261

8.1.2A. * Show that the free tci-deduction graph over the discrete graph of all
propositional variables is equivalent, as a deduction system, to one of the usual
formalisms for the TA>-fragment of minimal logic.


8.1.3. In systems of natural deduction, the reduction relation generated
by the usual conversions suggests an equivalence relation on the terms de-
noting deductions. Similarly we can impose identifications on the arrows of
deduction graphs and tci-deduction graphs; this time the identifications are
suggested by the notion of category and cartesian closed category respectively.


DEFINITION. A category A is a deduction graph such that the arrows satisfy

iden     f o id A = f, ¡dB o f = f for every arrow f : A =- B,
ass      f o(goh)=(fog)oh
              for all arrows f:C           D, g: B         C, h: A =- B.


DEFINMON. A cartesian closed category (a "CCC" for short) is a tci-de-
duction graph which is a category and in which the arrows satisfy for all
f : A =. T:

true     f = trA,

and for all f : C      A, g: C      B, h:C =- A A B:

                    (f7g)   f5        o      g)       g5
proj
surj     (70h, 71h) = h,




evcurL
and for all h:CAB=-A,k:CB+A:

curev
                                       CA)
         eVA'B o (cur(h) o 7ro 'CA , 7ri
         cur(evA,B o (k o 1-0", 7r1c'A)) = k.
                                             =    ,




REMARK. If we write f A g for (f o ro, g 01'0, the last set of equations reads

         evo (cur(h) A id) = h, cur(ev o (k A id)) = k.

From this last equation follows cur(ev) = idA'B. The equation cur(evA2B) =
idB together with cur(h)ok = cur(ho(k Aid) again yields cur(evo (k Aid)) =
k.
262                                                             Chapter 8. Categorical logic

8.1.4. EXAMPLES. (a) There are numerous examples of categories; they
abound in mathematics. A very important example is the category Set, with
as objects all sets, and as arrows from A to B all set-theoretic mappings
from A to B. Composition is the usual function composition, and idA is the
identity mapping on A. Set is made into a CCC by choosing a singleton set
as terminal object, say {0}. It is then obvious what to take for trA, since
there is no choice; for the product A A B we choose a fixed representation of
the cartesian product, say {(a, 0) : a E A} U {(b, 1) : b E B} where 0 = 0,
1 = {0}, and (x, y) is the set-theoretic ordered pair of x and y. A       B is
the set of all functions from A to B. We leave it as an exercise to complete
the definition. Note that in this example elements of a set A are in bijective
correspondence with the arrows f : T  A, and that there is a bijective
correspondence between the arrows from A to B and the elements of the
object A + B.
  (b) Given a directed graph A a (A0, A1), we obtain a free category over A,
Cat(A), by taking as objects the objects of A, and as arrows the equivalence
classes of arrows in the free deduction graph over A. That is to say the
equality between arrows is the least equivalence                    satisfying

        t o (s o r)      (t o s) o r, t o id       t, id o t   t,

and congruence:

        if t     t', s    s' then tos          t' o s'.

In other words, equality between arrows can be proved from the axioms t o
(s o r) = (t o s) o r, t o id = t, id o t = t, t = t, by means of the rules

        t = t'        e = t"        t = t'          t = t'      s = s'
                 t = t"             t' = t            tos=t'os'
Similarly we construct the free CCC(A) over A, by first constructing the free
tci-deduction graph and then imposing as equivalence on arrows the least
equivalence relation satisfying

        t o (s o r)      (t o s) o r, t o id t, id o t t,
        f trA for all f : A T ,
        7ro o (t, 8) Pz% t, ir o (t, s)    s, (7ro o t, 7r1 o  t,
        ev o (cur(s) o 7r0, 7ri)      s, cur(ev o (t o 70, 71)) t,

and the congruences

        if t     t', s    s' then t o s Pe, t' o s' ,
        if t     t', s    s' then (t, s) (t', s'),
                                     cur(e).
8.1. Deduction graphs                                                           263

Again this can be reformulated as: equality = between arrows can be proved
from axioms t = t, (7ro o t,7r1 o t) = t, ... by means of the rules

        t = t'        t' = t"   t = t'      t = t'    s = s'
                                                                   etc.
                                t' =t
                                                               ,
                 t = t"                      (t,$) = (ti,s1)

An important special case of this construction is CCC(PV), where PV , the
collection of proposition variables, is interpreted as a discrete category with
no arrows and with PV as its objects.

8.1.4A. 4 Complete the definition of Set as a CCC.

REMARK. Free categories, graphs and CCC's may also be defined by cer-
tain universal properties, or via the left adjoint of a forgetful functor; but
since we concentrate here on the proof-theoretic aspects, while minimizing
the category-theoretic apparatus, we have chosen to define the free objects
by an explicit construction; cf. Lambek and Scott [1986, section 1.4].

8.1.5. LEMMA. The following identities hold in any CCC and will be fre-
quently used later on:

         (f,g)oh= (foh,g0h),
        ev(cur(f),g) = f (id, g),
        cur( f) o g' = cur(f o (g' o 70,71)),

where f:A A B         C, g: A   B, g': A'    A.


8.1.5A. 4 Prove this lemma.

8.1.6. DEFINITION. Two objects A, B in a category A       (A0, A1) are
isomorphic, if there are arrows f : A B, g : B A such that g o f = idA,
f o g = idB. We write A B for "A and B are isomorphic".
  One readily sees that if A  A', B    B', then there is a bijective cor-
respondence between the arrows from A to B and the arrows from A' to
B'
  For example, the isomorphism A --+ T = T holds in every CCC. This is
verified as follows: trA-+T : A     T       T and cur(trTAA) : T          A > T are
inverse to each other; trA-41- o f = trT = idT for every f : T   A > T;
and cur(trTA)A
               o trA'1- = cur(trT" o (trA'T A idA)) = cur(tr(A'1-)AA)
cur(evA'T,A)     idA>T. We shall have occasion to use this isomorphism,
together with others mentioned in 8.1.6A below.
264                                                        Chapter 8. Categorical logic

8.1.6A. 4 Show that in any CCC the following isomorphisms hold: A A B
B A A, T A - -A,(AAB)ACfL-AA(BAC),TA- -,A,A-1-- -T,
(C A A B) (C > A) A (C        B), (B A C A) fL- B > (C    A).

We note the following:

8.1.7. PROPOSITION. (One-to-one correspondence between Ai(A, B) and
   (T, A + B)) In any tci-deduction graph there are operators E and
such that for f : A B, g : T A * B:
                                 g:A     B.

Moreover, in a CCC they satisfy:
                    f, rg^-n = g.

PROOF. Take

                   cur(f            g   ev,
                                         AB o (g o trA , idA).


8.1.7A. 4 Verify the required properties for r       and     as defined.


8.2           Lambda terms and combinators
In this section we construct a one-to-one correspondence between the arrows
of the free cartesian closed category over a countable discrete graph CCC(PV)
and the closed terms of the extensional typed lambda calculus with function
types and product types, A714A. This is the term calculus for -4A-Ni with
two extra conversions, namely n-conversion and surjectivity of pairing, in
prooftree form
          D                                   7,             D
      A > B A' cont          D            A1 A A2      A1 A A2
      ,       B            A>B              A1           A2
                                                               cont
                                                                    Ai A A2
          /1> B                                    Ai A A2

We have already encountered the inverses of these transformations (so-called
expansions) in section 6.7.

8.2.1. DEFINITION. (The calculus )rp+AT) We introduce an extension of
A, with product types (conjunction types) and a type of truth T. The
type structure T---yAT corresponds with the objects of the free cartesian closed
category CCC(PV) over the countable discrete graph PV:

  (i) T        T, P E TAT for all p E PV.
8.2. Lambda terms and cornbinators                                               265

        If A, B E 7-_,AT, then (A                 B), (A A B) E 7-4AT

Terms are given by the clauses:
        There is a countably infinite supply of variables of each type;
        *: T;

  (y) if t: Ao A Ai, then pit: A (i E {0,1});
        if t: A --+ B, s: A, then ts: B;
        if t: A, s: B, then p(t, s): A A B; for p(t, s) we also write (t, s).
Axioms and rules for 07i-reduction are

true       tT
Ocon       (AxA .tB)8A              ta[x/si,
?icon      AxA.tx         t (x        FV(t)),
proj       pi(toti)           t, (i E {0, 1.}),
surj       (pot, pit)          t.

In addition we have
                                                                    t »- s
           (refl) t       t                         (repl)
                                                                        s[xlr]
where x in "repl" denotes any occurrence, free or bound, of the variable x. E]
The rule repl may be split into special cases:
            t             s »-                      t     t'      8-
           p(t, 8)        P(ti,                          ts »- ti

                t     e                                 t »- t'
                                                                    (i E 0,11)
           Ax.t »- Ax.e                             pit -; pit'
Below we shall prove strong normalization for An_yA, extending the proof of
section 6.8 for A_,; by Newman's lemma (1.2.8) uniqueness of normal form
readily follows.

8.2.2. NOTATION. Below we shall very often drop o in the notation for
composition, and simply write tti for tot', whenever this can be done without
impairing readability.                                                             El


DEFINITION. An expression denoting an arrow in CCC(PV) is called a com-
binator. An A-combinator is a combinator in CCC(PV) constructed without
ev, cur,
266                                                      Chapter 8. Categorical logic

8.2.3. THEOREM. Let A, B be conjunctions of propositional variables and
T, such that no propositional variable occurs twice in A and such that each
variable in B occurs in A. Then there is a unique A-combinator

         e AB: A   B.
Moreover, if A and B have the same variables, and also in B no variable
occurs twice, then AB is an isomorphism with inverse i3A
PROOF. We use a main induction on the depth 1B1 of B. If B = Bo AB1, we
put eAB := (eAB0) eABi) . For the basis case, B is either T or a propositional
variable. If B is T, take eAT := trA. If B is a P E PV, then B occurs as a
component of A and may be extracted by repeated use of Po, pi. This may
be shown by a subinduction on IA1: suppose A -a Ao A A1, then P occurs in
Ai for i = 0 or i = 1; take CAP    eA,P7ri
  The uniqueness of the A-combinator from A to B may be shown as fol-
lows. Again, the main induction is on IBI. Suppose [3: A      B is another
A-combinator. If B Bo A B1, then ir i o A/3 : A =- B. By the IH it follows
that ir i o AB = 7rio 0, but then AB = (7ro eAB 71 0 eAB) = (70 o ß, 7ri. 0 0)
=
    So we are left with the case of B prime. B = T is trivial; so consider
B = P for some variable P. We may assume that ß is written in such a way
that no associative regrouping 0' of ß (i.e. 13' obtained from i3 by repeated
use of the associativity for arrow composition) contains a subterm of one of
the forms 7ri o (t, s), id o t, t o id. Let 13 be written as (... (tot') tn) such
that no ti is of the form t' o t". tn cannot be of the form (t', t") , for then .B
could not be a variable, since this would require somewhere a projection 7ri
to appear in front of some (s', s") (use induction on n).
   So either n = 1 and then ß = id = AB, or n> 1, and then tn 7r0 or
depending on whether, if A          Ao A A,, P occurs in Ao or in Al. Suppose
tn    70, then (... (toti) tn_1) is an A-combinator of Ao         P; now apply the
IH, and it follows that (... (toti) tn-i) -= Clop, hence ß = eitoP 01rO = CAP.


8.2.4. DEFINITION. Let
              xi: Ai,    , xn: An,   CY       Bi,    ,      B,n

be lists of typed variables such that in e all variables are distinct, and such
that all variables in e' occur in 8. Put
         G := (.. . (P1 A P2)    Pa),     8' := (   (Q1 A Q2)      Qn)
such that Q3 = P iff yi = xi. By theorem 8.2.3 there is a unique A-combinator
      Now define ,800, as the combinator obtained by replacing pi by Ai in
the types of the components of eoc),. Furthermore put, for any list e:
8.2. Lambda terms and combinators                                             267

          e° := (... ((T A A1) A A2) ... A An).                                 [s]


The following lemma is then readily checked.

8.2.5. LEMMA. Let 8, 8' be as above, 8" a permutation of 8.

     /30,e = id; /3e,c13e,,,e = id;         =

     Sex,e,x = (00,e,70,7r].) if x 0 88';

            = ,(30,e, o 4, where in OT each variable occurs exactly once,
     and where 4 is a string of operators 7r0 of the appropriate types, of a
     length equa/ to the length of T;

     A)        = 4 o /30,0,, where each variable in e'T also occurs in 8, and
     where 741 is a string of operators 7r0 of the appropriate types, of a length
     equal to the length of W.                                                  El



8.2.5A. * Prove the lemma.

8.2.6. DEFINITION. (Mapping T from arrows in CCC(PV) to typed terms)
The mapping r assigns a typed term tB [xA] to each arrow from A to B in the
CCC(PV). r(t) has at most one free variable. We write 7-y(t) to indicate that
y is the letter chosen to represent the variable free in the expression r(t).

                                   A
          Tx (idA)             X       ,


          rx(trA)           := *,
                            := pixAAB
          Tx (AB
          rx((t 8))         := (TA Tx8)   P(Txt, Tx8),
          Tx (eVA'B)           (pox(A-4B)AA)(pix(ArB)AA),
          Tx (cur(t4^13-4)) := AzB .(AyAAB .ryt)(xA z.13),
          rx(t o s)         := (Ay.ryt)rxs.

One should think of the variable x in r(t) as being bound, i.e. what re-
ally matters is Ax.rx(t). However, the use of Ax.rx(t) is less convenient in
computations.                                                                   N


8.2.7. DEFINITION. (Mapping o from typed terms to arrows) Let tB be a
typed lambda term with its free variables contained in a list O. By induction
on It we define a combinator o-e(tB) : 8°    B.
268                                                      Chapter 8. Categorical logic

                           := SyTexAcy,xA,
                              evA'B(o-et, o-es),
                           := (Cret, eS),
                              CUr(Cf exA(tB)) (w.l.o.g. xA    6),
                              7rio-e(t) (i E {0, 1}),
                              tre°.

8.2.8. LEMMA. (7- preserves equality between combinators) For terms t,s
denoting arrows in CCC('PV) such that t = s we have r(t) = Tx(S).
PROOF. The proof is by induction on the depth of a prooftree for t = s. We
have to verify the statement for instances of the axioms, and show that the
property is transmitted by the rules. The latter is straightforward. For the
basis case of the axioms, we shall verify two complicated cases.
Case I. The axiom evcur. Let t: A A B       C.

        rx(ev(cur(t)70,71)) = (def. of T)
        (Ay.     (ev)) (Tx (cur(t)7o), Tx7ri) = (def. of T)
        (Ay.poy(piy))(rx(cur(t)7ro), Tx7r1) = (Own, Prop
        (rx(cur(t)70))(rx7i) = (def. of r)
        (Ay.ry(cur(t))7x70)(PixA^B) = (def. of T)
        (Ay! I Az.B .puAAB .Tu(t)) (yA zB)))(poxAA/3)(pixAAB) = (Own)
        (AuAna.
               TA\\/ Pox, Pix) =
        pkuAna.ruoxAAB = (ßeon) rut.

Case 2. The axiom curev.

        Tx(cur(ev(tro,r1))) = (def. of r)
            zB (411AB .Ty (ev(tro, ri))(xA, zB), abbreviated (*).

We observe that

            (ev(bro, 70) = (def. of T)
        Au(B-4C)1\B.Tu(ev)Ty((bro,71)) = (def. of T)
        (Au(B-W)AB .(POU) (P1u))(T0(bro),Ty7ri) = Pcon, Aron
                      (def. of    AxA.Txt) (poyAAB) (pi yAAB ).
        TY (t7r0 )7Y71 =              7) (

Therefore
        Tx (cur (ev(tro, 70)) = (*) =
        AzB.(AyAA.B., xA Txt)(POY)(PlY))(xA7 ZB) = (ficon, Proi)
        A.0.(AxA.Txt)xAzB = (ßcon) AzB.Tx(t)zB = (ncon) Txt.
8.2. Lambda terms and combinators                                            269

8.2.8A. * Complete the proof.

8.2.9. LEMMA. Let 8, 8' be lists of typed variables without repetitions,
such that all variables of e are in 8', and FV(t) is contained in8. Then

        0-01(0 = Cle(t)ßyTel,yTo.


PROOF. By induction on Itl. We check one case. Let t a AxA.s. Then
        ere, (t) = cur(o-cyxA(s)) = (IH)
        cur(o-exA (s)Ou-re,xA,y-rexA) = (8.1.5)
        cur (crexA (s))(ATcy,y-re)70 , iri) = (8.1.5)
        cur(o-exA(s)),(3y-re,,y-re = cro(AxA.$),3y-re,,y-re (def. of o`).     El


8.2.9A. * Complete the proof of the lemma.

8.2.10. LEMMA. (a® respects 0-conversion)
                         0.®((AxA.t.$)8A)        0.e(tn[xi v sA]).



PROOF. The proof proceeds by induction on Iti. We first note that

        cre ((AxA.tB)sA) = ev(cur(o-e (tB)), o-es) = o-e(t)(id, o-es).

Hence we only need to show

        o-ex(t)ry = o-e(t[x/s]) where 7 := (id, cre(s)).

If x is not free in t, then t[x/ s] E t, and o-exy = o-e70(id, o-e(s)) = o-e(t) =
o-e(t[x/s]). So we may concentrate on cases where x actually occurs free in t.
   We check the most complicated case of the induction step, and leave the
other cases to the reader.
 Case 1. Let t AyD.e.

        aex(t)7 = (def. of u)
        cur(o-oxy(e))7 = (8.1.5)
        cur (o-oxy (e) (77o, 7r1)) =
              (since Oz-rexml-eyx = ((rorch 7r1), mimo), and 8.2.9)
        cur (o-eyx (e)((7ro7ro, 70, 7r1.7r0)) (Tiro , 7r1)

Now
270                                                         Chapter 8. Categorical logic

          ueyx(e)((ro7ro,71),71.7ro) (77ro,71-1) = (8.1.5)
          Ueyx(e) ((7o7ro, 71) (77o, 71), 717o (77ro 71)) = (8-1.5, Pron
          Ueyx(e)((7ro7ro (77ro, 70,71(77o, 70), 7177o) = (Prop
          0-eyx(e)((7roWro,71),71.77ro) = (def. of -y)
          aeyx(e)(7ro(id,0-08)7ro,71),71(id, ues)7ro) = (Pron
          aeyx (e)((7ro,71-1), ue (8)70) = (surj)
          ueyx(e)(id, o-e(s)70) = (since o-e(s)7ro = o-ey(s) and 8.2.5)
          Creyx (e) (id, o-oy(s)) = (by 1H) crey(tqx/s1) hence
          a-e(t[x/s]) = cur(a-e0e[x/s]) = a-e(t)[x/s].                                E

8.2.10A. 4 Do the remaining cases in the proof of the lemma.

8.2.11. LEMMA. (a- preserves 07i-equality) If for lambda terms t, t' we have
t = t', then for all appropriate O, cr®t = a-et'.
PROOF. We prove this by induction on the depth of a deduction of t = t'.
Preservation under the rules is easy; we also have to check that the property
holds for axioms. For example, if x FV(t),

          a-e(Ax.tx) = (def. of u) cur(o-ox(tx) = (def. of u)
          cur(ev(o-oxt, 0-ex)) = (8.2.9) cur(ev((aet)70,71)) = (8.1.5) o-et.
Also a-e((Ax.t)s) = a-e(t[x/s]) by lemma 8.2.10. Other cases are left to the
reader.

8.2.12. LEMMA. (ax is inverse to Tx modulo a projection)
                                crxA(rx(t)) = t7T'A.


PROOF. By induction on t. We check two difficult cases of the induction
step and leave the others to the reader.
Case I. Let t cur(s), s: A A B C.
          crxrx(cur(s)) = (def. of T)
          CI x()ZB .(ÀyAr13 .7-0)(xA zgk)
                                       )      (def. of u)
          cur(o-xz(AyA'1 .7-ys)(xA , zB))) = (def. of u)
          cur(ev(o-x,(AyA'B.rys),o-x,(xA,zB))) = (def. of u)
          cur(ev(cur(o-xnrys), Orgro, 70)).
Now observe that
          axzy(TyS) = (8.2.9) (o-0rys)(7o7r0ro, mi) = (III)
8.3. Decidability of equality                                             271

Hence

         cur(ev(cur(o-x,yrys), (717ro, 71))) =
         cur(ev(cur(s71), (7170,71))) = (8.1.5)
         cur (s71 (id, (7170, 7))) = (proj)
         cur(s(7170,71)) = (8.1.5) cur(5)71.
Case 2. Let t     s o s', s:C     B,           C.

         o-xA(rx(ss')) = (def. of 7-)
         o-xA((Ayc .rys)rxs') = (def. of u)
         eVC'B(o-x(Ay.Ty8),CrxrxSt) = (def. of u)
         e-vc,B (cur (o-xyry s), 0-sTxSt, abbreviated (*).

Observe that
          xyry S = (8.2.9) o-yrys(7070,70 = (IH)
            (7070, 7riTAA,C)
                              (proj) s71TAA C    '




hence (*) is
         evc,B(cur(o-xyrys), axrx5') = (8.1.5)
         ev C B (cuRisrTAA,C s/rTAA,C%
                                ,     Ì     (8.1.5)
            Cg           ,/ \ ,TAA,C                   73TAA,C.
         ev      cur    5 Pi         (8.1.5) S o s/

8.2.12A. 4 Complete the proof.

8.2.13. THEOREM. For combinators t, s, t = s iff rx(t) = rx(s).
PROOF. If t = s then r(t) = rx(s) by lemma 8.2.8. If for two combinators
t, s: A  B we have r(t) = rx(s), we have by lemma 8.2.11 o-x(rx(t)) =
ax(Tx(8)), hence t71 = s7i:T A A =. B (lemma 8.2.12). Therefore t
tri (trA , idA) = sri (trA, idA) = s.


8.3      Decidability of equality
We consider here the question of decidability of equality between combina-
tors. First of all, we note that we can restrict attention to the case where A
and B are objects of CCC(PV) which do not contain T. To see this, one ob-
serves that any object B constructed from PV, T by means of A, -4 is either
isomorphic to T or to an object B' not containing T. This follows from the
isomorphisms (cf. 8.1.6A):

                                  A>T- T;
272                                                    Chapter 8. Categorical logic

By the results of the preceding section, the problem is equivalent to comparing
closed terms in A71A. By proving strong normalization and uniqueness of
normal form for Arr.,A we obtain decidability between the lambda terms, hence
between the combinators. (In the calculus Aii,AT uniqueness of normal form
fails, see 8.3.6C.)


8.3.1. We extend the results of section 6.8 in a straightforward way; the
method uses a predicate "Comp" as before. We use -4, V and A also on the
metalevel, as in the following definition.


DEFINITION. For each formula (type) A in the A>--fragment we define the
computability predicate CompA, by induction on the complexity of A; for
prime A and A B > C the definition is as before (6.8.2), for A -= B A C
we put
         ComPosnc (t) :=
                    SN(t) A Vtit"(t -- p(t', t")   CompB (e) A Compc(t"))

8.3.2. LEMMA. The properties C1-4 of lemma 6.8.3 remain valid for CompA
PROOF. The proof proceeds by induction On the complexity of A, as before.
We have to consider one extra case for the induction step, namely where
AaBAC.
  Cl is trivial in this case, since included in the definition.
       If t h t*, then obviously ComPBAc(t*) since SN(t*) follows from SN(t)
and if e - p(t', t"), then also t »- p(t', t").
       Assume Vti -- it(ComPanc(ti)), and t non-introduced, that is to say
not of the form p(t', t"). It is obvious from the assumption that SN(t). As-
sume t »- p(t', t") in n steps. n = 0 is excluded since t is non-introduced;
so there is a t1 such that t --1 t1 p(ti, t"); it now follows that CompB(e),
ComPc (t").
   For the induction step where A a B       C, we have to take 77-conversion
into account, but this does not change the proof.

8.3.3. LEMMA. VS E CompA (CompB (t[xls]) -4 Comp,4B (Ax.t) )           .




PROOF. We extend the proof of lemma 6.8.4. There is only one extra case if
(Àx.t)s >-1 t", namely

      t a t'x, t"     s.

But also in this case CompB(t") by the assumption.
8.3. Decidability of equality                                                  273

8.3.4. LEMMA. CompB(t) A Compc(e)                     ComPBAc(P(t, ti))
PROOF. p(t, t') is strongly normalizable. For consider any reduction sequence
of p(t, t'):

             t" a- p(t, t') »-i 4 ».-1 4 >--1

If there is no step in the sequence where

(1)          4     P(tn, tin)    P(Pot41, Pot4i)        t'941

occurs, the reduction sequence is essentially a combination of reduction se-
quences of t and t' and hence bounded in length by ht + he. If on the other
hand there is a first step as in (1), then the length of the reduction sequence
is bounded by ht + he + 1, since the reduction tree of t',/, is embedded in the
reduction tree of t.
   Now assume p(t, t') p(s, s'). Then either this reduction is obtained by
reducing t to s and t' to s', and then CompB(s), Compc(s') follow; or the
reduction sequence proceeds as

             P(t, t')   P (Pot", Pit") - t"     p(8, s'),

where t h pot", t'       pit". But in this case, also t pot" »- pop(s,s') >--1 s,
t' »- pot" »- pip(s, s') »-i s', and therefore CompB(8), Compc(8').

8.3.5. THEOREM. All terms of An..+A are strongly computable under substi-
tution, and hence strongly normalizable.
PROOF. The proof extends the proof of section 6.8 by considering some extra
cases.
Case 4. t   pot'. We have to show that for any substitution * with com-
putable terms, e is computable. e po(t'*), and by the induction hypothe-
sis t' is computable. So it suffices to show that whenever CompBAc (s), then
CompB(pos) for arbitrary s of type B A C. This is done by induction on h3.
Since pos is non-introduced, it suffices to prove CompB(t) for all t pos. If
t pos, then either
         t     p0(5') with s'       s; then CompB(t) by induction hypothesis, or
         s     p(s', 3"), t     s'; CompB(t) is now immediate from CompBAc(s).

Case 5. t   pit' is treated symmetrically.
Case 6. t    p(to, ti). We have to show that for a substitution * with com-
putable terms, e p(4, VI) is computable; but this now follows immediately
from the induction hypothesis plus lemma 8.3.4.
274                                                    Chapter 8. Categorical logic

8.3.6. PROPOSITION. Y-1 is weakly confluent and hence normal forms in
)tiv,A are unique.
PROOF. The proof of this fact proceeds as for A, (cf. 1.2.11).                    Z

8.3.6A. 4 Prove the confluence of terms in Avv,A.

8.3.6B. 4 Show that in Arv,A long normal forms (cf. 6.7.2) are unique. Hint.
Show by induction on the complexity of t that if t,s are expanded normal and
t     8, then t -a s.

8.3.6C. 4 Give an example showing failure of confluence in An_.>AT. Hint. Con-
sider p(pot, pit) with pot or pit of type T, or AxA.tx with tx of type T, x 0 FV(t).


8.4 A coherence theorem for CCC's
Coherence theorems are theorems of the following type: given a free category
C of a certain type (here cartesian closed) and objects A, B of C satisfying
suitable conditions, there is exactly one combinator from A to B (modulo
equality of arrows in a category of the given type). In this section we prove
a coherence theorem for CCC(PV); the proof is based on Mints [19924

8.4.1. NOTATION. In this section we write I- I'               A if A is deducible
from open assumptions I' in A>-Nm (cf. 2.1.8). In term notation we write
g: r       t: A, or sometimes more compactly t[ fi': 1]: A or trill: A. We write
[x: B], il: I'    A, or [x-B], il: I' A to indicate that the assumption xB may
be either present or absent.                                                   N

8.4.2. DEFINITION. A A>-formula A is balanced if no propositional variable
occurring in A has more than one occurrence with the same sign (so there
are at most two occurrences of any propositional variable, and if there are
two, they have opposite signs). A sequent I'  A is balanced if the formula
A I' > A is balanced.                                                    El

The theorem which we shall prove is

8.4.3. THEOREM. (Coherence theorem) Let A, B be objects of CCC('PV)
not containing T. If A B is ba/anced, there is at most one combinator in
CCC(PV) from A to B.
The theorem is obviously false if we drop the condition of balance: in A there
are two distinct arrows f , g : Po A Po    Po A Po, namely idP°^P° a (70, 71),
and (r1, 70). The theorem will first be proved for so-called 2-sequents.
8.4. A coherence theorem for CCC's                                           275

8.4.4. DEFINITION. A 2-sequent is a sequent of the form F               R, where
each formula in F has one of the following forms:

         P + P', (P          P') + P", P"   (P     P'), P"     P A P'
for distinct P, P', P" E PV

8.4.5. PRoPosiTioN. Let Y: F        t: R be a /3n-normal deduction term for a
2-sequent. Then t has one of the following forms:

      xR ,

      xP'(Q--,R)trt?,
      xQ-Rt?,
      x(P-+Q)-4 R yP -4Q ,

      x(P'Q)'R(AyP.t?),
      x(P-sQ)-4R (yP'        Q)tri

      po (xP-rRAQtr or pi (xP' QARtp),

where t1, t2 are again normal.
PROOF. If t is not a variable (case (a)), t represents a deduction ending
in an E-rule; a main branch must therefore begin in an open assumption,
corresponding to a variable. Since        R is a 2-sequent, we have the following
possibilities. In the first three cases we assume that the final rule is --+E.
      The open assumption is of the form x(Q'R); this yields case (b).
      The open assumption is of the form XP 41 (case (c)).
      The open assumption is of the form x(Q)R, and t has the form
X(P-4Q)- RtP0-+Q . to may either be a variable (case (d)), or end with *I (case
(e)), or end with an E-rule. In the third subcase, the main branch of to mUst
start in an open assumption, i.e. a variable yPi -4(P   ; this yields case (f) of
the proposition.
       Now assume that the final E-rule is AE. The open assumption is of the
form P --+ R A Q or P --+ Q A R; this yields case (g).                         N


8.4.6. LEMMA. If F             R, R E PV is derivable, then R has a positive
occurrence among the formulas of r.
PROOF. F        R is intuitionistically true, hence classically true; if R has no
positive occurrences in F, we can take a valuation v with v(R) = I, v(Q) = T
for all Q distinct from R; this would make r true and R false.
276                                                 Chapter 8. Categorical logic

8.4.7. LEMMA. Let 1: F          t: R be a /3r-normal deduction term for a 2-
sequent. Then any propositional variable occurring negatively in F also occurs
positively in F.
PROOF. By induction on ti, using proposition 8.4.5 to distinguish cases. We
shall leave most of the cases to the reader.
Case (b). t    x4R)trt?        , t1, t2 also normal. For negative occurrences of

propositional variables in the sequents corresponding to t1, t2 we can therefore
apply the 1H. Q in the type of x is a negative occurrence; but il:         t2: Q
plus the preceding lemma shows that r c r necessarily contains a positive
occurrence of Q.                                                              El


8.4.7A. 4 Do the remaining cases of the proof.

8.4.8. DEFINITION. Let S : F R be a balanced 2-sequent. An S-sequent
is a sequent    Q where r' c r, Q occurs positively in S, and A is a list
of propositional variables such that if P E A then a formula (P       P1)    P2
occurs in F.

8.4.9. LEMMA. Let S: r         R be a balanced 2-sequent, and let A E r be a
formula with a strictly positive occurrence of R. Then all positive occurrences
of R in the antecedent of any S-sequent are in a single occurrence of A.
PROOF. Strictly positive occurrence of R in A, A occurring in the antecedent
of a 2-sequent, means that A has one of the forms P --+ R, P'         --+ R),
P >RAPI,P> P' A R. We argue by contradiction. Let r'A                 .0C2 be an
S-sequent containing a positive occurrence of R not in A.
  The occurrence cannot be in ry, because then S would be unbalanced, since
   C P. Also, the occurrence can not be in A, because then r would contain
      P1)    P2 for certain P1, P2, again making S unbalanced.

8.4.10. DEFINMON. An occurrence A E r, r              R a 2-sequent, is called
redundant in the sequent if A contains a negative occurrence of R (so A is of
one of the forms R --> P2, Pi -+ (R -4 P2), (P1 -> R)    P2, R    (P1 -4 P2) ,
R Pi A P2).

8.4.11. LEMMA. Let S be a balanced 2-sequent,         R an S-sequent,
g: r   t: R a normal deduction term. Then r contains no redundant ele-
ments.
PROOF. We use induction on It', arguing by cases according to 8.4.5.
Case (a). t a xR. r R has no negative occurrences, hence no redundant
members.
8.4. A coherence theorem for CCC's                                                  277

Case (b). t         xR-4(Q-4R)tiRt?. Then [xP-4(Q-+R)],     Fi    ti: P and
[xP-4(42-'9,2': r2   t2: Q represent deductions of S-sequents, hence x must
be absent, by the IH. P -+ (Q R) contains a strictly positive occurrence
of R, so the preceding lemma applies and we see that r1, r2 contain no pos-
itive occurrences of R. And thus by lemma 8.4.7 there is also no negative
occurrence of R.
   The other cases are left to the reader.

8.4.11A. é Do the remaining cases of the proof.

8.4.12. PROPOSITION. (Coherence for 2-sequents) Let F    R be a bal-
anced 2-sequent, g: F' t: R, F" s: R normal deduction terms such that
    r" c F     ,      r) u (il: r") = 2 r for suitable g. Then I" = r"            r and
t   s.
PROOF. By induction on it + Isl. Assume iti> isi. We use a case distinction
according to proposition 8.4.5.
 Case (a). t is a variable; then t xR s.
 Case (b). Suppose t         x)trt?. The term s' cannot have one of
the other forms, since this would yield that there were two distinct positive
occurrences of R in F. Therefore s               sf4. Furthermore
         [xP'(Q-'1)1,               t1: P,    [xP'()], g2: F          t2: Q,
                                    s 1: P,   [x(')],                  s2: Q.

P -> (Q    R) F       Pisa (r R)-sequent. In this sequent P (Q --> R)
is redundant, since it contains a negative occurrence of P. Then M.:
t1: P, and similarly

         il2   1-      t2: Q,           si: P,    1-i     s2:Q.
It follows that ill: F U     rg and p'2: F'2 U 2'2: are again balanced, and we
can apply the induction hypothesis.
 Cases (c) and (d). Similar, and left to the reader.
 Case (e). t    x(R-'0'R(AyP.t?). The possibility that s falls under one of
the cases (a)-(c), (g) is readily excluded. For (e) we can argue as in case (b)
above, using the IH. The possibilities (d) and (f) can both be excluded; since
the argument is similar in both cases, we restrict ourselves to (f). So we have
         s = x(P-40-+R(ypi-qP-+Q)(8/)Pi).

The terms t and s correspond to deductions
                            ti: Q                            z : P'      (P Q)    s' : P'
X: (P    Q) -> R        Ay.ti: P    Q     x: (P   Q) -4 R              zs': P Q
         t
278                                                      Chapter 8. Categorical logic

s': P' is a normal deduction of

                 [(P + Q) --+ R], [P' + (P        Q)],         P'.
z: P' + (P Q) is redundant, hence absent in s'. But then x: (P --+ Q) R
is also absent, since Q is a negative occurrence in F, while another positive
occurrence outside R'      (P --+ Q) ought to be present but cannot be present
since this would make F       R unbalanced.
   Among the assumptions of ti there must be positive occurrences of Q; also

        c {(P --+ Q) --+ R, P'         (P + Q),Fn U {(P         Q)    R,

But then these must coincide with P' --+ (P              Q) in PI (otherwise there
would be two positive occurrences of Q in r); and since Q is strictly positive
in P'    (P Q), this is the only occurrence in I). This would give as the
only possibility for ti

                      z:          (P     Q) t2:./31
                              zt2: P      Q          t3: P
                                       ti (zt2)t3: Q
But again from the balancedness of F'         R it follows that apart from the
occurrence of P in (P     Q) > R there can be no other positive occurrence
of P in F. Hence t3: P must be the bound assumption variable yP , which
contradicts the 77-normality of t (for if t3 is not a variable, the main branch
of the subdeduction of t3: P must contain another positive occurrence of P).
  The cases (f) and (g) are left to the reader.

8.4.12A. * Do the remaining cases of the proof.

8.4.13. Reduction to 2-sequents. Let us assign to a formula a "deviation"
which measures the deviation of the formula from a form which is acceptable
as antecedent formula in a 2-sequent:

        dev(B > C) := IBI +             dev(B A    := IBI      ICI + 1.

For a multiset F, let n be the maximum of the deviations of formulas in F,
and let m be the number of formula occurrences in r with deviation n. If we
replace, in a multiset with formulas of deviation > 0, a formula A of maximum
deviation by one or two formulas FA according to a suitably chosen line in
the table below, either n is lowered, or n stays the same and m is lowered.

DEFINITION.    (Deviation reductions) A formula A which has a logical form
not permitted in the antecedent of a 2-sequent may be replaced by a set PA
8.4. A coherence theorern for CCC's                                                    279

with at most two elements; we also define for each replacement a term OA,
according to the following table. The propositional variable P is fresh.

         A              rA                 sbA

(a)      B -+ C         B _), p, p _), c   AuB .zp-W (yB-)PuB)

(b)      (D -+ B)   CB        P,           AuD-03 .z(D-)P)-W (AvD .yB-)P (uD-rB vD))

                        (D Y P) -+ C
(C)      (B -+ C)   D P > B,               AuB-W .z(P-W)-03 ovP .uB-)C (yP-)B vP))

                        (P > C) Y D
(d)      BACYD       B>(C>D)               AUBAC .yB-r(C-r.13)(pou)(piu)

(e)      C > (D > B) C (D > P),            Au0AvD.z.13 (yC-)(D-)P)uC vD)

                        P>B
(f)      BAC            B,C                013   ,z9
(g), DBAC DPAC,                            Au]) 0P-r.13 (po (zD(PAC)u)), pi (zD-(PAC)uD))

                        PYB
(g),     DCAB           D>CAP,             AUD (po (z.D.(CAND) y P-03 (pi (zDr (CAP)up))

                        P>B
 FA is not uniquely determined by A, but by A together with a subformula
occurrence B in A, which is represented in FA by a new propositional variable
P. In all cases except (d) the free variables of the OA are {y, .z}; in case (d)
y is the only free variable. Note that by a suitable substitution for the new
propositional variable P in rA we get A back.
   Repeated application of appropriate deviation reductions to a multiset
results ultimately in a multiset A, from which I' is recoverable by a suitable
substitution in the propositional variables, and such that A consists of for-
mulas of one of the following forms only: P, P          P', P (P' > P"),
(P > P') --+ P", P > P' A P". Thus A is almost the antecedent for a 2-
sequent, except that P, P', P" are not necessarily distinct. But further trans-
formation to a 2-sequent can be achieved, again using the replacements in the
table above; for example, (P P') --+ P' may be replaced by (P > Q)          P',
Q     P', with Q a fresh propositional variable. Summing up, we have shown:

LEMMA. Repeated replacement of formulas A by PA for a suitable choice
of reduction rule from the table above in a sequent A R terminates in a
2-sequent.                                                                              N


8.4.14. LEmmA. Let A, P A and OA correspond according to one of the lines
of the table in the preceding definition. Let P be a propositional variable not
occurring in AA         B. Let ft. be the new variables appearing as free variables
in OA. Then

      (i) If AA     B is balanced, so is               B.
280                                                     Chapter 8. Categorical logic

      If x: A,        t: B, then 17: rA,          t[x/ 0,4]: B.

      If x: A, g: A t:B and x: A, il:     s: B, then t =fln s iff t[x/0,1] =fln
      S [XNA] and x is On-equal to some substitution instance of 0A[p/E] for
      a suitable formula E.

Here OA[p[E] is obtained from OA by substituting in the the types of all vari-
ables (free and bound) of OA the formula E for the proposition variable P.
In fact, it will turn out that for E we can always take B as appearing in the
table of the preceding definition.
PRooF. (i) by direct verification. (ii) is obtained by combining ti: rA (here
77 are the free variables of OA) with x: A, il: A      t: B (using closure under
substitution for prooftrees in N-systems).
        Assume x: A, g: A     t: B and x: A, g : A   s: B. Suppose first t =on s.
Then t[x/ OA] =on s[x/OA] holds because [397-conversion is compatible with
substitution.
   Conversely, suppose t[x/OA] =fln s[xAbA]. Choose a substitution of a for-
mula E for the propositional variable P in OA suc-h that A becomes logically
equivalent to the conjunction of r A[pi El (in fact, for E we can always take B
in the table of the preceding definition), and a substitution [q1] in (/) A{p E],
such that OA[pig[ii/r] =fln x. Then this shows that t =pn s. The appropri-
ate substitution [ft/f1 is defined according to the cases of the table in the
foregoing definition.
 Case (a). A[P/B] Aus.zB>C(yrisus ) Substitution [y, z/AvA.t), XA-+B].
 Case (b). OA[p/B]           z(13)-C pkvD .yB-+B (11D-YB vB)).
Substitution [y, z pkwa .w x(D-g3)-495
Case (c). Similar to the preceding case, and left to the reader.
Case (d). There is no propositional substitution.
Substitution [y/AvBAwc.xBAC-+Dp(vB ,wC)].
Case (e). Substitution [y, z/x          +B) AwB.wi.
Case (f). Substitution [y, z/poxBAC ,pixBAC].
Case (01. Substitution [y, z/AwB .w x D-4AB1
                                          C j for y, z.

Case (02. Similar to the preceding case.                                          N

8.4.14A. 01 Check the missing details.

8.4.15. LEMMA. For any sequent A B, with A = A1,                ,A, there are a
2-sequent r      R, a sequence of terms s= sl, . ,s,-, and a term r, in variables
                                                  .


el: r, such that
      If 1: A    t: B, then fi:       r(t[Vg]): R.
      If g: A    t: B, g: A       t': B, then t =on s ifir(t[g/3])., r(tIV§.1).
8.5. Notes                                                                  281

 (iii) If A   B is balanced, so is r    R.

PROOF. We consider the sequent AB * R             R (R a fresh propositional
variable). If A         t: B then A, V: B        R      vt: R. Conversely, if
Y: Ls., y: B  R      vt: R, we can substitute B for P, AtoB .toB for y, and
we get Y: A     t: B back, using the fact that AwB .wB : B -4 B and the fact
that the deduction terms are closed under substitution. Now repeatedly ap-
ply the preceding lemma to I: y: B           R    t: R until we have found a
2-sequent as in the statement of the lemma of 8.4.13.

8.4.16. Proof of the coherence theorem. This is now almost immediate: an
arbitrary combinator from A to B in CCC(PV) with A * E balanced is
representable by a lambda term; this may be seen as deduction term of a
sequent. Lambda terms for balanced r B are in bijective correspondence
with arrows for a suitable 2-sequent by the preceding lemma, and for arrows
between 2-sequents the coherence theorem was proved in proposition 8.4.12.


8.5      Notes
8.5.1.   The presentation in the first section is inspired by Lambek and Scott
[1986], but in the next section, in the treatment of the correspondence between
terms in the .\it-calculus and arrows in the free cartesian closed category we
have followed Mints [1992b]. The treatment of strong normalization for typed
A71-+A extends the earlier proof for A. The first proof of the extension was
due to de Vrijer [1987]; a proof by a quite different method, reducing the *A-
case to the implication case, is given in Troelstra [1986], see also Troelstra
and van Dalen [1988, 9.2.16].

8.5.2. Coherence for CCC's. Mints [1979] indicated a short proof of the co-
herence theorem for cartesian closed categories for objects constructed with --*
alone; Babaev and Solovjov [1979] proved by a different method the coherence
theorem for -4A-objects. Mints [1992d] then observed that the properties of
the depth-reducing transformations (our lemmas 8.4.14, 8.4.15) established
in Solovjov [1979] could be used to give a simplified proof (similar to his proof
for the -4-case) for this result. The depth-reducing transformation as such
was already known to Wajsberg [1938], and to Rose [1953]. Our treatment
follows Mints [1992d], with a correction in proposition 8.4.12. (The correction
was formulated after exchanges between Mints, Solovjov and the authors.)
   There are obvious connections between these results and certain results on
so-called BCK-logic. In particular, it follows from the -4A-coherence theorem
that for balanced implications *A-I is conservative over the corresponding
fragment of BCK-logic. See, for example, Ja6kowski [1963], Hirokawa [1992],
282                                                  Chapter 8. Categorical logic

Hindley [1993]. In the direction of simple type theory, this "ramifies" into
theorems counting the number of different deductions of a formula (type).

8.5.3. Other coherence theorems. There is a host of coherence theorems for
various kinds of categories; some use, as for the result sketched here, proof-
theoretical methods, by reduction to a logical language (usually a fragment of
the typed lambda calculus), for example Mints [1977], Babaev and Solovjov
[1990]; others use very different methods, for example, Joyal and Street [1991].
  In Kelly and Mac Lane [1971] the presentation of a coherence result for
closed categories is entirely in terms of categories. However, inspired by
Lambek [1968,1969], the proof uses an essential ingredient from proof theory,
namely cut elimination (cf. Kelly and Mac Lane [1971, p. 101]). The results of
Kelly and Mac Lane [1971] are extended and strengthened in Voreadou [1977]
and Solovjov [1997].
  Lambek [1968,1969,1972] systematically explores the relationships between
certain types of categories and certain deductive systems, in the spirit of our
first section in this chapter. The first of these papers deals with categories
corresponding to the so-called Lambek calculus, the second paper deals with
closed categories, and the third paper with cartesian closed categories; it
contains a sketch of the connection between extensional typed combinatory
logic (which is equivalent to An) and arrows in the free CCC(PV). A different
treatment was given in Lambek [1974], Lambek and Scott [1986].
   The link between (a suitable equivalence relation on) natural deduction
proofs and arrows in free cartesian closed categories was made more precise
in Mann [1975].
   Curen [1985,1986] also investigated the connection between the typed
lambda calculus and CCC's; in these publications an intermediate system
has been interpolated between extensional A71 and the categorical combina-
tors. Hardin [1989] investigates ChurchRosser properties for (fragments of)
these calculi.
Chapter 9

Modal and linear logic

Another possible title for this chapter might have been "some non-standard
logics" , since its principal aim is to illustrate how the methods we introduced
for the standard logics M, I and C are applicable in different settings as well.
   For the illustrations we have chosen two logics which are of considerable
interest in their own right: the wellknown modal logic S4, and linear logic.
For a long time modal logic used to be a fairly remote corner of logic. In
recent times the interest in modal and tense logics has increased considerably,
because of their usefulness in artificial intelligence and computer science. For
example, modal logics have been used (1) in modelling epistemic notions such
as belief and knowledge, (2) in the modelling of the behaviour of programs,
 (3) in the theory of non-monotonic reasoning.
   The language of modal logics is an extension of the language of first-order
predicate logic by one or more propositional operators, modal operators or
modalities. Nowadays modal logics are extremely diverse: several primitive
modalities, binary and ternary operators, intuitionistic logic as basis, etc. We
have chosen S4 as our example, since it has a fairly well-investigated proof
theory and provides us with the classic example of a modal embedding result:
intuitionistic logic can be faithfully embedded into S4 via a so-called modal
translation, a result presented in section 9.2.
   Linear logic is one of the most interesting examples of what are often called
 "substructural logics" logics which in their Gentzen systems do not have all
the structural rules of Weakening, Exchange and Contraction. Linear logic
has connections with S4 and is useful in analyzing the "fine-structure" of
deductions in C and I. In section 9.3 we introduce linear logic as a sequent
calculus Gel and sketch a proof of cut elimination, and demonstrate its ex-
pressive power by showing that intuitionistic linear logic can be faithfully
embedded in Gcl. The next section shows for the case of intuitionistic impli-
cation logic how linear logic may be used to obtain some fine-structure in our
standard logics. Finally we leave the domain of Gentzen-system techniques
and discuss the simplest case of proofnets for linear logic, which brings graph-
theoretic notions into play (section 9.5). Proofnets have been devised so as to
exploit as fully as possible the symmetries present in (classical) linear logic.
                                      283
284                                                  Chapter 9. Modal and lineariogic

9.1          The modal logic S4
The modal theory S4 discussed in this section includes quantifiers; for its
propositional part we write S4p. The language of S4 is obtained by adding
to the language of first-order predicate logic a unary propositional operator
D. DA may be read as "necessarily A" or "box A". The dual of D is 0; OA
is pronounced as "possibly A" or "diamond A"; OA may be defined in S4 as


9.1.1. DEFINITION. (Hilbert system Hs for the modal logic S4) A Hilbert
system for S4 is obtained by adding to the axiom schemas and rules for
classical logic Hc the schemas
             DA -4 A (T-axioms)
             D(A   B)    (DA -4 DB) (K-axioms, or normality axioms)
             DA -4 ODA (4-axioms)
and the necessitation rule:
DI           If I- A then F- OA.
The notion of a deduction from a set of assumptions r may be defined as
follows.
   The sequence A1,   , An is a deduction of r F- A (A from assumptions r)

if A An, and for all Ai either
        Az E r, or
        there are j, k <i such that Ak               Ai, or

        Ai     Vx4i, j <i, x not free in r, or
        Ai    DAi, j < i, and there is a subsequence of A1,           ,A which is a
        derivation of I- A.
     An alternative formulation of a "deduction from assumptions" is as follows:
a deduction is a tree constructed starting from (r, z sets of formulas)
             r F- A (A E r)                      A (A axiom)
by means of rules.
              r I- A                             -A DI
             P, B F- A                       I- DA

                               F- A
                                      -4E
                                                 r         VI (x   Fv(r))
                                             r       VxA
9.1. The modal logic S4                                                    285

REMARK. Instead of -4E, DI one usually talks about "modus ponens" and
"necessitation" (or "rule N") when discussing Hilbert systems. The designa-
tion "axiom K" or "K-axiom" ("K" from "Kripke") is standard in the litera-
ture on modal logics. "Axiom K" is also used in the literature for the axiom
(schema) A -+ (B          A), because of the connection with the combinator
called K (in standard notation for combinatory logic) via the formulas-as-
types parallel. In order to avoid confusion we have used in this text k for the
combinator, and k-axiom for an axiom of the form A > (B -4 A).

9.1.2. LEMMA. The deduction theorem
           If P,AF-B then FF-A-4B
and the generalization of DI
           If 0131,    ,OBH A then 0.131,     ,   0./3,1 I- OA

are derived rules in Hs.
PROOF. We leave the proof of the deduction theorem to the reader. The
generalization of the necessitation rule is proved by induction on n. Suppose
we have already derived for all or of length n that Or I- A         or h DA.
Now let or, OA I- B. Then
           or     DA   B (deduction theorem)
           or I- 0(0A -4 B) (induction hypothesis)
           or h DDA OB (normality axiom, modus ponens)
           or H DA -4 OB (4-axiom, transitivity of >).
Hence with modus ponens and or, DA h DA we find or, DA I- OB.

REMARK. One often finds in the literature the notion of a deduction from
assumptions formulated without restriction on the rule DI, i.e.
                F- A
         r H DA
Let us write 1-* for the notion of deducibility with this more liberal rule of
necessitation. Forl-* we can prove only a "modal deduction theorem" , namely
           If r, A F-* B, then r h* OA > B.
In fact,
             F-* B iff   01'1-* B iff or B.
Of course, the generalized DI of the preceding lemma is now trivial. We
have chosen the definition in 9.1.1, because it is more convenient in proving
equivalences with Gentzen systems and systems of natural deduction.
286                                                      Chapter 9. Modal and linear logic

  In the notion of "deduction from assumptions" in first-order predicate logic
we formulated the rule VI as: "If F I- A, then F VxA, provided x FV(F)".
The variable restriction on VI is comparable to the restriction on DI (namely
that the premise of OI is derived without assumptions). An alternative version
of VI, "If F F- A, then r H VxA" without the condition "x     Fv(r)" is
analogous to the strong version of DI considered above. The unrestricted
VI also entails a restriction on the deduction theorem, which now has to be
modified as "If F, A I- B then F H VA     B" where VA is the universal closure
of A.

9.1.2A. 4 Defining "deduction from assumptions" as in the preceding remark,
prove the modal deduction theorem and the equivalences r H. B ifOr     B iff
Or I- B.

9.1.2B. 4 Prove modal replacement for S4p in the following form:
                              0(A        B)    (F[A]         F[B])

for arbitrary contexts F[*]. Refine this result similaxly to 2.1.811.

9.1.3. DEFINITION. (The Gentzen system Gis) This calculus is based on
the language of first-order predicate logic with two extra operators, O and O.
To the sequent rules of Gic we add
                   A =- A                 DF          B, OA
           LO I"'                   RE
                F, DA =. A                or          DB, OA

                 or A OA                       r        A, A
           LO
                OF, OA =. OA
                                         RO
                                               r       OA, A

From these rules we easily prove OA            4--F            as follows:
                    AA _1_                         A     A     1
                     A,
                                                                A
                    A, 0-1A
                                                         -IA, OA
                    OA, 0-,A
                                                        O-,A, OA
                  OA, 0-1A      1                       -11:1-1A     OA
                                                                        _L


                  OA =-

So it suffices to add LO, RO (with A = O in Ro), or LO, RO (with r = O in
LO).

9.1.3A. A Show the equivalence of the Hilbert system Hs with Gis in the fol-
lowing sense: treat 0 as defined and show r I-- A in Hs iff GYS  A, for sets
r.
9.1. The modal logic S4                                                    287

9.1.3B. 4 Formulate a one-sided sequent calculus for S4.

9.1.4. DEFINITION. (The Gentzen system G3s) A version of the sequent
calculus where Weakening and Contraction have been built into the other
rules is obtained by extending G3c with the following rules:
                     OA      A                       OF       A, 0A
         LO F' A'                          RO
                r, DA       A                   F', OF       OA, 0A, A'

         LO
                    OF, A    0A
                                           RO
                                                r       A, OA, A
               F', DF, OA        0A, A'             F    OA, A              IE

In order to retain the symmetry both 0 and 0 have been adopted as primi-
tives.

9.1.4A. 4 Prove that Contraction is derivable for G3s.

9.1.5. THEOREM. Cut elimination holds for G3s, Gis.
PROOF. For G3s, we can follow the model of the proof for G3c. Let us
consider the case where the cut formula DA is principal in both premises of
the Cut rule, so the deduction with a critical cut as last inference terminates
in

                                  D1                    D2
                          Or -} A, OA'      F,A, OA A
                      F", or DA, OA', A" F, DA A
                            F, 1', DF' A, A", OA'

This is transformed into
                                      Di
                                  or    A, OA'           D2
               D1           F", DF'    DA, OA', A" r, A, DA     A
                                                                  Cut
         DF'    A, OA'            In r, DF', A A, OA', A"
                                                            Cut
                    F, 1', DF', DF'A, OA', OA', A"

The extra cut is of lower degree, and the rank of the subdeduction ending
in the cut of maximal degree is lower than in the original deduction. By
the induction hypothesis we know how to eliminate cuts from this deduction;
then we use closure under Contraction to obtain a cutfree deduction of the
original conclusion.
   Cut elimination for Gis does not work directly, but via introduction of the
"Multicut" rule, as in 4.1.9.
288                                                   Chapter 9. Modal and linear logic

9.1.5A. 4 Complete the proof of the theorem and describe cut elimination for
Gis with the help of "Multicut".

9.1.5B. 4 Formulate a G3-type system for the logic K, defined as S4, but with
only K-axioms, no T- and 4-axioms. Prove a cut elimination theorem for this
system.


9.2       Embedding intuitionistic logic into S4
9.2.1. DEFINITION. (The modal embedding): The embedding exists in sev-
eral variants. We describe a variant °, and a more familiar variant °. The
definition is by induction on the depth of formulas (P atomic, not I):
          P°          := P                    p0            := OP
          _L°                                          :=
          (A A B)° := A° A B°                 (A A     := A° A B°
          (A B)° := OA° V DB°                 (A V B)° := A° V B°
          (A -4     := OA° B°                 (A -+              D(A°     B°)
          (3xJ1.)°    := ]x1=1A°              (AxA)°        := ]xA°
          (VxA)°      := VxA°                 (VxA)°             LIVxA°

9.2.2. PROPOSITION. The two versions of the modal embedding are equiv-
alent in the following sense: S4 I- OA° i4 A° and hence S4 I- Or° A° iff
S4 F- rci    A°.

9.2.2A. 4 Prove OA° 44 A° by induction on the depth of A.

9.2.3. THEOREM. The embeddings ° and ° are sound, i.e. preserve de-
ducibility.
PROOF. It is completely straightforward to show, by induction on the length
of a deduction in G3i, that if G3i F- r               A, then G3s               A°. We
consider two typical cases of the induction step, namely where the last rule
in the G3i-deduction is L-4, R-4 respectively.
   L-4: the deduction terminates with
                                                     r, B    c
                                      r, A   B       C
which is transformed into
                                                    r°, B°
                r°, o(A°     B°)       A°    r°, o(A° -4 B°), B°          C°
                           r°, o(A°      B°), A° -4 B°        C°
9.2. Ernbedding intuitionistic logic into S4                                       289

The transition marked by the dashed line is justified by a weakening trans-
formation applied to the proof of F°,          .

  R+: We use as a lemma, that DA° ÷-> A° for all A (proof by induction on
IAI). The deduction in G3i terminates in
                                  r, A B
                                F     A  B
which is transformed into
                                       r°, A°
                                   ro          AD .4 Bo
                                  Dro  AD _+ Bo Cuts
                                 Dro  0(A0   Bo)
                                                 Cuts
                                 r°    B°)
where the "Cuts" are cuts with standard deductions of DC°                  C°,
DC° (C E r).
  So apart from these cuts, the transformation of deductions is straightfor-
ward. A direct proof of soundness for ° requires more complicated cuts. Z

9.2.3A. 4 Complete the proof.

9.2.4. More interesting is the proof of faithfulness of the embeddings. We
prove the faithfulness of ° via a number of lemmas.

DEFINITION. Let F be the fragment of S4 based on A, V,                  D. We
assign to each deduction D in the .F-fragment of G3s a grade p(D) which
counts the applications of rules in D other than R>, RA, RV. More precisely,
the assignment may be read off from the following schemas, where p, p' are
grades assigned to the premises, and the expression to the left of the conclu-
sion gives the grade of the conclusion, expressed in terms of the grade(s) of
the premises.
         p(D) = 0 for an azdom D
                :F
                                 for LA,RV, LO, RD, LV
         p + 1;
         p:r,A                    p'       B                     A,A     p'   ,B
            p + p' + 1 : F,AVBA                           p + p' + : F, A -4 B
           p: F, A      B,             p: F A[xly],VxA, A
         p:F         A>B     ,             p :F VxA, A
         p :r        A, A         p' : F       B,A
                p + p' :F         AAB, A
290                                                 Chapter 9. Modal and linear logic

9.2.5. LEMMA. (Inversion lemma) Let F-7, F   A mean that F A can be
proved by a G3s-derivation D with p(D) < n, where the axioms have only
atomic principal formulas. Then

          F =- A     B, A iff I--n r, A =- B, A;

          r     A A B, A iff       r     A, A and I--n F    B, A;

      I-7, r    VxA, A iff     r        A[x/y], A (y not free in F, A, VxA).

From this it follows that a cutfree derivation D of r      A in the Y-fragment
may be assumed to consist of derivations of a number of sequents ri         Ai,
with all formulas in Ai atomic, disjunctions, existential or modal, followed by
applications of RA, R-4 and RV only.

9.2.5A. * Prove the inversion lemma.

9.2.6. DEFINITION. A formula C is prim,itive if C is either atomic, or a
disjunction, or starts with an existential quantifier.

LEMMA. Let ° be the embedding of 9.2.1. Suppose we have derivations of
either

      OF°, A° =- OA°, or
      or., A.      DA., B. (-.
                           n primitive).

Then there are derivations of these sequents where any sequent with more
than one formula in the succedent has one of the following two forms:
      DE.,         De., A with lei _> 1, A° primitive, or

      D0, A0 =- De°, with ie > 2.
PROOF. We apply induction on p(D). If p(D) = 0, D is necessarily an axiom
and the result is trivial.
  Suppose p(D) > 0. If a sequent of type (a) is the consequence of a right
rule, the rule must be RO; in this case A = 0, A = 1, hence the deduction
ends with
                                        OF°   A°
                                       OF     OA°
The premise has been obtained by application of RA, R-4 and RV from de-
ductions Di of Oil   A, A7 primitive. Now apply the induction hypothesis
to the V.
9.2. Embedding intuitionistic logic into S4                                      291

  If a sequent of type (b) is the conclusion of a right rule, the rule must
be RV or R. Consider the case where the rule is RV. Then the final rule
application is
                                OF°     DA°, OB,
                                OF°    DM, OB,3 V 0./3
We can then apply the IH to the premise. Similarly if the last rule applied
was R.
  Now assume that a sequent of type (a) or (b) was obtained by a left rule,
for example

                    A°, OF°      OA°, OA°          A°, or°, B°    DA°
                               A., or., DA.        B. ono
Then we can apply the IH. Other cases are left to the reader.

9.2.7. DEFINITION. Let (a), (b), (i), (ii) be as in the preceding lemma.
Standard derivations are cutfree derivations with conclusions of type (a) or
(b) and each sequent with more than one formula in the succedent of types
(i) or (ii) only.                                                                  1E1




LEMMA. If G3s or.             A°, then there is a cutfree derivation such that
all its applications of R-4, RV have at most one formula in the succedent.
PROOF. By the inversion lemma, OF°                 A° can be obtained from deductions
Di of oil    il) with ./4.) primitive, using only R>, RA, RV, and by the
preceding lemma the Di may be assumed to be standard. So if we have
somewhere an application of R> or RV with more than one formula in the
succedent of the conclusion, the conclusion must be of one of the forms (i), (ii)
in the statement of the preceding lemma, which is obviously impossible.


9.2.8. THEOREM. (Faithfulness of the modal embedding)

         G3s 1- Er            A° iff G3s      r°     An   iff Ip A r -+ A.

PROOF. The first equivalence has already been established, so it suffices to
show that if OF°        A° then Ip I- A r -4 A. Now delete all modalities in
a standard derivation of OF°        A'; then we find a derivation in a classical
sequent calculus in which all applications of R--+ and RV have one formula in
the succedent; it is easy to see that then all derivable sequents are intuition-
istically valid, by checking that, whenever I'    A occurs in such a deduction,
then r              provable in Ip (cf. 3.2.1A).                              N
292                                              Chapter 9. Modal and linear logic

9.3      Linear logic
There are several possible reasons for studying logics which are, relative to our
standard logics, "substructural", that is to say, when formulated as Gentzen
systems, do not have all the structural rules.
   For example, in systems of relevance logic, one studies notions of formal
proof where in the proof of an implication the premise has to be used in an
essential way (the premise has to be relevant to the conclusion). In such
a logic we cannot have Weakening, since Weakening permits us to conclude
B --+ A from A; B does not enter into the argument at all. On the other
hand, Contraction is retained.
  In the calculus of Lambek [1958], designed to model certain features of the
syntax of natural language, not only Weakening and Contraction are absent,
but Exchange as well. Therefore the Lambek calculus has two analogues
of implication, AIB and A\B. The rules for these operators are (r, A, A'
sequences, antecedents of sequents always inhabited)
                 A      ABA'        C
                                            R'
                                                  ArB
               Ar(A\B)A'        C           '" 1           A\B
          ir            ABA1        C
               A (A/B)rA'       C                r         AIB
In so-called BCK-logic, Weakening and Exchange are permitted, but Con-
traction is excluded (see, for example, Ono and Komori [1985]).
   If we think of formulas, not as representing propositions, but as types of
information, and each occurrence of a formula A as representing a bit of
information of type A, we naturally may want to keep track of the use of
information; and then several occurrences of A are not equivalent to a single
occurrence. These considerations lead to linear logic, introduced in Girard
[1987a]. In the Gentzen system for linear logic we have neither Weakening
nor Contraction, but Exchange is implicitly assumed since in the sequents
      A considered the r, A are multisets, not sequences.
   From the viewpoint of structural proof theory, the most interesting aspect
of linear logic is that it can be used to obtain more insight into the systems
for the standard logics. This is illustrated in a simple case (intuitionistic
implication logic) in the next section. See in addition the literature mentioned
in the notes

9.3.1. Conjunction
In order to set the stage, we consider the rules for conjunction. For both the
left and the right rule two obvious possibilities present themselves:
               rA       A                                  Ao, Ai   A
        LA                     (i = 0, 1)   LA'      l''
9.3. Linear logic                                                                         293

          RA
               rA0,z              F    Ai, A
                                                        RA'
                                                               ro     Ao, Ao
                    F         Ao A Ai,A                          F0, F1    Ao A Ai, Ao,

In the absence of the rules W and C, we have to consider four possible com-
binations: (LA,RA), (LA',RA), (LA,RA'), (LA',RA'). However, the second
and the third combination yield undesirable results: versions of Weakening
and/or Contraction become derivable. For example, combining LA' with RA
permits us to derive Contraction by one application of the Cut rule:

                              A
                                   _AAAA
                                                 r,,A  F,AAALX

Therefore only the first and the fourth combination remain. It is easy to see
that for each of these combinations the crucial step in cut elimination, where
the cut formula has been active in both premises, is possible:

               F        Ao,           r     Ai, A            r',A0
                                                             Ao A Ai       A'
                                                                                Cut

becomes

                                  r       Ao6,
                                                                     Cut

and
               r        Ao,           r     Ai,         r", Ao,            A"
                              Ao A A1, A, A'           F", A0 A Ai          A"
                                                                                 Cut
                                            r"      A, A', A"

becomes

                                      F      A0, A     PI, A0, A1
                                                                                Cut
                                                                       Cut
                                  r,r",r"        A, A', A"

 "Context-free" or "context-sharing" becomes visible only in the case of rules
with several premises. But a secondary criterion is whether rules "mesh
together" in proving cut elimination. That is why LA' is to be regarded as
 "context-free": its natural counterpart RA' is context-free.

9.3.1A. * Investigate the consequences of the second and third combinations of
conjunction rules in more detail; can you get full Weakening and Contraction?
294                                                        Chapter 9. Modal and linear logic

9.3.2. Gentzen systems for linear logic
In linear logic Weakening and Contraction are absent. As we have seen, in the
absence of these rules, the combinations LA, RA and LA', RA' characterize
two distinct analogues of conjunction: the context-free tensor (notation *),
with rules corresponding to (LA,RA), and the context-sharing and (notation
n) with rules corresponding to (LA',RA'). In a similar way V splits into
context-free par (-I-) and context-sharing or (Li), into context-free linear
implication (-0) and context-sharing additive implication (-4). There is a
single, involutory, negation
  The logical constants T (true) and 1 (false) also split each into two op-
erators, namely T (true), 1 (unit) and 1 (false), 0 (zero) respectively. This
yields the following set of rules for the "pure" propositional part of classical
linear logic:
Logical axiom and Cut rule:
                                                              F         A, A       F', A
         Ax A                                         Cut
                        A
                                                                        r,P
Rules for the propositional constants:

                                                              rA
                      ,A          A                                            A

                                                                                   r
         Ln
                 r,AonAl
                                       (2;   0,1)     Rn
                                                                        rAnB,A
                                  A                                    A,,6.               .13,A'
         L* r'A'B                                     R*r                          I''

                 F,A*B            A
                 r 'A       ,6,       r,B             Ru                               (2 = 0,1)
         Lu
                        r,AuB,6,                              r                '
                                                                        AouAl, A

         L+
                             ri,BA,'                  R+
                                                                  l'    A,B,A
                                                              r         A+ B,A

         L-0
                  r      A,,6,        r',B       A'   R___,            r,AB,A
                 r A,A r,B                   A
                                                      rt^'4
                                                                       rB,A,               r,A=.A
         L--->
                        r,,4---BA,                            riLl---4B,A r                  ,L1---B,A,



         Li
                  r                                   Rl                1
9.3. Linear logic                                                                           295



         (no LT)                                   RT F           T, A

         LO O

         LI r,±                                    (no RI)

It is routine to add rules for the quantifiers; in behaviour they are rather
like the context-sharing operators (no good context-free versions are known),
even if this is not "visible" since there are no multi-premise quantifier rules.
Rules for the quantifiers (y not free in F, A):
                 A[xI t]           A                           A[x/y1, A
                                                   RV
         LV
                F, Vx A        z                        FVxA,z

                 A[x I y]          A                    F      A[x t], A
         L3 F'                                     R3
                F,3xAA                                            3xA,A

More interesting is the addition of two operators ! ("of course" or "storage")
and ? ("why not" or "reuse") which behave like the two S4-modalities 0, O.
These operators re-introduce Weakening and Contraction, but in a controlled
way, for specific formulas only. Intuitively "!A" means something like "A
can be used zero, one or more times", and "?A" means "A can be obtained
zero, one or more times". The rules express that for formulas !A we have
Weakening and Contraction on the left, and for ?A we have Weakening and
Contraction on the right.
Rules for the exponentials:
         F      A                                  !F       A,?      C! r, !A, !A     A
   W!                     L!       A   A      R!
        r, !A       A          r, !A   A                    !A, ?A         F, !A     A

            F     A       mA           .`?A             A, A                        ?A, A
   W?                 L?    '                 R?                     C?
        F       ?A, A    T, ?A          ?A         F    ?A, A              F       ?A, A



DEFINITION. We denote the Gentzen system of classical linear logic by Gcl.
Intuitionistic linear logic Gil is the subsystem of Gcl where all succedents
contain at most one formula, and which does not contain ?, +, O,      We use
CL, IL for the sets of sequents provable in Gcl and Gil respectively.
296                                                     Chapter 9. Modal and linear logic

EXAMPLES. We give two examples of deductions in Gil:
                             AA A
                            A1113
                                                 B
                                               AnBB
                                                            B
                           !(AnB)   A !(AnB)    B
                           !(AnB)   !A !(AnB)   !B
                            !(AnB),!(AnB)  !A*!B


                                                                    gc
                                !(An B)        !A *!B

                AA CC                                   B

        (A--0C)n(B-0C),AC (A--0C)n(B--0C),C
                (A--0C)n(B--0C),AuBC
               (A-0C)n(B-0C) (AuB)-0C
                       (A   0 C)    (B ---0   C) 0 ((A u B) 0 C)
9.3.3. De Morgan dualities
There is a great deal of redundancy in the very symmetric calculus Gcl: there
is a set of "De Morgan dualities" which permits the elimination of many
constants. Using I- A .#> B as abbreviation for "I- A  B and I- B A",
we have
          I-   A *B -#>                         I- A + B                   ,B),
               AnB                              I- A U B         .#> ,(A n B),
          -A0 B             ,A+B,               I-- A       B      ,AuB,
                VxA <#;>                                3xA
          H       !A           A,               I-          ?A

The operators *, +, n and U are associative and commutative modulo ,#>, and
further n and U are idempotent modulo <*. The constants 0, 1, J_ and T
behave as neutral elements w.r.t. +,*, U and 11 respectively (i.e. I- A*1 <#. A,
I- A U   .4.> A, etc.).

   Exploiting the symmetries of the classical calculus, we can introduce a
system GScl which has one-sided sequents only, just like the GS-systems for
ordinary classical logic (9.3.3G).

9.3.3A. * Prove in Gcl the De Morgan dualities listed above.

9.3.3B. * Prove in Gcl for the relevant operators the associativity, idempotency,
comnfutativity, and neutral-element properties. Which of these properties also hold
in Gil?

9.3.3C. 4 Prove in Gil !A*!B          !(AnB) and (A U B)* C        (A* C)U (B *C).
Show that (A u B) n C        (A n C) u (B n C) is not derivable in Gcl.
9.3. Linear logic                                                                   297

9.3.3D. 4 A natural deduction system for 0IL is given by the axioms and rules
(1)AA,(2)IfF,ABthenFA-0 B, (3)IfF=.AoBandAA
then FA        B (r, A finite multisets). Prove equivalence with Gil.

9.3.3E. 4 Show that a Hilbert system for 0IL is obtained by taking the axiom
schemas (A 0 B) 0 ((B 0 C) 0 (A 0 C)) and [A 0 (B 0 C)] 0 [B 0
(A 0 C)], with modus ponens as deduction rule (Troelstra [1992a]). Hint. Use
the preceding exercise, and derive a deduction theorem for the Hilbert system.

9.3.3F. 4 The positive (2) and negative (./V) contexts in the language of linear
logic are defined as for the language of ordinary first-order logic, that is to say that

          P           AnPIPnAIA*PIP*AIA+PIP+Al AUP
                = AnArpfnAIA*IVI.Af*AIA+Arl.Af+AlAuAr

Let F[*], G[*] be a positive and a negative context respectively, and let be a list
of variables free in B or C but bound in F[B] or F[C]; similarly, let 77 be a list
of variables free in E or C but bound in G[B] or G[C]. Ptove that in Gcl, Gil
without exponentials !,? (Troelstra [1992a, 3.10])

          I-1 FIV,F(B 0 C)       FEB] 0 F[C],
          I- 1 nV7.7(B--0C)      G[C] 0 G[B].

In the full theories we only have

          If     (B 0 C) then I- F[B] 0 F[C] and G[C] 0 G[B].

9.3.3G. 4 Write down a system GScl with one-sided sequents for CL, similar
to the GS-systems for C.

9.3.3H. 4 (Approximation theorem, Girard [1987a]) Prove the following result.
Let

          !A := (1 nA)*... (n times ) ...* (1 nA)
          ?nA := (0 Li A) +  (n times )...+ (0 u A).

Suppose that we have shown GScl r (GScl as in the preceding exercise), and
assume each occurrence a of ! in I' to have been assigned a label n(a) E 11\1 \ {0}.
Then we can assign to each occurrence ß of ? a label n(0) E DI \ {0} such that if
F' is obtained from r by replacing every occurrence a of ! and every occurrence
0 of ? by !n(,), ?7,(3) respectively, then in GScl without !, ? we have I- v. Hint.
Use induction on the depth of deductions, staxting from atomic instances of the
axioms, and use the monotonicity laws of exercise 9.3.3F.
298                                                             Chapter 9. Modal and linear logic

9.3.4. THEOREM. Cut elimination holds for Gcl and Gil.
PROOF. The proof is more or less standard, and similar to the proof for G3s.
However, we cannot "absorb contraction", so we need an analogue of the
Multicut rule. For example, one would like to replace
                                                           D'
                           !r         A, ?A       F', !A, !A
                           !F        -!A, ?A        F', !A
                                       !F, F'     -`:?A, A'
                                                                         Cut

by

                                      !r        A, ?A                D'
                 !r     A, ?A         !r           ?A      P, !A, !A            A'
                                                                                     Cut
                 !F    -!A, ?A                  !A, !F,    -`?A, A'
                                                                    Cut
                           F, !F,              ?LX, ?A, A'
                                                               C!,C?
                                 T,                 A'
where the double line stands for a number of C!- and C?-applications. This
does not work because the lower cut will have the same height as the original
one. The solution is to permit certain derivable generalizations of the Cut
rule, similar to "Multicut":
                         A, !A             r, (!A)n, -!A, A'
                                                             Cut! (n > 1)
                                r,            A, A'
                          (?A), A               I'', ?A        A'
                                                                    Cut? (n > 1)
                            r, F'
Let us write "Cut*" for either Cut?, Cut!, or Cut. Now we can transform the
deduction above into

                         !r          A, ?A                D'
                         !r      -!A, ?A         ri, !A, !A         A'
                                                                         Cut!
                                      !   F,      -?A, A'
If the cutformula is not principal in at least one of the premises of the terminal
cut, we have to permute Cut* upwards over a premise where the cut formula is
not principal. This works as usual, except where the Cut* involved is Cut! or
Cut? and the multiset (!A)'2 or (?A) removed by Cut! or Cut? is derived from
two premises of a context-free rule (R*, L+, L-0 or Cut*); a representative
example is
                                 F, (!A)P        A, B           F', (!A)q   A', C
            r"        !A, A"          1", ri, (!A)P+q            A, A', B * C     *
                                                                                     Cut*
9.3. Linear logic                                                            299

If either p = 0 or q = 0, there is no difficulty in permuting Cut! upwards on
the right. But if p, q > 0, then in this case cutting F"     !A, A" with both the
upper sequents on the right, followed by R*, leaves us with duplicated F", A".
To get out of this difficulty, we look at the premise on the left. There are two
possibilities. If !A is not principal in the left hand premise of the Cut!, we can
permute Cut! upwards on the left. The obstacle which prevented permuting
with the right premise does not occur here, since only a single occurrence of
!A is involved. On the other hand, if !A is principal in the left hand premise,
we must have r" !F", A" ?A" for suitable F", A", and we may cut with
the upper sequents on the right, followed by contractions of !r-, r" into !r-
and of ?A'", ?A" into ?A", and an application of the multiplicative rule (R*
in our example).

9.3.4A. 4 Complete the proof (cf. Lincoln et al. [1992]).

9.3.4B. 4 Devise a variant of Gcl where the W- and C-rules for the exponentials
have been absorbed into the other rules, and which permits cut elimination. Hint.
Cf. G3s.

9.3.5. PROPOSMON. A fragment of CL determined by a subset of {*,
0, n, u, 1, 1, T, V, 2, !} is conservative over IL (i.e. if CL restricted to
proves A, then so does IL restricted to L) iff L does not include both 0 and
I.
PROOF. .@ Suppose that J.. is not in L, let D be a cutfree deduction of
F   A, and assume that D contains a sequent with a succedent consisting
of more than one formula. This can happen only if there is an application of
L-0 of the form
                             r     A, C       ,   B
                                 r,r,,A-0/3   C
We can then find a branch in the deduction tree with empty succedents only.
This branch must end in an axiom with empty succedent, which can only
be LO or LI. The first possibility is excluded since the whole deduction is
carried out in a sublanguage of Gil; the second possibility is excluded by
assumption.
   If 0 is not in L, we can prove, by a straightforward induction on the length
of a cutfree deduction of a sequent A      B, that all sequents in the deduction
have a single consequent.
      As to the converse, in the fragment {o, 1} of Gel we can prove
(P, Q, R, S atomic)

                    P 0 ((± ---0 Q) 0 R), (P 0 S) --o         R
This sequent does not have a cutfree deduction in Gil.                         E]
300                                             Chapter 9. Modal and linear logic

9.3.5A. 4 Construct a Gcl-derivation for the sequent mentioned in the proof.

9.3.6. DEFINITION. The Girard embedding of I into CL is defined by
                        := P (P atomic),
          J_

          (A A B)* := A* n B*,
          (A V B)* := !A* LJ !B*,
          (A    B)* := !A* 0 B*,
          (AxA)*   := ]x!A*,
          (VxA)*   := VxA*.
CL is at least as expressive as the standard logics, as shown by the following
result:

9.3.7. THEOREM. If Gcl h F*            A*, then Gli   r    A.
PROOF. Almost immediate from the observations that (1) if we replace n, u,!
by A, V, El in the *-clauses, and we read ° for *, we obtain the.faithful embed-
ding of I into S4 of 9.2.1, and (2) behaves like El in S4, and all the laws
                                       !


for V, A, 0,11, ±, 1 in Gel are also laws for their analogues V, 3, -4, A, V, _L
in S4. This second fact has as a consequence that if Gcl h r*           A*, then
S4 I r° A° for the modal embedding °, hence G1i r A.

9.4 A system with privileged formulas
In this section we illustrate how linear logic may be used to encode "fine struc-
ture" of Glc and G1i. We consider a version of the intuitionistic Gentzen
system for implication, rather similar to >h-GKi of 6.3.5, in which at most
one of the antecedent formulas is "privileged". That is to say, sequents are
of the form
          11; 1.   A, with 1111 < 1.
So H contains at most one formula. To improve readability we write ; r
(H; -) for a11; r with empty II (empty 1'). The rules are suggested by thinking
of H; F    A as H*,        A* in linear logic, where * is the Girard embedding.

9.4.1. DEFINMON. The system IU ("U" from "universal") is given by
Axioms
          A;        A

Logical rules

          L.4
                   ;FA         B;ri    C
                                             R+ 11' r'A
                                                                B
                                                  H;rA-4./3
9.4. A system with privileged formulas                                                      301

Structural rules
                     r     A           ri;
                                             r'B'B         A
                                                                    B"r
                                                                                 A
        LW     II"
             II;r,B
                                  LC                           D
                                                                   ;B,r
REMARK. An equivalent system is obtained by taking the context-sharing
version of L*. Observe also that A B can never be introduced by L*, if B
has been introduced by Weakening or Contraction. Thus deleting semicolons
in all sequents of an IU-proof, we have, modulo some repetitions caused by
D, a restricted kind of intuitionistic deduction.

9.4.2. PROPOSMON. The system TU is closed under the rules "Headcut"
(Cuth) and "Midcut" (Cut,n):

        Cuth
               II; F       A      A; ri       B
                                                    Cutm
                                                               ;FA               II; A, r   B
                         ri; r,        B                                     P       B

9.4.2A. 4 Show that TU is closed under Cuth and Cutm.

9.4.3. THEOREM. If Gli             r A then TU ; r                      A.

PROOF. By induction on the length of deductions D of                                 A in Gli.
Problems can arise only when the last rule in D is 1,--> or LV. So suppose 1,
to end with


By 1H we have in TU

                                             and

So we cannot apply L--> directly, since this would require a premise B; r                       C.
However, we can derive ;
                                  A;- A
                                  ;AA B;.B
                                    A*B;AB
and then we may construct a derivation with the help of cuts

                                               B
                                                   uutni           ,B        C cutm
                                                           C
                                  ;r,A>BC LC
302                                                        Chapter 9. Modal and linear logic

As noted above, the rule L+ of TU is motivated by the Girard embedding:
if we read B; r C as B*, !F*    C*, it precisely corresponds to
                                !F*      A*
                                !F*    -!A*      !A*, B*       C*
                                !F*, !A*, !A* 0 B*             C*

It is easy to see that the soundness of * for TU can be proved by a straightfor-
ward step-by-step deduction transformation, without the need for auxiliary
cuts.
  This contrasts with the proof of soundness of * for Gli. In that case we
need cuts to correct matters (cf. the proof of 9.2.3). For example,
                                                   AA
                                  C=C B,AA
                                      C, C       B, A      A
leads to
             !C*    !C*    B*         B*
               !C*, !C* 0 B*      B*
                                                                      A*       A*
             !(!C* 0 B*), !C*      B*
                                                                      !A*      A*
             !(!C* --o B'), !C*    !B*           !C*    !C*         !B*, !A*     A*
           !(!C* 0 B*)        !C*   !B*          !C*, !C* 0 !B*, !A*            A*
                          !C*, !(!C* --o B), !A*                                      Cut
                                                            A*

After translating and eliminating the auxiliary cut we are left with
                                           A*     A*
                                           !A*    A*
                           !C*, !(!C* 0 B*), !A*               A*

deriving from a deduction with weakenings alone, not requiring auxiliary
cuts under translation. This suggests that translated deductions of Gli after
elimination of the auxiliary cuts will correspond to deductions in TU; this
impression is confirmed by the following result.

9.4.4. PROPOSITION. If D is a deduction in the !-0-fragment of Gcl of
a sequent II*, T*      !E*, A*, where all cutformulas are of the form A* or
!A*, and all identity axioms of the form A*     A*, then the skeleton of D,
sk(D), obtained by replacing sequents II*, !F*   !E*, A* by 11; r    E, A, is
an TU-deduction modulo possible repetitions of sequents.
PROOF. We prove the statement of the theorem, together with III U El < 1
and IE U AI < 1 simultaneously by induction on the length of D.
Basis. For an axiom A*    A*, with skeleton ; A       A, all conditions are
met.
9.5. Proofnets                                                                           303

Induction step. Case 1. Suppose the last step is L-0:
                              !E*0`, A*0`    B*,        !ET, AT
         lit, HI, !A* 0 B*, !Ft, !r1.           !E:, !ET, At

With the IH we see that

         Fli = Eo = Ao = 0, lEi U Ail = 1.

Case 2. Suppose the last rule is L!, so 7, ends with
             II*, A*, !r*     !E*, A*
         II*, !A*, !F*        !E*, A*

So by IH 1E U      = 1, 1E1 = 0, hence 1A1 = 1, and hence A; r                       A; then
; A, F A by dereliction D.
Case 3. The last step is R!
         !r*        A*
         !F*       !A*

By the IH we can derive ; r                 A which is the skeleton of the conclusion. El

9.4.4A. A Extend IU so as to cover the other propositional operators as well.


9.5          Proofnets
9.5.1. In this section we present Girard's notion of proofnet for the context-
free ("multiplicative") fragment containing only +,* as operators, and as a
defined operation; formulas are constructed from positive literals P,Q,P',...
and negative literals                    by means of + and *, using the De
Morgan symmetries of 9.3.3 for defining -,A for compound A (as with the
GS-calculi for C). As our starting point we take the one-sided Gentzen system
for this fragment, with axioms and rules

       AA                A'r         A          ABF            1"   ,A          ,A Cut
                                                                         r, A
         ,
                         A * B, r,B,A          A      ,r
Just as in the Gentzen systems for our standard logics, cutfree sequent proofs
may differ in the order of the application of the rules, e.g. the two deductions
       A,
        A*             CC
       (A*                                                 A* B,,A+
      (A * B) * C, A +                                 (A * B) * C, A +
304                                              Chapter 9. Modal and linear logic

represent "essentially" the same proof: only the order of the application of
the rules differs. The proofs also exhibit a lot of redundancy inasmuch as
the inactive formulas are copied many times. There is also a good deal of
non-determinism in the process of cut elimination, due to the possibilities for
permuting cut upwards either to the left or to the right.
   Proofnets were introduced by Girard [1987a] in order to remove such re-
dundancies and the non-determinism in cut elimination, and to find a unique
representative for equivalent deductions in Gcl. In the same manner as Ni
improves upon Gli, proofnets improve on Gcl. For the full calculus Gcl
proofnets are complicated, but for the +*-fragment there is a simple and sat-
isfying theory. Proofnets are labelled graphs, and therefore we define in the
next subsection some graph-theoretic notions for later use.


9.5.2. Notions from graph theory
DEFINMON. A graph is a pair G             (X, R), where X is a set, and R is an
irreflexive symmetric binary relation on X (R irreflexive means Vx,Rxx, and
R symmetric means Vxy(Rxy > Ryx)). The elements of X are the nodes or
vertices of the graph, and the pairs in R are the edges of the graph. (X', R')
is a subgraph of (X, R) if X' C X and R' C R.
   We shall use lower case letters x, y, z, . . for nodes; an edge (x, y) is simply
                                             .


written as xy or yx.
   A node is of order k if it belongs to exactly k different edges.
In the usual way finite graphs may be represented as diagrams with the nodes
as black dots; dots z, y are connected by a line segment if Rxy. For example
the picture below is a graph with five nodes and seven edges (so the crossing
of the two diagonal lines does not count as a node).




DEFINMON. A path x1x2...xn in a graph G is a sequence of nodes xl, x2,
  , xn with n > 1, and XiXi-Fi an edge for 1 < i < n. A path xix2 xn is
said to be a path from xl to xn. A subpath of a path x1x2...xn, is a path
           ... xi with 1 < i <j < n.
  A cycle is a path of the form x1x2 XnXi, such that for no i j Xi =
(so a cycle cannot contain a proper subpath which is a cycle).
  For the concatenation xl... xnxn+i xm of paths a = xl ...xn and ß =
Xn+1    Xm we write a     13.
9.5. Proofnets                                                              305

REMARK. A cycle is sometimes defined as a path of the form x1x7,. xnxi;
cycles satisfying our extra condition above are then called simple cycles.

DEFINITION. A graph is connected if for each pair of nodes x, y there is a
path from x to y. The component of a node x in G is the largest connected
subgraph containing x. A tree (-graph) is a graph which is connected and
contains no cycles.

9.5.3. Proof structures
A proof structure with hypotheses is a graph with nodes labelled by formulas
or by the symbol "cut", built from the following components, each consisting
of 1, 2 or 3 labelled nodes with 0, 1 or 2 edges between them:
      single nodes labelled with a formula H (a hypothesis); the conclusion
      and premise of this component are H.
      axiom links A             with conclusions A, A and no premises;
      cut 14 k         cut        A with premise A, A and no conclusions;
      logical links with premises A, B, namely
      tensor links or *-links A     A *BB, with conclusion A *B, and
      par links or +-links AA + BB with conclusion A + B.
So edges with cut, A * B or A + B always appear in pairs. More precisely we
define proof structures as follows:

DEFINMON. The notion of a proof structure and the notion of the set of
conclusions of a proof structure are defined simultaneously. We write 1,,p,
for proof structures. CON(v) is the set of conclusions of 1,, a subset of the
labelled nodes of v. Let 1,, A, B,.. .D indicate a proof structure (PS) u with
some of its conclusions labelled A, B, . , D. We shall indulge in a slight abuse
                                         .


of notation in frequently using the labels of the nodes to designate the nodes
themselves. Proof structures are generated by:
      (hypothesis clause) a single node labelled with a formula H is a PS with
      conclusion H;
      (axiom clause) A ---,A is a PS (axiom), with conclusions A,
      (join clause) if v,     are PS's, then so is 1/ U i, with CON(v U ti) =
      CON(v) U CON(p);
      (cut clause) if u, A,      is a PS, so is the graph obtained by adding
      edges and the symbol "cut" Acut --,A; the new conclusions
      are CON(v) U {cut} \ {A,         (i.e. conclusions of v except A,     and
      "cut" added);
306                                                Chapter 9. Modal and linear logic

 (y) (*-clause, +-clause) if u, A, B is a PS, then so are the graphs obtained
     by adding two edges and a node A              A*B         B (*-link) or
      A      A+B         B (+-link). The conclusions are CON(v) with A, B
     omitted and A * B, respectively A + B added.

The hypotheses of a PS are simply all the nodes which went into the construc-
tion by the hypothesis clause. Sometimes we shall use the expression "the
conclusions of a PS" also for the multiset of labels corresponding to the set
of conclusions. A notation for PS which is closer to our usual deduction no-
tation is obtained by the following version of the definition (with the obvious
clauses for terminal nodes):

 (i)' iÏ is a hypothesis for any multiplicative formula H;

 (0 A         A is a PS (axiom link);

(iii)' the union of two PS's is a PS;

(iy)' connecting conclusions A, B in a PS by

                                A BA B
                                 A*B orA+ B
      gives a new PS (adding a *-link and a +-link respectively);

 (\T)' connecting terminal nodes A,         A in a PS by

                                        A
                                             cut
      gives a new PS.


REMARK. Alternatively, a PS may be globally characterized as a finite graph,
with nodes labelled with formulas or "cut"; every node is either a hypothesis
or conclusion of a unique link, and is the premise of at most one link. A
formula which is not the premise of another link is a conclusion.
   A hypothesis which is a conclusion is of degree 0, otherwise of degree 1;
axioms are of degree 1 when conclusions of the PS, otherwise of degree 2; and
conclusions of +,*-links are of degree 2 when conclusions of the PS, otherwise
of degree 3.


9.5.3A. 4 Show that the global characterization of a PS in the remark is equiv-
alent to the inductive characterization in the definition of PS.
9.5. Proofnets                                                           307

EXAMPLE. The two deductions at the beginning of this section are both
represented by the following PS without hypotheses, and with conclusions
    +


                                 A




If we delete any single edge entering one of the nodes       +      A* B, or
(A *B)*C, the result is no longer a PS. If we delete both edges in
or any of the axiom links, the result is again a PS, but now with hypotheses.
   Another graphic representation of the PS exhibited above:


                              ,,,13       A        B
                                              A* B      C
                                               (A* B)* C
A certain subset of the PS's, the set of inductive PS's corresponds in an
obvious way to sequent deductions.

9.5.4. DEFINITION. Inductive PS's (IPS's) are obtained by the clauses:
      A single node with label H (a hypothesis) is an IPS;
      A           is an IPS (axiom), with A,          as conclusions;

      if 1/, A and v', ,A are IPS 's, then so is v, A    cut       A, 1/ (cut
      link: two new edges and a node labelled "cut"), the conclusions are
      (CON(v) U CON(v') U {cut}) \ {A, ,A};
      if v, A and i/ , B are IPS's, then so is 1/, A A* B B,v/ (two new
      edges and a node A * B), the conclusions are
      (CON(v) U CON(11) U {A * B})\ {A, B};
      if 1,, A, B is an IPS, then so is

                                              v,A,B
                                               \/
308                                            Chapter 9. Modal and linear logic

        (two new edges and a node A +B), conclusions as in the corresponding
        clause of the preceding definition.

N.B. The example above of a PS is in fact an IPS. An IPS can usually be
generated in many different ways from the clauses (i)(v).

LEMMA. The multiset r is derivable in the sequent calculus iff F is the
multiset of conclusions of an IPS without hypotheses.
The proof of the lemma is straightforward and left to the reader. We are now
looking for an intrinsic, graph-theoretic criterion which singles out the IPS's
from among the PS's.

9.5.5. DEFINITION. A switching of a PS is a graph obtained by omitting
one of the two edges of every +-link of the PS. We call a PS a proofnet if
every switching is a tree.
  We shall now establish that a PS is a proofnet iff it is ari IPS. One side is
easy:


9.5.6. LEMMA. Each IPS is a proofnet.

9.5.6A. 4 Prove the lemma by induction on the generation of an IPS.
In order to to prove the converse we move to a more abstract setting and
prove a graph-theoretic theorem. In this connection it is useful to observe
that we need not consider proofnets with cut links: if we replace in a PS a
cut link Acut                by a *-link, A A*,-,A ---,A, the result is
again a PS which is a proofnet iff the original PS was a proofnet.

9.5.7. Abstract proof structures
DEFINITION. An abstract proof structure (APS) S a (N, E, P) is a triple
with (N, E) a finite graph, P set of pairs (xy, xz) of edges with y z; x is
the basis of the pair. A node can be the basis of at most one pair in P. An
element of P is said to be a pair of S. The graph terminology introduced
above is also applied, with the obvious meaning, to an APS.
   A sub-APS (N', E', P') of an APS (N, E, P) is an APS with (N', E') a
subgraph of (N, E), and such that P' is P restricted to E x E.
   A switching of an APS (N, E, P) is a subgraph (N, E') of (N, E) such E'
is obtained by omitting one edge from each pair of the APS. (So if the APS
has n pairs, there are 2" switchings).
  An APS is a net, if all its switchings are trees.
9.5. Proofnets                                                                309

EXAMPLE. The following picture shows an APS on the left (with the pairs
marked by * at the bases of the pairs), with its four switchings on the right.
Clearly this APS is a net.




9.5.7A. 4 Is there a PS with this APS as underlying graph, the pairs correspond-
ing to +-links?

9.5.8. DEFINITION. Let S (N, E, P) be an APS, cEP a pair with edges
xy, x z and ba,sis x. Let c(S) := S \ {xy, xz}
   S: is the component of x in c(S), ,57 is c(S)\ S The pair c is a section
if S does not contain y or z; that is to say, each path in S from x to y or
from x to z passes through one of the edges xy,xz.

9.5.9. LEMMA. Let S be an APS, and c a section of S. Then S is a net if
S: and S: are nets.
PROOF. Each switching of S decomposes into switchings of St, St connected
by a single edge.

9.5.10. DEFINITION. A pair of edges {xy,xz} is free in the APS S if xy, xz
are the only edges with x as endpoint (in other words, x is of degree 2).
   A path passes through a pair if it contains both its edges.
   A free path (free cycle) is a path (cycle) which passes only through free
pairs, and passes through at least one pair.
   A path -y is nice if for each node x -y, there are two free paths from x to
-y, distinct in x (i.e. starting with distinct edges in x), each intersecting 7 in
a single node.
N.B. Since a cycle does not contain smaller cycles, it follows that a cycle
passes through a pair {xy, x z} iff the edges appear consecutively in the cycle
(as    yxz ...).

9.5.11. PROPOSMON. Let S be a net with an inhabited set of pairs P,
then one of the pairs is a section.
PROOF. We shall derive a contradiction from the following three assumptions:
310                                            Chapter 9. Modal and linear logic

         S is a net,
         P is inhabited,
         no pair of P is a section.
Assuming H1-3 we shall construct a properly increasing sequence So, Si, S2,
... of sub-APS's of S, which contradicts the finiteness of S. In our construc-
tion of the sequence we use the following double induction hypothesis:
   Hil[n] Sn is a sub-APS of S;
   Hi2[n] Sn has a free, nice cycle D.


Basis. S must contain a cycle So; for if not, each pair of S is a section,
contradicting H2-3. Then Do := So satisfies Hil[0], Hi2[0]. (Observe that
relative to So each pair through which So passes is necessarily free.) Note
also that we can assume So to have at least one pair; for if cycles did not
contain pairs, there would be switchings containing cycles.


Induction step. Now assume Hil[n], Hi2[n] for Sn, Dn. Dn is free in Sn, and
must contain at least one pair - otherwise there would be a switching of S
containing a cycle.
   Let {yx, xz} be a free pair in Dn; it cannot be a section of S, hence there is
a path in S from x to y or from x to z, not passing through yx, xz. Starting
from x, let u E Sn be the first edge after x that the path ha' s in common with
S. Let a be this path from x to u; a intersects Sn in x and u only. We put
       SnU a. Sn+i will be Sn' with a new set of pairs added, namely all edges
paired in S, and not yet paired in Sn. We note
      Either such a pair entirely belongs to a, and then it is free, or the pair
has u as basis, and then one edge belongs to a;
      The only possible non-free new pair has basis u;
      The only old pairs possibly becoming non-free have basis x or u.
We now have to check Hil[n + 1], Hi2[n + 1] for the new Sn+i. Hil[n + 1] is
automatically guaranteed.


Construction of Dn+1. By Hi2[n] for Sn, if u Ø Dn, there exist two free paths
61462 in Sn from u to Dn, distinct in u, each intersecting Dn in a single point
only. We call these intersection points u1,u2 respectively (see fig. a). x = 711
and x = u2 are excluded since x has degree 2 in Sn, and u1, u2 have degree 3.
   One of the paths a - 61, a          02 is free. For 61, 62 are free in 5n (by
hypothesis), hence also free in Sn+i; a is also free, and a 61, and a -
intersect in u only. 61 and 62 differ in u, so a    61, a   62 cannot both pass
through a possible new pair with basis u; say a - 61 does not do so. Then
ce    61 is free.
9.5. Proofnets                                                                311




   There are two proper subpaths 01, 02 ofDn connecting ui with x. Then
either a Si       f3i or a           02 is free. To see this, note (fig. b) a (5].
and 01, a 61 and 02 respectively intersect in { ui, x} only; 01,02 are free in
Sn+i (since they are free in Sn) and do not contain pairs which can become
non-free going from Sn to Sn+1. 01 and 02 are distinct in ui, and hence one
of the two joins in ui is correct, i.e. does not pass through a new pair added
in u. And since the unique pair with basis x belongs to Dn, the junctions
      a, 02    a do not pass through this pair.
Suppose, say, a      -Th 01 is free; then this will be our D+1.
  If u E Dn, then argue as above, with ui = u.

Niceness of Dn+1. Finally we have to show that Dn+i is nice. Take some
V* E Sn+1    Dn+1. Then by the construction y* E S.
      If v* E Dn, take the two proper subpaths of Dn connecting y with x
and with ui.
       If y* i;Z Dn, there are two free paths 61,62 from y ending in Dn, distinct
from y, by Hi2[n]. Two possible situations for (y*, 61,12) are pictured in fig. c:
   ei, 62) and (//, 6'2).
  Consider ci. If it does not intersect Dn+i, one can continue it to x or to ui
such that it is free.
  Or if it does intersect Dn+1, then the piece of ei from y to the first inter-
section with Dn+i is correct. The two free paths 61,62 are distinct in y* since
they always agree on the first edge with 61,62 respectively, where they must
be different.                                                                   N
312                                                Chapter 9. Modal and linear logic




                       v'




                        '...e1




9.5.11A. * The preceding abstract theory for APS's still functions if we permit
that a pair has the form (xy,xy), but then in the definition of free pair we must
restrict attention to pairs with x, y, z distinct. We consider two contractions on such
APS's when finite: (a) deleting an edge xy not belonging to a pair and identifying
x and y, and deleting the edges of a pair (xy,xy) and identifying x and y. This
yields a notion of reduction which is terminating and confluent. Show that an
APS S is a net iff the normal form with respect to this reduction is a single point
(Danos [1990]).


9.5.12. Equating IPS's and proofnets
We are now ready to prove that inductive proof structures and nets coincide.
We have already seen that inductive proof structures are proofnets (9.5.6). It
remains to show the converse.

THEOREM. Every proofnet is an IPS.
PROOF. Let y be a given proofnet, and S = (N, E, P) the corresponding
APS, where (N, E) is the graph underlying y, and P consists of the pairs of
edges corresponding to +-links in v. S is a net, since y is a proofnet. We
apply induction on the number of +-links in v.
Basis. There are no +-links in v; we apply a subinduction on the number of
*-links in y.
Subbasis. If there is no *-link, v has been obtained from axiom links, hy-
potheses and join (cf. 9.5.3). But join is excluded, since v is connected; hence
v is an axiom or a hypothesis, hence an IPS by definition.
Subinduction step. Suppose there is at least one *-link in v. The last clause
applied in an inductive construction of v can never have been a join, since
9.6. Notes                                                                313

this would conflict with y being connected. So let the last clause applied in
an inductive construction of v be a tensor clause, with conclusion A * B and
premises A, B, and let VA, vB be the components of A and B in y after deletion
of the tensor link. VA, vB are connected (if not, v would not be connected),
are disjoint (otherwise v would contain a cycle) and together with the tensor
link make up all of v (otherwise v would not be connected). Hence, by IH,
vA, vg are IPS's, and so is V.
Induction step. v has +-links, so S has pairs. Hence we can find a pair c
in S which is a section. Then Sc- and 5? are nets. The proof structure zi:
corresponding to 5? has conclusions A, B and is an IPS by the IH; add a +-
link to obtain an IPS v* with conclusion A +B. Sc- corresponds to zi which
has A + B as hypothesis and which is also an IPS by the IH; substituting v*
for the hypothesis A + B in zi yields v as an IPS.                        Z

COROLLARY. A PS v is an IPS iff v is a proofnet.                            E


9.6      Notes
For a general introduction to modal logics, the reader may consult, for ex-
ample, Bull and Segerberg [1984], Hughes and Cresswell [1968], Fitting [1983,
1993], Mints [1992d].

9.6.1. The modal logic S4. The first axiomatization of S4 is due to C. I.
Lewis (in Lewis and Langford [1932]), but the Hilbert system given here is
due to Gödel [1933a]. For some background information on this paper see the
"Introductory Note to 1938f' in Gödel [1986].
   An early reference for a Gentzen system for S4 with a proof of cut elimina-
tion is Curry [1952a]. A form of G3s with 0 as the only primitive modality
appears in Kanger [1957].
   Some examples of modal logics which in many respects can be treated in
the same way as S4 are the following sublogics of S4 (cf. the definition of
S4 in 9.1.1), based on the same classical basis and the same deduction rules
as S4, but with only some of the modal axioms: K (K-axioms only), K4
(K- and 4-axioms only), T (K- and T-axioms). These systems are examples
of normal modal logics, i.e. they have a modal-logic Kripke semantics of the
standard type.
   In Mints [1990,1994b] resolution calculi for S4 and some closely related
logics are developed, in the spirit of sections 7.4, 7.5.

9.6.2. Interpolation for modal logics. Fitting [1983] and Rautenberg [1983]
contain proofs of interpolation for many modal formalisms. In Fitting [1983,
3.9, 7.13] it is shown that in S4 (and some closely related modal logics such
314                                            Chapter 9. Modal and linear logic

as K, K4, T) one can impose an additional condition on the interpolant of
A B.
   In order to define this extra condition, let us extend the notion of positive
and negative formula occurrence by adding to the clauses for positive and
negative contexts in 1.1.4: DB+ , 0B+ E P and OB-, OB- E Al. A formula
is said to be of 0-type ((>-type) if all occurrences of O occur positively (neg-
atively) and all occurrences of 0 occur negatively (positively). Then we can
require for the interpolant C of A       B
      if B is of 0-type, then C is of 0-type;
       if A is of 0-type, then C is of 0-type;
        if A is of 0-type and B is of 0-type, then C is non-modal, that is to
say contains neither 0 nor O.

9.6.3. Modal embedding of I into S4. There are many, slightly different,
embeddings of I into S4. Gödel [1933a] proved correctness and conjectured
faithfulness for a particular embedding and a slight variant of this, in the case
of Ip and S4p.
  The original motivation in Gödel [1933a] for the embedding was provided
by reading DA as "A is (intuitionistically) provable", where "provable" is
not to be read as "formally provable in a specific recursively axiomatizable
system" (as Gödel was careful to point out), but rather as "provable by any
intuitionistically acceptable argument" , or "provable in the sense of the BHK-
interpretation" (2.5.1).
   For some variant embeddings, see McKinsey and Tarski [1948], Maehara
[1954]. The ° mapping is copied from the Girard embedding (9.3.6, Girard
[1987a]) of intuitionistic logic into classical linear logic. For ° (the mapping
used by Rasiowa and Sikorski [1953,1963], but for the fact that we have
1 instead of as a primitive) the proof of faithfulness is somewhat easier
to give. The proof of faithfulness given here is an adaptation of the proof
by Schellinx [1991] of faithfulness for the original Girard embedding of I
into classical linear logic. Our proof is rather similar to the argument in
Maehara [1954]; as in Maehara's proof, a sequent calculus for I with finite
multisets in the succedent plays a role (cf. exercise 3.2.1A).
   A very elegant alternative method for proving faithfulness is found in Flagg
and Friedman [1986]; this method works not only for predicate logic, but also
for other formalisms based on intuitionistic logic on the one hand, and S4 on
the other hand (for example, intuitionistic arithmetic and so-called epistemic
arithmetic; proof-theoretic arguments for the faithfulness of the embedding
in this case had been given before in Goodman [1984] and Mints [1978].
   It should be pointed out, however, that S4 is by no means the strongest
system for which such an embedding works (cf. again the Introductory Note
to 1933f in Gödel [1986]).
9.6. Notes                                                                  315

9.6.4. Semantic tableaux for modal logics. Semantic tableaux (cf. 4.9.7)
have been widely used in the study of modal logics (for example, see Fitting
[1983,1988], Goré [1992] to obtain completeness proofs relative to a suitable
Kripke semantics. These proofs as a rule then establish completeness for a
cutfree sequent calculus, with closure under Cut as a by-product.
  Direct proofs of cut elimination by a Gentzen-type algorithm are less nu-
merous (e.g. Curry [19524 Valentini [1986]).
  Just as for intuitionistic logic, semantic tableaus for modal logics cannot
have all rules strictly cumulative. Thus we have for the modalities in S4 the
rules
                              8, tA         6, fA
                            8*, tOA       8*, f DA
where 6* := {t       :t OA E el U {f0A : f0A E e}. More flexibility is
achieved by considering tableaus with indexed sequents, also called "prefixed
tableau systems" (Fitting [1983, chapter 8]); the idea for such systems (but
without the indices explicitly appearing) goes back to Kripke [1963]. The
indices correspond to "worlds" in the Kripke semantics for the logic under
consideration.
   Mints [1994a] gives a cut elimination algorithm for a whole group of such
systems. He also shows that there is a close relationship between these sequent
calculi with indexed sequents, and systems (Wansing [1994]) in the display-
logic style of Belnap [1982]. N- and G- systems with a linearly ordered set of
 "levels" are considered in Martini and Masini [1993], Masini [1992,1993].

9.6.5. Linear logic. For a first introduction beyond the present text, the
reader may consult Troelstra [1992a]. Full bibliographical information on
linear logic may be found in electronic form under http : / /www . cs . cmu edu/
-carsten/linearbib/linearbib.html.
   The system of linear logic in its present form was introduced by Girard
[1987a]. As already noted in the preamble of section 9.3, this was not the
first study of Gentzen systems in which (some of) the structural rules had
been dropped; see Do6en [1993] and the references given there. The novel
idea of Girard was to reintroduce Weakening and Contraction in a controlled
form by means of the exponential operators (namely !, ?).
   Some of our symbols for linear logic deviate from the ones used in Girard
[1987a] and many other papers on linear logic: we use n, u,*, +,       0, for
                                                                       ,

Girard's Sz, ED, 0, ga, 0, I, (note the interchange between 0, I);    does not
appear in Girard's paper; the other symbols coincide. ga is also printed as an
upside-down 8.6. For the r'easons behind our choice of notation, see Troelstra
[1992a, 2.7].
  The embeddability of I into Gcl is stated in Girard [1987a] and completely
proved in Schellinx [1991]. A one-sided version of G3s is embedded into
classical linear logic Gcl in Martini and Masini [1994]. Combining this with
316                                             Chapter 9. Modal and linear logic

the embedding of I into S4 yields another proof of the embeddability of I into
Gcl. The results in 9.4 are taken from Schellinx [1994]. For much farther-
reaching results in this direction, see Danos et al. [1997,1995].
   Interpolation for fragments of CL is treated in Roorda [1994]. For resolu-
tion calculi for linear logic, see Mints [1993].
   Natural deduction formulations of IL are discussed in Benton et al. [1992],
Mints [1995], Ronchi della Rocca and Roversi [1994], Troelstra [1995].
   Proofnets were introduced in Girard [1987a]. The original criterion for
a proof structure to be a proofnet was formulated as the so-called "longtrip
condition". It is not hard to see that this criterion is equivalent to the switch-
ing criterion as given here (the terminology of "switching" was suggested by
the notion of a longtrip). Later Girard [1991] gave a much simpler proof,
also covering the case of quantifiers, reproduced (without the quantifiers) in
Troelstra [1992a, chapter 17]. Another proof, of independent interest, was
given in the thesis of Danos [1990]; this is the proof presented here. For yet
another proof see Metayer [1994]. An important early paper on proofnets is
Danos and Regnier [1989]. In the meantime, the concept of proofnets has
been extended (without the "boxes" of Girard [1987a]) to cover quantifiers
and context-sharing operators ri, LI as well (Girard [1996]).
   Basic logic of Sambin et al. [1997], Sambin and Faggian [1998] goes one
step beyond linear logic; here also the role of the contexts is isolated. Among
the extensions of basic logic we find linear logic and quantum logic, and the
cut elimination procedure for basic logic extends to these systems.

9.6.6. Computational content of classical logic. For a long time the quest
after a form of "computational content" in classical logic, comparable to the
computational content in I provided by the formulas-as-types parallel, seemed
hopeless. But recently the picture has changed. See for example Danos et
al. [1997], Joinet et al. [1998], Danos et al. [1999], where methods for "con-
structivizing" classical logic, in the sense just referred to, are being studied
via a classification of possible methods for embedding Gentzen's system LK
into linear logic.
Chapter 10


Proof theory of arithmetic

This chapter presents an example of the type of proof theory inspired by
Hilbert's programme and the Gödel incompleteness theorems. The principal
goal will be to offer an example of a true mathematically meaningful prin-
ciple not derivable in first-order arithmetic. Some experience with formal
proofs in arithmetic and the first elements of recursion theory will facilitate
understanding for the reader, even if most sections (the last two excepted)
are essentially self-contained.
  The main tool for proving theorems in arithmetic is clearly the induction
schema
Ind(A, x)    A[x10] --+ Vx(A + A[x ISx]) > VxA.

Here A is an arbitrary formula. An equivalent form of this schema is "cumu-
lative" induction
Ind(A, x)*   Vy<x (A[xly]      A) + VxA.
Ind(A, x) and Ind(A, x)* refer to the standard ordering of the natural num-
bers. Now it is tempting to try to strengthen arithmetic by allowing more
general induction schemas, e.g. with respect to the lexicographical ordering
of IN x IN. More generally, we might pick an arbitrary well-ordering < over
IN, i.e. a linear ordering without infinite descending sequences. Then the
following schema of transfinite induction holds.
TI< (A, x)   Vx (Vy <1x A [xly] > A) -4 WA.

This can be read as follows. Suppose the property A(x) is "progressive", i.e.
from the validity of A(y) for all y < x we can always conclude that A(x) holds.
Then A(x) holds for all x.
   To see the validity of this schema consider the set of all x such that A(x)
does not hold. If this set is not empty, then by the well-foundedness of <1
it must contain a smallest element xo. But by the choice of xo we have
Vy<xo A(y) and hence a contradiction against the assumed progressiveness
of A(x).
                                     317
318                                                  Chapter 10. Proof theory of arithmetic

   One might wonder whether this schema of transfinite induction actually
strengthens arithmetic. We will prove here a classic result of Gentzen [1943]
which in a sense answers this question completely. However, in order to state
the result we have to be more explicit about the well-orderings used. This is
done in the following section 10.1.


10.1          Ordinals below 60
From elementary set theory we know that there are particular well-ordered
sets called ordinals such that any well-ordered set is isomorphic to an ordi-
nal, and the ordinals themselves form a well-ordered class. Here we restrict
ourselves to a countable set of relatively small ordinals, traditionally called
ordinals below E. Moreover, we equip these ordinals with an extra structure
(a kind of algebra). It is then customary to speak of ordinal notations. These
ordinal notations can be introduced without any set theory in a purely formal,
combinatorial way. Our treatment is based on the Cantor "normal form for
ordinals; for detailed information we refer to Bachmann [1955]. We also in-
troduce some elementary relations and operations for such ordinatnotations,
which will be used later. For brevity we from now on use the word "o-rdinal"
instead of "ordinal notation".

10.1.1. DEFINITION. We define the two notions a is an ordinal and a <
for ordinals a, ß simultaneously by induction:

       If cem,        , ao are ordinals, m > 1 and am >                > do (where a >
       means a >             or a = ,8), then
                     warn           wa()


       is an ordinal. Note that the empty sum denoted by 0 is allowed here.
       If wam +             + wa° and co)3' +    + c4.»3° are ordinals, then

                     wam +        + wa° < c.,P3" +     + c.4,°

       iff there is an i > 0 such that am_i < On-i, am-i+1 = 13n-i+17                       =
       On, or else m < n and am = ßn,.        ao = ¡3n-m.

For proofs by induction on ordinals it is convenient to introduce the notion
of level of an ordinal by the stipulations (a) if a is the empty sum 0, level(a)
= 0, and (b) if a =            ...+ b..)'° with am >       > ao, then leyel(ce)
level ( cem ) + 1.

   For ordinals of level k, cok <          < wk+i, where coo = 0, c4.)1 = C4), Wk+1 = C,-)4'k
10.1. Ordinals below 60                                                                        319

NOTATION. We shall use the notation 1 for w°, a for w° +    + w° with a
copies of w° and waa for wa + + wa again with a copies of wa
  Note that limit ordinals (ordinals            0 not having an immediate predecessor)
are written as a + w' a for c> 0, a > O.

10.1.1A. 4 Prove (by induction on the levels in the inductive definition) that <
is a linear order with 0 as the smallest element. Show that the ordering is decidable.

10.1.2. DEFINITION. (Addition) We now define addition for ordinals:
 (warn +        + c2°) + (wd3' +       + w'3°) := cem +            +            + w°' +     + wfl°

where i is minimal such that ai > [3n; if there is no such i, take i = m + 1
(i.e. w8" +         + w'8°).                                                                     1E1




10.1.2A. 4 Prove that + is an associative operation which is strictly monotonic
in the second argument and weakly monotonic in the first argument. Note that +
is not commutative: l+w,--ww+ 1.

10.1.2B. 4 There is also a commutative version of addition: the natural (or
Hessenberg) sum of two ordinals is defined by

           (w                                    u.,00) := w7m+n       .    .    w70


where 7,n+n,... ,70 is a decreasing permutation of am, ... ao, On,    00. Prove         7



that # is associative, commutative and strictly monotonic in both arguments.

10.1.3. We will also need to know how ordinals of the form ,8 + (AP can be
approximated from below. First note that
              < ce --+ß + w5a <       + wa.

Rirthermore, for any -y <          + coa with a> 0 we can find a 8 < a and an a
such that
                <    + co6 a.


10.1.3A. 4 Prove this, and describe an algorithm that, when given a> O, 0, 7
such that 7 < + wa, produces 6, a with 7 < + w5a.

10.1.4. DEFINITION. We now define 2a for ordinals a. Let am >                                    >
ao > w > kn >  > k1 > O. Then (writing exp2(a), expw(a) for 2, w')
                                cock° + colon        wki      w0a)
           exP2(Wam                        wao     wkn-1
                    := (exp(wam                                            wk1-1))2a.            N
320                                                  Chapter 10. Proof theory of arithmetic

10.1.4A. * Prove that 2+1 = 2' +2" and that 2a is strictly monotonic in a.

10.1.5. In order to work with ordinals in a purely arithmetical system we
set up some effective bijection between our ordinals < eo and non-negative
integers (i.e. a Gödel numbering). For its definition it is useful to refer to
ordinals in the form

          u.,am km +        w'ko with am >                >a and ki       0 (m > 1).
(By convention, m = 1 corresponds to the empty sum.)

DEFINITION. For any ordinal a we define its Gödel number ra-' inductively
by


          rwakm+           + wa'ko-1 :=      ( 11Pti, 1,
                                             i<n-t

where pr, is the n-th prime number starting with Po := 2. For any non-negative
integer x we define its corresponding ordinal notation o(x) inductively by

          o   ( (H pli) 1) := E co°(i)qi,
                                       i<t

where the sum is to be understood as the natural sum.

10.1.6. LEMMA. (i) o(ra-') = a, (ii) r o(x)                 x.
PROOF. This can be proved easily by induction.
  Hence we have a simple bijection between ordinals and non-negative in-
tegers. Using this bijection we can transfer our relations and operations on
ordinals to computable relations and operations on non-negative integers.

10.1.7. NOTATION. We use the following abbreviations.

          x     y   :=   o(x) < o(y),
          wx        :=   rC4./0(x)1,
          x 1ED y   :=   ro(x) o(yr,
          xk        :=   ro(x)k7,
          wk        :=   r k

where wo := 1, wk+i :=W.
     We leave it to the reader to verify that              Ax.wx, Axy.x le y, Axk.xk and
Mc!' wk-1 are all primitive recursive.
10.2. Provability of initial cases of TI                                   321

10.2          Provability of initial cases of TI
We now derive initial cases of the principle of transfinite induction in arith-
metic, i.e. of

TI,a(P)        Vx(Vy-<xPy       Px)         Px

for some number a and a predicate symbol P, where is the standard order
of order type ec, defined in the preceding section. In section 10.4 we will
see that our results here are optimal in the sense that for our full system of
ordinals < 60 the principle

TI_<(P)        Vx(Vy-x Py       Px) +VxPx
of transfinite induction is underivable. All these results are due to Gentzen
[1943].


10.2.1. DEFINITION. By an arithmetical system Z we mean a theory based
on minimal logic V*_L-M (including equality axioms) with the following
properties. The language of Z consists of a fixed (possibly countably infinite)
supply of function and relation constants which are assumed to denote fixed
functions and relations on the non-negative integers for which a computation
procedure is known. Among the function constants there must be a constant
S for the successor function and 0 for (the 0-place function) zero. Among
the relation constants there must be a constant = for equality and for the
ordering of type eo of the natural numbers, as introduced in section 10.1.
In order to formulate the general principle of transfinite induction we also
assume that a unary relation symbol P is present, which acts like a free set
variable.
    Terms are built up from object variables x, y, z by means of f(ti,...
where f is a function constant. We identify closed terms which have the same
value; this is a convenient way to express in our formal systems the assumption
that for each function constant a computation procedure is known. Terms of
the form S(S(... 5(0) ...)) are called numerals. We use the notation SnO or
rt, or (only in this chapter) even n for them. Formulas are built up from J_
and atomic formulas R(ti,..., t,,), with R a relation constant or a relation
symbol, by means of A -4 B and VxA. Recall that we abbreviate A -4 I by

  The axioms of Z will always include the Peano axioms, i.e. the universal
closures of

PA1            Sx = Sy --+ x = y,
PA2            Sx= 0 >A,
322                                               Chapter 10. Proof theory of arithmetic

with A an arbitrary formula. We express our assumption that for any relation
constant R a decision procedure is known by adding the axiom Rni whenever
Rit is true, and 1171 whenever Rfi is false. Concerning we require irreflex-
ivity and transitivity for - as axioms, and also following Schfitte the
universal closures of
ordl         - 0 --+ A,
ord2     z   y    w°    (z          y    A)      (z = y     A)   A,
ord3     x ED 0 = x,
ord4     x ED (y ED z)= (x       y)      z,
ord5     0 ED x = x,
ord6     wx0 = 0,
ord7     wx(Sy) = wxy         wx,
ord8     z-<yED WSx                      we(s'Y'z)m(x, y, z),
ord9         y ED WSX
         z                  e(x, y, z)      Sx,

where ED, Axy.wxy, e and m denote the appropriate function constants and
A is any formula. (The reader should check that e, m can be taken to 6e
primitive recursive.) These axioms are formal counterparts to the properties
of the ordinal notations observed in the preceding section; for example, ord8
correponds to the remark in 10.1.3. We also allow an arbitrary supply of true
formulas Vi'A with A quantifier-free and without P as axioms. Such formulas
are called Ili-formulas (in the literature also 1--formulas).
  Moreover, we may also add an ex-falso-quodlibet schema or even a stability
schema for A:
Efq             A,
Stab            > A.
Addition of Efq leads to an intuitionistic arithmetical system (the V>±-
fragment of a version of Heyting arithmetic HA, cf. 6.6.2) and addition of
Stab to a classical arithmetical system (a version of Peano arithmetic PA;
see 10.5). Note that in our V-41-fragment of minimal logic these schemas
are derivable from their instances
EfqR    VY(1
StabR                     Rg),

with R a relation constant or the special relation symbol P. The proof uses
theorem 2.3.6 and the first half of exercise 2.3.6A. Note also that when the
stability schema is present, we can replace PA2, ordl and ord2 by their more
familiar classical versions
PA2c     Sx    0,
ordlc    X 74 0,
         z     y ED w°
10.2. Provability of initial cases of TI                                            323

   We will also consider restricted arithmetical systems Zk. They are defined
like Z, but with the induction schema Ind(A, x) restricted to formulas A of
level lev(A) < k. The level of a formula A is defined by

         lev(Ri')     := lev(1) := 0,
         lev(A    B) := max(lev(A) 1,1ev(B)),
         lev(VxA)     := max(1,1ev(A)).
However, the trivial special case of induction A[x/0] + VxA[x/Sx]         VxA,
which amounts to case distinction, is allowed for arbitrary A. (This is needed
in the proof of theorem 10.2.3 below; in the full language with V this is
equivalent to adding Vx(x = 0V 3y(x = Sy)).)

10.2.2. THEOREM. (Provable initial cases of TI in Z) Transfinite induction
up to tan, i.e. for arbitrary A(x)

         Vx(Vy-<x A(y)         A(x))       V x -<can A(x)

is derivable in Z.
PROOF. To any formula A(x) we assign a formula A±(x) (with respect to a
fixed variable x) by

         A+ (x) := Vy(Vz-q A(z) --+ Vz-q             cox A(z)).

We first show

         If A(x) is progressive, then A+ (x) is progressive,

where "B(x) is progressive" means Vx(Vy-x B(y) --+ B(x)). So assume that
A(x) is progressive and

         Vy--<x A+(y).

We have to show A+(x). So assume further

         Vz--q A(z)

and z y wx. We have to show A(z).
Case x = 0. Then z y co°. By ord2 it suffices to derive A(z) from z y
as well as from z = y. If z y, then A(z) follows from (2), and if z = y, then
A(z) follows from (2) and the progressiveness of A(x).
Case Sx. From z y e wsx we obtain z y e we(x,,,z)m ix  ( y, z) by (ord8) and
e(x, y,z)   Sx by ord9.  From (1) we obtain A+(e(x, y,  z)). By the definition
of A+ (x) we get
                                                                  we(x,y,z) A (u)
         Vu-q        we(x'Y'z)v A(u)   Vu-<(y El) we(x,y,z)v)
324                                        Chapter 10. Proof theory of arithmetic

and hence, using ord4 and ord7
        Vu-q e cide(x'Y'')v A(u)   Vu-<y ED we(x'Y'')S(v) A(u).

Also from (2) and ord6, ord3 we obtain
        Vu-q ED we(x'Y'')0 A(u).

Using an appropriate instance of the induction schema we can conclude that
        Vu-q ED we(x'Y'z)m(x, y, z) A(u)

and hence A(z).
  We now show, by induction on n, how for an arbitrary formula A(x) we
can obtain a derivation of
        Vx(Vy-<x A(y) > A(x))        Vx-o.) A(x).
So assume the left hand side, i.e. assume that A(x) is progressive.
Case O. Then x 23 and hence x 0 ED w° by ord5. By ord2 it suffices to
derive A(x) from x 0 as well as from x = O. Now x               A(x) holds by
ordl, and A(0) then follows from the progressiveness of A(x).
Case n+1. Since A(x) is progressive, by what we have shown above A+ (x) is
also progressive. Applying the IH to A+ (x) yields Vx- cori A+ (x), and hence
A+ (o.,,i) by the progressiveness of A+(x). Now the definition of A+(x) (to-
gether with ordl and ord5) yields V z--<cow' A(z).
  Note that in the induction step of this proof we have derived transfinite
induction up to wri+i for A(x) from transfinite induction up to    for a formula
of level higher than the level of A(x).

10.2.3. We now want to refine the preceding theorem to a corresponding
result for the subsystems Zk of Z.

THEOREM. (Provable initial cases of TI in Zk) Let 1 < E < k. Then in Zk
we can derive transfinite induction for any formula A(x) of level < L up to
wke+2[m] for arbitrary in, i.e.

        Vx(Vy-x A(y)       A(x))     Vx-c4.;k_e+2[m] A(x),

where wi [m] := m,       [m] :=
PROOF. Note first that if A(x) is a formula of level E > 1, then the formula
A+ (z) constructed in the proof of the preceding theorem has level E + 1, and
for the proof of
        If A(x) is progressive, then A+ (x) is progressive,
10.3. Normalization with the omega rule                                    325

we have used induction with an induction formula of level E.
  Now let A(x) be a fixed formula of level < t, and assume that A(x) is
progressive. Define A° := A, A2+1 := (A4)+. Then lev(A2) <     i, and hence
in Zk we can derive that A1, Az    Aki+1 are all progressive. Now from the
progressiveness of A"+1(x) we obtain A"+1(0), A"+1 (1), Ak(2) andi+1.
generally Aki+1(m) for any m, i.e. Aki+1(Wi[m]). But since
        Aki+1(x)       (Akt)±(x) = Vy(Vz-q A"(z) --+ V.z.-<y ED biX A" (Z))

we first get (with y = 0) V.z-<co2[m] A"(Z) and then A"(cid2[m]) by the
progressiveness of A". Repeating this argument we finally obtain
        VZ-<Wk_t+2[717.] A° (Z).

   Our next aim is to prove that these bounds are sharp. More precisely, we
will show that in Z (no matter how many true 111-formulas we have added as
axioms) one cannot derive "purely schematic" transfinite induction up to eo,
i.e. one cannot derive the formula
        Vx(Vy-x Py         Px) VxPx
with a relation symbol P, and that in Zk one cannot derive transfinite induc-
tion up to wk+i, i.e. the formula
        Vx(Vy-x Py         Px)      Vx-<cok+i Px.

This will follow from the method of normalization applied to arithmetical
systems, which we have to develop first.


10.3       Normalization with the omega rule
We will show in theorem 10.4.12 that a normalization theorem does not hold
for arithmetical systems Z, in the sense that for any formula A derivable in Z
there is a derivation of the same formula A in Z which only uses formulas of
a level bounded by the level of A. The reason for this failure is the presence
of induction axioms, which can be of arbitrary level.
   Here we remove that obstacle against normalization in a somewhat drastic
way: we leave the realm of proofs as finite combinatory objects and replace
the induction azdoms by a rule with infinitely many premises, the so-called
co-rule (suggested by Hilbert and studied by Lorenzen, Novikov and Schiitte),
which allows us to conclude that VxA(x) from A(0), A(1), A(2), ..., i.e.
                         DO
                        A(0)       A(1)  ' '  A(n)   " co
                                       VxA(x)
So derivations can be viewed as labelled infinite (countably branching) trees.
As in the finitary case a label consists of the derived formula and the name of
326                                       Chapter 10. Proof theory of arithmetic

the rule applied. Since we define derivations inductively, any such derivation
tree must be well-founded, i.e. must not contain an infinite descending path.
   Clearly this w-rule can also be used to replace the rule VI. As a consequence
we do not need to consider free individual variables.
   It is plain that any derivation in an arithmetical system Z can be trans-
lated into an infinitary derivation with the w-rule; this will be carried out
in lemma 10.3.5 below. The resulting infinitary derivation has a noteworthy
property: in any application of the w-rule the cutranks of the infinitely many
immediate subderivations Dr, are bounded, and also their sets of free assump-
tion variables are bounded by a finite set. Here the cutrank of a derivation is
as usual the least number > the level of any subderivation obtained by *I as
the main premise of +E or by the w-rule as the main premise of VE, where
the level of a derivation is the level of its type as a term, i.e. of the formula
it derives. Clearly a derivation is called normal iff its cutrank is zero, and
we will prove below that any (possibly infinite) derivation of finite cutrank
can be transformed into a derivation of cutrank zero. The resulting normal
derivation will continue to be infinite, so the result may seem useless at first
sight. However, we will be able to bound the depth of the resulting derivation
in an informative way, and this will enable us in 10.4 to obtain the desired
results on unprovable initial cases of transfinite induction. Let us now carry
out this programme.
  N.B. The standard definition of cutrank in predicate logic measures the
depth of formulas; here one uses the level, as in section 6.10.

10.3.1. DEFINITION. We introduce the systems Z" of w-arithmetic as fol-
lows. Z' has the same language and apart from the induction axioms
the same axioms as Z. Derivations in Z" are infinite objects. It is useful to
employ a term notation for these, and we temporarily use d, e, f to denote
such (infinitary) derivation terms. For the term corresponding to the deduc-
tion obtained by applying the w-rule to di, i E IN we write (di)i<. However,
for our purposes here it suffices to only consider derivations whose depth is
bounded below 60.
  In the present chapter we will also regard the term t in VE as a "minor
premise" , as mentioned in 2.1.6, remark (v). The notion of a track (see 6.2.2)
is adapted accordingly.

DEFINITION. We define the notion "d is a derivation of depth < a" (written
dl < a) inductively as follows (i ranges over numerals).
       (A) Any assumption variable uA with A a closed formula and any axiom
           axA is a derivation of depth < a, for any a.
      (A) If dB is a derivation of depth < ao < a, then (AuAAB)A -4.8 is a
           derivation of depth < a.
10.3. Normalization with the omega rule                                     327

  (+E) If dA-+B and eA are derivations of depths <aj < a (i=1,2), then
        (dA-4.13 eA)B is a derivation of depth < a.


    (w) For all A(x), if d) are derivations of depths < ai < a (i < w),
         then ((diA(i))2<w)VmA is a derivation of depth < a.

   (VE) For all A(x), if dv.A is a derivation of depth < ao < a, then, for all
         (d'dx Ai)A(i) is a derivation of depth < a.



NOTATION. We will use PI to denote the least a such that d < a.
  Note that in (VE) it suffices to use numerals as minor premises. The reason
is that we only need to consider closed terms, and any such term is in our
setup identified with a numeral.

10.3.2. DEFINITION. The cutrank cr(d) of a derivation d is defined by

        cr(uA)      := cr(axA) := 0,
        cr(Au.d)    := cr(d),
        cr(dAseA)       r max(lev(A + B), cr(d), cr (e)) if d = Au.d',
                          max(cr(d), cr(e))              otherwise,
        cr((di)i<w) :=        cr(di),
                        f max(lev(VxA), cr(d)) if d =
        cr(exAi)    :=
                            cr(d)                   otherwise.

Clearly cr(d) E IN U {w} for all d. For our purposes it will suffice to consider
only derivations with finite cutranks (i.e. with cr(d) E IN) and with finitely
many free assumption variables.

10.3.3. LEMMA. If d is a derivation of depth < a, with free assumption
variables among u, fi and of cutrank cr(d) = k, and e is a derivation of depth
< ,8, with free assumption variables among 7.7 and of cutrank cr(e) =
then d[u/e] is a derivation with free assumption variables among 77, of depth
I d[u/e] I <fi + a and of cutrank cr(d[u/e]) < max(lev(e) , k,E).
PROOF. Straightforward induction on the depth of d.

10.3.3A. * Give the proof in some detail.

10.3.4. Using this lemma we can now embed our systems Zk (i.e. arithmetic
with induction restricted to formulas of level < k) and hence Z into Z°°. In
this embedding we refer to the number 711(d) of nested applications of the
induction schema within a Zk-derivation d.
328                                            Chapter 10. Proof theory of arithmetic

DEFINITION. The nesting of applications of induction in d, ni(d), is defined
by induction on d, as follows.
         ni(u)       := ni(ax) := O (axioms and assumption variables),
         nI(Ind)     := 1,
         ni (Ind de) := max(ni(d), ni(e) + 1),
         ni(de)      := max(ni(d), ni(e)), if d is not of the form Ind do,
         ni(Au.d) := ni(d) (case of -*I).
         ni(Ax.d) := ni(d) (case of VI).
         ni(dt)       := ni(d) (case of VE).

10.3.5. LEMMA. Let a Zk-derivation in long normal form (see 6.7.2) be
given with <m nested applications of the induction schema, i.e. of
Ind(A, x)    A[x/0]      Vx(A -+ A[x/Sx]) -+ VxA.
all with lev(A) < k. We consider subderivations dB not of the form Ind E or
Ind rdo. For every such subderivation and closed substitution instance Bo- of
B we construct (d) in Ze° with free assumption variables           for tic free
assumption of d, such that Idr1 < wm+1 and cr(dn < k, and moreover such
that d is obtained by        iff dr is, and d is obtained by VI or of the form
Ind rdoe iff do.' is obtained by the w-rule.
PROOF. By recursion on such subderivations d.
Case zic or ax. Take etc' or ax.
Case Ind rde'. Since the deduction is in long normal form, e' = Axv.e. By IH
we have do.e° and ea."). (Note that neither d nor e can have one of the forbidden
forms Ind r and Ind rdo, since both are in long normal form). Write e,'(t, f)
for eo.'[x, v/t, f], and let
         (Ind Ed(Axv .e))r := (dr, e0 (O, dr), er (1, 40(0, dr)),       .).

By IH 1401 <          .p and WI < wmq for some p,q < w. By lemma 10.3.3
we obtain
         140(0, dc,`,11 < wm.q +
         Ie0(1,e0(0,d0))I < wm.q + win-1.2p
and so on, and hence
         1(Ind d(Axv.e))(:1 < wm.(q + 1).

Concerning the cutrank we have by IH cr(dn, cr(e,') < k. Therefore
         cr(e)(0, dn) < max(1ev(A(0)), cr(dc:), cr(e°))           k,
10.3. Norrnalization with the omega rule                                     329

and so on, and hence

        cr((Ind d(Axv.e)),'.))   k.

Case AuC .d3 . By 1H, we have (dT)B6 with possibly free assumptions uc'.
Take (Au.d),7 := AuCff
Case de, with d not of the form Ind tor Ind tdo. By III we have d," and ec".
Since de is subderivation of a normal derivation we know that d and hence
also do" is not obtained by       Therefore (de)" := de" is normal and
cr(d,we" ) = max(cr(dn,cr(e")) < k. Also we clearly have ld"e." I < w"1.
Case (Ax.d)vxB(x). By 1H for every i and substitution instance B(i)o- we have
dZi. Take (Ax.d)." := (do"i)i<c.
Case (dt)B[xiti. By IH, we have (don (Vx.13)o Since dt is a subderivation of a
normal derivation, d is not obtained by VI, hence dwo is not obtained by the
w-rule. Therefore we may take (dt)" := don, where i is the numeral with the
same value as tu.

10.3.6. DEFINITION. A derivation is called convertible or a redex if it is of
the form (Au.d)e or else (d)<j, which can be converted into d[u/e] or dj,
respectively. A derivation is called normal if it does not contain a convertible
subderivation. Note that a derivation is normal iff it is of cutrank O.
   Call a derivation a simple application if it is of the form clod]. ...dm with
do an assumption variable or an axiom.

10.3.7.     We want to define an operation which by repeated conversions
transforms a given derivation into a normal one with the same end formula
and no additional free assumption variables. The usual methods to achieve
such a task have to be adapted properly in order to deal with the new situation
of infinitary derivations. Here we give a particularly simple argument due to
Tait [1965].

LEMMA. For any derivation dA of depth < a and cutrank k +1 we can find a
derivation (dk)A with free assumption variables contained in those of d, which
has depth < 2 and cutrank < k.
PROOF. By induction on a. The only case which requires some argument is
when the derivation is of the form de with Idl <      <a and ll <a2 < a, but
is not a simple application. We first consider the subcase where dk = Au.di(u)
and lev(d) = k 1. Then lev(e) < k by the definition of level (recall that
the level of a derivation was defined to be the level of the formula it derives),
and hence di[u/ek] has cutrank < k by lemma 10.3.3. Furthermore, also by
lemma 10.3.3, di[u/ek] has depth < 2a2 + 2'1 < 2'('2,"1)+1 < 2'. Hence we
can take (de)k to be di[u/ek].
330                                       Chapter 10. Proof theory of arithrnetic

   In the subca,se where dk = (di),<, lev(d) = k 1 and ek = j we can take
(de)k to be d3, since clearly di has cutrank < k and depth < 2. If we are not
in the above subcases, we can simply take (de)k to be dkek. This derivation
clearly has depth < 2°. Also it has cutrank < k, which can be seen as follows.
If lev(d) < k + 1 we are done. But lev(d) > k +2 is impossible, since we have
assumed that de is not a simple application. In order to see this, note that
if de is not a simple application, it must be of the form dodi     d,-,e with do
not an assumption variable or axiom and do not itself of the form d'd"; then
do must end with an introduction q or w, hence there is a cut of a degree
exceeding k + 1, which is excluded by assumption.

10.3.7A. 4 Complete the proof.
As an immediate consequence we obtain

10.3.8. THEOREM. (Normalization for Z') For any derivation dA of depth
<a and cutrank < k we can find a normal derivation (d*)A with free assump-
tion variables contained in those of d, which has depth < 2, where 27 := a,
4+1 := 22k
   As in section 6.2 we can now analyze the structure of normal derivations
in Z`K). In particular we obtain

10.3.9. THEOREM. (Subformula property for Z°°) Let D be a normal de-
duction in Z' for r A. Then each formula in D is a subformula of a formula
in r u {A}.
PROOF. We prove this for tracks (see 6.2.2) of order n, by induction on n. Z

10.3.9A. 4 Complete the proof.


10.4       Unprovable initial cases of TI
We now apply the technique of normalization for arithmetic with the w-rule
to obtain a proof that transfinite induction up to ro is underivable in Z, i.e.
a proof of

        Z V Vx(Vy-<x Py > Px)         VxPx

with a relation symbol P, and that transfinite induction up to cok+i is unde-
rivable in Zk, i.e. a proof of

        Zk V Vx(Vy--<x Py      Px)
10.4. Unprovable initial cases of TI                                                  331

It clearly suffices to prove this for arithmetical systems based on classical
logic. Hence we may assume that we have used only the classical versions
PA2c, ordlc and ord2c of the axioms from section 10.2.
   Our proof is based on an idea of Schiitte, which consists in adding a so-
called progression rule to the infinitary systems. This rule allows us to con-
clude Pj (where j is any numeral) from all Pi for i j.

10.4.1. DEFINITION. More precisely, we define the notion of a derivation in
Z"' + Prog(P) of depth <c by the inductive clauses of definition 10.3.1 and
the additional clause Prog(P):
(Prog)     If for all i j we have derivations dr of depths <cj < a, then
           Wi)P. i is a derivation of depth < a.
We also define cr(d.i).i,i) :=         cr(di).
  Since this progression rule only deals with derivations of atomic formulas, it
does not affect the cutranks of derivations. Hence the proof of normalization
for Z' carries over unchanged to Z' + Prog(P). In particular we have

10.4.2. LEMMA. For any derivation dA in Z" + Prog(P) of depth < a
and cutrank < k + 1 we can find a derivation (dk)A in Z°° + Prog(P) with
free assumption variables contained in those of d, which has depth < 2' and
cutrank < k.

10.4.3. We now show that from the progression rule for P we can easily
derive the progressiveness of P.

LEMMA. We have a normal derivation of Vx(Vy--<x Py                          Px) in Ze° +
Prog(P) with depth 5.


          iPi
PROOF.
                Py
                     VE
                   Pi                            (all i   j)
                                                               Prog
                            Pj
                           >
                     Vy-0 PyPj                                        ...   (all j)
                          Vx(Vy-<x Py > Px)

10.4.4. The crucial observation now is that a normal derivation of Pr
must essentially have a depth of at least 0. However, to obtain the right esti-
mates for the subsystems Zk we cannot apply lemma 10.4.2 down to cutrank
0 (i.e. to normal form) but must stop at cutrank 1. Such derivations, i.e.
those of cutrank < 1, will be called quasi-normal; they can also be analyzed
easily.
332                                       Chapter 10. Proof theory of arithmetic

10.4.5. We begin by showing that a quasi-normal derivation of a quantifier-
free formula can always be transformed without increasing its cutrank or its
depth into a quasi-normal derivation of the same formula which

      does not use the w-rule, and
      contains VE only in the initial part of a track starting with an axiom.

Recall that our axioms are of the form Vi 'A with A quantifier-free.

DEFINITION. (Quasi-subformula) The quasi-subformulas of a formula A are
given by the following clauses.

      A, B are quasi-subformulas of A      B;

      A(i) is a quasi-subformula of VxA(x), for all numerals i;
      if A is a quasi-subformula of B, and C is an atomic formula, then C -+ A
      and VxA are quasi-subformulas of B;

      "... is a quasi-subformula of ..." is a reflexive and transitive relation.


EXAMPLE. Q > Vx(P --+ A), P, Q atomic, is a quasi-subformula of A -4 B.
  We now transfer the subformula property for normal derivations (theo-
rem 10.3.9) to a quasi-subformula property for quasi-normal derivations.

10.4.6. THEOREM. (Quasi-subformula property) Let T, be a quasi-normal
deduction in Z + Frog(P) for I' I- A. Then each formula in T, is a quasi-
subformula of a formula in r U {A}.
PROOF. We prove this for tracks of order n, by induction on n.

10.4.6A. 4 Prove this in detail.

10.4.7. COROLLARY. Let 7, be a quasi-normal deduction in Z"+Prog(P) of
a formula VgA with A quantifier-free from quantifier-free assumptions. Then
any track in 7, of positive order ends with a quantifier-free formula.
PROOF. If not, then the major premise of the >E whose minor premise is
the offending end formula of the track, would contain a quantifier to the left
of >. This contradicts theorem 10.4.6.                                      Ei

Our next aim is to eliminate the w-rule. For this we need the notion of an
instance of a formula.
10.4. Unprovable initial cases of TI                                           333

10.4.8. DEFINITION. (Instance) The instances of a formula are given by the
following clauses.
       If B' is an instance of B and A is quantifier-free, then A -4 B' is an
       instance of A -4 B;
       A(i) is an instance of VxA(x), for all numerals i;
       The relation "... is an instance of ..." is reflexive and transitive.

10.4.9. LEMMA. Let D be a quasi-normal deduction in Zc° + Prog(P) of a
formula A without V to the left of -4 from quantifier-free assumptions. Then
for any quantifier-free instance A' of A we can find a quasi-normal derivation
TY of A' from the same assumptions such that
       TY does not use the w-rule,
       TY contains VE only in the initial elimination part of a track starting
       with an axiom, and

       ITY1   IDI.

PROOF. By induction on the depth of D. We distinguish cases according to
the last rule in D.
Case >E.
                                 A -4 B A >E
By the quasi-subformula property 10.4.6 A must be quantifier-free. Let B' be
a quantifier-free instance of B. Then by definition A -4 B' is a quantifier-free
instance of A > B. The claim now follows from the IH.
Case
                                                -41
                                      A -4 B
Any instance of A > B has the form A > B' with B' an instance of B.
Hence the claim follows from the IH.
Case VE.
                                 VxA(x)         i
                                   A(i)             VE

Then any quantifier-free instance of A(i) is also a quantifier-free instance of
VxA(x), and hence the claim follows from the IH.
Case w.
                               A(i)     ... (all i <w) co
                                       VxA(x)
Any quantifier-free instance of VxA(x) has the form A(i)' with A(i)' a quan-
tifier-free instance of A(i). Hence the claim again follows from the IH.  N
334                                             Chapter 10. Proof theory of arithmetic

10.4.9A. 4 Do the remaining cases.

DEFINITION. A derivation d in Z°°+Prog(P) is called a P                  g-refutation
if C't and g are disjoint and d derives a formula 2,1" --+ B := A1 -+     --+ Ak   B
with JT and the free assumptions in d among Prai-',        ,

  -13'73n-I or true quantifier-free formulas without P, and B a false quantifier-
free formula without P or else among P'731-1, , P'73n7 .
   (So, classically, a      .P:(3'-refutation shows A, Prai7 -4 V, Prie[.)

10.4.10. LEMMA. Let d be a quasi-normal Pd',---,Pg-refutation. Then
         min (T3) < dl + lh(ä),
where ä is the sublist of S consisting of all cx, < min(Th, and 1h(ä) denotes
the length of the list 5'.
PROOF. By induction on ldl. By lemma 10.4.9 we may assume that d does not
contain the w-rule, and contains VE only in a context where leading universal
quantifiers of an axiom are removed. We distinguish cases according to the
last rule in d.
 Case       By our definition of refutations the claim follows immediately from
the IH.
 Case >E. Then d          fc-r(I-r13)ec If C is a true quantifier-free formula
without P or of the form Pr-y1 with -y < min* the claim follows from the
IH for f:

         min(g)      If I + lh(51) +1    Idl +
If C is a false quantifier-free formula without P or of the form Pr-y-1 with
min(g) < -y, the claim follows from the IH for e:

         min(T)      lel +1h(ä) + 1 <_ Idl + ih(ein
It remains to consider the case when C is a 5uantifier-free implication involv-
ing P. Then lev(C) > 1, hence lev(C > (A > B)) > 2 and therefore (since
cr(d) < 1) f must be a simple application (10.3.6) starting with an axiom.
Now our only axioms involving P are Eqp: Vx, y(x = y > Px -+ Py) and
Stabp:              Px), and of these only Stabp has the right form. Hence
f = Stabpr-y7 and therefore e: -I-Pr-C. Now from 1ev(-1-,Pr-y1) = 2, the
assumption cr(e) < 1 and again the form of our axioms involving P, it follows
that e must end with >I, i.e. e = Au-Pr-Y1.4. So we have
                                                  [u: -,./3r77]
                                                       eo
                                                       J_
                                        pr71
                                        pry-i
10.4. Unprovable initial cases of TI                                                335

The claim now follows from the IH for eo.
Case VE. By assumption we then are in the initial part of a track starting
with an axiom. Since d is a P5, -,P[3'-refutation, that axiom must contain
P. It cannot be the equality axiom Eqp: Vx, y(x = y        Px     Py), since
1-7-1 = EP      PE77 -4 PEP can never be (whether -y = 6 or 7 0 (5) the
end formula of a Pa', -,Pß-refutation. For the same reason it can not be the
stability axiom Stabp:Vx(-,---,Px   Px). Hence the case VE cannot occur.
Case Prog(P). Then d = (drr),P,r-71-. By assumption on d, 7 is in g. We
may assume 'y =   := min(g), for otherwise the premise deduction  P73-1
would be a quasi-normal Pd, -43g-refutation, to which we could apply the
IH.
  If there are no a., < -y, the argument is simple: every clj is a Pa,
refutation, so by IH, since also no ai <6,

          min (g, 6) =          d5I

hence 7 = min(g) <
  To deal with the situation that some cei are less than 'y, we observe that
there can be at most finitely many ai immediately preceding 7; so let E be
the least ordinal such that
          V6(e < 6 < -y -> ô E
Then e,e + 1,             + k - 1 E 5, e + k = -y. e is either a successor or a limit.
                                                                                -
                     ,

If e = e' + 1, it follows by the IH that since de is a Pa,
refut ation ,

          e - 1 < 14_1 +lh(&) - k,
where ee' is the sequence of ai < 7. Hence e < idi+ lh(Ckg) - k, and so
          -y < di = lh(61).
If e is a limit, there is a sequence (6f(n)),, with limit e, and with all ai < e
below 6 f(0), and so by IH

          6 f (n)   id f (n)1   lh(&) - k,
and hence e 5_ Idf(n)1+ lh(cV) - k, so 7 < I dI                                      N

10.4.11. THEOREM. Transfinite induction up to ec, is underivable in Z, i.e.
          Z V Vx(Vy--<x Py            Px)    VxPx
with a relation symbol P, and for k > 3 transfinite induction up to wk+i is
underivable in Zk, i.e.
          Zk                          Px)    Vx-<wk+i Px.
336                                      Chapter 10. Proof theory of arithmetic

PROOF. We restrict ourselves to the second part. So assume that transfinite
induction up to wk+i is derivable in Zk. Then by the embedding of Zk into
Z" (lemma 10.3.5) and the normal derivability of the progressiveness of P
in Zoo + Prog(P) with finite depth (lemma 10.4.3) we can conclude that
Vx-<wk+i Px is derivable in Z" + Prog(P) with depth < wm+1 and cutrank
< k. (Note that here we need k > 3, since the formula expressing transfinite
induction up to wk+i has level 3). Now k 1 applications of lemma 10.4.2
yield a derivation of the same formula Vx-<wk+i Px in Z' + Prog(P) with
depth 7 < 2r1+1 < wk+i and cutrank < 1.
  Hence there is also a quasi-normal derivation of Prry+37 in Z" + Prog(P)
with depth 7 + 2 and cutrank < 1, of the form

                       Vx-<wk+iPx                       TY
                  +       coic+i   Pr7 +        r'y +        (.4.4+1
                                   Pr'y
where TY is a deduction of finite depth (it may even be an axiom, depending
on the precise choice of axioms for Z); this contradicts lemma 10.4.10.  E

10.4.12. Normalization for arithmetic is impossible
The normalization theorem for first-order logic applied to one of our arith-
metical systems Z is not particularly useful since we may have used in our
derivation induction axioms of arbitrary complexity. Hence it is tempting to
first eliminate the induction schema in favour of an induction rule allowing
us to conclude VxA(x) from a derivation of A(0) and a derivation of A(Sx)
with an additional assumption A(x) to be cancelled at this point (note that
this rule is equivalent to the induction schema), and then to try to normalize
the resulting derivation in the new system Z with the induction rule. We will
apply theorems 10.4.11 and 10.2.2 to show that even a very weak form of the
normalization theorem cannot hold in Z with the induction rule.

THEOREM. The following weak form of a normalization theorem for Z with
the induction rule is false: "For a.ny derivation dB with free assumption vari-
ables among itA for formulas A, B of level < t there is a derivation (d*)B,
with free assumption variables contained in those of d, which contains only
formulas of level < k, where k depends on t only."
PROOF. Assume that such a normalization theorem holds. Consider the
formula

          Vx(Vy-x Py     Px)               Px
expressing transfinite induction up to b..),,+1, which is of level 3. By theo-
rem 10.2.2 it is derivable in Z. Now from our assumption it follows that there
10.5. TI for non-standard orderings                                          337

exists a derivation of this formula containing only formulas of level < k, for
some k independent of n. Hence Zk derives transfinite induction up to wn+i
for any n. But this clearly contradicts theorem 10.4.11.                    El



10.5       TI for non-standard orderings
The results proved up to now in this chapter all refer to the standard definition
of a well-ordering -- of order type 60 in section 10.1. We now consider the
question whether these results can be transferred to orderings defined in a
less standard way. It will turn out that all our attempts in this direction fail.
   The results in this section require classical logic, but apart from that are
to a large extent independent of the particular formulation of an arithmetical
system. However, in 10.5.4 it will be convenient to be more specific about
the function constants allowed. Therefore we assume that we have constants
for all primitive recursive functions; clearly it then suffices to have a single
relation constant = for equality. As non-logical axioms we take the defining
equations for all primitive recursive functions (and of course the equality
axioms) plus the Peano axioms PA1, PA2c and the induction schema from
10.2.1. The resulting formalism is called Peano arithmetic PA.

10.5.1. We first consider the schema TI< (A, x), where < is a primitive
recursive (non-standard) definition of a well-ordering of order type <ro. By
means of a counterexample we will see that in general TI< (A, x) is unprovable
in PA, even if the ordering defined by < is the standard ordering < of the
natural numbers.
   Let VxA(x) be an arbitrary universal formula of arithmetic. We may as-
sume that x < y AA(y) > A(x) is provable; otherwise take Vz<x A(z) instead
of A(x). Depending on A we define an ordering <A by
                {n < m and A(n), or
        n <A RI :=
                  771 <n and -,A(n).


Then n <A m or m <A n whenever n m. To see this, suppose n < m.
Then in case A(n) we have n <A m, and in case -,A(n) we also have -,A(m)
by our assumption on A, hence m <A n.
   If VxA(x) is true, <A defines the standard ordering < of IN. Otherwise there
is a minimal k such that -A(k) holds; the ordering may then be visualized as
        0, 1, 2, 3, ..., k   1, ... k + 3, k + 2, k + 1,k,

i.e. the initial segment [0, k 1] ordered by <, followed by the segment (w, k]
ordered by >. So the linear ordering <A is a well-ordering iff VxA(x) holds.
   We now show that we can formally derive VxA(x) from an instance of
transfinite induction on <A within PA, or more precisely
        PA -I- TI<, (A, x)l- VxA.
338                                        Chapter 10. Proof theory of arithmetic

To prove (2), recall that TI<, (A, x) is
        Vy(Vx<Ay A(x)          A(y))   VxA(x).
It clearly suffices to prove the premise Vy(Vx<Ay A(x) > A(y)). So let y be
given and assume
(3)     Vx<Ay A(x).
We have to show A(y). So assume -,A(y). Then k < y for the minimal k
such that -,A(k). Because of the form (1) of the ordering <A we can conclude
that y is in the non-well-founded part of <A, hence y + 1 <A y. Therefore
A(y + 1) by (3), contradicting ---,A(k) and k < y <y + 1.
   Note that if A is quantifier-free, then the ordering <A is primitive recursive
(and the above argument may be recast in minimal logic). Now since there
is a true formula Vx(fx = 0) with f primitive recursive that is unprovable in
PA (e.g. the formula expressing the consistency of PA), we have

PROPOSITION. There is a primitive recursive definition <i of the standard or-
dering of IN such that PA does not derive the schema TI< (A, x) of transfinite
induction with respect to <I.                                               El


10.5.2. We now ask ourselves whether PA I- TI<(A, x) for an ordering <
and all arithmetical A implies that < defines a well-ordering of order type
less than ro. The answer is no, in a strong sense: it is not even true that such
a < must be well-founded, even if we require it to be primitive recursive. We
now prove this by means of a counterexample. The idea for this example is
based on the properties of an implicit truth function for arithmetic. As a first
step we need Tarski's classic result on the undefinability of a truth predicate
for arithmetic.
   For the rest of this chapter we presuppose some familiarity with Gödel
numberings of arithmetic. We shall assume that a standard numbering for
terms, formulas and formal proofs of classical first-order arithmetic PA has
been given.
  We use p for some standard primitive recursive bijective coding of pairs of
natural numbers onto the natural numbers, with inverses po, pi.
  Furthermore there is some coding of finite sequences from IN into IN, such
that the primitive recursive extraction function Axy. (x)5 given by

        ( n)       = xyotherwise,
                        if y < u,
               Y     {0
for an n coding the sequence (x0, xl,       ,   xu_i), and a primitive recursive
length function lth such that
        lth(n) = u.
  For the Gödel number of an expression E we write rE7.
10.5. TI for non-standard orderings                                         339

10.5.3. THEOREM. (Undafinability of a truth predicate for PA) A truth
predicate for arithmetic is a predicate T such that T(A) A is true for all
arithmetical sentences A. There is no arithmetically definab/e truth predicate
for arithmetic.
PROOF. Let Sub, be the arithmetical operation such that
         Sub,(Ft-', FA-1) = FA[z/tr,
where z is a fixed variable, t a term, and [z/t] indicates substitution of t for
the variable z. Assume now T to be arithmetically definable.
         S(x,y) := T(Subz(rY7, Y)),
where -a := 0, n + 1 := STE. Then we have
         S(rt, FA-1) 44 A[z/T-1].

To see this, note
         S(97,,F A-1)4S(n,FA-1)44T(Sub,(FTT,-1, FA-1))44T(FA[z/77]-1)44A[z/rd.
Now a contradiction follows. Let
         A := ThS(z, z),    and Ti =
Then
         S()                A-1)    A[z    = 45(97, T).

10.5.4. Implicit truth function
Let f be the characteristic function of the truth predicate for arithmetical
sentences, i.e. for sentences A:
         f(A) = O 44 A.
(For definiteness, we may assume fn to be any value, say 0, on n which are
not the Gödel number of a formula). f is not arithmetically definable, as we
have seen, but in any case it must satisfy a number of conditions with respect
to the logical operators:
       f(rsi = s2-1) = O i4 Val(Fsi-1) = Val(r827),
       f (c(rA-i, rB1)) =O     f (r-A-1\
                                      ) = 0 A f (FEr) = 0, where c(FA-1,1-B-1) =
       FA A Er',

       f (n(F A-1)) = O 4 f(FA) = 1, where n(FA) =
       f (FVviA(vi)) = O 44 Vn( f (Sub,, (1-    FA-1)) = 0),
where Val is a function computing the value of the closed terms. The con-
ditions (i)(iv) completely determine f on the set Sent of Gödel numbers of
sentences.
340                                       Chapter 10. Proof theory of arithmetic

LEMMA. f satisfies a II?-condition of the form

        Vx]yR(x, y, f),
where R is a primitive recursive predicate.
PROOF. We recast the conditions above. For the components (n)i of n, when
n is viewed as the code of a finite sequence, we write ni in this proof. For
definiteness, we assume that if n E Sent, then no describes the main operator
of a formula given as a Gödel number: no = 0 for rA-1 = n prime, no = 1, 2, 3
for conjunctions, negations, and universal quantifiers respectively. From (i)
(iv) we obtain

        VnESent((fn = O ± {(no = O -4 Val(ni) = Val(n2)) A
                            (no = 1 -4 fni = 0 A fn2 = 0) A
                                (no = 2 * fni     0) A
                                (no = 3 -4 Vm(f (Sub(ni, n2, m)) = 0))1) A
                  (fn     O -4 {(no =      Val(ni) Val(n2)) A
                                (no = 1 -4 fni 0 V fn2 0) A
                                (no = 2 -4 fni = 0) A
                                (no = 3    Am' (f (Sub(ni , n2, m'))   0))1)).
Here Sub(ni, n2, m) = Sub2 ('Fi n, n1) and if no = 3, n codes f-Vvn2B-1. Note
that Val(ni) = Val(n2) can be written in the form 3kQ(ni, n2, k) with primi-
tive recursive Q. Intuitively, Q(ni, n2, k) says that k codes two terminating
computations yielding the values of the closed terms coded by n1, n2, and
that the values are equal. Similarly, Val(ni)    Val(n2) can be written as
3klq(ni, n2, k').
   By moving the quantifiers Vm, 3m', 3k, 3k' outwards we obtain a quanti-
fier-free formula R preceded by VnVm3m/3k3e, and the truth of the lemma
is now obvious.                                                                  N


10.5.4A. * Describe the construction of Q mentioned in the proof.

10.5.5. REMARK. At this point one can conclude easily that Beth's defin-
ability theorem 4.4.2B and hence also the interpolation theorem 4.4.2 cannot
hold for Peano arithmetic PA. To see this, note that as in 10.5.4 one can
give an implicit definition of the truth predicate T for arithmetic (here for
definiteness we assume that Tn is false for n which are not the Gödel number
of a formula), in the form A(P) := Vx3yR(x, y, P) with a unary predicate
symbol P and a primitive recursive predicate R. Clearly P is uniquely deter-
mined by A(P), i.e. A(P) A A(Q)     Vx(Px 44 Qx) is derivable in PA. Now
if Beth's theorem would hold, then there would be a formula C not involving
P such that A(P) Vx(C 44 Px) in derivable in PA and hence true in the
standard model. This contradicts Tarski's undefinability theorem 10.5.3.
10.5. TI for non-standard orderings                                              341

10.5.6. DEFINMON. Let fix := minyR(x, y, f), where f is the characteris-
tic function of the truth predicate, and R is as above.
   Note that VxR(x, f'x, f) holds. Let (f', f) be the encoding of f' and f into
a single sequence; this sequence is obviously not arithmetical, but satisfies
the I17-condition just mentioned.

10.5.7. We now want to argue that any pair f', f satisfying VxR(x, fix, f)
is such that f is the characteristic function of the truth predicate for arith-
metical sentences. To see this, observe that from WR(x, f'x, f) we obtain
Vx3yR(x, y, f) and hence the condition given in the proof of the lemma in
10.5.4. But as already noted this determines f on the set Sent of Gödel
numbers of sentences.

10.5.8. Let us now make use of this insight to produce the counterexample
we are aiming at. As a first step we will rewrite VxR(x, f'x, f) in the form
WQ(TEx), or more precisely construct a primitive recursive predicate Q such
that (f', f) I VxR(x, f'x, f) 1 = { a Q(75x) 1.
  The first step consists in replacing each subterm ft in R(x, f'x, f) by pi (at)
and f'x by po(ax), yielding the form V xRi(x , a). We now argue that this
can be rewritten as
        Vx`91xi .    Vxn(xi = ati A       A xn = atn      R2(X,         ,Xn))

where t1,... ,tn are terms without a. This can be proved easily by induc-
tion on the number of nestings of a; e.g. Vx(a(ax) = 0) is rewritten as
VxVxiVx2(xi = ax A x2 = axi -4 x2 = 0). Now this can be further rewritten
as
         VyVx, xi,        , xn, Yi,   , Yn<Y (Yi = ti A    Ay = tn A
                      x1 = ayi A      A xn = ay n -+ R2(x, xi,    5   Xn))
Finally ayi can be replaced by (rty)y, and y by lth(rty). This yields the form
VxQ(a-x) with a primitive recursive Q.

10.5.9. DEFINITION. Let a be a variable ranging over functions in 1\1 >
With any 111-sentence Va3x-Q(ax) we associate a tree
        TrQ :-= { ax I Vy<x Q(rty) }.

The converse of the partial ordering <1 on TrQ (initial segment ordering of
finite sequences) can be extended to a linear ordering 4* (the Brouwer-Kleene
ordering of Tr(?) by defining the converse
         rxx        ,3y if either (-6-x <I -igy) or
                                  (Tex = ,T3z and az > ,8z for some z < x, y).
342                                        Chapter 10. Proof theory of arithmetic

10.5.10. LEMMA. If TrQ is well-founded under the converse of <i, then <I*
is a well-ordering.
PROOF. Consider any infinite sequence within TrQ

        dOXO N* alX1 N* TV2X2 N* '     ;



from this we find an increasing sequence in <, within TrQ, that is to say, an
infinite sequence a in TrQ. For a0 we can take (assuming xo > 0)

         a0 = hm ai0.
               i-+00

This limit is determined, since d1x1 is either a prolongation of(Teoxo, or doz =
     and aiz < aoz; so either a00 = a10 or a10 < a00; the value of ai at 0
can go down at most finitely often, then ai0 remains fixed. And so on for
al, a2 etc.

10.5.11. THEOREM. The BrouwerKleene ordering <1* of the HIsentence
Vce3x,Q(Cix), Q as in 10.5.8, is primitive recursive, not well-founded, but
well-founded w.r.t. all arithmetical sequences. It follows that TI.1- (A, x) holds
for any arithmetical formula A(x), i.e.

        Vy(Vx<*yA(x)        A(y))     VxA(x).

PROOF. If the BrouwerKleene ordering <* were well-founded, it would mean
that there was no truth definition; in other words, the encoding of arithmetical
truth (fi, f) provides an infinite sequence on the BrouwerKleene ordering.
  On the other hand, we have observed in 10.5.7 that any a = (fi, f) satis-
fying VxQ(eix) and hence VxR(x,          f) is such that f is the characteristic
function of the truth predicate for arithmetical sentences. Hence there is no
arithmetically definable such a, i.e. <* is arithmetically well-founded.
  Finally let A(x) be any arithmetical formula and assume that (A, x)
does not hold. Then the premise Vy(Vx<*yA(x) > A(y)) is true but the
conclusion VxA(x) is false, hence --,A(x0) for some xo. From the premise for
xo we obtain an x1 1*xo such that ,A(xi), then an x2<*x1 such that iA(x2),
and so on. If we pick the smallest xo such that ,A(xo), then the smallest
xi <* xo such that --,A(xi) and so on, we obtain an arithmetically definable
sequence xo, x1, x2, . . such that xi+i <*xi for all i, contradicting our previous
                       .


observation.


10.6       Notes
Some important general references on the branch of proof theory generated
by (modifications of) Hilbert's programme (cf. remarks in the preface) are
10. 6. Notes                                                                 343

Schötte [1960], Kreisel [1977], Schötte [1977], Takeuti [1987], Girard [1987b],
Pohlers [1989], Buchholz et al. [1981]. Girard [1987b] covers more than just
proof theory in the Hilbert programme tradition. In the appendices to Takeuti
[1987] some leading proof-theorists have given their views on proof theory.

10.6.1. Gentzen's consistency proofs. The proof in Gentzen [1936] starts
from a formalism for arithmetic based on natural deduction. Gentzen defines
a notion of "reduction step" for deductions, which preserves correctness. If
no reduction step is possible, the conclusion must be a sequent the truth of
which is immediately decidable. He then assigns ordinal notations less than e0
to derivations and shows that suitable reduction steps lower the ordinal (no-
tation) assigned to a derivation, ultimately producing a derivation to which
no reduction step is applicable. A fully reduced derivation of 1 = 2 is impos-
sible, and from this it may be concluded that arithmetic is consistent. In fact,
Gentzen's argument uses        (A, x) for a quantifier-free A in his consistency
proof.
   Originally Gentzen had a different version of the proof, not based on trans-
finite induction, but on a notion of "reduction rule" instead. A reduction rule
is something like a strategy for reducing derivations to correct derivations.
Objections raised to this proof because of a supposed use of Brouwer's fan the-
orem induced Gentzen to shortcircuit this discussion by using transfinite in-
duction instead. On this early version of Gentzen's proof, see Bernays [1970].
   Gentzen's first proof is not easy to follow, and in Gentzen [1938] he presents
a second version, based on a "Gentzen system" (as it is called in this book),
which is more perspicuous, even if the formalism of arithmetic itself is some-
what less natural.
   Finally, in Gentzen [1943], he proved the initial cases of transfinite induc-
tion along - (10.2.2) and gave a direct proof of the underivability of        (P)
for a predicate letter P (10.4.11).
   Schötte [1950a] showed that Gentzen's consistency proofs could be made
more perspicuous using an infinitary proof system with w-rule (such as Z in
our exposition), and embedding standard arithmetic in the infinitary system.
   Our exposition in section 10.4 takes Gentzen [1943] as point of departure,
but incorporates Schötte's idea of using an infinitary system. Moreover, the
logical basis is an N-system; for a similar exposition based on a Gentzen
system, see Schwichtenberg [1977].
   Gentzen's results on transfinite induction provided the first example of a
true, mathematically meaningful statement not provable in first-order arith-
metic, in contrast to the original incompleteness result of Gödel, where the
unprovable statement was entirely motivated by metamathematical consid-
erations. Still, transfinite induction up to ec, might be regarded as esoteric.
The first example of a purely combinatorial statement, of "straightforwardly
mathematical character" was found by Paris [1978]; see also Harrington and
344                                       Chapter 10. Proof theory of arithmetic

Paris [1977]. After the first result of this type, many more followed; examples
with references may be found in Takeuti [1987, section 12], Buchholz and
Wainer [1987], Gallier [1991], Friedman and Sheard [1995].

10.6.2. Subsystems of Z. Refinements of Gentzen's theorem 10.2.2 on prov-
able and 10.4.11 on unprovable initial cases on TI in Z to corresponding results
for the subsystems Zk were first obtained by Mints [1971] and Parsons [1973].

10.6.3. Continuous cut elimination. An important version of cut elimina-
tion for infinitary systems is continuous cut elimination, due to Mints [1975].
Provided one permits a "repetition rule" (which simply repeats the premise
as the conclusion), cut elimination may be defined as a continuous operation
(in the usual tree topology) on prooftrees.
   This technique has been successfully applied in, for example, Gordeev
[1988] and Buchholz [1991]. Buchholz obtains a neat proof of the uniform
reflection principle by this method. The uniform reflection principle may be
stated as

        ProofpA(EA(±)7       A(x))     (FV(A) C {x}),

where Proofs is the standard arithmetized proof predicate for system S, and
rA(&)1 is the Gödel number of A(Sx0) as a function of x, i.e. r A(&)7 is
represented by a term containing at most x free.
  For continuous normalization of infinite terms, see Schwichtenberg [1998].

10.6.4. TI for non-standard orderings Both counterexamples in the text
are due to Kreisel. The first one, in 10.5.1, was given by Kreisel in lectures
on proof theory at UCLA (Kreisel [1968]). It is also mentioned in Kreisel
[1977]. The second one, leading to theorem 10.5.11, is from Kreisel [1953].
In fact, we can find a primitive recursive ordering which is not well-founded,
but well-founded w.r.t. all hyperarithmetical sequences. This follows from
the characterization of II1-predicates as EHyp-predicates given by Kleene
[1955, Theorem XXVI].
  This should be contrasted with the result of Friedman and Scedrov [1986]
showing that matters for intuitionistic first-order arithmetic HA are different.
   The remark on the failure of interpolation for arithmetic (10.5.5) we owe
to G.E. Mints, who considers it to be folklore.
Chapter 11

Second-order logic

11.1       Intuit ionist ic second-order logic
There exists a close connection between intuitionistic second-order logic and
the so-called polymorphic lambda calculus A2. A2 is an extension of A,
permitting abstraction over type variables, and under the formulas-as-types
paradigm it may be regarded as isomorphic to the natural deduction system
for intuitionistic second-order propositional logic -4V2Nip2, that is to say,
1\Trilp extended with quantification over propositions. A2 is an important
component of various type systems studied in computer science.
  In this chapter we show how strong normalization for intuitionistic second-
order predicate logic may be reduced to normalization for Nmp2, and we
present a proof of strong normalization for --Al2Nip2 (= )2). Next we show
that intuitionistic second-order arithmetic HA2 (formal intuitionistic anal-
ysis) can be represented in intuitionistic second-order logic, and show that
every recursive function which is provably total in HA2 can be represented by
a term of A2. From the formal deduction establishing totality of the function
being considered, one can read off an algorithm, encoded by a term of A2, for
computing the function.

11.1.1. Description of Ni2
To the first-order language, second-order quantifiers VXn, 3.)Cn are added. If
we wish to distinguish the symbols for second-order quantification from those


                   AVXnA
for first-order quantification, we write V2, 32. The additional quantifier rules
are given by

             VYnA[Xn/Yn] V2I                   A[Xn/Axi    xn.B] V2E

                                                          [A[Xn I Yn]]u

          A[Xn Axi       xn..13]                 3XnA          C    32E
                                   321
                 3Xn A
                                         345
346                                                 Chapter 11. Second-order logic

 where

       in V21 A does not depend on open hypotheses containing Xn free, and
       Yn is free for Xn in A;

       A[Xn/Axi    xn.13] is obtained from A by replacing each occurrence of
       a subformula Xnti tn in A by B[xi,...,xn/ti.,      , tn]



       in 32E Yn does not occur free in assumptions on which C depends exept
       A[Xn /1/1, nor does Yn occur free in C.

These rules are the same as in 6.6.3, except that the restriction on B has
been dropped.


11.1.2. Restriction to the language with -+, V, V2

There is a good deal of redundancy in the operators of second-order logic,
since we can define 1_, A, V, ], A' from --+, V, V2 as follows. In the definitions
below X° is not free in A, B.

          1     :=(VX°) X° ,
          A A B := V X° ((A -4 (B -4 X)) -> X),
          A V B := VX°((A -> X) -4 ((B X) -> X)),
          3yA := VX°(Vy(A -4 X) -4 X),
          3YA := VX°CdYn(A -> X) -4 X)).

Under these definitions, the usual introduction and elimination rules for the
defined operators become derived rules in the fragment based on        V, V2.
For example, the following deductions show that AI, AEL are derivable.

      A-4(B--X°) u    A
          B.- X°          B                                           Au
                X°                 VX° ((A->(B-a) )->X)             B --+ A
         (A->(B-> X°))-- - a°          (A-qB--+ A))- } A          A-qB --+ A) -
       V X° ((A-4(B--+ X))--+ X)                         A

and the proof of AER is similar to the proof of AEL. Note that the distinction
between minimal and intuitionistic logic disappears in second-order logic.
  Henceforth we shall assume I2 to be formulated with primitives -4, V, V2
only, unless expressly indicated otherwise.


11.1.2A.      Derive the rules for the other defined operators.
11.1. Intuitionistic second-order logic                                     347

11.1.3. Normal deductions and normalization for Ni2
We can formulate notions of conversion, reduction and normal form in the
same way as for Ni. In particular, to the detour conversions of the +V-
fragment of Ni we add V2-detour conversions:

                      A                          D[Xn / ..B]
                  VYnA[xn/yn]
                                          cont
                                                 A[Xn / Ai.B]
                   A[Xn / A.B]
Since we restrict attention to the *V V2-language, there is no need for con-
sidering permutative conversions and immediate simplifications. But it is
of interest to note that the detour conversions for the operators A, V, _L,], 32
correspond under the definitions to transformations of prooftrees which result
from --*V V2-detour conversions. On the other hand, permutative conversions
correspond after translation under the definitions to transformations not gen-
erated by the V V2-detour conversions.

11.1.4. -PROPOSITION. Strong normalization w.r.t. detour conversions of
Ni2 in the full language is reducible to strong normalization w.r.t. detour
conversions for the *V V2-fragment of Ni2.

11.1.4A. 4 Prove the preceding proposition in detail.
11.1.4B. 4 Give an example of a permutation conversion in the full second-order
language which does not translate into a series of conversions relative to V and
V2

There is no meaningful subformula property for second-order logic. Any
A[Xn1A1..13] ought to count as a subformula of VXnA, but the logical com-
plexity of the subformula may be very much larger than the complexity of
VXnA. This is also the reason why it does not seem to be worthwhile to
strive for normalization relative to the full language, including permutative
conversions.
  Nevertheless, some useful conclusions can be drawn from the fact that a
derivation can be brought into normal form.
  For one thing, a normal derivation of a first-order formula (i.e. a formula
without V2) does not contain second-order quantifiers. Another example is
given by the following (cf. 6.2.7D):

11.1.5. PROPOSITION. A normal derivation without open assumptions ends
with an introduction.
PROOF. Let 7, be a normal derivation without open assumptions. Assume
that D ends with an elimination rule. Follow a main branch (defined as in
348                                              Chapter 11. Second-order logic

6.2.5) starting from the conclusion. We pass through eliminations only; at
the top we find a formula which cannot be an open assumption (there are
none, by hypothesis), but also cannot be discharged by --q since there are no
introductions below this formula; contradiction.                            El



11.1.6. PROPOSITION. Let D be a normal derivation in Ni2 of AV B without
open hypotheses, i.e. D derives VX°((A -- X) -- (B > X) -4 X). Then
Ni2 F- A or Ni2 I- B.

PROOF. First proof. There is an immediate proof from the preceding propo-
sition, if we consider normal deduction w.r.t. the full language, so that V
appears as a primitive.
   However, it is instructive to see how we have to argue if V is defined and
we are reasoning about the >V V2-fragment.
  Second proof. Let us follow the main branch (defined as in 6.2.5) of D,
going upwards from the conclusion.
  If the final rule applied in D is an E-rule, then the main branch passes
through eliminations only and its topmost formula must be an open assump-
tion, which is impossible. So the final rule applied is V2I. The immediate
subdeduction D1 of D therefore terminates with (A-4X) -- (B-->X) -4 X
and has no open assumptions. Again, the final rule of D1 must have been an
introduction, so the premise (B --> X) > X is the conclusion of a subdeduc-
tion D2 from open assumptions of the form A --> X.
Case 1. A -4 X does actually occur as the top formula of the main branch.
Then the first rule applied to A --> X has to be an elimination rule, otherwise
A --> X or VX(A -+ X) would have to occur as a subformula of the conclusion
in the strict sense. We see that this is impossible, if we keep in mind that X
does not occur in A or B. So >E is applied at the top -


                                           D'
                                A    >XA
                                     X

- and then introductions must follow in the main branch. D' may use A -->
X, B > X as open'assumptions. But if in D' we replace the X everywhere by
A V B, these assumptions become derivable and we have found a deduction
for A.
Case 2. If there is no formula A -4 X at the top of the main branch, it must
be the case that the final rule of D2 is an introduction discharging B -4 X
at the top of the main branch and possibly other places. The argument is
similar to the preceding case, and we find a deduction of B.              E
11.2. Ip2 and A2                                                            349

11.2       Ip2 and A2
11.2.1. Ni2 and polymorphic lambda calculus
In a more or less routine fashion we can reformulate Ni2 as a calculus of
typed terms. We shall not give here the description for the full calculus,
but only for intuitionistic second-order propositional logic Ip2. In Ip2 only
propositional variables X°, Y°, zo,      occur; we drop the superscript O. As in
the full system, 1, A, V, 3, 32 are definable.
   The new clauses describing the formation of terms for deductions in propo-
sitional Ni2 are given by
              t: A              t: (VX)A
         AX .t: (V X)A     t()- B: A[X I B]
There is an obvious condition to be met in the case of V2I: t may not contain
free individual variables with a type in which X occurs free. We have added
new operators of type abstraction, AX, and type application (application of
a term to a type (= formula). The resulting calculus of typed terms is also
known as the polymorphic lambda calculus or system F (Girard [1971,1972])
or A2.
  Henceforth term will be used for first-order terms; for second-order terms
we use type or formula.
  The conversions for --> and V2 correspond in term notation to

         (ÀaA .tB)(sA) cont t[xA I sA]: B
         (AXIA: (V X)B)A cont t[X I A]: B[X IA]

Observe that we do not have application on the level of types: instead of
having ((V X)A)B convert to A[X I B], we simply identify ((V X)A)B with
A[X I B], so that we can in fact dispense with the notation ((V X)A)B.
  For this system we shall prove strong normalization and uniqueness of
normal form in the next section. The remainder of this section is devoted to
computational aspects of A2, in preparation for section 11.5.

11.2.2. Computational content
DEFINITION. Let X be a fixed propositional variable in A,. We put

         N'x := X -4 ((X --> X) --> X).

This is the type of (variant) natural numbers over X. The so-called (variant)
Church numerals are terms of type Nix in normal form:
         filx := Axx fx-+'.f(x) : mx,
350                                                 Chapter 11. Second-order logic

where as before
         f0(x) :=
                         f"1(x) := f (fri(x))-
We shall drop the subscript X in the sequel, since it will be kept fixed.       IE

  Of course we can also define it'A and NIA for an arbitrary type A in the same
manner.

NOTATION. In the remainder of this chapter we shall simply write NA, fiA
for N'A, filA respectively.                                                     El


11.2.2A. 4 Show that the variant Church numerals of type X are the only terms
in normal form of type N Nx

11.2.2B. 4 All extended polynomials are representable in the variant Church
numerals. Hint. Take as representing terms
         F+ := AxNyN zx x x
         F := Ax NyN zX X X XZ (Aux .yu f)
         Fpk :=
         Fc := AxN
         Fsg   := AxNyx fx-+x. xy(Azx .fy)
               := Ax NyX fX-a .x(fy)(Azx .y).

As we have seen before in 1.2.21, the class of representable functions becomes
larger, if one considers NA for arbitrary A, and permits representing terms
where the types of the input numerals and output numerals may differ.
  In A, there is arbitrariness in the choice of the type X in Nx. This
arbitrariness is removed in A2. There we put:

11.2.3. DEFINITION.
         N := V X(X           ((X > X) > X)),
           "ft := AX Axx fx'x fn (x).
The results on representability of extended polynomials carry over to A2,
modulo small adaptations. But as will become clear from the exercises, many
more functions are representable in A2 than are representable in A,. In
particular, the functions representable in A2 are closed under recursion.

11.2.3A. 4 Show that the following operators p, Po, Pi may be taken as pairing
with inverses for types U, V with a defined product type U A V:
         p := AUEIVV AXAX(11->X).XUV,U->
         Po := Axunv .xu(Ayu zv .y),    /31 := Axunv.xv(Avu zv .z).

N.B. These terms encode the deductions exhibited in 11.1.2.
11.3. Strong norrnalization for NIL'                                     351

11.2.3B. 4 Let S -=7_ AzNAXAxxyx-4x .y(zXxy), It         AX.ÀuXfXzN.zXuf.
Show that
         It Xux fxrx6                u,
         It Xux fx-4x (St) = f (It Xux fx-4xt).

11.2.3C. 4 Define with the help of pairing and the iterator of the preceding
exercise a recursor Rec such that
         Rec Xux fx-4(N-006 =ux
         Rec Xux fx-4(N--)x)(sn) = f(Recuffi)ft.


11.3       Strong normalization for Ni2
We first show that strong normalization for full second-order logic can be
reduced to strong normalization for propositional Ni2 or A2.

11.3.1. PROPOSITION. Strong normalization for Ni2 is a consequence of
strong normalization for propositional Ni2.
PROOF. We define a mapping from formulas and deductions of Ni2 to
formulas and deductions of propositional Ni2, as follows.

        0(xnt1...tn):=x*
where X* is some propositional variable bijectively associated with the rela-
tion variable Xn, and for compound formulas we put
        çb(A > B) := çbA -4 OB,
        .1)(VXnA) :=VX*0A,
        çb(VxA)    :=Vx*OA, x* not free in OA.
Here x* is a propositional variable associated to the individual variable x.
Deductions are translated as follows. We write 114 for "0 maps to".
 The single-node prooftree "A" is translated into the single-node prooftree
440A,

  For prooftrees of depth greater than one, we define inductively

                               1-4
        A > B -41                           OAB -41
                    D'                            OD     OTY
        A -4 B      A
                         _4E
                                          1-4     > OB   OA
352                                                       Chapter 11. Second-order logic


                                      i
                D                                        OD
            A[Xn]2
                 VI
                                      0
                                                       0(A[X])
       VYnA[xn/111                                                   VI
                                                 çb(VY*A[xn/y1)
            D
           VXnA
                       V2E
                                      i
                                      0
                                                      OD
                                                   V X*0(A)
       A[Xn I Ax.13]                             .0(A)[X* 10B] V E

          A[x]0
           D

       VyA[x/y] V/
                                I-4
                                               OD
                                           0(A[x])
                                          Vy*O(A[x])
                                                        V21


          D                               OD
                            0
        VxA                 F4        V x* çbA
               VE                                V2E
       A[x It]                            OA

Note that for all individual variables -±' and terms
        OA -- - .0 (A[±7n).

Furthermore,
        D >.-   V'     OD        0(D').                                               Z

11.3.2.     In contrast to the situation for A, the propositional variables
in Ni2 cannot simply be regarded as formulas of minimal complexity, since
in the course of the normalization process quite complex formulas may be
substituted for these variables. The notion of computability for A2 has to
reflect this; the idea is to assign "variable computability predicates" to the
propositional variables. A "computability candidate" has to satisfy certain
requirements. A straightforward generalization of 6.8.3 (on which the proof
of strong normalization of A2 in Girard et al. [1988] is based) is obtained by
defining the notion of a computability candidate as follows.

DEFINITION. A term t is called non-introduced if t is not of the form Ax.s or
AX.s. A set of terms X, all of the same type A, is a computability candidate
(a c.c.) (of type A) iff
CC1 If t E X then SN(t);
CC2 If t E X and t         e then e E X;

CC3 If t is non-introduced, and Vti--<it(ti E X) then t E X.                          Z
As a corollary of CC3 we find
CC4 If t : A is non-introduced and normal, then t E X.
Instead of this definition, obtained by transferring the properties C1-3 in 6.8.3
from computability predicates for function types to c.c.'s, we use the slightly
different notion of a saturated set which is convenient for generalizations.
11.3. Strong normalization for Ni2                                           353

11.3.3. Saturated sets. To motivate our definition of saturated sets we first
collect some properties of the set SN of strongly normalizable terms. In this
section, e w ill be used for a sequence of first- and second-order terms (types).
We say that 't is in SN, if the first-order terms of t are in SN.

LEMMA.

      If e E SN, then for any variable x of the appropriate type xe E SN.
      If t E SN, then Ax.t E SN.
     If t[x/r]e E SN and r E SN, then ().x.t)re E SN.
      If t E SN, then AX.t E SN.
      If t[x Bie E SN, then (AX.t)Be E SN.
PROOF. (i) Immediate, since every reduction step must take place in a mem-
ber of e.
  (ii), (iv) are treated similarly.
  (iii) (cf. lemma 6.8.4) Assume t[x/r]e E SN and r E SN; we have to show
(Ax.t)re E SN. We use induction on fir + hg+ ht, the sum of the sizes of the
reduction trees of r, e and t. If (Ax.t)re>-1 t", then either
      t"   (Ax.t)riE.' with r   r', and by induction hypothesis t" E SN; or
      t"   (Ax.t)re with ei          and by induction hypothesis t" E SN; or
      t"   (Ax.e)re with t      t', and by induction hypothesis t" E SN; or
      t"   t[x/rV, and t" E SN holds by assumption.
  (v) is treated similarly.
  Parts (i), (iii) and (IT) yield non-introduced terms. We call a set A of
strongly normalizable terms of type A saturated if it is closed under (i), (iii)
and (v):

DEFINITION. A set A of terms is said to be saturated of type A (notation
A: A) if A consists of terms of type A such that
Sat-1 If t E A, then t E SN.
Sat-2 If e E SN, then for any variable x of the appropriate type xE E A.
Sat-3 If t[x/rV E A and r E SN, then (Ax.t)re E A.
Sat-4 If t[X/EnE'E A, then (AX.t)Ii3f.'E A.
  So in particular the set SNA of strongly normalizable terms of type A is
saturated.
354                                              Chapter II. Second-order logic

11.3.4. DEFINITION. The following definition of a predicate of strong com-
putability "Comp" extends the definition given before for predicate logic.
  Let A be a formula with FV(A) C X, and let II B1, . . , Bn be a sequence
of formulas of the same length, and let fi B1,    , Bn be a sequence of

saturated sets with Bi: B. We define CompA[g.1,6] (computability under
assignment of      to.g.) as follows:
       Compxge/ti] :=
        CompD,D[ie/] := { tESN : VsECompD[je/](ts E Compc[X/]) 1,
        Comp (,,y)c[fe/tij := { tEsN : VDVD: D(tD E Compc             DD
        (D ranging over types).                                             El


NOTATION. In order to save on notation, we shall use in the remainder of this
section a standard abbreviation: we write Comp*D for CompD[X'/11], where
Bi: Bi are saturated sets (1 <i < m), fixed in each proof. So Comp*D[Y/C]
stands for CompD       Y/ti, C] etc.                                    El


11.3.5. LEMMA. Comp*A is a saturated set of type AP- e I I-3].
PROOF. We have to show Sat-1-4 with Comp for A, i.e.
  If r E Comp*A then r E SN.
      If &E SN then xe E Comp.
       If r[xl s]e E Comp;!1 and s E SN, then (Ax.r)se E Comp.
     If r[Y1C]e E Comp*A then (AY.r)Ce E Comp.
       follows from the definition of Comp*A and the fact that every saturated
set is a subset of SN.
        is proved by induction on the depth of A. So assume E.' E SN. Note
that this implies xe E SN, by the properties of SN.
 Case (ii)1. A -a X. By Sat-2 for Bi we find xe E Bi, and hence xe E Comp.
 Case (ii)2. A m A1 > A2. We have to show xe E ComP*A1-4,42 Assume
s E Comp*Ai; we then have to show xes E Comp%. Since s E SN by (i), we
find that xes E Comp% (using (ii) for A2).
 Case (ii)3. Am (VY)Ai. We have to show that xe E COMW(`vymi . So let
C: C be a saturated set, then we must show that xeC E Comp*A, [Y/C]. But
this is a consequence of (ii) for Ai.
        is proved by induction on the depth of A. We assume s E SN, r [O]e E
Comp. Note that this implies (Ax.r)sa'E SN, by the properties of SN.
Case (iii)1. A m X. We have to show (Ax.r)se E B. But s E SN, so this
follows from Sat-3.
 Case (iii)2. A -m A1 > A2. Let t E Comp%. Then we must show (Ax.r)set E
Comp*A2. By IH for A2 it suffices to show that r[x/s]et E Comp*A2, which
holds by definition of Comp.
11.3. Strong normalization for Ni2                                         355

Case (iii)3. A   (VY)Ai. Let C: C be a saturated set. We must show
(Ax.r)sec E COmp*Ai [Y/C]. By the IH for A1 it suffices to show that r [x/s]eC E
Comp*Ai [Y/C], which holds by definition.
 (iv) is again proved by induction on the depth of A. Let r[Y/C]e E Comp.
Note that this implies (AY.r)CeE SN, by the properties of SN.
Cases (iv)1 and (iv)2. Left to the reader.
Case (iv)3. A  (VZ)Ai. Let D: D be a saturated set. We must show
(AY.r)CeD E Comp*AJZ/D]. By the IH it suffices to show r[Y/C]rD E
Comp*Ai [Z/D], which is trivial.


11.3.5A. 4 Supply the proofs of the missing cases for (iv) in the proof of the
preceding lemma.


11.3.6. LEMMA. Let        13' be a sequence of saturated sets as before. Then

        CompA[ym [XXI] = CompAPZ, Y/ft, compc[X-A.

(The right side is well-defined by the preceding lemma.)
PROOF. By induction on the complexity of A. Let A          VZ.B. Then

        Comp*NzB)Eym :=
        { tESN : VDVD:D(tD E CoMP*B[Y/C][Z/D])
        { tESN : VDVD:D(tD E Compl[Y, Z/Comp*c, D]) =
        Comp:I[Y/Comp*c].

We leave the other cases to the reader.

11.3.6A. 4 Complete the proof of the preceding lemma.

11.3.7. THEOREM. Let t[xi: A1,            ,    An]: C, and assume that the free
second-order variables of {t, A1,    ,   An} are contained in
  For 1 < i < m, 1 < j < n let Bi: Bi be saturated sets, si: A1[. /É],
si E CompAi [Xlii]. Then

        t[fe /AVM E ComPc[gA.
PROOF. Let us write e for t[5e/P]ri/gl. We prove the statement of the
theorem by induction on t.
Case 1. t xfi. Immediate, since si E Comp*A, by assumption.
Case 2. t rs. By IH, r*, s* are strongly computable, hence so is r*s*.
356                                                    Chapter 11. Second-order logic

Case 3. t r(vz)AC: A[Z/C]. By IH r* E COMp&z)A. By the definition of
Comp*, lemma 11.3.5 and lemma 11.3.6

               r*C[je /A] E COMp*A[Z/CoMp*c.] = COM13(vc].

Case 4. t    Azcl.rc2. We have to show that Azca/A.r* E COMpc2. So
assume s E Comp'¿.i. Then we have to show (Ax.r*)s E COMp%. By Sat-3 it
suffices to show that rlx/s] E COMp% (for Comp'¿.2 is saturated by lemma
11.3.5). But this follows by IH from

                              / .9] = r[.J?". /   x/    s].

Case 5. t ÀZ.r. t* is of the form AZ.e. We have to show t* E COMp k"vz)Ai
So let C: C. Then we have to show (AZ.r*)C E Comp':41[Z/C]. By Sat-4 we
                                                                                    .




need only to show r*[Z/C] E Comp*Ai [Z/C], which follows by IH.

COROLLARY. All terms of A2 belong to SN, hence they are strongly normal-
izable.

11.3.8. An auxiliary system
In section 11.5 we should like to map deductions and formulas of second-
order arithmetic to terms and types of A2, in such a way that the notion of
reducibility is preserved, and second-order propositions go to the correspond-
ing type. For this it is necessary that (VX)X is mapped to an inhabited
type of A2; but since the type (VX)X is uninhabited in A2, we introduce the
auxiliary system A2S2. In the next section we shall show that in A2S1 precisely
the same recursive functions are representable as in A2; this is proved by a
suitable encoding of AA/ into A2.

DEFINMON. Let A2S1 be obtained from A2 by adding a constant a VX.X.
There are no conversion rules involving a

THEOREM.

      The terms in AA/ are strongly normalizable.
      Normal forms in A2 and AA/ are unique.
      If we include conjunction as a type-forming operator, strong normaliza-
      tion and uniqueness of normal form remain valid for A2 and AZ/.
PROOF. (0 As for A2, adding some cases where necessary.
  (ii) By extending the proof of weak confluence in 1.2.11. The rest of the
proof is left to the reader.
11.4. Encoding of A211 into A2                                                          357

11.3.8A. * Supply the missing details in the proof of the preceding theorem.


11.4        Encoding of A212 into A2
11.4.1. PROPOSMON. Let t: N > N be a [closed] term in A21. Then there
is a [closed] term e in A2 such that th fit eft --
PROOF. For the proof we define (1) an encoding ° of types and terms of AA/
into A2, for which it can be proved that if t >-1 t', then t° (e)°, and (2)
maps W, C such that Wh, n°, Cit° ft. From this the e in the statement of
the theorem is obtained as AzN .C(t°(Wz)). Once the right definitions for °, W,
C have been given, the proofs become straightforward inductive arguments,
which are left almost entirely to the reader.
  We define the encoding map ° on types by
          .X°          := X,
          (A + B)° := A° > B°,
          (V X.A)°     := VX (X         A°).
It follows that
          (A[X/ B])°        A°[X /
In order to define the encoding of terms, we assume that there is associated to
each type variable X a "fresh" individual variable x of type X, not occurring
free in the terms to be encoded. The correspondence between the X and the
associated xx is assumed to be one-to-one. Below, in the definition of the
encoding, we shall use the tacit convention that the type variables Xi, X, Y
have xi, x, y associated to them.
  For A with FV(A) = {X1,                     ,   Xp}, we define a term rA: A° with free
variables xi:        ..., xp: Xp, X1,              Xp as follows:
          rxi  := xi: Xi
          TB-*C := Ay: B°            (y Ø FV(7-c))
          TVX.B := AX AXX TB
For closed A, TA : A° is closed. For example,
          r(vx)x = AX Axx .x: VX (X                 X).
We now extend ° to terms, and associate to each t E A, with free variables
X1,  , Xp,  A1,      , yq: Aq a term t°: A° with free variables X1,   , Xp,
xl: X1,     , xp: Xp, yi:            , yq: A°q, as follows:
          if A E Ai            then (y: A)°
          if A E B       C then          (Ay: B.t: C)°
                                         ((t: B-4A)(s: B))°             (t°: B°>A°)(s°: B°);
          if A a (VX)B then (AX.t:VX.B)°                               AX Ax: X.t°: B°;
          if A E B[X/C] then ((t: (V X)B)C)°                        := (t°: ((VX)B)°)C°1-c;
                                        110
358                                                  Chapter 11. Second-order logic

Then one verifies commutativity with substitution:
        (t[y: Al s: A])° t° [y: A°/s°:
        TA[xig      TA[X B°][x: B° ITB: B°], and
        (t[X I B])°    t° [X I B°][x: B° I TB: B°]

by induction on t, A and t respectively, and uses this in verifying
        if t --1 t' then t° -- (e)°.
For example, we have as one step in the induction for (ii):
        7-(vy)c[x/B] = AYAYYTc[x/B] =
        AYW.(Tc[XIB°][x: B° I TB: 131)
        (AnyY.(rc))[XIB°][x: B°/1-B: B°] =
        T(vy)c [XIB°][x: B° I TB: B°].
Further, we note that
        N°            VX(X > (X    ((X    X)     X)))
        (71)°         AX-Axxyxzx'x.zny.
We can define operators W ("weaken") and C ("contract") such that
                >--      Cft°   ft;

simply take
        W := AuNAXAxx yx zx'x .uXxz,
        C := MIN° AX Ayx zx-4x .uXyyz.
For the term t' of the proposition we may now take
           := AzN .C(t° (W z)).

11.4.1A. * Fill in the missing details of this proof.


11.5       Provably recursive functions of HA2
11.5.1. DEFINITION. Intuitionistic second-order arithmetic HA2 (alterna-
tive notation HAS) is obtained taking the language of pure second-order
logic, with a single individual constant 0 (zero), a single function constant S
(successor), and a binary predicate symbol = for equality between individ-
uals, with the axioms and rules of intuitionistic second-order logic, and the
following azdoms for equality and successor:
        Vx(x = x),
        V XlVxy(x = y A Xx > Xy),
        Vxy(Sx = Sy > x = y),
        Vx(,Sx = 0), i.e. Vx(Sx = O > (V X°)X),
11.5. Provably recursive functions of HA2                                  359

and the induction axiom:

        VX1(X0 A V x(X x + X (Sx))          VyXy).

Note that the second equality axiom implies

        Vxy(x =y±y= x);
        Vxyz(x=yAx=z-4y=z);
        Vxy(x = y + Sx = Sy).

(For the first, take Xz (z = x), then x = y A Xx   Xy yields x = y A
x=x-->y=x, and since x = x holds, x = y > y = x; for the second take
Xx (x -= z); for the third, take Xz (Sx =Sz)).

11.5.2. DEFINITION. A subsystem HA2* based on 12 and equivalent to HA2
is the following. The language consists of 0, S, = as before, but we define a
predicate EV by

        x E EV    Nx := V X1 (X0 -4 (V x(X x         X (Sx)) + X x)).

As axioms we include
        Vx(x = x), Vxyz(x = y (x = z y = z)),
        Vxy(Sx = Sy -4 x = y), Vxy(x = y Sx = Sy),
        Vx(Sx = O --+ (VX°)X).

The standard model of HA2* (and of HA2) has IN and the powersets of INk
as domains of individuals and k-place relations respectively; 0, S, = get their
usual interpretation.

11.5.3. DEFINITION. xn E Ext := ViElNWElN(i = il A X'> Xil), where
  E IN stands for xi E     , xn E IN etc.
  So "X E Ext" means that X behaves as an "extensional predicate" w.r.t.
IN, or, perhaps more appropriately, satisfies replacement w.r.t. elements of
IN. Note that IN E Ext.

11.5.4. DEFINITION. (Interpretation of HA2 in HA2*) Formulas of HA2
can now be interpreted in HA2*, by relativization of all individual variables
to IN, and all relation variables to Ext; so Vx, 2x go to VxElN, 3xElN, and
vxn,3xn to VXnEExt, 3XnEExt; with respect to the other logical operators
the embedding is a homomorphism.
  From now on we take as a matter of convenience the language based on
-4, A, V, V2, 3; from the results in 11.1.4 we know that we have strong normal-
ization w.r.t. detour conversions for this language.
360                                                 Chapter 11. Second-order logic

11.5.4A. 4 Verify that the embedding of the definition (call it 0) indeed satisfies
for all closed A of HA2: HA2 I- A   HA2* I- 0(A).


11.5.5, DEFINITION. (Normal deduction D[n] of SnO E IN in HA2*) For
7,[0] we take

                                   0E X1
                     Vy(y EX -+ Sy E X)   0EX
                0 E X > (Vy(y E X > Sy E X) -4 0 E X)
                                                              V21
                                   0 E IN

and for D[n] if n> 0:

                                                   [0 E X]2
                 Vy(y E X -* Sy E X)1               Dn-1
                 Sn-10 E X -> SnO E X vr'         Sn-10 E X
                                                                 E
                                   SnO E X
                    Vy(y E X Sy E X) -4 SnO E X
                0 E X -->Vy(y E X ->Sy E X) ->SnO E X
                                                                 V2I
                                   SnO E IN

where Dn_1 is either 0 E X (for n = 1) or is of the form

                                                       [0 E X]
                    Vy(y E X        Sy E X)            Dn-2
                   Sn-20 E X       Sn-10 E X VE      Sn-20 E X
                                     Sn-10 E X                                   1E1




It is easy to see that D[n] translates under the collapsing map into fl of A2.

11.5.6. LEMMA. D[n] is the unique normal deduction of SnO E IN.
PROOF. Let 7, be a normal deduction of SnO E IN. D cannot end with an
E-rule. For assume D to end with an E-rule; if we follow a main branch
from the conclusion upwards, the branch must start in a purely first-order
axiom, such as Vx(x = x), or in Vx(Sx = O -> (VX°)X). From a purely first-
order axiom we can never arrive at the conclusion alone, passing through
eliminations only. Elimination starting from Vx-iSx = 0 must begin with

                        Vx(Sx =         (V X)X)       DI
                          St = 0      (VX)X         St = 0
                                       (VX)X
11.5. Provably recursive functions of HA2                                 361

However, no open assumptions of D' can be discharged lower down; so D'
must deduce St = 0 from the axioms. But in the standard model St = 0 is
false (here we rely on the consistency of the system).
   Therefore the deduction ends with an introduction, with subdeduction
of the premise O E X        (Vy(y E X --+ Sy E X)      SnO E X). Again, the
final step of 1,1 must be an introduction, and the premise of the conclusion
of D1 is Vy(y E X          Sy E X) + SnO E X, which is the conclusion of
subdeduction D2 from assumptions O E X. D2 cannot end with an E-rule;
for if it did, a main branch of D2 would have to terminate either in O E X or
in an axiom. The axioms are excluded as possibilities for the same reasons
as before (assign IN to the variable X in the "standard model" part of the
argument). To 0 E X no elimination rule is applicable. So the final step of
D2 is an I-rule, and the immediate subdeduction D3 of D2 derives SnO E X
from assumptions 0 E X and Vy(y E X          Sy E X). The last rule of D3 must
be an elimination rule, and the main branch must terminate in 0 E X or in
Vy(y E X         Sy E X). If it terminates in 0 E X and n = 0, we are done.
Terminating in 0 E X while n 0 is impossible. So assume the main branch
to start in Vy(y E X      Sy E X):

                                   Vy(y E X           Sy E X)   Ty,
                                      tEX+StEX                  tEX
                                                      St E X


but then (St E X)               (Sn0 E X) etc.

11.5.7. DEFINITION. We define a collapsing map I from formulas and
deductions of HA2* to formulas and deductions of A212. Let M be a fixed
inhabited type of A20, e.g. M V X(X --> X), containing T AXAx.xx . To
the relation variables Xn we let bijectively correspond propositional (type-)
variables X*. For formulas we take
        [[t =                   := M,
        1[Xt1             4,1   := X*,
        [[AB                    := 1[A] --+ 1113]],
        1[Vzil]]                := 11/11,
        113 zit]]               := 11,41,
           XnAl                 := VX*[[.,41.

Observe that
         11A[x I    tll               [[t E iN1       N.

The definition is extended to deductions as follows. We have not before in-
troduced a complete term calculus for HA2*, but the notations below will be
362                                                           Chapter 11. Second-order logic

self-explanatory. The definition proceeds by induction on construction of de-
duction terms, or what is the same, by induction on the length of deductions.
First the basis case, assumptions and axioms:

           Ai                         1> xi: [[A,17
        Vx(x =                           T: M,
        Vxyz(x = y     (x = z y = z)) 1-4 Axmym .Tm:M > M                                      M,
        Vxy(Sx = Sy x = y)            1-4 Aym.Tm: M +
        Vxy(x = y --+ Sx = Sy)        1-4 Aym.Tm: M M,
        Vx(Sx =      VX.X)                Azm.S2: M (V X)X.

For the rules we put

        AxA.0: A + B                     1> Axi[A] .[[t][1131:[[A          131,
        tA-+B sA: B                      1>
        Axi.t:VxA                        F>         I[Vx1 All (note 11V xl              [[A[x /y11),
        tVyr A[x/y] 8/ A[x s]                                (note [[All       liVyA[x /O),
          (to tiA[x/t0]): 3xA
                                         1-4   [[t11: [[A]    (note EA[x/toll =1A1),
        Ey3,z (t3xA. s (y zA[Xi] )): C            (y, zA[2/Y1)][z/             ]:   .




For the next two cases observe that [[A[X0d.C]1                     11./41[X*/K1].


        AXn.tA: VXnA                            AX*.M            : VX*11,417
        tVX'A W.B): A[Xn I Ai.B]                 litivx*IA1[[B]:[[,41[X* /[[B1].

For the A-rules we need on the right hand side defined operators:

        pA,B := AxAyBAXAzA' (B-+X) zxy
                  AttAAB.                            ,B := A ttAAB
                            UA(AXAyB.X),                              .uB(AxAyB .y).

Then

        p(tA78B): A A B 1-4 p(tFAI JsPB11): Pi A Bl,

etc.


PROPOSITION. The collapsing map preserves reductions: if D reduces to D',
then the collapse of D reduces to the collapse of D'.


11.5.7A. * Verify this.
11.5. Provably recursive functions of HA2                                 363

11.5.8. THEOREM. The provably total recursive functions of HA2 are rep-
resentable in A2.
PROOF. Let 7, be a deduction in HA2*, with conclusion,

(1)      I VxEIN 3yEINA(x, y),

or expanded

           Vx(x E IN       3y(y E lN A A(x, y)).

The collapsing map applied to 1, produces a term t such that
         t: [[Vx(x E IN    3y(y E IN A A(x, y))A       N     (N A 1[AD.

Then t* := AxN .po(tx) encodes the recursive function f implicit in the proof
of (1). This is seen as follows. If we specialize the deduction 7, to x = SnO
we obtain a deduction 1, which must end with applications of VE, +E along
the main branch:

                Vx(x E IN --+ 3y(y E lN A A(x, y)))         D[n]
                S'0 E IN      3y(y E ]1\1 A A(SnO, y))     SnO E IN
                              3y(y E IN A A(SnO, y))

which afteenormalization must end with an introduction:

                             Sm0 E IN A A(SmO, SnO)
                              3y(y E lN A A(SnO,y))
Applying AE to Dn" we find a deduction 7,+ of Sm0 E IN; the collapsing map
produces a term which must be equal to eft. By lemma 11.5.6, the deduction
1,+ normalizes to D[m], so t* fi normalizes to fit. Combining this with the
embedding of AM into A2, we have the desired result. Since A(SnO, SmO) is
provable in HA2, it is true in the standard model, so m = f (n).

REMARK. As observed in 11.6.4, the A2-representable functions are in fact
exactly the functions provably total recursive in HA2.

11.5.9. The provably total recursive functions of PA2
The provably total recursive functions of classical second-order arithmetic
PA2 are in fact also provably total in HA2; PA2 is just HA2 with classical
logic. This fact may be proved directly, but can also be obtained from the
characterization of the provably recursive functions of HA2. In outline, the
proof is as follows.
364                                               Chapter 11. Second-order logic

      In HA2 and PA2 we can conservatively extend the language and the
system by adding symbols for all the primitive recursive functions. Then
a provably total recursive function is given by a code number n such that
  VxAy(xT(fi, x, y) = 0), where xT is the characteristic function of Kleene's
T-predicate.
       The Gödel-Gentzen negative translation g (cf. 2.3) embeds PA2 into
HA2. Hence, if PA2 ]y(xT(fi, x, y) = 0), then HA2                     x, y) =
0) (using -,Vx,A 1-2xA).
      By a method due to Friedman [1978] and Dragalin [1979] we can show
that HA2 is closed under "Markov's rule" in the form: "if H ,ax(t(x,g') =
0) then H 3x(t(x,g)= 0)" (an exposition of this result is found in Troelstra
and van Dalen [1988, section 5.1]).
   As to (a), we use the result on the conservativity of the addition for sym-
bols for definable functions, applied to functions defined by primitive recur-
sion (4.4.12). Therefore we need to show that in HA2 we can define graph
predicates H(±, z) for each primitive recursive function h. The graph PRD
for the predecessor function prd is given by

        PRD(x,      := (x = 0 A z = 0) V 3y(x = Sy A z = y)

The crucial step in the construction of these H goes as follows. If h is ob-
tained from f and the number m (for notational simplicity we do not consider
additional numerical parameters):

        h(0) = m,    h(Sz)    f (z , h(z))

and we have already constructed F as the graph of f, we obtain the graph H
as

        H(z, u) := VX2(A(z, X) -4 X (z , u)),

where

        A(z, X2) := V z' < zaz' = O > (X z'v ++ y = m)] A
        [z'  0 -4 (X zit))   3v'z"(PRD(i, z") A X (z", y') A F (z" , y', v))]).

Then one proves by induction on z

          X2 A(z, X), and VzI < zA!u(A(z, X) --> X (z', u)).


11.6       Notes
For a general introduction to higher-order logic, see Leivant [1994].
11.6. Notes                                                                  365

11.6.1. Takeuti's conjecture. Closure under Cut for second-order classical
logic, known as "Takeuti's Conjecture" , was first proved by Tait [1966] by a
semantical argument, using classical metamathematical reasoning; this was
extended to higher-order logic by Takahashi [1967].
  Prawitz [1967] also gave a proof, extended to higher-order logic in Prawitz
[1968], along the same lines as Takahashi's proof. Takahashi [1970] deals with
type theory with extensionality.
   Prawitz [1970] uses Beth models to obtain closure under Cut for a cutfree
system of intuitionistic second-order logic (cf. 4.9.1).

11.6.2. Normalization and strong normalization for A2. Girard [1971] was
the first to prove a normalization theorem for a system of terms correspond-
ing to intuitionistic second-order logic in A, >, V, V2, 32, based on his idea of
 "reducibility candidates" as a kind of variable computability predicate, as a
method for extending the method of computability predicates of Tait [1967]
to higher-order systems. Martin-Löf [1971b] proves normalization (not strong
normalization) for HA2 with *, V, V2 in the form of deduction trees (not
terms), using Girard's idea. Prawitz [1971], also inspired by Girard [1971],
contains a proof of strong normalization, for intuitionistic first- and second-
order logic, covering also permutation conversions for V, A. (Prawitz [1981]
is a supplement, in particular for classical second-order logic.) Girard [1972]
also proves strong normalization. Girard [1971] is also the first place where
A2 is defined (called system "F" by Girard). Not much later, A2 was redis-
covered by Reynolds [1974]. (Strong) normalization for A2 and the associated
logical systems has been re-proved many times, always in essence by the same
method (for example, Osswald [1973], Tait [1975]). A smooth version is given
in the recent Girard et al. [1988]; but the proof presented here is based on
Matthes [1998], where the result has been generalized considerably.
  The method of computability predicates by Tait, with its extension by
Girard, has a semantical flavour; see, for example, Hyland and Ong [1993],
Altenkirch [1993] and Gallier [1995].
  As to the significance of cut elimination and normalization for second- and
higher-order logic, see Kreisel and Takeuti [1974], Girard [1976], Päppinghaus
[1983].


11.6.3. A2 as a type theory has been further strengthened, for example
in the "calculus of constructions" of Coquand and Huet [1988], but then the
formulas-as-types parallel cannot any longer be viewed as an isomorphism.
See for this aspect Geuvers [1993,1994]. For some information on extensions
of A2 see Barendregt [1992]. An elegant normalization proof for the calculus
of constructions is found in Geuvers and Nederhof [1991].
   The characterization of the provable recursive functions of HA2 as the
functions representable in A2 is due to Girard [1971,1972]; the proof given
366                                                Chapter II. Second-order logic

here follows Girard et al. [1988].
   Leivant [1990] gave a proof of this characterization for classical second-order
arithmetic, by another, more semantically inspired method.

11.6.4. A converse theorem. All A2-representable functions are in fact prov-
ably recursive in HA2. The idea for the proof is based on (1) arithmetizing
the syntax of A2, and (2) observing that the proof of strong normalization
for any given closed term t of A2 can in fact be carried out in HA2 itself, and
in particular that we can prove

        HA2      Vn3!mRed(rtitI, rfiC),

where Es 7 is the code of the A2-term s, and Red(t, t') expresses that the
term with code t reduces to the term with code t'. The proof is carried
out in Girard [1972]. For a proof with similar details, see, for example, the
formalization of normalization of Ni2 in Troelstra [1973, section 4.4].
Solutions to selected exercises
2.1.8B.
                                                           Aw


                        -,(A      B)u            A > 1,                                     Bw
                                                 ,                            B)u       A        B


                                                     _L
                                                                u
                                                           B)
                                                                        B)v


2.1.8E.


                                                                              I,
                                                      Aw                             Btu'
                               -,(A V B)'            AV B           -,(A V BY'       AVB
                                                                                 w
                  A -,B)u
                                  I              v
                                AV B
                                         AVBv


The other half of the equivalence is easier and holds even intuitionistically.




                                (A      B)           Aw
                         Av                           A
                                             v

                        ((A > B)        A) > A w

                                             367
368                                                                                       Solutions to exercises

2.1.8F. Write Px,y for ((X -- Y) > X)                               X.
                                                                         (A        B) > C u       A         B wn
                                                      C > Aw                              C
                                                                         A
                                           P A,B               (A        B) > Awn
                       A        Cv                            A
                                            C
             PC,A               (C>A)>Cw
                                C
                     (A > C) > C v
       (( . A> B)          C)         (A        C)     Cu
2.1.8G.
                                                                    A         Bu     Aw       A       CI'     Aw
                                                                               B                       C
                                                                                       BAC
                           (A -- (B A C))               Awi                         ABAC.--
                                                               A
               P A,B                                  (A       B)         Av
                                             A
      PA,C                           (A > C)          Av
                           A
                       P A,BAC w
2.1.8H. Proof by induction on the complexity of contexts. We do two cases.
  Let G[*]          F[*]        C.
                                                      Ill     Vi(A ). B)v
                                                            F[A] >. F[B]              F[A]w
                                F[B]         Cu                           FEB]
                                                      C           9,
                                             F[A] > C -
                                      (F[B] >. C) > F[A] > C u
                       V g(A > B) > (FEB] > C) >. F[A] >. C v
Let F[*] F--- VyF'[*], then
                                            V y g(A         B)u
                                     Ill        Vg(A -4 B)             VyP[A] v
                                       F' [A] ). FIB]                    F' [A]
                                                   F'[B]
                                            VyF' [B]
                                       VyF'[A]     VP[13] v
                                Vyg(A > B) >. V y F' [A]   V F'[B] u
2.2.2A. The prooftree is exhibited with at each node
                                    term: type I Fl/a(term) I FVi(term)
Types of subterms have been omitted.
Solutions to exercises                                                                           369

                                       v: Vx(Rx  1=6) Ivi
                                       vx: Rx             w: Rx w I x
                                                14 I v I x,
               u:3xRx I ul             vxw: R1 y I 21, wI x, Y
                         E(u, vxw): R'y I u, v iv
                    Au.E!,x(u, vxw): 3xRx > ley I y Y u
           Avu.E,x(u, vxw):Vx(Rx ley)       (3xRx .14) 01
2.3.8A. For the equivalence I I- Ag   A" let A* be obtained from A by inserting
    after each V, so Aq          Then prove by induction on the depth of A that
,(A*       Ag).
2.4.2D. Let us call the alternative system H', and let us introduce abbreviations
for the axioms mentioned: kA'B (cf. 1.3.6), WA'B (contraction), eA'B'C (permuta-
tion) and tA'B'C (neax-transitivity).
   We may prove the equivalence to 41i either directly, by giving a derivation of
the axiom schema s in H', or by paralleling the proof that Ali is equivalent to
g\Ti. For the latter strategy, we have to derive A A, and to show closure under
    The first is easy: take (A    A    A) >..A A as instance of the contraction
axiom, and detach the premise as an instance of k.
  To show closure under        suppose we have derived in H'
                                            Do       y1
                                        A        B       A


where Do, Di use assumptions from r, C. By the induction hypothesis there are
TY, DI deriving C   (A   B) and C A respectively from r. We combine these
in a new proof

                                         eC,A,B      C                      B
                           tA,C-+B,C             A       C         B
                            (C Y A) Y (C             C        B)                      CYA
                  W'C B                          C       C     B
                                  C      B
3.1.3C.


A    A     A,1                               B       B

          A    B           jj BAB B,1_
                                  B         A, B

                                                             13),B
                                                                       j_        j_
                                                                                  _L

           A    B                 1_          -,(A                          1_              _L
                  B),-(A     _L                              13)




                                                              Y B)
370                                                                     Solutions to exercises

3.1.3D.
                                                            B
                                                            B
                               A=B                           B
                                                            A, B
                            A, A   B                       B AB
                              A, A > B            B   3 x(A    B)
                            A,3x(A    B)         3xB   3 x(A    B)
                                A>3xB            3x(A    B)
                                                               Ax, Az    Az, VyAy
                  A, B      A, B
                                                                     Az, AzAlyAy
                 A B,BA                                     Ax
                                                              Ax
                                                                  Az ,3x(Ax AlyAy)
                      A>B,BA                               Ax    VyAy, 3 x(Ax >Vy Ay)
          Aq 3 , (A       B) V (B         A)
                                                             AxN y Ay , 3 x(Ax Aty Ay)
      (AB) V (B -- A), (A q3) V (BA)
                                                           3x(Ax--WyAy), 3 x(Ax Afy Ay)
               (A q3) V (B         A)
                                                                   3x(Ax >Vy Ay)
3.2.1A. For the proof of equivalence we have to appeal to closure under Cut for
Gli. The easy direction is
          If G1i I- F      V A then m-Gli I- I-' - A.
The proof is perfectly straightforward, by an induction on the depth of deductions
in Gli, provided we prove simultaneously
          If Gli E- I'      then m-Gli I- I'           .


In the induction step, it helps to distinguish cases according to whether A contains
zero, one or more formulas. The difficult direction is to show
          (*) If m-Gli I- I'       A then G1i F- I'             V A.
Using closure of Gli under Cut we first establish that
          Gli I- (A V B) VCAV (B V C),
          Gli I- AV (B V C)             (A V B) v C,
          Glil-AVBBV A.
This permits us to disregard bracketing and order of the formulas in forming I'
V A. Now the proof proceeds by induction on the depth of deductions in m-Gli.
We treat some crucial cases in the proof of (*).
  The last step in the proof in m-Gli was RA:
                              I' A,A I'          A,B
                                   I' A,AAB
Let D be V A. By induction hypothesis we have deductions of
          Glil-I'        DVA and GliF-PDVB\
Hence we have
          Gli I- I'      (D V A) A (D v B)
We now prove Gli I- (D VA) A (D V B)      D V (A AB), and apply Cut.
  Suppose now the last step in the proof in m-G1i was L:
Solutions to exercises                                                                                371

                                    r     A,A     I',B        A


By Ili we have in Gli a proof D' of F -AVD and a proof?'" of I', B                               D.
  We get the required conclusion from the following deduction:

                          D     D
                                                  AA BB                                 D"

       D'          r,D,A_3-D LW                              F, A, A        B       D             Cut
  F.DVA                              F,DVA,A>BD Cut                                     LV

                                           LC

3.3.3B. The equivalence between classical G-systems and classical N-systems for
subsets of the operators not containing I.
   (a) Applications of _Lc in Nc as on the left may be replaced by applications of
Peirce's rule as on the right:




Conversely, applications of P in Nc' as on the left may be replaced by applications
of _Lc as on the right:
                                                  ,Av        Au
                                                        _L
                          [A        B]U
                                                   A >B Bu
                                Apu
                                A    '                  A



      The equivalence between any two 1-equivalents is easily seen to hold by the
following deduction steps:
                               A  B, A
                                                                  A, B, A       1', A     A, A
   I', A    B      B, A         A  B, A
                                            Cut                   1', A     B      B, A

By repeated application of these deduction steps, we see that from F, A                      B          B
follows F       B, A and vice versa (A > A is short for D1>                                  A where
A EE Di,        Dri).
       We give a proof by induction on the depth of deductions in G2c. A is said
to be the goal-formula of the 1-equivalent F, A A     A of the sequent    A, A.
   Let us consider a crucial case. Suppose the G2c-deduction ends with

                                          r, A    B, A
372                                                                Solutions to exercises

By induction hypothesis we have a deduction D* in Nc' deriving B from AJ1.,
A, r, A B. Let A _==        , Dr,. Then
                                 -r (A B)           Biu
                                     A>B                    Av

                            (1 < i < n) [Di           B]u

                                                B
                                           A         B-
which shows that in Nc F, A > (A > B)        A    B. For our goal-formula we
have chosen the principal formula.
  Another case is when the deduction in G2c ends with

                                     r, A A B, A
By IH we have natural deductions of A from A > A and of B from A > B. We
construct a new deduction
                     Di > A AB       Diu       Di 21AB
                           AAB                            AAB
                            A        u
             (1 < i < n) [Di > A] -                   [Di > /3] (1 < i < n)
                                D1                        D2
                                A
                                         AAB
Here again we have used the principal formula as goal-formula. But in this case
the alternative, choosing a formula of the context as goal-formula, works at least
as well, if not better. Let C be a formula from the context.
                                                Av    Bw
                                AABC.               AAB

                                     [A > C.] v
                                       Vi

                                     [B        C] W
                                          D2


If on the other hand the context is empty, the case becomes completely straight-
forwaxd.
  If the final rule is an RV-
                                          A V B, A
- it is definitely more advantageous to work with a 1-equivalent where A V B is not
the goal-formula. If A is empty, the case is trivial. If A C, A', we construct a
deduction as follows:
Solutions to exercises                                                           373
                                                      AV
                                     AVBC A V B
                                             [A       v



Here D is a proof given by the induction hypothesis. The treatment of the case
where the final rule is RV is similar to the case of RA; and the case for R3 resembles
the case for RV. The treatment of the cases where the deduction ends with a left
rule is easy, since then the goal-formula is not affected.
3.3.4B. We show that in G2i* + Cut, that is G2i + Cut with sequents with
inhabited succedent, we can define N such that IN (D)I < kIDI, where k can be
taken to be 2 for the full system, and 1 for the system without I.
   Axioms in G2i* + Cut are either of the form r, A A or of the form r, J        A.
In the first case, the axiom is translated as a prooftree with a single node A, and
IN(D)1 = O < 21DI = 20 = 1. In the second case, the axiom is translated as
Hence IN(D)1 = 1 < 2.211 = 21 = 2. Now we consider the induction step. We
check three typical cases. Let di = IDil, d = IVl, V = N(Di), d = 1D1, =
for i 1, 2.
Case 1. D ends with RA, so D is as on the left, and is translated as on the right:
                            Vi              D2
                                 A     r         B         A B
                                                           AAB

Then d' = max(di, 4)+1 < max(k2d1, k2d2 ) +1 = k2max(cl1,d2) +1 < k2max(di,d2)+1
= k2d .
Case 2. D ends with            D and D' have respectively the forms
                                                                     7,1
                                       D2                  A   B     A
                           A                 C                 [B]




Now

            <    + d2 +1 < k2d1             (k2d2 1) + 1
(using cll. < k2d1, d2 < k2d2        1), hence
                                     ax
            < k(2d1      2d2) < k2.2m(d1,d2) == k2d .

Case 3. D ends with Cut; then D and D' have the forms

                                                 D2
                                                               [A]

                                     ri,r
374                                                                  Solutions to exercises

and

                   + d2 <k(2''       2d2)   k2.2max(d1, d2) = k2d.

3.5.7A. Let B          ((PQ)Q)P, A      BQ. We first show that A,QP          Q is actually
provable:

        A,P,(P(2)(2,(P(2)(2 P
           A,P,(PQ)Q B           P,(PQ)Q,Q Q
                       A, P,(PQ)Q Q            (PQ)Q,PP
                                   A,QP,(PQ)Q P
                                      A,QP B         QP,Q
                                              A,QP Q
Now suppose we have a proof of A,QP Q with the restricted version of the rule
    Then we can show that all possibilities for constructing a proof bottom-up
fail.
        If A was introduced by        A,QP Q reduces to QP B and QP,Q                   Q.
QP       B reduces to QP,(PQ)Q           P, which, if (PQ)P was introduced by
reduces to
     (aa) QP     PQ and QP,Q          P - breakdown or, if QP was introduced by L>,
to
     (ab) P,(PQ)Q P and (PQ)Q               Q, the latter in turn reduces to Q      Q and
      PQ - breakdown.
      If QP was introduced by      A,QP Q reduces to A,P Q and A Q,
hence to A    Q; this reduces to Q   Q and B, the latter sequent reduces to
(PQ)Q P which is underivable.
3.5.11A. Let us assume that D proves F- r,vxA        A; since r,L consist of
quantifier-free formulas, r, does not contain VxA. D contains instances ai of

            VxA, A[x/ti],
                VxA,

Let to, ... ,tn_1 be a complete list of the terms involved in these applications. (This
sequence is possibly empty!) Replace in the deduction D the occurrences of VxA by
A[x/to],... ,A[xltn_i]. The result is a correct proof in G3[mic], except that the
ai are transformed into instances of contraction. (Why is the proof correct?) By
closure under contraction of G3[mic], we can successively remove these instances
of contraction. An alternative proof simply uses induction on the depth of D.
   The extra result for G3c may be proved similarly, or by reducing it to the pre-
ceding result using the definition of 3xA as `9fx-,A, and the possibility of shifting
formulas from left to right and vice versa in G3c.
4.2.7A Assume G3i Vx(P V Rx) P V VxRx. By inversion, this is equivalent
to having a proof D' of G3i Vx(P V Rx)          P V VxRx. In order to show that
this is unprovable, we establish by induction something more general, namely that
Solutions to exercises                                                            375

there is no deduction D" for Vx(P V Rx), Rto,           , Rtn_i    P V VxRx. This
is proved by induction on the depth of D". Let us abbreviate the antecedent of
the conclusion of V" as Ari. If the last rule applied in 1," is RV, it would mean
that An     P or An VxRx ought to be provable; but neither of these is even
classically valid. If the last rule applied in D" is LV, it means that we have a proof
D" of depth less thanID"i showing An, PVRt7, PVVxRx, which by the inversion
lemma means that there is a proof of no greater depth of A,P,Rt7, P V VxRx.
This is impossible by the induction hypothesis.
4.2.7B The only somewhat awkward case is the test for the sequent BQ,QP Q
with B      ((PQ)Q)P. (We have dropped in the notation, since the sequent is
purely implicational.) We put A BQ. The application of the algorithm leads
in principle to many branches in the search tree, which all yield failure because of
repetition of sequents. However, after some experimenting with branches, we may
note the following.
     Suppose we concentrate in the search tree on the left premises of applications
of       and forget about the right premises. Moreover, we always apply in reverse
       whenever possible. Then

           A, r C          yields A, r, (PQ)Q       P,
           QP,F C          yields QP,r Q,
           (PQ)Q,r       C yields (PQ)Q,r,P         Q.

Hence, after repeatedly treating the initial sequent by L>, always followed when
applicable by R>., we always find a sequent r       A with A equal to P or Q, and
r as a set a subset of A,(PQ)Q,QP, P.
   Modulo contraction, applying          (followed by R* when applicable) always
again yields one of these sequents, so all branches produce repetitions. (Actually,
the reader may note that the sequent considered is not even classically provable,
by finding a suitable falsifying valuation.)
4.2.7D. Let Gli[mic]° be the system obtained from Gli[mic] by replacing            by
its context-free version (as in Gentzen's original system). Suppose a deduction D
in Gli[micr establisheshn B, A         B,r A; then we readily see by induction on
n that there is also a deduction TY establishing 1-n B,       A, and D' is restricted
if D is restricted. This suffices to prove the property by induction on the depth of
proofs.
4.2.7F. Let D be a deduction in G3i with IV <n of r              C. D cannot be an
axiom. We apply induction on the depth of D. If the final rule in D was a right
rule, the premises are of the form I'    C' and the induction hypothesis applies. If
the last rule applied in 1, is an application of      (there is no other possibility),
the final step is of the form


                             C

where r      V, A,    Bi, and the result follows.
376                                                            Solutions to exercises

4.3.6A. We discuss the last formula of the exercise, abbreviated by not writing
many implication arrows to:

               (PR)R > (QR)R 4 (PQ)R          R.

Let us write A for (PR)R      (Q R)R. We shall always tacitly reduce any problem by
use of the invertible rule R>. As a shortcut we also observe that (for all B, C, D, r)
DB , B, l'   C is derivable iff B, r  c is derivable. Our initial problem is replaced
by (R-0:
               A, (PQ)R 4 R.
      First treat in (b) (PQ)R. This reduces with L--> to
           A, QR, P 4 PQ and R > R (Axiom)
We then apply L to A and obtain from the first problem:
           R    (QR)R, PR,QR, P 4 Q and (QR)R,QR 4 R.
We continue with the first and apply LO>:

           R(QR)R, P, R,QR 4 Q.
Again with LC1

           R,(QR)R, P,QR       Q.

This is equivalent to P, R 4 Q which is obviously underivable.
      Now treat in (b) first (PQ)R by L:
           R).(QR)R,QR, PR, P 4 Q and R>P(QR)R, R,PR                  R (Axiom).

Apply 1,0 to the first of these formulas, then

           R. (QR)R,QR, P, R 4. Q.
Again with 1,0

           (QR)R,QR, P, R 4. Q.

which is equivalent to P, R =. which is underivable.
  Hence the formula to be tested is underivable.
5.1.13C. The proofs of properties (i) and (ii) are more or less routine and left to
the reader; we concentrate on the proof of (iii). Let us write F-2, for Fi. Assume
we have

                r, u: (A*B)>C1 4. t: D.
Solutions to exercises                                                                 377

Let the final step in the deduction be an application of               with (Aq3)W as
principal formula. Then there are premises:

           hn r, u: (Ag3)W           so: AB,
                r, u: (A>.13)C,w:C          to: D.

By the inversion property (ii), the first line yields

                r, u: (A ,F3)>C , yo: A      si: B,

where so == Ay(,I.si. By the Ill applied to this result, we find

                r, z: BC, y: A, yo: A       s2: B,

where

           s 2 =0 si[ul AxA-4B.z(xy)].

From now on we write a for the substitution [ulAxA'B.z(xy)]. Apply the contrac-
tion property (i):

(*)             r, z: B)C, y: A      82 NO /Y1 B.

Put

           83     82 [Yo h], 84   81 [WY]

and note that 82[Yo/Y] =0 si[YolY], i.e., 83              840. Also, applying the 1H to the
other premise,
(**)       F-n r, z:       1, y: A, w:C     t1: D,

where ti        too'. Combining (*) and (**) we find

                  r, z: B>C, y: A       ti[w 1 zs3]: D.

Since, with an appeal to the substitution lemma 1.2.4,

           ti[wl zso] =,3 tocr[wl zso] Er- to[w/z84]cr,

we can take in this case e        to[whs4]. The other cases of the induction step are
easier.
6.8.7C. The proof of Cl and C2 of lemma 6.8.3 for the extra case is easy; only C3
asks some extra attention. Assume

           (Vti -<1t)CompAAB(e).

We have to show CompAAB(t), that is to say CompA(pot), CompB(pit); for this
it suffices to show

           (Vt"-<1 pot)CompA (t"),      (Vi" ipit)CompB (e).
378                                                              Solutions to exercises

Case 1. The term t is not of the form ptoti. Then if t" -<i pot, t" pjt', t' -<i t,
and by hypothesis C0mpAAB(t'), hence CompA(pot'), i.e., CompA(t"); similarly
CompB(t") for all t" -<i p1t.
Case 2. If t is of the form pt0t1, and t" -.< pet, t" is either of the form po(ptti)
with t'0 -< to, or of the form po(ptot'1) with t' -< t1, or is equal to to. In the first
subcase, since by assumption CompAAB(ptt1), also CompA(po(ptti)). In the
second subcase, CompAAB(ptot), hence CompA(po(ptotÇ)). In the third subcase,
we conclude that CompA (to), since as before we have COmPA (PO (ptti)) for all
t'0 -< to, and since C2 holds for A, it also follows that CompA(t). etc. In the same
way we establish in this case (Vt"-<lplt)CompB(t").
  But note that a better result may be obtained by strengthening the property
defining COmPAAB, see 8.3.1.
Bibliography

   ABRAMSKY, D. M. GABBAY, AND T. S. E. MAIBAUM
 [1992]eds., Handbook of Logic in Computer Science, Vol. 1. Background: Math-
           ematical Structures, Clarendon Press, Oxford. Editor of the volume
           D. M. Gabbay.
P. H. G. ACZEL
  [19681 Saturated intuitionistic theories, in Contributions to Mathematical Logic,
          H. A. Schmidt, K. Schiitte, and H.-J. Thiele, eds., Studies in Logic and
          the Foundations of Mathematics, North-Holland Publ. Co., Amsterdam,
           1-11.
   ALTENKIRCH
 [1993]    Constructions, Inductive Types and Strong Normalization, PhD thesis,
           The University of Edinburgh, Department of Computer Science, Edin-
           burgh.
Y. ANDOU
 [1995]    A normalization-procedure for the first-order natural deduction with full
           logical symbols, Tsukuba Journal of Mathematics, 19, 153-162.
J.-M. ANDREOLI
  [1992] Logic programming with focusing proofs in linear logic, Journal of Logic
           and Computation, 2, 297-347.
J.-M. ANDREOLI AND R. PARESCHI
  [1991]   Linear objects: logical processes with built-in inheritance, New Genera-
           tign Computing, 9, 445-473.
K. R. APT
  [1990]   Logic programming, in Handbook of Theoretical Computer Science, Vol-
           ume B. Formal Methods and Semantics, J. v. Leeuwen, ed., Elsevier
           Publ. Co., 493-574.
A. AVRON
  [1991]   Hypersequents, logical consequence and intermediate logic for concur-
           rency, Annals of Mathematics and Artificial Intelligence, 4, 225-248.
  [1996]   The method of hypersequents in the proof theory of propositional non-
           classical logics, in Logic: from Foundations to Applications. European
           Logic Colloquium, Clarendon Press, Oxford, 1-32.
  [1998]   Two types of multiple-conclusion systems, Logic Journal of the IGPL
           Interest Group in Pure and Applied Logics, 6, 695-717.
                                        379
380                                                                      Bibliography

F. BAADER AND J. SIEKMANN
  [1994]   Unification theory, in Gabbay et al. [1994], 41-125.
A. A. BABAEV AND S. V. SOLOVJOV
  [1979]   A coherence theorem for canonical maps in CCC's (Russian, with En-
           glish summary), Zapiski Nauchnykh Seminarov Lenin gradskogo Otde-
           leniya Ordena Lenina Matematicheskogo Instituta imeni V. A. Steklova
           Akademii Nauk SSSR (LOMI), 88, 3-29. Translation in Journal of So-
           viet Mathematics, 20 (1982), 2263-2279.
  [1990]   On conditions of full coherence in biclosed categories: a new applica-
           tion of proof theory, in COLOG-88, P. Martin-Löf and G. E. Mints,
           eds., Lecture Notes in Computer Science 417, Springer-Verlag, Berlin,
           Heidelberg, New York, 3-8.
H. BACHMANN
  [1955]    Transfinite Zahlen, Springer-Verlag, Berlin, Heidelberg, New York. 2nd,
           revised edition 1967.
H. P. BARENDREGT
  [1984]   The Lambda Calculus, North-Holland Publ. Co., Amsterdam. 2nd edi-
           tion.
  [1992]   Lambda calculi with types, in Handbook of Logic in Computer Science,
            Vol. 2, S. Abramsky, D. M. Gabbay, and T. S. E. Maibaum, eds., Oxford
           University Press, Oxford, 118-309.
      J. BEESON
  [1985]   Foundations of Constructive Mathematics, Springer-Verlag, Berlin, Hei-
           delberg, New York.
      D. BELNAP
  [1982]   Display logic, Journal of Philosophical Logic, 11, 375-417.
  [1990]   Linear logic displayed, The Notre Dame Journal of Formal Logic, 31,
           14-25.
N. BENTON, G. BIERMAN, J. M. E. HYLAND, AND V. C. V. DE PAIVA
 [1992] Term assignment for intuitionistic linear logic, Tech. Rep. 262, Computer
        Laboratory, University of Cambridge.
P. BERNAYS
  [1970]   On the original Gentzen consistency proof for number theory, in Myhill
           et al. [1970], 409-417.
E. W. BETH
 [1953] On Padoa's method in the theory of definition, Indagationes Mathemat-
           icae, 15, 330-339.
  [1955]   Semantic entailment and formal derivability, Mededelingen der Konink-
           lijke Nederlandse Akademie van Wetenschappen (Amsterdam), Afdeling
           Letterkunde. Nieuwe Reeks, 18, 309-342.
  [1956]   Semantic construction of intuitionistic logic, Mededelingen der Konink-
           lijke Nederlandse Akademie van Wetenschappen (Amsterdam), Afdeling
           Letterkunde. Nieuwe Reeks, 19, 357-388.
Bibliography                                                                     381

  [1959]   The Foundations of Mathematics, Studies in Logic and the Foundations
           of Mathematics, North-Holland Publ. Co., Amsterdam. 2nd edition,
           1965.
  [1962a] Formal Methods, D. Reidel Publ. Co., Dordrecht, Netherlands.
  [1962b] Umformung einer abgeschlossenen deduktiven oder semantischen Tafel
          in eine natiirliche Ableitung auf Grund der derivativen bzw. klassischen
          Implikationslogik, in Logik und Logikkalkiil, M. Käsbauer and F. von
          Kutschera, eds., Verlag Karl Alber, Freiburg i. Br./Mi.inchen, Germany,
           49-55.
M. N. BEZHANISHVILI
  [1987]   Notes on Wajsberg's proof of the separation theorem, in Initiatives in
           Logic, J. Srzednicki, ed., Martinus Nijhoff, Dordrecht, Netherlands, etc.,
           116-128.
W. BIBEL AND E. EDER
  [1993]   Methods and calculi for deduction, in Gabbay et al. 0994 68-182.
T. S. BLYTH
 [1986] Categories, Longman, London.

B. R. BoRi616
 [1985] On sequence-conclusion natural deduction systems, Journal of Philo-
           sophical Logic, 14, 359-377.
    BORISAVLJEVI6
  [1999] A cut-elimination proof in intuitionistic predicate logic, Annals of Pure
           and Applied Logic, 99, 105-136.
    G. DE BRUIJN
  [1972]   Lambda-calculus notation with nameless dummies, a tool for automatic
           formula manipulation, Indagationes Mathematicae, 34, 381-392.
W. BUCHHOLZ
  [1991]   Notation systems for infinitaxy derivations, Archive for Mathematical
           Logic, 30, 277-296.
W. BUCHHOLZ, S. FEFERMAN, W. POHLERS, AND W. SIEG
 [1981] Iterated Inductive Definitions and Subsystems of Analysis: Recent Proof-
        Theoretical Studies, Lecture Notes in Mathematics 897, Springer-Verlag,
        Berlin, Heidelberg, New York.
W. BUCHHOLZ AND S. S. WAINER
  [1987]   Provably computable functions and the fast growing hierarchy, in Logic
           and Combinatorics. Proceedings of a Summer Research Conference held
           August 4-10, 1985, S. G. Simpson, ed., Contemporary Mathematics 65,
           American Mathematical Society, Providence, RI, 179-198.
R. A. BULL AND K. SEGERBERG
  [1984]   Basic modal logic, in Handbook of Philosophical logic II. Extensions of
           Classical Logic, D. Gabbay and F. Guenthner, eds., Reidel, Dordrecht,
           Netherlands, 1-88.
382                                                                     Bibliography

      Buss AND G. E. MINTS
 [1999]     The complexity of the disjunction and existential properties in intuition-
            istic logic, Annals of Pure and Applied Logic, 99, 93-104.
D. H. C.
 [1994]     From Logic to Logic Programming, MIT Press, Cambridge, MA.
C. CELLUCCI
 [1992]     Existential instantiation and normalization in sequent natural deduc-
            tion, Annals of Pure and Applied Logic, 58, 111-148.
C.-L. CHANG AND R. C.-T. LEE
 [1973] Symbolic Logic and Mechanical Theorem Proving, Academic Press, New
            York.
A. CHURCH
 [1956]     Introduction to Mathematical Logic. Part I, Princeton University Press,
            Princeton, NJ. 2nd edition.
      COQUAND AND G. HUET
 [1988]     The calculus of constructions, Information and Computation, 76, 95
            120.
W. CRAIG
 [1957a] Linear reasoning. A new form of the HerbrandGentzen theorem, The
            Journal of Symbolic Logic, 22, 250-268.
 [1957b] Three uses of the HerbrandGentzen theorem in relating model theory
        and proof theory, The Journal of Symbolic Logic, 22, 269-285.
P .-L . CURIEN
 [1985]     Typed categorical combinatory logic, in Automata, Languages and Pro-
            gramming (ICALP 85), W. Brauer, ed., Lecture Notes in Computer
            Science 194, Springer-Verlag, Berlin, Heidelberg, New York, 130-139.
 [1986]     Categorical Combinators, Sequential Algorithms and Functional Pro-
            gramming, Pitman, London, and John Wiley and Sons, New York.
H. B. CURRY
 [1934] Functionality in combinatory logic, Proceedings of the National Academy
         of the U.S.A., 20, 584-590.
 [1942]     The combinatory foundations of mathematical logic, The Journal of
            Symbolic Logic, 7, 49-64.
 [1950]  A Theory of Formal Deductibility, Notre Dame Mathematical Lectures
         6, The University of Notre Dame Press, Notre Dame, IN.
 [1952a] The elimination theorem when modality is present, The Journal of Sym-
            bolic Logic, 17, 249-265.
 [1952b] The permutability of rules in the classical inferential calculus, The Jour-
            ntil of Symbolic Logic, 17, 245-248.
 [1963]     Foundations of Mathematical Logic, McGraw-Hill, New York. Also pub-
            lished by Dover, New York 1977.
H. B. CURRY AND R. FEYS
 [1958]     Combinatory Logic I, Studies in Logic and the Foundations of Mathe-
            matics, North-Holland Publ. Co., Amsterdam. 2nd edition 1968.
Bibliography                                                                      383

D. VAN DALEN
  [1994]   Logic and Structure, Springer-Verlag, Berlin, Heidelberg, New York. 3rd
           edition.
D. VAN DALEN AND R. STATMAN
  [1979]   Equality in the presence of apartness, in Essays on Mathematical Logic.
           Proceedings of the Fourth Scandinavian Logic Symposium and of the 1st
           SovietFinnish Logic Conference, J. Hintikka, I. Niiniluoto, and E. Saari-
           nen, eds., Reidel, Dordrecht, Netherlands, 95-116.
V. DANOS
  [1990]   La logique linéaire appliquée à l'étude de divers processus de normali-
           sation (principalernent du ).-calcul), PhD thesis, Université Paris VII,
           Juin.
V. DANOS, J.-B. JOINET, AND H. A. J. M. SCHELLINX
 [1995] On the linear decoration of intuitionistic derivations, Archive for Math-
        ematical Logic, 33, 387-412. Slightly revised and condensed version of a
           technical report from 1993 with the same title.
  [1997]   A new deconstructive logic: classical logic, The Journal of Symbolic
           Logic, 62, 755-807.
  [1999]   Computational isomorphisms in classical logic. To appear in Theoretical
           Computer Science.
V. DANOS AND L. REGNIER
  [1989]   The structure of multiplicatives, Archive for Mathematical Logic, 28,
           181-203.
    DILLER
  [1970] Zur Berechenbarkeit primitiv-rekursiver Funktionale endlicher Typen,
           in Contributions to Mathematical Logic, H. A. Schmidt, K. Schiitte, and
           H.-J. Thiele, eds., North-Holland Publ. Co., Amsterdam, 109-120.
    DO§EN
  [1987]   A note on Gentzen's decision procedure for intuitionistic propositional
           logic, Zeitschrift far Mathematische Logik und Grundlagen der Mathe-
           matik, 33, 453-456.
  [1993]   A historical introduction to substructural logics, in Substructural Logics,
           K. Difisen and P. Schroeder-Heister, eds., Clarendon Press, Oxford, 1-30.
A. G. DRAGALIN
  [1979]   Mathematical Intuitionism. Introduction to Proof Theory (Russian),
           Nauka, Moscow. Translated as Volume 67 in the series Translations of
           Mathematical Monographs, under the title Mathematical Intuitionism.
           American Mathematical Society, Providence, RI, 1988.
M. A. E. DUMMETT
 [1959] A propositional calculus with denumerable matrix, The Journal of Sym-
          bolic Logic, 24, 97-106.
R. DYCKHOFF
  [1992]   Contraction-free sequent calculi for intuitionistic logic, The Journal of
           Symbolic Logic, 57, 795-807.
384                                                                      Bibliography

  [1996]   Dragalin's proof of cut-admissibility for the intuitionistic sequent cal-
           culi G3i and G3r, Tech. Rep. CS-96-9, Computer Science Division,
           St Andrews University.
R. DYCKHOFF AND S. NEGRI
  [1999]   Admissibility of structural rules for contraction-free systems of intuition-
           istic logic, The Journal of Symbolic Logic, 64, to appear.
      DYCKHOFF AND L. PINTO
  [1999]   Permutability of proofs in intuitionistic sequent calculi, Theoretical
           Computer Science, 212, 141-155.
N. EISINGER AND H. J. OHLBACH
  [1993]   Deduction systems based on resolution, in Gabbay et al. 0994 184-271.
      FEFERMAN
  [1968]   Lectures on proof theory, in Proceedings of the Summer School in Logic,
           M. H. Löb, ed., Lecture Notes in Mathematics 70, Springer-Verlag,
           Berlin, Heidelberg, New York, 1-107.
W. FELSCHER
  [1975]   Kombinatorische Konstruktionen mit Beweisen und Schnittelimination,
           in ISILC Proof Theory Syrnposin, Kiel 1974, J. Diller and G. H. Miiller,
           eds., Springer-Verlag, Berlin, Heidelberg, New York, 119-151.
  [1976]   On interpolation when function symbols are present, Archiv für Mathe-
           matische Logik und Grundlagenforschung, 17, 145-157.
J. E. FENSTAD
  [1971]   ed., Proceedings of the Second Scandinavian Logic Symposium, North-
           Holland Publ. Co., Amsterdam.
M. D. FITTING
  [1969]   Intuitionistic Logic, Model Theory and Forcing, North-Holland Publ.
           Co., Amsterdam.
  [1983]   Proof Methods for Modal and Intuitionistic Logics, Reidel, Dordrecht,
           Netherlands.
  [1988]   First-order modal tableaux, Journal of Automated Reasoning, 4, 191
           213.
  [1993]   Basic modal logic, in Gabbay et al. [1993], 365-448.
  [1996]   First-Order Logic and Automated Theorem Proving, Springer-Verlag,
           Berlin, Heidelberg, New York. 2nd edition.
R. C. FLAGG AND H. M. FRIEDMAN
  [1986]   Epistemic and intuitionistic formal systems, Annals of Pure and Applied
           Logic, 32, 53-60.
G. FREGE
 [1879] Begriffschrift, eine der arithmetischen nachgebildete Formelsprache des
           reinen Denkens, Louis Nebert, Halle. Reprinted in: Ignacio Angelelli
           (ed.) Begriffschrift und andere Aufsiitze, Olms, Hildesheim 1964. Trans-
           lation in van Heijenoort [1967], 5-82.
Bibliography                                                                    385

H. M. FRIEDMAN
  [1978]   Classically and intuitionistically provable functions, in Higher Set The-
           ory, G. H. Willer and D. S. Scott, eds., Lecture Notes in Mathematics,
           Springer-Verlag, Berlin, Heidelberg, New York, 21-27.
H. M. FRIEDMAN AND A. SCEDROV
  [1986]   Intuitionistically provable recursive well-orderings, Annals of Pure and
           Applied Logic, 30, 165-171.
H. M. FRIEDMAN AND M. SHEARD
  [1995]   Elementary descent recursion and proof theory, Annals of Pure and Ap-
           plied Logic, 71, 1-45.
T. FUJIWARA
  [1978]   A generalization of the LyndonKeisler theorem on homomorphism and
           its application to interpolation theorem, Journal of the Mathematical
           Society of Japan, 30, 278-302.
D. M. GABBAY, C. J. HOGGER, AND J. A. ROBINSON
 [1993] eds., Handbook of Logic in Artificial Intelligence and Logic Programming.
        Vol. 1, Logical Foundations, Clarendon Press, Oxford.
 [1994] eds., Handbook of Logic in Artificial Intelligence and Logic Programming.
        Vol. 2, Deduction Methodologies, Clarendon Press, Oxford.
J. GALLIER
  [1991]   What's so special about Kruskal's theorem and the ordinal -yo? A survey
           of some results in proof theory, Annals of Pure and Applied Logic, 53,
           199-260.
  [1993]   Constructive Logics. Part I: a tutorial on proof systems and typed A-
           calculi, Theoretical Computer Science, 110, 249-339.
  [1995]   Proving properties of typed lambda-terms using realizability, covers and
           sheaves, Theoretical Computer Science, 142, 299-368.
R. O. GANDY
 [1980] An early proof of normalization by A. M. Turing, in Seldin and Hindley
        [1980], 453-455.
G. GENTZEN
  [1933a] Über das Verhältnis zwischen intuitionistischer und klassischer Logik.
          Originally to appear in the Mathematische Annalen, reached the stage
         of galley proofs but was withdrawn. It was finally published in Archiv
         far Mathematische Logik und Grundlagenforschung, 16 (1974), 119-132.
         Translation in Gentzen [1969], 53-67.
  [1933b] Ober die Existenz unabhängiger Axiomensysteme zu unendlichen Satz-
         systemen, Mathematische Annalen, 107, 329-350.
  [1935] Untersuchungen iiber das logische Schliessen I, II, Mathematische Zeit-
          schrift, 39, 176-210, 405-431. Translation in Gentzen [1969], 68-131.
  [1936] Die Widerspruchsfreiheit der reinen Zahlentheorie, Mathematische An-
          nalen, 112, 493-565. Translation in Gentzen [1969], 132-170.
  [1938] Neue Fassung des Widerspruchsfreiheitsbeweises fiir die reine Zahlen-
         theorie, Forschungen zur Logik und zur Grundlegung der exakten Wis-
          senschaften. Neue Reihe, 4, 19-44. Translation in Gentzen [1969], 252
           286.
386                                                                    Bibliography

  [1943]   Beweisbaxkeit und Unbeweisbarkeit von Anfangsfällen der transfiniten
           Induktion in der reinen Zahlentheorie, Mathematische Annalen, 119,
           140-161. Translation in Gentzen [1969], 287-311.
  [1969]   The Collected Papers of Gerhard Gentzen, North-Holland Publ. Co.,
           Amsterdam. English translation of Gentzen's papers, edited and intro-
           duced by M. E. Szabo.
H. GEUVERS
  [1993]   Logics and Type Systems, PhD thesis, Katholieke Universiteit Nijmegen.
  [1994]   Conservativity between logics and typed A-calculi, in Types for Proofs
           and Programs, H. Barendregt and T. Nipkow, eds., Lecture Notes in
           Computer Science 806, Springer-Verlag, Berlin, Heidelberg, New York,
           79-107.
H. GEUVERS AND M. J. NEDERHOF
  [1991]   A modular proof of strong normalization for the calculus of construc-
           tions, Journal of Functional Programming, 1, 155-189.
J .-Y . GIRARD
  [1971]   Une extension de l'interprétation de Gödel à l'analyse, et son application
             l'élimination des coupures dans l'analyse et la théorie des types, in
          Fenstad [1971], 63-92.
  [1972] Interprétation fonctionelle et élimination des coupures de l'arithmétique
          d'ordre supérieur, PhD thesis, Université Paris VII.
  [1976] Three-valued logic and cut elimination: the actual meaning of Takeuti's
          conjecture, Dissertationes Mathematicae, 136.
  [1987a] Linear logic, Theoretical Computer Science, 50, 1-102.
  [198713] Proof Theory and Logical Complexity, Bibliopolis, Napoli.
  [1991]   Quantifiers in linear logic II, in Nuovi problemi della logica e della
           filosofia della scienza, Volume II, G. Corsi and G. Sambin, eds., CLUEB,
           Bologna (Italy). Proceedings of the conference with the same name,
           Viaxeggio, 8-13 gennaio 1990.
  [1993]   On the unity of logic, Annals of Pure and Applied Logic, 59, 201-217.
  [1996]   Proof-nets: the paxallel syntax for proof theory, in Logic and Algebra.
           Papers from the International Conference in memory of Roberto Magari,
           held in Pontignano, April 26-30, 1994, A. Ursini and P. Aglian6, eds.,
           Lecture Notes in Pure and Applied Mathematics 180, Marcel Dekker
           Inc., New York, 97-124.
J.-Y. GIRARD, Y. LAFONT, AND P. TAYLOR
  [1988]   Proofs and Types, Cambridge Tracts in Theoretical Computer Science
           7, Cambridge University Press, Cambridge, UK.
V. GLIVENKO
  [1929]   Sur quelques points de la logique de M. Brouwer, Académie Royale de
           Belgi que. Bulletins de la Classe des Sciences, série 5, 15, 183-188.
K. GÖDEL
  [1933a] Eine Interpretation des intuitionistischen Aussagenkalküls, Ergebnisse
          eines mathematischen Kolloquiums, 4, 39-40. Also, with translation, in
           Gödel [1986], 300-303.
Bibliography                                                                      387

  [1933b] Zur intuitionistischen Arithmetik und Zahlentheorie, Ergebnisse eines
         mathernatischen Kolloquiurns, 4, 34-38. Also, with translation, in Gödel
           [1986], pp. 286-295.
  [1958]   Über eine bisher noch nicht beniitzte Erweiterung des finiten Stand-
           punktes, Dialectica, 12, 280-287. Also, with translation, in Gödel [1990],
           240-251.
  [1986]   Collected Works, Volume I, Oxford University Press, Oxford.
  [1990]   Collected Works, Volume II, Oxford University Press, Oxford.
N. D. GOODMAN
  [1984]   Epistemic arithmetic is a conservative extension of intuitionistic arith-
           metic, The Journal of Symbolic Logic, 192-203.
L. GORDEEV
  [1987]   On Cut elimination in the presence of Peirce rule, Archiv fiir Mathema-
           tische Logik und Grundlagenforschung, 26, 147-164.
  [1988]   Proof-theoretic analysis: weak systems of functions and classes, Annals
           of Pure and Applied Logic, 38, 1-121.
 R. P. GORÉ
  [1992] Cut-free sequent and tableau systems for propositional normal modal
         logics, Tech. Rep. 257, Computer Laboratory, University of Cambridge.
 C. A. GRABMAYER
  [1999]    Cut-elimination in the irnplicative fragment ->G3mi of an intuitionis-
           tic G3-Gentzen system and its Computational Meaning, Master's thesis,
           Institute for Logic, Language and Computation, University of Amster-
           dam.
 T. HARDIN
  [1989]   Confluence results for the pure strong categorical logic, Theoretical Com-
           puter Science, 65, 291-342.
 J. A. HARLAND
  [1994]   A proof-theoretic analysis of goal-directed provability, Journal of Logic
           and Cornputation, 4, 69-88.
 L. A. HARRINGTON AND J. B. PARIS
  [1977]   A mathematical incompleteness in Peano axithmetic, in Handbook of
           Mathernatical Logic, J. Barwise, ed., North-Holland Publ. Co., Amster-
           dam, 1133-1142.
 R. HARROP
  [1956]   On disjunctions and existential statements in intuitionistic systems of
           logic, Mathematische Annalen, 132, 347-361.
  [1960]   Concerning formulas of the type A -> 13 V C, A -> (Ex)B(x) in intu-
           itionistic formal systems, The Journal of Symbolic Logic, 25, 27-32.
 J. VAN HEIJENOORT
  [1967]   ed., From Frege to Gödel. A Source Book in Mathematical Logic 1879-
           1931, Harvaxd University Press, Cambridge, MA. Reprinted 1970.
388                                                                    Bibliography

L. HEINDORF
  [1994]   Elementare Beweistheorie, BI-Wissenschaftsverlag, Mannheim, Ger-
           many.
H. HERBELIN
  [1995]   A A-calculus structure isomorphic to Gentzen-style sequent calculus
           structure, in Computer Science Logic. 8th Workshop, CSL'94. Kaz-
           imierz, Poland, September 1994, L. Pacholski and J. Tiuryn, eds., Lec-
           ture Notes in Computer Science 933, Springer-Verlag, Berlin, Heidel-
           berg, New York, 61-75.
J. HERBRAND
  [1928]   Sur la théorie de la démonstration, Académie des Sciences de Paris.
           Comptes Rendus Hebdomadaires des Séances, 186, 1274-1276. Also in
           Herbrand [1968].
  [1930]   Recherches sur la théorie de la démonstration, Société des Sciences et des
           Leaves de Varsovie. Comptes Rendus des Sciences. Classe III: Sciences
           Mathématiques et Physiques, 33. Also in Herbrand [1968].
  [1968]   Écrits Logiques, Presses Universitaires de France, Paris. Translated as
           Logical Writings, Harvard University Press, Cambridge., MA, 1971.
P. HERTZ
  [1929]   tier Axiomensysteme für beliebige Satzsysteme, Mathematische An-
           nalen, 101, 457-514.
A. HEYTING
  [1930a] Die formalen Regeln der intuitionistischen Logik, Sitzungsberichte der
         Preussischen Akademie von Wissenschaften. Physikalisch-mathemat-
         ische Klasse, 42-56.
  [1930b] Die formalen Regeln der intuitionistischen Mathematik II, Sitzungs-
          berichte der Preussischen Akademie von Wissenschaften. Physikalisch-
         mathematische Klasse, 57-71.
D. HILBERT
  [1926]   Über das Unendliche, Mathematische Annalen, 95, 161-190.
  [1928]   Die Grundlagen der Mathematik, Abhandlungen aus dem mathematisch-
           en Seminar der Hamburgischen Universität, 6, 65-85.
D. HILBERT AND W. ACKERMANN
 [1928]    Grundziige der theoretischen Logik, Springer-Verlag, Berlin, Heidelberg,
           New York.
D. HILBERT AND P. BERNAYS
 [1934]    Grundlagen der Mathematik, Bd. I, Springer-Verlag, Berlin, Heidelberg,
           New York. 2nd edition 1968.
 [1939]    Grundlagen der Mathematik, Bd. II, Springer-Verlag, Berlin, Heidel-
           berg, New York. 2nd edition 1970.
J. R. HINDLEY
  [1993] BCK- and BCI-logics, condensed detachment and the 2-property, Notre
         Dame Journal of Formal Logic, 34, 231-250.
 [1997]    Basic Simple Type Theory, Cambridge University Press, Cambridge,
           UK.
Bibliography                                                                    389

   R. HINDLEY AND D. MEREDITH
  [1990]   Principal type-schemes and condensed detachment, The Journal of Sym-
           bolic Logic, 55, 90-105.
    J. J. HINTIKKA
  [1955]   Form and content in quantification theory. Two papers on symbolic logic,
           Acta Philosophica Fennica, 8, 7-55.
S. HIROKAWA
  [1992] Balanced formulas, BCK-minimal formulas and their proofs, in Logical
           Foundations of Computer Science (LFCS'92), A. Nerode and M. Tait-
           slin, eds., Lecture Notes in Computer Science 620, Springer-Verlag,
           Berlin, Heidelberg, New York, 198-208.
J. HODAS AND D. MILLER
  [1994]   Logic programming in a fragment of intuitionistic linear logic, Informa-
           tion and Computation, 110, 327-365.
W. HODGES
  [1993]   Logical features of Horn clauses, in Gabbay et al. [1994 449-518.
W. A. HOWARD
  [1970]   Assignment of ordinals to terms for primitive recursive functionals of
           finite type, in Myhill et al. [1970], 443-458.
  [1980]   The formulae-as-types notion of construction, in Seldin and Hindley
           [1980], 480-490. Circulated as preprint since 1969.
J. HUDELMAIER
  [1989]   Bounds for Cut Elimination in Intuitionistic Propositional Logic, PhD
           thesis, Eberhaxd-Karls Universität, Tiibingen, Germany.
  [1992]   Bounds for cut elimination in intuitionistic propositional logic, Archive
           for Mathematical Logic, 31, 331-354.
  [1993]   An 0(n log n)-space decision procedure for intuitionistic propositional
           logic, Journal of Logic and Computation, 3, 63-75.
  [1998]   Semantische Sequenzenkalkiile, habilitationsschrift, Fakultät fiir Infor-
           matik der Eberhard-Kaxls-tniversität Tiibingen, Germany.
G. E. HUGHES AND M. J. CRESSWELL
  [1968]   An Introduction to Modal Logic, Methuen, London.
J. M. E. HYLAND AND C. L. ONG
  [1993]   Modified realizability semantics and strong normalization proofs, in
           Typed Lambda Calculi and Applications, M. Bezem and J. Groote, eds.,
           Springer Lecture Notes in Computer Science 664, 179-194.
G. JÄGER AND R. F. STÄRK
 [1994] A proof-theoretic framework for logic programming. Draft for a chapter
        in the Handbook of Proof Theory, edited by S. Buss, to be published by
        North-Holland Publ. Co.
S. JAgKOWSKI
  [1934]   On the rules of supposition in formal logic (Polish), Studia Logica (old
           series), 1, 5-32. Translation in Polish Logic 1920-39, S. McCall, ed.,
           Clarendon Press, Oxford, 1967, 232-258.
390                                                                   Bibliography

 [1963]   Über Tautologieen, in welchen keine Variabele mehr als zweimal vor-
          kommt, Zeitschrift fiir Mathematische Logik und Grundlagen der Math-
          ernatik, 9, 231-250.
      JOACHIMSKI AND R. MATTHES
 [1999]   Short proofs of nornalization for the simply-typed A-calculus, permuta-
          tive conversions and Gödel's T. Submitted.
I. JOHANSSON
 [1937]   Der Minimalkalkiil, ein reduzierter intuitionistischer Formalismus, Corn-
          positio Mathematica, 4, 119-136.
J.-B. JOINET, H. A. J. M. SCHELLINX, AND L. TORTORA DE FALCO
 [1998]   Linear decorations, simulations and normalization, Tech. Rep. Preprint
          nr.1067, Mathematisch Instituut, Universiteit Utrecht. Submitted.
A. JOYAL AND R. STREET
 [1991] The geometry of tensor calculus 1, Advances in Mathematics, 88, 55-112.

M. B. KALSBEEK
 [1994]   Gentzen systems for logic programming styles, Tech. Rep. CT-94-12,
          Institute for Logic, Language and Computation, University of Amster-
          dam.
 [1995]   Meta-Logics for Logic Programming, PhD thesis, Universiteit van Ams-
          terdam.
S. KANGER
 [1957]   Provability in Logic, Acta Universitatis Stockholmiensis. Stockholm
          Studies in Philosophy, vol. 1, Almqvist and Wiksell, Stockholm.
      M. KELLY
 [1964] On Mac Lane's conditions for coherence of natural associativities, com-
        mutativities etc., Journal of Algebra, 1, 397-402.
 [1972a] An abstract approach to coherence, in Mac Lane [1972], 106-147.
 [1972b] A cut-elimination theorem, in Mac Lane [1974 196-213.
G. M. KELLY AND S. MAC LANE
 [1971]   Coherence in closed categories, Journal of Pure and Applied Algebra, 1,
          97-140.
O. KETONEN
 [1944]   Untersuchungen zum Pradikatenkalkiil, Annales Acaderniae Scientiarum
          Fennicae, ser. A, I. Mathematica-physica, 23. A detailed review by
          P. Bernays is in The Journal of Symbolic Logic, 10 (1945), 127-130.
S. C. KLEENE
 [1952a] Introduction to Metamathematics, North-Holland Publ. Co., Amster-
          dam.
 [1952b] Permutability of inferences in Gentzen's calculi LK and LJ, Memoirs of
        the American Mathematical Society, 10, 1-26.
 [1955] Hierarchies of number-theoretic predicates, Bulletin of the American
        Mathematical Society, 61, 193-213. Additions and corrections in Pro-
        ceedings of the American Mathematical Society 8 (1957), p. 1006.
Bibliography                                                                     391

  [1967]   Mathematical Logic, Wiley and Sons, New York.
A. N. KOLMOGOROV
  [1925]   On the principle of the excluded middle (Russian), Matematicheskij
           Sbornik. Akademiya Nauk SS SR i Moskovskoe Matematicheskoe Obshch-
           estvo, 32, 646-667. Translation in van Heijenoort [1967], 414-437.
    A. KOWALSKI
  [1974] Predicate logic as a programming language, in Information Processing
           74- Proceedings of the IFIP congress 74, J. L. Rosenfeld, ed., North-
           Holland Publ. Co., Amsterdam, 569-574.
G. KREISEL
  [1953]   A variant to Hilbert's theory of the foundations of arithmetic, British
           Journal for the Philosophy of Science, 4, 107-127.
  [1958]   Elementary completeness properties of intuitionistic logic with a note
           on negations of prenex formulae, The Journal of Symbolic Logic, 23,
           317-330.
  [1968]   Notes concerning the elements of proof theory. Course notes of a course
           on proof theory at U.C.L.A., 1967-1968.
  [1977]   Wie die Beweistheorie zu ihren Ordinalzahlen kam und kommt, Jahres-
           bericht der Deutschen Mathematiker-Vereinigung, 78, 177-223.
G. KREISEL AND J.-L. KRIVINE
 [1972] Modelltheorie, Springer-Verlag, Berlin, Heidelberg, New York.

G. KREISEL AND G. TAKEUTI
  [1974]   Formally self-referential propositions for cut free classical analysis and
           related systems, Dissertationes Mathematicae, 118.
    A. KRIPKE
  [1963] Semantical analysis of modal logic I, Zeitschrift fiir Mathematische Logik
          und Grundlagen der Mathematik, 9, 67-96.
  [1965]   Semantical analysis of intuitionistic logic I, in Formal Systems and Re-
           cursive Functions, J. N. Crossley and M. A. E. Dummett, eds., Studies
           in Logic and the Foundations of Mathematics, North-Holland Publ. Co.,
           Amsterdam, 92-130.
S. KURODA
  [1951]   Intuitionistische Untersuchungen der formalistischen Logik, Nagoya
           Mathematical Journal, 2, 35-47.
J. LAMBEK
  [1958]   The mathematics of sentence structure, The American Mathematical
           Monthly, 65, 154-170.
  [1968]   Deductive systems and categories I: syntactic calculi and residuated cat-
           egories, Mathematical Systems Theory, 2, 287-318.
  [1969]   Deductive systems and categories II: standard constructions and closed
           categories, in Category Theory, Homology Theory and their Applications,
           P. J. Hilton, ed., Lecture Notes in Mathematics 86, Springer-Verlag,
           Berlin, Heidelberg, New York, 76-122.
392                                                                   Bibliography

  [1972]   Deductive systems and categories III: cartesian closed categories, intu-
           itionist propositional calculus, and combinatory logic, in Toposes, Alge-
           braic Geometry and Logic, F. W. Lawvere, ed., Lecture Notes in Math-
           ematics 274, Springer-Verlag, Berlin, Heidelberg, New York, 57-82.
  [1974]   Functional completeness of cartesian categories, Annals of Pure and Ap-
           plied Logic, 6, 259-292.
J. LAMBEK AND P. J. SCOTT
  [1986]   Introduction to Higher-Order Categorical Logic, Cambridge University
           Press, Cambridge, UK.
D. LEIVANT
  [1979]   Assumption classes in natural deduction, Zeitschrift fiir Mathematische
           Logik und Grundlagen der Mathematik, 25, 1-4.
  [1990]   Contracting proofs to programs, in Logic and Computer Science,
           P. Odifreddi, ed., Academic Press, New York, 279-327.
  [1994]   Higher-order logic, in Gabbay et al. [1994], 229-321.
C. I. LEWIS AND C. H. LANGFORD
  [1932]   Symbolic Logic, Appleton-Century-Crofts, New York. Reprinted Dover
           Publications, New York, 1951, 1959.
V. A. LIFSCHITZ
  [1989]   What is the inverse method?, Journal of Automated Reasoning, 5, 1-23.
P. LINCOLN, J. MITCHELL, A. SCEDROV, AND N. SHANKAR
  [1992]   Decision problems for propositional linear logic, Annals of Pure and
           Applied Logic, 56, 239-311.
J. W. LLOYD
  [1987] Foundations of Logic Programming, Springer-Verlag, Berlin, Heidelberg,
         New York.
P. LORENZEN
  [1950]   Konstruktive Begriindung der Mathematik, Mathematische Zeitschrift,
           53, 162-202.
H. LUCKHARDT
  [1989]   Herbrand-Analysen zweier Beweise des Satzes von Roth: Polynomiale
           Anzahlschranken, The Journal of Symbolic Logic, 54, 234-263.
      C. LYNDON
  [1959]   An interpolation theorem in the predicate calculus, Pacific Journal of
           Mathematics, 9, 129-142.
      MAC LANE
  [1963]   Natural associativity and commutativity, Rice University Studies, 49,
           28-46.
  [1971]   Categories for the Working Mathematician, Springer-Verlag, Berlin, Hei-
           delberg, New York.
  [1972]   ed., Coherence in Categories, Springer-Verlag, Berlin, Heidelberg, New
           York.
Bibliography                                                                    393

  [1976]   Topology and logic as a source of algebra, Bulletin of the American
           Mathematical Society, 82, 1-40.
  [1982]   Why commutative diagrams coincide with equivalence proofs, Contem-
           porary Mathematics, 13, 387-401.
S. MAEHARA
  [1954]   Eine Darstellung der intuitionistische Logik in der klassischen, Nagoya
           Mathematical Journal, 7, 45-64.
  [1960]   On the interpolation theorem of Craig (Japanese), Sugaku, 12, 235-237.
           Not seen by us.
S. MAEHARA AND G. TAKEUTI
  [1961]   A formal system of first-order predicate calculus with infinitely long
           expressions, Journal of the Mathematical Society of Japan, 13, 357-370.
P. E. MALMNÄS AND D. PRAWITZ
  [1969]   A survey of some connections between classical, intuitionistic and
           minimal logic, in Contributions to Mathematical Logic, H Schmidt,
           K. Schtitte, and H. Thiele, eds., North-Holland Publ. Co., Amsterdam,
           215-229.
C. R. MANN
 [1975] The connection between equivalence of proofs and Cartesian closed cat-
        egories, Proceedings of the London Mathematical Society. Third series,
        31, 289-310.
A. MARTELLI AND U. MONTANARI
  [1982]   An efficient unification algorithm, ACM Transactions on Programming
           Languages and Systems, 4, 258-282.
P. MARTIN-LÖF
  [1971a] Hauptsatz for the intuitionistic theory of iterated inductive definitions,
         in Proceedings of the Second Scandinavian Logic Symposium, J. Fenstad,
         ed., North-Holland Publ. Co., Amsterdam, 179-216.
  [1971b] Hauptsatz for the theory of species, in Proceedings of the Second Scan-
           dinavian Logic Symposium, J. Fenstad, ed., North-Holland Publ. Co.,
           Amsterdam, 217-233.
S. MARTINI AND A. MASINI
  [1993]   A computational interpretation of modal proofs, Tech. Rep. TR-27/93,
           Dipartimento di Informatica, Università di Pisa.
  [1994]   A modal view of linear logic, The Journal of Symbolic Logic, 59, 888-899.
A. MASINI
  [1992]   2-Sequent calculus: a proof theory of modalities, Annals of Pure and
           Applied Logic, 58, 229-246.
  [1993]   2-Sequent calculus: intuitionism and natural deduction, Journal of Lan-
           guage and Computation, 3, 533-562.
R. MATTHES
  [1998]   Extensions of System F by Iteration and Primitive Recursion on Mono-
           tone Inductive Types, PhD thesis, Mathematisches Institut der Univer-
           sit& Miinchen, Germany.
394                                                                    Bibliography

J. C. C. MCKINSEY AND A. TARSKI
  [1948]   Some theorems about the sentential calculi of Lewis and Heyting, The
           Journal of Symbolic Logic, 13, 1-15.
C. MCLARTY
  [1992]   Elementary Categories, Elementary Toposes, Oxford Logic Guides 21,
           Clarendon Press, Oxford.
F. METAYER
  [1994]   Homology of proof nets, Archive for Mathematical Logic, 33, 169-188.
D. MILLER
  [1994]   A multiple-conclusion meta-logic, in Proceedings. Ninth Annual Sympo-
           sium on Logic in Computer Science. July 1994, Paris, S. Abramsky, ed.,
           IEEE Computer Society .Press, Los Alamitos, California, 272-281.
D. MILLER, G. NADATHUR, F. PFENNING, AND A. SCEDROV
  [1991]   Uniform proofs as a foundation for logic programming, Annals of Pure
           and Applied Logic, 51, 125-157.
G. E. MINTS
  [1971]   Exact estimates of the provability of transfinite induction in the ini-
           tial segments of arithmetic (Russian), Zapiski Nauchnykh Seminarov
           Lenin gradskogo Otdeleniya Ordena Lenina Matematicheskogo Instituta
           imeni V. A. Steklova Akademii Nauk SSSR (LOMI), 20, 134-144. Trans-
           lation in Journal of Soviet Mathematics, 1 (1973), 85-91.
  [1975]   Finite investigations of infinite derivations (Russian), Zapiski Nauchnykh
           Seminarov Leningradskogo Otdeleniya Ordena Lenina Matematicheskogo
           Instituta imeni V. A. Steklova Akademii Nauk SSSR (LOMI), 49, 67
           122. Translation in Journal of Soviet Mathematics, 10 (1978), 548-596.
  [1977]   Closed categories and the theories of proofs(Russian), Zapiski Nauch-
          nykh Seminarov Leningradskogo Otdeleniya Ordena Lenina Matematich-
          eskogo Instituta imeni V. A. Steklova Akademii Nauk SSSR (LOMI), 68,
         83-114. Translation in Journal of Soviet Mathematics, 15 (1981), 45-62;
         also revised translation in Mints [1992c], 183-212.
  [1978] On Novikov's hypothesis (Russian). Photocopied proceedings. Transla-
         tion in Mints [1992c], 147-151.
  [1979] A coherence theorem for for cartesian closed categories (abstract), 'The
          Journal of Symbolic Logic, 44, 453-454.
  [1990] Gentzen-type systems and resolution rules. Paxt I. Propositional logic, in
          Colog-88, G. E. Mints and P. Martin-Löf, eds., Lecture Notes in Math-
         ematics 417, Springer-Verlag, Berlin, Heidelberg, New York, 198-231.
  [1992a] Normalization of natural deduction and the effectivity of classical exis-
           tence, in Mints [1992c], 123-146. This is a translation of the Russian
          original in Logicheskij Vyvod (Logical Inference). Proceedings of the All-
          Union Symposium on the Theory of Logical inference, V. A. Smirnov,
          ed., Nauka, Moskva, 1979, 245-265.
  [1992b] Proof theory and category theory, in Mints [1992c], Bibliopolis, Napoli,
          and North-Holland Publ. Co., Amsterdam, 157-182.
  [1992c] Selected Papers in Proof Theory, North-Holland Publ. Co., Amsterdam;
          Bibliopolis, Napoli.
Bibliography                                                                     395

  [1992d] A Short Introduction to Modal Logic, CSLI Lecture Notes 30, Center for
          the Study of Language and Information, Stanford, California.
  [1992e] A simple proof of the coherence theorem for CCC, in Mints 1.1992q,
          Bibliopolis, Napoli, and North-Holland Pub!. Co., Amsterdam, 213-220.
  [1993] Resolution calculus for the first order linear logic, Journal of Logic, Lan-
          guage and Information, 2, 59-83.
  [1994a] Cut-elimination and normal forms of sequent derivations, Tech. Rep.
          CSLI-94-193, CSLI, Stanford. Contains: Normal forms for sequent
          derivations; Indexed systems of sequents and cut-elimination; Normal-
          ization as an epsilon substitution process.
  [1994b] Gentzen-type systems and resolution rule. Part II. Predicate Logic, in
          Logic Colloquium '90, J. Oikkonen and J. Väänänen, eds., Lecture Notes
          in Logic 2, Springer-Verlag, Berlin, Heidelberg, New York, 163-190.
  [1994c] Resolution strategies for intuitionistic logic, in Constraint Programming,
          B. Mayoh, E. Tyugu, and J. Penjam, eds., Springer-Verlag, Berlin, Hei-
           delberg, New York, 289-312.
  [1995]   Natural deduction in intuitionistic linear logic. Manuscript dated May
           19, 1995.
  [1996]   Normal forms for sequent derivations, in Kreiseliana, P. Odifreddi, ed.,
           A.K. Peters, Wellesley, MA., 469-492.
  [1997]   Indexed systems and cut-elimination, Journal of Philosophical Logic, 26,
           671-696.
  [1999]   Axiomatization of a Skolem function in intuitionistic logic, in Formaliz-
           ing the Dynamics of Information, M. Faller, S. Kaufmann, and M. Pauly,
           eds., CSLI, Stanford, CA. To appear.
N. MOTOHASHI
  [1984a] Approximation theory of uniqueness conditions by existence conditions,
          Fundamenta Mathematicae, 120, 127-142.
  [1984b] Equality and Lyndon's interpolation theorem, The Journal of Symbolic
           Logic, 49, 123-128.
J. MYHILL, A. KINO, AND R. E. VESLEY
  [1970]   eds., Intuitionism and Proof Theory, North-Holland Publ. Co., Amster-
           dam.
    NAGASHIMA
  [1966]   An extension of the CraigSchfitte interpolation theorem, Annals of the
           Japan Association for the Philosophy of Science, 3, 12-18.
    P. NEDERPELT, J. H. GEUVERS, AND R. C. DE VRIJER
  [1994]   eds., Selected Papers on Automath, North-Holland Publ. Co., Amster-
           dam.
   NEGRI
  [1999]   Sequent calculus proof theory of intuitionistic apartness and order rela-
           tions, Archive for Mathematical Logic, 38, 521-547.
S. NEGRI AND J. VON PLATO
  [1998]   Cut elimination in the presence of axioms, The Bulletin of Symbolic
           Logic, 4, 418-435.
396                                                                    Bibliography

  [1999]   Sequent calculus in natural deduction style. Manuscript.
J. VON NEUMANN
  [1927]   Zur Hilbertschen Beweistheorie, Mathematische Zeitschrift, 26, 1-46.
M. H. A. NEWMAN
 [1942] On theories with a combinatorial definition of "equivalence", Annals of
         Mathematics, 2nd series, 43, 223-243.
A. OBERSCHELP
  [1968]   On the CraigLyndon interpolation theorem, The Journal of Symbolic
           Logic, 33, 271-274.
H. ONO AND Y. KOMORI
  [1985]   Logics without the contra,ction rule, The Journal of Symbolic Logic, 50,
           169-201.
V. P. OREVKOV
  [1979]   Lower bounds for the lengthening of proofs after cut-elimination (Rus-
           sian), Zapiski Nauchnykh Seminarov Leningradskogo Otdeleniya Ordena
           Lenina Matematicheskogo Instituta imeni V. A. Steklova Akademii Nauk
           SSSR (LOMI), 88, 137-162, 242-243. Translation Journal of Soviet
           Mathematics, 20 (1982), 2337-2350.
 [1984]    Upper bounds for the lengthening of proofs after cut-elimination (Rus-
           sian), Zapiski Nauchnykh Seminarov Leningradskogo Otdeleniya Ordena
           Lenina Matematicheskogo Instituta imeni V. A. Steklova Akademiz Nauk
           SSSR (LOMA 137, 87-98. Translation Journal of Soviet Mathematics,
           34 (1986), 1810-1819.
  [1987]   Applications of Cut elimination to obtain estimates of proof lengths,
           Doklady Akademii Nauk SSSR, 296, 539-542. Translation Soviet Math-
           ematics Doklady, 36 (1988), 292-295.
H. OSSWALD
  [1973]   Ein syntaktischer Beweis fiir die Zuverlässigkeit der Schnittregel im
           Kalkill von Schfitte fiir die intuitionistische Typenlogik, Manuscripta
           Mathematica, 8, 243-249.
P. PÄPPINGHAUS
  [1983]   Completeness properties of classical theories of finite type and the nor-
           mal form theorem, Dissertationes Mathematicae, 207.
J. B. PARIS
  [1978]   Some independence results for Peano arithmetic, The Journal of Sym-
           bolic Logic, 43, 725-731.
C. PARSONS
  [1973]   Transfinite induction in subsystems of number theory (abstra,ct), The
           Journal of Symbolic Logic, 38, 544-545.
F. PFENNING
  [1994]   A structural proof of cut elimination and its representation in a logical
           framework, Tech. Rep. CMUCS-94-218, School of Computer Science,
           Carnegie-Mellon University.
Bibliography                                                                     397

A. M. PITTS
 [1992] On an interpretation of second-order quantification in first-order intu-
         itionistic propositional logic, The Journal of Symbolic Logic, 57, 33-52.
J. VON PLATO
  [1998]   Structure of derivations in natural deduction. Manuscript.
  [1999]   A proof of Gentzen's Hauptsatz without multicut. To appear in the
           Archive for Mathematical Logic.
W. POHLERS
  [1989]   Proof Theory. An Introduction, Lecture Notes in Mathematics 1407,
           Springer-Verlag, Berlin, Heidelberg, New York.
A. POIGNE
  [1992]   Basic category theory, in Abramsky et al. [1992], 413-640.
J. C. VAN DE POL AND H. SCHWICHTENBERG
  [1995]   Strict functionals for termination proofs, in Proceedings of the Second
           International Conference on Typed Lambda Calculi and Applications,
           Edinburgh, Scotland, M. Dezani-Ciancaglini and G. Plotkin, eds., Lec-
           ture Notes in Computer Science 902, Springer-Verlag, Berlin, Heidel-
           berg, New York, 350-364.
    POTTINGER
  [1977]   Normalization as a homomorphic image of cut-elimination, Annals of
           Mathematical Logic, 12, 323-357.
  [1983]   Uniform, cut-free formulations of T, 84 and 85, The Journal of Symbolic
           Logic, 48, 900.
D. PRAWITZ
  [1965]   Natural Deduction. A Proof-Theoretical Study, Almquist and Wiksell,
           Stockholm.
  [1967]   Completeness and Hauptsatz for second-order logic, Theoria, 33, 246
           253.
  [1968]   Hauptsatz for higher-order logic, The Journal of Symbolic Logic, 33,
           452-457.
  [1970]   Some results for intuitionistic logic with second-order quantification
           rules, in Myhill et al. [1970], 259-269.
  [1971]   Ideas and results in proof theory, in Proceedings of the Second Scandi-
           navian Logic Symposium, J. E. Fenstad, ed., North-Holland Publ. Co.,
           Amsterdam, 235-307.
  [1981]   Validity and normalizability of proofs in 1st and 2nd order classical and
           intuitionistic logic, in Atti de Congresso Nazionale di Logica, S. Bernini,
           ed., Bibliopolis, Napoli, 11-36.
D. J. PYM AND J. A. HARLAND
  [1994]   A uniform proof-theoretic investigation of logic programming, Journal
           of Logic and Computation, 4, 175-207.
    RASIOWA
  [1954] Constructive theories, Bulletin de l'Académie Polonaise des Sciences.
           Série des Sciences Mathématiques, Astronomiques et Physiques, 2, 121
           124.
398                                                                     Bibliography

  [1955]    Algebraic models of axiomatic theories, Fundamentae Mathematicae, 41,
            291-310.
H. RASIOWA AND R. SIKORSKI
  [1953]    Algebraic treatment of the notion of satisfiability, Fundamentae Mathe-
            maticae, 40, 62-95.
  [1960]    On the Gentzen theorem, Fundamentae Mathematicae, 48, 57-69.
  [1963]    The Mathematics of Metamathematics, PAN, Warszawa.
W. RAUTENBERG
  [1983]    Modal tableau calculi, Journal of Philosophical Logic, 12, 403-423.
J. C. REYNOLDS
  [1974]    Towards a theory of type structure, in Programming Symposium, Pro-
            ceedings. Colloque sur la Programmation, B. Robinet, ed., Lecture Notes
            in Computer Science 19, Springer-Verlag, Berlin, Heidelberg, New York,
            408-425.
A. ROBINSON
  [1956]    A result on consistency and its application to the theory of definition,
            Indagationes Mathematicae, 15, 330-339.
J. A. ROBINSON
  [1965]    A machin.e-oriented logic based on the resolution principle, Journal of
            the Association for Computing Machinery, 12, 23-41.
S. RONCHI DELLA ROCCA AND L. ROVERSI
  [1994]    Lambda-calculus and intuitionistic linear logic, tech. rep., Department
            of Computer Science, Università di Torino, Torino, Italy.
D. ROORDA
  [1994]    Interpolation in fragments of classical linear logic, The Journal of Sym-
            bolic Logic, 419-444.
G. F. ROSE
 [1953] Propositional calculus and realizability, Transactions of the American
        mathematical Society, 175, 1-19.
G. SAMBIN, G. BATTILOTTI, AND C. FAGGIAN
  [1997]    Basic logic: reflection, symmetry, visibility. To appear.
    SAMBIN AND C. FAGGIAN
  [1998] From basic logic to quantum logics with cut-elimination, International
            Journal of Theoretical Physics, 37, 31-37.
L. E. SANCHIS
  [1967]    Functionals defined by recursion, The Notre Dame Journal of Formal
            Logic, 8, 161-174.
  [1971]    A generalization of the Gentzen Hauptsatz, The Notre Dame Journal of
            Formal Logic, 12, 499-504.
      A. J. M. SCHELLINX
  [1991]     Some syntactical observations on linear logic, Journal of Logic and Com-
            putation, 1, 537-559.
Bibliography                                                                      399

  [1994]   The Noble Art of Linear Decorating, PhD thesis, Universiteit van Ams-
           terdam.
P. SCHROEDER-HEISTER
  [1984]   A natural extension of natural deduction, The Journal of Symbolic Logic,
           49, 1284-1300.
   S CHULTE- MONTING
  [1976]   Interpolation formulas for predicates and terms which carry their own
           history, Archiv fiir Mathematische Logik und Grundlagenforschung, 17,
           159-170.
    SCHÜTTE
  [1950a] Beweistheoretische Erfassung der unendliche Induktion in der Zahlen-
         theorie, Mathematische Annalen, 122, 369-389.
  [1950b] Schlussweisen-Kalkiile der Prädikatenlogik, Mathematische Annalen,
                  47-65.
  [1951]   Die Eliminierbarkeit des bestimmten Artikels, Mathematische Annalen,
                  166-186.
  [1956]   Ein System des verkniipfenden Schliessens, Archiv fiir Mathematische
           Logik und Grundlagenforschung, 2, 34-67.
  [1960]   Beweistheorie, Springer-Verlag, Berlin, Heidelberg, New York.
  [1962]   Der Interpolationssatz der intuitionistischen Prädikatenlogik, Mathema-
           tische Annalen, 148, 192-200.
  [1977]   Proof Theory, Springer-Verlag, Berlin, Heidelberg, New York.
H. S CHWICHTENB ERG
  [1976]   Definierbare Funktionen im A-Kalkiil mit Typen, Archiv fiir Mathema-
           tische Logik und Grundlagenforschung, 17, 113-114.
  [1977]   Proof theory: some applications of cut-elimination, in Handbook of
           Mathematical Logic, J. Barwise, ed., North-Holland Publ. Co., Ams-
           terdam, 867-895.
  [1991]   Normalization, in Logic, Algebra and Computation, F. Brauer, ed.,
           Springer-Verlag, Berlin, Heidelberg, New York, 201-235.
  [1992]   Minimal from classical proofs, in Computer Science Logic. 5th
           Workshop, CSL'91. Berne, Switzerland, October 1991. Proceedings,
           E. Börger, G. Jager, H. Kleine Biining, and M. Richter, eds., Lecture
           Notes in Computer Science 626, Springer-Verlag, Berlin, Heidelberg,
           New York, 326-328.
  [1998]   Finite notations for infinite terms, Annals of Pure and Applied Logic,
           94, 201-222.
  [1999]   Termination of permutative conversions in intuitionistic Gentzen calculi,
           Theoretical Computer Science, 212, 247-260.
D. S. S COTT
  [1979]   Identity and existence in intuitionistic logic, in Applications of Sheaves,
           M. P. Fourman, C. J. Mulvey, and D. S. Scott, eds., Lecture Notes in
           Mathematics 753, Springer-Verlag, Berlin, Heidelberg, New York, 660
           669.
400                                                                   Bibliography

J. P. SELDIN AND J. R. HINDLEY
  [1980]   eds., To H. B. Curry: Essays on Combinatory logic, Lambda Calculus
           and Formalism, Academic Press, New York.
D. J. SHOESMITH AND T. J. SMILEY
  [1978]   Multiple-Conclusion Logic, Cambridge University Press, Cambridge,
           UK.
      SKOLEM
  [1923]   Begriindung der elementaren Arithmetik durch die rekurrierende
           denkweise ohne Anwendung scheinbarer Veränderlichen mit unendlichen
           Ausdehnungsbereich, Videnskaps Selskapet i Kristiania, Skrifter Utgit
           (1), 6, 1-38. Translation van Heijenoort [1967], 303-333.
R. M. SMULLYAN
  [1965]   Analytic natural deduction, The Journal of Symbolic Logic, 30, 123-139.
  [1966]   Trees and nest structures, The Journal of Symbolic Logic, 31, 303-321.
  [1968]   First-order Logic, Springer-Verlag, Berlin, Heidelberg, New York.
      SOCHER-AMBROSIUS
  [1994]   Deduktionssysteme, BI-Wissenschaftsverlag, Mannheim, Germany.
      V. SOLOVJOV
  [1979]   Derivation of equivalence of proofs under reduction of formula depth
           (Russian, with English summary), Zapiski Nauchnykh Seminarov
           Lenin gradskogo Otdeleniya Ordena Lenina Matematicheskogo Instituta
           imeni V. A. Steklova Akademii Nauk SSSR (LOMA 88, 197-207. Trans-
           lation Journal of Soviet Mathematics, 20 (1982), 2370-2376.
  [1997]   Proof of a conjecture of S. Mac Lane, Annals of Pure and Applied Logic,
           90, 101-162.
C. SPECTOR
  [1962]   Provably recursive functions of analysis: a consistency proof of analysis
           by an extension of principles formulated in current intuitionistic mathe-
           matics, in Recursive Function Theory, J. C. E. Dekker, ed., Symposia in
           Pure Mathematics V, American Mathematical Society, Providence, RI,
           1-27.
G. STILMARCK
  [1991]   Normalization theorems for full first order classical natural deduction,
           The Journal of Symbolic Logic, 56, 129-149.
R. F. STÄRK
  [1990]   A direct proof for the completeness of SLD-resolution, in Computer
           Science Logic, Selected Papers from CSL '89, E. Börger, H. Kleine
           Böning, and M. M. Richter, eds., Lecture Notes in Computer Science
           440, Springer-Verlag, Berlin, Heidelberg, New York, 382-383.
R. S TATMAN
 [1978] Bounds for proof-search and speed-up in the predicate calculus, Annals
           of Pure and Applied Logic, 15, 225-287.
Bibliography                                                                    401

E. TAHHAN BITTAR
  [1999]   Strong normalization proofs for cut elimination in Gentzen's sequent
           calculi, Banach Center Publications, 46, 179-225. The title of the vol-
           ume is Logic, Algebra, and Computer Science, published by the Polish
           Academy of Sciences, Warszawa.
W. W. TAIT
 [1965] Infinitely long terms of transfinite type, in Formal Systems and Recur-
        sive Functions, J. N. Crossley and M. A. E. Dummett, eds., Studies in
        Logic and the Foundations of Mathematics, North-Holland Publ. Co.,
        Amsterdam, 176-185.
 [1966] A nonconstructive proof of Gentzen's Hauptsatz for second-order predi-
        cate logic, Bulletin of the American Mathematical Society, 72, 980-988.
 [1967] Intensional interpretation of functionals of finite type, I, The Journal of
           Symbolic Logic, 32, 198-212.
  [1968]   Normal derivability in classical logic, in The Syntax and Semantics of
           Infinitary Languages, K. J. Barwise, ed., Lecture Notes in Mathematics
           72, Springer-Verlag, Berlin, Heidelberg, New York, 204-236.
  [1975]   A realizability interpretation of the theory of species, in Proceedings of
           Logic Colloquium, R. J. Parikh, ed., Lecture Notes in Mathematics 453,
           Springer-Verlag, Berlin, Heidelberg, New York, 240-251.
M. TAKAHASHI
  [1967]   A proof of cut-elimination in simple type theory, Journal of the Mathe-
           matical Society of Japan, 19, 399-410.
  [1970]   A system of simple type theory of Gentzen style with inference on ex-
           tensionality and the cut-elimination in it, Commentarii Mathematici
           Universitatis Sancti Pauli, 18, 129-147.
G. TAKEUTI
  [1978]   Two Applications of Logic to Mathematics, Princeton University Press,
           Princeton NJ.
  [1987]   Proof Theory. 2nd edition, North-Holland Publ. Co., Amsterdam.
A. TARSKI
  [1956]   Logic, Semantics, Metamathematics. Papers from 1923 to 1938, Claren-
           don Press, Oxford, UK.
A. S. TROELSTRA
  [1973]   Metamathematical Investigation of Intuitionistic Arithmetic and Analy-
           sis. Chapters 1-4, Lecture Notes in Mathematics 344, Springer-Verlag,
           Berlin, Heidelberg, New York.
  [1983]   Logic in the writings of Brouwer and Heyting, in Atti del Convegno Inter-
           nazionale di Storia della Logica, San Gimignano, 4-8 dicembre 1982,
           V. M. Abrusci, E. Casan, and M. Mugnai, eds., Cooperativa Libraxia
           Universitaria Editrice Bologna, Bologna, Italy, 193-210.
  [1986]   Strong normalization for typed terms with surjective pairing, The Notre
           Dame Journal of Formal Logic, 27, 547-550.
  [1990]   On the early history of intuitionistic logic, in Mathematical Logic, P. P.
           Petkov, ed., Plenum Press, New York, 3-27. Proceedings of the Heyting
           '88 Summer School and Conference on Mathematical Logic, September
           13-23, 1988 in Chaika, Bulgaria.
402                                                                     Bibliography

  [1992a] Lectures on Linear Logic, CSLI-Lecture Notes 29, Center for the Study
          of Language and Information, Stanford, California.
  [1992b] Realizability, Tech. Rep. ML-92-09, Institute for Logic, Language and
          Computation, University of Amsterdam. A revised version is to appear
          in Handbook of Proof Theory, S. Buss, ed., North-Holland Publ. Co.,
          Amsterdam.
  [1995] Natural deduction for intuitionistic logic, Annals of Pure and Applied
           Logic, 73, 79-108.
  [1999]   Marginalia on sequent calculi, Studia Logica, 62, 291-303.
A. S. TROELSTRA AND D. VAN DALEN
  [1988]   Constructivism in Mathematics, Studies in Logic and the Foundations
           of Mathematics, North-Holland Publ. Co., Amsterdam. Two vols.
T. UESU
  [1984]   An axiomatization of the apartness fragment of the theory DLO+ of
           dense linear order, in Logic Colloquium '84, Lecture Notes in Mathe-
           matics 1104, Springer-Verlag, Berlin, Heidelberg, New York, 453-475.
A. M. UNGAR
  [1992]   Normalization, Cut-Elimination, and the Theory of Proofs, Center for
           the Study of Language and Information, Stanford, California. CSLI-
           Lecture Notes 28.
A. URQUHART
  [1995]   The complexity of propositional proofs, The Bulletin of Symbolic Logic,
           1, 425-467.
S. VALENTINI
  [1986]   A syntactic proof of cut-elimination of GLlin, Zeitschrift far Mathemat-
           ische Logik und Grundlagen der Mathematik, 32, 137-144.
R. VESTERGAARD
  [1998a] A computational anomaly in the Troelstra-Schwichtenberg G3i(m) sys-
          tem. Manuscript.
  [1998b] The cut rule and explicit substitutions (author's cut), Tech. Rep. TR-
          1998-9, Depaxtment of Computer Science, University of Glasgow.
A. VISSER
  [1996]   Uniform interpolation and layered bisimulation, in Gödel '96 (Brno,
           1996), Lecture Notes in Logic 6, Springer-Verlag, Berlin, Heidelberg,
           New York, 139-164.
R. VOREADOU
  [1977]   Coherence and non-commutative diagrams in closed categories, Memoirs
           of the American Mathematical Society, 182.
N. N. VOROB'EV
  [1964]   A new algorithm for derivability in a constructive propositional calcu-
           lus (Russian), Trudy Ordena Matematicheskogo Instituta imeni V. A.
           Steklova. Akademiya Nauk SSSR, 72, 195-227. Translation in American
           Mathematical Society Translations. Series 2, 94 (1970), 37-71.
Bibliography                                                                  403

R. C. DE VRIJER
 [1987] Surjective Pairing and Strong Normalization: two Themes in Lambda
         Calculus, PhD thesis, University of Amsterdam.
M. WAJSBERG
  [1938]   Untersuchungen iiber den Aussagenkalkiil von A. Heyting, Wiadomoici
           Matematyczne, 46, 45-101. Translation in Wajsberg [1977], 132-171.
  [1977]   Logical Works, Zaklad Narodowy Imiena Ossoliriskich., Wydawnictwo
           Polskiej Akademii Nauk. Wroclaw, Poland. Edited by S. J. Surma.
H. WANSING
  [1994]   Sequent calculi for normal modal propositional logics, Journal of Logic
           and Computation, 4, 125-142.
  [1998]   Translation of hypersequents into display sequents, Journal of the IGPL
           Interest Group in Pure and Applied Logics, 6, 719-733.
J. I. ZUCKER
  [1974]   The correspondence between cut-elimination and normalization I, II,
           Annals of Mathematical Logic, 7, 1-156.
Symbols and notations
Below we list symbols and notations which either appear in the text more
than just locally, or are important for other reasons. The more important
notations and conventions in use throughout the book are found in section
1.1. For conventions on prooftrees, see 1.3.2, 3.1.4, 4.1.2.

Logical operators
A, V, >                 2           (primitive propositional operators)
V, 3                    2, 345      (quantifiers)
-,, -.>-                3           (defined operators)
_L                      2, 294      (falsity)
T                       3, 294      (truth)
                        7           (sequent arrow)
0, 0                    284         (necessary, possible)
A, V                    3, 7        (iterated conjunction and disjunction)
n, u, *, +, 0, --4      294         (binary linear logic operators)
,--, 0, 1               294         (negation, zero, unit of linear logic)
i
- ,
      7                 295         (modalities of linear logic)

Substitution
E     [0]               4, 11       (substitution in expression)
E P. 1n                 4, 11       (simultaneous substitution)
A [Xn 1 AY .,6]         4           (second-order substitution)
A (t)                   4           (convention on substitution)
F [*] , F[A]            6           (context, substitution in context)

Measures on trees and formulas
I TI                    9           (depth of a tree T)
s(T)                    9           (size of a tree T)
ls(T)                   9           (leafsize of a tree T)
IAI                     10          (depth of a formula A)
s(A)                    10          (size of a formula A)
w(A)                    113         (weight of a formula A)
                                      404
Symbols and notations                                                                  405

lev(A)                           217, 323        (level of a formula A)

Turnstile symbols
H, Hs                            7               (deducibility)
Hc, Hi, Hm                       8               (deducibility in C, I, M)
1n, HI                           76              (deducibility with depth < n)
I-5<n; Hrsr<n                    76              (deducibility with size < n)
1c                               150, 153        (deducibility with 'rank' d and depth < n)

Theories. Theories, i.e. sets of theorems, are characterized by the formalisms
generating them. For general conventions in the designation of theories, see
1.1.7.
AP                   136    HA               203      IL           295      PA     322,337
C                     39    HA2              358      Ip2          349      PRA        127
CL                   295    I                 39      M             39      S4         284
EQAP                 137   le                200

Formalisms. For general conventions in the designation of formalisms, see
1.1.7.
AP-G3i                     136        G4ip                   112     Hs                284
G1 [mic]                    61        G5i                    247     IU                300
m-Gli                       68        Gcl                    295     N[mic]             35
Gis                        286        Gil                    295     Ni2               345
G2[mic]                     65        GK[mic]                 84     Nie, Nie          200
G3[mic]                     77        h-GKi                  193     Rcp               244
G3[mic]=                   134        t-GKi                  192     Rip               249
m-G3[mi]                    82        GS[123]                 86     Z                 321
G3s                        287        GS5p                   243     Zn                323
                                      H [mic]                 51

Type systems. Designations of the principal type systems:
A,                          15        )01--+AT               264     A2S2              356
)44                         15        A2                     349     CL,                  18



Terms and constants of type formalisms
App                              11, 47          (application operator)
tit2     tn                      11              (iterated application of t1, t2, .)
Ax                               11, 47          (abstraction on variable x)
Au                               46              (abstraction on assumption variable u)
Ax1x2         xn.t               11              (iterated lambda-abstraction on t)
k, s                             11, 18          (combinators)
406                                                               Symbols and notations

p(t, s), (t, s)                46, 47     (pair of t,$)
Po, Pi                         46         (unpairing functions, left and right)
1(0, ki                        46         (injections, left and right)
ExV,y                          46         (disjunction elimination operator)
E3y                            47         (existence elimination operator)
                               47         (operator corresponding to li)

Rules and axioms. Let t E {A, V, -4, V, 3},                E {A, V, ÷, V, 3, El, 0, W, C}.

tI, tE                         36-37      (introduction and elimination rules)
                               37         (absurdity rules)
DI                             284        (neccessitation rule)
Ax,                                       axioms; see the respective G-systems.
Rt, Lt                                    see the respective G-systems.
V2I, Y2E, 321, 32E             204, 345   (second-order quantifier-rules)
Cut                            66,86      (context-free Cut rule)
Cut                            67         (context-sharing Cut)
R,Ru                           236        (resolution, unrestricted resolution)
Ind                            317        (induction schema)
TI                             317        (transfinite induction)

Reductions and conversions
In chapter 10            >L- are used for orderings of the natural numbers, in
particular for the standard ordering of ordertype 5.

                               12         (reduction, general)
                               12         (converse reduction)
--<                            320        (in chapter 10: standard well-ordering)
                  >.-on etc.   13         (0-reduction, etc.)
:=0                            15         (0-equality)
=On                            15         (077-equality)
    =w                         19         (weak reduction, equality)
>gß,                           217        (generalized 0-reduction)



Translations and embeddings
                               49         (GödelGentzen negative translation)
                               50         (Kolmogorov's negative translation)
                               50         (Kuroda's negative translation)
                               288        (modal embeddings)
                               300        (Girard's embedding)
Symbols and notations                                                407

Resolution (chapter 7)
dom, ranv               232     (domain and variable-range)
                        236     (metavariables for Horn clauses)
P,                      236     (metavariables for programs)
9_1v7 pv7               236     (universal closures)
[1                      236     (empty goal)
R,Ru                    236     (resolution rules)
r, j9_,u r
                        237     (unrestricted resolution step)
            r           237     (resolution step)
rIP                     239     (computed answer)

Categorical logic (chapter 8)
f: A        B, A   B    259     (notation for arrows)
go     f                259                     f
                                (composition of and g)
AA B, A ÷ B             259     (product and exponent objects)
idA                     259     (identity arrow)
  AB        AB
7ro'       71'          259     (projection arrows)
(f,g)                   259     (pairing of arrows)
                        259     (terminal object)
trA                     259     (truth arrow)
ev A B                  259     (evaluation arrow)
cur                     259     (currying operator)
CCC(PV)                 263     (free category over PV)
                        263     (isomorphism of objects)

Other notations
                        2       (end-of-proof symbol)
-=-                     2       (literal identity)
lN                      2       (natural numbers)
PV                      2       (propositional variables)
FV                      4, 46   (free variables)
II                      6       (number of elements in multiset)
rus,rA                  6       (join of multisets)
Set(r)                  7       (set associated with multiset r)
hyp(t, t', t")          149     (hyperexponentiation)
21, 41,2k, 4k           149     (abbreviations for hyperexponentiation)
fiA, NA                 20      (Church numerals on basis A)
   N                    350     (second-order Church numerals)
Comp                    210     (computability predicate)
Index
abstraction, 11                               cancelled, 38
    type, 349                                 closed, 37
absurdity rule                                discharged, 38
    classical, 37                             eliminated, 38
    intuitionistic, 37                        open, 37
active formula, 62, 78                        stability, 50
Aczel, 140                                assumption class, 23, 36
Aczel slash, 107, 140                     assumption variable, 46
adjacent inferences, 164                  atomic formula, 2
admissible rule, 76                       atomic instances of axioms, 66
     dp-, 76                              AUTOMATH, 59
Altenkirch, 365                           Avron, 91
Andou, 224                                axiom
Andreoli, 257                                 b-, c-, w-, 42
answer, 239                                   k-, s-, 33
     computed, 239                            4-, 284
     correct, 239                             K-, 284
antecedent, 62                                normality, 284
application, 11                               T-, 284
     simple, 329                          axiom link, 305
     type, 349
approximation theorem, 297                Baader, 255
APS, 308                                  Babaev, 281, 282
Apt, 255                                  Bachmann, 318
arithmetic                                balanced formula, 274
     Heyting, 203                         Barendregt, 3, 10, 16, 365
     intuitionistic, 203                  basic logic, 316
     Peano, 322                           BCK-logic, 292
     primitive recursive, 127-129         Beeson, 224
arithmetical system, 321                  Belnap, 91, 315
     classical, 322                       Benthem, van, 140
     intuitionistic, 322                  Benton, 316
     restricted, 323                      Bernays, 139, 343
arrow, 259                                Beth, 89, 90, 139, 141
     identity, 259                        Beth's definability theorem, 118, 340
     truth, 259                           Bezhanishvili, 139
     variable, 260                        BHK-interpretation, 55
assumption                                Bibel, 87
     bound, 38                            Blyth, 258
                                    408
Index                                                                   409

Borisavljevie, 139                   collapsing map, 361
Borieie, 228                         Colmerauer, 255
bottom-violation lemma, 167, 175     combinator, 265
bound assumption, 38                     A-, 265
branch, 9                            combinatory logic
    main, 187                            typed, 18
branching                            complete discharge convention, 43
    k-, 9                            completeness
Brouwer, 35                              combinatorial, 20
BrouwerHeytingKolmogorov interpre-       semantic, 105
         tation, 55                  completeness for linear resolution, 241
BrouwerKleene ordering, 341          completeness of resolution calculus, 246
Bruijn, de, 3, 59                    complexity theory, 177
Buchholz, 176, 343, 344              composition of arrows, 259
Bull, 313                            composition of substitutions, 232
Buss, 140, 176                       comprehension
                                         elementary, 203
cancelled assumption, 38             computability candidate, 352
candidate                            computability predicate, 210, 272
     computability, 352              conclusion of a link, 305
cartesian closed category, 261       conclusion of a proof structure, 305,
category, 261                                 306
     cartesian closed, 261           confluent, 14
     free, 262                           weakly, 14
      free cartesian closed, 262     conjunction (object), 259
c.c., 352                            conservative, 8
CCC, 261                             conservativity of definable functions,
      free, 262                               124, 142
CDC, 43                              consistency (of contexts), 41
Cellucci, 228                        constructions
Chang, 255                               calculus of, 365
Church, 57                           context, 6, 41, 62
Church numeral, 20, 349                  negative, 5
ChurchRosser property, 14                positive, 5
     weak, 14                            strictly positive, 6
class                                context-free, 64
     predicative, 203                context-independent, 64
clause, 244                          context-sharing, 64
     initial, 246                    contraction, 61, 194
     intuitionistic, 248                 dp-admissible, 80
clause formula, 244                  convention
     intuitionistic, 248                 variable, 38
closed                               conversion, 12
     dp-, 76                             ß-, 13
closure (under a rule), 76               ßi-, 14
codomain of an arrow, 259                17-, 13
coherence theorem, 274, 281-282          A-, 180
410                                                                    Index

      V-, 180                             normal, 179
      V-perm, 180                         pure-variable, 38, 62
      -4-, 180                        deduction from hypotheses, 7
      V-, 180                         deduction graph, 259
      3-, 180                             positive, 259
      3perm, 181                          tci-, 259
      detour, 180, 347                deduction theorem, 58
     g0-, 183, 217                        modal, 285
     generalized 0-, 183, 217         deduction tree, 75
     permutation, 180                 deduction variable, see assumption vari-
     simplification, 181                       able
conversion equality, 12               definability
conversum, 12                             explicit, 107
convertible, 12                       definability theorem
Coquand, 365                              Beth's, 118, 340
CR, 14                                del-rule, 179
Craig, 141                            del-rules, 198
critical cut, 179                     depth (of a formula), 10
Curen, 282                            depth of a tree, 9
Curry, 56, 58-59, 89, 90, 140, 176,   dereliction, 194
          177, 224, 313, 315          derivable rule, 76
currying operator, 259                derivation, 22
Cut, 66                                    convertible, 329
     additive, 67                          normal, 329
     closure under, 67, 92-102             quasi-normal, 331
     context-sharing, 67              detachment rule, 58
cut, 66, 179                          deviation reduction, 278
     critical, 179                    Diller, 224
     critical g-, 217                 discharged assumption, 38
     g-, 217                          disjunction property, 106, 107
cut elimination, 92-102, 287, 298     Doets, 239, 255
     continuous, 344                  domain of an axrow, 259
     generalizations of, 126          domain of a substitution, 232
     numerical bounds on, 148-157     Dokn, 111
cut link, 305                         Dokn, 315
cut reduction lemma, 148              double negation law, 51
Cut rule, 66, 139                     dp-admissible rule, 76
cutformula, 66                        dp-closed, 76
cutlevel, 93                          dp-invertible, 77
cutrank, 93, 179, 327                 Dragalin, 68, 88, 139, 364
                                      duality
Dalen, van, ix, x, 143                    De Morgan, 85, 296
Danos, 139, 312, 316                  Dummett, 91
De Morgan duality, 85, 296            Dyckhoff, 139, 141, 225
decidability of Ip, 108
deduction, 22                         E-logic, 199
    natural, 23                       E-part, 187, 199
Index                                                                         411

E-rule, 36                                     principal, 62, 78
Eisinger, 255                                  Rasiowa-Harrop, 107, 140
eliminated assumption, 38                      side, 62
elimination                               formula clause, 244
    cut, see cut elimination              formula occurrence, 6, 7
elimination of empty succedent, 66             negative, 6, 7
elimination part, 187, 199                     positive, 6, 7
elimination rule, 36                           strictly positive, 6
embedding                                 formulas-as-types, 25, 58, 365
    Girard, 300                           fragment
    modal, 288, 314                            negative, 48
equality                                  free (for a variable), 3
    conversion, 12                        free cartesian closed category, 262
equivalent substitutions, 233             free category, 262
evaluation (arrow), 259                   free CCC, 262
ex-falso-quodlibet schema, 322            Frege, 57
exchange rule, 87                         Friedman, 344, 364
excluded middle                           Fujiwara, 142
    law of, 51                            function object, 259
expansion, 205
explicit definability, 107                G (rule), 51
exponent object, 259                      g-cut, 217
extensions (of G1-systems), 126               critical, 217
extensions (of G3-systems), 130           G-system, 60
extensions (of N-systems), 197                multi-succedent, 82
                                          Gallier, 87, 176, 344, 365
fa,ct, 207                                Gandy, 224, 225
faithfulness of modal embedding, 291      Generalization rule, 51
Felscher, 142, 176                        Gentzen, ix, 56-58, 60, 87, 89, 90, 111,
Fitting, 139, 143, 145, 176, 313, 315               139, 177, 318, 321, 343
Flagg, 314                                Gentzen system, 60, 61, 65, 77, 87, 88,
f.o,, 6                                             112, 141, 247, 286, 287, 294,
formula                                            295
      active, 62, 78                      Gentzen's method of cut elimination,
      atomic, 2                                    101
      balanced, 274                       Gentzen-Schfitte system, 85
      cut, 66                             Geuvers, 365
      goal, 236                           Girard, ix, 90, 142, 143, 176, 292, 297,
      Harrop, see Rasiowa-Harrop                   304, 314-316, 343, 349, 352,
      hereditary Harrop, see hereditary            365, 366
           Rasiowa-Harrop                 Girard emb'edding, 300
      hereditary Rasiowa-Harrop, 176      Glivenko, 57
      interpolation, 116                  goal, 236
      main, 62                            goal formula, 236
      negative, 48                        Gödel, 58, 224, 313, 314
             322                          Goodman, 314
    prime, 2                              Gordeev, 176, 344
412                                                                       Index

Goré, 315                              idempotent substitution, 234
Grabmayer, 89, 139                     identity
graph                                      literal, 2
    deduction, 259                     identity arrow, 259
    positive deduction, 259            iff, 2
    tci-deduction, 259                 IH, 2
                                       implication
H-system, 51                                linear, 294
Hardin, 282                            implication (object), 259
Harland, 256                           induction
Harrington, 344                             transfinite, 317
Harrop, 140                            instance of a formula, 332
Harrop formula, see Rasiowa-Harrop     interpolant, 116
    hereditary, see Rasiowa-Harrop     interpolation, 116-123, 141-142, 313,
head formula, 194                               316, 340
head-cut, 194                          interpolation formula, 116
Headcut rule, 301                      introduction paxt, 187, 199
height of a tree, 9                    introduction rule, 36
Heijenoort, van, 177                   intuitionistic logic, 57
Heindorf, ix, 139                      inversion lemma, 79, 89, 290
Herbelin, 89, 226                      inversion principle, 90
Herbrand, 58, 177, 255                 inversion-rule strategy, 149-157
Herbrand's theorem, 108, 168, 175      invertible, 77
Hertz, 139                                  dp-, 77
Heyting, 57, 58                             left, 77
Hilbert, ix, 57, 142                        right, 77
Hilbert system, 51, 57, 284, 297       IPS, 307
Hindley, x, 10, 58, 282                isomorphism (of objects), 263
Hintikka, 89, 139
Hirokawa, 281                          Jaeger, 255
Hodas, 256, 257                        Jáskowski, 56, 57, 281
Hodges, 255                            Joachimski, 225
Horn clause, 236                       Johansson, 57, 87
    definite, 236                      Joinet, 139, 316
Horn formula, 207                      Joyal, 282
    definite, 207
    definite generalized, 207          K-axiom, 284
    generalized, 207                   Kalsbeek, 255
Howard, 59, 224, 225                   Kanger, 90, 139, 313
Hudelmaier, 89, 141, 176               Ketonen, 88, 89, 139, 142
Hughes, 313                            Kleene, ix, 57, 84, 87, 139-142, 177,
Hyland, 365                                     344
hyperexponential function, 149         Kleene's systems, 83
hypothesis of a proof structure, 305   Kolmogorov, 57, 58
                                       Kowalski, 255
I-part, 187, 199                       Kreisel, 142, 176, 343, 344, 365
I-rule, 36                             Kripke, 139, 315
Index                                                                413

Kuroda, 58                          literal, 246
                                         negative, 85
1-rank, 217                              positive, 85
L-rule, 61                          Lloyd, 255
lambda calculus                     local permutation lemma, 170, 172
     extensional simple typed, 15   local rule, 75
     polymorphic, 349               Lorenzen, 90
     simple typed, 15               Luckhardt, 177
Lambek, 263, 282, 292               Lyndon, 141
Lambek calculus, 292
law of double negation, 51
                                    m.g.a., 234
law of the excluded middle, 51
                                    m.g.u., 234
leaf, 9
                                    Mac Lane, 258
leafsize, 9
                                    Maehara, 141, 314
left rule, 61
                                    main formula, 62
Leivant, 225, 364, 366
                                    major premise, 37
lemma
                                    Malmnäs, 140
     bottom-violation, 167, 175
                                    Mann, 282
     cut reduction, 99, 148
                                    marker, 36
     inversion, 79, 89, 290
     local permutation, 170, 172    Martelli, 255
     Newman's, 14                   Martin-Löf, 16, 223, 365
     substitution, 12               Martini, 315
length of a branch, 9               Matthes, 225, 365
length of a clause (formula), 244   maximal segment, 179
length of a formula, 10             McKinsey, 314
length of a segment, 179            McLarty, 258
length of a tree, 9                 Metayer, 316
letter                              mid-cut, 194
     proposition, 2                 Midcut rule, 301
level                               midsequent theorem, 177
    implication, 217                Miller, 256
level (of a cut), 93                minimal logic, 57
level of a derivation, 326          minimal part, 199
level of a formula, 217, 323        minimum part, 187
level of an ordinal, 318            minor premise, 37
level-rank, 217                     Mints, 91, 140, 223, 226, 255, 274,
Lewis, 313                                  281, 282, 313-316, 344
Lincoln, 299                        modal embedding, 288, 314
linear implication, 294             modal logic, 313
linear logic, 315                   Modus Ponens, 51
     classical, 295                 most general unifier, 234
     intuitionistic, 295            Motohashi, 140, 142
linear resolution                   MP, 51
     completeness for, 241          multi-succedent G-system, 82
     soundness for, 239             multicut, 101
link, 305                           Multicut rule, 101
414                                                                        Irtdex

multiple-conclusion natural deduction,   order of a track, 187
          228                            order-restriction, 167, 169
multiset, 6                              ordering theorem, 167, 171, 175
                                         ordinal, 318
N-system, 35                             ordinal notation, 318
Nagashima, 141, 143                      Orevkov, 225
natural deduction, 23, 56                Osswald, 365
    multiple-conclusion, 228
    term calculus for, 46                Päppinghaus, 365
natural deduction in sequent style, 41   par, 294
natural deduction system, 35             par link, 305
necessitation rule, 284                  parentheses, 3
Nederpelt, 59                            Paris, 343
negative formula, 48                     Parsons, 344
negative fragment, 48                    part
negative literal, 85                            elimination, 187, 199
negative translation, 48, 58                    introduction, 187, 199
    Gödel-Gentzen, 49                           minimal, 199
    Kolmogorov's, 50                            minimum, 187
    Kuroda's, 50                                strictly positive, 5
Negri, 143, 224, 226                     partition
Neumann, 57                                  admissible, 167, 169, 174
Newman, 14                               Peano arithmetic, 337
Newman's lemma, 14                       Peano axioms, 321
node, 9                                  Peirce rule, 56
    bottom, 9                            Peirce's law, 43
    top, 9                               permutable rules, 164, 252
non-introduced, 210, 352                 permutation
non-sharing, 64                               variable-, 233
normal, 193, 347                         permutation conversion, 180
normal deduction, 179                    permutation rule, 87
normal form, 12                          permuting below, 164
    unique, 274                          Pfenning, 89
normality axiom, 284                     Pitts, 141
normalization, 182, 218, 224, 347        Plato, von, 139, 143, 226
    bounds on, 215-216, 219-223          Pohlers, ix, 343
      strong, 183, 210, 218, 273, 347,   Poigné, 258
          351, 365                       Pol, van de, 225
normalizing                              polymorphic lambda calculus, 349
    strongly, 13                         polynomial, 21
numeral, 321                                  extended, 21
                                         positive deduction graph, 259
Oberschelp, 142                          positive literal, 85
object, 259                              Pottinger, 91, 225
    function, 259                        Prawitz, 13, 56, 57, 89, 90, 112, 140,
one-sided system, 85, 90                          189, 223-225, 365
Ono, 292                                 pre-cut formula, 217
Index                                                                       415

predecessor, 9                                 weak, 19
    immediate, 9                          reduction of strong normalization, 212
predicative class, 203                    reduction sequence, 12
premise                                   reduction tree, 12
    major, 37                             redundant, 276
    minor, 37                             relevant unifier, 234
premise of a link, 305                    renaming, 3
prime formula, 2                          Renardel de Lavalette, 224
primitive recursive arithmetic, 127-129   representable, 20
primitive rule, 76                        resolution, 255
principal formula, 62, 78                 resolution calculus, 249, 316
product (object), 259                     resolution derivation, 239
program                                        unrestricted, 238
    definite, 236                         resolution rule, 237, 244
progression rule, 331                          unrestricted, 236
progressive, 323                          resolution system, 244
proof, 22                                 resultant, 237
proof structure, 305                      Reynolds, 365
    abstract, 308                         right rule, 61
    inductive, 307                        Robinson, 141, 255
proofnet, 308, 316                        Ronchi della Rocca, 316
prooftree, 22, 75                         Roorda, 316
proper variable, 62                       root, 9
pruning, 193                              Rose, 281
PS, 305                                   rule
    inductive, 307                             admissible, 76
pure-variable deduction, 38, 62                Cut, 66, 139
Pym, 256                                       del-, 179
                                               derivable, 76
quantum logic, 316                             detachment, 58
query, 236                                     exchange, 87
                                               left, 61
R-rule, 61                                     local, 75
rank (of a cut), 93                            Multicut, 101
Rasiowa, 90, 140, 314                          Peirce, 56
RasiowaHarrop foimula, 107                     permutation, 87
    hereditary, 176                            primitive, 76
Rautenberg, 313                                progression, 331
recursive functions                            right, 61
    provably total, 363                   rule P, 56
redex, 12, 329
    critical, 217                         Sambin, 316
reduction, 12                             Sanchis, 142, 224
    deviation, 278                        Schellinx, 314-316
    generated, 12                         Schroeder-Heister, 226, 229
    one-step, 12                          SchulteMönting, 142
    proper, 12                            Schatte, 90
416                                                                       Index

Schiitte, 90, 139, 141, 142, 343         strong normalization, 183, 210, 218,
Schwichtenberg, 21, 176, 225, 255, 343           273
Schiitte, ix                                  reduction of, 212
Scott, 224                               strongly normalizing, 13
second-order arithmetic                  subformula, 4
    intuitionistic, 358                       literal, 4
second-order extension                        negative, 5
    weak, 203                                 positive, 5
segment, 179                                  strictly positive, 5
    maximal, 179                         subformula (segment), 179
    minimum, 187                         subformula property, 66, 105, 188
semantic tableau, 89, 143-146, 314       substitution, 3, 4, 11, 232
separation, 66, 106, 139, 189                 idempotent, 234
sequence                                      identical, 232
    reduction, 12                             rule, 57
sequent, 7                                    variable, 232
       2-, 275                           substitutivity, 15, 16
sharpened Hauptsatz, 177                 succedent, 62
Shoesmith, 228                           successful, 239
side formula, 62                             unrestrictedly, 239
simple type, 10                          successor, 9
simplification conversion, 181               immediate, 9
size
                                         sum
     leaf-, 9                                Hessenberg, 319
size of a formula, 10                        natural, 319
                                         switching, 308
size of a tree, 9
                                         system
Skolem, 127
                                                 60
slash
                                             Gentzen, 60
     Aczel, 107, 140
                                                 51
SLD-derivation, 239
                                             Hilbert, 51, 57
SLD-resolution
                                             LR-, 75
     completeness for, 241
                                             N-, 35
    soundness for, 239
                                         system F, 349
Smullyan, 57, 143, 224                   Szabo, 87
SN, 13
Socher-Ambrosius, 139                    T-axiom, 284
Solovjov, 281, 282                       tableau
soundness for linear resolution, 239          semantic, 89, 143-146, 314
s.P.P., 5                                Tahhan Bittax, 139
stability, 50                            Tait, 16, 90, 176, 224, 329, 365
stability axiom, 71                      Tait calculus, 90
stability schema, 322                    Takahashi, 365
Stälmarck, 224                           Takeuti, ix, 141, 176, 224, 343, 344
Stärk, 255                               Takeuti's conjecture, 365
Statman, 176                             Tarski, 58
strictly positive part, 5                tci-deduction graph, 259
Index                                                                         417

tensor, 294                                    assumption, 46
tensor link, 305                               free, 4, 11
term calculus for Ni, 46                       proper, 38, 62
term-labelled calculus for t-G2i, 73           proposition, 2, 3
theorem                                        type, 10
     approximation, 297                    variable arrow, 260
     Beth's definability, 118, 340         variable convention, 38, 62
     coherence, 274, 281-282               variable substitution, 232
     deduction, 58                         variable-permutation, 233
     Herbrand's, 108, 168, 175             variant, 233
     interpolation, 116, 123, 125, 340     Vestergaard, 89
     midsequent, 177                       Visser, 141
     modal deduction, 285                  Voreadou, 282
     ordering, 167, 171, 175               Vorob'ev, 141
     separation, 106, 139, 189             Vrijer, de, 281
track, 185
                                           Wajsberg, 139, 281
     main, 187
                                           Wansing, 91, 315
tree, 9
                                           WCR, 14
     deduction, 22, 75
                                           weak second-order extension, 203
     derivation, 22
                                           weakening, 61
     labelled, 9
                                                depth-preserving, 65
     reduction, 12
                                           weight, 113
Troelstra, 1, 35, 55, 58, 127, 128, 140,
                                           w.l.o.g., 2
          224-226, 281, 297, 315, 316,
         364, 366                          Zucker, 225
truth arrow, 259
truth function, 339
truth predicate, 339
Turing, 224
type
     function, 10
    simple, 10
type abstraction, 349
type application, 349

Uesu, 140
Ungax, 228
unification, 235, 255
unifier, 234
     most general, 234
     relevant, 234
unsuccessful, 239
     unrestrictedly, 239
Urquhaxt, 177

Valentini, 315
variable

