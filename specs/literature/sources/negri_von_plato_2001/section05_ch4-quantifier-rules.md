# Structural Proof Theory — Chapter 4: Quantifier Rules (lines 3152-4313)

4.1. QUANTIFIERS IN NATURAL DEDUCTION AND IN SEQUENT CALCULUS

(a) The language of predicate logic: The language of first-order logic con-
tains constants a,b,...,    variables x, y , . . . , n-place functions fn, gn,..., and
              n    n
predicates P , Q ,..., for any n ^ 0, the zero-place connective _L, the two-
place connectives &, V, D, and the quantifiers V, 3. The arity of functions and
predicates is often left unwritten. Constants and variables are sometimes writ-
ten as a\, a2,..., JCI, Jt2,..., or a,a\...,        x, xf,    Constants can be thought
of as zero-place functions, and there can be, analogously, zero-place constant
propositions.
Terms are denoted by t, u,... or t\, t2,... or t, tf,... and are defined inductively
by the clauses:

      1. Constants are terms,
      2. Variables are terms,
      3. Application of an n-ary function fn to terms t\,..., tn gives a term


                                                                                  61
62                      STRUCTURAL PROOF THEORY

Formulas are defined inductively by the clauses:

      1. J_ is a formula,
      2. Application of an n-ary predicate Pn to terms t\,...,tn          gives a
         formula P(h,...,  tn\
      3. If A and B are formulas, ASiB, A v B, and A D 5 are formulas,

      4. If A is a formula, VxA and 3JC A are formulas.

The set of free variables FV(t) in a term £ is defined inductively by:

      1. Fort = a,FV(a) = 0,
      2. Forf =x,FV(x) = {x},
      3. For? = fn(tu • • •, *„), FV(/(ri, ...,*„)) = F Vft) U . . . U FVfe).

The set of free variables FV(A) in a formula A is defined inductively by:

      1.
      2. FV(P(tu     • • •, tn)) = FV(h) U . . . U
      3. FV(A&B) = FV(A v 5 ) = FV(A D 5 ) = FV(A) U
      4. FV(VJCA) = FV(3xA) = FV(A) - {x}.

A term or formula that has free variables is open; otherwise it is closed. In 4, x is a
bound variable. In first-order logic, a principle of renaming of bound variables,
or of-conversion, is often assumed: It consists in identifying formulas differing
only in the names of bound variables, usually expressed as VJC A(X) = VyA(y) and
3xA(x) = 3yA(y). Such a principle is intuitively justified by the role of bound
variables as placeholders, as in fa f(x)dx, which is the same as fa               f(y)dy.
We shall not need to assume this principle here, as it will be formally derivable
once the quantifier rules are given an appropriate formulation. Also, we shall not
use the notation A(x) to indicate that A contains, or may contain, the free variable
x. The parenthesis notation is used for application of a function or predicate, as
in the definition of terms and formulas above. If a variable does not occur in a
formula, sequent, or derivation, we say it is fresh for that formula, sequent, or
derivation.
    In terms t, as well as in formulas A, a variable x can be substituted by a term
t'. To identify what is substituted for what, the notation [t'/x] is used. The result
of substitution [t'/x'] is written as t(t'/x) for a term t and as A(t'/x) for a formula
A. Substitution is defined by induction on the terms and formulas in which the
substitution is performed:
                                         THE QUANTIFIERS                                63

Substitution [t/x] in a term:

      1. a(t/x) — a,
      2. y(t/x)      = y if y ^ x a n d y(t/x)         =         tify=x,
           n                              n
      3 . f (tu     . . . , tn){t/x) = f (h(t/x\        . . . , tn(t/x)).

Substitution [t/x] in a formula:

      1. ±(t/x) = ±,
      2. ( P ^ f o , . . . , tn))(t/x)   - Pn(h(t/x),...,           tn{t/x)\
      3. (A o B)(t/x) = A(t/x) o B(t/x), for o = &, V, D,
      4. QiyA)(t/x) = VyA(t/x) ify^x,                       (WyA)(t/x) = WyA ify = x,
      5. (3yA)(t/x) = 3yA(t/x) \iy+x, (3yA)(t/x) = 3yA ify=x.

The last two clauses in the above definition guarantee that substitution does
not act on bound variables. We shall call A(t/x) a substitution instance of A.
Simultaneous substitution of n terms t\,..., tn for n variables x\,..., xn is writ-
ten as [t\/x\,..., tn/xn], and its result in a term t is written as t(t\/x\,..., tn/xn)
and in a formula A as A(t\/xi,...,       tn/xn).
   When a term r is substituted for a variable x in a formula A, it may happen that
some variables of the term t "get caught" in the substitution, by some quantifiers in
A. If this happens, the validity of substitution instances of a universal formula is no
longer guaranteed. As an example, consider the formula Vy3x(y < x) that holds
in a linearly ordered set without greatest element. Dropping the first quantifier
and substituting x for y produces 3x(x < x), which is not satisfiable in the same
domain. However, if we rename the bound variable x by z before performing the
substitution, we obtain 3z(x < z) that is satisfiable.
   We say that a term t is free for x in A if no variable of t becomes bound as
an effect of the substitution of t for x in A. The binding may happen if some
variables of t are in the scope of quantifiers in A. However, instead of con-
trolling the condition for each substitution, we observe that the condition can
always be met by appropriate renaming of bound variables in the formula A:
If A is, say, VxB and y is a variable not occurring in A, a-conversion guar-
antees that we can identify A with VyB(y/x). In this way we can ensure that
a variable does not occur both free and bound in a formula. When consider-
ing a substitution, we shall assume that this condition is satisfied, if neces-
sary by renaming of bound variables, and shall sometimes omit recalling the
condition.
64                      STRUCTURAL PROOF THEORY

(b) Quantifiers in natural deduction: The intuitionistic meaning explanations
for quantified formulas VJCA and =bt A are as follows:

       1. A direct proof of VxA consists of a proof of A(y/x) for an arbi-
       trary y.
       2. A direct proof of 3xA consists of a proof of A(a/x) for some
       individuals.

In natural deduction, the premiss for the introduction rule of a universal propo-
sition WxA is that A(y/x) has been derived for an arbitrary y. To be arbitrary
means that nothing more than the range of possible values is assumed known
about y. This condition is expressed as a variable restriction on the introduction
rule for the universal quantifier. The premiss for an existential proposition is that
A has been derived for some individual a.
     The introduction rules for the quantifiers are:

                              A(y/x)            A(a/x)
                                       v/                31



The rule of universal introduction has the variable restriction that y must not
occur free in any assumption that A(y/x) depends on nor in VxA. The latter
condition can be equivalently expressed by requiring that y is equal to x or
else y is not free in A. The variable restriction guarantees that y stands for an
"arbitrary individual" for which A holds, which is the direct ground for asserting
the universal proposition.
   Usually rule V/ is written as ^ ^ and the restriction is that x is not free in
any of the assumptions that A depends on, where one must keep in mind that if
A is an assumption it depends on itself. With this rule, a-conversion has to be
postulated as a principle to be added to the system. In the rule we use, instead,
this conversion is built in. We also modify rule 3 / for the same reason: Instead of
having the premiss for some individual, the premiss will have an arbitrary term f,
thus the rule we use for the existential quantifier is:

                                       A{t/x)
                                        3xA

   To determine the general elimination rule corresponding to rule V/, assume a
derivation of A(y/x) for an arbitrary y. In deriving consequences from A(y/x)
for y arbitrary, any instances A(t/x) may be used; thus the auxiliary deriva-
tion of the general elimination rule leads to some consequence C from assump-
tions A(t\/x),...,  A(tn/x). We simplify this situation by admitting only one
                              THE QUANTIFIERS                                  65

assumption A(t/x) and obtain the rule
                                        [A(t/x)]

                                VxA         C
                                                -WE
                                       C
The rule with the assumptions A(t\/x),...,  A{tn/x) is admissible, by the repeti-
tion of the above rule n times.
   Rules V7 and WE satisfy the inversion principle: Given a derivation of A(y/x)
for an arbitrary y, a derivation of A(t/x) is obtained for any given term t by
substitution. Therefore, the derivation

                                 :          [A(t/x)]
                                               \



converts through the use of the substitution into a derivation of C without rules
V/andV£:


                                      A(t/x)

                                        C
The standard elimination rule for universal quantification is obtained when
C = A(t/x):


                                     A(t/x)
The standard elimination rule for the existential quantifier already is of the form
of general elimination rules:

                                        [A(y/x)]

                                3xA         C   • 3E
                                       C
It has the restriction that y must not occur free in 3x A, C nor in any assumption
C depends on except A(y/x). The rule is in accordance with our inversion prin-
ciple: The direct grounds for deriving 3xA can consist in deriving A for any one
individual in the domain of the bound variable. For C to be derivable from 3x A,
in order to take all possible cases into account, it must be required that C follow
from A{y/x) for an arbitrary y, and this is what the variable restriction in rule
66                     STRUCTURAL PROOF THEORY

3E expresses. If in a derivation 3xA was inferred by 3 / from A(t/x) and 3xA is
the major premiss of 3E, then C follows in particular from A(t/x). The inversion
principle is satisfied, for the derivation

                                 :          [A(y/x)]
                              A(t/x)           !

                                        c
converts into a derivation of C without rules 31 and 3E:


                                       A(i/x)

                                         C
The addition of the above introduction and elimination rules to the system of
natural deduction for intuitionistic propositional logic will result in the system of
natural deduction for intuitionistic predicate logic.
   The introduction rule for existence is in accordance with the intuitionistic or
constructive notion of existence. Further, the definability of existence in terms
of negation and universal quantification, 3xA = ^Wx ~ A, fails in intuitionistic
predicate logic, and all four quantifier rules are needed.
   In classical logic, indirect existence proofs are permitted and existence cannot
have the same meaning as in intuitionistic logic, but no finitary system of natural
deduction with normalization and subformula property has been found for full
classical predicate logic. There is a natural deduction system with good structural
properties only for the v - and 3-free fragment, to be presented in Chapter 8. The
idea is to translate formulas with v or 3 into formulas known to be classically
equivalent but not containing these operations: For any formula C that should be
derivable but is not, there is a translated formula C* that is derivable. An example
of such a translation is Prawitz' system of natural deduction for stable logic, i.e.,
a system of propositional logic in which the law of double negation is derivable.
The translation gives a v-free fragment by translating disjunctions Av B into
implications ~ADB. However, such a translation is not suited for representing
the structure of derivations in full classical logic, disjunction included.

(c) Quantifiers in sequent calculus: As mentioned, there is at present no fini-
tary normalizing system of natural deduction for the full language of classical
predicate logic. In sequent calculus, instead, cut-free calculi for intuitionistic as
well as full classical predicate logic were found already by Gentzen. To obtain
a sequent calculus for intuitionistic predicate logic, quantifier rules are added to
the intuitionistic propositional calculus G3ip. The rules are, with repetition of the
                                THE QUANTIFIERS                                  67

principal formula in LV similarly to LD,

                                G3i
   A(t/x), VxA, F =* C
                           LV
                           LV
            , r =» c                      r=
   A(y/x), F =» C                       F => A(f/*)
                      L3


The restriction in RV is that y must not occur free in F, VxA. The restriction in
L3 is that y must not occur free in 3xA, F, C.
   Unlike in natural deduction, in sequent calculus all propositional rules are
local. In quantifier rules, fulfillment of the variable restrictions is controlled in
the same local way.
   We obtain the rules of sequent calculus for classical predicate logic by adding
to the propositional calculus G3cp the rules

                                 G3c
   A(t/x), VxA, F =• A                   F =^ A, A(y/x)
                           TV                        —    /?V
              F ^ A                        F ^ A V A
   A(y/x), F => A                         F =» A, 3xA, A(t/x)
                      L3
    3xA, F =^ A                              F ^   A,3JCA       *3

The restriction in /^V is that y must not occur free in F, A, Vx A. The restriction
in L3 is that y must not occur free in 3xA, F, A. We may summarize these
conditions by the requirement that y must not occur free in the conclusion of the
two rules. In the propositional part of G3c, because of invertibility of all rules
there was no need to repeat principal formulas in premisses of rules, but to obtain
admissibility of contraction for G3c, repetition is needed in LV and R3.
   The weight of quantified formulas is defined as

   wp/xA) = w(A)+l,
   w(3xA) = w(A)+l.
Height of derivation is defined as before.
   The following lemma is a formal version of the principle of renaming of bound
variables:

Lemma 4.1.1: Height-preserving a-conversion. Given a derivation V of
F => C in G3i (o/F => A in G3c), it can be transformed into a derivation V of
Tf => C (of Vf => A') where F', Ar, C, andV differ from F, A, C, and V only
by fresh renamings of bound variables.

Proof: We shall give the proof for G3i, the proof for G3c being similar, by
induction on the height n of the derivation. If n = 0, F =>• C is an axiom or
68                      STRUCTURAL PROOF THEORY

conclusion of L_L, then also F' =>> C", where the bound variables have been
renamed by fresh variables, is an axiom or conclusion of L_L. Else F =>• C has
derivation height > 0. If all the rules in the derivation are propositional ones,
the renaming is inherited from the premisses (axioms) to the conclusion of the
derivation. Otherwise we consider the last quantifier rule in the derivation. If it
is LV, with conclusion VxA, r " =>• C and premiss A(t/x), WxA, r " =>• C, and
x has to be renamed by the fresh variable y, by inductive hypothesis from the
premiss we obtain a derivation of the same height of A(t/x), WyA(y/x), V =>> C,
that is, of A(y/x)(t/y), VyA(y/x), V =» C", and therefore, by applying LV, we
obtain a derivation of the same height of the conclusion VyA(y/x), Tr =>• C.
If the last quantifier rule is Ri, with conclusion F =>• WxA from the premiss
F =>• A(z/x), by inductive hypothesis we have a derivation of the same height of
F / =>• A'(z/x), where bound occurrences of x have been renamed by y. This is
the same as F" =»• A\y/x){z/y)\    thus we obtain by #V, F" =>• VyA'(y/x), with
the same bound on the derivation height as the sequent F =>• V* A. The cases of
L3 and /?3 are treated symmetrically to RW and L3. QED.

   If in a sequent F ^ A a term t is substituted for a variable x, derivability of
the sequent is maintained, with the same derivation height. The proviso for the
substitution is that the term t be free for x in every formula of the sequent F =>> A
(or, for short, t is free for x in F =>• A). Substitution of free occurrences of x by
t in all formulas of F is denoted by T(t/x).

Lemma 4.1.2: Substitution lemma.
     (i) IfV=>C is derivable in G3i and t is free for x inV, C, then T{t/x)^
          C(t/x) is derivable in G3i, with the same derivation height.
     (ii) IfV^Ais      derivable in G3c and t is free for x inV, A, then T(t/x) =>
          A(t/x) is derivable in G3c, with the same derivation height.
Proof: We only give the proof of (i), the proof of (ii) being similar. The proof is
by induction on height of derivation.
   By Lemma 4.1.1, it is not restrictive to suppose that in the derivation of F =>• C
the bound variables have been renamed so that the sets of free and bound vari-
ables are disjoint. With this assumption, some cases in the proof can be avoided.
Furthermore, by the choice of fresh variables not occurring in the term to be
substituted, the condition of being free for x in the sequent where the substitution
occurs is maintained.
   If F => C is an axiom or conclusion of L_L, then T{t/x) => C(t/x) also is
an axiom or conclusion of L_L. Else F =>> C has derivation height n > 0, and
we consider the last rule in the derivation. If F =>• C has been derived by a
propositional rule, we observe that if t is free for x in the conclusion of any such
rule, then it is free for x in the premisses, since there is no alteration in the sets
                              THE QUANTIFIERS                                   69

of free and bound variables. Therefore the inductive hypothesis can be applied to
the premisses, and the conclusion follows by application of the rule.
   If F =>• C has been derived by LV, we can exclude the case in which x is
the quantified variable in the rule since in this case x would not be free and the
substitution would be vacuous. Therefore we can assume that the premiss is

                              A(t'/y),VyA,r'    => C
with y ^ x. Since t is free for x in A(t'/y), by inductive hypothesis we have a
derivation of height ^ n — 1 of

                               ), QfyA)(t/x), T\t/x) => C(t/x)

Observe that by definition of substitution and the fact that x / y, we have
                             QiyA)(f/x) = VyA(t/x).
The two substitutions in (A(tf / y))(t / x) can be given as one simultaneous substi-
tution A(t'(t/x)/y, t/x)\ Since t is free for x in VyA, the term t does not contain
the variable y, so the latter is equal to (A(t/x))(tf(t/x)/y). Summing up, we have
a derivation of height ^ n — 1 of

                  {A(t/xW/y),VyA(t/x\ T\t/x) =» C(t/x)

where t" = tf(t/x)\ so by LV we obtain a derivation of height < n of

                          VyA{t/x\ T\t/x) => C(t/x)

that is, of

                         QiyA){t/x\ T\t/x) => C(t/x)

  If the last rule is /?V, we can exclude, as above, the case in which x is the
quantified variable. Therefore the derivation ends with

                                   T =» A(z/y)


where j ^ x , and z is not free in F, and z = y or z is not free in A. By inductive
hypothesis we can replace z by a fresh variable v not in r. So we have a derivation
of height ^ n — 1 o f F =>- A(v/y). Again by inductive hypothesis we obtain a
derivation of height ^ n — 1 of

                              T{t/x) =• A(vly)(t/x)

By the choice of f and the fact that £ does not contain the variable y (as it is free
for x in Vj A) we can switch the order of substitutions and obtain a derivation of
70                     STRUCTURAL PROOF THEORY

height < n — 1 of

                              T{t/x) =* A(t/x)(v/y)
where the variable conditions for applying RW are met and we can infer T(t/x) =$>
VyA(t/x), and since x / y this is the same as T{t/x) => (VyA)(t/x).
   The cases of L3 and R3 are treated symmetrically to RV and LV. QED.


4.2. ADMISSIBILITY OF STRUCTURAL RULES

We first prove the admissibility of structural rules for the intuitionistic calculus.
The corresponding proofs for the classical calculus are very close to this because
of the similarity of the quantifier rules.

(a) Admissibility of structural rules for G3i: The proofs extend those for the
propositional calculus in Chapter 2.

Lemma 4.2.1: Sequents of the form C, F =>• C are derivable in G3i.

Proof: As for G3ip in Lemma 2.3.3, by induction on weight of C. The new
cases are for the quantified formulas. If C = VxA, by inductive hypothesis
A(y/*)> VxA, F => A(y/x) is derivable, where y is a fresh variable. By appli-
cation of LV and RV, VxA, F =>• VxA is derivable. If C = EbcA, by inductive
hypothesis we have a derivation of A(y/x), F =>• A(y/x) and the conclusion fol-
lows by application of R3 and L3. QED.

Theorem 4.2.2: Height-preserving weakening for G3i.

     / / \-n F => C, then hn D, F => C.

Proof: By induction on height of derivation, as in weakening for G3ip,
Theorem 2.3.4. For applications of LV and R3, the weakening formula can be
added to the context of the premiss. For RV and L3, we have to consider the effect
of variable restrictions.
   If the last rule applied is RW, the premiss is F =>• A(y/x). If y is not free in
D, by inductive hypothesis we get D, F =>• A(y/x) and hence Z), F => VxA(x)
by /^V. If j is free in D, we choose a fresh variable z and apply Lemma 4.1.2
to F =>• A(y/x) to obtain F =^ A(z/x). The inductive hypothesis gives Z), F =>•
A(z/x), so that by i^V we derive D, F =» Vx A.
   If the last rule is L3, with premiss A(y/x), V =>• C and j is not free in D,
we derive the conclusion by applying the inductive hypothesis to the premiss and
then the rule. If y is free in D, we choose a fresh variable z for substitution in the
premiss and obtain A(z/x), F / =>• C. By inductive hypothesis D, A(z/x), F' =>>
C is derivable, and by L3 the conclusion D, 3xA, F r =>• C follows. QED.
                                THE QUANTIFIERS                                       71

Lemma 4.2.3: Height-preserving inversion of L3 for G3i.

   / / \-n 3xA, F => C, f/ien hn A(v/x), F =^ C.

Proof: By induction on height of derivation. If n = 0 and if i t A, F =>• C is an
axiom or conclusion of L_L, then also A(y/x), F =>• C is an axiom or conclusion
ofL_L.
    For the inductive case, if 3x A is not principal in the last rule and y is not free in
its premisses, we have one or two premisses, 3xA, Ff =>> C and 3xA, Y" =>• C".
Now apply inductive hypothesis and then the rule again to conclude A(y/x), F =^
C. If instead the last rule is a rule with a variable restriction on y, we need a
substitution before applying the inductive hypothesis to the premiss of the rule,
as the substitution [y/x] could bring in free occurrences of y that would then
prevent applying the rule again. Suppose for instance that the derivation ends
with
                                       V => B(y/z)


By the substitution lemma we can replace y by a fresh variable v in the premiss
and obtain, using B(y/z)(v/y) = B(v/z), the derivation,
                                          B(v/z)
                                                   Ind
                               A(y/x), F => B(v/z)

If 3x A is principal in the last rule, the premiss gives a derivation of A(z/x), F =>
C, where z is not free in F, C. By Lemma 4.1.2 we obtain a derivation with the
same height of A(y/x), F =» C. QED.

   We can now prove that contraction is admissible and height-preserving in G3i:

Theorem 4.2.4: Height-preserving contraction for G3i.

   / / \-n D,D,   F =» C, ^ n K D , T 4 C.

Proof: Continuing the proof of admissibility for G3ip, Theorem 2.4.1, with n > 0
and D = WxA principal, we have as the last step


                                VJCA,VJCA,F => C

and this is transformed into

                                                          -Ind
                               A(t/x),WxA,V
72                    STRUCTURAL PROOF THEORY

With D = 3xA as principal formula, we have as the last step
                                  A(y/x), 3xA,F =^C
                                   3xA,3xA,V =^C L3
where y is not free in F, C By Lemma 4.2.3, we have the derivation

                               A(y/x),3xA,V=*C
                                                        I

                                  A(y/x\ T^C
                                                   L3
                                          rc
QED.

Theorem 4.2.5: The rule of cut is admissible in G3i.

Proof: Continuing the proof of admissibility of cut for G3ip with its numbering
of cases, Theorem 2.4.3, we have to consider only the case that neither premiss
is an axiom. There are three such cases:

3. The cut formula is not principal in the left premiss. There are two additional
subcases:
3.4. The left premiss has been concluded by LV. Then F = Wx A, Tf and we have
the derivation

                   A(t/x),VxA,Vf      => D
                                              LV
                        VJCA, r    => D            D, A =» C
                                                                 Cut
                                          r A c
This is transformed into

                     A(t/x),   VJCA, F r =» D      D,T ^     C
                                          f
                           A(t/x),VxA,F ,       A ^C
                                                        LV
                                VXA, r, A =^ c

3.5. If the left premiss has been concluded by the L3 rule, F = 3xA, Ff and we
have
                      A(y/x), r => D
                       3xA, r =^ D LB D, A =^ C


The cut cannot simply be permuted with L 3 as it can bring in formulas that do not
meet the variable restriction necessary for the application of L3, and a variable
substitution has to be performed first. Let z be a fresh variable. We have the
                                THE QUANTIFIERS                                    73

derivation, where the left premiss is derivable by Lemma 4.1.2,

                         A(z/x), r => D        D, A =» C
                                                                   Cut
                                A(z/x), r , A => c

4. If D is principal in the left premiss only, the derivation is transformed accord-
ing to the last rule in the derivation of the right premiss. There are four additional
subcases with quantifier rules:
4.7. LV, and A = VxA, A'. The derivation

                                  D, A(f/jt),VjcA, A'=^C
                                                                 Cut
                                     rA^c
is transformed into

                      r => Z)     Z), A(f/jt), VJCA, A7 =^ C
                            A(r/x),V;cA,r, A ; ^ C
                                      , r, A; =» c
4.8. L3, and A = 3xA, A'. We have

                                D, A(y/x), A' => C
                         T => D        , , ^
                             3xA,F, A'^C
Let z be a fresh variable. Using Lemma 4.1.2, we obtain the derivation

                         r => D      D, A(z/x), Af =» C
                                A(Z/JC), r , Ar ^   c              Cwr

                                                        L3


4.9. RV and C = VxA. We have the derivation

                                       P , A => A(y/JC)
                           r => D       D, A =^ VxA
                                                             c



By substituting a fresh variable z, we obtain by Lemma 4.1.2:

                           T ^ D D, A ^             A(z/x)
                                                             -Cwr
                               r, A =»
                                   T, A ^ VxA
74                    STRUCTURAL PROOF THEORY

4.10. R3, and C = 3xA. The derivation
                                    D, A =» A(f/jc)
                         r =* D      D, A =» x        *3
                                                    Cut
                                r , A => 3xA

is transformed into

                         r => D D, A =
                             r, A = ( / )
                              r, A' 3 A
5. If D is principal in both premisses, we have two additional subcases:
5.4. WxA is principal in both premisses, and we have the derivation
                  T =• A(y/x)        A(t/x), VJCA, A =^ C
                                                                 LV
                                               ,A ^ C
                                F , A =>• C                Cut


By Lemma 4.1.2, F =>• A(t/x) is derivable with the same height as the premiss
of the left branch F =>• A(y/x), and we transform the derivation into
                             F => VxA      A(*/JC), VxA, A => C
                                     A(t/x), F, A =^ C
                            r, F, A => c

5.5. Finally, we have the case of 3x A principal in both premisses:
                                               ), A = > C


                                  r, A =^c
Again, A(t/x), A =>• C is derivable with the same height as A(y/x),   A =>• C,
and we transform the derivation into

                       F =^ A(t/x)      A(t/x), A =^ C

QED.

(b) Admissibility of structural rules for G3c: The proofs extend those for the
propositional calculus in Chapter 3. We indicate only the differences with the
proofs for G3i and additions to those for G3cp.

Lemma 4.2.6: Sequents of the form C, F =>• A, C are derivable in G3c.
                               THE QUANTIFIERS                                      75

Proof: Similar to the proof of Lemma 4.2.1. QED.

Theorem 4.2.7: Height-preserving weakening for G3c.
  / / \ - n r =>• A, then hn D,T =» A. / / h n T=• A, then \-n T =» A, D.

Proof: Similar to the proof of Theorem 4.2.2. QED.

  In order to prove contraction admissible in G3c, we need the analogue of
Lemma 4.2.3, concerning invertibility of L3, plus invertibility of RW. The for-
mer is used, as in the intuitionistic calculus, in the proof of admissibility of left
contraction, the latter of right contraction.

Lemma 4.2.8: Height-preserving inversion of L3 and RV for G3c.
  (i) / / \~n 3xA, r =» A, then \~n A(y/x), V => A.
  (ii) / / \-n r =• A, VxA, then hn V =• A, A(;y/jt).

Proof: The proof of (i) is similar to that of Lemma 4.2.3, by induction on n. The
proof of (ii) is symmetric to the proof of (i). QED.

Theorem 4.2.9: Height-preserving contraction for G3c.
  (i) / / hn £>, D, T =» A, then hn D, F => A.
  (ii) / / \-n r =» A, D, D,

Proof: The proof extends the proof for G3cp by considering the new cases arising
from the addition of the quantifier rules, as in Theorem 4.2.4. The only essentially
new case is the one for right contraction in which the contraction formula is Wx A
and this is principal in the last rule used in the derivation. This case is taken care
of by the inversion lemma for RV. QED.

Theorem 4.2.10: The rule of cut

                            F=>A,D         p, r=> A'
                                                        -Cut
                                  r,r=^ A, A7
is admissible in G3c.

Proof: The proof is an extension of the proof for G3cp, similar to the proof for
G3i. The only new case to be considered is the one in which the cut formula is
not principal in the last rule used in the derivation of the left premiss, and this is a
right rule with variable restrictions, i.e., RV. This situation is treated as the case
in which the last rule used to derive the left premiss is L3: first, the free variable
of the active formula is substituted by a fresh variable, by use of the substitution
lemma, then cut is permuted to the premiss of the left premiss, and finally rule
RV is applied. QED.
76                     STRUCTURAL PROOF THEORY

4.3. APPLICATIONS OF CUT ELIMINATION

As applications of cut elimination, we conclude subformula properties and the
existence property and underivability results for G3i.

(a) Subformula property and existence property for intuitionistic deriva-
tions: The notion of subformulas for predicate logic has to be independent of the
particular choice of bound variables and substitution instances:

Definition 4.3.1: A(t/x) is a subformula ofixA   and 3xAfor all terms t.

By inspecting the respective rules, we obtain from the admissibility of cut,
Theorem 4.2.5, the subformula property for G3i and G3c:

Corollary 4.3.2: All formulas in the derivation ofF=$C        in G3i (of T => A in
G3c) are subformulas of T, C (of T, A).

As a consequence of the subformula property, we obtain underivability of the
sequent => _L in the systems G3i and G3c; therefore we have:

Corollary 4.3.3: The systems G3i and G3c are consistent.

Since in a cut-free derivation of =$3xA in G3i the last rule must be R3, we
obtain the existence property of intuitionistic predicate logic:

Corollary 4.3.4: If =^3xA is derivable in G3i, then =$A(t/x) is derivable for
some term t.

In G3c, instead, =>3xA can be concluded from =^3xA, A(t/x), and there is no
existence property. In case A is quantifier-free, a weaker result than Corollary
4.3.4 can be obtained: If =^3xA is derivable in G3c, there are terms t\,..., tn
such that =$A(t\/x) V . . . v A(tn/x) is derivable. By the subformula property,
the derivation uses only propositional logic. The formula A(t\/x) v . . . v A(tn/x)
is called the Herbrand disjunction of 3xA. This result follows from a more
general result to be given in Section 6.6.

(b) Underivability results for intuitionistic predicate logic: We show for intu-
itionistic logic that existence is not definable in terms of the universal quantifier,
that Glivenko's theorem does not extend to predicate logic, and that there is no
prenex normal form for formulas contrary to classical predicate logic.

Theorem 4.3.5: The sequent =>• ~ Vx ~ A D 3xA is not derivable in G3i.

Proof: We show that a root-first proof search for a derivation of the sequent
goes on forever. The last two steps in root-first order must be RD,LD or RD,R3.
In the second case the continuation can only be LD, so we have search trees
                                     THE QUANTIFIERS                                        77

beginning with


                                                                                      Ait/x) ^
                                                                           A(t/x)
                                                                                      R3
                                                      —•?        VX   /\   —) ~^Xi\


The second search succeeds only if the first one does, and the first one has two
continuations, with LD and Ri. Continuation with LD leads to a loop since it
reproduces the conclusion in its first premiss. Therefore we continue with RW,
which gives the premiss ~ VJC ~ A =$> ~A(y/x). Continuation with LD gives
again a loop, and the same pattern repeats itself. What remains is the search tree:


          r^j   W Y   ^^
                           A, A(y/x), A(z/x) =^ _L

                              , A(y/x) => Wx ~A ^V           ±,A(y/x)=>±
                                                            RD
                                                 A(y/x)
                                                VJC   A       ±            > 3JCA




Each time LD is applied, its left premiss must be the conclusion of Ri since
LD would give a loop. The only remaining search tree never terminates but
produces, by the variable restriction in rule Ri, ever-longer sequents
-VJC ~ A, A(y/x), A(z/x),...   ^ _L to be derived. QED.

   In Chapter 5, Theorem 5.4.9, we prove Glivenko's theorem that states that if a
negative formula of propositional logic is derivable classically, it is also derivable
intuitionistically. A corresponding result for predicate logic fails, as is shown
through a sequent that is easily derived in G3c but underivable in G3i:

Theorem 4.3.6: => — VJC(AV —A) is not derivable in G3i.

Proof: We prove underivability for an atom P(x) by showing that looping caused
by rule LD and variable restrictions produce an infinite derivation. The last two
steps must be
           - (VJC(P(JC)V - P(x))) => Vx(P(x)v             - P(x))     _L =• _L
78                      STRUCTURAL PROOF THEORY

If LD is used, its left premiss will reproduce the left topsequent. Therefore
we continue by RV, which gives as the premiss ~(VJC(P(JC)V ~ P(x))) =>•
P(y)v ~ P(y). As before, the next rule cannot be LD, so it is one of the Rv
rules. The first Rv rule leaves the atom P(x) in the succedent so from there the
continuation would have to be from the antecedent, by LD, but this is forbid-
den by looping. Therefore only the second Rv rule remains, with ~ P(x) in the
succedent. Now continuation is possible through RD, and we have the search
tree


                '(Vx(P(x)v ~P(x))), P(v) =k -L
                                              RD
                                         P(y)
                                                               Rw
           ~(VJC(P(JC)V ~ P ( J C ) ) ) => P(y)v   ~ P(y)
           (VJC(P(JC)V ~P(x)))      => Vx(P(x)v ~P(x)) ™ J_ =» -L
                          ~(VJC(P(JC)V ~ P ( J C ) ) ) =^ _L




Proof search now goes on exactly as from the second line from root, except for
the addition of the atom P(y) in the antecedent. When we arrive at applying
RV for the second time root-first, since the antecedent has y free, a variable z
distinct from y has to be chosen, which leads in two more steps to the sequent
^(Wx(P(x)v ~P(x))), P(y), P(z) => -L. Continuing again as from the second
line from root, but with also P(z) added in the antecedent, proof search produces
a third formula P(v) in the antecedent, with v / v, z, with no end. QED.

   A formula is in prenex normal form if it has a string of quantifiers followed
by a formula with only propositional connectives. In classical logic, all formulas
can be brought to an equivalent prenex normal form, but in intuitionistic logic,
this is not so:

Theorem 4.3.7: The following sequents, with x not free in A, are not derivable
in G3i:
     (i) =^Vx(Av B)D       AWxB,
     (ii) 4 ( A D 3xB) D 3x(A D B),
     (iii) =>(VxB D A)D 3x(B D A).

Proof: We show that the sequents are not derivable when A and B are atoms P
and Q(x).
  For (i), assume that there is a derivation of =>V;t(P v Q(x))DP V VxQ(x).
The last step isRD, and therefore Wx(P v Q(x)) =^P vWxQ(x) is derivable.
                              THE QUANTIFIERS                                   79

Since there is no implication in this sequent, in any of its derivations only formulas
of the forms Vx(P v <2(x)), P v Q(t), P, Q(t) can appear in antecedents and
formulas of the forms P V VJK Q(x), P, Vx Q(x), Q{y) in succedents. Further, top-
sequents can be only of the forms P, F =$> P or <2(jX T =>• <2(j). We show that
every proof search leads to a branch that cannot have an axiom of these two forms
as topsequent.
   A sequent is a nonaxiom in the derivation of (i) if: 1. Whenever P is a sub-
formula of the succedent, P is not in the antecedent, or 2. For any y, whenever
Q(y) is the succedent, Q(y) is not in the antecedent.
   We now define a branch such that all of its sequents are nonaxioms, from which
underivability of sequent (i) follows. Note that the only branchings that can appear
are due to rule Lv, with principal formula P v Q(t). If the succedent contains P
as subformula, we choose the premiss with Q(t), and if not, we choose the premiss
with P . The proof that all sequents in the branch so defined are nonaxioms is by
induction on length of the branch. There are four cases that depend on the prin-
cipal formula of an inference:
    1. Vx(P v Q(x)) in antecedent: The active formula in the premiss is P V Q(x)
so that if the conclusion is a nonaxiom the premiss also is.
   2. P V Q(x) in antecedent: If the succedent has P as subformula the chosen
branch has Q(x) in the premiss and the property of being a nonaxiom is preserved.
Else premiss with P is chosen and being a nonaxiom is preserved.
   3. P V Wx Q(x) in succedent: Since the conclusion is a nonaxiom, P is not in
the antecedent so having P or Wx Q(x) in the succedent of the premiss preserves
being a nonaxiom.
   4. VxQ(x) in the succedent: If Q(y) is in the antecedent, by the variable
restriction in PV the premiss contains in the succedent Q(z) with z / y so the
property of being a nonaxiom is preserved.
   For (ii), we attempt a proof search of the sequent for atoms P and Q(x). The last
step is RD, the one above it either LD or R3. The former gives as the left premiss
P D 3xQ(x) => P , but this is underivable since only LD applies and it gives a
loop. So the next-to-last step is R3 and the premiss is P D 3x Q{x) =+> P D Q(t)
for some term t. Again, LD would produce a loop, and the only remaining search
tree is



                 P D 3xQ(x), P => P   SxQjx), P => Q(t)
                                          Q(t)
                         P D3xQ(x)^    P D Q(t)-RD
                       PD3xQ(x)^3x(PD        Q(x))R3
                      => P D 3xQ(x) D 3x(P D Q(x))
80                     STRUCTURAL PROOF THEORY

The sequent Q(y), P =$> Q(t) is not an axiom since, by the variable restriction in
L3, we must have t ^ y.
  The proof of (iii) is similar to that of (ii). QED.

   Derivations of sequents containing only formulas in prenex normal form can be
turned into derivations in which the propositional rules precede all the quantifier
rules. In the system G3c this result, called the midsequent theorem, can be stated
as follows:

 Theorem 4.3.8: If F =>> A is derivable in G3c and F, A have all formulas in
prenex normal form, the derivation has a midsequent V =>> A' such that all in-
ferences up to the midsequent are propositional and all inferences after it quan-
 tificationai
Proof: For each derivation and each instance of a quantifier rule Q in it, con-
sider the number n(Q) of applications of propositional rules that are below the
quantifier rule in the derivation, and let n be the sum of the n(Q) for all the
applications of quantifier rules. We show by induction on n that every deriva-
tion can be transformed into a derivation in which n is zero. If n = 0, there is
nothing to prove. If n > 0, we consider the downmost application of a quantifier
rule with a propositional rule Prop immediately below it. There are several cases,
all dealt with similarly, and we consider the case in which the quantifier rule is
L3 and the propositional rule has one premiss. We have the following steps of
derivation:

                               A(y/x), F" =» A"
                                                  Prop
                                     ©=> A
Since by hypothesis the endsequent of the derivation consists of prenex formulas
only, by the subformula property all the sequents in the derivation consist of
prenex formulas only. Therefore 3xA cannot be active in the propositional rule,
for otherwise 0 would contain a formula of the form B o 3x A or 3x A o B that
is not in prenex form. Thus 0 = 3xA, T'" and the two steps of derivation can be
permuted as follows:
                               A(y/x), F" => A"
                                                    Prop
                               A(y/x),   T"r => A
                                                    L3


The variable restrictions are satisfied since the propositional rules do not alter the
variable binding. By inductive hypothesis the derivation of A(y/x), Y" =>• A"
can be transformed into one that satisfies the midsequent theorem, and all the
inferences below the steps considered are quantificational. QED.
                                 THE QUANTIFIERS                                    81


4.4.    COMPLETENESS OF CLASSICAL PREDICATE LOGIC

We shall give a proof of completeness for pure classical predicate logic, where
pure means that the language contains no functions or constants. A denumerable
set of variables x\, jt2, • • • ordered by the indices is needed in the proof. The notion
of a valuation for formulas of classical predicate logic is defined as an extension
of the definition for classical propositional logic:

Definition 4.4.1: A valuation is a function v from formulas of predicate logic to
the values 0 and 1, assumed to be given for all atoms,

   v(Pn{Xi, . . . , jc,-)) - 0 or v(Pn(xt, . . . , xj)) = 1,

and extended inductively to all formulas,

   v(±) = 0,
   V(ASLB)    = min(v(A),
   v(A V B) = max(v(A),
   v(A D B) = max{\ - v(A),
   vQ/xA) = inf{v{A(Xilx))\
   v(3xA) = sup(v(A(Xi/x))).
The infimum is taken over the denumerable sequence of values v(A(xt/x)) for
JCI, Jt2, • • •, and similarly for the supremum. These two classical valuations are
in general infinitary, and no method of actually computing values is assumed.
As in Section 3.3, we extend valuations to contexts by taking conjunctions and
disjunctions of their formulas and by setting v/\(T) = min(v(C)) for formulas C
in r and i;\f(F) = max(v(C)) for formulas C in I\

Definition 4.4.2: A sequent T =>• A is refutable if there is a valuation v such that
v/\(T)> t>\/(A). A sequent F =>> A is valid if it is not refutable.

A valuation showing refutability is called a refuting valuation. A sequent F =>• A
is valid if for all valuations v, v/\(T) ^ v\/(A). We now prove soundness of
the sequent calculus G3c for classical predicate logic, continuing the proof of
Theorem 3.3.5:

Theorem 4.4.3: If a sequent F =>• A is derivable in G3cp, it is valid.

Proof: Assume that F =^> A is derivable. We prove by induction on height of
derivation that it is valid. The new cases to consider are when the last rule in the
derivation is a quantifier rule. If the last rule is LV, suppose

       min(v(A{y/x)\ vQ/xA), u(A(H)) ^ v\J(A)
82                      STRUCTURAL PROOF THEORY

and show that

     min(v(VxA),v(/\(r)))^v\/(A).

This follows by v(Vx A) ^ v(A(y/x)).    If the last rule is RW, we have, by inductive
hypothesis,

     v/\(F) ^ max{v\J(A\ v(A(y/x))).

Since y does not occur in F, this implies

     v/\(V) ^ infy(max(v\J(A), v(A(y/x)))\

and since y does not occur in A,

     v/\(F) ^ max(v\/(A), infy{v(A{y/x)))\

that is,

     v/\(F) ^ max(v\/(A), v(VxA)).

The cases of L3 and R3 are symmetric to RW and LV, respectively. QED.

    The main idea of the completeness proof for the system G3c of classical
predicate logic is the following: Given a sequent F ^ Awe construct, by applying
root-first the rules G3c in all possible ways, a tree, called a reduction tree for
F =>> A. If all branches reach the form of an axiom or conclusion of L_L, the tree
gives a proof of the given sequent. Otherwise, we prove by classical reasoning
that the construction does not terminate. By Konig's lemma, a nonconstructive
result for infinite trees recalled below, the tree has an infinite branch. Given such
an infinite branch, we define a refuting valuation for the sequent.
    We remark that the procedure that follows gives as a special case the com-
pleteness proof for the calculus G3cp; as in the propositional case the procedure
of construction of the reduction tree reduces to a finite one. In the first-order case
instead, we cannot know in general if the tree terminates or goes on forever, and
no decision method is obtained.
    The following property of trees will be necessary in the proof of Lemma 4.4.3.
Its proof is nonconstructive, and we shall not give it.

 Lemma 4.4.4: Konig's lemma. Every infinite, finitely branching tree has an in-
finite branch.

Theorem 4.4.5: Any sequent T =^ A either has a proof in G3c or there is a
refuting valuation for the sequent.

Proof: The proof consists of two parts. In the first part we define for each sequent
a reduction tree that gives a proof when finite. In the second part we show that an
infinite tree gives a refuting valuation.
                               THE QUANTIFIERS                                   83

1. Construction of the reduction tree: We define for each sequent T =>• A a reduc-
tion tree having T =>> A as root and a sequent at each node. The tree is constructed
inductively in stages, as follows:
   Stage 0 has V =>• A at the root of the tree. Stage n > 0 has two cases:
Case I: If every topmost sequent is an axiom or conclusion of LA., the construction
of the tree ends.
Case II: If not every topmost sequent is an axiom or conclusion of L_L, we
continue the construction of the tree by writing above those topmost sequents
that are not axioms or conclusions of L_L other sequents, which we obtain by
applying root-first the rules of G3c whenever possible, in a given order. When no
rule is applicable the topmost sequent has distinct atoms in the antecedent and
succedent and no _L in the antecedent, and the sequent is repeated. (Thus, for
propositional logic, each branch terminates or starts repeating itself identically.)
   For stages n = 1 , . . . , 10, the reduction is illustrated below. For n = 11 we
repeat stage 1, for n = 12 stage 2, and so on for each n.
   We start for n = 1 with L&: For each topmost sequent of the form



where B\&C\,..., BmScCm are all the formulas in the antecedent with conjunc-
tion as outermost logical connective, we write

                           fli,Ci,...,Bm,cw,r'=>              A

on top of it. This step corresponds to applying root first m times rule L&.
   For n = 2, we consider all the sequents of the form

                          r = ^ 5 i & C i , . . . , 5 m & C m , A'

where B\ 8cC\,..., BmScCm are all the formulas in the succedent with conjunction
as the outermost logical connective, and write on top of them the 2m sequents



where Dt is either Bt or Ct (and all possible choices are taken). This is equivalent
to applying RSc root-first consecutively with principal formulas Bi&C\, . . . ,
Bm&Cm.
   For n = 3 and 4 we consider Lv and Rv and define the reductions symmet-
rically to the cases n = 2 and n = 1, respectively.
   For n = 5, for each topmost sequent having the formulas B\ D C\,...,
Bm D Cm with implication as the outermost logical connective in the antecedent,
Fr the other formulas, and succedent A, write on top of it the 2m sequents
84                         STRUCTURAL PROOF THEORY

where i\,..., ik e {1, . . . , m] and j k + \ , . . . , jm e { 1 , . . . , m] — {i\,..., ik}. This
step (perhaps less transparent because of the double indexing) corresponds to the
root-first application of rule LD with principal formulas B\ D C\, ..., Bm D C m .
   For n = 6, we consider all the sequents having implications in the succe-
dent, say B\ D C\,..., Bm D C m , and A7 the other formulas, and write on top of
them

                             B\,...,    Bm, F =>• C i , . . . , C m , A


that is, we apply root-first m times rule RD.
   For n = 1, consider all the topsequents having universally quantified formulas
Vxi B\, . . . , Vxm Z?m in the antecedent. For / = 1 , . . . , m, let yt be the first variable
not yet used for a reduction of VJC/2?/, and write on top of these sequents the
sequents

                                                                                 ;
              S i ( y i M ) , • • •, Bm(ym/xm),   VJCISI, . . . , Vx m £ m , T       => A

that is, apply root-first rule LV with principal formulas V^i^i, . . . , WxmBm. It is
essential that the variable yt be chosen starting from the beginning of the ordered
set of variables and by excluding those variables that have already been used in
a similar reduction for Vx; Bt, as the purpose of this step of the reduction is to
obtain, sooner or later, any substitution instance of Bt.
   For n = 8, let Vxi B\,..., Wxm Bm be the universally quantified formulas occur-
ring in the succedent of a topsequent of the tree, and let Ar be the other formulas.
Let z\,..., zm be fresh variables, not yet used in the reduction tree, and write on
top of each such sequent the sequents




that is, apply root-first m times rule RV.
   For n = 9 and 10 we consider L3 and R3 and define the reduction in a way
symmetric to the cases n = 8 and n = 1, respectively.
   For each n, for sequents that are neither axioms nor conclusions of L_L, nor
treatable by the above reductions, we write the sequent itself above them.
   If the reduction tree is finite, all its leaves are axioms. We observe that the tree,
read top-down from leaves to root, gives a proof of the endsequent F =>• A.
2. Definition of the refuting valuation: If the reduction tree is infinite, by Konig's
lemma it has an infinite branch. Let F o => A o be the given sequent T =>• A
and let

                                 ro=> Ao,...,rf- = > A i 9 . . .
                               THE QUANTIFIERS                                    85

be one such branch, and consider the sets of formulas




We define a valuation in which all formulas in F have value 1 and all formulas in
A have value 0, thereby refuting the sequent F => A.
   Observe that, by definition of the reduction tree, F and A have no atomic
formulas in common. For if P is in F and A, then for some i, j , P is in F;
and Aj, but then P is in F^ and A^ for k^ i, j , contrary to the assumption that
Ffc =>> A^ is not an axiom. Consider the valuation v defined by setting v(P) = 1
for each atomic formula in F and v(P) — 0 for P in A .
   We show by induction on the weight of formulas that v(A) = 1 if A is in F
and v(A) = 0 if A is in A . Therefore v is a refuting valuation.
   If A is _L, A cannot be in F, for otherwise the infinite branch would contain
a conclusion of L_L, so A can be in only A and v(A) = 0 by the definition of a
valuation.
   If A is atomic, the claim holds by definition of the refuting valuation.
   If A = B&C is in F, there exists / such that A e F/, and therefore B, C are
in Tf+k for some k^O. By inductive hypothesis, v(B) = 1 and v(C) = 1, so
v(B&C) = 1.
   If A = B&C is in A , consider the step / in which the reduction for A applies.
This gives a branching, and one of the two branches belongs to the infinite branch,
so either B or C is in A , and therefore by inductive hypothesis v(B) = 0 or
v(C) = 0, and therefore v(B&C) = 0 is satisfied.
   If A = B v C is in F, we reason similarly to the case of A = B&C in A . If
A = B V C is in A , we argue as with A = B&C in F.
   If A = B D C is in F, then either B e A or C e F. By inductive hypoth-
esis, in the former case v(B) = 0 and in the latter v(C) = 1, so in both cases
v(B D C)= 1.
   If A = B D C is in A , then for some i, B e F; and C e Ai9 so by inductive
hypothesis v(B) = 1 and v(C) = 0, so v(B D C ) = 0.
   If A = VxB is in F, let / be the least index such that A occurs in F,. Any
substitution instance B(y/x) occurs sooner or later in F 7 for j ^ /, so by inductive
hypothesis v(B(y/x)) = 1 for all y, and therefore v(VxB) = 1.
   If A = WxB is in A , consider the step at which the reduction applies to A.
At this step we have, for some z and some j , B(z/x) e A 7 , and therefore by
inductive hypothesis v(B(z/x)) = 0, so v(VxB) = 0.
   The cases of A = 3xB in F and A = 3xB in A are symmetric to the cases of
A = WxB in A and of A = VxB in F, respectively. QED.

By the theorem, we conclude:
86                       STRUCTURAL PROOF THEORY

Corollary 4.4.6: If a sequent T =>• A is valid, it is derivable in G3c.


NOTES TO CHAPTER 4

Our general elimination rule for the universal quantifier is presented in von Plato
(1998). It follows the pattern of general elimination rules as determined by the inver-
sion principle of Section 1.2.
    The calculus G3i is a single succedent version of Dragalin's (1988) contraction-
free intuitionistic calculus, first given in Troelstra and Schwichtenberg (1996). The
calculus G3c is the standard contraction-free classical calculus. The syntactic proofs
of underivability in Section 4.3 follow Kleene (1952).
    Our completeness proof for G3c uses valuations as a continuation of the proof for
propositional logic in Theorem 3.3.6. This is suggested, although not carried out in
detail, in Ketonen (1941). His result is mentioned in the introduction to Szabo's 1969
edition of Gentzen's papers (p. 7). The construction of the refutation tree is carried out
in Schutte (1956). In Takeuti (1987), whose exposition we closely follow, Schiitte's
method is applied to Gentzen's original calculus LK. For the use of Konig's lemma
in the completeness proof, see Beth (1959, p. 195).
                       Variants of Sequent Calculi




In this chapter we present different formulations of sequent calculi. In Sections
5.1 and 5.2 we give calculi with independent contexts in two versions, one with
explicit rules of weakening and contraction, the other with these rules built into
the logical rules similarly to natural deduction. The proofs of cut elimination for
these calculi are quite different from each other and from the earlier proofs for the
G3 calculi. For calculi of the second type in particular, with implicit weakening
and contraction, cut elimination will be limited to cut formulas that are principal
somewhere in the derivation of the right premiss of cut. All other cut formulas
are shown to be subformulas of the conclusion already.
   The structure of derivations in calculi with independent contexts is closely
connected to the structure of derivations in natural deduction. The correspondence
will be studied in Chapter 8.
   In Section 5.3 we present an intuitionistic multisuccedent calculus and its basic
properties. The calculus has a right disjunction rule that is invertible, which is
very useful in proof search. The calculus is also used in the study of extensions
of logical sequent calculi with mathematical axioms in Chapter 6.
   We also present a single succedent calculus for classical propositional logic. Its
main advantage compared with the multisuccedent calculus G3cp is that it has an
operational interpretation and a straightforward translation to natural deduction.
The calculus is obtained from the intuitionistic calculus G3ip by the addition
of a sequent calculus rule corresponding to the law of excluded middle. The
propositional part, from this point of view, amounts to an intuitionistic calculus
for theories with decidable basic relations.
   In the last section, we present a calculus for intuitionistic propositional logic,
called G4ip, with the property that proof search terminates.


