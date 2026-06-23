# Basic Proof Theory — Chapter 1: Introduction (lines 316-1829)

Chapter 1

Introduction

Proof theory may be roughly divided into two parts: structural proof theory
and interpretational proof theory. Structural proof theory is based on a com-
binatorial analysis of the structure of formal proofs; the central methods are
cut elimination and normalization.
  In interpretational proof theory, the tools are (often semantically moti-
vated) syntactical translations of one formal theory into another. We shall
encounter examples of such translations in this book, such as the Gödel-
Gentzen embedding of classical logic into minimal logic (2.3), and the modal
embedding of intuitionistic logic into the modal logic S4 (9.2). Other well-
known examples from the literature are the formalized version of Kleene's
realizability for intuitionistic arithmetic and Gödel's Dialectica interpretation
(see, for example, Troelstra [1973]).
  The present text is concerned with the more basic parts of structural proof
theory. In the first part of this text (chapters 2-7) we study several formal-
izations of standard logics. "Standard logics", in this text, means minimal,
intuitionistic and classical first-order predicate logic. Chapter 8 describes
the connection between cartesian closed categories and minimal conjunction-
implication logic; this serves as an example of the applications of proof theory
in category theory. Chapter 9 illustrates the extension to other logics (namely
the modal logic S4 and linear logic) of the techniques introduced before in
the study of standard logics. The final two chapters deal with first-order
arithmetic and second-order logic respectively.
   The first section of this chapter contains notational conventions and def-
initions, to be consulted only when needed, so a quick scan of the contents
will suffice to begin with. The second section presents a concise introduction
to simple type theory, with rigid typing; the parallel between (extensions of)
simple type theory and systems of natural deduction, under the catch-phrase
 "formulas-as-types", is an important theme in the sequel. Then follows a
brief informal introduction to the three principal types of formalism we shall
encounter later on, the N-, H- and G-systems, or Natural deduction, Hilbert
systems, and Gentzen systems respectively. Formal definitions of these sys-
tems will be given in chapters 2 and 3.
                                        1
2                                                        Chapter I. Introduction

1.1      Preliminaries
The material in this section consists primarily of definitions and notational
conventions, and may be skipped until needed.
   Some very general abbreviations are "iff" for "if and only if" , "IH" for "in-
duction hypothesis", "w.l.o.g." for "without loss of generality". To indicate
literal identity of two expressions, we use E. (In dealing with expressions
with bound variables, this is taken to be literal identity modulo renaming of
bound variables; see 1.1.2 below.)
   The symbol E is used to mark the end of proofs, definitions, stipulations
of notational conventions.
   IN is used for the natural numbers, zero included. Set-theoretic notations
such as E, C are standard.


1.1.1. The language of first-order predicate logic
The standard language considered contains V, A, -4,1, V, 3 as primitive logi-
cal operators (± being the degenerate case of a zero-place logical operator, i.e.
a logical constant), countably infinite supplies of individual variables, n-place
relation symbols for all n E IN, symbols for n-ary functions for all n E IN.
0-place relation symbols are also called proposition letters or proposition vari-
ables; 0-argument function symbols are also called (individual) constants.
The language will not, unless stated otherwise, contain = as a primitive.
    Atomic formulas are formulas of the form Rti        tn, R a relation symbol,
t1,    ,t,, individival terms, 1 is not regarded as atomic. For formulas which
are either atomic or I_ we use the term prime formula
    We use certain categories of letters, possibly with sub- or superscripts or
primed, as metavariables for certain syntactical categories (locally different
conventions may be introduced):

      x, y, z, u, y, w for individual variables;

      f, g,h for arbitrary function symbols;

      c, d for individual constants;

      t,s,r for arbitrary terms;

      P,Q for atomic formulas;

      R for relation symbols of the language;

      A, B,C,D,E,F for arbitrary formulas in the language.
1.1. Preliminaries                                                               3

NOTATION. For the countable set of proposition variables we write 'PV . We
introduce abbreviations:
        A      B :=(A+ B) A (B * A),
                 := A * 1,
        T
 In this text, T ("truth" ) is sometimes added as a primitive. If F is a finite
sequence A1,      , An of formulas, A F is the iterated conjunction (... (A1 A

A2) A .A), and V F the iterated disjunction (... (A1 V A2) V ... An). If I'
is empty, we identify V r with 1, and A r with T.

NOTATION. (Saving on parentheses) In writing formulas we save on paren-
theses by assuming that V, ], bind more strongly than V, A, and that in
turn V, A bind more strongly than -4,   Outermost parentheses are also
usually dropped. Thus A A B + C is read as ((A A (B))                  C). In the
case of iterated implications we sometimes use the short notation

    Ai -4 A2      .   .   . An_1 + An   for   Ai > (A2 +   (An_i     An) ...).
We also save on parentheses by writing e.g. Rxyz, Rt0t1t2 instead of R(x, y, z),
R(to, ti, t2), where R is some predicate letter. Similarly for a unary function
symbol with a (typographically) simple argument, so f x for f (x), etc. In this
case no confusion will arise. But readability requires that we write in full
R(f x,gy,hz), instead of Rf xgyhz.

1.1.2. Substitution, free and bound variables
Expressions ', E' which differ only in the names of bound variables will be
regarded by us as identical. This is sometimes expressed by saying that E
and E' are a-equivalent. In other words, we are only interested in certain
equivalence classes of (the concrete representations of) expressions, expres-
sions "modulo renaming of bound variables". There are methods of finding
unique representatives for such equivalence classes, for example the namefree
terms of de Bruijn [1972]. See also Barendregt [1984, Appendix C.
   For the human reader such representations are less convenient, so we shall
stick to the use of bound variables. But it should be realized that the issues of
handling bound variables, renaming procedures and substitution are essential
and non-trivial when it comes to implementing algorithms.
   In the definition of "substitution of expression E' for variable x in expression
C", either one requires that no variable free in E'' becomes bound by a variable-
binding operator in ', when the free occurrences of x are replaced by E' (also
expressed by saying that there must be no "clashes of variables"), "E' is free
for x in C", or the substitution operation is taken to involve a systematic
renaming operation for the bound variables, avoiding clashes. Having stated
4                                                         Chapter 1. Introduction

that we are only interested in expressions modulo renaming bound variables,
we can without loss of generality assume that substitution is always possible.
  Also, it is never a real restriction to assume that distinct quantifier occur-
rences are followed by distinct variables, and that the sets of bound and free
variables of a formula are disjoint.

NOTATION. "FV" is used for the (set of) free variables of an expression; so
FV(t) is the set of variables free in the term t, FV(A) the set of variables free
in formula A etc.
   E[x It] denotes the result of substituting the term t for the variable x in the
expression E. Similarly, E[X7r] is the result of simultaneously substituting
the terms E = t1,... , tn for the variables X' x1,... , xn respectively.
   For substitutions of predicates for predicate variables (predicate symbols)
we use essentially the same notational conventions. If in a formula A, con-
taining an n-ary relation variable Xn, Xn is to be replaced by a formula
B, seen as an n-ary predicate of n of its variables X' = x1,.. , xn, we write
A[Xn Pd'.13] for the formula which is obtained from A by replacing every
occurrence Xnr by Brij] (neither individual variables nor relation variables
of Vi B are allowed to become bound when substituting).
   Note that B may contain other free variables besides X', and that the "AX"
is needed to indicate which terms are substituted for which variables.
   Locally we shall adopt the following convention. In an argument, once a
formula has been introduced as A(x), i.e., A with a designated free variable
x, we write A(t) for A[x It], and similarly with more variables.            N


1.1.3. Subformulas
DEFINITION. (Gentzen subformula) Unless stated otherwise, the notion of
subformula we use will be that of a subformula in the sense of Gentzen.
(Gentzen) subformulas of A are defined by

      A is a subformula of A;

      if B o C is a subformula of A then so are B, C, for o = V, A, -->;

      if VxB or 3xB is a subformula of A, then so is B[xlt], for all t free for
      x in B.

If we replace the fhird clause by:

(iii)' if VxB or 3xB is a subformula of A then so is B,

we obtain the notion of literal subformula.
1.1. Preliminaries                                                                 5

DEFINITION. The notions of positive, negative, strictly positive subformula
are defined in a similar style:

        A is a positive and a stricly positive subformula of itself;
        if B A C or B V C is a positive [negative, strictly positive] subformula
        of A, then so are B, C;
        if VxB or 3xB is a positive [negative, strictly positive] subformula of A,
        then so is B[xIt] for any t free for x in B;
        if B C is a positive [negative] subformula of A, then B is a negative
        [positive] subformula of A, and C is a positive [negative] subformula of
        A;

 (IT)   if B + C is a strictly positive subformula of A then so is C.

A strictly positive subformula of A is also called a strictly positive part (s.p.p.)
of A. Note that the set of subformulas of A is the union of the positive and
the negative subformulas of A.
  Literal positive, negative, strictly positive subformulas may be defined in
the obvious way by restricting the clause for quantifiers.

EXAMPLE. (P --+ Q)          R V VxR' (x) has as s.p.p.'s the whole formula,
R V VxR/ (x), R,VxR'(x), R' (t). The positive subformulas are the s.p.p.'s and
in addition P; the negative subformulas are P > Q, Q.

1.1.4. Contexts and formula occurrences
Formula occurrences (f.o. 's) will play an even more important role than the
formulas themselves. An f.o. is nothing but a formula with a position in
another structure (prooftree, sequent, a larger formula etc.). If no confusion
is to be feared, we shall permit ourselves a certain "abus de langage" and talk
about formulas when really f.o.'s are meant.
   The notion of a (sub)formula occurrence in a formula or sequent is intu-
itively obvious, but for formal proofs of metamathematical properties it is
sometimes necessary to use a rigorous formal definition. This may be given
via the notion of a context. Roughly speaking, a context is nothing but a for-
mula with an occurrence of a special propositional variable, a "placeholder".
Alternatively, a context is sometimes described as a formula with a hole in it.

DEFINITION. We define positive (P) and negative (formula-)contexts (Ar)
simultaneously by an inductive definition given by the three clauses (i)(iii)
below. The symbol "*" in clause (i) functions as a special proposition letter
(not in the language of predicate logic), a placeholder so to speak.
6                                                         Chapter I. Introduction

       * E P;
and if B+ E P, B- E Ar, and A is any formula, then
       AAB+ , B+ AA, AVB+, B+V A, A-43+,                     Vx.B+ ,   x.B+ E P;
       AAB-, .13- AA, AVB-, B-V A, A>B-, B+-+A,Vx13- ,3xI3- E N.
The set of formula contexts is the union of P and Ar. Note that a context
contains always only a single occurrence of *. We may think of a context as
a formula in the language extended by *, in 'which * occurs only once. In a
positive [negative] context, * is a positive [negative] subformula. Below we
give a formal definition of (sub)formula occurrence via the notion of context.
  For arbitrary contexts we sometimes write FH, GH,              . Then F[A],

G[A], ... are the formulas obtained by replacing * by A (literally, without
renaming variables).
  The notion of context may be generalized to a context with several place-
holders *1,    , *n, which are treated as extra proposition variables, each of
which may occur only once in the context.
  The strictly positive contexts SP are defined by
       * E S'P; and if B E SP, then
       A A B,B A A, A V B,B V A, A > B,VxB, 3xB E SP.
An alternative style of presentation of this definition is
    P=*1AAPI 'P A AI AVP ITV AIA                 P      > A VeP 3xP,
      =AAArIATAAIAVIVI.ArVAIA>Arl P --+ A IVx.N.
       = * I A A SP IS'PAA1AVS'P ISPVA I A -4 SP 1VxS'P 13xSP.
A formula occurrence (f.o. for short) in a formula B is a literal subformula
A together with a context indicating the place where A occurs (so B may be
obtained by replacing * in the context by A). In the obvious way we can now
define positive, strictly positive and negative occurrence.

1.1.5. Finite multisets
Finite multisets, i.e. "sets with multiplicity", or to put it otherwise, finite
sequences modulo the ordering, will play an important role in this text.

NOTATION. If A is a multiset, we use 1A1 for the number of its elements. For
the multiset union of F and A we write r U A or in certain situations simply
r, A or even rA (namely when writing sequents, which will be introduced
later). The notation I', A or FA then designates a multiset which is the union
of F and the singleton multiset containing only A.
1.1. Preliminaries                                                           7

  If "c" is some unary operator and F :-=_ A1,     , An is a finite multiset of

formulas, we write cF for the multiset cAl,    , cAn.

  Finite sets may be regarded as special cases of finite multisets: a multiset
where each element occurs with multiplicity one represents a finite set. For
the set underlying a multiset F, we write Set(F); this multiset contains the
formulas of F with multiplicity one.

NOTATION. We shall use the notations A r, V F also in case r is a multiset.
A r, V r are then the conjunction, respectively disjunction of F' for some
sequence F' corresponding to F. A r, vr are then well-defined modulo logical
equivalence, as long as in our logic A, V obey the laws of symmetry and
associativity.

DEFINITION. The notions of (positive, negative) formula occurrence may be
defined for sequents, i.e., expressions of the form r   A, with F, A finite
multisets, as (positive, negative) formula occurrences in the corresponding
formulas A r -4 V A.

1.1.6. Deducibility and deduction from hypotheses, conservativity
NOTATION. In our formalisms, we derive either formulas or sequents (as
introduced in the preceding definition). For sequents derived in a formalism
S we write

         SFr          or   Hs r    A,

and for formulas derived in S
         S H A or     F-5 A.

If we want to indicate that a deduction 7, derives I'       A, we can write
D Hs r A (orVHFz if S is evident).
   For formalisms based on sequents, S H A will coincide with S H         A
(sequent r A with F empty).
   If a formula A is derivable from a finite multiset r of hypotheses or as-
sumptions, we write
         F Hs A.

In systems with sequents this is equivalent to S H F         A. (N.B. In the
literature F H A is sometimes given a slightly different definition for which
the deduction theorem does not hold; cf. remark in 9.1.2. Moreover, some
authors use H instead of our sequent-arrow
   A theory is a set of sentences (closed formulas); with each formalism is
associated a theory of deducible sentences. Since for the theories associated
8                                                        Chapter 1. Introduction

with the formalisms in this book, it is always true that the set of deducible
formulas and the set of pairs {(F, A) F H A} are uniquely determined by
the theory, we shall also speak of formulas belonging to a theory, and use the
expression "A is deducible from F in a theory".
  In particular, we write

        r [-in A,    F Hi A,    F I-, A

for deducibility in our standard logical theories M, I, C respectively (cf. the
next subsection).

DEFINITION. A system S is conservative over a system S' c S, if for formulas
A in the language of S' we have that if S H A, then S' H A. For systems with
sequents, conservativity similarly means: if H F      A in S, with F    A in
the language of S', then H F    A in S'. Similarly for theories.

1.1.7. Names for theories and systems
Where we are only interested in the logics as theories, i.e. as sets of theorems,
we use M, I and C for minimal, intuitionistic and classical predicate calculus
respectively; Mp, Ip and Cp are the corresponding propositional systems. If
we are interested only in formulas constructed from a set of operators A say,
we write A-S or AS for the system S restricted to formulas with operators
from A. Thus --*A-M is M restricted to formulas in A, > only.
   On the other hand, where the notion of formal deduction is under investiga-
tion, we have to distinguish between the various formalisms characterizing the
same theory. In choosing designations, we use some mnemonic conventions:

      We use "N", "H", "G" for "Natural Deduction" , "Hilbert system"
      and "Gentzen system" respectively. "GS" (from "Gentzen-Schiitte")
      is used as a designation for a group of calculi with one-sided sequents
      (always classical).

      We use "c" for "classical" , "i" for "intuitionistic" , "m" for "minimal" ,
      "s" for "S4", "p" for "propositional", "e" for "E-logic". If p is absent,
      the system includes quantifiers. The superscript "2" is used for second-
      order systems.
      Variants may be designated by additions of extra boldface capitals,
      numbers, superscripts such as "*" etc. Thus, for example, Glc is close
      to the original sequent calculus LK of Gentzen (and Gli to Gentzen's
      LJ), G2c is a variant with weakening absorbed into the logical rules,
      G3c a system with weakening and contraction absorbed into the rules,
      GK (from Gentzen-Kleene) refers to Gentzen systems very close to the
      system G3 of Kleene, etc.
1.1. Preliminaries                                                                9

         In order to indicate several formal systems at once, without writing
         down the exhaustive list, we use the following type of abbreviation:
         S[abc] refers to Sa, Sb, Sc; S[ab][cd] refers to Sac, Sbc, Sad, Sbd,
         etc.; [mic] stands for "m, or i or c"; [mi] for "m or i"; [123] for "1,
         2 or 3", etc. In such contracted statements an obvious parallelism is
         maintained, e.g. "G[123]c satisfies A iff G[123]i satisfies B" is read as:
         "Glc (respectively G2c, G3c) satisfies A iff Gli (respectively G2i,
         G3i) satisfies B".


1.1.8. Finite trees
DEFINITION. ( Terminology for trees) Trees are partially ordered sets (X,<)
with a lowest element and all sets {y : y < x} for x E X linearly ordered.
The elements of X are called the nodes of the tree; branches are maximal
linearly ordered subsets of X (i.e. subsets which cannot be extended further).
   Trees are supposed to grow upwards; the single node at the bottom is called
the root or bottom node of the tree. If a branch of a tree is finite, it ends in a
leaf or top node of the tree. If n, m are nodes of a tree with partial ordering
   and n m, then m is a successor of n, n a predecessor of m. If n m
and there are no nodes properly between n and m, then n is an immediate
predecessor of m, and m an immediate successor of n.
  A tree is said to be k-branching (strictly k-branching), if each node has at
most k (exactly k) immediate successors.
  We also consider labelled trees, with a function assigning objects (e.g. for-
mulas) to the nodes. The terminology for trees is also applied to labelled
trees.


1.1.9. DEFINITION. The length or size of a finite tree is the number of nodes
in the tree. We write s(T) for the size of T.
   The depth (of a tree) or height (of a tree) I TI of a tree T is the maximum
length of the branches in the tree, where the length of a branch is the number
of nodes in the branch minus 1.
   The leafsize ls(T) of a tree T is the number of top nodes of the tree.    Z
For future use we note: Let T be a tree which is at most k-branching, i.e.
each node has at most k (k > 1) immediate successors. Then

           s(T) < kir1+1,     ls(T)   s(T).

For strictly 2-branching trees s(T) = 21s(T) 1.
  Formulas may also be regarded as (labelled) trees. The definitions of size
and depth specialized to formulas yield the following definition.
10                                                         Chapter 1. Introduction

DEFINITION. The depth 1A1 of a formula A is the maximum length of a
branch in its construction tree. In other words, we define recursively II = O
for atomic P, J = 0, IA o BI max(IA1,1B1) + 1 for binary operators 0,
 o AI = AI + 1 for unary operators o.
     The size or length s(A) of a formula A is the number of occurrences of logical
symbols and atomic formulas (parentheses not counted) in A: s(P) = 1 for
P atomic, s(I) = 0, s(A o B) = s(A) + s(B) + 1 for binary operators o, s(oA)
= s(A) + 1 for unary operators o.
For formulas we therefore have

           s(A) < 21A1+1.



1.2        Simple type theories
This section briefly describes typed combinatory logic and typed lambda cal-
culus, and may be skipped by readers already familiar with simple type the-
ories. For more detailed information on type theories, see Barendregt [1992],
Hindley [1997]. Below, we consider only formalisms with rigid typing, i.e.
systems where every term and all subterms of a term carry a fixed type.
Hindley [1997] deals with systems of type assignment, where untyped terms
are assigned types according to certain rules. The untyped terms may pos-
sess many different types, or no type at all. There are many parallels between
rigidly typed systems and type-assignment systems, but in the theory of type
assignment there is a host of new questions, sometimes very subtle, to study.
But theories of type assignment fall outside the scope of this book.

1.2.1. DEFINMON. (The set of simple types) The set of simple types T,
is constructed from a countable set of type variables P0, P1, P2, . . by means
                                                                      .


of a type-forming operation (function-type constructor) >. In other words,
simple types are generated by two clauses:

        type variables belong to T;
        ifA,BE7,then(A*B)ET.
A type of the form A > B is called a function type. "Generated" means that
nothing belongs to T, except on the basis of (i) and (ii). Since the types
have the form of propositional formulas, we can use the same abbreviations
in writing types as in writing formulas (cf. 1.1.1).
Intuitively, type denote special sets. We may think of the type variables
as standing for arbitrary, unspecified sets, and given types A, B, the type
A > B is a set of functions from A to B.
1.2. Simple type theories                                                           11

1.2.2.. DEFINITION. (Terms of the sim,ply typed lambda calculus )_.,) All
terms appear with a type; for terms of type A we use tA,5A,rA, possibly with
extra sub- or superscripts. The terms are generated by the following three
clauses:

      For each A E 7"._ there is a countably infinite supply of variables of
      type A; for arbitrary variables of type A we use uA, vA, wA,xA, y A ZA
      (possibly with extra sub- or superscripts);

      if tA-rB SA are terms of types A                   B, A, then App(tA', sA)B is a
      term of type B;

      if tB is a term of type B and XA a variable of type A, then (AxA.tB)A-43
      is a term of type A      B.                                           1E1




NOTATION. For App(t}"B, SA)B we usually write simply (t)"B SA)B
  There is a good deal of redundancy in the typing of terms; provided the
types of x, t, s are known, the types of (Ax.t), (ts) are known and need
not be indicated by a superscript. In general, we shall omit type-indications
whenever possible without creating confusion. When writing ts it is always
assumed that this is a meaningful application, and hence that for suitable
A, B the term t has type A* B, s type A.
   If the type of the whole term is omitted, we usually simplify (ts) by
dropping the outer parentheses and writing simply ts. The abbreviation
t1t2    tn is defined by recursion on n as (t1t2 ...tn_i)tn, i.e. t1t2 tn is
(... ((tit2)t3 )tn)
   For Axi.(Ax2.(... (Axn.t)...)) we write Ax1x2 xn.t. Application binds
more strongly than Ax., so Ax.te is Ax.(tti), not (Ax.t)e.
   A frequently used alternative notation for xA ,tB is x: A, t:B respectively.
The notations tA and t: A are used interchangeably and may occur mixed;
readability determines the choice.

EXAMPLES. n Ài:     :=      X   y .,
                                AB XA    A
                                        SA
                                             ,, C   :B
                                                         AeyA-413 zA zgy z).

1.2.3. DEFINITION. The set FV(t) of variables free in t is specified by:
           FV(xA)   := xA,
           FV(ts) := FV(t) U FV(s),
           FV(Ax.t) := FV(t)\ {x}.                                                  N


1.2.4. DEFINITION. (Substitution) The operation of substitution of a term
s for a variable x in a term t (notation t[xls]) may be defined by recursion
12                                                                     Chapter 1. Introduction

on the complexity of t, as follows.

           x[x I s]     :-= s,
           y[x Is]       := y for y x,
           (tit2)[x I s] := ti[x I s]t2[x I s],
           (Ax.t)[xI s] := Ax.t,
           (Ay.t)[xls] := Ay.t[xI s] for y # x; w.l.o.g. y 0 FV(s).

A similar definition may be given for simultaneous substitution tr

LEMMA. (Substitution lemma) If x 0 y, x                        FV(t2), then

           t[xlti][ylt2] -=- t[yltd[xlti [02]].
PROOF. By induction on the depth of t.

1.2.5. DEFINMON. (Conversion, reduction, normal form) Let T be a set
of terms, and let cony be a binary relation on T, written in infix notation:
t cony s. If t cony s, we say that t converts to s; t is called a redex or
 convertible term, and s the conversum of t. The replacement of a redex by
its conversum is called a conversion. We write t        s (t reduces in one step
to 8) if s is obtained from t by replacement of (an occurrence of) a redex
e of t by a conversum t" of t', i.e. by a single conversion. The relation
 ("properly reduces to") is the transitive closure of H and »- ("reduces to") is
the reflexive and transitive closure of       The relation - is said to be the
notion of reduction generated by cont. -<1,        are the relations converse to
         »- respectively.
   With the notion of reduction generated by cony we associate a relation on
T called conversion equality: # =conys (t iS equal by conversion to s) if there
is a sequence to,.... ,t,., with to t, tn # 3, and ti ti+1 or ti »- ti+1 for each
i, O< i < n. The subscript "cony" is usually omitted when clear from the
context.
  A term t is in normal form, or t is normal, if t does not contain a redex. t
has a normal form if there is a normal s such that t s.
     A reduction sequence is a (finite or infinite) sequence of pairs (to, 80), (t1, 50,
(t2, 52), ... with 61i an (occurrence of a) redex in ti and ti - ti+1 by conversion
of Si, for all i. This may be written as
                                      O        .51        62
                                 to       ti         t2

We often omit the ô, simply writing to »-1. t1 »-i t2
   Finite reduction sequences are partially ordered under the initial part re-
lation ("sequence o is an initial part of sequence r"); the collection of finite
reduction sequences starting from a term t forms a tree, the reduction tree
1.2. Simple type theories                                                   13

of t. The branches of this tree may be identified with the collection of all
infinite and all terminating finite reduction sequences.
  A term is strongly norm,a4izing (is SN) if its reduction tree is finite.


REMARKS.     (i) As to the terminology, in the literature on lambda calculus
and combinatory logic, writers use mostly "contraction", "contracts", "con-
tractum" , instead of "conversion", "converts", "conversum". In the lambda
calculus literature "conversion" is used for a more general notion: there t
converts to s if t and s can be shown to be equal by reduction steps (go-
ing in both directions). On the other hand, there is a tradition, deriving
from Prawitz [1965], of using "conversion" instead of "contraction" for the
corresponding notion applied to natural deductions.
   Moreover, "contraction" is also widely used in the literature on Gentzen
systems (to be discussed later) for a specific deduction rule, whereas the
notion of "conversion" of the lambda calculus literature is hardly used here.
Therefore after prolonged hesitation we have chosen the terminology adopted
here.
   (ii) Usually it is more convenient to think of the reduction tree of a term
t as a tree with its nodes labelled with terms; t is put at the root, and if s
is the label of the node v, there is, for each pair (s', 6) such that s  s', an
immediate successor v' to 1/, with label s'.
  Instead of the notion defined above, we may also consider a less refined
notion of reduction sequence by disregarding the redexes; that is to say, we
identify sequences
                   613   51      62               ,       ,   ,    e2
               to .-1 t1 -1 t2        .   anu     to >-1 ti   t2

if ti = ei for all i. The notion of reduction tree is then changed accordingly.
The arguments in this book using reduction sequences hold with both notions
of reduction sequence.

NOTATION. We shall distinguish different conversion relations by subscripts;
so we have, for example, conto, conton (to be defined below). Similarly for
the associated relations of one-step reduction: »-34, -, »"0, etc. We write
-=,3 instead of =eonto etc.

1.2.6. EXAMPLES. For us, the most important reduction is the one induced
by 0-conversion:
         (ÀaA.tB )sA conts tB [xA I sal].
n-conversion is given by
         AxA.tx contn t          (x i;Z FV(t)).
14                                                      Chapter I. Introduction

Ori-conversion contsn is conto U contn.
   It is to be noted that in defining >-,8,1, conversion of redexes occur-
ring within the scope of a A-abstraction operator is permitted. However,
no free variables may become bound when executing the substitution in a
0-conversion. An example of a reduction sequence is the following:
         (Axyz.xz(yz))(Auv.u)(Au'v'.u')
         (Ayz.(Auv.u)z(yz))(Atilvi.u')
         (Ayz.(Av.z)(yz))(Au'vi.ui)
         (Ayz.z)(Au'v' .u')
         Az.z.

Relative to conton conversion of different redexes may yield the same result:
(Ax.yx)z      yz either by converting the 0-redex (Ax.yx)z or by converting
the ri-redex Ax.yx. So here the crude and the more refined notion of reduction
sequence, mentioned above, differ.

DEFINITION. A relation R is said to be confluent, or to have the Church-
Rosser property (CR), if, whenever to Rti and to Rt2, then there is a t3 such
that t1R t3 and t2 R t3. A relation R is said to be weakly confluent, or to
have the weak Church-Rosser property (WCR), if, whenever to Rt1, to R t2
then there is a t3 such that t1 R* t3, t2 t3, where R* is the reflexive and
transitive closure of R.

1.2.7. THEOREM. For a confluent reduction relation »- the normal forms
of terms are unique. Furthermore, if »- is a confluent reduction relation we
have: t = t' iff there is a term t" such that t t" and t' »- t".
PROOF. The first claim is obvious. The second claim is proved as follows.
If t = t' (for the equality induced by >-), then by definition there is a chain
t     to, ti, .
             .    tn   t', such that for all i < n ti ti+i or ti+i »- ti. The
existence of the required t" is now established by induction on n. Consider
the step from n to n + 1. By induction hypothesis there is an s such that
to »- s, tn »- s. If tn+i »- tn, take t" = s; if tn tn+i, use the confluence to
find a t" such that s »- t" and tn+1 >- t".                                  N


1.2.8. THEOREM. (Newman's /emma) Let »- be the transitive and reflexive
closure of     and /et >-1 be weakly confluent. Then the normal form w.r.t.
    of a strongly normalizing t is unique. Moreover, if all terms are strongly
normalizing w.r.t.      then the relation »- is confluent.
PROOF. Assume WCR, and let us write s E UN to indicate that s has a
unique normal form. If a term is strongly normalizing, then so are all terms
occurring in its reduction tree. In order to show that a strongly normalizing t
has a unique normal form (and hence satisfies CR), we argue by contradiction.
1.2. Simple type theories                                                                          15

We show that if t E SN, t 0 UN, then we can find a ti       t with ti 0 UN.
Repeating this construction leads to an infinite sequence t    t1    t2 >--
 contradicting the strong normalizability of t.
     So let t E SN, t 0 UN. Then there are two reduction sequences t               >-
t'2 >-- .
      .   .    t' and t    t' >--1              t" with t', t" distinct normal terms.
Then either        = q, or         q. In the first case we can take ti := =
In the second case, by WCR we can find a t* such that t*                     t E SN,
hence t*   t" for some normal t". Since t' t" or t" t", either 0 UN
or t' % UN; so take ti := if t' t", ti    tg otherwise. The final statement
of the theorem follows immediately.

1.2.9. DEFINITION. The simple typed lambda calculus A, is the calculus of
/3-reduction and /3-equality on the set of terms of A, defined in 1.2.2. More
explicitly, A, has the term system as described, with the following axioms
and rules for --< (is -i3) and -= (is =13):

              t      t             (AxA .tB)8,4       t13 [xi / sA]


                  t »- s            t 8                 t »- s              t »- s         s   r
              rt »- rs             tr »- sr           Ax.t »- Ax.s                   t >-- r

              t      s             t=s               t=s              s=r
              t=S                  S=t                        t=r
The extensional simple typed lambda calculus An, is the calculus of On-
reduction and k-equality =-,3,7 and the set of terms A,; in addition to the
axioms and rules already stated for the calculus A, there is the axiom
              Ax.tx »- t              FV(t)).

1.2.10. LEMMA. (Substitutivity of »- )3 and »73n) For »- either »- or »- on we
have

              if s         s' then s[y Is"]   _- sqy I s"1.

PROOF. By induction on the depth of a proof of s »- s'. It suffices to check
the crucial basis step, where s is (Ax.t)t' , and s' is t[x It']: (Ax.t)tgy I s"] =
 (Ax.(t[y I s"])tlyI s"] = t[y I 3"][x lily I s"]] = t[x I t'][y I s"1 using (1.2.4). Here it
is assumed that x y, x i;Z FV(s") (if not, rename x).

1.2.11. PROPOSMON. »-/3,1 and                                 are wealdy confluent.
PROOF. By distinguishing cases. If the conversions leading from t to t' and
from t to t" concern disjoint redexes, then t'" is simply obtained by converting
both redexes. More interesting are the cases where the redexes are nested.
16                                                                            Chapter I. Introduction

     If t ...(Ax.$)s'       t'       s[x/ s']..., and t"    (Ax.$)s"      s'     s",
then t"      .. s[x/s"]..., and t' - t" in as many steps as there are occurrences
                    .


of x in s, t" »- ell in a single step.
  If t                      t'       s[x/ s']..., and t"    (Ax.s")s'      s     s",
then t"'                       . Here we have to use the fact that if s »- s", then

s[x/s']»- slx/s11, i.e. the compatibility of reduction with substitution.
     The cases involving ri-conversion we leave to the reader.

1.2.12. THEOREM. The terms of A, Ari are strongly normalizing for »-0
and -,377 respectively, and hence the 0- and Oil-normal forms are unique.
PROOF. For -15/ and >--,877 see sections 6.8 and 8.3 respectively.
   From the preceding theorem it follows that the reduction relations are con-
fluent. This can also be proved directly, without relying on strong normal-
ization, by the following method, due to W. W. Tait and P. Martin-Löf (see
Barendregt [1984, 3.2]) which also applies to the untyped lambda calculus.
The idea is to prove confluence for a relation -p which intuitively corre-
sponds to conversion of a finite set of redexes such that in case of nesting the
inner redexes are converted before the outer ones.

1.2.13. DEFINITION. >--p on A, is generated by the axiom and rules
            (id) x L-p x

            (Amon)
                          Ax.t
                               t Y-
                                    P t'Ax.9        (appmon)
                                                                t        t'
                                                                    ta »-p t'a'
                                                                               s 2: s'
                                                                                   13




                         t          ti     8   13
                                                    (upar)      t
                                                               t->:Pti        (x   FV(t))
       (ßPar) (Ax.t)s p tqx/s'i
We need some lemmas.

1.2.14. LEMMA. (Substitutivity of -p) If t                          t', s hp s', then t[x/s] L-p
e[x/s1].
PROOF. By induction on Iti. Assume, without loss of generality, x FV(s).
We consider one case and leave others to the reader. Let t (Ay.t].)t2 and
assume (induction hypothesis):
            if t1 »-p    and s p s', then ti[x/ s]      t'jx/s1,
            if t2 -p t'2 and s   s', then t2[x/s] »-p t'2[x/ s'].
Then
            t »-p       [y/t12] ,    and
            t[x/s]           (AY.t1[x/s])t2[x/s] ?:p ti1[X/Si][y/t2[X/S1]]
by the IH, and by 1.2.4 this last expression is (t'1[y/t'2])[x/s1.
1.2. Simple type theories                                                                 17

1.2.15. LEMMA. -p is confluent.
PROOF. By induction on Iti we show: for all t', t", if t                 t', t" then there is
a t" such that t', t"            t".
Case I. If t >Th t', t" by application of the same clause in the definition of
the claim follows immediately from the IH, using 1.2.14 in the case of ßpar.
Case 2. Let
          t Ax.tox       Ax.t'ox, where to -p t'o (Amon), and
          t >Th tg, where to   tg (war).
Apply the IH to to               4,tg to find tgi such that tio, tg »-p tg/. We can then
take t"
Case 3. Let
          t     Ax.(Ax.to)x >Th Ax.tio, where to >Th t'o (f3par, Amon), and
          t         tg, where Ax.t0       tg    (npar).

Then Ax.t0 -p Ax.4; since lAx.e0 I < t, the IH applies and there is tg' such
that Ax.4, tg  tg,. Then we can put tll' tg'.
 Case 4. Let

          t     (AX.t0)ti
                    where to »-p          >-       (Amon, appmon), and
          t         tg[0111, where to              t1        (Opar).

By the IH we find t', t'1" such that
          tlo, tg     p 41,

then
          (Ax .4)4             tgqx I tfl (Opar) and
          tg[x/tg]            tgi[x/q] (substitutivity of
Take t" tglx1q1.
Case 5. Let
          t     (Ax.tox)ti L-p
                 where tO                 »-p       x i;Z FV(to) (npar, appmon), and
          t Th tg[X/q], where tox                t, ti L-p     (Opar).

Also tox p t'ox. Apply the IH to tox (which is possible since 'taxi < ItI) to
find tg' with

          t'ox, 4 L-p tg',
18                                                          Chapter 1. Introduction

and apply the 1H to t1 to find t'1' such that

            ti;

Then

         t'oti   (4x)[x/t'l] L-p (tg/x)[x/q1    tgit' and
         t'ax/q] L-p t'ofqx/q1

(both by substitutivity of

1.2.16. THEOREM. 0- and ßr-reduction are confluent.
PROOF. The reflexive closure of .-1 for 077-reduction is contained in         and
  is therefore the transitive closure of >Th. Write t >-p, t' if there is a chain
t tO >Th tl     t2 >Th . -p tn     ti. Then we show by induction on n + m,
using the preceding lemma, that if t p,n e, t p,m t" then there is a t" such
that t' -pon    t" >--p,n


1.2.17. Typed combinatory logic
We now turn to the description of (simple) typed combinatory logic, which is
an analogue of ), without bound variables.

DEFINITION.    ( Terms of typed combinatory logic CL,) The terms are induc-
tively defined as in the case of A,, but now with the clauses

       For each A E r+ there is a countably infinite supply of variables of
                                                        A vA, wA, xA ,,A, zA
       type A; for arbitrary variables of type A we use u,
       (possibly with extra sub- or superscripts)

       for all A, B,C E T there are constant terms

                  kA'B E A -4 (B > A),
                  sA,B,C E (A   (B     C)) > ((A > B) > (A > C));

       if tA-+B SA are terms of the types shown, then App(tA'13,As )B is a
       term of type B.

Conventions for notation remain as before. Free variables are defined as in
A,, but of course we put FV(k) = FV(s) = 0.
1.2. Simple type theories                                                              19

DEFINITION. The weak reduction relation >--, on the terms of CL, is gen-
erated by a conversion relation contw consisting of the following pairs:
       kA,B xAyB contw x,SA,B ' CXA-4(B-4C)yArB zA                     contw zz(yz).

In other words, CL is the term system defined above with the following
axioms and rules for .-w and -=w (abbreviated to                     =):

           t       t               kxy       x        sxyz -- xz(yz)

               t       s            t    s            t-s        s-r
           rt          rs          tr -- sr                 t>-- r

           t >-- s                 t=s                t=s      s=r
           t=s                     s=t                      t=r

1.2.18. THEOREM. The weak reduction relation in CL, is confluent and
strongly normalizing, so normal forms are unique.
PROOF. Similar to the proof for A, but easier (cf. 6.8.6).


1.2.19. The effect of lambda-abstraction can be achieved to some extent in
CL, as shown by the following theorem.

THEOREM. To each term t in CL, there is another term A*xA.t such that

      xA           FV(A*xA.t),

      (A*xA.t)sA >--w t[xA/sA].

PRooF.We define A*xA.t by recursion on the construction of t:
                            sA,A,AkA,A-+AkA,A,

      .\*xA.yB := kB,AyB for y 0 x

      A*xA t134.Cti3                    (A*x.ti)(A*x.t2).

The properties stated in the theorem are now easily verified by induction on
the complexity of t.

COROLLARY. CL, is combinatorially complete, i.e. for every applicative
combination t of k, s and variables xl, x2,.       there is a dosed term s
such that in CL, H        xr, =w t, in fact even CL F- sxi        -w t. Z
20                                                           Chapter 1. Introduction

REMARK. Note that the defined abstraction operator A*x fails to have an
important property of Az: it is not true that, if t = t', then A*x.t = A*
Counterexample (dropping all type indications): kxk = x, but A*x.kxk =
s(s(kk)(skk))(kk), A*x.x = skk. The latter two terms are both in weak
normal form, but distinct; hence by the theorem of the uniqueness of normal
form, they cannot be proved to be equal in CL,.

1.2.19A. 01 Consider the following variant A° x.t of A* x.t: A° x.x := skk, A° x.t :-=
kt if x FV(t), A° x.tx := t if x FV(t), A° x.ts := s(Vx.t)(Vx.$) if the preceding
clauses do not apply. Show that this alternative defined abstraction operator has
the properties mentioned in the theorem above, and in addition

       A° x.tx h     t if x   t,

       (A° x.t)[y I s] = A° x.t[y I s] if y #z, x   FV(s).

Show by examples that A*x.t does not have these properties in general. Also, verify
that it is still not true that if t
                                t', then Vx.t = A° x.t1


1.2.20. Computational content
In the remainder of this section we shall show that there is some "compu-
tational content" in simple type theory: for a suitable representation of the
natural numbers we can represent certain number-theoretic functions. This
will be utilized in 6.9.2 and 11.2.2.


DEFINITION. The Church numerals of type A are 0-normal terms TA of type
(A --+ A) -4 (A -4 A), n E IN, defined by

          9.7A      AfAritAxa.fn(x),

where f0(x) :=         f'-I-1(x) := f(fn(X))
                                          \\. NA is the set of all the TA.

N.B. If we want to use ßi-normal terms, we must use AfA-4A.f instead of
Af x. f x for TA.


DEFINITION. A function f:INk --+ IN is said to be A-representable if there is
a term F of A, such that (abbreviating TA as TO

          Frti      Ttk = f(ni        nk)

for all n1,      ,k E N,                                                           N
1.2. Simple type theories                                                            21

DEFINITION. Polynomials, extended polynomials

     The n-argument projections p' are given by pIL (xi,      , xn) = xi, the

     unary constant functions cm by cm(x) = m, and sg, g are unary func-
     tions which satisfy sg(Sn) = 1, sg(0) = 0, T,g(Sn) = 0, q(0) = 1, where
     S is the successor function.
     The n-argument function f is the composition of m-argument g, n-
     argument h1, . , hin if f satisfies f
                     . .                   = g(hi(1), , hin(1)).
     The polynomials in n variables are generated from     cm, addition and
     multiplication by closure under composition. The extended polynomials
     are generated from p, Cm, sg, g, addition and multiplication by closure
     under composition.

1.2.20A. 4 Show that all terms in 0-normal form of type (P P) (P P),
P a propositional variable, are either of the form Tip or of the form AfP'P.f.

1.2.21. THEOREM. All extended polynomials are representable in
PROOF. Abbreviate INIA as N. Take as representing terms for addition, mul-
tiplication, projections, constant functions, sg, Tg:
        F+ := AxN yN f A zA .x f (yfz),
        Fx := AxNyNfA4A .x(yf
        Fk := Axiv
            := AxN
        Fsg := AxN fArAzA.x(AuA.f z)z,
        Fro := AxN fa>AzA.x(Àua.z)(f z).

It is easy to verify that F+, Fx represent addition and multiplication respec-
tively by showing that
         (TA f Am) 0 (rnAf A-4A)     (n   in)A (f A-4A),   TIA 0 7,71A   (7-cfn)A,


where f o g :=      f (g(z)). The proof that the representable functions are
closed under composition is left to the reader.                                      N

  A proof of the converse of this theorem (in the case where A is a proposition
variable) may be found in Schwichtenberg [1976].

REMARK. Extended polynomials are of course majorized (bounded above)
by polynomials.
  However, if we permit ourselves the use of Church numerals of different
types, and in particular liberalize the notion of representation of a function
22                                                          Chapter 1. Introduction

by permitting numerals of different types for the input and the output, we
can represent more than extended polynomials. In particular we can express
exponentiation

          TIA-rAnlA = (mn)A (n > 0).


1.2.21A. * Complete the proof of the theorem and verify the remark.


1.3        Three types of formalism
The greater part of this text deals with the theory of the "standard" logics,
that is minimal, intuitionistic and classical logic. In this section we introduce
the three styles of formalization: natural deduction, Gentzen systems and
Hilbert systems. (On the names and history of these 'types of formalism,
see the notes to chapters 2 and 3.) The first two will play a leading role in
the sequel; the Hilbert systems are well known and widely used in logic, but
less important from the viewpoint of structural proof theory. Each of these
formalization styles will be illustrated for implication logic.
   Deductions will be presented as trees; the nodes will be labelled with for-
mulas (in the case of natural deduction and Hilbert systems) or with sequents
(for the Gentzen system); the labels at the immediate successors of a node I,
are the premises of a rule application, the label at 1/ the conclusion. At the
root of the tree we find the conclusion of the whole deduction.
   The word proof will as a rule be reserved for the meta-level; for formal
arguments we preferably use deduction or derivation. But prooftree will mean
the same as deduction tree or derivation tree, and a "natural deduction proof"
will be a formal deduction in one of the systems of natural deduction. Rules
are schemas; an instance of a rule is also called a rule-application or inference.
     If a node C in the underlying tree with say two predecessors and one
successor looks like the tree on the left, we represent this more compactly as
on the right:


                        A           i3
                                                   .    .



                                                   AB


We use script V, e, possibly sub- and/or superscripted, for deductions.
1.3. Three types of formalism                                                23

1.3.1. The BHK-interpretation
Minimal logic and intuitionistic logic differ only in the treatment of nega-
tion, or (equivalently) falsehood, and minimal implication logic is the same
as intuitionistic implication logic. The informal interpretation underlying in-
tuitionistic logic is the so-called BrouwerHeytingKolmogorov interpretation
(BHK-interpretation for short); this interpretation tells us what it means to
prove a compound statement such as A --+ B in terms of what it means to
prove the components A and B (cf. classical logic, where the truthvalue of
A     B is defined relative to the truthvalues of A and B). As primitive notions
in the BHK-interpretation there appear "construction" and "(constructive,
informal) proof". These notions are admittedly imprecise, but nevertheless
one may convincingly argue that the usual laws of intuitionistic logic hold for
them, and that, for our understanding of these primitives, certain principles
of classical logic are not valid for the interpretation. We here reproduce the
clause for implication only:
      A construction p proves A --* B if p transforms any possible proof q of
      A into a proof p(q) of B.
A logical law of implication logic, according to the BHK-interpretation, is a
formula for which we can give a proof, no matter how we interpret the atomic
formulas. A rule is valid for this interpretation if we know how to construct
a proof for the conclusion, given proofs of the premises.
   The following two rules for > are obviously valid on the basis of the BHK-
interpretation:
      If, starting from a hypothetical (unspecified) proof u of A, we can find
      a proof t(u) of B, then we have in fact given a proof of A > B (without
      the assumption that u proves A). This proof may be denoted by Au.t(u).
      Given a proof t of A > B, and a proof s of A, we can apply t to s
      to obtain a proof of B. For this proof we may write App(t, o) or to (t
      applied to s).

1.3.2. A natural deduction system for minimal implication logic
Characteristic for natural deduction is the use of assumptions which may
be closed at some later step in the deduction. Assumptions are formula
occurrences appearing at the top nodes (leaves) of the prooftree; they may
be open or closed. Assumptions are provided with markers (a type of label).
Any kind of symbol may be used for the markers, but below we suppose the
markers to be certain symbols for variables, such as u, y, w, possibly sub- or
sup erscripted.
  The assumptions in a deduction which are occurrences of the same formula
with the same marker form together an assumption class. The notations
24                                                          Chapter I. Introduction
                                                D'               D'
                [Alu             Au
                                                [A]               A



have the following meaning, from left to right: (1) a deduction 7, with con-
clusion B and a set [A] of open assumptions, consisting of all occurrences of
the formula A at top nodes of the prooftree D with marker u (note: both B
and the [A] are part of D, and we do not talk about the mu/tiset [A]u since
we are dealing with formula occurrences); (2) a deduction 1, with conclusion
B and a single assumption of the form A marked u occurring at some top
node; (3) deduction D with a deduction D', with conclusion A, substituted
for the assumptions [A]u of D; (4) the same, but now for a single assumption
occurrence A in D. Under (3) the formula A shown is the conclusion of TY
as well as the formula in an assumption class of D.
   In cases (3) and (4) this metamathematical notation may be considered
imprecise, since we have not indicated the label of A before substitution. But
in practice this will not cause confusion. Note that the marker u disappears
by the substitution: only topformulas bear markers.
   We now consider a system 1\Ini for the minimal theory of implication.
Prooftrees are constructed according to the following principles.
   A single formula occurrence A labelled with a marker is a single-node
prooftree, representing a deduction with conclusion A from open assumption
A.
     There are two rules for constructing new prooftrees from given ones, whicla
correspond precisely to the two principles (a), (b) valid for the BHK-inter-
pretation, mentioned above, and which may be rendered schematically as
follows:

                        [A]u
                                               D       D'
                                             A -4 B    A.4E
                       A -4 B
By application of the rule A of implication introduction, a new prooftree is
formed from D by adding at the bottom the conclusion A -4 B while closing
the set of open assumptions A marked by u. All other open assumptions
remain open in the new prooftree.
   The rule >E of implication elimination (also known as modus ponens)
construgts from two deductions V, V' with conclusions A > B, A a new
combined deduction with conclusion B, which has as open assumptions the
open assumptions of D and D' combined.
  Two occurrences a, /3 of the same formula belong to the same assumption
class if they bear the same label and either are both open or have both been
closed at the same inference.
1.3. Three types of formalism                                                  25

   It should be noted that in the rule -*I the "degenerate case", where [Alu
is empty, is permitted; thus for example the following is a correct deduction:
                                      AL
                                    B --+ A-
                                 A * (B --+ A)
At the first inference an empty class of occurrences is discharged; we have
assigned this "invisible class" a label y, for reasons of uniformity of treatment,
but obviously the choice of label is unimportant as long as it differs from all
other labels in use; in practice the label at the inference may be omitted in
such cases.
  In applying the rule --A, we do not assume that [Al consists of all open as-
sumptions of the form A occurring above the inference. Consider for example
the following two distinct (inefficient) deductions of A-+(A-+A):
                   Au   ,                            Au    9,
               A            Aw                   A        A-       Ay
                        A                                 A
                    A       -                         A -* A            9,,
                A > (A > A) -                    A        (A -* A) -
The formula tree in these deductions is the same, but the pattern of closing as-
sumptions differs. In the second deduction all assumptions of the given form
which are still open before application of an inference --+I are closed simulta-
neously. Deductions which have this property are said to obey the Complete
Discharge Convention; we shall briefly return to this in 2.1.9. But, no matter
how natural this convention may seem if one is interested in deducible formu-
las, for deductions as combinatorial structures it is an undesirable restriction,
as we shall see later.

1.3.3. EXAMPLE.
                   A -4 (B            Aw A           By       Aw
                          B- C
                                       C w
                                    A     C
                            (A     .13) -4 (A
                 (A -4 (B       C)) -4 ((A > B) > (A -4 C))u
We have not indicated the rules used, since these are evident.

1.3.4. Formulas-as-types
As already suggested by the notation, the BHK-valid principles (a) and (b)
correspond to function abstraction, and application of a function to an argu-
ment respectively. Starting from variables u, y, w associated with assumption
26                                                        Chapter 1. Introduction

formulas, these two principles precisely generate the terms of simple type
theory A,.
  Transferring these ideas to the formal rules constructing prooftrees, we
see that parallel to the construction of the prooftree, we may write next
to each formula occurrence the term describing the proof obtained in the
subdeduction with this occurrence as conclusion.
      To assumptions A correspond variables of type A; more precisely, for-
mulas with the same marker get the same variable. If we have already used
variable symbols as markers, we can use these same variables for the corre-
spondence.
      For the rules --A and *E the assignment of terms to the conclusion,
constructed from term(s) for the premise(s), is shown below.

                     [u: A]
                                                            D'
                      t: B        u
                                               t:A*B       s: A
                                                (0-4B sA): B
                MLA .tB : A   B
Thus there is a very close relationship between A, and -4Nm, which at
first comes as a surprise. In fact, the terms of A, are nothing else but
an alternative notation system for deductions in -4Nm. That is to say, if
we consider just the term assigned to the conclusion of a deduction, and
assuming not only the whole term to carry its type, but also all its subterms,
the prooftree may be unambiguously reconstructed from this term. This is
the basic observation of the formulas-as-types isomorphism, an observation
which has proved very fruitful, since it is capable of being extended to many
more complicated logical systems on the one hand, and more complicated
type theories on the other hand, and permits us to lift results and methods
of type theory to logic and vice versa.
  By way of illustration, we repeat our previous example, but now at each
node of the prooftree we also exhibit the corresponding terms. We have not
shown the types of subterms, since these follow readily from the construction
of the tree. We have dropped the superscript markers at the assumptions,
as well as the repetition of markers at the line where an assumption class is
discharged, since these are now redundant.

1.3.5. EXAMPLE.
                                      w:A    v:A>.13      w: A
                      uw: B       C               vw: B
                                  uw (vw): C
                           Aw.uw(vw): A > C
                  Avw.uw(vw): (A > B) > (A C)
         Auvw.uw(vw): (A --+ (B  C)) --+ ((A B) (A + C))
1.3. Three types of formalism                                                 27




                 AA
1.3.6. Identity of prooftrees. When are two prooftrees to be regarded as
identical? Taking the formulas-as-types isomorphism as our guideline, we can
say that two prooftrees are the same, if the corresponding terms of simple type
theory are the same (modulo renaming bound variables). Thus the following
two prooftrees are to be regarded as identical:
          (A     A)u   A'                       (A --+ A)u   A'
               AA,,               Aw                 A+A           Av

                    AAWA
                                                           AAV
                                                             A


since the first one corresponds to the term Atu.(Av.uv)w, and the second to
Av.(Av.uv)v, and these terms are the same modulo renaming of bound vari-
ables. On the other hand, the two deductions at the end of 1.3.2 correspond
to Awu.(Av.u)w and Awv.(Au.u)v respectively, which are distinct terms.
   In the right hand tree, the upper 4 closes only the upper occurrence A v;
the lower q only the lower occurrence of A' (since at that place the upper
occurrence has already been closed). In other words, the two A v-occurrences
belong to distinct assumption classes, since they are closed at different places.
   Without loss of generality we may assume that the labels for distinct as-
sumption classes of the same formula are always distinct, as in the first of the
two prooftrees above.
   However, there is more to the formulas-as-types isomorphism than just
another system of notation. The notion of /3-reduction is also meaningful for
prooftrees. A 0-conversion
                           (AxA .tB\ sA conto tB [xA/sAl
                                    )


corresponds to a transformation on prooftrees:
                           [A]u

                                       D'
                       A>B             A


Here the prooftree on the right is the prooftree obtained from D by replacing
all occurrences of A in the class [A] in 7, by V'. Note that the f.o. A > B in
the left deduction is a local maximum of complexity, being first introduced,
only to be removed immediately afterwards. The conversion may be said to
remove a "detour" in the proof. A proof without detours is said to be a
normal proof. Normal deductions may be said to embody an idea of "direct"
proof.
  In a normal proof the left (major) premise of >E is never the conclusion
of +I. One can show that such normal deductions have the subformula
28                                                       Chapter I. Introduction

property: if a normal deduction 1, derives A from open assumptions r, then
all formulas occurring in the deduction are subformulas of formulas in r, A.
   The term notation for deductions is compact and precise, and tells us ex-
actly how we should manage open and closed assumptions when we substi-
tute one prooftree into another one. Using distinct markers for distinct closed
assumption classes corresponds to the use of separate variables for each oc-
currence of a binding operator. The tree notation on the other hand gives us
some geometric intuition. It is not so compact, and although in principle we
can treat the trees with the same rigour as the terms, it is not always feasi-
ble to do so; one is led to the use of suggestive, but not always completely
precise, notation. In our discussion of natural deduction we shall extend the
term notation to full predicate logic (2.2) and give a notion of reduction for
the full system in chapter 6.

1.3.7. Gentzen systems
There are two motivations leading to Gentzen systems, which will be discussed
below. The first one views a Gentzen system as a metacalculus for natural
deduction; this applies in particular to systems for minimal and intuitionistic
logic. The second motivation is semantical: Gentzen systems for classical logic
are obtained by analysing truth conditions for formulas. This also applies to
intuitionistic and minimal logic if we use Kripke semantics instead of classical
semantics.
A Gentzen system as a metacalculus. Let us first consider a Gentzen system
obtained as a metacalculus for the system >Nm. Consider the following four
construction steps for prooftrees.
      The single-node tree with label A, marker u is a prooftree.
      Add at the bottom of a prooftree an application of -4I, discharging an
      assumption class.
      Given a prooftree D with open assumption class [B]u and a prooftree
      Di deriving A, replace all occurrences of B in [B]u by

                                               Di
                                   A > By       A
                                         B
      Substitute a deduction of A for the occurrences of an (open) assumption
      class [Art of another deduction.
These construction (or generation) principles suffice to obtain any prooftree of
-->Nm, for the first construction rule gives us the single-node prooftree which
derives A from assumption A, the second rule corresponds to applications of
>I, and closure under >E is seen as follows: in order to obtain the tree
1.3. Three types of formalism                                               29

                                     D1         D2
                                 A        ./3   A


from the prooftrees D1, D2, we first combine the first and third construction
principles to obtain
                                                D2
                                 A + Bu         A


and then use the fourth (substitution) principle to obtain the desired tree.
  Let I'    A express that A is deducible in 1\1111 from assumptions in F.
Then the four construction principles correspond to the following axiom and
rules for obtaining statements F A:

            U {A}    A (Axiom)

            U {A}    B                Auff3I
                                                         CL_*
                                 PUAU{A+B}              C

                     AU{A}       Bcut

Call the resulting system S (an ad hoc designation). Here in the sequents
F     A the r is treated as a (finite) set. For bookkeeping reasons it is
often convenient to work with multisets instead; multisets are "(finite) sets
with repetitions", or equivalently, finite sequences modulo the order of the
elements. If we rewrite the system above with multisets, we get the Gentzen
system described below, which we shall designate ad hoc by S', and where in
the sequents      A the I' is now a multiset. The rules and axioms of S' are
        A     A (Axiom)


            r,A,A>BC
            rA
                    ALW                          r,BA
              A      A,AB Cut
R-4 and L--+ are called the logical rules, LW, LC and Cut the structural rules.
LC is called the rule of (left-)contraction, LW the rule of (left-)weakening.
Due to the presence of LC and LW, derivability of              is equivalent to
derivability of Set(r)     A where Set(r) is the set underlying the multiset
30                                                                        Chapter I. Introduction

F. We have simplified the axiom, since some applications of LW produce
F, A     A from A     A.
   If one uses sequences instead of sets, in order to retain equivalence of deriv-
ability of F     A and derivability of Set(F)      A, an extra rule of exchange
then has to be added:
                              F,A,B,A C T
                              F,B,A,L         C

EXAMPLE. (Of a deduction in S and S')
                               AA               B            B
                                 A > B, A            B
                               A       (A      B)  B
                                                                 R+
                               A        ((A     B)   B)
The natural deduction of (A + (B > C)) > ((A                                 B) > (A > C)),
which we gave earlier in example 1.3.3 may be obtained by repeated use of
the generation principles 1-3 (not 4) as follows:
              3: A     (B > C)u           3: Aw          2: A        By 2: Aw
                        1: B       C                                 1:B
                                              0: C
                                         4: A + C w                   v
                                  B) > (A > C)
                               5: (A
                6: (A > (B > C)) -4 ((A B) > (A                              C)) u
In the displayed tree, the numbers 0-6 indicate the seven steps in the construc-
tion of the tree. The number 0 corresponds to an application of construction
principle 1, the numbers 4-6 to applications of principle 2, the numbers 1 and
3 to applications of principle 3, and number 2 to an application of principle
3 in the construction of the subtree with conclusion B. We can now readily
transform this into a sequent deduction in S:
                                      BB                                      (0)
                                   AA B B > C            ,                 C (1)
                       AA A, A --+ B B > C           ,                   C (2)
                        A, A > B , A --+ (B                      C)    C (3)
                       A -4 B , A > (B > C)                        A --+ C (4)
                     A > (B > C)           B) > (A > C) (5)
                                              (A
                     (A > (B > C)) -4 ((A -4 B) > (A -4 C)) (6)
where the lines 1-6 correspond to the steps 1-6 above; the only axiom appli-
cation appearing as a right premise for L>, namely C C, corresponds to
step O.
  Only a slight change is necessary to formulate the deduction in the calculus
with multisets:
1.3. Three types of formalism                                                      31


                                  AA BB B --+ CC=CC
                       AA
                                                ,




                       A, A, A + B , A     (B       C) =Cc
                        A, A     B , A + (B --+ C)    C
                       A    B, A       (B + C) A C
                    A + (B C) (A B) (A --+ C)
                    (A    (B --+ C))    ((A     B) + (A + C))
The appearance of two occurrences of A just before the LC-inference corre-
sponds to the two occurrences of A t" in the original deduction in --+Nm.
  It is not hard to convince oneself that, as long as only the principles 1-3
for the construction of prooftrees are applied, the resulting proof will always
be normal. Conversely, it may be proved that all normal prooftrees can be
obtained using construction principles 1-3 only. Thus we see that normal
prooftrees in -41\Tm correspond to deduction in the sequent calculus without
Cut; and since every proof in natural deduction may be transformed into a
normal proof of the same conclusion, using (at most) the same assumptions,
it also follows for the sequent calculus that every deducible sequent F     A
must have a deduction without Cut.
   Deductions in S without the rule Cut have a very nice property, which is
immediately obvious: the subformula property: all formulas occurring in a
deduction of r A are subformulas of the formulas in F, A.
   A point worth noting is that the correspondence between sequent calculus
deductions and natural deductions is usually not one-to-one. For example, in
our transformation of the example 1.3.3 above, the steps 2 and 3 might have
been interchanged, resulting in a different deduction in S.
   Another remark concerns construction principle 3: it follows in an indirect
way from the rule >E. Instead of --*E we might take the following:
                                                     [B]u
                                      Do       vi     D2
                           --+E*,uA + B        A      C

which closely corresponds to construction principle 3 (cf. 6.12.4).

1.3.7A. * There are other possible choices for the construction principles for
prooftrees. For example, we might replace principle 3 by the following principle 3':
  Given a prooftree D with open assumption class [B]u, replace all occurrences of
B in [B]u by
                                   A > By       A

Show that this also generates all natural deduction prooftrees for implication logic;
what sequent rules do these modified principles give rise to?
32                                                        Chapter 1. Introduction

1.3.7B. * Show that the following prooftree requires an application of construc-
tion principle 4:

                         AAB
                           A Au Au      B   n
                                                     Au


1.3.8. Semantical motivation of Gentzen systems
For classical logic, we may arrive in a very natural way at a Gentzen system
by semantical considerations. Here we use sequents F         A, with r and A
finite sets; the intuitive interpretation is that F  A is validiffAF-4VA
is true. Now suppose we want to find out if there is a valuation making all of
F true and all of A false. We can break down this problem by means of two
rules, one for reducing A       B on the left, another for reducing A > B on
the right:
         r    A,        F, B    A L.4       r, A      B, A
                                                               R+
              r,A--+B      A                       .14_*B, A

The problem of finding the required solution for the sequent at the bottom is
equivalent to finding the solution(s) for (each of) the sequent(s) at the upper
line. Thus starting at the bottom, we may work our way upwards; along each
branch, the possibility of applying the rules stops, if all components have been
reduced to atoms. If all branches terminate in sequents of the form r',P
P, A', there is no valuation for the sequent r     A making r true and A false.
Taking sequents r',P          P, A' as axioms, the search tree for the valuation
has then in fact become a derivation of the sequent r         A from axioms and
L-4, R-4. This very simple argument constitutes also a completeness proof
for classical propositional logic, relative to a Gentzen system without Cut.
This idea for a completeness proof may also be adapted (in a not entirely
trivial way) to intuitionistic and minimal logic, with Kripke semantics as the
intended semantics.
   The reader may be inclined to ask, why consider Gentzen systems at all?
They do look more involved than natural deduction. There are two reasons
for this. First of all, for certain logics Gentzen systems may be justified by
semantical arguments in cases where it is not obvious how to construct an
appropriate natural deduction system. Secondly, given the fact that there is
a special interest in systems with the subformula property (on which many
elementary proof-theoretic applications rest), we note that the condition of
normality, guaranteeing the subformula property for natural deduction, is a
global property of the deduction involving the order in which the rules are
applied, whereas for Gentzen systems this is simply achieved by excluding
the Cut rule.
1.3. Three types of formalism                                                33

1.3.9. A Hilbert system
A third type of formalism, extensively used in the logical literature, is the
Hilbert system. Here there is a notion of deduction from assumptions, as for
natural deductions, but assumptions are never closed. In Hilbert systems, the
number of rules is reduced at the expense of introducing formulas as axioms.
In most systems of this type, modus ponens (+E) is in fact the only rule for
propositional logic.
  The Hilbert system Hm for minimal implication logic has as axioms all
formulas of the forms:
              (B       A)    (k-axioms),
        (A > (B        C))      ((A > B) + (A > C))     (s-axioms),

for arbitrary A, B and C, and has *E as the only rule. A deduction of B
from assumptions F is then a tree with formulas from F and axioms at the
top nodes, and the conclusion B at the root. (Usually, one finds K and S
instead of k and s in the literature, since K and S are standard notations
in combinatory logic. However, in modal logic one also encounters an axiom
schema K, and we wish to avoid confusion.)

EXAMPLE. A deduction DA of A           A:

[Aq(A>A)A)) >.[(A>(AA))(AA)) A«A>A)A)
                       (A-4(A A)) > (A A)                              A>.(A>A)
                                              A>A

Deductions in Hilbert systems are often presented in linear format. Thus,
in the case of implication logic, we may define a deduction of a formula A
as a sequence A1, A2,     , An such that A    An, and moreover for each k
(1 <k < n) either Ak is an axiom, or there are Ai, Ai with i, j < k such that
      Ai 4. Ak. For example, the prooftree above may be represented by the
following sequence:

(1)     [Aq(A>/1)A)]              [(A*(A+A))*(AA)] s-axiom
(2)     A«A+A)>A)                                           k-axiom
(3)     (Aq/1-4,4)) > (A>A)                                 (1), (2)
(4)     A 4. (A > A)                                        k-axiom
(5)     A>A                                                 (3), (4)
In fact, it is also possible to present natural deduction proofs and Gentzen
system deductions in such a linear form. Where the primary aim is to discuss
the actual construction of deductions, this is common practice in the literature
on natural deduction. The disadvantage of the tree format, when compared
with the linear format, is that the width of prooftrees for somewhat more
complicated deductions soon makes it impracticable to exhibit them. On the
34                                                      Chapter 1. Introduction

other hand, as we shall see, the tree format for natural deductions has decided
advantages for meta-theoretical considerations, since it provides an element
of geometrical intuition.
   There is also a formulas-as-types isomorphism for Hm, but this time the
corresponding term system is CL, where the constants k and s represent
the axioms (cf. 1.2.17)

               A * (B --+ A),
               : (A > (B --+ C))     ((A    B) + (A --+ C)),
and application corresponds to *E as for natural deduction.

EXAMPLES. We write AB as an abbreviation for A + B.
             kB(CB),A     (B(CB))(A(B(CB)))      kB 'C : B(CB)
                           kB(CB),AkB,C : A(B(CB))

The prooftree exhibited before, establishing A + A, corresponds to a term
                             sA,A-4A,AkA,A-4AkA,A


The notion of weak reduction of course transfers from terms of CL, to Hm,
but is of far less interest than 0-reduction for >Nm. However, the construc-
tion of an "abstraction-surrogate" A*x in 1.2.19 plays a role in proving the
equivalence (w.r.t. derivable formulas) between systems of natural deduction
and Hilbert systems, since it corresponds to a deduction theorem (see 2.4.2),
and thereby provides us with a method for translating natural deduction
proofs into Hilbert system proofs.
