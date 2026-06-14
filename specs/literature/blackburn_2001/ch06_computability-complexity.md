<!-- Source: Blackburn, de Rijke & Venema (2001). Modal Logic. Cambridge University Press. Chapter 6: Computability and Complexity (pages 334-414). BibKey: Blackburn2001 -->


6
Computability and Complexity
In this chapter we investigate the computability and complexity of normal modal
logics. In particular, we examine the computability of satisﬁability problems (given
a modal formula
 and a class of models M, is it computable whether
 is M-
satisﬁable?) and validity problems (given a modal formula
 and a class of models
M, is it computable whether
 is valid on M?). When the answer is ‘yes’, we
probe further: how complex is the problem — in particular, what resources of time
(that is, computation steps) or space (that is, memory) are needed to carry out the
required computations? When the answer is ‘no’, we pose a similar question: how
uncomputable is the problem? There are vast differences in the complexities of
modal satisﬁability problems: some are no worse than the satisﬁability problem
for propositional calculus, while others are highly undecidable.
This chapter has two main parts. The ﬁrst, consisting of the ﬁve sections on the
basic track, introduces the basic ideas and discusses modal (un-)decidability. Three
techniques for proving decidability are discussed (ﬁnite models, interpretations in
monadic second-order theories of trees, and quasi-models and mosaics) and unde-
cidability is approached via tiling problems. In the second part, consisting of the
last three sections of the chapter, we examine the complexity of some key modal
satisﬁability problems. These sections are on the advanced track, but the initial
part of each of them should be accessible to all readers.
Basic ideas about computability and complexity are revised in the ﬁrst section,
and further background information can be found in Section C. Throughout the
chapter we assume we are working with countable languages.
Chapter guide
Section 6.1: Computing Satisﬁability (Basic track). In this section we introduce
the key concepts assumed throughout the chapter: satisﬁability and validity
problems, and how to compute them on Turing machines.
Section 6.2: Decidability via Finite Models (Basic track). We discuss the use of
334



6.1 Computing Satisﬁability
335
ﬁnite models for proving decidability results. Three basic theorems are
proved, and many of the logics discussed in Chapter 4 are shown to be
decidable.
Section 6.3: Decidability via Interpretations (Basic track). Another way of prov-
ing modal decidability results is via interpretations in powerful decidable
theories such as monadic second-order theories of trees. This technique
is useful for showing the decidability of logics without the ﬁnite model
property.
Section 6.4: Decidability via Quasi-models and Mosaics (Basic track).
For log-
ics lacking the ﬁnite model property it may also be possible to prove de-
cidability results by computing with more abstract kinds of ﬁnite structure;
quasi-models and mosaics are important examples of such structures.
Section 6.5: Undecidability via Tiling (Basic track). In this section we show just
how easily undecidable — and even highly undecidable — modal logics
can arise. We do so by introducing an important proof method: tiling
arguments.
Section 6.6: NP (Advanced track). This section introduces the concept of NP al-
gorithms, illustrates the modal content of this idea using some simple ex-
amples, and then proves Hemaspaandra’s Theorem: every normal logic
extending S4.3 is NP-complete.
Section 6.7: PSPACE (Advanced track). The key complexity class for the basic
modal language is PSPACE, the class of problems solvable in polynomial
space. We give a PSPACE algorithm for the satisﬁability problem for K,
and prove Ladner’s Theorem: every normal logic between K and S4 is
PSPACE-hard.
Section 6.8: EXPTIME (Advanced track). We show that the satisﬁability prob-
lem for PDL is EXPTIME-complete. EXPTIME-hardness is shown by
reduction from a tiling problem, and the EXPTIME algorithm introduces
an important technique called elimination of Hintikka sets.
6.1 Computing Satisﬁability
The work of this chapter revolves around satisﬁability and validity problems. Here
is an abstract formulation.
Deﬁnition 6.1 (Satisﬁability and Validity Problems) Let
 be a modal similar-
ity type,
 be a
-formula and M a class of
-models. The M-satisﬁability problem
is to determine whether or not
 is satisﬁable in some model in M. The M-validity
problem is to determine whether or not
 is true in all models in M; that is, whether
or not
M

. (We call this the validity problem because we are mostly interested



336
6 Computability and Complexity
in cases where M is the class of all models over some class of frames.) The M-
validity and M-satisﬁability problem are each other’s duals.
a
In fact, as far as discussions of computability (or non-computability) are concerned,
we are free to talk in terms of either satisﬁability or validity problems.
Lemma 6.2 Let
 be a modal similarity type, and suppose that M is a class of
-models. Then there is an algorithm for solving the M-satisﬁability problem iff
there is an algorithm for solving the M-validity problem.
Proof. As
: is not satisﬁable in M iff
M

, given an algorithm for M-satis-
ﬁability, we can test for the validity of
 by giving it the input
:. In a similar
fashion, an algorithm for M-validity can be used to test for M-satisﬁability.
a
This argument does not give us any interesting information about the relative com-
plexity of dual satisﬁability and validity problems; and indeed, they may well be
different.
How do the themes of this chapter relate to the normal modal logics introduced
in Section 1.6 and discussed in Chapters 4 and 5? Clearly we should investigate
the following two problems.
Deﬁnition 6.3 Let
 be a modal similarity type,
 be a normal modal logic in a
language for
, and
 a
-formula. The problem of determining whether or not
 is
-consistent is called the
-consistency problem, and the problem of determining
whether or not

`
 is called the
-provability problem.
a
Note that
-consistency and
-provability problems are satisﬁability and validity
problems in disguise. In particular, if
 is a normal modal logic, and
M is any
class of models such that

=

M, then the
-consistency problem is the
M-
satisﬁability problem, and the
-provability problem is the
M-validity problem. As
every normal modal logic is determined by at least one class of models (namely, the
singleton class containing its canonical model; see Theorem 4.22), we are free to
think of consistency and provability problems in terms of satisﬁability and validity
problems. We do so in this chapter, and to emphasize this we usually call the
-
consistency problem the
-satisﬁability problem, and the
-provability problem
the
-validity problem.
Our discussion so far has given an abstract account of the problems we will ex-
plore, and most of our results will be stated, proved, and discussed at this level. But
what does it mean to have an algorithm for solving (say) a validity problem? And
what does it mean to talk about the complexity of (say) a satisﬁability problem?
After all, computation is the ﬁnitary manipulation of ﬁnite structures — but both
formulas and models are abstract set-theoretical objects. To show that our abstract



6.1 Computing Satisﬁability
337
account really makes sense, we need to choose a well-understood method of com-
putation and show that formulas and models can be represented in a way that is
suited to our method.
We have chosen Turing machines (Section C) as our fundamental model of com-
putation. The most relevant fact about Turing machines for our purposes is that
they compute by manipulating ﬁnite strings of symbols; hence we need to rep-
resent models and formulas as symbol strings. As far as mere computability is
concerned, the key demand is that these symbol string representations be ﬁnite.
For complexity analyses more is required: representations must also be efﬁcient.
Let’s discuss these requirements.
Clearly modal formulas can be represented as ﬁnite strings over a ﬁnite set of
symbols: proposition letters can be represented by a single symbol (say,
p) fol-
lowed by (the representation of) a number. Thus, instead of working with an inﬁ-
nite collection of primitive symbols we could work with (say)
p1,
p10,
p11,
p100
and so on, where the numeric tail is represented in binary. Fine — but what about
models? Models are set-theoretic entities of the form
(W
;
R
;
V
), and each com-
ponent may be inﬁnite. However, the difﬁculty is more apparent than real. For a
start, when evaluating a formula
 in some model, the only relevant information in
the valuation is the assignments made to propositional letters actually occurring in
 (see Exercise 1.3.1). Thus, instead of working with
V , we can work with the ﬁ-
nite valuation
V
0 which is deﬁned on the (ﬁnite) language consisting of exactly the
proposition letters in
, and which agrees with
V on these letters. Secondly, much
of our work will revolve around models based on ﬁnite frames (or more generally,
the frames of ﬁnite character deﬁned below).
We already know quite a lot about ﬁnite models and their logics. For a start,
in Section 2.3 we introduced two techniques for building ﬁnite models (selection
and ﬁltration) and deﬁned the ﬁnite model property for the basic modal language.
In Section 3.4 we introduced the ﬁnite frame property (again, for the basic modal
language) and proved Theorem 3.28: a normal modal logic has the ﬁnite frame
property iff it has the ﬁnite model property. Since then we have learned what a
normal modal logic in a language of arbitrary similarity type is (Deﬁnition 4.13),
so let’s now deﬁne the ﬁnite frame property and the ﬁnite model property for modal
languages of arbitrary similarity type, and generalize Theorem 3.28.
Deﬁnition 6.4 Let
 be a modal similarity type. A frame of type
 has ﬁnite char-
acter if it contains ﬁnitely many states, and ﬁnitely many non-empty relations. If
 is a normal modal logic in a language for
, and
F is a class of
-frames of ﬁnite
character, and

=

F, then
 is said to have the ﬁnite frame property (f.f.p.) with
respect to F. If

=

F for some class of
-frames F of ﬁnite character, then
 has
the ﬁnite frame property.
A class of
-models M is ﬁnitely based
if every model in M is based on a
-



338
6 Computability and Complexity
frame of ﬁnite character. If
 is a normal modal logic in a language for
, and
M is a class of ﬁnitely based
-models, and

=

M, then
 has the ﬁnite model
property (f.m.p.) with respect to M. If

=

M for some class of of ﬁnitely based
-models M, then
 has the ﬁnite model property.
a
A few remarks may be helpful. First, the concept of ﬁnite character is a natural way
of coping with similarity types containing inﬁnitely many relations. Second, note
that the way the ﬁnite frame property is deﬁned here (where we simply insist that

=

F) is somewhat simpler than that used in Deﬁnition 4.13 (where we insisted
that
F

, and for every formula
 such that

62
 there is some
F
2
F such that
 is falsiﬁable on
F). It is easy to see that these deﬁnitions are equivalent Finally, a
class of frames of ﬁnite character (or indeed, a class of ﬁnite frames) may well be
a proper class. Nonetheless, up to isomorphism, there are only denumerably many
frames in any such class; hence, if
 has the ﬁnite frame property, it has the ﬁnite
frame property with respect to a denumerably inﬁnite set of frames, and we take
this for granted without further comment throughout the chapter.
Given this deﬁnition, it is straightforward to generalize Theorem 3.28.
Theorem 6.5 Let
 be a modal similarity type. Any normal modal logic in a lan-
guage for
 has the ﬁnite model property iff it has the ﬁnite frame property.
Proof. This is a matter of verifying that the proof of Theorem 3.28 extends to
arbitrary similarity types; see Exercise 6.1.1.
a
There are many ways to represent a frame of ﬁnite character, together with a val-
uation
V
0 deﬁned on ﬁnitely many proposition letters, as a ﬁnite symbol string.
While any such ﬁnitization is sufﬁcient for discussions of computability, we need
to exercise more care when it comes to complexity. Complexity theory measures
the difﬁculty of problems in terms of the resources required to solve them — and
these are measured as a function of the size of the input. A highly inefﬁcient rep-
resentation of the input can render such resource measures vacuous, so we must be
careful not to smuggle in sources of inefﬁciency. For the complexity classes we
will be dealing with, this is pretty much a matter of common sense, but the follow-
ing point should be made explicit: we must not represent the numeric subscripts
on propositional variables and states in unary notation.
The point is this. Even binary representations (which are longer than the more
familiar decimal representations) are exponentially more compact than unary ones.
For example, the representation of the number 64 in unary is a string of 64 con-
secutive ones, whereas its representation in binary is 1000000. If we represent our
subscripts in unary, we are using a highly inefﬁcient representation of the problem.
For this reason we will regard modal formulas (for the basic modal language)
as strings over the alphabet
fp,
0,
1,
(,
),
^,
:,
3g, and proposition letters will



6.1 Computing Satisﬁability
339
be represented by strings consisting of
p followed by the binary representation of
a number (without leading zeroes). Similarly, we will regard models as strings
over the alphabet
fw,
p,
0,
1,
;,
h,
ig. A state in a model will be represented by
w followed by the binary representation of a number (without leading zeroes), and
the representation of proposition letters (which we need to encode the valuation)
will be as just described. A string representing a model will have the following
form:

hw
1
;
:
:
:
;
w
n
i;
hhw
i
;
w
j
i;
:
:
:
;
hw
k
;
w
l
ii;
hhp
x
;
hw
r
;
:
:
:
;
w
s
ii;
:
:
:
;
hp
y
;
hw
t
;
:
:
:
;
w
u
ii

;
where
1

i,
j,
k,
l,
r,
s,
t,
u

n. Such triples represent models in the obvious
way: the ﬁrst component gives the states, the second the relation, and the third the
valuation. The subscripted
w’s and
p’s are metavariables over our representations
of states and proposition letters, respectively. We assume that our representations
of models contain no repetitions in any of the three components, and that they sat-
isfy obvious well-formedness conditions (in particular, the third component rep-
resents a function, thus we cannot have the same representation
p
y appearing as
the ﬁrst item in different tuples). Here is a simple example (though to keep things
readable we have represented the numbers in decimal):
A model
q
p
p
   
t
t
@
@
@
I
t

hw
1
;
w
2
;
w
3
i;
hhw
1
;
w
2
i;
hw
1
;
w
3
ii;
hhp
1
;
hw
1
;
w
2
ii;
hp
2
;
hw
3
iii

Its representation
Such representations open the door to all the standard concepts of computability
theory and computational complexity. For a start, it now makes sense to describe
sets of formulas (including normal modal logics), sets of models, and sets of frames
as being recursively enumerable (r.e.), or as being recursive. Saying that a set is
r.e. means that it is possible to write a Turing machine that will successively output
all and only its elements. Saying that a set is recursive means that it is possible to
write a Turing machine which, when given any input, will perform a ﬁnite number
of computation steps, halt, and then correctly tell us whether the input represents
a member of the set or not. (In short, recursive sets are those for which we can
decide membership using a terminating computation.)
Furthermore, it is clearly possible to program a Turing machine so that when it
is presented with (the representations of) a formula, a model, and a point, it will
evaluate (the representation of) the formula in (the representation of) the model at
(the representation of) the point. Admittedly it would be rather painful to write out



340
6 Computability and Complexity
such a Turing machine in detail — but it is straightforward to write a program to
carry out this task in most high-level programming languages; hence, by Church’s
Thesis (see Section C), it is possible to write a Turing machine to do the job as
well. Thus it makes perfectly good sense to talk about writing Turing machines
which test for the satisﬁability or validity of a formula on a class of ﬁnitely based
models and to inquire about the complexity of such problems.
Apart from asking the reader to generalize the above representation schema to
cover modal languages of arbitrary similarity type (see Exercise 6.1.2) we will not
discuss the issue of representation further. In most of what follows we talk as if the
abstract deﬁnition of satisﬁability and validity problems given earlier was the focus
of our computational investigations. For example, we will often call
jj the size
of the input formula; strictly speaking, it is the size of its representation. Nor do
we mention Turing machines very often. The results of this chapter rest on the fact
that there is an efﬁcient representation which enables us to compute satisﬁability
and validity problems; for many purposes we can ignore the details.
Exercises for Section 6.1
6.1.1 Prove Theorem 6.5. That is, show that for any modal similarity type
, any normal
modal logic in a language for
 has the ﬁnite model property if and only if it has the ﬁnite
frame property. This is simply a matter of verifying that the proof of Theorem 3.28 extends
to arbitrary similarity types — but note that there will be a gap in your proof if you haven’t
yet proved the Filtration Theorem for modal languages of arbitrary similarity type.
6.1.2 Modify the representation schema for models given above so that it can represent
any ﬁnitely based model of any modal similarity type.
6.1.3 Show that if
 is the normal modal logic generated by an r.e. set of formulas, then

itself is an r.e. set. (The reader unfamiliar with this type of proof may ﬁnd it useful to look
at the proof of Lemma 6.12 below.)
6.2 Decidability via Finite Models
Call a normal modal logic
 decidable if the
-satisﬁability (or equivalently:
-
validity) problem is decidable, and undecidable if it is not. How should we estab-
lish decidability results? A lot depends on our ‘access’ to the logic. For example,
we may know
 purely semantically: it is given as the logic of some class of
frames of interest. However, we may also have a syntactic handle on
; in partic-
ular, we may know that it is the logic generated by some set of axioms. Whether
 is semantically or syntactically speciﬁed, establishing that it has the ﬁnite model
property is a useful ﬁrst step towards proving decidability, for if we can prove this,
two plausible strategies for establishing decidability suggest themselves, as we will
now explain.



6.2 Decidability via Finite Models
341
 Decidability for semantically speciﬁed logics: informal argument. Suppose
we only have a semantic speciﬁcation of
, but that we have been able to prove
that
 possesses a strong form of the ﬁnite model property: not only does

have the f.m.p. with respect to some set of models, but for any formula
 there
is a computable function
f such that
f
(jj) is an upper bound on the size of
these models needed to satisfy
. Write a Turing machine that takes
 as input,
generates all the ﬁnite models belonging to this set up to size
f
(jj), and tests for
the satisﬁability of
 on these models. Because
 is
-satisﬁable iff it is satisﬁed
in a
-model of size at most
f
(jj), and because the machine systematically
examines all these models, our machine decides
-satisﬁability.
 Decidability for syntactically speciﬁed logics: informal argument. Suppose

is given axiomatically, and we have been able to show that
 has the f.m.p. with
respect to some set of models M. First, construct a Turing machine that makes
use of the axiomatization to recursively enumerate the
-validities. Second, con-
struct a Turing machine that recursively enumerates all the ﬁnite models in M.
Given two such machines we can effectively test the
-validity of any formula
: if
 is valid it will eventually be generated by the ﬁrst machine; if it is not,
we will eventually be able to falsify it on a model generated by the second. One
of the machines must eventually settle
’s fate, and thus decide
-validity.
Such arguments underly most applications of the ﬁnite model property to decidabil-
ity. We have deliberately phrased both arguments rather loosely; the fundamental
goal of this section is to explore the underlying ideas more carefully, and formulate
them rigorously. Our investigation will yield three main theorems. The ﬁrst is a
precise formulation of the argument for semantically speciﬁed logics. The second
and third are distinct reformulations of the argument for syntactically speciﬁed log-
ics. We will consider a number of applications of these theorems, and will put both
of the methods introduced in Section 2.3 for constructing ﬁnite models (namely
ﬁltration and selection) to work.
Let us begin by scrutinizing the ﬁrst of the above arguments. This revolves
around a strong form of the ﬁnite model property.
Deﬁnition 6.6 (Strong Finite Model Property)
Let
 be a normal modal logic,
M a set of ﬁnitely based models such that

=
M, and
f a function mapping nat-
ural numbers to natural numbers.
 has the
f
(n)-size model property with respect
to M if every
-consistent formula
 is satisﬁable in a model in M containing at
most
f
(jj) states.
 has the strong ﬁnite model property with respect to M if there is a computable
function
f such that
 has the
f
(n)-size model property with respect to M.
 has
the polysize model property with respect to M if there is a polynomial
p such that
 has the
p(n)-size model property with respect to M.



342
6 Computability and Complexity
 has the
f
(n)-size model property (respectively, strong ﬁnite model property,
polysize model property) if there is a set of ﬁnitely based models M such that

=
M and
 has the
f
(n)-size model property (respectively, strong ﬁnite model
property, polysize model property) with respect to M.
a
If a logic
 has the polysize model property, any
-satisﬁable formula is satisﬁable
not just on a ﬁnite model, but a genuinely small model. Even this very strong form
of the f.m.p does not guarantee decidability: as the reader is asked to prove in
Exercise 6.2.4, there are uncountably many normal modal logics which possess the
polysize model property but have undecidable satisﬁability problems.
In view of this result, the ﬁrst informal argument sketch is clearly inadequate —
but where does its deﬁciency lie? It makes the following (false) assumption: that
for any set of models, and any natural number
n, it is possible to generate all and
only the models in M of size at most
n. This assumption is warranted only if M
is a recursive set (that is, only if a Turing machine can decide exactly which ﬁnite
models belong to M). But this is the only shortcoming of the informal argument.
Theorem 6.7 If
 is a normal modal logic that has the strong ﬁnite model property
with respect to a recursive set of models M, then
 is decidable.
Proof. First, observe that for any natural number
n it is possible to generate all
distinct (representations of) models in M that have size at most
n: we need simply
write a machine that generates all distinct (representations of) models that have
size at most
n, tests each model (representation) as it is generated to see whether
it belongs to M (this is the key point: we can effectively test for membership in
M precisely because M is a recursive set) and then outputs exactly those models
(representations) which do belong to M. (From now on we drop all mention of
representations, and will speak simply of ‘generating all models’ or ‘generating all
models up to size
n’, and so on.)
So, given
, we use this machine to generate all models of the appropriate set up
to size
f
(), and test whether
 is satisﬁable on any of the models it produces. If

is satisﬁable on at least one of them, it is
-satisﬁable; if not, it is not
-satisﬁable,
for
 has the strong f.m.p. with respect to M.
a
Theorem 6.7 is an important result. If we are to apply it, how do we establish that a
logic has the strong ﬁnite model property? Unfortunately, no fully general answer
to this question is known — nonetheless, both ﬁltration and selection can be useful.
We start by illustrating the utility of ﬁltrations.
Corollary 6.8 K, T, KB, K4, S4, S5, K
t, K
t
4:3 and K
t
Q are decidable.
Proof. First, all these logics have the f.m.p. with respect to the expected sets of
models; for example, K4 has the f.m.p. with respect to the set of ﬁnite transitive



6.2 Decidability via Finite Models
343
models, and K
t
Q has the f.m.p with respect to the ﬁnite dense unbounded weak
total orders (that is, the ﬁnite DUWTO frames; see Theorem 4.41). The easiest
way to prove this is to use ﬁltrations. In Section 2.3 we deﬁned ﬁltrations for
both the basic modal language and the basic temporal language. Given a model
M
that satisﬁes a formula
 at some state, by ﬁltrating
M through the set of all
’s
subformulas we obtain a ﬁnite model
M
f that satisﬁes
. Of course, we need to be
careful that
M
f has all the right properties; for example, if
M was a K4-model, we
want
M
f to be a K4-model as well. By and large this is straightforward, though the
reader will need to think a little about how to handle density; see Exercise 6.2.1.
Such ﬁltration arguments actually establish the strong f.m.p. for these logics. If
we form
M
f by ﬁltrating
M through the subformulas of
, then
M
f has at most
2
jj nodes, thus we have a computable (though, unfortunately, exponential) upper
bound on the size of satisfying models for all these logics; see Section 2.3.
It remains to check that the relevant sets of ﬁnite models are recursive. Checking
for membership in these sets boils down to checking that the models possess (vari-
ous combinations of) such properties as reﬂexivity, transitivity, trichotomy, and so
on. It is clearly possible to devise algorithms to test for the relevant properties,
hence (by Church’s thesis) we can program a Turing machine to do so. Thus The-
orem 6.7 applies, and all these logics are decidable.
a
Filtration is a widely used technique for showing that logics have the strong ﬁnite
model property, but it has limitations. Suppose we are working with a modal lan-
guage containing
n unary modal operators (n
>
0) and no others. Let
F
n
1 be the set
of frames for this language such that for each
F
2
F
n
1, the relation corresponding
to each modality is a partial function, let
M
n
1 be the set of models built over
F
n
1,
and let K
nAlt
1 be its logic. Now, K
nAlt
1 has the strong ﬁnite model property, but
there is no obvious way of using ﬁltrations to show this; see Exercise 6.2.3.
However — at least in the present case — it is straightforward to use selection,
the other method of building ﬁnite models discussed in Section 2.3, to establish the
strong ﬁnite model property.
Corollary 6.9 K
nAlt
1 is decidable.
Proof. We argue as follows. Suppose
M is in
M
n
1 and
M;
w

. Let
M
0 be the
model that is identical to
M save possibly that any relations in
M
0 not correspond-
ing to modal operators in
 are empty. Clearly
M
0 is also in
M
n
1 and
M
0
;
w

.
Let
m be the degree of
 (that is, the maximal depth of nested modalities; see Deﬁ-
nition 2.28). Let
M
00 be the submodel of
M
0 formed by selecting all and only those
nodes reachable from
w in
m or fewer steps. Clearly
M
00 is in
M
n
1 and
M
00
;
w

.
Moreover, because each relation is a partial function,
M
00 has only ﬁnitely many
nodes: indeed, it can contain at most
t
m
+
1 nodes, where
t is the number of dis-



344
6 Computability and Complexity
tinct types of modality that occur in
. Hence K
nAlt
1 has the strong ﬁnite model
property with respect to
M
n
1.
It is clear that the set of ﬁnitely based
M
n
1 models is recursive, for testing whether
a ﬁnite model
M belongs to it essentially boils down to checking that each of
M’s
(ﬁnitely many non-empty) transition relations is a partial function. Decidability
follows by Theorem 6.7.
a
Selection is not as general a method as ﬁltration — but it can be useful, espe-
cially when working with non-transitive models. As we will see when we discuss
NP-completeness, selection is a natural way of turning a ﬁnite model (perhaps pro-
duced via a ﬁltration) into a truly small (that is, polysize) model.
Theorem 6.7, together with such methods as ﬁltration and selection, can be a
useful tool for establishing modal decidability results, for it does not require us to
have an axiomatization. Very often we do have an axiomatization at our disposal,
and it is natural to ask whether (and how) we can make use of it to help establish
decidability. This is what the second informal argument attempts to do. The key
idea it embodies is the following: if a logic is both axiomatizable and has the ﬁnite
model property with respect to some (recursively enumerable) set of models M,
then we should be able to prove decidability. This is an important idea that can be
developed in two different ways, depending on the kind of axiomatization we have,
and what we know about the computational properties of M.
When we discussed completeness in Chapter 4, we viewed axiomatizations very
abstractly: we simply said that if
 was a normal modal logic,
 a set of modal
formulas, and
K (the smallest normal logic generated by
) equaled
, then

was an axiomatization of
. To give computational content to the phrase ‘gener-
ated by’ we need to impose restrictions on
, for under the deﬁnition just given
every normal logic
 generates itself. This is too abstract to be useful here, so we
will introduce various notions of axiomatizability that offer more computational
leverage.
Deﬁnition 6.10 A logic
 is ﬁnitely axiomatizable if it has a ﬁnite axiomatization
; it is recursively axiomatizable if it has a recursive axiomatization
; and it is
axiomatizable if it has a recursively enumerable axiomatization
.
a
Although it won’t play a major role in what follows, there is a neat result called
Craig’s Lemma that readers should know: every axiomatizable logic is recursively
axiomatizable. So the following lemma is essentially Craig’s Lemma for modal
logic:
Lemma 6.11 If
 is axiomatizable, then
 is recursively enumerable.
So, given a computationally reasonable notion of axiomatizability, the idea of using
axiomatizations to generate validities is correct. But how do we use this fact to turn



6.2 Decidability via Finite Models
345
the informal argument into a theorem? Here’s the most obvious way: demand that
M be an r.e. set. As the following lemma shows, this ensures that we can recursively
enumerate the formulas that are not valid on M.
Lemma 6.12 If M is a recursively enumerable set of ﬁnite models, then the set of
formulas falsiﬁable in M is recursively enumerable.
Proof. As M is an r.e. set, we can construct a machine M1 to generate all its ele-
ments, and clearly we can construct a machine M2 that generates all the formulas.
So, construct a machine M3 that operates as follows: it calls on M1 to generate a
model, and on M2 to generate a formula, and then stores both the model and the
formula. It then tests all stored formulas on all stored models (M3 is not going to
win any prizes for efﬁciency) and outputs any of the stored formulas it can falsify
on some stored model. At any stage there are only ﬁnitely many stored formulas
and models, hence this testing process terminates. When the testing process is ﬁn-
ished, M3 calls on M1 and M2 once more to generate another model and formula,
stores them, performs another round of testing, and so on ad inﬁnitum.
Suppose
 is falsiﬁable on some model
M in M. At some ﬁnite stage both

and
M will be stored by M3, hence
 will eventually be tested on
M, falsiﬁed,
and returned as output. This means that the set of formulas falsiﬁable on
M is
recursively enumerable.
a
Theorem 6.13 If
 is an axiomatizable normal modal logic that has the ﬁnite
model property with respect to an r.e. set of models M, then
 is decidable.
Proof.
 is r.e. by Lemma 6.11. But the set of formulas not in
 is also r.e. for

=
M and the set of formulas that are not M-valid is r.e. by the previous lemma.
Any formula
 must eventually turn up on one of these enumerations, hence
 is
decidable.
a
As an application, we will show that the minimal propositional dynamic logic is
decidable.
Corollary 6.14 PDL is decidable.
Proof. By Theorem 4.91, PDL is complete with respect to the set of all regular
PDL-models. The axioms of PDL clearly form a recursive set, so trivially they
form a recursively enumerable set, thus to be able to apply the Theorem 6.13 it
only remains to show that PDL has the ﬁnite model property with respect to an r.e.
set of models.
This follows easily from our completeness proof for PDL. Recall that we proved
completeness by constructing, for any consistent formula
, a ﬁnite model
P that
satisﬁed
. This gives us what we want, modulo the following glitch: although



346
6 Computability and Complexity
P contains only ﬁnitely many nodes, it may contain inﬁnitely many non-empty
relations, thus it may not be of ﬁnite character and thus (strictly speaking) our
completeness proof does not establish that PDL has the ﬁnite model property. This
is a triviality: for any formula
, only ﬁnitely many of the relations on
P are
relevant to the satisﬁability of
, namely those that actually occur in
. Let
R
 be
the smallest set that contains all the relations in
P corresponding to modalities in
 and is downward closed under the usual relation constructors (that is, if
R

;
0
2
R
 then so are
R
 and
R

0, and analogously for relations deﬁned by union and
transitive closure). Note that
R
 is ﬁnite. Let
P
0 be the model that is identical
to
P save that all the relations not in
R
 are empty; we call
P
0 a reduced model.
Clearly
P
0 is a ﬁnitely based model that satisﬁes
. This shows that PDL has the
ﬁnite model property.
The set of reduced models is a recursive set, since checking that a ﬁnite model is
a reduced model boils down to showing that the relations corresponding to non-
basic modalities really are generated out of simpler relations via composition,
union, or transitive closure, and this is obviously something we can write a program
to do. Hence, the relevant models are recursively enumerable, thus the conditions
of Theorem 6.13 are satisﬁed, and PDL is decidable.
a
We can also show that PDL is decidable by appealing to Theorem 6.7. As we have
just seen, our completeness proof for PDL gives us the ﬁnite model property for
PDL — but in fact it even gives us the strong ﬁnite model property. To see this,
recall that for any consistent
, we constructed
P out of atoms, that is, maximal
consistent subsets of the Fisher-Ladner closure of
fg. As there are at most
2
cjj
such atoms for some constant
c, we have a computable upper bound on the size of
the models needed to satisfy
. We noted in the proof of Corollary 6.14 that the
relevant ﬁnite models (the reduced models) form a recursive set, hence we have
established everything we need to apply Theorem 6.7.
Theorem 6.13 is a fundamental one and is useful in practice. It does not make
use of axiomatizations in a particularly interesting way: it uses them merely to
enumerate validities. To apply the theorem we need to know that the set of relevant
ﬁnite models is recursively enumerable. We often have much stronger syntactic
information at our disposal: we may know that a logic is ﬁnitely axiomatizable.
Our next theorem is based on the following observation: if a logic with the f.m.p.
is ﬁnitely axiomatizable, we can use the axiomatization not only to recursively
enumerate the validities, but to help us enumerate the non-validities as well.
Theorem 6.15 If
 is a ﬁnitely axiomatizable normal modal logic with the ﬁnite
model property, then
 is decidable.
Proof. As in the proof of Theorem 6.13 we can use the axiomatization to recur-



6.2 Decidability via Finite Models
347
sively enumerate
, so if we can show that the set of formulas not in
 is also r.e.
we will have proved the theorem.
By Theorem 6.5, if
 has the ﬁnite model property it also has the ﬁnite frame
property, thus there is some set of ﬁnite frames F such that

=
F. Hence,
if

62
,
 is falsiﬁable in some model based on a frame in
F. Obviously all
such frames must validate every axiom of
, hence if

62
,
 is falsiﬁable in
some model based on a frame that validates the
 axioms. Now for the crucial
observation: we can write a machine
M which decides whether or not a ﬁnite
frame validates the
 axioms, for as
 has only ﬁnitely many axioms, each frame
can be checked in ﬁnitely many steps. With the help of
M, we can recursively
enumerate the formulas falsiﬁable in some F-based model, but these are just the
formulas which do not belong to
. It follows that
 is decidable.
a
Can Theorem 6.15 be strengthened by replacing its demand for a ﬁnite axiomati-
zation with a demand for a recursive axiomatization? No — in Exercise 6.2.5 we
give an example of an undecidable recursively axiomatizable logic KU
X with the
ﬁnite model property; the result hinges on Craig’s Lemma.
Theorem 6.15 has many applications, for many common modal and tense logics
have the f.m.p. and are ﬁnitely axiomatizable. For example, Theorem 6.15 yields
another proof that K, T, KB, K4, S4, S5, K
t, K
t
4:3, and K
t
Q are decidable, for
all these logics were shown to be ﬁnitely axiomatizable in Chapter 4, and we saw
above that they all have the (strong) ﬁnite model property. However, a more inter-
esting application follows from our work on logics extending S4.3 in Section 4.9.
Corollary 6.16 Every normal logic extending S4.3 is decidable.
Proof. By Bull’s Theorem (Theorem 4.96) every normal logic extending S4.3 has
the ﬁnite model property, and by Theorem 4.101 every normal logic extending
S4.3 is ﬁnitely axiomatizable. Hence the result is an immediate corollary of Theo-
rem 6.15.
a
Corollary 6.16 completes the main discussion of the section. To summarize what
we have learned so far, in Theorems 6.7, 6.13, and 6.15 we have results that pin
down three important situations in which the ﬁnite model property implies decid-
ability — and indeed, most modal decidability results make use of one of these
three theorems.
Exercises for Section 6.2
6.2.1 Provide full proof details for Corollary 6.8. Pay particular attention to showing that
K
t
Q has the f.m.p. with respect to the ﬁnite DUWTO-frames (see Theorem 4.41). Filtra-
tions generally don’t preserve density, so how do we know that this ﬁltration is dense?
(Hint: trichotomy.)



348
6 Computability and Complexity
6.2.2 Show that if
 is a ﬁnitely axiomatizable normal modal logic with the ﬁnite model
property, then
 has the ﬁnite frame property with respect to a recursive set of frames.
6.2.3 . In this exercise we ask you to show that there is method of ﬁltrating a partial
function that guarantees that the resulting relation is again a partial function.
Consider the model
M
=
(N
;
S;
V
) where
S is the successor relation on the set
N of
natural numbers, and
V makes the proposition letter
p true at precisely the even numbers.
Let
 be the set
f3:p;
3p;
:p;
pg. Prove that no ﬁltration of
M through
 is based on a
frame in which
S
f is a partial function.
6.2.4 In this exercise we ask the reader to prove that there are uncountably many undecid-
able normal modal logics with the polysize model property.
Let
F
suc be the set of all ﬁnite frames
(W
;
R
) such that
W
=
f0;
:
:
:
;
k
g (for some
k
2
!) and for all
0

n
<
m

k,
R
nm iff
m
=
n
+
1. (Note that this deﬁnition permits
reﬂexive points. Indeed, any frame in this set is uniquely determined by its size and which
points, if any, are reﬂexive.) Then, for each
j
2
! deﬁne
F
j to be the set containing: (1) all
the irreﬂexive frames in
F
suc; (2) all the frames in
F
suc whose last point is reﬂexive; and
(3) the (unique)
F
suc frame containing
j
+
1 nodes such that
0 is the only reﬂexive point;
call this frame
F
j. Now deﬁne, for any non-empty
I

!,
F
I as the set
S
i2I
F
i; let

I be
its logic.
Deﬁne

j to be the formula
p
^
3p
^
3(:p
^
3
j
 1
2
?).
(a) Prove that

j is satisﬁable in
F
i iff
i
=
j.
(b) Prove that if
 is
F
i-satisﬁable, then it is satisﬁable on a frame in
F
i that contains
at most
m
+
2 points, where
m is the number of modalities in
.
(c) Prove that if
I and
J are distinct (non-empty) subsets of
! then there is a formula
that is satisﬁable in
F
I but not in
F
J.
(d) Prove that each

I has the polysize model property.
(e) Prove that there can only be countably many decidable logics. (This step is actually
the easiest one: after all, how many distinct Turing machines can there be?)
(f) Conclude that there are uncountably many undecidable normal modal logics with
the polysize model property.
6.2.5 Let
X be an r.e. subset of the natural numbers that is not recursive; assume that
0
2
X but
1
62
X. Then KU
X is the smallest normal modal logic containing the following
formulas:
(U1)
3(3p
^
3q
)
!
33(p
^
q
)
(U2)
3(p
^
2
?)
^
3(q
^
2
?)
!
3(p
^
q
)
(U3)
3(p
^
3>)
^
3(q
^
3>)
!
3(p
^
q
)
(U4)
k
(32
?
^33>)
!
2
k
3>, where
k
2
X.
Note that by Craig’s Lemma KU
X has a recursive axiomatization.
(a) Use Sahlqvist’s Correspondence and Completeness Theorem to ﬁnd a ﬁrst order
deﬁnable class
U of frames for which KU
X is sound and complete.
(b) Prove that KU
X has the ﬁnite model property.
(c) Show that KU
X is undecidable.
(Hint: prove that any formula U4
j with
j not in
X, is not satisﬁable in
U.)



6.3 Decidability via Interpretations
349
6.3 Decidability via Interpretations
For all its usefulness, decidability via ﬁnite models has a number of limitations.
One is absolute: as we will shortly see, there are decidable logics that lack the
ﬁnite model property. Another is practical: it may be difﬁcult to establish the ﬁnite
model property, for although ﬁltration or selection work in many cases, no univer-
sal approach is known. Thus we need to become familiar with other techniques
for establishing decidability, and in this section we introduce an important one:
decidability via interpretations, and in particular, interpretations in SnS.
A general strategy for proving a problem decidable is to effectively reduce it to
a problem already known to be decidable. But there are many decidable problems;
which of them can help us prove modal decidability results? Ideally, we would
like to ﬁnd a decidable problem, or class of problems, to which modal satisﬁability
problems can be reduced in a reasonably natural manner. Moreover, we would
like the approach to be as general as possible: not only should a large number of
modal satisﬁability problems be so reducible, but the required reductions should
be reasonably uniform.
A suitable group of problems is the satisﬁability problem for SnS (where
n
2
!
or
n
=
!), the monadic second-order theory of trees of inﬁnite depth, where each
node has
n successors. Because these problems are themselves satisﬁability prob-
lems — and indeed, satisﬁability problems for monadic second-order languages,
the kinds of language used in correspondence theory — it can be relatively straight-
forward to reduce modal satisﬁability to SnS satisﬁability. Moreover, the various
reductions share certain core ideas; for example, analogs of the standard translation
play a useful role. The method can also be used for strong modal languages, such
as languages containing the until operator
U, see Exercise 2.2.4.
In this section we introduce the reader to such reductions (or better, for reasons
which will become clear, interpretations). We ﬁrst introduce the theories SnS,
note some examples of their expressivity, and state the crucial decidability results
on which subsequent work depends. We then illustrate the method of interpreta-
tions with two examples. First, we prove that KvB, a logic lacking the ﬁnite model
property, is decidable. As KvB is characterized by a single structure (namely, a
certain general frame) this example gives us a relatively straightforward introduc-
tion to the method. We then show how the decidability of S4 can be proved via
interpretation. The result itself is rather unexciting — we already know that S4 has
the ﬁnite model property and is decidable (see Corollary 6.8) — but the proof is
important and instructive. S4 is most naturally characterized as the logic of transi-
tive and reﬂexive frames, but this is a characterization in terms of an uncountable
class of structures. How can this characterization be ‘interpreted’ in SnS? In fact,
it can be done rather naturally, and the ideas involved open the doors to a wide
range of further decidability results.



350
6 Computability and Complexity
Let us set about deﬁning SnS. If
A is some ﬁxed set (our alphabet), then
A
 is
the set of all ﬁnite sequences of elements of
A, including the null-sequence
. We
introduce the following apparatus:
(i) Deﬁne an ordering
 on
A
 by
x

y if
y
=
xz for some
z
2
A
. Clearly
this ‘initial-segment-of’ relation is a partial order. If
x

y and
x
6=
y we
write
x
<
y.
(ii) Suppose
A is totally ordered by a relation
<
A. Then we deﬁne
 to be the
lexicographic ordering of
A
 induced by
<
A. That is,
x

y if and only if
x

y, or
x
=
z
au and
y
=
z
bv where
a;
b
2
A and
a
<
A
b. Note that

totally orders
A
.
(iii) For any
a
2
A we deﬁne
r
a
:
A

!
A
, the a-th successor function, by
r
a
(x)
=
xa.
Deﬁnition 6.17 (S
nS) For any
n such that
n is a natural number, or
n
=
!, let
T
n be
fi
2
!
j
i
<
ng
. The structure
N
n is
(T
n
;
r
i
;
;
)
i<n, where
 is the
lexicographic ordering induced by
<
!, the usual ordering of the natural numbers.
N
n is called the structure of
n successor functions. (Note that all these structures
are countably inﬁnite.)
The monadic second-order theory of
n successor functions is the monadic sec-
ond-order theory of
N
n in the monadic second-order language of appropriate signa-
ture (we spell out the details of this language below); this theory is usually referred
to as SnS.
a
Let us spell out the intuitions underlying this machinery. First, note that each
structure
N
n really is an inﬁnite tree where each node has
n immediate succes-
sors (or daughters, in standard tree terminology). For example, consider
N
1; that
is
(f0g

;
r
0
;
;
). This is the inﬁnite tree in which each node has exactly one
daughter; that is, it is simply an isomorphic copy of the natural numbers in their
usual order. Next, consider
N
2, that is
(f0;
1g

;
r
0
;
r
1
;
;
). This is the full bi-
nary tree (that is, the inﬁnite tree in which every node has exactly two daughters).
An initial segment of
N
2 is shown in Figure 6.1. Note that
 is the root node of
the tree depicted in Figure 6.1, and that
r
0 and
r
1 are the ﬁrst daughter and second
daughter relations, respectively. Further, note that
 has a natural tree-geometric
interpretation: it is simply the dominates relation. That is,
x

y iff it is possible
to reach
x by moving upwards in the tree from
y. Similarly,
 is the dominates-or-
to-the-left-of relation. The tree-like nature of these models plays an important role
in the work that follows, and must be properly understood. In particular, the reader
should check that
N
! really is an inﬁnite tree in which every node has
! daughters.
So much for the structures — what about the theories? Each of the theories
SnS is a monadic second-order theory in the appropriate language. For example,
the monadic second-order language appropriate for talking about
N
2 contains two



6.3 Decidability via Interpretations
351
...
...
...
...
11
10
01
00
1
0





A
A
A
A
A
A
A
A




@
@
@
@
    Fig. 6.1. An initial segment of
N
2
function symbols for talking about
r
0 and
r
1 (we will be economical with our
notation and use
r
0 and
r
1 for these symbols) and two binary predicate symbols
for talking about
 and
 (we use
 and
 for this purpose). In addition, the
language contains a denumerably inﬁnite set of individual variables
x,
y,
z, . . . , a
denumerably inﬁnite set of predicate (or set) variables
P,
Q,
S, . . . , that range over
subsets of the domain, and the usual quantiﬁers and boolean operators. The syntax
and semantics of the language is standard; see Section A for further discussion of
monadic second-order logic.
Using these languages, we can say many useful things about
N
n. First, note that
although we did not include a primitive equality predicate, an equality predicate is
deﬁnable over
N
n:
x
=
y iff
x

y
^
y

x:
Next, note that we can deﬁne a unary predicate symbol ROOT that is true only of
the root node
:
ROOT
(x) iff
:9y
(y
<
x):
(6.1)
We can deﬁne the unary higher-order predicate ‘P is a ﬁnite set.’ Recall that a
total ordering
R on a set
S is a well-ordering if every non-empty subset of
S has
an
R-least element; it is a standard observation that
S is well ordered by
R iff
S
contains no inﬁnitely descending
R-chains. It follows that a subset
P of
T
n is ﬁnite
iff it is well-ordered by both
 and its converse, for such a set contains no inﬁnitely
descending
-chains and no inﬁnitely ascending
-chains.
FINITE
(P
) iff
(6.2)
8Q
((9x
Qx
^
8y
(Qy
!
P
y
))
!
9u
(Qu
^
8w
(Qw
!
u

w
))
^
9v
(Qv
^
8w
(Qw
!
w

v
))):
(That is,
P is ﬁnite if every non-empty subset of
P has a
-ﬁrst and a
-last



352
6 Computability and Complexity
element.) In short, monadic second-order logic is an extremely powerful language
for talking about trees — which makes the following result all the more remarkable.
Theorem 6.18 (Rabin) For any natural number
n, or
n
=
!, SnS is decidable.
That is, for any
n, it is possible to write a Turing machine which, when given
a monadic second-order formula (in the language of appropriate signature), cor-
rectly decides whether or not the formula is satisﬁable in
N
n. The proof of this
beautiful result is beyond the scope of this book; we refer the reader to the Notes
for discussion and references.
Given a modal logic
, how can we use the fact of SnS-decidability to estab-
lish
-decidability? Suppose

=
M for some class of countable models M.
The essence of the interpretation method is to attempt to construct, for any modal
formula
, a monadic second-order formula Sat-
() that does three things.
 It must encode the information in
; this is usually achieved by using some
variant of the standard translation.
 It must deﬁne a set of substructures of
N
n (for some choice of
n) which are
isomorphic copies of the models in M.
 It must bring the two previous steps together. That is, Sat-
() must be con-
structed so that it is satisﬁable in
N
n iff (the translation of)
 is satisﬁable in (a
deﬁnable substructure of
N
n that is isomorphic to) a model in
M — that is, iff

is
-satisﬁable.
If such a formula Sat-
() can be constructed, the ramiﬁcations for modal decid-
ability are clear: as SnS is decidable, we can decide whether or not Sat-
() is
satisﬁable on
N
n. As this is equivalent to deciding the
-satisﬁability of
, we will
have established that
 is decidable.
As our ﬁrst example of the method in action, we will prove the decidability of
KvB. We met this logic brieﬂy in Exercise 4.4.2; it is the logic of a certain general
frame
J. The domain
J of
J consists of
N
[
f!
;
!
+
1g (that is, the set of natural
numbers together with two further points), and the relation
R is deﬁned by
R
xy iff
x
6=
!
+
1 and
y
<
x or
x
=
!
+
1 and
y
=
!. The frame
(J
;
R
) is shown in
Figure 6.2.
A, the collection of subsets of
J admissible in
J, consists of all
X

J
such that either
X is ﬁnite and
!
62
X, or
X is co-ﬁnite and
!
2
X.
As the reader was asked to show in Exercise 4.4.2, KvB is incomplete; that is, there
is no class of frames F such that
KvB
=
F. By Theorem 6.5 it follows that KvB
lacks the ﬁnite model property. Even though it lacks the ﬁnite model property, KvB
is decidable, and we will demonstrate this via an interpretation in S2S.
Theorem 6.19 KvB is decidable.



6.3 Decidability via Interpretations
353
:
:
:



2
1
0
a
a
a


a
a
a













)





=
?
v
v
v
v
v
!
!
+
1
Fig. 6.2. The frame underlying
J. Note that
!
+
1 is related only to
!.
Proof. Let us make two initial assumptions; we will shortly show that both as-
sumptions are correct. First, let us suppose that
J
=
(J
;
R
;
A) can be isomorphi-
cally embedded in
N
2. We will refer to this isomorphic copy as
J; no confusion
should arise because of this double usage. Furthermore, let us suppose that this
isomorphic image is deﬁnable in the monadic second-order language for
N
2. That
is, suppose that there are formulas
b
J
(x),
b
R
(x;
y
) and
b
A(P
) (containing 1 free indi-
vidual variable
x, 2 free individual variables
x and
y, and 1 free predicate variable
P, respectively) such that
J
=
ft
2
T
2
j
N
2
j
=
b
J
(x)[t]g
R
=
f(t;
t
0
)
2
T
2

T
2
j
N
2
j
=
b
R(x;
y
)[t;
t
0
]g
A
=
fU

T
2
j
N
2
j
=
b
A(P
)[U
]g:
Given these assumptions, it is easy to reduce the satisﬁability problem for the gen-
eral frame to the satisﬁability problem for S2S. First, with the help of the formula
b
R, we can deﬁne a translation
T from the modal language into the second-order
language:
T
x
(p)
=
P
x
T
x
(:)
=
:T
x
()
T
x
(
^
 
)
=
T
x
()
^
T
x
( 
)
T
x
(3)
=
9y
(
b
R
xy
^
T
y
())
Note that
T
x is just the standard translation with the formula
b
R replacing the use
of a ﬁxed relation symbol. We leave it as an exercise to show that for any modal
formula
 (built out of proposition letters
p
1
;
:
:
:
;
p
n)
((J
;
R
;
A);
V
);
w

 iff
N
2
j
=
T
x
()[w
;
V
(p
1
);
:
:
:
;
V
(p
n
)]:
(6.3)
(See Exercise 6.3.1; the notation
[w
;
V
(p
1
);
:
:
:
;
V
(p
n
)] means assign the state
w
to the free variable
x, and assign the subset
V
(p
i
) to the predicate variable
P
i.)
For any modal formula
, let Sat-KvB
() be the following monadic second-order
sentence:
9P
1
:
:
:
9P
n
9x
(
b
A(P
1
)
^



^
b
A(P
n
)
^
b
J
(x)
^
T
x
()):



354
6 Computability and Complexity
It follows that
 is satisﬁable in
(J
;
R
;
A) iff
N
2
j
= Sat-KvB
(). Thus — given our
two initial assumptions — we have effectively reduced the satisﬁability problem
for KvB to the S2S-satisﬁability problem, for
 is satisﬁable on
J iff Sat-KvB
()
belongs to S2S, and by Rabin’s result it is possible to decide the latter.
Hence, to complete the proof that KvB is decidable, it only remains to show that
our assumptions were justiﬁed; that is, to show that
J really does have a deﬁnable
isomorphic image in
N
2. Given the expressive power at our disposal, this is actu-
ally rather easy to do. We will make use of the general predicates
=, ROOT, and
FINITE deﬁned in (6.1) and (6.2). In addition, we will use
x
<
1
y iff
r
1
(x)

y
^
:9z
(x

z
^
r
0
(z
)

y
):
Note that
x
<
1
y means that
x is a proper initial subsequence of
y such that
y
extends
x by a ﬁnite sequence of 1s — or, in terms of tree geometry, it is possible
to move down from
x to
y by using only the ‘second daughter’ relation.
We will now deﬁne an isomorphic image of
J in
N
2. First, we can deﬁne the
numeric part of the underlying frame as follows:
N
(x) iff ROOT
(x)
_
9y
(ROOT
(y
)
^
y
<
1
x):
The isomorphism involved should be clear: the natural number zero is taken to be
the empty sequence, and the positive integer
n is taken to be the sequence of
n 1s.
Next, we will represent
! by 0, and
!
+
1 by 00. Deﬁning these choices is easy:
OMEGA
(x)
iff
9y
(ROOT
(y
)
^
x
=
r
0
(y
))
OMEGA+1
(x)
iff
9y
(ROOT
(y
)
^
x
=
r
0
(r
0
(y
))):
Putting it all together, we deﬁne the required predicates
b
J and
b
R as follows:
b
J
(x)
=
N
x
_ OMEGA
(x)
_ OMEGA+1
(x)
b
R(x;
y
)
=
(N
y
^
(y
<
1
x
_ OMEGA
(x)))
_
(OMEGA
(y
)
^ OMEGA+1
(x)):
Clearly these two formulas deﬁne a subset of the tree domain isomorphic to
(J
;
R
).
Thus it merely remains to deﬁne
A, the class of allowable valuations. With the help
of the FINITE predicate, this is straightforward.
b
A(P
) iff
8x
(P
x
!
b
J
(x))
^
((FINITE
(P
)
^
8z
(OMEGA
(z
)
!
:P
z
))
_
8Q8x
(Qx
$
(J
x
^
:P
x)
!
(FINITE
(Q)
^
8z
(OMEGA
(z
)
!
:Qz
))))
In short, a deﬁnable isomorphic image of
J really does live inside
N
2. We conclude
that KvB is decidable.
a
While the above result is a nice introduction to decidability via interpretation, in
one respect it is rather misleading. KvB is characterized by a single structure (and



6.3 Decidability via Interpretations
355
a rather simple one at that) thus we only had to deﬁne a single isomorphic image,
and were able to do this fairly straightforwardly using S2S. However, as we saw
in Chapter 4, it is usual to characterize logics in terms of a class of structures; for
example, S4 is usually characterized as the logic of the class of reﬂexive and tran-
sitive models. Do class-based characterizations mesh well with the idea of decid-
ability via interpretations? Classes of models may contain uncountable structures
— and only countable structures can be isomorphically embedded in
N
n. And
why should we expect to be able to isomorphically embed even countable models
in inﬁnite trees?
Two simple observations clear the way. First, in many important cases, only
the countable structures in characterizing classes are required. Second, there is
a standard method for converting a model into a tree-based model, namely the
unraveling method studied in Chapters 2 and 4. Taken together, these observations
enable us to view the classes of structures characterizing many important logics
as a collection of deﬁnable substructures of
N
!. We will illustrate the key ideas
involved by proving the decidability of S4 via interpretation in S!S.
As a ﬁrst step, we claim that S4 is sound and strongly complete with respect to
the class of countable reﬂexive and transitive models. We could prove this directly
(for example, using the step-by-step method discussed in Section 4.6) but it also
follows from the following general observation. (Recall that for the duration of this
chapter, we are only working with countable languages.)
Theorem 6.20 If
 is a normal logic that is sound and strongly complete with re-
spect to a ﬁrst-order deﬁnable class of models M, then
 is also sound and strongly
complete with respect to the class of all countable models in M.
Proof. Left as Exercise 6.3.3.
a
Lemma 6.21 S4 is sound and strongly complete with respect to the class of count-
able (reﬂexive and transitive) trees.
Proof. By Theorems 4.29 and 6.20, S4 is sound and strongly complete with respect
to the class of countable reﬂexive, transitive models; that is, every S4-consistent
set of sentences
 is satisﬁable on such a model
M
=
(W
;
R
;
V
) at some point
w.
Now, (as in the proof of Theorem 4.54) let
~
M
=
(
~
W
;
~
R
;
~
V
) be the unraveling of
M
around
w, and let
M
 be
(
~
W
;
R

;
~
V
), where
R
 is the reﬂexive transitive closure
of
~
R; this model is a reﬂexive transitive tree that veriﬁes
 at its root. Moreover,
it is a countable model, for its nodes are all the ﬁnite sequences of states in
M that
start at
w, and as
M is countable, there are only countably many such sequences.
The result follows.
a
Corollary 6.22 S4 is decidable, and its decidability can be proved via interpreta-
tions.



356
6 Computability and Complexity
Proof. Let us call a subset of
N
! an initial subtree if it contains
 and is closed
under the inverse of
 (that is, if
y belongs to the subset, and
x

y, then
x
belongs to the subset). If
S is such a subtree, then

S denotes the restriction of
 to
S. Now for the key observation. Let
(
~
W
;
~
R
) be the unraveling of some
countable S4-frame
(W
;
R
) around a point
w, and let
R
 be the reﬂexive transitive
closure of
~
R. Then
(
~
W
;
R

) is isomorphic to a pair
(S;

S
) for some initial subtree
S. To see this, note that we can inductively construct an isomorphism
f from
(
~
W
;
R

) to some initial subtree as follows. First, we stipulate that
f maps the root
of
(
~
W
;
R

) to
. Next, suppose that for some
~
u
2
~
W
;
f
(
~
u) has been deﬁned to be
m. Now,
f
~
s
2
~
W
j
~
u
~
R
~
sg is a countable set as
~
W is countable, so we can enumerate
its elements. Then, if
~
s is the
i-th element in this enumeration, we stipulate that
f
(
~
s
)
=
r
i
(m). (That is, the successor of
~
u that is
i-th in our enumeration is mapped
to the
i-th successor of
m.) In short,
N
! is ‘wide enough’ to accommodate a copy
of every branch through a tree-like S4 model in a very obvious way. In fact, it is
precisely because the required isomorphisms are so simple that we have elected to
work with
N
!.
With this observed, the interpretation is easy to deﬁne. First, we deﬁne a predi-
cate ISUBTREE
(S
), which picks out the initial subtrees of
N
!:
ISUBTREE
(S
) iff
9y
(ROOT
(y
)
^
S
y
)
^
8z
8u
((S
z
^
u

z
)
!
S
u)):
Second, we deﬁne a predicate

S that deﬁnes the restriction of
 to a subset
S of
N
! by
x

S
y iff
S
x
^
S
y
^
x

y
:
Third, we deﬁne a translation
T
! from the basic modal language to the monadic
second-order language for
N
!. Like the translation
T we used when proving the
decidability of KvB this translation is a simple variant of the standard translation.
In fact, it is identical to
T save in the clause for modalities, which is given by:
T
!
x;S
(3)
=
9y
(x

S
y
^
T
!
y
;S
()):
Note that as well as containing the free individual variable
x, the translation of
3
contains a free set variable
S; when written in full the above expression becomes:
T
!
x;S
(3)
=
9y
(S
x
^
S
y
^
x

y
^
T
!
y
;S
()):
We need the free variable here because we are not working with one ﬁxed isomor-
phic image (as we were when proving the decidability of KvB). Rather, we have
a separate relation for each initial subtree, and the presence of the free variable
allows all our deﬁnitions to be relativized in the appropriate way.
It simply remains to put it all together. Suppose
 is a modal formula constructed
out of the proposition letters
p
1, . . . ,
p
n. Deﬁne Sat-S4
() to be the following



6.3 Decidability via Interpretations
357
sentence:
9S
9P
1
:
:
:
9P
n
9x
 ISUBTREE
(S
)
^
8z
(P
1
z
!
S
z
)
^



^
8z
(P
n
z
!
S
z
)
^
S
x
^
T
!
x;S
()

:
Recall that
T
!
() contains free occurrences of
S and
x; these become bound in
this sentence. Bearing this in mind, it is clear this sentence asserts the existence of
an initial subtree
S of
N
!, a collection of
n subsets
P
i of this subtree, and a state
x in the subtree, that satisfy the translation of
. That is, it asserts the existence
of a tree-like S4 model for the (translation of)
, and we have reduced the
S4-
satisﬁability problem to the S!S-satisﬁability problem.
a
This completes our discussion of interpretations in SnS — though we should im-
mediately admit that we have barely scratched the surface of the method’s poten-
tial: Rabin’s theorem is very strong, the ideas underlying it make contact with many
branches of mathematics, and it has become a fundamental tool in many branches
of logic and theoretical computer science. Nonetheless, our discussion has un-
earthed themes relevant to modal logic: the importance of establishing complete-
ness results with respect to classes of countable structures, the use of unraveling
to produce tree-like models, and the particular utility of
N
! in allowing reasonably
straightforward isomorphic embeddings. These three ideas enable a wide range of
modal decidability results to be proved via interpretations.
One ﬁnal remark: while SnS is important, it is certainly not the only logical sys-
tem in which modal logics can be interpreted. Many fragments of classical logic,
or theories in classical logics, are known to be decidable, and offer opportunities
for proving modal decidability results. Indeed we have already met a (very simple)
example. We pointed out in Section 2.4 that the basic modal language translates
into the 2 variable fragment of classical logic, (see Proposition 2.49), from which it
immediately follows that K (and some simple extensions such as T) are decidable.
Moreover, on occasions it can be useful to interpret a modal logic in another modal
logic already known to be decidable. See the Notes for further discussion.
Exercises for Section 6.3
6.3.1 We claimed that the general frame for KvB is isomorphically embedded in the tree
domain, and that
b
R deﬁnes the accessibility relation of this isomorphic image. Check this
claim, and show that
((W
;
R
;
A);
V
);
w

 iff
N
2
j
=
T
x
()[w
;
V
(p
1
);
:
:
:
;
V
(p
n
)];
for any modal formula
 (see (6.3)).
6.3.2 Show by interpretation in S2S that both the tense logic of the natural numbers, and
the tense logic of the integers, are decidable. Now add the until operator
U to your language
(this operator was deﬁned in Chapter 2 in Exercise 2.2.4). Are the logics of the natural
numbers and the integers in this richer language still decidable?



358
6 Computability and Complexity
6.3.3 Prove Theorem 6.20. That is, show that if
 is a normal logic that is sound and
strongly complete with respect to a ﬁrst-order deﬁnable class of models M, then
 is also
sound and strongly complete with respect to the class of all countable models in M. (Hint:
use the standard translation and the Downward L¨owenheim-Skolem Theorem.)
6.4 Decidability via Quasi-models and Mosaics
In this section we will show that such familiar techniques as ﬁltration can be em-
ployed to prove decidability, even for logics lacking the ﬁnite model property. The
key move is simply to think more abstractly: instead of trying to work with ﬁnite
models themselves, we will work with ﬁnite structures which encode information
about models.
Quasi-models for
KvB
For our ﬁrst example we will re-examine the logic
KvB, which we proved de-
cidable in the previous section via interpretation in S2S. Recall that
KvB is the
logic of a single general frame
J whose universe
J is
N
[
f!
;
!
+
1g, and whose
accessibility relation is
R. Also recall that
KvB is an incomplete logic, which im-
plies that it does not have the ﬁnite model property. Nonetheless, we can establish
the decidability of
KvB using a ﬁltration argument. We cannot use ﬁltration to
build a ﬁnite
KvB model (no such model exists), but we can use it to build a ﬁnite
quasi-model.
Consider a model
M
=
(J
;
R
;
V
), where
V is an admissible valuation for
J.
What kind of ﬁltration seems natural for this structure? If it were not for the point
!
+
1, it is obvious that we would go for the transitive ﬁltration. Very well then
— let’s adopt the following procedure: ﬁrst delete the point
!
+
1, then take the
transitive ﬁltration of the remainder of the frame, and ﬁnally glue a copy of the
point
!
+
1 back on to the resulting ﬁnite structure. Of course, we know that this
will not result in a ﬁnite
KvB model; but hopefully it will yield something from
which we can construct a
KvB model.
First we need the notion of a closure of a set of sentences. We will not ﬁltrate
through arbitrary subformula-closed sets of sentences; rather, we will insist on
working with sets of sentences that are closed under single negations as well.
Deﬁnition 6.23 (Closed Sets and Closures) A set of formulas
 is said to be
closed if it is closed under subformulas and single negations. That is, if

2
 and
 is a subformula of
, then

2
; and moreover if

2
, and
 is not of the
form
:, then
:
2
.
If
  is a set of formulas, then
Cl
( ), the closure of
 , is the smallest closed set
of formulas containing
 . Note that if
  is ﬁnite then so is
Cl
( ). If
 =
fg,



6.4 Decidability via Quasi-models and Mosaics
359
where
 is any modal formula, then we usually write
Cl
 for
Cl
(fg) and call this
set the closure of
.
a
Advanced track readers should note that they have already met a more elaborate
version of this idea when we proved the completeness of PDL: any Fisher-Ladner
closed set (see Deﬁnition 4.79) is closed in the sense of the previous deﬁnition.
Now for quasi-models. Let
 be some basic modal formula. A
KvB quasi-
model for
 is a pair
Q
=
(F;
) where:
(i)
F
=
(Q;
S
) is a ﬁnite frame, containing two distinct distinguished points
called
c and
1, that satisﬁes conditions F1–F5 below; and
(ii)
 is a function mapping states of
F to subsets of
Cl
 that satisﬁes the con-
ditions L0–L3 below. We call
 a labeling.
Let’s ﬁrst consider the conditions F1–F5. These are very simple, and should be
checked against Figure 6.2. If you read
c as ‘co-ﬁnite’ and view this element as the
quasi-model’s analog of
!, and view
1 as the analog of
!
+
1, the resemblance
between ﬁnite frames fulﬁlling these conditions and the frame
(J
;
R
) should be
clear.
(F1) On
Q
n
f1g,
S is trichotomous and transitive,
(F2)
S
cw iff
w
6=
1,
(F3)
S
w
c iff
w
=
c or
w
=
1,
(F4)
S
1w iff
w
=
c, and
(F5)
S
w
1 for no
w in
Q.
Note that
c is reﬂexive. Intuitively, the ﬁltration process described above squashes
! down into a cluster.
There are also conditions on the labeling. One of these conditions is that every
label should be a Hintikka set. This is an important concept, and one we will use
again later in this chapter.
Deﬁnition 6.24 (Hintikka Sets) Let
 be a closed set of formulas. A Hintikka
set
H over
 is a maximal subset of
 that satisﬁes the following conditions:
(i)
?
62
H
(ii) If
:
2
, then
:
2
H iff

62
H.
(iii) If

^
 
2
, then

^
 
2
H iff

2
H and
 
2
H.
a
It is important to realize that Hintikka sets also satisfy conditions such as the fol-
lowing: if

_
 
2
, then

_
 
2
H iff

2
H or
 
2
H. This is because in
this book we deﬁne
_ (and also
!,
$, and
>) in terms of
?,
:, and
^ (see Deﬁ-
nition 1.12). Hintikka sets need not be satisﬁable (the reader is asked to construct
a non-satisﬁable Hintikka set in Exercise 6.4.2) but items (i) and (ii) above guar-
antee that they contain no blatant propositional contradictions. If a Hintikka set



360
6 Computability and Complexity
is satisﬁable we call it an atom. Note that both the MCSs used to build canonical
models, and the special atoms used to prove the completeness of PDL are examples
of (consistent) Hintikka sets.
We are now ready for the quasi-model labeling conditions:
(L0)

2
(w
) for some
w
2
Q,
(L1)
(w
) is a Hintikka set, for each
w
2
Q,
(L2) For all
3 
2
Cl
,
3 
2
(w
) iff
 
2
(v
) for some
v with
S
w
v,
(L3) If
3 
2
(w
), then
 
2
(v
) for some
v with
S
w
v and not
S
v
w.
We take the size of a quasi-model
(Q;
S;
) to be the size of its universe
Q.
Lemma 6.25 Let
 be a formula in the basic modal language. Then
 is satisﬁable
in
J if and only if there is a quasi-model for
, of size at most
2
jj.
Proof. We leave it to the reader to prove the left to right direction; this is simply a
matter ﬁlling in the details of the ‘delete
!
+
1, ﬁltrate, glue
!
+
1 back on’ strategy
sketched above (the ﬁltration must be made through
Cl
) and the upper bound on
the size of the quasi-model follows as in any ﬁltration argument. So let’s look at
the right to left direction.
Let
Q
=
(Q;
S;
) be a quasi-model for
, let
c and
1 be the distinguished
points of the quasi-model, and let
Q
0 denote the set
Q
n
f1g. We now deﬁne an
equivalence relation

0 on
Q
0 by
w

0
v iff
w
=
v or
(S
w
v and
S
v
w
):
This really is an equivalence relation, and a more-or-less familiar one at that: the
equivalence class

w containing a reﬂexive point
w is simply the cluster that
w be-
longs to (see Deﬁnition 4.55), while the equivalence class

w containing an irreﬂex-
ive point
w is simply
fw
g. The equivalence classes on
Q
0 are naturally ordered by
the relation
 deﬁned as follows:

w


v iff
S
w
v and not
S
v
w
:
It follows from F1 that
 is a strict total ordering. Now consider an enumeration
q
0,
q
1, . . . ,
q
N of the elements of
Q
0, such that
q ﬁrst enumerates all elements of
the leftmost equivalence class, then all elements of its rightmost neighbor, and so
on. We may extend this enumeration to a map
f
:
J
!
Q by putting
f
(w
)
=
8
<
:
q
w
if
w

N
;
c
if
w
>
N or
w
=
!
;
1
if
w
=
!
+
1:
It is straightforward to check that for all
w,
v in
J,
R
w
v implies
S
f
(w
)f
(v
).
Consider, for instance, the case where
w
=
!;
R
w
v implies that
v
=
n for some



6.4 Decidability via Quasi-models and Mosaics
361
natural number
n. But then
f
(w
)
=
c and
f
(v
)
2
Q
0, so
S
f
(w
)f
(v
) follows from
F2. The other cases are left to the reader. What we have shown is that
f is a homomorphism mapping
(J
;
R
) onto
(Q;
S
)
:
(6.4)
Now consider the following valuation
V on
(J
;
R
):
V
(p)
=
fw
2
J
j
p
2
(f
(w
))g:
It is easy to see that
V is admissible in the general frame
J: if
!
2
V
(p) then by
deﬁnition of
V ,
n
2
V
(p) for all
n
>
N, so
V
(p) is co-ﬁnite.
Hence, in order to prove the lemma, it is sufﬁcient to show that
 holds some-
where in the model
(J;
V
); but this follows from L0 and the following claim:
for all
 
2
Cl
, and all
w
2
J:
J;
V
;
w

 iff
 
2
(f
(w
)):
(6.5)
We will prove this claim by induction on the complexity of
 . The base case, where
 is a propositional variable, holds by deﬁnition of
V , and the induction step for
the boolean connectives is trivial since
 labels with Hintikka sets only. Hence,
the only interesting case is where
 is of the form
3. Note that the inductive
hypothesis applies to
 and that

2
Cl
 since the set is closed under taking
subformulas.
First assume that
J;
V
;
w

3. There is a state
v with
R
w
v and
v

.
By the fact that
f is a homomorphism it is immediate that
S
f
(w
)f
(v
), while the
inductive hypothesis implies that

2
(f
(v
)). From this and L2 it follows that
3
2
(f
(w
)).
Now suppose, in order to prove the other direction of (6.5), that
3
2
(f
(w
)).
We have to show that
J;
V
;
w

3. Distinguish the following cases:
(i)
w
=
!
+
1. From this it follows that
f
(w
)
=
1, so from L2 and the fact
(F4) that
c is the only successor of
1, it follows that

2
(c). Hence from
c
=
f
(!
) and the inductive hypothesis it follows that
!

. But then it is
immediate that
!
+
1

3.
(ii)
w
6=
!
+
1. By L3 we may assume the existence of an element
q
2
Q
satisfying
S
f
(w
)q, not
S
q
f
(w
) and

2
(q
). It is obvious from
S
f
(w
)q
and
F
5 that
q
6=
1. Let
v be a pre-image of
q; from
q
6=
1 it follows
that
v
6=
!
+
1. Since
R is trichotomous on
J
n
f!
+
1g, we have
R
v
w
or
w
=
v or
R
w
v. The ﬁrst two options are impossible:
R
v
w would imply
S
f
(v
)f
(w
), while
w
=
v is incompatible with the fact that
S
f
(v
)f
(w
) but
not
S
f
(w
)f
(v
). Hence, we ﬁnd that
R
w
v; but the induction hypothesis
gives
v

, so indeed we have
w

3.
This ﬁnishes the proof of (6.5) and hence, of the lemma.
a
Theorem 6.26 The logic
KvB is decidable.



362
6 Computability and Complexity
Proof. By Lemma 6.25 it sufﬁces to show that it is decidable whether there is a
quasi-model for
 of size not exceeding
2
jj. But this is easy to see: we ﬁrst
make a ﬁnite list of all triples
(Q;
S;
) such that
jQj

2
jj,
S

Q

Q and

:
Q
!
P
(Cl

); we then check for each member of this list whether it is a quasi-
model for
. And clearly it is possible to write a terminating program which does
this.
a
The important lesson is that in order to prove decidability of a logic, not only ﬁnite
models are useful: rather, any ﬁnite structure that encodes a model is potentially
valuable. Now, the ﬁnite structure employed in the previous example was still very
much like a model — as our name ‘quasi-model’ indicates — but in the general
case one can push the idea much further. The satisﬁability of
 doesn’t need to be
witnessed by a ﬁnite model for
, or indeed by anything that looks very much like
a model; all we need is a ﬁnite toolkit which contains the instructions needed to
construct a model for
. The concept of a mosaic develops this line of thought.
Mosaics for the tense logic of the naturals
Consider the frame
N
=
(N
;
<) with
< the standard ordering of the natural num-
bers, and let
K
t
N be its tense logic.
K
t
N does not have the ﬁnite model property
(see Exercise 6.4.1), but it is decidable, as we will now show using mosaics.
We use the following terminology and notation. For a given formula
 in the
basic temporal similarity type, let
Cl
 denote the smallest subformula closed set
containing
 (note that we use the same notation as before, but for a different set
since we are dealing with a different similarity type).
Deﬁnition 6.27 (Bricks) A brick is a pair
b
=
(;
) such that
 and
 are
Hintikka sets satisfying
(B0) if
G 
2
, then
G 
;
 
2
,
(B1) if
H
 
2
, then
H
 
;
 
2
.
A brick is called small if it satisﬁes, in addition:
(B2) if
F
 
2
, then either
 or
F
 is in
,
(B3) if
P
 
2
, then either
 or
P
 is in
.
What we are really interested in are sets of bricks satisfying certain saturation con-
ditions. A brick set
B is a saturated set of bricks for
 (in short: a
-SSB) if it
satisﬁes
(S0) for some
(;
),
H
?
2
 and

2

[
,
(S1) for all
(;
)
2
B, if
F
 
2
 then there is a
(;
 )
2
B with
 
2
 ,
(S2) for all
(;
)
2
B there is a path of small bricks leading from
 to
.



6.4 Decidability via Quasi-models and Mosaics
363
Here we say that a path of (small) bricks from
 to
 is a sequence
(
0
;

0
), . . . ,
(
n
;

n
) (n

0) of (small) bricks such that

=

0,

=

n and

i+1
=

i
for all
i
<
n. Finally, we simply deﬁne the size of an SSB
B to be the number of
bricks in
B.
a
The best way of grasping the intuitive meaning of these notions is by reading the
proof of the next lemma.
Lemma 6.28 If
 is satisﬁable in
N, then there is a
-SSB of size at most
2
2jj.
Proof. Assume that we have a valuation
V on
N such that
 is true at the number
k. For any number
n, let
 n denote the truth set of
n:
 n
=
f 
2
Cl

j
N;
V
;
n

 
g:
Deﬁne
B as the set
B
=
f( n
;
 m
)
j
n
<
mg;
and call a brick sequential if it is of the form
( n
;
 n+1
) for some number
n. We
now prove that
B satisﬁes the conditions B0–B3 and S0–S2.
For B0, assume that
G 
2
 n and that
n
<
m; we have to prove that both
G 
and
 belong to
 m. But from the assumption it follows that
N;
V
;
n

G . This
implies that
n
0

 for all
n
0
>
n; in particular,
m

 . But also
m

G , by
transitivity of
<. By deﬁnition of
 m then we have
G 
2
 m and
 
2
 m. B1 is
proved in a similar way.
For B2, take an arbitrary sequential brick
( n
;
 n+1
) and assume that
F
 
2
 n.
By deﬁnition,
N;
V
;
n

F
 , so there must be some
m
>
n with
m

 . Note
that either
m
=
n
+
1 or
m
>
n
+
1; in the ﬁrst case, we obtain
 
2
 n+1, in the
second,
F
 
2
 n+1. B3 is proved similarly, hence all sequential bricks are small.
It is likewise straightforward to prove the saturation conditions. For example, in
order to prove S0, we consider the brick
( 0
;
 k
) (recall that
k is the state where

holds).
Finally, the collection
f n
j
n
2
N
g is a subset of the power set of
Cl
, whence
its cardinality does not exceed
2
jj; but then the size of
B can be at most
(2
jj
)
2
=
2
2jj.
a
We now show that we have recorded enough information in the deﬁnition of a
saturated set of bricks for
 to construct an
N-based model for
.
Lemma 6.29 If there is a
-SSB, then
 is satisﬁable in
N.
Proof. Assume that
B is a saturated set of bricks for
. We will use these bricks
to build, step by step, the required model for
. As usual, in each ﬁnite stage
of the construction we are dealing with a ﬁnite approximation of this model: a



364
6 Computability and Complexity
history is a pair
(L;
) such that
L is a natural number and
 is a function on the
set
f0;
:
:
:
;
Lg to the set of atoms. Such a history
(L;
) is supposed to satisfy the
following constraints:
(H0)
H
?
2
(0).
(H1) for all
m with
m
<
L,
((m);
(m
+
1)) is a small brick.
We leave it to the reader to verify that any history
(L;
) has the following proper-
ties:
(H2) if
F
 
2
(n) for some
n
<
L, then there is some
m with
n
<
m

L and
 
2
(m), or otherwise
F
 
2
(L).
(H3) if
P
 
2
(n) for some
n

L, then there is some
m with
m
<
n and
 
2
(m).
The importance of the properties H2 and H3 is that they show that the only essential
shortcomings of a history (regarded as a ﬁnite approximation of a model) are of the
form ‘F
 
2
(L), and there is no witness for this fact; that is, no
m
>
L such that
 
2
(m).’
Of course, we are not going to use histories in isolation; we say that one history
(L
0
;

0
) is an extension of another history
(L;
), notation:
(L;
)

(L
0
;

0
), if
L
<
L
0, while
 and

0 agree on the domain of
. The crucial extension lemma of
the step-by-step construction is given in the following claim.
Any history
(L;
) with
F
 
2
(L)
has an extension
(L
0
;

0
) with
 
2

0
(L
0
):
(6.6)
To prove (6.6), let
(L;
) be a history and
 a formula such that
F
 
2
(L). It
follows from H1 that
((L
 1);
(L)) is a brick, so by S1 there is a brick
(;
)
in
B such that

=
(L) and
 
2
. We now use S2 to ﬁnd a path of small bricks
(
0
;

1
),
(
1
;

2
), . . . ,
(
k
 1
;

k
), such that

0
=
 and

k
=
. Obviously
we are going to ‘glue’ this path to the old history, thus creating a new history
(L
0
;

0
). To be precise,
L
0 is deﬁned as
L
0
=
L
+
k, while

0 is given by

0
(n)
=

(n)
if
n

L

i
if
n
=
L
+
i
:
With this deﬁnition
(L
0
;

0
) satisﬁes the condition of (6.6).
Using (6.6), by a standard step by step construction one can deﬁne a sequence
(L
0
;

0
)

(L
1
;

1
)
 . . . of histories such that
H
?
2

0
(0) and

2

0
(L
0
),
while for each
i and each formula
F
 
2

i
(L
i
) there is a
j
>
i and a number
L
i
<
m

L
j such that
 
2

j
(m). This sequence of nested histories will be our
guideline for the deﬁnition of a valuation on
N. Note that for all formulas
 and
all
i and
n, we have that
if
n

L
i
; then
 
2

i
(n) iff
 
2

j
(n) for all
j

i:



6.4 Decidability via Quasi-models and Mosaics
365
In other words, the histories always agree where they are deﬁned; this fact will be
used below without explicit comment.
Now consider the following valuation
V on
N:
V
(p)
=
fn
2
N
j
p
2

i
(n) for some
i
g:
We are now ready to prove the crucial claim of this lemma.
For all
 
2
Cl
 and all
n:
N;
V
;
n

 iff
 
2

i
(n) for some
i:
(6.7)
Obviously, (6.7) will be proved by induction on
 . The base step and the boolean
cases of the induction step are straightforward and we leave them to the reader; we
concentrate on the modal cases.
First assume that
 is of the form
F
. For the direction from left to right,
assume that
N;
V
;
n

F
. There must be a number
m
>
n with
m

; so by the
inductive hypothesis, there is an
i with

2

i
(m). It is easy to show (by backward
induction and H1) that this implies
F

2

i
(k
) for all
k with
n

k
<
m.
For the other direction, assume that
F

2

i
(n) for some
i. It follows from H2
that there is either a number
m with
n
<
m

L
i and

2

i
(m), or otherwise
F

2

i
(L
i
). In the ﬁrst case we use the inductive hypothesis to establish that
m

 and hence,
n

F
. Hence, assume that we are in the other case:
F

2

i
(L
i
). Now our sequence of histories is such that this implies the existence of a
history
(L
j
;

j
) with
j
>
i and such that

2

j
(m) for some
m with
L
i
;
m

L
j.
It follows from the inductive hypothesis that
m

; thus the truth deﬁnition gives
us that
n

F
.
Now assume that
 is of the form
P
. The direction from left to right is as in
the previous case. For the other direction, assume that
P

2

i
(n) for some
i; it
follows by H3 that there is an
m
<
n with

2

i
(m). The inductive hypothesis
yields that
M;
V
;
m

, so by the truth deﬁnition we get
n

F
.
a
Theorem 6.30
K
t
N is decidable
Proof. Immediate by Lemmas 6.28 and 6.29, and the obvious fact that it is decid-
able whether there is a
-SSB of size at most
2
2jj.
a
A wide range of modal satisﬁability problems can be studied in using quasi-models
and mosaics. Indeed, such methods are not only useful for establishing decidability
results, they can be used to obtain complexity results as well; see the Notes for
further references.
Exercises for Section 6.4
6.4.1 Prove that
K
t
N does not have the ﬁnite model property.



366
6 Computability and Complexity
6.4.2 Give an example of an unsatisﬁable Hintikka set. (Hint: work with the closure of
f2(p
^
q
);
:2p;
:2q
g.)
6.4.3 Extend our proof of the decidability of the tense logic of the natural numbers to a
similarity type including the next time operator
X. The semantics of this operator is given
by
(N;
V
);
n

X
 iff
(N;
V
);
n
+
1

:
6.4.4 Let
F
2 be the class of frames for the basic modal similarity type in which every point
has exactly two successors. Use a mosaic argument to prove that this class has a decidable
satisﬁability problem.
6.4.5 In this exercise we consider a version of deterministic PDL in which every program
is interpreted as a partial function — at least, in the intended semantics. The syntax of this
language is given by

::=
p
j
?
j
:
j

1
^

2
j
h
i
(p a proposition letter)

::=
a
j

1
;

2
j
if
(;

1
;

2
)
j
rep
eat
(
;
)
(a an atomic program)
:
In a regular model
M for this language, each relation
R
a is a partial function, and the
interpretation of the composed programs is given in the obvious way. That is,
R

1
;
2 is
the relational composition of
R

1 and
R

1;
R
if
(;
1
;
2
)
st holds if either
M;
s

 and
R

1
st or else
M;
s
6
 and
R

2
st. Finally, we have
R
r
ep
e
at
(
;)
st if there is a path
sR

t
1
R

t
2
:
:
:
R

t
n
=
t from
s to
t such that
n

1 and
t
=
t
n is the ﬁrst
t
i where

holds.
(a) Prove that in a regular model, each program
 is interpreted as a partial function.
(b) Prove that the class of regular models has a decidable theory over this language.
(Hint: use mosaics (bricks) of the form
(;
;

) where
 and
 are Hintikka sets
and
 is a set of programs closed under some natural conditions.)
6.5 Undecidability via Tiling
There are lots of undecidable modal logics; indeed, even uncountably many with
the polysize model property (see Exercise 6.2.4). Moreover, there are undecid-
able modal logics which in many other ways are rather well-behaved (we saw an
example in Exercise 6.2.5). Nice as they are, these examples do not really make
clear just how easily undecidable modal logics can arise, nor how serious the un-
decidability can be. This is especially relevant if we are working with the richer
modal languages (such as PDL) typically used in computer science and other appli-
cations, and the ﬁrst goal of this section is to show that natural (and on the face of it,
straightforward) ideas can transform simple decidable logics into undecidable (or
even highly undecidable) systems. While the examples are interesting in their own
right, this section has a second goal: to introduce the concept of tiling problems.
Given a modal satisﬁability problem
S, to prove that
S is undecidable we must
reduce some known undecidable problem
U to
S. But which problems are the
interesting candidates for reduction? Unsurprisingly, there is no single best answer



6.5 Undecidability via Tiling
367
to this question. As with decidability proofs, proving undecidability is something
of an art: it can be very difﬁcult, and there is no substitute for genuine insight
into the satisﬁability problem. Certain problems lend themselves rather naturally
to modal logic, and tiling problems are a particularly nice example.
What is a tiling problem? In essence, a jigsaw puzzle. A tile
T is simply a
1

1
square, ﬁxed in orientation, each side of which has a color. We refer to these four
colors as
right
(T
),
left
(T
),
up
(T
), and
down
(T
). Figure 6.3 depicts an example.
(We have used different types of shading to represent the different colors.)
@
@
@
@
    @
@
@
@
    s
s
s
s
s
s
s
s
s
s
@
@
@
@
    s
s
s
s
s
s
s
s
s
s
@
@
@
@
    s
s
s
s
s
s
s
s
s
s
@
@
@
@
    @
@
@
@
    Fig. 6.3. Six distinct tile types.
Six tiles are shown in Figure 6.3. Note that if we rotated the third tile 180
degrees clockwise, it would look just like the fourth tile, and that if we rotated the
ﬁrst tile 180 degrees clockwise it would look just like the sixth tile. We ignore
such similarities. (This is what we meant when we said that tiles are ‘ﬁxed in
orientation.’) That is, the diagram shows six distinct types of tile.
Now for a simple tiling problem:
Is it possible to arrange tiles of the type just shown on a
2

4 grid in such a
way that adjacent tiles have the same color on the common side?
A little experimentation shows that this is possible. A solution is given in Fig-
ure 6.4.
s
s
s
s
s
s
s
s
s
s
@
@
@
@
    s
s
s
s
s
s
s
s
s
s
@
@
@
@
    @
@
@
@
    @
@
@
@
    s
s
s
s
s
s
s
s
s
s
@
@
@
@
    s
s
s
s
s
s
s
s
s
s
@
@
@
@
    @
@
@
@
    @
@
@
@
    Fig. 6.4. A
2

4 tiling.
This simple idea of pattern-matching underlying tiling problems gives rise to a
family of problems which can be used to analyze computational complexity and
demonstrate undecidability. This is the general form that tiling problems take:
Given a ﬁnite set of tile types
T , can we cover a certain part of
Z

Z in such
a way that adjacent tiles have the same color on the common edge? (Below,
covering a grid with tiles so that adjacent colors match will be called ‘tiling’.)



368
6 Computability and Complexity
Some tiling problems impose additional constraints on what counts as a successful
tiling (we will shortly see an example) and some are formulated as games to be
played between two players (we will see an example at the end of this chapter).
To spell this out somewhat, we might describe our previous example as an in-
stance of the
2

4 tiling problem. That is, we were given a ﬁnite set of tile types
(six, to be precise), asked to tile a
2

4 grid, and no further constraints were im-
posed. In the remainder of this section, we are going to make use of two much
harder tiling problems. The ﬁrst is the:
N

N tiling problem. Given a ﬁnite set of tile types
T , can
T tile
N

N?
Here is a simple instance of this problem: can we tile
N

N using the six tile types
shown? Of course! We need simply ‘slot-together’ copies of our solution to the
2

4 problem.
In general, however, the
N

N tiling problem is hard, and in fact it is known
to be undecidable. Indeed, this problem is

0
1-complete; that is, it is a paradig-
matic example of ‘ordinary undecidability.’ (See Section C for further discussion
of degrees of undecidability.) We won’t prove this result here — see the Notes for
references — but it is really quite straightforward: think of each row of tiles as
encoding Turing machine tapes and states, and the matching process as governing
the state transitions.
The second problem we will use is the:
N

N recurrent tiling problem. Given a ﬁnite set of tile types
T , which
includes some distinguished tile type
T
1, can
T tile
N

N in such a way that
T
1 occurs inﬁnitely often in the ﬁrst row?
As an easy example, note that our previous six tile types recurrently tile
N

N
when either the ﬁrst, the third, the fourth, or the sixth tile type is distinguished.
Now our new problem is just the
N

N tiling problem with an additional con-
straint imposed — but what a difference this constraint makes! Not only is this
problem undecidable, it is

1
1-complete (again, see Section C).
We will prove two modal undecidability results with the aid of these problems.
Both examples are based around a natural variant of Deterministic Propositional
Dynamic Logic, with intersection replacing choice and iteration as program con-
structors; we call this variant KR. We obtain our undecidability results as follows.
First we enrich KR with the global modality. As we will show, the combination of
the intersection construct with the global modality is a powerful one: it is possible
to give an extremely straightforward reduction of the
N

N tiling problem. We
then enrich KR with a modality called the master modality. This is also a natural
operator — indeed, perhaps more natural than the global modality. As a very easy
reduction from the
N

N recurrent tiling problem reveals, the resulting system is
highly undecidable.



6.5 Undecidability via Tiling
369
Intersection and the global modality
Our ﬁrst example vividly illustrates how easily undecidability can arise. We are
going to mix two simple ingredients together, both of which are decidable, and
show that the result has an undecidable satisﬁability problem.
The ﬁrst ingredient is a variant of DPDL, with intersection replacing choice and
iteration as program constructors. Recall from Example 1.15 that DPDL is simply
PDL interpreted over deterministic PDL structures (that is, PDL structures in which
the relations
R
a corresponding to atomic programs
a are partial functions). Further,
recall from Example 1.26 that modalities built with the intersection constructor
(that is, modalities of the form
h
1
\

2
i) are interpreted by the relation
R

1
\
R

2,
where
R

1 is the relation corresponding to
h
1
i and
R

2 the relation corresponding
to
h
2
i.
In what follows we will not use the entire language; instead we will work with a
fragment (called KR) which consists of all formulas without occurrences of
 and
[. That is, KR contains precisely the following formulas
:

::=
p
j
?
j
:
j

1
^

2
j
h
i
(p a proposition letter)

::=
a
j

1
;

2
j

1
\

2
(a an atomic program)
:
The KR language is rather simple: essentially it allows us to state whether or not
different sequences of (deterministic) programs terminate in the same state when
executed in parallel. Note that (over deterministic PDL structures) a selection argu-
ment immediately shows that it is decidable. Over deterministic structures, every
modal operator in KR is interpreted by a partial function. (This is because all atomic
programs are modeled by partial functions, and the only program constructors we
have at our disposal are composition and intersection.) It follows that if a sentence
 from KR is satisﬁable in a deterministic model, then it is satisﬁable in a ﬁnite
deterministic model; the proof is essentially the same as that of Corollary 6.9.
The second ingredient is even simpler. We are going to add the global modality
A to our fragment. This is an interesting operator that we are going to discuss
in detail in Section 7.1; for present purposes we only need to know two things
about it. First, it is interpreted as follows:
M;
w

A if for all
v in
M we have
M;
v

. Thus, as its name suggests, the global modality is a modal operator
which allows us to express global facts. Second,
A has a decidable satisﬁability
problem. (To see this, simply observe that
A is an S5 operator, and we know that
S5 is decidable.) Thus, on its own,
A is pretty harmless.
But what happens when we add
A to KR? The resulting language called KRA can
talk about computations in a very natural (and very powerful) way. For example,
A(hai>
!
 
)
expresses that in every state of a computation,
 is a precondition for the program



370
6 Computability and Complexity
a to have a terminating execution. As we will now show, KRA has crossed the
border into undecidability.
Theorem 6.31 Assume that the language has at least two atomic programs. Then
the satisﬁability problem for KRA is undecidable. To be precise, it is

0
1-hard.
Proof. We show this by reducing the
N

N tiling problem to the KRA satisﬁability
problem; the undecidability (and

0
1-hardness) of the satisﬁability problem will
follow from the known undecidability (
0
1-hardness) of the
N

N tiling problem.
Recall that the
N

N tiling problem asks: given a ﬁnite set of tile types
T , can
T
tile
N

N? Putting this more formally: does there exist a function
t
:
N

N
!
T
such that
right
(t(n;
m))
=
left
(t(n
+
1;
m))
up
(t(n;
m))
=
down
(t(n;
m
+
1))?
We will reduce
N

N tiling to the satisﬁability problem as follows. Let
T
=
fT
1
;
:
:
:
;
T
k
g be the given set of tile types. We will construct a formula

T such
that
T tiles
N

N iff

T is satisﬁable.
(6.8)
If we succeed in constructing such a formula it follows that the KRA-satisﬁability
problem is undecidable. (For suppose it was decidable. Then we could solve the
N

N tiling problem as follows: given
T , form

T , and use the putative KRA-
satisﬁability algorithm to check for satisﬁability. By (6.8) this would solve the
tiling problem — which is impossible.)
The construction of

T proceeds in three steps. First, we show how to use KRA
to demand ‘gridlike’ models. Second, we show how to use KRA to demand that a
tiling exists on this ‘grid.’ Finally we prove (6.8).
Step 1. Forcing the grid. The basic idea is to let the nodes in
M mimic the nodes
in
N

N, and to use two relations
R
r and
R
u to mimic the ‘to-the-right’ and the
‘up’ functions of
N

N. To get the gridlike model we want, we simply demand
that
R
r and
R
u commute:

g
r
id
:=
Ah(r
;
u)
\
(u
;
r
)i>:
This says that everywhere in the model it is possible to make a ‘to-the-right transi-
tion followed by an up transition’ and an ‘up transition followed by a to-the-right
transition,’ and both these transition sequences lead to the same point. (Note that
this is all we need to say, since by assumption
R
r and
R
u are partial functions.)
Step 2. Tiling the model. We will ‘tile the model’ by making use of proposition
letters
t
1, . . . ,
t
k which correspond to the tile types in
T . The basic idea is simple:
we want
t
i to be true at a node
w iff a tile of type
T
i is placed on
w. Of course, not



6.5 Undecidability via Tiling
371
any placement of tiles will do: we want a genuine tiling. But the following three
demands ensure this:
(i) Exactly one tile is placed at each node:

1
:=
A
0
@
k
_
i=1
t
i
^
^
1i<j
k
:(t
i
^
t
j
)
1
A
:
(ii) Colors match going right:

2
:=
A
0
@
_
right
(T
i
)=left
(T
j
)
(t
i
^
hr
it
j
)
1
A
:
(iii) Colors match going up:

3
:=
A
0
@
_
up
(T
i
)=down
(T
j
)
(t
i
^
huit
j
)
1
A
:
Putting this together, we deﬁne

T
:=

g
r
id
^

1
^

2
^

3.
Step 3. Proving the equivalence. We now show that (6.8) holds. Assume ﬁrst
that
t
:
N

N
!
T is a tiling of
N

N. Construct a satisfying model for

T as
follows.
W
=
fw
n;m
j
n;
m
2
N
g
R
r
=
f(w
n;m
;
w
n+1;m
)
j
n;
m
2
N
g
R
u
=
f(w
n;m
;
w
n;m+1
)
j
n;
m
2
N
g
V
(t
i
)
=
fw
n;m
j
n;
m
2
N and
t(n;
m)
=
T
i
g:
Clearly,

T holds at any state
w of
M.
For the converse, let
M be a model such that
M;
w
0


T . It follows from
M;
w
0


g
r
id that there exists a function
f
:
N

N
!
W such that
f
(0;
0)
=
w
0,
R
r
f
(n;
m)f
(n
+
1;
m) and
R
u
f
(n;
m)f
(n;
m
+
1). Deﬁne the tiling
t
:
N

N
!
T by
t(n;
m)
=
T
i iff
M;
f
(n;
m)

t
i
:
By

1,
t is well-deﬁned and total. Moreover, if
t(n;
m)
=
T
i and
t(n
+
1;
m)
=
T
j,
then
R
r
f
(n;
m)f
(n
+
1;
m), and both
M;
f
(n;
m)

t
i and
M;
f
(n
+
1;
m)

t
j. Given that
w
0 satisﬁes

2, we conclude that
right
(T
i
)
=
left
(T
j
). Similarly,
because of

3, if
t(n;
m)
=
T
i and
t(n;
m
+
1)
=
T
j, then
up
(T
i
)
=
down
(T
j
).
Thus,
T tiles
N

N.
a
The above proof clearly depends on having two deterministic atomic programs at
our disposal. But what happens if we only have one? It should be clear that then



372
6 Computability and Complexity
\ cannot do any interesting work for us, and in fact the language has a decidable
satisﬁability problem; see Exercise 6.5.1.
We now know that KRA-satisﬁability is undecidable (given more than one atomic
program) but how undecidable is it? In particular can we also prove a

0
1 upper
bound to match the

0
1-hardness result? (That is, can we show that we are dealing
with a case of ‘ordinary undecidability’?) To prove this, it sufﬁces to show that the
validities of KRA form an r.e. set. Now we could do this by devising a recursive
axiomatization of the KRA-validities, but by making use of a general lemma from
correspondence theory we can establish the result more straightforwardly.
Lemma 6.32 If K is a class of frames deﬁned by a ﬁrst-order formula, then its
modal logic is recursively enumerable.
Proof. Assume that the ﬁrst-order formula
 deﬁnes
K, where
 is built using only
relation symbols of arity 2 or higher, and identity. Then, a modal formula
 is valid
on
K iff it is valid on all frames in K iff

j
=
8x8P
1
:
:
:
8P
n
ST
();
(6.9)
where
P
1, . . . ,
P
n are unary predicate symbols corresponding to the proposition
letters in
. As the predicate variables
P
1, . . . ,
P
n do not occur in
, (6.9) is
equivalent to

j
=
8x
ST
(). But this is an ordinary ﬁrst-order implication, which
is an r.e. notion. Hence, modal validity on K is an r.e. notion as well.
a
Theorem 6.33 Assume that our language has at least two, but at most ﬁnitely
many atomic programs. Then the satisﬁability problem for KRA is

0
1-complete.
Proof. The

0
1 lower bound is given by the encoding of the
N

N tiling problem
in the proof of Theorem 6.31. For the

0
1 upper bound we show that the validity
problem for KRA is r.e. The standard translations for the constructors
; and
\ are
given in Section 2.4; both are ﬁrst-order. (Recall that the
 constructor is the only
part of PDL that takes us out of ﬁrst-order logic.) The standard translation for
A is
obvious (and clearly ﬁrst-order):
ST
(A)
=
8y
[y
=x]ST
():
Thus — assuming we are working with a language of KRA that contains at most
ﬁnitely many atomic programs — the required class of frames is deﬁned by
^
 atomic
8xy
z
(R

xy
^
R

xz
!
y
=
z
):
Hence, by Lemma 6.32, the modal logic of the class of frames for KRA is r.e. as
required.
a



6.5 Undecidability via Tiling
373
Intersection and the master modality
Our next example illustrates how easily high undecidability can arise. Once again,
we will enrich the KR language, but this time with the master modality. As we will
see, the resulting language KR
2* has a

1
1-complete satisﬁability problem.
Like the global modality, the master modality
2* is a tool for expressing general
constraints in the object language, but it works rather differently. A formula of
the form
2*
 is true at a node
w iff
 is true at all nodes reachable by any ﬁnite
sequence of atomic transitions from
w. Formally,
w

2*
 iff
v

 for all
v such that
(w
;
v
)
2
 
[
a atomic
R
a
!

:
That is,
2* explores the reﬂexive transitive closure of the union of all the relations
used to interpret the atomic programs. If we only have ﬁnitely many atomic pro-
grams
a
1
;
:
:
:
;
a
n, the master modality is simply shorthand for the PDL modality
[(a
1
[



[
a
n
)

]. From a computational perspective, this modality is arguably even
more natural than the global modality: it is a way of looking at what must happen
throughout the space of possible computations. (It has other natural interpretations
as well. For example, if we interpret our basic modalities as in multi-agent epis-
temic logic — that is,
[a] means ‘agent
a knows that
’ — then
2* is the ‘common
knowledge’ operator.)
But, for all its naturalness, the master modality can be extremely dangerous.
Let us see what happens when we add it to KR. First, observe that KR
2* must be
undecidable. (There is nothing new to prove here; simply observe that if we sys-
tematically replace every occurrence of
A in the proof of Theorem 6.31 by
2
* , the
argument still goes through.) But can we prove a matching

0
1 upper bound? We
certainly cannot appeal to Lemma 6.32; while the global modality was essentially
ﬁrst-order, the master modality is not. (As with the
 constructor of PDL, its natural
correspondence language is inﬁnitary; see Section 2.4.) And indeed, any attempt
to recursively enumerate the validities of KR
2* is bound to fail.
Theorem 6.34 The satisﬁability problem for KR
2* is highly undecidable. To be
precise, it is

1
1-hard.
Proof. We show this by reducing the recurrent tiling problem to the KR
2* -satisﬁa-
bility problem; the

1
1-hardness of the satisﬁability problem will follow from the
known

1
1-hardness of the recurrent tiling problem.
Recall that the recurrent tiling problem asks: given a ﬁnite set of tile types
T ,
which includes some distinguished tile type
T
1, can
T tile
N

N in such a way that
T
1 occurs inﬁnitely often in the ﬁrst row? Putting this more formally: does there
exist a function
t
:
N

N
!
T such that
right
(t(n;
m))
=
left
(t(n
+
1;
m))



374
6 Computability and Complexity
up
(t(n;
m))
=
down
(t(n;
m
+
1))
fn
j
t(n;
0)
=
T
1
g
is inﬁnite
?
We reduce
N

N recurrent tiling to KR
2* -satisﬁability as follows.
Let
T
=
fT
1
;
:
:
:
;
T
k
g be the set of tile types. We will deﬁne a formula

T
;T
1 such that
T and
T
1 recurrently tile
N

N iff

T
;T
1 is satisﬁable.
(6.10)
Most of the real work was done in the proof of Theorem 6.31. Let us simply
take the earlier encoding

T and replace every occurrence of
A with
2* . Call the
result


T . This formula reduces the
N

N tiling problem to the KR
2* -satisﬁability
problem.
To reduce the recurrent tiling problem, it remains to ensure that our distin-
guished tile
T
1 occurs inﬁnitely often on the ﬁrst row. As
t
1 is the proposition
letter corresponding to
T
1, this means we want to force
t
1 to be true at nodes of the
form
t(n;
0) for inﬁnitely many
n. To do this, we will introduce a new proposition
letter ﬁrst-row and then deﬁne:

r
e
c
:= ﬁrst-row
^
2*
[u]:ﬁrst-row
^
2*
(ﬁrst-row
!
hr
i3*
(ﬁrst-row
^
t
1
)):
Suppose that

r
ec is satisﬁed at some point
w
0 of a grid-like model. It follows that
ﬁrst-row is satisﬁed at
w
0; that ﬁrst-row can only be satisﬁed at points reachable
by a ﬁnite number of
R
r transitions from
w
0; and that for inﬁnitely many distinct
natural numbers
n,
w
0

hr
i
n
(ﬁrst-row
^
t
1
).
So, let

T
;T
1 be the conjunction of


T and

r
ec. Then (6.10) holds.
a
To conclude this section, two general remarks. First, the examples in this section
were clearly chosen to make the undecidability proofs run as smoothly as possible.
In particular, our examples hinged on the use of
\ to force the existence of the
grid. What happens if we are working in languages without this constructor? That
is, how widely applicable is this method for proving undecidability?
Suppose we are working with an arbitrary modal language, and we want to es-
tablish the undecidability of its satisﬁability problem. If we abstract from the proof
of Theorem 6.31, we see that there is one ingredient that will always be needed
to make similar arguments go through: sufﬁcient ‘global’ expressive power. This
power may arise directly through the presence of additional operators, or it may
arise indirectly through special features of the class of models under consideration,
but one way or another we will need it. On the other hand, we do not need the
\
constructor; Exercise 6.5.2 is a nice example.
Second, we have discussed tiling problems as if they were useful only for estab-
lishing different grades of undecidability. In fact, they can also be used to analyze
the complexity of decidable problems: for example, there are NP-hard, PSPACE-
hard, and EXPTIME-hard tiling problems (see the Notes for further references).



6.6 NP
375
At the end of this chapter we will use a 2-player tiling problem to show that the
satisﬁability problem for PDL is EXPTIME-hard.
Exercises for Section 6.5
6.5.1 Show that KRA-satisﬁability is decidable if we have only one atomic program at our
disposal. (This result can be proved via a ﬁnite model property argument.)
6.5.2
(i) Show that the satisﬁability problem of the following ‘tiling’ logic
Tile
1 is
undecidable.
Tile
1 is a normal modal logic with three diamonds
hui;
hr
i and
3,
deﬁned by the following (Sahlqvist) axioms:
huip
!
[u]p and
hr
i
p
!
[r
]
p
(6.11)
hr
i
hui
p
!
[
u]
hr
i
p
33p
!
3p
huip
!
3p and
hr
i
p
!
3p:
(ii) Now use this logic plus the standard translation to conclude that the three variable
fragment of ﬁrst-order logic (without function symbols, but possibly with equality)
is undecidable.
(iii) Let
Tile
2 be obtained from
Tile
1 by omitting axiom (6.11). Show that
Tile
2
is still undecidable. (Hint: Reduce the satisﬁability problem of
Tile
1 to that of
Tile
2.)
(iv) Conclude that ﬁrst-order logic with three variables, but without equality is unde-
cidable.
(v) Use a similar tiling logic to show that ﬁrst-order logic with one variable, two unary
function symbols, and only unary predicate symbols is undecidable. (Hint: adjust
the standard translation so that it exploits the unary function symbols directly.)
6.6 NP
The interpretation method (and in particular, interpretations in
SnS) is a powerful
and widely applicable way of proving decidability. Nevertheless, it has disadvan-
tages. Reducing the satisﬁability problems of what are often rather simple modal
logics to
SnS is using a sledgehammer to crack a nut. The decision problem for
SnS is non-elementary. This means that the time required to decide whether an
arbitrary formula
 is decidable cannot be bounded by any ﬁnite tower of expo-
nentials of the form
2
2...
2
jj
:
The use of ﬁltrations to establish decidability is open to similar objections. A
ﬁltration is typically
2
jj in the size of the input formula. But it is not feasible to
enumerate all the models up to this size even for quite small values of
jj. And
even a nondeterministic Turing machine, which could ‘guess’ a ﬁltration in one
move (see Appendix C and the discussion below), would still be faced with the



376
6 Computability and Complexity
immensely costly task of checking that
 was true on this huge structure (to use
the terminology discussed in Appendix C, ﬁltrations typically offer us NEXPTIME
algorithms). Indeed, of the three decidability techniques discussed so far, only
the mosaic method (which ‘deconstructs’ models locally) respects what is special
about modal logic; and as we will learn in Section 7.4, the mosaic method can be
used to give essentially optimal satisfaction algorithms.
But this is jumping ahead. In this section and the three that follow, we will
use concepts drawn from computational complexity theory to present a more ﬁne-
grained analysis of modal satisﬁability. This analysis is interesting for two reasons.
First, by making use of only three central complexity classes (NP, PSPACE and
EXPTIME), we will be able to present a classiﬁcation of modal satisﬁability that
covers many important logics. Secondly, in many cases the techniques involved
have a distinctly modal ﬂavor: essentially, the work boils down to a reﬁned analysis
of the ﬁnite model property.
We begin our analysis with the class NP, the class of problems solvable using
nondeterministic polynomial time algorithms. We ﬁrst review the central ideas
underlying this complexity class and their import for modal satisﬁability problems.
Then, using examples from multi-modal and tense logic, we show how simple
selection arguments can be used to prove NP-completeness results. Finally, we
apply the same method to prove a more general result: every normal modal logic
extending S4.3 has an NP-complete satisﬁability problem.
When a problem
P is said to be complete with respect to a complexity class C,
two things are being claimed. The ﬁrst is that
P belongs to C; that is, there is an
algorithm using only the resources permitted by C that solves
P. For example, if
C
=
NP this means that there exists a non-deterministic polynomial time algorithm
for solving
P. The second claim is that
P is C-hard; that is, any other problem in
C is polynomial time reducible to
P.
Now, as far as the satisﬁability problem for normal modal logics is concerned,
NP-hardness is a triviality: all (consistent) normal modal logics have NP-hard sat-
isﬁability problems. The point is this. The classic NP-hard problem is the satis-
ﬁability problem for propositional logic. But as every normal modal logic is an
extension of propositional logic, every (consistent) normal modal logic has a sat-
isﬁability problem at least as hard as that for propositional logic. Thus — for the
class NP — our work is somewhat simpliﬁed: we are simply looking for normal
modal logics whose satisﬁability problem belongs to NP.
What sort of problems belong to NP? Many problems decompose naturally into
the following two steps: a search for a solution followed by a veriﬁcation of
the solution. In general, search is expensive, but by thinking in terms of non-
deterministic algorithms we can abstract away from this expense: if a solution
exists, such an algorithm will ﬁnd it in one non-deterministic step. (If necessary,
consult Section C for further discussion.) This abstraction leaves us free to concen-



6.6 NP
377
trate on the veriﬁcation step, and leads us to isolate the class NP: a problem belongs
to NP iff it has the above general proﬁle (that is, a non-deterministic choice of a
solution followed by a veriﬁcation) and moreover the veriﬁcation step is tractable
(that is, solvable in polynomial time).
How do such ideas bear on modal satisﬁability? The key idea we need is em-
bodied in the following lemma.
Lemma 6.35 Let
 be a ﬁnite similarity type. Let
 be a consistent normal modal
logic over
 with the polysize model property with respect to some class of models
M. If the problem of deciding whether
M
2
M is computable in time polynomial
in
jMj, then
 has an NP-complete satisﬁability problem.
Proof. As noted above, the NP-hardness of the problem is immediate, so it remains
to prove the existence of an algorithm in NP that solves
-satisﬁability. Given
,
non-deterministically choose a model
M whose size is polynomial in the size of
.
Because
M is polysize in
jj, we can check in time polynomial in
jj whether
M
veriﬁes
. For the special case of the basic modal language, this may be seen as
follows.
Let
jjMjj denote the sum of the number states in
M and the number of pairs in
M’s binary relation
R
M. Let
 
1, . . . ,
 
k be an enumeration of the subformulas of
, in increasing length. So
 
k
=
 and if
 
i is a subformula of
 
j, then
i
<
j.
Notice that
k

jj. One can show by induction on
m that we can mark each state
w in
M with
 
j or
: 
j, for
j
=
1, . . . ,
m, depending on whether or not
 
j is
true at
w in time
O
m

jjMjj. The only non-trivial case is if
 
m+1
=
3 
j, for
some
j
<
m
+
1. But in that case we mark
w with
2 
j if some
v with
R
w
v is
marked with
 
j. By our induction hypothesis, every state is already marked with
 
j or
: 
j, this step can be carried out in time
O
jjMjj. Since
M is polysize in
j,
so is
jjMjj. Hence, checking whether
M satisﬁes
 can indeed be done in time
polynomial in
jj.
Finally, then, because membership in M is decidable in time polynomial in
jMj,
and
jMj is polynomial in
jj, we can check in time polynomial in
jj that
M is in
M.
a
Where did we use the assumption that
 is a ﬁnite similarity type in the proof
of Lemma 6.35? Essentially, it allows us to check whether
M veriﬁes
 in time
polynomial in
 and in
jMj. The key point is this: when working with a ﬁxed ﬁnite
similarity type, we are actually working within a ﬁnite-variable fragment, say with
l variables. This allows us to restrict our attention to only ﬁnitely many relations of
arity at most
l in
M. While the total number of tuples in all relations in
M may be
huge, it is nonetheless independent of
; see Exercise 6.6.2 for further elaborations.
Note that the second demand — that M-membership be polynomial time decid-
able — is vital. As the reader was asked to show in Exercise 6.2.4, the polysize



378
6 Computability and Complexity
model property alone is insufﬁcient to ensure decidability, let alone the existence
of a solution in NP. However, for many important logics this property can be estab-
lished by appealing to the following standard result.
Lemma 6.36 If F is a class of frames deﬁnable by a ﬁrst-order sentence, then the
problem of deciding whether
F belongs to F is decidable in time polynomial in the
size of
F.
Proof. Left as Exercise 6.6.1.
a
We will show that many normal modal logics are NP-complete. The proofs revolve
around one central idea: the construction of polysize models by the selection of
polynomially many points from some given satisfying model.
For our ﬁrst example, we return to the multi-modal language containing
n unary
modal operators discussed earlier (see Corollary 6.9). Recall that
F
n
1 is the class of
frames for this language in which each relation is a partial function,
M
n
1 is the class
of models built over
F
n
1, and K
nAlt
1 is its logic.
Theorem 6.37 K
nAlt
1 has an NP-complete satisﬁability problem.
Proof. We already showed that this logic has the strong f.m.p., but the selection
argument we used generated models exponential in size of the input formula. A
simple reﬁnement of the method shows that K
nAlt
1 actually has the polysize model
property.
Given a formula
 of this language and a model
M
=
(W
;
R
;
V
) we deﬁne a
selection function
s as follows:
s(p;
w
)
=
fw
g
s(:;
w
)
=
s(;
w
)
s(
^
 
;
w
)
=
s(;
w
)
[
s( 
;
w
)
s(hai 
;
w
)
=
fw
g
[
[
fw
0
jR
a
w
w
0
g
s( 
;
w
0
)
Intuitively,
s(;
w
) selects the nodes actually needed when evaluating
 in
M at
w
— and indeed, it follows by induction on the structure of
 that for all nodes
w of
M, and all formulas

M;
w

 iff
M

s(;
w
);
w

:
It is clear that
M

s(;
w
)
2
M
n
1. So let us look at size of the new model. If
M
2
M
n
1, we claim that
js(;
w
)j

jj
+
1. To see this, note that only occurrences
of modalities in
 cause new nodes to be adjoined to
s(;
w
). This adjunction of
points is carried out in the fourth clause of the inductive deﬁnition for
s, which tells
us to adjoin every state
w
0 such that
R
a
w
w
0. Because
M
2
M
n
1, every relation
R
a



6.6 NP
379
is a partial function; hence if such a
w
0 exists, it is unique. In short, K
nAlt
1 has
the polysize model property: simply counting the number of occurrences of modal
operators in
 and adding one gives us an upper bound on the size of the domain
of the required satisfying model.
By Lemma 6.36, membership in K
nAlt
1 is decidable in polynomial time, for this
is a class of frames deﬁnable by a ﬁrst-order sentence — namely the conjunction
of sentences that say that each of the
n relations is a partial function.
The result follows by Lemma 6.35.
a
The argument for K
nAlt
1 shows the selection method in its simplest form: given
any model for
 we build a new polysize model for
 by making a suitable selection
of polynomially many points. This simple form of argumentation is applicable to a
number of logics, a particularly noteworthy example being S5. Given any S5 model
for
, it is possible to select
m
+
1 points from this model (where
m is the number
of modality occurrences in
) which sufﬁce to construct a new S5 model for
,
and the NP-completeness of S5 follows straightforwardly. We leave the details as
Exercise 6.6.4 and turn our attention to a modiﬁcation of the point selection method
frequently needed in practice: a detour via ﬁnite models.
Both K
nAlt
1 and S5 are very simple logics; in neither case is it difﬁcult to deter-
mine which points should be selected. In other cases, we may not be so fortunate.
Suppose we are trying to show that a logic
 has the polysize model property, and
we already know that
 has the f.m.p. Then, instead of trying to select points from
an arbitrary model, we are free to select points from a ﬁnite model, or even a point-
generated submodel of a ﬁnite model. This often gives us an easy way of zooming
in on the crucial points. In particular, when we are working with models based
on ﬁnite orderings it makes sense to talk of choosing points that are maximal (or
minimal) in the frame ordering that satisfy some subformula; such extremal points
are often the vital ones. As an example of such an argument, let us consider
K
t
4:3,
the temporal logic of linear frames (in the basic temporal language).
Theorem 6.38
K
t
4:3 has an NP-complete satisﬁability problem.
Proof. We will ﬁrst show that
K
t
4:3 has the polysize model property. Let
 be
a formula of the basic temporal language that is satisﬁable on a
K
t
4:3 model.
As
K
t
4:3 has the f.m.p. with respect to the class of weak total orders (see Def-
inition 4.37 and Corollary 6.8), there is a ﬁnite weakly totally ordered model
M
=
(T
;
;
V
) containing a node
t such that
M;
t

. We now build a poly-
sized model for
 by selecting points from
M.
Let
F
 
1, . . . ,
F
 
k and
P

1, . . . ,
P

l be all subformulas of
 of the form
F
 
and
P
, respectively, that are satisﬁed in
M. For each formula
F
 
i choose a point
u
i such that
M;
u
i

 
i and
u
i is a maximal point in the
-ordering with this
property. Similarly, for each formula
P

j choose a point
v
j satisfying

j that is



380
6 Computability and Complexity
minimal in the
-ordering with respect to this property. Let
M
0 (=
(T
0
;

0
;
V
0
))
be
M

ft;
u
1
;
:
:
:
;
u
k
;
v
1
;
:
:
:
;
v
l
g. As
 is a weak total ordering of
T,

0 is
a weak total ordering of
T
0. Furthermore, the number of nodes in
M
0 does not
exceed
m
+
1, where
m is the number of modalities in
, thus
M
0 is a polysize
model in the correct class. It remains to show that
M
0
;
t

, but this follows
straightforwardly by induction on the structure of
.
As the class of weak total orders is deﬁnable using a ﬁrst-order sentence, the NP-
completeness of
K
t
4:3 follows from Lemma 6.36 and the polysize model property
that we have just established.
a
We are ready to prove a general complexity result for the basic modal language: all
normal logics extending S4.3 have an NP-complete satisﬁability problem. Recall
from our discussion of Bull’s theorem in Section 4.9 that an S4.3 frame is a frame
that is rooted, transitive, and connected (8xy
(R
xy
_
R
y
x)); note that all such
frames are reﬂexive. Bull’s Theorem tells us that all normal modal logics extending
S4.3 have the ﬁnite frame property with respect to a class of S4.3 frames. By
making a suitable selection from models based on such frames, we can prove that
every such logic has the polysize model property. Then, by using the fact that every
normal logic extending S4.3 has a negative characterization in terms of ﬁnite sets of
ﬁnite frames (Theorem 4.103), we will be able to prove that all these satisﬁability
problems are NP-complete.
First we need the following lemma; it is really just Lemma 4.98, which linked
bounded morphisms and covering lists, stated in purely modal terms.
Lemma 6.39 Let
F and
G be two ﬁnite S4.3 frames. Then the following two state-
ments are equivalent:
(i) There exists a surjective bounded morphism from
F to
G.
(ii)
G is isomorphic to a subframe of
F that contains a maximal point of
F.
Proof. First suppose that
f is a surjective bounded morphism from
F to
G. Let
w
max be a maximal point in
F, and let
c
W consist of
w
max together with exactly
one maximal world in
f
 1
[v
] for every point
v of
G such that
v
6=
f
(w
max
). Then
b
F
=
F

c
W is the subframe we want.
Conversely, suppose that
c
W is a subset of the points in
F, such that
c
W contains
a maximal point
w
max, and
F

c
W is isomorphic to
G. We claim that the following
deﬁnes a bounded morphism from
F onto
F

c
W:
f
(w
)
=
w, for
w
2
c
W; and if
w
62
c
W, then
f
(w
) is a minimal world
b
w
2
c
W such that
R
w
b
w (that is, for any
w
0, if
R
w
w
0 then
R
b
w
w
0). Note that such a minimal world must always exist, since
w
max
2
c
W, thus
f is well deﬁned. (In short,
f maps ‘missing points’ to succes-
sors that are as close as possible. We used the same idea to deﬁne the bounded
morphism in the proof of Bull’s Theorem.) Clearly
f is surjective. So suppose



6.6 NP
381
R
w
w
0. Since
R
w
0
f
(w
0
) and
R is transitive, we have
R
w
f
(w
0
). By deﬁnition,
f
(w
) is a minimal element in
c
W such that
R
w
f
(w
), thus
R
f
(w
)f
(w
0
) and
f sat-
isﬁes the forth condition on bounded morphisms. Finally, suppose
R
f
(w
)f
(w
0
).
As
R
w
f
(w
), by the transitivity of
R we have
R
w
f
(w
0
). Since
f
(f
(w
0
))
=
f
(w
0
),
the back condition for bounded morphisms is also satisﬁed and we have shown that
F

c
W is a bounded morphic image of
F. As
F

c
W is isomorphic to
G,
G is a
bounded morphic image of
F as well.
a
We now show that any normal modal logic extending S4.3 has the polysize model
property.
Lemma 6.40 Let
 be a normal modal logic such that
S4:3

. Any formula

that is satisﬁable on a frame for
 is satisﬁable on a frame for
 that contains at
most
m
+
2 states, where
m is the number of occurrences of modal operators in
.
Proof. Suppose
 is satisﬁable on a frame for
. By Bull’s Theorem,
 has the
ﬁnite frame property, thus there is a ﬁnite model based on a
-frame that satisﬁes
 at some point
w
0. Let
M be the submodel of this model that is generated by
w
0. Clearly
M;
w
0

, and as formation of generated submodels preserves modal
validity,
M is based on a frame for
.
Now we select points. Let
3 
1
;
:
:
:
;
3 
k be all the
3-subformulas of
 that are
satisﬁed at
w
0. For each
1

i

k, select a point
w
i that is maximal with respect
to the property of satisfying
 
i. These are the points needed to ensure that
 is
satisﬁed in the polysize model at
w
0, but if we select only
w
0 and these points, we
have no guarantee that we have constructed a
-frame. However, as we will now
see, we can guarantee this if we glue on a maximal point. So, let
w
k
+1 be such a
point and deﬁne
c
M
:=
M

fw
0
;
w
1
;
:
:
:
;
w
k
;
w
k
+1
g:
c
M contains at most
m
+
2 points, where
m is the number of modal operators in
.
Moreover, it is based on a
-frame. To see this, note that the frame underlying
c
M
is a subframe of the frame underlying
M that satisﬁes the requirements of item (ii)
of Lemma 6.39; hence there is a surjective bounded morphism from
M to
c
M. Such
morphisms preserve modal validity, thus as
M is a
-model, so is
c
M.
It remains to ensure that
c
M
;
w
0

. We prove by induction that for all subfor-
mulas
 of
, and all
i such that
0

i

k, that
M;
w
i

 iff
c
M;
w
i

 
:
The only interesting step is for formulas of the form
3 . Suppose that
M;
w
i

3 (thus
 
=
 
j for some
1

j

k). Since
M is point-generated by
w
0
and transitive, it follows that
R
w
0
w
i, hence
M;
w
0

3 . We chose
w
j to be a
world maximal with respect to the property of satisfying
 
j, hence
R
w
i
w
j. By the



382
6 Computability and Complexity
induction hypothesis,
c
M
;
w
j

 
j. Hence
c
M
;
w
i

3 . The converse implication
is left to the reader.
a
Theorem 6.41 (Hemaspaandra’s Theorem) Every normal modal logic extend-
ing
S4:3 has an NP-complete satisﬁability problem.
Proof. Lemma 6.40 established the polysize model property for
, so it remains to
check that membership for
-frames can be decided in polynomial time. How can
we show this? Recall Theorem 4.103:
For every normal modal logic
 extending S4.3 there is a ﬁnite set
N of ﬁnite
S4.3 frames with the following property: for any ﬁnite frame
F,
F

 iff
F
is an S4.3 frame and there does not exist a bounded morphism from
F onto
any frame in
N.
This gives us a possible strategy: given any frame
F, check whether it is an S4.3
frame, and whether there is a surjective bounded morphism onto any frame in N.
Now, as S4.3 frames are ﬁrst-order deﬁnable, by Lemma 6.36 the ﬁrst part can be
performed in polynomial time. But what about the second? First, note that because
N is a ﬁxed ﬁnite set, we need only ensure that the task of checking whether there
is a bounded morphism from
F to a ﬁxed frame
G can be performed in polynomial
time. But the naive strategy of examining all the functions from
F to
G is com-
pletely unsuitable: the number of such functions is
jGj
jFj, which is exponential in
the size of
F. However, applying Lemma 6.39, we see that the task can be sim-
pliﬁed: we only need to check whether there is a set
c
W of worlds in
F such that
F

c
W is isomorphic to
G and
c
W contains a maximal world. Thus we need to
check less than
jFj
jGj embeddings. But this number is polynomial in the size of
F,
for
G is ﬁxed. By Lemma 6.35, NP-completeness follows.
a
The results of this section tell us something about the complexity of validity prob-
lems. The complement of NP is called co-NP. As a formula
 is not
-satisﬁable iff
: is
-valid, it follows that an NP-completeness result for
-satisﬁability tells us
that
-validity is co-NP complete (see Section C for further discussion). It is stan-
dardly conjectured that NP
6= co-NP, thus the validity and satisﬁability problems
for these logics probably have different complexities.
Exercises for Section 6.6
6.6.1 Prove Lemma 6.36. That is, show that if F is a class of frames deﬁnable by a ﬁrst-
order sentence, then the problem of deciding whether
F belongs to F is decidable in time
polynomial in the size of
F.
6.6.2 Explain why the argument given in the proof of Lemma 6.35 may break down when
we lift the restriction to ﬁnite similarity types. In particular, examine the situation when
the similarity type contains modal operators of arbitrarily high arities.



6.7 PSPACE
383
6.6.3 Extend the proof of Theorem 6.38 to show that
K
t
Q has the polysize model prop-
erty, and is NP-complete.
6.6.4 Use a selection of points argument to show that S5 has the polysize model property,
and is NP-complete.
6.6.5 Show that if we restrict attention to a ﬁxed ﬁnite set of proposition letters
, then the
satisﬁability problem for S5 is decidable in linear time.
(Hint: if
 is ﬁnite, the number of models we have to check to determine whether a given
formula
 is satisﬁed in them, is independent of
.)
6.7 PSPACE
PSPACE, the class of problems solvable by a deterministic Turing machine us-
ing only polynomial space, is the complexity class of most relevance to the basic
modal language. As we will see, some important modal satisﬁability problems
belong to PSPACE, and many modal logics have PSPACE-hard satisﬁability prob-
lems. This suggests that modal satisﬁability problems are typically tougher than
the satisﬁability problem for propositional calculus, for it is standardly conjectured
that PSPACE-hard problems are not solvable in NP.
The work of this section revolves around trees. We ﬁrst show that K lacks the
polysize model property by forcing the existence of binary-tree-based models using
short formulas. We then take a closer look at K-satisﬁability and show that it is in
PSPACE. The proof also shows that every K-satisﬁable formula is satisﬁable on
a tree-based model of polynomial depth. We then put all this work together to
prove Ladner’s theorem: every normal logic between K and S4 has a PSPACE-
hard satisﬁability problem.
Forcing binary trees
The NP-completeness results of the previous section were proved using polysize
model property arguments. So, before going any further, we will show that K does
not have the polysize model property. We do so by showing that K can force the
existence of binary trees. Many of the ideas introduced here will be reused in the
proof of Ladner’s theorem.
For any natural number
m, we are going to devise a satisﬁable formula

B
(m)
with the following properties:
(i) the size of

B
(m) is polynomial (indeed, quadratic) in
m, but
(ii) when

B is satisﬁed in any model
M at a node
w
0, then the submodel of
M generated by
w
0 contains an isomorphic copy of the binary tree of depth
m.



384
6 Computability and Complexity
(i)
q
0
(ii)
2
(m)
(q
i
!
V
i6=j
:q
j
)
(0

i

m)
(iii)
B
0
^
2B
1
^
2
2
B
2
^
2
3
B
3
^



^
2
m 1
B
m 1
(iv)
2S
(p
1
;
:p
1
)
^
2
2
S
(p
1
;
:p
1
)
^
2
3
S
(p
1
;
:p
1
)
^



^
2
m 1
S
(p
1
;
:p
1
)
^
2
2
S
(p
2
;
:p
2
)
^
2
3
S
(p
2
;
:p
2
)
^



^
2
m 1
S
(p
2
;
:p
2
)
^
2
3
S
(p
3
;
:p
3
)
^



^
2
m 1
S
(p
3
;
:p
3
)
...
^
2
m 1
S
(p
m 1
;
:p
m 1
)
Fig. 6.5. The formula

B
(m).
As the binary branching tree of depth
m contains
2
m nodes, the size of the smallest
satisfying model of

B
(m) is exponential in
j
B
(m)j. Thus we will have shown
that small formulas can force the existence of large models.
We will deﬁne these formulas by mimicking truth tables. For any natural number
m,

B
(m) will be constructed out of the following variables:
q
1, . . . ,
q
m, and
p
1,
. . . ,
p
m. The
q
i play a supporting role. They will be used to mark the level (or
depth) in the model; that is, they will mark the number of upward steps that need to
be taken to reach the satisfying node. But any satisfying model for

B
(m) will give
rise to a full truth table for
p
1
;
:
:
:
;
p
m: every possible combination of truth values
for
p
1
;
:
:
:
;
p
m will be realized at some node, and hence any model for

B
(m) must
contain at least
2
m nodes.
That’s the basic idea.
To carry it out, we ﬁrst deﬁne two macros:
B
i, and
S
(p
i
;
:p
i
). For
i
=
0;
:
:
:
;
m
 1,
B
i is deﬁned as follows:
B
i
:=
q
i
!
(
3(q
i+1
^
p
i+1
)
^
3(q
i+1
^
:p
i+1
))
:
(6.12)
Given that we are going to use the
q
is to mark the levels, the effect of
B
i should be
clear: it will force a branching to occur at level
i, set the value of
p
i+1 to true at
one successor at level
i
+
1, and set
p
i+1 to false at another.
Our other macro is closely related. For
i
=
0;
:
:
:
;
m
 1,
S
(p
i
;
:p
i
) is deﬁned
as follows:
S
(p
i
;
:p
i
)
:=
(p
i
!
2p
i
)
^
(:p
i
!
2:p
i
):
(6.13)
This formula sends the truth values assigned to
p
i and its negation one level down.
The idea is that once
B
i has forced a branching in the model by creating a
p
i+1
and a
:p
i+1 successor,
S
(p
i+1
;
:p
i+1
) ensures that these newly set truth values
are sent further down the tree; ultimately we want them to reach the leaves.
We are ready to deﬁne

B
(m). It is the conjunction of the formulas listed in
Figure 6.5. Note that

B
(m) has the required effect. The ﬁrst conjunct,
q
0, ensures



6.7 PSPACE
385
that any node that satisﬁes

B
(m) is marked as having level 0. The effect of (ii) is
to ensure that no two distinct level marking atoms
q
i and
q
j can be true at the same
node (at least, this will be the case all the way out to level
m, which is all we care
about). To see this, recall that
2
(m)
 is shorthand for

^
2
^
2
2

^



^
2
m
.
Thus our level markers are beginning to work as promised.
But the real work is carried out by (iii) and (iv). Because of the preﬁxed blocks
of
2 modalities, the
B
i macros in (iii) force
m successive levels of branching;
and each such branching ‘splits’ the truth value of one of the
p
is. Then, again
because of the preﬁxed
2 modalities, (iv) uses the
S
(p
i
;
:p
i
) macro to send each
of these newly split truth values all the way down to the
m-th level. In short,
(iii) creates branching, and (iv) preserves it. It is worthwhile sitting down with a
pencil and paper to check the details. If you do, it will become clear that

B
(m) is
satisﬁable, and that any satisfying model for

B
(m) must contain a submodel that
is isomorphic to the binary branching tree of depth
m. It follows that any model of

B
(m) must contain at least
2
m nodes, as we claimed.
In spite of its appearance,

B
(m) is indeed a small formula. To see this, consider
what happens when we increment
m by 1. The answer is: not much. For example
(iii) simply gains an extra conjunct, becoming
2B
0
^
2
2
B
1
^
2
3
B
2
^



^
2
m 1
B
m 1
^
2
m
B
m
:
Similarly, each row in (iv) gains an extra conjunct (as does the next empty row)
thus we gain a new column containing
m formulas. The biggest change occurs
in (ii). If you write (ii) out in full, you will see that it gains an extra row, and
an extra column, and an extra atomic symbol in each embedded disjunct, and this
means that the
j
B
(m)j will increase is
O
(m
2
log
m) (that is, slightly faster than
quadratically). This is negligible compared with the explosion in the size of the
smallest satisfying model: this doubles in size every time we increase
m by one.
Theorem 6.42 K lacks the polysize model property.
That is, K lacks a property enjoyed by all the NP-complete logics examined in
the previous section, and there is no obvious way of using NP guess-and-check
algorithms to solve K-satisﬁability. What sort of algorithms will work?
A PSPACE algorithm for K
We will now deﬁne a PSPACE-algorithm called Witness whose successful termi-
nation guarantees the K-satisﬁability of the input. It may seem surprising that we
can do this. After all, we have just seen that there are satisﬁable formulas

B
(m)
whose smallest satisfying model contains
2
m nodes. What happens if we give

B
(m) as input to Witness? Will it be forced to use an exponential amount of



386
6 Computability and Complexity
space to determine the satisﬁability of

B
(m)? The answer is: no. Witness will
take an exponential amount of time to terminate on difﬁcult input, but it uses space
efﬁciently. As we will see, if a formula
 is satisﬁable in some model, it is sat-
isﬁable in a tree-based model of polynomial depth. While some formulas require
models with exponentially many nodes, we can always ﬁnd a shallow satisfying
model: the length of each branch is polynomial in
jj. Witness tests for the exis-
tence of shallow models, and does so one branch at a time. It does not need to keep
track of the entire model, and hence can be made to run in PSPACE.
Witness is essentially an abstract tableaux system for K: it explores spaces of
Hintikka sets (see Deﬁnition 6.24). Recall that Hintikka sets need not be satisﬁable,
and that we call satisﬁable Hintikka sets atoms. Witness will take two ﬁnite sets
of formulas
H and
 as input, and determine whether or not
H is an atom over
. It does so by looking at the demands that
H makes and recursively calculating
whether all these demands can be met. The following deﬁnition makes the idea of
a demand precise (compare Deﬁnition 4.62).
Deﬁnition 6.43 Suppose
H is a Hintikka set over
, and
3 
2
H. Then the
demand that
3 creates in
H (notation:
Dem
(H
;
3 
)) is
f 
g
[
f
j
2
2
H
g:
We use
H
3 to denote the set of Hintikka sets over Cl(Dem
(H
;
3 
)) that contain
Dem
(H
;
3 
). (Recall that for any set of sentences
, Cl(
) denotes the closure
of
; see Deﬁnition 6.23.)
a
Remark 6.44 Suppose that
A is an atom over
, and that
3 
2
A. As
A is
satisﬁable, so is
Dem
(A;
3 
). From this it follows that there is at least one atom
in
A
3 that contains
Dem
(A;
3 
). For suppose
M;
w

Dem
(A;
3 
). Let
	
be the set of all formulas satisﬁed in
M at
w. Then
	
\ Cl(Dem
(A;
3 
)) is a an
atom over Cl(Dem
(A;
3 
)) that contains
Dem
(A;
3 
).
Furthermore, as the reader can easily ascertain, for any formula
,
 is satisﬁable
iff there is an atom
A over Cl() that contains
.
a
Deﬁnition 6.45 Suppose
H and
 are ﬁnite sets of formulas such that
H is a
Hintikka set over
. Then
H
 Pow(
) is a witness set generated by
H on
 if
H
2
H and
(i) if
I
2
H, then for each
3 
2
I, there is a
J
2
I
3 such that
J
2
H.
(ii) if
J
2
H and
J
6=
H then for some
n
>
0 there are
I
0
;
:
:
:
;
I
n
2
H such
that
H
=
I
0,
J
=
I
n, and for each
0

i
<
n there is some formula
3 
2
I
i such that
I
i+1
2
I
i
3 .
The degree of a ﬁnite set of formulas
 is simply the maximum of the degrees of
the formulas contained in
; that is,
deg
(
)
=
max
fdeg
()
j

2

g.
a



6.7 PSPACE
387
For all choices of
H and
, any witness set
H generated by
H on
 must be ﬁnite,
for
H
 Pow
(
), which is a ﬁnite set. Further, observe that if
I
;
J
2
H and
J
2
I
3 then the degree of
J is strictly less than that of
I. Moreover, observe that
item (ii) of the previous deﬁnition is essentially a ‘no junk’ condition: if
J belongs
to
H, it is there because it is generated by some other elements of
H, and ultimately
by
H itself.
Lemma 6.46 Suppose that
H and
 are ﬁnite sets of formulas such that
H is a
Hintikka set over
. Then
H is an atom iff there is a witness set generated by
H
on
.
Proof. For the left to right direction we proceed by induction on the degree of
.
Let
deg
(
)
=
0, and suppose
H is an atom. Trivially,
H
=
fH
g is a witness set
generated by
H. For the inductive step, suppose the required result holds for all
pairs
H
0 and

0 such that
H
0 is an atom of

0 and
deg
(
0
)
<
n. Let
H be an atom
of
 such that
deg
(
)
=
n. Then, as we noted in Remark 6.44, for all
3 
2
H
there exists at least one atom
I
 in
H
3 . As the degree of Cl(Dem
(H
;
3 
))
<
n,
for all
3 
2
H, the inductive hypothesis applies and every such atom
I
 generates
a witness set
I
 on Cl(Dem
(H
;
3 
)). Deﬁne
H
=
fH
g
[
[
3 
2H
I
 
:
Clearly
H is a witness set generated by
H on
.
For the right to left direction, we will show that if
H is a witness set on

generated by
H, then
H can be satisﬁed in a model
(F;
V
) where
F is a ﬁnite tree
of depth at most
deg
(H
). This is stronger than the stated result, and later it will
help us understand why K-satisﬁability is solvable in PSPACE. Assume we have
a countably inﬁnite set of new entities
W
=
fw
0
;
w
1
;
w
2
;
w
3
;
:
:
:
g at our disposal.
We will use (ﬁnitely many) elements of
W to build a model for
H, using a ﬁnitary
version of the step-by-step method discussed in Section 4.6. This model will be a
tree, thus showing once again that K has the tree model property.
Deﬁne
W
0
=
fw
0
g,
R
0
=
?,
f
0
(w
0
)
=
H. Suppose
W
n,
R
n and
f
n have been
deﬁned. If for all
w
2
W
n such that
3 
2
f
n
(w
) there exists a
w
0
2
W
n such that
(i)
 
2
f
n
(w
0
) and (ii)
f
n
(w
0
)
2
f
n
(w
)
3 , then halt the step-by-step construction.
Otherwise, if there is a
w
2
W
n such that
3 
2
f
n
(w
), while for no
w
0
2
W
n are
these two conditions satisﬁed, then carry on to stage
n
+
1 and deﬁne:
W
n+1
=
W
n
[
fw
n+1
g;
R
n+1
=
R
n
[
f(w
;
w
n+1
)g;
f
n+1
=
f
n
[
f(w
n+1
;
I
)g;



388
6 Computability and Complexity
where
I
2
H is such that
I
2
f
n
(w
)
3 . Note that because
H is a witness set it
will always be possible to ﬁnd such an
I.
This step-by-step procedure halts after ﬁnitely many steps since each
I
2
H con-
tains only ﬁnitely many formulas of the form
3 (thus ensuring that the tree we
are constructing is ﬁnitely branching), and whenever
R
n
w
w
0, then
deg
(f
n
(w
0
))
<
deg
(f
n
(w
)) (thus ensuring that the tree is not only ﬁnite, but shallow: it has
depth at most
deg
(H
)). Let
m be the stage at which it halts, and deﬁne
F to
be
(W
m
;
R
m
). To construct the desired model for
H, it only remains to deﬁne a
suitable valuation
V , and we do this as follows: choose
V to be any function from
 to
P
(W
m
) satisfying
w
2
V
(p) iff
p
2
f
m
(w
), for all
p
2
. Let
M
=
(F;
V
).
Exercise 6.7.1 asks the reader to show that
M;
w
0

H; an immediate consequence
is that
H is an atom.
a
Two remarks. The above proof shows that every atom is satisﬁable in a shallow
tree-based model — a fact which will prove to be important below. Second, we now
have a syntactic criterion — namely the existence or non-existence of witness sets
— for determining whether a Hintikka set is K-satisﬁable. (In short, we have just
proved a completeness result.) Moreover, the criterion is intuitively computable:
witness sets are simple ﬁnite structures, thus it seems reasonable to expect that we
can algorithmically test for their existence. And indeed we can.
We now deﬁne the Witness algorithm. This takes as input two ﬁnite sets of
formulas
H and
 and returns the value true if and only if there is a witness set
generated by
H on
.
*function
Witness
(H
;

) returns boolean*
begin
if
H is a Hintikka set over

and for each subformula
3 
2
H there is a set of formulas
I
2
H
3 such that
Witness
(I
; Cl
(Dem
(H
;
3 
)))
then return true
else return false
end
Note that
Witness is an intuitively acceptable algorithm — and hence (by Church’s
thesis) implementable on a Turing machine. Checking that
H is a Hintikka set
over
 involves ascertaining that
 is closed, and that
H satisﬁes the properties
demanded of Hintikka sets; these tasks involve only simple syntactic checking.
Moreover, both the ‘and for each subformula . . . there is’ clause and the recursive
call to
Witness are clearly computable: the ﬁrst involves search through a ﬁnite
space, while the recursive call performs the same tasks on input of lower degree.
Thus
Witness is indeed an algorithm. Moreover, it is correct: if
H and
 are
ﬁnite sets of formulas, then
Witness
(H
;

) returns true iff
H is Hintikka set over



6.7 PSPACE
389
 that generates a witness set in
. This follows by induction on the degree of
.
The right to left direction is easy, while the left to right direction is similar to the
proof of Lemma 6.46; see Exercise 6.7.2.
We are now ready for the main result.
Theorem 6.47 K-satisﬁability is in PSPACE.
Proof. It follows from Lemma 6.46 and the correctness of
Witness that for any
formula
,
 is satisﬁable iff there is an
H
 Cl() such that

2
H and
Witness
(H
; Cl
()) returns the value true. Thus, if we can show that
Witness
can be given a PSPACE implementation, we will have the desired result. We will
implement
Witness on a non-deterministic Turing machine. Given any formula
,
this machine will non-deterministically pick a Hintikka set
H in Cl() that con-
tains
, and run
Witness
(H
; Cl()). It will be easy to show that this machine runs
in non-deterministic PSPACE (that is, NPSPACE). But then it follows by an appeal
to Savitch’s Theorem (PSP
A
CE
=
NPSP
A
CE; see Section C) that the required
PSPACE implementation exists.
So how do we implement
Witness on a non-deterministic Turing machine? The
key points are the following:
(i) All sets of formulas used in the execution of the program are subsets of
Cl(), and we can represent any such subset by using pointers to the con-
nectives and proposition letters in
’s representation: a pointer to a propo-
sitional letter will mean that the letter belongs to the subset, and a pointer to
a connective means that the subformula built using that connective belongs
to it. Thus encoding a subset of Cl() requires only space
O
(jj) (that is,
space of the order of the size of
).
(ii) The ‘and for each subformula
3 
2
H’ part can be handled by treating
each subformula in turn. As any subformula can be represented using a
pointer to
’s representation, we can cycle through all possible subformu-
las, using only polynomial space, by cycling through these pointers. More-
over, as we are using a non-deterministic Turing machine, the ‘there is a set
of formulas . . . ’ clause can be implemented by making non-deterministic
choices. Note that although
H
3 is a set of sets of formulas, to verify
whether
I belongs to it is a rather trivial task, given the deﬁnition of
H
3 .
(iii) To enable the recursive calls to be made, we implement a stack on our
Turing machine. To perform the recursion, we copy the formula
 onto the
stack and point to propositional variables and connectives to indicate the
subsets of interest.
So, suppose we run
Witness on input
H and
. The crucial point that must be
investigated is whether the recursive calls to
Witness cause a blow-up in space



390
6 Computability and Complexity
requirements. From items (i), (ii) and (iii) it is clear that at each level of recur-
sion we use space
O
(jj). How long does it take for the recursion to bottom out?
Note that after
deg
() recursive calls,

=
?. That is, the depth of recursion is
bounded by
deg
() and hence by
jj. Thus, when we implement
Witness on a
non-deterministic Turing machine the total amount of space required is
O
(jj
2
),
hence the algorithm runs in NPSPACE. Thus, by Savitch’s theorem, we conclude
that K-satisﬁability is in PSPACE.
a
The appeal to Savitch’s theorem in the above proof can be avoided:
Witness can
be implemented on a deterministic Turing machine. This involves replacing the
non-deterministic choice used in item (iii) by brute force search through subsets
of Cl() that uses only polynomial space, and the reader is asked to do this in
Exercise 6.7.4. But the above proof illustrates why Savitch’s Theorem is so useful
in practice: by freeing us to think in terms of non-deterministic computations, it
reduces the required bookkeeping to a minimum.
Let us try and pin down the key intuition underlying Theorem 6.47. K lacks
the polysize model property, but in spite of this the K-satisﬁability problems can
be determined in PSPACE. Why? The key lies in the proof of Lemma 6.46 which
showed that every atom is satisﬁable in a shallow ﬁnite tree-based model. Such
models make it easy to visualize the explorations that
Witness makes as it tests
the satisﬁability of
: it just works out what each branch of such a model must
contain. While the size of the entire model may be exponential in
jj it is not
necessary to keep track of all this information. The locally relevant information is
simply the information on each branch — and we know that the tree has depth at
most
deg
()
+
1. In short,
Witness exploits the fact that only shallow tree-based
models are needed to determine K-satisﬁability.
PSPACE algorithms have been devised for a number of well-known logics in-
cluding T, K4 and S4, the temporal counterparts of K, T, K4 and S4, and multi-
modal K, T, K4, S4 and S5. While proofs of these results are essentially reﬁne-
ments of the proof Theorem 6.47, some are rather tricky. The reader who does
Exercise 6.7.3, which asks for a PSPACE algorithm for K4, will ﬁnd out why. In
some cases alternative methods are preferable; see the Notes for pointers.
Ladner’s theorem
We are ready to prove the major result of the section: every normal modal logic
between K and S4 is PSPACE-hard, and hence (assuming PSPACE
6= NP) the
satisﬁability problems for all these logics are tougher than the satisﬁability problem
for propositional logic. We prove this by giving a polynomial time reduction of
the validity problem for prenex quantiﬁed boolean formulas to all these modal



6.7 PSPACE
391
satisﬁability problems. The reduction boils down to forcing the existence of certain
tree-based models, and we will be able to reuse much of our previous work.
Deﬁnition 6.48 The set of quantiﬁed boolean formulas is the smallest set
X con-
taining all formulas of propositional calculus such that if

2
X and
p is a proposi-
tion letter, then both
8p
 and
9p

2 S. The quantiﬁers range over the truth values
1 (true) and 0 (false), and a quantiﬁed boolean formula without free variables is
valid if and only if it evaluates to 1.
A quantiﬁed boolean formula is said to be in prenex form if it is of the form
Q
1
p
1



Q
m
p
m

(p
1
;
:
:
:
;
p
m
); here
Q is either
8 or
9, and

(p
1
;
:
:
:
;
p
m
) is a for-
mula of propositional logic. We will refer to such prenex formulas as QBFs.
a
The problem of deciding whether a QBF containing no free variables is valid is
called the QBF-validity problem, and it is known to be PSPACE-complete.
We are going to deﬁne a polynomial time translation
f
L from QBFs to modal
formulas, and prove that it has the following two properties:
(i) If
 is a QBF-validity, then
f
L
(
) is S4-satisﬁable.
(ii) If
f
L
(
) is K-satisﬁable, then
 is a QBF-validity.
These two properties — together with the known PSPACE-hardness of the QBF-
validity problem — will lead directly to the desired theorem.
Let’s think about what is involved in evaluating a QBF. We start by peeling off
the outermost quantiﬁer. If it is of the form
9p we choose one of the truth values
1 or
0 and substitute for the newly freed occurrences of
p. On the other hand, if it
is of the form
8p we must substitute both
1 and
0 for the newly freed occurrences
of
p. In this fashion, we work our way successively through the preﬁxed list of
quantiﬁers until we reach the matrix, a formula of propositional logic.
Abstractly considered we are generating a tree. This tree consists of the root
node, and then — working inwards along the quantiﬁer string — each existential
quantiﬁer extends it by adding a single branch, and each universal quantiﬁer ex-
tends it by adding two branches. Indeed, we are even generating an annotated tree:
we can label each node with the substitution it records. For example, corresponding
to the QBF
8p9q
(p
$
:q
) we have the following annotated tree:
0=q
1=q
1=p
0=p
6
6
   
@
@
@
I
t
t
t
t
t



392
6 Computability and Complexity
(i)
q
0
(ii)
2
(m)
(q
i
!
V
i6=j
:q
j
)
(0

i

m)
(iiia)
2
(m)
(q
i
!
3q
i+1
)
(0

i
<
m)
(iiib)
V
fijQ
i
=8g
2
i
B
i
(iv)
2S
(p
1
;
:p
1
)
^
2
2
S
(p
1
;
:p
1
)
^
2
3
S
(p
1
;
:p
1
)
^



^
2
m 1
S
(p
1
;
:p
1
)
^
2
2
S
(p
2
;
:p
2
)
^
2
3
S
(p
2
;
:p
2
)
^



^
2
m 1
S
(p
2
;
:p
2
)
^
2
3
S
(p
3
;
:p
3
)
^



^
2
m 1
S
(p
3
;
:p
3
)
...
^
2
m 1
S
(p
m 1
;
:p
m 1
)
(v)
2
m
(q
m
!

)
Fig. 6.6. The formula
f
L
(
).
The information in such annotated trees — we will call them quantiﬁer trees —
will play a crucial role. For a start, QBF-validity is witnessed by certain quantiﬁer
trees:
 is a QBF-validity if and only if there is a quantiﬁer tree for
 such that the
substitutions it records ensure that the matrix evaluates to
1. Moreover, quantiﬁer
trees give us a bridge between the QBF world and the modal world:
f
L
(
) will be
a modal formula that describes the structure of a quantiﬁer tree evaluating
.
We deﬁne the translation
f
L by modifying the way we forced the existence of
binary trees in the proof of Theorem 6.42, and we will reuse the macros
B
i and
S
(p
1
;
:p
1
) deﬁned in (6.12) and (6.13), respectively.
Deﬁnition 6.49 Given any QBF

=
Q
1
p
1



Q
m
p
m

(p
1
;
:
:
:
;
p
m
), choose new
propositional variables
q
0
;
:
:
:
;
q
m. Then
f
L
(
) is the conjunction of the formulas
displayed in Figure 6.6.
a
The idea underlying
f
L is this: for any QBF
,
f
L
(
) describes the peel-of-
quantiﬁers-and-substitute evaluation process for
. (That is, it describes how we
generate a quantiﬁer tree for
.) Moreover, it does so using ideas we have met
already: note that (i), (ii) and (iv) are exactly the same formulas we used when
forcing the existence of binary trees.
In fact, the major difference between these formulas and our earlier work lies in
the word binary. Here we don’t always want binary branching: we only want it
when we encounter the quantiﬁer
8. Thus, instead of the earlier (iii) which forced
branching all the way down to level
m, we have the pair of formulas (iiia) and
(iiib). (iiia) guarantees that if
q
i is true and
i
<
m then there is a next level
q
i+1;
which simply amounts to saying that if
i
<
m then we have not yet peeled off
all the quantiﬁers and a new level will be necessary. But it does not force binary



6.7 PSPACE
393
branching. The task of forcing binary branching, when necessary, is left to (iiib).
Note that this formula is simply a selection of conjuncts from our earlier (iii). There
is only one other difference: (v) insists that after
m quantiﬁers have been peeled
off, the propositional matrix
 must be true.
Clearly,
f
L
(
) is polysize in
j
j, thus this translation causes no blowup in space
requirements.
Theorem 6.50 (Ladner’s Theorem) If
 is a normal modal logic such that
K


 S4, then
 has a PSPACE-hard satisﬁability problem. Moreover,
 has a
PSPACE-hard validity problem.
Proof. Fix a modal logic
 with
K


 S4. We are going to prove that
f
L is a
(polynomial time) reduction from the QBF-validity problem to the
-satisﬁability
problem. The crucial step in this proof is summarized in the following two state-
ments:
if
 is a QBF-validity, then
f
L
(
) is satisﬁable on a frame for S4;
(6.14)
and
if
f
L
(
) is satisﬁed in a K-model then
 is a QBF-validity
:
(6.15)
From these two statements the desired result follows immediately. For suppose

is a QBF-validity. Then by (6.14)
f
L
(
) is S4-satisﬁable and hence
-satisﬁable.
Conversely, if
f
L
(
) is
-satisﬁable then it is also K-satisﬁable, and by (6.15)
 is a QBF-validity. Thus
-satisﬁability is PSPACE-hard. That the
-validity
problem is also PSPACE-hard follows immediately from the fact that PSPACE =
co-PSPACE.
It remains to prove (6.14) and (6.15). For (6.14), assume that
 is a QBF-validity.
Generate a quantiﬁer tree witnessing the validity of
; if
 is valid, such a tree
must exist. This tree gives rise to an S4-model for
f
L
(
) as follows. First, take
the transitive and reﬂexive closure of the ‘daughter-of’ relation of the tree; this
gives us the S4-frame we require. Then make the variable
q
i true precisely at the
nodes of level
i;
p
i is to be made true at a node of level
j

i iff the substitution
connected to that node, or its predecessor at level
i returns the value 1 for
p
i. (For
nodes at level
j
<
i it does not matter what truth value we choose for
p
i.) It is
straightforward to check that the formula
f
L
(
) is true in this model at the root of
the tree; see Exercise 6.7.5.
For (6.15), suppose that
 is a QBF of quantiﬁer depth
m, and that
f
L
(
) is
K-satisﬁable. Note that
deg
(f
L
(
))
=
m, hence from the proof of Lemma 6.46
we know that
f
L
(
) holds at the root
r of a tree-based model
M
=
(T
;
R
;
V
) of
depth at most
m. Using clauses (iiia) and (iiib) of the deﬁnition of
f
L
(
), it is
easily veriﬁed that we may cut off branches from this tree such that in the resulting



394
6 Computability and Complexity
tree, a node at level
i
<
m has either one or two successors. This number is one
iff
Q
i+1
=
9. And if
Q
i+1
=
8, then one of the successors satisﬁes
p
i+1 and the
other one,
:p
i+1. But then this reduced tree model is a quantiﬁer tree witnessing
the validity of
.
a
Among other things, Ladner’s theorem tells us that K, T, K4 and S4 have PSPACE-
hard satisﬁability problems. It follows that the temporal counterparts of K, T, K4
and S4, and multi-modal K, T, K4, and S4, are PSPACE-hard too, for they con-
tain the unimodal satisﬁability problems as a special case. Hence, as PSPACE
algorithms are known for these logics, they all have PSPACE-complete satisﬁabil-
ity problems. As PSPACE
= co-PSPACE, these logics have PSPACE-complete
validity problems too.
Exercises for Section 6.7
6.7.1 Show that in the model
M constructed in the proof of Lemma 6.46,
M;
w
0

H.
6.7.2 We claimed that Witness is a correct algorithm. That is, if
H and
 are ﬁnite sets of
formulas, then
Witness
(H
;

) returns true iff
H is Hintikka set over
 that generates a
witness set in
. Prove this.
6.7.3 Adapt the Witness algorithm so that it decides K4 satisﬁability correctly. (Hint:
since you can’t consider smaller and smaller Hintikka sets (why not?) make use of lists of
Hintikka sets, rather than the single Hintikka sets used in the proof for K, and show that
the length of such lists can always be kept polynomial.)
6.7.4 Show how to avoid the use of Savitch’s Theorem in the proof of Theorem 6.47. That
is, show that the
Witness function can be implemented on a deterministic Turing machine.
(Hint: implement the ‘and for each subformula ...there is’ clause by cycling through all
possible subsets of Cl(). This cycling process has a simple implementation using only
space
O
(jj): generate all binary strings of length
jj, and decide of each whether or not
it encodes a subset of Cl
().)
6.7.5 Supply the missing details in the proof of Ladner’s Theorem.
6.7.6 Show that the satisﬁability problem for bimodal S5 is PSPACE-hard.
6.7.7 In this exercise we examine the effects of bounding the number of proposition letters
and of restricting the degree of formulas.
(a) Show that for any ﬁxed
k, the satisﬁability problem for K with respect to a language
consisting of all formulas whose degree is at most
k, is NP-complete.
(b) Show that, in contrast, the satisﬁability problem for S4 remains PSPACE-complete
for languages consisting of all formulas of degree at most
k (k

2).
(c) Now suppose that
, the set of proposition letters, is ﬁnite. Show that for any ﬁxed
k, the satisﬁability problems for K and S4 with respect to a language consisting of
all formulas whose degree is at most
k, is decidable in linear time.



6.8 EXPTIME
395
6.8 EXPTIME
EXPTIME, the class of problems deterministically solvable in exponential time, is
an important complexity class for many modal languages. In particular, when a
modal language has operators
[a] and
[a

] which explore a relation
R
a and its re-
ﬂexive transitive closure
(R
a
)
, its satisﬁability problem is likely to be EXPTIME-
hard, which means that the worst cases are computationally intractable. As such
operator pairs are important in many applications, we need to understand the com-
plexity theoretic issues they give rise to. In this section we examine the satisﬁability
problem for PDL; our discussion illustrates some key themes and introduces some
useful techniques.
Forcing exponentially deep models
By Corollary 6.14 we know that PDL has a decidable satisﬁability problem —
but just how difﬁcult is it? Clearly it is PSPACE-hard, for each basic modality
[a]
is a K operator, and we saw in the previous section (Theorem 6.50) that K has a
PSPACE-hard satisﬁability problem. But can we prove a matching PSPACE upper
bound?
We used a tableaux-like algorithm called
Witness to show that K-satisﬁability
was solvable in PSPACE.
Witness traded on the following insight: while a K-
consistent formula
 may require a satisfying model of size
2
jj, it is always possi-
ble to build a satisfying tree model of this size in which each branch has less than
jj nodes.
Witness tests for K-satisﬁability by building such trees one branch
at a time; as each branch is polynomial in the size of the input,
Witness runs in
PSPACE. However, as we will now show, even small fragments of PDL are strong
enough to force the existence of exponentially deep models.
Proposition 6.51 For every natural number
n there is a satisﬁable PDL formula

n
of size
O
(n
2
) such that every model which satisﬁes

n contains an
R
a-path con-
taining
2
n distinct nodes. Moreover,

n contains occurrences of only two modali-
ties
[a] and
[a

], where
a is an atomic program.
Proof. We will show how to count using this PDL-fragment. Given a natural num-
ber
n, we select
n distinct proposition letters
q
1
;
:
:
:
;
q
n. Using 1 for true, and 0
for false, the list of truth values
[V
(q
n
;
w
);
:
:
:
;
V
(q
i
;
w
);
:
:
:
;
V
(q
1
;
w
)] is the
n-bit
binary encoding of a natural number. We take
V
(q
1
;
w
) to be the least signiﬁcant
digit, and
V
(q
n
;
w
) to be the most signiﬁcant.
We now construct a formula

n which, when satisﬁed at some state
w
0, forces
the (n-bit representation of) zero to hold at
w
0, and forces the existence of a path
of distinct successors of
w
0 which correctly count from
0 to
2
n 1 in binary. For
example, if
n
=
2, the model will contain a path of length
4 from
w
0 to
w
3, and as



396
6 Computability and Complexity
we move along this path we will successively encounter the following truth value
lists:
[0;
0];
[0;
1];
[1;
0
];
[1
;
1
].
To do the encoding, we need to know what happens when we add 1 to a binary
number
m. First suppose that the least signiﬁcant bit of
m is 0; for example,
suppose that
m is 010100. When we add 1 we obtain 010101; that is, we ﬂip the
least signiﬁcant digit to 1 and leave everything else unchanged. We can force this
kind of incrementation in PDL as follows:
INC
0
:=
:q
1
!
0
@
[a]q
1
^
^
j
>1
((q
j
!
[a]q
j
)
^
(:q
j
!
[a]:q
j
)
1
A
:
This guarantees that the value of
q
1 changes to 1 at any successor state, while the
truth values of all the other
q
js remain unchanged.
Now suppose that the least signiﬁcant digit of
m is 1. For example, suppose that
m is 01011. When we add 1 we obtain 01100. We can describe this incrementation
as follows. First, we locate the longest unbroken block of 1s containing the least
signiﬁcant digit and ﬂip all these 1s to 0s. Second, we ﬂip the following digit from 0
to 1 (we have to ‘carry one’). Finally, we leave all remaining digits unchanged. The
following formula forces this kind of incrementation when the longest unbroken
block of 1s containing the least signiﬁcant digit has length
i, where
0
<
i
<
n:
INC
1
(i)
:=
0
@
:q
i+1
^
i
^
j
=1
q
j
1
A
!
0
@
[a](q
i+1
^
i
^
j
=1
:q
j
^
^
k
>i+1
((q
k
!
[a]q
k
)
^
(:q
k
!
[a]:q
k
))
1
A
:
We can now deﬁne the required formula

n:
(:q
n
^



^
:q
1
)
^
[a

]hai>
^
[a

]
 
INC
0
^
n 1
^
i=1
INC
1
(i)
!
:
The ﬁrst conjunct of

n initializes the counting at 0, the second guarantees that
there will always be successor states, while the third guarantees that incrementation
is carried out correctly. Clearly

n is of size
O
(n
2
) and uses only the allowed
modalities.
a
Proposition 6.51 is suggestive. It does not prove that no PSPACE algorithm is
possible, but it does tend to conﬁrm our suspicions that PDL-satisﬁability is com-
putationally difﬁcult. And indeed it is. The remainder of the chapter is devoted to
proving the following result: PDL-satisﬁability problem is EXPTIME-complete.



6.8 EXPTIME
397
The proof methods we use are important in their own right and well worth master-
ing: we will prove EXPTIME-hardness by reduction from the two person corridor
tiling game, and demonstrate the existence of an EXPTIME algorithm using elim-
ination of Hintikka sets.
EXPTIME-hardness via tiling
In Section 6.5 we used tiling problems to prove two undecidability results. We
remarked that tiling problems were also useful for proving complexity results, and
in this section we give an example. We will describe the two person corridor tiling
game and use it to prove the EXPTIME-hardness of PDL-satisﬁability; we make
use of notation and ideas introduced in our discussion of undecidability.
As with our earlier tiling games, the two person corridor tiling game involves
placing tiles on a grid so that colors match, but there are some extra ingredients.
There are two players, and we assume that there is a third person present — the
referee — who starts the game correctly and keeps it ﬂowing smoothly. The referee
will give the players a ﬁnite set
fT
1
;
:
:
:
;
T
s
g of tile types; the players will use tiles
of these types to attempt to tile a grid so that colors match. In addition, the referee
will set aside two special tile types:
T
0 and
T
s+1.
T
0 is there solely to mark the
boundaries of the corridor (we think of the boundaries as having some distinctive
color, say white), while
T
s+1 is a special winning tile, whose role will be described
later.
At the start of play, the referee places
n initial tiles
I
1, . . . ,
I
n in a row. To the
left of
I
1 and to the right of
I
n he places copies of the white tile
T
0. That is, the
following sequence of tiles is the initial position:
I
1
I
2
. . .
I
n 1
I
n
This is the ﬁrst row of the corridor. The white tiles in column
0 and column
n
+
1
mark the boundaries of the corridor. Columns 1 through
n are the corridor proper.
Actually, we may as well stipulate that the referee immediately ﬁlls in columns
0
and
n
+
1 with the special boundary-marking white tile. That is, the players are
going to be playing into the grid inside the following
n-column corridor:
...
I
1
I
2
. . .
I
n 1
I
n
...



398
6 Computability and Complexity
Now the players are ready to start. There are two players, Eloise and Abelard. The
players take turn placing tiles in the corridor, and it’s always Eloise who moves
ﬁrst. The rules for tile placement are strict: the corridor has to be ﬁlled in from
the bottom, from left to right. For example, after Eloise has placed her ﬁrst tile the
corridor will look like this:
...
I
1
T
I
2
. . .
I
n 1
I
n
...
When Abelard replies, he must place his tile immediately to the right of tile
T.
When the players have completed tiling a row, they start tiling the next one, starting
at column 1. In short, the players have no choice about where to place a tile,
only about which type of tile they will place there. The player’s choice of tiles is
subject to the usual color-matching rules of tiling, and any tile placed in column
0 or column
n has to match the white of the corridor tile. (For example, in the
previous diagram, it must be the case that left
(T
)
= white.)
When do the players win or lose? As follows. If after ﬁnitely many rounds a
tiling is constructed in which the special winning tile
T
s+1 is placed in column 1,
Eloise wins. Otherwise (that is, if one of the players can’t make a legal move and
T
s+1 is not in column 1, or if the game goes on inﬁnitely long) Abelard wins.
Now for the EXPTIME-complete problem: given a game, does Eloise have a
winning strategy in that game? That is, can she win the game no matter what
Abelard does? It is useful to think of winning strategies in terms of game trees.
For any game, a game tree for that game records all possible responses Abelard
can make to Eloise’s moves. (Note that we don’t insist that game trees encode all
of Eloise’s options; but it is vital that game trees record all of Abelard’s options.)
Note that Abelard has only ﬁnitely many possible responses, for there are only
ﬁnitely many tile types. Clearly, if Eloise has a winning strategy in a game, then
there is a game tree that describes that strategy: such a tree spells out exactly what
she has to do, and takes all Abelard’s possible responses into account.
Now that we know about game trees, let’s think about winning strategies for
Eloise. In fact, we can recursively characterize this concept. We ﬁrst deﬁne the
notion of a winning position for Eloise in a game tree:
(i) Whenever the winning tile
T
s+1 is placed in column 1, that position is a
winning position for Eloise.
(ii) In case Eloise is to move in position
x, then
x is a winning position for
Eloise if there exists a move to a winning position for Eloise.



6.8 EXPTIME
399
(iii) In case Abelard is to move in position
x, then
x is a winning position for
Eloise if Abelard can make a move and all his moves lead to a winning
position for Eloise.
We now say that Eloise has a winning strategy iff there is a game tree such that
the root of the game tree is a winning position for her. The problem of determin-
ing whether Eloise has a winning strategy is called the two person corridor tiling
problem, which is known to be EXPTIME-complete (see the Notes for references).
Theorem 6.52 The satisﬁability problem for PDL is EXPTIME-hard.
Proof. We show this by reducing the two person corridor tiling problem to the
PDL satisﬁability problem. We will view a game tree as a rooted regular PDL
model with one atomic transition
R
m which codes one move of the game. Given
an instance
T
=
(n;
fT
0
;
:
:
:
;
T
s+1
g) of the two person corridor tiling game (here
n is the width of the corridor, and the
T
i are the tile types), we will show how to
create a formula

T such that
(i) If Eloise has a winning strategy,

T is satisﬁable at the root of some game
tree for
T (viewed as a regular PDL model).
(ii) If

T is satisﬁable, then Eloise has a winning strategy in the game
T; in
fact, she will be able to read off her winning strategy by following a path
through the satisfying model (starting at the point that satisﬁes

T ).
(iii) The formula

T can be computed in time polynomial in
n and
s.
The formula

T contains two kinds of information: it fully describes the structure
of the game tree, and states necessary and sufﬁcient conditions for Eloise to win.
The ﬁrst part boils down to using PDL to describe the initial conﬁguration, that
players move alternately, that colors match, and so on; this is a little tedious, but
straightforward. Stating necessary and sufﬁcient conditions for Eloise to win in-
volves ﬁnding PDL formulas that capture the recursive characterization of winning
strategies, and prevent the game from running for inﬁnitely many moves; this is the
interesting part of the proof.
We use the following proposition letters to construct

T :
(i)
t
0,
t
1, . . . ,
t
s, and
t
s+1. These will be used to represent the tiles. We will
often write
t
0 as white.
(ii) eloise. This will be used to indicate that Eloise has the next move. Its
negation will indicate that Abelard has the next move.
(iii) pos
1
;
:
:
:
; pos
n. We use pos
i to indicate that in the current round, a tile is to
be placed in column
i.
(iv) col
i
(t), for all
0

i

n
+
1 and all
t
2
ft
0
;
t
1
;
:
:
:
;
t
s
;
t
s+1
g. These will
be used to indicate that the tile previously placed in column
i is of type
t.



400
6 Computability and Complexity
(v) win. This means that the current position is a winning position for Eloise.
In addition, we make use of the modalities
[m] and
hmi (‘after every possible
move’ and ‘after some possible move’ respectively) and
[m

], which can be read
as ‘after every possible sequence of moves’.
So let’s describe the structure of the game tree. The following formula records
the situation at the start of play:
eloise
^ pos
1
^ col
0
(white
)
^ col
1
(t
I
1
)
^



^ col
n
(t
I
n
)
^ col
n+1
(white
):
The ﬁrst conjunct says that Eloise has to make the ﬁrst move, while the second
says that she has to place her tile in column 1. The remaining conjuncts simply say
that the tiles previously placed in all columns are those of the initial conﬁguration.
(Of course, these were not placed by the players but by the referee.) That is, they
say that columns 1 through
n contain the initial tiles
I
1, . . . ,
I
n, and that there is a
white corridor tile on each side.
We now write down a series of formulas which regulate the way that further play
takes place. (Note that all these conditions are preceded by the
[m

] modality, thus
ensuring that they continue to hold after any ﬁnite sequence of moves.) We start
by giving the desired meaning to
pos
i and
col
i
(t).
 Tiles always have to be placed in one of columns 1 through
n:
[m

](pos
1
_



_ pos
n
);
and indeed, in exactly one of these columns:
[m

](pos
i
!
:pos
j
)
(1

i
6=
j

n):
 In every column
i, at least one tile type was previously placed:
[m

](col
i
(t
0
)
_



_ col
i
(t
s+1
))
(0

i

n
+
1):
 In every column
i, at most one tile type was previously placed:
[m

](col
i
(t
u
)
!
:col
i
(t
v
))
(0

i

n
+
1 and
0

u
6=
v

s
+
1):
 Moreover, the referee has already placed white tiles in columns 0 and
n
+
1:
[m

](col
0
(white
)
^ col
n+1
(white
)):
 In the course of play, tiles are placed left-to-right (ﬂipping back to column 1
when a row has been completed):
[m

]((pos
1
!
[m]pos
2
)
^
(pos
2
!
[m]pos
3
)
^



^
(pos
n
!
[m]pos
1
)):
 In columns where no tile is placed, nothing changes when a move is made:
[m

](:pos
i
!
((col
i
(t
u
)
!
[m]col
i
(t
u
))
^
(:col
i
(t
u
)
!
[m]:col
i
(t
u
)):
(Here
0

i

n
+
1 and
0

u

s
+
1.)



6.8 EXPTIME
401
With these preliminaries behind us, we can now describe the structure of the game
tree.
 First of all, players alternate:
[m

]((eloise
!
[m]:eloise
)
^
(:eloise
!
[m]eloise
)):
 Next, both players make legal moves; that is, they only place tiles which cor-
rectly match adjacent tiles. It will be helpful to deﬁne the following ternary
relation of ‘compatibility’ between propositional variables:
C
(t
0
;
t;
t
00
) iff
right
(T
0
)
=
left
(T
) and
down
(T
)
=
up
(T
00
);
where
T,
T
0 and
T are the tiles that correspond to the propositional variables
t,
t
0 and
t
00 respectively. That is,
C
(t
0
;
t;
t
00
) holds iff the tile
T can be placed to the
right of tile
T
0 and above tile
T
00. With the aid of this relation we can formulate
the ﬁrst constraint on tile placement as follows:
[m

]

pos
i
^
col
i 1
(t
0
)
^
col
i
(t
00
)
!
[m]
_
fcol
i
(t)
j
C
(t
0
;
t;
t
00
)g

:
(Here
0

i

n, and, by convention,
W
?
=
?.)
 However this constraint is not quite enough; it only ensures matching to the left
and downwards. We also need to ensure that tiles placed in column
n match the
white corridor tile to their right, and we can do this as follows:
[m

]

pos
n
!
[m]
_
fcol
n
(t)
j
right
(T
)
= white
g

:
(Here
t is the proposition letter corresponding to tile
T.)
 Next, we need to ensure that all of Abelard’s possible responses are encoded in
the model:
[m

]

:eloise
^
p
os
i
^
col
i
(t
00
)
^
col
i 1
(t
0
)
!
^
fhmicol
i
(t)
j
C
(t
0
;
t;
t
00
)g

:
(Here
1

i
<
n, and, by convention,
V
?
=
>.)
That completes our description of the game tree. So let’s turn to our other task:
ensuring that Eloise indeed has a winning strategy. We will do this with the help of
our recursive characterization of winning strategies, thus the ﬁrst step is easy; we
simply state that the initial position is a winning position for Eloise:
win:
Next, we spell out the recursive conditions:
[m

]
(
win
!
(col
1
(t
s+1
)
_
(:eloise
^
hmi>
^
[m]win
)
_
(eloise
^
hmiwin
)))
:
We’re almost there — but we don’t have quite enough. If a game does not ter-
minate, Abelard wins, so we need to rule out this possibility. Now, any inﬁnite



402
6 Computability and Complexity
branch must involve repetition of rows. Indeed, if
N
=
n
s+2, then if a game runs
N moves, repetition must have occurred.
Repetitions do not help Eloise: if she can win, she can do so in fewer than
N moves. So we are simply going to insist that games run fewer than
N moves
— and we can do this with the help of the PDL counter deﬁned in the proof of
Proposition 6.51. To use the notation of that proof, we make use of propositional
variables
q
1, . . . ,
q
n, all initially set to zero, and increment the counter by 1 at every
move. If the counter reaches
N (that is, if all these propositional variables are true
in some successor state) then the game has gone on too long and Abelard wins.
The following formula encodes this observation:
[m

]((counter
=
N
)
!
[m]:win):
Let

T be the conjunction of all these formulas. We must now verify the three
claims made about

T at the start of the proof.
First we need to show that if Eloise has a winning strategy, then there is a game
tree such that

T is satisﬁable at the root of the game tree viewed as a PDL model. If
Eloise has a winning strategy, then she can win in at most
N moves. If
M is the PDL
model corresponding to this at-most-N move strategy, then it is straightforward to
check that

T is satisﬁed at the root of
M.
The second claim is more interesting: we need to show that if
M;
w


T , then
Eloise has a winning strategy in the game
T — and that her winning strategy is
encoded in
M. So suppose there is such a model. Imagine Eloise facing Abelard
across the playing board and consulting this model to choose her moves. As

T is
satisﬁed at
w, win is satisﬁed at
w (remember that the initial position is marked as
winning), hence
eloise
^
hmiwin, the third disjunct of our recursive characteriza-
tion of winning strategy, is true at
w too. Eloise simply needs to pick a successor
state in the model marked as winning to see which tile to place. In short, she plays
the move described in the model, and continues doing so in subsequent rounds.
Though this guarantees that Eloise can keep moving to winning positions, can
she actually win the game after ﬁnitely many moves? Yes! In fact she can win
in at most
N moves. For suppose the
N-th move has just been played (that is,
counter
=
N has just become true). As Eloise has always been moving to winning
positions, the
N-th position is also winning, which means that one of the following
formulas is satisﬁed there:
 col
1
(t
s+1
), or

:eloise
^
hmi>
^
[m]win, or
 eloise
^
hmiwin.
As the counter has reached
N,
[m]:win is satisﬁed too. This means there aren’t
any more winning positions, and so the second and third disjuncts are false. Hence



6.8 EXPTIME
403
col
1
(t
s+1
) is satisﬁed: the winning tile was placed in the ﬁrst column in the previ-
ous round. Thus Eloise has already won.
It remains to check that

T is polynomial in
n and
s. The only point that requires
comment is that we can encode
N. Encoding any natural number
m

2 in binary
requires at most
l
g
(m)
+
1 bits (l
g denotes the logarithm to base 2). So encoding
N takes at most
l
g
(n
s+2
)
=
(s
+
2)l
g
(n)

(s
+
2)n bits, which is polynomial
in
n and
s. Thus we have reduced the two person corridor tiling problem to the
satisﬁability problem for PDL, hence the latter is EXPTIME-hard.
a
As the previous proof makes clear, the EXPTIME-hardness of PDL largely stems
from the fact that it contains a pair of modalities, one for working with a rela-
tion
R
m and the other for reﬂexive transitive closure
(R
m
)
; this is what enabled
us to force exponentially deep models, and to code the corridor tiling problem.
Now, this is not the entire story, for there are logics containing such modality pairs
whose satisﬁability problem is in PSPACE: one example is the modal logic of the
frame
(N
;
S;
<), in a language with two diamonds
hsi and
h<i. Here
N is the
set of natural numbers,
S is the successor-of relation, and
< is the usual ordering
of
N. An even more expressive language — one involving the until operator —
has a PSPACE-complete satisﬁability problem over
(N
;
S;
<); see the Notes for
references.
Despite this, the following is a reliable rule of thumb: when working with a
modal language containing a pair of modalities for working with a relation and its
transitive closure, suspect EXPTIME-hardness. Don’t begin your investigations by
looking for a PSPACE-algorithm, unless you are working with a class of frames
that allows little or no branching. And as this section has demonstrated, an elegant
way of proving EXPTIME-hardness is via the two person corridor tiling game.
Elimination of Hintikka sets
By Theorem 6.52 there are instances of the PDL-satisﬁability problem which will
require exponentially many steps to solve. As yet we have no matching upper
bound. In fact, so far the best solution to PDL-satisﬁability we have is the fol-
lowing nondeterministic algorithm: given a formula
, let
 be the set of all
’s
subformulas, form the collection of all Hintikka sets in
, nondeterministically
choose a model of size at most
2
cjj, and check
 on this model. By the decidabil-
ity result for PDL (Corollary 6.14), if
 is satisﬁable, it is satisﬁable in a model of
at most this size, hence PDL-satisﬁability is solvable in NEXPTIME.
As we will now show, the EXPTIME-hardness result of the previous section can
be matched by an EXPTIME algorithm. Like the PSPACE
Witness algorithm de-
veloped in the previous section, the EXPTIME algorithm for PDL is based around
the idea of Hintikka sets. Here’s how we deﬁne this notion for PDL.



404
6 Computability and Complexity
Deﬁnition 6.53 (Hintikka set for PDL) Let
 be a set of PDL formulas and
:FL
(
) the closure under single negations of its Fisher-Ladner closure (see Deﬁ-
nition 4.79). A Hintikka set over
 is any maximal subset of
:FL
(
) that satisﬁes
the following conditions:
(i) If
:
2
:FL
(
), then
:
2
H iff

62
H.
(ii) If

^
 
2
:FL
(
), then

^
 
2
H iff

2
H and
 
2
H.
(iii) If
h
1
;

2
i
2
:FL
(
), then
h
1
;

2
i
2
H iff
h
1
ih
2
i
2
H.
(iv) If
h
1
[

2
i
2
:FL
(
), then
h
1
[

2
i
2
H iff
h
1
i or
h
2
i
2
H.
(v) If
h

i
2
:FL
(
), then
h

i
2
H iff

2
H or
h
ih

i
2
H.
We denote the set of all Hintikka sets over
 by Hin(
).
a
The ﬁrst clause of Deﬁnition 6.53 ensures the maximality of Hintikka sets: if
H
2
Hin(
) then there is no
H
0
2 Hin(
) such that
H

H
0. So, when the effect
of clause (ii) is taken into account, we see that Hintikka sets are maximal subsets
of
:FL
(
) that contain no blatant propositional inconsistencies. Hintikka sets for
PDL are a generalization of something we met in Chapter 4, namely atoms (see
Deﬁnition 4.80). Clearly
At(
)

H
in(
); indeed,
At(
) contains precisely the
PDL-consistent Hintikka sets.
We use Hintikka sets as follows. We deﬁne a model
M
0 that is built out of
Hin(
). We then iteratively eliminate Hintikka sets from this model, thus forming
a sequence of ever smaller models. This process is deterministic, and terminates
after at most exponentially many steps yielding a model
M. We will then show
that a PDL formula
 is satisﬁable iff it is satisﬁable in
M.
Elimination of Hintikka sets:
Base case. Let
 be a ﬁnite set of PDL formulas, and let
 be the set of
programs that occur in
. Deﬁne
W
0 to be Hin(
). For all basic programs
a, and all
H
;
H
0
2
W
0, deﬁne a binary relation
Q
0
a by
H
Q
0
a
H
0 iff for every

2
H
0, if
hai
2
:FL(
) then
hai
2
H. For all other programs

2
, deﬁne
Q
0
 to be the usual inductively deﬁned PDL relations, and let
F
0
be
(W
0
;
Q
0

)

2. Deﬁne
V
0 by
V
0
(p)
=
fH
2
W
0
j
p
2
H
g, for all
propositional variables
p. Finally, let
M
0 be
(F
0
;
V
0
).
Inductive step. Suppose that
n

0 and that
F
n
=
(W
n
;
Q
n

)

2 and
M
n
=
(F
n
;
V
n
) are deﬁned. Say that
H
2
W
n is demand-satisﬁed iff for all

2
,
and all formulas
 , if
h
i 
2
H then there is an
H
0
2
W
n such that
H
Q
n

H
0
and
 
2
H
0. Then deﬁne:
(i)
W
n+1
=
fH
2
W
n
j
H is demand-satisﬁed
g.
(ii)
Q
n+1

is
Q
n

\
(W
n+1

W
n+1
), and
F
n+1 is
(W
n+1
;
Q
n+1

)

2.
(iii)
V
n+1 is
V
n

W
n+1, and
M
n+1 is
(F
n+1
;
V
n+1
).



6.8 EXPTIME
405
As Hin(
) is ﬁnite and
W
n+1

W
n, then for some
m

0 this inductive
process stops creating new structures. (That is, for all
j

m,
M
j
=
M
m.)
Deﬁne
F
(=
(W
;
Q

)

2
) to be
F
m and deﬁne
M
(=
(F;
V
)) to be
M
m.
The reader should contrast this use of Hintikka sets with the way we used them in
our discussion of PSPACE. The
Witness algorithm carefully builds sequences of
ever smaller Hintikka sets using only PSPACE resources. In sharp contrast to this,
the ﬁrst step of Elimination of Hintikka sets forms all possible Hintikka sets (and
there are exponentially many), and subsequent steps ﬁlter out the useless ones.
Theorem 6.54 The satisﬁability problem for PDL is solvable in deterministic ex-
ponential time.
Proof. Given a PDL formula
 , we will test for its satisﬁability as follows. Letting
 be the set of all
 ’s subformulas, we form Hin(
) and perform elimination of
Hintikka sets. This process terminates yielding a model
M
=
(W
;
Q

;
V
)

2. We
will shortly prove the following claim, for all formulas

2
:
 is satisﬁable iff

2
H for some
H
2
W
:
(6.16)
If we can prove this claim, the theorem follows. To see this, note that the number
of Hintikka sets over
 is exponential in the size of
 , and the process of con-
structing
M
n+1 out of
M
n is a deterministic process that can be performed in time
polynomial in the size of the model, and hence elimination of Hintikka sets is an
EXPTIME algorithm.
So it remains to establish (6.16). For the right to left direction, we will show that
if

2
H for some
H
2
W, then
M itself satisﬁes
 at
H. Indeed, we will show
that for all

2
:FL
(
) and all
H
2
W,
M;
H

 iff

2
H. This proof is by
induction. The clause for propositional symbols is clear, and the step for boolean
combinations follows using clauses (i) and (ii) in the deﬁnition of Hintikka sets.
For the step involving the modal operators we need the following subclaim:
for all
h
i
2
:FL(
),
h
i
2
H iff
for some
H
0
2
W we have
Q

H
H
0 and

2
H
0.
(6.17)
The left to right direction of (6.17) is immediate from the construction of
M, for at
the end of the elimination process only the demand-satisﬁed Hintikka sets remain.
The right to left direction follows by induction on the structure of
; we demon-
strate the base case and the step for modalities constructed using
. Suppose that
for some basic program
a there are Hintikka sets
H and
H
0 such that
H
Q
a
H
0 and

2
H
0. As we built the relation
Q
a by a sequence of eliminations and restriction,
it follows that if
H
Q
a
H
0 then
H
Q
0
a
H
0 — and hence it follows by deﬁnition that
hai
2
H
0. Next, suppose that for some program

 there are Hintikka sets
H and



406
6 Computability and Complexity
H
0 such that
H
Q


H
0 and

2
H
0. But this means there is a ﬁnite sequence
H
=
H
0
Q

H
1
:
:
:
H
n 1
Q

H
n
=
H
0
:
As

2
H
0 it follows inductively that
h
i
2
H
n 1 and hence (due the fact that all
Hintikka sets are Fisher-Ladner closed) that
h

i
2
H
n 1. Again, by induction
on
 it follows that
h
ih

i
2
H
n 2, whence
h

i
2
H
n 2 since this set if
Fisher-Ladner closed. By repeating this argument we obtain that
h

i
2
H
0
=
H. This establishes the inductive proof of (6.17), which in turn completes the
inductive proof of the right to left direction of (6.16).
The fastest way to prove the left to right direction of (6.16) is to make use of
ideas developed when proving the completeness of PDL in Chapter 4. Recall that
we deﬁned
P, the PDL model over
, to be
(At(
);
fR


g

2
;
V

). Here
At(
)
is the set of all atoms over
,
V
 is the natural valuation, and
R

 is deﬁned as
follows: for any two atoms
A and
B, and any basic program
a,
AR

a
B holds iff
b
A
^
hai
b
B is consistent. We deﬁned
R
 for arbitrary programs by closing these
basic relations under composition, union, and reﬂexive transitive closure in the
usual way.
Now, we ﬁrst claim that for all programs
,
R



Q
0
. To see this, ﬁrst observe
that as
At(
)

H
in(
), all atoms
A and
B are in
W
0. So suppose
AR

a
B.
Then, as
b
A
^
hai
b
B is consistent, by the maximality of Hintikka sets we have that
for all

2
B, if
hai
2
:FL(
) then
hai
2
H, that is,
AQ
0

B. Thus for
all atomic programs, the desired inclusion holds. But the relations
R
 and
Q
0

corresponding to arbitrary programs
 are generated out of
R
a and
Q
0
a in the usual
way, hence the inclusion follows for all programs.
The importance of this observation is the following consequence: atoms can
never be discarded in the process of elimination of Hintikka sets. This follows
from the Existence Lemma for PDL (Lemma 4.89, which states that for all atoms
A, and all formulas
h
i 
2
:FL(
), if
h
i 
2
A, there is an atom
B such that
AR


B and
 
2
B. As all atoms belong to
W
0, and as
R



Q
0
, it follows
that every atom in
W
0 is demand-satisﬁed. Moreover, this demand satisﬁability
depends only on the presence of other atoms. It follows that Hintikka elimination
cannot get rid of atoms; that is,
H
in(
)

W.
But now the left to right direction of (6.16) follows easily. Suppose that
 is
satisﬁable. Then
 is PDL-consistent, which means it belongs to at least one atom
in
. This atom will survive the elimination process, and we have the result.
a
This establishes the result we wanted: an EXPTIME algorithm for deciding the
satisﬁability problem for PDL. One question may be bothering some readers: what
is the relationship between the models
M and
P in the proof of Theorem 6.54?
Let us consider the matter. In the proof, we observed that all atoms survive the
Hintikka elimination process. In fact, only atoms can survive. (To see this, simply



6.9 Summary of Chapter 6
407
observe that if some inconsistent Hintikka set
H survived the Hintikka process,
then by (6.16), every formula in
H would be satisﬁed in
M at
H. But as
M is a
regular model, this is impossible.) Hence
M, like
P, is a model built over the set
of atoms. Moreover, we showed in the course of proving the previous theorem that
every relation in
P is a subrelation of the corresponding relation in
M. It follows
that
P is a submodel of
M.
Actually, we can say a little more. Recall from Exercise 4.8.4 that
P is isomor-
phic to a certain ﬁltration. In fact,
M is isomorphic to a ﬁltration over the same
set of sentences. Which ﬁltration? We leave this as an exercise for the reader; see
Exercise 6.8.4.
Exercises for Section 6.8
6.8.1 Enrich the basic modal language with the global modality
A. (This was deﬁned in
Section 6.5.) Show that the satisﬁability problem for the enriched language over the class
of all frames is EXPTIME-hard.
6.8.2 As in the previous exercise, enrich the basic modal language with the global modality
A. Use elimination of Hintikka sets to show that the satisﬁability problem for the enriched
language over the class of all frames is solvable in EXPTIME.
6.8.3 In this exercise we investigate the complexity of deterministic PDL.
(a) Change the PDL-hardness proof so that it works for deterministic PDL. How many
programs do you need? Are two programs sufﬁcient?
(b) Encode with just one functional program that a model has an exponential deep path.
Use this to describe
n-corridor tiling. What can you conclude?
(c) So by now we might have a suspicion that with only one program, the satisﬁability
problem for deterministic PDL might be in PSPACE. But how to prove that? The
best way is to ﬁnd a proof in the literature which can be used almost immediately.
What are the crucial features of functional PDL with one program? Think of a tem-
poral logic which has precisely these same features. Can you interpret functional
PDL into that temporal logic, using some kind of translation function? If so, what
is the complexity of that function? What can you conclude?
6.8.4 Determine the exact relationship between the models
P and
M discussed following
the proof of Theorem 6.54.
6.8.5 PDL has an EXPTIME-complete satisﬁability problem. Suppose we add the the
universal modality to the language. What is the complexity of the resulting satisﬁability
problem?
6.9 Summary of Chapter 6
I Decidability and Undecidability: A logic is called decidable if its satisﬁability
problem (or equivalently, its validity problem) is decidable. Otherwise it is
called undecidable.



408
6 Computability and Complexity
I Decidability via the Finite Model Property: While possession of the ﬁnite model
property does not guarantee decidability, ﬁnite models can be used to prove
decidability given some extra information about the models or the logic. The
decidability of many of the more important modal logics, including PDL, can
be established using such arguments.
I Decidability via Interpretations: Another important technique for establishing
decidability is via interpretation in decidable logical theories, most notably the
monadic second-order theories of countable ﬁnitely- or
!-branching trees. If a
modal logic is complete with respect to a class of models that can be viewed
as monadic second-order deﬁnable substructures of such a tree, its decidability
follows.
I Quasi-Models and Mosaics: Even when a modal logic lacks the ﬁnite model
property, it is sometimes possible to prove decidability using ﬁnite represen-
tations of the information contained in satisfying models. Quasi-models and
mosaics are such representations.
I Undecidability: Undecidability arises easily in modal logic. Moreover, not all
undecidable modal logics have the simplest degree of undecidability; many are
highly undecidable.
I Tiling Problems: Tiling problems can be used to classify the difﬁculty of both
decidable and undecidable problems. The simple geometric ideas underlying
them makes them a useful tool for investigating modal satisﬁability problems.
I The Modal Signiﬁcance of NP: Only modal logics with the polysize model prop-
erty with respect to particularly simple classes of structures can be expected to
have satisﬁability problems in NP. Some important logics, such as the normal
logics extending S4.3, fall into this category.
I The Modal Signiﬁcance of PSPACE: Assuming that PSPACE
6= NP, most
modal satisﬁability problems are not solvable in NP, but are at least PSPACE-
hard. For example, every normal logic between K and S4 has a PSPACE-hard
satisﬁability problem. Explicit PSPACE algorithms are known for some of these
logics.
I The Modal Signiﬁcance of EXPTIME: Modal languages containing a modal-
ity
hr
i and a matching reﬂexive transitive closure modality
hr

i often have
EXPTIME-hard satisﬁability problems. The two person corridor tiling game
is an attractive tool for proving modal EXPTIME-hardness results, and elimina-
tion of Hintikka sets is a standard way of deﬁning EXPTIME algorithms.
Notes
Finite models have long been used to establish decidability, both in modal logic and
elsewhere. Arguments based on ﬁnite axiomatizability together with the f.m.p. are



6.9 Summary of Chapter 6
409
widely used (Theorem 6.15); this approach traces back to Harrop [219]. Also pop-
ular is the use of the strong ﬁnite model property; our formulation (Theorem 6.7) is
based on Goldblatt’s [183]. The fact that a recursive axiomatization together with
the f.m.p. with respect to a recursively enumerable class of models guarantees de-
cidability (Theorem 6.13) seems to have ﬁrst been made explicit in Urquhart [432].
The main point of Urquhart’s article is to prove the result we presented as Exer-
cise 6.2.5: there is a normal modal logic which is recursively axiomatizable, and
has the f.m.p., but is undecidable. This shows that the use of ﬁnite axiomatizations
in the statement of Theorem 6.15 cannot be replaced by recursive axiomatizations,
and Urquhart states Theorem 6.13 as the correct generalization. Exercise 6.2.4
is due to Hemaspaandra (n´ee Spaan); see Spaan [412]. For Craig’s Lemma, see
Craig [95].
The original proof of Rabin’s Tree Theorem may be found in Rabin [372]. Rabin
shows that the decidability of
SnS for
n
>
2 or
n
=
! is reducible to the decidabil-
ity of S2S, and the bulk of his paper is devoted to proving that S2S is decidable.
Rabin’s paper is demanding, and simpler proofs have subsequently been found;
for an up to date survey of Rabin’s Theorem and related material, see Gecseg and
Steinby [174] and Thomas [424]. Rabin’s Theorem was applied in modal logic al-
most immediately: Fine [135] used it to prove decidability results in second-order
modal logic (that is, modal logic in which it is possible to bind propositional vari-
ables), and Gabbay [154, 155, 156] applied it to a wide range of modal logics in
many different languages. Gabbay, Hodkinson, and Reynolds [163] is a valuable
source on the subject.
Two kinds of variations on Rabin’s Tree Theorem are relevant to our readers.
First, the weak monadic second-order theory of
n successor functions (WSnS)
constrains the set variables to range over ﬁnite sets only. The decidability of
WSnS
— which is due to Thatcher and Wright [421] and Doner [121] — is based on a
close correspondence between formulae in
WSnS and ﬁnite automata; any relation
 deﬁnable in
WS2S can also be deﬁned by a tree automaton
A
 that encodes the
satisfying assignments to the formula in the labels on the nodes of the tree that it
accepts. The MONA system [226] implements this decision procedure. Despite
the non-elementary worst-case complexity of
WS2S, MONA works well in prac-
tice on a large range of problems; Basin and Klarlund [28] offer empirical evidence
and an analysis of why this is the case. At the time of writing there are no exper-
imental results evaluating the performance of tools such as MONA on logics such
as propositional dynamic logic. Muller et al. [344] use reductions to
WS2S to
explain why many temporal and dynamic logics are decidable in EXPTIME.
A second variation is important when working with expressive modal languages
(for example, those containing the until operator
U) over highly restricted classes
of models (for example, models isomorphic to the real numbers in their usual order)
it may be necessary to appeal to stronger results about speciﬁc classes of structures;



410
6 Computability and Complexity
Burgess and Gurevich [78] and Gurevich and Shelah [207] are essential reading
here.
Prenex normal form fragments of ﬁrst-order logic are deﬁned using strings over
f9,
9
,
8,
8

g; for instance,
98
 represents the class of ﬁrst-order formulas in
prenex normal form where the quantiﬁer preﬁx starts with an existential quanti-
ﬁer and is followed by a (possibly empty) sequence of universal quantiﬁers. The
decidability of prenex normal form fragments seems to have been studied at least
since early 1920s, which is when Skolem showed that
8

9
 is undecidable. In
1928, Bernays and Sch¨onﬁnkel gave a decision procedure for the satisﬁability of
9

89
 sentences. G¨odel, Kalm´ar and Sch¨utte, independently in 1931, 1933 and
1934 respectively, discovered decision procedures for the satisﬁability of
9

8
2
9

sentences. In 1933, G¨odel showed that
8
3
9
 sentences form a reduction class for
satisﬁability. More recently, Kahr in 1962 proved the undecidability of
898. Con-
sult B¨orger et al. [69] for references and an encyclopedic account of prenex normal
form fragments. For recent work on the relevance of such fragments to modal logic,
see Hustadt [243].
That the two-variable fragment of any ﬁrst-order language is decidable is rel-
evant to a number of modal decidability problems. The ﬁrst decidability result
for this fragment (without equality) was obtained by Scott [393]; Mortimer [343]
established decidability of the two-variable fragment with equality. In contrast,
for
k

3, the
k-variable fragment is undecidable. Consult Gr¨adel, Kolaitis, and
Vardi [201] for complexity results, and Gr¨adel, Otto, and Rosen [202] for related
results.
But perhaps the most natural way to reduce a modal logic is — to another modal
logic! Such reductions are far likelier to yield not only decidability results, but
information about complexity as well. Embeddings of temporal logic into the basic
modal language were ﬁrst studied by Thomason in the mid 1970s (see, for example,
[429]). The approach has gained a new lease of life recently — important results
on the approach can be found in Kracht and Wolter [289] and Kracht [286].
Our use of quasi-models and mosaics has it roots in the work of Zakharyaschev
and others. In particular, Zakharyaschev and Alekseev [460] use such arguments
to show that all ﬁnitely axiomatizable normal logics extending K4.3 are decidable,
and Wolter [450] uses them to show that all ﬁnitely axiomatizable tense logics
extending K
t
4:3 are decidable too.
The mosaic method for proving decidability of a logic stems from N´emeti [345]
who proved that various classes of relativized cylindric algebras have a decidable
equational theory. It has since been used for a wide range of logics, often with a
multi-dimensional ﬂavor; see for instance Marx and Venema [326], Mikul´as [335],
Reynolds [379], Wolter and Zakharyaschev [454], Wolter [453], or the references
in our Notes on the guarded fragment in Chapter 7. With hindsight, even G¨odel’s
proof of the decidability of the satisﬁability problem for the
8
2
9
 prenex sentences



6.9 Summary of Chapter 6
411
can be called a mosaic style proof as well; see the very clear exposition in the
monograph [69]. Mosaics can also be used to investigate modal complexity theory;
see Marx [322] for further details.
Constructing speciﬁc examples of undecidable modal logics is not trivial, and
Thomason [427] contains the earliest explicit example of an undecidable normal
logic in the basic modal language that we know of. Undecidable logics can be
constructed in a variety of ways. Urquhart’s [432] deﬁnition of

U (see Exer-
cise 6.2.5) is neat, if abstract. For undecidable logics in the basic modal language
constructed by detailed simulation of a concrete model of computation (namely,
Minsky machines), see Chagrov and Zakharyaschev [86, Chapter 16].
We have chosen to focus on tiling problems (or domino problems, as they are
sometimes called). These were introduced in Wang [446] and have since been
used in a variety of forms to prove undecidability and complexity results. Proofs
that the
N

N tiling problem is undecidable can be found in Berger [50], Robin-
son [381], and Lewis and Papadimitriou [308]. Two important papers on tiling
are Harel [216, 217]: these demonstrate the ﬂexibility of the method as a tool for
measuring the complexity of logics. Harel uses tiling to give an intuitive account
of highly undecidable (and in particular,

1
1-complete) problems, and these two
papers are probably the best starting point for readers interested in learning more.
The logic KR used in the text to illustrate the tiling method is a notational variant
of Kasper Rounds logic, which is used in computational linguistics to analyze the
notion of feature structure uniﬁcation. Decidability and complexity results for (var-
ious versions of) Kasper Rounds logic can be found in Kasper and Rounds [271]
and Blackburn and Spaan [59]; the latter is the source for Theorems 6.31 and 6.34.
A wide range of related results can be found in the literature (see for example
Harel [215], Halpern and Vardi [209], and Passy and Tinchev [362]). Even in quite
modest languages, asserting something about all paths through a model can lead to
extremely high complexity; for a deeper understanding of why this is so, we refer
the reader to Harel [216, 217], and to Harel, Kozen and Tiuryn [218].
As to complexity-theoretic classiﬁcations of modal satisﬁability and validity
problems, Ladner [299] is one of the earliest analyses; this classic paper is the
source of Ladner’s Theorem and much else besides — it is required reading! Hal-
pern and Moses [212] is an excellent introduction to the decidability and complex-
ity of multi-modal languages. We strongly recommend this article to our readers
— especially those who are encountering complexity theoretic ideas for the ﬁrst
time.
But to return to the results in this chapter, the NP-completeness of S5 was proved
in Ladner [299]. Ono and Nakamura [353] is the source of Theorem 6.38; in
that paper it is also shown that the complexity of the satisﬁability problems in
the language with
F and
P with respect to the following ﬂows of time are all
NP-complete: linear transitive ﬂows of time without endpoints, and dense linear



412
6 Computability and Complexity
transitive ﬂows of time without endpoints (see Exercise 6.6.3). Hemaspaandra’s
Theorem, that all normal modal logics extending S4.3 are NP-complete, may be
found in Spaan [412] and Hemaspaandra [221]). As an aside, the satisﬁability
problem for the ﬂow of time
(N
;
) in the language with just
F was shown to be
NP-complete by Sistla and Clarke [408]; the satisﬁability problem is also shown
to be NP-complete for formulas using
F and the so-called operator nexttime oper-
ator. NP-complete modal-like logics were also investigated in the area of descrip-
tion logic; see below for references. Many NP-completeness results make use of
Lemma 6.36, that frame membership is decidable in polynomial time for ﬁrst-order
deﬁnable frame classes (see in Exercise 6.6.1). This is a standard result in ﬁnite
model theory, and you can ﬁnd a proof in Ebbinghaus and Flum [126].
The key results on PSPACE come from Ladner [299]. Ladner ﬁrst establishes
the existence of PSPACE algorithms for K, T, and S4. His proof of the PSPACE-
completeness of K is like that given in the text, save that Ladner uses ‘concrete
tableaux’ (that is, his algorithm speciﬁes how to construct the required atoms)
rather than ‘abstract tableaux’ (which factor out the required boolean reasoning).
Concrete tableaux are also used by Halpern and Moses [212] to construct PSPACE
algorithms for multi-modal versions of K, S4 — and indeed S5; as they show, log-
ics containing two S5 modalities are PSPACE-hard. This paper gives a very clear
exposition of how to use tableaux systems to establish decidability and complexity
results. The abstract tableaux systems used in this chapter are based on the work of
Hemaspaandra [413, 412, 221]. In the description logic community, tableaux sys-
tems are often called constraint systems [123]; description logics (also known as
concept languages or terminological logics) are essentially multi-modal languages,
often equipped with additional operators to facilitate the representation of knowl-
edge, with global constraints (the so-called TBox), or with means to reason about
individuals and properties (the so-called ABox). Unlike the modal logic commu-
nity, in the description logic community considerable attention has been paid to
reasoning tasks other than satisﬁability or validity checking, such as subsumption
checking, instance checking, and reasoning in the presence of a background the-
ory [122].
In the text (page 403) we also mentioned the fact that, over the natural num-
bers (with
< and the successor function
S), the temporal logic with the until op-
erator has a PSPACE-complete satisﬁability problem; this result is due to Sistla
and Clarke [408]. In the same paper, the authors also show that the satisﬁability
problem for
(N
;
<) is PSPACE-complete for each of the following systems:
F
and
X;
U (until);
U,
S (since),
X; and the extended temporal logic ETL due to
Wolper [449].
The effect of bounding the number of proposition letters and the degree of modal
formulas has been studied by Halpern [210]. In addition to the results mentioned
in Exercises 6.6.5 and 6.7.7, he shows that the PSPACE-completeness results of



6.9 Summary of Chapter 6
413
Ladner and Halpern and Moses hold for multi-modal versions of K, T, S4, S5,
even if there is only one proposition letter in the language. If we restrict to a ﬁnite
degree, then the satisﬁability problem is NP-complete for all the logics considered,
but S4, and if we impose both restrictions, the complexity goes down to linear time
in all cases.
The EXPTIME-hardness of PDL (Theorem 6.52) is due to Fisher and Lad-
ner [143], who explicitly construct a PDL formula which simulates the actions of
a linear space bounded space bounded alternating Turing machine. The (simpler)
proof given in the text stems from Chlebus [91], which establishes the EXPTIME
hardness of the two person corridor tiling game (via a reduction from alternating
Turing machines) and uses it to provide a new proof of EXPTIME hardness for
PDL. Another proof of this via two person corridor tiling can be found in Van
Emde Boas [128], and we have also drawn on this; the recursive formulation of the
game halting condition is due to Maarten Marx.
The existence of an EXPTIME algorithm for PDL, and the method of eliminat-
ing Hintikka sets, comes from Pratt [366]. Other applications of the method can
be found in multi-modal logics of knowledge equipped with a common knowledge
operator (see Halpern and Vardi [209], or Fagin et al. [133]); in computational tree
logic (CTL; see Emerson [129]); in expressive description logics (see Donini et
al. [123]); and in work on the global modality (see Marx [322] or Spaan [412]).
One important approach to the analysis of modal complexity has not been dis-
cussed in this chapter: the use of ﬁnite automata. The theory of automata has
been a subject of research since the 1960s (B¨uchi [70], Thatcher and Wright [421],
Rabin [372]). Especially relevant to temporal and dynamic logics has been a resur-
gence of interest in ﬁnite automata on inﬁnite objects in the 1980s and 1990s; see
Gecseg and Steinby [174], Hayashi [220], and Thomas [423, 424]. A wide va-
riety of automata have been studied, and complexity results for their acceptance
problems are known.
It is often possible to analyze the complexity of modal
satisﬁability problems by reducing them to acceptance problems for types of au-
tomata. For example, general automata-theoretic techniques for reasoning about
relatively simple logics using B¨uchi tree automata have been described by Vardi
and Wolper [435].
We conclude on a more general note. In this chapter we have focussed mainly on
satisﬁability and validity problems — what about the decidability and complexity
of other reasoning tasks? For a start, the global satisﬁability problem (whether
there is a model which satisﬁes a formula at all its points) is important in many ap-
plications and quite different from the (local) satisﬁability problem discussed here.
The discussion of the global modality in Section 6.5 and Exercise 6.8.1 has given
the reader some of the ﬂavor of such problems; for more, see Marx [322]. Other
reasoning tasks that are closely related to the global satisﬁability problem, are often



414
6 Computability and Complexity
studied in the area of description logic mentioned before; see De Giacomo [102]
or Areces and de Rijke [15].
Furthermore, there is a great deal of interest in building practical systems that
evaluate formulas (not necessarily modal ones) in models; this ﬁeld is known as
model checking.
Many interesting problems can be usefully viewed as model
checking problems, and representations which enable evaluation to be performed
efﬁciently — even when the models contain a very large number of states — have
been developed. For an intuitive, modally oriented, introduction to the basic ideas,
see Halpern and Vardi [213]. For further pointers to the model checking literature,
see [332, 93, 245].
Third, it is interesting to inquire into the decidability or otherwise of a wide range
of metalogical properties of logics. One such result was mentioned in Section 3.7:
Chagrova’s Theorem tells us that it is undecidable whether a ﬁrst-order property of
frames can be deﬁned by a modal formula. And many other questions along these
lines can be raised (for example: is it decidable whether a new proof rule is admis-
sible in a given logic?). The best sources for further information on such topics are
Chagrov and Zakharyaschev [86, Chapters 16 and 17] and Kracht [286]. Another
line of results that we should mention here is work on the following question: given
two (ﬁnite) models
M and
N, how hard is it to decide whether they are bisimilar?
Ponse et al. [364] contains a number of valuable starting points for such questions.


