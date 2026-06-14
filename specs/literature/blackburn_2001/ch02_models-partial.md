<!-- Source: Blackburn, de Rijke & Venema (2001). Modal Logic. Cambridge University Press. Chapter 2: Models (pages 50-69, partial - file ends at page 69). BibKey: Blackburn2001 -->


30
1 Basic Concepts
Clearly, for any frame
, if
then for any collection of admissible assign-
ments
on
, we have
too. The converse does not hold. Here is a
counterexample that will be useful in Chapter 4.
Example 1.34 Consider the McKinsey formula,
. It is easy to see
that the McKinsey formula is not valid on the frame
, for we obtain a coun-
termodel by choosing a valuation for
that lets the truth value of
alternate in-
ﬁnitely often (for instance, by letting
be the collection of even numbers).
However there is a general frame based on
in which the McKinsey for-
mula is valid. First some terminology: a set is co-ﬁnite if its complement is ﬁnite.
Now consider the general frame
, where
is the collection of all
ﬁnite and co-ﬁnite sets. We leave it as an exercise to show that
satisﬁes all the
constraints of Deﬁnition 1.32; see Exercise 1.4.5.
To see that the McKinsey formula is indeed valid on , let
be an admissible
valuation, and let
. If
, then
must be co-ﬁnite (why?),
hence for some
every state
is in
. But this means that
,
as required.
Although we will make an important comment about general frames in Section 3.2,
and use them to help prove an incompleteness result in Section 4.4, we will not re-
ally be in a position to grasp their signiﬁcance until Chapter 5, when we introduce
boolean algebras with operators. Until then, we will concentrate on modal lan-
guages as tools for talking about models and frames.
Exercises for Section 1.4
1.4.1 Deﬁne, analogous to
, an operation
on the power set of a frame such that
for an arbitrary modal formula
and an arbitrary valuation
we have that
. Extend this deﬁnition to the dual of a polyadic modal operator.
1.4.2 Consider the basic modal formula
.
(a) Construct a frame
and a general frame
such that
, but
.
(b) Construct a general frame
and a valuation
on
such that
, but
.
1.4.3 Show that if
is any collection of valuations over some frame
, then there is a
smallest general frame
such that
. (‘Smallest’ means that for any general
frame
such that
,
.)
1.4.4 Show that for square arrow frames, the operation
is nothing but composition of
two binary relations. What is
’?
1.4.5 Consider the basic modal language, and the general frame
, where
is the collection of all ﬁnite and co-ﬁnite sets. Show that
is a general frame.


---


1.5 Modal Consequence Relations
31
1.4.6 Consider the structure
where
is the collection of ﬁnite and coﬁnite
subsets of
, and
is deﬁned by
iff
and
and
If
is the accessibility relation of a dyadic modal operator, show that
is a general frame.
1.4.7 Let
be some modal model. Prove that the structure
is a formula
is a general frame.
1.5 Modal Consequence Relations
While the idea of validity in frames (and indeed, validity in general frames) gives
rise to logically interesting formulas, so far we have said nothing about what logical
consequence might mean for modal languages. That is, we have not explained what
it means for a set of modal formulas
to logically entail a modal formula
.
This we will now do. In fact, we will introduce two families of consequence
relations: a local one and a global one. Both families will be deﬁned semantically;
that is, in terms of classes of structures. We will deﬁne these relations for all three
kinds of structures we have introduced, though in practice we will be primarily
interested in semantic consequence over frames. Before going further, a piece of
terminology. If
is a class of models, then a model from
is simply a model
in
. On the other hand, if
is a class of frames (or a class of general frames) then a
model from
is a model based on a frame (general frame) in
.
What is a modally reasonable notion of logical consequence? Two things are
fairly clear. First, it seems sensible to hold on to the familiar idea that a relation
of semantic consequence holds when the truth of the premises guarantees the truth
of the conclusion. Second, it should be clear that the inferences we are entitled to
draw will depend on the class of structures we are working with. (For example,
different inferences will be legitimate on transitive and intransitive frames.) Thus
our deﬁnition of consequence will have to be parametric: it must make reference
to a class of structures S.
Here’s the standard way of meeting these requirements. Suppose we are working
with a class of structures S. Then, for a formula
(the conclusion) to be a logical
consequence of
(the premises) we should insist that whenever
is true at some
point in some model from
, then
should also be true in that same model at the
same point. In short, this deﬁnition demands that the maintenance of truth should
be guaranteed point to point or locally.
Deﬁnition 1.35 (Local Semantic Consequence) Let
be a similarity type, and
let
be a class of structures of type
(that is a class of models, a class of frames,


---


32
1 Basic Concepts
or a class of general frames of this type). Let
and
be a set of formulas and
a single formula from a language of type
. We say that
is a local semantic
consequence of
over
(notation:
) if for all models
from
, and all
points
in
, if
then
Example 1.36 Suppose that we are working with
, the class of transitive
frames. Then:
On the other hand,
is not a local semantic consequence of
over the
class of all frames.
Local consequence is the notion of logical entailment explored in this book, but it
is by no means the only possibility. Here’s an obvious variant.
Deﬁnition 1.37 (Global Semantic Consequence) Let
,
,
and
be as in
Deﬁnition 1.35. We say that
is a global semantic consequence of
over
(notation:
) if and only if for all structures
in
, if
then
(Here, depending on the kind of structures
contains,
denotes either validity in
a frame, validity in a general frame, or global truth in a model.)
Again, this deﬁnition hinges on the idea that premises guarantee conclusions, but
here the guarantee covers global notions of correctness.
Example 1.38 The local and global consequence relations are different. Consider
the formulas
and
. It is easy to see that
does not locally imply
— indeed,
that this entailment should not hold is pretty much the essence of locality. On the
other hand, suppose that we consider a model
where
is globally true. Then
certainly holds at all successors of all states, so
, and so
.
Nonetheless, there is a systematic connection between the two consequence rela-
tions, as the reader is asked to show in Exercise 1.5.3.
Exercises for Section 1.5
1.5.1 Let
be a class of frames for the basic modal similarity type, and let
denote
the class of models based on a frame in
. Prove that
iff
(every point has a predecessor).
Does this equivalence hold as well if we work with
instead?
1.5.2 Let M denote the class of all models, and
the class of all frames. Show that if
then
, but that the converse is false.
1.5.3 Let
be a set of formulas in the basic modal language, and let
denote the class of
all frames. Show that
iff
.


---


1.6 Normal Modal Logics
33
1.5.4 Again, let
denote the class of all frames. Show that the local consequence relation
does have the deduction theorem:
iff
, but the global one does not.
However, show that on the class
of transitive frames we have that
iff
.
1.6 Normal Modal Logics
Till now our discussion has been largely semantic; but logic has an important syn-
tactic dimension, and our discussion raises some obvious questions. Suppose we
are interested in a certain class of frames F: are there syntactic mechanisms capable
of generating
, the formulas valid on F? And are such mechanisms capable of
coping with the associated semantic consequence relation? The modal logician’s
response to such questions is embodied in the concept of a normal modal logic.
A normal modal logic is simply a set of formulas satisfying certain syntactic clo-
sure conditions. Which conditions? We will work towards the answer by deﬁning a
Hilbert-style axiom system called K. K is the ‘minimal’ (or ‘weakest’) system for
reasoning about frames; stronger systems are obtained by adding extra axioms. We
discuss K in some detail, and then, at the end of the section, deﬁne normal modal
logics. By then, the reader will be in a position to see that the deﬁnition is a more-
or-less immediate abstraction from what is involved in Hilbert-style approaches to
modal proof theory. We will work in the basic modal language.
Deﬁnition 1.39 A K-proof is a ﬁnite sequence of formulas, each of which is an
axiom, or follows from one or more earlier items in the sequence by applying a
rule of proof. The axioms of K are all instances of propositional tautologies plus:
(K)
(Dual)
.
The rules of proof of K are:
Modus ponens: given
and
, prove
.
Uniform substitution: given
, prove , where
is obtained from
by uniformly
replacing proposition letters in
by arbitrary formulas.
Generalization: given
, prove
.
A formula
is K-provable if it occurs as the last item of some K-proof, and if this
is the case we write
.
Some comments. Tautologies may contain modalities (for example,
is a
tautology, as it has the same form as
). As tautologies are valid on all frames
(Exercise 1.3.4), they are a safe starting point for modal reasoning. Our decision
to add all propositional tautologies as axioms is an example of axiomatic overkill;


---


34
1 Basic Concepts
we could have chosen a small set of tautologies capable of generating the rest via
the rules of proof, but this reﬁnement is of little interest for our purposes.
Modus ponens is probably familiar to all our readers, but there are two important
points we should make. First, modus ponens preserves validity. That is, if
and
then
. Given that we want to reason about frames, this property is
crucial. Note, however, that modus ponens also preserves two further properties,
namely global truth (if
and
then
) and satisﬁability
(if
and
then
). That is, modus ponens is not
only a correct rule for reasoning about frames, it is also a correct rule for reasoning
about models, both globally and locally.
Uniform substitution should also be familiar. It mirrors the fact that validity ab-
stracts away from the effects of particular assignments: if a formula is valid, this
cannot be because of the particular value its propositional symbols have, thus we
should be free to uniformly replace these symbols with any other formula what-
soever. And indeed, as the reader should check, uniform substitution preserves
validity. Note, however, that it does not preserve either global truth or satisﬁabil-
ity. (For example,
is obtainable from
by uniform substitution, but just because
is globally true in some model, it does not follow that
is too!) In short, uniform
substitution is strictly a tool for generating new validities from old.
That’s the classical core of our Hilbert system, so let’s turn to the the genuinely
modal axioms and rules of proof. First the axioms. The K axiom is the fundamental
one. It is clearly valid (as the reader who has not done Exercise 1.3.4 should now
check) but why is it a useful addition to our Hilbert system?
K is sometimes called the distribution axiom, and is important because it lets us
transform
(a boxed formula) into
(an implication). This
box-over-arrow distribution enables further purely propositional reasoning to take
place. For example, suppose we are trying to prove
, and have constructed a
proof sequence containing both
and
. If we could apply modus
ponens under the scope of the box, we would have proved
. And this is what
distribution lets us do: as K contains the axiom
,
by uniform substitution we can prove
. But then a
ﬁrst application of modus ponens proves
, and a second proves
as
desired.
The Dual axiom obviously reﬂects the duality of
and
; nonetheless, readers
familiar with other discussions of K (many of which have K as the sole modal
axiom) may be surprised at its inclusion. Do we really need it? Yes, we do. In this
book,
is primitive and
is an abbreviation. Thus our K axiom is really shorthand
for
. We need a way to maneuver around
these negations, and this is the syntactic role that Dual plays. (Incidentally had we
chosen
as our primitive operator, Dual would not have been required.) We prefer
working with a primitive
(apart from anything else, it is more convenient for the


---


1.6 Normal Modal Logics
35
algebraic work of Chapter 5) and do not mind adding Dual as an extra axiom. Dual,
of course, is valid.
It only remains to discuss the modal rule of proof: generalization (another com-
mon name for it is necessitation). Generalization ‘modalizes’ provable formulas by
stacking boxes in front. Roughly speaking, while the K axiom lets us apply classi-
cal reasoning inside modal contexts, necessitation creates new modal contexts for
us to work with; modal proofs arise from the interplay of these two mechanisms.
Note that generalization preserves validity: if it is impossible to falsify
, then
obviously we will never be able to falsify
at any accessible state! Similarly,
generalization preserves global truth. But it does not preserve satisfaction: just
because
is true in some state, we cannot conclude that
is true at all accessible
states.
is the minimal modal Hilbert system in the following sense. As we have
seen, its axioms are all valid, and all three rules of inference preserve validity,
hence all K-provable formulas are valid. (To use the terminology introduced in
Deﬁnition 4.9, K is sound with respect to the class of all frames.) Moreover, as we
will prove in Theorem 4.23, the converse is also true: if a basic modal formula is
valid, then it is K-provable. (That is, K is complete with respect to the class of all
frames.) In short, K generates precisely the valid formulas.
Example 1.40 The formula
is valid on any frame, so
it should be K-provable. And indeed, it is. To see this, consider the following
sequence of formulas:
Tautology
Generalization: 1
K axiom
Uniform Substitution: 3
Modus Ponens: 2, 4
Uniform Substitution: 3
Propositional Logic: 5, 6
Propositional Logic: 7
Strictly speaking, this sequence is not a K-proof — it is a subsequence of the proof
consisting of the most important items. The annotations in the right-hand column
should be self-explanatory; for example ‘Modus Ponens: 2, 4’ labels the formula
obtained from the second and fourth formulas in the sequence by applying modus
ponens. To obtain the full proof, ﬁll in the items that lead from line 6 to 8.
Remark 1.41 Warning: there is a pitfall that is very easy to fall into if you are used
to working with natural deduction systems: we cannot freely make and discharge


---


36
1 Basic Concepts
assumptions in the Hilbert system K. The following ‘proof’ shows what can go
wrong if we do:
Assumption
Generalization: 1
Discharge assumption
So we have ‘proved’
! This is obviously wrong: this formula is not valid,
hence it is not K-provable. And it should be clear where we have gone wrong:
we cannot use assumptions as input to generalization, for, as we have already re-
marked, this rule does not preserve satisﬁability. Generalization is there to enable
us to generate new validities from old. It is not a local rule of inference.
For many purposes, K is too weak. If we are interested in transitive frames, we
would like a proof system which reﬂects this. For example, we know that
is valid on all transitive frames, so we would want a proof system that generates
this formula; K does not do this, for
is not valid on all frames.
But we can extend K to cope with many such restrictions by adding extra ax-
ioms. For example, if we enrich K by adding
as an axiom, we obtain
the Hilbert-system called K4. As we will show in Theorem 4.27, K4 is sound and
complete with respect to the class of all transitive frames (that is, it generates pre-
cisely the formulas valid on transitive frames). More generally, given any set of
modal formulas
, we are free to add them as extra axioms to K, thus forming the
axiom system
. As we will learn in Chapter 4, in many important cases it is
possible to characterize such extensions in terms of frame validity.
One ﬁnal issue remains to be discussed: do such axiomatic extensions of K give
us a grip on semantic consequence, and in particular, the local semantic conse-
quence relation over classes of frames (see Deﬁnition 1.35)?
In many important cases they do. Here’s the basic idea. Suppose we are inter-
ested in transitive frames, and are working with K4. We capture the notion of local
consequence over transitive frames in K4 as follows. Let
be a set of formulas,
and
a formula. Then we say that
is a local syntactic consequence of
in K4
(notation:
) if and only if there is some ﬁnite subset
of
such that
. In Theorem 4.27 we will show that
iff
where
denotes local semantic consequence over transitive frames. In short,
we have reduced the local semantic consequence relation over transitive frames to
provability in K4.
Deﬁnition 1.42 (Normal Modal Logics) A normal modal logic
is a set of for-
mulas that contains all tautologies,
, and
,


---


1.6 Normal Modal Logics
37
and that is closed under modus ponens, uniform substitution and generalization.
We call the smallest normal modal logic K.
This deﬁnition is a direct abstraction from the ideas underlying modal Hilbert sys-
tems. It throws away all talk of proof sequences and concentrates on what is really
essential: the presence of axioms and closure under the rules of proof.
We will rarely mention Hilbert systems again: we prefer to work with the more
abstract notion of normal modal logics. For a start, although the two approaches
are equivalent (see Exercise 1.6.6), it is simpler to work with the set-theoretical
notion of membership than with proof sequences. More importantly, in Chapters 4
and 5 we will prove results that link the semantic and syntactic perspectives on
modal logic. These results will hold for any set of formulas fulﬁlling the normality
requirements. Such a set might be the formulas generated by a Hilbert-style proof
system — but it could just as well be the formulas provable in a natural-deduction
system, a sequent system, a tableaux system, or a display calculus. Finally, the
concept of a normal modal logic makes good semantic sense: for any class of
frames
, we have that
, the set of formulas valid on
, is a normal modal logic;
see Exercise 1.6.7.
Exercises for Section 1.6
1.6.1 Give K-proofs of
and
.
1.6.2 Let
be the ‘demodalized’ version of a modal formula
; that is,
is obtained
from
by simply erasing all diamonds. Prove that
is a propositional tautology when-
ever
is K-provable. Conclude that not every modal formula is K-provable.
1.6.3 The axiom system known as S4 is obtained by adding the axiom
to K4.
Show that
; that is, show that S4 does not prove this formula. (Hint: ﬁnd an
appropriate class of frames for which S4 is sound.) If we add this formula as an axiom to
S4 we obtain the system called
. Give an S5-proof of
.
1.6.4 Try adapting K to obtain a minimal Hilbert system for the basic temporal language.
Does your system cope with the fact that we only interpret this language on bidirectional
frames? Then try and deﬁne a minimal Hilbert system for the language of propositional
dynamic logic.
1.6.5 This exercise is only for readers who like syntactical manipulations and have a lot
of time to spare. KL is the axiomatization obtained by adding the L¨ob formula
as an extra axiom to K. Try and ﬁnd a KL proof of
. That is, show
that KL
KL4.
1.6.6 In Chapter 4 we will use
to denote the smallest normal modal logic containing
; the point of the present exercise is to relate this notation to our discussion of Hilbert
systems. So (as discussed above) suppose we form the axiom system
by adding as
axioms all the formulas in
to K. Show that the Hilbert system
proves precisely the
formulas contained in the normal modal logic
.


---


38
1 Basic Concepts
1.6.7 Let
be a class of frames. Show that
is a normal modal logic.
1.7 Historical Overview
The ideas introduced in this chapter have a long history. They evolved as responses
to particular problems and challenges, and knowing something of the context in
which they arose will make it easier to appreciate why they are considered im-
portant, and the way they will be developed in subsequent chapters. Some of the
discussion that follows may not be completely accessible at this stage. If so, don’t
worry. Just note the main points, and try again once you have explored the chapters
that follow.
We ﬁnd it useful to distinguish three phases in the development of modal logic:
the syntactic era, the classical era, and the modern era. Roughly speaking, most of
the ideas introduced in this chapter stem from the classical era, and the remainder
of the book will explore them from the point of view of the modern era.
The syntactic era (1918–1959)
We have opted for 1918, the year that C.I. Lewis published his Survey of Sym-
bolic Logic [306], as the birth of modal logic as a mathematical discipline. Lewis
was certainly not the ﬁrst to consider modal reasoning, indeed he was not even the
ﬁrst to construct symbolic systems for this purpose: Hugh MacColl, who explored
the consequences of enriching propositional logic with operators
(‘it is certain
that’) and
(‘it is impossible that’) seems to have been the ﬁrst to do that (see his
book Symbolic Logic and its Applications [312], and for an overview of his work,
see [373]). But MacColl’s work is ﬁrmly rooted in the 19-th century algebraic
tradition of logic (well-known names in this tradition include Boole, De Morgan,
Jevons, Peirce, Schr¨oder, and Venn), and linking MacColl’s contributions to con-
temporary concerns is a non-trivial scholarly task. The link between Lewis’s work
and contemporary modal logic is more straightforward.
In his 1918 book, Lewis extended propositional calculus with a unary modality
I (‘it is impossible that’) and deﬁned the binary modality
(
strictly implies
) to be I
. Strict implication was meant to capture the notion of logical
entailment, and Lewis presented a
-based axiom system. Lewis and Langford’s
joint book Symbolic Logic [307], published in 1932, contains a more detailed de-
velopment of Lewis’ ideas. Here
(‘it is possible that’) is primitive and
is deﬁned to be
. Five axiom systems of ascending strength, S1–S5,
are discussed; S3 is equivalent to Lewis’ system of 1918, and only S4 and S5 are
normal modal logics. Lewis’ work sparked interest in the idea of ‘modalizing’
propositional logic, and there were many attempts to axiomatize such concepts as


---


1.7 Historical Overview
39
obligation, belief and knowledge. Von Wright’s monograph An Essay in Modal
Logic [456] is an important example of this type of work.
But in important respects, Lewis’ work seems strange to modern eyes. For a
start, his axiomatic systems are not modular. Instead of extending a base system of
propositional logic with speciﬁcally modal axioms (as we did in this chapter when
we deﬁned K), Lewis deﬁnes his axioms directly in terms of
. The modular
approach to modal Hilbert systems is due to Kurt G¨odel. G¨odel [181] showed
that (propositional) intuitionistic logic could be translated into S4 in a theorem-
preserving way. However instead of using the Lewis and Langford axiomatization,
G¨odel took
as primitive and formulated S4 in the way that has become standard:
he enriched a standard system for classical propositional logic with the rule of
generalization, the
axiom, and the additional axioms (
and
).
But the fundamental difference between current modal logic and the work of
Lewis and his contemporaries is that the latter is essentially syntactic. Propositional
logic is enriched with some new modality. By considering various axioms, the
logician tries to pin down the logic of the intended interpretation. This simple view
of logical modeling has its attractions, but is open to serious objections. First, there
are technical difﬁculties. Suppose we have several rival axiomatizations of some
concept. Forget for now the problem of judging which is the best, for there is a
more basic difﬁculty: how can we tell if they are really different? If we only have
access to syntactic ideas, proving that two Hilbert-systems generate different sets
of formulas can be extremely difﬁcult. Indeed, even showing syntactically that two
Hilbert systems generate the same set of formulas can be highly non-trivial (recall
Exercise 1.6.5).
Proving distinctness theorems was standard activity in the syntactic era; for in-
stance, Parry [359] showed that S2 and S3 are distinct, and papers addressing such
problems were common till the late 1950s. Algebraic methods were often used to
prove distinctness. The propositional symbols would be viewed as denoting the
elements of some algebra, and complex formulas interpreted using the algebraic
operations. Indeed, algebras were the key tool driving the technical development
of the period. For example, McKinsey [328] used them to analyze S2 and S4
and show their decidability; McKinsey and Tarski [330], McKinsey [329], and
McKinsey and Tarski [331] extended this work in a variety of directions (giving,
among other things, a topological interpretation of S4); while Dummett and Lem-
mon [125] built on this work to isolate and analyze S4.2 and S4.3, two important
normal logics between S4 and S5. But for all their technical utility, algebraic meth-
ods seemed of limited help in providing reliable intuitions about modal languages
and their associated logics. Sometimes algebraic elements were viewed as multiple
truth values. But Dugundji [124] showed that no logic between S1 and S5 could be
viewed as an
-valued logic for ﬁnite
, so the multi-valued perspective on modal
logic was not suited as a reliable source of insight.


---


40
1 Basic Concepts
The lack of a natural semantics brings up a deeper problem facing the syntac-
tic approach: how do we know we have considered all the relevant possibilities?
Nowadays the normal logic T (that is, K enriched with the axiom
) would
be considered a fundamental logic of possibility; but Lewis overlooked T (it is in-
termediate between S2 and S4 and neither contains nor is contained by S3). More-
over, although Lewis did isolate two logics still considered important (namely S4
and S5), how could he claim that either system was, in any interesting sense, com-
plete? Perhaps there are important axioms missing from both systems? The exis-
tence of so many competing logics should make us skeptical of claims that it is easy
to ﬁnd all the relevant axioms and rules; and without precise, intuitively acceptable,
criteria of what the the reasonable logics are (in short, the type of criteria a decent
semantics provides us with) we have no reasonable basis for claiming success.
For further discussion of the work of this period, the reader should consult the
historical section of Bull and Segerberg [73]). We close our discussion of the syn-
tactic era by noting three lines of work that anticipate later developments: Carnap’s
state-description semantics, Prior’s work on temporal logic, and the J´onsson and
Tarski Representation Theorem for boolean algebras with operators.
A state description is simply a collection of propositional letters. (Actually,
Carnap used state descriptions in his pioneering work on ﬁrst-order modal logic,
so a state for Carnap could be a set of ﬁrst-order formulas.) If
is a collection of
state descriptions, and
, then a propositional symbol
is satisﬁed at
if and
only
. Boolean operators are interpreted in the obvious way. Finally,
is
satisﬁed at
if and only if there is some
such that
satisﬁes
. (See,
for example, Carnap [83, 84].)
Carnap’s interpretation of
in state descriptions is strikingly close to the idea
of satisfaction in models. However one crucial idea is missing: the use of an
explicit relation
over state descriptions. In Carnap’s semantics, satisfaction for
is deﬁned in terms of membership in
(in effect,
is taken to be
). This
implicit ﬁxing of
reduces the utility of his semantics: it yields a semantics for
one ﬁxed interpretation of
, but deprives us of the vital parameter needed to map
logical options.
Arthur Prior founded temporal logic (or as he called it, tense logic) in the early
1950s. He invented the basic temporal language and many other temporal lan-
guages, both modal and non-modal. Like most of his contemporaries, Prior viewed
the axiomatic exploration of concepts as one of the logician’s key tasks. But there
the similarity ends: his writings are packed with an extraordinary number of se-
mantic ideas and insights. By 1955 Prior had interpreted the basic modal lan-
guage in models based on
(see Prior [368], and Chapter 2 of Prior [369]),
and used what would now be called soundness arguments to distinguish logics.
Moreover, the relative expressivity of modal and classical languages (such as the
Prior-Meredith U-calculus [333]) is a constant theme of his writings; indeed, much


---


1.7 Historical Overview
41
of his work anticipates later work in correspondence theory and extended modal
logic. His work is hard to categorize, and impossible to summarize, but one thing
is clear: because of his inﬂuence temporal logic was an essentially semantically
driven enterprise. The best way into his work is via Prior [369].
With the work of J´onsson and Tarski [260, 261] we reach the most important
(and puzzling) might-have-beens in the history of modal logic. Brieﬂy, J´onsson
and Tarski investigated the representation theory of boolean algebras with operators
(that is, modal algebras). As we have remarked, while modal algebras were useful
tools, they seemed of little help in guiding logical intuitions. The representation
theory of J´onsson and Tarski should have swept this apparent shortcoming away for
good, for in essence they showed how to represent modal algebras as the structures
we now call models! In fact, they did a lot more than this. Their representation
technique is essentially a model building technique, hence their work gave the
technical tools needed to prove the completeness result that dominated the classical
era (indeed, their approach is an algebraic analog of the canonical model technique
that emerged 15 years later). Moreover, they provided all this for modal languages
of arbitrary similarity type, not simply the basic modal language.
Unfortunately, their work was overlooked for 20 years; not until the start of the
modern era was its signiﬁcance appreciated. It is unclear to us why this happened.
Certainly it didn’t help matters that J´onsson and Tarski do not mention modal logic
in their classic article; this is curious since Tarski had already published joint pa-
pers with McKinsey on algebraic approaches to modal logic. Maybe Tarski didn’t
see the connection at all: Copeland [94, page 13] writes that Tarski heard Kripke
speak about relational semantics at a 1962 talk in Finland, a talk in which Kripke
stressed the importance of the work by J´onsson and Tarski. According to Kripke,
following the talk Tarski approached him and said he was unable to see any con-
nection between the two lines of work.
Even if we admit that a connection which nows seems obvious may not have
been so at the time, a puzzle remains. Tarski was based in California, which in
the 1960s was the leading center of research in modal logic, yet in all those years,
the connection was never made. For example, in 1966 Lemmon (also based in
California) published a two part paper on algebraic approaches to modal logic [302]
which reinvented (some of) the ideas in J´onsson and Tarski (Lemmon attributes
these ideas to Dana Scott), but only cites the earlier Tarski and McKinsey papers.
We present the work by J´onsson and Tarski in Chapter 5; their Representation
Theorem underpins the work of the entire chapter.
The classical era (1959–1972)
‘Revolutionary’ is an overused word, but no other word adequately describes the
impact relational semantics (that is, the concepts of frames, models, satisfaction,


---


42
1 Basic Concepts
and validity presented in this chapter) had on the study of modal logic. Problems
which had previously been difﬁcult (for example, distinguishing Hilbert-systems)
suddenly yielded to straightforward semantic arguments. Moreover, like all revolu-
tions worthy of the name, the new world view came bearing an ambitious research
program. Much of this program revolved around the concept of completeness: at
last is was possible to give a precise and natural meaning to claims that a logic gen-
erated everything it ought to. (For example, K4 could now be claimed complete
in a genuinely interesting sense: it generated all the formulas valid on transitive
frames.) Such semantic characterizations are both simple and beautiful (especially
when viewed against the complexities of the preceding era) and the hunt for such
results was to dominate technical work for the next 15 years. The two outstanding
monographs of the classical era — the existing fragment of Lemmon and Scott’s
Intensional Logic [303], and Segerberg’s An Essay in Classical Modal Logic [396]
— are largely devoted to completeness issues.
Some controversy attaches to the birth of the classical era. Brieﬂy, relational
semantics is often called Kripke semantics, and Kripke [290] (in which S5-based
modal predicate logic is proved complete with respect to models with an implicit
global relation), Kripke [291] (which introduces an explicit accessibility relation
and gives semantic characterization of some propositional modal logics in terms of
this relation) and Kripke [292] (in which relational semantics for ﬁrst-order modal
languages is deﬁned) were crucial in establishing the relational approach: they are
clear, precise, and ever alert to the possibilities inherent in the new framework: for
example, Kripke [292] discusses provability interpretations of propositional modal
languages. Nonetheless, Hintikka had already made use of relational semantics to
analyze the concept of belief and distinguish logics, and Hintikka’s ideas played
an important role in establishing the new paradigm in philosophical circles; see,
for example, [230]. Furthermore, it has since emerged that Kanger, in a series of
papers and monographs published in 1957, had introduced the basic idea of rela-
tional semantics for propositional and ﬁrst-order modal logic; see, for example,
Kanger [266, 267]. And a number of other authors (such as Arthur Prior, and
Richard Montague [341]) had either published or spoken about similiar ideas ear-
lier. Finally, the fact remains that J´onsson and Tarski had already presented and
generalized the mathematical ideas needed to analyze propositional modal logics
(though they do not discuss ﬁrst-order modal languages).
But disputes over priority should not distract the reader from the essential point:
somewhere around 1960 modal logic was reborn as a new ﬁeld, acquiring new
questions, methods, and perspectives. The magnitude of the shift, not who did
what when, is what is important here. (The reader interested in more detail on
who did what when, should consult Goldblatt [188]. Incidentally, after carefully
considering the evidence, Goldblatt concludes that Kripke’s contributions were the
most signiﬁcant.)


---


1.7 Historical Overview
43
So by the early 1960s it was was clear that relational semantics was an important
tool for classifying modal logics. But how could its potential be unlocked? The
key tool required — the canonical models we discuss in Chapter 4 — emerged
with surprising speed. They seem to have ﬁrst been used in Makinson [314] and
in Cresswell [97] (although Cresswell’s so-called subordination relation differs
slightly from the canonical relation), and in Lemmon and Scott [303] they appear
full-ﬂedged in the form that has become standard.
Lemmon and Scott [303] is a fragment of an ambitious monograph that was in-
tended to cover all then current branches of modal logic. At the time of Lemmon’s
death in 1966, however, only the historical introduction and the chapter on the ba-
sic modal languages had been completed. Nonetheless, it’s a gem. Although for
the next decade it circulated only in manuscript form (it was not published until
1977) it was enormously inﬂuential, setting much of the agenda for subsequent
developments. It unequivocally established the power of the canonical model tech-
nique, using it to prove general results of a sort not hitherto seen. It also introduced
ﬁltrations, an important technique for building ﬁnite models we will discuss in
Chapter 2, and used them to prove a number of decidability results.
While Lemmon and Scott showed how to exploit canonical models directly,
many important normal logics (notably, KL and the modal and temporal logic of
structures such as
,
,
, and
, and their reﬂexive counter-
parts) cannot be analyzed in this way. However, as Segerberg [396, 395] showed,
it is possible to use canonical models indirectly: one can transform the canonical
model into the required form and prove these (and a great many other) complete-
ness results. Segerberg-style transformation proofs are discussed in Section 4.5.
But although completeness and canonical models were the dominant issues of
the classical era, there is a small body of work which anticipates more recent
themes. For example, Robert Bull, swimming against the tide of fashion, used
algebraic arguments to prove a striking result: all normal extensions of S4.3 are
characterized by classes of ﬁnite models (see Bull [72]). Although model-theoretic
proofs of Bull’s Theorem were sought (see, for example, Segerberg [396, page
170]), not until Fine [136] did these efforts succeed. Kit Fine was shortly to play a
key role in the birth of the modern era, and the technical sophistication which was
to characterize his later work is already evident in this paper; we discuss Fine’s
proof in Theorem 4.96. As a second example, in his 1968 PhD thesis [263], Hans
Kamp proved one of the few (and certainly the most interesting) expressivity result
of the era. He deﬁned two natural binary modalities, since and until (discussed in
Chapter 7), showed that the standard temporal language was not strong enough to
deﬁne them, and proved that over Dedekind continuous strict total orders (such as
) his new modalities offered full ﬁrst-order expressive power.
Summing up, the classical era supplied many of the fundamental concepts and
methods used in contemporary modal logic. Nonetheless, viewed from a modern


---


44
1 Basic Concepts
perspective, it is striking how differently these ideas were put to work then. For
a start, the classical era took over many of the goals of the syntactic era. Modal
investigations still revolved round much the same group of concepts: necessity,
belief, obligation and time. Moreover, although modal research in the classical era
was certainly not syntactical, it was, by and large, syntactically driven. That is —
with the notable exception of the temporal tradition — relational semantics seems
to have been largely viewed as a tool for analyzing logics: soundness results could
distinguish logics, and completeness results could give them nice characterizations.
Relational structures, in short, weren’t really there to be described — they were
there to fulﬁll an analytic role. (This goes a long way towards explaining the lack
of expressivity results for the basic modal language; Kamp’s result, signiﬁcantly,
was grounded in the Priorean tradition of temporal logic.) Moreover, it was a self-
contained world in a way that modern modal logic is not. Modal languages and
relational semantics: the connection between them seemed clear, adequate, and
well understood. Surely nothing essential was missing from this paradise?
The modern era (1972–present)
Two forces gave rise to the modern era: the discovery of frame incompleteness re-
sults, and the adoption of modal languages in theoretical computer science. These
unleashed a wealth of activity which profoundly changed the course of modal logic
and continues to inﬂuence it till this day. The incompleteness results results forced
a fundamental reappraisal of what modal languages actually are, while the inﬂu-
ence of theoretical computer science radically changed expectations of what they
could be used for, and how they were to be applied.
Frame-based analyses of modal logic were revealing and intoxicatingly success-
ful — but was every normal logic complete with respect to some class of frames?
Lemmon and Scott knew that this was a difﬁcult question; they had shown, for
example that there were obstacles to adapting the canonical model method to ana-
lyze the logic yielded by McKinsey axiom. Nonetheless, they conjectured that the
answer was yes:
However, it seems reasonable to conjecture that, if a consistent normal K-
system S is closed with respect to substitution instances . . . then
determines
a class
of world systems such that
iff
. We have no proof of
this conjecture. But to prove it would be to make a considerable difference to
our theoretical understanding of the general situation. [303, page 76]
Other optimistic sentiments can be found in the literature of the period. Segerberg’s
thesis is more cautious, simply identifying it as ‘probably the outstanding question
in this area of modal logic at the present time’ [396, page 29].
The question was soon resolved — negatively. In 1972, S.K. Thomason [426]


---


1.7 Historical Overview
45
showed that there were incomplete normal logics in the basic temporal language,
and in 1974 Thomason [427] and Fine [137] both published examples of incom-
plete normal logics in the basic modal language. Moreover, in an important series
of papers Thomason showed that these results were ineradicable: as tools for talk-
ing about frames, modal languages were essentially monadic second-order logic in
disguise, and hence were intrinsically highly complex.
These results stimulated what remains some of the most interesting and innova-
tive work in the history of the subject. For a start, it was now clear that it no longer
sufﬁced to view modal logic as an isolated formal system; on the contrary, it was
evident that a full understanding of what modal languages were, required that their
position in the logical universe be located as accurately as possible. Over the next
few years, modal languages were to be extensively mapped from the perspective of
both universal algebra and classical model theory.
Thomason [426] had already adopted an algebraic perspective on the basic tem-
poral language.
Moreover, this paper introduced general frames, showed that
they were equivalent to semantics based on boolean algebras with operators, and
showed that these semantics were complete in a way that the frame-based seman-
tics was not: every normal temporal logic was characterized by some algebra.
Goldblatt introduced the universal algebraic approach towards modal logic and
developed modal duality theory (the categorical study of the relation between rela-
tional structures endowed with topological structure on the one hand, and boolean
algebras with operators on the other). This led to a belated appreciation of the fun-
damental contributions made in J´onsson and Tarski’s pioneering work. Goldblatt
and Thomason showed that the concepts and results of universal algebra could be
applied to yield modally interesting results; the best known example of this is the
Goldblatt-Thomason theorem a model theoretic characterization of modally deﬁn-
able frame classes obtained by applying the Birkhoff variety theorem to boolean
algebras with operators. We discuss such work in Chapter 5 (and in Chapter 3 we
discuss the Goldblatt-Thomason theorem from the perspective of ﬁrst-order model
theory). Work by Blok made deeper use of algebras, and universal algebra became
a key tool in the exploration of completeness theory (we brieﬂy discuss Blok’s
contribution in the Notes to Chapter 5). The revival of algebraic semantics — to-
gether with a genuine appreciation of why it was so important — is one of the most
enduring legacies of this period.
But the modern period also ﬁrmly linked modal languages with classical model
theory. One line of inquiry that led naturally in this direction was the following:
given that modal logic was essentially second-order in nature, why was it so often
ﬁrst-order, and very simple ﬁrst-order at that? That is, from the modern perspec-
tive, incomplete normal logics were to be expected — it was the elegant results of
the classical period that now seemed in need of explanation. One type of answer
was given in the work of Sahlqvist [388], who isolated a large set of axioms which


---


46
1 Basic Concepts
guaranteed completeness with respect to ﬁrst-order deﬁnable classes of frames.
(We deﬁne the Sahlqvist fragment in Section 3.6, where we discuss the Sahlqvist
Correspondence Theorem, an expressivity result. The twin Sahlqvist Complete-
ness Theorem is proved algebraically in Theorem 5.91.) Another type of answer
was developed in Fine [140] and van Benthem [39, 40]; we discuss this work (albeit
from an algebraic perspective) in Chapter 5.
A different line of work also linked modal and classical languages: an investi-
gation of modal languages viewed purely as description languages. As we have
mentioned, the classical era largely ignored expressivity in favor of completeness.
The Sahlqvist Correspondence Theorem showed the narrowness of this perspec-
tive: here was a beautiful result about the basic modal language that did not even
mention normal modal logics! Expressivity issues were subsequently explored by
van Benthem, who developed the subject now known as correspondence theory;
see [41, 42]. His work has two main branches. One views modal languages as
tools for describing frames (that is, as second-order description languages) and
probes their expressive power. This line of investigation, together with Sahlqvist’s
pioneering work, forms the basis of Chapter 3. The second branch explores modal
languages as tools for talking about models, an intrinsically ﬁrst-order perspec-
tive. This lead van Benthem to isolate the concept of a bisimulation, and prove the
fundamental Characterization Theorem: viewed as a tool for talking about mod-
els, modal languages are the bisimulation invariant fragment of the corresponding
ﬁrst-order language. Bisimulation driven investigations of modal expressivity are
now standard, and much of the following chapter is devoted to such issues.
The impact of theoretical computer science was less dramatic than the discov-
ery of the incompleteness results, but its inﬂuence has been equally profound.
Burstall [80] already suggests using modal logic to reason about programs, but the
birth of this line of work really dates from Pratt [367] (the paper which gave rise
to PDL) and Pnueli [363] (which suggested using temporal logic to reason about
execution-traces of programs). Computer scientists tended to develop powerful
modal languages; PDL in its many variants is an obvious example (see Harel [215]
for a detailed survey). Moreover, since the appearance of Gabbay et al. [167], the
temporal languages used by computer scientists typically contain the until opera-
tor, and often additional operators which are evaluated with respect to paths (see
Clarke and Emerson [92]). Gabbay also noted the signiﬁcance of Rabin’s theo-
rem [372] for modal decidability (we discuss this in Chapter 6), and applied it to a
wide range of languages and logics; see Gabbay [155, 156, 154].
Computer scientists brought a new array of questions to the study of modal logic.
For a start, they initiated the study of the computational complexity of normal log-
ics. Already by 1977 Ladner [299] had showed that every normal logic between K
and S4 had a PSPACE-hard satisﬁability problem, while the results of Fischer and
Ladner [143] and Pratt [366] together show that PDL has an EXPTIME-complete


---


1.7 Historical Overview
47
satisﬁability problem. (These results are proved in Chapter 6.) Moreover, the in-
terest of the modal expressivity studies emerging in correspondence theory was
reinforced by several lines of work in computer science. To give one particularly
nice example, computer scientists studying concurrent systems independently iso-
lated the notion of bisimulation (see Park [358]). This paved the way for the work
of Hennessy and Milner [225] who showed that weak modal languages could be
used to classify various notions of process invariance.
But one of the most signiﬁcant endowments from computer science has actu-
ally been something quite simple: it has helped remove a lingering tendency to see
modal languages as intrinsically ‘intensional’ formalisms, suitable only for analyz-
ing such concepts as knowledge, obligation and belief. During the 1990s this point
was strongly emphasized when connections were discovered between modal logic
and knowledge representation formalisms. In particular, description logics are a
family of languages that come equipped with effective reasoning methods, and a
special focus on balancing expressive power and computational and algorithmic
complexity; see Donini et al. [123]. The discovery of this connection has lead to
a renewed focus on efﬁcient reasoning methods, dedicated languages that are ﬁne-
tuned for speciﬁc modeling tasks, and a variety of novel uses of modal languages;
see Schild [392] for the ﬁrst paper to make the connection between the two ﬁelds,
and De Giacomo [102] and Areces [12, 15] for work exploiting the connection.
And this is but one example. Links with computer science and other disciplines
have brought about an enormous richness and variety in modal languages. Com-
puter science has seen a shift of emphasis from isolated programs to complex enti-
ties collaborating in heterogeneous environments; this gives rise to new challenges
for the use of modal logic in theoretical computer science. For instance, agent-
based theories require ﬂexible modeling facilities together with efﬁcient reason-
ing mechanisms; see Wooldridge and Jennings [455] for a discussion of the agent
paradigm, and Bennet et al. [33] for the link with modal logic. More generally,
complex computational architectures call for a variety of combinations of modal
languages; see the proceedings of the Frontiers of Combining Systems workshop
series for references [16, 160, 273].
Similar developments took place in foundational research in economics. Game
theory (Osborne and Rubinstein [354]) also shows a nice interplay between the no-
tions of action and knowledge; recent years have witnessed an increasing tendency
to give a formal account of epistemic notions, cf. Battigalli and Bonanno [30] or
Kaneko and Nagashima [265]. For modal logics that combine dynamic and epis-
temic notions to model games we refer to Baltag [20] and van Ditmarsch [117].
Further examples abound. Database theory continues to be a fruitful source
of questions for logicians, modal or otherwise.
For instance, developments in
temporal databases have given rise to new challenges for temporal logicians (see
Finger [142]), while decription logicians have found new applications for their


---


48
1 Basic Concepts
modeling and reasoning methods in the area of semistructured data (see Calvanese
et al. [82]). In the related, but more philosophically oriented area of belief re-
vision, Fuhrmann [152] has given a modal formalization of one of the most in-
ﬂuential approaches in the area, the AGM approach [4]. Authors such as Fried-
man and Halpern [150], Gerbrandy and Groeneveld [177], De Rijke [112], and
Segerberg [403] have discussed various alternative modal formalizations.
Cognitive phenomena have long been of interest to modal logicians. This is clear
from examples such as belief revision, but perhaps even more so from language-
related work in modal logic. The feature logic mentioned in Example 1.17 is but
one example; authors such as Blackburn, Gardent, Meyer Viol, and Spaan [59, 53],
Kasper and Rounds [271, 386], Kurtonina [294], Kracht [287], and Reape [378]
have offered a variety of modal logical perspectives on grammar formalisms, while
others have analyzed the semantics of natural language by modal means; see Fer-
nando [134] for a sample of modern work along these lines.
During the 1980s and 1990s a number of new themes on the interface of modal
logic and mathematics received considerable attention. One of these themes con-
cerns links between modal logic and non-wellfounded set theory; work that we
should certainly mention here includes Aczel [2], Barwise and Moss [26], and Bal-
tag [19, 21]; see the Notes to Chapter 2 for further discussion. Non-wellfounded
sets and many other notions, such as automata and labeled transition systems,
have been brought together under the umbrella of co-algebras (cf. Jacobs and Rut-
ten [248]), which form a natural and elegant way to model state-based dynamic sys-
tems. Since it was discovered that modal logic is as closely related to co-algebras
as equational logic is to algebras, there has been a wealth of results reporting on
this connection; we only mention Jacobs [247], Kurz [297] and R¨oßiger [385] here.
Another 1990s theme on the interface of modal logic and mathematics concerns
an old one: geometry. Work by Balbiani et al. [18], Stebletsova [416] and Ven-
ema [441] indicates that modal logic may have interesting things to say about ge-
ometry, while Aiello and van Benthem [3] and Lemon and Pratt [304] investigate
the potential of modal logic as a tool for reasoning about space.
As should now be clear to all our readers, the simple question posed by the modal
satisfaction deﬁnition — what happens at accessible states? — gives us a natural
way of working with any relational structure. This has opened up a host of new
applications for modal logic. Moreover, once the relational perspective has been
fully assimilated, it opens up rich new approaches to traditional subjects: see van
Benthem [44] and Fagin, Halpern, Moses, and Vardi [133] for thoroughly modern
discussions of temporal logic and epistemic logic respectively.
1.8 Summary of Chapter 1
Relational Structures: A relational structure is a set together with a collection


---


1.8 Summary of Chapter 1
49
of relations. Relational structures can be used to model key ideas from a wide
range of disciplines.
Description Languages: Modal languages are simple languages for describing
relational structures.
Similarity Types: The basic modal language contains a single primitive unary
operator
. Modal languages of arbitrary similarity type may contain many
modalities
of arbitrary arity.
Basic Temporal Language: The basic temporal language has two operators
and
whose intended interpretations are ‘at some time in the future’ and ‘at
some time in the past.’
Propositional Dynamic Logic: The language of propositional dynamic logic
has an inﬁnite collection of modal operators indexed by programs
built up
from atomic programs using union
, composition , and iteration ; additional
constructors such as intersection
and test
may also be used. The intended
interpretation of
is ‘some terminating execution of program
leads to a
state where
holds.’
Arrow Logic: The language of arrow logic is designed to talk about any object
that may be represented by arrows; it has a modal constant ’ (‘skip’), a unary
operator
(‘converse’), and a dyadic operator
(‘composition’).
Satisfaction: The satisfaction deﬁnition is used to interpret formulas inside mod-
els. This satisfaction deﬁnition has an obvious local ﬂavor: modalities are inter-
preted as scanning the states accessible from the current state.
Validity: A formula is valid on a frame when it is globally true, no matter what
valuation is used. This concept allows modal languages to be viewed as lan-
guages for describing frames.
General Frames: Modal languages can also be viewed as talking about general
frames. A general frame is a frame together with a set of admissible valuations.
General frames offer some of the advantages of both models and frames and are
an important technical tool.
Semantic Consequence: Semantic consequence relations for modal languages
need to be relativized to classes of structures. The classical idea that the truth
of the premises should guarantee the truth of the conclusion can be interpreted
either locally or globally. In this book we almost exclusively use the local inter-
pretation.
Normal Modal Logics: Normal modal logics are the unifying concept in modal
proof theory. Normal modal logics contain all tautologies, the K axiom and the
Dual axiom; in addition they should be closed under modus ponens, uniform
substitution and generalization.
