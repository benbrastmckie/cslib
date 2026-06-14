<!-- Source: Blackburn, de Rijke & Venema (2001). Modal Logic. Cambridge University Press. Chapter 1: Basic Concepts (pages 1-49). BibKey: Blackburn2001 -->


1
Basic Concepts
Languages of propositional modal logic are propositional languages to which sen-
tential operators (usually called modalities or modal operators) have been added.
In spite of their syntactic simplicity, such languages turn out to be useful tools for
describing and reasoning about relational structures. A relational structure is a
non-empty set on which a number of relations have been deﬁned; they are wide-
spread in mathematics, computer science, artiﬁcial intelligence and linguistics, and
are also used to interpret ﬁrst-order languages.
Now, when working with relational structures we are often interested in struc-
tures possessing certain properties. Perhaps a certain transitive binary relation is
particularly important. Or perhaps we are interested in applications where ‘dead
ends,’ ‘loops,’ and ‘forkings’ are crucial, or where each relation is a partial func-
tion. Wherever our interests lie, modal languages can be useful, for modal oper-
ators are essentially a simple way of accessing the information contained in rela-
tional structures. As we will see, the local and internal access method that modali-
ties offer is strong enough to describe, constrain, and reason about many interesting
and important aspects of relational structures.
Much of this book is essentially an exploration and elaboration of these remarks.
The present chapter introduces the concepts and terminology we will need, and the
concluding section places them in historical context.
Chapter guide
Section 1.1: Relational Structures. Relational structures are deﬁned, and a num-
ber of examples are given.
Section 1.2: Modal Languages. We are going to talk about relational structures
using a number of different modal languages. This section deﬁnes the
basic modal language and some of its extensions.
Section 1.3: Models and Frames. Here we link modal languages and relational
structures. In fact, we introduce two levels at which modal languages can
1


---


2
1 Basic Concepts
be used to talk about structures: the level of models (which we explore
in Chapter 2) and the level of frames (which is examined in Chapter 3).
This section contains the fundamental satisfaction deﬁnition, and deﬁnes
the key logical notion of validity.
Section 1.4: General Frames. In this section we link modal languages and rela-
tional structures in yet another way: via general frames. Roughly speak-
ing, general frames provide a third level at which modal languages can be
used to talk about relational structures, a level intermediate between those
provided by models and frames. We will make heavy use of general frames
in Chapter 5.
Section 1.5: Modal Consequence Relations. Which conclusions do we wish to
draw from a given a set of modal premises? That is, which consequence
relations are appropriate for modal languages? We opt for a local conse-
quence relation, though we note that there is a global alternative.
Section 1.6: Normal Modal Logics. Both validity and local consequence are de-
ﬁned semantically (that is, in terms of relational structures). However, we
want to be able to generate validities and draw conclusions syntactically.
We take our ﬁrst steps in modal proof theory and introduce Hilbert-style
axiom systems for modal reasoning. This motivates a concept of central
importance in Chapters 4 and 5: normal modal logics.
Section 1.7: Historical Overview. The ideas introduced in this chapter have a long
and interesting history. Some knowledge of this will make it easier to
understand developments in subsequent chapters, so we conclude with a
historical overview that highlights a number of key themes.
1.1 Relational Structures
Deﬁnition 1.1 A relational structure is a tuple
whose ﬁrst component is a non-
empty set
called the universe (or domain) of
, and whose remaining compo-
nents are relations on
. We assume that every relational structure contains at
least one relation. The elements of
have a variety of names in this book, includ-
ing: points, states, nodes, worlds, times, instants and situations.
An attractive feature of relational structures is that we can often display them as
simple pictures, as the following examples show.
Example 1.2 Strict partial orders (SPOs) are an important type of relational struc-
ture. A strict partial order is a pair
such that
is irreﬂexive (
) and
transitive (
). A strict partial order
is a linear order (or
a total order) if it also satisﬁes the trichotomy condition:
.
An example of an SPO is given in Figure 1.1, where
, , , , , ,
,


---


1.1 Relational Structures
3
Fig. 1.1. A strict partial order.
and
means ‘ and
are different, and
can be divided by .’ Obviously this is
not a linear order. On the other hand, if we deﬁne
by ‘ is numerically smaller
than ,’ we obtain a linear order over the same universe
. Important examples of
linear orders are
,
,
and
, the natural numbers, integers,
rationals and reals in their usual order. We sometimes use the notation
for
.
In many applications we want to work not with strict partial orders, but with
plain old partial orders (POs). We can think of a partial order as the reﬂexive
closure of a strict partial order; that is, if
is a strict partial order on
, then
is a partial order (for more on reﬂexive closures, see Exer-
cise 1.1.3). Thus partial orders are transitive, reﬂexive (
) and antisymmetric
(
). If a partial order is connected (
)
it is called a reﬂexive linear order (or a reﬂexive total order).
If we interpret the relation in Figure 1.1 reﬂexively (that is, if we take
to
mean ‘
and
are equal, or
can be divided by
’) we have a simple example of
a partial order. Obviously, it is not a reﬂexive linear order. Important examples of
reﬂexive linear orders include
(or
),
,
and
, the
natural numbers, integers, rationals and reals under their respective ‘less-than-or-
equal-to’ orderings.
Example 1.3 Labeled Transition Systems (LTSs), or more simply, transition sys-
tems, are a simple kind of relational structure widely used in computer science. An
LTS is a pair
) where
is a non-empty set of states,
is a non-
empty set (of labels), and for each
,
. Transition systems can
be viewed as an abstract model of computation: the states are the possible states
of a computer, the labels stand for programs, and
means that there is
an execution of the program
that starts in state
and terminates in state
. It is
natural to depict states as nodes and transitions
as directed arrows.
In Figure 1.2 a transition system with states
and labels
is
shown. Formally,
, while
and
. This transition system is actually rather special, for it is deterministic:


---


4
1 Basic Concepts
Fig. 1.2. A deterministic transition system.
if we are in a state where it is possible to make one of the three possible kinds of
transition (for example, an
transition) then it is ﬁxed which state that transition
will take us to. In short, the relations
,
and
are all partial functions.
Deterministic transition systems are important, but in theoretical computer sci-
ence it is more usual to take non-deterministic transition systems as the basic model
of computation. A non-deterministic transition system is one in which the state we
reach by making a particular kind of transition from a given state need not be ﬁxed.
That is, the transition relations do not have to be partial functions, but can be arbi-
trary relations.
Fig. 1.3. A non-deterministic transition system.
In Figure 1.3 a non-deterministic transition system is shown:
is now a non-
deterministic program, for if we execute it in state
there are two possibilities:
either we loop back into
, or we move to
.
Transition systems play an important role in this book. This is not so much be-
cause of their computational interpretation (though that is interesting) but because
of their sheer ubiquity. Sets equipped with collections of binary relations are one
of the simplest types of mathematical structures imaginable, and they crop up just
about everywhere.
Example 1.4 For our next example we turn to the branch of artiﬁcial intelligence
called knowledge representation. A central concern of knowledge representation
is objects, their properties, their relations to other objects, and the conclusions one
can draw about them. For example, Figure 1.4 represents some of the ways Mike
relates to his surroundings.
One conclusion that can be drawn from this representation is that Sue has chil-


---


1.1 Relational Structures
5
loves
owns
son-of
BMW
Diana
Mike
Sue
Fig. 1.4. Mike and others.
dren. Others are not so clear. For example, does Mike love Sue, and does he
love his BMW? Assuming that absence of a not loves arc (like that connecting
the Mike and the Diana nodes) means that the loves relation holds, this is a safe
conclusion to draw. There are often such ‘gaps’ between pictures and relational
structures, and to ﬁll them correctly (that is, to know which relational structure
the picture corresponds to) we have to know which diagrammatic conventions are
being assumed.
Let’s take the picture at face value. It gives us a set BMW Sue Mike Diana
together with binary relations son-of, owns, and not loves. So we have here
another labeled transition system.
Example 1.5 Finite trees are ubiquitous in linguistics. For example, the tree de-
picted in Figure 1.5 represents some simple facts about phrase-structure, namely
that a sentence (S) can consist of a noun phrase (NP) and a verb phrase (VP); an NP
can consist of a proper noun (PN); and VPs can consist of a transitive verb (TV)
and an NP.
S
VP
NP
NP
PN
TV
PN
Fig. 1.5. A ﬁnite decorated tree.
Trees play an important role in this book, so we will take this opportunity to deﬁne
them. We ﬁrst introduce the following important concepts.
Deﬁnition 1.6 Let
be a non-empty set and
a binary relation on
. Then
,
the transitive closure of
, is the smallest transitive relation on
that contains
.
That is,
is a transitive binary relation on
Furthermore,
, the reﬂexive transitive closure of
, is the smallest reﬂexive and


---


6
1 Basic Concepts
transitive relation on
containing
. That is,
is a reﬂexive transitive binary relation on
Note that
holds if and only if there is a sequence of elements
,
,
. . . ,
(
) from
such that for each
we have
. That
is,
means that
is reachable from
in a ﬁnite number of
-steps. Thus
transitive closure is a natural and useful notion; see Exercise 1.1.3.
With these concepts at our disposal, it is easy to say what a tree is.
Deﬁnition 1.7 A tree
is a relational structure
where:
(i)
, the set of nodes, contains a unique
(called the root) such that
.
(ii) Every element of
distinct from
has a unique
-predecessor; that is, for
every
there is a unique
such that
.
(iii)
is acyclic; that is,
. (It follows that
is irreﬂexive.)
Clearly, Figure 1.5 contains enough information to give us a tree
in the sense
just deﬁned: the nodes in
are the displayed points, and the relation
is indicated
by means of a straight line segment drawn from a node to a node immediately
below (that is,
is the obvious successor or daughter-of relation). The root of the
tree is the topmost node (the one labeled S).
But the diagram also illustrates something else: often we need to work with
structures consisting of not only a tree
, but a whole lot else besides. For
example, linguists wouldn’t be particularly interested in the bare tree
just
deﬁned, rather they’d be interested in (at least) the structure
LEFT-OF S NP VP PN TV
Here S, NP, VP, PN, and TV are unary relations on
(note that S and
are distinct
symbols). These relations record the information attached to each node, namely the
fact that some nodes are noun phrase nodes, while others are proper name nodes,
sentential nodes, and so on. LEFT-OF is a binary relation which captures the left-
to-right aspect of the above picture; the fact that the NP node is to the left of the
VP node might be linguistically crucial.
Similar things happen in mathematical contexts. Sometimes we will need to
work with relational structures which are much richer than the simple trees
just deﬁned, but which, perhaps in an implicit form, contain a relation with all the
properties required of
. It is useful to have a general term for such structures; we
will call them tree-like. A formal deﬁnition here would do more harm than good,
but in the text we will indicate, whenever we call a structure tree-like, where this
implicit tree
can be found. That is, we will say, unless it is obvious, which
deﬁnable relation in the structure satisﬁes the conditions of Deﬁnition 1.7. One of


---


1.1 Relational Structures
7
the most important examples of tree-like structures is the Rabin structure, which
we will meet in Section 6.3.
One often encounters the notion of a tree deﬁned in terms of the (reﬂexive) tran-
sitive closure of the successor relation. Such trees we call (reﬂexive and) transitive
trees, and they are dealt with in Exercises 1.1.4 and 1.1.5
Example 1.8 We have already seen that labeled transition systems can be regarded
as a simple model of computation. Indeed, they can be thought of as models for
practically any dynamic notion: each transition takes us from an input state to an
output state. But this treatment of states and transitions is rather unbalanced: it
is clear that transitions are second-class citizens. For example, if we talked about
LTSs using a ﬁrst-order language, we couldn’t name transitions using constants
(they would be talked about using relation symbols) but we could have constants
for states. But there is a way to treat transitions as ﬁrst-class citizens: we can work
with arrow structures.
The objects of an arrow structure are things that can be pictured as arrows. As
concrete examples, the mathematically inclined reader might think of vectors, or
functions or morphisms in some category; the computer scientist of programs; the
linguist of the context changing potential of a grammatically well-formed piece of
text or discourse; the philosopher of some agent’s cognitive actions; and so on. But
note well: although arrows are the prime citizens of arrow structures, this does not
mean that they should always be thought of as primitive entities. For example, in
a two-dimensional arrow structure, an arrow
is thought of as a pair
of
which
represents the starting point of , and
its endpoint.
Having ‘deﬁned’ the elements of arrow structures to be objects graphically rep-
resentable as arrows, we should now ask: what are the basic relations which hold
between arrows? The most obvious candidate is composition: vector spaces have
an additive structure, functions can be composed, language fragments can be con-
catenated, and so on. So the central relation on arrows will be a ternary composi-
tion relation
, where
says that arrow
is the outcome of composing arrow
with arrow
(or conversely, that
can be decomposed into
and ). Note that
in many concrete examples,
is actually a (partial) function; for example, in the
two-dimensional framework we have
iff
and
(1.1)
What next? Well, in all the examples listed, the composition function has a neutral
element; think of the identity function or the SKIP-program. So, arrow structures
will contain degenerate arrows, transitions that do not lead to a different state.
Formally, this means that arrow structures will contain a designated subset
of
identity arrows; in the pair-representation,
will be (a subset of) the diagonal:
iff
(1.2)


---


8
1 Basic Concepts
Another natural relation is converse. In linguistics and cognitive science we might
view this as an ‘undo’ action (perhaps we’ve made a mistake and need to recover)
and in many ﬁelds of mathematics arrow-like objects have converses (vectors) or
inverses (bijective functions). So we’ll also give arrow structures a binary reverse
relation
. Again, in many cases this relation will be a partial function. For exam-
ple, in the two-dimensional picture,
is given by
iff
and
(1.3)
Although there are further natural candidates for arrow relations (notably some
notion of iteration) we’ll leave it at this. And now for the formal deﬁnition: an
arrow frame is a quadruple
such that
,
and
are a ternary,
a binary and a unary relation on
, respectively. Pictorially, we can think of them
as follows:
The two-dimensional arrow structure, in which the universe consists of all pairs
over the set
(and the relations
,
and
are given by (1.1), (1.3) and (1.2),
respectively) is called the square over
, notation:
. The square arrow frame
over
can be pictorially represented as a full graph over
: each arrow object
in
can be represented as a ‘real’ arrow from
to
; the relations
are as pictured above. Alternatively, square arrow frames can be represented two-
dimensionally, cf. the pictures in Example 1.27.
Exercises for Section 1.1
1.1.1 Let
be a quasi-order; that is, assume that
is transitive and reﬂexive. Deﬁne
the binary relation
on
by putting
iff
and
.
(a) Show that
is an equivalence relation
Let
denote the equivalence class of
under this relation, and deﬁne the following rela-
tion on the collection of equivalence classes:
iff
.
(b) Show that this is well-deﬁned.
(c) Show that
is a partial order.
1.1.2 Let
be a transitive relation on a ﬁnite set
. Prove that
is well-founded iff
is
irreﬂexive. (
is called well-founded if there are no inﬁnite paths
.)
1.1.3 Let
be a binary relation on
. In Example 1.2 we deﬁned the reﬂexive closure
of
to be
. But we can also give a deﬁnition analogous to those


---


1.2 Modal Languages
9
of
and
in Deﬁnition 1.6, namely that it is the smallest reﬂexive relation on
that
contains
:
r
is a reﬂexive binary relation on
Explain why this new deﬁnition (and the deﬁnitions of
and
) are well deﬁned. Show
the equivalence of the two deﬁnitions of reﬂexive closure. Finally, show that
if and
only if there is a sequence of elements
,
, ...,
from
such that for each
we have
, and give an analogous sequence-based deﬁnition of reﬂexive
transitive closure.
1.1.4 A transitive tree is an SPO
such that (i) there is a root
satisfying
for all
and (ii) for each
, the set
of predecessors of
is ﬁnite
and linearly ordered by
.
(a) Prove that if
is a tree then
is a transitive tree.
(b) Prove that
is a transitive tree iff
is a tree, where
is the immediate
successor relation given by
iff
and
for no
.
(c) Under which conditions does the converse of (a) hold?
1.1.5 Deﬁne the notion of a reﬂexive and transitive tree, such that if
is a tree then
is a reﬂexive and transitive tree.
1.1.6 Show that the following formulas hold on square arrow frames:
(a)
,
(b)
,
(c)
.
1.2 Modal Languages
It’s now time to meet the modal languages we will be working with. First, we
introduce the basic modal language. We then deﬁne modal languages of arbitrary
similarity type. Finally we examine the following extensions of the basic modal
language in more detail: the basic temporal language, the language of proposi-
tional dynamic logic, and a language of arrow logic.
Deﬁnition 1.9 The basic modal language is deﬁned using a set of proposition let-
ters (or proposition symbols or propositional variables)
whose elements are usu-
ally denoted
,
,
, and so on, and a unary modal operator
(‘diamond’). The
well-formed formulas
of the basic modal language are given by the rule
where
ranges over elements of
. This deﬁnition means that a formula is either a
proposition letter, the propositional constant falsum (‘bottom’), a negated formula,
a disjunction of formulas, or a formula preﬁxed by a diamond.
Just as the familiar ﬁrst-order existential and universal quantiﬁers are duals to
each other (in the sense that
), we have a dual operator
(‘box’)


---


10
1 Basic Concepts
for our diamond which is deﬁned by
. We also make use of the classi-
cal abbreviations for conjunction, implication, bi-implication and the constant true
(‘top’):
,
,
and
.
Although we generally assume that the set
of proposition letters is a countably
inﬁnite
, occasionally we need to make other assumptions. For in-
stance, when we are after decidability results, it may be useful to stipulate that
is
ﬁnite, while doing model theory or frame theory we may need uncountably inﬁnite
languages. This is why we take
as an explicit parameter when deﬁning the set of
modal formulas.
Example 1.10 Three readings of diamond and box have been extremely inﬂuen-
tial. First,
can be read as ‘it is possibly the case that
.’ Under this reading,
means ‘it is not possible that not
,’ that is, ‘necessarily
,’ and examples
of formulas we would probably regard as correct principles include all instances
of
(‘whatever is necessary is possible’) and all instances of
(‘whatever is, is possible’). The status of other formulas is harder to decide. Should
(‘whatever is, is necessarily possible’) be regarded as a general truth
about necessity and possibility? Should
(‘whatever is possible, is
necessarily possible’)? Are any of these formulas linked by a modal notion of log-
ical consequence, or are they independent claims about necessity and possibility?
These are difﬁcult (and historically important) questions. The relational semantics
deﬁned in the following section offers a simple and intuitively compelling frame-
work in which to discuss them.
Second, in epistemic logic the basic modal language is used to reason about
knowledge, though instead of writing
for ‘the agent knows that
’ it is usual to
write
. Given that we are talking about knowledge (as opposed to, say, belief
or rumor), it seems natural to view all instances of
as true: if the agent
really knows that
, then
must hold. On the other hand (assuming that the agent
is not omniscient) we would regard
as false. But the legitimacy of other
principles is harder to judge (if an agent knows that
, does she know that she
knows it?). Again, a precise semantics brings clarity.
Third, in provability logic
is read as ‘it is provable (in some arithmetical
theory) that
.’ A central theme in provability logic is the search for a complete
axiomatization of the provability principles that are valid for various arithmetical
theories (such as Peano Arithmetic). The L¨ob formula
plays a
key role here. The arithmetical ramiﬁcations of this formula lie outside the scope
of the book, but in Chapters 3 and 4 we will explore its modal content.
That’s the basic modal language. Let’s now generalize it. There are two obvious
ways to do so. First, there seems no good reason to restrict ourselves to languages


---


1.2 Modal Languages
11
with only one diamond. Second, there seems no good reason to restrict ourselves
to modalities that take only a single formula as argument. Thus the general modal
languages we will now deﬁne may contain many modalities, of arbitrary arities.
Deﬁnition 1.11 A modal similarity type is a pair
where
is a non-
empty set, and
is a function
.
The elements of
are called modal
operators; we use
(‘triangle’),
,
, . . . to denote elements of
. The function
assigns to each operator
a ﬁnite arity, indicating the number of arguments
can be applied to.
In line with Deﬁnition 1.9, we often refer to unary triangles as diamonds, and
denote them by
or
, where
is taken from some index set. We often assume
that the arity of operators is known, and do not distinguish between
and
.
Deﬁnition 1.12 A modal language
is built up using a modal similarity
type
and a set of proposition letters
. The set
of modal
formulas over
and
is given by the rule
where
ranges over elements of
.
The similarity type of the basic modal language is called
. In the sequel we
sometimes state results for modal languages of arbitrary similarity types, give the
proof for similarity types with diamonds only, and leave the general case as an ex-
ercise. For binary modal operators, we often use inﬁx notation; that is, we usually
write
instead of
. One other thing: note that our deﬁnition permits
nullary modalities (or modal constants), triangles that take no arguments at all.
Such modalities can be useful — we will see a natural example when we discuss
arrow logic — but they play a relatively minor role in this book. Syntactically (and
indeed, semantically) they are rather like propositional variables; in fact, they are
best thought of as propositional constants.
Deﬁnition 1.13 We now deﬁne dual operators for non-nullary triangles. For each
the dual
of
is deﬁned as
. The
dual of a triangle of arity at least
is called a nabla. As in the basic modal language,
the dual of a diamond is called a box, and is written
or
.
Three extensions of the basic modal language deserve special attention. Two of
these, the basic temporal language and the language of propositional dynamic logic
will be frequently used in subsequent chapters. The third is a simple language of
arrow logic; it will provide us with a natural example of a binary modality.
Example 1.14 (The Basic Temporal Language) The basic temporal language is
built using a set of unary operators
. The intended interpretation


---


12
1 Basic Concepts
of a formula
is ‘
will be true at some Future time,’ and the intended inter-
pretation of
is ‘
was true at some Past time.’ This language is called the
basic temporal language, and it is the core language underlying a branch of modal
logic called temporal logic. It is traditional to write
as
and
as
, and
their duals are written as
and
, respectively. (The mnemonics here are: ‘it is
always Going to be the case’ and ‘it always Has been the case.’)
We can express many interesting assertions about time with this language. For
example,
, says ‘whatever has happened will always have happened,’
and this seems a plausible candidate for a general truth about time. On the other
hand, if we insist that
must always be true, it shows that we are
thinking of time as dense: between any two instants there is always a third. And if
we insist that
(the McKinsey formula) is true, for all propositional
symbols
, we are insisting that atomic information true somewhere in the future
eventually settles down to being always true. (We might think of this as reﬂecting
a ‘thermodynamic’ view of information distribution.)
One ﬁnal remark: computer scientists will have noticed that the binary until
modality is conspicuous by its absence. As we will see in the following chapter,
the basic temporal language is not strong enough to express until. We examine a
language containing the until operator in Section 7.2.
Example 1.15 (Propositional Dynamic Logic) Another important branch of mo-
dal logic, again involving only unary modalities, is propositional dynamic logic.
PDL, the language of propositional dynamic logic, has an inﬁnite collection of
diamonds. Each of these diamonds has the form
, where
denotes a (non-
deterministic) program. The intended interpretation of
is ‘some terminating
execution of
from the present state leads to a state bearing the information
.’
The dual assertion
states that ‘every execution of
from the present state leads
to a state bearing the information
.’
So far, there’s nothing really new — but a simple idea is going to ensure that
PDL is highly expressive: we will make the inductive structure of the programs
explicit in PDL’s syntax. Complex programs are built out of basic programs using
some repertoire of program constructors. By using diamonds which reﬂect this
structure, we obtain a powerful and ﬂexible language.
Let us examine the core language of PDL. Suppose we have ﬁxed some set of
basic programs
, , , and so on (thus we have basic modalities
,
,
, . . .
at our disposal). Then we are allowed to deﬁne complex programs
(and hence,
modal operators
) over this base as follows:
(choice) if
and
are programs, then so is
.
The program
(non-deterministically) executes
or
.


---


1.2 Modal Languages
13
(composition) if
and
are programs, then so is
.
This program ﬁrst executes
and then
.
(iteration) if
is a program, then so is
.
is a program that executes
a ﬁnite (possibly zero) number of times.
For the collection of diamonds this means that if
and
are modal operators,
then so are
,
and
. This notation makes it straightforward to
describe properties of program execution. Here is a fairly straightforward example.
The formula
says that a state bearing the information
can
be reached by executing
a ﬁnite number of times if and only if either we already
have the information
in the current state, or we can execute
once and then ﬁnd
a state bearing the information
after ﬁnitely many more iterations of
. Here’s a
far more demanding example:
This is Segerberg’s axiom (or the induction axiom) and the reader should try work-
ing out what exactly it is that this formula says. We discuss this formula further in
Chapter 3, cf. Example 3.10.
If we conﬁne ourselves to these three constructors (and in this book for the most
part we do) we are working with a version of PDL called regular PDL. (This is
because the three constructors are the ones used in Kleene’s well-known analysis of
regular programs.) However, a wide range of other constructors have been studied.
Here are two:
(intersection) if
and
are programs, then so is
.
The intended meaning of
is: execute both
and
, in parallel.
(test)
if
is a formula, then
is a program.
This program tests whether
holds, and if so, continues; if not, it fails.
To ﬂesh this out a little, the intended reading of
is that if we execute
both
and
in the present state, then there is at least one state reachable by both
programs which bears the information
. This is a natural constructor for a variety
of purposes, and we will make use of it in Section 6.5.
The key point to note about the test constructor is its unusual syntax: it allows us
to make a modality out of a formula. Intuitively, this modality accesses the current
state if the current state satisﬁes
. On its own such a constructor is uninteresting
(
simply means
). However, when other constructors are present, it can
be used to build interesting programs. For example,
is ‘if
then
else .’
Nothing prevents us from viewing the basic programs as deterministic, and we
will discuss a fragment of deterministic PDL (DPDL) in Section 6.5


---


14
1 Basic Concepts
Example 1.16 (An Arrow Language) A similarity type with modal operators
other than diamonds, is the type
of arrow logic. The language of arrow logic
is designed to talk about the objects in arrow structures (entities which can be
pictured as arrows). The well-formed formulas
of the arrow language are given
by the rule
’
That is, ’ (‘identity’) is a nullary modality (a modal constant), the ‘converse’ oper-
ator
is a diamond, and the ‘composition’ operator
is a dyadic operator. Possible
readings of these operators are:
’
identity
‘skip’
converse
‘
conversely’
composition
‘ﬁrst
, then
’
Example 1.17 (Feature Logic and Description Logic) As we mentioned in the
Preface, researchers developing formalisms for describing graphs have sometimes
(without intending to) come up with notational variants of modal logic. For ex-
ample, computational linguists use Attribute-Value Matrices (AVMs) for describ-
ing feature structures (directed acyclic graphs that encode linguistic information).
Here’s a fairly typical AVM:
AGREEMENT
PERSON
1st
NUMBER
plural
CASE
dative
But this is just a two dimensional notation for the following modal formula
AGREEMENT
PERSON 1st
NUMBER plural
CASE dative
Similarly, researchers in AI needing a notation for describing and reasoning about
ontologies developed description logic. For example, the concept of ‘being a hired
killer for the mob’ is true of any individual who is a killer and is employed by a
gangster. In description logic we can deﬁne this concept as follows:
killer
employer gangster
But this is simply the following modal formula lightly disguised:
killer
employer gangster
It turns out that the links between modal logic on the one hand, and feature and
description logic on the other, are far more interesting than these rather simple ex-
amples might suggest. A modal perspective on feature or description logic capable


---


1.2 Modal Languages
15
of accounting for other important aspects of these systems (such as the ability to
talk about re-entrancy in feature structures, or to perform ABox reasoning in de-
scription logic) must make use of the kinds of extended modal logics discussed in
Chapter 7 (in particular, logics containing the global modality, and hybrid logics).
Furthermore, some versions of feature and description logic make use of ideas
from PDL, and description logic makes heavy use of counting modalities (which
say such things as ‘at most 3 transitions lead to a
state’).
Substitution
Throughout this book we’ll be working with the syntactic notion of one formula
being a substitution instance of another. In order to deﬁne this notion we ﬁrst
introduce the concept of a substitution as a function mapping proposition letters to
variables.
Deﬁnition 1.18 Suppose we’re working a modal similarity type
and a set
of
proposition letters. A substitution is a map
.
Now such a substitution
induces a map
which we can recursively deﬁne as follows:
This deﬁnition spells out exactly what is meant by carrying out uniform substitu-
tion. Finally, we say that
is a substitution instance of
if there is some substitu-
tion
such that
.
To give an example, if
is the substitution that maps
to
,
to
and leaves all other proposition letters untouched, then we have
Exercises for Section 1.2
1.2.1 Using
to mean ‘the agent knows that
’ and
to mean ‘it is consistent with
what the agent knows that
,’ represent the following statements.
(a) If
is true, then it is consistent with what the agent knows that she knows that
.
(b) If it is consistent with what the agent knows that
, and it is consistent with what
the agent knows that
, then it is consistent with what the agent knows that
.
(c) If the agent knows that
, then it is consistent with what the agent knows that
.


---


16
1 Basic Concepts
(d) If it is consistent with what the agent knows that it is consistent with what the agent
knows that
, then it is consistent with what the agent knows that
.
Which of these seem plausible principles concerning knowledge and consistency?
1.2.2 Suppose
is interpreted as ‘
is permissible’; how should
be understood?
List formulas which seem plausible under this interpretation. Should the L¨ob formula
be on your list? Why?
1.2.3 Explain how the program constructs ‘while
do
’ and ‘repeat
until
’
can be expressed in PDL.
1.2.4 Consider the following arrow formulas. Do you think they should be always true?
’
1.2.5 Show that ‘being-a-substitution-instance-of’ is a transitive concept. That is, show
that if
is a substitution instance of
, and
is a substitution instance of
, then
is a
substitution instance of
.
1.3 Models and Frames
Although our discussion has contained many semantically suggestive phrases such
as ‘true’ and ‘intended interpretation’, as yet we have given them no mathemat-
ical content. The purpose of this (key) section is to put that right. We do so by
interpreting our modal languages in relational structures. In fact, by the end of the
section we will have done this in two distinct ways: at the level of models and at
the level of frames. Both levels are important, though in different ways. The level
of models is important because this is where the fundamental notion of satisfaction
(or truth) is deﬁned. The level of frames is important because it supports the key
logical notion of validity.
Models and satisfaction
We start by deﬁning frames, models, and the satisfaction relation for the basic
modal language.
Deﬁnition 1.19 A frame for the basic modal language is a pair
such
that
(i)
is a non-empty set.
(ii)
is a binary relation on
.


---


1.3 Models and Frames
17
That is, a frame for the basic modal language is simply a relational structure bearing
a single binary relation. We remind the reader that we refer to the elements of
by many different names (see Deﬁnition 1.1).
A model for the basic modal language is a pair
, where
is a frame
for the basic modal language, and
is a function assigning to each proposition
letter
in
a subset
of
. Informally we think of
as the set of points
in our model where
is true. The function
is called a valuation. Given a model
, we say that
is based on the frame
, or that
is the frame
underlying
.
Note that models for the basic modal language can be viewed as relational struc-
tures in a natural way, namely as structures of the form:
That is, a model is a relational structure consisting of a domain, a single binary
relation
, and the unary relations given to us by
. Thus, viewed from a purely
structural perspective, a frame
and a model
based on
, are simply two re-
lational models based on the same universe; indeed, a model is simply a frame
enriched by a collection of unary relations.
But in spite of their mathematical kinship, frames and models are used very dif-
ferently. Frames are essentially mathematical pictures of ontologies that we ﬁnd
interesting. For example, we may view time as a collection of points ordered by
a strict partial order, or feel that a correct analysis of knowledge requires that we
postulate the existence of situations linked by a relation of ‘being an epistemic
alternative to.’ In short, we use the level of frames to make our fundamental as-
sumptions mathematically precise.
The unary relations provided by valuations, on the other hand, are there to dress
our frames with contingent information. Is it raining on Tuesday or not? Is the
system write-enabled at time
? Is a situation where Janet does not love him an
epistemic alternative for John? Such information is important, and we certainly
need to be able to work with it — nonetheless, statements only deserve the de-
scription ‘logical’ if they are invariant under changes of contingent information.
Because we have drawn a distinction between the fundamental information given
by frames, and the additional descriptive content provided by models, it will be
straightforward to deﬁne a modally reasonable notion of validity.
But this is jumping ahead. First we must learn how to interpret the basic modal
language in models. This we do by means of the following satisfaction deﬁnition.
Deﬁnition 1.20 Suppose
is a state in a model
. Then we induc-
tively deﬁne the notion of a formula
being satisﬁed (or true) in
at state
as


---


18
1 Basic Concepts
follows:
iff
where
never
iff
not
iff
or
iff
for some
with
we have
(1.4)
It follows from this deﬁnition that
if and only if for all
such
that
, we have
. Finally, we say that a set
of formulas is true at a
state
of a model
, notation:
, if all members of
are true at
.
Note that this notion of satisfaction is intrinsically internal and local. We evaluate
formulas inside models, at some particular state
(the current state). Moreover,
works locally: the ﬁnal clause (1.4) treats
as an instruction to scan states
in search of one where
is satisﬁed. Crucially, only states
-accessible from the
current one can be scanned by our operators. Much of the characteristic ﬂavor of
modal logic springs from the perspective on relational structures embodied in the
satisfaction deﬁnition.
If
does not satisfy
at
we often write
, and say that
is false or
refuted at
. When
is clear from the context, we write
for
and
for
. It is convenient to extend the valuation
from proposition
letters to arbitrary formulas so that
always denotes the set of states at which
is true:
Deﬁnition 1.21 A formula
is globally or universally true in a model
(nota-
tion:
) if it is satisﬁed at all points in
(that is, if
, for all
). A formula
is satisﬁable in a model
if there is some state in
at
which
is true; a formula is falsiﬁable or refutable in a model if its negation is
satisﬁable.
A set
of formulas is globally true (satisﬁable, respectively) in a model
if
for all states
in
(some state
in
, respectively).
Example 1.22 (i) Consider the frame
,
,
,
,
,
, where
iff
:
If we choose a valuation
on
such that
,
,
,
,
,
, and
, then in the model
we have that


---


1.3 Models and Frames
19
,
,
, and
.
Furthermore,
. Now, it is clear that
is true at
,
,
and
, but
why is it true at
? Well, as
has no successors at all (we often call such points
‘dead ends’ or ‘blind states’) it is vacuously true that
is true at all
-successors
of
. Indeed, any ‘boxed’ formula
is true at any dead end in any model.
(ii) As a second example, let
be the SPO given in Figure 1.1, where
,
, , , , ,
,
and
means ‘
and
are different, and
can be divided
by
.’ Choose a valuation
on this frame such that
, and
, and let
. Then
,
,
, and
(iii) Whereas a diamond
corresponds to making a single
-step in a model,
stacking diamonds one in front of the other corresponds to making a sequence
of
-steps through the model. The following deﬁned operators will sometimes
be useful: we write
for
preceded by
occurrences of
, and
for
preceded by
occurrences of
. If we like, we can associate each of these deﬁned
operators with its own accessibility relation. We do so inductively:
is deﬁned
to hold if
, and
is deﬁned to hold if
. Under this
deﬁnition, for any model
and state
in
we have
iff there exists
a
such that
and
.
(iv) The use of the word ‘world’ (or ‘possible world’) for the entities in
derives from the reading of the basic modal language in which
is taken to mean
‘possibly
,’ and
to mean ‘necessarily
.’ Given this reading, the machinery of
frames, models, and satisfaction which we have deﬁned is essentially an attempt to
capture mathematically the view (often attributed to Leibniz) that necessity means
truth in all possible worlds, and that possibility means truth in some possible world.
The satisfaction deﬁnition stipulates that
and
check for truth not at all possi-
ble worlds (that is, at all elements of
) but only at
-accessible possible worlds.
At ﬁrst sight this may seem a weakness of the satisfaction deﬁnition — but in fact,
it’s its greatest source of strength. The point is this: varying
is a mechanism
which gives us a ﬁrm mathematical grip on the pre-theoretical notion of access be-
tween possible worlds. For example, by stipulating that
we can allow
all worlds access to each other; this corresponds to the Leibnizian idea in its purest
form. Going to the other extreme, we might stipulate that no world has access to
any other. Between these extremes there is a wide range of options to explore.
Should interworld access be reﬂexive? Should it be transitive? What impact do
these choices have on the notions of necessity and possibility? For example, if we
demand symmetry, does this justify certain principles, or rule others out?
(v) Recall from Example 1.10 that in epistemic logic
is written as
and
is interpreted as ‘the agent knows that
.’ Under this interpretation, the intuitive
reading for the semantic clause governing
is: the agent knows
in a situation


---


20
1 Basic Concepts
(that is,
) iff
is true in all situations
that are compatible with her
knowledge (that is, if
for all
such that
). Thus, under this interpre-
tation,
is to be thought of as a collection of situations,
is a relation which
models the idea of one situation being epistemically accessible from another, and
governs the distribution of primitive information across situations.
We now deﬁne frames, models and satisfaction for modal languages of arbitrary
similarity type.
Deﬁnition 1.23 Let
be a modal similarity type. A -frame is a tuple
consisting
of the following ingredients:
(i) a non-empty set
,
(ii) for each
, and each
-ary modal operator
in the similarity type
,
an (
)-ary relation
.
So, again, frames are simply relational structures. If
contains just a ﬁnite number
of modal operators
, . . . ,
, we write
, . . . ,
; otherwise we
write
or
. We turn such a frame into a
model in exactly the same way we did for the basic modal language: by adding a
valuation. That is, a
-model is a pair
where
is a
-frame, and
is
a valuation with domain
and range
, where
is the universe of
.
The notion of a formula
being satisﬁed (or true) at a state
in a model
(notation:
) is deﬁned inductively. The clauses
for the atomic and Boolean cases are the same as for the basic modal language (see
Deﬁnition 1.20). As for the modal case, when
we deﬁne
iff
for some
, . . . ,
with
we have, for each ,
This is an obvious generalization of the way
is handled in the basic modal lan-
guage. Before going any further, the reader should formulate the satisfaction clause
for
.
On the other hand, when
(that is, when
is a nullary modality) then
is a unary relation and we deﬁne
iff
That is, unlike other modalities, nullary modalities do not access other states. In
fact, their semantics is identical to that of the propositional variables, save that the
unary relations used to interpret them are not given by the valuation — rather, they
are part of the underlying frame.
As before, we often write
for
where
is clear from the
context. The concept of global truth (or universal truth) in a model is deﬁned


---


1.3 Models and Frames
21
as for the basic modal language: it simply means truth at all states in the model.
And, as before, we sometimes extend the valuation
supplied by
to arbitrary
formulas.
Example 1.24 (i) Let
be a similarity type with three unary operators
,
,
and
. Then a
-frame has three binary relations
,
, and
(that is, it is a
labeled transition system with three labels). To give an example, let
,
,
and
be as in Figure 1.2, and consider the formula
. Informally,
this formula is true at a state, if it has an
-successor satisfying
only if it has
an
-successor satisfying
. Let
be a valuation with
. Then the
model
has
.
(ii) Let
be a similarity type with a binary modal operator
and a ternary
operator
. Frames for this
contain a ternary relation
and a 4-ary rela-
tion
. As an example, let
,
, and
as in Figure 1.6, and consider a valuation
on this frame with
,
and
. Now, let
be the formula
:
:
Fig. 1.6. A simple frame
. An informal reading of
is ‘any triangle of which the
evaluation point is a vertex, and which has
and
true at the other two vertices,
can be expanded to a rectangle with a fourth point at which
is true.’ The reader
should be able to verify that
is true at
, and indeed at all other points, and hence
that it is globally true in the model.
Example 1.25 (Bidirectional Frames and Models) Recall from Example 1.14
that the basic temporal language has two unary operators
and
. Thus, according
to Deﬁnition 1.23, models for this language consist of a set bearing two binary re-
lations,
(the into-the-future relation) and
(the into-the-past relation), which
are used to interpret
and
respectively. However, given the intended reading
of the operators, most such models are inappropriate: clearly we ought to insist on
working with models based on frames in which
is the converse of
(that is,
frames in which
).
Let us denote the converse of a relation
by
. We will call a frame of the


---


22
1 Basic Concepts
form
a bidirectional frame, and a model built over such a frame a bidi-
rectional model. From now on, we will only interpret the basic temporal language
in bidirectional models. That is, if
is a bidirectional model
then:
iff
iff
But of course, once we’ve made this restriction, we don’t need to mention
ex-
plicitly any more: once
has been ﬁxed, its converse is ﬁxed too. That is, we are
free to interpret the basic temporal languages on frames
for the basic modal
language using the clauses
iff
iff
These clauses clearly capture a crucial part of the intended semantics:
looks
forward along
, and
looks backwards along
. Of course, our models will
only start looking genuinely temporal when we insist that
has further properties
(notably transitivity, to capture the ﬂow of time), but at least we have pinned down
the fundamental interaction between the two modalities.
Example 1.26 (Regular Frames and Models) As explained in Example 1.15, the
language of PDL has an inﬁnite collection of diamonds, each indexed by a program
built from basic programs using the constructors
, , and . Now, according to
Deﬁnition 1.23, a model for this language has the form
is a program
That is, a model is a labeled transition system together with a valuation. However,
given our reading of the PDL operators, most of these models are uninteresting. As
with the basic temporal language, we must insist on working with a class of models
that does justice to our intentions.
Now, there is no problem with the interpretation of the basic programs: any
binary relation can be regarded as a transition relation for a non-deterministic pro-
gram. Of course, if we were particularly interested in deterministic programs we
would insist that each basic program be interpreted by a partial function, but let us
ignore this possibility and turn to the key question: which relations should interpret
the structured modalities? Given our readings of
, and , as choice, composition,
and iteration, it is clear that we are only interested in relations constructed using
the following inductive clauses:
the reﬂexive transitive closure of


---


1.3 Models and Frames
23
These inductive clauses completely determine how each modality should be inter-
preted. Once the interpretation of the basic programs has been ﬁxed, the relation
corresponding to each complex program is ﬁxed too. This leads to the following
deﬁnition.
Suppose we have ﬁxed a set of basic programs. Let
be the smallest set of
programs containing the basic programs and all programs constructed over them
using the regular constructors
,
and . Then a regular frame for
is a labeled
transition system
such that
is an arbitrary binary relation
for each basic program , and for all complex programs
,
is the binary relation
inductively constructed in accordance with the previous clauses. A regular model
for
is a model built over a regular frame; that is, a regular model is regular
frame together with a valuation. When working with the language of PDL over the
programs in
, we will only be interested in regular models for
, for these are
the models that capture the intended interpretation.
What about the
and
constructors? Clearly the intended reading of
demands
that
. As for ?, it is clear that we want the following deﬁnition:
and
This is indeed the clause we want, but note that it is rather different from the others:
it is not a frame condition. Rather, in order to determine the relation
, we need
information about the truth of the formula
, and this can only be provided at the
level of models.
Example 1.27 (Arrow Models) Arrow frames were deﬁned in Example 1.8 and
the arrow language in Example 1.16. Given these deﬁnitions, it is clear how the
language of arrow logic should be interpreted. First, an arrow model is a structure
such that
is an arrow frame and
is a valuation.
Then:
’
iff
iff
for some
with
iff
and
for some
and
with
When
is a square frame
(as deﬁned in Example 1.8), this works out as
follows.
now maps propositional variables to sets of pairs over
; that is, to
binary relations. The truth deﬁnition can be rephrased as follows:
’
iff
iff
iff
and
for some
Such situations can be represented pictorially in two ways. First, one could draw


---


24
1 Basic Concepts
the graph-like structures as given in Example 1.8. Alternatively, one could draw
a square model two-dimensionally, as in the picture below. It will be obvious that
the modal constant ’ holds precisely at the diagonal points and that
is true at a
point iff
holds at its mirror image with respect to the diagonal. The formula
holds at a point
iff we can draw a rectangle
such that:
lies on the vertical
line through
,
lies on the vertical line through
; and
lies on the diagonal.
’
Frames and validity
It is time to deﬁne one of the key concepts in modal logic. So far we have been
viewing modal languages as tools for talking about models. But models are com-
posite entities consisting of a frame (our underlying ontology) and contingent in-
formation (the valuation). We often want to ignore the effects of the valuation and
get a grip on the more fundamental level of frames. The concept of validity lets
us do this. A formula is valid on a frame if it is true at every state in every model
that can be built over the frame. In effect, this concept interprets modal formulas
on frames by abstracting away from the effects of particular valuations.
Deﬁnition 1.28 A formula
is valid at a state
in a frame
(notation:
)
if
is true at
in every model
based on
;
is valid in a frame
(notation:
) if it is valid at every state in
. A formula
is valid on a class of frames
(notation:
) if it is valid on every frame
in
; and it is valid (notation:
) if it is valid on the class of all frames. The set of all formulas that are valid in
a class of frames
is called the logic of
(notation:
).
Our deﬁnition of the logic of a frame class
(as the set of ‘all’ formulas that
are valid on
) is underspeciﬁed: we did not say which collection of proposition
letters
should be used to build formulas. But usually the precise form of this
collection is irrelevant for our purposes. On the few occasions in this book where
more precision is required, we will explicitly deal with the issue. (If the reader is


---


1.3 Models and Frames
25
worried about this, he or she may just ﬁx a countable set
of proposition letters
and deﬁne
to be
.)
As will become abundantly clear in the course of the book, validity differs from
truth in many ways. Here’s a simple example. When a formula
is true at a
point
, this means that that either
or
is true at
(the satisfaction deﬁnition
tells us so). On the other hand, if
is valid on a frame
, this does not mean
that either
or
is valid on
(
is a simple counterexample).
Example 1.29 (i) The formula
is valid on all frames. To
see this, take any frame
and state
in
, and let
be a valuation on
. We have
to show that if
, then
. So assume that
. Then, by deﬁnition there is a state
such that
and
. But, if
then either
or
. Hence either
or
. Either way,
.
(ii) The formula
is not valid on all frames. To see this we need to
ﬁnd a frame
, a state
in
, and a valuation on
that falsiﬁes the formula at
.
So let
be a three-point frame with universe
and relation
.
Let
be any valuation on
such that
. Then
, but
since 0 is not related to 2.
(iii) But there is a class of frames on which
is valid: the class
of transitive frames. To see this, take any transitive frame
and state
in
,
and let
be a valuation on
. We have to show that if
, then
. So assume that
. Then by deﬁnition there are
states
and
such that
and
and
. But as
is transitive, it
follows that
, hence
.
(iv) As the previous example suggests, when additional constraints are imposed
on frames, more formulas may become valid. For example, consider the frame
depicted in Figure 1.2. On this frame the formula
is not valid; a coun-
termodel is obtained by putting
. Now, consider a frame satisfying
the condition
; an example is depicted in Figure 1.7.
Fig. 1.7. A frame satisfying
.
On this frame it is impossible to refute the formula
at
, because a
refutation would require the existence of a point
with
and
true at
, but
not
; but such points are forbidden when we insist that
.
This is a completely general point: in every frame
of the appropriate similarity
type, if
satisﬁes the condition
, then
is valid in
. More-


---


26
1 Basic Concepts
over, the converse to this statement also holds: whenever
is valid on
a given frame
, then the frame must satisfy the condition
. To use the
terminology we will introduce in Chapter 3, the formula
deﬁnes the
property that
.
(v) When interpreting the basic temporal language (see Example 1.25) we ob-
served that arbitrary frames of the form
were uninteresting given the
intended interpretation of
and
, and we insisted on interpreting them using a
relation
and its converse. Interestingly, there is a sense in which the basic tempo-
ral language itself is strong enough to enforce the condition that the relation
is
the converse of the relation
: such frames are precisely the ones which validate
both the formulas
and
; see Exercise 3.1.1.
(vi) The formula
is not valid on all frames. To see this we need
to ﬁnd a frame
, a state
in
, and a valuation on
that falsiﬁes
this formula at . So let
, and let
be the relation
. Let
be a valuation such that
. Then
, but obviously
.
(vii) But there is a frame on which
is valid. As the universe of the
frame take the set of all rational numbers
, and let the frame relation be the usual
-ordering on
. To show that
is valid on this frame, take any point
in it, and any valuation
such that
; we have to show that
. But this is easy: as
, there exists a
such that
and
.
Because we are working on the rationals, there must be an
with
and
(for example,
). As
, it follows that
.
(viii) The special conditions demanded of PDL models also give rise to validities.
For example,
is valid on any frame such that
, and in fact the converse is also true. The reader is asked to prove this
in Exercise 3.1.2.
(ix) In our last example we consider arrow logic. We claim that in any square
arrow frame
, the formula
is valid. For, let
be a
valuation on
, and suppose that for some pair of points
in
, we have
. It follows that
, and hence,
there must be a
for which
and
.
But then we have
and
. This in turn
implies that
.
Exercises for Section 1.3
1.3.1 Show that when evaluating a formula
in a model, the only relevant information in
the valuation is the assignments it makes to the propositional letters actually occurring in
. More precisely, let
be a frame, and
and
be two valuations on
such that
for all proposition letters
in
. Show that
iff
. Work in the
basic modal language. Do this exercise by induction on the number of connectives in
(or


---


1.4 General Frames
27
as we usually put it, by induction on
). (If you are unsure how to do this, glance ahead to
Proposition 2.3 where such a proof is given in detail.)
1.3.2 Let
and
be the following frames for a modal
similarity type with two diamonds
and
. Here
is the set of natural numbers,
is
the set of strings of s and s, and the relations are deﬁned by
iff
iff
iff
or
iff
is a proper initial segment of
Which of the following formulas are valid on
and
, respectively?
(a)
,
(b)
,
(c)
,
(d)
,
(e)
,
(f)
,
(g)
.
1.3.3 Consider the basic temporal language and the frames
,
and
(the integer, rational, and real numbers, respectively, all ordered by the usual less-than
relation
). In this exercise we use E
to abbreviate
, and A
to abbreviate
. Which of the following formulas are valid on these frames?
(a)
,
(b)
,
(c)
E
E
A
A
E
.
1.3.4 Show that every formula that has the form of a propositional tautology is valid.
Further, show that
is valid.
1.3.5 Show that each of the following formulas is not valid by constructing a frame
that refutes it.
(a)
,
(b)
,
(c)
,
(d)
.
Find, for each of these formulas, a non-empty class of frames on which it is valid.
1.3.6 Show that the arrow formulas
and ’
are valid in
any square.
1.4 General Frames
At the level of models the fundamental concept is satisfaction. This is a relatively
simple concept involving only a frame and a single valuation. By ascending to the


---


28
1 Basic Concepts
level of frames we get a deeper grip on relational structures — but there is a price to
pay. Validity lacks the concrete character of satisfaction, for it is deﬁned in terms of
all valuations on a frame. However there is an intermediate level: a general frame
is a frame
together with a restricted, but suitably well-behaved collection
of admissible valuations.
General frames are useful for at least two reasons. First, there may be appli-
cation driven motivations to exclude certain valuations. For instance, if we were
using
to model the temporal distribution of outputs from a computational
device, it would be unreasonable to let valuations assign non recursively enumer-
able sets to propositional variables. But perhaps the most important reason to work
with general frames is that they support a notion of validity that is mathematically
simpler than the frame-based one, without losing too many of the concrete prop-
erties that make models so easy to work with. This ‘simpler behavior’ will only
really become apparent when we discuss the algebraic perspective on complete-
ness theory in Chapter 5. It will turn out that there is a fundamental and universal
completeness result for general frame validity, something that the frame semantics
lacks. Moreover, we will discover that general frames are essentially a set-theoretic
representation of boolean algebras with operators. Thus, the
in
stands
not only for Admissible, but also for Algebra.
So what is a ‘suitably well-behaved collection of valuations’? It simply means a
collection of valuations closed under the set-theoretic operations corresponding to
our connectives and modal operators. Now, fairly obviously, the boolean connec-
tives correspond to the boolean operations of union, relative complement, and so
on — but what operations on sets do modalities correspond to? Here is the answer.
Let us ﬁrst consider the basic modal similarity type with one diamond. Given a
frame
, let
be the following operation on the power set of
:
for some
Think of
as the set of states that ‘see’ a state in
. This operation corre-
sponds to the diamond in the sense that for any valuation
and any formula
:
Moving to the general case, we obtain the following deﬁnition.
Deﬁnition 1.30 Let
be a modal similarity type, and
a -frame.
For
we deﬁne the following function
on the power set of
:
there are
, . . . ,
such that
and
for all
.
Example 1.31 Let
be the converse operator of arrow logic, and consider a


---


1.4 General Frames
29
square frame
. Note that
is the following operation:
for some
But by the rather special nature of
this boils down to
and
for some
In other words,
is nothing but the converse of the binary relation
.
Deﬁnition 1.32 (General Frames) Let
be a modal similarity type. A general
-
frame is a pair
where
is a
-frame, and
is a non-empty
collection of subsets of
closed under the following operations:
(i) union: if
,
then
.
(ii) relative complement: if
, then
.
(iii) modal operations: if
, . . . ,
, then
for all
.
A model based on a general frame is a triple
where
is a general
frame and
is a valuation satisfying the constraint that for each proposition letter
,
is an element of
. Valuations satisfying this constraint are called admis-
sible for
.
It follows immediately from the ﬁrst two clauses of the deﬁnition that both the
empty set and the universe of a general frame are always admissible. Note that
an ordinary frame
can be regarded as a general frame where
(that is, a general frame in which all valuations are admissible). Also,
note that if a valuation
is admissible for a general frame
, then the closure
conditions listed in Deﬁnition 1.32 guarantee that
, for all formulas
. In short, a set of admissible valuations
is a ‘logically closed’ collection of
information assignments.
Deﬁnition 1.33 A formula
is valid at a state
in a general frame
(no-
tation:
) if
is true at
in every admissible model
on
; and
is valid in a general frame
(notation:
) if
is true
at every state in every admissible model
on
.
A formula
is valid on a class of general frames
(notation:
) if it is
valid on every general frame
in
. Finally, if
is valid on the class of all
general frames we say that it is g-valid and write
. We will learn in Chapter 4
(see Exercise 4.1.1) that a formula
is valid if and only if it is g-valid.


---
