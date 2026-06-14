<!-- Source: Blackburn, de Rijke & Venema (2001). Modal Logic. Cambridge University Press. Chapter 2: Models (pages 50-123). BibKey: Blackburn2001 -->


2
Models
In Section 1.3 we deﬁned what it means for a formula to be satisﬁed at a state in
a model — but as yet we know virtually nothing about this fundamental semantic
notion. What exactly can we say about models when we use modal languages
to describe them? Which properties of models can modal languages express, and
which lie beyond their reach?
In this chapter we examine such questions in detail.
We introduce disjoint
unions, generated submodels, bounded morphisms, and ultraﬁlter extensions, the
‘big four’ operations on models that leave modal satisfaction unaffected. We dis-
cuss two ways to obtain ﬁnite models and show that modal languages have the ﬁnite
model property. Moreover, we deﬁne the standard translation of modal logic into
ﬁrst-order logic, thus opening the door to correspondence theory, the systematic
study of the relationship between modal and classical logic. All this material plays
a fundamental role in later work; indeed, the basic track sections in this chapter are
among the most important in the book.
But the central concept of the chapter is that of a bisimulation between two
models. Bisimulations reﬂect, in a particularly simple and direct way, the locality
of the modal satisfaction deﬁnition. We introduce them early on, and they gradually
come to dominate our discussion. By the end of the chapter we will have a good
understanding of modal expressivity over models, and the most interesting results
all hinge on bisimulations.
Chapter guide
Section 2.1: Invariance Results (Basic track). We introduce three classic ways of
constructing new models from old ones that do not affect modal satisfac-
tion: disjoint unions, generated submodels, and bounded morphisms. We
also meet isomorphisms and embeddings.
Section 2.2: Bisimulations (Basic track). We introduce bisimulations and show
that modal satisfaction is invariant under bisimulation. We will see that
50



2.1 Invariance Results
51
the model constructions introduced in the ﬁrst section are all special cases
of bisimulation, learn that modal equivalence does not always imply bisim-
ilarity, and examine an important special case in which it does.
Section 2.3: Finite Models (Basic track). Here we show that modal languages en-
joy the ﬁnite model property. We do so in two distinct ways: by the se-
lection method (ﬁnitely approximating a bisimulation), and by ﬁltration
(collapsing a model into a ﬁnite number of equivalence classes).
Section 2.4: The Standard Translation (Basic track). We start our study of cor-
respondence theory. By deﬁning the standard translation, we link modal
languages to ﬁrst-order (and other classical) languages and raise the two
central questions that dominate later sections: What part of ﬁrst-order logic
does modal logic correspond to? And which properties of models are de-
ﬁnable by modal means?
Section 2.5: Modal Saturation via Ultraﬁlter Extensions (Basic track). The ﬁrst
step towards obtaining some answers is to introduce ultraﬁlter extensions,
the last of the big four modal model constructions. We then show that al-
though modal equivalence does not imply bisimilarity, it does imply bisim-
ilarity somewhere else, namely in the ultraﬁlter extensions of the models
concerned.
Section 2.6: Characterization and Deﬁnability (Advanced track).
We prove the
two main results of this chapter. First, we prove van Benthem’s theorem
stating that modal languages are the bisimulation invariant fragments of
ﬁrst-order languages. Second, we show that modally deﬁnable classes of
(pointed) models are those that are closed under bisimulations and ultra-
products and whose complements are closed under ultrapowers.
Section 2.7: Simulations and Safety (Advanced track). We prove two results that
give the reader a glimpse of recent work in modal model theory. The ﬁrst
describes the properties that are preserved under simulations (a one-way
version of bisimulation), the second characterizes the ﬁrst-order deﬁnable
operations on binary relations which respect bisimilarity.
2.1 Invariance Results
Mathematicians rarely study structures in isolation. They are usually interested in
the relations between different structures, and in operations that build new struc-
tures from old. Questions that naturally arise in such a context concern the struc-
tural properties that are invariant under or preserved by such relations and opera-
tions. We’ll not give precise deﬁnitions of these notions, but roughly speaking, a
property is preserved by a certain relation or operation if, whenever two structures
are linked by the relation or operation, then the second structure has the property



52
2 Models
if the ﬁrst one has it. We speak of invariance if the property is preserved in both
directions.
When it comes to this research topic, logic is no exception to the rule — indeed,
logicians add a descriptive twist to it. For instance, modal logicians want to know
when two structures, or perhaps two points in distinct structures, are indistinguish-
able by modal languages in the sense of satisfying the same modal formulas.
Deﬁnition 2.1 Let
M and
M
0 be models of the same modal similarity type
, and
let
w and
w
0 be states in
M and
M
0 respectively. The
-theory (or
-type) of
w is
the set of all
-formulas satisﬁed at
w: that is,
f
j
M;
w

g. We say that
w and
w
0 are (modally) equivalent (notation:
w
!
w
0) if they have the same
-theories.
The
-theory of the model
M is the set of all
-formulas satisﬁed by all states
in
M: that is,
f
j
M

g. Models
M and
M
0 are called (modally) equivalent
(notation:
M
!
M
0) if their theories are identical.
a
We now introduce three important ways of constructing new models from old ones
which leave the theories associated with states unchanged: disjoint unions, gen-
erated submodels, and bounded morphisms. These constructions (together with
ultraﬁlter extensions, which we introduce in Section 2.5) play an important role
throughout the book. For example, in the following chapter we will see that they
lift to the level of frames (where they preserve validity), we will use them repeat-
edly in our work on completeness and complexity, and in Chapter 5 we will see
that they have important algebraic analogs.
Disjoint Unions
Suppose we have the following two models:
'
&
$
%
t
w

	


'
&
$
%
t
v
3
t
v
2
t
v
1
t
v
0
-
-
-
M
N
Don’t worry that we haven’t speciﬁed the valuations — they’re irrelevant here. All
that matters is that
M and
N have disjoint domains, for we are now going to lump
them together to form the model
M
]
N:
t
w

	


t
v
3
t
v
2
t
v
1
t
v
0
-
-
-
M
]
N
'
&
$
%
The model
M
]
N is called the disjoint union of
M and
N. It gathers together
all the information in the two smaller models unchanged: we have not altered the
way the points are related, nor the way atomic information is distributed. Suppose



2.1 Invariance Results
53
we’re working in the basic modal language, and suppose that a formula
 is true at
(say)
v
1 in
N: is
 still true at
v
1 in
M
]
N? More generally, is modal satisfaction
preserved from points in the original models to the points in the disjoint union?
And what about the reverse direction: if a modal formula is true at some state in
M
]
N, is it also true at that same state in the smaller model it came from?
The answer to these questions is clearly yes: modal satisfaction must be invariant
(that is, preserved in both directions) under the formation of disjoint unions. Modal
satisfaction is intrinsically local: only the points accessible from the current state
are relevant to truth or falsity. If we evaluate a formula
 at (say)
w, it is completely
irrelevant whether we perform the evaluation in
M or
M
]
N;
 simply cannot
detect the presence or absence of states in other islands.
Deﬁnition 2.2 (Disjoint Unions)
We ﬁrst deﬁne disjoint unions for the basic
modal language. We say that two models are disjoint if their domains contain
no common elements. For disjoint models
M
i
=
(W
i,
R
i,
V
i
) (i
2
I), their
disjoint union is the structure
U
i
M
i
=
(W
;
R
;
V
), where
W is the union of
the sets
W
i,
R is the union of the relations
R
i, and for each proposition letter
p,
V
(p)
=
S
i2I
V
i
(p).
Now for the general case. For disjoint
-structures
M
i
=
(W
i
;
R
Mi
;
V
i
)
M2
(i
2
I) of the same modal similarity type
, their disjoint union is the structure
U
i
M
i
=
(W
;
R
M
;
V
)
M2 such that
W is the union of the sets
W
i; for each
M
2
,
R
M is the union
S
i2I
R
Mi; and
V is deﬁned as in the basic modal case.
If we want to put together a collection of models that are not disjoint, we ﬁrst
have to make them disjoint (say by indexing the domains of these models). To use
the terminology introduced shortly, we simply take mutually disjoint isomorphic
copies of the models we wish to combine, and combine the copies instead.
a
Proposition 2.3 Let
 be a modal similarity type and, for all
i
2
I, let
M
i be a
-model. Then, for each modal formula
, for each
i
2
I, and each element
w
of
M
i, we have
M
i
;
w

 iff
U
i2I
M
i
;
w

. In words: modal satisfaction is
invariant under disjoint unions.
Proof. We will prove the result for the basic similarity type. The proof is by in-
duction on
 (we explained this concept in Exercise 1.3.1). Let
i be some index;
we will prove, for each basic modal formula
, and each element
w of
M
i, that
M
i
;
w

 iff
M;
w

, where
M is the disjoint union
U
i2I
M
i.
First suppose that
 contains no connectives. Now, if
 is a proposition letter
p, then we have
M
i
;
w

 iff
w
2
V
i
(p) iff (by deﬁnition of
V )
w
2
V
(p)
iff
M;
w

. On the other hand,
 could be
? (for the purposes of inductive
proofs it is convenient to regard
? as a propositional letter rather than as a logical
connective). But trivially
? is false at
w in both models, so we have the desired
equivalence here too.



54
2 Models
Our inductive hypothesis is that the desired equivalence holds for all formulas
containing at most
n connectives (where
n

0). We must now show that the
equivalence holds for all formulas
 containing
n
+
1 connectives. Now, if
 is of
the form
: or
 
_
 this is easily done — we will leave this to the reader — so
as we are working with the basic similarity type, it only remains to establish the
equivalence for formulas of the form
3 . So assume that
M
i
;
w

3 . Then
there is a state
v in
M
i with
R
i
w
v and
M
i
;
v

 . By the inductive hypothesis,
M;
v

 . But by deﬁnition of
M, we have
R
w
v, so
M;
w

3 .
For the other direction, assume that
M;
w

3 holds for some
w in
M
i. Then
there is a
v with
R
w
v and
M;
v

v. It follows by the deﬁnition of
R that
R
j
w
v for
some
j, and by the disjointness of the universes we must have that
j
=
i. But then
we ﬁnd that
v belongs to
M
i as well, so we may apply the inductive hypothesis;
this yields
M
i
;
v

 , so we ﬁnd that
M
i
;
w

3 .
a
We will use Proposition 2.3 all through the book — here is a simple application
which hints at the ideas we will explore in Chapter 7.
Example 2.4 Deﬁned modalities are a convenient shorthand for concepts we ﬁnd
useful. We have already seen some examples. In this book
2, the ‘true at all ac-
cessible states modality’, is shorthand for
:3:, and we have inductively deﬁned
a ‘true somewhere
n-steps from here’ modality
3
n for each natural number
n (see
Example 1.22). But while it is usually easy to show that some modality is deﬁnable
(we need simply write down its deﬁnition), how do we show that some proposed
operator is not deﬁnable? Via invariance results! As an example, consider the
global modality. The global diamond E has as its (intended) accessibility relation
the relation
W

W implicitly present in any model. That is:
M;
w
 E iff
M;
v

 for some state
v in
M
:
Its dual, A, the global box, thus has the following interpretation:
M;
w
 A iff
M;
v

 for all states
v in
M:
Thus the global modality brings a genuinely global dimension to modal logic. But
is it deﬁnable in the basic modal language? Intuitively, no: as
3 and
2 work
locally, it seems unlikely that they can deﬁne a truly global modality over arbitrary
structures. Fine — but how do we prove this?
With the help of the previous proposition. Suppose we could deﬁne A. Then
we could write down an expression
(p) containing only symbols from the basic
modal language such that for every model
M,
M;
w

(p) iff
M

p. We
now derive a contradiction from this supposition. Consider a model
M
1 where
p holds everywhere, and a model
M
2 where
p holds nowhere. Let
w be some
point in
M
1. It follows that
M
1
;
w

(p), so as (by assumption)
(p) contains



2.1 Invariance Results
55
only symbols from the basic modal language, by Proposition 2.3 we have that
M
1
]
M
2
;
w

(p). But this implies that
M
1
]
M
2
;
v

p for every
v in
M
2,
which, again by Proposition 2.3, in turn implies that
M
2

p: contradiction. We
conclude that the global box (and hence the global diamond) is not deﬁnable in the
basic modal language.
So, if we want the global modality, then we either have to introduce it as a
primitive (we will do this in Section 7.1), or we have to work with restricted classes
of models on which it is deﬁnable (in Exercise 1.3.3 we worked with a class of
models in which we could deﬁne A in the basic temporal language).
a
Generated submodels
Disjoint unions are a useful way of making bigger models from smaller ones — but
we also want methods for doing the reverse. That is, we would like to know when it
is safe to throw points away from a satisfying model without affecting satisﬁability.
Disjoint unions tell us a little about this (if a model is a disjoint union of smaller
models, we are free to work with the component models), but this is not useful in
practice. We need something sharper, namely generated submodels.
Suppose we are using the basic modal language to talk about a model
M based
on the frame
(Z;
<), the integers with their usual order. It does not matter what the
valuation is — all that’s important is that
M looks something like this:




...
t
 3
t
 2
t
 1
t
0
t
1
t
2
t
3
...
-
-
-
-
-
-
-
-
First suppose that we form a submodel
M
  of
M by throwing away all the positive
numbers, and restricting the original valuation (whatever it was) to the remaining
numbers. So
M
  looks something like this:




...
t
 3
t
 2
t
 1
t
0
-
-
-
-
The basic modal language certainly can see that
M and
M
  are different. For
example, it sees that 0 has successors in
M (note that
M;
0

3>) but is a dead
end in
M
  (note that
M
 ;
0
6
3>). So there’s no invariance result for arbitrary
submodels. But now consider the submodel
M
+ of
M that is formed by omitting
the negative numbers, and restricting the original valuation to the numbers that
remain:




t
0
t
1
t
2
t
3
...
-
-
-
-



56
2 Models
Suppose a basic modal formula
 is satisﬁed at some point
n in
M. Is
 also
satisﬁed at the same point
n in
M
+? The answer must be yes. The only points that
are relevant to
’s satisﬁability are the points greater than
n — and all such points
belong to
M
+. Similarly, it is clear that if
M
+ satisﬁes a basic modal formula
 at
m, then
M must too.
In short, it seems plausible that modal invariance holds for submodels which
are closed under the accessibility relation of the original model. Such models are
called generated submodels, and they do indeed give rise to the invariance result
we are looking for.
Deﬁnition 2.5 (Generated Submodels) We ﬁrst deﬁne generated submodels for
the basic modal language. Let
M
=
(W
;
R
;
V
) and
M
0
=
(W
0
;
R
0
;
V
0
) be two
models; we say that
M
0 is a submodel of
M if
W
0

W,
R
0 is the restriction of
R
to
W
0 (that is:
R
0
=
R
\
(W
0

W
0
)), and
V
0 is the restriction of
V to
M
0 (that is:
for each
p,
V
0
(p)
=
V
(p)
\
W
0). We say that
M
0 is a generated submodel of
M
(notation:
M
0

M) if
M
0 is a submodel of
M and for all points
w the following
closure condition holds:
if
w is in
M
0 and
R
w
v, then
v is in
M
0.
For the general case, we say that a model
M
0
=
(W
0
;
R
0
M
;
V
0
)
M2 is a generated
submodel of the model
M
=
(W
;
R
M
;
V
)
M2 (notation:
M
0

M) whenever
M
0
is a submodel of
M (with respect to
R
M for all
M
2
), and the following closure
condition is fulﬁlled for all
M
2

if
u
2
W
0 and
R
M
uu
1
:
:
:
u
n, then
u
1
;
:
:
:
;
u
n
2
W
0.
Let
M be a model, and
X a subset of the domain of
M; the submodel generated
by
X is the smallest generated submodel of
M whose domain contains
X (such a
model always exists: why?). Finally, a rooted or point generated model is a model
that is generated by a singleton set, the element of which is called the root of the
frame.
a
Proposition 2.6 Let
 be a modal similarity type and let
M and
M
0 be
-models
such that
M
0 is a generated submodel of
M. Then, for each modal formula
 and
each element
w of
M
0 we have that
M;
w

 iff
M
0
;
w

. In words: modal
satisfaction is invariant under generated submodels.
Proof. By induction on
. The reader unused to such proofs should write out the
proof in full. In Proposition 2.19 we provide an alternative proof based on the
observation that generated submodels induce a bisimulation.
a
Four remarks. First, note that the invariance result for disjoint unions (Proposi-
tion 2.3) is a special case of the result for generated submodels: any component of



2.1 Invariance Results
57
a disjoint union is a generated submodel of the disjoint union. Second, using an
argument analogous to that used in Example 2.4 to show that the global box can’t
be deﬁned in the basic modal language, we can use Proposition 2.6 to show that we
cannot deﬁne a backward looking modality in terms of
3; see Exercise 2.1.2. Thus
if we want such a modality we have to add it as a primitive — which is exactly what
we did, of course, when deﬁning the basic temporal language. Third, although we
have not explicitly discussed generated submodels for the basic temporal language,
PDL, or arrow logic, the required concepts are all special cases of Deﬁnition 2.5,
and thus the respective invariance results are special cases of Proposition 2.6. But
it is worth making a brief comment about the basic temporal language. When we
think explicitly in terms of bidirectional frames (see Example 1.25) it is obvious
that we are interested in submodels closed under both
R
F and
R
P. But when work-
ing with the basic temporal language we usually leave
R
P implicit: we work with
ordinary models
(W
;
R
;
V
), and use
R
, the converse of
R, as
R
P . Thus a tem-
poral generated submodel of
(W
;
R
;
V
) is a submodel
(W
0
;
R
0
;
V
0
) that is closed
under both
R and
R
. Finally, generated submodels are heavily used throughout
the book: given a model
M that satisﬁes a formula
 at a state
w, very often the
ﬁrst thing we will do is form the submodel of
M generated by
w, thus trimming
what may be a very unwieldy satisfying model down to a more manageable one.
Morphisms for modalities
In mathematics the idea of morphisms or structure preserving maps is of funda-
mental importance. What notions of morphism are appropriate for modal logic?
That is, what kinds of morphism give rise to invariance results? We will approach
the answer bit by bit, introducing a number of important concepts on the way. We
will start by considering the general notion of homomorphism (this is too weak to
yield invariance, but it is the starting point for better attempts), then we will deﬁne
strong homomorphisms, embeddings, and isomorphisms (these do give us invari-
ance, but are not particularly modal), and ﬁnally we will zero in on the answer:
bounded morphisms.
Deﬁnition 2.7 (Homomorphisms) Let
 be a modal similarity type and let
M and
M
0 be
-models. By a homomorphism
f from
M to
M
0 (notation:
f
:
M
!
M
0)
we mean a function
f from
W to
W
0 with the following properties.
(i) For each proposition letter
p and each element
w from
M, if
w
2
V
(p),
then
f
(w
)
2
V
0
(p).
(ii) For each
n
>
0 and each
n-ary
M
2
, and
(n
+
1)-tuple
w from
M, if
(w
0, . . . ,
w
n
)
2
R
M then
(f
(w
0
), . . . ,
f
(w
n
))
2
R
0
M (the homomorphic
condition).



58
2 Models
We call
M the source and
M
0 the target of the homomorphism.
a
Note that for the basic modal language, item (ii) is just this:
if
R
w
u then
R
0
f
(w
)f
(u).
Thus item (ii) simply says that homomorphisms preserve relational links.
Are modal formulas invariant under homomorphisms? No: although homomor-
phisms reﬂect the structure of the source in the structure of the target, they do
not reﬂect the structure of the target back in the source. It is easy to turn this
observation into a counterexample, and we will leave this task to the reader as
Exercise 2.1.3.
So let us try and strengthen the deﬁnition. There is an obvious way of doing
so: turn the conditionals into equivalences. This leads to a number of important
concepts.
Deﬁnition 2.8 (Strong Homomorphisms, Embeddings and Isomorphisms) Let
 be a modal similarity type and let
M and
M
0 be
-models. By a strong homo-
morphism of
M into
M
0 we mean a homomorphism
f
:
M
!
M
0 which satisﬁes
the following stronger version of the above items (i) and (ii):
(i) For each proposition letter
p and element
w from
M,
w
2
V
(p) iff
f
(w
)
2
V
0
(p).
(ii) For each
n

0 and each
n-ary
M in
 and
(n
+
1)-tuple
w from
M,
(w
0,
. . . ,
w
n
)
2
R
M iff
(f
(w
0
), . . . ,
f
(w
n
))
2
R
0
M (the strong homomorphic
condition).
An embedding of
M into
M
0 is a strong homomorphism
f
:
M
!
M
0 which is
injective. An isomorphism is a bijective strong homomorphism. We say that
M
is isomorphic to
M
0, in symbols
M

=
M
0, if there is an isomorphism from
M to
M
0.
a
Note that for the basic modal language, item (ii) is just:
R
w
u iff
R
0
f
(w
)f
(u).
That is, item (ii) says that relational links are preserved from the source model to
the target and back again. So it is not particularly surprising that we have a number
of invariance results.
Proposition 2.9 Let
 be a modal similarity type and let
M and
M
0 be
-models.
Then the following holds:
(i) For all elements
w and
w
0 of
M and
M
0, respectively, if there exists a
surjective strong homomorphism
f
:
M
!
M
0 with
f
(w
)
=
w
0, then
w
and
w
0 are modally equivalent.



2.1 Invariance Results
59
(ii) If
M

=
M
0, then
M
!
M
0.
Proof. The ﬁrst item follows by induction on
; the second one is an immediate
consequence.
a
None of the above results is particularly modal. For a start, as in all branches of
mathematics, ‘isomorphic’ basically means ‘mathematically identical’. Thus, we
do not want to be able to distinguish isomorphic structures in modal (or indeed,
any other) logic. Quite the contrary: we want to be free to work with structures
‘up to isomorphism’ — as we did, for example, in our discussion of disjoint union,
when we talked of taking isomorphic copies. Item (ii) tells us that we can do this,
but it isn’t a surprising result.
But why is item (i), the invariance result for strong homomorphisms, not ‘gen-
uinely modal’? Quite simply, because there are many morphisms which do give
rise to invariance, but which fail to qualify as strong homomorphisms. To ensure
modal invariance we need to ensure that some target structure is reﬂected back in
the source, but strong morphisms do this in a much too heavy-handed way. The
crucial concept is more subtle.
Deﬁnition 2.10 (Bounded Morphisms — the Basic Case) We ﬁrst deﬁne bound-
ed morphisms for the basic modal language. Let
M and
M
0 be models for the
basic modal language. A mapping
f
:
M
=
(W
;
R
;
V
)
!
M
0
=
(W
0
;
R
0
;
V
0
) is a
bounded morphism if it satisﬁes the following conditions:
(i)
w and
f
(w
) satisfy the same proposition letters.
(ii)
f is a homomorphism with respect to the relation
R (that is, if
R
w
v then
R
0
f
(w
)f
(v
)).
(iii) If
R
0
f
(w
)v
0 then there exists
v such that
R
w
v and
f
(v
)
=
v
0 (the back
condition).
If there is a surjective bounded morphism from
M to
M
0, then we say that
M
0 is a
bounded morphic image of
M, and write
M

M
0.
a
The idea embodied in the back condition is utterly fundamental to modal logic —
in fact, it is the idea that underlies the notion of bisimulation — so we need to get
a good grasp of what it involves right away. Here’s a useful example.
Example 2.11 Consider the models
M
=
(W,
R,
V
) and
M
0
=
(W
0,
R
0,
V
0
),
where

W
=
N (the natural numbers),
R
mn iff
n
=
m
+
1, and
V
(p)
=
fn
2
N
j
n is even
g

W
0
=
fe;
og,
R
0
=
f(e;
o);
(o;
e)g, and
V
0
(p)
=
feg.



60
2 Models




t
0
t
1
t
2
t
3
t
4
t
5
...
-
-
-
-
-
-




t
-
t

e
o
?
?
...
Fig. 2.1. A bounded morphism
Now, let
f
:
W
!
W
0 be the following map:
f
(n)
=

e
if
n is even
o
if
n is odd
Figure 2.1 sums this all up in a simple picture.
Now,
f is not a strong homomorphism (why not?), but it is a (surjective) bounded
morphism from
M to
M
0. Let’s see why. Trivially
f satisﬁes item (i) of the deﬁ-
nition. As for the homomorphic condition consider an arbitrary pair
(n;
n
+
1) in
R. There are two possibilities:
n is either even or odd. Suppose
n is even. Then
n
+
1 is odd, so
f
(n)
=
e and
f
(n
+
1)
=
o. But then we have
R
0
f
(n)f
(n
+
1),
as required. The argument for
n odd is analogous.
And now for the interesting part: the back condition. Take an arbitrary element
n of
W and assume that
R
0
f
(n)w
0. We have to ﬁnd an
m
2
W such that
R
nm
and
f
(m)
=
w
0. Let’s assume that
n is odd (the case for even
n is similar). As
n is odd,
f
(n)
=
o, so by deﬁnition of
R
0, we must have that
w
0
=
e. But then
f
(n
+
1)
=
w
0 since
n
+
1 is even, and by the deﬁnition of
R we have that
n
+
1
is a successor of
n. Hence,
n
+
1 is the
m that we were looking for.
a
Deﬁnition 2.12 (Bounded Morphisms — the General Case) The deﬁnition of
a bounded morphism for general modal languages is obtained from the above by
adapting the homomorphic and back conditions of Deﬁnition 2.10 as follows:
(ii)
0 For all
M
2
,
R
M
w
v
1
:
:
:
v
n implies
R
0
M
f
(w
)f
(v
1
)
:
:
:
f
(v
n
).
(iii)
0 If
R
0
M
f
(w
)v
0
1
:
:
:
v
0
n then there exist
v
1
:
:
:
v
n such that
R
M
w
v
1
:
:
:
v
n and
f
(v
i
)
=
v
0
i (for
1

i

n).
a
Example 2.13 Suppose we are working in the modal similarity type of arrow
logic; see Example 1.16 and 1.27. Recall that the language has a modal constant
1’, a unary operator

 and a single dyadic operator
Æ. Semantically, to these oper-
ators correspond a unary relation
I, a binary
R and a ternary
C. We will deﬁne a



2.1 Invariance Results
61
bounded morphism from a square model to a model based on the addition of the
integer numbers. We will use the following notation: if
x is an element of
Z

Z,
then
x
0 denotes its ﬁrst component, and
x
1 its second component.
Consider the two models
M
=
(W
;
C
;
R
;
I
;
V
) and
M
0
=
(W
0
;
C
0
;
R
0
;
I
0
;
V
0
)
where

W
=
Z

Z,
C
xy
z iff
x
0
=
y
0,
y
1
=
z
0 and
z
1
=
x
1,
R
xy if
x
0
=
y
1
and
x
1
=
y
0,
I
x iff
x
0
=
x
1, and ﬁnally, the valuation
V is given by
V
(p)
=
f(x
0
;
x
1
)
j
x
1
 x
0 is even
g,

W
0
=
Z,
C
0
stu iff
s
=
t
+
u,
R
0
st iff
s
=
 t,
I
0
s iff
s
=
0, and the valuation
V
0 is given by
V
0
(p)
=
fs
2
Z
j
s is even
g.
This example is best understood by looking at Figure 2.2. The left picture shows a
fragment of the model
M; the points of
Z

Z are represented as disks or circles,
depending on whether
p is true or not. The diagonal is indicated by the dashed
diagonal line. The picture on the right-hand side shows the image under
f of the
points in
Z

Z.
            a
a
a
a
q
q
q
q
q
a
a
a
a
a
a
q
q
q
q
q
a
a
a
a
a
a
q
q
q
q
q
a
a
a
a
...
...
1
    
    	
2
     
     	
0
     
     	
-1
     
     	
-2
    
    	
...
...
Fig. 2.2. Another bounded morphism.
We claim that the function
f
:
Z

Z
!
Z given by
f
(z
)
=
z
1
 z
0
is a bounded morphism for this similarity type. The clause for the propositional
variables is trivial. For the unary relation
I we only have to check that for any
z in
Z

Z,
z
0
=
z
1 iff
z
1
 z
0
=
0. This is obviously true. We leave the case of the
binary relation
R to the reader.
So let’s turn to the clauses for the ternary relation
C. To check item (ii)
0 (the
homomorphic condition), assume that
C
xy
z holds for
x,
y and
z in
W. That is,
we have that
x
0
=
y
0,
y
1
=
z
0 and
z
1
=
x
1. But then we ﬁnd that
f
(x)
=
x
1
 x
0
=
z
1
 y
0
=
z
1
 z
0
+
y
1
 y
0
=
f
(z
)
+
f
(y
);



62
2 Models
so by deﬁnition of
C
0 we do indeed ﬁnd that
C
0
f
(x)f
(y
)f
(z
).
For item (iii)
0 (the back condition) assume that we have
C
0
f
(x)tu for some
x
2
Z

Z and
t;
u
2
Z. In other words, we have that
x
1
 x
0
=
t
+
u. Consider
the pairs
y
:=
(x
0
;
x
0
+
t) and
z
:=
(x
0
+
t;
x
1
). It is obvious that
C
xy
z; we also
ﬁnd that
f
(y
)
=
t and
f
(z
)
=
x
1
 (x
0
+
t)
=
(x
1
 x
0
)
 t
=
u. Hence
y and
z
are the elements of
W that we need to satisfy item (iii)
0.
a
Deﬁnition 2.12 covers the basic temporal language, PDL, and arrow logic, as spe-
cial cases — but once more it is worth issuing a warning concerning the basic
temporal language. Although
R
P is usually presented implicitly (as the converse
of the relation
R in some model
(W
;
R
;
V
)) we certainly cannot ignore it. Thus
a temporal bounded morphism from
(W
1
;
R
1
;
V
1
) to
(W
2
;
R
2
;
V
2
) is a bounded
morphism from
(W
1
;
R
1
;
R

1
;
V
1
) to
(W
2
;
R
2
;
R

2
;
V
2
).
Proposition 2.14 Let
 be a modal similarity type and let
M and
M
0 be
-models
such that
f
:
M
!
M
0. Then, for each modal formula
, and each element
w of
M we have
M;
w

 iff
M
0
;
f
(w
)

. In words: modal satisfaction is invariant
under bounded morphisms.
Proof. Let
M,
M
0 and
f be as in the statement of the proposition. We will prove
that for each formula
 and state
w,
M;
w

 iff
M
0
;
f
(w
)

. The proof is
by induction on
. We will assume that
 is the basic similarity type, leaving the
general case to the reader.
The base step and the boolean cases are routine, so let’s turn to the case where
 is of the form
3 . Assume ﬁrst that
M;
w

3 . This means there is a state
v with
R
w
v and
M;
v

 . By the inductive hypothesis,
M
0
;
f
(v
)

 . By the
homomorphic condition,
R
0
f
(w
)f
(v
), so
M
0
;
f
(w
)

3 .
For the other direction, assume that
M
0
;
f
(w
)

3 . Thus there is a successor
of
f
(w
) in
M
0, say
v
0, such that
M
0
;
v
0

 . Now we use the back condition
(of Deﬁnition 2.10). This yields a point
v in
M such that
R
w
v and
f
(v
)
=
v
0.
Applying the inductive hypothesis, we obtain
M;
v

 , so
M;
w

3 .
a
Here is a simple application: we will now show that any satisﬁable formula can be
satisﬁed in a tree-like model. To put it another way: modal logic has the tree model
property.
Let
 be a modal similarity type containing only diamonds (thus if
M is a
-model, it has the form
(W
;
R
1
;
R
2
;
:
:
:
;
V
), where each
R
i is a binary rela-
tion on
W). In this context we will call a
-model
M tree-like if the structure
(W
;
S
i
R
i
;
V
) is a tree in the sense of Example 1.5.
Proposition 2.15 Assume that
 is a modal similarity type containing only dia-
monds. Then, for any rooted
-model
M there exists a tree-like
-model
M
0 such
that
M
0

M. Hence any satisﬁable
-formula is satisﬁable in a tree-like model.



2.1 Invariance Results
63
Proof. Let
w be the root of
M. Deﬁne the model
M
0 as follows. Its domain
W
0
consists of all ﬁnite sequences
(w,
u
1, . . . ,
u
n
) such that
n

0 and for some modal
operators
ha
1
i, . . . ,
ha
n
i
2
 there is a path
w
R
a
1
u
1



R
a
n
u
n in
M. Deﬁne
(w
;
u
1
;
:
:
:
;
u
n
)R
0
a
(w
;
v
1
;
:
:
:
;
v
m
) to hold if
m
=
n
+
1,
u
i
=
v
i for
i
=
1;
:
:
:
;
n,
and
R
a
u
n
v
m holds in
M. That is,
R
0
a relates two sequences iff the second is an
extension of the ﬁrst with a state from
M that is a successor of the last element
of the ﬁrst sequence. Finally,
V
0 is deﬁned by putting
(w
;
u
1
;
:
:
:
;
u
n
)
2
V
0
(p)
iff
u
n
2
V
(p). As the reader is asked to check in Exercise 2.1.4, the mapping
f
:
(w
;
u
1
:
:
:
;
u
n
)
7!
u
n deﬁnes a surjective bounded morphism from
M
0 to
M,
thus
M
0 and
M are equivalent.
But then it follows that any satisﬁable
-formula is satisﬁable in a tree-like
model. For suppose
 is satisﬁable in some
-model at a point
w. Let
M be
the submodel generated by
w. By Proposition 2.3,
M;
w

, and as
M is rooted
we can form an equivalent tree-like model
M
0 as just described.
a
The method used to construct
M
0 from
M is well known in both modal logic
and computer science: it is called unravelling (or unwinding, or unfolding). In
essence, we built
M
0 by treating the paths through
M as ﬁrst class citizens: this
untangles the (possibly very complex) way information is stored in
M, and makes
it possible to present it as a tree. We will make use of unravelling several times in
later work; in the meantime, Exercise 2.1.7 asks the reader to extend the notion of
‘tree-likeness’ to arbitrary modal similarity types, and generalize Proposition 2.15.
Exercises for Section 2.1
2.1.1 Suppose we wanted an operator D with the following satisfaction deﬁnition: for any
model
M and any formula
,
M;
w
 D iff there is a
u
6=
w such that
M;
u

. This
operator is called the difference operator and we will discuss it further in Section 7.1. Is
the difference operator deﬁnable in the basic modal language?
2.1.2 Use generated submodels to show that the backward looking modality (that is, the
P
of the basic temporal language) cannot be deﬁned in terms of the forward looking operator
3.
2.1.3 Give the simplest possible example which shows that the truth of modal formulas is
not invariant under homomorphisms, even if condition 1 is strengthened to an equivalence.
Is modal truth preserved under homomorphisms?
2.1.4 Show that the mapping
f deﬁned in the proof of Proposition 2.15 is indeed a surjec-
tive bounded morphism.
2.1.5 Let
B
=
(B
;
R
) be the transitive binary tree; that is,
B is the set of ﬁnite strings
of
0s and
1s, and
R

 holds if
 is a proper initial segment of
. Let
N
=
(N
;
<) be the
frame of the natural numbers with the usual ordering.



64
2 Models
(a) Let
V
0 be the valuation on
N given by
V
0
(p)
=
f2n
j
n
2
N
g for each proposition
letter
p. Deﬁne a valuation
U
0 on
B and a bounded morphism from
(B;
U
0
) to
(N;
V
0
).
(b) Let
U
1 be the valuation on
B given by
U
1
(p)
=
f1
j

2
B
g for each proposition
letter
p. Give a valuation
V
1 on
N and a bounded morphism from
(B;
U
0
) to
(N;
V
0
).
(c) Can you also ﬁnd surjective bounded morphisms?
2.1.6 Show that every model is the bounded morphic image of the disjoint union of point-
generated (that is: rooted) models. This exercise may look rather technical, but in fact it is
very straightforward — think about it!
2.1.7 This exercise generalizes Proposition 2.15 to arbitrary modal similarity types.
(a) Deﬁne a suitable notion of tree-like model that works for arbitrary modal similarity
types. (Hint: in case of
R
M
s
0
s
1
:
:
:
s
n, think of
s
0 as being the parent node and of
s
1
;
:
:
:
;
s
n as the children.)
(b) Generalize Proposition 2.15 to arbitrary modal similarity types.
2.2 Bisimulations
What do the invariance results of the previous section have in common? They all
deal with special sorts of relations between two models, namely relations with the
following properties: related states carry identical atomic information, and when-
ever it is possible to make a transition in one model, it is possible to make a match-
ing transition in the other. For example, with generated submodels the inter-model
relation is identity, and every transition in one model is matched by an identical
transition in the other. With bounded morphisms, the inter-model relation is a func-
tion, and the notion of matching involves both the homomorphic link from source
to target, and the back condition which reﬂects target structure in the source.
This observation leads us to the central concept of the chapter: bisimulations.
Quite simply, a bisimulation is a relation between two models in which related
states have identical atomic information and matching transition possibilities. The
interesting part of the deﬁnition is the way it makes the notion of ‘matching transi-
tion possibilities’ precise.
Deﬁnition 2.16 (Bisimulations — the Basic Case) We ﬁrst give the deﬁnition
for the basic modal language. Let
M
=
(W
;
R
;
V
) and
M
0
=
(W
0
;
R
0
;
V
0
) be two
models.
A non-empty binary relation
Z

W

W
0 is called a bisimulation between
M
and
M
0 (notation:
Z
:
M
$
M
0) if the following conditions are satisﬁed.
(i) If
w
Z
w
0 then
w and
w
0 satisfy the same proposition letters.
(ii) If
w
Z
w
0 and
R
w
v, then there exists
v
0 (in
M
0) such that
v
Z
v
0 and
R
0
w
0
v
0
(the forth condition).



2.2 Bisimulations
65
(iii) The converse of (ii): if
w
Z
w
0 and
R
0
w
0
v
0, then there exists
v (in
M) such
that
v
Z
v
0 and
R
w
v (the back condition).
When
Z is a bisimulation linking two states
w in
M and
w
0 in
M
0 we say that
w
and
w
0 are bisimilar, and we write
Z
:
M;
w
$
M
0
;
w
0. If there is a bisimulation
Z such that
Z
:
M;
w
$
M
0
;
w
0, we sometimes write
M;
w
$
M
0
;
w
0; likewise,
if there is some bisimulation between
M and
M
0, we write
M
$
M
0.
a
Think of Deﬁnition 2.16 pictorially. Figure 2.3 shows the content of the forth
clause. Suppose we know that
w
Z
w
0 and
R
w
v (the solid arrow in
M and the
Z-
link at the bottom of the diagram display this information). Then the forth condition
says that it is always possible to ﬁnd a
v
0 that ‘completes the square’ (this is shown
by the dashed arrow in
M
0 and the dotted
Z-link at the top of the diagram). Note
the symmetry between the back and forth clauses: to visualize the back clause,
simply reﬂect the picture through its vertical axis.
M
q
w
q
v
6
M
0
q
w
0
q
v
0
6
Z
Z
Fig. 2.3. The forth condition.
In effect, bisimulations are a relational generalization of bounded morphisms: we
drop the directionality from source to target (and with it the homomorphic con-
dition) and replace it with a back and forth system of matching moves between
models.
Example 2.17 The models
M and
M
0 shown in Figure 2.4 are bisimilar. To see
this, deﬁne the following relation
Z between their states:
Z
=
f(1;
a),
(2;
b),
(2;
c),
(3;
d),
(4;
e),
(5;
e)g. Condition (i) of Deﬁnition 2.16 is obviously satisﬁed:
Z-related states make the same propositional letters true. Moreover, the back-and-
forth conditions are satisﬁed too: any move in
M can be matched by a similar move
in
M
0, and conversely, as the reader should check.
This example also shows that bisimulation is a genuine generalization of the
constructions discussed in the previous section. Although
M and
M
0 are bisimilar,
neither is a generated submodel nor a bounded morphic image of the other.
a



66
2 Models
M
'
&
$
%
s
1
p
-
s
2
q
-
s
3
p
  
@
@
R
s
4
q
s
5
q
M
0
'
&
$
%
s
a
p
  
@
@
R
s
b
q
@
@
R
s
c
q
  
s
d
p
-
s
e
q
Fig. 2.4. Bisimilar models.
Deﬁnition 2.18 (Bisimulations — the General Case) Let
 be a modal similarity
type, and let
M
=
(W
;
R
M
;
V
)
M2 and
M
0
=
(W
0
;
R
0
M
;
V
0
)
M2 be
-models. A
non-empty binary relation
Z

W

W
0 is called a bisimulation between
M and
M
0 (notation:
Z
:
M
$
M
0) if the above condition (i) from Deﬁnition 2.16
is satisﬁed (that is,
Z-related states satisfy the same proposition letters) and in
addition the following conditions (ii)
0 and (iii)
0 are satisﬁed:
(ii)
0 If
w
Z
w
0 and
R
M
w
v
1
:
:
:
v
n then there are
v
0
1, . . . ,
v
0
n (in
W
0) such that
R
0
M
w
0
v
0
1
:
:
:
v
0
n and for all
i (1

i

n)
v
i
Z
v
0
i (the forth condition).
(iii)
0 The converse of (ii)
0: if
w
Z
w
0 and
R
M
w
0
v
0
1
:
:
:
v
0
n then there are
v
1, . . . ,
v
n
(in
W) such that
R
M
w
v
1
:
:
:
v
n and for all
i (1

i

n)
v
i
Z
v
0
i (the back
condition).
a
Examples of bisimulations abound — indeed, as we have already mentioned, the
constructions of the previous section (disjoint unions, generated submodels, iso-
morphisms, and bounded morphisms), are all bisimulations:
Proposition 2.19 Let
 be a modal similarity type, and let
M,
M
0 and
M
i (i
2
I)
be
-models.
(i) If
M

=
M
0, then
M
$
M
0.
(ii) For every
i
2
I and every
w in
M
i,
M
i
;
w
$
U
i
M
i
;
w.
(iii) If
M
0

M, then
M
0
;
w
$
M;
w for all
w in
M
0.
(iv) If
f
:
M

M
0, then
M;
w
$
M
0
;
f
(w
) for all
w in
M.
Proof. We only prove the second item, leaving the others as Exercise 2.2.2. As-
sume we are working in the basic modal language. Deﬁne a relation
Z between
M
i and
U
i
M
i by putting
Z
=
f(w
;
w
)
j
w
2
M
i
g. Then
Z is a bisimulation.
To see this, observe that clause (i) of Deﬁnition 2.16 is trivially fulﬁlled, and as to
clauses (ii) and (iii), any
R-step in
M
i is reproduced in
U
i
M
i, and by the disjoint-
ness condition every
R-step in
U
i
M
i that departs from a point that was originally
in
M
i, stems from a corresponding
R-step in
M
i. The reader should extend this
argument to arbitrary similarity types.
a



2.2 Bisimulations
67
We will now show that modal satisﬁability is invariant under bisimulations (and
hence, by Proposition 2.19, provide an alternative proof that modal satisﬁability is
invariant under disjoint unions, generated submodels, isomorphisms, and bounded
morphisms). The key thing to note about the following proof is how straight-
forward it is — the back and forth clauses in the deﬁnition of bisimulation are
precisely what is needed to push the induction through.
Theorem 2.20 Let
 be a modal similarity type, and let
M,
M
0 be
-models. Then,
for every
w
2
W and
w
0
2
W
0,
w
$
w
0 implies that
w
!
w
0. In words, modal
formulas are invariant under bisimulation.
Proof. By induction on
. The case where
 is a proposition letter follows from
clause (i) of Deﬁnition 2.16, and the case where
 is
? is immediate. The boolean
cases are immediate from the induction hypothesis.
As for formulas of the form
3 , we have
M;
w

3 iff there exists a
v in
M
such that
R
w
v and
M;
v

 . As
w
$
w
0 we ﬁnd by clause (ii) of Deﬁnition
2.16 that there exists a
v
0 in
M
0 such that
R
0
w
0
v
0 and
v
$
v
0. By the induction
hypothesis,
M
0
;
v
0

 , hence
M
0
;
w
0

3 . For the converse direction use
clause (iii) of Deﬁnition 2.16.
The argument for the general modal case, with triangles
M, is an easy extension
of that just given, as the reader should check.
a
This ﬁnishes our discussion of the basics of bisimulation — so let’s now try and
understand the concept more deeply. Some of the remarks that follow are concep-
tual, and some are technical, but they all point to ideas that crop up throughout the
book.
Remark 2.21 (Bisimulation, Locality, and Computation) In the Preface we sug-
gested that the reader think of modal formulas as automata. Evaluating a modal
formula amounts to running an automaton: we place it at some state inside a struc-
ture and let it search for information. The automaton is only permitted to explore
by making transitions to neighboring states; that is, it works locally.
Suppose such an automaton is standing at a state
w in a model
M, and we pick
it up and place it at a state
w
0 in a different model
M
0; would it notice the switch?
If
w and
w
0 are bisimilar, no. Our automaton cares only about the information
at the current state and the information accessible by making a transition — it is
indifferent to everything else. Thus the deﬁnition of bisimulation spells out exactly
what we have to do if we want to fool such an automaton as to where it is being
evaluated. Viewed this way, it is clear that the concept of bisimulation is a direct
reﬂection of the locality of the modal satisfaction deﬁnition.
But there is a deeper link between bisimulation and computation than our infor-
mal talk of automaton might suggest. As we discussed in Example 1.3, labelled



68
2 Models
N
w
0
M
w
s

 	
 	









...
s

 	
 	









...
Z
Z
~
Z
Z
~
Z
Z
~
Z
Z
~ .. ...
Fig. 2.5. Equivalent but not bisimilar.
transition systems (LTSs) are a standard way of thinking about computation: when
we traverse an LTS we build a sequence of state transitions — or to put it another
way, we compute. When are two LTSs computationally equivalent? More pre-
cisely, if we ignore practical issues (such as how long it takes to actually perform
a computation) when can two different LTSs be treated as freely exchangeable
(‘observationally equivalent’) black boxes? One natural answer is: when they are
bisimilar. Bisimulation turns out to be a very natural notion of equivalence for both
mathematical and computational investigations. For more on the history of bisim-
ulation and the connection with computer science, see the Notes.
a
Remark 2.22 (Bisimulation and First-Order Logic) According to Theorem 2.20
modal formulas cannot distinguish between bisimilar states or between bisimilar
models, even though these states or models may be quite different. It follows
that modal logic is very different from ﬁrst-order logic, for arbitrary ﬁrst-order
formulas are certainly not invariant under bisimulations. For example, the model
M
0 of Example 2.17 satisﬁes the formula
9y
1
y
2
y
3
(y
1
6=
y
2
^
y
1
6=
y
3
^
y
2
6=
y
3
^
R
xy
1
^
R
xy
2
^
R
y
1
y
3
^
R
y
2
y
3
);
if we assign the state
a to the free variable
x. This formula says that there is a
diamond-shaped conﬁguration of points, which is true of the point
a in
M
0, but
not of the state
1 in
M. But as far as modal logic is concerned,
M
0 and
M, being
bisimilar, are indistinguishable. In Section 2.4 we will start examining the links
between modal logic and ﬁrst-order logic more systematically.
a
Now for a fundamental question: is the converse of Theorem 2.20 true? That is, if
two models are modally equivalent, must they be bisimilar? The answer is no.
Example 2.23 Consider the basic modal language. We may just as well work with
an empty set of proposition letters here. Deﬁne models
M and
N as in Figure 2.5,
where arrows denote
R-transitions. Each of
M and
N has, for each
n
>
0, a ﬁnite
branch of length
n; the difference between the models is that, in addition,
N has an
inﬁnite branch.



2.2 Bisimulations
69
One can show that for all modal formulas
,
M;
w

 iff
N;
w
0

 (this is
easy if one is allowed to use some results that we will prove further on, namely
Propositions 2.31 and 2.33, but it is not particularly hard to prove from ﬁrst prin-
ciples, and the reader may like to try this). But even though
w and
w
0 are modally
equivalent, there is no bisimulation linking them. To see this, suppose that there
was such a bisimulation
Z: we will derive a contradiction from this supposition.
Since
w and
w
0 are linked by
Z, there has to be a successor of
w, say
v
0, which
is linked to the ﬁrst point
v
0
0 on the inﬁnite path from
w
0. Suppose that
n is the
length of the (maximal) path leading from
w through
v
0, and let
w,
v
0, . . . ,
v
n 1
be the successive points on this path. Using the bisimulation conditions
n
 1
times, we ﬁnd points
v
0
1, . . . ,
v
0
n 1 on the inﬁnite path emanating from
w
0, such
that
v
0
0
R
0
v
0
1
:
:
:
R
0
v
0
n 1 and
v
i
Z
v
0
i for each
i. Now
v
0
n 1 has a successor, but
v
n 1
does not; hence, there is no way that these two points can be bisimilar.
a
Nonetheless, it is possible to prove a restricted converse to Theorem 2.20, namely
the Hennessy-Milner Theorem. Let
 be a modal similarity type, and
M a
-
model.
M is image-ﬁnite if for each state
u in
M and each relation
R in
M, the
set
f
(v
1
;
:
:
:
;
v
n
)
j
R
uv
1
:
:
:
v
n
g is ﬁnite; observe that we are not putting any
restrictions on the total number of different relations
R in the model
M — just that
each of them is image-ﬁnite.
Theorem 2.24 (Hennessy-Milner Theorem) Let
 be a modal similarity type,
and let
M and
M
0 be two image-ﬁnite
-models. Then, for every
w
2
W and
w
0
2
W
0,
w
$
w
0 iff
w
!
w
0.
Proof. Assume that our similarity type
 only contains a single diamond (that is,
we will work in the basic modal language). The direction from left to right follows
from Theorem 2.20; for the other direction, we will prove that the relation
! of
modal equivalence itself satisﬁes the conditions of Deﬁnition 2.16 — that is, we
show that the relation of modal equivalence on these models is itself a bisimulation.
(This is an important idea; we will return to it in Section 2.5.)
The ﬁrst condition is immediate. For the second one, assume that
w
!
w
0
and
R
w
v. We will try to arrive at a contradiction by assuming that there is no
v
0
in
M
0 with
R
0
w
0
v
0 and
v
!
v
0. Let
S
0
=
fu
0
j
R
0
w
0
u
0
g. Note that
S
0 must
be non-empty, for otherwise
M
0
;
w
0

?, which would contradict
w
!
w
0
since
M;
w

3>. Furthermore, as
M
0 is image-ﬁnite,
S
0 must be ﬁnite, say
S
0
=
fw
0
1
;
:
:
:
;
w
0
n
g. By assumption, for every
w
0
i
2
S
0 there exists a formula
 
i
such that
M;
v

 
i but
M
0
;
w
0
i
6
 
i. It follows that
M;
w

3( 
1
^



^
 
n
) and
M
0
;
w
0
6
3( 
1
^



^
 
n
);
which contradicts our assumption that
w
!
w
0. The third condition of Deﬁni-



70
2 Models
tion 2.16 may be checked in a similar way. Extending the proof to other similarity
types is routine.
a
Theorem 2.20 (together with the Hennessy-Milner Theorem) on the one hand, and
Example 2.23 on the other, mark important boundaries. Clearly, bisimulations have
something important to say about modal expressivity over models, but they don’t
tell us everything. Two pieces of the jigsaw puzzle are missing. For a start, we are
still considering modal languages in isolation: as yet, we have made no attempt to
systematically link them to ﬁrst-order logic. We will remedy this in Section 2.4 and
this will eventually lead us to a beautiful result, the Van Benthem Characterization
Theorem (Theorem 2.68): modal logic is the bisimulation invariant fragment of
ﬁrst-order logic.
The second missing piece is the notion of an ultraﬁlter extension. We will intro-
duce this concept in Section 2.5, and this will eventually lead us to Theorem 2.62.
Informally, this theorem says: modal equivalence implies bisimilarity-somewhere-
else. Where is this mysterious ‘somewhere else’? In the ultraﬁlter extension. As
we will see, although modally equivalent models need not be bisimilar, they must
have bisimilar ultraﬁlter extensions.
Remark 2.25 (Bisimulations for the Basic Temporal Language, PDL, and Ar-
row Logic) Although we have already said the most fundamental things that need
to be said on this topic (Deﬁnition 2.18 and Theorem 2.20 covers these languages),
a closer look reveals some interesting results for PDL and arrow logic. But let us
ﬁrst discuss the basic temporal language.
First we issue our (by now customary) warning. When working with the basic
temporal language, we usually work with models
(W
;
R
;
V
) and implicitly take
R
P
to be
R
. Thus we need a notion of bisimulation which takes
R
 into account, and
so we deﬁne a temporal bisimulation between models
(W
;
R
;
V
) and
(W
0
;
R
0
;
V
0
)
to be a relation
Z between the states of the two models that satisﬁes the clauses
of Deﬁnition 2.16, and in addition the following two clauses (iv) and (v) requiring
that backward steps in one model should be matched by similar steps in the other
model:
(iv) If
w
Z
w
0 and
R
v
w, then there exists
v
0 (in
M
0) such that
v
Z
v
0 and
R
0
v
0
w
0.
(v) The converse of (iv): if
w
Z
w
0 and
R
0
v
0
w
0, then there exists
v (in
M) such
that
v
Z
v
0 and
R
v
w.
If we don’t do this, we are in trouble. For example, if
M is a model whose underly-
ing frame is the integers, and
M
0 is the submodel of
M generated by
0, then these
two models are bisimilar in the sense of Deﬁnition 2.16, and hence equivalent as
far as the basic modal language is concerned. But they are not equivalent as far as
the basic temporal language is concerned:
M;
0

P
>, but
M;
0
6
P
>.



2.2 Bisimulations
71
Given our previous discussion, this is unsurprising. What is (pleasantly) sur-
prising is that things do not work this way in PDL. Suppose we are given two
regular models. Checking that these models are bisimilar for the language of PDL
means checking that bisimilarity holds for all the (inﬁnitely many) relations that
exist in regular models (see Deﬁnition 1.26). But as it turns out, most of this work
is unnecessary. Once we have checked that bisimilarity holds for all the relations
which interpret the basic programs, we don’t have to check anything else: the
relations corresponding to complex programs will automatically be bisimilar. In
Section 2.7 we will introduce some special terminology to describe this: the oper-
ations in regular PDL’s modality building repertoire ([, ;, and
) will be called safe
for bisimulation. Note that taking the converse of a relation is not an operation that
is safe for bisimulation (in effect, that’s what we just noted when discussing the
basic temporal language); see Exercise 2.2.6.
What about arrow logic? The required notion of bisimulation is given by Def-
inition 2.18; note that the clause for
1’ reads that for bisimilar points
a and
a
0 we
have
I
a iff
I
0
a.
a
Remark 2.26 (The Algebra of Bisimulations) Bisimulations give rise to alge-
braic structure quite naturally. For instance, if
Z
0 is a bisimulation between
M
0
and
M
1, and
Z
1 a bisimulation between
M
1 and
M
2, then the composition of
Z
0
and
Z
1 is a bisimulation linking
M
0 and
M
2. It is also a rather easy observation
that the set of bisimulations between two models is closed under taking arbitrary
(ﬁnite or inﬁnite) unions. This shows that if two points are bisimilar, there is al-
ways a maximal bisimulation linking them; see Exercise 2.2.8. Further information
on closure properties of the set of bisimulations between two models can be found
in Section 2.7.
a
Exercises for Section 2.2
2.2.1 Consider a modal similarity type with two diamonds
hai and
hbi, and with

=
fpg.
Show that the following two models are bisimilar.
p
p
s
w
s
v

b
-
a
p
p
p
p
s
v
1
s
w
1
s
v
0
s
w
0
...
a
-
b
-
a
-
2.2.2 This exercise asks the reader to complete in detail the proof of Proposition 2.19,
which links bisimulations and the model constructions discussed in the previous section.
You should prove these results for arbitrary similarity types.
(a) Show that if
M

=
M
0, then
M
$
M
0
(b) Show that if
U
i
M
i is the disjoint union of the models
M
i (i
2
I), then, for each
i,
M
i
$
U
i
M
i
(c) Show that if
M
0 is a generated submodel of
M, then
M
0
$
M
(d) Show that if
M
0 is a bounded morphic image of
M, then
M
0
$
M



72
2 Models
2.2.3 This exercise is about temporal bisimulations.
(a) Show from ﬁrst principles that the truth of basic temporal formulas is invariant
under temporal bisimulations. (That is, don’t appeal to any of the results proved in
this section.)
(b) Let
M and
M
0 be ﬁnite rooted models for basic temporal logic with
F and
P. Let
w and
w
0 be the roots of
M and
M
0, respectively. Prove that if
w and
w
0 satisfy
the same basic temporal formulas with
F and
P, then there exists a basic temporal
bisimulation that relates
w and
w
0.
2.2.4 Consider the binary until operator
U. In a model
M
=
(W
;
R
;
V
) its truth deﬁnition
reads:
M;
t

U
(;
 
)
iff
there is a
v such that
R
tv and
v

, and
for all
u such that
R
tu and
R
uv:
u

 
:
Prove that
U is not deﬁnable in the basic modal language. Hint: think about the following
two models, but with arrows added to make sure that the relations are transitive:
t
t
t
t
t
t
t
t
t
t
t



*
H
H
H
Y



*
H
H
H
Y



*
H
H
H
Y
I

I

I

s
0
s
1
t
0
v
0
u
v
1
t
1
s
0
u
0
v
0
t
0
q
p
q
p
q
2.2.5 Consider the following two models, which we are going to use to interpret the basic
temporal language:
M
0
=
(R
;
<;
V
0
) and
M
1
=
(R;
<;
V
1
), where
V
0 makes
q true at all
non-zero integers and
V
1 in addition makes
q true at all points of the form
1=z with
z a
non-zero integer number.
(a) Prove that there is a temporal bisimulation between
M
0 and
M
1, linking
0 (in the
one model) to
0 (in the other model).
(b) Let
 be the progressive operator deﬁned by the following truth table:
M;
s



iff
there are
t and
u such that
t
<
s
<
u and
M;
x

 for all
x between
t and
u:
Prove that this operator is not deﬁnable in the basic temporal language.
2.2.6 Suppose we have two bisimilar LTSs. Show that bisimilar states in these LTSs satisfy
exactly the same formulas of PDL.
2.2.7 Prove that two square arrow models
M
=
(S
U
;
V
) and
M
0
=
(S
U
0
;
V
0
) are bisim-
ilar if and only if there is a relation
Z between pairs over
U and pairs over
U
0 such that
(i) if
(u;
v
)Z
(u
0
;
v
0
), then
(u;
v
)
2
V
(p) iff
(u
0
;
v
0
)
2
V
0
(p),
(ii) if
(u;
v
)Z
(u
0
;
v
0
), then
u
=
v iff
u
0
=
v
0,
(iii) if
(u;
v
)Z
(u
0
;
v
0
), then
(v
;
u)Z
(v
0
;
u
0
),
(iv) if
(u;
v
)Z
(u
0
;
v
0
), then for any
w
2
U there exists a
w
0
2
U
0 such that both
(u;
w
)Z
(u
0
;
w
0
) and
(w
;
v
)Z
(w
0
;
v
0
),
(v) and vice versa.



2.3 Finite Models
73
Must any two bisimilar square arrow models be isomorphic? (Hint: think of
V
(p) and
V
0
(p) as the natural ordering relations of the rational and the real numbers, respectively.)
2.2.8 Suppose that
fZ
i
j
i
2
I
g is a non-empty collection of bisimulations between
M and
M
0. Prove that the relation
S
i2I
Z
i is also a bisimulation between
M and
M
0. Conclude
that if
M and
M
0 are bisimilar, then there is a maximal bisimulation between
M and
M
0;
that is, a bisimulation
Z
m such that for any bisimulation
Z
:
M
$
M
0 we have
Z

Z
m.
2.3 Finite Models
Preservation and invariance results can be viewed either positively or negatively.
Viewed negatively, they map the limits of modal expressivity: they tell us, for
example, that modal languages are incapable of distinguishing a model from its
generated submodels. Viewed positively, they are a toolkit for transforming mod-
els into more desirable forms without affecting satisﬁability. Proposition 2.15 has
already given us a taste of this perspective (we showed that modal languages have
the tree model property) and it will play an important role when we discuss com-
pleteness in Chapter 4.
The results of this section are similarly double-edged. We are going to investi-
gate modal expressivity over ﬁnite models, and the basic result we will prove is that
modal languages have the ﬁnite model property: if a modal formula is satisﬁable
on an arbitrary model, then it is satisﬁable on a ﬁnite model.
Deﬁnition 2.27 (Finite Model Property)
Let
 be a modal similarity type, and
let
M be a class of
-models. We say that
 has the ﬁnite model property with
respect to
M if the following holds: if
 is a formula of similarity type
, and
 is
satisﬁable in some model in
M, then
 is satisﬁable in a ﬁnite model in
M.
a
In this section we will mostly be concerned with the special case in which
M in
Deﬁnition 2.27 is the collection of all
-models, so to simplify terminology we
will use the term ‘ﬁnite model property’ for this special case. The fact that modal
languages have the ﬁnite model property (in this sense) can be viewed as a lim-
itative result: modal languages simply lack the expressive strength to force the
existence of inﬁnite models. (By way of contrast, it is easy to write down ﬁrst-
order formulas which can only be satisﬁed on inﬁnite models.) On the other hand,
the result is a source of strength: we do not need to bother about (arbitrary) inﬁnite
models, for we can always ﬁnd an equivalent ﬁnite one. This opens the door to the
decidability results of Chapter 6. (The satisﬁability problem for ﬁrst-order logic,
as the reader probably knows, is undecidable over arbitrary models.)
We will discuss two methods for building ﬁnite models for satisﬁable modal
formulas. The ﬁrst is to (carefully!) select a ﬁnite submodel of the satisfying
model, the second (called the ﬁltration method) is to deﬁne a suitable quotient
structure.



74
2 Models
Selecting a ﬁnite submodel
The selection method draws together four observations. Here is the ﬁrst. We know
that modal satisfaction is intrinsically local: modalities scan the states accessible
from the current state. How much of the model can a modal formula see from the
current state? That obviously depends on how deeply the modalities it contains are
nested.
Deﬁnition 2.28 (Degree) We deﬁne the degree of modal formulas as follows.
deg
(p)
=
0
deg
(?)
=
0
deg
(:)
=
deg
()
deg
(
_
 
)
=
maxfdeg
();
deg
( 
)g
deg
(M(
1
;
:
:
:
;

n
))
=
1
+
max
fdeg
(
1
);
:
:
:
;
deg
(
n
)g:
In particular, the degree of a basic modal formula
3 is
1
+
deg
().
a
Second, we observe the following:
Proposition 2.29 Let
 be a ﬁnite modal similarity type, and assume that our col-
lection of proposition letters is ﬁnite as well.
(i) For all
n, up to logical equivalence there are only ﬁnitely many formulas of
degree at most
n.
(ii) For all
n, and every
-model
M and state
w of
M, the set of all
-formulas
of degree at most
n that are satisﬁed by
w, is equivalent to a single formula.
Proof. We prove the ﬁrst item by induction on
n. The case
n
=
0 is obvious. As
for the case
n
+
1, observe that every formula of degree

n
+
1 is a boolean combi-
nation of proposition letters and formulas of the form
3 , where
deg
( 
)

n. By
the induction hypothesis there can only be ﬁnitely many non-equivalent such for-
mulas
 . Thus there are only ﬁnitely many non-equivalent boolean combinations
of proposition letters and formulas
3 , where
 has degree at most
n. Hence,
there are only ﬁnitely many non-equivalent formulas of degree at most
n
+
1.
Item (ii) is immediate from item (i).
a
Third, we observe that there is a natural way of ﬁnitely approximating a bisimula-
tion. These ﬁnite approximations will prove crucial in our search for ﬁnite models.
Deﬁnition 2.30 (n-Bisimulations)
Here we deﬁne
n-bisimulations for modal
similarity types containing only diamonds, leaving the deﬁnition of the general
case as part of Exercise 2.3.2. Let
M and
M
0 be models, and let
w and
w
0 be
states of
M and
M
0, respectively. We say that
w and
w
0 are
n-bisimilar (notation:



2.3 Finite Models
75
w
$
n
w
0) if there exists a sequence of binary relations
Z
n





Z
0 with the
following properties (for
i
+
1

n):
(i)
w
Z
n
w
0
(ii) If
v
Z
0
v
0 then
v and
v
0 agree on all proposition letters;
(iii) If
v
Z
i+1
v
0 and
R
v
u, then there exists
u
0 with
R
0
v
0
u
0 and
uZ
i
u
0;
(iv) If
v
Z
i+1
v
0 and
R
0
v
0
u
0, then there exists
u with
R
v
u and
uZ
i
u
0.
a
The intuition is that if
w
$
n
w
0, then
w and
w
0 bisimulate up to depth
n. Clearly,
if
w
$
w
0, then
w
$
n
w
0 for all
n — but the converse need not hold; see Exer-
cise 2.3.1.
Fourth, we observe that for languages containing only ﬁnitely many proposition
letters, there is an exact match between modal equivalence and
n-bisimilarity for
all
n. That is, for such languages not only does
n-bisimilarity for all
n imply modal
equivalence, but the converse holds as well.
Proposition 2.31 Let
 be a ﬁnite modal similarity type,
 a ﬁnite set of proposi-
tion letters, and let
M and
M
0 be models for this language. Then for every
w in
M
and
w
0 in
M
0, the following are equivalent.
(i)
w
$
n
w
0
(ii)
w and
w
0 agree on all modal formulas of degree at most
n.
It follows that ‘n-bisimilarity for all
n’ and modal equivalence coincide as rela-
tions between states.
Proof. The implication (i)
) (ii) may be proved by induction on
n. For the con-
verse implication one can use an argument similar to the one used in the proof of
Theorem 2.24; we leave the proof as part of Exercise 2.3.2.
a
It is time to draw these observations together. The following deﬁnition and lemma,
which are about rooted models, give us half of what we need to build ﬁnite models.
Deﬁnition 2.32 Let
 be a modal similarity type containing only diamonds. Let
M
=
(W
;
R
1, . . . ,
R
n,
:
:
:
) be a rooted
-model with root
w. The notion of the
height of states in
M is deﬁned by induction. The only element of height 0 is the
root of the model; the states of height
n
+
1 are those immediate successors of
elements of height
n that have not yet been assigned a height smaller than
n
+
1.
The height of a model
M is the maximum
n such that there is a state of height
n in
M, if such a maximum exists; otherwise the height of
M is inﬁnite.
For a natural number
k, the restriction of
M to
k (notation:
M

k) is deﬁned
as the submodel containing only states whose height is at most
k. More precisely,
(M

k
)
=
(W
k
;
R
1k
;
:
:
:
;
R
nk
;
:
:
:
;
V
k
), where
W
k
=
fv
j
heigh
t
(v
)

k
g,
R
nk
=
R
n
\
(W
k

W
k
), and for each
p,
V
k
(p)
=
V
(p)
\
W
k.
a



76
2 Models
In words: the restriction of
M to
k contains all states that can be reached from
the root in at most
k steps along the accessibility relations. Typically, this will not
give a generated submodel, so why does it interest us? Because, as we can now
show, given a formula
 of degree
k that is satisﬁable in some rooted model
M, the
restriction of
M to
k contains all the states we need to satisfy
. To put it another
way: we are free to simply delete all states that lie beyond the ‘k-horizon.’
Lemma 2.33 Let
 be a modal similarity type that contains only diamonds. Let
M be a rooted
-model, and let
k be a natural number. Then, for every state
w of
(M

k
), we have
(M

k
);
w
$
l
M;
w, where
l
=
k
 heigh
t
(w
).
Proof. Take the identity relation on
(M

k
). We leave the reader to work out the
details as Exercise 2.3.3. The following comment may be helpful: in essence this
lemma tells us that if we are only interested in the satisﬁability of modal formulas
of degree at most
k, then generating submodels of height
k sufﬁces to maintain
satisﬁability.
a
Putting together Proposition 2.31 and Lemma 2.33, we conclude that every satis-
ﬁable modal formula can be satisﬁed on a model of ﬁnite height. This is clearly
useful, but we are only halfway to our goal: the resulting model may still be inﬁ-
nite, as it may be inﬁnitely branching. We obtain the ﬁnite model we are looking
for by a further selection of points; in effect this discards unwanted branches and
leads to the desired ﬁnite model.
Theorem 2.34 (Finite Model Property — via Selection) Let
 be a modal simi-
larity type containing only diamonds, and let
 be a
-formula. If
 is satisﬁable,
then it is satisﬁable on a ﬁnite model.
Proof. Fix a modal formula
 with
deg
()
=
k. We restrict our modal simi-
larity type
 and our collection of proposition letters to the modal operators and
proposition letters actually occurring in
. Let
M
1
;
w
1 be such that
M
1
;
w
1

.
By Proposition 2.15, there exists a tree-like model
M
2 with root
w
2 such that
M
2
;
w
2

. Let
M
3
:=
(M
2

k
). By Lemma 2.33 we have
M
2
;
w
2
$
k
M
3
;
w
2,
and by Proposition 2.31 it follows that
M
3
;
w
2

.
By induction on
n

k we deﬁne ﬁnite sets of states
S
0, . . . ,
S
k and a (ﬁnal)
model
M
4 with domain
S
0
[



[
S
k; the points in each
S
n will have height
n.
Deﬁne
S
0 to be the singleton
fw
2
g. Next, assume that
S
0, . . . ,
S
n have already
been deﬁned. Fix an element
v of
S
n. By Proposition 2.29 there are only ﬁnitely
many non-equivalent modal formulas whose degree is at most
k, say
 
1, . . . ,
 
m.
For each such formula that is of the form
hai and holds in
M
3 at
v, select a state
u from
M
3 such that
R
a
v
u and
M
3
;
u

. Add all these
us to
S
n+1, and repeat
this selection process for every state in
S
n.
S
n+1 is deﬁned as the set of all points
that have been selected in this way.



2.3 Finite Models
77
Finally, deﬁne
M
4 as follows. Its domain is
S
0
[



[
S
k; as each
S
i is ﬁnite,
M
4
is ﬁnite. The relations and valuation are obtained by restricting the relations and
valuation of
M
3 to the domain of
M
4. By Exercise 2.3.4 we have that
M
4
;
w
2
$
k
M
3
;
w
2, and hence
M
4
;
w
2

, as required.
a
How well does the selection method generalize to other modal languages? For
certain purposes it is ﬁne. For example, to deal with arbitrary modal similarity
types, the notion of a tree-like model needs to be adapted (in fact, we explained
how to do this in Exercise 2.1.7), but once this has been done we can prove a
general version of Proposition 2.15. Next, the notion of
n-bisimilarity needs to
be adapted to other similarity types, but that too is straightforward (it is part of
Exercise 2.3.2). Finally, the selection process in the proof of Theorem 2.34 needs
adaptation, but this is unproblematic. In short, we can show that the ﬁnite model
property holds for arbitrary similarity types using the selection method.
The method has a drawback: the input model for our construction may satisfy
important relational properties (such as being symmetric), but the end result is al-
ways a ﬁnite tree-like model, and the desired relational properties may be (and
often are) lost. So if we want to establish the ﬁnite model property with respect
to a class of models satisfying additional properties — something that is very im-
portant in practice — we may have to do additional work once we have obtained
our ﬁnite tree-like model. In such cases, the selection method tends to be harder
to use than the ﬁltration method (which we discuss next). Nonetheless, the idea of
(intelligently!) selecting points to build submodels is important, and (as we will
see in Section 6.6 when we discuss NP-completeness) the idea really comes into
its own when the model we start with is already ﬁnite.
Finite models via ﬁltrations
We now examine the classic modal method for building ﬁnite models: ﬁltration.
Whereas the selection method builds ﬁnite models by deleting superﬂuous material
from large, possibly inﬁnite models, the ﬁltration method produces ﬁnite models
by taking a large, possibly inﬁnite model and identifying as many states as possible.
We ﬁrst present the ﬁltration method for the basic modal language.
Deﬁnition 2.35 A set of formulas
 is closed under subformulas (or: subformula
closed) if for all formulas
,

0: if

_

0
2
 then so are
 and

0; if
:
2
 then
so is
; and if
M
(
1
;
:
:
:
;

n
)
2
 then so are

1, . . . ,

n. (For the basic modal
language, this means that if
3
2
, then so is
.)
a
Deﬁnition 2.36 (Filtrations) We work in the basic modal language. Let
M
=
(W
;
R
;
V
) be a model and
 a subformula closed set of formulas. Let
!
 be the



78
2 Models




'
&
$
%
s
4
s
3
s
s
2
1
s
0
...
-
q
1
-
s
s
-
j1j
j0j
Æ


Fig. 2.6. A model and its ﬁltration
relation on the states of
M deﬁned by:
w
!

v iff for all
 in
:
(M;
w

 iff
M;
v

).
Note that
!
 is an equivalence relation. We denote the equivalence class of a
state
w of
M with respect to
!
 by
jw
j
, or simply by
jw
j if no confusion will
arise. The mapping
w
7!
jw
j that sends a state to its equivalence class is called the
natural map.
Let
W

=
fjw
j

j
w
2
W
g. Suppose
M
f
 is any model
(W
f
;
R
f
;
V
f
) such
that:
(i)
W
f
=
W
.
(ii) If
R
w
v then
R
f
jw
jjv
j.
(iii) If
R
f
jw
jjv
j then for all
3
2
, if
M;
v

 then
M;
w

3.
(iv)
V
f
(p)
=
fjw
j
j
M;
w

pg, for all proposition letters
p in
.
Then
M
f
 is called a ﬁltration of
M through
.
a
Because of item (ii), the natural map associated with any ﬁltration is guaranteed to
be a homomorphism (see Deﬁnition 2.7). And at ﬁrst glance it may seem that it
is even guaranteed to be a bounded morphism (see Deﬁnition 2.10), for item (iii)
seems reminiscent of the back condition. Unfortunately, this is not the case, as the
following example shows.
Example 2.37 Let
M be the model
(N
;
R
;
V
), where
R
=
f(0;
1),
(0;
2),
(1;
3)g
[
f(n;
n
+
1)
j
n

2g, and
V has
V
(p)
=
N
n
f0g and
V
(q
)
=
f2g.
Further, assume that

=
f3p;
pg. Clearly
 is subformula closed. Then,
the model
N
=
(fj0j;
j1jg;
f(j0j;
j1
j);
(j1
j;
j1j
)g;
V
0
), where
V
0
(p)
=
fj1jg, is a
ﬁltration of
M through
. See Figure 2.6.
Clearly,
N can not be a bounded morphic image of
M: any bounded morphism
would have to preserve the formula
q, and the natural map does not preserve
q, and
need not, because
q is not an element of our subformula closed set
.
a



2.3 Finite Models
79
But in many other respects ﬁltrations are well-behaved. For a start, the method
gives us a bound (albeit an exponential one) on the size of the resulting ﬁnite model:
Proposition 2.38 Let
 be a ﬁnite subformula closed set of basic modal formulas.
For any model
M, if
M
f is a ﬁltration of
M through a subformula closed set
,
then
M
f contains at most
2
card
(
) nodes (where
card(
) denotes the size of
).
Proof. The states of
M
f are the equivalence classes in
W
. Let
g be the function
with domain
W
 and range
P
(
) deﬁned by
g
(jw
j)
=
f
2

j
M;
w

g.
It follows from the deﬁnition of
!
 that
g is well deﬁned and injective. Thus
card
(W

)

card(P
(
))
=
2
card
(
).
a
Moreover — crucially — ﬁltrations preserve satisfaction in the following sense.
Theorem 2.39 (Filtration Theorem) Consider the basic modal language. Let
M
f
(=
(W

;
R
f
;
V
f
)) be a ﬁltration of
M through a subformula closed set
.
Then for all formulas

2
, and all nodes
w in
M, we have
M;
w

 iff
M
f
;
jw
j

.
Proof. By induction on
. The base case is immediate from the deﬁnition of
V
f.
The boolean cases are straightforward; the fact that
 is closed under subformulas
allows us to apply the inductive hypothesis.
So suppose
3
2
 and
M;
w

3. Then there is a
v such that
R
w
v and
M;
v

. As
M
f is a ﬁltration,
R
f
jw
jjv
j. As
 is subformula closed,

2
,
thus by the inductive hypothesis
M
f
;
jv
j

. Hence
M
f
;
jw
j

3.
Conversely, suppose
3
2
 and
M
f
;
jw
j

3. Thus there is a state
jv
j in
M
f such that
R
f
jw
jjv
j and
M
f
;
jv
j

. As

2
, by the inductive hypothesis
M;
v

. So the third clause in Deﬁnition 2.36 is applicable, and we conclude
that
M;
w

3.
a
Observe that clauses (ii) and (iii) of Deﬁnition 2.36 are designed to make the modal
case of the induction step go through in the proof above.
But we still have not done one vital thing: we have not actually shown that ﬁl-
trations exist! Observe that the clauses (ii) and (iii) in Deﬁnition 2.36 only impose
conditions on candidate relations
R
f — but we have not yet shown that a suitable
R
f can always be found. In fact, there are always at least two ways to deﬁne binary
relations that fulﬁll the required conditions. Deﬁne
R
s and
R
l as follows:
(i)
R
s
jw
jjv
j iff
9w
0
2
jw
j9v
0
2
jv
j
R
w
0
v
0.
(ii)
R
l
jw
jjv
j iff for all formulas
3 in
:
M;
v

 implies
M;
w

3.
These relations — which are not necessarily distinct — give rise to the smallest
and largest ﬁltrations respectively.



80
2 Models
Lemma 2.40 Consider the basic modal language. Let
M be any model,
 any
subformula closed set of formulas,
W
 the set of equivalence classes induced
by
!
, and
V
f the standard valuation on
W
. Then both
(W

;
R
s
;
V
f
) and
(W

;
R
l
;
V
f
) are ﬁltrations of
M through
. Furthermore, if
(W

;
R
f
;
V
f
) is
any ﬁltration of
M through
 then
R
s

R
f

R
l.
Proof. We show that
(W

;
R
s
;
V
f
) is a ﬁltration; the rest is left as an exercise.
It sufﬁces to show that
R
s fulﬁlls clauses (ii) and (iii) of Deﬁnition 2.36. But
R
s satisﬁes clause (ii) by deﬁnition, so it remains to check clause (iii). Suppose
R
s
jw
jjv
j, and further suppose that
3
2
 and
M;
v

. As
R
s
jw
jjv
j, there exist
w
0
2
jw
j and
v
0
2
jv
j such that
R
w
0
v
0. As

2
 and
M;
v

, then because
v
!

v
0, we get
M;
v
0

. But
R
w
0
v
0, so
M;
w
0

3. But
3
2
, thus as
w
0
!

w it follows that
M;
w

3.
a
Theorem 2.41 (Finite Model Property — via Filtrations) Let
 be a basic mo-
dal formula. If
 is satisﬁable, then it is satisﬁable on a ﬁnite model. Indeed, it is
satisﬁable on a ﬁnite model containing at most
2
m nodes, where
m is the number
of subformulas of
.
Proof. Assume that
 is satisﬁable on a model
M; take any ﬁltration of
M through
the set of subformulas of
. That
 is satisﬁed in the ﬁltration is immediate from
Theorem 2.39. The bound on the size of the ﬁltration is immediate from Proposi-
tion 2.38.
a
There are several points worth making about ﬁltrations. The ﬁrst has to do with
the possible loss of properties when moving from a model to one of its ﬁltrations.
As we have already discussed, a drawback of the selection method is that it can be
hard to preserve such properties. Filtrations are far better in this respect — but they
certainly are not perfect. Let us consider the matter more closely.
Suppose
(W

;
R
f
;
V
f
) is a ﬁltration of
(W
;
R
;
V
). Now, clause (ii) of Deﬁ-
nition 2.36 means that the natural map from
M to
M
f is a homomorphism with
respect to the accessibility relation
R. Thus any property of relations which is pre-
served under such maps will automatically be inherited by any ﬁltration. Obvious
examples include reﬂexivity and right unboundedness
(8x9y
R
xy
).
However, many interesting relational properties are not preserved under homo-
morphisms: transitivity and symmetry are obvious counterexamples. Thus we need
to ﬁnd special ﬁltrations which preserve these properties. Sometimes this is easy;
for example, the smallest ﬁltration preserves symmetry. Sometimes we need new
ideas to ﬁnd a good ﬁltration; the classic example involves transitivity. Let’s see
what this involves.
Lemma 2.42 Let
M be a model,
 a subformula closed set of formulas, and
W




2.3 Finite Models
81
s
s
s
s
-
s
s
s
s
-
s
s
s
s
-
...
-
s
s
s
s
Fig. 2.7. Filtrating a model based on
(Q
;
<)
the set of equivalence classes induced on
M by
!
. Let
R
t be the binary relation
on
W
 deﬁned by:
R
t
jw
jjv
j iff for all
, if
3
2
 and
M;
v


_
3 then
M;
w

3.
If
R is transitive then
(W

;
R
t
;
V
f
) is a ﬁltration and
R
t is transitive.
Proof. Left as Exercise 2.3.5.
a
In short, ﬁltrations are ﬂexible — but it is not a matter of ‘plug and play’. Creativity
is often required to exploit them.
The second point worth making is that ﬁltrations of an inﬁnite model through a
ﬁnite set manage to represent an inﬁnite amount of information in a ﬁnitary manner.
It seems obvious, at least from an intuitive point of view, that this can only be
achieved by identifying lots of points. As we have seen in Example 2.37, an inﬁnite
chain may be collapsed onto a single reﬂexive point by a ﬁltration. An even more
informative example is provided by models based on the rationals. For instance,
what happens to the density condition in the ﬁltration? Let
M
=
(Q
;
<;
V
); then
any (ﬁnite) ﬁltration of
M has the form displayed in Figure 2.7. What is going
on here? Instead of viewing models as structures made up of states and relations
between them, in the case of ﬁltrations it can be useful to view them as sets of
states (namely, the sets of identiﬁed states) and relations between those sets. The
following deﬁnition captures this idea.
Deﬁnition 2.43 Let
(W
;
R
;
V
) be a transitive frame. A cluster on
(W
;
R
;
V
) is
a subset
C of
W that is a maximal equivalence relation under
R. That is, the
restriction of
R to
C is an equivalence relation, and this is not the case for any
other subset
D of
W such that
C

D.
A cluster is simple if it consists of a single reﬂexive point, and proper if it con-
tains more than one point.
a
As Figure 2.7 shows, a (ﬁnite) ﬁltration of
(Q
;
<) can be thought of as resulting in
a ﬁnite linear sequence of clusters, perhaps interspersed with singleton irreﬂexive
points (no two of which can be adjacent). The reader is asked to check this claim
in Exercise 2.3.9. Clusters will play an important role in Section 4.5.
To conclude this section we brieﬂy indicate how the ﬁltration method can be
extended to other modal languages. Let us ﬁrst consider modal languages based



82
2 Models
on arbitrary modal similarity types
. Fix a
-model
M
=
(W,
R
M,
V
)
M2 and a
subformula closed set
 as in Deﬁnition 2.36. Suppose
M
f

=
(W
,
R
f
M,
V
f
)
M2
is a
-model where
W
 and
V
f are as in Deﬁnition 2.36, and for
M
2
,
R
f
M satisfy
(ii)
0 If
R
M
w
v
1
:
:
:
v
n then
R
f
jw
jjv
1
j
:
:
:
jv
n
j.
(iii)
0 If
R
f
jw
jjv
1
j
:
:
:
jv
n
j, then for all

1, . . . ,

n
2
, if
M
(
1
;
:
:
:
;

n
)
2

and
M;
v
1


1, . . . ,
M;
v
n


n, then
M;
w

M
(
1
;
:
:
:
;

n
).
Then
M
f
 is a
-ﬁltration of
M through
.
With this deﬁnition at hand, Proposition 2.38 and Theorem 2.39 can be reformu-
lated and proved for
-ﬁltrations, and suitable versions of the smallest and largest
ﬁltrations can also be deﬁned, resulting in a general modal analog of Theorem 2.41,
the Finite Model Property.
What about basic temporal logic, PDL, and arrow logic? It turns out that the
ﬁltration method works well for all of these. For basic temporal logic we need to
issue the customary warning (we need to be explicit about what the ﬁltration does
to
R
), but with this observed, matters are straightforward. Exercise 2.3.7 asks the
reader to deﬁne transitive ﬁltrations for the basic temporal language.
Matters are far more interesting (and difﬁcult) with PDL — but here too, by
making use of a clever idea called the Fisher-Ladner closure, it is possible to use a
ﬁltration style argument to show that PDL has the ﬁnite model property; we will do
this in Section 4.8 as part of a completeness proof (Theorem 4.91). Exercise 2.3.10
deals with the ﬁnite model property for arrow logic.
Exercises for Section 2.3
2.3.1 Find two models
M and
M
0 and states
w and
w
0 in these models such that
w
$
n
w
0
for all
n, but it is not the case that
w
$
w
0 are bisimilar. (Hint: we drew a picture of such
a pair of models in the previous section.)
2.3.2 Generalize the deﬁnition of
n-bisimulations (Deﬁnition 2.30) from diamond-only
to arbitrary modal languages. Then prove Proposition 2.31 (that
n bisimilarity for all
n
implies modal equivalence and conversely) for arbitrary modal languages.
2.3.3 Lemma 2.33 tells us that if we are only interested in the satisﬁability of modal for-
mulas of degree at most
k, we can delete all states that lie beyond the
k-horizon without
affecting satisﬁability. Prove this.
2.3.4 The proof of Theorem 2.34 uses a selection of points argument to establish the ﬁnite
model property. But no proof details were given for the last (crucial) claim in the proof,
namely that
M
4
;
w
2 is
k-bisimilar to
M
3
;
w
2. Fill in this gap.
2.3.5 First show that not every ﬁltration of a transitive model is transitive. Then prove
Lemma 2.42. That is, show that the relation
R
t deﬁned there is indeed a ﬁltration, and that
any ﬁltration of a transitive model that makes use of
R
t is guaranteed to be transitive.



2.4 The Standard Translation
83
2.3.6 Finish the proof of Lemma 2.40. That is, prove that the ﬁltrations
R
s and
R
l are
indeed the smallest and the largest ﬁltration, respectively. In addition, give an example of
a model and a set of formulas for which
R
s and
R
l coincide.
2.3.7 Show that every transitive model
(W
;
R
;
V
) has a transitive temporal ﬁltration. (Take
care to specify what the ﬁltration does to
R
.)
2.3.8 Call a frame or model euclidean if it satisﬁes
8xy
z
((R
xy
^
R
xz
)
!
R
y
z
), and let
E be the class of euclidean models. Fix a formula
, and let
 be the smallest subformula
closed set of formulas containing
 that satisﬁes, for all formulas
 : if
3
2
, then
23 
2
. (Recall that
2 is an abbreviation of
:3:.) Note that in general,
 will be
inﬁnite.
(a) Prove that
E

3 
!
23 .
(b) Prove that every euclidean model can be ﬁltrated through
 to a euclidean model.
(c) Show that every euclidean model satisﬁes the following modal reduction principles:
333
$
33,
332
$
32,
323
$
33 and
322
$
32. That is, prove that
the formulas
333
$
33, ... are true throughout every euclidean model.
Conclude that
 is ﬁnite modulo equivalence on euclidean models.
(d) Prove that the basic modal similarity type has the ﬁnite model property with respect
to the class of euclidean models. Can you prove this result simply by ﬁltrating
through any subformula closed set of formulas containing
?
2.3.9 Show that any ﬁnite ﬁltration of a model based on the rationals with their usual or-
dering is a ﬁnite linear sequence of clusters, perhaps interspersed with singleton irreﬂexive
points, no two of which can be adjacent.
2.3.10 Consider the similarity type

! of arrow logic.
(i) Show that

! has the ﬁnite model property with respect to the class of all arrow
models.
(ii) Consider the class of arrow models based on arrow frames
F
=
(W
;
C
;
R
;
I
) such
that for all
s,
t and
u in
W we have (i)
C
stu iff
C
sut iff
C
tus and (ii)
C
stu and
I
u iff
s
=
t. Prove that arrow formulas have the ﬁnite model property with respect
to this class of arrow models.
(iii) Prove that

! does not have the ﬁnite model property with respect to the class of all
square models. (Hint: try to express that the extension of the propositional variable
p is a dense, linear ordering.)
2.4 The Standard Translation
In the Preface we warned the reader against viewing modal logic as an isolated
formal system (remember Slogan 3?), yet here we are, halfway through Chapter 2,
and we still haven’t linked modal logic with the wider logical world. We now put
this right. We deﬁne a link called the standard translation. This paves the way
for the results on modal expressivity in the sections that follow, for the study of
frames in the following chapter, and for the introduction of the guarded fragment
in Section 7.4.
We ﬁrst specify our correspondence languages — that is, the languages we will
translate modal formulas into.



84
2 Models
Deﬁnition 2.44 For
 a modal similarity type and
 a collection of proposition
letters, let
L
1

() be the ﬁrst-order language (with equality) which has unary pred-
icates
P
0,
P
1,
P
2, . . . corresponding to the proposition letters
p
0,
p
1,
p
2, . . . in
, and an
(n
+
1)-ary relation symbol
R
M for each (n-ary) modal operator
M in
our similarity type. We write
(x) to denote a ﬁrst-order formula
 with one free
variable,
x.
a
We are now ready to deﬁne the standard translation.
Deﬁnition 2.45 (Standard Translation) Let
x be a ﬁrst-order variable. The stan-
dard translation
ST
x taking modal formulas to ﬁrst-order formulas in
L
1

() is
deﬁned as follows:
ST
x
(p)
=
P
x
ST
x
(?)
=
x
6=
x
ST
x
(:)
=
:ST
x
()
ST
x
(
_
 
)
=
ST
x
()
_
ST
x
( 
)
ST
x
(M(
1
;
:
:
:
;

n
))
=
9y
1
:
:
:
9y
n
(R
M
xy
1
:
:
:
y
n
^
ST
y
1
(
1
)
^



^
ST
y
n
(
n
));
where
y
1, . . . ,
y
n are fresh variables (that is, variables that have not been used so far
in the translation). When working with the basic modal language, the last clause
boils down to:
ST
x
(3)
=
9y
(R
xy
^
ST
y
()):
Note that (to keep notation simple) we prefer to use
R rather than
R
3, and we
will continue to do this. We leave to the reader the task of working out what
ST
x
(O(
1
;
:
:
:
;

n
)) is, but we will point out that for the basic modal language
the required clause is:
ST
x
(2)
=
8y
(R
xy
!
ST
y
()):
a
Example 2.46 Let’s see how this works. Consider the formula
3(2p
!
q
).
ST
x
(3(2p
!
q
))
=
9y
1
(R
xy
1
^
ST
y
1
(2p
!
q
))
=
9y
1
(R
xy
1
^
(ST
y
1
(2p)
!
ST
y
1
(q
)))
=
9y
1
(R
xy
1
^
(8y
2
(R
y
1
y
2
!
ST
y
2
(p))
!
Qy
1
))
=
9y
1
(R
xy
1
^
(8y
2
(R
y
1
y
2
!
P
y
2
)
!
Qy
1
))
Note that (this version of) the standard translation leaves the choice of fresh vari-
ables unspeciﬁed. For example,
9y
256
(R
xy
256
^
(8y
14
(R
y
256
y
14
!
P
y
14
)
!
Qy
256
)) is a legitimate translation of
3(2p
!
q
), and indeed there are inﬁnitely



2.4 The Standard Translation
85
many others, all differing only in the bound variables they contain. Later in the
section we remove this indeterminacy — elegantly.
a
It should be clear that the standard translation makes good sense: it is essentially
a ﬁrst-order reformulation of the modal satisfaction deﬁnition. For any modal for-
mula
,
ST
x
() will contain exactly one free variable (namely
x); the role of this
free variable is to mark the current state; this use of a free variable makes it pos-
sible for the global notion of ﬁrst-order satisfaction to mimic the local notion of
modal satisfaction. Furthermore, observe that modalities are translated as bounded
quantiﬁers, and in particular, quantiﬁers bounded to act only on related states; this
is the obvious way of mimicking the local action of the modalities in ﬁrst-order
logic. Because of its importance it is worth pinning down just why the standard
translation works.
Models for modal languages based on a modal similarity type
 and a collection
of proposition letters
 can also be viewed as models for
L
1

(). For example,
if
 contains just a single diamond
3, then the corresponding ﬁrst-order language
L
1

() has a binary relation symbol
R and a unary predicate symbol corresponding
to each proposition letter in
 — and a ﬁrst-order model for this language needs to
provide an interpretation for these symbols. But a (modal) model
M
=
(W
;
R
;
V
)
supplies precisely what is required: the binary relation
R can be used to interpret
the relation symbol
R, and the set
V
(p
i
) can be used to interpret the unary predicate
P
i. This should not come as a surprise. As we emphasized in Chapter 1 (especially
Sections 1.1 and 1.3) there is no mathematical distinction between modal and ﬁrst-
order models — both modal and ﬁrst-order models are simply relational structures.
Thus it makes perfect sense to write things like
M
j
=
ST
x
()[w
], which means
that the ﬁrst-order formula
ST
x
() is satisﬁed (in the usual sense of ﬁrst-order
logic) in the model
M when
w is assigned to the free variable
x.
Proposition 2.47 (Local and Global Correspondence on Models) Fix a modal
similarity type
, and let
 be a
-formula. Then:
(i) For all
M and all states
w of
M:
M;
w

 iff
M
j
=
S
T
x
()[w
].
(ii) For all
M:
M

 iff
M
j
=
8x
ST
x
().
Proof. By induction on
. We leave this to the reader as Exercise 2.4.1.
a
Summing up: when interpreted on models, modal formulas are equivalent to ﬁrst-
order formulas in one free variable. Fine — but what does that give us? Lots!
Proposition 2.47 is a bridge between modal and ﬁrst-order logic — and we can use
this bridge to import results, ideas, and proof techniques from one to the other.
Example 2.48 First-order logic has the compactness property: if
 is a set of
ﬁrst-order formulas, and every every ﬁnite subset of
 is satisﬁable, then so is




86
2 Models
itself. It also has the downward L¨owenheim-Skolem property: if a set of ﬁrst-order
formulas has an inﬁnite model, then it has a countably inﬁnite model.
It follows that modal logic must have both these properties (over models) too.
Consider compactness. Suppose
 is a set of modal formulas every ﬁnite subset
of which is satisﬁable — is
 itself satisﬁable? Yes. Consider the set
fS
T
x
()
j

2

g. As every ﬁnite subset of
 has a model it follows (reading item (i) of
Proposition 2.47 left to right) that every ﬁnite subset of
fST
x
()
j

2

g does
too, and hence (by ﬁrst-order compactness) that this whole set is satisﬁable in some
model, say
M. But then it follows (this time reading item (i) of Proposition 2.47
right to left) that
 is satisﬁable in
M, hence modal satisﬁability over models is
compact.
And there’s interesting trafﬁc from modal logic to ﬁrst-order logic too. For ex-
ample, a signiﬁcant difference between modal and ﬁrst-order logic is that modal
logic is decidable (over arbitrary models) but ﬁrst-order logic is not. By using our
understanding of modal decidability, it is possible to locate novel decidable frag-
ments of ﬁrst-order logic, a theme we will return to in Section 7.4 when we discuss
the guarded fragment.
a
Just as importantly, the standard translation gives us a new research agenda for
investigating modal expressivity: correspondence theory. The central aim of this
chapter is to explore the expressivity of modal logic over models — but how is ex-
pressivity to be measured? Proposition 2.47 suggests an interesting strategy: try to
characterize the fragment of ﬁrst-order logic picked out by the standard translation.
It is obvious on purely syntactic grounds that the standard translation is not
surjective (standard translations of modal formulas contain only bounded quan-
tiﬁers) — but could every ﬁrst-order formula (in the appropriate correspondence
language) be equivalent to the translation of a modal formula? No. This is very
easy to see: whereas modal formulas are invariant under bisimulations, ﬁrst-order
formulas need not be; thus any ﬁrst-order formula which is not invariant under
bisimulations cannot be equivalent to the translation of a modal formula. We have
seen such a formula in Section 2.2, (namely
9y
1
y
2
y
3
(y
1
6=
y
2
^
y
1
6=
y
3
^
y
2
6=
y
3
^
R
xy
1
^
R
xy
2
^
R
y
1
y
3
^
R
y
2
y
3
)), and it is easy to ﬁnd simpler examples.
Thus the (ﬁrst-order formulas equivalent to) standard translations of model for-
mulas are a proper subset of the correspondence language. Which subset? Here’s
a nice observation. The standard translation can be reformulated so that it maps
every modal formula into a very small fragment of
L
1

(), namely a certain ﬁnite-
variable fragment. Suppose the variables of
L
1

() have been ordered in some way.
Then the
n-variable fragment of
L
1

() is the set of
L
1

() formulas that contain
only the ﬁrst
n variables. As we will now see, by judicious reuse of variables, a
modal language with operators of arity at most
n can be translated into the
n
+
1-
variable fragment of
L
1

(). (Reuse of variables is the name of the game when



2.4 The Standard Translation
87
working with ﬁnite variable fragments. For example, we can express the existence
of three different points in a linear ordering using only two variables as follows:
9xy
(x
<
y
^
9x
(y
<
x)).)
Proposition 2.49
(i) Let
 be a modal similarity type that only contains di-
amonds. Then, every
-formula
 is equivalent to a ﬁrst-order formula
containing at most two variables.
(ii) More generally, if
 does not contain modal operators
M whose arity ex-
ceeds
n, all
-formulas are equivalent to ﬁrst-order formulas containing at
most
n
+
1 variables.
Proof. Assume
 contains only diamonds
hai,
hbi, . . . ; proving the general case
is left as Exercise 2.4.2. Fix two distinct individual variables
x and
y. Deﬁne two
variants
ST
x and
ST
y of the standard translation as follows.
ST
x
(p) =
P
x
ST
y
(p) =
P
y
ST
x
(?) =
x
6=
x
ST
y
(?) =
y
6=
y
ST
x
(:) =
:ST
x
()
ST
y
(:) =
:ST
y
()
ST
x
(
_
 
) =
ST
x
()
_
ST
x
( 
)
ST
y
(
_
 
) =
ST
y
()
_
ST
y
( 
)
ST
x
(hai) =
9y
(R
a
xy
^
ST
y
())
ST
y
(hai) =
9x
(R
a
y
x
^
ST
x
()).
Then, for any
-formula
, its
ST
x-translation contains at most the two variables
x and
y, and
S
T
x
() is equivalent to the original standard translation of
.
a
Example 2.50 Let’s see how this modiﬁed standard translation works. Consider
again the formula
3(2p
!
q
).
ST
x
(3(2p
!
q
))
=
9y
(R
xy
^
ST
y
(2p
!
q
))
=
9y
(R
xy
^
(8x
(R
y
x
!
ST
x
(p))
!
Qy
))
=
9y
(R
xy
^
(8x
(R
y
x
!
P
x)
!
Qy
))
That is, we just keep ﬂipping between the two variables
x and
y. The result is
a translation containing only two variables (instead of the three used in Exam-
ple 2.46). As a side effect, the indeterminacy associated with the original version
of the standard translation has disappeared.
a
This raises another question: is every ﬁrst-order formula
(x) in two variables
equivalent to the translation of a basic modal formula? Again the answer is no.
There is even a ﬁrst-order formula in a single variable
x which is not equivalent
to any modal formula, namely
R
xx. To see this, assume for the sake of a con-
tradiction that
 is a modal formula such that
ST
x
() is equivalent to
R
xx. Let
M be a singleton reﬂexive model and let
w be the unique state in
M; obviously
(irrespective of the valuation)
M
j
=
R
xx[w
]. Let
N be a model based on the strict
ordering of the integers; obviously (again, irrespective of the valuation), for every



88
2 Models
integer
v,
N
j
=
:R
xx[v
]. Let
Z be the relation which links every integer with the
unique state in
M, and assume that the valuations in
N and
M are such that
Z is
a bisimulation (for example, make all proposition letters true at all points in both
models). As
M
j
=
R
xx[w
], it follows by Proposition 2.47 that
M;
w

 (after all,
by assumption
R
xx is equivalent to
ST
x
()). But for any integer
v, we have that
w
$
v, hence
N;
v

. Hence (again by Proposition 2.47 and our assumption
that
ST
x
() is equivalent to
R
xx) we have that
N
j
=
R
xx[v
], contradicting the
fact that
N
j
=
:R
xx[v
].
We will not discuss correspondence theory any further here, but in Section 2.6
we will prove one of its central results, the Van Benthem Characterization Theo-
rem: a ﬁrst-order formula is equivalent to the translation of a modal formula if and
only if it is invariant under bisimulations.
Proposition 2.47 is also going to help us investigate modal expressivity in other
ways, notably via the concept of deﬁnability.
Deﬁnition 2.51 Let
 be a modal similarity type,
C a class of
-models, and
  a
set of formulas over
. We say that
  deﬁnes or characterizes a class
K of models
within
C if for all models
M in
C we have that
M is in
K iff
M

 . If
C is
the class of all
-models, we simply say that
  deﬁnes or characterizes
K; we omit
brackets whenever
  is a singleton. We will say that a formula
 deﬁnes a property
whenever
 deﬁnes the class of models satisfying that property.
a
It is immediate from Proposition 2.47 that if a class of models is deﬁnable by a set
of modal formulas, then it is also deﬁnable by a set a ﬁrst-order formulas — but
this is too obvious to be interesting. The important way in which Proposition 2.47
helps, is by making it possible to exploit standard model construction techniques
from ﬁrst-order model theory. For example, in Section 2.6 we will prove Theo-
rem 2.75 which says that a class of (pointed) models is modally deﬁnable if and
only if it is closed under bisimulations and ultraproducts (an important construc-
tion known from ﬁrst-order model theory; see Appendix A), and its complement
is closed under ultrapowers (another standard model theoretic construction). It
would be difﬁcult to overemphasize the importance of the standard translation; it
is remarkable that such a simple idea can lead to so much.
To conclude this section, let’s see how to adapt these ideas to the basic temporal
language, PDL, and arrow logic. The case of basic temporal logic is easy: all we
have to do is add a clause for translating the backward looking operator
P:
ST
x
(P
)
=
9y
(R
y
x
^
ST
y
()):
Note that we are using the more sophisticated approach introduced in the proof
of Proposition 2.49: ﬂipping between two translations
ST
x and
ST
y. (Thus we
really need to add a mirror clause which ﬂips the variables back.) So, just like



2.4 The Standard Translation
89
the basic modal language, the basic temporal language can be mapped into a two
variable fragment of the correspondence language. Moreover (again, as with the
basic modal language) not every ﬁrst-order formula in two variables is equivalent
to (the translation of) a basic temporal formula (see Exercise 2.4.3).
Propositional dynamic logic calls for more drastic changes. Let’s ﬁrst look at the
-free fragment — that is, at PDL formulas without occurrences of the Kleene star.
In PDL both formulas and modalities are recursively structured, so we’re going to
need two interacting translation functions: one to handle the formulas, the other to
handle the modalities. The only interesting clause in the formula translation is the
following:
ST
x
(h
i)
=
9y
(ST
xy
(
)
^
ST
y
()):
That is, instead of returning a ﬁxed relation symbol (say
R), the formula translation
ST
x calls on
S
T
xy to start recursively decomposing the program
. Why does this
part of the translation require two free variables? Because its task is to deﬁne a
binary relation.
ST
xy
(a)
=
R
a
xy (and similarly for other pairs of variables)
ST
xy
(
1
[

2
)
=
ST
xy
(
1
)
_
ST
xy
(
2
)
ST
xy
(
1
;

2
)
=
9z
(ST
xz
(
1
)
^
ST
z
y
(
2
)):
It follows that we can translate the
-free fragment of PDL into a three variable
fragment of the correspondence language. The details are worth checking; see
Exercise 2.4.4.
But the really drastic change comes when we consider the full language of PDL
(that is, with Kleene star). Recall that a program

 is interpreted using the reﬂex-
ive, transitive closure of
R
. But the reﬂexive, transitive closure of an arbitrary
relations is not a ﬁrst-order deﬁnable relation (see Exercise 2.4.5). So the standard
translation for PDL needs to take us to a richer background logic than ﬁrst-order
logic, one that can express this concept. Which one should we use? There are
many options here, but to motivate our actual choice recall the deﬁnition of the
meaning of a PDL program

:
R


=
[
n
(R

)
n
;
where
R
n
 is deﬁned by
R
0
xy iff
x
=
y and
R
n+1
xy iff
9z
(R
n
xz
^
R
z
y
):
Thus, if we were allowed to write inﬁnitely long disjunctions, it would be easy to
capture the meaning of an iterated program

:
(R

)

xy iff
(x
=
y
)
_
R

xy
_
_
n1
9z
1
:
:
:
z
n
(R

xz
1
^



^
R

z
n
y
):



90
2 Models
In inﬁnitary logic we can do this. More precisely, in
L
!
1
! we are allowed to form
formulas as in ﬁrst-order logic, and, in addition, to build countably inﬁnite dis-
junctions and conjunctions. We will take
L
!
1
! as the target logic for the standard
translation of PDL. We have seen most of the clauses we need: we use the clauses
for the
-free fragment given above, and in addition the following clause to cater
for the Kleene star:
ST
xy
(

)
=
(x
=
y
)
_
ST
xy
()
_
_
n1
9z
1
:
:
:
z
n
(ST
xz
1
()
^



^
ST
z
n
y
()):
This example of PDL makes an important point vividly: we cannot always hope
to embed modal logic into ﬁrst-order logic. Indeed in the following chapter we
will see that when it comes to analyzing the expressive power of modal logic at
the level of frames, the natural correspondence language (even for the basic modal
language) is second-order logic.
There is nothing particularly interesting concerning the standard translation for
the arrow language of Example 1.16. However, this changes when we turn to
square models: in Exercise 2.4.6 the reader is asked to prove that on this class of
models, the arrow language corresponds to a ﬁrst-order language with binary pred-
icate symbols, and that, in fact, it is expressively equivalent to the three variable
fragment of such a language.
Exercises for Section 2.4
2.4.1 Prove Proposition 2.47. That is, check that the standard translation really is correct.
2.4.2 Prove Proposition 2.49 for arbitrary modal languages. That is, show that if
 does
not contain modal operators
M whose arity exceeds
n, all
-formulas are equivalent to
ﬁrst-order formulas containing at most
n
+
1 variables.
2.4.3 Show that there are ﬁrst-order formulas
(x) using at most two variables that are not
equivalent to the standard translation of a basic temporal formula.
2.4.4 In this exercise you should ﬁll in some of the details for the standard translation for
PDL.
(a) Check that the translation for the
-free fragment of PDL really does map all such
formulas into the three variable fragment of the corresponding ﬁrst-order language.
(b) Show that in fact, there is a translation into the two variable fragment of this corre-
sponding ﬁrst-order language.
2.4.5 The aim of this exercise is to show that taking the reﬂexive, transitive closure of a
binary relation is not a ﬁrst-order deﬁnable operation.
(a) Show that the class of connected graphs is not ﬁrst-order deﬁnable:



2.5 Modal Saturation via Ultraﬁlter Extensions
91
(i) For
l
2
N, let
C
l be the graph given by a cycle of length
l
+
1:
C
l
=
(f0;
:
:
:
;
l
g;
f(i;
i
+
1);
(i
+
1;
i)
j
0

i
<
l
g
[
f(0;
l
);
(l
;
0)g)
Show that for every
k
2
N and
l

2
k the graph
C
l satisﬁes the same ﬁrst-
order sentences of quantiﬁer rank at most
k as the disjoint union
C
l
]
C
l.
(ii) Conclude that the class of connected graphs is not ﬁrst-order deﬁnable.
(b) Use item (a) to conclude that the reﬂexive transitive closure of a relation is not
ﬁrst-order deﬁnable.
2.4.6 Consider the class of square models for arrow logic. Observe that a square model
M
=
(S
U
;
V
) can be seen as a ﬁrst-order model
M

=
(U;
V
(p))
p2 if we let each
propositional variable
p
2
 correspond to a dyadic relation symbol
P.
(a) Work out this observation in the following sense. Deﬁne a suitable translation
()

mapping an arrow formula
 to a formula


(x
0
;
x
1
) in this ‘dyadic correspondence
language’. Prove that this translation has the property that for all arrow formulas

and all square models
M the following correspondence holds:
M;
(a
0
;
a
1
)

 iff
M

j
=


(x
0
;
x
1
)[a
0
;
a
1
]:
(b) Show that this translation can be done within the three variable fragment of ﬁrst-
order logic.
(c) Prove that conversely, every formula
(x
0
;
x
1
) that uses only three variables, in a
ﬁrst-order language with binary predicates only, is equivalent to the translation of
an arrow formula on the class of square models.
2.5 Modal Saturation via Ultraﬁlter Extensions
Bisimulations and the standard translation are two of the tools we need to under-
stand modal expressivity over models. This section introduces the third: ultraﬁlter
extensions. To motivate their introduction, we will ﬁrst discuss Hennessy-Milner
model classes and modally saturated models; both generalize ideas met in our ear-
lier discussion of bisimulations. We will then introduce ultraﬁlter extensions as a
way of building modally saturated models, and this will lead us to an elegant result:
modal equivalence implies bisimilarity-somewhere-else.
M-saturation
Theorem 2.20 tells us that bisimilarity implies modal equivalence, but we have
already seen that the converse does not hold in general (recall Figure 2.5). The
Hennessy-Milner theorem shows that the converse does hold in the special case of
image-ﬁnite models. Let’s try and generalize this theorem.
First, when proving Theorem 2.24, we exploited the fact that, between image-
ﬁnite models, the relation of modal equivalence itself is a bisimulation. Classes of
models for which this holds are evidently worth closer study.



92
2 Models
Deﬁnition 2.52 (Hennessy-Milner Classes) Let
 be a modal similarity type, and
K a class of
-models.
K is a Hennessy-Milner class, or has the Hennessy-Milner
property, if for every two models
M and
M
0 in
K and any two states
w,
w
0 of
M
and
M
0, respectively,
w
!
w
0 implies
M;
w
$
M;
w
0.
a
For example, by Theorem 2.24, the class of image-ﬁnite models has the Hennessy-
Milner property. On the other hand, no class of models containing the two models
in Figure 2.5 has the Hennessy-Milner property.
We generalize the notion of image-ﬁniteness; doing so leads us to the concept of
modally-saturated or (brieﬂy) m-saturated models. Suppose we are working in the
basic modal language. Let
M
=
(W
;
R
;
V
) be a model, let
w be a state in
W, and
let

=
f
0
;

1
;
:
:
:
g be an inﬁnite set of formulas. Suppose that
w has successors
v
0,
v
1,
v
2, . . . where (respectively)

0,

0
^

1,

0
^

1
^

2, . . . hold. If there is no
successor
v of
w where all formulas from
 hold at the same time, then the model
is in some sense incomplete. A model is called m-saturated if incompleteness of
this kind does not occur.
To put it another way: suppose that we are looking for a successor of
w at
which every formula

i of the inﬁnite set of formulas

=
f
0
;

1
;
:
:
:
g holds.
M-saturation is a kind of compactness property, according to which it sufﬁces to
ﬁnd satisfying successors of
w for arbitrary ﬁnite approximations of
.
Deﬁnition 2.53 (M-saturation) Let
M
=
(W
;
R
;
V
) be a model of the basic
modal similarity type,
X a subset of
W and
 a set of modal formulas.
 is
satisﬁable in the set
X if there is a state
x
2
X such that
M;
x
j
=
 for all
 in
;
 is ﬁnitely satisﬁable in
X if every ﬁnite subset of
 is satisﬁable in
X.
The model
M is called m-saturated if it satisﬁes the following condition for
every state
w
2
W and every set
 of modal formulas.
If
 is ﬁnitely satisﬁable in the set of successors of
w,
then
 is satisﬁable in the set of successors of
w.
The deﬁnition of m-saturation for arbitrary modal similarity types runs as follows.
Let
 be a modal similarity type, and let
M be a
-model.
M is called m-saturated
if, for every state
w of
M and every (n-ary) modal operator
M
2
 and sequence

1, . . . ,

n of sets of modal formulas we have the following.
If for every sequence of ﬁnite subsets

1


1, . . . ,

n


n there are
states
v
1, . . . ,
v
n such that
R
w
v
1
:
:
:
v
n and
v
1


1, . . . ,
v
n


n,
then there are states
v
1, . . . ,
v
n in
M such that
R
w
v
1
:
:
:
v
n and
v
1


1, . . . ,
v
n


n.
a
Proposition 2.54 Let
 be a modal similarity type. Then the class of m-saturated
-models has the Hennessy-Milner property.



2.5 Modal Saturation via Ultraﬁlter Extensions
93
Proof. We only prove the proposition for the basic modal language. Let
M
=
(W
;
R
;
V
) and
M
0
=
(W
0
;
R
0
;
V
0
) be two m-saturated models. It sufﬁces to prove
that the relation
! of modal equivalence between states in
M and states in
M
0 is a
bisimulation. We conﬁne ourselves to a proof of the forth condition of a bisimula-
tion, since the condition concerning the propositional variables is trivially satisﬁed,
and the back condition is completely analogous to the case we prove.
So, assume that
w,
v
2
W and
w
0
2
W
0 are such that
R
w
v and
w
!
w
0.
Let
 be the set of formulas true at
v. It is clear that for every ﬁnite subset
 of
 we have
M;
v

V
, hence
M;
w

3
V
. As
w
!
w
0, it follows that
M
0
;
w
0

3
V
, so
w
0 has an
R
0-successor
v
 such that
M
0
;
v


V
. In
other words,
 is ﬁnitely satisﬁable in the set of successors of
w
0; but, then, by
m-saturation,
 itself is satisﬁable in a successor
v
0 of
w
0. Thus
v
!
v
0.
a
Ultraﬁlter extensions
So the class of m-saturated models satisﬁes the Hennessy-Milner property — but
how do we actually build m-saturated models? To this end, we will now introduce
the last of the ‘big four’ model constructions: ultraﬁlter extensions. The ultraﬁlter
extension of a structure (model or frame) is a kind of completion of the original
structure. The construction adds states to a model in order to make it m-saturated.
Sometimes the result is a model isomorphic to the original (for example, when
the original model is ﬁnite) but when working with inﬁnite models, the ultraﬁlter
extension always adds lots of new points. power set algebra of a frame; we have
met this operation already in Section 1.4 when we introduced general frames, but
we repeat the deﬁnition here.
Deﬁnition 2.55 Let
 be a modal similarity type, and
F
=
(W
;
R
M
)
M2 a
-frame.
For each
(n
+
1)-ary relation
R
M, we deﬁne the following two operations
m
M and
m
Æ
M on the power set
P
(W
) of
W.
m
M
(X
1
;
:
:
:
;
X
n
)
:=
fw
2
W
j there exist
w
1
;
:
:
:
;
w
n such that
R
M
w
w
1
:
:
:
w
n and
w
i
2
X
i for all
ig
m
Æ
M
(X
1
;
:
:
:
;
X
n
)
:=
fw
2
W
j for all
w
1
;
:
:
:
;
w
n: if
R
M
w
w
1
:
:
:
w
n,
then there is an
i with
w
i
2
X
i
g:
a
In the basic modal language
m
3
(X
) is the set of points that ‘can see’ a state in
X,
and
m
Æ
3
(X
) is the set of points that ‘only see’ states in
X. It follows that for any
model
M
V
(3)
=
m
3
(V
()) and
V
(2)
=
m
Æ
3
(V
()):
Similar identities hold for modal operators of higher arity. Furthermore,
m
M and
m
Æ
M are each other’s dual, in the following sense:



94
2 Models
Proposition 2.56 Let
 be a modal similarity type, and
F
=
(W
;
R
M
)
M2 a
-
frame. For every
n-ary modal operator
M and for every
n-tuple
X
1
;
:
:
:
;
X
n of
subsets of
W, we have
m
Æ
M
(X
1
;
:
:
:
;
X
n
)
=
W
n
m
M
(W
n
X
1
;
:
:
:
;
W
n
X
n
):
Proof. Left to the reader.
a
We are ready to deﬁne ultraﬁlter extensions. As the name is meant to suggest, the
states of the ultraﬁlter extension of a model
M are the ultraﬁlters over the universe
of
M. Filters and ultraﬁlters are discussed in Appendix A. Readers that encounter
this notion for the ﬁrst time, are advised to make the Exercises 2.5.1–2.5.4.
Deﬁnition 2.57 (Ultraﬁlter Extension) Let
 be a modal similarity type, and
F
=
(W,
R
M
)
M2 a
-frame. The ultraﬁlter extension
ue
F of
F is deﬁned as
the frame
(Uf
(W
);
R
ue
M
)
M2. Here
Uf
(W
) is the set of ultraﬁlters over
W and
R
ue
M
u
0
u
1
:
:
:
u
n holds for a tuple
u
0
;
:
:
:
;
u
n of ultraﬁlters over
W if we have that
m
M
(X
1
;
:
:
:
;
X
n
)
2
u
0 whenever
X
i
2
u
i (for all
i with
1

i

k).
The ultraﬁlter extension of a
-model
M
=
(F;
V
) is the model
ue
M
=
(ue
F,
V
ue
) where
V
ue
(p
i
) is the set of ultraﬁlters of which
V
(p
i
) is a member.
a
What are the intuitions behind this deﬁnition? First, note that the main ingredients
have a logical interpretation. Any subset of a frame can, in principle, be viewed as
(the extension or interpretation of) a proposition. A ﬁlter over the universe of the
frame can thus be seen as a theory, in fact as a logically closed theory, since ﬁlters
are both closed under intersection (conjunction) and upward closed (entailment).
Viewed this way, a proper ﬁlter is a consistent theory, for it does not contain the
empty set (falsum). Finally, an ultraﬁlter is a complete theory, or as we will call it,
a state of affairs: for each proposition (subset of the universe) an ultraﬁlter decides
whether the proposition holds (is a member of the ultraﬁlter) or not.
How does this relate to ultraﬁlter extensions? In a given frame
F not every state
of affairs need be ‘realized’, in the sense that there is a state satisfying all and
only the propositions belonging to the state of affairs; only the states of affairs that
correspond to the principal ultraﬁlters are realized, namely, as the points of the
frame. We build
ue
F by adding every state of affairs for
F as a new element of the
domain — that is,
ue
F realizes every proposition in
F.
How should we relate these new elements in
ue
F to each other and to the original
elements from
F? The obvious choice is to stipulate that
R
ue
u
0
u
1
:
:
:
u
n if
u
0
‘sees’ the
n-tuple
u
1, . . . ,
u
n. That is, whenever
X
1, . . . ,
X
n are propositions of
u
1, . . . ,
u
n respectively, then
u
0 ‘sees’ this combination: that is, the proposition
m
M
(X
1
;
:
:
:
;
X
n
) is a member of
u
0. The deﬁnition of the valuation
V
ue is self-
explanatory.



2.5 Modal Saturation via Ultraﬁlter Extensions
95
One ﬁnal comment: a special role in this section is played by the so-called prin-
cipal ultraﬁlters over
W. Recall that, given an element
w
2
W, the principal
ultraﬁlter

w generated by
w is the ﬁlter generated by the singleton set
fw
g: that
is,

w
=
fX

W
j
w
2
X
g. By identifying a state
w of a frame
F with the prin-
cipal ultraﬁlter

w, it is easily seen that any frame
F is (isomorphic to) a submodel
(but in general not a generated submodel) of its ultraﬁlter extension. For we have
the following equivalences (here proved for the basic modal similarity type):
R
w
v
iff
w
2
m
3
(X
) for all
X

W such that
v
2
X
iff
m
3
(X
)
2

w for all
X

W such that
X
2

v
(2.1)
iff
R
ue

w

v
:
Let’s make our discussion more concrete by considering an example.
Example 2.58 Consider the frame
N
=
(N
;
<) (the natural numbers in their usual
ordering):
u
0
u
1
u
2
u
3
u
4
. . .
-
-
-
-
-
What is the ultraﬁlter extension of
N? There are two kinds of ultraﬁlters over an
inﬁnite set: the principal ultraﬁlters that are in 1–1 correspondence with the points
of the set, and the non-principal ones which contain all co-ﬁnite sets, and only
inﬁnite sets, cf. Exercise 2.5.4. We have just remarked (see (2.1)) that the principal
ultraﬁlters form an isomorphic copy of the frame
N inside
ue
N. So where are
the non-principal ultraﬁlters situated? The key fact here is that for any pair
u,
u
0 of
ultraﬁlters, if
u
0 is non-principal, then
R
ue
uu
0. To see this, let
u
0 be a non-principal
ultraﬁlter, and let
X
2
u
0. As
X is inﬁnite, for any
n
2
N there is an
m such that
n
<
m and
m
2
X. This shows that
m
3
(X
)
=
N. But
N is an element of every
ultraﬁlter
u.
This shows that the ultraﬁlter extension of
N looks like a gigantic balloon at the
end of an inﬁnite string: it consists of a copy of
N, followed by an large (uncount-
able) cluster consisting of all the non-principal ultraﬁlters:
t
0
t
1
t
2
t
3
t
4
. . .
-
-
-
-
-




t
t
t
t
t
t
t
t
t
t
t
a
We will prove two results concerning ultraﬁlter extensions. The ﬁrst one, Proposi-
tion 2.59, is an invariance result: any state in the original model is modally equiv-
alent to the corresponding principal ultraﬁlter in the ultraﬁlter extension. Then, in
Proposition 2.61 we show that ultraﬁlter extensions are m-saturated. Putting these
two facts together leads us to the main result of this section: two states are modally
equivalent iff their representatives in the ultraﬁlter extensions are bisimilar.



96
2 Models
Proposition 2.59 Let
 be a modal similarity type, and
M a
-model. Then, for
any formula
 and any ultraﬁlter
u over
W,
V
()
2
u iff
ue
M;
u

. Hence, for
every state
w of
M we have
w
!

w.
Proof. The second claim of the proposition is immediate from the ﬁrst one by the
observation that
w

 iff
w
2
V
() iff
V
()
2

w.
The proof of the ﬁrst claim is by induction on
. The basic case is immediate
from the deﬁnition of
V
ue. The proofs of the boolean cases are straightforward
consequences of the deﬁning properties of ultraﬁlters. As an example, we treat
negation; suppose that
 is of the form
: , then
V
(: 
)
2
u
iff
W
n
V
( 
)
2
u
iff
V
( 
)
62
u
iff
ue
M;
u
6
 
(induction hypothesis)
iff
ue
M;
u

: 
:
Next, consider the case where
 is of the form
3 (we only treat the basic modal
similarity type, leaving the general case as an exercise to the reader). Assume ﬁrst
that
ue
M;
u

3 . Then, there is an ultraﬁlter
u
0 such that
R
ue
uu
0 and
ue
M;
u
0

 . The induction hypothesis implies that
V
( 
)
2
u
0, so by the deﬁnition of
R
ue,
m
3
(V
( 
))
2
u. Now the result follows immediately from the observation that
m
3
(V
( 
))
=
V
(3 
).
The left-to-right implication requires a bit more work. Assume that
V
(3 
)
2
u.
We have to ﬁnd an ultraﬁlter
u
0 such that
V
( 
)
2
u
0 and
R
ue
uu
0. The latter con-
straint reduces to the condition that
m
3
(X
)
2
u whenever
X
2
u
0, or equivalently
(see Exercise 2.5.5):
u
0
0
:=
fY
j
m
Æ
3
(Y
)
2
ug

u
0
:
We will ﬁrst show that
u
0
0 is closed under intersection. Let
Y ,
Z be members of
u
0
0. By deﬁnition,
m
Æ
3
(Y
) and
m
Æ
3
(Z
) are in
u. But then
m
Æ
3
(Y
\
Z
)
2
u, as
m
Æ
3
(Y
\
Z
)
=
m
Æ
3
(Y
)
\
m
Æ
3
(Z
), as a straightforward proof shows. This proves
that
Y
\
Z
2
u
0
0.
Next we make sure that for any
Y
2
u
0
0,
Y
\
V
( 
)
6=
?. Let
Y be an ar-
bitrary element of
u
0
0, then by deﬁnition of
u
0
0,
m
Æ
3
(Y
)
2
u. As
u is closed
under intersection and does not contain the empty set, there must be an element
x in
m
Æ
3
(Y
)
\
V
(3 
). But then
x must have a successor
y in
V
( 
). Finally,
x
2
m
Æ
3
(Y
) implies
y
2
Y .
¿From the fact that
u
0
0 is closed under intersection, and the fact that for any
Y
2
u
0
0,
Y
\
V
( 
)
6=
?, it follows that the set
u
0
0
[
fV
( 
)g has the ﬁnite intersection
property. So the Ultraﬁlter Theorem (Fact A.14 in the Appendix) provides us with
an ultraﬁlter
u
0 such that
u
0
0
[
fV
( 
)g

u
0. This ultraﬁlter
u
0 has the desired
properties: it is clearly a successor of
u, and the fact that
ue
M;
u
0

 follows
from
V
( 
)
2
u
0 and the induction hypothesis.
a



2.5 Modal Saturation via Ultraﬁlter Extensions
97
Example 2.60 As with the invariance results of Section 2.1 (disjoint unions, gen-
erated submodels, and bounded morphisms), our new invariance result can be used
to compare the relative expressive power of modal languages. Consider the modal
constant
	 whose truth deﬁnition in a model for the basic modal language is
M;
w

	 iff
M
j
=
R
xx[v
] for some
v in
M.
Can such a modality be deﬁned in the basic modal language? No — a bisimulation
based argument given at the end of the previous section already establishes this.
Alternatively, we can see this by comparing the pictures of the frames
(N
;
<) and
its ultraﬁlter extension given in Example 2.58. The former is loop-free (thus in any
model over this frame,
ue
M;

0
6
	), but the later contains uncountably many
loops (thus
ue
M;

0

	). So if we want
	 we have to add it as a primitive.
a
Proposition 2.61 Let
 be a modal similarity type, and let
M be a
-model. Then
ue
M is m-saturated.
Proof. We only prove the proposition for the basic modal similarity type. Let
M
=
(W
;
R
;
V
) be a model; we will show that its ultraﬁlter extension
ue
M is m-
saturated. Consider an ultraﬁlter
u over
W, and a set
 of modal formulas which
is ﬁnitely satisﬁable in the set of successors of
u. We have to ﬁnd an ultraﬁlter
u
0
such that
R
ue
uu
0 and
ue
M;
u
0

. Deﬁne

=
fV
()
j

2

0
g
[
fY
j
m
Æ
3
(Y
)
2
ug;
where

0 is the set of (ﬁnite) conjunctions of formulas in
. We claim that the set
 has the ﬁp. Since both
fV
()
j

2

0
g and
fY
j
m
Æ
3
(Y
)
2
ug are closed
under intersection, it sufﬁces to prove that for an arbitrary

2

0 and an arbitrary
set
Y

W for which
m
Æ
3
(Y
)
2
u, we have
V
()
\
Y
6=
?. But if

2

0, then
by assumption, there is a successor
u
00 of
u such that
ue
M;
u
00

, or, in other
words,
V
()
2
u
00. Then,
m
Æ
3
(Y
)
2
u implies
Y
2
u
00 by Exercise 2.5.5. Hence,
V
()
\
Y is an element of the ultraﬁlter
u
00 and, therefore, cannot be identical to
the empty set.
It follows by the Ultraﬁlter Theorem that
 can be extended to an ultraﬁlter
u
0.
Clearly,
u
0 is the required successor of
u in which
 is satisﬁed.
a
We have ﬁnally arrived at the main result of this section: a characterization of
modal equivalence as bisimilarity-somewhere-else — namely, between ultraﬁlter
extensions.
Theorem 2.62 Let
 be a modal similarity type, and let
M and
M
0 be
-models,
and
w,
w
0 two states in
M and
M
0, respectively. Then
M;
w
!
M
0
;
w
0 iff
ue
M;

w
$
ue
M
0
;

w
0
:



98
2 Models
Proof. Immediate by Propositions 2.59, 2.61 and 2.54.
a
Three remarks. First, it is easy to deﬁne ultraﬁlter extensions and prove an analog
of Theorem 2.62 for the basic temporal logic and arrow logic; see Exercises 2.5.8
and 2.5.9. With PDL the situation is a bit more complex; see Exercise 2.5.11. (The
problem is that the property of one relation being the reﬂexive transitive closure
of another is not preserved under taking ultraﬁlter extensions.) Second, we have
not seen the last of ultraﬁlter extensions. Like disjoint unions, generated submod-
els, and bounded morphisms, ultraﬁlter extensions are a fundamental modal model
construction technique, and we will make use of them when we discuss frames (in
Chapter 3) and algebras (in Chapter 5). We will shortly see that ultraﬁlter exten-
sions tie in neatly with ideas from ﬁrst-order model theory — and we will use this
to prove a second bisimilarity-somewhere-else result, Lemma 2.66. Finally, some
readers may still have the feeling that taking the ultraﬁlter extension of a model is
a far less natural construction than the other model operations that we have met.
These readers are advised to hold on until (or take a peek ahead towards) Chapter 5,
where we will see that ultraﬁlter extensions are indeed a very natural byproduct of
modal logic’s duality theory.
Exercises for Section 2.5
2.5.1 Let
E be any subset of
P
(W
), and let
F be the ﬁlter generated by
E.
(a) Prove that indeed,
F is a ﬁlter over
W. (Show that in general, the intersection of a
collection of ﬁlters is again a ﬁlter.)
(b) Show that
F is the set of all
X
2
P
(W
) such that either
X
=
W or for some
Y
1,
...,
Y
n
2
E,
Y
1
\



\
Y
n

X
:
(c) Prove that
F is proper (that is: it does not coincide with
P
(W
)) iff
E has the ﬁnite
intersection property.
2.5.2 Let
W be a non-empty set, and let
w be an element of
W. Show that the principal
ultraﬁlter generated by
w, that is, the set
fX
2
P
(W
)
j
w
2
X
g, is indeed an ultraﬁlter
over
W.
2.5.3 Let
F be a ﬁlter over
W.
(a) Prove that
F is an ultraﬁlter if and only if it is proper and maximal, that is, it has
no proper extensions.
(b) Prove that
F is an ultraﬁlter if and only if it is proper and for each pair of subsets
X
;
Y of
W we have that
X
[
Y
2
F iff
X
2
F or
Y
2
F.
2.5.4 Let
W be an inﬁnite set. Recall that
X

W is co-ﬁnite if
W
n
X is ﬁnite.
(a) Prove that the collection of co-ﬁnite subsets of
W has the ﬁnite intersection prop-
erty.
(b) Show that there are ultraﬁlters over
W that do not contain any ﬁnite set.



2.5 Modal Saturation via Ultraﬁlter Extensions
99
(c) Prove that an ultraﬁlter is non-principal if and only if it contains only inﬁnite sets
if and only if it contains all co-ﬁnite sets.
(d) Prove that any ultraﬁlter over
W has uncountably many elements.
2.5.5 Given a model
M
=
(W
;
R
;
V
) and two ultraﬁlters
u and
v over
W, show that
R
ue
uv if and only if
fY
j
m
Æ
3
(Y
)
2
ug

v.
2.5.6 Let
B
=
(B
;
R
) be the transitive binary tree; that is,
B is the set of ﬁnite strings of
0s and
1s, and
R

 holds if
 is a proper initial segment of
. The aim of this exercise is
to prove that any non-principal ultraﬁlter over
B determines an inﬁnite string of
0s and
1s.
To this end, let
B
! be the set of ﬁnite and inﬁnite strings of 0s and 1s, and
R
! the relation
on
B
! given by
R

 if
 is an initial segment of
. Deﬁne a function
f
:
Uf
(B
)
!
B
!
such that for all ultraﬁlters over
B we have
uR
ue
v iff
f
(u)R
!
f
(v
).
2.5.7 Give an example of a model
M which is point-generated while its ultraﬁlter exten-
sion is not.
2.5.8 Develop a notion of ultraﬁlter extension for basic temporal logic, and establish an
analog of Theorem 2.62 for basic temporal logic.
2.5.9 Develop a notion of ultraﬁlter extension for the arrow language introduced in Exam-
ple 1.14, and establish an analog of Theorem 2.62 for this language.
2.5.10 Show that, in general, ﬁrst-order formulas are not preserved under ultraﬁlter ex-
tensions. That is, give a model
M, a state
w, and a ﬁrst-order formula
(x) such that
M
j
=
(x)[w
], but
ue
M
6j
=
(x)[
w
], where

w is the principal ultraﬁlter generated by
w.
2.5.11 Consider a modal similarity type with two diamonds,
3 and
hi, and take any
model
M
=
(S;
R
;
R

;
V
) with
S
=
N
[
f1g;
R
=
f(n
+
1;
n);
(1;
n)
j
n
2
N
g;
R

=
f(m;
n)
j
m;
n
2
N
;
m

ng
[
(f1g

S
):
Note that
R
 is the reﬂexive transitive closure of
R.
(a) Show that
M;
1

2hi2?.
(b) Let
u be an arbitrary non-principal ultraﬁlter over
S. Prove that
R
ue

1
u.
(c) Let
u be an arbitrary non-principal ultraﬁlter over
S. Prove that
u has an
R
ue-
successor in
ue
M, and that each of its
R
ue-successors is again a non-principal
ultraﬁlter.
(d) Now suppose that we add an new diamond
h?i to the language, and that in the
model
ue
M we take
R
? to be the reﬂexive transitive closure of
R
ue. Show that
ue
M;

1

3[?]3>.
(e) Prove that
R
ue

6=
R
? (hint: use Proposition 2.59), and conclude that the ultraﬁlter
extension of a regular PDL-model need not be a regular PDL-model.
(f) Prove that every non-principal ultraﬁlter over
S has a unique
R
ue-successor.



100
2 Models
2.6 Characterization and Deﬁnability
In Section 2.3 we posed two important questions about modal expressivity:
(i) What is the modal fragment of ﬁrst-order logic? That is, which ﬁrst-order
formulas are equivalent to the standard translation of a modal formula?
(ii) Which properties of models are deﬁnable by means of modal formulas?
In this, the ﬁrst advanced track section of the book, we answer both questions. Our
main tool will be a second characterization of modal equivalence as bisimilarity-
somewhere-else, the Detour Lemma. Unlike the characterization just proved (The-
orem 2.62), the Detour Lemma rests on a number of non-modal concepts and re-
sults, all of which are centered on saturated models (a standard concept of ﬁrst-
order model theory). We start by introducing saturated models and use them to
describe the modal fragment of ﬁrst-order logic. After that we show how to build
saturated models. As corollaries we obtain results on modally deﬁnable proper-
ties of models. For background information on ﬁrst-order model theory, see Ap-
pendix A.
The Van Benthem Characterization Theorem
To deﬁne the notion of saturated models, we need the concept of
-saturation, but
before giving a formal deﬁnition of the latter, we provide an informal description,
which the reader may want to use as a ‘working’ deﬁnition.
Informally, then, the notion of
-saturation can be explained as follows. First of
all, let
 (x) be a set of ﬁrst-order formulas in which a single individual variable
x
may occur free — such a set of formulas is called a type. A ﬁrst-order model
M
realizes
 (x) if there is an element
w in
M such that for all

2
 ,
M
j
=

[w
].
Next, let
M be a model for a given ﬁrst-order language
L
1 with domain
W.
For a subset
A

W,
L
1
[A] is the language obtained by extending
L
1 with new
constants
a for all elements
a
2
A.
M
A is the expansion of
M to a structure for
L
1
[A] in which each
a is interpreted as
a.
Assume that
A is of size at most
. For the sake of our informal deﬁnition
of
-saturation, assume that

=
3 and
A
=
fa
1,
a
2
g. Let
 (a
1
;
a
2
;
x) be a
type of the language
L
1
[A]; it is not difﬁcult to see that
 (a
1
;
a
2
;
x) is consistent
with the ﬁrst-order theory of
M
A iff
 (a
1
;
a
2
;
x) is ﬁnitely realizable in
M
A, (that
is,
M
A realizes every ﬁnite subset
 of
 (a
1
;
a
2
;
x)). So, for this particular set
 (a
1
;
a
2
;
x),
3-saturation of
M means that if
 (a
1
;
a
2
;
x) is ﬁnitely realizable in
M
A, then
 (a
1
;
a
2
;
x) is realizable in
M
A.
Yet another way of looking at
3-saturation for this particular set of formulas is
the following. Consider a formula

(a
1
;
a
2
;
x), and let

(x
1
;
x
2
;
x) be the formula
with the fresh variables
x
1 and
x
2 replacing each occurrence in
 of
a
1 and
a
2,
respectively. Then we have the following equivalence:



2.6 Characterization and Deﬁnability
101
M
A realizes
f
(a
1
;
a
2
;
x)g iff there is a
b such that
M
j
=

(x
1
;
x
2
;
x)[a
1
;
a
2
;
b].
So, a model is
-saturated iff the following holds for every
n
<
, and every set
 of formulas of the form

(x
1
;
:
:
:
;
x
n
;
x).
If
(a
1
;
:
:
:
;
a
n
) is an
n-tuple such that for every ﬁnite


  there is a
b

such that
M
j
=

(x
1
;
:
:
:
;
x
n
;
x)[a
1
;
:
:
:
;
a
n
;
b

] for every

2
,
then we have that there is a
b such that
M
j
=

(x
1
;
:
:
:
;
x
n
;
x)[a
1
;
:
:
:
;
a
n
;
b]
for every

2
 .
This way of looking at
-saturation is useful, for it makes the analogy with m-
saturation of the previous section clear. Both m-saturated and countably saturated
models are rich in the number of types
 (x) they realize, but the latter are far richer
than the former: they realize the maximum number of types.
Now, for the ‘ofﬁcial’ deﬁnition of
-saturation.
Deﬁnition 2.63 Let
 be a natural number, or
!. A model
M is
-saturated if for
every subset
A

W of size less than
, the expansion
M
A realizes every set
 (x)
of
L
1
[A]-formulas (with only
x occurring free) that is consistent with the ﬁrst-order
theory of
M
A. An
!-saturated model is usually called countably saturated.
a
Example 2.64 (i) Every ﬁnite model is countably saturated. For, if
M is ﬁnite,
and
 (x) is a set of ﬁrst-order formulas consistent with the ﬁrst-order theory of
M, there exists a model
N that is elementarily equivalent to
M and that realizes
 (x). But, as
M and
N are ﬁnite, elementary equivalence implies isomorphism,
and hence
 (x) is realized in
M.
(ii) The ordering of the rational numbers
(Q
;
<) is countably saturated as well.
The relevant ﬁrst-order language
L
1 has
< and
=. Take a subset
A of
Q and
let
 (x) be a set of formulas in the resulting expansion
L
1
[A] of this ﬁrst-order
language that is consistent with the theory of
(Q
;
<;
a)
a
2A. Then, there exists a
model
N of the theory of
(Q
;
<;
a)
a2A that realizes
 (x). Now take a countable
elementary submodel
N
0 of
N that contains at least one object realizing
 (x). Then
N
0 is a countable dense linear ordering without endpoints, and hence the ordering
of
N
0 is isomorphic to
(Q
;
<). The interpretations (in
N) of the constants
a for
elements
a in
A may be copied across to
N
0. Hence, as
N realizes
 (x), so does
N
0, and hence, so does
(Q
;
<), as required.
(iii) The ordering of the natural numbers
(N
;
<) is not countably saturated. To
see this, consider the following set of formulas.
 (x)
:=
f9y
1
(y
1
<
x);
:
:
:
;
9y
1
:
:
:
y
n
(y
1
<



<
y
n
<
x);
:
:
:
g:
 (x) is clearly consistent with the theory of
(N
;
<) as each of its ﬁnite subsets is
realizable in
(N
;
<). Yet,
 (x) is clearly not realizable in
(N
;
<).
a



102
2 Models
The following result explains why countably saturated models matter to us.
Theorem 2.65 Let
 be a modal similarity type. Any countably saturated
-model
is m-saturated. It follows that the class of countably saturated
-models has the
Hennessy-Milner property.
Proof. We only consider the basic modal language. Assume that
M
=
(W
;
R
;
V
),
viewed as a ﬁrst-order model, is countably saturated. Let
a be a state in
W, and
consider a set
 of modal formulas which is ﬁnitely satisﬁable in the successor set
of
a. Deﬁne

0 to be the set

0
=
fR
a
xg
[
ST
x
(
);
where
ST
x
(
) is the set
fST
x
()
j

2

g of standard translations of formulas
in
. Clearly,

0 is consistent with the ﬁrst-order theory of
M
a:
M
a realizes every
ﬁnite subset of

0, namely in some successor of
a. So, by the countable saturation
of
M,

0 itself is realized in some state
b. By
M
a
j
=
R
ax[b] it follows that
b is a
successor of
a. Then, by Theorem 2.47 and the fact that
M
a
j
=
S
T
x
()[b] for all

2
, it follows that
M;
b

. Thus
 is satisﬁable in a successor of
a.
a
In fact, we only need 2-saturation for the proof of Theorem 2.65 to go through.
This is because we restricted ourselves to the basic modal similarity type. We
leave it to the reader to check to which extent the ‘amount of saturation’ needed to
make the proof of Theorem 2.65 go through depends on the rank of the operators
of the similarity type.
We have yet to show that countably saturated models actually exist; this issue
will be addressed below (see Theorem 2.74). For now, we merely want to record the
following important use of saturated models; you may want to recall the deﬁnition
of an elementary embedding before reading the result (see Appendix A)).
Lemma 2.66 (Detour Lemma) Let
 be a modal similarity type, and let
M and
N be
-models, and
w and
v states in
M and
N, respectively. Then the following
are equivalent.
(i) For all modal formulas
:
M;
w

 iff
N;
v

.
(ii) There exists a bisimulation
Z
:
ue
M;

w
$
ue
N;

v.
(iii) There exist countably saturated models
M

;
w
 and
N

;
v
 and elementary
embeddings
f
:
M
4
M
 and
g
:
N
4
N
 such that
(a)
f
(w
)
=
w
 and
g
(v
)
=
v

(b)
M

;
w

$
N

;
v
.
What does the Detour Lemma say in words? Obviously (i)
) (ii) is just our old
bisimulation-somewhere-else result (Theorem 2.62). The key new part is the im-
plication (i)
) (iii). This says that if
M;
w and
N;
v are modally equivalent, then



2.6 Characterization and Deﬁnability
103
both can be extended — more accurately: elementarily extended — to countably
saturated models
M

;
w
 and
N

;
v
. As
M;
w and
N;
v were modally equivalent,
so are
M

;
w
 and
N

;
v
; it follows by Theorem 2.65 that the latter two models
are bisimilar. In short, this is a second ‘bisimilarity somewhere else’ result, this
time the ‘somewhere else’ being ‘in some suitable ultrapower’. Notice that in or-
der to prove the Detour Lemma all we need to establish is that every model can be
elementarily embedded in a countably saturated model — there are standard ﬁrst-
order techniques for doing so, and we will introduce one in the second half of this
section.
With the help of the Detour Lemma, we can now precisely characterize the
relation between ﬁrst-order logic, modal logic, and bisimulations. To prove the
theorem we need to explicitly deﬁne a concept which we have already invoked
informally on several occasions.
Deﬁnition 2.67 A ﬁrst-order formula
(x) in
L
1
 is invariant for bisimulations if
for all models
M and
N, and all states
w in
M,
v in
N, and all bisimulations
Z
between
M and
N such that
w
Z
v, we have
M
j
=
(x)[w
] iff
N
j
=
(x)[v
].
a
Theorem 2.68 (Van Benthem Characterization Theorem) Let
(x) be a ﬁrst-
order formula in
L
1
. Then
(x) is invariant for bisimulations iff it is (equivalent
to) the standard translation of a modal
-formula.
Proof. The direction from right to left is a consequence of Theorem 2.20. To prove
the direction from left to right, assume that
(x) is invariant for bisimulations and
consider the set of modal consequences of
:
MOC()
=
fST
x
()
j
 is a modal formula, and
(x)
j
=
ST
x
()
g:
Our ﬁrst claim is that if
MOC()
j
=
(x), then
(x) is equivalent to the translation
of a modal formula. To see why this is so, assume that
MOC()
j
=
(x); then,
by the Compactness Theorem for ﬁrst-order logic, for some ﬁnite subset
X

MOC
() we have
X
j
=
(x). So
j
=
V
X
!
(x). Trivially
j
=
(x)
!
V
X,
thus
j
=
(x)
$
V
X. And as every

2
X is the translation of a modal formula,
so is
V
X. This proves our claim.
So it sufﬁces to show that
MOC()
j
=
(x). Assume
M
j
=
MOC()[w
]; we
need to show that
M
j
=
(x)[w
]. Let
T
(x)
=
fST
x
()
j
M
j
=
ST
x
()[w
]g:
We claim that
T
(x)
[
f(x)g is consistent. Why? Assume, for the sake of con-
tradiction, that
T
(x)
[
f(x)g is inconsistent. Then, by compactness, for some
ﬁnite subset
T
0
(x)

T
(x) we have
j
=
(x)
!
:
V
T
0
(x). Hence
:
V
T
0
(x)
2
MOC
(). But this implies
M
j
=
:
V
T
0
(x)[w
], which contradicts
T
0
(x)

T
(x)
and
M
j
=
T
(x)[w
].



104
2 Models
So, let
N;
v be such that
N
j
=
T
(x)
[
f(x)g[v
]. Observe that
w and
v are
modally equivalent:
M;
w

 implies
ST
x
()
2
T
(x), which implies
N;
v

;
and likewise, if
M;
w
6
 then
M;
w

:, and
N;
v

:. If modal equivalence
implied bisimilarity we would be done, because then
M;
w and
N;
v would be
bisimilar, and from this we would be able to deduce the desired conclusion
M;
w
j
=
(x)[w
] by invariance under bisimulation. But, in general, modal equivalence does
not imply bisimilarity, so this is not a sound argument.
However, we can use the Detour Lemma and make a detour through a Hennessy-
Milner class where modal equivalence and bisimilarity do coincide! More pre-
cisely, the Detour Lemma yields two countably saturated models
M

;
w

<
M;
w
and
N

;
v

<
N;
v such that
M

;
w

$
N

;
v
:
M;
w
N;
v
4






4
M

;
w

$
N

;
v

:
This is where we really need the new characterization of modal equivalence in
terms of bisimulation-somewhere-else that Theorem 2.74 gives us. We need to
‘lift’ the ﬁrst-order formula
(x) from the model
N;
v to the model
N

;
v
. By
deﬁnition, the truth of ﬁrst-order formulas is preserved under elementary embed-
dings, so that this can indeed be done. However, ﬁrst-order formulas need not be
preserved under ultraﬁlter extensions (see Exercise 2.5.10), and for that reason we
cannot use the ultraﬁlter extension
ue
N;

v instead of
N

;
v
.
Returning to the main argument,
N
j
=
(x)[v
] implies
N

j
=
(x)[v

]. As
(x) is invariant for bisimulations, we get
M

j
=
(x)[w

]. By invariance under
elementary embeddings, we have
M
j
=
(x)[w
]. This proves the theorem.
a
Ultraproducts
The preceding discussion left us with an important technical question: how do
we get countably saturated models? Our next aim is to answer this question and
thereby prove the Detour Lemma.
The fundamental construction underlying our proof is that of an ultraproduct.
Here we brieﬂy recall the basic ideas; further details may be found in Appendix A.
We ﬁrst apply the construction to sets, and then to models. Suppose
I
6=
?,
U is
an ultraﬁlter over
I, and for each
i
2
I,
W
i is a non-empty set. Let
C
=
Q
i2I
W
i
be the Cartesian product of those sets. That is:
C is the set of all functions
f with
domain
I such that for each
i
2
I,
f
(i)
2
W
i. For two functions
f,
g
2
C we say
that
f and
g are
U-equivalent (notation
f

U
g) if
fi
2
I
j
f
(i)
=
g
(i)g
2
U.
The result is that

U is an equivalence relation on the set
C.



2.6 Characterization and Deﬁnability
105
Deﬁnition 2.69 (Ultraproduct of Sets) Let
f
U be the equivalence class of
f mod-
ulo

U, that is:
f
U
=
fg
2
C
j
g

U
f
g. The ultraproduct of
W
i modulo
U is
the set of all equivalence classes of

U. it is denoted by
Q
U
W
i. So
Q
U
W
i
=
ff
U
j
f
2
Q
i2I
W
i
g:
In the case where all the sets are the same, say
W
i
=
W for all
i, the ultraproduct
is called the ultrapower of
W modulo
U, and written
Q
U
W.
a
Following the general deﬁnition of the ultraproduct of ﬁrst-order models (Deﬁni-
tion A.17), we now deﬁne the ultraproduct of modal models.
Deﬁnition 2.70 (Ultraproduct of Models) Fix a modal similarity type
, and let
M
i (i
2
I) be
-models. The ultraproduct
Q
U
M
i of
M
i modulo
U is the model
described as follows.
(i) The universe
W
U of
Q
U
M
i is the set
Q
U
W
i, where
W
i is the universe of
M
i.
(ii) Let
V
i be the valuation of
M
i. Then the valuation
V
U of
Q
U
M
i is deﬁned
by
f
U
2
V
U
(p) iff
fi
2
I
j
f
(i)
2
V
i
(p)g
2
U:
(iii) Let
M be a modal operator in
, and
R
Mi its associated relation in the model
M
i. The relation
R
MU in
Q
U
M
i is given by
R
MU
f
1
U
:
:
:
f
n+1
U
iff
fi
2
I
j
R
Mi
f
1
(i)
:
:
:
f
n+1
(i)g
2
U:
In particular, for a diamond item (iii) boils down to
R
3U
f
U
g
U iff
fi
2
I
j
R
3i
f
(i)g
(i)g
2
U:
a
To show that the above deﬁnition is consistent, we should check that
V
U and
R
U
depend only on the equivalence classes
f
1
U, . . . ,
f
n+1
U
.
Proposition 2.71 Let
Q
U
M be an ultrapower of
M. Then, for all modal formulas
 we have
M;
w

 iff
Q
U
M;
(f
w
)
U

, where
f
w is the constant function such
that
f
w
(i)
=
w, for all
i
2
I.
Proof. This is left as Exercise 2.6.1.
a
To build countably saturated models, we use ultraproducts based on a special kind
of ultraﬁlters. An ultraﬁlter is countably incomplete if it is not closed under count-
able intersections (of course, it will be closed under ﬁnite intersections).



106
2 Models
Example 2.72 Consider the set of natural numbers
N. Let
U be an ultraﬁlter over
N that does not contain any singletons
fng. (The reader is asked to prove that such
ultraﬁlters exist in Exercise 2.5.4.) Then, for all
n,
(N
n
fng)
2
U. But
?
=
T
n2N
(N
n
fng)
=
2
U:
So
U is countably incomplete.
a
Lemma 2.73 Let
L be a countable ﬁrst-order language,
U a countably incomplete
ultraﬁlter over a non-empty set
I, and
M an
L-model. The ultrapower
Q
U
M is
countably saturated.
Proof. See Appendix A.
a
We are now ready to prove the Detour Lemma. In Theorem 2.62 we showed that
‘bisimulation somewhere else’ can mean ‘in the ultraﬁlter extension’. Now we will
show that it can also mean: ‘in a suitable ultrapower of the original models.’
Theorem 2.74 Let
 be a modal similarity type, and let
M and
N be
-models,
and
w and
v states in
M and
N, respectively. Then the following are equivalent.
(i) For all modal formulas
:
M;
w

 iff
N;
v

.
(ii) There exist ultrapowers
Q
U
M and
Q
U
N and as well as a bisimulation
Z
:
Q
U
M;
(f
w
)
U
$
Q
U
N;
(f
v
)
U linking
(f
w
)
U and
(f
v
)
U, where
f
w
(f
v) is the constant function mapping every index to
w (v).
Proof. It is easy to see that (ii) implies (i). By Proposition 2.71
M;
w

 iff
Q
U
M;
(f
w
)
U

. By assumption this is equivalent to
Q
U
N;
(f
v
)
U

, and
the latter is equivalent to
N;
v

.
To prove the implication from (i) to (ii) we have to do some more work. Assume
that for all modal formulas
 we have
M;
w

 iff
N;
v

. We need to create
bisimilar ultrapowers of
M and
N.
Take the set of natural numbers
N as our index set, and let
U be a countably
incomplete ultraﬁlter over
N (cf. Example 2.72). By Lemma 2.73 the ultrapowers
Q
U
M and
Q
U
N are countably saturated. Now
(f
w
)
U and
(f
v
)
U are modally
equivalent: for all modal formulas
,
Q
U
M;
(f
w
)
U

 iff
Q
U
N;
(f
v
)
U

.
This claim follows from the assumption that
w and
v are modally equivalent to-
gether with Proposition 2.71. Next, apply Theorem 2.65: as
(f
w
)
U and
(f
v
)
U are
modally equivalent and
Q
U
M and
Q
U
N are countably saturated, there exists a
bisimulation
Z
:
Q
U
M;
(f
w
)
U
$
Q
U
N;
(f
v
)
U. This proves the theorem.
a
We obtain the Detour Lemma as an immediate corollary of Theorem 2.74 and
Theorem 2.62.



2.6 Characterization and Deﬁnability
107
Deﬁnability
Our next aim is to answer the second of the two questions posed at the start of this
section: which properties of models are deﬁnable by means of modal formulas?
Like the Detour Lemma, the answer is a corollary of Theorem 2.74. We formulate
the result in terms of pointed models. Given a modal similarity type
, a pointed
model is a pair
(M;
w
) where
M is a
-model and
w is a state of
M. Although
the results below can also be given for models, the use of pointed models allows
for a smoother formulation, mainly because pointed models reﬂect the local way
in which modal formulas are evaluated.
We need some further deﬁnitions. A class of pointed models
K is said to be
closed under bisimulations if
(M;
w
) in
K and
M;
w
$
N;
v implies
(N;
v
) in
K.
K is closed under ultraproducts if any ultraproduct
Q
U
(M
i
;
w
i
) of a family of
pointed models
(M
i
;
w
i
) in
K belongs to
K. If
K is a class of pointed
-models,
K
denotes the complement of
K within the class of all pointed
-models. Finally,
K is
deﬁnable by a set of modal formulas if there is a set of modal formulas
  such that
for any pointed model
(M;
w
) we have
(M;
w
) in
K iff for all

2
 ,
M;
w

;
K is deﬁnable by a single modal formula iff it is deﬁnable by a singleton set.
By Proposition 2.47 deﬁnable classes of pointed models must be closed under
bisimulations, and by Corollary A.20 they must be closed under ultraproducts as
well. Theorems 2.75 and 2.76 below show that these two closure conditions sufﬁce
to completely describe the classes of pointed models that are deﬁnable by means
of modal formulas.
Theorem 2.75 Let
 be a modal similarity type, and
K a class of pointed
-models.
Then the following are equivalent.
(i)
K is deﬁnable by a set of modal formulas.
(ii)
K is closed under bisimulations and ultraproducts, and
K is closed under
ultrapowers.
Proof. The implication from (i) to (ii) is easy. For the converse, assume
K and
K
satisfy the stated closure conditions. Observe that
K is closed under bisimulations,
as
K is. Deﬁne
T as the set of modal formulas holding in
K:
T
=
f
j for all
(M;
w
) in
K:
M;
w

g:
We will show that
T deﬁnes the class
K. First of all, by deﬁnition every pointed
model
(M;
w
) in
K is a model satisfying
T in the sense that
M;
w

T. Second,
assume that
M;
w

T; to complete the proof of the theorem we show that
(M;
w
)
must be in
K.
Deﬁne
 to be the modal theory of
w; that is,

=
f
j
M;
w

g. It is
obvious that
 is ﬁnitely satisﬁable in
K; for suppose that the set
f
1
;
:
:
:
;

n
g

 is not satisﬁable in
K. Then the formula
:(
1
^



^

n
) would be true on all



108
2 Models
pointed models in
K, so it would belong to
T, yet be false in
M;
w. But then the
following claim shows that
 is satisﬁable in the ultraproduct of pointed models
in
K.
Claim 1 Let
 be a set of modal formulas, and
K a class of pointed models in
which
 is ﬁnitely satisﬁable. Then
 is satisﬁable in some ultraproduct of models
in
K.
Proof of Claim. Deﬁne an index set
I as the collection of all ﬁnite subsets of
:
I
=
f
0


j

0 is ﬁnite
g:
By assumption, for each
i
2
I there is a pointed model
(N
i
;
v
i
) in
K such that
N
i
;
v
i

i. We now construct an ultraﬁlter
U over
I such that the ultraproduct
Q
U
N
i has a state
f
U with
Q
U
N
i
;
f
U

.
For each

2
, let
b
 be the set of all
i
2
I such that

2
i. Then the set
E
=
f
b

j

2

g has the ﬁnite intersection property because
f
1
;
:
:
:
;

n
g
2
b

1
\



\
b

n
:
So, by Fact A.14,
E can be extended to an ultraﬁlter
U over
I. This deﬁnes
Q
U
N
i;
for the deﬁnition of
f
U, let
W
i denote the universe of the model
N
i and consider
the function
f
2
Q
i2I
W
i such that
f
(i)
=
v
i.
It is left to prove that
Q
U
N
i
;
f
U


:
(2.2)
To prove (2.2), observe that for
i
2
b
 we have

2
i, and so
N
i
;
v
i

. Therefore,
for each

2

fi
2
I
j
N
i
;
v
i


g

b
 and
b

2
U
:
It follows that
fi
2
I
j
N
i
;
v
i


g
2
U, so by Theorem A.19,
Q
U
N
i
;
f
U

.
This proves (2.2).
a
It follows from Claim 1 and the closure of
K under taking ultraproducts that
 is
satisﬁable in some pointed model
(N;
v
) in
K. But
N;
v

 implies that
v and
the state
w from our original pointed model
(M;
w
) are modally equivalent. So by
Theorem 2.74 there exists an ultraﬁlter
U
0 such that
Q
U
0
(N;
v
);
(f
v
)
U
$
Q
U
0
(M;
w
);
(f
w
)
U
:
By closure under ultraproducts, the pointed model
(
Q
U
0
(N;
v
);
(f
v
)
U
) belongs to
K. Hence by closure under bisimulations,
(
Q
U
0
(M;
w
);
(f
w
)
U
) is in
K as well. By
closure of
K under ultrapowers it follows that
(M;
w
) is in
K. This completes the
proof.
a



2.6 Characterization and Deﬁnability
109
Theorem 2.76 Let
 be a modal similarity type, and
K a class of pointed
-models.
Then the following are equivalent.
(i)
K is deﬁnable by means of a single modal formula.
(ii) Both
K and
K are closed under bisimulations and ultraproducts.
Proof. The direction from (i) to (ii) is easy. For the converse we assume that
K,
K satisfy the stated closure conditions. Then both are closed under ultraproducts,
hence by Theorem 2.75 there are sets of modal formulas
T
1,
T
2 deﬁning
K and
K, respectively. Obviously their union is inconsistent in the sense that there is no
pointed model
(M;
w
) such that
(M;
w
)

T
1
[
T
2. So then, by compactness,
there exist

1, . . . ,

n
2
T
1 and
 
1
;
:
:
:
;
 
m
2
T
2 such that for all pointed models
(M;
w
)
M;
w


1
^



^

n
!
: 
1
_



_
: 
m
:
(2.3)
To complete the proof we show that
K is in fact deﬁned by the conjunction

1
^



^

n. By deﬁnition, for any
(M;
w
) in
K we have
M;
w


1
^



^

n.
Conversely, if
M;
w


1
^



^

n, then, by (2.3),
M;
w

: 
1
_



_
: 
m.
Hence,
M;
w
6
T
2. Therefore,
(M;
w
) does not belong to
K, whence
(M;
w
)
belongs to
K.
a
Theorems 2.75 and 2.76 correspond to analogous deﬁnability results in ﬁrst-order
logic: to get the analogous ﬁrst-order results, simply replace closure under bisim-
ulations in 2.75 and 2.76 by closure under isomorphisms; see the Notes at the end
of the chapter for further details. This close connection to ﬁrst-order logic may
explain why the results of this section seem to generalize to any modal logic that
has a standard translation into ﬁrst-order logic. For example, all of the results of
this section can also be obtained for basic temporal logic.
Exercises for Section 2.6
2.6.1 Prove Proposition 2.71: Let
Q
U
M be an ultrapower of
M. Then, for all modal
formulas
 we have
M;
w

 iff
Q
U
M;
(f
w
)
U

, where
f
w is the constant function
such that
f
w
(i)
=
w, for all
i
2
I.
2.6.2 Give simple proofs of Theorem 2.75 and Theorem 2.76 using the analogous proof
for ﬁrst-order logic (see Theorem A.23).
2.6.3 Let
I be an index set, and let
fM
i
g
i2I and
fN
i
g
i2I be two collections of models
such that for each
i
2
I,
M
i
$
N
i. Show that for any ultraﬁlter
U over
I, the ultraproducts
of the two collections are bisimilar:
Q
U
M
i
$
Q
U
N
i.
2.6.4
(a) Show that the ultraproduct of point-generated models need not be point-
generated.
(b) How is this for transitive models?



110
2 Models
2.7 Simulation and Safety
Theorem 2.68 provided a result characterizing the modal fragment of ﬁrst-order
logic as the class of formulas invariant for bisimulations. In this section we present
two further results in the same spirit; we focus on these results not just because they
are interesting and typical of current work in modal model theory, but also because
they provide instructive examples of how to apply the tools and proof strategies we
have discussed. We ﬁrst look at a notion of simulation that has been introduced
in various settings, and characterize the modal formulas preserved by simulations.
We then examine a question that arises in the setting of dynamic logic and process
algebra: which operations on models preserve bisimulation? That is, if we have
the back-and-forth clauses holding for
R, and we apply an operation
O to
R which
returns a new relation
O
(R
), then when do we also have the back-and-forth-clauses
for
O
(R
)?
Simulations
A simulation is simply a bisimulation from which half of the atomic clause and the
back clause have been omitted.
Deﬁnition 2.77 (Simulations) Let
 be a modal similarity type. Let
M
=
(W,
R
M,
V
)
M
2 and
M
0
=
(W
0
;
R
0
M
;
V
0
)
M2 be
-models. A non-empty binary relation
Z

W

W
0 is called a
-simulation from
M to
M
0 if the following conditions
are satisﬁed.
(i) If
w
Z
w
0 and
w
2
V
(p), then
w
0
2
V
0
(p).
(ii) If
w
Z
w
0 and
R
M
w
v
1
:
:
:
v
n then there are
v
0
1, . . . ,
v
0
n (in
W
0) such that
R
0
M
w
0
v
0
1
:
:
:
v
0
n and for all
i (1

i

n)
v
i
Z
v
0
i.
Thus, simulations only require that atomic information is preserved and that the
forth condition holds.
If
Z is a simulation from
w in
M to
w
0 in
M
0, we write
Z
:
M;
w
!
M
0
;
w
0;
if there is a simulation
Z such that
Z
:
M;
w
!
M
0
;
w
0, we sometimes write
M;
w
!
M
0
;
w
0.
A modal formula
 is preserved under simulations if for all models
M and
M
0,
and all states
w and
w
0 in
M and
M
0, respectively,
M;
w

 implies
M
0
;
w
0

,
whenever it is the case that
M;
w
!
M
0
;
w
0.
a
In various forms and under various names simulations have been considered in the-
oretical computer science. In the study of reﬁnement,
! is interpreted as follows:
if
M;
w
!
M
0
;
w
0 then (the system modeled by)
M
0
;
w
0 reﬁnes or implements (the
system modeled by)
M;
w. And in the database world one looks at simulations the
other way around: if
M;
w
!
M
0
;
w
0, then
M
0
;
w
0 constrains the structure of
M;
w



2.7 Simulation and Safety
111
by only allowing those relational patterns that are present in
M
0
;
w
0 itself. Note that
if
M;
w
!
M
0
;
w
0 then
M
0
;
w
0 cannot enforce the presence of patterns. (See the
Notes for references.) The following question naturally arises: which formulas
are preserved when passing from
M;
w to
M
0
;
w
0 along a simulation? Or, dually,
which constraints on
M;
w can be expressed by requiring that
M;
w
!
M
0
;
w
0?
Clearly simulations do not preserve the truth of all modal formulas. In particular,
let
M be a one-point model with domain
fw
g and empty relation; then, there is a
simulation from
M;
w to any state with the same valuation, no matter which model
it lives in. Using this observation it is easy to show that universal modal formulas of
the form
2(


) or
O(


) are not preserved under simulations. On the other hand,
by clause (ii) of Deﬁnition 2.77 existential modal formulas of the form
3(


) or
M
(


) are preserved under simulations. This leads to the conjecture that a modal
formula is preserved under simulations if, and only if, it is equivalent to a formula
that has been built from proposition letters, using only
^,
_ and existential modal
operators, that is, diamonds or triangles. Below we will prove this conjecture; our
proof follows the proof of Theorem 2.68 to a large extent but there is an important
difference. Since we are working within a modal language, and not in ﬁrst-order
logic, we can make do with a detour via (m-saturated) ultraﬁlter extensions rather
than the (countably saturated) ultrapowers needed in the proof of Theorem 2.68.
Call a modal formula positive existential if it has been built up from proposition
letters, using only
^,
_ and existential modal operators
3 and
4.
Theorem 2.78 Let
 be a modal similarity type, and let
 be a
-formula. Then

is preserved under simulations iff it is equivalent to a positive existential formula.
Proof. The easy inductive proof that positive existential formulas are preserved
under simulations is left to the reader. For the converse, assume that
 is preserved
under simulations, and consider the set of positive existential consequences of
:
PEC()
=
f 
j
 is positive existential and

j
=
 
g
:
We will show that
PEC()
j
=
; then, by compactness,
 is equivalent to a positive
existential modal formula. Assume that
M;
w

PEC
(); we need to show that
M;
w

. Let
 =
f: 
j
 is positive existential and
M;
w
6
 
g.
Our ﬁrst claim is that the set
fg
[
  is consistent. For, suppose otherwise. Then
there are formulas
: 
1, . . . ,
: 
n
2
  such that

j
=
 
1
_



_
 
n. By deﬁnition
each formula
 
i is a positive existential formula, hence, so is
 
1
_



_
 
n. But
then
M;
w

 
1
_



_
 
n, by assumption; from this it follows that
M;
w

 
i
for some
i (1

i

n). This contradicts
: 
i
2
 .
As a corollary we ﬁnd a model
N and a state
v of
N such that
N;
v


^
V
 .
Clearly, for every positive existential formula
 , if
N;
v

 , then
M;
w

 .
It follows from Proposition 2.59 that for the ultraﬁlter extensions
ue
M and
ue
N



112
2 Models
we have the same relation: for every positive existential formula
 , if
ue
N;

v

 , then
ue
M;

w

 . By exploiting the fact that ultraﬁlter extensions are m-
saturated (Proposition 2.61), it can be shown that this relation is in fact a simulation
from
ue
N;

v to
ue
M;

w; see Exercise 2.7.1.
In a diagram we have now the following situation.
N;
v
M;
w
!






!
ue
N;

v
!
ue
M;

w
:
We can carry
 around the diagram from
N;
v to
M;
w as follows.
N;
v


implies
ue
N;

v

 by Proposition 2.59. Since
 is preserved under simulations,
we get
ue
M;

w

. By Proposition 2.59 again we conclude
M;
w

.
a
Using Theorem 2.78 we can also answer the second of the two questions raised
above. Call a constraint
 expressible if whenever
M;
w satisﬁes
 and
N;
v
!
M;
w, then
N;
v also satisﬁes
. By Theorem 2.78 the expressible constraints
(in ﬁrst-order logic) are precisely the ones that are (equivalent to) the standard
translations of negative universal modal formulas, that is, translations of modal
formulas built up from negated proposition letters using only
_,
^ and universal
modal operators
2 and
O.
Safety
Recall from Exercise 2.2.6 that bisimulations preserve the truth of formulas from
propositional dynamic logic. This result hinges on the fact that bisimulations not
only preserve the relations
R
a corresponding to atomic programs, but also relations
that are deﬁnable from these using PDL’s relational repertoire
[,
; and
. Put differ-
ently, if the back-and-forth conditions in the deﬁnition of a bisimulation hold for
the relations
R
a
1, . . . ,
R
a
n, . . . , then they also hold for any relation that is deﬁnable
from these using
[,
; and
; these operations are ‘safe’ for bisimulation.
In this part of the section we work with modal similarity types having diamonds
only.
Deﬁnition 2.79 Let
 be a modal similarity type, and let
(x;
y
) denote an
L
1

()-
formula with at most two free variables. Then
(x;
y
) is called safe for bisimula-
tions if the following holds.
If
Z
:
M
$
M
0 is a bisimulation with
w
Z
w
0 and for some state
v of
M we
have
M
j
=
(x;
y
)[w
v
],
then there is a state
v
0 of
M
0 such that
M
0
j
=
(x;
y
)[w
0
v
0
] and
v
Z
v
0.



2.7 Simulation and Safety
113
In words,
(x;
y
) is safe if the back-and-forth clauses hold for
(x;
y
) whenever
they hold for the atomic relations.
a
Example 2.80 (i) All PDL program constructors (;,
[, and
) are safe for bisimu-
lations. For instance, assume that
w
Z
w
0, where
Z is a bisimulation, and
(w
;
v
)
2
(R
;
S
) in
M. Then, there exists
u with
R
w
u and
S
uv in
M; hence by the back-
and-forth conditions for
R and
S, we ﬁnd
u
0 with
uZ
u
0 and
R
0
w
0
u
0 in
M
0, and a
state
v
0 with
v
Z
v
0 and
S
0
u
0
v
0 in
M
0. Then
v
0 is the required
(R
;
S
)-successor of
w
0 in
M
0.
(ii) Atomic tests
(P
)?, deﬁned by
(P
)?
:=
f(x;
y
)
j
x
=
y
^
P
y
g, are safe. For,
assume that
w
Z
w
0, where
Z is a bisimulation, and
(w
;
v
)
2
(P
)?. Then
w
=
v and
M
j
=
P
x[w
]. By the atomic clause in the deﬁnition of bisimulation, this implies
M
0
j
=
P
x[w
0
]. Hence,
(w
0
;
w
0
)
2
(P
)?, as required.
(iii) Dynamic negation
(R
), deﬁned by
(R
)
=
f(x;
y
)
j
x
=
y
^
:9z
R
xz
g,
is safe. For, assume that
w
Z
w
0, where
Z is a bisimulation, and
(w
;
v
)
2

(R
) in
M. Then,
w
=
v and
w has no
R-successors in
M. Now, suppose that
w
0 did have
an
R
0-successor in
M
0; then, by the back-and-forth conditions,
w would have to
have an
R-successor in
M — a contradiction.
(iv) Intersection of relations is not safe; see Exercise 2.7.2.
a
Which operations are safe for bisimulations? Below, we give a complete answer for
the restricted case where we consider ﬁrst-order deﬁnable operations and languages
with diamonds only. We need some preparations before we can prove this result.
First, we deﬁne a modal formula
 to be completely additive in a proposition
letter
p if it satisﬁes the following.
For every family of non-empty sets
fX
i
g
i2I such that
V
(p)
=
S
i
X
i we
have
(W
;
R
1
;
:
:
:
;
V
);
w

 iff, for some
i,
(W
;
R
1
;
:
:
:
;
V
i
);
w

p, where
V
i
(p)
=
X
i and
V
i
(q
)
=
V
(q
) for
q
6=
p.
Completely additive formulas can be characterized syntactically. To this end, we
need the following technical lemma. Let
p be a ﬁxed proposition letter. We write
$
  to denote the existence of a bisimulation for the modal language without the
proposition letter
p (exactly which proposition letter is meant will be clear in the
applications of the lemma).
Lemma 2.81 Assume that
Z
:
M;
w
0
$
 N;
v
0, where
M and
N are intransi-
tive tree-like transition systems with
w
0
R



R
w
n (in
M),
v
0
R



R
v
n (in
N) and
w
i
Z
v
i (1

i

n). Then there are extensions
(M

;
w
0
) of
(M;
w
0
) and
(N

;
v
0
)
of
(N;
v
0
) (i.e., the universe of
M is a subset of the universe of
M
, and likewise



114
2 Models
for
N and
N
) such that
(M;
w
0
)
Z
:
$
 (N;
v
0
)
$






$
(M

;
w
0
)
Z
0
:
$
 (N

;
v
0
);
where
Z
0 is such that for any
i (1

i

n) we have that
w
i and
v
i are only related
to each other.
Proof. See Exercise 2.7.3.
a
Lemma 2.82 A modal formula is completely additive in
p iff it is equivalent to a
disjunction of path formulas, that is, formulas of the form
 
0
^
ha
1
i( 
1
^



^
ha
n
i( 
n
^
p)



);
(2.4)
where
p occurs in none of the formulas
 
i.
Proof. We only prove the hard direction. Assume that
 is completely additive in
p. Deﬁne
COC
()
:=
_
f 
j
 is of the form (2.4) and
 
j
=
g;
that is,
COC
() is an inﬁnite disjunction of modal formulas. We will show that

j
=
COC
(); then, by compactness,
 is equivalent to a ﬁnite disjunction of
formulas of the form speciﬁed in (2.4), and this proves the lemma.
So, assume that
M;
w
0

; we need to show
M;
w
0

COC
(). It sufﬁces to
ﬁnd a formula
 of the form speciﬁed in (2.4) such that
M;
w
0

 and
 
j
=
.
By Lemma 2.15 we may assume that
M is an intransitive, tree-like model with
root
w
0. As
 is completely additive in
p, we may also assume that
V
(p) is just a
singleton
w
n; see Figure 2.8. Consider the following description of the above path
leading up to
w
n:
	
(x
0
;
:
:
:
;
x
n
)
=
fST
x
i
( 
)
j
 
2
tp
 (w
i
) and
0

i

ng
[
fR
i
x
i
x
i+1
j
0

i

n
 1g
[
fP
x
n
g;
where we use
tp
 (w
i
) to denote the set of
p free modal formulas satisﬁed by
w
i.
The remainder of the proof is devoted to showing that
	
(x
0
;
:
:
:
;
x
n
)
j
=
ST
x
0
(),
and this will do to prove the lemma. For if
	
(x
0
;
:
:
:
;
x
n
)
j
=
ST
x
0
(), then, for
some ﬁnite subset
	
0
(x
0
;
:
:
:
;
x
n
)

	
(x
0
;
:
:
:
;
x
n
) we have
	
0
(x
0
;
:
:
:
;
x
n
)
j
=
ST
x
0
(), by compactness. Since
x
0 is the only free variable in
ST
x
0
(), this gives
9x
1
:
:
:
x
n
	
0
(x
0
;
:
:
:
;
x
n
)
j
=
ST
x
0
(). It is easy to see that the latter formula is
(the standard translation of) a path formula
 . Hence, we have found our formula
satisfying
M;
w
0

 and
 
j
=
.



2.7 Simulation and Safety
115
p
w
n
w
0
























B
B
B
B
S
S
S
a
a
a
a
S
S
S
a
a
a
a
S
S
S


















a
a
a
a
Fig. 2.8. True at only one state.
To show that
	
(x
0
;
:
:
:
;
x
n
)
j
=
ST
x
0
() we proceed as follows. Take a model
N with
N
j
=
	
(x
0
;
:
:
:
;
x
n
)[v
0
v
1
:
:
:
v
n
]; we need to show that
N
j
=
ST
x
0
()[v
0
].
It follows from the deﬁnition of
	 that each
w
i and
v
i agree on all
p free modal
formulas.
We may assume that
N is an intransitive tree with root
v. Take countably satu-
rated elementary extensions
M
y
;
w
0 and
N
y
;
v
0 of
M;
w
0 and
N;
v
0, respectively.
Since
M
y and
N
y are elementary extensions of
M and
N, respectively, we may
assume a number of things about
(M
y
;
w
0
) and
(N
y
;
v
0
) — things that can be ex-
pressed by ﬁrst-order means, and hence are preserved under passing from a model
to any of its elementary extensions. First, we may assume that
w
0 and
v
0 have no
incoming
R-transitions, for any
R, since this can be expressed by means of the
collection of all formulas of the form
8y
:R
y
x, where
R is a binary relation sym-
bol in our language. Second, we may assume that states different from
w
0 and
v
0
have at most one incoming
R-transition, for any
R, since this can be expressed by
the set of formulas of the form
8xy
z
(R
y
x
^
R
z
x
!
y
=
z
). Summarizing, then,
M
y
;
w
0 and
N
y
;
v
0 are very much like intransitive trees with roots
w
0 and
v
0 — but
possibly not quite: we have no guarantee that all nodes in
M
y and
N
y are actually
accessible from
w
0 and
v
0, respectively, in ﬁnitely many steps.
Now, from the fact that
w
i and
v
i agree on all modal formulas and Theorem 2.65,
we obtain a bisimulation
Z
y such that
Z
y
:
M
y
;
w
i
$
 N
y
;
v
i. Next, we want to
apply Lemma 2.81, but to be able to do so, our models need to be rooted, intran-
sitive trees. We can guarantee this by taking submodels
M
yÆ and
N
y
Æ of
M
y and
N
y that are generated by
w
0 and
v
0, respectively. Clearly, for some
Z, we have
Z
:
M
yÆ
$
 N
y
Æ.
By Lemma 2.81 we can move to bisimilar extensions
M
y and
N
y
 of
M
yÆ and
N
y
Æ, respectively, and ﬁnd a special bisimulation
Z
0 linking
w
i and
v
i only to each
other (for
1

i

n), as indicated in Figure 2.9.
We will amend the models
M
y
 and
N
y
 as follows. We shrink the interpretation



116
2 Models
'
&
$
%
'
&
$
%
v
1
v
0
v
n
J
J
J
J
J
]
J
J
J
J
J
]
J
J
J
]
J
J
J
]
T
T
T
T





















J
J
J
J
J
J
J
J
]
J
J
J
J
J
J
J
J
]







7



7



:



:
w
1
w
0
w
n




















B
B
B
B
S
S
S
X
X
X
X
S
S
S
X
X
X
X
S
S
S









X
X
X
X
Fig. 2.9. Linking
w
i only to
v
i (1

i

n).
of the proposition letter
p so that it only holds at
w
n and
v
n. This allows us to
extend
Z
0 to a full directed simulation
Z
00 for the whole language:
(M;
w
0
)
4
(M
y
;
w
0
)
Z
y
:
$
 (N
y
;
v
0
)
<
(N;
v
0
)
$






$
(M
yÆ
;
w
0
)
Z
:
$
 (N
y
Æ
;
v
0
)
$






$
(M
y
;
w
0
)
Z
0
:
$
 (N
y

;
v
0
)
Shrink
V
(p)






Expand
V
(p)
(M
y
;
w
0
)
Z
00
:
$
(N
y
;
v
0
):
(2.5)
We can chase
 around the diagram displayed in (2.5), from
M;
w
0 to
N;
v
0; see
Exercise 2.7.4. This proves the lemma.
a
Lemma 2.83 For any program
a and any formulas
 and
 , the following identi-
ties hold in any model:
(i)
(:)?
=
()?
(ii)
(
^
 
)?
=
()?
;
( 
)?
(iii)
(hai)?
=

(a
;
()?).
The proof of this lemma is left as Exercise 2.7.5.
Theorem 2.84 Let
 be a modal similarity type containing only diamonds, and let
(x;
y
) be a ﬁrst-order formula in
L
1

(). Then
(x;
y
) is safe for bisimulations



2.7 Simulation and Safety
117
iff it can be deﬁned from atomic formulas
R
a
xy and atomic tests
(P
)? using only
;,
[ and
.
Proof. To see that the constructions mentioned are indeed safe, consult Exam-
ple 2.80. Now, to prove the converse, let
(x;
y
) be a safe ﬁrst-order operation, and
choose a new proposition letter
p. Our ﬁrst observation is that
9y
((x;
y
)
^
P
y
) is
preserved under bisimulations. So by Theorem 2.68, the formula
9y
((x;
y
)
^
P
y
)
is equivalent to a modal formula
.
Next we exploit special properties of
 to arrive at our conclusion. First, because
of its special form,
9y
((x;
y
)
^
P
y
) is completely additive in
P, and hence,
 is completely additive in
p. Therefore, by Lemma 2.82 it is (equivalent to) a
disjunction of the form speciﬁed in (2.4). Then,
(x;
y
) must be deﬁnable using
the corresponding union of relations
( 
0
)?
;
a
1
;
( 
1
)?
;



;
a
n
;
( 
n
)?. Finally, by
using Lemma 2.83 all complex tests can be pushed inside until we get a formula of
the required form, involving only
;,
[,
 and
?.
a
Exercises for Section 2.7
2.7.1 Assume that
M and
M
0 are m-saturated models and suppose that for every positive
existential formula
 it holds that
M;
w

 only if
M
0
;
w
0

 for some
w and
w
0. Prove
that
M;
w
!
M
0
;
w
0.
2.7.2 Prove that intersection of relations is not an operation that is safe for bisimulations
(see Example 2.80).
2.7.3 The aim of this exercise is to prove Lemma 2.81: assume that
Z
:
M;
w
0
$
 N;
v
0,
where
M and
N are intransitive tree-like transition systems with
w
0
R
j



R
k
w
n (in
M),
v
0
R
j



R
k
v
n (in
N) and
w
i
Z
v
i (1

i

n).
(a) Explain why we may assume that all bisimulation links (between
M and
N) occur
between states at the same height in the tree.
(b) Next, work your way up along the branch
w
0
R
j



R
k
w
n and remove any double
bisimulation links involving the
w
i. from the
w
i. More precisely, and starting at
height 1, assume that
w
1
Z
v
1 and
w
1
Z
v. Add a copy of the submodel generated
by
w
1 to
M, connect
w
0 to the copy
w
0
1 of
w
1 by
R
j, and ‘divert’ the bisimulation
link
w
1
Z
v to
w
0
1
Z
v. Show that the resulting model
M
0 is bisimilar (in the sense of
$) to
M and that
M
0 is bisimilar to
N (in the sense of
$
 ).
(c) Similar to the previous item, but now working up the branch
v
0
R
j



R
k
v
n in
N
to eliminate any double bisimulation links ending in one of the
v
is (1

i

n).
(d) By putting together the previous items conclude that there are extensions
(M

;
w
0
)
of
(M;
w
0
) and
(N

;
v
0
) of
(N;
v
0
) (i.e., the universe of
M is a subset of the uni-
verse of
M
, and likewise for
N and
N
) such that
(M;
w
0
)
Z
:
$
 (N;
v
0
)
$






$
(M

;
w
0
)
Z
0
:
$
 (N

;
v
0
);



118
2 Models
where
Z
0 is such that for any
i (1

i

n) we have that
w
i and
v
i are only related
to each other.
2.7.4 Explain why we can chase
 around the diagram displayed in (2.5) to infer
N;
v
0


from
M;
w
0

.
2.7.5 Prove Lemma 2.83.
2.8 Summary of Chapter 2
I New Models from Old Ones: Taking disjoint unions, generated submodels, and
bounded morphic images are three important ways of building new models from
old that leave the truth values of modal formulas invariant.
I Bisimulations: Bisimulations offer a unifying perspective on model invariance,
and each of the constructions just mentioned is a kind of bisimulation. Bisimi-
larity implies modal equivalence, but the converse does not hold in general. On
image-ﬁnite models, however, bisimilarity and modal equivalence coincide.
I Using Bisimulations: Bisimulations can be used to establish non-deﬁnability
results (for example, to show that the global modality is not deﬁnable in the ba-
sic modal language), or to create models satisfying special relational properties
(for example, to show that every satisﬁable formula is satisﬁable in a tree-like
model).
I Finite Model Property: Modal languages have the ﬁnite model property (f.m.p.).
One technique for establishing the f.m.p. is by a selection of states argument
involving ﬁnite approximations to bisimulations. Another, the ﬁltration method,
works by collapsing as many states as possible.
I Standard Translation: The standard translation maps modal languages into clas-
sical languages (such as the language of ﬁrst-order logic) in a way that reﬂects
the satisfaction deﬁnition. Every modal formula is equivalent to a ﬁrst-order
formula in one free variable; if the similarity type is ﬁnite, ﬁnitely many vari-
ables sufﬁce to translate all modal formulas. Propositional dynamic logic has to
be mapped into a richer classical logic capable of expressing transitive closure.
I Ultraﬁlter Extensions: Ultraﬁlter extensions are built by using the ultraﬁlters
over a given model as the states of a new model, and deﬁning an appropriate re-
lation between them. This leads to the ﬁrst bisimilarity-somewhere-else result:
two states in two models are modally equivalent if and only if their (counterparts
in) the ultraﬁlter extensions of the two models are bisimilar.
I Van Benthem Characterization Theorem: The Detour Lemma — a bisimilarity-
somewhere-else result in terms of ultrapowers — can be used to prove the Van
Benthem Characterization Theorem: the modal fragment of ﬁrst-order logic is
the set of formulas in one free variable that are invariant for bisimulations.



2.8 Summary of Chapter 2
119
I Deﬁnability: The Detour Lemma also leads to the following result: the modally
deﬁnable classes of (pointed) models are those that are closed under bisimula-
tions and ultraproducts, while their complements are closed under ultrapowers.
I Simulation: The modal formulas preserved under simulations are precisely the
positive existential ones.
I Safety: An operation on relations is safe for bisimulations if whenever the back-
and-forth conditions hold for the base relations, they also hold for the result
of applying the operation to the relations. The ﬁrst-order operations safe for
bisimulations are the ones that can be deﬁned from atoms and atomic tests,
using only composition, union, and dynamic negation.
Notes
Kanger, Kripke, Hintikka, and others introduced models to modal logic in the late
1950s and early 1960s, and relational semantics (or Kripke semantics as it was
usually called) swiftly became the standard way of thinking about modal logic.
In spite of this, much of the material discussed in this chapter dates not from the
1960s, or even the 1970s, but from the late 1980s and 1990s. Why? Because re-
lational semantics was not initially regarded as of independent interest, rather it
was thought of as a tool that lead to interesting modal completeness theory and
decidability results. Only in the early 1970s (with the discovery of the frame in-
completeness results) did modal expressivity become an active topic of research
— and even then, such investigations were initially conﬁned to expressivity at the
level of frames rather than at the level of models. Thus the most fundamental level
of modal semantics was actually the last to be explored mathematically.
Generated submodels and bounded morphisms arose as tools for manipulating
the canonical models used in modal completeness theory (we discuss canonical
models in Chapter 4). Point-generated submodels, however, were already men-
tioned, under the name of connected model structures, in Kripke [291]. Bounded
morphisms go back to at least Segerberg [396], where they are called pseudo epi-
morphisms; this soon got shortened down to p-morphism, which remains the most
widely used terminology. A very similar, earlier, notion is in de Jongh and Troel-
stra [103]. The name bounded morphism stems from Goldblatt [192]. Disjoint
unions and ultraﬁlter extensions seem to have ﬁrst been isolated when modal lo-
gicians started investigating modal expressivity over frames in the 1970s (along
with generated submodels and bounded morphisms they are the four constructions
needed in the Goldblatt-Thomason theorem, which we discuss in the following
chapter). Neither construction is as useful as generated submodels and bounded
morphisms when it comes to proving completeness results, which is probably why
they weren’t noted earlier. However, both arise naturally in the context of modal
duality theory, cf. Goldblatt [190, 191]. Ultraﬁlter extensions independently came



120
2 Models
about in the model-theoretic analysis of modal logic, see Fine [140]; the name
seems to be due to van Benthem. The unraveling construction (that is, unwind-
ing arbitrary models into trees; see Proposition 2.15) is helpful in many situations.
Surprisingly, it was ﬁrst used as early as in 1959, by Dummett and Lemmon [125],
but the method only seems to have become widely known because of Sahlqvist’s
heavy use of it in his classic 1975 paper [388].
Vardi [434] has stressed the importance of the tree model property of modal
logic: the property that a formula is satisﬁable iff it is satisﬁable at the root of a
tree-like model. The tree model property paves the way for the use of automata-
theoretic tools and tableaux-based proof methods. Moreover, it is essential for
explaining the so-called robust decidability of modal logic — the phenomenon
that the basic modal logic is decidable itself, and of reasonably low complexity,
and that these features are preserved when the basic modal logic is extended by a
variety of additional constructions, including counting, transitive closure, and least
ﬁxed points.
We discussed two ways of building ﬁnite models: the selection method and
ﬁltration. However, the use of ﬁnite algebras predates the use of ﬁnite models:
they were ﬁrst used in 1941 by McKinsey [328]; Lemmon [302] used and extended
this method in 1966. The use of model-theoretic ﬁltration dates back to Lemmon
and Scott’s long unpublished monograph Intensional Logic [303] (which began
circulating in the mid 1960s); it was further developed in Segerberg’s An Essay in
Classical Modal Logic [396], which also seems to have given the method its name
(see also Segerberg [394]). We introduced the selection method via the notion of
ﬁnitely approximating a bisimulation, an idea which seems to have ﬁrst appeared
in 1985 in Hennessy and Milner [225].
The standard translation, in various forms, can be found in the work of a number
of writers on modal and tense logic in the 1960s — but its importance only became
fully apparent when the ﬁrst frame incompleteness results were proved. Thoma-
son [426], the paper in which frame incompleteness results was ﬁrst established,
uses the standard translation — and shows why the move to frames and validities
requires a second-order perspective (something we will discuss in the following
chapter). Thus the need became clear for a thorough investigation of the relation
between modal and classical logic, and correspondence theory was born. But al-
though other authors (notably Sahlqvist [388]) helped pioneer correspondence the-
ory, it was the work of Van Benthem [35] which made clear the importance of sys-
tematic use of the standard translation to access results and techniques from classi-
cal modal theory. The observation that at most two variables are needed to translate
basic modal formulas into ﬁrst-order logic is due to Gabbay [158]. The earliest
systematic study of ﬁnite variable fragments seems to be due to Henkin [223] in
the setting of algebraic logic, and Immerman and Kozen [246] study the link with
complexity and database theory. Consult Otto [355] for more on ﬁnite variable



2.8 Summary of Chapter 2
121
logics. Keisler [272] is still a valuable reference for inﬁnitary logic. A variety of
other translations from modal to classical logic have been studied, and for a wide
variety of purposes. For example, simply standardly translating modal logics into
ﬁrst-order logic and then feeding the result to a theorem prover is not an efﬁcient
way of automating modal theorem proving. But the idea of automating modal rea-
soning via translation is interesting, and a variety of translations more suitable for
this purpose have been devised; see Ohlbach et al. [351] for a survey.
Under the name of p-relations, bisimulations were introduced by Johan van Ben-
them in the course of his work on correspondence theory. Key references here are
Van Benthem’s 1976 PhD thesis [35]; his 1983 book based on the thesis [35]; and
[42], his 1984 survey article on correspondence theory. In keeping with the spirit
of the times, most of Van Benthem’s early work on correspondence theory dealt
with frame deﬁnability (in fact he devotes only 6 of the 227 pages in his book
to expressivity over models). Nonetheless, much of this chapter has its roots in
this early work, for in his thesis Van Benthem introduced the concept of a bisim-
ulation (he used the name p-relation in [35, 41], and the name zigzag relation in
[42]) and proved the Characterization Theorem. His original proof differs from
the one given in the text: instead of appealing to saturated models, he employs an
elementary chains argument. Explicitly isolating the Detour Lemma (which brings
out the importance of ultrapowers) opens the way to Theorems 2.75 and 2.76 on
deﬁnability and makes explicit the interesting analogies with ﬁrst-order model the-
ory discussed below. On the other hand, the original proof is more concrete. Both
are worth knowing. The ﬁrst published proof using saturated models seems to be
due to Rodenburg [382], who used it to characterize the ﬁrst-order fragment corre-
sponding to intuitionistic logic.
The back-and-forth clauses of a bisimulation can be adapted to analyze the ex-
pressivity of a wide range of extended modal logics (such as those studied in Chap-
ter 7), and such analyses are now commonplace. Bisimulation based characteriza-
tions have been given for the modal mu-calculus by Janin and Walukiewicz [249],
for temporal logics with since and until by Kurtonina and De Rijke [295], for
subboolean fragments of knowledge representation languages by Kurtonina and
De Rijke [296], and for CTL
 by Moller and Rabinovich [339]. Related model-
theoretic characterizations can be found in Immerman and Kozen [246] (for ﬁnite
variable logics) and Toman and Niwi´nski [430] (for temporal query languages).
Rosen [384] presents a version of the Characterization Theorem that also works
for the case of ﬁnite models; the proof given in the text breaks down in the ﬁnite
case as it relies on compactness and saturated models.
But bisimulations did not just arise in modal logic — they were independently
invented in computer science as an equivalence relation on process graphs. Park
[358] seems to have been the ﬁrst author to have used bisimulations in this way.
The classic paper on the subject is Hennessy and Milner [225], the key reference for



122
2 Models
the Hennessy-Milner Theorem. The reader should be warned, however, that just as
the notion of bisimulation can be adapted to cover many different modal systems,
the notion of bisimulation can be adapted to cover many different concepts of pro-
cess — in fact, a survey of bisimulation in process algebra in the early 1990s lists
over 155 variants of the notion [179]! Our deﬁnitions do not exclude bisimulations
between a model and itself (auto-bisimulations); the quotient of a model with re-
spect to its largest auto-bisimulation can be regarded as a minimal representation
of this model. The standard method for computing the largest auto-bisimulation is
the so-called Paige-Tarjan algorithm; see the contributions to Ponse, de Rijke and
Venema [364] for relevant pointers and surveys.
More recently, bisimulations have become fundamental in a third area, non-well
founded set theory. In such theories, the axiom of foundation is dropped, and sets
are allowed to be members of themselves. Sets are thought of as graphs, and two
sets are considered identical if and only if they are bisimilar. The classic source for
this approach is Aczel [2], who explicitly draws on ideas from process theory. A
recent text on the subject is Barwise and Moss [26], who link their work with the
modal tradition. For recent work on modal logic and non-well founded set theory,
see Baltag [19].
The name ‘m-saturation’ stems from Visser [443], but the notion is older: its ﬁrst
occurrence in the literature seems to be in Fine [140] (under the name ‘modally
saturated
2’). The concept of a Hennessy-Milner class is from Goldblatt [185] and
Hollenberg [239]. Theorem 2.62, that equivalence of models implies bisimilar-
ity between their ultraﬁlter extensions, is due to [239]. Chang and Keisler [89,
Chapters 4 and 6] is the classic reference for the ultraproduct construction; their
Chapters 2 and 5 also contain valuable material on saturated models. Doets and
Van Benthem [120] give an intuitive explanation of the ultraproduct construction.
The results proved in this chapter are often analogs of standard results in ﬁrst-
order model theory, with bisimulations replacing partial isomorphisms. The Keis-
ler-Shelah Theorem (see Chang and Keisler [89, Theorem 6.1.15]) states that two
models are elementarily equivalent iff they have isomorphic ultrapowers; a weak-
ened form, due to Doets and Van Benthem [120], replaces ‘isomorphic’ with ‘par-
tially isomorphic’. Theorem 2.74, which is due to De Rijke [109], is a modal ana-
log of this weakened characterization theorem. Proposition 2.31 is similar to char-
acterizations of logical equivalence for ﬁrst-order logic due to Ehrenfeucht [127]
and Fra¨ıss´e [149]; in fact, bisimulations can be regarded as the modal cousins of the
model theoretic Ehrenfeucht-Fra¨ıss´e games. We will return to the theme of analo-
gies between ﬁrst-order and modal model theory in Section 7.6 when we prove a
Lindstr¨om theorem for modal logic. See De Rijke [109] and Sturm [418] for further
work on modal model theory; De Rijke and Sturm [113] provide global counter-
parts for the local deﬁnability results presented in Section 2.6. One can also charac-



2.8 Summary of Chapter 2
123
terize modal deﬁnability of model classes using ‘modal’ structural operations only,
i.e., bisimulations, disjoint unions and ultraﬁlter extensions, cf. Venema [437].
Sources for the use of simulations in reﬁnement are Henzinger et al. [227] and
He Jifeng [252], and for their use in a database setting, consult Buneman et al. [74];
see De Rijke [106] for Theorem 2.78. The Safety Theorem 2.84 is due to Van
Benthem [47]. The text follows the original proof fairly closely; an alternative
proof has been given by Hollenberg [238], who also proves generalizations.
One ﬁnal remark. Given the importance of ﬁnite model theory, the reader may
be surprised to ﬁnd so little in this chapter on the topic. But we don’t neglect
ﬁnite model theory in this book: virtually all the results proved in Chapter 6 re-
volve around ﬁnite models and the way they are structured. That said, the topic
of ﬁnite modal model theory has received less attention from modal logicians than
it deserves. In spite of Rosen’s [384] proof of the Van Benthem characterization
theorem for ﬁnite models, and in spite of work on modal 0-1 laws (Halpern and
Kapron [211], Goranko and Kapron [197], and Grove et al. [206, 205]), ﬁnite
modal model theory is clearly an area where interesting questions abound.


