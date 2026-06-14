<!-- Source: Blackburn, de Rijke & Venema (2001). Modal Logic. Cambridge University Press. Chapter 7: Extended Modal Logic (pages 415-487). BibKey: Blackburn2001 -->


7
Extended Modal Logic
As promised in the preface, this chapter is the party at the end of the book. We’ve
chosen six of our favorite topics in extended modal logic, and we’re going to tell
you a little about them. There’s no point in offering detailed advice here: sim-
ply read these introductory remarks and the following Chapter Guide and turn to
whatever catches your fancy.
Roughly speaking, the chapter works it’s way from fairly concrete to more ab-
stract. A recurrent theme is the interplay between modal and ﬁrst-order ideas. We
start by introducing a number of important logical modalities (and learn that we’ve
been actually been using logical modalities all through the book). We then exam-
ine languages containing the since and until operators, and show that ﬁrst-order
expressive completeness can be used to show modal deductive completeness. We
then explore two contrasting strategies, namely the strategy underlying hybrid logic
(import ﬁrst-order ideas into modal logic, notably the ability to refer to worlds) and
the strategy that leads to the guarded fragment of ﬁrst-order logic (export the modal
locality intuition to classical logic). Following this we discuss multi-dimensional
modal logic (in which evaluation is performed at a sequence of states), and see that
ﬁrst-order logic itself can be viewed as modal logic. We conclude by proving a
Lindstr¨om Theorem for modal logic.
Chapter guide
Section 7.1: Logical Modalities (Basic track). Logical modalities have a ﬁxed in-
terpretation in every model. We introduce two of the most important (the
global modality, and the difference operator) and brieﬂy discuss Boolean
Modal Logic (a system which contains an entire algebra of diamonds).
Section 7.2: Since and Until (Basic track). We introduce the since and until op-
erators (and their stronger cousins, the Stavi connectives), discuss the ex-
pressive completeness results they give rise to, and use expressive com-
pleteness to prove deductive completeness.
415



416
7 Extended Modal Logic
Section 7.3: Hybrid Logic (Basic track). Hybrid languages are modal languages
which can refer to worlds. They do so using atomic formulas called nom-
inals which are true at exactly one world in any model. We introduce the
basic hybrid language and discuss its completeness theory.
Section 7.4: The Guarded Fragment (Advanced track). As is clear from the stan-
dard translation, modal operators perform a ‘guarded’ form of quantiﬁca-
tion across states. What happens when this idea is exported to ﬁrst-order
logic and generalized? This section provides some answers.
Section 7.5: Multi-Dimensional Modal Logic (Advanced track). By viewing as-
signments as possible worlds and quantiﬁers as diamonds, one can treat
ﬁrst-order logic itself as a modal formalism. In fact, orthodox Tarskian
semantics for ﬁrst-order logic provides a prime example of multi-dimen-
sional modal logic: formulas are evaluated at a sequence of points.
Section 7.6: A Lindstr¨om Theorem for Modal Logic (Advanced track). As a fa-
mous theorem due to Lindstr¨om tells us, any logic satisfying complete-
ness, compactness, and L¨owenheim Skolem is essentially ﬁrst-order logic.
Is there an analogous abstract characterization of modal logic?
7.1 Logical Modalities
Pure ﬁrst-order logic has a signiﬁcant expressive weakness: it’s not strong enough
to express the concept of equality in arbitrary structures. But because equality is
such an important relation, logicians introduce a special binary relation symbol
(namely =) and stipulate that it denotes the equality relation. As the interpretation
of = is ﬁxed, and as the relation it denotes is so fundamental, the equality symbol
is called a logical predicate.
Logical modalities trade on the same idea. Are there important relations which
ordinary modal languages cannot express? Very well then: let’s add new modal-
ities and stipulate that they be interpreted by the relation in question.
In this
section we’ll discuss two of the most important logical modalities: the global
modality (which is interpreted by the relation
W

W) and the difference oper-
ator (which is interpreted by
6=, the inequality relation). We’ll also make a few
remarks about Boolean Modal Logic (BML), a system containing an entire family
of logical modalities.
But before going any further, let’s get one thing absolutely clear: we’ve been
using logical modalities all through the book. Here’s the simplest example. Sup-
pose we are working with the basic modal language. Now, for many purposes we
may be happy simply using
3 to talk about the relation
R — but sometimes we
may want to talk about
R
, the converse of
R, as well. Now, we know (see Exer-
cise 2.1.2) that this can’t be done in the basic modal language, so we have to add
a new backward-looking modality as a primitive; doing so, of course, gives us the



7.1 Logical Modalities
417
basic temporal language. But note: we don’t have to bring in the concept of time
to justify this extension. If a binary relation
R is important, its converse is likely
to be too — so it’s simply common sense to consider adding a diamond for
R
. In
short, the ‘temporal operator’
P is really a logical modality.
The other important example is PDL. To motivate PDL we told a story about pro-
grams and transition systems — but a more abstract motivation is not only possible,
it’s more satisfying. The point is this. As soon as we ﬁx a collection of relations
R
, regular algebra is staring us in the face: we can combine these relations using
union and composition, and form transitive closures. Any model containing the
initial
R
 relations implicitly contains many other interesting relations as well —
so it’s natural to add extra modalities to deal with them explicitly, and doing so
yields PDL. As this example shows, we can go way beyond the idea of adding a
single new logical modality: we can add an entire algebra of diamonds. We’ll see
another example of this when we discuss BML.
The global modality
Throughout the book we’ve emphasized the locality of modal logic, and for many
purposes local languages are ideal. For example, suppose we’re working with a
modal language for talking about computer networks, and in this language
 means
Server 1 is active and
 means Server 2 is active. Then we can
check whether the network makes it possible for Server 1 to be active by check-
ing whether
 is satisﬁable, and we can check whether it is possible for Server
2 to be inactive by testing for the satisﬁability of
: .
But suppose we want to know if whenever Server 1 is active, then so is
Server 2. There’s no obvious way to test this. Testing for the satisﬁability
of

!
 does not answer this question: if

!
 is satisﬁable, this only means
that there is a state where either
 is false or
 is true. We want to know whether
every state that makes
 true is also a state that makes
 true. This is clearly a
global query. What are we to do?
Here’s an elegant answer: enrich the language language with the global modal-
ity. To keeps things simple, suppose we’re working in the basic modal language
over some ﬁxed choice of proposition letters; let’s call this language ML(3). We’ll
now add a second diamond, written E, and call the resulting language ML
(3; E
).
The interpretation of E is ﬁxed: in any model
M
=
(W
;
R
;
V
), E must be inter-
preted using the relation
W

W. That is:
M;
w
 E
 iff there is a
u
2
W such that
M;
u

:
Thus E scans the entire model for a state that satisﬁes
. Its dual A
:=
:E
: has
the following interpretation:
M;
w
 A
 iff
M;
u

; for all
u
2
W.



418
7 Extended Modal Logic
That is, A
 asserts that
 holds at all points in the model. In effect, A brings the
metatheoretic notion of global truth in a model down into the object language: for
any model
M, and any formula
, we have that
M

 iff A is satisﬁable in
M. We’ll call E the global diamond, and A the global box. When it’s irrelevant
whether we mean E or its dual, we’ll simply say global modality.
It should now be clear how to handle the computer network problem: to test
whether Server 2 is active whenever Server 1 is, we test the satisﬁability
not of

!
 , but of A(
!
 
). This query has exactly the global force required.
Well — this looks appealing. But what are the properties of this (obviously
richer) new language? Maybe introducing the global modality destroys the prop-
erties that make model logic attractive in the ﬁrst place! We’ve made an important
change, and we need to take a closer look at the consequences.
Now, we could begin by discussing the sublanguage ML(E) — but this is not
very interesting (it’s easy to see that E is just an S5 modality). Anyway (as our
server example shows) the main reason for adding logical modalities is to have
them available as additional tools. So the real question is: what does ML(3; E
)
offer that ML
(3) doesn’t? The most obvious answer is expressivity. Let’s ﬁrst
consider expressivity at the level of frames:
(R
=
W
2)
Ep
!
3p
(R
6=
?)
E3>
(9x8y
:R
xy)
E2
?
(8x9y
R
y
x)
p
! E
3p
(jW
j
=
1)
Ep
!
p
(jW
j

n)
V
n+1
i=1 E
p
i
!
W
i6=j E
(p
i
^
p
j
)
(R is trichotomous)
(p
^
2q
)
! A(q
_
p
_
3p)
(R
 is well-founded) A(2p
!
p)
!
p
None of the frame classes listed is deﬁnable in ML
(3), but (as we ask the reader
to check in Exercise 7.1.1) the ML
(3; E) formulas to their right do deﬁne the cor-
responding property.
Where does this extra frame expressivity come from? From trivializing the no-
tion of generated submodel (generating on
W

W always yields
W

W) and
rendering inapplicable the notion of disjoint union (for any disjoint frames
(W
;
R
)
and
(W
0
;
R
0
),
(W

W
)
]
(W
0

W
0
)
6=
(W
]
W
0
)

(W
]
W
0
)). By insisting
that E be interpreted using
W

W, we’ve trashed two of the classic modal preser-
vation results and thereby bought ourselves more expressivity. How much more?
For ﬁrst-order deﬁnable frame classes, the answer is elegant:
Theorem 7.1 A ﬁrst-order deﬁnable class of frames is deﬁnable in ML(3; E
) iff it
is closed under taking bounded morphic images, and reﬂects ultraﬁlter extensions.



7.1 Logical Modalities
419
This is exactly the Goldblatt-Thomason Theorem — minus closure under disjoint
unions and generated subframes.
There is also a gain of expressivity at the level of models (the server example
makes this clear, and we already know from Section 2.1 that the global modality
is not deﬁnable in the basic modal language). Moreover, we can measure the gain
using our old friends: bisimulations. It’s an easy exercise to adapt the deﬁnition
of bisimulation for the basic modal language to ML
(3; E), and a rather more de-
manding one to prove a van Benthem style characterization result for the language.
The reader is asked to attend to these matters in Exercises 7.1.3 and 7.1.4.
What about completeness? The set of valid ML
(3; E
) formulas can be axioma-
tized as follows. Take the minimal normal logic in
3 and E (that is, apply Deﬁni-
tion 4.13 to this two-diamond similarity type), and add the following axioms:
(reﬂexivity)
p
! E
p
(symmetry)
p
! AEp
(transitivity) EE
p
! E
p
(inclusion)
3p
! E
p
Note that ﬁrst three axioms are the familiar T, B, and 4 axioms (written in E and A
rather than
3 and
2). We discussed Inclusion in Example 1.29(4). We’ll call this
logic
K
g.
Theorem 7.2 K
g is strongly complete with respect to the class of all frames.
This theorem says that to lift the minimal logic K (for the basic modal language)
to ML
(3; E), we need merely treat the global modality as a normal operator that
satisﬁes four further axioms. In fact, we can lift any canonical ML
(3) logic in
this way. If
K  is a normal modal logic in ML
(3), let
K
g
  be the normal modal
logic in ML(3; E
) obtained by treating E as a normal operator and adding the four
axioms listed above. Then:
Theorem 7.3 Let
  be a set of ML(3) formulas, and let F be the class of frames
that
  deﬁnes. If
K  is canonical, then
K
g
  is strongly complete with respect to
F.
Proof. Let
M
=
(W
;
R
3
;
RE
;
V
) be the canonical model for
K
g
 . Note that as
K 
K
g
 , we have that
(W
;
R
3
) belongs to
F, for
K  is canonical. Indeed, any
generated subframe of
(W
;
R
3
) belongs
F, for validity in the basic modal language
is closed under generated subframes.
Given a
K
g
 -consistent set of sentences
, use Lindenbaum’s Lemma to ex-
pand it to an
K
g-MCS

+. By the Canonical Model Theorem,
M;

+

.
Now, (reﬂexivity), (symmetry), and (transitivity) are canonical formulas, thus
RE
is an equivalence relation. And although there is no guarantee that
RE is
W

W,



420
7 Extended Modal Logic
this is easy to correct: let
M
0
=
(W
0
;
R
0
3
;
R
0
E
;
V
) be the submodel of
M gener-
ated by

+ using the
RE-relation. Then
R
0
E
=
W
0

W
0, so we have the global
relation we need. Furthermore, because of Inclusion,
R
3

RE, thus
M
0 is also a
generated submodel of
M with respect to
R
3, hence
M
0
;

+

. It only remains
to observe that (by our initial remarks)
(W
0
;
R
0
3
) is in
F, hence the result follows.
(Theorem 7.2 is the special case in which
 =
?.)
a
Example 7.4 Suppose we’re working with ML(3) over transitive frames (so the
relevant logic is K4, which is canonical). Now, we may want to state global con-
straints on models, or insist that certain information holds somewhere or other, and
of course we can do this if we add the global modality. But how do we obtain a
complete logic for transitive frames in the enriched language?
Simply enrich K4 by treating the global modality as a normal operator and
adding the (reﬂexivity), (transitivity), (symmetry), and (inclusion) axioms. Doing
so yields K
g4, and by the theorem just proved this logic is strongly complete with
respect to the class of transitive frames.
a
What about decidability and complexity? We brieﬂy met the global modality in
Section 6.5, and we saw that its global reach makes it possible to force the exis-
tence of gridlike models. This led to undecidability results for languages contain-
ing several diamonds, and it’s not difﬁcult to adapt these arguments to ﬁnd frame
classes with decidable ML(3) logics and undecidable ML
(3; E
) logics (we give
such an example in Exercise 7.1.5). Moreover, although undecidability does not
strike over the class of all frames, K
g is probably more complex than K, for K
g has
an EXPTIME-complete satisﬁability problem (the reader was asked to prove this in
Exercises 6.8.1 and 6.8.2) while K is PSPACE-complete (see Section 6.7). On the
other hand, there is a rather nice transfer result concerning the ﬁltration method:
if we can prove the decidability of a ML
(3) logic by using ﬁltrations to establish
establish the strong ﬁnite frame property, then we can also do so after adding the
global modality. For example, it follows that the logic K
g4 (see Example 7.4) is
decidable. We’ll state and prove a stronger version of this result when we discuss
the difference operator.
All in all, the global modality is a strikingly natural extension of modal logic —
and at ﬁrst glance this seems surprising. How can something so obviously global
blend so well with the locality of modal logic? Basically, because the enriched
language still takes an internal perspective on relational structure. Although we
now have a global operator at our disposal, we still place formulas inside models
and evaluate them at a particular state. To put it another way, the intuition that
a modal formula is an automaton scanning accessible states is remarkably robust:
even if we add a special automaton programmed to regard all states as accessible,
we retain much of the characteristic ﬂavor of ordinary modal logic.



7.1 Logical Modalities
421
A lot more could be said about the global modality. For a start, it’s natural
when viewed from an algebraic perspective (it gives rise to discriminator vari-
eties). Moreover, the global modality can be added to many richer modal systems,
including PDL and the hybrid and multi-dimensional logics discussed later in the
chapter, often without raising the computational complexity (for example PDL is
EXPTIME-complete, and adding E doesn’t change this). But for more information
the reader will have to consult the Notes and Exercises, for it’s time to discuss an
even more powerful logical modality.
The difference operator
At the bottom of every toolbox lies a heavy cast-iron hammer. It’s not the sort
of tool we use every day — for delicate jobs it’s inappropriate, and we may feel
slightly embarrassed about using it at all. Still, there’ll always come a time when
something simply won’t budge, and then we ﬁnd ourselves reaching for it. Think
of the difference operator as that hammer.
Once again, we’ll start with ML
(3). We’ll add a second diamond D, the differ-
ence operator, and call the resulting language ML
(3; D). The interpretation of D
is ﬁxed: in any model
M
=
(W
;
R
;
V
), D must be interpreted using the inequality
relation
6=. That is:
M;
w
 D iff there is a
u
6=
w such that
M;
u

:
Thus the difference operator scans the entire model looking for a different state that
satisﬁes
. Its dual D
:=
:D
: has the following interpretation
M;
w
 D iff
M;
u

 for all
u
6=
w.
In what follows we discuss ML
(3; D
), but the sublanguage ML
(D) is quite inter-
esting in its own right, and we ask the reader is asked to explore it in Exercise 7.1.6.
Using the difference operator, we can deﬁne the global modality: E
:=

_D
.
Thus all our earlier examples of frame classes deﬁnable in ML
(3; E
) are deﬁnable
in ML
(3; D) too. But ML
(3; D
) can deﬁne even more:
(irreﬂexivity)
3p
! D
p
(antisymmetry)
(p
^
:D
p)
!
2(3p
!
p)
(9xy
(x
6=
y
))
D>
(jW
j
>
n)
A(
W
1in
p
i
)
! E
W
1in
(p
i
^ D
p
i
)
None of these frame classes is closed under bounded morphic images hence (by
Theorem 7.1) none of them is deﬁnable in ML
(3; E); but it is easy to see that the
listed ML
(3; D) formulas successfully capture them. Incidentally, we have already
seen that ML
(3; E
) can deﬁne
jW
j

n, thus as ML
(3; D
) can deﬁne
jW
j
>
n,
the difference operator can count states, at least as far as frames are concerned; in



422
7 Extended Modal Logic
Exercise 7.1.7 we ask the reader to investigate whether it can count over models as
well. Furthermore, note the
p
^
:D
p antecedent in the deﬁnition of antisymmetry.
This is only true when
p is true at exactly one state in the model: in effect we are
using the power of D to force
p to act as ‘name’ for a state; we’ll put this power to
good use shortly.
What about completeness? The set of valid ML
(3; D) formulas can be axioma-
tized as follows. Take the minimal normal logic in
3 and D, and add the following
axioms:
(symmetry)
p
! DD
p
(pseudo-transitivity) DD
p
!
(p
_ D
p)
(D-inclusion)
3p
!
p
_ Dp
We’ll call this logic
K
d. Now, it’s not particularly difﬁcult to prove the complete-
ness of
K
d (we ask the reader to do so in Exercise 7.1.8) — but it’s harder than
with
K
g (we have to do more than simply take a generated submodel) and the
result doesn’t extend to stronger logics so easily (there’s no obvious analog of The-
orem 7.3). Moreover, it’s easy to ﬁnd frame incompleteness results, indeed we can
even ﬁnd them in the sublanguage ML(D)! Things aren’t looking too good . . .
Enter the hammer. When we discussed rules for the undeﬁnable (Section 4.7) we
learned that proof rules which rely on ‘names’ can lead to general frame complete-
ness results. And as we noted above, the difference operator is powerful enough
to simulate state names, thus we can formulate the following rule of proof (the
D-rule):
`
(p
^
:D
p)
!

`

(Here
p is a proposition letter that doesn’t occur in
. The intuitions underlying
this rule are analogous to those underlying the IRR rule discussed in Section 4.7,
and we’ll leave it to the reader to verify that it preserves validity.) And now for a
remarkable result. The
D-rule neatly meshes with our earlier work on Sahlqvist
formulas to yield one of the most general completeness results known in modal
logic, the D-Sahlqvist theorem.
Here we only formulate a version in the basic temporal language. Consider the
language with operators
F,
P and D; let, for a set
 of axioms in this logic,
K
td

be the normal modal logic generated by the axioms of basic temporal logic, the
D-axioms and D-rule given above, and the formulas in
.
Theorem 7.5 Let
 be a collection of Sahlqvist formulas in the basic temporal
language. Then
K
td
 is strongly sound and complete with respect to the class of
bidirectional frames deﬁned by (the ﬁrst-order frame correspondents of) the axioms
in
.



7.1 Logical Modalities
423
Proof. We will prove weak completeness only. The ﬁrst step of the proof is to
prove the existence of a collection
W of maximal consistent sets such that
(i) each
  in
W contains a name, that is, a formula of the form

^
:D,
(ii) for each
  in
W and each formula
F
 
2
 , there is a
 in
W such that
  and
 are in the canonical accessibility relation
R
c
F for
F; and likewise,
for the operators
P and D.
(iii) for each pair of distinct points
  and
 in
W we have
R
c
D
 .
All of this can be proved in the style of Proposition 4.71.
It easily follows from (i) and (iii) above that
R
c
D is the inequality relation on
W.
But then the model on
W given by
V
(p)
=
f 2
W
j
p
2
 g is named; that
is, for every point in the model there is a formula which is true only at this point,
see Deﬁnition 4.76. However, condition (ii) allows us to prove a Truth Lemma
which implies that all axioms of the logic are true throughout the model. But then
it follows from Theorem 4.77 that the Sahlqvist axioms are valid on the underlying
frame as well.
a
The pinch of Theorem 7.5 lies in the fact that the ﬁrst-order frame correspondents
it mentions use inequality for the ‘relation symbol’ referring to the accessibility
relation of D. This means that we can automatically axiomatize frame properties
like irreﬂexivity or antisymmetry. The reader doubt the usefulness of this: isn’t
the logic of the class of irreﬂexive frames is identical to the logic of the class of
all frames? True, but this may change when we consider irreﬂexivity in addition
with other properties. Conditions like irreﬂexivity, undeﬁnable in themselves, may
nevertheless have ‘side effects’ so to speak. What we mean is that there are frame
classes
K such that the logic of
K differs from the logic of the irreﬂexive frames in
K. In such cases the above theorem can be of tremendous help.
In a surprisingly large number of cases we ﬁnd ourselves in the situation that
over a certain class of frames, the difference operator is deﬁnable in the underlying
modal language. For example, over the class of strict linear orders, the temporal
formula
F
p
_
P
p holds at a point if and only if
p holds at a different point. In
general, we say that a formula
Æ
(p) acts as D on a frame
F if
F

Æ
(p)
$ Dp; if
Æ
(p) acts as the difference operator on every frame in a class
K then we say that
Æ
deﬁnes D over
K.
Deﬁnability of the difference operator is of great use for axiomatizability, as the
following result shows. For a formula
Æ
(p), let
K
tÆ
 be the ‘Æ’-version of
K
td,
that is, the logic in the language without the D-operator obtained by replacing, in
all axioms and derivation rules of
K
td every formula D with
Æ
().
Theorem 7.6 Let
 be a collection of Sahlqvist formulas. Then
K
tÆ
 is strongly
sound and complete with respect to the class of those bidirectional frames on which
 is valid and on which
Æ acts as the difference operator.



424
7 Extended Modal Logic
In the section on multi-dimensional modal logic we will see an application of this
theorem; for a proof, we refer the reader to Exercise 7.1.9. We will examine another
name-driven proof rule (called PASTE) in detail when we discuss hybrid logic. First
we turn to decidability issues concerning the difference operator.
ML(3; D
) is a strong language. As it can deﬁne the global modality,
K
d must
have an EXPTIME-hard satisﬁability problem (in fact, the problem is EXPTIME-
complete; see Exercise 7.1.10) and it is even easier to ﬁnd undecidable logics
than in ML
(3; E
). Nonetheless, decidability is often retained. In particular, if
the ML
(3) logic of a class of frames can be proved decidable by using a ﬁltration
argument to establish the strong ﬁnite frame property, then the ML
(3; D
) logic of
that same frame class can be proved decidable in the same way. Let’s prove this.
Deﬁnition 7.7 Let
 be a logic, and let
F be a class of frames for
. We say that
 admits ﬁltrations on
F if for any model
M which is based on a frame in F, and
for any ﬁnite subformula closed set
 of ML
(3) formulas, there is a ﬁltration
M
f
of
M through
 which is based on a frame in
F.
a
Theorem 7.8 Suppose that
F is a class of frames, and that

F (the set of all
ML
(3)-formulas valid on
F) admits ﬁltrations on
F. Then the logic

d
F (the set
of all ML(3; D
)-formulas valid on
F) has the strong ﬁnite frame property with
respect to
F.
Proof. Let
 be a ML
(3; D)-formula satisﬁable in a model
M
=
(W
;
R
;
V
) of
which the underlying frame
(W
;
R
) is in
F. We want to show that
 is satisﬁable in
an
F-frame of bounded size.
Let
 be the set of subformulas of
. First consider the relation

 which holds
between two points if they satisfy the same formulas in
. As the points of our
ﬁnite model we would like to take the equivalence classes of this relation but this
would not work out well (it is instructive to see how the proof of the ﬁltration
lemma fails in the inductive step of the difference operator). The key idea of the
proof of the theorem is to solve this problem by splitting each equivalence class
in two parts — unless the original class is a singleton. To achieve this we add a
new proposition letter
d to the language and we make
d true at exactly one point of
each equivalence class. We would then like to ﬁltrate the new model according the
equivalence relation


[fdg.
There is still a problem however: we can only guarantee that the underlying
frame of the ﬁltrated model is in
F if we ﬁltrate through a set of ML(3) formulas.
But
 may contain formulas with occurrences of D. In order to get rid of these, we
employ a little technical trick. For every formula of the form D in
, choose a
distinct propositional variable
q
 that does not occur in any formula in
. Let
V
0 be
the valuation that differs from
V , if at all, only in that
V
0
(q
 
)
=
fw
j
M;
w
 D
 
g
and that
V
0
(d) is as indicated above. Let
M
0 be the model
(W
0
;
R
0
;
V
0
).



7.1 Logical Modalities
425
Now deﬁne the set

0 as follows. It is not difﬁcult to see that for every

2
 there is a unique ML
(3) formula

0 such that
 can be obtained from

0 by
replacing in

0 every proposition letter
q
 by D . Put

0
=
f
0
j

2

g
[
fd;
q
 
j D
 
2

g:
Observe that the formulas in

0 are D-free and that

0 is subformula closed. The
model
M
0 is (or can be seen as) an ML
(3)-model satisfying
M;
s

 iff
M
0
;
s


0
(7.1)
for all formulas
 in
. Let


0 hold between two points iff they satisfy the same
formulas in

0; it is easy to see that every

-equivalence class
jsj splits into
either one or two


0-equivalence classes, depending on whether
jsj has one or
more elements.
In any case, it follows from the assumption in the theorem that there is a ﬁltration
M
f through

0 which is based on a frame in
F. Note that by deﬁnition, the points
of
M
f are the


0-equivalence classes. We claim that this model
M
f satisﬁes the
following property for all ML
(3; D
)-formulas
 in
 and all states
s in
M:
M;
s

 iff
M
f
;
jsj

:
(7.2)
From this, the theorem is almost immediate.
The proof of (7.2) proceeds by a formula induction of which we omit the stan-
dard inductive steps concerning the boolean operators; the clauses for
3 are fairly
easy as well — but note that for one direction, one needs (7.1). For the case that
 is of the form D
 we also omit the easy right-to-left direction of (7.2). For the
other direction, suppose that
M;
s
 D . Then there is a point
s
0
6=
s such that
M;
s
0

 . If
jsj and
js
0
j are distinct then we are ﬁnished, so suppose otherwise.
But from
s


0
s
0 it follows on the one hand that
M;
s

d iff
M;
s
0

d, and
on the other hand, that
s and
s
0 belong to the same

-equivalence class. Since
we chose exactly one point in each

-class to satisfy
d, this means that neither
s nor
s
0 can be this special point. Hence, there must be another point
s
00 in this

-equivalence class which does make
d true. From
s
0


s
00 it follows that
M;
s
00

 , so by the inductive hypothesis we have that
M
f
;
js
00
j

 . But
js
00
j is
distinct from
jsj since
d holds at
s
00 and not at
s. This gives that
M
f
;
jsj
 D , as
required.
a
How does decidability follow? Any logic
 that admits ﬁltrations on F has the
strong ﬁnite frame property with respect to F — so if F is recursive we can apply
Theorem 6.7 and conclude that

F is decidable. But then by the result just proved,
we know that

d
F also has the strong ﬁnite frame property with respect to F, so we
can apply the model enumeration idea underlying the proof of Theorem 6.7 to for-
mulas of the richer languages. As D is always interpreted by the inequality relation,



426
7 Extended Modal Logic
and as this relation is obviously computable on ﬁnite structures, the decidability of

d
F follows.
A great deal more could be said about the difference operator (in particular,
bisimulations are easily adapted to cope with D, and a van Benthem style charac-
terization result is forthcoming; see Exercises 6.8.1 and 6.8.2) but it’s time to take
a brief look at a system containing a whole family of logical modalities.
Boolean modal logic
As we have remarked, as soon as we ﬁx a collection of relations
R
, we can form
the regular algebra over this base; building an algebra of diamonds corresponding
to these leads to PDL. But an even more obvious algebra demands attention: we can
also form the boolean algebra over base relations
R
. Why not deﬁne an algebra
of diamond corresponding to
1,
 ,
\, and
[? Doing so leads to Boolean Modal
Logic (BML).
We deﬁne the language of BML as follows. As with PDL, we ﬁx a set of primitive
relation symbols
a,
b,
c, . . . , and in addition a distinguished relation symbol
1.
From these we build complex relations using the relation constructors
 ,
\ and
[:
that is, if
 and
 are relation symbols, then so are
:,

\
, and

[
. BML
is the modal language containing a diamond
hi for each relation symbol
. In
principle we can interpret BML on any model of appropriate similarity type — that
is triples
M
=
(W
;
fR

j
 is a relation symbol
g;
V
) — but most such models
are inappropriate. We are only interested in boolean models, the models in which
R
1
=
W

W, and such that, for all relation symbols
 and
,
R
 
=
R
 (that
is,
(W

W
)
n
R
),
R
\
=
R

\
R
, and
R
[
=
R

[
R
.
BML is an expressive language — for a start, it contains the global modality
— and it may seem that we’ve bitten off more than we can chew. While the
[
constructor is well behaved (in particular
F

h
[

ip
$
hi
_
h
ip iff
R
[
=
R

[
R
), the
\ constructor is difﬁcult to work with. However, as we will now
see, with the help of the
  constructor we can get an exact grip on the relations of
interest.
First we deﬁne the following operator (often called window): for any relation
symbol
:
[
jj
]
:=
[ ]::
That is:
M;
w

[
jj
] iff
8u(M;
u


)
R

w
u):
Window is an extremely natural operator — once you’ve seen it, you wonder how
you ever managed without it. For example, if we read
[] as saying that all
executions of program
 lead to a
 state, then
[
jj
] says that only executions of



7.1 Logical Modalities
427
program
 can lead to a
 state, and it has other useful readings too (see the Notes)
But what concerns us here is the following result: window allows very smooth
deﬁnitions of the relations we are interested in.
Proposition 7.9 Let
F be a frame
(W
;
fR

j
 is a relation symbol
g). Then:
(i)
F

[ ]p
$
[
jj
]:p iff
R


R

(ii)
F

[]:p
$
[
j
 j
]p iff
R


R

(iii)
F

[
j
\

j
]p
$
[
jj
]p
^
[
j
j
]p iff
R
\
=
R

\
R
.
Proof. We prove the third claim. The right to left direction is trivial. For the left
to right direction, assume that
F

[
j
\

j
]p
$
[
jj
]p
^
[
j
j
]p. We need to show
that
R
\
=
R

\
R
. To see that
R
\

R

\
R
, suppose that
R
\
w
u, and
let
V be any valuation on
F such that
V
(p)
=
fug. Then
(F;
V
);
w

[
j
\

j
]p.
As
F

[
j
\

j
]p
$
[
jj
]p
^
[
j
j
]p we have
(F;
V
);
w

[
jj
]p
^
[
j
j
]p. But
u is the
only point satisfying
p, hence
R

w
u and
R

w
u. A similar argument shows that
R

\
R


R
\.
a
In a sense, the relations are divided into two kingdoms: the ordinary
[] modalities
govern relations built with
[, the widow modalities
[
jj
] govern the relations built
with
\, and the
  constructor acts as a bridge between the two realms. Moreover
the bridging function of
  also ﬁnds expression in a new rule of proof, BR. Unlike
the other additional rules discussed in this book, BR is not name-driven:
`
[]p
!
([
]p
!
[
]p)
`
[]p
!
([
j
j
]:p
!
[
j
j
]:p)
(BR
)
While it is possible to prove a completeness result for BML without using BR, its
use leads to an elegant axiomatization, for it enables us to thread negations through
the structured modalities.
A ﬁnal surprise is in store. In Theorem 6.31 we showed that the fragment con-
taining the
\ constructor and the global modality was undecidable over determin-
istic frames. Nonetheless, the minimal logic in BML actually turns out to be de-
cidable. All in all, BML is a fascinating system. For more information, see the
Notes.
Exercises for Section 7.1
7.1.1 We listed numerous frame conditions deﬁnable in ML
(3; E
) and ML(3; D
) which
were not deﬁnable in ML(3). Show that these deﬁnability claims are correct.
7.1.2 Show that ML
(3; E
) validity is preserved under bounded morphisms and reﬂects
ultraﬁlter extensions. (That is, show the easy direction of the Goldblatt-Thomason style
result for ML
(3; E
) stated in Theorem 7.1.) Can you prove the (far more demanding)
converse?



428
7 Extended Modal Logic
7.1.3 Extend the standard translation to the global modality and the difference opera-
tor. Extend the notion of bisimulation for the basic modal language to ML(3; E
) and
ML(3; D
), and show prove that your deﬁnition leads to an invariance result.
7.1.4 Building on the previous exercise, characterize the expressivity of ML
(3; E
) and
ML(3; D
) over models.
7.1.5 Let 2-3 be the class of frames
(W
;
R
) such that every state has 2
R-successors, and
3
R-successors of
R-successors. First show that the satisﬁability problem in ML(3) over
2-3 is decidable (note: this cannot be proved using a ﬁltration argument). Then show that
the satisﬁability problem in ML(3; E
) over 2-3 is undecidable. (It may be helpful to note
that this exercise is related to Exercise 6.5.2.)
7.1.6 Show that a class of frames is deﬁnable in ML
(D) if and only if it is deﬁnable in
the ﬁrst-order language over
= (that is, the ﬁrst-order language of equality). What is the
complexity of the satisﬁability problem for ML
(D)?
7.1.7 Clearly we can deﬁne in ML
(3; D
) an operator
Q with the following satisfaction
deﬁnition: for any model
M, any state
w in
M, and any formula
,
M;
w
j
=
Q iff there
is exactly one state
u in
M such that
M;
u
j
=
Q. But it is also possible in to deﬁne
modalities
Q
2
,
Q
3
,
Q
3
, and so on, that are satisﬁed when
 holds at precisely
Q
n
states
(n

2) in the model?
7.1.8 Show that
K
d is complete with respect to the class of all frames. (No need to try
anything fancy here — just ﬁddle with the canonical model.)
7.1.9 Prove Theorem 7.6. That is, let
 be a collection of Sahlqvist formulas in the basic
modal language. Show that
K
tÆ
 is strongly sound and complete with respect to the class
of those frames on which
 is valid and on which
Æ acts as the difference operator.
(Hint: use an auxiliary logic
K
tÆ

+ in the temporal language expanded with the difference
operator. Simply deﬁne this logic as having both the D and the
Æ versions of the D-axioms
and rules. Now ﬁrst use Theorem 7.5 to prove that this logic is sound and strongly complete
with respect to the class of
-frames on which
Æ acts as the difference operator. Then,
prove that
K
tÆ

+ is conservative over
K
tÆ
; that is, show that for every purely temporal
formula
, we have that
 belongs to
K
tÆ
 iff it belongs to
K
tÆ

+.)
7.1.10 Use an elimination of Hintikka sets argument to show that the
K
d satisﬁability
problem is solvable in EXPTIME.
7.2 Since and Until
The modal operators considered in previous chapters all have satisfaction deﬁni-
tions involving only existential or only universal quantiﬁers. In this section we
look at a popular temporal logic whose operators are based on modalities with
more complex satisfaction deﬁnitions:
S (since) and
U (until). The main rea-
son for considering these modalities is, again, to achieve an increase in expressive
power. We’ll ﬁrst give some examples demonstrating why the increased expres-
sivity is useful. We’ll then learn that (over Dedekind complete frames) we have



7.2 Since and Until
429
actually achieved expressive completeness: any expression in the ﬁrst-order corre-
spondence language (in one free variable) has an equivalent in the modal language
in
S and
U. Finally, we’ll show that this (ﬁrst-order) expressive completeness leads
to (modal) deductive completeness.
Basic deﬁnitions
The basic operators needed for temporal reasoning seem to be
F and
P. These
allow us to say things like ‘Something good will happen’ and ‘Something bad has
happened.’
q
p
P
q,
F
p
-



?


?
But in several application areas this is not enough. For example, in the semantics of
concurrent programs one often needs to be able to express properties of executions
of programs that have the general format ‘Something good is going to happen, and
until that time nothing bad will happen.’ Or, more concretely:
p will be the case,
and until that time
q will hold:
. . . . . . . . . . . . . . . . . . .
p
q
-



?
U
(p;
q
)
Such properties are sometimes called guarantee properties in the computational
literature. To state them, the binary until operator
U can be used; its satisfaction
deﬁnition reads:
t

U
(;
 
) iff
there is a
v
>
t such that
v

 and for all
s with
t
<
s
<
v:
s

 
:
The mirror image of
U is the since operator
S:
t

S
(;
 
) iff
there is a
v
<
t such that
v

 and for all
s with
v
<
s
<
t:
s

 .
That’s the basic idea — but before going further, let’s make our discussion a little
more precise. The set of
S,
U-formulas is built up from a collection
 of proposi-
tion letters, the usual boolean connectives, and the binary operators
S and
U. The
mirror image of a formula
 is obtained by simultaneously substituting
S for
U
and
U for
S in
.



430
7 Extended Modal Logic
S,
U-formulas are interpreted on frames of the form
F
=
(T
;
<), where
T is a
set of time points and
< is a binary relation on
T.
U looks forward along
<, and
S looks backwards. We use the notation
(T
;
<) for frames (rather than our usual
(T
;
R
)) because here we are primarily interested in the temporal interpretation of
S and
U. In fact, will be working with frames
(T
;
<) such that
< is a Dedekind
complete order — more on this below. To emphasize our interest in the temporal
interpretation, we will often refer to frames as ﬂows of time. As usual, a valuation
is a function assigning subsets of
T to the proposition letters in the language.
How does the language in
S and
U relate to the basic temporal language? First,
observe that
F and
P are deﬁnable in the language with
S and
U: we can deﬁne
F

:=
U
(;
>),
P

:=
S
(;
>),
G
:=
:F
: and
H

:=
:P
:. Thus the
language with
S and
U is at least as strong as the basic temporal language. In fact,
it is strictly stronger. For a start, we saw in Exercise 2.2.4 that the basic temporal
language couldn’t deﬁne
U. Moreover, as the following proposition shows, even
if we restrict attention to models based on the real numbers, the basic temporal
language still isn’t strong enough to deﬁne
U.
Proposition 7.10
U is not deﬁnable over
(R
;
<) using
F and
P.
Proof. We will give two models that agree on all formulas in the language with
F and
P only, but that can be distinguished using the until operator. Consider the
following model
M
1 based on the reals:
. . . . . . . . . . .
. . . . .
. . . . .
. . . . .
0

U
(p;
q
)
5
4
3
2
1
0
 1
 2
 3
p
p
p
p
p
p
p
p
q
q
q
q
-

So,
V
1
(p)
=
fr
j
r
2
Zg, and
V
1
(q
)
=
f0g
[
fr
j
9n
2
N
(
 2n
 1
<
r
<
 2n)g
[
fr
j
9n
2
N
(2
n
<
r
<
2n
+
1)g.
Next, consider the model
M
2 given by the following picture:
. . . . . . . . . . .
. . . . .
. . . . .
. . . . .
0
6
U
(p;
q
)
5
4
3
2
1
0
 1
 2
 3
p
p
p
p
p
p
q
q
q
q
-

We leave it to the reader to show that the models
M
1 and
M
2 agree on all for-
mulas in
F and
P, but that
M
1
;
0

U
(p;
q
), whereas
M
2
;
0
6
U
(p;
q
) (see
Exercise 7.2.1).
a
So the temporal language in
S and
U is expressive — but just how expressive is
it? To answer such questions we need a correspondence language and a standard
translation of
S and
U into the correspondence language. Let
 be a collection of



7.2 Since and Until
431
proposition letters, and let
L
1
<
(), or simply
L
1
<, be the ﬁrst-order language with
unary predicate symbols corresponding to the proposition letters in
, and with
=
and
< as binary relation symbols. We use
L
1
<
(x) to denote the set of
L
1
< formulas
having one free variable
x. Note: this is the familiar correspondence language for
the basic temporal language, except that we are using
< rather than
R as the binary
relation symbol.
The standard translation
ST
x for the until operator
U is
ST
x
(U
(;
 
))
=
9z
(x
<
z
^
ST
z
()
^
8y
(x
<
y
<
z
!
ST
y
( 
))):
The standard translation of
S is the mirror image of that of
U. Observe that we need
3 variables to specify the translation of since and until! We only needed 2 variables
to specify the translation of the basic modal operators (see Proposition 2.49).
Let K be a class of models,
ML a modal or temporal language, and
L a classical
language. Then
ML is expressively complete over K, if every
L
1
<
(x)-formula has
an equivalent (over
K) in the modal language
ML. The study of expressive com-
pleteness is an important theme in temporal logics with since and until because of
the following remarkable result: the language with
S and
U is expressively com-
plete over the class of all Dedekind complete ﬂows of time (we will deﬁne this
class shortly). Moreover, below we will deﬁne an even richer temporal language
that is expressively complete for the class of all linear ﬂows of time. In the remain-
der of this section we will brieﬂy explain these expressive completeness results,
and use them to obtain a deductive completeness result for since and until over
well-ordered ﬂows of time.
Further preliminaries
A ﬂow of time is called Dedekind complete if every subset with an upper bound has
a least upper bound. The standard examples are the reals
(R
;
<) and the natural
numbers
(N
;
<). A ﬂow of time is well-ordered if every non-empty subset has a
smallest element; the canonical example here is
(N
;
<).
To arrive at our goal of axiomatizing the well-ordered ﬂows of time, we make a
detour through a still richer temporal language built using the Stavi connectives.
Deﬁnition 7.11 (The Stavi Connectives) To introduce the Stavi connectives we
need the notion of a gap. A gap of a frame
F
=
(T
;
<) is a proper subset
g

T
which is downward closed (that is,
t
2
g and
s
<
t implies
s
2
g), and which
does not have a supremum. One can think of a gap as a hole in a Dedekind-
incomplete ﬂow of time; see Figure 7.1 Now,
U
0
(;
 
) holds at a point
t if the
situation depicted in the above ﬁgure holds; that is, if
(i) there are a point
s and a gap
g such that
t
2
g and
s
=
2
g;
(ii)
 holds between
t and
g;



432
7 Extended Modal Logic
h
-

t
s
g
z
}|
{
z
}|
{
:
:
:
 
: 
 

Fig. 7.1. The Stavi connectives
(iii)
 holds between
s and
g; and
(iv)
: is true arbitrarily soon after
g.
S
0
(;
 
) is the mirror image of
U
0
(;
 
).
The above informal second-order deﬁnition (we quantify over gaps, and hence
over sets) can be replaced by a ﬁrst-order deﬁnition; see Exercise 7.2.2.
a
Theorem 7.12 (Expressive Completeness)
(i)
U,
S is complete over Dedekind complete ﬂows of time.
(ii)
U,
S,
U
0,
S
0 are complete over all linear ﬂows of time.
Next, we need an complete axiom system for the class of linear ﬂows of time:
Deﬁnition 7.13 Consider the following collection of axioms:
(A1a)
G(p
!
q
)
!
(U
(p;
r
)
!
U
(q
;
r
))
(A2a)
G(p
!
q
)
!
(U
(r
;
p)
!
U
(r
;
q
))
(A3a)
p
^
U
(q
;
r
)
!
U
(q
^
S
(p;
r
);
r
)
(A4a)
U
(p;
q
)
^
:U
(p;
r
)
!
U
(q
^
:r
;
q
)
(A5a)
U
(p;
q
)
!
U
(p;
q
^
U
(p;
q
))
(A6a)
U
(q
^
U
(p;
q
);
q
)
!
U
(p;
q
)
(A7a)
U
(p;
q
)
^
U
(r
;
s)
!
U
(p
^
r
;
q
^
s)
_
U
(p
^
s;
q
^
s)
_
U
(q
^
r
;
q
^
s)
(Aib)
the mirror images of (A1a)–(A7a)
(D)
(F
>
!
U
(>;
?))
^
(P
>
!
S
(>;
?))
(L)
H
?
_
P
H
?
(W)
F
p
!
U
(p;
:p)
(N)
D
^
L
^
F
>
a
Axioms (D), (L), (W), and (N) are discussed in Lemma 7.14 and Exercise 7.2.3
below. As to the other axioms, (A1a) and (A2a) can be viewed as counterparts of
the familiar distribution or K axiom
2(p
!
q
)
!
(2p
!
2q
). (A3a) captures
the fact that
U and
S explore relations that are each other’s converse. (A4a) and
(A5a) connect the current and the future point (at which something good is going
to happen) on the one hand with the points in between on the other hand. (A6a)



7.2 Since and Until
433
expresses transitivity of the ﬂow of time, and, ﬁnally, (A7a) forces the ﬂow of time
to be linearly ordered.
Lemma 7.14 Let
F be a linear ﬂow of time. Then
(i)
F
j
=
D iff
F is a discrete ordering.
(ii)
F
j
=
W
^
L iff
F is a well-ordering.
(iii)
F
j
=
W
^
N iff
F

=
(N
;
<).
The proof of Lemma 7.14 is left as Exercise 7.2.3.
Next, we deﬁne three axiom systems: B, BW, and BN. The set of axioms of B
consists of all classical tautologies, (A1a)–(A7a), and (A1b)–(A7b). BW extends
B with W, and BN extends BW with N. All three derivation systems have modus
ponens, temporal generalization, and uniform substitution as derivation rules:
(MP)
If
`
 and
`

!
 , then
`
 .
(TG)
If
`
, then
`
G and
`
H
.
(SUB) If
`
, then
`
[ 
=p].
A model
M is called an X-model if it has
M
j
=
 for all X-theorems
, where
X
2
fB;
BW
;
BNg.
For future use we state the following axiomatic completeness result:
Theorem 7.15 For all sets of
S,
U-formulas
 and formulas
:

`
B
 iff

j
=
B
.
We need one more preliminary result, on deﬁnable properties. By Exercise 7.2.4,
well-foundedness is a condition on linear frames which cannot be expressed in ﬁrst-
order logic: it involves an essential second-order quantiﬁcation over all subsets of
the universe. However, to arrive at our expressive completeness result we can get
by with less, namely the condition that every ﬁrst-order deﬁnable non-empty subset
must have a smallest element; one can show that deﬁnably well-ordered models are
sufﬁciently similar to genuine well-ordered models.
The following deﬁnition and lemma capture what we need.
Deﬁnition 7.16 Let
 be a ﬁrst-order formula in
L
1
<
(x),
M
=
(T
;
<;
V
) a model
for
L
1
<. Deﬁne
X
 to be the set deﬁned by
, that is,
X

:=
ft
2
T
j
M
j
=
[t]g.
Then,
M is called deﬁnably well-ordered if for all
(x)
2
L
1
<, the set
X
 has a
smallest element.
Two
L
1
<-models
M
1 and
M
2 are called
n-equivalent, notation
M
1

n
F
OL
M
2,
if for all ﬁrst-order sentences

2
L
1
< of quantiﬁer depth at most
n,
M
1
j
=
 iff
M
2
j
=
.
a



434
7 Extended Modal Logic
Proviso. For the remainder of this section we will assume that our collection of
proposition letters
 is ﬁnite. This is not an essential restriction, but it simpliﬁes
some of the arguments below (see Exercise 7.2.5 for a way of circumventing the
assumption).
Lemma 7.17 Let
n
2
N. Them every deﬁnably well-ordered linear model is
n-
equivalent to a fully well-ordered model.
Proof. Let
M
=
(T
;
<;
V
) be a deﬁnably well-ordered linear model. For
a,
b
2
T
such that
b
<
a, deﬁne
[b;
a)
=
ft
2
T
j
b

t
<
ag, and
(1;
a)
=
ft
2
T
j
t
<
ag. Obviously, we can view such sets — with the ordering and valuation induced
by
M — as linear
L
1
<-models in their own right. Deﬁne
Z
:=
fa
2
T
j
8b
<
a
([b;
a) has a well-ordered
n-equivalent)
g:
By Exercise 7.2.6 there are only ﬁnitely many ﬁrst-order formulas
(x;
y
) of quan-
tiﬁer depth at most
n, say

1
(x;
y
), . . . ,

m
(x;
y
). Let

1
(x;
y
), . . . ,

k
(x;
y
)
2
f
1
(x;
y
), . . . ,

m
(x;
y
)g be such that if
M
j
=

i
(x;
y
)[ab] then
[b;
a) has a well-
ordered
n-equivalent. Then
Z is deﬁned by the formula
(x)
:=
8y
0
@
y

x
!
_
ik

(x;
y
)
1
A
:
As a consequence,
T
n
Z (the complement of
Z in
M) is deﬁnable as well. We
will now show that
T
n
Z is empty. For, suppose otherwise. Then
Z must have
a smallest element
a (as
M is deﬁnably well-ordered). Distinguish the following
cases:
(i)
a is the ﬁrst element of
T,
(ii)
a has an immediate successor, and
(iii) there exists an ascending sequence
(b

)

<, which is coﬁnal in
[b;
a) and
such that
b
0
=
b. (That is,
b
0
=
b,
b
i
<
b
j whenever
i
<
j, and for all
c
2
[b;
a) there exists a
b
i
>
c.)
It is easy to see that the ﬁrst two cases lead to contradictions. As to the third
case, since
a is the minimal element of
T
n
Z, all
b
 are in
Z. So, by deﬁnition,
every interval
[b

;
b

+1
) has a well-ordered
n-equivalent
M
. By Exercise 7.2.7
the lexicographic sum
P

<
M
 is well-ordered and an
n-equivalent to
[b;
a). But
then
a
2
Z — a contradiction.
Therefore
T
n
Z
=
?, and hence
Z
=
T, so every interval
[b;
a) of
T has an
n-equivalent well-ordered model. By using Exercise 7.2.7 again, we see that
M
must have a well-ordered
n-equivalent, as required.
a



7.2 Since and Until
435
Completeness via completeness
With the above preliminaries out of the way, we are now in a position to use the
expressive completeness result recorded in Theorem 7.12 to arrive at an axiomatic
completeness result for BW over well-ordered ﬂows of time.
We need the following lemma.
Lemma 7.18 Every linear BW-model is deﬁnably well-ordered.
Proof. Let
M be a linear model satisfying all instances of the BW-theorems. We
will prove that every non-empty
L
1
<-deﬁnable subset of
T has a smallest element
via detour using the Stavi connectives
S
0 and
U
0.
Let
X be a non-empty
L
1
<-deﬁnable subset of
T. By Theorem 7.12.2 it follows
that
X has a deﬁning formula
 in the language with
S,
U,
S
0,
U
0. If we can show
that
 does in fact belong to the sublanguage with
S and
U, then we are done,
because then we can use the validity of the axioms W and L to show that there
must be a minimal element in
X.
It sufﬁces to show that every formula in the language with
S,
U,
S
0,
U
0 is equiv-
alent to an
S,
U-formula over
M. To this end we argue by induction of formulas in
the richer language. The only non-trivial case is for formulas of the form
U
0
(;
 
)
(and their mirror images), where
 and
 are already assumed to equivalent to
S,
U formulas by the induction hypothesis. So assume
M;
t

U
0
(;
 
). Then there
is a gap
g after
t such that (i)
 holds everywhere between
t and
g, and (ii)
 is
false arbitrarily soon after
g. Now (i) implies that
M;
t

F
 , so by the validity of
the W axiom in
M it follows that
M;
t

U
(: 
;
 
). But this contradicts (ii).
a
Theorem 7.19 BW is (weakly) complete for the class of all well-ordered ﬂows of
time.
Proof. Let
 be a BW-consistent formula. Construct a maximal BW-consistent set
 with

2
. As BW extends B,
 must also be B-consistent. By Theorem 7.15
there exists a linear model
M
=
(T
;
<;
V
) in which
 is satisﬁable. Clearly, for
every
S,
U-formula
 , the formula
H
W( 
)
^
W( 
)
^
GW( 
) is in
, where
W( 
) is the W axiom instantiated for
 . Thus
M is a BW-model, and hence, by
Lemma 7.18 it is deﬁnably well-ordered.
Now, for the ﬁnal step, let
n be the quantiﬁer rank of
ST
(). By Lemma 7.17
there is well-ordered model
M
0 that is
n
+
1-equivalent to
M. Therefore,
M
0
j
=
9x
ST
()(x), and we are done.
a
Using Theorem 7.19 it is easy to obtain a further completeness result, for the tem-
poral logic of the natural numbers.
Theorem 7.20 BN is weakly complete for
(!
;
<), the natural numbers with their
standard ordering.



436
7 Extended Modal Logic
The proof of Theorem 7.20 is left as Exercise 7.2.8.
Exercises for Section 7.2
7.2.1 Supply the missing details for the proof of Proposition 7.10.
7.2.2 Give a ﬁrst-order deﬁnition for the Stavi connectives introduced in Deﬁnition 7.11
— you may assume that we are working on linear ﬂows of time.
7.2.3 Prove Lemma 7.14. That is, show that D deﬁnes discrete orderings, that W
^ L,
deﬁnes well-orderings, and that W
^N picks out the natural numbers in their usual ordering
up to isomorphism.
7.2.4 Show that well-foundedness is a condition on linear frames which cannot be ex-
pressed in ﬁrst-order logic.
7.2.5 Throughout this section we assumed that the collection of proposition symbols that
we are working with is ﬁnite. Show that this assumption can be lifted.
7.2.6 Show that, over a ﬁnite vocabulary, there are at only ﬁnitely many non-equivalent
ﬁrst-order formulas
(x;
y
) of quantiﬁer depth at most
n
7.2.7 Show that the lexicographic sum of a collection of structures that are well-ordered
and
n-equivalent to a given structure
M, is again well-ordered and
n-equivalent to
M.
7.2.8 Prove Theorem 7.20: show that BN is weakly complete for
(!
;
<), the natural num-
bers with their standard ordering.
7.3 Hybrid Logic
An oddity lurks at the heart of modal logic: although states are the cornerstone
of modal semantics, they are not directly reﬂected in modal syntax. We evaluate
formulas inside models, at some state, and use the modalities to scan accessible
states. But modal syntax offers no grip on the states themselves: it does not let us
name them, and it does not let us reason about state equality. Modal syntax and
semantics dance to different tunes.
For many applications, this is a drawback. As we mentioned in Example 1.17,
both feature and description logics can be viewed as modal logics — or at least,
they can up to a point. Real feature logics contain mechanisms for asserting that
two sequences of transitions lead to the same state, and description logics allow
us to name and reason about individuals. Such capabilities (which are crucial)
take us beyond the kinds of modal language we have considered so far. Similarly,
it is often important to reason about what is going on at particular times, and the
temporal formalisms used in artiﬁcial intelligence usually provide expressions such
as Holds(i;
), asserting that the information
 holds at the time named by
i, to



7.3 Hybrid Logic
437
make this possible. The modal logics considered so far contain no analogs of these
important tools.
In their simplest form, hybrid languages are modal languages which put this
right. Hybrid languages treat states as ﬁrst class citizens, and they do so in a par-
ticularly simple way. The key idea is simply to sort the atomic formulas, and to
use one sort of atom — the nominals — to refer to states. Because this mecha-
nism is so simple, may of the attractive properties of modal logic (such as robust
decidability) are unaffected. Indeed, in certain respects hybrid logics are arguably
better behaved than their ordinary modal counterparts: their completeness theory
is particularly straightforward, and they are proof theoretically natural.
In this section we examine one of the simplest hybrid languages: a two-sorted
system with names for states. To build such a language, take a basic modal lan-
guage (built over propositional variables
p,
q,
r, and so on) and add a second sort
of atomic formula. These new atoms are called nominals, and are typically writ-
ten
i,
j and
k. Both types of atom can be freely combined to form more complex
formulas in the usual way. For example,
3(i
^
p)
^
3(i
^
q
)
!
3(p
^
q
)
is a well formed formula. And now for the key idea: insist that each nominal be
true at exactly one state in any model. Thus a nominal names a state by being
true there and nowhere else. This simple idea gives rise to richer logics. Note,
for example, that the previous formula is valid: if the antecedent is satisﬁed at a
state
w, then the unique state named by
i must be accessible from
w, and both
p
and
q must be true there. And note that the use of the nominal
i is crucial: if we
substituted the ordinary propositional variable
r for
i, the resulting formula could
be falsiﬁed.
Actually, what we call the basic hybrid language offers more than this: it also
enables us to build formulas of the form
@
i
, where
i is a nominal. The composite
symbol
@
i is called a satisfaction operator, and it has the following interpretation:
@
i
 is true at any state in a model if and only if
 is satisﬁed at the (unique) state
named by
i (so
@
i
 is analogous to Holds(i;
)). Satisfaction operators play an
important role in hybrid proof theory.
Our discussion of basic hybrid logic is largely conﬁned to a single topic: the
link between frame deﬁnability and completeness. We will show that when pure
formulas are used as axioms they always yield systems which are complete with
respect to the class of frames they deﬁne. Now, a pure formula is simply a formula
whose only atoms are nominals, so in effect this result tells us that frame complete-
ness is automatic for axioms constructed solely out of names. Our discussion will
center on a proof rule called PASTE which is related to the IRR rule discussed in
Section 4.7 and the D-rule of Section 7.1.



438
7 Extended Modal Logic
The basic hybrid language
Given a basic modal language built over propositional variables

=
fp;
q
;
r
;
:
:
:
g,
let

=
fi;
j;
k
;
:
:
:
g be a nonempty set disjoint from
. The elements of

 are
called nominals; they are a second sort of atomic formula which will be used to
name states. We call

[

 the set of atoms and deﬁne basic hybrid language (over

[

) as follows:

::=
i
j
p
j
?
j
:
j

^
 
j
3
j
@
i
:
For any nominal
i, the symbol
@
i is called a satisfaction operator. Note that, syn-
tactically speaking, the basic hybrid language is simply a multimodal language (the
modalities being
3 and all the
@
i), whose atomic symbols are subdivided into two
sorts. If a formula contains no propositional variables (that is, if its only atoms
are nominals) we call it a pure formula. In what follows we assume that we are
working with a ﬁxed basic hybrid language
L in which both
 and

 are countably
inﬁnite.
The basic hybrid language is interpreted on models. As usual, a model
M is
a triple
(W
;
R
;
V
), where
(W
;
R
) is a frame, and
V is a valuation. But although
the deﬁnition of a frame is unchanged, we want nominals to act as names, so we
will insist that a valuation
V on a frame
(W
;
R
) is a function with domain

[

and range
P
(W
) such that for all
i
2

,
V
(i) is a singleton subset of
W. That
is, as usual we place no restrictions on the interpretation of ordinary propositional
variables, but we insist that a valuation makes each nominal true at a unique state.
We call the unique state
w that belongs to
V
(i) the denotation of
i under
V . We
interpret the basic hybrid language by adding the following two clauses to the sat-
isfaction deﬁnition for the basic modal language:
M;
w

i
iff
w
2
V
(i)
M;
w

@
i

iff
M;
d

 where
d is the denotation of
i under
V
:
As usual,
M

 means that
 is true at all states in
M,
F

 means that
 is
valid on the frame
F, and

 means that
 is valid on all frames.
Note that a formula of the form
@
i
j expresses the identity of the states named
by
i and
j. Further, note that a formula of the form
@
i
3j says that the state named
by
i has as an
R-successor the state named by
j.
Although it allows us to refer to states, and talk about state equality, the basic
hybrid language is very much a modal language. Nominals name, but they are sim-
ply a second sort of atomic formula. Moreover, satisfaction operators are normal
modal operators: note that for every nominal
i,

@
i
(
!
 
)
!
(@
i

!
@
i
 
);
is valid; and if

, then

@
i
.
Moreover, the basic hybrid language is quite a simple modal language. For
example, its satisﬁability problem is known to be no more complex than the satis-
ﬁability problem for the basic modal language:



7.3 Hybrid Logic
439
Theorem 7.21 The satisﬁability problem for the basic hybrid logic is PSPACE-
complete.
But in spite of its simplicity the basic hybrid language is surprisingly strong when
it comes to frame deﬁnability. For a start, many properties deﬁnable in the basic
modal language can be deﬁned using pure formulas:
(reﬂexivity)
i
!
3i
(symmetry)
i
!
23i
(transitivity)
33i
!
3i
(density)
3i
!
33i
(determinism)
3i
!
2i
Moreover, pure formulas also enable us to deﬁne many properties not deﬁnable in
the basic modal language, as the reader can easily verify:
(irreﬂexivity)
i
!
:3i
(asymmetry)
i
!
:33i
(antisymmetry)
i
!
2(3i
!
i)
(intransitivity)
33i
!
:3i
(universality)
3i
(trichotomy)
@
j
3i
_
@
j
i
_
@
i
3j
(at most 2 states)
@
i
(:j
^
:k
)
!
@
j
k
All the frame properties deﬁned above are ﬁrst-order. This is no coincidence: all
pure formulas deﬁne ﬁrst-order frame conditions. This is easy to prove: there is a
natural way of extending the Standard Translation to cover nominals and satisfac-
tion operators which explains why (see Exercise 7.3.1).
But not only do pure formulas deﬁne ﬁrst-order properties, when used as axioms
they are automatically complete with respect to the class of frames they deﬁne.
More precisely, there is a proof system called
K
h
+ RULES such that for any set of
pure formulas
:
If P is the normal hybrid logic (which we will shortly deﬁne) obtained by
adding the formulas in
 as axioms to
K
h
+ RULES, then P is complete with
respect to the class of frames deﬁned by P.
The rest of the section is devoted to proving this, but before diving into the tech-
nicalities it is worth noting that the result hinges on a rather simple observation.
Let us say that a model
(W
;
R
;
V
) is named if every state in the model is the de-
notation of some nominal (that is, for all
w
2
W there is some nominal
i such that
V
(i)
=
fw
g). Furthermore, if
 is a pure formula, we say that
 is a pure instance
of
 if
 is obtained from
 by uniformly substituting nominals for nominals. Then
we have:



440
7 Extended Modal Logic
Lemma 7.22 Let
M
=
(F;
V
) be a named model and
 a pure formula. Suppose
that for all pure instances
 of
,
M

 . Then
F

.
Proof. Exercise 7.3.3.
a
That is, for named models and pure formulas the gap between truth in a model and
validity in a frame is non-existent. So if we had a way of building named models,
we wouldn’t need to appeal to relatively complex syntactic criteria (such as being a
Sahlqvist formula) to obtain general completeness results: any pure formula would
give rise to strongly complete logic for the class of frames it deﬁned. In essence,
the work that follows can be summed as follows: we are going to isolate the logic
K
h
+RULES and show that we can build named models from its MCSs and prove an
Existence Lemma. Once this is done, a wide range of frame completeness results
will be immediate by appeal to Lemma 7.22.
Pure extensions of
K
h
+ RULES
Let’s ﬁrst say what a normal hybrid logic is:
Deﬁnition 7.23 A set of formulas
 in the basic hybrid language is a normal hy-
brid logic if it contains all tautologies,
2(p
!
q
)
!
(2p
!
2q
),
3p
$
:2:p,
the axioms listed below, and it is closed under the following rules of proof: modus
ponens, generalization,
@
i-generalization (if
 is provable then so is
@
i
, for any
nominal
i) and sorted substitution (if

2
, and
 results from
 by uniformly
replacing propositional letters by arbitrary formulas, and nominals by nominals,
then

2
). We call the smallest normal hybrid logic
K
h.
a
The motivation for the sorted substitution rule should be clear: while propositional
variables are placeholder for arbitrary information, nominals are names, and sub-
stitution must respect the distinction.
The axioms needed to complete our deﬁnition of
K
h fall into three groups. The
ﬁrst identiﬁes the basic logic of satisfaction operators:
(K
@)
@
i
(p
!
q
)
!
(@
i
p
!
@
i
q
)
(self-dual)
@
i
p
$
:@
i
:p
(introduction)
i
^
p
!
@
i
p
As satisfaction operators are normal modal operators, the inclusion of
K
@ should
come as no surprise. As for self-dual, note that self-dual modalities are those whose
transition relation is a function: given the jump-to-the-named-state interpretation of
satisfaction operators, this is exactly the axiom we would expect. Introduction tells
us how to place information under the scope of satisfaction operators. Actually,
it also tells us how to get hold of such information, for if we replace
p by
:p,



7.3 Hybrid Logic
441
contrapose, and make use of self-dual, we obtain
(i
^
@
i
p)
!
p; we call this the
elimination formula.
The second group is a modal theory of naming (or to put it another way, a modal
theory of state equality):
(ref)
@
i
i
(sym)
@
i
j
$
@
j
i
(nom)
@
i
j
^
@
j
p
!
@
i
p
(agree)
@
j
@
i
p
$
@
i
p
Note that the transitivity of naming follows from the nom axiom; for example,
substituting the nominal
k for the propositional variable
p yields
@
i
j
^
@
j
k
!
@
i
k.
The ﬁnal axiom pins down the interaction between @ and
3:
(back)
3@
i
p
!
@
i
p
Note that
3i
^
@
i
p
!
3p is another valid @-3 interaction principle; it is called
bridge and we will use it when we prove the Existence Lemma. However bridge is
provable in
K
h as the reader is asked to show in Exercise 7.3.4.
The soundness of these axioms is clear — but what about completeness? Let
us say that a
K
h-MCS is named if and only if it contains a nominal, and call any
nominal belonging to a
K
h-MCS a name for that MCS. Now,
K
h is strong enough to
prove a lemma which is fundamental to our later work: hidden inside any
K
h-MCS
are a collection of named MCSs with a number of desirable properties:
Lemma 7.24 Let
  be a
K
h-MCS. For every nominal
i, let

i be
f
j
@
i

2
 g.
Then:
(i) For every nominal
i,

i is a
K
h-MCS that contains
i.
(ii) For all nominals
i and
j, if
i
2

j then

j
=

i.
(iii) For all nominals
i and
j,
@
i

2

j iff
@
i

2
 .
(iv) If
k is a name for
 , then
 =

k.
Proof. (i) First, for every nominal
i we have the ref axiom
@
i
i, hence
i
2

i.
Next,

i is consistent. For assume for the sake of a contradiction that it is not.
Then there are
Æ
1
;
:::;
Æ
n
2

i such that
`
:(Æ
1
^



^
Æ
n
). By
@
i-necessitation,
`
@
i
:(Æ
1
^



^
Æ
n
), hence
@
i
:(Æ
1
^



^
Æ
n
) is in
 , and thus by self-dual
:@
i
(Æ
1
^



^
Æ
n
) is in
  too. On the other hand, as
Æ
1
;
:::;
Æ
n
2

i, we have
@
i
Æ
1
;
:::;
@
i
Æ
n
2
 . As
@
i is a normal modality,
@
i
(Æ
1
^



^
Æ
n
)
2
  as well,
contradicting the consistency of
 . So

i is consistent.
Is

i maximal? Assume it is not. Then there is a formula
 such that neither
 nor
: is in

i. But then both
:@
i
 and
:@
i
: belong to
 , and this is
impossible: if
:@
i

2
 , then by self-duality
@
i
:
2
  as well. We conclude
that

i is a
K
h-MCS named by
i.



442
7 Extended Modal Logic
(ii) Suppose
i
2

j; we will show that

j
=

i. As
i
2

j,
@
j
i
2
 .
Hence, by sym,
@
i
j
2
  too. But now the result is more-or-less immediate. First,

j


i. For if

2

j, then
@
j

2
 . Hence, as
@
i
j
2
 , it follows by nom
that
@
i

2
 , and hence that

2

i as required. A similar nom-based argument
shows that

i


j.
(iii) By deﬁnition
@
i

2

j iff
@
j
@
i

2
 . By agree,
@
j
@
i

2
  iff
@
i

2
 . (We call this the @-agreement property; it plays an important role
in the completeness proof.)
(iv) Suppose
  is named by
k. Let

2
 . Then as
k
2
 , by Introduction
@
k

2
 , and hence

2

k. Conversely, if

2

k, then
@
k

2
 . Hence, as
k
2
 , by elimination we have

2
 .
a
In what follows, if
  is a
K
h-MCS and
i is a nominal, then we will call
f
j
@
i

2
 g a named set yielded by
 .
We have reached an important crossroad. It is now reasonably straightforward to
prove that
K
h is the minimal hybrid logic. We would do so as follows. Given a
K
h-
consistent set of sentences
, use the ordinary Lindenbaum’s Lemma to expand
it to a
K
h-MCS

+, and build a model by taking the submodel of the ordinary
canonical model generated by

+
[
f
i
j

i is a named set yielded by

+
g:
The reader is asked to do this in Exercise 7.3.5.
But we have a more ambitious goal in mind: we don’t want to build just any
model, we want a named model. This will enable us to apply Lemma 7.22 and
prove the completeness of pure axiomatic extensions. However we face two prob-
lems. The ﬁrst is this. Given a
K
h-consistent set of formula, we can certainly
expand it to an MCS using Lindenbaum’s Lemma — but nothing guarantees that
this MCS will be named. The second problem is much deeper. Suppose we over-
came the ﬁrst problem and learned how to expand any consistent set of sentences
 to a named MCS

+. Now, as we want to build a named model, this pretty much
dictates that only the named MCSs yielded by

+ should be used in the model con-
struction. And now for the tough part: nothing we have seen so far guarantees that
there are enough MCSs here to support an Existence Lemma. Incidentally, note
that the completeness-via-generation method sketched in the previous paragraph
doesn’t face this problem: generation automatically gives us all successor MCSs,
so we can make use of the ordinary modal Existence Lemma. Unfortunately, not
all these successor MCSs need be named, so the generation method won’t help with
the stronger result we have in mind.
But these difﬁculties are similar to those we faced when discussing rules for the
undeﬁnable, and this suggests a solution. In Section 7.22 we simulated names us-
ing tense operators, and used the forward-and-backwards interplay of
F and
P to
create a coherent network of named MCSs which supported a suitable Existence
Lemma. Moreover, simulated names were used to deﬁne the D-rule mentioned in



7.3 Hybrid Logic
443
Section 7. But nominals are genuine names, and satisfaction operators are an excel-
lent way of enforcing coherence — surely it must be possible to deﬁne analogous
proof rules for the basic hybrid language? Indeed it is:
(NAME
)
`
j
!

`

(PASTE
)
`
@
i
3j
^
@
j

!

`
@
i
3
!

In both rules,
j is a nominal distinct from
i that does not occur in
 or
. The
NAME rule is going to solve our ﬁrst problem, the PASTE rule our second. These
rules are clearly close cousins of the IRR rule and the D-rule, but let’s defer further
discussion till the end of the section, and put them to work right away.
Let
K
h
+ RULES be the logic obtained by adding the NAME and PASTE rules to
K
h. We say that an
K
h
+ RULES-MCS
  is pasted iff
@
i
3
2
  implies that for
some nominal
j,
@
i
3j
^
@
j

2
 . And now for the key observation: our new
rules guarantee we can extend any
K
h
+ RULES-consistent set of sentences to a
named and pasted
K
h
+ RULES-MCS, provided we enrich the language with new
nominals:
Lemma 7.25 (Extended Lindenbaum Lemma) Let

0 be a (countably) inﬁnite
collection of nominals disjoint from

, and let
L
0 be the language obtained by
adding these new nominals to
L. Then every
K
h
+ RULES-consistent set of formu-
las in language
L can be extended to a named and pasted
K
h
+ RULES-MCS in
language
L
0.
Proof. Enumerate

0. Given a consistent set of
L-formulas
, deﬁne

k to be

[
fk
g, where
k is the ﬁrst new nominal in our enumeration.

k is consistent.
For suppose not. Then for some conjunction of formulas
 from
,
`
k
!
:.
But as
k is a new nominal, it does not occur in
; hence, by the NAME rule,
`
:.
But this contradicts the consistency of
, so

k must be consistent after all.
We now paste. Enumerate all the formulas of
L
0, deﬁne

0 to be

k, and sup-
pose we have deﬁned

m, where
m

0. Let

m+1 be the
m
+
1-th formula in our
enumeration of
L
0. We deﬁne

m+1 as follows. If

m+1
[
f
m+1
g is inconsistent,
then

m+1
=

m. Otherwise:
(i)

m+1
=

m
[
f
m+1
g if

m+1 is not of the form
@
i
3. (Here
i can be
any nominal.)
(ii)

m+1
=

m
[
f
m+1
g
[
f@
i
3j
^
@
j
g, if

m+1 is of the form
@
i
3.
(Here
j is the ﬁrst nominal in the new nominal enumeration that does not
occur in

m or
@
i
3.)
Let

+
=
S
n0

n. Clearly this set is named (by
k), maximal, and pasted.
Furthermore, it is consistent, for the only non-trivial aspects of the expansion is
that deﬁned by the second item, and the consistency of this step is precisely what



444
7 Extended Modal Logic
the PASTE rule guarantees. Note the similarity of this argument to the standard
completeness proof for ﬁrst-order logic: in essence, PASTE gives us the deductive
power required to use nominals as Henkin constants.
a
And now we can deﬁne the models we need. In fact, we’re basically going to use
the named sets examined in Lemma 7.24, but with one small but crucial change:
instead of starting with an arbitrary
K
h-MCS, we’ll insist on using the named sets
yielded by a named and pasted
K
h
+ RULES-MCS.
Deﬁnition 7.26 Let
  be a named and pasted
K
h
+ RULES-MCS. The named
model yielded by
 , is
M
 =
(W
 ;
R
 ;
V
 ). Here
W
  is the set of all named sets
yielded by
 ,
R is the restriction to
W
  of the usual canonical relation between
MCSs (so
R
 uv iff for all formulas
,

2
v implies
3
2
u) and
V
  is the usual
canonical valuation (so for any atom
a,
V
 (a)
=
fw
2
W
 j
a
2
w
g).
a
Note that
M
  really is a model: by items (i) and (ii) of Lemma 7.24,
V
  assigns
every nominal a singleton subset of
W
 . And, because we insisted that
  be
named and pasted, we can prove the Existence Lemma we require:
Lemma 7.27 (Existence Lemma) Let
  be a named and pasted
K
h
+ RULES-
MCS, and let
M
=
(W
;
R
;
V
) be the named model yielded by
 . Suppose
u
2
W
and
3
2
u. Then there is a
v
2
W such that
R
uv and

2
v.
Proof. As
u
2
W, for some nominal
i we have that
u
=

i. Hence as
3
2
u,
@
i
3
2
 . But
  is pasted so for some nominal
j,
@
i
3j
^
@
j

2
 , and so
3j
2

i and

2

j. If we could show that
R

i

j, then

j would be a suitable
choice of
v. So suppose
 
2

j. This means that
@
j
 
2
 . By @-agreement
(item (iii) of Lemma 7.24)
@
j
 
2

i. But
3j
2

i. Hence, by Bridge,
3 
2

i
as required.
a
In short, we have successfully blended the ﬁrst-order idea of Henkin constants with
the modal idea of canonical models, and it’s plain sailing all the way to the desired
completeness result.
Lemma 7.28 (Truth Lemma) Let
M
=
(W
;
R
;
V
) be the named model yielded
by a named and pasted
K
h
+RULES-MCS
 , and let
u
2
W. Then, for all formulas
,

2
u iff
M;
u

.
Proof. Induction on the structure of
. The atomic, boolean, and modal cases are
obvious (we use the Existence Lemma just proved for the modalities). What about
the satisfaction operators? Suppose
M;
u

@
i
 . This happens iff
M;

i

 (for
by items (i) and (ii) of Lemma 7.24,

i is the only MCS containing
i, and hence,
by the the atomic case of the present lemma, the only state in
M where
i is true) iff
 
2

i (inductive hypothesis) iff
@
i
 
2

i (using the fact that
i
2

i together



7.3 Hybrid Logic
445
with Introduction for the left-to-right direction and elimination for the right-to-left
direction) iff
@
i
 
2
u (@-agreement).
a
Theorem 7.29 (Completeness) Every
K
h
+ RULES-consistent set of formulas in
language
L is satisﬁable in a countable named model. Moreover, if
 is a set
of pure formulas (in
L), and P is the normal hybrid logic obtained by adding all
the formulas in
 as extra axioms to
K
h
+ RULES, then every P-consistent set
of sentences is satisﬁable in a countable named model based on a frame which
validates every formula in
.
Proof. For the ﬁrst claim, given a
K
h
+ RULES-consistent set of formulas
, use
the Extended Lindenbaum Lemma to expand it to a named and pasted set

+ in
a countable language
L
0. Let
M
=
(W
;
R
;
V
) be the named model yielded by

+. By item (iv) of Lemma 7.24, because

+ is named,

+
2
W. By the Truth
Lemma,
M;

+

. The model is countable because each state is named by
some
L
0 nominal, and there are only countably many of these.
For the ‘moreover’ claim, given a P-consistent set of formulas
, use the Ex-
tended Lindenbaum Lemma to expand it to a named pasted P-MCS

+. The named
model
M
 that

+ gives rise to will satisfy
 at

+; but in addition, as ev-
ery formula in
 belongs to every P-MCS, we have that
M


. Hence, by
Lemma 7.22, the frame underlying
M
 validates
.
a
Example 7.30 We know that
i
!
:3i deﬁnes irreﬂexivity and
33i
!
3i de-
ﬁnes transitivity, hence adding these formulas as axioms to
K
h
+ RULES yields a
logic (let’s call it I4) which is complete with respect to the class of strict preorders.
Hence
33p
!
3p, the ordinary modal transitivity axiom, must be I4-provable.
Furthermore, as
i
!
:33i is valid on any asymmetric frame, and
i
!
2(3i
!
i)
is valid on any antisymmetric frame, these must be I4-provable too. The reader is
asked to supply I4-proofs in Exercise 7.3.6.
a
The PASTE rule has played an pivotal role in our work; is there anything we can
say about it apart from ‘Hey, it works!’? There is. As we will now see, PASTE is
actually a lightly-disguised sequent rule.
A sequent is an expression of the form
  !
, where
  and
 are multisets of
formulas (that is,
  and
 may contain multiple occurrences of the same formula).
Note that the sequent arrow
 ! is longer than the material implication arrow
!.
Sequents can be read as follows: whenever all the formulas in
  are true at some
state in a model, at least one formula in
 is true at that state too. A sequent rule
takes a sequent as input, and returns another sequent as output.
Now, here’s PASTE as we stated it above:
`
@
i
3j
^
@
j

!

`
@
i
3
!




446
7 Extended Modal Logic
Let’s get rid of the
` symbols and replace the implications by sequent arrows:
@
i
3j
^
@
j

 !

@
i
3
 !

Splitting the formula in the top line into two simpler formulas yields:
@
i
3j;
@
j

 !

@
i
3
 !

This rule works in arbitrary deductive contexts, so let’s add a left-hand multiset
 ,
and turn
 into a right-hand multiset
, thus obtaining:
@
i
3j;
@
j
;
  !

@
i
3;
  !

But this is just a sequent rule, and a useful one at that. Let’s read it from bottom
to top: to prove
 given the information
@
i
3 and
  (that’s the bottom line) in-
troduce a brand new nominal
j and try to prove
 from
@
i
3j,
@
j
 and
  (that’s
the top line). That is, we should search for a proof by decomposing the formula
@
i
3 into a near-atomic formula
@
i
3j and simpler formula
@
j
. In fact, this
decomposition is the key idea needed to deﬁne sequent calculi, tableaux, and natu-
ral deduction systems for hybrid logics, and several systems which work this way
have been developed (see the Notes for details). In effect, such systems discard
K
h
from
K
h
+ RULES (after all, why bother keeping the clumsy Hilbert-style part?)
and strengthen the RULES component so it can assume full deductive responsibility.
To conclude, a general remark. As should now be clear (especially if you have
already done Exercises 7.3.1, 7.3.2, and 7.3.3), the basic hybrid language is a gen-
uine hybrid between ﬁrst-order and modal logic: it makes available a number of
key ﬁrst-order capabilities (such as names for states and state-equality assertions)
in a decidable (indeed, PSPACE-complete) propositional modal logic. But now
that we are used to viewing names as formulas, it is easy to go even further. For
example, instead of thinking of nominals as names, we could think of them as
variables over states and bind them with quantiﬁers. For example, we could allow
ourselves to form expressions such as
9x
(x
^
39y
(y
^

^
@
x
2(3y
!
 
))):
This expression captures the effect of the until operator: it says
U
(;
 
). Note that
in this example the
9 quantiﬁer is only used to bind nominals to the current state.
This is such an important operation that a special notation,
#, has been introduced
for it. Using this notation the deﬁnition of
U
(;
 
) can be written as
#
x(x
^
3#
y
(y
^

^
@
x
2(3y
!
 
))):



7.3 Hybrid Logic
447
It turns out that when the basic hybrid language is enriched only with
# (that is,
not with the full power of
9) then the resulting language picks out exactly the frag-
ment of the ﬁrst-order correspondence language that is invariant under generated
submodels. See the Notes for more details.
Exercises for Section 7.3
7.3.1 Extend the standard translation to the basic hybrid language by adding clauses for
nominals and satisfaction operators. Use your translation to show that all classes of frames
deﬁned by pure formulas are ﬁrst-order deﬁnable. (Hint: translate nominals to free ﬁrst-
order variables.)
7.3.2 For any
n

1, let
R
n
xy be the ﬁrst-order formula
9z
1



9z
n
(R
xz
1
^
R
z
1
z
2
^



^
R
z
n
y
). Let
 be a ﬁrst-order formula that is a boolean combination of formulas of
the form
R
n
xy,
R
xy, and
x
=
y. Show that the class of frames deﬁned by the universal
closure of
 is deﬁnable in the basic hybrid language. (Hint: look at the way we deﬁned
trichotomy.)
7.3.3 Prove Lemma 7.22. That is, if
M
=
(F;
V
) is a named model and
 is a pure formula
and for all pure instances
 of
 we have that
M

 , then
F

.
7.3.4 Show that
3i
^
@
i
p
!
3p, the Bridge formula, is provable in
K
h. (Hint: prove the
contraposed form
3i
^
2p
!
@
i
p with the help of
3q
^
2p
!
3(q
^
p), Introduction,
and Back.)
7.3.5 Prove that
K
h is the minimal hybrid logic by ﬂeshing out the completeness-via-
generation argument sketched in the text.
7.3.6 Find I4-proofs of
33p
!
3p,
i
!
:33i, and
i
!
2(3i
!
i). (The logic I4 was
introduced in Example 7.30.)
7.3.7 The PASTE rule makes crucial use of @-operators. Prove an analog of Theorem 7.29
for the @-free sublanguage of the basic hybrid language. (Hint: you need to simulate the
satisfaction operators using the modalities. So for all
n;
m

0, add the axiom
3
n
(i
^
p)
!
2
m
(i
!
p). Furthermore, let
3
i
 be shorthand for
3(i
^
), and add all rules of the form
`
3
k



3
i
3
j

!

`
3
k



3
i
3
!

Here
j is a nominal distinct from
k
;



;
i that does not occur in
 or
.)
7.3.8 Let I4D be the normal hybrid logic obtained by adding the axiom
3(i
_
:i) to
I4. Clearly I4D lacks the ﬁnite frame property. Show that it possesses the ﬁnite model
property (and hence that Theorem 3.28 fails for hybrid languages). Exploit this by proving
the decidability of I4D using a ﬁltration argument.
7.3.9 Add the global diamond E to the basic hybrid language. Use a ﬁltration argument to
show that the satisﬁability problem the resulting language is decidable. What is its com-
plexity? (Note that
@
i
 can be deﬁned to be E
(i
^
), so you don’t have to deal explicitly
with the satisfaction operators.) Show that a class of frames is deﬁnable in this language if
and only if it is deﬁnable in the basic modal language enriched with the D-operator. (Here
‘deﬁnable’ means deﬁnable by an arbitrary formula, not just a pure formula.)



448
7 Extended Modal Logic
7.4 The Guarded Fragment
In Chapter 2 we saw that modal languages can be viewed as fragments of ﬁrst-
order logic, and in Chapter 6 we discovered that these fragments have some nice
computational properties. It thus seems natural to try and see how far we can
generalize these properties to larger fragments of ﬁrst-order logic. This will be the
main aim of this section: we will deﬁne and discuss two extensions of the modal
fragment with reasonably nice computational behavior.
In order to isolate such fragments, what properties of the modal fragment of
ﬁrst-order logic should we concentrate on? In particular, what makes modal logic
decidable? If we conﬁne ourselves to the basic modal language, is it perhaps the
fact that the standard translation can be carried out entirely within the two variable
fragment of ﬁrst-order logic (which has a decidable satisﬁability problem)? This
argument immediately breaks down if we consider languages with modal operators
of higher arity: while giving rise to decidable logics as well, these languages have
standard translations that really need more than two variables. But as soon as we
are considering
n-variable fragments of ﬁrst-order logic with
n
>
2, we face an
undecidable satisﬁability problem.
Rather, it seems to be the fact that the modal fragment of ﬁrst-order logic allows
quantiﬁcation only in a very restricted form, as is obvious from the modal clause
in the deﬁnition of the standard translation function:
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
(7.3)
It is this restricted form of quantiﬁcation which ensures that modal logic is the
bisimulation invariant fragment of ﬁrst-order logic, and bisimulation invariance of
modal truth was critical in the ﬁrst method of proving the ﬁnite model property for
the basic modal language (see Section 2.3). Recall that the starting point of this
method was the observation that modal logic has the tree model property (meaning
that every satisﬁable modal formula is satisﬁable on a tree model), and that bisimu-
lation invariance is pivotal in proving this result. In short, there seems to be a direct
line from the restricted quantiﬁer pattern in (7.3), via bisimulation invariance and
the tree model property, to the ﬁnite model property and decidability.
This provides our ﬁrst search direction: look for ﬁrst-order fragments charac-
terized by restricted quantiﬁcation. It turns out that one can easily relax many
constraints applying to the (basic) modal fragment. For example, we do not have
to conﬁne ourselves to formulas using two variables only, to formulas having pre-
cisely one free variable, or to formulas with predicates of arity at most two. Relax-
ing these constraints naturally leads to the so-called guarded fragment of ﬁrst-order
logic; the idea here is that quantiﬁers may appear only in the following form:
9y
(G(x
;
y
)
^
 
(x;
y
))
(7.4)
in which
G(x
;
y
) is an atomic formula that we will call the guard of the quantiﬁ-



7.4 The Guarded Fragment
449
cation (or, of the formula). The crucial ingredient that we keep from (7.3) is that
all free variables of
 are also free in the guard
G(x;
y
). And indeed, it can be
shown that the guarded fragment has various nice properties, such as a decidable
satisﬁability problem and the ﬁnite model property.
However, there are some very natural modal-like languages, or alternative but
intuitive interpretations for standard modal languages, that correspond to a decid-
able fragment of ﬁrst-order logic as well, but are not covered by this deﬁnition. For
example, consider the language with the since and until operators: it is straightfor-
ward to turn the truth deﬁnitions for these operators into a standard translation to
ﬁrst-order logic. The interesting clauses are
ST
x
(U
(;
 
))
=
9y
(R
xy
^
ST
y
()
^
8z
((R
xz
^
R
z
y
)
!
ST
z
( 
)));
()
and a similar one for the since operator. We can prove that this kind of clause
takes us outside the guarded fragment of ﬁrst-order logic: the problem concerns
the ‘betweenness conjunct’
8z
((R
xz
^
R
z
y
)
!
ST
z
( 
)) which has a ‘compos-
ite’ guard,
(R
xz
^
R
z
y
). Nevertheless, the language with since and until has a
decidable satisﬁability problem; apparently, some composite guards are admissible
as well.
Examples such as
() lead to extensions of the guarded fragment to fragments
in which one is more liberal in the precise conditions imposed on the guard. One
can be a bit more liberal here because in the ‘direct line’ mentioned earlier there
are some steps that could be skipped on the way. In particular, if we are interested
in decidability rather than the ﬁnite model property, we could just as well settle
for fragments of ﬁrst-order logic to which we may apply the mosaic method of
Section 6.4. Recall that the mosaic method is a way of proving decidability by
‘deconstructing’ a model into a ﬁnite number of ﬁnite pieces, and then using such
ﬁnite toolboxes for constructing models again, models that usually hang together
quite loosely (in a sense to be made precise later). This provides the second di-
rection in our quest: try to ﬁnd fragments of ﬁrst-order logic to which the mosaic
method applies, leading to a loose model property. Implementing this idea one
naturally ﬁnds quantiﬁer restrictions of the form
9y
(
(x
;
y
)
^
 
(x
;
y
))
(7.5)
in which there are constraints on the presence of variables in certain subformulas
of the guard
. For such fragments one may ﬁnd a direct line from the restricted
quantiﬁer pattern in (7.5), via an appropriate notion of bisimulation invariance and
the loose model property, to some ﬁnite mosaic property and decidability.
The particular extension that we discuss in this section is that of the packed
fragment; it ﬁts very nicely in the mosaic approach. On a ﬁrst reading of the
section the reader may choose to skip the parts referring to this packed fragment,
and concentrate on the guarded fragment.



450
7 Extended Modal Logic
The guarded and the packed fragment
We need some preliminaries. The ﬁrst-order language that we will be working
in is purely relational, with equality; the language contains neither constants nor
function symbols. For a sequence of variables
x
=
x
1
;
:
:
:
;
x
n, we frequently
write
9x
, which, as usual, has the same meaning as
9x
1
:
:
:
9x
n
. However,
in this section we view
9x not as an abbreviation, but as a primitive operator. In
particular this means that the subformulas of
9x
 are just
9x
 itself, together with
the subformulas of
. As usual, by writing
(x) we indicate that the free variables
of
 are among
x
1
;
:
:
:
;
x
n.
Deﬁnition 7.31 We say that a formula
 packs a set of variables
fx
1
;
:
:
:
;
x
k
g if
(i)
F
r
e
e
()
=
fx
1
;
:
:
:
;
x
k
g and (ii)
 is a conjunction of formulas of the form
x
i
=
x
j or
R
(x
i
1
;
:
:
:
;
x
i
n
) or
9y
R
(x
i
1
;
:
:
:
;
x
i
n
) such that (iii) for every
x
i
6=
x
j,
there is a conjunct in
 in which
x
i and
x
j both occur free.
The packed fragment
PF is deﬁned as the smallest set of ﬁrst order formulas
which contains all atomic formulas and is closed under the boolean connectives
and under packed quantiﬁcation. That is, whenever
 is a packed formula,
 packs
F
r
e
e
(
), and
F
r
e
e
( 
)

F
r
e
e
(
), then
9x
(
^
 
) is packed as well;
 is called
the guard of this formula. The guarded fragment
GF is the subfragment of
PF in
which we only allow guarded quantiﬁcation as displayed in (7.4); that is, packed
quantiﬁcation in which the guard
 is an atomic formula.
PF
n and
GF
n denote the restrictions to
n variables and at most
n-ary predicate
symbols of
PF and
GF, respectively.
a
Examples of guarded formulas are
(i) the standard translation of any modal formula (in any language),
(ii) the standard translation of any formula in the basic temporal language,
(iii) formulas like
8xy
(R
xy
!
R
y
x),
9xy
(R
xy
^
R
y
x
^
(R
xx
_
R
y
y
)), . . .
For an example of a packed formula which is not guarded, consider
9xy
z
((R
xy
^
R
xz
^
R
y
z
)
^
:C
xy
z
). For another example, ﬁrst consider the standard translation
9y
(R
xy
^
P
y
^
8z
((R
xz
^
R
z
y
)
!
Qz
)) of the formula
U
(p;
q
). This formula is
not packed itself, because the guard of the subformula
8z
((R
xz
^
R
z
y
)
!
Qz
))
has no conjunct in which the variables
x and
y occur together. But of course, the
formula is equivalent to
9x
(R
xy
^
P
y
^
8z
((R
xz
^
R
z
y
^
R
xy
)
!
Qz
))
which is packed. It is not hard to convert this example into a proof showing that
every formula in the since and until language is equivalent to a packed formula.
Second, note that the notion of packedness only places meaningful restrictions
on pairs of distinct variables: since the formula
x
=
x packs the set of variables



7.4 The Guarded Fragment
451
fxg, the formula
9x(x
=
x
^
 
(x)), (that is, with a single quantiﬁcation over the
variable
x) is a packed formula, at least, provided that
 
(x) is packed. Since the
given formula is equivalent to
9x
 
(x) this shows that packedness allows a fairly
mild form of ordinary quantiﬁcation, namely over formulas with one free variable
only. A nice corollary of this is that we may perform the standard translation of the
global diamond
E within the two variable guarded fragment:
ST
x
(E)
=
ST
y
(E)
=
9x
(ST
x
())

9x
(x
=
x
^
ST
x
()):
Finally, not all formulas are packed, or equivalent to a packed formula. For exam-
ple, the transitivity formula
8y
z
((R
xy
^
R
y
z
)
!
R
xz
) is not packed, and neither
is the standard translation of the difference operator:
9y
(x
6=
y
^
P
y
).
Nice properties
Having deﬁned the packed and the guarded fragment of ﬁrst-order logic, let us
see now what we can prove about these fragments. To start with, for each of the
two fragments we can ﬁnd a suitable notion of bisimulation which characterizes
the fragment in the same way as the ordinary bisimulation characterizes the modal
fragment of ﬁrst-order logic. Unfortunately we do not have the space to go into
detail here. Nevertheless, we will show that both fragments have what we call the
loose model property: in Theorem 7.33 we will show that every satisﬁable packed
formula can be satisﬁed on a loose model. What, then, is a loose model?
Deﬁnition 7.32 Let
A
=
(A;
I
) be a ﬁrst-order structure. A tuple
(a
1
;
:
:
:
;
a
n
) of
objects in
A is called live in
A if either
a
1
=



=
a
n or
(a
1
;
:
:
:
;
a
n
)
2
I
(P
)
for some predicate symbol
P. A subset
X of
A is called guarded if there is some
live tuple
(a
1
;
:
:
:
;
a
n
) such that
X

fa
1
;
:
:
:
;
a
n
g. In particular, singleton sets
are always guarded; note also that guarded sets are always ﬁnite.
X is packed or
pairwise guarded if it is ﬁnite and each of its two-element subsets is guarded.
We say that
A is a loose model of degree
k
2
N if there is some acyclic connected
graph
G
=
(G;
E
) and a function
f mapping nodes of
G to subsets of
A of size
not exceeding
k such that for every live tuple

s from
A, the set
L(s)
=
fg
2
G
j
s
i
2
f
(g
) for all
s
i
g, is a non-empty and connected subset of
G.
a
In words, we call a model
A
=
(A;
I
) loose if we can associate a connected graph
G
=
(G;
E
) with it in the following way. Each node
t of the graph corresponds
to a small subset
f
(t) of the model; a good way of thinking about this is that
t
‘describes’
f
(t). One then requires that the graph ‘covers’ the entire model in the
sense that any
a
2
A belongs to one of these sets (this follows from the fact that
for any
a
2
A, the ‘tuple’
a is live). The fact that each set
L(a
) is connected when-
ever
a is live, implies that various nodes of the graph will not give contradictory



452
7 Extended Modal Logic
descriptions of the model. Finally, the looseness of the model intuitively stems
from the acyclicity of
G and the connectedness of the sets
L(a
); for, this ensures
that in walking through the graph we may describe different parts of the model,
but we never have to worry about returning to the same part once we have left it.
Summarizing, we may see the graph as a loose, coherent collection of descriptions
of local submodels of the model. Loose models are the ones for which we can ﬁnd
such a graph.
The following result states that the packed fragment of ﬁrst-order logic has the
loose model property.
Theorem 7.33 Every satisﬁable packed formula can be satisﬁed on a loose model
(of degree at most the number of
9x subformulas of
).
But the big question is of course whether following this looseness principle we
have indeed arrived at a decidable fragment of ﬁrst-order logic. The next theorem
states that we have.
Theorem 7.34 The satisﬁability problems for the guarded and the packed frag-
ment are decidable; both problems are DEXPTIME-complete (complete for doubly
exponential time). However, for a ﬁxed natural number
n, the satisﬁability problem
for formulas in the packed fragment
PF
n is decidable in EXPTIME.
And ﬁnally, what about the ﬁnite model property? Will every satisﬁable packed
formula have a ﬁnite model? Here as well, the packed fragment displays very nice
behavior. Unfortunately, we do not have the space for a proof of the ﬁnite model
property for the packed fragment — sufﬁce it to say that it involves some quite
advanced techniques from ﬁnite model theory. For some further information the
reader is referred to the Notes at the end of the section.
Mosaics
The remainder of the section is devoted to proving the Theorems 7.34 and 7.33.
The main idea behind the proof is to use the mosaic method that we met in Chap-
ter 6. Roughly speaking, this method is based on the idea of deconstructing mod-
els into a ﬁnite collection of ﬁnite submodels, and conversely, of building up new,
‘loose’, models from such parts. We will see that the packed fragment is in a sense
tailored towards making this idea work.
The proof is structured as follows. We start by formally deﬁning mosaics and
some related concepts. After that we state the main result concerning the mosaic
method, namely the Mosaic Theorem stating that a packed formula is satisﬁable if
and only if there is a so-called linked set of mosaics for it, of bounded size. This



7.4 The Guarded Fragment
453
equivalence enables us to deﬁne our decision algorithm and establish the com-
plexity upper bounds mentioned in Theorem 7.34. We then continue to prove the
Mosaic Theorem. In doing so we obtain the loose model property for the packed
fragment as a spin-off.
For a formal deﬁnition of the concept of a mosaic we ﬁrst need some syntactic
preliminaries. Given a ﬁrst-order formula
, we let
V
ar
(
) and
F
r
e
e
(
) denote
the sets of variables and free variables occurring in
, respectively. Let
V be a
set of variables. A
V -substitution is any partial map

:
V
!
V . The result of
performing the substitution
 on the formula
 is denoted by
 
. (We can and
may assume that such substitutions can be carried out without increasing the total
number of variables involved; more precisely, we assume that if
V
ar
( 
)

V then
V
ar
( 

)

V .)
As usual, we will employ a notion of closure to delineate a ﬁnite set of relevant
formulas, that is formulas that for some reason critically inﬂuence the truth of a
given formula
. Let the single negation
 of a formula
 denote the formula
 
if
 is of the form
: ; otherwise,
 is the formula
:; we say that a set
 of
formulas is closed under single negations if

2
 whenever

2
.
Deﬁnition 7.35 Let
 be a set of packed formulas in the set
V of variables.
We call

V -closed if it is closed under subformulas, single negations and
V -
substitutions (that is, if
 belongs to
, then so does
 
 for every
V -substitution
). With
Cl
g
(
) we denote the smallest
V
ar
(
)-closed set of formulas containing
.
a
For the remainder of this section, we ﬁx a packed formula
 — all deﬁnitions to
come should be understood as being relativized to
. The number of variables oc-
curring in
 (free or bound) is denoted by
k; that is,
k is the size of
V
ar
(
). It
can easily be veriﬁed that the sets of guarded and packed formulas are both closed
under taking subformulas; hence, the set
Cl
g
(
) consists of guarded (packed, re-
spectively) formulas. An easy calculation shows that the cardinality of
Cl
g
(
) is
bounded by
k
k

(2j
j
).
The following notion is the counterpart of the atoms that we have met in earlier
decidability proofs (see Lemma 6.29, for instance). All three deﬁning conditions
are fairly obvious.
Deﬁnition 7.36 Let
X

V
ar
(
) be a set of variables. An
X-type is a set
 
Cl
g
(
) with free variables in
X satisfying, for all formulas

^
 ,

,
 in
Cl
g
(
)
with free variables in
X, the conditions (i)

^
 
2
  iff

2
  and
 
2
 ,
(ii)

62
  iff


2
  and (iii) if
;
x
i
=
x
j
2
  then


2
  for any substitution
 mapping
x
i to
x
j and/or
x
j to
x
i, while leaving all other variables ﬁxed.
a
The next deﬁnition introduces our key tool in proving the decidability of the packed



454
7 Extended Modal Logic
fragment: mosaics and linked sets of them. Basically, a mosaic consists of a subset
X of
V
ar
(
) together with a set
  encoding the relevant information on some
small part of a model. Here ‘small’ means that its size is bounded by the number of
objects that can be named using variables in
X, and ‘relevant’ refers to all formulas
in
Cl
g
(
) whose free variables are in
X. It turns out that a ﬁnite set of such mosaics
contains sufﬁcient information to construct a model for
 provided that the set links
the mosaics together in a nice way. Here is a more formal deﬁnition.
Deﬁnition 7.37 A mosaic is a pair
(X
;
 ) such that
X

V
ar
(
) and
 
Cl
g
(
).
A mosaic is coherent if it satisﬁes the following conditions:
(C1)
  is an
X-type,
(C2)
if
 
(x
;
z
) and

(x;
z
) are in
 , then so is
9y
(
(x;
y
)
^
 
(x
;
y
)),
(provided that the latter formula belongs to
Cl
g
(
)).
A link between two mosaics
(X
;
 ) and
(X
0
;
 0
) is a renaming (that is, an injec-
tive substitution)
 with
dom


X and
range


X
0 which satisﬁes, for all
formulas

2
Cl
g
(
):

2
  iff


2
 0.
A requirement of a mosaic is a formula of the form
9y
(
(x
;
y
)
^
 
(x;
y
)) be-
longing to
 . A mosaic
(X
0
;
 0
) fulﬁlls the requirement
9y
(
(x;
y
)
^
 
(x;
y
))
of a mosaic
(X
;
 ) via the link
 if for some variables
u,
v in
X
0 we have that

(x)
=
u and

(u
;
v
) and
 
(u
;
v
) belong to
 0. A set
S of mosaics is linked if
every requirement of a mosaic in
s is fulﬁlled via a link to some mosaic in
S.
S is
a linked set of mosaics for
 if it is linked and

2
  for some
(X
;
 ) in
S.
a
Note that a mosaic
(X
;
 ) may fulﬁll its own requirements, either via the identity
map or via some other map from
X to
X.
The key result concerning mosaics is the following Mosaic Theorem.
Theorem 7.38 (Mosaic Theorem) Let
 be a packed formula. Then
 is satisﬁ-
able if and only if there is a linked set of mosaics for
.
Proof. The hard, right to left, direction of the theorem is treated in Lemma 7.39
below; here we only prove the other direction.
Suppose that
 is satisﬁed in the model
A
=
(A;
I
). In a straightforward way
we can ‘cut out’ from
A a linked set of mosaics for
. Consider the set of partial
assignments of elements in
A to variables in
V
ar
(
). For each such
, let
(X

;
 
)
be the mosaic given by
X

=
dom
 and
 
=
f
2
Cl
g
(
)
j
A
j
=
[]g:
We leave it to the reader to verify that this collection forms a linked set of mosaics
for
.
a



7.4 The Guarded Fragment
455
When establishing the hard direction of this proposition we will in fact prove some-
thing stronger: starting from a linked set of mosaics for a formula
 we will show,
via a step by step argument, that there is a loose or tree-like model for
. First
however, we want to show that the Mosaic Theorem is the key towards proving
the decidability of the packed fragment, and also for ﬁnding an upper bound for its
complexity.
The decision algorithm and its complexity
The mosaic theorem tells us that any packed formula
 is satisﬁable if and only if
there is a linked set of mosaics for
. Thus an algorithm answering the question
whether a linked set of mosaics exists for
, also decides whether
 is satisﬁable.
By providing such an algorithm we establish the upper complexity bound for the
satisﬁability problem of the packed fragment.
Recall that
k denotes the number of variables occurring in
. The following
observations are fairly straightforward consequences of our deﬁnitions:
(i) up to isomorphism there are at most
2
k

2
2j
jk
k mosaics. Using the big
O
notation, this is at most
2
O
(j
j)2
k
log
k.
(ii) given sets
X
;
  with
jX
j

k and
 
Cl
g
(
) it is decidable in time
polynomial in
k
k and
j
j whether
(X
;
 ) is a coherent mosaic.
(iii) given a set
X of coherent mosaics and a requirement
(x
) it is decidable in
time polynomial in
jX
j and
j(x
)j whether
X fulﬁlls the requirement
(x).
Using methods similar to the elimination of Hintikka sets that we saw in the de-
cidability proof for propositional dynamic logic (see Section 6.8), we now give an
algorithm which decides the existence of a linked set of mosaics for
. Let
S
0 be
the set of all coherent mosaics. By the observations above,
S
0 contains at most
2
O
(j
j)2
k
log
k elements and can be constructed in time polynomial in
jS
0
j. We now
inductively construct a sequence of sets of mosaics
S
0

S
1

S
2

S
3


. If
every requirement of a mosaic
 in a set
S
i is fulﬁlled we call
 happy. If every
mosaic in
S
i is happy then return ‘there is a linked set of mosaics for
’ if
S
i con-
tains a mosaic
(X
;
 ) with

2
 , and return ‘there is no linked set of mosaics for
’ otherwise. If, on the other hand,
S
i contains unhappy mosaics, let
S
i+1 consist
of all happy mosaics in
S
i and continue the construction. Since our sets decrease in
size at every step, the construction must halt after at most
jS
0
j many stages. By the
observations above, computing which states in
S
i are happy can be done in time
polynomial in
 and
jS
i
j. Thus the entire computation can be performed in time
polynomial in
jS
0
j. Clearly the algorithm is correct.
Hence, if we consider a formula
 in a packed fragment with a ﬁxed number of
variables,
jS
0
j is exponential in
j
j. In general however, the number of variables
occurring in a formula depends on the formula’s length and hence in general,
jS
0
j



456
7 Extended Modal Logic
is doubly exponential in
j
j. Thus, pending the correctness of Lemma 7.39 below,
this establishes the complexity upper bounds in the Theorem 7.34.
Loose models
Finally, we show the hard direction of the Mosaic Theorem; as a spin-off we estab-
lish the ‘loose model property’ mentioned in Theorem 7.33.
Lemma 7.39 Let
 be a packed formula. If there is a linked set of mosaics for
,
then
 is satisﬁable in a loose model of degree
jV
ar
(
)
j.
Proof. Assume that
S is a linked set of mosaics for
. Using a step-by-step con-
struction, we will build a loose model for
, together with an acyclic graph asso-
ciated with the model. At each stage of the construction we will be dealing with
some kind of approximation of the ﬁnal model and tree; these approximations will
be called networks and are slightly involved structures.
A network is a quintuple
(A;
G;
;
;

) such that
A
=
(A;
I
) is a model for
the ﬁrst-order language;
G
=
(G;
E
) is a connected, directed and acyclic graph;

:
G
!
S is a map associating a mosaic

t
=
(X
t
;
 t
) in
S with each node
t of
the graph;
 is a map associating an assignment

t
:
X
t
!
A with each node
t of
the graph; and ﬁnally,
 is a map associating with each edge
(t;
t
0
) of the graph a
link

tt
0 from

t to

t
0 (we will usually simplify our notation by writing
 instead
of

tt
0).
The idea is that each mosaic

t is meant to give a complete description of the
relevant requirements that we impose on a small part of the model-to-be. Which
part? This is given by the assignment

t. And the word ‘relevant’ refers to the
fact that we are only interested in the formulas inﬂuencing the truth of
; that is,
the formulas in
Cl
g
(
). The links between neighboring mosaics are there to ensure
that distinct mosaics agree on the part of the model that they both have access to.
Now obviously, if we want all of this to work properly we have to impose some
conditions on networks. In order to formulate these, we need some auxiliary no-
tation. For a subset
Q

A, let
L(Q) denote the set of nodes in
G that have
‘access’ to
Q; formally, we deﬁne
L(Q)
=
ft
2
G
j
A

range
(
t
)g. For a
tuple
a
=
(a
1
;
:
:
:
;
a
n
) of elements in
A we set
L(a)
=
L(fa
1
;
:
:
:
;
a
n
g). Now
a network is called coherent if it satisﬁes the following conditions (all to be read
universally quantiﬁed):
(C1)
P
x
2
 t iff
A
j
=
P
x[
t
],
(C2)
x
i
=
x
j
2
 t iff

t
(x
i
)
=

t
(x
j
),
(C3)
L(Q) is non-empty for every guarded set
Q

A,
(C4)
L(Q) is connected for every guarded set
Q

A,
(C5)
if
E
tt
0 then

tt
0
(x)
=
x
0 iff

t
(x)
=

t
0
(x
0
).



7.4 The Guarded Fragment
457
A few words of explanation about these conditions: (C1) and (C2) ensure that ev-
ery mosaic is a complete description of the atomic formulas holding in the part of
the model it refers to. Condition (C3) states that no live tuple of the model remains
unseen from the graph, while the conditions (C4) and (C5) are the crucial ones
making that remote parts of the graph cannot contain contradictory information
about the model — how this works precisely will become clear further on. Note
that condition (C5) has two directions: the left-to-right direction states that neigh-
boring mosaics have common access to part of the model, while the other direction
ensures that they agree on their requirements concerning this common part.
The motivation for using these networks is that in the end we want any formula
(x)
2
Cl
g
(
) to hold in
A under the assignment

t if and only
(x
) belongs
to
 t. Coherence on its own is not sufﬁcient to make this happen. A defect of
a network consists of a formula
9y
(
(x
;
y
)
^
 
(x
;
y
)) which is a requirement of
the mosaic

t for some node
t while there is no neighboring node
t
0 such that

t
0
fulﬁlls
9y
(
(x
;
y
)
^
 
(x;
y
)) via the link

tt
0. A coherent network
N is perfect if
it has no defects. We say that
N is a network for
 if for some
t
2
G,

t
=
(X
t
;
 t
)
is such that

2
 t.
Claim 1 If
N
=
(A;
G;
;
;

) is a perfect network, then
(i)
A is a loose model of degree
jV
ar
(
)
j, and
(ii) for all formulas
(x
)
2
Cl
g
(
) and all nodes
t of
G:

2
 t iff
A
j
=
[
t
].
Proof of Claim. For part (i) of the claim, let
N
=
(A;
G;
;
;

) be the perfect
network for
. Let
A
=
(A;
I
). As the function
f mapping nodes of
G to subsets
of
A, simply take the map that assigns the range of

t to the node
t. Since the
domain of each map

t is always a subset of
V
ar
(
), it follows immediately that
f
(t) will always be a set of size at most
jV
ar
(
)
j. Now take an arbitrary live tuple
s in
A; it follows from (C3) and (C4) that
L(s
) is a non-empty and connected part
of the graph
G. Thus
A is a loose model of degree
jV
ar
(
)
j.
We prove part (ii) of the claim by induction on the complexity of
. For atomic
formulas the claim follows by conditions (C1) and (C2), and the boolean case of
the induction step is straightforward (since
 t is an
X–type) and left to the reader.
We concentrate on the case that
(x) is of the form
9y
(
(x;
y
)
^
 
(x
;
y
)).
First assume that
(x)
2
 t. Since
N is perfect there is a node
t
0 in
G and
variables
u,
v in
X
t
0 such that
E
tt
0,

(u
;
v
) and
 
(u
;
v
) belong to
 t
0, while the
link
 from

t to

t
0 maps
x to
u. By the induction hypothesis we ﬁnd that
A
j
=

(u
;
v
)
^
 
(u
;
v
)[
t
0
]:
(7.6)
But from condition (C5) it follows that

t
0
(x
)
=

t
(u), whence (7.6) implies that
A
j
=
9y
(
(x;
y
)
^
 
(x
;
y
))[
t
];



458
7 Extended Modal Logic
which is what we were after.
Now suppose, in order to prove the converse direction, that
A
j
=
(x
)[
t
]. Let
a
denote

t
(x), then there are
b in
A such that
A
j
=

(x
;
y
)[a
b] and
A
j
=
 
(x;
y
)[ab].
Our ﬁrst aims are to prove that
L(a
b)
6=
?;
(7.7)
and
L(Q) is connected for every
Q

fa
;
bg:
(7.8)
Note that if we are working in the guarded fragment, then

(x;
y
) is an atomic
formula, whence it follows from
A
j
=

(x;
y
)[a
b] that
ab is live. Thus
fa;
b
g is
guarded, and hence (7.7) is immediate by condition (C3). In fact, every
Q

fa;
b
g
is guarded in this case, so (7.8) is immediate by condition (C4).
In the more general case of the packed fragment we have to work a bit harder.
First, observe that it does follow from
A
j
=

(x;
y
)[a
b] and the conditions on

(x;
y
) in the deﬁnition of packed quantiﬁcation, that
fc;
dg is guarded, and thus,
L(c;
d)
6=
?, for every pair
(c;
d) of points taken from
ab. It follows from (C4) that
fL(c;
d)
j
c;
d taken from
abg is a collection of non-empty, connected, pairwise
overlapping subgraphs of the acyclic graph
G. It is fairly straightforward to prove,
for instance, by induction on the size of the graph
G, that any such collection must
have a non-empty intersection. From this, (7.7) and (7.8) are almost immediate.
Thus, we may assume the existence of a node
t
0 in
G such that
fa
;
bg

range

t
0.
Let
u and
v in
X
t
0 be the variables such that

t
0
(u)
=
a and

t
0
(v
)
=
b. The
induction hypothesis implies that

(u;
v
) and
 
(u
;
v
) belong to
 t
0, whence
(u)
2
 t
0 by coherence of

t
0. Since both
t and
t
0 belong to
L(a), it follows from (7.8)
that there is a path from
t to
t
0 within
L(a), say
t
0
=
s
0
E
s
1
E
:
:
:
E
s
n
=
t. Let

i
be the link between the mosaics of
s
i and
s
i+1, and deﬁne
 to be the composition
of these maps. It follows by an easy inductive argument on the length of the path
that
 is a link between

t
0 and

t such that
(u
)
=
x. Hence, by deﬁnition of a
link we have that
(x)
2
 t
0.
a
By Claim 1, in order to prove the Lemma it sufﬁces to construct a perfect network
for
. This construction uses a step-by-step argument; to start the construction we
need some coherent network for
.
Claim 2 There is a coherent network for
.
Proof of Claim. By our assumption on
 there is a coherent mosaic

=
(X
;
 )
such that

2
 . Without loss of generality we may assume that
X is the set
fx
1
;
:
:
:
;
x
n
g (otherwise, take an isomorphic copy of
 in which
X does have this
form). Let
a
1
;
:
:
:
;
a
n be a list of objects such that for all
i and
j we have that
a
i
=
a
j if and only if the formula
x
i
=
x
j belongs to
 . Deﬁne
A
=
fa
1
;
:
:
:
;
a
n
g



7.4 The Guarded Fragment
459
and put the tuple
(a
i
1
;
:
:
:
;
a
i
k
) in the interpretation
I
(P
) of the
k-ary predicate
symbol
P precisely if
P
x
i
1
:
:
:
x
i
n
2
 . Let
A be the resulting model
(A;
I
) and
deﬁne
G as the trivial graph with one node
0 and no edges. Let
(0) be the mosaic
;

0
:
X
!
A is given by
(x
i
)
=
a
i; and ﬁnally,

00 is the identity map from
X to
X.
We leave it to the reader to verify that the quintuple
(A;
G;
;
;

) is a coherent
network for
.
a
The crucial step of this construction will be to show that any defect of a coherent
network can be repaired.
Claim 3 For any coherent network
N
=
(A;
G;
;
;

) and any defect of
N there
is a coherent network
N
+ extending
N and lacking this defect.
Proof of Claim. Suppose that
(x) is a defect of
N because it is a requirement of
the mosaic

t and not fulﬁlled by any neighboring mosaic

t
0. We will deﬁne an
extension
N
+ of
N in which this defect is repaired.
Since
S is a linked set of mosaics and

t belongs to
S,

t is linked to a mosaic
(X
0
;
 0
)
2
S in which the requirement is fulﬁlled via some link
. Let
Y be
the set of variables in
X
0 that do not belong to the range of
; suppose that
Y
=
fy
1
;
:
:
:
;
y
k
g (with all
y
i being distinct). For the sake of a smooth presentation,
assume that
 0 contains the formulas
:x
0
=
y for all variables
x
0
2
X
0 and
y
2
Y
(this is not without loss of generality — we leave the general case as an exercise
to the reader). Take a set
fc
1
;
:
:
:
;
c
k
g of fresh objects (that is, no
c
i is an element
of the domain
A of
A), and let
 be the assignment with domain
X
0 deﬁned as
follows:

(x
0
)
=


t
(x)
if
x
0
=
(x);
c
i
if
x
0
=
y
i
;
and let
t
0 be an object not belonging to
G. Now deﬁne the network
N
+
=
(A
+,
G
+,

+
;

+
;

+
) as follows:
A
+
=
A
[
fc
1
;
:
:
:
;
c
k
g;
I
+
(P
)
=
I
(P
)
[
fd
j for some
x,
d
=

(x) and
P
x
2
 0
g;
G
+
=
G
[
ft
0
g;
E
+
=
E
[
f(t;
t
0
)g;
while

+,

+ and

+ are given as the obvious extensions of
,
 and
, namely
by putting

+
t
0
=
(X
0
;
 0
),

+
t
0
=
 and

tt
0
=
.
Since the interpretation
I
+ agrees with
I on ‘old’ tuples it is a straightforward
exercise to verify that the new network
N
+ satisﬁes the conditions (C1)–(C3) and
(C5).
In order to check that condition (C4) holds, take some guarded subset
Q from



460
7 Extended Modal Logic
A
+; we will show that
L
+
(Q) is a connected subgraph of
G
+. It is rather easy
to see that
L
+
(Q) is identical to either
L(Q) or
L(Q)
[
ft
0
g; hence by the con-
nectedness of
L(Q) it sufﬁces to prove, on the assumptions that
t
0
2
L
+
(Q) and
L(Q)
6=
?, that
t
2
L(Q). Hence, suppose that
t
0
2
L
+
(Q); that is, each
a
2
Q
is in the range of
. But if
L(Q)
6=
?, each such point
a must be old; hence, by
deﬁnition of
, each
a
2
Q must belong to
range

t. This gives that
t
2
L(Q), as
required.
a
As in our earlier step-by-step proofs, the previous two claims show that using some
standard combinatorics we can construct a chain of networks such that their limit
is a perfect network. This completes the proof of the lemma.
a
Exercises for Section 7.4
7.4.1 In the loosely guarded fragment the following quantiﬁcation patterns are allowed:
9x(
(x
;
y
)
^
 
(x
;
y
)) is a loosely guarded formula if
 
(x
;
y
) is loosely guarded,

(x
;
y
)
is a conjunction as in the packed fragment, and any pair
z,
z
0 of distinct variables from
x
y
occurs free in some conjunct of the guard
, unless
z and
z
0 are both from
y. For example,
9x
((R
y
x
^
R
xy
0
)
^
:C
xy
y
0
) is loosely guarded, but not packed since there is no conjunct
having both
y and
y
0 free.
Show that for every loosely guarded sentence
 there exists an equivalent packed sen-
tence

0 in the same language.
7.4.2 Deﬁne the universal packed fragment as the fragment of ﬁrst-order logic that is gen-
erated from atoms, negated atoms, conjunction, disjunction, ordinary existential quantiﬁ-
cation, and packed universal quantiﬁcation. (With the latter we mean that
8x
(
!
 
) is
in the fragment if
 is universally packed,
 packs its own free variables, and
F
r
e
e
( 
)

F
r
e
e
(
).)
Show that satisﬁability is decidable for the universal packed fragment.
7.4.3 Fix a natural number
n, and suppose that we are working in an
n-bounded ﬁrst-order
signature; that is, all predicate symbols have arity at most
n. Prove that in such a signature,
every guarded sentence is equivalent to a guarded sentence using at most
n variables. Does
this hold for packed sentences as well? What are the consequences for the complexity of
the respective satisﬁability problems?
7.4.4 Let
 be a packed formula, and suppose that
 is satisﬁable. Prove that
 is satisﬁable
in a loose model with an associated graph
G of which the out-degree is bounded by some
recursive function on
. In particular, this out-degree should be ﬁnite. (The out-degree of
a node
k of a graph
(G;
E
) is deﬁned as the number of its neighbors, or, formally, as the
size of the set
fk
0
2
G
j
k
E
k
0
g; the out-degree of a graph is deﬁned as the supremum of
the out-degrees of the individual nodes.)
7.5 Multi-Dimensional Modal Logic
In Chapter 2 we backed up our claim that logical formalisms do not live in isola-
tion by developing the correspondence theory of modal logic: we studied modal



7.5 Multi-Dimensional Modal Logic
461
languages as fragments of ﬁrst-order languages. In this section we will turn the
looking glass around and examine ﬁrst-order logic as if it were a modal formalism.
The basic observations enabling this perspective are that we may view assignments
(the functions that give ﬁrst-order variables their value in a ﬁrst-order structure) as
states of a modal model, and that this makes standard ﬁrst-order quantiﬁers behave
just like modal diamonds and boxes. First-order logic thus forms an example of
a multi-dimensional modal system. Multi-dimensional modal logic is a branch of
modal logic dealing with special relational structures in which the states, rather
than being abstract entities, have some inner structure. More speciﬁcally, these
states are tuples or sequences over some base set, in our case, the domain of the
ﬁrst-order structure. Furthermore, the accessibility relations between these states
are (partly) determined by this inner structure of the states.
Reverse correspondence theory
To simplify our presentation, in this section we will not treat modal versions of
ﬁrst-order logic in general, but restrict our attention to certain ﬁnite variable frag-
ments. A precise deﬁnition of these fragments will be given later on (see Deﬁni-
tion 7.40). For the time being, we ﬁx a natural number
n

2 and invite the reader
to think of a ﬁrst-order language with equality, but without constants or function
symbols, in which all predicates are
n-adic. Consider the basic declarative state-
ment in ﬁrst-order logic concerning the truth of a formula in a model under an
assignment
s:
M
j
=

[s]:
(7.9)
The basic observation underlying our approach, is that we can read (7.9) from a
modal perspective as: ‘the formula
 is true in
M at state
s’. But since we have
only
n variables at our disposal, say
v
0, . . . ,
v
n 1, we can identify assignments
with maps:
n
(=
f0;
:
:
:
;
n
 1g)
!
U, or equivalently, with
n-tuples over the
domain
U of the structure
M — we will denote the set of such
n-tuples by
U
n.
But then we ﬁnd ourselves in the setting of multi-dimensional modal logic: the
universe of our modal models will be of the form
U
n for some base set
U. Now
recall that the truth deﬁnition of the quantiﬁers reads as follows:
M
j
=
9v
i
[s] iff there is an
u
2
U such that
M
j
=

[s
i
u
],
where
s
i
u is the assignment deﬁned by
s
i
u
(k
)
=
u if
k
=
i and
s
i
u
(k
)
=
s(k
) other-
wise. We can replace the above truth deﬁnition with the more ‘modal’ equivalent,
M
j
=
9v
i
[s] iff there is an assignment
s
0 with
s

i
s
0 and
M
j
=

[s
0
];
where

i is given by
s

i
s
0 iff for all
j
6=
i,
s
j
=
s
0
j.
(7.10)



462
7 Extended Modal Logic
In other words: existential quantiﬁcation behaves like a modal diamond, having

i
as its accessibility relation.
Since the semantics of the boolean connectives in the predicate calculus is the
same as in modal logic, this shows that the inductive clauses in the truth deﬁnition
of ﬁrst-order logic neatly ﬁt a modal mould. So let us now concentrate on the
atomic formulas. To start with, we observe that equality formulas do not cause any
problem: the formula
v
i
=
v
j, with truth deﬁnition
M
j
=
v
i
=
v
j
[s] iff
s
2
Id
ij
;
can be seen as a modal constant. Here
Id
ij is deﬁned by
s
2
Id
ij iff
s
i
=
s
j
:
(7.11)
The case of the other atomic formulas is more involved, however. Since we con-
ﬁned ourselves to the calculus of
n-adic relations and do not have constants or func-
tion symbols, our atomic predicate formulas are of the form
P
v

(0)
:
:
:
v

(n 1).
Here
 is an
n-transformation, that is, a map:
n
!
n. In the model theory of ﬁrst-
order logic the predicate symbol
P will be interpreted as a subset of
U
n; but this is
precisely how modal valuations treat propositional variables in models where the
universe is of the form
U
n! Therefore, we can identify the set of propositional vari-
ables of the modal formalism with the set of predicate symbols of our ﬁrst-order
language. In this way, we obtain a modal reading of (7.9) for the case where
 is the
atomic formula
P
v
0
:
:
:
v
n 1:
M
j
=
P
v
0
:
:
:
v
n 1
[s] iff
s belongs to the interpreta-
tion of
P. However, as a consequence of this approach our set-up will not enjoy a
one-to-one correspondence between atomic ﬁrst-order formulas and atomic modal
ones: the atomic formula
P
v

(0)
:
:
:
v

(n 1) will correspond to the modal atom
p
only if
 is the identity function on
n. For the cases where
 is not the identity map
we still have to ﬁnd some kind of solution. There are many options here.
Since we are working in a ﬁrst-order language with equality, atomic formulas
with a multiple occurrence of a variable can be rewritten as formulas with only
‘unproblematic’ atomic subformulas, for instance
P
v
1
v
0
v
0

9v
2
(v
2
=
v
0
^
P
v
1
v
2
v
2
)

9v
2
(v
2
=
v
0
^
9v
0
(v
0
=
v
1
^
P
v
0
v
2
v
2
))

9v
2
(v
2
=
v
0
^
9v
0
(v
0
=
v
1
^
9v
1
(v
1
=
v
2
^
P
v
0
v
1
v
2
))):
This leaves the case what to do with atoms of the form
P
v

(0)
:
:
:
v

(n 1), where

is a permutation of
n, or in other words, atomic formulas where variables have been
substituted simultaneously. The previous trick does not work here: for example, to
write an equivalent of the formula
P
v
1
v
0
v
2 one needs extra variables as buffers,
for instance, when replacing
P
v
1
v
0
v
2 by
9v
3
9v
4
(v
3
=
v
0
^
v
4
=
v
1
^
9v
0
9v
1
(v
0
=
v
4
^
v
1
=
v
3
^
P
v
0
v
1
v
2
)):



7.5 Multi-Dimensional Modal Logic
463
One might consider a solution where a predicate
P is translated into various modal
propositional variables
p
, one for every permutation
 of
n, but this is not very
elegant. One might also forget about simultaneous substitutions and conﬁne one-
self to a fragment of
n-variable logic where all atomic predicate formulas are of the
form
P
v
0
:
:
:
v
n 1 — this fragment of restricted ﬁrst-order logic is deﬁned below.
A third solution is to take substitution seriously, so to speak, by adding special
‘substitution operators’ to the language. The crucial observation is that for any
transformation

2
n
n, we have that
M
j
=
P
v

(0)
:
:
:
v

(n 1)
[s] iff
M
j
=
P
v
0
:
:
:
v
n 1
[s
Æ

];
(7.12)
where
s
Æ
 is the composition of
 and
s (recall that
s is a map:
n
!
U). So, if
we deﬁne the relation
1


U
n

U
n by
s
1

t iff
t
=
s
Æ

;
(7.13)
we have rephrased (7.12) in terms of an accessibility relation (in fact, a function):
M
j
=
P
v

(0)
:
:
:
v

(n 1)
[s] iff
M
j
=
P
v
0
:
:
:
v
n 1
[t] for some
t with
s
1

t:
So if we add an operator

 to the modal language for every
n-transformation

in
n
n, with
1
 as its intended accessibility relation, we have found the desired
modal equivalent for any atomic formula
P
v

(0)
:
:
:
v

(n 1), namely in the form


p. (As a special case, for the formula
P
v
0
:
:
:
v
n 1 one can take the identity
map on
n.)
Deﬁnition 7.40 Let
n be an arbitrary but ﬁxed natural number. The alphabet of
L
n and of
L
r
n consists of a set of variables
fv
i
j
i
<
ng, a countable set of
n-adic
relation symbols (P
0
;
P
1
;
:
:
:), equality (=), the boolean connectives
:;
_ and the
quantiﬁers
9v
i. The collection of formulas is deﬁned as usual in ﬁrst-order logic,
with the restriction that the atomic formulas of
L
r
n are of the form
v
i
=
v
j or
P
l
(v
0
:
:
:
v
n 1
); for
L
n we allow all atomic formulas (but note that all predicates
are of arity
n).
A ﬁrst-order structure for
L
n (L
r
n) is a pair
M
=
(U;
V
) such that
U is a set
called the domain of the structure and
V is an interpretation function mapping
every
P to a subset of
U
n. The notion of a formula
 being true in a ﬁrst-order
structure
M under an assignment
s is deﬁned as usual. For instance, given our
notation we have, for any atomic formula:
M
j
=
P
(v
0
:
:
:
v
n 1
)
[s]
if
s
2
V
(P
);
M
j
=
P
(v

(0)
:
:
:
v

(n 1)
)
[s]
if
s
Æ

(=
(s

(0)
:
:
:
s

(n 1)
))
2
V
(P
):
An
L
n-formula
 is true in
M (notation:
M
j
=
), if
M
j
=

[s] for all
s
2
U
n;



464
7 Extended Modal Logic
it is valid (notation:
j
=
fo
), if it is true in every ﬁrst-order structure of
L
n. The
same deﬁnition applies to
L
r
n.
a
From now on, we will concentrate on the modal versions of
L
r
n and
L
n, which are
given in the following deﬁnition:
Deﬁnition 7.41 Let
n be an arbitrary but ﬁxed natural number.
MLR
n (short for:
modal language of relations) is the modal similarity type having constants
Æ
ij and
diamonds
3
i,

 (for all
i;
j
<
n;

2
n
n).
CML
n, the similarity type of cylindric
modal logic, is the fragment of
MLR
n-formulas in which no substitution operator

 occurs.
A ﬁrst-order structure
M
=
(U;
V
) can be seen as a modal model based on the
universe
n
U, and formulas of these modal similarity types are interpreted in such a
structure in the obvious way; for instance, we have
M;
s

Æ
ij
iff
s
i
=
s
j
M;
s




iff
M;
s
Æ



(iff
there is a
t with
s
1

t and
M;
t

)
M;
s

3
i

iff
there is a
t with
s

i
t and
M;
t


:
If an
MLR
n-formula
 holds throughout any ﬁrst-order structure, we say that it is
ﬁrst-order valid, notation:
C
n

 (this notation will be clariﬁed further on).
a
The modal disguise of
L
n in
MLR
n and of
L
r
n in
CML is so thin, that we give the
translations mapping ﬁrst-order formulas to modal ones without further comments.
Deﬁnition 7.42 Let
()
t be the following translation from
L
n to
MLR
n:
(P
v

(0)
:
:
:
v

(n 1)
)
t
=


p
(v
i
=
v
j
)
t
=
Æ
ij
(:)
t
=
:
t
(
_
 
)
t
=

t
_
 
t
(9v
i
)
t
=
3
i

t
:
a
This translation allows us to see
L
r
n and
CML
n as syntactic variants:
()
t is easily
seen to be an isomorphism between the formula algebras of
L
r
n and
CML
n. Note
that in the case of
L
n versus
MLR
n, we face a different situation: where in
MLR
the simultaneous substitution of two variables for each other is a primitive operator,
in ﬁrst-order logic it can only be deﬁned by induction. Nevertheless, we could
easily deﬁne a translation mapping
MLR
n-formulas to equivalent
L
r
n-formulas. In
any case, the following proposition shows that we really have developed a reverse
correspondence theory; we leave the proof as an exercise to the reader.
Proposition 7.43 Let
 be a formula in
L
n, then



7.5 Multi-Dimensional Modal Logic
465
(i) for any ﬁrst-order structure
M, and any
n-tuple/assignment
s, we have that
M
j
=
[s] if and only if
M;
s


t;
(ii) as a corollary, we have that
j
=
fo

(
)
C
n


t.
Let us now put the modal machinery to work and see whether we can ﬁnd out
something new about ﬁrst-order logic.
Degrees of validity
Perhaps the most interesting aspect of this modal perspective on ﬁrst-order logic is
that it allows us to generalize the semantics of ﬁrst-order logic, and thus offers a
wider perspective on the standard Tarskian semantics. The basic idea is fairly ob-
vious: now that we are talking about modal languages, it is clear that the ﬁrst-order
structures of Deﬁnition 7.41 are very speciﬁc modal models for these languages.
We may abstract from the ﬁrst-order background of these models, and consider
modal models in which the universe is an arbitrary set and the accessibility rela-
tions are arbitrary relations (of the appropriate arity).
Deﬁnition 7.44 A
MLR
n-frame is a tuple
(W
;
T
i
;
E
ij
;
F

)
i;j
<n;
2n
n such that ev-
ery
E
ij is a subset of the universe
W, and such that every
T
i and every
F
 is a bi-
nary relation on
W. A
MLR
n-model is a pair
M
=
(F;
V
) with
F a
MLR
n-frame
and
V a valuation, that is, a map assigning subsets of
W to propositional variables.
CML
n-models and frames are deﬁned likewise.
a
For such models, truth of a formula at a state is deﬁned via the usual modal induc-
tion, for instance:
M;
w



 iff there is a
v with
F

w
v and
M;
v

:
In this very general semantics, states (that is, elements of the universe) are no
longer real assignments, but rather, abstractions thereof. First-order logic now re-
ally has become a poly-modal logic, with quantiﬁcation and substitution diamonds.
It is interesting and instructive to see how familiar laws of the predicate calculus
behave in this new set-up. For example, the axiom schema

!
9v
i
 will be valid
only in
n-frames where
T
i is a reﬂexive relation (this follows from the fact that the
modal formula
p
!
3
i
p corresponds to the frame condition
8xT
i
xx). Likewise,
the axiom schemes
9v
i
9v
i

!
9v
i
 and

!
8v
i
9v
i
 will be valid only in frames
where the relation
T
i is transitive and symmetric, respectively.
Later on we will see more of such correspondences; the point to be made here
is that the abstract perspective on the semantics of ﬁrst-order logic imposes a cer-
tain ‘degree of validity’ on well-known theorems of the predicate calculus. Some
theorems are valid in all abstract assignment frames, like distribution:
8v
i
(
!
 
)
!
(8v
i

!
8v
i
 
);



466
7 Extended Modal Logic
which is nothing but the modal
K-axiom. Other theorems of the predicate cal-
culus, like the ones mentioned above, are only valid in some classes of frames.
Narrowing down the class of frames means increasing the set of valid formu-
las, and vice versa. In particular, we now have the option to look at classes of
frames that are only slightly more general than the standard ﬁrst-order structures,
but have much nicer computational properties. This new perspective on ﬁrst-order
logic, which was inspired by the literature on algebraic logic, provides us with
enormous freedom to play with the semantics for ﬁrst-order logic. In particu-
lar, consider the fact that ﬁrst-order structures can be seen as frames of the form
(U
n
;

i
;
I
d
ij
;
1

)
i;j
<n;
2n
n where all assignments
s
2
U
n are available. But why
not study a semantics where states are still real assignments on the base set
U, but
not all such assignments are available?
There are at least two good reasons to make such a move. First, it turns out that
the logic of such generalized assignment frames has much nicer meta-properties
than the logic of the cubes such as decidability, see for instance Theorem 7.46
below. These logics will provide less laws than the usual predicate calculus, but
their supply of theorems may be sufﬁcient for particular applications. Note for
instance, that the schemes

!
9v
i
,
9v
i
9v
i

!
9v
i
 and

!
8v
i
9v
i
 are still
valid in every generalized assignment frame, since

i

W is always an equivalence
relation.
In some situations it may even be useful not to have all familiar validities. Con-
sider for instance the schema
9v
i
9v
j

!
9v
j
9v
i
:
(7.14)
It follows from correspondence theory that (7.14) is valid in a frame
F iff (7.15)
below holds in
F.
8xz
(9y
(T
i
xy
^
T
j
y
z
)
!
9u
(T
j
xu
^
T
i
uz
)):
(7.15)
The point is that the schema (7.14) disables us to make the dependency of vari-
ables explicit in the language (that is, whether
v
j is dependent of
v
i or the other
way around), while these dependencies play an important role in some proof-
theoretical approaches. So, the second motivation for generalizing the semantics
of ﬁrst-order logic is that it gives us a ﬁner sieve on the notion of equivalence
between ﬁrst-order formulas. Note for instance that (7.14) is not valid in frames
with assignment ‘holes’: take
n
=
2. In a square (that is, 2-cubic) frame we have
(a;
b)

0
(a
0
;
b)

1
(a
0
;
b
0
), but if
(a;
b
0
) is not an available tuple, then there is no
s such that
(a;
b)

1
s

0
(a
0
;
b
0
) — hence this frame will not satisfy (7.15). So,
the schema (7.14) will not be valid in this frame.
In this new paradigm, a whole landscape of frame classes and corresponding
logics arises. In the most general approach, any subset of
U
n may serve as the uni-
verse of a multi-dimensional frame, but it seems natural to impose restrictions on



7.5 Multi-Dimensional Modal Logic
467
the set of available assignments. Unfortunately, for reasons of space limitations we
cannot go into further detail here, conﬁning ourselves to the following deﬁnition.
Deﬁnition 7.45 Let
U be some set, and
W a set of
n-tuples over
U, that is,
W

U
n. The cube over
U or full assignment frame over
U is deﬁned as the frame
C
n
(U
)
=
(U
n
;

i
;
I
d
ij
;
1

)
i;j
<n;
2n
n
:
The
W-relativized cube over
U or
W-assignment frame on
U is deﬁned as the
frame
C
W
n
(U
)
=
(W
;

i

W
;
I
d
ij
\
W
;
1


W
)
i;j
<n;
2n
n
:
C
n and
R
n are the classes of cubes and relativized cubes, respectively.
a
Observe that this deﬁnition clariﬁes our earlier notation ‘C
n

’ for the fact that
the modal formula
 is ‘ﬁrst-order valid’.
Decidability
As we already mentioned, one of the reasons for developing the abstract and gen-
eralized assignment semantics is to ‘tame’ ﬁrst-order logic by looking for core
versions with nicer computational behavior. This idea is substantiated by the fol-
lowing theorem.
Theorem 7.46 It is decidable in exponential time whether a given
MLR
n-formula
is satisﬁable in a given relativized cube. As a corollary, the problem whether a
given ﬁrst-order formula in
L
n can be satisﬁed in a general assignment frame is
also decidable in exponential time.
Proof. This theorem can be proved directly by using the mosaic method that we
encountered in Section 6.4 — in fact, the mosaic method was developed for this
particular proof! However, space limitations prevent us from giving the mosaic
argument here. Therefore, we prove the theorem by a reduction of the
R
n satisﬁ-
ability problem to the satisﬁability problem of the
n-variable guarded fragment of
Section 7.4.
This reduction is quite interesting in itself: the key idea is that we ﬁnd a syntactic
counterpart to the semantic notion of restricting the set of available assignments.
There is in fact a very simple way of doing so, namely by introducing a special
n-adic predicate
G that will be interpreted as the collection of available assign-
ments. One can then translate modal formulas (or
L
n-formulas) into ﬁrst-order
ones, with the proviso that this translation is syntactically relativized to
G. The
formula
Gv
0
:
:
:
v
n 1 so to speak acts as a guard of the translated formula, and
indeed, it will be easily seen that the range of this translation formally falls inside
the guarded fragment.



468
7 Extended Modal Logic
Now for the technical details. Given a collection
 of propositional variables,
assume that with each
p
2
 we have an associated
n-adic predicate symbol
P.
Also, ﬁx a new
n-adic predicate symbol
G; let

+ denote the expanded signature
fP
j
p
2
g
[
fGg. Consider the following translation
()
 mapping
MLR
n-
formulas to ﬁrst-order formulas:
p

=
P
v
0
:
:
:
v
n 1
Æ

ij
=
v
i
=
v
j
(:)

=
Gv
0
:
:
:
v
n 1
^
:

(
^
 
)

=


^
 

(

)

=
(Gv
0
:
:
:
v
n 1
^


)

(3
i
)

=
9v
i
(Gv
0
:
:
:
v
n 1
^


)
Here, for a given transformation
,
()
 denotes the corresponding syntactic sub-
stitution operation on ﬁrst-order formulas.
We want to show the following claim.
Claim 1 For any
MLR
n-formula
 we have that
R
n

 if and only if the formula
Gv
0
:
:
:
v
n 1
!

 is a ﬁrst order validity.
Proof of Claim. In order to prove this claim, we need a correspondence between
modal models and ﬁrst-order models for the new language. Given a relativized
assignment model
M
=
(C
W
n
(U
);
V
), deﬁne the corresponding ﬁrst-order model
M
 as the structure
(U;
I
) where
I
(P
)
=
V
(p) for every propositional variable
p,
and
I
(G)
=
W. Conversely, given a ﬁrst-order structure
A
=
(A;
I
) for the ex-
panded ﬁrst-order signature
, let
A
 be the relativized cube model
(C
I
(G)
n
(A);
V
),
where the valuation
V is given by
V
(p)
=
I
(P
).
For any relativized assignment model
M, and any available assignment
s, we
have
M;
s

 iff
M

j
=


[s]:
(7.16)
This sufﬁces to prove Claim 1, because of the following. First suppose that the
modal formula
 is satisﬁable in some relativized cube model
M, say at state
s.
Since
s is an available tuple, it follows from (7.16) that

 is satisﬁable in the ﬁrst-
order structure
M
 under the assignment
s; but also, since
s is available we have
M

j
=
Gv
0
:
:
:
v
n 1
[s]. This shows that


^
Gv
0
:
:
:
v
n 1 is satisﬁable.
Conversely, if the latter formula is satisﬁable, there is some ﬁrst-order structure
A for the language

+, and some assignment
s such that
A
j
=


^
Gv
0
:
:
:
v
n 1
[s].
It is not difﬁcult to see that
(A

)

=
A. Since
A
j
=
Gv
0
:
:
:
v
n 1
[s], it follows by
deﬁnition that
s is an available assignment of
A
. But then we may apply (7.16)
which yields that
A

;
s

; in particular,
 is satisﬁable in
R
n. The proof of (7.16)
proceeds by a standard induction, which we leave to the reader.
a



7.5 Multi-Dimensional Modal Logic
469
Finally, we leave it to the reader to verify that the range of
()
 indeed falls entirely
inside the
n-variable guarded fragment
F
n. From Claim 1 and this observation the
theorem is immediate.
a
Axiomatization
To ﬁnish off the section we will sketch how to prove completeness for the class of
cube models. For simplicity we conﬁne ourselves to the similarity type of cylindric
modal logic — but observe that this completeness result will immediately transfer
to the restricted
n-variable fragment
L
r
n.
Multi-dimensional modal logic is an area with a very interesting completeness
theory. For instance, if one only admits the standard modal derivation rules (modus
ponens, necessitation and uniform substitution), then ﬁnite axiomatizations are few
and far between.
For instance, concerning the
CML
n-theory of the class
C
n,
Andr´eka proved that if
 is a set of
CML
n-formulas axiomatizing
C
n, then for
each natural number
m,
 contains inﬁnitely many formulas that contain all di-
amonds
3
i, at least one diagonal constant
Æ
ij and at least
m propositional vari-
ables. . . However, if we allow special derivation rules, in the style of Section 4.7,
then a nice ﬁnite axiomatization can be obtained, as we will see now. A key role
in our axiomatization and in our proof will be played by a deﬁned operator D
n
p
which acts as the difference operator on the class of cube frames, see Section 7.1.
For its deﬁnition we need some auxiliary operators:

ij

=
3
i
(Æ
ij
^
)
(i
6=
j
)
E
n
i

=
3
0
:
:
:
3
i 1
3
i+1
:
:
:
3
n 1

D
n

=
W
j
6=i

j
i
3
i
(:Æ
ij
^ E
n
i
):
The deﬁnition of D
n may look fairly complex, but it is directly based on the obser-
vation that two
n-tuples
s and
t are distinct if and only for some coordinate
i,
s
i is
distinct from
t
i.
Proposition 7.47 D
n acts as the difference operator on the class of cubes.
Proof. Let
M
=
(C
n
(U
);
V
) be a cube model. We will show that
M;
s
 D
n
p iff
M;
t
j
=
p for some
t such that
s
6=
t
:
(7.17)
For the sake of a clear exposition we assume that
n
=
3, so that we may write
s
=
(s
0
;
s
1
;
s
2
).
For the left to right direction of (7.17), suppose that
M;
s
 D
n
p. Without loss
of generality we may assume that
s


10
3
0
(:Æ
01
^ E
n
0
p). By deﬁnition of

10
it follows that
(s
0
;
s
0
;
s
2
)

3
0
(:Æ
01
^ E
n
0
p). This in its turn implies that there is
some
s
0
0 such that
(s
0
0
;
s
0
;
s
2
)

:Æ
01 and
(s
0
0
;
s
0
;
s
2
)
 E
n
0
p. It is easily seen that



470
7 Extended Modal Logic
the meaning of E
n
0 is given by
M;
u
 E
n
i
 iff
M;
v
j
=
 for some
v such that
u
i
=
v
i
;
so
(s
0
0
;
s
0
;
s
2
)
 E
n
0
p means that there is some
n-tuple
t such that
t

p and
s
0
0
=
t
0. But it follows from
(s
0
0
;
s
0
;
s
2
)

:Æ
01 that
s
0
6=
s
0
0, so that we ﬁnd that
t
0
6=
s
0. But then, indeed,
t is distinct from
s. We leave it to the reader to prove
the right to left direction of (7.17).
a
However, the connection between D
n and the class of cubes is far tighter than this
Proposition suggests. In fact, the cubes are the only frames on which D
n acts as
the difference operator, at least, against the right background of the class
HCF
n of
hypercylindric frames.
Deﬁnition 7.48 A
CML
n-frame is called hypercylindric if the following formulas
are valid on it:
(CM1
i
)
p
!
3
i
p
(CM2
i
)
p
!
2
i
3
i
p
(CM3
i
)
3
i
3
i
p
!
3
i
p
(CM4
ij
)
3
i
3
j
p
!
3
j
3
i
p
(CM5
i
)
Æ
ii
(CM6
ij
)
3
i
(Æ
ij
^
p)
!
2
i
(Æ
ij
!
p))
(i
6=
j
)
(CM7
ij
k
)
Æ
ij
$
3
k
(Æ
ik
^
Æ
k
j
)
(k
62
fi;
j
g)
(CM8
ij
)
(Æ
ij
^
3
i
(:p
^
3
j
p))
!
3
j
(:Æ
ij
^
3
i
p)
(i
6=
j
)
a
All these axioms are Sahlqvist formulas and thus express ﬁrst-order properties of
frames. Clearly, the axioms
CM1–3 together say that each
T
i is an equivalence
relation.
CM6
ij then means that in every
T
i-equivalence class there is at most one
element on the diagonal
E
ij (i
6=
j). One can combine this fact with the (ﬁrst-
order translations of)
CM5
j and
CM7
j
j
i to show that every
T
i-equivalence class
contains exactly one representative on the
E
ij-diagonal. Apart from this effect,
the contribution of
CM7 is rather technical. Finally, the meaning of
CM4 and
CM8 is best made clear by Figure 7.2 below, where the straight lines represent
the antecedent of the ﬁrst-order correspondents, and the dotted lines, the relations
holding of the ‘old’ states and the ‘new’ ones given by the succedent.
The key theorem in our completeness proof is the following.
Theorem 7.49 For any frame
F in
HCF
n, D
n acts as the difference operator on
F
if and only if
F is a cube.
Proof. We have already proved the left to right direction of this equivalence in
Proposition 7.47. The proof of the other direction is technically rather involved
and falls outside the scope of this book.
a



7.5 Multi-Dimensional Modal Logic
471
z
q
y
q
x
q
u
q
T
j
T
i
T
i
T
j
z
q
y
q
x
2
E
ij
q
u
62
E
ij
q
E
ij
     T
j
;
6=
T
i
T
i
T
j
Fig. 7.2. The meaning of
CM4
ij (left) and
CM8
ij (right)
In fact, with Theorem 7.49 we have all the material in our hands to prove the
desired completeness result.
Deﬁnition 7.50 Consider the following modal derivation system

n. Its axioms
are (besides the ones of the minimal modal logic for the similarity type
CML
n),
the formulas
CM1–8; as its derivation rules we take, besides the standard ones,
also the D
n-rule:
`
(p
^
:D
n
p)
!

`

As usual,

n will also denote the logic generated by this derivation system.
a
Theorem 7.51

n is sound and strongly complete with respect to the class
C
n.
Proof. It follows immediately from Theorem 7.6 and Theorem 7.49 that we obtain
a complete axiomatization for
C
n if we extend

n with the D
n-versions of the
axioms Symmetry, Pseudo-transitivity and D-Inclusion. However, as its turns out,
these axioms are valid on the class of hypercylindric frames, so they are already
derivable in

n (even without the use of the D
n-rule). From this, the theorem is
immediate.
a
Exercises for Section 7.5
7.5.1 Let
n and
m be natural numbers such that
n
<
m, and consider a
CML
n-formula
.
First, observe that
 is also a
CML
m-formula. Prove that
C
n

 iff
C
m

. Conclude
that our deﬁnition of an
MLR
n-formula being ﬁrst order valid, is unambiguous.
7.5.2 Prove that the formula
3
0



3
n 1
p acts as the global modality on the class of
hypercylindric frames. That is, show that for any model
M based on such a frame we have
that
M;
s

3
0



3
n 1
p iff
M;
t

p for some
t in
M.



472
7 Extended Modal Logic
Which of the axioms CM1–8 are actually needed for this?
7.5.3 Let
L
 n denote the equality-free fragment of
L
r
n; that is, all atomic formulas are of
the form
P
v
0
:
:
:
v
n 1. In an obvious way we can deﬁne relativized assignment frames for
this language. Prove that the satisﬁability problem for
L
 n in this class of frames can be
solved in PSPACE.
7.5.4 Prove that every hypercylindric
CML
2-frame is the bounded morphic image of a
square frame (that is, a 2-cube). Use this fact to ﬁnd a complete axiomatization for the
class
C
2 that only uses the standard modal derivation rules.
7.5.5 Let
CF
n be the class of cylindric frames, that is, those
CML
n-frames that satisfy
the axioms CM1–7. The class of
n-dimensional cylindric algebras is deﬁned as
CA
n
=
S
P
CmCF
n. The classes
HCF
n and
HCA
n are deﬁned similarly, now using all axioms
CM1–8.
(a) Prove that
CA
n and
HCA
n are canonical, that is, closed under taking canonical
embedding algebras.
(b) Prove that
CA
n and
HCA
n are varieties.
7.5.6 A full
n-dimensional cylindric set algebra is an algebra of the form
(P
(U
n
);
[;
 ;
?;
C
i
;
Id
ij
)
i;j
<n
:
Here the
i-th cylindriﬁcation is deﬁned as the map
C
i
:
P
(U
n
)
!
P
(U
n
) given by
C
i
(X
)
=
fs
2
U
n
j
t
2
X for some
t in
X with
s

i
t
g:
If we close the class of these algebras under products and subalgebras, we arrive at the
variety
RCA
n of representable
n-dimensional cylindric algebras.
(a) Prove that every representable
n-dimensional cylindric algebra is a boolean algebra
with operators.
(b) Prove that
RCA
n is contained in the classes
CA
n and
HCA
n of the previous exer-
cise.
(c) Prove that
RCA
n is canonical. (Hint: use Theorem 7.49 to show that the class
C
n
of
n-dimensional cubes is ﬁrst-order deﬁnable in the frame language of
CML
n.)
7.6 A Lindstr¨om Theorem for Modal Logic
Throughout this book we have seen many examples of modal languages, espe-
cially in the present chapter. To get a clear picture of the emerging spectrum, these
languages may be classiﬁed according to their expressive power or their semantic
properties. But what — if any — is the special status of the familiar modal lan-
guages deﬁned in Chapter 1. If we focus on characteristic semantic properties, then
clearly their invariance under bisimulations must be a key feature. But what else is
needed to single the out (standard) modal languages?
The answer to this question is a modal analogue of a classic result in ﬁrst-order
model theory: Lindstr¨om’s Theorem. It states that, given a suitable explication
of what ‘classical logic’ is, ﬁrst-order logic is the strongest logic to possess the



7.6 A Lindstr¨om Theorem for Modal Logic
473
Compactness and L¨owenheim-Skolem properties. To prove an analogous charac-
terization result for modal logic we need to agree on a number of things:
 What will be the distinguishing property of the logic that we want to characterize
(on top of its invariance for bisimulations)? To answer this question we will
exploit the notion of degree introduced in Deﬁnition 2.28.
 What is a suitable notion of an abstract modal logic? To answer this question we
will introduce some bookkeeping properties from the formulation of the original
Lindstr¨om Theorem for ﬁrst-order logic, and add a further property having to do
with invariance under bisimulations.
Our plan for this section is to discuss each of the above items, one after the other,
and to conclude with a Lindstr¨om Theorem for modal logic.
Background material
Throughout this section models for modal languages are pointed models of the
form
(M;
w
), where
M is a relational structure and
w is an element of
M (its
distinguished point) at which evaluation takes place.
Our main reasons for adopting this convention are the following. First, the basic
semantic unit in modal logic simply is a structure together with a distinguished
node at which evaluation takes place. Second, some of the results below admit
smoother formulations when we adopt the local perspective of pointed models.
Bisimulations between pointed models
(M;
w
) and
(N;
v
) are required to link
the distinguished points
w and
v.
Deﬁnition 7.52 (In-degree) Let
 be a modal similarity type, and let
M be a
-
model. The in-degree of a state
u in
M is the number of times
u occurs as an
non-ﬁrst argument in a relation:
R
w
:
:
:
u
:
:
:. More formally, it is deﬁned as
jf
~
w
2
M
<!
j for some
R and
i
>
1,
u
=
w
i and
R
M
w
1
:
:
:
w
i
:
:
:
w
n
)
gj:
a
In addition to the in-degree of an element of a model, we will also need to use the
notion of height as deﬁned in Deﬁnition 2.32.
Below we will want to get models that have nice properties, such as a low in-
degree or ﬁnite height for each of its elements. To obtain such models, the notion
of forcing comes in handy. Fix a similarity type
. A property P of models is
$
-enforceable, or enforceable, iff for every pointed
-model
(M;
w
), there is a
pointed
-model
(N;
v
) with
(M;
w
)
$

(N;
v
) and
(N;
v
) has P.
For example, the property ‘every element has ﬁnite height’ is enforceable. To
see this, let
(M;
w
) be a pointed
-model; we may assume that
M is generated by
w. Let
(N;
w
) be the submodel of
M whose domain consists of all elements of
ﬁnite height. Then
(M;
w
)
$

(N;
w
).



474
7 Extended Modal Logic
Proposition 7.53 below generalizes the unraveling construction from the stan-
dard modal language to arbitrary vocabularies.
Proposition 7.53 The following properties of models are enforceable:
(i) tree-likeness, and
(ii) the conjunction of ‘having a root with in-degree 0’ and ‘every element (ex-
cept the root) has in-degree at most 1’.
Proof. Item (ii) follows from item (i). A proof of item (i) for similarity types
only involving diamonds is given in Proposition 2.15; for the general case, consult
Exercise 2.1.7.
a
We will characterize modal logic (in the sense of Deﬁnitions 1.12 and 1.23) by
showing that it is the only modal logic satisfying a modal counterpart of the original
Lindstr¨om conditions: having a notion of ﬁnite degree which gives a ﬁxed upper
bound on the height of the elements that need to be considered to verify a formula;
recall Deﬁnition 2.28 for the deﬁnition.
To wrap up our discussion of background material needed for our Lindstr¨om
Theorem, let us brieﬂy recall some basic facts related to degrees and height. Here’s
the ﬁrst of these facts; recall that
((M;
w
)

n;
w
) denotes the submodel of
M that
is generated from
w and that only has states of height at most
n.
Proposition 7.54 Let
 be a modal formula with
deg
()

n. Then
(M;
w
)


iff
((M;
w
)

n;
w
)

.
Next, recall from Proposition 2.29 that, up to logical equivalence, there are only
ﬁnitely many non-equivalent modal formulas with a ﬁxed ﬁnite degree over a ﬁnite
similarity type.
We say that
(M;
w
) and
(N;
v
) are
n-equivalent if
w and
v satisfy the same
modal formulas of degree at most
n.
Proposition 7.55 Let
 be a ﬁnite similarity type.
Let
(M;
w
),
(N;
v
) be two
rooted models such that the roots have in-degree 0, every element different from
the root has in-degree at most 1, all nodes have and height at most
n.
If
(M;
w
) and
(N;
v
) are
n
+
1-equivalent, then
(M;
w
)
$
(N;
v
).
Proof. Deﬁne
Z

A

B by
xZ
y iff:
heigh
t
(x)
=
heigh
t(y
)
=
m and
(M;
x) and
(N;
y
) are
(n
 m)-equivalent.
We claim that
Z
:
(M;
w
)
$
(N;
v
). To prove this, we only show the forth
condition. Assume
xZ
y and
R
M
xx
1
:
:
:
x
k, where
heigh
t
(x)
=
heigh
t
(y
)
=
m.
Then
n
 m

1. Let
M be the modal operator whose semantics is based on
R.
As
 is ﬁnite, there are only ﬁnitely many non-equivalent formulas of degree at



7.6 A Lindstr¨om Theorem for Modal Logic
475
most
n
 m
 1. Let
 
i be the conjunction of all non-equivalent modal formu-
las of at most this degree that are satisﬁed at
x
i (1

i

k). Then
(M;
x)

M
( 
1
;
:
:
:
;
 
k
), and
M( 
1
;
:
:
:
;
 
k
) has degree
n
 m. Hence, as
xZ
y,
(N;
y
)

M
( 
1
;
:
:
:
;
 
k
). So there are
y
1, . . . ,
y
k in
N such that
R
N
y
y
1
:
:
:
y
k and
(N;
y
i
)

 
i (1

i

k).
Now, as all states have in-degree at most 1,
heigh
t
(x
i
)
=
heigh
t
(y
i
)
=
m
+
1,
and
(M;
x
i
) and
(N;
y
i
) (1

i

k) are
(n
 (m
+
1))-equivalent. Hence,
(M;
x
i
)
$

(N;
y
i
). This proves the forth condition.
a
Abstract modal logic
The original Lindstr¨om Theorem for ﬁrst-order logic starts from a deﬁnition of an
abstract classical logic as a pair (L;
j
=
L
) consisting of a set of formulas
L and a
satisfaction relation
j
=
L between
L-structures and
L-formulas that satisﬁes three
bookkeeping conditions, an Isomorphism property, and a Relativization property
which allows one to consider deﬁnable submodels. Then, an abstract logic extend-
ing ﬁrst-order logic coincides with ﬁrst-order logic if, and only if, it satisﬁes the
Compactness and L¨owenheim-Skolem properties. We will now set up our modal
analogue of Lindstr¨om’s Theorem along similar lines.
The deﬁnition runs along the same lines as the deﬁnition of an abstract classical
logic. An abstract modal logic is characterized by three properties: two book keep-
ing properties, and a Bisimilarity property to replace the Isomorphism property.
Deﬁnition 7.56 (Abstract Modal Logic) By an abstract modal logic we mean
a pair
(L;

L
) with the following properties (here
L is the set of formulas, and

L is its satisfaction relation, that is, a relation between (pointed) models and
L-
formulas):
(i) Occurrence property. For each
 in
L there is an associated ﬁnite language
L(

). The relation
(M;
w
)

L
 is a relation between
L-formulas
 and struc-
tures
(M;
w
) for languages
L containing
L(

). That is, if
 is in
L, and
M is
an
L-model, then the statement
(M;
w
)

L
 is either true or false if
L contains
L(

), and undeﬁned otherwise.
(ii) Expansion property. The relation
(M;
w
)

L
 depends only on the reduct of
M to
L(

). That is, if
(M;
w
)

L
 and
(N;
w
) is an expansion of
(M;
w
) to a
larger language, then
(N;
v
)

L
.
(iii) Bisimilarity property. The relation
(M;
w
)

L
 is preserved under bisimu-
lations: if
(M;
w
)
$

(N;
v
) and
(M;
w
)

L
, then
(N;
v
)

L
.
a



476
7 Extended Modal Logic
If we compare the above deﬁnition to the list of properties deﬁning an abstract
classical logic, we see that it’s the Bisimilarity property that determines the modal
character of an abstract modal logic.
Obviously, ordinary modal formulas provide an example of an abstract modal
logic, but so does propositional dynamic logic. In contrast, the language of basic
temporal logic provides an example of a logic that is not an abstract modal logic,
as formulas from basic temporal logic are not preserved under bisimulations.
Next, we need to say what we mean by ‘(L;

L
) extends basic modal logic’ and
by closure under negation.
Deﬁnition 7.57 We say that
(L;

L
) extends modal logic if for every basic modal
formula there exists an equivalent
L-formula, that is, if for each basic modal for-
mula
 there exists an
L-formula
 such that for any model
(M;
w
) we have
(M;
w
)

 iff
(M;
w
)

L
 .
Also,
(L;

L
) is closed under negation if for all
L-formulas
 there exists an
L-formula
: such that for all models
(M;
w
),
(M;
w
)

 iff
(M;
w
)
6
:.
a
Of course, propositional dynamic logic is an example of an abstract modal logic
that extends (basic) modal logic.
Logics in the sense of Deﬁnition 7.56 deal with the same class of pointed mod-
els as (basic) modal logic, and only the formulas and satisfaction relation may be
different. This implies, for example, that intuitionistic logic or the hybrid logics
considered in Section 7.3 are not abstract modal logics: their models need to sat-
isfy special constraints. The original Lindstr¨om characterization of ﬁrst-order logic
suffers from similar limitations (by not allowing
!-logic as a logic, for example).
As a ﬁnal step in our preparations, we need to say what the notion of degree
means in the setting of an abstract modal logic.
Deﬁnition 7.58 (Notion of Finite Degree) An abstract modal logic has a notion
of ﬁnite degree if there is a function
deg
L
:
L
!
! such that for all
(M;
w
), all

in
L,
(M;
w
)

L

iff
((M;
w
)

deg
L
());
w

L
:
If
L extends (basic) modal logic, we assume that
deg
L behaves regularly with
respect to standard modal operators and proposition letters. That is, if
M is a modal
operator (see Deﬁnition 1.12), then
deg
L
(p)
=
0 and
deg
L
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
L
(
i
)
j
1

i

ng.
Finally, two models
(M;
w
) and
(N;
v
) for the same language are
L-equivalent
if for every
 in
L,
(M;
w
)

 iff
(N;
v
)

.
a
Having a ﬁnite degree is a very restrictive property, which is not implied by the
ﬁnite model property (FMP). To see this recall that propositional dynamic logic



7.6 A Lindstr¨om Theorem for Modal Logic
477
has the FMP: it has the property that every satisﬁable formula
 is satisﬁable on a
model of size at most
jj
3, where
 is the length of
. However, it does not have a
notion of ﬁnite degree. To see this, consider the model
(!
;
R
a
;
V
), where
R
a is the
successor relation and
V is an arbitrary valuation, and let

=
[a

]hai>; clearly
(!
;
R
a
;
V
);
0

. But for no
n
2
! does the restriction
(!
;
R
a
;
V
)

n satisfy

at
0. It follows that PDL does not have a notion of ﬁnite degree.
Characterizing modal logic
We are almost ready now to prove our characterization result. The following lemma
is instrumental.
Lemma 7.59 Let
(L;

L
) be an abstract modal logic which is closed under nega-
tion. Assume
L has a notion of ﬁnite degree
deg
L. Let
 be an
L-formula with
deg
L
()
=
n. Then, for any two models
(M;
w
),
(N;
v
) such that
(M;
w
) and
(N;
v
) are
n-equivalent, we have that
(M;
w
)

L
 implies
(N;
v
)

L
.
Proof. Assume that the conclusion of the lemma does not hold. Let
(M;
w
),
(N;
v
)
be such that
(M;
w
) and
(N;
v
) are
n-equivalent, but
(M;
w
)

L
 and
(N;
v
)

L
:.
By the Occurrence and Expansion properties we may assume that
L
=
L(

),
where
L(

) is the ﬁnite language in which
 lives.
By Proposition 7.53 we can assume that
(M;
w
) and
(N;
v
) are rooted such that
the roots have in-degree 0, while all other nodes have in-degree at most 1. Then
((M;
w
)

n;
w
) and
((N;
v
)

n;
v
) are
n-equivalent, and
((M;
w
)

n;
w
)

L

but
((N;
v
)

n;
v
)

L
:. In addition
((M;
w
)

n;
w
) and
((N;
v
)

n;
v
)
both have in-degree 1 and roots of in-degree 0. By Proposition 7.55 it follows
that
((M;
w
)

n;
w
) and
((N;
v
)

n;
v
) are bisimilar — but now we have a
contradiction with the Bisimilarity property as
((M;
w
)

n;
w
) and
((N;
v
)

n;
v
)
are bisimilar but don’t agree on
.
a
Theorem 7.60 Let
(L;

L
) extend modal logic. If
(L;

L
) has a notion of ﬁnite
degree, then it is equivalent to the modal language as deﬁned in Deﬁnition 1.12.
Proof. We must show that every
L-formula
 is
L-equivalent to a basic modal
formula
 , that is, for all
(M;
w
),
(M;
w
)

L
 iff
(M;
w
)

L
 . As before,
by the Occurrence and Expansion properties we may restrict ourselves to a ﬁnite
language. Moreover,
 has a basic modal equivalent iff it has such an equivalent
with the same degree; so we have to locate the equivalent we are after among the
basic modal formulas whose degree equals the
L-degree of
.
Assume
n
=
deg
L
(). By Proposition 2.29 there are only ﬁnitely many (non-
equivalent) basic modal formulas whose degree equals
n; assume that they are all



478
7 Extended Modal Logic
contained in
 n. It sufﬁces to show the following
if
(M;
w
) and
(N;
v
) agree on all formulas in
 n, then they agree on
.
(7.18)
For then,
 will be equivalent to a Boolean combination of formulas in
 n. To see
this, reason as follows. The relation ‘satisﬁes the same formulas in
 n’ is an equiv-
alence relation on the class of all models; as
 n is ﬁnite, there can only be ﬁnitely
many equivalence classes. Choose representatives
(M
1
;
w
1
), . . . ,
(M
m
;
w
m
), and
for each
i, with
1

i

m, let
 
i be the conjunction of all formulas in
 n that are
satisﬁed by
(M
i
;
w
i
). Then
 is equivalent to
W
f 
i
j
(M
i
;
w
i
)

L
g.
Now to conclude the proof of the theorem we need only observe that condition
(7.18) is exactly the content of Lemma 7.59.
a
To conclude this section a few remarks are in order. First, the property of having a
notion of ﬁnite degree can be characterized algebraically in terms of preservation
under ultraproducts over the natural numbers; Theorem 7.60 can then be reformu-
lated accordingly.
Second, in the proof of the Lindstr¨om Theorem the basic modal formula
 that is
found as the equivalent of the abstract modal formula
 is in the same vocabulary
as
. This means, for example, that the only abstract modal logic over a binary
relation that has a notion of ﬁnite degree is the standard modal logic with a single
modal operator
3.
Here, we have only covered the modal logics as deﬁned in Deﬁnition 1.12; in
some cases extensions beyond this pattern can easily be obtained. As a ﬁrst exam-
ple, consider the basic temporal language with operators
F and
P, where
x

F
p
(x

P
p) iff for some
y,
R
xy and
y

 (R
y
x and
y

). Consider temporal
bisimulations in which one not only looks forward along the binary relation, but
also backward, and adopt the notion of height accordingly. Given the obvious def-
inition of an abstract temporal logic, standard temporal logic is the only temporal
logic over a single binary relation that has a notion of ﬁnite degree.
7.7 Summary of Chapter 7
I Logical Modalities: Logical modalities receive a ﬁxed interpretation in every
model. Simple examples are the past tense operator
P, the global diamond E,
and the difference operator D. As well a enhancing expressivity, some of them
(notably
P and D) make it possible to prove general completeness theorems
using additional rules of proof.
I Algebra of Diamonds: Some modal languages offer not just a single logical
modality but an entire algebra of diamonds. Good examples are PDL and BML.
I Since and Until: The since and until operators are interesting in applied logic
because they enable us to specify guarantee properties. They are mathematically



7.7 Summary of Chapter 7
479
interesting because they are expressively complete over Dedekind complete to-
tal orders.
I Completeness-via-Completeness: While deductive completeness of since and
until logic can be proved using standard modal techniques, for Dedekind com-
plete total order there is an interesting alternative: taking a detour via expressive
completeness.
I Hybrid Logic: The basic hybrid language lets us refer to states using nominals,
atomic symbols true at exactly one state in every model. Some stronger hybrid
languages allow us to bind nominals.
I Hybrid Proof Theory: We can deﬁne a rule of proof called PASTE in the basic
hybrid language. This rule is essentially a sequent rule lightly disguised. With
its help, a frame completeness result covering all pure formulas can be proved
fairly straightforwardly.
I Guarded fragment: As the standard translation shows, modalities are essentially
macros which permit restricted forms of quantiﬁcation. Abstracting from this
insight leads to the guarded fragment, a decidable fragment of ﬁrst-order logic
with the ﬁnal model property.
I Packed Fragment: By taking this observation even further, and noting that the
mosaic method sufﬁces to prove decidability, it is possible to isolate an even
larger decidable fragment of ﬁrst-order logic: the packed fragment. This frag-
ment also has the ﬁnite model property.
I Multi-Dimensional Modal Logic: Multi-dimensional modal logic is essentially
modal logic in which evaluation is performed at a sequence of states, rather
than at a single state. By viewing variable assignments as sequence of states, it
is possible to view ﬁrst-order logic itself as a multi-dimensional modal logic.
I Lindstr¨om’s Theorem: Given a suitable (bisimulation centered) explication of
what an abstract modal logic is, our Lindstr¨om Theorem for modal logic says
that the general modal languages deﬁned in Deﬁnition 1.12 are the strongest
ones to have a notion of ﬁnite degree.
I Extended Modal Logic: In many ways, this chapter is badly named. Among
other things, we’ve just seen that not only it is possible to introduce global-
ity, more complex quantiﬁer alternations in satisfaction deﬁnitions, names for
states, and evaluation at sequences of states, but we can do so without losing
the properties that made modal logic attractive in the ﬁrst place. So forget the
‘extended’. As we said in the Preface: it’s all just modal logic!
Notes
A really serious guide to extended modal logic would have to cover the (vast)
literature on temporal logics, ﬁxed point logics, and variants of PDL discussed in
the theoretical computer science literature, plus formalisms such as feature and



480
7 Extended Modal Logic
description logic, and much else besides. We don’t have space to do all that, and
the following Notes stick to the six topics discussed in the text. Nonetheless, with
the help of the following remarks (coupled with a little judicious reference chasing)
the reader should be able to form a coherent map of territory.
Logical Modalities. It’s hard to precise about when the idea of adding ﬁxed in-
terpretation operators to modal languages came to be seen as standard. Certainly
the writings of Johan van Benthem (for example, his book on temporal logic, his
‘manual’ on intensional logic, and his inﬂuential survey of correspondence theory)
played an important role. So did the new applications of modal logic, particularly
in computer science (once you’ve seen PDL it’s hard to believe that the basic modal
language is the be-all and end-all of modal logic). At any rate, by the end of the
1980s the idea that modal languages are abstract tools for talking about relational
structures — tools that it was not only legitimate, but actually interesting to extend
— was well established in both Amsterdam and Bulgaria. Nowadays this view is
taken for granted by many (perhaps most) modal logicians, and given this perspec-
tive the use of logical modalities is as natural as breathing.
Of course, many of the operators we now call ‘logical’ have been around a lot
longer than that. In a way, the global modality has always been there (after all its
just a plain old S5 operator). But when did it ﬁrst emerge as an additional operator?
We’re not sure. Prior used it on a number of occasions (see, for example, [369,
Appendix B4]), though sometimes Prior’s global modality is actually the master
modality
2* discussed in Section 6.5 (that is, sometimes Prior views globality as
the reﬂexive transitive closure of the underlying relation).
But it seems fair to say that it was the Bulgarian-school who ﬁrst exploited it
systematically: it’s the Swiss Army knife underlying their investigation of BML,
and their work on hybrid logic. Goranko and Passy [198] is a systematic study of
the global modality as an additional operator, and is the source of Theorem 7.1, the
Goldblatt-Thomason theorem for ML
(3; E
). The operator has also been studied
from an algebraic angle, being closely connected to the notion of a discriminator
variety; these classes display nice algebraic behavior and have been intensively
investigated in universal algebra. For, in the context of boolean algebra with oper-
ators, having the global modality is equivalent to having a so-called discriminator
term; this is why in algebraic circles this modality is sometimes dubbed a ’unary
discriminator term’; see Jipsen [253] for some information. The basic complexity
results for the global modality were proved in Hemaspaandra’s thesis [412]. Inci-
dentally, the global modality is usually referred to as the ‘universal’ modality in the
literature. However the word ‘universal’ suggests that we are working with a box,
so we prefer the term ‘global’, which is appropriate for both boxes and diamonds.
The history of the difference operator is harder to untangle. It is probably due
to von Wright [457] (who viewed it as a ‘logic of elsewhere’) and Segerberg gave



7.7 Summary of Chapter 7
481
an axiomatization in a festschrift for von Wright (see [399]). Segerberg’s axioma-
tization, together with a more detailed completeness proof, was later published in
[401]. But Segerberg treats D as an isolated modality. The use of D as an additional
modality seems to have been proposed independently by Koymans [276, 277] and
Sain [389]. The difference operator is also discussed in Goranko [195]. For a sys-
tematic investigation of D as an additional, logical modality, see de Rijke [104].
The D-Sahlqvist theorem in the text is due to Venema [439]. Theorem 7.8 is an
unpublished result due to Szabolcs Mikul´as.
BML is a Bulgarian school invention. The system is ﬁrst described in Gargov,
Passy and Tinchev [173] (as part of a wide ranging discussion of extended modal
logic) and Gargov and Passy [172] concentrates on BML and gives proofs of the key
completeness and decidability results. See also the results on modal deﬁnability in
Goranko [195]. All these papers view modal languages as general tools for talking
about structures, very much in the spirit of the present book. The window operator
has an interesting independent history: van Benthem [37] used it as part of a logic
of permissions and obligations, Goldblatt [182] used it to deﬁne negation in quan-
tum logic, Humberstone [242] used it in a discussion of inaccessible worlds, while
Gargov, Passy and Tinchev [173] view it as a ‘logic of sufﬁciency’ that balances
the usual ‘logic of necessity’ provided by
2. Complexity-theoretic aspects of BML
have been studied and surveyed by Lutz and Sattler [310], while resolution-based
decision procedures for extensions of BML and related languages are explored by
Hustadt and Schmidt [244].
As we pointed out in the text, both BML and PDL are examples of modal lan-
guages equipped with highly structured collections of modal operators. The dy-
namic modal logic of De Rijke [112] is a further example, and many description
logics allow for the construction of complex roles (that is, accessibility relations)
by means of some or all of the booleans, converse, and sometimes even transitive
closure and least ﬁxed point constructors; see Donini et al. [123].
The algebraic counterparts of modal languages with structured collections of
modal operators can best be phrased in terms of multi-sorted algebras, where the
(algebraic counterparts of the) modal operators provide the links between the sorts.
Kleene algebras [278] and Peirce algebras [108, 111] are two important examples.
The former provide an algebraic semantics for PDL and consist of a boolean algebra
and a regular algebra together with systematic links between them that are used
to interpret the diamonds. The latter provide an algebraic semantics of dynamic
modal logic and consist of a boolean algebra and a relation algebra together various
links between that are, again, used to interpret the modalities in the language.
Since and Until. The invention of since and until logic was a major breakthrough
in the study of modal logic. Hans Kamp tells the story this way. In a semester-long
course Arthur Prior gave on tense logic at UCLA in the fall of 1965, when Kamp



482
7 Extended Modal Logic
had just started his PhD, Prior stressed that the
P and
F operators operators were
strictly topological, and asked whether it was possible to develop some notion of
metric time within the framework of tense logic. Now, a ﬁrst requirement on such
an enterprise is that it can express what it is for some proposition
q to have been
true since the last time some periodically true proposition
p was true. Trying to
ﬁnd a genuinely topological tense logic in which these kinds of relations could be
expressed lead Kamp to the deﬁnitions of since and until. As the technical interest
of the new operators became clear, the original topological motivation seems to
have been shelved (Kamp, personal communication, remarks that ‘The question
of how to embed a logic of metric temporal notions within a topological tense
logic unfortunately never got properly off the ground.’). Kamp ﬁrst showed that
P and
F were not capable of expressing since and until, and eventually succeeded
in proving Theorem 7.12(i), the expressive completeness of since and until logic
over Dedekind complete total orders (see his thesis [263]). At that time, deductive
completeness was the dominant interest in modal logic. Kamp’s result showed that
the neglected topic of modal expressivity deserved further attention, and can be
regarded as a precursor to the study of correspondence theory that emerged in the
1970s.
The next step was taken by Dov Gabbay. Kamp’s result was clearly important,
but his direct proof was complex, and although Jonathan Stavi [415] succeeded
in providing a direct proof of Theorem 7.12(ii), it was not obvious how proceed
further. Matter were greatly simpliﬁed when Gabbay introduced the notion of sep-
arability (see [157, 159]). Roughly speaking, a language is separable over a class
of models if every formula is equivalent to a boolean combination of atomic for-
mulas, formulas that only talk about the past, and formulas that only talk about
the future. This idea drastically simpliﬁes the proofs of Theorem 7.12(i) and Theo-
rem 7.12(ii), and opens the way to more general investigations. Nowadays a variety
of techniques are used for proving expressive completeness results for modal (and
other) languages; game-based approaches (see Immerman and Kozen [246]) have
proved particularly useful. The best introduction to expressive completeness is
the encyclopedic Gabbay, Hodkinson, and Reynolds [163]; both separability and
game-based proofs are discussed. It also contains many other results on since and
until logic and a useful bibliography.
But what really made the until operator so popular is the simple observation
made in the text: it offers precisely the what is needed to express guarantee prop-
erties (this was ﬁrst noted in Gabbay, Pnueli, Shelah, and Stavi [167]). Nowadays
until may well be the single best known modal operator (at least in computer sci-
ence) and it occurs in both in its original form, and in a number of variant forms
in the study of linear and branching time temporal logics (see Clarke and Emer-
son [92], Goldblatt [183]).
Good discussions of step-by-step completeness proofs for since and until can



7.7 Summary of Chapter 7
483
be found in Burgess [76] and Xu [458]. The classiﬁcation of properties of ﬂows
of time (in terms of safety, liveness, and guarantees) referred to in Section 7.2
can be found in Manna and Pnueli’s textbook [318] on using temporal logic for
specifying concurrent and reactive systems. Theorem 7.19 is due to Venema [438];
the strategy of using expressive completeness to obtain axiomatic completeness
results goes back at least to Gabbay and Hodkinson [164].
One ﬁnal remark: in spite of the fact that its satisfaction deﬁnition makes use of a
more complex patterns of quantiﬁcation, the since and until operators are genuinely
modal. In particular, the notion of bisimulation can be adapted to these operators:
the only complication is that, instead of the simple ‘complete the square’ idea il-
lustrated in Figure 2.3 (65), bisimulations now need to match relational steps plus
intermediate intervals in suitable ways. Kurtonina and de Rijke [295] contain a
solution to this issue as well as a survey of earlier proposals.
Hybrid Logic. Arthur Prior introduced and made systematic use of hybrid logic;
see Prior [369] (in particular, Chapter 5 and Appendix B.3), several of the papers
in Prior [370], and the posthumously published Prior and Fine [371]. Prior’s sys-
tems typically allowed explicit quantiﬁcation over states using
8 and
9, and con-
tained the global modality. Technical aspects of such languages were explored in
Bull [71], an important paper, which among other things notes that pure formulas
give rise to easy frame completeness results. In the mid 1980s Passy and Tinchev
independently reinvented the idea of ‘names as formulas’. Their earliest paper
[360] added nominals and the global modality to a rich version of PDL; in [361]
they considered
8 and
9 (again in the setting of PDL); and [362], their beautiful
essay on hybrid languages, remains one of the key papers on hybrid languages.
The subsequent history of hybrid languages revolves around attempts to ﬁnd
well-behaved sublanguages of such strong systems. The most obvious way to do
this is one explored in the text: treat nominals as names, rather than variables open
to binding, and keep the underlying modal language relatively weak. Early papers
which explore this option include Gargov and Goranko [171] (the basic modal
language enriched with nominals and the global modality) and Blackburn [52] (the
basic tense language enriched with nominals alone). The basic hybrid language
discussed in the text can be viewed as an interesting compromise between simply
adding nominals to the basic modal language (which makes the axiomatics messier,
as Exercise 7.3.7 shows) and adding both nominals and the global modality (which
raises the complexity to EXPTIME-complete). A proof of Theorem 7.21 (that the
basic hybrid language has a PSPACE-complete satisﬁability problem) can be found
in Areces, Blackburn and Marx [14]. For a more detailed look at the complexity
of hybrid logic, see [13] by the same authors. Theorem 7.29 is a modiﬁcation of
results proved in Blackburn and Tzakova [61]. It simpliﬁes similar a result proved
in Gargov and Goranko [171] with the aid of the global modality.



484
7 Extended Modal Logic
But the idea of binding variables to states turns out to be important. Binding
admits a rich expressivity hierarchy. For a start, even if binding with
8 and
9
is allowed, when there are no satisfaction operators in the language, the result-
ing language does not have full ﬁrst-order expressivity; see Blackburn and Selig-
man [57]. Moreover, as we mentioned in the text, the
# binder simply binds vari-
ables to the current state; in effect, it lets us create a name for the here-and-now (see
Goranko [196], Blackburn and Seligman [57, 58], Blackburn and Tzakova [61]). If
we enrich the basic hybrid language with the
# binder we obtain a hybrid language
which corresponds to precisely the fragment of the ﬁrst-order correspondence lan-
guage which is invariant under generated submodels. This is proved in Areces,
Blackburn and Marx [14] by isolating notions of bisimulation suitable for various
hybrid languages and proving a characterization theorem. The paper also links
these notions of bisimulation to restricted forms of Ehrenfeucht-Fra¨ıss´e games.
Hybrid logic provide a natural setting for modal proof theory. Seligman [404]
is the pioneering paper here, and Seligman [405] discusses satisfaction operator
based natural deduction and sequent systems. Blackburn [55] deﬁnes satisfaction
operator driven tableau and sequent systems and uses Hintikka sets to prove an
analog of Theorem 7.29. Tzakova [431] combines the use of nominals with the
preﬁx systems of Fitting [145]. Demri [115] deﬁnes a sequent calculus for the
basic tense language enriched with nominals, and Demri and Gore [116] introduce
a display calculus for the basic tense language enriched with nominals and D.
Hybrid logics turn up naturally in a number of applications. The AVMs used
in computational linguistics (recall Example 1.17) can be viewed as modal log-
ics: path re-entrancy tags are treated as nominals (see, for example, Blackburn and
Spaan [59]). And while it has long been known that description logics are nota-
tional variants of modal logics, this relation only holds at the level of concepts.
So-called A-Box (or assertional) reasoning — that is, reasoning about how con-
cepts apply to particular individuals — corresponds to a restricted use of satisfac-
tion operators, while the ‘one-of’ operators used in some versions of description
logic are essentially disjunctions of nominals; see Blackburn and Tzakova [60],
Areces and de Rijke [15], and Areces’s PhD thesis [12]. Nominals also turn up in
the Polish tradition of modal logics for information systems and rough-set theory:
see Konikowska [274, 275]. They also provide a natural model of tense and other
forms of temporal reference in natural language (see Blackburn [54]).
A ﬁnal remark. The basic hybrid language shows that sorting is interesting in
the setting of modal logic — so why not introduce further sorts? In fact, this
step was already taken in Bull [71] who introduced a third sort of atomic symbol:
path nominals, true at precisely the points belonging to some path through the
model. For more information on hybrid logic, see the Hybrid Logic home page at
www.hylo.net. For a recent ‘manifesto’ on hybrid logic that touches on most
of the themes just mentioned, see Blackburn [56]



7.7 Summary of Chapter 7
485
The Guarded Fragment. The guarded fragment was introduced by Andr´eka, van
Benthem and N´emeti in 1994. The roots of the decidability proof date back to
1986, when N´emeti [345] showed that the equational theory of the class of so-
called relativized cylindric set algebras is decidable. The ﬁrst-order counterpart of
this result is that a certain subfragment of the guarded fragment is decidable.
The importance of this result for ﬁrst-order logic was realized in 1994 when
Andr´eka, van Benthem and N´emeti introduced the guarded fragment and showed
that many nice properties of the basic modal system K generalize to it. In par-
ticular, the authors established a characterization in terms of guarded bisimula-
tions, decidability and a kind of tree model property. The journal version of their
paper is [9]. Some time later van Benthem, was able to generalize some of the
results, introducing the loosely guarded fragment in [433]. The slightly more gen-
eral packed fragment was introduced in Marx [323] in order to give a semantic
characterization in terms of packed bisimulations. (An example of a packed sen-
tence which is not equivalent to a loosely guarded sentence in the same signature
is
9xy
z
(9w
C
xy
w
^
9w
C
xz
w
^
9w
C
z
y
w
^
:C
xy
z
).)
The mosaic based decision algorithms of Andr´eka, van Benthem and N´emeti
were essentially optimal: a result established by Gr¨adel [200]. In this paper, Gr¨adel
also deﬁnes and establishes the loose model property for the loosely guarded frag-
ment. Our deﬁnition of a loose model is based on the deﬁnition of a tree model
given there. Gr¨adel and Walukiewicz [203] showed that the same bounds obtain
when the guarded fragment is expanded with least and greatest ﬁxed point oper-
ators. Marx, Mikul´as and Schlobach [325] deﬁned a PSPACE-complete guarded
fragment with the ﬁnite tree model property. This fragment satisﬁes both locality
principles.
The ﬁnite model property for the guarded fragment, and several subfragments of
the packed fragment, was established in an algebraic setting by Andr´eka, Hodkin-
son and N´emeti [7]. Gr¨adel [200] provides a direct proof for the guarded fragment.
The remaining open question for the full packed fragment was solved afﬁrmatively
by Hodkinson [236]. All these results are based on variants of a result due to Her-
wig [228]. The use of Herwig’s Theorem to establish the ﬁnite model property
and to eliminate the need of step-by-step constructions originates with Hirsch et
al. [232].
Multi-Dimensional Modal Logic. The idea of evaluating modal languages at se-
quences of points, rather than at the points simpliciter, is extremely natural, so it
is no surprise that over the years modal logicians with very diverse interests have
devised multi-dimensional systems.
It seems that logicians interested in natural language were ﬁrst off the mark.
Natural language utterances are so context dependent, that evaluating at sequences
of points (each coordinate modelling a different aspect of context) proved a useful



486
7 Extended Modal Logic
idea. Evaluation at pairs of points is built into Montague’s [342] general framework
for natural language semantics. Kamp’s [264] classic analysis of the word ‘now’
uses a second coordinate to keep track of utterance time. Vlach [445] provided an
analysis of the word ‘then’, and in a series of papers, ˚Aqvist and co-workers [11]
developed a number of rich multi-dimensional modal logics for analyzing natu-
ral language temporal phenomena. Before long, such systems were subjected to
rigorous logical investigation: see, for example, Segerberg’s elegant decidability
and completeness result in [398], and Gabbay’s work on expressiveness and other
topics (much of which reappeared in the later work by Gabbay et al. [163]).
Somewhat later, a rich source of inspiration came from logic itself. Some work
here, such as the sorted modal logic PREDBOX of Kuhn [293], ﬁtted in the tradition
of Quine-style ﬁrst-order logic without variables, but most of it was linked, one
way or another, with the algebraic logic framework of the Tarskian school (see the
Notes of Chapter 5). This certainly applies to the multi-dimensional logics that we
presented in Section 7.5. Venema [436], from which our Theorem 7.51 originates,
made the connection between modal logic and cylindric algebras. Subsequent re-
search drew on existing ideas on relativized cylindric algebras (see N´emeti [345])
to use the modal framework to ‘tame’ ﬁrst-order logic and its ﬁnite variable frag-
ments (see our discussion of the abstract and relativized assignment frames in the
text; more information on this program can be found in van Benthem [47] or
Mikul´as [335]). This line of work is closely related to arrow logic, which is a
multi-dimensional modal logic in its own right (see Marx et al. [324] for more
information) and in fact this strand of work ultimately lead to the isolation of the
guarded fragment. All of these (and more) multi-dimensional modal logics are cov-
ered in the monograph Marx and Venema [326]; readers interested in complexity
results should consult Marx [322].
Computer scientists have different motivations for studying multi-dimensional
modal logics. In order to build formal models of an application domain, they
need to take account of various features simultaneously. Of the wealth of litera-
ture on this topic we’ll just mention Fagin et al. [133], which concentrates on the
combination of temporal and epistemic logics in the context of distributed systems.
Such applications have led logicians to study various ways of constructing complex
logics from relatively simple ones. A particularly interesting and mathematically
non-trivial branch of multi-dimensional modal logics arises if one studies a modal
language with various modal operators over a semantics in which the frames are
cartesian products of frames for the individual operators. This area of so-called
product logics, which has an early predecessor in Shehtman [406], has recently
become very active; a monograph Gabbay et al. [153] is on its way.
Finally, multi-dimensional modal logic remains one of the most philosophically
important branches of modal logic. Important references include Kaplan [269,
270], Stalnaker [414], and Chalmers [88]



7.7 Summary of Chapter 7
487
The Lindstr¨om Theorem for Modal Logic. Theorem 7.60, a Lindstr¨om-type
characterization of the modal languages deﬁned in Deﬁnitions 1.9 and 1.12 is due
to De Rijke [107]; the result was obtained as part of a general program to come up
with modal counterparts of model-theoretic results in ﬁrst-order logic [106]. The
original ﬁrst-order version of Lindstr¨om’s Theorem was ﬁrst presented in Lind-
str¨om [309]. The original result states that, given a suitable explication of a ‘clas-
sical logic’, ﬁrst-order logic is the strongest logic to possess the Compactness and
L¨owenheim-Skolem properties; it formed an important source of inspiration for
the area of model-theoretic logics [25]. Deﬁnitions of the abstract notion of a logic
can be found in Chang and Keisler [89] and in Barwise [24]. A very accessible pre-
sentation of Lindstr¨om’s Theorem for ﬁrst-order logic can be found in Doets [119,
Chapter 4].


