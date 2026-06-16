<!-- Source: Zakharyaschev, Wolter & Chagrov (2001). Advanced Modal Logic (Handbook of Philosophical Logic vol. 3, 2nd ed.). Introduction and overview. Authors: Zakharyaschev, Wolter, Chagrov. -->

# Advanced Modal Logic


*
Preface

i

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

ADVANCED MODAL LOGIC
This chapter is a continuation of the preceding one, and we begin it at the
place where the authors of Basic Modal Logic left us about fteen years
ago. Concluding his historical overview, Krister Segerberg wrote: \Where
we stand today is dicult to say. Is the picture beginning to break up,
or is it just the contemporary observer's perennial problem of putting his
own time into perspective?" So, where did modal logic of the 1970s stand?
Where does it stand now? Modal logicians working in philosophy, computer
science, articial intelligence, linguistics or some other elds would probably
give di erent answers to these questions. Our interpretation of the history
of modal logic and view on its future is based upon understanding it as part
of mathematical logic.
Modal logicians of the First Wave constructed and studied modal systems
trying to formalize a few kinds of necessity-like and possibility-like operators. The industrialization of the Second Wave began with the discovery
of a deep connection between modal logics on the one hand and relational
and algebraic structures on the other, which opened the door for creating
many new systems of both articial and natural origin. Other disciplines|
the foundations of mathematics, computer science, articial intelligence,
etc.|brought (or rediscovered1) more. \This framework has had enormous
inuence, not only just on the logic of necessity and possibility, but in other
areas as well. In particular, the ideas in this approach have been applied
to develop formalisms for describing many other kinds of structures and
processes in computer science, giving the subject applications that would
have probably surprised the subject's founders and early detractors alike"
Barwise and Moss 1996]. Even two or three mathematical objects may lead
to useful generalizations. It is no wonder then that this huge family of logics
gave rise to an abstract notion (or rather notions) of a modal logic, which
in turn put forward the problem of developing a general theory for it.
Big classes of modal systems were considered already in the 1950s, say
extensions of S5 Scroggs 1951] or S4 Dummett and Lemmon 1959]. Completeness theorems of Lemmon and Scott 1977],2 Bull 1966b] and Segerberg
1971] demonstrated that many logics, formerly investigated \piecewise",
1 One of the celebrities in modal logic|the G
odel{Lob provability logic GL|was rst
introduced by Segerberg 1971] as an \articial" system under the name K4W.
2 This book was written in 1966.

2

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

have in fact very much in common and can be treated by the same methods. A need for a uniting theory became obvious. \There are two main
lacunae in recent work on modal logic: a lack of general results and a lack
of negative results. This or that logic is shown to have such and such a property, but very little is known about the scope or bounds of the property.
Thus there are numerous results on completeness, decidability, nite model
property, compactness, etc., but very few general or negative results", wrote
Fine 1974c]. The creation of duality theory between relational and algebraic
semantics (Lemmon 1966a,b], Goldblatt 1976a,b]), originated actually by
Jonsson and Tarski 1951], the establishment of the connection between
modal logics and varieties of modal algebras (Kuznetsov 1971], Maksimova
and Rybakov 1974], Blok 1976]), and between modal and rst and higher
order languages (Fine 1975b], van Benthem 1983]) added those mathematical ingredients that were necessary to distinguish modal logic as a separate
branch of mathematical logic.
On the other hand, various particular systems became subjects of more
special disciplines, like provability logic, deontic logic, tense logic, etc., which
has found reection in the corresponding chapters of this Handbook.
In the 1980s and 1990s modal logic was developing both \in width"
and \in depth", which made it more dicult for us to select material for
this chapter. The expansion \in width" has brought in sight new interesting types of modal operators, thus demonstrating again the great expressive power of propositional modal languages. They include, for instance,
polyadic operators, graded modalities, the xed point and di erence operators. We hope the corresponding systems will be considered in detail
elsewhere in the Handbook in this chapter they are briey discussed in the
appendix, where the reader can nd enough references.
Instead of trying to cover the whole variety of existing types of modal
operators, we decided to restrict attention mainly to the classes of normal
(and quasi-normal) uni- and polymodal logics and follow \in depth" the
way taken by Bull and Segerberg in Basic Modal Logic, the more so that
this corresponds to our own scientic interests.
Having gone over from considering individual modal systems to big classes
of them, we are certainly interested in developing general methods suitable
for handling modal logics en masse. This somewhat changes the standard
set of tools for dealing with logics and gives rise to new directions of research.
First, we are almost completely deprived of proof-theoretic methods like
Gentzen-style systems or natural deduction. Although proof theory has
been developed for a number of important modal logics, it can hardly be
extended to reasonably representative families. (Proof theory is discussed
in the chapter Sequent systems for modal logics some references to recent
results can be found in the appendix.)

ADVANCED MODAL LOGIC

3

In fact, modern modal logic is primarily based upon the frame-theoretic
and algebraic approaches. The link connecting syntactical representations
of logics and their semantics is general completeness theory which stems
from the pioneering results of Bull 1966b], Fine 1974c], Sahlqvist 1975],
Goldblatt and Thomason 1974]. Completeness theorems are usually the
rst step in understanding various properties of logics, especially those that
have semantic or algebraic equivalents. A classical example is Maksimova's
1979] investigation of the interpolation property of normal modal logics
containing S4, or decidability results based on completeness with respect to
\good" classes of frames. Completeness theory provides means for axiomatizing logics determined by given frame classes and characterizes those of
them that are modal axiomatic.
Standard families of modal logics are endowed with the lattice structure
induced by the set-theoretic inclusion. This gives rise to another line of
studies in modal logic, addressing questions like \what are co-atoms in the
lattice?" (i.e., what are maximal consistent logics in the family?), \are there
innite ascending chains?" (i.e., are all logics in the family nitely axiomatizable?), etc. From the algebraic standpoint a lattice of logics corresponds
to a lattice of subvarieties of some xed variety of modal algebras, which
opens a way for a fruitful interface with a well-developed eld in universal
algebra.
A striking connection between \geometrical" properties of modal formulas, completeness, axiomatizability and -prime elements in the lattice of
modal logics was discovered by Jankov 1963, 1969], Blok 1978, 1980b]
and Rautenberg 1979]. These observations gave an impetus to a project
of constructing frame-theoretic languages which are able to characterize
the \geometry" and \topology" of frames for modal logics (Zakharyaschev
1984, 1992], Wolter 1996d]) and thereby provide new tools for proving their
properties and clarifying the structure of their lattices.
One more interesting direction of studies, arising only when we deal with
big classes of logics, concerns the algorithmic problem of recognizing properties of (nitely axiomatizable) logics. Having undecidable nitely axiomatizable logics in a given class (Thomason 1975a], Shehtman 1978b]), it
is tempting to conjecture that non-trivial properties of logics in this class
are undecidable. However, unlike Rice's Theorem in recursion theory, some
important properties turn out to be decidable, witness the decidability of
interpolation above S4 (Maksimova 1979]). The machinery for proving the
undecidability of various properties (e.g. Kripke completeness and decidability) was developed in Thomason 1982] and Chagrov 1990b,c].
Thomason 1982] proved the undecidability of Kripke completeness rst
in the class of polymodal logics and then transferred it to that of unimodal
ones. In fact, Thomason's embedding turns out to be an isomorphism from

T

4

M. ZAKHARYASCHEV, F. WOLTER, AND A. CHAGROV

the lattice of logics with n necessity operators onto an interval in the lattice of unimodal logics, preserving many standard properties (Kracht and
Wolter 1997a]). Such embeddings are interesting not only from the theoretical point of view but can also serve as a vehicle for reducing the study of
one class of logics to another. Perhaps the best known example of such a
reduction is the Godel translation of intuitionistic logic and its extensions
into normal modal logics above S4 (Maksimova and Rybakov 1974], Blok
1976], Esakia 1979a,b]). We will take advantage of this translation to give
a brief survey of results in the eld of superintuitionistic logics which actually were always studied in parallel with modal logics (see also Section 5 in
Intuitionistic Logic).
Listed above are the most important general directions in mathematical modal logic we are going to concentrate on in this chapter. They, of
course, do not cover the whole discipline. Other topics, for instance, modal
systems with quantiers, the relationship between the propositional modal
language and the rst (or higher) order classical language, or proof theory
are considered in other chapters of the Handbook.
It should be emphasized once again that the reader will nd no discussions of particular modal systems in this chapter. Modal logic is presented
here as a mathematical theory analyzing big families of logics and thereby
providing us with powerful methods for handling concrete ones. (In some
cases we illustrate technically complex methods by considering concrete logics for instance Rybakov's 1994] technique of proving the decidability of
the admissibility problem for inference rules is explained only for GL.)

Acknowledgments. First of all, we are indebted to our friend and colleague Marcus Kracht who not only helped us with numerous advices but
also supplied us with some material for this chapter. We are grateful to
Hiroakira Ono and the members of his Logic Group in Japan Advanced
Institute of Science and Technology for the creative and stimulating atmosphere that surrounded the rst two authors during their stay in JAIST,
where the bulk of the chapter was written. Thanks are also due to Johan
van Benthem, Wim Blok, Dov Gabbay, Silvio Ghilardi, Krister Segerberg,
Heinrich Wansing for their helpful comments and stimulating discussions.
And certainly our work would be impossible without constant support and
love of our wives: Olga, Imke and Lilia.
Partly the work of the rst author was nanced by the Alexander von
Humboldt Foundation.

ADVANCED MODAL LOGIC

5

1 UNIMODAL LOGICS
