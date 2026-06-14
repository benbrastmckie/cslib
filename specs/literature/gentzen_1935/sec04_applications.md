<!-- Source: Gentzen, G. (1935). Untersuchungen über das logische Schließen (Investigations into Logical Deduction). Section IV: Some Applications of the Hauptsatz. BibKey: Gentzen1935 -->

9 1. Applications of the Hauptsatz in propositional logic
1.1. A trivial consequence of the Hauptsatz is the already known con-
sistency of classical (and intuitionist) predicate logic (cf., e.g., D. Hilbert
and W. Ackermann, Grundziige der theoretischen Logik (Berlin, 1928,
1st edition), p. 65): the sequent + (which is derivable from every contra-
dictory sequent + % &
'%, cf. 3.21) cannot be the lower sequent of any
inference figure other than of a cut and is therefore not derivable.
1.2. Solution of the decision problem for intuitionist propositional logic.
On the basis of the Hauptsatz we can state a simple procedure for deciding
of a formula of propositional logic - i.e., a formula without object variables -

---

whether or not it is classically or intuitionistically true. (For classical
propositional logic a simple solution has actually been known for some
time, cf., e.g., p. 11 of Hilbert-Ackermann.)
First we prove the following lemma:
A sequent in whose antecedent one and the same formula does not occur
more than three times as an S-formula, and in whose succedent, furthermore,
one and the same formula occurs no more than three times as an S-formula,
will be called a 'reduced sequent'. The following lemma now holds:
1.21. Every LJ- or LK-derivation whose endsequent is reduced, may be
transformed into an LJ- or LK-derivation with the same endsequent,
in which all sequents are reduced (and in which no cuts occur if the original
derivation did not contain any).
PROOF
OF THIS LEMMA: If we eliminate from the antecedent of a sequent,
in any places whatever (possibly none), all S-formulae occurring more
than once, and if we do the same independently in the succedent, so that
eventually these formulae occur only once, twice, or three times, we obtain
a sequent that will be called a 'reduction instance of the given sequent'.
From a reduction instance of a sequent we may obviously derive all other
reduction instances of the same sequent by means of thinnings, contractions,
and interchanges such that in the course of these operations only reduced
sequents occur.
After these preliminary remarks we now transform the LJ- or LK-
derivation at hand in the following way:
All basic sequents as well as the endsequent are left intact; they are already
reduced sequents.
The D-sequents which belong to an inference figure are transformed into
reduction instances of these sequents in a way about to be indicated. By
virtue of our preliminary remark it does not matter if a sequent belonging
to two different D-inference figures is in each case replaced by a diferent
reduction instance, since one sequent is derived very simply from the other
by thinnings, contractions, and interchanges so that eventually another
complete derivation results. (The same holds for a sequent whch, while
belonging to an inference figure, is also a basi,c sequent or an endsequent,
since it is of course a reduction instance of itself.)
The transformations of the inference figures are now carried out in the
following way:
If a formula occurs more than once within r, it is eliminated from r,
both from the upper sequents and the lower sequent, as many times (from

---

!j 1, APPLICATIONS OF THE Hauptsatz IN PROPOSITIONAL LOGIC
105
the appropriate places) as is necessary to ensure that finally it occurs in
r no more than once. The same procedure is used for A ,  0,
and A (i-e.,
those sequences of formulae that are designated by these letters in the
schema 111.1.21 and 1.22, of the inference figure concerned).
Having carried out the transformations described, we have now a deriva-
tion consisting only of reduced sequents. (An interchange where %I
is
identical with B may form an exception, yet this figure would be an identical
inference figure and could have been avoided.)
The lemma is thus proved.
Given the Hauptsatz, together with corollary 111. 2.513, and the preceding
lemma (1.21), it now holds that:
1.22. For every correctly reduced sequent, both intuitionist and classical,
there exists an LJ- or LK-derivation resp. without cuts consisting only of
reduced sequents, and whose D-S-formulae are subformulae of the S-
formula of that sequent.
1.23. Consider now a sequent not containing an object variable. We wish
to decide whether or not it is intuitionistically or classically true. We can
begin by taking in its place an equivalent reduced sequent 6q.
The number of all reduced sequents whose S-formulae are subformulae
of the S-formulae of Gq is obviously finite. The decision procedure may
therefore be carried out without further complications in the following way:
We consider the finite system of sequents in question and investigate
first of all, which of these sequents are basic sequents. Then we examine
each of the remaining sequents to determine whether there occurs an
inference figure in which the sequent in question is the lower sequent and in
which there occur as upper sequents one or two of those sequents that have
already been found to be derivable. If this is the case, the sequent is added
to the derivable sequents. (All this is obviously decidable.) We continue in
this way until either the sequent Gq itself turns out to be derivable, or until
the procedure yields no new derivable sequents. In the latter case the sequent
Gq (by virtue of 1.22) is not derivable at all in the calculus under considera-
tion (LJ or LK). We have therefore succeeded in establishing the validity of
that sequent.
1.3. A new proof of the nonderivability of the law of the excluded middle
in intuitionist logic.
Our decision procedure could have been formulated in a way better suited
to the needs of practical application; yet the above presentation (1.2) was
intended only to indicate a possibility in principle.
As an example, we shall prove the nonderivability of the law of the

---

excluded middle in intuitionist logic by a method independent of the decision
procedure described (although this procedure would have to yield the same
result). (This nonderivability has already been proved by HeytingZ4 in a
completely different way.)
A .  Suppose there exists
an LJ-derivation for it. According to the Hauptsatz there then exists sucb a
derivation without cuts. Its lowest inference figure must be a v-IS, for in
all other LJ-inference figures either the antecedent of the lower sequent is
not empty, or a formula occurs in the succedent whose terminal symbol
is not v; there might still be the case of a thinning in the succedent, but the
upper sequent would then be a +, which, by virtue of 1.1, is not derivable.
Hence either + A or + 1
A would have to be already derivable
(without cuts).
(From the same considerations, incidentally, it follows in general:
If '% v B is an intuitionistically true formula, then either % or B is an
intuitionistically true formula. In classical logic this does not hold, as the
example of A v
Now + A cannot be the lower sequent of any LJ-inference figure whatever
(if it is not a cut), unless that figure is another thinning with -+ for its
upper sequent. Furthermore, since + A is not a basic sequent, it is thus not
derivable.
A is derivable only from A +
by a T-ZS figure, and A + is in turn derivable only from A, A +, since A
contains no terminal symbol. Continuing in this way, we always reach only
sequents of the type A, A, . . . , A +, but never a basic sequent.
The sequent in question is of the form + A v
A already shows.)
The same considerations show that +
Hence A v 1
A is not derivable in intuitionist predicate logic.
0 2. A sharpened form of the Hauptsatz for classical predicate logic
2.1. w e  are here concerned with the following SHARPENING OF THE HAUPTSATZ:
Suppose that we have an LK-derivation whose endsequent is of the
following kind:
Each S-formula of this sequent contains V and hymbols at most at the
beginning, and their scope extends over the whole of the remaining formula.
In that case, the given derivation may be transformed into an LK-deriva-
tion with the same endsequent and having the following properties:
1. It contains no cuts.
2. It contains a D-sequent, let us call it the 'midsequent', which is such
that its derivation (and hence the midsequent itself) contains no V and

---

$2, A SHARPENED FORM OF THE Hauptsatz FOR CLASSICAL PREDICATE LOGIC
107
hymbols, and where the only inference figures occurring in the remaining
part of the derivation, the midsequent included, are V-IS, V-IA, 3-IS, 3-IA,
and structural inference figures.
2.11. The midsequent divides the derivation, as it were, into an upper part
beolnging to propositional logic, and a lower part containing only V and
3introductions.
Concerning the form of the transformed derivation, the following may
still be readily concluded: The lower part, from the midsequent to the
endsequent, belongs to only one path since only inference figures with one
upper sequent occur in it. The S-formulae of the midsequent are of the
following kind:
Every S-formula in the antecedent of the midsequent results from an
S-formula in the antecedent of the endsequent by the elimination of the V
and 3-symbols (together with the bound object variables beside them),
and by the replacement of the bound object variables in the rest of the
formula by certain free object variables. The same procedure is followed
in the case of succedents.
2.2. PROOF OF THE THEOREM (2.1)?
2.21. We begin by applying the Hauptsatz (111.2.5): The derivation may
accordingly be transformed into a derivation without cuts.
2.22. Transformation of basic sequents containing a V- or 3-symbol:
By virtue of the properties of subformulae 111.2.513, such sequents can
only have the form VF & --+ V z  3s or 3z 3~
+ 3g SF. They are trans-
formed into (suppose a to be a free object variable not yet occurring in the
derivation):
This follows from the same consideration as in 111.2.512.
The transformation of the derivation is carried out in several steps.
By repeating this procedure sufficiently often we can obviously eliminate
all V- and 3-symbols from every basic sequent of the derivation.
2.23. We now perform a complete induction on the 'order' of the derivation,
which is defined as follows:
Of the operational inference figures we call those belonging to the symbols
&, v, l, and 13 'propositional inference figures', and the rest, i.e., V-IS,
V-IA, ]-IS, 3-IA, 'predicate inference figures'. To each predicate inference
figure in the derivation we assign the following ordinal number:

---

We consider that path of the derivation that extends from the lower sequent
of the inference figure up to the endsequent of the derivation (including the
endsequent) and count the number of lower sequents of the propositional
inference figures occurring in it. Their number is the ordinal number.
The sum of the ordinal numbers of all predicate inference figures in the
derivation is the order of the derivation.
We intend to reduce that order step by step until it becomes zero.
Note that once this has been achieved the rest of the proof of the theorem
(2.1) is easily carried out: (The steps involved (2.232) will be such as to
preserve the properties that were established in 2.21 and 2.22.)
2.231. In order to do so we assume that the derivation has already been
reduced to order zero. From the endsequent we now proceed to the upper
sequent of the inference figure above it. We stop as soon as we encounter
the lower sequent of a propositional inference figure or a basic sequent;
that sequent we call Gq. (It will serve us as 'midsequent', once it has been
transformed in a way about to be indicated.)
The derivation of 6q is now transformed as follows:
We simply omit all D-S-formulae which still contain the symbols V and
3. The above derivation remains correct after the described operation
since, by virtue of 2.22, its basic sequents are not affected. Furthermore,
no principal or side formula of an inference figure has been eliminated,
for if such a formula had contained a symbol V or 3, the principal formula
would certainly have contained that symbol. But no predicate inference
figures occur (if they did, the ordinal number of the inference figure would
be greater than zero), and by virtue of the subformula property (111.2.513)
and the hypothesis of theorem 2.1, the principal formulae of the proposi-
tional inference figures cannot contain a V or 3. Now every inference figure
remains correct if we eliminate, wherever it occurs as an S-formula in the
figure, a formula which occurs neither as a principal nor as a side formula.
This is easily seen from the schemata 111.1.21 and 111.1.22. (At worst, an
identical inference figure may result, which is then eliminated in the usual
manner.)
The sequent Gq*, which has resulted from Gq by this transformation,
differs from Gq in that certain S-formulae may possibly have been elimi-
nated. We follow the transformation up with several thinnings and inter-
changes such that in the end the sequent Gq reappears, and to it we attach
the unaltered lower part of the derivation.
We have now reached our goal: Gq* is the 'midsequent', and it obviously
satisfies all conditions imposed on the latter by theorem (2.1).

---

0 2, A SHAPRENED FORM OF THE Hauptsatz FOR CLASSICAL PREDICATE LOGIC
109
2.232. It now remains for us to carry out the induction step of our proof,
i.e., the order of the derivation is assumed to be greater than zero, and
our task is to diminish it.
2.232.1. We begin by redesignating the free object variables in the same way
as in 111.3.10. As a result of this, the derivation has the following property
(111.3.101):
For every V-IS (or 1-44) it holds that the eigenvariable in the derivation
occurs only in the sequent above the lower sequent of the V-IS (or 3-IA)
and does furthermore not occur in any other V-IS or 3-IA as an eigen-
variable.
The order of the derivation is hereby obviously left unchanged.
2.232.2. We now come to the transformation proper.
To begin with, we observe that in the derivation there occurs a predicate
inference figure - let us call it Sfl - with the following property: If we
follow that path of the inference figure which extends from the lower
sequent to the endsequent, then the first lower sequent of an operational
inference figure reached is the lower sequent of a propositional inference
figure (that inference figure we call 8f2). If there were no such instance, the
order of the derivation would be equal to zero.
Now our aim is to slide the inference figure Sfl lower down in the deriva-
tion beyond 8f2. This is easily done by means of the following schemata:
2.232.21. Suppose that Sf2 has one upper sequent.
2.232.211. Suppose that Sfl is a V-IS. Then that part of the derivation on
which the operation is to be carried out runs as follows:
r+ @,%a
V-IS
8f2, possibly preceded by structural inference figures.
+ 0 , V Z S E
A + A
This we transform into:
r + 0,
Sa
A + Sa, A
possibly several interchanges, as well as a thinning
possibly preceded by structural inference figures
3% Vb ?& inference figures of exactly the same kind as above, i.e., 3f2,
possibly several interchanges
A + 4 S a
V-IS
A + A, vx Sb possibly several interchanges and contractions.
A + A
The elimination of V& 3 g  by contraction in the last step of the trans-
formation is made possible by the fact that in A, Vg 8~ must occur as an

---

S-formula. (For the S-formula VF 3~
could not, in the original derivation,
have been eliminated from the succedent by means of 9f2 and the preceding
structural inference figures, since it can obviously not be a side formula of
3f2, by virtue of the subformula property 111.2.513 and the hypothesis of
theorem 2.1 .)
The restriction on variables is satisfied by the above V-IS (9fl) by virtue
of 2.232.1.
The order of the derivation has obviously been diminished by 1.
2.232.212. The case where 9fl is a 3-IS is dealt with analogously; all we
need do is to replace V by 3.
2.232.213. The cases where 3fl is a V-IA or 3-IA are treated dually to
the two preceding cases.
2.232.22. The case where 9f2 has two upper sequents, i.e., &-IS, v-IA, or
I-IA, can be dealt with quite correspondingly. At most a number of
additional structural inference figures may be required.
2.3. Analogously to theorem 2.1 there are several ways in which the Haupt-
satz may be further strengthened in the sense that certain restrictions can be
placed on the order of occurrence of the operational inference figures in
a derivation. For we can permute the inference figures to a large extent by
sliding them above and beyond each other as was done above (2.232.2).
We shall not pursue this question further.
6 3. Application of the sharpened Hauptsatz (2.1) to a newz6 consistency
proof for arithmetic without complete induction
By arithmetic we mean the (elementary, i.e., employing no analytic
techniques) theory of the natural numbers. Arithmetic may be formalized
by means of our logical calculus LK in the following way:
3.1. In arithmetic it is cubtomary to employ 'functions', e.g., x' (equals
x+ I), x+y, x * y. Since we have not introduced function symbols into our
logical formalism, we shall, in order to be able to apply it to arithmetic
nevertheless, formalize the propositions of arithmetic in such a way that
predicates take the place of functions. In place of the function x', for
example, we shall use the predicate xPry, which reads: x is the predecessor
of y, i.e., y = x+ 1. Furthermore, [x+y = z ]  will be considered a predicate
with three argument places. Thus the symbols + and = have here no
independent meaning. A different predicate is x = y ;  the equality symbol
here has thus no formal connection at all with the equality symbol in the
previous predicate.

---

9 3, APPLICATION OF THE sharpened Hauptsatz TO A CONSISTENCY PROOF
11 1
The number 1, furthermore, will not be written as a symbol for a definite
object, since we have only object variables in our logical formalism and no
symbols for definite objects. We shall overcome this difficulty by saying that
the predicate 'One
means informally the same as 'x is the number 1'.
The sentence 'x+ 1 is the successor of
for example, could be rendered
thus in our formalism:
All other natural numbers can be respresented by the predicates
One x & xPry; One x & xPry & yPrz, etc.
How are we now to integrate into our calculus the predicate symbols just
introduced, having admitted only propositional variables? To do so we
simply stipulate that the predicate symbols are to be treated in exactly the
same way as propositional variables. More precisely: We regard expressions
of the form
One F 7  FPr97 F = 9 7  (F+9 = a),
where any object variables stand for E, 9, g, merely as more easily intelligible
ways of writing the formulae
In this sense the axiom formulae that follow are indeed formulae in accor-
dance with our definition.
(We cannot, of course, regard the number 1 as a way of writing an object
variable, since in our calculus the object variables really function as variables,
which is not so in the case of propositional variables.)
As 'axiom formulae' of our arithmetic we shall initially take the following,
and shall later, once the consistency proof has been carried out (cf. 3.3),
statq general criteria for the formation of further admissible axiom formulae:
Equality :
vx (x = x)
(reflexivity)
VxVyVz((x = y & y  = z) 3 x  = 2)
3x (One x)
VxVy ((One x & Oney) 3 x = y)
VxVy(x = y 3
y = x)
(symmetry)
(transitivity)
(existence of 1)
(uniqueness of 1)
One:
Predecessor:
Vx 3y (xPry)
(existence of successor)

---

Vx Vy (xpry 3 One y)
(1 has no predecessor)
Vx Vy Vz Vu ((xpry & zPru & x = z) 3
y = u) (uniqueness of successor)
Vx Vy Vz Vu ((xPry & zPru & y = u) 3
x = u) (uniqueness of predecessor).
A formula 23 is called derivable in arithmetic without complete induction,
if there is an LK-derivation for a sequent
al, . . .
y a# + 23
in which gl,
. . . Up are axiom formulae of arithmetic.
The fact that this formal system does actually allow us to represent the
types of proof customary in informal arithmetic (as long as they do not use
complete induction) cannot be proved, since for considerations of an in-
formal character no precisely delimited framework exists. We can merely
verify this in the case of individual informal proofs by testing them.
3.2. We shall now prove the consistency of the formal system just presented.
With the help of the sharpened Hauptsatz (2.1) our task is in fact quite
simple.
3.21. A 'contradiction' & 1
% is derivable in our system if and only if
there exists an LK-derivation for a sequent with an empty succedent and
with arithmetic axiom formulae in the antecedent, viz.:
From r + % &
% we obtain r + in the following way:
7 - I A
% + %
&-IA
interchange
contraction
cut.
&-IA
r+
The converse is obtained by carrying out a thinning in the succedent.
Thus, if our arithmetic is inconsistent, there exists an LK-derivation
with the endsequent
a1 Y * - - 9 ap +,
where
. . . %p are arithmetic axiom formulae.
3.22. We now apply the sharpened Hauptsatz (2.1). The arithmetic axiom
formulae fulfil the requirement laid down for the S-formulae of the end-
sequent. Hence there exists an LK-derivation with the same endsequent
which has the following properties:

---

0 3, APPLICATION OF THE sharpened Hauptsatr TO A CONSISTENCY PROOF
113
1. It contains no cuts.
2. It contains a D-sequent. the 'midsequent', whose derivation contains
no V and 3-symbols, and whose endsequent results from a number of
inference figures V-IA, 34A, thinnings, contractions and interchanges in
the antecedent. The midsequent has an empty succedent (2.11).
3.23. We then proceed to redesignate the free object variables as in 111.3.10.
All mentioned properties remain unchanged, and the following property
is added (111.3.101): The eigenvariable of each 3-IA in the derivation occurs
only in sequents above the lower sequent of the 3-IA.
3.24. Then we replace every occurrence of a free object variable by one and
the same natural number in a way to be described presently. In doing so
we are left with a figure which we can no longer call an LK-derivation.
We shall see later to what extent it nevertheless has an informal sense.
The replacement of the free object variables by numbers is carried out
in the following order:
3.241. First we replace all free object variables which do not occur as the
eigenvariable of a 3-IA by the number 1 throughout. (We could also take
another number.)
3.242. Then we take every 3-IA inference figure in the derivation, beginning
with the lowest and taking each figure in turn, and replace each eigenvariable
(wherever it occurs in the 'derivation') by a number. That number is deter-
mined as follows:
The 3-IA can only run:
One a, r + 0
vPra, r -+ 0
or
3x One x ,  r --+ 0
3y vPry,
+ 0
(by virtue of the subformula property 111.2.513; v can be only a number,
by virtue of 3.241 and 3.23). In the first case we replace a by 1, in the second
case by the number that is one greater than v .
3.25. Now we examine the figure which has resulted from the derivation.
We are particularly interested in what the (former) midsequent now looks
like. We can say this about it:
Its succedent is empty, and each of the antecedent S-formulae either has
the form One 1 or vPrv', where a number stands for v, and where a number
one greater than the previous one stands for v'; or it results from an arith-
metic axiom formula that has only V-symbols at the beginning, by the
elimination of the V-symbols (and the bound object variables next to them)
and the substitution of numbers for the bound object variables in the

---

remaining part of the formula. (All this follows from the same consideration
as in 111.2.512, also cf. 2.11.)
Thus, the S-formulae in the antecedent of the midsequent represent
informally true numerical propositions. It further holds for the 'derivation'
of the midsequent that it has resulted from a derivation containing no
V- or 3-symbols, by having all its occurrences of free object variables
replaced by numbers. Informally, such a 'derivation' constitutes in effect a
proof in arithmetic using only forms of inference from propositional logic.
This leads us to the following result:
If our arithmetic is inconsistent, we can derive a contradiction from true
numerical propositions through the mere application of inferences from
propositional logic.
Here 'true numerical propositions' are propositions of the form One 1,
vPrv', as well as all numerical special cases of general propositions occurring
among the axioms such as, e.g., 3 = 3, 4 = 5 3 5 = 4, 3Pr4 3 1
One 4.
It is almost self-evident that from such propositions no contradictions
are derivable by means of propositional logic. A proof for this would hardly
be more than a formal paraphrasing of an informally clear situation of fact.
Such a proof will therefore not be carried out save for indicating briefly
the customary procedure for it:
We determine generally for which numerical values the formulae
One p, p = v, pPrv, p+v = p, etc., are true and for which values they are
false; furthermore, we explain in the customary way (cf., e.g., Hilbert-
Ackermann p. 3) the truth or falsity of 8 & 58, 8 v 23, 1
a, and
3 23,
as functions of the truth or falsity of the subformulae; we then show that all
numerical special cases of axiom formulae are 'true'; and finally, that
inference figures of propositional logic always lead from true formulae
to other true formulae. A contradiction, however, is not a true formula.
3.3. It is easy to see from the remarks made in 3.25 in what way the system
of arithmetic axiom formulae may be extended without making a contra-
diction derivable in it: Quite generally, we can allow the introduction of
axiom formulae that begin with V-symbols spanning the whole formula,
which do not contain any 3-syrnbols, and of which every numerical special
case is informally true. (We could also admit certain formulae containing
hymbols, as long as they can be dealt with in the consistency proof in a
way analogous to that of the two cases occurring above.)
E.g., the following axiom formulae for addition are admissible:
VxVy (xpry =I [x+I = y1)

---

5 1, THE CONCEPT OF EQUIVALENCE
V X V ~ V Z V U V U
((.Pry
& [z+x = u ]  & [z+y = u ] )  =) upru)
v x  vy vz v u  (( [x+y = z ]  & [x+y = u ] )  =) z = u)
v x v y v z  ( [ x + y  = z ]  3 [ y + x  = z l )
etc.
3.4. Arithmetic without complete induction is, however, of little practical
significance, since complete induction is constantly required in number
theory. Yet the consistency of arithmetic with complete induction has not
been conclusively proved to date.
SECTION V. THE EQUIVALENCE OF THE NEW CALCULI NJ, NK,
