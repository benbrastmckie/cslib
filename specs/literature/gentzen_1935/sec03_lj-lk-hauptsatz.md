<!-- Source: Gentzen, G. (1935). Untersuchungen über das logische Schließen (Investigations into Logical Deduction). Section III: The Deductive Calculi LJ, LK and Proof of the Hauptsatz. BibKey: Gentzen1935 -->

HAUPTSATZ
0 1. The calculi LJ and LK (logistic intuitionist and classical calculi)
1.1. Preliminary remarks concerning the construction of the calculi U
and LK.

---

## 82

What we want to do is to formulate a deductive calculus (for predicate
logic) which is 'logistic' on the one hand, i.e., in which the derivations do not,
as in the calculus NJ, contain assumption formulae, but which, on the other
hand, takes over from the calculus NJ the division of the forms of inference
into introductions and eliminations of the various logical symbols.
The most obvious method of converting an NJ-derivation into a logistic
one is this: We replace a D-formula 23, which depends on the assumption
formulae !211 , . . . , !21p, by the new formula (al & . . . & 'illp) 3 23. This
we do with all D-formulae.
We thus obtain formulae which are already true in themselves, i.e., whose
truth is no longer conditional on the truth of certain assumption formulae.
This procedure, however, introduces new logical symbols & and 3,
neces-
sitating additional inference figures for & and 3,
and thus upsets the
systematic character of our method of introducing and eliminating symbols.
For this reason we have introduced the concept of a sequent (1.2.3). Instead
of a formula (a, & . . . & 'illp) 3
23, e.g., we therefore write the sequent
The informal meaning of this sequent is no different from that of the
above formula; the expressions differ merely in their formal structure
(cf. I. 2.4).
Even now new inference figures are required that cannot be integrated
into our system of introductions and eliminations; but we have the advantage
of being able to reserve them special places within our system, since they
no longer refer to logical symbols, but merely to the structure of the sequents.
We therefore call these 'structural inference figures', and the others 'opera-
tional inference figures'.
In the classical calculus NK the law of the excluded middle occupied a
special place among the forms of inference (11.5.3), because it could not be
integrated into our system of introductions and eliminations. In the classical
logistic calculus LK about to be presented, this characteristic is removed.
This is made possible by the admission of sequents with several formulae
in the succedent, whereas the transition from the calculus NJ just described
led only to sequents with one formula in the succedent. (For the informal
meaning of sequents in general cf. 1.2.4.) The symmetry thus obtained is
more suited to classical logic. On the other hand, the restriction to at most
one formula in the succedent will be retained for the intuitionist calculus
LJ. (Cf. below. - An empty succedent means the same as if A stood in the
succedent. )

---

## 8 1, THE CALCULI u
AND LK
We have thus outlined a number of points that underlie the construction
of the calculi that follow. Their form is largely determined, however, by
considerations connected with the 'Hauptsatz' (a 2) whose proof follows
later. That form cannot therefore be justified more fully at this stage.
1.2. We now define the concepts of an 'LK-derivation' and an 'LJ-derivation'
as follows:
An LJ- or LK-derivation consists of sequents arranged in tree form
(1.3.3).
The initial sequents of the derivation are basic sequents of the form
5D + 3,
where 5D may be an arbitrary formula.
Each inferencefigure of the derivation results from one of the schemata
below by a substitution of the following kind (cf. 11.2.21):
Replace a, 23, B, Q by an arbitrary formula; for Vx 3~
( 3 ~
3~)
put an
arbitrary formula having V(3) for its terminal symbol, where
designates
the associated bound object variable; for 3a put that formula which is
obtained from Sx by replacing every occurrence of the bound object
variable g by the free object variable a.
For r, A ,  0, A put arbitrary (possibly empty) sequences of formulae
separated by commas.
The following restriction is furthermore placed on LJ-inference figures
(this is the only respect in which the concepts of an LJ- and an LK-derivation
differ):
'In the succedent of each D-sequent no more than one S-formula may
occur'.
The designations of the various schemata for operational inference figures
&-IS, &-IA, etc., are intended to mean: An inference figure formed
according to the schema is an introduction ( I )  in the succedent (S) or
antecedent ( A )  of the conjunction (&), the disjunction (v), the universal
quantifier (V), the existential quantifier (3), the negation (-I), or the
implication (3).
The inference jgure schemata
1.21. Schemata for structural inference figures:
Thinning:
in the antecedent
in the succedent
r-+@
r-+o .
%,r+o'
r - + 0 , B 7

---

## 84

Contraction:
in the antecedent
in the succedent
sb, sb, r -+ o
r -+ o,~,sb.
%,r-+d r-+o,%
Interchange:
in the antecedent
in the succedent
A ,  9, e, r -+ o
A ,  e, B, r -+ o
r -+ o, e, 9, A .
r -+ o, %,&, A
cut:
r-+o,s B , A - + A
r, 4 -+ o, A
1.22. Schemata for operational inference figures:
@,r-+o
3Zi!iO, r -+ 0
3-IA :
Restrictions on variables: The object variable in the last two schemata,
which is designated by a and is called the eigenvariable of the V-IS (S-IA),
must not occur in the lower sequent of the inference figure (i.e., not in
r, 0, and 3 ~ ) .

---

## 8 2, SOME REMARKS CONCERNING THE CALCULI LJ AND LK
85
r40,9i
l u , r + o
u, r -+ o, B
r + o, u 3 B '
r + o , u
B , A + A
u = , ~ , r , ~ + o , n
1 - I A  :
34s :
3-IA:
1.3. Example of an LJ-derivation (using 11.1.3):
1 - f  A
1
3~ Fx, 3~ FX +
3~ Fx, i
3~ FX +
Fa + Fa
3-1s
Interchange
Fa + 3x Fx
-
Cut
Fa,
3x Fx +
1-IS
3x Fx +
Fa
v-IS
i 3 x  FX + Vy i
F y
=-IS.
+ (7
3x Fx) 3
( V p  Fy)
1.4. Example of an LK-derivation (derivation of the 'law of the excluded
middle'):
A + A
1-1s
A
v-IS
+ A, i
+ A , A v T A
+ A v - - I A , A
+ A V  7
A , A v  --I A
- t A v i A
Interchange
v-I s
Contraction.
0 2. Some remarks concerning the calculi LJ and LK. The Hauptsatz
(We shall make no further use, in this paper, of remarks 2.1 to 2.3.)
2.1. The schemata are not all mutually independent, i.e., certain schemata
could be eliminated with the help of the remaining ones. Yet if they were
left out, the 'Hauptsatz' would no longer be valid.
2.2. In general, we could simplifv the calculi in various respects if we
attached no importance to the Hauptsatz. To indicate this briefly: the

---

## 86

inference figures &-IS, v-ZA, &-ZA, v-IS, V-IA, 3-ZSY 1-ZS, 1-ZA, and
=-ZA
in the calculus LK could be replaced by basic sequents according to
the following schemata:
8,B+8&%
8VB-+8,B 8 & B + 8
% & B + B
8 + % V %
% + 8 V B
Vs8:F + 8 a
8 a  + %8:F
+ 8,
7
8 (law of the excluded middle)
1
8,8
+ (law of contradiction)
%=%,8+B.
These basic sequents and our inference figures may easily be shown
to be equivalent.
The same possibility exists for the calculus LJ, with the exception of the
inference figures v-ZA and l-ZS,
since LJ-D-sequents may not in fact
contain two S-formulae in the succedent (cf. V. 9 5).
2.3. The distinction between intuitionist and classical logic is, externally,
of a quite different type in the calculi L J  and LK from that in the calculi
NJ and NK. In the case of the latter, the distinction is based on the inclusion
or exclusion of the law of the excluded middle, whereas for the calculi L J
and LK the difference is characterized by the restriction on the succedent.
(The fact that both distinctions are equivalent will become evident as a
result of the equivalence proofs in section V for all calculi discussed in this
2.4. If 1-ZS and the 1-ZA are excluded, the calculus LK is dual in the
following sense: If we reverse all sequents of an LK-derivation (in which the
=-symbol
does not occur), i.e., if for
, . . . , 8,,
+ Bl , . . . , Bv
we put
By,.
. . , B1 + a,,,.
. . , g1,
and if we exchange, in inference figures with
two upper sequents, the right- and left-hand upper sequents, including their
derivations, and also replace every occurrence of & by v, V by 3, v by &,
and 3 by V (in the case of & and v we also have to interchange the respective
scopes of the symbols, e.g., for B v 8
we have to put 8
& B), then another
LK-derivation results.
This can be seen at once from the schemata. (Special care was taken to
arrange them in such a way as to bring out their symmetry.) (Cf. H.-A.'s
duality principle, p. 62.)
2.41. In any case, the =-symbol may, in a well-known manner, be eliminated
from the calculus NK, by regarding 8
3 B as an abbreviation for (1
8)
v B.
It may easily be shown that the schemata for the 3-ZS and the Z-ZA
may then be replaced by the schemata for v and l.
paper. 1

---

## 8 2, SOME REMARKS CONCERNING THE CALCULI u
AND LK
The calculus NJ has no corresponding property.
2.5. The most important fact for us with regard to the calculi L J  and LK
is the following:
HAUPTSATZ:
Every LJ- or LK-derivation can be transformed into an LJ-
or LK-derivation with the same endsequent and in which the inference
figure called a 'cut' does not occur.
The proof follows in 0 3.
2.51. In order to give greater clarity to the meaning of the Hauptsatz,
we shall prove a simple corollary (2.513).
For this purpose we introduce a number of expressions (which will be
needed frequently later on) relating to the operational inference figures:
2.511. That S-formula which contains the logical symbol in its schema will
be called the principal formula of an inference figure.
For the &-IS and the &-IA this is simply the S-formula of the form
2l & 23; for the v-IS and the v-IA it is 2l v 23; for the V-IS and the V-IA
it is VF 8s; for the 3-IS and the 3-IA it is 3s 8s; for the ?-IS and the
7 - I A  it is
8;
and for the =-IS and the 3 - I A  it is 2l 1
23.
The S-formulae designated by a, 23, Sa in the schemata will be called
the side formulae of the respective inference figures.
They are always subformulae of the principal formula (according to the
definition of a subformula in 1.2.2).
2.512. We can now easily read off the following facts from the inference
figure schemata:
The principal formula occurs always in the lower sequent and the side
formulae always in the upper sequents of an operational inference figure.
If a formula occurs as an S-formula in an upper sequent of a given
inference figure, and if it is here neither a side formula nor the % of a cut,
then it occurs also as an S-formula in the lower sequent.
These two facts entail the following:
If anywhere in an LJ- or LK-derivation a formula occurs as an S-formula,
and if we trace the path of the derivation from the formula concerned up
to the endsequent, the formula can only vanish from that path if it is the
% of a cut or the side formula of an operational inference figure. In the
latter case, however, there appears, in the next sequent, the principal formula
of the inference figure of which our side formula is a subformula. To that
principal formula we can then, continuing downwards, apply the same
consideration, and so on. Thus we obtain the following corollary:
2.513. COROLLARY
OF THE HAUPTSATZ
(SUBFORMULA PROPERTY): In an LJ- or

---

## 88

LK-derivation without cuts, all occurring D-S-formulae are subformulae of
the S-formulae that occur in the endsequent.
2.514. Intuitively speaking, these properties of derivations without cuts
may be expressed as follows: The S-formulae become longer as we descend
lower down in the derivation, never shorter. The final result is, as it were,
gradually built up from its constituent elements. The proof represented by
the derivation is not roundabout in that it contains only concepts which
recur in the final result (cf. the synopsis at the beginning of this paper).
3 F 3g) 3
(Vg 7
39)
msy be written without a cut as follows:
Example: The derivation given above (1.3) for + (
Fa -+ Fa
Fa -+ 3x Fx 34s
1 - I A
3x Fx, Fa +
Fa,
3x Fx -+
Interchange,
etc., as above.
$3. Proof of the Hauptsatz
The Hauptsatz runs as follows:
Every LJ- or LK-derivation can be transformed into another LJ- or
LK-derivation with the same endsequent, in which no cuts occur.
3.1. Proof of the Hauptsatz for LK-derivations.
We introduce a new inference figure (in order to facilitate the proof)
which constitutes a modified form of the cut, and which we call a mix.
The schema of that figure runs as follows:
In order to obtain an inference figure from this schema, 0 and A must be
replaced by sequences of formulae, separated by commas, in each of which
occurs at least once (as a member of the sequence) a formula of the form D,
called the 'mix formula'; and @* and A* must be replaced by the same
sequences of formulae, save that all formulae of the form '93 occurring as
members of the sequence are omitted. ('93 may be any arbitrary formula.)
r and A must be replaced, as in the other schemata, by arbitrary (possibly
empty) sequences of formulae, separated by commas.

---

## § 3, PROOF OF THE Hauptsatz
Example of a mix:
## 89
A + B y  1 A
B V  C, B, By D, B 4
A , B v C , D + i A
B is the mix formula.
We notice at once that every cut may be transformed into a mix by means
of a number of thinnings and interchanges. (Conversely, every mix may be
transformed into a cut by means of a certain number of preceding inter-
changes and contractions, though we do not use this fact.)
In the following we shall consider only derivations in which no cufs occur,
but which may contain mixes instead.
Since derivations in the old sense may be transformed into derivations
of the new kind, it suffices, for the proof of the Hauptsatz, to show that a
derivation of the new type may be transformed into a derivation with
no mix.
Furthermore, the following lemma is already sufficient:
LEMMA:
A derivation with a mix for its lowest inference figure, and not
containing any other mix, may be transformed into a derivation (with the
same endsequent) in which no mix occurs.
From this the theorem as a whole easily follows:
In an arbitrary derivation consider a mix above whose lower sequent
no further mix occurs. The derivation for this lower sequent is then of the
kind mentioned in the lemma, i.e., it may be transformed in such a way
that it no longer contains a mix. In doing so, the rest of the derivation
remains unchanged. This operation is then repeated until every mix has
systematically been eliminated.
It now remains for us to establish the proof of the lemma. (This proof
extends into 3.2 incl.)
We have to consider a derivation whose lowest inference figure is a mix
and which contains no other mix.
The degree of the mix formula will be called the 'degree of the derivation'
(defined in 1.2.2).
We shall call the rank of the derivation the sum of its rank on the left
and its rank on the right. These two terms are defined as follows:
The left rank is the largest number of consecutive sequents in a path so
that the lowest of these sequents is the left-hand upper sequent of the mix
and each of the sequents contains the mix formula in the succedent.

---

The right rank is (correspondingly) the largest number of consecutive
sequents in a path so that the lowest of these sequents is the right-hand
upper sequent of the mix and each of the sequents contains the mix formala
in the antecedent.
The lowest possible rank is evidently 2.
To prove the lemma we carry out two complete inductions, one on the
degree y, the other on the rank p ,  of the derivation, i.e., we prove the
theorem for a derivation of degree y, assuming it to hold for derivations
of a lower degree (in so far as there are such derivations, i.e., as long as
y is not equal to zero), supposing, therefore, that derivations of lower
degree can already be transformed into derivations with no mix. Further-
more, we shall begin by considering the case where the rank p of the deriva-
tion equals 2 (3.11), and after that the case of p > 2 (3.12), where we
assume that the theorem already holds for derivations of the same degree,
but of a lower rank.
In the following German capital letters will generally serve as syntactic
variables for formulae, and Greek capital letters as syntactic variables for
(possibly empty) sequences of formulae.
In transforming derivations, we shall occasionally meet 'identical inference
figures', i.e., inference figures with identical upper and lower sequents.
Since we have not admitted such figures in our calculus, they must be
eliminated as soon as they occur; we can do this trivially by omitting one of
the two sequents.
The mix formula of the mix that occurs at the end of the derivation is
designated by !JJ?. It is of degree y.
3.10. Redesignating of free object variables in preparation for the trans-
formation of derivations.
3.101. For every V-IS (3-IA) it holds that: Its eigenvariable occurs in the
derivation only in sequents above the lower sequent of the V-IS ( 3 4 4 )
and does not occur as an eigenvariable in any other V-IS (344).
3.102. This is achieved by redesignating free object variables in the follow-
ing way:
We take a V-IS (3-IA) above whose lower sequent either no further
inference figures of this kind occur, or if they do, they have already been
dealt with in a way still to be described.
In all sequents above the lower sequent of this inference figure we replace
the eigenvariable by one and the same free object variable which, so far,
has not yet occurred in the derivation. This obviously leaves the V-IS
We wish to obtain a derivation that has the following properties:

---

5 3, PROOF OF THE Hauptsatr
91
(344) itself correct, as is easily seen. (The eigenvariable did not in fact
occur in its lower sequent.) Furthermore, rest of the derivation remains
correct, as is shown by the lemma to follow shortly.
A systematic application of this method to every single V-IS and 3-IA,
thus leaves the derivation correct throughout and the conclusion ob-
viously has the desired property (3.101). Furthermore, as was essential,
the degree and rank of the derivation, as well as its endsequent, have
remained unaltered.
3.103. Now we give the still outstanding proof of the following lemma.
(It is enunciated in a somewhat more general form than is immediately
necessary, since we shall have to apply it again later on (3.1 13.33))
An LK-basic sequent or inference figure becomes a basic sequent or
inference figure of the same kind, if we replace a free object variable which
is not the eigenvariable of the inference figure in all its occurrences in the
basic sequent or inference figure, by one and the same free object variable,
provided again that this is not the eigenvariable of the inference figure.
This holds trivially except for the V-IS, V-IA, 3-1s and 3 4 4 .  Even here,
however, there is no cause for concern: the restrictions on variables are not
violated, since we may neither substitute nor replace the eigenvariable.
(This is the reason why both restrictions on variables are necessary.)
Furthermore, the formula resulting from %a is again obtained by substituting
a for F in the formula resulting from 3:s.
Having prepared the way (3.10), we now proceed to the actual transforma-
tion of the derivation which serves to eliminate the mix occurring in it.
As already mentioned, we distinguish the two cases: p = 2 (3.11) and
p > 2 (3.12).
3.11. Suppose p = 2.
We distinguish between several individual cases, of which the cases
3.111, 3.112, 3.113.1, 3.113.2 are especially simple in that they allow the
mix to be immediately eliminated. The other cases (3.113.3) are the most
important since their consideration brings out the basic idea behind the
whole transformation. Here we use the induction hypothesis with respect
to y, i.e., we reduce each one of the cases to transformed derivations of a
lower degree.
3.111. Suppose the left-hand upper sequent of the mix at the end of the
derivation is a basic sequent. The mix then reads:
%R+%R
A + A
%R,A*-+A
7

---

which is transformed into:
A - + A
!JX,A*-+A possibly several interchanges and contractions.
That part of the derivation which is above A -+ A remains the same, and
we thus have a derivation without a mix.
3.112. Suppose the right-hand upper sequent of the mix is a basic sequent.
The treatment of this case is symmetric to that of the previous one. We have
only to regard the two schemata as 'duals' (cf. 2.4).
3.113. Suppose that neither the left- nor the right-hand upper sequent of
the mix is a basic sequent. Then both are lower sequents of inferenceJigures
since p = 2, and the right and left rank both equal 1, i.e.: In the sequents
directly above the lef-hand upper sequent of the mix, the mix formula !JX
does not occur in the succedent; in the sequents directly above the right-hand
upper sequent '3n does not occur in the antecedent.
Now the following holds generally: If a formula occurs in the antecedent
(succedent) of the lower sequent of an inference figure, it is either a principal
formula or the 9 of a thinning, or else it also occurs in the antecedent
(succedent) in at least one upper sequent of the inference figure.
This can be seen immediately by looking at the inference figure schemata
If we now consider the hypotheses in the following three cases, we see
at once that they exhaust all the possibilities that exist within case 3.113.
3.113.1. Suppose the left-hand upper sequent of the mix is the lower sequent
of a thinning. Then the conclusion of the derivation runs:
(1.21, 1.22).
r-+o
r + o , n
A + A
r, A* --* 0,
A
This is transformed into:
r + o
possibly several thinnings and interchanges.
r, A* --f 0,
A
That part of the derivation which occurs above A --f A disappears.
3.113.2. Suppose the right-hand upper sequent of the mix is the lower
sequent of a thinning. This case is dealt with symmetrically to the
previous one.
3.113.3. The mix formula % occurs both in the succedent of the left-hand

---

0 3, PROOF OF THE Hauptsatz
93
upper sequent and in the antecedent of the right-hand upper sequent solely
as the principal formula of one of the operational inference figures.
is &, v, V, 3, 1,
1,
we distinguish the cases 3.113.31 to 3.113.36 (a formula without logical
symbols cannot be a principal formula).
3.113.31. Suppose the terminal symbol of YI'l is &. In that case the end of
the derivation runs:
Depending on whether the terminal symbol of
'5
r2 * '2
&-IA
&-IS
rl -+ @,,a rl -+ q , ~
rl,r2
-+
mix
rl -+ @ , , a & ~
a&23,r2-+02
(the other form of the &-IA is treated analogously).
We transform it into:
rl -+ 0, , a
a, r2
-+ o2 mix
rl , r; -+ o;, o2
rl,r2
-+ ol,
o2
possibly several thinnings and interchanges.
We can now apply the induction hypothesis with respect to y to that part
of the derivation whose lowest sequent is rl , rz + O:, 0, , because it has
a lower degree than y. (a obviously contains fewer logical symbols than
8 & 23.) This means that the whole derivation may be transformed into
one with no mix.
3.113.32. Suppose the terminal symbol of )rJt is v. This case is dealt with
symmetrically to the previous one.
3.113.33. Suppose the terminal symbol of )rJt is V. Then the end of the
derivation runs:
This is transformed into:
rl -+ o1 , 8b
?ih rz -, o2 mix
rl,r; -+ o;, o2
rl,r2
-+ 01,02
possibly several thinnings and interchanges.
Above the left-hand upper sequent of the mix, rl 3 0, , %by we write
the same part of the derivation which previously occurred above
rl -+ 0, , %a, yet having replaced every occurrence of the free object
variable a by b. It now follows from lemma 3.103, together with 3.101,

---

that in performing this operation the part of the derivation aboue
rl -+ 0, , Sb has again become a correct part of the derivation. (By virtue
of 3.101 neither a nor b can be the eigenvariable of an inference figure
occurring in that part of the derivation.) The same consideration may be
applied to that part of the derivation which includes the sequent
rl -+ 0, , ?jb, since it too results from rl -+ a,, %a by the substitution
of b for a. It is now in fact clear that by virtue of the restriction on variables
for V-IS, a could have occurred neither in rl and 0, , nor in 8 ~ .
Further-
more, %a results from '& by the substitution a for x, and sb from Sx by the
substitution b for x. This is why sb results from Sa by the substitution b
for a.
The mix formula 86 in the new derivation has a lower degree than y.
Therefore, according to the induction hypothesis, the mix may be eliminated.
3.113.34. Suppose the terminal symbol of Zm is 3. This case is dealt with
symmetrically to the previous one.
3.113.35. Suppose the terminal symbol of Zm is l. Then the end of the
derivation runs:
a,rl
-+ o1
r2 -+ 02, a
7 4 s
7 - I A
rl -+ ol, la
1
a, r2 + 0 2
mix.
rl, r2
-+ o,, o2
This is transformed into:
r2
-+ 02,a %,r1
-+ o, mix
r2,r:
-+ or, o,
rl,r2
-+ ol,
o2
possibly several interchanges and thinnings.
The new mix may be eliminated by virtue of the induction hypothesis.
3.113.36. Suppose the terminal symbol of Zm is 2.
Then the end of the
derivation runs:
r-+o,a B , A - + A
a = BJ, A -+ o, A
=-IS
3-IA
a, rl -+ o,, B
mix.
rl -+ @,,a 3 B
r, , r, A -+ o, , o, A
a , r , - + o l , ~
B , A - + A
This is transformed into:
mix
mix
r+o,a
% J , ,  A* -+ O:, A
r, r:, A** -+ 0*, O:, A
possibly several interchanges and thinnings.
rl , r, A -+ o1 , o, A

---

$ 3 ,  PROOF OF THE Hauptsatz
95
(The asterisks are, of course, intended as follows: A* and @* result from
A and 0,
by the omission of all S-formulae of the form %; r* , A** and @*
result fromr, , A* and 0 by the omission of all S-formulae of the form 8.)
Now we have two mixes, but both mix formulae are of a lower degree than
y. We first apply the induction hypothesis to the upper mix (i.e., to that
part of the derivation whose lowest figure it is). Thus the upper mix may be
eliminated. We can then also eliminate the lower mix.
3.12. Suppose p > 2.
To begin with, we distinguish two main cases: First case: The right rank
is greater than 1 (3.121). Second case: The right rank is equal to 1 and the
left rank is therefore greater than 1 (3.122).
The second case may essentially be dealt with symmetrically to the first.
3.121. Suppose the right rank is greater than 1.
1.e.: The right-hand upper sequent of the mix is the lower sequent of an
inference figure, let us call it Sf, and
occurs in the antecedent of at least
one upper sequent of Sf.
The basic idea behind the transformation procedure is the following:
In the case of p = 2, we generally reduced the derivation to one of a
lower degree. NOW, however, we shall proceed to reduce the derivation to
one of the same degree, but of a lower rank, in order to be able to use the
induction hypothesis with respect to p.
The only exception is the first case, 3.121.1, where the mix may be
eliminated immediately.
In the remaihing cases the reduction to derivations of a lower rank is
achieved in the following way: The mix is, as it were, moved up one level
within the derivation, beyond the inference figure Sf. (Case 3.121.231,
for example, illustrates this point particularly well.) To speak more precisely,
the left-hand upper sequent of the mix (which from now on will be de-
signated by I7 + Z), at present occurring beside the lower sequent of Sf,
is instead written next to the upper sequents of Sf. These now become upper
sequents of new mixes. The lower sequents of these mixes are now used as
upper sequents of a new inference figure that takes the place of Sf. This
new inference figure takes us back either directly, or after having added
further inference figures, to the original endsequent. Each new mix obviously
has a rank smaller than p, since the left rank remains unchanged and the
right rank is diminished by at least 1.
In the strict application of this basic idea special circumstances still arise
which make it necessary to distinguish the corresponding cases and to deal
with them separately.

---

INVESTIoATIONS INTO LOGICAL DEDUCTION
3.121.1. Suppose 9Jl occurs in the antecedent of the left-hand upper sequent
of the mix. The end of the derivation runs:
This is transformed into:
A - t A
possibly several thinnings, contractions and interchanges.
n, A* + z*, A
3.121.2. Suppose
does not occur in the antecedent of the left-hand upper
sequent of the mix.(This hypothesis will be used for the first time in 3.121.222.)
3.121.21. Suppose 8f is a thinning, contraction, or interchange in the
antecedent. Then the end of the derivation runs:
Qf
ly-0
n + z
3 - 0  mix.
n, 8* + z*, 0
This is transformed into:
possibly several interchanges
Y*. n + x*. 0 -
F,
n -+ x*, 0 "
n,5* 4 z*, 0
possibly several interchanges.
The inference figure marked $ is of the same kind as 3f, in so far as the
S-formulae designated in the schema of 8f (in 1.21) by 5D and Q, were not
equal to D. If 5D or Q is equal to B, we have an identical inference figure
(Y* equals S*).
The derivation for the lower sequent of the new mix has the same left
rank as the old derivation, whereas its right rank is lower by 1. Thus the mix
may be completely eliminated by virtue of the induction hypothesis.
3.121.22. Suppose af is an inference figure with one upper sequent, but not
containing a thinning, contraction, or interchange in the antecedent. Then
the end of the derivation runs:
n+x
z,r+tz,
n, %*, r* + z*, n,
mix.

---

## 8 5. PROOF OF THE Hauptsatz
Here we have collected in 1" the same S-formulae that are designated by
r in the schema of the inference figure (1.21, 1.22). Hence Y may be empty
or consist of a side formula of the inference figure, and E may be empty or
consist of the principal formula of the inference figure.
First of all, the end of the derivation is transformed into:
n-+z ~ , r - + a ~
n, Y*, r* -+. c*, 52,
Y ,  r*, n -+ z*, al
8, r*, n -+ c*, 52,
mix
possibly several interchanges and thinnings.
The lowest inference is obviously an inference figure of the same kind as
Sf (taking r*, n as the r of the inference figure and including Z* in the 0
of the inference figure).
We must only be careful not to violate the restrictions on variables
(if 8f is a V-IS or 3 - h ) :  Any such violation is precluded by 3.101, which
entails that an eigenvariable that may have occurred in Sf cannot have
occurred in 17 and Z.
The mix may be eliminated from the new derivation by virtue of the
induction hypothesis.
We therefore obtain a derivation with no mix and which is terminated
by the following inference figure:
Y ,  r*, n -+ z*, 52,
E, r*, n -+ z*, a2 '
In general, the endsequent is not yet of the form aimed at. Hence we
proceed as follows:
3.121.221. Suppose E does not contain '9X.
In that case we perform a number of interchanges, if necessary, and
obtain the endsequent of the original derivation.
3.121.222. Suppose B contains '9X. Then E is the principal formula of sf
and is identical with %. We then adjoin:
n -+ L;
%, r*, n -+ z*, 52,
n, r*, n* .+ z*, c*, sz,
n, r* -+ z*, a,
possibly several contractions and interchanges.
Once again, this is the endsequent of the original derivation. (Above
l7 -+ Z we once more write the derivation associated with it.) Thus we have
another mix in the derivation. The left rank of our derivation is the same

---

as that of the original derivation. The right rank is now equal to 1. This
is so because directly above the right-hand upper sequent occurs the sequent
Y, r*, n -, z*, a,.
m no longer occurs in its antecedent, for r* does not contain 'D, nor
does n, because of 3.121.2; and Y contains at most one side formula of
3f, which cannot be equal to m, since the principal forniula of 3f is equal
to m.
Hence this mix, too, may be eliminated by virtue of the induction hypo-
thesis.
3.121.23. Suppose 3f is an inference figure with two upper sequents, i.e.,
a &-IS, v-IA, or a x-IA.
(In view of the application to intuitionist logic (3.2) we shall deal with
each possibility in greater detail than would be necessary for the classical
case.)
3.121.231. Suppose Sf is a &-IS.
Then the end of the derivation runs:
r-+o,a r-+o,%
&,Is
mix.
u - + z
r - + o , % m
n, r* -+ z*, o, 'LI & %
(m occurs in r.) This is transformed into:
n-+c
r - + o , a m i x  n + z
r-+o,%
mix
n, r* -+ z*, o, 'LI
n, r* -+ z*, 0, %
&-Is.
n, r* -+ z*, o, % & 8
Both mixes may be eliminated by virtue of the induction hypothesis.
Then the end of the derivation runs:
3.121.232. Suppose Sf is a d-IA.
V-IA
%,r-+o %,r-,o
n + c
ixv%,r-+o
mix.
n, (a v %)*, r* -+ c*, o
((a v %)* stands either for
unequal or equal to !lX.)
and the right rank would be equal to 1 contrary to 3.121.)
v % or for nothing according as 'LI v % is
'D certainly occurs in r. (For otherwise !lX would be equal to 'LI v 8,
To begin with, we transform the end of the derivation into:

---

0 3, PROOF OF THE Hauptsatz
99
n 4 z  %,r-+omix
II -+ I: %, r' -+ o mix
a, n, r* -+ z*, 0
r* * '*,
possibly several inter-
changes and thinnings n,
B*9 r*
--f Z*7
@ possibly several inter-
changes and thinnings
8,
n, r* -+ z*, o v-IA.
8 v B, n, r'* -+ z*, o
Both mixes may be eliminated by virtue of the induction hypothesis.
From here on the procedure is the same as that in 3.121.221 and 3.121.222,
i.e., we distinguish two cases according as % v B is unequal or equal to YJl.
In the first case we may have to add several interchanges to obtain the
endsequent of the original derivation; in the second case we add a mix with
Il -+ I: for its left-hand upper sequent, and thus once again obtain the
endsequent of the original derivation by going on to perform a number of
contractions and interchanges, if necessary. The mix concerned may be
eliminated, since the associated right rank equals 1. (All this as in 3.121.222.)
3.121.233. Suppose 3f is a I-IA.
Then the end of the derivation runs:
3.121.233.1. Suppose 2Jl occurs in r and A .
In that case we begin by transforming the derivation into:
I I + Z
B , A - + A m i x
n + ~
r-+0,%
%*, '*
-+ '*,
possibly several inter-
mix
changes and thinnings
I - I A .
n, r* 4 z*, o, %
%, II, A* -+ Z*, A
8 3 8, n, r*, 17, A* + Z*, 0, Z*, A
Both mixes may be eliminated by virtue of the induction hypothesis.
'Then we proceed as in 3.121.221 and 3.121.222. (All that may happen in
the first case is that beside interchanges a number of contractions become
necessary.)
3.121.233.2. Suppose 2Jl does not occur in both r and A simultaneously.
%R must occur in either r or A because of 3.121. Consider the case of YIl
occurring in A but not in r. The second case is treated analogously.
The end of the derivation is transformed into:

---

IZ-+Z
B , A - t A m i x
possibly several interchanges and thinnings
n, B*, A* -, Z*, A
8, n, A* -+ c*, A 3-IA.
r-+B,a
8 3 8, r, n, A* -+ O,,Z*, A
The mix may be eliminated by virtue of the induction hypothesis. We
then proceed as in 3.121.221 and 3.121.222. (In the second case, where
% 3 B is equal to %!, the right rank belonging to the new mix equals 1 as
always, since %! does not occur in By n, A* for the usual reasons, nor does
it occur in r according to the assumption in the case under consideration.)
3.122. Suppose the right rank is equal to 1. In that case the left rank is
greater than 1.
This case is, in essence, treated dually to 3.121. Special attention is required
only for those inference figures with no symmetric counterpart, viz., the
3-ZS and the 3-ZA.
The inference figures 3f with one upper sequent were incorporated, in
3.121.22, in the general schema:
The dual schema runs:
Q, -+ r, Y
n, -+ r,
which also covers the 3-1s without any further change. (r here represents
the formulae designated by 0 in the schemata 1.21, 1.22.)
3.122.1. On the other hand, the case where the inference figure %f is a
I-IA, must be treated separately. Although this treatment will seem very
similar to that in 3.121.233, it is not entirely dual.
Thus the end of the derivation runs:
3.122.11. Suppose
the end of the derivation into:
occurs both in 0 and A. In that case we transform

---

## 8 3, PROOF OF THE Hauptsatz
Both mixes may be eliminated by virtue of the induction hypothesis.
3.122.12. Suppose 93 does not occur in both 0 and A simultaneously.
It must occur in one of them. We consider the case of 93 occurring in A, but
not in 0; the alternative case is completely analogous.
We transform the end of the derivation into:
B , A - + A
Z - I l  mix
r-+@,a B, A, C* + A*, fl
3-IA.
3 B, r, A, Z* --+ 0, A*, Il
The mix may be eliminated by virtue of the induction hypothesis.
3.2. Proof of the Hauptsatz for LJ-derivations.
In order to transform an LJ-derivation into an LJ-derivation without cuts,
we apply exactly the same procedure as for LK-derivations.
Since an LJ-derivation is a special case of an LK-derivation, it is clear
that the transformation can be carried out. We have only to convince
ourselves that with every transformation step an LJ-derivation becomes
another LJ-derivation, i.e., that the D-sequents of the transformed deriva-
tion do not contain more than one S-formula in the succedent, given that
this was the case before.
We therefore examine each step of the transformation from that point
of view.
3.21. Replacement of cuts by mixes. An LJ-cut runs:
r-+b D , A - + A
Y
r , A - + A
where A contains at most one S-formula. We transform this cut into:
r-+b b , d - , n m i x
r, A* -+ A
r , A - + A
This replacement gives us a new LJ-derivation.
possibly several interchanges and thinnings in the antecedent.

---

3.22. By relabelling free object variables (3.10) we trivially get another
LJ-derivation from a previous one.
3.23. The transformation proper (3.1 1 and 3.12).
We have to show for each of the cases 3.11 1 to 3.122.12 that the specified
transformations do not introduce any sequents with more than one S-
formula in the succedent.
3.231. Let us begin with the cases 3.11:
In the cases 3.111, 3.113.1, 3.113.31, 3.113.35 and 3.113.36, only such
formulae occur in each succedent of the sequent of a new derivation as had
already occurred in the succedent of the sequent of the original derivation.
Essentially the same applies in 3.113.33. The only difference is an addi-
tional replacement of free object variables, which does not, of course,
alter the number of succedent formulae of a sequent.
Cases 3.112, 3.113.2,3.113.32, and 3.113.34 were dealt with symmetrically
tocases3.111,3.113.1,3.113.31,and3.113.33,i.e.,inordertogetonecase
from another, we read the schemata from right to left instead of from left
to right (as well as changing logical symbols, a process which is here of no
consequence). Hence in the antecedent of one case we get precisely the
same as in the succedent of another. For the antecedents of cases 3.111,
3.113.1, 3.113.31 and 3.113.33, the same applies as for the succedents, viz.,
in every antecedent of a sequent of the new derivation only such formulae
occur as had already occurred in an antecedent of a sequent of the original
derivation.
This disposes of all dual cases: 3.112, 3.113.2, 3.113.32 and 3.113.34.
3.232. Now let us look at the cases, 3.12:
3.232.1. For the cases 3.121 it holds generally that Z* is empty, since in
l7 -+ Z, ,Z must contain only one formula, and that formula must be equal
to m.
It is now obvious that in every succedent of a sequent only such formulae
occur as had already occurred in the succedent of a sequent of the original
derivation.
3.232.2. In the cases 3.122 it is somewhat more difficult to see that from an
LJ-derivation we always get another LJ-derivation. We must direct our
attention, as was done in our earlier consideration of dual cases, to the
antecedents in the schemata 3.121.
3.232.21. The case which is dual to 3.121.1 is trivial, since in every antecedent
of a sequent of a new derivation (in case 3.121.1) only such formulae occur
as had already occurred in an antecedent of a sequent of the original derivation.
At this point we distinguish two further subcases:

---

0 1, APPLICATIONS OF THE Hauptsatz IN PROPOSITIONAL LOGIC
103
3.232.22. In the cases that are dual to 3.121.2, the mix in the end of the
derivation runs:
a + m
z-kn
a, z* + n
Y
where 17 contains at most one S-formula, and where D +
is the lower
sequent of an LJ-inference figure in which at least one upper sequent
contains 9Jl as a succedent formula.
If we now look at the inference figure schemata 1.21, 1.22, it becomes
easily apparent that such an inference figure can only be a thinning, con-
traction, or interchange in the antecedent, or a v-IA, a &-ZA, a +ZA,
a V-IA, and a 3-ZA. Let us disregard for the moment the v-IA and the
1-U. Then all the possibilities enumerated above fall within the case dual
to 3.121.22, where both Y and Z always remain empty. (r corresponds
to the 0 of the inference figure.) Thus we have the case which is dual to
3.121.221. Furthermore, r is equal to '%, i.e., r* is empty, and n contains
at most one formula. Hence in the new derivation there never in fact occurs
more than one formula in the succedent of a sequent.
The case of a v-IA is dual to 3.121.231. Again, r is equal to '557, I'*
is
empty, and 17 contains at most one formula; all is thus in order.
There now remains the case of a x-IA, i.e., 3.122.1. In an LJ- 3 4 4 ,
the 0 of the schema (1.22) is empty. Thus we have the case set out under
3.122.12. A* is also empty, and n contains at most one formula, which
means that here, too, we again obtain an LJ-derivation from an LJ-deriva-
tion.
SECTION IV. SOME APPLICATIONS OF THE HAUPTSATZ
