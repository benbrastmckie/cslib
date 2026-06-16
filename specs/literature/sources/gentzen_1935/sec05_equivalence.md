<!-- Source: Gentzen, G. (1935). Untersuchungen über das logische Schließen (Investigations into Logical Deduction). Section V: Equivalence of NJ, NK with LJ, LK. BibKey: Gentzen1935 -->

AND LJ, LK WITH A CALCULUS MODELLED ON THE
FORMALISM OF HILBERT
5 1. The concept of equivalence
1.1. We shall introduce the following concept of equivalence between
formulae and sequents (which is in harmony with what was said in 1.1.1
and 1.2.4, concerning the informal sense of the symbol A and of sequents:
Identical formulae are equivalent.
Identical sequents are equivalent.
Two formulae are equivalent if the replacement of every occurrence of the
A yields the other formula.
The sequents Z1,.
. . , aP + Bl,
. . . , Bv is equivalent to the following
If the 2l's and B's are not empty:
symbol A in one of them by the formula A &
formula:
(al & . . . & aP) 3 (Bv v . . . v B1);
(this version is more convenient for the equivalence proof than that with
Bl v . . . v Bv); if the a's are empty, but the %'s are not:
Bv v.. . v ,823,;
(al & . . . & ap) 3
( A  & 1
A);
if the 23's are empty, but the a's are not:
if the Ws and the 8's are empty:
A & T A .
The equivalence is transitive.

---

INVESTIGATIONS INTO LOQICAL DEDUCTION
1.2. (We could of course give a substantially wider definition of equivalence,
e.g., two formulae are usually called equivalent if one is derivable from the
other. Here we shall content ourselves with the particular definition given,
which is adequate for our proofs of equivalence.)
Two derivations will be called equivalent if the endformula (endsequent)
of one is equivalent to that of the other.
Two calculi will be called equivalent if every derivation in one calculus
can be transformed into an equivalent derivation in the other calculus.
In 0 2 of this section we shall present a calculus (LHJ for intuitionist,
LHK for classical predicate logic) modelled on Hilbert's formalism. In the
remaining paragraphs of this section we shall then demonstrate the equiv-
alence of the calculi LHJ, NJ, and L J  ($0 3-5) as well as the equivalence of
the calculi LHK, NK, and LK (0 6) in the sense just explained. We shall thus
successively prove the following:
Every LHJ-derivation can be transformed into an equivalent NJ-deriva-
tion (8 3); every NJ-derivation can lye transformed into an equivalent
LJ-derivation (0 4); and every LJ-derivation can be transformed into an
equivalent LHJ-derivation (0 5). This obviously proves the equivalence of all
three calculi. The three classical calculi are dealt with analogously in 0 6
(6.1-6.3).
6 2. A logistic calculus according to Hilbert2' and Glivenko28
We shall begin by explaining the intuitionist form of the calculus:
An LHJ-derivation consists of formulae arranged in tree form, where
the initial formulae are basic formulae.
The basic formulae and the inference figures are obtained from the
following schemata by the same rule of replacement as in 11.2.21, i.e.:
For %, '23, B, put any arbitrary formula; for VX & or 3~ '& put any arbitrary
formula with V or 3 for its terminal symbol, where x designates the associated
bound object variable; for g a  put that formula which results from
by
the replacement of every occurrence of the bound object variable
by the
free object variable a.
2.11. cu: 3 cu:
2.12.
2.13.
(% 3 (a
23)) =I (3 3 %)
2.14.
Schemata for basic formulae:
9i 3
(23 3 9i)
(a 3
('23 3 G)) 3 (23 3 ((ZI 3 G))

---

0 3, TRANSFORMATION OF AN LHJ-DERIVATION
117
2.15.
2.21.
2.22.
2.23.
2.31.
2.32.
2.33.
2.41.
2.42.
2.51.
2.52.
((21 3
23) 3 ((23 3 G) = (a = G))
(a&B) 3%
((21&23) 3 23
((21 =J 23) 3
(((21 3 G) 3 ((21 3 (8 & 6)))
%=,(%V%)
B = ((21vB)
(a 3 G) 3 ((23 3 G) = (((21v 23) = G))
(% = 23) = (((21 3 123) = 1
a)
(7
a) = ((21 3 B)
V.si?z
3a
3a = 3 z  3.s.
(Several of the schemata are dispensable, but independence does not
Schemata for inference figures:
concern us here.)
a
( 2 1 3 %
a33a
Ba 3 (21
B
(21 = V z %
( 3 E W  3%.
Restriction on variables: In the inference figures obtained from the last
two schemata, the object variable, designated by a in the schema, must not
occur in the lower formula (hence not in
and 3:~).
(The calculus LHJ is essentially equivalent to that of Heyting".)
By including the basic formula schema
v 7 (21, the calculus LHK
(This latter calculus is essentially equivalent to the calculus presented in
(classical predicate calculus) results.
Hilbert-Ackermann, p. 53.)
8 3. Transformation of an LHJ-derivation into an equivalent NJ-derivation
From an LHJ-derivation (V.2) we obtain an NJ-derivation (11.2) with
the same endformula by transforming the LHJ-derivation in the following
way: (In this transformation all D-formulae of this derivation will reappear
as D-formulae of the NJ-derivation, and they will not depend on any assump-
tion formula. Included further will be other D-formulae dependent on
assumption formulae.)
3.1. The LHJ-basic formulae are replaced by NJ-derivations according to
the following schemata:

---

(2.11)
(2.13)
(2.14)
(2.15)
1

1
(a =) (23 36))
=) (23 3 (a 3 6))
1
3

(2.12)
1
&-E
2.22, 2.31, 2.32, 2.51 and 2.52 are dealt with analogously to 2.21.
1
3

1
2

---

0 3, TRANSFORMATION OF AN LHJ-DERIVATION
119
1
4

1
3
3 - E  '
3 - E
2
a a = %
(2.33)
V-E 1
% V B
Q
Q
rr
1
3

1
2

3 - E
% a3123
3 - E
% %I23
(2.41)
23
1 B
A
~
1-11
1%
(a 3 123) = 7
a
(a = 23) = ((a 3 1
23) 3 1
a)
=-I,
3 - I 3
1
2

(2.42)
a l a
7 - E
A
3-11
(1
a) = (a =) 93)
B
a323
=-I,.
3.2. The LHJ-inferenceJigures are replaced by sections of an NJ-derivation
according to the following schemata:
remains as it is, since it has already the form of a 3-E.
%a323
23
1

---

The restriction on variables for V-I and 3-E is satisfied, as is easily seen,
by virtue of the restriction on variables existing for LHJ-inference figures.
This completes the transformation of an LHJ-derivation into an equiv-
alent NJ-derivation.
5 4. Transformation of an NJ-derivation into an equivalent LJ-derivation
4.1. We proceed as follows: First we replace every D-formula of the NJ-
derivation by the following sequent (cf. 111.1.1): In its succedent only the
formula itself occurs; in its antecedent occur the assumption formulae upon
which the sequent depended, and they occur in the same order from left
to right as they did in the NJ-derivation. (It is presumably clear what is
meant by the order from left to right of the initial formulae of a figure in
tree form.)
We then replace every occurrence of the symbol A by A & 1
A. (The
formula resulting from A in this way will be designated by A*.)
4.2. We thus already have a system of sequents in tree form. The antecedent
of the endsequent is empty (11.2.2); it is obviously equivalent to the end-
sequent of the NJ-derivation. The initial sequents a11 have the form %* --* %*
(11.2.2) and are thus already basic sequents of an LJ-derivation.
The figures formed from NJ-inferencefigures are transformed into sections
of an LJ-derivation according to the following schemata:
4.21. The inference figures v-I, V-I, and 3-1 have become LJ-inference
figures as a result of the substitution performed. (In the case of a V-I,
the LJ-restriction on variables is satisfied by virtue of the NJ-restriction on
variables.)
4.22. A &-I became:
r+8*
A + @ *
r , A + a * & B T '
This is transformed into:

---

5 4, TRANSFORMATION OF AN NJ-DERIVATION
121
r + a* possibly several inter-
r, A + a* changes and contractions r, A + B*
r, A + %* & B*
A + B* possibly several
thinnings
&-IS.
4.23. A =-I became:
rl,
%*, r2,.
. . ,%*, rp + B*
rl, r 2 , .
. . , rp + %* 3 B*
*
This we transform into:
rl
9 %*?
r2
9 * - * 9 a*, r~ + B* possibly several interchanges and
contractions, sometimes a thinning
a*, r,, r,, . . . , r, + B*
I"
- D - l A .
-
-

__ r1,r2,.
. . ,rp
-+ a* 3 B*
4.24. The same procedure applies to a l-I. Finally, we still have to consider
the figure
First we derive A &
A -+ in the calculus LJ as follows:
7 - I A
&-IA
A + A
i A , A +
A & i A , A +
A , A & - I A +
A & i  A , A & T A +
A & 7 A - +
interchange
contraction.
&-IA
By including this sequent, the figure in question is transformed as follows:
% * , r + A & 7 A
A & T A +  cut
1 - I S .
8*,
r +
r+7a*
A
5D
4.25. By substitution (4.1) the NJ-inference figure - became:
This is transformed into:

---

T - t A & T A
A & i A +  cut
r +
r + a*
thinning.
The derivation for A &
written above that sequent.
4.26. A V-E became:
A +, as presented in 4.24, should here still be
r + vx ~ * x
r+S*a
'
This is transformed into:
4.27. The same method is used for &-E.
4.28. A 2-E became:
r+%* A + % *  3 B *
r, A + B*
This is transformed into:
A,r+ B*
r , A + B *
possibly several interchanges.
4.29. A --E
became:
This is transformed into:
1 - I A
r + %*
A + T % *
,%*,r-t
- cut
A,r+
possibly several interchanges
thinning.
r, A -+
r, A -+ A & 7
A

---

5 5, TRANSFORMATION OF AN LJ DERIVATION
123
4.2.10. v-E. Both right-hand upper sequents are followed up, as in the case
of a 3-I and 7-1 (4.23) above, by interchanges, contractions, and thinnings
(wherever necessary) so that in each case the result is a sequent in whose
antecedent occurs a formula of the form %* or B* at the beginning (whereas
the original assumption formulae involved have been absorbed into the rest
of the antecedent). Then follows:
possibly several thinnings
B*, A
Q* possiblyseveralthinnings
23*, r, A -+ 0.
--t
* and interchanges
V-IA
* and interchanges
%*, r, A -, Q
E -, %* v 23*
%* v %*, r, A -, Q* cut.
4.2.11. A 3-E is treated quite similarly: First we move S*
a in the right-hand
upper sequent to the beginning of the antecedent (cf. 4.23); then follows:
E, r, A -+ Q*
b,r -, Q*
The LJ-restriction on variables for 3-IA is satisfied by virtue of the NJ-
This completes the transformation of an NJ-derivation into an equivalent
restriction on variables for 3-E.
LJ-derivation.
§ 5. Transformation of an LJ-derivation into an equivalent LHJ-derivation
This transformation is a little more difficult than the two previous ones.
We shall carry it out in a number of separate steps.
Preliminary remark: Contractions and interchanges in the succedent do
not occur in the calculus LJ, since they require the occurrence of at least
two S-formulae in the succedent.
5.1. We first introduce new basic sequents in place of the figures &-IA,
v-IS, V-IA, %IS, -,-IA, and I-IA; these are to be formed according to
the following schemata (rule of replacement as in 111.1.2 - the same rule
will always apply below; in addition to the letters 8,
23, By and 6 we shall
also, incidentally, use the letters, 6, $, and 3):
2351: M & B + %
2332: % & 2 3 + 2 3
2333: %+Mv23
2334: 23+Mv23
2355: VF 3~ -, %a
23G6: Sa -+ 3~ 3~
2357: 1
M, M -+
2358: M 3
23, % -+ 23.

---

Thus in the LJ-derivation to be considered, we transform the inference
A &-IA becomes :
figures concerned in the following way:
2331
a&%-+%
a,r+o cut.
imB,r+o
The other form of the &-IA is transformed correspondingly, so is every
v-IS and 3-1s are dealt with symmetrically.
A 7-IA becomes:
&-IA.
2337
+ interchange
cut
r + 8  aYl8+
r,-a+
lix,r+
possibly several interchanges.
(The 0 in the schema of - 1 4 4  (111.1.22) must be empty by virtue of the
LJ-restrictions on succedents; the same holds for the 5 I A . )
A z-ZA becomes:
B38
" +
interchange
8
8 , 8 3 b + B c u t
cut
rY8=%-+8
2 3 , A + A
r, 8 3 By
A + A
possibly several
8 3  23, r, A + A
interchanges.
5.2. We now write the formula A &
A in the succedent of all D-formulae
whose succedent is empty.
In doing so the basic sequents of the form 5B + 9, as well as 2331 to
2336 and 2338, also the figures &-IS, V-IS, and =-IS, remain unchanged.
The other basic sequents and inference figures are transformed into new
basic sequents and inference figures according to the following schemata:
2339: a, 7 a + @

---

0 5, TRANSFORMATION OF AN LJ-DERIVATION
125
(For 3f7 the reexists the following restriction on variables: The free object
variable designated by a must not occur in the lower sequent.)
5.3. The inference figure 3f4 is now replaceable by other figures as follows
(this is mainly due to our having kept general the form of the schema 93359):
B62
3f5
BS9
r - + a 1 A
A & ~ A - + ~ A
3f5
r - + T A
i A , A - + %
%Sl
r , A - + %  possibly several
A, r -+ B af5
3 f 5
T + A & l A
A & i A - + A
T + A
r,r+%
1-39
possibly several
and
In a similar way we replace the inference figure 3f8 (wherever it occurs
in the derivation), only this time we use a new inference figure according
to the following schema:
I - , % + A
r , % - + l A
3f9 :
r - + T A
We substitute as follows (in place of Sf8):
23351
m 2
3f5
% , ~ - + A & ~ A
A & ~ A - + ~ A
% , r - + i A
I-,%-+
A
r , % - + T A
3 f 5
~
+
~
s
!
i

Q , ~ - + A & ~ A
A & ~ A - + A
8 , r - A  possibly several
possibly several 3f3's
3j9.
5.4. Now we still introduce two new inferenceJigures schemata, viz.:

---

and its converse:
The two types of inference figures are introduced into the derivation in
order to enable us to replace a number of other inference figures by more
specialized ones (in 5.42 and 5.43).
5.41. To begin with, ='-IS inference figures are now replaceable by means
of 3 f l O :
A =-IS is transformed into:
- 1 -  -
-J
"-I----
"=. ,-.
5.42. The inference figures 3f1, 3f2, 3f3, 3f5, Sf6, and 3f7 are then trans-
formed in the following way:
As an example we take an 3f2, which is transformed into the followdg
figure (suppose r equals S1, . . . , 3,):
3f10
several
Sf13
several
Sf lo's
3fll's.
We proceed quite analogously with all other figures mentioned, i.e.,
using 8 f l O  and Sfll, we replace them by inference figures according to
these schemata:
(For 3f17 there exists a restriction on variables: The free object variable
designated by a must not occur in the lower sequent.)
5.43. In a similar way we also replace the inference figures 3f9, 3f13, and
3f14 by the following (using 8 f l O  and 3fll):

---

5 5, TRANSFORMATION OF AN LJ-DERIVATION
127
+ sb 3
(5D 3 0.)
3f19:
r - - + % = ~
r + % D I A
A + sb 3
(0: 3 0.)
fl + E 3 (sb D 0.)
*
8f18:
r j 7 %
j s b 3 G
8f20 :
The basic sequents 2338 and 2339 may be replaced in the same way by:
% 3
23 + % 3 23, this form falls under the schema sb + 3;
as well as
23310: 1
% + ill 3
@.
5.5. Now comes theJinal step:
Every D-sequent
%I , . . . , %@ + 23
is replaced by the formula
(If the Ws are empty, we mean 23. An empty succedent no longer occurs,
according to 5.2.)
All basic sequents (viz. sb + 9, 2331 to 2336, 23310) are thus transformed
into LHJ-basic sequents.
OF the inference figures, V-IS and 3f17 are also transformed into LHJ-
inference figures. (V-ZS, however, forms an exception if r is empty. In that
case we first derive (in the LHJ-calculus) (A 3
A )  3 Sa from Sa by means
of 2.12, and by then applying the LHJ-inference figure, we finally obtain
VF 3s once again by means of 2.11.)
The figures obtained from the remaining inference figures (which are
&-IS, Sflo, 11, 12, 15, 16, 18, 19, 20) by substitution, are turned into
sections of an LHJ-derivation in the following way:
& . . . &
3
23.
An &-IS has become (suppose first that r is not empty):
G 3 %  6 3 %
This is transformed into:
0.323
(0. 3 %) 3 (0. 3
(% & 23))
G 3(%&%)
If r is empty, we proceed as in the case of V-ZS.
The figures obtained from 8f12, 15, 16, and 19 by substitution are
dealt with quite analogously using basic formulae according to the schemata
2.12, 2.15, 2.33, and 2.13.

---

In a similar way 3f18 and 3f20 are dealt with by means of 2.41 and 2.14
and by the application of 2.15 and 2.14, 2.13.
The only figures now left are those having resulted from 8 f l O  and8f11.
Both are trivial for an empty T,
hence suppose that r is not empty. In that
case we transform these figures into sections of LHJ-derivations as follows:
(3flO): From (Q & %) 13 B we have to derive 0. 3 (a 3 23). Now 2.23
together with 2.11 yields: (Q 3 %) 3 (0: 3 (0. & a)). This together with
(0. & 8)
3 23 and 2.15, 2.14 yields (0. 3
%) 2 (0. 13 %), and from this
formula together with 2.12, 2.15 yields % 13 (0. 3 B), and by 2.14
0. 13 (a 3 '3) results.
(3fll): From B 13 (3 13 23) we derive (Q & a) 13 B in the LHJ-calculus
as follows: 2.21 and 2.22 yield (6 & a) 3 Q and (6 & %) 13 %; and from
this together with Q 3 (% 3 Ti), we obtain (0. & a) 13 23 (by using 2.15,
2.14, 2.15, 2.13).
This completes the transformation of the LJ-derivation into an LHJ-
derivation. Furthermore, the two derivations really are equivalent, since the
endsequent of the LJ-derivation was affected only by the transformations
5.2 and 5.5, and has thus obviously been transformed into a formula
equivalent with it (according to 1.1).
If the results of $0 3-5 are taken together, the equivalence of the three
calculi LHJ, NJ, and L J  is now fully proved.
4 6. The equivalence of the calculi LHR, NK, and LK
Now that the equivalence of the different intuitionist calculi has been
proved, it is fairly easy to deduce that of the classical calculi.
6.1. In order to transform an LHK-derivation into an equivalent NK-
derivation we proceed exactly as in 0 3. The additional basic formulae
according to the schema % v 1
% remain unchanged, and are thus at once
basic formulae of the NK-derivation.
6.2. In order to transform an NK-derivation into an equivalent LK-deriva-
tion we proceed initially as in 0 4. In this way the additional basic formulae
according to the schema
v
% are transformed into sequents of the
form -+ %* & 7 %*. These we then replace by their LK-derivations
(according to 111.1.4). The transformation of an NK-derivation into an
equivalent LK-derivation is thus complete.
6.3. Transformation of an LK-derivation into an LHK-derivation.
following respect:
We introduce an auxiliary calculus differing from the LK-calculus in the

---

0 6, THE EQUIVALENCE OF THE CALCULI LHK, NK AND LK
Inference figures may be formed according to the schemata 111.1.21,
111.1.22, but with the following restrictions: Contractions and interchanges
in the succedent are not permissible; in the remaining schemata no substitu-
tion may be performed on 0 and A; these places thus remain empty.
Furthermore, the following two schemata for inference figures are added
(rule of replacement as usual: 111.1.2):
and its converse:
(Thus, here 0 need not be empty.)
6.31. Transformation of an LK-derivation into a derivation of the auxiliary
calculus:
(The procedure is similar to that in 5.4.)
All inference figures, with the exception of contractions and interchanges
in the succedent, are transformed according to the following rule: The
upper sequents are followed by inference figures Sfl, until all formulae of
0 or A have been negated and brought into the antecedent (to the right of
r or A ) .  Then follows an inference figure of the same kind as the one just
transformed, which is now actually a permissible inference figure in the
auxiliary calculus. (The formulae that have been brought into the antecedent
are treated as part of r or d.) Then follow 3f2 inference figures, and 0
and A are thus brought back into the succedent. (In the case of the =-ZA
and the cut, we may first have to carry out interchanges in the antecedent,
but these are also permissible inference figures in the auxiliary calculus.)
Now we still have to consider contractions - or interchanges - in the
succedent. Here, as in the previous case. the whole succedent is negated and
brought forward into the antecedent. We then carry out interchanges, a
contraction, and further interchanges - or one interchange - in the antece-
dent, and then the negated formulae are brought back into the succedent
(bq means of the inference figures Sf2).
6.32. Transformation of a derivation of the auxiliary calculus into a deriva-
tion of the calculus L J  augmented by the inclusion of the basic sequent
schema -, v
a:
We begin by transforming all D-sequents as follows:
%I 3 . . . , afl
--+ '231 , . . . , '23" becomes

---

U1, . . . ,
+ '23" v . . . v Bl . If the succedent was empty, it remains empty.
Now all basic sequents or inference figures of the auxiliary calculus with
the exception of the figures Sfl and Sf2, have thus already become basic
sequents or inference figures of the calculus LJ. This is so since these
inference figures have resulted from the schemata 111.1.21 , 111.1.22 (with the
exception of the schemata for contraction and interchange in the succedent)
by 0 and A always having remained empty. At most one formula could
therefore occur in the succedent.
Hence we still have to transform the figures which have resulted from the
inference figures 3fl and 3f2 in the course of the above modification.
6.321. First Sfl: If 0 is empty, we replace the inference figure by a l-L4,
followed by interchanges in the antecedent. Suppose, therefore, that 0 is
not empty, where O* designates the formulae belonging to 0, in reverse
order and connected by v.
After the transformation of the succedents, the inference figure in that
case rum as follows:
r - + o * v 8
r, 8- o*
This is transformed into the following section of an LJ-derivation:
% + %
o* + o*
1%,8-+
%,7%+
8, 7 8 + o*
thinning
interchange
1
%, o* + o*
o*, 1 8
-+ o*
r, 8 -+ o*
o* V%, 7 8 + o* cut.
~ .-_I._-
r + o * v 8
1 - I A
interchange
thinning
V-IA
6.322. After the transformation of its succedents, an inference figure 3f2
runs as follows:
r, 4 x - +  o*
r + o * V &
where @* has the same meaning as in the previous case. If 0 is empty,
assume @* to be empty too, and let @* v 8 mean 8.
It is transformed into the following section of a derivation:

---

6, THE EQUIVALENCE OF THE CALCULI LHK, NK AND LK
131
* %possibly several thin- r,
% * @*possibly several
nings and interchanges
* interchanges
la,r-,o
v-IS
v-IS
V-IA
%,r-+%
%,r
-+ @ * v %
%, r -, o* v %
cut.
-,%v-l%
% V
%, r -, o*vt?i
r-,o*v%
It is easy to see that in the case of an empty 0 all is in order.
6.33. The LJ-derivation now obtained, together with the additional basic
sequents of the form + 8 v 1
%, may be transformed, as in 0 5, into an
LHJ-derivation with the inclusion of additional basic formulae of the form
% v 1
% (cf. 5.5), i.e., into an LHK-derivation. This completes the trans-
formation of the LK-derivation into an LHK-derivation. At the same time,
the endsequent has been transformed (in accordance with 6.32,5.2, and 5.5)
into an equivalent formula (according to 1.1).
By combining the results of 6.1, 6.2, and 6.3, we have now also proved
the equivalence of the three classical calculi of predicate logic: LHK, NK,
and LK.