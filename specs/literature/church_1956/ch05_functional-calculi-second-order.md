<!-- Source: Church, A. (1956). Introduction to Mathematical Logic. Chapter V: Functional Calculi of Second Order (pages 308+). BibKey: Church1956 -->

The functional calculus of second order or, as we shall also say (in order 
to distinguish from the ramified functional calculi of second order which 
are described in § 58 below), the simple functional calculus of second order 
has, in addition to notations of the functional calculus of first order, 
quantifiers with propositional or functional variables as operator variables. 
As in the case of the functional calculus of first order, there are various 
different systems, (simple) functional calculi of second order, which we 
shall treat simultaneously. 
The particular formulation selected for 
treatment in this chapter we call F\ (the subscript referring to the par­
ticular formulation of the propositional calculus which is contained). 
Or, where necessary to distinguish the different functional calculi of second 
order, F£p is the formulation of the pure functional calculus of second order 
treated in this chapter, F*'1 the singulary functional calculus of second order, 
F*,a the binary functional calculus of second order, and so on.
50- The primitive basis of F^. The primitive symbols of Fg are identical 
with those of F1 or ¥ \ (see §30). The pure functional calculus of second order 
F ?  includes among its primitive symbols all the individual, propositional, 
and functional variables, but no (individual or functional) constants. The 
n-ary functional calculus of second order F®’” includes all the individual and 
propositional variables, all the functional variables which are no more than 
»-ary, and no constants. An applied functional calculus of second order in­
cludes at least one constant, as well as all the individual variables and at 
least one kind of functional variables.
In order that the system be considered a functional calculus of second 
order at all, of course functional variables of one kind at least should be 
included among the primitive symbols. We shall confine our treatment to 
the case that both propositional variables and singulary functional variables 
(at least) are present, and in particular we use variables of both these kinds in 
the axioms. This is, however, not an essential point, and modification of the 
treatment to fit other cases may be left to the reader.
The formation rules of F* are the same as those of F1, with removal of the 
restriction to individual variables in the fifth rule:

---


296
FUNCTIONAL CALCULI OF SECOND ORDER [Chap. V
50i. 
A propositional variable standing alone is a wff.
50ii. 
If f is an «-ary functional variable or an «-ary functional constant, 
and if ax, aa, . .
an are individual variables or individual constants 
or both (not necessarily all different), then f(aJ( aa, . . 
an) is a wff. 
50iii. 
If T is wf, then ~T is wf.
50iv. 
If T and A are wf, then [T r> A] is wf.
50v. 
If r  is wf and a is any variable, then (Va)T is wf.
As in the case of F1, an effective test of well-formedness follows, as well 
as uniqueness of the analysis of a wff into one of the forms ~A, [A 3  B], 
(Va)A, and analogues of the metatheorems **313—**316. The terms 
antecedent, consequent, principal implication sign, converse, elementary part 
are introduced with the same meaning as for F1,
The distinction between bound variables and free variables is made in the 
same way as in §30. But in the functional calculus of second order, not only 
individual variables but also propositional and functional variables may have 
bound occurrences.
A wff will be called an n-ary form if it has exactly n different free variables, 
and it will be called a constant, or a closed wff, if it has no free variables. 
As in F1, all forms are propositional forms, and all closed wffs are sentences.
The same methods of abbreviating wffs are used as for F1, including the 
same conventions for omission of brackets, and the definition schemata 
D3-17. In D 13-17 it is to be understood that the variables a, alP a2, . . 
a* 
may be of any kinds, propositional or functional as well as individual. 
Additional definitions and definition schemata may be introduced from 
time to time as required. And in particular we introduce at once the two 
following definitions:
D20. 
/ -> (s)s 
D21. 
t -* (3s)s
The rules of inference, axiom schemata, and axioms of F\ are the follow­
ing:
*500. 
From A id B and A to infer B. 
(Rule of modus ponens.)
*501. 
From A, if a is any variable, to infer (a)A.
(Rule of generalization.)
*502. 
From A, if a is an individual variable which is not free in N and b is 
an individual variable which does not occur in N, if B results from 
A by substituting S£N; for a particular occurrence of N in A, to in­
fer B. 
(Rule of alphabetic change of bound individual variable.)

---


§51]
PROPOSITIONAL CALCULUS AND QUANTIFIERS 
297
*503. 
From A, if a is an individual variable, if b is an individual variable
or an individual constant, if no free occurrence of a in A is in a wf 
part of A of the form (b)C, to infer $jjA|.600
(Rule of substitution for individual variables.)
f505. 
pZD *q ZD p 
f506.
f507. 
~pZD ~qZD *qD> p 
"{*508. 
p z d x F(x) z d  n P =3 (x)F(x)
*508o. 
A D p B D  . A d  (p)B, where p is any propositional variable
which is not a free variable of A.
*508n. 
A d , B d i A d  (f)B, where f is an tt-ary functional variable which
is not a free variable of A. 
f509. 
(x)F(x) z d  F(y)
*5090. 
(p)A ^S& A [, where p is any propositional variable.600
*509n. 
(f)A z d  S^*!***1—*** A[, where f is an «-ary functional variable
and x1( xa, . . x n are distinct individual variables.500
As in the case of FIp (or Fjp), the principal interpretation of Fjp depends on a 
domain of individuals, which must be non-empty. Once the domain of individ­
uals is chosen, the principal interpretation is given by the same semantical 
rules a-f as in §30, with the single change that in rule f the restriction is removed 
that the variable a must be an individual variable. I.e., rule f is replaced by the 
following:
f*. 
Let a be any variable and let A be any wff. For a given system of values 
of the free variables of (Va)A, the value of (Va)A is t if the value of A is t for 
every value of a; and the value of (Va)A is f if the value of A is f for at least one 
value of a.
51.
Propositional calculus and laws of quantifiers. Deduction
theorem. By *509 (with *501 and *500) the rule of substitution for prop­
ositional and functional variables follows as a derived rule of Fa:
•51Q0. 
If p is a propositional variable, if b A, then
h S PBA|.
*510n. 
If f is an «-ary functional variable and xv x2, . . 
x n are distinct
individual variables, if b A, then
££*«-**....*j a i .
Now by *502, *503, and *510 we may obtain from +505-1508, f509 all 
of the axiom schemata (*302-*306) of F1 as theorem schemata of F2. Since
“ •The syntactical notations 
and "5" have the meanings which are explained in 
H30, 35.

---


298
FUNCTIONAL CALCULI OF SECOND ORDER [Chap. V
the two rules of inference (i.e., *300 and *301) of F1 are included in *600 
and *501, it follows that every theorem of Fxis a theorem of Fj, with the un­
derstanding that we take calculi F1 and Fj that have the same list of primi­
tive symbols. Analogously to the use of the term in §31 let us understandby 
a substitution instance of a wff A of F1 any wff B of the logistic system under 
consideration (in this chapter, the system Fj) such that B is obtained from 
A by a finite succession of the substitution steps of *503, *6I00, and *510n. 
Then follows:
*611. 
Every substitution instance of a theorem of F1 is a theorem of Fj,
The role of *511 as a derived rule of ¥ \ is similar to that of *311 as a 
derived rule of F1. In using *511 in this way, we may refer to it by the 
phrase "by F1," or "by P" (in case propositional calculus only is involved); 
or we may simply refer to one of the theorem schemata of F1 by number, 
treating it as a theorem schema of Fj.
It is also possible to establish, as theorem schemata of Fj, analogues of 
the theorem schemata of §33 in which a and b are allowed to be variables of 
arbitrary kind, instead of merely individual variables. (In the analogues 
of *330 and *339, but not in that of *336, a and b must be variables which 
are of the same kind.) The proofs follow closely those given in §33 and are 
left to the reader.
The following analogue of *340 may also be established as a theorem 
schema of Fj (the proof follows closely that in §34, using in case 3 the 
analogue of *334 in place of *334 itself):
*512. 
If B results from A by substitution of N for M at zero or more 
places (not necessarily at all occurrences of M in A), and if 
the variables at, a2, .. 
an include at least those free variables 
of M and N which occur also as bound variables of A, then 
hM== 
_ N = > . A = B .
■i *i—*i*
Hence, as in §34, we obtain the rule of substitutivity of equivalence as a 
derived rule:
*513. 
If B results from A by substitution of N for M at zero or more places 
(not necessarily at all occurrences of M in A), if b M =  N and 
1- A, then b B.
The following theorem schema is also a consequence of *512:
*614. 
b Sf A| rs . S£A| zd (p)A, where pis a propositional variable which is 
not a bound variable of A.

---


§51] 
PROPOSITIONAL CALCULUS AND QUANTIFIERS 
299
Proof. By *5090, h (s)~s 
~ . q ^  q.
Hence by P, h ~{s)~s.
I.e. (cf. D21), h t.
Also, by *5090, |- / D p ,
By *512, h p = * = >  . A== Sf A|.
And, by *512, h p == / :=> - A =  S* A|.
Hence (using the four preceding lines) we have by P that
h Sf A| => .SJAj => A.
Hence by *501, h (p) . Sf A| 
. S*A| 
A.
Then use *5080 and P.
The rule of alphabetic change of bound propositional and functional vari­
ables may now be proved in exact analogy to the proof of *350 in §35, by 
using the analogue of *339 and using *513 in place of *342:
*515. 
If a is a propositional or functional variable which is not free in N, 
and b is a variable of the same kind as a not occurring in N, if B 
results from A by substituting S£N| for a particular occurrence of N 
in A, and if h A, then h B.
The definition of proof from hypotheses for Fa is closely analogous to that 
given in §36 for F1. The changes are that the axioms of F1 are replaced by 
those of F*, and *300 is replaced by *500, *301 by *501, *350 by *502 and 
*515, *351 by *503, and *352 by *510. Then the deduction theorem may be 
proved in the same way as in §36:
*510. 
If Av Aa, .. 
An h B, then Av Aa, . . 
An_t f- An r> B.
Also we may prove an analogue of *362:
*517. 
If every wff which occurs at least once in the list Av Aa, . . ., A„ 
also occurs at least once in the list C1; C8, . . 
Cr and if Av Aa, . . 
A n I- B, then C1( Ca.........Cr h B.
By first proving analogues of the theorem schemata *364 and *365, we 
pay establish the following derived rules facilitating the use of the existen­
tial quantifier in connection with the deduction theorem:
•518. 
If Av Aa, .... A J B , and a is any variable which does not occur as 
a free variable in Alt A2, . . 
A„_rj B, then A*, A2, .. 
An_r, (3a) . 
An-r+jAn^+a. . . An h B. (r — 1, 2, . . ., «.)
*519. 
If A lt Aaj..., An hB , and a is any variable which does not occur as 
a free variable in A1( Aa, . .
An_r, then Av Aa, ,. 
An_r, (3a) ■ 
^ n -r+ l^ n -r+ 2  • ■ • A„ h (3 a )B . (r =  1, 2, . . 
».)

---


300
FUNCTIONAL CALCULI OF SECOND ORDER [Chap, V
The discussion of duality for Fg follows closely that in §37 and may be 
left to the reader. The definition of the dual is word for word the same,5*1 
as well as the statement of the three principles of duality which correspond 
to *372~*374 and which may be shown to hold also for Fj.
Finally, analogues of the theorem schemata of §§3"-38 may be proved in 
which a and b are allowed to be variables of arbitrary kind; and hence the 
reduction to prenex normal form (§39) may also be extended to Fj.
It should be noticed that all the derived rules of this section including 
*510 and *515, in contrast with the remark of footnote 340 about *352, 
have been established in such a way as to show that they will continue to 
hold for a system obtained from Fg by the addition of any further axioms.
52. Equality,
In  §48 we saw  how  the functional calculus of first order can be augm ented by 
adding a  functional constant I  to d enote th e relation of equality, or identity, 
betw een individuals, together w ith appropriate axiom s containing I .  We could 
of course do th e sam e thing in connection w ith the functional calculus of second 
order, so obtaining a  functional calculus of second order w ith  equality. B ut this 
is unnecesssary because it is in fact possible to introduce th e  relation of equality 
by definition in FJ. I.e., it is possible to find a  wff of F j w hich has the in d iv id u i 
variables a and b as its only free variables and w hich has th e  value t or f (in any 
principal in terp retatio n  of FJ) according as a and b do or do no t have the same 
value; one such wff of FJ is the definiens in D22 below, and the notation =s 
m ay thus be introduced by the abbreviative definition D 22.101
In the functional calculi of fo u rth  an d  higher orders we are able, by an exactly
M1In addition to D3-11 and D14, abbreviation by D20-23 may be allowed in an 
expression to be dualized. In this case, / and t are to be interchanged in dualizing, and 
also 
and 
4 #.
M*This definition is due to Leibniz in the form, "Eadem sunt quorum unum potest 
substitui alteri salva veritate." See Erdmann's God. Guil. Leibnitii Opera Philosophica,
vol. 1 (1840), p. 94, and Gerhardt's Die Pkilosophiscken Schriften von Gottfried Wilhelm 
Leibniz, vol. 7 (1890), pp. 228, 236 (also in English translation in the appendix of 
Lewis’s A Survey of Symbolic Logic). In this form there is a certain confusion of use and 
mention: things are identical if the name of one can be substituted for that of the other 
without loss of truth. Nevertheless the important idea of the definition is to be credited 
to Leibniz.
Frege adopts Leibniz's definition unchanged in Die Grundlagen der Arithmetih (1884), 
In Frege’s Grundgesetze der Arithmetih, vol. 1 (1893), the confusion of use and mention 
is corrected, but the principle appears in the form of an axiom rather than a definition: 
<p{x 
^  
F(y)]). The first statement of the principle in the form of a
definition of identity and without the confusion of use and mention Beeras to have been 
by C. S. Peirce in 1885 {American Journal of Mathematics, vol. 7, see page 199). In 
Russell's The Principles of Mathematics (1903) the definition appears in the form: 
“x is identical with y if y belongs to every class to which x belongs, in other words, 
if *x is a u‘ implies *y is a «' for all values of 
In Principia Mathematica, vol. I, 
(1910). we find the notation =* introduced by an abbreviative definition which is 
substantially the same as our D2 2 .

---


[82]
EQUALITY
301
analogous definition, to introduce the relation of equality also between things 
other than individuals, allowing a and b to be, e.g., propositional or functional 
variables (of the same type).
We add now the two following definition schemata, in which a is an in­
dividual variable or individual constant and b is an individual variable or 
individual constant, and then we go on to a number of theorems and derived 
rules in the statement of which we make use of the definitions:
D22, 
[a =  b] -*F (a) =>*• F(b)
D23. 
[a 4= b] ^  (3F) . F(a) 
F(b)
f520. x =  x 
(Reflexive law of equality.)
Proof. By P, b F(x) zd  F(x).
Generalize upon F (*501).
t521. x =  y zd m y =  z  
(Commutative law of equality.)
Proof, By *5091( h a; =  y => 5™F ( x )  => F(y)\.
Hence by modus fionens (*500), x — y h x  =  x i D . y ~ x .
Hence by f520 and modus fionens, x =  y h y =  x.
Then use the deduction theorem.
f522. 
z =  y z D * y  =  zzDmX^=z 
(’Transitive law of equality.)
Proof. By J521, x =  y h y =  x.
Hence by *5091( x =  y b  $^ F ( y )  => F(x)\.
Then use the deduction theorem.
fS23. 
x — y ^ * y  =  x 
(Complete commutative law of equality.)
Proof. By f521, *503, and P.
\SH. 
x =  y zd  * F(x) ~  F(y)
Proof. By *509lf x =  y b  F(x) id F(y).
By f521 and *509^ x =  y I- F(y) zd  F(x).
Then use P and the deduction theorem.
|525. 
x ^ y  =  ~ Mx =  y
Proof. By f523 and P, I- ~(F)[F(y) zd  F(a?)] =  -  . x — y.
By P, b F(y) zd  F(x) == -  . F(x) 4: F(y).
Then use *513.
f826. 
F(x) => ,~F(y)=> x *  y
Proof. By *509^ b x 
y ZD * F(x)^> F(y).
Hence by P, I- F(ar) id  . ~F(y) zd  ~  • x —  y.
Then use t525 and P.

---


302
FUNCTIONAL CALCULI OF SECOND ORDER [Chap. V
*527 
If a is an individual variable or an individual constant, if b is an 
individual variable or an individual constant, if B results from A 
by substitution of b for zero or more free occurrences of a, no one of 
which is within a wf part of A of the form (b)C—and not necessarily 
at all free occurrences of a in A—then |-a  =  b D , A D B
Proof. Let x be an individual variable which does not occur in A. Take 
all the occurrences of a in A at which b is substituted in obtaining B, and 
for every such occurrence of a substitute x. And let X be the wff which re­
sults from A by this substitution.
By *509^
ba =  b=> .§ x (XJF (a)=j F(b)|.
I.e., l-a =  b D  , A d  B.
From this of course we have as corollaries, by modus fionens:
*528. 
If a is an individual variable or an individual constant, if b is an 
individual variable or an individual constant, if B results from A 
by substitution of b for zero or more free occurrences of a, no one of 
which is within a wf part of A of the form (b)C—and not necessarily 
at all free occurrences of a in A—then a =  b I- A id B.
*529. 
If a is an individual variable or an individual constant, if b is an 
individual variable or an individual constant, if B results from Aby 
substitution of b for zero or more free occurrences of a, no one of 
which is within a wf part of A of the form (b)C—and not necessarily 
at all free occurrences of a in A—then a =  b, A I- B.
(Rule of subsiitutivity of equality
EXERCISES 52
5 * .° . Prove the following theorems of Fj}:
(1)
H
II
Hi
*
ii
hi■
H
II
(2)
b,
III
a
III
H
H
(3)
F(x) =s (3y) . F{y) .x  =  y
(4)
F(x) =>x x *  y =  ~F(y)
(5)
F{xv xt) =>F [F(ylt y2) => F{zv z2)] =
[*i =  
L^z =  *2] v [y, =  *,] [y2 =  i j

---


303
m
E X E R C I S E S  52
5 2 .1 . A formulation of the functional calculus of second order is to have 
the same primitive symbols as F2 with the omission of **, the notation ~A  
being introduced by definition in the way suggested in §28. Show how the 
fcules and axioms of F2 are to be modified, and in an appropriate sense 
establish the equivalence of the resulting system to F2.
52.2. A formulation of the functional calculus of second order is to have 
the same primitive symbols as F2 with omission of ~ and of all propositional 
variables. Show how notation ~A  is to be defined and how the rules and 
axioms of F2 are to be modified, and in an appropriate sense establish the 
equivalence of the resulting system to F2. Then generalize this to the case 
that not only ~  and the propositional variables are omitted but also all 
functional variables that are less than n-ary, the n-ary functional variables 
being retained.
5*-3- Extend **434 to F2P. Hence using the result of 48.5. show that every 
wff of Fgp which is a theorem of F2p is also a theorem of F2P.
5 M -  Solve the decision problem for the singulary functional calculus of 
Second order F2,1, by adding to the reduction steps (a)-(g) of exercise 39.6 
and the reduction steps {cc)~[rj) of exercise 48.14, in the first place analogues 
of (a)-(g) in which a is a singulary functional variable instead of an individ­
ual variable, and secondly the following reduction steps (in which p is any 
propositional variable, and f is any singulary functional variable, and 
a, ax, a2, . . 
am, 
b2, . . 
b n, c1( c2, . . 
c* are distinct individual vari­
ables): (A) to replace a wf part (p)E by the conjunction S£E|S*E|; (B) to 
replace a wf part 
.f(a 2) 3  . .  ,. f(am) 3  ~f(a)] by /; (C) to replace
a wf part (f)[~f(ax) 3  . ~f(a2) 3  . . . .  ^f(am) 3  f(a)] by/; (D) to replace a 
wfpart {f)[~f(aj)3 .~ f(a 2) 3  . . .  .~f(am) 3  . f(b,) 3  -f(b2) 3  «. . .  f(b„) 3  
f(a)] by bj *  ax 3  . b2 *  ax 3  . . . .  bn 4= ax 3  . bjL *  a23  . b2 4= a23  . . . .
bn 4= a23  ..............b1 4 a m3 . b 2 4 a m3 - . . . b n 4 a m= ) i b1 4 a 3 i
bg +  a 3  . ... btt =  a; (E) to replace a wf part (f)[E, 3  . E2 3  ■ . . . 
E „ 3  (a)D] by (a)(f)[E j3 . E2 3  «. . . En 3  D] if a is not a free variable of 
Ex, Ea, . . En; (F) to replace a wf part (f)[Ex 3  . E2 3  . .  . . En 3  ~(a)D] 
by (f)[Ej 3  . E' 3  «. . . E'n 3  ~(a)D'], where E^ is
(/ =  1, 2, . . ., n), and P' is
s;s.D
£f(a)
provided that E1( E2( . . 
En, D contain no bound propositional or func­
tional variables other than the bound functional variable F in wf parts of 
the form b =  c or b 4= cf and D contains no bound individual variables; (G)

---


304
FUNCTIONAL CALCULI OF SECOND ORDER [Chap.
to replace a wf part (f)[Ex 3  . E23  ....  En3  ~(a)(c1)(c2) ... (c<) .a  4= cx3  
a 4= c2 3 . . . .  a 4= c, 3  . cx 4= c2 3  ■ cx + c3 35 . . .  . c,_x 4= c< 3  , ~CX 3  
~C2 3  . .  . . ~C, 3  A], where G* is
s; ai
[j = 1 , 2 , . . . ,  »), by 
(cx) (c„) . .. (c<) (f) [E, =5 . E , 
Bn => -.(a)l
a 4= cx 3  . a 4s c8 3  . . . .  a 4= ct. 3  A], provided that Ex, E2, . , En, A da 
not contain cx, c2, . . c, as free variables, and contain no bound proposi­
tional or functional variables other than the bound functional variable F in 
wf parts of the form b =  c or b 4= c, and A contains no bound individual 
variables. (In all of these reduction steps of course w o r n  may as a special 
case be 0.)
S ^ S - With the aid of the foregoing results discuss the completeness, in 
various senses, (1) of the singulary functional calculus of second order Fj*1, 
and (2) of the logistic system obtained from F^'1 by adding the following 
infinite list of axioms: 
(3a?j) (3a;8) . xx 4= z 2, 
( 3 ^ )  (3®8) (3 » 8) . xx 4=
4= #3 ■ ^2 4= £31 (3a?x) (3#2) (^^3) (3a?4) • x l 4= ^2 ■ ^1 ^ *^3 - 
^4 a ^2 ^ %%»
4= 
■ ^3 41 ^41 ■ ■ ■*
5 * .6 . The elimination problem of the functional calculus of second order 
is the problem to find an effective procedure by which from a given wff K 
of the functional calculus of second order there is obtained a wff B of the 
functional calculus of first order with equality, such that A =  B is a theorem 
of the functional calculus of second order.803 We shall here require also an 
effective procedure by which to find a proof of A =  B. The wff B is then 
called the resultant of A.
(1) Solve the elimination problem of the singulary functional calculus of 
second order Fj’1 by means of the reduction steps (a)-(g), (a)-(rj), (A)-(G). 
of 39.6, 48.14, and 52.4.504
(2) Apply the elimination procedure found in (1) to get the resultant of 
the following wff A:806
(3 F ) . F(x) =>x G1(x) , G2(x) =>x F(x) . (3x)[F(x)H(x)] =>. H[x) =>x F(x) 
Show that the resultant can be simplified to:
G2(x) =>x G1(x) . (3x)[G,(x)ff(x)] z i . H ( x )  =>x G ,(*)
5 2 ,7 . (I) Solve the elimination problem for the special case of wffs of 
F8P of the form
*°*The elim ination problem goes back to Schrader. See an account of the m atter b y  
Ackermann m a paper in the Mathematiscke Annalen, vol. 110 (1934), pp. 390-413.
4MThis solution is due to Skolem and Behmann in their papers of 1919 and 1922, 
referred to in §49. There is also a sketch of a solution in Lbwenheim's paper of 1915.
M*This exam ple is taken from A ckerm ann's paper, cited in footnote 603.

---


EXERCISES 52
305
m
(3f) . C . f ( a , b ) = > abD
where f is a binary functional variable and a and b are distinct individual 
variables, C and D contain no bound propositional or functional variables, 
t) does not contain f, and the matrix M  of the prenex normal form of G has 
the property that506
I- M  
S |(a'b) M |.
Show that in this case a resultant is
where C' and D' differ from C and D by (at most) certain alphabetic changes 
of bound variables.507 Hence in particular find resultants of the following 
wffs of F^:
(2) 
(3 F )  . (x)(y)[F(x, y) ■=> G{x, y)]{x)(3y)[H(x, y) => F(x, y)}
(3) 
(3F){x){y) . F{x, y) =3 G(a;, y) .H^x, y) ■=> F( x, x).
H 2(x, y) ■=> F{x, x)F{y, y)
5 3 .8 . 
Similarly solve the elimination problem for the special case of 
wffs of F j1 of the form
( 3 f ) . C . D ^ a b f(a, b)
where f  is a binary functional variable and a  and b  are distinct individual 
variables, C  and D contain no bound propositional or functional variables, 
D does not contain f, and the matrix M  of the prenex normal form of C  has 
the property that508
h M id  
M[.
•••In other words, M  can be reduced to a disjunctive normal form (in the sense of 
footnote 299) in which f nowhere appears with a negation sign before it.
••’The solution of this special case of the elimination problem, as well as of the special 
cases of 52.8-52.10 and the particular examples 52.7(2) and 52.7(3), are due to Acker- 
mann in his paper cited in footnote 503.
Ackermann’s paper contains also a proof of the unsolvability of the general elimina­
tion problem of the functional calculus of second order, in the sense that for some wffs 
there is no possible resultant; and a generalization of the elimination problem is treated 
in which the resultant of a wff of the functional calculus of second order is to be a class 
of wffs of the functional calculus of first order.
A note by Ackermann in the Malhematiscke Annalen, vol. I ll (1935), pp. 81-63, 
contains solutions of a few further special cases of the elimination problem— not quite 
for the functional calculus of second order, but for a system obtained from the func­
tional calculus of second order by adding as axioms, summarized in an axiom schema, 
certain special cases of an axiom of choice which are expressible in the notation of the 
functional calculus of second order (see §56 and footnote 555).
•••I.e., M  has a disjunctive normal form in which f nowhere appears without a ne­
gation sign before it. Or alternatively we might define the parity (oddness or evenness)

---


306
FUNCTIONAL CALCULI OF SECOND ORDER [Chap. V
52-9* Generalize the results of 52.7(1) and 52.8,(1) by replacing f by an 
n-ary functional variable, and (2) by replacing f(a, b) by f ^ , a2, ..., a„) 
s  E, where E is quantifier-free and does not contain f.
Parallel to the foregoing series of solutions of the elimination 
problem for wffs beginning with an existential quantifier (3f), find a series 
of solutions of the elimination problem for wffs beginning with a universal 
quantifier (f) (by considering the negations of the latter wffs).
5 2 .II*  Following Behmann, show that the decision problem of the ex­
tended propositional calculus may, instead of the method described in §28, 
be solved by a reduction process like that of exercise 39.6, i.e., by a reversal 
of the process of reduction to prenex normal form.
5 2 .1 2 . Apply the decision procedure found in the foregoing exercise to 
the four examples of exercise 28.0.
5 2 .1 3 . How may the decision procedure of exercise 52.4 be modified in 
the light of exercise 52.11?
53. Consistency of F2. As already suggested in §49, it is possible to
prove the consistency of F2 by a very elementary syntactical argument, 
closely similar to that used in §32 to prove the consistency of F1.
For this purpose let us take a formulation of the extended propositional 
calculus in which the primitive connectives and operator are implication, 
negation, and the universal quantifier, and let us modify as follows the de­
cision procedure described in §28. Take t and /  not as abbreviations of wffs 
of F2 or of the extended propositional calculus but as primitive constants 
of a formulation of the propositional calculus. Given a wff A of the extended 
propositional calculus, replace a wff part (b)B in it by the conjunction
S?B|S?B|,
and iterate this until all occurrences of the universal quantifier have been 
removed. If the quantifier-free formula A$ which is thus obtained is a 
tautology (of the appropriate formulation of the propositional calculus), we 
shall say that A is valid.
Thus we have an effective test for the validity of any wff of the extended 
propositional calculus.
From any wff of F2 we obtain an associated formula of the extended prop-
of each occurrence of an elementary part in 'M  as follows: when an elementary part 
stands alone, this is an even occurrence of the elementary part; in <*K the parity of 
each occurrence of an elementary part is reversed as compared to K; in K 3  L the 
parity is reversed for each occurrence of an elementary part in K but remains the same 
in L. Then the requirement here is th at f shall appear only at odd places in M ; and in
52.7(1) the requirement is th at f shall appear only a t even places.

---


HENKIN COMPLETENESS THEOREM
307
§64]
tstiional calculus (abbreviated "afep’') as follows. First we delete all those 
occurrences of the universal quantifer in which the operator variable is an 
individual variable. Then, if flt f2, . . .,fm are the distinct functional vari­
ables and functional constants that appear, we select m distinct propositional 
variables pl, pa, . , 
pm not previously occurring, and we replace every wf 
part 
a2, . . ., an<) by pt, and we replace every universal quantifier 
(Vf<) by (Vpi) (i — 1 ,2 ........ m).
We need not (for our present purpose) distinguish among the different 
afeps of a given wff of ¥\, since they differ among themselves only by alpha­
betic changes of bound and free variables.
Now every axiom of F2 has a valid afep, and the rules of inference pre­
serve the property of having a valid afep, as we leave it to the reader to 
verify in detail. Hence follows:
•*630. 
Every theorem of F2 has a valid afep.
Since any afep of ~C is the negation of an afep of C, it follows that not 
both ~G and G can have a valid afep, hence by **530 that not both ~C and 
Q can be theorems of F}. Thus we have:
**631. 
F* is consistent with respect to the transformation of C into ~C. 
*•532. 
F* is absolutely consistent.
**633. 
F{ is consistent in the sense of Post.
Similar syntactical consistency proofs are possible also for the functional 
calculi of higher order, employing, instead of the afep, an associated formula 
of protothetic or of higher protothetic.509
54. Henkin’s completeness theorem.510
The principal interpretation of F*p for a given non-empty domain 3 of individ­
uals is given by rules a-e, f* of‘§50. We now introduce also what we call the 
interpretation of Fjp for a given domain 3  of individuals and given domains 
(classes) gfl( ??,, g»* . . . of propositional functions of individuals, where all 
members of 
must be singulary propositional functions whose range is the
•"See §49 and footnote 482. For the singulary functional calculus of order aj the 
p ro o f is carried out in especial detail by Gentzen in the Malhematische Zeitschrift, vol. 41 
(1930), pp. 357-366, though in a slightly different form from that indicated here.
luThe method which is used in this section to prove a weak completeness theorem for 
th e functional calculus o f second order is due to Leon Henkin (in his dissertation, 
Princeton University, 1947). It is essentially the same as the method used in §45 
(also due to Henkin, cf. footnote 465) to prove Gddel's completeness theorem for the 
functional calculus of first order. And it may be extended to functional calculi of higher 
o rder, though for systems containing a suitable form of the axiom of choice the modified 
m e th o d  which is used by Henkin in a paper in The Journal of Symbolic Logic, vol. 15 
(1950), pp. 81-91, may be preferable.

---


308
FUNCTIONAL CALCULI OF SECOND ORDER [Chap. V
individuals, all members of 
must be binary propositional functions whoS6 
range is the ordered pairs of individuals, and so on. Namely, these new inter­
pretations of F*p are given by the same rules which give the principal inter­
pretations, except that rules bt, b2, b3, . . . are replaced by the following: 
bx5 i- 
The singulary functional variables are variables having 
as their range, 
bgi. 
The binary functional variables are variables having 
as their range.
bg„. The n-ary functional variables are variables having 
as their ranges
Among these interpretations of Fjp it is clear that not all are sound. But tho«s 
among them which are sound, and are not principal interpretations, we call 
secondary interpretations of F*p.
We must leave open temporarily the question of existence of such secondary 
interpretations. But an affirmative answer to this question will follow front 
results obtained below. In fact it will follow that there exist secondary inter­
pretations of FJP in which all of the domains Q, 
g,, ga, . . . are enumerably 
infinite.
A n a lo g o u sly  to w h at w as done in §43, the sem a n tica l rules, ju st described 
in sm all ty p e , m a y  be resta ted  an d  reinterp reted in  su ch  a w ay as to give 
them  a p u rely sy n ta ctica l ch aracter. N am ely, th e w ords "range” and 
" value" are replaced  everyw h ere b y th e phrases "ran ge w ith  resp ect to 
3# %i> Sr*. 3f*. • • ■” and "value w ith  resp ect to  3 . %lr $ 2, g 3, . . .” resp ectively. 
A nd th e ru les are then regarded as co n stitu tin g  a (sy n ta ctica l) definition 
of th ese la tte r  phrases.
A  w ff of Fgp is said to  be valid with respect to th e sy ste m  o f dom ain s 3# 
2k* 2fe* Sf», • ■ • if it has, w ith  resp ect to 3 , 
3f*. 
* * •» th e valu e t for all
possible v a lu es o f its free variab les;511 an d  satisfiable with respect to th e system  
of d om ain s 3 , & , g a, 
. . ., if it h as, w ith  resp ect to  %  2ri> 
the.
value t for a t lea st one sy stem  of p ossib le valu es of its  free variab les. (H ere, 
by a " p ossib le"  v a lu e of a variab le is m ean t a v alu e th a t b elon gs to th e range 
of th e variab le w ith  resp ect to 3 , 2fi* 
2r*i * • *■)
A  sy ste m  o f dom ain s 3 , 2k. 
2r3, • ■ •1S said to  b e normal if all th e axiom !
of F 2P are v a lid  w ith  respect to it, a n d  every rule of in feren ce o f F ^  has the 
prop erty of p reservin g v a lid ity  w ith  respect to  it (i.e., th e p rop erty that," 
w hen ever th e prem isses of th e rule are valid  w ith  resp ect to  3 , $ 1, 
Srs* ■ ■ ** 
the con clu sion  is also valid w ith  resp ect to  3 , 2ft* 2ft> 2rs* * • ■)■ E v id e n tly , in 
a norm al sy ste m  of d om ain s, no dom ain is em p ty .
A  w ff of F 2P is said  to be valid in th e n o n -em p ty  d om ain  3  of in d ivid u als 
if it is v a lid  w ith  respect to  th e sy ste m  of dom ain s 3 i 2ft* 2ra* 2k. • . 
where 
2ft is th e cla ss of all p ro p o sitio n a l functions h a v in g  th e in d ivid u als (all 
m em bers of 3 )  as their range, 2ra is th e class o f a ll p rop osition al fu n ction s
4UAs usual, if there are no free variables, then, by ''having the value t for all possible 
values of its free variables,” we understand simply, denoting t. (Compare footnote 312.)

---


§**]
HENKIN COMPLETENESS THEOREM
309
Which have all ordered pairs of individuals as their range, and so on.612 
,And a wff is said to be satisfiable in the non-empty domain $  of individuals 
if it is satisfiable with respect to this same system of domains.
A wff is valid if it is valid in every non-empty domain 
of individuals; 
Satisfiable if it is satisfiable in some non-empty domain $  of individuals. A 
wff is secondarily valid if it is valid with respect to every normal system of 
domains; secondarily satisfiable if it is satisfiable with respect to some normal 
system of domains. It can be shown that every secondarily valid wff is valid, 
and every satisfiable wff is secondarily satisfiable (compare the proof of 
**434).
The universal closure of a wff B in which no free functional variable is 
more than «-ary is the wff
{<£ ) (c: _t) . . • (c?) (c"-1) (c;-1 .).. . (c”- 1) ■
n 
n 
n- 1  
n- 1
(O (<-l) • • • (Cl) (O 
■ ■ • (Cl) (C«) (Cu-1) • • -(Cl)B-
where c*, c*, . . 
c£ are the free A-ary functional variables of B in alpha­
betic order (k — 1, 2, . . ., n), cj, c2) . . 
c^  are the free propositional vari­
ables of B in alphabetic order, and cv c2, . . 
c u are the free individual 
variables of B in alphabetic order. The existential closure of B is similarly 
defined, with existential quantifiers replacing the universal quantifiers.
The following metatheorems about F2P are proved in the same way as 
their analogues in §43:
**540. 
A wff A is valid with respect to a given normal system of domains 
if and only if ~A is not satisfiable with respect to that system of 
domains; valid in a given non-empty domain of individuals if and 
only if ~A is not satisfiable in that domain; valid if and only if ~A 
is not satisfiable; secondarily valid if and only if ~A is not secon­
darily satisfiable.
**541. 
A wff A is satisfiable with respect to a given normal system of 
domains if and only if ~A is not valid with respect to that system 
of domains; satisfiable in a given non-empty domain of individuals 
if and only if —A is not valid in that domain; satisfiable if and 
only if ~A  is not valid; secondarily satisfiable if and only if ~*A is 
not secondarily valid. l
lllThe domain of individuals being fixed as some particular non-empty domain, a 
closed wff may be said to be true if it is valid in that domain. Since the sentences of the 
(pure) functional calculus of second order are the same as the closed wffs, this may be 
taken as the syntactical equivalent of the semantical property of being a true sentence, 
as described in §09.

---


310
FUNCTIONAL CALCULI OF SECOND ORDER [Chap. V-
**542. 
A wff is valid with respect to a given normal system of domains if 
and only if its universal closure is valid with respect to that system 
of domains; valid in a given non-empty domain of individuals if 
and only if its universal closure is valid in that domain; valid if 
and only if its universal closure is valid; secondarily valid if and 
only if its universal closure is secondarily valid.
**543. 
A wff is satisfiable with respect to a given normal system of do­
mains if and only if its existential closure is satisfiable (or equiva­
lently, valid) with respect to that system of domains; satisfiable in 
a given non-empty domain of individuals if and only if its existential 
closure is satisfiable in that domain; secondarily satisfiable if and 
only if its existential closure is secondarily satisfiable.
*544. 
Every theorem of F|p is secondarily valid, and therefore also valid.
As in §45, if T  is any class of wffs of any of the functional calculi of second 
order, we say that P h  B if there are a finite number of wffs Alt A2, .. „ A*, 
of T  such that Alf Aa, . . Am h B. 
JT is inconsistent if JHf- /, and in the 
contrary case r  is consistent. 
C is inconsistent with r  or consistent with T  
according as the class whose members are C and the members of /Ms incon­
sistent or consistent. JT is a maximal consistent class of closed well-formed 
formulas if JT is consistent and no closed wff C is consistent with JT which is 
not a member of JT.
A class r  of wffs of F2P is said to be simultaneously satisfiable with respect 
to a system of domains if, with respect to that system of domains, all the 
wffs of r  have the value t simultaneously for at least one system of possible 
values of all their free variables taken together. And /Ms said to be simultane­
ously satisfiable in the non-empty domain Q of individuals if it is simultane­
ously satisfiable with respect to the system of domains 
* * •»
where ^  is the class of all propositional functions having the class ^  of 
individuals as their range, 
is the class of all propositional functions having 
the class of ordered pairs of individuals as their range, and so on. And /Ms 
said to be simultaneously satisfiable if it is simultaneously satisfiable in some 
non-empty domain 3 -
We consider an applied functional calculus of,second order, S, having as 
primitive symbols all the primitive symbols of Fjp, together with the indi­
vidual constants wQ, wv w%t . . . and, for every positive integer k, the A-ary 
functional constants wJ, 
By an adaptation of the method of
footnote 416, we fix a particular enumeration of the closed wffs of S, and

---


HENKIN COMPLETENESS THEOREM
311
5641
referring to this enumeration, we speak of "the first closed wff of S," "the 
Second closed wff of S," and so on. Moreover, using this enumeration, we 
Can extend an arbitrary consistent class /'o f closed wffs of S to a maximal 
consistent class P  of closed wffs of S—by the same method which was used in 
§46 (compare **452 and its proof).
Now let H be a closed wff of FgP which is not a theorem.
The class JT0 whose single member is ~H is then a consistent class of 
wffs—of F*p, and therefore also of S. We define the classes Tn by the follow­
ing recursion rule:613 If the (n -f- 1)th closed wff of S has the form (a)A, 
Where a is an individual variable, and if in the list w0, wx, w2t. . .  the first 
constant that does not occur either in A or in any member of T n is wm, 
then r n+1 is the class whose members are
S * b A| => (a)A
and the members of r n\ if the (w +  1)th closed wff of S has the form (a)A, 
where a is a 6-ary functional variable (6 — 1, 2, 3, . . .). and if in the list 
wj, w\, w\, . . . the first constant that does not occur either in A or in any 
member of T n is w*, then T n+1 is the class whose members are
S**A | Z3 (a)A
tit
and the members of Tn] and otherwise Tn+l is the same as T n.
Then (for n =  0, 1, 2( . . .) Tn is a finite class of closed wffs of S. We shall 
show by mathematical induction that every I \  is consistent.
Suppose that, for some particular n, Tn is consistent but i'n+1 is incon­
sistent. Then we must have the case that JTn+1 is not the same as T n but has 
the additional member
S “ A| r> (a)A,
where w is a suitably chosen constant (as described above). By the incon­
sistency of jTn+ll and the deduction theorem (*516),
r n b S* A| zd (a)A zd /.
In this proof from hypotheses, replace w  everywhere by a new variable x, 
which is of the same type as a and which does not otherwise occur. Since w  
does not occur in A or in any of the members of T n, we thus have
4WThe device which is used a t this point was suggested to the writer by Henkm in 
July 1650. As compared to the procedure at the corresponding point in §45. or in Hen- 
kin’s dissertation, it has the advantage of making it possible to replace the infinite 
sequence of applied functional calculi Slf St, S*. . . . by the single applied functional 
calculus S. A similar simplification could have been made in §45 in the proof of **453; 
•but, because the difference in length is slight, we have there retained the older form of 
the proof (which it is thought may be instructive).

---


312
FUNCTIONAL CALCULI OF SECOND ORDER [Chap. Vj
r n hS*A | Z3 (a)An3 /.
Hence by generalizing upon x and then using the theorem schemata *380 
and *383 (or analogues of them),
r n V (x)S* A| =3 (a) A => /.
By alphabetic change of bound variable,61*
Zn b (a) A zd (a)A z> /.
But since (a)A zd (a)A is a theorem (by P), we then have Zn b /, contrary 
to the supposed consistency of Z n.
Since Z0 is consistent, and the consistency of Z ^  follows from that of Z« 
(as just shown), therefore every r n is consistent.
Let r  be the union of the classes Z0, r v Z2, . .
and let Z  be the extension 
of r  to a maximal consistent class of closed wffs of S.
We need the following properties of Z  (where in dl-e3, A and B are 
closed wffs of S):
dl. If A is a member of Z, then ~A  is a non-member of Z (For otherwise 
r  would be inconsistent, by P.)
d2. If A is a non-member of Z, then ~A is a member of Z. (For if A is a 
non-member of Z, then A must be inconsistent with Z; therefore, by the 
deduction theorem and P, Z b ~ A ;  therefore ~A is consistent with Z; 
therefore ~A is a member of Z.)
el. If B is a member of Z, then A zd B is a member of Z. 
(For by P. 
Zb A zd B; thus A zd B is consistent with Z  and therefore a member of Z.
e2. If A is a non-member of Z, then A zd B is a member of Z. (For by d2< 
~A  is a member of Z, and therefore by P, Z b  A zd B.)
e3. If A is a member of Z  and B is a non-member of Z, then A ZD B is a 
non-member of Z. (For by d2, ~B  is a member of Z; hence if A zd B were a 
member of Z, Z  would be inconsistent.)
fl. If a is an individual or functional variable, and if, for every constant 
w of the same type as the variable a,
s>
is a member of Z, then (a)A is a member of Z. (For in consequence of the 
way in which the classes Zn were defined, there is some constant w of the 
same type as the variable a such that
M4If a does not occur as a bound variable in A, one application of *515 is sufficient. 
Otherwise the required result may be obtained by three or more successive applications 
of *515.

---


§54]
HENKIN COMPLETENESS THEOREM
313
S“ A| 
(a) A
is a member of / ,  therefore a member of /*.)
fl'. If a is a propositional variable, and if both S*A| and S*A] are 
members of /*, then (a)A is a member of /*. (By *514, *515.)
f2. If a is an individual or functional variable, and if, for at least one 
constant w of the same type as the variable a,
Sw A I
is a non-member o f / 1, then (a) A is a non-member o f / 1, (By f509 and *5Q9n.)
f2', If a is a propositional variable, and if either
S*A | 
or S*A|
is a non-member of /*, then (a)A is a non-member of /*. (By *5090.)
To each of the individual constants i&n we now assign as associated natural 
number the number n (i.e., 0 is the associated natural number of w0, 1 is 
the associated natural number of wv and so on). And to each of the A-ary 
functional constants w\ we assign as associated propositional junction the 
fc-ary propositional function 
of natural numbers determined by the rule 
that 
u%, . . 
uk) is t or f according as w*(wu . 
a-*Ujb) is a
member or a non-member of / \
We shall also speak of the natural number n as associated to the constant 
wn, and of the propositional function 
as associated to the constant w \.
Let the domain $  consist of the natural numbers, let the domain ^  
consist of the associated propositional functions of ail the singulary func­
tional constants w\, let 
consist of the associated propositional functions 
of all the binary functional constants w\, and so on. Then each of the do­
mains 
Si* &2* 2t3< • * • is finite or enumerably infinite.615
With respect to the system of domains 
$ 2> $ 3' * • •- 
va*ue 
a 
wff X of Fjp, for a given system of values of its free variables x1( x 2, . . 
x7n, 
is t or f according as
C * i* a  **■ 
V i
V W j W ,...W m  A
is a member or a non-member of /*, where w (. is the constant, or one of the 
constants, to which the value of x, is associated [i =  1, 2,..., w), or in case x^ 
is a propositional variable, w t- is t or / according as the value of x, is t or f.
,1#The possibility that the domains jji, Sa- Ss- • - ■ may all be finite is realized if, 
for example, we take H to be the wff (3x)(3y)(3i?) . F(x) ~F{y), which has a non- 
valid afep and is therefore not a theorem (**530). On the other hand, if we take H to 
be the negation of one of the axioms of infinity (see §57), then all the domains m ust 
be enumerably infinite.

---


314
FUNCTIONAL CALCULI OF SECOND ORDER 
[Chap. V
This follows, in fact, from the definition of validity with respect to a 
system of domains and from the properties dl, d2, el, e2, e3, fl, ft', f2, f2' 
listed above.
Taking X to be the particular wff —H, which has no free variables, and 
which is of course a member of 
we have therefore that ~H is valid 
with respect to the system of domains 3* % v  
........
Taking X to be any axiom of F f, we have that
ss;-rxi
is always a theorem of S and therefore a member of F .  Therefore again X 
is valid with respect to the system of domains 3. 
% t>  %s> • • ••
In order to establish that 3. 
5»> • • •are a normal system of domains,
we have to show further that each of the four rules of inference of Fj1* 
preserves validity with respect to this system of domains. In each case this 
may be done by considering the universal closure of the premiss or premisses 
of the rule and the universal closure of the conclusion, since it is obviously 
always a derived rule of inference that the universal closure of the conclusion 
may be inferred from the universal closure of the premisses. If the premisses 
are valid with respect to the system of domains in question, then by **542 
their universal closures are valid with respect to that system of domains, 
and are therefore members of F] therefore the universal closure of the con­
clusion is a member of F \ therefore the universal closure of the conclusion 
is valid with respect to the system of domains in question; therefore 
finally by **542 the conclusion itself is valid with respect to that system 
of domains.
Thus we have proved the metatheorem:
**545. If a closed wff H of Fj* is not a theorem, there exists a normal 
system of finite or enumerably infinite domains with respect to 
which —H is valid.
Now consider a secondarily valid wff A of Fj1*, and let H be the universal 
closure of A. By **542, H is also secondarily valid. Therefore there can be 
no normal system of domains with respect to which ~H is valid. Therefore 
by **545, H is a theorem of F j\ Therefore A is a theorem of Fj1*.
Thus we have as a corollary of **545 the following metatheorem (Henkin’s 
completeness theorem for the pure functional calculus of second order):
**546. Every secondarily valid wff of Fj1* is a theorem.
From one point of view, Henkin’s completeness theorem for the functional 
calculus of second order is much like Godel's completeness theorem for the

---


§54]
EXERCISES 54
315
functional calculus of first order, since the semantical significance in both cases 
is that all those wffs are theorems which, under all of a certain class of interpre­
tations of the calculus, have the value t for all systems of values of their free 
variables. There is, however, the im portant difference that in the case of the pure 
functional calculus of first order the interpretations are the principal interpre­
tations, whereas in the case of the pure functional calculus of second order 
they include also the secondary interpretations. At issue is the question of the 
intention in formulating the calculus; and properly speaking, Henkin’s theorem 
has the meaning of a completeness theorem only if it was intended in formulating 
the pure functional calculus of second order to treat the secondary as well as the 
principal interpretations. In fact it is impossible to extend the pure functional 
calculus of second order by adding rules and axioms in such a way that the theo­
rems come to coincide with the wffs which have the value t for all systems of 
values of their free variables, under all the principal interpretations. (This last 
will follow from the famous incompleteness theorems of Godel, to be discussed 
in a later chapter.)
There is also another point of view from which Henkin's completeness theorem 
for the functional calculus of second order is weak compared to that of Gddel 
for the functional calculus of first order. For we have in connection with the 
latter theorem that there is one particular interpretation (the principal inter­
pretation with the natural numbers as the individuals) under which the theorems 
coincide with the wffs that have the value t for all systems of values of their 
free variables. But in the case of the pure functional calculus of second order 
there appears no such one interpretation relative to which we have completeness; 
and if in particular we adopt the principal interpretation with the natural 
numbers as the individuals, there are various independent axioms (not contain­
ing any new primitive symbols) which we may be led to add, and some of the 
most immediate of which are given in §§56, 57.
As further corollaries we have;
**547. 
Every wff of Fj1* which is valid with respect to all normal systems 
of finite and enumerably infinite domains is secondarily valid, 
and valid.
**548. Every wff of Fj1* whose negation is not a theorem is satisfiable with 
respect to some normal system of finite and enumerably infinite 
domains.
EXERCISES 54
54.0. The wffs of the extended propositional calculus (in the formulation 
of it which is used in §53) are included among the wffs of Fj1’. Hence the 
definition in §54 of validity of wffs of Fj1* applies in particular to wffs of the 
extended propositional calculus. (1) Prove that this definition of validity of 
wffs of the extended propjositional calculus is equivalent to that of §53 in the

---


316
FUNCTIONAL CALCULI OF SECOND ORDER [Chap. V
sense that the class of valid wffs is the same. (2) Prove that a wff of the 
extended propositional calculus is a theorem of Fjp if and only if it is valid.
S4-I- In view of the solution of the elimination problem of the singulary 
functional calculus of second order in 52.6(1), and of results concerning F/p 
obtained in exercises 48, prove that, if a wff of the singulary functional 
calculus of second order Fg’1 is valid in every non-empty finite domain, 
then it is valid, and a theorem.
54-»- Determine which of the following things are true of every normal 
system of domains Q, 
^ 2, %3, . . 
and supply a proof or disproof in each 
case: (1) ^  contains the null class and the universal class of individuals.Blfl 
(2) If ^  contains any two classes of individuals, it always contains also the 
class which is the union of those two classes. (3) 
contains the relation of 
identity or equality between individuals, and the relation of non-identity or 
diversity between individuals.516 (4) If 
contains any relation between 
individuals, then 
always contains the domain and the converse domain 
of that relation.617 (5) If 
contains any two relations between individuals, 
it always contains also their relative product 618
54-3 Let 
$ lt 2fa, fj3, ..., be a system of domains of the kind described 
in the first paragraph of §54. Show that it is a normal system of domains if 
and only if Q; is non-empty and, for every wff A of F |p, for every list 
a1( a2, ..., an of distinct individual variables {n ^  1), and for every system 
© of values (with respect to 
2fi* $ 2- S 3 • ■ •) °f the free variables of A
other than a1( a2, . . anJ there is a propositional function 0  in %n such 
that 0 (a v az, ..., an) is always the same as the value of A with respect to 
& 
%2> 2r3* • * ■ for the values av a2, . . an of a1( a2, . . an and the
system of values © of the remaining free variables of A. (Notice that this 
characterization of a normal system of domains, unlike that in the text, is 
independent of the axioms and rules of inference of F2P.)
54-4- Show (as is assumed in the text) that every consistent class of 
wffs of Fap is a consistent class of wffs of the applied functional calculus S. * 87 818
*u As explained in §04, we take classes to be singulary propositional functions and 
relations to be binary propositional functions.
8l7The domain of a relation is the class of things (individuals) which bear that relation 
to at least one thing; and the converse domain of a relation is the class of things to which 
at least one thing bears that relation. (The converse domain of a relation is thus the 
same as the domain of the converse of the.relation, where "converse’' has the meaning 
explained in §03.)
818The relative product of two relations 
and 
is the relation which holds between 
two things (individuals) a and b if and only if there is a t least one thing c such that a 
bears the relation ^  to c and c bears the relation W to b.
For example, if we take the individuals to be human beings, the relative product of 
the relation husband and the relation daughter is the relation son-in-law; and the relative 
product of the relation parent and the relation parent is the relation grandparent.

---


§55]
POSTULATE THEORY
317
54-5- By the methods of §54 prove: Every consistent class of wffs of F 
is simultaneously satisfiable with respect to some normal system of finite 
and enumerably infinite domains.
5 4 .6 , Supply a proof of Godel’s completeness theorem for the functional 
calculus of first order which parallels as closely as possible the proof of 
the metatheorems **545 and **546 in §54.
55. Postulate theory.618 From the viewpoint which is explained in 
§07, when a system of postulates is used as basis for the formal treatment of 
some mathematical theory or branch of mathematics (say, for example, 
arithmetic, or Euclidean plane geometry), the postulates have to be thought 
of as added to an underlying logic. And indeed for the precise syntactical 
definition of the particular branch of mathematics it is necessary to state 
not only the specific mathematical postulates but also a formalization of 
the underlying logic, since the class of theorems belonging to the branch of 
mathematics in question is determined by both the postulates and the 
underlying logic, and could be changed by a change in either.620
81BFor other discussions of postulate theory from the logistic standpoint see for exam ­
ple Carnap's Abriss der Logistik (Vienna, 1929), Carnap's The Logical Syntax of Lan­
guage (New York and London, 1937), and Hilbert and Bernays's Grundlagen der Mathe- 
matik (Berlin, 1934, 1939). Though the reader m ust allow for some differences in 
approach and term inology, we believe that our account of the matter is in essential 
agreem ent w ith that of these authors.
8aoThe poin t m ay be illustrated by the case of elem entary number theory versus 
analysis, since these two branches of m athem atics m ay be based if we like on the very 
same system  of postulates, but w ith different underlying logics, Namely, elem entary 
number theory m ay be defined by adding the postulates (Ax), given below, to an applied 
functional calculus of first order containing all propositional and functional variables 
as well as the functional constants which appear in the postulates. And analysis m ay 
be defined by adding the sam e postulates to an applied functional calculus of fourth 
order— since, in the resulting system , rational, real, and com plex numbers m ay be 
introduced by any of various well-know n m ethods for defining these numbers in term s 
of the natural numbers.
The foregoing statem ent is open to certain reservations because of uncertainty as to 
exactly w hat should be understood by "elem entary num ber theory" and "analysis" 
a s they appear in common (informal) m athem atical usage. It is the feeling of the writer, 
however, th at "elem entary number theory" is preferably understood in such a w ay as 
not to exclude the expression of certain generalities about classes and functions of 
natural num bers— as, e.g., the proposition that in every class of natural numbers there 
is a least number.
On the other hand, in the system  obtained by adding the postulates (Ax) to an 
applied functional calculus of second order there is a certain sense in which a large part 
of analysis can already be obtained, by m eans of appropriate artifices which are beyond 
the scope of our present discussion.T he decision to go as high as the functional calculus 
of fourth order in specifying the underlying logic of m athem atical analysis is thus open 
to som e question, but again it would seem  to the writer th at this best represents the 
existing inform al usage.
W hen the underlying logic is a functional calculus of second or higher order it is usual, 
as noted below, to replace the postulates (AJ by the more economical system  of 
postulates (A ,). However, this need not affect our present illustration, since the postu ­
lates (Ai) could always be retained if desired.

---


318
FUNCTIONAL CALCULI OF SECOND ORDER [Chap. V
The present section is devoted to a digression for the further treatment of 
this matter, and the introduction of a number of examples. This seems to be 
an appropriate place for such a discussion, because in many cases it is 
sufficient to take the underlying logic to be a functional calculus of first or 
second order.
As a first example we take the following system of postulates for arith­
metic, which we shall call (A0), and for which the underlying logic is to be 
(syntactically) a simple applied functional calculus of first order. There are 
two undefined terms, the ternary functional constants E  and 77; and the 
notations Z0, Zv  and =  are introduced by the following definition sche­
mata,621 in which a and c are any variables, b is the next individual variable 
in alphabetic order after a, and d and e are the first two individual variables 
in alphabetic order distinct from each other and from a and c;
Z0(a) -* (b)J7(a, b. b)
Z,(a) 
(b)/7(a, b, b)
[a =  cl -> (d)(e) . Z(a, d, e) => S{c, d, e)
The postulates include first of all the twelve following:
{3z)£(z, y, z)
£(*i. *2. t/i) => ■ £(**, z3, y2) => ■ £(yi, *s. *) => £(*i. Vz. z)
Z{x, y, 2) => Z(y, z, z)
£ ( * 1, y , 2) 3  * 2 { x t , y , 2) => ■ *i =  *2
{3 x )2 :{x , y , y )
{3z)IJ[x, y, z)
n (*„ x2, y,) 
. 77(*2, x3, y2) =3 . Tl{ylt xa, z) => II{xv, y2, z)
m In connection with the informal statem ent of these postulates, additional undefined 
terms 0, l, and =  (some or all of them) would often be listed. However, the logistic 
method shows these additional undefined terms to be unnecessary. Individual constants 
0 and 1 indeed are not provided for by the definitions which we give, but the notations 
ZQ and 2\ serve the essential purposes which would be served by the actual inclusion of 
individual constants 0 and l as undefined terms.
For the informal statem ent of the postulates, "natural number" would also ordinarily 
be listed as an undefined term. This additional undefined term  has not so much been 
eliminated by our present method as incorporated into the undefined terms £  and il, 
because we regard the range of a function as determined by the function, and as being 
given as soon as the function itself is given. (To change the range would be to change 
the function itself to a different function.) Or alternatively, if the reader prefers, he 
may regard the undefined term "natural number" of the informal statem ent as rep­
resented by the individual variables—which have the individuals, i.e., the natural 
numbers, as their range.

---


§55]
POSTULATE THEORY
319
77(x; y , z) z> /7(t/, x, z)
2/> *) => - /7(«2. Vi *) ==> 
12/) V ^  =  ar2
(3a?)/7(ar, y, y)
/ 7(*1» *^2> yz) ^  ■ n [x v xz, yz) :d ■ Z{x%t a?3, yx) r> . S[yv y3, *) r> i7(aslf yXi z)
Zx(y) => m£(x, y, z) r> ~Z0(z)
Then in addition to these twelve, there is an infinite list of postulates of 
mathematical induction—as given by the following postulate schema, in 
which A is any wff not containing the variable z and B is $*A|:
ZQ{x) CD . Zx(y) :d . A d
. A d , (3 z){Z(x, y , z) B] r> [x)A
This system of postulates (A0) is to be added to the simple applied 
functional calculus of first order Flh (see §30) as underlying logic. The re­
sulting system is a formulation of what we shall call elementary arithmetic
Of the logistic system  A0, obtained by adding the postulates (A0) to F lh, the 
principal interp retatio n  is th e sam e as for Flh itself, and is given by th e se­
m antical rules a -£  of §30. T he separation of th e sem antical rules into two 
categories, as spoken of in §07, is by assigning the rules a 0, 0O, y, <5, e, £ to the 
underlying logic, and th u s p u ttin g  them  in th e first category, while th e  rules 
«i* Pit an d  p t are p u t in th e  second category.
As a result, for the value a of a, Z 0(a) denotes t or f according as a is or is not 
0, Z t (a) denotes t or f according as a is or is not 1. Wc m ay th u s take these 
notations as m eaning respectively th a t a is 0 and th a t a is 1. And in a  sim ilar 
way we m ay  take the n o tatio n  =  as m eaning eq u ality  of natural num bers. For 
although th is is a different sense of " = "  or "eq u als’1 from th a t given by  D22, 
there is no reason th a t we should n o t change the sense of "equals" m  connection 
w ith A 0, since the propositional function is not changed in extension, an d  since 
the m athem atical theory is not thereby altered form ally or prevented from  serv­
ing its purpose.
T he first five postulates of (A0) express, in order, the existence of th e sum  of 
two n atu ral num bers, the associative law of addition, the com m utative law  of 
addition, th e  law of cancellation for addition, and (in a  weak sense) the existence 
of an id en tity  elem ent for addition. The next five postulates express th e five 
corresponding properties of m ultiplication of n atu ra l num bers. The eleventh 
postulate expresses the d istrib u tiv e law. And th e tw elfth postulate expresses 
th at the result of adding 1 to  a natural num ber is never 0.
E ach of the postulates of m athem atical induction— as given by the postulate 
schem a— either expresses a certain  particular case of the principle of m ath e­
m atical induction, if A contains no free variables except x, or else, if A contains 
other free variables, expresses a  principle which (though it has some generality)
•“ Introducing this term in a sense which we distinguish from that oi "elementary 
number theory."

---


320
FUNCTIONAL CALCULI OF SECOND ORDER [Chap. V
is still to be regarded as ob tain ed  from  th e general p rin cip le of m ath em atical 
induction b y  a specialization.
In view  of th e  lack of fu n ction al variables, it is n ot p o ssib le in A0 to express 
the p rinciple o f m ath em atical in d u ctio n  as a general law . H ow ever, such an 
expression of th e general prin cip le o f m ath em atical in d u ctio n  appears below  
as th e final p ostu late of th e sy stem  o f p ostu lates (A,).
In sp ite of th e  restriction im p osed  b y th e lack of fu n ctio n a l variables, su b stan ­
tia lly  all th e prop osition s o f elem en ta ry  num ber th eory, as u su ally understood, 
can b e exp ressed  and proved in A0, ex cep tin g  o n ly  th o se w h ich  d irectly  require 
fun ction al v ariab les (such as, e.g ., th e principle of m a th em a tica l in d u ction , or 
the principle th a t is stated  in ex ercise 55.12). W e sh all n o t carry th is o u t here, 
even in part, b u t refer th e reader to  th e treatm en t o f an  eq u iv a len t sy ste m  by 
H ilbert and B ern a y s in G r u n d l a g e n  d e r  M a t h e f n a t i k . A cru cia l p oin t is th e m eth od , 
due to  G o d e l/”  of introducing b y  d efin ition  oth er num erical fu n ction s than 
ad d ition and m u ltip lication — e.g ., ex p o n en tia tio n , th e  factorial, th e q u o tien t 
and rem ainder upon division, th e n th  p rim e num ber as a fu n ction  o f n , and in ­
deed recursive functions gen erally.
Another example is the following system of postulates (AJ. The undefined 
terms are 27 and 77, and the definition schemata for the notations Z0> Z v  =» 
are the same as in the case of (A0). There are thirteen postulates, of which 
the first twelve are the same as the first twelve postulates of (A0), and the 
thirteenth is the p o s tu la te  o f m a th e m a tic a l in d u c tio n ,
Zq^ )  =3 . Z^y) zd . F{x,} => . F(x) zdx (32)[27(a;, y, z)F(z)] => ( s ) 7 » .
The underlying logic is (or is formalized as) the functional calculus F\A, 
i.e., a functional calculus of first order which has the ternary functional 
constants 27 and 77, and in addition all propositional and functional vari­
ables, the same as the functional calculus Fla of 30.4 except that the rules 
and axioms of §40 are used instead of those of §30. And the logistic system 
obtained by adding the postulates (Aj) to this underlying logic we shall take 
as a formulation of e le m e n ta r y  n u m b e r  th e o ry , or (as we shall also say) of 
fir s t-o r d e r  a r ith m e tic .6M
The postulates (Ax) might of course also be added to a functional calculus 
of second or higher order as underlying logic, so obtaining a stronger system,
il9Monatshefte fiir Mathematik und Physik, vol. 38 (1931), see pp. 191—103.
6MCf. footnote 520. T o  logistic formulations of either elementary arithmetic o r  first- 
order arithmetic the name Hilbert arithmetic is often given because of the introduction 
of systems of this kind by Hilbert and his school. See a paper by Hilbert in Abhand- 
lungen aus dem Mathemaiischen Seminar der Hamburgiscken UniversittU, vol. 6 (1028), 
pp. 65*85 (reprinted in the seventh edition of Hilbert's Grundlagen der Geometrie); 
«Ut> m p a p e r  b y  A o k e rm a n n  In th e  Mathematieehe Annabn, v o l. 117 U 04Q ), p p . 108-1941 
as well as the treatm ent of the systems Z, Z*. Z**, Z', etc. by Wilbert and Bernays 
in Grundlagen der Mathematik.

---


§55]
POSTULATE THEORY
321
but instead of this we prefer to employ the following different system of 
postulates (A2), which are equivalent to (Ax) when so used.
The postulates (A2) are essentially a form of Peano's postulates for the 
natural numbers,62* as modified for use in the present context. There is a 
single undefined term, the binary functional constant S. The notations =  
and #= are those introduced in D22 and D23. And the notations Z0, Zx are 
introduced by the following definition schemata, in which a is any individual 
variable, and b is the next individual variable in alphabetic order after a;
Zq{a) -* (b)~S(b, a)
Zt ( a) ^ (3 b ).Z 0(b)S(b, a)
The postulates are the five following:
(3y)S{x, y )
S(x, y) => . S(z, 2) => . y  — z 
S(y, x) r> .S(z, x) => . y — z 
(3x)Z0(x)
Z0(x) => . F{x) => . F[y) =>„ [S(y, z) =>, /'(z)] => {y)F(y)
In  th e interpretation, the individuals are again the natural num bers. And S 
denotes th e relation of having as sttccessor, so th a t, if a and b are the values of a 
and b, th en  5 (a, b) denotes t or f according as b is or is not equal to  a +  1. 
D etailed statem ent of the sem antical rules, for the case of a functional calculus 
of second order as underlying logic, m ay be supplied by analogy and is left to 
the reader.
The notations Z G(a) and Z x{a), for a value a of a, again m ay be taken as m ean­
ing, respectively, th a t a is 0 and th a t a is 1. The sense is indeed changed as com­
pared to  th e notations Z Q and Z x used in connection w ith (A0), or w ith (At). 
B ut th e  fact th a t the corresponding propositional functions are the sam e in 
extension is sufficient for th e purpose of the m athem atical theory.
A sim ilar rem ark applies to  the notations 27 and I J  which are introduced below 
by definition to replace th e notations 27 and I I  th a t appeared as undefined 
term s in the postulates (A0), or (A,).
The logistic system obtained by adding the postulates (A0) to Flh we 
call A0. That obtained by adding the postulates (Aj) to F2a we call A1. 
Those obtained by adding the postulates (A2) to a functional calculus of
m Aritkmetices Principia, Nova Methodo Exposita, Turin, 1889; Formulaire de Mathe- 
maliques, vol. II §2, Turin, 2898. As Peano points out, his postulates are in the treatise 
of ftjohftitt DeUekind, fK#i S i n d  ttnd was Soiten die Zahten* (1888), though not 
quite as postulates. Some of the essentials, however, are already contained in a paper 
by C. S. Peirce in the American Journal of Mathematics, vol. 4 (1881), pp. 85-95.

---


322
FUNCTIONAL CALCULI OF SECOND ORDER [Chap. V
wth order (n =  2, 3, 4, . . .) which has all propositional and functional vari­
ables appropriate to its order, and has in addition the binary functional 
constant S, we call A2, A3, A4, . . .. And we call An (n — 1, 2, 3, 4, ...) 
a formulation of nth-order arithmetic.
The detailed development of the system Aa will be the subject of a later 
chapter. At this place, we carry the matter no further, except to state the 
following definition schemata, introducing notations E  and I I  to replace 
the primitive notations E  and I I  of A° and A1:636
E ( & , b, c) -> [Z0(bo) ^>b0 ■ h =  c0 ”^Cq 
c0)][F(bo, ^o) ^b0c0 ■
S(b0) bi) =>bi. 5(c0, Cl) r>Ci F(blf cx)l 
F(b, c)
/7(a, b, c) 
[Z0(bo) 
Z 0 (c0) 
F(b0, c0)][F(b0, c0) ZDboCo -
S(b0, bx) =>bi. E { a, c0( q) zdCi F ( b l t q)] =3^ F(b, c)
—where, in both cases, a, b, c are any individual variables, and b0, c0, bXJ q  
are the first four individual variables in alphabetic order after the latest, 
in alphabetic order, of the variables a, b, c.
It should be noticed th a t these definitions do not introduce the notations 
E  and n  as functional constants, or as nam es of the propositional functions which 
in the system s A0 and A1 were denoted b y  E  and 27. In  fact the system  A* does 
not contain nam es of these propositional functions, an d  th e definitions do not 
assign any form ula of A 8 w hich is abbreviated by the le tte r E  or the letter 77 
standing alone. Only the com plete notations X (a, b, c) and 77(a, b , c) are 
abbreviations of formulas of A*.
N evertheless, for every theorem  of A0 or A1 there is a  corresponding theorem  
of A1 in w hich th e notations E ( a, b, c) and 77(a, b, c) of A0 or A1 are replaced
“ •These two definition schemata illustrate a general method that may be used to 
find expressions in the system to represent a numerical function which, in the informal 
treatment, would be introduced by means of recursion equations. The first schema, for 
example, corresponds to the following recursion equations for addition:
a -r 0 =  a
a +  (b +  1) =  (a +  6) +  I
And the second schema similarly corresponds to the following recursion equations for 
multiplication:
a x 0 =  0
a x  (fc -f- l) = a -r- [a x b)
This method, illustrated in the two detinition schemata in the text, was introduced 
by Hilbert and Bernays in G ru n d la g en  d er M a ih e m a tik , vol. 2 (1939), Supplement IV G, 
and by Paul Lorenzen in a paper in M o n a tsh e fte  fiir  M a th e m a tik  u n d  P h y s ik , vol. 47 
(1933-1939), pp. 356-358. Other methods serving the same purpose are due to Dede­
kind (1888) and to Kalm&r (1930, 1940), and might also be adapted for use in the pres­
ent connection. For an informal exposition of the m atter and a brief account of its 
history, see Kalm ar’s paper in A c ta  S c ie n tia r w n  M a tk e m a tic a r u m , vol. 9 no. 4 (1940), 
pp. 227-232.
The (informally stated) recursion equations themselves for addition and multipli­
cation are due to C. S. Peirce in the paper cited in the preceding footnote.

---


§55]
POSTULATE THEORY
323
by the different notations 
b, c) and 77(a, b, c) of A*.5”  And it is in this 
sense th a t we say th a t A* is adequate for elem entary num ber theory and does 
not require the functional constants 2T and 77 as additional undefined term s.
In  such a case, w here a com plex notation introduced by definition carries the 
false appearance or suggestion th a t some p a rt of the notation is to be tak en  as 
denoting (or otherw ise as having meaning in isolation), it is usual to speak of 
contextual definition. F or exam ple, by the two definition schem ata ju st given, 
the letters 2T and 77 are contextually defined; th ey  acquire significance only in 
the particu lar contexts 2?(a, b, c), 77(a, b, c), and not in isolation or in other 
contexts. Similarly, by earlier definition schem ata in this section— w hether 
those introduced in connection w ith A0 and A1 or those for A*— the letters Z 0 
and Z x are contextually defined.
On the other hand, D0 (for example) would n o t ordinarily be called a co n tex t­
ual definition of the sign =  , and D24 would not be called a contextual definition 
of =  . T he difference is th a t, in the notations w hich are introduced by 1)6 and 
D24, th ere is nothing w hich suggests th a t either of the signs =  or =  standing 
alone is significant in any w ay (e.g., as an abbreviation of a formula of a logistic 
system ).
T hus the contextuality of th e definitions of £  and 77 arises from the fact that, 
in th e above definition schem ata, we introduced the same parentheses and 
com m as for use after the letters £  and 77 th a t we also use after functional 
variables and functional constants. The contextual character of the definitions 
m ight be avoided b y  changing th e notations £ (a , b, c) and /7(a, b, c) to, say, 
Zabc and 77abc* However, th e convenience of using ordinary parentheses and 
com m as outw eighs the possible deceptiveness,628 and the present explanation 
should serve to preclude m isunderstandings.
W e tu rn  now  to  co n sid eratio n  of a n o th e r an d  different p o in t of view 
to w ard s th e p o stu lates of a m ath em atica l th e o ry , w hich is possible in certain  
connections, and w hich also requires e x p lan a tio n  here. In  o rd er to  d istin ­
guish th e  tw o we m ay, from  the point of view  w hich we have so fa r been 
explaining, speak of postulates as added axiom s of a logistic system an d , from  
th e new  p o in t of view , of postulates as propositional functions.529
“ ’This will follow from our later detailed treatm ent of the system Az, since all the 
postulates of A° and A1 can be proved as theorems of A4 when they are modified in the 
way described (i.e., when the notations £{a, b, c) and 77(a, b, c) of A° and A1 are 
replaced by those of A2).
"•One aspect of this convenience is in the process of substitution for functional vari­
ables. For example, the mere replacement of the ternary functional variable F  every­
where by the Letter £  represents what, in the unabbreviated notation, would appear as 
a considerably more complicated substitution operation (permitted by the rule of 
substitution for functional variables).
“ •The second point of view, as described below, has long been implicit m the use made 
of postulates by mathematicians, and in informal expositions of postulate theory, 
though the logistic method makes possible a more accurate statement of it. This point 
of view has been emphasized in particular by C, J. Keyser, who speaks in this connection 
of a "doctrinal function"—see a paper by him in The Journal of Philosophy, vol. 15

---


324
FUNCTIONAL CALCULI OF SECOND ORDER [Chap. V
It is necessary first to introduce the notion of the representing form of a 
postulate belonging to a given system of postulates.630
Given a system of postulates, we first select for each of the undefined 
terms a corresponding variable of the same type (i.e., an individual variable 
to correspond to an individual constant, and an n-ary functional variable 
to correspond to an n-ary functional constant), these variables being all 
different among themselves, and all of them occupying an odd-numbered 
place (first, third, fifth, etc.) in alphabetic order. To make the procedure 
definite, we are to select in each case the first available variable in alpha­
betic order; and where there are several undefined terms of the same type, 
they are to be taken in their own alphabetic order (the order in which they 
were originally listed) and the corresponding variables for them are to be 
introduced in that order. Then we replace each postulate by its universal 
closure—where the ‘'universal closure'1 is to be understood in the sense that 
all the free variables of the postulate are bound by initially placed universal 
quantifiers, and where therefore in some cases the expression obtained may 
not be a wff of the underlying logic of the postulates but only of the func­
tional calculus of next higher order. Then in these closures of the postulates 
we make alphabetic changes of all the variables, replacing a variable that 
occupies the mth place, in the alphabetic order of variables of its type, by 
the variable of the same type that occupies the 2wth place in alphabetic 
order. Then finally in each postulate we substitute everywhere for the un­
defined terms (constants) appearing, their corresponding variables. The 
result of this substitution is the representing form of the postulate.
For example, in the system of postulates (A^, the representing form of the 
postulate of mathematical induction is the following wff of the pure func­
tional calculus of second order:
(G)(*i)(y,) ■ (*»)F(Vv x3> *3) =3 . (z1)H(xl, XV *,) => . G(ys) => .
G(y) =>„ (3^)[F(y, xv ^)G(^)] => (y)G(y)
(19181, pp. 262-267. The “abstract'1 treatm ent of a system of postulates (“ assump­
tions"), as described by Veblen and Young in the Introduction of the first volume of 
their Projective Geometry (first published in 1910), represents substantially the same 
idea, though the term “propositional function" is not actually used.
Neither Veblen and Young nor Keyser make the distinction which is introduced 
below between the theorems and the consequences of a system of postulates. Indeed 
this would hardly have been possible before the work of Tarski and Carnap.
“ °We treat here only the case th at the underlying logic is one of the functional calculi 
of not higher than second order—though extensions to other cases, in particular to one 
of the functional calculi of higher order, may be made by analogy. The method of 
extension to functional calculi of higher order will become clear after the explicit for­
mulation of these calculi which is to be given in our next chapter.

---


§55]
POSTULATE THEORY
325
After having obtained thus the representing forms of the postulates, we 
may introduce also in the same way the representing form of any sentence 
or propositional form,631 B, of the logistic system which consists of the under­
lying logic together with the postulates. Namely, we apply the same proce­
dure to the wff B that we did to each of the postulates.
In order to introduce the notion of a model of a system of postulates, let 
T h e  the class of representing forms of the postulates, and let F be the pure 
functional calculus of lowest order in which all the formulas of T  are wf.532 
Then a model of the postulates is a non-empty domain Q of individuals 
together with a system of values of the free variables of the representing 
forms of the postulates which satisfies T  simultaneously in §  (or, in other 
words, which gives the value t simultaneously to the representing forms of 
the postulates, according to the notion of “value” which is defined in the 
theoretical syntax of F).
We remark that the various definitions of “value," as introduced for the 
various pure functional calculi, are coherent in the sense that a wff A of a 
pure functional calculus F has the same value for a given system of values of 
its free variables, whether A is taken as a wff of F or as a wff of one of the 
pure functional calculi of higher order than F. In regard to the pure function­
al calculi of first and second orders, this is clear from the definitions already 
given; and it will continue to hold also for the pure functional calculi of third 
and higher orders (to be discussed in Chapter VI). Hence in connection with 
a model of a system of postulates, the representing form of a wff that belongs 
to the underlying logic may be said to have a value for the model, even if 
this representing form is wf only in a functional calculus of higher order than 
is required for the representing forms of any of the postulates.
Now given a system of postulates, instead of considering the theorems of 
the logistic system, we may consider the consequences of the postulates in 
the following different (and non-effective) sense: A sentence or propositional 
form, A, of the logistic system which consists of the underlying logic to­
gether with the postulates is a consequence of the postulates if the value of the 
representing form of A is t for every model of the postulates.533
From the point of view towards postulate theory which we are now explaining, 
each postulate is looked upon in effect as a propositional function such that a
m In  the case of one of the functional calculi, any wff.
,,fFor this purpose, the pure functional calculus of first order with equality is to be 
counted as having an order between the first and the second.
,wThis is the notion of “ logical consequence" introduced by Tarski, Przeglqd Filo- 
xofiezny, vol. 39 (1936), pp. 58-68, and Actes du Congr&s International de Philosophic 
Scixntifique (Paris, 1936), p art VII, pp. I—11.

---


326
FUNCTIONAL CALCULI OF SECOND ORDER [Chap. V
system of arguments of the propositional function would consist of a non-empty 
domain $t of individuals together with a value of each of the free variables of 
the representing form of the postulate, and the value of the propositional 
function for these arguments would be the same as the value which they deter­
mine of the representing form of the postulate. Similarly the complete system 
of postulates corresponds to a propositional function, of which a system of argu­
ments would consist of a non-empty domain Of of individuals together with a 
value of each of the different free variables that appear in the representing forms 
of the postulates, the value of the propositional function being t or f according 
as these arguments do or do not constitute a model of the postulates.” 4 The 
consequences of the postulates—in the above non-effective sense of “conse­
quence’'—again correspond to propositional functions in the same way. Syn­
tactically, the mathematical theory to which the postulates lead consists of 
all the wffs taken together which are consequences.538 This mathematical theory, 
however, may be expected to have many interpretations—in fact, since we 
require a principal interpretation of the underlying logic, each different model * 65
H4We assume, in making this statement, that the number of undefined terms is 
finite. Modification to fit the contrary case could be made by considering a binary 
propositional function of which one argument would be the domain of individuals and 
the other argument would be the complete system of values of the free variables of the 
representing forms of the postulates.
655Contrast this with the previous point of view, according to which the mathematical 
theory consists of the theorems.
Objection may indeed be made to this new point of view, on the basis of the sort of 
absolutism which it presupposes—or Platonism as Bernays calls it (L*Enseignement 
Mathematique, vol. 34 nos. 1-2 (1935), pp. 52-69; cf. also A. Fraenkel, ibid., pp. 18-32). 
But it should be pointed out that this Platonism is already inherent in classical mathe­
matics generally, and it is not made more acute or more doubtful, but only more con­
spicuous, by its application to theoretical syntax. For our definition of the conse­
quences of a system of postulates can be stated for, and treated within, a formalized 
meta-language which we do not describe in detail here but which can be seen to be 
not essentially different from formalized languages which are required for the logistic 
treatment of classical mathematics.
There would certainly be cogent objections (cf, §07) to the proposal to introduce a 
formalized language by means of the non-effective notion of consequence, and to re­
place in this way the initial construction of the language within what we have called 
elementary syntax (§08). But after this formalization of the language (or at least after 
the formalization of both the object language and the meta-language), the use of the 
non-effective notion of consequence in the theoretical syntax of the object language is 
a different matter, and objections to it are on a different level.
It is true that the non-effective notion of consequence, as we have introduced it in 
theoretical syntax, presupposes a certain absolute notion of ALL propositional functions 
of individuals. B ut this is presupposed also in classical mathematics, especially classical 
analysis, and objections against it lead to such modifications of classical mathematics 
as mathematical intuitionism (to be discussed in a later chapter) or the partial intui- 
tionism of Hermann Weyl's Das Kontinuum (Leipzig, 1918).
(In this latter book, Weyl's objections to the absolute notion of all and to the vicious 
circle which it is held to involve lead him to a position which we may describe roughly 
as follows, that the simple functional calculi are replaced either by the corresponding 
predicative functional calculi or by the ramified functional calculi (cf. §58 and footnote 
583), Russell's axioms of reducibility (§59) being rejected. As is well known, though he 
is able to make a partial reconstruction of analysis, Weyl reaches the conclusion that 
a substantial part of the classical theory is a house built upon sand.)

---


§55]
POSTULATE THEORY
327
of th e syatc*in of postulates yields one interpretation of the m athem atical 
th eo ry .688 Thus th e co n ten t of the m athem atical theory is not fixed, b u t is itself 
to be looked on as th e value of a function.637
The notions of consistency, independence, and completeness in connection 
with a system of postulates can be introduced in two different ways, which 
we may associate with the two different points of view towards postulate 
theory. We shall distinguish "consistency as to provability" and "consist­
ency as to consequences"—and similarly in the cases of independence and 
completeness.
The notions of consistency, independence, and completeness as to prov­
ability will each depend in an essential way on the choice of the underlying 
logic as well as on the postulates themselves. But in the case of the corre­
sponding notions as to consequences this dependence can be wholly or partly 
removed, as we shall see below.
A system of postulates will be said to be consistent as to provability if the 
logistic system which consists of the postulates together with the underlying 
logic is consistent in one of our earlier senses (§17), say in the sense that there 
is no wff A such that both A and ~A are theorems.536
A system of postulates will be said to be consistent as to consequences if 
there is no wff A such that both A and ~A are consequences of the postu­
lates. Here A is a wff of the logistic system which consists of the postulates 
together with the underlying logic. But the dependence on the underlying 
logic is removed at once by the following metatheorem (which for the mo­
ment we must restrict to the case that the underlying logic is a functional 
calculus of no more than second order, but which can be generalized later 
to the case of a functional calculus of higher order):
” 6By an interpretation of the mathematical theory we mean, namely, an interpre­
tation of the logistic system which is obtained by adjoining the postulates, as additional 
axioms, to the underlying logic. This is the same sense in which an interpretation of the 
postulates is referred to in the last paragraph of §07.
The advantage of economy in the axiomatic method, in that the results obtained 
hold for all the various interpretations, is a point which has been too often stressed by 
other writers to need repetition here. (Compare the corresponding remark about the 
logistic method generally in §07.)
M7This is Keyser's doctrinal function, referred to in footnote 529. An accurate account 
of this notion from the point of view of the distinction of sense and denotation involves 
some complexities and will not be attempted here.
688Such a no'tion of consistency, involving the particular symbol 
is sufficient here 
because we are considering, as underlying logic, only the ordinary (applied) functional 
calculi of various orders, in the particular formulations adopted in Chapters III-V I. 
In order to extend the account to other systems as underlying logics, it will be necessary 
in each case to specify the sign (primitive or defined) which has to be identified as 
Or if this cannot be done, then one of the other notions of consistency may be used 
which is introduced in §17.

---


328
FUNCTIONAL CALCULI OF SECOND ORDER [Chap. V
**550. 
A system of postulates is consistent as to consequences if and only 
if it has a model.
We leave the proof of this to the reader, as well as of the following meta­
theorem ;
**55L 
If a system of postulates is consistent as to consequences, it is 
consistent as to provability.
In a system of postulates, the postulate A will be said to be independent as 
to provability if it is not a theorem of the logistic system which consists of the 
postulates other than A together with the underlying logic. And A will be 
said to be independent as to consequences if it is not a consequence of the other 
postulates.
Again we leave to the reader the proof of the metatheorems:
**552. 
In a system of postulates, a postulate A is independent as to con­
sequences if and only if the postulates other than A have a model 
for which the value of the representing form of A is f.
**553. 
In a system of postulates, if a postulate A is independent as to 
consequences, it is independent as to provability.
The metatheorem **552 provides for the familiar method of establishing 
the independence of a postulate A in a system of postulates by exhibiting a 
model of the remaining postulates which gives to the representing form of 
A the value f. Such a model is called an independence example for A.68*
The similar method of proving consistency of a system of postulates, 
namely, by exhibiting a model, is also well known.840 However, it happens 
in certain important cases that such a proof of consistency, though possible, 
is of doubtful significance, because in establishing the existence of the model 
it is necessary to use a meta-language in which equivalents (in some relevant 
sense) of the postulates and their underlying logic are already present. For 
example, the consistency of the postulates (A0), (A^, or (A2) may be dem­
onstrated by using the natural numbers in the obvious way to provide a 
model; but this is a line of argument which evidently would carry no weight 
at all for one who had real doubts of the consistency of ordinary arithmetic, 
and which, even if the purpose is only to verify the correct formalization of
#wThis method of establishing independence of postulates was used by Peano, 
Rivista di Matematica, vol. 1 (1891), see pp. 93-94, and by H ilbert in his Grundlagen det 
Geometric, first edition (1899), However, the origin of the method is to be seen still 
earlier in connection with the non-Euclidean geometry of Bolyai and Lobachevsky— 
models of the postulates of this geometry, found by Eugenio Beltrami (1868) and Felix 
Klein (1871), being in effect independence examples for Euclid's parallel postulate.
MoCf. the first edition of Hilbert’s Grundlagen der Geometric, pp. 19-21.

---


§55]
POSTULATE THEORY
329
a theory already admitted informally, seems to accomplish relatively little.
A system of postulates will be said to be complete as to provability if the 
logistic system which consists of the postulates together with the underlying 
logic is complete with respect to the transformation of A into 
(in the 
sense of §18). In many important cases, however, such completeness is 
unattainable, as is shown in the incompleteness theorems of Godel, which 
were already referred to in the discussion following * **546.
A system of postulates will be said to be complete as to consequences if, 
in the case of every wff A of the logistic system which consists of the postu­
lates together with the underlying logic, the value of the representing form 
of A either is t for every model of the postulates or is f for every model of 
the postulates.
The notion of completeness as to consequences, as thus defined, is not 
wholly free of dependence on the choice of the underlying logic. But such 
independence of the underlying logic is possessed by still a different com­
pleteness notion for postulate systems, namely, that of categoricalness, due 
to Huntington and Veblen,541 which we go on to define.
We consider only the case that the undefined terms belong to the notation 
of a functional calculus of first or second order, or of a functional calculus 
of first order with equality, i.e., the undefined terms are individual constants 
or functional constants in the sense of these calculi. However, the extension 
to higher cases is straightforward (compare footnote 530),
Two models of a system of postulates are said to be isomorphic if there is 
a one-to-one correspondence between the two domains of individuals used 
in the two models542 such that the values given in the two models to any
*41E. V. Huntington, Transactions oj the American Mathematical Society, vol. 3 (1902), 
see pp. 204, 277-278, 281, 283-284; Oswald Veblen, ibid., vol. 5 (1904), see pp. 346-347. 
Compare further the remarks of Huntington, ibid., vol. 0 (1905), pp. 209-210. The term 
categorical (now the usual one) appears first in the paper of Veblen, who credits the 
suggestion of it to John Dewey.
Though the formulation of the idea of categoricalness as a concept applicable to postu­
late systems generally seems to have been made first by Huntington and Veblen, results 
are found in the literature much earlier which are tantam ount to the categoricalness 
of particular systems of postulates. Thus paragraph 134 of Dedekind's Was Sind und 
was Sollen die Zahlen? (cf. footnote 525) contains the essentials of the usual proof of 
categoricalness of Peano's postulates, similar to that which is described in exercise 55.15 
below. And the result established by Georg Cantor in the Mathematische Annalen, 
vol. 4 6  (1895), pp. 510-512, is in effect that a certain system of postulates—his well- 
known characterization of the continuum—is categorical. (Dedekind speaks of "Be- 
dingungen" and Cantor of "Merkmale," rather than of postulates or axioms.)
M,Of course it is not excluded as a special case that the two domains of individuals 
may be the same, in which case the one-to-one correspondence required is some one-to- 
one correspondence of that domain of individuals on to itself. (We assume the term 
"one-to-one correspondence" to be familiar to the reader, but an explanation of it may 
be found, if needed, in footnotes 556, 564.)

---


330
FUNCTIONAL CALCULI OF SECOND ORDER [Chap. V
particular free variable occurring in the representing forms of the postulates 
always correspond to each other according to this one-to-one correspondence. 
I.e., if in the first model the value a is given to an individual variable a, 
and in the second model the value ar is given to a, then a must correspond to 
a' in the one-to-one correspondence between the two domains of individuals; 
and if in the first model the value 0  is given to an n-ary functional variable 
f, while in the second model the value 0 ' is given to f, then the propositional 
functions 0  and 0' must be so related that, whenever the individuals a^, at, 
. . 
an of the first domain of individuals correspond in order to the indi­
viduals av  a'a, . . dn of the second domain, the value 0 (av a2, . . 
a*)
is the same as the value 0 '{a'v dv .. 
dn).
Then a system of postulates is said to be categorical if all its models are 
isomorphic.
We leave to the reader the proof of the following metatheorems, which 
state some obvious connections among the three notions of completeness of 
a postulate system:
**554. 
Every system of postulates complete as to provability is complete 
as to consequences.
**555. 
Every categorical system of postulates is complete as to conse­
quences.
**556. 
If a categorical system of postulates has a model SK, then every 
system of postulates with the same undefined terms and the same 
underlying logic, if it is complete as to consequences and has the 
model SK, must be categorical.
Finally, before concluding this section, we have to consider one other way 
in which postulates are often used. Namely, instead of serving as basis for 
a special branch of mathematics, a system of postulates may be used in the 
course of the development of some more general mathematical theory, in 
the role of a definition of some particular kind of structure which is to be 
considered in the context of the more general theory.
As an illustration we may take the case of postulates for an integral 
domain.
One system of postulates for an integral domain may be obtained from 
the postulates (Ax) by omitting the postulate of mathematical induction, 
changing the fifth postulate to (3a:)Z,(a:f y, z), changing the twelfth postulate 
to (3a?) (3y) ~  . x =  y and adding the postulate xx =  x2 Z3 . F fo) Z3 F(*a). 
The fourth postulate then becomes non-independent and may be omitted.

---


§55]
POSTULATE THEORY
331
Thus, retaining the same definition schemata that were used in connection 
with (A0), we have the following system of twelve postulates, which we shall 
call (ID):
(3z)E{x, y, z)
2 (#!, x3, y x) 3  m2*(x2i x3, y2) z d  . 2 ( y 1( x 3, z ) z d  2 ( x x, y2> z )
2 ( x t y ,  z )  z d  2 ( y t x ,  z )
(3x)2;(x, y, z)
(3z)I7(x, y t z)
IJ{xv x2l y x) 
nll{xt) xz, y2) z d  ,TUyu x.it z )  z d  II (x u y2l z)
TI[x, y, z) z d  11 [y, z, z) 
n { x lt y,z) zd . I I (xit y, z )  z d Z 0 (y) v xt =  x2  
(3x)H(xt y,y)
IJ(x2, x2, y3) z d  m II[xXi x3, 2/3) ^  ■ 2 [x2l 
Vi) —^ ■ 2 {y2) y%, z) z d  FI(xt, ylt z)
(3a:) (3*/) ~ mx — y 
. 
x x —  x 2 z d  .  E [ x x) z d F ( x2)
When these postulates are used, not as basis for their own branch of 
mathematics, but in order to introduce in the context of a more general 
theory the term “integral domain/' or a notation serving the same purpose, 
they must be rewritten in the form of a definition schema. It would usually 
be necessary to be able to speak not only of the individuals as forming an 
integral domain with respect to a pair of operations (in the roles of addition 
and multiplication) but also of any class of individuals as forming an integral 
domain. Thus the definition schema must introduce a notation, say id(f,g, h), 
in which f and g are ternary functional variables and h is a singulary func­
tional variable.
And for values 0, 
and 0  of f, g, and h, it must be possible to understand 
id(f, g, h) as expressing that 0  is an integral domain with respect to 0  and 
in the usual sense of those words in informal treatments of algebra.
As derived from the particular system of postulates (ID), this definition 
schema for id(f,g, h) is the following: 5 4 3
B48The definiens has an evident relationship to the representing form of the con­
junction of the postulates (ID), but differs in several ways, in particular it has one 
more free functional variable. As here given, it does not parallel the postulates quite 
perfectly, some obvious simplifications by P and F 1 having bven made.

---


332
FUNCTIONAL CALCULI OF SECOND ORDER [Chap. V
D 24. 
id(f, g, h) -* h (x) =3X . h (y) =>„ . h(z) =3, . h (x ,) =>Xi . h (y ,) =Jt i . 
h (* j) =>X/ .h ( j / 2) = v a ■ h ( x 3) = > * ,. h fo 3) =3V j. (3z)[h (*)f(x, y, z)]
[f(*l, *2. Vi) => -*(*2. *3. Vt) => 
*3. 2) => *(*1.1/2. 2)] [f(*. V> 2) ^
f(3/. *. 2)] (3 x )[h (x )f(x , y, z)j (3 z )[h (z )g (x , 
*)] [g (x x, x „  f t)  =3 .
g ( * 2. * 3 . l/z) = 3  . g ( j / i .  * 3 . 2 ) => g ( * l .  ^ 2. 2 ) j  [ g ( * .  V- 2 ) = >  g ( 3/ . * .  * ) ]
[g(*i, ft  z) rj . g ( x !( 1/, z) =j . [h(z) =3, f(ft z, z)] v . h (x ) =3* . 
h (l/) =>v .i{x1,x ,y )  =3 f ( x a,x , j/)] ( 3 x )[ h ( x )g ( x , y, y)]
[ g ( * i .  * 2 . 1 /2 )  = >  ■ g ( * i .  * 3 . l / s )  = >  • f (* 2 . * 3 . ! / , )  = >  ■ f (2/ 2. ^ 3 . 2  ) = >
g (* i. Vi, 2)] ( 3 * ) ( 3 y ) ( 3 z ) ( 3 x 1) [ h ( x ) h (y ) h ( z )h (x 1)f(x, z, x ,) ~ f ( f t  z, x,)] 
. [h (x ) =>J: . h{y) =>v . f(x „  x, y) => f(x 2, x, y )j => . f  (Xj) Z3F F(xt)
In many informal treatments of abstract algebra in the literature, systems of 
postulates for a group, a ring, an integral domain, a field, etc. enter in this 
way—in the role not of axioms but of definitions which, in a corresponding 
formalized treatment, would appear as definition schemata analogous to D24. 
And the formalization of such a treatment of abstract algebra would then be 
a development within a pure functional calculus Of second order, say FJP, with 
perhaps the axiom of well-ordering of the individuals and an axiom of infinity 
(see §§56, 57), one or both, as added axioms. Or it may well be necessary for 
the sake of some parts of the development to use a functional calculus of 
higher order than the second—this will depend on just what the content 
of abstract algebra is conceived to be. In any case, abstract algebra is thus 
formalized within one of the pure functional calculi, and in this sense we may 
say if we like that it has been reduced to a branch of pure logic.
Many other branches of mathematics are customarily treated in a similar 
way, so that their formalization brings them entirely within one of the pure 
functional calculi. And though it is more natural or more usual in some cases 
than others, it seems clear that every branch of mathematics might be treated 
in this way if we chose. For example, instead of deriving elementary number 
theory from the postulates (A,) in the role of axioms added to an underlying 
logic, we might transform these postulates into a definition of the term "an 
arithmetic" (in the formalized treatment, a definition schema), and then re­
state and re-prove all the usual theorems of elementary number theory as general 
theorems about "an arithmetic. ”
844 * * * 848
Thus it is possible to say that all of mathematics is reducible to pure logic, 
and to maintain that logic and mathematics should be characterized, not as 
different subjects, but as elementary and advanced parts of the same subject. 8 4 1
844As long as it is desired only to reproduce (in this sense) the theorems of A1 within
F)p no added axioms are necessary. Also the theorem expressing that there exist at most
one arithmetic (to within a one-to-one correspondence) requires no added axioms. But
for some other theorems, in particular for the theorem expressing that there exist at 
least one arithmetic, an axiom of infinity and perhaps also the axiom of well-ordering 
of the individuals will be necessary.
848There is also another sense (that of Frege and Russell) in which it is often main­
tained th at mathematics is reducible to logic. This is reserved for discussion in a later 
section. But in the meantime it should be remarked that the issue is a t least partly one

---


§55]
EXERCISES 55
333
EXERCISES ss
5 5 .O, 
Extend the principles of duality, *372-*374, to a logistic system 
obtained by adding arbitrary postulates to an applied functional calculus 
of second order as underlying logic. Carry out the proof in such a way as 
to include as a special case a proof of the principles of duality for the pure 
functional calculus of second order.
I . Prove the following as theorems of the logistic system A0 without 
making use of any of the postulates (A„) (thus also as theorems of Flh):
(1) 
% ~  x
(2) 
a: =  </=> . y  ~  z => J x =  z
(3) 
x =  y => . Z0(x) =3 Z0(y)
Prove the following as theorems of the logistic system A0, using 
only the first four of the postulates (A0):
(1) 
Z0{x) =j . Z0(y) =>. x =  y
(2) 
E(x, y, zt) =J . E(x, y, z2) => . zx =
(3) 
x =  y=3 . y  =  x
SS»3* Prove the following (in order) as theorems of the logistic system A0, 
using only the first five of the postulates (A0):
(1) 
(3x)Z0(x)
(2) 
z: =  z2 =j .E(x, y, z2) =j E[x, y, z,)
55-4- With the aid of the results of preceding exercises (if needed), prove 
the following as a theorem of A0, using only the first nine of the postu­
lates (A0):
17(x, y, Zl) =5 -77(*, y, z2) 
*zt =  z2
55*5* With the aid of the results of preceding exercises, prove the follow­
ing as theorems of A0, using only the first eleven of the postulates (A0);
(1) 
Z ,(y )= >  I7(x,y,y)
(2) 
z, =  z2 
. 77(x, y, z2) =j 77(x, y, *,)
(3) 
Vi =  y s => . 77(*, y2, 2) =5 77(x, y1: z)
(4) 
Z0(z) 
,77(x, y, z) => Z0(x) v Z0(y)
(5) 
(3x)Z1(x)
of decision as to terminology. It is also possible to hold, for example, that an axiom of 
infinity is outside the province of logic, and that logic ends and mathematics begins 
as soon as such an axiom is added.

---


334
FUNCTIONAL CALCULI OF SECOND ORDER [Chap. V
55-6. Prove the following theorems of the logistic system which is ob­
tained by adding the first eleven of the postulates (ID) to Flh as underlying
logic:
(1) 
E{x, y, zj) => . E(x, y, z2) =>. z, =  z2
(2) 
-T(*x,y, z) =j .E {xv y, z) =>.% =  x9
(3) 
Z0(x) =j . ^i(y) =><*■■* =  y
55-7- Show that every theorem of A1 which contains no functional vari­
ables is also a theorem of A0.
55-8. In the system of pustulates (A1)> establish the independence of the 
seventh postulate (the associative law of multiplication) by means of the 
following independence example. The individuals are the four natural num­
bers 0( 1, 2, 3, and addition and multiplication are as given in the following 
tables:
4- 0
1
2
3
0
0
1
2
3
1
l
0
3
2
2
2
3
0
1
3
3
2
1
0
X 0
1
2
3
0
0
0
0
0
1
0
3
2
2
0
3
2
1
3
0
2
1
3
(I.e., more explicitly, in the representing forms of the postulates the func­
tional variables corresponding to 27 and 11 are F 3 and Hz respectively; and 
in the model which constitutes the independence example, the value of 
F® is the propositional function 0  such that <P(a, bt c) is t if and only if 
a -h b =  c according to the first of the above tables, and the value of IP 
is the propositional function W such that W(at b, c) is t if and only if a X b =  c 
according to the second of the above tables.)
55-9* In the system of postulates (AJ, establish the independence of the 
eighth postulate (the commutative law of multiplication) by means of the 
following independence example. The individuals are 0 and all the complex 
numbers a +  pi in which a and p are positive rational numbers. The sum 
is taken in the usual way. A product is 0 if either factor is 0, and otherwise 
(a 4- pi) X (y +  di) =  ay -f- pyi (the products ay and Py being taken in 
the usual way).
55 -10. Establish the independence of the remaining postulates of (Aj) 
by means of independence examples.
55-11- Establish the independence of the postulates of (ID) by means 
of independence examples.

---


§55]
EXERCISES 5.5
335
55«I2« Express by means of a wff of A1 that the only ternary relation, 
among natural numbers a, b, c, that satisfies the second pair of recursion equa­
tions of footnote 526 and the further condition that c is uniquely determined 
when a and b are given is the ternary relation 0 such that 0 {a, b, c) holds when 
and only when a X b —- c (in the sense that any ternary relation among natural 
numbers satisfying the two recursion equations and the further condition is 
formally equivalent to 0 ).
5 5 -I3 - Prove the wff of the preceding exercise as a theorem of A1. 
(Make use of the postulate of mathematical induction.)
5 5 . 1 4 . For A1, suppose that the signs 0 and 1 are introduced by contex­
tual definition, according to the following definition schema, Of the signs 
alf a2, . . ,, aT1, let some (possibly) be 0’s, let others (possibly) be l's, and let 
the remainder be individual variables (not necessarily all different); let f 
be any w-ary functional variable or functional constant, let x and y be the 
first two (distinct) individual variables in alphabetic order that do not occur 
among alf a2, . . 
a„, and let b v b2, , . b„ be obtained from alt a2, . . an by
replacing the sign 0 everywhere by x and the sign 1 everywhere by y; then
f(a,, a2----- - a j  
(3x)(3y)[20(x)Z,(y)f(b1, b2........b j].
For expressions which abbreviate wffs of A1 according to this definition 
schema, establish as a derived rule a rule of substitution for individual 
variables, allowing to be substituted for an individual variable not only 
another individual variable but also one of the signs U. I.046
5 5 . 1 5 , Prove that the system of pustulates (A j is categorical. {Sugges­
tion: In one model let 0  and 0  be the values of the functional variables 
that correspond to 27 and FI respectively, and in a second model let &' and 
!P' be the values of the functional variables that correspond to 27 and f l  re­
spectively. In the first domain of individuals there must be two unique 
individuals 0 and 1, distinct from each other, such that 0 (0, b, b) and 
¥*(1, b, b) hold for all individuals b of the domain. In the second domain of 
individuals there must be two unique individuals 0 ' and 1', distinct from 
each other, such that 0'(O', b, b) and 
b, b) hold for all individuals
b of the domain. The required one-to-one correspondence between the two 
domains is that in which 0 corresponds to O', and 1 corresponds to 1', and
“ •Compare footnote 528.
This definition schema may be thought of as a modified form of a special case of 
Russell's contextual definition of descriptions, i.e., of his schema for contextual def­
inition of the notation (?*)A; see the American Journal of Mathematics, vol. 30 (1908), 
p. 253. In this special case, following the remark of Herbrand in Comptes Rendus des 
Stances de la Sociiti des Sciences et des Lettrcs de Varsovie, Classe III, vol. 24 (1931). 
p. 33, we are able to simplify the definitions {contained in the schema) by taking ad­
vantage of the theorems, Zq{x) id . Z9(y) 
=  y and 
id ■ Zl(y) id x =  y, of A1.

---


336
FUNCTIONAL CALCULI OF SECOND ORDER [Chap. V
whenever a corresponds to a*, and 
1, c) and <P'(a'r V, e') hold in the 
respective domains, then c corresponds to c'. The proof proceeds in the meta­
language by the method of mathematical induction.)
5 5-»6 . Hence show that the postulates (A0) with Flh as underlying logic 
are complete as to consequences.
5 5 .* 7 . Show that the postulates (A0) are not categorical because, besides 
the obvious model with the natural numbers as the individuals, there is also 
the following model. The individuals are the positive and negative integers 
and 0, The value of the functional variable corresponding to £  is the ter­
nary relation that holds among a, b, c if and only if \a\ +  |6[ — |e|. And the 
value of the functional variable corresponding to 77 is the ternary relation 
that holds among a, b, c if and only if Jab\ =  |cj.
The non-categoricalnessof the postulates (A0) as established in the 
preceding exercise may be thought to be of relatively trivial character, 
since there does exist a one-many correspondence between the domains of 
individuals of the two models such that the values of the functional variables 
corresponding to £, and to IT, in the two models correspond to each other 
according to the one-many correspondence. The second model could more­
over be excluded by taking an appropriate simple applied functional cal­
culus of first order with equality as underlying logic, and replacing "xx =  x%n 
in the fourth and ninth postulates by 'T(xx, ar2)'\ Let the system of postu­
lates so obtained from (A0) be called (A;), and let the logistic system ob­
tained by adding them to the appropriate simple applied functional calculus 
of first order with equality be called A1. (1) Show that the postulates (Af) 
are complete as to consequences. (2) By means of the metatheorems of 
exercise 48.22, establish the non-categoricalness of (A/), and hence also the 
non-categoricalness of (A0) in a less trivial sense.547
SS* *9 * 
V be a binary functional constant, and consider the system of 
postulates consisting of the single postulate (z)(y)V(a;, y), added to a simple 
applied functional calculus of first order, having V as its one functional 
constant, as underlying logic. Show that this system of postulates is complete 
as to consequences but not categorical.
5 §02 O0 Show that in every model of the following system of postulates 
the domain of individuals is finite, but that there exist models with an arbi­
trarily large finite domain of individuals. There is one undefined term, a 
binary functional constant S . The underlying logic is an applied functional
MTThis is a special case of the result of Skolem stated in footnote 462. His proof, by 
a different method from that suggested here, is given in Fundament a Malhematica#, 
vol. 23 (1034), pp. 150-101.

---


§55]
EXERCISES 55
337
calculus of first order with equality, having among its primitive symbols 
all propositional and functional variables, and S as its one functional 
constant. The postulates are:
S(x, y) ZD . S(x, z) zd - y =  z 
F(x) =j . F(y) =}„ [S(y, z) ra, F(z)] => (y)F(y)
5 g ,S I, To the postulates of the preceding exercise let the following in­
finite list of postulates be added:
(3y}S{x, y)
S{xv x2) z d. xx 4= x2
S ( X Xg) ID * *S(X2, X3) D  ■ Tj ^  ^3
S(xv xz) ^  ■ S(x2» x3) ^  ■ S(x3, x^) ^  ■ Xj
S(Xjl, x2) id ■ 
xa) id ■ Sixa, Xj) id . S(xit x5) zd a xl 4s *^5
Show that the resulting system of postulates is consistent as to provability 
but not consistent as to consequences.548
5 5 .2 3 , The following are inform ally stated postulates for partial order, w ith 
a relation precedes as the one undefined te rm :649
No individual precedes itself.
If a precedes b and b precedes c, then a precedes c.
From  these a system  of postulates for simple order is obtained by adding the 
following th ird  p o stu late :460 * 640
644This is an adaptation of an example due to Tarski—see Monatshefle fur Mathe- 
matih und Pkysih, vol. 40 (1933), pp. 97-112. By making use of the Gddel incomplete­
ness theorems (to be treated in a later chapter), it is also possible to find a finite 
system of postulates which is consistent as to provability without being consistent as 
to consequences.
M9The name "partially ordered class" is taken from the German "teilweise geordnete 
Menge" of Felix Hausdorffs Grundziige der Mcngenlekre (Leipzig, 1914), p. 139. where 
the general notion of partial order (as distinguished from the treatment of particular 
cases of it) seems to have been first introduced.
640This definition of simple order should perhaps be credited to C. S. Peirce, who. 
in the American Journal of Mathematics, vol. 4 (1881). p. 86, gives a closely related 
definition, in terms of a relation analogous to ^  (rather than to < as in the exercise 
above).
A definition of simple order in term s of the relation precedes (analogous to < ) is 
given by Const. Gutberlet in the Zeilschrift fur Philosophic und Pkilosophische Kritik, 
new series, vol. 88 (1886), pp. 183-184. The same definition is used also by Georg 
Cantor in the Mathematiscke Annalcn, vol. 46 (1895), p. 496 (or see his Gesammellt 
Abkandlungen, p. 296); and it is probable that Gutberlet may have taken the definition 
from a manuscript of Cantor (see Gesammellc Abkandlungen, pp. 388. 482-483). though 
his own statem ent about the m atter is not entirely clear. Both Gutberlet and Cantor 
state explicitly only the last two of the three postulates given above, but the additional 
condition th at no element precedes itself is tacitly intended, at least by Cantor, as is

---


338
FUNCTIONAL CALCULI OF SECOND ORDER 
[Ch a p, V
If a and b are any two different individuals, either a precedes b or b precedes a.
From  these in turn a system  of postulates for well-ordering is obtained by 
adding th e fourth postulate:251
In any non-em pty class of individuals there is a first individual, i.e., an in­
dividual th a t precedes all the others in the class.
(1) 
W ith a binary functional constant R denoting the relation of preceding, 
restate these postulates in the n o tatio n  of an appropriate functional calculus of 
first order. (2) Hence, by the m ethod which is used in th e te x t to transform  the 
postulates (ID) into the definition schem a D24 for id(f, g, h), find expressions 
for each of the following, in th e notation of the pure functional calculus of 
second order: the class 
(of individuals) is partially ordered by the relation 0; the 
class 
is simply ordered by the relation 0', the class \F is well-ordered by the 
relation 0.
5S-*3. In the case of each of the following system s of postulates found in the 
literature, restate the postulates in the notation of an appropriate functional 
calculus (of not higher than second order), using the indicated functional con­
stants as th e undefined term s:
(1) P ostulates for Euclidean plane geom etry. Veblen and Young, Projective 
Geometry, Volum e 2, §66, pp, 144-146. O, denoting the ternary relation among 
A, B.C, th a t A, B,C are in the order {ABC}', C, denoting the quaternary re­
lation am ong A, B, C, D, th a t AB is congruent to CD. (Omit the continuity 
postulate, X V II. In stating the postulate XVI, use m ay be m ade of the postu­
lates (A2), as they are stated above, but modified as required, in particular by 
replacing th e functional constant S by a binary functional variable.)
(2) T he sam e postulates w ith the following continuity postulate added: If K 
is a non-em pty class of points of a line a, if B and C are points of a such that 
every point A' of K is in the order {ArBC), there is a point A of a such that 
every point X  of K distinct from A is in the order {XA C}, an d  no point Z of a in 
the order {ZAC} has the property th a t every point X  of K  is in the order {XZC}.
(3) P ostulates for (real) projective plane geom etry. H . S. M. Coxeter, The 
Real Projective Plane, 2.21-2.25 (p. 12), 3.11-3.16 (p. 22), and 10.11 (p. 138). 
P, denoting th e class of points; L, denoting the class of lines; I, denoting the
clear from M u tk e m a tisc h e  A n n u le n , vol. 49 (1897), p. 216 (or G esa m m elte A b h a n d lu n g e n ,
P- 321).
The condition that no element precedes itself is of course replaceable by the 
condition that not both x  precedes y  and y  precedes x . In this form the three 
postulates are given explicitly by B. I. Gilman (a student of Peirce) in M in d , 
n.s., vol. 1 (1892), pp. 518-526; and by Giovanni Vailati in R iv is ta  d i M a te m a tic a , 
vol. 2 (1892). p. 73.
M1The notion of a well-ordered class is due to Georg Cantor in G ru n d la g en  ein er 
A llg e m e m e n  M a n m g fa ltig k e its le h r e, Leipzig, 1883, p. 4 (or M a tk e m a tisc h c  A n n a le n , 
vol, 21 (1883), p. 548, or A c ta  M u th e m a tic a , vol. 2 (1883), p. 393, or G esa m m elte A b ­
h a n d lu n g en , p. 168). Cantor's definition of well-ordering is somewhat different from, 
but equivalent to, what is now the usual definition by means of the fourth pos­
tulate above. Moreover Cantor at first merely presupposed the notion of simple 
order in giving the definition of well-ordering. But a definition of simple order was 
supplied in 1895, as explained in the preceding footnote.

---


§55]
EXERCISES 5 5
339
relation of incidence; S, denoting the q u atern ary  relation of sep aratio n .” 1
(4) P ostulates for E uclidean three-dim ensional geom etry. D avid H ilbert, 
Grundlagen der Geometric, seventh edition (1930). $51-8. U, C, P. L, and 1 as in 
parts (1) and (3). n, denoting the class of planes; i, demoting the relation wf 
incidence between points and planes; K, denoting the senary relation am ong 
A, B, C, A ', B r, C', th a t the angle ADC is congruent to the angle A 'B 'C '. 
Special atten tio n  m ust be given to the postulate of linear com pleteness ("A xiom  
der linearen V ollstandigkeit'’), whose expression in the notation of a functional 
calculus of no higher th an  second order offers some difficulty, and of w hich some 
restatem ent or m odification m ay be necessary in order to render such expression 
possible,
(5) P ostulates for (real) projective three-dim ensional geometry, M ario Pieri, 
Memorie della Reale Accademia delle Science di Torino, ser. 2 vol. 48 (1899), 
pp. 1-56. J, denoting the tern a ry  relation am ong a, b, c, th a t c is on the straig h t 
line joining a and b.
(6) E . V. H untington's postulates 1-14 for "th e  theory of real q u an tities," 
Transactions of the A m erican M athem atical Society, vol, 4 (1903), pp, 358-370,
(7) C hurch's postulates for " th e  second ordinal class," or second num ber class, 
of C antor, Transactions of the American M athem atical Societyt vol. 29 (1927). 
p. 179.
(8) A. L indenbaum 's postulates for a m etric space,553 Tundam enta Malhc- 
maticae, vol. 8 (1926), p. 211; given also bv C. K uratow ski, Topofogie I. first 
edition (1933), pp. 82-83, or second edition ^ IU4S;, p. 99. '.bur tin- introduction 
of the notion of real num ber, m ake use of the postulates of part (6 ; of tins 
exercise, or of some other system  of postulates serving the sam e purpose.)
(9) P ostulates for a com plete space,553 obtained from the foregoing by adding 
the p o stu late th a t is given by  K uratow ski, Topoiogic f , first edition, p. 196, or 
second edition, p. 312.
5 5 - 2 4 -  ln  a many-soried functional calculus™* (of first or higher o u le i) them  
are individual variables of m ori than one sort, the different sorts being d istin ­
guished by superscripts, and an infinite list of individual variables of each soil 
being available. Say in an w-sorted functional calculus the in d iu d u al variables 
of the first sort are xl, y l, zl, x\, . . , ; those of the second so n  are .r2, y z, zz, 
. . . ; 
and so on, up to x n, y n, z n, x\, , . . as individual variables of the nth sort. There * 563
B5,As in part (1 ), the notion of an infinite sequ'ihc of individuals which enters m 
these postulates may be provided for b, making use of the postulates (Aa) appro­
priately modified. (Compare the procedure m the text m transforming the postulates 
(ID) for an integral domain into a propositional form with three iree variables, express­
ing that a class is an integral domain with respect to two ternary relations.)
563The notion of a metric space and that of a complete (or complete metric) space 
are due to Maurice l-’rechet, though in a different terminology. Sen Ins thesis in the 
Rendiconti del Circolo Matematico di Palermo, vol. 22 (1906), pp. 1-74, and a paper m 
the Transactions of the American Mathematical Society, vol. 19 (1918), pp. 53-65.
B55See a paper by Arnold Schmidt in the Mathematische Annalen, vol. 115 (1938), 
pp. 485-506. (Added in proof. See also improved treatm ents of the same topic by Arnold 
Schmidt in the Mathematische Annalen, vol. 123 (1951), pp. 187-200, and by Hao 
Wang in The Journal of Symbotic 
, vol. 17 (1952), pp. 105-116.)

---


340
FUNCTIONAL CALCULI OF SECOND ORDER [Chap. V
are (or m ay be) then n sorts of singulary functional variables, again distinguished 
by superscripts, an infinite list of each sort; thus F 1, G1, H l, F \, . . .  as singulary 
functional variables of the first sort, F \  Ga, H*t F j, . . . as singulary functional 
variables of th e second sort, and so on. And where a  is an individual variable 
and f is a singulary functional variable, f (a) is wf if and only if f and a  are of the 
same sort. T here are {or m ay be) n a sorts of binary functional variables, distin­
guished by superscripts thus: F 1-1, Gl>l, H 1-1, F}*1, . . . ; F 1-3, G1>3t H 1-2, F j-2; and 
so on. And, for example, F a>I(a1, a 2) is wf if and only if a x is an individual 
variable of the second sort and a 2 is an individual variable of the first sort. 
Sim ilarly there are (or m ay be) w3 sorts of ternary functional variables, and so on.
For the principal interpretation of an n-sorted functional calculus, there must 
be a non-em pty dom ain of individuals of the first sort, w hich is the range of the 
individual variables of the first sort; a non-em pty dom ain of individuals of the 
second sort, w hich is the range of th e individual variables of the second sort; 
and so on (« dom ains of individuals altogether). The various functional variables 
then have ranges consisting of propositional functions in a w ay which will be 
obvious by analogy w ith the principal interpretations already given (in Chapters 
III and V) for the one-sorted functional calculi of first and second order.
For an applied (as distinguished from  a pure) n-sorted functional calculus there 
m ay also be individual and functional constants, each of w hich m ust belong to 
a particular sort in the sam e w ay as the individual and functional variables.
Taking th e rem aining prim itive sym bols to be the eight im proper symbols 
listed a t the beginning of §30, we m ay use for an w-sorted functional calculus of 
first order th e form ation rules of §30, except th a t 30ii is modified in the way 
indicated in th e first paragraph of this exercise; the rules of inference and axiom 
schem ata m ay then be the sam e as in §30, except th a t to *306 th e requirem ent is 
added th a t b  m ust be of the sam e so rt as a. An w-sorted functional calculus of 
second order m ay be form ulated sim ilarly, with appropriate provision added for 
quantification of functional variables.
(1) S tate in full a prim itive basis for an n-sorted functional calculus of second 
order, as closely as possible analogous to the prim itive basis for F j given in §50, 
For a fixed kt show th a t those theorem s of the system  w hich contain individual 
variables of only the Ath sort are (ap art from trivial no tatio n al differences) the 
same as the theorem s of Fj.
(2) W ith a tw o-sorted functional calculus of second order as underlying logic, 
taking the individuals of the first sort to be the points, and the individuals of the 
second sort to be the lines, and taking as undefined term s a binary functional 
constant T denoting the relation of incidence and a q u atern ary  functional con­
stan t S denoting the relation of separation, state C oxeter's postulates for pro­
jective piane geom etry (see 55.23(3)) in this notation.
(3) Sim ilarly, state H ilbert's postulates for Euclidean three-dim ensional ge­
om etry (see 55.23(4)), with a three-sorted functional calculus of second order as 
underlying logic, the three sorts of individuals being the points, the lines, the 
planes.
(4) Sim ilarly, state the postulates for a m etric space (55.23(8)) with a two- 
sorted functional calculus of second order as underlying logic, the tw o sorts of 
individuals being the points of the space and the real num bers.

---


§56]
WELL-ORDERING OF THE INDIVIDUALS
341
(5) 
T he logistic system  of p a rt (2) of this exercise (i.e., the logistic system  
obtained b y  adding the indicated postulates to  the underlying logic) is in an 
appropriate sense equivalent to th e logistic system  of 55,23(3). In  a like sense, 
the logistic system  of p a rt (3) is equivalent to th a t of 55.23(4), and the logistic 
system  of p a rt (4) is equivalent to  th a t of 55.23(8). E xplain in w hat sense the 
equivalence holds. And sta te  an d  prove a general m etatheorem  establishing th e 
appropriate equivalence in all such cases. (C/. th e papers of footnote 554.)
56. Well-ordering of the individuals. Returning to consideration of 
the pure functional calculus of second order Fjp, we now take up the question 
of axioms expressible in the notation of the pure functional calculus of 
second order, alone, which—for some purposes or in some connections—it 
may be desirable to adjoin to 
as additional axioms.
One such axiom , the possible addition of w hich to F ap we shall wish to con­
sider, is an axiom  to th e effect th a t the individuals can be well-ordered.
In  order to express this, we m a y  m ake use of th e definition of well-ordering 
which was given in 55.22, w riting the conjunction of the universal closures of 
the four postulates of 55.22, replacing the undefined term  "precedes" everyw here 
by th e functional variable F a, an d  then prefixing th e  existential quantifier 
(3Fa) to th is conjunction. T he resulting expression m ay  be simplified, however, 
by om itting the third postulate, w hich can be shown to be non-independent. 
Thus we o b tain  the axiom  (w) w hich is w ritten below.
The axiom s of choice are reserved for discussion id connection w ith the func­
tional calculi of higher order, although certain special cases of an axiom  of choice 
can be sta te d  already in the n o tatio n  of the functional calculus of second order 
and sum m arized in an axiom  schem a.566 W e an ticip ate this discussion here so 
far as to say th a t it will follow, from  th e axiom s of choice, not only th a t th e in d i­
viduals can be well-ordered b u t also various higher dom ains— in particular th a t 
the singulary propositional functions (classes) of individuals can be well- 
ordered, th e binary propositional functions of individuals, and so on— and con­
versely th a t the axiom s of choice will follow from  such assum ptions of well- 
ordering.
H ow ever, our present axiom  (w) m ust not be considered as representing a 
special case or a weak form  of an  axiom  of choice. For the effect when we add 
it as an axiom  to F*p is ju st th a t we restrict th e  in terp retatio n  to such dom ains 
of individuals as are capable of being well-ordered, a procedure which should 
be acceptable even to those w ho d istru st or prefer not to assume any axiom  of 
choice. 6
666The axiom schema in question is
(x)(3f)A =3 (3g)(x)$ f(Xj, Xj, ..., X,)}
a ;
g(x, xltxt,
where x, x lt x a, . . x„ are distinct individual variables, f is an n-arv functional variable, 
g is an (n -f l)-ary functional variable, and A is a wff containing no bound occurrences 
of either g or x. It is given by H ilbert and Ackermann, G ru n d ziig e d er th eo retisch en  
L o g ik , second edition (1938), p. 104, and third edition (1949), p. Ill; also in the paper 
of Ackermann mentioned in the last paragraph of footnote 507.

---


342
FUNCTIONAL CALCULI OF SECOND ORDER 
[Chap. V
Thus the following axiom of well-ordering of the individuals—or axiom 
(w), as we shall also call it—is to be considered as a possible added axiom:
(3F) . {x)—F[x, x) . F{x, y) 
[F{y, z) 
F(x, *)] .
=>Gx $ y ) ■ G{y) ■ G(z) 
F{y, z ) v y  =  z 
Following a method of naming that we adopt as systematic, we call the 
resulting logistic system 
when the axiom (w) is added to the logistic
system Fi|p.
EXERCISES 56
56.O. 
Restate (w) as an equivalent axiom in prenex normal form, with 
only four different individual variables, one singulary functional variable, 
and one binary functional variable.
5 6 -1* Prove the statement made in the text that the third of the four 
postulates for well-ordering (55.22) is non-independent.
56.2. State and prove as a theorem of FJD(wJ that the individuals can be 
simply ordered. (Use the definition of simple order given in 55.22.)
5 6 .3 . It follows from axiom (w) that every relation between individuals 
has a many-one subrelation with the same domain.888 Expressed in the notation 
of the functional calculus of second order, this is:8M
(3G) . G(zt z) 
Fix, z) . F{z, z) 3 ^ (3^) . G{x, z) =st ;r =
Prove this as a theorem of F2P[w).
56.4. Prove the same theorem in the logistic system that is obtained by 
adding to F|p the axiom schema of footnote 555.
57. Axiom  of infinity. A wff of one of the functional calculi may be 
considered as an axiom of infinity if it is valid in at least one infinite domain 
of individuals but is not valid in any finite domain of individuals.
Of the pure functional calculus of first order with equality, and therefore 
also of the pure functional calculus of first order, there is in fact no wff 6
6660ne relation is said to be a subrelation of a second one if it formally implies the 
second one, in the sense of formal implication explained in §06. A relation R is said to 
be many-one if for every member a of the domain of R there is a unique corresponding 
member b of the converse domain of R such that a bears the relation R to 6. Moreover 
a relation is said to be one-many if its converse is many-one; and one-to-one if both it 
and its converse are many-one. (See further the explanation of terminology in footnote 
517.)
“ ’Compare Hilbert and Ackermann, Grundziige der Theoretischen Logik, second 
edition (1938), formula g on page 104, and third edition (1949), formula g on page 111.

---


§57]
AXIOM OF INFINITY
343
which may thus he considered an axiom of infinity.**8 Therefore the various 
axioms of infinity which we discuss in this section are wffs only of the pure 
functional calculus of second order.559
An effect of adjoining an axiom  of infinity to F 2p as additional axiom  is of 
course to restrict the interpretation to domains of individuals which are infinite. 
We prefer to take an axiom of infinity which imposes no great further restriction 
on the interpretation, beyond th e exclusion of finite dom ains of individuals.R8° 
Consider for example the wff w hich results when we w rite the conjunction of 
the universal closures of th e postulates (Aa) of §55, replace the functional con- 
stant 5  everyw here by the functional variable G8, and then prefix the existential 
quantifier ( 3 G a) to this conjunction. As an axiom  added to  F J P ( this wff would 
restrict th e dom ain of individuals not merely to be infinite but moreover to be 
enum erably infinite. This is too severe a restriction for w hat we regard as the 
purpose of an axiom  of infinity. B u t a more acceptable axiom  of infinity, nam ely
(oo3) (or (oo4)) below, m ay be obtained by treatin g  sim ilarly four (or three) 
of the five postulates (A,).
Of various alternative axioms of infinity which we might consider adjoin­
ing to Fap as additional axioms, we list here the five following, (ool)-(oc5):
(col) 
(3 i7) 
(a:2) (a:3) (3y) . F(xv x2) => 'F(xt, x3) => F[xv z.,)] .
~F{xv z,) Flxv y)
(002) 
(3/;')(z)(3v)(z) . F(z, x) r> F(z, y) 
x) F{x, y)
(003) 
(37-') . (z)(3 y)F{x, y) . F(x. y) ~3 
; / - V ,  ; )  = 3 2 y  =  7 
.
F{y, *) =>«» [F(z, x)= }t y =  z i .  (3x){y)~F{y, x)
M8For an axiom  of infinity that would be valid in an enum erably infinite dom ain of 
individuals, th is is a corollary of exercise 48.24. The same result can be obtained for an. 
axiom of infinity valid only in a non-enumerably infinite domain of individuals by 
making use of an axiom of choice in the meta-language and following the m ethod of 
exercise 48.22— as was done by Leon Hcnkin in his dissertation of 1947 and in the 
paper cited in footnote 465. (Compare further footnote 451.)
“ *There arc also axiom s of infinity which are wffs only of functional calculi of still 
higher order, in particular the “Infin ax" of Princ.ipia Mathernatica as it would be re­
produced in our notation, and the three axiom s of infinity that correspond to Tarski's 
definitions of finitencss I, II, III in Fvmdamenta Mathemaiicae, vol. 6 (1924), pp. 46, 93.
460It im m ediately suggests itself to introduce a more restricted notion of an axiom o/ 
infinity, defining an axiom of infinity (syntactically) as a w ff which is valid in every 
infinite dom ain but not in any finite domain. This might indeed be done in a suitable 
meta-language. B ut from the point of view  of justifying or explaining a preference for 
one proposed axiom  of infinity over another, the effect is less satisfactory than m ight 
have been expected. For under the more restricted notion of an axiom  of infinity the 
decision as to which of the wffs (o o l)-(o o 5 ) given below actually is to be classed as an 
axiom of infinity depends on w hat are taken as definitions of '‘infinite" and "finite" 
for the meta-language; and also on the axiom s of the (ultim ately formalized) m eta­
language, in particular on th e presence and the form of axiom s playing the role of axiom s 
of infinity and of choice. (Compare a sim ilar remark by M ostowski, Comptes rendus des 
Stances de la Sociiti des Sciences et des Lettres de Varsovie, Classe 111, vol. 31 (1938), p. 16.)

---


344
FUNCTIONAL CALCULI OF SECOND ORDER [Chap. V
(go4) 
(3F) . (z)(3y)I<'(a;, y) . F{yt x) ^ xg [F{zt x) =>z y =  z] .
(3x)(y)~F(y, x)
(co5) 
-(3 G )(i7) . G[x, y) 
[G(x, z)^>£y =  z] . F{x) =>x ■
*'(y) =>v [ G { y ,  z) zdz F{z)]=> (y)F(y)
Of these, (ool) has an obvious relationship to the example of Bemays 
and Schonfinkel of a wff of the pure functional calculus of first order which 
is satisfiable in an infinite domain of individuals but not in any finite 
domains;561 (oo2), to Schiitte's example of such a wff of the pure functional 
calculus of first order;562 (oc3) and (004), to the Peano postulates, (Az); 
and (oo5), to the postulates of exercise 55.20.683
(oo3) expresses the existence of a one-to-one correspondence betw een the in­
dividuals and a proper subclass of th e individuals.*84 Therefore it m ay also be 
thought of as derived from the Peirce-D edekind definition of an infinite class as 
one having a one-to-one correspondence w ith a proper subclass.*8*
(co4) expresses the existence of a one-m any correspondence of the individuals 
to a proper subclass of the individuals, and thus represents a m odified form of the 
Peirce-D edekind definition of an infinite class.
It is not to be expected that these and other axioms of infinity which we 
might consider will turn out all to be equivalent to one another in the sense 
that the (material) equivalence of any two of them is a theorem of Fjp.
In fact, let B be called weaker than A if A d  B is a theorem of F |p but
*81In die paper cited in footnote 481. Compare also exercise 43.5(2).
**aIn his paper cited in footnote 430. Compare also exercise 43.5(1).
*63The axiom (ao5) of the writer's monograph of 1944 has here been simplified is 
accordance with a suggestion made by Paul Bemays in a letter of August 31, 1945. 
The idea of the axiom, that the individuals cannot be arranged in a closed cyclic order, 
is taken from Dedekind's second definition of finiteness, which was given in the preface 
to the second edition (1893) of his W a s S in d  u n d  w a s S o lle n  d ie  Z a h le n ? , and concerning 
which see further §7 of a paper by Alfred Tarski in F u n d a m e n ta  M a th e m a tic a e , vol. 6 
(1924), pp. 83-93, and a paper by Jean CavaillSs, ibid, vol. 19 (1932), pp.143-148.
8840 ne class is said to be a sub cla ss of a second one if all its members are members of 
the second one (compare footnote 556); and if in addition there is a t least one member 
of the second class which is not a member of the first class, then the first class is said 
to be a p ro p e r su b c la ss of the second one. By a one-to-one co rresp o n d en ce between two 
classes is meant a one-to-one relation, in the sense of footnote 556, having one class as 
its domain and the other class as its converse domain. (These are terms familiar in 
mathematical writing generally, such as we have often assumed to be known to the 
reader without the need for special explanation. In particular, the notion of a one-to one 
correspondence has been used in ** *439 and its proof and in the definition of categorical­
ness in §65, the notions of many-one and one-many correspondence in §23 and in 65.18.)
***C. S. Peirce, A m e r ic a n  J o u r n a l o f M a th e m a tic s , vol. 7 (1885), p. 202; Richard 
Dedekind, W a s S i n d  u n d  w as S o llen  d ie  Z a h le n ?  (1888), paragraph 64. As Dedekind 
points out in the preface to his second edition, the one-to-one correspondence of an 
infinite class to a proper subclass was first exhibited by Bernard Bolzano in his P a ra • 
d o x ie n  des U n e n d lic k e n  (1851) and was known also to Cantor in 1878, but neither of 
these authors has the proposal to make this the definition of an infinite class.

---


§57]
EXERCISES 5 7
345
B ZD A is not a theorem of Fgp. Then according to a result due to Andrzej 
Mostowski588 and B. A. Trachtenbrot,887 there is no weakest axiom of in­
finity, i.e„ more exactly, given any axiom of infinity, there exists a weaker 
axiom of infinity,588
As regards the particular axioms of infinity, (ool)-(oo5), some of the im­
plications and equivalences which hold among them are indicated in the 
following exercises (together with similar considerations concerning a few 
additional axioms of infinity introduced in the exercises). These are stated 
in each case in the form that a particular axiom of infinity is a theorem of 
the logistic system obtained from Fjp by adding one of the other axioms of 
infinity, with or without also the axiom of well-ordering of the individuals. 
But in view of the deduction theorem, they could also be put (without im­
portant difference) in the form that certain implications and equivalences 
are theorems of FgP
EXERCISES 5 7
5 7.0. Restate (oo5) as an equivalent axiom in prenex normal form, with 
no free variables, and with the shortest prefix that can be obtained by use of 
propositional calculus and elementary laws of quantifiers in a straight­
forward process of reduction.
5 7.1. According to the result just stated (without proof) in the text, if 
A is any axiom of infinity there exists an axiom of infinity B such that A ^  B 
but not B d  A is a theorem of F\p. Assuming this, show that, if A is any 
axiom of infinity, there exists an axiom of infinity B such that A d B bin 
not B zd A is a theorem of
57-». Restate in the notation of F*p (as closely as possible) the following 
informally stated axioms of infinity:
(006) 
There is a subclass of the individuals isomorphic to the natural numbers 
as given by the Peano postulates.
iMComptes Rendus des Stances de la Sociele des Sciences el des Let (res de Varsovie, 
Classe III, vol. 31 (1938), pp. 13-20.
™Dohlady Akadimii Nauk SSSR, vol. 70 (19r>0), pp. 569-572.
•••Both M ostowski and T rachtenbrot deal with logistic system s different from F | p, 
and they treat directly the question of a strongest definition of iiniteness (of a class) 
rather than th at of a w eakest axiom  of infinity. The result stated in the text is thus 
not explicitly contained in their papers but must be inferred from them. Botli papers 
are moreover abstracts in which proofs are not given of the results announced, but w hat 
are perhaps sufficient indications to m ake possible a reconstruction of the proofs are 
given in Trachtenbrot's paper and in M ostowski's review of it in The Journal of Symbolic 
Logic, vol. 15 (1950), p 229.

---


346
FUNCTIONAL CALCULI OF SECOND ORDER [Chap* V
(oo7) If the individuals can be sim ply ordered, they can be p u t into a simple 
order in which there is no last individual,8"
(oC'8 ) There exists a one-many correspondence of a class of individuals to 
itself th a t is not a one-to-one correspondence of th a t class of individuals to itself.
(oo9) The individuals cannot be sim ply ordered in such a w ay th a t in every 
non-em pty class of individuals there is both a first individual and a last individ­
ual.670
(oo 10) There exist a t least two different individuals, and th ere exists a one- 
lnany correspondence of the ordered pairs of individuals to the individuals.8,1 
{Suggestion: A correspondence between th e ordered pairs of individuals and the 
individuals m ay be thought of as a tern a ry  propositional function and thus rep­
resented by a tern ary  functional variable,)
S7-3- Prove each of the following as a theorem of Fjptc08j: (006); 
(ccl); (oc2); (coo).
57-4* * Prove (co3) as a theorem of F ^ * 1*004*.
5 7 .5 . (1) Prove (oo9) as theorem of F |ptc0B). (2) Prove (co5) as a theorem 
of F*p(=09>.
5 7 .6 , Prove (oo3) 
as a theorem of
5 7 .7 , Prove (oc5) 
as a theorem of F2pt<x>4).
5 7 .8 . Prove (oo5) 
as a theorem of F2p(flCZ).
58. The predicative and ramified functional calculi of second 
order.
Objections against the absolute notion of a ll—as it is involved, e.g,, in the 
notion of a ll classes of individuals, w ithout qualification— have already been 
discussed briefly in footnote 535. T here is m uch difference of opinion am ong 
m athem aticians regarding the significance of these objections, some holding 
them  to be pointless and others believing th a t they cast serious doubts on the 
m ethods used and the results obtained in large parts of classical m athem atics. 
Our purpose in this section is not to debate the question of significance but to 
m ake a proposed definition of these objections—or of one form  of them — by
•"This axiom of infinity is suggested by the definition of finiteness which was given 
by H. Weber and slightly simplified by J. Kurschak. See J a h re s b e ric h t dev D eutsch en  
M a th e m a iik e r -V e re in ig u n g , vol. 15 (1906). p. 177, and vol. 16 (1907), p. 425. The re­
lationship should also be noticed to (ool), which asserts the existence of a partial order 
of the individuals in which there is no last individual.
•^Suggested by Paul Stackers definition of finiteness. J a h re s b e ric h t der D eutsch en  
M a fh e m a tik e r -V e r e im g u n g , vol. 16 (1907), p. 425.
87,Suggested by Tarski's definition of finiteness E , in F u n d a m e n ta  M a lh em a tica e, 
vol. 30 (1938), p. 162. As here stated, however, the axiom has been modified by using 
a one-many correspondence in place of the one-to-one correspondence of Tarski's 
definition £“.
•78That this cannot be done without using axiom (w) follows from a result obtained 
by Mostowski in his dissertation, O  N ie s a le tn o ic i D e fin ic ji S k o ric zo n o ic i w  S y ste m ic  
L o g ik i, published as a supplement to A n n a lc s  tie la  S o c iiti P o lo n a ise  de M a th im a tiq u e , 
vol. II {1938), pp. 1-54.

---


§58]
RAMIFIED FUNCTIONAL CALCULI
347
form ulating as a logistic system  the weakened functional calculus of second order 
to which th ey  lead.
In the form in which we wish to take them  here, these objections m ay be said 
to have originated in H enri Poincar6’s condem nation of w hat he called impre- 
dicative definitions, i.e., "definitions par . . . une relation entre l'objet <l d^finir 
et tous les individus d ’un genre dont l’objet k d^finir est suppose faire lui-m^me 
partie (ou bien dont sont supposes faire partie des etres qui ne peuvent £tre eux 
mfimes d^finis que par l'objet k d^finir),"67* This was afterw ards embodied in 
Russell’s vicious-circle principle S’1* th a t "no to tality  can contain m embers de­
fined in term s of itself," or "w hatever contains an ap p aren t variable m ust not 
be a possible value of th a t v ariab le."676 Also W eyl objects in a similar way to 
w hat he takes to be a vicious circle in classical analysis.676
As understood by Russell in p articular (and by W hitehead and Russell in 
Principia Mathemalica) the vicious-circle principle constitutes a restriction upon 
the possible range of a propositional or functional variable, and hence a restric­
tion upon substitutions for such a variable. The application of this to the func­
tional calculus of second order affects prim arily the axiom  schem ata *509 and 
leads first to the predicative functional calculus of second order and then to the 
ramified functional calculi of second order, as these are form ulated below.* 674 * 676 677
*7*The quotation is from a paper by Poincar^ in "Scientia,” vol. 12 (1912), see p. 7. 
For the earliest statem ent of Poincare's objection against impredicative definitions 
("definitions non predicatives") see the Revue de Mitaphysique et de Morale, vol. 14 
(1900), p. 307.
674It is not certain, however, that the vicious-circle principle of Russell is the same 
thing that Poincar4 intended, since Poincar4 never made a system atic development of 
his ideas in this direction and the exam ples which he gives (informally) of impredicative 
definition are not sufficient to determ ine what would have been his verdict regarding 
other exam ples of what m ight be considered impredicative definition.
In a paper in the Revue de Mitaphysique et de Morale, vol, 17 (1909), pp. 461-482 
(afterwards reprinted as Chapter IV  of Dernihres PensSes (1913)), there is a discussion 
by PoincarS of Russell's "hierarchy of types," i.e., of the (higher-order) ramified func­
tional calculus which Russell introduced as based on the vicious-circle principle. From 
this it is perhaps fair to infer that Poincar£ regarded the vicious-circle principle as being 
in general accord with his own ideas; but that he was unwilling to accept without re­
servations the ramified functional calculus which Russell proposed as embodying it—  
even if modified by omission of R ussell’s axiom s of rcducibility, discussed in our next 
section.
Apparently PoincarS (unlike W eyl) believed or hoped that all of classical m athem at­
ics could be developed without resort to impredicative definition once the postulates 
of arithm etic, including the postulate of m athem atical induction, are granted. Compare 
his paper in Acta Mathematica, vol. 32 (1909), pp. 195-200, especially §5, pp. 198-200.
676See the American Journal of Mathematics, vol. 30 (1908), p. 237. The term" appar­
ent variable" is used by Russell in the sense in which we have been using "bound 
variable" (cf. footnote 28), and the second quoted statem ent of the vicious-circle 
principle is therefore to be rendered in our term inology as follows: a wff which contains 
a bound variable m ust not denote one of the values in the range of that variable.
•T6See the explanation in his paper, "Der Circulus Vitiosus in der Heutigen Begriin- 
dung der Analysis" in the Jakresbericht der Deutscken Mathematiker-Vereimgung. vol. 28 
(1919), pp. 85-92.
E,7We shall not try here to decide upon or state the sem antical rules for a principal 
interpretation of any of the predicative or ramified functional calculi of second order. 
But we remark that, m order to accord w ith the m otivation as just described, it is

---


348
FUNCTIONAL CALCULI OF SECOND ORDER [Chap. V
It should be noticed th at the functional calculus of first order rem ains un- 
affected by the vicious-circle principle.
The predicative functional calculus of second order in the formulation 
Fg! has the same primitive symbols and the same wffs as the simple func­
tional calculus of second order F\. A distinction is made of pure and ap­
plied, of singulary, binary, etc., predicative functional calculi of second 
order in the same way as for the simple functional calculus of second order; 
but where the term “predicative functional calculus of second order" is used 
without qualification, we shall understand that propositional variables and 
functional variables of all kinds—singulary, binary, ternary, etc.—are con­
tained, with or without individual and functional constants.
The four rules of inference *500-*503 remain the same for F*! as for F\, 
The axioms of F*! are given by the following seven axiom schemata (the 
relationship of which to the axioms and axiom schemata of F* will be evi­
dent):
A d . B d  A
A d
[ B d C ] 3 . A = ) B d . A = ) C  
d  - B  d  , B d  A
A z>a B d . A d  (a)B, where a is a variable of any kind that is not a 
free variable of A.
(a)A n  S£A|, where a is an individual variable, b is an individual variable 
or an individual constant, and no free occurrence of a in A is in a wf part 
of A of the form (b)C.
necessary to abandon the idea that a sentence denotes one of the two truth-values t 
and f, and hence to avoid taking these two truth-values as the values of the propositional 
variables, or classes and relations in extension as values of the functional variables. 
The standpoint of Russell in 1908, and of Whitehead and Russell in the first edition of 
P n n c ip ia  M a th e m a tic a , is apparently best represented by supposing sentences to denote 
propositions, taking propositions as values of the propositional variables, and prop­
erties and relations in intension as values of the functional variables. And the more 
extensional view advocated by Russell in his In tro d u c tio n  to th e  S eco n d  E d itio n  of 
P r in c ip ia  M a th e m a tic a  (cf. footnote 590) can perhaps be represented by means of an 
infinite list ot truth-values, namely, two truth-values t m and f w for each level m , the 
values of the propositional variables of wth level being t m and fm, and the values of the 
w-ary functional variables of mth level being functions (in extension) having the ordered 
w-tuples of individuals as their range, and having t m and fm (one or both) as values.
It must be added at once that the foregoing is not a reproduction of Russell’s own 
account of semantical matters, especially as found in the introduction and appendices 
to the second edition of P n n c ip ia  M a th e m a tic a , But it is rather a first step of a contem­
plated attem pt to fit the ramjficd functional calculi into our own semantical program 
and to provide for them "semantical rules" of a kind to which Russell would certainly 
not consent.

---


§58]
RAMIFIED FUNCTIONAL CALCULI
349
(p)A=>S£A|, where p is a propositional variable, and B contains no 
bound propositional or functional variables.
(f)A z? S^*1’**....*">A|, where f is an «-ary functional variable, and
xv x 2, . . ., x n are distinct individual variables, and B contains no bound 
propositional or functional variables.
The characteristic feature is the restriction upon substitution for propo­
sitional and functional variables that is contained in the last two schemata, 
the restriction, namely, that B must not contain bound propositional or 
functional variables. And indeed if this restriction were removed we would 
obtain merely another system of axioms and rules for the simple functional 
calculus of second order.
The predicative functional calculus of second order is the same (apart 
from trivial notational differences) as the ramified functional calculus of 
second order and first level, and its propositional and functional variables 
are said to be predicative, or of the first level,578 In the ramified functional 
calculi of second order and higher levels, additional propositional and func­
tional variables are introduced, of successively higher levels, the leading 
idea being that in substituting for a propositional or functional variable of 67
67*Thc use of the word "level" here is a departure from the terminology of Russell 
and of Principia Mathematica. In the second-order functional calculi, what we call the 
level of a propositional or functional variable is the sam e thing tluit W hitehead and 
Russell call the order. B ut in general, and especially in connection with the ramified 
functional calculi of higher order, we understand by th e level of a functional variable 
what would be called in the term inology of W hitehead and Russel! the amount by which 
the order of the functional variable exceeds the order of the variable1 of highest order 
which m ay stand in any of the argument places (i.e., in any one of the places between 
parentheses following the functional variable).
W e shall not use the word “order" in this connection except in the sense in which we 
speak of functional calculi of first order, of second order, and so on (a use of the word 
very different from that of W hitehead and Russell). Also we shall use the word '"type" 
in a way which differs from the usage of W hitehead and Russell, and which is suited 
rather to the simple functional calculi than to the ramified functional calculi. N am ely— 
as will be explained more fully in Chapter VI—all the functional variables which appear 
in the functional calculi of first (or second) order are said to be of the jirst type-class, 
the new functional variables which are introduced in the functional calculus of third 
order are said to be of the second type-class, and so on, a new type-class of functional 
variables being introduced in each successive functional calculus of odd order. There is 
in our term inology no distinction of typo among propositional variables, all of them  
being of the same type— though in the ramified functional calculi there are propositional 
variables of different levels. Likewise all individual variables are of the sam e type 
(and of a different type from propositional and functional variables). Two functional 
variables, one m-ary and the other «-ary, are of the same type, if they are botii of 
the first type-class and m ~ n, or if they are of the same higher type-class and 
m — n and the variable which may stand in each argum ent place (in order) after 
one of them is of the same type as the variable which may stand in the corresponding 
argument place after the other.

---


350
F U N C T I O N A L  C A L C U L I  O F  S E C O N D  O R D E R  [Chap. V
given level, the wff B which is substituted may contain bound propositional
and functional variables of lower levels only. Thus the ramified functional 
calculus of second order and second level, Fa/a (in our present formulation of 
it), contains propositional and functional variables of the first level and of 
the second level. Similarly Fj/a contains propositional and functional vari­
ables of three different levels, and so on. The ramified functional calculus of 
second order and level co, Fj^", contains all the propositional and functional 
variables of all (finite) levels.
The primitive bases of these (and other) ramified functional calculi may 
be given simultaneously in the following way.579 
The primitive symbols are first the eight following:
r => i ~ { . ) v
Hum therp in an infinite list of individual variables, the same as for Fj:
* y 
* 
xi 
Vx 
h  
x*
Then there are or may be propositional variables of various levels, namely, 
dther no propositional variable, or all propositional variables of not more 
than a certain maximum level, or all propositional variables of all levels. 
Explicitly, the symbols admitted as propositional variables are the following, 
where the superscripts indicate the level and where for any particular level 
used the list of variables is infinite:
p 1
q1
r1 
s1 
p\
q\ 
. . .
P1
ql
r* s* pi
q\ 
. . .
Ps
<?
r3 s3 
p\
ql 
. . .
Then for each n there are or may be «-ary functional variables of various 
levels (n =  1, 2, 3, . . 
Namely, there are either no n~ary functional vari­
ables, or all M-ary functional variables of not more than a certain maximum 
level, or all «-ary functional variables of all levels. The explicit symbols 
admitted as functional variables are as follows, where the first numeral in 
the superscript indicates whether the functional variable is singulary, or
*79This formulation should be compared not only with the original formulation of 
Russell (in the paper cited in footnote 454) and that in Principia Malhematica but also 
with the formulation of Hilbert and Ackermann in Grundzuge der Theoretischen Logik, 
first edition (1928), and that of Frederic B. Fitch in The Journal of Symbolic Logic, vol. 
3 (1938), pp. 140-149. All of these differ from our present formulation of (say) F j'“ in 
not being restricted to what we here call the second order. Fitch's formulation moreover 
contains notations and axioms which are designed to include in the system in some sense 
a formulation or partial formulation of arithmetic, so that his system is more nearly 
comparable to our Xl/at (see below) than to F j/Ct\

---


§58]
R A M I F I E D  F U N C T I O N A L  C A L C U L I
351
binary, or ternary, etc., and the second numeral in the superscript indicates 
the level:
p m
Gin
# 1/1
p m
6 1/2
H w
# 1 /2
G \lt 
. .
p m
G l/3
W *
/,*l/3 
1 1
GJ'» 
..
p*!i
Q2!1
1
3/1 
1 1
G f  
. .
p m
r ;2 /2
# 2 / 2
j: 2/2 
1 1
/-•2»'2
jg-2/3
G 2/3
# 2 / 3
;,'2/3 
1 1
G f  
. .
/,~3/l
and so on.
Then finally there may be individual constants ui tuncnonal constants - i 
both—where for each functional cousunt it must be given what its level is 
and whether it is singulary, binary,, ternary, etc.
The formation rules are the same as for the simple functional calculus ui 
second order, F*, with the understanding that the level of a functional 
variable or functional constant is to be ignored. -In particular, e.g., if f is 
an n-ary functional variable or functional constant, and x ,, x a, . . 
x n arc- 
individual variables or individual constants (or both), then f ( x If x 2, . . 
x„)
is wf, regardless of the level of f.
The same abbreviations of wffs and in particular the same definitions are 
used as forFg. But in D20and D21 the propositional variable s is replaced by 
the propositional variable sl, of the first level. And in D22 and D23 the 
functional variable F1 is replaced by the variable F 1'1, of the first level.580
As a further abbreviation in writing wffs, the superscripts of the-propo­
sitional and functional variables may be omitted ordinarily. In order to make 
this possible, the level which is to be given to a particular variable may be 
specified in words. Or following Principia Mathematica we may write an 
exclamation point after a letter to indicate that it represents a variable which 
is predicative, or of the first level.
The four rules of inference are the same as for F*, i.e., *500-*503.
The axioms are given by seven axiom schemata, closely analogous to those 
given above for the predicative functional calculus of second order. Indeed 
the first five axiom schemata are exactly the same as for F —except of 
course that A, B, C are now wffs of the particular ramified functional cal­
culus of second order whose axioms are being given, and in the fourth schema
M0If desired, we might introduce also notations 
and =|=„ replacing the variable 
F  in D22 and D23 by F 1/2. Likewise ==8 and =|=S) and so on.

---


352
FUNCTIONAL CALCULI OF SECOND ORDER 
[Chap. V
a is a variable of any kind belonging to the particular ramified functional 
calculus of second order (subject to the condition that a is not free in A). 
The sixth and seventh axiom schemata are modified as follows:
(p) A z d $£A |, where p is a propositional variable, the bound propositonal 
and functional variables of B are all of level lower than that of p, and the 
free propositional and functional variables of B are of level not higher than 
that of p.
(f)A z d 
*"ix*)A, where f is an w-ary functional variable, and
xv x 2, . . 
x„ are distinct individual variables, and the bound proposi­
tional and functional variables of B are all of level lower than that of f, 
and the functional constants and the free propositional and functional 
variables of B are all of level not higher than that of f.
The ramified second-order functional calculi of various levels are specified 
as follows by means of a maximum level of propositional and functional 
variables and functional constants. 
has all the first-level variables and 
may have first-level functional constants, but has no variables or constants 
of higher level (thus it differs only trivially from F^1). Fj/a has all the 
propositional and functional variables of first and second levels and may 
have functional constants of these levels, but has no variables or constants 
of higher level; and so on. Fg/tu has all the propositional and functional 
variables of all levels and may have functional constants of any level.
Of particular interest is the pure ramified functional calculus of second 
order and level co, 
having as primitive symbols all the possible kinds of
variables listed above, and no constants. Also logistic systems obtained from 
F^®p by adding one of the axioms of infinity (ool)-(oo4), with F taken as 
a variable of the first level, or the infinite list of axioms obtained from axiom 
(w) by taking F to be of the first level and G of all possible levels (succes­
sively), or both.681 Also further, logistic systems obtained from F^“p by 
adding functional constants and postulates containing them. 48
48,That part of the system  of Principia Matkemaiica which does not go beyond 
second-order functional calculus is approxim ately represented by the pure ramified 
functional calculus of second order and level to, with the addition of an axiom  of infinity 
and the infinite list of axiom s obtained from axiom  (w) as described, and the further 
addition (at least for the first edition of Principia) of the axiom s of reducibility given 
in §59 below. For the com plete system  of Principia, functional variables of higher type- 
class (cf. footnote 578) added, but again ramified, or divided into levels; the axiom  of 
infinity is restated in a different form (the "Infin ax" referred to in footnote 559) 
requiring functional variables of higher type-class; the axiom s obtained, as described In 
the text, from axiom  (w) are superseded by Russell's multiplicative axioms (equivalent to 
axiom s of choice); and (at least for the first edition) axiom s of reducibility with varia­
bles of higher type-class are included, in addition to those given in §59.

---


§58]
RAMIFIED FUNCTIONAL CALCULI
353
Of this last kind is the system of ramified second-order arithmetic, A2/<" 
which we go on to formulate briefly before concluding this section.582
T he system  A2'", in its intended in terp retatio n , probably w ould n o t be 
acceptable to the authors of Principia Mathematica, since they require th a t the 
n atu ra l num bers be defined and their properties proved rather th an  postulated. 
On th e oth er hand it can be th ought of as in accord w ith the program  of W eyl in 
Das Kontinuum,683 or w ith the ideas of Poincar6, both of whom accept the 
elem entary m ethods of arithm etic, including proof by m athem atical induction, 
as being (to quote W eyl) ein letztes Fundament des mathematischen Denkens.
As stated, A2/“ is obtained from F2/a,p by adding functional constants as 
undefined terms, and postulates. The functional constants are E  and 77, 
ternary functional constants of the first level, the same as the functional 
constants E  and 77 of the systems A0 and A1. The postulates are the first 
twelve postulates of A1 unaltered, and an infinite list of postulates obtained 
from the thirteenth postulate of A1 (the postulate of mathematical induction) 
by taking the function variable F1 to be of all possible levels, successively.584
A2/“ may be called, more fully, a formulation of the ramified second-order 
arithmetic of level co; and ramified second-order arithmetics of lower levels 
may be obtained by specifying a maximum level of propositional and func­
tional variables. For example, the wffs of A2/2 are the same as the wffs of A2/w 
which contain no propositional or functional variables of level higher than 
the second; and the postulates of A2/a are fourteen in number, being the 
same as the postulates of A2^ which contain no propositional or functional 
variables of level higher than the second.
The system of predicative second-order arithmetic, A21, is obtained from the 
pure predicative functional calculus of second order, Fglp, by adding the 
undefined terms and postulates of A1. Thus it differs only trivially from A2/1.
For A81 and for the various ramified second-order arithmetics, as here 
formulated, including AB/W, the same definitions are used as for the corre­
sponding second-order functional calculi F21, F^", etc., except that the def-
“ *The system s A0 and A 1, form ulated in 555, rem ain unaffected by adoption of the 
point of view  of ram ification or division into levels.
“ ■Compare footnote 535.
W eyl describes a form ulation of ramified arithm etic of second order, and of higher 
order, and holds such a system  to be admissible. H ow ever, the actual developm ents of 
the book are largely within a predicative second-order arithm etic that would seem to 
be essentially equivalent to the system  A2! (see below), though differing in details of 
the form ulation. At som e places this must be extended to a predicative third-order 
arithm etic, by adding variables of the next higher type-class, but allow ing them  to 
appear only as free variables.
m I.e., more explicitly, Fl is replaced by Fm to obtain the first postulate of the in­
finite list, by Fl/i to obtain the second one, and so on.

---


354
FUNCTIONAL CALCULI OF SECOND ORDER [Chap. V
inition schemata D22 and D23 are discarded, and the notation [a =  b] is 
defined rather in the same way as was done for A0 and A1 in §55. The nota­
tions Z0(a) and Zx{a) are also defined in the same way as for A0 and A1.
EXERCISES 58
5 8 .0 . Prove as a theorem of Fg! :
x ~  y => . y =  x
58.1 . Where F i s a  singulary functional variable of arbitrary level,585 
prove as a theorem of A2'1" ;
x =  y =  . F[x) =>F F(y),
i.e., written more fully, E[xt zt x^) z>ex E[y, z, xl ) =  . F(x) 
F(y). (Use 
the postulates of mathematical induction.)
5 8.2. Where F and Care singulary functional variables of different levels, 
show that the following is a theorem of A2/tw but not of 
:
F{x) =>F F(y) =  - G(x) 
G(y)
[Suggestion: C onsider an interpretation of F *'01 according to w hich the individuals 
are the natural num bers; the values of the propositional variables are t and f, th e 
sam e for all levels; the first-level propositional functions, i.e., th e values of the 
first-level functional variables, are those w hich m ake no distinction am ong the 
different individuals, thus only the null class and the universal class, the null 
relation and the universal relation, and so on; the second-level propositional 
functions are those additional propositional functions which m ake no distinction 
am ong the different individuals except the distinction of odd and even; the 
third-level propositional functions are those additional propositional functions 
which distinguish th e individuals as congruent to 0, 1, 2, or 3 m odulo 4; and so 
on .*88 In  a m anner w hich will now be fam iliar to the reader, th e  sem antical a r­
gum ent so obtained can be converted into a syntactical independence proof.)
59. A xiom s of reducibility.
Because th ey  w ere unable otherw ise to develop classical m athem atics w ithin 
their system  in th e  m anner which th ey  desired, Russell in 1908,85 * 887 and later
885Thus " F “ becomes in effect a syntactical variable, having F I/l, F 1'*, F 1'3, . ..  as 
values: and a theorem schema summarizing an infinite list of theorems is established. 
This is an instance of what the authors of Principia Mathematica call typical ambiguity.
The infinite list of postulates ol mathematical induction, of A*/(W, might also be con­
veniently summarized in a single postulate schema by means of typical ambiguity. 
(Compare footnote 584.)
s8flOf course not m eant to be a principal interpretation but a special interpretation 
serving the purpose of the particular independence proof. 
fi87ln the paper cited in footnote 454.

---


§59]
AXIOMS OF REDUCIBILITY
W hitehead and Russell in Principia Mathematica, were led to supplem ent the 
ram ified functional calculi by the addition not only of an axiom  of infinity and 
m ultiplicative axiom s (as explained in footnote 581) bu t also of th e famous 
axiom s of reducibility. The content of the axiom s of reducibility h:, for a prop­
ositional function of a rb itra ry  level, th a t there exists a form ally equivalent 
propositional function of th e  first level (the intended interpretation being such 
th a t th e  formal equivalence of propositional functions is not alone sufficient to 
render them  identical). T his has been m uch criticized ,588 in p articu lar oil the 
ground th a t the effect is largely to restore the possibility of im predicative def­
inition which the distinction of levels was designed to elim inate, indeed, as 
m any have urged,388 the tru e choice would seem  to be betw een th e  sim ple 
functional calculi and the ram ified functional calculi w ithout axiom s of reduci­
bility. I t  is hard to th in k  of a point of view from w hich the interm ediate position 
represented by the ram ified functional calculi w ith axiom s of reducibility would 
appear to be significant. A nd in the Introduction to the Second Edition of Principia 
Mathematica (.1925), Russell in fact recom m ends abandonm ent of the axiom s of 
red u cib ility .680 N evertheless, because of their historical im portance, it seems 
desirable to give these axiom s here (as far as th ey  fall w ithin the second-order 
functional calculi).
Syntactically, the axioms of reducibility, intended as axioms to be added 
to F^", are the following doubly infinite list, where G is always a functional 
variable of the first level, and F is of arbitrary higher level:
(3G) . F{x) = x G(x)
(3G) . F(x, y) = xv G(x, y )
(3G) . F{x, y, z) = XVI G{x, y, z)
355
#8BIn particular by Leon Chwistck in Przeglqd Filozoficzny, vol. 24 (1921), pp, 
164-171; Hilbert and Ackermann, Grundziige der Tkeoreliscken Logik, first edition 
(1928), pp. 114-115: Adolf Fraenkel, Einleitung in die Mengenlehre, third edition (1928), 
pp. 259-203; W. V. Quine in Mind, n.s., vol. 45 (1936), pp. 498-500, and in a paper in 
The Philosophy of Alfred North Whitehead (1941), see pp. 151-152.
M*Chwistek in the paper cited in the preceding footnote; F. P, Ramsey in a paper m 
the Proceedings of the London Mathematical Society, ser. 2 vol. 25 (1926), pp. 338-384, 
reprinted in his The Foundations of Mathematics and other Logical Essays (1931), pp. 
1-01; Rudolf Carnap in Abriss der Logistik (1929), §9. See also scattered remarks by 
Carnap and Hans Hahn in Frkenntms, vol. 2 (1931), pp. 73, 97, 145
B»°With the suggestion that their place could be partly taken by axioms of extcnsional- 
ity, expressing in the notation of the ramified higher-order functional calculi that for­
mally equivalent propositional functions of the same type and the same level are identi­
cal. (Cf. footnote 577.)
Compare also The theory of constructive types, a paper in the Annales de la Societe 
Polonaise de Math&matique, vol. 2 (1924), pp. 9-48, and vol. 3 (1925), pp. 92-141, in 
which Chwietek takes what Russell describes as the heroic course of dispensing with 
the axioms of reducibility without adopting any substitute, thus undertaking to base 
a logistic treatm ent of mathematics on the system of Principia Mathematica without 
these axioms.

---


356
FUNCTIONAL CALCULI OF SECOND ORDER [Chap. V
(There are also axioms of similar form intended to be added to the higher 
order functional calculi.)
These axioms are not all independent, since those which contain singulary 
functional variables can be proved by using those which contain binary 
functional variables, and so on down the list. Also among those which 
contain n-ary functional variables (with fixed n), it is obvious that one in 
which F is of lower level can be proved by using one of those in which F is 
of higher level.
EXERCISES 59
59.°. In the logistic system 
obtained by adding the axioms of
reducibility to 
prove
F[x) 
F(y) =  . G{x) 
G{y)t
where F and G are singulary functional variables of different levels.
5 9 . 1 . In 
(thus without using axioms of reducibility), prove
(3q) 
=
where p and q are propositional variables of different levels.
59*2- In the logistic system obtained by adding to 
the axioms of 
reducibility containing binary functional variables, prove as theorems the 
axioms of reducibility containing singulary functional variables.
59-3- In the logistic system obtained by adding to 
the axiom 
schema of footnote 555, f and g being taken as predicative functional 
variables, show that the axioms of reducibility are theorems. Discuss the 
question of prescribing the levels of f and g in this axiom schema so as to 
avoid obtaining from it any theorem (3G ). F(a?) = 2 G(a) in which G is of 
lower level than F.

---


Index of Definitions
This index includes references to all passages in which a new term is 
introduced or the meaning or usage of a term is explained, whether by 
definition or otherwise. Both the terms used in the meta-language and 
the characters used in the various object languages are covered (excepting 
letters used as variables, and parentheses, brackets, commas); and also 
references to terminology which is employed by others but not adopted in 
this book. The numbered definitions D1-D25 pertaining to the object 
languages are indexed according to their numbers, at the proper place in 
alphabetic order (under the letter D). And designations used for particular 
logistic systems, consisting of a capital letter with superscripts or subscripts 
or both, are included in the index also, each at its proper place in alphabetic 
order.
In order to fix the alphabetic arrangement the following special rules 
are adopted. Greek letters are treated as coming in alphabetic order after 
all the English letters, and are arranged among themselves in their own 
alphabetic order. Arabic numerals are treated as coming after both English 
and Greek letters, and are arranged among themselves in order of increasing 
magnitude (of the corresponding numbers — thus 0 first, then 1, then 2. 
and so on). Special characters (including inverted letters treated as special 
characters) are arranged in an arbitrary order after English letters, Greek 
letters, and Arabic numerals. To the distinction between capital and small 
letters, roman and italic letters, unaccented and accented letters no attention 
is ordinarily paid in alphabetizing; but where two entries would otherwise 
coincide in the alphabetic order, the rule is followed to put capital letters 
before small letters, and then to put roman letters before italic letters, 
and then to put unaccented letters before accented letters. Parentheses, 
the hyphen, the solidus, exclamation point, comma, and other punctation 
marks are also ordinarily ignored in alphabetizing, but where (in spite of 
all preceding rules) two entries would otherwise coincide in the alphabetic 
order, the entry lacking the parentheses or other punctuation mark is 
placed before the other entry. Finally, account is taken of superscripts 
and subscripts only in cases in which (in spite of all preceding rules) two 
or more entries would otherwise coincide in alphabetic order; in such cases,

---


358
I N D E X  O F  D E F I N I T I O N S
the entries are arranged in the alphabetic order of their superscripts; or 
if the superscripts are identical, or non-existent, the entries are arranged 
in the alphabetic order of their subscripts.
The references given in the index are by section number (indicated by 
"§”); or by the number of an axiom, rule of inference, theorem, or meta- 
theorem (indicated by "t”, 
or "**” forming part of the number); 
or by numbered footnote (indicated by "n.”); or by numbered exercise 
(indicated by the occurrence of a period as part of the number). Footnote 
152 of §10 (see page 70) should be consulted for an explanation of the 
system of numbering which is used in the text. And it should be noticed 
in particular how the number of any section indicates in what chapter it 
will be found, and the number of any axiom, rule, theorem, or metatheorem 
indicates in what section it will be found. As explained in footnote 152, 
exercises are placed immediately after the section that is indicated by the 
number of the exercise — so that, e.g., 46.0 is the first exercise in the 
collection of exercises (called "Exercises 46”) which follow §46, and 46.19 
is the twentieth exercise in the same collection.
In searching for a reference from the index, page numbers may be 
ignored, and there may be used instead the numbers of chapters, sections, 
and exercise collections which are given at the top of the pages of the text. 
When the reference is to a footnote, observe that footnotes 1-149 are in 
the Introduction and that beyond that the number of the footnote indicates 
directly in what chapter it falls, numbers in the one hundreds being for 
footnotes in Chapter I, those in the two hundreds for footnotes in Chapter II, 
and so on.
A1: 55.18.
A": §55.
A0: §55, n. 582. See elementary 
arithmetic, Hilbert arithmetic. 
A1: §55, n. 582. See elementary num­
ber theory, Hilbert arithmetic.
A2: §55. See Peano’s postulates. 
A2!: §58.
As/<u: §58, n. 583, n. 584, n. 585. 
A2/1: §58.
Aa/2: §58.
A3: §55.
A1: §55.
(A,): 55.18.
(A0); §55.
(AJ: §55.
(Aa): §55. See PeanoJs postulates. 
A: n. 91.
A1( A2........A„ b B: §13, §36, n. 343.
Abbreviative definition: n. 168. 
Absolute completeness: §18. 
Absolute consistency; §17. 
Absolutism: n. 535.
Absorption, laws of: 15.8. 
Abstraction: §03.
Abstraction operator: §06.

---


I N D E X  O F  D E F I N I T I O N S
359
Abstraktion: n. 112.
afep: §53.
Affirmation of the consequent, law 
of: f l 02, t202.
afp: §32.
Algebra of logic: n. 125, §29.
Algorithm: n. 118.
Algorithms logique: n. 125.
Alphabetic change of bound (in­
dividual) variable, rule of: *350, 
*402, *502.
Alphabetic change of bound prop­
ositional and functional variables, 
rule of: *515.
Alphabetic order: §10, §20, §30.
Alternation: §05.
Analysis: n. 520.
Antecedent: §10, n. 162, §20, §30.
Apparent variable: n. 28, n. 575.
Applied functional calculus of first 
order: §30.
Applied functional calculus of first 
order with equality: §48.
Applied functional calculus of second 
order: §50.
Argument: §03.
Argument place: n. 578.
Assert (a proposition): §04, n. 72.
Assert (a propositional form): §06, 
n. 106, n. 107.
Assert (a sentence): §04, n. 72.
Assertion, law of: 12.7.
Assertion sign: n. 65.
Associated form (of a connective): 
§05.
Associated formula of the extended 
propositional calculus: §53.
Associated formula of the propo­
sitional calculus: §32.
Associated function (of a connec­
tive): §05.
Associated function (of a constant): 
§03.
Associated function (of a form): §03.
Associated m-ary functions of an 
n-ary form: §03.
Associated natural number (of wn): 
§54.
Associated propositional function: 
§54.
Associated quantifier-free formula: 
§32.
Associative law of multiplication:
55.8.
Associative laws: see complete as­
sociative laws.
Autouymy: §08, n. 156.
Axiom: §07, n. 128.
Axiom 
of infinity: 
§57, 
n. 559, 
n. 560.
Axiom of well-ordering of the in­
dividuals: §56.
Axiom schema: §27, §30.
Axiom (w): §66.
Axiomatic method: §07, n. 126, n. 
127.
Axiomatic set theory: n. 75, n. 129, 
end of §09.
Axioms of choice: §56, n. 555.
Axioms of extensionality: n. 590.
Axioms of reducibiiity: §59.
Basic instance: §30.
Bear (a relation); §04.
Bedeuten: n. 7.
Biconditional: §05.
Binary cunnectLve: §05.
Binary form: §02.
Binary function: §03.

---


360
I N D E X  O F  D E F I N I T I O N S
Binary functional calculus of first 
order: §30.
Binary relation: n. 78.
Boolean algebra: 15.8.
Boolean ring: 15.6, n. 185, 15.7. 
Boole's law of development: 28.1(5), 
28.1(6), n. 237.
Bound occurrence of a variable: 
§06, n. 117, §30, 38.6.
Bound variable: n. 28, n. 36, n. 52, 
n. 64, §06, n. 96, §30, §50. 
Brackets: §05, §10, n. 156.
By P: §31, n. 319, §51.
Bf: §32 (proof of **323).
Bt: §32 (proof of **323).
C: n. 91, 12.2.
Calculus of inference: n. 125. 
Calculus of logic; n. 125.
Calculus ratiocinator: n. 125. 
Categorical proposition; 46.22. 
Categorical syllogism: 46.22, n. 441. 
Categorical system of postulates: §55. 
Characteristic function: 43.2. 
Characteristic 
(system of truth- 
tables): n. 217.
Choice, axioms of: §56, n. 555. 
Class: §04.
Class concept: n. 17, §04.
Closed wff: §50.
Closure; §43, §54.
Coincide in extension: §04. 
Collective name: n. 6.
Combinatory logic: n. 100.
Common name: n. 4, n. 6. 
Commutation, law of: 12.7. 
Commutative law of equality: §48, 
1*521.
Commutative law of (material) e- 
auivalence: f!55.
Commutative law of multiplica­
tion: 55.9.
Commutative laws: see complete 
commutative laws.
Compatibility: n. 2.
Complete as to consequences: §55.
Complete as to provability: §55.
Complete associative law of (ma­
terial) equivalence: 26.0.
Complete associative laws: compare 
also 15.5, 15.7.
Complete commutative law of equal­
ity: f523.
Complete commutative law of (ma­
terial) equivalence: 15.0(7), 26.0.
Complete commutative laws: com­
pare also 15.5, 15.7.
Complete distributive law of con­
junction over disjunction: 15.8.
Complete distributive law of disjunc­
tion over conjunction: 15.8.
Complete distributive laws: compare 
also 15.5, 15.7.
Complete in the sense of Post: §18.
Complete law of double negation: 
n. 163, |154.
Complete self-distributive law of 
(material) implication: n. 163.
Complete system of primitive con­
nectives: §24.
Complete with respect to a given 
transformation: §18.
Completeness of a logistic system: 
§18, §32, §54.
Composition, law of: 15.0(5).
Concept: §01, n. 17.
Concept of: §01, n. 21.
Conclusion: §07, n. 162.
Concurrent constants: §02.

---


I N D E X  OF D E F I N I T I O N S
361
Concurrent forms: §02.
Concurrent to a constant: §02. 
Conditional: §05.
Conditioned disjunction: §24. 
Confirmation: n. 2.
Conjunction: §05, n. 227, n. 232. 
Conjunctive normal form: n. 299. 
Connectives: n. 64, §05, n. 112. 
Connotation: n. 14.
Connote: n. 16.
Consequence: §55.
Consequent: §10, n. 162, §20, §30. 
Consistency of a logistic system: §17. 
Consistent as to consequences: §55. 
Consistent as to provability: §55. 
Consistent class of wffs; §45, §54. 
Consistent in the sense of Post: §17. 
Consistent with a class of wffs: §45, 
§54.
Consistent with respect to a given 
transformation: §17.
Constant: n. 6, §02, n. 31, n. 112, 
n. 117, §10, §30, n. 460, §50. 
Constant function: §03.
Contextual definition: § 55, n. 528. 
Continuity: n. 102.
Contradiction: §15, §23. 
Contradiction, law of: 15.0(9), 26.13. 
Contraposition, converse law of: 
t204.
Contraposition, law of: 15.0(6), 
f223, 26.13.
Converse: §10, §30.
Converse domain: n. 517.
Converse implication: §05.
Converse law of contraposition: 
f204.
Converse law of double negation: 
n. 163, f222, 26.13.
Converse non-implication: §05.
Converse of a function: §03.
Converse seif-distributive law of 
(material) implication: n. 163.
Z): n. 91.
Decision problem: §15, n. 183, n. 184, 
§46.
Decision problem, reduction of: see 
reduction.
Decision problem, solution in a 
special case: n. 421.
Decision problem for provability: 
§15, n. 184.
Decision problem for satisfiability: 
§46.
Decision problem for validity: §46.
Decision procedure: §15.
Declarative sentence: §04.
Deducibility problem: n. 184.
Deduction theorem: *130, n. 181, 
§29, n. 332, *360, *516.
Definiendum: §11.
Definiens: §11.
Definition: n. 49, §11, n. 167, n. 168, 
n. 305.
Definition schema: §11.
Dcfinitionally equivalent: beginning 
of Chap. in.
De Morgan, laws of: 15.8, n. 188.
Denial of the antecedent, law of: 
1123, f220, §26.
Denotation: §01.
Denotation value: n. 27.
Denote: §01, n. 6, n. 7, n. 148.
Denote in the syntactical sense: 
n. 143.
Derived rule of inference: §12.
Derived semantical rule: n. 168.
Description operator: §06.

---


362
I N D E X  O F  D E F I N I T I O N S
Descriptions (Russell's contextual 
definition): n. 546,
Designate: n. 20.
Designated truth-value: §19. 
Development, law of: 28.1 (5), 28.1(6). 
Dilemma: 15.9, n. 189, n. 190. 
Disjunction: §05, n. 227. 
Disjunctive normal form: n. 299. 
Disjunctive syllogism: 15.9, n. 189, 
n. 190, n. 191.
Disjunctively valid: 45.5.
Disproof: n. 2.
Distributive laws: see complete 
distributive laws.
Doctrinal function: n. 529, n. 537. 
Domain (of a relation): n. 517. 
Domain of individuals: §43.
Double negation, complete law of: 
n. 163, tl54.
Double negation, converse law of: 
n. 163, f222, 26.13.
Double negation, law of: fI04, n.
163, •j‘221.
Druckt aus: n. 16.
Dual: §16, §37, 48.11, §51, n. 501. 
Dual of a metatheorem: n. 354. 
Dual of a theorem schema: §37. 
Duality, principle of: *161, *372, 
48.11, 55.0.
D l, D2, D3, D4, D5, D6, D7, D8, 
D9, D10, D ll: §11.
D12: §24.
D13, D14, D15, D16, D17: §30. 
D18, D19: §48.
D20, D21: §50.
D22, D23: §52.
D24: §55.
E: §48.
E: 48.0.
£: §48.
E: n. 91.
Effectiveness: §07, n. 119, §12, n. 
183, n. 535.
Elementary arithmetic: §55, n. 522. 
Elementary number theory: §55, 
n. 520, n. 522.
Elementary part: §30, 38.13, §44, 
n. 423, §50.
Elementary syntax: §08. 
Elimination problem; 52.6.
Empty class: §04.
Equality: n. 43, §48, §52, n. 502. 
Equality by definition; n. 168. 
Equivalence: §05, n. 227. 
Equivalence of logistic systems: §23, 
n. 202.
Erweiterter Aussagenkalkul: n. 224. 
Excluded middle, law of: 15.0(10). 
Excluded middle, weak law of: 26.13. 
Exclusive disjunction: §05. 
Existential closure: §43, §54. 
Existential import: n. 441. 
Existential quantifier: §06. 
Expansion of a wff with respect to 
negation: §23.
Explicative definition; n, 168. 
Exportation, law of; 15.0(3). 
Express: §01, n. 16.
Extended propositional calculus: 
§28.
Extensionality, axioms of: n. 590. 
External to an occurrence of a 
quantifier: §39.
F7: §48.
F7p: §48.
F7p: §48.
F1: beginning of Chap. III.
Fi: 39.11.

---


I N D E X  O F  D E F I N I T I O N S
303
F*b: 39.10.
Fgh: 39.12.
F>: 38.9.
Fla: 30.4.
FJ‘: §55.
Flh: §30.
F1*: 38.6.
Fj,p: 41.2.
Flm: 38.10.
Fjm: 38.11.
F\'m: §40.
Flp; §30.
F*p: 46.24.
F*p: §40.
F1'1: §30.
F1-2: §30.
F2: §50.
F2!: §58.
F2,n: §50.
F2^n: §58.
F2P: §50.
F2lp: §58.
F»<w>: §56.
F2/m: §58.
F |/a,p: §58.
F2/tt,{r); 59.0.
F2'1: beginning of Chap. V, §50. 
F f : §58.
F2'2: beginning of Chap. V, §50. 
F|'2: §58. 
f: §05, §10.
/; §10, §28, §50(D20).
False (proposition): §04.
False (sentence): see true (sentence). 
Falsehood (i.e., the truth-value 
falsehood): §04.
Falsifying assignment: §44. 
Falsifying system of truth-values: 
§46.
Final bracket; §14,
First level: §58. n. 578.
First type-class: n. 578.
First-order arithmetic: §55.
Form: §00, §07, n. 124.
Form: §02, n. 25, n. 26, n. 117.
Formal axiomatic method: §07.
Formal equivalence: §06, n. 104, 
n. 305.
Formal 
implication: 
§06, 
n. 104, 
n. 305.
Formal logic: §00.
Formalized language: §00.
Formation rules: §07.
Formula: §07.
Formulations of the propositional 
calculus: beginning of Chap. I, 
§25.
Free occurrence of a variable: §06, 
n. 117, §30, 38.6.
Free variable: §02, n. 28, n. 36, n. 52, 
§30, §50.
Full conjunctive normal form: §29, 
n. 299, 39.8.
Full disjunctive normal form: 24.9, 
n. 237, §29, n. 299, 39.3.
Full many-valued propositional cal­
culus: §29.
Full propositional calculus: §29.
Function: n. 26, §03, n. 39.
Function concept: §03.
Function from . . .  to: §03.
Function in extension: §03.
Function of: §03.
Function of two arguments: §03.
Function of two variables: n. 42.
Functional abstraction: §03.
Functional calculus of first order: 
beginning of Chap. HI.

---


364
I N D E X  O F  D E F I N I T I O N S
Functional calculus of first order 
with equality: §48.
Functional calculus of second order: 
beginning of Chap. V.
Functional constant: §05, §30. 
Functional variable: §30.
Gedanke: §04.
General name: n. 4, n. 6. 
Generalization, rule of: *301, *401, 
*50 L.
Generalized upon: §30.
Godel’s completeness theorem: §44, 
**4.40.
Henkin’s completeness theorem: 
§54, **546.
Higher protothetic: n. 229.
Hilbert arithmetic: n. 524.
Hold between: §04.
Hold for (an argument): §04. 
Hypothetical syllogism: 15.9.
/: §48.
(ID): §55.
id: §55(D24), n. 543.
Idempotent laws: n. 186.
Identity: see equality.
If . . . then: n. 89.
Immediate inference: n. 115. 
Immediately infer: §07.
Imperative logic: n. 63. 
Implication: §05.
Implicational propositional calculus: 
§26.
Implicative normal form: 15.4. 
Implies: n. 89.
Importation, law of: 15.0(4). 
Impredicative definition: §58, n. 573, 
n. 574.
Improper symbol: §05, n. 117, § 10, 
§30.
Inclusive disjunction: §05.
Inconsistent class of wffs: §45, §54.
Inconsistent with a class of wffs: 
§45, §54.
Independence example: §55.
Independence (of axioms and prim­
itive rules of a logistic system): 
§19, n. 195, n. 468.
Independence (of postulates): §55.
Independent: §19.
Independent as to consequences: §55.
Independent as to provability: §55.
Independent connective: §24.
Indirect proof, law of: 26.11.
Individual constant: §30.
Individual variable: §30.
Individuals: §30, n. 309.
Infin ax: n. 559, n. 581.
Infinity, axiom of: §57, n.559, n. 560.
Informal axiomatic method: §07.
Initial bracket: §14.
Initially placed: §39.
Instance (of a theorem schema): §33.
Integral domain: §55.
Intensional propositional variable: 
§04.
Interpretation (of a logistic system): 
§07, n. 199.
Interpretation (of a mathematical 
theory): n. 536.
Interpretation of Fjp: §54.
Interrogative logic: n. 63.
Intertypical variables: n. 87.
Intuitionism: see mathematical in- 
tuitionism.
Intuitionistic functional calculus of 
first order: 38.6.
Intuitionistic propositional calculus: 
§26.

---


I N D E X  O F  D E F I N I T I O N S
365
Isomorphic: §55.
Judgment: §04.
K : n. 91.
Language: §07, n. I ll, n. 116.
Law of affirmation of the con­
sequent: f ! 02, f202.
Law of assertion: 12.7.
Law of commutation: 12.7 
Law of composition: 15.0(5).
Law of contradiction: 15.0(9), 26.13. 
Law of contraposition: 15.0(6), f223,
26.13.
Law of denial of the antecedent: 
f 123, f220, §26.
Law of double negation: ^104, n. 163,
f 221.
Law of excluded middle: 15,0(10). 
Law of exportation: 15.0(3).
Law of importation: 15.0(4).
Law of indirect proof: 26.11.
Law of reductio ad absurdum: §26,
26.13.
Law of triple negation: 26.13. 
Laws of absorption: 15.8.
Laws of De Morgan: 15,8, n. 188. 
Laws of tautology: n. 186.
Leading principle: 15.9(1), 46.22. 
Level: n. 578.
Lexicographic order: §44, n. 410. 
L K : n. 365, n. 366.
Logic; §00.
Logical axioms: §07.
Logical consequence: n. 533. 
Logical form: n. 26, n. 124.
Logical primitive symbols*. §07. 
Logical syntax: §08.
Logikkalkul: n. 125.
Logique algorithmique: n. 125. 
Logische Funktion: n. 458.
Logischer Calcul: n. 125.
Logistic: §07, n, 125.
Logistic method: §07.
Logistic system: §07.
Lowenheim's theorem: **450. 
Major premiss: §10, n. 162, §30. 
Many-one: n. 556.
Many-sorted functional calculus (of 
first or higher order): 55.24. 
Many-valued function: n. 41. 
Many-valued propositional calculus: 
§19.
m-ary: see also n-ary. 
w-ary functional abstraction: §03. 
w-ary functional calculus of first 
order: §40.
w-ary-n-ary operator: §06.
Mate of a bracket: §11.
Material equivalence: §05.
Material implication: §05, n. 188. 
Material non-equivalence: §05. 
Material non-implication: §05. 
Mathematical intuitionism: §26, n. 
183, n. 535.
Mathematical induction, postulate(s) 
of: §55.
Mathematical logic: §07, n. 125. 
Matrix: §39.
Matter. §00, §07.
Maximal consistent class of closed 
wffs: §54.
Maximal consistent class of wffs. 
§45.
Mean: n. 7.
Meaning-: n. 7, n. 13, n. 20 
Meaningfulness: n. 120.
Members of a class: §04.
Mention of a word: §08. 
Meta-language: §07.

---


B66
I N D E X  O F  D E F I N I T I O N S
Metamathematics: n. 110, n. 139. 
Metatheorem: §09.
Minimal functional calculus of first 
order: 38.10, 38.11.
Minimal propositional calculus: §26, 
n. 210.
Minimalkalkiil: n. 210.
Minor premiss: §10, n. 162, §30. 
Modal logic: n. 2.
Model: n. 451, §55.
Modus ponendo tollens: 15.9.
Modus ponens: §10, n. 162, 15.9. 
Modus ponens, rule of: *100, *200, 
*300, *400, *500.
Modus tollendo ponens: 15.9.
Modus tollens: 15.9.
Multiplicative axioms: n. 581.
N: n. 91.
Name: §01, n. 4, n. 7.
Name of: §01.
Name relation: §01, n. 8. 
n-ary: see also m-ary. 
w-ary connective: §05. 
w-ary form: §02, §30, §50. 
n-ary function: §03. 
n-ary functional calculus of second 
order: §50.
Natural number: §30, n. 521. 
Negation: §05, n. 227.
Non-assertive use of a sentence: 
n. 65.
Non-conjunction: §05, n. 207. 
Non-disjunction: §05. 
Non-equivalence: §05. 
Non-implication: §05.
Non-normal interpretation: 19.10, 
n. 199.
Non-vacuous occurrence of a quan­
tifier: §39.
Normal form: see conjunctive normal 
form, disjunctive normal form, 
full conjunctive normal form, full 
disjunctive normal form, impli­
cative normal form, normal form 
(with respect to conditioned dis­
junction), prenex normal form, 
prenex-disjunctive normal form, 
Skolem 
normal 
form, 
Skolem 
normal form for satisfiability.
Normal form (with respect to con­
ditioned disjunction): 24.10.
Normal interpretation: 19.10, n. 199.
Normal system of domains: §54,54.3.
wth-order arithmetic: §55.
Null class: §04, n. 77.
Null formula: §10.
Object language: §07.
Oblique use of a name: §01.
Occurrence as a P-constituent: §46.
Occurrence as a truth-functional 
constituent: §46.
Of the first level: §58.
One-many: n. 556.
One-to-one correspondence: n. 564.
One-to-one relation: n. 556.
One-valued singulary function: §03.
Operand: §05, §06.
Operation: n. 112.
Operator: n. 64, §06, n. 112.
Operator variables: §06.
Optative logic: n. 63.
Order: n. 578.
Ordered pair: n. 88.
Ordinary use of a name: §01.
Organic (axiom): §25.
Ostensive definition: n. 168.
P: §27. See also by P, use P.
PB: §25.

---


I N D E X  O F  D E F I N I T I O N S
367
P,,: 23.6.
Pg; §25.
PH: §26, §29.
PH.: n. 267.
Pj: 29.4.
PL: §25.
PL: 23.7.
P,: 23.8.
PLo: §27.
PN: §25.
Pn; §25.
PR: §25.
Pr: §29.
Ps: 23.9.
Pw: 12.7.
Pw; §25.
Pr : 26.14.
P^: §29, 29.2.
P*: §26.
Pr' §10.
Pit.: 12.2.
P2: §20.
P2L: 23.0.
Pf: 26.3(2).
Pfv: 26.0.
PE: 26.3(1).
PE/: 26.4.
PEN: 26.4.
P^: 18.3.
Pj.: 18.4.
P's- §26.
PW: 26.19.
P[: 26.18.
PrK: §29.
Pf: 26.19.
P“‘: 26.21.
P?: §26.
Pp: §26, §29.
P+: 19.6, §26, §29.
Parentheses: §05, n. 81, n. 82.
Parenthesis-free notation of Luka­
siewicz: n. 91, 12.2.
Parity (of an occurrence of an elemen­
tary part): n. 508.
Partial order: 55.22.
P-constituent: §46.
Peano's postulates; §55, n. 525.
Pegasus: n. 18.
Peirce's law: 12.6, n. 187.
Perfect number: n. 317.
Personal name: n, 18.
Platonism: n. 535.
Positive implicational propositional 
calculus: §26, §29.
Positive propositional calculus; §26, 
§29.
Postulate: §07, n. 128, §55.
Postulates as added axioms of a 
logistic system: §55.
Postulates as propositional func­
tions: §55, n. 529.
Postulate (s) of mathematical induc­
tion: §55.
Pr&dikat: §49, n. 458.
Prddikat&nkalkul: §49.
Pradikatensymhol: n. 458.
Precede: 55.22.
Predicate: §49, n. 458.
Predicative: §58.
Predicative functional calculus of 
second order: §58.
Predicative second-order arithmetic: 
§58.
Predicative third-order arithmetic: 
n. 583.
Predicative variables: §58.
Prefix: §39.
Premiss: n. 3, §07, n. 162.

---


368
I N D E X  O F  D E F I N I T I O N S
Prenex normal form; §39.
Prencx-disjunctive normal form; 
39.5.
Primitive basis: §07, n. 117.
Primitive constant: n. 117, §10.
Primitive proper name: §01.
Primitive semantical rule: n. 168.
Primitive symbols: §07.
Principal dual: §16, §37.
Principal implication sign: §10, §20, 
§30.
Principal interpretation: §07.
Principle of duality: *161, *372, 
48.11, 55.0.
Proof: §07, n. 121, §10, n. 164.
Proof from hypotheses: §13, §36, §51.
Proper name: §01, n. 4, n. 6, n. 10, 
n. 18.
Proper subclass: n. 564.
Proper symbol: §05, n. 117, §10.
Property: §04.
Propositio mentalis: §04.
Proposition: §04, n. 68, n. 69.
Propositional calculus: beginning of 
Chap. I, §29.
Propositional calculus with quan­
tifiers: n. 229.
Propositional form: §04, n. 117, §10, 
§30, §50.
Propositional function: §04, n. 74.
Propositional variable: §04, n. 64, 
§30.
Protothetic; §28.
Pure functional calculus of first or­
der: §30.
Pure functional calculus of first or­
der with equality: §48.
Pure functional calculus of second 
order: §50.
Pure predicative functional calculus 
of second order: §58.
Pure ramified functional calculus of 
second order and level w: §58.
Purely designative occurrence: n. 20.
Quantification: §06, §49.
Quantifier: n. 64, §06, §49.
Quantifier-free: §32.
Quotation marks: §08, n. 136.
R: n. 91.
Ramified functional calculi of second 
order: §58.
Ramified 
functional 
calculus 
of 
second order and level co: §58.
Ramified second-order arithmetic: 
§58.
Ramified second-order arithmetic of 
level co; §58.
Range of a class: §04.
Range of a function: §03.
Range of a variable: §02, §43.
Range of arguments of a function: 
§03.
Range of values of a function: §03.
Range-members of a class: §04.
Real definition: n. 168.
Real variable: n. 28.
Recursion equations: n. 526.
Reducibility, axioms of: §59.
Reductio ad absurdum, special law 
of: §26.
Reductio ad absurdum, law of: §26.
Reduction class*. §47.
Reduction of the decision problem: 
§47.
Reduction of the decision problem 
for satisfiability: §47.
Reduction of the decision problem 
for validity; §47.

---


I N D E X  o r  D E F I N I T I O N S
:mh>
Reflexive law of equality: §48, f520.
Reflexive law of (material) impli­
cation: 1120, f211.
Related 
rows: n. 439.
Relation: §04.
Relation concept: §04.
Relation in extension; §04.
Relation in intension: §04.
Relative consistency: §17.
Relative product: n. 518.
Relevant value (of a form used as 
operand of a connective): §05.
Representative of a wff in P1; §23.
Representing form; §55.
Resultant (of a wff of FJ); 52.6.
Row-pair; n, 440.
Rule of alphabetic change of bound 
(individual) variable; *350, *402, 
*502.
Rule of alphabetic change of bound 
propositional and functional var­
iables; *515.
Rule of generalization: *301, *401, 
*501.
Rule of inference: §07.
Rule of modus ponens: *100, *200, 
*300, *400, *500.
Rule of procedure: §07.
Rule of substitution for individual 
variables: *351, *403, *503.
Rule of substitution for n-ary func­
tional variables: 
*352„, *404„, 
*510w.
Rule of substitution for propositional 
variables: *3520, *4040, *510o.
Rule of substitution (in the propo­
sitional calculus): *101, *201.
Rule of substitutivity of equality; 
*529.
Rule of substitutivity of (material) 
equivalence: *159, *342, *513. 
Rules of definition: n. 168.
S: §10, §12, §30.
S: §54.
S„: § « .
V  §45.
S: §30.
S: §35.
S: §55.
Satisfiable: §43, n. 407, §54. 
Satisfiable in a domain §43, §54. 
Satisfiable with respect to a system 
of domains: §54.
Satisfied by (a value of a variable): 
§04.
Satisfied by (an argument): §04. 
Satisfy (a propositional form): §04. 
Schema of proof: §33.
Scope: §39.
Secondarily satisfiable: §54. 
Secondarily valid: §54.
Secondary interpretation of Fgp: §54. 
Second type-class: n. 578. 
Self-distributive law of (material) 
implication: +103, n. 163, t203. 
Self-dual, §16, §37.
Semantical decision problem: §15, 
§46.
Semantical rules: §07. n. 168. 
Semantical theorem: §09. 
Semantics: §09, n. 140.
Sense: §01, n. 13, n. 37.
Sense of a sentence: §04.
Sense value: n. 27. 
Sense-concurrent: n. 30.
Sentence: 
§04, 
n. 117, 
§10, 
§30, 
39.10, §50.
Sentence connective: §05.

---


370
INDEX OF DEFINITIONS
Sentential calculus: n. 252,
Sequenzen: §29, n. 295, 39.11.
Set: §04.
sfp: n. 318.
Sheffer's stroke: §05, n. 207.
Simple applied functional calculus 
of first order: §30.
Simple applied functional calculus 
of first order with equality: §48.
Simple calculus of equality: §48.
Simple functional calculus of second 
order: beginning of Chap. V, §58.
Simple operator: §06.
Simple order: 55.22.
Simultaneous substitution: §12.
Simultaneously satisfiable (class of 
wffs): §45, n. 415, §54.
Simultaneously satisfiable in a do­
main: §45, §54.
Simultaneously satisfiable with re­
spect to a system of domains: §54.
Single-row: n. 440.
Singular name: n. 4.
Singulary: n. 29.
Singulary associated formula of the 
propositional calculus: n. 318.
Singulary connective: §05.
Singulary form: §02.
Singulary function: §03.
Singulary functional abstraction op­
erator: §06.
Singulary functional 
calculus 
of 
first order: §30.
Singulary-singulary operator; §06.
Sinn: n. 13, n. 14.
Skolem normal form: §42,
Skolem normal form for satisfiabili­
ty: §43.
Skolem-Lowenheim theorem: **455.
j Solution of the decision problem in 
a special case: n. 421.
Sound interpretation: §07, n. 173, 
§19.
Sound language: §07.
Special law of reductio ad absurdum: 
§26.
Special principle of duality for (ma­
terial) equivalences: *165, *374.
Special principle of duality for (ma­
terial) implications: *164, *373.
Specialized system of primitive con­
nectives: 24.7.
Stand in (a relation): §04.
Subclass: n. 564.
Subrelation: n. 556.
Substitution for individual variables, 
rule of: *351, *403, *503.
Substitution for «-ary functional 
variables, rule of: *352n, *404n, 
§49, n. 461, *510n.
Substitution for propositional var­
iables, rule of: *3520, *4040, *5100.
Substitution (in the propositional 
calculus), rule of: *101, *201, §29.
Substitution instance: §31, §51.
Substitutivity of equality, rule of: 
*529.
Substitutivity of (material) equiva­
lence, rule of: *159, *342, *513.
Successor relation: 48.23, §55.
Suppositio formalis: n. 134.
| Suppositio materialis: n. 134.
! Syllogism: 15.9, n. 189, n. 190, n.
| 
191, 46.22, n. 441.
( Symbolic logic: §07, n. 125.
] Symmetric binary form: §03, n, 56.
| Symmetric function: §03.
| Syncategorematic: §05.

---


INDEX OF DEFINITIONS
371
Synonymous: §01.
Syntactical constant: §08, n. 133. 
Syntactical theorem: §08. 
Syntactical variable: §08.
Syntax: §08. 
t: §05, §10.
i: §11 (Dl), §28, §50(D21). 
Tautologous: 46.6(1).
Tautology: §15, §19, §23. 
Tautology, laws of: n. 186.
Term: n. 4.
Term: 39.10.
Ternary form: §02.
Ternary relation: n. 78.
Theorem: §07, §10.
Theorem schema: §33.
Theoretical syntax: §08. 
Theoretische Logik: n. 125.
Theory of deduction: n. 252. 
Theory of implication: n. 224. 
Thing: n. 9, n. 148.
Transitive law of equality: §48, f522. 
Transitive law of (material) equiv­
alence: f 157.
Transitive law of (material) im­
plication: 12.4, "f 141.
Triple negation, law of: 26.13.
True for (a system of values of the 
free variables): §04.
True (proposition): §04.
True (sentence): §04, §09, n. 172,
43.2, n. 512.
Truth (i.e., the truth-value truth): 
§04.
Truth 
(in 
Tarski's 
sense): 
§09, 
n. 142, n. 143, n, 407, n. 512. 
Truth-function: §05, n. 92. 
Truth-functional biconditional: §05. 
Truth-functional conditional: §05.
Truth-functional constituent: §46. 
Truth-functional variable: §28. 
Truth-table: §15, §24.
Truth-table decision procedure: §15, 
§29.
Truth-value: §04, §19.
Type: n. 578.
Type-class: n. 578.
Types, theory of: n. 87, n. 148. 
Typical ambiguity: n. 149, n. 585. 
Unary: n. 29.
Undefined terms: §07.
Uniform continuity: n. 102. 
Universal cl^ss: §04.
Universal closure: §43, §54, §55. 
Universal quantifier: §06. 
Univocacy: §01.
Unsound interpretation: §07. 
Unsound language: §07.
Use of a word (distinguished from 
mention): §08.
Use P: §31, n. 324.
Vacuous occurrence of a quantifier: 
§39.
Valid: §43, n. 407, 43.2, §53, §54. 
Valid in a domain; §43, §54.
Valid with respect to a system of 
domains: §54.
Validity in Flh: 43.2.
Validity in the extended proposition­
al calculus: §53.
Validity in the pure functional cal­
culus of first order: §43.
Validity in the pure functional cal­
culus of second order: §54. 
Valuation: 45.4.
Value for (a model): §55.
Value for a null class of variables: 
§10, n. 312.

---


372
INDEX OF DEFINITIONS
Value in the syntactical sense: n. 143, 
§43.
Value of a constant: §10, n. 312. 
Value of a form: §02, n. 312.
Value of a function: §03.
Value of a variable: §02, §43.
Value of a wff: §15, §23, §43.
Value of a wff of Px: §15.
Value of a wff of Pa: §23. 
Variable: §02, n. 24, n. 26, n. 31, 
n. il2 , n. 117.
Variable quantity: n. 62.
Variant of a wff: §13, §36.
Variant proof: §13.
Vicious-circle principle: §58, n. 574. 
(w): §56.
Weak law of 
excluded middle: 
26.13.
Weaker than: §57.
Weight of a functional variable: 
46.11(2).
Well-formed formula: §07, n. 310, 
Well-ordering: 55.22.
Well-ordering of the individuals, 
axiom of: §56, 
wf: §10.
wf part; n. 200. 
wff: §10. 
wffs: §10.
(*): §06, §30(D13).
§55.
Z x ' §5 5 - 
F: **452, §54. 
r  b B: §45, §54. 
te: §03, §06.
77: §30, §55.
Z: §30, §55.
0: 55.14.
0-ary connective; §24.
0-ary-w-ary operator; n. 99.
1: 55.14.
=  : n. 43.
=  : §48(1)18), §52(D22), §55, §58. 
= 2: n. 580.
= 3: n. 580.
+  : §48(D19), §52(D23).
# a: n. 580.
* 3: n. 580.
[— : n. 65.
h  n. 65, §12, §13, §30, §36, n. 343.
§05, §11 (D2), §20, §30. 
v: §05, §11 (D4). 
v: §05, n. 169, §11 (D10).
«=: §05, §11 (D8).
<£: §05, §11 (D3).
=>: §05, §10, §20, §30.
= V  §28.
3 . :  §06, §30(D15).
=>„: §06, §30(D15). 
p :  §05, §11(D9).
=  : §05, §11 (D6).
3 , :  §06, §30(D16).
§06, §30(D18). 
p :  §05, §11 (D7).
| : §05, §11 (D ll), n. 207.
I*: §30(D17).
.:  §06, §11, n. 165.
(ix): 
§06, n. 546.
V: §06, §30.
3: §06, §30(D14).
§11-
- k. §29, 39.10.
+ : §32 (proof of **323). 
t: §32(proof of **323).
(col), (co2), (oo3), (oo4), 
(co5): 
§57.
(cc6), (co7), (008), (co9), (oolO):
57.2.

---


Index o f Authors
Ackermann, Wilhelm: n. 28, n. 125, 
n. 210, n. 299, §29, n. 430, n. 432, 
n. 435, n. 447, §49, n. 458, n. 459, 
n. 
468, n. 503, n. 505, n. 507,
n. 
524, n. 555, n, 557, 
n. 579,
n. 588.
Aldrich, Henry: n. 68.
Behmann, Heinrich: n. 299, §29, 
n. 362, §46, 48.14, §49, n. 457, 
n. 477, n. 478, n. 504, 52.11.
Beltrami, Eugenio: n. 539.
Bernays, Paul: n. 28, n. 119, n. 168, 
n. 221, §29, n. 246, n. 250, n. 258, 
n. 
266, n. 267, n. 281, n. 292,
n. 
299, n. 351, n. 365, 
n. 409,
n. 420, §46, 46.10, §49, n. 458, 
n, 460, n. 478, n. 519, §55, n. 524, 
n. 526, n. 535, §57, n. 561, n. 563.
Bernoulli, Jean: §03.
Bernstein, B. A.: n. 199.
Berry, G. D. W.: n. 107, n. 140.
Beth, E. W.: n. 462.
Boehner, Philotheus: n. 188.
Bolyai, Janos: n. 539.
Bolzano, Bernard: n. 565.
Boole, George: n. 125, n. 237, §29, 
n. 240.
Brouwer, L. E. J.: §26.
Burkhardt, H.: n. 59.
Cantor, Georg: n. 541, n. 550, n. 551, 
n. 565.
Carnap, Rudolf: n. 5, n. 17, n. 57, 
n. 70, n. 87, n. 110, n. 116, §07,
n. 131, §08, n. 139, n. 142, n. 168, 
19.10, n. 199, n. 309, n. 458, §49, 
n. 519, n. 529, n. 589.
Castillon, G. F.: n. 125, n. 239.
Cavailles, Jean: n. 563.
Cervantes, Miguel de: n. 192.
Church, Alonzo: n. 19, n. 20, n. 100, 
n. 119, n. 140, n. 199, 19.12, 
n. 239, n. 332, n. 351, n. 420. 
n. 461, 55.23(7), n. 563.
Chwistek, Leon: n. 588, n. 589, 
n. 590.
Clairaut, A. C.: §03.
Couturat, Louis: n. 125, n. 239, §29, 
n. 251.
Coxeter, H. S. M,: 55.23(3).
Curry, H. B.: n. 100, p. 377.
Dedekind, Richard: n. 525, n. 526, 
n. 541, n. 563, §57, n. 565.
Delboeuf, J. R. L.: n. 125.
De Morgan, Augustus: n. 125, n. 188, 
§29, n. 240, n. 241.
Dewey, John: n. 541.
Dienes, Z. P.: 19.12.
Dirichlet, G. Lejeune: §03, n. 59.
Dreben, Burton: n. 442.
Durr, Karl: n. 239.
Eaton, R. M.: n. 70.
Euclid: 48.0.
Euler, Leonhard; §03, n. 58, n. 59, 
n. 62.
Feys, Robert: n. 100.
Fitch, Frederic B.: n. 107, n. 579.

---


374
INDEX OF AUTHORS CITED
Fourier, J. B. J.; n. 59.
Fraenkel, Adolf; n. 635, n, 588.
Fr^chet, Maurice; n. 553.
Frege, Gottlob: §01, n. 5, n. 7, n. 12, 
n, 13, n. 14, n.. 16, n. 17, n, 20, 
§02, n. 32, n. 33, n. 37, §03, §04, 
n. 65, n. 66, n. 67, n. 71, n. 74, 
n. 103, n. 114, §08, n. 136, n. 139, 
n. 225, §29. §49, n. 502, n. 545.
G^galkine, J. J.: n. 185, n. 186, n. 435.
Gentzen, Gerhard: §26, n. 212, §29, 
n, 270, n. 294, n. 295, n. 296, 
n. 365, n. 366, n.372, n.462, n. 509.
Gilman, B. I.: n. 550.
iilivenko, V , n. 210, SJjB.lS, n.. 213, 
§29, n. 271,
Godel, Kiiit; n. 145, n L46, 20.12, 
20.16, n. 218, §29, n. 284, n. 358, 
41.1, n. 430, n. 433, n. 438, n. 446, 
n. 461, §49, n. 464, n. 466, n. 473, 
n. 485, §55, n. 523.
Gotlind, Erik: §29, n. 248.
Gutberlet, Const.: n. 550.
Hahn, Hans: n. 589.
Hankel, Hermann: §03, n. 61.
Hausdorff, Felix: n. 549.
Hempel, C. G.: n. 2.
Henkin, Leon: n. 288, §29, §49, 
n. 465, n.486, n.510, n.513, n.558.
Herbrand, Jacques: n. 186, n. 221, 
§29, n. 290, n. 430, n. 431, n. 432, 
46.23, n. 442, 46,24, §47, n. 443, 
§49, n, 462, n. 464, n. 479, n. 546.
Hertz, Paul: n. 295.
Heyting, Arend: §26, n. 209, n. 210, 
§29, n. 283.
Hilbert, David: n. 28, n. 110, n. 119, 
n. 125, n. 139, n. 168, §17, §26, 
n. 210, n. 221, n. 250, §29, n. 266,
n. 267, n. 292, n. 299, n. 351, 
n,420, §49, n. 458, n. 459, n. 460, 
n. 468, n. 478, n. 519, §55, n. 524, 
n. 526, n. 539, n. 540, 55.23(4), 
n. 555, n. 557, n. 579, n. 588.
Huntington, E. V.; §29, n. 282, §55, 
n. 541, 55.23(6).
Itelson: n. 126.
Jaikowski, Stanislaw, n. 177, n, 217, 
§29, n. 293, 29.4.
Johansson’, Ingebrigt: §26, n. 210, 
n. 219.
j0rgensen, J0rgen; n. 239.
Kalmar, Laszlo: §29, n. 286, n. 288, 
t\. 430, n.433, n.445, n.446, n. 447, 
n. 448, n. 449, n. 450, §49, n. 472, 
n. 526. '
Kemeny, John G.: §18, n. 318.
Keynes, J. N.: n. 26.
Keyser, C. J.: n. 529, n. 537.
Kleene, S. C.: n. 119, n. 131, n. 142, 
n. 176, n. 351, n. 357, n. 461.
Klein, Felix: n. 539.
Kolmogoroff, A.: §26, n. 210, n. 219, 
26.20, n. 357.
Kuratowski, C.: 55.23(8), 55.23(9).
Kiirschak, J.: n. 509.
Lalande, Andre: n. 125.
Lambert, J. H.: n. 239.
Langer, Susanne K.: n. 26, n. 191.
Langford, C. H.; n. 136, §49, n. 471.
Leibniz, G. W. v.; §03, n. 125, n, 239, 
n. 502.
LeSniewski, Stanislaw: n. 113, n. 168, 
§25, n. 213, n. 214, n. 228, n. 233, 
§29, n. 260, n. 261.
Levi, Beppo: n. 112.
Lewis, C. I.: n. 239, §29, n. 249.
Liard, Louis: n. 125.

---


INDEX OF AUTHORS CITED
375
Lindenbaum, Adolf: 55.23(8).
Lobachevsky, N. I.: n. 539.
Lorenzen, Paul: n. 526.
Lowenheim, 
Leopold: 
§47, 
§49,
n. 455, n, 475, n. 504.
Lukasiewicz, Jan: n. 91, n. 177, 
n. 188,18.4, § 19,19.8, § 28, n, 224, 
§29, n. 243, n. 255, n. 257, n. 263, 
n. 265, n. 273, n. 276, n. 278, n. 280, 
§49.
MacColl, Hugh: n. 26, §29, n. 242.
Macfarlane, Alexander: n. 125.
McKinsey, J. C. C.: n. 212, n, 214, 
n. 217, §49, n. 467, n. 468.
MacLane, Saunders: n. 131.
Malcev, A.: n. 451.
Menger, Karl: n. 177.
Meredith, C. A.: n. 257.
Mihailescu, Eugen Gh.: n. 214, n. 215, 
§29, n. 264.
Mill, J. S.: n. 6, n. 14, n. 16.
Mitchell, O. H.: n. 103, §49, n. 453.
Morris, C. W.: n. 140.
Mostowski, Andrzej: n. 560, §57, 
n. 566, n. 568, n. 572.
Murphy, J. J.: n. 241.
Neumann, J. v.: n. 28, n. 112, n. 113, 
§29, n. 250.
Nicod, J. G. P.: n. 207, §25, §29, 
n. 247, n. 253.
Northrop, E. P.: n. 26.
Notcutt, Bernard: n. 87.
Ockham, William of: §04, n. 188.
Peano, Giuseppe: n. 28, §05, n. 125, 
n. 152, n.165, §29, §49, §55, n. 525, 
n. 539.
Peirce, C. S.; n. 3, n. 67, n. 103, 
n. 125, n.187, n. 207, n. 226, n. 241, 
§ 29, n. 277, n. 299, §49, n. 453,
n. 469, n. 502, n. 525, n. 526, 
n. 550, §57, n. 565.
Pepis, J6zef: n. 448, n. 449.
Petrus Hispanus: n. 68.
Philo of Megara: n. 188.
Pieri, Mario: 55.23(5).
Pil'cak, B. 0 .: n. 212.
Ploucquet, Gottfried: n. 125, n. 239.
Poincare, Henri: §58, n. 573, n. 574.
Poretsky, Platon: n. 125.
Post, E. L.: n. 119, n. 193, §18, §24, 
n. 206, §29, n. 274, n. 277, n. 285, 
n. 297.
Quine, W. V.: n. 20, n. 29, n. 90, 
n. 107, §08, n. 152, §15, n. 221, 
n. 244, § 29, n. 287, §46, n, 427, 
n. 428, a. 436, §49, n. 461, n. 478, 
n. 480, n. 588.
Ramsey, F. P.: §49, n. 482, n. 589.
Rasiowa, Helena: 25.5, §29, n. 248.
Rescher, Nicholas: 19.12.
Rieger, Ladislav; n. 212.
Riemann, Bernhard: n. 41, §03, n. 60.
Rose, Alan: n. 280.
Rose, Gene F.: n. 217.
Rosser, j. B.: n. 100, §29, n. 351.
Russell, Bertrand: n. 5, n. 12, n. 13, 
n. 17, n. 28, n. 65, n. 74, n. 77, 
§05, n. 92, n. 104, n. 107, n. 125, 
n. 165, n. 171, §28, n. 224, n. 225, 
n. 226, §29, n. 244, n. 245, n. 252, 
n. 297, n. 309, §49, n. 454, n. 461, 
n. 502, n. 535, n. 545, n. 546, 
n. 559, §58, n. 574, n. 575, n. 577, 
n. 578, n. 579, n. 581, n. 585, §59, 
n. 587, n. 590.
Schmidt, Arnold: n. 554.
Scholz, Heinrich: n. 26, n. 263, §29, 
n. 268, §49, n. 474.

---


376
INDEX OF AUTHORS CITED
Schonfinkel, Moses: n. 100, n. 409, 
§46, 40.10, §49, n. 481, §57, n. 581.
Schroder, Ernst: n. 77, n. 125, n. 241, 
§29, §49, n. 503.
Schroter, Karl: n. 177, §29, n. 268.
Schiitte, Kurt: n. 409, n. 430, n. 433, 
§57, n. 562, p. 377.
Sheffer, H. M.: n. 207, §29.
Skolem, Thoralf: n. 430, n. 432, 
n. 434, n. 437,46.13, n. 446, n. 452, 
§49, n. 456, n. 464, n. 475, n. 483, 
n. 504, n. 547.
Slupecki, Jerzy: §29, n. 279.
Sobociftski, Boleslaw: n. 238, §29, 
n. 256.
Stackel, Paul: n. 570.
Stamm, Edward: n. 207.
Stone, M. H.: n. 185, n. 186, n. 216.
Surdnyi, J4nos; n. 446, n. 448, n. 449, 
n. 450.
Tarski, Alfred: n. 87, n. 110, n. 136, 
n. 139, §09, n. 142, n. 143, n. 146, 
n. 193, n. 212, §28, n. 224, n. 230, 
n. 233, n. 236, n. 243, §29, n. 258, 
n. 291, n. 314, n. 400, n. 462, n. 529, 
n. 533, n. 548, n. 559, n. 563, n. 571.
Thomae, J.: n. 139.
Trachtenbrot, B. A.: n. 450, §57, 
n. 567, n. 568.
Turing, A. M.: n. 119.
Turquette, A. R.: §29.
Vailati, Giovanni: n. 550.
Veblen, Oswald: n. 126, n. 127, 
n. 529, §55, n. 541, 55.23(1).
Venn, John: n. 125.
Wajsberg, Mordchaj: §25, n, 210, 
§26, n. 211, n. 212, n. 219, n. 220, 
§29, n. 254, n. 259, n. 262, n, 263, 
n. 269, n. 280, n. 288, n. 289, 
n. 298, p. 377.
Wang, Hao: n. 554.
Watts, Isaac: n. 68.
Weber, H.: n. 569.
Wernick, William; n. 206,
Weyl, Hermann: n. 139, n. 535, 
n. 574, §58, n. 576, n. 583.
Whately, Richard; n. 68.
White, Morton fir: n. 20.
Whitehead, A. N.; n. 5, n. 65, §05, 
n. 104, n. 165, §29, n. 244, n. 297, 
n. 309, §49, n. 470, n. 502, n. 559, 
§58, n. 577, n. 578, n. 579, n. 581, 
n. 585, §59.
Wittgenstein, Ludwig: §29, n. 275.
Young, J. W.: n. 126, n. 127, n. 529, 
55.23(1).
Zermelo, Ernst: §04, n. 75, n. 129, 
§09.