<!-- Source: Church, A. (1956). Introduction to Mathematical Logic. Chapter IV: The Pure Functional Calculus of First Order (pages 226-307). BibKey: Church1956 -->

40. An alternative form ulation. In the case of a functional calculus 
of first order having a sufficient apparatus of variables, a formulation is 
possible, as already remarked, in which rules of substitution are used (in 
addition to the rules of modus ponens and generalization) and the axiom 
schemata of §30 are replaced by basic instances of them—so that the number 
of axioms is then finite. In this section we give such a formulation, Fjp, of 
the pure functional calculus of first order.
The primitive symbols are the eight improper symbols listed in §30, the 
individual variables, the propositional variables, and for each positive inte­
ger n the n-ary functional variables. The formation rules, 40i-v are the same 
as 30i-v except that the references to functional constants and individual 
constants in 30ii are deleted. The same abbreviations of wffs are used as 
described in §30, including the definition schemata D3-17. The rules of 
inference are the following:
MOO. 
From 
B and A to infer B. 
(Rule of modus ponens.)
*401. 
From A, if a is an individual variable, to infer (a) A.
(Rule of generalization.)
*402. 
From A, if a is an individual variable which is not free in N and b 
is an individual variable which does not occur in N, if B results 
from A by substituting S()N| for a particular occurrence of N in A, 
to infer B. 
(Rule of alphabetic change of bound variable.)
*403. 
From A, if a and b are individual variables, if no free occurrence of 
a in A is in a wf part of A of the form (b)C, to infer §bA|.
(Rule of substitution for individual variables.)
*4040. 
From A, if p is a propositional variable, to infer S^A).
(Rule of substitution for propositional variables.) *
*404n. From A, if f is an n-ary functional variable and x lf x2, . . x n are 
distinct individual variables, to infer
*"JA|. 
(Rule of substitution for functional variables.)

---


m
AN ALTERNATIVE FORMULATION
219
The axioms are the five following: 
f405. 
p => *q => p 
f406. 
s ID
f407. 
~p => ~q => • q 13 p 
f408. 
p 13 x F(x) i> mp 13 (ar)F(ar)
|409. 
(aJFfc) i> F{y)
From results obtained in the preceding chapter (especially §35), there 
follows the equivalence of the systems F\v and Flp in the sense that every 
theorem of either system is a theorem also of the other. Hence also the de­
rived rules of Flp which were obtained in the preceding chapter may be 
extended at once to the system Fgp-
The developments of the following sections (§§41-47) belong to the theoret­
ical syntax of the pure functional calculus of first order, and—except the 
results of §41, which concern the particular formulation Fgp—’they apply 
to the pure functional calculus of first order indifferently in either of the 
formulations Flp or Fgp. Many of the results can be extended to other func­
tional calculi of first order, some even to an arbitrary functional calculus of 
first order in the formulation F1. But we shall confine attention to the pure 
functional calculus of first order, leaving it to the reader to make such 
extensions of the results where obvious.
We remark that the method of the present section, for obtaining a for­
mulation of the functional calculus of first order in which the axiom sche­
mata of F1 are replaced by a finite number of axioms, can be extended to 
any case in which functional variables of at least one type are present. 
Namely, the appropriate changes are made in the list of primitive symbols 
and in the formation rules. The rules of inference remain the same except 
that: (1) if individual constants are present, the appropriate changes are 
to be made in *403 and *404n to allow for them (as in *351 and *352n); and
(2) if any of the rules *404n become vacuous, they may be omitted. The 
five axioms remain the same as in Fgp if the required variables are present, 
and otherwise they receive an obvious modification.
In particular, for any positive integer m, a formulation Fg,m of the m-ary 
functional calculus of first order may be obtained from F\? by merely 
omitting from the list of primitive symbols all functional variables which 
are more than m-ary and omitting all the rules *404n for which n >  m. 
This formulation of the w-ary functional calculus of first order is easily

---


220 PURE FUNCTIONALCALCULUSOF FIRSTORDER [Chap. IV
seen to be equivalent (in the sense that the theorems are the same) to the 
m-ary functional calculus of first order in the formulation F1,w of Chapter III.
EXERCISES 40
4 0 .0 . Show that the theorems of the singulary functional calculus of first 
order are identical with those theorems of the pure functional calculus of 
first order in which all the functional variables are singulary.
4 0 .1 . In the system Fg13 show that, without changing the class of theorems, 
the rule of generalization and the axioms t408 and f409 could be replaced 
by the two following rules of inference: from A d  B, if a is an individual 
variable which is not free in A, to infer A 
(a)B; from A 
(a)B, if a is 
not free in A, to infer A n B .
4 0 .2 . For a formulation of the extended propositional calculus with prim­
itive symbols as indicated in exercise 30.7, let the rules of inference be 
modus ponens, the rule of substitution (for propositional variables), and the 
two rules introduced in 40.1 as these are modified by taking a to be a prop­
ositional variable rather than an individual variable. And let the axioms 
be the same as the three axioms of P3. Carry the development of the system 
far enough to establish a solution of its decision problem along the lines 
suggested in §28.400 (Make use of the result of 18.3.)
4 0 .3 . In a partial system of extended propositional calculus, with 
primitive symbols as in 30.7, rules of inference modus ponens, generaliza­
tion, and substitution, the two axioms of P+, and axiom schemata (a) A =5 A, 
and (a)[b ro A] ro . b ^  (a)A where b is not a, show that under suitable 
definitions of conjunction, disjunction, equivalence, and negation the entire 
intuitionistic propositional calculus is contained. (See 19.6.)
41. Independence. From the equivalence of Fgp and Flp it is easily 
seen that the rules *4042, *4043, . . .  of Fj13 are non-independent. For by 
means of the rules *402, *403, *4040, *404x it is possible to infer an arbitrary 
instance of one of the five schemata *302~*306 from the corresponding one 
of the five axioms t40o~~t409.
Though not independent, th e rules *404n (n  >  1) are nevertheless in a certain 
sense n o t superfluous, since th ey  restrict the class of sound interpretations of 
F jp. Indeed an  interpretation w hich is like the principal in terp retatio n  of F 1* 
except th a t functional variables w ith superscript greater th a n  1 are interpreted 
as functional co n stan ts (each one corresponding to a p artic u la r propositional 
function of individuals) is a sound in terp re tatio n  of the system  F 1*, and of the
400These axioms and rules of inference for the extended calculus are given in the paper
of footnote 243, where they are credited to Tarski.

---


§41]
I N D E P E N D E N C E
221
system  obtained from  F,JP by deleting the rules * 4 0 4 n (n >  1), b u t is not a sound 
in terp retatio n  of F |p itself.
The need for the rules *404n (n >  1) may be seen from a syntactical 
standpoint if Fgp is thought of not as a self-sufficient system but as a system 
to which undefined terms and postulates are to be added in order to develop 
some special branch of mathematics by the formal axiomatic method (as 
described in the concluding paragraphs of §07). For such an added postulate 
may well contain, e.g., a binary functional variable in such a way that *404a 
must be used in making required inferences from it.
Except *404n (n >  1), the rules and axioms of Fgp are independent. We 
go on to indicate briefly how this may be established.
Consider a formulation of the propositional calculus in which the rules of 
inference are substitution and modus ponens, and the five axioms are f405, 
f406, t^07, p id  r id  mp 
r, and r id r. Here the last two axioms are afps of 
f408 and f409 respectively, in the sense of §32. Hence from a given proof of 
any theorem A of Fgp upon replacing each wff in the proof by a suitably 
chosen afp of it, we obtain a proof of an afp A0 of A as a theorem of this 
formulation of the propositional calculus. By the methods of §19 we may 
show, for this formulation of the propositional calculus, the independence 
of the rule of modus ponens and of each of the axioms |405, f4G6, f4G7. 
There follows, for Fap, the independence of each of *400, f405, f406, f407. 
(Details are left to the reader.)
Consider the transformation upon the wffs of F£p which consists in re­
placing all occurrences of (Va) by ~(Va)~, simultaneously for all individual 
variables a. I.e., briefly, consider the transformation which consists in re­
placing the universal quantifier everywhere by the existential quantifier. 
It may be verified that this transforms every axiom of F}/ except f409 
into a theorem of Fgp; and, in an obvious sense, it transforms every primitive 
rule of inference of F\p into a primitive or derived rule of F\?. But f409 is 
transformed into (3#)F(#) id  F{y), which is not a theorem. (If V 
id
F(y), then, by *330 and P, b F(x) id  F(y), contrary to **324.) The inde­
pendence of f409 follows.
Consider the transformation upon the wffs of F\p which consists in re­
placing simultaneously every wf partof the form (Va)Cby (Va)~[C id C] 401 
This transforms every axiom into a theorem, and every primitive rule of 
inference except *401 (the rule of generalization) into a primitive or derived
40lMore explicitly, by this transform ation every quantifier-free formula is trans­
formed into itself, and if C and D are transformed into G' and D ' respectively, then 
[C Z> Dj is transformed into [O' id D 'l, ~C  is transformed into ~C ', and (Va)G is 
transformed into (V a)^[C / => C '].

---


222 P U R E  F U N C T I O N A L  C A L C U L U S  O F  F I R S T  O R D E R  [Chap. IV
rule. On the other hand it transforms the theorem F(x) 
F{z) into the 
non-theorem (x)~ . F(z) i d  F(x) i d  . F(x) =) F(x). There follows the inde­
pendence of *401.
Consider the transformation upon the wffs of Fgp which consists in re­
placing (Va) by ~ (V a )~  whenever a is a different variable than x. This 
transforms every axiom into a theorem and every primitive rule of inference 
except *402 (the rule of alphabetic change of bound variable) into a primi­
tive or derived rule. It transforms the theorem (;y)F{y) 3  jF(x) into the 
non-theorem (3y).F(y) id F(x). There follows the independence of *402.
Consider the transformation upon the wffs of Fgp which consists in re­
placing every wf part of the form (V a)C  by S*C|. (Or, as the transformation 
may also be described, every bound occurrence of an individual variable in 
the wff is replaced by the particular individual variable y, and then (Vy) is 
omitted wherever it occurs.) This transforms every axiom into a theorem 
and every primitive rule of inference except *403 (the rule of substitution 
for individual variables) into a primitive or derived rule. It transforms the 
theorem (x)F(x) id F { z ) into the non-theorem F(y) ^  F(z) (cf. §32). There 
follows the independence of *403.
Consider the transformation upon the wffs of FgP which consists in omit­
ting ~ wherever it occurs and at the same time replacing p everywhere by 
[p 
p], This transforms every axiom into a theorem and every primitive 
rule of inference except *404o (the rule of substitution for propositional 
variables) into a primitive or derived rule. It transforms the theorem 
~q id q id q into the non-theorem q id q^> q (**320). There follows the inde­
pendence of *4040.
Consider the transformation upon the wffs of 
which consists in 
replacing F(a) throughout by [/'"(a) ^  F (a)] (for every individual variable 
a, but only for the one functional variable F1) and at the same time replacing 
(Va) throughout by ~ (V a )~  (for every individual variable a), This trans­
forms every axiom into a theorem and every primitive rule of inference 
except *404* (the rule of substitution for singulary functional variables) 
into a primitive or derived rule. It transforms the theorem (x)G(x) id G{y) 
into the non-theorem (3x)G(x) id G(y). There follows the independence of 
*404*.
Finally, to establish the independence of |408 we use a more elaborate 
transformation upon the wffs of Fgp, which is described in steps as follows. 
First replace every individual variable by the individual variable next 
following it in alphabetic order, i.e., replace simultaneously x by y, y by z, 
z by xXt and so on. Then change simultaneously every propositional variable

---


§41]
E X E R C I S E S  4 1
223
to a singulary functional variable and every »-ary functional variable to an 
(» +  l)-ary functional variable in the following way: a propositional vari­
able a is to be replaced by b(x), where b is the singulary functional variable 
having the same alphabetic position as a (i.e., if a is the zth propositional 
variable in alphabetic order, then b is the zth singulary functional variable 
in alphabetic order); and, a being an n-ary functional variable, each wf 
part a(cx, c2, . .
cn) is to be replaced by b(c1, c2, . . 
cn, x) where b is the 
(« +  l)-ary functional variable having the same alphabetic position as a. 
Then in every wf part having the form of an implication [A ^  B] prefix an 
existential quantifier ~(V x)~ to the antecedent A and to the consequent B 
(i,e.( change [A id B] to [~ (V x)~ A ^  ~(V x)~B]), and at the same time 
change every universal quantifier (Va) to (Va){Vx), and change ~  every­
where to (Vx)~.
The result of applying this transformation to |408 is
(1) (3a;)[(3a:)F(as) =>vx {3x)F(y, x)] => (3x) . (3x)F(x) => (3x) (y) [x)F{y,x),
which is not a theorem of F2P. On the other hand, application of this trans­
formation to the remaining axioms of F\p yields, in order,
(2) 
(3x)F{x) zd (3x) ■ (3x)G(x) => (3x)F{x),
(3) 
(3x)[(3x)F1(x) => (3x) ■ (3x)F(x) => (3x)G(x)] zd (3x) . 
(3x)[(3x)F1(x) id (3x)F(x)] id (3x) . (HxjZ^fx) => (3x)G(x),
(4) (3x)[(3x)(x)~F(x) ^  (3x)(x)~G(x)] id (3x) . (3x)G(x) 
(3x)jF(x),
(5) 
{3x)(y){x)F{y,x) =3 {3x)F(z,x), 
which are theorems of F\p.
Moreover, by this transformation every primitive rule of inference of F\p 
is transformed into a primitive or derived rule. (In order to show this in the 
case of *400, it is necessary to make use of the fact, which is a corollary of 
**320, that no theorem of F\p fails to contain an implication sign, and hence 
that no theorem of Fgp is transformed into a wff containing x as a free 
variable.) The independence of f408 follows.
EXERCISES 41
4 1 .0 . 
In order to complete the proof of independence of f408 as described 
above, supply details of the demonstration that (1) is a non-theorem of 
Fgp and that (2)-(5) are theorems. (For the first part, using rules of sub­
stitution for functional variables, proceed by showing that, if (1) is a theo­
rem, then C(x) => G(y) is a theorem, contrary to **324.)

---


224 P U R E  F U N C T I O N  A L C A L C U L U S  O F  F I R S T  O R D E R  
[Ch a p. I V
4 1 . 1. Following Godel, prove the independence of |408 by means of the 
transformation upon wffs of Fgp which consists in replacing every wf part 
of the form (Va)f(a)J where a is an individual variable and f is a singulary 
functional variable, and also every wf part of the form (Va)b, where a is 
an individual variable and b is a propositional variable, by [p 
fi],
4 1 .2 . Following the analogy of §40, and using the same rules of inference 
*40Q-*404n as in §40, reformulate the system F11 of exercise 38.0 as a pure
intuitionistic functional calculus of first order Fj*p with a finite number of 
axioms. Discuss the independence of the axioms and rules of Fgip. (Use may 
be made of the results of 26.18, 36.6-38.8, and §41.)
4 1 .3 . Investigate the independence of the axioms and rules of the for­
mulation of the extended propositional calculus which was introduced in 
exercise 40.2.
42. Skolem normal form. A wff402 is said to be in Skolem normal form
if it is in prenex normal form without free individual variables and has 
a prefix of the form
(3ai)(3a2) . . . (aaJfbjH b,).. . (bn),
where m ^  1 and n ^  0. In other words, a wff in prenex normal form is 
in Skolem normal form if it has no free individual variables and its prefix 
contains at least one existential quantifier and every existential quantifier 
in the prefix precedes every universal quantifier.*03
In order to obtain what we shall call the Skolem normal form of a wff A, 
we apply the following reduction procedure;
i.
First reduce A to its prenex normal form B by the method of §39.
ii.
If Ci is the first in alphabetic order of the free individual variables
of B, prefix the universal quantifier (Vcx) to B. Repeat this step until B 
has been reduced to a wff Cx which is in prenex normal form without free 
individual variables. (Thus Cx is (cu)(cu_x) . . .  (cJB, where 
ca, . . cu 
are the free individual variables of B in alphabetic order. Of course u may 
be 0 .)
iii.
If Cx is in Skolem normal form, let C be the same as Cx.
iv.
If Cx has a null prefix (this will be the case if Cx is a wff of P), let C
be (3s) . F*(x) r> F(a:} ^  Cj. Then G is in Skolem normal form.
40JIn §§42-47, "wff" shall mean "well-formed formula of the pure functional calculus 
of first order in either of the formulations F*p or F*p," except where the contrary is 
indicated by using the explicit wording "wff of" such and such a system.
4o«when we refer to the universal quantifiers in the prefix, we mean only the uni* 
versal quantifiers which are without ~  before and after, i.e.r we exclude those universal 
quantifiers which occur as parts of the existential quantifiers (D14). This remark applies 
here and a t various places below.

---


§42]
S K O L E M  N O R M A L  F O R M
225
v. 
Except in the cases iii and iv, Cx must have the form 
(3ai)(3a4) . .. (33 ^ (3^ ) ^ ,
where k 
0, and Nx is in prenex normal form and has alf a2, . . 
afc+1 
as its only free individual variables. Let fx be the first (k +  1 )-ary functional 
variable in alphabetic order which does not occur in Cx. Let C2 be the prenex 
normal form of
(3a1)(3a2) . . .  (3a*) . (a ^ K N , => 
a2, . . aw )] =>
( a fc + x )^ l(a i^ a 2» ’ ' *' a Jfc+l)'
Then, if C2 is in Skolem normal form, let C be the same as C2. Otherwise 
repeat the reduction. I.e., C2 has the form
(3a1)(3a2) . . .  (3 afcO(aJe/+i)^2*
where kl >  k, and N 2 is in prenex normal form and has ax, a2J . . 
a**+1 as
its only free individual variables. Let f2 be the first (k* +  l)-ary functional 
variable in alphabetic order which does not occur in C2. Let C3 be the prenex 
normal form of
(3a1)(3a2) . . . (3afc#) . (afc,+1)[N2 id f2(ax> a2, . . 
a&>+1)] id
( a * '- f l) ^ 2 ( a i» a 2* • * 
a fc/4 -l)■
Then, if C3 is in Skolem normal form, let C be the same as C3. Otherwise 
repeat the reduction again, reducing C3 to C4; and so on until a wff Cn_(+X 
in Skolem normal form is obtained, which is then C. We shall see that C is 
C«_(+i, where l is the number of universal quantifiers which occur at the end 
of the prefix of Cx, after the last existential quantifier, and where n is the total 
number of universal quantifiers in the prefix of Cx (which is in fact the 
same as that in the prefix of C).
**420. 
Any wff A can be reduced to a wff G in Skolem normal form, by 
the procedure just described in i-v. This process of reduction is 
effective, and the resulting wff C in Skolem normal form is uniquely 
determined when A is given.
Proof. In the series of reductions described in v, by which Cx is reduced to
C2, Ca to C3> and so on, the effect on the prefix at each step is to change the
first universal quantifier to an existential quantifier and at the same time to
W4To see this it is necessary to take into account the nature of the process of reduction 
to prenex normal form, as defined in §39. Thus, if the prefix of NT,, is n . n .  
n . .  the 
prefix of G, is
(3“i)(3a.) • • • (3a») (3a*«)nin, • ■ . n .(b 1+l)
by the reduction steps (iii)-(v) of §39. Here e =  m + l — A — 1, and b I+1 is the first 
individual variable in alphabetic order after a***, which does not occur in Cv )

---


226 PURE FUNCTIONAL CALCULUS OF FIRST ORDER [Chap. IV
add a universal quantifier at the end of the prefix (without other change in 
the prefix) .40* Thus at each step the number of universal quantifiers is re­
duced by 1 which occur in a position preceding any existential quantifier. 
The series of reductions must therefore terminate in a wff C in Skolem nor­
mal form. The remaining part of the theorem is then obvious.
Definition. The wff C which is obtained from the wff A by the procedure 
described in i-v is called the Skolem normal form of A.
*421. 
If G is the Skolem normal form of A, then h A if and only if b C.
Proof. We continue to use the same notations as in the statement of i-v 
above.
By *392, 1 - A s B .  Hence by P, b A if and only if b B.
By *301 and *306—else by *401, f409, and *404t— b B if and only if
b Cv**
If C is obtained by iii, then C is the same as Cv Hence b A if and only if 
bC.
In case C is obtained by iv, we have by P:
f- Cx == . F{x) zd F(x) => Cv
Hence by generalizing upon x and then using *388, since Cx is without free 
individual variables, we have:
f-Ca~  {lx) . F{x) zd F{x) zd Cv
I.e., I- C! s  C. Hence by P, b 
if and only if b G. Hence b A if and only if 
bC.
Finally we consider the case that C is obtained by v. We must show that 
1- Cj if and only if I- C2; b C2 if and only if I- C3; . . 
b Cn__t if and only if 
b Cn_m . Since C is the same as Cn_t^v it will then follow that h A if and only 
if 1-C.
We state in detail the proof that b 
if and only if b C2. The proofs that 
b C2 if and only if b C3, and so on, are precisely similar—the argument may 
therefore be completed by mathematical induction, a step that is left to 
the reader.
By *306 (cf. footnote 405) and P,
(a fc+ i)N i b N x zd fx(a ii a 2, . . 
a* + i) ^  
a 2» ■ • *» a fc+i)'
Hence by generalization upon afc+1, and *333,
4MThe axiom schemata of Fn> are, with obvious modification in wording, also theorem 
schemata of F*p. And we shall hereafter use them by number in this dual role (just as 
we use the numbered theorem schemata of F*p as being a t the same time theorem sche­
mata of FJp).

---


§43]
V A L I D I T Y  A N D  S A T I S F I A B I L I T Y
227
(afc+JNi I- (am )[N! 3 f^a,, a2....... a*+1)] 3  (a*.1)f1(a1, a2, . . 
a*+1).
Hence by *367,
(i38^(3a2) . .. (3a*) (a*^)]^ I- (Ha^Sa* ) . . .  (3a*) .
(a it+ l)[N 1 ^  ^ l(a i* a 2> • • * ‘ a Jfc+l)] ^  (a fc+l)^l(a i' a 2< ' * *i a fc-n) ■
Hence by *392 and P, Cx b C2. Hence if b Cx then b C2.
Now suppose that b C2. Then by *392 and P,
1- (3a1)(Baz) . . . (3a*) . (a * ^ )^  3  ^(a, » a 2» * • ■» a A:+l)] ^
(a A:+l)^l(a i» a 2i * • ** a fc+i)'
Hence by the rule of substitution for functional variables, substituting 
Nx for 
aa, . . 
a*+1), we have:
1- (3ai)(3az) . . . (3a*) . ( a ^ N , 3  N,] 3  (a^JN,.
Now by P and generalization, I- (a*+1)[N, 3  N J. Hence by m o d u s  p o n e n s ,
(“*■*45*1 ^  NJ 13 (a*+i)Ni h (a*+i)Ni-
Hence by *367,
(3ai)(3a2) . . . (3a*). (ajfc+1)[Ni 
Nx] 
(a*+1)Ni b 
(3ai) (3a.2) . . ,  (3a*)(afc+1)N1.
Therefore b (3ax)(3a2) . . . (3afc)(afc+1)N!. I.e., \ - C v
43.
Validity and satisfiability. The rules a-f, given in small type
in §30 as semantical rules determining a principal interpretation of F^, may 
be modified or reinterpreted in such a way as to give them a purely syn­
tactical character.
N am ely, in the statem en t of these rules in §30 we understood th e w ords 
" ra n g e '' and "v alue" each in a (presupposed) sem antical sense— so th a t the 
rules are thereby relevant to the question w hat we take to be in ten d ed  by a 
person who, using F*p as an actual language for purposes of com m unication, 
asserts a particular one of its wffs— or, m ore exactly, so th a t th e rules constitute 
a  proposal of a norm , an ideal dem and as to w hat shall be intended by such a 
person.
But we now reintroduce the rules a-f with a new meaning, according to 
which we do not take the words “range” and “value” in any semantical 
sense, but rather, after selecting a particular non-empty class as domain of in­
dividuals, we regard the rules as constituting a definition of the words “range” 
and “value” (in the case of the word “value,” an inductive definition). On 
this basis, the “range” of a variable comes to be merely a certain class 
which is abstractly associated with the variable by the definition; and the 
“value” of a wff for a given system of “values” of the variables a^ a2, . . 
an 
(all of the free variables of the wff being included among aL, a2l . . 
an)

---


228 PURE FUNCTION ALCALCULUS OF FIRST ORDER [Ch a p. IV
comes to be merely a certain truth-value40* which is abstractly associated 
with the wff and with n ordered pairs 
at>, <a8l fla> ,, . 
<an> «„) in
which each ai is a member of the range of a*. Hereafter, when the words 
"range" and "value" occur in a syntactical discussion, they are to be under­
stood in this syntactical sense, the fact that a passage is not in small type 
being sufficient indication that the words do not have their semantical 
sense. (Where needed for clarity, however, we may use such more explicit 
phrases as "value in the syntactical sense.")
These syntactical notions of range and value may of course be used in­
dependently of any interpretation of the system Fxp or F^p—thus even if 
the system is used purely as a formal calculus, without interpretation—or 
even if it is used with some interpretation quite different from the principal 
interpretations as given in §30.
A nqn-empty domain of individuals having been selected, a wff is said to 
be valid in that domain if it has the value t for all possible values of its free 
variables, satisfiable in that domain if it has the value t for at least one 
hyhiem of possible values of its free variables. (Hfcre, by a "possible" value 
uf a variable is meant merely a value that belongs to the range of the 
variable according to rules a, b„.)
A wff is said to be valid if it is valid in every non-empty domain, satisfiable 
if it is satisfiable in some non-empty domain.* 407
By the universal closure of a wff B we shall mean the wff (cJfCu^) , . . 
(cJB, where cv c2, . . 
cu are the free individual variables of B in alpha­
betic order. Similarly, the existential closure of B is the wff (3cu)(3cti_1) . . (
40*Observe that this reference in the definition to truth-values does not of itself render 
the definition semantical. Nevertheless, if preferred, any two other things may be used 
here instead of the two truth-values. For example, in the syntactical definition of 
"value" we might use the numbers 0 and 1 in place of the truth-values, truth and false­
hood respectively, and then define a wff to be "valid" in a given domain if it has the 
value 0 for all possible values of its free variables.
407At this point §§07-09 of the introduction should be reread, especially the discussion 
in §09 of Tarski's syntactical definition of truth, and footnotes 142, 143. That we have 
given here a syntactical definition of validity rather than of truth is just because the 
pure functional calculus of first order has no wffs without free variables,
The notions of validity and of satisfiability may also be regarded as analogues, 
for the functional calculus of first order, of the notions of being a tautology and of not 
being a contradiction in the propositional calculus. Indeed, in the special case of a wff 
of the pure functional calculus of first order which is at the same time a wff of the prop­
ositional calculus, the former notions immediately reduce to the latter. And it is 
obvious that the discussion in the present section, regarding the distinction between the 
syntactical and the semantical notions of value, and the corresponding discussion at 
the beginning of §15 are closely parallel. But there is the im portant difference that an 
effective test was given for recognizing a wff of the propositional calculus (say of PA, 
or of P,) as being or not being a tautology, whereas no effective test is possible for 
recognizing a wff of the pure functional calculus of first order as being or not being valid.

---


§43]
VALIDITY AND SATISFIABILITY
229
where ca, ca, , . 
cu are the tree individual variables of B in alpha­
betic order.
*’430. 
A wff A is valid in a given non-empty domain if and only if its 
negation ~A is not satisfiable in that domain. A wff A is valid if 
and only if its negation ~A is not satisfiable.
Proof. This follows at once by rule d, or, more correctly, by the clause 
corresponding to rule d in the definition of “■value" in the syntactical 
sense.
**431. 
A wff is satisfiable in a given non-empty domain if and only if its 
negation is not valid in that domain. A wff is satisfiable if and only 
if its negation is not valid.
Proof. Again this follows at once by rule d.
**432. 
A wff is valid in a given non-empty domain if and only if its univer­
sal closure is valid in that domain. A wff is valid if and only if its 
universal closure is valid.
Proof. By rule f.
**433. 
A wff is satisfiable in a given non-empty domain if and only if its 
existential closure is satisfiable in that domain. A wff is satisfiable 
if and only if its existential closure is satisfiable.
Proof. By rules d and f. For from these two rules together it follows that, 
for a given system of values of the free variables of (3a)A, the value of 
(3a)A is t if the value of A is t for at least one value of a, and the value of 
(3a)A is f if the value of A is f for every value of a,
**434. 
Every theorem is valid.408
Proof. Using either of the formulations F1** and FgP, we may show that 
all the axioms are valid and all the rules of inference preserve validity. 
Details are left to the reader.
**435. 
A wff is valid in a given non-empty domain if and only if its prenex 
normal form is valid in that domain. A wff is valid if and only if its 
prenex normal form is valid.
408This metatheorem may be regarded as the analogue (for the pure functional 
calculus of first order) of **150 or **235 (for the propositional calculus). And in fact 
the method of proof is the same. Notice that **324, and hence **323, could now 
be proved as corollaries of **434. But by the proofs in §32 these two metatheorems 
were established on a much weaker basis than that required for **434.

---


230 PURE FUNCTIONAL CALCULUS OF FIRST ORDER [Chap.IV
Proof. If B is the prenex normal form of A, we have by *392 that b A =  B. 
Hence by **434, A ~  B is valid. Hence by rules d and e, A and B have the 
same value for every system of values of their free variables. From this the 
metatheorem follows by the definition of validity.
**436. 
A wff is satisfiable in a given non-empty domain if and only if its 
prenex normal form is satisfiable in that domain. A wff is satisfiable 
if and only if its prenex normal form is satisfiable.
Proof. As in the previous proof, if B is the prenex normal form of A, then 
A and B have the same value for every system of values of their free vari­
ables. From this the metatheorem follows by the definition of satisfiability.
**437. 
A wff is valid in a given non-empty domain if and only if its Skolem 
normal form is valid in that domain. A wff is valid if and only if its 
Skolem normal form is valid.
Proof. The proof of this parallels exactly the proof of *421, except that 
wherever that proof makes use of a theorem the present proof must instead 
make use of the fact that that theorem is valid, and wherever that proof 
makes use of a rule of inference the present proof must instead make use 
of the fact that that rule of inference preserves validity (in an arbitrary 
non-empty domain).
A wff is said to be in the Skolem normal form for satisfiability if it is in 
prenex normal form without free individual variables and has a prefix of 
the form
(ai)(a8) . . .  ( a J f lb O f lb ,) ... (3b,).
where m ^  1, n ^  0.
Given any wff A, we may find the Skolem normal form of ~A. This will 
be a wff
(3ax)(3a2) . . . (3am)(b1)(bz) ... (b„)M
in which m ^  1, n ^  0, and M is quantifier-free. Then the prenex normal 
form of the negation of this wff will be a wff
(a1)(a2) ...( a J ( 3 b 1)(3b2) ...( 3 b n)M'I
where M' is obtained from M by either deleting or inserting an initial ne­
gation sign 
This last wff, the prenex normal form of the negation of the 
Skolem normal form of the negation of A, is in Skolem normal form for 
satisfiability; we shall call it the Skolem normal form of A for satisfiability.

---


231
**438. 
A wff is satisfiable in a given non-empty domain if and only if its 
Skolem normal form for satisfiability is satisfiable in that domain. 
A wff is satisfiable if and only if its Skolem normal form for satis­
fiability is satisfiable.
Proof. By **431, **437, **430, **436.
**439. 
If a wff is valid in a given non-empty domain, it is valid in any 
non-empty domain having the same or a smaller number of 
individuals. If a wff is satisfiable in a given non-empty domain, it 
is satisfiable in any domain having the same or a larger number 
of individuals.
Proof. Suppose that A is satisfiable in the non-empty domain 
and let 
ft be a domain having the same or a larger number of individuals. Then a 
One-to-one correspondence can be found between $  and some part ft’0 of the 
domain ft (where ft° may coincide with ft or may be a proper part of ft). 
If i is any individual in 
let i* be the corresponding individual in ft° under 
this one-to-one correspondence. Also select a particular individual 
in 3- 
If A is any individual in ft0, let A' be the corresponding individual in ^  under 
the foregoing one-to-one correspondence; and if A is any individual which is 
in ft but not in ft°, let A' be iQ. If 0  is an m-ary propositional function over 
i,e., a propositional function whose range is the ordered w-tuples of individ­
uals of 
let 0 ' be an m-ary propositional function over ft, determined by 
the rule that 0'(kv A2, . . ., Am) is 0 {k \t k \,. . ., k'm).
Let av a 2l . . ., a n be the complete list of free variables of A. Since A is 
Satisfiable in 
there is a system of values ax, a2, 
of a I# a2, . . ., a n for
which the value of A is truth, each at- being an individual in 
or a propo­
sitional function over 3 . Then av az, . . ., an is a system of values of a p a 2, 
, . a„ for which the value of A is truth, each a. being an individual in ft or 
a propositional function over ft. Thus A is satisfiable in ft.
This completes the proof of the second part of the metatheorem. From this 
the first part then follows by **430.
EXERCISES 43
4 3 .0 . Let A have no free individual variables and let C be the Skolem 
normal form of A. Show by an example that it is not in general true that 
hA =  C. Is it always true that F A D  C? That h C D  A?
43-1- Find the Skolem normal form of each of the following:
§43] 
EXERCISES 4 3

---


232 PURE FUNCTIONAL CALCULUS OF FIRST ORDER 
[Ch a p. IV
(1) 
F(*) => F(x)
(2) 
(x)F{x) zd (3*)F(*)
(3) 
p zd (3x)p
(4) 
G{x) zdx Mix) zd . (3*)G(*) => (3x)H{x)
(5) 
(3x){3y)F{x, y, z) zd (3y)(3x)F(x, y, z)
4 3 .2 . As was done in the text for Flp and rules a-f, let the rules oc-f of 
§30 be reinterpreted as syntactical definitions of "range” and "value" for
the case of the system Flh. Let a wff of FIh be called valid if it has the value 
truth for all possible values of its free variables; and let a wff of Flh without 
free variables be called true if it has the value truth. Also, given a wff A 
of Flh in which the distinct individual variables (bound and free) that occur 
are ax, a2, . . 
a„, let the characteristic function of any wf part B of A be
defined by induction as follows: The characteristic function of 
aJ( afc) 
is the w-ary function of natural numbers whose value for arguments av a9, 
. . 
an is 0 if at u- ^  =  ak, and 1 in the contrary case; the characteristic 
function of 77(a*, a,, a*) is the «-ary function of natural numbers whose 
value for arguments av a2, . . 
an is 0 if a ^  — ak, and 1 in the contrary 
case; if the characteristic function of 
is fv the characteristic function of 
~BX is the w-ary function of natural numbers whose value for arguments 
alt a2, . . 
an is 1 -  fl(a1, at, . . 
an)\ if the characteristic functions of Bx 
and B2 are fx and /2 respectively, the characteristic function of [Bx 
Ba] 
is the «-ary function of natural numbers whose value for arguments 
av a2i . . 
an is (1 — fx[alt a%} . . 
an))f2(av as, . . 
an); if the characteristic 
function of Bx is flt the characteristic function of (VaJBi is the «-ary 
function of natural numbers whose value for arguments alJ a%i.. ., a„ is
1 IT 
/i(fli> a & • • *» ®«))*
<H
the product being taken over all natural numbers a{t with the convention 
that the product is 1 if all the factors are 1, 0 if any factor is 0. Prove that 
a wff A of Flh is valid (or in case A has no free variables, true) if and only if 
the characteristic function of A as a wf part of A vanishes identically, i.e., 
has the value 0 for all possible arguments.
43*3* Show that the wff
(3*) [y) . F{x, y ) zd . ~F{y, x) => . F[x, x) == F(y, y)
is valid in any domain consisting of not more than three individuals but is 
not valid in a domain of four individuals.

---


§44]
GOEDEL COMPLETENESS THEOREM
233
43-4- Prove **324 by showing that, if a quantifier-free formula is not a 
substitution instance of a tautology, there is a finite non-empty domain in 
which it is non-valid.
4 3-5. Show that the following wffs are valid in every non-empty finite 
domain but not valid in an infinite domain:409
(1) 
(3x)(y)(3z) . F{y, z) 3  F{x, z) 3  . F{z, x) 3  F{y, x)
(2) (*i)(*2)(*a)[F(*i, *i) . F fo, x3) 3  F(xv x2) v -F(x2>^)] 3  (3y)[s)F(y,z)
4 3 .6 . (1) Without relying on or presupposing the reduction of a wff to 
Skolem normal form by the method of §42, make a direct statement of a 
process for reducing a wff to its Skolem normal form (or satisfiability. 
(2) Apply this process to the negation of the wff of exercise 43.5(1).
4 3 .7 . Prove directly that a wff is satisfiable if and only if its dual is not 
valid.
44. Gddel’s completeness theorem.
**440. 
Every valid wff is a theorem. 
(Gddel’s completeness theorem.)
Proof. By *421 and **437, it is sufficient to consider a wff A in Skolem 
normal form,
(3a1)(3a2) ...( 3 a m)(bI)(b2) . . . ( b n)M,
where M is quantifier-free and contains the individual variables alf a2, . . 
a*,, ba, b2l . . ., b„ (and no other individual variables). We shall show that 
either (1) A is a theorem, or (2) A is not valid.
Let us enumerate the (ordered) w-tuples of positive integers according to 
the following rule: If ix +  i2 +  .. . +  im <  jx -f /2 +  . . . 4- jin, the w-tuple 
(iv H, • ■ •, 
comes before (i.e., comes earlier in the enumeration than)
the w-tuple </„ ;'E----- - ;m>; if t, 4- u +  . . . u- im =  /, +  ?2 -4- . . .  -4- /*,,
h =  ii, H =  h, ■ ■ ■> ** =  /*, t*+i <  W
 the w-tuple (iv it, . . 
tm> again 
comes before the w-tuple ( jlt jlt . .
/m>.410
Thus the w-tuples of positive integers are enumerated, or arranged in an 
infinite sequence. The first w-tuple in this enumeration is ( 1 , 1 , 1 , . . 1 , 1 , 1 )  
the second w-tuple is ( 1, 1, 1, . . ., 1, 1, 2): the third one is ( 1, 1, 1, . .
<otThese are modified forms of examples due, one to K urt Schutte, and the other to 
Paul Bernays and Moses SchOnfinkel.
110That is, the w-tuples <iJ( 
i m> arc arranged in order of increasing sums
l\ 4* ig . . . -f- i m. And w-tuples having the same sum are arranged among themselves 
in lexicographic order.

---


234 PURE FUNCTIONAL CALCULUS OF FIRST ORDER 
[Ch a p. IV
1, 2, I); the fourth is <1, 1, 1, . . 
2, 1, 1); and so on.411 Evidently, no po­
sitive integer occurring in the Ath m-tuple is greater than A (if m S  1).
We let the Ath w-tuple in this enumeration be <[A1], [A2],. . 
[Aw]>.
I.e., we use [A/] as a notation for the Ith. positive integer in the Ath w-tuple. 
Now let B fc be
0 * 1  
—* *  
b l 
b* 
JUT]
let Cfc be
B, v B2 v .. . v Bkt
and let Dfc be
(arl)(ar2) ■ * ’
We notice that the variables x{k__l)n+2l ^u-Dn+s* • ■ •> xkn+v which are here 
substituted for bx, b2, . . 
bn are none of them the same as any of the 
variables 
x^kmy which are substituted for ai( a2, . . aTO.
Moreover the variables xu„1)n+2, x(fc_1)n+3, .. 
xkn+1 are all different among 
themselves, and different from all the variables occurring in Blf Ba^ .. 
Bfc_j. But all the variables xv x2, . . 
xkn+l occur in C*.
(It is possible that n may be 0, and the reader should observe that this 
special case makes no difficulty; but m  is never less than 1.)
Since M is quantifier-free, it follows that Bfc and C* are also quantifier- 
free. And, except in the case n =  0, the complete list of free individual 
variables in Ck is xv x2, . . 
xkn+1.
Lemma; 
For every A, Dfc h A.
We prove the lemma by mathematical induction with respect to A. In
doing so, we assume that none of the variables a1# a2__ _ am, b1( b2, .
bn
are the same as any of the variables x1( x2, xa, . . .  (as may be brought 
about by'alphabetic changes of bound variable in A if necessary).
By *330 and modus ponens, repeated m times,
(bxjo*,). . .  (b„) 
i- a .
Hence by *306 and modus ponens,
{*i)(bi)(b«). . .  (b„) 
v a .
Hence by alphabetic change of bound variable, repeated n times, Dx I- A. 
This is the case A — 1 of the lemma.
4llHere, for purposes of illustration, we have taken m >  8; and the dots in each case 
represent a number of l's. As further illustration the wth fn-tuple is <1, 2, 1, . . . » 1,1,1);
the [m +  1)th is <2, 1, 1 ,___ l, 1, 1>; the {m +  2)th is <1, 1, 1, . . .  1, 1, 3>; the
(m +  3)th is <1, 1, 1......... 1, 2, 2>; the (tn +  4)th is <1, 1, 1, . . . .  I, 3, 1>; the
(m +  6)th is <1, 1 ,1 ,___ 2, 1, 2>.

---


m
GOEDEL COMPLETENESS THEOREM
235
Now suppose, for some particular k greater than 1, that 
1- A. By *385 
and *341 and P, repeating n times, we have that
(^tfc-Un+aM^lf c - l) n +3 ) ■ • ■ (xfcn+l) [ ^ f c - 1  V
Cfc-l V  (X {A-l>n+2) {X (A~l)n+3) ' ' ■ (x Jfc»+l)®fc*
From this, since 
v Bfc is the wff Gfc, we have by *306 and modus fonens, 
repeated (k — 1 )n +  1 times, that
Die h 
v
Hence by alphabetic change of bound variable, repeated n times,
D „ I-c M v l b .) {!>.)...<!>„)
Also by *330 and the transitive law of implication, m times,
h (b,)(b,) . . . (b„) S
^
^
M
I  =  A.
Hence by P,
f- Cfc_1 v A.
Hence by generalizing upon # (fc_1)n+1 and using *386 and P, then generalizing 
upon 
n and using *386 and P, and so on, repeating (k — l)n +  1 
times, we have that
v A
Since 
I- A, we have that h T>k-i :d A, and hence by P that Dft h A.
This completes the proof of the lemma. Continuing the proof of **440, 
we distinguish two cases.412
Case 1: for some k, C* is a theorem. Then by generalization (kn +  1 
times), Dfc is a theorem. Hence by the lemma, A is a theorem.
Case 2; for every kt Cfc is a non-theorem. Then for every kt by *311, it 
is possible to find such an assignment of truth-values to the elementary 
farts of Cfc (i.e., the wf parts which have either the form of a propositional 
variable alone or the form f(Cj, c2, . . 
cf)) that the value of C*. as obtained 
by the truth-tables of :d and 
is f. Or, as we shall say, it is possible to find 
a falsifying assignment of truth-values to the elementary parts of Ck. (The 
same elementary part may occur more than once in Ck, in which case of 
course the same truth-value is to be given to it at every occurrence; but 
different elementary parts may receive different truth-values, even if they 
differ only as to individual variables.)
4l#At this point of the proof we make use of the law of excluded middle (in the 
syntax language). But since no effective means is at hand to determine which of the two 
cases holds for a given A, the method of the proof yields no solution of the decision 
problem of the pure functional calculus of first order.

---


236 PURE FUNCTION ALCALCULUS OF FIRST ORDER [Ch a p. IV
Now let Ex, Ea, Ea, .
.
be an enumeration of the different elementary 
parts occurring in Glf C2, C3, . . 
according to the following order: first 
the different elementary parts of C1( in the order of their first occurrence in 
Cx; then the different elementary parts of C2 that do not occur in Cv in the 
order of their first occurrence in C2; then the different elementary parts of 
C8 that do not occur in Gj, Ga, in the order of their first occurrence in Cg; 
and so on.
We proceed to make a r'master assignment” of truth-values to Ex, Ea, 
Eg,.. .t as follows. If Ex receives the value t in infinitely many of the falsi­
fying assignments413 of truth-values to the elementary parts of Cv Ga, 
C3, . . 
we give ^  the value t in the master assignment; in the contrary 
case, Ex must receive the value f in infinitely many of the falsifying assign­
ments of truth-values to the elementary parts of G1( Ca, Ca, ,. 
and we give 
Ej the value f in the master assignment. Next we consider those infinitely 
many falsifying assignments of truth-values to the elementary parts of 
Ci, C2, Cg, . . . in which Ex receives the same truth-value as in the master 
assignment; if Ea receives the value t in infinitely many of these, we give Ea 
the value t in the master assignment; and in the contrary case we give Eg 
the value f in the master assignment. Next we consider those infinitely many 
falsifying assignments of truth-values to the elementary parts of Gx> C2, 
C3l . . . in which 1^ and Ea receive each the same truth-value as in the master 
assignment; if E3 receives the value t in infinitely many of these, we give Eg 
the value t in the master assignment; and in the contrary case we give 
Eg the value f in the master assignment. And so on.
Now suppose that the master assignment should result in the value t for 
one of 
Ga, C3, . . say for Cfc. The different elementary parts of Gfc are 
contained in a finite initial segment of Ex, Ea, Ea, , , say in E^ Ea, , . Ej. 
Let ev e2, . , , ,  et be the truth-values assigned to Eg, Ea, , . , ,  Ej respectively, 
by the master assignment. Then in view of the form of G1# Ga, Ca, . . .  as 
disjunctions, and in view of the truth-table of v, we have that no assignment 
of truth-values to the elementary parts of G); j >  k, can be a falsifying 
assignment if it includes the assignment of ev e2, . . 
et to Ex, Ea, .. ., Et
41#It may happen that there is more than one falsifying assignment of truth-values 
to the elementary parts of Cfc (though the number is always finite for a fixed Ck). 
In speaking of “ the falsifying assignments of truth-values to the elementary parts of 
C1( C„ CSl . . . 
we mean to include, for each C*. all the various falsifying assignments 
of truth-values to the elementary parts of C4.
In the special case n — 0, it may also happen that falsifying assignments of truth- 
values to the elementary parts of C* and of C, coincide in the sense that the list of 
elementary parts involved is the same and the truth-values assigned are the same; 
nevertheless we count the two assignments as different if A and / are different.

---


m
GOEDEL COMPLETENESS THEOREM
237
respectively. But this contradicts the rule which was used in assigning the 
truth-value ex to Et in the construction of the master assignment.
It follows that the master assignment results in the value f for every Gk. 
I.e., C1( C2, C3, . . . are simultaneously falsified by the master assignment.
Now we take the positive integers as domain of individuals, and proceed 
to assign values to the propositional and functional variables of A as follows. 
To a propositional variable p is given the same value as given to p in the 
master assignment. To an i- ary functional variable f is assigned as value 
an t-ary propositional function 0  of individuals, as determined by the 
following rule; 0 (ult u2l . . 
«,) has the same truth-value which is assigned
to f(zUl> xut> * * •> z u{) in the master assignment; or if no truth-value is 
assigned to f(zu ,x u^, . . ,,x Uf) in the master assignment, the truth-value 
of 0 (ult u2, ---- « £) is t.
This assignment of values to the propositional and functional variables of 
A is at the same time an assignment of values to the propositional and 
functional variables of each Bk and of each Gk. If we also assign to each in­
dividual variable xu the positive integer u as value, we have an assignment 
of values to all the variables of Bk and of C*. This assignment gives to C*. 
the value f (since we have proved that the master assignment falsifies (JA). 
Hence it also gives to B* the value f (since Gk is CH  V B*, and in view of 
the truth-table of v). Hence by rule f of §30 (or by the clause corresponding 
to rule f in the definition of “value" in the syntactical sense), it gives the 
value f also to
i.e., to
(b1)(b2) . . .  (b„)
(b.)(b.) . . .  (b.) S? ?  
M|.
v 1M a; 
v n/ 
1
This holds for all k ; and as k runs through all values, we know that 
xlk2)> * * 
mns through all possible w-tuples of the variables xu> and
hence that all possible substitutions are made of variables xu for a1( a 2, 
.
.
am. Hence the value f is given to
(3a1)(3 a2) . . . ( 3 a m)(bl)(b2) . . . ( b n)M.
Thus we have found an assignment of values to the propositional and 
functional variables of A such that the value of A is f. Therefore A is not 
valid.
This completes the proof of **440. We notice as a corollary the following 
metatheorem;

---


238 P U R E  F U N C T I O N A L  C A L C U L U S  O F  F I R S T  O R D E R  [Chap. IV
**441. 
If A is a wff in Skolem normal form,
(3ai)(3a2) . . .  (3am)(b1)(b2) . . .  (b„)M, 
if B* is the quantifier-free wff,
Cai a* 
bi 
bt 
”*b*» \|j
and if Cfc is Bx v B2 v . . . v BfcI then A is a theorem (and is valid) 
if and only if there is some positive integer k such that C* is a sub­
stitution instance of a tautology of P.
45. Ldwenheim’s theorem and Skolem’s generalization. In case 2 
of the foregoing proof of Godel's completeness theorem we have shown about 
an arbitrary wff A which is in Skolem normal form and is not a theorem that 
it is not valid in the domain of positive integers. Hence, if a wff in Skolem 
normal form is valid in the domain of positive integers, it is a theorem, and 
therefore by **434 it is valid in every non-empty domain. Hence by **437, 
if any wff is valid in the domain of positive integers, it is valid in every non­
empty domain.
Moreover, by **439, any enumerably infinite domain (in particular, e.g„ 
the domain of natural numbers) may take the place here of the domain of 
positive integers. Thus follows:
**450. 
If a wff is valid in an enumerably infinite domain, it is valid in 
every non-empty domain.414 
(Lowenkeim’s theorem.)
As a corollary by **431, we have also:
**451. 
If a wff is satisfiable in any non-empty domain, it is satisfiable in 
an enumerably infinite domain.
Skolem's generalization of this is the metatheorem that, if a class of wffs 
(it may be an infinite class) is simultaneously satisfiable in any non-empty 
domain, then it is simultaneously satisfiable in an enumerably infinite 
domain.
Here the definition of simultaneous satisfiability is the obvious generali­
zation of the definition of satisfiability of a single wff. Namely, a class T  
of wffs is said to be simultaneously satisfiable in a given non-empty domain 
of individuals if, of all the free variables of all the wffs of F taken together, 
there exists at least one system of possible values for which every wff of T
4UThus, if a wff is valid in the domain of natural numbers, it is valid also in non- 
enumerably infinite domains. If a wff is satisfiable in a non-enumerably infinite 
domain, it is satisfiable also in the domain of natural numbers.

---


§45]
L O E W E N H E I M - S K O L E M  T H E O R E M S
239
has the value t. (In the case of a finite non-empty class T  of wffs, it is clear 
that simultaneous satisfiability is equivalent to the satisfiability of a single 
wff, the conjunction of all the wffs of F.)
A class of wffs is said to be simultaneously satisfiable if it is simultaneously 
satisfiable in some non-empty domain of individuals.
We shall need also the following definitions (which we adopt not only for 
the case of the pure functional calculus of first order but also for other 
functional calculi of first and higher orders415 * *).
Where F  is any class of wffs and B is any wff, we say that FV B if there 
are a finite number of wffs Alf Aa, . . 
Amof r such that A1, Aa, . . .. Aw h B.
A class F of wffs is called inconsistent if there exists a wff B such that 
r\~ B and T h ^ B . If no such wff B exists, we say that r  is consistent.
Where JTis any class of wffs and C is any wff, we say that C is consistent 
with F  if the class is consistent whose members are C and the members 
(wffs) of r \  otherwise we say that C is inconsistent with F.
A class F of wffs is called a maximal consistent class if F  is consistent and 
no wff C is consistent with r  which is not a member of F.
We establish the following as a lemma:
**462. 
Every consistent class F  of wffs can be extended to a maximal 
consistent class F, i.e., there exists a maximal consistent class F 
among whose members arc all the members of r.
Proof. We shall give a rule by which the maximal consistent class F is 
uniquely determined when JTis given. (However, this rule will not be such 
as to provide in any sense an effective construction of the members of F.)
First the wffs must be enumerated, as is possible by well-known methods 
(since the primitive symbols are enumerable, and the wffs are certain finite 
sequences of primitive symbols).418 Then we shall speak of “the first wff," 
“the second wff,” and so on, referring to this enumeration of the wffs.
u#At one place below, we use also an obvious extension of the definition of simulta­
neous satisfiability to an applied functional calculus of first order.
41aFor example, wc may use the following enumeration of the wffs.
First take the enumeration of the ordered w-tuples of positive integers which was 
introduced in §44. And let us speak of the 6th w-tuple of positive integers to mean the 
6th w-tuple of positive integers in this enumeration. (In particular, wc shall speak in 
this way of the 6th ordered pair of positive integers.)
Then let the primitive symbols of the pure functional calculus of first order, as intro­
duced in §30, be enumerated as follows, The first eight primitive symbols in the enu­
meration are the eight improper symbols, in the order in which they are listed in §30. 
The (k -f- 8)th primitive symbol in the enumeration is: the rath individual variable in 
alphabetic order, if the 6th ordered pair of positive integers is <1, ra>; the rath prop­
ositional variable in alphabetic order, if the 6th ordered pair of positive integers is

---


240 P U R E  F U N C T I O N A L C A L C U L U S O F  F I R S T  O R D E R  [Chap. IV
And for every wff there is a positive integer n such that it is “the nth wff" 
(i.e., the nth wff of the enumeration).
Given any class J 1 of wffs, we define the infinite sequence of classes 
r°, n ,  r 2, . . 
(by recursion) as follows: P ° is the same as r . If the (« -|- I) th 
wff is consistent with f ”, then r n+l is the class whose members are the 
(« + l)th wff and the members of iT". Otherwise i"Tn+l is the same as P n.
It follows by mathematical induction that r ° , r 1, P 2, , .. are consistent 
classes of wffs if r  is consistent. For P° is the same as J1. And the consistency 
of P n+l follows at once from that of r n.
We let P  be the union of the classes r °, r \  P 2, . ... I.e., a wff C is a mem­
ber of r  if and only if there is some n such that C is a member of r n.
Now if r  is a consistent class, it follows that P  is a consistent class.
For suppose that P  is inconsistent. Then there are a finite number of 
wffs Av A2, . . 
Am of P. and a wff B, such that Ax, A2, . . Am h B and 
Alf A2, . . 
Am h ~B. Say that Ax is the c^th wff, A^ is the 
th wff,..., Am is 
the amth wff; and let a be the greatest of the positive integers av a$, . . am, 
Then all the wffs Ax, A2> . . ., A„, are members of Fa, and consequently P 1 
is inconsistent. But this contradicts our proof above that all the classes 
r ° t r it r i, . . . are consistent (if P  is consistent).
Moreover P  is a maximal class, if P  is consistent.
For let G be any wff which is consistent w ith/'.Say that G is the (n +  1) th 
wff. Being consistent with P, C must be consistent with /*n. Therefore, by 
the definition of P n+1, C is a member of P n+1. Therefore C is a member of P.
Thus the proof of the lemma, **452, is completed. We observe that a 
corresponding lemma holds not only for the pure functional calculus of 
first order but also for any applied functional calculus of first order if the 
primitive symbols are enumerable. And indeed **452 can be extended to a 
wide variety of logistic systems, since the proof requires only a suitable 
notion of consistency of a class of wffs, and the enumerability of the primi­
tive symbols of the system.417
<2, t»>; and the wth i-ary functional variable in alphabetic order, if the Ath ordered 
pair of positive integers is <* 4- 2, w>.
And let us speak of the /zth prim itive symbol to mean the fjXh primitive symbol in 
the foregoing enumeration.
Then let the formulas of the pure functional calculus of first order be enumerated by 
the rule that, if the Ath order pair of positive integers is </*, m> and the f i th w-tuple of 
positive integers is 
. • . /um>, then the Ath formula in the enumeration is
where ^  is the /Zjth primitive symbol, (£f is the /zgth primitive symbol, 
.. ., 
is the yumth primitive symbol.
Finally, from the enumeration of the formulas, delete all those which are not 
well-formed, so obtaining an enumeration of the wffs.
4l7This last is presumably a consequence of requirement (I) of §07.

---


§45]
LOEWENHEIM-SKOLEM THEOREMS
241
We now consider an infinite sequence of applied functional calculi of first 
order S0, Sx, S2, . .
having as primitive symbols all the primitive symbols 
of the pure functional calculus of first order and in addition certain individual 
constants. Namely, the primitive symbols of S0 are those of the pure func­
tional calculus of first order and the individual constants wQ Q, w1Ql 
.. .; 
the primitive symbols of Sn+X are those of S„ and the additional individual 
constants w0in+1, w1$n+l, wM +l........
Also we let Sm be the applied functional calculus of first order which has 
as its primitive symbols the primitive symbols of all the systems S0, S3j 
Ss, . . .. (Thus the individual constants of Sm are all the constants wmn, for 
m =  0 , 1, 2, . . . and n =  0, 1 , 2, . . ..)
In the same way that we have already remarked for the pure functional 
calculus of first order, it is possible to enumerate the wffs of S^. Then, in 
the case of each Sn, an enumeration of its wffs is obtained by deleting from 
the enumeration of the wffs of Sw those which are not wffs of Sn. And re­
ferring to this enumeration we shall speak of "the first wff of Sn," "the 
second wff of Sn," and so on.
Using these enumerations, we can extend any consistent class A7l of wffs 
of Sn to a maximal consistent class A ni of wffs of Sn, by the method stated 
above in the proof of **452.
Now let a consistent class Z0 be given of wffs of S0 which have no free 
individual variables. We define the classes Z™ [m =  0, 1, 2, 3, . . . and 
n — 1, 2, 3, . . .) as follows: Z° is Z0. If the [m 4  l)th wff of S„, n >  0 , 
has the form ~(a)A and is a member of Z°, then JP^ 1 is the class whose 
members are
and the members of Z” ; otherwise Z™+1 is the same as Z™. A ndZ °+1 isA n, 
where A n is the union of the classes JP°, Z B, IP*, . . ..
Evidently the members of Z™ are wffs of SB. And Z £+1 is a maximal con­
sistent class of wffs of Sn;
Assume that, for some particular m, Z™is consistent but Z £+ lis incon­
sistent. Then we must have the case that Z ^ +1 is not the same as Z ” but has 
the additional member
By the inconsistency of Z B+\  and the deduction theorem,
n
 H -S -..,. A! =  B
a n d

---


242 PURE FUNCTIONAL CALCULUS OF FIRST ORDER [Chap. IV
C  «- 
A| => ~B.
Hence by P,
n
 i- 
ai
Let x be an individual variable which does not occur in this proof 
from hypotheses, and in it replace the constant wmn everywhere by x; 
since wm n does not occur in any of the members of JT” , we thus have:
m  i- s “x A|.
By generalizing upon x ,418 and then making one or more alphabetic changes 
of bound variable, we have that JT” h (a)A; but since ~(a)A  is a member of 
J 1® and therefore of JT” , this contradicts the assumption that F™ is consistent. 
Thus we have proved that, if JT™ is consistent, then 7’™4'1 is consistent. 
By mathematical induction, it follows that, if JT® is consistent, then JF^is 
consistent for every m, and therefore jT®+1 is consistent. Since F j is the same 
as r», and is therefore consistent, it follows by a second mathematical in­
duction that JT® is consistent for every n.
Let Fw be the union of the classes JTJ, JTj, JT®,. . . .  Then /*„ is a maximal 
consistent class of wffs of Su. (For Fa could be inconsistent only if, for some 
n, JT® were inconsistent. Further, if C is a wff of Sw consistent with Fm, then, 
for some nt C is a wff of Sn and is consistent with / 1®+1; since JT®+1 is a maximal 
consistent class of wffs of Sn, it follows that C is a member of -T®+1 and 
therefore a member of Fm.)
We need the following properties of Fa:
dl. If A is a member of Fm, then ~A is a non-member of Fa. (For other­
wise Fm would be inconsistent.)
d2. If A is a non-member of Fal then ~A is a member of Fm. (For, if A 
is a non-member of JTW, then A must be inconsistent with 
therefore, by 
the deduction theorem and P, r a h ~A; therefore ~A is consistent with Fa; 
therefore ~A  is a member of Fa.)
el. If B is a member of 
then A z> B is a member of 7^. (For by P, 
A=> B; thus A z> B is consistent with Fa and therefore a member of
r
m .)
e2. If A is a non-member of F^, then A z> B is a member of Fa. (For by 
d2, ~A is a member of 7^, and therefore by P, JTU 1- A 
B.) 
e3. If A is a member of Fm and B is a non-member of 7^, then A 
B is a
4llThis is permissible because x does not occur in any of the members of T7” which 
are here actually used as hypotheses in the proof of
5Sai

---


LOEWENHEIM-SKOL EM THEOREMS
243
non-member of Tm, (For by d2, ~B  is a member of JT^; hence, if A 
B were 
ft member of Tm, r w would be inconsistent, by an application of modus po- 
nens.)
fl. If, for every individual constant
sL, a,
Is a member of JPto, then (a) A is a member of Fm. (For, if (a) A is not a mem- 
her of r a, it follows by d2 that ~(a)A is a member of 7^; hence, for some 
~(a)A is a member of r%; hence, by the way in which the classes 7'£5+x 
were defined, we have for some m that
~S
a
wm,n A|
is a member of F^ 1 and therefore a member of r a; thus by dl we have for 
some m and n that
a
is a non-member of JTW.)
f2. If, for at least one individual constant wtn,nr
s
A
Is a non-member of Fmi then (a) A is a non-member of r a. (For, if (a) A is a 
member of jPw, we have by *306 and modus ponens, for an arbitrary individ­
ual constant wmint that
and hence that
being consistent with Fat must be a member of Fa.)
Taking the natural numbers as domain of individuals, we now assign 
Values to all the propositional and functional variables of Su —or, what is 
the same thing, to all the propositional and functional variables of the pure 
functional of first order—as follows:
To a propositional variable p is assigned the value t if the wff p is a 
member of r a, the value f if the wff p is a non-member of JPw. Letting «mp„ 
be the natural number \(m z 4 - 2mn +  n2 4- 3m -r «),419 we have for each
•“This corresponds in an obvious way to the following enumeration of the ordered 
pairs of natural numbers,
<0. 0>,<0, 1>,<1, 0>,<0, 2>A l, i>.s 2. 0>a O, 3>.........
fttt&logous to the enumeration of the ordered m-tuples of positive integers which was 
introduced in §44.

---


244 PURE FUNCTIONAL CALCULUS OF FIRST ORDER [Ch a p. IV
individual constant wmpn a unique corresponding natural number «mj„, and 
for each natural number umtn a unique corresponding individual constant 
wmpn. Then to an i-ary functional variable f is assigned as value the t-ary 
propositional function 0  of individuals such that0 («m n um%pn%l . . 
is t or f according as f (w*, n , wm9,nt, .
.
is a member or a non-member
of r a.
Now notice the way in which dl and d2 above are related to rule d 
of §30, and el, e2, e3 are related to rule e of §30, and fl and f2 are related to 
rule f of §30. From this relationship (or, more correctly, we should speak of 
the relationship to the clauses which correspond to rules d-f in the definition 
of "value” in the syntactical sense) it follows that every wff of Sw without 
free individual variables has, for the system of values that we have just 
assigned to the propositional and functional variables of Sm, the value t or 
the value f according as it is a member or a non-member of Fm. (It is left 
to the reader to state the proof of this explicitly by mathematical induction.)
Since the members of F0 are without free individual variables and are 
included among the members of JTW, we have thus shown that JT0 is simulta- 
neously satisfiable in the domain of natural numbers, hence, by an obvious 
extension of **439, simultaneously satisfiable in any enumerably infinite 
domain.
But r 0 was chosen as an arbitrary consistent class of wffs of S0 without 
free individual variables. Hence every consistent class of well-formed formulas 
of S„ without free individual variables is simultaneously satisfiable in an 
enumerably infinite domain (with such an assignment of values to the individ­
ual constants as to give a different value to each).
To extend this result to any consistent class of wffs of the pure functional 
calculus of first order, we have only to substitute, for the free occurrences 
of individual variables, individual constants wnpXt, in such a way that a 
different individual constant is substituted for the free occurrences of each 
different individual variable.
Thus we have the following metatheorem of the pure functional calculus 
of first order:
**453. 
Every consistent class of wffs is simultaneously satisfiable in an 
enumerably infinite domain.
We need also the following:
**454. 
Every simultaneously satisfiable class of wffs is consistent.
Proof. Let F be an inconsistent class of wffs. Then there are a finite

---


EXERCISES 45
2 U>
i w
number of wffs A,, A2, . . ., Am of r . and a wff B, such that \ lt A2, . .
I" B and Av A2, . , 
Am I- ~ B.  By **321, m >  0. Therefore by the de­
duction theorem and P, Y ~ . A ^  . . . Am. Therefore by **434, -  . A XA 2 
. . .  Am is valid. In view of the truth-table* of negation and conjunction, it 
follows that Aj, A2, . . 
Am cannot have the value t simultaneously, for any 
System of values of their free variables. Thu* r  cannot be simultaneously 
Sfttisfiable.
From **453 and **454 we obtain as a corollary the result of Skolem which 
vas mentioned at the beginning of this section:
♦455. 
If a class of wffs is simultaneously satisfiable in any non-empty 
domain, it is simultaneously satisfiable in an enumerably infinite 
domain.
It is worth noticing that Godel's completeness theorem and Lowenheim's 
theorem now follow as corollaries, so that we obtain alternative proofs of 
these theorems, in which there is no use of the Skolem normal form or of §44.
In the case of Godel's theorem, this is seen as follows. Let A be any valid 
wff. Then by **430, the class whose single member is ~A is not simulta­
neously satisfiable. Therefore by **453, this class is not consistent. Therefore, 
lor some wff B, both -A  1- B and ~A i- ~B, Therefore by the deduction 
th e o re m  and P, Y A.
EXERCISES 45
45*0* Carry through the proof of **440 (as given in §44) explicitly for the 
case that n — 0, making such simplifications as are possible in this special 
case, and verifying that the proof is sound also for tins case.
4 5 .I . Establish **454, without use of **321 and **434, by showing 
directly that the process of proof from hypotheses, as defined in §36, pre­
serves the property of having the value t for a given system of values of the 
fe e  variables of the hypotheses (and for all values of the other free variables 
Occurring).
4 5 .* . On the basis of thedefinition of validity (§43) and of the two proofs 
Of **440 that are given in the text (§§44 and 45), discuss the questions, 
(1) whether **440 may be used as a derived rule of inference of the pure 
functional calculus of first order, and (2) whether **440 may be used in the 
foie of an axiom schema in a formulation of the pure functional calculus of 
first order. (See the discussion of the logistic method and the definition of a 
logistic system in §07, the distinction in §08 between elementary and theoret­

---


246 PURE FUNCTION A L CALCULUS OF FIRST ORDER
ical syntax, the introduction of the idea of derived rules of inference in §12, 
and the remarks of footnotes 183, 221.)
45-3* Prove the completeness of the propositional calculus, in the formu­
lation P1( by applying the ideas used in the text in the proof of **452 and 
**453. Compare this completeness proof for the propositional calculus with 
the completeness proof of Chapter I, especially as regards the question of 
a stronger or weaker basis on which results are obtained (cf. the initial 
paragraphs of §08).
45*4* Let a class/ 1 of wffs be given, and a particular valuation of P in  the
domain of natural numbers, i.e., with the natural numbers as the individuals, 
a particular system of possible values of the free variables of the wffs of 71, 
And suppose that, for this valuation, every wff of P  has the value t. Show 
that the method which is employed in §45 (in the proofs of **452 and **453), 
to obtain a valuation of P  for which every wff of P  has the value t, can be 
made to yield the given particular valuation of P  by a suitable choice (a) 
of the enumeration of the wffs that is used, and (b) of the correspondence 
that is used, not necessarily a one-to-one correspondence, between the 
constants n-min and the natural numbers «rn>n.
45*5* Let a class P  of wffs be called disjunctively valid in a given non­
empty domain of individuals if, for each valuation of P  in that domain, there 
exists at least one wff of P  which has the value t. (1) If a class of wffsfc 
disjunctively valid in an infinite domain, then the disjunction of some finite 
subclass of them is valid. (2) If a class of wffs is disjunctively valid in a 
finite domain, then the disjunction of some finite subclass of them is vali^ 
in that domain.
46. The decision problem, solution in special cases. Though the
decision problem of the pure functional calculus of first order is known to be 
unsolvable—in the sense that no effective decision procedure exists which 
suffices to determine of an arbitrary wff whether or not it is a theorem4**— 
there nevertheless exist solutions in a number of special cases421 which have
4,0Alonzo Church m The Journal of Symbolic Logic, vol. 1 (1936), pp. 40-41, 101-102. 
Hilbert and Bernays. (jfundlagen tier Mathemalik, vol. 2, Supplement H.
**lBy a solution of the decision problem in a special case we mean that there shall be 
given a special class of wffs. an effective procedure to determine of an arbitrary wff 
whether it belongs to this class (this will be obvious in most cases discussed below), 
and an effective procedure to determine of any wff of this class whether it is a theorem* 
To this we seek always to add an effective procedure by which to find a proof of any 
wff which has thus been ascertained to be a theorem—but this last requirement is 
subject to the reservations that are indicated in footnote 183.
[Added in proof,) A comprehensive treatm ent of solutions of the decision problem 
in special cases is in Wilhelm Ackermann’a monograph. Solvable Cases of the Decision 
Problem (1984).

---


§46] 
THE DECISION PROBLEM, SPECIAL CASES
247
some substantial interest. Some of the simpler of these will be treated in 
this section.
We begin with a solution of the decision problem (due to Bernays and 
Schonfinkel) for the special case of:
I 
Well-formed formulas having a prenex normal form such that, in the 
prefix, no existential quantifier precedes any universal quantifier.
It will be sufficient, by §39, and *301, *306, to find a decision procedure 
for the universal closure of the prenex normal form of the wff. Hence the 
Solution of this case of the decision problem is contained in the four following 
metatheorems:
*460. 
Let M be a quantifier-free formula, and let b1( b2, , . 
bn (» ^  0) 
be the complete list of individual variables in M. If any afp of M is a 
tautology,
t- (3b1)(3ba) . . . (3bn)M.
Proof. 
is a substitution instance of the afp of M and is
therefore a theorem by *311. Hence use *330 and modus ponens.
**461. 
Let M be a quantifier-free formula, and let blt b2, . . 
b„ (n 
0) 
be the complete list of individual variables in M. If
f- f l b ^ b . ) . . .  (3bn)M,
every afp of M is a tautology.
Proof. Every afp of M becomes an afp of
( a b ^ b , ) . . .  (3bn)M
upon prefixing 2n negation signs, 
Hence use **320 and the truth-table 
of negation.
*462. 
Let M be a quantifier-free formula, and let ax, a2, . . 
am, b v  b2 
- • 
bn (m ^  1, n ^  0 ) be the complete list of individual variables 
in M. If the disjunction D of all the wffs422
mi
is a substitution instance of a tautology of P, where dx, d2, . . 
dn
4MThe order in which these m" different wffs are combined into a disjunction is 
evidently immaterial, in view of the commutative and associative laws of disjunction. 
In order to make the decision procedure definite, it may be fixed in some arbitrary 
(effective) way.

---


248 PURE FUNCT10NALCALCULUS0F FIRSTORDER [Ch a p.IV
are any among the variables a,, a2, . . 
am, taken in any order and 
not necessarily all different, then
I- (al){a2) . . . (am)(3b1)(3b2) . . . (3bn)M.
Proof, By *330 and modus ponens,
SS&::£ M| H (3b1)(3b2) . . .  (3bn)M.
Hence by the deduction theorem and P,
DH(3b1)(3b2) ...( 3 b n)M.
Therefore, since D is a substitution instance of a tautology, we have by 
*311 that
H(3b1)(3b2) ...( 3 b n)M.
Hence by generalization,
I
-
•• • ( a j f lb j f lb ,) ... (3bn)M.
**463. 
Let M be a quantifier-free formula, and let a1( a2, . . am, bXl ba, 
.. 
bn (m ^  1, n 
0 ) be the complete list of individual variables 
in M. If
I- («i){a*) ■ • • (amJlHbJCSbj) . . .  (3b„)M,
then the disjunction D of all the wffs4aa
mi
is a substitution instance of a tautology of P, where d lt d2, .. 
dn 
are any among the variables a1( a2, . . 
am, taken in any order and 
not necessarily all different.
Proof. By *306 and modus ponens, (3b1)(3b2) . . . (3bn)M is a theorem. 
Therefore by **434 it is valid, hence, in particular, valid in a domain of m 
individuals uv u2, , . 
um.
Taking this finite domain of individuals, consider any system of possible 
values of the free variables of (3b1)(3b2) .. .(3bn)M such that the values of 
ax, a2, ., 
am are 
u2, .. 
um respectively. For this system of values of its 
free variables {3b1)(3b2) . . . (3bn)M has the value t. Hence by the def­
inition of value (rules d and f of §30), for this same system of values of the 
variables and for certain values ui t w*, , . 
uin of bv b2, . . 
bn respectively, 
M has the value t. If d x> d2, . .
dn are chosen as a^, af , . .  
a<(| respectively,
then
Sb,b,.;;b„ M|
has the value t. Therefore—still for the same system of values of the free

---


m
THE DECISION PROBLEM, SPECIAL CASES
249
variables of (3b1)(3 b 2) . . . (3 b n)M —the disjunction D has the value t.
Since the free variables of Dare the same as those of (3b1)(3b2) .. .(3bn)M 
we have thus shown that—for this finite domain of m individuals, and for 
any system of possible values of the free variables of D such that a1( a 2, 
. .
am have the values 
u2, . . 
um respectively—the value of D is t. Now 
given any assignment of truth-values to the elementary parts of D ,4*3 it is 
clear that (because the values of a1( a 2, . .
am are all different) it will always 
be possible to choose the values of the propositional and functional variables 
of D in such a way as to reproduce the given assignment of truth-values to 
the elementary parts of D. Therefore D has the value t for every assignment 
of truth-values to its elementary parts. Therefore D is a substitution instance 
of a tautology of P.
In *462 and **463, it is now clear that the condition that D is a substi­
tution instance of a tautology is equivalent to the condition that
(a1)(a2) . . . ( a m)(3b1)(3b 2) . . . ( 3 b n)M
is valid in a domain of m individuals. Also in *460 and **461, the condition 
that an afp of M is a tautology is equivalent to the condition that
(3b 1)(3 b 2) . . . ( 3 b n)M
is valid in a domain of a single individual. Hence we have the following 
corollary of *460-* *463:
*464. 
Let M be a quantifier-free formula, and let ax, a2, . . 
am, bv b 2, 
. . 
bn (m ^  0, n ^  0) be the complete list of individual variables 
in M. Then
(a^tea) . . .  (am)(3bj)(3b2) . . .  (3bn)M
is a theorem if it is valid in a domain of m individuals, or, in the case 
m =  0 , of a single individual.
Since the definition of validity in a domain leads immediately to an effec­
tive test for validity in any particular finite domain—and since, by **434, a 
theorem must be valid in all non-empty domains, including finite domains— 
we may regard *464 as stating an alternative form of our solution of the 
special case I of the decision problem. Indeed it is in this latter form that
4l,Where the same elementary part occurs more than once in D, of course it is meant 
that the same truth-value is assigned to it at all of its occurrences.
(As defined in §30, the elementary parts of a wff are those wf parts which have either 
the form of a propositional variable alone or the form f(ax, a8, . . . , a n).)

---


250 PURE FUNCTIONAL CALCULUS OF FIRST ORDER 
[Ch a p. IV
the solution is more usually stated. And we shall introduce a corresponding 
form of statement of the solution (referring to validity in a specified finite 
domain) also in some other cases below.
We turn now to consideration of another decision procedure, which is 
applicable in a variety of cases. It will be convenient first to state the de­
cision procedure itself, before considering the question of characterizing a 
class of wffs to which it is applicable.
A particular occurrence of a wff P  as a wf part of a wff A is called an 
occurrence as a truth-functional constituent, or, as we shall also say, an occur­
rence as a P-constituent, in A if it is not within the scope of a quantifier and 
does not have either of the forms ~ B  or [Bt :d B 2]. And the truth-functional 
constituents, or the V-constituents, of A are those wffs which have occurrences 
as P-constituents in A.
It is clear that each of the P-constituents of a wff either is an elementary 
part or else is of the form (a)B. Moreover, any wff can be thought of as 
obtained from a wff of P by substituting its P-constituents in an appropriate 
way for the propositional variables; and, for a particular wff, the wff of P 
and the required substitution are determined uniquely to within an alpha­
betic change of propositional variables.
As a first step in the decision procedure we are about to describe, we reduce 
(separately) each P-constituent of the given wff to prenex normal form, and 
if any of the P-constituents are then found to differ only by alphabetic 
changes of bound variables, we make the appropriate alphabetic changes 
of bound variables to render them identical.424 Let A be the wff so obtained. 
(Evidently the given wff is a theorem if and only if A is a theorem.)
If A  has just m different P-constituents, P 1( P 2). . ., P m, then for each 
of the 2m different systems of truth-values of these P-constituents we may 
ascertain the corresponding truth-values of A. (The work of doing this may 
be arranged in the same way as described in §15 for the case of wffs of the 
propositional calculus.) If the value of A is found to be t for all systems of 
truth-values of its P-constituents, then b A by *311. Otherwise we list all 
the falsifying systems of truth-values of the P-constituents of A, i.e., the 
systems of truth-values for which the corresponding value of A is f. And
‘“ In practice it will be desirable also to make at this stage any preliminary simplifi­
cations by propositional calculus that are seen to be possible, both to the wff as a whole 
(the P-constituents being treated as units) and within the m atrix of each separate 
P-constituent. Especially, if any of the P-constituents can be rendered identical by 
such simplifications of their matrices, together with alphabetic changes of bound varia­
bles, this should be done; and it may be desirable to test systematically for the possi­
bility of this, by the truth-table decision procedure (§15).

---


§46]
THE DECISION PROBLEM, SPECIAL CASES
2 5 1
then we make use of the following metatheorem, which has an obvious 
connection with the conjunctive normal form:
*465. 
Where A is any wff, let the complete list of the P-constituents of A 
be Pv P2j . . 
Pm, and let the complete list of falsifying systems of 
truth-values of the P-constituents of A consists in the systems of 
values t[, tJ, . .
of Pv P2, . .  
Pw respectively [i =  1, 2, . . ., w). 
Let Pj be P* or ~P^ according as rj is t or f. Then b A if and only if 
all of the wffs
are theorems.
Proof, For every system of truth-values of Px, P2, . . 
Pmj the value of 
A is f if and only if the value of one of the wffs
p ‘ = >.  p ;  = > . . . .  P L x  ^
is f. Consequently
A  S  [P} =) . P i  =) . . . .  P L x  =  - P i . ] t P j  =  ■ PS =  ■ • • ■ K - i => - P n J  
• • • [p: => ■ p." => • ■ ■ • p^i ^'-p;^
is a substitution instance of a tautology, and therefore a theorem by *311. 
Hence, by P, if H A, all of the wffs
P{ 3  . P ‘ ID . . 
P ;_ j =  -P t,
are theorems, and conversely, if all of these wffs are theorems, then h A.
Thus the decision problem for A is reduced to the decision problem for 
the wffs
P* => . P‘ =) . . . . P U  3  ~P^.
We deal with these latter wffs by reducing them to a prenex normal form, 
since decision procedure are known for wffs in prenex normal form with 
prefixes of various special kinds. According to the fixed procedure of §39 
for reduction to the prenex normal form, the quantifiers are taken one by 
one in left-to-right order and brought forward into the prefix. Here, however, 
we vary this fixed procedure by allowing the quantifiers to be taken (and 
brought forward into the prefix) also in any other order that is feasible. 
And we endeavor in this way to obtain a prefix of one of the kinds for which 
a decision procedure is known. E.g., if we succeed in obtaining, in all of the 
n cases, a prefix in which no existential quantifier precedes any universal 
quantifier, we are then able to decide whether A is a theorem by using our 
previous solution of the decision problem for the special case I.

---


252 PURE FUNCTIONAL CALCULUS OF FIRST ORDER 
[Ch a p. IV
In particular, such a reduction to the special case I can always be obtained 
when the foregoing procedure is applied to any one of the:425
II 
Well-formed formulas in which every truth-functional constituent either is 
quantifier-free or has a prenex normal form that has only universal 
quantifiers in the prefix.
We mention also the following subcase of II as of especial importance:
II' 
Well-formed formulas in which there are no free individual variables and 
in which every truth-functional constituent either is quantifier-free {there­
fore a propositional variable) or has the form (a)M, where M is quantifier- 
free and contains no propositional variables.
In the subcase IF the two following simplifications of the decision proce­
dure are possible, as it is left to the reader to verify:
(1) 
Suppose that the P-constituents of A are numbered in such an order 
that Plf P2, . . 
Pjt are the ones which are propositional variables, and the 
remaining P-constituents are Pfc+1, 
• * * * •> Pm- Then in applying *465 
we may simplify the conclusion of the metatheorem as follows: h A if and 
only if all of the wffs
Plfl =» ■ P*+2 =>■••• PL l  =  ~ Pm
are theorems.
(2) 
By alphabetic changes of bound variables we may suppose that A 
has been brought into such a form that only the one individual variable x 
occurs. Then P*+1, Pi+2, . . 
P,„ have the forms (x)M*+1, (a?)Mfc+a, . .
respectively, where 
M*+2l . . 
Mm are quantifier free and
contain no propositional variables and no individual variables other than x. 
From a particular falsifying system of truth-values tj, tj, . . 
of Pl# P2. 
.. 
Pm select the last m — k truth-values 
t*+2, . . 
and among 
these suppose that x \t 
. . ., x\t are t and tJ , tJ , .. 
are f. Then in
order that
446As a m atter of fact, whenever such a reduction to the special case I is possible, it 
will always be possible also to reduce more directly to case I. Namely, among the various 
prenex normal forms to which A can be reduced, there will always be one in whose pre­
fix no existential quantifier precedes any universal quantifier. B ut by making use of
*465 in the way described, it is possible more easily to control the kind of prefix which 
is obtained and often also, especially in case II„ to shorten the work otherwise.
When the procedure described in the text, by making use of *465, results in a reduc­
tion to one of the special cases V -IX  th at are listed at the end of this section, it is not 
necessarily true th at one of the prenex normal forms of the given wff A will also 
fall under one of these cases. And in this way solutions may be obtained of additional 
special cases of the decision problem.

---


§48] 
THE DECISION PROBLEM, SPECIAL CASES 
253 
K+x => - P £ta = > - ■• •  P L  ^
shall be a theorem, it is necessary and sufficient that at least one of the 
quantifier-free formulas
Mt, =3 ■ 
=> ■ ' • • Mi, => M/,
shall be a substitution instance of a tautology {/ =  1, 2, . . 
m — k — l).
Returning to the general case of the above-described decision procedure 
(based on *465), we notice that, roughly speaking, the finer the division of 
A obtained by dividing A into its P-constituents, the greater is the chance of 
success in determining by this procedure whether A is a theorem. Therefore 
before applying the decision procedure to a given wff A it may be desirable 
first to reduce A as far as possible by means of the reduction steps (a)-(g) 
of exercise 39.6.42fl
In particular, as proved in exercise 39.6, if A contains none but singulary 
functional variables, the reduction process of that exercise suffices to reduce 
the universal closure of A to the case IT which we have just treated. This is 
Quine's solution of the decision problem for the special case of:
III 
Well-formed formulas of the singulary functional calculus of first order.
The history of this case of the decision problem is described in §49. Besides 
Quine’s solution (which goes back to Behmann), another approach may be 
based on the following metatheorem of Bernays and Schonfinkel:427
**466. If a wff of the singulary functional calculus of first order is valid in 
a domain of 2^ individuals, where N is the number of different func­
tional variables appearing, then it is valid in all domains of individ­
uals.
Proof. We may suppose, by **432, that the given wff has no free individual 
variables. Let the propositional variables appearing be px, p 2, . . 
p ( and
<MThe reduction process may be shortened by adding corresponding reduction steps 
for connectives other than implication and negation, so as to be able to deal directly 
with a wff abbreviated by means of D3- II (as well as 014} rather than first to rewrite 
it in unabbreviated form. The full disjunctive and full conjunctive normal forms may 
also be found useful, as in 39.8. Or the implicative normal form (15.4) may replace the 
full disjunctive normal form, and the full conjunctive normal form may be used in the 
modified version that appears In the proof of *405. Detail* of organizing the reduction 
process in the most efficient m anner are left to the reader.
MTIn practice the decision procedure of **400 is generally longer and therefore less 
advantageous than Quine's. B ut even Quine's procedure may become forbiddingly 
long in comparatively simple cases, as the reader may see by applying it, for instance, 
to 40.12(3).

---


254 PURE FUNCTIONAL CALCULUS OF FIRST ORDER [Chap. IV
the functional variables, fx, f2, . . 
f^; and consider a system of values
rv r2, • • 
0 lt 0 2, . .., 0 N of these variables in order, the domain of in­
dividuals being some arbitrary non-empty domain U. Let the individuals 
pf U be divided into classes by the rule that ux and w2 belong to the same class 
if and only if the truth-values ^ (t^ ), 0 %{ux) , . .  
are identical with
the truth-values 0 x{u2), 0 z(u2) , . . 
0 N(u2) respectively. Thus are obtained
at most 2^ non-empty classes of individuals, call them vlt v2, . . 
vn 
(1 5* m ^  2^J, And let singulary propositional functions *FV 
lPN
of these classes be defined by the rule that ^(v*) is the same truth-value as 
0 i{u), where u is any member of the class vjt
Now we may take also the finite domain S3, consisting of the individuals 
vlt v2, . . 
vn and consider the values rv r2, . .
r(, *PV !F2j . . 
*PN of 
Pi. P2. * * 
Pi. 
• ■ •. fjv respectively. For this system of values of its
free variables the given wff has the value t (because, being valid in a domain 
of 2N individuals, it is by **439 valid in the domain S3). But from the way 
in which the propositional functions xPi were defined it follows that the given 
wff has the same value for the domain S3 and for the system of values
*1. 
........ n  f v . . . .  y N of its free variables that it does for the domain
U and for the system of values t1(t2i . . .t xx, 0 v 0 z> • . *,0 n °* 
*ree 
variables. Therefore the value of the given wff is t also for the domain U 
and for the latter system of values of its free variables.
Thus we have shown about the given wff that its value is t for an arbitrary 
system of values of its free variables and for an arbitrarily chosen domain U- 
I.e., we have shown that it is valid.
It will be observed that **466 is stated not as a solution of a special case 
of the decision problem (i.e., of the decision problem for provability) but 
rather as a solution of a special case of what we shall call the decision prob­
lem for validity, i.e., the problem of finding an effective procedure to deter­
mine validity.
By Godel's completeness theorem (as proved in §44, and by another 
method in §45) it is true in one sense that a solution of a special case of the 
decision problem for validity is also a solution, in the same special case, of 
the decision problem. But in another sense—which we have not attempted 
to make precise—this is not true, as may be seen from the fact that the proof 
of **466 provides no effective method of finding a proof of a wff A which 
passes the test of containing none but singulary functional variables and 
being valid in a domain of 2^ individuals.488
4” On the other hand, our demonstration of Quine's solution of the special case TII

---


§46]
THE DECISION PROBLEM, SPECIAL CASES
255
Closely related to the decision problem for validity is the decision problem 
for satisfiability, i.e., the problem of finding an effective procedure to de­
termine satisfiability. By **430 and **431, every solution of a special case 
of either of these problems leads to a solution of a corresponding special 
case of the other, so that the two problems need not be considered separately. 
In much of the existing literature on the subject, it is the decision problem 
for satisfiability to which attention is primarily given. And apropos of the 
importance of this problem it should be observed that (by Godel’s complete­
ness theorem) the consistency of a logistic system obtained by adding postu­
lates428 to a simple applied functional calculus of first order is always equiv­
alent, in an obvious way, to the satisfiability of a corresponding wff of the 
pure functional calculus of first order.
T h e pure fu n ctio n a l calcu lu s of first order becom es a form alized language 
upon ad o p tin g  o n e o f th e  p rincip al in terp reta tio n s (§30). T h e d o m a in  o f in d i­
vid u a ls on w h ich  th e in terp reta tio n  is b ased m a y  be either in fin ite or finite. In 
th e form er case th e semantical decision problem of the lan gu age (as defined in 
§15) is eq u iv a len t to  th e  decision  p rob lem  for v a lid ity , in the sen se th a t a n y  
so lu tio n  of a sp ecia l ca se o f eith er prob lem  is also a solution, in th e sam e sp ecial 
case, of th e other. In th e la tter case th e  sem an tical decision, p roblem  of the 
la n gu age is e q u iv a len t to  th e d ecision  p rob lem  for v a lid ity  in th e sam e finite 
d om ain  and is th erefo re co m p letely  so lv ed  (on the a ssu m p tion  th a t the finite 
d om ain  is g iv en  in  su ch  a w ay th a t th e n u m b er of in d ivid u als is k n ow n ).
We shall not here treat further the question of special cases of any of these 
decision problems, but we conlcude merely by recording the existence of 
solutions of the decision problem or of the decision problem for validity in 
each of the following cases (either explicitly in the literature or easily ob­
tained by methods existing in the literature):430
of the decision problem does (implicitly) provide such an effective method of finding a 
proof of a wff which passes the test. In order to accomplish this also in connection with 
the Bemays-Schdnfinkel solution of case III, the method may be followed which is 
suggested below in exercise 46.1.
•■•Compare §55, as well as the discussion of the axiomatic method at the end of §07. 
4S0See Wilhelm Ackermann in the Mathematische Annalen, vol. 100 (1928), pp. 
638-049; Thoralf Skolem in the Norsk Matematisk Ttdsskrift, vol. 10 (1928), pp. 
125-142; Jacques H erbrand in the Comptes Rendus des Stances de la Societe des Sciences 
et des Lettres de Varsovie, Classe III, vol. 24 (1931), pp. 12-56; Kurt Gttdel in Menger's 
Ergebnisse eines Matkematischen Kolloquiums, no. 2 (for 1929-1930, published 1932), 
pp. 27-28; L&szld Kalm&r in the Mathematische Annalen, vol. 108 (1933), pp. 466-484; 
GOdel in the Monatshefte fur Mathematik und Physik, vol. 40 (1933), pp. 433-443; 
K urt Schutte in the Mathematische Annalen, vol. 109 (1934), pp. 572-603. and vol. 
110 (1934). pp. 161-194; Ackermann m the Mathematische Annalen, vol. 112 (1936), 
pp. 419-432,
Whenever in these papers the results arc given in the form of solutions of special 
cases of the decision problem for satisfiability, they may be restated as solutions of

---


266 PURE FUNCTIONAL CALCULUS OF FIRST ORDER [Ch a p. IV
IV 
Well-formed formulas A such that in each elementary part at most one
variable has occurrences at which it is a bound variable of A.
V 
Well-formed formulas having a prenex normal form in which the matrix
satisfies the condition of being a disjunction of elementary parts and
negations of elementary parts or equivalent by laws of the propositional 
calculus to such a disjunction 431 432 *
VI 
Well-formed formulas having a prenex normal form with only one 
existential quantifier in the prefix, i.e.f with a prefix of the form 
(ai) (a2> • • ■ (am)(3b )(Cl)(c.,) • • ■ (ci ) ™
VII 
Well-formed formulas having a prenex normal form with a prefix of the 
form (aj)(a2) . . . (am)(3 b i)(3 b 2)(c1)(c2) . . . (c!).« 3
VIII 
Well-formed formulas having a prenex normal form with a prefix of the
form (a2) (a2) . . . ( a j  (3 b J  (3b2) . . . (3bn) ( c j ( c 2) . . . (c,) 
and 
a 
matrix in which every elementary part that contains any of the variables 
b x, b 3> . . 
b n contains either all of the variables bx, ba, . . 
b n or 
at least one of the variables cx, c 2, . . 
ct 434
corresponding special cases ol the decision problem for validity, and for the sake of 
uniformity in summarizing the results we have done this systematically. The decision 
problem in the sense of footnote 421 is dealt with explicitly only by Herbrand.
481This case is solved by Herbrand, loc.cit. An equivalent condition on the m atrix is 
that it shall have the form A, 3  , A, D  . .  . . A n^  3  A„, where » ^  1 and each A, 
(* =  1, 2, . , , , «) is either an elementary part or the negation of an elementary part, 
or shall be equivalent by laws of the propositional calculus to a m atrix of this form. 
Still another equivalent condition is th at the value of the m atrix shall be f for at most 
one assignment of truth-values to the elementary parts,
432Ackermann, Skolem, and Herbrand, loc.cit. According to Ackermann (1928), a 
wff of class VI which contains no free individual variables and no functional variables 
that are more than binary is valid if it is valid in a domain m -j- {{ml -j- l)¥ — l)/(w f +  
l — 1) individuals, where N is the number of different functional variables appearing 
and
v =  3 x 
-j- I.
Or in case m =  0, / =  1, the wff is valid if valid in a domain of 3 X 2^ individuals. 
If ternary or higher functional variables appear, then a similar result may be found by 
Ackermann's methods.
This provides a strictly theoretical solution of case VI of the decision problem for 
validity, and is hardly available for use in practice. A more practicable decision proce­
dure, however, may be obtained from any one of the three papers, and is indicated in 
exercises at the end of this section.
483G6del, Kalmar, and Schiitte, loc.cit. According to Schiitte, a wff of class VII that 
contains no free individual variables is valid if it is valid in a domain of m -j- 280* 
individuals, where N  is the number of different functional variables appearing, none of 
the functional variables is more than A-ary, and
v  =  
+  1)*+ *.
Again there is a more practicable decision procedure which may be obtained from 
the papers of Gddel or that of KalmAr.
434Skolem, loc.cit.

---


§40]
EXERCISES 46
257
IX 
Well-formed formulas having a prenex normal form with a prefix ter­
minating in (c1)(c2) . . . (a*) and a matrix in which every elementary 
part that contains any of the variables occurring in the prefix contains 
at least one of the variables c1( c2, . . 
c(,434
X 
Well-formed formulas of the form (aj (a2) . . . (an)M z d  (3b)(c)f(b, c),
where n ^  4, and M is quantifier-free and contains no variables other 
than f , al( a2l . . 
an.435
Treatment or partial treatment of all of these cases except VII and X 
will be indicated briefly in exercises which follow at the end of this section, 
as well as of some other cases of lesser importance.
In most of the cases it is possible to put the solution of the decision prob­
lem for validity in the form that, if a wff of the class in question is valid in 
a domain of a specified finite number of individuals, then it is valid (though 
this is seldom the most efficient form of the solution for use in practice, 
i.eM in applying the decision procedure to particular wffs). Case X is of some 
interest as an exception to this. For it includes wffs that are valid in every 
finite domain without being valid in an infinite domain, as may be shown 
by the example 43.5(2).
EXERCISES 46
46.0. In order to establish the simplified decision procedure for case IT 
of the decision problem, prove the rules (1) and (2) which are given above in 
connection with this case.
46.1. (1) Consider a wff A of the singuiary functional calculus of first 
Order (case III) and let the different functional variables appearing in A be 
In f*> * - * 1 I#. We may suppose, by **432, that there are no free individual 
variables in A. According to Quine's solution of case III of the decision prob­
lem, as described above, the reduction process of exercise 39.6 is first to be 
applied to A. By a modification of this reduction process, show that A may 
be reduced to a wff B such that |-A = B , and all the P-constituents of B 
other than propositional variables are of the form (x) , D x zd *D2 zd » 
, . .  DN__X zd Dn where each D, separately is either f,(ar) or ~f4(x) (i — 1, 2, 
. . N). But only 2s  different P-constituents of this form are possible. 
Hence prove **466 by applying to B the decision procedure of case IT.
m The solution of this case is in A ckerm ann’s paper of 1936, cited in footnote 430. 
A m odification of one p a rt of A ckerm ann's decision procedure, reducing its length for 
application in practice, is given by J. T. G^galkine in the Recueil MaMmatique, new 
series vol. 6 (1939), pp. 185-198.
The solution of the decision problem  in case X  should be com pared w ith the reduction 
of the decision problem  which is stated in footnote 447.

---


258 P U R E F U N C T I O N A L C A L C U L U S O F F I R S T O R D E R  [Chap. IV
(2) Show also that h A if and only if in every falsifying system of truth- 
values of the P-constituents of B all the P-constituents other than propo­
sitional variables have the value t.
4 6 .2 . Apply Quine's solution of case III to each of the following wffs:
(1)
( 3 x ) ( y ) . F ( x ) ~ P = 3 .  F ( y )  &  p
(2)
( 3 * ) ( y ) .
111
(3)
(3 x )[F (x ) zd G { x )J == (3 x )(3 y )[F (z ) => G( y ) ]
(4)138
F ( x )  z d x [ F ( y )  zd G { x )] => . p  zd . (x ) F { x ) => G{y)
(5)
(3 * )(3 y ) (2
i)(2
2) . F { y )  :15 G(2
j  ID G(:r) ~ F ( z x) ID .
F ( x )  v G ( x ) zd H { x )  zd H ( z2) . H ( y )  zd .  F (2
,) v G ( z s) zd H ( z 2,
4 6 . 3 . Solve case IV of the decision problem by employing the same 
reduction process (cf. exercise 39.6) as in Quine's solution of case III. 
Illustrate by using this method to determine which of the following wffs are 
theorems:
(1) 
(3k) (Vl) {y2) . ~F{x, z) => F{z, yt) zd . F{yt, z) => F{z, y2)
(2) (32)F(x, 2) zd (z)G(x, z) z d. (2) [G(2, 2) zd F{z, y)] zd ,F(x,y) == (z)G(x,z)
46.4. Solve case IV of the decision problem by reducing it to case III, 
finding for every wff A of class IV a corresponding wff of class III which is 
a theorem if and only if A is a theorem. (Suggestion: Make use of the idea of 
replacing each elementary part of A by an elementary part involving only a 
singulary functional variable.) Check your solution by applying it to the 
two following wffs and verifying that the same results are obtained as when 
the decision procedure for case I is applied to them:
F(x, y) =>* F(y, x) ID ~ . F(x, y) ID* 
x)
F(x, y) ID F(y, x) ID* G(x, y) id ~ . F(x, y) id F(y, x) ID* ~G(x, y)
46.5. As explained above, every solution of a special case of the decision 
problem for validity leads to a solution of a corresponding special case of the 
decision problem for satisfiability. State special cases of the decision problem 
for satisfiability which thus correspond to cases I-IV of the decision problem 
for validity; and state a decision procedure for each of them, directly (i.e., 
without referring to decision procedures for cases I-IV of the decision prob­
lem for validity).
4 6 .6 . Let case VIJ be the subcase of case VI in which there are no free 
individual variables, and m =  0, / — I. I.e., in case VIJ the given wff A
^•This is a modified form of an example used by Quine.

---


m
EXERCISES 46
259
has as prenex normal form (3b)(c)M, where M is the matrix and contains 
no individual variables except b and c.
Suppose that no propositional variables appear and the only functional 
variable appearing is a binary functional variable f. Taking the positive 
integers as the domain of individuals, consider the following attempt to 
find a value of the functional variable f for which the value of A is f (false­
hood). For the value 1 of b we must find a corresponding value of c for which 
M has the value f, and we may suppose without loss of generality that this 
corresponding value of c is 2. The (distinct) elementary parts of M are some 
or all of f(b, c), f(c, b), f(b, b), f(c, c); by assigning appropriate truth- 
values to these we can, in 0 or more ways, give to M the value f. Thus, if 
0 is the propositional function which is to be the value of f, we determine the 
possibilities as to what 0(1, 2), 0(2, 1), 0(1, 1),0(2, 2) may be. Then we 
must consider also the value 2 of b and find corresponding to it a value of c 
for which M has the value f. Without loss of generality we may suppose that 
this new value of c is 3. Again we consider the truth-values to be assigned to 
f(b, c), f(c, b), f(b, b), f(c, c) so as to give to M the value f; and thus we 
determine the possibilities as to what 0(2, 3), 0(3, 2), 0(2, 2), 0(3, 3) may 
be. This gives us two separate determinations of what 0(2, 2) is to be, and 
it is seen that there are the following alternatives, (i) It may happen that 
the two determinations of the value 0(2, 2) of 0  cannot be reconciled with 
each other by using any of the possible assignments of truth-values to 
f(b, c), f(c, b), f(b, b), f (c, c) that give to M the value f (either by using the 
same assignment of truth-values to f(b, c), f(c, b), f(b, b), f(c, c) both 
times or by using two different assignments); then A is valid, (ii) It may hap­
pen that the two determinations of the value 0(2, 2) of 0  can be reconciled 
with each other; then we may go on to find corresponding to the value 3 of 
b a value 4 of c for which M has the value f, and corresponding to the value 
4 of b a value 5 of c for which M has the value f, and so forth; because no 
further hindrance can be encountered, it follows that A is not valid. Thus 
the issue depends on whether or not it is possible to find a value 0  of f such 
that M has the value falsehood both for the values I, 2 of b, c and for the 
values 2, 3 of b, c.
(1) Supply details of the argument which is outlined in the preceding 
paragraph, and complete it so as to show that A is valid if and only if the 
disjunction
s i ;
m i v s : ; , m i
is a substitution instance of a tautology, or, as we shall say, if and only if 
this disjunction is tautologous.

---


260 PURE FUNCTIONAL CALCULUS OF FIRST ORDER [Ch a p. IV
(2) Extend this result to the more general subase of case Vlj in which 
any number of propositional variables appear and a single functional vari­
able (not necessarily binary). I.e., show in this case also that A is valid if 
and only if the disjunction
c
^*i*t M| v S
b  c M|
is tautologous.
(3) 
Complete the solution of this special case of the decision problem by 
stating explicitly a proof of A if the foregoing disjunction is tautologous.
4 6 .7 . 
By the same method solve the further subcase of case VI* of the 
decision problem in which there appear any number of propositional varia­
bles and just two functional variables. Show in this case that A is a theorem 
if and only if the disjunction
Ml v S ^ M |  v S*! Ml
* 4 *1
is tautologous.
46.8. 
By the same method solve case VlJ of the decision problem. 
Namely, show that A is a theorem if and only if the disjunction
S
b  c
*i*»M| v S
b  c 
*t*a M| v . . . v S
b  
c
M|
is tautologous, where N  is the number of different functional variables 
appearing.
46.9. Apply the decision procedure of 46.6-46.8 to determine which of 
the following wffs are theorems;
(!) 
(3*)(y) ■ F{X, y) == F(x, x) ZD . F{x, y) = F(y, y)
(2)437 
(3z)(y) . F(x, x) => F(y, y) => F(x, y)G(x) => G{y)
(Notice that it is not asked to write out explicitly the proof of a wff which 
is found to be a theorem. Therefore instead of making use of the disjunction 
which, according to 46.6-46.8, is tautologous if and only if the given wff is 
a theorem, it may often be found more convenient just to follow through the 
same procedure by which this disjunction was obtained, i.e., the procedure 
described in the second paragraph of 46.6, or a suitable generalization of 
this procedure.)
46.10. As a corollary of 46.8 establish the resplt of Bernays and Schon- 
finkel that, in case VIJ, A is valid if it is valid in a domain of 2N/ individuals, 
where N ' is the number of different functional variables appearing or the 
number 2, whichever is greater.
4,7This is essentially the same as one of Skolem's examples.

---


m
EXERCISES 46
261
46.I I . 
The method used in 46.6-46.8 to solve case VIJ of the decision 
problem can as a matter of fact be extended to solve case VI in general.438
(1) Use this method to solve the case V I i n  which the given wff A has 
a prenex normal form (3b)(Ci)(c2)Mf where M is the matrix and contains 
no individual variables except b, cx, c2. Show in this case that A is a theorem 
if and only if the disjunction
is tautoiogous, where N  is the number of different functional variables 
appearing and
fi =  2aiV -  1.
(2) Use this method to solve the case VIJ, in which the given wff A has a 
prenex normal form (a)(3b)(c)M, where M is the matrix and contains no 
individual variables except a, b, c. Show in this case that A is a theorem if 
and only if the disjunction
is tautoiogous, where v is the sum of the weights of the different functional 
variables that appear, the weight of an h-ary functional variable f being 
the number of different wffs of the form f(dx, da, .. . , dh) which occur as 
elementary parts in S£M|, with the exception of the one wff f(a, a ,. . 
a) 
(which is not to be counted). (Taking the natural numbers as the domain of 
individuals, attempt to give to A the value f; for this it is sufficient to find 
one value of a for which the value of (3b)(c)M is f, and it may be supposed 4
4llT he close relationship should be noticed between this method and the method 
which was later used by G6del in his proof of completeness of the functional calculus 
of first order. Indeed the disjunctions which are used in 46.6-46.8 and in 46.11(1) are 
the sam e as the disjunctions C* of §44, each for a certain particular value of k.
In working with p a rt (1) of exercise 46.11, it is recommended th at the reader replace 
the notations,
Sb cic*M!
S ^ M ! ,
*4*4X5
a n d  so on,
by the sim pler notations M x xx ^ e %l M x ^ x ^  and so on. Similarly, in p art (2) the no­
tations,
S’ m , 1*!- 
S ^ M I .  
and so on,
may be replaced by Maase*. M x x lx il and so on respectively. This simplified notation 
for substitution, essentially th a t of the H ilbert school, m ay conveniently be used in a 
context in which all substitutions are for the sam e list of variables, and especially when 
It is always a variable (or other single symbol) th a t is substituted for each variable. It 
will be useful also in connection w ith the exercises im m ediately following, and a t many 
other places. However, in the te x t we shall retain the more explicit notation for substi­
tution.

---


262 PURE FUNCTIONAL CALCULUS OF FIRST ORDER [Chap. IV
without loss of generality that this value of a is 0; then proceed as in 46.6, 
or as in 46.8.)
46 .12. Apply the decision procedures of 46.11 to determine which of the 
following wffs are theorems:
(!) 
(3*)(y)(*) ■ F (V’ z) => lG(y) => H (x)] => F ix> *) => ■
F(z, x) 
G(x) 
H(z) 
. F(x, y) 
F{zt z)
(2) 
(*) (By) (z) .  F (y , x) i d  [F (x , z ) => F (x , y)} .
F(x, y) i d  . ~F(x, z) i d  F(y, x)F(z, y)
(3) 
(3x)(y)(z) .  F(y) i d  G(y) =  F(x) = > . F(y) i d  
(y) =  G(x) i d  .
F(y) 3  G(i/) 3  H(i/) =  H(x) => F(z)G(z)H(z)
46.13. 
As remarked by Skolem in 1928, the same method may also be 
extended to cases in which there is more than one existential quantifier.
Take as an example the case of the prefix (3b1)(3b2)(c). In connection 
with the prefix (3b) (c), we used the following successive pairs of values of 
the variables b, c: <1, 2), <(2, 3), <(3, 4), <(4, 5), and so on indefinitely 
Similarly, in connection with the prefix (3b1)(3b2)(c), we may parallel the 
method of 46.6—46.8 as closely as possible, using the following successive 
triples of positive integers as values of the variables b1( b2, c: <1, 1, 2); 
<1, 2, 3>, <2, 1, 4>, <2, 2, 5>; <1, 3, 6>, <3, 1, 7), <2, 3, 8>, < 3,2,9>, < 3,3,10>; 
<1, 4, 11>, <4, 1, 12>, <2, 4, 13>, <4, 2, 14>, <3, 4, 15>, <4, 3, 16>, <4, 4, 17>;
<1, 5, 18), <5, 1, 19>, <2, 5, 20), <5, 2, 21>, <3, 5, 22>, <5, 3, 23), <4, 5, 24),
<5, 4, 25), <5, 5, 26); <1, 6, 27), <6, 1, 2 8 ) , . . . .  The enumeration of the or­
dered pairs of positive integers which is here employed has been modified,
as compared to that used in §44. But this modification is non-essential from 
the point of view of §44, and we may therefore take the wffs Gk of §44 as 
modified correspondingly, i.e., by using the modified enumeration of the 
ordered pairs of positive integers. If in a special case we can find a particular 
value K  of k about which we can prove that either c *  is tautologous or none 
of the wffs C& is tautologous, then a solution of this special case of the de­
cision problem follows by direct application of the methods of §44.439
(1) 
Apply this method to solve case V" of the decision problem, in which 
the given wff A  is in Skolem normal form and at the same time satisfies the 
conditions of case V'. Show in this case that K  =  (l +  l)n, where n is the 
number of existential quantifiers in the prefix, and l the number of universal 
quantifiers. (Make use of the fact that M has the value f for at most one 
system of truth-values of its elementary parts.)
489For the assistance of the reader we add the following table, the significance of

---


§46]
EXERCISES 46
263
(2) 
Apply this method to solve the subcase IX' of case IX  in which there 
are no free individual variables and the prefix is (3b1)(3b2) . . . (3bn)(Cj) 
(c2) . .  . (c;), showing in this case that the given wff A  is a theorem if and 
only if
p b 1b]...btt M|
is tautologous.
w h ic h  w ill b e  c le a r b y  a n a lo g y  w ith  t h e  e x p la n a tio n  g iv e n  in  4 6 .6 :
b l b ,
c
*(blf bj) f(bg, b 2)
b 2) f(b2, bj)
K b!, c)
Kc, b j )
f(b2, c)
« c , b 2)
f(c, c)
1
1
2
0 ( 1 ,1 )
0 ( 1 ,1 )
0 ( 1 ,1 )
0 ( 1 ,2 )
0 ( 2 ,1 )
0 ( 1 ,2 )
0 ( 2 ,1 )
0 ( 2 ,2 )
1 2
3 0(1,1)
0 ( 2 ,2 )
0 ( 1 ,2 )
0 ( 2 ,1 )
0 ( 1 ,3 )
0 ( 3 ,1 )
0 ( 2 ,3 )
0 ( 3 ,2 )
0 ( 3 ,3 )
2
1
4
0 ( 2 ,2 )
0 ( 1 ,1 )
0 ( 2 ,1 )
0 ( 1 ,2 )
0 ( 2 ,4 )
® (4 ,2 )
0 ( 1 ,4 )
0 ( 4 ,1 )
0 ( 4 ,4 )
2
2
5
0 ( 2 ,2 )
0 ( 2 ,2 )
0 ( 2 ,2 )
0 ( 2 ,2 )
0 ( 2 ,5 )
0 ( 5 ,2 )
0 ( 2 ,5 )
0 ( 5 ,2 )
0 ( 5 ,5 )
1 3
6 0(1,1)
0 ( 3 ,3 )
0 ( 1 ,3 )
0 ( 3 ,1 )
0 ( 1 ,6 )
0 ( 6 ,1 )
0 ( 3 ,6 )
0 ( 6 ,3 )
0 ( 6 ,6 )
3
1
7
0 ( 3 ,3 )
0 ( 1 ,1 )
0 ( 3 ,1 )
0 ( 1 ,3 )
0 ( 3 ,7 )
0 ( 7 ,3 )
0 ( 1 ,7 )
0 ( 7 ,1 )
0 ( 7 ,7 )
2
3
8
0 ( 2 ,2 )
0 ( 3 ,3 )
0 ( 2 ,3 )
0 ( 3 ,2 )
0 ( 2 ,8 )
0 ( 8 ,2 )
0 ( 3 ,8 )
0 ( 8 ,3 )
0 ( 8 ,8 )
3
2
0
0 ( 3 ,3 )
0 ( 2 ,2 )
0 ( 3 ,2 )
0 ( 2 ,3 )
0 ( 3 ,0 )
0 ( 9 ,3 )
0 ( 2 ,9 )
0 ( 9 ,2 )
0 ( 9 ,9 )
3
3
10
0 ( 3 ,3 )
0 ( 3 ,3 )
0 ( 3 ,3 )
0 ( 3 ,3 )
0 ( 3 ,1 0 )
0 ( 1 0 ,3 )
0 ( 3 ,1 0 )
0 ( 1 0 ,3 )
0 ( 1 0 ,1 0 )
1 4
11
0 ( 1 ,1 )
0 ( 4 ,4 )
0 ( 1 ,4 )
0 ( 4 ,1 )
0 ( 1 ,1 1 )
0 ( 1 1 ,1 )
0 ( 4 ,1 1 )
0 ( 1 1 ,4 )
0 ( 1 1 ,1 1 )
4
1
12
0 ( 4 ,4 ) 0(1,1)
0 ( 4 ,1 )
0 ( 1 ,4 )
0 ( 4 ,1 2 )
0 ( 1 2 ,4 )
0 ( 1 ,1 2 )
0 ( 1 2 ,1 )
0 ( 1 2 ,1 2 )
2
4
13
0 ( 2 ,2 )
0 ( 4 ,4 )
0 ( 2 ,4 )
0 ( 4 ,2 )
0 ( 2 ,1 3 )
0 ( 1 3 ,2 )
0 ( 4 ,1 3 )
0 ( 1 3 ,4 )
0 ( 1 3 ,1 3 )
4
2
14
0 ( 4 ,4 )
0 ( 2 ,2 )
0 ( 4 ,2 )
0 ( 2 ,4 )
0 ( 4 ,1 4 )
0 ( 1 4 ,4 )
0 ( 2 ,1 4 )
0 ( 1 4 ,2 )
0 ( 1 4 ,1 4 )
3
4
15
0 ( 3 ,3 )
0 ( 4 ,4 )
0 ( 3 ,4 )
0 ( 4 ,3 )
0 ( 3 ,1 5 )
0 ( 1 5 ,3 )
0 ( 4 ,1 5 )
0 ( 1 5 ,4 )
0 ( 1 5 ,1 5 )
4
3
16
0 ( 4 ,4 )
0 ( 3 ,3 )
0 ( 4 ,3 )
0 ( 3 ,4 )
0 ( 4 ,1 6 )
0 ( 1 6 ,4 )
0 ( 3 ,1 6 )
0 ( 1 6 ,3 )
0 ( 1 6 ,1 6 )
4
4
17
0 ( 4 ,4 )
0 ( 4 ,4 )
0 ( 4 ,4 )
0 ( 4 ,4 )
0 ( 4 ,1 7 )
0 ( 1 7 ,4 )
® (4 ,1 7 )
0 ( 1 7 ,4 )
0 ( 1 7 ,1 7 )
1 5
18
0 ( 1 ,1 )
0 ( 5 ,5 )
0 ( 1 ,5 )
0 ( 5 ,1 )
0 ( 1 ,1 8 )
0 ( 1 8 ,1 )
0 ( 5 ,1 8 )
0 ( 1 8 ,5 )
0 ( 1 8 ,1 8 )
5
1
10
0 ( 5 ,5 )
0 ( 1 ,1 )
0 ( 5 ,1 )
0 ( 1 ,5 )
0 ( 5 ,1 9 )
0 ( 1 9 ,5 )
0 ( 1 .1 9 )
® (1 9 ,1 )
0 ( 1 9 ,1 9 )
2
5
2 0
0 ( 2 ,2 )
0 ( 5 ,5 )
0 ( 2 ,5 )
0 ( 5 ,2 )
0 ( 2 ,2 0 )
0 ( 2 0 ,2 )
0 ( 5 ,2 0 )
0 ( 2 0 ,5 )
0 ( 2 0 ,2 0 )
5
2
21
0 ( 5 ,5 )
0 ( 2 ,2 )
0 ( 5 ,2 )
0 ( 2 ,5 )
0 ( 5 ,2 1 )
0 ( 2 1 ,5 )
0 ( 2 ,2 1 )
0 ( 2 1 ,2 )
0 ( 2 1 ,2 1 )
3
5
22
0 ( 3 ,3 )
0 ( 5 ,5 )
0 ( 3 ,5 )
0 ( 5 ,3 )
0 ( 3 ,2 2 )
0 ( 2 2 ,3 )
0 ( 5 ,2 2 )
0 ( 2 2 ,5 )
0 ( 2 2 ,2 2 )
5
3
23
0 ( 5 ,5 )
0 ( 3 ,3 )
0 ( 5 ,3 )
0 ( 3 ,5 )
0 ( 5 ,2 3 )
0 ( 2 3 ,5 )
0 ( 3 ,2 3 )
0 ( 2 3 ,3 )
0 ( 2 3 ,2 3 )
4
5
2 4
0 ( 4 ,4 )
0 ( 5 ,5 )
0 ( 4 ,5 )
0 ( 5 ,4 )
0 ( 4 ,2 4 )
0 ( 2 4 ,4 )
0 ( 5 ,2 4 )
0 ( 2 4 ,5 )
0 ( 2 4 ,2 4 )
5 4
25
0 ( 5 ,5 )
0 ( 4 ,4 )
0 ( 5 ,4 )
0 ( 4 ,5 )
0 ( 5 ,2 5 )
0 ( 2 5 ,5 )
0 ( 4 ,2 5 )
0 ( 2 5 ,4 )
0 ( 2 5 ,2 5 )
5
5
26
0 ( 5 ,5 )
0 ( 5 ,5 )
0 ( 5 ,5 )
0 ( 5 ,5 )
0 ( 5 ,2 6 )
0 1 2 6 ,5 )
0 ( 5 ,2 6 )
0 ( 2 6 ,5 )
0 ( 2 6 ,2 6 )
1 6
27
0 ( 1 ,1 )
0 ( 6 ,6 )
0 ( 1 ,6 )
0 ( 6 ,1 )
0 ( 1 ,2 7 )
0 ( 2 7 ,1 )
0 ( 6 ,2 7 )
0 ( 2 7 ,6 )
0 ( 2 7 ,2 7 )
6
1 28
0 ( 6 ,6 )
0 ( i , i )
0 ( 6 ,1 )
0 ( 1 ,6 )
0 ( 6 ,2 8 )
0 ( 2 8 ,6 )
0 ( 1 ,2 8 )
0 ( 2 8 ,1 )
0 ( 2 8 ,2 8 )
2
6
20
0 ( 2 ,2 )
0 ( 6 ,6 )
0 ( 2 ,6 )
0 ( 6 ,2 )
0 ( 2 ,2 9 )
0 ( 2 9 ,2 )
0 ( 6 ,2 9 )
0 ( 2 9 ,6 )
0 ( 2 9 ,2 9 )
•
T h is  ta b le  h a s  b e e n  c o n s tr u c te d  fo r th e  c a s e  t h a t  o n ly  a  s in g le  b in a r y  f u n c tio n a l 
v a r ia b le  f  a p p e a r s  (a n d  0  is  th e  p r o p o s itio n a l f u n c tio n  w h ic h  is  to  b e  t h e  v a lu e  o f f ). 
T h e  r e a d e r  m a y  f in d  i t  h e lp fu l to  c o n s tr u c t s im ila r  ta b le s  f o r o n e  o r tw o  o th e r  c a se s, 
s a y  t h e  c a s e  o f tw o  b in a r y  f u n c tio n a l v a r ia b le s  a n d  t h e  c a s e  o f o n e  t e r n a r y  f u n c tio n a l 
v a r ia b le .
F o r  p a r t  (3) o f th is  e x e rc is e  th e  f ir s t tw o  c o lu m n s  o f t h e  a b o v e  ta b le , h e a d e d  f  (b t b x) 
a n d  f  ( b , b 2), a r e  to  b e  d e le te d . A n d  f o r p a r t  (2 ), th e  f ir s t fo u r  c o lu m n s  o f t h e  ta b le  a r e

---


264 PURE FUNCTIONAL CALCULUS OF FIRST ORDER [Ch a p. IV
(3) Apply this method to solve the subcase VIIlJ1 of case VIII, in which 
there are no free individual variables and the prefix is (3b1)(3b2)(c). 
(i) On the hypothesis that there is only a single binary functional variable 
appearing, supply a quantifier-free disjunction, as short as possible and not 
necessarily one of the wffs Cfc, such that the given wff A is a theorem if and 
only if this disjunction is tautologous. Do the same thing also on the hypoth­
esis: (ii) that there is one binary functional variable appearing and any 
number of singulary functional variables; (iii) that there are just two binary 
functional variables f and g appearing and that the only elementary parts 
which occur are f(bv b2), g(b2, b2), f(b2, c), g(b2, c), f(c, c), g(c, c). Then 
(iv) show how to solve case VIIIJ*1 generally, not necessarily seeking the 
shortest decision procedure or the smallest number K t but establishing the 
success of the method by finding an upper bound of K .m
(4) Apply this method to solve the subcase VIII0 of case VIII, in which 
there are no free individual variables and m ~  0. (Again find an upper bound 
of K .)*40
to be deleted. For part (4) the reader should construct a new table, similar to that for 
part (3) but involving a greater number of individual variables (the case n — 3, / =  2 
m ay be taken as illustrative).
In any of these tables, let two rows be called related if there is a t least one entry, 
consisting of 0  (or W, etc.) with particular numbers as arguments, th at appears in both 
rows. For example, in the table used for part (1), the first and fifth rows are related, and 
the fifth and ninth rows are related, but the first and ninth rows are not related. In the 
table used for part (3), the first, second, and third rows are m utually related; also the 
first and fourth rows are related, but not the second and fourth rows or the first and 
fifth rows.
In the tables for parts (3) and (4), it will be seen th at each row is related to the rows 
obtained by a permutation of the values assigned to bt, ba, . . . ,  bw, and th at otherwise 
each row is related to at most one earlier row of the table. Use m ay be made of this in proving 
the existence of the number K, or in finding an upper bound of K.
^ F o r  the solution of case VIIIJ*1, one approach is the following. (We state the 
m atter for this particular subcase, but it will be seen th at the same idea is applicable 
to case V III0, and indeed to case V III generally.)
In the table constructed as described in the preceding footnote, let a row be called a 
single-row if the values assigned to bt and ba are the same (e.g., the first row in the table, 
the fourth row, and the ninth row are single-rows). And excepting the single-rows, let 
each row of the table be associated with the row obtained from it by interchanging the 
values assigned to ba and ba, and let the resulting pair of associated rows be called a 
row-pair (e.g., the second and third rows in the table are a row-pair, likewise the fifth 
and sixth rows, and so on). For any single-row, taken in isolation, there is a finite class 
Cx of possible assignments of truth-values th at falsify the m atrix M  (i.e., give to M  
the value f) and a t the same tim e satisfy the condition th at the same truth-value must 
be assigned to two elementary parts which are so related th at they become identical 
when bx and bt are replaced by the same variable b. Similarly, for any row-pair there 
is a finite class Ca of pairs of possible assignments of truth-values (one assignment for 
each row) th at falsify M  and a t the same time satisfy the condition th at the same

---


§46]
EXERCISES 46
266
46.14. 
Apply the decision procedures of 46.13 to determine which of the 
following wffs are theorems:
(1) 
(3as) (3y) (z) ,F (x ,x )= > . F(y, y) => . F(x, z) => F (z, y)
(2) 
(3*)(3y)(z) . F(x, z) =  F(z, y) r> . F(z, y) =  F (z,z)= > .
F(x, y) =  F(y, x) => ,F (x ,y ) =  F(x, z)
(3) 
3 (*) (3y) (z) . F(x, z) => . F(y, z) => ,F (x ,y ) =  F(z, z) => .
F{y, x) v F(z, z) => . F(z, x) v F(z, y)
(4) 
(3*) (3y)(z) . F(x, y)F(y, x) =£ F(x, z) => . F(x, z) =  F(z, x) => .
F(x, z) =  F(y, z) => . F{y, x) => F(x, y) =  F{z, z) z d .
F{x, y) =  F(y, x) =  F(z, y) 
(Answer: (4) is a theorem.)
(5) 
(3*)(3y)(z) . F(x, y) =3 F(y, z)F(z, z) . F(x, y)G(x, y) => G(x, z)G(z, z)
tr u th - v a lu e  m u s t b e  a s s ig n e d  to  a n y  tw o  e le m e n ta r y  p a r ts , o n e  in  e a c h  ro w , w h ic h  c a n  
b e  o b ta in e d  o n e  f ro m  t h e  o th e r  b y  in te r c h a n g in g  bx a n d  bt. L e t  
b e  a  n o n - e m p ty  
s u b c la s s  o f Cv  a n d  le t S a b e  a  n o n - e m p ty  s u b c la s s  o f Ca.
I t  is  n e c e s s a r y  to  c o n s id e r fiv e  d if f e r e n t p a t t e r n s  o f c o rre s p o n d e n c e  t h a t  o c c u r 
b e tw e e n  a  s in g le -ro w  o r  ro w - p a ir  in  t h e  ta b le  a n d  a n  e a r lie r  ( re la te d ) s in g le -ro w  o r 
ro w -p a ir. T h e s e  a re , n a m e ly , th e  p a t te r n s  w h ic h  a p p e a r : (i) in  th e  c o rre s p o n d e n c e  
b e tw e e n  t h e  f o u r th  ro w  a n d  t h e  f i r s t  ro w  in  th e  ta b le  (o r b e tw e e n  t h e  tw e n ty - f if th  ro w  
a n d  t h e  f o u r th  ro w , o r  b e tw e e n  t h e  h u n d r e d th  ro w  a n d  t h e  n i n th  ro w , a n d  so  o n ) ; 
(ii) in  th e  c o rre s p o n d e n c e  b e tw e e n  t h e  r o w - p a ir  c o n s is tin g  o f th e  s e c o n d  a n d  t h i r d  ro w s , 
o n  th e  o n e  h a n d , a n d  t h e  f ir s t ro w , o n  t h e  o th e r  h a n d ; (iii) b e tw e e n  t h e  r o w - p a ir  c o n ­
s is tin g  o f th e  f if th  a n d  s ix th  ro w s , o n  th e  o n e  h a n d , a n d  t h a t  c o n s is tin g  o f th e  s e c o n d  
a n d  th ir d  ro w s, o n  t h e  o th e r  h a n d ; (iv ) b e tw e e n  th e  r o w - p a ir  c o n s is tin g  o f t h e  s e v e n th  
a n d  e ig th  ro w s, o n  th e  o n e  h a n d , a n d  t h a t  c o n s is tin g  o f t h e  s e c o n d  a n d  th i r d  ro w s , 
o n  th e  o th e r  h a n d ; (v ) b e tw e e n  t h e  n in th  ro w  a n d  t h e  r o w - p a ir  c o n s is tin g  o f th e  s e c o n d  
a n d  th i r d  ro w s.
I n  c a s e  (i) w e m u s t a s c e r ta in  t h a t ,  fo r a n  a r b i t r a r y  m e m b e r  o f 
u s e d  a s  th e  a s s ig n ­
m e n t o f tr u th - v a lu e s  in  th e  e a r lie r  s in g le -ro w , th e r e  is  a  c o r r e s p o n d in g  m e m b e r  o f Sx 
w h ic h  m a y  b e  u s e d  s im u lta n e o u s ly  a s  th e  a s s ig n m e n t o f tr u th - v a lu e s  in  t h e  l a t e r  s in g le ­
ro w . I n  c a s e  (ii) w e m u s t a s c e r ta in  t h a t ,  f o r  a n  a r b i t r a r y  m e m b e r  o f Sx u s e d  a s  th e  a s s ig n ­
m e n t o f tr u th - v a lu e s  in  t h e  s in g le -ro w , th e r e  is  a  c o r r e s p o n d in g  m e m b e r  o f S% w h ic h  m a y  
b e  u s e d  s im u lta n e o u s ly  a s  t h e  a s s ig n m e n t o f tr u th - v a lu e s  in  t h e  r o w - p a ir. I n  e a c h  o f 
c a se s (iii), (iv ) w e m u s t a s c e r ta in  t h a t ,  f o r a n  a r b i t r a r y  m e m b e r  o f S% u s e d  a s  th e  a s s ig n ­
m e n t o f tr u th - v a lu e s  in  th e  e a r lie r  ro w -p a ir, th e r e  is  a  c o r r e s p o n d in g  m e m b e r  o f St 
w h ic h  m a y  b e  u s e d  s im u lta n e o u s ly  a s  th e  a s s ig n m e n t o f tr u th - v a lu e s  in  t h e  l a t e r  ro w - 
p a ir . I n  c a s e  (v ) w e m u s t a s c e r ta in  t h a t ,  fo r a n  a r b i t r a r y  m e m b e r  o f S a u s e d  a s  th e  
a s s ig n m e n t o f tr u th - v a lu e s  in  th e  ro w -p a ir, th e r e  is  a  c o r r e s p o n d in g  m e m b e r  o f St 
w h ic h  m a y  b e  u s e d  s im u lta n e o u s ly  a s  t h e  a s s ig n m e n t o f tr u th - v a lu e s  in  t h e  s in g le -ro w .
S in c e  Cx a n d  Ca a r e  fin ite , th e  n u m b e r  o f d if f e r e n t p a ir s  Slt S a o f n o n - e m p ty  s u b ­
c la s s e s  o f Clt Ca is  fin ite . I n  th e  c a s e  o f a n y  p a r ti c u la r  w ff A  t h e  c o m p le te  lis t o f p a ir s  
5 lf S a m a y  b e  w r i tte n  d o w n , a n d  fo r e a c h  s u c h  p a i r  5 X, S a i t  m a y  b e  d e te r m in e d  w h e th e r  
th e  c o n d itio n s  j u s t  s ta te d  a r e  s a tis f ie d . I f  o n e  p a i r  Sx, S% is  fo u n d  f o r  w h ic h  th e s e  c o n ­
d itio n s  a r e  s a tis f ie d , th e  w ff A  is  n o n - v a lid ; in  t h e  c o n t r a r y  c a se , A  is  v a lid .

---


266 PURE FUNCTIONAL CALCULUS OF FIRST ORDER [Chap. IV
(6) 
(3*) (3y)(z) . F(z, y) zd [F(z, z) == G(y, *)] zd .
F(z, y) s  [F(z, z) zd G{z, z)] => . G(x, y) =s G(z, z)
(7) 
(3z)(3y)(z) . F{x, z) z> . F(z, z) zd G{z, z) =  F{x,y)ZD .
G(z, z) zd F{z, z) =  G[x, y) zd . G(x, y) zd F(y, x) =  G{y, z) zd .
F(z, y) =  F(y,x)
46-I5- Extend the method of 46.13 (1) (compare also 46.11 (2)) to solve 
case V' of the decision problem. First work out the method in application 
to the following particular examples:
(1) (z) (3yx) (3ya) (z) . F(x, z ) zd . F { y v  z ) z d . F  (ya, z) =3 . F(y„ x) zd F { z , ya)
(2 ) 
(*i)W (3y)(z) - f {x i >y )  
‘ F l z . x J  Z D m F ( z , y ) Z D F ( x 2, y ) v F ( x t , z )
(3) 
(3*)(y){3z) . F(x, y )  zd . F(z, x) zd F(y, y)
(4) 
(3*) (y) (3z) . F(z, y,z) zd F (y. z, z)
(5) 
(3*) (y) (3zx) (3za) . F (x, y, zx, z2, zv) zd F (zx, x , y , zx. z2)
(6) 
(3^) (a;,) (3za) (z4) . F(zx, z2, za) => F (z2, z3, z4)
(7) 
f o )  (3za) (za) (3z4) . F(zj, x 2, x 3) => F(z4, z4, zx)
Then (8) state the method in general and show that it provides a solution of 
case V' of the decision problem for validity. Finally (9) show how to obtain 
a proof of a wff which has been found by this method to be valid.
4 6.1 6 . (1) By the same method solve also the following case V of the 
decision problem:
V 
Well-formed formulas with a prenex normal form in which the matrix 
satisfies the condition of not having the value falsehood for two different 
assignments of truth-values to its elementary parts unless the two assign* 
ments differ in the truth-value for at least one elementary part that con* 
tains none of the variables occurring in the prefix.
And illustrate by applying the solution to the following particular examples 
(after dropping universal quantifiers from the beginning of the prefix if 
necessary):
(2) 
(3yi)(3y2)(z). F[x, yx) zd F( z , x ) zd F ( x, x ) zd F( x, x)F(yv y2)
(3) 
(z)(3yj)(3y2)(z) . F(z, z) zd [F(yx, z) zd F(y2, a?)] zd F ( x , x ) zd .
F{x, x) . F(y1, y2) zd F (z. z)
(4) 
(z1)(*,)(3y1)(3y,)(z) .
F { x v  x %, Vi) =5 F iV z , Vi, *) => [F(zXj x i> x t ) ZD F { x 1, z2, z8)] ZD .
F(z2, Vi, Vi) => F(yXl z, z) zd [F(zx, z 2, z2) zd F { x v  x v  z2)] zd .
F{yv Vi> a) =3 F(z2, z2, yx) . F(z„ xv z2) =  F (zlf z2, z2)

---


EXERCISES 46
267
46 ,17, (1) In the same way, extend the method of 46.13(2) to solve case 
IX of the decision problem. And illustrate by applying the solution to the 
following particular examples:
(2) 
(as,) (* ,)(3 y1)(3 y ,) (z2) (z2) . Fix.,, zx) id .
F(yu z2) id  F(y„ z,)F{y2, z,) v /•'(*„, z2)F(y2, z2)
(3) 
(3*!) (3a;2) { y ) . [ F f o ,  y) =  F {* 2, y) =  F(zt, z2)] v [F fo , y) =  F{z2, y )]
(4) 
( 3 ^ )  (x2) (3a:3) (x4) . [ F f o ,  xt ) == F(xit x3) =  F(xs, x4) =  F(xt , arj] .
F(xa, x4) =  F[x4, a;,) =  F(x3, x4) =  F(x4, x2)
(6) 
(Sajj) (*2) (3*3) (a:4) . F[xx, x4) =  F(a;2, x4) 3  .
F(ar„ x4) =  F(x4, x3) =  F(xa, x4) =  F{x4, xt)
46.1$. (1) In the same way, extend the method of 46.13(3), (4) to solve 
case VIII of the decision problem.440 Illustrate by applying the decision 
procedure to the following particular examples:
(2) 
(* )(3 y1)(3y*)(z) . F{x, z) =  F[z,x) => .
F[x, z) =  F ( y 2, z) . F(y„ z) id  F ( y „  y 2)
(3) 
(*!)(**) (3 y i)(3 y2)(z) . F f* !, y2, x „  z) id .
F(x i. Vv *v V2) s  F(y„ x2, yv y2) id .
F(xv yv x„ y2) id [ F f o , y2, yv y2) =3 F{a;„ z, ylt z)] .
Fix,, z, y„ z) => . F  (*1( y„ x„ y2) =  F{x„ y2, y„ y2)
(4) 
{x,) (a:2) (3 ^ ) (3 y 2) (z) . F f o ,  a:2) id . F (y „  y 2) 3  F(a:2, z) v F ( y 2, z) ID . 
F (yi- y 2) => [F (® ,. z) =  F (y j, z)l =3 F {z, z) =3 .
Ffax. y 2) ■ F {y i, z) =  F ( y 2, z)
(6) 
{ * )(3 y i)(3 y2){3 y ,)(z ) .
F{yx, yt, Vi) = ) [F(x, x, z) =3 F ( y 2, y3, y2) v F ( y 3, ylf y 2)] => .
f  (y». yi- y*) => F (yx. y2> y3)-F(y2. y3. yi) =■ F(ya, ylf z) =>.
F{ya, ySl yi) => F{y„ y2, y3)F (y 3, y^ y 2) =  F (y lf z, y 2) id  .
^ ( y 3. yi- y 3) => ~F(yt, ya, y,) ID F{ylt y 2, y 3) =  F (z, y2, y ,) id .
F (yx. y 3. y3) ^ ( y 2. y3. y i) ^ ( y 3, yi, y 2) =  F ( z ,2. 2)
46.19. Apply the remark of footnote 425 in order to reduce the solution 
of each of the following additional special cases of the decision problem to 
that of cases I, V-IX:
XI1 
Well-formed formulas in which every truth-functional constituent is in
prenex normal form with an elementary part or the negation of an 
elementary part as its matrix.

---


268 
P U R E  F U N C T I O N A L  C A L C U L U S  O F  F I R S T  O R D E R  
[Ch a p. IV
XI 
Well-formed formulas in which every truth-functional constituent is in 
prenex normal form with a matrix that has at most one elementary part 
containing any of the variables that occur in its prefix.
XII 
Well-formed formulas in which the prenex normal forms of the truth•
functional constituents have prefixes of the following forms only: 
(ai)» (ai)(a2)> (ai)(3^i)> 
(ai)(3bj)(3b2), (aj)(a2)(3bj)
(3b2).
XIII 
Well-formed formulas in which the prenex normal form of each truth- 
functional constituent P{ has a prefix of one of the forms (bl) (b8). . . (bn) 
or ( a ^ f o ) . . .  (am<)(3bx)(3b2) .. . (3bn) and a matrix in whicti) 
every elementary part other than a propositional variable contains aU of 
the variables b2, b2, .. 
bn—where the number n is the same for aU the 
constituents Pif and the numbers m{ are each of them less than or equal 
to n.
46,20, Consider the following additional case of the decision problem:
XIV 
Well-formed formulas having a prenex normal form with a prefix of the 
form (a,)(a,) .. . ( a j (3b1)(3bl) . . . (3bn(Cx) (c,).. .(c,) and a ma- 
trix in which the complete list of functional variables occurring is
gx, g 2l . . ., g^, such that no elementary part with one 
of the functional variables f( contains any of the variables cv c2, . . 
cl( 
and each elementary pari with one of the functional variables g i contains 
either none of the variables b1# b2l . . ., bn or at least one of the variables 
c 2j . .  •, C(.
(1) By the method described in 46.13, solve the subcase XIV0 in which there 
are no free individual variables and m =  0, showing in this case that K  — I.
(2) Extend this method to solve case XIV in general. (3) By taking l =  0, 
find a solution of case I as a corollary of the solution of case XIV. (4) Illu­
strate the solution of case XIV by applying it to the following example:
(*2) (3yA) (3y2) C-Sf) ■ F(*„ *„) =>. G ( x h  x t ) zd .
G ( x v  z )  =  G ( y t , z )  zd [ F { y v  y t ) zd F(xt, ys)] => .
G(*2, z) =  G ( y v  z )  zd F (Xj, y J F f a ,  
y t ).
46 .2 1. Consider the general method for the solution of the decision prob­
lem which is outlined in footnotes 439 and 440, and study the question of 
extending it to cases in which a row in the table (or row-pair, etc.) may be 
related to more than one earlier row (row-pair, etc.). Explain why the 
method cannot be extended to an arbitrary such case; and seek for any 
special cases of this sort to which the extension may be possible. Consider

---


EXERCISES 46
260
§46]
in p articu lar th e case V I lj  of a n y w ff A  h a v in g  a prenex norm al form  in 
w hich th ere are n o free in d iv id u a l v ariab les and th e prefix is (3 b J  (3 b 2) (c).
46, 22 , 
T h e p rob lem  tr a d itio n a lly  trea ted  u n d er the hpad of th e categorical 
syllogism m a y  b e rep resen ted  as fo llo w s in  co n n ection  w ith  an  ap p lied 
fu n ctio n a l calcu lu s of fir st order h a v in g  sin g u la ry  fu n ctio n a l co n sta n ts 
am ong its p rim itiv e sy m b o ls. L et a sen ten ce be sa id  to exp ress a categorical 
proposition if it h as o n e o f th e four form s f(a;) 3 s g(a;), f{x) ^ X~g[x), 
(3a:) . f(a?)g(a?), (3a;) . f(a;) ~ g ( z ) , w here (in each  case) f  and g  are sin g u la ry 
fu n ctio n a l c o n sta n ts.441 I t is required to  fin d  all valid  form s of in feren ce in 
w hich th ere are tw o  p rem isses, and th e p rem isses an d  conclu sion each  of them  
have on e of th e four ca teg o rica l form s. B u t c a ses are to  be ex clu d ed  in w hich 
there is e ssen tia lly  o n ly  o n e prem iss, i.e., in w h ich  there is a sim p ler valid 
inference accord in g to w h ic h  th e con clu sion  in q u estion  w ou ld  fo llo w  from  
one of the tw o p rem isses alone.
F or ex a m p le, am o n g  th e required form s o f inference are th e follow in g 
w hich correspond to  th e trad ition al sy llo g ism s in Darii, Ferio, a n d  Feriso 
resp ectiv ely , and w h ich are to be d istin g u ish ed  as all three d ifferen t: from  
g(x) zdx h(a;) an d  (3a?) «f(a:)g(a:) to  infer (3a:) . f(a:)h (x); from  g(a?) ZDX ~h(ar) 
and (3a;) . f(a:)g(a?) 
to  in fer (3a;) ■ f(a;) ~h (a;); from  g(a:) D a ^h(a:) 
and 
(3a;) • g(se)f(a;) to in fer (3a:) . f (a;) ~ h (x ).
E v id e n tly  su ch  form s of inference can  be teste d  b y w ritin g for each  one 
a corresp on d in g leading principle, ex p ressed  as a w ff of th e pure fu n ctio n a l 
calcu lu s o f first order (com p are exercise lo .9 ). A n d  the form  of in feren ce is 
to be con sid ered  v a lid  if a n d  o n ly  if its lea d in g  prin cip le is v a lid . F or ex a m p le, 
the lea d in g  prin cip le of D a rii is G(a;) z^x H(x) id . (3x)[F(a:)G(a;)] id (3 x) . 
F{x)H{x) ; an d  it m a y  b e v erified  b y  th e d ecisio n  procedure for ca se III, as 
given  a b o v e, th a t th is le a d in g  principle is v a lid , and th a t n eith er of the 
sim pler lea d in g  p rin cip les G(x) zdx H{x) zd (3 z ) . F(x)H{x), (3x)[F(a:)G(z)] 
3  (3a;) . F(x)H(x) is v a lid .
^T raditionally the four forms are called A, E, I, O respectively and are rendered in 
words as: all F's are G's, no F's are G's, some F's are G's, some F ’s are not G's, Notice, 
however, that the version here suggested of the traditional doctrine of categorical 
propositions and the categorical syllogism is not put forward as the correct interpretation 
but rather only as one possible or plausible interpretation.
The fact is th at the traditional doctrine is not sufficiently definite and coherent—and 
different writers are not sufficiently in agreement— to make it clear what is the best or 
most faithful representation of it in a logistic system. For there is, on the one hand, the 
difficulty about "existential im port/' as it is called (some aspects of the traditional 
doctrine would seem to be better represented if A and E were taken as (3a:)f(x) .
(a;) and (3x)f(a:) *f(x) 
respectively, instead of in the way suggested
in the exercise). And there is, on the other hand, the question whether the traditional 
"term s" should not rather be construed as common names bee footnotes 4, 6) or as 
variables instead of class names or functional constants.

---


270 PURE FUNCTIONAL CALCULUS Ob' FIRST ORDER [Ch a p. IV
By the method indicated, solve the problem of finding all such valid forms 
of inference (valid categorical syllogisms).
46.23, Implicit in some of the foregoing exercises (see 46.11(2), 46.13, 
46.15-46.18) is a metatheorem due to Herbrand 448 namely a generalization 
of **441 to the case of a wff A in prenex normal form with an arbitrary 
prefix, the only further difference in the statement of the generalized meta- 
theorem being in the substitution by which the quantifier-free wff B* is 
obtained from M. State this generalization of **441 explicitly: (1) for the 
case that the prefix is (3b)(c)(3d)(e) and the free individual variables of 
A are ax and a2; (2) for the case of an arbitrary prefix and an arbitrary 
number of free individual variables in A.
46.24, By means of the metatheorem of 46.23, prove the completeness 
(in the sense of §44) of the following described formulation, F£p, of the pure 
functional calculus of first order, due to Herbrand:448 The primitive sentence 
connectives are negation and disjunction. The primitive quantifiers are the 
universal and existential quantifiers. The axioms are all quantifier-free, 
tautologous wffs. And the rules of inference, none requiring more than a 
single premiss, are as follows: the rule of alphabetic change of bound variable 
(*402); the rule of generalization (*401); from A to infer (3b)B, where b 
is an individual variable which does not occur in A, and B is obtained front 
A by replacing zero or more free occurrences of the individual variable a in* 
A (not necessarily all free occurrences of a in A) by b; to replace a wf part 
(a)[C v D] by (a)C v D. if a is not free in D; to replace a wf part (3a) (C v D] 
by (3a)C v D, if a is not free in D; to replace a wf part (a) ~C by ~(3a)C; 
to replace a wf part (3a) ~C by ~(a)C; to replace a wf part P v 0 by 0 v P; 
to replace a wf part Pv[QvR’ by [P v 0] v R; to replace a wf part 
[P v 0] v R by P v [0 v R]; to replace a wf part P v P by P.
47. Reductions of the decision problem. A reduction of the decision, 
problem (of the pure functional calculus of first order) consists in a special 
class F  of wffs and an effective procedure by which, when an arbitrary wff 
A is given, a corresponding wff Ar of the class Fean be found such that A 
is a theorem if and only if Ar is a theorem, and by which, further, a proof of 
A can be found if a proof of Ar is known. For example, **420 and *421 con­
stitute a reduction of the decision problem, the class F  being in this case the 
class of wffs in Skolem normal form.
44*Reckerche$ sur la Thiorie de la Demonstration, Warsaw 1930. This is Herbrand's 
dissertation at the University oi Paris. (Added in proof. See in this connection a paper 
of Burton Dreben in the Proceeding of the National Academy of Sciences of the U,S.A,, 
vol. 38 (1952), pp. 1047-1052.)

---


§47]
REDUCTIONS OF THE DECISION PROBLEM
271
A reduction of the decision problem for validity consists in a special class T  
of wffs and an effective procedure by which, when an arbitrary wff A is 
given, a corresponding wff Ar of the class J1 can be found which is valid if 
and only if A is valid. Similarly, a reduction of the decision problem for 
satisfiability consists in a special class of wffs and an effective procedure by 
which, when an arbitrary wff A is given, a corresponding wff of the special 
class can be found which is satisfiable if and only if A is satisfiable.
Clearly, every reduction of the decision problem for satisfiability leads to 
a corresponding reduction of the decision problem for validity, and vice 
versa. (The correspondence between **437 and **438 may be taken as an 
illustration of this.) Thus it is necessary to treat only one of the two kinds of 
reduction. Wherever results in the literature are stated as reductions of the 
decision problem for satisfiability, we shall here reproduce them in the other 
form, i.e., we shall state the corresponding reduction of the decision problem 
for validity.
With the exception of the reduction to Skolem normal form, and reduc­
tions which (like that to prenex normal form) can be regarded as included 
in this or which (like those of 39.5, *465) follow by little more than propo­
sitional calculus, reductions of the decision problem in our present sense, 
i.e., of the decision problem for provability, have rarely received treatment 
in the literature, perhaps only in the work of Herbrand. Since for many pur­
poses the weaker result is sufficient, we shall deal in the remainder of this 
section with reductions of the decision problem for validity; and it will be 
convenient to express such reductions by saying that the class r  is a reduc­
tion class.
In view of the unsolvability of the general decision problem of the pure 
functional calculus of first order (whether for provability or validity), it is 
evident that, if T  is a reduction class, then the special case of the decision prob­
lem for wffs of the class T  is unsolvable. And this may be regarded as being 
a part of the significance of reductions of the decision problem for validity.
As a lemma for later proofs, we first establish the following metatheorem, 
the idea of which is due to Herbrand:443
**470. 
Let A be any wff, let px, p2, . . pM be the complete list of distinct 
propositional variables occurring in A, and let iv f2, . . ., fN be the 
complete list of distinct functional variables occurring in A. Sup­
pose that if is an ht-ary functional variable (i =  1, 2, .. ., N), and 
let h — 1 be the greatest of the*numbers hlt h2, .. ., hN. Choose 48
448I n  t h e  p a p e r  c ite d  in  f o o tn o te  4 3 0 .

---


272 PURE FUNCTION ALCALCULUSOF FIRST ORDER TChap.I ^
distinct individual variables444 x v x 2, . . 
x w
, y1( ya, . . 
yh_v 
of which x1( x2, . . 
x^ +iV do not occur in A, and choose an A-ary 
functional variable f.444 Let Cybef(x^ x,, . . 
x^) {/ =  1, 2, . . M)
let F, be f,(yx, y2-----, yht) (i =  1( 2.........N); let D, be f(xw+^
■ • •' x M~i> Yv y* * ■ •* ya<) (i =  1, 2, . . 
AT); and let B be
Then B is valid if and only if A is valid.
Proof. If h A, then h B by *352. By **440 and **434 it follows that, if A 
is valid, then B is valid.
By *301 and *306, we may suppose that A contains no free individual 
variables. Taking the positive integers as domain of individuals, assume that 
B is valid, and consider any system of values rx, r2, . . 
rM, 0 V 0 2, 
of the free variables px, p2, . . 
p^, flt f2, . . 
fN of A. Let the values'
1, 2,. .
M +  IV be assigned to the free variables xx, x2, . . 
xM+N of B 
respectively, and let a value 0  of the free variable f of B be determined as 
follows: 0(j, j, .. 
/) =  Tj (j =  1, 2, . . 
M); 0 { M + i } M + i , . . 
M + it
«i, «a----- - «*,) ^  
#*,) ( * = 1 , 2 , . . . ,  N); 0 (u lt u%, . . 
«*)= t1
in all other cases. The value of B for this system of values of its free variables, 
is evidently the same as the value of A for the system of values xv x2i ■. ** 
• • •» 
of the free variables of A. And since the value of B is t* 
it follows that the value of A is t.
Thus we have shown that, if B is valid in the domain of positive integers, 
then A is valid in the domain of positive integers. Hence by **450, if B 
valid, then A is valid.
It follows that the class of wffs containing only one functional variable,, 
and no propositional variables, is a reduction class. However, we go on at 
once to obtain stronger reductions than this.
According to a result of Lowenheim, the class of wffs containing only bi­
nary functional variables is a reduction class. By a refinement of Lowen- 
heim's method it is possible to obtain the result that the class of wffs con­
taining only a single binary functional variable (no other functional vari­
ables, and no propositional variables) is a reduction class.445 We proceed to 
show how this may be done.
Given an arbitrary wff A, we first reduce it by **470 to a wff B which con­
444To render the reduction process effective, the choice m ust be made explicit in 
some manner, say by taking in each case the first available variable or variables, 
according to the alphabetic order of the variables.
“ ‘First proved by Kalm&r in Compositio Mathematica, vol. 4 (1936), pp. 137-144.

---


§47]
REDUCTIONS OF THE DECISION PROBLEM
273
tains only a single A-ary functional variable f. If h =£ 2, we choose a binary 
functional variable g, and 2h +  1 distinct individual variables q , c2l .. ., ch, 
d1( d2, • • •» dA+1, °f which dv  d2, . . . ,  dA+1 do not occur in B .444 And we let 
G be the conjunction
g(di, d2)g(d2, d8) . . .  g(dA, dA+1)g(dA+1, d1)g(d1, Cj)g(d2, c2) . . .
c h) 
d i) ~ * (C i. d a) ^ ( c 2> d a) * * • 
d J w ) * ( « W C i) .
Then letting C be
®*» ***» 
1>|
^ ( 3 d 1)(3d1)...(3 d A+l)G  
* * \ >
we show that C is valid if and only if B is valid, therefore if and only if A 
is valid.
If h B, then h C by *352. By **440 and **434 it follows that, if B is valid, 
then G is valid.
By *301 and *306 we may consider, instead of B and C, their universal 
closures B' and C'. Taking the natural numbers as domain of individuals, 
assume that C' is valid, and consider an arbitrary value 0  of the single free 
variable f of B'. Then let a value W of the single free variable g of C' be 
detemined as follows.
The (ordered) A-tuples of natural numbers are enumerated in such a way 
that the natural numbers occurring in the &th A-tuple are all less than k. 
(Analogously to the enumeration used in §44, this may be done by arranging 
the A-tuples (vv  v2t. . 
vhy in order of increasing sums vx +  v2 +  . . . +  vh, 
A-tuples having the same sum being arranged among themselves in lexico­
graphic order.) Then W{ut u) =  t except when u =  k(h +  1) +  1 (i.e., 
except when u is congruent to 1 mod h +  1). If there is a natural number k 
such that % =  k(h +  1) +  1, w2 =  k(h +  1) +  2, . . . ,  «*+1 =  (k -(- 1) (A—|— 1), 
then 
!?(«!, u2) =  W{u2i «8) =  . . .  =  W{uhi uh+1) =  W («A+1, Uj) =  t. 
If 
(vv v2, . .., vhy is the (k +  l)th A-tuple and ux =  k(h +  1) +  l (l =  1, 2 , 
• • • , * +  1), then !?(«!, v±) =  W(u2t v2) = = . . . =  W{uhf vh) =  t, and 
W{uh+1, vx) =  0{vlt v2t. . . ,  t/A). And in all remaining cases W{ut v) =  f.
In view of the special properties of the propositional function Wt the 
value of C' for the value W of g is the same as the value of B' for the value 
0  of f. And since the value of G' is t, it follows that the value of B' is t.
Thus we have shown that, if C' is valid in the domain of natural numbers, 
then B' is valid in that domain. It follows that, if C is valid, then B is valid.
This completes the proof, since C contains only the single binary func­
tional variable g, and we have shown altogether that C is valid if and only 
if A is valid.

---


274 PURE FUNCTIONAL CALCULUS OF FIRST ORDER [Ch a p.IY
Notice that in place of (3dx)(3d2) . . . (3dA+x)G in the foregoing proof 
we might equally well have used (d1)(d2) .. .(dA+1)H, where H is
g(dX) d2) 
. g ( d 2, d3) 
.. . . g(dA, dA_x) 
.g (d A+x, dx) =3 .
g(dx, cx) =3 ■ g(d2, 
g(dA, cA) =3 . ~g(dx, dx) => .
~g(cx, d2) 
. ~g(c2, d3) 
.. .. ~g(cA, dA+1) => g(dA+ll cj.
For both of the wffs (3dx)(3d2) , . . (3dA+x)G and (dx)(d2) . .. (dA+x)H 
alike have the value &(vx, v%i . . 
vA) for the system of values W, vv v2, .. 
vh of their free variables g, q , c2, . . 
cA (where V  is the propositional func­
tion which was introduced above). By taking advantage of this observation 
we now go on to establish the following still stronger reduction of the deci­
sion problem for validity;
**471. 
The class of wffs in Skolem normal form which contain only a single 
binary functional variable (no other functional variables, and no, 
propositional variables) is a reduction class.
Proof • By **437 we may suppose that the given wff A is already in Skolem 
normal form.
We consider first the case that A contains only a single h-ary functional 
variable f, making use in this case of the wffs G and H that were introduced 
above. Therefore let A be
(3ax)(3a2) . . . (3am)(bx)(b2) .. . (bn)M,
and let the distinct elementary parts of the matrix M of A be Ex, Ee, . . 
where E, is f(ctX, cl2, . . 
ciA) {i ~  1, 2, . . 
Since the P-constituents 
of M are the same as its elementary parts, we have by *465 that a certain 
equivalence M =  Mx is valid, where Mx has the form of a conjunction
[E}=3 ■ Ei 3  . .  . . EJ_X 3  ~Ej][Ex2 ro . E2=d . .  . . E2_x 
~E 2] . ..
[e ; 3 . e ^ . . . . e^ 1 z>~e;j
each Ej being either E* or ~Et (i — I, 2, . . pt, and j =  1, 2, . .
v) 
Therefore A is valid if and only if Ax is valid, where Ax is
(3a!)(3a2) . . . (3am)(b1)(b2) . . . (bJM,.
Choose distinct individual variables cX) ca, . .
cAl dx, d2, . . 
dA+ll of 
which dx, d2, . . 
dA+x do not occur in A^ 444 let M2 be obtained from Mt 
by replacing each part Ej by
and let A2 be

---


§47]
REDUCTIONS OF THE DECISION PROBLEM
2 7 5
Then A* is
( 3 ^ ( 3 8 .) ... ( S a J ^ K b , ) . . .  (b„)M,
and by *352, **440, and **434 it follows that if Aj is valid, then A2 is valid. 
Let M3 be obtained from Mx by replacing each part E* by
^ (3 d 1)(3d2)...(3dA+1)G 1^/l
or
ca^ 
i?i|
^ ( d 1K d 1)...(d w .1)H  
I
according as E* is E, or ~E8-, and let A3 be
(3a,) (3a,) • • • (3am)(bi)(b2) .. . (b„)M3.
Let A4 be
(3d!) (3da) . .. (3dft+1)G =3ClCs...cA(d1)(d2) .. . (dw )H => A,.
By the same argument that was used above (employing again the domain 
of natural numbers and the same binary propositional function W) we may 
show that, if A4 is valid, then Ax is valid.
Letting K be the conjunction of all the wffs
S W
- i ( 3di)(3d*> • • • (3d*+i)G =  W W  ■ • • (d*a )Hl.
we have by P that h M2 d . K d  M3. Hence by *306 and P,
h Ma =>. (3d1)(3d1) . . .  (B dfc+O G ^,^ (d,)(d,).. . (dw )H => M3.
Hence by *301, *333, *335, *365, *382, and P, h A2 id A4. By modus ponens, 
and since we know that the valid wffs are the same as the theorems (by 
**440 and **434), it follows that, if A2 is valid, then A4 is valid. Consequent­
ly, if At is valid, then A4 is valid.
Then the prenex normal form of A4 is in Skolem normal form, contains 
only the single binary functional variable g, and is valid if and only if A 
is valid.
This completes the proof of the case that A contains only one functional 
variable. Turning now to the general case, we suppose that A is in Skolem 
normal form
(3a,) ( 3 a , ) . . .  (3am) (b,) (b,). . .  (bn)M,
M being the matrix, and contains M  different propositional variables 
Pi> Ps> - • 
Pi* and N  different functional variables flt f2, . . ., f^. Let ft be 
an h^ary functional variable (i =  1, 2, . .  .,iV), and let h be the greatest 
of the numbers 
h2, . . . ,  hN.

---


276 PURE FUNCTION ALCALCULUSOF FIRST ORDER [Chap. IV.
In place of the two wffs G and H which were used in the first part of the 
proof, we now use 2(Af +  N) wffs Gx, G2, . .
GM+iV, H1( Ha, . . Hw+w. 
Namely, where g is a binary functional variable and c1( ca, . . cA, dv da,
. . 
&h+M+N are distinct individual variables of which dlf d2l . . 
dA+Af+JV 
do not occur in A,444 we take Ga to be the conjunction
g(di, d2)g(d2l d3) . . . g(dA+Af+iv_i> dA+Af+w)g(dA+M+iVl dx) 
g(di, cx)g(d2, c2) . . .  g(d„, ch) ~g(dx, dx) ~g(cx, d2)
~6 (C2' da) * • ' 
dA+1)g(dA+a, Cl)
(a =  1, 2, . . 
M  +  N), and we take Ha to be
g(dx, d2) id . g(d2, d3) zd •. . . g(dA+Af+JV_x, dft+Af+w) id m&{dh+M+St di) ^  ■ 
g(dx, cx) id . g(d2, c2) id . .  . . g(dA, cA) =>. ~g(dx, dx) => . 
d2) 3  v
~g(c3, d3) id . . .  . -g (c Al dA+1) id g(d*+a, cx)
(« =  1,2....... M +  JV).
The same use is made as before of the natural numbers as domain of 
individuals. And given a system of values rx, r2, . . 
rM> 0 Xt 0%, . .
0 n 
of the propositional and functional variables p1( p2, . . 
pM, fx, f2, . , 
*N>
the propositional function W, used as a value of the variable g, is now deter-, 
mined as follows. The same enumeration is used of the ordered A-tuples of. 
natural numbers. W(u, u) =  t except when u =  k(h +  M  +  N) +  1 (i.e., 
except when u is congruent to 1 modulo h +  M  +  N ). If there is a natural 
number k such that wx =  k(h +  M  +  N) +  1, u2 =  k(k +  M +  N) +  2,
• • •» WA+Af+N =  (A +  1)(* +  Af +  N), then 
«8) =  W{uZt «,) =  . . .  =  
'Pfah+M+s-i f Uh+M+N) “  *P(uh+M+N, wx) — t. 
If 
<wx, v%, . . 
vhy 
is the 
(k +  l)th A-tuple of natural numbers and ut =  k(h +  M  +  N) + 1 
(l =  1, 2, . . 
h +  M  +  N), then 
vx) =  W{u%, v2) =  . . .  =  W{uht vA) 
=  t, and W(uh+j, vx) =  r, (; =  1, 2, . . . ,  M), and W{uh+M+i, vx) =  #<(vXl 
v2> • * *> vh{) (l =  1, 2, ,. 
N). And in all remaining cases *P{u, v) =  f.
In place of the substitutions
^
c l - c 2 .......ca > 
a n r l  
M
 cv c2,...,ch)
;3(3d1)(3d2)...(3dA+1)G 
anQ ‘:)(di)(d2)...(dA+l)H
which were used in the first part of the proof, we now use the substitutions
£Pi
^(3d1)(3d2)...(3dA+/tf+w)G#»
<*p ,
3 ( d 1)(<l2)...( d A + M + ^ ) H J -
.......cft>
f ' i l ' l ,  c 2» - . CA>
J
(d l ) ( d 2 ) - ( d A+ A f+A ')H M +< ’
where /  =
 1, 2, . . 
A f ,  and i —  1, 2, . . „N .

---


§47]
REDUCTIONS OF THE DECISION PROBLEM
211
With these indications, we leave it to the reader to supply the remainder 
of the proof, following the same plan used in the first part of the proof.
By similar methods, involving the use of an enumerably infinite domain 
of individuals (such as the positive integers or the natural numbers) and of 
an enumeration of the ordered pairs or of the ordered A-tuples of individuals, 
many other reductions of the decision problem for validity can be obtained. 
We shall indicate briefly the proof of one more such result, and then con­
clude this section by stating without proof some of the other results which 
can be found in the literature.
**472. 
The class of wffs which are in Skolem normal form with just three 
existential quantifiers in the prefix and which contain just four 
binary functional variables (no other functional variables, and no 
propositional variables) is a reduction class.
Proof. By **471 we may suppose that the given wff A is in Skolem normal
f0rm 
(3a*) (3a.) . . .  (3am) (b*) (b.) . . . (b.)M.
M being the matrix, and contains only a single binary functional variable g. 
We may suppose also that m >  3, the required reduction being obvious in 
the contrary case. Let gx, g2, g3 be binary functional variables which are 
distinct from one another and from g, let xx, x a, . . . ,  
y, z, 
c2, C3 
be distinct individual variables which do not occur in A, and let B be:
(Xi)(y)(z)(3c1)(3c2)(3ca)[g1 (x1, c1)g2(x1, c^g jca, y)g2(Ca, z ) .
6 1 (xi, y te ite , z) =3 g3(y, z) - ga(xx, y)ga(xi» *) => &*(y> z ) . g3(y, z) =>.
6 1 (y* Xi) =  gx(z, xx) . g 2(y, xx) =  g 2(z, xx) . g(y, xx) == g(z, xx) .
g(xx, y) =  g(xx, z)] z>
(3 xi)(x2)(x3) . . .  (xm_1)(a1)(a2) . . .  (am)(b1 )(b2) . . .  (bn) . gx(xx, t^) 
.
g a(xi, x 2) ^ . gx(x2, a2) ^  . g a(x a» Xs) ^  ■ • • * 6 i(Xm™i, am_i) ^  ■
g 2 ( V
l .  ^ m )  ^
By *381, B can be reduced to an equivalent wff C in which the quantifiers 
(xx) and (3xx) have been deleted from the antecedent and the consequent 
of B respectively and have been replaced by an initially placed quantifier 
(3xx). The prenex normal form of C then satisfies the required conditions, 
that it is in Skolem normal form with just three existential quantifiers in 
the prefix and contains just four binary functional variables gx, g2, g3, g.
We have at once that the prenex normal form of C is valid if and only if 
B is valid. That B is valid if and only if A is valid we leave to the reader to 
prove, with the aid of the following remark.

---


278 PURE FUNCTIONALCALCULUSOF FIRST ORDER [Chap.IVJ
Take the natural numbers as domain of individuals, and choose any 
enumeration of the ordered pairs of natural numbers. Given an arbitrary 
value V  of g, a system of values Wv 
of gv g2, g8J may be determined
as follows so as to give to the antecedent of B  the value t; 
v) — t if 
and only if v is the first number in the (u -r l)th ordered pair; W2(ut v) =  t  
if and only if vis the second number in the (w -f l}th ordered pair; Wz(u,v) =  
t if and only if u — v. For this particular system of values of gx, g2, g3 it is 
clear that the consequent of B  has the value t if and only if A  has the value 
t. It is true that, for a given value of g, other systems of values of g*. g2, g« 
may in general be found so as to give to the antecedent of B  the value t; 
but (as may be read from the antecedent of B  itself) these other systems 
of values of g t, g2, g3 must always have certain properties in common with 
the system 
W2, 
which are sufficient to ensure that the consequent, 
of B  has the value t if and only if A  has the value t.
As will be indicated in exercises below, the reduction process of **472 may 
readily be modified so as to obtain only three binary functional variables 
in the wffs of the reduction class instead of four, or, alternatively, so as to 
obtain one binary and one ternary functional variable (the other conditions 
remaining in either case unchanged). By more elaborate methods of the same 
kind it is even possible to reduce this to a single binary functional variable*
According to known results, including that just mentioned, each of the 
following classes of wffs is a reduction class (where it shall be understood in 
each case, without separate mention, that the wffs are to contain no free indi* 
vidual variables and no propositional variables, and that either the wff itself 
or its indicated antecedent and consequent aretobeinprenexnormal form):
Wffs with prefix (BaJ (3a2) (3as) (b1)(b2) .. . (bn) which contain a single 
binary functional variable.446
Wffs with prefix (a)(3b)(c)(3dx)(3d2) . . . (3d„) which contain a single 
binary functional variable.447
44#The reduction to wffs of this prefix containing none but binary functional variables 
is due to Gddel in Monatshefte fiir Mathematik und Physik, vol. 40 (1933), pp. 433-44S 
(another proof by Skolem in Acta Scientiarum Mat hematic arum, vol. 7 (1935), pp. 
193-199). The further reduction to a single binary functional variable is due to Liszto 
Kalradr and J&nos Sur&nyi in The Journal of Symbolic Logic, vol. 12 (1947), pp. 65-73| 
The proof of **472 which is given in outline above is by Gbdel's method.
447The reduction to wffs of this prefix is due to Ackermann in the paper cited in foots* 
notes 430, 435, and the further reduction to a single binary functional variable is due tQ 
Kalm&r in The Journal of Symbolic Logic, vol. 4 (1939), pp. 1-9. The result proved by 
Ackermann can be stated in the somewhat stronger form th at the class of wffs of thfc
f0rm 
(3a) (a,) (a,) . . . (a„)M => (3b) (c)f (b, c),
where M is quantifier>free and contains no individual variables other than a, ax, Og
.. ., a n and f is a binary functional variable occurring in M, is a reduction class.

---


§47]
REDUCTIONS OF THE DECISION PROBLEM
2 7 9
Wffs with prefix (3b1)(3b2)(c)(3d1)(3d2) . . . (3dn) which contain a 
single binary functional variable.448
Wffs with prefix (3ax) (3a2) . .. (3an) (b) which contain a single binary 
functional variable.449
Wffs of the form (a)(b)(c)M1 
(3a)(3b)(c)M2, where Mx and M2 are
quantifier-free and contain none but binary functional variables.450
Hence also wffs with prefix (3a) (3b) (3c) (d) which contain none but 
binary functional variables.450
And also wffs with prefix (3a) (3b) (c) (3d) which contain none but binary 
functional variables.450
448The reduction to wffs of this prefix is due to J6zef Pepis in Fundament a Mathe- 
maticae, vol. 30 (1938), pp. 257-348. More fully, Pepis's result in this paper is th at the 
class of wffs of the form
(a,) (a.) . .. (an)M  => ( S b ^ S b ^ c ) ^ ,  bs, c), 
where M  is quantifier-free, and contains no individual variables other than ai, a2, 
.. ., a n, and contains besides the ternary functional variable f only one singulary 
functional variable, is a reduction class. Or f(b1( b8, c) may be replaced by the dis­
junction fi(bx, c) v f*(bt, c), in which case M  contains the two binary functional 
variables 
and fj and one singulary functional variable. The reduction to the prefix 
(3b1)(3b,)(c)(3d1)(3dl) . . .  (3d n) and a single binary functional variable is due to 
Kalmdr and Surdnyi in The Journal of Symbolic Logic, vol. 15 (1950), pp. 161-173.
449The reduction to wffs of this prefix is again due to Pepis, being a corollary of the 
fuller result quoted in the preceding footnote. The further reduction to a single binary 
functional variable is due to Surdnyi in Matematikai is Fizikai Lapok, vol. 50 (1943), 
pp. 51-74 (see also the paper of Kalmdr and Surdnyi which is cited in the preceding 
footnote).
The same paper of Pepis contains also a number of other results, in the direction 
of reducing the number of functional variables required in connection with various 
prefixes. Some of these have since been superseded by stronger results, but the following 
seems to be worth quoting: in the Ackermann normal form as given in footnote 447, 
M may be restricted to contain, besides the binary functional variable f, only one singu­
lary and one ternary functional variable, or else only one singulary and two binary 
functional variables (as preferred).
450These reductions are due to Surdnyi in the paper cited in the preceding footnote.
(Added in proof.) The same reductions are also obtained by Surdnyi in a paper in 
Acta Mathematica Academiae Scientiarum Hungaricae, vol. 1 (1950), pp. 261-271. 
Another paper by Surdnyi in the same periodical, vol. 2 (1951), pp. 325-335, adds to 
the list of reduction classes the two following: wffs w ith prefix (a)(3b)(c)(3d)(3e) 
which contain none but singulary and binary functional variables, including a t most 
seven binary functional variables; and wffs with prefix (3a)(b)(c)(3d)(3e) which 
contain none but singulary and binary functional variables, including at most seven 
binary functional variables. Two papers by Kalmdr, ibid., vol. 1 (1950), pp. 64-73, 
and vol. 2 (1951), pp. 19-38, add the three following reduction classes: wffs with 
prefix (3a1)(3as)(b1)(bs) ... (bn)(3c) which contain a single binary functional variable; 
wffs with prefix (3a)(b1)(b1) ... (b#l)(3c1)(3c1) which contain a single binary functional 
variable; and wffs with prefix (a1)(a2) . . .  JfanJfSbJfCjJfc,).. . (c^S dJfS d,) which 
contain a single binary functional variable. A reduction of the decision problem for 
satisfiability to th at concerning validity in every finite domain, and hence a reduction 
of the decision problem for validity to th at concerning satisfiability in some finite 
domain, is contained in another paper of Kalmdr, ibid., vol. 2 (1951), pp. 125-141 
(the unsolvability of the decision problem concerning validity in every finite domain 
had already been proved by Trachtenbrot in the paper cited in footnote 567).

---


EXERCISES 47
4 7 .0 . Extend the result of **470 to obtain a reduction of the decision 
problem for provability, by showing how to find a proof of A if a proof of 
B is known.
4 7 .1 . Supply in detail the last part of the proof of **471, which was 
omitted in the text.
4 7 a .  For the proof of **472, supply in detail the omitted demonstration 
that B is valid if and only if A is valid.
47-3- Show that, in **472, the number of binary functional variables may 
be reduced from four to three by introducing a binary functional variable h, 
replacing g2(d, e) everywhere by h(d, e) ~h(e, d), and g3(d, e) everywhere 
by h(d, e)h(e, d).
47-4- Show that, in **472, the reduction process may be modified so as 
to obtain one binary and one ternary functional variable, replacing gj(d, e) 
everywhere by h(d, e, e), g2(d, e) by h(d, e, d), andg3(d, e) by ~h(d, d, e)
4 7 . 5 , 
The leading idea of the reduction process of **472 is to make use of 
an enumeration of the ordered pairs of natural numbers in order to replace a 
sequence of existential quantifiers (3a1)(3aa) . . . {3am) by a single exis­
tential quantifier (SxJ, at the expense of increasing the number of univer­
sal quantifiers. With appropriate modifications, the same idea may be used 
to replace a sequence of universal quantifiers by a single universal quantifi- 
er, at the expense of increasing the number of existential quantifiers. For 
example, (b ^ b g jM  might be replaced by (x1)(3 b 1){3b8) . g^Xj, b2) 
g 2(x1, b2)M , which will have the same value as (b1)(b 2)M  if gx andg2 have 
the values W2 and W2 that are given in the proof of **472. Investigate the 
question what additional reductions of the decision problem for validity can 
be obtained (beyond those of **470-**472) by using this method, together 
with the methods and results of **420-**421, **470-**472.
48* Functional calculus of first order with equality. The functional 
calculus of first order with equality is a logistic system obtained from the 
functional calculus of first order by adding a binary functional constant t, 
and certain axioms (or postulates, according to the point of view) that con­
tain I. Or, alternatively, it may be described as obtained by adjoining 
additional axioms to an applied functional calculus of first order among 
whose primitive symbols is the binary functional constant I . The wffs of the 
system are the same as the wffs of this applied functional calculus of first 
order, but of course there are additional theorems in consequence of the 
added axioms.
280 PURE FUNCTIONALCALCULUSOF FIRST ORDER [Chap.IV

---


§48]
FUNCTIONAL CALCULUS WITH EQUALITY
281
We shall speak of the pure functional calculus of first order with equality if 
the primitive symbols include all propositional and functional variables (as 
listed in §30) and no functional constants except /; an applied functional 
calculus of first order with equality if there are other functional constants in 
addition to I; a simple applied functional calculus of first order with equality 
if there are other functional constants in addition to I  and no functional 
variables. Besides these there is the simple calculus of equality, obtained by 
adding appropriate axioms to the simple applied functional calculus of first 
order which has I as its only functional constant.
If the formulation of §30 is used for the functional calculus of first order, 
the axioms to be added are the single axiom
I(x, x)
and the infinite list of axioms given by the axiom schema
/(a , b) zd . A d  B.
where a is an individual variable or an individual constant, b is an individual 
variable or an individual constant, and B is obtained from A by replacing 
one particular occurrence of a by b, this particular occurrence of a being 
within the scope neither of a quantifier (a) nor of a  quantifier (b). The for­
mulation of the functional calculus of first order with equality that is ob­
tained by adding the functional constant I and the foregoing axioms to F1 
we shall call FJ. And in particular the formulation F/p of the pure functional 
calculus of first order with equality is obtained by adding the functional 
constant I and these axioms to F*p.
For the simple calculus of equality we may begin with the formulation F1 
of a simple applied functional calculus of first order having I as its only 
functional constant. To this we may add the axiom I (x, x) and all the axioms 
given by the above axiom schema, so obtaining the formulation £  of the 
simple calculus of equality. It is sufficient, however, to add only the three 
following axioms:
I(x, x) 
(Reflexive law of equality.)
I(x, y) ZD I(y, x) 
(Commutative law of equality.)
I(x, y) ZD ml(y, z) ZD I(x, z) 
(Transitive law of equality.)
And the formulation of the simple calculus of equality that is obtained in 
this way we call E.
For the pure functional calculus of first order we may use also the formu­
lation Fjp of §40. By adding to this the functional constant I and two axioms,

---


282 PURE FUNCTIONAL CALCULUS OF FIRST ORDER 
[Ch a p. IV
I{x, x)
I{x, y)=> mF(x)=> F(y),
we obtain a formulation of the pure functional of first order with equality 
which we shall call F j\
In all of these calculi the notations =  and =f=, more familiar than/, may 
be introduced by definition as follows:
DI8. 
[a =  b] -> /(a,b)
D19. 
[a + b] ->■ ~/(a, b)
And of course all the definitions and methods of abbreviation of wffs con­
tinue in force which were introduced for the functional calculus of first 
order in §30.
For the principal interpretation of all of these systems it is intended that F 
shall denote the relation of equality, or identity, between individuals.
For example, in the case of the pure functional calculus of first order with 
equality, after choosing some non-empty class as the individuals, we fix the 
principal interpretation by the same semantical rules a-f as given in §30 (for 
the pure functional calculus of first order), together with two additional rules aa 
follows:
gt. 
If a is an individual variable, the value of/(a, a) is t for all values of a,
g2. 
If a and b are distinct individual variables, the value of /(a, b) is t if 
the value of a is the same as the value of b, and the value of /(a, b) is f if the 
values of a and b are different.
The syntactical definitions of validity and satisfiability (§43), as well as 
the metatheorem that every theorem is valid (**434), can be extended in 
obvious fashion to the pure functional calculus of first order with equality, 
and, especially in some of the exercises following, we shall assume that this 
has been done.
EXERCISES 48
48.0. 
In the formulation E of the simple calculus of equality, the commu­
tative and transitive laws of equality may be replaced by Euclid's axiom 
that "things equal to the same thing are also equal to each other," expressed 
as follows in the notation of the system:
I(x, z)I[y, z) =3 /(z, y)
Thus is obtained a formulation £  of the simple calculus of equality which 
has only two added axioms instead of three. Show that E and £  are equiva­
lent in the sense that their theorems are the same.

---


§48]
EXERCISES 48
283
48.1. For each of the systems E and £  show that the added axioms, con­
taining I, are independent.
48.2. Show that the two formulations £  and E of the simple calculus of 
equality are equivalent in the sense that their theorems are the same. (Com­
pare the proof of *340, which may here be paralleled in certain respects.)
48.3. Show that the two formulations F7p and Fgp of the pure functional 
calculus of first order with equality are equivalent in the sense that their 
theorems are the same. (The same method may be used by which the equiv­
alence of Flp and Fjp was proved. But notice, in particular, that the added 
axioms here introduce some new questions in connection with the rules of 
substitution.)
48.4. For a formulation of a simple applied functional calculus of first 
order with equality, if the number of functional constants is finite, show that 
a finite number of added axioms is sufficient, as follows: the reflexive, 
commutative, and transitive laws of equality: for each singulary functional 
constant f  an axiom,
I{x,y)  => ,l{x)
for each binary functional constant f other than I, two axioms,
I{x, y) r> .f(z, z) zd f (y, z),
I{x, y) zd *i(z, x) ZDf{z, y)\
for each ternary functional constant, three analogous axioms; and so on until 
axioms of this kind have been introduced for all the functional constants. 
(Again, compare the method of proof of *340.)
4 8 . 5 . By using an idea similar to that of the preceding exercise, but 
applied to functional variables rather than functional constants, show how, 
for any wff A of F/p, to find a corresponding wff A' of Flp which is valid if 
and only if A is valid and which is a theorem of Flp if and only if A is a theo­
rem of F/p. Hence extend the Godel completeness theorem, **440, to the pure 
functional calculus of first order with equality.
48.6. Use the same method to prove the following extension of **450 
to the pure functional calculus of first order with equality: if a wff of F7p is 
valid in every non-empty finite domain and is also valid in an enumerably 
infinite domain, then it is valid in every non-empty domain.
48,7* Find and prove similar extensions of **453 and **455 to the pure 
functional calculus of first order with equality.
48 .8 . 
Prove the consistency of F7 by making use of the afp of a wff as in 
§32.

---


284 PURE FUNCTIONAL CALCULUS OF FIRST ORDER [Chap. IV
4 8 .9 . Extend the metatheorem **323 to Fz.
4 8 .1 0 . Extend the metatheorem **325 to Fz.
4 8 .11. Extend the principles of duality *372—*374 to F1. (Wffs of F* 
are to be rewritten by means of D18 and D19 in such a way that the symbol 
I  no longer appears explicitly. Then in dualizing, the notations =  and + 
are to be interchanged, as well as 3  and cj:, disjunction and conjunction, 
s  and 
c: and ip t v and |, V and 3.)
4 8 . 1 2 . By using the reduction found in 48.5, solve the decision problem 
for the case of wffs of F/p which have a prenex normal form such that, in the 
prefix, no existential quantifier precedes any universal quantifier. (Notice 
that this includes, in particular, the case of quantifier-free formulas of F/p.)
4 8 . 1 3 - Solve the decision problem for quantifier-free formulas of F/p 
directly, by a method as closely similar as possible to the truth-table decision 
procedure by which it is determined whether a quantifier-free formula of 
Flp is tautologous. Hence restate the solution of the decision problem for the 
special case of 48.12, in a form as similar as possible to that of *460~**463.
4 8 . 1 4 - Solve the decision problem for the singulary functional calculus of 
first order with equality, i.e., for the class of wffs of F/p in which all the 
functional variables occurring are singulary.
Suggestion: Following Behmann, we may add the following reduction 
steps to the reduction steps (a)-(g) of exercise 39.6: (a) to replace a wf part 
(a) [a =  b] by (a) (c) [a =  c], if a and b are distinct individual variables and 
c is the first individual variable in alphabetic order other than a and b; 
(P) to replace a wf part (a) [a 4= b] by (a)[a 4= a], if a and b are distinct 
individual variables; (y) to replace a wf part (a)[a 4= bx 3  . a 4= b8 3  ■... 
a 4= bn 3  a =  b] by the conjunction An[b2 =  b23  A^Jtbj =  b3 3  An_J 
- [bn «  b 3 An_1][b1 = b2 3  . b2 =  b3 3  An_2] [bx =  b2 3  . ^  =  b4 3  
An„2] . .. [bn_2 =  b n ,  bn_! =  bn 3  An-JO.-* =  bno  . bn_x =  b 3
An_2j ............[bj, — b23  ■ bA =  b3 3  . .  . . bj =  b id A^], if a, b^ b2, .. ,,
b n, b are distinct individual variables, cv c2, . . c n, c are the first n +  I 
individual variables in alphabetic order distinct from each other and from 
a, bv b 2> . . ., b n, b, and At is
(a) (Cl) (Ca) . . . (q) (c) „ a 4= q 3  . a 4= c2 3  .. . . a 4= q 3  ■ q 4= c2 3  . 
q  4= c3 3  .. . . q  4= ct 3  . q 4= c 3  * c2 4= c3 3 ..............q 4= c 3  a =  c
(i — 0, I, 2 ,. . 
n)\ (<5) to replace a wf part (a)[a =  a 3  A] by (a)A;
(e) to replace a wf part (a) [a =  b 3  A] by

---


§48]
EXERCISES 48
2 8 5
if a and b are distinct individual variables and A is quantifier-free; (£) to 
replace a wf part (a)[a 4= a zd A] by (a)[a — a]; (?/) to replace awf part 
(a) [a 4= bx zd * a 4= b2 zd . .  . . a 4= b n zd A] by the conjunction A * ^  
=> An J  [B2 zd An_x] . . . [Bb => A n_J [bt =  b2 zd A J  [bx =  b3 zd An_j] . . . 
[bn-i =  bn =3 Ab_J [Bx zd . Ba zd An„2] [Bx =>. B3 =z> An_2] . . .  [ B ^  3  . B„ 
^  An„2] [bx =  b2 rz) ■ B3 zd An_a] [bx — b2 id ■ B4 id An_a] . . . fbn__l — bn ^  . 
B n_a rz> An_2] [bx =  b2 id ■ bx =  b3 id An_2] [bx =  b2 i d  ■ bj — b4 id An_2] . . . 
[b„_3 == bn zd - bn_2 — bn_j zd An„2] [bn„2 =  bn_x 3  ■ bn_2 =  bn zd An_2] . .. 
. . ,  [Bx i d  . B 2 i d  .. .. B n zd A0], if a, ba, b2, . . 
bn are distinct individual 
variables and cX) c2, , .
cn are the first n individual variables in alphabetic 
"order distinct from each other and from a, bv b 2, . . 
b„, and if, further,
A is quantifier-free and contains no individual variables except a, and B i 
and C* are respectively
AI 
and 
S* A|
(i ==1, 2, . . . ,  n), and A* is
(a) (cx) (c2) . .. (c,). a 4= cx rz> . a 4= c2 id .. . . a 4= 
zd .
4= ca ZD „ Cx 4= C3 ID . . . . Cj_x 4= Ct- ID . "C j ZD . ~C 2 ZD - . . . ~Gt ID A
(i =  0, 1, 2, . . ., n) (thus in particular A<, is (a)A).
4 8 . 1 5 . Solve the decision problem for wffs A of FJp such that in each 
elementary part not containing I at most one variable has occurrences at 
which it is a bound variable of A.
4 8 . 1 6 . (1) Extend the method of 46.8 to solve the decision problem for 
wffs of FJp having a prenex normal form (3b)(c)M in which M is the 
matrix and contains no individual variables except b and c. And illustrate 
by applying the solution to the following particular examples:
(2) (3*) (iy) . F(x) zd [F(y) 
F(x) =  G(y) z> . F(y) =  G(x)
{3) 
( 3 * )( y ) . [F(x) =  G(x)] v [F(y) =  G[y) =z x =  y]
4 8 . 1 7 . (1) Extend the method of 46.11(2) to solve the decision problem 
for wffs of Frp having a prenex normal form (a) (3b) (c)M in which M is the 
matrix and contains no individual variables except a, b, c. And illustrate 
by applying the solution to the following particular examples:
(2) 
(a;)(3i/)(z) . F(x, x) zd . F(x, z)ZDx =  y v y  =  zzD.
F{x, z) =  F(x, y) =  F(y, y) zd . F(y, y) =  F(z, z )
(3) 
(x) (3y) (z) . F(x) zd . G(x) ZD . F(y) zd [G(y] zd x  =  y] zd , 
x *  ZZD , G(y) =  F(z) zd . F(y) =  G(z)

---


286 PURE FUNCTIONAL CALCULUS OF FIRST ORDER [Ch a p. IV
(4) 
(x)(3y){z) . x  *  z v y  *  z
48.18. Apply the decision procedure of 48.14 to (2) the example 48.16(2), 
and (3) the example 48.17(3).
4 8 . 1 9 . (1) Solve the decision problem for wffs of F/p having a prenex 
normal form (a1)(a2)(3b)(c)M in which M is the matrix and contains no 
individual variables except av a2J b, c. Illustrate by applying the decision 
procedure to show that the following wffs are theorems of F/p:
(2) 
fa)fa)(iy){z). Ffa, x2) :=> . Ffa, z) == F{y, y) z=> .
x1 4= 2 v x2 4= * => [Ffa, z) Z3 F(xv y)} zd .
F f a ,  V) v F(arl( z) => F f a , x2)
(3) 
fa) fa) (By) (2) .  F fa) 
. F fa ) Z3 .G  fa) Z3 .G  (x2) 
.
xj 4= y=3[F(z) =3 G(z)] =3 . U fa) =3 U fa) =3 [G(y) =3 F(y)] =3 .
G(y) s  F(z) => . F(y) =  G(z)
48.20. Apply the decision procedure of 48.15 to the example 48,19(2).
48.21. (1) State and solve a special case of the decision problem of F/p 
which is analogous to case V' of the decision problem of F1*. (Cf. 40.16.) 
(2) Illustrate by applying the solution to the following particular example:
(3*) (3y) (z) n ~F(x, x) v F(x, z)v F(y, z)
v O =s z =  . F[x, X) =  F[z, z)] v my =* z s  • F{y, y) s  F(z> z)
48.22. Prove the following metatheorem: Let I"1 be a (finite or infinite)
class of wffs of F/p. Let the complete list of free individual variables occur­
ring in wffs of r  be ax, a2, a3, . . .. Let the complete list of propositional 
variables occurring be p1( p2, p3, . . 
and let the complete list of functional 
variables occurring be 
f2, f3, . . . (of course any or all of these lists may be 
infinite), and suppose that f, is an Ar ary functional variable (i — 1, 2, 3,. . .) 
Suppose further that f  is simultaneously satisfied in the domain of positive 
integers by the system of values vv v2, vZl. . 
t v r2, r3, . . 
0 2) 0 3) . ..
of the variables ap a2, a3, . . 
pv p2, p3, .. 
f1( f2, f3, . ... Then in the
domain of rational integers (i.e., positive integers, negative integers, and 0) 
there exist propositional functions Wv 
such that 
is an A,-ary
propositional function of rational integers (t =  1, 2, 3 ,. ..), and for arbi­
trary positive integers uv u%) . . . uhi the truth-value ^(w*, u2, . . 
uht) is 
the same as 0 ,(14, u2, . . 
uh(), and r  is simultaneously satisfied in the
domain of rational integers by the system of values vv vv vv . . 
rlt r2, rv

---


EXERCISES 48
287
.
.
W2, W3, . . . of the variables a,. a2, a3, . . 
p„ p2, p3....... f„ f2, f3,
4fii
Suggestion; We may suppose without loss of generality that the individual
variables alf a2, a3, . . ., if any, are the particular variables zx, z2, 23........
Adjoin to F  all of the wffs xi 4= xk for which the subscripts j and k are 
distinct positive integers, also all of the wffs
for which &i(uv 
uh%) is truth, and also all of the wffs
for which 0 i(u1, u2, . . ., uh ) is falsehood. Let the class of wffs so obtained 
be P ; and let F" be obtained from P  by adjoining further all of the wffs 
yi 4= xk for which the subscripts j and k are arbitrary positive integers, and 
all of the wffs yi 4= y* for which the subscripts 7 and k are distinct positive 
integers. Show that P  is consistent, hence that every finite subclass of P ' 
is consistent. Hence use the result of exercise 48.7 to show that F" is 
simultaneously satisfiable in an enumerably infinite domain $. The individ­
uals of the domain $  which serve as values of xx> z s. x.^, . . . may be identi­
fied with the positive integers 1, 2, ;j, . . . respectively. Besides these $  
necessarily includes infinitely many other individuals, which may then be 
identified in some arbitrary way with the non-positive integers 0, —1, — 2,. .
4 8 .2 3 . 
As a corollary of the foregoing, prove the following metatheorem: 
Let r  be a (finite or infinite) class of wffs of FJp, and let one of the functional 
variables occurring in wffs of Fbe the binary functional variable s. Suppose
*MThe reference to the particular domains of positive integers and of rational integers 
is evidently non-essential, the substance of the metatheorem being that an enumerably 
infinite model of F  (i.e., an enumerably infinite domain together with such a system 
of values of the free variables as to satisfy Fsim ultaneously in that domain) is always 
capable of an enumerably infinite extension. The result is substantially duo to A. Mal­
cev in a paper in the Recuetl Mathematique, vol. 43 (n.s. vol. 1) (1936). pp. 323-336, and 
the proof which is suggested above employs some of Maleev's ideas. Although Malcev's 
own proof is defective in regard to the use which he makes of the Skolcm normal form 
for satisfiability, it appears that the defect is not difficult to remedy—by supplying an 
appropriate discussion of the relationship between a model of P  and a model of the 
class r% obtained from r  bv first making a suitably chosen alphabetic change of func­
tional variables and then reducing every wff to Skolcm normal form for satisfiability in 
such a way that the new functional variables introduced are all distinct from each 
Other and from functional variables previously present. However, it seems to be pref­
erable to avoid use of the Skolem normal form for satisfiability by substituting a proof 
like that suggested above.
It should be added that Malcev proves only that every infinite model of F  has an 
extension (which might be a finite extension). But liis methods can be made to yield the 
Stronger result that there is an enumerably infinite extension.
On the other hand, Malcev deals with non-emimerably infinite models as well as 
enumerably infinite models, a m atter into which we do not enter here.

---


288 PURE FUNCTIONAL CALCULUS OF FIRST ORDER [Chap. IV
that r  is simultaneously satisfiable in the domain of positive integers in 
such a way that the value of s is the successor relation, i.e., the relation a 
such that a(u, v) is truth if and only if u +  1 =  v. Then T  is also simultane­
ously satisfiable in an enumerably infinite domain ft, with 0  as the value of 
s, in such a way that there is no one-to-one transformation of ft into the 
positive integers under which the relation 0  is transformed into the re­
lation <r452
4 8 , 
^4 . Prove that, if a class of wffs of F/p is simultaneously satisfiable in 
some non-empty finite domain of individuals but is not simultaneously 
satisfiable in an enumerably infinite domain, then there is a greatest finite 
domain in which it is simultaneously satisfiable.
49, H istorical notes. The chief features which distinguish the functional 
calculi of first order (and of higher orders) from the propositional calculus, 
namely, the notion of propositional function and the use of quantifiers, 
originated with Frege in his Begriffssckrift of 1879.
Somewhat later, and independently, quantifiers were introduced by C. S. 
Peirce,453 who credits the idea to 0. H. Mitchell. Still later, quantifiers 
appear in the work of Schroder, Peano, Russell, and others. The terms 
"quantifier” and "quantification” are Peirce's. The notation which we have 
been using for quantifiers is Russell's modification of the Peano notation.
The separation of the functional calculi of first order from those of higher 
order is implicit in Russell's theory of types,454 or perhaps even earlier in 
Frege’s hierarchy of "Stufen” or Schrdder's hierarchy of "reine Mannig- 
faltigkeiten.” The consideration by Lowenheim,466 and afterwards by 
Skolem,450 of "Zahlausdriicke” and "Zahlgleichungen” in connection with 
the Schroder calculus is in effect a treatment of the functional calculus of 
first order with equality. The singulary functional calculi of first and second 
order, with and without equality, were also treated by Behmann.467 But the 
first explicit formulation of the functional calculus of first order as an in-
‘“ From this there follows quickly the result of Skolem according to which no cate­
gorical system of postulates for the positive integers (whether the number of postulates 
is finite of infinite) can be expressed in the notation of a simple applied functional 
calculus of first Order with equality. See exercise 55.18 and footnote 547.
•‘•See American Journal of Mathematics, vol. 7 (1885), p. 194. Peirce's reference is 
probably to a paper by Mitchell in Studies in Logic (1883); but one essential point, the 
use of an Operator variable in connection with the quantifier, was contributed by 
Peirce himself as a modification of Mitchell's notation.
‘“ Bertrand Russell, “ Mathematical Logic as Based on the Theory of Types," pub­
lished m the American Journal of Mathematics, vol. 30 (1008), pp. 222-202,
‘“ In the Mathematische Annalen, vol, 76 (1915), pp. 447-470.
‘“ In papers published in Sknfter Utgit av V idenshapsselskapet i Kristiania, I. Mate- 
matisk-naturvidenskabelig Klasse, volumes for 1919 and 1920.
*6TIn the Mathematische Annalen, vol. 86 (1922), pp. 163-229.

---


m
HISTORICAL NOTES
289
dependent logistic system is perhaps in the first edition of Hilbert and 
Ackermann's Grundziige der Theoretischen Logik {1928).
For the functional calculus of first order and the functional calculus of 
second order (see Chapter V) Hilbert and Ackermann in their first edition 
employ the names “engerer Funktionenkalkiil" and “erweiterter Funk- 
tionenkalkiil" respectively. In their second edition (1938), partly following 
Hilbert and Bernays, they change these names to '‘engerer Pradikatenkal- 
kiil" and "Pradikatenkalkiil der zweiten Stufe.” This change is based on a 
usage of the word “Pradikat" (predicate)458 which appears already in the 
first edition of Hilbert and Ackermann, but which we wish to avoid. In 
this book we have taken the term “functional calculus" from Hilbert and 
Ackermann's first edition, but have borrowed the numbering of orders 
from their second edition (where they use "Pradikatenkalkiil der ersten 
Stufe" as synonymous with "engerer Pradikatenkalkiil").
The axioms and rules of inference for the system F1 are essentially those 
of Russell in his paper of 1908,454 with some modifications, and with Russell's 
axioms for the propositional calculus replaced by those of Lukasiewicz. 
Russell, however, does not make it unmistakably clear whether he is stating 
single axioms or axiom schemata. It is possible to resolve this ambiguity in 
favor of axiom schemata, as in F1. Later statements by Russell seem to 
favor on the whole the interpretation as single axioms, but then his rules of 
inference must be augmented by adding rules of substitution, as in FgP.
Especially difficult is the matter of a correct statement of the rule of 
substitution for functional variables. An inadequate statement of this rule 
for the pure functional calculus of first order appears in the first edition of 
Hilbert and Ackermann (1928). There are better statements of the rule in 
Carnap's Logische Syntax der Sprache and in Quine's A System of Logistic 
(1934), but neither of these is fully correct. In the first volume of Hilbert 
and Bernays's Grundlagen der Mathematik (1934) the error of Hilbert and 
Ackermann is noted,469 and a correct statement of a rule of substitution for *
*MBy H ilbert and Ackermann, and by Hilbert and Bernays, the name "Pr£dikat" 
is applied to the same things which we call “propositional functions" and which 
Hilbert and Bernays call also "logische Funktionen" (see their Grundlagen der Mathe- 
matik, vol. 1 (1934), pp. 7, 120, 190). We prefer here the usage of Carnap (Logische 
Syntax der Sprache, 1934), who applies the name "Pradikat" to what is called by Hilbert 
and Bernays "Pr&dikatensymbol." Indeed Carnap’s usage is nearer to the familiar use 
of "predicate" as a grammatical term  in connection with the natural languages, and 
therefore seems to run less risk of leading in practice to confusion of use and mention 
(cf, §08).
4MA revised statem ent of the rule is given also in the second edition of Hilbert and 
Ackermann's book (1938, see pp. 56-57), but this is still open to some objection. In 
the third edition the rule is correctly stated (1949, see pp. 00-01).

---


290 PURE FUNCTIONAL CALCULUS OF FIRST ORDER 
[Ch a p. IV
functional variables is given for the first time. However, Hilbert and Ber- 
nays's form of the rule could not be used in this book, because its correctness 
depends on a special feature of their formation rule corresponding to our 
30v, according to which (Va)B is not wf if B contains a as a bound vari­
able.460 And our form of the rule is to be thought of rather as compiled by 
combining the versions of Carnap and of Quine.461
In §32 the proof of consistency of F1 which depends on **320 is taken from 
the first edition of Hilbert and Ackermann (1928), It is given in a form to 
make its character unmistakable as being purely syntactical (rather than 
semantical). But it may also be described as depending on the remark, that 
the axioms are valid in a domain consisting of a single individual and the 
rules of inference preserve this property. And in this form it becomes ob­
vious how the method may be extended to prove the consistency of the 
functional calculi of higher order, in particular of the functional calculus of 
order cu. This is Herbrand's proof462 of the consistency of the functional cal- 40 * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
4l0This contravenes the idea, which is implicit in the account given in §02, and which
would seem to the writer natural on its own account, that a constant, as distinct from a
form, may be used with the same meaning in any context (without regard to variables
appearing). And, more serious, it imposes in connection with the use of abbreviative
definition the practically intolerable burden of remembering for every definiendum the
particular bound variables that occur in the definiens. However, this latter difficulty 
does not arise for H ilbert and Bernays, because, as already noticed, they do not make
use of abbreviative definition.
wlIn the case of logistic systems which involve operators other than quantifiers,
such as the abstraction operator A or the description operator 1 (see §00), correct state­
ment of the rule of substitution for functional variables becomes still more troublesome
and lengthy. For an example of astatem ent of the rule insuch a case, reference may be made
to Godel's On Undecidable Propositions of Formal Mathematical Systems (mimeographed
lecture notes of 1934), where the full statem ent was included at the suggestion of S. C,
Kleene; also to a reproduction of this statem ent, with modifications to adapt it to another 
system, in the present writer's review of the above-mentioned book of Quine in the
Bulletin of the American Mathematical Society, vol. 41 (1936), pp. 698-003. (The state­
ment in the Gddel notes is, however, not quite correct, but requires to be amended by
adding to 4b on page 10 the additional condition that no bound variable of G(x) is free
in A.)
In the case of systems having the abstraction operator A, it is possible to replace the
rule of substitution for functional variables by a number of simpler primitive rules 
which may be thought of as constituting an analysis of it, as we shall see in Chapter X,
Because of the complications which attend the rule of substitution for functional varia­
bles, even in the comparatively simple case of the functional calculus of first order, there
therefore seems to be some ground for preferring systems (like th at of Chapter X)
which have the operator A, However, the functional calculi, not having this operator,
have been more extensively studied; and they do have an argument of economy in their
favor, in view of Russell's discovery that description and abstraction operators can for
many purposes be dispensed with,
*” In his dissertation, cited in footnote 442—Warsaw 1930, see p, 51 and pp. 67-60.
Independently of Herbrand, and of one another, this consistency proof was later found
also by Tarski, then by Gentzen, and by E. W. Beth. The remark is added by Beth
(Nieuw Archief voor Wiskunde, ser. 2 vol. 19 nos 1-2 (1936), pp. 69-62) that the same
method can be used to prove consistency of the predicative and ramified functional

---


§49]
HISTORICAL NOTES
291
culi of first and higher orders; it remains applicable if axioms of choice or 
multiplicative axioms are added (as Herbrand remarks) and if axioms of 
extensionality are also added, but not of course upon addition of any sort 
Of axiom of infinity,488
The remark is made in the first edition of Hilbert and Ackermann that 
the functional calculus of first order (in a formulation which is somewhat 
different from F1 or Fjp, but easily seen to be equivalent) is not complete 
with respect to the transformation of A into ~A , and the question of 
completeness in the weaker sense of **440 is put as an unsolved problem. 
The first proof of completeness in the latter sense is that of Godel,464 which is 
reproduced in §44. Another proof of completeness of the functional calculus of 
first order is due to Leon Henkin486 and is reproduced in §45 (see further §54).
Independence of axioms for the pure functional calculus of first order was 
first treated by Godel,468 and for a formulation which is nearer to that of 
Russell454 than our Flp or Fjp. Indeed Godel adds also the axioms x — x 
and x =  y ^  . F(x) ^  F(y), and establishes the independence of the axioms 
of the resulting formulation of the pure functional calculus of first order 
with equality. He does not prove the independence of the rules of inference, 
but makes only the statement that this can easily be done.
For the Hilbert-Ackermann formulation of the pure functional cal­
culus of first order, independence of both the axioms and the rules of in­
ference was treated by McKinsey.487 However, McKinsey understands the 
independence of a rule of inference in a weaker sense than that which we have 
adopted, and his proofs are not in all cases sufficient to show the independ­
ence of Hilbert and Ackermann's rules in the strong sense 468 The second 
edition of Hilbert and Ackermann (1938) contains a demonstration of the
Calculi—to which axioms of reducibility may be added, if desired, as well as axioms of 
Choice and of extensionality, but not of course any axiom of infinity.
4MThe terminology will be explained in Chapters V and VI.
iMM o n a ls h e fte  fu r  M a th e m a tik  u n d  P h y s ik , vol. 37 (1930), pp. 349-360. The essential 
points of a completeness proof by a  method similar to th at of Godel are also in Her- 
brand’s dissertation of 1930—compare exercises 46.23, 46.24. The germ of the method 
used by H erbrand and by Gtidel is to be found already in Skolem's paper of 1928 
(cited in footnote 430).
4,#In his dissertation (Princeton University, 1947) and in a paper in T h e J o u r n a l o f 
S ym b o lic L o g ic , vol 14 (1949), pp. 159-166.
4l4In the paper cited in footnote 464. Compare exercise 41.1.
A m e r ic a n  J o u r n a l o f M a th e m a tic s , vol. 58 (1936), pp. 336-344.
441 As indicated in the discussion in §41 of the rules *404* (« >  1), the weaker sense of 
independence is not without its importance. But it seems desirable to prove independ­
ence in the strong sense when possible. (The question of the separate independence of 
the different rules *404* does not arise for McKinsey or for Hilbert and Ackermann 
because they take all of these rules together as a single rule, or, in the case of Hilbert 
and Ackermann, all of them but *404o.)

---


292 PURE FUNCTIONAL CALCULUS OF FIRST ORDER [Ch a p. IV
independence of their axioms and rules, credited to Bernays, in which this 
defect is overcome.
The results of §34 are found in the first edition of Hilbert and Ackermann 
(1928) in a form which differs only in detail from ours. And see also the 
discussion of “truth-functions" and “formal equivalence" in the introduc­
tion to the first volume of Principia Matkematica (1910).
Use of the prenex normal form was introduced by C. S. Peirce, although in 
a different terminology and notation.469 Peirce uses the term “Boolian” for 
what we here, following Principia Matkematica, call the matrix, and speaks 
of the prefix as “Quantifier" or “quantifiers." The process of reduction 
to prenex normal form which is explained in §39 is to be found in substance 
in the first volume of Principia Mathematical70 though it is there somewhat 
obscured by the peculiar doctrine that (in effect) only formulas in prenex 
normal form are to be considered wf, other formulas which we would treat 
as wf being construed, by abbreviative definition, simply as standing for 
their prenex normal forms. And from this source the reduction process 
appears in Behmann's paper of 1922, already referred to, and again in a 
paper of C. H. Langford.471
Origin of the functional calculus of first order with equality is difficult to 
fix. In a sense, it is implicit already in the work of Peirce and Schroder. 
Especially good is the treatment of this subject in the first volume of Hilbert 
and Bernays, which contains much that we have not here touched upon. 
From this source we have taken, in particular, the results which are indi­
cated in exercises 48.0, 48.4. The idea of the reduction indicated in exercise 
48.5 is due to Kalmar472 and Godel,473 and the result of the exercise is due to 
Godel.473 The simple calculus of equality has been treated in detail by 
Heinrich Scholz.474
Developments of the last three or four decades in regard to questions of 
validity and satisfiability, the decision problem, and related matters may
4WSee a paper in The Monist, vol. 7 (1897), pp. 161-217; also his paper, already 
referred to, in the American Journal of Mathematics, vol. 7 (1885), pp. 180-202; and 
an otherwise unpublished addendum to the latter which appears in his Collected Papers, 
vol. 3 (1933), pp. 239-249.
4760 f course it is not im portant in this connection th a t in Principia disjunction and 
negation are used as primitive connectives rather than our im plication and negation, 
as the process of reduction to prenex norm al form appropriate to one system  of primi­
tive lontonco connectives is very easily modified to fit another, And in fact the Intro* 
duction to the second edition of Principia indicates the m odification to be made for 
the case of Sheffer's stroke as sole prim itive sentence connective.
471In the Bulletin of the American Mathematical Society, vol 32 (1926), see p. 701,
in Acta Scientarum Mathematicarum, vol. 4 no. 4 (1929), pp. 246-252,
47#In the paper cited in footnote 464.
474In his Metaphysik als Slrenge Wissenschaft, 1941.

---


§49]
HISTORICAL NOTES
293
perhaps be dated from Lowenheim's paper of 1915.475 This contains the 
following results regarding the functional calculus of first order with equal­
ity: a solution of the decision problem for validity in the case that only 
singulary functional variables appear; a reduction of the general case of the 
decision problem for validity to that in which only binary functional vari­
ables appear; recognition of the existence of wffs that are valid in every 
finite domain but not valid in an infinite domain, and a demonstration 
that no wff containing only singulary functional variables can have this 
property; finally, a proof of the metatheorem now known as Lbwenheim's 
theorem, i.e,, **450 and the extension of **450 which is stated in exercise 
48.6.
After the pioneering work of Lowenheim there followed the contributions 
of Skolem in his papers of 1919 and 1920.478 The first paper contains, in 
effect, a solution of the decision problem for validity for the singulaiy func­
tional calculus of second order, including at the same time an improved form 
of the solution for the singulary functional calculus of first order with equal­
ity. In the paper of 1920 the Skolem normal form for satisfiability is intro­
duced and is used to obtain a simpler proof of Lowenheim's theorem. The 
point of view of satisfiability is adopted in this paper rather than that of 
validity (as by Lowenheim), and Lowenheim's theorem is therefore restated 
in the form of **451 and the extension of **451 to F7. Also Skolem's gen­
eralization of Lowenheim's theorem, **455, is here proved for the first time.
Behmann's paper477 of 1922 contains the result of exercise 39.6, and solu­
tions of the decision problem for validity for the singulary functional cal­
culus of first order, the singulary functional calculus of first order with 
equality, and the singulary functional calculus of second order. Lor the 
singulary functional calculus of first order Behmann's method, with some 
modifications due to Quine,478 is reproduced in §46 above. And for the sin­
gulary functional calculus of first order with equality Behmann's method is 
sketched in exercise 48.14. The latter method is similar to that of Skolem in 
some important respects, but seems to have been found independently by 
Behmann.
The reduction of a wff A of the singulary functional calculus of first order 
to the form B which is described in exercise 46.1(1) is due in substance to
*f* *Cited in footnote 465.
*MCited in footnote 456.
*” Cited in footnote 457.
4T,See Quine’s paper in The Journal of Symbolic Logic, vol. 10 (1946), pp. 1-12. Com­
pare also the modified form of Behmann's method which is given by Hilbert and Ber- 
Oftys. Grundlagen der MaikemcUik, vol. 1 (1934], pp. 193-195.

---


294 
PURE FUNCTIONAL CALCULUS OF FIRST ORDER [Chap. IV
Herbrand 479 and the resulting form of the solution of the decision problem 
of the singulary functional calculus of first order which is given in 40.1(2) 
is due to Quine.480
The first treatment of cases of the decision problem in which functional 
variables other than singulary may appear is in a paper by Paul Bernays 
and Moses Schonfinkel in 1928.481 This paper contains a solution of case I 
of the decision problem of the functional calculus of first order which (ex­
cept that only the decision problem for validity is treated) is substantially 
the same as that given in §46 above. Also a solution of case VIJ of the de­
cision problem for validity, and the solution of case III (singulary functional 
calculus of first order) which is reproduced above in **466 and its proof.
The subsequent history of work on the decision problem has already been 
given in some detail in §§46 and 47, including exercises and footnotes to these 
sections. It remains only to mention the paper of F. P. Ramsey482 dealing 
with the special case of the decision problem of the pure functional calculus 
of first order with equality for which a solution is indicated in exercises
48.12, 48.13. (The method of these two exercises is, however, much simpler 
than that of Ramsey.)
In a paper of 1929,483 Skolem gives a new proof of his generalization of 
Lowenheim's theorem in which the result is freed of dependence on the axiom 
of choice,484 and at the same time use of the Skolem normal form is avoided.
The metatheorem **453 is due to Godel,485 as well as the extension of 
**453 to the pure functional calculus of first order with equality (48.7). 
The proof of **453 which is given in §45 is due to Henkin, as well as the proof 
of Skolem's generalization of Lowenheim's theorem (**455) which is based 
on this,483 and the remark of exercise 45.4.
w In his dissertation, cited in footnote 442, Chapter 2, §9.2.
480In his 0  S e n tid o  da  N o va  L d g ica , S&o Paulo, Brazil, 1944. 
i n M a ih e m a tisc h e  A n n a le n , vol. 99 (1928), pp. 342-372.
w P ro ceed in g s o f the L o n d o n  M a th e m a tic a l S o ciety, ser. 2 vol. 30 (1930), pp. 264-288. 
Reprinted in Ramsey’s T h e F o u n d a tio n s  o f M a th e m a tic s a n d  O ther L o g ica l E ssa ys,
pp. 82-111.
*n S k r ifie r  u tg iti av del N o rsk s V id e n s k a p s -A  k a d em i i O slo, X. Matematisk-naturviden- 
skapelig Klasse, volume lor 1929.
4Ml.e., the axiom of choice is not used in the syntax language. (See the discussion of 
the axiom of choice in Chapter VI.)
4MIn the paper cited in footnote 464.
48* *In his dissertation, and in the paper cited in footnote 485.

---


V. Functional Calculi of Second Order
