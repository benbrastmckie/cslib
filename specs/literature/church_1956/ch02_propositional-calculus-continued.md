<!-- Source: Church, A. (1956). Introduction to Mathematical Logic. Chapter II: The Propositional Calculus (Continued, pages 119-179). BibKey: Church1956 -->

20. The primitive basis of P2. Another formulation of the propositional 
calculus is the logistic system P2, which differs from Pj primarily in the lack 
of (propositional) constants.
The primitive symbols of P2 are the four improper symbols
[ 
=> 
] 
~
and the infinite list of (propositional) variables
P 
q r s px qx 
rx 
sx p% 
. . ■
(the order here indicated being called the alphabetic order of the variables). 
The formation rules of P2 are:
20i. 
A variable standing alone is a wff.
20ii. 
If r  is wf( then ~T is wf.
20iii. 
If r  and A are wf, then [T=>A] is wf.
A formula of Pa is wf if and only if its being so follows from the three 
formation rules. As in the case of Pv an effective test of well-formedness 
follows. In §22 we shall prove also that every wff of P2, other than a variable 
standing alone, is of one and only one of the forms »A and [A =3 B] (where 
A and B are wf) and in each case is of that form in only one way. In a wff 
[A ID B], the wf parts A and B are the antecedent and consequent respectively 
and the occurrence of ID  between them is the principal implication sign. 
The rules of inference of P2 are the same as those of P*:
*200. 
From [A id  B] and A to infer B. 
(Rule of modus ponens.)
*201. 
From A to infer SgA|. 
(Rule of substitution.)
The axioms of Pa are the three following:
f202. 
pz> 
p
f 203. 
s =d O= d ?]:d . s =d £ = > . s :=>? 
f204, 
~pz> 
ID 
p
The axioms are in order the law of affirmation of the consequent, the self­
distributive law of implication, and the converse law of contraposition. In

---


120
THE PROPOSITIONAL CALCULUS
[Chap. II
stating them we have used the same conventions about omission of brackets 
and use of heavy dots that were explained in §11, and we shall use these 
hereafter without remark in connection with any formulation of the prop­
ositional calculus. For P2 we shall use also the definition schemata D3-11 
of §11, however understanding the 
which appears in them to be the 
primitive symbol * of P2.
The principal interpretation of P, is given by the following semantical rules:
a. 
The variables are variables having the range t and f.
b. A wff consisting of a variable a standing alone has the value t for the 
value t of a, and the value f for the value f of a.
c. 
For a given assignment of values to the variables of A, the value of ~A 
is f if the value of A is t; and the value of ~A is t if the value of A is f.
d. For a given assignment of values to the variables of A and B, the value 
of [A zo B] is t if either the value of B is t or the value of A is f; and the value 
of [A 13 B] is f if the value of B is f and at the same time the value of A is t.
21. The deduction theorem for P2. As in the case of Pv we have 
at once the rule of simultaneous substitution as a derived rule:
*210. 
If 1- A and if blf b2, . . bnare distinct variables, then b Sjf
We have also, as theorem of P2:
f211. 
p zd p 
(Reflexive law of implication,)
Proof. By simultaneous substitution in f203:
b p=>[q-=>p}-=>mp-=>q-=)mpZDp 
Hence by f202 and modus ponens:
Yp zd ? zd mp zdp
Hence by substituting q zd p iorq, and using f202 and modus ponens again:
vp-=>p
Now the proof of the deduction theorem in §13 required only£ ZD p, the 
law of affirmation of the consequent, and the self-distributive law of im­
plication (together with the rules of modus ponens and simultaneous sub­
stitution). Hence by the same proof we obtain the deduction theorem, and 
its corollary, as metatheorems of P2:
*212. 
If Aj, A2, . . 
An b B, then Aj, A2, . . 
An_x b A„ ZD B. 
*213. 
If A b B, then b A => B.

---


§22] 
FURTHER THEOREMS AND METATHEOREMS
121
Also analogues of *133 and *134 are proved as before:
*214. 
If every wff which occurs at least once in the list A1( A2>. . 
An 
also occurs at least once in the list ClP C2, . . 
Cr, and if Aj, A2, . . 
Afl 1- B, then C1( C2, . . . f Cr t B ,
*215. 
If b B then Cl( C„ . . 
Cr b B.
22. Some further theorems and metatheorems of P2. Hereafter 
we shall adopt a more condensed arrangement in exhibiting proofs of P2, 
and later of other logistic systems. In particular we shall often omit explicit 
references to uses of substitution, modus ponens, or deduction theorem.
■f220. 
~p z> mp ZD q 
(Law of denial of the antecedent.)
Proof. By 1202, «*p b ~q Z> ~p.
Hence by f204, ~ p V p z * q .
Then use the deduction theorem.
f221. 
~~p => p 
(Law of double negation.)
Proof. By |220, ~~p b ~p z> ~—*p.
Hence b y  f204, —»p b +~p i d  p
Use modus ponens, then the deduction theorem.
|222. 
p ZD ~~p 
(Converse law of double negation.)
Proof. By f  221, b ~~~p i d  ~p. Hence use f204.
•j-223. 
p Z 3 q z o * ~ q Z > ~ p  
(Law of contraposition.)
Proof. By f221, p z>  q, ~~p b q.
Hence by |222, p z> q, ~~p b ~~q.
Hence p O  q b ~~p ID  ~~q.
Use f204. Then use the deduction theorem.
|224* 
p Z) [r <$: r] => ~p
Proof. By f221, p ZD [r c£ r], — p b r c£ r.
Hence p 3  [r 
r) b ~~p id . r 
r.
Hence by \2Q4, p 3  [r c£ r] b r 3  r Z> ~p.
Hence by f211, p z> [r 
r] b ~p.
Then use the deduction theorem.
For the effective test of well-formedness referred to in §20, and also for 
a number of other metatheorems which now follow, we make use of the

---


122
THE PROPOSITIONAL CALCULUS
[Chap. II
same process of counting brackets which is described in §10. Namely, we 
start at the beginning (or left) of a formula and proceed from left to right, 
counting each occurrence of [ as +1 and each occurrence of ] as —1, and 
adding as we go. The number which we assign, by this counting process, to 
an occurrence of a bracket will be called the number of that occurrence of a 
bracket in the formula.
It follows from the definition of a wff that, if a wff contains brackets, it 
must end with an occurrence of ] as its final symbol; this we shall call the 
final bracket of the wff. By mathematical induction with respect to the total 
number of occurrences of => and 
the following lemma is readily established: 
The number of an occurrence of a bracket in a wff is positive, except in the case 
of the final bracket, which has the number 0, and the number of an occurrence 
of [ in a wff is greater than 1, except in the case of the first occurrence of [.
**225. 
Every wff, other than a variable standing alone, is of one and only 
one of the forms ~A and [A 
B], and in each case it is of that form 
in one and only one way.
Proof. The first half of the theorem is obvious, by the definition of a wff.
Again it is obvious that, if a wff has the form ~A, it has that form in only 
one way (i.e., A is uniquely determined), for we may obtain A by just 
deleting ~ from the beginning of the wff.
It remains to show that, if a wff has the form [A 
B], it has that form in 
only one way. Suppose then that [A => B] and [G zd D] are the same wff. 
If A contains no brackets; then—because it is evident, from the definition 
of a wff, that the first occurrence of id in a wff must be preceded by an occur­
rence somewhere of [—it follows that the first occurrence of id in [A ID B] 
is immediately after A, and hence—for the same reason—that C is iden­
tical with A. By the same argument, if G contains no brackets, G and A 
are identical. If A and G both contain brackets, then the final bracket of A 
is the first occurrence of a bracket with the number 0 in A, and therefore is 
the second occurrence of a bracket with the number 1 in [A zd B]; and the 
final bracket of G is the first occurrence of a bracket with the number 0 in C, 
therefore the second occurrence of a bracket with the number 1 in [G zd D ]; 
this makes the final bracket of A and the final bracket of C coincide, and 
so makes A and G identical. Thus we have in every case that A and G are 
identical, and it then follows obviously that B and D are identical.
**226. 
A wf part200 of ~A either coincides with 
or is a wf part of A.
Proof. The case to be excluded is that of a wf part M of ~A, obtained by

---


§22] 
FURTHER THEOREMS AND METATHEOREMS
123
deleting one or more symbols at the end (or right) of -A  and none at the 
beginning (or left). If M contains brackets, the impossibility of this follows 
because the number of the final bracket of M would be 0 in A although it 
is not the final bracket of A. If M contains no brackets, the impossibility 
follows quickly by mathematical induction with respect to the number 
of consecutive occurrences of ~ at the beginning of A.
**227. 
A wf part of [A ^  B] either coincides with [A => B] or is a wf part 
of A or is a wf part of B.201
Proof. The case to be excluded is that of a wf part of [A i d B] which, 
without coinciding with [A ^  B], includes the principal implication sign 
of [A zd B] or the final bracket of [A id B] or the occurrence of [ at the 
beginning of [ A d B],
Suppose that M is such a wf part of [A ^  B]. Then M contains brackets. 
Either the final bracket of M precedes the final bracket of [A zd B], and 
therefore has the number 0 in M but a positive number in [A ^  B]; or else 
the first occurrence of [ in M is later than the occurrence of [ at the beginning 
of [A r> B], and therefore has the number 1 in M but a greater number in 
[A ZD B]. It follows in either case that every occurrence of a bracket in M 
has a number in M less than its number in [A id B]. Hence the final bracket 
of M must indeed precede the final bracket of [ A id B], and the first 
occurrence of [ in M must also be later than the occurrence of [ at the 
beginning of [A zd B].
Since we now have, as the only remaining possibility, that M includes 
the principle implication sign of [ A d B], it must include somewhere at 
least one bracket which precedes this principal implication sign and is 
therefore in A. Thus A contains brackets. The final bracket of A has the 
number 0 in A, therefore the number 1 in [A zd B], therefore a number less 
than 1 in M; but this is impossible because it is not the final bracket of M.
**228. 
If A, M, N are wf and T results from A by substitution of N for 
M at zero or more places (not necessarily at all occurrences of M 
in A), then T is wf.
Proof. For the two special cases, (a) that the substitution of N for M is 
at zero places in A, and (b) that M coincides with A and the substitution of 
N for M is at this one place in A, the result is immediate. For we have in 
case (a) that T is A, and in case (b) that T is N.
■«By a "wf part" of a formula we shall always mean a wf consecutive part of it—as 
indeed is the natural and obvious terminology.
S0XAs to the metatheorems **225-**227, compare 12.1 and footnote 176.

---


124
THE PROPOSITIONAL CALCULUS
[Ch a p . II
In order to prove **228 generally, we proceed by mathematical induction 
with respect to the total number of occurrences of the symbols zd and ~ 
in A. If this total number is 0, we must have either case (a) or case (b), and 
the well-formedness of T is then immediate, as we have just seen. Consider 
then a wff A in which this total number is greater than 0; the only possible 
cases are the two following:
Case I: A is of the form ~A X. Then by **226 (unless we have the special 
case (b) already considered) T is ~ r x, where 1^ results from At by substi­
tution of N for M at zero or more places. By hypothesis of induction, 
is 
wf. Hence by 20ii it follows that T is wf.
Case 2: A is of the form [At:z> Aa].Then by **227 (unless we have the special 
case (b) already considered) T is [1^ => T2], where I \ and V2 result from 
Ax and A2 respectively by substitution of N for M at zero or more places. 
By hypothesis of induction, Tx and T2 are wf. Hence by 20iii it follows that 
T is wf.
The proof by mathematical induction is then complete.
*229. 
If B results from A by substitution of N for M at zero or more 
places (not necessarily at all occurrences of M in A), then
M=>N,  N d M I - A d
B
and
M d N, N d  M 1- B d  A.
Proof. For the two special cases, (a) that the substitution of N for M is 
at zero places in A, and (b) that M coincides with A, and the substitution of 
N for M is at this one place in A, the result is immediate; namely, in case
(a) by substitution in f211, and in case (b) because A d B and B id A are 
the same as M d  N and N d M respectively.
In order to prove *229 generally, we proceed by mathematical induction 
with respect to the total number of occurrences of the symbols rD and ~ 
in A. If this total number is 0, we must have one of the special cases (a) and
(b) , and the result of *229 then follows immediately, as we have just seen. 
Consider then a wff A in which this total number is greater than 0; the only 
possible cases are the two following:
Case 1: A is of the form ~A X. Then by **226 (unless we have the special 
case (b) already considered) B is of the form ~ Bv where Bx results from Ax 
by substitution of N for M at zero or more places. By hypothesis of induction,
M n N ,
M d N, N zd M f- 
=d Ax.

---


§23] 
RELATIONSHIP OF THE TWO FORMULATIONS
125
Hence we get the result of *229 by substitution in f223 and modus ponens.
Case 2: A is of the form Ax o  Aa. Then by **227 (unless we have the special
case (b) already considered) B is of the form 
=d Ba, where 
and B2 result
from At and Aa respectively, by substitution of N for M at zero or more 
places. By hypothesis of induction,
M => N, N d MI - A1 d B1,
M 
N, N d
M F B ^ A ,  
M d N , N d
M F A 2 d B 2j 
M n N ,  N d M1 - B z d  Aa.
By modus ponens,
Bj 3  Ax, A2 => B2j Ax => A2, Bx 1- B2,
A^ 
B1( B2 o  A2j B^ ^  B2, Aj t- A2.
Hence we get the result of *229 by use of the deduction theorem.
Thus the proof of *229 by mathematical induction is complete.
23. Relationship of P2 to P v  Though the constant / is absent from 
the system P2, we shall nevertheless be able to show the equivalence of the 
systems Px and P2 in a sense which involves using in P2 the wff r 
r (i.e., 
~[r io r]) to replace the constant / of Pv
Under the principal interpretations of Pl and P2l the constant / of 
and the 
wff r 
r of P,\n fact do not have the same meaning. For the former is a constant 
denoting f, while the latter is a singulary form which has the value f for every 
value of its variable- r. Nevertheless the two meanings sufficiently resemble 
each other that r cfc r can be used in Fa to serve many of the same purposes as 
might a constant denoting f.
If A is any wff of P2, then by a process of one-by-one replacement of the 
various wf parts ~C each in turn by C d  [r cj: r] we may obtain from A a 
wff Afl of P2 in which ~ does not occur otherwise than as a constituent in 
f c}: r. We may impose the restriction that, if 
is the special wff r dpr, 
the replacement of ~C by C r? [r c£ r] shall not be made. Then from a given 
wff A we obtain, by the process described, a unique wff A0, which we shall 
call the expansion of A with respect to negation. If then in A0 we replace r c£ r 
everywhere by /, we obtain a unique wff Af of Px which we shall call the 
representative of A  in Pv
We have the following metatheorems (proofs omitted when obvious):
*230. 
If B results from A by replacement of ~C by C 
[r c£ r] at one 
place in A, then A 1- B and B V A.

---


126
THE PROPOSITIONAL CALCULUS
[Chap. II
Proof. This follows from *229 and modus ponens because, by substitution 
in f220 and j-224,
1- ~C 10 « C 3  [r <£ r], 
b C 3  [r <£ r] 3  ~G.
*231. 
If Aq is the expansion of A with respect to negation, A bA^ and 
Aq I- A.
*232. 
If two wffs A and B of P2 have the same representative in Plf then 
A I- B and B I- A.
*233. 
If two wffs A and B of P2 have the same representative in Px, then 
( • A n B  and 1- B 3  A.
*234. 
A wff A of Pz is a theorem of P2 if its representative Af in Px is a 
theorem of Pv
Proof. Let A0 be the expansion of A with respect to negation. By *231, it 
is sufficient to prove that Aq is a theorem of P2 if A^ is a theorem of Pv 
Since A0 is
Si[f o
we proceed as follows.
We first observe that, if X is an axiom of P1( then
S-;r =. rjXi
is a theorem of P2. In fact, if X is f!02 or f 103, this is immediate by |202 and 
■[203; and if X is 1104, this follows by f22I and *23L 
If a proof of Af in P* is given in which the variable r does not occur, we 
replace / everywhere in this proof by ~[r 3  r]. The resulting sequence of 
wffs of P2 becomes a proof of A0 in P2 upon supplying the proof of
SU = r]X|
whenever necessary (this will be, as a matter of fact, whenever X is f 104).
If the variable r does occur in the given proof of Af in Pv we begin by 
selecting a variable a which does not occur and replacing r by a throughout. 
After that we proceed as before, i.e., we replace / everywhere by ~[r zo r], 
and then supply proof (in P2) of
I
wherever necessary. Then finally we use *201 to substitute r for a.
Employing the same truth-tables of 3  and ~ as those given in §15, we 
may define the value of a wff of P2 for a system of values of its variables, in 
the same way that we did in the case of a wff of Px. It is also possible, in the

---


§23] 
RELATIONSHIP OF THE TWO FORMULATIONS
127
same way as before, to cairy out the actual computation of the values of a 
wff for ail systems of values of its variables. And a wff of P2 is called a 
tautology if its value is t for all systems of values of its variables, a contra­
diction if its value is f for all systems of values of its variables.
**235. 
Every theorem of P2 is a tautology.
Proof. The three axioms of P2 are tautologies and the two rules of infer­
ence have the property of preserving tautologies. (Lf. the proof of **150.)
**236. 
If two wffs of P2 have the same representative in P*, then they have 
the same value for any system of values of the variables occurring 
in them.
Proof. By *233, **235, and the truth-table of id.
**237. 
A wff A of P2 is a tautology if and only if its representative A, in 
Pt is a tautology.
Proof. Let A0 be the expansion of A with respect to negation. Because the 
wff ~[r 
r] of P2 has always the value f, it follows that Aq is a tautology 
if and only if A, is a tautology. (For the full proof of this, the reader 
must supply an analogue of the lemma which was used in the proof 
of **150.) Therefore **237 follows by **236.
**238. 
A wff A of P2 is a theorem of P2 only if its representative Af in 
Pj is a theorem of Px.
Proof. If A is a theorem of P2, then by **235 it is a tautology. Therefore, 
by **237, Ar is a tautology. Therefore, by *152, A, is a theorem of
The sense in which we have equivalence of the systems P2 and l \  now 
appears in *234 and **238. Namely, in the correspondence of each wff of 
P2 to its representative in Px we have a many-one correspondence between 
the wffs of P2 and of Px such that theorems correspond to theorems and 
non-theorems to non-theorems. And this many-one correspondence satis­
fies the structural conditions that, if A, and Br are the representatives of 
A and B respectively, then Af id  B, is the representative of A id  B, and 
Af id / is the representative of ~A 202 (unless A is [r id r]).
*DaThe bare existence of a many-one correspondence, or even of a one-to-one corre­
spondence, between the wffs of Pj and of Pa, such th at theorems correspond to theorems
and non-theorems to non-theorems, might be demonstrated just on the ground that 
the theorems and the non-theorems are denumerably infinite classes both m the case 
of Pj and in the case of Pt. B ut without some added condition*, such as the structural 
conditions here stated, the bare existence of such a correspondence could hardly be 
said to constitute a significant equivalence of the two systems. We shall return m Chap­
ter X  to the question, what meaning is best given, in general, to the equivalence of 
two logistic systems.

---


128
THE PROPOSITIONAL CALCULUS
[Chap. II
From this equivalence between the two systems, together with **237, 
we have also the converse of **235:
*239. 
If a wff A of P2 is a tautology, I- A.
In **235 and *239, together with the algorithm for determining whether 
a wff is a tautology, we have a solution of the decision problem of P3. In 
this connection the reader should satisfy himself that the proof of *239 
(together with the proofs of preceding metatheorems on which it depends) 
directly provides an effective procedure to construct a proof of A in P2 if 
it has been verified that A is a tautology.
As in the case of P1( the consistency and completeness of P2, in the various 
senses discussed in Chapter I, now follow as corollaries of this solution of 
the decision problem.
Principles of duality for P2, analogues of *161, *164, *165, also follow in 
the same way as for Pr
EXERCISES 23
2 3 .0 . Let P2L be the logistic system which is identical with P2 except 
that the wffs are translated into the parenthesis-free notation of Lukasie­
wicz. State the primitive basis of P2L, and state and prove the analogues 
of **225-**227 for P2L. (Compare exercise 12.2, and footnote 91.)
2 3 .1 . By the methods of §19, discuss the independence of the axioms and 
rules of P2.
2 3 .2 . As a corollary of *229, prove the analogue of *159 (substitutivity 
of equivalence) for P2.
^3-3- Prove for P2 that every tautology is a theorem, by a method which 
parallels the proof of the corresponding metatheorem of Px as this is con­
tained in §§12-15, and which therefore avoids use of **226-*229.
2 3 .4 . According to our conventions, the expression il~p 
. q (£ pn ab­
breviates a certain wff of Px and a certain (different) wff of P2. Write each 
of these wffs without abbreviations other than omissions of brackets. For 
each wff, as thus written, carry out the computation of its values for all 
systems of values of its variables. Verify that corresponding values of the 
two wffs are always the same; and explain why this must be so in all such 
cases.
2 3 .5 . By analogy to §16, treat in detail the matter of duality in P2.
2 3 .6 - Let PF be the logistic system having the same primitive symbols and
wffs as P2, *200 and *201 as its rules of inference, and the six following 
axioms:

---


§24]
PRIM ITIVE CONNECTIVES
129
p zd , g zd p
s^>[p zd q]^>.szz>p^>msZDq 
p zz> \_q zd V] ZD u q zd * p zd r 
p zd g ZD . ~q ZD ~p 
~*"P ZD p
p=>~~p
(1) Prove 1204 as a theorem of PF, and thus establish that the theorems of 
Pjj are the same as those of P2. (2) Discuss the independence of the axioms 
of PF.
2 3 -7 - Let Pt be the logistic system having the same primitive symbols 
and wffs as P2, *200 and *201 as its rules of inference, and the single follow­
ing axiom:
Pl => [qx ZD pY] ZD l~ r ZD [p  ZD ~ s] ZD [Y ZD [p ZD g~\ ZD m s Z3 p ZD » S ZD q]
^  P%\ ^  ■ ?2 ^  Pl
Establish that the theorems of Pt are the same as those of P2 by showing 
(1) that the single axiom of PL is a tautology, and (2) that the axioms of 
P2 are theorems of Pt.
* 3 -8 . Establish the same result also for the logistic system P* which is 
like Pt except that the following (somewhat shorter) single axiom is used:
[p ZD ■ ~q ZD [r no s] ZD ,s ZD q ZD m pj zi mr ZD q] ZD [~qx ZD [qx ZD r x] ZD sx) ZD sx
2 3 .9 . 
Establish the same result also for the logistic system Ps, which 
is like PL except that the single axiom is the following:
rt ZD [p ZD g ID S ZD qx] 
[s^ ZD n S ZD P^ ZD * ^P ZD ~Y~\ ZD m Sj ID m S ZD p ZD ,r ZD p
(Make use of the result of exercise 18.4.)
2 4 . Primitive connectives for the propositional calculus. In P2
we used implication and negation as primitive connectives for the prop­
ositional calculus, and in Px we used implication and the constant /. We 
go on now to consider some other choices of primitive connectives (including, 
for convenience of expression, the constants as 0-ary connectives).
With one exception, we shall not consider connectives which take more 
than two operands. The exception is a ternary connective for which, when 
applied to operands A, B, C, we shall use the notation [A, B, Cj. We call 
this connective conditioned disjunction, and assign to it the following truth- 
table:203
ao9A convenient oral reading of *'[/>, q, /j"  is “/> or r according as q or not q."

---


130
THE PROPOSITIONAL CALCULUS
[Chap. II
p
?
r
i IP. 1  r]
t
t
t
! 
t
t
t
f
t
t
f
t
t
t
f
f
f
f
t
t
f
f
t
f
f
f
f
t
t
f
f
f
f
(It follows that the dual of {f, q, r] is [r, q, p] in the sense that the truth- 
table of 
q, r] becomes the truth-table of [r, q, p] upon interchanging t
and f.)
The singulary and binary connectives which we shall consider are those 
of §05,*°* with truth-tables as in §15. The constants are t and /, with values 
assigned as t and f respectively. If we include the truth-table
p 
!
p
t
t
f
f
it will be seen that all possible truth-tables are then covered (for connectives 
that are no more than binary), except those truth-tables in which the value 
in the last column is independent of one of the earlier columns.
When a number of primitive connectives are given, together with the 
usual infinite list of propositional variables, the definition of wff is then 
immediate by analogy with §§10, 20. And the value of a wff for each system 
of values of its variables is then given by a definition analogous to that of 
§15. It is clear that the values of a particular wff for all systems of values of 
its variables may be given completely in a finite table like the truth-table 
of a connective; we shall call this the truth-table of the wff.
A system of primitive connectives for propositional calculus will be called 
complete if all possible truth-tables of two or more columns205 are found among 
the truth-tables of the resulting wffs. And a particular one of the connectives
the sentence connectives of §05.
“ ‘Notice that a wff with one variable has a truth-table of two columns, a wff with 
two variables a truth-table of three columns, and so on. A wff with no variables has 
just one (fixed) value and may therefore be said to have a truth-table of just one column 
(and one row). In the definition of completeness we have purposely excluded one-col­
umn truth-tables because we wish to allow as complete not only such a system of 
connectives as implication and / but also, e.g., such a system as implication and nega­
tion.

---


PRIMITIVE CONNECTIVES
131
will be called independent if, upon suppression of that particular connective, 
its truth-table is no longer among the truth-tables of the resulting wffs—or 
in the case of a constant, t, or /, if upon suppression of it there is no longer 
among the resulting wffs any one which has the value t, or the value f, 
respectively, for all systems of values of its variables.
The problem of complete systems of independent primitive connectives 
for the propositional calculus has been treated systematically by Post.208 
We shall not make an exhaustive treatment here, but shall consider only 
certain special cases. We begin with the following:
Conditioned disjunction, t, and f constitute a complete syst&n of independent 
primitive connectives for the propositional calculus.
The completeness is proved by mathematical induction with respect to 
the number of different variables in a wff constructed from these connectives. 
Among the wffs containing no variables, it is clear that all possible systems 
of values are found, since the wff / has the value f, and the wff t has the value 
t. Suppose that among the wffs containing n variables all possible systems of 
values, i.e., all possible truth-tables, are found. And consider a proposed 
system of values for a wff containing n -f- 1 variables, i.e., a proposed 
(n -r 2)-column truth-table, T. Let the first column in the truth-table T 
be for the variable b. Let the truth-table Tx be obtained from T by deleting 
all the rows which have f in the first column and then deleting the first 
column. Let T2 be obtained from T by deleting all the rows which have t in 
the first column and then deleting the first column. By hypothesis of 
induction, wffs A and G exist whose truth-tables are Tt and T2 respectively. 
Then the wff [A, b, C] has the truth-table T, as may be seen by reference 
to the truth-table of conditioned disjunction. (Thus the completeness of 
the given system of primitive connectives follows by mathematical 
induction.)
The independence of conditioned disjunction is obvious, since without 
conditioned disjunction there would be no wffs except those consisting of a 
single symbol (/ or t or a variable).
The independence of t may be proved by reference to the last row in the 
truth-table of conditioned disjunction, since it follows from this last row 
that, if a wff is constructed from conditioned disjunction and / (without
ao,In his monograph, The Two-Valued Iterative Systems of Mathematical Logic (1941). 
For connectives which are no more than binary, there is a different treatm ent by 
William Wernick in the Transactions of the American Mathematical Society, vol. 51 
(1942), pp. 117-132.
Post deals also with the problem of characterizing the truth-tables which result from 
an arbitrary system of prim itive connectives (with assigned truth-tables).
§2£]

---


132
THE PROPOSITIONAL CALCULUS
[Chap. II
use of t), then it must have the value f when the value f is given to all its 
variables. In the same way the independence of / may be proved by reference 
to the first row in the truth-table of conditioned disjunction.
We may now prove completeness of other systems of primitive connectives 
by defining by means of the given primitive connectives (in the manner of 
§11) the three connectives, conditional disjunction, t, and /, and showing 
that the definitions give the value t to t, the value f to /, and the required 
truth-table to conditioned disjunction. Thus the completeness of implication 
and / follows by D1 (see §11) and the definition;
D12. 
[A, B, C] -» [B =3 A][~B =3 C]
In the case of systems of primitive connectives which do not include 
constants, it is not possible to give definitions of t and /. But in proving 
completeness it is sufficient instead to give an example of a wff which has 
the value t for all systems of values of its variables, i.e., which is a tautology, 
and an example of a wff which has the value f for all systems of values of its 
variables, i.e., which is a contradiction. Thus the completeness of impli­
cation and negation follows by D 12 above (as reconstrued when implication 
and negation are the primitive connectives) together with any example of 
a tautology, say r d  r, and any example of a contradiction, say r 
r.
In each of the systems, implication and /, implication and negation, the 
independence of the second connective follows because no wff constructed 
from implication alone can be a contradiction (as we may prove by mathe­
matical induction, using the truth-table of implication). The independence 
of implication is in each case obvious because of the very restricted class of 
wffs which could be constructed without implication. Thus:
Each of the systems, implication and f, implication and negation, is a com­
plete system of independent primitive connectives for the propositional calculus.
Having this, we may now also prove completeness of a system of primitive 
connectives by defining either implication and / or implication and negation, 
and showing that the definitions give the required truth-tables (and, if / 
is defined, that they give the value f to /).
In particular the completeness of negation and disjunction follows by 
the definition of [ A d B] as - A  v B. And the completeness of negation 
and conjunction follows by the definition of [Ad B] as~[A  ~B], Independ­
ence may be proved in each case in a manner analogous to that in which the 
independence of implication and negation was proved. Thus:
Each of the systems negation and disjunction, negation and conjunction, is

---


§24]
PRIM ITIVE CONNECTIVES
133
a complete system of independent primitive connectives for the propositional 
calculus.
We leave to the reader the proof of the following;
Implication and converse non-implication constitute a complete system of 
independent primitive connectives for the propositional calculus.
This last system of primitive connectives has, like the system consisting 
of conditioned disjunction, t, and f, the substantial advantage of being self- 
dual in the sense that the dual of each primitive connective either is itself 
a primitive connective or is obtained from a primitive connective by 
permuting the operands. Indeed it is clear that a treatment of duality, 
like that of §16 for P1; would be much simpler in the case of a formulation 
of the propositional calculus based on a self-dual system of primitive 
connectives.
Of the two self-dual systems of primitive connectives suggested, that con­
sisting of implication and converse non-implication has the disadvantage 
that it is impossible to make a definition of negation which is self-dual in 
the sense that the dual of -A  is ~Alt where Aj is the dual of A. Therefore it 
becomes necessary (for convenience in dualizing) to make two definitions of 
negation which are duals of each other. Then, if the symbols ~ and — are 
used for the two negations, the dual of ~A will be —AXJ where Ax is the dual 
of A.
The self-dual system consisting of conditioned disjunction, t, and /, does 
not have this disadvantage. But it does have the obvious disadvantages 
associated with the use, as primitive, of a connective which takes more than 
two operands.
For this reason it has sometimes been suggested that the requirement of 
independence be abandoned in the interest of admitting a more convenient 
self-dual system of primitive connectives. In particular the system consisting 
of negation, conjunction, and disjunction has been proposed. Another possi­
bility, of course, is negation, implication, and converse non-implication.
For certain purposes there are advantages in a complete system of primi­
tive connectives which consists of one connective only, although to obtain 
such a system it is necessary to make a rather artificial choice of the primi­
tive connective (and also to abandon any requirement of self-duality if 
the primitive connective is to be no more than binary). We leave to the 
reader the proof of the following:207
107The possibility of a single prim itive connective for the propositional calculus was 
known to C. S. Peirce, as appears from a fragment, w ritten about 1880, and from

---


134
THE PROPOSITIONAL CALCULUS
[C h a p . II
Non-conjunction, taken alone, constitutes a complete system of primitive 
connectives for the propositional calculus. Likewise non-disjunction alone. These 
are the only connectives which are no more than binary and which have the 
property of constituting a complete system of primitive connectives for the 
propositional calculus when taken alone.
EXERCISES 24
2 4 .0 * Taking conditioned disjunction, 
and / as primitive, give defini­
tions of all the singulary and binary connectives. Select the simplest pos­
sible definitions, subject to the conditions that definitions of mutually dual 
connectives shall be dual to each other and that the definition of negation 
shall be self-dual.
24.1. Taking implication and converse non-implication as primitive, give 
definitions of the singulary and remaining binary connectives. Select the 
simplest possible definitions, subject to the condition that definitions of 
mutually dual connectives shall be dual to each other. As indicated in the 
text, supply definitions of two negations dual to each other.
2 4 .2 . With conditioned disjunction, t, and / as primitive, assume that a 
formulation of the propositional calculus has been given such that every 
theorem is a tautology and every tautology is a theorem. Supply for this 
formulation of the propositional calculus a treatment of duality, analogous 
to that of §16 for Pr Discuss first the dualization of wffs proper, and then
Chapter 3 of his unfinished Minute Logic, dated January-February 1902. These were 
unpublished during Peirce's lifetime, but appeared in 1933 in the fourth volume of his 
Collected Papers (see pp. 13-18, 215-216 thereof). First publication of the rem ark that 
the propositional calculus may be based on a single primitive connective was by 
H. M. Sheffer in a paper in the Transactions of the American Mathematical Society, vol. 
14 (1913), pp. 481-488.
The analogous remark for Boolean algebra is that the usual Boolean operations may 
be based on a single primitive operation, for which two choices, dual to each other, are 
possible. Both of these operations are used together by Edward Stamm as a self-dual 
system of primitive operations for a postulational treatm ent of Boolean algebra, in a 
paper in Monatshefie fur Mathematik und Physik, vol. 22 (1911), pp. 137-149. The ex­
plicit basing of Boolean algebra on a single primitive connective first appears in Sheffer's 
paper of 1913 (there is also some suggestion of this in Peirce's unpublished fragment of 
1880).
Peirce's notations, which are his two alternative single primitive connectives for 
the propositional calculus, have not been used by others and need not be reproduced 
here. Sheffer uses the sign of disjunction, v, inverted as a sign of non-disjunction; he 
introduces non-conjunction only in a footnote and uses no special sign for it. The 
vertical line, since called Sheffer's stroke, was used by Sheffer only in connection with 
Boolean algebra; its use as a sign of non-conjunction was introduced by J. G. P. Nicod 
in the paper which has his single axiom for the propositional calculus, discussed in the 
next section (cf. Proceedings of the Cambridge Philosophical Society, vol. 19 (1917-1920), 
pp. 32-41).

---


§24]
EXERCISES 24
135
also the duaiization of expressions that are abbreviations of wffs under the 
definitions of 24.0.
24*3* Show that equivalence, disjunction, and / constitute a complete 
system of independent primitive connectives for the propositional calculus. 
(Compare exercise 15.7, and footnote 186.)
2 4 .4 . In each of the following systems of primitive connectives for the 
propositional calculus, demonstrate the independence of the connectives: 
(1) negation and disjunction; (2) negation and conjunction; (3) implication 
and converse non-implication.
2 4 *5 * Taking non-conjunction as the only primitive connective, give 
definitions of the singulary and remaining binary connectives. Neglecting 
considerations of duality, select the definitions in which the definiens is 
shortest (when written out in full, in terms of the primitive connective).
2 4 *6 . Show that equivalence and non-equivalence do not constitute a 
complete system of primitive connectives for the propositional calculus. 
Determine all possible ways of adding to the list one or more connectives 
which are no more than binary, so as to obtain a complete system of inde­
pendent primitive connectives for the propositional calculus.
2 4 .7 - It may happen that a complete system of primitive connectives for 
the propositional calculus, though all are independent, is capable of being 
reduced without loss of completeness by replacing one of the connectives by 
a connective which can be defined from it alone and takes fewer operands than 
it does. For this purpose, any tautology is to be treated as if it supplied a 
definition of /, and any contradiction a definition of /, though these are not 
definitions in the proper sense (cf. the remark in the text on this point). 
When a complete system of independent primitive connectives for the prop­
ositional calculus is not capable of being reduced in this way, it is a spe­
cialized system of primitive connectives for the propositional calculus, in the 
sense of Post. Of the various complete systems of independent primitive 
connectives for the propositional calculus which are mentioned in the text, 
determine which are specialized systems. Of those which are not, supply all 
possible reductions to specialized systems.
24.8. Do the same thing for each of the complete systems of independent 
primitive connectives found in 24.6.
2 4 .9 . Consider a formulation of the propositional calculus in which the 
primitive connectives are negation, conjunction, and disjunction. A wff B 
which contains n different variables is said to be in full disjunctive normal 
form if the following conditions are satisfied: (i) B has the form of a dis­
junction Cj v C2 v . . . v Cm; (ii) each term Cf of this disjunction has the

---


136
THE PROPOSITIONAL CALCULUS
rcHAP. ii
form of a conjunction, 
. . . Gin; (iii) each Ga  (t =  1, 2 ,. . 
m and
k  =  1, 2, .. 
n ) is either b* or 
where bfc is the k t h  of the variables 
occurring in B, according to the alphabetic order of the variables (§20); 
(iv) the terms G* are all different and are arranged among themselves accord­
ing to the rule that, if C i v  Ct2, , . 
are the same as CA, C,a,
. • 
G ^^, respectively, and Cf* is b k, and G^ is ~bfc( then i <  j . Introduce
material equivalence by an appropriate definition, and let a wff B be called 
a f u l l  d is ju n c t iv e  n o r m a l f o r m  o f a wff A if B is in full disjunctive normal form 
and contains the same variables as A does and A =  B is a tautology. Show 
that every wff not a contradiction has a unique full disjunctive normal 
form; and by means of the two laws of De Morgan (cf. 15.8) and commuta­
tive, associative, and distributive laws involving conjunction and dis­
junction {cf. 15.5,15.7, 15.8), show how to reduce the wff to full disjunctive 
normal form. Show that a wff is a tautology if and only if it has a full 
disjunctive normal form in which m  =  2n.
2 4 .IO. 
For a formulation of the propositional calculus in which the primi­
tive connectives are conditioned disjunction, t , and /, we may define n o r m a l
f o r m  as follows, by recursion with respect to the number of different variables 
which a wff contains: a wff containing no variables is in normal form if and 
only if it is one of the two wffs, t t /; a wff in which the distinct variables 
contained are, in alphabetic order, bl, ba, . .
bn is in normal form if and 
only if it has the form [A, bn, G], where each of the wffs A and C contains 
all of the variables b^ b2, .. 
bn_lf does not contain bn, and is in normal 
form. For this case establish a result about reduction to normal form, 
analogous to that of exercise 24.9 for reduction to full disjunctive normal 
form in the case of negation, conjunction, and disjunction as primitive 
connectives.
25. Other formulations of the propositional calculus. Formulations
of the propositional calculus so far considered, in the text and in exercises, 
have been based either on implication and / or on implication and negation 
as primitive connectives. We go on now to describe briefly some formulations 
based on other primitive connectives.
Very well known is the formulation, PR, of the propositional calculus 
which is used in P r i n c i p i a  M a t h e m a i i c a , In this the primitive connectives 
are negation and disjunction. The rules of inference are substitution and 
m o d u s  p o n e n s (the latter in the form, from ~A v B and A to infer B). The 
axioms are the five following, in which A ro B is to be understood as an 
abbreviation of ~A v B;

---


§25]
OTHER FORMULATIONS
137
p V p Z D p  
q z D  p y  q 
p  v q z D  q v  p  
p  v [q v r] z d q v [ p  v r \  
q z d y z d  mp v  q z d p  v r
Several reductions of this sytem have been proposed. Of these the most 
immediate is the system PB obtained by just deleting the fourth axiom, 
which is, in fact, non-independent. Another is the system PN in which the 
five axioms are replaced by the following four axioms:
p v p Z D p
p Z D  p v  q
P v [q v r] z d q v [ p v r] 
q Z D Y Z D * p V q Z D p V Y
Still another is the system PG in which the five axioms are replaced by the 
following three:
£ V p ZD p 
p zd pv q
q  z d y  z d mp y  q z D  y  v  p
For some purposes there may be advantages in a formulation of the prop­
ositional calculus which is based on only one primitive connective, only 
one axiom, and besides substitution only one rule of inference, although in 
order to accomplish this it is necessary to make a rather artificial selection 
of the primitive connective and to allow the single axiom to be relatively 
long. As long as the procedure in constructing a logistic system is regarded 
as tentative, with the choice held open as to what assumptions (in the form 
of axioms or rules) will finally be accepted—or if the emphasis is upon fixing 
the ground of theorems and metatheorems in the sense of distinguishing 
what assumptions each one rests upon —the preference will be for natural­
ness in the selection of primitive connectives and for simplicity in the individ­
ual axioms and rules, rather than for reduction in their number. On the 
other hand the proof of desired metatheorems may well be simplified in 
some cases by the contrary course of reducing the number of primitive 
connectives, axioms, and rules, even at the expense of naturalness or sim­
plicity; and a metatheorem, once proved for one formulation, may perhaps 
be extended to other formulations by establishing equivalence of the for­
mulations (in some appropriate sense).
For the propositional calculus, a formulation of the proposed kind was 
first found by J. G. P. Nicod. His system, call it P n, is based on non-conjunc­

---


138
THE PROPOSITIONAL CALCULUS
[Chap. II
tion as the primitive connective. The rules of inference are substitution and 
the rule; from A | . B | C  and A to infer C, The single axiom is:
P I [? I r] I ■ P i I [P i I P li I ■ s I ?1 ■ P I s I ■ P I s
In another such formulation of the propositional calculus, P w, the prim­
itive connective and the rules of inference are the same as in Pn, and the 
single axiom is the following:
P I fa I r] I ■ 0 J r I ■ P I S I • P I s] I ■ P I ■ P I ?
(This axiom, unlike Nicod's, is organic, in the sense of Wajsberg and Le- 
Sniewski, i.e., no wf part shorter than the whole is a tautology.)
In still another such formulation of the propositional calculus, PL, the 
primitive connective and the rules of inference are still the same as in Pn, 
and the single axiom is:
P I fa I r] | . p | [r I p] | . s | q | . p | s | . p | s 
(This axiom is closer to Nicod’s, and still organic.)
EXERCISES 25
25.0. Establish the sufficiency of PR for the propositional calculus by 
carrying the development of the system far enough, either to prove directly 
that a wff is a theorem if and only if it is a tautology, or to show equivalence 
to P2 in a sense analogous to that of §23. (To facilitate the development, the 
derived rule should be established as early as possible, that if M, N, A, B 
satisfy the conditions stated in *229, and if b M id N and F N d  M, then 
h A zd B and b B => A.)
Establish the sufficiency of PB for the propositional calculus by 
proving the fourth axiom of PR as a theorem.
25.2. Discuss the independence of the axioms and rules of PB.
25*3* Establish the sufficiency of PN for the propositional calculus by 
proving the second and third axioms of PR as theorems.
Discuss the independence of the axioms and rules of PN.
Establish the sufficiency of PG for the propositional calculus by 
proving the axioms of PR as theorems. (The chief difficulty is to prove the 
theorem p 
p. For this purpose, following H. Rasiowa, we may first prove 
in order the theorems p id  
q v  p zd .~ p  zd q, 
* ~~~p id  ~p, ~p v . 
p v 
~ ~ \ p  r> r] r > . s v [q v p] r> r  v q v s.)
25.6. Discuss the independence of the axioms and rules of PG.
*5-7- Establish the sufficiency of Pn for the propositional calculus by 
showing its equivalence to PR in a sense analogous to that of §23.

---


§25]
EXERCISES 25
139
25.8. Establish the sufficiency of Pn for the propositional calculus, with­
out use of PR, by showing its equivalence to P2 in a sense analogous to that 
Of §23,
2 5 .9 . Discuss the independence of the axioms and rules of Pn, (This 
question can be answered by means of immediately obvious considerations, 
without use of truth-tables or generalized systems of truth-values in the 
sense of §19.)
25.10. By the method of §19 or otherwise, determine whether Pn remains 
sufficient for the propositional calculus when its second rule of inference is 
weakened to the following: from A  | . B  | B  and A  to infer B .
25.11. Establish the sufficiency of Pw for the propositional calculus by 
proving the axiom of Pn as a theorem.
25.12. Establish the sufficiency of PL for the propositional calculus.
25.13.208 (1) Given implication and converse non-implication as primitive
connectives, and substitution and modus ponens as rules of inference, find 
axioms so that the resulting system is sufficient for the propositional cal­
culus. Seek, as far as feasible, to make the individual axioms simple, and 
after that to make their number small. (2) Establish the independence of 
the axioms and rules.
25.14. 
** Given negation, conjunction, and disjunction as primitive con­
nectives, find axioms and rules of inference so that the resulting logistic 
system is sufficient for the propositional calculus. In doing so, make the 
system of axioms and rules of inference self-dual in such a sense that a meta­
theorem analogous to *161 (principle of duality) follows immediately there­
from. Subject to this condition seek, as far as feasible, to make the individual 
axioms and rules simple, and after that to make their number small. Can 
the axioms and rules be made independent without excessive complication 
or loss of the feature of self-duality?
25.15. 
** Answer the same questions if the primitive connectives are con­
ditioned disjunction, t, and /.
2 5 .1 6 . 
** Let the primitive connectives be conditioned disjunction, 
and /. Let the rules of inference be the rule of substitution and the following 
rule: from (A , B , C ] and B  to infer A . Find axioms so that the resulting 
system is sufficient for the propositional calculus. Seek, as far as feasible, 
to make the individual axioms simple, and after that to make their number 
small. (Ignore the matter of duality.)
*0BThis is offered as an open problem for investigation, rather than as an exercise m
the ordinary sense. The w riter has not attem pted to find a solution.

---


140
THE PROPOSITIONAL CALCULUS
[Chap. II
26. Partial systems of propositional calculus. We have so far
emphasized the matter of logistic systems adequate to the full propositional 
calculus, in the sense of being equivalent in some appropriate sense to 
or 
P2. Studies have also been made, however, of various partial systems, not 
adequate to the full propositional calculus, and in this section we shall 
describe briefly some of these.
One sort of partial system of propositional calculus is based on an in­
complete system of primitive connectives, axioms and rules being so chosen 
that the theorems coincide with the tautologies in those connectives. An 
example is the implicational propositional calculus, which has implication as 
its only primitive connective, and which is formulated by (e.g.) either the 
logistic system 
of exercise 18.3 or the system P£ of 18.4. Other examples 
will be found in the exercises following this section.
The chief interest of partial systems of this sort would seem to be as step­
ping-stones toward formulations of the full propositional calculus. For 
example, the result of exercise 18.4, together with that of 12.7, leads to a 
formulation P^ of the propositional calculus in which the primitive connec­
tives are implication and /, the rules of inference are modus ponens and sub­
stitution, and the axioms are the two following:
p z j q z D r z D mr z D p Z D ms^>p
f z o p
The foregoing formulation of the full propositional calculus is elegant for 
its brevity, and sharply separates out the role of the constant / from that of 
implication, but fails to separate from one another what may be regarded 
as different assumptions about implication. If we wished to separate from 
the others those properties of implication which are involved in the deduc­
tion theorem, we might begin with the logistic system P+ of exercise 19.6 
(or an equivalent)—the positive implicational propositional calculus of 
Hilbert—and add primitive connectives and axioms to obtain a formulation 
of the full propositional calculus.
Akin to the positive implicational propositional calculus is the positive 
propositional calculus of Hilbert, designed to embody the part of the prop­
ositional calculus which may be said to be independent in some sense of 
the existence of a negation. This may be formulated as a logistic system Pp, 
as follows. The primitive connectives are implication, conjunction, disjunc­
tion, and equivalence (which then are not independent, even as primitive 
connectives for this partial system of propositional calculus). The rules of 
inference are modus ponens and substitution. And the axioms are the

---


§26]
PARTIAL SYSTEMS
Ul
eleven following:
p 
mqzD p
s zd [p zd q]-^>ms=)pZD.s=)q 
PqZDp 
i>q=>q 
pZD .q=>pq 
pZD p v q 
q 3  p v q
p zd r ZD- MqZD?ZDmpvq-^>r 
P =  q=> .p=>q 
p - q Z D . q z ^ p  
p Z D q Z D m q n p Z D m p ^ q
The system Pp may be extended to a formulation of the full propositional 
calculus by adding negation as a primitive connective and one or more 
suitably chosen axioms involving negation. We may for example use f204 as 
a single additional axiom, so obtaining a formulation of the propositional 
calculus which we shall call PH.
On the other hand by adding to 
a weaker axiom or axioms involving 
negation we may obtain a formulation of the intuitionistic propositional 
calculus of Heyting.200
The mathematical intuitionism of L. E. J. Brouwer will be discussed in 
Chapter XII. On grounds to be explained in that chapter, it rejects certain 
principles of logic which mathematicians have traditionally accepted without 
question, among them certain laws of propositional calculus, especially the 
law of double negation and the law of excluded middle. (Of course this in­
volves also rejection of such an interpretation of propositional calculus as 
that of §10 or §20, not perhaps in itself but in the light of the actual use of 
the propositional calculus as a part of a more extensive language.)
Heyting's logistic formalization of the ideas of Brouwer (accepted by 
Brouwer) gave them a precision which they otherwise lacked, and has played 
a major role in subsequent debate of the merits of the intuitionistic critique 
of classical mathematics. For the intuitionistic propositional calculus we 
adopt not Heyting's original formulation but the following equivalent 
formulation Tls.
The primitive connectives of Pg are implication, conjunction, disjunction, 
equivalence, and negation. The rules of inference are modus ponens and
*°*Arend Heyting in StUungsberichte der Pveussischen Akademie der Wissenschaften, 
Physikalisch-mathematische Klasse, 1030, pp. 42-56.

---


142
THE PROPOSITIONAL CALCULUS
[Chap. II
substitution. The axioms are the eleven axioms of Pp and the two following 
additional axioms:
p zd <~p zz$ ~p 
(Special law of reductio ad absurdum.)
~p zd mp zd q 
(Law of denial of the antecedent.)
The minimal propositional calculus of Kolmogoroff and Johansson810 
makes a more drastic rejection of classical laws involving negation. A for­
mulation of it, P“, may be obtained from Pg by replacing the two foregoing 
axioms by the single axiom:
pZDq^>, pZD~qZD~p 
(Law of reductio ad absurdum.)
Wajsberg has shown211 that any theorem A of Pg can be proved from the 
first two of the thirteen axioms together with only those axioms which 
contain the connectives, other than implication, actually appearing in A. 
As a corollary the same thing may be shown also for P”. It follows that those 
theorems of the intuitionistic propositional calculus Pg, or of the minimal 
propositional calculus P“, which do not contain negation are identical with 
the theorems of the positive propositional calculus; further, that those 
theorems of any one of the three systems in which implication appears as 
the only connective are identical with the theorems of the positive implica- 
tional propositional calculus.
The decision problem of Pg has been solved by Gentzen, and again by 
Wajsberg.218 By the results referred to in the preceding paragraph, solution 
of the decision problem follows for Pp and P+. And by the result of 
exercise 26.19 (2), solution of the decision problem follows also for P”. * *
*10A. Kolmogoroff in R e c u e il M a th d m a tiq u e  de la  S o c ii ti M a th im a tiq u e  de M o s c o u , 
vol. 32 (1024-1925), pp. 646-667, and Xngebrigt Johansson in C o m p o sitio  M a th e m a tic a l 
vol. 4 (1936), pp. 119-136. See also the paper of Wajsberg cited in the next footnote.
Kolmogoroff considers prim arily not the full minimal calculus but the part of it 
obtained by suppressing the three primitive connectives, conjunction, disjunction, 
equivalence, and the axioms containing them (and finds for this calculus a similar 
result to th at later found by V. Glivenko, quoted in exercise 26.15, for the intuitionistic 
propositional calculus). Addition of the three axioms for disjunction which are given in 
the text is mentioned by Kolmogoroff in a footnote, but the full minimal calculus and 
the name (“ minimal calculus" or “ Minimaikalkul") first occur in Johansson's paper. 
Kolmogoroff uses for implication not the two axioms in the text but four axioms taken 
from Hilbert th at are equivalent to these; and he takes the three axioms for disjunction 
from Ackermann. Johansson uses Heyting's axioms (from the paper cited in footnote 
209), suppressing one of those for negation,
*n Mordchaj Wajsberg in W ia d o m o lc i M a te m a ty c zn e , vol. 46 (1938), pp. 46-101.
m Gerhard Gentzen in M a th e m a tisc h e  Z e itsc h rift, vol. 39 (1934), pp. 176-210, 405-431. 
Wajsberg, lo c x it. Other decision procedures for the intuitionistic propositional calculus 
are due to J. C. C. McKinsey and Alfred Tarski in T h e  J o u r n a l o f S y m b o lic  L o g ic, vol. 13 
(1948), pp. 1-15, to Ladislav Rieger in A d a  F a c u lta tis  R e tu r n  N a tu r a liu m  U n iv e r s i- 
ta tis C a ro lin a e, no. 189 (1949), and to B. ti, Pil'Cak in the D o k la d y  A ka d & m ii N a u k  
S S S R , vol. 75 (1950), pp. 773-776.

---


§26]
EXERCISES 26
143
EXERCISES 26
26.0. Let P^, be the partial system of propositional calculus based on 
equivalence as the only primitive connective, the rules of inference being 
substitution and the rule, from A =  B and A to infer B, and the axioms 
being the two following:
p =  q s . q  =  p 
p = [ q  =  r ] = = . p = = q = = r
Prove the following theorems of P^:
p =  p ^ q = ~ q  
p ~ p
p ~ q ^ * r ~ mp ~ mq ~ r
Pi =  9i “  ■ Pz s  ?2 ^  
— P i =  • #1 =  #2
(The order in which the theorems are given is one possible order in which 
they may be proved. Heuristically, solution of 26.0 and 26.2 may be facili­
tated by noticing that the given axioms are the complete commutative and 
associative laws of equivalence.)
26.x. Hence prove the followingmetatheorem of P^( by a method anal­
ogous to that of the proof of *229: If B results from A by substitution of N 
for M at zero or more places (not necessarily at all occurrences of M in A), 
and if 1- M =  N, then 1-A =  B.
2 6 .2 . Hence prove that a wff of P;^ is a theorem if and only if every 
variable in it occurs an even number of times.213 Hence the theorems of P^ 
coincide with the tautologies in which equivalence appears as the only 
connective.
26.3. (I) Let P® be the system obtained from P^ by replacing the 
two axioms by the following single axiom:
Prove that the theorems of P^ are identical with those of P^.
(2) Let P f be the system obtained fTom P^ by replacing the two axioms 
by the following single axiom:
,wThis solution of the decision problem of the equivalence calculus is due to LeSniew* 
ski. Notice its relationship to 15.7.

---


144
THE PROPOSITIONAL CALCULUS
[Chap. II
q =  r ~  ^ p ~  q =  - r  =  p
Prove that the theorems of Pf are identical with those of P^.
(3) 
Following Lukasiewicz, use the result of 26.2 and the method of §19 
to show that no shorter single axiom can thus replace the two axioms of P^.
26.4. Let PEN be the system obtained from P j  by adjoining negation as 
an additional primitive connective, and one additional axiom;
~p = ~ q =  . p  =  q
In a sense analogous to that of §23, demonstrate equivalence of PEN to 
the system PE/ obtained from P^ by adjoining / as an additional primitive 
symbol, and no additional axioms—negation being defined thus in PE/:
~ A  
A  == /
Hence prove that a wff of PEN is a theorem if and only if every variable in it 
and the sign -  occur each an even number of times (if at all).214 Hence the 
theorems of PEN and of PE/ coincide with the tautologies in equivalence 
and negation, and in equivalence and /, respectively.
26.5. Show that the system PEN is not complete in the sense of Post, 
since the wff p =  
can be added as an axiom without making the wff p 
a theorem.215
26.6. A partial system of propositional calculus is to have equivalence 
and disjunction as primitive connectives, and, besides the rule of substitu­
tion, the two following rules of inference: from A  and A  =  B to infer B; 
from A  to infer A  v B .216 (1) Find axioms such that the theorems coincide 
with the tautologies in equivalence and disjunction. (2) With the aid of any 
previous results proved in the text or in exercises, show that the system (as 
based on these axioms) is complete in the sense of Post. (3) Discuss also the 
independence of the axioms and rules of inference.
2 6 .7 . Making use of results already found for P2 (so far as they apply), 
show that a wff of PH is a theorem if and only if it is a tautology.
2 6 .8 . (1) Establish the independence of p 
. q 
p as an axiom of PH 
by means of the following truth-tables, in which 0 and 1 are the designated 
truth-values: *
*uThis solution of the decision problem of the equivalence-negation calculus is due 
independently to McKinsey and Mihailcscu. as a corollary of LeSniewski's solution of 
the decision problem of the equivalence calculus: see The Journal of Symbolic Logic, vol. 
2, p. 175, and vol. 3, p. 55. Here again the relationship to 15.7 should be noticed.
m Eugen Gh. Mihailcscu in Annates Scientifiques de VUnxversiU de Jassy, part l, 
vol 23 (1937), pp. 369-408, iv.
m These two rules are used by M. H. Stone in American Journal of Mathematics,
vol. 59 (1937), pp. 506-514.

---


§26]
EXERCISES 26
145
p
9
p => ?
Pq
f s q
p =  q
0
0
0
1
1
1
3
0
1
1
1
1
1
0
2
2
4
1
4
0
3
2
4
1
4
0
4
4
4
1
4
1
0
0
1
1
1
2
1
1
l
1
1
1
1
2
2
4
1
4
1
3
2
4
1
4
1
4
4
4
1
4
2
0
0
4
1
4
3
2
1
1
4
1
4
2
2
0
4
4
1
2
3
0
4
4
4
2
4
1
4
4
1
3
0
2
4
1
4
3
3
1
1
4
1
4
3
2
2
4
4
4
3
3
2
4
4
4
3
4
1
4
4
1
4
0
0
4
1
4
0
4
1
1
4
1
4
4
2
0
4
4
1
4
3
0
4
4
1
4
4
1
4
4
1
(2) By a modification of these truth-tables establish also the independence 
o i p ’z > mq z 3 pBSzn axiom of Pg. {Suggestion: In both parts (1) and (2), in 
order to minimize the labor of verifying tautologies mechanically, make 
use as far as possible of arguments of a general character.)
2 6 .9 . Discuss the independence of the remaining axioms (1) of the 
system PH, and (2) of the system Pj.
26.10. Consider a system of truth-values 0, 1, . . .,v with 0 as the only 
designated truth-value, and the following truth-tables of the connectives of 
P*s; the value of p 3  q is 0 if the value of p is greater than or equal to the 
value of q, and in the contrary case it is the same as the value of q\ the value 
of pq is the greater of the values of p and q\ the value of p v q is the lesser of

---


146
THE PROPOSITIONAL CALCULUS
[Chap. II
the values of p and q\ the value of p s  q is 0 if the values of p and q are the 
same, and in the contrary case it is the greater of the values of p and q\ 
the value of ~p is 0 if the value of p is v, and in all other cases the value of 
~p is v. Show that all theorems of Ps are tautologies according to these 
truth-tables.
2 6 . 1 1 . 
Hence show that the following are not theorems of P^: the law 
of double negation; the law of excluded middle; the converse law of contra­
position; and the law of indirect proof,
~p r> q 
. ~p 
z> p.
26.12. Following Kurt Godel, use these same truth-tables to show that
IA =  Pzl v £Pi s  A] v . . . v [A =  pn]
v f e  =  W
v ^ s ^ 4] v . . . v [ ^  =  ^ ] v ...............V [p n,_x =  p n]
is not a theorem of Pg (for any «), also that this wff becomes a theorem 
of Pg upon identifying any two of its variables (by substituting one of the 
variables everywhere for the other}, and hence finally that there is no system 
of truth-tables in finitely many truth-values such that under it not only are all 
theorems of Pg tautologies but also all tautologies are theorems of Pg.217
2 6 . 1 3 . 
With the aid of the deduction theorem (which can be demon­
strated for Pg in the same way as for P2), show that the following are theo­
rems of Pi:
pz DqZD. pZD~qz D~p  
(Law of reductio ad absurdutn.)
p-z>~~p 
(Converse law of double negation.)
~~~p zd ~p 
(Law of triple negation.)
p zd y D  m~q =3 ~p 
(Law of contraposition.)
~ ~ m p v ~ p  
(Weak law of excluded middle.)
~ 9p ~p 
(Law of contradiction.)
26.14. Let Pr be the system obtained by adjoining the law of excluded 
middle, p v ~p, to Pg as an additional axiom. Prove |204 as a theorem of 
Pr . Hence show that the theorems of Pr are the same as the theorems of 
PH—therefore, by the result of 26.7, that the theorems of Pr  are the same as 
the tautologies (according to the usual two-valued truth-tables, §15).
26.15. Using the results of 26.13 and 26.14, establish the following results *
*,7Stanislaw Jankowski has constructed a system of truth-tables in infinitely many 
truth-values which is such that under it the tautologies coincide with the theorems of 
the intuitionistic propositional calculus (i.e., which, in the terminology of McKinsey, 
is characteristic for the intuitionistic propositional calculus). See Acies du Congres Inter­
national de Philosophie Scientifique, Paris 1935 (published 1936), part VI, pp. 58-61.
(Added in proof. See further a paper by Gene F. Rose in the Transactions of the 
American Mathematical Society, vol. 75 (1953), pp. 1-19.)

---


§26]
EXERCISES 26
147
of V. Glivenko: If a wff A of Pls is a tautology according to the usual two­
valued truth-tables, then 
is a theorem of Pg. A wff ~A of Pg is a theo­
rem of Pg if and only if it is a tautology according to the usual two-valued 
truth-tables.
2 6 . 1 6 . As a corollary of the results of 26.15, establish also the following 
result of Godel:218 A wff A of Pg in which conjunction and negation are the 
only connectives appearing is a theorem of Pls if and only if it is a tautology 
according to the usual two-valued truth-tables.
2 6 . 1 7 . Discuss the independence of the axioms of Pr (exercise 26.14), 
showing in particular that the axiom p id ~p z> 
is non-independent.
2 6 . 1 8 . Let Pg be the system obtained from Pg by replacing the axiom 
P 
~p 
~p by the two following axioms:
~ m p * **p
p ro q =3 m~q Z> ~p
(1) Show that the theorems of Pg are the same as those of Pg. (2) Show that 
the theorems of Pg which can be proved without use of the axiom ~ p i}  mp ^ q  
are the same as the theorems of P®. (3) Discuss the independence of the 
axioms of Pg.
2 6 . 1 9 . Let P!w be the system obtained from Pp by adjoining / as an 
additional primitive symbol and / id p as an additional axiom. Let F f be 
the system obtained from Pp by adjoining / as an additional primitive 
symbol and no additional axioms. Show that *229 is valid as a 
metatheorem of P*s, and of P“ . (1) Hence establish the equivalence of Pg 
and P*w in the sense of §23. (2) Likewise establish the equivalence of P“ 
and Pj1 in the sense of §23 219
2 6 .2 0 . Establish the following result (substantially that of Kolmogoroff 
referred to in footnote 210): In any theorem of the full propositional calculus 
P2—in which the connectives occurring are only implication and negation— 
let every variable a be replaced throughout by its double negation 
a. 
The resulting formula is a theorem of the minimal calculus PJ1.
2 6 .2 1  • Establish the equivalence of PJ1 and the system P™ obtained from 
it by replacing its last axiom (the law of reductio ad absurdum) by the axiom 
p =3 ~q zd . q ro ~p.
2 6 .2 2 . For the system Pp, show that implication is definable from con­
*u See G livenko's paper cited in footnote 271, and a paper by GOdel in E rg e b n isse  
etnes Mathematiscken Kolloquiums, no. 4 (1933), pp. 34-38.
ai#This result regarding the m inim al calculus was found by Johansson, loc.ctt.; and 
later by W ajsberg, loc.cit, for Kolmogoroff's m inim al calculus w ith im plication and 
negation as only prim itive connectives. (See footnotes 210, 211.)

---


148
T H E  P R O P O S I T I O N A L  C A L C U L U S
[Chap. II
junction and equivalence, in the sense that p z) q — . p ~  pq is a theorem 
of the system,
3 6 ,2 3 . For the system Pp, show in a like sense that both implication and 
conjunction are definable from disjunction and equivalence. Hence disjunc­
tion, equivalence, and j constitute {in an appropriate sense) a complete 
system of independent primitive connectives for P!w (see 26.19).aao
26 *24 * B y  m ean s of th e tru th -ta b le of exercise 2 6 .1 0  w ith  v — 2, show , 
for th e sy stem  P s, that eq u iv a len ce (s noj; definaDle from d isju n ction  and 
n egation . H en ce, b y  the resu lt of th e preceding exercise, d isju n ction , eq u iv ­
alence, an d  n egation c o n stitu te  
(in an ap p rop riate sense) a co m p lete 
sy stem  o f in d ep en d en t p rim itiv e co n n ectiv es for Ps***°
27. Formulations employing axiom schemata. Formulations of the 
propositional calculus so far considered have been based each on a finite 
number of axioms, although the program of §07 allows also that the number 
of axioms be infinite, provided there is supplied an effective method by 
which to recognize a given wff as being or not being an axiom.
When the axioms are infinite in number, of course they cannot be written 
out in full, and it is necessary rather to indicate them (or all but a finite 
number of them) by one or more statements in the syntax language each 
introducing an infinite class of axioms. Such a statement in the syntax 
language may always be reworded as a rule of inference with an empty class 
of premisses, and in this sense the distinction between an infinite and a finite 
number of axioms is illusory. The more significant distinction is between 
formulations which rely more or less heavily on syntactical statements (such 
as rules of inference) to take the place of separately stated axioms in the 
object language—but here no sharp line of division can be drawn.
Formulations of the kind which we describe as based on an infinite number 
of axioms have important advantages in some cases. We consider in this 
section a particular class of such formulations, namely, those in which the 
primitive basis involves axiom schemata.221
m Wajsberg has shown (loc.cit.) that implication-conjunction-disjunction-/ and im­
plication-conjunction-disjunction-negation constitute complete systems of independent 
primitive connectives for P^, and Pg respectively, i.e., for the intuitionistic proposi­
tional calculus.
m A formulation of a different kind having an infinite number of axioms is obtained 
by choosing some suitable system of connectives as primitive and then making every 
tautology an axiom, no rules of inference being then necessary—as pointed out, in 
effect, by Herbrand in 1930.
This procedure provides no deductive analysis of the propositional calculus, and no 
opportunity to consider the effects of making or rejecting various particular assump­
tions (such as, e.g., the law of excluded middle or the law of denial of the antecedent— 
cf. §26). Nevertheless it may be useful in a case where it is desired to deal with the prop-

---


§27]
A X I O M  S C H E M A T A
149
An axiom schema represents an infinite number of axioms by means of 
an expression containing syntactical variables—a form, in the sense of 
§02—which has wffs as values.222 Every value of the expression is to be taken 
as an axiom. For convenience of statement we shall indicate this by writing 
the expression itself in the same manner as an axiom.
An example of a formulation of the propositional calculus with axiom 
schemata is the following system P,
The primitive symbols and the wffs of P are the same as those of P2 (§20). 
The axioms, infinite in number, are given by the three following axiom 
schemata:
A n . B o A
A zo [ B 3 C ] n , A 3 B D , A n C  
~A d ^ B d . B d A
And the only rule of inference (if we do not count the axiom schemata as 
such) is the rule of modus ponens.
*270. 
Every theorem of P is a theorem of P2.
Proof. Every axiom of P either is an axiom of P2 or is obtained from an 
axiom of P2 by a substitution (*201) or a simultaneous substitution (*210). 
And the one rule of inference of P is also a rule of inference of P2.
**271. 
Every theorem of P2 is a theorem of P.
Proof. Since every axiom of P2 is an axiom of P, and the rules of inference 
are the same except for the rule of substitution (*201), it will be sufficient 
to show that the rule of substitution is a derived rule of P. This is done as 
follows:
In an application of the rule of modus ponens, let the major premiss be 
C d  D, the minor premiss C, and the conclusion D. If we substitute the 
wff B for the variable b throughout in both premisses and in the conclusion, 
the three resulting wffs,
S|C  o  D|. 
S&C,. 
SlD \,
are also premisses and conclusion of an application of the rule of modus
ositional calculus rapidly and only as a preliminary to a study of more comprehensive 
systems. It has been used in this way by Hilbert and Bernays (Gnmdlagen dev Mathe- 
maiik, vol. 1 (1934), see pp. 83, 105), by Quine (Mathematical Logic, 1940, see pp. 88-89) 
and by others.
A similar short cut is indeed possible in the treatm ent of any logistic system whose 
decision problem has been solved in such a way as to provide a practically feasible 
decision procedure, but of course only after the solution of the decision problem. 
M*Compare the discussion of definition schemata in §11.

---


150
THE PROPOSITIONAL CALCULUS
[Chap. II
ponens, in view of the fact that
S bC 
D|
is the same wff as
S bB C \ => S|D|.
Since the only rule of inference of P is modus ponens, and since the result of 
making the substitution of B for b throughout an axiom of P is again an 
axiom of P, it follows that a proof of a wff A as a theorem of P can be trans­
formed into a proof of
S b A )
as a theorem of P by just substituting B for b throughout, in every wff in 
the proof.
This completes the proof of the metatheorem **271.223 It may of course be 
used as a derived rule of P, but we have numbered it with a double asterisk 
as a metatheorem of P2.
As a corollary of **271, we have also the following metatheorem of Pa:
**272. 
There is an effective process by which any proof of a theorem of Pa 
can be transformed into a proof of the same theorem of Pa in which 
substitution is applied only to axioms (i.e., in every application of 
the rule of substitution the premiss A is one of the axioms of P2).
In the foregoing we have chosen the system P as an example, because it 
is closely related to the particular formulations of the'functional calculi of 
first order that receive treatment in the next chapter. It is clear, however, 
that any formulation of the propositional calculus or any partial system of 
propositional calculus, if the rules of inference are modus ponens and sub­
stitution, may be reformulated in the same way, i.e., we may replace each 
axiom by a corresponding axiom schema and take modus ponens as the one 
rule of inference, so obtaining a new system which has the same theorems 
as the original one.
A like reformulation is also possible if the rules of inference are substitution 
and one or more rules similar in character to modus ponens. For example, 
the system PL of §25 may be reformulated as follows, as a system PLff
2MThe remark should be made that, in spite of the equivalence of P to Pa in the strong 
sense that is given by *270 and **271, and in spite of the completeness of Pg, neverthe­
less P is not complete in any of the three senses of §18. In fact the wff pZ2g, for example, 
could be added to P as an axiom without producing any inconsistency. Semantically, 
this is connected with the fact that P has a wider class of sound interpretations than 
Pt, the rules of P being (in consequence of the omission of the rule of substitution) no 
longer sufficient to distinguish between propositional variables and propositional 
constants.

---


§28]
PROTOTHETIC
151
whose theorems are the same as those of PL. The primitive symbols and the 
wffs of PLer are the same as those of PL. The one rule of inference is: From 
A | . B | G and A to infer C. And the axioms are all the wffs,
A | [B | C] | . A | [C | A] | . D | B | . A | D | . A | Df
where A, B, C, D are wffs (to be taken in all possible ways).
28. Extended propositional calculus and protothetic.
The extended propositional calculus of Russell and Lukasiewicz-Tarski824 has, 
besides notations of the propositional calculus, also the universal quantifier or 
the existential quantifier or both (cf. §06), with propositional variables as the 
operator variables.
Primitive symbols for a formulation of the extended propositional calculus 
may be selected in various ways, among which may seem most obvious the 
addition of one or both of the quantifiers to the primitive symbols of a formula­
tion of the propositional calculus. But because this latter method, when applied 
to Pi or P 8l leads to non-independence of the primitive connectives and operators, 
Lukasiewicz and Tarski propose instead implication and the universal quantifier 
as primitive connective and operator. 
Other connectives and operators are 
then introduced by definition. E.g., the following definitions may be made;226
/ -* * (S)J 
~A 
A 
/
(3c)A -v ~(c)~A
i 
(3s)s
[A 
B] -> (c) [A 
B]
And other sentence connectives may then be defined as in §11.
M,The extended propositional calculus was treated by Russell under the name of 
"theory of im plication" in the American Journal of Mathematics, vol. 28 (1906), pp. 
169-202. I t was treated by Lukasiewicz and Tarski as "erw eitcrter Aussagenkalkul" 
in the Comptes Rendus des Seances de la Societe dts Sciences et des Retires de Varsovie, 
Classe III, vol. 23 (1930), pp. 44-50.
m As appears from an inform al account in The Principles of Mathematics (1903) and 
from his further discussion of the m atter in 1906, Russell also intended to use these 
prim itives for the extended propositional calculus. B u t in 1906 he takes negation as an 
additional prim itive connective on the ground th at it would otherwise be impossible 
to express the proposition th a t n o t everything is true— which, he holds, is adequately 
expressed by *'[p)p but not by (p)p o  (s)s. (To the w riter it would seem th at Russell's 
position of 1906 involves the very doubtful thesis th a t there is one indispensable con­
cept of negation, given a priori, which it is the business of the logician to reproduce; 
perhaps n o t even the extrem e realism  of Frege w ould support this.)
*,8In 1903 Russell defines ~'p, in effect, as p ZDf r. In 1906 he considers and rejects 
the definition ot ^ £ a s p  CD (s)s. Also due to Russell (1903, 1908) is the definition of the 
conjunction pq (or, more generally, of A B ), which is suggested by the third of the four 
displayed formulas on th e n ex t page.
The definition of ~p as p ZDr r is foreshadowed in C. S. Peirce's paper of 1885 
{American Journal of Mathematics, vol. 1, see pp. 189-190). And it m ay have been from 
this source th a t Russell had the idea. However, Peirce does not explicitly use the uni­
versal quantifier in a definition of negation, but rath er expresses the negation of p 
by p Z2 a, where a  is explained verbally as an "index of no m atter w hat token."

---


152
THE PROPOSITIONAL CALCULUS
[Chap. II
Adopting the Lukasiewicz-Tarski primitives and the above definitions, to­
gether with conventions about omissions of brackets parallel to those of §11, 
we may cite the following as some examples of wffs (sentences or propositional 
forms) which are true or have always the value truth in the intended interpre­
tation and therefore ought to be theorems:
p  zd q  ZDQ[q zd r ]  zd r  
pZDq =  . q ^ r z D r , p ^ r  
p q  =  . p  ■=> {q  =3 r ]  = > r  »■
(#») (3«) t*') -P => ?=> ■? =>P =3r
Using still the same primitives, and relying on the intended interpretation, we 
can show that the extended propositional calculus and the formulation Pa of 
the propositional calculus are equivalent in a sense similar to that in which Pj 
and P2 were shown to be equivalent in §23. For it is clear that (b)B is concurrent 
(in the sense of §02) to the conjunction CD,287 where C is obtained from B by 
substituting/ id / (i.e.. (s)s id (s)^) for all free occurrences ofb, and D is obtained 
from B by substituting { (i.e., (5 )5 ) for all free occurrences of b. Given a wff A of 
the extended propositional calculus, we may iterate the operation of replacing 
a wf part (b)B by the conjunction CD just described, only obeying the restric­
tion that this replacement is not be made if (b)B is the particular wff (s)s. 
After a sufficient number of iterations of this, the wff A will be changed to a 
wff A0 in which the universal quantifier does not appear except in wf parts 
(5 )5 . Upon replacing (5 ) 5  everywhere by the primitive symbol / of P A 0 becomes 
a wff Af of Pj. The correspondence between A and Af is a many-one correspond­
ence between wffs of the extended propositional calculus and wffs of Pj. And by 
assumption (4) of §02, A and Af are concurrent. In view of the solution of the 
decision problem of PXJ this leads us to a solution of the semantical decision 
problem of the extended propositional calculus; and in formulating the extended 
propositional calculus as a logistic system we may be guided by the demand that 
solution of the decision problem for provability shall be the same as of the 
semantical decision problem.
The p r o t o i k e t i c  of Le&niewski228 has, in addition to the notations of the extend­
ed propositional calculus, also variables whose values are truth-functions (in 
the sense of the last paragraph of §05), say
t \  i l, h \ /{, g\, h\, /*,...
as variables whose range consists of the singulary truth-functions, and
f%> z \ h \ t\, g\, h\t
as variables whose range is the binary truth-functions, and
___________ 
/•. Z*> h*. f\. 
h\,
,t7In addition to the use of the word “conjunction*' to denote the connective or its 
associated truth-function, as explained in §05, it will be convenient also to speak of 
a wff CD (formed from C and D by means of this connective) as “a conjunction/’ 
Similarly a wff G V D will be called “a disjunction," a wff G s D  “an equivalence," 
a wff ~C “a negation," and so on.
*MStanislaw Le£niewski, “Grundziige einesneuen SystemsderGrundlagenderMathe- 
matik," in Fundamenta Mathematicae, vol. 14 (1929), pp. 1-81.

---


§28]
PROTOTHETIC
153
as variables whose range is th e ternary truth-functions, and so on, F urther, the 
notation for application of a function to its argum ent or argum ents (see §03) is 
provided for am ong th e prim itive sym bols. A nd the quantifiers are allowed to 
have n o t only propositional variables b u t variables of any kind as operator 
variables. Le£niewski allow s also variables of still other types, e.g., variables 
whose values are propositional functions of truth-functions, b u t these seem to 
play a less im p o rtan t role, and we venture to  change his term inology to the 
ex ten t of excluding th em  from p ro to th etic .282 Finally, LeSniewski allows asser­
tion of sentences only, and not of wffs containing free variables (cf. th e end of 
§0 0); b u t this is from  one point of view a non-essential feature, an d  we would 
propose th a t th e nam e protothetic be applied also to system s, otherw ise like 
Leiniew ski's, in w hich wffs w ith or w ithout free variables m ay be asserted.
F o r the prim itive sym bols of a form ulation of protothetic, besides the various 
kinds of variables and th e notation for application of a function to its argum ent 
or argum ents, we m ay take im plication as prim itive sentence connective, and 
the universal q u an tifier as prim itive operator (allowing it to have a variable of 
any kind as operator variable). Or, following a discovery of T arski,2*0 im plication 
m ay be replaced by (m aterial) equivalence as prim itive connective.
E quivalence of p ro to th etic to extended propositional calculus, an d  th u s ulti­
m ately  to propositional calculus, m ay be show n by a sim ilar m ethod and in a 
sim ilar sense to those for the equivalence of extended propositional calculus to 
Pi. In  lieu of an explicit statem en t of the m any-one correspondence between 
wffs of protothetic an d  of extended propositional calculus (which would be 
lengthy), we shall m erely indicate the correspondence by giving som e examples. 
F o r the wff* 231 (/l) , p  zd (tf)/l(?) ^  (?) - p zd f l {q) of protothetic, the correspond­
ing wff of extended propositional calculus is the conjunction of the four 
follow ing:232
p zd (q)t = (q) . p  zd t
P =3 (?)? =  (?) • P => ?
P => (?) ~q =  {q) .p  => ~q
P => (q)f =  ( q ) . p z z f
A gain, for the wff (/2) < p =  q zd (r) . f2{p, r) =  f2[q, r) of protothetic, the cor­
responding wff of extended propositional calculus is a conjunction of sixteen 
Others, which we shall n o t w rite out in full b u t which include, e.g , th e  following:
m We may speak of higher protothetic when variables of such higher types arc to be 
allowed. (Added in proof. Since this was w ritten a comprehensive account of proto­
thetic by Jerzy Sfupecki has appeared in Studia Logica (Warsaw), vol. 1 (1953), pp. 
4-4-112; Slupecki gives the names propositional calculus with quantifiers, elementary 
protothetics, and protothelics to what we here call extended propositional calculus, 
protothetic, and higher protothetic respectively.)
twFundamenta Mathematicae, vol. 4 (1923), pp. 196-200.
231 As an abbreviation, in writing particular wffs of protothetic, the superscripts after 
the letters /, g, h may simply be omitted. No confusion can result among variables 
whose values are functions of different numbers of arguments, or even with the letter / 
denoting the truth-value falsehood.
S82By the conjunction of four wffs A, B, C, D we mean, of course, the conjunction 
ABCD, understood according to the convention of association to the left (§11).

---


154
THE PROPOSITIONAL CALCULUS
[Chap. II
p == q => (r) - t ss * 
p  =  q ^ D ( r ) . p y r ~ q y r  
p  =  q => ( f ) . ? c f = . ^ c r  
p ss ? => (r) - p ss q
(i =  p ( y ) ^ D r 3 . p j '
£ =  ? => M  
'  s  r
For a wff (say) (/2 * * * * *)B of protothetic, w here B contains /* as a  free variable only 
and contains no other truth-functional variables, the corresponding w ff of 
extended propositional calculus would be a conjunction of 256 others (there are, 
nam ely, 256 different ternary truth-functions, and we m u st use some system atic 
m ethod of setting down for each one a propositional form  which has it as an 
associated function).” 8 If the entire given wff (as distinguished from  a wf p a rt 
of it) has free truth-functional variables, it is necessary first to prefix universal 
quantifiers binding these variables, and then to apply the indicated m ethod of 
obtaining a corresponding wff of extended propositional calculus.
Like propositional calculus, both extended propositional calculus and p ro to ­
thetic or a m odified form of p ro to th etic23* will occur as p a rts of m ore extensive 
logistic system s to be considered later— in particular, of functional calculi of 
second or higher orders. However, in th e treatm ent of these logistic system s w hich 
we shall adopt, extended propositional calculus and protothetic do not p lay  a 
fundam ental role in the way th a t the propositional calculus does. Therefore in 
this section we have confined ourselves to a brief sketch.
EXERCISES 38
28.0. U sing the solution of the decision problem  w hich is indicated in the 
text, verify th e four examples w hich are given of wffs of extended propositional 
calculus th a t are true or have alw ays the value tru th . (Of course, where possible, 
m ake use of known results regarding propositional calculus in order to shorten 
the work.)
2 8 . 1 . In  the same way, verify the following as wffs of protothetic th a t have 
alw ays the value tru th .281
2” For this solution of the decision problem of protothetic, cf. LeSniewski, loc.cit.,
and references to Lukasiewicz and to Tarski which are there given.
” *In the case of the functional calculus of fourth or higher order, the modification of
protothetic (besides a change in the letters used as truth-functional variables) will
consist in allowing the notation for application of a function to its arguments to be used
only in such combinations as a(b), a(b, c), a(b, c, d), . . 
where a is in each case a 
truth-functional variable of appropriate kind and b, c, d, . . . mu9t be propositional 
variables. For reasons which will become clear later, this may be considered a modi­
fication in  t h e  particular formulation of protothetic r a t h e r  t h a n  i n  p r o t o t h e t i c  i ts e lf , 
the decision depending on what notion of equivalence b e t w e e n  logistic systems w e  are 
willing to accept for this purpose. But, e.g., although 28.1(4) and 28.1(7) are wffs of 
formulations of protothetic which are contemplated in this section, they are not wffs 
of any functional calculus of higher order (even with change of the letters /, g).
On the other hand, protothetic occurs as a part of the logistic system of Chapter X 
with no modifications other than essentially trivial changes of notation.

---


§29]
HISTORICAL NOTES
155
(!).»
p = q = )  ■f(p) =  /(?)
(2)
P =  q =  if) - HP) => /(?)
(3)” ‘
pq =  {f) . p s= .f(p) = f [ q )
(4)
tip. P) => - tip. ~P) =  iq)fiP. q)
(5)
g(p) =  g{t)p v g(f) ~p 
(Boole's law of development.™)
(6)
g(p, q) =  g(i, t)pq v g(t, f) p ~q v g(f, t) ~p q v g{ft f) ~p ~q
(Bootes law of development in two variables.™)
(7)
Oq)iP) -figiP)) =  gif ip)) = q
(8)*«
111
m
>
IH
pq =  (/) ,f{p. q) = f { q . p  =  q)
28.2. W ith aid of the solution of the decision problem which is indicated in 
the text, establish a principle of duality for a formulation of extended propo­
sitional calculus with the Lukasiewicz-Tarski primitives, analogous to the prin­
ciple of duality *161 for the propositional calculus.
28.3. Likewise establish a principle of duality for a formulation of protothetic 
with implication as the only primitive sentence connective, and the universal 
quantifier as the only prim itive operator.
29. H istorical notes. The algebra of logic htui its beginning in 1847,239 
in the publications of Boole and De Morgan.240 This concerned itself at 
first with an algebra or calculus of classes, to which a similar algebra of
••■Notice the relationship of this to the metathcorem of exercise 15.2 (or to the 
analogue of this metatheorem for any other formulation of the propositional calculus). 
Namely, all theorems given by this metatheorem are in a certain sense included in the 
one theorem of protothetic, being directly obtainable from it by a rule of substitution 
for propositional variables, like *10 1 or *2 0 1, and a rule of substitution for truth-func­
tional variables, analogous to the rule of substitution for functional variables which is 
discussed in the next chapter. Thus the relationship is like that of, e.g., the theorem 
. p 
q of the propositional calculus to the metathcorem that every wff ~A. rj . 
A 
B is a theorem.
M,Cf. Tarski in the paper cited in footnote 230.
l97Given by George Boole for the class calculus. Notice the relationship to the meta­
theorem of exercise 24.9 (concerning reduction to full disjunctive normal form).
•••From a  paper by Boleslaw Sobocihski, Z B a dart nad Prototetyk<\, which was 
published as an offprint in 1939, but nearly all copies of which were destroyed in the 
war. An English translation with an added explanatory introduction was published in 
1949 by the "Institut d'fitudes Polonaises en Belgique’1 under the title An Investigation 
of Protothetic.
•••There were a number of anticipations of the idea of an algebra or a calculus of 
logic, especially by Leibniz, Gottfried Ploucquet, J. H. Lambert, G. K. Castillon, but 
these were in various ways inadequate or incomplete and never led to a connected 
development. See Louis Couturat's La Logique de. Leibnis (1001) and Opuscules ft 
Frag want* [ nidus tie Leibnit (1003), C I. LusviH'* W .Vwwy of Symbols Lohu (MjIM), 
Jsrgcm Jergonsen'a A Treatise of Formal Logic (1031). Karl Uiirr's “ Dio Logiatlii 
Johann Heinrich Lam berts" in Festschrift Andreas Spriser (1945); and the writer's 
"A Bibliography of Symbolic Logic" in volumes 1 and 3 of The Journal of Symbolic 
Logic.
•••George Boole, The Mathematical Analysis of Logic (1847), and An Investigation of 
the Laws of Thought (1854). Augustus Dc Morgan, Formal Logic (1847).

---


156
THE PROPOSITIONAL CALCULUS
[Chap. II
relations241 was later added. Though it was foreshadowed in Boole's treat­
ment of “Secondary Propositions," a true propositional calculus perhaps 
first appeared from this point of view in the work of Hugh MacColl, begin­
ning in 1877.242
The logistic method was first applied by Frege in his Begriffsschrift of 
1879. And this work contains in particular the first formulation of the prop­
ositional calculus as a logistic system, the system PF of 23.6. Due to 
Lukasiewicz243 as a simplification of Frege's formulation is the system P2, 
which we have used in this chapter (§20).
However, Frege’s work received little recognition or understanding until 
long after its publication, and the propositional calculus continued develop­
ment from the older point of view, as may be seen in the work of C. S. Peirce, 
Ernst Schroder, Giuseppe Peano, and others. The beginnings of a change 
(though not yet the logistic method) appear in the work of Peano and his 
school. And from this source A. N. Whitehead and Bertrand Russell derived 
much of their earlier inspiration; later they became acquainted with the 
more profound work of Frege and were perhaps the first to appreciate its 
significance.214
After Frege, the earliest treatments of propositional calculus by the lo­
gistic method are by Russell. Some indications of such a treatment may be 
found in The Principles of Mathematics (1903). It is extended propositional 
calculus (§28) which is there contemplated rather than propositional cal­
culus; but by making certain changes in the light of later developments, it 
is possible to read into Russell’s discussion the following axioms for a partial 
system P jf of propositional calculus with implication and conjunction as 
primitive connectives, the rules of inference being modus ponens (explicitly 
stated by Russell) and substitution (tacit): * 84
M1De Morgan, S y lla b u s  o f a  P ro p o sed  S y s te m  o} L o g ic (1860), and a paper in the 
T ra n s a c tio n s o f th e C a m b rid g e P h ilo s o p h ic a l S o ciety, vol. 10 (1864), pp. 331-358; 
C. S. Peirce, various papers 1870-1903, reprinted in volume 3 of his C ollected P a p ers', 
J. J. Murphy, various papers 1875-1891; Ernst Schr&der, A lg e b ra  d e r  L o g ik , vol. 3
(1895).
H iM a th e m a tic a l Q u e stio n s, vol. 28 (1877), pp. 20-23; P ro c e e d in g s o f the L o n d o n  
M a th e m a tic a l S o c ie ty , vol. 9 (1877-1878), pp. 9-20, 177-186, and vol. 10 (1878-1879), 
pp. 16-28; M i n d , vol. 5 (1880), pp. 45-60; P h ilo so p h ic a l M a g a z in e , 5s. vol. 11 (1881), 
pp. 40-43.
84SSee Lukasiewicz and Tarski, “ Untersuchungen fiber den Aussagenkalkul" in 
C o m p tes R e n d u s  d es S ta n c e s  de la  S o c titd  d es S cien c es et des L e ttr e s  de V a rso vie, Classe 
III, vol. 23 (1930), pp. 30-50.
*MAn excellent historical and expository account of the work of Whitehead and 
Russell is found in Chapter 2 (by W. V. Quine) of T h e  P h ilo s o p h y  o f A lfr e d  N o r th  
W h iteh ea d .

---


§29]
HISTORICAL NOTES
157
pqZDp
[p ZD q][q ZD r) ZD . p ZD r 
p ZD [q ZD r] ZD .pq ZD r 
pqZDrZD.pZD,q=>r 
[p ZD q] [p ZD r j 3  , p ZD 
p ZD q ZD p ZD p
As a part of Russell's treatment of extended propositional calculus in 1906,224 
there appears a formulation Pr of the propositional calculus, with implication 
and negation as primitive connectives, modus ponens and substitution as 
rules of inference, and the following axioms:
p ZD p 
p ZD * q ZD p
p^>qZD.qZDrZD.pZDr 
p ZD [q ZD r]zD.q^>.pZDr 
) p
p ZD ~p ZD ~p 
p ZD ~q ZD - q ZD ~p
The formulation PR of the propositional calculus (§25) was published by 
Russell in 1908,245 and was afterwards used by Whitehead and Russell in 
Principia Mathematica in 1910. It may be simplified to the system PB by 
just deleting the axiom whose non-independence was discovered by Paul 
Bemays.246 Other simplifications of it are the system PN, due to J. G. P. 
Nicod,247 and the system PG, due to Gotlind and Rasiowa.248
Statement of the rule of substitution was neglected by Frege in 1879, but 
appears explicitly in connection with a different system in his Grundgeseize 
der Arithmetik, vol. 1 (1893). First statement of the rule of substitution 
specifically for the propositional calculus is by Louis Couturat in Les 
Principes des Mathematiques (1905), but his statement is perhaps insufficient 
as failing to make clear that the expression substituted for a (propositional) 
variable may itself contain variables. Russell states this rule more satis­
factorily in his paper of 1906, but omits it in 1908. And in Principia Mathe­
matica the authors hold that the rule of substitution cannot be stated, 
writing: "The recognition that a certain proposition is ajx instance of some 
general proposition previously proved . . . cannot itself be erected into a
U6American Journal of Mathematics, vol. 30 (1908), pp. 222-262.
U9Mathematische Zeitschrift, vol. 25 (1926), pp. 305-320.
,47Proceedings of the Cambridge Philosophical Society, vol. 19 (1917-1920), pp. 32-41.
a48E rik Gdtlind in the Norsk Matematisk Tidsskrift, vol. 29 (1947), pp. 1-4; H. 
Rasiowa, ibid,, vol. 31 (1949), pp. 1-3.

---


158
THE PROPOSITIONAL CALCULUS
[Chap. II
general rule." This seems to show that Whitehead and Russell had aban­
doned Frege's method ol stating rules of inference syntactically, or perhaps 
had never fully accepted it. But C. I. Lewis, writing in immediate connection 
with Principia Mathematical states the rule of substitution explicitly for 
a proposed system of Strict Implication in 1913,249 and in his Survey of 
Symbolic Logic (1918) he supplies this rule also for the system of Principia. 
And Russell, in his Introduction to Mathematical Philosophy (1919), recog­
nizes that there is an omission in Principia in failing to state the rule of 
substitution for the propositional calculus.
The device of using axiom schemata, as in §27, so that a rule of sub­
stitution becomes unnecessary was introduced by J. v. Neumann.260
For the propositional calculus, the name "calculus of equivalent state­
ments" wTas used by MacColl The name "Aussagenkalkul" was introduced 
by Schroder in German in 1890 and 1891. Perhaps as a translation of this, 
Russell uses "propositional calculus" in 1903 and again in 1906—but, at 
least in 1903, he applies the name to extended propositional calculus rather 
than to propositional calculus proper (according to the terminology now 
standard). Couturat251 translates Russell's "propositional calculus" into 
French as "calcul des propositions," but at the same time he so alters Rus­
sell's method that the name comes to be applied to propositional calculus 
proper. The name "calculus of propositions" was used by Lewis in a series 
of papers beginning in 1912 and in A Survey of Symbolic Logic (1918). Since 
then the names "propositional calculus" and "calculus of propositions" have 
received general acceptance in the sense, or about the sense, in which we 
have used the former.252
Zi*The J o u r n a l o f P h ilo so p h y, P sy c h o lo g y , a n d  S c ie n tific  M e th o d s, vol. 10 [1913), 
pp. 428-438.
2i0M a th e m a tisc h e  Z e iisc h rift, vol. 26 (1927), pp. 1-46. Von Neumann's device may be 
employed as a means of formulating a logistic system for which a rule of substitution 
cannot be used because of the absence of propositional variables or other variables 
suitable for the purpose. Thus in particular a simple applied functional calculus of first 
order, in the sense of the next chapter (§30), must be formulated with the aid of axiom 
schemata rather than a rule or rules of substitution.
See a discussion of the m atter by H ilbert and Bernays in G ru n d la g e n  der M a th e m a tik , 
vol. 1, pp. 248-249; also, specially for the propositional calculus, by Bernays in L o g ic a l 
C a lcu lu s (1935-1936), pp. 44-47; also by Bernays, ib id ., pp. 50-53.
**lIn R e v u e  de M ita p h y s iq u e  et de M o r a le , vol. 12 (1904), pp. 25—30, and in L e s  
P n n c ip e s  des M a ih im a tiq u e s (1905).
a“ Other names found in the literature are ''theory of deduction" (in P r in c ip ia  
M a th e m a tic a  and in Russell's In tr o d u c tio n  to M a th e m a tic a l P h ilo s o p h y ) and "sentential 
calculus" (i.e., calculus of sentences, by a number of recent writers). But both of these 
names seem rather inappropriate because they refer to certain syntactical aspects of 
the calculus (deducibility, sentences) rather than to corresponding meanings (impli­
cation, propositions). Indeed a theory of deduction or a calculus of sentences would more 
naturally be a branch of logical syntax and be expressed in a meta-language.

---


§29]
HISTORICAL NOTES
J59
A formulation of the propositional calculus with a single axiom was given 
by Nicod in January 1917,253 the system Pn of §25. Modifications of this, 
having still a single axiom, are the systems Pw of Wajsberg,254 and 
of Lukasiewicz.256 All three systems are based on Sheffer's stroke (non­
conjunction) as primitive connective and employ a more powerful rule of 
inference in place of modus ponens.
Regarding formulations of the propositional calculus with a single axiom 
and with only modus ponens and substitution as rules of inference, see the 
historical account given by Lukasiewicz and Tarski in the paper cited in 
footnote 243. Of these, the system PL (exercise 23.7) is due to Lukasiewicz 
and is given in the same paper; the system Pt (23.8) is also due to Lukasie­
wicz, being credited to him in a paper by Boleslaw Sobocihski;256 and the 
system of Ps (23.9) is obtained, by a method of Sobocinski,256 from the single 
axiom of exercise 18.4 for the implicational propositional calculus (the 
system P^), which latter is due to Lukasiewicz.257
Another formulation of the implicational propositional calculus is the 
system Pg of exercise 18.3, which is due to Tarski and Bernays.258 Wajsberg 
has shown that,259 the rules of inference being always modus ponens and 
substitution, a complete formulation of the implicational propositional cal­
culus becomes a complete formulation of the (full) propositional calculus 
with implication and / as primitive connectives upon adjoining f 
p as an 
additional axiom. 
Hence the 
system 
Pw 
of 
12.7, 
obtained 
thus 
from Pg, and the system P^ (§26), which is obtained in the same way 
from P£.
LeSniewski was especially interested in equivalence as a primitive con­
nective because he took definitions in sense (3) of footnote 168, and therefore 
expressed definitions, in the propositional calculus or in protothetic, as 
(material) equivalences.260 The first formulation of a partial system of prop­
ositional calculus with equivalence as sole primitive connective (such that
MiIn the paper cited in footnote 247.
l5iMonatshefte fiir Mathemalik und Physik, vol. 39 (1932). pp. 259-202.
I5BGiven in W ajsberg's paper cited in the preceding footnote. Still another modifi­
cation of Nicod's axiom, due to Lukasiewicz, is given by Lesniewski m the paper cited 
in footnote 228, p. 10.
mprzeglqd Filozoficzny, vol. 35 (1932), pp. 171-193.
187Proceedings of ike Royal Irish Academy, vol. 52 section A no. 3 (1948), pp. 25-33.
(Added in proof. Various still shorter single axioms for the propositional calculus are 
given by C. A. Meredith in The Journal of Computing Systems, vol. 1 no. 3 (1953), 
pp. 155-164.)
>5SSee the account of the m atter by Lukasiewicz and Tarski in the paper cited in 
footnote 243.
BHIn Wiadomoici Matematyczne, vol. 43 (1937), pp. 131-168.
a80See the paper cited in footnote 228, pp. 10-11.

---


160
THE PROPOSITIONAL CALCULUS
[Chap. II
all tautologies in this connective are theorems) was by LeSniewski.281 Other 
such formulations are the system 
of 26.0, by Wajsberg;882 and the 
systems with a single axiom, Pj; of 26.3(1), by Wajsberg, and PE of 
26.3(2), by Lukasiewicz.883 The system PEN of 26.4, with equivalence and 
negation as primitive connectives, is due to Mihailescu.864
Returning to formulations of the full propositional calculus, we mention 
also the system PA of Lukasiewicz, having implication and negation as 
primitive connectives, modus ponens and substitution as rules of inference, 
and the three following axioms;
p ZD qZD .qzD rZD  ,pZD r 
~p ZD P ZD P 
P  ZD n~p ZD q
A proof of the completeness of PA (not quite the same as the original treat­
ment of the system by Lukasiewicz285) is outlined in exercise 29.2 below.
Opposite in tendency to such formulations as P* and P , in which econ­
omy is emphasized, are formulations of the propositional calculus by Hil­
bert286 which are designed to separate the roles of the various connectives, 
though at the cost of economy and of independence of the primitive connec­
tives. Of this latter kind is the system PH (§26), which is one of a number of 
closely related such formulations that are given by Hilbert and Bernays in 
the first volume of their Grundlagen der Mathematik (1934) 887
■“ In the same paper, p. 16.
■“ In the paper cited in footnote 259, p. 163. The axioms were previously announced, 
without proof of their sufficiency, in the paper cited in footnote 254.
■“ The system of 26.3(1) is in W ajsberg's paper of footnote 259, p. 165, previously 
announced in the paper of footnote 254. The same papers have also two other formu­
lations of the equivalence calculus by Wajsberg, one of them  with a single axiom. 
Various other single axioms for the equivalence calculus are quoted (without proof of 
sufficiency) in the paper cited in footnote 256. However, the shortest single axioms for 
the equivalence calculus, with rules of inference as in 26.0, are due to Lukasiewicz, 
one of them being the axiom given in 26.3(2) (see a review by Heinrich Scholz in 
Z e n tr a lb la tt f u r  M a th e m a tik  u n d  ih re G renzgebiete, vol. 22 {1940), pp. 289-290),
■“ In the paper cited in footnote 215.
■“ In his mimeographed E le m e n ty  L o g ik i M a te m a ty c z n e j, Warsaw 1929.
in A b h a n d lu n g e n  a u s d e m  M a tk e m a tis c k e n  S e m in a r  d e r H a m b u rg isc h e n  U n iv e r ­
s i t y , vol. 6 (1928), pp. 65-85.
■“ Hilbert and Bernays use the axiom p Z D q Z 3* p Z D r^mpZDqrin place of the shorter 
axiom p ^  * q ^ p q . They mention the obvious possibility of using the shorter axiom, 
but point out that by doing so in the case of the formulation of the propositional cal­
culus which they adopt primarily (and which is in some other respects not quite the 
same as our system Ph ) the independence of the axiom p ZD m q ZD p would be destroyed. 
In his L o g ic a l C a lcu lu s (1935-1936), p. 44, Bernays introduces a formulation P h / of 
the propositional calculus which differs from P h only in having the law of re d u c tio  a d  
a b su r d u m  and the law of double negation as axioms in place of the converse law of 
contraposition. The independence of p zd ■ q 3  p as an axiom of P h was established

---


§29]
HISTORICAL NOTES
161
By omitting from PH negation and the one axiom containing negation, 
there is obtained a formulation Pp of what Hilbert and Bernays call ''posi­
tive Logik," or positive propositional calculus. This is intended to be that part 
of the propositional calculus which is in some sense independent of the existence 
of a negation (e.g., Peirce’s law is not a theorem of it). By omitting all con­
nectives other than implication, and the axioms containing them, there is 
obtained a formulation P+ of the positive implicational propositional calculus.
Such a system as PH has also the advantage (indicated by Hilbert and 
Bernays) of exhibiting in very convenient form the relationship between 
the full propositional calculus and the intuitionistic propositional calculus. 
Namely, the systems Pg and P“ of §26 are obtained by adding to Pp negation 
and appropriate axioms containing negation, or in other words by altering 
only the negation axioms of PH. The formulation P*s of the intuitionistic 
propositional calculus is due to Heinrich Scholz and Karl Schroter.288 The 
formulation P*w of the intuitionistic propositional calculus (employing / 
as primitive instead of negation, and adding the axiom / 
p to Pp) was 
given by Wajsberg,269 but a similar observation regarding the possibility of 
using / in place of negation in formulating the intuitionistic propositional 
calculus had been made also by Gerhard Gentzen.270
The formulation Pr (26.14) of the full propositional calculus may be cred­
ited to V. Glivenko on the basis of his remark that a formulation of the full 
propositional calculus is obtained from a formulation of the intuitionistic 
propositional calculus by adjoining only the law of excluded middle as an 
additional axiom.271
Many other formulations of the propositional calculus and partial systems 
of propositional calculus are found in the literature. We mention in this sec­
tion only those which we have actually used in text or exercises, or which 
seem to have some outstanding interest or historical importance.
The truth-table decision procedure for the propositional calculus (cf. §15) 
is applied in an informal way to special cases by Frege in his Begriffsschrift
above m 26.8; and its independence as ail axiom of 1*^' (a question left open by Bernays) 
may be established by a minor modification of the same method.
Additional results and remarks in connection with PH and related systems, including 
the positive implicational propositional calculus, the positive propositional calculus, 
and the intuitionistic propositional calculus, are in Supplement III of the second 
volume of Hilbert and Bernays’s Grundlagen dev Mathematik.
••■Credited to them  by Wajsberg m the paper cited in footnote 211.
M,In the paper cited in footnote 2 1 1 .
,T0See Mathematiscke Zeitschrifi. vol. 39, p. 189.
,n In his paper in Acadimie Royale de Belgique, Bulletins de la Classe des Sciences, 
series 6 vol. 15 (1929), pp. 183-188 (which contains also, as its principal result, the m eta­
theorems of exercise 26.15).

---


162
THE PROPOSITIONAL CALCULUS
[Chap. II
of 1879 (in connection with implication and negation as primitive connec­
tives). The first statement of it as a general decision procedure is six years 
later by Peirce* *71 (in connection with Implication and non-implication as 
primitive connectives). Much of the recent development of the method 
stems from its use by Lukasiewicz*78 and by Post.*74 The term tautology is 
taken from Wittgenstein.276
Using three truth-values instead of two, and truth-tables in thote three truth- 
values. Lukasiewicz first introduced a three-valued propositional calculus (cf. 
§19) in 1920.IT* He was led to this by ideas about modality, according to which 
o third truth-value—possibility, or better, contingency—has to be considered 
in addition to truth and falsehood; but the abstract importance of the new 
calculus transcends that of any particular associated ideas of this kind. Gen­
eralization to a many-valued propositional calculus with v +  1 truth-values 
of which /i +  1 are designated (1 
<  v), was made by Post in 1921,177
independently of Lukasiewicz, and from a purely abstract point of view. After­
wards, but independently of Post, Lukasiewicz generalized his three-valued 
propositional calculus to obtain higher many-valued propositional calculi; this 
was in 1922, according to his statement, but was not published until 1929 and 
1930.*7® Lukasiewicz's calculi differ from those of Post in that there is just one 
designated truth-value, and also in not being full (i.e., not every possible truth- 
function, in terms of the v truth-values, is represented by a form of which it is 
an associated function). When, however, Lukasiewicz's many-valued proposi­
tional calculi are extended to full many-valued propositional calculi by the 
method of Slupecki,*7* they become special cases of those of Post.
A primitive basis (especially axioms and rules of inference) for Lukasiewicz's 
three-valued propositional calculus, so that it becomes a logistic system, was 
provided by Wajsberg;280 and Lukasiewicz and Tarski assert that this may also
m In his paper cited in footnote 67, pp. 190-192 (or Collected Papers, vol. 3, pp
223-226).
|7>Jan Lukasiewicz in Przeglqd Filozoficzny, vol. 23 (1921), pp. 189-206, and in 
later publications.
,74E. L. Post in the American Journal of Mathematics, vol. 43 (1921), pp. 163-186. 
m Ludwig Wittgenstein, "Logisch-philosophische Abhandlung" in Annalen der N atur- 
philosophic, vol. 14 (1921), pp. 185-262; reprinted in book form, with English trans­
lation in parallel, as Traciatus Logico-philosophtcvs,
*u Ruch Filozoficzny, vol. 6 (1920), pp. 169-171. Lukasiewicz's truth-table for Z3 
appears in exercise 19.8, where a three-valued propositional calculus closely related 
to that of Lukasiewicz is described.
t77In the paper cited in footnote 274, which is Post's dissertation of 1920.
,78In the publications cited in footnotes 243, 265, and in Lukasiewicz's Philosophiscke 
Bemerkungen zu mehrwertigen Systemen des Aussagenkalkiils, which immediately follows 
(in the same periodical) the paper of footnote 243.
,7#Jerzy Slupecki in Comptes Rendus des Stances de la Sociiti des Sciences et des 
Lettres de Varsovie, Classe III, vol. 29 (1936), pp. 9-11, and vol. 32 (1939), pp. 102-128.
,wIn the Comptes Rendus des Stances de la Sociiti des Sciences et des Lettres de Varsovie, 
Classe III, vol. 24 (1931), pp. 126-148. Another system of axioms and rules of inference 
for Lukasiewicz's three-valued propositional calculus has been given recently by 
Alan Rose in The Journal of the London Mathematical Society, vol. 26 (1961), pp. 60-68.

---


§29]
HISTORICAL NOTES
163
be done for all the Lukasiewicz finitely many-valued propositional calculi. For 
full finitely many~valuod propositional calculi primitive bases have been given 
by Slupecki.,7# And more recently the question of primitive bases for finitely 
many-valued propositional calculi (and functional calculi) has been treated by 
J. B. Rosser and A. R. Turquette in a series of papers in The Journal of Symbolic 
Logic. Lukasiewicz introduced also an infinitely many-valued propositional 
calculus, but the question of a primitive basis for this seems to be still open.
For the purpose of proving independence of the axioms of the proposi­
tional calculus, the use of many-valued truth-tables (with one or more 
designated values) was introduced by Bernays in his Habilitationsschrift of 
1918, but not published until 1926 281 This idea was also discovered indepen­
dently by Lukasiewicz but not published. The remark that the method i an 
be extended to rules of inference was made by Huntington.282 The method 
employed in §19 of proving independence of the rule of substitution is due 
to Bernays (who suggested it to the writer in 1936).
The independence results of 26.11 and the three-valued truth-table used 
to obtain them are due to Heyting.m  The result of 26.12, and the many­
valued truth-tables of 26.10 (except in the cases v =  1,2) are Godel’s.284
Proofs of consistency and completeness of the propositional calculus, 
based on the truth-table method, were first made by Post.285 Since then, a 
number of different proofs of completeness of the propositional calculus have 
been published, of which we mention here only those by Kalmar286 and 
Quine.287 Quine makes use of the particular formulation Pw of the propo­
sitional calculus, with implication and / as primitive connectives. The for­
mulation 
of the propositional calculus, due to Wajsberg,288 combines 
some of the features of P2 and Pw: and the method by which we proved the 
completeness of Pl in Chapter I is an adaptation to this case of the method * 18
,B1In the Mathematische Zeitschrift, vol. 25 (1926), pp. 305-320.
18“E. V. Huntington in the Annals of Mathematics, ser. 2 vol. 36 (1935), pp. 313-324.
••■The first two of the independence results of 26.11 are proved in his paper of 1930, 
cited in footnote 209. All of them  follow immediately by the same method, whether for 
Heyting’s original formulation of the intuitionistic propositional calculus or any other.
tB4Akademie dev Wissensckaften in Wien, Mathematisch-naturwissenschaftliche Klasse, 
Angeiger, vol. 89 (1932), pp. 85-86.
■” In the paper of footnote 274.
BML4szI6 Kalmdr in Acta Scientiarum Matkematicarum, vol. 7 no. 4 (1935), pp. 
222-243.
l8Tln  The Journal of Symbolic Logic, vol. 3 (1938), pp. 37-40. References to earlier 
completeness proofs will be found in this paper.
■8sIn a paper in Wiadomoici Matematyczne, vol. 47 (1939), pp. 119-139. The idea of 
applying K alm ir's method to this formulation of the propositional calculus was sug­
gested to the writer by Leon Henkin as yielding perhaps the briefest available complete­
ness proof for the propositional calculus (if based on independent axioms with modus 
ponens and substitution as rules of inference).
The system PJJ of exercise 26.21 is obtained from this same paper of Wajsberg, where 
it is briefly mentioned on p. 139 in indicating a correction to the paper of footnote 211.

---


164
THE PROPOSITIONAL CALCULUS
[Chap. II
of Kalmar. Especially the method of the proof of *152 (which is a necessary 
preliminary to the proof of completeness in §18), the idea of using *151 as 
a lemma for *152, and the method of the proof of *151, are taken from 
Kalmar with obvious adaptations.
For the implicational propositional calculus, a completeness proof was 
published by Wajsberg289 (an earlier completeness proof by Tarski seems not 
to have been published). The method which was suggested in 18.3 for a 
completeness proof for the implicational propositional calculus follows 
Kalmar288 in general plan; but the idea of using a propositional variable in 
place of f is taken from Wajsberg,289 and the crucial idea of taking B' to be 
B ro r  i d  r  (rather than B) when the value of B is t, together with correspond­
ing changes at various places in proving analogues of *151 and *152, was 
communicated to the writer by Leon Henkin in July 1948.
The proof of equivalence of P2 to Px in §23 follows in large part a 
proof used by Wajsberg389 * * for a similar purpose.
The deduction theorem (§13) is not a peculiarity of the propositional cal­
culus but has analogues for many other logistic systems (in particular for 
functional calculi of first and higher orders, as we shall see in the chapters 
following). The idea of the deduction theorem and the first proof of it for 
a particular system must be credited to Jacques Herbrand,290 Its formulation 
as a general methodological principle for logistic systems is due to Tarski.291 
The name “deduction theorem” is taken from the German “Deduktions- 
theorem" of Hilbert and Bernays.392
The idea of using the deduction theorem as a primitive rule of inference in 
formulations of the propositional calculus or functional calculus is due in­
dependently to Jankowski293 and Gentzen.294 Such a primitive rule of infer­
ence has a less elementary character than is otherwise usual (cf. footnote 
181), and indeed it would not be admissible for a logistic system according
Ztt8In the paper cited in footnote 259.
8P0A modified form of the deduction theorem, adapted to a special formulation of the 
functional calculus of first order, was stated by him, without proof, in an abstract in the 
Comptes Rendus des Stances de I'AcaUtmie Ues Sciences (Paris), vol. 186 (1928), see 
p. 1275. The deduction theorem was stated and proved, for a system like the functional 
calculus of order w, in his Paris dissertation, Reckerches sur la Theorie de la Demon­
stration, published in 1930 as no. 33 of the Travaux de la Sociiii des Sciences et des 
Letlres de Varsovie, see pp. 61-62. In proving the deduction theorem, in Chapter I and 
again in Chapter III, we employ w hat is substantially H erbrand's method.
MlIt is stated by him in this way in a paper in the Comptes Rendus des Stances de la 
Socitit des Sciences et des Lettres de Varsovie, Classe III, vol. 23 (1930)—see Axiom 8* 
on p. 24.
2nGnmdlagen der Mathematik, vol. 1, p. 155, and vol. 2, p. 387.
a93Stanislaw Jaskowski, On the Rules of Suppositions in Formal Logic, 1934.
““ In the Mathematiscke Zeitschnft, vol. 39 (1934), pp. 170-210, 405-431; see especially 
II. Abschnitt, pp. 183-190.

---


§29]
HISTORICAL NOTES
IG5
to the definition as we actually gave it in §07. But this disadvantage may be 
thought to be partly offset by a certain naturalness of the method; indeed 
to take the deduction theorem as a primitive rule is just to recognize formally 
the usual informal procedure (common especially in mathematical reasoning) 
of proving an implication by making an assumption and drawing a conclusion.
Employment of the deduction theorem as primitive or derived rule must 
not, however, be confused with the use of Sequenzen by Gentzen295 (cf. 
39.10-39,12 below). For Gentzen's arrow, —»■, is not comparable to our 
syntactical notation, h, but belongs to his object language (as is clear from 
the fact that expressions containing it appear as premisses and conclusions 
in applications of his rules of inference). And in fact we might well have 
introduced Sequenzen in connection with Pj by means of the following 
definition schemata:298
Aj, A 2, . . . , A n—>-
Ax ZD m A 2
■ -.. An z>
Ali ^ 2# • - w A-n > B|, B2j . . 
Bm
-> ^  d  , A2 3  . .  .. An d  Bt v B2 v . . . vB m
where n =-= 0, 1, 2, 3, . . 
and m — 1, 2, 3, . . 
and where in both cases the 
abbreviation is to be used only for an entire asserted wff (never for a wf 
proper part of such). Thus we would have obtained all the formal properties 
of Gentzen's Sequenzen, and in particular would have been able to state the 
derived rules of 14.9 somewhat more conveniently.
For the derived rules of 14.9 themselves (as an alternative to use of the 
deduction theorem) credit should be given to Frege, rules very similar in 
nature and purpose having been employed by him in the first volume of 
his Grundgesetze der Arithmetik (1893).
The derived rule of substitntivity of equivalence (*159) and the related 
metatheorem of 15.2 were demonstrated for the propositional calculus— 
specifically, for PR—by Post.297 The related metatheorem *229 (where two 
implications take the place of an equivalence) was obtained for the implica- 
tional propositional calculus by Wajsberg.298
The full disjunctive normal form (24.9) may be traced back to Boole's law
" 5Ibid., 111. Abschnitt, pp. 190-210. Gentzen's use of Sequenzen is taken in part 
from Paul H ertz—see a paper by Gentzen in the Mathemalische Annalen, vol. 107(1932), 
pp. 329-350, and references to Hertz which are there given.
"^Substantially the same equivalences as those which appear from these definition 
schemata are given by Gentzen in the paper just cited, p. 180 and p. 418.
*” In the paper cited in footnote 274. See also the discussion of truth-functions and 
formal equivalence in the introduction to the first volume of Principia Mathematica 
(1910).
,MIn the paper cited in footnote 259.

---


166
THE PROPOSITIONAL CALCULUS
[Chap. II
of development (28.1(5), (6)), and it is used on this basis by Schroder in 
Der Operationskreis des Logikkalkuls (1877). Both the full disjunctive normal 
form and its dual, the full conjunctive normal form, were given in 1880 by 
Peirce.209 Schroder-and Peirce state the normal forms for the class calculus, 
but extension to the propositional calculus is immediate.
The principle of duality is to be credited to Schroder, who gives it for the 
class calculus in his Operationskreis, just cited, and again in his Algebra der 
Logik. Schrdder does not extend the principle of duality to the propositional 
calculus, but such extension is immediate and seems to have been assumed 
by various later authors without special statement of it (e.g., by Whitehead, 
Couturat, Sheffer) Heinrich Behmann, in the paper cited in footnote 299, 
explicitly establishes the principle of duality in a form corresponding to 
*165 not only for the propositional calculus but also, in effect, for the func­
tional calculi of first and second orders (where quantifiers are involved in 
addition to sentence connectives—see Chapters III-V below); and Hilbert 
and Ackermann in the first edition of their Grundziige der theoretischen Logik 
(1928) establish analogues of *164 and *165 for the propositional calculus 
and for the functional calculus of first order. However, a principle of duality 
in connection with quantifiers appears already in the third volume of 
Schroder’s Algebra der Logik.
EXERCISES 29
2 9 .O. (1) Establish the completeness of PT by proving as theorems the 
axioms of some formulation of the propositional calculus which has the 
same primitive connectives and the same rules of inference and is already 
known to be complete. (2) Discuss the independence of the axioms of Pr.
2 9 .1* (1) Establish the completeness of the partial system of propositional 
calculus P^K. (Compare 18.3.) (2 ) Discuss the independence of the axioms 
of P™
2flflIn the American Journal of Mathematics, vol. 3 (1880), pp. 37-39 (or Collected 
Papers, vol. 3, pp. 133-134).
Heinrich Behmann (in a paper in the Mathematische Annalen, vol. 88 (1922), pp. 
183-229) gives the name "disjunktive Normalform" to a disjunction of terms C< in 
which each term C< has the form of a conjunction of propositional variables and ne­
gations of propositional variables; and the name "konjunktive Normalform" to the 
dual of this. For the use of these normal forfns in the propositional calculus, Behmann 
refers to Bernays's unpublished Habilitaiionsschrift of 1918.
The full conjunctive normal form corresponds to the "ausgezeichnete konjunktive 
Normalform" of H ilbert and Ackermann (in Grundziige der theoretischen Logik) and 
is thus a special case of the "konjunktive Normalform" of Bernays, Behmann, Hilbert 
and Ackermann. And dually the full disjunctive normal form is a special case of the 
disjunctive normal form.

---


§29]
EXERCISES 29
167
29.2. E s t a b l i s h  t h e  c o m p l e te n e s s  o f P A b y  p r o v i n g  t h e  fo llo w in g  t h e o r e m s  
o f P A ( in  o r d e r )  a n d  t h e n  u s i n g  t h e  r e s u l t  o f e x e r c is e  1 2 .7 :
~ p  ZD 
[ ~ q  ZD q] ZD %p Z D  . ~ q  ZD q 
~ q Z D  ~ p  =0 mp  ZD m~ q z >  q 
~ q Z D ~ p Z D . ~ q Z D q Z D q Z D . p Z D q  
q Z D %~ q Z D q z D q z D + p Z D q  
p  ZD . ~ q  ZD q ZD q
~ qZ D  qZD qZD [ p  zd q]ZD .  ~ [ p  zd q] ZD mp  ZD q 
~ q  ZD q ZD q ZD [p ZD q) ZD . p  D  q 
q z D  . p Z D  q 
~ q  ZD ~ p Z D  , p  ZD q 
~ p  ZD » p  ZD q 
P ZD q ZD p  ZD p
29.3. I n  t h e  s y s te m  P A, u s e  t h e  m e t h o d  o f t r u t h - t a b l e s  t o  e s t a b l i s h  t h e  
i n d e p e n d e n c e  o f t h e  t h r e e  a x i o m s  a n d  t h e  r u le  o f m o d u s  ponens.  ( E x c e p t  in  
o n e  c a s e , t h a t  o f  t h e  f i r s t  a x i o m , a  s y s te m  o f tw o  t r u t h - v a l u e s  is  s u f f ic i e n t.)
29.4.  U s e  t h e  r e s u l t  o f 2 9 .2  t o  e s t a b li s h  t h e  c o m p le te n e s s  o f t h e  s y s te m  
P j o f  p r o p o s i t i o n a l  c a lc u lu s  in  w h ic h  t h e  p r i m i t i v e  c o n n e c t iv e s  a n d  th e  
r u le s  o f  in f e r e n c e  a r e  t h e  s a m e  a s  fo r P H (se e  §2G) a n d  t h e  a x io m s  a r e  th e  
n in e  f o llo w in g :
p V q  =  * p Z D q Z D q  
p  ZD q ZD m q  V  m p  ZD r  
i> =  q ^ ) . p z y q  
fi =  qv.qvj> 
f i = >  , q  =  P ~ q  
p = > . p q  =  q 
p  DD . q  ZD .  T ZD p  
P =5 ~ p  ZD q 
p q z D  p
( T h is  s y s t e m — m i n im iz i n g  t h e  le n g t h  o f  t h e  s e p a r a t e  a x io m s  r a t h e r  t h a n  
t h e  n u m b e r  o f a x io m s — is  d u e  t o  S t a n i s l a w  J a n k o w s k i , m  S l u d i a  Soci et at i s 
S c ie n tia r u m  T o ru n e n sis, v o l. 1 n o . 1 (1 9 4 8 ).)
* 9 - 5 -  D is c u s s  t h e  i n d e p e n d e n c e  o f t h e  a x i o m s  o f  P j.

---


III. Functional Calculi o f First Order
