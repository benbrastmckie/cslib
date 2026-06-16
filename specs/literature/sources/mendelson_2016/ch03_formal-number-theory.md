<!-- Source: Mendelson, E. (2016). Introduction to Mathematical Logic (6th ed). Chapter 3: Formal Number Theory (pages 153-230). BibKey: not yet in references.bib -->

3.1  An Axiom System
Together with geometry, the theory of numbers is the most immediately intui-
tive of all branches of mathematics. It is not surprising, then, that attempts to 
formalize mathematics and to establish a rigorous foundation for mathemat-
ics should begin with number theory. The first semiaxiomatic presentation of 
this subject was given by Dedekind in 1879 and, in a slightly modified form, 
has come to be known as Peano’s postulates.* It can be formulated as follows:
(P1) 0 is a natural number.†
(P2) If x is a natural number, there is another natural number denoted 
by x′ (and called the successor of x).‡
(P3) 0 ≠ x′ for every natural number x.
(P4) If x′ =  y′, then x = y.
(P5) If Q is a property that may or may not hold for any given natural 
number, and if (I) 0 has the property Q and (II) whenever a natural 
number x has the property Q, then x′ has the property Q, then 
all natural numbers have the property Q (mathematical induction 
principle).
These axioms, together with a certain amount of set theory, can be used to 
develop not only number theory but also the theory of rational, real, and 
complex numbers (see Mendelson, 1973). However, the axioms involve cer-
tain intuitive notions, such as “property,” that prevent this system from 
being a rigorous formalization. We therefore shall build a first-order theory 
S that is based upon Peano’s postulates and seems to be adequate for the 
proofs of all the basic results of elementary number theory.
The language LA of our theory S will be called the language of arithmetic. 
LA has a single predicate letter A1
2. As usual, we shall write t = s for A t s
1
2( , ). 
*	 For historical information, see Wang (1957).
†	 The natural numbers are supposed to be the nonnegative integers 0, 1, 2, … .
‡	 The intuitive meaning of x′ is x + 1.



154
Introduction to Mathematical Logic
LA has one individual constant a1. We shall use 0 as an alternative notation 
for a1. Finally, LA has three function letters, f
f
1
1
1
2
,
, and f2
2. We shall write (t′) 
instead of f
t
t
s
1
1( ), (
)
+
 instead of f
t s
1
2( , ), and (t s⋅) instead of f
t s
2
2( , ). However, 
we shall write t′, t + s, and t s⋅ instead of (t′), (t + s), and (t s⋅) whenever this 
will cause no confusion.
The proper axioms of S are
(S1)	 x1 = x2 ⇒ (x1 = x3 ⇒ x2 = x3)
(S2)	 x1 = x2 ⇒ x1′ = x2′
(S3)	 0 ≠ x1′
(S4)	 x1′ = x2′ ⇒ x1 = x2
(S5)	 x1 + 0 = x1
(S6)	 x1 + x2′ = (x1 + x2)′
(S7)	 x1 0
⋅ = 0
(S8)	 x
x
x
x
x
1
2
1
2
1
⋅
′ =
⋅
+
(
)
(
)
(S9)	 B (0) ⇒ ((∀x)(B (x) ⇒ B (x′)) ⇒ (∀x)B (x)) for any wf B (x) of S.
We shall call (S9) the principle of mathematical induction. Notice that axioms 
(S1)–(S8) are particular wfs, whereas (S9) is an axiom schema providing an 
infinite number of axioms.*
Axioms (S3) and (S4) correspond to Peano postulates (P3) and (P4), respec-
tively. Peano’s axioms (P1) and (P2) are taken care of by the presence of 0 as 
an individual constant and f1
1 as a function letter. Our axioms (S1) and (S2) 
furnish some needed properties of equality; they would have been assumed 
as intuitively obvious by Dedekind and Peano. Axioms (S5)–(S8) are the 
recursion equations for addition and multiplication. They were not assumed 
by Dedekind and Peano because the existence of operations + and · satisfy-
ing (S5)–(S8) is derivable by means of intuitive set theory, which was presup-
posed as a background theory (see Mendelson, 1973, Chapter 2, Theorems 
3.1 and 5.1).
Any theory that has the same theorems as S is often referred to in the lit-
erature as Peano arithmetic, or simply PA.
From (S9) by MP, we can obtain the induction rule:
	
B
B
B
B
0( )
∀
(
)
( ) ⇒
( )
(
)
∀
(
)
( )
′
,
.
x
x
x
x
x
⊢s
It will be our immediate aim to establish the usual rules of equality; that is, 
we shall show that the properties (A6) and (A7) of equality (see page 93) are 
derivable in S and, hence, that S is a first-order theory with equality.
*	 However, (S9) cannot fully correspond to Peano’s postulate (P5), since the latter refers intui-
tively to the 2
0
ℵ properties of natural numbers, whereas (S9) can take care of only the denu-
merable number of properties defined by wfs of LA.



155
Formal Number Theory
First, for convenience and brevity in carrying out proofs, we cite some 
immediate, trivial consequences of the axioms.
Lemma 3.1
For any terms t, s, r of LA, the following wfs are theorems of S.
(S1′)	 t = r ⇒ (t = s ⇒ r = s)
(S2′)	 t = r ⇒ t′ = r′
(S3′)	 0 ≠ t′
(S4′)	 t′ = r′ ⇒ t = r
(S5′)	 t + 0 = t
(S6′)	 t + r′ = (t + r)′
(S7′)	 t⋅
=
0
0
(S8′)	 t r
t r
t
⋅′ =
⋅
+
(
)
Proof
(S1′)–(S8′) follow from (S1)–(S8), respectively. First form the closure by means 
of Gen, use Exercise 2.48 to change all the bound variables to variables not 
occurring in terms t, r, s, and then apply rule A4 with the appropriate terms 
t, r, s.*
Proposition 3.2
For any terms t, s, r, the following wfs are theorems of S.
	 a.	 t = t
	 b.	 t = r ⇒ r = t
	 c.	 t = r ⇒ (r = s ⇒ t = s)
	 d.	 r = t ⇒ (s = t ⇒ r = s)
	 e.	 t = r ⇒ t + s = r + s
	 f.	 t = 0 + t
	 g.	 t′ + r = (t + r)′
	 h.	 t + r = r + t
	 i.	 t = r ⇒ s + t = s + r
	
j.	 (t + r) + s = t + (r + s)
*	 The change of bound variables is necessary in some cases. For example, if we want to obtain 
x2 = x1 ⇒ x2′ = x1′ from x1 = x2 ⇒ x1′ = x2′, we first obtain (∀x1)(∀x2)(x1 = x2 ⇒ x1′ = x2′). We can-
not apply rule A4 to drop (∀x1) and replace x1 by x2, since x2 is not free for x1 in (∀x2)(x1 = x2 ⇒ 
x1′ = x2′). From now on, we shall assume without explicit mention that the reader is aware that 
we sometimes have to change bound variables when we use Gen and rule A4.



156
Introduction to Mathematical Logic
	 k.	 t = r ⇒t s⋅ = r s⋅
	 l.	 0
0
⋅=
t
	 m.	
′⋅
= ⋅+
t r
t r
r
	 n.	 t r
r t
⋅
=
⋅
	 o.	 t
r
s t
s r
=
⇒⋅= ⋅
Proof
	
a.	 1.	 t + 0 = t	
(S5′)
	
	
2.	 (t + 0 = t) ⇒ (t + 0 = t ⇒ t = t)	
(S1′)
	
	
3.	 t + 0 = t ⇒ t = t	
1, 2, MP
	
	
4.	 t = t	
1, 3, MP
	
b.	 1.	 t = r ⇒ (t = t ⇒ r = t)	
(S1′)
	
	
2.	 t = t ⇒ (t = r ⇒ r = t)	
1, tautology, MP
	
	
3.	 t = r ⇒ r = t	
2, part (a), MP
	
c.	 1.	 r = t ⇒ (r = s ⇒ t = s)	
(S1′)
	
	
2.	 t = r ⇒ r = t	
Part (b)
	
	
3.	 t = r ⇒ (r = s ⇒ t = s)	
1, 2, tautology, MP
	
d.	 1.	 r = t ⇒ (t = s ⇒ r = s)	
Part (c)
	
	
2.	 t = s ⇒ (r = t ⇒ r = s)	
1, tautology, MP
	
	
3.	 s = t ⇒ t = s	
Part (b)
	
	
4.	 s = t ⇒ (r = t ⇒ r = s)	
2, 3, tautology, MP
	
e.	 Apply the induction rule to B (z): x = y ⇒ x + z = y + z.
	
	
i.	 1.	 x + 0 = x	
(S5′)
	
	
	
2.	 y + 0 = y	
(S5′)
	
	
	
3.	 x = y	
Hyp
	
	
	
4.	 x + 0 = y	
1, 3, part (c), MP
	
	
	
5.	 x + 0 = y + 0	
4, 2, part (d), MP
	
	
	
6.	 ⊢S x = y ⇒ x + 0 = y + 0	
1–5, deduction theorem
	
	
Thus, ⊢S B (0).
	
	
ii.	 1.	 x = y ⇒ x + z = y + z	
Hyp
	
	
	
2.	 x = y	
Hyp
	
	
	
3.	 x + z′ = (x + z)′	
(S6′)
	
	
	
4.	 y + z′ = (y + z)′	
(S6′)
	
	
	
5.	 x + z = y + z	
1, 2, MP
	
	
	
6.	 (x + z)′ = (y + z)′	
5, (S2′), MP
	
	
	
7.	 x + z′ = (y + z)′	
3, 6, part (c), MP
	
	
	
8.	 x + z′ = y + z′	
4, 7, part (d), MP
	
	
	
9.	 ⊢S (x = y ⇒ x + z = y + z) ⇒	 1–8, deduction theorem twice
	
	
	
	
(x = y ⇒ x + z′ = y + z′)
Thus, ⊢S B (z) ⇒ B (z′), and, by Gen, ⊢S(∀z)(B (z) ⇒ B (z′)). Hence, 
⊢S(∀z)B (z) by the induction rule. Therefore, by Gen and rule A4, 
⊢S t = r ⇒ t + s = r + s.



157
Formal Number Theory
	
f.	 Let B (x) be x = 0 + x.
	
	
i.	 ⊢S 0 = 0 + 0 by (S5′), part (b) and MP; thus, ⊢S B (0).
	
	
ii.	 1.	 x = 0 + x	
Hyp
	
	
	
2.	 0 + x′ = (0 + x)′	
(S6′)
	
	
	
3.	 x′ = (0 + x)′	
1, (S2′), MP
	
	
	
4.	 x′ = 0 + x′	
3, 2, part (d), MP
	
	
	
5.	 ⊢S x = 0 + x ⇒ x′ = 0 + x′	
1–4, deduction theorem
	
	
Thus, ⊢S B (x) ⇒ B (x′) and, by Gen, ⊢S (∀x)(B (x) ⇒ B (x′)). So, by (i), 
(ii) and the induction rule, ⊢S (∀x)(x = 0 + x), and then, by rule A4, 
⊢S t = 0 + t.
	
g.	 Let B (y) be x′ + y =(x + y)′.
	
	
i.	 1.	 x′ + 0 = x′	
(S5′)
	
	
	
2.	 x + 0 = x	
(S5′)
	
	
	
3.	 (x + 0)′ = x′	
2, (S2′), MP
	
	
	
4.	 x′ + 0 =(x + 0)′	
1, 3, part (d), MP
	
	
Thus, ⊢S B (0).
	
	
ii.	 1.	 x′ + y = (x + y)′	
Hyp
	
	
	
2.	 x′ + y′ = (x′ + y)′	
(S6′)	
	
	
	
3.	 (x′ + y)′ = (x + y)″	
1, (S2′), MP
	
	
	
4.	 x′ + y′ = (x + y)″	
2, 3, part (c), MP
	
	
	
5.	 x + y′ = (x + y)′	
(S6′)
	
	
	
6.	 (x + y′)′ = (x + y)″	
5, (S2′), MP
	
	
	
7.	 x′ + y′ = (x + y′)′	
4, 6, part (d), MP
	
	
	
8.	 ⊢S x′ + y = (x + y)′ ⇒	
1–7, deduction theorem
	
	
	
	
x′ + y′ = (x + y′)′
	
	
Thus, ⊢S B (y) ⇒ B (y′), and, by Gen, ⊢S (∀y)(B (y) ⇒ B (y′)). Hence, by 
(i), (ii), and the induction rule, ⊢S (∀y)(x′ + y =(x + y)′). By Gen and 
rule A4, ⊢S t′ + r = (t + r)′.
	
h.	 Let B (y) be x + y = y + x.
	
	
i.	 1.	 x + 0 = x	
(S5′)
	
	
	
2.	 x = 0 + x	
Part (f)
	
	
	
3.	 x + 0 = 0 + x	
1, 2, part (c), MP
	
	
Thus, ⊢S B (0).
	
	
ii.	 1.	 x + y = y + x	
Hyp
	
	
	
2.	 x + y′ =(x + y)′	
(S6′)
	
	
	
3.	 y′ + x =(y + x)′	
Part (g)
	
	
	
4.	 (x + y)′ = (y + x)′	
1, (S2′), MP
	
	
	
5.	 x + y′ = (y + x)′	
2, 4, part (c), MP
	
	
	
6.	 x + y′ = y′ + x	
5, 3, part (d), MP
	
	
	
7.	 ⊢S x + y = y + x ⇒	
1–6, deduction theorem
	
	
	
	
x + y′ = y′ + x
Thus, ⊢S B (y) ⇒ B (y′) and, by Gen, ⊢S (∀y)(B (y) ⇒ B (y)′). So, by (i), 
(ii) and the induction rule, ⊢S (∀y)(x + y = y + x). Then, by rule A4, 
Gen and rule A4, ⊢S t + r = r + t.



158
Introduction to Mathematical Logic
	
i.	
1.	 t = r ⇒ t + s = r + s	
Part (e)
	
	
2.	 t + s = s + t	
Part (h)
	
	
3.	 r + s = s + r	
Part (h)
	
	
4.	 t = r	
Hyp
	
	
5.	 t + s = r + s	
1, 4, MP
	
	
6.	 s + t = r + s	
2, 5, (S1′) MP
	
	
7.	 s + t = s + r	
6, 3, part (c), MP
	
	
8.	 ⊢S t = r ⇒ s + t = s + r	
1–7, deduction theorem
	
j.	 Let B (z) be (x + y) + z = x + (y + z).
	
	
i.	 1.	
(x + y) + 0 = x + y	
(S5′)
	
	
	
2.	
y + 0 = y	
(S5′)
	
	
	
3.	
x + (y + 0) = x + y	
2, part (j), MP
	
	
	
4.	
(x + y) + 0 = x + (y + 0)	
1, 3, part (d), MP
	
	
Thus, ⊢S B (0).
	
	
ii.	 1.	 (x + y) + z = x + (y + z)	
Hyp
	
	
	
2.	 (x + y) + z′ =((x + y) + z)′	
(S6′)
	
	
	
3.	 ((x + y) + z)′ =(x +(y + z))′	
1, (S2′), MP
	
	
	
4.	 (x + y) + z′ =(x +(y + z))′	
2, 3, part (c), MP
	
	
	
5.	 y + z′ = (y + z)′	
(S6′)
	
	
	
6.	 x + (y + z′) = x + (y + z)′	
5, part (i), MP
	
	
	
7.	 x + (y + z)′ = (x + (y + z))′	
(S6′)
	
	
	
8.	 x +(y + z′) = (x + (y + z))′	
6, 7, part (c), MP
	
	
	
9.	 (x + y) + z′ = x + (y + z′)	
4, 8, part (d), MP
	
	
	
10.	 ⊢S (x + y) + z = x + (y + z) ⇒	
1–9, deduction theorem
	
	
	
	
(x + y) + z′ = x +(y + z′)
Thus, ⊢S B (z) ⇒ B (z′) and, by Gen, ⊢S (∀z)(B (z)) ⇒ (B (z′)). So, by (i), (ii) and 
the induction rule, ⊢S (∀z)B (z), and then, by Gen and rule A4, ⊢S (t + r) + s = 
t + (r + s).
Parts (k)–(o) are left as exercises.
Corollary 3.3
S is a theory with equality.
Proof
By Proposition 2.25, this reduces to parts (a)–(e), (i), (k) and (o) of proposition 
3.2, and (S2′).
Notice that the interpretation in which
	
a.	 The set of nonnegative integers is the domain
	
b.	 The integer 0 is the interpretation of the symbol 0



159
Formal Number Theory
	
c.	 The successor operation (addition of 1) is the interpretation of the ′ 
function (that is, of f1
1)
	
d.	 Ordinary addition and multiplication are the interpretations of + 
and ·
	
e.	 The interpretation of the predicate letter = is the identity relation
is a normal model for S. This model is called the standard interpretation or 
standard model. Any normal model for S that is not isomorphic to the stan-
dard model will be called a nonstandard model for S.
If we recognize the standard interpretation to be a model for S, then, of 
course, S is consistent. However, this kind of semantic argument, involving 
as it does a certain amount of set-theoretic reasoning, is regarded by some 
as too precarious to serve as a basis for consistency proofs. Moreover, we 
have not proved in a rigorous way that the axioms of S are true under the 
standard interpretation, but we have taken it as intuitively obvious. For these 
and other reasons, when the consistency of S enters into the argument of a 
proof, it is common practice to take the statement of the consistency of S as 
an explicit unproved assumption.
Some important additional properties of addition and multiplication are 
covered by the following result.
Proposition 3.4
For any terms t, r, s, the following wfs are theorems of S.
	
a.	 t
r
s
t r
t s
⋅
+
=
⋅
+
⋅
(
)
(
)
(
) (distributivity)
	
b.	 (
)
(
)
(
)
r
s t
r t
s t
+
⋅=
⋅
+
⋅ (distributivity)
	
c.	 (
)
(
)
t r
s
t
r s
⋅
⋅= ⋅
⋅
 (associativity of ·)
	
d.	 t + s = r + s ⇒ t = r (cancellation law for +)
Proof
	
a.	 Prove ⊢S x · (y + z) = (x · y) + (x · z) by induction on z.
	
b.	 Use part (a) and Proposition 3.2(n).
	
c.	 Prove ⊢S (x · y) · z = x · (y · z) by induction on z.
	
d.	 Prove ⊢S x + z = y + z ⇒ x = y by induction on z. This requires, for the 
first time, use of (S4′).
The terms 0, 0′, 0″, 0″′, … we shall call numerals and denote by 0 1 2 3
, , , , … 
More precisely, 0 is 0 and, for any natural number n n
,
+1 is (n)′. In general, 
if n is a natural number, n stands for the numeral consisting of 0 followed 
by n strokes. The numerals can be defined recursively by stating that 0 is a 
numeral and, if u is a numeral, then u′ is also a numeral.



160
Introduction to Mathematical Logic
Proposition 3.5
The following are theorems of S.
	
a.	 t
t
+
= ′
1
	
b.	 t
t
⋅
=
1
	
c.	 t
t
t
⋅
= +
2
	
d.	 t + s = 0 ⇒ t = 0 ∧ s = 0
	
e.	 t ≠ 0 ⇒ (s · t = 0 ⇒ s = 0)
	
f.	 t
s
t
s
t
s
+
=
⇒
=
∧
=
∨
=
∧
=
1
0
1
1
0
(
)
(
)
	
g.	 t s
t
s
⋅=
⇒
=
∧
=
1
1
1
(
)
	
h.	 t ≠ 0 ⇒ (∃y)(t = y′)
	
i.	 s ≠ 0 ⇒ (t · s = r · s ⇒ t = r)
	
j.	 t ≠ 0 ⇒ (t ≠ 1 ⇒ (∃y)(t = y″))
Proof
	
a.	 1.	 t + 0′ = (t + 0)′	
(S6′)
	
	
2.	 t + 0 = t	
(S5′)
	
	
3.	 (t + 0)′ = t′	
2, (S2′), MP
	
	
4.	 t + 0′ = t′	
1, 3, Proposition 3.2(c), MP
	
	
5.	 t
t
+
= ′
1
	
4, abbreviation
	
b.	 1.	 t · 0′ = t · 0 + t	
(S8′)
	
	
2.	 t · 0 = 0	
(S7′)
	
	
3.	 t · 0 + t = 0 + t	
2, Proposition 3.2(e), MP
	
	
4.	 t · 0′ = 0 + t	
1, 3, Proposition 3.2(c), MP
	
	
5.	 0 + t = t	
Proposition 3.2(f, b), MP
	
	
6.	 t · 0′ = t	
4, 5, Proposition 3.2(c), MP
	
	
7.	 t
t
⋅
=
1
	
6, abbreviation
	
c.	 1.	 t
t
t
⋅
′=
⋅
(
) +
( )
1
1
	
(S8′)
	
	
2.	 t
t
⋅
=
1
	
Part (b)
	
	
3.	
t
t
t
t
⋅
(
) + = +
1
	
2, Proposition 3.2(e), MP
	
	
4.	 t
t
t
⋅( )′= +
1
	
1, 3, Proposition 3.2(c), MP
	
	
5.	 t
t
t
⋅
= +
2
	
4, abbreviation
	
d.	 Let B (y) be x + y = 0 ⇒ x = 0 ∧ y = 0. It is easy to prove that ⊢S B (0). 
Also, since ⊢S (x + y)′ ≠ 0 by (S3′) and Proposition 3.2(b), it follows 
by (S6′) that ⊢S x + y′ ≠ 0. Hence, ⊢S B (y′) by the tautology ¬A ⇒ 
(A ⇒ B). So, ⊢S B (y) ⇒ B (y′) by the tautology A ⇒ (B ⇒ A). Then, by 
the induction rule, ⊢S (∀y)B (y) and then, by rule A4, Gen and rule 
A4, we obtain the theorem.
	
e.	 The proof is similar to that for part (d) and is left as an exercise.
	
f.	 Use induction on y in the wf x
y
x
y
x
y
+
= ⇒
= ∧
=
∨
=
∧
=
1
0
1
1
0
((
)
(
)).
	
g.	 Use induction on y in x y
x
y
⋅
=
⇒
=
∧
=
1
1
1
(
).
	
h.	 Perform induction on x in x ≠ 0 ⇒ (∃w)(x = w′).



161
Formal Number Theory
	
i.	 Let B (y) be (∀x)(z ≠ 0 ⇒ (x · z = y · z ⇒ x = y)).
	
	
i.	 1.	 z ≠ 0	
Hyp
	
	
	
2.	 x · z = 0 · z	
Hyp
	
	
	
3.	 0 · z = 0	
Proposition 3.2(l)
	
	
	
4.	 x · z = 0	
2, 3 Proposition 3.2(c), MP
	
	
	
5.	 x = 0	
1, 4, part(e), MP
	
	
	
6.	 ⊢S z ≠ 0 ⇒ (x · z = 0 · z ⇒ x = 0)	
1–5, deduction theorem
	
	
	
7.	 ⊢S (∀z)(z ≠ 0 ⇒ (x · z = 0 · z 	
6, Gen
	
	
	
	 	
⇒ x = 0))
	
	
	
	Thus, ⊢S B (0).
	
	
ii.	1.	 (∀x)(z ≠ 0 ⇒ (x · z = y · z ⇒ x = y))	
Hyp (B (y))
	
	
	
2.	 z ≠ 0	
Hyp
	
	
	
3.	 x · z = y′ · z	
Hyp
	
	
	
4.	 y′ ≠ 0	
(S3′), Proposition 3.2(b), MP
	
	
	
5.	 y′ · z ≠ 0	
2, 4, part (e), a tautology, MP
	
	
	
6.	 x · z ≠ 0	
3, 5, (S1′), tautologies, MP
	
	
	
7.	 x ≠ 0	
6, (S7′), Proposition 3.2(o, n),
	
	
(S1′), tautologies, MP
	
	
	
8.	 (∃w)(x = w′)	
7, part (h), MP
	
	
	
9.	 x = b′	
8, rule C
	
	
	 10.	 b′ · z = y′ · z	
3, 9, (A7), MP
	
	
	 11.	 b · z + z = y · z + z	
10, Proposition 3.2(m, d), MP
	
	
	 12.	 b · z = y · z	
11, Proposition 3.4(d), MP
	
	
	 13.	 z ≠ 0 ⇒ (b · z = y · z ⇒ b = y)	
1, rule A4
	
	
	 14.	 b · z = y · z ⇒ b = y	
2, 13, MP
	
	
	 15.	 b = y	
12, 14, MP
	
	
	 16.	 b′ = y′	
15, (S2′), MP
	
	
	 17.	 x = y′	
9, 16, Proposition 3.2(c), MP
	
	
	 18.	 B (y), z ≠ 0, x · z = y′ · z ⊢S x = y′	
1–17, Proposition 2.10
	
	
	 19.	 B (y) ⊢S z ≠ 0 ⇒	
18, deduction theorem twice
	
	
	 	
(x · z = y′ · z ⇒ x = y′)
	
	
	 20.	 B (y) ⊢S(∀x)(z ≠ 0 ⇒	
19, Gen
	
	
	 	
(x · z = y′ · z ⇒ x = y′))
	
	
	 21.	 ⊢S B (y) ⇒ B (y′)	
20, deduction theorem
	
	
Hence, by (i), (ii), Gen, and the induction rule, we obtain ⊢S(∀y)B (y) 
and then, by Gen and rule A4, we have the desired result.
	
j.	 This is left as an exercise.
Proposition 3.6
	
a.	 Let m and n be any natural numbers.
	
	
i.	 If m ≠ n, then ⊢S m
n
≠
.
	
	
ii.	 ⊢S m
n
m
n
+
=
+  and ⊢S m n
m n
⋅
=
⋅.



162
Introduction to Mathematical Logic
	
b.	
Any model for S is infinite.
	
c.	
For any cardinal number ℵβ, S has a normal model of cardinality ℵβ.
Proof
	
a.	 i.	 Assume m ≠ n. Either m < n or n < m. Say, m < n.
	
	
	
1.	 m
n
=
	
Hyp
	
	
	
2.	
m
n
times
times




 




′′
′
… = ′′′
′
…
0
0
	
1 is an abbreviation of 2
	
	
	
3.	 Apply (S4′) and MP m times in a row. We get 
n
m
Let
−
= ′′
′
…
times





0
0
 be 
n
m
−
−1. Since n > m, n −m −1 ≥ 0. Thus, we obtain 0 = t′.
	
	
	
4.	 0 ≠ t′	
(S3′)
	
	
	
5.	 0 = t′ ∧ 0 ≠ t′	
3, 4, conjunction introduction
	
	
	
6.	
⊢
m
n
t
t
=
= ′ ∧
≠
S 0
0
	
1–5
	
	
	
7.	 ⊢S m
n
≠
	
1–6, proof by contradiction
	
	
	
A similar proof holds in the case when n < m. (A more rigor-
ous proof can be given by induction in the metalanguage with 
respect to n.)
	
	
ii.	 We use induction in the metalanguage. First, m + 0 is m. 
Hence, ⊢S m +
=
0
 m + 0 by (S5′). Now assume ⊢S m
n
m
n
+
=
+ . 
Then ⊢S m
n
m
n
+
(
)′ =
+
′
( )  by (S2′) and (S6′). But m
n
+
+
(
)1  
is 
m
n
+
(
)′  and n +1 is n
( )′. Hence, ⊢S m
n
m
n
+
+
(
) =
+
+
(
)
1
1 . 
Thus, ⊢S m
n
m
n
+
=
+ . The proof that ⊢S m n
m n
⋅
=
⋅ is left as an 
exercise.
	
b.	 By part (a), (i), in a model for S the objects corresponding to the 
numerals must be distinct. But there are denumerably many 
numerals.
	
c.	 This follows from Corollary 2.34(c) and the fact that the standard 
model is an infinite normal model.
An order relation can be introduced by definition in S.
Definitions
	
t
s
w
w
w
t
s
t
s
t
s
t
s
t
s
s
t
t
s
s
t
t
s
<
∃
≠
∧
+ =
(
)
≤
< ∨=
>
<
≥
≤
/<
for
for
for
for
fo
(
)
0
r
and so on
¬
<
(
),
t
s
In the first definition, as usual, we choose w to be the first variable not in t or s.



163
Formal Number Theory
Proposition 3.7
For any terms t, r, s, the following are theorems.
	 a.	 t /< t
	 b.	 t < s ⇒ (s < r ⇒ t < r)
	 c.	 t < s ⇒ s /< t
	 d.	 t < s ⇔ t + r < s + r
	 e.	 t ≤ t
	
f.	 t ≤ s ⇒ (s ≤ r ⇒ t ≤ r)
	 g.	 t ≤ s ⇔ t + r ≤ s + r
	 h.	 t ≤ s ⇒ (s < r ⇒ t < r)
	
i.	 0 ≤ t
	
j.	 0 < t′
	 k.	 t < r ⇔ t′ ≤ r
	
l.	 t ≤ r ⇔ t < r′
	 m.	 t < t′
	 n.	 0
1 1
2 2
3
<
<
<
…
,
,
,
	 o.	 t ≠ r ⇒ (t < r ∨ r < t)
	 p.	 t = r ∨ t < r ∨ r < t
	 q.	 t ≤ r ∨ r ≤ t
	
r.	 t + r ≥ t
	 s.	 r ≠ 0 ⇒ t + r > t
	
t.	 r ≠ 0 ⇒ t · r ≥ t
	 u.	 r ≠ 0 ⇔ r > 0
	 v.	 r > 0 ⇒ (t > 0 ⇒ r · t > 0)
	 w.	 r ≠ 0 ⇒ (t > 1 ⇒ t · r > r)
	 x.	 r ≠ 0 ⇒ (t < s ⇔ t · r < s · r)
	 y.	 r ≠ 0 ⇒ (t ≤ s ⇔ t · r ≤ s · r)
	 z.	 t /< 0
	 z′.	 t ≤ r ∧ r ≤ t ⇒ t = r
Proof
	
a.	 1.	 t < t 	
Hyp
	
	
2.	 (∃w)(w ≠ 0 ∧ w + t = t)	
1 is an abbreviation of 2
	
	
3.	 b ≠ 0 ∧ b + t = t	
2, rule C
	
	
4.	 b + t = t	
3, conjunction rule
	
	
5.	 t = 0 + t	
Proposition 3.2(f)
	
	
6.	 b + t = 0 + t	
3, 4, Proposition 3.2(c), MP
	
	
7.	 b = 0	
6, Proposition 3.4(d), MP
	
	
8.	 b ≠ 0	
3, conjunction elimination
	
	
9.	 b = 0 ∧ b ≠ 0	
7, 8, conjunction elimination
	
	 10.	 0 = 0 ∧ 0 ≠ 0	
9, tautology: B ∧ ¬B ⇒ C, MP
	
	 11.	 t < t ⊢S 0 = 0 ∧ 0 ≠ 0	
1–10, Proposition 2.10
	
	 12.	 ⊢S t /< t	
1–11, proof by contradiction



164
Introduction to Mathematical Logic
	
b.	 1.	 t < s	
Hyp
	
	
2.	 s < r	
Hyp
	
	
3.	 (∃w)(w ≠ 0 ∧ w + t = s)	
1 is an abbreviation of 3
	
	
4.	 (∃v)(v ≠ 0 ∧ v + s = r)	
2 is an abbreviation of 4
	
	
5.	 b ≠ 0 ∧ b + t = s	
3, rule C
	
	
6.	 c ≠ 0 ∧ c + s = r	
4, rule C
	
	
7.	 b + t = s	
5, conjunction elimination
	
	
8.	 c + s = r	
6, conjunction elimination
	
	
9.	 c + (b + t) = c + s	
7, Proposition 3.2(i), MP
	
	 10.	 c + (b + t) = r	
9, 8, Proposition 3.2(c), MP
	
	 11.	 (c + b) + t = r	
10, Proposition 3.2(j, c), MP
	
	 12.	 b ≠ 0	
5, conjunction elimination
	
	 13.	 c + b ≠ 0	
12, Proposition 3.5(d), tautology, MP
	
	 14.	 c + b ≠ 0 ∧ (c + b) + t = r	
13, 11, conjunction introduction
	
	 15.	 (∃u)(u ≠ 0 ∧ u + t = r)	
14, rule E4
	
	 16.	 t < r	
Abbreviation of 15
	
	 17.	 ⊢S t < s ⇒ (s < r ⇒ t < r)	
1–15, Proposition 2.10,
	
deduction theorem
Parts (c)–(z′) are left as exercises.
Proposition 3.8
	
a.	 For any natural number k
x
x
k
x
k
,
.
⊢S
=
∨… ∨
=
⇔
≤
0
	
a′.	 For any natural number k and any wf B
B
B
B
,
( )
( )
( )
⊢S
0
1
∧
∧… ∧
⇔
k
	
	
(
)(
( )).
∀
≤
⇒
x x
k
x
B
	
b.	 For any natural number k
x
x
k
x
k
>
=
∨… ∨
=
−
⇔
<
0
0
1
,
(
)
⊢S
	
b′.	 For any natural number k > 0 and any wf B
B
,
( )
⊢S
0 ∧ 
B
B
B
( )
(
)
(
)(
( )).
1
1
∧… ∧
−
⇔∀
<
⇒
k
x x
k
x
	
c.	 ⊢S ((∀x)(x < y ⇒ B (x)) ∧ (∀x)(x ≥ y ⇒ C (x))) ⇒ (∀x)(B (x) ∨ C (x))
Proof
	
a.	 We prove ⊢S x
x
k
x
k
=
∨… ∨
=
⇔
≤
0
 by induction in the metalan-
guage on k. The case for 
⊢
k
x
x
=
=
⇔
≤
0
0
0
,
S
, is obvious from the 
definitions and Proposition 3.7, Assume as inductive hypothesis 
⊢S x
x
k
x
k
=
∨… ∨
=
⇔
≤
0
. Now assume x
x
k
x
k
=
∨… ∨
=
∨
=
+
0
1. 
But 
⊢S x
k
x
k
=
+
⇒
≤
+
1
1  and, by the inductive hypothesis, 
⊢S x
x
k
x
k
=
∨… ∨
=
⇒
≤
0
. Also ⊢S x
k
x
k
≤
⇒
≤
+1. Thus, x
k
≤
+1. So, 
⊢S x
x
k
x
k
x
k
=
∨… ∨
=
∨
=
+ ⇒
≤
+
0
1
1. Conversely, assume x
k
≤
+1. 
Then x
k
k
x
=
+
+
∨
<
1
1. If x
k
=
+1, then x
x
k
x
k
=
∨… ∨
=
∨
=
+
0
1. 
If x
k
<
+1, then since k +1 is ( ) ,
k ′  we have x
k
≤
 by Proposition 
3.7(l). By the inductive hypothesis, x
x
k
=
∨… ∨
=
0
, and, therefore, 



165
Formal Number Theory
x
x
k
x
k
=
∨… ∨
=
∨
=
+
0
1. In either case, x
x
k
x
k
=
∨… ∨
=
∨
=
+
0
1. 
This proves ⊢S x
k
≤
+
⇒
1
 x
x
k
x
k
=
∨… ∨
=
∨
=
+
0
1. From the induc-
tive hypothesis, we have derived ⊢S x
x
k
x
k
=
∨… ∨
=
+
⇔
≤
+
0
1
1 
and this completes the proof. (This proof has been given in an infor-
mal manner that we shall generally use from now on. In particular, 
the deduction theorem, the eliminability of rule C, the replacement 
theorem, and various derived rules and tautologies will be applied 
without being explicitly mentioned.)
Parts (a′), (b), and (b′) follow easily from part (a). Part (c) follows almost imme-
diately from Proposition 3.7(o), using obvious tautologies.
There are several other forms of the induction principle that we can prove 
at this point.
Proposition 3.9
	
a.	 Complete induction. ⊢S (∀x)((∀z)(z < x ⇒ B (z)) ⇒ B (x)) ⇒ (∀x)B (x). In ordi-
nary language, consider a property P such that, for any x, if P holds for 
all natural numbers less than x, then P holds for x also. Then P holds 
for all natural numbers.
	
b.	 Least-number principle. ⊢S (∃x)B (x) ⇒ (∃y)B (y) ∧ (∀z)(z < y ⇒ ¬B (z)). If a 
property P holds for some natural number, then there is a least number 
satisfying P.
Proof
	
a.	 Let C (x) be (∀z)(z ≤ x ⇒ B (z)).
	
	
i.	 1.	 (∀x)((∀z)(z < x ⇒ B (z)) ⇒ B (x))	
Hyp
	
	
	
2.	 (∀z)(z < 0 ⇒ B (z)) ⇒ B (0)	
1, rule A4
	
	
	
3.	 z /< 0	
Proposition 3.7(y)
	
	
	
4.	 (∀z)(z < 0 ⇒ B (z))	
3, tautology, Gen
	
	
	
5.	 B (0)	
2, 4, MP
	
	
	
6.	 (∀z)(z ≤ 0 ⇒ B (z)) i.e., C (0)	
5, Proposition 3.8(a′)
	
	
	
7.	 (∀x)((∀z)(z < x ⇒ B (z))	
1–6
	
	
	
	 ⇒ B (x)) ⊢S C (0)
	
	
ii.	 1.	 (∀x)((∀z)(z < x ⇒ B (z)) ⇒ B (x))	
Hyp
	
	
	
2.	 C (x), i.e., (∀z)(z ≤ x ⇒ B (z))	
Hyp
	
	
	
3.	 (∀z)(z < x′ ⇒ B (z))	
2, Proposition 3.7(ℓ)
	
	
	
4.	 (∀z)(z < x′ ⇒ B (z)) ⇒ B (x′)	
1, rule A4
	
	
	
5.	 B (x′)	
3, 4, MP
	
	
	
6.	 z ≤ x′ ⇒ z < x′ ∨ z = x′	
Definition, tautology
	
	
	
7.	 z < x′ ⇒ B (z)	
3, rule A4



166
Introduction to Mathematical Logic
	
	
	
8.	 z = x′ ⇒ B (z)	
5, axiom (A7), Proposition
	
	
	
	 	
2.23(b), tautologies
	
	
	
9.	 (∀z)(z ≤ x′ ⇒ B (z)) i.e., C (x′)	
6, 7, 8, Tautology, Gen
	
	
	 10.	 (∀x)((∀z)(z < x ⇒ B (z)) ⇒ B (x))	
1–9, deduction theorem, Gen
	
	
	
	 ⊢S (∀x)(C (x) ⇒ C (x′))
By (i), (ii), and the induction rule, we obtain D ⊢S (∀x)C (x), that is, D ⊢S (∀x)
(∀z)(z ≤ x ⇒ B (z)), where D is (∀x)((∀z)(z < x ⇒ B (z)) ⇒ B (x)). Hence, by rule 
A4 twice, D ⊢S x ≤ x ⇒ B (x). But ⊢S x ≤ x. So, D ⊢S B (x), and, by Gen and the 
deduction theorem, ⊢S D ⇒ (∀x)B (x).
	
b.	 1.	 ¬(∃y)(B (y) ∧ (∀z)
	
	
	
(z < y ⇒ ¬B (z)))	
Hyp
	
	
2.	 (∀y) ¬(B (y) ∧ (∀z)	
1, derived rule for negation
	
	
	
(z < y ⇒ ¬B (z)))
	
	
3.	 (∀y)((∀z)(z < y ⇒	
2, tautology, replacement
	
	
	
¬B (z)) ⇒ ¬B (y))	
	
	
4.	 (∀y) ¬B (y)	
3, part (a) with ¬B instead of B
	
	
5.	 ¬(∃y)B (y)	
4, derived rule for negation
	
	
6.	 ¬(∃x)B (x)	
5, change of bound variable
	
	
7.	 ⊢S ¬(∃y)(B (y) ∧ (∀z)(z < y ⇒	
1–6, deduction theorem
	
	
	
¬B (z))) ⇒ ¬(∃x)B (x)
	
	
8.	 ⊢S(∃x)B (x) ⇒ (∃y)(B (y) ∧ (∀z)	
7, derived rule
	
	
	
(z < y ⇒ ¬B (z)))
Exercise
3.1	 (Method of infinite descent)
Prove ⊢S (∀x)(B (x) ⇒ (∃y)(y < x ∧ B (y))) ⇒ (∀x) ¬B (x)
Another important notion in number theory is divisibility, which we now 
define.
Definition
t|s for (∃z)(s = t · z). (Here, z is the first variable not in t or s.)
Proposition 3.10
The following wfs are theorems for any terms t, s, r.
	 a.	 t|t
	 b.	 1|t



167
Formal Number Theory
	 c.	 t|0
	 d.	 t|s ∧ s|r ⇒ t|r
	 e.	 s ≠ 0 ∧ t|s ⇒ t ≤ s
	
f.	 t|s ∧ s|t ⇒ s = t
	 g.	 t|s ⇒ t|(r · s)
	 h.	 t|s ∧ t|r ⇒ t|(s + r)
Proof
	
a.	 t
t
= ·1. Hence, t|t.
	
b.	 t
t
= 1· . Hence, 1| .t
	
c.	 0 = t · 0. Hence, t|0.
	
d.	 If s = t · z and r = s · w, then r = t · (z · w).
	
e.	 If s ≠ 0 and t|s, then s = t · z for some z. If z = 0, then s = 0. Hence, z ≠ 0. 
So, z = u′ for some u. Then s = t · (u′) = t · u + t ≥ t.
	 f–h.	 These proofs are left as exercises.
Exercises
3.2	 Prove ⊢S t
t
|1
1
⇒
=
.
3.3	 Prove ⊢S (t|s ∧ t|s′) ⇒ t = 1.
It will be useful for later purposes to prove the existence of a unique quo-
tient and remainder upon division of one number x by another nonzero 
number y.
Proposition 3.11
	
⊢S y
u
v
x
y u
v
v
y
u
v
x
y u
v
v
y
u
u
≠
⇒∃
(
) ∃
(
)
=
⋅
+
∧
<
∧∀
(
) ∀
(
)
=
⋅
+
∧
<
⇒
=
0
1
1
1
1
1
[
((
)
1
1
∧
=
v
v )]
Proof
Let B (x) be y ≠ 0 ⇒ (∃u)(∃v)(x = y · u + v ∧ v < y).
	
i.	 1.	
y ≠ 0	
Hyp
	
2.	 0 = y · 0 + 0	
(S5′), (S7′)
	
3.	 0 < y	
1, Proposition 3.7(t)
	
4.	 0 = y · 0 + 0 ∧ 0 < y	
2, 3, conjunction rule
	
5.	 (∃u)(∃v)(0 = y · u + v ∧ v < y)	
4, rule E4 twice
	
6.	 y ≠ 0 ⇒ (∃u)(∃v)(0 = y · u + v ∧ v < y)	
1–5, deduction theorem



168
Introduction to Mathematical Logic
	
ii.	 1.	 B (x), i.e., y ≠ 0 ⇒ (∃u)(∃v)	
Hyp
	
(x = y · u + v ∧ v < y)
	
	
2.	 y ≠ 0	
Hyp
	
	
3.	 (∃u)(∃v)(x = y · u + v ∧ v < y)	
1, 2, MP
	
	
4.	 x = y · a + b ∧ b < y	
3, rule C twice
	
	
5.	 b < y	
4, conjunction elimination
	
	
6.	 b′ ≤ y	
5, Proposition 3.7(k)
	
	
7.	 b′ < y ∨ b′ = y	
6, definition
	
	
8.	 b′ < y ⇒ (x′ = y · a + b′ ∧ b′ < y)	
4, (S6′), derived rules
	
	
9.	 b′ < y ⇒ (∃u)(∃v)(x′ = y · u + v ∧ v < y)	 8, rule E4, deduction theorem
	
	
10.	
′ =
⇒′ =
⋅+
⋅
b
y
x
y a
y 1	
4, (S6′), Proposition 3.5(b)
	
	
11.	
′ =
⇒
′ =
⋅
+
(
)
b
y
x
y
a
(
1 	
10, Proposition 3.4, 2,
	
	
	 + 0 ∧ 0 < y)	
Proposition 3.7(t), (S5′)
	
	
12.	 b′ = y ⇒ (∃u)(∃v)(x′ = y · u	
11, rule E4 twice, deduction
	
	
+ v ∧ v < y)	
theorem
	
	
13.	 (∃u)(∃v)(x′ = y · u + v ∧ v < y)	
7, 9, 12, disjunction elimination
	
	
14.	 B (x) ⇒ (y ≠ 0 ⇒ (∃u)(∃v)	
1–13, deduction theorem
	
	
(x′ = y · u + v ∧ v < y)),
	
	
i.e., B (x) ⇒ B (x′)
By (i), (ii), Gen and the induction rule, ⊢S (∀x)B (x). This establishes the exis-
tence of a quotient u and a remainder v. To prove uniqueness, proceed as 
follows. Assume y ≠ 0. Assume x = y · u + v ∧ v < y and x = y · u1 + v1 ∧ v1 < y. 
Now, u = u1 or u < u1 or u1 < u. If u = u1, then v = v1 by Proposition 3.4(d). If 
u < u1, then u1 = u + w for some w ≠ 0. Then y · u + v = y · (u + w) + v1 = y · u + 
y · w + v1. Hence, v = y · w + v1. Since w ≠ 0, y · w ≥ y. So, v = y · w + v1 ≥ y, 
contradicting v < y. Hence, u /< u1. Similarly, u1 /< u. Thus, u = u1. Since y · u + 
v = x = y · u1 + v1, it follows that v = v1.
From this point on, one can generally translate into S and prove the results 
from any text on elementary number theory. There are certain number-the-
oretic functions, such as xy and x!, that we have to be able to define in S, 
and this we shall do later in this chapter. Some standard results of number 
theory, such as Dirichlet’s theorem, are proved with the aid of the theory of 
complex variables, and it is often not known whether elementary proofs (or 
proofs in S) can be given for such theorems. The statement of some results 
in number theory involves nonelementary concepts, such as the logarithmic 
function, and, except in special cases, cannot even be formulated in S. More 
information about the strength and expressive powers of S will be revealed 
later. For example, it will be shown that there are closed wfs that are neither 
provable nor disprovable in S, if S is consistent; hence there is a wf that is 
true under the standard interpretation but is not provable in S. We also will 
see that this incompleteness of S cannot be attributed to omission of some 
essential axiom but has deeper underlying causes that apply to other theo-
ries as well.



169
Formal Number Theory
Exercises
3.4	
Show that the induction principle (S9) is independent of the other axi-
oms of S.
3.5D	 a.	 Show that there exist nonstandard models for S of any cardinality ℵα.
	
b.	 Ehrenfeucht (1958) has shown the existence of at least 2
0
ℵ mutually 
nonisomorphic models of cardinality ℵα. Prove the special case that 
there are 2
0
ℵ mutually nonisomorphic denumerable models of S.
3.6D	 Give a standard mathematical proof of the categoricity of Peano’s pos-
tulates, in the sense that any two “models” are isomorphic. Explain 
why this proof does not apply to the first-order theory S.
3.7D	 (Presburger, 1929) If we eliminate from S the function letter f2
2 for mul-
tiplication and the axioms (S7) and (S8), show that the new system S+ is 
complete and decidable (in the sense of Chapter 1, page 27).
3.8	
a.	 Show that, for every closed term t of S, we can find a natural num-
ber n such that ⊢S t
n
=
.
	
b.	 Show that every closed atomic wf t = s of S is decidable—that is, 
either ⊢S t = s or ⊢S t ≠ s.
	
c.	 Show that every closed wf of S without quantifiers is decidable.
3.2  Number-Theoretic Functions and Relations
A number-theoretic function is a function whose arguments and values are nat-
ural numbers. Addition and multiplication are familiar examples of number-
theoretic functions of two arguments. By a number-theoretic relation we mean 
a relation whose arguments are natural numbers. For example, = and < are 
binary number-theoretic relations, and the expression x + y < z determines a 
number-theoretic relation of three arguments.* Number-theoretic functions 
and relations are intuitive and are not bound up with any formal system.
Let K be any theory in the language LA of arithmetic. We say that a num-
ber-theoretic relation R of n arguments is expressible in K if and only if there 
is a wf B (x1, …, xn) of K with the free variables x1, …, xn such that, for any 
natural numbers k1, …, kn, the following hold:
	
1.	 If R(k1, …, kn) is true, then ⊢K B k
kn
1,
,
…
(
).
	
2.	 If R(k1, …, kn) is false, then ⊢K ¬
…
(
)
B k
kn
1,
,
.
*	 We follow the custom of regarding a number-theoretic property, such as the property of 
being even, as a “relation” of one argument.



170
Introduction to Mathematical Logic
For example, the number-theoretic relation of identity is expressed in S by 
the wf x1 = x2. In fact, if k1 = k2, then k1 is the same term as k2 and so, by 
Proposition 3.2(a), ⊢S k
k
1
2
=
. Moreover, if k1 ≠ k2, then, by Proposition 3.6(a), 
⊢S k
k
1
2
≠
.
Likewise, the relation “less than” is expressed in S by the wf x1 < x2. Recall 
that x1 < x2 is (∃x3)(x3 ≠ 0 ∧ x3 + x1 = x2). If k1 < k2, then there is some nonzero 
number n such that k2 = n + k1. Now, by Proposition 3.6(a)(ii), ⊢S k
n
k
2
1
=
+
. 
Also, by (S3′), since n
n
≠
≠
0
0
,
.
⊢S
 Hence, by rule E4, one can prove in S the wf 
(
)
∃
≠
∧
+
=
(
)
w
w
w
k
k
0
1
2 ; that is, ⊢S k
k
1
2
<
.  On the other hand, if k1 /< k2, then 
k2 < k1 or k2 = k1. If k2 < k1, then, as we have just seen, ⊢S k
k
2
1
<
. If k2 = k1, then 
⊢S k
k
2
1
=
. In either case, ⊢S k
k
2
1
≤
 and then, by Proposition 3.7(a,c), ⊢S k
k
1
2
/<
.
Observe that, if a relation is expressible in a theory K, then it is expressible 
in any extension of K.
Exercises
3.9	
Show that the negation, disjunction, and conjunction of relations 
that are expressible in K are also expressible in K.
3.10	 Show that the relation x + y = z is expressible in S.
Let K be any theory with equality in the language LA of arithmetic. A num-
ber-theoretic function f of n arguments is said to be representable in K if and 
only if there is a wf B (x1, …, xn, y) of K with the free variables x1, …, xn, y such 
that, for any natural numbers k1, …, kn, m, the following hold:
	 1.	 If f(k1, …, kn) = m, then ⊢K B k
k
m
n
1,
,
,
…
(
) .
	 2.	 ⊢K ∃
(
)
…
(
)
1
1
y
k
k
y
n
B
,
,
,
.
	
	 If, in this definition, we replace condition 2 by
	 2′.	 ⊢K ∃
(
)
…
(
)
1
1
y
x
x
y
n
B
,
,
,
.
	
	 then the function f is said to be strongly representable in K. Notice 
that 2′ implies 2, by Gen and rule A4. Hence, strong representability 
implies representability. The converse is also true, as we now prove.
Proposition 3.12 (V.H. Dyson)
If f(x1, …, xn) is representable in K, then it is strongly representable in K.
Proof
Assume f representable in K by a wf B (x1, …, xn, y). Let us show that f is 
strongly representable in K by the following wf C (x1, …, xn, y):
	
∃
(
)
…
(
)

∧
…
(
)
(
)∨¬
∃
(
)
…
(
)


1
1
1
1
1
y
x
x
y
x
x
y
y
x
x
y
n
n
n
B
B
B
,
,
,
,
,
,
,
,
,
∧
=
(
)
y
0



171
Formal Number Theory
	
1.	Assume f(k1, …,  kn) = m. Then ⊢K B (
,
,
,
)
k
k
m
n
1 …
 and ⊢K (
)
∃1y
B k
k
y
n
1,
,
,
.
…
(
)  So, by conjunction introduction and disjunction 
introduction, we get ⊢K C k
k
m
n
1,
,
,
…
(
).
	
2′. We must show ⊢K(∃1y)C (x1, …, xn, y).
Case 1. Take (∃1y)B (x1, …, xn, y) as hypothesis. (i) It is easy, using rule C, 
to obtain B (x1, …, xn, b) from our hypothesis, where b is a new individual 
constant. Together with our hypothesis and conjunction and disjunction 
introduction, this yields C (x1, …, xn, b) and then, by rule E4, (∃y)C (x1, …, 
xn, y). (ii) Assume C (x1, …, xn, u) ∧ C (x1, …, xn, v). From C (x1, …, xn, u) and 
our hypothesis, we obtain B (x1, …, xn, u), and, from C (x1, …, xn, v) and our 
hypothesis, we obtain B (x1, …, xn, v). Now, from B (x1, …, xn, u) and B (x1, …, 
xn, v) and our hypothesis, we get u = v. The deduction theorem yields C (x1, 
…, xn, u)∧ C (x1, …, xn, v) ⇒ u = v. From (i) and (ii), (∃1y) C (x1, …, xn, y). Thus, 
we have proved ⊢K(∃1y)B (x1, …, xn, y) ⇒ (∃1y) C (x1, …, xn, y).
Case 2. Take ¬(∃1y)B (x1, …, xn, y) as hypothesis. (i) Our hypothesis, together 
with the theorem 0 = 0, yields, by conjunction introduction, ¬(∃1y)B (x1, …, xn, 
y) ∧, 0 = 0. By disjunction introduction, C (x1, …, xn, 0), and, by rule E4, (∃y) 
C (x1, …, xn, y). (ii) Assume C (x1, …, xn, u) ∧ C (x1, …, xn, v). From C (x1, …, xn, u) 
and our hypothesis, it follows easily that u = 0. Likewise, from C (x1, …, xn, v) 
and our hypothesis, v = 0. Hence, u = v. By the deduction theorem, C (x1, …, xn, 
u) ∧ C (x1, …, xn, v) ⇒ u = v. From (i) and (ii), (∃1y) C (x1, …, xn, y). Thus we have 
proved ⊢K ¬(∃1y) B (x1, …, xn, y) ⇒ (∃1y)C (x1, …, xn, y).
By case 1 and case 2 and an instance of the tautology [(D ⇒ E) ∧ (¬ D ⇒ E)] ⇒ 
E, we can obtain ⊢K(∃1y)C (x1, …, xn, y).
Since we have proved them to be equivalent, from now on we shall use 
representability and strong representability interchangeably.
Observe that a function representable in K is representable in any exten-
sion of K.
Examples
In these examples, let K be any theory with equality in the language LA.
	 1.	 The zero function, Z(x) = 0, is representable in K by the wf x1 = x1 ∧ 
y = 0. For any k and m, if Z(k) = m, then m = 0 and ⊢K k
k
=
∧
=
0
0; 
that is, condition 1 holds. Also, it is easy to show that ⊢K(∃1y)(x1 = x1 
∧ y = 0). Thus, condition 2′ holds.
	 2.	 The successor function, N(x) = x + 1, is representable in K by the 
wf y = x1′. For any k and m, if N(k) = m, then m = k + 1; hence, m is ′k . 
Then ⊢K m
k
=
′ . It is easy to verify that ⊢K(∃1y)(y = x′1).
	 3.	 The projection function, U
x
x
x
j
n
n
j
1,
,
…
(
) =
, is representable in K 
by x1 = x1 ∧ x2 = x2 ∧ … ∧ xn = xn ∧ y = xj. If U
k
k
m
j
n
n
1,
,
,
…
(
) =
then m  = kj. Hence, ⊢K k
k
k
k
k
k
m
k
n
n
j
1
1
2
2
=
∧
=
∧… ∧
=
∧
=
. Thus, 



172
Introduction to Mathematical Logic
condition 1 holds. Also, ⊢K (∃1y)(x1 = x1 ∧ x2 = x2 ∧ … ∧ xn = xn ∧ y = xj), 
that is, condition 2′ holds.
	 4.	 Assume that the functions ɡ(x1, …, xm), h1(x1, …, xn), …, hm(x1, …, xn) 
are strongly representable in the theory with equality K by the 
wfs C (x1, …, xm, z), B1(x1, …, xn, y1), …, Bm(x1, …, xn, ym), respectively. 
Define a new function f by the equation
	
f x
x
h
x
x
h
x
x
n
n
m
n
1
1
1
1
,
,
,
,
,
,
,
,
…
(
) =
…
(
) …
…
(
)
(
)
g
f is said to be obtained from ɡ, h1, …, hm by substitution. Then f is also strongly 
representable in K by the following wf D(x1, …, xn, z):
	 ∃
(
) … ∃
(
)
…
(
) ∧… ∧
…
(
) ∧
…
(
)
(
)
y
y
x
x
y
x
x
y
y
y
z
m
n
m
n
m
m
1
1
1
1
1
1
B
B
C
,
,
,
,
,
,
,
,
,
To prove condition 1, let f(k1, …, kn) = p. Let hj(k1, …, kn) = rj for 1 ≤ j ≤ m; then ɡ(r1, 
…, rm) = p. Since C, B1, …, Bm represent ɡ, h1, …, hm, we have ⊢K Bj
n
j
k
k
r
1,
,
,
…
(
) 
for 1 ≤
≤
j
m and ⊢K C
r
r
p
m
1,
,
,
…
(
). So by conjunction introduction, 
⊢K B
B
C
1
1
1
1
1
k
k
r
k
k
r
r
r
p
n
m
n
m
m
,
,
,
,
,
,
,
…
(
) ∧… ∧
…
(
) ∧
…
(
). Hence, by rule E4, 
⊢K D k
k
p
n
1,
,
,
…
(
). Thus, condition 1 holds. Now we shall prove condition 2′. 
Assume D(x1, …, xn, u) ∧ D(x1, …, xn, v), that is
	 ∆
( )
∃
(
)… ∃
(
)
…
(
) ∧…∧
…
(
) ∧
…
(
)
y
y
x
x
y
x
x
y
y
y
u
m
n
m
n
m
m
1
1
1
1
1
1
B
B
C
,
,
,
,
,
,
,
,
,
(
)
And
	 
( ) ∃
(
)… ∃
(
)
…
(
) ∧…∧
…
(
) ∧
…
(
)
y
y
x
x
y
x
x
y
y
y
v
m
n
m
n
m
m
1
1
1
1
1
1
B
B
C
,
,
,
,
,
,
,
,
,
(
)
By (Δ), using rule C m times,
	
B
B
C
1
1
1
1
1
x
x
b
x
x
b
b
b
u
n
m
n
m
m
,
,
,
,
,
,
,
,
,
…
(
) ∧… ∧
…
(
) ∧
…
(
)
By (□) using rule C again,
	
B
B
C
1
1
1
1
1
x
x
c
x
x
c
c
c
v
n
m
n
m
m
,
,
,
,
,
,
,
,
,
…
(
) ∧… ∧
…
(
) ∧
…
(
)
Since ⊢K (∃1yj)Bj(x1, …, xn, yj), we obtain from Bj(x1, …, xn, bj) and Bj(x1, …, xn, cj), 
that bj = cj. From C (b1, …, bm, u) and b1 = c1, …, bm = cm, we have C (c1, …, cm, u). 
This, with ⊢K (∃1z)C (x1, …, xn, z) and C (c1, …, cm, v) yields u = v. Thus, we have 



173
Formal Number Theory
shown ⊢K D (x1, …, xn, u) ∧ D (x1, …, xn, v) ⇒ u = v. It is easy to show that ⊢K (∃z)
D (x1, …, xn, z). Hence, ⊢K (∃1z) D (x1, …, xn, z).
Exercises
3.11	 Let K be a theory with equality in the language LA. Show that the fol-
lowing functions are representable in K.
	
a.	 Zn(x1, …, xn) = 0 Hint Z x
x
Z U
x
x
n
n
n
n
:
,
,
(
,
,
).
(
)
(
)
1
1
1
…
=
…


	
b.	 C
x
x
k
k
n
n
1,
,
…
(
) =
, where k is a fixed natural number. [Hint: Use 
mathematical induction in the metalanguage with respect to k.]
3.12	 Prove that addition and multiplication are representable in S.
	
	 If R is a relation of n arguments, then the characteristic function CR 
is defined as follows:
	
C
x
x
x
x
x
x
R
n
n
n
1
1
1
0
1
,
,
(
,
,
)
(
,
,
)
…
(
) =
…
…



if
is true
if
is false
R
R
Proposition 3.13
Let K be a theory with equality in the language LA such that ⊢K 0
1
≠
. Then a 
number-theoretic relation R is expressible in K if and only if CR is represent-
able in K.
Proof
If R is expressible in K by a wf B (x1, …, xn), it is easy to verify that CR is rep-
resentable in K by the wf B
B
x
x
y
x
x
y
n
n
1
1
0
1
,
,
,
,
.
…
(
) ∧
=
(
)∨¬
…
(
) ∧
=
(
)  
Conversely, if CR is representable in K by a wf C (x1, …, xn, y), then, using the 
assumption that ⊢K 0
1
≠, we can easily show that R is expressible in K by the 
wf C (x1, …, xn, 0).
Exercises
3.13	 The graph of a function f(x1, …, xn) is the relation f(x1, …, xn) = xn+1. Show 
that f(x1, …, xn) is representable in S if and only if its graph is expressible 
in S.
3.14	 If Q and R are relations of n arguments, prove that Cnot−R = 1 − CR, 
C (Q or R) = CQ · CR, and C (Q and R) = CQ + CR − CQ · CR.
3.15	 Show that f(x1, …, xn) is representable in a theory with equality K in the 
language LA if and only if there is a wf B (x1, …, xn, y) such that, for any 
k1, …, kn, m, if f(k1, …, kn) = m, then ⊢K ∀
(
)
…
(
) ⇔
=
(
)
y
k
k
y
y
m
n
B
1,
,
,
.



174
Introduction to Mathematical Logic
3.3  Primitive Recursive and Recursive Functions
The study of representability of functions in S leads to a class of number-
theoretic functions that turn out to be of great importance in mathematical 
logic and computer science.
Definition
	
1.	The following functions are called initial functions.
	
I.	The zero function, Z(x) = 0 for all x.
	
II.	The successor function, N(x) = x + 1 for all x.
	
III.	The projection functions, U
x
x
x
i
n
n
i
1,
,
…
(
) =
 for all x1, …, xn.
	
2.	The following are rules for obtaining new functions from given 
functions.
	
IV.	 Substitution:
	
f x
x
h
x
x
h
x
x
n
n
m
n
1
1
1
1
,
,
,
,
,
,
,
,
…
(
) =
…
(
) …
…
(
)
(
)
g
	
	
f is said to be obtained by substitution from the functions
	
g y
y
h
x
x
h
x
x
m
n
m
n
1
1
1
1
,
,
,
,
,
,
,
,
,
…
(
)
…
(
) …
…
(
)
	
V.	 Recursion:
	
f x
x
x
x
f x
x
y
h x
x
y f x
x
n
n
n
n
n
1
1
1
1
1
0
1
,
,
,
,
,
,
,
,
,
,
, ,
,
,
,
…
(
) =
…
(
)
…
+
(
) =
…
…
g
y
(
)
(
)
	
	
Here, we allow n = 0, in which case we have
	
f
k
k
f y
h y f y
( )
(
)
,
( )
0
1
=
+
= (
)
where
is a fixed natural number
We shall say that f is obtained from ɡ and h (or, in the case n = 0, 
from h alone) by recursion. The parameters of the recursion are 
x1, …, xn. Notice that f is well defined: f(x1, …, xn, 0) is given by the 
first equation, and if we already know f(x1, …, xn, y), then we can 
obtain f(x1, …, xn, y + 1) by the second equation.
	
VI.	 Restricted μ-Operator. Assume that ɡ(x1, …, xn, y) is a func-
tion such that for any x1, …, xn there is at least one y such that 



175
Formal Number Theory
ɡ(x1, …, xn, y) = 0. We denote by μy(ɡ(x1, …, xn, y) = 0) the least 
number y such that ɡ(x1, …, xn, y) = 0. In general, for any rela-
tion R(x1, …, xn, y), we denote by μyR(x1, …, xn, y) the least y 
such that R(x1, …, xn, y) is true, if there is any y at all such that 
R(x1, …, xn, y) holds. Let f(x1, …, xn) = μy(ɡ(x1, …, xn, y) = 0). 
Then f is said to be obtained from ɡ by means of the restricted 
μ-operator if the given assumption about ɡ holds, namely, for 
any x1, …, xn, there is at least one y such that ɡ(x1, …, xn, y) = 0.
	
3.	A function f is said to be primitive recursive if and only if it can be 
obtained from the initial functions by any finite number of substitu-
tions (IV) and recursions (V)—that is, if there is a finite sequence 
of functions f0, …,  fn such that fn = f and, for 0 ≤ i ≤ n, either fi is an 
initial function or fi comes from preceding functions in the sequence 
by an application of rule (IV) or rule (V).
	
4.	A function f is said to be recursive if and only if it can be obtained from 
the initial functions by any finite number of applications of substitution 
(IV), recursion (V) and the restricted μ-operator (VI). This differs from 
the definition above of primitive recursive functions only in the addi-
tion of possible applications of the restricted μ-operator. Hence, every 
primitive recursive function is recursive. We shall see later that the con-
verse is false.
We shall show that the class of recursive functions is identical with the class 
of functions representable in S. (In the literature, the phrase “general recur-
sive” is sometimes used instead of “recursive.”)
First, let us prove that we can add “dummy variables” to and also per-
mute and identify variables in any primitive recursive or recursive function, 
obtaining a function of the same type.
Proposition 3.14
Let ɡ(y1, …, yk) be primitive recursive (or recursive). Let x1, … xn be distinct 
variables and, for 1 ≤ i ≤ k, let zi be one of x1, …, xn. Then the function f such 
that f(x1, …, xn) = ɡ(z1, …, zk) is primitive recursive (or recursive).
Proof
Let z
x
i
ji
=
, where 1 ≤ ji ≤ n. Then z
U
x
x
i
j
n
n
i
=
…
(
,
,
)
1
. Thus,
	
f x
x
U
x
x
U
x
x
n
j
n
n
j
n
n
k
1
1
1
1
,
,
,
,
,
,
,
,
…
(
) =
…
(
) …
…
(
)
(
)
g
and therefore f is primitive recursive (or recursive), since it arises from 
g,
,
,
U
U
j
n
j
n
k
1 …
 by substitution.



176
Introduction to Mathematical Logic
Examples
	
1.	 Adding dummy variables. If ɡ(x1, x3) is primitive recursive and if f(x1, x2, 
x3) = ɡ(x1, x3), then f(x1, x2, x3) is also primitive recursive. In Proposition 
3.14, let z1 = x1 and z2 = x3. The new variable x2 is called a “dummy 
variable” since its value has no influence on the value of f(x1, x2, x3).
	 2.	 Permuting variables. If ɡ(x1, x2, x3) is primitive recursive and if f(x1, 
x2, x3) = ɡ(x3, x1, x2), then f(x1, x2, x3) is also primitive recursive. In 
Proposition 3.14, let z1 = x3, z2 = x1, and z3 = x2.
	 3.	 Identifying variables. If ɡ(x1, x2, x3) is primitive recursive and if f(x1, x2) = 
ɡ(x1, x2, x1), then f(x1, x2) is primitive recursive. In Proposition 3.14, let 
n = 2 and z1 = x1, z2 = x2 and z3 = x1.
Corollary 3.15
	 a.	 The zero function Zn(x1, …, xn) = 0 is primitive recursive.
	 b.	 The constant function C
x
x
k
k
n
n
1,
,
…
(
) =
, where k is some fixed nat-
ural number, is primitive recursive.
	 c.	 The substitution rule (IV) can be extended to the case where each 
hi may be a function of some but not necessarily all of the variables. 
Likewise, in the recursion rule (V), the function g may not involve 
all of the variables x1, …, xn, y, or f(x1, …, xn, y) and h may not involve all 
of the variables x1, …, xn, y, or f(x1, …, xn, y).
Proof
	 a.	 In Proposition 3.14, let g be the zero function Z; then k = 1. Take 
z1 to be x1.
	 b.	 Use mathematical induction. For k = 0, this is part (a). Assume Ck
n 
primitive recursive. Then C
x
x
k
n
n
+
…
1
1
(
,
,
) is primitive recursive by 
the substitution C
x
x
N C
x
x
k
n
n
k
n
n
+
…
(
) =
…
(
)
(
)
1
1
1
,
,
,
,
.
	 c.	 By Proposition 3.14, any variables among x1, …, xn not 
present in a function can be added as dummy vari-
ables. For example, if h(x1, x3) is primitive recursive, then 
h
x
x
x
h x
x
h U
x
x
x
U
x
x
x
*
1
2
3
1
3
1
3
1
2
3
3
3
1
2
3
,
,
,
,
,
,
,
,
(
) = (
) =
(
)
(
)
(
) 
is 
also 
primitive recursive, since it is obtained by a substitution.
Proposition 3.16
The following functions are primitive recursive.
	 a.	 x + y
	 b.	 x · y
	
c.	 xy



177
Formal Number Theory
	
d.
	
δ( )
x
x
x
x
=
−
>
=



1
0
0
0
if
if
	
	 δ is called the predecessor function.
	
e.
	
x
y
x
y
x
y
x
y
−
=
−
≥
<



if
if
0
	
f.
	
x
y
x
y
x
y
x
y
y
x
−
=
−
≥
<


−
if
if
	
g.
	
sg
if
if
x
x
x
( ) =
=
≠



0
0
1
0
	
h.
	
sg
if
if
( )
x
x
x
=
=
≠



1
0
0
0
	
i.	 x!
	
j.	 min (x, y) = minimum of x and y
	 k.	 min (x1, …, xn)
	
l.	 max (x, y) = maximum of x and y
	 m.	 max (x1, …, xn)
	 n.	 rm (x, y) = remainder upon division of y by x
	 o.	 qt (x, y) = quotient upon division of y by x
Proof
	 a.	 Recursion rule (V)
	
b.
	
x
x
f x
U x
x
y
N x
y
f x y
N f x y
x
+
=
=
+
+
=
+
+
=
⋅
=
0
0
1
1
0
0
1
1
or
o
( , )
( )
(
)
(
)
( ,
)
( ( , ))
r
g
g
g
( , )
( )
(
)
(
)
( ,
)
( ( , ), )
x
Z x
x
y
x y
x
x y
f
x y x
0
1
1
=
⋅
+
=
⋅
+
+
=
	
	 where f is the addition function
	
c.
	
x
x
x
x
y
y
0
1
1
=
= (
) ⋅
+
	
d.
	
δ
δ
( )
(
)
0
0
1
=
+
=
y
y
	
e.
	
x
x
x
y
x
y



−
=
−
+
=
−
0
1
(
)
(
)
δ
	
f.	 |
| (
)
(
)
x
y
x
y
y
x
−
=
−
+
−


 (substitution)
	 g.	 sg( )
( )
x
x
x
=
− δ
 (substitution)
	 h.	 sg
sg
( )
( )
x
x
=
−
1 
 (substitution)



178
Introduction to Mathematical Logic
	
i.
	
0
1
1
1
!
(
)!
( !) (
)
=
+
=
⋅
+
y
y
y
 
	
j.	 min( , )
(
)
x y
x
x
y
=
−
−


	 k.	 Assume min x
xn
1,
,
…
(
) already shown primitive recursive.
	
min
,
,
,
min min
,
,
,
x
x
x
x
x
x
n
n
n
n
1
1
1
1
…
(
) =
…
(
)
(
)
+
+
	
l.	 max( , )
(
)
x y
y
x
y
=
+
−
	 m.	 max
,
,
,
max max
,
,
,
x
x
x
x
x
x
n
n
n
n
1
1
1
1
…
(
) =
…
(
)
(
)
+
+
	
n.
	
rm
rm
rm
sg
rm
( , )
( ,
)
(
( , ))
(|
(
( , ))|)
x
x y
N
x y
x
N
x y
0
0
1
=
+
=
⋅
−
	
o.
	
qt
qt
sg
rm( , ))
( , )
( ,
)
( , )
(
(
)
x
x y
qt x y
x
N
x y
0
0
1
=
+
=
+
−
In justification of (n) and (o), note that, if q and r denote the quotient qt(x, y) 
and remainder rm(x, y) upon division of y by x, then y = qx + r and 0 ≤ r < x. 
So, y + 1 = qx + (r + 1). If r + 1 < x (that is, if |x −N(rm(x, y))|> 0), then the quo-
tient qt(x, y + 1) and remainder rm(x, y + 1) upon division of y + 1 by x are q 
and r + 1, respectively. If r + 1 = x (that is, if |x −N(rm(x, y))| = 0), then y + 1 = 
(q + 1)x, and qt(x, y + 1) and rm(x, y + 1) are q + 1 and 0, respectively.*
Definitions
	
f x
x
y
z
f x
x
f x
x
z
z
y z
n
n
n
<∑
…
(
) =
=
…
+
+
…
−
>

1
1
1
0
0
0
1
0
,
,
,
(
,
,
, )
(
,
,
,
)
if
if



…
=
…
…
=
≤
< +
<
∑
∑
∏
f x
x
y
f x
x
y
f x
x
y
y z
n
y z
n
y z
n
(
,
,
, )
(
,
,
, )
(
,
,
, )
1
1
1
1
1 if z
f x
x
f x
x
z
z
f x
x
y
f
n
n
y z
n
y
=
…
…
…
−
>



…
=
≤∏
0
0
1
0
1
1
1
(
,
,
, )
(
,
,
,
)
(
,
,
, )
if
< +∏
…
z
n
x
x
y
1
1
(
,
,
, )
*	 Since one cannot divide by 0, the values of rm(0, y) and qt(0, y) have no intuitive significance. 
It can be easily shown by induction that the given definitions yield rm(0, y) = y and qt(0, y) = 0.



179
Formal Number Theory
These bounded sums and products are functions of x1, …, xn, z. We can also 
define doubly bounded sums and products in terms of the ones already 
given; for example,
	
f x
x
y
f x
x
u
f x
x
v
f
u y v
n
n
n
y
v
< <
<
∑
…
(
) =
…
+
(
) +
+
…
−
(
)
=
1
1
1
1
1
,
,
,
,
,
,
,
,
,
(


δ
−∑
…
+
+
(
)
u
n
x
x
y
u
)
,
,
,
1
1
Proposition 3.17
If f(x1, …, xn, y) is primitive recursive (or recursive), then all the bounded 
sums and products defined above are also primitive recursive (or recursive).
Proof
Let g x
x
z
x
x
y
n
y z
n
1
1
,
,
,
,
,
,
…
(
) =
…
(
)
<∑f
. Then we have the following recursion:
	
g
g
g
x
x
x
x
z
x
x
z
f x
x
z
n
n
n
n
1
1
1
1
0
0
1
,
,
,
,
,
,
,
,
,
,
,
,
…
(
) =
…
+
(
) =
…
(
) +
…
(
)
	
If
then
h x
x
z
f x
x
y
n
y z
n
1
1
,
,
,
,
,
,
,
…
(
) =
…
(
)
≤∑
	
h x
x
z
x
x
z
n
n
1
1
1
,
,
,
,
,
,
…
(
) =
…
+
(
)(
)
g
substitution
The proofs for bounded products and doubly bounded sums and products 
are left as exercises.
Examples
Let τ(x) be the number of divisors of x, if x > 0, and let τ(0) = 1. (Thus, τ(x) is 
the number of divisors of x that are less than or equal to x.) Then τ is primi-
tive recursive, since
	
τ( )
(
( , ))
x
y x
y x
=
≤∑sg rm
Given expressions for number-theoretic relations, we can apply the connec-
tives of the propositional calculus to them to obtain new expressions for 



180
Introduction to Mathematical Logic
relations. For example, if R1(x, y) and R2(x, u, v) are relations, then R1(x, y) ∧ 
R2(x, u, v) is a new relation that holds for x, y, u, v when and only when both 
R1(x, y) and R2(x, u, v) hold. We shall use (∀y)y<zR(x1, …, xn, y) to express the 
relation: for all y, if y is less than z, then R(x1, …, xn, y) holds. We shall use 
(∀y)y≤z, (∃y)y<z, and (∃y)y≤z in an analogous way; for example, (∃y)y<zR(x1, …, xn, y) 
means that there is some y < z such that R(x1, …, xn, y) holds. We shall call 
(∀y)y<z, (∀y)y≤z, (∃y)y<z, and (∃y)y≤z bounded quantifiers. In addition, we define a 
bounded μ-operator:
	
µy
R x
x
y
y
z
R x
x
y
y z
n
n
<
…
=
<
…
(
,
,
, )
(
,
,
, )
1
1
the least
for which
holds if there is such a
otherwise
y
z



The value z is chosen in the second case because it is more convenient in later 
proofs; this choice has no intuitive significance. We also define μyy≤zR(x1, …, 
xn, y) to be μyy<z+1R(x1, …, xn, y).
A relation R(x1, …, xn) is said to be primitive recursive (or recursive) if and 
only if its characteristic function CR(x1, …, xn) is primitive recursive (or recur-
sive). In particular, a set A of natural numbers is primitive recursive (or 
recursive) if and only if its characteristic function CA(x) is primitive recursive 
(or recursive).
Examples
	 1.	 The relation x1 = x2 is primitive recursive. Its characteristic function 
is sg(|x1 − x2|), which is primitive recursive, by Proposition 3.16(f, g).
	 2.	 The relation x1 < x2 is primitive recursive, since its characteristic 
function is sg x
x
2
1
−
(
), which is primitive recursive, by Proposition 
3.16(e, h).
	 3.	 The relation x1|x2 is primitive recursive, since its characteristic func-
tion is sg(rm(x1, x2)).
	 4.	 The relation Pr(x), x is a prime, is primitive recursive, since CPr(x) = 
sg(|τ(x) − 2|). Note that an integer is a prime if and only if it has 
exactly two divisors; recall that τ(0) = 1.
Proposition 3.18
Relations obtained from primitive recursive (or recursive) relations by means 
of the propositional connectives and the bounded quantifiers are also primi-
tive recursive (or recursive). Also, applications of the bounded μ-operators 
μyy<z and μyy≤z lead from primitive recursive (or recursive) relations to primi-
tive recursive (or recursive) functions.



181
Formal Number Theory
Proof
Assume R1(x1, …, xn) and R2(x1, …, xn) are primitive recursive (or recursive) rela-
tions. Then the characteristic functions CR1 and CR2 are primitive recursive (or 
recursive). But C
x
x
C
x
x
R
n
R
n
¬
…
=
−
…
1
1
1
1
1
(
,
,
)
(
,
,
);

 hence ¬R1 is primitive recur-
sive (or recursive). Also, C
x
x
C
x
x
C
x
x
R
R
n
R
n
R
n
1
2
1
2
1
1
1
∨
…
=
…
⋅
…
(
,
,
)
(
,
,
)
(
,
,
); 
so, R1 ∨ R2 is primitive recursive (or recursive). Since all propositional connec-
tives are definable in terms of ¬ and ∨, this takes care of them. Now, assume 
R(x1, …, xn, y) is primitive recursive (or recursive). If Q(x1, …, xn, z) is the rela-
tion (∃y)y<zR(x1, …, xn, y), then it is easy to verify that CQ(x1, …, xn, z) = Πy<zCR(x1, 
…, xn, y), which, by Proposition 3.17, is primitive recursive (or recursive). The 
bounded quantifier (∃y)y≤z is equivalent to (∃y)y<z+1, which is obtainable from 
(∃y)y<z by substitution. Also, (∀y)y<z is equivalent to ¬(∃y)y<z¬, and (∀y)y≤z is 
equivalent to ¬(∃y)y≤z¬. Doubly bounded quantifiers, such as (∃y)u<y<v, can be 
defined by substitution, using the bounded quantifiers already mentioned. 
Finally, Πu≤yCR(x1, …, xn, u) has the value 1 for all y such that R(x1, …, xn, u) is 
false for all u ≤ y; it has the value 0 as soon as there is some u ≤ y such that 
R(x1, …, xn, u) holds. Hence, 
(
(
,
,
, ))
Πu y
R
n
y z
C
x
x
u
≤
<
…
∑
1
 counts the number of 
integers from 0 up to but not including the first y < z such that R(x1, …, xn, y) 
holds and is z if there is no such y; thus, it is equal to μyy<zR(x1, …, xn, y) and 
so the latter function is primitive recursive (or recursive) by Proposition 3.17.
Examples
	 1.	 Let p(x) be the xth prime number in ascending order. Thus, p(0) = 2, 
p(1) = 3, p(2) = 5, and so on. We shall write px instead of p(x). Then px 
is a primitive recursive function. In fact,
	
p
p
y
p
y
y
x
y
p
x
x
0
1
1
2
=
=
<
∧
+
≤
+
µ
(
)! (
)
( )
Pr
	
	 Notice that the relation u < y ∧ Pr(y) is primitive recursive. Hence, 
by Proposition 3.18, the function μyy≤v(u < y ∧ Pr(y)) is a primitive 
recursive function g(u, v). If we substitute the primitive recursive 
functions z and z! + 1 for u and v, respectively, in ɡ(u, v), we obtain 
the primitive recursive function
	
h z
y
z
y
y
y z
( )
( )
(
)
!
=
<
∧
≤
+
µ
1
Pr
	
	 and the right-hand side of the second equation above is h(px); hence, 
we have an application of the recursion rule (V). The bound (px)! + 1 
on the first prime after px is obtained from Euclid’s proof of the 
infinitude of primes (see Exercise 3.23).
	 2.	 Every positive integer x has a unique factorization into prime pow-
ers: x
p p
p
a
a
k
ak
=
0
1
0
1 
. Let us denote by (x)j the exponent aj in this 



182
Introduction to Mathematical Logic
factorization. If x = 1, (x)j = 1 for all j. If x = 0, we arbitrarily let 
(x)j = 0 for all j. Then the function (x)j is primitive recursive, since 
( )
|
|
.
x
y
p
x
p
x
j
y x
j
y
j
y
=
∧¬(
)
(
)
<
+
µ
1
	 3.	 For x > 0, let ℓħ(x) be the number of nonzero exponents in the fac-
torization of x into powers of primes, or, equivalently, the number 
of distinct primes that divide x. Let ℓħ(0) = 0. Then ℓħ is primitive 
recursive. To see this, let R(x, y) be the primitive recursive rela-
tion Pr(y) ∧ y|x ∧ x ≠ 0. Then ℓℏ( )
,
x
C
x y
R
y x
=
(
)
(
)
≤
∑
sg
. Note that 
this yields the special cases ℓħ(0) = ℓħ(1) = 0. The expression “ℓħ(x)” 
should be read “length of x.”
	 4.	 If the number x
p
a
a
k
ak
=
…
2 3
0
1
 is used to “represent” or “encode” 
the sequence of positive integers a0, a1, …, ak, and y
p
b
b
m
bm
=
…
2 3
0
1
 
­“represents” the sequence of positive integers b0, b1, …, bm, then the 
number
	
x y
p p
p
p
a
a
k
a
k
b
k
b
k
m
b
k
m
*
=
…
…
+
+
+ +
2 3
0
1
0
1
1
2
1
	
	 “represents” the new sequence a0, a1, …, ak, b0, b1, …, bm obtained by 
juxtaposing the two sequences. Note that ℓħ(x) = k + 1, which is the 
length of the first sequence, ℓħ(y) = m + 1, which is the length of the 
second sequence, and bj = (y)j. Hence,
	
x y
x
p
x
j
y
j
y
j
*
=
(
)
+
<∏
×
ℓℏ
ℓℏ
( )
( )
( )
	
	 and, thus, * is a primitive recursive function, called the juxtaposition 
function. It is not difficult to show that x * (y * z) = (x * y) * z as long 
as y ≠ 0 (which will be the only case of interest to us). Therefore, 
there is no harm in omitting parentheses when writing two or more 
applications of *. Also observe that x * 0 = x * 1 = x.
Exercises
3.16	 Assume that R(x1, …, xn, y) is a primitive recursive (or recursive) rela-
tion. Prove the following:
	
a.	 (∃y)u<y<vR(x1, …, xn, y), (∃y)u≤y≤vR(x1, …, xn, y), and (∃y)u≤y<vR (x1, …, xn, 
y) are primitive (or recursive) relations.
	
b.	 μyu<y<vR(x1, …, xn, y), μyu≤y≤vR(x1, …, xn, y), and μyu≤y<vR (x1, …, xn, y) 
are primitive recursive (or recursive) functions.
	
c.	 If, for all natural numbers x1, …, xn, there exists a natural number y 
such that R(x1, …, xn, y), then the function f(x1, …, xn) = μyR(x1, …, xn, y) 
is recursive. [Hint: Apply the restricted μ-operator to CR(x1, …, xn, y).]



183
Formal Number Theory
3.17	 a.	Show that the intersection, union and complement of primitive 
recursive (or recursive) sets are also primitive recursive (or recur-
sive). Recall that a set A of numbers can be thought of as a relation 
with one argument, namely, the relation that is true of a number x 
when and only when x ∈ A.
	
b.	Show that every finite set is primitive recursive.
3.18	 Prove that a function f(x1, …, xn) is recursive if and only if its represent-
ing relation f(x1, …, xn) = y is a recursive relation.
3.19	 Let [
]
n  denote the greatest integer less than or equal to n, and let 
Π(n) denote the number of primes less than or equal to n. Show that 
[
]
n  and Π(n) are primitive recursive.
3.20	 Let e be the base of the natural logarithms. Show that [ne], the greatest 
integer less than or equal to ne, is a primitive recursive function.
3.21	 Let RP(y, z) hold if and only if y and z are relatively prime, that is, y and 
z have no common factor greater than 1. Let φ(n) be the number of posi-
tive integers less than or equal to n that are relatively prime to n. Prove 
that RP and φ are primitive recursive.
3.22	 Show that, in the definition of the primitive recursive functions, one 
need not assume that Z(x) = 0 is one of the initial functions.
3.23	 Prove that pk+1 ≤ (p0p1… pk) + 1. Conclude that pk+1 ≤ pk! + 1.
For use in the further study of recursive functions, we prove the following 
theorem on definition by cases.
Proposition 3.19
Let
	
f x
x
x
x
R x
x
x
x
R x
n
n
n
n
(
,
,
)
(
,
,
)
(
,
,
)
(
,
,
)
(
1
1
1
1
1
2
1
2
1
…
=
…
…
…
g
g
if
holds
if
,
,
)
(
,
,
)
(
,
,
)
…
…
…






x
x
x
R x
x
n
k
n
k
n
holds
if
holds

g
1
1
If the functions ɡ1, …, ɡk and the relations R1, …, Rk are primitive recursive 
(or recursive), and if, for any x1, …, xn, exactly one of the relations R1(x1, …, xn), 
…, Rk(x1, …, xn) is true, then f is primitive recursive (or recursive).
Proof
	
f x
x
x
x
C
x
x
x
x
n
n
R
n
k
n
(
,
,
)
(
,
,
)
(
(
,
,
))
(
,
,
)
(
1
1
1
1
1
1
…
=
…
⋅
…
+
+
…
⋅
g
g
sg
sg
 

C
x
x
R
n
k(
,
,
)).
1 …



184
Introduction to Mathematical Logic
Exercises
3.24	 Show that in Proposition 3.19 it is not necessary to assume that Rk is 
primitive recursive (or recursive).
3.25	 Let
	
f x
x
x
x
x
( ) =
+



2
1
if
is even
if
is odd
	
	 Prove that f is primitive recursive.
3.26	 Let
	
h x
( ) = 2
1
if Goldbach’s conjecture is true
if Goldbach’s conjecture is false



Is h primitive recursive?
It is often important to have available a primitive recursive one–one cor-
respondence between the set of ordered pairs of natural numbers and the set 
of natural numbers. We shall enumerate the pairs as follows:
	
( , ),
( , ),( , ),( , ),
( , ),( , ),( , ),( , ),( , ),
0 0
0 1
1 0
1 1
0 2
2 0
1 2
2 1
2 2
…
After we have enumerated all the pairs having components less than or 
equal to k, we then add a new group of all the new pairs having components 
less than or equal to k + 1 in the following order: (0, k + 1), (k + 1, 0), (1, k + 1), 
(k + 1, 1), …, (k, k + 1), (k + 1, k), (k + 1, k + 1). If x < y, then (x, y) occurs before (y, x) 
and both are in the (y + 1)th group. (Note that we start from 1 in counting 
groups.) The first y groups contain y2 pairs, and (x, y) is the (2x + 1)th pair 
in the (y + 1)th group. Hence, (x, y) is the (y2 + 2x + 1)th pair in the ordering, 
and (y, x) is the (y2 + 2x + 2)th pair. On the other hand, if x = y, (x, y) is 
the ((x + 1)2)th pair. This justifies the following definition, in which σ2(x, y) 
denotes the place of the pair (x, y) in the above enumeration, with (0, 0) con-
sidered to be in the 0th place:
	
σ2
2
2
2
1
2
( , )
(
) (
)
(
) (
)
x y
x
y
x
y
x
y
y
x
=
−
⋅
+
+
+
−
⋅
+
sg
sg


Clearly, σ2 is primitive recursive.
Let us define inverse functions σ1
2 and σ2
2 such that σ σ
1
2
2
(
( , ))
,
x y
x
=
σ σ
2
2
2
(
( , ))
x y
y
=  and σ σ
σ
2
1
2
2
2
(
( ),
( ))
z
z
z
= . Thus, σ1
2( )z  and σ2
2( )z  are the first and 
second components of the zth ordered pair in the given enumeration. Note 
first that σ
σ
1
2
2
2
0
0
0
0
( )
,
( )
=
= ,
	
σ
σ
σ
σ
σ
σ
σ
σ
1
2
2
2
1
2
2
2
2
2
1
2
2
2
1
1
1
0
(
)
( )
( )
( )
( )
( )
( )
n
n
n
n
n
n
n
+
=
<
+
>
if
if
if
2
2
2
( )
( )
n
n
=





σ



185
Formal Number Theory
and
	
σ
σ
σ
σ
σ
σ
σ
2
2
1
2
1
2
2
2
1
2
1
2
2
2
1
1
(
)
( )
( )
( )
( )
( )
( )
n
n
n
n
n
n
n
+
=
≠
+
=



if
if
Hence,
	
σ
σ
σ
σ
σ
σ
1
2
2
2
2
2
1
2
2
2
1
2
1
1
(
)
( ) (
(
( )
( )))
(
( )
) (
(
( )
n
n
n
n
n
n
+
=
⋅
−
+
+
⋅
sg
sg

−
=
+
=
⋅
−
σ
φ σ
σ
σ
σ
σ
σ
2
2
1
2
2
2
2
2
1
2
2
2
1
1
( )))
(
( ),
( ))
(
)
( ) (
(|
( )
n
n
n
n
n
n
sg
2
1
2
1
2
2
2
1
2
2
2
1
( )|))
(
( )
) (
(|
( )
( )|))
(
( ),
( ))
n
n
n
n
n
n
+
+
⋅
−
=
σ
σ
σ
ψ σ
σ
sg
where ϕ and ψ are primitive recursive functions. Thus, σ1
2 and σ2
2 are defined 
recursively at the same time. We can show that σ1
2 and σ2
2 are primitive recur-
sive in the following devious way. Let h u
u
u
( )
.
( )
( )
= 2
3
1
2
2
2
σ
σ
 Now, h is primitive 
recursive, since h( )
,
( )
( )
0
2
3
2
3
1
1
2
2
2
0
0
0
0
=
=
=
⋅
σ
σ
 and h n
n
n
(
)
(
)
(
)
+
=
=
+
+
1
2
3
1
2
2
2
1
1
σ
σ
2
3
2
3
1
2
2
2
1
2
2
2
0
1
φ σ
σ
ψ σ
σ
φ
ψ
(
( ),
( ))
(
( ),
( ))
(( ( )) ,( ( )) )
((
n
n
n
n
h n
h n
=
h n
h n
( )) ,( ( )) ).
0
1  Remembering. that the 
function ( )
x i is primitive recursive (see Example 2 on page 181), we conclude 
by recursion rule (V) that h is primitive recursive. But σ1
2
0
( )
( ( ))
x
h x
=
 and 
σ2
2
1
( )
( ( ))
x
h x
=
. By substitution, σ1
2 and σ2
2 are primitive recursive.
One–one primitive recursive correspondences between all n-tuples of nat-
ural numbers and all natural numbers can be defined step-by-step, using 
induction on n. For n = 2, it has already been done. Assume that, for n = k, we 
have primitive recursive functions σ
σ
σ
k
k
k
k
k
x
x
x
x
(
,
,
),
( ),
,
( )
1
1
…
…
 such that 
σ σ
i
k
k
k
i
x
x
x
(
(
,
,
))
1 …
=
 for 1 ≤≤
i
k, and σ σ
σ
k
k
k
k
x
x
x
(
( ),
,
( )
)
1
…
=
. Now, for 
n
k
=
+1, define σ
σ σ
σ
σ σ
k
k
k
k
k
k
i
k
i
k
x
x
x
x
x
x
x
x
+
+
+
+
…
=
…
=
1
1
1
2
1
1
1
1
2
(
,
,
,
)
(
(
,
,
),
),
( )
(
( )) 
for 1 ≤≤
i
k and σ
σ
k
k
x
x
+
+
=
1
1
2
2
( )
( ). Then σ
σ
σ
k
k
k
k
+
+
+
+
…
1
1
1
1
1
,
,
,
 are all primitive recur-
sive, and we leave it as an exercise to verify that σ
σ
i
k
k
k
i
x
x
x
+
+
+
…
=
1
1
1
1
(
(
,
,
))
 for 
1
1
≤≤
+
i
k
, and σ σ
σ
k
k
k
k
x
x
x
(
( ),
,
( ))
1
1
1
1
+
+
+
…
=
.
It will be essential in later work to define functions by a recursion in which 
the value of f(x1, …, xn, y + 1) depends not only upon f(x1, …, xn, y) but also upon 
several or all values of f(x1, …, xn, u) with u ≤ y. This type of recursion is called 
a course-of-values recursion. Let f
x
x
y
p
n
u
f x
x
u
u y
n
#(
,
,
, )
.
(
,
,
, )
1
1
…
=
…
<
∏
 Note that 
f can be obtained from f # as follows: f x
x
y
f
x
x
y
n
n
y
(
,
,
, )
( #(
,
,
,
))
1
1
1
…
=
…
+
.
Proposition 3.20 (Course-of-Values Recursion)
If h(x1, …, xn, y, z) is primitive recursive (or recursive) and f (x1, …, xn, y) = h(x1, 
…, xn, y, f #(x1, …, xn, y)), then f is primitive recursive (or recursive).



186
Introduction to Mathematical Logic
Proof
	
f
x
x
f
x
x
y
f
x
x
y p
n
n
n
y
f x
x
y
n
#(
,
,
, )
#(
,
,
,
)
#(
,
,
, )
(
,
,
,
1
1
1
0
1
1
1
…
=
…
+
=
…
⋅
…
)
(
,
,
, ,
#(
,
,
, ))
#(
,
,
, )
=
…
⋅
…
…
f
x
x
y
p
n
y
h x
x
y f
x
x
y
n
n
1
1
1
Thus, by the recursion rule, f# is primitive recursive (or recursive), and 
f(x1, …, xn, y) = (f#(x1, …, xn, y + 1))y.
Example
The Fibonacci sequence is defined as follows: f(0) = 1, f(1) = 1, and f(k + 2) = f(k) + 
f(k + 1) for k ≥ 0. Then f is primitive recursive, since
	
f n
n
n
f
n
f
n
n
n
n
( )
( )
(|
|)
(( #( ))
( #( ))
)
)
=
+
−
+
+
⋅
−
−
−
sg
sg
sg(
1
1
1
2



The function
	
h y z
y
y
z
z
y
y
y
( , )
( )
(|
|)
(( )
( )
)
(
)
=
+
−
+
+
⋅
−
−
−
sg
sg
sg
1
1
1
2



is primitive recursive, and f(n) = h(n, f # (n)).
Exercise
3.27	 Let ɡ(0) = 2, ɡ(1) = 4, and ɡ(k + 2) = 3ɡ(k + 1) −(2ɡ(k) + 1). Show that g is 
primitive recursive.
Corollary 3.21 (Course-of-Values Recursion for Relations)
If H(x1, …, xn, y, z) is a primitive recursive (or recursive) relation and 
R(x1, …, xn, y) holds if and only if H x
x
y C
x
x
y
n
R
n
(
,
,
, ,(
)#(
,
,
, ))
1
1
…
…
, where CR 
is the characteristic function of R, then R is primitive recursive (or recursive).
Proof
CR(x1, …, xn, y) = CH(x1, …, xn, y, (CR)#(x1, …, xn, y)). Since CH is primitive 
recursive (or recursive), Proposition 3.20 implies that CR is primitive 
recursive (or recursive) and, therefore, so is R.
Proposition 3.20 and Corollary 3.21 will be drawn upon heavily in what 
follows. They are applicable whenever the value of a function or relation for y 
is defined in terms of values for arguments less than y (by means of a primi-
tive recursive or recursive function or relation). Notice in this connection 



187
Formal Number Theory
that R(x1, …, xn, u) is equivalent to CR(x1, …, xn, u) = 0, which, in turn, for u < y, 
is equivalent to ((CR)#(x1, …, xn, y))u = 0.
Exercises
3.28	 Prove that the set of recursive functions is denumerable.
3.29	 If f0, f1, f2, … is an enumeration of all primitive recursive functions (or 
all recursive functions) of one variable, prove that the function fx(y) is 
not primitive recursive (or recursive).
Lemma 3.22 (Gödel’s β-Function)
Let β(x1, x2, x3) = rm(1 + (x3 + 1) · x2, x1). Then β is primitive recursive, by 
Proposition 3.16(n). Also, β is strongly representable in S by the following wf 
Bt(x1, x2, x3, y):
	
(
)(
(
(
)
)
(
)
)
∃
=
+
+
⋅
⋅
+
∧
<
+
+
⋅
w x
x
x
w
y
y
x
x
1
3
2
3
2
1
1
1
1
Proof
By Proposition 3.11 ⊢S (∃1y)Bt(x1, x2, x3, y). Assume β(k1, k2, k3) = m. 
Then k1 = (1 + (k3 + 1) · k2) · k + m for some k, and m < 1 + (k3 + 1) · k2. 
So, 
⊢S k
k
k
k
m
1
3
2
1
1
=
+
+
(
)
(
)
+
·
·
, 
by 
Proposition 
3.6(a). 
Moreover, 
⊢S m
k
k
<
+
+
(
)⋅
1
1
3
2 by the expressibility of < and Proposition 3.6(a). Hence, 
⊢S k
k
k
k
m
m
k
k
1
3
2
3
2
1
1
1
1
=
+
+
(
)⋅
(
)⋅
+
∧
<
+
+
(
)⋅
 from which by rule E4,
⊢S Bt k k
k
m
1
2
3
,
,
,
.
(
)  Thus, Bt strongly represents β in S.
Lemma 3.23
For any sequence of natural numbers k0, k1, …, kn, there exist natural numbers 
b and c such that β(b, c, i) = ki for 0 ≤ i ≤ n.
Proof
Let j = max(n, k0, k1, …, kn) and let c = j!. Consider the numbers ui = 1 + (i + 1)c 
for 0 ≤ i ≤ n; no two of them have a factor in common other than 1. In fact, 
if p were a prime dividing both 1 + (i + 1)c and 1 + (m + 1)c with 0 ≤ i < m ≤ n, 
then p would divide their difference (m − i)c. Now, p does not divide c, since, 
in that case p would divide both (i + 1)c and 1 + (i + 1)c, and so would divide 1, 
which is impossible. Hence, p also does not divide (m − i); for m − i ≤ n ≤ j 
and so, m − i divides j! = c. If p divided m − i, then p would divide c. 



188
Introduction to Mathematical Logic
Therefore, p does not divide (m − i)c, which yields a contradiction. Thus, 
the numbers ui, 0 ≤ i ≤ n, are relatively prime in pairs. Also, for 0 ≤ i ≤ n, ki ≤ j ≤ 
j! = c < 1 + (i + 1)c = ui; that is, ki < ui. Now, by the Chinese remainder theorem 
(see Exercise 3.30), there is a number b < u0u1 … un such that rm(ui, b) = ki for 
0 ≤ i ≤ n. But β(b, c, i) = rm(1 + (i + 1)c, b) = rm(ui, b) = ki.
Lemmas 3.22 and 3.23 enable us to express within S assertions about finite 
sequences of natural numbers, and this ability is crucial in part of the proof 
of the following fundamental theorem.
Proposition 3.24
Every recursive function is representable in S.
Proof
The initial functions Z, N, and Ui
n are representable in S, by Examples 1–3 on 
page 171. The substitution rule (IV) does not lead out of the class of repre-
sentable functions, by Example 4 on page 172.
For the recursion rule (V), assume that ɡ(x1, …, xn) and h(x1, …, xn, y, z) are 
representable in S by wfs B (x1, …, xn+1) and C (x1, …, xn+3), respectively, and let
	
I.
	
f x
x
x
x
f x
x
y
h x
x
y f x
x
n
n
n
n
n
1
1
1
1
1
0
1
,
,
,
,
,
,
,
,
,
,
, ,
,
,
,
…
(
) =
…
(
)
…
+
(
) =
…
…
g
y
(
)
(
)
Now, f(x1, …, xn, y) = z if and only if there is a finite sequence of numbers 
b0, …, by such that b0 = ɡ(x1, …, xn), bw+1 = h(x1, …, xn, w, bw) for w + 1 ≤ y, and 
by = z. But, by Lemma 3.23, reference to finite sequences can be paraphrased 
in terms of the function β and, by Lemma 3.22, β is representable in S by the 
wf Bt(x1, x2, x3, y).
We shall show that f(x1, …, xn, xn+1) is representable in S by the following 
wf D(x1, …, xn+2):
	
(
)(
)[((
)(
( , , ,
)
(
,
,
,
)))
( , ,
,
∃
∃
∃
∧
…
∧
+
+
u
v
w
u v
w
x
x
w
u v x
x
n
n
n
Bt
Bt
0
1
1
2
B
)
(
)(
(
)(
)(
( , ,
, )
( , ,
, )
(
,
,
∧∀
<
⇒∃
∃
∧
′
∧
…
+
w w
x
y
z
u v w y
u v w z
x
x
n
n
1
1
Bt
Bt
C
,
, , )))]
w y z
	
i.	First, assume that f(x1, …, xn, p) = m. We wish to show that 
⊢S D k
k
p m
n
1,
,
, ,
…
(
). If p = 0, then m = ɡ(k1, …, kn). Consider the 
sequence consisting of m alone. By Lemma 3.23, there exist b and c 
such that β(b, c, 0) = m. Hence, by Lemma 3.22,
	
X
( )
(
)
⊢S Bt b c
m
, , ,0



189
Formal Number Theory
	
	 Also, since m = ɡ(k1, …, kn), we have ⊢S B k
k m
n
1,
,
,
.
…
(
) Hence, by rule E4,
	
XX
(
)
∃
(
)
(
) ∧
…
(
)
(
)
⊢S
Bt
w
b c
w
k
k
w
n
, , ,
,
,
,
0
1
B
	
	 In addition, since ⊢S w ≮ 0, a tautology and Gen yield
	
XXX
(
) ∀
(
)
<
⇒∃
(
) ∃
(
)
(
)
(
)
∧
(
) ∧
…
′
w
w
y
z
b c w y
b c w z
k
kn
(
, ,
,
, ,
,
,
,
,
0
1
Bt
Bt
C
w y z
, ,
(
)
(
)))
	
	 Applying rule E4 to the conjunction of (X), (XX), and (XXX), we obtain 
⊢S D k
k
m
n
1
0
,
,
, ,
.
…
(
)  Now, for p > 0, f(k1, …, kn, p) is calculated from 
the equations (I) in p + 1 steps. Let ri = f(k1, …, kn, i). For the sequence 
of numbers r0, …, rp, there are, by Lemma 3.23, numbers b and c such 
that β(b, c, i) = ri for 0 ≤ i ≤ p. Hence, by Lemma 3.22, ⊢S Bt b c i ri
, , ,
.
(
)  
In particular, β b c
r
f k
k
k
k
n
n
, ,
,
,
,
,
,
.
0
0
0
1
1
(
) =
=
…
(
) =
…
(
)
g
 Therefore, 
⊢S Bt b c
r
k
k
r
n
, , ,
,
,
,
0
0
1
0
(
) ∧
…
(
)
B
, and, by rule E4, (i) ⊢S ∃
(
)
w
Bt b c
w
k
k
w
n
, , ,
,
,
,
.
0
1
(
) ∧
…
(
)
(
)
B
 
Since 
r
f k
k
p
m
p
n
=
…
=
(
,
,
, )
,
1
 
we 
have 
β( , , )
.
b c p
m
=
 
Hence, 
(ii) 
⊢S Bt b c p m
, , ,
.
(
)  
For 
0
1
1
< ≤
−
=
=
i
p
b c i
r
f k
k
i
i
n
, ( , , )
(
,
,
, )
β
…
 
and 
β( , ,
)
b c i
ri
+
=
=
+
1
1
f k
k
i
h k
k
i f k
k
i
h k
k
i r
n
n
n
n
i
(
,
,
,
)
(
,
,
, , (
,
,
, ))
(
,
,
, , ).
1
1
1
1
1
…
+
=
…
…
=
…
 
Therefore, ⊢S Bt
Bt
b c i r
b c i
r
k
k
i r r
i
i
n
i
i
, , ,
, ,
,
,
,
, , ,
.
(
)∧
(
) ∧
…
(
)
′
+
+
1
1
1
C
 By 
Rule E4, ⊢S
Bt
Bt
∃
(
) ∃
(
)
(
) ∧
(
) ∧
(
′
y
z
b c i y
b c i
z
, , ,
, ,
,
C k
k
i y z
n
1,
,
, , ,
…
(
) 
So, 
by 
Proposition 
3.8(b′), 
(iii) 
⊢S ∀
(
)
<
⇒∃
(
) ∃
(
)
w
w
p
y
z
(
Bt
Bt
b c w y
b c w z
k
k
w y z
n
, ,
,
, ,
,
,
,
,
, ,
)
(
) ∧
(
) ∧
…
(
)
(
)
′
C
1
. Then, apply-
ing rule E4 twice to the conjunction of (i), (ii), and (iii), we obtain 
⊢S D k
k
p m
n
1,
,
, ,
…
(
). Thus, we have verified clause 1 of the definition 
of representability (see page 170).
	
ii.	We must show that ⊢S ∃
(
)
…
(
)
+
+
1
2
1
2
x
k
k
p x
n
n
n
D
,
,
, ,
. The proof is by 
induction on p in the metalanguage. Notice that, by what we have 
proved above, it suffices to prove only uniqueness. The case of p = 0 is 
left as an easy exercise. Assume ⊢S ∃
(
)
…
(
)
+
+
1
2
1
2
x
k
k
p x
n
n
n
D
,
,
, ,
. Let α = 
ɡ(k1, …, kn), β = f(k1, …, kn, p), and γ = f(k1, …, kn, p + 1) = h(k1, …, kn, p, β). Then
	
( )
(
,
,
, , , )
( )
(
,
,
, )
( )
(
,
,
, , )
(
1
2
3
1
1
1
⊢
⊢
⊢
S
S
S
C
B
D
k
k
p
k
k
k
k
p
n
n
n
…
…
…
β γ
α
β
4
1
5
1
1
2
1
2
)
(
,
,
,
, )
( )
(
) (
,
,
, ,
)
⊢
⊢
S
S
D
D
k
k
p
x
k
k
p x
n
n
n
n
…
+
∃
…
+
+
γ



190
Introduction to Mathematical Logic
Assume
	
6
1
1
2
( )
…
+
(
)
+
D k
k
p
x
n
n
,
,
,
,
We must prove xn+ =
2
γ. From (6), by rule C,
	
a.
	
∃
(
)
(
) ∧
…
(
)
(
)
w
b c
w
k
k
w
n
Bt
, , ,
,
,
,
0
1
B
	 b.	 Bt( , ,
,
)
b c p
xn
+
+
1
2
	
c.
	
∀
(
)
<
+ ⇒∃
(
) ∃
(
)
(
) ∧
(
)
(
∧
…
′
w
w
p
y
z
b c w y
b c w z
k
k
w y
n
(
, ,
,
, ,
,
,
,
,
, ,
1
1
Bt
Bt
C
z
(
)))
	
	 From (c),
	
d.
	
∀
(
)
<
⇒∃
(
) ∃
(
)
(
) ∧
(
)
(
∧
…
(
′
w
w
p
y
z
b c w y
b c w z
k
k
w y z
n
(
, ,
,
, ,
,
,
,
,
, ,
Bt
Bt
C
1
)))
	
	 From (c) by rule A4 and rule C,
	
e.
	
Bt
Bt
b c p d
b c p
e
k
k
p d e
n
, , ,
, ,
,
,
,
, , ,
(
) ∧
+
(
) ∧
…
(
)
1
1
C
	
	 From (a), (d), and (e),
	
f.
	
D k
k
p d
n
1,
,
, ,
…
(
)
	
	 From (f), (5) and (3),
	 g.	 d = β
	
	 From (e) and (g),
	
h.
	 C k
k
p
e
n
1,
,
, , ,
…
(
)
β
	
	 Since β represents h, we obtain from (l) and (h),
	
i.	 γ = e
	
	 From (e) and (i),
	
j.	 Bt( , ,
, )
b c p +1 γ
	
	 From (b), (j), and Lemma 3.22,
	 k.	 xn+ =
2
γ
This completes the induction.
The μ-operator (VI). Let us assume, that, for any x1, …, xn, there is some y 
such that ɡ(x1, …, xn, y) = 0, and let us assume ɡ is representable in S by a wf 
E(x1, …, xn+2). Let f(x1, …, xn) = μy(ɡ(x1, …, xn, y) = 0). Then we shall show that f 
is representable in S by the wf F (x1, …, xn+1):
	
E
E
x
x
y
y
x
x
x
y
n
n
n
1
1
1
1
0
0
,
,
,
,
,
, ,
…
(
) ∧∀
(
)
<
⇒¬
…
(
)
(
)
+
+



191
Formal Number Theory
Assume f(k1, …, kn) = m. Then ɡ(k1, …, kn, m) = 0 and, for k < m, ɡ(k1, …, kn, k) ≠ 0. 
So, ⊢S E k
k
m
n
1
0
,
,
,
,
…
(
) and, for k
m
k
k
k
n
<
¬
…
(
)
,
,
,
, ,
⊢S
E
1
0 . By Proposition 
3.8(b′), 
⊢S ∀
(
)
<
⇒¬
…
(
)
(
)
y
y
m
k
k
y
n
E
1
0
,
,
, ,
. 
Hence, 
⊢S F
k
k
m
n
1,
,
,
.
…
(
)  
We  must also show: ⊢S ∃
(
)
…
(
)
+
+
1
1
1
1
x
k
k
x
n
n
n
F
,
,
,
. It suffices to prove the 
uniqueness. Assume E
E
k
k
u
y
y
u
k
k
y
n
n
1
1
0
0
,
,
, ,
,
,
, ,
.
…
(
) ∧∀
(
)
<
⇒¬
…
(
)
(
)  By 
Proposition 3.7(o′), ⊢S m
u
m
u
u
m
<
∨
=
∨
<
. Since ⊢S E k
k
m
n
1
0
,
,
,
,
…
(
), we 
cannot have m
u
< . Since ⊢S ∀
(
)
<
⇒¬
…
(
)
(
)
y
y
m
k
k
y
n
E
1
0
,
,
, ,
, we cannot 
have u
m
<
. Hence, u
m
=
. This shows the uniqueness.
Thus, we have proved that all recursive functions are representable in S.
Corollary 3.25
Every recursive relation is expressible in S.
Proof
Let R(x1, …, xn) be a recursive relation. Then its characteristic function CR 
is recursive. By Proposition 3.24, CR is representable in S and, therefore, by 
Proposition 3.13, R is expressible in S.
Exercises
3.30A	 a.	 Show that, if a and b are relatively prime natural numbers, then 
there is a natural number c such that ac ≡ 1(mod b). (Two numbers 
a and b are said to be relatively prime if their greatest common divi-
sor is 1. In general, x ≡ y(mod z) means that x and y leave the same 
remainder upon division by z or, equivalently, that x − y is divisible 
by z. This exercise amounts to showing that there exist integers u 
and v such that 1 = au + bv.)
	
b.	 Prove the Chinese remainder theorem: if x1, …, xk are relatively 
prime in pairs and y1, …, yk are any natural numbers, there is a nat-
ural number z such that z ≡ y1(mod x1), …, z ≡ yk(mod xk). Moreover, 
any two such z’s differ by a multiple of x1 … xk. [Hint: Let x = x1 … xk 
and let x
w x
w x
w x
k
k
=
=
=
=
1
1
2
2

. Then, for 1 ≤ j ≤ k, wj is relatively 
prime to xj and so, by (a), there is some zj such that wjzj ≡ 1(mod xj). 
Now let z
w z y
w z y
w z y
k
k
k
=
+
+
+
1 1
1
2
2
2

. Then z ≡ wjzjyj ≡ yj(mod xj). 
In addition, the difference between any two such solutions is divis-
ible by each of x1, …, xk and hence by x1 … xk.]
3.31	 Call a relation R(x1, …, xn) arithmetical if it is the interpretation of some 
wf B (x1, …, xn) in the language LA of arithmetic with respect to the 
standard model. Show that every recursive relation is arithmetical. 
[Hint: Use Corollary 3.25.]



192
Introduction to Mathematical Logic
3.4  Arithmetization: Gödel Numbers
For an arbitrary first-order theory K, we correlate with each symbol u of K an 
odd positive integer g(u), called the Gödel number of u, in the following manner:
	
g
g
g
g
g
g
g
(()
,
())
,
(,)
,
( )
,
(
)
,
( )
,
(
)
=
=
=
¬ =
⇒=
∀=
=
+
3
5
7
9
11
13
13
8
x
k
k
for k
a
k
k
f
k n
A
k
k
n
n
k
k
n
n
≥
=
+
≥
=
+
≥
=
+
1
7
8
1
1
8 2 3
1
3
8 2 3
g
g
g
(
)
(
)
(
)
,
(
)
(
for
for
k
k n
)
,
for
≥1
Clearly, every Gödel number of a symbol is an odd positive integer. Moreover, 
when divided by 8, ɡ(u) leaves a remainder of 5 when u is a variable, a remain-
der of 7 when u is an individual constant, a remainder of 1 when u is a func-
tion letter, and a remainder of 3 when u is a predicate letter. Thus, different 
symbols have different Gödel numbers.
Examples
	
g
g
g
g
x
a
f
A
2
4
1
2
2
1
29
39
97
147
(
) =
(
) =
(
) =
(
) =
,
,
,
Given an expression u0u1 … ur, where each uj is a symbol of K, we define its 
Gödel number ɡ(u0u1 … ur) by the equation
	
g u u
u
p
r
g u
g u
r
g ur
0
1
2
3
0
1
…
(
) =
…
(
)
(
)
(
)
where pj denotes the jth prime number and we assume that p0 = 2. For 
example,
	
g
g
A x x
A
x
x
1
2
1
2
99
3
2
2
3
5
7
11
13
2 3 5
1
2
1
2
(
,
)
(
)
(()
(
)
(,)
(
)
())
(
) =
=
g
g
g
g
g
1
7
29
5
7 11 13
Observe that different expressions have different Gödel numbers, by virtue 
of the uniqueness of the factorization of integers into primes. In addition, 
expressions have different Gödel numbers from symbols, since the former 
have even Gödel numbers and the latter odd Gödel numbers. Notice also 
that a single symbol, considered as an expression, has a different Gödel 
number from its Gödel number as a symbol. For example, the symbol x1 has 
Gödel number 21, whereas the expression that consists of only the symbol x1 
has Gödel number 221.



193
Formal Number Theory
If e0, e1, …, er is any finite sequence of expressions of K, we can assign a 
Gödel number to this sequence by setting
	
g e
e
e
p
r
g e
g e
r
g er
0
1
2
3
0
1
,
,
,
…
(
) =
…
(
)
(
)
(
)
Different sequences of expressions have different Gödel numbers. Since a 
Gödel number of a sequence of expressions is even and the exponent of 2 in 
its prime power factorization is also even, it differs from Gödel numbers of 
symbols and expressions. Remember that a proof in K is a certain kind of 
finite sequence of expressions and, therefore, has a Gödel number.
Thus, ɡ is a one–one function from the set of symbols of K, expressions of K, and 
finite sequences of expressions of K, into the set of positive integers. The range of 
ɡ is not the whole set of positive integers. For example, 10 is not a Gödel number.
Exercises
3.32	 Determine the objects that have the following Gödel numbers.
	
a.	 1944  b. 49  c. 15  d. 13 824  e. 25131159
3.33	 Show that, if n is odd, 4n is not a Gödel number.
3.34	 Find the Gödel numbers of the following expressions.
	
a.	 f
a
1
1
1
(
)  b. ((
)
(
,
)))
∀
¬
x
A a x
3
1
2
1
3
(
This method of associating numbers with symbols, expressions and 
sequences of expressions was originally devised by Gödel (1931) in order to 
arithmetize metamathematics,* that is, to replace assertions about a formal 
system by equivalent number-theoretic statements and then to express these 
statements within the formal system itself. This idea turned out to be the key 
to many significant problems in mathematical logic.
The assignment of Gödel numbers given here is in no way unique. Other meth-
ods are found in Kleene (1952, Chapter X) and in Smullyan (1961, Chapter 1, § 6).
Definition
A theory K is said to have a primitive recursive vocabulary (or a recursive vocabu-
lary) if the following properties are primitive recursive (or recursive):
	
a.	IC(x): x is the Gödel number of an individual constant of K;
	
b.	FL(x): x is the Gödel number of a function letter of K;
	
c.	PL(x): x is the Gödel number of a predicate letter of K.
*	 An arithmetization of a theory K is a one–one function ɡ from the set of symbols of K, expres-
sions of K and finite sequences of expressions of K into the set of positive integers. The fol-
lowing conditions are to be satisfied by the function ɡ: (1) ɡ is effectively computable; (2) there 
is an effective procedure that determines whether any given positive integer m is in the range 
of ɡ and, if m is in the range of ɡ, the procedure finds the object x such that ɡ(x) = m.



194
Introduction to Mathematical Logic
Remark
Any theory K that has only a finite number of individual constants, func-
tion letters, and predicate letters has a primitive recursive vocabulary. For 
example, if the individual constants of K are a
a
a
j
j
jn
1
2
,
,
,
…
, then IC(x) if and 
only if x = 7 + 8j1 ∨ x = 7 + 8j2 ∨ … ∨ x = 7 + 8jn. In particular, any theory K in 
the language LA of arithmetic has a primitive recursive vocabulary. So, S has 
a primitive recursive vocabulary.
Proposition 3.26
Let K be a theory with a primitive recursive (or recursive) vocabulary. Then 
the following relations and functions (1–16) are primitive recursive (or recur-
sive). In each case, we give first the notation and intuitive definition for the 
relation or function, and then an equivalent formula from which its primi-
tive recursiveness (or recursiveness) can be deduced.
	 1.	 EVbl(x): x is the Gödel number of an expression consisting of a vari-
able, (∃z)z<x(1 ≤ z ∧ x = 213+8z). By Proposition 3.18, this is primitive 
recursive.
	
	 EIC(x): x is the Gödel number of an expression consisting of an indi-
vidual constant, (∃y)y<x(IC(y) ∧ x = 2y) (Proposition 3.18).
	
	 EFL(x): x is the Gödel number of an expression consisting of a func-
tion letter, (∃y)y<x(FL(y) ∧ x = 2y) (Proposition 3.18).
	
	 EPL(x): x is the Gödel number of an expression consisting of a predi-
cate letter, (∃y)y<x(PL(y) ∧ x = 2y) (Proposition 3.18).
	 2.	 Arg
qt
T( )
(
( ,
))
x
x
=
−
8
1
0

: If x is the Gödel number of a function letter 
fj
n, then ArgT(x) = n. ArgT(x) is primitive recursive.
	
	 Arg
qt
P( )
(
( ,
))
x
x
=
−
8
3
0

: If x is the Gödel number of a predicate letter 
Aj
n, then Arg
Arg
P
P
( )
.
( )
x
n
x
=
 is primitive recursive.
	 3.	 Gd(x): x is the Gödel number of an expression of K, EVbl(x) ∨ EIC(x) 
∨ EFL(x) ∨ EPL(x) ∨ x = 23 ∨ x = 25 ∨ x = 27 ∨ x = 29 ∨ x = 211∨ x = 213 ∨ 
(∃u)u<x(∃v)v<x(x = u * v ∧ Gd(u) ∧ Gd(v)). Use Corollary 3.21. Here, * is 
the juxtaposition function defined in Example 4 on page 182.
	 4.	 MP (x, y, z): The expression with Gödel number z is a direct conse-
quence of the expressions with Gödel numbers x and y by modus 
ponens, y
x
z
x
z
=
∧
∧
2
2
2
3
11
5
*
*
* *
Gd
Gd
( )
( ).
	 5.	 Gen(x, y): The expression with Gödel number y comes from the 
expression with Gödel number x by the generalization rule:
	
(
)
(
( )
( ))
∃
∧
=
∧
<
v
v
y
v
x
x
v y EVbl
Gd
2
2
2
2
2
3
3
13
5
5
*
*
*
*
*
*
	 6.	 Trm(x): x is the Gödel number of a term of K. This holds when and 
only when either x is the Gödel number of an expression consisting 
of a variable or an individual constant, or there is a function letter fk
n 



195
Formal Number Theory
and terms t1, …, tn such that x is the Gödel number of f
t
t
k
n
n
( ,
,
).
1 …
 
The latter holds if and only if there is a sequence of n + 1 expressions
	
f
f
t
f
t t
f
t
t
f
t
t
t
k
n
k
n
k
n
k
n
n
k
n
n
n
1
1
2
1
1
1
1
(
(
…
…
(
…
−
−
,
,
,
,
,
,
( ,
,
,
)
	
	 the last of which, f
t
t
k
n
n
( ,
,
)
1 …
, has Gödel number x. This 
sequence can be represented by its Gödel number y. Clearly, 
y
p
p
p
p
x
x
n
x
n
n
x
x
x
<
…
=
⋅⋅
⋅
<
<
2 3
2 3
(
)
(
!)
(
!) .
…
 Note that ℓh(y) = n + 1 
and also that n = ArgT((x)0), since (x)0 is the Gödel number of fk
n. 
Hence, Trm(x) is equivalent to the following relation:
	
EVbl
EIC
ArgT
( )
( )
(
)
( )
( )
(( ) )
[
(
)
( )
!
x
x
y
x
y
h y
x
y
p
h y
x x
∨
∨∃
=
∧
=
<
−
ℓ

ℓ
1
0 + ∧
∧
=
∧
=
∧∀
∃
<
−
<
1
3
2
0 0
0 1
0
2
FL((( ) ) )
(( ) )
(( ) )
(
)
(
)
( )
y
y
h y
u
v
u
h y
v x
ℓ
ℓ

(( )
( )
( ))
(
)
(( )
( )
( )
( )
y
y
v
v
v
y
y
u
u
v x
h y
h y
+
<
−
−
=
∧
∧
∃
=
1
7
1
2
2
*
*
Trm
ℓ

ℓ
 *
*
v
v
25 ∧Trm( ))]
	
	 Thus, Trm(x) is primitive recursive (or recursive) by Corollary 3.21, 
since the formula above involves Trm(v) for only v < x. In fact, if we 
replace both occurrences of Trm(v) in the formula by (z)v = 0, then the 
new formula defines a primitive recursive (or recursive) relation H(x, z), 
and Trm(x) ⇔ H(x, (CTrm)#(x)). Therefore, Corollary 3.21 is applicable.
	
7.	 Atfml(x): x is the Gödel number of an atomic wf of K. This holds if 
and only if there are terms t1, …, tn and a predicate letter Ak
n such 
that x is the Gödel number of A t
t
k
n
n
( ,
,
)
1 …
. The latter holds if and 
only if there is a sequence of n + 1 expressions:
	
A
A
t
A
t t
A
t
t
A t
t
t
k
n
k
n
k
n
k
n
n
k
n
n
n
1
1
2
1
1
1
1
(
…
(
…
(
…
−
−
,
,
,
,
,
,
( ,
,
,
)
	
	 the last of which, A t
t
k
n
n
( ,
,
)
1 …
, has Gödel number x. This sequence 
of expressions can be represented by its Gödel number y. Clearly, 
y < (px!)x (as in (6) above) and n = ArgP((x)0). Thus, Atfml(x) is equiva-
lent to the following:
	
(
)
( )
( )
(( ) )
((( ) ) )
[
(
!)
( )
∃
=
∧
=
+ ∧
∧
<
−
y
x
y
h y
x
y
y
p
h y
x
x
ℓ

ℓ
1
0
0 0
1
Arg
PL
P
(( ) )
(( ) )
(
)
(
)
(( )
( )
( )
y
h y
u
v
y
y
v
u
h y
v x
u
u
0 1
0
2
1
3
2
=
∧
=
∧
∀
∃
=
<
−
<
+
ℓ
ℓ

*
* 2
2
7
1
2
5
∧
∧
∃
=
∧
<
−
−
Trm
Trm
( ))
(
)
(( )
( )
( ))]
( )
( )
v
v
y
y
v
v
v x
h y
h y
ℓ

ℓ
 *
*
	
	 Hence, by Proposition 3.18, Atfml(x) is primitive recursive (or 
recursive)



196
Introduction to Mathematical Logic
	 8.	 Fml(y): y is the Gödel number of a formula of K:
	
Atfml
Fml
Fml
Fml
( )
(
)
(
( )
)
(
(( ) )
(( )
[
y
z
z
y
z
z
z
z
y
∨∃
∧
=
∨
∧
<3
3
9
5
0
2
2
2
*
* *
1
3
0
11
1
5
0
1
3
3
2
2
2
2
2
2
)
( )
( )
)
(
(( ) )
(( ) )
∧
=
∨
∧
∧
=
y
z
z
z
z
y
*
*
*
*
*
*
Fml
EVbl
13
1
5
0
5
2
2
*
*
*
*
( )
( )
)]
z
z
	
	 It is easy to verify that Corollary 3.21 is applicable.
	 9.	 Subst(x, y, u, v): x is the Gödel number of the result of substituting in 
the expression with Gödel number y the term with Gödel number u 
for all free occurrences of the variable with Gödel number v:
	
Gd
Trm
EVbl
( )
( )
(
)
[(
)
(
)
(
)
(
y
u
y
x
u
w
y
y
x
y
v
v
w y
w
v
∧
∧
∧
=
∧
=
∨
∃
=
∧
≠
∧
=
∨
<
2
2
2
2
∃
∃
∧
=
∧
∃
=
<
<
<
z
w
w
y
w z
x
z y
w y
v
x
)
(
)
(
( )
(
)
(
Fml
2
2
2
2
2
2
3
13
5
3
13
*
*
*
*
*
*
*
α α
2
2
2
2
5
3
1
v
z y
w y
w
z u v
z
w
w
y
*
*
*
*
α
α
∧
∨
¬ ∃
∃
∧
=
<
<
Subst
Fml
( , , , )))
(
)
(
)
(
( )
3
5
2
2
1
2
0
*
*
*
*
*
*
v
x
x
z y
y
w z
z
z
y
z
x
(
)
(
) ∧
∃
∃
∃
<
∧
=
∧
=
<
<
<
(
)
(
)
(
)
(
( )
α
β
α β
α
β
∧
∧
Subst
Subst
( ,
, , )
( , , , )))]
( )
α
β
2
0
y
u v
z u v
	
	 Corollary 3.21 is applicable.* The reader should verify that this for-
mula actually captures the intuitive content of Subst(x, y, u, v).
	 10.	 SuB (y, u, v): the Gödel number of the result of substituting the term 
with Gödel number u for all free occurrences in the expression with 
Gödel number y of the variable with Gödel number v:
	
Sub
Subst
( , , )
( , , , )
(
!)
y u v
x
u y u v
x
puy
uy
=
<
µ
	
	 Therefore, Sub is primitive recursive (or recursive) by Proposition 
3.18. (When the conditions on u, v, and y are not met, SuB (y, u, v) is 
defined, but its value is of no interest.)
	 11.	 Fr(y, v): y is the Gödel number of a wf or term of K that contains free 
occurrences of the variable with Gödel number v:
	
(
( )
( ))
(
)
( , ,
)
,
Fml
Trm
EVbl
Subst
y
y
y y
v
v
v
∨
∧
∧¬
+
2
213 8
*	 Actually a simultaneous recursion in x and y is involved. In the given formula, replace “x” 
by “(q)0” and “y” by “(q)1” and the result by Corollary 3.21 yields a recursive relation R(q, u, v). 
Now define Subst(x, y, u, v) as R(2x3y, u, v).



197
Formal Number Theory
	
	 (That is, substitution in the wf or term with Gödel number y of a 
certain variable different from the variable with Gödel number v 
for all free occurrences of the variable with Gödel number v yields 
a different expression.)
	 12.	 Ff(u, v, w): u is the Gödel number of a term that is free for the vari-
able with Gödel number v in the wf with Gödel number w:
	
Trm
EVbl
Fml
Atfml
Ff
( )
(
)
( )
[
( )
(
)
(
(
u
w
w
y
w
y
u
v
y w
∧
∧
∧
∧∃
=
∧
<
2
2
2
2
3
9
5
*
*
*
, , ))
(
)
(
)
(
( , , )
( , , )
v y
y
z
w
y
z
u v y
u v z
y w
z w
∨∃
∃
=
∧
∧
<
<
2
2
2
3
11
5
*
*
* *
Ff
Ff
)
(
)
(
)
(
(
)
(
(
∨
∃
∃
=
∧
∧
≠
⇒
<
<
y
z
w
y
z
v
y w
z w
z
z
2
2
2
2
2
2
2
3
3
13
5
5
*
*
*
*
*
*
EVbl
Ff u v y
u z
y v
, , )
(
( , )
( , ))))]
∧
⇒¬
Fr
Fr
	
	 Use Corollary 3.21 again.
	 13.	 a.	 Ax1(x): x is the Gödel number of an instance of axiom schema (A1):
	
(
)
(
)
( )
( )
(
)
∃
∃
∧
∧
=
<
<
u
v
u
v
x
u
v
u
u x
v x Fml
Fml
2
2
2
2
2
2
3
11
3
11
5
5
*
*
*
*
*
*
*
*
	
b.	 Ax2(x): x is the Gödel number of an instance of axiom schema (A2):
	
(
)
(
)
(
)
( )
( )
( )
(
∃
∃
∃
∧
∧
∧
=
<
<
<
u
v
w
u
v
w
x
u
u x
v x
w x Fml
Fml
Fml
2
2
2
2
3
3
11
*
*
*
*
3
11
5
5
11
3
3
11
5
11
3
11
5
5
2
2
2
2
2
2
2
2
2
2
2
2
2
*
*
*
*
*
*
*
*
*
*
*
*
*
*
*
*
*
*
*
v
w
u
v
u
w
* 25)
	
c.	 Ax3(x): x is the Gödel number of an instance of axiom schema (A3):
	
(
)
(
)
( )
( )
(
∃
∃
∧
∧
=
<
<
u
v
u
v
x
v
u x
v x Fml
Fml
2
2
2
2
2
2
2
2
3
3
3
9
5
11
3
9
*
*
*
*
*
*
*
*
* u
v
u
v
*
*
*
*
*
*
*
*
*
*
*
*
*
*
*
*
2
2
2
2
2
2
2
2
2
2
2
2
2
5
5
11
3
3
3
9
5
11
5
11
5
5)
	
d.	 Ax4(x): x is the Gödel number of an instance of axiom schema (A4):
	
(
)
(
)
(
)
( )
( )
(
)
( , , )
(
∃
∃
∃
∧
∧
∧
∧
=
<
<
<
u
v
y
y
u
u v y
x
u x
v x
y x
v
Fml
Trm
EVbl
Ff
2
23
3
3
13
5
11
5
2
2
2
2
2
2
2
*
*
*
*
*
*
*
*
*
v
y
y u v
Sub( , , )
)



198
Introduction to Mathematical Logic
	
e.	 Ax5(x): x is the Gödel number of an instance of axiom schema (A5):
	
(
)
(
)
(
)
( )
( )
(
)
( , )
(
∃
∃
∃
∧
∧
∧¬
∧
=
<
<
<
u
v
w
u
w
u v
x
u x
v x
w x
v
Fml
Fml
EVbl
Fr
2
23 *
*
*
*
*
*
*
*
*
*
*
*
*
*
*
*
*
*
*
2
2
2
2
2
2
2
2
2
2
2
2
2
2
2
3
3
13
5
3
11
5
5
11
3
11
3
3
13
v
u
w
u
2
2
2
2
2
5
5
5
5
v
w
*
*
*
*
*
)
	
f.	 LAX(y): y is the Gödel number of a logical axiom of K
	
Ax
Ax
Ax
Ax
Ax
1
2
3
4
5
( )
( )
( )
( )
( )
y
y
y
y
y
∨
∨
∨
∨
	 14.	 The following negation function is primitive recursive. Neg(x): the 
Gödel number of (¬B) if x is the Gödel number of B:
	
Neg( )
x
x
= 2
2
2
3
9
5
*
*
*
	 15.	 The following conditional function is primitive recursive. Cond(x, y): 
the Gödel number of (B ⇒ C) if x is the Gödel number of B and y is 
the Gödel number of C:
	
Cond( , )
x y
x
y
= 2
2
2
3
11
5
*
*
*
*
	 16.	 Clos(u): the Gödel number of the closure of B if u is the Gödel num-
ber of a wf B. First, let V(u) = μvv≤u(EVbl(2v) ∧ Fr(u, v)). V is primi-
tive recursive (or recursive). V(u) is the least Gödel number of a free 
variable of u (if there are any). Let Sent(u) be Fml(u) ∧ ¬(∃v)v≤uFr(u, v). 
Sent is primitive recursive (or recursive). Sent(u) holds when and 
only when u is the Gödel number of a sentence (i.e., a closed wf). 
Now let
	
G
if Fml
Sent
otherwise
( )
( )
( )
( )
u
u
u
u
u
V u
=
∧¬

2
2
2
2
2
2
3
3
13
5
5
*
*
*
*
*
*

G is primitive recursive (or recursive). If u is the Gödel number of a wf B that 
is not a closed wf, then G(u) is the Gödel number of (∀x)B, where x is the free 
variable of B that has the least Gödel number. Otherwise, G(u) = u. Now, let
	
H
G
H
G H
( , )
( )
( ,
)
(
( , ))
u
u
u y
u y
0
1
=
+
=
H is primitive recursive (or recursive). Finally,
	
Clos
H
H
H
( )
( ,
(
( , )
( ,
)))
u
u
y
u y
u y
y u
=
=
+
≤
µ
1
Thus, Clos is primitive recursive (or recursive).



199
Formal Number Theory
Proposition 3.27
Let K be a theory having a primitive recursive (or recursive) vocabulary and 
whose language contains the individual constant 0 and the function letter 
f1
1 of LA. (Thus, all the numerals are terms of K. In particular, K can be S 
itself.) Then the following functions and relation are primitive recursive (or 
recursive).
	 17.	 Num(y): the Gödel number of the expression y
	
Num
Num
Num
( )
(
)
( )
0
2
1
2
2
2
15
49
3
5
=
+
=
y
y
*
*
*
	
	 Num is primitive recursive by virtue of the recursion rule (V).
	 18.	 Nu(x): x is the Gödel number of a numeral
	
(
)
(
( ))
∃
=
<
y
x
y
y x
Num
	
	 Nu is primitive recursive by Proposition 3.18.
	 19.	 D(u): the Gödel number of B u
( ), if u is the Gödel number of a wf B (x1):
	
D( )
( ,
( ),
)
u
u
u
= Sub
Num
21
	
	 Thus, D is primitive recursive (or recursive). D is called the diagonal 
function.
Definition
A theory K will be said to have a primitive recursive (or recursive) axiom set if 
the following property PrAx is primitive recursive (or recursive):
	
PrAx
is the Godel number of a proper axiom of K
( ):
y
y

Notice that S has a primitive recursive axiom set. Let a1, a2, …, a8 be the 
Gödel numbers of axioms (S1)–(S8). It is easy to see that a number y is the Gödel 
number of an instance of axiom schema (S9) if and only if
	
(
)
(
)
(
(
)
( )
( ,
, )
∃
∃
∧
∧
=
<
<
v
w
w
y
w
v
v y
w y
v
EVbl
Fml
Sub
2
2
2
2
2
2
3
15
11
3
3
*
*
*
*
*
*
*
*
*
*
*
*
*
*
*
*
*
*
*
2
2
2
2
2
2
2
2
2
2
2
2
2
2
3
13
5
3
11
49
3
5
5
5
11
3
v
v
w
w
v
Sub( ,
, )
*
*
*
*
*
*
*
2
2
2
2
2
2
3
13
5
5
5
v
w
)



200
Introduction to Mathematical Logic
Denote the displayed formula by A9(y). Then y is the Gödel number of a 
proper axiom of S if and only if
	
y
a
y
a
y
a
y
=
∨
=
∨… ∨
=
∨
1
2
8
9
A ( )
Thus, PrAx(y) is primitive recursive for S.
Proposition 3.28
Let K be a theory having a primitive recursive (or recursive) vocabulary and 
a primitive recursive (or recursive) axiom set. Then the following three rela-
tions are primitive recursive (or recursive).
	 20.	 Ax(y): y is the Gödel number of an axiom of K:
	
LAX
PrAx
( )
( )
y
y
∨
	 21.	 Prf(y): y is the Gödel number of a proof in K:
	
(
)
(
)
(
)
(
)
([
( )]
( )
(( )
[
∃
∃
∃
∃
=
∧
∨
∧
<
<
<
<
u
v
z
w
y
w
u
u
u y
v y
z y
w y
w
w
2
Ax
Prf
Fml
)
(( ) , )]
( )
(( ) )
(( ) )
[
∧
=
∧
∨
∧
∧
∧
=
∧
y
u
u
v
u
u
u
y
u
v
w
z
w
v
*
*
2
2
Gen
Prf
Fml
Fml
MP
Prf
Ax
(( ) ,( ) , )]
[
( )
( )]
u
u
v
u
y
u
v
z
w
v
∨
∧
=
∧
* 2
	
	 Apply Corollary 3.21.
	 22.	 Pf(y, x): y is the Gödel number of a proof in K of the wf with Gödel 
number x:
	
Prf( )
( ) ( )
y
x
y lh y
∧
=
− 1
The relations and functions of Propositions 3.26–3.28 should have the sub-
script “K” attached to the corresponding signs to indicate the dependence 
on K. If we considered a different theory, then we would obtain different 
relations and functions.
Exercise
3.35	 a.	 If K is a theory for which the property Fml(y) is primitive recursive 
(or recursive), prove that K has a primitive recursive (or recursive) 
vocabulary.
	
b.	 Let K be a theory for which the property Ax(y) is primitive recur-
sive (or recursive).



201
Formal Number Theory
	
	
i.	
Show that K has a primitive recursive (or recursive) vocabulary.
	
	
ii.	 Assuming also that no proper axiom of K is a logical axiom, 
prove that K has a primitive recursive (or recursive) axiom set.
Proposition 3.29
Let K be a theory with equality whose language contains the individual con-
stant 0 and the function letter f1
1 and such that K has a primitive recursive (or 
recursive) vocabulary and axiom set. Also assume:
	
∗( )
=
=
For any natural numbers
and
if
then
K
r
s
r
s
r
s
,
,
.
⊢
Then any function f(x1, …, xn) that is representable in K is recursive.
Proof
Let B (x1, …, xn, xn+1) be a wf of K that represents f. Let PB(u1, …, un, un+1, y) mean 
that y is the Gödel number of a proof in K of the wf B u
u
u
n
n
1
1
,
,
,
.
…
(
)
+
 Note 
that, if PB(u1, …, un, un+1, y), then f(u1, …, un) = un+1. (In fact, let f(u1, …, un) = r. 
Since B represents f in K, ⊢K B u
u
r
n
1,
,
,
…
(
) and ⊢K ∃
(
)
…
(
)
1
1
y
u
u
y
n
B
,
,
,
. By 
hypothesis, PB(u1, …, un, un+1, y). Hence, ⊢K B u
u
u
n
n
1
1
,
,
,
…
(
)
+
. Since K is a the-
ory with equality, it follows that ⊢K r
un
=
+1. By (*), r = un+1.) Now let m be the 
Gödel number of B (x1, …, xn, xn+1). Then PB (u1, …, un, un+1, y) is equivalent to:
	 Pf
Sub
Sub Sub m Num
Num
Num
( ,
(
(
(
,
(
),
),
(
),
)
(
),
y
u
u
un
…
…
+
+
1
2
1
21
29
21
8n))
So, by Propositions 3.26–3.28, PB (u1, …, un, un+1, y) is primitive recursive (or 
recursive). Now consider any natural numbers k1, …, kn. Let f(k1, …, kn) = r. Then 
⊢K B k
k
r
n
1,
,
,
.
…
(
)  Let j be the Gödel number of a proof in K of B k
k
r
n
1,
,
,
.
…
(
)  
Then P
k
k
r j
n
B
1,
,
, ,
…
(
). Thus, for any x1, …, xn, there is some y such that PB (x1, 
…, xn, (y)0, (y)1). Then, by Exercise 3.16(c), μy(PB (x1, …, xn, (y)0, (y)1)) is recursive. 
But, f(x1, …, xn) = (μy(PB (x1, …, xn, (y)0, (y)1)))0 and, therefore, f is recursive.
Exercise
3.36	 Let K be a theory whose language contains the predicate letter =, the 
individual constant 0, and the function letter f1
1.
	
a.	 If K satisfies hypothesis (*) of Proposition 3.29, prove that K must be 
consistent.
	
b.	 If K is inconsistent, prove that every number-theoretic function is 
representable in K.
	
c.	 If K is consistent and the identity relation x = y is expressible in K, 
show that K satisfies hypothesis (*) of Proposition 3.29.



202
Introduction to Mathematical Logic
Corollary 3.30
Assume S consistent. Then the class of recursive functions is identical with 
the class of functions representable in S.
Proof
We have observed that S has a primitive recursive vocabulary and axiom 
set. By Exercise 3.36(c) and the already noted fact that the identity relation is 
expressible in S, we see that Proposition 3.29 entails that every function rep-
resentable in S is recursive. On the other hand, Proposition 3.24 tells us that 
every recursive function is representable in S.
In Chapter 5, it will be made plausible that the notion of recursive function 
is a precise mathematical equivalent of the intuitive idea of effectively comput-
able function.
Corollary 3.31
A number-theoretic relation R(x1, …, xn) is recursive if and only if it is express-
ible in S.
Proof
By definition, R is recursive if and only if CR is recursive. By Corollary 3.30, 
CR is recursive if and only if CR is representable in S. But, by Proposition 3.13, 
CR is representable in S if and only if R is expressible in S.
It will be helpful later to find weaker theories than S for which the repre-
sentable functions are identical with the recursive functions. Analysis of the 
proof of Proposition 3.24 leads us to the following theory.
Robinson’s System
Consider the theory in the language LA with the following finite list of proper 
axioms.
	 1.	 x1 = x1
	 2.	 x1 = x2 ⇒ x2 = x1
	 3.	 x1 = x2 ⇒ (x2 = x3 ⇒ x1 = x3)
	 4.	 x1 = x2 ⇒ x1′ = x2′
	 5.	 x1 = x2 ⇒ (x1 + x3 = x2 + x3 ∧ x3 + x1 = x3 + x2)
	 6.	 x1 = x2 ⇒ (x1 · x3 = x2 · x3 ∧ x3 · x1 = x3 · x2)
	
7.	 x1′ = x2′ ⇒ x1 = x2
	 8.	 0 ≠ x1′
	 9.	 x1 ≠ 0 ⇒ (∃x2)(x1 = x2′)
	 10.	 x1 + 0 = x1



203
Formal Number Theory
	 11.	 x1 + x2′ = (x1 + x2)′
	 12.	 x1 · 0 = 0
	 13.	 x1 · x2′ = (x1 · x2) + x1
	 14.	 (x2 = x1 · x3 + x4 ∧ x4 < x1 ∧ x2 = x1 · x5 + x6 ∧ x6 < x1) ⇒ x4 = x6 (unique-
ness of remainder)
We shall call this theory RR. Clearly, RR is a subtheory of S, since all the axioms 
of RR are theorems of S. In addition, it follows from Proposition 2.25 and axioms 
(1)–(6) that RR is a theory with equality. (The system Q of axioms (1)–(13) is due 
to R.M. Robinson (1950). Axiom (14) has been added to make one of the proofs 
below easier.) Notice that RR has only a finite number of proper axioms.
Lemma 3.32
In RR, the following are theorems.
	 a.	 n
m
n
m
+
=
+
 for any natural numbers n and m
	 b.	 n m
n m
⋅
=
⋅
 for any natural numbers n and m
	
c.	 n
m
≠
 for any natural numbers such that n ≠ m
	 d.	 n
m
<
 for any natural numbers n and m such that n
m
<
	 e.	 x ≮ 0
	
f.	 x
n
x
x
x
n
≤
⇒
=
∨
=
∨… ∨
=
0
1
 for any natural number n
	 g.	 x
n
n
x
≤
∨
≤ for any natural number n
Proof
Parts (a)–(c) are proved the same way as Proposition 3.6(a). Parts (d)–(g) are 
left as exercises.
Proposition 3.33
All recursive functions are representable in RR.
Proof
The initial functions Z, N, and Ui
n are representable in RR by the same wfs 
as in Examples 1–3, page 171. That the substitution rule does not lead out of 
the class of functions representable in RR is proved in the same way as in 
Example 4 on page 172. For the recursion rule, first notice that β(x1, x2, x3) is 
represented in RR by Bt(x1, x2, x3, y) and that ⊢RR Bt(x1, x2, x3, y) ∧ Bt(x1, x2, x3, z) 
⇒ y = z. Reasoning like that in the proof of Proposition 3.24 shows that the 
recursion rule preserves representability in RR.* The argument given for the 
restricted μ-operator rule also remains valid for RR.
*	 This part of the argument is due to Gordon McLean, Jr.



204
Introduction to Mathematical Logic
By Proposition 3.33, all recursive functions are representable in any exten-
sion of RR. Hence, by Proposition 3.29 and Exercise 3.36(c), in any consistent 
extension of RR in the language LA that has a recursive axiom set, the class 
of representable functions is the same as the class of recursive functions. 
Moreover, by Proposition 3.13, the relations expressible in such a theory are 
the recursive relations.
Exercises
3.37D	 Show that RR is a proper subtheory of S. [Hint: Find a model for RR 
that is not a model for S.] (Remark: Not only is S different from RR, but 
it is not finitely axiomatizable at all, that is, there is no theory K having 
only a finite number of proper axioms, whose theorems are the same 
as those of S. This was proved by Ryll-Nardzewski, 1953.)
3.38	
Show that axiom (14) of RR is not provable from axioms (1)–(13) and, 
therefore, that Q is a proper subtheory of RR. [Hint: Find a model of 
(1)–(13) for which (14) is not true.]
3.39	
Let K be a theory in the language LA with just one proper axiom: (∀x1)
(∀x2)x1 = x2.
	
a.	
Show that K is a consistent theory with equality.
	
b.	 Prove that all number-theoretic functions are representable in K.
	
c.	
Which number-theoretic relations are expressible in K? [Hint: Use 
elimination of quantifiers.]
	
d.	 Show that the hypothesis ⊢K 0 ≠ 1 cannot be eliminated from 
Proposition 3.13.
	
e.	
Show that, in Proposition 3.29, the hypothesis (*) cannot be 
replaced by the assumption that K is consistent.
3.40	
Let R be the theory in the language LA having as proper axioms the 
equality axioms (1)–(6) of RR as well as the following five axiom sche-
mas, in which n and m are arbitrary natural numbers:
	
(R1) n
m
n
m
+
=
+
	
(R2) n m
n m
⋅
=
⋅
	
(R3) n
m
n
m
≠
≠
if
	
(R4) x
n
x
x
n
≤
⇒
=
∨… ∨
=
0
	
(R5) x
n
n
x
≤
∨
≤
	
Prove the following.
	
a.	
R is not finitely axiomatizable. [Hint: Show that every finite subset 
of the axioms of R has a model that is not a model of R.]
	
b.	 R is a proper subtheory of Q.



205
Formal Number Theory
	
c.D	
Every recursive function is representable in R. (See Monk, 1976, p. 248.)
	
d.	 The functions representable in R are the recursive functions.
	
e.	
The relations expressible in R are the recursive relations.
3.5  The Fixed-Point Theorem: Gödel’s Incompleteness Theorem
If K is a theory in the language LA, recall that the diagonal function D has the 
property that, if u is the Gödel number of a wf B (x1), then D(u) is the Gödel 
number of the wf B u
( ).
Notation
When C is an expression of a theory and the Gödel number of C is q, then we 
shall denote the numeral q by ⌜⌝
C . We can think of ⌜⌝
C  as being a “name” for 
C within the language LA.
Proposition 3.34 (Diagonalization Lemma)
Assume that the diagonal function D is representable in a theory with equal-
ity K in the language LA. Then, for any wf E (x1) in which x1 is the only free 
variable, there exists a closed wf C  such that
	
⊢
⌜⌝
K C
E
C
⇔
(
)
Proof
Let D(x1, x2) be a wf representing D in K. Construct the wf
	
∇
( ) ∀
(
)
(
) ⇒
(
)
(
)
x
x x
x
2
1
2
2
D
E
,
Let m be the Gödel number of (∇). Now substitute m for x1 in (∇):
	
C
D
E
( ) ∀
(
)
(
) ⇒
(
)
(
)
x
m x
x
2
2
2
,
Let q be the Gödel number of this wf C. So, q is ⌜⌝
C . Clearly, D(m) = q. (In fact, 
m is the Gödel number of a wf B (x1), namely, (∇), and q is the Gödel number 
of B m
( ).) Since D represents D in K,
	
∂( )
(
)
⊢K D m q
,



206
Introduction to Mathematical Logic
	 a.	 Let us show ⊢K C
E
⇒( )
q .
	
1.	 C	
Hyp
	
2.	
∀
(
)
(
) ⇒
(
)
(
)
x
m x
x
2
2
2
D
E
,
	
Same as 1
	
3.	 D
E
m q
q
,
(
) ⇒( )	
2, rule A4
	
4.	 D m q
,
(
) 	
(∂)
	
5.	 E q( )	
3, 4, MP
	
6.	 C
E
⊢K
q( ) 	
1–5
	
7.	 ⊢K C
E
⇒( )
q 	
1–6, Corollary 2.6
	 b.	 Let us prove ⊢K E
C
q( ) ⇒
.
	
1.	 E q( )	
Hyp
	
2.	 D m x
,
2
(
)	
Hyp
	
3.	
∃
(
)
(
)
1
2
2
x
m x
D
,
	
D represents D
	
4.	 D m q
,
(
)	
(∂)
	
5.	 x
q
2 = 	
2–4, properties of =
	
6.	 E x2
(
)	
1, 5, substitutivity of =
	
7.	 E
D
E
q
m x
x
( )
(
)
(
)
,
,
2
2
⊢K
	
1–6
	
8.	 E
D
E
q
m x
x
( )
(
) ⇒
(
)
⊢K
,
2
2 	
1–7, Corollary 2.6
	
9.	 E
D
E
q
x
m x
x
( )
∀
(
)
(
) ⇒
(
)
(
)
⊢K
2
2
2
,
	
8, Gen
	
10.	 ⊢K E
D
E
q
x
m x
x
( ) ⇒∀
(
)
(
) ⇒
(
)
(
)
2
2
2
,
	 1–9, Corollary 2.6
	
11.	 ⊢K E
C
q( ) ⇒
	
Same as 10
From parts (a) and (b), by biconditional introduction, ⊢K C
E
⇔
( )
q .
Proposition 3.35 (Fixed-Point Theorem)*
Assume that all recursive functions are representable in a theory with equal-
ity K in the language LA. Then, for any wf E (x1) in which x1 is the only free 
variable, there is a closed wf C such that
	
⊢
⌜⌝
K C
E
C
⇔
(
)
*	 The terms “fixed-point theorem” and “diagonalization lemma” are often used interchange-
ably, but I have adopted the present terminology for convenience of reference. The central 
idea seems to have first received explicit mention by Carnap (1934), who pointed out that the 
result was implicit in the work of Gödel (1931). The use of indirect self-reference was the key 
idea in the explosion of progress in mathematical logic that began in the 1930s.



207
Formal Number Theory
Proof
By Proposition 3.27, D is recursive.* Hence, D is representable in K and 
Proposition 3.34 is applicable.
By Proposition 3.33, the fixed-point theorem holds when K is RR or any 
extension of RR. In particular, it holds for S.
Definitions
Let K be any theory whose language contains the individual constant 0 and 
the function letter f1
1. Then K is said to be ω-consistent if, for every wf B (x) of 
K containing x as its only free variable, if ⊢K ¬
( )
B n  for every natural number 
n, then it is not the case that ⊢K (∃x)B (x).
Let K be any theory in the language LA. K is said to be a true theory if all 
proper axioms of K are true in the standard model. (Since all logical axioms 
are true in all models and MP and Gen lead from wfs true in a model to wfs 
true in that model, all theorems of a true theory will be true in the standard 
model.)
Any true theory K must be ω-consistent. (In fact, if ⊢K ¬
( )
B n  for all natural 
numbers n, then B (x) is false for every natural number and, therefore, (∃x)B 
(x) cannot be true for the standard model. Hence, (∃x)B (x) cannot be a theo-
rem of K.) In particular, RR and S are ω-consistent.
Proposition 3.36
If K is ω-consistent, then K is consistent.
Proof
Let E(x) be any wf containing x as its only free variable. Let B (x) be E(x) ∧ 
¬E(x). Then ¬
( )
B n  is an instance of a tautology. Hence, ⊢K ¬
( )
B n  for every 
natural number n. By ω-consistency, not-⊢K (∃x)B (x). Therefore, K is consis-
tent. (Remember that every wf is provable in an inconsistent theory, by virtue 
of the tautology ¬A ⇒ (A ⇒ B). Hence, if at least one wf is not provable, the 
theory must be consistent.)
It will turn out later that the converse of Proposition 3.36 does not hold.
*	 In fact, D is primitive recursive, since K, being a theory in LA, has a primitive recursive 
vocabulary.



208
Introduction to Mathematical Logic
Definition
An undecidable sentence of a theory K is a closed wf B of K such that neither B 
nor ¬B is a theorem of K, that is, such that not-⊢K B and not-⊢K ¬B.
Gödel’s Incompleteness Theorem
Let K be a theory with equality in the language LA satisfying the following 
three conditions:
	 1.	 K has a recursive axiom set (that is, PrAx(y) is recursive).
	 2.	 ⊢K 0
1
≠.
	 3.	 Every recursive function is representable in K.
By assumption 1, Propositions 3.26–3.28 are applicable. By assumptions 
2 and 3 and Proposition 3.13, every recursive relation is expressible in K. 
By assumption 3, the fixed-point theorem is applicable. Note that K can 
be taken to be RR, S, or, more generally, any extension of RR having a 
recursive axiom set. Recall that Pf(y, x) means that y is the Gödel number 
of a proof in K of a wf with Gödel number x. By Proposition 3.28, Pf is 
recursive. Hence, Pf is expressible in K by a wf PF (x2, x1). Let E (x1) be the 
wf (∀x2) ¬P F (x2, x1). By the fixed-point theorem, there must be a closed 
wf G such that
	
$
,
.
( )
⇔∀
(
)¬
(
)
⊢
⌜⌝
K G
Pf
G
x
x
2
2
Observe that, in terms of the standard interpretation, ∀
(
)¬
(
)
x
x
2
2
Pf
G
,⌜⌝ says 
that there is no natural number that is the Gödel number of a proof in K of the 
wf G, which is equivalent to asserting that there is no proof in K of G. Hence, 
G is equivalent in K to an assertion that G is unprovable in K. In other words, 
G says “I am not provable in K”. This is an analogue of the liar paradox: “I am 
lying” (that is, “I am not true”). However, although the liar paradox leads to 
a contradiction, Gödel (1931) showed that G is an undecidable sentence of K. 
We shall refer to G as a Gödel sentence for K.
Proposition 3.37 (Gödel’s Incompleteness Theorem)
Let K satisfy conditions 1–3. Then
	
a.	If K is consistent, not-⊢K G.
	
b.	If K is ω-consistent, not-⊢K ¬G.
Hence, if K is ω-consistent, G is an undecidable sentence of K.



209
Formal Number Theory
Proof
Let q be the Gödel number of G.
	 a.	 Assume ⊢K G. Let r be the Gödel number of a proof in K of G. Then 
Pf(r, q). Hence, ⊢K
r q
P f
,
(
), that is ⊢
⌜⌝
K
r
P f
G
,
(
). But, from ($) 
above by biconditional elimination, ⊢K(∀x2) ¬P  f (x2, ⌊G ⌋). By rule A4, 
⊢
⌜⌝
K ¬
(
)
Pf
G
r ,
. Therefore, K is inconsistent.
	 b.	 Assume K is ω-consistent and ⊢K ¬G. From ($) by biconditional elim-
ination, ⊢K ¬(∀x2)¬P  f (x2, ⌜G⌝), which abbreviates to
	
∗( )
∃
(
)
(
)
⊢
⌜⌝
K
x
x
2
2
P f
G
,
On the other hand, since K is ω-consistent, Proposition 3.36 implies that K 
is consistent. But, ⊢K ¬G. Hence, not-⊢K G, that is, there is no proof in K of G. 
So, Pf(n, q) is false for every natural number n and, therefore, ⊢
⌜⌝
K ¬
(
)
Pf
G
n,
 
for every natural number n. (Remember that ⌜G⌝ is q.) By ω-consistency, not-
⊢K(∃x2)P  f (x2, ⌜G⌝), contradicting (*).
Remarks
Gödel’s incompleteness theorem has been established for any theory with 
equality K in the language LA that satisfies conditions 1–3 above. Assume 
that K also satisfies the following condition:
	
( )
.
+
K is a true theory
(In particular, K can be S or any subtheory of S.) Proposition 3.37(a) shows 
that, if K is consistent, G is not provable in K. But, under the standard inter-
pretation, G asserts its own unprovability in K. Therefore, G is true for the 
standard interpretation.
Moreover, when K is a true theory, the following simple intuitive argu-
ment can be given for the undecidability of G in K.
	
i.	 Assume ⊢K G. Since ⊢K G ⇔ (∀x2) ¬P f  (x2, ⌜G⌝), it follows that ⊢K(∀x2) 
¬P  f  (x2, ⌜G⌝). Since K is a true theory, (∀x2) ¬P  f (x2, ⌜G⌝) is true 
for the standard interpretation. But this wf says that G is not 
provable in K, contradicting our original assumption. Hence, 
not-⊢K G.
	 ii.	 Assume ⊢K ¬G. Since ⊢K G ⇔ (∀x2) ¬P  f (x2, ⌜G⌝), ⊢K ¬(∀x2) ¬ P  f (x2, ⌜G⌝). 
So, ⊢K (∃x2)P  f (x2, ⌜G⌝). Since K is a true theory, this wf is true for the 
standard interpretation, that is, G is provable in K. This contradicts 
the result of (i). Hence, not-⊢K ¬G.



210
Introduction to Mathematical Logic
Exercises
3.41	 Let G be a Gödel sentence for S. Let Sg be the extension of S obtained 
by adding ¬G as a new axiom. Prove that, if S is consistent, then Sg is 
consistent, but not ω-consistent.
3.42	 A theory K whose language has the individual constant 0 and func-
tion letter f1
1 is said to be ω-incomplete if there is a wf E (x) with one free 
variable x such that ⊢K E n
( ) for every natural number n, but it is not 
the case that ⊢K (∀x)E (x). If K is a consistent theory with equality in the 
language LA and satisfies conditions 1–3 on page 208, show that K is 
ω-incomplete. (In particular, RR and S are ω-incomplete.)
3.43	 Let K be a theory whose language contains the individual constant 0 
and function letter f1
1. Show that, if K is consistent and ω-inconsistent, 
then K is ω-incomplete.
3.44	 Prove that S, as well as any consistent extension of S having a recursive 
axiom set, is not a scapegoat theory. (See page 85.)
3.45	 Show that there is an ω-consistent extension K of S such that K is not a 
true theory. [Hint: Use the fixed point theorem.]
The Gödel–Rosser Incompleteness Theorem
The proof of undecidability of a Gödel sentence G required the assumption 
of ω-consistency. We will now prove a result of Rosser (1936) showing that, at 
the cost of a slight increase in the complexity of the undecidable sentence, the 
assumption of ω-consistency can be replaced by consistency.
As before, let K be a theory with equality in the language LA satisfying 
conditions 1–3 on page 208. In addition, assume:
	
4.	⊢K x
n
x
x
x
n
≤
⇒
=
∨
=
∨… ∨
=
0
1
 for every natural number n.
	
5.	⊢K x
n
n
x
≤
∨
≤ for every natural number n.
Thus, K can be any extension of RR with a recursive axiom set. In particular, 
K can be RR or S.
Recall that, by Proposition 3.26 (14), Neg is a primitive recursive function 
such that, if x is the Gödel number of a wf B, then Neg(x) is the Gödel num-
ber of (¬B). Since all recursive functions are representable in K, let Neg(x1, x2) 
be a wf that represents Neg in K. Now construct the following wf E (x1):
	
∀
(
)
(
) ⇒∀
(
)
(
) ⇒∃
(
)
≤
∧
(
)
(
)
(
)
(
)
x
x
x
x
x x
x
x
x
x
x
2
2
1
3
1
3
4
4
2
4
3
Pf
Neg
Pf
,
,
,
By the fixed-point theorem, there is a closed wf R such that
	
*( )
⇔
(
)
⊢
⌜
⌝
K R
E
R



211
Formal Number Theory
R is called a Rosser sentence for K. Notice what the intuitive meaning of R is 
under the standard interpretation. R asserts that, if R has a proof in K, say 
with Gödel number x2, then ¬R has a proof in K with Gödel number smaller 
than x2. This is a roundabout way for R to claim its own unprovability under 
the assumption of the consistency of K.
Proposition 3.38 (Gödel–Rosser Theorem)
Let K satisfy conditions 1–5. If K is consistent, then R is an undecidable sen-
tence of K.
Proof
Let p be the Gödel number of R. Thus, ⌜R⌝ is p. Let j be the Gödel number 
of ¬R.
	 a.	 Assume ⊢K R. Since ⊢K R ⇒ E(⌜R⌝), biconditional elimination yields 
⊢K E(⌜R⌝), that is
	
⊢K ∀
(
)
(
) ⇒∀
(
)
(
) ⇒∃
(
)
≤
∧
(
)
(
)
(
)
(
)
x
x
p
x
p x
x
x
x
x
x
2
2
3
3
4
4
2
4
3
Pf
Neg
Pf
,
,
,
	
	 Let k be the Gödel number of a proof in K of R. Then Pf(k, p) and, 
therefore, ⊢K Pf
k p
,
(
). Applying rule A4 to E(⌜R⌝), we obtain
	
⊢K Pf
Neg
Pf
k p
x
p x
x
x
k
x
x
,
,
,
(
) ⇒∀
(
)
(
) ⇒∃
(
)
≤
∧
(
)
(
)
(
)
3
3
4
4
4
3
	
	 So, by MP,
	
%
,
,
(
)
∀
(
)
(
) ⇒∃
(
)
≤
∧
(
)
(
)
(
)
⊢K
x
p x
x
x
k
x
x
3
3
4
4
4
3
Neg
Pf
	
	 Since j is the Gödel number of ¬R, we have Neg(p, j), and, 
therefore, ⊢K Neg p j,
(
). Applying rule A4 to (%), we obtain 
⊢K Neg
Pf
p j
x
x
k
x
j
,
,
(
) ⇒∃
(
)
≤
∧
(
)
(
)
4
4
4
. Hence, by MP, ⊢K ∃
(
)
x4
x
k
x
j
4
4
≤
∧
(
)
(
)
Pf
,
, which is an abbreviation for
	
#
,
( )
¬ ∀
(
)¬
≤
∧
(
)
(
)
⊢K
x
x
k
x
j
4
4
4
Pf
	
	 Since ⊢K R, the consistency of K implies not-⊢K ¬R. Hence, Pf(n, j) is 
false for all natural numbers n. Therefore, ⊢K ¬
(
)
Pf
n j,
 for all natural 



212
Introduction to Mathematical Logic
numbers n. Since K is a theory with equality, ⊢K x
n
x
j
4
4
=
⇒¬
(
)
Pf
,
 
for all natural numbers n. By condition 4,
	
( )
≤
⇒
=
∨
=
∨… ∨
=
⊢K x
k
x
x
x
k
4
4
4
4
0
1
	
	 But
	
 
( )
=
⇒¬
(
)
=
…
⊢K
for
x
n
x
j
n
k
4
4
0 1
Pf
,
, ,
,
	
	 So, by a suitable tautology, ( )  and  
( )  yield ⊢K x
k
x
j
4
4
≤
⇒¬
(
)
Pf
,
 
and then, by another tautology, ⊢K ¬
≤
∧
(
)
(
)
x
k
x
j
4
4
Pf
,
. By Gen, 
⊢K ∀
(
)¬
≤
∧
(
)
(
)
x
x
k
x
j
4
4
4
Pf
,
. This, together with (#), contradicts 
the consistency of K.
	
b.	 Assume ⊢K ¬R. Let m be the Gödel number of a proof of ¬R   in K. So, 
Pf(m, j) is true and, therefore, ⊢K Pf
m
j
,
(
). Hence, by an application of rule 
E4 and the deduction theorem, ⊢K m
x
x
x
x
x
j
≤
⇒∃
(
)
≤
∧
(
)
(
)
2
4
4
2
4
Pf
,
. 
By consistency of K, not-⊢K R  and, therefore, Pf(n, p) is false for all 
natural numbers n. Hence, ⊢K ¬
(
)
Pf
n p
,
 for all natural numbers 
n. By condition 4, ⊢K x
m
x
x
x
m
2
2
2
2
0
1
≤
⇒
=
∨
=
∨… ∨
=
. Hence, 
⊢K x
m
x
p
2
2
≤
⇒¬
(
)
Pf
,
. Consider the following derivation.
	
1.	 Pf
x
p
2,
(
) 	
Hyp
	
2.	
Neg p x
,
3
(
) 	
Hyp
	
3.	
x
m
m
x
2
2
≤
∨
≤
	
Condition 5
	
4.
	
m
x
x
x
x
x
j
≤
⇒∃
(
)
≤
∧
(
)
(
)
2
4
4
2
4
Pf
,
	
Proved above
	
5.	 x
m
x
p
2
2
≤
⇒¬
(
)
Pf
,
	
Proved above
	
6.
	
¬
(
)∨∃
(
)
≤
∧
(
)
(
)
Pf
Pf
x
p
x
x
x
x
j
2
4
4
2
4
,
,
	
3–5, tautology
	
7.
	
∃
(
)
≤
∧
(
)
(
)
x
x
x
x
j
4
4
2
4
Pf
,
	
1, 6, disjunction rule
	
8.	
Neg p j,
(
) 	
Proved in part (a)
	
9.	
∃
(
)
(
)
1
3
3
x
p x
Neg
,
	
Neg represents Neg
	
10.	 x
j
3 =
	
2, 8, 9, properties of =
	
11.	
∃
(
)
≤
∧
(
)
(
)
x
x
x
x
x
4
4
2
4
3
Pf
,
	
7, 10, substitutivity of =
	
12.	 Pf
Neg
x
p
p x
x
2
3
4
,
,
,
(
)
(
)
∃
(
)
⊢K
	
1–11
	
	
x
x
x
x
4
2
4
3
≤
∧
(
)
(
)
Pf
,



213
Formal Number Theory
	
13.	 P f
Neg
(
, )
( ,
)
(
)
x
p
p x
x
2
3
4
⊢K
⇒∃
	
1–12, Corollary 2.6
	
	
(
(
,
))
x
x
x
x
4
2
4
3
≤
∧P f
	
14.	 Pf
Neg
x
p
x
p x
2
3
3
,
(
( ,
)
(
)
∀
(
)
⊢K
	
13, Gen
	
	
⇒∃
≤
∧
(
)(
)
(
,
))
x
x
x
x
x
4
4
2
4
3
P f
	
15.	 ⊢K P f
Neg
(
, )
(
)(
( ,
)
x
p
x
p x
2
3
3
⇒∀
	
1–14, Corollary 2.6
	
	
⇒∃
≤
∧
(
)(
(
,
)))
x
x
x
x
x
4
4
2
4
3
P f
	
16.	 ⊢K (
)(
(
, )
(
)(
( ,
)
∀
⇒∀
x
x
p
x
p x
2
2
3
3
Pf
Neg
	
15, Gen
	
	
 ⇒ (∃x4)(x4 ≤ x2 ∧ P F   (x4, x3))))
	
17.	 ⊢K R	
((*), 
16, 
biconditional 
elimination)
	
	
Thus, ⊢K R and ⊢K ¬R, contradicting the consistency of K.
The Gödel and Rosser sentences for the theory S are undecidable sentences 
of S. They have a certain intuitive metamathematical meaning; for exam-
ple, a Gödel sentence G asserts that G is unprovable in S. Until recently, no 
undecidable sentences of S were known that had intrinsic mathematical 
interest. However, in 1977, a mathematically significant sentence of combi-
natorics, related to the so-called finite Ramsey theorem, was shown to be 
undecidable in S (see Kirby and Paris, 1977; Paris and Harrington, 1977; and 
Paris, 1978).
Definition
A theory K is said to be recursively axiomatizable if there is a theory K* having 
the same theorems as K such that K* has a recursive axiom set.
Corollary 3.39
Let K be a theory in the language LA. If K is a consistent, recursively axiomat-
izable extension of RR, then K has an undecidable sentence.
Proof
Let K* be a theory having the same theorems as K and such that K* has a recur-
sive axiom set. Conditions 1–5 of Proposition 3.38 hold for K*. Hence, a Rosser 
sentence for K* is undecidable in K* and, therefore, also undecidable in K.
An effectively decidable set of objects is a set for which there is a mechanical 
procedure that determines, for any given object, whether or not that object 



214
Introduction to Mathematical Logic
belongs to the set. By a mechanical procedure we mean a procedure that is 
carried out automatically without any need for originality or ingenuity in 
its application. On the other hand, a set A of natural numbers is said to be 
recursive if the property x ∈ A is recursive.* The reader should be convinced 
after Chapter 5 that the precise notion of recursive set corresponds to the intuitive 
idea of an effectively decidable set of natural numbers. This hypothesis is known 
as Church’s thesis.
Remember that a theory is said to be axiomatic if the set of its axioms 
is effectively decidable. Clearly, the set of axioms is effectively decidable 
if and only if the set of Gödel numbers of axioms is effectively decidable 
(since we can pass effectively from a wf to its Gödel number and, con-
versely, from the Gödel number to the wf). Hence, if we accept Church’s 
thesis, to say that K has a recursive axiom set is equivalent to saying that K 
is an axiomatic theory, and, therefore, Corollary 3.39 shows RR is essentially 
incomplete, that is, that every consistent axiomatic extension of RR has an 
undecidable sentence. This result is very disturbing; it tells us that there 
is no complete axiomatization of arithmetic, that is, there is no way to set 
up an axiom system on the basis of which we can decide all problems of 
number theory.
Exercises
3.46	 Church’s thesis is usually taken in the form that a number-theoretic func-
tion is effectively computable if and only if it is recursive. Prove that this is 
equivalent to the form of Church’s thesis given above.
3.47	 Let K be a true theory that satisfies the hypotheses of the Gödel–Rosser 
theorem. Determine whether a Rosser sentence R for K is true for the 
standard interpretation.
3.48	 (Church, 1936b) Let Tr be the set of Gödel numbers of all wfs in the lan-
guage LA that are true for the standard interpretation. Prove that Tr is 
not recursive. (Hence, under the assumption of Church’s thesis, there is 
no effective procedure for determining the truth or falsity of arbitrary 
sentences of arithmetic.)
3.49	 Prove that there is no recursively axiomatizable theory that has Tr as 
the set of Gödel numbers of its theorems.
3.50	 Let K be a theory with equality in the language LA that satisfies condi-
tions 4 and 5 on page 210. If every recursive relation is expressible in K, 
prove that every recursive function is representable in K.
*	 To say that x ∈ A is recursive means that the characteristic function CA is a recursive function, 
where CA(x) = 0 if x ∈ A and CA(x) = 1 if x ∉ A (see page 180).



215
Formal Number Theory
Gödel’s Second Theorem
Let K be an extension of S in the language LA such that K has a recursive 
axiom set. Let Con K be the following closed wf of K:
	
∀
(
) ∀
(
) ∀
(
) ∀
(
)¬
(
) ∧
(
) ∧
(
)
(
)
x
x
x
x
x x
x
x
x
x
1
2
3
4
1
3
2
4
3
4
Pf
Pf
Neg
,
,
,
For the standard interpretation, Con K asserts that there are no proofs in K of a 
wf and its negation, that is, that K is consistent.
Consider the following sentence:
	
G
( )
⇒
Con
G
K
where G is a Gödel sentence for K. Remember that G asserts that G is unprov-
able in K. Hence, (G) states that, if K is consistent, then G is not provable in 
K. But that is just the first half of Gödel’s incompleteness theorem. The meta-
mathematical reasoning used in the proof of that theorem can be expressed 
and carried through within K itself, so that one obtains a proof in K of (G) 
(see Hilbert and Bernays, 1939, pp. 285–328; Feferman, 1960). Thus, ⊢K Con K ⇒ G. 
But, by Gödel’s incompleteness theorem, if K is consistent, G is not provable 
in K. Hence, if K is consistent, Con K is not provable in K.
This is Gödel’s second theorem (1931). One can paraphrase it by stating that, 
if K is consistent, then the consistency of K cannot be proved within K, or, 
equivalently, a consistency proof of K must use ideas and methods that go 
beyond those available in K. Consistency proofs for S have been given by 
Gentzen (1936, 1938) and Schütte (1951), and these proofs do, in fact, employ 
notions and methods (for example, a portion of the theory of denumerable 
ordinal numbers) that apparently are not formalizable in S.
Gödel’s second theorem is sometimes stated in the form that, if a “sufficiently 
strong” theory K is consistent, then the consistency of K cannot be proved 
within K. Aside from the vagueness of the “sufficiently strong” (which can be 
made precise without much difficulty), the way in which the consistency of 
K is formulated is crucial. Feferman (1960, Cor. 5.10) has shown that there is a 
way of formalizing the consistency of S—say, Con S*—such that ⊢S Con S*. A pre-
cise formulation of Gödel’s second theorem may be found in Feferman (1960). 
(See Jeroslow 1971, 1972, 1973) for further clarification and development.)
In their proof of Gödel’s second theorem, Hilbert and Bernays (1939) based 
their work on three so-called derivability conditions. For the sake of definite-
ness, we shall limit ourselves to the theory S, although everything we say also 
holds for recursively axiomatizable extensions of S. To formulate the Hilbert–
Bernays results, let Bew(x1) stand for (∃x2)P   f (x2, x1). Thus, under the standard 
interpretation, Bew(x1) means that there is a proof in S of the wf with Gödel 
number x1; that is, the wf with Gödel number x1 is provable in S.* Notice that a 
Gödel sentence G for S satisfies the fixed-point condition: ⊢S G ⇔ ¬Bew(⌜G⌝).
*	 Bew” consists of the first three letters of the German word beweisbar, which means “provable.”



216
Introduction to Mathematical Logic
The Hilbert–Bernays Derivability Conditions*
	
HB
If
then
S
S
1
(
)
(
)
⊢
⊢
⌜⌝
C
Bew
C
,
	
HB
S
2
(
)
⇒
(
) ⇒
(
) ⇒
(
)
(
)
⊢
⌜
⌝
⌜⌝
⌜⌝
Bew
C
D
Bew
C
Bew
D
	
HB
S
3
(
)
(
) ⇒
(
)
(
)
⊢
⌜⌝
⌜
⌜⌝⌝
Bew
C
Bew
Bew
C
Here, C and D are arbitrary closed wfs of S. (HB1) is straightforward and 
(HB2) is an easy consequence of properties of P  f. However, (HB3) requires 
a careful and difficult proof. (A clear treatment may also be found in Boolos 
(1993, Chapter 2), and in Shoenfield (1967, pp. 211–213).)
A Gödel sentence G for S asserts its own unprovability in S: ⊢S G ⇔ ¬Bew(⌜G⌝). 
We also can apply the fixed-point theorem to obtain a sentence H  such that 
⊢S H ⇔ Bew(⌜H⌝). H is called a Henkin sentence for S. H   asserts its own provability 
in S. On intuitive grounds, it is not clear whether H  is true for the standard 
interpretation, nor is it easy to determine whether H   is provable, disprovable 
or undecidable in S. The problem was solved by Löb (1955) on the basis of 
Proposition 3.40 below. First, however, let us introduce the following conve-
nient abbreviation.
Notation
Let □C stand for Bew(⌜C⌝), where C  is any wf. Then the Hilbert–Bernays deriv-
ability conditions become
	
HB
If
then
S
S
1
(
)
⊢
⊢
C
C
,

	
HB
S
2
(
)
⇒
(
) ⇒
⇒
(
)
⊢


C
D
C
D
	
HB
S
3
(
)
⇒
⊢

C
C
The Gödel sentence G and the Henkin sentence H satisfy the equivalences 
⊢S G ⇔ ¬ □ G and ⊢S H ⇔ □ H.
Proposition 3.40 (Löb’s Theorem)
Let C be a sentence of S. If ⊢S □ C ⇒ C, then ⊢S C.
*	 These three conditions are simplifications by Löb (1955) of the original Hilbert–Bernays 
conditions.



217
Formal Number Theory
Proof
Apply the fixed-point theorem to the wf Bew(x1) ⇒ C to obtain a sentence L 
such that ⊢S L ⇔ (Bew(⌜L⌝) ⇒ C). Thus, ⊢S L ⇔ (□L ⇒ C). Then we have the fol-
lowing derivation of C.
	 1.	 ⊢S L ⇔ (□L ⇒ C )	
Obtained above
	 2.	 ⊢S L ⇒ (□L ⇒ C )	
1, biconditional
	
	 	
elimination
	 3.	 ⊢S □ (L ⇒ (□L ⇒ C ))	
2, (HB1)
	 4.	 ⊢S □L ⇒ □ (□L ⇒ C )	
3, (HB2), MP
	 5.	 ⊢S □ (□L ⇒ C) ⇒ (□□L ⇒ □ C )	
(HB2)
	 6.	 ⊢S □L ⇒ (□□L ⇒ □ C )	
4, 5 tautology
	
7.	 ⊢S □L ⇒ □□L	
(HB3)
	 8.	 ⊢S □L ⇒ □ C	
6, 7, tautology
	 9.	 ⊢S □ C ⇒ C	
Hypothesis of the theorem
	 10.	 ⊢S □L ⇒ C	
8, 9, tautology
	 11.	 ⊢S L	
1, 10, biconditional
	
	 	
elimination
	 12.	 ⊢S □L	
11, (HB1)
	 13.	 ⊢S C	
10, 12, MP
Corollary 3.41
Let H  be a Henkin sentence for S. Then ⊢S H  and H  is true for the standard 
interpretation.
Proof
⊢S H ⇔ □ H. By biconditional elimination, ⊢S □ H ⇒ H. So, by Löb’s theorem, 
⊢S H. Since H asserts that H  is provable in S, H  is true
Löb’s theorem also enables us to give a proof of Gödel’s second theorem 
for S.
Proposition 3.42 (Gödel’s Second Theorem)
If S is consistent, then not-⊢S ConS.
Proof
Assume S consistent. Since ⊢S 0
1
≠, the consistency of S implies not-⊢S 0
1
= . By 
Löb’s theorem, not-⊢S 0
1
0
1
=
(
) ⇒
= . Hence, by the tautology ¬A ⇒ (A ⇒ B), 
we have:
	
*( )
¬
=
(
)
not- S⊢
 0
1



218
Introduction to Mathematical Logic
But, since ⊢S 0
1
≠
, (HB1) yields ⊢S 0
1
≠
(
). Then it is easy to show that 
⊢S
S
Con ⇒¬
=
(
)
 0
1 . So, by (*), not-⊢S
S
Con .
Boolos (1993) gives an elegant and extensive study of the fixed-point theo-
rem and Löb’s theorem in the context of an axiomatic treatment of provabil-
ity predicates. Such an axiomatic approach was first proposed and developed 
by Magari (1975).
Exercises
3.51	 Prove (HB1) and (HB2).
3.52	 Give the details of the proof of ⊢
⌜
⌝
S
S
Con
Bew
⇒¬
=
(
)
0
1
, which was used 
in the proof of Proposition 3.42.
3.53	 If G is a Gödel sentence of S, prove ⊢
⌜
⌝
S G
Bew
⇔¬
=
(
)
0
1
. (Hence, any 
two Gödel sentences for S are provably equivalent. This is an instance 
of a more general phenomenon of equivalence of fixed-point sentences, 
first noticed and verified independently by Bernardi (1975, 1976), 
De Jongh and Sambin (1976). See Smoryński (1979, 1982).
3.54	 In each of the following cases, apply the fixed-point theorem for S 
to obtain a sentence of the indicated kind; determine whether that 
sentence is provable in S, disprovable in S, or undecidable in S; 
and determine the truth or falsity of the sentence for the standard 
interpretation.
	
a.	 A sentence C that asserts its own decidability in S (that is, that ⊢S C 
or ⊢S ¬C).
	
b.	 A sentence that asserts its own undecidability in S.
	
c.	 A sentence C asserting that not-⊢S ¬C.
	
d.	 A sentence C asserting that ⊢S ¬C.
3.6  Recursive Undecidability: Church’s Theorem
If K is a theory, let TK be the set of Gödel numbers of theorems of K.
Definitions
K is said to be recursively decidable if TK is a recursive set (that is, the property 
x ∈ TK is recursive). K is said to be recursively undecidable if TK is not recursive. 



219
Formal Number Theory
K is said to be essentially recursively undecidable if K and all consistent exten-
sions of K are recursively undecidable.
If we accept Church’s thesis, then recursive undecidability is equivalent to 
effective undecidability, that is, nonexistence of a mechanical decision pro-
cedure for theoremhood. The nonexistence of such a mechanical procedure 
means that ingenuity is required for determining whether arbitrary wfs are 
theorems.
Exercise
3.55	 Prove that an inconsistent theory having a recursive vocabulary is 
recursively decidable.
Proposition 3.43
Let K be a consistent theory with equality in the language LA in which 
the diagonal function D is representable. Then the property x ∈ TK is not 
expressible in K.
Proof
Assume x ∈ TK is expressible in K by a wf T  (x1). Thus
	
a.	If n
T
n
∈
( )
K
K
,⊢T
.
	
b.	If n
T
n
∉
K
K
,⊢¬
( )
T
.
	
	 By the diagonalization lemma applied to ¬T  (x1), there is a sentence C 
such that ⊢K C ⇔ ¬T  (⌜C⌝). Let q be the Gödel number of C. So
	
c.	⊢K C
T
⇔¬
( )
q .
Case 1: ⊢K C. Then q ∈ TK. By (a), ⊢K T
q( ). But, from ⊢K C and (c), by bicon-
ditional elimination, ⊢K ¬
( )
T
q . Hence K is inconsistent, contradicting our 
hypothesis.
Case 2: not-⊢K C. So, q ∉ TK. By (b), ⊢K ¬
( )
T
q . Hence, by (c) and biconditional 
elimination, ⊢K C.
Thus, in either case a contradiction is reached.
Definition
A set B of natural numbers is said to be arithmetical if there is a wf B (x) in the 
language LA, with one free variable x, such that, for every natural number n, 
n ∈ B if and only if B n
( ) is true for the standard interpretation.



220
Introduction to Mathematical Logic
Corollary 3.44 [Tarski’s Theorem (1936)]
Let Tr be the set of Gödel numbers of wfs of S that are true for the standard 
interpretation. Then Tr is not arithmetical.
Proof
Let N  be the extension of S that has as proper axioms all those wfs that 
are true for the standard interpretation. Since every theorem of N  must be 
true for the standard interpretation, the theorems of N  are identical with 
the axioms of N.  Hence, TN = Tr. Thus, for any closed wf B, B  holds for the 
standard interpretation if and only if ⊢N B. It follows that a set B is arithmeti-
cal if and only if the property x ∈ B is expressible in N.  We may assume that 
N  is consistent because it has the standard interpretation as a model. Since 
every recursive function is representable in S, every recursive function is 
representable in N   and, therefore, D is representable in N.  By Proposition 
3.43, x ∈ Tr is not expressible in N.  Hence, Tr is not arithmetical. (This result 
can be roughly paraphrased by saying that the notion of arithmetical truth is 
not arithmetically definable.)
Proposition 3.45
Let K be a consistent theory with equality in the language LA in which all 
recursive functions are representable. Assume also that ⊢K 0
1
≠. Then K is 
recursively undecidable.
Proof
D is primitive recursive and, therefore, representable in K. By Proposition 
3.43, the property x ∈ TK is not expressible in K. By Proposition 3.13, the char-
acteristic function CTK is not representable in K. Hence, CTK is not a recursive 
function. Therefore, TK is not a recursive set and so, by definition, K is recur-
sively undecidable.
Corollary 3.46
RR is essentially recursively undecidable.
Proof
RR and all consistent extensions of RR satisfy the conditions on K in 
Proposition 3.45 and, therefore, are recursively undecidable. (We take for 
granted that RR is consistent because it has the standard interpretation as 



221
Formal Number Theory
a model. More constructive consistency proofs can be given along the same 
lines as the proofs by Beth (1959, § 84) or Kleene (1952, § 79).)
We shall now show how this result can be used to give another derivation 
of the Gödel-Rosser theorem.
Proposition 3.47
Let K be a theory with a recursive vocabulary. If K is recursively axiomatiz-
able and recursively undecidable, then K is incomplete (i.e., K has an unde-
cidable sentence).
Proof
By the recursive axiomatizability of K, there is a theory J with a recursive 
axiom set that has the same theorems as K. Since K and J have the same theo-
rems, TK = TJ and, therefore, J is recursively undecidable, and K is incomplete 
if and only if J is incomplete. So, it suffices to prove J incomplete. Notice that, 
since K and J have the same theorems, J and K must have the same individual 
constants, function letters, and predicate letters (because all such symbols 
occur in logical axioms). Thus, the hypotheses of Propositions 3.26 and 3.28 
hold for J. Moreover, J is consistent, since an inconsistent theory with a recur-
sive vocabulary is recursively decidable.
Assume J is complete. Remember that, if x is the Gödel number of a wf, 
Clos(x) is the Gödel number of the closure of that wf. By Proposition 3.26 (16), 
Clos is a recursive function. Define:
	
H
Fml
Pf
Clos
Pf
Neg Clos
Fml
( )
[(
( )
(
( ,
( ))
( ,
(
( )))))
(
x
y
x
y
x
y
x
x
=
∧
∨
∨¬
µ
)]
Notice that, if x is not the Gödel number of a wf, H(x) = 0. If x is the Gödel 
number of a wf B, the closure of B   is a closed wf and, by the completeness of 
J, there is a proof in J of either the closure of B or its negation. Hence, H(x) is 
obtained by a legitimate application of the restricted μ-operator and, therefore, 
H is a recursive function. Recall that a wf is provable if and only if its closure 
is provable. So, x ∈ TJ if and only if Pf(H(x), Clos(x)). But Pf(H(x), Clos(x)) is 
recursive. Thus, TJ is recursive, contradicting the recursive undecidability of J.
The intuitive idea behind this proof is the following. Given any wf B, we 
form its closure C  and start listing all the theorems in J. (Since PrAx is recur-
sive, Church’s Thesis tells us that J is an axiomatic theory and, therefore, by 
the argument on page 84, we have an effective procedure for generating all 
the theorems.) If J is complete, either C  or ¬C  will eventually appear in the 
list of theorems. If C  appears, B is a theorem. If ¬C  appears, then, by the con-
sistency of J, C  will not appear among the theorems and, therefore, B  is not 
a theorem. Thus, we have a decision procedure for theoremhood and, again 
by Church’s thesis, J would be recursively decidable.



222
Introduction to Mathematical Logic
Corollary 3.48 (Gödel–Rosser Theorem)
Any consistent recursively axiomatizable extension of RR has undecidable 
sentences.
Proof
This is an immediate consequence of Corollary 3.46 and Proposition 3.47.
Exercises
3.56	 Prove that a recursively decidable theory must be recursively axiomatizable.
3.57	 Let K be any recursively axiomatizable true theory with equality. 
(So, TK  ⊆ Tr.) Prove that K has an undecidable sentence. [Hint: Use 
Proposition 3.47 and Exercise 3.48.]
3.58	 Two sets A and B of natural numbers are said to be recursively inseparable 
if there is no recursive set C such that A ⊆ C and B
C
⊆
. (C is the com-
plement ω −C.) Let K be any consistent theory with equality in the lan-
guage LA in which all recursive functions are representable and such that 
⊢K 0
1
≠
. Let RefK be the set of Gödel numbers of refutable wfs of K, that 
is, {x|Neg(x) ∈ TK}. Prove that TK and RefK are recursively inseparable.
Definitions
Let K1 and K2 be two theories in the same language.
	
a.	K2 is called a finite extension of K1 if and only if there is a set A of wfs 
and a finite set B of wfs such that (1) the theorems of K1 are precisely 
the wfs derivable from A; and (2) the theorems of K2 are precisely the 
wfs derivable from A ∪ B.
	
b.	Let K1 ∪ K2 denote the theory whose set of axioms is the union of the 
set of axioms of K1 and the set of axioms of K2. We say that K1 and K2 
are compatible if K1 ∪ K2 is consistent.
Proposition 3.49
Let K1 and K2 be two theories in the same language. If K2 is a finite extension 
of K1 and if K2 is recursively undecidable, then K1 is recursively undecidable.
Proof
Let A be a set of axioms of K1 and A ∪ {B1, …, Bn} a set of axioms for K2. We 
may assume that B1, …, Bn are closed wfs. Then, by Corollary 2.7, it is easy to 



223
Formal Number Theory
see that a wf C  is provable in K2 if and only if (B1 ∧ … ∧ Bn) ⇒ C   is provable 
in K1. Let c be a Gödel number of (B1 ∧ … ∧ Bn). Then b is a Gödel number of 
a theorem of K2 when and only when 23 * c * 211 * b * 25 is a Gödel number of a 
theorem of K1; that is, b is in TK2 if and only if 23 * c * 211 * b * 25 is in TK1. Hence, 
if TK1 were recursive, TK2 would also be recursive, contradicting the recursive 
undecidability of K2.
Proposition 3.50
Let K be a theory in the language LA. If K is compatible with RR, then K is 
recursively undecidable.
Proof
Since K is comptatible with RR, the theory K ∪ RR is a consistent extension 
of RR. Therefore, by Corollary 3.46, K ∪ RR is recursively undecidable. Since 
RR has a finite number of axioms, K ∪ RR is a finite extension of K. Hence, by 
Proposition 3.49, K is recursively undecidable.
Corollary 3.51
Every true theory K is recursively undecidable.
Proof
K ∪ RR has the standard interpretation as a model and is, therefore, consis-
tent. Thus, K is compatible with RR. Now apply Proposition 3.50.
Corollary 3.52
Let PS be the predicate calculus in the language LA. Then PS is recursively 
undecidable.
Proof
PS ∪ RR = RR. Hence, PS is compatible with RR and, therefore, by Proposition 
3.50, recursively undecidable.
By PF we mean the full first-order predicate calculus containing all predi-
cate letters, function letters and individual constants. Let PP be the pure 
first-order predicate calculus, containing all predicate letters but no function 
letters or individual constants.



224
Introduction to Mathematical Logic
Lemma 3.53
There is a recursive function h such that, for any wf B of PF having Gödel 
number u, there is a wf B ′ of PP having Gödel number h(u) such that B is 
provable in PF if and only if B ′ is provable in PP.
Proof
Let Φ be a wf of PF. First we will eliminate any individual constants from Φ. 
Assume b is an individual constant in Φ. Let Am
1 be the first new symbol of 
that form. Intuitively we imagine that Am
1 represents a property that holds 
only for b. Let Φ*(z) be obtained from Φ by replacing all occurrences of b by z. 
We will associate with Φ a new wf Ψ, where Ψ has the form
	 ((
)
( ))
(
)(
)
( )
( )
(
)
( )
∃
∧∀
∀
=
⇒
⇔


(
)
{
} ⇒∀
1
1
1
1
1
z A
z
x
y
x
y
A
x
A
y
z
A
z
m
m
m
m
⇒
∗


Φ ( )z
Then Ψ is logically valid if and only if Φ is logically valid. We apply the 
same procedure to Ψ and so on until we obtain a wf Φ$ that contains no 
individual constants and is logically valid if and only if Φ is logically 
valid. Now we apply to Φ$ a similar, but somewhat more complicated, pro-
cedure to obtain a wf Θ that contains no function letters and is logically 
valid if and only if Φ is logically valid. Consider the first function letter fj
n 
in Φ$. Take the first new symbol Ar
n+1 of that form. Intuitively we imagine 
that Ar
n+1 holds for (x1, …, xn+1) if and only if f
x
x
x
j
n
n
n
(
,
,
)
.
1
1
…
=
+  We wish 
to construct a wf that plays a role similar to the role played by Ψ above. 
However, the situation is more complex here because there may be iterated 
applications of fj
n in Φ$. We shall take a relatively easy case where fj
n has 
only simple (noniterated) occurrences, say, f
s
s
j
n
n
( ,
,
)
1 …
 and f
t
t
j
n
n
( ,
,
).
1 …
 
Let Φ$* be obtained from Φ$ by replacing the occurrences of f
s
s
j
n
n
( ,
,
)
1 …
 
by v and the occurrences of f
t
t
j
n
n
( ,
,
)
1 …
 by w. In the wf Θ analogous to 
Ψ, use as conjuncts in the antecedent (
)
(
)(
)
(
,
,
, )
∀
… ∀
∃
…
+
x
x
z A
x
x
z
n
r
n
n
1
1
1
1
 
and the n + 1 equality substitution axioms for Ar
n+1, and, as the consequent 
(
)(
)(
(
,
,
, )
( ,
,
,
)
)
$
∀
∀
…
∧
…
⇒
+
+
v
w A
S
S
v
A
t
t
w
r
n
n
r
n
n
1
1
1
1
Φ * . We leave it to the 
reader to construct Θ when there are nonsimple occurrences of fj
n. If u is 
the Gödel number of the original wf Φ, let h(u) be the Gödel number of the 
result Θ. When u is not the Gödel number of a wf of PF, define h(u) to be 0. 
Clearly, h is effectively computable because we have described an effective 
procedure for obtaining Θ from Φ. Therefore, by Church’s thesis, h is 
recursive. Alternatively, an extremely diligent reader could avoid the use 
of Church’s thesis by “arithmetizing” all the steps described above in the 
computation of h.



225
Formal Number Theory
Proposition 3.54 (Church’s Theorem (1936a))
PF and PP are recursively undecidable.
Proof
	 a.	 By Gödel’s completeness theorem, a wf B of PS is provable in PS if 
and only if B is logically valid, and B is provable in PF if and only 
if B is logically valid. Hence, ⊢PS B  if and only if ⊢PF B. However, 
the set FmlPS of Gödel numbers of wfs of PS is recursive. Then 
T
T
P
PF
P
S
S
Fml
=
∩
, where TPS and TPF are, respectively, the sets of 
Gödel numbers of the theorems of PS and PF. If TPF were recursive, 
TPS would be recursive, contradicting Corollary 3.52. Therefore, PF is 
recursively undecidable.
	 b.	 By Lemma 3.53, u is in TPF if and only if h(u) is in TPP. Since h is recur-
sive, the recursiveness of TPP would imply the recursiveness of TPF, 
contradicting (a). Thus, TPP is not recursive; that is, PP is recursively 
undecidable.
If we accept Church’s thesis, then “recursively undecidable” can be replaced 
everywhere by “effectively undecidable.” In particular, Proposition 3.54 
states that there is no decision procedure for recognizing theoremhood, 
either for the pure predicate calculus PP or the full predicate calculus PF. By 
Gödel’s completeness theorem, this implies that there is no effective method for 
determining whether any given wf is logically valid.
Exercises
3.59D	 a.	 By a wf of the pure monadic predicate calculus (PMP) we mean 
a wf of the pure predicate calculus that does not contain predi-
cate letters of more than one argument. Show that, in contrast to 
Church’s theorem, there is an effective procedure for determining 
whether a wf of PMP is logically valid. [Hint: Let B1, B2, …, Bk be the 
distinct predicate letters in a wf B. Then B is logically valid if and 
only if B is true for every interpretation with at most 2k elements. 
(In fact, assume B is true for every interpretation with at most 2k 
elements, and let M be any interpretation. For any elements b and c 
of the domain D of M, call b and c equivalent if the truth values of 
B1(b), B2(b), …, Bk(b) in M are, respectively, the same as those of B1(c), 
B2(c), …, Bk(c). This defines an equivalence relation in D, and the 
corresponding set of equivalence classes has at most 2k members 
and can be made the domain of an interpretation M* by defining 
interpretations of B1, …, Bk, in the obvious way, on the equivalence 
classes. By induction on the length of wfs C that contain no predicate 



226
Introduction to Mathematical Logic
letters other than B1, …, Bk, one can show that C is true for M if and 
only if it is true for M*. Since B is true for M*, it is also true for M. 
Hence, B is true for every interpretation.) Note also that whether B 
is true for every ­interpretation that has at most 2k elements can be 
effectively determined.]*
	
b.	 Prove that a wf B of PMP is logically valid if and only if B is true for 
all finite interpretations. (This contrasts with the situation in the 
pure predicate calculus; see Exercise 2.56 on page 92.)
3.60	 If a theory K* is consistent, if every theorem of an essentially recursively 
undecidable theory K1 is a theorem of K*, and if the property FmlK1( )
y  
is recursive, prove that K* is essentially recursively undecidable.
3.61	 (Tarski et al., 1953, I)
	
a.	 Let K be a theory with equality. If a predicate letter Aj
n, a function 
letter fj
n and an individual constant aj are not symbols of K, then 
by possible definitions of A
f
j
n
j
n
,
, and aj in K we mean, respectively, 
expressions of the form
	
	
i.
	
∀
(
) … ∀
(
)
…
(
) ⇔
…
(
)
(
)
x
x
A
x
x
x
x
n
j
n
n
n
1
1
1
,
,
,
,
B
	
	
ii.
	
∀
(
) … ∀
(
) ∀
(
)
…
(
) =
⇔
…
(
)
(
)
x
x
y
f
x
x
y
x
x
y
n
j
n
n
n
1
1
1
,
,
,
,
,
C
	
	
iii.	 (∀y)(aj = y ⇔ D(y))
	
	
	
where B, C, and D are wfs of K; moreover, in case (ii), 
we must also have ⊢K(∀x1) … (∀xn)(∃1y)C (x1, …, xn, y), 
and, in case (iii), ⊢K(∃1y)D(y). Moreover, add to (ii) the 
requirement of n new equality axioms of the form 
y
z
f
x
x
y x
x
f
x
x
z x
x
j
n
i
i
n
j
n
i
i
n
=
⇒
…
…
=
…
…
−
+
−
+
(
,
, ,
,
,
)
(
,
,
, ,
,
,
).
1
1
1
1
1
1
 
If K is consistent, prove that addition of any possible defini-
tions to K as new axioms (using only one possible definition 
for each symbol and assuming that the set of new logical con-
stants and the set of possible definitions are recursive) yields 
a consistent theory K′, and K′ is recursively undecidable if and 
only if K is.
	
b.	 By a nonlogical constant we mean a predicate letter, function let-
ter or individual constant. Let K1 be a theory with equality that 
has a finite number of nonlogical constants. Then K1 is said to be 
interpretable in a theory with equality K if we can associate with 
*	 The result in this exercise is, in a sense, the best possible. By a theorem of Kalmár (1936), there 
is an effective procedure producing for each wf B of the pure predicate calculus another wf 
B2 of the pure predicate calculus such that B2 contains only one predicate letter, a binary one, 
and such that B is logically valid if and only if B2 is logically valid. (For another proof, see 
Church, 1956, § 47.) Hence, by Church’s theorem, there is no decision procedure for logical 
validity of wfs that contain only binary predicate letters. (For another proof, see Exercise 4.68 
on page 277.)



227
Formal Number Theory
each nonlogical constant of K1 that is not a nonlogical constant of 
K a possible definition in K such that, if K* is the theory obtained 
from K by adding these possible definitions as axioms, then every 
axiom (and hence every theorem) of K1 is a theorem of K*. Notice 
that, if K1 is interpretable in K, it is interpretable in every extension 
of K. Prove that, if K1 is interpretable in K and K is consistent, and 
if K1 is essentially recursively undecidable, then K is essentially 
recursively undecidable.
3.62	 Let K be a theory with equality and Aj
1 a monadic predicate let-
ter not in K. Given a closed wf C, let C
Aj
1
(
) (called the relativization of 
C with respect to Aj
1) be the wf obtained from C by replacing every 
subformula (starting from the smallest subformulas) of the form 
(∀x)B (x) by ∀
(
)
( ) ⇒
( )
(
)
x
A
x
x
j
1
B
. Let the proper axioms of a new 
theory with equality K
Aj
1
 be: (i) all wfs C
Aj
1
(
), where C is the clo-
sure of any proper axiom of K; (ii) (
)
( )
∃x A x
j
1
; (iii) A a
j
m
1(
) for each 
individual constant am of K; (iv) x
x
A x
A x
j
j
1
2
1
1
1
2
=
⇒
⇒
(
(
)
(
)); and 
(v)  A x
A x
A
f
x
x
j
j
n
j
k
n
n
1
1
1
1
1
(
)
(
)
(
(
,
,
))
∧… ∧
⇒
…
 for any function letter fk
n 
of K. Prove the following.
	
a.	 As proper axioms of K
Aj
1
 we could have taken all wfs C
Aj
1
(
), where C 
is the closure of any theorem of K.
	
b.	 K
Aj
1
 is interpretable in K.
	
c.	 K
Aj
1
 is consistent if and only if K is consistent.
	
d.	 K
Aj
1
 is essentially recursively undecidable if and only if K is (Tarski 
et al., 1953, pp. 27–28).
3.63	 K is said to be relatively interpretable in K′ if there is some predicate 
letter Aj
1 not in K such that K
Aj
1
 is interpretable in K′. If K is relatively 
interpretable in a consistent theory with equality K′ and K is essen-
tially recursively undecidable, prove that K′ is essentially recursively 
undecidable.
3.64	 Call a theory K in which RR is relatively interpretable sufficiently 
strong. Prove that any sufficiently strong consistent theory K is essen-
tially recursively undecidable, and, if K is also recursively axiomatiz-
able, prove that K is incomplete. Roughly speaking, we may say that 
K is sufficiently strong if the notions of natural number, 0, 1, addi-
tion and multiplication are “definable” in K in such a way that the 
axioms of RR (relativized to the “natural numbers” of K) are prov-
able in K. Clearly, any theory adequate for present-day mathematics 
will be sufficiently strong and so, if it is consistent, then it will be 
recursively undecidable and, if it is recursively axiomatizable, then it 
will be incomplete. If we accept Church’s thesis, this implies that any 



228
Introduction to Mathematical Logic
consistent sufficiently strong theory will be effectively undecidable 
and, if it is axiomatic, it will have undecidable sentences. (Similar 
results also hold for higher-order theories; for example, see Gödel, 
1931.) This destroys all hope for a consistent and complete axiomatization of 
mathematics.
3.7  Nonstandard Models
Recall from Section 3.1 that the standard model is the interpretation of the lan-
guage £A of arithmetic in which:
	 a.	 The domain is the set of nonnegative integers
	 b.	 The integer 0 is the interpretation of the symbol 0
	
c.	 The successor operation (addition of 1) is the interpretation of the 
function ′ (that is, of f1
1)
	 d.	 Ordinary addition and multiplication are the interpretations of + 
and ·
	 e.	 The predicate letter = is interpreted by the identity relation
By a nonstandard model of arithmetic we shall mean any normal interpretation 
M of £A that is not isomorphic to the standard model and in which all formu-
las are true that are true in the standard model (that is, M and the standard 
model are elementarily equivalent). Also of interest are nonstandard models of 
S, that is, normal models of S that are not isomorphic to the standard model, 
and much of what we prove about nonstandard models of arithmetic also 
holds for nonstandard models of S. (Of course, all nonstandard models of 
arithmetic would be nonstandard models of S, since all axioms of S are true 
in the standard model.)
There exist denumerable nonstandard models of arithmetic. Proof: 
Remember (page 221) that N   is the theory whose axioms are all wfs true 
for the standard interpretation. Add a constant c to the language of arith-
metic and consider the theory K obtained from N   by adding the axioms 
c
n
≠
 for all numerals n. K is consistent, since any finite set of axioms of 
K has as a model the standard model with a suitable interpretation of  c. 
(If c
n c
n
c
nr
≠
≠
…
≠
1
2
,
,
,
 are the new axioms in the finite set, choose the inter-
pretation of c to be a natural number not in {n1, …, nr}.) By Proposition 2.26, 
K has a finite or denumerable normal model M. M is not finite, since the 
interpretations of the numerals will be distinct. M will be a nonstandard 
model of arithmetic. (If M were isomorphic to the standard model, the inter-
pretation cM of c would correspond under the isomorphism to some natural 
number m and the axiom c
m
≠
 would be false.)



229
Formal Number Theory
Let us see what a nonstandard model of arithmetic M must look like. 
Remember that all wfs true in the standard model are also true in M. So, for 
every x in M, there is no element between x and its successor x′ = x + 1. Thus, 
if z is the interpretation of 0, then z, z′, z″, z′″, …, form an initial segment z < 
z′ < z″ < z′″ <…, of M that is isomorphic to the standard model. Let us call 
these elements the standard elements of M. The other elements of M will be 
greater than the standard elements and will be called nonstandard elements 
of M. Since every nonzero element w of M has an “immediate predecessor” u 
such that w = u′ and u will have an immediate predecessor t, and so on, every 
nonstandard element w will belong to a block Bw={…, t, u, w, w′, w″, …} con-
sisting of nonstandard elements. Bw is isomorphic to a copy of the ordinary 
integers, where w, w′, w″, …, correspond to 0, 1, 2, …, and …, t, u correspond 
to …, −2, −1. More precisely, we can define a binary relation R on the set of 
nonstandard elements by specifying that x R y if and only if there is a stan-
dard element s such that x + s = y or y + s = x. R is an equivalence relation and 
the resulting equivalence classes are the blocks. The blocks inherit an order 
relation from M. If one element of a block B1 is less than an element of a block 
B2, then every element of B1 is less than every element of B2; in that case, we 
specify that B1 < B2. The resulting ordering of the blocks is obviously a total 
order and it is dense and without first or last member. (See Exercise 2.67.) To 
see that there is no last member, note that, if w belongs to a block B, then 2w 
belongs to a larger block. To see that there is no first member, note that, if w 
belongs to a block B, then there exists a non-standard element x such that 
either w = 2x or w = 2x + 1, and, therefore, the block of x is smaller than B. To 
show that the ordering is dense, assume that x belongs to a block B1 and that 
y belongs to a larger block B2. We may assume that x and y are even. (If x is 
not even, we could consider x + 1, and similarly for y.) Then there is a non-
standard element z such that 2z = x + y. We leave it as an exercise to check that 
x < z and z < y and that the block of z is strictly between B1 and B2.
Exercise 3.65
Show that, if < and <2 are dense total orders without first and last element 
and their domains D1 and D2 are denumerable, then there is a “similarity 
mapping” f from D1 onto D2 (that is, for any x and y in D1, x <1 y if and only 
if f(x) <2 f(y)). (Hint: Start with enumerations <a1, a2, …> and <b1, b2, …> of D1 
and D2. Map a1 to b1. Then look at a2. If a2 >1 a1, map a2 to the first unused bj 
such that bj >2 b1 in D2. On the other hand, if a2 <1 a1, map a2 to the first unused 
bj such that bj <2 b1 in D2. Now look at a3, observe its relation to a1 and a2, and 
map a3 to the first unused bk so that the b’s are in the same relation as the a’s. 
Continue to extend the mapping in similar fashion.)
Note that, with respect to its natural ordering, the set of rational num-
bers is a denumerable totally ordered set without first or last element. So, by 
Exercise 3.65, the totally ordered set of blocks of any denumerable nonstan-
dard model of arithmetic looks just like the ordered set of rational numbers. 



230
Introduction to Mathematical Logic
Thus, the model can be pictured in the following way: First come the natural 
numbers 0, 1, 2, … . These are followed by a denumerable collection of blocks, 
where each block looks like the integers in their natural order, and this denu-
merable collection of blocks is ordered just like the rational numbers.
Exercise 3.66
Prove that there is no wf Φ(x) of the language of arithmetic such that, in each 
nonstandard model M of arithmetic, Φ is satisfied by those and only those 
elements of M that are standard. (Hint: Note that Φ(0) and (∀x)(Φ(x) ⇒ Φ(x′)) 
would be true in M, and the principle of mathematical induction holds in M.)
We have proved that there are denumerable nonstandard models of S, as 
well as denumerable nonstandard models of arithmetic. We may assume 
that the domain of any such model M is the set ω of natural numbers. The 
addition and multiplication operations in the model M are binary opera-
tions on ω (and the successor operation is a unary operation on ω). Stanley 
Tennenbaum proved that, in any denumerable nonstandard model of arith-
metic, it is not the case that the addition and multiplication operations are 
both recursive. (See Tennenbaum, 1959.) This was strengthened by Georg 
Kreisel, who proved that addition cannot be recursive, and by Kenneth 
McAloon, who proved that multiplication cannot be recursive, and by 
George Boolos, who proved that addition and multiplication each cannot be 
arithmetical. (See Kaye, 1991; Boolos et al., 2007.)



231
4
Axiomatic Set Theory
