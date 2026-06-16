<!-- Source: Mendelson, E. (2016). Introduction to Mathematical Logic (6th ed). Chapter 2: First-Order Logic and Model Theory (pages 45-152). BibKey: not yet in references.bib -->


45
2
First-Order Logic and Model Theory
2.1  Quantifiers
There are various kinds of logical inference that cannot be justified on the 
basis of the propositional calculus; for example:
	
1.	Any friend of Martin is a friend of John.
	
	 Peter is not John’s friend.
	
	 Hence, Peter is not Martin’s friend.
	
2.	All human beings are rational.
	
	 Some animals are human beings.
	
	 Hence, some animals are rational.
	
3.	The successor of an even integer is odd.
	
	 2 is an even integer.
	
	 Hence, the successor of 2 is odd.
The correctness of these inferences rests not only upon the meanings of the 
truth-functional connectives, but also upon the meaning of such expressions 
as “any,” “all,” and “some,” and other linguistic constructions.
In order to make the structure of complex sentences more transparent, it 
is convenient to introduce special notation to represent frequently occur-
ring expressions. If P(x) asserts that x has the property P, then (∀x)P(x) means 
that property P holds for all x or, in other words, that everything has the 
­property P. On the other hand, (∃x)P(x) means that some x has the property 
P—that is, that there is at least one object having the property P. In (∀x)P(x), 
“(∀x)” is called a universal quantifier; in (∃x)P(x), “(∃x)” is called an existential 
quantifier. The study of quantifiers and related concepts is the principal sub-
ject of this chapter.



46
Introduction to Mathematical Logic
Examples
	
1′. Inference 1 above can be represented symbolically:
	
(
)( ( ,
)
( , ))
( , )
( ,
)
∀
⇒
¬
¬
x F x m
F x j
F p j
F p m
	
	 Here, F(x, y) means that x is a friend of y, while m, j, and p denote 
Martin, John, and Peter, respectively. The horizontal line above 
“¬F(p, m)” stands for “hence” or “therefore.”
	
2′. Inference 2 becomes:
	
(
)(
( )
( ))
(
)( ( )
( ))
(
)( ( )
( ))
∀
⇒
∃
∧
∃
∧
x H x
R x
x A x
H x
x A x
R x
	
	 Here, H, R, and A designate the properties of being human, rational, 
and an animal, respectively.
	
3′. Inference 3 can be symbolized as follows:
	
(
)( ( )
( )
( ( )))
( )
( )
( ( ))
∀
∧
⇒
∧
x I x
E x
D s x
I b
E b
D s b
	
	 Here, I, E, and D designate respectively the properties of being an 
integer, even, and odd; s(x) denotes the successor of x; and b denotes 
the integer 2.
Notice that the validity of these inferences does not depend upon the par-
ticular meanings of F, m, j, p, H, R, A, I, E, D, s, and b.
Just as statement forms were used to indicate logical structure dependent 
upon the logical connectives, so also the form of inferences involving quan-
tifiers, such as inferences 1–3, can be represented abstractly, as in 1′–3′. For 
this purpose, we shall use commas, parentheses, the symbols ¬ and ⇒ of the 



47
First-Order Logic and Model Theory
propositional calculus, the universal quantifier symbol ∀, and the following 
groups of symbols:
Individual variables: x1, x2, …, xn, …
Individual constants: a1, a2, …, an, …
Predicate letters: Ak
n (n and k are any positive integers)
Function letters: fk
n (n and k are any positive integers)
The positive integer n that is a superscript of a predicate letter Ak
n or of a 
function letter fk
n indicates the number of arguments, whereas the subscript 
k is just an indexing number to distinguish different predicate or function 
letters with the same number of arguments.*
In the preceding examples, x plays the role of an individual variable; m, 
j, p, and b play the role of individual constants; F is a binary predicate letter 
(i.e., a predicate letter with two arguments); H, R, A, I, E, and D are monadic 
predicate letters (i.e., predicate letters with one argument); and s is a function 
letter with one argument.
The function letters applied to the variables and individual constants gen-
erate the terms:
	
1.	Variables and individual constants are terms.
	
2.	If fk
n is a function letter and t1, t2, …, tn are terms, then f
t t
t
k
n
n
( ,
,
,
)
1
2 …
 
is a term.
	
3.	An expression is a term only if it can be shown to be a term on the 
basis of conditions 1 and 2.
Terms correspond to what in ordinary languages are nouns and noun 
phrases—for example, “two,” “two plus three,” and “two plus x.”
The predicate letters applied to terms yield the atomic formulas; that is, if Ak
n 
is a predicate letter and t1, t2, …, tn are terms, then A t t
t
k
n
n
( ,
,
,
)
1
2 …
 is an atomic 
formula.
The well-formed formulas (wfs) of quantification theory are defined as follows:
	
1.	Every atomic formula is a wf.
	
2.	If B and C are wfs and y is a variable, then (¬B), (B ⇒ C), and ((∀y)B) 
are wfs.
	
3.	An expression is a wf only if it can be shown to be a wf on the basis 
of conditions 1 and 2.
*	 For example, in arithmetic both addition and multiplication take two arguments. So, we 
would use one function letter, say f1
2, for addition, and a different function letter, say f2
2 for 
multiplication.



48
Introduction to Mathematical Logic
In ((∀y)B), “B” is called the scope of the quantifier “(∀y).” Notice that B need 
not contain the variable y. In that case, we understand ((∀y)B) to mean the 
same thing as B.
The expressions (B ∧ C), (B ∨ C), and (B ⇔ C) are defined as in system L (see 
page 29). It was unnecessary for us to use the symbol ∃ as a primitive symbol 
because we can define existential quantification as follows:
	
((
)
)
( ((
)(
)))
∃
∀
x
x
B
B
stands for
¬
¬
This definition is faithful to the meaning of the quantifiers: B(x) is true for 
some x if and only if it is not the case that B(x) is false for all x.*
2.1.1  Parentheses
The same conventions as made in Chapter 1 (page 11) about the omission of 
parentheses are made here, with the additional convention that quantifiers 
(∀y) and (∃y) rank in strength between ¬, ∧, ∨ and ⇒, ⇔. In other words, 
when we restore parentheses, negations, conjunctions, and disjunctions are 
handled first, then we take care of universal and existential quantifications, 
and then we deal with conditionals and biconditionals. As before, for con-
nectives of the same kind, we proceed from left to right. For consecutive 
negations and quantifications, we proceed from right to left.
Examples
Parentheses are restored in the following steps.
	
1.	(
)
(
)
(
,
)
∀
⇒
x A x
A x
x
1
1
1
1
1
2
2
1
	
	 ((
)
(
))
(
,
)
∀
⇒
x A x
A x
x
1
1
1
1
1
2
2
1
	
	 (((
)
(
))
(
,
))
∀
⇒
x A x
A x
x
1
1
1
1
1
2
2
1
	
2.	(
)
(
)
(
,
)
∀
∨
x A x
A x
x
1
1
1
1
1
2
2
1
	
	 (
)(
(
)
(
,
))
∀
∨
x
A x
A x
x
1
1
1
1
1
2
2
1
	
	 ((
)(
(
))
(
,
)))
∀
∨
x
A x
A x
x
1
1
1
1
1
2
2
1
*	 We could have taken ∃ as primitive and then defined ((∀x)B) as an abbreviation for (¬((∃x)
(¬B))), since B(x) is true for all x if and only if it is not the case that B(x) is false for some x.



49
First-Order Logic and Model Theory
	
3.	(
) (
)
(
,
)
∀
¬ ∃
x
x A x x
1
2
1
2
1
2
	
	 (
) ((
)
(
,
))
∀
¬ ∃
x
x A x x
1
2
1
2
1
2
	
	
(
)( ((
)
(
,
)))
∀
¬ ∃
x
x A x x
1
2
1
2
1
2
	
	 ((
)( ((
)
(
,
))))
∀
¬ ∃
x
x A x x
1
2
1
2
1
2
Exercises
2.1	
Restore parentheses to the following.
	
a.	 (
)
(
)
(
)
∀
∧¬
x A x
A x
1
1
1
1
1
1
2
	
b.	 (
)
(
)
(
)
∀
⇔
x A x
A x
2
1
1
2
1
1
2
	
c.	 (
)(
)
(
,
)
∀
∃
x
x A x x
2
1
1
2
1
2
	
d.	 (
)(
)(
)
(
)
(
)
(
)
∀
∀
∀
⇒
∧¬
x
x
x A x
A x
A x
1
3
4
1
1
1
1
1
2
1
1
1
	
e.	 (
)(
)(
)
(
)
(
) (
)
(
,
)
∃
∀
∃
∨∃
¬ ∀
x
x
x A x
x
x A x
x
1
2
3
1
1
1
2
3
1
2
3
2
	
f.	 (
)
(
)
(
,
,
)
(
)
(
)
∀
¬
⇒
∨∀
x
A x
A x x x
x A x
2
1
1
1
1
3
1
1
2
1
1
1
1
	
g.	 ¬ ∀
⇒∃
⇒
∧
(
)
(
)
(
)
(
)
(
,
)
(
)
x A x
x A x
A x x
A x
1
1
1
1
2
1
1
2
1
2
1
2
1
1
2
2.2	
Eliminate parentheses from the following wfs as far as is possible.
	
a.	 (((
)(
(
)
(
)))
((
)
(
)))
∀
⇒
∨
∃
x
A x
A x
x A x
1
1
1
1
1
1
1
1
1
1
1
	
b.	 (( ((
)(
(
)
(
))))
(
))
¬ ∃
∨
⇔
x
A x
A a
A x
2
1
1
2
1
1
1
1
1
2
	
c.	 (((
)( (
(
))))
(
(
)
(
)))
∀
¬ ¬
⇒
⇒
x
A a
A x
A x
1
1
1
3
1
1
1
1
1
2
An occurrence of a variable x is said to be bound in a wf B if either it is the 
occurrence of x in a quantifier “(∀x)” in B or it lies within the scope of a quan-
tifier “(∀x)” in B. Otherwise, the occurrence is said to be free in B.
Examples
	
1.	A x x
1
2
1
2
(
,
)
	
2.	A x x
x A x
1
2
1
2
1
1
1
1
(
,
)
(
)
(
)
⇒∀
	
3.	(
)(
(
,
)
(
)
(
))
∀
⇒∀
x
A x x
x A x
1
1
2
1
2
1
1
1
1
	
4.	(
)
(
,
)
∃x A x x
1
1
2
1
2
In Example 1, the single occurrence of x1 is free. In Example 2, the occurrence 
of x1 in A x x
1
2
1
2
(
,
) is free, but the second and third occurrences are bound. In 
Example 3, all occurrences of x1 are bound, and in Example 4 both occur-
rences of x1 are bound. (Remember that (
)
(
,
)
∃x A x x
1
1
2
1
2  is an abbreviation of 
¬ ∀
¬
(
)
(
,
)
x
A x x
1
1
2
1
2 .) In all four wfs, every occurrence of x2 is free. Notice that, 



50
Introduction to Mathematical Logic
as in Example 2, a variable may have both free and bound occurrences in the 
same wf. Also observe that an occurrence of a variable may be bound in some 
wf B but free in a subformula of B. For example, the first occurrence of x1 is free 
in the wf of Example 2 but bound in the larger wf of Example 3.
A variable is said to be free (bound) in a wf B if it has a free (bound) occur-
rence in B. Thus, a variable may be both free and bound in the same wf; for 
example, x1 is free and bound in the wf of Example 2.
Exercises
2.3	
Pick out the free and bound occurrences of variables in the following wfs.
	
a.	 (
)(((
)
(
,
))
(
,
))
∀
∀
⇒
x
x A x x
A x
a
3
1
1
2
1
2
1
2
3
1
	
b.	 (
)
(
,
)
(
)
(
,
)
∀
⇒∀
x A x
x
x A x
x
2
1
2
3
2
3
1
2
3
2
	
c.	 ((
)(
)
(
,
,
(
,
)))
(
)
(
,
(
))
∀
∃
∨¬ ∀
x
x A x x
f
x x
x A x
f
x
2
1
1
3
1
2
1
2
1
2
1
1
2
2
1
1
1
2.4	
Indicate the free and bound occurrences of all variables in the wfs of 
Exercises 2.1 and 2.2.
2.5	
Indicate the free and bound variables in the wfs of Exercises 2.1–2.3.
We shall often indicate that some of the variables x
x
i
ik
1,
,
…
 are free vari-
ables in a wf B by writing B as B (
,
,
).
x
x
i
ik
1 …
 This does not mean that B 
contains these variables as free variables, nor does it mean that B does not 
contain other free variables. This notation is convenient because we can then 
agree to write as B(t1, …, tk) the result of substituting in B the terms t1, …, tk 
for all free occurrences (if any) of x
x
i
ik
1,
,
…
, respectively.
If B  is a wf and t is a term, then t is said to be free for xi in B  if no free occurrence 
of xi in B  lies within the scope of any quantifier (∀xj), where xj is a variable in t. 
This concept of t being free for xi in a wf B   (xi) will have certain technical applica-
tions later on. It means that, if t is substituted for all free occurrences (if any) of 
xi in B  (xi), no occurrence of a variable in t becomes a bound occurrence in B  (t).
Examples
	
1.	The term x2 is free for x1 in A x
1
1
1
(
), but x2 is not free for x1 in (
)
(
).
∀x A x
2
1
1
1
	
2.	The term f
x x
1
2
1
3
(
,
) is free for x1 in (
)
(
,
)
(
)
∀
⇒
x A x x
A x
2
1
2
1
2
1
1
1  but is not 
free for x1 in (
)(
)
(
,
)
(
).
∃
∀
⇒
x
x A x x
A x
3
2
1
2
1
2
1
1
1
The following facts are obvious.
	
1.	A term that contains no variables is free for any variable in any wf.
	
2.	A term t is free for any variable in B if none of the variables of t is 
bound in B.
	
3.	xi is free for xi in any wf.
	
4.	Any term is free for xi in B if B contains no free occurrences of xi.



51
First-Order Logic and Model Theory
Exercises
2.6	
Is the term f
x x
1
2
1
2
(
,
) free for x1 in the following wfs?
	
a.	 A x x
x A x
1
2
1
2
2
1
1
2
(
,
)
(
)
(
)
⇒∀
	
b.	 ((
)
(
,
))
(
)
(
,
)
∀
∨∃
x A x
a
x A x x
2
1
2
2
1
2
1
2
1
2
	
c.	 (
)
(
,
)
∀x A x x
1
1
2
1
2
	
d.	 (
)
(
,
)
∀x A x x
2
1
2
1
2
	
e.	 (
)
(
)
(
,
)
∀
⇒
x A x
A x x
2
1
1
2
1
2
1
2
2.7	 Justify facts 1–4 above.
When English sentences are translated into formulas, certain general guide-
lines will be useful:
	
1.	A sentence of the form “All As are Bs” becomes (∀x)(A(x) ⇒ B(x)). For 
example, Every mathematician loves music is translated as (∀x)(M(x) ⇒ 
L(x)), where M(x) means x is a mathematician and L(x) means x loves 
music.
	
2.	A sentence of the form “Some As are Bs” becomes (∃x)(A(x) ∧ B(x)). 
For example, Some New Yorkers are friendly becomes (∃x)(N(x) ∧ F(x)), 
where N(x) means x is a New Yorker and F(x) means x is friendly.
	
3.	A sentence of the form “No As are Bs” becomes (∀x)(A(x) ⇒ ¬B(x)).* 
For example, No philosopher understands politics becomes (∀x)(P(x) ⇒ 
¬U(x)), where P(x) means x is a philosopher and U(x) means x under-
stands politics.
Let us consider a more complicated example: Some people respect everyone. 
This can be translated as (∃x)(P(x) ∧ (∀y)(P(y) ⇒ R(x, y))), where P(x) means x 
is a person and R(x, y) means x respects y.
Notice that, in informal discussions, to make formulas easier to read we 
may use lower-case letters u, v, x, y, z instead of our official notation xi for 
individual variables, capital letters A, B, C,… instead of our official notation 
Ak
n for predicate letters, lower-case letters f, g, h,… instead of our official nota-
tion fk
n for function letters, and lower-case letters a, b, c,… instead of our 
official notation ai for individual constants.
Exercises
2.8	
Translate the following sentences into wfs.
	
a.	 Anyone who is persistent can learn logic.
	
b.	 No politician is honest.
*	 As we shall see later, this is equivalent to ¬(∃x)(A(x) ∧ B(x)).



52
Introduction to Mathematical Logic
	
c.	 Not all birds can fly.
	
d.	 All birds cannot fly.
	
e.	 x is transcendental only if it is irrational.
	
f.	 Seniors date only juniors.
	
g.	 If anyone can solve the problem, Hilary can.
	
h.	 Nobody loves a loser.
	
i.	 Nobody in the statistics class is smarter than everyone in the logic 
class.
	
j.	 John hates all people who do not hate themselves.
	
k.	 Everyone loves somebody and no one loves everybody, or some-
body loves everybody and someone loves nobody.
	
l.	 You can fool some of the people all of the time, and you can fool all 
the people some of the time, but you can’t fool all the people all the 
time.
	
m.	  Any sets that have the same members are equal.
	
n.	  Anyone who knows Julia loves her.
	
o.	  There is no set belonging to precisely those sets that do not belong 
to themselves.
	
p.	  There is no barber who shaves precisely those men who do not 
shave themselves.
2.9	
Translate the following into everyday English. Note that everyday 
English does not use variables.
	
a.	 (∀x)(M(x) ∧ (∀y) ¬W(x, y) ⇒ U(x)), where M(x) means x is a man, W(x, y) 
means x is married to y, and U(x) means x is unhappy.
	
b.	 (∀x)(V(x) ∧ P(x) ⇒ A(x, b)), where V(x) means x is an even integer, P(x) 
means x is a prime integer, A(x, y) means x = y, and b denotes 2.
	
c.	 ¬(∃y)(I(y) ∧ (∀x)(I(x) ⇒ L(x, y))), where I(y) means y is an integer and 
L(x, y) means x ≤ y.
	
d.	 In the following wfs, A x
1
1( ) means x is a person and A x y
1
2( , ) means 
x hates y.
	
i.	 (
)(
( )
(
)(
( )
( , )))
∃
∧∀
⇒
x A x
y A y
A x y
1
1
1
1
1
2
	
ii.	 (
)(
( )
(
)(
( )
( , )))
∀
⇒∀
⇒
x A x
y A y
A x y
1
1
1
1
1
2
	
iii.	 (
)(
( )
(
)(
( )
(
( , )
( , ))))
∃
∧∀
⇒
⇔
x A x
y A y
A x y
A y y
1
1
1
1
1
2
1
2
	
e.	 (∀x)(H(x) ⇒ (∃y)(∃z)(¬A(y, z) ∧ (∀u)(P(u, x) ⇔ (A(u, y) ∨ A(u, z))))), where 
H(x) means x is a person, A(u, v) means “u = v,” and P(u, x) means u is 
a parent of x.



53
First-Order Logic and Model Theory
2.2  First-Order Languages and Their Interpretations: 
Satisfiability and Truth: Models
Well-formed formulas have meaning only when an interpretation is given for 
the symbols. We usually are interested in interpreting wfs whose symbols 
come from a specific language. For that reason, we shall define the notion of 
a first-order language.*
Definition
A first-order language L contains the following symbols.
	
a.	The propositional connectives ¬ and ⇒, and the universal quantifier 
symbol ∀.
	
b.	Punctuation marks: the left parenthesis “(”, the right parenthesis “)”, 
and the comma “,”.†
	
c.	Denumerably many individual variables x1, x2, .…
	
d.	A finite or denumerable, possibly empty, set of function letters.
	
e.	A finite or denumerable, possibly empty, set of individual constants.
	
f.	A nonempty set of predicate letters.
	
	 By a term of L we mean a term whose symbols are symbols of L.
	
	 By a wf of L we mean a wf whose symbols are symbols of L.
Thus, in a language L, some or all of the function letters and individual con-
stants may be absent, and some (but not all) of the predicate letters may be 
absent.‡ The individual constants, function letters, and predicate letters of a 
language L are called the nonlogical constants of L. Languages are designed 
in accordance with the subject matter we wish to study. A language for arith-
metic might contain function letters for addition and multiplication and a 
*	 The adjective “first-order” is used to distinguish the languages we shall study here from 
those in which there are predicates having other predicates or functions as arguments or in 
which predicate quantifiers or function quantifiers are permitted, or both. Most mathemati-
cal theories can be formalized within first-order languages, although there may be a loss 
of some of the intuitive content of those theories. Second-order languages are discussed in 
the appendix on second-order logic. Examples of higher-order languages are studied also in 
Gödel (1931), Tarski (1933), Church (1940), Leivant (1994), and van Bentham and Doets (1983). 
Differences between first-order and higher-order theories are examined in Corcoran (1980) 
and Shapiro (1991).
†	 The punctuation marks are not strictly necessary; they can be avoided by redefining the 
notions of term and wf. However, their use makes it easier to read and comprehend formulas.
‡	 If there were no predicate letters, there would be no wfs.



54
Introduction to Mathematical Logic
predicate letter for equality, whereas a language for geometry is likely to 
have predicate letters for equality and the notions of point and line, but no 
function letters at all.
Definition
Let L  be a first-order language. An interpretation M of L  consists of the fol-
lowing ingredients.
	
a.	A nonempty set D, called the domain of the interpretation.
	
b.	For each predicate letter Aj
n of L, an assignment of an n-place relation 
(
)
Aj
n M in D.
	
c.	For each function letter fj
n of L, an assignment of an n-place opera-
tion (
)
fj
n M in D (that is, a function from Dn into D).
	
d.	For each individual constant ai of L, an assignment of some fixed ele-
ment (ai)M of D.
Given such an interpretation, variables are thought of as ranging over the 
set D, and ¬, ⇒ and quantifiers are given their usual meaning. Remember 
that an n-place relation in D can be thought of as a subset of Dn, the set of all 
n-tuples of elements of D. For example, if D is the set of human beings, then 
the relation “father of” can be identified with the set of all ordered pairs 〈x, y〉 
such that x is the father of y.
For a given interpretation of a language L, a wf of L  without free variables 
(called a closed wf or a sentence) represents a proposition that is true or false, 
whereas a wf with free variables may be satisfied (i.e., true) for some values 
in the domain and not satisfied (i.e., false) for the others.
Examples
Consider the following wfs:
	
1.	A x x
1
2
1
2
(
,
)
	
2.	 (
)
(
,
)
∀x A x x
2
1
2
1
2
	
3.	 (
)(
)
(
,
)
∃
∀
x
x A x x
1
2
1
2
1
2
Let us take as domain the set of all positive integers and interpret A y z
1
2( , ) as 
y ≤ z. Then wf 1 represents the expression “x1 ≤ x2”, which is satisfied by all 
the ordered pairs 〈a, b〉 of positive integers such that a ≤ b. Wf 2 represents the 
expression “For all positive integers x2, x1 ≤ x2”,* which is satisfied only by the 
integer 1. Wf 3 is a true sentence asserting that there is a smallest positive integer. 
If we were to take as domain the set of all integers, then wf 3 would be false.
*	 In ordinary English, one would say “x1 is less than or equal to all positive integers.”



55
First-Order Logic and Model Theory
Exercises
2.10	 For the following wfs and for the given interpretations, indicate for 
what values the wfs are satisfied (if they contain free variables) or 
whether they are true or false (if they are closed wfs).
	
i.	A
f
x x
a
1
2
1
2
1
2
1
(
(
,
),
)
	
ii.	A x x
A x
x
1
2
1
2
1
2
2
1
(
,
)
(
,
)
⇒
	
iii.	(
)(
)(
)(
(
,
)
(
,
)
(
,
))
∀
∀
∀
∧
⇒
x
x
x
A x x
A x
x
A x x
1
2
3
1
2
1
2
1
2
2
3
1
2
1
3
	
a.	 The domain is the set of positive integers, A y z
1
2( , ) is y
z f
y z
≥,
( , )
1
2
 
is y · z, and a1 is 2.
	
b.	 The domain is the set of integers, A y z
1
2( , ) is y
z f
y z
= ,
( , )
1
2
 is 
y + z, and a1 is 0.
	
c.	 The domain is the set of all sets of integers, A y z
1
2( , ) is 
y
z f
y z
⊆,
( , )
1
2
 is y ∩ z, and a1 is the empty set ∅.
2.11	 Describe in everyday English the assertions determined by the follow-
ing wfs and interpretations.
	
a.	 (
)(
)(
( , )
(
)(
( )
( , )
( , )))
∀
∀
⇒∃
∧
∧
x
y A x y
z A z
A x z
A z y
1
2
1
1
1
2
1
2
, 
where 
the 
domain D is the set of real numbers, A x y
1
2( , ) means x < y, and A z
1
1( ) 
means z is a rational number.
	
b.	 (
)(
( )
(
)(
( )
( , )))
∀
⇒∃
∧
x A x
y A y
A y x
1
1
2
1
1
2
, where D is the set of all days 
and people, A x
1
1( ) means x is a day, A y
2
1( ) means y is a sucker, and 
A y x
1
2( , ) means y is born on day x.
	
c.	 (
)(
)(
( )
( )
(
( , )))
∀
∀
∧
⇒
x
y A x
A y
A
f
x y
1
1
1
1
2
1
1
2
, where D is the set of integers, 
A x
1
1( ) means x is odd, A x
2
1( ) means x is even, and f
x y
1
2( , ) denotes x + y.
	
d.	 For the following wfs, D is the set of all people and A u v
1
2( , ) means u 
loves v.
	
i.	(
)(
)(
( , )
∃
∀
x
y A x y
1
2
	
ii.	(
)(
)
( , )
∀
∃
y
x A x y
1
2
	
iii.	(
)(
)((
)(
( , ))
( , ))
∃
∀
∀
⇒
x
y
z A y z
A x y
1
2
1
2
	
iv.	(
)(
)
( , )
∃
∀
¬
x
y
A x y
1
2
	
e.	 (∀x) (∀u) (∀v) (∀w)(E(f(u, u), x) ∧ E(f(v, v), x) ∧ E(f(w, w), x) ⇒ E(u, v) ∨ 
E(u, w) ∨ E(v, w)), where D is the set of real numbers, E(x, y) means 
x = y, and f denotes the multiplication operation.
	
f.	 A x
x
A x x
A x
x
1
1
1
3
2
2
1
3
2
2
3
2
(
)
(
)(
(
,
)
(
,
))
∧∃
∧
 where D is the set of people, 
A u
1
1( ) means u is a woman and A u v
2
2( , ) means u is a parent of v.
	
g.	 (
)(
)(
(
)
(
)
(
(
,
)))
∀
∀
∧
⇒
x
x
A x
A x
A
f
x x
1
2
1
1
1
1
1
2
2
1
2
1
1
2
 where D is the set of real 
numbers, A u
1
1( ) means u is negative, A u
2
1( ) means u is positive, and 
f
u v
1
2( , ) is the product of u and v.
The concepts of satisfiability and truth are intuitively clear, but, following 
Tarski (1936), we also can provide a rigorous definition. Such a definition is 
necessary for carrying out precise proofs of many metamathematical results.



56
Introduction to Mathematical Logic
Satisfiability will be the fundamental notion, on the basis of which the notion 
of truth will be defined. Moreover, instead of talking about the n-tuples of objects 
that satisfy a wf that has n free variables, it is much more convenient from a tech-
nical standpoint to deal uniformly with denumerable sequences. What we have 
in mind is that a denumerable sequence s = (s1, s2, s3, …) is to be thought of as 
satisfying a wf B  that has x
x
x
j
j
jn
1
2
,
,
,
…
 as free variables (where j1 < j2 < ⋯ < jn) 
if the n-tuple 〈
…
〉
s
s
s
j
j
jn
1
2
,
,
,
 satisfies B in the usual sense. For example, a denu-
merable sequence (s1, s2, s3, …) of objects in the domain of an interpretation M 
will turn out to satisfy the wf A x
x
1
2
2
5
(
,
) if and only if the ordered pair, 〈s2, s5〉 is 
in the relation (
)
A1
2 M assigned to the predicate letter A1
2 by the interpretation M.
Let M be an interpretation of a language L and let D be the domain of M. 
Let Σ be the set of all denumerable sequences of elements of D. For a wf B of 
L, we shall define what it means for a sequence s = (s1, s2, …) in Σ to satisfy B 
in M. As a preliminary step, for a given s in Σ we shall define a function s* 
that assigns to each term t of L   an element s*(t) in D.
	
1.	If t is a variable xj, let s * (t) be sj.
	
2.	If t is an individual constant aj, then s*(t) is the interpretation (aj)M of 
this constant.
	
3.	If fk
n is a function letter, (
)
fk
n M is the corresponding operation in D, 
and t1, …, tn are terms, then
	
s
f
t
t
f
s t
s t
k
n
n
k
n
n
*
*
*
M
(
( ,
,
))
(
) (
( ),
,
( ))
1
1
…
=
…
Intuitively, s*(t) is the element of D obtained by substituting, for each j, a 
name of sj for all occurrences of xj in t and then performing the operations 
of the interpretation corresponding to the function letters of t. For instance, 
if t is f
x
f
x a
2
2
3
1
2
1
1
(
,
(
,
)) and if the interpretation has the set of integers as its 
domain, f2
2 and f1
2 are interpreted as ordinary multiplication and addition, 
respectively, and a1 is interpreted as 2, then, for any sequence s = (s1, s2, …) 
of integers, s*(t) is the integer s3 · (s1 + 2). This is really nothing more than the 
ordinary way of reading mathematical expressions.
Now we proceed to the definition of satisfaction, which will be an induc-
tive definition.
	
1.	If B is an atomic wf A t
t
k
n
n
( ,
,
)
1 …
 and (
)
Ak
n M is the corresponding 
n-place relation of the interpretation, then a sequence s = (s1, s2, …) 
satisfies B if and only if (
) (
( ),
,
( ))
A
s t
s t
k
n
n
M
*
*
1 …
—that is, if the n-tuple 
〈s*(t1), …, s*(tn)〉 is in the relation (
)
Ak
n M.*
*	 For example, if the domain of the interpretation is the set of real numbers, the interpreta-
tion of A1
2 is the relation ≤, and the interpretation of f1
1 is the function ex, then a sequence 
s = (s1, s2, …) of real numbers satisfies A
f
x
x
1
2
1
1
2
5
(
(
),
) if and only if e
s
s2
5
≤
. If the domain is the 
set of integers, the interpretation of A
x y u v
1
4( ,
, , ) is x . v = u . y, and the interpretation of a1 is 3, 
then a sequence s = (s1, s2, …) of integers satisfies A
x
a
x
x
1
4
3
1
1
3
(
,
,
,
) if and only if (s3)2 = 3s1.



57
First-Order Logic and Model Theory
	
2.	s satisfies ¬B if and only if s does not satisfy B.
	
3.	s satisfies B ⇒ C   if and only if s does not satisfy B or s satisfies C.
	
4.	s satisfies (∀xi)B  if and only if every sequence that differs from s in at 
most the ith component satisfies B.*
Intuitively, a sequence s = (s1, s2, …) satisfies a wf B  if and only if, when, for 
each i, we replace all free occurrences of xi (if any) in B  by a symbol repre-
senting si, the resulting proposition is true under the given interpretation.
Now we can define the notions of truth and falsity of wfs for a given 
interpretation.
Definitions
	
1.	A wf B is true for the interpretation M (written ⊧M B) if and only if 
every sequence in Σ satisfies B.
	
2.	B is said to be false for M if and only if no sequence in Σ satisfies B.
	
3.	An interpretation M is said to be a model for a set Γ of wfs if and only 
if every wf in Γ is true for M.
The plausibility of our definition of truth will be strengthened by the fact 
that we can derive all of the following expected properties I–XI of the notions 
of truth, falsity, and satisfaction. Proofs that are not explicitly given are left 
to the reader (or may be found in the answer to Exercise 2.12). Most of the 
results are also obvious if one wishes to use only the ordinary intuitive 
understanding of the notions of truth, falsity, and satisfaction.
	
I.	a.	 B is false for an interpretation M if and only if ¬B is true for M.
	
	 b.	 B is true for M if and only if ¬B is false for M.
	
II.	It is not the case that both ⊧M B and ⊧M ¬B; that is, no wf can be both 
true and false for M.
	 III.	If ⊧M B and ⊧M B ⇒ C, then ⊧M C.
	 IV.	B ⇒ C is false for M if and only if ⊧M B and ⊧M ¬C.
	
V.	 †Consider an interpretation M with domain D.
	
	 a.	 A sequence s satisfies B ∧ C  if and only if s satisfies B  and s satisfies C.
	
	 b.	 s satisfies B  ∨ C  if and only if s satisfies B or s satisfies C.
	
	 c.	 s satisfies B ⇔ C   if and only if s satisfies both B and C or s satisfies 
neither B  nor C.
*	 In other words, a sequence s = (s1, s2, …, si, …) satisfies (∀xi)B if and only if, for every element 
c of the domain, the sequence (s1, s2, …, c, …) satisfies B. Here, (s1, s2, …, c, …) denotes the 
sequence obtained from (s1, s2, …, si, …) by replacing the ith component si by c. Note also that, 
if s satisfies (∀xi)B, then, as a special case, s satisfies B.
†	 Remember that B ∧ C, B ∨ C, B ⇔ C and (∃xi)B are abbreviations for ¬(B ⇒ ¬C), ¬B ⇒ C, 
(B ⇒ C) ∧ (C ⇒ B) and ¬(∀xi) ¬B, respectively.



58
Introduction to Mathematical Logic
	
	 d.	 s satisfies (∃xi)B if and only if there is a sequence s′ that differs from s 
in at most the ith component such that s′ satisfies B. (In other words 
s = (s1, s2, …, si, …) satisfies (∃xi)B if and only if there is an element c 
in the domain D such that the sequence (s1, s2, …, c, …) satisfies B.)
	 VI.	⊧M B if and only if ⊧M(∀xi)B.
	
	 We can extend this result in the following way. By the closure* of B we 
mean the closed wf obtained from B by prefixing in universal quanti-
fiers those variables, in order of descending subscripts, that are free 
in B. If B has no free variables, the closure of B is defined to be B itself. 
For example, if B is A x x
x A x x x
1
2
2
5
2
1
3
1
2
3
(
,
)
(
)
(
,
,
)
⇒¬ ∃
, its closure is (∀x5)
(∀x3)(∀x2)(∀x1)B. It follows from (VI) that a wf B is true if and only if its 
closure is true.
	 VII.	Every instance of a tautology is true for any interpretation. (An instance 
of a statement form is a wf obtained from the statement form by sub-
stituting wfs for all statement letters, with all occurrences of the same 
statement letter being replaced by the same wf. Thus, an instance of 
A1 ⇒ ¬A2 ∨ A1 is A x
x A x
A x
1
1
2
1
1
1
1
1
1
2
(
)
( (
)
(
))
(
)
⇒¬ ∀
∨
.)
	
	 To prove (VII), show that all instances of the axioms of the system L are 
true and then use (III) and Proposition 1.14.
	VIII.	If the free variables (if any) of a wf B occur in the list x
x
i
ik
1,
,
…
 and if 
the sequences s and s′ have the same components in the i1th, …, ikth 
places, then s satisfies B if and only if s′ satisfies B [Hint: Use induc-
tion on the number of connectives and quantifiers in B. First prove this 
lemma: If the variables in a term t occur in the list x
x
i
ik
1,
,
…
, and if s 
and s′ have the same components in the i1th, …, ikth places, then s*(t) = 
(s′)*(t). In particular, if t contains no variables at all, s*(t) = (s′)*(t) for any 
sequences s and s′.]
Although, by (VIII), a particular wf B with k free variables is essentially satis-
fied or not only by k-tuples, rather than by denumerable sequences, it is more 
convenient for a general treatment of satisfaction to deal with infinite rather 
than finite sequences. If we were to define satisfaction using finite sequences, 
conditions 3 and 4 of the definition of satisfaction would become much more 
complicated.
Let x
x
i
ik
1,
,
…
 be k distinct variables in order of increasing subscripts. Let 
B (
,
,
)
x
x
i
ik
1 …
 be a wf that has x
x
i
ik
1,
,
…
 as its only free variables. The set of 
k-tuples 〈b1, …, bk〉 of elements of the domain D such that any sequence with 
b1, …, bk in its i1th, …, ikth places, respectively, satisfies B (
,
,
)
x
x
i
ik
1 …
 is called 
the relation (or property†) of the interpretation defined by B. Extending our ter-
minology, we shall say that every k-tuple 〈b1, …, bk〉 in this relation satisfies 
B (
,
,
)
x
x
i
ik
1 …
 in the interpretation M; this will be written ⊧M B[b1, …, bk] . This 
extended notion of satisfaction corresponds to the original intuitive notion.
*	 A better term for closure would be universal closure.
†	 When k = 1, the relation is called a property.



59
First-Order Logic and Model Theory
Examples
	
1.	If the domain D of M is the set of human beings, A x y
1
2( , ) is inter-
preted as x is a brother of y, and A x y
2
2( , ) is interpreted as x is a par-
ent of y, then the binary relation on D corresponding to the wf 
B (
,
):(
)(
(
,
)
(
,
))
x x
x
A x x
A x
x
1
2
3
1
2
1
3
2
2
3
2
∃
∧
 is the relation of unclehood. 
⊧M B[b, c] when and only when b is an uncle of c.
	
2.	If the domain is the set of positive integers, A1
2 is interpreted as =, f1
2 is 
interpreted as multiplication, and a1 is interpreted as 1, then the wf B(x1):
	
¬
∧∀
∃
⇒
∨
A x a
x
x A x
f
x
x
A x
x
A x
1
2
1
1
2
3
1
2
1
1
2
2
3
1
2
2
1
1
2
(
,
)
(
)((
)
(
,
(
,
))
(
,
)
(
2
1
,
))
a
	
	 determines the property of being a prime number. Thus ⊧M B[k] if 
and only if k is a prime number.
	 IX.	 If B is a closed wf of a language L, then, for any interpretation M, 
either ⊧M B or ⊧M ¬B—that is, either B is true for M or B is false for 
M. [Hint: Use (VIII).] Of course, B may be true for some interpreta-
tions and false for others. (As an example, consider A a
1
1
1
(
). If M is 
an interpretation whose domain is the set of positive integers, A1
1 is 
interpreted as the property of being a prime, and the interpretation 
of a1 is 2, then A a
1
1
1
(
) is true. If we change the interpretation by inter-
preting a1 as 4, then A a
1
1
1
(
) becomes false.)
If B is not closed—that is, if B contains free variables—B may be 
neither true nor false for some interpretation. For example, if B is 
A x x
1
2
1
2
(
,
) and we consider an interpretation in which the domain 
is the set of integers and A y z
1
2( , )  is interpreted as y < z, then B is 
satisfied by only those sequences s = (s1, s2, …) of integers in which 
s1 < s2. Hence, B is neither true nor false for this interpretation. On 
the other hand, there are wfs that are not closed but that neverthe-
less are true or false for every interpretation. A simple example is the 
wf A x
A x
1
1
1
1
1
1
(
)
(
),
∨¬
 which is true for every interpretation.
	
X.	Assume t is free for xi in B(xi). Then (∀xi)B(xi) ⇒ B(t) is true for all 
interpretations.
	
	 The proof of (X) is based upon the following lemmas.
Lemma 1
If t and u are terms, s is a sequence in Σ, t′ results from t by replacing all 
occurrences of xi by u, and s′ results from s by replacing the ith component 
of s by s*(u), then s*(t′) = (s′)*(t). [Hint: Use induction on the length of t.*]
*	 The length of an expression is the number of occurrences of symbols in the expression.



60
Introduction to Mathematical Logic
Lemma 2
Let t be free for xi in B(xi). Then:
	
a.	A sequences s = (s1, s2, …) satisfies B(t) if and only if the sequence s′, 
obtained from s by substituting s*(t) for si in the ith place, satisfies B(xi). 
[Hint: Use induction on the number of occurrences of connectives and 
quantifiers in B(xi), applying Lemma 1.]
	
b.	If (∀xi)B(xi) is satisfied by the sequence s, then B(t) also is satisfied by s.
	 XI.	If B does not contain xi free, then (∀xi)(B ⇒ C) ⇒ (B ⇒ (∀xi)C) is true for 
all interpretations.
Proof
Assume (XI) is not correct. Then (∀xi)(B ⇒ C) ⇒ (B ⇒ (∀xi)C) is not true for some 
interpretation. By condition 3 of the definition of satisfaction, there is a sequence 
s such that s satisfies (∀xi)(B ⇒ C) and s does not satisfy B ⇒ (∀xi)C. From the latter 
and condition 3, s satisfies B and s does not satisfy (∀xi)C. Hence, by condition 4, 
there is a sequence s′, differing from s in at most the ith place, such that s′ does 
not satisfy C. Since xi is free in neither (∀xi)(B ⇒ C) nor B, and since s satisfies 
both of these wfs, it follows by (VIII) that s′ also satisfies both (∀xi)(B ⇒ C) and B. 
Since s′ satisfies (∀xi)(B ⇒ C), it follows by condition 4 that s′ satisfies B ⇒ C. Since 
s′ satisfies B ⇒ C and B, condition 3 implies that s′ satisfies C, which contradicts 
the fact that s′ does not satisfy C. Hence, (XI) is established.
Exercises
2.12	 Verify (I)–(X).
2.13	 Prove that a closed wf B is true for M if and only if B is satisfied by some 
sequence s in Σ. (Remember that Σ is the set of denumerable sequences 
of elements in the domain of M.)
2.14	 Find the properties or relations determined by the following wfs and 
interpretations.
	
a.	 [(
)
(
( , ), )]
[(
)
(
( , ), )]
∃
∧∃
u A
f
x u y
v A
f
x v z
1
2
1
2
1
2
1
2
, where the domain D is the 
set of integers, A1
2 is =, and f1
2 is multiplication.
	
b.	 Here, D is the set of nonnegative integers, A1
2 is =, a1 denotes 0, f1
2 is 
addition, and f2
2 is multiplication.
	
i.	 [(
)(
( ,
)
(
( , ), ))]
∃
¬
∧
z
A z a
A
f
x z y
1
2
1
1
2
1
2
	
ii.	 (
)
( ,
( , ))
∃y A x f
y y
1
2
2
2
	
c.	 (
)
(
(
,
),
)
∃x A
f
x x
x
3
1
2
1
2
1
3
2 , where D is the set of positive integers, A1
2 is =, 
and f1
2 is multiplication,



61
First-Order Logic and Model Theory
	
d.	 A x
x
A x x
1
1
1
2
1
2
1
2
(
)
(
)
(
,
)
∧∀
¬
, where D is the set of all living people, A x
1
1( ) 
means x is a man and A x y
1
2( , ) means x is married to y.
	
e.	 i.	 (
)(
)(
(
,
)
(
,
)
(
,
))
∃
∃
∧
∧
x
x
A x x
A x
x
A x x
1
2
1
2
1
3
1
2
2
4
2
2
1
2
	
	
ii.	 (
)(
(
,
)
(
,
))
∃
∧
x
A x x
A x
x
3
1
2
1
3
1
2
3
2
	
	
	
where D is the set of all people, A x y
1
2( , ) means x is a parent of y, 
and A x y
2
2( , ) means x and y are siblings.
	
f.	 (
)((
)(
(
(
,
),
)
(
)(
(
(
,
),
))
∀
∃
∧∃
⇒
x
x
A
f
x
x
x
x
A
f
x
x
x
A
3
4
1
2
1
2
4
3
1
4
1
2
1
2
4
3
2
1
2
3
1
(
,
)),
x
a
 
where D is the set of positive integers, A1
2 is =, f1
2 is multiplication, 
and a1 denotes 1.
	
g.	 ¬
∧∃
∧
A x
x
y A y x
A x
y
1
2
2
1
1
2
1
2
2
2
(
,
)
(
)(
( ,
)
(
, )), where D is the set of all peo-
ple, A u v
1
2( , ) means u is a parent of v, and A u v
2
2( , ) means u is a wife 
of v.
2.15	 For each of the following sentences and interpretations, write a transla-
tion into ordinary English and determine its truth or falsity.
	
a.	 The domain D is the set of nonnegative integers, A1
2 is =, f1
2 is addi-
tion, f2
2 is multiplication, a1 denotes 0, and a2 denotes 1.
	
	
i.	 (
)(
)(
( ,
( , ))
( ,
(
( , ),
)))
∀
∃
∨
x
y A x f
y y
A x f
f
y y a
1
2
1
2
1
2
1
2
1
2
2
	
	
ii.	 (
)(
)(
(
( , ),
)
( ,
)
( ,
))
∀
∀
⇒
∨
x
y A
f
x y a
A x a
A y a
1
2
2
2
1
1
2
1
1
2
1
	
	
iii.	(
)
(
( , ),
)
∃y A
f
y y a
1
2
1
2
2
	
b.	 Here, D is the set of integers, A1
2 is =, and f1
2 is addition.
	
	
i.	 (
)(
)
(
(
,
),
(
,
))
∀
∀
x
x A
f
x x
f
x
x
1
2
1
2
1
2
1
2
1
2
2
1
	
	
ii.	 (
)(
)(
)
(
(
,
(
,
)),
(
(
,
),
))
∀
∀
∀
x
x
x A
f
x
f
x
x
f
f
x x
x
1
2
3
1
2
1
2
1
1
2
2
3
1
2
1
2
1
2
3
	
	
iii.	(
)(
)(
)
(
(
,
),
)
∀
∀
∃
x
x
x A
f
x x
x
1
2
3
1
2
1
2
1
3
2
	
c.	 The wfs are the same as in part (b), but the domain is the set of posi-
tive integers, A1
2 is =, and f
x y
1
2( , ) is xy.
	
d.	 The domain is the set of rational numbers, A1
2 is =, A2
2 is <, f1
2 is mul-
tiplication, f
x
1
1( ) is x + 1, and a1 denotes 0.
	
	
i.	 (
)
(
( , ),
(
(
)))
∃x A
f
x x
f
f
a
1
2
1
2
1
1
1
1
1
	
	
ii.	 (
)(
)(
( , )
(
)(
( , )
( , )))
∀
∀
⇒∃
∧
x
y A x y
z A x z
A z y
2
2
2
2
2
2
	
	
iii.	(
)(
( ,
)
(
)
(
( , ),
(
)))
∀
¬
⇒∃
x
A x a
y A
f
x y
f
a
1
2
1
1
2
1
2
1
1
1
	
e.	 The domain is the set of nonnegative integers, A u v
1
2( , ) means u ≤ v, 
and A u v w
1
3( , ,
) means u + v = w.
	
	
i.	 (
)(
)(
)(
( , , )
( , , ))
∀
∀
∀
⇒
x
y
z A x y z
A y x z
1
3
1
3
	
	
ii.	 (
)(
)(
( , , )
( , ))
∀
∀
⇒
x
y A x x y
A x y
1
3
1
2
	
	
iii.	(
)(
)(
( , )
( , , ))
∀
∀
⇒
x
y A x y
A x x y
1
2
1
3
	
	
iv.	(
)(
)
( , , )
∃
∀
x
y A x y y
1
3



62
Introduction to Mathematical Logic
	
	
v.	 (
)(
)
( , )
∃
∀
y
x A x y
1
2
	
	
vi.	(
)(
)(
( , )
(
)
( , , ))
∀
∀
⇔∃
x
y A x y
z A x z y
1
2
1
3
	
f.	 The domain is the set of nonnegative integers, A u v
1
2( , ) means 
u
v f
u v
u
v
=
=
+
,
( , )
1
2
, and f
u v
u v
2
2( , ) =
⋅
	
(
)(
)(
)
( ,
(
( , ),
( , )))
∀
∃
∃
x
y
z A x f
f
y y
f
z z
1
2
1
2
2
2
2
2
Definitions
A wf B is said to be logically valid if and only if B is true for every 
interpretation.*
B is said to be satisfiable if and only if there is an interpretation for which B 
is satisfied by at least one sequence.
It is obvious that B is logically valid if and only if ¬B is not satisfiable, and 
B is satisfiable if and only if ¬B is not logically valid.
If B is a closed wf, then we know that B is either true or false for any given 
interpretation; that is, B is satisfied by all sequences or by none. Therefore, if 
B is closed, then B is satisfiable if and only if B is true for some interpretation.
A set Γ of wfs is said to be satisfiable if and only if there is an interpretation 
in which there is a sequence that satisfies every wf of Γ.
It is impossible for both a wf B and its negation ¬B to be logically valid. 
For if B is true for an interpretation, then ¬B is false for that interpretation.
We say that B is contradictory if and only if B is false for every interpreta-
tion, or, equivalently, if and only if ¬B is logically valid.
B is said to logically imply C if and only if, in every interpretation, every 
sequence that satisfies B also satisfies C. More generally, C is said to be a logi-
cal consequence of a set Γ of wfs if and only if, in every interpretation, every 
sequence that satisfies every wf in Γ also satisfies C.
B and C are said to be logically equivalent if and only if they logically imply 
each other.
The following assertions are easy consequences of these definitions.
	
1.	B  logically implies C   if and only if B ⇒ C  is logically valid.
	
2.	B  and C   are logically equivalent if and only if B ⇔ C   is logically valid.
	
3.	If B  logically implies C and B  is true in a given interpretation, then 
so is C.
	
4.	If C   is a logical consequence of a set Γ of wfs and all wfs in Γ are true 
in a given interpretation, then so is C.
*	 The mathematician and philosopher G.W. Leibniz (1646–1716) gave a similar definition: B is 
logically valid if and only if B is true in all “possible worlds.”



63
First-Order Logic and Model Theory
Exercise
2.16	 Prove assertions 1–4.
Examples
	
1.	Every instance of a tautology is logically valid (VII).
	
2.	If t is free for x in B(x), then (∀x)B(x) ⇒ B(t) is logically valid (X).
	
3.	If B does not contain x free, then (∀x)(B ⇒ C) ⇒ (B ⇒ (∀x)C) is logi-
cally valid (XI).
	
4.	B is logically valid if and only if (∀y1) … (∀yn)B is logically valid (VI).
	
5.	The wf (
)(
)
(
,
)
(
)(
)
(
,
)
∀
∃
⇒∃
∀
x
x A x x
x
x A x x
2
1
1
2
1
2
1
2
1
2
1
2  is not logically 
valid. As a counterexample, let the domain D be the set of integers 
and let A y z
1
2( , ) mean y < z. Then (
)(
)
(
,
)
∀
∃
x
x A x x
2
1
1
2
1
2  is true but 
(
)(
)
(
,
)
∃
∀
x
x A x x
1
2
1
2
1
2  is false.
Exercises
2.17	 Show that the following wfs are not logically valid.
	
a.	 [(
)
(
)
(
)
(
)]
[(
)(
(
)
(
))]
∀
⇒∀
⇒
∀
⇒
x A x
x A x
x
A x
A x
1
1
1
1
1
2
1
1
1
1
1
1
2
1
1
	
b.	 [(
)(
(
)
(
))]
[((
))
(
))
(
)
(
)]
∀
∨
⇒
∀
∨∀
x
A x
A x
x
A x
x A x
1
1
1
1
2
1
1
1
1
1
1
1
2
1
1
2.18	 Show that the following wfs are logically valid.*
	
a.	 B(t) ⇒ (∃xi)B(xi) if t is free for xi in B(xi)
	
b.	 (∀xi)B ⇒ (∃xi)B
	
c.	 (∀xi)(∀xj)B ⇒ (∀xj)(∀xi)B
	
d.	 (∀xi)B ⇔ ¬(∃xi)¬B
	
e.	 (∀xi)(B ⇒ C) ⇒ ((∀xi)B ⇒ (∀xi)C)
	
f.	 ((∀xi)B) ∧ (∀xi)C ⇔ (∀xi)(B ∧ C)
	
g.	 ((∀xi)B) ∨ (∀xi)C ⇒ (∀xi)(B ∨ C)
	
h.	 (∃xi)(∃xj)B ⇔ (∃xj)(∃xi)B
	
i.	 (∃xi)(∀xj)B ⇒ (∀xj)(∃xi)B
2.19 a.	 If B is a closed wf, show that B logically implies C if and only if C is 
true for every interpretation for which B is true.
	
b.	 Although, by (VI), (
)
(
)
∀x A x
1
1
1
1  is true whenever A x
1
1
1
(
) is true, find 
an interpretation for which A x
x A x
1
1
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
)
⇒∀
 is not true. (Hence, 
the hypothesis that B is a closed wf is essential in (a).)
*	 At this point, one can use intuitive arguments or one can use the rigorous definitions of 
satisfaction and truth, as in the argument above for (XI). Later on, we shall discover another 
method for showing logical validity.



64
Introduction to Mathematical Logic
2.20	 Prove that, if the free variables of B are y1, …, yn, then B is satisfiable if 
and only if (∃y1), …, (∃yn)B is satisfiable.
2.21	 Produce counterexamples to show that the following wfs are not logi-
cally valid (that is, in each case, find an interpretation for which the wf 
is not true).
	
a.	 [(
)(
)(
)(
( , )
( , )
( , ))
(
)
( , )]
∀
∀
∀
∧
⇒
∧∀
¬
x
y
z A x y
A y z
A x z
x
A x x
1
2
1
2
1
2
1
2
 
	
	
⇒∃
∀
¬
(
)(
)
( , )
x
y
A x y
1
2
	
b.	 (
)(
)
( , )
(
)
( , )
∀
∃
⇒∃
x
y A x y
y A y y
1
2
1
2
	
c.	 (
)(
)
( , )
(
)
( , )
∃
∃
⇒∃
x
y A x y
y A y y
1
2
1
2
	
d.	 [(
)
( )
(
)
( )]
(
)(
( )
( ))
∃
⇔∃
⇒∀
⇔
x A x
x A x
x A x
A x
1
1
2
1
1
1
2
1
	
e.	 (
)(
( )
( ))
((
)
( )
(
)
( ))
∃
⇒
⇒
∃
⇒∃
x A x
A x
x A x
x A x
1
1
2
1
1
1
2
1
	
f.	 [(
)(
)(
( , )
( , ))
(
)(
)(
)(
( , )
( ,
∀
∀
⇒
∧∀
∀
∀
∧
x
y A x y
A y x
x
y
z A x y
A y z
1
2
1
2
1
2
1
2
)
	
	
⇒
⇒∀
A x z
x A x x
1
2
1
2
( , ))]
(
)
( , )
	
g.D	(
)(
)(
( , )
( , )
[
( , )
( , )])
∃
∀
∧¬
⇒
⇔
x
y A x y
A y x
A x x
A y y
1
2
1
2
1
2
1
2
	
h.	 (
)(
)(
)(
( , )
(
( , )
( , )
( , )))
∀
∀
∀
∧
⇒
∨
x
y
z A x x
A x z
A x y
A y z
1
2
1
2
1
2
1
2
	
	
⇒∃
∀
(
)(
)
( , )
y
z A y z
1
2
	
i.	 (
)(
)(
)((
( , )
( , ))
(
( , )
( , )))
∃
∀
∃
⇒
⇒
⇒
x
y
z
A y z
A x z
A x x
A y x
1
2
1
2
1
2
1
2
2.22	 By introducing appropriate notation, write the sentences of each of the 
following arguments as wfs and determine whether the argument is 
correct, that is, determine whether the conclusion is logically implied 
by the conjunction of the premisses
	
a.	 All scientists are neurotic. No vegetarians are neurotic. Therefore, 
no vegetarians are scientists.
	
b.	 All men are animals. Some animals are carnivorous. Therefore, 
some men are carnivorous.
	
c.	 Some geniuses are celibate. Some students are not celibate. 
Therefore, some students are not geniuses.
	
d.	 Any barber in Jonesville shaves exactly those men in Jonesville who 
do not shave themselves. Hence, there is no barber in Jonesville.
	
e.	 For any numbers x, y, z, if x > y and y > z, then x > z. x > x is false for 
all numbers x. Therefore, for any numbers x and y, if x > y, then it is 
not the case that y > x.
	
f.	 No student in the statistics class is smarter than every student in 
the logic class. Hence, some student in the logic class is smarter 
than every student in the statistics class.
	
g.	 Everyone who is sane can understand mathematics. None of 
Hegel’s sons can understand mathematics. No madmen are fit to 
vote. Hence, none of Hegel’s sons is fit to vote.



65
First-Order Logic and Model Theory
	
h.	 For every set x, there is a set y such that the cardinality of y is greater 
than the cardinality of x. If x is included in y, the cardinality of x 
is not greater than the cardinality of y. Every set is included in V. 
Hence, V is not a set.
	
i.	 For all positive integers x, x ≤ x. For all positive integers x, y, z, if 
x ≤ y and y ≤ z, then x ≤ z. For all positive integers x and y, x ≤ y or 
y ≤ x. Therefore, there is a positive integer y such that, for all posi-
tive integers x, y ≤ x.
	
j.	 For any integers x, y, z, if x > y and y > z, then x > z. x > x is false for 
all integers x. Therefore, for any integers x and y, if x > y, then it is 
not the case that y > x.
2.23	 Determine whether the following sets of wfs are compatible—that is, 
whether their conjunction is satisfiable.
	
a.	 (
)(
)
( , )
∃
∃
x
y A x y
1
2
	
	
(
)(
)(
)(
( , )
( , ))
∀
∀
∃
∧
x
y
z A x z
A z y
1
2
1
2
	
b.	 (
)(
)
( , )
∀
∃
x
y A y x
1
2
	
	
(
)(
)(
( , )
( , ))
∀
∀
⇒¬
x
y A x y
A y x
1
2
1
2
	
	
(
)(
)(
)(
( , )
( , )
( , ))
∀
∀
∀
∧
⇒
x
y
z A x y
A y z
A x z
1
2
1
2
1
2
	
c.	 All unicorns are animals.
	
	
No unicorns are animals.
2.24	 Determine whether the following wfs are logically valid.
	
a.	 ¬ ∃
∀
⇔¬
(
)(
)(
( , )
( , ))
y
x A x y
A x x
1
2
1
2
	
b.	 [(
)
( )
(
)
( )]
(
)(
( )
( ))
∃
⇒∃
⇒∃
⇒
x A x
x A x
x A x
A x
1
1
2
1
1
1
2
1
	
c.	 (
)(
( )
(
)
( ))
∃
⇒∀
x A x
y A y
1
1
1
1
	
d.	 (
)(
( )
( ))
(((
)
( ))
(
)
( ))
∀
∨
⇒
∀
∨∃
x A x
A x
x A x
x A x
1
1
2
1
1
1
2
1
	
e.	 (
)(
)(
( , )
(
)
( , ))
∃
∃
⇒∀
x
y A x y
z A z y
1
2
1
2
	
f.	 (
)(
)(
( )
( ))
(
)(
( )
( ))
∃
∃
⇒
⇒∃
⇒
x
y A x
A y
x A x
A x
1
1
2
1
1
1
2
1
	
g.	 (
)(
( )
( ))
(
)(
( )
( ))
∀
⇒
⇒¬ ∀
⇒¬
x A x
A x
x A x
A x
1
1
2
1
1
1
2
1
	
h.	 (
)
( , )
(
)(
)
( , )
∃
⇒∃
∃
x A x x
x
y A x y
1
2
1
2
	
i.	 ((
)
( ))
(
)
( )
(
)(
( )
( ))
∃
∧∃
⇒∃
∧
x A x
x A x
x A x
A x
1
1
2
1
1
1
2
1
	
j.	 ((
)
( ))
(
)
( )
(
)(
( )
( ))
∀
∨∀
⇒∀
∨
x A x
x A x
x A x
A x
1
1
2
1
1
1
2
1
2.25	 Exhibit a logically valid wf that is not an instance of a tautology. 
However, show that any logically valid open wf (that is, a wf without 
quantifiers) must be an instance of a tautology.



66
Introduction to Mathematical Logic
2.26	 a.	 Find a satisfiable closed wf that is not true in any interpretation 
whose domain has only one member.
	
b.	 Find a satisfiable closed wf that is not true in any interpretation 
whose domain has fewer than three members.
2.3  First-Order Theories
In the case of the propositional calculus, the method of truth tables provides an 
effective test as to whether any given statement form is a tautology. However, 
there does not seem to be any effective process for determining whether a 
given wf is logically valid, since, in general, one has to check the truth of a 
wf for interpretations with arbitrarily large finite or infinite domains. In fact, 
we shall see later that, according to a plausible definition of “effective,” it may 
actually be proved that there is no effective way to test for logical validity. The 
axiomatic method, which was a luxury in the study of the propositional cal-
culus, thus appears to be a necessity in the study of wfs involving quantifiers,* 
and we therefore turn now to the consideration of first-order theories.
Let L be a first-order language. A first-order theory in the language L will 
be a formal theory K whose symbols and wfs are the symbols and wfs of L 
and whose axioms and rules of inference are specified in the following way.†
The axioms of K are divided into two classes: the logical axioms and the 
proper (or nonlogical) axioms.
2.3.1  Logical Axioms
If B, C, and D are wfs of L, then the following are logical axioms of K:
(A1) B ⇒ (C ⇒ B)
(A2) (B ⇒ (C ⇒ D)) ⇒ ((B ⇒ C) ⇒ (B ⇒ D))
(A3) (¬C ⇒ ¬B) ⇒ ((¬C ⇒ B) ⇒ C)
*	 There is still another reason for a formal axiomatic approach. Concepts and propositions 
that involve the notion of interpretation and related ideas such as truth and model are often 
called semantical to distinguish them from syntactical concepts, which refer to simple rela-
tions among symbols and expressions of precise formal languages. Since semantical notions 
are set-theoretic in character, and since set theory, because of the paradoxes, is considered 
a rather shaky foundation for the study of mathematical logic, many logicians consider a 
syntactical approach, consisting of a study of formal axiomatic theories using only rather 
weak number-theoretic methods, to be much safer. For further discussions, see the pioneer-
ing study on semantics by Tarski (1936), as well as Kleene (1952), Church (1956), and Hilbert 
and Bernays (1934).
†	 The reader might wish to review the definition of formal theory in Section 1.4. We shall use 
the terminology (proof, theorem, consequence, axiomatic, ⊢ B, etc.) and notation (Γ ⊢ B, ⊢ B) 
introduced there.



67
First-Order Logic and Model Theory
(A4) (∀xi)B(xi) ⇒ B(t) if B(xi) is a wf of L  and t is a term of L  that is free 
for xi in B(xi). Note here that t may be identical with xi so that all 
wfs (∀xi)B ⇒ B are axioms by virtue of axiom (A4).
(A5) (∀xi)(B ⇒ C) ⇒ (B ⇒ (∀xi)C) if B contains no free occurrences of xi.
2.3.2  Proper Axioms
These cannot be specified, since they vary from theory to theory. A first-
order theory in which there are no proper axioms is called a first-order predi-
cate calculus.
2.3.3  Rules of Inference
The rules of inference of any first-order theory are:
	
1.	Modus ponens: C follows from B and B ⇒ C.
	
2.	Generalization: (∀xi)B follows from B.
We shall use the abbreviations MP and Gen, respectively, to indicate applica-
tions of these rules.
Definition
Let K be a first-order theory in the language L. By a model of K we mean an 
interpretation of L for which all the axioms of K are true.
By (III) and (VI) on page 57, if the rules of modus ponens and general-
ization are applied to wfs that are true for a given interpretation, then the 
results of these applications are also true. Hence every theorem of K is true in 
every model of K.
As we shall see, the logical axioms are so designed that the logical conse-
quences (in the sense defined on pages 63–64) of the closures of the axioms of 
K are precisely the theorems of K. In particular, if K is a first-order predicate 
calculus, it turns out that the theorems of K are just those wfs of K that are 
logically valid.
Some explanation is needed for the restrictions in axiom schemas (A4) 
and (A5). In the case of (A4), if t were not free for xi in B(xi), the following 
unpleasant result would arise: let B(x1) be ¬ ∀
(
)
(
,
)
x A x x
2
1
2
1
2  and let t be x2. 
Notice that t is not free for x1 in B(x1). Consider the following pseudo-
instance of axiom (A4):
	
( )
(
)
(
)
(
,
)
(
)
(
,
)
∇
∀
¬ ∀
(
) ⇒¬ ∀
x
x A x x
x A x
x
1
2
1
2
1
2
2
1
2
2
2



68
Introduction to Mathematical Logic
Now take as interpretation any domain with at least two members and let 
A1
2 stand for the identity relation. Then the antecedent of (∇) is true and the 
consequent false. Thus, (∇) is false for this interpretation.
In the case of axiom (A5), relaxation of the restriction that xi not be free in 
B would lead to the following disaster. Let B and C both be A x
1
1
1
(
). Thus, x1 is 
free in B. Consider the following pseudo-instance of axiom (A5):
	
(
)
(
)
(
)
(
)
(
)
(
)
(
)
∇∇
∀
⇒
(
) ⇒
⇒∀
(
)
x
A x
A x
A x
x A x
1
1
1
1
1
1
1
1
1
1
1
1
1
1
The antecedent of (∇∇) is logically valid. Now take as domain the set of 
integers and let A x
1
1( ) mean that x is even. Then (
)
(
)
∀x A x
1
1
1
1  is false. So, any 
sequence s = (s1, s2, …) for which s1 is even does not satisfy the consequent of 
(∇∇).* Hence, (∇∇) is not true for this interpretation.
Examples of first-order theories
	
1.	Partial order. Let the language L have a single predicate letter A2
2 and 
no function letters and individual constants. We shall write xi < xj 
instead of A x x
i
j
2
2(
,
). The theory K has two proper axioms.
	
a.	 (∀x1)(¬ x1 < x1)	
(irreflexivity)
	
b.	 (∀x1)(∀x2)(∀x3)(x1 < x2 ∧ x2 < x3 ⇒ x1 < x3)	
(transitivity)
	
	 A model of the theory is called a partially ordered structure.
	
2.	Group theory. Let the language L have one predicate letter A1
2, one 
function letter f1
2, and one individual constant a1. To conform with 
ordinary notation, we shall write t = s instead of A t s t
s
1
2( , ), +  instead 
of f
t s
1
2( , ), and 0 instead of a1. The proper axioms of K are:
	
a.	 (∀x1)(∀x2)(∀x3)(x1 +(x2 + x3) 	
(associativity)
	
	
= (x1 + x2) + x3)
	
b.	 (∀x1)(0 + x1 = x1)	
(identity)
	
c.	 (∀x1)(∃x2)(x2 + x1 = 0)	
(inverse)
	
d.	 (∀x1)(x1 = x1)	
(reflexivity of =)
	
e.	 (∀x1)(∀x2)(x1 = x2 ⇒ x2 = x1)	
(symmetry of =)
	
f.	 (∀x1)(∀x2)(∀x3)(x1 = x2 ∧ x2 = x3 ⇒ x1 = x3)	
(transitivity of =)
	
g.	 (∀x1)(∀x2)(∀x3)(x2 = x3 ⇒ x1 + x2 	
(substitutivity of =)
	
	
= x1 + x3 ∧ x2 + x1 = x3 + x1)
A model for this theory, in which the interpretation of = is the identity rela-
tion, is called a group. A group is said to be abelian if, in addition, the wf (∀x1)
(∀x2)(x1 + x2 = x2 + x1) is true.
*	 Such a sequence would satisfy A x
1
1
1
(
), since s1 is even, but would not satisfy (
)
(
)
∀x A x
1
1
1
1 , since 
no sequence satisfies (
)
(
).
∀x A x
1
1
1
1



69
First-Order Logic and Model Theory
The theories of partial order and of groups are both axiomatic. In general, 
any theory with a finite number of proper axioms is axiomatic, since it is 
obvious that one can effectively decide whether any given wf is a logical 
axiom.
2.4  Properties of First-Order Theories
All the results in this section refer to an arbitrary first-order theory K. Instead 
of writing ⊢K B, we shall sometimes simply write ⊢ B. Moreover, we shall 
refer to first-order theories simply as theories, unless something is said to the 
contrary.
Proposition 2.1
Every wf B of K that is an instance of a tautology is a theorem of K, and it 
may be proved using only axioms (A1)–(A3) and MP.
Proof
B arises from a tautology S by substitution. By Proposition 1.14, there is a 
proof of S in L. In such a proof, make the same substitution of wfs of K for 
statement letters as were used in obtaining B from S, and, for all statement 
letters in the proof that do not occur in S, substitute an arbitrary wf of K. 
Then the resulting sequence of wfs is a proof of B, and this proof uses only 
axiom schemes (A1)–(A3) and MP.
The application of Proposition 2.1 in a proof will be indicated by writing 
“Tautology.”
Proposition 2.2
Every theorem of a first-order predicate calculus is logically valid.
Proof
Axioms (A1)–(A3) are logically valid by property (VII) of the notion of truth 
(see page 58), and axioms (A4) and (A5) are logically valid by properties (X) 
and (XI). By properties (III) and (VI), the rules of inference MP and Gen pre-
serve logical validity. Hence, every theorem of a predicate calculus is logi-
cally valid.



70
Introduction to Mathematical Logic
Example
The wf (
)(
)
(
,
)
(
)(
)
(
,
)
∀
∃
⇒∃
∀
x
x A x x
x
x A x x
2
1
1
2
1
2
1
2
1
2
1
2  is not a theorem of any first-
order predicate calculus, since it is not logically valid (by Example 5, page 63).
Definition
A theory K is consistent if no wf B and its negation ¬B are both provable in K. 
A theory is inconsistent if it is not consistent.
Corollary 2.3
Any first-order predicate calculus is consistent.
Proof
If a wf B and its negation ¬B were both theorems of a first-order predicate 
calculus, then, by Proposition 2.2, both B and ¬B would be logically valid, 
which is impossible.
Notice that, in an inconsistent theory K, every wf C of K is provable in K. In 
fact, assume that B and ¬B are both provable in K. Since the wf B ⇒ (¬B  ⇒ C) 
is an instance of a tautology, that wf is, by Proposition 2.1, provable in K. 
Then two applications of MP would yield ⊢C.
It follows from this remark that, if some wf of a theory K is not a theorem 
of K, then K is consistent.
The deduction theorem (Proposition 1.9) for the propositional calculus can-
not be carried over without modification to first-order theories. For example, 
for any wf B, B ⊢K(∀xi)B, but it is not always the case that ⊢K B ⇒ (∀xi)B. 
Consider a domain containing at least two elements c and d. Let K be a predi-
cate calculus and let B be A x
1
1
1
(
). Interpret A1
1 as a property that holds only 
for c. Then A x
1
1
1
(
) is satisfied by any sequence s = (s1, s2, …) in which s1 = c, 
but (
)
(
)
∀x A x
1
1
1
1  is satisfied by no sequence at all. Hence, A x
x A x
1
1
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
)
⇒∀
 
is not true in this interpretation, and so it is not logically valid. Therefore, by 
Proposition 2.2, A x
x A x
1
1
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
)
⇒∀
 is not a theorem of K.
A modified, but still useful, form of the deduction theorem may be derived, 
however. Let B be a wf in a set Γ of wfs and assume that we are given a 
deduction D1, …, Dn from Γ , together with justification for each step in the 
deduction. We shall say that Di depends upon B in this proof if and only if:
	
1.	Di is B and the justification for Di is that it belongs to Γ, or
	
2.	Di is justified as a direct consequence by MP or Gen of some preced-
ing wfs of the sequence, where at least one of these preceding wfs 
depends upon B.



71
First-Order Logic and Model Theory
Example
B, (∀x1)B ⇒ C ⊢ (∀x1)C
(D1)
B
Hyp
(D2)
(∀x1) B
(D1), Gen
(D3)
(∀x1) B ⇒ C
Hyp
(D4)
C
(D2), (D3), MP
(D5)
(∀x1)C
(D4), Gen
Here, (D1) depends upon B, (D2) depends upon B, (D3) depends upon (∀x1)
B ⇒ C, (D4) depends upon B and (∀x1)B ⇒ C, and (D5) depends upon B and 
(∀x1)B ⇒ C.
Proposition 2.4
If C does not depend upon B in a deduction showing that Γ, B ⊢ C, then Γ ⊢ C.
Proof
Let D1 …, Dn be a deduction of C  from Γ and B, in which C  does not depend 
upon B. (In this deduction, Dn is C.) As an inductive hypothesis, let us 
assume that the proposition is true for all deductions of length less than n. If 
C  belongs to Γ or is an axiom, then Γ ⊢ C. If C  is a direct consequence of one 
or two preceding wfs by Gen or MP, then, since C  does not depend upon B, 
neither do these preceding wfs. By the inductive hypothesis, these preceding 
wfs are deducible from Γ alone. Consequently, so is C.
Proposition 2.5 (Deduction Theorem)
Assume that, in some deduction showing that Γ, B ⊢ C, no application of Gen 
to a wf that depends upon B has as its quantified variable a free variable 
of B. Then Γ ⊢ B ⇒ C.
Proof
Let D1, …, Dn be a deduction of C from Γ and B, satisfying the assumption of 
our proposition. (In this deduction, Dn is C.) Let us show by induction that Γ 
⊢ B ⇒ Di for each i ≤ n. If Di is an axiom or belongs to Γ, then Γ ⊢ B ⇒ Di, since 
Di ⇒ (B ⇒ Di) is an axiom. If Di is B, then Γ ⊢ B ⇒ Di, since, by Proposition 
2.1, ⊢ B ⇒ B. If there exist j and k less than i such that Dk is Dj ⇒ Di, then, by 
inductive hypothesis, Γ ⊢ B ⇒ Dj and Γ ⊢ B ⇒ (Dj ⇒ Di). Now, by axiom (A2), 
⊢ (B ⇒ (Dj ⇒ Di)) ⇒ ((B ⇒ Dj) ⇒ (B ⇒ Di)). Hence, by MP twice, Γ ⊢ B ⇒ Di. 
Finally, suppose that there is some j < i such that Di is (∀xk)Dj. By the inductive 



72
Introduction to Mathematical Logic
hypothesis, Γ ⊢ B ⇒ Dj, and, by the hypothesis of the theorem, either Dj does 
not depend upon B or xk is not a free variable of B. If Dj does not depend 
upon B, then, by Proposition 2.4, Γ ⊢ Dj and, consequently, by Gen, Γ ⊢ (∀xk)
Dj. Thus, Γ ⊢ Di. Now, by axiom (A1), ⊢ Di ⇒ (B ⇒ Di). So, Γ ⊢ B ⇒ Di by MP. If, 
on the other hand, xk is not a free variable of B, then, by axiom (A5), ⊢ (∀xk)
(B  ⇒ Dj) ⇒ (B ⇒ (∀xk)Dj). Since Γ ⊢ B ⇒ Dj, we have, by Gen, Γ ⊢ (∀xk)(B ⇒ Dj), 
and so, by MP, Γ ⊢ B ⇒ (∀xk)Dj; that is, Γ ⊢ B ⇒ Di. This completes the induc-
tion, and our proposition is just the special case i = n.
The hypothesis of Proposition 2.5 is rather cumbersome; the following 
weaker corollaries often prove to be more useful.
Corollary 2.6
If a deduction showing that Γ, B ⊢ C involves no application of Gen of which 
the quantified variables is free in B, then Γ ⊢ B ⇒ C.
Corollary 2.7
If B is a closed wf and Γ, B ⊢ C, then Γ ⊢ B ⇒ C.
Extension of Propositions 2.4–2.7
In Propositions 2.4–2.7, the following additional conclusion can be drawn from 
the proofs. The new proof of Γ ⊢ B ⇒ C (in Proposition 2.4, of Γ ⊢ C) involves 
an application of Gen to a wf depending upon a wf E of Γ only if there is an 
application of Gen in the given proof of Γ, B ⊢ C that involves the same quan-
tified variable and is applied to a wf that depends upon E. (In the proof of 
Proposition 2.5, one should observe that Dj depends upon a premiss E of Γ in 
the original proof if and only if B ⇒ Dj depends upon E in the new proof.)
This supplementary conclusion will be useful when we wish to apply the 
deduction theorem several times in a row to a given deduction—for example, 
to obtain Γ ⊢ D ⇒ (B ⇒ C) from Γ, D, B ⊢ C; from now on, it is to be considered 
an integral part of the statements of Propositions 2.4–2.7.
Example
	
⊢(
)(
)
(
)(
)
∀
∀
⇒∀
∀
x
x
x
x
1
2
2
1
B
B
Proof
	
1.	(∀x1)(∀x2)B	
Hyp
	
2.	(∀x1)(∀x2)B ⇒(∀x2)B	
(A4)



73
First-Order Logic and Model Theory
	
3.	(∀x2)B	
1, 2, MP
	
4.	(∀x2)B ⇒ B	
(A4)
	
5.	B	
3, 4, MP
	
6.	(∀x1)B	
5, Gen
	
7.	(∀x2)(∀x1)B	
6, Gen
Thus, by 1–7, we have (∀x1)(∀x2)B ⊢ (∀x2)(∀x1)B, where, in the deduction, no 
application of Gen has as a quantified variable a free variable of (∀x1)(∀x2)B. 
Hence, by Corollary 2.6, ⊢ (∀x1)(∀x2)B ⇒ (∀x2)(∀x1)B.
Exercises
2.27	
Derive the following theorems.
	
a.	 ⊢ (∀x)(B ⇒ C) ⇒ ((∀x)B ⇒ (∀x)C)
	
b.	 ⊢ (∀x)(B ⇒ C) ⇒ ((∃x)B ⇒ (∃x)C)
	
c.	 ⊢ (∀x)(B ∧ C) ⇔ (∀x)B) ∧ (∀x)C
	
d.	 ⊢ (∀y1) … (∀yn)B ⇒ B
	
e.	 ⊢ ¬(∀x)B ⇒ (∃x) ¬B
2.28D	 Let K be a first-order theory and let K# be an axiomatic theory having 
the following axioms:
	
a.	 (∀y1) … (∀yn)B, where B is any axiom of K and y1, …, yn(n ≥ 0) are 
any variables (none at all when n = 0);
	
b.	 (∀y1) … (∀yn)(B ⇒ C) ⇒ [(∀y1) … (∀yn)B ⇒ (∀y1) … (∀yn)C ] where B 
and C are any wfs and y1 …, yn are any variables.
	
Moreover, K# has modus ponens as its only rule of inference. Show 
that K# has the same theorems as K. Thus, at the expense of adding 
more axioms, the generalization rule can be dispensed with.
2.29	
Carry out the proof of the Extension of Propositions 2.4–2.7 above.
2.5  Additional Metatheorems and Derived Rules
For the sake of smoothness in working with particular theories later, we 
shall introduce various techniques for constructing proofs. In this section it 
is assumed that we are dealing with an arbitrary theory K.
Often one wants to obtain B(t) from (∀x)B(x), where t is a term free for x in 
B(x). This is allowed by the following derived rule.



74
Introduction to Mathematical Logic
2.5.1  Particularization Rule A4
If t is free for x in B(x), then (∀x)B(x) ⊢ B(t).*
Proof
From (∀x)B(x) and the instance (∀x)B(x) ⇒ B(t) of axiom (A4), we obtain B(t) 
by modus ponens.
Since x is free for x in B(x), a special case of rule A4 is: (∀x)B ⊢ B.
There is another very useful derived rule, which is essentially the contra-
positive of rule A4.
2.5.2  Existential Rule E4
Let t be a term that is free for x in a wf B(x, t), and let B(t, t) arise from B(x, t) by 
replacing all free occurrences of x by t. (B(x, t) may or may not contain occur-
rences of t.) Then, B(t, t) ⊢ (∃x)B(x, t)
Proof
It suffices to show that ⊢B(t, t) ⇒ (∃x)B(x, t). But, by axiom (A4), ⊢(∀x)¬B(x, t) 
⇒ ¬B(t, t). Hence, by the tautology (A ⇒ ¬B) ⇒ (B ⇒ ¬A) and MP, ⊢B(t, t) ⇒ 
¬(∀x)¬B(x, t), which, in abbreviated form, is ⊢ B(t, t) ⇒ (∃x)B(x, t).
A special case of rule E4 is B(t) ⊢ (∃x)B(x), whenever t is free for x in B(x). 
In particular, when t is x itself, B(x) ⊢ (∃x)B(x).
Example
⊢ (∀x)B ⇒ (∃x)B
	
1.	(∀x)B	
Hyp
	
2.	B	
1, rule A4
	
3.	(∃x)B	
2, rule E4
	
4.	(∀x)B ⊢ (∃x)B	
1–3
	
5.	⊢ (∀x)B ⇒ (∃x)B	
1–4, Corollary 2.6
The following derived rules are extremely useful.
Negation elimination:
¬¬B ⊢ B
Negation introduction:
B ⊢ ¬¬B
Conjunction elimination:
B ∧ C ⊢ B
B ∧ C ⊢ C
¬(B ∧ C) ⊢ ¬B ∨ ¬C
*	 From a strict point of view, (∀x)B(x) ⊢ B(t) states a fact about derivability. Rule A4 should be 
taken to mean that, if (∀x)B(x) occurs as a step in a proof, we may write B(t) as a later step 
(if t is free for x in B(x)). As in this case, we shall often state a derived rule in the form of the 
corresponding derivability result that justifies the rule.



75
First-Order Logic and Model Theory
Conjunction introduction:
B, C ⊢ B ∧ C
Disjunction elimination:
B ∨ C, ¬B ⊢ C
B ∨ C, ¬C ⊢ B
¬(B ∨ C) ⊢ ¬B ∧ ¬C
B ⇒ D, C ⇒ D, B ∨ C ⊢ D
Disjunction introduction:
B ⊢ B ∨ C
C ⊢ B ∨ C
Conditional elimination:
B ⇒ C, ¬C ⊢ ¬B
B ⇒ ¬C, C ⊢ ¬B
¬B ⇒ C, ¬C ⊢ B
¬B ⇒ ¬C, C ⊢ B
¬(B ⇒ C) ⊢ B
¬(B ⇒ C) ⊢ ¬C
Conditional introduction:
B, ¬C ⊢ ¬(B ⇒ C)
Conditional contrapositive:
B ⇒ C ⊢ ¬C ⇒ ¬B
¬C ⇒ ¬B ⊢ B ⇒ C
Biconditional elimination:
B ⇔ C, B ⊢ C B ⇔ C, ¬B ⊢ ¬C
B ⇔ C, C ⊢ B B ⇔ C, ¬C ⊢ ¬B
B ⇔ C ⊢ B ⇒ C B ⇔ C ⊢ C ⇒ B
Biconditional introduction:
B ⇒ C, C ⇒ B ⊢ B ⇔ C
Biconditional negation:
B ⇔ C ⊢ ¬B ⇔ ¬C
¬B ⇔ ¬C ⊢ B ⇔ C
Proof by contradiction: If a proof of Γ, ¬B ⊢ C ∧ ¬C involves no application 
of Gen using a variable free in B, then Γ ⊢B. (Similarly, one obtains Γ ⊢ ¬B 
from Γ, B ⊢C ∧ ¬C.)
Exercises
2.30	 Justify the derived rules listed above.
2.31	 Prove the following.
	
a.	 ⊢(
)(
)
( , )
(
)
( , )
∀
∀
⇒∀
x
y A x y
x A x x
1
2
1
2
	
b.	 ⊢ [(∀x)B] ∨ [(∀x)C] ⇒ (∀x)(B ∨ C)
	
c.	 ⊢ ¬(∃x)B ⇒ (∀x) ¬B
	
d.	 ⊢ (∀x)B ⇒ (∀x)(B ∨ C)
	
e.	 ⊢(
)(
)(
( , )
( , ))
(
)
( , )
∀
∀
⇒
⇒∀
x
y A x y
A y x
x
A x x
1
2
1
2
1
2
¬
¬
	
f.	 ⊢ [(∃x)B ⇒ (∀x)C] ⇒ (∀x)(B ⇒ C)
	
g.	 ⊢ (∀x)(B ∨ C) ⇒ [(∀x)B] ∨ (∃x)C
	
h.	 ⊢(
)(
( , )
(
)
( , ))
∀
⇒∃
x A x x
y A x y
1
2
1
2



76
Introduction to Mathematical Logic
	
i.	 ⊢ (∀x)(B ⇒ C) ⇒ [(∀x) ¬C ⇒ (∀x) ¬B]
	
j.	 ⊢(
)[
( )
(
)
( )]
∃
⇒∀
y A y
y A y
1
1
1
1
	
k.	 ⊢ [(∀x)(∀y)(B(x, y) ⇒ B(y, x)) ∧ (∀x)(∀y)(∀z)(B(x, y) ∧
	
B(y, z) ⇒ B(x, z))] ⇒ (∀x)(∀y)(B(x, y) ⇒ B(x, x))
	
l.	 ⊢(
)
( , )
(
)(
)
( , )
∃
⇒∃
∃
x A x x
x
y A x y
1
2
1
2
2.32	 Assume that B and C are wfs and that x is not free in B. Prove the 
following.
	
a.	 ⊢ B ⇒ (∀x)B
	
b.	 ⊢ (∃x)B ⇒ B
	
c.	 ⊢ (B ⇒ (∀x)C) ⇔ (∀x)(B ⇒ C)
	
d.	 ⊢ ((∃x)C ⇒ B) ⇔ (∀x)(C ⇒ B)
	
	   We need a derived rule that will allow us to replace a part C of a wf B 
by a wf that is provably equivalent to C. For this purpose, we first must 
prove the following auxiliary result.
Lemma 2.8
For any wfs B and C, ⊢ (∀x)(B ⇔ C) ⇒ ((∀x)B ⇔ (∀x)C).
Proof
	
1.	(∀x)(B ⇔ C)	
Hyp
	
2.	(∀x)B	
Hyp
	
3.	B ⇔ C	
1, rule A4
	
4.	B	
2, rule A4
	
5.	C	
3, 4, biconditional elimination
	
6.	(∀x)C	
5, Gen
	
7.	(∀x)(B ⇔ C), (∀x)B ⊢ (∀x)C	
1–6
	
8.	(∀x)(B ⇔ C) ⊢ (∀x)B ⇒ (∀x)C	
1–7, Corollary 2.6
	
9.	(∀x)(B ⇔ C) ⊢ (∀x)C ⇒ (∀x)B	
Proof like that of 8
	 10.	(∀x)(B ⇔ C) ⊢ (∀x)B ⇔ (∀x)C	
8, 9, Biconditional introduction
	 11.	⊢ (∀x)(B ⇔ C) ⇒ ((∀x)B ⇔ (∀x)C)	
1–10, Corollary 2.6
Proposition 2.9
If C is a subformula of B, B ′ is the result of replacing zero or more occur-
rences of C in B by a wf D, and every free variable of C or D that is also a 
bound variable of B occurs in the list y1, …, yk, then:
	
a.	⊢ [(∀y1) … (∀yk)(C ⇔ D)] ⇒ (B ⇔ B ′) (Equivalence theorem)
	
b.	If ⊢ C ⇔ D, then ⊢ B ⇔ B ′ (Replacement theorem)
	
c.	If ⊢ C ⇔ D and ⊢ B, then ⊢ B ′



77
First-Order Logic and Model Theory
Example
	
a.	⊢(
)(
( )
( ))
[(
)
( )
(
)
( )]
∀
⇔
⇒
∃
⇔∃
x A x
A x
x A x
x A x
1
1
2
1
1
1
2
1
Proof
	
a.	We use induction on the number of connectives and quantifiers in B. 
Note that, if zero occurrences are replaced, B ′ is B and the wf to be 
proved is an instance of the tautology A ⇒ (B ⇔ B). Note also that, if C 
is identical with B and this occurrence of C  is replaced by D, the wf to 
be proved, [(∀y1) … (∀yk)(C ⇔ D)] ⇒ (B ⇔ B ′), is derivable by Exercise 
2.27(d). Thus, we may assume that C is a proper part of B and that at 
least one occurrence of C is replaced. Our inductive hypothesis is that the 
result holds for all wfs with fewer connectives and quantifiers than B.
	
	 Case 1. B is an atomic wf. Then C cannot be a proper part of B.
	
	 Case 2. B is ¬E. Let B ′ be ¬E ′. By inductive hypothesis, ⊢ [(∀y1) … (∀yk) 
(C ⇔ D)] ⇒ (E ⇔ E ′). Hence, by a suitable instance of the tautology (C ⇒ 
(A ⇔ B)) ⇒ (C ⇒ (¬A ⇔ ¬B)) and MP, we obtain ⊢ [(∀y1) … (∀yk)(C ⇔ D)] 
⇒ (B ⇔ B ′).
	
	 Case 3. B is E ⇒ F. Let B ′ be E ′ ⇒ F ′. By inductive hypothesis, ⊢ [(∀y1) … 
(∀yk)(C ⇔ D)] ⇒ (E ⇔ E ′) and ⊢ [(∀y1) … (∀yk)(C ⇔ D)] ⇒ (F ⇔ F ′). Using a 
suitable instance of the tautology
	
(
(
))
(
(
))
(
[(
)
(
)])
A
B
C
A
D
E
A
B
D
C
E
⇒
⇔
∧
⇒
⇔
⇒
⇒
⇒
⇔
⇒
	
	 we obtain ⊢ [(∀y1) … (∀yk)(C ⇔ D)] ⇒ (B ⇔ B ′).
	
	 Case 4. B is (∀x)E. Let B ′ be (∀x)E ′. By inductive hypothesis, ⊢ [(∀y1) … 
(∀yk) (C ⇔ D)] ⇒ (E ⇔ E ′). Now, x does not occur free in (∀y1) … (∀yk)
(C ⇔ D) because, if it did, it would be free in C or D and, since it is 
bound in B, it would be one of y1, …, yk and it would not be free in 
(∀y1) … (∀yk)(C ⇔ D). Hence, using axiom (A5), we obtain ⊢ (∀y1) … 
(∀yk)(C ⇔ D) ⇒ (∀x)(E ⇔ E ′). However, by Lemma 2.8, ⊢ (∀x)(E ⇔ E) ⇒ 
((∀x)E ⇔ (∀x)E ′). Then, by a suitable tautology and MP, ⊢ [(∀y1) … (∀yk)
(C ⇔ D)] ⇒ (B ⇔ B ′).
	
b.	From ⊢ C ⇔ D, by several applications of Gen, we obtain ⊢ (∀y1) … (∀yk)
(C ⇔ D). Then, by (a) and MP, ⊢ B ⇔ B ′.
	
c.	Use part (b) and biconditional elimination.
Exercises
2.33	 Prove the following:
	
a.	 ⊢ (∃x) ¬B ⇔ ¬(∀x)B
	
b.	 ⊢ (∀x)B ⇔ ¬(∃x) ¬B
	
c.	 ⊢ (∃x)(B ⇒ ¬(C ∨ D)) ⇒ (∃x)(B ⇒ ¬C ∧ ¬D)



78
Introduction to Mathematical Logic
	
d.	 ⊢ (∀x)(∃y)(B ⇒ C) ⇔ (∀x)(∃y)(¬B ∨ C)
	
e.	 ⊢ (∀x)(B ⇒ ¬C) ⇔ ¬(∃x)(B ∧ C)
2.34	 Show by a counterexample that we cannot omit the quantifiers (∀y1) … 
(∀yk) in Proposition 2.9(a).
2.35	 If C is obtained from B by erasing all quantifiers (∀x) or (∃x) whose 
scope does not contain x free, prove that ⊢ B ⇔ C.
2.36	 For each wf B below, find a wf C such that ⊢ C ⇔ ¬B and negation signs 
in C apply only to atomic wfs.
	
a.	 (
)(
)(
)
( , , )
∀
∀
∃
x
y
z A x y z
1
3
	
b.	 (∀ε)(ε > 0 ⇒ (∃δ)(δ > 0 ∧ (∀x)(|x − c| < δ ⇒ |f(x) − f(c) | < ε))
	
c.	 (∀ε)(ε > 0 ⇒ (∃n)(∀m)(m > n ⇒ |am − b| < ε))
2.37	 Let B be a wf that does not contain ⇒ and ⇔. Exchange universal and 
existential quantifiers and exchange ∧ and ∨. The result B* is called the 
dual of B.
	
a.	 In any predicate calculus, prove the following.
	
i.	 ⊢ B if and only if ⊢ ¬B*
	
ii. ⊢ B ⇒ C if and only if ⊢ C * ⇒ B*
	
iii. ⊢ B ⇔ C if and only if ⊢ B * ⇔ C *
	
iv.	  ⊢ (∃x)(B ∨ C) ⇔ [((∃x)B) ∨ (∃x)C]. [Hint: Use Exercise 2.27(c).]
	
b.	 Show that the duality results of part (a), (i)–(iii), do not hold for arbi-
trary theories.
2.6  Rule C
It is very common in mathematics to reason in the following way. Assume 
that we have proved a wf of the form (∃x)B(x). Then we say, let b be an object 
such that B(b). We continue the proof, finally arriving at a formula that does 
not involve the arbitrarily chosen element b.
For example, let us say that we wish to show that (∃x)(B (x) ⇒ C (x)), 
(∀x)B (x) ⊢ (∃x)C (x).
	
1.	(∃x)(B (x) ⇒ C (x))	
Hyp
	
2.	(∀x)B (x)	
Hyp
	
3.	B (b) ⇒ C (b) for some b	
1
	
4.	B (b)	
2, rule A4
	
5.	C (b)	
3, 4, MP
	
6.	(∃x)C (x)	
5, rule E4



79
First-Order Logic and Model Theory
Such a proof seems to be perfectly legitimate on an intuitive basis. In fact, 
we can achieve the same result without making an arbitrary choice of an ele-
ment b as in step 3. This can be done as follows:
	
1.	(∀x)B (x)	
Hyp
	
2.	(∀x) ¬C (x)	
Hyp
	
3.	B (x)	
1, rule A4
	
4.	¬C (x)	
2, rule A4
	
5.	¬(B (x) ⇒ C (x))	
3, 4, conditional introduction
	
6.	(∀x) ¬(B (x) ⇒ C (x))	
5, Gen
	
7.	(∀x)B (x), (∀x) ¬C (x) 	
1–6
	
	 ⊢ (∀x) ¬(B (x) ⇒ C (x))
	
8.	(∀x)B (x) ⊢ (∀x) ¬C (x) ⇒	
1–7, corollary 2.6
	
	  (∀x) ¬(B (x) ⇒ C (x))
	
9.	(∀x)B (x) ⊢ ¬(∀x) ¬(B (x) ⇒	
8, contrapositive
	
	 C (x)) ⇒ ¬(∀x) ¬C (x)
	 10.	(∀x)B (x) ⊢ (∃x)(B (x) ⇒	
Abbreviation of 9
	
	 C (x)) ⇒ (∃x)C (x)
	 11.	(∃x)(B (x) ⇒ C (x)),	
10, MP
	
	 (∀x)B (x) ⊢ (∃x)C (x)
In general, any wf that can be proved using a finite number of arbitrary 
choices can also be proved without such acts of choice. We shall call the rule 
that permits us to go from (∃x)B (x) to B (b), rule C (“C” for “choice”). More 
precisely, a rule C deduction in a first-order theory K is defined in the follow-
ing manner: Γ ⊢C B if and only if there is a sequence of wfs D1, …, Dn such that 
Dn is B and the following four conditions hold:
	
1.	For each i < n, either
	
a.	 Di is an axiom of K, or
	
b.	 Di is in Γ, or
	
c.	 Di follows by MP or Gen from preceding wfs in the sequence, or
	
d.	 there is a preceding wf (∃x)C (x) such that Di is C (d), where d is a 
new individual constant (rule C).
	
2.	As axioms in condition 1(a), we also can use all logical axioms that 
involve the new individual constants already introduced in the 
sequence by applications of rule C.



80
Introduction to Mathematical Logic
	
3.	No application of Gen is made using a variable that is free in some 
(∃x)C (x) to which rule C has been previously applied.
	
4.	B contains none of the new individual constants introduced in the 
sequence in any application of rule C.
A word should be said about the reason for including condition 3. If an appli-
cation of rule C to a wf (∃x)C (x) yields C (d), then the object referred to by d 
may depend on the values of the free variables in (∃x)C (x). So that one object 
may not satisfy C (x) for all values of the free variables in (∃x)C (x). For exam-
ple, without clause 3, we could proceed as follows:
	
1.	(
)(
)
( , )
∀
∃
x
y A x y
1
2
	
Hyp
	
2.	(
)
( , )
∃y A x y
1
2
	
1, rule A4
	
3.	A x d
1
2( , ) 	
2, rule C
	
4.	(
)
( , )
∀x A x d
1
2
	
3, Gen
	
5.	(
)(
)
( , )
∃
∀
y
x A x y
1
2
	
4, rule E4
However, there is an interpretation for which (
)(
)
( , )
∀
∃
x
y A x y
1
2
 is true but 
(
)(
)
( , )
∃
∀
y
x A x y
1
2
 is false. Take the domain to be the set of integers and let 
A x y
1
2( , ) mean that x < y.
Proposition 2.10
If Γ ⊢C B, then Γ ⊢ B. Moreover, from the following proof it is easy to verify 
that, if there is an application of Gen in the new proof of B from Γ using a 
certain variable and applied to a wf depending upon a certain wf of Γ, then 
there was such an application of Gen in the original proof.*
Proof
Let (∃y1)C1(y1), …, (∃yk)Ck(yk) be the wfs in order of occurrence to which rule C 
is applied in the proof of Γ ⊢C B, and let d1, …, dk be the corresponding new 
­individual constants. Then Γ, C1(d1), …, Ck(dk) ⊢ B. Now, by condition 3 of the 
definition above, Corollary 2.6 is applicable, yielding Γ, C1(d1), …, Ck−1(dk−1) ⊢ 
Ck(dk) ⇒ B. We replace dk everywhere by a variable z that does not occur in 
the proof.
Then
	
Γ,
(
),
,
(
)
( )
C
C
C
B
1
1
1
1
d
d
z
k
k
k
…
⇒
−
−
⊢
*	 The first formulation of a version of rule C similar to that given here seems to be due to Rosser 
(1953).



81
First-Order Logic and Model Theory
and, by Gen,
	
Γ,
(
),
,
(
)
(
)(
( )
)
C
C
C
B
1
1
1
1
d
d
z
z
k
k
k
…
∀
⇒
−
−
⊢
Hence, by Exercise 2.32(d),
	
Γ,
(
),
,
(
)
(
) (
)
C
C
C
B
1
1
1
1
d
d
y
y
k
k
k
k
k
…
∃
⇒
−
−
⊢
But,
	
Γ,
(
),
,
(
)
(
) (
)
C
C
C
1
1
1
1
d
d
y
y
k
k
k
k
k
…
∃
−
−
⊢
Hence, by MP,
	
Γ,
(
),
,
(
)
C
C
B
1
1
1
1
d
d
k
k
…
−
−
⊢
Repeating this argument, we can eliminate Ck−1(dk−1), …, C1(d1) one after the 
other, finally obtaining Γ ⊢ B.
Example
	
⊢(
)(
( )
( ))
((
)
( )
(
) ( ))
∀
⇒
⇒
∃
⇒∃
x
x
x
x
x
x
x
B
C
B
C
	
1.	(∀x)((B x) ⇒ C (x))	
Hyp
	
2.	(∃x)B (x)	
Hyp
	
3.	B (d)	
2, rule C
	
4.	B (d) ⇒ C (d)	
1, rule A4
	
5.	C (d)	
3, 4, MP
	
6.	(∃x)C (x)	
5, rule E4
	
7.	(∀x)(B (x) ⇒ C (x)), (∃x)B (x) ⊢C (∃x)C (x)	
1–6
	
8.	(∀x)(B (x) ⇒ C (x)), (∃x)B (x) ⊢ (∃x)C (x)	
7, Proposition 2.10
	
9.	(∀x)(B (x) ⇒ C (x)) ⊢ (∃x)B (x) ⇒ (∃x)C (x)	
1–8, corollary 2.6
	 10.	⊢ (∀x)(B (x) ⇒ C (x)) ⇒ ((∃x)B (x) ⇒ (∃x)C (x))	 1–9, corollary 2.6
Exercises
Use rule C and Proposition 2.10 to prove Exercises 2.38–2.45.
2.38	 ⊢ (∃x)(B (x) ⇒ C (x)) ⇒ ((∀x)B (x) ⇒ (∃x)C (x))



82
Introduction to Mathematical Logic
2.39	 ⊢¬
¬
(
)(
)(
( , )
( , ))
∃
∀
⇔
y
x A x y
A x x
1
2
1
2
2.40	 ⊢[(
)(
( )
( )
( ))
(
)(
( )
( ))]
(
)(
∀
⇒
∨
∧
∀
⇒
⇒∃
x A x
A x
A x
x A x
A x
x A
1
1
2
1
3
1
1
1
2
1
1
¬
1( )
x ∧ 
A x
3
1( ))
2.41	 ⊢ [(∃x)B (x)] ∧ [(∀x)C (x)] ⇒ (∃x)(B (x) ∧ C (x))
2.42	 ⊢ (∃x)C (x) ⇒ (∃x)(B (x) ∨ C (x))
2.43	 ⊢ (∃x)(∃y)B (x, y) ⇔ (∃y)(∃x)B (x, y)
2.44	 ⊢ (∃x)(∀y)B (x, y) ⇒ (∀y)(∃x)B (x, y)
2.45	 ⊢ (∃x)(B (x) ∧ C (x)) ⇒ ((∃x)B (x)) ∧ (∃x)C (x)
2.46	 What is wrong with the following alleged derivations?
	
a.	 1.	 (∃x)B (x)	
Hyp
	
2.	 B (d)	
1, rule C
	
3.	 (∃x)C (x)	
Hyp
	
4.	 C (d)	
3, rule C
	
5.	 B (d) ∧ C (d)	
2, 4, conjunction introduction
	
6.	 (∃x)(B (x) ∧ C (x))	
5, rule E4
	
7.	 (∃x)B (x), (∃x)C (x) 	
1–6, Proposition 2.10
	
	 ⊢ (∃x)(B (x) ∧ C (x))
	
b.	 1.	 (∃x)(B (x) ⇒ C (x))	
Hyp
	
2.	 (∃x)B (x)	
Hyp
	
3.	 B (d) ⇒ C (d)	
1, rule C
	
4.	 B (d)	
2, rule C
	
5.	 C (d)	
3, 4, MP
	
6.	 (∃x)C (x)	
5, rule E4
	
7.	 (∃x)(B (x) ⇒ C (x)),	
1–6, Proposition 2.10
	
	 (∃x)B (x) ⊢ (∃x)C (x)
2.7  Completeness Theorems
We intend to show that the theorems of a first-order predicate calculus K are 
precisely the same as the logically valid wfs of K. Half of this result was proved 
in Proposition 2.2. The other half will follow from a much more general prop-
osition established later. First we must prove a few preliminary lemmas.
If xi and xj are distinct, then B(xi) and B(xj) are said to be similar if and only 
if xj is free for xi in B(xi) and B(xi) has no free occurrences of xj. It is assumed 
here that B(xj) arises from B(xi) by substituting xj for all free occurrences 
of xi. It is easy to see that, if B(xi) and B(xj) are similar, then xi is free for xj in 



83
First-Order Logic and Model Theory
B(xj) and B(xj) has no free occurrences of xi. Thus, if B(xi) and B(xj) are simi-
lar, then B(xj) and B(xi) are similar. Intuitively, B(xi) and B(xj) are similar if 
and only if B(xi) and B(xj) are the same except that B(xi) has free occurrences 
of xi in exactly those places where B(xj) has free occurrences of xj.
Example
	
(
)
(
,
)
(
(
[
(
,
)
(
)
)
∀
∨


∀
∨


x
A x x
A x
x
A x
x
A x
3
1
2
1
3
1
1
1
3
1
2
2
3
1
1
2
and
are similar.
Lemma 2.11
If B (xi) and B (xj) are similar, then ⊢ (∀xi)B (xi) ⇔ (∀xj)B (xj).
Proof
⊢ (∀xi)B (xi) ⇒ B (xj) by axiom (A4). Then, by Gen, ⊢ (∀xj)((∀xi)B (xi) ⇒ B (xj)), 
and so, by axiom (A5) and MP, ⊢ (∀xi)B (xi) ⇒ (∀xj)B(xj). Similarly, ⊢ (∀xj) B (xj) 
⇒ (∀xi)B (xi). Hence, by biconditional introduction, ⊢ (∀xi)B (xi) ⇔ (∀xj)B (xj).
Exercises
2.47	 If B (xi) and B (xj) are similar, prove that ⊢ (∃xi)B (xi) ⇔ (∃xj)B (xj).
2.48	 Change of bound variables. If B (x) is similar to B (y), (∀x)B (x) is a subfor-
mula of C, and C ′ is the result of replacing one or more occurrences of 
(∀x)B (x) in C by (∀y)B (y), prove that ⊢ C ⇔ C ′.
Lemma 2.12
If a closed wf ¬B of a theory K is not provable in K, and if K′ is the theory 
obtained from K by adding B as a new axiom, then K′ is consistent.
Proof
Assume K′ inconsistent. Then, for some wf C, ⊢K′ C and ⊢K′ ¬C. Now, ⊢K′ C ⇒ 
(¬C ⇒ ¬B) by Proposition 2.1. So, by two applications of MP, ⊢K′ ¬B. Now, 
any use of B as an axiom in a proof in K′ can be regarded as a hypothesis 
in a proof in K. Hence, B ⊢K ¬B. Since B is closed, we have ⊢K B ⇒ ¬B by 
Corollary 2.7. However, by Proposition 2.1, ⊢K(B ⇒ ¬B) ⇒ ¬B. Therefore, by 
MP, ⊢K ¬B, contradicting our hypothesis.
Corollary
If a closed wf B of a theory K is not provable in K, and if K′ is the theory 
obtained from K by adding ¬B as a new axiom, then K′ is consistent.



84
Introduction to Mathematical Logic
Lemma 2.13
The set of expressions of a language L is denumerable. Hence, the same is 
true of the set of terms, the set of wfs and the set of closed wfs.
Proof
First assign a distinct positive integer g(u) to each symbol u as follows: 
g(() = 3, g()) = 5, g(,) = 7, g(¬) = 9, g(⇒) = 11, g(∀) = 13, g(xk) = 13 + 8k, g(ak) = 7 + 
8k, g fk
n
n
k
(
)
(
)
=
+
1
8 2 3
, and g Ak
n
n
k
(
)
(
)
=
+
3
8 2 3
. Then, to an expression u0u1 … 
ur associate the number 2
3
0
1
g u
g u
r
g u
p
r
(
)
(
)
(
)
…
, where pj is the jth prime number, 
starting with p0 = 2. (Example: the number of A x
1
1
2
(
) is 2513352975.) We can enu-
merate all expressions in the order of their associated numbers; so, the set of 
expressions is denumerable.
If we can effectively tell whether any given symbol is a symbol of L, then this 
enumeration can be effectively carried out, and, in addition, we can effectively 
decide whether any given number is the number of an expression of L. The 
same holds true for terms, wfs and closed wfs. If a theory K in the language L  is 
axiomatic, that is, if we can effectively decide whether any given wf is an axiom 
of K, then we can effectively enumerate the theorems of K in the following man-
ner. Starting with a list consisting of the first axiom of K in the enumeration just 
specified, add to the list all the direct consequences of this axiom by MP and by 
Gen used only once and with x1 as quantified variable. Add the second axiom to 
this new list and write all new direct consequences by MP and Gen of the wfs in 
this augmented list, with Gen used only once and with x1 and x2 as quantified 
variables. If at the kth step we add the kth axiom and apply MP and Gen to the 
wfs in the new list (with Gen applied only once for each of the variables x1, …, xk), 
we eventually obtain in this manner all theorems of K. However, in contradis-
tinction to the case of expressions, terms, wfs and closed wfs, it turns out that 
there are axiomatic theories K for which we cannot tell in advance whether any 
given wf of K will eventually appear in the list of theorems.
Definitions
	
i.	A theory K is said to be complete if, for every closed wf B of K, either 
⊢K B or ⊢K ¬B.
	
ii. A theory K′ is said to be an extension of a theory K if every theorem of K 
is a theorem of K′. (We also say in such a case that K is a subtheory of K′.)
Proposition 2.14 (Lindenbaum’s Lemma)
If K is a consistent theory, then there is a consistent, complete extension of K.



85
First-Order Logic and Model Theory
Proof
Let B1, B2, … be an enumeration of all closed wfs of the language of K, by 
Lemma 2.13. Define a sequence J0, J1, J2, … of theories in the following way. 
J0 is K. Assume Jn is defined, with n ≥ 0. If it is not the case that ⊢J
n
n ¬B +1, then 
let Jn+1 be obtained from Jn by adding Bn+1 as an additional axiom. On the other 
hand, if ⊢J
n
n ¬B +1, let Jn+1 = Jn. Let J be the theory obtained by taking as axioms 
all the axioms of all the Jis. Clearly, Ji+1 is an extension of Ji, and J is an exten-
sion of all the Jis, including J0 = K. To show that J is consistent, it suffices to 
prove that every Ji is consistent because a proof of a contradiction in J, involv-
ing as it does only a finite number of axioms, is also a proof of a contradiction 
in some Ji. We prove the consistency of the Jis, by induction. By hypothesis, 
J0 = K is consistent. Assume that Ji is consistent. If Ji+1 = Ji, then Ji+1 is consistent. 
If Ji ≠ Ji+1, and therefore, by the definition of Ji+1, ¬Bi+1 is not provable in Ji, then, 
by Lemma 2.12, Ji+1 is also consistent. So, we have proved that all the Jis are 
consistent and, therefore, that J is consistent. To prove the completeness of J, 
let  C   be any closed wf of K. Then C = Bj+1 for some j ≥ 0. Now, either ⊢J
j
j ¬B +1 or 
⊢J
j
j+
+
1
1
B
, since, if it is not the case that ⊢J
j
j ¬B +1, then Bj+1 is added as an axiom 
in Jj+1. Therefore, either ⊢J ¬Bj+1 or ⊢J Bj+1. Thus, J is complete.
Note that even if one can effectively determine whether any wf is an axiom 
of K, it may not be possible to do the same with (or even to enumerate effec-
tively) the axioms of J; that is, J may not be axiomatic even if K is. This is due 
to the possibility of not being able to determine, at each step, whether or not 
¬Bn+1 is provable in Jn.
Exercises
2.49	
Show that a theory K is complete if and only if, for any closed wfs B 
and C of K, if ⊢K B ∨ C, then ⊢K B or ⊢K C.
2.50D	 Prove that every consistent decidable theory has a consistent, decid-
able, complete extension.
Definitions
	
1.	A closed term is a term without variables.
	
2.	A theory K is a scapegoat theory* if, for any wf B (x) that has x as its 
only free variable, there is a closed term t such that
	
⊢K
x
x
t
(
)
( )
( )
∃
⇒
¬
¬
B
B
*	 If a scapegoat theory assumes that a given property B fails for at least one object, then there 
must be a name (that is, a suitable closed term t) of a specific object for which B provably fails. 
So, t would play the role of a scapegoat, in the usual meaning of that idea. Many theories lack 
the linguistic resources (individual constants and function letters) to be scapegoat theories, 
but the notion of scapegoat theory will be very useful in proving some deep properties of first-
order theories.



86
Introduction to Mathematical Logic
Lemma 2.15
Every consistent theory K has a consistent extension K′ such that K′ is a 
scapegoat theory and K′ contains denumerably many closed terms.
Proof
Add to the symbols of K a denumerable set {b1, b2, …} of new individual con-
stants. Call this new theory K0. Its axioms are those of K plus those logical 
axioms that involve the symbols of K and the new constants. K0 is consistent. 
For, if not, there is a proof in K0 of a wf B ∧ ¬B. Replace each bi appearing in 
this proof by a variable that does not appear in the proof. This transforms 
axioms into axioms and preserves the correctness of the applications of the 
rules of inference. The final wf in the proof is still a contradiction, but now 
the proof does not involve any of the bis and therefore is a proof in K. This 
contradicts the consistency of K. Hence, K0 is consistent.
By Lemma 2.13, let F x
F x
F x
i
i
k
ik
1
2
1
2
(
),
(
),
,
(
),
…
… be an enumeration of all wfs 
of K0 that have one free variable. Choose a sequence b
b
j
j
1
2
,
,… of some of the 
new individual constants such that each bjk is not contained in any of the 
wfs F x
F x
i
k
ik
1
1
(
),
,
(
)
…
 and such that bjk is different from each of b
b
j
jk
1
1
,
,
.
…
− 
Consider the wf
	
(
)
(
)
(
)
(
)
S
x
F x
F b
k
i
k
i
k
j
k
k
k
∃
¬
⇒¬
Let Kn be the theory obtained by adding (S1), …, (Sn) to the axioms of K0, 
and let K∞ be the theory obtained by adding all the (Si)s as axioms to K0. 
Any proof in K∞ contains only a finite number of the (Si)s and, therefore, 
will also be a proof in some Kn. Hence, if all the Kns are consistent, so is 
K∞. To demonstrate that all the Kns are consistent, proceed by induction. 
We know that K0 is consistent. Assume that Kn−1 is consistent but that Kn 
is inconsistent (n ≥ 1). Then, as we know, any wf is provable in Kn (by the 
tautology ¬A ⇒ (A ⇒ B), Proposition 2.1 and MP). In particular, ⊢K
n
n
S
¬(
). 
Hence, (
)
(
).
S
S
n
K
n
n
⊢
−1 ¬
 Since (Sn) is closed, we have, by Corollary 2.7, 
⊢K
n
n
n
S
S
−1 (
)
(
).
⇒¬
 But, by the tautology (A ⇒ ¬A) ⇒ ¬A, Proposition 2.1 and 
MP, we then have ⊢K
n
n
S
−1 ¬(
); that is, ⊢K
i
n
i
n
j
n
n
n
n
x
F x
F b
−1 ¬
¬
¬
[(
)
(
)
(
)]
∃
⇒
. Now, 
by conditional elimination, we obtain ⊢K
i
n
i
n
n
n
x
F x
−1 (
)
(
)
∃
¬
 and ⊢K
n
j
n
n
F b
−1 ¬¬
(
), 
and then, by negation elimination, ⊢K
n
j
n
n
F b
−1
(
). From the latter and the fact 
that bjn does not occur in (S0), …, (Sn−1), we conclude ⊢K
n
r
n
F x
−1
(
), where xr 
is a variable that does not occur in the proof of F b
n
jn
(
). (Simply replace in 
the proof all occurrences of bjn by xr.) By Gen, ⊢K
r
n
r
n
x F x
−1 (
)
(
)
∀
, and then, by 
Lemma 2.11 and biconditional elimination, ⊢K
i
n
i
n
n
n
x
F x
−1 (
)
(
)
∀
. (We use the 
fact that Fn(xr) and F x
n
in
(
) are similar.) But we already have ⊢K
i
n
i
n
n
n
x
F x
−1 (
)
(
),
∃
¬
 
which is an abbreviation of ⊢K
i
n
i
n
n
n
x
F x
−1 ¬
¬¬
(
)
(
)
∀
, whence, by the replace-
ment theorem, ⊢K
i
n
i
n
n
n
x
F x
−1 ¬(
)
(
),
∀
 contradicting the hypothesis that Kn−1 is 



87
First-Order Logic and Model Theory
consistent. Hence, Kn must also be consistent. Thus K∞ is consistent, it is 
an extension of K, and it is clearly a scapegoat theory.
Lemma 2.16
Let J be a consistent, complete scapegoat theory. Then J has a model M whose 
domain is the set D of closed terms of J.
Proof
For any individual constant ai of J, let (ai)M = ai. For any function letter fk
n 
of J and for any closed terms t1, …, tn of J, let (
) ( ,
,
)
( ,
,
)
f
t
t
f
t
t
k
n
n
k
n
n
M
1
1
…
=
…
. 
(Notice that f
t
t
k
n
n
( ,
,
)
1 …
 is a closed term. Hence, (
)
fk
n M is an n-ary operation 
on D.) For any predicate letter Ak
n of J, let (
)
Ak
n M consist of all n-tuples 〈t1, …, tn〉 
of closed terms t1, …, tn of J such that ⊢J
k
n
n
A t
t
( ,
,
)
1 …
. It now suffices to show 
that, for any closed wf C of J:
	
( )


⊢
M C
C
if and only if
J
(If this is established and B is any axiom of J, let C be the closure of B. By Gen, 
⊢J C. By (□), ⊧M C. By (VI) on page 58, ⊧M B. Hence, M would be a model of J.) 
The proof of (□) is by induction on the number r of connectives and quanti-
fiers in C. Assume that (□) holds for all closed wfs with fewer than r connec-
tives and quantifiers.
Case 1. C  is a closed atomic wf A t
t
k
n
n
( ,
,
)
1 …
. Then (□) is a direct consequence 
of the definition of (
)
Ak
n M.
Case 2. C is ¬D. If C is true for M, then D is false for M and so, by inductive 
hypothesis, not-⊢J D. Since J is complete and D is closed, ⊢J ¬D—that is, ⊢J C. 
Conversely, if C is not true for M, then D is true for M. Hence, ⊢J D. Since J is 
consistent, not-⊢J ¬D, that is, not-⊢J C.
Case 3. C is D ⇒ E. Since C is closed, so are D and E. If C is false for M, then D 
is true and E is false. Hence, by inductive hypothesis, ⊢J D and not-⊢J E. By 
the completeness of J, ⊢J ¬E. Therefore, by an instance of the tautology D ⇒ 
(¬E ⇒ ¬(D ⇒ E)) and two applications of MP, ⊢J ¬(D ⇒ E), that is, ⊢J ¬C, and 
so, by the consistency of J, not-⊢J C. Conversely, if not-⊢J C, then, by the com-
pleteness of J, ⊢J ¬C, that is, ⊢J ¬(D ⇒ E). By conditional elimination, ⊢J D and 
⊢J ¬E. Hence, by (□) for D, D is true for M. By the consistency of J, not-⊢J E 
and, therefore, by (□) for E, E is false for M. Thus, since D is true for M and E 
is false for M, C is false for M.
Case 4. C is (∀xm)D.
Case 4a. D is a closed wf. By inductive hypothesis, ⊧M D if and only if 
⊢J D. By Exercise 2.32(a), ⊢J D ⇔ (∀xm)D. So, ⊢J D  if and only if ⊢J(∀xm)D, by 



88
Introduction to Mathematical Logic
biconditional elimination. Moreover, ⊧M D if and only if ⊧M(∀xm)D by prop-
erty (VI) on page 58. Hence, ⊧M C if and only if ⊢J C.
Case 4b. D is not a closed wf. Since C is closed, D has xm as its only free vari-
able, say D is F(xm). Then C is (∀xm)F(xm).
	
i.	Assume ⊧M C and not-⊢J C. By the completeness of J, ⊢J ¬C, that is, 
⊢J ¬(∀xm)F(xm). Then, by Exercise 2.33(a) and biconditional elimina-
tion, ⊢J(∃xm) ¬F(xm). Since J is a scapegoat theory, ⊢J ¬F(t) for some 
closed term t of J. But ⊧M C, that is, ⊧M(∀xm)F(xm). Since (∀xm)F(xm) ⇒ F(t) 
is true for M by property (X) on page 59, ⊧MF(t). Hence, by (□) for F(t), 
⊢JF(t). This contradicts the consistency of J. Thus, if ⊧M C, then, ⊢J C.
	
ii. Assume ⊢J C and not-⊧M C. Thus,
	
(#)
(
) (
)
(##)
(
) (
).
⊢

J
and
∀
∀
x
F x
x
F x
m
m
M
m
m
not−
By (##), some sequence of elements of the domain D does not satisfy (∀xm)
F(xm). Hence, some sequence s does not satisfy F(xm). Let t be the ith compo-
nent of s. Notice that s*(u) = u for all closed terms u of J (by the definition of 
(ai)M and (
)
fk
n M). Observe also that F(t) has fewer connectives and quantifiers 
than C and, therefore, the inductive hypothesis applies to F(t), that is, (□) 
holds for F(t). Hence, by Lemma 2(a) on page 60, s does not satisfy F(t). So, F(t) 
is false for M. But, by (#) and rule A4, ⊢J F(t), and so, by (□) for F(t), ⊧M F(t). This 
contradiction shows that, if ⊢J C, then ⊧M C.
Now we can prove the fundamental theorem of quantification theory. By 
a denumerable model we mean a model in which the domain is denumerable.
Proposition 2.17*
Every consistent theory K has a denumerable model.
Proof
By Lemma 2.15, K has a consistent extension K′ such that K′ is a scapegoat 
theory and has denumerably many closed terms. By Lindenbaum’s lemma, 
K′ has a consistent, complete extension J that has the same symbols as K′. 
Hence, J is also a scapegoat theory. By Lemma 2.16, J has a model M whose 
domain is the denumerable set of closed terms of J. Since J is an extension of 
K, M is a denumerable model of K.
*	 The proof given here is essentially due to Henkin (1949), as simplified by Hasenjaeger (1953). 
The result was originally proved by Gödel (1930). Other proofs have been published by 
Rasiowa and Sikorski (1951, 1952) and Beth (1951), using (Boolean) algebraic and topologi-
cal methods, respectively. Still other proofs may be found in Hintikka (1955a,b) and in Beth 
(1959).



89
First-Order Logic and Model Theory
Corollary 2.18
Any logically valid wf B of a theory K is a theorem of K.
Proof
We need consider only closed wfs B, since a wf D is logically valid if and only 
if its closure is logically valid, and D is provable in K if and only if its closure 
is provable in K. So, let B be a logically valid closed wf of K. Assume that 
not-⊢K B. By Lemma 2.12, if we add ¬B as a new axiom to K, the new theory 
K′ is consistent. Hence, by Proposition 2.17, K′ has a model M. Since ¬B is an 
axiom of K′, ¬B is true for M. But, since B is logically valid, B is true for M. 
Hence, B is both true and false for M, which is impossible (by (II) on page 57). 
Thus, B must be a theorem of K.
Corollary 2.19 (Gödel’s Completeness Theorem, 1930)
In any predicate calculus, the theorems are precisely the logically valid wfs.
Proof
This follows from Proposition 2.2 and Corollary 2.18. (Gödel’s original proof 
runs along quite different lines. For other proofs, see Beth (1951), Dreben 
(1952), Hintikka (1955a,b) and Rasiowa and Sikorski (1951, 1952).)
Corollary 2.20
Let K be any theory.
	
a.	A wf B is true in every denumerable model of K if and only if ⊢K B.
	
b.	If, in every model of K, every sequence that satisfies all wfs in a set Γ 
of wfs also satisfies a wf B, then Γ ⊢K B.
	
c.	If a wf B of K is a logical consequence of a set Γ of wfs of K, then Γ ⊢K B.
	
d.	If a wf B of K is a logical consequence of a wf C of K, then C ⊢K B.
Proof
	
a.	We may assume B is closed (Why?). If not-⊢K B, then the theory K′ = 
K + {¬B} is consistent, by Lemma 2.12.* Hence, by Proposition 2.17, K′ 
has a denumerable model M. However, ¬B, being an axiom of K′, is 
true for M. By hypothesis, since M is a denumerable model of K, B is 
true for M. Therefore, B is true and false for M, which is impossible.
*	 If K is a theory and Δ is a set of wfs of K, then K + Δ denotes the theory obtained from K by 
adding the wfs of Δ as axioms.



90
Introduction to Mathematical Logic
	
b.	Consider the theory K + Γ. By the hypothesis, B is true for every 
model of this theory. Hence, by (a), ⊢K+Γ B. So, Γ ⊢K B.
Part (c) is a consequence of (b), and part (d) is a special case of (c).
Corollaries 2.18–2.20 show that the “syntactical” approach to quantifica-
tion theory by means of first-order theories is equivalent to the “semantical” 
approach through the notions of interpretations, models, logical validity, 
and so on. For the propositional calculus, Corollary 1.15 demonstrated the 
analogous equivalence between the semantical notion (tautology) and the 
syntactical notion (theorem of L). Notice also that, in the propositional cal-
culus, the completeness of the system L (see Proposition 1.14) led to a solu-
tion of the decision problem. However, for first-order theories, we cannot 
obtain a decision procedure for logical validity or, equivalently, for prov-
ability in first-order predicate calculi. We shall prove this and related results 
in Section 3.6.
Corollary 2.21 (Skolem–Löwenheim Theorem, 1920, 1915)
Any theory that has a model has a denumerable model.
Proof
If K has a model, then K is consistent, since no wf can be both true and 
false for the same model M. Hence, by Proposition 2.17, K has a denumer-
able model.
The following stronger consequence of Proposition 2.17 is derivable.
Corollary 2.22A
For any cardinal number 𝔪 ≥ℵ0, any consistent theory K has a model of car-
dinality 𝔪.
Proof
By Proposition 2.17, we know that K has a denumerable model. Therefore, it 
suffices to prove the following lemma.
Lemma
If 𝔪 and 𝔫 are two cardinal numbers such that 𝔪 ⩽ 𝔫 and if K has a model 
of cardinality 𝔪, then K has a model of cardinality 𝔫.



91
First-Order Logic and Model Theory
Proof
Let M be a model of K with domain D of cardinality 𝔪. Let D′ be a set of 
cardinality n that includes D. Extend the model M to an interpretation M′ 
that has D′ as domain in the following way. Let c be a fixed element of D. We 
stipulate that the elements of D′ − D behave like c. For example, if Bj
n is the 
interpretation in M of the predicate letter Aj
n and (
)
Bj
n ′ is the new interpreta-
tion in M′, then for any d1, …, dn in D′
′
, (
)
Bj
n  holds for (d1, …, dn) if and only 
if Bj
n holds for (u1, …, un), where ui = di if di ∈ D and ui = c if di ∈ D′ − D. The 
interpretation of the function letters is extended in an analogous way, and 
the individual constants have the same interpretations as in M. It is an easy 
exercise to show, by induction on the number of connectives and quantifiers 
in a wf B, that B is true for M′ if and only if it is true for M. Hence, M′ is a 
model of K of cardinality 𝔫.
Exercises
2.51	 For any theory K, if Γ ⊢K B and each wf in Γ is true for a model M of K, 
show that B is true for M.
2.52	 If a wf B without quantifiers is provable in a predicate calculus, prove 
that B is an instance of a tautology and, hence, by Proposition 2.1, has 
a proof without quantifiers using only axioms (A1)–(A3) and MP. [Hint: 
if B were not a tautology, one could construct an interpretation, having 
the set of terms that occur in B as its domain, for which B is not true, 
contradicting Proposition 2.2.]
	
	 Note that this implies the consistency of the predicate calculus and 
also provides a decision procedure for the provability of wfs without 
quantifiers.
2.53	 Show that ⊢K B if and only if there is a wf C that is the closure of the 
conjunction of some axioms of K such that C ⇒ B is logically valid.
2.54	 Compactness. If all finite subsets of the set of axioms of a theory K have 
models, prove that K has a model.
2.55	 a.	 For any wf B, prove that there is only a finite number of interpreta-
tions of B on a given domain of finite cardinality k.
	
b.	 For any wf B, prove that there is an effective way of determining 
whether B is true for all interpretations with domain of some 
fixed cardinality k.
	
c.	 Let a wf B be called k-valid if it is true for all interpretations that 
have a domain of k elements. Call B precisely k-valid if it is k-valid 
but not (k + 1)-valid. Show that (k + 1)-validity implies k-validity 
and give an example of a wf that is precisely k-valid. (See Hilbert 
and Bernays (1934, § 4–5) and Wajsberg (1933).)



92
Introduction to Mathematical Logic
2.56	
Show that the following wf is true for all finite domains but is false for 
some infinite domain.
	
(
)(
)(
)
( , )
( , )
( , )
( , )
( , )
∀
∀
∀
∧
∧
⇒
) ∧
∨
x
y
z
A x x
A x y
A y z
A x z
A x y
1
2
1
2
1
2
1
2
1
2
A y x
y
x A y x
1
2
1
2
( , )
(
)(
)
( , )
(
)
(


⇒∃
∀
2.57	
Prove that there is no theory K whose models are exactly the interpre-
tations with finite domains.
2.58	
Let B be any wf that contains no quantifiers, function letters, or indi-
vidual constants.
	
	
a.	 Show that a closed prenex wf (∀x1) … (∀xn)(∃y1) … (∃ym)B, with m ≥ 0 
and n ≥ 1, is logically valid if and only if it is true for every interpre-
tation with a domain of n objects.
	
	
b.	 Prove that a closed prenex wf (∃y1) … (∃ym)B is logically valid if and 
only if it is true for all interpretations with a domain of one element.
	
	
c.	 Show that there is an effective procedure to determine the logical 
validity of all wfs of the forms given in (a) and (b).
2.59	
Let K1 and K2 be theories in the same language L. Assume that any 
interpretation M of L is a model of K1 if and only if M is not a model 
of K2. Prove that K1 and K2 are finitely axiomatizable, that is, there are 
finite sets of sentences Γ and Δ such that, for any sentence B
B
, ⊢K1
 if 
and only if Γ ⊢ B, and ⊢K2 B  if and only if Δ ⊢ B.*
2.60	
A set Γ of sentences is called an independent axiomatization of a theory K 
if (a) all sentences in Γ are theorems of K, (b) Γ ⊢ B for every theorem B 
of K, and (c) for every sentence C of Γ, it is not the case that Γ − {C } ⊢ C.* 
Prove that every theory K has an independent axiomatization.
2.61A	 If, for some cardinal 𝔪 ≥ ℵ0, a wf B is true for every interpretation of 
cardinality 𝔪, prove that B is logically valid.
2.62A	 If a wf B is true for all interpretations of cardinality 𝔪 prove that B is 
true for all interpretations of cardinality less than or equal to 𝔪.
2.63	
a.	 Prove that a theory K is a scapegoat theory if and only if, for any wf 
B (x) with x as its only free variable, there is a closed term t such that 
⊢K (∃x)B (x) ⇒ B(t).
	
	
b.	 Prove that a theory K is a scapegoat theory if and only if, for any wf 
B (x) with x as its only free variable such that ⊢K (∃x)B (x), there is a 
closed term t such that ⊢K B (t).
	
	
c.	 Prove that no predicate calculus is a scapegoat theory.
*	 Here, an expression Γ ⊢ B, without any subscript attached to ⊢, means that B is derivable 
from Γ using only logical axioms, that is, within the predicate calculus.



93
First-Order Logic and Model Theory
2.8  First-Order Theories with Equality
Let K be a theory that has as one of its predicate letters A1
2. Let us write t = s 
as an abbreviation for A t s
1
2( , ), and t ≠ s as an abbreviation for ¬A t s
1
2( , ). Then 
K is called a first-order theory with equality (or simply a theory with equality) if 
the following are theorems of K:
	
(
) (
)
(
)
(
)
(
( , )
( ,
A
x x
x
A
x
y
x x
x y
6
7
1
1
1
∀
=
=
⇒
⇒
reflexivity of equality
B
B
)) (
)
substitutivity of equality
where x and y are any variables, B(x, x) is any wf, and B(x, y) arises from 
B(x, x) by replacing some, but not necessarily all, free occurrences of x by y, 
with the proviso that y is free for x in B(x, x). Thus, B(x, y) may or may not 
contain free occurrences of x.
The numbering (A6) and (A7) is a continuation of the numbering of the 
logical axioms.
Proposition 2.23
In any theory with equality,
	
a.	⊢ t = t for any term t;
	
b.	⊢ t = s ⇒ s = t for any terms t and s;
	
c.	⊢ t = s ⇒ (s = r ⇒ t = r) for any terms t, s, and r.
Proof
	
a.	By (A6), ⊢ (∀x1)x1 = x1. Hence, by rule A4, ⊢ t = t.
	
b.	Let x and y be variables not occurring in t or s. Letting B(x, x) be x = x 
and B(x, y) be y = x in schema (A7), ⊢ x = y ⇒ (x = x ⇒ y = x). But, 
by (a), ⊢ x = x. So, by an instance of the tautology (A ⇒ (B ⇒ C)) ⇒ 
(B ⇒ (A ⇒ C)) and two applications of MP, we have ⊢ x = y ⇒ y = x. 
Two applications of Gen yield ⊢ (∀x)(∀y)(x = y ⇒ y = x), and then two 
applications of rule A4 give ⊢ t = s ⇒ s = t.
	
c.	Let x, y, and z be three variables not occurring in t, s, or r. Letting 
B(y, y) be y = z and B(y, x) be x = z in (A7), with x and y inter-
changed, we obtain ⊢ y = x ⇒ (y = z ⇒ x = z). But, by (b), ⊢ x = 
y ⇒ y = x. Hence, using an instance of the tautology (A ⇒ B) ⇒ 
((B ⇒ C) ⇒ (A ⇒ C)) and two applications of MP, we obtain ⊢ x = 
y ⇒(y = z ⇒ x = z). By three applications of Gen, ⊢ (∀x)(∀y)(∀z)(x = 
y ⇒ (y = z ⇒ x = z)), and then, by three uses of rule A4, ⊢ t = s ⇒ 
(s = r ⇒ t = r).



94
Introduction to Mathematical Logic
Exercises
2.64	 Show that (A6) and (A7) are true for any interpretation M in which 
(
)
A1
2 M is the identity relation on the domain of the interpretation.
2.65	 Prove the following in any theory with equality.
	
a.	 ⊢ (∀x)(B (x) ⇔ (∃y)(x = y ∧ B (y))) if y does not occur in B (x)
	
b.	 ⊢ (∀x)(B (x) ⇔ (∀y)(x = y ⇒ B (y))) if y does not occur in B (x)
	
c.	 ⊢ (∀x)(∃y)x = y
	
d.	 ⊢ x = y ⇒ f(x) = f(y), where f is any function letter of one argument
	
e.	 ⊢ B (x) ∧ x = y ⇒ B (y), if y is free for x in B (x)
	
f.	 ⊢ B (x) ∧ ¬B (y) ⇒ x ≠ y, if y is free for x in B (x)
We can reduce schema (A7) to a few simpler cases.
Proposition 2.24
Let K be a theory for which (A6) holds and (A7) holds for all atomic wfs 
B (x, x) in which there are no individual constants. Then K is a theory with 
equality, that is, (A7) holds for all wfs B (x, x).
Proof
We must prove (A7) for all wfs B (x, x). It holds for atomic wfs by assump-
tion. Note that we have the results of Proposition 2.23, since its proof used 
(A7) only with atomic wfs without individual constants. Note also that we 
have (A7) for all atomic wfs B (x, x). For if B (x, x) contains individual con-
stants, we can replace those individual constants by new variables, obtaining 
a wf B*(x, x) without individual constants. By hypothesis, the correspond-
ing instance of (A7) with B*(x, x) is a theorem; we can then apply Gen with 
respect to the new variables, and finally apply rule A4 one or more times to 
obtain (A7) with respect to B (x, x).
Proceeding by induction on the number n of connectives and quantifiers in 
B (x, x), we assume that (A7) holds for all k < n.
Case 1. B (x, x) is ¬C (x, x). By inductive hypothesis, we have ⊢ y = x ⇒ (C (x, y) 
⇒ C (x, x)), since C (x, x) arises from C (x, y) by replacing some occurrences of 
y by x. Hence, by Proposition 2.23(b), instances of the tautologies (A ⇒ B) ⇒ 
(¬B ⇒ ¬A) and (A ⇒ B) ⇒ ((B ⇒ C) ⇒ (A ⇒ C)) and MP, we obtain ⊢ x = y ⇒ 
(B (x, x) ⇒ B (x, y)).
Case 2. B (x, x) is C (x, x) ⇒ D (x, x). By inductive hypothesis and Proposition 
2.23(b), ⊢ x = y ⇒ (C (x, y) ⇒ C (x, x)) and ⊢ x = y ⇒ (D(x, x) ⇒ D(x, y)). Hence, 
by the tautology (A ⇒ (C1 ⇒ C)) ⇒ [(A ⇒ (D ⇒ D1)) ⇒ (A ⇒ ((C ⇒ D) ⇒ (C1 ⇒ 
D1)))] , we have ⊢ x = y ⇒ (B (x, x) ⇒ B (x, y)).



95
First-Order Logic and Model Theory
Case 3. B(x, x) is (∀z)C (x, x, z). By inductive hypothesis, ⊢ x = y ⇒ (C (x, x, z) ⇒ 
C (x, y, z)). Now, by Gen and axiom (A5), ⊢ x = y ⇒(∀z) (C (x, x, z) ⇒ C (x, y, z)). 
By Exercise 2.27(a), ⊢ (∀z)(C (x, x, z) ⇒ C (x, y, z)) ⇒ [(∀z)C (x, x, z) ⇒ (∀z)C (x, y, z)], 
and so, by the tautology (A ⇒ B) ⇒ ((B ⇒ C) ⇒ (A ⇒ C)), ⊢ x = y ⇒ (B (x, x) ⇒ 
B (x, y)).
The instances of (A7) can be still further reduced.
Proposition 2.25
Let K be a theory in which (A6) holds and the following are true.
	
a.	Schema (A7) holds for all atomic wfs B (x, x) such that no function 
letters or individual constants occur in B(x, x) and B (x, y) comes 
from B (x, x) by replacing exactly one occurrence of x by y.
	
b.	⊢x
y
f
z
z
f
w
w
j
n
n
j
n
n
=
⇒
…
=
…
(
,
,
)
(
,
,
)
1
1
, where fj
n is any function 
letter of K, z1, …, zn are variables, and f
w
w
j
n
n
(
,
,
)
1 …
 arises from 
f
z
z
j
n
n
(
,
,
)
1 …
 by replacing exactly one occurrence of x by y.
Then K is a theory with equality.
Proof
By repeated application, our assumptions can be extended to replacements 
of more than one occurrence of x by y. Also, Proposition 2.23 is still deriv-
able. By Proposition 2.24, it suffices to prove (A7) for only atomic wfs without 
individual constants. But, hypothesis (a) enables us easily to prove
	
⊢(
)
(
(
,
,
)
(
,
,
))
y
z
y
z
y
y
z
z
n
n
n
n
1
1
1
1
=
∧…∧
=
⇒
…
⇒
…
B
B
for all variables y1, …, yn, z1, …, zn and any atomic wf B(y1, …, yn) without 
function letters or individual constants. Hence, it suffices to show:
(*) If t(x, x) is a term without individual constants and t(x, y) comes from 
t(x, x) by replacing some occurrences of x by y, then ⊢ x = y ⇒ t(x, x) = t(x, y).*
But (*) can be proved, using hypothesis (b), by induction on the number of 
function letters in t(x,x), and we leave this as an exercise.
It is easy to see from Proposition 2.25 that, when the language of K has only 
finitely many predicate and function letters, it is only necessary to verify 
(A7) for a finite list of special cases (in fact, n wfs for each Aj
n and n wfs for 
each fj
n).
*	 The reader can clarify how (*) is applied by using it to prove the following instance of (A7): 
⊢x
y
A
f
x
A
f
y
=
⇒
⇒
(
(
( ))
(
( )))
1
1
1
1
1
1
1
1
. Let t(x,  x) be f
x
1
1( ) and let t(x,  y) be f
y
1
1( ).



96
Introduction to Mathematical Logic
Exercises
2.66	 Let K1 be a theory whose language has only = as a predicate letter and 
no function letters or individual constants. Let its proper axioms be 
(∀x1)x1 = x1, (∀x1)(∀x2)(x1 = x2 ⇒ x2 = x1), and (∀x1)(∀x2)(∀x3)(x1 = x2 ⇒ (x2 = 
x3 ⇒ x1 = x3)). Show that K1 is a theory with equality. [Hint: It suffices 
to prove that ⊢ x1 = x3 ⇒ (x1 = x2 ⇒ x3 = x2) and ⊢ x2 = x3 ⇒ (x1 = x2 ⇒ 
x1 = x3).] K1 is called the pure first-order theory of equality.
2.67	 Let K2 be a theory whose language has only = and < as predicate letters 
and no function letters or individual constants. Let K2 have the follow-
ing proper axioms.
	
a.	 (∀x1)x1 = x1
	
b.	 (∀x1)(∀x2)(x1 = x2 ⇒ x2 = x1)
	
c.	 (∀x1)(∀x2)(∀x3)(x1 = x2 ⇒ (x2 = x3 ⇒ x1 = x3))
	
d.	 (∀x1)(∃x2)(∃x3)(x1 < x2 ∧ x3 < x1)
	
e.	 (∀x1)(∀x2)(∀x3)(x1 < x2 ∧ x2 < x3 ⇒ x1 < x3)
	
f.	 (∀x1)(∀x2)(x1 = x2 ⇒ ¬ x1 < x2)
	
g.	 (∀x1)(∀x2)(x1 < x2 ∨ x1 = x2 ∨ x2 < x1)
	
h.	 (∀x1)(∀x2)(x1 < x2 ⇒ (∃x3)(x1 < x3 ∧ x3 < x2))
	
	 Using Proposition 2.25, show that K2 is a theory with equality. K2 is 
called the theory of densely ordered sets with neither first nor last element.
2.68	 Let K be any theory with equality. Prove the following.
	
a.	 ⊢ x1 = y1 ∧ … ∧ xn = yn ⇒ t(x1, …, xn) = t(y1, …, yn), where t(y1, …, yn) 
arises from the term t(x1, …, xn) by substitution of y1, …, yn for x1, …, 
xn, respectively.
	
b.	 ⊢ x1 = y1 ∧ … ∧ xn = yn ⇒ (B (x1, …, xn) ⇔ B (y1, …, yn)), where B (y1, …, 
yn) is obtained by substituting y1, …, yn for one or more occurrences 
of x1, …, xn, respectively, in the wf B (x1, …, xn), and y1, …, yn are free 
for x1, …, xn, respectively, in the wf B (x1, …, xn).
Examples
(In the literature, “elementary” is sometimes used instead of “first-order.”)
	
1.	Elementary theory G of groups: predicate letter =, function letter f1
2, 
and individual constant a1. We abbreviate f
t s
1
2( , ) by t + s and a1 by 0. 
The proper axioms are the following.
	
a.	 x1 + (x2 + x3) = (x1 + x2) + x3
	
b.	 x1 + 0 = x1
	
c.	 (∀x1)(∃x2)x1 + x2 = 0



97
First-Order Logic and Model Theory
	
d.	 x1 = x1
	
e.	 x1 = x2 ⇒ x2 = x1
	
f.	 x1 = x2 ⇒ (x2 = x3 ⇒ x1 = x3)
	
g.	 x1 = x2 ⇒ (x1 + x3 = x2 + x3 ∧ x3 + x1 = x3 + x2)
	
	 That G is a theory with equality follows easily from Proposition 2.25. 
If one adds to the axioms the following wf:
	
h.	 x1 + x2 = x2 + x1
	
	
the new theory is called the elementary theory of abelian groups.
	
2.	Elementary theory F of fields: predicate letter =, function letters f1
2 and 
f2
2, and individual constants a1 and a2. Abbreviate f
t s
1
2( , ) by t + s, 
f
t s
2
2( , ) by t · s, and a1 and a2 by 0 and 1. As proper axioms, take (a)–(h) 
of Example 1 plus the following.
	
i.	 x1 = x2 ⇒ (x1 · x3 = x2 · x3 ∧ x3 · x1 = x3 · x2)
	
j.	 x1 · (x2 · x3) = (x1 · x2) · x3
	
k.	 x1 · (x2 + x3) = (x1 · x2) + (x1 · x3)
	
l.	 x1 · x2 = x2 · x1
	
m.	  x1 · 1 = x1
	
n.	  x1 ≠ 0 ⇒ (∃x2)x1 · x2 = 1
	
o.	  0 ≠ 1
F is a theory with equality. Axioms (a)–(m) define the elementary theory RC 
of commutative rings with unit. If we add to F the predicate letter A2
2, abbre-
viate A t s
2
2( , ) by t < s, and add axioms (e), (f), and (g) of Exercise 2.67, as well 
as x1 < x2 ⇒ x1 + x3 < x2 + x3 and x1 < x2 ∧ 0 < x3 ⇒ x1 · x3 < x2 · x3, then the new 
theory F< is called the elementary theory of ordered fields.
Exercise
2.69	 a.	 What formulas must be derived in order to use Proposition 2.25 to 
conclude that the theory G of Example 1 is a theory with equality?
	
b.	 Show that the axioms (d)–(f) of equality mentioned in Example 1 
can be replaced by (d) and
	
(
) :
(
).
′
=
⇒
=
⇒
=
f
x
x
x
x
x
x
1
2
3
2
1
3
One often encounters theories K in which=may be defined; that is, there 
is a wf E(x, y) with two free variables x and y, such that, if we abbreviate 
E(t, s) by t = s, then axioms (A6) and (A7) are provable in K. We make the 



98
Introduction to Mathematical Logic
convention that, if t and s are terms that are not free for x and y, respectively, 
in E (x, y), then, by suitable changes of bound variables (see Exercise 2.48), we 
replace E (x, y) by a logically equivalent wf E*(x, y) such that t and s are free for 
x and y, respectively, in E*(x, y); then t = s is to be the abbreviation of E*(t, s). 
Proposition 2.23 and analogues of Propositions 2.24 and 2.25 hold for such 
theories. There is no harm in extending the term theory with equality to cover 
such theories.
In theories with equality it is possible to define in the following way phrases 
that use the expression “There exists one and only one x such that.…”
Definition
	
(
)
( )
(
)
( )
(
)(
)(
( )
( )
)
∃
∃
∧∀
∀
∧
⇒
=
1x
x
x
x
x
y
x
y
x
y
B
B
B
B
for
In this definition, the new variable y is assumed to be the first variable that 
does not occur in B(x). A similar convention is to be made in all other defini-
tions where new variables are introduced.
Exercise
2.70	 In any theory with equality, prove the following.
	
a.	 ⊢ (∀x)(∃1y)x = y
	
b.	 ⊢ (∃1x)B (x) ⇔ (∃x)(∀y)(x = y ⇔ B (y))
	
c.	 ⊢ (∀x)(B (x) ⇔ C (x)) ⇒ [(∃1x)B (x) ⇔ (∃1x)C (x)]
	
d.	 ⊢ (∃1x)(B ∨ C) ⇒ ((∃1x)B) ∨ (∃1x)C
	
e.	 ⊢ (∃1x)B (x) ⇔ (∃x)(B (x) ∧ (∀y)(B (y) ⇒ y = x))
In any model for a theory K with equality, the relation E in the model corre-
sponding to the predicate letter = is an equivalence relation (by Proposition 
2.23). If this relation E is the identity relation in the domain of the model, 
then the model is said to be normal.
Any model M for K can be contracted to a normal model M* for K by taking the 
domain D* of M* to be the set of equivalence classes determined by the relation 
E in the domain D of M. For a predicate letter Aj
n and for any equivalence classes 
[b1], …, [bn] in D* determined by elements b1, …, bn in D, we let (
)
Aj
n M* hold for 
([b1], …, [bn]) if and only if (
)
Aj
n M holds for (b1, …, bn). Notice that it makes no differ-
ence which representatives b1, …, bn we select in the given equivalence classes 
because, from (A7), ⊢x
y
x
y
A
x
x
A
y
y
n
n
j
n
n
j
n
n
1
1
1
1
=
∧…∧
=
⇒
…
⇔
…
(
(
,
,
)
(
,
,
)). 
Likewise, for any function letter fj
n and any equivalence classes [b1], …, 
[bn] in D*, let (
)
([ ],
, [
])
[(
) ( ,
,
)]
f
b
b
f
b
b
j
n
n
j
n
n
M*
M
1
1
…
=
…
. Again note that this is 
independent of the choice of the representatives b1, …, bn, since, from (A7), 



99
First-Order Logic and Model Theory
we can prove ⊢x
y
x
y
f
x
x
f
y
y
n
n
j
n
n
j
n
n
1
1
1
1
=
∧…∧
=
⇒
…
=
…
(
,
,
)
(
,
,
). For any 
individual constant ai let (ai)M* = [(ai)M]. The relation E* corresponding to = in 
the model M* is the identity relation in D*: E*([b1], [b2]) if and only if E(b1, b2), 
that is, if and only if [b1] = [b2]. Now one can easily prove by induction the 
following lemma: If s = (b1, b2, …) is a denumerable sequence of elements of 
D, and s′ = ([b1], [b2], …) is the corresponding sequence of equivalence classes, 
then a wf B is satisfied by s in M if and only if B is satisfied by s′ in M*. It fol-
lows that, for any wf B, B is true for M if and only if B is true for M*. Hence, 
because M is a model of K, M* is a normal model of K.
Proposition 2.26 (Extension of Proposition 2.17)
(Gödel, 1930) Any consistent theory with equality K has a finite or denumer-
able normal model.
Proof
By Proposition 2.17, K has a denumerable model M. Hence, the contraction 
of M to a normal model yields a finite or denumerable normal model M* 
because the set of equivalence classes in a denumerable set D is either finite 
or denumerable.
Corollary 2.27 (Extension of the Skolem–Löwenheim Theorem)
Any theory with equality K that has an infinite normal model M has a denu-
merable normal model.
Proof
Add to K the denumerably many new individual constants b1, b2, … together 
with the axioms bi ≠ bj for i ≠ j. Then the new theory K′ is consistent. If K′ 
were inconsistent, there would be a proof in K′ of a contradiction C ∧ ¬C, 
where we may assume that C is a wf of K. But this proof uses only a finite 
number of the new axioms: bi1 ≠ bj1, …, bin ≠ bjn. Now, M can be extended to a 
model M# of K plus the axioms bi1 ≠ bj1, …, bin ≠ bjn; in fact, since M is an infi-
nite normal model, we can choose interpretations of bi1, bj1, …, bin, bjn, so that 
the wfs bi1 ≠ bj1, …, bin ≠ bjn are true. But, since C ∧ ¬C is derivable from these 
wfs and the axioms of K, it would follow that C ∧ ¬C is true for M#, which is 
impossible. Hence, K′ must be consistent. Now, by Proposition 2.26, K′ has a 
finite or denumerable normal model N. But, since, for i ≠ j, the wfs bi ≠ bj are 
axioms of K′, they are true for N. Thus, the elements in the domain of N that 
are the interpretations of b1, b2, … must be distinct, which implies that the 
domain of N is infinite and, therefore, denumerable.



100
Introduction to Mathematical Logic
Exercises
2.71	 We define (∃nx)B (x) by induction on n ≥ 1. The case n = 1 has already 
been taken care of. Let (∃n+1x)B(x) stand for (∃y)(B(y) ∧ (∃nx) (x ≠ y ∧ B 
(x))).
	
a.	
Show that (∃nx)B (x) asserts that there are exactly n objects for 
which B holds, in the sense that in any normal model for (∃nx)B(x) 
there are exactly n objects for which the property corresponding 
to B(x) holds.
	
b.	 i.	
For each positive integer n, write a closed wf Bn such that Bn 
is true in a normal model when and only when that model 
contains at least n elements.
	
	
ii.	
Prove that the theory K, whose axioms are those of the pure 
theory of equality K1 (see Exercise 2.66), plus the axioms B1, 
B2, …, is not finitely axiomatizable, that is, there is no theory 
K′ with a finite number of axioms such that K and K′ have the 
same theorems.
	
	
iii.	 For a normal model, state in ordinary English the meaning of 
¬Bn+1.
	
c.	
Let n be a positive integer and consider the wf (En) (∃nx)x = x. Let Ln 
be the theory K1 + {En}, where K1 is the pure theory of equality.
	
	
i.	
Show that a normal model M is a model of Ln if and only if 
there are exactly n elements in the domain of M.
	
	
ii.	
Define a procedure for determining whether any given sen-
tence is a theorem of Ln and show that Ln is a complete theory.
2.72	 a.	
Prove that, if a theory with equality K has arbitrarily large finite 
normal models, then it has a denumerable normal model.
	
b.	 Prove that there is no theory with equality whose normal models 
are precisely all finite normal interpretations.
2.73	 Prove that any predicate calculus with equality is consistent. (A predi-
cate calculus with equality is assumed to have (A1)–(A7) as its only 
axioms.)
2.74D	 Prove the independence of axioms (A1)–(A7) in any predicate calculus 
with equality.
2.75	 If B is a wf that does not contain the = symbol and B is provable in a 
predicate calculus with equality K, show that B is provable in K with-
out using (A6) or (A7).
2.76D	 Show that = can be defined in any theory whose language has only a 
finite number of predicate letters and no function letters.
2.77	 a.A	 Find a nonnormal model of the elementary theory of groups G.



101
First-Order Logic and Model Theory
	
b.	 Show that any model M of a theory with equality K can be 
extended to a nonnormal model of K. [Hint: Use the argument in 
the proof of the lemma within the proof of Corollary 2.22.]
2.78	 Let B be a wf of a theory with equality. Show that B is true in every 
normal model of K if and only if ⊢K B.
2.79	 Write the following as wfs of a theory with equality.
	
a.	
There are at least three moons of Jupiter.
	
b.	 At most two people know everyone in the class.
	
c.	
Everyone in the logic class knows at least two members of the 
geometry class.
	
d.	 Every person loves at most one other person.
2.80	 If P(x) means x is a person, A(x, y) means x is a parent of y, G(x, y) means 
x is a grandparent of y, and x = y means x and y are identical, translate the 
following wfs into ordinary English.
	
i. (
)( ( )
[(
)( ( , )
(
)( ( ,
)
( , )))])
∀
⇒
∀
⇔∃
∧
x P x
y G y x
w A y w
A w x
	
ii.(
)( ( )
(
)(
)(
)(
)(
∀
⇒∃
∃
∃
∃
≠
∧
≠
∧
≠
∧
≠
∧
x P x
x
x
x
x
x
x
x
x
x
x
x
x
1
2
3
4
1
2
1
3
1
4
2
3
x
x
x
x
G x x
G x
x
G x
x
G x
x
y G y x
y
2
4
3
4
1
2
3
4
≠
∧
≠
∧
∧
∧
∧
∧∀
⇒
(
, )
(
, )
(
, )
(
, )
(
)( ( , )
=
∨
=
∨
=
∨
=
x
y
x
y
x
y
x
1
2
3
4)))
2.81	 Consider the wf
	
( )
(
)(
)(
)(
( )).
∗
∀
∀
∃
≠
∧
≠
∧
x
y
z z
x
z
y
A z
	
Show that (*) is true in a normal model M of a theory with equality if 
and only if there exist in the domain of M at least three things having 
property A(z).
2.82	 Let the language L  have the four predicate letters =, P, S, and L. Read 
u = v as u and v are identical, P(u) as u is a point, S(u) as u is a line, and 
L(u, v) as u lies on v. Let the theory of equality G of planar incidence 
geometry have, in addition to axioms (A1)–(A7), the following nonlogi-
cal axioms.
	
1.	
P(x) ⇒ ¬S(x)
	
2.	
L(x, y) ⇒ P(x) ∧ S(y)
	
3.	
S(x) ⇒ (∃y)(∃z)(y ≠ z ∧ L(y, x) ∧ L(z, x))
	
4.	
P(x) ∧ P(y) ∧ x ≠ y ⇒ (∃1z)(S(z) ∧ L(x, z) ∧ L(y, z))
	
5.	
(∃x)(∃y)(∃z)(P(x) ∧ P(y) ∧ P(z) ∧ ¬C (x, y, z))



102
Introduction to Mathematical Logic
	
where C (x, y, z) is the wf (∃u)(S(u) ∧ L(x, u) ∧ L(y, u) ∧ L(z, u)), which is 
read as x, y, z are collinear.
	
a.	
Translate (1)–(5) into ordinary geometric language.
	
b.	 Prove ⊢G (∀u)(∀v)(S(u) ∧ S(v) ∧ u ≠ v ⇒ (∀x)(∀y)(L(x, u) ∧ L(x, v) ∧ 
L(y, u) ∧ L(y, v) ⇒ x = y)), and translate this theorem into ordinary 
geometric language.
	
c.	
Let R(u, v) stand for S(u) ∧ S(v) ∧ ¬(∃w)(L(w, u) ∧ L(w, v)). Read R(u, v) 
as u and v are distinct parallel lines.
	
	
i.	
Prove: ⊢G R(u, v) ⇒ u ≠ v
	
	
ii.	
Show that there exists a normal model of G with a finite 
domain in which the following sentence is true:
	
(
)(
)( ( )
( )
( , )
(
)( ( , )
( , )))
∀
∀
∧
∧¬
⇒∃
∧
x
y S x
P y
L y x
z L y z
R z x
1
	
d.	 Show that there exists a model of G in which the following sen-
tence is true:
	
(
)(
)( ( )
( )
( , ))
∀
∀
∧
∧
≠
⇒¬
x
y S x
S y
x
y
R x y
2.9  Definitions of New Function Letters 
and Individual Constants
In mathematics, once we have proved, for any y1, …, yn, the existence of 
a unique object u that has a property B(u, y1, …, yn), we often introduce a 
new function letter f(y1, …, yn) such that B(f(y1, …, yn), y1, …, yn) holds for all 
y1, …, yn. In cases where we have proved the existence of a unique object u 
that satisfies a wf B(u) and B(u) contains u as its only free variable, then we 
introduce a new individual constant b such that B(b) holds. It is generally 
acknowledged that such definitions, though convenient, add nothing really 
new to the theory. This can be made precise in the following manner.
Proposition 2.28
Let K be a theory with equality. Assume that ⊢K (∃1u)B (u, y1, …, yn). Let K# 
be the theory with equality obtained by adding to K a new function letter f 
of n arguments and the proper axiom B (f(y1, …, yn), y1, …, yn),* as well as all 
*	 It is better to take this axiom in the form (∀u)(u = f(y1, …, yn) ⇒ B(u, y1, …, yn)), since f(y1, …, yn) 
might not be free for u in B(u, y1, …, yn).



103
First-Order Logic and Model Theory
instances of axioms (A1)–(A7) that involve f. Then there is an effective trans-
formation mapping each wf C of K# into a wf C # of K such that:
	
a.	If f does not occur in C, then C # is C.
	
b.	(¬ C)# is ¬ (C #).
	
c.	(C ⇒ D)# is C# ⇒ D#.
	
d.	((∀x)C)# is (∀x)(C #).
	
e.	⊢K#(C⇐ C #).
	
f.	If ⊢K#C, then ⊢K C #.
Hence, if C does not contain f and ⊢K
# C, then ⊢K C.
Proof
By a simple f-term we mean an expression f(t1, …, tn) in which t1, …, tn are terms 
that do not contain f. Given an atomic wf C of K#, let C  * be the result of replac-
ing the leftmost occurrence of a simple term f(t1, …, tn) in C by the first variable 
v not in C or B. Call the wf (∃v)(B (v, t1, …, tn) ∧ C *) the f-transform of C. If C does 
not contain f, then let C be its own f-transform. Clearly, ⊢K#(∃v)(B(v, t1, …, tn) ∧ 
C  *)⇐C. (Here, we use ⊢K (∃1u)B(u, y1, …, yn) and the axiom B (f(y1, …, yn), y1, …, 
yn) of K#.) Since the f-transform C ′ of C contains one less f than C and ⊢K#C ′⇔C, 
if we take successive f-transforms, eventually we obtain a wf C# that does not 
contain f and such that ⊢K#C  #⇔C. Call C  # the f-less transform of C. Extend the 
definition to all wfs of K# by letting ( ¬ D)# be  ¬ (D #),(D ⇒E)# be D #⇒E  #, and 
((∀ x)D)# be (∀ x)D#. Properties (a)–(e) of Proposition 2.28 are then obvious. 
To prove property (f), it suffices, by property (e), to show that, if C does not 
contain f and ⊢K#C, then ⊢K C. We may assume that C is a closed wf, since a wf 
and its closure are deducible from each other.
Assume that M is a model of K. Let M1 be the normal model obtained by 
contracting M. We know that a wf is true for M if and only if it is true for 
M1. Since ⊢K (∃1u)B (u, y1, …, yn), then, for any b1, …, bn in the domain of M1, 
there is a unique c in the domain of M1 such that M
n
c b
b
1
1
B [ ,
,
,
]
…
. If we 
define f1(b1, …, bn) to be c, then, taking f1 to be the interpretation of the func-
tion letter f, we obtain from M1 a model M# of K#. For the logical axioms of K# 
(including the equality axioms of K#) are true in any normal interpretation, 
and the axiom B (f(y1, …, yn), y1, …, yn) also holds in M# by virtue of the defi-
nition of f1. Since the other proper axioms of K# do not contain f and since 
they are true for M1, they are also true for M#. But ⊢K#C. Therefore, C is true 
for M#, but since C does not contain f, C is true for M1 and hence also for M. 
Thus, C is true for every model of K. Therefore, by Corollary 2.20(a), ⊢K C. 
(In the case where ⊢K (∃1u)B (u) and B (u) contains only u as a free variable, 
we form K# by adding a new individual constant b and the axiom B (b). Then 
the analogue of Proposition 2.28 follows from practically the same proof as 
the one just given.)



104
Introduction to Mathematical Logic
Exercise
2.83	 Find the f-less transforms of the following wfs.
	
a.	 (
)(
)(
( , , ( ,
,
,
))
( , ,
, )
)
∀
∃
…
⇒
…
=
x
y A x y f x y
y
f y x
x
x
n
1
3
1
	
b.	 A
f y
y
f y
y
x A x f y
y
n
n
n
1
1
1
1
1
1
2
1
( (
,
,
, (
,
,
)))
(
)
( , (
,
,
))
…
…
∧∃
…
−
Note that Proposition 2.28 also applies when we have introduced several 
new symbols f1, …, fm because we can assume that we have added each fi to 
the theory already obtained by the addition of f1, …, fi−1; then m successive 
applications of Proposition 2.28 are necessary. The resulting wf C  # of K can be 
considered an (f1, …, fm)-free transform of C into the language of K.
Examples
	
1.	In the elementary theory G of groups, one can prove (∃1y)x + y = 0. 
Then introduce a new function f of one argument, abbreviate f(t) by 
(−t), and add the new axiom x + (−x) = 0. By Proposition 2.28, we now 
are not able to prove any wf of G that we could not prove before. 
Thus, the definition of (−t) adds no really new power to the original 
theory.
	
2.	In the elementary theory F of fields, one can prove that (∃1y)((x ≠ 0 ∧ 
x · y = 1) ∨ (x = 0 ∧ y = 0)). We then introduce a new function letter g 
of one argument, abbreviate g(t) by t−1, and add the axiom (x ≠ 0 ∧ x · 
x−1 = 1) ∨ (x = 0 ∧ x−1 = 0), from which one can prove x ≠ 0 ⇒ x · x−1 = 1.
From the statement and proof of Proposition 2.28 we can see that, in theories 
with equality, only predicate letters are needed; function letters and indi-
vidual constants are dispensable. If fj
n is a function letter, we can replace it 
by a new predicate letter Ak
n+1 if we add the axiom (
)
( ,
,
,
)
∃
…
+
1
1
1
u A
u y
y
k
n
n . An 
individual constant is to be replaced by a new predicate letter Ak
1 if we add 
the axiom (
)
( )
∃1
1
u A u
k
.
Example
In the elementary theory G of groups, we can replace + and 0 by predicate 
letters A1
3 and A1
1 if we add the axioms (
)(
)(
)
(
,
,
)
∀
∀
∃
x
x
x A x x
x
1
2
1
3
1
3
1
2
3  and 
(
)
(
)
∃1
1
1
1
1
x A x , and if we replace axioms (a), (b), (c), and (g) by the following:
	
a′.	A x
x
u
A x u v
A x x
w
A w x
y
v
y
1
3
2
3
1
3
1
1
3
1
2
1
3
3
(
,
, )
(
, , )
(
,
,
)
( ,
, )
∧
∧
∧
⇒
=
	
b′.	A y
A x y z
z
x
1
1
1
3
( )
( , , )
∧
⇒
=
	
c′.	(
)(
)(
)(
( )
( , , )
)
∃
∀
∀
∧
⇒
=
y
u
v A u
A x y v
v
u
1
1
1
3
	
g′.	[
(
, , )
(
, , )
( ,
, )
( ,
,
)]
x
x
A x
y z
A x
y u
A y x v
A y x
w
z
1
2
1
3
1
1
3
2
1
3
1
1
3
2
=
∧
∧
∧
∧
⇒
= u
∧
=
v
w 



105
First-Order Logic and Model Theory
Notice that the proof of Proposition 2.28 is highly nonconstructive, since it 
uses semantical notions (model, truth) and is based upon Corollary 2.20(a), 
which was proved in a nonconstructive way. Constructive syntactical proofs 
have been given for Proposition 2.28 (see Kleene, 1952, § 74), but, in general, 
they are quite complex.
Descriptive phrases of the kind “the u such that B (u, y1, …, yn)” are 
very common in ordinary language and in mathematics. Such phrases 
are called definite descriptions. We let ιu(B (u, y1, …, yn)) denote the unique 
object u such that B (u, y1, …, yn) if there is such a unique object. If there 
is no such unique object, either we may let ιu(B (u, y1, …, yn)) stand for 
some fixed object, or we may consider it meaningless. (For example, we 
may say that the phrases “the present king of France” and “the smallest 
integer” are meaningless or we may arbitrarily make the convention that 
they denote 0.) There are various ways of incorporating these ι-terms in 
formalized theories, but since in most cases the same results are obtained 
by using new function letters or individual constants as above, and since 
they all lead to theorems similar to Proposition 2.28, we shall not discuss 
them any further here. For details, see Hilbert and Bernays (1934) and 
Rosser (1939, 1953).
2.10  Prenex Normal Forms
A wf (Q1y1) … (Qnyn)B, where each (Qiyi) is either (∀yi) or (∃yi), yi is different 
from yj for i ≠ j, and B contains no quantifiers, is said to be in prenex normal 
form. (We include the case n = 0, when there are no quantifiers at all.) We 
shall prove that, for every wf, we can construct an equivalent prenex nor-
mal form.
Lemma 2.29
In any theory, if y is not free in D, and C (x) and C (y) are similar, then the 
­following hold.
	
a.	⊢ ((∀x)C (x) ⇒ D) ⇔ (∃y)(C (y) ⇒ D)
	
b.	⊢ ((∃x)C (x) ⇒ D) ⇔ (∀y)(C (y) ⇒ D)
	
c.	⊢ (D ⇒ (∀x)C (x)) ⇔ (∀y)(D ⇒ C (y))
	
d.	⊢ ¬(D ⇒ (∃x)C (x)) ⇔ (∃y)(D ⇒ C (y))
	
e.	⊢ ¬(∀x)C ⇔ (∃x) ¬C
	
f.	⊢ ¬(∃x)C ⇔ (∀x) ¬C



106
Introduction to Mathematical Logic
Proof
For part (a):
	
1.	(∀x)C (x) ⇒ D	
Hyp
	
2.	¬(∃y)(C (y) ⇒ D)	
Hyp
	
3.	¬¬(∀y) ¬(C (y) ⇒ D)	
2, abbreviation
	
4.	(∀y) ¬(C (y) ⇒ D)	
3, negation elimination
	
5.	(∀y)(C (y) ∧ ¬D)	
4, tautology, Proposition 2.9(c)
	
6.	C (y) ∧ ¬D	
5, rule A4
	
7.	C (y)	
6, conjunction elimination
	
8.	(∀y)C (y)	
7, Gen
	
9.	(∀x)C (x)	
8, Lemma 2.11, Biconditional elimination
	 10.	D	
1, 9, MP
	 11.	¬D	
6, conjunction elimination
	 12.	D ∧ ¬D	
10, 11, conjunction introduction
	 13.	(∀x)C (x) ⇒ D, 	
1–12
	
	 ¬(∃y)(C (y) ⇒ D) ⊢ D ∧ ¬D
	 14.	(∀x)C (x) ⇒ D	
1–13, proof by contradiction
	
	 ⊢ (∃y)(C (y) ⇒ D)
	 15.	⊢ (∀x)C (x) ⇒	
1–14, Corollary 2.6
	
	 D ⇒ (∃y)(C (y) ⇒ D)
The converse is proven in the following manner.
	
1.	(∃y)(C (y) ⇒ D)	
Hyp
	
2.	(∀x)C (x)	
Hyp
	
3.	C (b) ⇒ D	
1, rule C
	
4.	C (b)	
2, rule A4
	
5.	D	
3, 4, MP
	
6.	(∃y)(C (y) ⇒ D), (∀x)C (x) ⊢C D	
1–5
	
7.	(∃y)(C (y) ⇒ D), (∀x)C (x) ⊢ D	
6, Proposition 2.10
	
8.	⊢ (∃y)(C (y) ⇒ D) ⇒ ((∀x)C (x) ⇒ D)	
1–7, Corollary 2.6 twice
Part (a) follows from the two proofs above by biconditional introduction. 
Parts (b)–(f) are proved easily and left as an exercise. (Part (f) is trivial, and 
(e) follows from Exercise 2.33(a); (c) and (d) follow easily from (b) and (a), 
respectively.)
Lemma 2.29 allows us to move interior quantifiers to the front of a wf. This 
is the essential process in the proof of the following proposition.
Proposition 2.30
There is an effective procedure for transforming any wf B into a wf C in 
prenex normal form such that ⊢ B ⇔ C.



107
First-Order Logic and Model Theory
Proof
We describe the procedure by induction on the number k of occurrences of 
connectives and quantifiers in B. (By Exercise 2.32(a,b), we may assume that 
the quantified variables in the prefix that we shall obtain are distinct.) If k = 0, then 
let C  be B itself. Assume that we can find a corresponding C for all wfs with 
k < n, and assume that B has n occurrences of connectives and quantifiers.
Case 1. If B is ¬D, then, by inductive hypothesis, we can construct a wf E 
in prenex normal form such that ⊢ D ⇔ E. Hence, ⊢ ¬D ⇔ ¬E by bicondi-
tional negation. Thus, ⊢ B ⇔ ¬E, and, by applying parts (e) and (f) of Lemma 
2.29 and the replacement theorem (Proposition 2.9(b)), we can find a wf C in 
prenex normal form such that ⊢ ¬E ⇔ C. Hence, ⊢ B ⇔ C.
Case 2. If B is D ⇒ E, then, by inductive hypothesis, we can find wfs D1 and 
E1 in prenex normal form such that ⊢ D ⇔ D1 and ⊢ E ⇔ E1. Hence, by a suit-
able tautology and MP, ⊢ (D ⇒ E) ⇔ (D1 ⇒ E1), that is, ⊢ B ⇔ (D1 ⇒ E1). Now, 
applying parts (a)–(d) of Lemma 2.29 and the replacement theorem, we can 
move the quantifiers in the prefixes of D1 and E1 to the front, obtaining a wf C 
in prenex normal form such that ⊢ B ⇔ C.
Case 3. If B is (∀x)D, then, by inductive hypothesis, there is a wf D1 in prenex 
normal form such that ⊢ D ⇔ D1; hence, ⊢ B ⇔ (∀x)D1 by Gen, Lemma 2.8, and 
MP. But (∀x)D1 is in prenex normal form.
Examples
	
1.	Let B be (
)(
( )
(
)(
( , )
(
)(
( , )))
∀
⇒∀
⇒¬ ∀
x A x
y A x y
z A y z
1
1
2
2
3
2
. By part (e) 
of Lemma 2.29: (
)(
( )
(
)[
( , )
(
)
( , )]).
∀
⇒∀
⇒∃¬
x A x
y A x y
z
A y z
1
1
2
2
3
2
	
	 By part (d): (
)(
( )
(
)(
)[
( , )
( , )]).
∀
⇒∀
∃
⇒¬
x A x
y
u A x y
A y u
1
1
2
2
3
2
	
	 By part (c): (
)(
)(
( )
(
)[
( , )
( , )]).
∀
∀
⇒∃
⇒¬
x
v A x
u A x v
A v u
1
1
2
2
3
2
	
	 By part (d): (
)(
)(
)(
( )
(
( , )
( ,
))).
∀
∀
∃
⇒
⇒¬
x
v
w A x
A x v
A v w
1
1
2
2
3
2
	
	 Changing bound variables: (
)(
)(
)(
( )
(
( , )
( , ))).
∀
∀
∃
⇒
⇒¬
x
y
z A x
A x y
A y z
1
1
2
2
3
2
	
2.	Let B be A x y
y A y
x A x
A y
1
2
1
1
1
1
2
1
( , )
(
)[
( )
([(
)
( )]
( ))].
⇒∃
⇒
∃
⇒
	
	 By part (b): A x y
y A y
u A u
A y
1
2
1
1
1
1
2
1
( , )
(
)(
( )
(
)[
( )
( )]).
⇒∃
⇒∀
⇒
	
	 By part (c): A x y
y
v A y
A v
A y
1
2
1
1
1
1
2
1
( , )
(
)(
)(
( )
[
( )
( )]).
⇒∃
∀
⇒
⇒
	
	 By part (d): (
)(
( , )
(
)[
( )
(
( )
( ))]).
∃
⇒∀
⇒
⇒
w A x y
v A w
A v
A w
1
2
1
1
1
1
2
1
	
	 By part (c): (
)(
)(
( , )
[
( )
(
( )
( ))]).
∃
∀
⇒
⇒
⇒
w
z A x y
A w
A z
A w
1
2
1
1
1
1
2
1
Exercise
2.84 Find prenex normal forms equivalent to the following wfs.
	
a.	[(
)(
( )
( , ))]
([(
)
( )]
(
)
( , ))
∀
⇒
⇒
∃
⇒∃
x A x
A x y
y A y
z A y z
1
1
1
2
1
1
1
2
	
b.	(
)
( , )
(
( )
(
)
( , ))
∃
⇒
⇒¬ ∃
x A x y
A x
u A x u
1
2
1
1
1
2



108
Introduction to Mathematical Logic
A predicate calculus in which there are no function letters or individual 
constants and in which, for any positive integer n, there are infinitely many 
predicate letters with n arguments, will be called a pure predicate calculus. 
For pure predicate calculi we can find a very simple prenex normal form 
theorem. A wf in prenex normal form such that all existential quantifiers 
(if any) precede all universal quantifiers (if any) is said to be in Skolem 
normal form.
Proposition 2.31
In a pure predicate calculus, there is an effective procedure assigning to each 
wf B another wf S  in Skolem normal form such that ⊢ B  if and only if ⊢ S 
(or, equivalently, by Gödel’s completeness theorem, such that B is logically 
valid if and only if S  is logically valid).
Proof
First we may assume that B is a closed wf, since a wf is provable if and only 
if its closure is provable. By Proposition 2.30 we may also assume that B is in 
prenex normal form. Let the rank r of B be the number of universal quanti-
fiers in B that precede existential quantifiers. By induction on the rank, we 
shall describe the process for finding Skolem normal forms. Clearly, when 
the rank is 0, we already have the Skolem normal form. Let us assume that 
we can construct Skolem normal forms when the rank is less than r, and let r 
be the rank of B. B can be written as follows: (∃y1) … (∃yn) (∀u)C (y1, …, yn, u), 
where C  (y1, …, yn, u) has only y1, …, yn, u as its free variables. Let Aj
n+1 be the 
first predicate letter of n + 1 arguments that does not occur in B. Construct 
the wf
	
(
) (
)
(
)([(
)( (
,
,
, )
(
,
,
, ))]
(
)
B
C
1
1
1
1
1
∃
… ∃
∀
…
⇒
…
⇒∀
+
y
y
u
y
y
u
A
y
y
u
u
n
n
j
n
n
A
y
y
u
j
n
n
+
…
1
1
(
,
,
, ))
Let us show that ⊢ B if and only if ⊢ B1. Assume ⊢ B1. In the proof of B1, 
replace all occurrences of A
z
z
w
j
n
n
+
…
1
1
( ,
,
,
) by C *(z1, …, zn, w)), where C * is 
obtained from C by replacing all bound variables having free occurrences 
in the proof by new variables not occurring in the proof. The result is a 
proof of
	
(
)
(
)(((
)( (
,
,
, )
(
,
,
, )))
(
)
(
,
∃
… ∃
∀
…
⇒
…
⇒∀
…
y
y
u
y
y
u
y
y
u
u
y
n
n
n
1
1
1
1
C
C
C
*
*
,
, ))
y
u
n



109
First-Order Logic and Model Theory
(C * was used instead of C so that applications of axiom (A4) would remain 
applications of the same axiom.) Now, by changing the bound variables back 
again, we see that
	
⊢(
)
(
)[(
)( (
,
,
, )
(
,
,
, ))
(
) (
,
,
∃
… ∃
∀
…
⇒
…
⇒∀
…
y
y
u
y
y
u
y
y
u
u
y
y
n
n
n
n
1
1
1
1
C
C
C
, u)]
Since ⊢ (∀u)(C (y1, …, yn, u) ⇒ C (y1, …, yn, u)), we obtain, by the replace-
ment theorem, ⊢ (∃y1) … (∃yn)(∀u)C (y1, …, yn, u), that is, ⊢ B. Conversely, 
assume that ⊢ B. By rule C, we obtain (∀u)C (b1, …, bn, u). But, ⊢ (∀u)D ⇒ 
((∀u)(D ⇒ E) ⇒ (∀u)E) (see Exercise 2.27 (a)) for any wfs D and E. Hence, 
⊢C
n
j
n
n
j
n
u
b
b
u
A
b
b
u
u A
(
)( ( ,
,
, )
( ,
,
, ))
(
)
∀
…
⇒
…
⇒∀
+
+
C
1
1
1
1  (b1, …, bn, u). So, 
by rule E4, 
⊢C
n
n
j
n
n
y
y
u
b
b
u
A
y
y
u
(
)
(
)([(
)(
,
,
,
,
,
,
)]
∃
… ∃
∀
…
(
) ⇒
…
(
) ⇒
+
1
1
1
1
C
(
)
(
,
,
, ))
∀
…
+
u A
y
y
u
j
n
n
1
1
, that is, ⊢C B1. By Proposition 2.10, ⊢ B1. A prenex nor-
mal form of B1 has the form B2: (∃y1) … (∃yn) (∃u)(Q1z1) … (Qszs)(∀v)G, where 
G has no quantifiers and (Q1z1) … (Qszs) is the prefix of C. [In deriving the 
prenex normal form, first, by Lemma 2.29(a), we pull out the first (∀u), which 
changes to (∃u); then we pull out of the first conditional the quantifiers in 
the prefix of C. By Lemma 2.29(a,b), this exchanges existential and universal 
quantifiers, but then we again pull these out of the second conditional of B1, 
which brings the prefix back to its original form. Finally, by Lemma 2.29(c), 
we bring the second (∀u) out to the prefix, changing it to a new quantifier 
(∀v).] Clearly, B2 has rank one less than the rank of B and, by Proposition 
2.30, ⊢ B1 ⇔ B2. But, ⊢ B if and only if ⊢ B1. Hence, ⊢ B if and only if ⊢ B2. By 
inductive hypothesis, we can find a Skolem normal form for B2, which is also 
a Skolem normal form for B.
Example
B: (∀x)(∀y)(∃z)C (x, y, z), where C contains no quantifiers
	
B
C
1
1
1
:(
)((
)(
) ( , , )
( ))
(
)
( )
∀
∀
∃
⇒
⇒∀
x
y
z
x y z
A x
x A x
j
j
, where Aj
1 is not in C.
We obtain the prenex normal form of B1:
	
(
)
(
)(
) ( , , )
( )
(
)
( )
∃
∀
∃
⇒

⇒∀
(
)
x
y
z
x y z
A x
x A x
j
j
C
1
1
	
2.29(a)
	
(
) (
) [(
) ( , , )
( )
(
)
( )
∃
∃
∃
⇒

⇒∀
(

x
y
z
x y z
A x
x A x
j
j
C
1
1
	
2.29(a)
	
(
) (
)(
)
( , , )
( )
(
)
( )
∃
∃
∀
⇒

⇒∀
(
)
x
y
z
x y z
A x
x A x
j
j
C
1
1
	
2.29(b)



110
Introduction to Mathematical Logic
	
(
)(
) (
)
( , , )
( )
(
)
( )
∃
∀
∀
⇒
(
) ⇒∀


x
y
z
x y z
A x
x A x
j
j
C
1
1
	
2.29(b)
	
(
)(
)(
)
( , , )
( )
(
)
( )
∃
∀
∃
⇒

⇒∀
(

x
y
z
x y z
A x
x A x
j
j
C
1
1
	
2.29(a)
	
(
)(
)(
)(
)
( , , )
( )
( )
∃
∀
∃
∀
⇒
(
) ⇒


x
y
z
v
x y z
A x
A v
j
j
C
1
1
	
2.29(c)
We repeat this process again: Let D(x, y, z, v) be ( ( , , )
( ))
( )
C x y z
A x
A v
j
j
⇒
⇒
1
1
. 
Let Ak
2 not occur in D. Form:
	
(
)
(
) (
)(
)(
( , , , ))
( , )
(
)
( , )
∃
∀
∃
∀
⇒



⇒∀
x
y
z
v
x y z v
A x y
y A x y
k
k
D
2
2
(
)
	
(
)(
)[[(
)(
)(
( , , , ))
( , )]
(
)
( , )]
∃
∃
∃
∀
⇒
⇒∀
x
y
z
v
x y z v
A x y
y A x y
k
k
D
2
2
	
2.29(a)
	
(
)(
)(
)(
)([(
( , , , )
( , )]
(
)
( , ))
∃
∃
∃
∃
⇒
⇒∀
x
y
z
v
x y z v
A x y
y A x y
k
k
D
2
2
	 2.29(a,b)
	
(
)(
)(
)(
)(
)([
( , , , )
( , )]
( ,
)]
∃
∃
∃
∀
∀
⇒
⇒
x
y
z
v
w
x y z v
A x y
A x w
k
k
D
2
2
	
2.29(c)
Thus, a Skolem normal form of B is:
	 (
)(
)(
)(
)(
)([(( ( , , )
( ))
( ))
( , )]
∃
∃
∃
∀
∀
⇒
⇒
⇒
x
y
z
v
w
x y z
A x
A v
A x y
j
j
k
C
1
1
2
⇒A x w
k
2( ,
))
Exercises
2.85	 Find Skolem normal forms for the following wfs.
	
a.	 ¬ ∃
⇒∀
∃
∀
(
)
( )
(
)(
)(
)
( , , )
x A x
u
y
x A u x y
1
1
1
3
	
b.	 (
)(
)(
)(
)
( , , , )
∀
∃
∀
∃
x
y
u
v A x y u v
1
4
2.86	 Show that there is an effective procedure that gives, for each wf B 
of a pure predicate calculus, another wf D of this calculus of the form 
(∀y1) … (∀yn)(∃z1) … (∃zm)C, such that C is quantifier-free, n, m ≥ 0, and 
B is satisfiable if and only if D is satisfiable. [Hint: Apply Proposition 
2.31 to ¬B.]
2.87	 Find a Skolem normal form S for (
)(
)
( , )
∀
∃
x
y A x y
1
2
 and show that it 
is not the case that ⊢S ⇔∀
∃
(
)(
)
( , )
x
y A x y
1
2
. Hence, a Skolem normal 
form for a wf B is not necessarily logically equivalent to B, in contra-
distinction to the prenex normal form given by Proposition 2.30.



111
First-Order Logic and Model Theory
2.11  Isomorphism of Interpretations: Categoricity of Theories
We shall say that an interpretation M of some language L  is isomorphic with 
an interpretation M* of L   if and only if there is a one–one correspondence g 
(called an isomorphism) of the domain D of M with the domain D* of M* 
such that:
	
1.	For any predicate letter Aj
n of L   and for any b1, …, bn in D, MA b
b
j
n
n
[ ,
,
]
1 …
 
if and only if M* A
b
b
j
n
n
[ (
),
,
(
)]
g
g
1 …
.
	
2.	For any function letter fj
n of L and for any b1, …, bn in D, 
g
g
g
((
) ( ,
,
))
(
)
( (
),
, (
))
f
b
b
f
b
b
j
n
n
j
n
n
M
M*
1
1
…
=
…
.
	
3.	For any individual constant aj of L, ɡ((aj)M) = (aj)M*.
The notation M ≈ M* will be used to indicate that M is isomorphic with M*. 
Notice that, if M ≈ M*, then the domains of M and M* must be of the same 
cardinality.
Proposition 2.32
If g is an isomorphism of M with M*, then:
	
a.	for any wf B of L, any sequence s = (b1, b2, …) of elements of the 
domain D of M, and the corresponding sequence ɡ(s) = (ɡ(b1), 
ɡ(b2), …), s satisfies B in M if and only if ɡ(s) satisfies B in M*;
	
b.	hence, ⊧M B if and only if ⊧M* B.
Proof
Part (b) follows directly from part (a). The proof of part (a) is by induction 
on the number of connectives and quantifiers in B and is left as an exercise.
From the definition of isomorphic interpretations and Proposition 2.32 we 
see that isomorphic interpretations have the same “structure” and, thus, dif-
fer in no essential way.
Exercises
2.88	 Prove that, if M is an interpretation with domain D and D* is a set that 
has the same cardinality as D, then one can define an interpretation M* 
with domain D* such that M is isomorphic with M*.
2.89	 Prove the following: (a) M is isomorphic with M. (b) If M1 is isomorphic 
with M2, then M2 is isomorphic with M1. (c) If M1 is isomorphic with M2 
and M2 is isomorphic with M3, then M1 is isomorphic with M3.



112
Introduction to Mathematical Logic
A theory with equality K is said to be 𝔪—categorical, where 𝔪 is a car-
dinal number, if and only if: any two normal models of K of cardinality m 
are isomorphic, and K has at least one normal model of cardinality 𝔪 (see 
Loś, 1954c).
Examples
	
1.	Let K2 be the pure theory of equality K1 (see page 96) to which has 
been added axiom (E2): (∃x1)(∃x2)(x1 ≠ x2 ∧ (∀x3)(x3 = x1 ∨ x3 = x2)). 
Then K2 is 2-categorical. Every normal model of K2 has exactly two 
elements. More generally, define (En) to be:
	
(
)
(
)
(
)(
)
∃
… ∃
∧
≠
∧∀
=
∨…∨
=




≤< ≤
x
x
x
x
y y
x
y
x
n
i j n
i
j
n
1
1
1
	
	 where ∧1≤i<j≤n xi ≠ xj is the conjunction of all wfs xi ≠ xj with 1 ≤ i < j 
≤ n. Then, if Kn is obtained from K1 by adding (En) as an axiom, Kn is 
n-categorical, and every normal model of Kn has exactly n elements.
	
2.	The theory K2 (see page 96) of densely ordered sets with neither first 
nor last element is ℵ0–categorical (see Kamke, 1950, p. 71: every denu-
merable normal model of K2 is isomorphic with the model consisting 
of the set of rational numbers under their natural ordering). But one 
can prove that K2 is not 𝔪–categorical for any 𝔪 different from ℵ0.
Exercises
2.90A	 Find a theory with equality that is not ℵ0–categorical but is 𝔪–categori-
cal for all 𝔪 > ℵ0. [Hint: Consider the theory GC of abelian groups 
(see page 96). For each integer n, let ny stand for the term (y + y) + ⋯ + y 
consisting of the sum of n ys. Add to GC the axioms (Bn):(∀x)(∃1y)(ny = x) 
for all n ≥ 2. The new theory is the theory of uniquely divisible abelian 
groups. Its normal models are essentially vector spaces over the field 
of rational numbers. However, any two vector spaces over the rational 
numbers of the same nondenumerable cardinality are isomorphic, and 
there are denumerable vector spaces over the rational numbers that are 
not isomorphic (see Bourbaki, 1947).]
2.91A	 Find a theory with equality that is 𝔪–categorical for all infinite cardi-
nals 𝔪. [Hint: Add to the theory GC of abelian groups the axiom (∀x1)
(2x1 = 0). The normal models of this theory are just the vector spaces 
over the field of integers modulo 2. Any two such vector spaces of the 
same cardinality are isomorphic (see Bourbaki, 1947).]
2.92	
Show that the theorems of the theory Kn in Example 1 above are pre-
cisely the set of all wfs of Kn that are true in all normal models of 
cardinality n.



113
First-Order Logic and Model Theory
2.93A	 Find two nonisomorphic densely ordered sets of cardinality 2
0
ℵ 
with neither first nor last element. (This shows that the theory K2 of 
Example 2 is not 2
0
ℵ–categorical.)
	Is there a theory with equality that is 𝔪–categorical for some noncountable 
cardinal 𝔪 but not 𝔪–categorical for some other noncountable cardinal 
𝔫? In Example 2 we found a theory that is only ℵ0-categorical; in Exercise 
2.90 we found a theory that is 𝔪–categorical for all infinite 𝔪 > ℵ0 but not 
ℵ0–­categorical, and in Exercise 2.91, a theory that is 𝔪–categorical for any 
infinite  𝔪. The elementary theory G of groups is not 𝔪–categorical  for 
any  infinite  𝔪. The problem is whether these four cases exhaust all the 
­possibilities. That this is so was proved by Morley (1965).
2.12  Generalized First-Order Theories: 
Completeness and Decidability*
If, in the definition of the notion of first-order language, we allow a non-
countable number of predicate letters, function letters, and individual con-
stants, we arrive at the notion of a generalized first-order language. The notions 
of interpretation and model extend in an obvious way to a generalized first-
order language. A generalized first-order theory in such a language is obtained 
by taking as proper axioms any set of wfs of the language. Ordinary first-
order theories are special cases of generalized first-order theories. The reader 
may easily check that all the results for first-order theories, through Lemma 
2.12, hold also for generalized first-order theories without any changes in 
the proofs. Lemma 2.13 becomes Lemma 2.13′: if the set of symbols of a gen-
eralized theory K has cardinality ℵα, then the set of expressions of K also 
can be well-ordered and has cardinality ℵα. (First, fix a well-ordering of the 
symbols of K. Second, order the expressions by their length, which is some 
positive integer, and then stipulate that if e1 and e2 are two distinct expres-
sions of the same length k, and j is the first place in which they differ, then e1 
precedes e2 if the jth symbol of e1 precedes the jth symbol of e2 according to the 
given well-ordering of the symbols of K.) Now, under the same assumption 
as for Lemma 2.13′, Lindenbaum’s Lemma 2.14′ can be proved for generalized 
theories much as before, except that all the enumerations (of the wfs Bi and of 
the theories Ji) are transfinite, and the proof that J is consistent and complete 
uses transfinite induction. The analogue of Henkin’s Proposition 2.17 runs 
as follows.
*	 Presupposed in parts of this section is a slender acquaintance with ordinal and cardinal 
numbers (see Chapter 4; or Kamke, 1950; or Sierpinski, 1958).



114
Introduction to Mathematical Logic
Proposition 2.33
If the set of symbols of a consistent generalized theory K has cardinality ℵα, 
then K has a model of cardinality ℵα.
Proof
The original proof of Lemma 2.15 is modified in the following way. Add 
ℵα new individual constants b1, b2, …, bλ, …. As before, the new theory 
K0 is consistent. Let F x
F x
i
i
1
1
(
),
,
(
),
(
)
…
…
<
λ
α
λ
λ
ω
 be a sequence consist-
ing of all wfs of K0 with exactly one free variable. Let (Sλ) be the sentence 
(
)
(
)
(
)
∃
¬
⇒¬
x
F x
F b
i
i
j
λ
λ
λ
λ
λ
, where the sequence b
b
b
j
j
j
1
2
,
,
,
…
…
λ
 of distinct indi-
vidual constants is chosen so that bjλ does not occur in F xi
β
β
(
)  for β ≤ λ. The 
new theory K∞, obtained by adding all the wfs (Sλ) as axioms, is proved to 
be consistent by a transfinite induction analogous to the inductive proof 
in Lemma 2.15. K∞ is a scapegoat theory that is an extension of K and con-
tains ℵα closed terms. By the extended Lindenbaum Lemma 2.14′, K∞ can 
be extended to a consistent, complete scapegoat theory J with ℵα closed 
terms. The same proof as in Lemma 2.16 provides a model M of J of cardi-
nality ℵα.
Corollary 2.34
	
a.	If the set of symbols of a consistent generalized theory with equality 
K has cardinality ℵα, then K has a normal model of cardinality less 
than or equal to ℵα.
	
b.	If, in addition, K has an infinite normal model (or if K has arbitrarily 
large finite normal models), then K has a normal model of any cardi-
nality ℵβ ≥ ℵα.
	
c.	In particular, if K is an ordinary theory with equality (i.e., ℵα = ℵ0) 
and K has an infinite normal model (or if K has arbitrarily large 
finite normal models), then K has a normal model of any cardinality 
ℵβ(β ≥ 0).
Proof
	
a.	The model guaranteed by Proposition 2.33 can be contracted to a 
normal model consisting of equivalence classes in a set of cardinal-
ity ℵα. Such a set of equivalence classes has cardinality less than or 
equal to ℵα.
	
b.	Assume ℵβ ≥ ℵα. Let b1, b2, … be a set of new individual constants of 
cardinality ℵβ, and add the axioms bλ ≠ bμ for λ ≠ μ. As in the proof 
of Corollary 2.27, this new theory is consistent and so, by (a), has a 



115
First-Order Logic and Model Theory
normal model of cardinality less than or equal to ℵβ (since the new 
theory has ℵβ new symbols). But, because of the axioms bλ ≠ bμ, the 
normal model has exactly ℵβ elements.
	
c.	This is a special case of (b).
Exercise
2.94	 If the set of symbols of a predicate calculus with equality K has 
­cardinality ℵα, prove that there is an extension K′ of K (with the same 
symbols as K) such that K′ has a normal model of cardinality ℵα, but K′ 
has no normal model of cardinality less than ℵα.
From Lemma 2.12 and Corollary 2.34(a,b), it follows easily that, if a gen-
eralized theory with equality K has ℵα symbols, is ℵβ-categorical for some 
β ≥ α, and has no finite models, then K is complete, in the sense that, for any 
closed wf B, either ⊢K B or ⊢K ¬B (Vaught, 1954). If not-⊢K B and not-⊢K ¬B, 
then the theories K′ = K + {¬B} and K′′ = K + {B} are consistent by Lemma 
2.12, and so, by Corollary 2.34(a), there are normal models M′ and M″ of K′ 
and K″, respectively, of cardinality less than or equal to ℵα. Since K has no 
finite models, M′ and M″ are infinite. Hence, by Corollary 2.34(b), there are 
normal models N′ and N″ of K′ and K″, respectively, of cardinality ℵβ. By the 
ℵβ-categoricity of K, N′ and N″ must be isomorphic. But, since ¬B is true in 
N′ and B is true in N′′, this is impossible by Proposition 2.32(b). Therefore, 
either ⊢K B or ⊢K ¬B.
In particular, if K is an ordinary theory with equality that has no 
finite models and is ℵβ-categorical for some β ≥ 0, then K is complete. 
As an example, consider the theory K2 of densely ordered sets with nei-
ther first nor last element (see page 96). K2 has no finite models and is 
ℵ0-categorical.
If an ordinary theory K is axiomatic (i.e., one can effectively decide whether 
any wf is an axiom) and complete, then K is decidable, that is, there is an 
effective procedure to determine whether any given wf is a theorem. To see 
this, remember (see page 84) that if a theory is axiomatic, one can effectively 
enumerate the theorems. Any wf B is provable if and only if its closure is 
provable. Hence, we may confine our attention to closed wfs B. Since K is 
complete, either B is a theorem or ¬B is a theorem, and, therefore, one or the 
other will eventually turn up in our enumeration of theorems. This provides 
an effective test for theoremhood. Notice that, if K is inconsistent, then every 
wf is a theorem and there is an obvious decision procedure; if K is consistent, 
then not both B and ¬B can show up as theorems and we need only wait until 
one or the other appears.
If an ordinary axiomatic theory with equality K has no finite models and is 
ℵβ-categorical for some β ≥ 0, then, by what we have proved, K is decidable. 
In particular, the theory K2 discussed above is decidable.



116
Introduction to Mathematical Logic
In certain cases, there is a more direct method of proving completeness 
or decidability. Let us take as an example the theory K2 of densely ordered 
sets with neither first nor last element. Langford (1927) has given the fol-
lowing procedure for K2. Consider any closed wf B. By Proposition 2.30, 
we can assume that B is in prenex normal form (Q1y1) … (Qnyn)C, where 
C contains no quantifiers. If (Qnyn) is (∀yn), replace (∀yn)C by ¬(∃yn)¬C. In 
all cases, then, we have, at the right side of the wf, (∃yn)D, where D has no 
quantifiers. Any negation x ≠ y can be replaced by x < y ∨ y < x, and ¬(x < y) 
can be replaced by x = y ∨ y < x. Hence, all negation signs can be eliminated 
from D. We can now put D into disjunctive normal form, that is, a disjunc-
tion of conjunctions of atomic wfs (see Exercise 1.42). Now (∃yn)(D1 ∨ D2 ∨ 
… ∨ Dk) is equivalent to (∃yn)D1 ∨ (∃yn)D2 ∨ … ∨ (∃yn)Dk. Consider each (∃yn)
Di separately. Di is a conjunction of atomic wfs of the form t < s and t = s. If 
Di does not contain yn, just erase (∃yn). Note that, if a wf E does not contain 
yn, then (∃yn)(E ∧ F  ) may be replaced by E ∧ (∃yn)F. Hence, we are reduced 
to the consideration of (∃yn)F, where F is a conjunction of atomic wfs of the 
form t < s or t = s, each of which contains yn. Now, if one of the conjuncts is 
yn = z for some z different from yn, then replace in F  all occurrences of yn by 
z and erase (∃yn). If we have yn = yn alone, then just erase (∃yn). If we have 
yn = yn as one conjunct among others, then erase yn = yn. If F  has a conjunct 
yn < yn, then replace all of (∃yn)F  by yn < yn. If F  consists of yn < z1 ∧ … ∧ yn 
< zj ∧ u1 < yn ∧ … ∧ um < yn, then replace (∃yn)F  by the conjunction of all the 
wfs ui < zp for 1 ≤ i ≤ m and 1 ≤ p ≤ j. If all the uis or all the zps are missing, 
replace (∃yn)F   by yn = yn. This exhausts all possibilities and, in every case, 
we have replaced (∃yn)F  by a wf containing no quantifiers, that is, we have 
eliminated the quantifier (∃yn). We are left with (Q1y1) … (Qn−1yn−1)G, where G 
contains no quantifiers. Now we apply the same procedure successively to 
(Qn−1yn−1), …, (Q1y1). Finally we are left with a wf without quantifiers, built 
up of wfs of the form x = x and x < x. If we replace x = x by x = x ⇒ x = x 
and x < x by ¬(x = x ⇒ x = x), the result is either an instance of a tautology 
or the negation of such an instance. Hence, by Proposition 2.1, either the 
result or its negation is provable. Now, one can easily check that all the 
replacements we have made in this whole reduction procedure applied to B 
have been replacements of wfs H  by other wfs U such that ⊢K H ⇔ U. Hence, 
by the replacement theorem, if our final result R is provable, then so is the 
original wf B, and, if ¬R is provable, then so is ¬B. Thus, K2 is complete and 
decidable.
The method used in this proof, the successive elimination of existential 
quantifiers, has been applied to other theories. It yields a decision procedure 
(see Hilbert and Bernays, 1934, §5) for the pure theory of equality K1 (see 
page 96). It has been applied by Tarski (1951) to prove the completeness and 
decidability of elementary algebra (i.e., of the theory of real-closed fields; see 
van der Waerden, 1949) and by Szmielew (1955) to prove the decidability of 
the theory GC of abelian groups.



117
First-Order Logic and Model Theory
Exercises
2.95	 (Henkin, 1955) If an ordinary theory with equality K is finitely axi-
omatizable and ℵα-categorical for some α, prove that K is decidable.
2.96	 a.	 Prove the decidability of the pure theory K1 of equality.
	
b.	 Give an example of a theory with equality that is ℵα-categorical for 
some α, but is incomplete.
2.12.1  Mathematical Applications
	
1.	Let F be the elementary theory of fields (see page 96). We let n 
stand for the term 1 + 1 + ⋯ + 1, consisting of the sum of n 1s. Then 
the assertion that a field has characteristic p can be expressed by 
the wf Cp: p = 0. A field has characteristic 0 if and only if it does 
not have characteristic p for any prime p. Then for any closed wf 
B of F that is true for all fields of characteristic 0, there is a prime 
number q such that B is true for all fields of characteristic greater 
than or equal to q. To see this, notice that, if F0 is obtained from 
F by adding as axioms ¬C2, ¬C3, …, ¬Cp, … (for all primes p), the 
normal models of F0 are the fields of characteristic 0. Hence, by 
Exercise 2.77, ⊢F0 B . But then, for some finite set of new axioms 
¬
¬
¬
C
C
C
q
q
qn
1
2
,
,
,
…
, we have ¬
¬
¬
C
C
C
B
q
q
qn
1
2
,
,
,
.
…
⊢F
 Let q be a prime 
greater than all q1, …, qn, In every field of characteristic greater 
than or equal to q, the wfs ¬
¬
¬
C
C
C
q
q
qn
1
2
,
,
,
…
 are true; hence, B is also 
true. (Other applications in algebra may be found in A. Robinson 
(1951) and Cherlin (1976).)
	
2.	A graph may be considered as a set with a symmetric binary rela-
tion R (i.e., the relation that holds between two vertices if and 
only if they are connected by an edge). Call a graph k-colorable 
if and only if the graph can be divided into k disjoint (possibly 
empty) sets such that no two elements in the same set are in the 
relation R. (Intuitively, these sets correspond to k colors, each color 
being painted on the points in the corresponding set, with the pro-
viso that two points connected by an edge are painted different 
colors.) Notice that any subgraph of a k-colorable graph is k-color-
able. Now we can show that, if every finite subgraph of a graph G 
is k-colorable, and if G can be well-ordered, then the whole graph 
G is k-colorable. To prove this, construct the following generalized 
theory with equality K (Beth, 1953). There are two binary predi-
cate letters, A1
2( )
=  and A2
2 (corresponding to the relation R on G); 
there are k monadic predicate letters A
Ak
1
1
1
,
,
…
 (corresponding to 
the k subsets into which we hope to divide the graph); and there 
are individual constants ac, one for each element c of the graph G. 



118
Introduction to Mathematical Logic
As proper axioms, in addition to the usual assumptions (A6) and 
(A7), we have the following wfs:
	
I.	¬A x x
2
2( , ) 	
(irreflexivity of R)
	
II.	A x y
A y x
2
2
2
2
( , )
( , )
⇒
	
(symmetry of R)
	
III.	(
)(
( )
( )
( ))
∀
∨
∨
∨
x A x
A x
A x
k
1
1
2
1
1
…
	 (division into k classes)
	
IV.	(
)
(
( )
( ))
∀
¬
∧
x
A x
A x
j
i
1
1
	
(disjointness of the k classes)
	
	 	
for 1 ≤ i < j ≤ k	
V.	(
)(
)(
( )
( )
∀
∀
∧
⇒
x
y A x
A y
i
i
1
1
	
(two elements of the same
	
	 ¬
≤≤
A x y
i
k
2
2
1
( , )) for
	
class are not in the relation R)
	
VI.	ab ≠ ac,	
for any two distinct elements b 
and c of G
	
VII.	A a a
b
c
2
2(
,
), ,	
if R(b, c) holds in G
Now, any finite set of these axioms involves only a finite number of the indi-
vidual constants a
a
c
cn
1,
,
…
, and since the corresponding subgraph {c1, …, cn}
is, by assumption, k-colorable, the given finite set of axioms has a model 
and is, therefore, consistent. Since any finite set of axioms is consistent, K 
is consistent. By Corollary 2.34(a), K has a normal model of cardinality less 
than or equal to the cardinality of G. This model is a k-colorable graph and, 
by (VI)–(VII), has G as a subgraph. Hence G is also k-colorable. (Compare this 
proof with a standard mathematical proof of the same result by de Bruijn and 
Erdös (1951). Generally, use of the method above replaces complicated appli-
cations of Tychonoff’s theorem or König’s Unendlichkeits lemma.)
Exercises
2.97A	(Loś, 1954b) A group B is said to be orderable if there exists a binary 
relation R on B that totally orders B such that, if xRy, then (x + z)
R(y + z) and (z + x)R(z + y). Show, by a method similar to that used 
in Example 2 above, that a group B is orderable if and only if every 
finitely generated subgroup is orderable (if we assume that the set B 
can be well-ordered).
2.98A	Set up a theory for algebraically closed fields of characteristic p(≥ 0) by 
adding to the theory F of fields the new axioms Pn, where Pn states that 
every nonconstant polynomial of degree n has a root, as well as axioms 
that determine the characteristic. Show that every wf of F that holds for 
one algebraically closed field of characteristic 0 holds for all of them. 
[Hint: This theory is ℵβ-categorical for β > 0, is axiomatizable, and has 
no finite models. See A. Robinson (1952).]
2.99	 By ordinary mathematical reasoning, solve the finite marriage problem. 
Given a finite set M of m men and a set N of women such that each man 
knows only a finite number of women and, for 1 ≤ k ≤ m, any subset 



119
First-Order Logic and Model Theory
of M having k elements knows at least k women of N (i.e., there are at 
least k women in N who know at least one of the k given men), then it is 
possible to marry (monogamously) all the men of M to women in N so 
that every man is married to a women whom he knows. [Hint (Halmos 
and Vaughn, 1950): m = 1 is trivial. For m > 1, use induction, consider-
ing the cases: (I) for all k with 1 ≤ k < m, every set of k men knows at 
least k + 1 women; and (II) for some k with 1 ≤ k < m, there is a set of k 
men knowing exactly k women.] Extend this result to the infinite case, 
that is, when M is infinite and well-orderable and the assumptions 
above hold for all finite k. [Hint: Construct an appropriate generalized 
theory with equality, analogous to that in Example 2 above, and use 
Corollary 2.34(a).]
2.100	Prove that there is no generalized theory with equality K, having one 
predicate letter < in addition to =, such that the normal models of K are 
exactly those normal interpretations in which the interpretation of < is 
a well-ordering of the domain of the interpretation.
Let B be a wf in prenex normal form. If B is not closed, form its closure 
instead. Suppose, for example, B is (∃y1)(∀y2)(∀y3)(∃y4)(∃y5)(∀y6)C (y1, y2, y3, 
y4, y5, y6), where C contains no quantifiers. Erase (∃y1) and replace y1 in C  by 
a new individual constant b1: (∀y2)(∀y3)(∃y4)(∃y5)(∀y6) C (b1, y2, y3, y4, y5, y6). 
Erase (∀y2) and (∀y3), obtaining (∃y4)(∃y5)(∀y6)C (b1, y2, y3, y4, y5, y6). Now 
erase (∃y4) and replace y4 in C  by g(y2, y3), where g is a new function letter: 
(∃y5)(∀y6)C (b1, y2, y3, g(y2, y3), y5, y6). Erase (∃y5) and replace y5 by h(y2, y3), 
where h is another new function letter: (∀y6)C (b1, y2, y3, g(y2, y3), h(y2, y3), y6). 
Finally, erase (∀y6). The resulting wf C (b1, y2, y3, g(y2, y3), h(y2, y3), y6) con-
tains no quantifiers and will be denoted by B*. Thus, by introducing new 
function letters and individual constants, we can eliminate the quantifiers 
from a wf.
Examples
	
1.	If B is (∀y1)(∃y2)(∀y3)(∀y4)(∃y5)C (y1, y2, y3, y4, y5), where C is quantifier-
free, then B* is of the form C (y1, g(y1), y3, y4, h(y1, y3, y4)).
	
2.	If B is (∃y1)(∃y2)(∀y3)(∀y4)(∃y5)C (y1, y2, y3, y4, y5), where C is quantifier-
free, then B* is of the form C (b, c, y3, y4, g(y3, y4)).
Notice that B * ⊢ B, since we can put the quantifiers back by applications 
of Gen and rule E4. (To be more precise, in the process of obtaining B*, we 
drop all quantifiers and, for each existentially quantified variable yi, we 
substitute a term g(z1, …, zk), where g is a new function letter and z1, …, zk 
are the variables that were universally quantified in the prefix preceding 
(∃yi). If there are no such variables z1, …, zk, we replace yi by a new indi-
vidual constant.)



120
Introduction to Mathematical Logic
Proposition 2.35 (Second ε-Theorem)
(Rasiowa, 1956; Hilbert and Bernays, 1939) Let K be a generalized theory. 
Replace each axiom B of K by B*. (The new function letters and individual 
constants introduced for one axiom are to be different from those introduced 
for another axiom.) Let K* be the generalized theory with the proper axi-
oms B*. Then:
	
a.	If D is a wf of K and ⊢K*D , then ⊢K D.
	
b.	K is consistent if and only if K* is consistent.
Proof
	
a.	Let D be a wf of K such that ⊢K*D . Consider the ordinary theory K° 
whose axioms B1, …, Bn are such that B1*, …, Bn* are the axioms used 
in the proof of D. Let K○* be the theory whose axioms are B1*, …, Bn*. 
Hence ⊢K*D . Assume that M is a denumerable model of K°. We may 
assume that the domain of M is the set P of positive integers (see 
Exercise 2.88). Let B be any axiom of K°. For example, suppose that B 
has the form (∃y1)(∀y2)(∀y3)(∃y4)C (y1, y2, y3, y4), where C is quantifier-
free. B* has the form C (b, y2, y3, g(y2, y3)). Extend the model M step by 
step in the following way (noting that the domain always remains P); 
since B is true for M, (∃y1)(∀y2)(∀y3) (∃y4)C (y1, y2, y3, y4) is true for M. 
Let the interpretation b* of b be the least positive integer y1 such that 
(∀y2)(∀y3)(∃y4) C (y1, y2, y3, y4) is true for M. Hence, (∃y4)C (b, y2, y3, y4) is 
true in this extended model. For any positive integers y2 and y3, let 
the interpretation of g(y2, y3) be the least positive integer y4 such that 
C (b, y2, y3, y4) is true in the extended model. Hence, C  (b, y2, y3, g(y2, y3)) 
is true in the extended model. If we do this for all the axioms B of K°, 
we obtain a model M* of K°*. Since ⊢K°*D D
,
 is true for M*. Since M* 
differs from M only in having interpretations of the new individual 
constants and function letters, and since D does not contain any of 
those symbols, D is true for M. Thus, D is true in every denumerable 
model of K°. Hence, ⊢K° D, by Corollary 2.20(a). Since the axioms of 
K° are axioms of K, we have ⊢K D. (For a constructive proof of an 
equivalent result, see Hilbert and Bernays (1939).)
	
b.	Clearly, K* is an extension of K, since B * ⊢ B. Hence, if K* is consis-
tent, so is K. Conversely, assume K is consistent. Let D be any wf of 
K. If K* is inconsistent, ⊢K*D ∧ ¬ D. By (a), ⊢K D ∧ ¬D, contradicting the 
consistency of K.
Let us use the term generalized completeness theorem for the proposition that 
every consistent generalized theory has a model. If we assume that every set 
can be well-ordered (or, equivalently, the axiom of choice), then the general-
ized completeness theorem is a consequence of Proposition 2.33.



121
First-Order Logic and Model Theory
By the maximal ideal theorem (MI) we mean the proposition that every proper 
ideal of a Boolean algebra can be extended to a maximal ideal.* This is equiva-
lent to the Boolean representation theorem, which states that every Boolean 
algebra is isomorphic to a Boolean algebra of sets (Compare Stone 1936). For 
the theory of Boolean algebras, see Sikorski (1960) or Mendelson (1970). The 
usual proofs of the MI theorem use the axiom of choice, but it is a remarkable 
fact that the MI theorem is equivalent to the generalized completeness theo-
rem, and this equivalence can be proved without using the axiom of choice.
Proposition 2.36
(Loś, 1954a; Rasiowa and Sikorski, 1951, 1952) The generalized completeness 
theorem is equivalent to the maximal ideal theorem.
Proof
	
a.	Assume the generalized completeness theorem. Let B be a Boolean 
algebra. Construct a generalized theory with equality K having the 
binary function letters ∪ and ∩, the singulary function letter f1
1 [we 
denote f
t
1
1( ) by t ], predicate letters=and A1
1, and, for each element b 
in B, an individual constant ab. By the complete description of B, we 
mean the following sentences: (i) ab ≠ ac if b and c are distinct ele-
ments of B; (ii) ab ∪ ac = ad if b, c, d are elements of B such that b ∪ c = d 
in B; (iii) ab ∩ ac = ae if b, c, e are elements of b such that b ∩ c = e in B; 
and (iv) a
a
b
c
=
 if b and c are elements of B such that b
c
=  in B, where b 
denotes the complement of b. As axioms of K we take a set of axioms 
for a Boolean algebra, axioms (A6) and (A7) for equality, the complete 
description of B, and axioms asserting that A1
1 determines a maxi-
mal ideal (i.e., A x
x
1
1(
)
∩
, A x
A y
A x
y
1
1
1
1
1
1
( )
( )
(
),
∧
⇒
∪
 A x
A x
y
1
1
1
1
( )
(
),
⇒
∩
 
A x
A x
1
1
1
1
( )
( )
∨
, and ¬
∪
A x
x
1
1(
)). Now K is consistent, for, if there were 
a proof in K of a contradiction, this proof would contain only a 
finite number of the symbols ab, ac, …—say, a
a
b
bn
1,
,
…
. The elements 
b1, …, bn generate a finite subalgebra B′ of B. Every finite Boolean 
algebra clearly has a maximal ideal. Hence, B′ is a model for the wfs 
that occur in the proof of the contradiction, and therefore the contra-
diction is true in B′, which is impossible. Thus, K is consistent and, by 
the generalized completeness theorem, K has a model. That model 
can be contracted to a normal model of K, which is a Boolean alge-
bra A with a maximal ideal I. Since the complete description of B is 
included in the axioms of K, B is a subalgebra of A, and then I ∩ B is 
a maximal ideal in B.
*	 Since {0} is a proper ideal of a Boolean algebra, this implies (and is implied by) the proposition 
that every Boolean algebra has a maximal ideal.



122
Introduction to Mathematical Logic
	
b.	Assume the maximal ideal theorem. Let K be a consistent gener-
alized theory. For each axiom B of K, form the wf B* obtained by 
constructing a prenex normal form for B and then eliminating the 
quantifiers through the addition of new individual constants and 
function letters (see the example preceding the proof of Proposition 
2.35). Let K# be a new theory having the wfs B*, plus all instances of 
tautologies, as its axioms, such that its wfs contain no quantifiers and 
its rules of inference are modus ponens and a rule of substitution 
for variables (namely, substitution of terms for variables). Now, K# is 
consistent, since the theorems of K# are also theorems of the consis-
tent K* of Proposition 2.35. Let B be the Lindenbaum algebra deter-
mined by K# (i.e., for any wfs C and D, let C Eq D mean that ⊢K# C  ⇔ D; 
Eq is an equivalence relation; let [C] be the equivalence class of C; 
define [C] ∪ [D] = [C ∨ D], [ ]
[
]
[
], [ ]
[
]
C
D
C
D
C
C
∩
=
∧
= ¬
; under these 
operations, the set of equivalence classes is a Boolean algebra, called 
the Lindenbaum algebra of K#). By the maximal ideal theorem, let I 
be a maximal ideal in B. Define a model M of K# having the set of 
terms of K# as its domain; the individual constants and function let-
ters are their own interpretations, and, for any predicate letter Aj
n, we 
say that A t
t
j
n
n
( ,
,
)
1 …
 is true in M if and only if [
( ,
,
)]
A t
t
j
n
n
1 …
 is not 
in I. One can show easily that a wf C of K# is true in M if and only if 
[C] is not in I. But, for any theorem D of K#, [D] = 1, which is not in I. 
Hence, M is a model for K#. For any axiom B of K, every substitution 
instance of B*(y1, …, yn) is a theorem in K#; therefore, B*(y1, …, yn) is 
true for all y1, …, yn in the model. It follows easily, by reversing the 
process through which B* arose from B, that B is true in the model. 
Hence, M is a model for K.
The maximal ideal theorem (and, therefore, also the generalized complete-
ness theorem) turns out to be strictly weaker than the axiom of choice (see 
Halpern, 1964).
Exercise
2.101	 Show that the generalized completeness theorem implies that every 
set can be totally ordered (and, therefore, that the axiom of choice 
holds for any set of nonempty disjoint finite sets).
The natural algebraic structures corresponding to the propositional calcu-
lus are Boolean algebras (see Exercise 1.60, and Rosenbloom, 1950, Chapters 
1 and 2). For first-order theories, the presence of quantifiers introduces more 
algebraic structure. For example, if K is a first-order theory, then, in the cor-
responding Lindenbaum algebra B, [(∃x)B(x)] = Σt[B(t)], where Σt indicates 
the least upper bound in B, and t ranges over all terms of K that are free 
for x in B(x). Two types of algebraic structure have been proposed to serve 



123
First-Order Logic and Model Theory
as algebraic counterparts of quantification theory. The first, cylindrical alge-
bras, have been studied extensively by Tarski, Thompson, Henkin, Monk, 
and others (see Henkin et al., 1971). The other approach is the theory of poly-
adic algebras, invented and developed by Halmos (1962).
2.13  Elementary Equivalence: Elementary Extensions
Two interpretations M1 and M2 of a generalized first-order language L  are said 
to be elementarily equivalent (written M1 ≡ M2) if the sentences of L  true for M1 are 
the same as the sentences true for M2. Intuitively, M1 ≡ M2 if and only if M1 and 
M2 cannot be distinguished by means of the language L. Of course, since L   is a 
generalized first-order language, L   may have nondenumerably many symbols.
Clearly, (1) M ≡ M; (2) if M1 ≡ M2, then M2 ≡ M1; (3) if M1 ≡ M2 and M2 ≡ M3, 
then M1 ≡ M3.
Two models of a complete theory K must be elementarily equivalent, since 
the sentences true in these models are precisely the sentences provable in K. 
This applies, for example, to any two densely ordered sets without first or 
last elements (see page 115).
We already know, by Proposition 2.32(b), that isomorphic models are ele-
mentarily equivalent. The converse, however, is not true. Consider, for exam-
ple, any complete theory K that has an infinite normal model. By Corollary 
2.34(b), K has normal models of any infinite cardinality ℵα. If we take two 
normal models of K of different cardinality, they are elementarily equivalent 
but not isomorphic. A concrete example is the complete theory K2 of densely 
ordered sets that have neither first nor last element. The rational numbers 
and the real numbers, under their natural orderings, are elementarily equiv-
alent nonisomorphic models of K2.
Exercises
2.102	 Let K∞, the theory of infinite sets, consist of the pure theory K1 of 
equality plus the axioms Bn, where Bn asserts that there are at least n 
elements. Show that any two models of K∞ are elementarily equiva-
lent (see Exercises 2.66 and 2.96(a)).
2.103D	 If M1 and M2 are elementarily equivalent normal models and M1 is 
finite, prove that M1 and M2 are isomorphic.
2.104	 Let K be a theory with equality having ℵα symbols.
	
a.	 Prove that there are at most 2ℵα models of K, no two of which are 
elementarily equivalent.
	
b.	 Prove that there are at most 2ℵλ mutually nonisomorphic models 
of K of cardinality ℵβ, where γ is the maximum of α and β.



124
Introduction to Mathematical Logic
2.105	 Let M be any infinite normal model of a theory with equality K hav-
ing ℵα symbols. Prove that, for any cardinal ℵγ ≥ ℵα, there is a normal 
model M* of K of cardinality ℵα such that M ≡ M*.
A model M2 of a language L is said to be an extension of a model M1 of L 
(written M1 ⊆ M2)* if the following conditions hold:
	
1.	 The domain D1 of M1 is a subset of the domain D2 of M2.
	
2.	 For any individual constant c of L, cM2 = cM1, where cM2 and cM1 are 
the interpretations of c in M2 and M1.
	
3.	 For any function letter fj
n of L and any b1,…, bn in D1, 
(
)
( ,
,
)
(
)
( ,
,
).
f
b
b
f
b
b
j
n
n
j
n
n
M
M
2
1
1
1
…
=
…
	
4.	 For any predicate letter Aj
n  of L and any b1, …, bn in D1, M1
1
A b
b
j
n
n
[ ,
,
]
…
 
if and only if M2
1
A b
b
j
n
n
[ ,
,
]
…
.
When M1 ⊆ M2, one also says that M1 is a substructure (or submodel) of M2.
Examples
	
1.	If L  contains only the predicate letters = and <, then the set of ratio-
nal numbers under its natural ordering is an extension of the set of 
integers under its natural ordering.
	
2.	If L  is the language of field theory (with the predicate letter =, func-
tion letters + and ×, and individual constants 0 and 1), then the field 
of real numbers is an extension of the field of rational numbers, the 
field of rational numbers is an extension of the ring of integers, and 
the ring of integers is an extension of the “semiring” of nonnegative 
integers. For any fields F1 and F2, F1 ⊆ F2 if and only if F1 is a subfield 
of F2 in the usual algebraic sense.
Exercises
2.106	 Prove:
	
a.	 M ⊆ M;
	
b.	 if M1 ⊆ M2 and M2 ⊆ M3, then M1 ⊆ M3;
	
c.	 If M1 ⊆ M2 and M2 ⊆ M1, then M1 = M2.
2.107	 Assume M1 ⊆ M2.
	
a.	 Let B(x1, …, xn) be a wf of the form (∀y1) … (∀ym)C (x1, …, xn, y1, …, ym), 
where C is quantifier-free. Show that, for any b1, …, bn in the domain 
of M1, if M2 B [ ,
,
]
b
bn
1 …
, then M1 B [ ,
,
]
b
bn
1 …
. In particular, any 
sentence (∀y1) … (∀ym) C (y1, …, ym), where C is quantifier-free, is true 
in M1 if it is true in M2.
*	 The reader will have no occasion to confuse this use of ⊆ with that for the inclusion relation.



125
First-Order Logic and Model Theory
	
b.	 Let B(x1, …, xn) be a wf of the form (∃y1) … (∃ym)C (x1, …, xn, y1, …, ym), 
where C is quantifier-free. Show that, for any b1, …, bn in the domain 
of M1, if M1 B [ ,
,
]
b
bn
1 …
, then M2 B [ ,
,
]
b
bn
1 …
. In particular, any 
sentence (∃y1) … (∃ym) C (y1, …, ym), where C is quantifier-free, is true 
in M2 if it is true in M1.
2.108	 a.	 Let K be the predicate calculus of the language of field theory. Find 
a model M of K and a nonempty subset X of the domain D of M 
such that there is no substructure of M having domain X.
	
b.	 If K is a predicate calculus with no individual constants or func-
tion letters, show that, if M is a model of K and X is a subset of the 
domain D of M, then there is one and only one substructure of M 
having domain X.
	
c.	 Let K be any predicate calculus. Let M be any model of K and let 
X be any subset of the domain D of M. Let Y be the intersection of 
the domains of all submodels M* of M such that X is a subset of the 
domain DM* of M*. Show that there is one and only one submodel of 
M having domain Y. (This submodel is called the submodel generated 
by X.)
A somewhat stronger relation between interpretations than “extension” is 
useful in model theory. Let M1 and M2 be models of some language L. We say 
that M2 is an elementary extension of M1 (written M1 ≤e M2) if (1) M1 ⊆ M2 and 
(2) for any wf B(y1, …, yn) of L and for any b1, …, bn in the domain D1 of M1, 
M1
1
B [ ,
,
]
b
bn
…
 if and only if M2
1
B [ ,
,
]
b
bn
…
. (In particular, for any sentence 
B of L, B is true for M1 if and only if B is true for M2.) When M1 ≤e M2, we shall 
also say that M1 is an elementary substructure (or elementary submodel) of M2.
It is obvious that, if M1 ≤e M2, then M1 ⊆ M2 and M1 ≡ M2. The converse is not 
true, as the following example shows. Let G be the elementary theory of groups 
(see page 96). G has the predicate letter =, function letter +, and individual con-
stant 0. Let I be the group of integers and E the group of even integers. Then E ⊆ I 
and I ≅ E. (The function g such that g(x) = 2x for all x in I is an isomorphism 
of I with E.) Consider the wf B(y): (∃x)(x + x = y). Then ⊧I B[2], but not-⊧E B[2]. Thus, 
I is not an elementary extension of E. (This example shows the stronger result 
that even assuming M1 ⊆ M2 and M1 ≅ M2 does not imply M1 ≤e M2.)
The following theorem provides an easy method for showing that M1 ≤e M2.
Proposition 2.37 (Tarski and Vaught, 1957)
Let M1 ⊆ M2. Assume the following condition:
($) For every wf B (x1, …, xk) of the form (∃y)C (x1, …, xk, y) and for all b1, …, bk in 
the domain D1 of M1, if .
[ ,
,
]
M2
1
B b
bk
…
, then there is some d in D1 such 
that M2
1
C [ ,
,
, ]
b
b
d
k
…
.
Then M1 ≤e M2.



126
Introduction to Mathematical Logic
Proof
Let us prove:
(*) M1
1
D[ ,
,
]
b
bk
…
 if and only if M2
1
D[ ,
,
]
b
bk
…
 for any wf D(x1, …, xk) and 
any b1, …, bk in D1.
The proof is by induction on the number m of connectives and quantifiers in D. 
If m = 0, then (*) follows from clause 4 of the definition of M1 ⊆ M2. Now assume 
that (*) holds true for all wfs having fewer than m connectives and quantifiers.
Case 1. D is ¬E. By inductive hypothesis, M1
1
E [ ,
,
]
b
bk
…
 if and only if 
M2
1
E [ ,
,
]
b
bk
…
. Using the fact that not-M1
1
E [ ,
,
]
b
bk
…
 if and only if 
M1
1
¬E [ ,
,
]
b
bk
…
, and similarly for M2, we obtain (*).
Case 2. D is E ⇒ F. By inductive hypothesis, M1
1
E [ ,
,
]
b
bk
…
 if and only if 
M2
1
E [ ,
,
]
b
bk
…
 and similarly for F. (*) then follows easily.
Case 3. D is (∃y)E(x1, …, xn, y). By inductive hypothesis,
(**) M1
1
E [ ,
,
, ]
b
b
d
k
…
 if and only if M2
1
E [ ,
,
, ]
b
b
d
k
…
, for any b1, …, bk, d in D1.
Case 3a. Assume M1
1
1
(
) (
,
,
,
)[ ,
,
]
∃
…
…
y
x
x
y b
b
k
k
E
 for some b1, …, bk in D1. 
Then M1
1
E [ ,
,
, ]
b
b
d
k
…
 for some d in D1. So, by (**), M2
1
E [ ,
,
, ]
b
b
d
k
…
. Hence, 
M2
1
1
(
) (
,
,
,
)[ ,
,
]
∃
…
…
y
x
x
y b
b
k
k
E
.
Case 3b. Assume M2
1
1
(
) (
,
,
,
)[ ,
,
]
∃
…
…
y
x
x
y b
b
k
k
E
 for some b1, …, bk in D1. By 
assumption ($), there exists d in D1 such that M2
1
E [ ,
,
, ]
b
b
d
k
…
. Hence, by (**), 
M1
1
E [ ,
,
, ]
b
b
d
k
…
 and therefore M1
1
1
(
) (
,
,
,
)[ ,
,
]
∃
…
…
y
x
x
y b
b
k
k
E
.
This completes the induction proof, since any wf is logically equivalent to 
a wf that can be built up from atomic wfs by forming negations, conditionals 
and existential quantifications.
Exercises
2.109	 Prove:
	
a.	 M ≤e M;
	
b.	 if M1 ≤e M2 and M2 ≤e M3, then M1 ≤e M3;
	
c.	 if M1 ≤e M and M2 ≤e M and M1 ⊆ M2, then M1 ≤e M2.
2.110	 Let K be the theory of totally ordered sets with equality (axioms (a)–
(c) and (e)–(g) of Exercise 2.67). Let M1 and M2 be the models for K 
with domains the set of positive integers and the set of nonnegative 
integers, respectively (under their natural orderings in both cases). 
Prove that M1 ⊆ M2 and M1 ≃ M2, but M1 ≰eM2.
Let M be an interpretation of a language L. Extend L to a language L * by 
adding a new individual constant ad for every member d of the domain of M. 
We can extend M to an interpretation of L * by taking d as the interpretation 



127
First-Order Logic and Model Theory
of ad. By the diagram of M we mean the set of all true sentences of M of the 
forms A
a
a
A
a
a
j
n
d
d
j
n
d
d
n
n
(
,
,
),
(
,
,
)
1
1
…
¬
…
, and f
a
a
a
j
n
d
d
d
n
m
(
,
,
)
1 …
=
. In particular, 
a
a
d
d
1
2
≠
 belongs to the diagram if d1 ≠ d2. By the complete diagram of M we 
mean the set of all sentences of L * that are true for M.
Clearly, any model M# of the complete diagram of M determines an ele-
mentary extension M## of M,* and vice versa.
Exercise
2.111	 a.	 Let M1 be a denumerable normal model of an ordinary theory K 
with equality such that every element of the domain of M1 is the 
interpretation of some closed term of K.
	
	
i.	 Show that, if M1 ⊆ M2 and M1 ≡ M2, then M1 ≤e M2.
	
	
ii.	 Prove that there is a denumerable normal elementary extension 
M3 of M1 such that M1 and M3 are not isomorphic.
	
b.	 Let K be a predicate calculus with equality having two function 
letters + and × and two individual constants 0 and 1. Let M be the 
standard model of arithmetic with domain the set of natural num-
bers, and +, ×, 0 and 1 having their ordinary meaning. Prove that 
M has a denumerable normal elementary extension that is not iso-
morphic to M, that is, there is a denumerable nonstandard model 
of arithmetic.
Proposition 2.38 (Upward Skolem–Löwenheim–Tarski Theorem)
Let K be a theory with equality having ℵα symbols, and let M be a normal 
model of K with domain of cardinality ℵβ. Let γ be the maximum of α and β. 
Then, for any δ ≥ γ, there is a model M* of cardinality ℵδ such that M ≠ M* 
and M ≤e M*.
Proof
Add to the complete diagram of M a set of cardinality ℵδ of new individual 
constants bτ, together with axioms bτ ≠ bρ for distinct τ and ρ and axioms 
bτ ≠ ad for all individual constants ad corresponding to members d of the 
domain of M. This new theory K# is consistent, since M can be used as a 
model for any finite number of axioms of K#. (If b
b
a
a
z
d
d
k
m
τ
τ
1
1
,
,
,
,
,
…
…
 are the 
new individual constants in these axioms, interpret b
b k
τ
τ
1 ,
,
…
 as distinct 
elements of the domain of M different from d1, …, dm.) Hence, by Corollary 
2.34(a), K# has a normal model M# of cardinality ℵδ such that M ⊆ M#, 
M ≠ M#, and M ≤e M#.
*	 The elementary extension M## of M is obtained from M# by forgetting about the interpreta-
tions of the ads.



128
Introduction to Mathematical Logic
Proposition 2.39 (Downward Skolem–Löwenheim–Tarski Theorem)
Let K be a theory having ℵα symbols, and let M be a model of K with domain 
of cardinality ℵγ ≥ ℵα. Assume A is a subset of the domain D of M having 
cardinality n, and assume ℵβ is such that ℵγ ≥ ℵβ ≥ max(ℵα, 𝔫). Then there 
is an elementary submodel M* of M of cardinality ℵβ and with domain D* 
including A.
Proof
Since 𝔫 ≤ ℵβ ≤ ℵγ, we can add ℵβ elements of D to A to obtain a larger set 
B of cardinality ℵβ. Consider any subset C of D having cardinality ℵβ. For 
every wf B(y1, …, yn, z) of K, and any c1, …, cn in C such that ⊧M (∃z)B(y1, …, 
yn, z)[c1, …, cn] , add to C the first element d of D (with respect to some fixed 
well-ordering of D) such that ⊧M (∃z)B[c1, …, cn, d] . Denote the so-enlarged 
set by C#. Since K has ℵα symbols, there are ℵα wfs. Since ℵα ≤ ℵβ, there 
are at most ℵβ new elements in C# and, therefore, the cardinality of C# is 
ℵβ. Form by induction a sequence of sets C0, C1, … by setting C0 = B and 
C
C
n
n
+ =
1
#. Let D* = ∪n∈ωCn. Then the cardinality of D* is ℵβ. In addition, D* 
is closed under all the functions (
)
fj
n M. (Assume d1, …, dn in D*. We may 
assume d1, …, dn in Ck for some k. Now M (
)(
(
,
,
)
)[ ,
,
].
∃
…
=
…
z
f
x
x
z d
d
j
n
n
n
1
1
 
Hence, (
) (
,
,
)
f
d
d
j
n
n
M
1 …
, being the first and only member d of D such that 
M (
(
,
,
)
)[ ,
,
, ]
f
x
x
z d
d
d
j
n
n
n
1
1
…
=
…
, must belong to C
C
D
k
k
# =
⊆
+1
*.) Similarly, 
all interpretations (aj)M of individual constants are in D*. Hence, D* deter-
mines a substructure M* of M. To show that M* ≤e M, consider any wf 
B (y1, …, yn, z) and any d1, …, dn in D* such that ⊧M(∃z)B(y1, …, yn, z) [d1, …, dn]. 
There exists Ck such that d1, …, dn are in Ck. Let d be the first element of D 
such that ⊧M B[d1, …, dn, d]. Then d
C
C
D
k
k
∈
=
⊆
+
#
1
*. So, by the Tarski–Vaught 
theorem (Proposition 2.37), M* ≤e M.
2.14  Ultrapowers: Nonstandard Analysis
By a filter* on a nonempty set A we mean a set F of subsets of A such that:
	
1.	A ∈ F
	
2.	B ∈ F ∧ C ∈ F ⇒ B ∩ C ∈ F
	
3.	B ∈ F ∧ B ⊆ C ∧ C ⊆ A ⇒ C ∈ F
*	 The notion of a filter is related to that of an ideal. A subset F  of P  (A) is a filter on A if and only 
if the set G = {A − B|B ∈ F} of complements of sets in F  is an ideal in the Boolean algebra P  (A). 
Remember that P  (A) denotes the set of all subsets of A.



129
First-Order Logic and Model Theory
Examples
Let B ⊆ A. The set FB = {C|B ⊆ C ⊆ A} is a filter on A. FB consists of all subsets 
of A that include B. Any filter of the form FB is called a principal filter. In par-
ticular, FA = {A} and F∅ = P(A) are principal filters. The filter P(A) is said to be 
improper and every other filter is said to be proper.
Exercises
2.112	 Show that a filter F  on A is proper if and only if ∅ ∉ F.
2.113	 Show that a filter F  on A is a principal filter if and only if the intersec-
tion of all sets in F  is a member of F.
2.114	 Prove that every finite filter is a principal filter. In particular, any filter 
on a finite set A is a principal filter.
2.115	 Let A be infinite and let F    be the set of all subsets of A that are comple-
ments of finite sets: F = {C|(∃W)(C = A − W ∧ Fin(W)}, where Fin(W) 
means that W is finite. Show that F  is a nonprincipal filter on A.
2.116	 Assume A has cardinality ℵβ. Let ℵα ≤ ℵβ. Let F  be the set of all sub-
sets of A whose complements have cardinality < ℵα. Show that F  is a 
nonprincipal filter on A.
2.117	 A collection G of sets is said to have the finite intersection property if B1 ∩ 
B2 ∩ … ∩ Bk ≠ ∅ for any sets B1, B2, …, Bk in G. If G is a collection of sub-
sets of A having the finite intersection property and H is the set of all 
finite intersections B1 ∩ B2 ∩ … ∩ Bk of sets in G, show that F = {D|(∃C)
(B ∈ H ∧ C ⊆ D ⊆ A)} is a proper filter on A.
Definition
A filter F on a set A is called an ultrafilter on A if F  is a maximal proper filter 
on A, that is, F is a proper filter on A and there is no proper filter G on A such 
that F ⊂ G.
Example
Let d ∈ A. The principal filter Fd = {B|d ∈ B ∧ B ⊆ A} is an ultrafilter on A. 
Assume that G is a filter on A such that Fd ⊂ G. Let C ∈ G − Fd. Then C ⊆ A and 
d ∉ C. Hence, d ∈ A − C. Thus, A − C ∈ Fd ⊂ G. Since G is a filter and C and 
A − C are both in G, then ∅ = C ∩ (A − C) ∈ G. Hence, G is not a proper filter.
Exercises
2.118	 Let F  be a proper filter on A and assume that B ⊆ A and A − B ∉ F. 
Prove that there is a proper filter F′ ⊇F  such that B ∈ F′.
2.119	 Let F  be a proper filter on A. Prove that F is an ultrafilter on A if and 
only if, for every B ⊆ A, either B ∈ F  or A − B ∈ F.



130
Introduction to Mathematical Logic
2.120	 Let F  be a proper filter on A. Show that F  is an ultrafilter on A if and 
only if, for all B and C in P  (A), if B ∉ F  and C ∉ F, then B ∪ C ¬ ∈ F.
2.121	 a.	Show that every principal ultrafilter on A is of the form Fd = {B|d ∈ 
B ∧ B ⊆ A} for some d in A.
	
	 b.	Show that a nonprincipal ultrafilter on A contains no finite sets.
2.122	 Let F  be a filter on A and let I   be the corresponding ideal: B ∈ I  if and 
only if A − B ∈ F. Prove that F  is an ultrafilter on A if and only if I  is 
a maximal ideal.
2.123	 Let X be a chain of proper filters on A, that is, for any B and C in X, 
either B ⊆ C or C ⊆ B. Prove that the union ∪X = {a|(∃B)(B ∈ X ∧ a ∈ B)} 
is a proper filter on A, and B ⊆ ∪X for all B in X.
Proposition 2.40 (Ultrafilter Theorem)
Every proper filter F on a set A can be extended to an ultrafilter on A.*
Proof
Let F   be a proper filter on A. Let I  be the corresponding proper ideal: B ∈ I 
if and only if A − B ∈ F. By Proposition 2.36, every ideal can be extended to 
a maximal ideal. In particular, I  can be extended to a maximal ideal H. If 
we let U  = {B|A − B ∈ H  }, then U is easily seen to be an ultrafilter and F  ⊆ U.
Alternatively, the existence of an ultrafilter including F  can be proved easily 
on the basis of Zorn’s lemma. (In fact, consider the set X of all proper filters F′ 
such that F   ⊆ F   ′. X is partially ordered by ⊂, and any ⊂ -chain in X has an upper 
bound in X, namely, by Exercise 2.123, the union of all filters in the chain. Hence, 
by Zorn’s lemma, there is a maximal element F   * in X, which is the required 
ultrafilter.) However, Zorn’s lemma is equivalent to the axiom of choice, which is 
a stronger assumption than the generalized completeness theorem.
Corollary 2.41
If A is an infinite set, there exists a nonprincipal ultrafilter on A.
Proof
Let F  be the filter on A consisting of all complements A − B of finite subsets 
B of A (see Exercise 2.115). By Proposition 2.40, there is an ultrafilter U ⊇F. 
Assume U is a principal ultrafilter. By Exercise 2.121(a), U = Fd for some d ∈ A. 
Then A − {d} ∈ F  ⊆ U. Also, {d} ∈ U. Hence, ∅ = {d} ∩ (A − {d}) ∈ U, contradicting 
the fact that an ultrafilter is proper.
*	 We assume the generalized completeness theorem.



131
First-Order Logic and Model Theory
2.14.1  Reduced Direct Products
We shall now study an important way of constructing models. Let K be any 
predicate calculus with equality. Let J be a nonempty set and, for each j in 
J, let Mj be some normal model of K. In other words, consider a function F 
assigning to each j in J some normal model. We denote F(j) by Mj.
Let F  be a filter on J. For each j in J, let Dj denote the domain of the model 
Mj. By the Cartesian product Πj∈JDj we mean the set of all functions f with 
domain J such that f(j) ∈ Dj for all j in J. If f ∈ Πj∈JDj, we shall refer to f(j) as 
the jth component of f. Let us define a binary relation =F in Πj∈JDj as follows:
	
f
g
j f j
g j
=
=
∈
F
F
if and only if
{ | ( )
( )}
If we think of the sets in F as being “large” sets, then, borrowing a phrase 
from measure theory, we read f =F g as “f(j) = g(j) almost everywhere.”
It is easy to see that =F is an equivalence relation: (1) f =F f; (2) if f =F g then 
g =F f; (3) if f =F g and g =F h, then f =F h. For the proof of (3), observe that 
{j|f(j) = g(j)} ∩ {j|g(j) = h(j)} ⊆ {j|f(j) = h(j)}. If {j|f(j) = g(j)} and {j|g(j) = h(j)} are 
in F, then so is their intersection and, therefore, also {j|f(j) = h(j)}.
On the basis of the equivalence relation =F  , we can divide Πj∈JDj into 
equivalence classes: for any f in Πj∈JDj, we define its equivalence class fF  as 
{g|f =F g}. Clearly, (1) f ∈ fF; (2) fF = hF  if and only if f =F h; and (3) if fF   ≠ hF, 
then fF  ∩ hF = ∅. We denote the set of equivalence classes fF  by Πj∈JDj/F. 
Intuitively, Πj∈JDj/F  is obtained from Πj∈JDj by identifying (or merging) ele-
ments of Πj∈JDj that are equal almost everywhere.
Now we shall define a model M of K with domain Πj∈JDj/F.
	
1.	Let c be any individual constant of K and let cj be the interpretation 
of c in Mj. Then the interpretation of c in M will be fF, where f is the 
function such that f(j) = cj for all j in J. We denote f by {cj}j∈J.
	
2.	Let fk
n be any function letter of K and let Ak
n be any predicate letter of 
K. Their interpretations (
)
fk
n M and (
)
Ak
n M are defined in the following 
manner. Let (g1)F, …, (gn)F  be any members of Πj∈JDj/F.
	
a.	 (
) ((
) ,
, (
) )
f
g
g
h
k
n
n
M
1 F
F
F
…
=
, where h j
f
g
j
g
j
k
n
n
j
( )
(
)
(
( ),
,
( ))
=
…
M
1
 
for all j in J.
	
b.	 (
) ((
) ,
, (
) )
A
g
g
k
n
n
M
1 F
F
…
 
holds 
if 
and 
only 
if 
{ |
j
j
M  
A
g j
g
j
k
n
n
[
( ),
,
( )]}
1
…
∈F .
Intuitively, (
)
fk
n M is calculated componentwise, and (
)
Ak
n M holds if and 
only if Ak
n holds in almost all components. Definitions (a) and (b) have 
to be shown to be independent of the choice of the representatives 
g1, …, gn in the equivalence classes (g1)F, …, (gn)F: if g
g
g
g
n
n
1
1
=
…
=
F
F
*
*
,
,
, 
and 
h
j
f
g
j
g
j
k
n
n
j
*
*
*
( )
(
)
(
( ),
,
( ))
=
…
M
1
, 
then 
(i) 
hF 
=F 
hF* 
and 
(ii) 
j
A
g j
g
j
j
k
n
n
|
[
( ),
,
( )]}
M
{
…
∈
1
F  if and only if j
A
g
j
g
j
j
k
n
n
|
[
( ),
,
( )]
.
M
*
*
1
…
{
}∈F



132
Introduction to Mathematical Logic
Part (i) follows from the inclusion:
	
{ |
( )
*( )}
{ |
( )
*( )}
|
(
( ),
,
(
j g
j
g
j
j g
j
g
j
j
f
g
j
g
j
n
n
k
n
n
j
1
1
1
=
∩… ∩
=
⊆
(
)
…
M
))
(
( ),
,
*( ))
= (
)
…
{
}
f
g
j
g
j
k
n
n
j
M
1 *
Part (ii) follows from the inclusions:
	
{ |
( )
*( )}
{ |
( )
*( )}
|
[
( ),
,
( )
j g
j
g
j
j g
j
g
j
j
A
g
j
g
j
n
n
k
n
n
j
1
1
1
=
…
=
⊆
…
∩
∩
M
]
[
( ),
,
*( )]
if and only if
*
M

j A
g
j
g
j
k
n
n
1
…
{
}
and
	
j
A
g
j
g
j
j
A
g
j
g
j
j
j
k
n
n
k
n
n
|
[
( ),
,
( )]
|
[
( ),
,
( )]


M
M
if and
onl
1
1
…
{
}
…
{
∩
y if
M
M


j
j
A
g
j
g
j
j
A
g
j
g
j
k
n
n
k
n
n
[ *( ),
,
*( )]
|
[ *( ),
,
*( )]
1
1
…
} ⊆
…
{
}
In the case of the equality relation =, which is an abbreviation for A1
2,
	
(
) (
,
)
|
[ ( ), ( )]
A
g
h
j
A g j h j
j
1
2
1
2
M
M
if and only if
if and only if
F
F
F

{
}∈
{ | ( )
( )}
j g j
h j
g
h
=
∈
=
F
F
if and only if
that is, if and only if gF = hF  . Hence, the interpretation (
)
A1
2 M is the identity 
relation and the model M is normal.
The model M just defined will be denoted Πj∈JMj/F and will be called a 
reduced direct product. When F  is an ultrafilter, Πj∈JMj/F is called an ultra-
product. When F  is an ultrafilter and all the Mjs are the same model N, then 
Πj∈JMj/F  is denoted NJ/F and is called an ultrapower.
Examples
	
1.	Choose a fixed element r of the index set J, and let F   be the prin-
cipal ultrafilter Fr = {B|r ∈ B ∧ B ⊆ J}. Then, for any f, g in Πj∈JDj, 
f =F g if and only if {j|f(j) = g(j)} ∈ F, that is, if and only if f(r) = 
g(r) . Hence, a member of Πj∈JDj/F consists of all f in Πj∈JDj that 
have the same rth component. For any predicate letter Ak
n of 
K and any g1, …, gn in Π j J
j
k
n
n
D
A
g
g
∈
…
,
[(
) ,
, (
) ]
M
1 F
F
 if and 
only if 
j
A
g j
g
j
j
k
n
n
|
[
( ),
,
( )]
M
1
…
{
}∈F , that is, if and only if 
Mr A
g j
g
j
k
n
n
[
( ),
,
( )]
1
…
. Hence, it is easy to verify that the function φ: 
Πj∈JDj/F → Dr, defined by φ(gF) = g(r) is an isomorphism of Πj∈JMj/F 
with Mr. Thus, when F  is a principal ultrafilter, the ultraproduct 
Πj∈JMj/F  is essentially the same as one of its components and yields 
nothing new.



133
First-Order Logic and Model Theory
	
2.	Let F be the filter {J}. Then, for any f, g in Πj∈JDj, f =F g if and only 
if {j|f(j) = g(j)} ∈ F, that is, if and only if f(j) = g(j) for all j in J, or 
if and only if f = g. Thus, every member of Πj∈JDj/F is a singleton 
{g} for some g in Πj∈JDj. Moreover, (
) ((
) ,
, (
) )
{ }
f
g
g
g
k
n M
n
1 F
F
…
=
, 
where g is such that g j
f
g j
g
j
k
n
n
j
( )
(
)
(
( ),
,
( ))
=
…
M
1
 for all j in J. Also, 
M A
g
g
k
n
n
[(
) ,
, (
) ]
1 F
F
…
 if and only if Mj A
g
j
g
j
k
n
n
[
( ),
,
( )]
1
…
 for all j 
in J. Hence, Πj∈JMj/F  is, in this case, essentially the same as the ordi-
nary “direct product” Πj∈JMj, in which the operations and relations 
are defined componentwise.
	
3.	Let F  be the improper filter P  (J). Then, for any f, g in Πj∈JDj, f =F g 
if and only if {j|f(j) = g(j)} ∈ F, that is, if and only if {j|f(j) = g(j)} ∈ 
P  (J). Thus, f =F g for all f and g, and Πj∈JDj/F consists of only one 
element. For any predicate letter A
A
f
f
k
n
k
n
,
[
,
,
]
M
F
F
…
 if and only if 
{
[ ( ),
,
( )]}
( )
j
A
f j
f j
P J
j
k
n
M
…
∈
; that is, every atomic wf is true.
The basic theorem on ultraproducts is due to Loś (1955b).
Proposition 2.42 (Loś’s Theorem)
Let F  be an ultrafilter on a set J and let M = Πj∈JMj/F  be an ultraproduct.
	
a.	Let s = ((g1)F, (g2)F, …) be a denumerable sequence of elements of 
Πj∈JDj/F. For each j in J, let sj be the denumerable sequence (g1(j), 
g2(j), …) in Dj. Then, for any wf B of K, s satisfies B in M if and only 
if {j|sj satisfies B in Mj} ∈ F.
	
b.	For any sentence B of K, B is true in Πj∈JMj/F   if and only if j
Mj
|
.

B
F
∈
 
(Thus, (b) asserts that a sentence B is true in an ultraproduct if and 
only if it is true in almost all components.)
Proof
	
a.	We shall use induction on the number m of connectives and quanti-
fiers in B. We can reduce the case m = 0 to the following subcases*: 
(i) A
x
x
k
n
i
in
(
,
,
)
1 …
; (ii) x
f
x
x
k
n
i
in
ℓ=
…
(
,
,
)
1
; and (iii) xℓ = ak. For subcase 
(i), s satisfies A
x
x
k
n
i
in
(
,
,
)
1 …
 if and only if M A
g
g
k
n
i
in
[(
) ,
, (
) ],
1 F
F
…
 
which is equivalent to { |
[
( ),
,
( )]}
j
A
g
j
g
j
j
n
k
n
i
i
M
1
…
∈F ; that is 
j s satisfies A
x
x
in M
F
j
k
n
i
i
j
n
|
(
,
,
)
1 …
{
}∈. Subcases (ii) and (iii) are han-
dled in similar fashion.
*	 A wf A t
t
k
n
n
( ,
,
)
1 …
 can be replaced by (
)
(
)(
(
,
,
))
∀
… ∀
=
∧…∧
=
⇒
…
u
u
u
t
u
t
A u
u
n
n
n
k
n
n
1
1
1
1
, and a 
wf x
f
t
t
k
n
n
=
…
( ,
,
)
1
 can be replaced by (
)
(
)(
(
,
,
))
∀
… ∀
=
∧…∧
=
⇒
=
…
z
z
z
t
z
t
x
f
z
z
n
n
n
k
n
n
1
1
1
1
. In 
this way, every wf is equivalent to a wf built up from wfs of the forms (i)–(iii) by applying 
connectives and quantifiers.



134
Introduction to Mathematical Logic
	
	 Now, let us assume the result holds for all wfs that have fewer than 
m connectives and quantifiers.
	
	 Case 1. B is ¬C. By inductive hypothesis, s satisfies C in M if and only 
if {j|sj satisfies C in Mj} ∈ F. s satisfies ¬C in M if and only if {j|sj sat-
isfies C in Mj} ∉ F. But, since F is an ultrafilter,the last condition is 
equivalent, by exercise 2.119, to {j|sj satisfies ¬C in Mj} ∈ F.
	
	 Case 2. B is C ∧ D. By inductive hypothesis, s satisfies C in M if and 
only if {j|sj satisfies C in Mj} ∈ F, and s satisfies D in M if and only if 
{j|sj satisfies D in Mj} ∈ F. Therefore, s satisfies C ∧ D if and only 
if both of the indicated sets belong to F. But, this is equivalent to their 
intersection belonging to F, which, in turn, is equivalent to {j|sj satisfies 
C ∧ D in Mj} ∈ F.
	
	 Case 3. B is (∃xi)C. Assume s satisfies (∃xi)C. Then there exists h in 
Πj∈JDj such that s′ satisfies C in M, where s′ is the same as s except that 
hF is the ith component of s′. By inductive hypothesis, s′ satisfies C  in 
M if and only if {j|sj′ satisfies C in Mj} ∈ F. Hence, {j|sj satisfies(∃xi)C 
in Mj} ∈ F, since, if sj′ satisfies C in Mj then sj satisfies (∃xi)C in Mj.
	
	   Conversely, assume W = {j|sj satisfies (∃xi)C in Mj} ∈ F. For each j in 
W, choose some sj′ such that sj′ is the same as sj except in at most the 
ith component and sj′ satisfies C. Now define h in Πj∈JDj as follows: 
for j in W, let h(j) be the ith component of sj′, and, for j ∉ W, choose h(j) 
to be an arbitrary element of Dj. Let s′′ be the same as s except that its 
ith component is hF. Then W
j s
M
j
j
⊆
∈
′′
{ |
}
satisfies
in
C
F . Hence, 
by the inductive hypothesis, s′′ satisfies C in M. Therefore, s satisfies 
(∃xi)C in M.
	
b.	This follows from part (a) by noting that a sentence B is true in a 
model if and only if some sequence satisfies B.
Corollary 2.43
If M is a model and F is an ultrafilter on J, and if M* is the ultrapower MJ/F, 
then M* ≡ M.
Proof
Let B be any sentence. Then, by Proposition 2.42(b), B is true in M* if and 
only if {j|B is true in Mj} ∈ F. If B is true in M, {j|B is true in Mj} = J ∈ F. If B 
is false in M, {j|B is true in Mj} = ∅ ∉ F.
Corollary 2.43 can be strengthened considerably. For each c in the domain 
D of M, let c# stand for the constant function such that c#(j) = c for all j in J. 
Define the function ψ such that, for each c in D, ψ(c) = (c#)F ∈ DJ/F, and denote 
the range of ψ by M#. M# obviously contains the interpretations in M* of the 
individual constants. Moreover, M# is closed under the operations (
)
fk
n M*; for 



135
First-Order Logic and Model Theory
(
)
((
) ,
, (
) )
#
#
f
c
c
k
n
n
M*
1
F
F
…
 is hF  , where h j
f
c
c
k
n
n
( )
(
) ( ,
,
)
=
…
M
1
 for all j in J, and 
(
) (( ,
,
)
f
c
c
k
n
n
M
1 …
 is a fixed element b of D. So, hF = (b#)F ∈ M#. Thus, M# is a 
substructure of M*.
Corollary 2.44
ψ is an isomorphism of M with M#, and M# ≤e M*.
Proof
	
a.	By definition of M#, the range of ψ is M#.
	
b.	ψ is one–one. (For any c, d in D, (c#)F = (d#)F if and only if c# = F   d#, 
which is equivalent to {j|c#(j) = d#(j)} ∈ F  ; that is, {j|c = d} ∈ F. If 
c
d
j c
d
≠
=
= ∅∈
, { |
}
F , and, therefore, ψ (c) ≠ ψ (d).
	
c.	For any c1, …, cn in D, (
)
( ( )
,
(
))
(
)
((
) ,
,
#
f
c
c
f
c
k
n
n
k
n
M
M
*
*
ψ
ψ
1
1
…
=
…
F
 
(
) )
#c
h
n F
F
=
, 
where 
h j
f
c
j
c
j
f
c
c
k
n
n
k
n
n
( )
(
) (
( ),
,
( ))
(
) ( ,
,
)
#
#
=
…
=
…
M
M
1
1
. 
Thus, h
f
c
c
f
c
c
k
n
n
k
n
n
F
F
=
…
=
…
((
) ( ,
,
))
((
) ( ,
,
))
#
M
M
1
1
/
ψ
.
	
d.	M* A
c
c
k
n
n
[ ( )
,
(
)]
ψ
ψ
1 …
 if and only if { |
( ( )( ),
,
( )( ))}
,
j
A
c
j
c
j
M
k
n
n

ψ
ψ
1
…
∈F  
which 
is 
equivalent 
to 
j
A c
c
k
n
n
|
( ,
,
)
M
1 …
{
}∈F , 
that 
is, 
M A c
c
k
n
n
[ ,
,
].
1 …
 Thus, ψ is an isomorphism of M with M#.
To see that M# ≤ eM*, let B  be any wf and (
) ,
, (
)
#
#
#
c
c
M
n
1 F
F
…
∈
. Then, by proposi-
tion 2.42(a), M* B
F
F
[(
) ,
, (
) ]
#
#
c
cn
1
…
 if and only if { |
[
( ),
,
( )]}
#
#
j
c
j
c
j
n
M B
F
1
…
∈
, 
which is equivalent to {j| ⊨MB[c1, …, cn]} ∈ F, which, in turn, is equivalent to 
⊨M B[c1, …, cn], that is, to M#
[(
) ,
, (
) ]
#
#
B
F
c
c
F
n
1
…
, since ψ is an isomorphism of 
M with M#.
Exercises
2.124	 (The compactness theorem again; see Exercise 2.54) If all finite subsets 
of a set of sentences Γ have a model, then Γ has a model.
2.125	 a.	 A class W  of interpretations of a language L  is called elementary if 
there is a set Γ of sentences of L such that W   is the class of all mod-
els of Γ. Prove that W   is elementary if and only if W   is closed under 
elementary equivalence and the formation of ultraproducts.
	
	
b.	 A class W  of interpretations of a language L  will be called sentential 
if there is a sentence B of L such that W  is the class of all models of 
B. Prove that a class W   is sentential if and only if both W    and its 
complement W  (all interpretations of L   not in W   ) are closed with 
respect to elementary equivalence and ultraproducts.
	
	
c.	 Prove that theory K of fields of characteristic 0 (see page 116) is 
axiomatizable but not finitely axiomatizable.



136
Introduction to Mathematical Logic
2.14.2  Nonstandard Analysis
From the invention of the calculus until relatively recent times the idea of 
infinitesimals has been an intuitively meaningful tool for finding new results 
in analysis. The fact that there was no rigorous foundation for infinitesimals 
was a source of embarrassment and led mathematicians to discard them in 
favor of the rigorous limit ideas of Cauchy and Weierstrass. However, almost 
fifty years ago, Abraham Robinson discovered that it was possible to res-
urrect infinitesimals in an entirely legitimate and precise way. This can be 
done by constructing models that are elementarily equivalent to, but not iso-
morphic to, the ordered field of real numbers. Such models can be produced 
either by using Proposition 2.33 or as ultrapowers. We shall sketch here the 
method based on ultrapowers.
Let R be the set of real numbers. Let K be a generalized predicate calculus 
with equality having the following symbols:
	
1.	For each real number r, there is an individual constant ar.
	
2.	For every n-ary operation φ on R, there is a function letter fφ.
	
3.	For every n-ary relation Φ on R, there is a predicate letter AΦ.
We can think of R as forming the domain of a model R for K; we simply let 
(ar)R = r, (fφ)R = φ, and (AΦ)R = Φ.
Let F be a nonprincipal ultrafilter on the set ω of natural numbers. We can 
then form the ultrapower R * = R  ω/F. We denote the domain Rω/F of R* by R*. 
By Corollary 2.43, R * ≡ R and, therefore, R* has all the properties formaliz-
able in K that R possesses. Moreover, by Corollary 2.44, R* has an elementary 
submodel R  # that is an isomorphic image of R. The domain R# of R  # consists 
of all elements (c#)F  corresponding to the constant functions c#(i) = c for all i in 
ω. We shall sometimes refer to the members of R# also as real numbers; the 
elements of R* − R# will be called nonstandard reals.
That there exist nonstandard reals can be shown by explicitly exhibiting 
one. Let ι(j) = j for all j in ω. Then ιF ∈ R*. However, (c#)F < ιF for all c in R, by 
virtue of Loś’s theorem and the fact that {j|c#(j) < ι(j)} = {j|c < j}, being the set 
of all natural numbers greater than a fixed real number, is the complement 
of a finite set and is, therefore, in the nonprincipal ultrafilter F. ιF is an “infi-
nitely large” nonstandard real. (The relation < used in the assertion (c#)F < ιF 
is the relation on the ultrapower R* corresponding to the predicate letter < of 
K. We use the symbol < instead of (<)R * in order to avoid excessive notation, 
and we shall often do the same with other relations and functions, such as 
u + v, u × v, and |u|.)
Since R* possesses all the properties of R formalizable in K, R* is an 
ordered field having the real number field R  # as a proper subfield. (R* is non-
Archimedean: the element ιF   defined above is greater than all the natural 
numbers (n#)F  of R*.) Let R1, the set of “finite” elements of R*, contain those 
elements z such that |z| < u for some real number u in R#. (R1 is easily seen 



137
First-Order Logic and Model Theory
to form a subring of R*.) Let R0 consist of 0 and the “infinitesimals” of R*, that 
is, those elements z ≠ 0 such that |z| < u for all positive real numbers u in R#. 
The reciprocal 1/ιF is an infinitesimal.) It is not difficult to verify that R0 is an 
ideal in the ring R1. In fact, since x ∈ R1 − R0 implies that 1/x ∈ R1 − R0, it can 
be easily proved that R0 is a maximal ideal in R1.
Exercises
2.126	 Prove that the cardinality of R* is 2
0
ℵ.
2.127	 Prove that the set R0 is closed under the operations of +, −, and ×.
2.128	 Prove that, if x ∈ R1 and y ∈ R0, then xy ∈ R0.
2.129	 Prove that, if x ∈ R1 − R0, then 1/x ∈ R1 − R0.
Let x ∈ R1. Let A = {u|u ∈ R# ∧ u < x} and B = {u|u ∈ R# ∧ u > x}. Then 〈A, B〉 
is a “cut” and, therefore, determines a unique real number r such that (1) (∀x)
(x ∈ A ⇒ x ≤ r) and (2) (∀x)(x ∈ B ⇒ x ≥ r).* The difference x − r is 0 or an 
infinitesimal. (Proof: Assume x − r is not 0 or an infinitesimal. Then |x − r| 
> r1 for some positive real number r1. If x > r, then x − r > r1. So x > r + r1 > r. 
But then r + r1 ∈ A, contradicting condition (1). If x < r, then r − x > r1, and so 
r > r − r1 > x. Thus, r − r1 ∈ B, contradicting condition (2).) The real number 
r such that x − r is 0 or an infinitesimal is called the standard part of x and is 
denoted st(x). Note that, if x is itself a real number, then st(x) = x. We shall use 
the notation x ≈ y to mean st(x) = st(y). Clearly, x ≈ y if and only if x − y is 0 or 
an infinitesimal. If x ≈ y, we say that x and y are infinitely close.
Exercises
2.130	 If x ∈ R1, show that there is a unique real number r such that x − r is 0 
or an infinitesimal. (It is necessary to check this to ensure that st(x) is 
well-defined.)
2.131	 If x and y are in R1, prove the following.
	
a.	 st(x + y) = st(x) + st(y)
	
b.	 st(xy) = st(x)st(y)
	
c.	 st(−x) = −st(x) ∧ st(y − x) = st(y) − st(x)
	
d.	 x ≥ 0 ⇒ st(x) ≥ 0
	
e.	 x ≤ y ⇒ st(x) ≤ st(y)
The set of natural numbers is a subset of the real numbers. Therefore, in the 
theory K there is a predicate letter N corresponding to the property x ∈ ω. 
Hence, in R*, there is a set ω* of elements satisfying the wf N(x). An element 
*	 See Mendelson (1973, Chapter 5).



138
Introduction to Mathematical Logic
fF of R* satisfies N(x) if and only if {j|f(j) ∈ ω} ∈ F. In particular, the elements 
nF
# , for n ∈ ω, are the “standard” members of ω*, whereas ιF   , for example, is a 
“nonstandard” natural number in R*.
Many of the properties of the real number system can be studied from the 
viewpoint of nonstandard analysis. For example, if s is an ordinary denu-
merable sequence of real numbers and c is a real number, one ordinarily says 
that lim sn = c if
	
(&)
(
)(
(
)(
(
)(
)))
∀
>
⇒∃
∈
∧∀
∈
∧
≥
⇒
−
<
ε ε
ω
ω
ε
0
n n
k k
k
n
s
c
k
Since s ∈ Rω, s is a relation and, therefore, the theory K contains a predicate 
letter S(n, x) corresponding to the relation sn = x. Hence, R* will have a rela-
tion of all pairs 〈n, x〉 satisfying S(n, x). Since R * ≡ R, this relation will be a 
function that is an extension of the given sequence to the larger domain ω*. 
Then we have the following result.
Proposition 2.45
Let s be a denumerable sequence of real numbers and c a real number. Let s* 
denote the function from ω* into R* corresponding to s in R*. Then lim sn = c 
if and only if s*(n) ≈ c for all n in ω* − ω. (The latter condition can be para-
phrased by saying that s*(n) is infinitely close to c when n is infinitely large.)
Proof
Assume lim sn = c. Consider any positive real ε. By (&), there is a natural 
number n0 such that (∀k)(k ∈ ω ∧ k ≥ n0 ⇒ |sk − c| < ε) holds in R. Hence, the 
corresponding sentence (∀k)(k ∈ ω* ∧ k ≥ n0 ⇒ |s*(k) − c| < ε) holds in R*. For 
any n in ω* − ω, n > n0 and, therefore, |s*(n) − c| < ε. Since this holds for all 
positive real ε, s*(n) − c is 0 or an infinitesimal.
Conversely, assume s*(n) ≈ c for all n ε ω* − ω. Take any positive real ε. Fix 
some n1 in ω* − ω. Then (∀k)(k ≥ n1 ⇒ |s*(k) − c| < ε). So the sentence (∃n)(n ∈ ω 
∧ (∀k)(k ∈ ω ∧ k ≥ n ⇒ |sk − c| < ε)) is true for R* and, therefore, also for R. So 
there must be a natural number n0 such that (∀k)(k ∈ ω ∧ k ≥ n0 ⇒ |sk − c| < ε). 
Since ε was an arbitrary positive real number, we have proved lim sn = c.
Exercise
2.132	 Using Proposition 2.45, prove the following limit theorems for the real 
number system. If s and u are denumerable sequences of real numbers 
and c1 and c2 are real numbers such that lim sn = c1 and lim un = c2, then:
	
a.	 lim (sn + un) = c1 + c2;
	
b.	 lim (snun) = c1c2;
	
c.	 If c2 ≠ 0 and all un ≠ 0, lim (sn/un) = c1/c2.



139
First-Order Logic and Model Theory
Let us now consider another important notion of analysis, continuity. Let B 
be a set of real numbers, let c ∈ B, and let f be a function defined on B and 
taking real values. One says that f is continuous at c if
	
(¶)
(
)(
(
)(
(
)(
|
|
| ( )
( )|
)))
∀
>
⇒∃
>
∧∀
∈∧
−
<
⇒
−
<
ε ε
δ δ
δ
ε
0
0
x x
B
x
c
f x
f c
Proposition 2.46
Let f be a real-valued function on a set B of real numbers. Let c ∈ B. Let B* be 
the subset of R* corresponding to B, and let f* be the function corresponding 
to f.† Then f is continuous at c if and only if (∀x)(x ∈ B* ∧ x ≈ c ⇒ f*(x) ≈ f(c)).
Exercises
2.133	 Prove Proposition 2.46.
2.134	 Assume f and g are real-valued functions defined on a set B of real 
numbers and assume that f and g are continuous at a point c in B. 
Using Proposition 2.46, prove the following.
	
a.	f + g is continuous at c.
	
b.	f · g is continuous at c.
2.135	 Let f be a real-valued function defined on a set B of real numbers and 
continuous at a point c in B, and let g be a real-valued function defined 
on a set A of real numbers containing the image of B under f. Assume 
that g is continuous at the point f(c). Prove, by Proposition 2.46, that 
the composition g ○ f is continuous at c.
2.136	 Let C ⊆ R.
	
a.	C is said to be closed if (∀x)((∀ε)[ε > 0 ⇒ (∃y)(y ∈ C ∧|x − y| < ε)] ⇒ 
x ∈ C). Show that C is closed if and only if every real number that is 
infinitely close to a member of C* is in C.
	
b.	C is said to be open if (∀x)(x ∈ C ⇒ (∃δ)(δ > 0 ∧ (∀y)(|y − x| < δ ⇒ 
y ∈ C))). Show that C is open if and only if every nonstandard real 
number that is infinitely close to a member of C is a member of C*.
Many standard theorems of analysis turn out to have much simpler proofs 
within nonstandard analysis. Even stronger results can be obtained by start-
ing with a theory K that has symbols, not only for the elements, operations and 
relations on R, but also for sets of subsets of R, sets of sets of subsets of R, and 
*	 To be more precise, f is represented in the theory K by a predicate letter Af, where Af(x, y) 
corresponds to the relation f(x) = y. Then the corresponding relation Af* in R* determines a 
function f* with domain B*.



140
Introduction to Mathematical Logic
so on. In this way, the methods of nonstandard analysis can be applied to all 
areas of modern analysis, sometimes with original and striking results. For fur-
ther development and applications, see A. Robinson (1966), Luxemburg (1969), 
Bernstein (1973), Stroyan and Luxemburg (1976), and Davis (1977a). A calculus 
textbook based on nonstandard analysis has been written by Keisler (1976) and 
has been used in some experimental undergraduate courses.
Exercises
2.137	 A real-valued function f defined on a closed interval [a, b] = {x|a ≤ x ≤ 
b} is said to be uniformly continuous if
	
(
)(
(
)(
(
)(
)(
|
|
| ( )
( )|
∀
>
⇒∃
>
∧∀
∀
≤
≤
∧
≤
≤∧
−
<
⇒
−
ε ε
δ δ
δ
0
0
x
y a
x
b
a
y
b
x
y
f x
f y
< ε)))
	
Prove that f is uniformly continuous if and only if, for all x and y in 
[a, b]*, x ≈ y ⇒ f*(x) ≈ f*(y).
2.138	 Prove by nonstandard methods that any function continuous on [a, b] 
is uniformly continuous on [a, b].
2.15  Semantic Trees
Remember that a wf is logically valid if and only if it is true for all interpre-
tations. Since there are uncountably many interpretations, there is no sim-
ple direct way to determine logical validity. Gödel’s completeness theorem 
(Corollary 2.19) showed that logical validity is equivalent to derivability in 
a predicate calculus. But, to find out whether a wf is provable in a predicate 
calculus, we have only a very clumsy method that is not always applicable: 
start generating the theorems and watch to see whether the given wf ever 
appears. Our aim here is to outline a more intuitive and usable approach in 
the case of wfs without function letters. Throughout this section, we assume 
that no function letters occur in our wfs.
A wf is logically valid if and only if its negation is not satisfiable. We shall 
now explain a simple procedure for trying to determine satisfiability of a 
closed wf B.* Our purpose is either to show that B is not satisfiable or to find 
a model for B.
We shall construct a figure in the shape of an inverted tree. Start with the 
wf B at the top (the “root” of the tree). We apply certain rules for writing 
*	 Remember that a wf is logically valid if and only if its closure is logically valid. So it suffices 
to consider only closed wfs.



141
First-Order Logic and Model Theory
wfs below those already obtained. These rules replace complicated wfs by 
simpler ones in a way that corresponds to the meaning of the connectives 
and quantifiers.
	
¬¬
¬
¬
¬
x
¬
x
¬
x ¬
x ¬
¬
¬
C
C
D
C
D
C
C
C
C
C
C
C
C
D
(
)
(
)
(
)
(
)
(
)
(
)
∨
⇒
∀
∃
↓
↓
↓
↓
↓
∃
∀
Negation
Conjunction
Disjunctio
:
(
)
(
)
:
¬
¬
¬
¬
¬
¬
C
D
C
D
C
D
C
C
D
D
C
D
C
D
∧
⇔
∧
↓
↙↘
↙↘
n
Conditional
Biconditional
Uni
:
:
:
C
D
C
D
C
D
C
D
C
D
C
C
D
D
∨
⇒
⇔
↙↘
↙↘
↙↘
¬
¬
¬
versal quantifier
Rule U
Here, b is any individu
:
(
) ( )
( )
(
) [
∀
↓
x
x
b
C
C
al constant
already present
Existential quantifier
.]
:
(
) ( )
∃
↓
x
x
C
C ( )
[
.]
c
c is a new individual
constant not already in
the figure
 
Note that some of the rules require a fork or branching. This occurs when the 
given wf implies that one of two possible situations holds.
A branch is a sequence of wfs starting at the top and proceeding down the fig-
ure by applications of the rules. When a wf and its negation appear in a branch, 
that branch becomes closed and no further rules need be applied to the wf at the 
end of the branch. Closure of a branch will be indicated by a large cross ×.
Inspection of the rules shows that, when a rule is applied to a wf, the useful-
ness of that wf has been exhausted (the formula will be said to be discharged) 
and that formula need never be subject to a rule again, except in the case of a 
universally quantified wf. In the latter case, whenever a new individual constant 



142
Introduction to Mathematical Logic
appears in a branch below the wf, rule U can be applied with that new constant. 
In addition, if no further rule applications are possible along a branch and no individual 
constant occurs in that branch, then we must introduce a new individual constant for 
use in possible applications of rule U along that branch. (The idea behind this require-
ment is that, if we are trying to build a model, we must introduce a symbol for at 
least one object that can belong to the domain of the model.)
2.15.1  Basic Principle of Semantic Trees
If all branches become closed, the original wf is unsatisfiable. If, however, a 
branch remains unclosed, that branch can be used to construct a model in 
which the original wf is true; the domain of the model consists of the indi-
vidual constants that appear in that branch.
We shall discuss the justification of this principle later on. First, we shall 
give examples of its use.
Examples
	 1.	
To prove that (∀x)C (x) ⇒ C (b) is logically valid, we build a semantic tree 
starting from its negation.
	 	
i.	 ¬((∀x)C (x) ⇒ C (b))
	 	
ii.	  (∀x)C (x)	
(i)
	 	
iii.	 ¬C (b)	
(i)
	 	
iv.	  C ( )
b
× 	
(ii)
The number to the right of a given wf indicates the number of the line 
of the wf from which the given wf is derived. Since the only branch in 
this tree is closed, ¬((∀x)C (x) ⇒ C (b)) is unsatisfiable and, therefore, (∀x)
C (x) ⇒ C (b) is logically valid.
	 2.	
i.	  ¬[(∀x)(C (x) ⇒ D(x)) ⇒ ((∀x)C (x) ⇒ (∀x)D(x))]
	 	
ii.	 (∀x)(C (x) ⇒ D(x))	
(i)
	 	
iii.	 ¬((∀x)C (x) ⇒ (∀x)D(x))	
(i)
	 	
iv.	 (∀x)C (x)	
(iii)
	 	
v.	 ¬(∀x)D(x)	
(iii)
	 	
vi.	 (∃x) ¬D(x)	
(v)
	 	
vii.	 ¬D(b)	
(vi)
	 	
viii.	 C (b)	
(iv)
	 	
ix.
	
C
D
( )
( )
b
b
⇒
↙↘
	
(ii)
	 	
x.
	
¬
b
b
C
D
( )
( )
×
× 	
(ix)



143
First-Order Logic and Model Theory
Since both branches are closed, the original wf (i) is unsatisfiable and, 
therefore, (∀x)(C (x) ⇒ D(x)) ⇒ ((∀x)C (x) ⇒ (∀x)D(x)) is logically valid.
	 3.	
i.	 ¬ ∃
⇒∀
[(
)
( )
(
)
( )]
x A x
x A x
1
1
1
1
	 	
ii.	 (
)
( )
∃x A x
1
1
	
(i)
	 	
iii.	 ¬ ∀
(
)
( )
x A x
1
1
	
(i)
	 	
iv.	 A b
1
1( ) 	
(ii)
	 	
v.	 (
)
( )
∃
¬
x
A x
1
1
	
(iii)
	 	
vi.	 ¬A c
1
1( ) 	
(v)
No further applications of rules are possible and there is still an open 
branch. Define a model M with domain {b, c} such that the interpretation 
of A1
1 holds for b but not for c. Thus, (
)
( )
∃
¬
x
A x
1
1
 is true in M but (
)
( )
∀x A x
1
1
 
is false in M. Hence, (
)
( )
(
)
( )
∃
⇒∀
x A x
x A x
1
1
1
1
 is false in M and is, therefore, 
not logically valid.
	 4.	
i.	  ¬[(∃y)(∀x)B(x, y) ⇒ (∀x)(∃y)B(x, y)]
	 	
ii.	 (∃y)(∀x)B(x, y)	
(i)
	 	
iii.	 ¬(∀x)(∃y)B(x, y)	
(i)
	 	
iv.	 (∀x)B(x, b)	
(ii)
	 	
v.	 (∃x)¬(∃y)B(x, y)	
(iii)
	 	
vi.	 B(b, b)	
(iv)
	 	
vii.	 ¬(∃y)B(c, y)	
(v)
	 	
viii.	 B(c, b)	
(iv)
	 	
ix.	 (∀y)¬B(c, y)	
(vii)
	 	
x.	 ¬
c b
B ( ,
)
×
	
(ix)
Hence, (∃y)(∀x)B(x, y) ⇒ (∀x)(∃y)B(x, y) is logically valid.
Notice that, in the last tree, step (vi) served no purpose but was required 
by our method of constructing trees. We should be a little more precise 
in describing that method. At each step, we apply the appropriate rule 
to each undischarged wf (except universally quantified wfs), starting 
from the top of the tree. Then, to every universally quantified wf on a 
given branch we apply rule U with every individual constant that has 
appeared on that branch since the last step. In every application of a 
rule to a given wf, we write the resulting wf(s) below the branch that 
contains that wf.
	 5.	
i.	  ¬[(∀x)B(x) ⇒ (∃x)B(x)]
	 	
ii.	 (∀x)B(x)	
(i)
	 	
iii.	 ¬(∃x)B(x)	
(i)
	 	
iv.	  (∀x)¬B(x)	
(iii)



144
Introduction to Mathematical Logic
	 	
v.	  B(b)	
(ii)*
	 	
vi.	  ¬
b
B ( )
×
	
(iv)
Hence, (∀x)B(x) ⇒ (∃x)B(x) is logically valid.
	 6.	
i.	 ¬ ∀
¬
⇒∃
∀
¬
[(
)
( , )
(
)(
)
( , )]
x
A x x
x
y
A x y
1
2
1
2
	 	
ii.	 (
)
( , )
∀
¬
x
A x x
1
2
	
(i)
	 	
iii.	 ¬
x
y
A x y
(
)(
)
( , )
∃
∀
¬
1
2
	
(ii)
	 	
iv.	 (
) (
)
( , )
∀
¬ ∀
¬
x
y
A x y
1
2
	
(iii)
	 	
v.	 ¬A a a
1
2
1
1
(
,
) 	
(ii)†
	
vi.	 ¬ ∀
¬
(
)
(
, )
y
A a y
1
2
1
	
(iv)
	 	
vii.	 (
)
(
, )
∃
¬¬
y
A a y
1
2
1
	
(vi)
	 	
viii.	 ¬¬A a a
1
2
1
2
(
,
) 	
(vii)
	 	
ix.	 A a a
1
2
1
2
(
,
) 	
(viii)
	 	
x.	 ¬A a
a
1
2
2
2
(
,
) 	
(ii)
	 	
xi.	 ¬ ∀
¬
(
)
(
, )
y
A a
y
1
2
2
	
(iv)
	 	
xii.	 (
)
(
, )
∃
¬¬
y
A a
y
1
2
2
	
(xi)
	 	
xiii.	 ¬¬A a
a
1
2
2
3
(
,
) 	
(xii)
	 	
xiv.	 A a
a
1
2
2
3
(
,
)	
(xiii)
We can see that the branch will never end and that we will obtain a sequence 
of constants a1, a2, … with wfs A a
a
n
n
1
2
1
(
,
)
+  and ¬A a
a
n
n
1
2(
,
). Thus, we construct 
a model M with domain {a1, a2, …} and we define (
)
A1
2 M to contain only the 
pairs 〈an, an+1〉. Then, (
)
( , )
∀
¬
x
A x x
1
2
 is true in M, whereas (
)(
)
( , )
∃
∀
¬
x
y
A x y
1
2
 is 
false in M. Hence, (
)
( , )
(
)(
)
( , )
∀
¬
⇒∃
∀
¬
x
A x x
x
y
A x y
1
2
1
2
 is not logically valid.
Exercises
2.139	 Use semantic trees to determine whether the following wfs are logi-
cally valid.
	
a.	 (
)(
( )
( ))
((
)
( ))
(
)
( )
∀
∨
⇒
∀
∨∀
x A x
A x
x A x
x A x
1
1
2
1
1
1
2
1
	
b.	 ((∀x)B(x)) ∧ (∀x)C (x) ⇒ (∀x)(B(x) ∧ C (x))
	
c.	 (∀x)(B(x) ∧ C (x)) ⇒ ((∀x)B(x)) ∧ (∀x)C (x)
*	 Here, we must introduce a new individual constant for use with rule U since, otherwise, the 
branch would end and would not contain any individual constants.
†	 Here, we must introduce a new individual constant for use with rule U since, otherwise, the 
branch would end and would not contain any individual constants.



145
First-Order Logic and Model Theory
	
d.	 (
)(
( )
( ))
((
)
( )
(
)
( ))
∃
⇒
⇒
∃
⇒∃
x A x
A x
x A x
x A x
1
1
2
1
1
1
2
1
	
e.	 (
)(
)
( , )
(
)
( , )
∃
∃
⇒∃
x
y A x y
z A z z
1
2
1
2
	
f.	 ((
)
( ))
(
)
( )
(
)(
( )
( ))
∀
∨∀
⇒∀
∨
x A x
x A x
x A x
A x
1
1
2
1
1
1
2
1
	
g.	 (
)(
)(
( , )
(
)
( , ))
∃
∃
⇒∀
x
y A x y
z A z y
1
2
1
2
	
h.	 The wfs of Exercises 2.24, 2.31(a, e, j), 2.39, and 2.40.
	
i.	 The wfs of Exercise 2.21(a, b, g).
	
j.	 (
)(
( )
( ))
(
)(
( )
( ))
∀
⇒
⇒¬ ∀
⇒¬
x A x
A x
x A x
A x
1
1
2
1
1
1
2
1
Proposition 2.47
Assume that Γ is a set of closed wfs that satisfy the following closure condi-
tions: (a) if ¬¬B is in Γ, then B is in Γ; (b) if ¬(B ∨ C) is in Γ, then ¬B and ¬C are 
in Γ; (c) if ¬(B ⇒ C) is in Γ, then B and ¬C are in Γ; (d) if ¬(∀x)B is in Γ, then (∃x) 
¬B is in Γ; (e) if ¬(∃x)B is in Γ, then (∀x) ¬B is in Γ; (f) if ¬(B ∧ C) is in Γ, then at 
least one of ¬B and ¬C is in Γ; (g) if ¬(B ⇔ C) is in Γ, then either B and ¬C are 
in Γ, or ¬B and C are in Γ; (h) if B ∧ C is in Γ, then so are B and C; (i) if B ∨ C 
is in Γ, then at least one of B and C is in Γ, (j) if B ⇒ C is in Γ, then at least one 
of ¬B and C is in Γ; (k) if B ⇔ C is in Γ, then either B and C are in Γ or ¬B and 
¬C are in Γ; (l) if ∀x)B(x) is in Γ, then B(b) is in Γ (where b is any individual 
constant that occurs in some wf of Γ); (m) if (∃x)B(x) is in Γ, then B(b) is in Γ 
for some individual constant b. If no wf and its negation both belong to Γ and 
some wfs in Γ contain individual constants, then there is a model for Γ whose 
domain is the set D of individual constants that occur in wfs of Γ.
Proof
Define a model M with domain D by specifying that the interpretation 
of any predicate letter Ak
n in Γ contains an n-tuple 〈b1, …, bn〉 if and only if 
A b
b
k
n
n
( ,
,
)
1 …
 is in Γ. By induction on the number of connectives and quanti-
fiers in any closed wf E, it is easy to prove: (i) if E is in Γ, then E is true in M; 
and (ii) if ¬E is in Γ then E is false in M. Hence, M is a model for Γ.
If a branch of a semantic tree remains open, the set Γ of wfs of that branch 
satisfies the hypotheses of Proposition 2.47. If follows that, if a branch of a 
semantic tree remains open, then the set Γ of wfs of that branch has a model 
M whose domain is the set of individual constants that appear in that branch. 
This yields half of the basic principle of semantic trees.
Proposition 2.48
If all the branches of a semantic tree are closed, then the wf B at the root of 
the tree is unsatisfiable.



146
Introduction to Mathematical Logic
Proof
From the derivation rules it is clear that, if a sequence of wfs starts at B and 
continues down the tree through the applications of the rules, and if the 
wfs in that sequence are simultaneously satisfiable in some model M, then 
that sequence can be extended by another application of a rule so that the 
added wf(s) would also be true in M. Otherwise, the sequence would form 
an unclosed branch, contrary to our hypothesis. Assume now that B is sat-
isfiable in a model M. Then, starting with B, we could construct an infi-
nite branch in which all the wfs are true in M. (In the case of a branching 
rule, if there are two ways to extend the sequence, we choose the left-hand 
wf.) Therefore, the branch would not be closed, contrary to our hypothesis. 
Hence, B is unsatisfiable.
This completes the proof of the basic principle of semantic trees. Notice 
that this principle does not yield a decision procedure for logical validity. If 
a closed wf B is not logically valid, the semantic tree of ¬B may (and often 
does) contain an infinite unclosed branch. At any stage of the construction of 
this tree, we have no general procedure for deciding whether or not, at some 
later stage, all branches of the tree will have become closed. Thus, we have 
no general way of knowing whether B is unsatisfiable.
For the sake of brevity, our exposition has been loose and imprecise. 
A clear and masterful study of semantic trees and related matters can be 
found in Smullyan (1968).
2.16  Quantification Theory Allowing Empty Domains
Our definition in Section 2.2 of interpretations of a language assumed that 
the domain of an interpretation is nonempty. This was done for the sake of 
simplicity. If we allow the empty domain, questions arise as to the right way 
of defining the truth of a formula in such a domain.* Once that is decided, 
the corresponding class of valid formulas (that is, formulas true in all inter-
pretations, including the one with an empty domain) becomes smaller, and 
it is difficult to find an axiom system that will have all such formulas as its 
theorems. Finally, an interpretation with an empty domain has little or no 
importance in applications of logic.
Nevertheless, the problem of finding a suitable treatment of such a more 
inclusive logic has aroused some curiosity and we shall present one possible 
approach. In order to do so, we shall have to restrict the scope of the investi-
gation in the following ways.
*	 For example, should a formula of the form (
)(
( )
( ))
∀
∧¬
x A x
A x
1
1
1
1
 be considered true in the 
empty domain?



147
First-Order Logic and Model Theory
First, our languages will contain no individual constants or function let-
ters. The reason for this restriction is that it is not clear how to interpret indi-
vidual constants or function letters when the domain of the interpretation is 
empty. Moreover, in first-order theories with equality, individual constants 
and function letters always can be replaced by new predicate letters, together 
with suitable axioms.*
Second, we shall take every formula of the form (∀x)B(x) to be true in the 
empty domain. This is based on parallelism with the case of a nonempty 
domain. To say that (∀x)B(x) holds in a nonempty domain D amounts to 
asserting
	
( )
,
,
( )
∗
∈
for any object
if
then
c
c
D
B c
When D is empty, “c ∈ D” is false and, therefore, “if c ∈ D, then B(c)” is true. 
Since this holds for arbitrary c, (*) is true in the empty domain D, that is, (∀x)
B(x) is true in an empty domain. Not unexpectedly, (∃x)B(x) will be false in 
an empty domain, since (∃x)B(x) is equivalent to ¬(∀x)¬B(x).
These two conventions enable us to calculate the truth value of any closed 
formula in an empty domain. Every such formula is a truth-functional com-
bination of formulas of the form (∀x)B(x). Replace every subformula (∀x)B(x) 
by the truth value T and then compute the truth value of the whole formula.
It is not clear how we should define the truth value in the empty domain of 
a formula containing free variables. We might imitate what we do in the case 
of nonempty domains and take such a formula to have the same truth values 
as its universal closure. Since the universal closure is automatically true in the 
empty domain, this would have the uncomfortable consequence of declaring 
the formula A x
A x
1
1
1
1
( )
( )
∧¬
 to be true in the empty domain. For this reason, we 
shall confine our attention to sentences, that is, formulas without free variables.
A sentence will be said to be inclusively valid if it is true in all interpreta-
tions, including the interpretation with an empty domain. Every inclusively 
valid sentence is logically valid, but the converse does not hold. To see this, 
let f stand for a sentence C ∧ ¬C, where C is some fixed sentence. Now, f is false 
in the empty domain but (∀x)f is true in the empty domain (since it begins 
with a universal quantifier). Thus the sentence (∀x)f ⇒ f is false in the empty 
domain and, therefore, not inclusively valid. However, it is logically valid, 
since every formula of the form (∀x)B ⇒ B is logically valid.
The problem of determining the inclusive validity of a sentence is reduc-
ible to that of determining its logical validity, since we know how to deter-
mine whether a sentence is true in the empty domain. Since the problem of 
determining logical validity will turn out to be unsolvable (by Proposition 
3.54), the same applies to inclusive validity.
*	 For example, an individual constant b can be replaced by a new monadic predicate letter P, 
together with the axiom (∃y)(∀x)(P(x) ⇔ x = y). Any axiom B(b) should be replaced by (∀x)(P(x) 
⇒ B(x)).



148
Introduction to Mathematical Logic
Now let us turn to the problem of finding an axiom system whose theo-
rems are the inclusively valid sentences. We shall adapt for this purpose an 
axiom system PP# based on Exercise 2.28. As axioms we take all the follow-
ing formulas:
(A1) B ⇒ (C ⇒ B)
(A2) (B ⇒ (C ⇒ D)) ⇒ ((B ⇒ C) ⇒ (B ⇒ D))
(A3) (¬C ⇒ ¬B) ⇒ ((¬C ⇒ B) ⇒ C)
(A4) (∀x)B(x) ⇒ B(y) if B(x) is a wf of L and y is a variable that is free for x in 
B(x). (Recall that, if y is x itself, then the axiom has the form (∀x)B ⇒ B. 
In addition, x need not be free in B(x).)
(A5) (∀x)(B ⇒ C) ⇒ (B ⇒ (∀x)C) if B contains no free occurrences of x.
(A6) (∀y1) … (∀yn)(B ⇒ C) ⇒ [(∀y1) … (∀yn)B ⇒ (∀y1) … (∀yn)C]
together with all formulas obtained by prefixing any sequence of universal 
quantifiers to instances of (A1)–(A6).
Modus ponens (MP) will be the only rule of inference.
PP denotes the pure first-order predicate calculus, whose axioms are (A1)–
(A5), whose rules of inference are MP and Gen, and whose language contains 
no individual constants or function letters. By Gödel’s completeness theorem 
(Corollary 2.19), the theorems of PP are the same as the logically valid for-
mulas in PP. Exercise 2.28 shows first that Gen is a derived rule of inference 
of PP#, that is, if ⊢PP# D, then ⊢PP# (∀x)D, and second that PP and PP# have the 
same theorems. Hence, the theorems of PP# are the logically valid formulas.
Let PPS# be the same system as PP# except that, as axioms, we take only the 
axioms of PP# that are sentences. Since MP takes sentences into sentences, 
all theorems of PPS# are sentences. Since all axioms of PPS# are axioms of 
PP#, all theorems of PPS# are logically valid sentences. Let us show that the 
converse holds.
Proposition 2.49
Every logically valid sentence is a theorem of PPS#.
Proof
Let B be any logically valid sentence. We know that B is a theorem of PP#. 
Let us show that B is a theorem of PPS#. In a proof of B in PP#, let u1, …, un be 
the free variables (if any) in the proof, and prefix (∀u1) … (∀un) to all steps of 
the proof. Then each step goes into a theorem of PPS#. To see this, first note 
that axioms of PP# go into axioms of PPS#. Second, assume that D comes from 
C and C ⇒ D by MP in the original proof and that (∀u1) … (∀un)C and (∀u1) … 
(∀un)(C ⇒ D) are provable in PPS#. Since (∀u1) … (∀un)(C ⇒ D) ⇒ [(∀u1) … (∀un)C 
⇒ (∀u1) … (∀un)D] is an instance of axiom (A6) of PPS#, it follows that (∀u1) … 
(∀un)D is provable in PPS#. Thus, (∀u1) … (∀un)B is a theorem of PPS#. Then n 
applications of axiom (A4) and MP show that B is a theorem of PPS#.



149
First-Order Logic and Model Theory
Not all axioms of PPS# are inclusively valid. For example, the sentence (∀x) f ⇒ 
f discussed earlier is an instance of axiom (A4) that is not inclusively valid. So, 
in order to find an axiom system for inclusive validity, we must modify PPS#.
If P is a sequence of variables u1, …, un, then by ∀P we shall mean the 
expression (∀u1) … (∀un).
Let the axiom system ETH be obtained from PPS# by changing axiom 
(A4) into:
(A4′) All sentences of the form ∀P[(∀x)B(x) ⇒ B(y)], where y is free for x in 
B(x) and x is free in B(x), and P is a sequence of variables that includes all 
variables free in B (and possibly others).
MP is the only rule of inference.
It is obvious that all axioms of ETH are inclusively valid.
Lemma 2.50
If T is an instance of a tautology and P is a sequence of variables that 
­contains all free variables in T,  then ⊢ETH ∀PT.
Proof
By the completeness of axioms (A1)–(A3) for the propositional calculus, there 
is a proof of T   using MP and instances of (A1)–(A3). If we prefix ∀P to all 
steps of that proof, the resulting sentences are all theorems of ETH. In the 
case when an original step B was an instance of (A1)–(A3), ∀PB is an axiom 
of ETH. For steps that result from MP, we use axiom (A6).
Lemma 2.51
If P is a sequence of variables that includes all free variables of B ⇒ C, and 
⊢ETH ∀PB and ⊢ETH ∀P[B ⇒ C], then ⊢ETH ∀PC.
Proof
Use axiom (A6) and MP.
Lemma 2.52
If P is a sequence of variables that includes all free variables of B, C, D, and 
⊢ETH ∀P[B ⇒ C] and ⊢ETH ∀P[C ⇒ D], then ⊢ETH ∀P[B ⇒ D].
Proof
Use the tautology (B ⇒ C ⇒ ((C ⇒ D) ⇒ (B ⇒ D)), Lemma 2.50, and Lemma 
2.51 twice.



150
Introduction to Mathematical Logic
Lemma 2.53
If x is not free in B and P is a sequence of variables that contains all free vari-
ables of B, ⊢ETH ∀P[B ⇒ (∀x)B].
Proof
By axiom (A5), ⊢ETH ∀P[(∀x)(B ⇒ B) ⇒ (B ⇒ (∀x) B)]. By Lemma 2.50, ⊢ETH 
∀P[(∀x)(B ⇒ B)]. Now use Lemma 2.51.
Corollary 2.54
If B has no free variables, then ⊢ETH B ⇒ (∀x)B.
Lemma 2.55
If x is not free in B and P is a sequence of variables that includes all variables 
free in B, then ⊢ETH ∀P[¬(∀x) f ⇒ ((∀x)B ⇒ B)].
Proof
⊢ETH ∀P[¬B ⇒ (B ⇒ f)] by Lemma 2.50. By Lemma 2.53, ⊢ETH ∀P[(B ⇒ f) ⇒ (∀x)
(B ⇒ f)]. Hence, by Lemma 2.52, ⊢ETH ∀P[¬B ⇒ (∀x)(B ⇒ f)]. By axiom (A6), ⊢ETH 
∀P[(∀x)(B ⇒ f) ⇒ ((∀x)B ⇒ (∀x)f)]. Hence, by Lemma 2.52, ⊢ETH ∀P[¬B ⇒ ((∀x)B 
⇒ (∀x)f)]. Since [¬B ⇒ ((∀x)B ⇒ (∀x)f)] ⇒ [¬(∀x)f ⇒ ((∀x)B ⇒ B)] is an instance 
of a tautology, Lemmas 2.50 and 2.51 yield ⊢ETH ∀P[¬(∀x)f ⇒ ((∀x)B ⇒ B)].
Proposition 2.56
ETH + {¬(∀x)f} is a complete axiom system for logical validity, that is, a sen-
tence is logically valid if and only if it is a theorem of the system.
Proof
All axioms of the system are logically valid. (Note that (∀x)f is false in all 
interpretations with a nonempty domain and, therefore, ¬(∀x)f is true in all 
such domains.) By Proposition 2.49, all logically valid sentences are prov-
able in PPS#. The only axioms of PPS# missing from ETH are those of the 
form ∀P[(∀x)B ⇒ B], where x is not free in B and P is any sequence of vari-
ables that include all free variables of B. By Lemma 2.55, ⊢ETH ∀P[¬(∀x)f ⇒ 
((∀x)B ⇒ B)]. By Corollary 2.54, ∀P[¬(∀x)f] will be derivable in ETH + {¬(∀x)f}. 
Hence, ∀P[(∀x)B ⇒ B] is obtained by using axiom (A6).



151
First-Order Logic and Model Theory
Lemma 2.57
If P is a sequence of variables that include all free variables of B, ⊢ETH ∀P[(∀x)
f ⇒ ((∀x)B ⇔ t)], where t is ¬ f.
Proof
Since f ⇒ B is an instance of a tautology, Lemma 2.50 yields ⊢ETH ∀P(∀x)[f ⇒ 
B]. By axiom (A6), ⊢ETH ∀P [(∀x)[f ⇒ B] ⇒ [(∀x)f ⇒ (∀x)B]]. Hence, ⊢ETH ∀P[(∀x)
f ⇒ (∀x)B] by Lemma 2.51. Since (∀x)B ⇒ [(∀x)B ⇔ t] is an instance of a tautol-
ogy, Lemma 2.50 yields ⊢ETH ∀P[(∀x)B ⇒ [(∀x)B ⇔ t]]. Now, by Lemma 2.52, 
⊢ETH ∀P [(∀x)f ⇒ [(∀x)B ⇔ t]].
Given a formula B, construct a formula B* in the following way. Moving 
from left to right, replace each universal quantifier and its scope by t.
Lemma 2.58
If P is a sequence of variables that include all free variables of B, then 
⊢ETH ∀P [(∀x) f ⇒ [B ⇔ B*]].
Proof
Apply Lemma 2.57 successively to the formulas obtained in the stepwise 
construction of B*. We leave the details to the reader.
Proposition 2.59
ETH is a complete axiom system for inclusive validity, that is, a sentence B is 
inclusively valid if and only if it is a theorem of ETH.
Proof
Assume B is a sentence valid for all interpretations. We must show that ⊢ETH 
B. Since B is valid in all nonempty domains, Proposition 2.56 implies that B 
is provable in ETH + {¬(∀x)f}. Hence, by the deduction theorem,
	
( )
(
)
.
+
∀
⇒
⊢ETH ¬
x f
B
Now, by Lemma 2.58,
	
(
)
(
)
[
]
%
x f
B
B
⊢ETH ∀
⇒
⇔
*



152
Introduction to Mathematical Logic
(Since B has no free variables, we can take P in Lemma 2.58 to be empty.) 
Hence, [(∀x)f ⇒ [B ⇔ B*]] is valid for all interpretations. Since (∀x)f is valid 
in the empty domain and B is valid for all interpretations, B* is valid in the 
empty domain. But B* is a truth-functional combination of ts. So, B* must 
be truth-functionally equivalent to either t or f. Since it is valid in the empty 
domain, it is truth-functionally equivalent to t. Hence, ⊢ETH B*. Therefore by 
(%), ⊢ETH (∀x)f ⇒ B. This, together with (+), yields ⊢ETH B.
The ideas and methods used in this section stem largely, but not entirely, 
from a paper by Hailperin (1953).* That paper also made use of an idea in 
Mostowski (1951b), the idea that underlies the proof of Proposition 2.59. 
Mostowski’s approach to the logic of the empty domain is quite different 
from Hailperin’s and results in a substantially different axiom system for 
inclusive validity. For example, when B does not contain x free, Mostowski 
interprets (∀x)B and (∃x)B to be B itself. This makes (∀x)f equivalent to f, 
rather than to t, as in our development.
*	 The name ETH comes from “empty domain” and “Theodore Hailperin.” My simplification of 
Hailperin’s axiom system was suggested by a similar simplification in Quine (1954).



153
3
Formal Number Theory
