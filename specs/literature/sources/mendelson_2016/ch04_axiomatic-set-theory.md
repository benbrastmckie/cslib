<!-- Source: Mendelson, E. (2016). Introduction to Mathematical Logic (6th ed). Chapter 4: Axiomatic Set Theory (pages 231-310). BibKey: not yet in references.bib -->

4.1  An Axiom System
A prime reason for the increase in importance of mathematical logic in the 
twentieth century was the discovery of the paradoxes of set theory and the 
need for a revision of intuitive (and contradictory) set theory. Many differ-
ent axiomatic theories have been proposed to serve as a foundation for set 
theory but, no matter how they may differ at the fringes, they all have as 
a common core the fundamental theorems that mathematicians require for 
their daily work. We make no claim about the superiority of the system we 
shall use except that, from a notational and conceptual standpoint, it is a 
convenient basis for present-day mathematics.
We shall describe a first-order theory NBG, which is basically a system of 
the same type as one originally proposed by J. von Neumann (1925, 1928) 
and later thoroughly revised and simplified by R. Robinson (1937), Bernays 
(1937–1954), and Gödel (1940). (We shall follow Gödel’s monograph to a great 
extent, although there will be some significant differences.)*
NBG has a single predicate letter A2
2 but no function letter or individual 
constants.† In order to conform to the notation in Bernays (1937–1954) and 
Gödel (1940), we shall use capital italic letters X1, X2, X3, … as variables instead 
of x1, x2, x3, … . (As usual, we shall use X, Y, Z, … to represent arbitrary vari-
ables.) We shall abbreviate A X Y
2
2(
,
) by X ∈ Y, and ¬A X Y
2
2(
,
) by X ∉ Y.
Intuitively, ∈ is to be thought of as the membership relation and the values 
of the variables are to be thought of as classes. Classes are certain collections 
of objects. Some properties determine classes, in the sense that a property 
P may determine a class of all those objects that possess that property. This 
“interpretation” is as imprecise as the notions of “collection” and “property.” 
The axioms will reveal more about what we have in mind. They will provide 
us with the classes we need in mathematics and appear modest enough so 
that contradictions are not derivable from them.
Let us define equality in the following way.
*	 I coined the name NBG in honor of von Neumann, Bernays, and Gödel. Paul Halmos, who 
favored the Zermelo-Fraenkel system, suggested that “NBG” stood for “No Bloody Good.”
†	 We use A2
2 instead of A1
2 because the latter was used previously for the equality relation.



232
Introduction to Mathematical Logic
Definition
	
X
Y
Z Z
X
Z
Y
=
∀
∈
⇔
∈
for(
)(
)*
Thus, two classes are equal when and only when they have the same 
members.
Definitions
	
X
Y
Z Z
X
Z
Y
X
Y
X
Y
X
Y
⊆
∀
∈
⇒
∈
⊂
⊆
∧
≠
for
inclusion
for
proper inclusio
(
)(
)
(
)
(
n)
When X ⊆ Y, we say that X is a subclass of Y. When X ⊂ Y, we say that X is a 
proper subclass of Y.
As easy consequences of these definitions, we have the following.
Proposition 4.1†
	
a.	⊢ X = Y ⇔ (X ⊆ Y ∧ Y ⊆ X)
	
b.	⊢ X = X
	
c.	⊢ X = Y ⇒ Y = X
	
d.	⊢ X = Y ⇒ (Y = Z ⇒ X = Z)
We shall now present the proper axioms of NBG, interspersing among the 
axioms some additional definitions and various consequences of the axioms.
We shall define a class to be a set if it is a member of some class. Those 
classes that are not sets are called proper classes.
Definitions
	
M
for
is a set
Pr
for
M
is a proper class
(
)
(
)(
)
(
)
(
)
(
)
(
)
X
Y X
Y
X
X
X
X
∃
∈
¬
It will be seen later that the usual derivations of the paradoxes now no lon-
ger lead to contradictions but only yield the results that various classes are 
proper classes, not sets. The sets are intended to be those safe, comfortable 
classes that are used by mathematicians in their daily work, whereas proper 
*	 As usual, Z is to be the first variable different from X and Y.
†	 The subscript NBG will be omitted from ⊢NBG in the rest of this chapter.



233
Axiomatic Set Theory
classes are thought of as monstrously large collections that, if permitted to be 
sets (i.e., allowed to belong to other classes), would engender contradictions.
Exercise
4.1	
Prove ⊢ X ∈ Y ⇒ M(X).
The system NBG is designed to handle classes, not concrete individuals.* 
The reason for this is that mathematics has no need for objects such as cows 
and molecules; all mathematical objects and relations can be formulated in 
terms of classes alone. If nonclasses are required for applications to other 
sciences, then the system NBG can be modified slightly so as to apply to both 
classes and nonclasses alike (see the system UR in Section 4.6 below).
Let us introduce lower-case letters x1, x2, … as special restricted variables 
for sets. In other words, (∀xj)B (xj) stands for (∀X)(M(X) ⇒ B (X)), that is, B 
holds for all sets, and (∃xj)B (xj) stands for (∃X)(M(X) ∧ B (X)), that is, B holds 
for some set. As usual, the variable X used in these definitions should be 
the first one that does not occur in B (xj). We shall use x, y, z, … to stand for 
arbitrary set variables.
Example
	
(
)(
)(
)(
)(
)
(
)(
)(
(
)
(
∀
∀
∃
∃
∈
∧
∈
∀
∀
⇒∃
X
x
y
X
X
x
y
X
X
X
X
X
1
3
1
3
1
2
2
stands for
M
4
4
3
1
2
4
3
)(
(
)
(
)(
)))
M X
X
X
X
X
X
∧∃
∈
∧
∈
Exercise
4.2	
Prove that ⊢ X = Y ⇔ (∀z)(z ∈ X ⇔ z ∈ Y). This is the so-called exten-
sionality principle: two classes are equal when and only when they 
contain the same sets as members.
Axiom T
	
X
X
X
X
X
X
1
2
1
3
2
3
=
⇒
∈
⇔
∈
(
)
This axiom tells us that equal classes belong to the same classes.
Exercise
4.3	
Prove that ⊢ M(Z) ∧ Z = Y ⇒ M(Y).
*	 If there were concrete individuals (that is, objects that are not classes), then the definition 
of equality would have to be changed, since all such individuals have the same members 
(namely, none at all).



234
Introduction to Mathematical Logic
Proposition 4.2
NBG is a first-order theory with equality.
Proof
Use Proposition 4.1, axiom T, the definition of equality, and the discussion 
on page 97.
Note that Proposition 4.2 entails the substitutivity of equality, which will 
be used frequently in what follows, usually without explicit mention.
Axiom P (Pairing Axiom)
	
(
)(
)(
)(
)(
)
∀
∀
∃
∀
∈
⇔
=
∨
=
x
y
z
u u
z
u
x
u
y
Thus, for any sets x and y, there is a set z that has x and y as its only members.
Exercises
4.4	 Prove ⊢ (∀x)(∀y)(∃1z)(∀u)(u ∈ z ⇔ u = x ∨ u = y). This asserts that there 
is a unique set z, called the unordered pair of x and y, such that z has 
x and y as its only members. Use axiom P and the extensionality 
principle.
4.5	 Prove ⊢ (∀X)(M(X) ⇔ (∃y)(X ∈ y)).
4.6	 Prove ⊢ (∃X) Pr(X) ⇒ ¬(∀Y)(∀Z)(∃W)(∀U)(U ∈ W ⇔ U = Y ∨ U = Z).
Axiom N (Null Set)
	
(
)(
)(
)
∃
∀
∉
x
y y
x
Thus, there is a set that has no members. From axiom N and the extensionality 
principle, there is a unique set that has no members—that is, ⊢ (∃1x)(∀y)(y ∉ x). 
Therefore, we can introduce a new individual constant ∅ by means of the 
following condition.
Definition
	
(
)(
)
∀
∉∅
y y
It then follows from axiom N and Exercise 4.3 that ∅ is a set.
Since we have (by Exercise 4.4) the uniqueness condition for the unordered 
pair, we can introduce a new function letter ɡ(x, y) to designate the unor-
dered pair of x and y. In accordance with the traditional notation, we shall 



235
Axiomatic Set Theory
write {x, y} instead of ɡ(x, y). Notice that we have to define a unique value for 
{X, Y} for any classes X and Y, not only for sets x and y. We shall let {X, Y} be 
∅ whenever X is not a set or Y is not a set. One can prove
⊢(
)([(
(
)
( ))
] [
(
)
( ) (
)(
)]).
∃
¬
∨¬
∧
=∅∨
∧
∧∀
∈⇔=
∨=
1Z
X
Y
Z
X
Y
u u Z
u
X u Y
M
M
M
M
This justifies the introduction of a term {X, Y} satisfying the following 
condition:
	
[
(
)
( )
(
)(
{
,
}
)]
[(
(
)
( ))
{
,
}
]
M
M
M
M
X
Y
u u
X Y
u
X
u
Y
X
Y
X Y
∧
∧∀
∈
⇔
=
∨
=
∨¬
∨¬
∧
= ∅
One can then prove ⊢ (∀x)(∀y)(∀u)(u ∈ {x, y} ⇔ u = x ∨ u = y) and ⊢ (∀X)(∀Y)
M({X, Y}).
Definition
	
{ }
{
,
}
X
X X
for
For a set x, {x} is called the singleton of x. It is a set that has x as its only 
member.
In connection with these definitions, the reader should review Section 2.9 
and, in particular, Proposition 2.28, which assures us that the introduction 
of new individual constants and function letters, such as ∅ and {X, Y}, adds 
nothing essentially new to the theory NBG.
Exercise
4.7	 a.	 Prove ⊢ {X, Y} = {Y, X}.
	b.	 Prove ⊢ (∀x)(∀y)({x} = {y} ⇔ x = y).
Definition
	
〈
〉
X Y
X
X Y
,
{{ },{
,
}}
for
For sets x and y, 〈x, y〉 is called the ordered pair of x and y.
The definition of 〈X, Y〉 does not have any intrinsic intuitive meaning. It 
is just a convenient way (discovered by Kuratowski, 1921) to define ordered 
pairs so that one can prove the characteristic property of ordered pairs 
expressed in the following proposition.



236
Introduction to Mathematical Logic
Proposition 4.3
	
⊢∀
(
) ∀
(
) ∀
(
) ∀
(
) 〈
〉= 〈
〉⇒
=
∧
=
(
)
x
y
u
v
x y
u v
x
u
y
v
,
,
Proof
Assume 〈x, y〉 = 〈u, v〉. Then {{x}, {x, y}} = {{u}, {u, v}}. Since {x} ∈ {{x}, {x, y}}, 
{x} ∈ {{u}, {u, v}}. Hence, {x} = {u} or {x} = {u, v}. In either case, x = u. Now, {u, v} 
∈ {{u}, {u, v}}; so, {u, v} ∈ {{x}, {x, y}}. Then {u, v} = {x} or {u, v} = {x, y}. Similarly, 
{x, y} = {u} or {x, y} = {u, v}. If {u, v} = {x} and {x, y} = {u}, then x = y = u = v; 
if not, {u, v} = {x, y}. Hence, {u, v} = {u, y}. So, if v ≠ u, then y = v; if v = u, then 
y = v. Thus, in all cases, y = v.
Notice that the converse of Proposition 4.3 holds by virtue of the substitu-
tivity of equality.
Exercise
4.8	 a.	 Show that, instead of the definition of an ordered pair given in the 
text, we could have used 〈X, Y〉 = {{∅, X}, {{∅}, Y}}; that is, Proposition 
4.3 would still be provable with this new meaning of 〈X, Y〉.
	
b.	 Show that the ordered pair also could be defined as {{∅, {X}}, {{Y}}}. 
(This was the first such definition, discovered by Wiener (1914). For a 
thorough analysis of such definitions, see A. Oberschelp (1991).)
We now extend the definition of ordered pairs to ordered n-tuples.
Definitions
	
〈
〉=
〈
…
〉= 〈〈
…
〉
〉
+
+
X
X
X
X
X
X
X
X
n
n
n
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
Thus, 〈X, Y, Z〉 = 〈〈X, Y〉, Z〉 and 〈X, Y, Z, U〉 = 〈〈〈X, Y〉, Z〉, U〉.
It is easy to establish the following generalization of Proposition 4.3:
	
⊢∀
(
) … ∀
(
) ∀
(
) … ∀
(
) 〈
…
〉= 〈
…
〉⇒
=
∧… ∧
=
x
x
y
y
x
x
y
y
x
y
x
y
n
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
1
(
,
,
,
,
)
Axioms of Class Existence
(B1)	 (∃X)(∀u)(∀v)(〈u, v〉 ∈ X ⇔ u ∈ v)	
(∈-relation)
(B2)	 (∀X)(∀Y)(∃Z)(∀u)(u ∈ Z ⇔ u ∈ X ∧ u ∈ Y)	
(intersection)
(B3)	 (∀X)(∃Z)(∀u)(u ∈ Z ⇔ u ∉ X)	
(complement)
(B4)	 (∀X)(∃Z)(∀u)(u ∈ Z ⇔ (∃v)(〈u, v〉 ∈ X))	
(domain)



237
Axiomatic Set Theory
(B5)	 (∀X)(∃Z)(∀u)(∀v)(〈u, v〉 ∈ Z  ⇔ u  ∈ X)
(B6)	 (∀X)(∃Z)(∀u)(∀v)(∀w)(〈u, v, w〉 ∈ Z  ⇔ 〈v, w, u〉 ∈ X)
(B7)	 (∀X)(∃Z)(∀u)(∀v)(∀w)(〈u, v, w〉 ∈ Z  ⇔ 〈u, w, v〉 ∈ X)
From axioms (B2)–(B4) and the extensionality principle, we obtain:
	
⊢∀
(
) ∀
(
) ∃
(
) ∀
(
)
∈
⇔
∈
∧
∈
(
)
X
Y
Z
u
u
Z
u
X
u
Y
1
	
⊢∀
(
) ∃
(
) ∀
(
)
∈
⇔
∉
(
)
X
Z
u
u
Z
u
X
1
	
⊢∀
(
) ∃
(
) ∀
(
)
∈
⇔∃
(
) 〈
〉∈
(
)
(
)
X
Z
u
u
Z
v
u v
X
1
,
These results justify the introduction of new function letters: ∩, −, and D.
Definitions
	
  
intersection of
and
                
(
)(
)
(
)
∀
∈
∩
⇔
∈
∧
∈
u u
X
Y
u
X
u
Y
X
Y
     
complement of
(
)(
)
(
)
(
)(
(
)
(
)(
,
∀
∈
⇔
∉
∀
∈
⇔∃
〈
〉∈
u u
X
u
X
X
u u
X
v
u v
X
D
))
(
)
(
domain of
                                
unio
X
X
Y
X
Y
∪
=
∩
n of
and
                                              
X
Y
V
)
= ∅
−
=
∩
(
)
universal class
                                
∗
X
Y
X
Y
(
)
difference of
and
X
Y
Exercises
4.9	
Prove:
	
a.	 ⊢ (∀u)(u ∈ X ∪ Y ⇔ u ∈ X ∨ u ∈ Y)
	
b.	 ⊢ (∀u)(u ∈ V)
	
c.	 ⊢ (∀u)(u ∈ X − Y ⇔ u ∈ X ∧ u ∉ Y)
4.10	 Prove:
	a.	 ⊢ X ∩ Y = Y ∩ X
	b.	 ⊢ X ∪ Y = Y ∪ X
	c.	 ⊢ X ⊆ Y ⇔ X ∩ Y = X
	d.	 ⊢ X ⊆ Y ⇔ X ∪ Y = Y
	e.	 ⊢ (X ∩ Y) ∩ Z = X ∩ (Y ∩ Z)
	 f.	 ⊢ (X ∪ Y) ∪ Z = X ∪ (Y ∪ Z)
*	 It will be shown later that V is a proper class, that is, V is not a set.



238
Introduction to Mathematical Logic
	g.	 ⊢ (X ∩ X) = X
	h.	 ⊢ X ∪ X = X
	 i.	 ⊢ X ∩ ∅ = ∅
	 j.	 ⊢ X ∪ ∅ = X
	k.	 ⊢ X ∩ V = X
	 l.	 ⊢ X ∪ V = V
	m.	 ⊢X
Y
X
Y
∪
=
∪
	n.	 ⊢X
Y
X
Y
∩
=
∪
	o.	 ⊢ X − X = ∅
	p.	 ⊢V
X
X
−
=
	q.	 ⊢ X −(X − Y) = X ∩ Y
	 r.	 ⊢Y
X
X
Y
X
⊆
⇒
−
=
	s.	 ⊢X
X
=
	 t.	 ⊢V = ∅
	u.	 ⊢ X ∩ (Y ∪ Z) = (X ∩ Y) ∪ (X ∩ Z)
	v.	 ⊢ X ∪ (Y ∩ Z) = (X ∪ Y) ∩ (X ∪ Z)
4.11	 Prove the following wfs.
	a.	 ⊢ (∀X)(∃Z)(∀u)(∀v)(〈u, v〉 ∈ Z ⇔ 〈v, u〉 ∈ X) [Hint: Apply axioms (B5), 
(B7), (B6), and (B4) successively.]
	b.	 ⊢ (∀X)(∃Z)(∀u)(∀v)(∀w)(〈u, v, w〉 ∈ Z ⇔ 〈u, w〉 ∈ X) [Hint: Use (B5) 
and (B7).]
	c.	 ⊢ (∀X)(∃Z)(∀v)(∀x1) … (∀xn)(〈x1, …, xn, v〉 ∈ Z ⇔ 〈x1, …, xn〉 ∈ X) [Hint: 
Use (B5).]
	d.	 ⊢ (∀X)(∃Z)(∀v1) … (∀vm)(∀x1) … (∀xn)(〈x1, …, xn, v1, …, vm〉 ∈ Z ⇔ 
〈x1, … , xn〉 ∈ X) [Hint: Iteration of part (c).]
	e.	 ⊢ (∀X)(∃Z)(∀v1) … (∀vm)(∀x1) … (∀xn)(〈x1, …, xn−1, v1, …, vm, xn〉 ∈ Z ⇔ 
〈x1, …, xn〉 ∈ X) [Hint: For m = 1, use (b), substituting 〈x1, …, xn−1〉 for 
u and xn for w; the general case then follows by iteration.]
	 f.	 ⊢ (∀X)(∃Z)(∀x)(∀v1) … (∀vm)(〈v1, …, vm, x〉 ∈ Z ⇔ x ∈ X) [Hint: Use (B5) 
and part (a).]
	g.	 ⊢ (∀X)(∃Z)(∀x1) … (∀xn)(〈x1, …, xn〉 ∈ Z ⇔ (∃y)(〈x1, …, xn, y〉 ∈ X)) [Hint: 
In (B4), substitute 〈xn, …, xn〉 for u and y for v.]
	h.	 ⊢ (∀X)(∃Z)(∀u)(∀v)(∀w)(〈v, u, w〉 ∈ Z ⇔ 〈u, w〉 ∈ X) [Hint: Substitute 
〈u, w〉 for u in (B5) and apply (B6).]
	 i.	 ⊢ (∀X)(∃Z)(∀v1) … (∀vk)(∀u)(∀w)(〈v1, …, vk, u, w〉 ∈ Z ⇔ 〈u, w〉 ∈ X) 
[Hint: Substitute 〈v1, …, vk〉 for v in part (h).]
Now we can derive a general class existence theorem. By a predicative wf we mean 
a wf φ(X1, …, Xn, Y1, …, Ym) whose variables occur among X1, …, Xn, Y1, … , Ym 



239
Axiomatic Set Theory
and in which only set variables are quantified (i.e., φ can be abbreviated in such 
a way that only set variables are quantified).
Examples
(∃x1)(x1 ∈ Y1) is predicative, whereas (∃Y1)(x1 ∈ Y1) is not predicative.
Proposition 4.4 (Class Existence Theorem)
Let φ(X1, …, Xn, Y1, …, Ym) be a predicative wf. Then ⊢ (∃Z)(∀x1) … (∀xn) 
(〈x1, … , xn〉 ∈ Z ⇔ φ(x1, …, xn, Y1, …, Ym)).
Proof
We shall consider only wfs φ in which no wf of the form Yi ∈ W occurs, since 
Yi ∈ W can be replaced by (∃x)(x = Yi ∧ x ∈ W), which is equivalent to (∃x) [(∀z)(z ∈ x 
⇔ z ∈ Yi) ∧ x ∈ W]. Moreover, we may assume that φ contains no wf of the form 
X ∈ X, since this may be replaced by (∃u)(u = X ∧ u ∈ X), which is equivalent to 
(∃u) [(∀z)(z ∈ u ⇔ z ∈ X) ∧ u ∈ X]. We shall proceed now by induction on the num-
ber k of connectives and quantifiers in φ (written with restricted set variables).
Base: k = 0. Then φ has the form xi ∈ xj or xj ∈ xi or xi ∈ Yℓ, where 1 ≤ i < j ≤ n. 
For xi ∈ xj, axiom (B1) guarantees that there is some W1 such that (∀xi)(∀xj)(〈xi, 
xj〉 ∈ W1 ⇔ xi ∈ xj). For xj ∈ xi, axiom (B1) implies that there is some W2 such 
that (∀xi)(∀xj)(〈xi, xj〉 ∈ W2 ⇔ xj ∈ xi) and then, by Exercise 4.11(a), there is some 
W3 such that (∀xi)(xj)(〈xi, xj〉 ∈ W3 ⇔ xj ∈ xi). So, in both cases, there is some 
W such that (∀xi)(∀xj)(〈xi, xj〉 ∈ W ⇔ φ(x1, …, xn, Y1, …, Ym)). Then, by Exercise 
4.11(i) with W = X, there is some Z1 such that (∀x1) … (∀xi−1)(∀xi)(∀xj)(〈x1, …, 
xi−1, xi, xj〉 ∈ Z1 ⇔ φ(x1, …, xn, Y1, …, Ym)). Hence, by Exercise 4.11(e) with Z1 = X, 
there exists Z2 such that (∀x1) … (∀xi)(∀xi+1) … (∀xj)(〈x1, …, xj〉 ∈ Z2 ⇔ φ(x1, …, 
xn, Y1, …, Ym)). Then, by Exercise 4.11(d) with Z2 = X, there exists Z such that 
(∀x1) … (∀xn)(〈x1, …, xn〉 ∈ Z ⇔ φ(x1, …, xn, Y1, …, Ym)). In the remaining case, xi 
∈ Yℓ, the theorem follows by application of Exercise 4.11(f, d).
Induction step. Assume the theorem provable for all k < r and assume that φ 
has r connectives and quantifiers.
	
a.	φ is ¬ψ. By inductive hypothesis, there is some W such that (∀x1) … (∀xn)
(〈x1, …, xn〉 ∈ W ⇔ ψ(x1, …, xn, Y1, …, Ym)). Let Z
W
=
.
	
b.	φ is ψ ⇒ ϑ. By inductive hypothesis, there are classes Z1 and Z2 such 
that (∀x1) … (∀xn)(〈x1, …, xn〉 ∈ Z1 ⇔ ψ(x1, …, xn, Y1, …, Ym)) and (∀x1) … 
(∀xn)(〈x1, …, xn〉 ∈ Z2, ϑ(x1, …, xn, Y1, …, Ym)). Let Z
Z
Z
=
∩
1
2.
	
c.	φ is (∀x)ψ. By inductive hypothesis, there is some W such that (∀x1) … 
(∀xn)(∀x)(〈x1, …, xn, x〉 ∈ W ⇔ ψ(x1, …, xn, x, y1, …, Ym)). Apply Exercise 
4.11(g) with X
W
=
 to obtain a class Z1 such that (∀x1) … (∀xn)(〈x1, …, xn〉 
∈ Z1 ⇔ (∃x) ¬ ψ(x1, …, xn, x, Y1, …, Ym)) Now let Z
Z
=
1, noting that (∀x)ψ 
is equivalent to ¬(∃x)¬ψ.



240
Introduction to Mathematical Logic
Examples
	
1.	Let φ(X, Y1, Y2) be (∃u)(∃v)(X = 〈u, v〉 ∧ u ∈ Y1 ∧ v ∈ Y2). The only 
quantifiers in φ involve set variables. Hence, by the class existence 
theorem, ⊢ (∃Z)(∀x)(x ∈ Z ⇔ (∃u)(∃v)(x = 〈u, v〉 ∧ u ∈ Y1 ∧ v ∈ Y2)). By 
the extensionality principle,
	
⊢(
)(
)(
(
)(
)(
,
).
∃
∀
∈
⇔∃
∃
= 〈
〉∧
∈
∧
∈
1
1
2
Z
x x
Z
u
v x
u v
u
Y
v
Y
So, we can introduce a new function letter ×.
Definition
(Cartesian product of Y1 and Y2)
	
(
)(
(
)(
)(
,
))
∀
∈
×
⇔∃
∃
= 〈
〉∧
∈
∧
∈
x x
Y
Y
u
v x
u v
u
Y
v
Y
1
2
1
2
Definitions
	
Y
Y
Y
Y
Y
Y
n
X
X
V
X
relation
n
n
2
1
2
2
for
for
when
Rel
for
is a
×
×
>
⊆
−
(
)
(
)*
V2 is the class of all ordered pairs, and Vn is the class of all ordered n-tuples. 
In ordinary language, the word “relation” indicates some kind of connection 
between objects. For example, the parenthood relation holds between parents 
and their children. For our purposes, we interpret the parenthood relation to 
be the class of all ordered pairs 〈u, v〉 such that u is a parent of v.
	
2.	Let φ(X, Y) be X ⊆ Y. By the class existence theorem and the extension-
ality principle, ⊢ (∃1Z)(∀x)(x ∈ Z ⇔ x ⊆ Y). Thus, there is a unique class Z 
that has as its members all subsets of Y. Z is called the power class of Y 
and is denoted P(Y).
Definition
	
∀
(
)
∈( ) ⇔
⊆
(
)
x
x
Y
x
Y
P
	
3.	Let φ(X, Y) be (∃v)(X ∈ v ∧ v ∈ Y)). By the class existence theorem and 
the extensionality principle, ⊢ (∃1Z)(∀x)(x ∈ Z ⇔ (∃v)(x ∈ v ∧ v ∈ Y)). 
*	 More precisely, Rel(X) means that X is a binary relation.



241
Axiomatic Set Theory
Thus, there is a unique class Z that contains all members of members 
of Y. Z is called the sum class of Y and is denoted ⋃ Y.
Definition
	
(
)(
(
)(
))
∀
∈
⇔∃
∈
∧
∈
x x
Y
v x
v
v
Y
∪
	
4.	Let φ(X) be (∃u)(X = 〈u, u〉). By the class existence theorem and the exten-
sionality principle, there is a unique class Z such that (∀x)(x ∈ Z ⇔ (∃u)
(x = 〈u, u〉)). Z is called the identity relation and is denoted I.
Definition
	
(
)(
(
)(
,
))
∀
∈⇔∃
= 〈
〉
x x
I
u x
u u
Corollary 4.5
If φ(X1, …, Xn, Y1, …, Ym) is a predicative wf, then
	
⊢∃
(
)
⊆
∧∀
(
) … ∀
(
) 〈
…
〉∈
⇔
…
…
(
)
(
)
(
)
1
1
1
1
1
W
W
V
x
x
x
x
W
x
x
Y
Y
n
n
n
n
m
,
,
,
,
,
,
,
ϕ
Proof
By Proposition 4.4, there is some Z such that (∀x1) … (∀xn)(〈x1, …, xn〉 ∈ Z ⇔ 
φ(x1, …, xn, Y1, …, Ym)). Then W = Z ∩ Vn satisfies the corollary, and the unique-
ness follows from the extensionality principle.
Definition
Given a predicative wf φ(X1, …, Xn, Y1, …, Ym), let {〈x1, …, xn〉|φ(x1, …, xn, Y1, …, 
Ym)} denote the class of all n-tuples 〈x1, …, xn〉 that satisfy φ(x1, …, xn, Y1, …, 
Ym); that is,
	
(
)(
{
,
,
| (
,
,
,
,
,
)}
(
)
(
)(
,
,
∀
∈〈
…
〉
…
…
⇔
∃
… ∃
= 〈
…
u u
x
x
x
x
Y
Y
x
x
u
x
i
n
n
m
n
ϕ
1
1
1
1
x
x
x
Y
Y
n
n
m
〉∧
…
…
ϕ(
,
,
,
,
,
)))
1
1
This definition is justified by Corollary 4.5. In particular, when n = 1, ⊢ (∀u)
(u ∈ {x|φ(x, Y1, …, Ym)} ⇔ φ(u, Y1, …, Ym)).



242
Introduction to Mathematical Logic
Examples
	
1.	Take φ to be 〈x2, x1〉 ∈ Y. Let 
⌣
Y be an abbreviation for {〈x1, x2〉|〈x2, x1〉 ∈ Y}. 
Hence, 
⌣
⌣
Y
V
x
x
x x
Y
x
x
Y
⊆
∧∀
∀
〈
〉∈
⇔〈
〉∈
2
1
2
1
2
2
1
(
)(
)(
,
,
) . Call ⌣
Y the inverse 
relation of Y.
	
2.	Take φ to be (∃v)(〈v, x〉 ∈ Y). Let R (Y) stand for {x|(∃v)(〈v, x〉 ∈ Y)}. Then 
⊢ (∀u)(u ∈ R (Y) ⇔ (∃v)(〈v, x〉 ∈ Y)). R (Y) is called the range of Y. Clearly, 
⊢R
D
( )
( ).
Y
Y
=
⌣
Notice that axioms (B1)–(B7) are special cases of the class existence theo-
rem, Proposition 4.4. Thus, instead of the infinite number of instances of the 
axiom schema in Proposition 4.4, it sufficed to assume only a finite number 
of instances of that schema.
Exercises
4.12	 Prove:
	
a.	 ⊢ ⋃ ∅ = ∅
	
b.	 ⊢ ⋃ {∅} = ∅
	
c.	 ⊢ ⋃ V = V
	
d.	 ⊢ P (V) = V
	
e.	 ⊢ X ⊆ Y ⇒ ⋃ X ⊆ ⋃ Y ∧ P  (X) ⊆ P  (Y)
	
f.	 ⊢ ⋃ P  (X) = X
	
g.	 ⊢ X ⊆ P  ( ⋃ X)
	
h.	 ⊢ (X ∩ Y) × (W ∩ Z) = (X × W) ∩ (Y × Z)
	
i.	 ⊢ (X ∪ Y) × (W ∪ Z) = (X × W) ∪ (X × Z) ∪ (Y × W) ∩ (Y × Z)
	
j.	 ⊢ P (X ∩ Y) = P (X) ∩ P (Y)
	
k.	 ⊢ P (X) ∪ P (Y) ⊆ P (X ∪ Y)
	
l.	 ⊢ Rel(Y) ⇒ Y ⊆ D (Y) × R (Y)
	
m.	 ⊢ ⋃ (X ⋃ Y) = ( ⋃ X) ⋃ ( ⋃ Y)
	
n.	 ⊢ ⋃ (X ∩ Y) ⊆ ( ⋃ X) ∩ ( ⋃ Y)
	
o.	 ⊢Z
Y
Z
Y
V
=
⇒
=
∩
⌣
⌣
2
	
p.	 ⊢Rel( )I
I
I
∧
=
⌣
	
q.	 ⊢ P (∅) = {∅}
	
r.	 ⊢ P ({∅}) = {∅, {∅}}
	
s.	 ⊢ (∀x)(∀y)(x × y ⊆ P (P (x ∪ y)))
	
t.	 What simple condition on X and Y is equivalent to P (X ∪ Y) ⊆ P 
(X) ∪ P (Y)?



243
Axiomatic Set Theory
Until now, although we can prove, using Proposition 4.4, the existence of a 
great many classes, the existence of only a few sets, such as ∅, {∅}, {∅, {∅}}, 
and {{∅}}, is known to us. To guarantee the existence of sets of greater com-
plexity, we require more axioms.
Axiom U (Sum Set)
	
(
)(
)(
)(
(
)(
))
∀
∃
∀
∈
⇔∃
∈
∧
∈
x
y
u u
y
v u
v
v
x
This axiom asserts that the sum class ⋃ x of a set x is also a set, which we 
shall call the sum set of x, that is, ⊢(∀ x)M( ⋃ x). The sum set ⋃ x is usu-
ally referred to as the union of all the sets in the set x and is often denoted 
∩v xv
∈
.
Exercises
4.13	 Prove:
	
a.	 ⊢(∀x)(∀y)( ⋃ {x, y} = x ∪ y)
	
b.	 ⊢(∀x)(∀y)M(x ∪ y)
	
c.	 ⊢(∀x)( ⋃ {x} = x)
	
d.	 ⊢(∀x)(∀y)( ⋃ 〈x, y〉 = {x, y})
4.14	 Define by induction {x1, …, xn} to be {x1, …, xn−1} ∪ {xn}. Prove ⊢ (∀x1) … 
(∀xn)(∀u)(u ∈ {x1, …, xn} ⇔ u = x1 ∨ … ∨ u = xn) Thus, for any sets x1, …, xn, 
there is a set that has x1, …, xn as its only members.
Another means of generating new sets from old is the formation of the set 
of subsets of a given set.
Axiom W (Power Set)
	
(
)(
)(
)(
)
∀
∃
∀
∈
⇔
⊆
x
y
u u
y
u
x
This axiom asserts that the power class P (x) of a set x is itself a set, that is, 
⊢ (∀x)M(P (x)).
A much more general way to produce sets is the following axiom of 
subsets.
Axiom S (Subsets)
	
(
)(
)(
)(
)(
)
∀
∀
∃
∀
∈
⇔
∈
∧
∈
x
Y
z
u u
z
u
x
u
Y



244
Introduction to Mathematical Logic
Corollary 4.6
	
a.	⊢ (∀x)(∀Y) M(x ∩ Y) (The intersection of a set and a class is a set.)
	
b.	⊢ (∀x)(∀Y)(Y ⊆ x ⇒ M(Y)) (A subclass of a set is a set.)
	
c.	For any predicative wf B (y), ⊢ (∀x)M({y|y ∈ x ∧ B (y)}).
Proof
	
a.	By axiom S, there is a set z such that (∀u)(u ∈ z ⇔ u ∈ x ∧ u ∈ Y), which 
implies (∀u)(u ∈ z ⇔ u ∈ x ∩ Y). Thus, z = x ∩ Y and, therefore, x ∩ Y is a 
set.
	
b.	If Y ⊆ x, then x ∩ Y = Y and the result follows by part (a).
	
c.	Let Y = {y|y ∈ x ∧ B (y)}.* Since Y ⊆ x, part (b) implies that Y is a set.
Exercise
4.15	 Prove:
	
a.	 ⊢ (∀x)(M(D (x)) ∧ M(R (x))).
	
b.	 ⊢ (∀x)(∀y) M(x × y). [Hint: Exercise 4.12(s).]
	
c.	 ⊢ M(D (Y)) ∧ M(R (Y)) ∧ Rel(Y) ⇒ M(Y). [Hint: Exercise 4.12(t).]
	
d.	 ⊢ Pr(Y) ∧ Y ⊆ X ⇒ Pr(X).
On the basis of axiom S, we can show that the intersection of any nonempty 
class of sets is a set.
Definition
	
∩X
y
x x
X
y
x
for
(intersection)
{ |(
)(
)}
∀
∈
⇒
∈
 
Proposition 4.7
	
a.	⊢(∀x)(x ∈ X ⇒ ⋂ X ⊆ x)
	
b.	⊢X ≠ ∅ ⇒ M( ⋂ X)
	
c.	⊢ ⋂ ∅ = V
Proof
	
a.	Assume u ∈ X. Consider any y in ⋂ X. Then (∀x)(x ∈ X ⇒ y ∈ x). Hence, 
y ∈ u. Thus, ⋂ X ⊆ u.
*	 More precisely, the wf Y ∈ X ∧ B (Y) is predicative, so that the class existence theorem yields 
a class {y|y ∈ X ∧ B (y)}. In our case, X is a set x.



245
Axiomatic Set Theory
	
b.	Assume X ≠ ∅. Let x ∈ X. By part (a), ⋂ X ⊆ x. Hence, by Corollary 
4.6(b), ⋂ X is a set.
	
c.	Since ⊢ (∀x)(x ∉ ∅), ⊢ (∀y)(∀x)(x ∈ ∅ ⇒ y ∈ x), from which we obtain ⊢(∀ y)
(y ∈ ⋂ ∅). From ⊢ (∀y)(y ∈ V) and the extensionality principle, ⊢ ⋂ ∅ = V.
Exercise
4.16	 Prove:
	
a.	 ⊢ ⋂ {x, y} = x ⋂ y
	
b.	 ⊢ ⋂ {x} = x
	
c.	 ⊢X ⊆ Y ⇒ ⋂ Y ⊆ ⋂ X
A stronger axiom than axiom S will be necessary for the full development of 
set theory. First, a few definitions are convenient.
Definitions
Fnc(X)	
for Rel(X) ∧ (∀x)(∀y)(∀z)(〈x, y〉 ∈ X ∧ 〈x, z〉 ∈ X ⇒ y = z) (X is a 
function)
X:Y → Z	
for Fnc(X)  ∧ D (X) = Y  ∧ R (X) ⊆ Z (X is a function from Y into Z)
Y X	
for X ∩ (Y × V) (restriction of X to the domain Y)
Fnc1(X)	
for Fnc
Fnc
(
)
(
)
X
X
∧
⌣
 (X is a one–one function)
X Y
z
u
Y u
u
′
=
∀
〈
〉∈
⇔
=
∅



if
otherwise
(
)(
,
)
X
z
X″Y = R (Y X)
If there is a unique z such that 〈y, z〉 ∈ X, then z = X′y; otherwise, X′y = ∅. 
If X is a function and y is a set in its domain, X′y is the value of the function 
applied to y. If X is a function, X″Y is the range of X restricted to Y.*
Exercise
4.17 Prove:
	
a.	 ⊢ Fnc(X) ∧ y ∈ D(X) ⇒ (∀z)(X′y = z ⇔ 〈y, z〉 ∈ X)
	
b.	 ⊢ Fnc(X) ∧ Y ⊆ D(X) ⇒ Fnc(Y X) ∧D(Y X) = Y ∧ (∀y)(y ∈ Y ⇒ X′y = 
(Y X)′y)
	
c.	 ⊢ Fnc(X) ⇒ [Fnc1(X) ⇔ (∀y)(∀z)(y ∈ D(X) ∧ z ∈ D(X) ∧ y ≠ z ⇒ X′y ≠ X′z)]
	
d.	 ⊢ Fnc(X) ∧ Y ⊆ D(X) ⇒ (∀z)(z ∈ X″Y ⇔ (∃y)(y ∈ Y ∧ X′y = z))
*	 In traditional set-theoretic notation, if F is a function and y is in its domain, F′y is written as 
F(y), and if Y is included in the domain of F, F″Y is sometimes written as F[Y].



246
Introduction to Mathematical Logic
Axiom R (Replacement)
	
Fnc( )
(
)(
)(
)(
(
)(
,
))
Y
x
y
u u
y
v
v u
Y
v
x
⇒∀
∃
∀
∈
⇔∃
〈
〉∈
∧
∈
Axiom R asserts that, if Y is a function and x is a set, then the class of second 
components of ordered pairs in Y whose first components are in x is a set (or, 
equivalently, R(x Y) is a set).
Exercises
4.18	 Show that, in the presence of the other axioms, the replacement axiom 
(R) implies the axiom of subsets (S).
4.19	 Prove ⊢ Fnc(Y) ⇒ (∀x)M(Y″x).
4.20	 Show that axiom R is equivalent to the wf Fnc(Y) ∧ M(D (Y)) ⇒ M(R (Y)).
4.21	 Show that, in the presence of all axioms except R and S, axiom R is 
equivalent to the conjunction of axiom S and the wf Fnc1(Y) ∧ M(D (Y)) 
⇒ M(R (Y)).
To ensure the existence of an infinite set, we add the following axiom.
Axiom I (Axiom of Infinity)
	
(
)(
(
)(
{ }
))
∃
∅∈
∧∀
∈
⇒
∪
∈
x
x
u u
x
u
u
x
Axiom I states that there is a set x that contains ∅ and such that, whenever 
a set u belongs to x, then u ∪ {u} also belongs to x. Hence, for such a set x, 
{∅} ∈ x, {∅, {∅}} ∈ x, {∅, {∅}, {∅, {∅}}} ∈ x, and so on. If we let 1 stand for {∅}, 
2 for {∅, 1}, 3 for {∅, 1, 2}, …, n for {∅, 1, 2, …, n − 1}, etc., then, for all ordinary 
integers n ≥ 0, n ∈ x, and ∅ ≠ 1, ∅ ≠ 2, 1 ≠ 2, ∅ ≠ 3, 1 ≠ 3, 2 ≠ 3, … .
Exercise
4.22	 a.	 Prove that any wf that implies (∃X)M(X) would, together with axiom 
S, imply axiom N.
	
b.	 Show that axiom I is equivalent to the following sentence (I*):
	
(
)((
)(
(
)(
))
(
)(
{ }
))
∃
∃
∈
∧∀
∉
∧∀
∈
⇒
∪
∈
x
y y
x
u u
y
u u
x
u
u
x
	
Then prove that (I*) implies axiom N. (Hence, if we assumed (I*) 
instead of (I), axiom N would become superfluous.)
This completes the list of axioms of NBG, and we see that NBG has only 
a finite number of axioms—namely, axiom T, axiom P (pairing), axiom 
N (null set), axiom U (sum set), axiom W (power set), axiom S (subsets), 



247
Axiomatic Set Theory
axiom R (replacement), axiom I (infinity), and the seven class existence axi-
oms (B1)–(B7). We have also seen that axiom S is provable from the other axi-
oms; it has been included here because it is of interest in the study of certain 
weaker subtheories of NBG.
Let us verify now that the usual argument for Russell’s paradox does not 
hold in NBG. By the class existence theorem, there is a class Y = {x|x ∉ x}. 
Then (∀x)(x ∈ Y ⇔ x ∉ x). In unabbreviated notation this becomes (∀X)(M(X) 
⇒ (X ∈ Y ⇔ X ∉ X)). Assume M(Y). Then Y ∈ Y ⇔ Y ∉ Y, which, by the tau-
tology (A ⇔ ¬A) ⇒ (A ∧ ¬A), yields Y ∈ Y ∧ Y ∉ Y. Hence, by the derived 
rule of proof by contradiction, we obtain ⊢ ¬M(Y). Thus, in NBG, the argu-
ment for Russell’s paradox merely shows that Russell’s class Y is a proper 
class, not a set. NBG will avoid the paradoxes of Cantor and Burali-Forti in 
a similar way.
Exercise
4.23	 Prove ⊢ ¬M(V), that is, the universal class V is not a set. [Hint: Apply 
Corollary 4.6(b) with Russell’s class Y.]
4.2  Ordinal Numbers
Let us first define some familiar notions concerning relations.
Definitions
X Irr Y for Rel(X) ∧ (∀y)(y  ∈ Y  ⇒ 〈y, y〉 ∉ X)
	
(X is an irreflexive relation on Y)
X Tr Y for Rel(X) ∧ (∀u)(∀v)(∀w)([u  ∈ Y ∧ v  ∈ Y ∧ w ∈ Y ∧
〈u, v〉 ∈ X ∧ 〈v, w〉 ∈ X]  ⇒ 〈u, w〉 ∈ X)
(X is a transitive relation on Y)
X Part Y for (X Irr Y) ∧ (X Tr Y)	
(X partially orders Y)
X Con Y for Rel(X) ∧ (∀u)(∀v)([u ∈ Y ∧ v ∈ Y ∧ u ≠ v] ⇒ 〈u, v〉 ∈ X ∨ 〈v, u〉 ∈ X)
(X is a connected relation on Y)
X Tot Y for (X Irr Y) ∧ (X Tr Y) ∧ (X Con Y)	 (X totally orders Y)
X We Y for (X Irr Y) ∧ (∀Z)([Z ⊆ Y ∧ Z ≠ ∅] ⇒ (∃y)(y ∈ Z ∧
(∀v)(v ∈ Z ∧ v ≠ y ⇒ 〈y, v〉 ∈ X ∧ 〈v, y〉 ∉ X)))
(X well-orders Y, that is, the relation X is irreflexive on Y and every nonempty 
subclass of Y has a least element with respect to X).



248
Introduction to Mathematical Logic
Exercises
4.24	 Prove ⊢ X We Y ⇒ X Tot Y. [Hint: To show X Con Y, let x ∈ Y ∧ y ∈ Y ∧ 
x ≠ y. Then {x, y} has a least element, say x. Then 〈x, y〉 ∈ X. To show X 
Tr Y, assume x ∈ Y ∧ y ∈ Y ∧ z ∈ Y ∧ 〈x, y〉 ∈ X ∧ 〈y, z〉 ∈ X. Then {x, y, z} 
has a least element, which must be x.]
4.25	 Prove ⊢ X We Y ∧ Z ⊆ Y ⇒ X We Z.
Examples (from intuitive set theory)
	
1.	The relation < on the set P of positive integers well-orders P.
	
2.	The relation < on the set of all integers totally orders, but does not well-
order, this set. The set has no least element.
	
3.	The relation ⊂ on the set W of all subsets of the set of integers par-
tially orders W but does not totally order W. For example, {1} ⊄ {2} and 
{2} ⊄ {1}.
Definition
Simp(Z, W1, W2) for (∃x1)(∃x2)(∃r1)(∃r2)(Rel(r1) ∧ Rel(r2) ∧ W1 = 〈r1, x1〉 ∧ W2 = 
〈r2, x2〉 ∧ Fnc1(Z) ∧ D(Z) = x1 ∧ R(Z) = x2 ∧ (∀u)(∀v)(u ∈ x1 ∧ v ∈ x1 ⇒ (〈u, v〉 ∈ r1 
⇔ 〈Z′u, Z′v〉 ∈ r2)))
(Z is a similarity mapping of the relation r1 on x1 onto the relation r2 on x2.)
Definition
	
Sim
for
Simp
and
are
(
,
)
(
)
( ,
,
)
(
W W
z
z W W
W
W
similar ordered str
1
2
1
2
1
2
∃
uctures)
Example
Let r1 be the less-than relation < on the set A of nonnegative integers {0, 1, 
2, …}, and let r2 be the less-than relation < on the set B of positive integers 
{1, 2, 3, …}. Let z be the set of all ordered pairs 〈x, x + 1〉 for x ∈ A. Then z is a 
similarity mapping of 〈r1, A〉 onto 〈r2, B〉.
Definition
	
X
X
u v
z
u z
X
z v
X
composition
X
1
2
2
1
2

for
the
of
{
,
|(
)(
,
,
)}
(
〈
〉
∃
〈
〉∈
∧〈
〉∈
and X1)



249
Axiomatic Set Theory
Exercises
4.26	 Prove:
	a.	 ⊢ Simp(Z, X, Y) ⇒ M(Z) ∧ M(X) ∧ M(Y)
	b.	 ⊢Simp Z X Y
,
,
(
) ⇒ Simp
⌣
Z Y X
,
,
(
)
4.27	 a.	 Prove: ⊢ Rel(X1) ∧ Rel(X2) ⇒ Rel(X1 ⚬ X2)
	b.	 Let X1 and X2 be the parent and brother relations on the set of human 
beings. What are the relations X1 ⚬ X1 and X1 ⚬ X2?
	c.	 Prove: ⊢ Fnc(X1) ∧ Fnc(X2) ⇒ Fnc(X1 ⚬ X2)
	d.	 Prove: ⊢ Fnc1(X1) ∧ Fnc1(X2) ⇒ Fnc1(X1 ⚬ X2)
	e.	 Prove: ⊢ (X1: Z → W ∧ X2: Y → Z) ⇒ X1 ⚬ X2: Y → W
Definitions
	
Fld
for
the
of
TOR
for Rel
Tot Fld
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
(
(
X
X
D
R
X
X
field
X
X
X
X
∪
∧
)))
(
)
(
)
(
)
(
(
(
)))
(
X
total order
X
X
X
X
well
is a
WOR
for Rel
We Fld
is a
X
∧
−ordering relation)
Exercise
4.28	 Prove:
	
a.	 ⊢ Sim(W1, W2) ⇒ Sim(W2, W1)
	
b.	 ⊢ Sim(W1, W2) ∧ Sim(W2, W3) ⇒ Sim(W1, W3)
	
c.	 ⊢ Sim(〈X, Fld(X)〉, 〈Y, Fld(Y)〉) ⇒ (TOR(X) ⇔ TOR(Y)) ∧ (WOR(X) ⇔ 
WOR(Y))
If x is a total order, then the class of all total orders similar to x is called the 
order type of x. We are especially interested in the order types of well-­ordering 
relations, but, since it turns out that all order types are proper classes (except 
the order type {∅} of ∅), it will be convenient to find a class W of well-ordered 
structures such that every well-ordering is similar to a unique member of W. 
This leads us to the study of ordinal numbers.
Definitions
E for {〈x, y〉|x ∈ y}	
(the membership relation)
Trans(X) for (∀u)(u ∈ X ⇒ u ⊆ X)	
(X is transitive)
SectY(X, Z) for Z ⊆ X ∧ (∀u)(∀v)([u ∈ X ∧ v ∈ Z ∧ 〈u, v〉 ∈ Y] ⇒ u ∈ Z)
(Z is a Y-section of X, that is, Z is a subclass of X and every 
member of X that Y-precedes a member of Z is also a member 
of Z.)



250
Introduction to Mathematical Logic
SegY(X, W) for {x|x ∈ X ∧ 〈x, W〉 ∈ Y} (the Y-segment of X determined by W, 
that is, the class of all members of X that Y-precede W).
Exercises
4.29	 Prove:
	
a.	 ⊢ Trans(X) ⇔ (∀u)(∀v)(v ∈ u ∧ u ∈ X ⇒ v ∈ X)
	
b.	 ⊢Trans(X)⇔ ⋃ X ⊆ X
	
c.	 ⊢ Trans(∅)
	
d.	 ⊢ Trans({∅})
	
e.	 ⊢ Trans(X) ∧ Trans(Y) ⇒ Trans(X ∪ Y) ∧ Trans(X ∩ Y)
	
f.	 ⊢Trans(X) ⇒ Trans(⋃ X)
	
g.	 ⊢(∀ u)(u ∈ X ⇒ Trans(u)) ⇒ Trans(⋃ X)
4.30	 Prove:
	
a.	 ⊢ (∀u) [SegE(X, u) = X ∩ u ∧ M(SegE(X, u))]
	
b.	 ⊢ Trans(X) ⇔ (∀u)(u ∈ X ⇒ SegE(X, u) = u)
	
c.	 ⊢ E We X ∧ SectE(X, Z) ∧ Z ≠ X ⇒ (∃u)(u ∈ X ∧ Z = SegE(X, u))
Definitions
Ord(X) for E We X ∧ Trans(X)	
(X is an ordinal class if and only if the 
∈-relation well – orders X and any mem-
ber of X is a subset of X)
On for {x|Ord(x)}	
(The class of ordinal numbers)
Thus, ⊢ (∀x)(x ∈ On ⇔ Ord(x)). An ordinal class that is a set is called an ordi-
nal number, and On is the class of all ordinal numbers. Notice that a wf x ∈ 
On is equivalent to a predicative wf—namely, the conjunction of the follow-
ing wfs:
	
a.	(∀u)(u ∈ x ⇒ u ∉ u)
	
b.	(∀u)(u ⊆ x ∧ u ≠ ∅ ⇒ (∃v)(v ∈ u ∧ (∀w)(w ∈ u ∧ w ≠ v ⇒ v ∈ w ∧ w ∉ v)))
	
c.	(∀u)(u ∈ x ⇒ u ⊆ x)
(The conjunction of (a) and (b) is equivalent to E We x, and (c) is Trans(x).) In 
addition, any wf On ∈ Y can be replaced by the wf (∃y)(y ∈ Y ∧ (∀z)(z ∈ y ⇔ 
z ∈ On)). Hence, any wf that is predicative except for the presence of “On” is 
equivalent to a predicative wf and therefore can be used in connection with 
the class existence theorem.



251
Axiomatic Set Theory
Exercise
4.31	 Prove: (a) ⊢ ∅ ∈ On. (b) ⊢ 1 ∈ On, where 1 stands for {∅}.
We shall use lower-case Greek letters α, β, γ, δ, τ, … as restricted variables 
for ordinal numbers. Thus, (∀α)B (α) stands for (∀x)(x ∈ On ⇒ B (x)), and (∃α)B 
(α) stands for (∃x)(x ∈ On ∧ B (x)).
Proposition 4.8
	
a.	⊢ Ord(X) ⇒ (X ∉ X ∧ (∀u)(u ∈ X ⇒ u ∉ u))
	
b.	⊢ Ord(X) ∧ Y ⊂ X ∧ Trans(Y) ⇒ Y ∈ X
	
c.	⊢ Ord(X) ∧ Ord(Y) ⇒ (Y ⊂ X ⇔ Y ∈ X)
	
d.	⊢ Ord(X) ∧ Ord(Y) ⇒ [(X ∈ Y ∨ X = Y ∨ Y ∈ X) ∧ ¬(X ∈ Y ∧ Y ∈ X) ∧ 
¬(X ∈ Y ∧ X = Y)]
	
e.	⊢ Ord(X) ∧ Y ∈ X ⇒ Y ∈ On
	
f.	⊢ E We On
	
g.	⊢ Ord(On)
	
h.	⊢ ¬ M(On)
	
i.	⊢ Ord(X) ⇒ X = On ∨ X ∈ On
	
j.	⊢ y ⊆ On ∧ Trans(y) ⇒ y ∈ On
	
k.	⊢ x ∈ On ∧ y ∈ On ⇒ (x ⊆ y ∨ y ⊆ x)
Proof
	
a.	If Ord(X), then E is irreflexive on X; so, (∀u)(u ∈ X ⇒ u ∉ u); and, if X ∈ X, 
X ∉ X. Hence, X ∉ X.
	
b.	Assume Ord(X) ∧ Y ⊂ X ∧ Trans(Y). It is easy to see that Y is a proper 
E-section of X. Hence, by Exercise 4.30(b, c), Y ∈ X.
	
c.	Assume Ord(X) ∧ Ord(Y). If Y ∈ X, then Y ⊆ X, since X is transitive; but 
Y ≠ X by (a); so, Y ⊂ X. Conversely, if Y ⊂ X, then, since Y is transitive, 
we have Y ∈ X by (b).
	
d.	Assume Ord(X) ∧ Ord(Y) ∧ X ≠ Y. Now, X ∩ Y ⊆ X and X ∩ Y ⊆ Y. Since 
X and Y are transitive, so is X ∩ Y. If X ∩ Y ⊂ X and X ∩ Y ⊂ Y, then, by 
(b), X ∩ Y ∈ X and X ∩ Y ∈ Y; hence, X ∩ Y ∈ X ∩ Y, contradicting the 
irreflexivity of E on X. Hence, either X ∩ Y = X or X ∩ Y = Y; that is, X ⊆ Y 
or Y ⊆ X. But X ≠ Y. Hence, by (c), X ∈ Y or Y ∈ X. Also, if X ∈ Y and 
Y ∈ X, then, by (c), X ⊂ Y and Y ⊂ X, which is impossible. Clearly, 
X ∈ Y ∧ X = Y is impossible, by (a).
	
e.	Assume Ord(X) ∧ Y ∈ X. We must show E We Y and Trans(Y). Since 
Y ∈ X and Trans(X), Y ⊂ X. Hence, since E We X, E We Y. Moreover, 
if u ∈ Y and v ∈ u, then, by Trans(X), v ∈ X. Since E Con X and Y ∈ X ∧ 
v ∈ X, then v ∈ Y ∨ v = Y ∨ Y ∈ v. If either v = Y or Y ∈ v, then, since 
E Tr X and u ∈ Y ∧ v ∈ u, we would have u ∈ u, contradicting (a). Hence 
v ∈ Y. So, if u ∈ Y, then u ⊆ Y, that is, Trans(Y).



252
Introduction to Mathematical Logic
	
f.	By (a), E Irr On. Now assume X ⊆ On ∧ X ≠ ∅. Let α ∈ X. If α is the least 
element of X, we are done. (By least element of X we mean an element 
v in X such that (∀u)(u ∈ X ∧ u ≠ v ⇒ v ∈ u).) If not, then E We α and X ∩ 
α ≠ ∅; let β be the least element of X ∩ α. It is obvious, using (d), that β is 
the least element of X.
	
g.	We must show E We On and Trans(On). The first part is (f). For the 
­second, if u ∈ On and v ∈ u, then, by (e), v ∈ On. Hence, Trans(On).
	
h.	If M(On), then, by (g), On ∈ On, contradicting (a).
	
i.	Assume Ord(X). Then X ⊆ On. If X ≠ On, then, by (c), X ∈ On.
	
j.	Substitute On for X and y for Y in (b). By (h), y ⊂ On.
	
k.	Use parts (d) and (c).
We see from Proposition 4.8(i) that the only ordinal class that is not an ordi-
nal number is the class On itself.
Definitions
	
x
y
x
On
y
On
x
y
x
y
y
On
x
y
x
y
<
∈
∧
∈
∧
∈
≤
∈
∧
=
∨
<
o
o
o
for
for
(
)
Thus, for ordinals, <⚬ is the same as ∈; so, <⚬ well-orders On. In particular, 
from Proposition 4.8(e) we see that any ordinal x is equal to the set of smaller 
ordinals.
Proposition 4.9 (Transfinite Induction)
	
⊢∀
(
)
∀
(
)
∈
⇒
∈
(
) ⇒
∈

⇒
⊆
β
α
α
β
α
β
X
X
On
X
(If, for every β, whenever all ordinals less than β are in X, β must also be in X, 
then all ordinals are in X.)
Proof
Assume (∀β) [(∀α)(α ∈ β ⇒ α ∈ X) ⇒ β ∈ X]. Assume there is an ordinal in 
On – X. Then, since On is well-ordered by E, there is a least ordinal β in On – X. 
Hence, all ordinals less than β are in X. So, by hypothesis, β is in X, which is 
a contradiction.
Proposition 4.9 is used to prove that all ordinals have a given prop-
erty B(α). We let X = {x|B(x) ∧ x ∈ On} and show that (∀β)[(∀α)(α ∈ β ⇒ 
B(α)) ⇒B(β)].



253
Axiomatic Set Theory
Definition
x′ for x ∪ {x}
Proposition 4.10
	
a.	⊢ (∀x)(x ∈ On ⇔ x′ ∈ On)
	
b.	⊢ (∀α) ¬(∃β)(α <⚬ β <⚬ α′)
	
c.	⊢ (∀α)(∀β)(α′ = β′ ⇒ α = β)
Proof
	
a.	x ∈ x′. Hence, if x′ ∈ On, then x ∈ On by Proposition 4.8(e). Conversely, 
assume x ∈ On. We must prove E We (x ∪ {x}) and Trans(x ∪ {x}). Since 
E We x and x ∉ x, E Irr (x ∩ {x}). Also, if y ≠ ∅ ∧ y ⊆ x ∪ {x}, then either 
y = {x}, in which case the least element of y is x, or y ∩ x ≠ ∅ and the least 
element of y ∩ x is then the least element of y. Hence, E we (x ∪ {x}). In 
addition, if y ∈ x ∪ {x} and u ∈ y, then u ∈ x. Thus, Trans(x ∪ {x}).
	
b.	Assume α <⚬ β <⚬ α′. Then, α ∈ β ∧ β ∈ α′. Since α ∈ β, β ∉ α, and β ≠ α by 
Proposition 4.8(d), contradicting β ∈ α′.
	
c.	Assume α′ = β′. Then β <⚬ α′ and, by part (b), β ≤⚬ α. Similarly, α ≤⚬ β. 
Hence, α = β.
Exercise
4.32	 Prove: ⊢ (∀α)(α ⊂ α′)
Definitions
Suc(X) for X ∈ On ∧ (∃α)(X = α′)	
(X is a successor ordinal)
K1 for {x|x = ∅ ∨ Suc(x)}	
(the class of ordinals of the first kind)
ω for {x|x ∈ K1 ∧ ∀u)(u ∈ x ⇒ u ∈ K1)}	
(ω is the class of all ordinals
	
α of the first kind such that
	
all ordinals smaller than α are
	
also of the first kind)
Example
⊢ ∅ ∈ ω ∧ 1 ∈ ω. (Recall that 1 = {∅}.)
Proposition 4.11
	
a.	⊢ (∀α)(α ∈ ω ⇔ α′ ∈ ω)
	
b.	⊢ M(ω)
	
c.	⊢ ∅ ∈ X ∧ (∀u)(u ∈ X ⇒ u′ ∈ X) ⇒ ω ⊆ X
	
d.	⊢ (∀α)(α ∈ ω ∧ β <⚬ α ⇒ β ∈ ω)



254
Introduction to Mathematical Logic
Proof
	
a.	Assume α ∈ ω. Since Suc(α′), α′ ∈ K1. Also, if β ∈ α′, then β ∈ α or β = α. 
Hence, β ∈ K1. Thus, α′ ∈ ω. Conversely, if α′ ∈ ω, then, since α ∈ α′ and 
(∀β)(β ∈ α ⇒ β ∈ α′), it follows that α ∈ ω.
	
b.	By the axiom of infinity (I), there is a set x such that ∅ ∈ x and (∀u)(u ∈ 
x ⇒ u′ ∈ x). We shall prove ω ⊆ x. Assume not. Let α be the least ordinal 
in ω − x. Clearly, α ≠ ∅, since ∅ ∈ x. Hence, Suc(α). So, (∃β)(α = β′). Let δ be 
an ordinal such that α = δ′. Then δ <⚬ α and, by part (a), δ ∈ ω. Therefore, 
δ ∈ x. Hence, δ′ ∈ x. But α = δ′. Therefore, α ∈ x, which yields a contradic-
tion. Thus, ω ⊆ x. So, M(ω) by Corollary 4.6(b).
	
c.	This is proved by a procedure similar to that used for part (b).
	
d.	This is left as an exercise.
The elements of ω are called finite ordinals. We shall use the standard nota-
tion: 1 for ∅′, 2 for 1′, 3 for 2′, and so on. Thus, ∅ ∈ ω, 1 ∈ ω, 2 ∈ ω, 3 ∈ ω, ….
The nonzero ordinals that are not successor ordinals are called limit 
ordinals.
Definition
Lim(x) for x ∈ On ∧ x ∉ K1
Exercise
4.33	 Prove:
	
a.	 ⊢ Lim(ω)
	
b.	 ⊢ (∀α)(∀β)(Lim(α) ∧ β <⚬ α ⇒ β′ <⚬ α).
Proposition 4.12
	 a.	 ⊢∀
(
)
⊆
⇒
∈
∧∀
(
)

(
∈
⇒
≤
(
) ∧∀
(
)
∀
(
)
(
x
x
On
On
x
∪
∪
x
x
α
α
α
β
α
o
 
(
)
α
α
β
β
∈
⇒
≤
⇒
≤
))
x
o
o
∪x
. (If x is a set of ordinals, then ⋃ x is an 
ordinal that is the least upper bound of x.)
	 b.	 ⊢ (∀x)(x ⊆ On ∧ x ≠ ∅ ∧ (∀α)(α ∈ x ⇒ (∃β)(β ∈ x ∧ α <⚬ β))] ⇒ Lim( ⋃ x)). 
(If x is a nonempty set of ordinals without a maximum, then ⋃ x is a 
limit ordinal.)
Proof
	
a.	Assume x ⊆ On. ⋃ x, as a set of ordinals, is well-ordered by E. 
Also, if α ∈ ⋃ x ∧ β ∈ α, then there is some γ with γ ∈ x and α ∈ γ. 



255
Axiomatic Set Theory
Then β ∈ α ∧ α ∈ γ; since every ordinal is transitive, β ∈ γ. So, β ∈ ⋃ x. 
Hence, ⋃ x is transitive and, therefore, ⋃ x ∈ On. In addition, if 
α ∈ x, then α ⊆ ⋃ x; so, α ≤⚬ ⋃ x, by Proposition 4.8(c). Assume now 
that (∀α)(α ∈ x ⇒ α ≤⚬ β). Clearly, if δ ∈ ⋃ x, then there is some γ such 
that δ ∈ γ ∧ γ ∈ x. Hence, γ ≤⚬ β and so, δ <⚬ β. Therefore, ⋃ x ⊆ β and, 
by Proposition 4.8(c), ⋃ x ≤⚬ β.
	
b.	Assume x ⊆ On ∧ x ≠ ∅ ∧ (∀α)(α ∈ x ⇒ (∃β)(β ∈ x ∧ α <⚬ β)). If ⋃ x = 
∅, then α ∈ x implies α = ∅. So, x = ∅ or x = 1, which contradicts our 
assumption. Hence, ⋃ x ≠ ∅. Assume Suc( ⋃ x). Then ⋃ x = γ′ for 
some γ. By part (a), ⋃ x is a least upper bound of x. Therefore, γ is not 
an upper bound of x; there is some δ in x with γ <⚬ δ. But then δ = ⋃ x, since 
⋃ x is an upper bound of x. Thus, ⋃ x is a maximum element of x, 
contradicting our hypothesis. Hence, ¬ Suc( ⋃ x), and Lim( ⋃ x) is the 
only possibility left.
Exercise
4.34	 Prove:
	
a.	 ⊢∀
(
)
( ) ⇒(
)′=


(
∧
( ) ⇒
=
)


α
α
α
α
α
Suc
Lim
∪
∪
α
α
.
	
b.	 If ∅ ≠ x ⊆ On, then ⋂ x is the least ordinal in x.
We can now state and prove another form of transfinite induction.
Proposition 4.13 (Transfinite Induction: Second Form)
	
a.	⊢ [∅ ∈ X ∧ (∀α)(α ∈ X ⇒ α′ ∈ X) ∧ (∀α)(Lim(α) ∧ (∀β)(β <⚬ α ⇒ β ∈ X) 
⇒ α ∈ X)] ⇒ On ⊆ X
	
b.	(Induction up to δ.) ⊢ [∅ ∈ X ∧ (∀α)(α <⚬ δ ∧ α ∈ X
	
	 ⇒ α′ ∈ X) ∧ (∀α)(α <⚬ δ ∧ Lim(α) ∧ (∀β)(β <⚬ α
	
	 ⇒ β ∈ X) ⇒ α ∈ X)] ⇒ δ ⊆ X.
	
c.	(Induction up to ω.) ⊢ ∅ ∈ X ∧ (∀α)(α <⚬ ω ∧ α ∈ X ⇒ α′ ∈ X) ⇒ ω ⊆ X.
Proof
	
a.	Assume the antecedent. Let Y = {x|x ∈ On ∧ (∀α)(α ≤⚬ x ⇒ α ∈ X)}. It is 
easy to prove that (∀α)(α <⚬ γ ⇒ α ∈ Y) ⇒ γ ∈ Y. Hence, by Proposition 
4.9, On ⊆ Y. But Y ⊆ X. Hence, On ⊆ X.
	
b.	The proof is left as an exercise.
	
c.	This is a special case of part (b), noting that ⊢ (∀α)(α <⚬ ω ⇒ ¬Lim(α)).
Set theory depends heavily upon definitions by transfinite induction, which 
are justified by the following theorem.



256
Introduction to Mathematical Logic
Proposition 4.14
	
a.	⊢ (∀X)(∃1Y)(Fnc(Y) ∧ D(Y) = On ∧ (∀α)(Y′α = X′ (α   Y))). (Given X, there is 
a unique function Y defined on all ordinals such that the value of Y at α 
is the value of X applied to the restriction of Y to the set of ordinals less 
than α.)
	
b.	⊢ (∀x)(∀X1)(∀X2)(∃1Y)(Fnc(Y) ∧ D(Y) = On ∧ Y′∅ = x ∧ (∀α)(Y′(α′) = X1′(Y′α)) 
∧ (∀α)(Lim(α) ⇒Y′α = X2′ (α   Y))).
	
c.	(Induction up to δ.) ⊢ (∀x)(∀X1)(∀X2)(∃1Y)(Fnc(Y) ∧ D(Y) = δ ∧ Y′∅ = x 
∧ (∀α)(α′ <⚬ δ ⇒ Y′ (α′) = X1′ (Y′ α)) ∧ (∀α)(Lim(α) ∧ α <0 δ ⇒Y′ α = X2′ 
(α   Y))).
Proof
	
a.	Let Y1 = {u|Fnc(u) ∧ D (u) ∈ On ∧ (∀α)(α ∈ D (u) ⇒ u′α = X′(α   u))}. Now, 
if u1 ∈ Y1 and u2 ∈ Y1, then u1 ⊆ u2 or u2 ⊆ u1. In fact, let γ1 = D (u1) and 
γ2 = D (u2). Either γ1 ≤⚬ γ2 or γ2 ≤⚬ γ1; say, γ1 ≤⚬ γ2. Let w be the set of 
ordinals α <⚬ γ1 such that u1′α ≠ u2′α; assume w ≠ ∅ and let η be the 
least ordinal in w. Then for all β <⚬ η, u1′β = u2′β. Hence, u1′α = η   u2. But 
u1′η = X′ (η   u1) and u2′η = X′ (η   u2); and so, u1′η = u2′η, contradicting 
our assumption. Therefore, w = ∅; that is, for all α ≤⚬ γ1, u1′α = u2′α. 
Hence, u1 = γ1   u1 = γ1   u2 ⊆ u2. Thus, any two functions in Y1 agree in 
their common domain. Let Y = ⋃ Y1. We leave it as an exercise to prove 
that Y is a function, the domain of which is either an ordinal or the 
class On, and (∀α)(α ∈ D (Y) ⇒ Y′α = X′ (α   Y)). That D (Y) = On follows 
easily from the observation that, if D (Y) = δ and if we let W = Y ∪ {〈δ, 
X′Y〉}, then W ∈ Y1; so, W ⊆ Y and δ ∈ D (Y) = δ, which contradicts the 
fact that δ ∉ δ. The uniqueness of Y follows by a simple transfinite 
induction (Proposition 4.9).
The proof of part (b) is similar to that of (a), and part (c) follows from (b).
Using Proposition 4.14, one can introduce new function letters by transfi-
nite induction.
Examples
	
1.	Ordinal addition. In Proposition 4.14(b), take
	
x
X
u v
v
u
X
u v
v
u
=
= 〈
〉
=
= 〈
〉
=
( )
′
β
1
2
{
,
|
}
{
,
|
}
∪R
	
	 Hence, for each ordinal β, there is a unique function Yβ such that
	
Y
Y
Y
Y
Y
β
β
β
β
β
β
α
α
α
α
α
α
′∅=
∧∀
′
′ =
′
′ ∧
⇒
′
=
″
(
)(
(
)
(
)
[
( )
(
)])
Lim
∪



257
Axiomatic Set Theory
	
	 Hence there is a unique binary function +⚬ with domain (On)2 such that, 
for any ordinals β and γ, + ⚬(β, γ) = Yβ′γ. As usual, we write β +⚬ γ instead 
of +⚬(β, γ). Notice that:
	
β
β
β
γ
β
γ
α
β
α
β
τ
τ
α
+ ∅=
+
′ =
+
′
⇒
+
=
+
<
o
o
o
o
o
Lim
o
( )
(
)
( )
(
)
∪
	
	 In particular,
	
β
β
β
β
+
=
+
′
∅=
+ ∅′ = ′
o
o
o
1
(
)
(
)
	
2.	Ordinal multiplication. In Proposition 4.14(b), take
	
x
X
u v
v
u
X
u v
v
u
= ∅
= 〈
〉
=
+
= 〈
〉
=
1
2
{
,
|
}
{
,
|
( )}
o β
R
∪
Then, as in Example 1, one obtains a function β ×⚬ γ with the properties
	
β
β
γ
β
γ
β
α
β
α
β
τ
τ
α
× ∅= ∅
×
′ =
×
+
⇒
×
=
×
<
o
o
o
o
o
o
Lim
o
( )
(
)
( )
(
)
∪
Exercises
4.35	 Prove: ⊢ β ×⚬ 1 = β ∧ β ×⚬ 2 = β +⚬ β.
4.36	 Justify the following definition of ordinal exponentiation.*
	
exp( ,
)
exp( ,
)
exp( , )
( )
exp( , )
exp
β
β γ
β γ
β
α
β α
τ
α
∅=
′ =
×
⇒
=
∅<
<
1
o
Lim
o
o∪
( , )
β τ
For any class X, let EX be the membership relation restricted to X; that is, 
EX = {〈u, v〉|u ∈ v ∧ u ∈ X ∧ v ∈ X}.
*	 We use the notation exp (β, α) instead of βα in order to avoid confusion with the notation XY to 
be introduced later.



258
Introduction to Mathematical Logic
Proposition 4.15*
Let R be a well-ordering relation on a class Y; that is, R We Y. Let F be a ­function 
from Y into Y such that, for any u and v in Y, if 〈u, v〉 ∈ R, then 〈F′u, F′v〉 ∈ R. 
Then, for all u in Y, u = F′ u or 〈u, F′u〉 ∈ R.
Proof
Let X = {u|〈F′u, u〉 ∈ R}. We wish to show that X = ∅. Assume X ≠ ∅. Since 
X ⊆ Y and R well-orders Y, there is an R-least element u0 of X. Hence, 〈F′u0, u0〉 
∈ R. Therefore 〈F′(F′u0), F′u0〉 ∈ R. Thus, F′u0 ∈ X, but F′u0 is R-smaller than u0, 
contradicting the definition of u0.
Corollary 4.16
If Y is a class of ordinals, F: Y → Y, and F is increasing on Y (that is, α ∈ Y ∧ β 
∈ Y ∧ α <⚬ β ⇒ F′α <⚬ F′β), then α ≤⚬ F′α for all α in Y.
Proof
In Proposition 4.15, let R be EY. Note that EY well-orders Y, by Proposition 
4.8(f) and Exercise 4.25.
Corollary 4.17
Let α <⚬ β and y ⊆ α; that is, let y be a subset of a segment of β. Then 〈Eβ, β〉 is 
not similar to 〈Ey, y〉.
Proof
Assume 〈Eβ, β〉 is similar to 〈Ey, y〉. Then there is a function f from β onto y such 
that, for any u and v in β, u <⚬ v ⇔ f′u <⚬ f′v. Since the range of f is y, f′α ∈ y. But 
y ⊆ α. Hence f′α <⚬ α. But, by Corollary 4.16, α ≤⚬ f′α, which yields a contradiction.
Corollary 4.18
	 a.	 For α ≠ β, 〈Eα, α〉 and 〈Eβ, β〉 are not similar.
	 b.	 For any α, if f is a similarity mapping of 〈Eα, α〉 with 〈Eα, α〉, then f is 
the identity mapping, that is, f′β = β for all β <⚬ α.
*	 From this point on, we shall express many theorems of NBG in English by using the cor-
responding informal English translations. This is done to avoid writing lengthy wfs that are 
difficult to decipher and only in cases where the reader should be able to produce from the 
English version the precise wf of NBG.



259
Axiomatic Set Theory
Proof
	
a.	Since α ≠ β, it follows by Proposition 4.8(d, c) that one of α and β is a 
segment of the other; say, α is a segment of β. Then Corollary 4.17 tells 
us that 〈Eβ, β〉 is not similar to 〈Eα, α〉.
	
b.	By Corollary 4.16, f′β ≥⚬ β for all β <⚬ α. But, noting by Exercise 4.26(b) that 
⌣
f is a similarity mapping of 〈Eα, α〉 with 〈Eα, α〉, we again use Corollary 
4.16 to conclude that (
⌣
f)′β ≥⚬ β for all β <⚬ α. Hence β = (
⌣
f )′(f′β) ≥⚬ f ′β ≥⚬ 
β and, therefore, f′β = β.
Proposition 4.19
Assume that a nonempty set u is the field of a well-ordering r. Then there is a 
unique ordinal γ and a unique similarity mapping of 〈Eγ, γ〉 with 〈r, u〉.
Proof
Let F = {〈v, w〉|w ∈ u − v ∧ (∀z)(z ∈ u − v ⇒ 〈z, w〉 ∉ r)}. F is a function such that, 
if v is a subset of u and u − v ≠ ∅, then F′v is the r-least element of u − v. Let 
X = {〈v, w〉|〈R(v), w〉 ∈ F}. Now we use a definition by transfinite induction 
(Proposition 4.14) to obtain a function Y with On as its domain such that (∀α)
(Y′α = X′ (α   Y)). Let W = {α|Y′′α ⊆ u ∧ u − Y′′α ≠ ∅}. Clearly, if α ∈ W and β ∈ α, 
then β ∈ W. Hence, either W = On or W is some ordinal γ. (If W ≠ On, let γ be the 
least ordinal in On − W.) If α ∈ W, then Y′α = X′ (α   Y) is the r-least element of 
u − Y′′α; so, Y′α ∈ u and, if β ∈ α, Y′α ≠ Y′β. Thus, Y is a one-one function on W 
and the range of Y restricted to W is a subset of u. Now, let h = (W   Y) and f
h
=
⌣
; 
that is, let f be the inverse of Y restricted to W. So, by the replacement axiom (R), 
W is a set. Hence, W is some ordinal γ. Let ɡ = γ   Y. Then ɡ is a one–one func-
tion with domain γ and range a subset u1 of u. We must show that u1 = u and 
that, if α and β are in γ and β <⚬ α, then 〈ɡ′β, ɡ′α〉 ∈ r. Assume α and β are in 
γ and β <⚬ α. Then ɡ′′β ⊆ ɡ′′α and, since ɡ′α ∈ u − ɡ′′α, ɡ′α ∈ u − ɡ′′β. But ɡ′′β 
is the r-least element of u − ɡ′′β. Hence, 〈ɡ′β, ɡ′α〉 ∈ r. It remains to prove that 
u1 = u. Now, u1 = Y′′γ. Assume u −u1 ≠ ∅. Then γ ∈ W. But W = γ, which yields 
a contradiction. Hence, u = u1. That γ is unique follows from Corollary 4.18(a).
Exercise
4.37	 Show that the conclusion of Proposition 4.19 also holds when u = ∅ and 
that the unique ordinal γ is, in that case, ∅.
Proposition 4.20
Let R be a well-ordering of a proper class X such that, for each y ∈ X, the class 
of all R-predecessors of y in X (i.e., the R-segment in X determined by y) is a set. 



260
Introduction to Mathematical Logic
Then R is “similar” to E⚬n; that is, there is a (unique) one–one mapping H of 
On onto X such that α ∈ β ⇔ 〈H′α, H′β〉 ∈ R.
Proof
Proceed as in the proof of Proposition 4.19. Here, however, W = On; also, one 
proves that R(Y) = X by using the hypothesis that every R-segment of X is a 
set. (If X − R(Y) ≠ ∅, then, if w is the R-least element of X − R(Y), the proper 
class On is the range of ⌣
Y, while the domain of ⌣
Y is the R-segment of X deter-
mined by w, contradicting the replacement axiom.)
Exercise
4.38	 Show that, if X is a proper class of ordinal numbers, then there 
is a unique one–one mapping H of On onto X such that α ∈ β ⇔ H′α 
∈ H′β.
4.3  Equinumerosity: Finite and Denumerable Sets
We say that two classes X and Y are equinumerous if and only if there is a one–
one function F with domain X and range Y. We shall denote this by X ≅ Y.
Definitions
	
X
Y
F
F
X
F
Y
X
Y
F
X
Y
F
F
≅
∧
=
∧
=
≅
∃
(
)
≅
for Fnc
for
1( )
( )
( )
(
)
D
R
Notice that ⊢(
)(
)(
(
)(
))
∀
∀
≅
⇔∃
≅
x
y x
y
z x
y
z
. Hence, a wf x ≅ y is predicative 
(that is, is equivalent to a wf using only set quantifiers).
Clearly, if X
Y
F≅
, then Y
X
G≅
, where G
F
=
⌣
. Also, if X
Y
F≅
1
 and Y
Z
F≅
2
, then X
Z
H≅
, 
where H is the composition F2 ⚬ F1. Hence, we have the following result.
Proposition 4.21
	
a.	⊢ X ≅ X
	
b.	⊢ X ≅ Y ⇒ Y ≅ X
	
c.	⊢ X ≅ Y ∧ Y ≅ Z ⇒ X ≅ Z



261
Axiomatic Set Theory
Proposition 4.22
	
a.	⊢ (X ≅ Y ∧ Z ≅ W ∧ X ∩ Z = ∅ ∧ Y ∩ W = ∅) ⇒ X ∪ Z ≅ Y ∪ W
	
b.	⊢ (X ≅ Y ∧ Z ≅ W) ⇒ X × Z ≅ Y × W
	
c.	⊢ X × {y} ≅ X
	
d.	⊢ X × Y ≅ Y × X
	
e.	⊢ (X × Y) × Z ≅ X × (Y × Z)
Proof
	
a.	Let X
Y
F≅
 and Z W
G≅
. Then X
Z
Y
W
H
∪
∪
≅
, where H = F ∪ G.
	
b.	Let X
Y
F≅
 and Z W
G≅
. Let H = {〈u, v〉|(∃x)(∃y)(x ∈ X ∧ y ∈ Z ∧ u = 〈x, y〉 
∧ v = 〈F′x, G′y〉)}. Then X
Z
Y W
H
×
≅
×
.
	
c.	Let F = {〈u, v〉|u ∈ X ∧ v = 〈u, y〉}. Then
 
X
X
y
F≅
×{ }.
	
d.	Let F = {〈u, v〉|(∃x)(∃y)(x ∈ X ∧ y ∈ Y ∧ u = 〈x, y〉 ∧ v = 〈y, x〉)}. Then 
X
Y
Y
X
F
×
≅
×
.
	
e.	Let F = {〈u, v〉|(∃x)(∃y)(∃z)(x ∈ X ∧ y ∈ Y ∧ z ∈ Z ∧ u = 〈〈x, y〉, z〉 ∧ v = 
〈x, 〈y, z〉〉)}. Then (
)
(
)
X
Y
Z
X
Y
Z
F
×
×
≅
×
×
.
Definition
XY for {u|u: Y → X}
XY is the class of all sets that are functions from Y into X.
Exercises
Prove the following.
4.39	 ⊢ (∀X)(∀Y)(∃X1)(∃Y1)(X ≅ X1 ∧ Y ≅ Y1 ∧ X1 ∩ Y1 = ∅)
4.40	 ⊢P (y) ≅ 2y (Recall that 2 = {∅, 1} and 1 = {∅}.)
4.41	 a.	 ⊢ ¬M(Y) ⇒ XY = ∅
	
b.	 ⊢ (∀x)(∀y) M(xy)
4.42	 a.	 ⊢ X∅ = 1
	
b.	 ⊢ 1y ≅ 1
	
c.	 ⊢ Y ≠ ∅ ⇒ ∅Y = ∅
4.43	 ⊢ X ≅ X{u}
4.44	 ⊢ X ≅ Y ∧ Z ≅ W ⇒ XZ ≅ YW
4.45 ⊢ X ∩ Y = ∅ ⇒ ZX∪Y ≅ ZX × ZY
4.46	 ⊢ (∀x)(∀y)(∀z) [(xy)z ≅ xy×z]
4.47	 ⊢ (X × Y)Z ≅ XZ × YZ
4.48	 ⊢ (∀x)(∀R)(R We x ⇒ (∃α)(x ≅ α))



262
Introduction to Mathematical Logic
We can define a partial order ≼ on classes such that, intuitively, X ≼ Y if 
and only if Y has at least as many elements as X.
Definitions
X ≼ Y for (∃Z)(Z ⊆ Y ∧ X ≅ Z)
	
(
)
X
Y
is equinumerous with a subclass of
X
Y
≺
 for X ≼ Y ∧ ¬(X ≅ Y)
	
(
)
Y
X
is strictly greater in size than
Exercises
Prove the following.
4.49	 ⊢ X ≼Y ⇔ (X ≺ Y ∨ X ≅ Y)
4.50	 ⊢ X ≼ Y ∧ ¬M(X) ⇒ ¬M(Y)
4.51	 ⊢ X ≼ Y ∧ (∃Z)(Z We Y) ⇒ (∃Z)(Z We X)
4.52	 ⊢ (∀α)(∀β)(α ≼ β ∨ β ≼ α) [Hint: Proposition 4.8(k).]
Proposition 4.23
	
a.	⊢ X ≼ X ∧ ¬(X ≺ X)
	
b.	⊢ X ⊆ Y ⇒ X ≼ Y
	
c.	⊢ X ≼ Y ∧ Y ≼ Z ⇒ X ≼ Z
	
d.	⊢ X ≼ Y ∧ Y ≼ X ⇒ X ≅ Y (Bernstein’s theorem)
Proof
	(a), (b) These proofs are obvious.
	
c.	Assume X
Y
Y
Y
Y
Z
Z
Z
F
G
≅
∧
⊆
∧
≅
∧
⊆
1
1
1
1
. Let H be the composition of 
F and G. Then R
R
H
Z
X
H
H
(
) ⊆
∧
≅
(
). So, X ≼ Z.
	
d.	There are many proofs of this nontrivial theorem. The following one 
was devised by Hellman (1961). First we derive a lemma.
Lemma
Assume X ∩ Y = ∅, X ∩ Z = ∅ and Y ∩ Z = ∅, and let X
X
Y
Z
F≅
∪
∪
. Then there 
is a G such that X
X
Y
G≅
∪
.
Proof
Define a function H on a subclass of X × ω as follows: 〈〈u, k〉, v〉 ∈ H if and 
only if u ∈ X and k ∈ ω and there is a function f with domain k′ such that 



263
Axiomatic Set Theory
f′∅ = F′u and, if j ∈ k, then f′j ∈ X and f′(j′) = F′(f′j) and f′k = v. Thus, H′(〈u, ∅〉) = 
F′u, H′(〈u, 1〉) = F′(F′u) if F′u ∈ X, and H′(〈u, 2〉) = F′(F′(F′u)) if F′u and F′(F′u) 
are in X, and so on. Let X* be the class of all u in X such that (∃y)(y ∈ ω ∧ 
〈u, y〉 ∈ D (H) ∧ H′(〈u, y〉) ∈ Z). Let Y* be the class of all u in X such that (∀y)
(y ∈ ω ∧ 〈u, y〉 ∈ D (H) ⇒ H′(〈u, y〉) ∉ Z). Then X = X * ∪ Y *. Now define G 
as follows: D (G) = X and, if u ∈ X *, then G′u = u, whereas, if u ∈ Y *, then 
G′u = F′u. Then X
X
Y
G≅
∪.(This is left as an exercise.)
Now, to prove Bernstein’s theorem, assume X
Y
Y
Y
Y
X
X
X
F
G
≅
∧
⊆
∧
≅
∧
⊆
1
1
1
1
. 
Let A = G′′Y1 ⊆ X1 ⊆ X. But A ∩ (X1 −A) = ∅, A ∩ (X −X1) = ∅ and (X −X1) 
∩ (X1 −A) = ∅. Also, X = (X −X1) ∪ (X1 −A) ∪ A, and the composition H of F 
and G is a one–one function with domain X and range A. Hence, A
X
H≅
. So, 
by the lemma, there is a one–one function D such that A
X
D≅
1 (since (X1 −A) ∪ 
A = X1). Let T be the composition of the functions H, D and 
⌣
G; that is, T′u = 
(Ğ)′(D′(H′u)). Then X
Y
T≅
, since X
A
H≅
 and A
X
D≅
1 and X
Y
G
1 ≅
.
Exercises
4.53	 Carry out the details of the following proof (due to J. Whitaker) 
of Bernstein’s theorem in the case where X and Y are sets. Let 
X
Y
Y
Y
Y
X
X
X
F
G
≅
∧
⊆
∧
≅
∧
⊆
1
1
1
1
. We wish to find a set Z ⊆ X such 
that G, restricted to Y − F″Z, is a one–one function of Y − F″Z onto X 
−Z. [If we have such a set Z, let H = (Z   F)∪((X − Z)   G); that is, H′x = 
F′x for x ∈ Z, and H′x = Ğ′x for x ∈ X −Z. Then X
Y
H≅
.] Let Z = {x|(∃u)
(u ⊆ X ∧ x ∈ u ∧ G″(Y − F″u) ⊆ X − u)}. Notice that this proof does not 
presuppose the definition of ω nor any other part of the theory of 
ordinals.
4.54	 Prove: (a) ⊢ X ≼ X ∪ Y (b) ⊢ X ≺ Y ⇒ ¬(Y ≺ X) (c) ⊢ X ≺ Y ∧ Y ≼ Z ⇒ 
X ≺ Z
Proposition 4.24
Assume X ≼ Y and A ≼ B. Then:
	
a.	Y ∩ B = ∅ ⇒ X ∪ A ≼ Y ∪ B
	
b.	X × A ≼ Y × B
	
c.	XA ≼ YB if B is a set and ¬(X = A = Y = ∅ ∧ B ≠ ∅)
Proof
	
a.	Assume X
Y
Y
F≅
⊆
1
 and A
B
B
G≅
⊆
1
. Let H be a function with domain 
X ∪ A such that H′x = F′x for x ∈ X, and H′x = G′x for x ∈ A −X. Then 
X
A
H X
A
Y
B
H
∪
≅
′′
∪
⊆
∪
(
)
.
	
b.	and (c) are left as exercises.



264
Introduction to Mathematical Logic
Proposition 4.25
	
a.	⊢ ¬(∃f)(Fnc(f) ∧ D (f) = x ∧ R (f) = P (x)). (There is no function from x 
onto P (x).)
	
b.	⊢ x ≺ P (x) (Cantor’s theorem)
Proof
	
a.	Assume Fnc(f) ∧D (f) = x ∧ R (f) = P (x). Let y = {u|u ∈ x ∧ u ∉ f′u}. 
Then y ∈ P (x). Hence, there is some z in x such that f′z = y. But, (∀u)(u 
∈ y ⇔ u ∈ x ∧ u ∉ f′u). Hence, (∀u)(u ∈ f′z ⇔ u ∈ x ∧ u ∉ f′u). By rule A4, 
z ∈ f′z ⇔ z ∈ x ∧ z ∉ f′z. Since z ∈ x, we obtain z ∈ f′z ⇔ z ∉ f′z, which 
yields a contradiction.
	
b.	Let f be the function with domain x such that f′u = {u} for each u in x. 
Then f″x ⊆ P (x) and f is one–one. Hence, x ≼ P (x). By part (a), x ≅ P (x) 
is impossible. Hence, x ≺ P (x).
In naive set theory, Proposition 4.25(b) gives rise to Cantor’s paradox. If we 
let x = V, then V ≺ P (V). But P (V) ⊆V and, therefore, P (V) ≼ V. From V ≺ P (V), 
we have V ≼ P (V). By Bernstein’s theorem, V ≅ P (V), contradicting V ≺ P (V). 
In NBG, this argument is just another proof that V is not a set.
Notice that we have not proved ⊢ (∀x)(∀y)(x ≼ y ∨ y ≼ x). This intuitively 
plausible statement is, in fact, not provable, since it turns out to be equivalent 
to the axiom of choice (which will be discussed in Section 4.5).
The equinumerosity relation ≅ has all the properties of an equivalence 
relation. We are inclined, therefore, to partition the class of all sets into 
equivalence classes under this relation. The equivalence class of a set x would 
be the class of all sets equinumerous with x. The equivalence classes are 
called Frege–Russell cardinal numbers. For example, if u is a set and x = {u}, then 
the equivalence class of x is the class of all singletons {v} and is referred to 
as the cardinal number 1c. Likewise, if u ≠ v and y = {u, v}, then the equiva-
lence class of y is the class of all sets that contain exactly two elements and 
would be the cardinal number 2c; that is 2c is {x|(∃w)(∃z)(w ≠ z ∧ x = {w, z})}. 
All the Frege–Russell cardinal numbers, except the cardinal number 
Oc of ∅ (which is {∅}), turn out to be proper classes. For example, V ≅ 1c. 
(Let F′x = {x} for all x. Then V
F≅1c.) But, ¬M(V). Hence, by the replacement 
axiom, ¬M(1c).
Exercise
4.55	 Prove ⊢ ¬M(2c).
Because all the Frege–Russell cardinal numbers (except Oc) are proper 
classes, we cannot talk about classes of such cardinal numbers, and it is dif-
ficult or impossible to say and prove many interesting things about them. 



265
Axiomatic Set Theory
Most assertions one would like to make about cardinal numbers can be 
paraphrased by the suitable use of ≅, ≼, and ≺. However, we shall see later 
that, given certain additional plausible axioms, there are other ways of defin-
ing a notion that does essentially the same job as the Frege–Russell cardinal 
numbers.
To see how everything we want to say about cardinal numbers can be said 
without explicit mention of cardinal numbers, consider the following treat-
ment of the “sum” of cardinal numbers.
Definition
X +cY for (X × {∅}) ∪ (Y × {1})
Note that ⊢ ∅ ≠ 1 (since 1 is {∅}). Hence, X × {∅} and Y × {1} are disjoint 
and, therefore, their union is a class whose “size” is the sum of the “sizes” of 
X and Y.
Exercise
4.56	 Prove:
	
a.	 ⊢ X ≼ X +c Y ∧ Y ≼ X +c Y
	
b.	 ⊢ X ≅ A ∧ Y ≅ B ⇒ X +c Y ≅ A + cB
	
c.	 ⊢ X +c Y ≅ Y +c X
	
d.	 ⊢ M(X +c Y) ⇔ M(X) ∧ M(Y)
	
e.	 ⊢ X +c (Y +c Z) ≅ (X +c Y) +c Z
	
f.	 ⊢ X ≼ Y ⇒ X +c Z ≼ Y +c Z
	
g.	 ⊢ X +c X = X × 2 (Recall that 2 is {∅, 1}.)
	
h.	 ⊢XY +c
 Z ≅ XY × XZ
	
i.	 ⊢ x ≅ x +c 1 ⇒ 2x +c x ≅ 2x
4.3.1  Finite Sets
Remember that ω is the set of all ordinals α and all smaller ordinals are 
successor ordinals or ∅. The elements of ω are called finite ordinals, and the 
elements of On – ω are called infinite ordinals. From an intuitive standpoint, 
ω consists of ∅, 1, 2, 3, …, where each term in this sequence after ∅ is the 
successor of the preceding term. Note that ∅ contains no members, 1 = {∅} 
and contains one member, 2 = {∅, 1} and contains two members, 3 = {∅, 1, 2} 
and contains three members, etc. Thus, it is reasonable to think that, for each 
intuitive finite number n, there is exactly one finite ordinal that contains 
exactly n members. So, if a class has n members, it should be equinumerous 
with a finite ordinal. Therefore, a class will be called finite if and only if it is 
equinumerous with a finite ordinal.



266
Introduction to Mathematical Logic
Definition
	
Fin
for
is finite
(
)
(
)(
)
(
)
X
X
X
∃
∈
∧
≅
α α
ω
α
Exercise
4.57	 Prove:
	
a.	 ⊢ Fin(X) ⇒ M(X) (Every finite class is a set)
	
b.	 ⊢ (∀α)(α ∈ ω ⇒ Fin(α)) (Every finite ordinal is finite.)
	
c.	 ⊢ Fin(X) ∧ X ≅ Y ⇒ Fin(Y)
Proposition 4.26
	
a.	⊢ (∀α)(α ∉ ω ⇒ α ≅ α′).
	
b.	⊢ (∀α)(∀β)(α ∈ ω ∧ α ≠ β ⇒ ¬(α ≅ β)). (No finite ordinal is equinumer-
ous with any other ordinal.)
	
c.	⊢ (∀α)(∀x)(α ∈ ω ∧ x ⊂ α ⇒ ¬(α ≅ x)). (No finite ordinal is equinumer-
ous with a proper subset of itself.)
Proof
	
a.	Assume α ∉ ω. Define a function f with domain α′ as follows: f′δ = δ′ 
if δ ∈ ω; f′δ = δ if δ ∈ α′ ∧ δ ∉ ω ∪ {α}; and f′α = ∅. Then ′≅
α
α
f
.
	
b.	Assume this is false, and let α be the least ordinal such that α ∈ ω 
and there is β ≠ α such that α ≅ β. Hence, α <⚬ β. (Otherwise, β would 
be a smaller ordinal than α and β would also be in ω, and β would 
be equinumerous with another ordinal, namely, α.) Let α
β
≅
f
. If α = ∅, 
then f = ∅ and β = ∅, contradicting α ≠ β. So, α ≠ ∅. Since α ∈ ω, α = δ′ 
for some δ ∈ ω. We may assume that β = γ′ for some γ. (If β ∈ ω, then 
β ≠ ∅; and if β ∉ ω, then, by part (a), β ≅ β′ and we can take β′ instead 
of β.) Thus, ′ =
≅′
δ
α
γ
f
. Also, δ ≠ γ, since α ≠ β.
	
Case 1. f′δ = γ. Then δ
γ
≅
g , where ɡ = δ    f.
	
	 Case 2. f′δ ≠ γ. Then there is some μ ∈ δ such that f′μ = γ. Let h = ((δ  f) − 
{〈μ, γ〉}) ∪ {〈μ, f′δ〉}; that is, let h′τ = f′τ if τ ∉ {δ, μ}, and h′μ = f′δ. 
Then δ
γ
≅
h .
	
	 In both cases, δ is a finite ordinal smaller than α that is equinumer-
ous with a different ordinal γ, contradicting the minimality of α.
	
c.	Assume β ∈ ω ∧ x ⊂ β ∧ β ≅ x holds for some β, and let α be the least 
such β. Clearly, α ≠ ∅; hence, α = γ′ for some γ. But, as in the proof 
of part (b), one can then show that γ is also equinumerous with a 
proper subset of itself, contradicting the minimality of α.



267
Axiomatic Set Theory
Exercises
4.58	 Prove: ⊢ (∀α)(Fin(α) ⇔ α ∈ ω).
4.59	 Prove that the axiom of infinity (I) is equivalent to the following 
sentence.
	
( )
(
)((
)(
)
(
)(
(
)(
)))
∗
∃
∃
∈
∧∀
∈
⇒∃
∈
∧
⊂
x
u u
x
y y
x
z z
x
y
z
Proposition 4.27
	
a.	⊢ Fin(X) ∧ Y ⊆ X ⇒ Fin(Y)
	
b.	⊢ Fin(X) ⇒ Fin(X ∪ {y})
	
c.	⊢ Fin(X) ∧ Fin(Y) ⇒ Fin(X ∪ Y)
Proof
	
a.	Assume Fin(X) ∧ Y ⊆ X. Then X ≅ α, where α ∈ ω. Let g = Y   f and 
W = g″Y ⊆ α. W is a set of ordinals, and so, EW is a well-ordering of 
W. By Proposition 4.19, 〈EW, W〉 is similar to 〈Eβ, β〉 for some ordinal 
β. Hence, W ≅ β. In addition, β ≤⚬ α. (If α <⚬ β, then the similarity of 
〈Eβ, β〉 to 〈EW, W〉 contradicts Corollary 4.17.) Since α ∈ ω, β ∈ ω. From 
Y
W
W
g≅
∧
≅β, it follows that Fin(Y).
	
b.	If y ∈ X, then X ∪ {y} = X and the result is trivial. So, assume y ∉ X. 
From Fin(X) it follows that there is a finite ordinal α and a func-
tion f such that α ≅
f X. Let g = f ∪ {〈α, y〉}. Then ′≅
∪
α
g X
y
{ }. Hence, 
Fin(X ∪ {y}).
	
c.	Let Z
u u
x
y
f
x
u
y
x
y
f
=
∈
∧∀
∀
∀
≅
∧
⇒
∪
{ |
(
)(
)(
)(
( )
(
))}
ω
Fin
Fin
. We must 
show that Z = ω. Clearly, ∅ ∈ Z, for if x ≅ ∅, then x = ∅ and x ∪ y = y. 
Assume that α ∈ Z. Let x
f≅′
α  and Fin(y). Let w be such that f′w = α 
and let x1 = x −{w}. Then x1 ≅ α. Since α ∈ Z, Fin(x1 ∪ y). But x ∪ y = 
(x1 ∪ y) ∪ {w}. Hence, by part (b), Fin(x ∪ y). Thus, α′ ∈ Z. Hence, by 
Proposition 4.11(c), Z = ω.
Definitions
DedFin(X) for M(X) ∧ (∀Y)(Y ⊂ X ⇒ ¬(X ≅ Y))
(X is Dedekind-finite, that is, X is a set that is not equinumerous with any 
proper subset of itself)
DedInf(X) for M(X) ∧ ¬DedFin(X)
(X is Dedekind-infinite, that is, X is a set that is equinumerous with a proper 
subset of itself)



268
Introduction to Mathematical Logic
Corollary 4.28
(∀x)(Fin(x) ⇒ DedFin(x)) (Every finite set is Dedekind-finite)*
Proof
This follows easily from Proposition 4.26(c) and the definition of “finite.”
Definitions
Inf(X) for ¬Fin(X)	
(X is infinite)
Den(X) for X ≅ ω	
(X is denumerable)
Count(X) for Fin(X) ∨ Den(X)	
(X is countable)
Exercise
4.60	 Prove:
	
a.	 ⊢ Inf(X) ∧ X ≅ Y ⇒ Inf(Y)
	
b.	 ⊢ Den(X) ∧ X ≅ Y ⇒ Den(Y)
	
c.	 ⊢ Den(X) ⇒ M(X)
	
d.	 ⊢ Count(X) ∧ X ≅ Y ⇒ Count(Y)
	
e.	 ⊢ Count(X) ⇒ M(X)
Proposition 4.29
	
a.	⊢ Inf(X) ∧ X ⊆ Y ⇒ Inf(Y)
	
b.	⊢ Inf(X) ⇔ Inf(X ∪ {y})
	
c.	⊢ DedInf(X) ⇒ Inf(X)
	
d.	⊢ Inf(ω)
Proof
	
a.	This follows from Proposition 4.27(a).
	
b.	⊢ Inf(X) ⇒ Inf(X ∪ {y}) by part (a), and ⊢ Inf(X ∪ {y}) ⇒ Inf(X) by 
Proposition 4.27(b)
	
c.	Use Corollary 4.28.
	
d.	⊢ ω ∉ ω. If Fin(ω), then ω ≅ α for some α in ω, contradicting Proposition 
4.26(b).
*	 The converse is not provable without additional assumptions, such as the axiom of choice.



269
Axiomatic Set Theory
Proposition 4.30
⊢ (∀v)(∀z)(Den(v) ∧ z ⊆ v ⇒ Count(z)). (Every subset of a denumerable set is 
countable.)
Proof
It suffices to prove that z ⊆ ω ⇒ Fin(z) ∨ Den(z). Assume z ⊆ ω ∧ ¬Fin(z). Since 
¬Fin(z), for any α in z, there is some β in z with α <⚬ β. (Otherwise, z ⊆ α′ and, 
since Fin(α′), Fin(z).), Let X be a function such that, for any α in ω, X′α is the 
least ordinal β in z with α <⚬ β. Then, by Proposition 4.14(c) (with δ = ω), there 
is a function Y with domain ω such that Y′∅ is the least ordinal in z and, for 
any γ in ω, Y′(γ′) is the least ordinal β in z with β >⚬ Y′γ. Clearly, Y is one–one, 
D(Y) = ω, and Y″ω ⊆ z. To show that Den(z), it suffices to show that Y″ω = z. 
Assume z − Y″ω ≠ ∅. Let δ be the least ordinal in z − Y″ω, and let τ be the least 
ordinal in Y″ω with τ >⚬ δ. Then τ = Y′σ for some σ in ω. Since δ <⚬ τ, σ ≠ ∅. 
So, σ = μ′ for some μ in ω. Then τ = Y′σ is the least ordinal in z that is greater 
than Y′μ. But δ >⚬ Y′μ, since τ is the least ordinal in Y″ω that is greater than δ. 
Hence, τ ≤⚬ δ, which contradicts δ <⚬ τ.
Exercises
4.61	 Prove: ⊢ Count(X) ∧ Y ⊆ X ⇒ Count(Y).
4.62	 Prove:
	
a.	 ⊢ Fin(X) ⇒ Fin(P (X))
	
b.	 ⊢Fin(X) ∧ (∀ y)(y ∈ X ⇒ Fin(y)) ⇒ Fin(⋃ X)
	
c.	 ⊢ X ≼ Y ∧ Fin(Y) ⇒ Fin(X)
	
d.	 ⊢ Fin(P (X)) ⇒ Fin(X)
	
e.	 ⊢Fin(⋃ X)⇒Fin(X) ∧ (∀ y)(y ∈ X ⇒ Fin(y))
	
f.	 ⊢ Fin(X) ⇒ (X ≼ Y ∨ Y ≼ X)
	
g.	 ⊢ Fin(X) ∧ Inf(Y) ⇒ X ≺ Y
	
h.	 ⊢ Fin(X) ∧ Y ⊂ X ⇒ Y ≺ X
	
i.	 ⊢ Fin(X) ∧ Fin(Y) ⇒ Fin(X × Y)
	
j.	 ⊢ Fin(X) ∧ Fin(Y) ⇒ Fin(XY)
	
k.	 ⊢ Fin(X) ∧ y ∉ X ⇒ X ≺ X ∪ {y}
4.63	 Define X to be a minimal (respectively, maximal) element of Y if and only 
if X ∈ Y and (∀y)(y ∈ Y ⇒ ¬(y ⊂ X)) (respectively, (∀y)(y ∈ Y ⇒ ¬(X ⊂ y))). 
Prove that a set Z is finite if and only if every nonempty set of subsets 
of Z has a minimal (respectively, maximal) element (Tarski, 1925).



270
Introduction to Mathematical Logic
4.64	 Prove:
	
a.	 ⊢ Fin(X) ∧ Den(Y) ⇒ Den(X ∪ Y)
	
b.	 ⊢ Fin(X) ∧ Den(Y) ∧ X ≠ ∅ ⇒ Den(X × Y)
	
c.	 ⊢ (∀x)[DedInf(x) ⇔ (∃y)(y ⊆ x ∧ Den(y))]. (A set is Dedekind-infinite 
if and only if it has a denumerable subset)
	
d.	 ⊢ (∀x)[(∃y)(y ⊆ x ∧ Den(y)) ⇔ ω ≼ x]
	
e.	 ⊢ (∀α)(α ∉ ω ⇒ DedInf(α)) ∧ (∀α)(Inf(α) ⇒ α ∉ ω)
	
f.	 ⊢ (∀x)(∀y)(y ∉ x ⇒ [DedInf(x) ⇔ x ≅ x ∪ {y}])
	
g.	 ⊢ (∀x)(ω ≼ x ⇔ x +c 1 ≅ x)
4.65	 If NBG is consistent, then, by Proposition 2.17, NBG has a denumer-
able model. Explain why this does not contradict Cantor’s theorem, 
which implies that there exist nondenumerable infinite sets (such as 
P (ω)). This apparent, but not genuine, contradiction is sometimes called 
Skolem’s paradox.
4.4  Hartogs’ Theorem: Initial Ordinals—Ordinal Arithmetic
An unjustly neglected proposition with many uses in set theory is Hartogs’ 
theorem.
Proposition 4.31 (Hartogs, 1915)
⊢ (∀x)(∃α)(∀y)(y ⊆ x ⇒ ¬(α ≅ y)). (For any set x, there is an ordinal that is not 
equinumerous with any subset of x.)
Proof
Assume that every ordinal α is equinumerous with some subset y of x. 
Hence, y
f≅α for some f. Define a relation r on y by stipulating that 〈u, v〉 
∈ r if and only if f′u ∈ f′v. Then r is a well-ordering of y such that 〈r, y〉 
is similar to 〈Eα, α〉. Now define a function F with domain On such that, 
for any α, F′α is the set w of all pairs 〈z, y〉 such that y ⊆ x, z is a well-
ordering of y, and 〈Eα, α〉 is similar to 〈z, y〉. (w is a set, since w ⊆ P (x × x) × 
P (x).) Since, F″(On) ⊆ P (P (x × x) × P (x)), F″(On) is a set. F is one–one; 
hence, On
F F On
=
″
″
⌣
(
(
)) is a set by the replacement axiom, contradicting 
Proposition 4.8(h).



271
Axiomatic Set Theory
Definition
Let H denote the function with domain V such that, for every x, H ′x is the 
least ordinal α that is not equinumerous with any subset of x. (H is called 
Hartogs’ function.)
Corollary 4.32
	
(
)(
( ))
∀
′
≤
x
x
x
H
PPPP
Proof
With each β <⚬ H ′x, associate the set of relations r such that r ⊆ x × x, r is a 
well-ordering of its field y, and 〈r, y〉 is similar to 〈Eβ, β〉. This defines a one–
one function from H ′x into PP (x × x). Hence, H ′x ≼ PP (x × x). By Exercise 
4.12(s), x × x ⊆ PP (x). So, PP (x × x) ⊆ PPPP (x), and therefore, H ′x ≼ PPPP (x).
Definition
	
Init
for
is an
(
)
(
)(
(
))
(
)
X
X
On
X
X
X
initial ordinal
∈
∧∀
<°
⇒¬
≅
β β
β
An initial ordinal is an ordinal that is not equinumerous with any smaller 
ordinal.
Exercises
4.66	 a.	 ⊢ (∀α)(α ∈ ω ⇒ Init(α)). (Every finite ordinal is an initial ordinal.)
	
b.	 ⊢ Init(ω).
	
[Hint: Use Proposition 4.26(b) for both parts.]
4.67	 Prove:
	
a.	 For every x, H ′x is an initial ordinal.
	
b.	 For any ordinal α, H ′α is the least initial ordinal greater than α.
	
c.	 For any set x, H ′x = ω if any only if x is infinite and x is Dedekind-
finite. [Hint: Exercise 4.64(c).]
Definition by transfinite induction (Proposition 4.14(b)) yields a function G 
with domain On such that
	
G
G
G
G
G
′∅=
′(
) =
′
′
(
)
′
=
″
′
ω
α
α
α
λ
λ
H
for every
for every limit ordin
∪(
( ))
al λ



272
Introduction to Mathematical Logic
Proposition 4.33
	
a.	⊢ (∀α)(Init(G′α) ∧ ω ≤⚬ G′α ∧ (∀β)(β <⚬ α ⇒ G′β <⚬ G′α))
	
b.	⊢ (∀α)(α ≤⚬ G′α)
	
c.	⊢ (∀β)(ω ≤⚬ β ∧ Init(β) ⇒ (∃α)(G′α = β))
Proof
	
a.	Let X = {α|Init(G′α) ∧ ω ≤⚬ G′α ∧ (∀β)(β <⚬ α ⇒ G′β <⚬ G′α)}.
	
	 We must show that On ⊆ X. To do this, we use the second form of 
transfinite induction (Proposition 4.13(a)). First, ∅ ∈ X, since G′∅ = ω. 
Second, assume α ∈ X. We must show that α′ ∈ X. Since α ∈ X, G′α 
is an infinite initial ordinal such that (∀β)(β <⚬ α ⇒ G′β <⚬ G′α). By 
definition, G′(α′) = H ′(G′α), the least initial ordinal >⚬ G′(α). Assume 
β <⚬ α′. Then β <⚬ α ∨ β = α. If β <⚬ α, then, since α ∈ X, G′β <⚬ G′α <⚬ 
G′(α′). If β = α, then G′β = G′α <⚬ G′(α′). In either case, G′β <⚬ G″(α′), 
Hence, α′ ∈ X. Finally, assume Lim(α) ∧ (∀β)(β <o α ⇒ β ∈ X). We 
must show that α ∈ X. By definition, G′α = ∪ (G′(α)). Now consider 
any β <⚬ α. Since Lim(α), β′ <⚬ α. By assumption, β′ ∈ X, that is, G′(β′) 
is an infinite initial ordinal such that, for any γ <⚬ β′, G′γ <⚬ G′(β′). It 
follows that G″(α) is a nonempty set of ordinals without a maximum 
and, therefore, by Proposition 4.12, G′α, which is ∪ (G″(a)), is a limit 
ordinal that is the least upper bound of G′(α). To conclude that G′α ∈ X, 
we must show that G′α is an initial ordinal. For the sake of contradic-
tion, assume that there exist δ such that δ <⚬ G′(α) and δ ≅ G′α. Since 
G′α is the least upper bound of G″(α), there must exist some μ in G″(α) 
such that δ <⚬ μ. Say, μ = G′β with β <⚬ α. So, δ ⊆ μ = G′β ⊂ G′(β′) ⊆ 
G′α ≅ δ. Since δ ⊂ G′(β′), δ ∈ G′(β′) and δ ≼ G′(β′). On the other hand, 
since G′(β′) ⊆ G′α ≅ δ, G′(β′) ≼ δ. By Bernstein’s theorem, δ ≅ G′(β′), 
contradicting the fact that G′(β′) is an initial ordinal.
	
b.	This follows from Corollary 4.16 and part (a).
	
c.	Assume, for the sake of contradiction, that there is an infinite initial 
ordinal that is not in the range of G, and let σ be the least such. 
By part (b), σ ≤⚬ G′σ and, by part (a), G′σ is an initial ordinal. Since 
σ is not in the range of G, σ <⚬ G′σ. Let μ be the least ordinal such that 
σ <⚬ G′μ. Clearly, μ ≠ ∅, since G′∅ = ω <⚬ σ. Assume first that μ is a suc-
cessor ordinal γ′. Then, by the minimality of μ, G′γ <⚬ σ. Since G′(γ′) = 
H ′(G′γ), G′(γ′) is the least initial ordinal greater than G′γ. However, 
this contradicts the fact that σ is an initial ordinal greater than G′γ 
and σ <⚬ G′(γ′). So, μ must be a limit ordinal. Since G′μ = ⋃ (G″(μ)), 
the least upper bound of G″(μ), and σ <⚬ G′μ, there is some δ <⚬ μ such 
that σ <⚬ G′δ <⚬ G′μ, contradicting the minimality of μ.
Thus, by Proposition 4.33, G is a one–one <⚬-preserving function from On 
onto the class of all infinite initial ordinals.



273
Axiomatic Set Theory
Notation
ωα for G′α
Hence, (a) ω∅ = ω; (b) ωα′ is the least initial ordinal greater than ωα; (c) for a 
limit ordinal λ, ωλ is the initial ordinal that is the least upper bound of the 
set of all ωγ with γ <⚬ λ. Moreover, ωα ≥⚬ α for all α. In addition, any infinite 
ordinal α is equinumerous with a unique initial ordinal ωβ ≤⚬ α, namely, with 
the least ordinal equinumerous with α.
Let us return now to ordinal arithmetic. We already have defined ordi-
nal addition, multiplication and exponentiation (see Examples 1–2 on 
pages 256–257 and Exercise 4.36).
Proposition 4.34
The following wfs are theorems.
	
a.	β +⚬ 1 = β′
	
b.	∅ +⚬ β = β
	
c.	∅ <⚬ β ⇒ (α <⚬ α +⚬ β ∧ β ≤⚬ α +⚬ β)
	
d.	β <⚬ γ ⇒ α +⚬ β <⚬ α +⚬ γ
	
e.	α +⚬ β = α +⚬ δ ⇒ β = δ
	
f.	α <⚬ β ⇒ (∃1 δ)(α +⚬ δ = β)
	
g.	∅≠
⊆
⇒
+
=
+
∈
∈
x
On
x
x
α
β
α
β
β
β


∪
∪(
)
	
h.	∅ <⚬ α ∧ 1 <⚬ β ⇒ α <⚬ α ×⚬ β
	
i.	∅ <⚬ α ∧ ∅ <⚬ β ⇒ α ≤⚬ α ×⚬ β
	
j.	γ <⚬ β ∧ ∅ <⚬ α ⇒ α ×⚬ γ <⚬ α ×⚬ β
	
k.	x
On
x
x
⊆
⇒
×
=
×
∈
∈
α
β
α
β
β
β


∪
∪(
)
Proof
	
a.	β +⚬ 1 = β +⚬(∅′) = (β +⚬ ∅)′ = β′
	
b.	Prove ∅ +⚬ β = β by transfinite induction (Proposition 4.13(a)). Let 
X = {β|∅ +⚬ β = β}. First, ∅ ∈ X, since ∅ +⚬ ∅ = ∅. If ∅ +⚬ γ = γ, then 
∅ +⚬ γ′ = (∅ +⚬ γ)′ = γ′. If Lim(α) and ∅ +⚬ τ = τ for all τ <⚬ α, then 
∅+
=
∅+
=
=
<
<




α
τ
τ
α
τ
α
τ
α
∪
∪
(
)
, since ∪τ
ατ
<
 is the least upper 
bound of the set of all τ <⚬ α, which is α.
	
c.	Let X = {β|∅ <⚬ β ⇒ α <⚬ α +⚬ β}. Prove X = On by transfinite 
induction. Clearly, ∅ ∈ X. If γ ∈ X, then α ≤⚬ α +⚬ γ; hence α ≤⚬ 
α +⚬ γ <⚬(α +⚬ γ)′ = α +⚬ γ′. If Lim(λ) and τ ∈ X for all τ <⚬ λ, then 
α
α
α
α
τ
α
λ
τ
λ
τ
λ
<
′ =
+
≤
+
=
+
<
°
<





1
∪
(
)
. The second part is left as an 
exercise.
	
d.	Let X = {γ|(∀α)(∀β)(β <⚬ γ ⇒ α +⚬ β <⚬ α +⚬ γ)} and use transfinite induc-
tion. Clearly, ∅ ∈ X. Assume γ ∈ X and β <⚬ γ′. Then β <⚬ γ or β = γ. If β 
<⚬ γ then, since γ ∈ X, α +⚬ β <⚬ α +⚬ γ <⚬(α +⚬ γ)′ = α +⚬ γ′. If β = γ, then 



274
Introduction to Mathematical Logic
α +⚬ β = α +⚬ γ <⚬ (α +⚬ γ)′ = α +⚬ γ′. Hence, γ′ ∈ X. Assume Lim(λ) and 
τ ∈ X for all τ <⚬ λ. Assume β <⚬ λ. Then β <⚬ τ for some τ <⚬ λ, since 
Lim(λ). Hence, since τ ∈ X, α +⚬ β <⚬ α +⚬ τ ≤⚬ ∪τ
λ α
τ
α
λ
<°
+
=
+
(
)
.


Hence, λ ∈ X.
	
e.	Assume α +⚬ β = α +⚬ δ. Now, either β <⚬ δ or δ <⚬ β or δ = β. If β <⚬ δ, then 
α +⚬ β <⚬ α +⚬ δ by part (d), and, if δ <⚬ β, then α +⚬ δ <⚬ α +⚬ β by part (d); 
in either case, we get a contradiction with α +⚬ β = α +⚬ δ. Hence, δ = β.
	
f.	The uniqueness follows from part (e). Prove the existence by induc-
tion on β. Let X = {β|α <⚬ β ⇒ (∃1 δ)(α +⚬ δ = β)}. Clearly, ∅ ∈ X. 
Assume γ ∈ X and α <⚬ γ′. Hence, α = γ or α <⚬ γ. If α = γ, then (∃δ)
(α +⚬ δ = γ′), namely, δ = 1. If α <⚬ γ, then, since γ ∈ X, (∃1 δ)(α +⚬ δ = γ). 
Take an ordinal σ such that α +⚬ σ = γ. Then α +⚬ σ′ = (α +⚬ σ)′ = γ′; 
thus, (∃δ)(α +⚬ δ = γ′); hence, γ′ ∈ X. Assume now that Lim(λ) and 
τ ∈ X for all τ <⚬ λ. Assume α <⚬ λ. Now define a function f such 
that, for α <⚬ μ <⚬ λ, f ′μ is the unique ordinal δ such that α +⚬ δ = μ. 
But λ
µ
α
µ
µ
λ
α
µ
λ
=
=
+
′
<
<
<
<
∪
∪




a
f
(
)

. Let ρ
µ
α
µ
λ
=
′
<
<
∪

 (
)
f
. Notice 
that, if α <⚬ μ <⚬ λ, then f′μ <° f′(μ′); hence, ρ is a limit ordinal. Then 
λ
α
µ
ρ α
σ
α
ρ
α
µ
λ
σ
=
+
′
=
+
=
+
<
<
<
∪
∪

o
o
(
)
(
)



f
.
	
g.	Assume ∅ ≠ x ⊆ On. By part (f), there is some δ such that 
α
δ
α
β
β
+
=
+
∈


∪
x(
). We must show that δ
β
β
=
∈
∪
x . If β ∈ x, then α +⚬ 
β ≤ ⚬α + ⚬δ. Hence, β ≤ ⚬δ by part (d). Therefore, δ is an upper bound 
of the set of all β in x. So, ∪β β
δ
∈
≤
x
 . On the other hand, if β ∈ x, then 
α
β
α
β
β
+
≤
+
∈


 ∪
x . Hence, α
δ
α
β
α
β
β
β
+
=
+
≤
+
∈
∈




∪
∪
x
x
(
)
. Hence, 
α
δ
α
β
α
β
β
β
+
=
+
≤
+
∈
∈




∪
∪
x
x
(
)
 and so, by part (d), δ
β
β
≤°
∈
∪
x . 
Therefore, δ
β
β
=
∈
∪
x .
	(h)–(k) are left as exercises.
Proposition 4.35
The following wfs are theorems.
	
a.	β ×o 1 = β ∧ 1 ×o β = β
	
b.	∅ ×o β = ∅
	
c.	(α +o β) +o γ = α +o (β +o γ)
	
d.	(α ×o β) ×o γ = α ×o (β ×o γ)
	
e.	α ×o (β +o γ) = (α ×o β) +o (α ×o γ)
	
f.	exp(β, 1) = β ∧ exp(1, β) = 1
	
g.	exp(exp(β, γ), δ) = exp(β, γ ×o δ)
	
h.	exp(β, γ +o δ) = exp(β, γ) ×o exp(β, δ)*
	
i.	α >o 1 ∧ β <o γ ⇒ exp(α, β) <o exp(α, γ)
*	 In traditional notation, the results of (f)–(h) would be written as β1 = β, 1β = 1, 
(
)
,
.
β
β
β
β
β
γ δ
γ
δ
γ
δ
γ
δ
=
=
×
×
+
o
o
o



275
Axiomatic Set Theory
Proof
	
a.	β ×o 1 = β ×o ∅′ = (β ×o ∅) +o β = ∅ +o β = β, by Proposition 4.34(b). 
Prove 1 ×o β = β by transfinite induction.
	
b.	Prove ∅ ×o β = ∅ by transfinite induction.
	
c.	Let X = {γ|(∀ α)(∀ β)((α +o β) +⚬ γ = α +o(β +o γ))}. ∅ ∈ X, since (α +o 
β) + o∅ = (α + oβ) = α + o(β + o∅). Now assume γ ∈ X. Then (α + oβ) + 
oγ′ = ((α +o β) +o γ)′ = (α +o (β +o γ))′ = α +o (β +o γ)′ = α +o (β +o γ′). 
Hence, γ′ ∈ X. Assume now that Lim(γ) and τ ∈ X for all τ <⚬ λ. Then 
(
)
((
)
)
(
(
))
(
)
α
β
γ
α
β
τ
α
β
τ
α
β
τ
τ
λ
τ
λ
τ
λ
+
+
=
+
+
=
+
+
=
+
+
<
<
<
o
o
o
o
o
o
o
o
o
o
o
∪
∪
∪
,
by Proposition 4.34(g), and this is equal to α +o(β +o λ).
	
(d)–(i) are left as exercises.
We would like to consider for a moment the properties of ordinal addition, 
multiplication and exponentiation when restricted to ω.
Proposition 4.36
Assume α, β, γ are in ω. Then:
	
a.	α +o β ∈ ω
	
b.	α ×o β ∈ ω
	
c.	exp(α, β) ∈ ω
	
d.	α +o β = β +o α
	
e.	α ×o β = β ×o α
	
f.	(α +o β) ×o γ = (α ×o γ) +o (β ×o γ)
	
g.	exp(α ×o β, γ) = exp(α, γ) ×o exp(β, γ)
Proof
	
a.	Use induction up to ω (Proposition 4.13(c)). Let X = {β|β ∈ ω ∧ (∀α)
(α ∈ ω ⇒ α +o β ∈ ω)}. Clearly, ∅ ∈ X. Assume β ∈ X. Consider any α ∈ 
ω. Then α +o β ∈ ω. Hence, α +o β′ = (α +o β)′ ∈ ω by Proposition 4.11(a). 
Thus, β′ ∈ X.
	
b.	and (c) are left as exercises.
	
d.	Lemma. ⊢ α ∈ ω ∧ β ∈ ω ⇒ α′ +o β = α +o β′. Let Y = {β|β ∈ ω ∧ (∀α)
(α ∈ ω ⇒ α′ +o β = α +⚬ β′)}. Clearly, ∅ ∈ Y. Assume β ∈ Y. Consider 
any α ∈ ω. So, α′ +o β = α +o β′. Then α′ +o β′ = (α′ +o β)′ = (α +o β′)′ = 
α +o(β′)′. Hence, β′ ∈ Y.
	
	 To prove (d), let X = {β|β ∈ ω ∧ (∀α)(α ∈ ω ⇒ α +o β = β +o α)}. Then ∅ ∈ X 
and it is easy to prove, using the lemma, that β ∈ X ⇒ β′ ∈ X.
(e)–(g) are left as exercises.
The reader will have noticed that we have not asserted for ordinals cer-
tain well-known laws, such as the commutative laws for addition and 



276
Introduction to Mathematical Logic
multiplication, that hold for other familiar number systems. In fact, these 
laws fail for ordinals, as the following examples show.
Examples
	
1.	(∃α)(∃β)(α +o β ≠ β +o α)
	
1
1
1
+
=
+
=
+
=
′ >
<
o
o
o
o
o
ω
α
ω
ω
ω
ω
α
ω
(
)
∪
	
2.	(∃α)(∃β)(α ×o β ≠ β ×o α)
	
2
2
2
1
1
1
1
×
=
×
=
×
=
×
+
=
×
+
×
=
+
>
<
o
o
o
o
o
o
o
o
o
o
o
ω
α
ω
ω
ω
ω
ω
ω
ω
ω
α
ω
(
)
(
)
(
)
(
)
∪
	
3.	(∃α)(∃β)(∃γ)((α +o β) ×o γ ≠ (α ×o γ) +o(β ×o γ))
	
(
)
(
)
(
)
1
1
2
1
1
+
×
=
×
=
×
+
×
=
+
>
o
o
o
o
o
o
o
o
ω
ω
ω
ω
ω
ω
ω
ω
	
4.	(∃α)(∃β)(∃γ)(exp(α ×o β, γ) ≠ exp(α, γ) ×o exp(β, γ))
	
exp(
, )
exp( , )
exp( , )
exp( , )
exp( , )
2
2
4
4
2
2
×
=
=
=
=
<
<
o
o
o
ω
ω
α
ω
ω
α
α
ω
α
ω
∪
∪
= ω
	
	 So, exp(2, ω) ×oexp(2, ω) = ω ×o ω >o ω.
Given any wf B of formal number theory S (see Chapter 3), we can associ-
ate with B a wf B * of NBG as follows: first, replace every “+” by “+⚬,” every “·” 
by “×⚬,” and every “ f
t
1
1( )” by “t ∪ {t}”*; then, if B is C ⇒ D or ¬C, respectively, 
and we have already found C * and D*, let B* be C * ⇒ D* or ¬ C *, respectively; 
if B is (∀x)C(x), replace it by (∀x)(x ∈ ω ⇒ C *(x)). This completes the definition 
of B *. Now, if x1, …, xn are the free variables (if any) of B, prefix (x1 ∈ ω ∧ … ∧ 
xn ∈ ω) ⇒ to B *, obtaining a wf B #. This amounts to restricting all variables 
*	 In abbreviated notation for S, “ f
t
1
1( )” is written as t′, and in abbreviated notation in NBG, 
“t ∪ {t}” is written as t′. So, no change will take place in these abbreviated notations.



277
Axiomatic Set Theory
to ω and interpreting addition, multiplication and the successor function on 
natural numbers as the corresponding operations on ordinals. Then every 
axiom B of S is transformed into a theorem B # of NBG. (Axioms (S1)–(S3) 
are obviously transformed into theorems, (S4) # is a theorem by Proposition 
4.10(c), and (S5)#–(S8)# are properties of ordinal addition and multiplica-
tion.) Now, for any wf B of S, B # is predicative. Hence, by Proposition 4.4, all 
instances of (S9)# are provable by Proposition 4.13(c). (In fact, assume B #(∅) ∧ 
(∀x)(x ∈ ω ⇒ (B #(x) ⇒ B#(x′)))). Let X = {y|y ∈ ω ∧ B #(y)}. Then, by Proposition 
4.13(c), (∀x)(x ∈ ω ⇒ B#(x)).) Applications of modus ponens are easily seen to 
be preserved under the transformation of B into B #. As for the generaliza-
tion rule, consider a wf B(x) and assume that B #(x) is provable in NBG. But 
B #(x) is of the form x ∈ ω ∧ y1 ∈ ω ∧…∧ yn ∈ ω ⇒ B*(x). Hence, y1 ∈ ω ∧…∧ yn 
∈ ω ⇒ (∀x)(x ∈ ω ⇒ B*(x)) is provable in NBG. But this wf is just ((∀x)B(x))#. 
Hence, application of Gen leads from theorems to theorems. Therefore, for 
every theorem B of S, B # is a theorem of NBG, and we can translate into 
NBG all the theorems of S proved in Chapter 3.
One can check that the number-theoretic function h such that, if x is the 
Gödel number of a wf B of S, then h(x) is the Gödel number of B #, and if x is 
not the Gödel number of a wf of S, then h(x) = 0, is recursive (in fact, primi-
tive recursive). Let K be any consistent extension of NBG. As we saw above, 
if x is the Gödel number of a theorem of S, then h(x) is the Gödel number of 
a theorem of NBG and, hence, also a theorem of K. Let S(K) be the extension 
of S obtained by taking as axioms all wfs B of the language of S such that B # 
is a theorem of K. Since K is consistent, S(K) must be consistent. Therefore, 
since S is essentially recursively undecidable (by Corollary 3.46), S(K) is 
recursively undecidable. Now, assume K is recursively decidable; that is, the 
set TK of Gödel numbers of theorems of K is recursive. But C
x
C
h x
T
T
S K
K
(
)( )
( ( ))
=
 
for any x, where CTS K
(
) and CTK are the characteristic functions of TS(K) and TK. 
Hence, TS(K) would be recursive, contradicting the recursive undecidability 
of S(K). Therefore, K is recursively undecidable, and thus, if NBG is consis-
tent, NBG is essentially recursively undecidable. Recursive undecidability of 
a recursively axiomatizable theory implies incompleteness (see Proposition 
3.47). Hence, NBG is also essentially incomplete. Thus, we have the following 
result: if NBG is consistent, then NBG is essentially recursively undecidable and 
essentially incomplete. (It is possible to prove this result directly in the same 
way that the corresponding result was proved for S in Chapter 3.)
Exercise
4.68	 Prove that a predicate calculus with a single binary predicate letter is 
recursively undecidable. [Hint: Use Proposition 3.49 and the fact that 
NBG has a finite number of proper axioms.]
There are a few facts about the “cardinal arithmetic” of ordinal numbers 
that we would like to deal with now. By “cardinal arithmetic” we mean 



278
Introduction to Mathematical Logic
properties connected with the operations of union (⋃), Cartesian product 
(×) and XY, as opposed to the properties of +⚬, ×⚬, and exp. Observe that × is 
distinct from ×⚬; also notice that ordinal exponentiation exp(α, β) has nothing 
to do with XY, the class of all functions from Y into X. From Example 4 on 
page 276 we see that exp(2, ω) is ω, whereas, from Cantor’s theorem, ω ≺ 2ω, 
where 2ω is the set of functions from ω into 2.
Proposition 4.37
	
a.	⊢ ω × ω ≅ ω
	
b.	⊢ 2 ≼ X ∧ 2 ≼ Y ⇒ X ∪ Y ≼ X × Y
	
c.	⊢ Den(x) ∧ Den(y) ⇒ Den(x ∪ y)
Proof
	
a.	Let f be a function with domain ω such that, if α ∈ ω, then f′α = 〈α, ∅〉. 
Then f is a one–one function from ω into a subset of ω × ω. Hence, ω 
≼ ω × ω. Conversely, let g be a function with domain ω × ω such that, 
for any 〈α, β〉 in ω × ω, g′〈α, β〉 = exp(2, α) ×⚬ exp(3, β). We leave it as 
an exercise to show that g is a one–one function from ω × ω into ω. 
Hence, ω × ω ≼ ω. So, by Bernstein’s theorem, ω × ω ≅ ω.
	
b.	Assume a1 ∈ X, a2 ∈ X, a1 ≠ a2, b1 ∈ Y, b2 ∈ Y, b1 ≠ b2. Define
	
′ =
〈
〉
∈
〈
〉
∈
−
≠
〈
〉
=
∈
−

f x
a b
x
X
a x
x
Y
X
x
b
a b
x
b
x
Y
X
1
1
1
1
2
2
1
,
,
,
if
if
and
if
and


	
	 Then f is a one–one function with domain X ∪ Y and range a subset 
of X × Y. Hence, X ∪ Y ≼ X × Y.
	
c.	Assume Den(x) and Den(y). Hence, each of x and y contains at least 
two elements. Then, by part (b), x ∪ y ≼ x × y. But x ≅ ω and y ≅ ω. 
Hence, x × y ≅ ω × ω. Therefore, x ∪ y ≼ ω × ω. By Proposition 4.30, 
either Den(x ∪ y) or Fin(x ∪ y). But x ⊆ x ∪ y and Den(x); hence, 
¬Fin(x ∪ y).
For the further study of ordinal addition and multiplication, it is quite useful 
to obtain concrete interpretations of these operations.
Proposition 4.38 (Addition)
Assume that 〈r, x〉 is similar to 〈Eα, α〉, that 〈s, y〉 is similar to 〈Eβ, β〉, and that 
x ∩ y = ∅. Let t be the relation on x ∪ y consisting of all 〈u, v〉 such that 



279
Axiomatic Set Theory
〈u, v〉 ∈ x × y or u ∈ x ∧ v ∈ x ∧ 〈u, v〉 ∈ r or u ∈ y ∧ v ∈ y ∧ 〈u, v〉 ∈ s (i.e., t is 
the same as r in the set x, the same as s in the set y, and every element of x 
t-precedes every element of y). Then t is a well-ordering of x ∪ y, and 〈t, x ∪ y〉 
is similar to 〈
+
〉
+
Eα
β α
β
o
o
,
.
Proof
First, it is simple to verify that t is a well-ordering of x ∪ y, since r is a well-
ordering of x and s is a well-ordering of y. To show that 〈t, x ∪ y〉 is similar 
to 〈
+
〉
+
Eα
β α
β
o
o
,
, use transfinite induction on β. For β = ∅, y = ∅. Hence, t = r, 
x ∪ y = x, and α +⚬ β = α. So, 〈t, α ∪ β〉 is similar to 〈
+
〉
+
Eα
β α
β
o
o
,
. Assume the 
proposition for γ and let β = γ′. Since 〈s, y〉 is similar to 〈Eβ, β〉, we have a 
function f with domain y and range β such that, for any u, v in y, 〈u, v〉 ∈ s if 
and only if f′u ∈ f′v. Let b
f
=
′
( )
⌣
γ, let y1 = y −{b} and let s1 = s ∩ (y1 × y1). Since 
b is the s-­maximum of y, it follows easily that s1 well-orders y1. Also, y1 f is 
a similarity mapping of y1 onto γ. Let t1 = t ∩ ((x ∪ y1) × (x ∪ y1)). By induc-
tive hypothesis, 〈t1, x ∪ y1〉 is similar to 〈
+
〉
+
Eα
γ α
γ
o
o
,
, by means of some 
similarity mapping ɡ with domain x ∪ y1 and range α +⚬ γ. Extend ɡ to ɡ1 = 
ɡ ∪ {〈b, α +⚬ γ〉}, which is a similarity mapping of x ∪ y onto (α +⚬ γ)′ = α +⚬ 
γ′ = α +⚬ β. Finally, if Lim(β) and our proposition holds for all τ <⚬ β, assume 
that f is a similarity mapping of y onto β. Now, for each τ <⚬ β, let y
f
τ
τ
=
′
( ) ,
⌣
 
sτ = s ∩ (yτ × yτ), and tτ = t ∩ ((x ∪ yτ) × (x ∪ yτ)). By inductive hypothesis 
and Corollary 4.18(b), there is a unique similarity mapping ɡτ of 〈tτ, x ∪ yτ〉 
with 〈
+
〉
+
Eα
τ α
τ
o
o
,
; also, if τ1 <⚬ τ2 <⚬ β, then, since (
)
x
y
∪
τ1   gτ2 is a similar-
ity mapping of 〈
∪
〉
t
x
y
τ
τ
1
1
,
 with 〈
+
〉
+
Eα
τ α
τ
o
o
1
1
,
 and, by the uniqueness of 
gτ1, (
)
x
y
∪
τ1   g
g
τ
τ
2
1
=
; that is, gτ2 is an extension of gτ1. Hence, if g
g
=
<
∪τ
β
τ
o
 
and λ
α
τ
τ
β
=
+
<
∪
o
o
(
), then ɡ is a similarity mapping of 〈
∪
〉
<
t
x
y
,
)
(
∪τ
β
τ
o
 with 
〈
〉
Eλ λ
,
. But, ∪τ
β
τ
<
∪
=
∪
o (
)
x
y
x
y and ∪τ
β α
τ
α
β
<
+
=
+
o
o
o
(
)
. This completes the 
transfinite induction.
Proposition 4.39 (Multiplication)
Assume that 〈r, x〉 is similar to 〈Eα, α〉 and that 〈s, y〉 is similar to 〈Eβ, β〉. Let 
the relation t on x × y consist of all pairs 〈〈u, v〉, 〈w, z〉〉 such that u and w are 
in x and v and z are in y, and either 〈v, z〉 ∈ s or (v = z ∧ 〈u, w〉 ∈ r). Then t is a 
well-ordering of x × y and 〈t, x × y〉 is similar to 〈
×
〉
×
Eα
β α
β
o
o
,
.*
Proof
This is left as an exercise. Proceed as in the proof of Proposition 4.38.
*	 The ordering t is called an inverse lexicographical ordering because it orders pairs as follows: 
first, according to the size of their second components and then, if their second components 
are equal, according to the size of their first components.



280
Introduction to Mathematical Logic
Examples
	
1.	2 ×o ω = ω. Let 〈r, x〉 = 〈E2, 2〉 and 〈s, y〉 = 〈Eω, ω〉. Then the Cartesian 
product 2 × ω is well-ordered as follows: 〈∅, ∅〉, 〈1, ∅〉, 〈∅, 1〉, 〈1, 1〉, 
〈∅, 2〉, 〈1, 2〉, …, 〈∅, n〉, 〈1, n〉, 〈∅, n + 1〉, 〈1, n + 1〉, …
	
2.	By Proposition 4.34(a), 2 = 1′ = 1 +o 1. Then by Proposition 4.35(e,a), 
ω ×o 2 = (ω ×o 1) +o(ω ×o 1) = ω +o ω. Let 〈r, x〉 = 〈Eω, ω〉 and 〈s, y〉 = 〈E2, 2〉. 
Then the Cartesian product ω × 2 is well-ordered as follows: 〈∅, ∅〉, 
〈1, ∅〉, 〈2, ∅〉, …, 〈∅, 1〉, 〈1, 1〉, 〈2, 1〉, …
Proposition 4.40
For all α, ωα × ωα ≅ ωα.
Proof
(Sierpinski, 1958) Assume this is false and let α be the least ordinal such that 
ωα × ωα ≅ ωα is false. Then ωβ × ωβ ≅ ωβ for all β <o α. By Proposition 4.37(a), 
α >o ∅. Now let P = ωα × ωα and, for β <o ωα, let Pβ = {〈γ, δ〉|γ +o δ = β}. First 
we wish to show that P
P
=
<
∪β
ω
β
α
o
. Now, if γ +o δ = β <o ωα, then γ ≤o β <o 
ωα and δ ≤o β <o ωα; hence, 〈γ, δ〉 ∈ ωα × ωα = P. Thus, ∪β
ω
β
α
<
⊆
o
P
P. To show 
that P
P
⊆
<
∪β
ω
β
α
o
, it suffices to show that, if γ <o ωα and δ <o ωα, then γ +o δ 
<o ωα. This is clear when γ or δ is finite. Hence, we may assume that γ and 
δ are equinumerous with initial ordinals ωσ ≤o γ and ωρ ≤o δ, respectively. 
Let ζ be the larger of σ and ρ. Since γ <o ωα and δ <o ωα, then ωζ <o ωα. Hence, 
by the minimality of α, ωζ × ωζ ≅ ωζ. Let x = γ × {∅} and y = δ × {1}. Then, by 
Proposition 4.38, x ∪ y ≅ γ +o δ. Since γ ≅ ωσ and δ ≅ ωρ, x ≅ ωσ × {∅} and y ≅ 
ωρ × {1}. Hence, since x ∩ y = ∅, x ∪ y ≅ (ωσ × {∅}) ∪ (ωρ × {1}). But, by Proposition 
4.37(b), (ωσ × {∅}) ∪ (ωρ × {1}) ≼ (ωσ × {∅}) × (ωρ × 1}) ≅ ωσ × ωρ ≼ ωζ × ωζ ≅ ωζ. 
Hence, γ +o δ ≼ ωζ <o ωα. It follows that γ +o δ <o ωα. (If ωα ≤o γ +o δ, then ωα ≼ 
ωζ. Since ωζ <o ωα, ωζ ≼ ωα. So, by Bernstein’s theorem, ωα ≅ ωζ, contradicting 
the fact that ωα is an initial ordinal.) Thus, P
P
=
<
∪β
ω
β
α
o
. Consider Pβ for any 
β <o ωα. By Proposition 4.34(f), for each γ ≤o β, there is exactly one ordinal 
δ such that γ +o δ = β. Hence, there is a similarity mapping from β′ onto Pβ, 
where Pβ is ordered according to the size of the first component γ of the pairs 
〈γ, δ〉. Define the following relation R on P. For any γ <o ωα, δ <o ωα, μ <o ωα, ν 
<o ωα, 〈〈γ, δ〉, 〈μ, ν〉〉 ∈ R if and only if either γ +o δ <o μ +o ν or (γ +o δ = μ +o ν ∧ 
γ <o μ). Thus, if β1 <o β2 <0 ωα, then the pairs in Pβ1 R-precede the pairs in Pβ2, 
and, within each Pβ, the pairs are R-ordered according to the size of their 
first components. One easily verifies that R well-orders P. Since P = ωα × ωα, 
it suffices now to show that 〈R, P〉 is similar to 〈
〉
Eω
α
α ω
,
. By Proposition 4.19, 
〈R, P〉 is similar to some 〈Eξ, ξ〉, where ξ is an ordinal. Hence, P ≅ ξ. Assume 
that ξ >o ωα. There is a similarity mapping f between 〈Eξ, ξ〉 and 〈R, P〉. Let 
b = f′(ωα); then b is an ordered pair 〈γ, δ〉 with γ <o ωα, δ <o ωα, and ωα  f is a 



281
Axiomatic Set Theory
similarity mapping between 〈
〉
Eω
α
α ω
,
 and the R-segment Y = SegR(P, 〈γ, δ〉) of 
P determined by 〈γ, δ〉. Then Y ≅ ωα. If we let β = γ +o δ, then, if 〈σ, ρ〉 ∈ Y, we 
have σ +o ρ ≤o γ +o δ = β; hence, σ ≤o β and ρ ≤o β. Therefore, Y ⊆ β′ × β′. But 
β′ <o ωα. Since β is obviously not finite, β′ ≅ ωμ with μ <o α. By the minimality 
of α, ωμ × ωμ ≅ ωμ. So, ωα ≅ Y ≼ ωμ, contradicting ωμ ≺ ωα. Thus, ξ ≤o ωα and, 
therefore, P ≼ ωα. Let h be the function with domain ωα such that h′β = 〈β, ∅〉 
for every β <o ωα. Then h is a one–one correspondence between ωα and the 
subset ωα × {∅} of P and, therefore, ωα ≼ P. By Bernstein’s theorem, ωα ≅ P, 
contradicting the definition of α. Hence, ωβ × ωβ ≅ ωβ for all β.
Corollary 4.41
If x ≅ ωα and y ≅ ωβ, and if γ is the maximum of α and β, then x × y ≅ ωγ and x 
∪ y ≅ ωγ. In particular, ωα × ωβ ≅ ωγ.
Proof
By Propositions 4.40 and 4.37(b), ωγ ≼ x ∪ y ≼ x × y ≅ ωα × ωβ ≼ ωγ × ωγ ≅ ωγ. 
Hence, by Bernstein’s theorem, x × y ≅ ωγ and x ∪ y ≅ ωγ.
Exercises
4.69	 Prove that the following are theorems of NBG.
	
a.	 x ≼ ωα ⇒ x ∪ ωα ≅ ωα
	
b.	 ωα +c ωα ≅ ωα
	
c.	 ∅ ≠ x ≼ ωα ⇒ x × ωα ≅ ωα
	
d.	 ∅ ≠ x ≺ ω ⇒ (ωα )x ≅ ωα
4.70	 Prove that the following are theorems of NBG
	
a.	 P (ωα) × P (ωα) ≅ P (ωα)
	
b.	 x ≼ P (ωα) ⇒ x ∪ P (ωα) ≅ P (ωα)
	
c.	 ∅ ≠ x ≼ P (ωα) ⇒ x × P (ωα) ≅ P (ωα)
	
d.	 ∅ ≠ x ≼ ωα ⇒ (P (ωα))x ≅ P (ωα)
	
e.	 1 ≺ x ≼ ωα ⇒ xωα ≅ (ωα )ωα ≅ (P  (ωα))ωα ≅ P  (ωα).
4.71	 Assume y ≠ ∅ ∧ y ≅ y +c y. (This assumption holds for y = ωα by Corollary 
4.41 and for y = P (ωα ) by Exercise 4.70(b). It will turn out to hold for all 
infinite sets y if the axiom of choice holds.) Prove the following proper-
ties of y.
	
a.	 Inf(y)
	
b.	 y ≅ 1 +cy
	
c.	 (∃u)(∃v)(y = u ∪ v ∧ u ∩ v = ∅ ∧ u ≅ y ∧ v ≅ y)



282
Introduction to Mathematical Logic
	
d.	 {z|z ⊆ y ∧ z ≅ y} ≅ P  (y)
	
e.	 {z|z ⊆ y ∧ Inf(z)} ≅ P  (y)
	
f.	 (
)(
(
)(
))
∃
≅
∧∀
∈
⇒
≠
f
y
y
u u
y
f u
u
f
‘
4.72	 Assume y ≅ y × y ∧ 1 ≺ y. (This holds when y = ωα by Proposition 4.40 
and for y = P (ωα) by Exercise 4.70(a). It is true for all infinite sets y if the 
axiom of choice holds.) Prove the following properties of y.
	
a.	 y ≅ y +c y
	
b.D	Let Perm(y) denote { |
}
f
y
y
f≅
. Then Perm(y) ≅ P  (y).
4.5  The Axiom of Choice: The Axiom of Regularity
The axiom of choice is one of the most celebrated and contested statements 
of the theory of sets. We shall state it in the next proposition and show its 
equivalence to several other important assertions.
Proposition 4.42
The following wfs are equivalent.
	
a.	Axiom of choice (AC). For any set x, there is a function f such that, for 
any nonempty subset y of x, f′y ∈ y. (f is called a choice function for x.)
	
b.	Multiplicative axiom (Mult). If x is a set of pairwise disjoint nonempty 
sets, then there is a set y (called a choice set for x) such that y contains 
exactly one element of each set in x:
	
(
)(
(
)(
))
(
)(
)(
(
)(
∀
∈
⇒
≠∅∧∀
∈
∧
≠
⇒
∩
= ∅
⇒
∃
∀
∈
⇒∃
∈
∩
u u
x
u
v v
x
v
u
v
u
y
u u
x
u
y
1ω ω
))
	
c.	Well-ordering principle (WO). Every set can be well-ordered: (∀x)(∃y)
(y We x).
	
d.	Trichotomy (Trich). (∀x)(∀y)(x ≼ y ∨ y ≼ x)*
	
e.	Zorn’s Lemma (Zorn). Any nonempty partially ordered set x, in which 
every chain (i.e., every totally ordered subset) has an upper bound, 
has a maximal element:
	
(
)(
)([(
)
(
)(
(
)(
(
)(
∀
∀
∧∀
⊆
∧
⇒
∃
∈
∧∀
∈
⇒
=
∨〈
x
y
y
x
u u
x
y
u
v v
x
w w
u
w
v
w
Part
Tot
,
)))]
(
)(
(
)(
,
)))
v
y
v v
x
w w
x
v w
y
〉∈
⇒
∃
∈
∧∀
∈
⇒〈
〉∉
*	 This is equivalent to (∀x)(∀y)(x ≺ y ∨ x ≅ y ∨ y ≺ x), which explains the name “trichotomy” for 
this principle.



283
Axiomatic Set Theory
Proof
	
1.	⊢ WO ⇒ Trich. Given sets x and y, then, by WO, x and y can be well-
ordered. Hence, by Proposition 4.19, x ≅ α and y ≅ β for some ordinals 
α and β. But, by Exercise 4.52, α ≼ β or β ≼ α. Therefore, x ≼ y or y ≼ x.
	
2.	⊢ Trich ⇒ WO. Given a set x, Hartogs’ theorem yields an ordinal α 
such that α is not equinumerous with any subset of x, that is, α ≼ x is 
false. So, by Trich, x ≼ α, that is, x is equinumerous with some subset 
y of α. Hence, by translating the well-ordering Ey of y to x, x can be 
well-ordered.
	
3.	⊢ WO ⇒ Mult. Let x be a set of nonempty pairwise disjoint sets. By 
WO, there is a well-ordering R of ⋃ x. Hence, there is a function f 
with domain x such that, for any u in x, f′u is the R-least element of u. 
(Notice that u is a subset of ⋃ x.)
	
4.	⊢ Mult ⇒ AC. For any set x, we can define a one–one function g such 
that, for each nonempty subset u of x, ɡ′u = u × {u}. Let x1 be the range 
of ɡ. Then x1 is a set of nonempty pairwise disjoint sets. Hence, by 
Mult, there is a choice set y for x1. Therefore, if u is a nonempty subset 
of x, then u × {u} is in x1, and so y contains exactly one element 〈v, u〉 in 
u × {u}. Then the function f such that f′u = v is a choice function for x.
	
5.	⊢ AC ⇒ Zorn. Let y partially order a nonempty set x such that 
every y-chain in x has an upper bound in x. By AC, there is a choice 
function f for x. Let b be any element of x. By transfinite induction 
(Proposition 4.14(a)), there is a function F such that F′∅ = b and, for 
any α >⚬ ∅, F′α is f′u, where u is the set of y-upper bounds v in x of 
F″α such that v ∉ F″α. Let β be the least ordinal such that the set of 
y-upper bounds in x of F″β that are not in F″β is empty. (There must 
be such an ordinal. Otherwise, F would be a one–one function with 
domain On and range a subset of x, which, by the replacement axiom 
R, would imply that On is a set.) Let ɡ = β   F. Then it is easy to check 
that g is one-one and, if α <⚬ γ <⚬ β, 〈ɡ′α, ɡ′γ 〉 ∈ y. Hence, ɡ″β is a 
y-chain in x; by hypothesis, there is a y-upper bound w of ɡ″β. Since 
the set of y-upper bounds of F″β(= g″β) that are not in g″β is empty, 
w ∈ ɡ″β and w is the only y-upper bound of g″β (because a set can 
contain at most one of its y-upper bounds). Hence, w is a y-maximal 
element. (If 〈w, z〉 ∈ y and z ∈ x, then z is a y-upper bound of ɡ″β, 
which is impossible.)
	
6.	⊢ Zorn ⇒ WO. Given a set z, let X be the class of all one–one func-
tions with domain an ordinal and range a subset of z. By Hartogs’ 
theorem, X is a set. Clearly, ∅ ∈ X. X is partially ordered by the 
proper inclusion relation ⊂. Given any chain of functions in X, of 
any two, one is an extension of the other. Hence, the union of all the 
functions in the chain is also a one–one function from an ordinal 
into z, which is a ⊂-upper bound of the chain. Hence, by Zorn, X has 
a maximal element g, which is a one–one function from an ordinal 



284
Introduction to Mathematical Logic
α into z. Assume z − ɡ″α ≠ ∅ and let b ∈ z − ɡ″α. Let f = ɡ ∪ {< α, β >}. 
Then f ∈ X and ɡ ⊂ f, contradicting the maximality of g. So, ɡ″α = z. 
Thus, α ≅
g z. By means of ɡ, we can transfer the well-ordering Eα of α 
to a well-ordering of z.
Exercises
4.73	 Show that each of the following is equivalent to the axiom of choice.
	
a.	 Any set x is equinumerous with some ordinal.
	
b.	 Special case of Zorn’s lemma. If x is a nonempty set and if the union 
of each nonempty ⊂ -chain in x is also in x, then x has a ⊂ -maximal 
element.
	
c.	 Hausdorff maximal principle. If x is a set, then every ⊂ -chain in x is a 
subset of some maximal ⊂ -chain in x.
	
d.	 Teichmüller–Tukey Lemma. Any set of finite character has a ⊂ -maxi-
mal element. (A nonempty set x is said to be of finite character if and 
only if: (i) every finite subset of an element of x is also an element of x; 
and (ii) if every finite subset of a set y is a member of x, then y ∈ x.)
	
e.	 (∀x)(Rel(x) ⇒ (∃y)(Fnc(y) ∧ D(x) = D(y) ∧ y ⊆ x))
	
f.	 For any nonempty sets x and y, either there is a function with 
domain x and range y or there is a function with domain y and 
range x.
4.74	 Show that the following finite axiom of choice is provable in NBG: if x 
is a finite set of nonempty disjoint sets, then there is a choice set y for x. 
[Hint: Assume x ≅ α where α ∈ ω. Use induction on α.]
Proposition 4.43
The following are consequences of the axiom of choice.
	
a.	Any infinite set has a denumerable subset.
	
b.	An infinite set is Dedekind-infinite.
	
c.	If x is a denumberable set whose elements are denumerable sets, 
then ⋃ x is denumerable.
Proof
Assume AC.
	
a.	Let x be an infinite set. By Exercise 4.73(a), x is equinumerous with 
some ordinal α. Since x is infinite, so is α. Hence, ω ≤o α; therefore, 
ω is equinumerous with some subset of x.



285
Axiomatic Set Theory
	
b.	The proof is by part (a) and Exercise 4.64(c).
	
c.	Assume x is a denumerable set of denumerable sets. Let f be a func-
tion assigning to each u in x the set of all one–one correspondences 
between u and ω. Let z be the union of the range of f. Then, by AC 
applied to z, there is a function ɡ such that ɡ′v ∈ v for each non-
empty v ⊆ z. In particular, if u ∈ X, then ɡ′(f′u) is a one–one cor-
respondence between u and ω. Let h be a one–one correspondence 
between ω and x. Define a function F on ⋃ x as follows: let y ∈ ⋃ x 
and let n be the smallest element of ω such that y ∈ h′n. Now, h′n ∈ x; 
so, ɡ′(f′(h′n)) is a one–one correspondence between h′n and ω. Define 
F′y = 〈n, (ɡ′(f′(h′n)))′y〉. Then F is a one–one function with domain ⋃ x 
and range a subset of ω × ω. Hence, ⋃ x ≤ ω × ω. But ω × ω ≅ ω and, 
therefore, ⋃ x ≤ ω. If v ∈ x, then v ⊆ ⋃ x and v ≅ ω. Hence, ω ≤  ⋃ x. 
By Bernstein’s theorem, ⋃ x ≅ ω.
Exercises
4.75	 If x is a set, the Cartesian product Πu∈xu is the set of functions f with 
domain x such that f′u ∈ u for all u ∈ x. Show that AC is equivalent to 
the proposition that the Cartesian product of any set x of nonempty sets 
is also nonempty.
4.76	 Show that AC implies that any partial ordering of a set x is included in 
a total ordering of x.
4.77	 Prove that the following is a consequence of AC: for any ordinal α, if x is 
a set such that x ≼ ωα and such that (∀u)(u ∈ x ⇒ u ≼ ωα), then ⋃ x ≤ ωα. 
[Hint: The proof is like that of Proposition 4.43(c).]
4.78	 a.	 Prove y ≼ x ⇒ (∃f)(Fnc(f) ∧D(f) = x ∧R(f) = y).
	
b.	 Prove that AC implies the converse of part (a).
4.79D	a.	 Prove (u +c v)2 ≅ u2 +c (2 × (u × v)) +c v2.
	
b.	 Assume y is a well-ordered set such that x × y ≅ x +c y and ¬(y ≼ x). 
Prove that x ≼ y.
	
c.	 Assume y ≅ y × y for all infinite sets y. Prove that, if Inf(x) and z = H  ′x, 
then x × z ≅ x +c z.
	
d.	 Prove that AC is equivalent to (∀y)(Inf(y) ⇒ y ≅ y × y) (Tarski, 1923).
A stronger form of the axiom of choice is the following sentence: (∃X)(Fnc(X) 
∧ (∀u)(u ≠ ∅ ⇒ X′u ∈ u)). (There is a universal choice function (UCF)—i.e., a 
function that assigns to every nonempty set u an element of u.) UCF obvi-
ously implies AC, but W.B. Easton proved in 1964 that UCF is not provable 
from AC if NBG is consistent. However, Felgner (1971b) proved that, for any 
sentence B in which all quantifiers are restricted to sets, if B is provable from 
NBG + (UCF), then B is provable in NBG + (AC). (See Felgner (1976) for a 
thorough treatment of the relations between UCF and AC.)



286
Introduction to Mathematical Logic
The theory of cardinal numbers can be simplified if we assume AC; for AC 
implies that every set is equinumerous with some ordinal and, therefore, 
that every set x is equinumerous with a unique initial ordinal, which can 
be designated as the cardinal number of x. Thus, the cardinal numbers would 
be identified with the initial ordinals. To conform with the standard nota-
tion for ordinals, we let ℵα stand for ωα. Proposition 4.40 and Corollary 4.41 
establish some of the basic properties of addition and multiplication of 
cardinal numbers.
The status of the axiom of choice has become less controversial in recent 
years. To most mathematicians it seems quite plausible, and it has so many 
important applications in practically all branches of mathematics that not to 
accept it would seem to be a willful hobbling of the practicing mathemati-
cian. We shall discuss its consistency and independence later in this section.
Another hypothesis that has been proposed as a basic principle of set the-
ory is the so-called regularity axiom (Reg):
	
(
)(
(
)(
))
∀
≠∅⇒∃
∈
∧
∩
= ∅
X X
y y
X
y
X
(Every nonempty class X contains a member that is disjoint from X.)
Proposition 4.44
	
a.	The regularity axiom implies the Fundierungsaxiom:
	
¬ ∃
(
)
( ) ∧
( ) =
∧∀
(
)
∈
⇒
′( )∈′
(
))
′
f
f
f
u
u
f
u
f u
Fnc
D
ω
ω
	
	 that is, there is no infinitely descending ∈-sequence x0 ∋ x1 ∋ x2 ∋…
	
b.	If we assume AC, then the Fundierungsaxiom implies the regularity 
axiom.
	
c.	The regularity axiom implies the nonexistence of finite ∈-cycles—
that is, of functions f on a nonzero finite ordinal α such that f′∅ ∈ f′1 
∈ … ∈ f′α ∈ f′∅. In particular, it implies that there is no set y such that 
y ∈ y.
Proof
	
a.	Assume Fnc(f) ∧D(f) = ω ∧ (∀u)(u ∈ ω ⇒ f′(u′) ∈ f′u). Let z = f″ω. By 
(Reg), there is some element y in z such that y ∩ z = ∅. Since y ∈ z, 
there is a finite ordinal α such that y = f′α. Then f′(α′) ∈ y ∩ z, contra-
dicting y ∩ z = ∅.
	
b.	First, we define the transitive closure TC(u) of a set u. Intuitively, we 
want TC(u) to be the smallest transitive set that contains u. Define by 
induction a function g on ω such that ɡ′∅ = {u} and ɡ′(α′) = ⋃ (ɡ′α) 



287
Axiomatic Set Theory
for each α in ω. Thus, ɡ′1 = u, ɡ′2 = ⋃ u, ɡ′3 = ⋃ (⋃ u), and so on. Let 
TC(u) = ⋃ (ɡ″ω) be called the transitive closure of u. For any u, TC(u) 
is transitive; that is, (∀v)(v ∈ TC(u) ⇒ v ⊆ TC(u)). Now, assume AC and 
the Fundierungsaxiom; also, assume X ≠ ∅ but there is no y in X 
such that y ∩ X = ∅. Let b be some element of X; hence, b ∩ X ≠ ∅. Let 
c = TC(b) ∩ X. By AC, let h be a choice function for c. Define a func-
tion f on ω such that f′∅ = b and, for any α in ω, f′(α′) = h′((f′α) ∩ X). 
It follows easily that, for each α in ω, f′(α′) ∈ f′α, contradicting the 
Fundierungsaxiom. (The proof can be summarized as follows: we 
start with an element b of X; then, using h, we pick an element f′1 in 
b ∩ X; since, by assumption, f′1 and X cannot be disjoint, we pick an 
element f′2 in f′1 ∩ X, and so on.)
	
c.	Assume given a finite ∈-cycle: f′∅ ∈ f′1 ∈ … ∈ f′n ∈ f′∅. Let X be the 
range of f:{f′∅, f′1, …, f′n}. By (Reg), there is some f′j in X such that f′j 
∩ X = ∅. But each element of X has an element in common with X.*
Exercises
4.80	 If z is a transitive set such that u ∈ z, prove that TC(u) ⊆ z.
4.81	 By the principle of dependent choices (PDC) we mean the following: if 
r is a nonempty relation whose range is a subset of its domain, then 
there is a function f: ω → D(r) such that (∀u)(u ∈ ω ⇒ 〈f′u, f′(u′)〉 ∈ r) 
(Mostowski, 1948).
	
a.	 Prove ⊢ AC ⇒ PDC.
	
b.	 Show that PDC implies the denumerable axiom of choice (DAC):
Den( )
(
)(
)
(
)(
:
(
)(
))
x
u u x
u
f
f
x
x
u u x
f u u
∧∀
∈⇒
≠∅⇒∃
→
∧∀
∈⇒′ ∈
∪
	
c.	 Prove ⊢ PDC ⇒ (∀x)(Inf(x) ⇒ ω ≼ x) (Hence, by Exercise 4.64(c), PDC 
implies that a set is infinite if and only if it is Dedekind-infinite.)
	
d.	 Prove that the conjunction of PDC and the Fundierungsaxiom 
implies (Reg).
Let us define by transfinite induction the following function Ψ with domain On:
	
Ψ
Ψ
Ψ
Ψ
Ψ
′∅= ∅
′(
) =
′
(
)
( ) ⇒
′
=
′
′
<
α
α
λ
λ
β
β
λ
P
Lim
o
∪
*	 The use of AC in deriving (Reg) from the Fundierungsaxiom is necessary. Mendelson (1958) 
proved that, if NBG is consistent and if we add the Fundierungsaxiom as an axiom, then 
(Reg) is not provable in this enlarged theory.



288
Introduction to Mathematical Logic
Let H stand for ∪ (Ψ″On), that is, H consists of all members of sets of the form 
Ψ′α. Let Hβ stand for Ψ′(β′). Thus, Hβ = P (Ψ′β) and Hβ′ = P (Ψ′(β′)) = P (Hβ). In 
particular, H∅ = P (Ψ′∅) = P (∅) = {∅}, H1 = P (H∅) = P ({∅}) = {∅, {∅}}, and H2 = P 
(H1) = P ({∅, {∅}}) = {∅, {∅}, {{∅}}, {∅, {∅}}}.
Define a function ρ on H such that, for any x in H, ρ′x is the least ordinal α 
such that x ∈ Ψ′α. ρ′x is called the rank of x. Observe that ρ′x must be a suc-
cessor ordinal. (In fact, there are no sets of rank ∅, since Ψ′∅ = ∅. If λ is a limit 
ordinal, every set in Ψ′λ already was a member of Ψ′β for some β <⚬ λ.) As 
examples, note that ρ′∅ = 1, ρ′{∅} = 1, ρ′{∅, {∅}} = 2, and ρ′{{∅}} = 2.
Exercise
4.82	 Prove that the following are theorems of NBG.
	
a.	 (∀α) Trans (Ψ′α)
	
b.	 Trans(H)
	
c.	 (∀α)(Ψ′α ⊆ Ψ′(α′))
	
d.	 (∀α)(∀β)(α <⚬ β ⇒ Ψ′α ⊆ Ψ′β)
	
e.	 On ⊆ H
	
f.	 (∀α)(ρ′α = α′)
	
g.	 (∀u)(∀v)(u ∈ H ∧ v ∈ H ∧ u ∈ v ⇒ ρ′u <⚬ ρ′v)
	
h.	 (∀u)(u ⊆ H ⇒ u ∈ H)
Proposition 4.45
The regularity axiom is equivalent to the assertion that V = H, that is, that 
every set is a member of H.
Proof
	
a.	Assume V = H. Let X ≠ ∅. Let α be the least of the ranks of all the 
members of X, and let b be an element of X such that ρ′b = α. Then b ∩ 
X = ∅; for, if u ∈ b ∩ X, then, by Exercise 4.82(g), ρ′u ∈ ρ′b = α, contra-
dicting the minimality of α.
	
b.	Assume (Reg). Assume V ≠ H. Then V − H ≠ ∅. By (Reg), there is 
some y in V − H such that y ∩ (V − H) = ∅. Hence, y ⊆ H and so, by 
Exercise 4.82(h), y ∈ H, contradicting y ∈ V − H.
Exercises
4.83	 Show that (Reg) is equivalent to the special case: (∀x)(x ≠ ∅ ⇒ (∃y)(y ∈ 
x ∧ y ∩ x = ∅)).



289
Axiomatic Set Theory
4.84	 Show that, if we assume (Reg), then Ord(X) is equivalent to Trans(X) ∧ 
E ConX, that is, to the wf
	
(
)(
)
(
)(
)(
)
∀
∈
⇒
⊆
∧∀
∀
∈
∧
∈
∧
≠
⇒
∈∨
∈
u u
X
u
X
u
v u
X
v
X
u
v
u
v
v
u
Thus, with the regularity axiom, a much simpler definition of the notion of 
ordinal class is available, a definition in which all quantifiers are restricted 
to sets.
4.85	 Show that (Reg) implies that every nonempty transitive class contains ∅
Proposition 4.45 certainly increases the attractiveness of adding (Reg) as 
a new axiom to NBG. The proposition V = H asserts that every set can be 
obtained by starting with ∅ and applying the power set and union oper-
ations any transfinite number of times. The assumption that this is so is 
called the iterative conception of set. Many set theorists now regard this con-
ception as the best available formalization of our intuitive picture of the 
universe of sets.*
By Exercise 4.84, the regularity axiom would also simplify the definition 
of ordinal numbers. In addition, we can develop the theory of cardinal num-
bers on the basis of the regularity axiom; namely, just define the cardinal 
number of a set x to be the set of all those y of lowest rank such that y ≅ x. 
This would satisfy the basic requirement of a theory of cardinal numbers, 
the existence of a function Card whose domain is V and such that (∀x)(∀y)
(Card′x = Card′y ⇔ x ≅ y).
There is no unanimity among mathematicians about whether we have suffi-
cient grounds for adding (Reg) as a new axiom, for, although it has great sim-
plifying power, it does not have the immediate plausibility that even the axiom 
of choice has, nor has it had any mathematical applications. Nevertheless, it is 
now often taken without explicit mention to be one of the axioms.
The class H determines an inner model of NBG in the following sense. For any 
wf B (written in unabbreviated notation), let RelH(B) be the wf obtained from 
B by replacing every subformula (∀X)C  (X) by (∀X)(X ⊆ H ⇒ C  (X)) (in mak-
ing the replacements we start with the innermost subformulas) and then, if B 
contains free variables. Y1, …, Yn, prefixing (Y1 ⊆ H ∧ Y2 ⊆ H ∧ … ∧ Yn ⊆ H) ⇒.
In other words, in forming RelH (B), we interpret “class” as “subclass of H.” 
Since M(X) stands for (∃Y)(X ∈ Y), RelH(M(X)) is (∃Y)(Y ⊆ H ∧ X ∈ Y), which 
is equivalent to X ∈ H; thus, the “sets” of the model are the elements of H. 
Hence, RelH ((∀x)B) is equivalent to (∀x)(x ∈ H ⇒ B#), where B# is RelH(B). 
Note also that ⊢ X ⊆ H ∧ Y ⊆ H ⇒ [RelH(X = Y) ⇔ X = Y]. Then it turns out 
that, for any theorem B of NBG, RelH (B) is also a theorem of NBG.
*	 The iterative conception seems to presuppose that we understand the power set and union 
operations and that ordinal numbers (or something essentially equivalent to them) are avail-
able for carrying out the transfinite iteration of the power set and union operations.



290
Introduction to Mathematical Logic
Exercises
4.86	 Verify that, for each axiom B of NBG, ⊢NBG RelH(B). If we adopt a 
semantic approach, one need only show that, if M is a model for NBG, 
in the usual sense of “model,” then the objects X of M that satisfy the wf 
X ⊆ H also form a model for NBG. In addition, one can verify that (Reg) 
holds in this model; this is essentially just part (a) of Proposition 4.45. 
A direct consequence of this fact is that, if NBG is consistent, then so is 
the theory obtained by adding (Reg) as a new axiom. That (Reg) is inde-
pendent of NBG (that is, cannot be proved in NBG) can be shown by 
means of a model that is somewhat more complex than the one given 
above for the consistency proof (see Bernays, 1937–1954, part VII). Thus, 
we can consistently add either (Reg) or its negation to NBG, if NBG is 
consistent. Practically the same arguments show the independence and 
consistency of (Reg) with respect to NBG + (AC).
4.87	 Consider the model whose domain is Hα and whose interpretation of 
∈ is EHα, the membership relation restricted to Hα. Notice that the “sets” 
of this model are the sets of rank ≤⚬ α and the “proper classes” are the sets 
of rank α′. Show that the model Hα satisfies all axioms of NBG (except 
possibly the axioms of infinity and replacement) if and only if Lim(α). 
Prove also that Hα satisfies the axiom of infinity if and only if α >⚬ ω.
4.88	 Show that the axiom of infinity is not provable from the other axioms 
of NBG, if the latter form a consistent theory.
4.89	 Show that the replacement axiom (R) is not provable from the other axi-
oms (T, P, N, (B1)–(B7), U, W, S) if these latter form a consistent theory.
4.90	 An ordinal α such that Hα is a model for NBG is called inaccessible. Since 
NBG has only a finite number of proper axioms, the assertion that α is 
inaccessible can be expressed by the conjunction of the relativization 
to Hα of the proper axioms of NBG. Show that the existence of inacces-
sible ordinals is not provable in NBG if NBG is consistent. (Compare 
Shepherdson (1951–1953), Montague and Vaught (1959), and, for 
related results, Bernays (1961) and Levy (1960).) Inaccessible ordinals 
have been shown to have connections with problems in measure theory 
and algebra (see Ulam, 1930; Zeeman, 1955; Erdös and Tarski, 1961).* 
The consistency of the theory obtained from NBG by adding an axiom 
asserting the existence of an inaccessible ordinal is still an open ques-
tion. More about inaccessible ordinals may be found in Exercise 4.91.
The axiom of choice turns out to be consistent and independent with 
respect to the theory NBG + (Reg). More precisely, if NBG is consistent, AC 
is an undecidable sentence of the theory NBG + (Reg). In fact, Gödel (1938, 
*	 Inaccessible ordinals are involved also with attempts to provide a suitable set-theoretic founda-
tion for category theory (see MacLane, 1971; Gabriel, 1962; Sonner, 1962; Kruse, 1966; Isbell, 1966).



291
Axiomatic Set Theory
1939, 1940) showed that, if NBG is consistent, then the theory NBG + (AC) + 
(Reg) + (GCH) is also consistent, where (GCH) stands for the generalized con-
tinuum hypothesis:
	
∀
(
)
( ) ⇒¬ ∃
(
)
∧
( )
(
)
(
)
x
x
y
x
y
y
x
Inf
≺
≺P
(Our statement of Gödel’s result is a bit redundant, since ⊢NBG (GCH) ⇒ 
(AC) has been proved by Sierpinski (1947) and Specker (1954). This result 
will be proved below.) The unprovability of AC from NBG + (Reg), if NBG is 
consistent, has been proved by P.J. Cohen (1963–1964), who also has shown 
the independence of the special continuum hypothesis, 2ω ≅ ω1, in the theory 
NBG + (AC) + (Reg). Expositions of the work of Cohen and its further devel-
opment can be found in Cohen (1966) and Shoenfield (1971b), as well as in 
Rosser (1969) and Felgner (1971a). For a thorough treatment of these results 
and other independence proofs in set theory, Jech (1978) and Kunen (1980) 
should be consulted.
We shall present here a modified form of the proof in Cohen (1966) of 
Sierpinski’s theorem that GCH implies AC.
Definition
For any set v, let P  0(v) = v, P  1(v) = P  (v), P  2(v) = P  (P (v)), …, P  k + 1(v) = P  (P  k(v)) 
for all k in ω.
Lemma 4.46
If ω ≼ v, then P  k(v) +c P  k(v) ≅ P  k(v) for all k ≥⚬ 1.
Proof
Remember that P  (x) ≅ 2x (see Exercise 4.40). From ω ≼ v we obtain ω ≼ P  k(v) 
for all k in ω. Hence, P  k(v) +c 1 ≅ P  k(v) for all k in ω, by Exercise 4.64(g). Now, 
for any k ≥⚬ 1,
	
P
P
P
P P
P
P
k
k
k
k
v
v
v
v
v
v
k
k
( )
( )
( )
(
( ))
( )
( )
+
=
×
=
×
≅
×
≅
×
≅
−
−
−
c
2
2
2
2
2
2
2
1
1
1
1
P
P
P P
P
k
k
v
v
k
k
v
v
−
−
+
−
≅
≅
=
1
1
1
1
2
( )
( )
(
( ))
( )
c
Lemma 4.47
If y +c x ≅ P  (x +c x), then P  (x) ≼ y.



292
Introduction to Mathematical Logic
Proof
Notice that P  (x + cx) ≅ 2x + 
c
x ≅ 2x × 2x ≅ P  (x) × P  (x). Let y* = y × {∅} and x* = 
x × {1}. Since y +c x ≅ P  (x +c x) ≅ P  (x) × P  (x), there is a function f such that 
y
x
x
x
f
∗
∗≅
×
∪
P
P
( )
( ). Let h be the function that takes each u in x* into the first 
component of the pair f′u. Thus, h: x* ⇒ P  (x). By Proposition 4.25(a), there 
must exist c in P  (x) − h″(x*). Then, for all z in P  (x), there exists a unique v in 
y* such that f′v = 〈c, z〉. This determines a one–one function from P  (x) into y. 
Hence, P  (x) ≼ y.
Proposition 4.48
Assume GCH.
	
a.	If u cannot be well-ordered and u +c u ≅ u and β is an ordinal such 
that β ≼ 2u, then β ≼ u.
	
b.	The axiom of choice holds.
Proof
	
a.	Notice that u +c u ≅ u implies 1 +c u ≅ u, by Exercise 4.71(b). Therefore, 
by Exercise 4.55(i), 2u +c u ≅ 2u. Now, u ≼ β +c u ≅ 2u. By GCH, either 
(i) u ≅ β +c u or (ii) β +c u ≅ 2u. If (ii) holds, β +c u ≅ 2u +c u ≅ P(u +c u). 
Hence, by Lemma 4.47, P(u) ≼ β and, therefore, u ≼ β. Then, since 
u would be equinumerous with a subset of an ordinal, u could be 
well-ordered, contradicting our assumption. Hence, (i) must hold. 
But then, β ≼ β +c u ≅ u.
	
b.	We shall prove AC by proving the equivalent sentence asserting that 
every set can be well-ordered (WO). To that end, consider any set 
x and assume, for the sake of contradiction, that x cannot be well-
ordered. Let v = 2x∪ω. Then ω ≼ x ∪ ω ≼ v. Hence, by Lemma 4.46, 
P  k(v) +c P  k(v) ≅ P  k(v) for all k ≥⚬ 1. Also, since x ≼ x ∪ ω ≼ v ≺ P  (v) ≺ 
P (P (v)) ≺…, and x cannot be well-ordered, each P k(v) cannot be well-
ordered, for k ≥⚬ 0. Let β = H  ′v. We know that β ≼ P  4(v) by Corollary 
4.32. Hence, by part (a), with u = P  3(v), we obtain β ≼ P  3(v). Using 
part (a) twice more (successively with u = P  2(v) and u = P (v)), we 
obtain H ′v = β ≼ v. But this contradicts the definition of H ′v as the 
least ordinal not equinumerous with a subset of v.
Exercise
4.91	 An α-sequence is defined to be a function f whose domain is α. If the 
range of f consists of ordinals, then f is called an ordinal α-sequence and, 
if, in addition, β <o γ <⚬ α implies f′β <⚬ f′γ, then f is called an increasing 



293
Axiomatic Set Theory
ordinal α-sequence. By Proposition 4.12, if f is an increasing ordinal 
α-sequence, then ⋃ (f″α) is the least upper bound of the range of f. An 
ordinal δ is said to be regular if, for any increasing ordinal α-sequence 
such that α <⚬ δ and the ordinals in the range of f are all <⚬ δ, ∪ (f″α) + o1<oδ. 
Nonregular ordinals are called singular ordinals.
	
a.	 Which finite ordinals are regular?
	
b.	 Show that ω0 is regular and ωω is singular
	
c.	 Prove that every regular ordinal is an initial ordinal.
	
d.	 Assuming the AC, prove that every ordinal of the form ωγ+° 1 is regular.
	
e.	 If ωα is regular and Lim(α), prove that ωα = α. (A regular ordinal ωα 
such that Lim(α) is called a weakly inaccessible ordinal.)
	
f.	 Show that, if ωα has the property that γ <⚬ ωα implies P(γ) ≺ ωα, then 
Lim(α). The converse is implied by the generalized continuum 
hypothesis. A regular ordinal ωα such that α >⚬ ∅ and such that 
γ <⚬ ωα implies P(γ) ≺ ωα, is called strongly inaccessible. Thus, every 
strongly inaccessible ordinal is weakly inaccessible and, if (GCH) 
holds, the strongly inaccessible ordinals coincide with the weakly 
inaccessible ordinals.
	
g.	 (i) If γ is inaccessible (i.e., if Hγ is a model of NBG), prove that γ is 
weakly inaccessible. (ii)D In the theory NBG + (AC), show that γ is 
inaccessible if and only if γ is strongly inaccessible (Sheperdson, 
1951–1953; Montague and Vaught, 1959).
	
h.	 If NBG is consistent, then in the theory NBG + (AC) + (GCH), show 
that it is impossible to prove the existence of weakly inaccessible 
ordinals.
4.6  Other Axiomatizations of Set Theory
We have chosen to develop set theory on the basis of NBG because it is rela-
tively simple and convenient for the practicing mathematician. There are, of 
course, many other varieties of axiomatic set theory, of which we will now 
make a brief survey.
4.6.1  Morse–Kelley (MK)
Strengthening NBG, we can replace axioms (B1)–(B7) by the axiom schema:
	

( )
∃
∀
∈
⇔
(
)(
)(
)
( )
Y
x x
Y
x s
B
where
B(x) is any wf (not necessarily predicative) of NBG
 Y is not free in B(x)



294
Introduction to Mathematical Logic
The new theory MK, called Morse–Kelley set theory, became well-known 
through its appearance as an appendix in a book on general topology by 
Kelley (1955). The basic idea was proposed independently by Mostowski, 
Quine, and Morse (whose rather unorthodox system may be found in Morse 
(1965)). Axioms (B1)–(B7) follow easily from (□) and, therefore, NBG is a 
subtheory of MK. Mostowski (1951a) showed that, if NBG is consistent, then 
MK is really stronger than NBG. He did this by constructing a “truth defi-
nition” in MK on the basis of which he proved ⊢MK ConNBG, where ConNBG is a 
standard arithmetic sentence asserting the consistency of NBG. On the other 
hand, by Gödel’s second theorem, ConNBG is not provable in NBG if the latter 
is consistent.
The simplicity and power of schema (□) make MK very suitable for use 
by mathematicians who are not interested in the subtleties of axiomatic set 
theory. But this very strength makes the consistency of MK a riskier gamble. 
However, if we add to NBG + (AC) the axiom (In) asserting the existence 
of a strongly inaccessible ordinal θ, then Hθ is a model of MK. Hence, MK 
involves no more risk than NBG + (AC) + (In).
There are several textbooks that develop axiomatic set theory on the basis 
of MK (Rubin, 1967; Monk, 1980; Chuquai, 1981). Some of Cohen’s indepen-
dence results have been extended to MK by Chuquai (1972).
Exercises
4.92	 Prove that axioms (B1)–(B7) are theorems of MK.
4.93	 Verify that, if θ is a strongly inaccessible ordinal, then Hθ is a model 
of MK.
4.6.2  Zermelo–Fraenkel (ZF)
The earliest axiom system for set theory was devised by Zermelo (1908). The 
objects of the theory are thought of intuitively as sets, not the classes of NBG 
or MK. Zermelo’s theory Z can be formulated in a language that contains 
only one predicate letter ∈. Equality is defined extensionally: x = y stands for 
(∀z)(z ∈ x ⇔ z ∈ y). The proper axioms are:
T: x = y ⇒ (x ∈ z ⇔ y ∈ z)	
(substitutivity of =)
P: (∃z)(∀u)(u  ∈ z  ⇔ u = x ∨ u = y)	
(pairing)
N: (∃x)(∀y)(y ∉ x)	
(null set)
U: (∃y)(∀u)(u ∈ y ⇔ (∃v)(u ∈ v ∧ v ∈ x))	
(sum set)
W: (∃y)(∀u)(u ∈ y ⇔ u ⊆ x)	
(power set)
S*: (∃y)(∀u)(u ∈ y ⇔ (u ∈ x ∧ B(u))), 	
(selection)
where B(u) is any wf not containing y free
I: (∃x)(∅ ∈ x ∧ (∀z)(z ∈ x ⇒ z ∪ {z} ∈ x))	
(infinity)
Here we have assumed the same definitions of ⊆, ∅, ∪ and {u} as in NBG.



295
Axiomatic Set Theory
Zermelo’s intention was to build up mathematics by starting with a few 
simple sets (∅ and ω) and then constructing further sets by various well-
defined operations (such as formation of pairs, unions and power sets). In 
fact, a good deal of mathematics can be built up within Z. However, Fraenkel 
(1922a) observed that Z was too weak for a full development of mathemat-
ics. For example, for each finite ordinal n, the ordinal ω +⚬ n can be shown to 
exist, but the set A of all such ordinals cannot be proved to exist, and, there-
fore, ω +⚬ ω, the least upper bound of A, cannot be shown to exist. Fraenkel 
proposed a way of overcoming such difficulties, but his idea could not be 
clearly expressed in the language of Z. However, Skolem (1923) was able to 
recast Fraenkel’s idea in the following way: for any wf B(x, y), let Fun(B) 
stand for (∀x)(∀u)(∀v)(B(x, u) ∧ B(x, v) ⇒ u = v). Thus, Fun (B) asserts that B 
determines a function. Skolem’s axiom schema of replacement can then be for-
mulated as follows:
	
(
)
(
)(
)(
)(
(
)(
( , )))
( ,
R
w
z
v v
z
u u
w
u v
x y
#
Fun(
)
for any wf
B
B
B
⇒∀
∃
∀
∈
⇔∃
∈
∧
)
This is the best approximation that can be found for the replacement axiom 
R of NBG.
The system Z + (R#) is denoted ZF and is called Zermelo–Fraenkel set the-
ory. In recent years, ZF is often assumed to contain a set-theoretic regularity 
axiom (Reg*): x ≠ ∅ ⇒ (∃y)(y ∈ x ∧ y ∩ x = ∅). The reader should always check 
to see whether (Reg*) is included within ZF. ZF is now the most popular 
form of axiomatic set theory; most of the modern research in set theory on 
independence and consistency proofs has been carried out with respect to 
ZF. For expositions of ZF, see Krivine (1971), Suppes (1960), Zuckerman (1974), 
Lévy (1978), and Hrbacek and Jech (1978).
ZF and NBG yield essentially equivalent developments of set theory. Every 
sentence of ZF is an abbreviation of a sentence of NBG since, in NBG, lower-
case variables x, y, z, … serve as restricted set variables. Thus axiom N is an 
abbreviation of (∃x)(M(x) ∧ (∀y)(M(y) ⇒ y ∉ x)) in NBG. It is a simple mat-
ter to verify that all axioms of ZF are theorems in NBG. Indeed, NBG was 
originally constructed so that this would be the case. We can conclude that, 
if NBG is consistent, then so is ZF. In fact, if a contradiction could be derived 
in ZF, the same proof would yield a contradiction in NBG.
The presence of class variables in NBG seems to make it much more pow-
erful than ZF. At any rate, it is possible to express propositions in NBG that 
either are impossible to formulate in ZF (such as the universal choice axiom) 
or are much more unwieldy in ZF (such as transfinite induction theorems). 
Nevertheless, it is a surprising fact that NBG is no riskier than ZF. An even 
stronger result can be proved: NBG is a conservative extension of ZF in the 
sense that, for any sentence B of the language of ZF, if ⊢NBG B, then ⊢ZF B (see 
Novak (Gal) 1951; Rosser and Wang, 1950; Shoenfield, 1954). This implies that, 



296
Introduction to Mathematical Logic
if ZF is consistent, then NBG is consistent. Thus, NBG is consistent if and only 
if ZF is consistent, and NBG seems to be no stronger than ZF. However, NBG 
and ZF do differ with respect to the existence of certain kinds of models (see 
Montague and Vaught, 1959). Moreover, another important difference is that 
NBG is finitely axiomatizable, whereas Montague (1961a) showed that ZF (as 
well as Z) is not finitely axiomatizable. Montague (1961b) proved the stronger 
result that ZF cannot be obtained by adding a finite number of axioms to Z.
Exercise
4.94	 Let H
H
α
α
* = ∪
 (see page 288).
	
a.	 Verify that Hα* consists of all sets of rank less than α.
	
b.	 If α is a limit ordinal >⚬ ω, show that Hα* is a model for Z.
	
c.D	 Find an instance of the axiom schema of replacement (R#) that is 
false in Hω
ω
+°
*
. [Hint: Let B(x, y) be x ∈ ω ∧ y = ω +⚬ x. Observe that 
ω
ω
ω
ω
+
∉
°
+°
H*
 and ω +⚬ ω = ⋃ {v|(∃u)(u ∈ ω ∧ B(u, v))}.]
	
d.	 Show that, if ZF is consistent, then ZF is a proper extension of Z.
4.6.3  The Theory of Types (ST)
Russell’s paradox is based on the set K of all those sets that are not members 
of themselves: K = {x|x ∉ x}. Clearly, K ∈ K if and only if K ∉ K. In NBG this 
argument simply shows that K is a proper class, not a set. In ZF the conclu-
sion is just that there is no such set K.
Russell himself chose to find the source of his paradox elsewhere. He 
maintained that x ∈ x and x ∉ x should be considered “illegitimate” and 
“ungrammatical” formulas and, therefore, that the definition of K makes no 
sense. However, this alone is not adequate because paradoxes analogous to 
Russell’s can be obtained from slightly more complicated circular properties, 
like x ∈ y ∧ y ∈ x.
Exercise
4.95	 a.	 Derive a Russell-style paradox by using x ∈ y ∧ y ∈ x.
	
b.	 Use x ∈ y1 ∧ y1 ∈ y2 ∧ … ∧ yn−1 ∈ yn ∧ yn ∈ x to obtain a paradox, 
where n ≥ 1.
Thus, to avoid paradoxes, one must forbid any kind of indirect circularity. 
For this purpose, we can think of the universe divided up into types in the 
following way. Start with a collection W of nonsets or individuals. The ele-
ments of W are said to have type 0. Sets whose members are of type 0 are 
the objects of type 1. Sets whose members are of type1 will be the objects of 
type 2, and so on.



297
Axiomatic Set Theory
Our language will have variables of different types. The superscript of a 
variable will indicate its type. Thus, x0 is a variable of type 0, y1 is a variable 
of type 1, and so on. There are no variables other than type variables. The 
atomic wfs are of the form xn ∈ yn+1, where n is one of the natural numbers 
0, 1, 2, … . The rest of the wfs are built up from the atomic wfs by means of 
logical connectives and quantifiers. Observe that ¬(x ∈ x) and ¬(x ∈ y ∧ y ∈ x) 
are not wfs.
The equality relation must be defined piecemeal, one definition for each type.
Definition
	
x
y
z
x
z
y
z
n
n
n
n
n
n
n
=
∀
∈
⇔
∈
+
+
+
for
(
)(
)
1
1
1
Notice that two objects are defined to be equal if they belong to the same 
sets of the next higher type. The basic property of equality is provided by the 
following axiom scheme.
4.6.3.1  ST1 (Extensionality Axiom)
	
(
)(
)
∀
∈
⇔
∈
⇒
=
+
+
+
+
x
x
y
x
z
y
z
n
n
n
n
n
n
n
1
1
1
1
This asserts that two sets that have the same members must be equal. On the 
other hand, observe that the property of having the same members could 
not be taken as a general definition of equality because it is not suitable for 
objects of type 0.
Given any wf B(xn), we wish to be able to define a set {xn|B(xn)}.
4.6.3.2  ST2 (Comprehension Axiom Scheme)
For any wf B(xn), the following wf is an axiom:
	
∃(
) ∀
(
)
∈
⇔
(
)
(
)
+
+
y
x
x
y
x
n
n
n
n
n
1
1
B
Here, yn+1 is any variable not free in B(xn). If we use the extensionality axiom, 
then the set yn+1 asserted to exist by axiom ST2 is unique and can be denoted 
by {xn|B(xn)}.
Within this system, we can define the usual set-theoretic notions and 
operations, as well as the natural numbers, ordinal numbers, cardinal num-
bers and so on. However, these concepts are not unique but are repeated 
for each type (or, in some cases, for all but the first few types). For example, 
the comprehension scheme provides a null set Λn+1 = {xn|xn ≠ xn} for each 



298
Introduction to Mathematical Logic
nonzero type. But there is no null set per se. The same thing happens for 
natural numbers. In type theory, the natural numbers are not defined as they 
are in NBG. Here they are the finite cardinal numbers. For example, the set 
of natural numbers of type 2 is the intersection of all sets containing {Λ1} and 
closed under the following successor operation: the successor S(y2) of a set 
y2 is {v1|(∃u1)(∃z0)(u1 ∈ y2 ∧ z0 ∉ u1 ∧ v1 = u1 ∪ {z0})}. Then, among the natural 
numbers of type 2, we have 0 = {Λ1}, 1 = S(0), 2 = S(1), and so on. Here, the 
numerals 0, 1, 2, … should really have a superscript “2” to indicate their type, 
but the superscripts were omitted for the sake of legibility. Note that 0 is the 
set of all sets of type 1 that contain no elements, 1 is the set of all sets of type 1 
that contain one element, 2 is the set of all sets of type 1 that contain two ele-
ments, and so on.
This repetition of the same notion in different types makes it somewhat 
inconvenient for mathematicians to work within a type theory. Moreover, 
it is easy to show that the existence of an infinite set cannot be proved from 
the extensionality and comprehension schemas.* To see this, consider the 
“model” in which each variable of type n ranges over the sets of rank less 
than or equal to n +⚬ 1. (There is nothing wrong about assigning overlapping 
ranges to variables of different types.)
We shall assume an axiom that guarantees the existence of an infinite 
set. As a preliminary, we shall adopt the usual definition {{xn}, {xn, yn}} of the 
ordered pair: 〈xn, yn〉, where {xn, yn} stands for {un|un = xn ∨ un = yn}. Notice 
that 〈xn, yn〉 is of type n + 2. Hence, a binary relation on a set A, being a set of 
ordered pairs of elements of A, will have type 2 greater than the type of A. In 
particular, a binary relation on the universe V1 = {x0|x0 = x0} of all objects of 
type 0 will be a set of type 3.
4.6.3.3  ST3 (Axiom of Infinity)
	
(
)([(
)(
)(
,
)]
(
)(
)(
)(
,
∃
∃
∃
〈
〉∈
∧
∀
∀
∀
〈
〉∉
∧
x
u
v
u
v
x
u
v
w
u
u
x
3
0
0
0
0
3
0
0
0
0
0
3
[
,
,
,
]
[
,
(
)(
,
〈
〉∈
∧〈
〉∈
⇒
〈
〉∈
∧〈
〉∈
⇒∃
〈
u
v
x
v
w
x
u
w
x
u
v
x
z
v
0
0
3
0
0
3
0
0
3
0
0
3
0
0 z
x
0
3
〉∈
)]))
This asserts that there is a nonempty irreflexive, transitive binary relation x3 
on V1 such that every member of the range of x3 also belongs to the domain 
of x3. Since no such relation exists on a finite set, V1 must be infinite.
The system based on ST1–ST3 is called the simple theory of types and is 
denoted ST. Because of its somewhat complex notation and the repetition 
of concepts at all (or, in some cases, almost all) type levels, ST is not gen-
erally used as a foundation of mathematics and is not the subject of much 
*	 This fact seemed to undermine Russell’s doctrine of logicism, according to which all of math-
ematics could be reduced to basic axioms that were of an essentially logical character. An 
axiom of infinity could not be thought of as a logical truth.



299
Axiomatic Set Theory
contemporary research. Suggestions by Turing (1948) to make type theory 
more usable have been largely ignored.
With ST we can associate a first-order theory ST*. The nonlogical constants 
of ST* are ∈ and monadic predicates Tn for each natural number n. We then 
translate any wf B of ST into ST* by replacing subformulas (∀xn)C (xn) by (∀x)
(Tn(x) ⇒ C  (x)) and, finally, if y
y
j
jk
1,
,
…
 are the free variables of B, prefixing 
to the result T
y
T
y
j
j
k
k
1
1
(
)
(
)
∧…∧
⇒ and changing each y j1 into yi. In a rigor-
ous presentation, we would have to specify clearly that the replacements are 
made by proceeding from smaller to larger subformulas and that the vari-
ables x, y1, …, yk are new variables. The axioms of ST* are the translations of 
the axioms of ST. Any theorem of ST translates into a theorem of ST*.
Exercise
4.96	 Exhibit a model of ST* within NBG.
By virtue of Exercise 4.96, NBG (or ZF) is stronger than ST: (1) any theorem 
of ST can be translated into a corresponding theorem of NBG, and (2) if NBG 
is consistent, so is ST.*
To provide a type theory that is easier to work with, one can add axi-
oms that impose additional structure on the set V1 of objects of type 0. For 
example, Peano’s axioms for the natural numbers were adopted at level 0 in 
Gödel’s system P, for which he originally proved his famous incompleteness 
theorem (see Gödel, 1931).
In Principia Mathematica (1910–1913), the three-volume work by Alfred 
North Whitehead and Bertrand Russell, there is a theory of types that is 
further complicated by an additional hierarchy of orders. This hierarchy was 
introduced so that the comprehension scheme could be suitably restricted 
in order not to generate an impredicatively defined set, that is, a set A defined 
by a formula in which some quantified variable ranges over a set that turns 
out to contain the set A itself. Along with the mathematician Henri Poincaré, 
Whitehead and Russell believed impredicatively defined sets to be the root 
of all evil. However, such concepts are required in analysis (e.g., in the proof 
that any nonempty set of real numbers that is bounded above has a least 
upper bound). Principia Mathematica had to add the so-called axiom of reduc-
ibility to overcome the order restrictions imposed on the comprehension 
scheme. The Whitehead–Russell system without the axiom of reducibility is 
called ramified type theory; it is mathematically weak but is of interest to those 
who wish an extreme constructivist approach to mathematics. The axiom 
of reducibility vitiates the effect of the order hierarchy; therefore, it is much 
simpler to drop the notion of order and the axiom of reducibility. The result 
is the simple theory of types ST, which we have described above.
*	 A stronger result was proved by John Kemeny (1949) by means of a truth definition within Z: 
if Z is consistent, so is ST.



300
Introduction to Mathematical Logic
In ST, the types are natural numbers. For a smoother presentation, some 
logicians allow a larger set of types, including types for relations and/or 
functions defined on objects taken from previously defined types. Such a 
system may be found in Church (1940).
Principia Mathematica must be read critically; for example, it often overlooks 
the distinction between a formal theory and its metalanguage. The idea of 
a simple theory of types goes back to Ramsey (1925) and, independently, 
to Chwistek (1924–1925). Discussions of type theory are found in Andrews 
(1986), Hatcher (1982) and Quine (1963).
4.6.4  Quine’s Theories NF and ML
Quine (1937) invented a type theory that was designed to do away with some 
of the unpleasant aspects of type theory while keeping the essential idea of the 
comprehension axiom ST2. Quine’s theory NF (New Foundations) uses only one 
kind of variable x, y, z, … and one binary predicate letter ∈. Equality is defined 
as in type theory: x = y stands for (∀z)(x ∈ z ⇔ y ∈ z). The first axiom is familiar:
4.6.4.1  NF1 (Extensionality)
	
(
)(
)
∀
∈
⇔
∈
⇒
=
z z
x
z
y
x
y
In order to formulate the comprehension axiom, we introduce the notion 
of stratification. A wf B is said to be stratified if one can assign integers to 
the variables of B so that: (1) all occurrences of the same free variable are 
assigned the same integer, (2) all bound occurrences of a variable that are 
bound by the same quantifier must be assigned the same integer, and (3) for 
every subformula x ∈ y of B, the integer assigned to y is 1 greater than the 
integer assigned to x.
Examples
	
1.	(∃y)(x ∈ y ∧ y ∈ z) ∨ u ∈ x is stratified by virtue of the assignment 
indicated below by superscripts:
	
(
)(
)
∃
∈
∧
∈
∨
∈
y
x
y
y
z
u
x
2
1
2
2
3
0
1
	
2.	((∃y)(x ∈ y)) ∧ (∃y)(y ∈ x) is stratified as follows:
	
((
)(
))
(
)(
)
∃
∈
∧∃
∈
y
x
y
y
y
x
2
1
2
0
0
1
	
	 Notice that the ys in the second conjunct do not have to have the 
same integers assigned to them as the ys in the first conjunct.



301
Axiomatic Set Theory
	
3.	x ∈ y ∨ y ∈ x is not stratified. If x is assigned an integer n, then the 
first y must be assigned n + 1 and the second y must be assigned 
n − 1, contradicting requirement (1).
4.6.4.2  NF2 (Comprehension)
For any stratified wf B(x),
	
∃
(
) ∀
(
)
∈
⇔
( )
(
)
y
x
x
y
x
B
is an axiom. (Here, y is assumed to be the first variable not free in B(x).)
Although NF2 is an axiom scheme, it turns out that NF is finitely axiomat-
izable (Hailperin, 1944).
Exercise
4.97	 Prove that equality could have been defined as follows: x = y for (∀z)(x 
∈ z ⇒ y ∈ z). (More precisely, in the presence of NF2, this definition is 
equivalent to the original one.)
The theory of natural numbers, ordinal numbers and cardinal numbers 
is developed in much the same way as in type theory, except that there is 
no longer a multiplicity of similar concepts. There is a unique empty set Λ = 
{x|x ≠ x} and a unique universal set V = {x|x = x}. We can easily prove V ∈ V, 
which immediately distinguishes NF from type theory (and from NBG, MK 
and ZF).
The usual argument for Russell’s paradox does not hold in NF, since 
x ∉ x is not stratified. Almost all of standard set theory and mathematics 
is derivable in NF; this is done in full detail in Rosser (1953). However, NF 
has some very strange properties. First of all, the usual proof of Cantor’s 
theorem, A ≺ P (A), does not go through in NF; at a key step in the proof, 
a set that is needed is not available because its defining condition is not 
stratified. The apparent unavailability of Cantor’s theorem has the desir-
able effect of undermining the usual proof of Cantor’s paradox. If we could 
prove A ≺ P (A), then, since P (V) = V, we could obtain a contradiction 
from V ≺ P (V). In NF, the standard proof of Cantor’s theorem does yield 
USC(A) ≺ P (A), where USC(A) stands for {x|(∃u)(u ∈ A ∧ x = {u})}. If we let 
A = V, we conclude that USC(V) ≺ V. Thus, V has the peculiar property that 
it is not equinumerous with the set of all unit sets of its elements. In NBG, 
the function f, defined by f(u) = {u} for all u in A, establishes a one–one cor-
respondence between A and USC(A) for any set A. However, the defining 
condition for f is not stratified, so that f may not exist in NF. If f does exist, 
A is said to be strongly Cantorian.



302
Introduction to Mathematical Logic
Other surprising properties of NF are the following.
	
1.	The axiom of choice is disprovable in NF (Specker, 1953).
	
2.	Any model for NF must be nonstandard in the sense that a well-
ordering of the finite cardinals or of the ordinals of the model is not 
possible in the metalanguage (Rosser and Wang, 1950).
	
3.	The axiom of infinity is provable in NF (Specker, 1953).
Although property 3 would ordinarily be thought of as a great advantage, 
the fact of the provability of an axiom of infinity appeared to many logicians 
to be too strong a result. If that can be proved, then probably anything can be 
proved, that is, NF is likely to be inconsistent. In addition, the disprovability 
of the axiom of choice seems to make NF a poor choice for practicing math-
ematicians. However, if we restrict attention to so-called Cantorian sets, sets 
A for which A and USC(A) are equinumerous, then it might be consistent to 
assume the axiom of choice for Cantorian sets and to do mathematics within 
the universe of Cantorian sets.
NF has another attractive feature. A substantial part of category theory (see 
MacLane, 1971) can be developed in a straightforward way in NF, whereas 
this is not possible in ZF, NBG, or MK. Since category theory has become an 
important branch of mathematics, this is a distinct advantage for NF.
If the system obtained from NF by assuming the existence of an inac-
cessible ordinal is consistent, then ZF is consistent (see Collins, 1955; Orey, 
1956a). If we add to NF the assumption of the existence of an infinite strongly 
Cantorian set, then Zermelo’s set theory Z is consistent (see Rosser, 1954). The 
question of whether the consistency of ZF implies the consistency of NF is 
still open (as is the question of the reverse implication).
Let ST− be the simple theory of types ST without the axiom of infinity. 
Given any closed wf B of ST, let B+ denote the result of adding 1 to the types 
of all variables in B. Let SP denote the theory obtained from ST− by adding as 
axioms the wfs B ⇔ B+ for all closed wfs B. Specker (1958, 1962) proved that 
NF is consistent if and only if SP is consistent.
Let NFU denote the theory obtained from NF by restricting the extension-
ality axiom to nonempty sets:
	
NF *
1
(
)(
)
(
)(
)
∃
∈
∧∀
∈
⇔
∈
⇒
=
u u
x
z z
x
z
y
x
y
Jensen (1968–1969) proved that NFU is consistent if and only if ST− is con-
sistent, and the equiconsistency continues to hold when both theories are 
supplemented by the axiom of infinity or by axioms of infinity and choice.
Discussions of NF may be found in Hatcher (1982) and Quine (1963). Forster 
(1983) gives a survey of more recent results.
Quine also proposed a system ML that is formally related to NF in much 
the same way that MK is related to ZF. The variables are capital italic letters 



303
Axiomatic Set Theory
X, Y, Z, …; these variables are called class variables. We define M(X), X is a 
set,* by (∃Y)(X ∈ Y), and we introduce lower-case italic letters x, y, z, … as 
variables restricted to sets. Equality is defined as in NBG: X = Y for (∀Z)(Z ∈ 
X ⇔ Z ∈ Y). Then we introduce an axiom of equality:
	
ML1:
X
Y
X
Z
Y
Z
=
∧
∈
⇒
∈
There is an unrestricted comprehension axiom scheme:
	
ML2 :
(
)(
)(
( ))
∃
∀
∈
⇔
Y
x x
Y
x
B
where B(x) is any wf of ML. Finally, we wish to introduce an axiom that has 
the same effect as the comprehension axiom scheme NF2:
	
ML3
1
:
(
)(
)(
)(
( ))
(
)
∀
… ∀
∃
∀
∈
⇔
y
y
z
x x
z
x
n
B
where B(x) is any stratified wf whose free variables are x, y1, …, yn(n ≥ 0) and 
whose quantifiers are set quantifiers.
All theorems of NF are provable in ML. Hence, if ML is consistent, so is NF. 
The converse has been proved by Wang (1950). In fact, any closed wf of NF 
provable in ML is already provable in NF.
ML has the same advantages over NF that MK and NBG have over ZF: a 
greater ease and power of expression. Moreover, the natural numbers of ML 
behave much better than those of NF; the principle of mathematical induc-
tion can be proved in full generality in ML.
The prime source for ML is Quine (1951).† Consult also Quine (1963) and 
Fraenkel et al. (1973).
4.6.5  Set Theory with Urelements
The theories NBG, MK, ZF, NF, and ML do not allow for objects that are 
not sets or classes. This is all well and good for mathematicians, since only 
sets or classes seem to be needed for dealing with mathematical concepts 
and problems. However, if set theory is to be a part of a more inclusive 
theory having to do with the natural or social sciences, we must permit 
reference to things like electrons, molecules, people, companies, etc., and to 
sets and classes that contain such things. Things that are not sets or classes 
are sometimes called urelements.‡ We shall sketch a theory UR similar to 
*	 Quine uses the word “element” instead of “set.”
†	 Quine’s earlier version of ML, published in 1940, was proved inconsistent by Rosser (1942). 
The present version is due to Wang (1950).
‡	 “Ur” is a German prefix meaning primitive, original or earliest. The words “individual” and 
“atom” are sometimes used as synonyms for “urelement.”



304
Introduction to Mathematical Logic
NBG that allows for the existence of urelements.* Like NBG, UR will have a 
finite number of axioms.
The variables of UR will be the lower-case Latin boldface letters x1, x2, … . 
(As usual, let us use x, y, z, … to refer to arbitrary variables.) In addition to 
the binary predicate letter A2
2 there will be a monadic predicate letter A1
1. We 
abbreviate A2
2( , )
x y  by x
y
x y
∈
¬
,
( , )
A2
2
 by x ∉ y, and A1
1( )
x  by Cls (x). (Read 
“Cls(x)” as “x is a class.”) To bring our notation into line with that of NBG, 
we shall use capital Latin letters as restricted variables for classes. Thus, 
(∀X)B(X) stands for (∀x)(Cls(x) ⇒ B(x)), and (∃X)B(X) stands for (∃x)(Cls(x) ∧ 
B(x)). Let M(x) stand for Cls(x) ∧ (∃y (x ∈ y), and read “M(x)” as “x is a set.” 
As in NBG, use lower-case Latin letters as restricted variables for sets. Thus, 
(∀x)B(x) stands for (∀x)(M(x) ⇒ B(x)), and (∃x)B(x) stands for (∃x)(M(x) ∧ B(x)). 
Let Pr(x) stand for Cls(x) ∧ ¬M(x), and read “Pr(x)” as “x is a proper class.” 
Introduce Ur(x) as an abbreviation for ¬Cls(x), and read “Ur(x)” as “x is an 
urelement.” Thus, the domain of any model for UR will be divided into two 
disjoint parts consisting of the classes and the urelements, and the classes 
are divided into sets and proper classes. Let El(x) stand for M(x) ∨ Ur(x), and 
read “El(x)” as “x is an element.” In our intended interpretation, sets and ure-
lements are the objects that are elements (i.e., members) of classes.
Exercise
4.98	 Prove: ⊢UR (∀x)(El(x) ⇔ ¬Pr(x)).
We shall define equality in a different way for classes and urelements.
Definition
x = y is an abbreviation for:
	 [
( )
( )
(
)(
)]
[
( )
( )
(
)(
)]
Cls
Cls
Ur
Ur
x
y
z z
x
z
y
x
y
z x
z
y
z
∧
∧∀
∈
⇔
∈
∨
∧
∧∀
∈
⇔
∈
Exercise
4.99	 Prove: ⊢UR(∀x)(x = x).
Axiom UR1
	
(
)(
( )
(
)(
)]
∀
⇒∀
∉
x
x
y y
x
Ur
Thus, urelements have no members.
*	 Zermelo’s 1908 axiomatization permitted urelements. Fraenkel was among the first to draw 
attention to the fact that urelements are not necessary for mathematical purposes (see 
Fraenkel, 1928, pp. 355f). Von Neumann’s (1925, 1928) axiom systems excluded urelements.



305
Axiomatic Set Theory
Exercise
4.100	 Prove: ⊢UR(∀x)(∀y)(x ∈ y ⇒ Cls(y) ∧ El(x)).
Axiom UR2
	
(
)(
)(
)(
)
∀
∀
∀
=
∧
∈
⇒
∈
X
Y
Z X
Y
X
Z
Y
Z
Exercise
4.101	 Show:
	
a.	 ⊢UR (∀x)(∀y)(x = y ⇒ (∀z)(z ∈ x ⇔ z ∈ y))
	
b.	 ⊢UR (∀x)(∀y)(x = y ⇒ (∀z)(x ∈ z ⇔ y ∈ z))
	
c.	 ⊢UR (∀x)(∀y)(x = y ⇒ [Cls(x) ⇔ Cls(y)] ∧ [Ur(x) ⇔ Ur(y)] ∧ [M(x) ⇔ M(y)])
	
d.	 ⊢UR (∀x)(∀y)[x = y ⇒ (B(x, x) ⇒ B(x, y))], where B(x, y) arises from 
B(x, x) by replacing some, but not necessarily all, free occurrences 
of x by y, with the proviso that y is free for x in B(x, x).
	
e.	 UR is a first-order theory with equality (with respect to the given 
definition of equality).
Axiom UR3 (Null Set)
	
(
)(
)(
)
∃
∀
∉
x
x
y y
This tell us that there is a set that has no members. Of course, all urelements 
also have no elements.
Exercise
4.102	 Show: ⊢UR (∃1x)(∀y)(y ∉ x). On the basis of this exercise we can introduce 
a new individual constant ∅ satisfying the condition M(∅) ∧ (∀y)(y ∉ ∅).
Axiom UR4 (Pairing)
	
(
)(
)(
( )
( )
(
)(
)(
[
])
∀
∀
∧
⇒∃
∀
∈
⇔
=
∨
=
x
y
x
y
u u
u
x
u
y
El
El
z
z
Exercise
4.103	 Prove: ⊢UR (∀x)(∀y)(∃1z)([El(x) ∧ El(y) ∧ (∀u)(u ∈ z ⇔ [u = x ∨ u = y]) ∨ 
[(¬El(x) ∨ ¬El(y)) ∧ z = ∅]) On the basis of this exercise we can intro-
duce the unordered pair notation {x, y}. When x and y are elements, 
{x, y} is the set that has x and y as its only members; when x or y is 
a proper class, {x, y} is arbitrarily chosen to be the empty set ∅. As 
usual, the singleton notation {x} stands for {x, x}.



306
Introduction to Mathematical Logic
Definition (Ordered Pair)
Let 〈x, y〉 stand for {{x}, {x, y}}. As in the proof of Proposition 4.3, one can 
show that, for any elements x, y, u, v, 〈x, y〉 = 〈u, v〉 ⇔ [x = u ∧ y = v]. Ordered 
n-tuples can be defined as in NBG.
The class existence axioms B1–B7 of NBG have to be altered slightly by 
sometimes replacing universal quantification with respect to sets by univer-
sal quantification with respect to elements.
Axioms of Class Existence
(UR5)	
(∃X)(∀u)(∀v)(El(u) ∧ El(v) ⇒ [〈u, v〉 ∈ X ⇔ u ∈ v])
(UR6)	
(∀X)(∀Y)(∃Z)(∀u)(u ∈ Z ⇔ u ∈ X ∧ u ∈ Y)
(UR7)	
(∀X)(∃Z)(∀u)(El(u) ⇒ [u ∈ Z ⇔ u ∉ X])
(UR8)	
(∀X)(∃Z)(∀u)(El(u) ⇒ (u ∈ Z ⇔ (∃v)(〈u, v〉 ∈ X))
(UR9)	
(∀X)(∃Z)(∀u)(∀v)(El(u) ∧ El(v) ⇒ (〈u, v〉 ∈ Z ⇔ u ∈ X))
(UR10)	
(∀X)(∃Z)(∀u)(∀v)(∀w)(El(u) ∧ El(v) ∧ El(w) ⇒ [〈u, v, w〉 ∈ Z ⇔ 
〈v, w, u〉 ∈ X])
(UR11)	
(∀X)(∃Z)(∀u)(∀v)(∀w)(El(u) ∧ El(v) ∧ El(w) ⇒ [〈u, v, w〉 ∈ Z ⇔ 
〈u, w, v〉 ∈ X])
As in NBG, we can prove the existence of the intersection, complement and 
union of any classes, and the existence of the class V of all elements. But in 
UR we also need an axiom to ensure the existence of the class VM of all sets, 
or, equivalently, of the class Vur of all urelements.
Axiom UR12
	
(
)(
)(
( ))
∃
∀
∈
⇔
X
X
u u
u
Ur
This yields the existence of Vur and implies the existence of VM, that is, (∃X)
(∀u)(u ∈ X ⇔ M(u)). The class VEl of all elements is then the union Vur ∪ VM. 
Note that this axiom also yields (∃X)(∀u)(El(u) ⇒ [u ∈ X ⇔ Cls(u)]), since VM 
can be taken as the required class X.
As in NBG, we can prove a general class existence theorem.
Exercise
4.104	 Let φ(x1, …, xn, y1, …, ym) be a formula in which quantification takes 
place only with respect to elements, that is, any subformula (∀u)B has 
the form (∀u)(El(u) ⇒ C  ). Then
	
⊢UR
x
x
El x
El x
x
x
x
x
y
∃
(
) ∀
(
) … ∀
(
)
(
) ∧… ∧
(
) ⇒
〈
…
〉∈
⇔
…
Z
Z
n
n
n
n
1
1
1
1
1
(
,
,
,
,
,
ϕ
,
,
.
…
(
)


ym



307
Axiomatic Set Theory
The sum set, power set, replacement and infinity axioms can be translated 
into UR.
Axiom UR13
	
(
)(
)(
)(
(
)(
))
∀
∃
∀
∈
⇔∃
∈
∧
∈
x
y
y
x
u u
v u
v
v
Axiom UR14
	
(
)(
)(
)(
)
∀
∃
∀
∈
⇔
⊆
x
y
y
x
u u
u
where u ⊆ x stands for M(u) ∧ M(x) ∧ (∀v)(v ∈ u ⇒ v ∈ x).
Axiom UR15
	
(
)(
)(
( )
(
)(
)[
(
)(
,
)])
∀
∀
⇒∃
∀
∈
⇔∃
〈
〉∈
∧
∈
Y
x
Y
y
y
Y
x
Un
u u
v
v u
v
where Un(z) stands for
	(
)(
)(
)[
(
)
(
)
(
)
(
,
,
∀
∀
∀
∧
∧
⇒〈
〉∈
∧〈
〉∈
⇒
x
x
x
x
x
x
x
x
z
x
x
z
1
2
3
1
2
3
1
2
1
3
El
El
El
x
x
2
3
=
)]
Axiom UR16
	
(
)(
(
)(
{ }
))
∃
∅∈
∧∀
∈
⇒
∪
∈
x
x
u u
x
u
u
x
From this point on, the standard development of set theory including the 
theory of ordinal numbers, can be imitated in UR.
Proposition 4.49
NBG is a subtheory of UR.
Proof
It is easy to verify that every axiom of NBG is provable in UR, provided that 
we take the variables of NBG as restricted variables for “classes” in UR. The 
restricted variables for sets in NBG become restricted variables for “sets” 
in UR.*
*	 In fact, a formula (∀x)B(x) in NBG is an abbreviation in NBG for (∀X)((∃Y)(X ∈ Y) ⇒ B(X)). The 
latter formula is equivalent in UR to (∀x)(M(x) ⇒ B(x)), which is abbreviated as (∀x)B(x) in UR.



308
Introduction to Mathematical Logic
Proposition 4.50
UR is consistent if and only if NBG is consistent.
Proof
By Proposition 4.49, if UR is consistent, NBG is consistent. For the converse, 
note that any model of NBG yields a model of UR in which there are no ure-
lements. In fact, if we replace “Cls(x)” by the NBG formula “x = x,” then the 
axioms of UR become theorems of NBG. Hence, a proof of a contradiction in 
UR would produce a proof of a contradiction in NBG.
The axiom of regularity (Reg) takes the following form in UR.
	
(
)
(
)(
(
)(
(
)(
)))
Reg
u u
v v
v
u
UR
∀
≠∅⇒∃
∈
∧¬ ∃
∈
∧
∈
X X
X
X
It is clear that an analogue of Proposition 4.49 holds: UR + (RegUR) is an 
extension of NBG + (Reg). Likewise, the argument of Proposition 4.50 shows 
the equiconsistency of NBG + (Reg) and UR + (RegUR).
Since definition by transfinite induction (Proposition 4.14(b)) holds in UR, 
the cumulative hierarchy can be defined
	
Ψ
Ψ
Ψ
Ψ
Ψ
′∅= ∅
′(
) =
′
(
)
( ) ⇒
′
=
′
′
<
α
α
λ
λ
β
β
λ
P
Lim
o
∪
and the union H = ⋃ (Ψ″On) is the class of “pure” sets in UR and forms a 
model of NBG + (Reg). In NBG, by Proposition 4.45, (Reg) is equivalent to 
V = H, where V is the class of all sets.
If the class Vur of urelements is a set, then we can define the following by 
transfinite induction:
	
Ξ
Ξ
Ξ
Ξ
Ξ
′∅=
′(
) =
′
(
)
( ) ⇒
′
=
′
′
<
Vur
Lim
o
α
α
λ
λ
β
β
λ
P
∪
The union Hur = ∪ (Ξ″On) is a model of UR + (RegUR), and (RegUR) holds in UR 
if and only if Hur is the class VEl of all elements.
If the class Vur of urelements is a proper class, it is possible to obtain an 
analogue of Hur in the following way. For any set x whose members are 



309
Axiomatic Set Theory
urelements and any ordinal γ, we can define a function Ξx
γ by transfinite 
induction up to γ:
	
Ξ
Ξ
Ξ
Ξ
Ξ
x
x
x
o
x
x
x
if
Lim
if
o
γ
γ
γ
γ
β
λ
γ
α
α
α
γ
λ
λ
β
λ
′∅=
′(
) =
(
)
<
( ) ⇒
′
=
′
<
′
′
′
<
P
∪
o γ
Let Hur*  be the class of all elements v such that, for some x and γ, v is in 
the range of Ξx
γ. Then Hur*  determines a model of UR + (RegUR), and, in UR, 
(RegUR) holds if and only if Hur*  is the class VEl of all elements.
The equiconsistency of NBG and UR can be strengthened to show the fol-
lowing result.
Proposition 4.51
If NBG is consistent, then so is the theory UR + (Regur) + “Vur is denumerable.”
Proof
Within NBG one can define a model with domain ω that is a model of NBG 
without the axiom of infinity. The idea is due to Ackermann (1937). For any 
n and m in ω, define m
n
∈ to mean that 2m occurs as a term in the expansion 
of n as a sum of different powers of 2.* If we take “A-sets” to be members 
of ω and “proper A-classes” to be infinite subsets of ω, it is easy to verify 
all axioms of NBG + (Reg) except the axiom of infinity.† (See Bernays 1954, 
pp. 81–82 for a sketch of the argument.) Then we change the “membership” 
relation on ω by defining m ∈1 n to mean that 2m n
∈. Now we define a “set” 
to be either 0 or a member n of ω for which there is some m in ω such that 
m ∈1n. We take the “urelements” to be the members of ω that are not “sets.” 
For example, 8 is an “urelement,” since 8 = 23 and 3 is not a power of 2. 
Other small “urelements” are 1, 9, 32, 33, and 40. In general, the “urele-
ments” are sums of one or more distinct powers 2k, where k is not a power 
of 2. The “proper classes” are to be the infinite subsets of ω. Essentially the 
same argument as for Ackermann’s model shows that this yields a model 
M of all axioms of UR + (RegUR) except the axiom of infinity. Now we want 
to extend M to a model of UR. First, let r stand for the set of all finite subsets 
*	 This is equivalent to the statement that the greatest integer k such that k · 2m ≤ n is odd.
†	 For distinct natural numbers n1, …, nk, the role of the finite set {n1, …, nk} is played by the 
natural number 2n
1 + ⋯ + 2n
k.



310
Introduction to Mathematical Logic
of ω that are not members of ω, and then define by transfinite induction the 
following function Θ.
	
Θ
Θ
Θ
Θ
Θ
′∅=
′(
) =
′
(
) −
( ) ⇒
′ =
′
′
<
ω
α
α
λ
λ
β
β
λ
P
r
Lim
o
∪
Let HB = ∪ (Θ″On). Note that HB contains no members of r. Let us define a 
membership relation ∈* on HB. For any members x and y of HB, define x ∈* y 
to mean that either x and y are in ω and x ∈1y, or y ∉ ω and x ∈ y. The “urele-
ments” will be those members of ω that are the “urelements” of M. The “sets” 
will be the ordinary sets of HB that are not “urelements,” and the “proper 
classes” will be the proper classes of NBG that are subclasses of HB. It now 
requires a long careful argument to show that we have a model of UR + 
(RegUR) in which the class of urelements is a denumerable set.
A uniform method for constructing a model of UR + (RegUR) in which the 
class of urelements is a set of arbitrary size may be found in Brunner (1990, 
p. 65).* If AC holds in the underlying theory, it holds in the model as well.
The most important application of axiomatic set theories with urelements 
used to be the construction of independence proofs. The first independence 
proof for the axiom of choice, given by Fraenkel (1922b), depended essen-
tially on the existence of a denumerable set of urelements. More precise 
formulations and further developments may be found in Lindenbaum and 
Mostowski (1938) and Mostowski (1939).† Translations of these proofs into 
set theories without urelements were found by Shoenfield (1955), Mendelson 
(1956b) and Specker (1957), but only at the expense of weakening the axiom of 
regularity. This shortcoming was overcome by the forcing method of Cohen 
(1966), which applies to theories with (Reg) and without urelements.
*	 Brunner attributes the idea behind the construction to J. Truss.
†	 For more information about these methods, see Levy (1965), Pincus (1972), Howard (1973), 
and Brunner (1990).



311
5
Computability
