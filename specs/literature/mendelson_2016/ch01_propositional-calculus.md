<!-- Source: Mendelson, E. (2016). Introduction to Mathematical Logic (6th ed). Chapter 1: The Propositional Calculus (pages 1-44). BibKey: not yet in references.bib -->


1
1
The Propositional Calculus
1.1  Propositional Connectives: Truth Tables
Sentences may be combined in various ways to form more complicated sen-
tences. We shall consider only truth-functional combinations, in which the 
truth or falsity of the new sentence is determined by the truth or falsity of its 
component sentences.
Negation is one of the simplest operations on sentences. Although a sen-
tence in a natural language may be negated in many ways, we shall adopt a 
uniform procedure: placing a sign for negation, the symbol ¬, in front of the 
entire sentence. Thus, if A is a sentence, then ¬A denotes the negation of A.
The truth-functional character of negation is made apparent in the follow-
ing truth table:
	
A
A
¬
T
F
F
T
When A is true, ¬A is false; when A is false, ¬A is true. We use T and F to 
denote the truth values true and false.
Another common truth-functional operation is the conjunction: “and.” The 
conjunction of sentences A and B will be designated by A ∧ B and has the 
following truth table:
	
A
B
A
B
∧
T
T
T
F
T
F
T
F
F
F
F
F
A ∧ B is true when and only when both A and B are true. A and B are called 
the conjuncts of A ∧ B. Note that there are four rows in the table, correspond-
ing to the number of possible assignments of truth values to A and B.
In natural languages, there are two distinct uses of “or”: the inclusive and 
the exclusive. According to the inclusive usage, “A or B” means “A or B or 
both,” whereas according to the exclusive usage, the meaning is “A or B, but 



2
Introduction to Mathematical Logic
not both,” We shall introduce a special sign, ∨, for the inclusive connective. 
Its truth table is as follows:
	
A
B
A
B
∨
T
T
T
F
T
T
T
F
T
F
F
F
Thus, A ∨ B is false when and only when both A and B are false. “A ∨ B” is 
called a disjunction, with the disjuncts A and B.
Another important truth-functional operation is the conditional: “if A, then 
B.” Ordinary usage is unclear here. Surely, “if A, then B” is false when the 
antecedent A is true and the consequent B is false. However, in other cases, 
there is no well-defined truth value. For example, the following sentences 
would be considered neither true nor false:
	
1.	If 1 + 1 = 2, then Paris is the capital of France.
	
2.	If 1 + 1 ≠ 2, then Paris is the capital of France.
	
3.	If 1 + 1 ≠ 2, then Rome is the capital of France.
Their meaning is unclear, since we are accustomed to the assertion of some 
sort of relationship (usually causal) between the antecedent and the conse-
quent. We shall make the convention that “if A, then B” is false when and 
only when A is true and B is false. Thus, sentences 1–3 are assumed to be 
true. Let us denote “if A, then B” by “A ⇒ B.” An expression “A ⇒ B” is called 
a conditional. Then ⇒ has the following truth table:
	
A
B
A
B
⇒
T
T
T
F
T
T
T
F
F
F
F
T
This sharpening of the meaning of “if A, then B” involves no conflict with 
ordinary usage, but rather only an extension of that usage.*
*	 There is a common non-truth-functional interpretation of “if A, then B” connected with 
causal laws. The sentence “if this piece of iron is placed in water at time t, then the iron will 
dissolve” is regarded as false even in the case that the piece of iron is not placed in water at 
time t—that is, even when the antecedent is false. Another non-truth-functional usage occurs 
in so-called counterfactual conditionals, such as “if Sir Walter Scott had not written any nov-
els, then there would have been no War Between the States.” (This was Mark Twain’s conten-
tion in Life on the Mississippi: “Sir Walter had so large a hand in making Southern character, as 
it existed before the war, that he is in great measure responsible for the war.”) This sentence 
might be asserted to be false even though the antecedent is admittedly false. However, causal 
laws and counterfactual conditions seem not to be needed in mathematics and logic. For a 
clear treatment of conditionals and other connectives, see Quine (1951). (The quotation from 
Life on the Mississippi was brought to my attention by Professor J.C. Owings, Jr.)



3
The Propositional Calculus
A justification of the truth table for ⇒ is the fact that we wish “if A and 
B, then B” to be true in all cases. Thus, the case in which A and B are true 
justifies the first line of our truth table for ⇒, since (A and B) and B are both 
true. If A is false and B true, then (A and B) is false while B is true. This cor-
responds to the second line of the truth table. Finally, if A is false and B is 
false, (A and B) is false and B is false. This gives the fourth line of the table. 
Still more support for our definition comes from the meaning of statements 
such as “for every x, if x is an odd positive integer, then x2 is an odd positive 
integer.” This asserts that, for every x, the statement “if x is an odd positive 
integer, then x2 is an odd positive integer” is true. Now we certainly do not 
want to consider cases in which x is not an odd positive integer as coun-
terexamples to our general assertion. This supports the second and fourth 
lines of our truth table. In addition, any case in which x is an odd positive 
integer and x2 is an odd positive integer confirms our general assertion. 
This corresponds to the first line of the table.
Let us denote “A if and only if B” by “A ⇔ B.” Such an expression is called 
a biconditional. Clearly, A ⇔ B is true when and only when A and B have the 
same truth value. Its truth table, therefore is:
	
A
B
A
B
⇔
T
T
T
F
T
F
T
F
F
F
F
T
The symbols ¬, ∧, ∨, ⇒, and ⇔ will be called propositional connectives.* Any 
sentence built up by application of these connectives has a truth value that 
depends on the truth values of the constituent sentences. In order to make 
this dependence apparent, let us apply the name statement form to an expres-
sion built up from the statement letters A, B, C, and so on by appropriate appli-
cations of the propositional connectives.
	
1.	All statement letters (capital italic letters) and such letters with 
numerical subscripts† are statement forms.
	
2.	If B and C are statement forms, then so are (¬B), (B ∧ C), (B ∨ C), 
(B ⇒ C), and (B ⇔ C).
*	 We have been avoiding and shall in the future avoid the use of quotation marks to form 
names whenever this is not likely to cause confusion. The given sentence should have quota-
tion marks around each of the connectives. See Quine (1951, pp. 23–27).
†	 For example, A1, A2, A17, B31, C2, ….



4
Introduction to Mathematical Logic
	
3.	Only those expressions are statement forms that are determined 
to be so by means of conditions 1 and 2.* Some examples of state-
ment forms are B, (¬C2), (D3 ∧ (¬B)), (((¬B1) ∨ B2) ⇒ (A1 ∧ C2)), and 
(((¬A) ⇔ A) ⇔ (C ⇒ (B ∨ C))).
For every assignment of truth values T or F to the statement letters that occur 
in a statement form, there corresponds, by virtue of the truth tables for the 
propositional connectives, a truth value for the statement form. Thus, each 
statement form determines a truth function, which can be graphically repre-
sented by a truth table for the statement form. For example, the statement 
form (((¬A) ∨ B) ⇒ C) has the following truth table:
	
A
B
C
A
A
B
A
B
C
(
)
((
)
)
(((
)
)
)
¬
¬
∨
¬
∨
⇒
T
T
T
F
T
T
F
T
T
T
T
T
T
F
T
F
F
T
F
F
T
T
T
T
F
F
F
F
T
T
T
T
T
T
T
T
T
T
F
F
F
F
F
F
F
F
F
F
Each row represents an assignment of truth values to the statement letters 
A, B, and C and the corresponding truth values assumed by the statement 
forms that appear in the construction of (((¬A) ∨ B) ⇒ C).
The truth table for ((A ⇔ B) ⇒ ((¬A) ∧ B)) is as follows:
	
A
B
A
B
A
A
B
A
B
A
B
(
)
(
)
((
)
)
((
)
((
)
))
⇔
¬
¬
∧
⇔
⇒
¬
∧
T
T
T
F
F
F
F
T
F
T
T
T
T
F
F
F
F
T
F
F
T
T
F
F
If there are n distinct letters in a statement form, then there are 2n possible 
assignments of truth values to the statement letters and, hence, 2n rows in 
the truth table.
*	 This can be rephrased as follows: C  is a statement form if and only if there is a finite sequence 
B1, …, Bn (n ≥ 1) such that Bn = C  and, if 1 ≤ i ≤ n, Bi is either a statement letter or a negation, con-
junction, disjunction, conditional, or biconditional constructed from previous expressions in 
the sequence. Notice that we use script letters A, B, C, … to stand for arbitrary expressions, 
whereas italic letters are used as statement letters.



5
The Propositional Calculus
A truth table can be abbreviated by writing only the full statement form, 
putting the truth values of the statement letters underneath all occurrences 
of these letters, and writing, step by step, the truth values of each component 
statement form under the principal connective of the form.* As an example, 
for ((A ⇔ B) ⇒ ((¬A) ∧ B)), we obtain
	
((
)
((
)
))
A
B
A
B
⇔
⇒
¬
∧
T
T
T
F
FT
F
T
F
F
T
T
TF
T
T
T
F
F
T
FT
F
F
F
T
F
F
TF
F
F
Exercises
1.1	
Let ⊕ designate the exclusive use of “or.” Thus, A ⊕ B stands for “A or 
B but not both.” Write the truth table for ⊕.
1.2	 Construct truth tables for the statement forms ((A ⇒ B) ∨ (¬A)) and 
((A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C))).
1.3	
Write abbreviated truth tables for ((A ⇒ B) ∧ A) and ((A ∨ (¬C)) ⇔ B).
1.4	
Write the following sentences as statement forms, using statement let-
ters to stand for the atomic sentences—that is, those sentences that are 
not built up out of other sentences.
	
a.	 If Mr Jones is happy, Mrs Jones is not happy, and if Mr Jones is not 
happy, Mrs Jones is not happy.
	
b.	 Either Sam will come to the party and Max will not, or Sam will not 
come to the party and Max will enjoy himself.
	
c.	 A sufficient condition for x to be odd is that x is prime.
	
d.	 A necessary condition for a sequence s to converge is that s be 
bounded.
	
e.	 A necessary and sufficient condition for the sheikh to be happy is 
that he has wine, women, and song.
	
f.	 Fiorello goes to the movies only if a comedy is playing.
	
g.	 The bribe will be paid if and only if the goods are delivered.
	
h.	 If x is positive, x2 is positive.
	
i.	 Karpov will win the chess tournament unless Kasparov wins 
today.
*	 The principal connective of a statement form is the one that is applied last in constructing the 
form.



6
Introduction to Mathematical Logic
1.2  Tautologies
A truth function of n arguments is defined to be a function of n arguments, the 
arguments and values of which are the truth values T or F. As we have seen, 
any statement form containing n distinct statement letters determines a cor-
responding truth function of n arguments.*
A statement form that is always true, no matter what the truth values of its 
statement letters may be, is called a tautology. A statement form is a tautol-
ogy if and only if its corresponding truth function takes only the value T, 
or equivalently, if, in its truth table, the column under the statement form 
contains only Ts. An example of a tautology is (A ∨ (¬A)), the so-called law 
of the excluded middle. Other simple examples are (¬(A ∧ (¬A))), (A ⇔ (¬(¬A))), 
((A ∧ B) ⇒ A), and (A ⇒ (A ∨ B)).
B is said to logically imply C (or, synonymously, C is a logical consequence of B) 
if and only if every truth assignment to the statement letters of B and C that 
makes B true also makes C true. For example, (A ∧ B) logically implies A, A 
logically implies (A ∨ B), and (A ∧ (A ⇒ B)) logically implies B.
B and C are said to be logically equivalent if and only if B and C receive the 
same truth value under every assignment of truth values to the statement 
letters of B and C. For example, A and (¬(¬A)) are logically equivalent, as are 
(A ∧ B) and (B ∧ A).
*	 To be precise, enumerate all statement letters as follows: A, B, …, Z; A1, B1, …, Z1; A2, …,.  If a 
statement form contains the i
in
1th
th
,
,
…
 statement letters in this enumeration, where i1 < ⋯ < in, 
then the corresponding truth function is to have x
x
i
in
1 ,
,
…
, in that order, as its arguments, 
where xij corresponds to the ijth statement letter. For example, (A ⇒ B) generates the truth 
function:
	
x
x
f x
x
1
2
1
2
,
(
)
T
T
T
F
T
T
T
F
F
F
F
T
	 whereas (B ⇒ A) generates the truth function:
	
x
x
x
x
1
2
1
2
g
,
(
)
T
T
T
F
T
F
T
F
T
F
F
T



7
The Propositional Calculus
Proposition 1.1
	
a.	B logically implies C if and only if (B ⇒ C) is a tautology.
	
b.	B and C are logically equivalent if and only if (B ⇔ C) is a tautology.
Proof
	
a.	(i) Assume B logically implies C. Hence, every truth assignment 
that makes B true also makes C true. Thus, no truth assignment 
makes B true and C false. Therefore, no truth assignment makes 
(B ⇒ C) false, that is, every truth assignment makes (B ⇒ C) true. 
In other words, (B ⇒ C) is a tautology. (ii) Assume (B ⇒ C) is a 
tautology. Then, for every truth assignment, (B ⇒ C) is true, and, 
therefore, it is not the case that B is true and C false. Hence, every 
truth assignment that makes B true makes C true, that is, B logi-
cally implies C.
	
b.	(B ⇔ C) is a tautology if and only if every truth assignment makes (B ⇔ C) 
true, which is equivalent to saying that every truth assignment gives 
B and C the same truth value, that is, B and C are logically equivalent.
By means of a truth table, we have an effective procedure for determining 
whether a statement form is a tautology. Hence, by Proposition 1.1, we have 
effective procedures for determining whether a given statement form logi-
cally implies another given statement form and whether two given statement 
forms are logically equivalent.
To see whether a statement form is a tautology, there is another method 
that is often shorter than the construction of a truth table.
Examples
	
1.	Determine whether ((A ⇔ ((¬B) ∨ C)) ⇒ ((¬A) ⇒ B)) is a tautology.
Assume that the statement form 
sometimes is F (line 1). Then (A ⇔ 
((¬B) ∨ C)) is T and ((¬A) ⇒ B) is F 
(line 2). Since ((¬A) ⇒ B) is F, (¬A) 
is T and B is F (line 3). Since (¬A)is 
T, A is F (line 4). Since A  is F and 
(A ⇔ ((¬B) ∨ C)) is T, ((¬B) ∨ C) is F 
(line 5). Since ((¬B) ∨ C) is F, (¬B) 
and C are F (line 6). Since (¬B) is F, 
B is T (line 7). But B is both T and F 
(lines 7 and 3). Hence, it is impos-
sible for the form to be false.	
((A ⇔ ((¬B) ∨ C)) ⇒ ((¬A) ⇒ B))
F
1
T
F
2
T	
F
3
F
F
4
F
5
F
F
6
T
7



8
Introduction to Mathematical Logic
	
2.	Determine whether ((A ⇒ (B ∨ C)) ∨ (A ⇒ B)) is a tautology.
Assume that the form is F 
(line 1). Then (A ⇒ (B ∨ C)) and 
(A ⇒ B) are F (line 2). Since 
(A  ⇒ B) is F, A  is T and B is F 
(line 3). Since (A ⇒ (B ∨ C)) is F, 
A is T and (B ∨ C) is F (line 4). 
Since (B  ∨ C) is F, B and C are 
F (line 5). Thus, when A is T, B 
is F, and C is F, the form is F. 
Therefore, it is not a tautology.
((A ⇒ (B ∨ C)) ∨ (A ⇒ B))
F
1
F
F
2
T	
F
3
T
F
4
F
F
5
Exercises
1.5	
Determine whether the following are tautologies.
	
a.	 (((A ⇒ B) ⇒ B) ⇒ B)
	
b.	 (((A ⇒ B) ⇒ B) ⇒ A)
	
c.	 (((A ⇒ B) ⇒ A) ⇒ A)
	
d.	 (((B ⇒ C) ⇒ (A ⇒ B)) ⇒ (A ⇒ B))
	
e.	 ((A ∨ (¬(B ∧ C))) ⇒ ((A ⇔ C) ∨ B))
	
f.	 (A ⇒ (B ⇒ (B ⇒ A)))
	
g.	 ((A ∧ B) ⇒ (A ∨ C))
	
h.	 ((A ⇔ B) ⇔ (A ⇔ (B ⇔ A)))
	
i.	
((A ⇒ B) ∨ (B ⇒ A))
	
j.	
((¬(A ⇒ B)) ⇒ A)
1.6	
Determine whether the following pairs are logically equivalent.
	
a.	 ((A ⇒ B) ⇒ A) and A
	
b.	 (A ⇔ B) and ((A ⇒ B) ∧ (B ⇒ A))
	
c.	 ((¬A) ∨ B) and ((¬B) ∨ A)
	
d.	 (¬(A ⇔ B)) and (A ⇔ (¬B))
	
e.	 (A ∨ (B ⇔ C)) and ((A ∨ B) ⇔ (A ∨ C))
	
f.	 (A ⇒ (B ⇔ C)) and ((A ⇒ B) ⇔ (A ⇒ C))
	
g.	 (A ∧ (B ⇔ C)) and ((A ∧ B) ⇔ (A ∧ C))
1.7	
Prove:
	
a.	 (A ⇒ B) is logically equivalent to ((¬A) ∨ B).
	
b.	 (A ⇒ B) is logically equivalent to (¬(A ∧ (¬B))).
1.8	
Prove that B is logically equivalent to C if and only if B logically implies 
C and C logically implies B.



9
The Propositional Calculus
1.9	
Show that B and C are logically equivalent if and only if, in their truth 
tables, the columns under B and C are the same.
1.10	 Prove that B and C are logically equivalent if and only if (¬B) and (¬C) 
are logically equivalent.
1.11	 Which of the following statement forms are logically implied by (A ∧ B)?
	
a.	 A
	
b.	 B
	
c.	 (A ∨ B)
	
d.	 ((¬A) ∨ B)
	
e.	 ((¬B) ⇒ A)
	
f.	 (A ⇔ B)
	
g.	 (A ⇒ B)
	
h.	 ((¬B) ⇒ (¬A))
	
i.	
(A ∧ (¬B))
1.12	 Repeat Exercise 1.11 with (A ∧ B) replaced by (A ⇒ B) and by (¬(A ⇒ B)), 
respectively.
1.13	 Repeat Exercise 1.11 with (A ∧ B) replaced by (A ∨ B).
1.14	 Repeat Exercise 1.11 with (A ∧ B) replaced by (A ⇔ B) and by (¬(A ⇔ B)), 
respectively.
A statement form that is false for all possible truth values of its statement 
letters is said to be contradictory. Its truth table has only Fs in the column 
under the statement form. One example is (A ⇔ (¬A)):
	
A
A
A
A
(
)
(
(
))
¬
⇔¬
T
F
F
F
T
F
Another is (A ∧ (¬A)).
Notice that a statement form B is a tautology if and only if (¬B) is contra-
dictory, and vice versa.
A sentence (in some natural language like English or in a formal theory)* 
that arises from a tautology by the substitution of sentences for all the state-
ment letters, with occurrences of the same statement letter being replaced by 
the same sentence, is said to be logically true (according to the propositional 
calculus). Such a sentence may be said to be true by virtue of its truth-func-
tional structure alone. An example is the English sentence, “If it is raining or 
it is snowing, and it is not snowing, then it is raining,” which arises by substi-
tution from the tautology (((A ∨ B) ∧ (¬B)) ⇒ A). A sentence that comes from 
*	 By a formal theory we mean an artificial language in which the notions of meaningful expres-
sions, axioms, and rules of inference are precisely described (see page 27).



10
Introduction to Mathematical Logic
a contradictory statement form by means of substitution is said to be logically 
false (according to the propositional calculus).
Now let us prove a few general facts about tautologies.
Proposition 1.2
If B and (B ⇒ C) are tautologies, then so is C.
Proof
Assume that B and (B ⇒ C) are tautologies. If C took the value F for some 
assignment of truth values to the statement letters of B and C, then, since B 
is a tautology, B would take the value T and, therefore, (B ⇒ C) would have 
the value F for that assignment. This contradicts the assumption that (B ⇒ C) 
is a tautology. Hence, C never takes the value F.
Proposition 1.3
If T   is a tautology containing as statement letters A1, A2, …, An, and B 
arises from T   by substituting statement forms S1, S2, …, Sn for A1, A2, …, An, 
respectively, then B is a tautology; that is, substitution in a tautology yields 
a tautology.
Example
Let T   be ((A1 ∧ A2) ⇒ A1), let S1 be (B ∨ C) and let S2 be (C ∧ D). Then B is 
(((B ∨ C) ∧ (C ∧ D)) ⇒ (B ∨ C)).
Proof
Assume that T   is a tautology. For any assignment of truth values to the state-
ment letters in B, the forms S1, …, Sn  have truth values x1, …, xn (where each 
xi is T or F). If we assign the values x1, …, xn to A1, …, An, respectively, then 
the resulting truth value of T    is the truth value of B for the given assign-
ment of truth values. Since T   is a tautology, this truth value must be T. Thus, 
B always takes the value T.
Proposition 1.4
If C1 arises from B1 by substitution of C for one or more occurrences of B, then 
((B ⇔ C) ⇒ (B1 ⇔ C 1)) is a tautology. Hence, if B and C are logically equivalent, 
then so are B1 and C 1.



11
The Propositional Calculus
Example
Let B1 be (C  ∨ D), let B   be C , and let C   be (¬(¬C )). Then C 1 is ((¬(¬C )) ∨ D). Since 
C  and (¬(¬C )) are logically equivalent, (C  ∨ D) and ((¬(¬C )) ∨ D) are also logi-
cally equivalent.
Proof
Consider any assignment of truth values to the statement letters. If B and 
C have opposite truth values under this assignment, then (B ⇔ C) takes the 
value F, and, hence, ((B ⇔ C) ⇒ (B1 ⇔ C 1)) is T. If B and C take the same truth 
values, then so do B1 and C 1, since C 1 differs from B1 only in containing 
C in some places where B 1 contains B. Therefore, in this case, (B ⇔ C) is T, 
(B1 ⇔ C1) is T, and, thus, ((B ⇔ C) ⇒ (B1 ⇔ C1)) is T.
Parentheses
It is profitable at this point to agree on some conventions to avoid the use 
of so many parentheses in writing formulas. This will make the reading of 
complicated expressions easier.
First, we may omit the outer pair of parentheses of a statement form. (In the 
case of statement letters, there is no outer pair of parentheses.)
Second, we arbitrarily establish the following decreasing order of strength 
of the connectives: ¬, ∧, ∨, ⇒, ⇔. Now we shall explain a step-by-step process 
for restoring parentheses to an expression obtained by eliminating some or 
all parentheses from a statement form. (The basic idea is that, where possible, 
we first apply parentheses to negations, then to conjunctions, then to disjunc-
tions, then to conditionals, and finally to biconditionals.) Find the leftmost 
occurrence of the strongest connective that has not yet been processed.
	
i.	If the connective is ¬ and it precedes a statement form B, restore left 
and right parentheses to obtain (¬B).
	
ii.	If the connective is a binary connective C and it is preceded by a state-
ment form B and followed by a statement form D , restore left and right 
parentheses to obtain (B C D).
	 iii.	If neither (i) nor (ii) holds, ignore the connective temporarily and find 
the leftmost occurrence of the strongest of the remaining unprocessed 
connectives and repeat (i–iii) for that connective.
Examples
Parentheses are restored to the expression in the first line of each of the fol-
lowing in the steps shown:
	 1.	 A ⇔ (¬B) ∨ C ⇒ A
	
	
A ⇔ ((¬B) ∨ C) ⇒ A
	
	
A ⇔ (((¬B) ∨ C) ⇒ A)
	
	
(A ⇔ (((¬B) ∨ C) ⇒ A))



12
Introduction to Mathematical Logic
	 2.	 A ⇒ ¬B ⇒ C
	
	
A ⇒ (¬B) ⇒ C
	
	
(A ⇒ (¬B)) ⇒ C
	
	
((A ⇒ (¬B)) ⇒ C)
	 3.	 B ⇒ ¬¬A
	
	
B ⇒ ¬(¬A)
	
	
B ⇒ (¬(¬A))
	
	
(B ⇒ (¬(¬A)))
	 4.	 A ∨ ¬(B ⇒ A ∨ B)
	
	
A ∨ ¬(B ⇒ (A ∨ B))
	
	
A ∨ (¬(B ⇒ (A ∨ B)))
	
	
(A ∨ (¬(B ⇒ (A ∨ B))))
Not every form can be represented without the use of parentheses. For exam-
ple, parentheses cannot be further eliminated from A ⇒ (B ⇒ C), since A ⇒ 
B ⇒ C stands for ((A ⇒ B) ⇒ C). Likewise, the remaining parentheses cannot 
be removed from ¬(A ∨ B) or from A ∧ (B ⇒ C).
Exercises
1.15	 Eliminate as many parentheses as possible from the following forms.
	
a.	 ((B ⇒ (¬A)) ∧ C)
	
b.	 (A ∨ (B ∨ C))
	
c.	 (((A ∧ (¬B)) ∧ C) ∨ D)
	
d.	 ((B ∨ (¬C)) ∨ (A ∧ B))
	
e.	 ((A ⇔ B) ⇔ (¬(C ∨ D)))
	
f.	 ((¬(¬(¬(B ∨ C)))) ⇔ (B ⇔ C))
	
g.	 (¬((¬(¬(B ∨ C))) ⇔ (B ⇔ C)))
	
h.	 ((((A ⇒ B) ⇒ (C ⇒ D)) ∧ (¬A)) ∨ C)
1.16	 Restore parentheses to the following forms.
	
a.	 C ∨ ¬A ∧ B
	
b.	 B ⇒ ¬¬¬A ∧ C
	
c.	 C ⇒ ¬(A ∧ B ⇒ C) ∧ A ⇔ B
	
d.	 C ⇒ A ⇒ A ⇔ ¬A ∨ B
1.17	 Determine whether the following expressions are abbreviations of 
statement forms and, if so, restore all parentheses.
	
a.	 ¬¬A ⇔ A ⇔ B ∨ C
	
b.	 ¬(¬A ⇔ A) ⇔ B ∨ C
	
c.	 ¬(A ⇒ B) ∨ C ∨ D ⇒ B



13
The Propositional Calculus
	
d.	 A ⇔ (¬A ∨ B) ⇒ (A ∧ (B ∨ C)))
	
e.	 ¬A ∨ B ∨ C ∧ D ⇔ A ∧ ¬A
	
f.	 ((A ⇒ B ∧ (C ∨ D) ∧ (A ∨ D))
1.18	 If we write ¬B instead of (¬B), ⇒B C instead of (B ⇒ C), ∧B C instead of 
(B ∧ C), ∨B C instead of (B ∨ C), and ⇔B C instead of (B ⇔ C), then there 
is no need for parentheses. For example, ((¬A) ∧ (B ⇒ (¬D))), which is 
ordinarily abbreviated as ¬A ∧ (B ⇒ ¬D), becomes ∧ ¬A ⇒ B ¬D. This 
way of writing forms is called Polish notation.
	
a.	 Write ((C ⇒ (¬A)) ∨ B) and (C ∨ ((B ∧ (¬D)) ⇒ C)) in this notation.
	
b.	 If we count ⇒, ∧, ∨, and ⇔ each as +1, each statement letter as −1 
and ¬ as 0, prove that an expression B in this parenthesis-free nota-
tion is a statement form if and only if (i) the sum of the symbols of 
B is −1 and (ii) the sum of the symbols in any proper initial segment 
of B is nonnegative. (If an expression B can be written in the form 
CD, where C ≠ B, then C is called a proper initial segment of B.)
	
c.	 Write the statement forms of Exercise 1.15 in Polish notation.
	
d.	 Determine whether the following expressions are statement forms 
in Polish notation. If so, write the statement forms in the standard 
way.
	
	
i.	 ¬⇒ ABC ∨ AB ¬C
	
	
ii.	 ⇒⇒ AB ⇒⇒ BC ⇒¬AC
	
	
iii.	 ∨ ∧ ∨ ¬A¬BC ∧ ∨ AC ∨ ¬C ¬A
	
	
iv.	 ∨ ∧ B ∧ BBB
1.19	 Determine whether each of the following is a tautology, is contradic-
tory, or neither.
	
a.	 B ⇔ (B ∨ B)
	
b.	 ((A ⇒ B) ∧ B) ⇒ A
	
c.	 (¬A) ⇒ (A ∧ B)
	
d.	 (A ⇒ B) ⇒ ((B ⇒ C) ⇒ (A ⇒ C))
	
e.	 (A ⇔ ¬B) ⇒ A ∨ B
	
f.	 A ∧ (¬(A ∨ B))
	
g.	 (A ⇒ B) ⇔ ((¬A) ∨ B)
	
h.	 (A ⇒ B) ⇔ ¬(A ∧ (¬B))
	
i.	 (B ⇔ (B ⇔ A)) ⇒ A
	
j.	 A ∧ ¬A ⇒ B
1.20	 If A and B are true and C is false, what are the truth values of the fol-
lowing statement forms?
	
a.	 A ∨ C
	
b.	 A ∧ C



14
Introduction to Mathematical Logic
	
c.	 ¬A ∧ ¬C
	
d.	 A ⇔ ¬B ∨ C
	
e.	 B ∨ ¬C ⇒ A
	
f.	 (B ∨ A) ⇒ (B ⇒ ¬C)
	
g.	 (B ⇒ ¬A) ⇔ (A ⇔ C)
	
h.	 (B ⇒ A) ⇒ ((A ⇒ ¬C) ⇒ (¬C ⇒ B))
1.21	 If A ⇒ B is T, what can be deduced about the truth values of the 
following?
	
a.	 A ∨ C ⇒ B ∨ C
	
b.	 A ∧ C ⇒ B ∧ C
	
c.	 ¬A ∧ B ⇔ A ∨ B
1.22	 What further truth values can be deduced from those shown?
	
a.	 ¬A ∨ (A ⇒ B)
	
F
	
b.	 ¬(A ∧ B) ⇔ ¬A ⇒ ¬B
	
T
	
c.	 (¬A ∨ B) ⇒ (A ⇒ ¬C)
	
F
	
d.	 (A ⇔ B) ⇔ (C ⇒ ¬A)
	
F	
T
1.23	 If A ⇔ B is F, what can be deduced about the truth values of the 
following?
	
a.	 A ∧ B
	
b.	 A ∨ B
	
c.	 A ⇒ B
	
d.	 A ∧ C ⇔ B ∧ C
1.24	 Repeat Exercise 1.23, but assume that A ⇔ B is T.
1.25	 What further truth values can be deduced from those given?
	
a.	 (A ∧ B) ⇔ (A ∨ B)
	
F	 F
	
b.	 (A ⇒ ¬B) ⇒ (C ⇒ B)
	
F
1.26	 a.	 Apply Proposition 1.3 when T   is A1 ⇒ A1 ∨ A2, S1 is B ∧ D, and S2 
is ¬B.
	
b.	 Apply Proposition 1.4 when B1 is (B ⇒ C) ∧ D, B  is B ⇒ C, and C  
is ¬B ∨ C.



15
The Propositional Calculus
1.27	 Show that each statement form in column I is logically equivalent to 
the form next to it in column II.
I 
II 
a.	 A ⇒ (B ⇒ C)
(A ∧ B) ⇒ C
b.	 A ∧ (B ∨ C)
(A ∧ B) ∨ (A ∧ C)
(Distributive law)
c.	 A ∨ (B ∧ C)
(A ∨ B) ∧ (A ∨ C)
(Distributive law)
d.	 (A ∧ B) ∨ ¬ B A ∨ ¬ B
e.	 (A ∨ B) ∧ ¬ B A ∧ ¬ B
f.	
A ⇒ B
¬ B ⇒ ¬A
(Law of the contrapositive)
g.	 A ⇔ B
B ⇔ A
(Biconditional commutativity)
h.	 (A ⇔ B) ⇔ C
A ⇔ (B ⇔ C)
(Biconditional associativity)
i.	
A ⇔ B
(A ∧ B)  ∨ (¬A ∧¬B)
j.	
¬(A ⇔ B)
A ⇔ ¬ B
k.	 ¬(A ∨ B)
(¬A) ∧ (¬B)
(De Morgan’s law)
l.	
¬(A ∧ B)
(¬A) ∨ (¬B)
(De Morgan’s law)
m.	 A ∨ (A ∧ B)
A
n.	 A ∧ (A ∨ B)
A
o.	 A ∧ B
B ∧ A
(Commutativity of conjunction)
p.	 A ∨ B
B ∨ A
(Commutativity of disjunction)
q.	 (A ∧ B) ∧ C
A ∧ (B  ∧ C)
(Associativity of conjunction)
r.	
(A ∨ B) ∨ C
A ∨ (B  ∨ C)
(Associativity of disjunction)
s.	 A ⊕ B
B ⊕ A
(Commutativity of exclusive “or”)
t.	
A ⊕ B) ⊕ C
A ⊕ (B ⊕ C)
(Associativity of exclusive “or”)
u.	 A ∧ (B ⊕ C)
(A ∧ B) ⊕ (A ∧ C)
(Distributive law)
1.28	 Show the logical equivalence of the following pairs.
	
a.	 T  ∧ B and B, where T   is a tautology.
	
b.	 T   ∨ B and T, where T   is a tautology.
	
c.	 F  ∧ B and F, where F   is contradictory.
	
d.	 F  ∨ B and B, where F   is contradictory.
1.29	 a.	 Show the logical equivalence of ¬(A ⇒ B) and A ∧ ¬B.
	
b.	 Show the logical equivalence of ¬(A ⇔ B) and (A ∧ ¬B) ∨ (¬A ∧ B).
	
c.	 For each of the following statement forms, find a statement form 
that is logically equivalent to its negation and in which negation 
signs apply only to statement letters.
	
i.	 A ⇒ (B ⇔ ¬C)
	
ii.	 ¬A ∨ (B ⇒ C)
	
iii.	 A ∧ (B ∨ ¬C)



16
Introduction to Mathematical Logic
1.30	 (Duality)
	
a.	 If B  is a statement form involving only ¬, ∧, and ∨, and B ′ results 
from B by replacing each ∧ by ∨ and each ∨ by ∧, show that B is a 
tautology if and only if ¬B ′ is a tautology. Then prove that, if B ⇒ C 
is a tautology, then so is C ′ ⇒ B ′, and if B ⇔ C  is a tautology, then so 
is B ′ ⇔ C ′. (Here C  is also assumed to involve only ¬, ∧, and ∨.)
	
b.	 Among the logical equivalences in Exercise 1.27, derive (c) from (b), 
(e) from (d), (l) from (k), (p) from (o), and (r) from (q).
	
c.	 If B is a statement form involving only ¬, ∧, and ∨, and B* results 
from B by interchanging ∧ and ∨ and replacing every statement let-
ter by its negation, show that B* is logically equivalent to ¬B. Find a 
statement form that is logically equivalent to the negation of (A ∨ B 
∨ C) ∧ (¬A ∨ ¬B ∨ D), in which ¬ applies only to statement letters.
1.31	 a.	 Prove that a statement form that contains ⇔ as its only connective 
is a tautology if and only if each statement letter occurs an even 
number of times.
	
b.	 Prove that a statement form that contains ¬ and ⇔ as its only con-
nectives is a tautology if and only if ¬ and each statement letter 
occur an even number of times.
1.32	 (Shannon, 1938) An electric circuit containing only on–off switches 
(when a switch is on, it passes current; otherwise it does not) can be 
represented by a diagram in which, next to each switch, we put a letter 
representing a necessary and sufficient condition for the switch to be on 
(see Figure 1.1). The condition that a current flows through this network 
can be given by the statement form (A ∧ B) ∨ (C ∧ ¬A). A statement form 
representing the circuit shown in Figure 1.2 is (A ∧ B) ∨ ((C ∨ A) ∧ ¬B), 
which is logically equivalent to each of the following forms by virtue 
of the indicated logical equivalence of Exercise 1.27.
A
B
C
A
Figure 1.1
A
A
B
C
B
Figure 1.2



17
The Propositional Calculus
	
((
)
(
))
((
)
)
A
B
C
A
A
B
B
∧
∨
∨
∧
∧
∨¬
	
(c)
	
((
)
(
))
(
)
A
B
C
A
A
B
∧
∨
∨
∧
∨¬
	
(d)
	
((
)
(
))
(
)
A
B
A
C
A
B
∧
∨
∨
∧
∨¬
	
(p)
	
(((
)
)
)
(
)
A
B
A
C
A
B
∧
∨
∨
∧
∨¬
	
(r)
	
(
)
(
)
A
C
A
B
∨
∧
∨¬
	
(p), (m)
	
A
C
B
∨
∧¬
(
) 	
(c)
	
Hence, the given circuit is equivalent to the simpler circuit shown 
in Figure 1.3. (Two circuits are said to be equivalent if current flows 
through one if and only if it flows through the other, and one circuit is 
simpler if it contains fewer switches.)
	
a.	 Find simpler equivalent circuits for those shown in Figures 1.4 
through 1.6.
	
b.	 Assume that each of the three members of a committee votes yes on 
a proposal by pressing a button. Devise as simple a circuit as you 
can that will allow current to pass when and only when at least 
two of the members vote in the affirmative.
	
c.	 We wish a light to be controlled by two different wall switches in a 
room in such a way that flicking either one of these switches will 
turn the light on if it is off and turn it off if it is on. Construct a 
simple circuit to do the required job.
A
B
C
Figure 1.3
C
A
A
C
B
C
B
C
Figure 1.4



18
Introduction to Mathematical Logic
1.33	 Determine whether the following arguments are logically correct by 
representing each sentence as a statement form and checking whether 
the conclusion is logically implied by the conjunction of the assump-
tions. (To do this, assign T to each assumption and F to the conclusion, 
and determine whether a contradiction results.)
	
a.	 If Jones is a communist, Jones is an atheist. Jones is an atheist. 
Therefore, Jones is a communist.
	
b.	 If the temperature and air pressure remained constant, there was 
no rain. The temperature did remain constant. Therefore, if there 
was rain, then the air pressure did not remain constant.
	
c.	 If Gorton wins the election, then taxes will increase if the deficit 
will remain high. If Gorton wins the election, the deficit will remain 
high. Therefore, if Gorton wins the election, taxes will increase.
	
d.	 If the number x ends in 0, it is divisible by 5. x does not end in 0. 
Hence, x is not divisible by 5.
	
e.	 If the number x ends in 0, it is divisible by 5. x is not divisible by 5. 
Hence, x does not end in 0.
	
f.	 If a = 0 or b = 0, then ab = 0. But ab ≠ 0. Hence, a ≠ 0 and b ≠ 0.
	
g.	 A sufficient condition for f to be integrable is that ɡ be bounded. 
A necessary condition for h to be continuous is that f is integrable. 
Hence, if ɡ is bounded or h is continuous, then f is integrable.
	
h.	 Smith cannot both be a running star and smoke cigarettes. Smith is 
not a running star. Therefore, Smith smokes cigarettes.
	
i.	 If Jones drove the car, Smith is innocent. If Brown fired the gun, 
then Smith is not innocent. Hence, if Brown fired the gun, then 
Jones did not drive the car.
A
C
C
D
D
B
A
A
B
Figure 1.6
A
C
C
C
B
B
B
A
Figure 1.5



19
The Propositional Calculus
1.34	 Which of the following sets of statement forms are satisfiable, in the 
sense that there is an assignment of truth values to the statement let-
ters that makes all the forms in the set true?
	
a.	 A ⇒ B
	
	 B ⇒ C
	
	 C ∨ D ⇔ ¬B
	
b.	 ¬(¬B ∨ A)
	
	 A ∨ ¬C
	
	 B ⇒ ¬C
	
c.	 D ⇒ B
	
	 A ∨ ¬B
	
	 ¬(D ∧ A)
	
	 D
1.35	 Check each of the following sets of statements for consistency by rep-
resenting the sentences as statement forms and then testing their con-
junction to see whether it is contradictory.
	
a.	 Either the witness was intimidated or, if Doherty committed 
suicide, a note was found. If the witness was intimidated, then 
Doherty did not commit suicide. If a note was found, then Doherty 
committed suicide.
	
b.	 The contract is satisfied if and only if the building is completed 
by 30 November. The building is completed by 30 November 
if and only if the electrical subcontractor completes his work by 
10 November. The bank loses money if and only if the contract is 
not satisfied. Yet the electrical subcontractor completes his work by 
10 November if and only if the bank loses money.
1.3  Adequate Sets of Connectives
Every statement form containing n statement letters generates a correspond-
ing truth function of n arguments. The arguments and values of the func-
tion are T or F. Logically equivalent forms generate the same truth function. 
A natural question is whether all truth functions are so generated.
Proposition 1.5
Every truth function is generated by a statement form involving the connec-
tives ¬, ∧, and ∨.



20
Introduction to Mathematical Logic
Proof
(Refer to Examples 1 and 2 below for clarification.) Let f(x1, …, xn) be a truth func-
tion. Clearly f can be represented by a truth table of 2n rows, where each row 
represents some assignment of truth values to the variables x1, …, xn, followed 
by the corresponding value of f(x1, …, xn). If 1 ≤ i ≤ 2n, let Ci be the conjunction 
U
U
U
i
i
n
i
1
2
∧
∧…∧
, where Uj
i is Aj if, in the ith row of the truth table, xj takes the 
value T, and Uj
i is ¬Aj if xj takes the value F in that row. Let D be the disjunction of 
all those Cis such that f has the value T for the ith row of the truth table. (If there 
are no such rows, then f always takes the value F, and we let D be A1 ∧ ¬A1, which 
satisfies the theorem.) Notice that D involves only ¬, ∧, and ∨. To see that D has 
f as its corresponding truth function, let there be given an assignment of truth 
values to the statement letters A1, …, An, and assume that the corresponding 
assignment to the variables x1, …, xn is row k of the truth table for f. Then Ck has 
the value T for this assignment, whereas every other Ci has the value F. If f has 
the value T for row k, then Ck is a disjunct of D. Hence, D would also have the 
value T for this assignment. If f has the value F for row k, then Ck is not a dis-
junct of D and all the disjuncts take the value F for this assignment. Therefore, 
D would also have the value F. Thus, D generates the truth function f.
Examples
	
1.	
x
x
f x
x
1
2
1
2
(
,
)
T
T
F
F
T
T
T
F
T
F
F
T
	
	 D is (¬A1 ∧ A2) ∨ (A1 ∧ ¬A2) ∨ (¬A1 ∧ ¬A2).
	
2.
		
x
x
x
x
x
x
1
2
3
1
2
3
g
,
,
(
)
T
T
T
T
F
T
T
F
T
F
T
T
F
F
T
T
T
T
F
F
F
T
F
F
T
F
F
F
F
F
F
T
	
D
A
A
A
A
A
A
A
A
A
A
A
A
is (
)
(
)
(
)
(
).
1
2
3
1
2
3
1
2
3
1
2
3
∧
∧
∨
∧¬
∧
∨¬
∧¬
∧
∨¬
∧¬
∧¬



21
The Propositional Calculus
Exercise
1.36	 Find statement forms in the connectives ¬, ∧, and ∨ that have the fol-
lowing truth functions.
	
x
x
x
f x
x
x
x
x
x
h x
x
x
1
2
3
1
2
3
1
2
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
(
)
(
)
(
)
g
T
T
T
T
T
F
F
T
T
T
T
T
T
F
T
T
T
F
F
F
T
F
F
F
T
T
F
F
T
T
F
T
F
F
F
T
T
F
F
F
T
F
F
F
F
T
F
T
Corollary 1.6
Every truth function can be generated by a statement form containing as 
connectives only ∧ and ¬, or only ∨ and ¬, or only ⇒ and ¬.
Proof
Notice that B ∨ C is logically equivalent to ¬(¬B ∧ ¬C). Hence, by the sec-
ond part of Proposition 1.4, any statement form in ∧, ∨, and ¬ is logically 
equivalent to a statement form in only ∧ and ¬ [obtained by replacing all 
expressions B ∨ C  by ¬(¬B ∧ ¬C  )]. The other parts of the corollary are similar 
consequences of the following tautologies:
	
B
C
B
C
B
C
B
C
B
C
B
C
∧
⇔
∨
(
)
∨
⇔
⇒
(
)
∧
⇔
⇒
(
)
¬ ¬
¬
¬
¬
¬
We have just seen that there are certain pairs of connectives—for exam-
ple, ∧ and ¬—in terms of which all truth functions are definable. It turns 
out that there is a single connective, ↓ (joint denial), that will do the same 
job. Its truth table is
	
A
B
A
B
↓
T
T
F
F
T
F
T
F
F
F
F
T



22
Introduction to Mathematical Logic
A ↓ B is true when and only when neither A nor B is true. Clearly, ¬A ⇔ (A ↓ 
A) and (A ∧ B) ⇔ ((A ↓ A) ↓ (B ↓ B)) are tautologies. Hence, the adequacy of ↓ 
for the construction of all truth functions follows from Corollary 1.6.
Another connective, | (alternative denial), is also adequate for this pur-
pose. Its truth table is
	
A
B
A B
|
T
T
F
F
T
T
T
F
T
F
F
T
A|B is true when and only when not both A and B are true. The adequacy 
of | follows from the tautologies ¬A ⇔ (A|A) and (A ∨ B) ⇔ ((A|A)|(B|B)).
Proposition 1.7
The only binary connectives that alone are adequate for the construction 
of all truth functions are ↓ and |.
Proof
Assume that h(A, B) is an adequate connective. Now, if h(T, T) were T, then 
any statement form built up using h alone would take the value T when all 
its statement letters take the value T. Hence, ¬A would not be definable in 
terms of h. So, h(T, T) = F. Likewise, h(F, F) = T. Thus, we have the partial 
truth table:
	
A
B
h A B
(
,
)
T
T
F
F
T
T
F
F
F
T
If the second and third entries in the last column are F, F or T, T, then h is ↓ 
or |. If they are F, T, then h(A, B) ⇔ ¬B is a tautology; and if they are T, F, then 
h(A, B) ⇔ ¬A is a tautology. In both cases, h would be definable in terms of ¬. 



23
The Propositional Calculus
But ¬ is not adequate by itself because the only truth functions of one vari-
able definable from it are the identity function and negation itself, whereas 
the truth function that is always T would not be definable.
Exercises
1.37	 Prove that each of the pairs ⇒, ∨ and ¬, ⇔ is not alone adequate to 
express all truth functions.
1.38	 a.	 Prove that A ∨ B can be expressed in terms of ⇒ alone.
	
b.	 Prove that A ∧ B cannot be expressed in terms of ⇒ alone.
	
c.	 Prove that A ⇔ B cannot be expressed in terms of ⇒ alone.
1.39	 Show that any two of the connectives {∧, ⇒, ⇔} serve to define the 
remaining one.
1.40	 With one variable A, there are four truth functions:
	
A
A
A
A
A
A
¬
∨¬
∧¬
T
F
T
F
F
T
T
F
	
a.	 With two variable A and B, how many truth functions are there?
	
b.	 How many truth functions of n variables are there?
1.41	 Show that the truth function h determined by (A ∨ B) ⇒ ¬C generates 
all truth functions.
1.42	 By a literal we mean a statement letter or a negation of a statement 
letter. A statement form is said to be in disjunctive normal form (dnf) 
if it is a disjunction consisting of one or more disjuncts, each of 
which is a conjunction of one or more literals—for example, (A ∧ B) 
∨ (¬A ∧ C), (A ∧ B ∧ ¬A) ∨ (C ∧ ¬B) ∨ (A ∧ ¬C), A, A ∧ B, and A ∨ (B 
∨ C). A form is in conjunctive normal form (cnf) if it is a conjunction 
of one or more conjuncts, each of which is a disjunction of one or 
more literals—for example, (B ∨ C) ∧ (A ∨ B), (B ∨ ¬C) ∧ (A ∨ D), A ∧ 
(B ∨ A) ∧ (¬B ∨ A), A ∨ ¬B, A ∧ B, A. Note that our terminology con-
siders a literal to be a (degenerate) conjunction and a (degenerate) 
disjunction.
	
a.	 The proof of Proposition 1.5 shows that every statement form B is 
logically equivalent to one in disjunctive normal form. By applying 
this result to ¬B, prove that B is also logically equivalent to a form 
in conjunctive normal form.



24
Introduction to Mathematical Logic
	
b.	 Find logically equivalent dnfs and cnfs for ¬(A ⇒ B) ∨ (¬A ∧ C) and 
A ⇔ ((B ∧ ¬A) ∨ C). [Hint: Instead of relying on Proposition 1.5, it is 
usually easier to use Exercise 1.27(b) and (c).]
	
c.	 A dnf (cnf) is called full if no disjunct (conjunct) contains two occur-
rences of literals with the same letter and if a letter that occurs in 
one disjunct (conjunct) also occurs in all the others. For example, 
(A ∧ ¬A ∧ B) ∨ (A ∧ B), (B ∧ B ∧ C) ∨ (B ∧ C) and (B ∧ C) ∨ B are 
not full, whereas (A ∧ B ∧ ¬C) ∨ (A ∧ B ∧ C) ∨ (A ∧ ¬B ∧ ¬C) and 
(A ∧ ¬B) ∨ (B ∧ A) are full dnfs.
	
i.	
Find full dnfs and cnfs logically equivalent to (A ∧ B) ∨ ¬A 
and ¬(A ⇒ B) ∨ (¬A ∧ C).
	
ii.	
Prove that every noncontradictory (nontautologous) state-
ment form B  is logically equivalent to a full dnf (cnf) C, and, 
if C  contains exactly n letters, then B  is a tautology (is contra-
dictory) if and only if C  has 2n disjuncts (conjuncts).
	
d.	 For each of the following, find a logically equivalent dnf (cnf), and 
then find a logically equivalent full dnf (cnf):
	
i.	 (A ∨ B) ∧ (¬B ∨ C)
	
ii.	 ¬A ∨ (B ⇒ ¬C)
	
iii.	 (A ∧ ¬B) ∨ (A ∧ C)
	
iv.	 (A ∨ B) ⇔ ¬C
	
e.	 Construct statement forms in ¬ and ∧ (respectively, in ¬ and ∨ or in 
¬ and ⇒) logically equivalent to the statement forms in (d).
1.43	 A statement form is said to be satisfiable if it is true for some assignment 
of truth values to its statement letters. The problem of determining the 
satisfiability of an arbitrary cnf plays an important role in the theory of 
computational complexity; it is an example of a so-called NP-complete 
problem (see Garey and Johnson, 1978).
	
a.	 Show that B is satisfiable if and only if ¬B is not a tautology.
	
b.	 Determine whether the following are satisfiable:
	
i.	
(A ∨ B) ∧ (¬A ∨ B ∨ C) ∧ (¬A ∨ ¬B ∨ ¬C)
	
ii.	
((A ⇒ B) ∨ C) ⇔ (¬B ∧ (A ∨ C))
	
c.	 Given a disjunction D of four or more literals: L1 ∨ L2 ∨ … ∨ Ln, let 
C1, …, Cn−2 be statement letters that do not occur in D, and construct 
the cnf E:
	
(
)
(
)
(
)
(
)
(
L
L
C
C
L
C
C
L
C
C
L
C
C
n
n
n
1
2
1
1
3
2
2
4
3
3
1
2
∨
∨
∧¬
∨
∨
∧¬
∨
∨
∧…
∧¬
∨
∨
∧¬
−
−
−
n
n
L
C
−∨
∨¬
2
1)
	
	
Show that any truth assignment satisfying D can be extended 
to a truth assignment satisfying E and, conversely, any truth 



25
The Propositional Calculus
assignment satisfying E is an extension of a truth assignment sat-
isfying D. (This permits the reduction of the problem of satisfy-
ing cnfs to the corresponding problem for cnfs with each conjunct 
containing at most three literals.)
	
d.	 For a disjunction D of three literals L1 ∨ L2 ∨ L3, show that a 
form that has the properties of E in (c) cannot be constructed, 
with E a cnf in which each conjunct contains at most two literals 
(R. Cowen).
1.44	 (Resolution) Let B be a cnf and let C be a statement letter. If C is a dis-
junct of a disjunction D1 in B and ¬C is a disjunct of another disjunc-
tion D2 in B, then a nonempty disjunction obtained by eliminating C 
from D1 and ¬C from D2 and forming the disjunction of the remaining 
literals (dropping repetitions) is said to be obtained from B by resolu-
tion on C. For example, if B is
	
(
)
(
)
(
)
A
C
B
A
D
B
C
D
A
∨¬
∨¬
∧¬
∨
∨¬
∧
∨
∨
	
the first and third conjuncts yield A ∨ ¬B ∨ D by resolution on C. In 
addition, the first and second conjuncts yield ¬C ∨ ¬B ∨ D by resolu-
tion on A, and the second and third conjuncts yield D ∨ ¬B ∨ C by 
resolution on A. If we conjoin to B any new disjunctions obtained by 
resolution on all variables, and if we apply the same procedure to 
the new cnf and keep on iterating this operation, the process must 
eventually stop, and the final result is denoted Res(B). In the example, 
Res(B) is
	
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
A
C
B
A
D
B
C
D
A
C
B
D
D
B
C
A
B
D
D
∨¬
∨¬
∧¬
∨
∨¬
∧
∨
∨
∧¬
∨¬ ∨
∧
∨¬ ∨
∧
∨¬ ∨
∧
∨¬B)
	
Notice that we have not been careful about specifying the order in 
which conjuncts or disjuncts are written, since any two arrangements 
will be logically equivalent.)
	
a.	 Find Res(B ) when B is each of the following:
	
i.	 (A ∨ ¬B) ∧ B
	
ii.	 (A ∨ B ∨ C) ∧ (A ∨ ¬B ∨ C)
	
iii.	 (A ∨ C) ∧ (¬A ∨ B) ∧ (A ∨ ¬C) ∧ (¬A ∨ ¬B)
	
b.	 Show that B logically implies Res(B).
	
c.	 If B is a cnf, let BC be the cnf obtained from B by deleting those con-
juncts that contain C or ¬C. Let rC(B ) be the cnf that is the conjunc-
tion of BC and all those disjunctions obtained from B  by resolution 



26
Introduction to Mathematical Logic
on C. For example, if B   is the cnf in the example above, then rC(B) 
is (¬A ∨ D ∨ ¬B) ∧ (A ∨ ¬B ∨ D). Prove that, if rC(B) is satisfiable, 
then so is B (R. Cowen).
	
d.	 A cnf B is said to be a blatant contradiction if it contains some letter 
C and its negation ¬C as conjuncts. An example of a blatant contra-
diction is (A ∨ B) ∧ B ∧ (C ∨ D) ∧ ¬B. Prove that if B is unsatisfiable, 
then Res(B) is a blatant contradiction. [Hint: Use induction on the 
number n of letters that occur in B. In the induction step, use (c).]
	
e.	 Prove that B is unsatisfiable if and only if Res(B) is a blatant 
contradiction.
1.45	 Let B and D be statement forms such that B ⇒ D is a tautology.
	
a.	 If B and D have no statement letters in common, show that either B 
is contradictory or D is a tautology.
	
b.	 (Craig’s interpolation theorem) If B and D have the statement letters 
B1, …, Bn in common, prove that there is a statement form C having 
B1, …, Bn as its only statement letters such that B ⇒ C and C ⇒ D are 
tautologies.
	
c.	 Solve the special case of (b) in which B is (B1 ⇒ A) ∧ (A ⇒ B2) and D 
is (B1 ∧ C) ⇒ (B2 ∧ C).
1.46	 a.	 A certain country is inhabited only by truth-tellers (people who 
always tell the truth) and liars (people who always lie). Moreover, 
the inhabitants will respond only to yes or no questions. A tourist 
comes to a fork in a road where one branch leads to the capital 
and the other does not. There is no sign indicating which branch 
to take, but there is a native standing at the fork. What yes or 
no question should the tourist ask in order to determine which 
branch to take? [Hint: Let A stand for “You are a truth-teller” 
and let B stand for “The left-hand branch leads to the capital.” 
Construct, by means of a suitable truth table, a statement form 
involving A and B such that the native’s answer to the question as 
to whether this statement form is true will be yes when and only 
when B is true.]
	
b.	 In a certain country, there are three kinds of people: workers (who 
always tell the truth), businessmen (who always lie), and students 
(who sometimes tell the truth and sometimes lie). At a fork in the 
road, one branch leads to the capital. A worker, a businessman and 
a student are standing at the side of the road but are not identifiable 
in any obvious way. By asking two yes or no questions, find out 
which fork leads to the capital (Each question may be addressed to 
any of the three.)
More puzzles of this kind may be found in Smullyan (1978, Chapter 3; 1985, 
Chapters 2, 4 through 8).



27
The Propositional Calculus
1.4  An Axiom System for the Propositional Calculus
Truth tables enable us to answer many of the significant questions concerning 
the truth-functional connectives, such as whether a given statement form is a 
tautology, is contradictory, or neither, and whether it logically implies or is logi-
cally equivalent to some other given statement form. The more complex parts 
of logic we shall treat later cannot be handled by truth tables or by any other 
similar effective procedure. Consequently, another approach, by means of for-
mal axiomatic theories, will have to be tried. Although, as we have seen, the 
propositional calculus surrenders completely to the truth table method, it will 
be instructive to illustrate the axiomatic method in this simple branch of logic.
A formal theory S  is defined when the following conditions are satisfied:
	
1.	A countable set of symbols is given as the symbols of S .* A finite 
sequence of symbols of S  is called an expression of S.
	
2.	There is a subset of the set of expressions of S called the set of well-
formed formulas (wfs) of S. There is usually an effective procedure to 
determine whether a given expression is a wf.
	
3.	There is a set of wfs called the set of axioms of S. Most often, one can 
effectively decide whether a given wf is an axiom; in such a case, S  is 
called an axiomatic theory.
	
4.	There is a finite set R1, …, Rn of relations among wfs, called rules of infer-
ence. For each Ri, there is a unique positive integer j such that, for every 
set of j wfs and each wf B, one can effectively decide whether the given 
j wfs are in the relation Ri to B, and, if so, B is said to follow from or to be 
a direct consequence of the given wfs by virtue of Ri.†
A proof in S  is a sequence B1, …, Bk of wfs such that, for each i, either Bi is an 
axiom of S  or Bi is a direct consequence of some of the preceding wfs in the 
sequence by virtue of one of the rules of inference of S.
A theorem of S  is a wf B of S such that B is the last wf of some proof in S. 
Such a proof is called a proof of B in S.
Even if S is axiomatic—that is, if there is an effective procedure for check-
ing any given wf to see whether it is an axiom—the notion of “theorem” is 
not necessarily effective since, in general, there is no effective procedure for 
determining, given any wf B, whether there is a proof of B. A theory for 
which there is such an effective procedure is said to be decidable; otherwise, 
the theory is said to be undecidable.
*	 These “symbols” may be thought of as arbitrary objects rather than just linguistic objects. 
This will become absolutely necessary when we deal with theories with uncountably many 
symbols in Section 2.12.
†	 An example of a rule of inference will be the rule modus ponens (MP): C  follows from B and 
B ⇒ C. According to our precise definition, this rule is the relation consisting of all ordered 
triples 〈B, B ⇒ C, C 〉, where B and C are arbitrary wfs of the formal system.



28
Introduction to Mathematical Logic
From an intuitive standpoint, a decidable theory is one for which a machine 
can be devised to test wfs for theoremhood, whereas, for an undecidable 
theory, ingenuity is required to determine whether wfs are theorems.
A wf C   is said to be a consequence in S of a set Γ of wfs if and only if there 
is a sequence B1, …, Bk of wfs such that C is Bk and, for each i, either Bi is an 
axiom or Bi is in Γ, or Bi is a direct consequence by some rule of inference of 
some of the preceding wfs in the sequence. Such a sequence is called a proof 
(or deduction) of C from Γ. The members of Γ are called the hypotheses or prem-
isses of the proof. We use Γ ⊢ C as an abbreviation for “C is a consequence of 
Γ”. In order to avoid confusion when dealing with more than one theory, we 
write Γ ⊢S  C, adding the subscript S  to indicate the theory in question.
If Γ is a finite set {H 1, …, Hm}, we write H1, …, Hm ⊢ C instead of {H1, …, 
Hm} ⊢ C. If Γ is the empty set ∅, then ∅ ⊢ C if and only if C is a theorem. It is 
customary to omit the sign “∅” and simply write ⊢C. Thus, ⊢C is another way 
of asserting that C  is a theorem.
The following are simple properties of the notion of consequence:
	 1.	 If Γ ⊆ Δ and Γ ⊢ C, then Δ ⊢ C.
	 2.	 Γ ⊢ C if and only if there is a finite subset Δ of Γ such that Δ ⊢ C.
	 3.	 If Δ ⊢ C, and for each B in Δ, Γ ⊢ B, then Γ ⊢ C.
Assertion 1 represents the fact that if C is provable from a set Γ of premisses, 
then, if we add still more premisses, C is still provable. Half of 2 follows from 
1. The other half is obvious when we notice that any proof of C from Γ uses 
only a finite number of premisses from Γ. Proposition 1.3 is also quite simple: 
if C is provable from premisses in Δ, and each premiss in Δ is provable from 
premisses in Γ, then C is provable from premisses in Γ.
We now introduce a formal axiomatic theory L for the propositional calculus.
	 1.	 The symbols of L are ¬, ⇒, (, ), and the letters Ai with positive integers 
i as subscripts: A1, A2, A3, …. The symbols ¬ and ⇒ are called primitive 
connectives, and the letters Ai are called statement letters.
	 2.	 a.	 All statement letters are wfs.
	
	
b.	 If B and C are wfs, then so are (¬B) and (B ⇒C).* Thus, a wf of L 
is just a statement form built up from the statement letters Ai by 
means of the connectives ¬ and ⇒.
	 3.	 If B, C, and D are wfs of L, then the following are axioms of L:
(A1) (B ⇒ (C ⇒B ))
(A2) ((B ⇒ (C ⇒D )) ⇒ ((B ⇒C ) ⇒ (B ⇒D )))
(A3) (((¬C ) ⇒ (¬B )) ⇒(((¬C ) ⇒B) ⇒C ))
*	 To be precise, we should add the so called extremal clause: (c) an expression is a wf if and 
only if it can be shown to be a wf on the basis of clauses (a) and (b). This can be made rigorous 
using as a model the definition of statement form in the footnote on page 4.



29
The Propositional Calculus
	 4.	 The only rule of inference of L is modus ponens: C is a direct consequence 
of B and (B ⇒ C). We shall abbreviate applications of this rule by MP.*
We shall use our conventions for eliminating parentheses.
Notice that the infinite set of axioms of L is given by means of three axiom 
schemas (A1)–(A3), with each schema standing for an infinite number of axi-
oms. One can easily check for any given wf whether or not it is an axiom; 
therefore, L is axiomatic. In setting up the system L, it is our intention to 
obtain as theorems precisely the class of all tautologies.
We introduce other connectives by definition:
D
for
1
(
)
∧
(
)
⇒
(
)
B
C
B
C
¬
¬
D
for
2
(
)
∨
(
)
(
) ⇒
B
C
B
C
¬
D
for
3
(
)
⇔
(
)
⇒
(
) ∧
⇒
(
)
B
C
B
C
C
B
The meaning of (D1), for example, is that, for any wfs B and C, “(B ∧ C )” is an 
abbreviation for “¬(B ⇒ ¬C)”.
Lemma 1.8:  ⊢L B ⇒ B for all wfs B.
Proof†
We shall construct a proof in L of B ⇒ B.
	 1.	 (B  ⇒ ((B ⇒ B) ⇒ B)) ⇒	
Instance of axiom schema (A2)
	
	
((B ⇒ (B ⇒ B)) ⇒ (B ⇒ B))
*	 A common English synonym for modus ponens is the detachment rule.
†	 The word “proof” is used in two distinct senses. First, it has a precise meaning defined above as 
a certain kind of finite sequence of wfs of L. However, in another sense, it also designates certain 
sequences of the English language (supplemented by various technical terms) that are supposed to 
serve as an argument justifying some assertion about the language L (or other formal theories). In 
general, the language we are studying (in this case, L) is called the object language, while the language 
in which we formulate and prove statements about the object language is called the metalanguage. 
The metalanguage might also be formalized and made the subject of study, which we would carry 
out in a metametalanguage, and so on. However, we shall use the English language as our (unfor-
malized) metalanguage, although, for a substantial part of this book, we use only a mathematically 
weak portion of the English language. The contrast between object language and metalanguage 
is also present in the study of a foreign language; for example, in a Sanskrit class, Sanskrit is the 
object language, while the metalanguage, the language we use, is English. The distinction between 
proof and metaproof (i.e., a proof in the metalanguage) leads to a distinction between theorems of 
the object language and metatheorems of the metalanguage. To avoid confusion, we generally use 
“proposition” instead of “metatheorem.” The word “metamathematics” refers to the study of logi-
cal and mathematical object languages; sometimes the word is restricted to those investigations 
that use what appear to the metamathematician to be constructive (or so-called finitary) methods.



30
Introduction to Mathematical Logic
	 2.	 B ⇒ ((B ⇒ B) ⇒ B)	
Axiom schema (A1)
	 3.	 (B ⇒ (B ⇒ B)) ⇒ (B ⇒ B)	
From 1 and 2 by MP
	 4.	 B ⇒ (B ⇒ B)	
Axiom schema (A1)
	 5.	 B ⇒ B	
From 3 and 4 by MP*
Exercise
1.47	 Prove:
	
a.	 ⊢L (¬B ⇒ B) ⇒ B
	
b.	 B ⇒ C, C ⇒ D ⊢L B ⇒ D
	
c.	 B ⇒ (C ⇒ D) ⊢L C ⇒ (B ⇒ D)
	
d.	 ⊢L (¬C ⇒ ¬B) ⇒ (B ⇒ C)
In mathematical arguments, one often proves a statement C on the assump-
tion of some other statement B and then concludes that “if B, then C ” is 
true. This procedure is justified for the system L by the following theorem.
Proposition 1.9 (Deduction Theorem)†
If Γ is a set of wfs and B and C are wfs, and Γ, B ⊢ C, then Γ ⊢ B ⇒ C. In par-
ticular, if B ⊢ C, then ⊢B ⇒ C (Herbrand, 1930).
Proof
Let C1, …, Cn be a proof of C from Γ ∪ {B}, where Cn is C. Let us prove, by induction 
on j, that Γ ⊢ B ⇒ Cj for 1 ≤ j ≤ n. First of all, C1 must be either in Γ or an axiom of 
L or B itself. By axiom schema (A1), C1 ⇒ (B ⇒ C1) is an axiom. Hence, in the first 
two cases, by MP, Γ ⊢ B ⇒ C1. For the third case, when C1 is B, we have ⊢B ⇒ C1 by 
Lemma 1.8, and, therefore, Γ ⊢ B ⇒ C1. This takes care of the case j = 1. Assume 
now that Γ ⊢ B ⇒ Ck for all k < j. Either Cj is an axiom, or Cj is in Γ, or Cj is B, or Cj fol-
lows by modus ponens from some Cℓ and Cm, where ℓ < j, m < j, and Cm has the form 
Cℓ ⇒ Cj. In the first three cases, Γ ⊢ B ⇒ Cj as in the case j = 1 above. In the last case, 
we have, by inductive hypothesis, Γ ⊢ B ⇒ Cℓ and Γ ⊢ B ⇒ (Cℓ ⇒ Cj). But, by axiom 
schema (A2), ⊢ (B ⇒ (Cℓ ⇒ Cj)) ⇒ ((B ⇒ Cℓ) ⇒ (B ⇒ Cj)). Hence, by MP, Γ ⊢ (B ⇒ Cℓ) ⇒ 
(B ⇒ Cj), and, again by MP, Γ ⊢ B ⇒ Cj. Thus, the proof by induction is complete. 
The case j = n is the desired result. [Notice that, given a deduction of C from Γ and 
*	 The reader should not be discouraged by the apparently unmotivated step 1 of the proof. As 
in most proofs, we actually begin with the desired result, B ⇒ B, and then look for an appro-
priate axiom that may lead by MP to that result. A mixture of ingenuity and experimentation 
leads to a suitable instance of axiom (A2).
†	 For the remainder of the chapter, unless something is said to the contrary, we shall omit the 
subscript L in ⊢L. In addition, we shall use Γ, B ⊢ C to stand for Γ ∪ {B} ⊢ C. In general, we let 
Γ, B1, …, Bn ⊢ C stand for Γ ∪ {B1, …, Bn} ⊢ C.



31
The Propositional Calculus
B, the proof just given enables us to construct a deduction of B ⇒ C  from Γ. Also 
note that axiom schema (A3) was not used in proving the deduction theorem.]
Corollary 1.10
	 a.	 B ⇒ C, C ⇒ D ⊢ B ⇒ D
	 b.	 B ⇒ (C ⇒ D), C ⊢ B ⇒ D
Proof
For part (a):
	 1.	 B ⇒ C	
Hyp (abbreviation for “hypothesis”)
	 2.	 C ⇒ D	
Hyp
	 3.	 B	
Hyp
	 4.	 C	
1, 3, MP
	 5.	 D	
2, 4, MP
Thus, B ⇒ C, C ⇒ D, B ⊢ D. So, by the deduction theorem, B ⇒ C, C ⇒ D ⊢ B ⇒ D.
To prove (b), use the deduction theorem.
Lemma 1.11
For any wfs B and C, the following wfs are theorems of L.
	 a.	 ¬¬B ⇒ B
	 b.	 B ⇒ ¬¬B
	 c.	 ¬B ⇒ (B ⇒ C)
	 d.	 (¬C ⇒ ¬B) ⇒ (B ⇒ C)
	 e.	 (B ⇒ C) ⇒ (¬C ⇒ ¬B)
	 f.	 B ⇒ (¬C ⇒ ¬(B ⇒ C))
	 g.	 (B ⇒ C) ⇒ ((¬B ⇒ C) ⇒ C)
Proof
	 a.	 ⊢ ¬¬B ⇒ B
	
1.	 (¬B ⇒ ¬¬B) ⇒ ((¬B ⇒ ¬B) ⇒ B)      Axiom (A3)
	
2.	 ¬B ⇒ ¬B	
Lemma 1.8*
*	 Instead of writing a complete proof of ¬B ⇒ ¬B, we simply cite Lemma 1.8. In this way, we indi-
cate how the proof of ¬¬B ⇒ B could be written if we wished to take the time and space to do so. 
This is, of course, nothing more than the ordinary application of previously proved theorems.



32
Introduction to Mathematical Logic
	
3.	 (¬B ⇒ ¬¬B) ⇒ B	
1, 2, Corollary 1.10(b)
	
4.	 ¬¬B ⇒ (¬B ⇒ ¬¬B)	
Axiom (A1)
	
5.	 ¬¬B ⇒ B	
3, 4, Corollary 1.10(a)
	 b.	 ⊢ B ⇒ ¬¬B
	
1.	 (¬¬¬B ⇒ ¬B) ⇒ ((¬¬¬B ⇒ B) ⇒ ¬¬B)	
Axiom (A3)
	
2.	 ¬¬¬B ⇒ ¬B	
Part (a)
	
3.	 (¬¬¬B ⇒ B) ⇒ ¬¬B	
1, 2, MP
	
4.	 B ⇒ (¬¬¬B ⇒ B)	
Axiom (A1)
	
5.	 B ⇒ ¬¬B	
3, 4, Corollary 1.10(a)
	 c.	 ⊢ ¬B ⇒ (B ⇒ C)
	
1.	 ¬B	
Hyp
	
2.	 B	
Hyp
	
3.	 B ⇒ (¬C ⇒ B)	
Axiom (A1)
	
4.	 ¬B ⇒ (¬C ⇒ ¬B)	
Axiom (A1)
	
5.	 ¬C ⇒ B	
2, 3, MP
	
6.	 ¬C ⇒ ¬B	
1, 4, MP
	
7.	 (¬C ⇒ ¬B) ⇒ ((¬C ⇒ B) ⇒ C)	
Axiom (A3)
	
8.	 (¬C ⇒ B) ⇒ C	
6, 7, MP
	
9.	 C	
5, 8, MP
	
10.	 ¬B, B ⊢ C	
1–9
	
11.	 ¬B ⊢ B ⇒ C	
10, deduction theorem
	
12.	 ⊢ ¬B ⇒ (B ⇒ C)	
11, deduction theorem
	 d.	 ⊢ (¬C ⇒ ¬B) ⇒ (B ⇒ C)
	
1.	 ¬C ⇒ ¬B	
Hyp
	
2.	 (¬C ⇒ ¬B) ⇒ ((¬C ⇒ B) ⇒ C)	
Axiom (A3)
	
3.	 B ⇒ (¬C ⇒ B)	
Axiom (A1)
	
4.	 (¬C ⇒ B) ⇒ C	
1, 2, MP
	
5.	 B ⇒ C	
3, 4, Corollary 1.10(a)
	
6.	 ¬C ⇒ ¬B ⊢ B ⇒ C	
1–5
	
7.	 ⊢ (¬C ⇒ ¬B) ⇒ (B ⇒ C)	
6, deduction theorem
	 e.	 ⊢ (B ⇒ C) ⇒ (¬C ⇒ ¬B)
	
1.	 B ⇒ C	
Hyp
	
2.	 ¬¬B ⇒ B	
Part (a)
	
3.	 ¬¬B ⇒ C	
1, 2, Corollary 1.10(a)
	
4.	 C ⇒ ¬¬C	
Part (b)



33
The Propositional Calculus
	
5.	 ¬¬B ⇒ ¬¬C	
3, 4, Corollary 1.10(a)
	
6.	 (¬¬B ⇒ ¬¬C) ⇒ (¬C ⇒ ¬B)	
Part (d)
	
7.	 ¬C ⇒ ¬B	
5, 6, MP
	
8.	 B ⇒ C ⊢ ¬C ⇒ ¬B	
1–7
	
9.	 ⊢ (B ⇒ C) ⇒ (¬C ⇒ ¬B)	
8, deduction theorem
	 f.	 ⊢ B ⇒ (¬C ⇒ ¬(B ⇒ C))
	
	 Clearly, B, B ⇒ C⊢C by MP. Hence, ⊢B ⇒ ((B ⇒ C) ⇒ C)) by two uses of 
the deduction theorem. Now, by (e), ⊢((B ⇒ C) ⇒ C) ⇒ (¬C ⇒ ¬(B ⇒ C)). 
Hence, by Corollary 1.10(a), ⊢B ⇒ (¬C ⇒ ¬(B ⇒ C)).
	 g.	 ⊢ (B ⇒ C) ⇒ ((¬B ⇒ C) ⇒ C)
	
1.	 B ⇒ C	
Hyp
	
2.	 ¬B ⇒ C	
Hyp
	
3.	 (B ⇒ C) ⇒ (¬C ⇒ ¬B)	
Part (e)
	
4.	 ¬C ⇒ ¬B	
1, 3, MP
	
5.	 (¬B ⇒ C) ⇒ (¬C ⇒ ¬¬B)	
Part (e)
	
6.	 ¬C ⇒ ¬¬B	
2, 5, MP
	
7.	 (¬C ⇒ ¬¬B) ⇒ ((¬C ⇒ ¬B) ⇒ C)	
Axiom (A3)
	
8.	 (¬C ⇒ ¬B) ⇒ C	
6, 7, MP
	
9.	 C	
4, 8, MP
	
10.	 B ⇒ C, ¬B ⇒ C ⊢ C	
1–9
	
11.	 B ⇒ C ⊢ (¬B ⇒ C) ⇒ C	
10, deduction theorem
	
12.	 ⊢(B ⇒ C) ⇒ ((¬B ⇒ C) ⇒ C)	
11, deduction theorem
Exercises
1.48	 Show that the following wfs are theorems of L.
	
a.	 B ⇒ (B ∨ C)
	
b.	 B ⇒ (C ∨ B)
	
c.	 C ∨ B ⇒ B ∨ C
	
d.	 B ∧ C ⇒ B
	
e.	 B ∧ C ⇒ C
	
f.	 (B ⇒ D) ⇒ ((C ⇒ D) ⇒ (B ∨ C ⇒ D))
	
g.	 ((B ⇒ C) ⇒ B) ⇒ B
	
h.	 B ⇒ (C ⇒ (B ∧ C))
1.49	 Exhibit a complete proof in L of Lemma 1.11(c). [Hint: Apply the proce-
dure used in the proof of the deduction theorem to the demonstration 



34
Introduction to Mathematical Logic
given earlier of Lemma 1.11(c).] Greater fondness for the deduction the-
orem will result if the reader tries to prove all of Lemma 1.11 without 
using the deduction theorem.
It is our purpose to show that a wf of L is a theorem of L if and only if it is 
a tautology. Half of this is very easy.
Proposition 1.12
Every theorem of L is a tautology.
Proof
As an exercise, verify that all the axioms of L are tautologies. By Proposition 
1.2, modus ponens leads from tautologies to other tautologies. Hence, every 
theorem of L is a tautology.
The following lemma is to be used in the proof that every tautology is a 
theorem of L.
Lemma 1.13
Let B be a wf and let B1, …, Bk be the statement letters that occur in B. For 
a given assignment of truth values to B1, …, Bk, let Bj′ be Bj if Bj takes the 
value T; and let Bj′ be ¬Bj if Bj takes the value F. Let B ′ be B if B takes the 
value T under the assignment, and let B ′ be ¬B if B takes the value F. Then 
B
Bk
1′ …
′
′
,
,
⊢B .
For example, let B be ¬(¬A2 ⇒ A5). Then for each row of the truth table
	
A
A
A
A
2
5
2
5
¬ ¬
⇒
(
)
T
T
F
F
T
F
T
F
F
F
F
T
Lemma 1.13 asserts a corresponding deducibility relation. For instance, cor-
responding to the third row there is A2, ¬A5 ⊢ ¬¬(¬A2 ⇒ A5), and to the fourth 
row, ¬A2, ¬A5 ⊢ ¬(¬A2 ⇒ A5).
Proof
The proof is by induction on the number n of occurrences of ¬ and ⇒ in B. 
(We assume B written without abbreviations.) If n = 0, B is just a statement 



35
The Propositional Calculus
letter B1, and then the lemma reduces to B1 ⊢ B1 and ¬B1 ⊢ ¬B1. Assume now 
that the lemma holds for all j < n.
Case 1: B is ¬C. Then C  has fewer than n occurrences of ¬ and ⇒.
Subcase 1a: Let C take the value T under the given truth value assignment. 
Then B takes the value F. So, C ′ is C and B ′ is ¬B. By the inductive hypoth-
esis applied to C, we have B
Bk
1′ …
′
,
,
⊢C . Then, by Lemma 1.11(b) and MP, 
B
Bk
1′ …
′
,
,
⊢¬¬C . But ¬¬C is B ′.
Subcase 1b: Let C take the value F. Then B takes the value T. So, C ′ is ¬C and B ′ 
is B, By inductive hypothesis, B
Bk
1′ …
′
,
,
⊢¬C . But ¬C is B ′.
Case 2: B is C ⇒ D. Then C and D have fewer occurrences of ¬ and ⇒ than B. 
So, by inductive hypothesis, B
Bk
1′ …
′
′
,
,
⊢¬C  and B
Bk
1′ …
′
′
,
,
⊢¬D .
Subcase 2a: C takes the value F. Then B takes the value T. So, C ′ is ¬ C and B ′ 
is B. Hence, B
Bk
1′ …
′
,
,
⊢¬C . By Lemma 1.11(c) and MP, B
Bk
1′ …
′
⇒
,
,
⊢C
D . 
But C ⇒ D is B ′.
Subcase 2b: D takes the value T. Then B takes the value T. So, D ′ is D and B ′ 
is B. Hence, B
Bk
1′ …
′
,
,
⊢D . Then, by axiom (A1) and MP, B
Bk
1′ …
′
⇒
,
,
.
⊢C
D  
But C ⇒ D is B ′.
Subcase 2c: C takes the value T and D takes the value F. Then B takes the value F. 
So, C ′ is C, D ′ is ¬D, and B ′ is ¬B. Therefore, B
Bk
1′ …
′
,
,
⊢C  and B
Bk
1′ …
′
,
,
⊢¬D. 
Hence, by Lemma 1.11(f) and MP, B
Bk
1′ …
′
⇒
(
)
,
,
⊢¬ C
D . But ¬(C ⇒ D) is B ′.
Proposition 1.14 (Completeness Theorem)
If a wf B of L is a tautology, then it is a theorem of L.
Proof
(Kalmár, 1935) Assume B is a tautology, and let B1, …, Bk be the statement 
letters in B. For any truth value assignment to B1, …, Bk, we have, by Lemma 
1.13, B
Bk
1′ …
′
,
,
⊢B . (B ′ is B because B always takes the value T.) Hence, when 
Bk′ is given the value T, we obtain B
Bk
1
1
′ …
′−
,
,
, Bk ⊢ B, and, when Bk is given 
the value F, we obtain B
Bk
1
1
′ …
′−
,
,
, ¬Bk ⊢ B. So, by the deduction theorem, 
B
Bk
1
1
′ …
′−
,
,
 ⊢ Bk ⇒ B and B
Bk
1
1
′ …
′−
,
,
, ⊢ ¬Bk ⇒ B. Then by Lemma 1.11(g) and 
MP, B
Bk
1
1
′ …
′−
,
,
 ⊢ B. Similarly, Bk−1 may be chosen to be T or F and, again 
applying the deduction theorem, Lemma 1.11(g) and MP, we can eliminate 
Bk−′ 1 just as we eliminated Bk′. After k such steps, we finally obtain ⊢B.
Corollary 1.15
If C  is an expression involving the signs ¬, ⇒, ∧, ∨, and ⇔ that is an abbrevia-
tion for a wf B of L, then C is a tautology if and only if B is a theorem of L.



36
Introduction to Mathematical Logic
Proof
In definitions (D1)–(D3), the abbreviating formulas replace wfs to which 
they are logically equivalent. Hence, by Proposition 1.4, B and C are logically 
equivalent, and C is a tautology if and only if B is a tautology. The corollary 
now follows from Propositions 1.12 and 1.14.
Corollary 1.16
The system L is consistent; that is, there is no wf B such that both B and ¬B 
are theorems of L.
Proof
By Proposition 1.12, every theorem of L is a tautology. The negation of a 
tautology cannot be a tautology and, therefore, it is impossible for both B 
and ¬B to be theorems of L.
Notice that L is consistent if and only if not all wfs of L are theorems. In fact, 
if L is consistent, then there are wfs that are not theorems (e.g., the negations of 
theorems). On the other hand, by Lemma 1.11(c), ⊢ L ¬B ⇒ (B ⇒ C), and so, if L 
were inconsistent, that is, if some wf B and its negation ¬B were provable, then 
by MP any wf C  would be provable. (This equivalence holds for any theory that 
has modus ponens as a rule of inference and in which Lemma 1.11(c) is provable.) 
A theory in which not all wfs are theorems is said to be absolutely consistent, and 
this definition is applicable even to theories that do not contain a negation sign.
Exercise
1.50	 Let B be a statement form that is not a tautology. Let L+ be the formal 
theory obtained from L by adding as new axioms all wfs obtainable 
from B by substituting arbitrary statement forms for the statement let-
ters in B, with the same form being substituted for all occurrences of a 
statement letter. Show that L+ is inconsistent.
1.5  Independence: Many-Valued Logics
A subset Y of the set of axioms of a theory is said to be independent if some 
wf in Y cannot be proved by means of the rules of inference from the set of 
those axioms not in Y.
Proposition 1.17
Each of the axiom schemas (A1)–(A3) is independent.



37
The Propositional Calculus
Proof
To prove the independence of axiom schema (A1), consider the following 
tables:
	
A
A
A
B
A
B
¬
⇒
0
1
0
0
0
1
1
1
0
2
2
0
2
0
0
0
1
2
1
1
2
2
1
0
0
2
2
1
2
0
2
2
0
For any assignment of the values 0, 1, and 2 to the statement letters of a wf 
B, these tables determine a corresponding value of B. If B always takes the 
value 0, B is called select. Modus ponens preserves selectness, since it is easy 
to check that, if B and B ⇒ C are select, so is C. One can also verify that all 
instances of axiom schemas (A2) and (A3) are select. Hence, any wf deriv-
able from (A2) and (A3) by modus ponens is select. However, A1 ⇒ (A2 ⇒ A1), 
which is an instance of (A1), is not select, since it takes the value 2 when A1 
is 1 and A2 is 2.
To prove the independence of axiom schema (A2), consider the following 
tables:
	
A
A
A
B
A
B
¬
⇒
0
1
0
0
0
1
0
1
0
0
2
1
2
0
0
0
1
2
1
1
2
2
1
0
0
2
1
1
2
0
2
2
0
Let us call a wf that always takes the value 0 according to these tables 
­grotesque. Modus ponens preserves grotesqueness and it is easy to verify 



38
Introduction to Mathematical Logic
that all instances of (A1) and (A3) are grotesque. However, the instance 
(A1 ⇒ (A2 ⇒ A3)) ⇒ ((A1 ⇒ A2) ⇒ (A1 ⇒ A3)) of (A2) takes the value 2 when A1 
is 0, A2 is 0, and A3 is 1 and, therefore, is not grotesque.
The following argument proves the independence of (A3). Let us call a wf 
B super if the wf h(B ) obtained by erasing all negation signs in B is a tautol-
ogy. Each instance of axiom schemas (A1) and (A2) is super. Also, modus 
ponens preserves the property of being super; for if h(B ⇒ C) and h(B) are 
tautologies, then h(C ) is a tautology. (Just note that h(B ⇒ C) is h(B) ⇒ h(C) 
and use Proposition 1.2.) Hence, every wf B derivable from (A1) and (A2) by 
modus ponens is super. But h((¬A1 ⇒ ¬A1) ⇒ ((¬A1 ⇒ A1) ⇒ A1)) is (A1 ⇒ A1) ⇒ 
((A1 ⇒ A1) ⇒ A1), which is not a tautology. Therefore, (¬A1 ⇒ ¬A1) ⇒ ((¬A1 ⇒ 
A1) ⇒ A1), an instance of (A3), is not super and is thereby not derivable from 
(A1) and (A2) by modus ponens.
The idea used in the proof of the independence of axiom schemas (A1) 
and (A2) may be generalized to the notion of a many-valued logic. Select a 
positive integer n, call the numbers 0, 1, …, n truth values, and choose a num-
ber m such that 0 ≤ m < n. The numbers 0, 1, …, m are called designated values. 
Take a finite number of “truth tables” representing functions from sets of 
the form {0, 1, …, n}k into {0, 1, …, n}. For each truth table, introduces a sign, 
called the corresponding connective. Using these connectives and state-
ment letters, we may construct “statement forms,” and every such state-
ment form containing j distinct letters determines a “truth function” from 
{0, 1, …, n}j into {0, 1, …, n}. A statement form whose corresponding truth 
function takes only designated values is said to be exceptional. The numbers 
m and n and the basic truth tables are said to define a (finite) many-valued 
logic M. A formal theory involving statement letters and the connectives of 
M is said to be suitable for M if and only if the theorems of the theory coin-
cide with the exceptional statement forms of M. All these notions obviously 
can be generalized to the case of an infinite number of truth values. If n = 1 
and m = 0 and the truth tables are those given for ¬ and ⇒ in Section 1.1, 
then the corresponding two-valued logic is that studied in this chapter. The 
exceptional wfs in this case were called tautologies. The system L is suit-
able for this logic, as proved in Propositions 1.12 and 1.14. In the proofs of 
the independence of axiom schemas (A1) and (A2), two three-valued logics 
were used.
Exercises
1.51	 Prove the independence of axiom schema (A3) by constructing appro-
priate “truth tables” for ¬ and ⇒.
1.52	 (McKinsey and Tarski, 1948) Consider the axiomatic theory P in which 
there is exactly one binary connective *, the only rule of inference is 
modus ponens (that is, C follows from B and B * C), and the axioms 
are all wfs of the form B * B. Show that P is not suitable for any (finite) 
many-valued logic.



39
The Propositional Calculus
1.53	 For any (finite) many-valued logic M, prove that there is an axiomatic 
theory suitable for M.
Further information about many-valued logics can be found in Rosser 
and Turquette (1952), Rescher (1969), Bolc and Borowik (1992), and 
Malinowski (1993).
1.6  Other Axiomatizations
Although the axiom system L is quite simple, there are many other systems 
that would do as well. We can use, instead of ¬ and ⇒, any collection of 
primitive connectives as long as these are adequate for the definition of all 
other truth-functional connectives.
Examples
L1: ∨ and ¬ are the primitive connectives. We use B ⇒ C as an abbreviation for 
¬B ∨ C. We have four axiom schemas: (1) B ∨ B ⇒ B; (2) B ⇒ B ∨ C; (3) B ∨ C ⇒ 
C ∨ B; and (4) (C ⇒ D) ⇒ (B ∨ C ⇒ B ∨ D). The only rule of inference is modus 
ponens. Here and below we use the usual rules for eliminating parentheses. 
This system is developed in Hilbert and Ackermann (1950).
L2: ∧ and ¬ are the primitive connectives. B ⇒ C is an abbreviation for 
¬(B ∧ ¬C). There are three axiom schemas: (1) B ⇒ (B ∧ B); (2) B ∧ C ⇒ B; 
and (3) (B ⇒ C) ⇒ (¬(C ∧ D) ⇒ ¬(D ∧ B)). Modus ponens is the only rule of 
inference. Consult Rosser (1953) for a detailed study.
L3: This is just like our original system L except that, instead of the axiom 
schemas (A1)–(A3), we have three specific axioms: (1) A1 ⇒(A2 ⇒ A1); (2) (A1 
⇒(A2 ⇒ A3)) ⇒((A1 ⇒ A2) ⇒(A1 ⇒ A3)); and (3) (¬A2 ⇒ ¬A1) ⇒((¬A2 ⇒ A1) ⇒ A2). 
In addition to modus ponens, we have a substitution rule: we may substitute 
any wf for all occurrences of a statement letter in a given wf.
L4: The primitive connectives are ⇒, ∧, ∨, and ¬. Modus ponens is the only rule, 
and we have 10 axiom schemas: (1) B ⇒ (C ⇒ B); (2) (B ⇒ (C ⇒ D)) ⇒ ((B ⇒ C ) 
⇒ (B ⇒ D)); (3) B ∧ C ⇒ B ; (4) B ∧ C ⇒ C; (5) B ⇒ (C ⇒ (B ∧ C )); (6) B ⇒ (B ∨ C ); 
(7) C ⇒ (B ∨ C ); (8) (B ⇒ D) ⇒ ((C ⇒ D) ⇒ (B ∨ C ⇒ D)); (9) (B ⇒ C ) ⇒ ((B ⇒ ¬C ) 
⇒ ¬B); and (10) ¬¬B ⇒ B. This system is discussed in Kleene (1952).
Axiomatizations can be found for the propositional calculus that contain 
only one axiom schema. For example, if ¬ and ⇒ are the primitive connec-
tives and modus ponens the only rule of inference, then the axiom schema
	
B
D
E
D
F
F
B
E
B
C
⇒
(
) ⇒
⇒
(
)
(
) ⇒
(
) ⇒
⇒
]
[
⇒
(
) ⇒
⇒
(
)




¬
¬



40
Introduction to Mathematical Logic
is sufficient (Meredith, 1953). Another single-axiom formulation, due to 
Nicod (1917), uses only alternative denial |. Its rule of inference is: D follows 
from B |(C |D) and B, and its axiom schema is
	
(
|( |
))|{[ |( | )]|[(
| )|((
|
)|(
|
))]}
B
C
D
E
E E
F
C
B F
B F
Further information, including historical background, may be found 
in Church (1956) and in a paper by Lukasiewicz and Tarski in Tarski 
(1956, IV).
Exercises
1.54	 (Hilbert and Ackermann, 1950) Prove the following results about the 
theory L1.
	
a.	 B ⇒ C ⊢ L1 D ∨ B ⇒ D ∨ C
	
b.	 ⊢ L1 (B ⇒ C) ⇒ ((D ⇒ B) ⇒ (D ⇒ C))
	
c.	 D ⇒ B, B ⇒ C ⊢ L1 D ⇒ C
	
d.	 ⊢ L1 B ⇒ B (i.e., ⊢ L1 ¬B ∨ B)
	
e.	 ⊢ L1 B ∨ ¬B
	
f.	 ⊢ L1 B ⇒ ¬¬B
	
g.	 ⊢ L1 ¬B ⇒ (B ⇒ C)
	
h.	 ⊢ L1 B ∨ (C ∨ D) ⇒ ((C ∨ (B ∨ D)) ∨ B)
	
i.	 ⊢ L1 (C ∨ (B ∨ D)) ∨ B ⇒ C ∨ (B ∨ D)
	
j.	 ⊢ L1 B ∨ (C ∨ D) ⇒ C ∨ (B ∨ D)
	
k.	 ⊢ L1 (B ⇒ (C ⇒ D)) ⇒ (C ⇒ (B ⇒ D))
	
l.	 ⊢ L1 (D ⇒ B) ⇒ ((B ⇒ C) ⇒ (D ⇒ C))
	
m.	 B ⇒ (C ⇒ D), B ⇒ C ⊢ L1 B ⇒ (B ⇒ D)
	
n.	 B ⇒ (C ⇒ D), B ⇒ C ⊢ L1 B ⇒ D
	
o.	 If Γ, B ⊢ L1 C, then Γ ⊢ L1 B ⇒ C (Deduction theorem)
	
p.	 C ⇒ B, ¬C ⇒ B ⊢ L1 B
	
q.	 ⊢ L1 B if and only if B is a tautology.
1.55	 (Rosser, 1953) Prove the following facts about the theory L2.
	
a.	 B ⇒ C, C ⇒ D ⊢ L2 ¬(¬D ∧ B)
	
b.	 ⊢ L2 ¬(¬B ∧ B)
	
c.	 ⊢ L2 ¬¬B ⇒ B
	
d.	 ⊢ L2 ¬(B ∧ C) ⇒ (C ⇒ ¬B)
	
e.	 ⊢ L2 B ⇒ ¬¬B
	
f.	 ⊢ L2 (B ⇒ C) ⇒ (¬C ⇒ ¬B)



41
The Propositional Calculus
	
g.	 ¬B ⇒ ¬C ⊢ L2 C ⇒ B
	
h.	 B ⇒ C ⊢ L2 D ∧ B ⇒ C ∧ D
	
i.	 B ⇒ C, C ⇒ D, D ⇒ E ⊢ L2 B ⇒ E
	
j.	 ⊢ L2 B ⇒ B
	
k.	 ⊢ L2 B ∧ C ⇒ C ∧ B
	
l.	 B ⇒ C, C ⇒ D ⊢ L2 B ⇒ D
	
m.	 B ⇒ C, D ⇒ E ⊢ L2 B ∧ D ⇒ C ∧ E
	
n.	 C ⇒ D ⊢ L2 B ∧ C ⇒ B ∧ D
	
o.	 ⊢ L2 (B ⇒ (C ⇒ D)) ⇒ ((B ∧ C) ⇒ D)
	
p.	 ⊢ L2 ((B ∧ C) ⇒ D) ⇒ (B ⇒ (C ⇒ D))
	
q.	 B ⇒ C, B ⇒ (C ⇒ D) ⊢ L2 B ⇒ D
	
r.	 ⊢ L2 B ⇒ (C ⇒ B ∧ C)
	
s.	 ⊢ L2 B ⇒ (C ⇒ B)
	
t.	 If Γ, B ⊢ L2 C, then Γ ⊢ L2 B ⇒ C (Deduction theorem)
	
u.	 ⊢ L2 (¬B ⇒ B) ⇒ B
	
v.	 B ⇒ C, ¬B ⇒ C ⊢ L2 C
	
w.	 ⊢ L2 B if and only if B is a tautology.
1.56	 Show that the theory L3 has the same theorems as the theory L.
1.57	 (Kleene, 1952) Derive the following facts about the theory L4.
	
a.	 ⊢ L4 B ⇒ B
	
b.	 If Γ, B ⊢ L4 C, then Γ ⊢ L4 B ⇒ C (deduction theorem)
	
c.	 B ⇒ C, C ⇒ D ⊢ L4 B ⇒ D
	
d.	 ⊢ L4 (B ⇒ C) ⇒ (¬C ⇒ ¬B)
	
e.	 B, ¬B ⊢ L4 C
	
f.	 ⊢ L4 B ⇒ ¬¬B
	
g.	 ⊢ L4 ¬B ⇒ (B ⇒ C)
	
h.	 ⊢ L4 B ⇒ (¬C ⇒ ¬(B ⇒ C))
	
i.	 ⊢ L4 ¬B ⇒ (¬C ⇒ ¬(B ∨ C))
	
j.	 ⊢ L4 (¬C ⇒ B) ⇒ ((C ⇒ B) ⇒ B)
	
k.	 ⊢ L4 B if and only if B is a tautology.
1.58D	Consider the following axiomatization of the propositional calculus L 
(due to Lukasiewicz). L  has the same wfs as our system L. Its only rule 
of inference is modus ponens. Its axiom schemas are:
	
a.	 (¬B ⇒ B) ⇒ B
	
b.	 B ⇒ (¬B ⇒ C)
	
c.	 (B ⇒ C) ⇒ ((C ⇒ D) ⇒ (B ⇒ D))



42
Introduction to Mathematical Logic
	
Prove that a wf B of L  is provable in L  if and only if B is a tautology. 
[Hint: Show that L and L  have the same theorems. However, remember 
that none of the results proved about L (such as Propositions 1.8–1.13) 
automatically carries over to L . In particular, the deduction theorem is 
not available until it is proved for L .]
1.59	 Show that axiom schema (A3) of L can be replaced by the schema 
(¬B ⇒ ¬C) ⇒ (C ⇒ B ) without altering the class of theorems.
1.60	 If axiom schema (10) of L4 is replaced by the schema (10)′: ¬B ⇒ (B ⇒ C), 
then the new system LI is called the intuitionistic propositional calcu-
lus.* Prove the following results about LI.
	
a.	 Consider an (n + 1)-valued logic with these connectives: ¬B is 0 
when B is n, and otherwise it is n; B ∧ C has the maximum of the 
values of B and C, whereas B  ∨ C has the minimum of these values; 
and B ⇒ C is 0 if B has a value not less than that of C, and otherwise 
it has the same value as C. If we take 0 as the only designated value, 
all theorems of LI are exceptional.
	
b.	 A1 ∨ ¬A1 and ¬ ¬A1 ⇒ A1 are not theorems of LI.
	
c.	 For any m, the wf
	
A
A
A
A
A
A
A
A
A
A
m
m
m
m
1
2
1
2
3
2
1
⇔
(
)∨… ∨
⇔
(
)∨
⇔
(
)∨…
∨
⇔
(
)∨… ∨
⇔
(
)
−
	
	
is not a theorem of LI
	
d.	 (Gödel, 1933) LI is not suitable for any finite many-valued logic.
	
e.	
i.	 If Γ, B ⊢ LI C, then Γ ⊢ LI B ⇒ C (deduction theorem)
	
ii.	 B ⇒ C, C ⇒ D ⊢ LI B ⇒ D
	
iii.	 ⊢ LI B ⇒ ¬¬B
	
iv.	 ⊢ LI (B ⇒ C) ⇒ (¬C ⇒ ¬B)
	
v.	 ⊢ LI B ⇒ (¬B ⇒ C)
	
vi.	 ⊢ LI ¬¬(¬¬B ⇒ B)
	
vii.	 ¬¬(B ⇒ C), ¬¬B ⊢ LI ¬¬C
	
viii.	 ⊢ LI ¬¬¬B ⇒ ¬B
	
fD.	 ⊢LI ¬¬B if and only if B is a tautology.
*	 The principal origin of intuitionistic logic was L.E.J. Brouwer’s belief that classical logic is 
wrong. According to Brouwer, B ∨ C is proved only when a proof of B or a proof of C has 
been found. As a consequence, various tautologies, such as B ∨ ¬B, are not generally accept-
able. For further information, consult Brouwer (1976), Heyting (1956), Kleene (1952), Troelstra 
(1969), and Dummett (1977). Jaśkowski (1936) showed that LI is suitable for a many-valued 
logic with denumerably many values.



43
The Propositional Calculus
	
g.	 ⊢ LI ¬B if and only if ¬B is a tautology.
	
h.D	 If B  has ∨ and ¬ as its only connectives, then ⊢ LI B if and only if B 
is a tautology.
1.61A	Let B and C be in the relation R if and only if ⊢ L B ⇔ C. Show that R is 
an equivalence relation. Given equivalence classes [B ] and [C], let [B] ∪ 
[C ] = [B ∨ C], [B] ∩ [C] = [B ∧ C], and [B ] = [¬B]. Show that the equiva-
lence classes under R form a Boolean algebra with respect to ∩, ∪, and −, 
called the Lindenbaum algebra L* determined by L. The element 0 of L* is 
the equivalence class consisting of all contradictions (i.e., negations of 
tautologies). The unit element 1 of L* is the equivalence class consisting 
of all tautologies. Notice that ⊢ L B ⇒ C if and only if [B] ≤ [C] in L*, and 
that ⊢ L B ⇔ C if and only if [B] = [C]. Show that a Boolean function f 
(built up from variables, 0, and 1, using ∪, ∩, and −) is equal to the con-
stant function 1 in all Boolean algebras if and only if ⊢L  f #, where f # is 
obtained from f by changing ∪, ∩, −, 0, and 1 to ∨, ∧, ¬, A1 ∧ ¬A1, and 
A1 ∨ ¬A1, respectively.


