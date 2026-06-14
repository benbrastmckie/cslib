<!-- Source: Mendelson, E. (2016). Introduction to Mathematical Logic (6th ed). Front matter including Contents, Preface, and Introduction. BibKey: not yet in references.bib -->


TEXTBOOKS in MATHEMATICS
I N T R O D U C T I O N  T O 
MATHEMATICAL LOGIC
Elliott Mendelson
SIXTH EDITION



I N T R O D U C T I O N  T O 
MATHEMATICAL LOGIC
SIXTH EDITION



TEXTBOOKS in MATHEMATICS
Series Editors: Al Boggess and Ken Rosen
PUBLISHED TITLES
ABSTRACT ALGEBRA: AN INQUIRY-BASED APPROACH
Jonathan K. Hodge, Steven Schlicker, and Ted Sundstrom
ABSTRACT ALGEBRA: AN INTERACTIVE APPROACH
William Paulsen
ADVANCED CALCULUS: THEORY AND PRACTICE
John Srdjan Petrovic
ADVANCED LINEAR ALGEBRA
Nicholas Loehr
ANALYSIS WITH ULTRASMALL NUMBERS
Karel Hrbacek, Olivier Lessmann, and Richard O’Donovan
APPLIED DIFFERENTIAL EQUATIONS: THE PRIMARY COURSE
Vladimir Dobrushkin
APPLYING ANALYTICS: A PRACTICAL APPROACH
Evan S. Levine
COMPUTATIONS OF IMPROPER REIMANN INTEGRALS
Ioannis Roussos 
CONVEX ANALYSIS
Steven G. Krantz
COUNTEREXAMPLES: FROM ELEMENTARY CALCULUS TO THE BEGINNINGS OF ANALYSIS
Andrei Bourchtein and Ludmila Bourchtein
DIFFERENTIAL EQUATIONS: THEORY, TECHNIQUE, AND PRACTICE, SECOND EDITION
Steven G. Krantz
DIFFERENTIAL EQUATIONS WITH MATLAB®: EXPLORATION, APPLICATIONS, AND THEORY
Mark A. McKibben and Micah D. Webster
ELEMENTARY NUMBER THEORY 
James S. Kraft and Lawrence C. Washington
ELEMENTS OF ADVANCED MATHEMATICS, THIRD EDITION
Steven G. Krantz



EXPLORING LINEAR ALGEBRA: LABS AND PROJECTS WITH MATHEMATICA® 
Crista Arangala
AN INTRODUCTION TO NUMBER THEORY WITH CRYPTOGRAPHY
James Kraft and Larry Washington
AN INTRODUCTION TO PARTIAL DIFFERENTIAL EQUATIONS WITH MATLAB®, SECOND EDITION
Mathew Coleman
INTRODUCTION TO THE CALCULUS OF VARIATIONS AND CONTROL WITH MODERN APPLICATIONS
John T. Burns
INTRODUCTION TO MATHEMATICAL LOGIC, SIXTH EDITION
Elliott Mendelson
INTRODUCTION TO MATHEMATICAL PROOFS: A TRANSITION TO ADVANCED MATHEMATICS, SECOND EDITION
Charles E. Roberts, Jr.
LINEAR ALGEBRA, GEOMETRY AND TRANSFORMATION 
Bruce Solomon 
THE MATHEMATICS OF GAMES: AN INTRODUCTION TO PROBABILITY
David G. Taylor
QUADRACTIC IRRATIONALS: AN INTRODUCTION TO CLASSICAL NUMBER THEORY
Franz Holter-Koch
REAL ANALYSIS AND FOUNDATIONS, THIRD EDITION
Steven G. Krantz 
RISK ANALYSIS IN ENGINEERING AND ECONOMICS, SECOND EDITION
Bilal M. Ayyub
RISK MANAGEMENT AND SIMULATION
Aparna Gupta
TRANSFORMATIONAL PLANE GEOMETRY 
Ronald N. Umble and Zhigang Han
PUBLISHED TITLES CONTINUED



TEXTBOOKS in MATHEMATICS
I N T R O D U C T I O N  T O 
MATHEMATICAL LOGIC
Elliott Mendelson
Queens College
Flushing, New York, USA
SIXTH EDITION



CRC Press
Taylor & Francis Group
6000 Broken Sound Parkway NW, Suite 300
Boca Raton, FL 33487-2742
© 2015 by Taylor & Francis Group, LLC
CRC Press is an imprint of Taylor & Francis Group, an Informa business
No claim to original U.S. Government works
Version Date: 20150205
International Standard Book Number-13: 978-1-4822-3778-8 (eBook - PDF)
This book contains information obtained from authentic and highly regarded sources. Reasonable efforts 
have been made to publish reliable data and information, but the author and publisher cannot assume 
responsibility for the validity of all materials or the consequences of their use. The authors and publishers 
have attempted to trace the copyright holders of all material reproduced in this publication and apologize to 
copyright holders if permission to publish in this form has not been obtained. If any copyright material has 
not been acknowledged please write and let us know so we may rectify in any future reprint.
Except as permitted under U.S. Copyright Law, no part of this book may be reprinted, reproduced, transmit-
ted, or utilized in any form by any electronic, mechanical, or other means, now known or hereafter invented, 
including photocopying, microfilming, and recording, or in any information storage or retrieval system, 
without written permission from the publishers.
For permission to photocopy or use material electronically from this work, please access www.copyright.
com (http://www.copyright.com/) or contact the Copyright Clearance Center, Inc. (CCC), 222 Rosewood 
Drive, Danvers, MA 01923, 978-750-8400. CCC is a not-for-profit organization that provides licenses and 
registration for a variety of users. For organizations that have been granted a photocopy license by the CCC, 
a separate system of payment has been arranged.
Trademark Notice: Product or corporate names may be trademarks or registered trademarks, and are used 
only for identification and explanation without intent to infringe.
Visit the Taylor & Francis Web site at
http://www.taylorandfrancis.com
and the CRC Press Web site at
http://www.crcpress.com



To Arlene



ix
Contents
Preface................................................................................................................... xiii
Introduction............................................................................................................xv
 1. The Propositional Calculus...........................................................................1
1.1	
Propositional Connectives: Truth Tables............................................1
1.2	
Tautologies..............................................................................................6
1.3	
Adequate Sets of Connectives............................................................19
1.4	
An Axiom System for the Propositional Calculus..........................27
1.5	
Independence: Many-Valued Logics.................................................36
1.6	
Other Axiomatizations.......................................................................39
 2. First-Order Logic and Model Theory........................................................45
2.1	
Quantifiers............................................................................................45
2.1.1	
Parentheses..............................................................................48
2.2	
First-Order Languages and Their Interpretations: 
Satisfiability and Truth: Models........................................................53
2.3	
First-Order Theories............................................................................66
2.3.1	
Logical Axioms.......................................................................66
2.3.2	
Proper Axioms........................................................................67
2.3.3	
Rules of Inference...................................................................67
2.4	
Properties of First-Order Theories....................................................69
2.5	
Additional Metatheorems and Derived Rules................................73
2.5.1	
Particularization Rule A4...................................................... 74
2.5.2	
Existential Rule E4.................................................................. 74
2.6	
Rule C....................................................................................................78
2.7	
Completeness Theorems.....................................................................82
2.8	
First-Order Theories with Equality...................................................93
2.9	
Definitions of New Function Letters and Individual 
Constants........................................................................................ 102
2.10	 Prenex Normal Forms....................................................................... 105
2.11	 Isomorphism of Interpretations: Categoricity of Theories.......... 111
2.12	 Generalized First-Order Theories: Completeness and 
Decidability........................................................................................ 113
2.12.1	 Mathematical Applications................................................. 117
2.13	 Elementary Equivalence: Elementary Extensions........................123
2.14	 Ultrapowers: Nonstandard Analysis..............................................128
2.14.1	 Reduced Direct Products..................................................... 131
2.14.2	 Nonstandard Analysis.........................................................136



x
Contents
2.15	 Semantic Trees................................................................................... 140
2.15.1	 Basic Principle of Semantic Trees....................................... 142
2.16	 Quantification Theory Allowing Empty Domains....................... 146
 3. Formal Number Theory.............................................................................153
3.1	
An Axiom System..............................................................................153
3.2	
Number-Theoretic Functions and Relations.................................. 169
3.3	
Primitive Recursive and Recursive Functions.............................. 174
3.4	
Arithmetization: Gödel Numbers................................................... 192
3.5	
The Fixed-Point Theorem: Gödel’s Incompleteness Theorem.....205
3.6	
Recursive Undecidability: Church’s Theorem............................... 218
3.7	
Nonstandard Models........................................................................228
 4. Axiomatic Set Theory.................................................................................231
4.1	
An Axiom System..............................................................................231
4.2	
Ordinal Numbers..............................................................................247
4.3	
Equinumerosity: Finite and Denumerable Sets............................260
4.3.1	
Finite Sets...............................................................................265
4.4	
Hartogs’ Theorem: Initial Ordinals—Ordinal Arithmetic.........270
4.5	
The Axiom of Choice: The Axiom of Regularity..........................282
4.6	
Other Axiomatizations of Set Theory.............................................293
4.6.1	
Morse–Kelley (MK)..............................................................293
4.6.2	
Zermelo–Fraenkel (ZF)........................................................294
4.6.3	
The Theory of Types (ST)....................................................296
4.6.3.1	
ST1 (Extensionality Axiom).................................297
4.6.3.2	
ST2 (Comprehension Axiom Scheme)................297
4.6.3.3	
ST3 (Axiom of Infinity).........................................298
4.6.4	
Quine’s Theories NF and ML.............................................300
4.6.4.1	
NF1 (Extensionality).............................................300
4.6.4.2	
NF2 (Comprehension)..........................................301
4.6.5	
Set Theory with Urelements...............................................303
 5. Computability.............................................................................................. 311
5.1	
Algorithms: Turing Machines.......................................................... 311
5.2	
Diagrams............................................................................................. 317
5.3	
Partial Recursive Functions: Unsolvable Problems......................325
5.4	
The Kleene–Mostowski Hierarchy: Recursively 
Enumerable Sets.................................................................................341
5.5	
Other Notions of Computability.....................................................355
5.5.1	
Herbrand–Gödel Computability........................................355
5.5.2	
Markov Algorithms..............................................................362
5.6	
Decision Problems.............................................................................373



xi
Contents
Appendix A: Second-Order Logic...................................................................379
Appendix B: First Steps in Modal Propositional Logic..............................395
Appendix C: A Consistency Proof for Formal Number Theory...............407
Answers to Selected Exercises......................................................................... 419
Bibliography........................................................................................................451
Notations..............................................................................................................467
Index......................................................................................................................473



xiii
Preface
This book is a compact introduction to many of the important topics of 
mathematical logic, comprising natural and unrestricted set-theoretic 
methods. Here is a very brief sketch of some of its contents:
	
1.	One of the most prominent features of this new edition is a con-
sistency proof for formal number theory due to Kurt Schütte. This 
proof had been included in the first edition in 1964. It was dropped 
in later editions and is now brought back by “popular demand.” 
Quite a few people thought I had made a mistake in abandoning it. 
	
2.	There is now a greatly enlarged bibliography, with items that should 
be interesting to a wide audience. Many of them have to do with 
the philosophical significance of some important results of modern 
mathematical logic.
As before, the material in this book can be covered in two semesters, 
but Chapters 1 through 3 are quite adequate for a one-semester course. 
Bibliographic references are aimed at giving the best source of information, 
which is not always the earliest; hence, these references give no indication of 
priority.
I believe that the essential parts of the book can be read with ease by any-
one with some experience in abstract mathematical thinking. There is, how-
ever, no specific prerequisite.
This book owes an obvious debt to the standard works of Hilbert and 
Bernays (1934, 1939), Kleene (1952), Rosser (1953), and Church (1956). I am also 
grateful to many people for their help, including my editor Jessica Vakili, as 
well as the editors of the earlier editions.



xv
Introduction
One of the popular definitions of logic is that it is the analysis of methods of 
reasoning. In studying these methods, logic is interested in the form rather 
than the content of the argument. For example, consider these two arguments:
	
1.	All men are mortal. Socrates is a man. Hence, Socrates is mortal.
	
2.	All cats like fish. Silvy is a cat. Hence, Silvy likes fish.
Both have the same form: All A are B. S is an A. Hence, S is a B. The truth or 
falsity of the particular premises and conclusions is of no concern to logi-
cians. They want to know only whether the premises imply the conclusion. 
The systematic formalization and cataloguing of valid methods of reasoning 
are a main task of logicians. If the work uses mathematical techniques or if it 
is primarily devoted to the study of mathematical reasoning, then it may be 
called mathematical logic. We can narrow the domain of mathematical logic if 
we define its principal aim to be a precise and adequate understanding of the 
notion of mathematical proof.
Impeccable definitions have little value at the beginning of the study of a 
subject. The best way to find out what mathematical logic is about is to start 
doing it, and students are advised to begin reading the book even though 
(or especially if) they have qualms about the meaning and purpose of the 
subject.
Although logic is basic to all other studies, its fundamental and apparently 
self-evident character discouraged any deep logical investigations until the 
late nineteenth century. Then, under the impetus of the discovery of non-
Euclidean geometry and the desire to provide a rigorous foundation for 
calculus and higher analysis, interest in logic was revived. This new inter-
est, however, was still rather unenthusiastic until, around the turn of the 
century, the mathematical world was shocked by the discovery of the para-
doxes—that is, arguments that lead to contradictions. The most important 
paradoxes are described here.
	
1.	Russell’s paradox (1902): By a set, we mean any collection of objects—
for example, the set of all even integers or the set of all saxophone 
players in Brooklyn. The objects that make up a set are called its 
members or elements. Sets may themselves be members of sets; for 
example, the set of all sets of integers has sets as its members. Most 
sets are not members of themselves; the set of cats, for example, is not 
a member of itself because the set of cats is not a cat. However, there 
may be sets that do belong to themselves—perhaps, for example, 



xvi
Introduction
a set containing all sets. Now, consider the set A of all those sets X 
such that X is not a member of X. Clearly, by definition, A is a mem-
ber of A if and only if A is not a member of A. So, if A is a member of 
A, then A is also not a member of A; and if A is not a member of A, 
then A is a member of A. In any case, A is a member of A and A is not 
a member of A (see Link, 2004).
	
2.	Cantor’s paradox (1899): This paradox involves the theory of cardinal 
numbers and may be skipped by those readers having no previous 
acquaintance with that theory. The cardinal number Y of a set Y is a 
measure of the size of the set; Y
Z
=
 if and only if Y is equinumerous 
with Z (i.e., there is a one–one correspondence between Y and Z). 
We define Y
Z

 to mean that Y is equinumerous with a subset of 
Z; by Y
Z
<
 we mean Y Z
  and Y
Z
≠
. Cantor proved that if P (Y) 
is the set of all subsets of Y, then Y
Y
< P ( ). Let V be the universal 
set—that is, the set of all sets. Now, P (V) is a subset of V; so it fol-
lows easily that P ( )
V
V

. On the other hand, by Cantor’s theorem, 
V
V
< P ( ). Bernstein’s theorem asserts that if Y
Z
  and Z
Y
 , then 
Y
Z
=
. Hence, V
V
= P ( ), contradicting V
V
< P ( ).
	
3.	Burali-Forti’s paradox (1897): This paradox is the analogue in the the-
ory of ordinal numbers of Cantor’s paradox and requires familiarity 
with ordinal number theory. Given any ordinal number, there is still 
a larger ordinal number. But the ordinal number determined by the 
set of all ordinal numbers is the largest ordinal number.
	
4.	The liar paradox: A man says, “I am lying.” If he is lying, then what he 
says is true and so he is not lying. If he is not lying, then what he says 
is true, and so he is lying. In any case, he is lying and he is not lying.*
	
5.	Richard’s paradox (1905): Some phrases of the English language denote 
real numbers; for example, “the ratio between the circumference and 
diameter of a circle” denotes the number π. All the phrases of the 
English language can be enumerated in a standard way: order all 
phrases that have k letters lexicographically (as in a dictionary) and 
then place all phrases with k letters before all phrases with a larger 
number of letters. Hence, all phrases of the English language that 
denote real numbers can be enumerated merely by omitting all other 
phrases in the given standard enumeration. Call the nth real number 
in this enumeration the nth Richard number. Consider the phrase: 
“the real number whose nth decimal place is 1 if the nth decimal 
*	 The Cretan “paradox,” known in antiquity, is similar to the liar paradox. The Cretan philoso-
pher Epimenides said, “All Cretans are liars.” If what he said is true, then, since Epimenides 
is a Cretan, it must be false. Hence, what he said is false. Thus, there must be some Cretan 
who is not a liar. This is not logically impossible; so we do not have a genuine paradox. 
However, the fact that the utterance by Epimenides of that false sentence could imply the 
existence of some Cretan who is not a liar is rather unsettling.



xvii
Introduction
place of the nth Richard number is not 1, and whose nth decimal 
place is 2 if the nth decimal place of the nth Richard number is 1.” 
This phrase defines a Richard number—say, the kth Richard num-
ber; but, by its definition, it differs from the kth Richard number in 
the kth decimal place.
	
6.	Berry’s paradox (1906): There are only a finite number of symbols (let-
ters, punctuation signs, etc.) in the English language. Hence, there 
are only a finite number of English expressions that contain fewer 
than 200 occurrences of symbols (allowing repetitions). There are, 
therefore, only a finite number of positive integers that are denoted 
by an English expression containing fewer than 200 occurrences 
of symbols. Let k be the least positive integer that is not denoted by an 
English expression containing fewer than 200 occurrences of symbols. The 
italicized English phrase contains fewer than 200 occurrences of 
symbols and denotes the integer k.
	
7.	Grelling’s paradox (1908): An adjective is called autological if the prop-
erty denoted by the adjective holds for the adjective itself. An adjec-
tive is called heterological if the property denoted by the adjective 
does not apply to the adjective itself. For example, “polysyllabic” and 
“English” are autological, whereas “monosyllabic” and “French” are 
heterological. Consider the adjective “heterological.” If “heterologi-
cal” is heterological, then it is not heterological. If “heterological” is 
not heterological, then it is heterological. In either case, “heterologi-
cal” is both heterological and not heterological.
	
8.	Löb’s paradox (1955): Let A be any sentence. Let B be the sentence: “If 
this sentence is true, then A.” So B asserts, “If B is true, then A.” Now 
consider the following argument: Assume B is true; then, by B, since 
B is true, A holds. This argument shows that if B is true, then A. But 
this is exactly what B asserts. Hence, B is true. Therefore, by B, since 
B is true, A is true. Thus, every sentence is true. (This paradox may 
be more accurately attributed to Curry [1942].)
All of these paradoxes are genuine in the sense that they contain no obvi-
ous logical flaws. The logical paradoxes (1–3) involve only notions from the 
theory of sets, whereas the semantic paradoxes (4–8) also make use of con-
cepts like “denote,” “true,” and “adjective,” which need not occur within our 
standard mathematical language. For this reason, the logical paradoxes are 
a much greater threat to a mathematician’s peace of mind than the semantic 
paradoxes.
Analysis of the paradoxes has led to various proposals for avoiding them. 
All of these proposals are restrictive in one way or another of the “naive” 
concepts that enter into the derivation of the paradoxes. Russell noted the 
self-reference present in all the paradoxes and suggested that every object 
must have a definite nonnegative integer as its “type.” Then an expression 



xviii
Introduction
“x is a member of the set y” is to be considered meaningful if and only if the 
type of y is one greater than the type of x.
This approach, known as the theory of types and systematized and devel-
oped in Principia Mathematica by Whitehead and Russell (1910–1913), is suc-
cessful in eliminating the known paradoxes,* but it is clumsy in practice and 
has certain other drawbacks as well. A different criticism of the logical para-
doxes is aimed at their assumption that, for every property P(x), there exists 
a corresponding set of all objects x that satisfy P(x). If we reject this assump-
tion, then the logical paradoxes are no longer derivable.† It is necessary, how-
ever, to provide new postulates that will enable us to prove the existence of 
those sets that are needed by the practicing mathematician. The first such 
axiomatic set theory was invented by Zermelo (1908). In Chapter 4, we shall 
present an axiomatic theory of sets that is a descendant of Zermelo’s system 
(with some new twists given to it by von Neumann, R. Robinson, Bernays, 
and Gödel). There are also various hybrid theories combining some aspects 
of type theory and axiomatic set theory—for example, Quine’s system NF.
A more radical interpretation of the paradoxes has been advocated by 
Brouwer and his intuitionist school (see Heyting, 1956). They refuse to accept 
the universality of certain basic logical laws, such as the law of excluded 
middle: P or not P. Such a law, they claim, is true for finite sets, but it is 
invalid to extend it on a wholesale basis to all sets. Likewise, they say it is 
invalid to conclude that “There exists an object x such that not-P(x)” follows 
from the negation of “For all x, P(x)”; we are justified in asserting the exis-
tence of an object having a certain property only if we know an effective 
method for constructing (or finding) such an object. The paradoxes are not 
derivable (or even meaningful) if we obey the intuitionist strictures, but so 
are many important theorems of everyday mathematics, and for this reason, 
intuitionism has found few converts among mathematicians.
Exercises
P.1	 Use the sentence
	
(*) This entire sentence is false or 2 + 2 = 5 to prove that 2 + 2 = 5. Comment 
on the significance of this proof.
P.2	 Show how the following has a paradoxical result.
	
The smallest positive integer that is not denoted by a phrase in this 
book.
*	 Russells’s paradox, for example, depends on the existence of the set A of all sets that are not 
members of themselves. Because, according to the theory of types, it is meaningless to say 
that a set belongs to itself, there is no such set A.
†	 Russell’s paradox then proves that there is no set A of all sets that do not belong to them-
selves. The paradoxes of Cantor and Burali-Forti show that there is no universal set and no 
set that contains all ordinal numbers. The semantic paradoxes cannot even be formulated, 
since they involve notions not expressible within the system.



xix
Introduction
Whatever approach one takes to the paradoxes, it is necessary first to 
examine the language of logic and mathematics to see what symbols may be 
used, to determine the ways in which these symbols are put together to form 
terms, formulas, sentences, and proofs and to find out what can and cannot 
be proved if certain axioms and rules of inference are assumed. This is one of 
the tasks of mathematical logic, and until it is done, there is no basis for com-
paring rival foundations of logic and mathematics. The deep and devastat-
ing results of Gödel, Tarski, Church, Rosser, Kleene, and many others have 
been ample reward for the labor invested and have earned for mathematical 
logic its status as an independent branch of mathematics.
For the absolute novice, a summary will be given here of some of the basic 
notations, ideas, and results used in the text. The reader is urged to skip 
these explanations now and, if necessary, to refer to them later on.
A set is a collection of objects.* The objects in the collection are called 
­elements or members of the set. We shall write “x ∈ y” for the statement that 
x is a member of y. (Synonymous expressions are “x belongs to y” and “y 
­contains x.”) The negation of “x ∈ y” will be written “x ∉ y.”
By “x ⊆ y” we mean that every member of x is also a member of y (synony-
mously, that x is a subset of y or that x is included in y). We shall write “t = s” to 
mean that t and s denote the same object. As usual, “t ≠ s” is the negation of 
“t = s.” For sets x and y, we assume that x = y if and only if x ⊆ y and y ⊆ x—that 
is, if and only if x and y have the same members. A set x is called a proper 
subset of a set y, written “x ⊂ y” if x ⊆ y but x ≠ y. (The notation x ⊈ y is often 
used instead of x ⊂ y.)
The union x ∪ y of sets x and y is defined to be the set of all objects that are 
members of x or y or both. Hence, x ∪ x = x, x ∪ y = y ∪ x, and (x ∪ y) ∪ z = 
x ∪ (y ∪ z). The intersection x ∩ y is the set of objects that x and y have in com-
mon. Therefore, x ∩ x = x, x ∩ y = y ∩ x, and (x ∩ y) ∩ z = x ∩ (y ∩ z). Moreover, 
x ∩ (y ∪ z) = (x ∩ y) ∪ (x ∩ z) and x ∪ (y ∩ z) = (x ∪ y) ∩ (x ∪ z). The relative 
complement x − y is the set of members of x that are not members of y. We also 
postulate the existence of the empty set (or null set) ∅—that is, a set that has no 
members at all. Then x ∩ ∅ = ∅, x ∪ ∅ = x, x −∅ = x, ∅ −x = ∅, and x − x = ∅. 
Sets x and y are called disjoint if x ∩ y = ∅.
Given any objects b1, …, bk, the set that contains b1, …, bk as its only mem-
bers is denoted {b1, …, bk}. In particular, {x, y} is a set having x and y as its only 
members and, if x ≠ y, is called the unordered pair of x and y. The set {x, x} 
is identical with {x} and is called the unit set of x. Notice that {x, y} = {y, x}. 
By 〈b1, …, bk〉 we mean the ordered k-tuple of b1, …, bk. The basic property of 
ordered k-tuples is that 〈b1, …, bk〉 = 〈c1, …, ck〉 if and only if b1 = c1, b2 = c2, …, 
bk = ck. Thus, 〈b1, b2〉 = 〈b2, b1〉 if and only if b1 = b2. Ordered 2-tuples are called 
*	 Which collections of objects form sets will not be specified here. Care will be exercised to 
avoid using any ideas or procedures that may lead to the paradoxes; all the results can be 
formalized in the axiomatic set theory of Chapter 4. The term “class” is sometimes used as a 
synonym for “set,” but it will be avoided here because it has a different meaning in Chapter 4. 
If a property P(x) does determine a set, that set is often denoted {x|P(x)}.



xx
Introduction
ordered pairs. The ordered 1-tuple 〈b〉 is taken to be b itself. If X is a set and k 
is a positive integer, we denote by Xk the set of all ordered k-tuples 〈b1, …, bk〉 
of elements b1, …, bk of X. In particular, X1 is X itself. If Y and Z are sets, then 
by Y × Z we denote the set of all ordered pairs 〈y, z〉 such that y ∈ Y and z ∈ Z. 
Y × Z is called the Cartesian product of Y and Z.
An n-place relation (or a relation with n arguments) on a set X is a subset 
of Xn—that is, a set of ordered n-tuples of elements of X. For example, the 
3-place relation of betweenness for points on a line is the set of all 3-tuples 
〈x, y, z〉 such that the point x lies between the points y and z. A 2-place relation 
is called a binary relation; for example, the binary relation of fatherhood on 
the set of human beings is the set of all ordered pairs 〈x, y〉 such that x and y 
are human beings and x is the father of y. A 1-place relation on X is a subset 
of X and is called a property on X.
Given a binary relation R on a set X, the domain of R is defined to be the set 
of all y such that 〈y, z〉 ∈ R for some z; the range of R is the set of all z such that 
〈y, z〉 ∈ R for some y; and the field of R is the union of the domain and range 
of R. The inverse relation R−1 of R is the set of all ordered pairs 〈y, z〉 such that 
〈z, y〉 ∈ R. For example, the domain of the relation < on the set ω of nonnega-
tive integers* is ω, its range is ω − {0}, and the inverse of < is >. Notation: Very 
often xRy is written instead of 〈x, y〉 ∈ R. Thus, in the example just given, we 
usually write x < y instead of 〈x, y〉 ∈ <.
A binary relation R is said to be reflexive if xRx for all x in the field of R; R 
is symmetric if xRy implies yRx; and R is transitive if xRy and yRz imply xRz. 
The following are examples: The relation ≤ on the set of integers is reflexive 
and transitive but not symmetric. The relation “having at least one parent 
in common” on the set of human beings is reflexive and symmetric, but not 
transitive.
A binary relation that is reflexive, symmetric, and transitive is called an 
equivalence relation. Examples of equivalence relations are (1) the identity rela-
tion IX on a set X, consisting of all pairs 〈x, x〉, where x ∈ X; (2) given a fixed 
positive integer n, the relation x ≡ y (mod n), which holds when x and y are 
integers and x − y is divisible by n; (3) the congruence relation on the set of 
triangles in a plane; and (4) the similarity relation on the set of triangles in 
a plane. Given an equivalence relation R whose field is X, and given any 
y ∈ X, define [y] as the set of all z in X such that yRz. Then [y] is called 
the R-equivalence class of y. Clearly, [u] = [v] if and only if uRv. Moreover, if 
[u] ≠ [v], then [u] ∩ [v] = ∅; that is, different R-equivalence classes have no 
elements in common. Hence, the set X is completely partitioned into the 
R-equivalence classes. In example (1) earlier, the equivalence classes are just 
the unit sets {x}, where x ∈ X. In example (2), there are n equivalence classes, 
the kth equivalence class (k = 0, 1, …, n − 1) being the set of all integers that 
leave the remainder k upon division by n.
*	 ω will also be referred to as the set of natural numbers.



xxi
Introduction
A function f is a binary relation such that 〈x, y 〉 ∈ f and 〈x, z〉 ∈ f imply y = z. 
Thus, for any element x of the domain of a function f, there is a unique y such 
that 〈x, y〉 ∈ f; this unique y is denoted f(x). If x is in the domain of f, then f(x) 
is said to be defined. A function f with domain X and range Y is said to be a 
function from X onto Y. If f is a function from X onto a subset of Z, then f is 
said to be a function from X into Z. For example, if the domain of f is the set 
of integers and f(x) = 2x for every integer x, then f is a function from the set of 
integers onto the set of even integers, and f is a function from the set of inte-
gers into the set of integers. A function whose domain consists of n-tuples is 
said to be a function of n arguments. A total function of n arguments on a set X is 
a function f whose domain is Xn. It is customary to write f(x1, …, xn) instead 
of f(〈x1, …, xn〉), and we refer to f(x1, …, xn) as the value of f for the arguments 
x1, …, xn. A partial function of n arguments on a set X is a function whose 
domain is a subset of Xn. For example, ordinary division is a partial, but not 
total, function of two arguments on the set of integers, since division by 0 is 
not defined. If f is a function with domain X and range Y, then the restriction 
fz of f to a set Z is the function f ∩ (Z × Y). Then fZ(u) = v if and only if u ∈ Z 
and f(u) = v. The image of the set Z under the function f is the range of fz. The 
inverse image of a set W under the function f is the set of all u in the domain 
of f such that f(u) ∈ W. We say that f maps X onto (into) Y if X is a subset of the 
domain of f and the image of X under f is (a subset of) Y. By an n-place opera-
tion (or operation with n arguments) on a set X we mean a function from Xn 
into X. For example, ordinary addition is a binary (i.e., 2-place) operation 
on the set of natural numbers {0, 1, 2, …}. But ordinary subtraction is not a 
binary operation on the set of natural numbers.
The composition f ⚬ ɡ (sometimes denoted fɡ) of functions f and ɡ is the 
function such that (f ⚬ ɡ)(x) = f(ɡ(x)); (f ⚬ ɡ)(x) is defined if and only if ɡ(x) 
is defined and f(ɡ(x)) is defined. For example, if ɡ(x) = x2 and f(x) = x + 1 for 
every integer x, then (f ⚬ ɡ)(x) = x2 + 1 and (ɡ ⚬ f)(x) = (x + 1)2. Also, if h(x) = −x 
for every real number x and f x
x
( ) =
 for every nonnegative real number x, 
then (f ⚬ h)(x) is defined only for x ⩽ 0, and, for such x
f h x
x
,(
)( )
°
=
−. A func-
tion f such that f(x) = f(y) implies x = y is called a 1–1 (one–one) function. For 
example, the identity relation IX on a set X is a 1–1 function, since IX(y) = y for 
every y ∈ X; the function g with domain ω, such that ɡ(x) = 2x for every x ∈ ω, 
is 1–1 (one–one); but the function h whose domain is the set of integers and 
such that h(x) = x2 for every integer x is not 1–1, since h(−1) = h(1). Notice that 
a function f is 1–1 if and only if its inverse relation f −1 is a function. If the 
domain and range of a 1–1 function f are X and Y, then f is said to be a 1–1 
­correspondence between X and Y; then f −1 is a 1–1 correspondence between 
Y and X, and (f −1 ⚬ f) = IX and (f ⚬ f −1) = IY. If f is a 1–1 correspondence 
between X and Y and ɡ is a 1–1 correspondence between Y and Z, then ɡ ⚬ f 
is a 1–1 correspondence between X and Z. Sets X and Y are said to be equinu-
merous (written X ≅ Y) if and only if there is a 1–1 correspondence between 
X and Y. Clearly, X ≅ X, X ≅ Y implies Y ≅ X, and X ≅ Y and Y ≅ Z implies 
X ≅ Z. It is somewhat harder to show that, if X ≅ Y1 ⊆ Y and Y ≅ X1 ⊆ X, then 



xxii
Introduction
X ≅ Y (see Bernstein’s theorem in Chapter 4). If X ≅ Y, one says that X and Y 
have the same cardinal number, and if X is equinumerous with a subset of Y but 
Y is not equinumerous with a subset of X, one says that the cardinal number 
of X is smaller than the cardinal number of Y.*
A set X is denumerable if it is equinumerous with the set of positive integers. 
A denumerable set is said to have cardinal number ℵ0, and any set equinu-
merous with the set of all subsets of a denumerable set is said to have the 
cardinal number 2
0
ℵ (or to have the power of the continuum). A set X is finite 
if it is empty or if it is equinumerous with the set {1, 2, …, n} of all positive 
integers that are less than or equal to some positive integer n. A set that is 
not finite is said to be infinite. A set is countable if it is either finite or denu-
merable. Clearly, any subset of a denumerable set is countable. A denumerable 
sequence is a function s whose domain is the set of positive integers; one usu-
ally writes sn instead of s(n). A finite sequence is a function whose domain is 
the empty set or {1, 2, …, n} for some positive integer n.
Let P(x, y1, …, yk) be some relation on the set of nonnegative integers. 
In particular, P may involve only the variable x and thus be a property. If 
P(0, y1, …, yk) holds, and, if, for every n, P(n, y1, …, yk) implies P(n + 1, y1, …, yk), 
then P(x, y1, …, yk) is true for all nonnegative integers x (principle of mathemati-
cal induction). In applying this principle, one usually proves that, for every n, 
P(n, y1, …, yk) implies P(n + 1, y1, …, yk) by assuming P(n, y1, …, yk) and then 
deducing P(n + 1, y1, …, yk); in the course of this deduction, P(n, y1, …, yk) 
is called the inductive hypothesis. If the relation P actually involves variables 
y1, …, yk other than x, then the proof is said to proceed by induction on x. 
A similar induction principle holds for the set of integers greater than some 
fixed integer j. An example is as follows: to prove by mathematical induc-
tion that the sum of the first n odd integers 1 + 3 + 5 + ⋯ + (2n − 1) is n2, first 
show that 1 = 12 (i.e., P(1)), and then, that if 1
3
5
2
1
2
+
+
+
+
−
=

(
)
n
n , then 
1
3
5
2
1
2
1
1 2
+
+
+
+
−
+
+
=
+

(
)
(
)
(
)
n
n
n
 (i.e., if P(n), then P(n + 1)). From the 
principle of mathematical induction, one can prove the principle of complete 
induction: If for every nonnegative integer x the assumption that P(u, y1, …, yk) 
is true for all u < x implies that P(x, y1, …, yk) holds, then, for all nonnegative 
integers x, P(x, y1, …, yk) is true. (Exercise: Show by complete induction that 
every integer greater than 1 is divisible by a prime number.)
A partial order is a binary relation R such that R is transitive and, for every 
x in the field of R, xRx is false. If R is a partial order, then the relation R′ that 
is the union of R and the set of all ordered pairs 〈x, x〉, where x is in the field 
of R, we shall call a reflexive partial order; in the literature, “partial order” is 
used for either partial order or reflexive partial order. Notice that (xRy and 
yRx) is impossible if R is a partial order, whereas (xRy and yRx) implies x = y 
if R is a reflexive partial order. A (reflexive) total order is a (reflexive) partial 
*	 One can attempt to define the cardinal number of a set X as the collection [X] of all sets equi-
numerous with X. However, in certain axiomatic set theories, [X] does not exist, whereas in 
others [X] exists but is not a set.



xxiii
Introduction
order such that, for any x and y in the field of R, either x = y or xRy or yRx. For 
example, (1) the relation < on the set of integers is a total order, whereas ≤ is 
a reflexive total order; (2) the relation ⊂ on the set of all subsets of the set of 
positive integers is a partial order but not a total order, whereas the relation ⊆ 
is a reflexive partial order but not a reflexive total order. If B is a subset of the 
field of a binary relation R, then an element y of B is called an R-least element 
of B if yRz for every element z of B different from y. A well-order (or a well-
ordering relation) is a total order R such that every nonempty subset of the 
field of R has an R-least element. For example, (1) the relation < on the set of 
nonnegative integers is a well-order, (2) the relation < on the set of nonnega-
tive rational numbers is a total order but not a well-order, and (3) the relation 
< on the set of integers is a total order but not a well-order. Associated with 
every well-order R having field X, there is a complete induction principle: if P is 
a property such that, for any u in X, whenever all z in X such that zRu have 
the property P, then u has the property P, then it follows that all members 
of X have the property P. If the set X is infinite, a proof using this principle 
is called a proof by transfinite induction. One says that a set X can be well-
ordered if there exists a well-order whose field is X. An assumption that is 
useful in modern mathematics but about the validity of which there has been 
considerable controversy is the well-ordering principle: every set can be well-
ordered. The well-ordering principle is equivalent (given the usual axioms of 
set theory) to the axiom of choice: for any set X of nonempty pairwise disjoint 
sets, there is a set Y (called a choice set) that contains exactly one element in 
common with each set in X.
Let B be a nonempty set, f a function from B into B, and g a function from 
B2 into B. Write x′ for f(x) and x ∩ y for g(x, y). Then 〈B, f, g〉 is called a Boolean 
algebra if B contains at least two elements and the following conditions are 
satisfied:
	
1.	x ∩ y = y ∩ x for all x and y in B.
	
2.	(x ∩ y) ∩ z = x ∩ (y ∩ z) for all x, y, z in B.
	
3.	x ∩ y′ = z ∩ z′ if and only if x ∩ y = x for all x, y, z in B.
Let x ∪ y stand for (x′ ∩ y′)′, and write x ⩽ y for x ∩ y = x. It is easily proved 
that z ∩ z′ = w ∩ w′ for any w and z in B; we denote the value of z ∩ z′ by 0. 
Let 1 stand for 0′. Then z ∪ z′ = 1 for all z in B. Note also that ≤ is a reflexive 
partial order on B, and 〈B, f, ∪〉 is a Boolean algebra. (The symbols ∩, ∪, 0, 1 
should not be confused with the corresponding symbols used in set theory 
and arithmetic.) An ideal J in 〈B, f, ɡ〉 is a nonempty subset of B such that (1) if 
x ∈ J and y ∈ J, then x ∪ y ∈ J, and (2) if x ∈ J and y ∈ B, then x ∩ y ∈ J. Clearly, 
{0} and B are ideals. An ideal different from B is called a proper ideal. A maxi-
mal ideal is a proper ideal that is included in no other proper ideal. It can be 
shown that a proper ideal J is maximal if and only if, for any u in B, u ∈ J or 
u′ ∈ J. From the axiom of choice it can be proved that every Boolean algebra 



xxiv
Introduction
contains a maximal ideal, or, equivalently, that every proper ideal is included 
in some maximal ideal. For example, let B be the set of all subsets of a set X; 
for Y ∈ B, let Y′ = X −Y, and for Y and Z in B, let Y ∩ Z be the ordinary set-
theoretic intersection of Y and Z. Then 〈B,′ ∩〉 is a Boolean algebra. The 0 of B 
is the empty set ∅, and 1 is X. For each element u in X, the set Ju of all subsets 
of X that do not contain u is a maximal ideal. For a detailed study of Boolean 
algebras, see Sikorski (1960), Halmos (1963), and Mendelson (1970).


