<!-- Source: Mendelson, E. (2016). Introduction to Mathematical Logic (6th ed). Chapter 5: Computability (pages 311-443+). BibKey: not yet in references.bib -->

5.1  Algorithms: Turing Machines
An algorithm is a computational method for solving each and every problem 
from a large class of problems. The computation has to be precisely specified 
so that it requires no ingenuity for its performance. The familiar technique 
for adding integers is an algorithm, as are the techniques for computing the 
other arithmetic operations of subtraction, multiplication and division. The 
truth table procedure to determine whether a statement form is a tautology 
is an algorithm within logic itself.
It is often easy to see that a specified procedure yields a desired algorithm. 
In recent years, however, many classes of problems have been proved not to 
have an algorithmic solution. Examples are:
	
1.	Is a given wf of quantification theory logically valid?
	
2.	Is a given wf of formal number theory S true (in the standard 
interpretation)?
	
3.	Is a given wf of S provable in S?
	
4.	Does a given polynomial f(x1, …, xn) with integral coefficients have 
integral roots (Hilbert’s 10th problem)?
In order to prove rigorously that there does not exist an algorithm for answer-
ing such questions, it is necessary to supply a precise definition of the notion 
of algorithm.
Various proposals for such a definition were independently offered in 1936 
by Church (1936b), Turing (1936–1937), and Post (1936). All of these defini-
tions, as well as others proposed later, have been shown to be equivalent. 
Moreover, it is intuitively clear that every procedure given by these defini-
tions is an algorithm. On the other hand, every known algorithm falls under 
these definitions. Our exposition will use Turing’s ideas.
First of all, the objects with which an algorithm deals may be assumed to 
be the symbols of a finite alphabet A = {a0, a1, …, an}. Nonsymbolic objects can 



312
Introduction to Mathematical Logic
be represented by symbols, and languages actually used for computation 
require only finitely many symbols.*
A finite sequence of symbols of a language A is called a word of A. It is con-
venient to admit an empty word Λ consisting of no symbols at all. If P and Q 
are words, then PQ denotes the word obtained by writing Q to the right of P. 
For any positive integer k, Pk shall stand for the word made up of k consecu-
tive occurrences of P.
The work space of an algorithm often consists of a piece of paper or a 
blackboard. However, we shall make the simplifying assumption that all 
calculations take place on a tape that is divided into squares (see Figure 5.1). 
The tape is potentially infinite in both directions in the sense that, although 
at any moment it is finite, more squares always can be added to the right- 
and left-hand ends of the tape. Each square contains at most one symbol of 
the alphabet A. At any one time, only a finite number of squares contain 
symbols, while the rest are blank. The symbol a0 will be reserved for the 
content of a blank square. (In ordinary language, a space is sometimes used 
for the same purpose.) Thus, the condition of the tape at a given moment 
can be represented by a word of A; the tape in Figure 5.1 is a2a0a5a1. Our 
use of a one-dimensional tape does not limit the algorithms that can be 
handled; the information in a two-dimensional array can be encoded as a 
finite sequence.†
Our computing device, which we shall refer to as a Turing machine, works 
in the following way. The machine operates at discrete moments of time, not 
continuously. It has a reading head which, at any moment, will be scanning 
one square of the tape. (Observation of a larger domain could be reduced to 
consecutive observations of individual squares.) The device then reacts in 
any of four different ways:
	
1.	It prints a symbol in the square, erasing the previous symbol.
	
2.	It moves to the next square to the right.
	
3.	It moves to the next square to the left.
	
4.	It stops.
*	 If a language has a denumerable alphabet {a0, a1, …}, then we can replace it by the alphabet 
{b, *}. Each symbol an of the old alphabet can be replaced by the expression b* ⋯* , consisting 
of b followed by n occurrences of*.
†	 This follows from the fact that there is an effective one–one correspondence between the set 
of pairs of natural numbers and the set of natural numbers. For the details, see pages 184–185.
a2
a5
a1
Figure 5.1



313
Computability
What the machine does depends not only on the observed symbol but also on 
the internal state of the machine at that moment (which, in turn, depends on 
the previous steps of the computation and on the structure of the machine). 
We shall make the plausible assumption that a machine has only a finite 
number of internal states {q0, q1, …, qm}. The machine will always begin its 
operation in the initial state q0.
A step in a computation corresponds to a quadruple of one of the following 
three forms: (1) qjaiakqr; (2) qjaiRqr; (3) qjaiLqr. In each case, qj is the present 
internal state, ai is the symbol being observed, and qr is the internal state 
after the step. In form (1), the machine erases ai and prints ak. In form (2), the 
reading head of the machine moves one square to the right, and, in form (3), 
it moves one square to the left. We shall indicate later how the machine is 
told to stop.
Now we can give a precise definition. A Turing machine with an alphabet A 
of tape symbols {a0, a1, …, an} and with internal states {q0, q1, …, qm} is a finite set 
T  of quadruples of the forms (1) qjaiakqr, (2) qjaiRqr, and (3) qjaiLqr such that 
no two quadruples of T    have the same first two symbols.
Thus, for fixed qjai, no two quadruples of types (1), (2), and (3) are in T. 
This condition ensures that there is never a situation in which the machine is 
instructed to perform two contradictory operations.
The Turing machine T   operates in accordance with its list of quadruples. 
This can be made precise in the following manner.
By a tape description of T    we mean a word such that: (1) all symbols in the 
word but one are tape symbols; (2) the only symbol that is not a tape symbol 
is an internal state qj; and (3) qj is not the last symbol of the word.
A tape description describes the condition of the machine and the tape at a 
given moment. When read from left to right, the tape symbols in the descrip-
tion represent the symbols on the tape at that moment, and the tape symbol 
that occurs immediately to the right of qj in the tape description represents 
the symbol being scanned by the reading head at that moment. If the internal 
state qj is the initial state q0, then the tape description is called an initial tape 
description.
Example
The tape description a2a0q1a0a1a1 indicates that the machine is in the internal 
state q1, the tape is as shown in Figure 5.2, and the reading head is scanning 
the square indicated by the arrow.
a2
a0
a0
a1
a1
Figure 5.2 



314
Introduction to Mathematical Logic
We say that T   moves one tape description α into another one β (abbreviated 
α
β
↠
T
) if and only if one of the following is true.
	
1.	α is of the form PqjaiQ, β is of the form PqrakQ, and qjaiakqr is one of 
the quadruples of T . *
	
2.	α is of the form PasqjaiQ, β is of the form PqrasaiQ, and qjaiLqr is one 
of the quadruples of T .
	
3.	α is of the form qjaiQ, β is of the form qra0aiQ, and qjaiLqr is one of the 
quadruples of T .
	
4.	α is of the form PqjaiakQ, β is of the form PaiqrakQ, and qjaiRqr is one 
of the quadruples of T .
	
5.	α is of the form Pqjai, β is of the form Paiqra0, and qjaiRqr is one of the 
quadruples of T .
According to our intuitive picture, “T   moves α into β” means that, if the con-
dition at a time t of the Turing machine and tape is described by α, then the 
condition at time t + 1 is described by β. Notice that, by clause 3, whenever 
the machine reaches the left-hand end of the tape and is ordered to move 
left, a blank square is attached to the tape on the left; similarly, by clause 5, 
a blank square is added on the right when the machine reaches the right-
hand end and has to move right.
We say that T  stops at tape description α if and only if there is no tape 
description β such that α
β
↠
T
. This happens when qjai occurs in α but qjai is 
not the beginning of any quadruple of T .
A computation of T   is a finite sequence of tape descriptions α0, …, αk (k ≥ 0) 
such that the following conditions hold.
	
1.	α0 is an initial tape description, that is, the internal state occurring in 
α is q0.
	
2.	α
α
i
i
↠
T
+1 for 0 ≤ i < k
	
3.	T  stops at αk.
This computation is said to begin at α0 and end at αk. If there is a computation 
beginning at α0, we say that T    is applicable to α0.
The algorithm AlgT   determined by T   is defined as follows:
For any words P and Q of the alphabet A of T , AlgT  (P) = Q if and only if 
there is a computation of T    that begins with the tape description q0P and 
ends with a tape description of the form R1qjR2, where Q = R1R2.
This means that, when T    begins at the left-hand end of P and there is nothing 
else on the tape, T   eventually stops with Q as the entire content of the tape. 
*	 Here and below, P and Q are arbitrary (possibly empty) words of the alphabet of T.



315
Computability
Notice that AlgT   need not be defined for certain words P. An algorithm AlgT  
determined by a Turing machine T    is said to be a Turing algorithm.
Example
In any computation of the Turing machine T    given by
	
q a Rq
q a a q
q a a q
q a a q
0
0
0
0
1
0
1
0
2
0
1
0
0
1
,
,
,
,
…
n
T   locates the first nonblank symbol (if any) at or to the right of the square 
scanned at the beginning of the computation, erases that symbol, and then 
stops. If there are only blank squares at or to the right of the initial square, 
T    keeps on moving right forever.
Let us now consider computations of number-theoretic functions. For con-
venience, we sometimes will write | instead of a1 and B instead of a0. (Think 
of B as standing for “blank.”) For any natural number k, its tape representation 
k will stand for the word |k+1, that is, the word consisting of k + 1 occurrences 
of |. Thus, 0
1
2
=
=
=
|,
||,
|||, and so on. The reason why we represent k by 
k + 1 occurrences of | instead of k occurrences is that we wish 0 to be a non-
empty word, so that we will be aware of its presence. The tape representation 
(
,
,
,
)
k k
kn
1
2 …
 of an n-tuple of natural numbers (k1, k2, …, kn) is defined to be 
the word k
k
kn
1
2
B
B
B

. For example, ( , , , )
3 1 0 5  is ||||B||B|B||||||.
A Turing machine T    will be thought of as computing the following partial 
function fT ,1 of one variable.*
fT ,1(k)=m if and only if the following condition holds: AlgT ( )
k  is defined 
and Alg
E
E
T ( )
k
m
=
1
2, where E1 and E2 are certain (possibly empty) words 
consisting of only Bs (blanks).
The function fT,  1 is said to be Turing-computable. Thus, a one-place partial 
function f is Turing-computable if and only if there is a Turing machine such 
that f = fT,  1.
For each n > 1, a Turing machine T  also computes a partial function fT,  n of 
n variables. For any natural numbers k1, …, kn:
fT,   n(k1, …, kn) = m if and only if the following condition holds:
AlgT ((
,
,
,
))
k
k
kn
1
2 …
 is defined and Alg
E
E
T ((
,
,
,
))
k
k
k
m
n
1
2
1
2
…
=
, where 
E1 and E2 are certain (possibly empty) words consisting of only Bs (blanks).
The partial function fT,  n is said to be Turing-computable. Thus, an n-place 
­partial function f is Turing-computable if and only if there is a Turing 
machine T   such that f = fT,  n.
Notice that, at the end of a computation of a value of a Turing-computable 
function, only the value appears on the tape, aside from blank squares at 
either or both ends, and the location of the reading head does not matter. 
Also observe that, whenever the function is not defined, either the Turing 
*	 Remember that a partial function may fail to be defined for some values of its argument. 
Thus, a total function is considered to be a special case of a partial function.



316
Introduction to Mathematical Logic
machine will never stop or, if it does stop, the resulting tape is not of the 
appropriate form E
E
1
2
m
.
Examples
	
1.	Consider the Turing machine T, with alphabet {B, |}, defined 
by q0|Lq1, q1B|q2. T  computes the successor function N(x), 
since q k
q Bk
q k
0
1
2
1
↠
↠
T
T
+ , and T  stops at q2
1
k + . Hence N(x) is 
Turing-computable.
	
2.	The Turing machine T    defined by
	
q
Bq
q BRq
q B q
0
1
1
0
0
2
|
,
,
|
	
	 computes the zero function Z(x). Given k on the tape, T   moves right, 
erasing all |s until it reaches a blank, which it changes to a |. So, 0 is 
the final result. Thus, Z(x) is Turing-computable.
	
3.	The addition function is computed by the Turing machine T defined 
by the following seven quadruples:
	
q
Bq
q BRq
q
Rq
q B q
q
Rq
q BL q
q
Bq
0
0
0
1
1
1
1
2
2
2
2
3
3
3
|
,
,
|
,
|
,
|
,
|
,
|
In fact, for any natural numbers m and n,
	
q
q
B
q B
B
Bq
B
B
q B
0
0
1
1
0
1
1
1
1
1
(
, )
|
|
|
|
|
|
|
|
m n
m
n
m
n
m
n
m
n
=
+
+
+
+
+
↠
↠
↠
↠
T
T
T
T

↠
↠
↠
↠
↠
T
T
T
T
T
B
q
B
q B
B
q
B
B
q BB
B
|
||
||
|
|
|
m
n
m n
m n
m n
m
2
1
2
2
1
3
1
3
+
+
+ +
+ +
=
+

nq BB
3
and T   stops at B
q BB
m
n
+
3
.
Exercises
5.1	 Show that the function U2
2 such that U
x x
x
2
2
1
2
2
(
,
) =
 is Turing-computable.
5.2	 a.	
What function f(x1, x2, x3) is computed by the following Turing 
machine?
	
q
q
q
Bq
q BRq
q BRq
q
Rq
q BRq
q
Bq
q BRq
||
0
1
1
0
0
1
1
2
2
2
2
3
3
4
4
3
,
|
,
,
,
|
,
,
|
,
	
b.	 What function f(x) is computed by the following Turing machine?
	
q
Bq
q BRq
q B q
0
1
1
2
2
2
|
,
,
|



317
Computability
5.3	 a.	
State in plain language the operation of the Turing machine, 
described in Example 3, for computing the addition function.
	
b.	 Starting with the tape description q0|||B|||, write the sequence of 
tape descriptions that make up the computation by the addition 
machine of Example 3.
5.4	 What function f(x) is computed by the following Turing machine?
	
q
Rq
q
Rq
q B q
q
Bq
q B q
q B q
q BRq
q
Lq
q
Lq
q
R
0
1
4
4
6
0
1
2
4
5
1
7
2
3
5
5
7
7
3
|
|
|
|
|
|
|
|
| q
q BLq
q BRq
q BRq
q
Lq
q
Bq
3
5
6
7
8
3
4
6
6
8
8
|
|
5.5	 Find a Turing machine that computes the function sg(x). (Recall that 
sg(0) = 0 and sg(x) = 1 for x > 0.)
5.6D	Find Turing machines that compute the following functions.
	
a.	 x
y
− (Remember that x
y
x
y
−
=
− if x ≥ y, and x
y
−
= 0 if x < y.)
	
b.	 [x/2] (Recall that [x/2] is the greatest integer less than or equal to 
x/2. Thus, [x/2] = x/2 if x is even, and [x/2] = (x − 1)/2 if x is odd.)
	
c.	 x · y, the product of x and y.
5.7	 If a function is Turing-computable, show that it is computable by infi-
nitely many different Turing machines.
5.2  Diagrams
Many Turing machines that compute even relatively simple functions (like 
multiplication) require a large number of quadruples. It is difficult and 
tedious to construct such machines, and even more difficult to check that 
they do the desired job. We shall introduce a pictorial technique for con-
structing Turing machines so that their operation is easier to comprehend. 
The basic ideas and notation are due to Hermes (1965).
	
1.	Let T1, …, Tr   be any Turing machines with alphabet A = {a0, a1, …, ak}.
	
2.	Select a finite set of points in a plane. These points will be called 
vertices.
	
3.	To each vertex attach the name of one of the machines T1, …, Tr. Copies 
of the same machine may be assigned to more than one vertex.



318
Introduction to Mathematical Logic
	
4.	Connect some vertices to others by arrows. An arrow may go from 
a vertex to itself. Each arrow is labeled with one of the numbers 
0, 1, …, k. No two arrows that emanate from the same vertex are 
allowed to have the same label.
	
5.	One vertex is enclosed in a circle and is called the initial vertex.
The resulting graph is called a diagram.
Example
See Figure 5.3.
We shall show that every diagram determines a Turing machine whose 
operation can be described in the following manner. Given a tape and a spe-
cific square on the tape, the Turing machine of the initial vertex V of the dia-
gram begins to operate, with its reading head scanning the specified square 
of the tape. If this machine finally stops and the square being scanned at the 
end of the computation contains the symbol ai, then we look for an arrow 
with label i emanating from the vertex V. If there is no such arrow, the com-
putation stops. If there is such an arrow, it leads to a vertex to which another 
Turing machine has been assigned. Start that machine on the tape produced 
by the previous computation, at the square that was being scanned at the end 
of the computation. Repeat the same procedure that was just performed, and 
keep on doing this until the machine stops. The resulting tape is the output 
of the machine determined by the diagram. If the machine never stops, then 
it is not applicable to the initial tape description.
The quadruples for this Turing machine can be specified in the following 
way.
	
1.	For each occurrence in the diagram of a machine Tj, write its qua-
druples, changing internal states so that no two machine occur-
rences have an internal state in common. The initial vertex machine 
is not to be changed. This retains q0 as the initial internal state of 
the machine assigned to the initial vertex. For every other machine 
occurrence, the original initial state q0 has been changed to a new 
internal state.
0
0
2
1
2
3
0
1
1
1
Figure 5.3 



319
Computability
	
2.	If an occurrence of some Ti  is connected by an arrow →
u  to some 
Tj, then, for every (new) internal state qs of that occurrence of Ti 
such that no (new) quadruple of Ti  begins with qsau, add the qua-
druple qsauauqt, where qt is the (new) initial state for Tj. (Step 2 
ensures that, whenever Ti  stops while scanning au, Tj  will begin 
operating.)
The following abbreviations are used in diagrams:
	
1.	If one vertex is connected to another vertex by all arrows →→… →
0
1
,
,
,
,
k
we replace the arrows by one unlabelled arrow.
	
2.	If one vertex is connected to another by all arrows except →
u , we 
replace all the arrows by →
≠u.
	
3.	Let T1T2 stand for T1  → T2, let T1T2T3 stand for T1 → T2 → T3, and so on. 
Let T   2 be T T, let T   3 be T T T, and so forth.
	
4.	If no vertex is circled, then the leftmost vertex is to be initial.
To construct diagrams, we need a few simple Turing machines as building 
blocks.
	
1.	r (right machine). Let {a0, a1, …, ak} be the alphabet. r consists of the 
quadruples q0aiRq1 for all ai. This machine, which has k + 1 qua-
druples, moves one square to the right and then stops.
	
2.	l (left machine). Let {a0, a1, …, ak} be the alphabet. l consists of the 
quadruples q0aiLq1 for all ai. This machine, which has k + 1 quadru-
ples, moves one square to the left and then stops.
	
3.	aj (constant machine) for the alphabet {a0, a1, …, ak}. aj consists of 
the quadruples q0aiajq1 for all ai. This machine replaces the initial 
scanned symbol by aj and then stops. In particular, a0 erases the 
scanned symbol, and a1 prints |.
Examples of Turing Machines Defined by Diagrams
	
1.	P (Figure 5.4) finds the first blank to the right of the initially scanned 
square. In an alphabet {a0, a1, …, ak}, the quadruples for the machine 
P are q0aiRq1 for all ai, and q1aiaiq0 for all ai ≠ a0.
r
 ≠ 0
Figure 5.4 



320
Introduction to Mathematical Logic
	
2.	Λ (Figure 5.5) finds the first blank to the left of the initially scanned 
square.
Exercises
5.8	 Describe the operations of the Turing machines ρ (Figure 5.6) and λ 
(Figure 5.7) and write the list of quadruples for each machine.
5.9	 Show that machine S in Figure 5.8 searches the tape for a nonblank 
square. If there are such squares, S finds one and stops. Otherwise, 
S never stops.
≠ 0
1
Figure 5.5 
r
0
Figure 5.6 
1
0
Figure 5.7 
≠ 0
0
0
a11
a1ρa0r
λa0ρ  
ρa0λ
a1λa0
r
0
≠ 0
Figure 5.8 



321
Computability
To describe some aspects of the operation of a Turing machine on part of a 
tape, we introduce the following notation:
~	
arbitrary symbol
B … B	 sequence of blanks
B …	
everything blank to the right
… B	
everything blank to the left
W	
nonempty word consisting of nonblanks
X	
W1BW2B … Wn(n ≥ 1), a sequence of nonempty words of nonblanks, 
separated by blanks
Underlining will indicate the scanned symbol.
More Examples of Turing Machines Defined by Diagrams
	
3.	R (right-end machine). See Figure 5.9.
	
 XBB
XBB
⇒~
	
	 Squares on the rest of the tape are not affected. The same assump-
tion is made in similar places below. When the machine R begins 
on a square preceding a sequence of one or more nonempty words, 
followed by at least two blank squares, it moves right to the first of 
those blank squares and stops.
	
4.	L  (left-end machine). See Figure 5.10.
	
BBX
BBX
 ⇒
~
	
5.	T (left-translation machine). See Figure 5.11.*
	
 BWB
WBB
⇒~
	
	 This machine shifts the whole word W one square to the left.
*	 There is a separate arrow from r2 to each of the groups on the right and a separate arrow from 
each of these, except la0, back to r2.
Pr
1
0
≠ 0
Figure 5.9 



322
Introduction to Mathematical Logic
	
6.	σ (shift machine). See Figure 5.12.
	
BW BW B
BW B
B
1
2
2
⇒
…
	
	 In the indicated situation, W1 is erased and W2 is shifted leftward so 
that it begins where W1 originally began.
	
7.	C (clean-up machine). See Figure 5.13.
	
~
~
BBXBWB
WB
B
⇒
…
	
8.	K (word-copier). See Figure 5.14.
	
BWB
BWBWB
…⇒
…
r
0
≠ 0
Λ1
Figure 5.10 
r2
1
0
k
1a0
1a1
1ak
Figure 5.11 
a0T
T
0
≠ 0
Λ1
Figure 5.12 



323
Computability
	
9.	Kn (n-shift copier). See Figure 5.15.
	
BW BW
B
W B
BW BW
B
W BW B
n
n
n
n
n
−
−
…
… ⇒
…
…
1
1
1
1
Exercises
5.10	 Find the number-theoretic function f(x) computed by each of the fol-
lowing Turing machines.
	a.	 1a1
	b.	 Figure 5.16
	c.	 PKΛa1Λ(ra0)2
5.11	 Verify that the given functions are computed by the indicated Turing 
machines.
	a.	 |x − y| (Figure 5.17)
	b.	 x + y Pa1Λ(ra0)2
	c.	 x · y (Figure 5.18)
5.12	 Draw diagrams for Turing machines that will compute the following 
functions: (a) max(x, y) (b) min(x, y) (c) x
y
− (d) [x/2].
rPσ
TΛ1T
0
≠ 0
Λ1
Figure 5.13 
1
0
P
k
a0P2akΛ2ak
a0P2a1Λ2a1
Λr
Figure 5.14 



324
Introduction to Mathematical Logic
1
0
Pn
k
a0Pn+1a1Λn+1a1
a0Pn+1akΛn+1ak
Λnr
Figure 5.15 
0
a0r
a1ra1
≠ 0
Figure 5.16 
0
P2 1a01
1
1
a0r
Λa1
Λ2r
Figure 5.17 
0
0
K
r
r
Pra1rC
1a0(r2)
1a0
1a1Λ(ra0)2 P
1
1
1
Figure 5.18 



325
Computability
5.13	 Prove that, for any Turing machine T    with alphabet {a0, …, ak}, there is 
a diagram using the Turing machines r, l, a0, …, ak that defines a Turing 
machine T  such that T   and S   have the same effect on all tapes. (In fact, 
S  can be defined so that, except for two additional trivial initial moves 
left and right, it carries out the same computations as T  .)
5.3  Partial Recursive Functions: Unsolvable Problems
Recall, from Section 3.3, that the recursive functions are obtained from the 
initial functions (the zero function Z(x), the successor function N(x), and the 
projection functions U
x
x
i
n
n
(
,
,
)
1 …
) by means of substitution, recursion, and 
the restricted μ-operator. Instead of the restricted μ-operator, let us introduce 
the unrestricted μ-operator:
	
If
f x
x
y
x
x
y
x
x
n
n
n
(
,
,
)
( (
,
,
,
)
)
(
,
,
1
1
1
0
…
=
…
=
=
…
µ g
g
the least
such that
y
,
)
y = 0
then
is said to arise from
by means of the unrestricted
ope
f
g
µ
rator.
Notice that, for some x1, …, xn, the value f(x1, …, xn) need not be defined; this 
happens when there is no y such that ɡ(x1, …, xn, y) = 0.
If we replace the restricted μ-operator by the unrestricted μ-operator in 
the definition of the recursive functions, we obtain a definition of the par-
tial recursive functions. In other words, the partial recursive functions are 
those functions obtained from the initial functions by means of substitution, 
recursion and the unrestricted μ-operator.
Whereas all recursive functions are total functions, some partial recursive 
functions will not be total functions. For example, μy(x + y = 0) is defined 
only when x = 0.
Since partial recursive functions may not be defined for certain arguments, 
the definition of the unrestricted μ-operator should be made more precise:
	
µy
x
x
y
k
u
k
x
x
u
n
n
( (
,
,
, )
)
,
,
(
,
,
, )
g
g
1
1
0
0
…
=
=
≤
<
…
means that for
is defined and
and
g
g
(
,
,
, )
,
(
,
,
, )
x
x
u
x
x
k
n
n
1
1
0
0
…
≠
…
=
Observe that, if R(x1, …, xn, y) is a recursive relation, then μy(R(x1, …, xn, y)) 
can be considered an admissible application of the unrestricted μ-operator. 
In fact, μy(R(x1, …, xn, y)) = μy(CR(x1, …, xn, y) = 0), where CR is the characteristic 
function of R. Since R is a recursive relation, CR is, by definition, a recursive 
function.



326
Introduction to Mathematical Logic
Exercises
5.14	 Describe the following partial recursive functions.
	a.	 μy(x + y + 1 = 0)
	b.	 μy(y > x)
	c.	 μy(y + x = x)
5.15	 Show that all recursive functions are partial recursive.
5.16	 Show that every partial function whose domain is a finite set of natural 
numbers is a partial recursive function.
It is easy to convince ourselves that every partial recursive function 
f(x1, …, xn) is computable, in the sense that there is an algorithm that computes 
f(x1, …, xn) when f(x1, …, xn) is defined and gives no result when f(x1, …, xn) 
is undefined. This property is clear for the initial functions and is inher-
ited under the operations of substitution, recursion and the unrestricted 
μ-operator.
It turns out that the partial recursive functions are identical with the 
Turing-computable functions. To show this, it is convenient to introduce a 
different kind of Turing-computablility.
A partial number-theoretic function f(x1, …, xn) is said to be standard Turing-
computable if there is a Turing machine T   such that, for any natural numbers 
k1, …, kn, the following holds.
Let B B
B
B
k
k
kn
1
2 …
 be called the argument strip.* Notice that the argument 
strip is B(
,
,
)
k
kn
1 …
. Take any tape containing the argument strip but with-
out any symbols to the right of it. (It may contain symbols to the left.) The 
machine T   is begun on this tape with its reading head scanning the first | 
of k1. Then
	
1.	T   stops if and only if f(k1, …, kn) is defined.
	
2.	If T  stops, the tape contains the same argument strip as before, 
­followed by B f k
kn
(
,
,
)
1 …
. Thus, the final tape contains
	
B B
B
B
B
k
k
k
f k
k
n
n
1
2
1
…
…
(
,
,
)
	Moreover:
	
3.	The reading head is scanning the first | of f k
kn
(
,
,
)
1 …
.
	
4.	There is no nonblank symbol on the tape to the right of f k
kn
(
,
,
)
1 …
.
	
5.	During the entire computation, the reading head never scans any 
square to the left of the argument strip.
*	 For a function of one variable, the argument strip is taken to be Bk1.



327
Computability
For the sake of brevity, we shall say that the machine T   described above 
ST-computes the function f(x1, …, xn).
Thus, the additional requirement of standard Turing computability is that 
the original arguments are preserved, the machine stops if and only if the 
function is defined for the given arguments, and the machine operates on 
or to the right of the argument strip. In particular, anything to the left of the 
argument strip remains unchanged.
Proposition 5.1
Every standard Turing-computable function is Turing-computable.
Proof
Let T  be a Turing machine that ST-computes a partial function f(x1, …, xn). 
Then f is Turing-computable by the Turing machine T  PC. In fact, after T 
­operates, we obtain B
B
B
B
x
x
f x
x
n
n
1
1
…
…
(
,
,
), with the reading head at the 
leftmost | of f x
xn
(
,
,
)
1 …
. P then moves the reading head to the right of 
f x
xn
(
,
,
)
1 …
, and then C removes the original argument strip.
Proposition 5.2
Every partial recursive function is standard Turing-computable.
Proof
	
a.	Pra1 ST-computes the zero function Z(x).
	
b.	The successor function N(x) is ST-computed by PKa1Λr.
	
c.	The projection function U
x
x
x
i
n
n
i
(
,
,
)
1 …
=
 is ST-computed by R Kn−i+1Λr.
	
d.	(Substitution.) Let f(x1, …, xn) = g(h1(x1, …, xn), …, hm(x1, …, xn)) and 
assume that T    ST-computes g and Tj  ST-computes hj for 1 ≤ j ≤ m. Let 
Sj be the machine Tj    Pσn(Kn+j)nΛnr. The reader should verify that f is 
ST-computed by
	
T
S S
S
T
T
1
1
2
3
1
P K
r
P
r
P
r
(
)
n
n
n
m
m
n
m
m
+
−
…
Λ
σ Λ
σ Λ
	
	 We take advantage of the ST-computability when, storing x
xn
1,
,
,
…
 
h x
x
h x
x
n
i
n
1
1
1
(
,
,
),
,
(
,
,
)
…
…
…
 on the tape, we place (
,
,
)
x
xn
1 …
 on the tape 
to the right and compute h
x
x
i
n
+
…
1
1
(
,
,
) without disturbing what we have 
stored on the left.



328
Introduction to Mathematical Logic
	
e.	(Recursion.) Let
	
f x
x
g x
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
(
,
,
, )
(
,
,
)
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
1
1
1
1
1
0
1
…
=
…
…
+
=
…
…
n y
, ))
	
	 Assume that T  ST-computes ɡ and T    ST-computes h. Then the reader 
should verify that the machine in Figure 5.19 ST-computes f.
	
f.	Unrestricted μ-operator. Let f(x1, … xn) = μy(ɡ(x1, …, xn, y) = 0) and assume 
that T    ST-computes ɡ. Then the machine in Figure 5.20 ST-computes f.
Exercise
5.17	 For a recursion of the form
	
f
k
f y
h y f y
( )
(
)
( , ( ))
0
1
=
+
=
show how the diagram in Figure 5.19 must be modified.
Corollary 5.3
Every partial recursive function is Turing-computable.
ra1rK2 (Kn+3)n Λn+11a0 r Pr     PKn+2 1a01
r(Kn+2)n ra1r Kn+3 Λn+2r     PKn+4 1a01
r(Kn+4)n+1
1
CΛr
1
0
0
Figure 5.19 
   ra1Λn+1r    r
1ao1Λr
1
0
Pra1rσ1a01
Figure 5.20 



329
Computability
Exercise
5.18	 Prove that every partial recursive function is Turing-computable by a 
Turing machine with alphabet {a0, a1}.
In order to prove the converse of Corollary 5.3, we must arithmetize 
the language of Turing computability by assigning numbers, called Gödel 
numbers, to the expressions arising in our study of Turing machines. “R” 
and “L” are assigned the Gödel numbers 3 and 5, respectively. The tape 
symbols ai are assigned the numbers 7 + 4i, while the internal state sym-
bols qi are given the numbers 9 + 4i. For example, the blank B, which is a0, 
receives the number 7; the stroke |, which is a1, has the number 11; and the 
initial internal state symbol q0 has the number 9. Notice that all symbols 
have odd Gödel numbers, and different symbols have different numbers 
assigned to them.
As in Section 3.4, a finite sequence u0, u1, …, uk of symbols is assigned the 
Gödel number p
p
p
g u
g u
k
g uk
0
1
0
1
(
)
(
)
(
)
…
, where p0, p1, p2, … are the prime numbers 
2, 3, 5, … in ascending order and g(ui) is the Gödel number assigned to ui. For 
example, the quadruple q0a0a1q0 receives the Gödel number 293751179.
By an expression we mean a finite sequence of symbols. We have just shown 
how to assign Gödel numbers to expressions. In a similar manner, to any finite 
sequence E0, E1, …, Em of expressions we assign the number p
p
p
g E
g E
m
g Em
0
1
0
1
(
)
(
)
(
).
…
 
For example, this assigns Gödel numbers to finite sequences of Turing 
machine quadruples and to finite sequences of tape descriptions. Observe 
that the Gödel number of an expression is even and, therefore, different from 
the Gödel number of a symbol, which is odd. Moreover, the Gödel number 
of a sequence of expressions has an even number as an exponent of p0 and is, 
therefore, different from the Gödel number of an expression, which has an 
odd number as an exponent of p0.
The reader should review Sections 3.3 and 3.4, especially the functions lh(x), 
(x)i, and x * y. Assume that x is the Gödel number of a finite sequence w0, 
w1, …, wk; that is, x
p
p
p
g w
g w
k
g wk
=
…
0
1
0
1
(
)
(
)
(
), where g(wj) is the Gödel number 
of wj. Recall that lh(x) = k + 1, the length of the sequence, and (x)j = g(wj), the 
Gödel number of the jth term of the sequence. If in addition, y is the Gödel 
number of a finite sequence v0, v1, …, vm, then x * y is the Gödel number of the 
juxtaposition w0, w1, …, wk, v0, v1, …, vm of the two sequences.
Proposition 5.4
The following number-theoretic relations and functions are primitive recur-
sive. In each case, we write first the notation for the relation or function, then, 
the intuitive interpretation in terms of Turing machines, and, finally, the 
exact definition. (For the proofs of primitive recursiveness, use Proposition 
3.18 and various primitive relations and functions defined in Section 3.3. 



330
Introduction to Mathematical Logic
At a first reading, it may be advisable to concentrate on just the intuitive 
meanings and postpone the technical verification until later.)
IS(x): x is the Gödel number of an internal state symbol qu:
	
(
)
(
)
∃
=
+
<
u
x
u
u x
9
4
Sym(x): x is the Gödel number of an alphabet symbol au:
	
(
)
(
)
∃
=
+
<
u
x
u
u x
7
4
Quad(x): x is the Gödel number of a Turing machine quadruple:
	
lh( )
(( ) )
(( ) )
(( ) )
[
(( ) )
( )
( )
x
x
x
x
x
x
x
=
∧
∧
∧
∧
∨
=
∨
4
3
0
1
3
2
2
2
IS
Sym
IS
Sym
= 5]
TM(x): x is the Gödel number of a Turing machine (in the form of a finite 
sequence of appropriate quadruples):
	
(
)
(( ) )
(
)
(
)
(
[(( )
( )
( )
( )
∀
∧
>
∧∀
∀
≠
⇒
<
<
<
u
x
x
u
v
u
v
x
u
x
u
u
x
v
x
lh
lh
lh
Quad
1
u
v
u
v
x
x
x
)
(( ) )
(( ) )
(( ) ) ]
0
0
1
1
≠
∨
≠
TD(x): x is the Gödel number of a tape description:
	
x
u
x
x
u
x
u
x
u
u
u
x
u
> ∧∀
∨
∧∃
∧
<
<
1
1
(
)
[
(( ) )
(( ) )]
(
)
(( ) )
(
( )
( )
lh
lh
IS
Sym
IS
∀
⇒
+ <
<
u
x
u
x
u
x
u
)
(
(( ) )
( ))
( )
lh
lh
IS
1
Cons(x, y, z): x and y are Gödel numbers of tape descriptions α and β, and z 
is the Gödel number of a Turing machine quadruple that transforms α into β:
	
TD
TD
Quad
IS
( )
( )
( )
(
)
[
(( ) )
( )
( )
( )
( )
x
y
z
w
x
x
z
x
w
x
w
w
w
∧
∧
∧∃
∧
=
∧
<
−
lh
1
0
+
+
=
∧
∧
=
∧
=
∧
=
∧∀
1
1
2
1
2
3
( )
([
(( ) )
( )
( )
( )
( )
( )
( )
(
z
z
y
z
y
z
x
y
w
w
I
Sym
lh
lh
u
u
w
u
w
x
y
z
y
x
u
x
u
u
w
w
)
(
( )
( ) )]
[( )
( )
( )
( )
<
+
≠
∧
≠
+ ⇒
=
∨



=
∧
=
∧
lh
1
3
2
1
II
( )
( )
(
)
(
( )
( ) )
([
( )
( )
y
z
u
u
w
u
w
y
x
w
x
w
u
x
u
u
+
<
=
∧
∀
≠
∧
≠
+ ⇒
=
∧
+
<
∧
1
3
1
2
lh
lh
lh
lh
lh
lh
lh
( )
( )]
[
( )
( )
( )
( )
])]
y
x
w
x
y
x
y w
=
∨
+
=
∧
=
+ ∧
=
∨






+
2
1
7
2
III
[( )
{[
( )
( )
( )
( )
( )
( )
(
z
w
y
z
y
x
y
x
w
w
w
2
1
3
1
5
0
=
∧
≠
∧
=
∧
=
∧
=
∧∀
−
−


lh
lh
u
u
w
u
w
y
x
w
y
z
y
u
x
u
u
)
(
( )
( ) )]
[
( )
( )
( )
( )
<
≠
−∧
≠
⇒
=
∨
=
∧
=
∧
=
∧
lh
lh
 1
0
7
0
3
1
( )
( )
(
)
( )
( ) ]}])]
( )
y
x
u
y
x
u
x
u
u
=
+ ∧∀
=






< <
+
lh
lh
1
0
1



331
Computability
I corresponds to a quadruple qjaiakqr, II to a quadruple qjaiRqr, and III to a 
quadruple qjaiLqr.
NTD(x): x is the Gödel number of a numerical tape description—that is, a 
tape description in which the tape has the form E E
1
2
k
, where each of E1 and 
E2 is empty or consists entirely of blanks, and the location of the reading 
head is arbitrary:
	
TD
Sym
( )
(
)
(
(( ) )
( )
( )
)
(
)
(
( )
( )
x
u
x
x
x
u
v
u
x
u
u
u
u
x
∧∀
⇒
=
∨
=
∧∀
∀
<
<
lh
lh
7
11
)
(
)
(
( )
( )
( )
)
(
)
( )
( )
v
x
w
x
u
w
v
u
w
u
v
v
w
x
x
x
u
<
<
∀
<
∧
<
∧
=
∧
=
⇒
≠
∧∃
lh
lh
11
11
7
<
=
lh ( )(( )
)
x
u
x
11
Stop (x, z): z is the Gödel number of a Turing machine T   
    and x is the Gödel 
number of a tape description α such that T   stops at α:
	
TM
TD
IS
( )
( )
(
)
[
(( ) )
(
)
((( ) )
( )
( )
( )
z
x
u
x
v
z
x
u
x
u
v
z
v
u
∧
∧¬ ∃
∧∃
=
<
<
lh
lh
0
∧
=
+
(( ) )
( )
)]
z
x
v
u
1
1
Comp(y, z): z is the Gödel number of a Turing machine T   and y is the Gödel 
number of a computation of T   
         :
	
y
z
u
y
y
z
u
u
y
u
y
u
>
∧
∧∀
∧
∧
∀
<
−
<
1
1
TM
TD
Stop
( )
(
)
(( ) )
(( )
, )
(
)
( )
( )
lh
lh
lh

( )
( )
(( ) )
(
)
(( ) ,( )
,( ) )
(
)
(
y
w
z
u
u
w
v
y
w
y
y
z
v
−
<
+
<
∃
∧
∀
1
1
0
lh
lh
Cons
IS((( ) ) )
(( ) )
)
y
y
v
v
0
0
9
⇒
=
Num(x): The Gödel number of the word x—that is, of |x+1:
	
Num( )
x
pu
u x
=
≤∏
11
TR(x1, …, xn): The Gödel number of the tape representation (
,
,
)
x
xn
1 …
 of the 
n-tuple (x1, …, xn):
	
TR
Num
Num
Num
(
,
,
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
x
n
n
1
1
7
2
7
7
2
2
2
…
=
∗
…
*
*
*
*
*
U(y): If y is the Gödel number of a computation that results in a numerical 
tape description, then U(y) is the number represented on that final tape.*
	
U y
y
u
y
y
u
h y
( )
(|(( )
)
|)
(( )
( )
( )
)
=
−







−
<
−
−
∑
lh
lh
ℓ



1
1
11
1
sg
*	 If y is not the Gödel number of a computation that yields a numerical tape description, U(y) 
is defined, but its value in such cases will be of no significance.



332
Introduction to Mathematical Logic
[Let w be the number, represented by |w+1, on the final tape. The calculation 
of U(y) tallies a 1 for every stroke | that appears on the final tape. This yields 
a sum of w + 1, and then 1 is subtracted to obtain w.]
Tn(z, x1, …, xn, y): y is the Gödel number of a computation of a Turing 
machine with Gödel number z such that the computation begins on the tape 
(
,
,
)
x
xn
1 …
, with the reading head scanning the first | in x1, and ends with a 
numerical tape description:
	
Comp
TR
NTD
( , )
( )
*
(
,
,
)
(( )
)
( )
y z
y
x
x
y
n
y
∧
=
…
∧
−
0
9
1
1
2
lh

When n = 1, replace TR(x1, …, xn) by Num(x1). (Observe that, if Tn(z, x1, …, xn, y1) 
and Tn(z, x1, …, xn, y2), then y1 = y2, since there is at most one computation of a 
Turing machine starting with a given initial tape.)
Proposition 5.5
If T   is a Turing machine that computes a number-theoretic function f(x1, …, xn) 
and e is a Gödel number of T,  then*
	
f x
x
U
yT e x
x
y
n
n
n
(
,
,
)
(
( ,
,
,
, ))
1
1
…
=
…
µ
Proof
Let k1, …, kn be any natural numbers. Then f(k1, …, kn) is defined if and only 
if there is a computation of T  beginning with (
,
,
)
k
kn
1 …
 and ending with 
a numerical tape description—that is, if and only if (∃y)Tn(e, k1, …, xn, y). So, 
f(k1, …, kn) is defined if and only if μyTn(e, k1, …, kn, y) is defined. Moreover, 
when f(k1, …, kn) is defined, μyTn(e, k1, …, kn, y) is the Gödel number of a 
computation of T   beginning with (
,
,
)
k
kn
1 …
 and U(μyTn(e, k1, …, kn, y)) is the 
value yielded by the computation, namely, f(k1, …, kn).
Corollary 5.6
Every Turing-computable function is partial recursive.
Proof
Assume f(x1, …, xn) is Turing-computable by a Turing machine with Gödel 
number e. Then f(x1, …, xn) = U(μyTn(e, x1, …, xn, y)). Since Tn is primitive 
*	 Remember that an equality between two partial functions means that, whenever one of them 
is defined, the other is also defined and the two functions have the same value.



333
Computability
­recursive, μyTn(e, x1, …, xn, y) is partial recursive. Hence, U(μyTn(e, x1, …, xn, y)) 
is partial recursive.
Corollary 5.7
The Turing-computable functions are identical with the partial recursive 
functions.
Proof
Use Corollaries 5.6 and 5.3.
Corollary 5.8
Every total partial recursive function is recursive.
Proof
Assume that the total partial recursive function f(x1, …, xn) is Turing-
computable by the Turing machine with Gödel number e. Then, for all x1, …, 
xn, (∃y)Tn(e, x1, …, xn, y). Hence, μyTn(e, x1, …, xn, y) is produced by an application 
of the restricted μ-operator and is, therefore, recursive. So, U(μyTn(e, x1, …, 
xn, y)) is also recursive. Now use Proposition 5.5.
Corollary 5.9
For any total number-theoretic function f, f is recursive if and only if f is 
Turing-computable.
Proof
Use Corollaries 5.7–5.8 and Exercise 5.15.
Church’s thesis amounts to the assertion that the recursive functions 
are the same as the computable total functions. By Corollary 5.9, this is 
equivalent to the identity, for total functions, of computability and Turing 
computability. This strengthens the case for Church’s thesis because of the 
plausibility of the identification of Turing computability with computabil-
ity. Let us now widen Church’s thesis to assert that the computable func-
tions (partial or total) are the same as the Turing-computable functions. By 
Corollary 5.7, this implies that a function is computable if and only if it is 
partial recursive.



334
Introduction to Mathematical Logic
Corollary 5.10
Any number-theoretic function is Turing-computable if and only if it is stan-
dard Turing-computable.
Proof
Use Proposition 5.1, Corollary 5.6, and Proposition 5.2.
Corollary 5.11 (Kleene’s Normal Form Theorem)
As z varies over all natural numbers, U(μyTn(z, x1, …, xn, y)) enumerates with 
repetitions all partial recursive functions of n variables.
Proof
Use Corollary 5.3 and Proposition 5.5. The fact that every partial recur-
sive function of n variables reappears for infinitely many z follows from 
Exercise  5.7. (Notice that, when z is not the Gödel number of a Turing 
machine, there is no y such that Tn(z, x1, …, xn, y), and, therefore, the corre-
sponding partial recursive function is the empty function.*)
Corollary 5.12
For any recursive relation R(x1, …, xn, y), there exist natural numbers z0 and v0 
such that, for all natural numbers x1, …, xn:
	
a.	(∃y)R(x1, …, xn, y) if and only if (∃y)Tn(z0, x1, …, xn, y)
	
b.	(∀y)R(x1, …, xn, y) if and only if (∀y)¬Tn(v0, x1, …, xn, y)
Proof
	
a.	The function f(x1, …, xn) = μyR(x1, …, xn, y) is partial recursive. Let z0 
be a Gödel number of a Turing machine that computes f. Hence, f(x1, 
…, xn) is defined if and only if (∃y)Tn(z0, x1, …, xn, y). But f(x1, …, xn) is 
defined if and only if (∃y)R(x1, …, xn, y).
	
b.	Applying part (a) to the recursive relation ¬R(x1, …, xn, y), we obtain 
a number v0 such that:
	
(
)
(
,
,
, )
(
)
(
,
,
,
, )
∃
¬
…
∃
…
y
R x
x
y
y T v
x
x
y
n
n
n
1
0
1
if and only if
Now take the negations of both sides of this equivalence.
*	 The empty function is the empty set ∅. It has the empty set as its domain.



335
Computability
Exercise
5.19	 Extend Corollary 5.12 to two or more quantifiers. For example, if R(x1, …, 
xn, y, z) is a recursive relation, show that there are natural numbers z0 
and v0 such that, for all x1, …, xn:
	a.	 (∀z)(∃y)R(x1, …, xn, y, z) if and only if (∀z)(∃y)Tn+1(z0, x1, …, xn, z, y).
	b.	 (∃z)(∀y)R(x1, …, xn, y, z) if and only if (∃z)(∀y)¬Tn+1(v0, x1, …, xn, z, y).
Corollary 5.13
	
a.	(∃y)Tn(x1, x1, x2, …, xn, y) is not recursive.
	
b.	(∃y)Tn(z, x1, …, xn, y) is not recursive.
Proof
	
a.	Assume (∃y)Tn(x1, x1, x2, …, xn, y) is recursive. Then the relation ¬(∃y)
Tn(x1, x1, x2, …, xn, y) ∧ z = z is recursive. So, by Corollary 5.12(a), there 
exists z0 such that
	
(
)( (
)
(
,
,
,
,
, )
)
(
)
(
,
,
∃
¬ ∃
…
∧
=
∃
z
y T x x x
x
y
z
z
z T z
x
n
n
n
1
1
2
0
1
if and only if
x
x
z
n
2,
,
, )
…
	
	 Hence, since z obviously can be omitted on the left,
	
¬ ∃
…
∃
…
(
)
(
,
,
,
,
, )
(
)
(
,
,
,
,
, )
y T x x x
x
y
z T z
x x
x
z
n
n
n
n
1
1
2
0
1
2
if and only if
	
	 Let x1 = x2 = ⋯ = xn = z0. Then we obtain the contradiction
	
¬ ∃
…
∃
…
(
)
(
,
,
,
,
, )
(
)
(
,
,
,
,
, )
y T z
z
z
z
y
z T z
z
z
z
z
n
n
0
0
0
0
0
0
0
0
if and only if
	
b.	If (∃y)Tn(z, x1, x2, …, xn, y) were recursive, so would be, by substitu-
tion, (∃y)Tn(x1, x1, x2, …, xn, y), contradicting part (a).
Exercises
5.20	 Prove that there is a partial recursive function ɡ(z, x) such that, for 
any partial recursive function f(x), there is a number z0 for which f(x) = 
ɡ(z0, x) holds for all x. Then show that there must exist a number v0 such 
that ɡ(v0, v0) is not defined.
5.21	 Let h1(x1, …, xn), …, hk(x1, …, xn) be partial recursive functions, and let 
R1(x1, …, xn), …, Rk(x1, …, xn) be recursive relations that are exhaustive 



336
Introduction to Mathematical Logic
(i.e., for any x1, …, xn, at least one of the relations holds) and pairwise 
mutually exclusive (i.e., for any x1, …, xn, no two of the relations hold). 
Define
	
g(
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
,
,
x
x
h x
x
R x
x
h x
x
R x
x
n
n
n
k
n
k
n
1
1
1
1
1
1
1
…
=
…
…
…
…
if
if
)



	
	 Prove that ɡ is partial recursive.
5.22	 A partial function f(x) is said to be recursively completable if there is a 
recursive function h(x) such that, for every x in the domain of f, h(x) = f(x).
	a.	 Prove that μy T1(x, x, y) is not recursively completable.
	b.	 Prove that a partial recursive function f(x) is recursively complet-
able if the domain D of f is a recursive set—that is, if the property 
“x ∈ D” is recursive.
	c.	 Find a partial recursive function f(x) that is recursively completable 
but whose domain is not recursive.
5.23	 If R(x, y) is a recursive relation, prove that there are natural numbers z0 
and v0 such that
	a.	 ¬[(∃y)R(z0, y) ⇔ (∀y) ¬T1(z0, z0, y)]
	b.	 ¬[(∀y)R(v0, y) ⇔ (∃y)T1(v0, v0, y)]
5.24	 If S(x) is a recursive property, show that there are natural numbers z0 
and v0 such that
	a.	 ¬[S(z0) ⇔ (∀y) ¬T1(z0, z0, y)]
	b.	 ¬[S(v0) ⇔ (∃y)T1(v0, v0, y)]
5.25	 Show that there is no recursive function B(z, x1, …, xn) such that, if z is a 
Gödel number of a Turing number T    and k1, …, kn are natural numbers 
for which fT,   n (k1, …, kn) is defined, then the number of steps in the com-
putation of fT,   n(k1, …, kn) is less than B(z, k1, …, kn).
Let T   be a Turing machine. The halting problem for T   is the problem of 
determining, for each tape description β, whether T    is applicable to β, that 
is, whether there is a computation of T   that begins with β.
We say that the halting problem for T   is algorithmically solvable if there is 
an algorithm that, given a tape description β, determines whether T    is appli-
cable to β. Instead of a tape description β, we may assume that the algorithm 
is given the Gödel number of β. Then the desired algorithm will be a comput-
able function HT   such that
	
H
x
T
T
( ) =
0
if
is the Godel number of a tape description
to which
is a
x

β
pplicable
otherwise
1






337
Computability
If we accept Turing algorithms as exact counterparts of algorithms (that is, 
the extended Church’s thesis), then the halting problem for T   is algorithmi-
cally solvable if and only if the function HT    is Turing-computable, or equiva-
lently, by Corollary 5.9, recursive. When the function HT    is recursive, we say 
that the halting problem for T    is recursively solvable. If HT    is not recursive, we 
say that the halting problem for T    is recursively unsolvable.
Proposition 5.14
There is a Turing machine with a recursively unsolvable halting problem.
Proof
By Proposition 5.2, let T    be a Turing machine that ST-computes the partial 
recursive function μyT1(x, x, y). Remember that, by the definition of standard 
Turing computability, if T    is begun on the tape consisting of only x with its 
reading head scanning the leftmost |, then T   stops if and only if μyT1(x, x, y) 
is defined. Assume that T    has a recursively solvable halting problem, that is, 
that the function HT   is recursive. Recall that the Gödel number of the tape 
description q x
0  is 29 * Num(x). Now,
	
(
)
( , , )
( , , )
,
∃y T x x y
yT x x y
1
1
if and only if
isdefined
if and only if
b
µ
T
egun on
performs a computation
if and only if
* Num
q x
H
x
0
9
2
0
,
(
( ))
T
=
Since HT   , Num, and * are recursive, (∃y)T1(x, x, y) is recursive, contradicting 
Corollary 5.13(a) (when n = 1).
Exercises
5.26	 Give an example of a Turing machine with a recursively solvable halt-
ing problem.
5.27	 Show that the following special halting problem is recursively unsolvable: 
given a Gödel number z of a Turing machine T   and a natural number 
x, determine whether T    is applicable to q x
0 .
5.28	 Show that the following self-halting problem is recursively unsolvable: 
given a Gödel number z of a Turing machine T,  determine whether T     is 
applicable to q z
0 .
5.29	 The printing problem for a Turing machine T    and a symbol ak is the 
problem of determining, for any given tape description α, whether T, 
begun on α, ever prints the symbol ak. Find a Turing machine T   and a 
symbol ak for which the printing problem is recursively unsolvable.



338
Introduction to Mathematical Logic
5.30	 Show that the following decision problem is recursively unsolvable: 
given any Turing machine T,  if T   is begun on an empty tape, deter-
mine whether T   stops (that is, whether T    is applicable to q0B).
5.31D	Show that the problem of deciding, for any given Turing machine, 
whether it has a recursively unsolvable halting problem is itself recur-
sively unsolvable.
To deal with more intricate decision problems and other aspects of the 
theory of computability, we need more powerful tools. First of all, let us 
introduce the notation
	
ϕ
µ
z
n
n
n
n
x
x
U
yT z x
x
y
(
,
,
)
(
( ,
,
,
, ))
1
1
…
=
…
Thus, by Corollary 5.11, ϕ
ϕ
ϕ
0
1
2
n
n
n
,
,
, … is an enumeration of all partial recur-
sive functions of n variables. The subscript j is called an index of the func-
tion ϕj
n. Each partial recursive function of n variables has infinitely many 
indices.
Proposition 5.15 (Iteration Theorem or s-m-n Theorem)
For any positive integers m and n, there is a primitive recursive function 
s
z y
y
n
m
m
( ,
,
,
)
1 …
 such that
	
ϕ
ϕ
z
m n
n
m
s
z y
y
n
n
x
x
y
y
x
x
nm
m
+
…
…
…
=
…
(
,
,
,
,
,
)
(
,
,
)
( ,
,
,
)
1
1
1
1
Thus, not only does assigning particular values to z, y1, …, ym in 
ϕz
m n
n
m
x
x
y
y
+
…
…
(
,
,
,
,
,
)
1
1
 yield a new partial recursive function of n vari-
ables, but also the index of the resulting function is a primitive recursive 
function of the old index z and of y1, …, ym.
Proof
If T    is a Turing machine with Gödel number z, let T y
ym
1 ,
,
…
 be a Turing 
machine that, when begun on (
,
,
)
x
xn
1 …
, produces (
,
,
,
,
,
)
x
x
y
y
n
m
1
1
…
…
, 
moves back to the leftmost | of x1, and then behaves like T.  Such a machine 
is defined by the diagram
	
Rr a r
r a r
r
r a r
r
(
)
(
)
(
)
1
1
1
y
y
ym
1
2
1
1
1
+
+
+
…
L T
The Gödel number s
z y
y
n
m
m
( ,
,
,
)
1 …
 of this Turing machine can be effectively 
computed and, by Church’s thesis, would be partial recursive. In fact, sn
m can 
be computed by a primitive recursive function ɡ(z, y1, …, ym) defined in the 



339
Computability
following manner. Let t = y1 + ⋯ + ym + 2m + 1. Also, let u(i) = 29+4i3751179+4i 
and v(i) = 29+4i31153713+4i. Notice that u(i) is the Gödel number of the quadru-
ple qiB|qi and v(i) is the Gödel number of the quadruple qi|Rqi+1. Then take 
ɡ(z, y1, …, ym) to be
	
[
]
|
|
( )
2
3
5
7
2 3
5 7
2 3 5 7
2
3
5 7
2
3 5 7
2
4
9 11 3 9
9 7 3 13
13 11 3 9
13 7 7 17
*
p i
u i
i
−
=2
2
2
3
2
3 5 7
2
4
1
9 4
1 3
7 3 9 4
1
4
1
2
y
i
v i
i
y
u
p
p
y
y
+
−
−
+
∏
∗
+
+
+
+
|
|
( )
| (
)|
(
)
(
)
*
( )
| (
)|
( )
(
)
i
i y
y
y
i
y
v i
p
y
y
=
+
+
+
−
+
+
∏
+
+
+
+
1
1
2
1
9 4
5
7 3 9
4
4
2
4
1
2
3 5 7
2
1
2
*
4
2
6
9 4
1 2
1
7 3 9 4
1 2
1
1
1
22
3 5 7
(
)
(
)
(
)
y
y
y
ym
m
y
ym
m
+
+
+
+
+
−+
−
+
+
+
−+
…
*
*
*


p
p
i
y
y
m
u i
i y
y
m
y
y
m
i
y
m
m
m
2
2
2
2
2
1
1
1
1
1
1
| (
)|
( )
| (
−
+
+
+
=
+
+
+
+
+
+
−
−
−
∏



+
+
+
+
−
+
+
+
+
+
 y
m
v i
m
t
t
t
t
1
9 4
11 5 9 4
9 4
7 5 9 4
1
9
2
1
2
3
5 7
2
3 5 7
2
2
3
5
)|
( )
(
)
*
+
+
+
+
+
+
+
+
+
4
1
11 5 9 4
9 4
1
7 3 9 4
2
9 4
2
7 3
3
5 7
2
3 5 7
2
3 5 7
7
11
(
)
(
)
(
)
(
)
.
t
t
t
t
t
9 4
3
0
4
3
1
2
3
4
3
2
3
5
7
+
+
+
+
+
+
(
)
(( ) )
(
) (( ) )
(( ) )
(( ) )
(
)
t
z i
t
z i
z i
z i
t
pi
*
i
z
=∏
0
δ( ( ))
lh
ɡ is primitive recursive by the results of Section 3.3. When z is not a Gödel 
number of a Turing machine, ϕz
m n
+  is the empty function and, therefore, 
s
z y
y
n
m
m
( ,
,
,
)
1 …
 must be an index of the empty function and can be taken to 
be 0. Thus, we define
	
s
z y
y
z y
y
TM z
n
m
m
m
( ,
,
,
)
( ,
,
)
( )
,
1
1
0
…
=
…



g
if
otherwise
Hence, sn
m is primitive recursive.
Corollary 5.16
For any partial recursive function f(x1, …, xn, y1, …, ym), there is a recursive 
function g(y1, …, ym) such that
	
f x
x
y
y
x
x
n
m
g y
y
n
n
m
(
,
,
,
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
1
1
1
1
…
…
=
…
…
ϕ



340
Introduction to Mathematical Logic
Proof
Let e be an index of f. By Proposition 5.15,
	
ϕ
ϕ
e
m n
n
m
s
e y
y
n
x
x
y
y
x
x
nm
m
+
…
…
…
=
…
(
,
,
,
,
,
)
(
,
,
)
( ,
,
,
)
1
1
1
1
Let g y
y
s
e y
y
m
n
m
m
(
,
,
)
( ,
,
,
)
1
1
…
=
…
.
Examples
	
1.	Let G(x) be a fixed partial recursive function with nonempty 
domain. Consider the following decision problem: for any u, deter-
mine whether ϕu
G
1 =
. Let us show that this problem is recursively 
unsolvable, that is, that the property R(u), defined by ϕu
G
1 =
, is not 
recursive. Assume, for the sake of contradiction, that R is recursive. 
Consider the function f(x, u) = G(x) · N(Z(μyT1(u, u, y))). (Recall that 
N(Z(t)) = 1 for all t). Applying Corollary 5.16 to f(x, u), we obtain a 
recursive function g(u) such that f x u
x
g u
( , )
( )
( )
= ϕ1
. For any fixed 
u
G
g u
,
( )
ϕ1
=
 if and only if (∃y)T1(u, u, y). (Here, we use the fact that G 
has nonempty domain.) Hence, (∃y)T1(u, u, y) if and only if R(g(u)). 
Since R(g(u)) is recursive, (∃y)T1(u, u, y) would be recursive, contra-
dicting Corollary 5.13(a).
	
2.	A universal Turing machine. Let the partial recursive function 
U(μyT1(z, x, y)) be computed by a Turing machine V     with Gödel num-
ber e. Thus, U(μyT1(z, x, y)) = U(μyT2(e, z, x, y)). V    is universal in the 
following sense. First, it can compute every partial recursive func-
tion f(x) of one variable. If z is a Gödel number of a Turing machine 
that computes f, then, if V   begins on the tape ( , )
z x , it will compute 
U(μyT1(z, x, y)) = f(x). Further, V   can be used to compute any partial 
recursive function h(x1, …, xn). Let v0 be a Gödel number of a Turing 
machine that computes h, and let f(x) = h((x)0, (x)1, …, (x)n−1). Then 
h x
x
f p
p
n
x
n
xn
(
,
,
)
1
0
1
1
…
=
…
(
)
−. By applying Corollary 5.16 to the partial 
recursive function U(μyTn(v, (x)0, (x)1, …, (x)n−1, y)), we obtain a recur-
sive function g(v) such that U
yT v x
x
x
y
x
n
n
g v
(
( ,( ) ,( ) ,
, ( )
, ))
( )
( )
µ
ϕ
0
1
1
1
…
=
−
. 
Hence, f x
x
g v
( )
( )
( )
= ϕ1
. So h(x1, …, xn) is computed by applying V   to the 
tape g v
p
p
x
n
xn
(
),
0
0
1
1 …
(
)
−.
Exercises
5.32	 Find a superuniversal Turing machine V    * such that, for any Turing 
machine T,  if z is a Gödel number of T   and x is the Gödel number of 
an initial tape description α of T,  then V    * is applicable to q z x
0( , ) if and 



341
Computability
only if T   is applicable to α; moreover, if T,  when applied to α, ends 
with a tape description that has Gödel number w, then V     *, when applied to 
q z x
0( , ), produces w.
5.33	 Show that the following decision problem is recursively unsolvable: for 
any u and v, determine whether ϕ
ϕ
u
v
1
1
=
.
5.34	 Show that the following decision problem is recursively unsolv-
able: for any u, determine whether ϕu
1 has empty domain. (Hence, 
the condition in Example 1 above, that G(x) has nonempty domain is 
unnecessary).
5.35	 a. Prove that there is a recursive function g(u, v) such that
	
ϕ
ϕ
ϕ
g u v
u
v
x
x
x
( , )( )
( )
( )
1
1
1
=
⋅
	b.	 Prove that there is a recursive function C(u, v) such that
	
ϕ
ϕ ϕ
C u v
u
v
x
x
( , )( )
(
( ))
1
1
1
=
5.4  The Kleene–Mostowski Hierarchy: 
Recursively Enumerable Sets
Consider the following array, where R(x1, …, xn, y1, …, ym) is a recursive 
relation:
	
R x
x
y R x
x
y
y R x
x
y
y
y R
n
n
n
(
,
,
)
(
) (
,
,
,
)
(
) (
,
,
,
)
(
)(
) (
1
1
1
1
1
1
1
1
2
…
∃
…
∀
…
∃
∀
x
x
y
y
y
y R x
x
y
y
y
y
y R
n
n
1
1
2
1
2
1
1
2
1
2
3
,
,
,
,
)
(
)(
) (
,
,
,
,
)
(
)(
)(
) (
…
∀
∃
…
∃
∀
∃
x
x
y
y
y
y
y
y R x
x
y
y
y
n
n
1
1
2
3
1
2
3
1
1
2
3
,
,
,
,
,
)
(
)(
)(
) (
,
,
,
,
,
)
…
∀
∃
∀
…


Let ∑=
=
0
0
n
n
Π
 the set of all n-place recursive relations. For k > 0, let ∑k
n be the 
set of all n-place relations expressible in the prenex form (∃y1)(∀y2) … (Q yk)
R(x1, …, xn, y1, …, yk), consisting of k alternating quantifiers beginning with an 
existential quantifier and followed by a recursive relation R. (Here, “(Q yk)” 
denotes (∃yk) or (∀yk), depending on whether k is odd or even.) Let Πk
n be the 
set of all n-place relations expressible in the prenex form (∀y1)(∃y2) … (Qyk)
R(x1, …, xn, y1, …, yk), consisting of k alternating quantifiers beginning with 



342
Introduction to Mathematical Logic
a universal quantifier and followed by a recursive relation R. Then the array 
above can be written
	
0
1
1
2
2
3
3
n
n
n
n
n
n
n
∑
∑∏
∑∏
∑∏


This array of classes of relations is called the Kleene–Mostowski hierarchy, or 
the arithmetical hierarchy.
Proposition 5.17
	
a.	Every relation expressible in any form listed above is expressible in all 
the forms in lower rows; that is, for all j > k,
	
⊆
∩
⊆
∩
∑∑∏
∏∑∏
k
n
j
n
j
n
k
n
j
n
j
n
and
	
b.	There is a relation of each form, except ∑0
n, that is not expressible in the 
other form in the same row and, hence, by part (a), not in any of the 
rows above; that is, for k > 0,
	
−
≠∅
−
≠∅
∑∏
∏∑
k
n
k
n
k
n
k
n
and
	
c.	Every arithmetical relation is expressible in at least one of these forms.
	
d.	(Post) For any relation Q(x1, …, xn), Q is recursive if and only if both Q 
and ¬Q are expressible in the form (∃y1)R(x1, …, xn, y1), where R is recur-
sive; that is, ∑∩
= ∑
1
1
0
n
n
n
Π
.



343
Computability
	
e.	If Q
k
n
1 ∈∑ and Q
k
n
2 ∈∑, then Q1 ∨ Q2 and Q1 ∧ Q2 are in ∑k
n. If Q
k
n
1 ∈Π  and 
Q
k
n
2 ∈Π , then Q1 ∨ Q2 and Q1 ∧ Q2 are in Πk
n.
	
f.	In contradistinction to part (d), if k > 0, then
	
∩







−
∪







≠∅
+
+
∑
∑
∏
∏
k
n
k
n
k
n
k
n
1
1
Proof
	
a.	(∃z1)(∀y1) … (∃zk)(∀yk)R(x1, …, xn, z1, y1, …, zk, yk) ⇔
	
(
)(
)(
)
(
)(
)( (
,
,
,
,
,
,
,
)
)
(
∀
∃
∀
… ∃
∀
…
…
∧
=
⇔
∃
u
z
y
z
y
R x
x
z y
z
y
u
u
k
k
n
k
k
1
1
1
1
1
z
y
z
y
u R x
x
z y
z
y
u
u
k
k
n
k
k
1
1
1
1
1
)(
)
(
)(
)(
)( (
,
,
,
,
,
,
,
)
)
∀
… ∃
∀
∃
…
…
∧
=
	
	 Hence, any relation expressible in one of the forms in the array is 
expressible in both forms in any lower row.
	
b.	Let us consider a typical case, say ∑3
n. Take the relation (∃v)(∀z)(∃y)
Tn+2(x1, x1, x2, …, xn, v, z, y), which is in ∑3
n. Assume that this is in Π3
n, 
that is, it is expressible in the form (∀v)(∃z)(∀y)R(x1, …, xn, v, z, y), 
where R is recursive. By Exercise 5.19, this relation is equivalent to (∀v)
(∃z)(∀y) ¬Tn+2(e, x1, …, xn, v, z, y) for some e. When x1 = e, this yields a 
contradiction.
	
c.	Every wf of the first-order theory S can be put into prenex normal form. 
Then, it suffices to note that (∃u)(∃v)R(u, v) is equivalent to (∃z)R((z)0, 
(z)1), and (∀u)(∀v)R(u, v) is equivalent to (∀z)R((z)0, (z)1). Hence, suc-
cessive quantifiers of the same kind can be condensed into one such 
quantifier.
	
d.	If Q is recursive, so is ¬Q, and, if P(x1, …, xn) is recursive, then P(x1, …, 
xn) ⇔ (∃y)(P(x1, …, xn) ∧ y = y). Conversely, assume Q is expressible as 
(∃y)R1(x1, …, xn, y) and ¬Q as (∃y)R2(x1, …, xn, y), where the relations R1 
and R2 are recursive. Hence, (∀x1) … (∀xn) (∃y)(R1(x1, …, xn, y) ∨ R2(x1, 
…, xn, y)). So, ψ(x1, …, xn) = μy (R1(x1, …, xn, y) ∨ R2(x1, …, xn, y)) is recur-
sive. Then, Q(x1, …, xn) ⇔ R1(x1, …, xn, ψ(x1, …, xn)) and, therefore, Q is 
recursive.
	
e.	Use the following facts. If x is not free in A.
	
⊢
⊢
⊢
(
)(
)
(
(
)
),
(
)(
)
(
(
)
),
(
)(
)
(
(
∃
∨
⇔
∨∃
∃
∧
⇔
∧∃
∀
∨
⇔
∨∀
x
x
x
x
x
A
B
A
B
A
B
A
B
A
B
A
x
x
x
)
),
(
)(
)
(
(
)
)
B
A
B
A
B
⊢∀
∧
⇔
∧∀



344
Introduction to Mathematical Logic
	
f.	We shall suggest a proof in the case n = 1; the other cases are then 
easy consequences. Let Q x
k
k
( )∈∑−∏
1
1. Define P(x) as (∃z) [(x = 2z ∧ 
Q(z)) ∨ (x = 2z + 1 ∧ ¬Q(z))]. It is easy to prove that P
k
k
∉∑∪
1
1
Π  and that 
P
k
∈∑+1
1 . Observe that P(x) holds if and only if
	
(
)(
( ))
((
)
(
)
(
)(
( )))
∃
=
∧
∨
∃
=
+
∧∀
=
+
⇒¬
<
z x
z
Q z
z
x
z
z x
z
Q z
z x
2
2
1
2
1
Hence, P
k
∈
+
Π
1
1  (Rogers, 1959).
Exercises
5.36	 For any relation W of n variables, prove that W
k
n
∈∑ if and only if 
W
k
n
∈∏, where W is the complement of W with respect to the set of all 
n-tuples of natural numbers.
5.37	 For each k > 0, find a universal relation Vk in ∑+
k
n 1; that is, for any rela-
tion W of n variables: (a) if W
k
n
∈∑, then there exists z0 such that, for all 
x1, …, xn, W(x1, …, xn) if and only if Vk(z0, x1, …, xn); and (b) if W
k
n
∈∏, 
there exists v0 such that, for all x1, …, xn, W(x1, …, xn) if and only if ¬Vk(v0, 
x1, …, xn). [Hint: Use Exercise 5.19.]
The s-m-n theorem (Proposition 5.15) enables us to prove the following 
basic result of recursion theory.
Proposition 5.18 (Recursion Theorem)
If n > 1 and f(x1, …, xn) is a partial recursive function, then there exists a 
­natural number e such that
	
f x
x
e
x
x
n
e
n
n
(
,
,
, )
(
,
,
)
1
1
1
1
1
…
=
…
−
−
−
ϕ
Proof
Let d be an index of f x
x
s
x
x
n
n
n
n
(
,
,
,
(
,
))
1
1
1
1
…
−
−
. Then
	
f x
x
s
x
x
x
x
x
n
n
n
n
d
n
n
n
(
,
,
,
(
,
))
(
,
,
,
)
1
1
1
1
1
1
…
=
…
−
−
−
ϕ
By the s-m-n theorem, ϕ
ϕ
d
n
n
s
d x
n
n
x
x
x
x
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
( ,
)
1
1
1
1
1
1
…
=
…
−
−
−. Let e
s
d d
n
=
−1
1 ( , ). 
Then
	
f x
x
e
f x
x
s
d d
x
x
d
n
n
n
d
n
n
s
(
,
,
, )
(
,
,
,
( , ))
(
,
,
, )
1
1
1
1
1
1
1
1
…
=
…
=
…
=
−
−
−
−
ϕ
ϕ
n
d d
n
n
e
n
n
x
x
x
x
−
−
−
−
−
…
=
…
1
1
1
1
1
1
1
1
( , )(
,
,
)
(
,
,
)
ϕ



345
Computability
Corollary 5.19 (Fixed-Point Theorem)
If h(x) is recursive, then there exists e such that ϕ
ϕ
e
h e
1
1
=
( ).
Proof
Applying the recursion theorem to f x u
x
h u
( , )
( )
( )
= ϕ1
, we obtain a number e 
such that f x e
x
e
( , )
( )
= ϕ1
. But f x e
x
h e
( , )
( )
( )
= ϕ1
.
Corollary 5.20 (Rice’s Theorem) (Rice, 1953)
Let F   be a set consisting of at least one, but not all, partial recursive func-
tions of one variable. Then the set A
u
u
=
∈
{ |
}
ϕ1
F  is not recursive.
Proof
By hypothesis, there exist numbers u1 and u2 such that u1 ∈ A and u2 ∉ A. 
Now assume that A is recursive. Define
	
h x
u
x
A
u
x
A
( ) =
∉
∈



1
2
if
if
Clearly, h(x) ∈ A if and only if x ∉ A. h is recursive, by Proposition 3.19. By the 
fixed-point theorem, there is a number e such that ϕ
ϕ
e
h e
1
1
=
( ). Then we obtain 
a contradiction as follows:
	
e
A
h e
A
e
h e
∈
∈
∈
∈
if and only if
if and only if
if and only if
if a
ϕ
ϕ
1
1
F
F
( )
( )
nd only if
e
A
∉
Rice’s theorem can be used to show the recursive unsolvability of various 
decision problems.
Example
Consider the following decision problem: for any u, determine whether ϕu
1 
has an infinite domain. Let F  be the set of all partial recursive functions of 
one variable that have infinite domain. By Rice’s theorem, { |
}
u
F
u
ϕ1 ∈
 is not 
recursive. Hence, the problem is recursively undecidable.
Notice that Example 1 on page 340 and Exercise 5.34 can be handled in the 
same way.



346
Introduction to Mathematical Logic
Exercises
5.38	 Show that the following decision problems are recursively unsolvable.
	a.	 For any u, determine whether ϕu
1 has infinite range.
	b.	 For any u, determine whether ϕu
1 is a constant function.
	c.	 For any u, determine whether ϕu
1 is recursive.
5.39	 a. Show that there is a number e such that the domain of ϕe
1 is {e}.
	b.	 Show that there is a number e such that the domain of ϕe
1 is ω −{e}.
5.40	 This exercise will show the existence of a recursive function that is not 
primitive recursive.
	a.	 Let 
x

 be the largest integer less than or equal to x. Show that 
x

 is defined by the recursion
	
κ
κ
κ
κ
( )
(
)
( )
|(
)
( ( )
) |
0
0
1
1
1 2
=
+
=
+
+
−
+
x
x
x
x
sg
	
	
Hence, 
x

 is primitive recursive.
	b.	 The function Quadrem( )
[
]
x
x
x
=
−
2 is primitive recursive and 
­represents the difference between x and the largest square less than 
or equal to x.
	c.	 Let ρ(x, y) = ((x + y)2 + y)2 + x, ρ1(z) = Quadrem(z), and 
ρ2( )
([
])
z
z
= Quadrem
. These functions are primitive recursive. 
Prove the following:
	 i.	 ρ1 (ρ (x, y)) = x and ρ2 (ρ (x, y)) = y.
	ii.	 ρ is a one–one function from ω2 into ω.
	iii.	 ρ1(0) = ρ2(0) = 0 and
	
ρ
ρ
ρ
ρ
ρ
1
1
2
2
1
1
1
1
1
0
(
)
( )
(
)
( )
(
)
x
x
x
x
x
+
=
+
+
=



+
≠
if
	iv.	 Let ρ2 denote ρ, and, for n ≥ 3, define ρn(x1, …, xn) = ρ(ρn−1 
(x1, …, xn−1), xn). Then each ρn is primitive recursive. Define 
ρ
ρ
ρ
i
n
i
n
x
x
( )
(
( ))
=
−1
1
 for 1 ≤ i ≤ n − 1, and ρ
ρ
n
n x
x
( )
( )
=
2
. Then each 
ρi
n
i
n
,1 ≤≤, is primitive recursive, and ρ ρ
i
n
n
n
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
. 
Hence, ρn is a one–one function of ωn into ω. The ρns and the ρi
ns 
are obtained from ρ, ρ1, and ρ2 by substitution.
	d.	 The recursion rule (V) (page 174) can be limited to the form
	
F x
x
x
n
F x
x
y
G x
x
y F x
n
n
n
n
(
,
,
, )
(
)
(
,
,
,
)
(
,
,
, , (
1
1
1
1
1
1
1
0
0
1
…
=
≥
…
+
=
…
+
+
+
+
1
1
,
,
, ))
…
+
x
y
n



347
Computability
		
[Hint: Given
	
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
(
,
,
, )
(
,
,
)
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
1
1
1
1
1
0
1
…
=
…
…
+
=
…
…
g
n y
, ))
		
define F as above, letting G(x1, …, xn+1, y, z) = h(x1, …, xn, y, z). Then 
f(x1, …, xn, y) = F(x1, …, xn, ɡ(x1, …, xn), y).]
	e.	 Taking x + y, x · y, and [
]
x  as additional initial functions, we can 
limit the recursion rule to the one-parameter form:
	
F x
G x
F x y
H x y F x y
( , )
( )
( ,
)
( , , ( , ))
0
1
=
+
=
		
[Hint: Let n ≥ 2. Given
	
f x
x
g x
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
(
,
,
, )
(
,
,
)
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
1
1
1
1
1
0
1
…
=
…
…
+
=
…
…
n y
, ))
		
let F u y
f
u
u y
n
n
n
( , )
(
( ),
,
( ), )
=
…
ρ
ρ
1
. Define F by a permissible ­recursion. 
(Note that δ
ρ
( ),
,
x x
y
n
−
, and ρi
n are available.) f(x1, …, xn,  y)  = 
F(ρn(x1, …, xn), y).]
	f.	 Taking x + y, x · y, and [
]
x  as additional initial functions, we can 
use h(y, F(x, y)) instead of H(x, y, F(x, y)) in part (e).
		
[Hint: Given
	
F x
G x
F x y
H x y F x y
( , )
( )
( ,
)
( , , ( , ))
0
1
=
+
=
		
let F1(x, y) = ρ(x, F(x, y)). Then x = ρ1(F1(x, y)) and F(x, y) = ρ2(F1(x, y)). 
Define F1(x, y) by a permissible recursion.]
	g.	 Taking x + y, x · y, and [
]
x  as additional initial functions, we can 
limit uses of the recursion rule to the form
	
f x
x
f x y
h y f x y
( , )
( ,
)
( , ( , ))
0
1
=
+
=



348
Introduction to Mathematical Logic
		
Hint: Given
	
F x
G x
F x y
h y F x y
( , )
( )
( ,
)
( , ( , ))
0
1
=
+
=
		
define f as above. Then f(x, y) = f(G(x), y).
	h.	 Taking x
y x y
x
+ ,
,[
]
⋅
 and x y
− as additional initial functions, we 
can limit uses of the recursion rule to those of the form
	
g
g
g
( )
(
)
( , ( ))
0
0
1
=
+
=
y
H y
y
		
[Hint: First note that |
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
 and that [
]
x  is ­definable 
by a suitable recursion. Now, given
	
f x
x
f x y
h y f x y
( , )
( ,
)
( , ( , ))
0
1
=
+
=
		
let g(x) = f(ρ2(x), ρ1(x)). Then
	
g
f
f
g x
f
x
x
x
( )
(
( ),
( ))
( , )
(
)
(
(
),
(
))
(
0
0
0
0 0
0
1
1
1
2
1
2
1
2
=
=
=
+
=
+
+
=
ρ
ρ
ρ
ρ
ρ
+
+
−
+
+
−



+
=
1
1
1
1
1
1
1
0
1
2
1
1
1
)
(
(
)
, (
(
),
(
)
))
(
)
(
h
x
f
x
x
x
ρ
ρ
ρ
ρ
ρ


if
if
x
x
h
x
f
x
x
x
x
+
≠
=
+



+
=
1
0
1
1
0
2
1
1
2
1
1
)
(
)
(
( ), (
( ),
( )))
(
)
(
ρ
ρ
ρ
ρ
ρ
ρ
if
if
+
≠
=
+



+
=
+
≠
=
+
1
0
1
1
0
1
0
2
1
1
1
2
)
(
)
(
( ), ( ))
(
)
(
)
(
ρ
ρ
ρ
ρ
ρ
x
h
x
x
x
x
x
g
if
if
1
1
1
1
1
1
)
(
(
))
(
( ), ( ))
(
(
))
( , ( ))
⋅
+
+
⋅
+
=
sg
sg
ρ
ρ
ρ
x
h
x
x
x
H x
x
g
g
		
Then f(x, y) = ɡ(ρ (y, x)). (Note that sg is obtainable by a recursion of 
the appropriate form and sg( )
x
x
=
−
1 
.)
	i.	 In part (h), H(y, ɡ(y)) can be replaced by H(ɡ(y)).
		
[Hint: Given
	
g
g
g
( )
(
)
( , ( ))
0
0
1
=
+
=
y
H y
y



349
Computability
		
let f(u) = ρ (u, ɡ(u)) and φ(w) = ρ (ρ1(w) + 1, H(ρ1(w), ρ2(w))). Then
	
f
f y
f y
( )
(
)
( ( ))
0
0
1
=
+
= ϕ
		
and ɡ(u) = ρ2(f(u)). (Note that sg(x) is given by a recursion of the 
specified form.)
	j.	 Show that the equations
	
ψ
ψ
ψ
ψ
ψ ψ
( , )
( ,
)
( , )
(
,
)
( ( ,
), )
x
x
y
y
x
y
x y
y
0
1
0
1
1
1
1
1
=
+
+
=
+
+
=
+
		
define a number-theoretic function. In addition, prove:
	
	
I.	 ψ(x, y) > x.
	
	
II.	 ψ(x, y) is monotonic in x, that is, if x < z, then ψ(x, y) < ψ(z, y).
	
	
III.	 ψ(x + 1, y) ≤ ψ(x, y + 1).
	
	
IV.	 ψ(x, y) is monotonic in y, that is, if y < z, then ψ(x, y) < ψ(x, z).
	
	
V.D	Use the recursion theorem to show that ψ is recursive. [Hint: 
Use Exercise 5.21 to show that there is a partial recursive 
function ɡ such that g
g
( , , )
, ( ,
, )
( , )
x
u
x
y
u
y
u
0
1
0
1
1
2
=
+
+
= ϕ
, and 
g(
,
, )
(
( ,
), )
x
y
u
x y
y
u
u
+
+
=
+
1
1
1
2
2
ϕ ϕ
. Then use the recursion the-
orem to find e such that g( , , )
( , )
x y e
x y
e
= ϕ2
. By induction, show 
that ɡ(x, y, e) = ψ(x, y).]
	
	
VI.	 For every primitive recursive function f(x1, …, xn), there is 
some fixed m such that
	
f x
x
x
x
m
n
n
(
,
,
)
(max(
,
,
),
)
1
1
…
<
…
ψ
	
	 for all x1, …, xn. [Hint: Prove this first for the initial functions 
Z N U
x
y x
y
x
i
n
,
,
,
,
,[
]
+
×
 and x
y
−, and then show that it is 
preserved by substitution and the recursion of part (i).] Hence, 
for every primitive recursive function f(x), there is some m 
such that f(x) < ψ(x, m) for all x.
	
	
VII.	 Prove that ψ(x, x) + 1 is recursive but not primitive recursive. 
For other proofs of the existence of recursive functions that 
are not primitive recursive, see Ackermann (1928), Péter (1935, 
1967), and R.M. Robinson (1948).
A set of natural numbers is said to be recursively enumerable (r.e.) if and 
only if it is either empty or the range of a recursive function. If we accept 



350
Introduction to Mathematical Logic
Church’s Thesis, a collection of natural numbers is recursively enumerable 
if and only if it is empty or it is generated by some mechanical process or 
effective procedure.
Proposition 5.21
	
a.	A set B is r.e. if and only if x ∈ B is expressible in the form (∃y)R(x, y), 
where R is recursive. (We even can allow R here to be primitive 
recursive.)
	
b.	B is r.e. if and only if B is either empty or the range of a partial recursive 
function.*
	
c.	B is r.e. if and only if B is the domain of a partial recursive function.
	
d.	B is recursive if and only if B and its complement B are r.e.†
	
e.	The set K = {x|(∃y) T1(x, x, y)} is r.e. but not recursive.
Proof
	
a.	Assume B is r.e. If B is empty, then x ∈ B ⇔ (∃y)(x ≠ x ∧ y ≠ y). If B is non-
empty, then B is the range of a recursive function g. Then x ∈ B ⇔ (∃y)
(ɡ(y) = x). Conversely, assume x ∈ B ⇔ (∃y)R(x, y), where R is recursive. 
If B is empty, then B is r.e. If B is nonempty, then let k be a fixed element 
of B. Define
	
θ( )
(( ) ,( ) )
( )
(( ) ,( ) )
z
k
R z
z
z
R z
z
=
¬



if
if
0
1
0
0
1
	
	 θ is recursive by Proposition 3.19. Clearly, B is the range of θ. (We 
can take R to be primitive recursive, since, if R is recursive, then, by 
Corollary 5.12(a), (∃y)R(x, y) ⇔ (∃y)T1(e, x, y) for some e, and T1(e, x, y) is 
primitive recursive.)
	
b.	Assume B is the range of a partial recursive function ɡ. If B is empty, 
then B is r.e. If B is nonempty, then let k be a fixed element of B. By 
Corollary 5.11, there is a number e such that g(x) = U(μy T1(e, x, y)). Let
	
h z
U z
T e z
z
k
T e z
z
( )
(( ) )
( ,( ) ,( ) )
( ,( ) ,( ) )
=
¬



1
1
0
1
1
0
1
if
if
	
	 By Proposition 3.19, h is primitive recursive. Clearly, B is the range of h. 
Hence, B is r.e.
*	 Since the empty function is partial recursive and has the empty set as its range, the condition 
that B is empty can be omitted.
†	 B
B
=
−
ω
, where ω is the set of natural numbers.



351
Computability
	
c.	Assume B is r.e. If B is empty, then B is the domain of the partial recur-
sive function μy(x + y + 1 = 0). If B is nonempty, then B is the range of a 
recursive function ɡ. Let G be the partial recursive function such that 
G(y) = μx(ɡ(x) = y). Then B is the domain of G. Conversely, assume B is 
the domain of a partial recursive function H. Then there is a number e 
such that H(x) = U(μy T1(e, x, y)). Hence, x ∈ B if and only if (∃y)T1(e, x, y). 
Since T1(e, x, y) is recursive, B is r.e. by part (a).
	
d.	Use part (a) and Proposition 5.17(d). (The intuitive meaning of part (d) is 
the following: if there are mechanical procedures for generating B and 
B, then to determine whether any number n is in B we need only wait 
until n is generated by one of the procedures and then observe which 
procedure produced it.)
	
e.	Use parts (a) and (d) and Corollary 5.13(a).
Remember that the functions ϕ
µ
n x
U
yT n x y
1
1
( )
(
( , , ))
=
 form an enumeration 
of all partial recursive functions of one variable. If we designate the domain 
of ϕn
1 by Wn, then Proposition 5.21(c) tells us that W0, W1, W2, … is an enu-
meration (with repetitions) of all r.e. sets. The number n is called the index of 
the set Wn.
Exercises
5.41	 Prove that a set B is r.e. if and only if it is either empty or the range of a 
primitive recursive function. [Hint: See the proof of Proposition 5.21(b).]
5.42	 a.	 Prove that the inverse image of a r.e. set B under a partial recursive 
function f is r.e. (that is, {x|f(x) ∈ B} is r.e.).
	b.	 Prove that the inverse image of a recursive set under a recursive 
function is recursive.
	c.	 Prove that the image of a r.e. set under a partial recursive function 
is r.e.
	d.	 Using Church’s thesis, give intuitive arguments for the results in 
parts (a)–(c).
	e.	 Show that the image of a recursive set under a recursive function 
need not be recursive.
5.43	 Prove that an infinite set is recursive if and only if it is the range of 
a strictly increasing recursive function. (ɡ is strictly increasing if x < y 
implies ɡ(x) < ɡ(y).)
5.44	 Prove that an infinite set is r.e. if and only if it is the range of a one–one 
recursive function.
5.45	 Prove that every infinite r.e. set contains an infinite recursive subset.
5.46	 Assume that A and B are r.e. sets.
	a.	 Prove that A ∪ B is r.e. [In fact, show that there is a recursive ­function 
ɡ(u, v) such that Wɡ(u,v) = Wu ∪ Wv.]



352
Introduction to Mathematical Logic
	b.	 Prove that A ∩ B is r.e. [In fact, show that there is a recursive ­function 
h(u, v) such that Wh(u, v) = Wu ∩ Wv.]
	c.	 Show that A need not be r.e.
	d.	 Prove that ∪n A
n
W
∈
 is r.e.
5.47	 Show that the assertion
	
	 (∇) A set B is r.e. if and only if B is effectively enumerable (that is, there 
is a mechanical procedure for generating the numbers in B) is equiva-
lent to Church’s thesis.
5.48	 Prove that the set A = {u|Wu = ω} is not r.e.
5.49	 A set B is called creative if and only if B is r.e. and there is a partial recur-
sive function h such that, for any n, if W
B
n ⊆
, then h n
B
Wn
( )∈
−
.
	a.	 Prove that {x|(∃y)T1(x, x, y)} is creative.
	b.	 Show that every creative set is nonrecursive.
5.50D	A set B is called simple if B is r.e., B is infinite, and B contains no infinite 
r.e. set. Clearly, every simple set is nonrecursive. Show that a simple set 
exists.
5.51	 A recursive permutation is a one–one recursive function from ω onto ω. 
Sets A and B are called isomorphic (written A ≃ B) if there is a recursive 
permutation that maps A onto B.
	a.	 Prove that the recursive permutations form a group under the oper-
ation of composition.
	b.	 Prove that ≃ is an equivalence relation.
	c.	 Prove that, if A is recursive (r.e., creative, simple) and A ≃ B, then 
B is recursive (r.e., creative, simple).
	
	 Myhill (1955) proved that any two creative sets are isomorphic. (See 
also Bernays, 1957.)
5.52	 A is many–one reducible to B (written ARmB) if there is a recursive 
function f such that u ∈ A if and only if f(u) ∈ B. (Many–one reduc-
ibility of A to B implies that, if the decision problem for membership 
in B is recursively solvable, so is the decision problem for member-
ship in A.) A and B are called many–one equivalent (written A ≡ mB) 
if ARmB and BRmA. A is one–one reducible to B (written AR1B) if there 
is a one–one recursive function f such that u ∈ A if and only if f(u) ∈ 
B. A and B are called one–one equivalent (written A ≡1 B) if AR1B 
and BR1A.
	a.	 Prove that ≡m and ≡1 are equivalence relations.
	b.	 Prove that, if A is creative, B is r.e., and ARmB, then B is creative. 
[Myhill (1955) showed that, if A is creative and B is r.e., then 
BRmA.]



353
Computability
	c.	
(Myhill, 1955) Prove that, if AR1B then ARmB, and if A ≡ 1B then A ≡ mB. 
However, many–one reducibility does not imply one–one reducibil-
ity, and many–one equivalence does not imply one–one equivalence. 
[Hint: Let A be a simple set, C an infinite recursive subset of A, and 
B = A − C. Then AR1B and BRmA but not-(BR1A).] It can be shown that 
A ≡ 1B if and only if A ≃ B.
5.53	 (Dekker, 1955) A is said to be productive if there is a partial recur-
sive function f such that, if Wn ⊆ A, then f(n) ∈ A − Wn. Prove the 
following.
	a.	 If A is productive, then A is not r.e.; hence, both A and A are infinite.
	b.D	If A is productive, then A has an infinite r.e. subset. Hence, if A is 
productive, A is not simple.
	c.	 If A is r.e., then A is creative if and only if A is productive.
	d.D	There exist 2
0
ℵ productive sets.
5.54	 (Dekker and Myhill, 1960) A is recursively equivalent to B (written A ~ B) 
if there is a one–one partial recursive function that maps A onto B.
	a.	
Prove that ~ is an equivalence relation.
	b.	
A is said to be immune if A is infinite and A has no infinite r.e. 
subset. A is said to be isolated if A is not recursively equivalent 
to a proper subset of A. (The isolated sets may be considered the 
counterparts of the Dedekind-finite sets.) Prove that an infinite set 
is isolated if and only if it is immune.
	c.D	 Prove that there exist 2
0
ℵ immune sets.
	
Recursively enumerable sets play an important role in logic 
because, if we assume Church’s thesis, the set TK of Gödel num-
bers of the theorems of any axiomatizable first-order theory K is 
r.e. (The same holds true of arbitrary formal axiomatic systems.) In 
fact, the relation (see page 200)
	
Pf
is the G del number of a proof in K of a wf with
Godel numbe
K( , ) :
y x
y

r x
	
is recursive if the set of Gödel numbers of the axioms is recursive, 
that is, if there is a decision procedure for axiomhood and Church’s 
thesis holds. Now, x ∈ TK if and only if (∃y)PfK(y, x) and, therefore, 
TK is r.e. Thus, if we accept Church’s thesis, K is decidable if and 
only if the r.e. set TK is recursive. It was shown in Corollary 3.46 
that every consistent extension K of the theory RR is recursively 
undecidable, that is, TK is not recursive.



354
Introduction to Mathematical Logic
	Much more general results along these lines can be proved (see 
Smullyan, 1961; Feferman, 1957; Putnam, 1957; Ehrenfeucht and 
Feferman, 1960; and Myhill, 1955). For example, if K is a first-order 
theory with equality in the language LA of arithmetic: (1) if every 
recursive set is expressible in K, then K is essentially recursively 
undecidable, that is, for every consistent extension K′ of K, TK′ is 
not recursive (see Exercise 5.58); (2) if every recursive function is 
representable in K and K satisfies conditions 4 and 5 on page 210, 
then the set TK is creative. For further study of r.e. sets, see Post 
(1944) and Rogers (1967); for the relationship between logic and 
recursion theory, see Yasuhara (1971) and Monk (1976, part III).
Exercises
5.55	 Let K be a first-order theory with equality in the language LA of arith-
metic. A number-theoretic relation B(x1, …, xn) is said to be weakly 
expressible in K if there is a wf B(x1, …, xn) of K such that, for any natural 
numbers k1, …, kn, B(k1, …, kn) if and only if ⊢K
n
k
k
B (
,
,
)
1 …
.
	a.	 Show that, if K is consistent, then every relation expressible in K is 
weakly expressible in K.
	b.	 Prove that, if every recursive relation is expressible in K and K is 
ω-consistent, every r.e. set is weakly expressible in K. (Recall that, when 
we refer here to a r.e. set B, we mean the corresponding relation “x ∈ B.”)
	c.	 If K has a recursive vocabulary and a recursive axiom set, prove 
that any set that is weakly expressible in K is r.e.
	d.	 If formal number theory S is ω-consistent, prove that a set B is r.e. if 
and only if B is weakly expressible in S.
5.56	 a.	 (Craig, 1953) Let K be a first-order theory such that the set TK of 
Gödel numbers of theorems of K is r.e. Show that, if K has a recur-
sive vocabulary, K is recursively axiomatizable.
	
b.	 For any wf B of formal number theory S, let B  # represent its translation 
into axiomatic set theory NBG (see page 276). Prove that the set of wfs 
B such that ⊢NBG B  # is a (proper) recursively axiomatizable extension 
of S. (However, no “natural” set of axioms for this theory is known.)
5.57	 Given a set A of natural numbers, let u ∈ A* if and only if u is a Gödel 
number of a wf B(x1) and the Gödel number of B ( )
u . is in A. Prove that, 
if A is recursive, then A* is recursive.
5.58	 Let K be a consistent theory in the language LA of arithmetic.
	a.	 Prove that (
)
TK * is not weakly expressible in K.
	b.	 If every recursive set is weakly expressible in K, show that K is 
recursively undecidable.
	c.	 If every recursive set is expressible in K, prove that K is essentially 
recursively undecidable.



355
Computability
5.5  Other Notions of Computability
Computability has been treated here in terms of Turing machines because 
Turing’s definition is probably the one that makes clearest the equivalence 
between the precise mathematical concept and the intuitive notion.* We 
already have encountered other equivalent notions: standard Turing com-
putability and partial recursiveness. One of the strongest arguments for the 
rightness of Turing’s definition is that all of the many definitions that have 
been proposed have turned out to be equivalent. We shall present several of 
these other definitions.
5.5.1  Herbrand–Gödel Computability
The idea of defining computable functions in terms of fairly simple systems 
of equations was proposed by Herbrand, given a more precise form by Gödel 
(1934), and developed in detail by Kleene (1936a). The exposition given here 
is a version of the presentation in Kleene (1952, Chapter XI.)
First let us define the terms.
	
1.	All variables are terms.
	
2.	0 is a term.
	
3.	If t is a term, then (t)′ is a term.
	
4.	If t1, …, tn are terms and fj
n is a function letter, then f
t
t
j
n
n
( ,
,
)
1 …
 is a term.
For every natural number n, we define the corresponding numeral n as 
­follows: (1) 0 is 0 and (2) n +1 is ( )
n ′. Thus, every numeral is a term.
An equation is a formula r = s where r and s are terms. A system E of equa-
tions is a finite sequence r1 = s1, r2 = s2, …, rk = sk of equations such that rk is 
of the form f
t
t
j
n
n
( ,
,
)
1 …
. The function letter fj
n is called the principal letter of 
the system E. Those function letters (if any) that appear only on the right-
hand side of equations of E are called the initial letters of E; any function 
letter other than the principal letter that appears on the left-hand side of 
some equations and also on the right-hand side of some equations is called 
an auxiliary letter of E.
We have two rules of inference:
R1: An equation e2 is a consequence of an equation e1 by R1 if and only 
if e2 arises from e1 by substituting any numeral n for all occurrences of a 
variable.
*	 For further justification of this equivalence, see Turing (1936–1937), Kleene (1952, pp. 317–323, 
376–381), Mendelson (1990), Dershowitz and Gurevich (2008), and the papers in the collection 
Olszewski (2006). The work of Dershowitz and Gurevich, based on a finer analysis of the 
notion of computation, provides much stronger support for Church’s Thesis.



356
Introduction to Mathematical Logic
R2: An equation e is a consequence by R2 of equations f
n
n
p
h
m
m
(
,
,
)
1 …
=  
and r = s if and only if e arises from r = s by replacing one occurrence of 
f
n
n
h
m
m
(
,
,
)
1 …
 in s by p, and r = s contains no variables.
A proof of an equation e from a set B of equations is a sequence e0, …, en of 
equations such that en is e and, if 0 ≤ i ≤ n, then: (1) ei is an equation of B, or 
(2) ei is a consequence by R1 of a preceding equation ej(j < i), or (3) ei is a con-
sequence by R2 of two preceding equations ej and em(j < i, m < i). We use the 
notation B ⊢ e to state that there is a proof from B of e (or, in other words, that 
e is derivable from B).
Example
Let E be the system
	
f
x
x
f
x x
f
x
f
x
1
1
1
1
1
2
1
2
1
3
2
1
1
1
2
(
)
(
)
(
,
)
( ,
,
(
))
’
=
=
The principal letter of E is f1
2, f1
1 is an auxiliary letter, and f1
3 f is an initial 
­letter. The sequence of equations
	
f
x x
f
x
f
x
f
x
f
x
f
f
1
2
1
2
1
3
2
1
1
1
1
2
2
1
3
2
1
1
1
2
2
2
2
2
(
,
)
( ,
,
(
))
( ,
)
( ,
,
( ))
(
=
=
2 1
2 1
2
2
2
2
1
3
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
, )
( , ,
( ))
(
)
(
)
( )
( ) ( . .,
( )
’
’
=
=
=
=
f
f
f
x
x
f
f
i e
3
2 1
2 1 3
1
2
1
3
)
( , )
( , , )
f
f
=
is a proof of f
f
1
2
1
3
2 1
2 1 3
( , )
( , , )
=
 from E.
A number-theoretic partial function φ(x1, …, xn) is said to be computed by a 
system E of equations if and only if the principal letter of E is a letter fj
n and, 
for any natural numbers k1, …, kn, p,
	E
if and only if
isdefined and
⊢f
k
k
p
k
k
k
k
j
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
1
1
1
…
=
…
…
ϕ
ϕ
)=


p
The function φ is called Herbrand–Gödel-computable (for short, HG-computable) 
if and only if there is a system E of equations by which φ is computed.
Examples
	
1.	Let E be the system f
x
1
1
1
0
(
) = . Then E computes the zero function Z. 
Hence, Z is HG-computable.



357
Computability
	
2.	Let E be the system f
x
x
1
1
1
1
(
)
(
)
=
′. Then E computes the successor func-
tion N. Hence, N is HG-computable.
	
3.	Let E be the system f
x
x
x
i
n
n
i
(
,
,
)
1 …
=
. Then E computes the projection 
function Ui
n. Hence, Ui
n is HG-computable.
	
4.	Let E be the system
	
f
x
x
f
x
x
f
x x
1
2
1
1
1
2
1
2
1
2
1
2
0
(
, )
(
,(
))
(
(
,
))
=
′ =
′
	
	 Then E computes the addition function.
	
5.	Let E be the system
	
f
x
f
x
x
1
1
1
1
1
1
1
0
(
)
(
)
=
=
The function φ(x1) computed by E is the partial function with domain {0} 
such that φ(0) = 0. For every k
f
k
≠
=
0
0
1
1
,
( )
E ⊢
 and E ⊢f
k
k
1
1( ) = . Hence, φ(x1) 
is not defined for x1 ≠ 0.
Exercises
5.59	 a.	 What functions are HG-computable by the following systems of 
equations ?
	i.	
f
f
x
x
1
1
1
1
1
1
0
0
( )
,
((
) )
=
′ =
	ii.	
f
x
x
f
x
f
x
x
f
x x
1
2
1
1
1
2
2
1
2
1
2
1
2
1
2
0
0
0
(
, )
,
( ,
)
,
((
) , (
) )
(
,
)
=
=
′
′ =
	iii.	
f
x
f
x
1
1
1
1
1
1
0
0
(
)
,
(
)
=
= ′
	iv.	
f
x
x
f
x
x
f
x x
f
x
f
x x
1
2
1
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
1
1
1
2
1
1
0
(
, )
,
(
,(
))
(
(
,
)),
(
)
(
,
=
′ =
′
=
)
	b.	 Show that the following functions are HG-computable.
	i.	
|x1 − x2 |
	ii.	
x1 · x2
	iii.	 ϕ( )
x
x
x
= 


0
1
if
is even
if
is odd
5.60	 a.	 Find a system E of equations that computes the n-place function that 
is nowhere defined.
	b.	 Let f be an n-place function defined on a finite domain. Find a sys-
tem of equations that computes f.
	c.	 If f(x) is an HG-computable total function and ɡ(x) is a partial func-
tion that coincides with f(x) except on a finite set A, where ɡ is unde-
fined, find a system of equations that computes ɡ.



358
Introduction to Mathematical Logic
Proposition 5.22
Every partial recursive function is HG-computable.
Proof
	
a.	Examples 1–3 above show that the initial functions Z, N, and Ui
n are 
HG-computable.
	
b.	(Substitution rule (IV).) Let φ(x1, …, xn) = η(ψ1(x1, …, xn), …, 
ψm(x1,  …,  xn))  where η, ψ1, …, ψm have been shown to be 
HG-computable. Let Ei be a system of equations computing ψi, with 
principal letter fi
n, and let Em+1 be a system of equations computing 
η, with principal letter fm
n
+1. By changing indices we may  assume 
that no two of E1, …, Em+1 have any function letters in common. 
Construct a system E for φ by listing E1, …, Em+1 and then adding 
the equation 
f
x
x
f
f
x
x
f
x
x
m
n
n
m
m
n
n
m
n
n
+
+
…
=
…
…
…
2
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
(
,
,
),
,
(
,
,
)).
(We may assume that fm
n
+2 does not occur in E1, …, Em+1.) It is clear 
that, if φ(k1, …, kn) = p, then E
f
k
k
p
m
m
n
⊢
+
…
=
2
1
(
,
,
)
. Conversely, 
if 
E
f
k
k
p
m
n
n
⊢
+
…
=
2
1
(
,
,
)
, 
then 
E
f
k
k
p
E
f
n
n
m
n
⊢
⊢
1
1
1
(
,
,
)
,
,
…
=
…
 
(
,
,
)
k
k
p
n
m
1 …
=
 
and 
E
f
p
p
p
m
m
m
⊢
+
…
=
1
1
(
,
,
)
. 
Hence, 
it 
­readily 
­follows that E
f
k
k
p
E
f
k
k
p
n
n
m
m
n
n
m
1
1
1
1
1
⊢
⊢
(
,
,
)
,
,
(
,
,
)
…
=
…
…
=
  and 
E
f
p
p
p
m
m
m
m
+
+
…
=
1
1
1
⊢
(
,
,
)
. Consequently, ψ
ψ
1
1
1
1
( ,
,
)
,
,
( ,
,
)
k
k
p
k
k
p
n
m
n
m
…
=
…
…
=
 
and η(p1, …, pm) = p. So, φ(k1, …, kn) = p. [Hints as to the details of 
the proof may be found in Kleene (1952, Chapter XI, especially, pp. 
262–270).] Hence, φ is HG-computable.
	
c.	(Recursion rule (V).) Let
	
ϕ
ψ
ϕ
ϑ
ϕ
(
,
,
, )
(
,
,
)
(
,
,
,
)
(
,
,
, (
,
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
1
0
1
…
=
…
…
+
=
…
+
+
…
+
,
))
xn 1
	
	 where ψ and ϑ are HG-computable. Assume that E1 is a system of equa-
tions computing ψ with principal letter f n
1  and that E2 is a system of 
equations computing ϑ with principal letter f n
1
2
+ . Then form a system 
for computing φ by adding to E1 and E2
	
f
x
x
f
x
x
f
x
x
x
f
n
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
1
1
1
1
1
1
2
0
+
+
+
+
…
=
…
…
=
(
,
,
, )
(
,
,
)
(
,
,
,(
) )
(
′
x
x
f
x
x
n
n
n
1
1
1
1
1
1
,
,
,
(
,
,
))
…
…
+
+
+
	
	 (We assume that E1 and E2 have no function letters in common.) Clearly, 
if φ(k1, …, kn, k) = p, then E ⊢f
k
k
k
p
n
n
1
1
1
+
…
=
(
,
,
, )
. Conversely, one can 
prove easily by induction on k that, if E ⊢f
k
k
k
p
n
n
1
1
1
+
…
=
(
,
,
, )
, then 
φ(k1, …, kn, k) = p. Therefore, φ is HG-computable. (The case when the 
recursion has no parameters is even easier to handle.)



359
Computability
	
d.	(μ-operator rule (VI).) Let φ(x1, …, xn) = μy(ψ(x1, …, xn, y) = 0) and assume 
that ψ is HG-computable by a system E1 of equations with principal 
­letter f n
1
1
+ . By parts (a)–(c), we know that every primitive recursive func-
tion is HG-computable. In particular, multiplication is HG-computable; 
hence, there is a system E2 of equations having no function letters in 
common with E1 and with principal letter f2
2 such that E2
2
2
1
2
⊢f
k k
p
(
,
) =
 
if and only if k1 · k2 = p. We form a system E3 by adding to E1 and E2 the 
equations
	
f
x
x
f
x
x
x
f
f
x
x
n
n
n
n
n
n
n
3
1
1
3
1
1
1
2
2
3
1
1
0
1
+
+
+
′
+
…
=
…
=
…
(
,
,
, )
(
,
,
, (
) )
(
(
,
,
,
),
(
,
,
))
x
f
x
x x
n
n
n
n
+
+
+
…
1
1
1
1
1
One can prove by induction that E3 computes the function ∏
…
<
y z
n
x
x
y
ψ(
,
,
, );
1
that is, E3
3
1
1
⊢f
k
k
k
p
n
n
+
…
=
(
,
,
,
)
 if and only if ∏
…
=
<
y z
n
k
k
y
p
ψ(
,
,
, )
1
. Now 
construct the system E by adding to E3 the equations
	
f
x
x
x
f
x
x
f
f
x
x
x
f
n
n
n
n
n
n
4
3
1
3
3
3
1
4
3
3
1
1
1
3
0
((
) , ,
)
(
,
,
)
(
(
,
,
,
),
′
=
…
=
…
+
+
+
+
+
…
1
1
1
1
(
,
,
,(
) ),
)
x
x
x
x
n
n
n
′
Then E computes the function φ(x1, …, xn) = μy(ψ(x1, …, xn, y) = 0). If μy(ψ (k1, …, 
kn, y) = 0) = q, then E3
3
1
1
⊢f
k
k
q
p
n
n
+
…
= ′
(
,
,
,
)
, where p
k
k
y
y q
n
+
= ∏
…
<
1
1
ψ(
,
,
, ), 
and E3
3
1
1
0
⊢f
k
k
q
n
n
+
…
′ =
(
,
,
,
)
. Hence, E
f
k
k
f
p
q
n
n
⊢
3
1
4
3
0
(
,
,
)
( , , ).
…
=
′
  But, 
E⊢f
p
q
q
4
3
0
( , , )
′
= , and so, E⊢f
k
k
q
n
n
3
1
(
,
,
)
…
= . Conversely, if E ⊢f
k
k
q
n
n
3
1
(
,
,
)
,
…
=
 
then 
E⊢f
m
q
q
4
3
0
(
, ,
)
′
= , 
where 
E3
3
1
1
⊢f
k
k
q
m
n
n
+
…
=
′
(
,
,
,
) (
) 
and 
E3
3
1
1
0
⊢f
k
k
q
n
n
+
…
′ =
(
,
,
,
)
. 
Hence, 
∏
…
=
+
≠
<
y q
n
k
k
y
m
ψ(
,
,
,
)
1
1
0 
and 
∏
…
=
< +
y q
n
k
k
y
1
1
0
ψ(
,
,
,
)
. So, ψ(k1, …, kn, y) ≠ 0 for y < q, and ψ(k1, …, kn, q) = 0. 
Thus, μy(ψ(k1, …, kn, y) = 0) = q. Therefore, φ is HG-computable.
We now shall proceed to show that every HG-computable function is par-
tial recursive by means of an arithmetization of the apparatus of Herbrand–
Gödel computability. We shall employ the arithmetization used for first-order 
theories in Section 3.4, except for the following changes. The Gödel number 
ɡ(′) is taken to be 17. The only individual constant 0 is assigned the Gödel 
number 19, that is, g(0) = 19. The only predicate letter “=” is identified with 
“A1
2” and is assigned the Gödel number 99 (as in Section 3.4). Thus, an equa-
tion “r = s” is an abbreviation for “A1
2(r, s)”. The following relations and func-
tions are primitive recursive (compare Propositions 3.26–3.27).
FL(x): x is the Gödel number of the function letter
	
(
)
(
)
(
(
)
)
∃
∃
=
+
∧
>
∧
>
<
<
y
z
x
y
z
y x
z x
y
z
1
8 2
3
0
0
⋅
EVbl(x): x is the Gödel number of an expression consisting of a variable
EFL(x): x is the Gödel number of an expression consisting of a function letter



360
Introduction to Mathematical Logic
Num(x): the Gödel number of the numeral x
	
Num(0) = 19
	
Num(y + 1) = 23 * Num(y) * 25 * 217
Trm(x): x is the Gödel number of a term
Nu(x): x is the Gödel number of a numeral
	
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
ArgT(x) = number of arguments of a function letter, f, if x is the Gödel number 
of f
x * y = the Gödel number of an expression AB if x is the Gödel number of the 
expression A and y is the Gödel number of B
Subst(x, y, u, v): v is the Gödel number of a variable xi, u is the Gödel number 
of a term t, y is the Gödel number of an expression B, and x is 
the Gödel number of the result of substituting t for all occur-
rences of xi in B
The following are also primitive recursive:
Eqt(x): x is the Gödel number of an equation:
	
(
)
(
)
(
( )
( )
)
∃
∃
∧
∧
=
<
<
u
w
u
w
x
u x
w x
u
w
Trm
Trm
2
2
2
2
2
2
99
3
7
5
*
*
*
*
*
(Remember that = is A1
2, whose Gödel number is 99.)
Syst(x): x is the Gödel number of a system of equations:
	
(
)
(( ) )
(
)
(
)
[
( )
( )
( )
( )
∀
∧∃
∃
∧
∧
<
<
<
−
y
x
u
w
w
w
x
y
x
y
u x
w x
x
lh
lh
Eqt
EFL
Trm
1
99
3
7
5
2
2
2
2
=
*
*
*
*
*
w
u
]
Occ(u, v): u is the Gödel number of a term t or equation B and v is the Gödel 
number of a term that occurs in t or B:
	
(
( )
( ))
( )
(
)
(
)
(
Trm
Eqt
Trm
u
u
v
x
y
u
x v y
u
x v
u
v y
x u
y u
∨
∧
∧∃
∃
=
∨
=
∨
=
∨
<
<
*
*
*
*
u
v
= )
Cons1(u, v): u is the Gödel number of an equation e1, v is the Gödel number of 
an equation e2, and e2 is a consequence of e1 by rule R1:
	
Eqt
Eqt
Nu
Subst
Occ
( )
( )
(
)
(
)
(
( )
( , , , )
( , )
u
v
x
y
y
v u y x
u x
x u
y v
∧
∧∃
∃
∧
∧
<
<
)



361
Computability
Cons2(u, z, v): u, z, v are Gödel numbers of equations e1, e2, e3, respectively, and 
e3 is a consequence of e1 and e2 by rule R2:
	
Eqt
Eqt
Eqt
EVbl
Occ
( )
( ).
( )
(
)
(
( )
( , ))
(
)
(
u
z
v
x
x
z x
x
x z
x u
∧
∧
∧¬ ∃
∧
∧¬ ∃
<
< EVbl
Occ
( )
( , ))
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
[
x
u x
p
t
x
y
q
q
p u
t u
x u
y u
q u
∧
∧∃
∃
∃
∃
∃
=
<
<
<
<
<
21 8 2 3
99
3
7
5
2
2
2
2
+
<
<
∧
=
∧
∃
∃
(
)
( )
(
)
(
)
(
( )
x y
t
u
q
p
z
z
*
*
* *
*
*
Num
Trm
α
β
α
α
β
∧
∧
=
∧
=
∧
=
Trm
Num
( )
{[
( )
]
β
α
β
β
α
z
q
v
p
2
2
2
2
2
2
2
2
99
3
7
5
99
3
7
5
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
∨∃
∃
=
∧
=
∨
=
∧
<
<
(
)
(
)
[(
( )
)
(
γ
δ
β
γ
α
γ
β
δ
γ
δ
z
z
q
v
p
q
*
*
*
*
* *
*
*
2
2
2
2
99
3
7
5
Num
v
p
q
v
p
=
∨
=
∧
=
2
2
2
2
2
2
2
99
3
7
5
99
3
7
*
*
*
*
*
*
* *
*
*
*
* *
α
β
γ
δ
α
γ
q Num
Num
( )
)
(
( )
)]})
*
*
δ 25
Ded(u, z): u is the Gödel number of a system of equations E and z is the Gödel 
number of a proof from E:
	
Syst
Cons
( )
(
)
((
)
( )
( )
(
)
(( )
( )
( )
u
x
w
u
z
y
z
x
z
w
u
w
x
y x
y
∧∀
∃
=
∨∃
<
<
<
lh
lh
1
,( ) )
(
)
(
)
(( ) ,( ) ,( ) ))
z
y
v
z
z
z
x
y x
v x
y
v
x
∨∃
∃
<
< Cons2
Sn(u, x1, …, xn, z): u is the Gödel number of a system of equations E whose 
principal letter is of the form fj
n, and z is the Gödel number of a proof from E 
of an equation of the form f
x
x
p
j
n
n
(
,
,
)
1 …
=
:
	
Ded
*
*
*
( , )
(
)
(
)
[( )
(
( )
(
)
u z
w
y
u
y
w u
y u
u
n w
∧∃
∃
=
∧
∃
<
<
−
+
lh
1
99
3
1 8 2 3
2
2
2
t
t
z
x
t u
z
n w
)
(
( )
(( )
(
)
( )
(
)
<
−
+
∧
=
∗
∗
Nu
*
* Num
*
*
lh
1
99
3
1 8 2 3
3
1
7
2
2
2
2
2
Num
*
*
* Num
*
*
(
)
(
)
)]
x
x
t
n
2
7
5
2
2

Remember that ɡ(() = 3, ɡ()) = 5, and ɡ(,) = 7.
	
U x
y
w
x
w
y
y x
w x
x
( )
(
)
(( )
( )
)
( )
=
∃
=
<
<
−
µ
lh
1
99
3
7
5
2
2
2
2
*
*
*
* Num
*
(The significance of this formula is that, if x is the Gödel number of a proof 
of an equation r
p
= , then U(x) = p.)
Proposition 5.23
(Kleene, 1936a) If φ(x1, …, xn) is HG-computable by a system of equations E 
with Gödel number e, then
	
ϕ
µ
(
,
,
)
(
(
( ,
,
,
, )))
x
x
U
y
e x
x
y
n
n
n
1
1
…
=
…
S



362
Introduction to Mathematical Logic
Hence, every HG-computable function φ is partial recursive, and, if φ is total, 
then φ is recursive.
Proof
φ(k1, …, kn) = p if and only if E ⊢f
k
k
p
j
n
n
(
,
,
)
1 …
= , where fj
n is the principal let-
ter of E. φ(k1, …, kn) is defined if and only if (∃y)Sn(e, k1, …, kn, y). If φ(k1, …, kn) 
is defined, μy(Sn(e, k1, …, kn, y)) is the Gödel number of a proof from E of an 
equation f
k
k
p
j
n
n
(
,
,
)
1 …
=
. Hence, U(μy(Sn(e, k1, …, kn, y))) = p = φ(k1, …, kn). 
Also, since Sn is primitive recursive, μy(Sn(e, x1, …, xn, y)) is partial recursive. 
If φ is total, then (∀x1) … (∀xn)(∃y)Sn(e, x1, …, xn, y); hence, μy(Sn(e, x1, …, xn, y)) 
is recursive, and then, so is U(μy(Sn(e, x1, …, xn, y))).
Thus, the class of HG-computable functions is identical with the class of 
partial recursive functions. This is further evidence for Church’s thesis.
5.5.2  Markov Algorithms
By an algorithm in an alphabet A we mean a computable function 𝔄 whose 
domain is a subset of the set of words of A and the values of which are 
also words in A. If P is a word in A, 𝔄 is said to be applicable to P if P is in 
the domain of 𝔄; if 𝔄 is applicable to P, we denote its value by 𝔄(P). By an 
algorithm over an alphabet A we mean an algorithm 𝔄 in an extension B 
of A.* Of course, the notion of algorithm is as hazy as that of computable 
function.
Most familiar algorithms can be broken down into a few simple steps. 
Starting from this observation and following Markov (1954), we select a par-
ticularly simple operation, substitution of one word for another, as the basic 
unit from which algorithms are to be constructed. To this end, if P and Q are 
words of an alphabet A, then we call the expressions P → Q and P → ·Q pro-
ductions in the alphabet A. We assume that “→” and “·” are not symbols of A. 
Notice that P or Q is permitted to be the empty word. P → Q is called a simple 
production, whereas P → ·Q is a terminal production. Let us use P → (·)Q to 
denote either P → Q or P → ·Q. A finite list of productions in A
	
P
Q
P
Q
P
Q
1
1
2
2
→
→
→
( )
( )
( )
⋅
⋅
⋅

r
r
is called an algorithm schema and determines the following algorithm 𝔄 in A. 
As a preliminary definition, we say that a word T occurs in a word Q if there 
are words U, V (either one possibly the empty word Λ) such that Q = UTV. 
*	 An alphabet B is an extension of A if A ⊆ B.



363
Computability
Now, given a word P in A: (1) We write 𝔄 : P ⊐ if none of the words P1, …, Pr 
occurs in P. (2) Otherwise, if m is the least integer, with 1 ≤ m ≤ r, such that 
Pm occurs in P, and if R is the word that results from replacing the leftmost 
occurrence of Pm in P by Qm, then we write
	
a.
P
R
 :
⊢
if Pm → (·)Qm is simple (and we say that 𝔄 simply transforms P into R);
	
b
P
R
.
:

⊢⋅
if Pm → (·)Qm is terminal (and we say that 𝔄 terminally transforms P into R). 
We then define 𝔄. P ⊧ R to mean that there is a sequence R0, R1, …, Rk such 
that
	
i.	P = R0.
	
ii.	R = Rk.
	 iii.	For 0 ≤ j ≤ k −  2, 𝔄: Rj ⊢ Rj+1.
	 iv.	Either 𝔄: Rk−1 ⊢ Rk or 𝔄: Rk−1 ⊢ · Rk. (In the second case, we write 𝔄: 
P ⊧ · R.)
We set 𝔄(P) = R if and only if either 𝔄: P ⊧ · R, or 𝔄: P ⊧ R and 𝔄: R ⊐. The 
algorithm thus defined is called a normal algorithm (or a Markov algorithm) 
in the alphabet A.
The action of 𝔄 can be described as follows: given a word P, we find the 
first production Pm → (·)Qm in the schema such that Pm occurs in P. We then 
substitute Qm for the leftmost occurrence of Pm in P. Let R1 be the new word 
obtained in this way. If Pm → (·)Qm was a terminal production, the process 
stops and the value of the algorithm is R1. If Pm → (·)Qm was simple, then we 
apply the same process to R1 as was just applied to P, and so on. If we ever 
obtain a word Ri such that 𝔄: Ri ⊐, then the process stops and the value 𝔄(P) 
is Ri. It is possible that the process just described never stops. In that case, 
𝔄 is not applicable to the given word P.
Our exposition of the theory of normal algorithms will be based on Markov 
(1954).
Examples
	
1.	Let A be the alphabet {b, c}. Consider the schema
	
b
c
c
→
→
·Λ



364
Introduction to Mathematical Logic
	
	 The normal algorithm 𝔄 defined by this schema transforms any word 
that contains at least one occurrence of b into the word obtained by 
erasing the leftmost occurrence of b. 𝔄 transforms the empty word Λ 
into itself. 𝔄 is not applicable to any nonempty word that does not con-
tain b.
	
2.	Let A be the alphabet {a0, a1, …, an}. Consider the schema
	
a
a
a
0
1
→
→
→
Λ
Λ
Λ

n
	
	 We can abbreviate this schema as follows:
	
ξ
ξ
→Λ
(
)
in A
	
	 (Whenever we use such abbreviations, the productions intended may 
be listed in any order.) The corresponding normal algorithm trans-
forms every word into the empty word. For example,
	



:
:
.
,
(
a a a a a
a a a a
a a a
a a
a
and
Hence
a a
1
2
1
3
0
1
2
1
3
2
1
3
1
2
⊢
⊢
⊢
⊢
⊢
2
3
3
Λ
Λ ⊐
a a a
1
3
0)
.
= Λ
	
3.	Let A be an alphabet containing the symbol a1, which we shall abbre-
viate |. For natural numbers n, we define n inductively as follows: 
0 =| and n
n
+
=
1
|. Thus, 1
2
=
=
||,
|||, and so on. The words n will be 
called numerals. Now consider the schema Λ → ·|, defining a normal 
algorithm 𝔄. For any word P in A, 𝔄(P) = | P.* In particular, for every 
natural number n, ( )
.
n
n
=
+1
	
4.	Let A be an arbitrary alphabet {a0, a1, …, an}. Given a word P
a a
a
=
j
j
jk
0
1 
, 
let 
⌣

P
a
a a
=
j
j
j
k
1
0 be the inverse of P. We seek a normal algorithm 𝔄 such 
that ( )
P
P
=
⌣
. Consider the following (abbreviated) algorithm schema 
in the alphabet B = 𝔄 ∪ {α, β}.
	a.	
αα → β
	b.	 βξ → ξβ (ξ in A)
	c.	
βα → β
	d.	 β → · Λ
*	 To see this, observe that Λ occurs at the beginning of any word P, since P = ΛP.



365
Computability
	e.	
αηξ → ξαη (ξ, η in A)
	f.	
Λ → α
	
	 This determines a normal algorithm 𝔄 in B. Let P
a a
a
=
j
j
jk
0
1 
 
be any word in A. Then 𝔄: P ⊢ αP by production (f). Then, 
α
α
α
α
P
a
a a
a
a a
a a
a
a a
a
a
⊢
⊢
⊢
j
j
j
j
j
j
j
j
j
j
j
j
j
k
k
k
1
0
2
1
2
0
3
1
2
0
…
…
…
…
, all by pro-
duction (e). Thus, 𝔄: P ⊧ aj1 aj2 … ajk αaj0. Then, by production (f), 𝔄: P ⊧ aj2 
aj3 … ajk αaj1 αaj0 Iterating this process, we obtain 𝔄: P ⊧ αajk αajk−1 α … αaj1 
αaj0. Then, by production (f), 𝔄: P ⊧ ααajk αajk−1 α … αaj1 αaj0, and, by pro-
duction (a), 𝔄: P ⊧ βajk αajk−1 α … αaj1 αaj0. Applying productions (b) and (c) 
and finally (d), we arrive at  : P
P
 ⋅
⌣
. Thus, 𝔄 is a normal algorithm over 
A that inverts every word of A.*
Exercises
5.61	 Let A be an alphabet. Describe the action of the normal algorithms 
given by the following schemas.
	a.	 Let Q be a fixed word in A and let the algorithm schema be: Λ → · Q.
	b.	 Let Q be a fixed word in A and let α be a symbol not in A. Let B = 
A ∪ {α}. Consider the schema
	
αξ
ξα
ξ
α
α
→
→
→
(
)
in A
Q
⋅
Λ
	c.	 Let Q be a fixed word in A. Take the schema
	
ξ
ξ
→
→
Λ
Λ
(
)
in A
Q
⋅
	d.	 Let B = A ∪ {|}. Consider the schema
	
ξ
ξ
→
−
→
| (
{|})
|
in A
Λ
⋅
*	 The distinction between a normal algorithm in A and a normal algorithm over A is impor-
tant. A normal algorithm in A uses only symbols of A, whereas a normal algorithm over A 
may use additional symbols not in A. Every normal algorithm in A is a normal algorithm 
over A, but there are algorithms in A that are determined by normal algorithms over A but 
that are not normal algorithms in A (for example, the algorithm of Exercise 5.62(d)).



366
Introduction to Mathematical Logic
5.62	 Let A be an alphabet not containing the symbols α, β, γ. Let B = A ∪ {α} 
and C = A ∪ {α, β, γ}.
	a.	 Construct a normal algorithm 𝔄 in B such that 𝔄(Λ) = Λ and 
𝔄(ξP) = P for any symbol ξ in A and any word P in A. Thus, 𝔄 erases 
the first letter of any nonempty word in A.
	b.	 Construct a normal algorithm 𝔇 in B such that 𝔇(Λ) = Λ and 
𝔇(Pξ) = P for any symbol ξ in A and any word P in A. Thus, 𝔇 
erases the last letter of any nonempty word in A.
	c.	 Construct a normal algorithm ℭ in B such that ℭ(P) equals Λ if P 
contains exactly two occurrences of α and ℭ(P) is defined and is not 
equal to Λ in all other cases.
	d.	 Construct a normal algorithm B  in C such that, for any word P of 
A, 𝔅(P) = PP.
5.63	 Let A and B be alphabets and let α be a symbol in neither A nor B. For 
certain symbols a1, …, ak in A, let Q1, …, Qk be corresponding words 
in B. Consider the algorithm that associates with each word P of A 
the word Sub
P
Q
Q
a
a
1
1
…
k
k

( ) obtained by simultaneous substitution of each 
Qi for ai(i = 1, …, k). Show that this is given by a normal algorithm in 
A ∪ B ∪ {α}.
5.64	 Let H = {|} and M = {|, B}. Every natural number n is represented by its 
numeral n, which is a word in H. We represent every k-tuple (n1, n2, …, nk) 
of natural numbers by the word n
n
nk
1
2
B
B
B
…
 in M. We shall denote 
this word by (
,
,
,
)
n n
nk
1
2 …
. For example, ( , , )
3 1 2  is ||||B||B|||.
	a.	 Show that the schema
	
B
B
→
→
→
→
α
α
α
α

|
|
|
⋅
Λ
	
	
defines a normal algorithm 𝔄Z over M such that  Z n
( ) = 0 for 
any n, and 𝔄Z is applicable only to numerals in M.
	b.	 Show that the schema
	
B
B
→
→
→
α
α
|
⋅
Λ
	
	
defines a normal algorithm 𝔄N over M such that  N n
n
( ) =
+1 for 
all n, and 𝔄N is applicable only to numerals in M.



367
Computability
	c.	 Let α1, …, α2k be symbols not in M. Let 1 ≤ j ≤ k. Let Si be the list
	
α
α
α
α
α
α
α
α
2
1
2
1
2
1
2
2
2
2
2
1
i
i
i
i
i
i
i
i
−
−
−
+
→
→
→
→
B
B
B
|
|
|
	
If
consider
If
consider
If
consider
the algorithm sch
1
1
<
<
=
=
j
k
j
j
k
,
,
ema
the schema
the schema
B
B
S
S
S
S
1
1
1
1
1
2
1
2
2
1
α
α
α
α
α
α
α
→
→
→
−
−


|
|
| |
j
k
2
1
2
1
2
3
2
1
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
j
j
k
k
j
j
k
k
−
−
−
−
−
−
→
→
→
→
→
B
B
B
B
B
α
α
α
α
α
α
α
α
α
α
|
|
|
|
S
j
j
k
k
j
j
k
k
k
j
k
k
| |
| |
→
→
→
→
→
+
−
+
−
−
α
α
α
α
α
α
α
α
α
2
2
2
2
2
1
1
2
2
1
2
1
2
1

B
B
B
B
B
S
S
α
α
α
α
α
α
α
α
α
α
2
2
1
2
1
1
2
2
2
1
2
1
2
2
k
k
k
k
k
k
k
k
k
k
→
→
→
→
→
→
−
−
−
−
·
|
|
|
Λ
Λ

S
B
B
B
B
B
α
α
α
α
α
α
α
α
α
α
2
1
2
2
2
2
1
2
2
2
1
k
k
k
k
k
k
k
k
−→
→
→
→
→
→
→
|
·
|
·
Λ
Λ
Λ
Λ
B
B
	
	
Show that the corresponding normal algorithm  j
k is such that 
 j
k
k
j
n
n
n
((
,
,
))
1 …
=
; and  j
k is applicable to only words of the 
form (
,
,
)
n
nk
1 …
.
	d.	 Construct a schema for a normal algorithm in M transforming 
(
,
)
n n
1
2  into |
|
n
n
1
2
−
.
	e.	 Construct a normal algorithm in M for addition.
	f.	 Construct a normal algorithm over M for multiplication.
Given algorithms 𝔄 and B and a word P, we write 𝔄(P) ≈ 𝔅(P) if and only if 
either 𝔄 and B are both applicable to P and 𝔄(P) = 𝔅(P) or neither 𝔄 nor 𝔅 is 
applicable to P. More generally, if C and D are expressions, then C ≈ D is to 
hold if and only if neither C nor D is defined, or both C and D are defined and 



368
Introduction to Mathematical Logic
denote the same object. If 𝔄 and 𝔅 are algorithms over an alphabet A, then we 
say that 𝔄 and 𝔅 are fully equivalent relative to A if and only if 𝔄(P) ≈ 𝔅(P) for 
every word P in A; we say that 𝔄 and 𝔅 are equivalent relative to A if and only if, 
for any word P in A, whenever 𝔄(P) or 𝔅(P) exists and is in A, then 𝔄(P) ≈ 𝔅(P).
Let M be the alphabet {|, B}, as in Exercise 5.64, and let ω be the set of natu-
ral numbers. Given a partial number-theoretic function φ of k arguments, 
that is, a function from a subset of ωk into ω, we denote by 𝔅φ the correspond-
ing function in M; that is, ϕ
ϕ
((
,
,
))
(
,
,
)
n
n
n
n
k
k
1
1
…
=
…
 whenever either of 
the two sides of the equation is defined. 𝔅φ is assumed to be inapplicable 
to words not of the form (
,
,
)
n
nk
1 …
. The function φ is said to be Markov-
computable if and only if there is a normal algorithm 𝔄 over M that has the 
value ϕ(
,
,
)
n
nk
1 …
 when applied to (
,
,
)
n
nk
1 …
.*
A normal algorithm is said to be closed if and only if one of the productions in 
its schema has the form Λ → · Q. Such an algorithm can end only terminally—
that is, by an application of a terminal production. Given an arbitrary normal 
algorithm 𝔄, add on at the end of the schema for 𝔄 the new production Λ → · Λ, 
and denote by 𝔄· the normal algorithm determined by this enlarged schema. 
𝔄 · is closed, and 𝔄 · is fully equivalent to 𝔄 relative to the alphabet of 𝔄.
Let us now show that the composition of two normal algorithms is again 
a normal algorithm. Let 𝔄 and 𝔅 be normal algorithms in an alphabet A. 
For each symbol b in A, form a new symbol b, called the correlate of b. Let A 
be the alphabet consisting of the correlates of the symbols of A. We assume 
that A and A have no symbols in common. Let α and β be two symbols not in 
A
A
∪
. Let 𝔖A be the schema of 𝔄 · except that the terminal dot in terminal 
productions is replaced by α. Let 𝔖𝔅 be the schema of 𝔅 · except that every 
symbol is replaced by its correlate, every terminal dot is replaced by β, pro-
ductions of the form Λ → Q are replaced by α → αQ, and productions Λ → ·Q 
are replaced by α → αβQ. Consider the abbreviated schema
	
a
a
a in A
a
a
a in A
a
b
a, b in A
a
a
a in A
a
a
a in A
a
α
α
α
α
β
β
β
β
→
→
→
→
→
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
b
a
b
ab
a, b in A
B
A
→
→
(
)
αβ
⋅Λ


*	 In this and in all other definitions in this chapter, the existential quantifier “there is” is meant 
in the ordinary “classical” sense. When we assert that there exists an object of a certain kind, 
we do not necessarily imply that any human being has found or ever will find such an object. 
Thus, a function φ may be Markov-computable without our ever knowing it to be so.



369
Computability
This schema determines a normal algorithm 𝔊 over A such that 𝔊(P) ≈ 
𝔅(𝔄(P)) for any word P in A. 𝔊 is called the composition of 𝔄 and 𝔅 and is 
denoted 𝔅 ○ 𝔄.
Let 𝔜 be an algorithm in an alphabet A and let B be an extension of A. If we 
take a schema for 𝔜 and prefix to it the production b → b for each symbol b 
in B − A, then the new schema determines a normal algorithm 𝔜B in B such 
that 𝔜B(P) ≈ 𝔜(P) for every word P in A, and 𝔜B is not applicable to any word 
in B that contains any symbol of
B − A. 𝔜B is fully equivalent to 𝔜 relative to A and is called the propagation 
of 𝔜 onto B.
Assume that 𝔄 is a normal algorithm in an alphabet A1 and 𝔅 is a normal 
algorithm in an alphabet A2. Let A = A1 ∪ A2. Let 𝔄A and 𝔅A be the propaga-
tions of 𝔄 and 𝔅, respectively, onto A. Then the composition 𝔊 of 𝔄A and 𝔅A 
is called the normal composition of 𝔄 and 𝔅 and is denoted by 𝔅 ○ 𝔄. (When 
A1 = A2, the normal composition of 𝔄 and 𝔅 is identical with the composition 
of 𝔄 and 𝔅; hence the notation 𝔅 ○ 𝔄 is unambiguous.) 𝔊 is a normal algo-
rithm over A such that 𝔊(P) ≈ 𝔅(𝔄(P)) for any word P in A1, and 𝔊 is appli-
cable to only those words P of A such that P is a word of A1, 𝔄 is applicable 
to P, and 𝔅 is applicable to 𝔄(P). For a composition of three or more normal 
algorithms, we must use normal compositions, since a composition enlarges 
the alphabet.
Proposition 5.24
Let T   be a Turing machine with alphabet A. Then there is a normal algo-
rithm 𝔄 over A that is fully equivalent to the Turing algorithm AlgT  relative 
to A.
Proof*
Let D
q
q
=
…
k
km
0 ,
,
, where q
q
k
km
0 ,
,
…
 are the internal states of T    and q
q
k0
0
=
.
Write the algorithm schema for 𝔄 as follows: Choose a new symbol α and 
start by taking the productions αai → q0ai for all symbols ai in A, followed by 
the production α → α. Now continue with the algorithm schema in the fol-
lowing manner. First, for all quadruples qjaiakqr of T,  take the production qjai 
→ qrak. Second, for each quadruple qjaiLqr of T,  take the productions anqjai → 
qranai for all symbols an of A; then take the production
qjai → qra0ai. Third, for each quadruple qjaiRqr of T, take the productions 
qjaian → aiqran for all symbols an of A; then take the production qjai → aiqra0. 
Fourth, write the productions qki →·Λ for each internal state qki of T, and 
finally take Λ → α. This schema defines a normal algorithm 𝔄 over A, and it 
is easy to see that, for any word P of A, AlgT (P) ≈ 𝔄(P).
*	 This version of the proof is due to Gordon McLean, Jr.



370
Introduction to Mathematical Logic
Corollary 5.25
Every Turing-computable function is Markov-computable.
Proof
Let f(x1, …, xn) be standard Turing-computable by a Turing machine T    with 
alphabet A ⊇ {|, B}. (Remember that B is a0 and | is a1).) We know that, for 
any natural numbers k1, …, kn, if f(k1, …, kn) is not defined, then AlgT is not 
applicable to (
,
,
)
k
kn
1 …
, whereas, if f(k1, …, kn) is defined, then
	
AlgT ((
,
,
))
(
,
,
)
(
,
,
)
k
k
R k
k B f k
k R
n
n
n
1
1
1
1
2
…
≈
…
…
where R1 and R2 are (possibly empty) sequences of Bs. Let 𝔅 be a normal 
algorithm over A that is fully equivalent to AlgT    relative to A. Let 𝔊 be the 
normal algorithm over {|, B} determined by the schema
	
α
α
α
β
β
β
β
γ
γ
β
γ
γ
γ
β
α
B
B
B
B
B
→
→
→
→
→
→
→
→
→
|
|
| |
|
|
⋅
⋅
Λ
Λ
Λ
If R1 and R2 are possibly empty sequences of Bs, then 𝔊, when applied to 
R
B
R
1
1
1
2
(
,
,
)
(
,
,
)
k
k
f k
k
n
n
…
…
, will erase R1 and R2. Finally, let  n
n
+
+
1
1 be the 
­normal “projection” algorithm defined in Exercise 5.64(c). Then the normal 
composition 


n
n
+
+
°
°
1
1
 is a normal algorithm that computes f.
Let A be any algorithm over an alphabet A
a
a
=
…
{
,
,
}
j
jm
0
. We can associate 
with 𝔄 a partial number-theoretic function ψ𝔄 such that ψ𝔄 (n) = m if and 
only if either n is not the Gödel number* of a word of A and m = 0, or n and 
m are Gödel numbers of words P and Q of A such that 𝔄(P) = Q.
Proposition 5.26
If 𝔄 is a normal algorithm over A
a
a
=
…
{
,
,
}
j
jm
0
, then ψ𝔄 is partial recursive.
*	 Here and below, we use the Gödel numbering of the language of Turing computability given in 
Section 5.3 (page 325). Thus, the Gödel number ɡ(ai) of ai is 7 + 4i. In particular, ɡ(B) = ɡ(a0) = 7 
and ɡ(|) = ɡ(a1) = 11.



371
Computability
Proof
We may assume that the symbols of the alphabet of A are of the form ai. 
Given a simple production P → Q, we call 213g(P)5g(Q) its index; given a termi-
nal production P → ·Q, we let 223g(P)5g(Q) be its index. If P0 → (·)Q0, …, Pr → (·)Qr 
is an algorithm schema, we let its index be 2 3
0
1
k
k
r
kr
… p , where ki is the index 
of Pi → (·)Qi. Let Word(u) be the recursive predicate that holds if and only if u 
is the Gödel number of a finite sequence of symbols of the form ai:
	
u
u
z z
h u
y y
u
u
y
z
≠
∧
=
∨∀
<
⇒∃
<
∧
=
+
0
1
7
4
[
(
)(
( )
(
)(
( )
))]
ℓ
Let SI(u) be the recursive predicate that holds when u is the index of a simple 
production: l h(u) = 3 ∧ (u)0 = 1 ∧ Word((u)1) ∧ Word((u)2). Similarly, TI(u) is the 
recursive predicate that holds when u is the index of a terminal production: 
l h(u) = 3 ∧ (u)0 = 2 ∧ Word((u)1) ∧ Word((u)2). Let Ind(u) be the recursive predi-
cate that holds when u is the index of an algorithm schema: u>1 ∧ (∀ z)(z < 
l h(u)⇒SI((u)z) ∨ TI((u)z)). Let Lsub(x, y, e) be the recursive predicate that holds 
if and only if e is the index of a production P→(·)Q and x and y are Gödel 
numbers of words U and V such that P occurs in U, and V is the result of 
substituting Q for the leftmost occurrence of P in U:
	
Word
Word
SI
TI
( )
( )
(
( )
( ))
(
)
(
)
(
( )
x
y
e
e
u
v
x
u
e
v
y
u x
v x
∧
∧
∨
∧∃
∃
=
∧
=
≤
≤
*
*
1
u
e
v
w
z
x
w
e
z
w
u
w x
z x
*
*
*
*
( )
(
)
(
)
(
( )
))
2
1
∧¬ ∃
∃
=
∧
<
≤
≤
Let Occ(x, y) be the recursive predicate that holds when x and y are Gödel 
numbers of words U and V such that V occurs in U: Word(x) ∧ Word(y) ∧ 
(∃v)v≤x(∃z)z≤x (x = v * y * z). Let End(e, z) be the recursive predicate that holds 
when and only when z is the Gödel number of a word P, and e is the index 
of an algorithm schema defining an algorithm 𝔄 that cannot be applied to 
P (i.e., 𝔄: P ⊐): Ind(e) ∧ Word(z) ∧ (∀w)wht (e) ¬Occ(z,( (e)w)1). Let SCons(e, y, x) be 
the recursive predicate that holds if and only if e is the index of an algorithm 
schema and y and x are Gödel numbers of words V and U such that V arises 
from U by a simple production of the schema:
	
Ind
Word
Word
SI
Lsub
( )
( )
( )
(
)
[
(( ) )
( , ,( ) )
( )
e
x
y
v
e
x y e
v lh e
v
v
∧
∧
∧∃
∧
<
∧∀
¬
<
(
)
( ,(( ) ) )]
z
x
e
z v
z
Occ
1
Similarly, one defines the recursive predicate TCons(e, y, x), which differs 
from SCons(e, y, x) only in that the production in question is terminal. Let 
Der(e, x, y) be the recursive predicate that is true when and only when e 
is the index of an algorithm schema that determines an algorithm 𝔄, x is 
the Gödel number of a word U0, y is the Gödel number of a sequence of 
words U0, …, Uk(k ≥ 0) such that, for 0
1
1
≤<
−
+
i
k
i
 ,U
 arises from Ui by a 



372
Introduction to Mathematical Logic
production of the schema, and either  :U
U
k
k
−1 ⊢⋅
 or  :U
U
k
k
−1 ⊢
 and 𝔄: 
Uk ⊐ (or, if k = 0, just 𝔄: Uk ⊐):
	
Ind
Word
Word
( )
( )
(
)
(( ) )
( )
(
)
( )
( )
e
x
z
y
y
x
z
z
y
z
z
y
∧
∧∀
∧
=
∧∀
<
<
−
lh
lh
0
2
 SCons
End
TCo
( ,( )
,( ) )
[( ( )
( ,( ) ))
( ( )
{
e y
y
y
e y
y
z
z
+
∧
=
∧
∨
>
∧
1
0
1
1
lh
lh
ns
SCons
( ,( )
,( )
)
(
( ,( )
,
( )
( )
( )
( )
(
e y
y
e y
y
y
y
y
lh
lh
lh
lh



−
−
−
∨
1
2
1
y
y
e y
)
( )
)
( ,( )
))})]


−
−
∧
2
1
End
lh
Let WA(u) be the recursive predicate that holds if and only if u is the Gödel 
number of a word of A:
	
u
u
z
u
u
z
u
z
j
z
jm
≠
∧
=
∨∀
=
+
∨…∨
=
+
<
0
1
7
4
7
4
0
(
(
)
(( )
( )
)
( )
lh
Let e be the index of an algorithm schema for 𝔄. Now define the partial recur-
sive function φ(x) = μy((WA(x) ∧ Der(e, x, y)) ∨ ¬WA(x)). But ψ
ϕ
φ
( )
( ( ))
.
( ( ))
x
x
h
x
=
−
ℓ
1
Therefore, ψ𝔄 is partial recursive.
Corollary 5.27
Every Markov-computable function φ is partial recursive.
Proof
Let 𝔄 be a normal algorithm over {1, B} such that φ(k1, …, kn) = l if and only 
if ((
,
,
))
k
k
l
n
1 …
=
. By Proposition 5.26, the function ψ𝔄 is partial recur-
sive. Define the recursive function γ( )
( )
x
x
=
−
lh
 1. If x
p
i
n
i
=
=
Π
0
11, then n = γ(x). 
(Remember that a stroke |, which is an abbreviation for a1, has Gödel number 
11. So, if x is the Gödel number of the numeral n, then γ(x) = n.) Recall that 
TR(k1, …, kn) is the Gödel number of (
,
,
)
k
kn
1 …
.
TR is primitive recursive (by Proposition 5.4). Then φ = γ ○ ψ𝔄 ○ TR is 
partial recursive.
The equivalence of Markov computability and Turing computability fol-
lows from Corollaries 5.25 and 5.27 and the known equivalence of Turing 
computability and partial recursiveness. Many other definitions of comput-
ability have been given, all of them turning out to be equivalent to Turing 
computability. One of the earliest definitions, λ-computability, was developed 
by Church and Kleene as part of the theory of λ-conversion (see Church, 1941). 
Its equivalence with the intuitive notion of computability is not immediately 
plausible and gained credence only when λ-computability was shown to be 
equivalent to partial recursiveness and Turing computability (see Kleene, 
1936b; Turing, 1937). All reasonable variations of Turing computability seem 
to yield equivalent notions (see Oberschelp, 1958; Fischer, 1965).



373
Computability
5.6  Decision Problems
A class of problems is said to be unsolvable if there is no effective procedure for 
solving each problem in the class. For example, given any polynomial f(x) with 
integral coefficients (for example, 3x5 − 4x4 + 7x2 − 13x + 12), is there an integer 
k such that f(k) = 0? We can certainly answer this question for various special 
polynomials, but is there a single general procedure that will solve the prob-
lem for every polynomial f(x)? (The answer is given below in paragraph 4.)
If we can arithmetize the formulation of a class of problems and assign 
to each problem a natural number, then this class is unsolvable if and only 
if there is no computable function h such that, if n is the number of a given 
problem, then h(n) yields the solution of the problem. If Church’s thesis is 
assumed, the function h has to be partial recursive, and we then have a more 
accessible mathematical question.
Davis (1977b) gives an excellent survey of research on unsolvable prob-
lems. Let us look at a few decision problems, some of which we already have 
solved.
	
1.	Is a statement form of the propositional calculus a tautology? Truth tables 
provide an easy, effective procedure for answering any such question.
	
2.	Decidable and undecidable theories. Is there a procedure for determining 
whether an arbitrary wf of a formal system S  is a theorem of S  ? If so, 
S  is called decidable; otherwise, it is undecidable.
	a.	 The system L of Chapter 1 is decidable. The theorems of L are the 
tautologies, and we can apply the truth table method.
	b.	 The pure predicate calculus PP and the full predicate calculus PF 
were both shown to be recursively undecidable in Proposition 3.54.
	c.	 The theory RR and all its consistent extensions (including Peano 
arithmetic S) have been shown to be recursively undecidable in 
Corollary 3.46.
	d.	 The axiomatic set theory NBG and all its consistent extensions are 
recursively undecidable (see page 273).
	e.	 Various theories concerning order structures or algebraic structures 
have been shown to be decidable (often by the method of quanti-
fier elimination). Examples are the theory of unbounded densely 
ordered sets (see page 115 and Langford, 1927), the theory of abe-
lian groups (Szmielew, 1955), and the theory of real-closed fields 
(Tarski, 1951). For further information, consult Kreisel and Krivine 
(1967, Chapter 4); Chang and Keisler (1973, Chapter 1.5); Monk (1976, 
Chapter 13); Ershov et al. (1965); Rabin (1977); and Baudisch et al. 
(1985). On the other hand, the undecidability of many algebraic the-
ories can be derived from the results in Chapter 3 (see Tarski et al., 
1953, II.6, III; Monk, 1976, Chapter 16).



374
Introduction to Mathematical Logic
	
3.	Logical validity. Is a given wf of quantification theory logically valid? By 
Gödel’s completeness theorem (Corollary 2.19), a wf is logically valid if 
and only if it is provable in the full predicate calculus PF. Since PF is 
recursively undecidable (Proposition 3.54), the problem of logical valid-
ity is recursively unsolvable.
However, there is a decision procedure for the logical validity of wfs 
of the pure monadic predicate calculus (Exercise 3.59).
There have been extensive investigations of decision procedures for 
various important subclasses of wfs of the pure predicate calculus; for 
example, the class (∀ ∃ ∀) of all closed wfs of the form (∀x)(∃y)(∀z)B(x, 
y, z), where B(x, y, z) contains no quantifiers. See Ackermann (1954), 
Dreben and Goldfarb (1980) and Lewis (1979).
	
4.	Hilbert’s Tenth Problem. If f(x1, …, xn) is a polynomial with integral coeffi-
cients, are there integers k1, …, kn such that f(k1, …, kn) = 0? This difficult 
decision problem is known as Hilbert’s tenth problem.
For one variable, the solution is easy. When a0, a1, …, an are integers, 
any integer x such that anxn + ⋯ + a1x + a0 = 0 must be a divisor of a0.
Hence, when a0 ≠ 0, we can test each of the finite number of divisors 
of a0. If a0 = 0, then x = 0 is a solution. However, there is no analogous 
procedure when the polynomial has more than one variable. It was 
finally shown by Matiyasevich (1970) that there is no decision procedure 
for determining whether a polynomial with integral coefficients has 
a solution consisting of integers. His proof was based in part on some 
earlier work of Davis et al. (1961). The proof ultimately relies on basic 
facts of recursion theory, particularly the existence of a non-recursive 
r.e. set (Proposition 5.21(e)). An up-to-date exposition may be found in 
Matiyasevich (1993).
	
5.	Word problems.
	
	 Semi-Thue Systems. Let B = {b1, …, bn} be a finite alphabet. Remember that 
a word of B is a finite sequence of elements of B. Moreover, the empty 
sequence Λ is considered a word of B. By a production of B we mean an 
ordered pair 〈u, v〉, where u and v are words of B. If p = 〈u, v〉 is a produc-
tion of B, and if w and w′ are words of B, we write w ⇒p w′ if w′ arises from 
w by replacing a part u of w by v. (Recall that u is a part of w if there exist 
(possibly empty) words w1 and w2 such that w = w1uw2.)
By a semi-Thue system on B we mean a finite set S of productions of B. For 
words w and w′ of B, we write w ⇒S w′ if there is a finite sequence w0, w1, …, 
wk (k ≥ 0) of words of B such that w = w0, w′ = wk, and, for 0 ≤ i < k, there is a 
production p of S such that wi ⇒p wi+1. Observe that w ⇒S w for any word w 
of B. Moreover, if w1 ⇒S w2 and w2 ⇒S w3, then w1 ⇒S w3. In addition, if w1 ⇒S 
w2 and w3 ⇒S w4, then w1 w3 ⇒S w2 w4. Notice that there is no fixed order in 
which the productions have to be applied and that many different produc-
tions of S  might be applicable to the same word.



375
Computability
By a Thue system we mean a semi-Thue system such that, for every produc-
tion 〈u, v〉, the inverse 〈v, u〉 is also a production. Clearly, if S  is a Thue system 
and w ⇒S w′, then
w′ ⇒S w. Hence, ⇒S is an equivalence relation on the set of words of the 
alphabet of S.
Example
Let S  # be the Thue system that has alphabet {b} and productions 〈b3, Λ〉 and 
〈Λ, b3〉. It is easy to see that every word is transformable into b2, b, or Λ.
By a semigroup we mean a nonempty set G together with a binary operation 
on G (denoted by the juxtaposition uv of elements u and v) that satisfies the 
associative law x(yz) = (xy)z. An element y such that xy = yx = x for all x in G 
is called an identity element. If an identity element exists, it is unique and is 
denoted 1.
A Thue system S  on an alphabet B determines a semigroup G with an 
identity element. In fact, for each word w of B, let [w] be the set of all words 
w′ such that w ⇒S w′. [w] is just the equivalence class of w with respect to ⇒S . 
Let G consist of the sets [w] for all words w of B. If U and V are elements of 
G, choose a word u in U and a word v in V. Let UV stand for the set [uv]. This 
defines an operation on G, since, if u′ is any word in U and v′ is any word in 
V, [uv] = [u′v′].
Exercises
5.65	 For the set G determined by the Thue system S, prove:
	
a.	 (UV) W = U(VW) for all members U, V and W of G.
	
b.	 The equivalence class [Λ] of the empty word Λ acts as an identity 
element of G.
5.66	 a.	 Show that a semigroup contains at most one identity element.
	b.	 Give an example of a semigroup without an identity element.
A Thue system S provides what is called a finite presentation of the corre-
sponding semigroup G. The elements b1, …, bm of the alphabet of S  are called 
generators, and the productions 〈u, v〉 of S  are written in the form of equa-
tions u = v. These equations are called the relations of the presentation. Thus, 
in the Example above, b is the only generator and b3 = Λ can be taken as the 
only relation. The corresponding semigroup is a cyclic group of order 3.
If S  is a semi-Thue or Thue system, the word problem for S  is the problem 
of determining, for any words w and w′, whether w ⇒S w′.
Exercises
5.67	 Show that, for the Thue system S  # in the Example, the word problem is 
solvable.



376
Introduction to Mathematical Logic
5.68	 Consider the following Thue system S. The alphabet is {a, b, c, d} and 
the productions are 〈ac, Λ〉, 〈ca, Λ〉, 〈bd, Λ〉, 〈db, Λ〉, 〈a3, Λ〉, 〈b2, Λ〉, 〈ab, 
ba〉, and their inverses.
	a.	 Show that c ⇒S a2 and d ⇒S b.
	b.	 Show that every word of S  can be transformed into one of the words 
a, a2, b, ab, a2b, and Λ.
	c.	 Show that the word problem for S  is solvable. [Hint: To show that 
the six words of part (b) cannot be transformed into one another, 
use the cyclic group of order 6 generated by an element g, with 
a = g2 and b = g3.]
Proposition 5.30
(Post, 1947) There exists a Thue system with a recursively unsolvable word 
problem.
Proof
Let T   be a Turing machine with alphabet {a0, a1, …, an} and internal states 
{q0, q1, …, qm}. Remember that a tape description is a sequence of symbols 
describing the condition of T  at any given moment; it consists of symbols 
of the alphabet of T  plus one internal state qj, and qj is not the last symbol 
of the description. T  is in state qj, scanning the symbol following qj, and 
the alphabet symbols, read from left to right, constitute the entire tape at 
the given moment. We shall construct a semi-Thue system S  that will reflect 
the operation of T   : each action induced by quadruples of T   will be copied 
by productions of S. The alphabet of S  consists of {a0, a1, …, an, q0, q1, …, qm, β, 
δ, ξ}. The symbol β will be placed at the beginning and end of a tape descrip-
tion in order to “alert” the semi-Thue system when it is necessary to add an 
extra blank square on the left or right end of the tape. We wish to ensure that, 
if W
W
⇒
′
T
, then βWβ ⇒S βW′β. The productions of S are constructed from 
the quadruples of T   in the following manner.
	
a.	If qjaiakqr is a quadruple of T,  let 〈qjai, arqk〉 be a production of S.
	
b.	If qjaiRqr is a quadruple of T, let 〈qjaiaℓ, aiqraℓ〉 be a production of S  for 
every aℓ. In addition, let 〈qjai β ai, qra0 β〉 be a production of S. (This last 
production adds a blank square when Treaches the right end of the 
tape and is ordered to move right.)
	
c.	If qjaiLqr is a quadruple of T, let 〈aℓqjai, qralai〉 be a production of S   for 
each aℓ. In addition, let 〈β qjai, β qra0ai〉 be a production of S. (This last 
production adds a blank square to the left of the tape when this is 
required.)
	
d.	If there is no quadruple of T     beginning with qjai, let S  contain the following 
productions: 〈qjai, δ〉, 〈δ aℓ, δ〉 for all aℓ; 〈δ β, ξ〉, 〈aℓ ξ, ξ〉 for all aℓ; and 〈β ξ, ξ〉.



377
Computability
T   stops when it is in a state qj, scanning a symbol ai, such that qjai does not 
begin a quadruple of T.   In such a case, S  would replace qjai in the final tape 
description of T   by δ. Then δ proceeds to annihilate all the other symbols to 
its right, including the rightmost β, whereupon it changes to ξ. ξ then anni-
hilates all symbols to its left, including the remaining β. The final result is ξ 
alone. Hence:
(□) For any initial tape description α, T     halts when and only when βαβ ⇒S ξ
Now, enlarge S  to a Thue system S  ′ by adding to S  the inverses of all the 
productions of S. Let us show that
(∇) For any initial tape description α of T,  βαβ ⇒S′ ξ if and only if βαβ ⇒S ξ
Clearly, if βαβ ⇒S ξ, then βαβ ⇒S′ ξ. Conversely, assume for the sake of 
contradiction that βαβ ⇒S′ ξ, but it is not the case that βαβ ⇒S ξ. Consider a 
sequence of words leading from β α β to ξ in S  ′:
	
βαβ
ξ
=
⇒
…⇒
⇒
=
′
′
′
−
w
w
w
0
1
S
S
S
t
t
Here, each arrow is intended to indicate a single application of a produc-
tion. It is clear from the definition of S   that no production of S   applies to ξ 
alone. Hence, the last step in the sequence wt−1 ⇒S′ ξ must be the result of a 
production of S. So, wt−1 ⇒S ξ. Working backward, let us find the least p such 
that wp ⇒S ξ. Since we have assumed that it is not true that βαβ ⇒S ξ, we must 
have p > 0. By the minimality of p, it is not true that wp−1 ⇒S wp. Therefore, 
wp ⇒S wp−1. Examination of the productions of S shows that each of the words 
w0, w1, …, wt must contain exactly one of the symbols q0, q1, …, qm, δ, or ξ, 
and that, to such a word, at most one production of S   is applicable. But, wp is 
transformed into both wp+1 and wp−1 by productions of S. Hence, wp−1 = wp+1. 
But, wp+1 ⇒S ξ. Hence, wp−1 ⇒S ξ, contradicting the definition of p. This estab-
lishes (∇).
Now, let T be a Turing machine with a recursively unsolvable halting 
problem (Proposition 5.14). Construct the corresponding Thue system S  ′ as 
above. Then, by (□) and (∇), for any tape description α, T    halts if and only if 
βαβ ⇒S′ ξ. So, if the word problem for S′ were recursively solvable, the halt-
ing problem for T   would be recursively solvable. (The function that assigns 
to the Gödel number of α the Gödel number of 〈βαβ, ξ〉 is clearly recursive 
under a suitable arithmetization of the symbolism of Turing machines and 
Thue systems.) Thus, S′ has a recursively unsolvable word problem.
That the word problem is unsolvable even for certain Thue systems on a two-
element alphabet (semigroups with two generators) was proved by Hall (1949).
	
a.	Finitely presented groups. A finite presentation of a group consists of a finite 
set of generators g1, …, gr and a finite set of equations W1 = W1′, …, Wt 
= Wt′ between words of the alphabet B
g
g g
g
=
…
…
−
−
{
,
,
,
,
,
}.
1
1
1
1
r
r
 What 
is really involved here is a Thue system S with alphabet B, produc-
tions 〈W1, W1′〉, …, 〈Wt, Wt′〉 and their inverses, and all the productions 



378
Introduction to Mathematical Logic
〈
〉〈
〉
−
−
g g
g g
i
i
i
i
1
1
,
,
,
Λ
Λ  and their inverses. The corresponding semigroup 
G is actually a group and is called a finitely presented group. The word 
problem for G (or, rather, for the finite presentation of G) is the word 
problem for the Thue system S.
Problems that concern word problems for finitely presented groups are 
generally much more difficult than corresponding problems for finitely 
presented semigroups (Thue systems). The existence of a finitely presented 
group with a recursively unsolvable word problem was proved, indepen-
dently, by Novikov (1955) and Boone (1959). Other proofs have been given by 
Higman (1961), Britton (1963), and McKenzie and Thompson (1973). (See also 
Rotman, 1973.) Results on other decision problems connected with groups 
may be found in Rabin (1958). For corresponding problems in general alge-
braic systems, consult Evans (1951).



379
Appendix A: Second-Order Logic
Our treatment of quantification theory in Chapter 2 was confined to first-
order logic; that is, the variables used in quantifiers were only individual 
variables. The axiom systems for formal number theory in Chapter 3 and 
set theory in Chapter 4 also were formulated within first-order languages. 
This restriction brings with it certain advantages and disadvantages, and 
we wish now to see what happens when the restriction is lifted. That will 
mean allowing quantification with respect to predicate and function vari-
ables. Emphasis will be on second-order logic, since the important differ-
ences between first-order and higher-order logics already reveal themselves 
at the second-order level. Our treatment will offer only a sketch of the basic 
ideas and results of second-order logic.
Let L1C be the first-order language in which C is the set of nonlogical 
constants (i.e., individual constants, function letters, and predicate letters). 
Start with the language L1C, and add function variables gi
n gand predicate 
variables Ri
n, where n and i are any positive integers.* (We shall use gn, hn, … 
to stand for any function variables of n arguments and Rn, Sn, …, Xn, Yn, Zn 
to stand for any predicate variables of n arguments; we shall also omit the 
superscript n when the value of n is clear from the context.) Let 〈u〉n stand 
for any sequence of individual variables u1, …, un
† and let ∀〈u〉n stand for 
the expression (∀u1) … (∀un). Similarly, let 〈t〉n stand for a sequence of terms 
t1, …, tn. We expand the set of terms by allowing formation of terms gn(〈t〉n), 
where gn is a function variable, and we then expand the set of formulas by 
allowing formation of atomic formulas A
t
i
n
n
〈〉
(
) and Rn(〈t〉n) where 〈t〉n is 
any sequence of the newly enlarged set of terms, Ai
n is any predicate letter 
of C, and Rn is any n-ary predicate variable. Finally, we expand the set of 
formulas by quantification (∀gn) B and (∀Rn) B with respect to function and 
predicate variables.
Let L2C denote the second-order language obtained in this way. The lan-
guage L2C will be called a full second-order language. The adjective “full” 
indicates that we allow both function variables and predicate variables and 
that there is no restriction on the arity n of those variables. An example of 
a nonfull second-order language is the second-order monadic predicate 
*	 We use bold letters to avoid confusion with function letters and predicate letters. Note that 
function letters and predicate letters are supposed to denote specific operations and rela-
tions, whereas function variables and predicate variables vary over arbitrary operations and 
relations.
†	 In particular, 〈x〉n will stand for x1, …, xn.



380
Appendix A: Second-Order Logic
­language in which there are no function letters or variables, no predicate let-
ters, and only monadic predicate variables.*
It is not necessary to take = as a primitive symbol, since it can be defined 
in the following manner.
Definitions
	
t
u
t
u
x
x
x
n
n
n
n
n
n
=
∀
⇔
=
∀〈〉
〈〉
(
) =
〈
stands for
stands for
(
)(
)
R
R
R
g
h
g
h
1
1
1
〉
(
)
(
)
=
∀〈〉
〈〉
(
) ⇔
〈〉
(
)
(
)
n
n
n
n
n
n
n
n
x
x
x
R
S
R
S
stands for
Standard Second-Order Semantics for L2C
For a given language L2C, let us start with a first-order interpretation with 
domain D. In the first-order case, we defined satisfaction for the set ∑ of 
denumerable sequences of members of D. Now, instead of ∑, we use the 
set ∑2 of functions s that assign to each individual variable a member of 
D, to each function variable gn some n-ary operation s(gn) on D, and to 
each predicate variable Rn some n-ary relation† s(Rn) on D. For each such 
s, we extend the denotations determined by s by specifying that, for any 
terms t1, …, tn and any function variable gn, the denotation s(gn(t1, …, tn)) is 
s(gn)(s(t1), …, s(tn)). The first-order definition of satisfaction is extended as 
follows:
	
a.	For any predicate variable Rn and any finite sequence 〈t〉n of terms, s 
satisfies Rn(〈t〉n) if and only if 〈s(t1), …, s(tn)〉 ∈ s(Rn).
	
b.	s satisfies (∀gn) B if and only if s′ satisfies B for every s′ in ∑2  that 
agrees with s except possibly at gn.
	
c.	s satisfies (∀Rn) B if and only if s′ satisfies B  for every s′ in ∑2  that 
agrees with s except possibly at Rn.
The resulting interpretation M  is called a standard interpretation of the given 
language.
*	 Third-order logics are obtained by adding function and predicate letters and variables that 
can have as arguments individual variables, function and predicate letters, and second-order 
function and predicate variables and then allowing quantification with respect to the new 
function and predicate variables. This procedure can be iterated to obtain nth-order logics for 
all n ≥ 1.
†	 An n-ary relation on D is a subset of the set Dn of n-tuples of D. When n = 1, an n-ary relation 
is just a subset of D.



381
Appendix A: Second-Order Logic
A formula B  is said to be true for a standard interpretation M  (written 
M  ⊧ B) if B is satisfied by every s in ∑2. B  is false for M  if no function s in ∑2 
satisfies B.
A formula B  is said to be standardly valid if B is true for all standard 
interpretations. B   is said to be standardly satisfiable if B   is satisfied by 
some s in ∑2 in some standard interpretation. A formula C  is said to be 
a ­standard logical consequence of a set Γ of formulas if, for every standard 
interpretation, every s in ∑2 that satisfies every formula in Γ also satisfies C. 
A formula B is said to standardly logically imply a formula C if C is a logical 
consequence of {B }.
The basic properties of satisfaction, truth, logical consequence, and logi-
cal implication that held in the first-order case (see (I)–(XI) on pages 57–60) 
also hold here for their standard versions. In particular, a sentence 
B   is standardly satisfiable if and only if B   is true for some standard 
interpretation.
We shall see that second-order languages have much greater expressive 
power than first-order languages. This is true even in the case where the set 
C of nonlogical constants is empty. The corresponding language L2∅ will 
be denoted L2 and called the pure full second-order language. Consider the 
following sentence in L2:
	
( ) (
)(
)(
)[( ( )
(
)( ( )
( ( ))))
(
) ( )]
1
∃
∃
∀
∧∀
⇒
⇒∀
g
R
R
R
R g
R
x
x
y
y
y
x
x
This sentence is true for a standard interpretation if and only if the domain 
D is finite or denumerable. To see this, consider an operation ɡ and ele-
ment x given by this sentence. By induction, define the sequence x, ɡ(x), 
ɡ(ɡ(x)), ɡ(ɡ(ɡ(x))), …, and let R be the set of objects in this sequence. R is 
finite or denumerable, and (1) tells us that every object in D is in R. Hence, 
D = R and D is finite or denumerable. Conversely, assume that D is finite or 
denumerable. Let F be a one–one function from D onto ω (when D is denu-
merable) or onto an initial segment {0, 1, …, n} of ω (when D is finite).* Let 
x = F1(0) and define an operation g on D in the following manner. When D 
is denumerable, ɡ(u) = F−1(F(u) + 1) for all u in D; when D is finite, let ɡ(u) = 
F−1(F(u) + 1)) if F(u) < n and ɡ(u) = x if F(u) = n. With this choice of ɡ and x, 
(1) holds.
Exercise
A.1	 Show that there is no first-order sentence B such that B is true in an 
interpretation if and only if its domain is finite or denumerable. (Hint: 
Use Corollary 2.22.)
*	 Remember that the domain of an interpretation is assumed to be nonempty.



382
Appendix A: Second-Order Logic
Let us introduce the abbreviations Y1 ⊆ X1 for (∀u)(Y1(u) ⇒ X1(u)), NonEm 
(X1) for (∃u)(X1(u)), and Asym (R2, X1) for (∀u)(∀v)(X1(u) ∧ X1(v) ∧ R2(u, v) ⇒ 
¬R2(v, u)). Let R2 We X1 stand for the second-order formula:
	
Asym(
NonEm
R
X
Y
Y
X
Y
Y
Y
2
1
1
1
1
1
1
1
,
)
(
)(
(
)
(
)(
( )
(
)(
( )
∧∀
⊆
∧
⇒∃
∧∀
∧
≠
u
u
v
v
v
u
u v
⇒R2( , )))
Then R2 We X1 is satisfied by an assignment in a given standard interpre-
tation if and only if the binary relation assigned to R2 well-orders the set 
assigned to X1. (First note that the asymmetry Asym(R2, X1) implies that R2 is 
irreflexive on X1. To see that R2 is transitive on X1, assume R2(u, v) and R2(v, w). 
Letting Y1 = {u, v, w}, we leave it as an exercise to conclude that R2(u, w). To 
show that R2 is connected on X1, take any two distinct elements x and y of X1 
and consider Y2 = {x, y}.)
Let Suc(u, v, R2) stand for R2(v, u) ∧ (∀w)¬(R2(v, w) ∧ R2(w, u)), and let 
First(u, R2) stand for (∀v)(v ≠ u ⇒ R2(u, v)). Consider the following second-
order formula:
	
( ) (
)(
)(
(
)
( )
(
)(
( ,
)
(
)
(
2
2
1
2
1
1
2
∃
∃
∧∀
∧∀
¬
⇒∃
R
X
R
X
X
R
We
First
Suc
u
u
u
u
v
u, ,
))
(
)(
)(
( , )))
v
u
v v
u
v u
R
R
2
2
∧∃
∀
≠
⇒
This is true for a standard interpretation if and only if there is a well-­ordering 
of the domain in which every element other than the first is a successor and 
there is a last element. But this is equivalent to the domain being finite. 
Hence, (2) is true for a standard interpretation if and only if its domain is 
finite.
Exercise
A.2	 (a) Show that, for every natural number n, there is a first-order sentence 
the models of which are all interpretations whose domain contains at 
least n elements. (b) Show that, for every positive integer n, there is 
a first-order theory the models of which are all interpretations whose 
domain contains exactly n elements. (c) Show that there is no first-order 
sentence B that is true for any interpretation if and only if its domain is 
finite.
The second-order sentence (1) ∧ ¬(2) is true for a standard interpretation if 
and only if the domain is denumerable.
Exercises
A.3	 Show that there is no first-order sentence B  the models of which are all 
interpretations whose domain is denumerable.



383
Appendix A: Second-Order Logic
A.4	 Construct a second-order formula Den(X1) that is satisfied by an 
assignment in a standard interpretation if and only if the set assigned 
to X1 is denumerable.
Second-Order Theories
We define a second-order theory in a language L2C by adding the following 
new logical axioms and rules to the first-order axioms and rules:
(B4a) (∀Rn) B (Rn) ⇒B (Wn), where B (Wn) arises from B (Rn) by replacing 
all free occurrences of Rn by Wn and Wn is free for Rn in B (Rn).
(B4b) (∀gn) B (gn) ⇒B (hn), where B (hn) arises from B (gn) by replacing all 
free occurrences of gn by hn and hn is free for gn in B (gn).
(B5a) (∀Rn)( B ⇒C) ⇒ (B ⇒ (∀Rn) C), where Rn is not free in B.
(B5b) (∀gn)( B ⇒C) ⇒ (B ⇒ (∀gn) C), where gn is not free in B.
Comprehension Schema (COMP)
(∃Rn)(∀〈x〉n)(Rn(〈x〉n) ⇔B ), provided that all free variables of B  occur in 〈x〉n 
and Rn is not free in B.
Function Definition Schema (FUNDEF)
	
(
)
(
)
,
(
)
,
∀
∀〈〉
(
) ∃
〈〉
(
) ⇒∃
∀〈〉
(
)
〈〉
〈〉
+
+
+
R
R
g
R
g
n
n
n
n
n
n
n
n
n
x
y
x
y
x
x
x
1
1
1
1
n
(
)
(
)


New Rules
(Gen2a) (∀Rn) B  follows from B
(Gen2b) (∀gn) B  follows from B
Exercises
A.5	 Show that we can prove analogues of the usual equality axioms 
(A6)–(A7) in any second-order theory:
	
i.	 ⊢ t = t ∧ gn = gn ∧ Rn = Rn
	
ii.	 ⊢ t = s ⇒ (B  (t, t) ⇒B (t, s)), where B (t, s) arises from B (t, t) by replac-
ing zero or more occurrences of t by s, provided that s is free for t in 
B (t, t).
	
iii.	 ⊢ gn = hn ⇒ (B (gn, gn) ⇒B (gn, hn)), where B (gn, hn) arises from B (gn, 
gn) by replacing zero or more occurrences of gn by hn, provided that 
hn is free for gn in B (gn, gn).
	
iv.	 ⊢ Rn = Sn ⇒ (B (Rn, Rn) ⇒B (Rn, Sn)), where B (Rn, Sn) arises from B 
(Rn, Rn) by replacing zero or more occurrences of Rn by Sn, provided 
that Sn is free for Rn in B (Rn, Rn).



384
Appendix A: Second-Order Logic
A.6	 Formulate and prove a second-order analogue of the first-order deduc-
tion theorem (Proposition 2.5).
Let PC2 denote the second-order theory in the language L2C without any 
nonlogical axioms. PC2 is called a second-order predicate calculus.
Proposition A.1 (Soundness)
Every theorem of PC2 is standardly valid.
Proof
That all the logical axioms (except Comp and FunDef) are standardly 
valid and that the rules of inference preserve standard validity follow by 
­arguments like those for the analogous first-order properties. The standard 
validity of Comp and FunDef follows by simple set-theoretic arguments.
We shall see that the converse of Proposition A.1 does not hold. This will 
turn out to be not a consequence of a poor choice of axioms and rules but an 
inherent incompleteness of second-order logic.
Let us consider the system of natural numbers. No first-order theory will 
have as its models those and only those interpretations that are isomorphic 
to the system of natural numbers.* However, a second-order characterization 
of the natural numbers is possible. Let AR2 be the conjunction of the axioms 
(S1)–(S8) of the theory S of formal arithmetic (see page 154), and the following 
second-order principle of mathematical induction:
	
(
)
(
)
( )
(
)
( )
( )
(
)
( )
2 9
0
1
1
1
1
1
S
∀
∧∀
⇒
′
(
) ⇒∀


R
R
x
R x
R x
x R x
Notice that, with the help of Comp, all instances of the first-order axiom 
schema (S9) can be derived from (2S9).†
For any standard interpretation that is a model of AR2 we can prove the 
following result that justifies inductive definition.
*	 Let K be any first-order theory in the language of arithmetic whose axioms are true in the 
system of natural numbers. Add a new individual constant b and the axioms b
n
≠
 for every 
natural number n. The new theory K* is consistent, since any finite set of its axioms has a 
model in the system of natural numbers. By Proposition 2.17, K* has a model, but that model 
cannot be isomorphic to the system of natural numbers, since the object denoted by b cannot 
correspond to a natural number. 
†	 In AR2, the function letters for addition and multiplication and the associated axioms (S5)–
(S8) can be omitted. The existence of operations satisfying (S5)–(S8) can then be proved. See 
Mendelson (1973, Sections 2.3 and 2.5).



385
Appendix A: Second-Order Logic
Proposition A.2 (Iteration Theorem)
Let M  be a standard interpretation that is a model of AR2, and let D be the 
domain of M. Let c be an element of an arbitrary set W and let ɡ be a singu-
lary operation of W. Then there is a unique function F from D into W such 
that F(0) = c and (∀x)(x ∈ D ⇒ F(x′) = g(F(x))).*
Proof
Let C be the set of all subsets H of D × W such that 〈1, c〉 ∈ H and (∀x)(∀w)
(〈x, w〉 ∈ H ⇒ 〈x′, ɡ(w)〉 ∈ H). Note that D × W ∈ C. Let F be the intersection 
of all sets H in C. We leave it to the reader to prove the following assertions:
	
a.	F ∈ C
	
b.	F is a function from D into W. (Hint: Let B be the set of all x in D for 
which there is a unique w in W such that 〈x, w〉∈ F. By mathematical 
induction, show that B = D.)
	
c.	F(0) = c.
	
d.	F(x′) = ɡ(F(x)) for all x in D.
The uniqueness of F can be shown by a simple application of mathematical 
induction.
Proposition A.3 (Categoricity of AR2)
Any two standard interpretations M  and M  * that are models of AR2 are 
isomorphic.
Proof
Let D and D* be the domains of M  and M  *, 0 and 0* the respective zero 
elements, and f and f* the respective successor operations. By the iteration 
theorem applied to M, with W = D*, c = 0* and ɡ = f*, we obtain a function F 
from D into D* such that F(0) = 0* and F(f(x)) = f*(F(x)) for any x in D. An easy 
application of mathematical induction in M  * shows that every element of D* 
is in the range of F. To show that F is one–one, apply mathematical induction 
in M  to the set of all x in D such that (∀ y)[(y ∈ D ∧ y ≠ x)⇒F(x) ≠ F(y)].†
Let A consist of the nonlogical constants of formal arithmetic (zero, 
­successor, addition, multiplication, equality). Let N   be the standard 
*	 In order to avoid cumbersome notation, “0” denotes the interpretation in M of the individual 
constant “0,” and “x′” denotes the result of the application to the object x of the interpretation 
of the successor function.
†	 Details of the proof may be found in Mendelson (1973, Section 2.7).



386
Appendix A: Second-Order Logic
­interpretation of L2A  with the set of natural numbers as its domain and the 
usual interpretations of the nonlogical constants.
Proposition A.4
Let B  be any formula of L2 A . Then B  is true in N  if and only if AR2 ⇒B  is 
standardly valid.
Proof
Assume AR2 ⇒B is standardly valid. So AR2 ⇒B  is true in N . But AR2 is 
true in N. Hence, B is true in N . Conversely, assume B  is true in N. We must 
show that AR2 ⇒B  is standardly valid. Assume that AR2 is true in some 
standard interpretation M  of L2A. By the categoricity of AR2, M  is isomor-
phic to N. Therefore, since B  is true in N, B  is true in M. Thus, AR2 ⇒B  is 
true in every standard interpretation of L2A , that is, AR2 ⇒B  is standardly 
valid.
Proposition A.5
	
a.	The set SV of standardly valid formulas of L2A  is not effectively 
enumerable.
	
b.	SV is not recursively enumerable, that is, the set of Gödel numbers of 
formulas in SV is not recursively enumerable.
Proof
	
a.	Assume that SV is effectively enumerable. Then, by Proposition A4, 
we could effectively enumerate the set TR of all true formulas of first-
order arithmetic by running through SV, finding all formulas of the 
form AR2 ⇒B, where B  is a formula of first-order arithmetic, and 
listing those formulas B. Then the theory TR  would be decidable, 
since, for any closed formula C, we could effectively enumerate TR 
until either C or its negation appears. By Church’s thesis, TR  would 
be recursively decidable, contradicting Corollary 3.46 (since TR  is a 
consistent extension of RR).
	
b.	This follows from part (a) by Church’s thesis.
The use of Church’s thesis in the proof could be avoided by a consistent use 
of recursion-theoretic language and results. The same technique as the one 
used in part (a), together with Tarski’s theorem (Corollary 3.44), would show 
the stronger result that the set (of Gödel numbers) of the formulas in SV is 
not arithmetical.



387
Appendix A: Second-Order Logic
Corollary A.6
The set of all standardly valid formulas is not effectively (or recursively) 
enumerable.
Proof
An enumeration of all standardly valid formulas would yield an enumera-
tion of all standardly valid formulas of L2A , since the set of formulas of 
L2A  is decidable (recursively decidable).
Corollary A.7
There is no axiomatic formal system whose theorems are the standardly 
valid formulas of L2A .
Proof
If there were such an axiom system, we could enumerate the standardly 
valid formulas of L2A , contradicting Corollary A.5.
Proposition A.8 (Incompleteness of Standard Semantics)
There is no axiomatic formal system whose theorems are all standardly valid 
formulas.
Proof
If there were such an axiom system, we could enumerate the set of all stan-
dardly valid formulas, contradicting Corollary A.6.
Proposition A.8 sharply distinguishes second-order logic from first-order 
logic, since Gödel’s completeness theorem tells us that there is an axiomatic 
formal system whose theorems are all logically valid first-order formulas. 
Here are some additional important properties enjoyed by first-order theo-
ries that do not hold for second-order theories:
	
I.	Every consistent theory has a model. To see that this does not hold 
for second-order logic (with “model” meaning “model in the sense 
of the standard semantics”), add to the theory AR2 a new individ-
ual constant b. Let T  be the theory obtained by adding to AR2 the 
set of axioms b
n
≠
 for all natural number n. T  is consistent. (Any 
proof involves a finite number of the axioms b
n
≠
. AR2 plus any 
finite number of the axioms b
n
≠
 has the standard interpretation as 



388
Appendix A: Second-Order Logic
a model, with b interpreted as a suitable natural number. So every 
step of the proof would be true in N. Therefore, a contradiction can-
not be proved.). But T has no standard model. (If M  were such a 
model, AR2 would be true in M. Hence, M  would be isomorphic to 
N, and so the domain of M  would consist of the objects denoted by 
the numerals n. But this contradicts the requirement that the domain 
of M  would have to have an object denoted by “b” that would satisfy 
the axioms b
n
≠
 for all natural numbers n.)
	
II.	The compactness property: a set Γ of formulas has a model if and 
only if every finite subset of Γ has a model. A counterexample is 
furnished by the set of axioms of the theory T  in (I) earlier.
	 III.	The upward Skolem–Löwenheim theorem: every theory that has an 
infinite model has models of every infinite cardinality. In second-
order logic this fails for the theory AR2. By Proposition A.3, all mod-
els of AR must be denumerable.
	 IV.	The downward Skolem–Löwenheim theorem: every model M  of a 
theory has a countable elementary submodel.* In second-order logic, 
a counterexample is furnished by the second-order categorical the-
ory for the real number system.† Another argument can be given 
by the following considerations. We can express by the following 
second-order formula P (Y1, X1) the assertion that Y1 is equinumer-
ous with the power set of X1:
	
(
) (
)(
)(
(
)
(
)
(
)(
( )
[
(
, )
(
,
∃
∀
∀
[
∧
∧∀
⇒
⇔
R
X
X
Y
R
2
1
2
1
1
1
2
1
2
1
2
2
x
x
x
x
y
y
R x y
x
y
x
x
x
x
y
y
x y
)])
(
)(
(
)(
( )
(
)(
( )(
( , )))
)
⇒
=
∧∀
⊆
⇒∃
∧
∀
⇔

1
2
1
1
1
1
1
2
W
W
Y
X
W
R

R2 correlates with each x in X1 the set of all y in Y1 such that R2(x, y). Now 
consider the following sentence Cont:
	
∃(
) ∃(
)
(
) ∧∀
(
)
( ) ∧
(
)
(
)
X
Y
X
Y
Y
X
1
1
1
1
1
1
Den
y
y
P
,
Then Cont is true in a standard interpretation if and only if the domain of the 
interpretation has the power of the continuum, since the power set of a denu-
merable set has the power of the continuum. See Shapiro (1991, Section 5.1.2) 
*	 For a definition of elementary submodel, see Section 2.13.
†	 The axioms are those for an ordered field (see page 97) plus a second-order completeness 
axiom. The latter can be taken to be the assertion that every nonempty subset that is bounded 
above has a least upper bound (or, equivalently, that no Dedekind cut is a gap). For a proof of 
categoricity, see Mendelson (1973, Section 5.4).



389
Appendix A: Second-Order Logic
and Garland (1974) for more information about the definability of cardinal 
numbers in second-order logic.
Exercises
A.7 Show that a sentence of pure second-order logic is true in a standard 
interpretation M  if and only if it is true in any other standard interpre-
tation whose domain has the same cardinal number as that of M.
A.8	 a.	 Show that there is a formula Cont (X1) of pure second-order logic 
that is satisfied by an assignment in an interpretation if and only if 
the set assigned to X1 has the power of the continuum.
	
b.	 Find a sentence CH of pure second-order logic that is standardly 
valid if and only if the continuum hypothesis is true.*
Henkin Semantics for L2C
In light of the fact that completeness, compactness, and the Skolem–
Löwenheim theorems do not hold in second-order logic, it is of some inter-
est that there is a modification of the semantics for second-order logic that 
removes those drawbacks and restores a completeness property. The funda-
mental ideas sketched later are due to Henkin (1950).
Start with a first-order interpretation with domain D. For each positive 
integer n, choose a fixed collection D (n) of n-ary relations on D and a fixed 
collection F  (n) of n-ary operations on D. Instead of ∑2, we now use the set 
∑2
H of assignments s in ∑2 such that, for each predicate variable Rn, s(Rn) is 
in D  (n) and, for each function variable gn, s(gn) is in F  (n). The definitions of 
satisfaction and truth are the same as for standard semantics, except that ∑2 
is replaced by ∑2
H. Such an interpretation will be called a Henkin interpreta-
tion. Using a Henkin interpretation amounts to restricting the ranges of the 
predicate and function variables. For example, the range of a predicate vari-
able R1 need not be the entire power set P  (D) of the domain D. In order for 
a Henkin interpretation H   to serve as an adequate semantic framework, we 
must require that all instances of the comprehension schema and the func-
tion definition schema are true in H   . A Henkin interpretation for which this 
condition is met will be called a general model. A formula that is true in all 
general models will be said to be generally valid, and a formula that is satis-
fied by some assignment in some general model will be said to be generally 
satisfiable. We say that B  generally implies C if B  ⇒C is generally valid and that 
B  is generally equivalent to C if B  ⇔C is generally valid.
A standard interpretation on a domain D determines a corresponding gen-
eral model in which D  (n) is the set of all n-ary relations on D and F  (n) is the 
set of all n-ary operations on D. Such a general model is called a full general 
*	 We take as the continuum hypothesis the assertion that every subset of the set of real num-
bers is either finite or denumerable or is equinumerous with the set of all real numbers.



390
Appendix A: Second-Order Logic
model. Standard satisfaction and truth are equivalent to Henkin satisfaction 
and truth for the corresponding full general model. Hence, the following 
statements are obvious.
Proposition A.9
	
a.	Every generally valid formula is also standardly valid.
	
b.	Every standardly satisfiable formula is generally satisfiable.
We also have the following strengthening of Proposition A.1.
Proposition A.10
Every theorem of PC2 is generally valid.
Proof
The general validity of (Comp) and (FunDef) follows from the definition of 
a general model. The proofs for the other logical axioms are similar to those 
in the first-order case, as is the verification that general validity is preserved 
by the rules of inference.
Proposition A.11 (General Second-Order Completeness)
The theorems of PC2 coincide with the generally valid formulas of L2C.
Proof
Let B  be a generally valid formula of L2C. We must show that B is a theorem 
of PC2. (It suffices to consider only closed formulas.) Assume, for the sake of 
contradiction, that B  is not a theorem of PC2. Then, by the deduction theo-
rem, the theory PC2+{¬B } is consistent. If we could prove that any consistent 
extension of PC2 has a general model, then it would follow that PC2+{¬B } 
has a general model, contradicting our hypothesis that B is generally valid. 
Hence, it suffices to establish the following result.
Henkin’s Lemma
Every consistent extension T  of PC2 has a general model.
Proof
The strategy is the same as in Henkin’s proof of the fact that every consis-
tent first-order theory has a model. One first adds enough new individual 



391
Appendix A: Second-Order Logic
constants, function letters, and predicate letters to provide “witnesses” for all 
existential sentences. For example, for each sentence (∃x) C (x), there will be a 
new individual constant b such that (∃x) C (x) ⇒C (b) can be consistently added 
to the theory. (See Lemma 2.15 for the basic technique.) The same thing is 
done for existential quantifiers (∃gn) and (∃Rn). Let T * be the consistent exten-
sion of T  obtained by adding all such conditionals as axioms. Then, by the 
method of Lindenbaum’s lemma (Lemma 2.14), we inductively extend T * to a 
maximal consistent theory T #. A general model M  of T  can be extracted from 
T #. The domain consists of the constant terms of T #. The range of the predi-
cate variables consists of the relations determined by the predicate letters of 
T #. A predicate letter B determines the relation B# such that B#〈t〉n holds in 
M  if and only if B#〈t〉n is a theorem of T #. The range of the function variables 
consists of the operations determined by the function letters of T #. If f is a 
function letter of T #, define an operation f # by letting f #(〈t〉n) = f(〈t〉n). A proof 
by induction shows that, for every sentence C, C is true in M  if and only if C is 
a theorem of T #. In particular, all theorems of T  are true in M.
The compactness property and the Skolem–Löwenheim theorems also 
hold for general models. See Manzano (1996, Chapter IV) or Shapiro (1991) 
for detailed discussions.*
Corollary A.12
There are standardly valid formulas that are not generally valid.
Proof
By Corollary A.7, there is no axiomatic formal system whose theorems are 
the standardly valid formulas of L2A . By Proposition A.11, the generally 
valid formulas of L2A  are the theorems of the second-order theory PA 2. 
Hence, the set of standardly valid formulas of L2A  is different from the set 
of generally valid formulas of L2A . Since all generally valid formulas are 
standardly valid, there must be some standardly valid formula that is not 
generally valid.
We can exhibit an explicit sentence that is standardly valid but not gener-
ally valid. The Gödel–Rosser incompleteness theorem (Proposition 3.38) can 
be proved for the second-order theory AR2. Let R be Rosser’s undecidable 
sentence for AR2.† If AR2 is consistent, R  is true in the standard model of 
arithmetic. (Recall that R  asserts that, for any proof in AR2 of R, there is a 
proof in AR2, with a smaller Gödel number, of ¬R. If AR2 is consistent, R 
is undecidable in AR2 and, therefore, there is no proof in AR2 of R, which 
*	 Lindström (1969) has shown that, in a certain very precise sense, first-order logic is the stron-
gest logic that satisfies the countable compactness and Skolem–Löwenheim theorems. So 
general models really are disguised first-order models.
†	 We must assume that AR is consistent.



392
Appendix A: Second-Order Logic
makes R trivially true.) Hence, AR2 ⇒R is standardly valid, by Proposition 
A.4. However, AR2 ⇒R is not generally valid. For, if AR2 ⇒R  were generally 
valid, it would be provable in PA  2, by Proposition A.11. Hence, R  would be 
provable in AR2, contradicting the fact that it is an undecidable sentence of 
AR2.
Exercise
A.9 a.	 Show that the second-order theory AR2 is recursively undecidable.
	
b.	 Show that the pure second-order predicate calculus PA  2 is recur-
sively undecidable.*
It appears that second-order and higher-order logics were the implicitly 
understood logics of mathematics until the 1920s. The axiomatic charac-
terization of the natural numbers by Dedekind and Peano, the axiomatic 
characterization of the real numbers as a complete ordered field by Hilbert 
in 1900, and Hilbert’s axiomatization of Euclidean geometry in 1902 (in the 
French translation of his original 1899 book) all presupposed a second-order 
logic in order to obtain the desired categoricity. The distinction between 
first-order and second-order languages was made by Löwenheim (1915) and 
by Hilbert in unpublished 1917 lectures and was crystal clear in Hilbert and 
Ackermann’s (1950),† where the problem was posed about the completeness 
of their axiom system for first-order logic. The positive solution to this prob-
lem presented in Gödel (1930), and the compactness and Skolem–Löwenheim 
theorems that followed therefrom, probably made the use of first-order logic 
more attractive. Another strong point favoring first-order logic was the fact 
that Skolem in 1922 constructed a first-order system for axiomatic set theory 
that overcame the imprecision in the Zermelo and Fraenkel systems.‡ Skolem 
was always an advocate of first-order logic, perhaps because it yielded the 
relativity of mathematical notions that Skolem believed in. Philosophical 
support for first-order logic came from W.V. Quine, who championed the 
position that logic is first-order logic and that second-order logic is just set 
theory in disguise.
The rich lodes of first-order model theory and proof theory kept logicians 
busy and satisfied for over a half-century, but recent years have seen a revival 
of interest in higher-order logic and other alternatives to first-order logic, 
*	 The pure second-order monadic predicate logic MP2 (in which there are no nonlogical con-
stants and no function variables and all second-order predicate variables are monadic) is 
recursively decidable. See Ackermann (1954) for a proof. The earliest proof was found by 
Löwenheim (1915), and simpler proofs were given by Skolem (1919) and Behmann (1922).
†	 Hilbert and Ackermann (1950) is a translation of the second (1938) edition of a book which 
was first published in 1928 as Grundzüge der theoretischen Logik.
‡	 See Moore (1988) and Shapiro (1991) for more about the history of first-order logic. Shapiro 
(1991) is a reliable and thorough study of the controversies involving first-order and second-
order logic.



393
Appendix A: Second-Order Logic
and the papers in the book Model-Theoretic Logics (edited by Barwise and 
Feferman 1985) offer a picture of these new developments.* Barwise (1985) 
lays down the challenge to the old first-order orthodoxy, and Shapiro (1991) 
and Corcoran (1987, 1998) provide philosophical, historical, and technical 
support for higher-order logic. Of course, we need not choose between first-
order and higher-order logic; there is plenty of room for both.
*	 Van Benthem and Doets (1983) also provide a high-level survey of second-order logic and its 
ramifications.



395
Appendix B: First Steps in 
Modal Propositional Logic
(#) It is necessary that 1 + 1 = 2.
(##) It is possible that George Washington never met King George III of 
England.
These assertions are examples of the application of the modal operators “nec-
essary” and “possible.” We understand here that “necessity” and “possibil-
ity” are used in the logical or mathematical sense.* There are other usages, 
such as “scientific necessity,” but, unless something is said to the contrary, 
we shall hold to the logical or mathematical sense.
In its classical usage, the notation ◻α stands for the assertion that α is neces-
sary. Here, “α” and other lowercase Greek letters will stand for propositions. 
In traditional modal logic, ⬦α was taken to assert that α is possible. As before, 
as basic propositional connectives we choose negation ¬ and the condi-
tional ⇒. The other standard connectives, conjunction ∧, disjunction ∨, and the 
biconditional ⇔, are introduced by definition in the usual way. The well-formed 
formulas (wfs) of modal propositional logic are obtained from the propositional 
letters A1, A2, A3, … by applying ¬, ⇒, and ◻ in the usual ways. Thus, each Aj is 
a wf, and if α and β are wfs, then (¬α), (α ⇒ β), and (◻α) are wfs. The expression 
(⬦α) is defined as (¬ (◻ (¬ α))), since asserting that α is possible is intuitively 
equivalent to asserting that the negation of α is not necessary.
We shall adopt the same conventions for omitting parentheses as in 
Chapter 1, with the additional proviso that ◻ and ⬦ are treated like ¬. For 
example, (¬ (◻ (¬ A1))) is abbreviated as ¬ ◻ ¬ A1, and ◻A1 ⇒ A1 is an abbre-
viation of ((◻A1) ⇒ A1). Finally, to avoid writing too many subscripts, we 
often will write A, B, C, D instead of A1, A2, A3, A4.
Our study of modal logic will begin with the study of various axiomatic 
theories. A theory is a set of formulas closed with respect to two rules: the 
traditional modus ponens rule
(MP): β follows from α and α ⇒ β
and the necessitation rule
(N): ◻α follows from α
*	 We could also say that the sentence “1 + 1 = 2” is logically necessary and the sentence “George 
Washington never met King George III of England” is logically possible by virtue of the mean-
ing of those sentences, but some people prefer to avoid use of the concept of “meaning.” If we 
should find out that George Washington actually did meet King George III, then the sentence 
(##) would still be true, but uninteresting. If we should find out that George Washington 
never did meet King George III, then, although (##) is true, it would be silly to assert it when 
we knew a stronger statement. In general, a sentence A logically implies that A is possible.



396
Appendix B: First Steps in Modal Propositional Logic
An axiomatic theory will be determined in the usual way by a set of axioms 
and the rules of inference (MP) and (N). Thus, a proof in such a theory is a 
finite sequence of wfs such that each wf in the sequence is either an axiom or 
follows by (MP) or (N) from the preceding wfs in the sequence, and a theorem 
of a theory is the last wf of any proof in the theory. We shall study several 
modal theories that have historical and theoretical importance. For some of 
those theories, the principal interpretation of ◻α will not be “α is necessary.” 
For example, ◻α may mean that α is provable (in a specified formal system).
Inclusion of the necessitation rule (N) may call for some explanation, since 
we ordinarily would not want the necessity of α to follow from α. However, 
the systems to be studied here initially will have as theorems logical or 
mathematical truths, and these are necessary truths. Moreover, in most of 
the systems that are now referred to as modal logics, rule (N) will be seen 
to be acceptable. Axiomatic systems for which this is not so will not include 
rule (N).*
By K we shall denote the modal theory whose axioms are the following 
axiom schemas:
(A1) All instances of tautologies
(A2) All wfs of the form ◻(α ⇒ β) ⇒ (◻α ⇒ ◻β)
These are reasonable assumptions, given our interpretation of the necessity 
operator ◻, and they also will be reasonable with the other interpretations 
of ◻ that we shall study.
By a normal theory we shall mean any theory for which all instances of (A1) 
and (A2) are theorems. Unless something is said to the contrary, in what fol-
lows all our theories will be assumed to be normal. Note that any extension† 
of a normal theory is a normal theory.
Exercises
B.1	 a.	 If α is a tautology, then |−K ◻α.
	
b.	 If α ⇒ β is a tautology, then |−K ◻α ⇒ ◻β
	
c.	 If α ⇒ β is a tautology and |−K ◻α, then |−K ◻β.
	
d.	 If α ⇔ β is a tautology, then |−K ◻α ⇔ ◻β. (Note that, if α ⇔ β is a 
tautology, then so are α ⇒ β and β ⇒ α.)
	
e.	 If |−K α ⇒ β, then |−K ◻α ⇒ ◻β. (Use (N) and (A2).)
	
f.	 If |−K α ⇒ β, then |−K ⬦α ⇒ ⬦β. (First get |−K ¬ β ⇒ ¬ α and use (e).)
*	 When needed, the effect of rule (N) can be obtained for special cases by adding suitable 
axioms.
†	 A theory V is defined to be an extension of a theory U if all theorems of U are theorems of V. 
Moreover, an extension V of U is called a proper extension of U if V has a theorem that is not 
a theorem of U.



397
Appendix B: First Steps in Modal Propositional Logic
B.2	 a.	 |−K ◻(α ∧ β) ⇒ ◻α and |−K ◻(α ∧ β) ⇒ ◻β. (Use the tautologies 
α ∧ β ⇒ α and α ∧ β ⇒ β, and B.1(b).)
	
b.	 |−K ◻α ⇒ (◻β ⇒ ◻(α ∧ β)). (Use the tautology α ⇒ (β ⇒ α ∧ β), and 
B.1(b).)
	
c.	 |−K ◻α ∧ ◻β ⇔ ◻(α ∧ β)). (Use (a) and (b).)
	
d.	 If |−K α ⇔ β, then |−K ◻(α ⇔ β).
	
e.	 |−K ◻(α ⇔ β) ⇒ (◻α ⇔ ◻β). (Use (c) and (A2), recalling that γ ⇔ δ is 
defined as (γ ⇒ δ) ∧ (δ ⇒ γ).)
	
f.	 If |−K α ⇔ β then |−K ◻α ⇔ ◻β.
B.3	 |−K ⬦(α ∨ β) ⇔ ⬦α ∨ ⬦β. (Note that ¬ ⬦(α ∨ β) is provably equivalent* in 
K to ◻¬ (α ∨ β), which, by B.1(d), is, in turn, provably equivalent in K 
to ◻ (¬ α ∧ ¬ β) and the latter, by B.2(c), is provably equivalent in K to 
◻ ¬ α ∧ ◻ ¬ β. This wf is provably equivalent in K to ¬ (¬ ◻ ¬ α ∨ ¬ ◻ ¬ β), 
which is ¬ (⬦α ∨ ⬦β). Putting together these equivalences, we see that ¬ 
⬦(α ∨ β) is provably equivalent in K to ¬ (⬦α ∨ ⬦β) and, therefore, that 
⬦(α ∨ β) is provably equivalent in K to ⬦α ∨ ⬦β.)
B.4	 a. |−K ◻α ⇔ ¬ ⬦ ¬ α (note that ◻α is, by B.1(d), provably equivalent in 
K to ◻¬ ¬ α, and the latter is provably equivalent in K to ¬ ¬◻ ¬¬ α, 
which is ¬ ⬦ ¬ α)
	
b.	 |−K ¬ ◻α ⇔ ⬦ ¬ α
	
c.	 |−K ¬ ⬦ α ⇔ ◻ ¬ α
	
d.	 |−K ◻(α ⇔ β) ⇒ ◻ (¬ α ⇔ ¬ β)
	
e.	 |−K ◻(α ⇔ β) ⇒ (◻ ¬ α ⇔ ◻ ¬ β)
	
f.	 |−K ◻(α ⇔ β) ⇒ (⬦α ⇔ ⬦β)
	
g.	 |−K ¬ ◻◻ α ⇔ ⬦⬦ ¬ α
B.5	 a.	 |−K ◻α ∨ ◻β ⇒ ◻(α ∨ β).
	
b.	 |−K ⬦(α ∧ β) ⇒ ⬦α ∧ ⬦β.
	
c.	 |−K ◻α ⇒ (⬦β ⇒ ⬦(α ∧ β)).
Define α υ β as ◻(α ⇒ β). This relation is called strict implication.
B.6	 a.	 |−K α υ β ⇔ ¬ ⬦(α ∧ ¬ β)
	
b.	 |−K α υ β ∧ β υ γ ⇒ α υ γ
	
c.	 |−K ◻ α ⇒ (β υ α) (this says that a necessary wf is strictly implied by 
every wf)
	
d.	 |−K ◻¬ α ⇒ (α υ β) (this says that an impossible wf strictly implies 
every wf)
	
e.	 |−K ◻α ⇔ ((¬ α) υ α)
*	 To say that γ is provably equivalent in K to δ amounts to saying that |−K γ ⇔ δ.



398
Appendix B: First Steps in Modal Propositional Logic
Theorem B.1 Substitution of Equivalents
Let Γα be a modal wf containing the wf α and let Γβ be obtained from Γα by 
replacing one occurrence of α by β. If |−K α ⇔ β, then |−K Γα ⇔ Γβ.
Proof
Induction on the number n of connectives (including ◻) in Γα. If n = 0, then Γα 
is a statement letter A and α is A itself. So Γβ is β, the hypothesis is |−K A ⇔ β, 
and the required conclusion |−K Γα ⇔ Γβ is the same as the hypothesis. For 
the inductive step, assume that the theorem holds for all wfs having fewer 
than n connectives.
Case 1. Γα has the form ¬ Δα. Then Γβ has the form ¬ Δβ, where Δβ is obtained 
from Δα by replacing one occurrence of α by β. By the inductive hypothesis, 
|−K Δα ⇔ Δβ. Hence, |−K ¬ Δα ⇔ ¬ Δβ, which is the desired conclusion.
Case 2. Γα has the form Δα ⇒ Λα. By the inductive hypothesis, |−K Δα ⇔ Δβ 
and |−K Λα ⇔ Λβ, where Δβ and Λβ are obtained from Δα and Λα by replacing 
zero or one occurrence of α by β. But from |−K Δα ⇔ Δβ and |−K Λα ⇔ Λβ, one 
can derive |−K (Δα ⇒ Λα) ⇔ (Δβ ⇒ Λβ), which is the required conclusion |−K 
Γα ⇔ Γβ.
Case 3. Γα has the form ◻Δα. By the inductive hypothesis, |−K Δα ⇔ Δβ, where 
Δβ is obtained from Δα by replacing one occurrence of α by β. By B.2(f), |−K 
◻Δα ⇔ ◻Δβ, that is, |−K Γα ⇔ Γβ.
Note that, by iteration, this theorem can be extended to cases where more 
than one occurrence of α is replaced by β.
Theorem B.2 General Substitution of Equivalents
The result of Theorem B.1 holds in any extension of K (i.e., in any modal the-
ory containing (A1) and (A2)). The same proof works as that for Theorem B.1.
Exercise
B.7	 a.	 |−K ⬦◻⬦ (A ∨ B) ⇔ ⬦◻⬦ (¬ A ⇒ B)
	
b.	 |−K (◻α ⇒ ¬ ⬦β) ⇔ ¬ ¬ (◻α ⇒ ◻ ¬ β)
Notice that, if ◻α is interpreted as “α is necessary,” acceptance of the neces-
sitation rule limits us to theories in which all axioms are necessary. For, if α 
were an axiom that is not a necessary proposition, then ◻α would be a theo-
rem, contrary to the intended interpretation. Moreover, since it is obvious that 
(MP) and (N) lead from necessary propositions to necessary propositions, all 



399
Appendix B: First Steps in Modal Propositional Logic
theorems would be necessary. So, if we want an applied modal logic with 
some theorems that are not necessary, as we would, say, in physics, then we 
would be impelled to give up rule (N). To still have the theorem on substitu-
tion of equivalences, we would have to add as axioms certain necessary wfs 
that would enable us to obtain the result of Exercise B.2(f), namely, if |−K 
α ⇔ β, then |−K ◻α ⇔ ◻β. However, to avoid the resulting complexity, we 
shall keep (N) as a rule of inference in our treatment of modal logic.
Let us extend the normal theory K to a stronger theory T by adding to K 
the axiom schema:
(A3) All wfs of the form ◻α ⇒ α.
This schema is sometimes called the necessity schema. It asserts that every 
necessary proposition is true. We shall show later that T is stronger than K, 
that is, that there are wfs ◻α ⇒ α that are not theorems of K. Note that, in 
T, strict implication α υ β implies the ordinary conditional α ⇒ β (which is 
sometimes called a material implication).
Exercise
B.8	 a.	 |−T α ⇒ ⬦α (use the instance ◻ ¬ α ⇒ ¬ α of (A3) and an instance of 
the tautology (γ ⇒ ¬ δ) ⇒ (δ ⇒ ¬ γ))
	
b.	 |−T ◻◻α ⇒ ◻α (replace α by ◻α in (A3))
	
c.	 |−T ◻ … ◻α ⇒ ◻α (for any positive number of ◻′s in the antecedent)
	
d.	 |−T α ⇒ ⬦ … ⬦ α
Now we turn to an extension of the system T obtained by adding the axiom 
schema:
(A4) All wfs of the form ◻α ⇒ ◻◻α
This enlarged system is traditionally designated as S4. This notation is 
taken from the work Symbolic Logic (New York, 1932) by C.I. Lewis and C.H. 
Langford, one of the earliest treatments of modal logic from the standpoint 
of modern formal logic.
The justification of (A4) is not as straightforward as that for the previous 
axioms. If ◻α is true, then the necessity of α is due to the form of α, that is, 
to the logical structure of the proposition asserted by α. Since that structure 
is not an empirical fact, that is, it does not depend on the way our world is 
constituted, the truth of ◻α is necessary. Hence, ◻◻α follows.
Exercises
B.9	 a.	 |−S4 ◻◻α ⇒ ◻◻◻α (and so on, for any number of ◻′s)
	
b.	 |−S4 ◻α ⇒ ◻ … ◻α (and so on, for any number of ◻′s)
	
c.	 |−S4 ◻α ⇔ ◻◻α (use (A3) and B.8(b))
	
d.	 |−S4 ◻α ⇔ ◻ … ◻α (use (b) and B.8(c))



400
Appendix B: First Steps in Modal Propositional Logic
B.10	 a.	 |−S4 ◻α ⇔ ¬ ¬ ◻α
	
b.	 |−S4 ◻◻α ⇔ ◻¬ ¬ ◻α (use B.2(e))
	
c.	 |−S4 ◻α ⇔ ◻¬ ¬ ◻α (use (b) and B.9(c))
	
d.	 |−S4 ◻¬ α ⇔ ◻¬ ¬ ◻¬ α (replace α by ¬ α in (c))
	
e.	 |−S4 ¬ ◻¬ α ⇔ ¬ ◻¬ ¬ ◻¬ α
	
f.	 |−S4 ⬦α ⇔ ⬦⬦α (abbreviation of (e))
	
g.	 |−S4 ⬦α ⇔ ⬦ … ⬦α
By B.9(d) and substitution of equivalents, any sequence of consecutive ◻′s 
within a modal wf γ can be replaced by a single occurrence of ◻ to yield a wf 
that is provably equivalent to γ in S4 or any extension of S4. By B.10(g), the 
same holds for ⬦ instead of ◻.
Exercise
B.11 (A Sharper Substitution of Equivalents) Let Γα be a modal wf containing 
the wf α and let Γβ be obtained from Γα by replacing one occurrence 
of α by β. Then |−S4 ◻(α ⇔ β) ⇒ (Γα ⇔ Γβ). (Hint: The proof, like that of 
Theorem B.1, is by induction, except that the induction wf, instead of 
being
	
	   “If |−K α ⇔ β, then |−K Γα ⇔ Γβ,” is now “|−S4 ◻(α ⇔ β) ⇒ (Γα ⇔ Γβ).”
	
	   When n = 0, we now need (A3). For Case 3 of the induction step, we 
must use B.1(e), (A4), and B.2(e).) Note that we can extend B.11 to the case 
where two or more occurrences of α are replaced by β.
Exercises
B.12	 a.	 |−S4 ⬦◻⬦α ⇒ ⬦α (use (A3) to get |−S4 ◻⬦α ⇒ ⬦α and then B.1(f) to 
get |−S4 ⬦◻⬦α ⇒ ⬦⬦α and then B.10(f))
	
b.	 |−S4 ◻⬦α ⇒ ◻⬦◻⬦α (use B.8(a) to get |−S4 ◻⬦α ⇒ ⬦◻⬦α and then 
B.1(e) to get |−S4 ◻◻⬦α ⇒ ◻⬦◻⬦α; finally, apply B.9(c))
	
c.	 |−S4 ◻⬦α ⇔ ◻⬦◻⬦α (apply B.1(e) to B.12(a), and use B.12(b))
	
d.	 |−S4 ⬦◻α ⇔ ⬦◻⬦◻α (use (c) and negations)
B.13	 Consecutive occurrences of ◻′s and/or ⬦′s can be reduced in S4 to 
either ◻ or ⬦ or ◻⬦ or ⬦◻ or ◻⬦◻ or ⬦◻⬦.
We have seen (in B.9(d) and B.10(g)) that the axiom (A4) entails that con-
secutive occurrences of the same modal operator are reducible in S4 to 
a single occurrence of that operator. Now we shall introduce a similar 
simplification when there are consecutive occurrences of different modal 
operators.



401
Appendix B: First Steps in Modal Propositional Logic
Let S5 be the theory obtained by adding to T the following schema:
(A5)	


α
α
⇒
This amounts to saying that a proposition that is possible is necessarily possible.
Now we aim to show that (A4) is provable in S5.
Exercises
B.14	 a.	 |−S5 ⬦ ¬ α ⇒ ◻⬦ ¬ α (use (A5) with α replaced by ¬ α)
	
b.	 |−S5 ¬ ◻⬦ ¬ α ⇒ ¬ ⬦ ¬ α (use contrapositive of (a))
	
c.	 |−S5 ⬦ ¬ ⬦ ¬ α ⇔ ¬ ◻⬦ ¬ α (use B.4(b))
	
d.	 |−S5 ⬦ ¬ ⬦ ¬ α ⇒ ¬ ⬦ ¬ α (use (b) and (c))
	
e.	 |−S5 ⬦◻α ⇒ ◻α (use (d), B.4(a), and Theorem B.2)
	
f.	 |−S5 ◻α ⇒ ⬦◻α (use B.8(a), with α replaced by ◻α)
	
g.	 |−S5 ⬦◻α ⇔ ◻α (use (e) and (f))
B.15	 a.	 |−S5 ⬦α ⇔ ◻⬦α (use (A5), and (A3) with α replaced by ⬦α)
	
b.	 |−S5 ⬦◻α ⇔ ◻⬦◻α (replace α by ◻α in (a))
	
c.	 |−S5 ◻α ⇒ ⬦◻α (use B.8(a))
	
d.	 |−S5 ◻α ⇒ ◻⬦◻α (use (b) and (c))
	
e.	 |−S5 ◻α ⇒ ◻◻α (apply Theorem B.1 to (d) and B.12(g))
Note that B.15(e) is (A4). Since (A4) is a theorem of S5, it follows that S5 is an 
extension of S4. We shall prove later that (A5) is not provable in S4, so that S5 
is a proper extension of S4.
Exercise
B.16 If ⬦◻α ⇒ ◻α (which, by B.13(e), is a theorem of S5) is added as an axiom 
schema to T, show that schema (A5) becomes derivable. (Hence, ⬦◻α ⇒ 
◻α could be used as an axiom schema for S5 instead of (A5).)
Notice that the two theorem schemas ◻⬦α ⇔ ⬦α and ⬦◻α ⇔ ◻α of S5 
enable us (by substitution of equivalents) to reduce any sequence of modal 
operators in a wf to the last modal operator of the sequence.
Exercise
B.17 Find a modal wf that is provably equivalent in S5 to the wf
	
 





A
B
C
∨
¬
⇒
(
and contains no sequence of consecutive modal operators.
Note that the justification of (A5) is similar to the justification of (A4). If ⬦α 
is true, then the fact that α is possible is due to the form of α, that is, to the 



402
Appendix B: First Steps in Modal Propositional Logic
logical structure of the proposition asserted by α. Since that structure is not 
an empirical fact, that is, it does not depend on the way our world is consti-
tuted, the truth of ⬦α is necessary. Hence, ◻⬦α follows.
Semantics for Modal Logic
Recall that the basic wfs in propositional modal logic consist of the denumer-
able sequence A1, A2, A3, … of propositional letters. By a world we shall mean 
a function that assigns to each of the letters A1, A2, A3, … the value t (true) 
or the value f (false). By a Kripke frame* we shall mean a nonempty set W of 
worlds together with a binary relation R on W. If wRw* for worlds w and 
w*, then we shall say that w is R-related to w*. (Note that we are making no 
assumptions about the relation R. It may or may not be reflexive and it may 
or may not have any other special property of binary relations.)
Assume now that the pair (W, R) is a Kripke frame. (W, R) determines a 
truth value t or f for each modal wf α in each world w of W according to the 
following inductive definition, where the induction takes place with respect 
to the number of connectives (including ◻) in the wf α. If there are no con-
nectives in α, then α is a letter Aj and the truth value of α in w is taken to be 
the value assigned to Aj by the world w. For the inductive step, assume that 
the wf α has a positive number n of connectives and that the truth value 
of any wf β having fewer than n connectives is already determined in all 
worlds of W. If α is a negation ¬ β or a conditional β ⇒ γ, then the number of 
connectives in β and the number of connectives in γ are smaller than n and, 
therefore, the truth values of β and γ in every world w in W are already deter-
mined. The usual truth tables for ¬ and ⇒ then determine the truth value of 
¬ β and β ⇒ γ in w. Finally, assume that α has the form ◻β. Then the number 
of connectives in β is smaller than n and, therefore, the truth value of β in 
every world w in W is already determined. Now define the truth value of ◻β 
in a world w in W to be t if and only if the truth value of β in every world w* 
to which w is R-related is t. In other words, ◻β is true in w if and only if, for 
every world w* in W such that wRw*, β is true in w*.
A wf α is said to be valid in a Kripke frame (W, R) if it is true in every world 
w in W. α is said to be universally valid if it is valid in every Kripke frame.
Exercises
B.18	 For any world w in a Kripke frame (W, R), ⬦β is true in w if and only if 
there is a world w* in W such that wRw* and β is true in w*.
(Hint: Since ⬦β is ¬ ◻ ¬ β, ⬦β is true in w if and only if ◻ ¬ β is not true 
in w. Moreover, ◻ ¬ β is not true in w if and only if there exists w* in 
W such that wRw* and ¬ ¬ β is true in w*. But ¬ ¬ β is true in w* if and 
only if β is true in w*.)
*	 In honor of Saul Kripke, who is responsible for a substantial part of the development of mod-
ern modal logic



403
Appendix B: First Steps in Modal Propositional Logic
B.19	 If α and α ⇒ β are true in a world w in a Kripke frame, then so is β.
B.20	 Every modal wf that is an instance of a tautology is universally valid.
B.21	 α and α ⇒ β are universally valid, so is β.
B.22	 If α is universally valid, so is ◻α. (Hint: If ◻α is not universally valid, 
then it is not in some Kripke frame (W, R). Hence, ◻α is not true in some 
world w in W. Therefore, α is not true in some world w* in W such that 
wRw*. Thus, α is not valid in (W, R), contradicting the universal validity 
of α.)
B.23	 ◻(α ⇒ β) ⇒ (◻α ⇒ ◻β) is universally valid. (Hint: Assume the given wf 
is not valid in some Kripke frame (W, R). So it is false in some world w 
in W. Hence, ◻(α ⇒ β) is true in w, and ◻α ⇒ ◻β is false in w. Therefore, 
◻α is true in w and ◻β is false in w. Since ◻β is false in w, β is false in 
some world w* such that wRw*. Since ◻(α ⇒ β) and ◻α are true in w, 
and wRw*, it follows that α ⇒ β and α are true in w*. Hence, β is true in 
w*, contradicting the fact that β is false in w*.)
B.24	 a.	 The set of universally valid wfs form a theory. (Use B.21 and B.22.)
	
b.	 The set of valid wfs in a Kripke frame form a theory.
	
c.	 If all the axioms of a theory are valid in a Kripke frame (W, R), then 
all theorems of the theory are valid in (W, R).
B.25	 All theorems of K are universally valid. (Use B.20–B.23.)
Theorem B.3  ◻A1 ⇒ A1 Is Not Universally Valid
Proof
Let w1 be a world that assigns f to every propositional letter, and let w2 be 
a world that assigns t to every propositional letter. Let W = {w1, w2}, and let 
R be a binary relation on W that holds only for the pair (w1, w2). (W, R) is a 
Kripke frame and ◻A1 is true in the world w1 of that Kripke frame, since A1 
is true in every world w* of W such that w1Rw*. (In fact, w2 is the only such 
world in W, and A1 is true in w2.) On the other hand, A1 is false in w1. Thus, 
◻A1 ⇒ A1 is false in w1. So ◻A1 ⇒ A1 is not valid in the Kripke frame (W, R) 
and, therefore, ◻A1 ⇒ A1 is not universally valid.
Corollary B.4  ◻A1 ⇒ A1 Is Not a Theorem of the Theory K
Proof
Theorem B.3 and Exercise B.25.
Corollary B.4 shows that the theory T is a proper extension of K.
Let us call a Kripke frame (W, R) reflexive if R is a reflexive relation 
(i.e., wRw for all w in W.)



404
Appendix B: First Steps in Modal Propositional Logic
Exercise
B.26	 Every wf ◻α ⇒ α is valid in every reflexive Kripke frame (W, R).
(Hint: If ◻α is true in a world w in W, then α is true in every world w* 
such that wRw*. But wRw and, therefore, α is true in w. Thus, ◻α ⇒ α is 
true in every world in W.)
Exercise
B.27	 Every theorem of T is valid in every reflexive Kripke frame (W, R).
(Use Exercise B.24(c) and B.26.)
Let us call a Kripke frame (W, R) transitive if R is a transitive relation.*
Exercise
B.28	 Every wf ◻α ⇒ ◻◻α is valid in every transitive Kripke frame (W, R).
(Hint: Let w be a world in W, and assume ◻α true in w. Let us then show 
that ◻◻α is true in w. Assume wRw*, where w* is a world in W. We must 
show that ◻α is then true in w*. Assume w*Rw#, where w# is in W. By tran-
sitivity of R, wRw#. Since ◻α is true in w, α is true in w#. Hence, ◻α is true 
in w*. So ◻◻α is true in w. Thus, ◻α ⇒ ◻◻α is true in w for every w in W.)
Exercise
B.29	 Every theorem of S4 is valid in every reflexive, transitive Kripke frame.
Theorem B.5  There Is a Reflexive Kripke Frame 
in Which ◻A1 ⇒ ◻◻A1 Is Not Valid
Proof
Let w1 and w2 be worlds in which A1 is true and let w3 be a world in which 
A1 is false. Let W = {w1, w2, w3} and assume that R is a binary relation in W 
for which w1Rw1, w2Rw2, w3Rw3, w1Rw2, and w2Rw3, but R holds for no other 
pairs. (In particular, w1Rw3 is false.) Now, ◻A1 is true in w1, since, for any w* 
in W, if w1Rw*, then A1 is true in w*. On the other hand, ◻◻A1 is false in w1. 
To see this, first note that w1Rw2. Moreover, ◻A1 is false in w2, since w2Rw3 
and A1 is false in w3.
Thus, ◻A1 is true in w1 and ◻◻A1 is false in w1. Hence, ◻A1 ⇒ ◻◻A1 is false 
in w1 and, therefore, not valid in (W, R).
*	 R is said to be transitive if and only if whenever xRy and yRz, then xRz.



405
Appendix B: First Steps in Modal Propositional Logic
Corollary B.6  ◻A1 ⇒ ◻◻A1 Is a Theorem of S4 That Is Not a Theorem of T
Proof
Use Theorem B.5 and Exercise B.27.
Corollary B.7 S4 Is a Proper Extension of T
We want to show now that S5 is a proper extension of S4. Let us say that a 
Kripke frame (W, R) is symmetric if the relation R is symmetric in W, that is, 
for any w and w* in W, if wRw*, then w*Rw.
Exercise
B.30	 If a Kripke frame (W, R) is symmetric and transitive, then every instance 
⬦α ⇒ ◻⬦α of (A5) is valid in (W, R). (Hint: Let w be a world in W. 
Assume ⬦α is true in w. We wish to show that ◻⬦α is true in w. Since 
⬦α is ¬◻¬ α, ◻ ¬ α is false in w. Hence, there is a world w* in W such 
that wRw* and ¬ α is false in w*. So α is true in w*. In order to prove 
that ◻⬦α is true in w, assume that w# is in W and wRw#. We must prove 
that ⬦α is true in w#. Since (W, R) is symmetric and wRw#, it follows 
that w#Rw. Since wRw* and (W, R) is transitive, w#Rw*. But α is true in 
w*. So, by B.16, ⬦α is true in w#.)
Exercise
B.31	 All theorems of S5 are valid in every reflexive, symmetric, transitive 
Kripke frame.
Exercise
B.32	 ⬦A1 ⇒ ◻⬦A1 is not a theorem of S4. (Hint: Let W = {w1, w2}, where w1 
and w2 are worlds such that A1 is true in w1 and false in w2. Let R be the 
binary relation on W such that w1Rw1, w2Rw2, and w1Rw2, but w2Rw1 
is false. R is reflexive and transitive. ⬦A1 is true in w1 and false in w2. 
◻⬦A1 is false in w1 because w1Rw2 and ⬦A1 is false in w2. Hence, ⬦A1 ⇒ 
◻⬦A1 is false in w1 and, therefore, not valid in the reflexive, transitive 
Kripke frame (W, R). Now use B.29.)
Exercise
B.33	 S5 is a proper extension of S4.



406
Appendix B: First Steps in Modal Propositional Logic
Exercise
B.34	 S5 and all its subtheories (including K, T, and S4) are consistent. (Hint: 
Transform every wf α into the wf α* obtained by deleting all ◻’s. Each 
axiom of S5 is transformed into a tautology. Every application of MP 
taking wfs β and β ⇒ γ into γ is transformed into an application of MP 
taking β* and β* ⇒ γ* into γ*, and every application of N taking β into 
◻β simply takes β* into β*. Hence, the transform of every theorem is a 
tautology. So it is impossible to prove a wf δ and ¬ δ because in such a 
case both δ* and ¬ δ* would be tautologies.)
Exercise
B.35	 The theory obtained by adding to the theory T the schema
	
(Б)
α
α
⇒
	
will be denoted B and called Becker’s theory.*
	
a.	 All instances of Б are provable in S5, and therefore, S5 is an exten-
sion of B. (Hint: Use B.8(a) and (A5).)
	
b.	 A1 ⇒ ◻⬦A1 is not provable in S4 and, therefore, not provable in T. 
(Hint: Use the Kripke frame in the Hint for B.32.)
	
c.	 B is a proper extension of T.
	
d.	 All theorems of B are valid in every reflexive, symmetric Kripke 
frame (W, R). (Hint: Since (W, R) is reflexive, all theorems of T are 
valid in (W, R). We must show that every wf α ⇒ ◻⬦α is valid in 
(W, R). Assume, for the sake of contradiction, that there is a world 
w in W such that α is true and ◻⬦α is false in w. Since ◻⬦α is false 
in w, there exists a world w* in W such that wRw* and ⬦α is false in 
w*. Since R is symmetric, w*Rw and, since α is true in w, ⬦α is true 
in w*, which yields a contradiction.)
	
e.	 ◻A1 ⇒ ◻◻A1 is not a theorem of B. (Hint: Let W = {w1, w2, w3}, where 
w1, w2, w3 are worlds such that A1 is true in w1 and w2 and false 
in w3. Let R be a reflexive, binary relation on W such that w1Rw2, 
w2Rw1, w2Rw3, w3Rw2 hold, but w1Rw3 and w3Rw1 do not hold. Then 
◻A1 is true in w1 and, since ◻A1 is false in w2, ◻◻A1 is false in w1. 
Hence, ◻A1 ⇒ ◻◻A1 is false in w1 and, therefore, is not valid in the 
reflexive, symmetric Kripke frame (W, R). So, by (d), ◻A1 ⇒ ◻◻A1 is 
not a theorem of B.)
	
f.	 S4 is not an extension of B.
	
g.	 S5 is a proper extension of B. (Hint: Use (a) and (f).)
*	 B is usually called the Brouwerian system and Б is called the Brouwerian axiom because of 
a connection with L.E.J. Brouwer’s intuitionism. However, the system was proposed by O. 
Becker in Becker [1930].



407
Appendix C: A Consistency Proof 
for Formal Number Theory
The first consistency proof for first-order number theory S was given by 
Gentzen (1936, 1938). Since then, other proofs along similar lines have been 
given by Ackermann (1940), Schütte (1951). As can be expected from Gödel’s 
second theorem, all these proofs use methods that apparently are not avail-
able in S. Our exposition will follow Schütte’s proof (1951).
The consistency proof will apply to a system S∞ that is much stronger 
than S. S∞ is to have the same individual constant 0 and the same function 
letters +, ·, ′ as S, and the same predicate letter =. Thus, S and S∞ have the 
same terms and, hence, the same atomic formulas (i.e., formulas s = t, where s 
and t are terms). However, the primitive propositional connectives of S∞ will 
be ∨ and ~, whereas S had ⊃ and ~ as its basic connectives. We define a wf of 
S∞ to be an expression built up from the atomic formulas by a finite number 
of applications of the connectives ∨ and ~ and of the quantifiers (xi) (i = 1, 
2, …). We let A ⊃ B stand for (~A  ) ∨ B; then any wf of S is an abbreviation of 
a wf of S∞.
A closed atomic wf s = t (i.e., an atomic wf containing no variables) is called 
correct, if, when we evaluate s and t according to the usual recursion equa-
tions for + and ·, the same value is obtained for s and t; if different values are 
obtained, s = t is said to be incorrect. Clearly, one can effectively determine 
whether a given closed atomic wf is correct or incorrect.
As axioms of S∞ we take: (1) all correct closed atomic wfs and (2) negations 
of all incorrect closed atomic wfs. Thus, for example, (0″) · (0″) + 0″ = (0′″) · (0″) 
and 0′ + 0″ ≠ 0′· 0″ are axioms of S∞.
S∞ has the following rules of inference:
	
I.	Weak rules
	
a.	Exchange: C
A
B
D
C
B
A
D
∨
∨
∨
∨
∨
∨
	
b.	Consolidation: A
A
D
A
D
∨
∨
∨
	
II.	Strong rules
	
a.	Dilution: 
D
A
D
∨
 (where A  is any closed wf)
	
b.	De Morgan: ∼
∼
∼
A
D
B
D
A
B
D
∨
∨
∨
∨
(
)



408
Appendix C: A Consistency Proof for Formal Number Theory
	
c.	Negation: A
D
A
D
∨
∨
∼∼
	
d.	Quantification: 
~
( )
(~ ( )
( ))
A
D
A
D
t
x
x
∨
∨
 
(where t is a closed term)
	
e.	Infinite induction: 
A
D
A
D
( )
(( )
( ))
n
x
x
n
∨
∨
for all natural number
	 III.	Cut: C
A
A
D
C
D
∨
∨
∨
∼
In all these rules, the wfs above the line are called premisses, and the wfs 
below the line, conclusions. The wfs denoted by C and D are called the side wfs 
of the rule; in every rule either or both side wfs may be absent—except that 
D must occur in a dilution (II(a)), and at least one of C  and D in a cut (III). For 
­
example,  A
A
D
D
∼
∨
 
is a cut, and ∼
∼
∼
A
B
A
B
(
)
∨
 is an instance of De Morgan’s 
rule, II(b). In any rule, the wfs that are not side wfs are called the principal 
wfs; these are the wfs denoted by A  and B in the earlier presentation of the 
rules. The principal wf A  of a cut is called the cut wf; the number of proposi-
tional connectives and quantifiers in ~A  is called the degree of the cut.
We still must define the notion of a proof in S∞. Because of the rule of 
infinite induction, this is much more complicated than the notion of proof in 
S. A G-tree is defined to be a graph the points of which can be decomposed 
into disjoint “levels” as follows: At level 0, there is a single point, called the 
terminal point; each point at level i + 1 is connected by an edge to exactly one 
point at level i; each point P at level i is connected by edges to either zero, one, 
two, or denumerably many points at level i + 1 (these latter points at level 
i + 1 are called the predecessors of P); each point at level i is connected only to 
points at level i − 1 or i + 1; a point at level i not connected to any points at 
level i + 1 is called an initial point.
Examples of G-trees.
A
B
D
C
E
Level   4
Level   2
Level   3
Level   1
Level   0



409
Appendix C: A Consistency Proof for Formal Number Theory
A
B
C1 C2
C3
E
A
E
	
1.	A, B, C, D, are initial points. E is the terminal point.
	
2.	A, B, C1, C2, C3, … are the initial points. E is the terminal point.
	
3.	A is the only initial point.
E is the terminal point.
By a proof-tree, we mean an assignment of wfs of S∞ to the points of a G-tree 
such that
	
1.	The wfs assigned to the initial points are axioms of S∞;
	
2.	The wfs assigned to a non-initial point P and to the predecessors 
of P are, respectively, the conclusion and premisses of some rule of 
inference;
	
3.	There is a maximal degree of the cuts appearing in the proof-tree. 
This maximal degree is called the degree of the proof-tree. If there are 
no cuts, the degree is 0;
	
4.	There is an assignment of an ordinal number to each wf occurring in the 
proof-tree such that (a) the ordinal of the conclusion of a weak rule is the 
same as the ordinal of the premiss and (b) the ordinal of the conclusion 
of a strong rule or a cut is greater than the ordinals, of the premisses.



410
Appendix C: A Consistency Proof for Formal Number Theory
The wf assigned to the terminal point of a proof-tree is called the terminal 
wf; the ordinal of the terminal wf is called the ordinal of the proof-tree. 
The proof-tree is said to be a proof of the terminal wf, and the theorems of 
S∞ are defined to be the wfs that are terminal wfs of proof-trees. Notice 
that, since all axioms of S∞ are closed wfs and the rules of inference 
take closed premisses into closed consequences, all theorems of S∞ are 
closed wfs.
A thread in a proof-tree is a finite or denumerable sequence A 1,A 2, … of 
wfs starting with the terminal wf and such that each wf A i + 1 is a predeces-
sor of A i. Hence, the ordinals α1, α2, … assigned to the wfs in a thread do 
not increase, and they decrease at each application of a strong rule or a cut. 
Since there cannot exist a denumerably decreasing sequence of ordinals, it 
follows that only a finite number of applications of strong rules or cuts can 
be involved in a thread. Also, to a given wf, only a finite number of applica-
tions of weak rules are necessary. Hence, we can assume that there are only 
a finite number of consecutive applications of weak rules in any thread of 
a proof-tree. (Let us make this part of the definition of “proof-tree.”) Then 
every thread of a proof-tree is finite.
If we restrict the class of ordinals that may be assigned to the wfs of a 
proof-tree, then this restricts the notion of a proof-tree, and, therefore, we 
obtain a (possibly) smaller set of theorems. If one uses various “construc-
tive” segments of denumerable ordinals, then the systems so obtained and 
the methods used in the consistency proof later may be considered more or 
less “constructive”.
Exercise
Prove that the associative rules (
)
(
)
C
A
B
C
A
B
∨
∨
∨
∨
 
and
 
C
A
B
C
A
B
∨
∨
∨
∨
(
)
(
)
 are derivable 
from the exchange rule, assuming association to the left. Hence, parentheses 
may be omitted from a disjunction.
Lemma A.l
Let A  be a closed wf having n connectives and quantifiers. Then there is a proof of 
~A  ∨ A  of ordinal ≤ 2n + 1 (in which no cut is used).
Proof
Induction on n.
	
1.	n = 0. Then A  is a closed atomic wf. Hence, either A or ~A is 
an axiom, because A is either correct or incorrect. Hence, by 



411
Appendix C: A Consistency Proof for Formal Number Theory
one application of the dilution rule, one of the following is a 
proof-tree.
	
dilution
or
dilution
exchange
A
A
A
A
A
A
A
A
∼
∼
∼
∼
∨
∨
∨
	
	 Hence, we can assign ordinals so that the proof of ~A    ∨ A   has ­ordinal 1.
	
2.	Assume true for all k < n.
Case (i): A  is A 1 ∨ A 2. By inductive hypothesis, there are proofs of ~A 1 ∨ A 
and  ~A 2 ∨ A 2 of ordinals ≤2(n − 1) + 1 = 2n − 1. By dilution, we obtain 
proofs of ~A 1 ∨ A 1 ∨ A 2 and ~A 2 ∨ A 1 ∨ A 2, respectively, of order 2n and, by 
De Morgan’s rule, a proof of ~(A 1 ∨ A 2) ∨ A 1 ∨ A 2 of ordinal 2n + 1.
Case (ii): A  is ~B. Then, by inductive hypothesis, there is a proof of ~B   ∨ B of 
ordinal 2n − 1. By the exchange rule, we obtain a proof of B ∨ ~B of ordinal 
2n − 1, and then, applying the negation rule, we have a proof of ~~B  ∨ ~B, 
that is of ~A   ∨ A, of ordinal 2n ≤ 2n + 1.
Case (iii): A  is (x)B (x). By inductive hypothesis, for every natural number k, 
there is a proof of ~B ∨ B of ordinal ≤2n − 1. Then, by the quantification rule, 
for each k there is a proof of (~ ( )
( ))
( )
x
x
k
B
B
∨
 of ordinal ≤2n and; hence, by 
the exchange rule, a proof of B
B
( )
( )
( )
k
x
x
∨∼
 of ordinal ≤2n. Finally, by an 
application of the infinite induction rule, we obtain a proof of ((x)B(x)) ∨ ~(x)
B (x) of ordinal ≤2n + 1 and, by the exchange rule, a proof of (~(x)B(x)) ∨ 
(x)B (x) of ordinal ≤2n + 1.
Lemma A.2
For any closed terms t and s, and any wf A  (x) with x as its only free variable, the 
wf  s ≠ t ∨ ~A  (s) ∨ A  (t) is a theorem of S∞ and is provable without applying the 
gut rule.
Proof
In general, if a closed wf B(t) is provable in S∞, and s has the same value as t, 
then B(s) is also provable in S∞. (Simply replace all occurrences of t that are 
“deductively connected” with the t in the terminal wf B(t) by s.) Now, if s has 
the same value n as t, then, since ~
( )
( )
A
A
n
n
∨
 is provable, it follows by the 
previous remark that ~A(s) ∨ A(t) is provable. Hence, by dilution, s ≠ t ∨ ~A  (s) ∨ 
A  (t) is provable. If s and t have different values, s = t is incorrect; hence, s ≠ t is 
an axiom. So, by dilution and exchange, s ≠ t ∨ ~A  (s) ∨ A  (t) is a theorem.



412
Appendix C: A Consistency Proof for Formal Number Theory
Lemma A.3
Every closed wf that is a theorem of S is also a theorem of S∞.
Proof
Let A be a closed wf that is a theorem of S. Clearly, every proof in S can be 
represented in the form of a finite proof-tree, where the initial wfs are axioms 
of S and the rules of inference are modus ponens and generalization. Let n be 
an ordinal assigned to such a proof-tree for A.
If n = 0, then A  is an axiom of S.
	
1.	A is B ⊃ (C  ⊃ B), that is, ~B ∨ (~C ∨ B). But, ~B ∨ B is provable in 
S∞ (Lemma A.1). Hence, so is ~B ∨ ~C ∨ B  by a dilution and an 
exchange.
	
2.	A  is (B ⊃ (C  ⊃ D) ⊃ ((B  ⊃ C ) ⊃ (B  ⊃ D)), that is, ~(~B ∨ ~C ∨ ~D) ∨ 
~(~B ∨ C) ∨ (~B ∨ D). By Lemma A.l, we have ~(~B ∨ C ) ∨ ~B ∨ C and 
(~B ∨ ~C ∨ D) ∨ ~(~B ∨ ~C ∨ D). Then, by exchange, a cut (with C as 
cut formula), and consolidation, ~(~B ∨ ~C ∨ D) ∨ ~(~B ∨ C ) ∨ ~B ∨ D 
is provable.
	
3.	A is (~B ⊃ ~A) ⊃ ((~B ⊃ A  ) ⊃ B)), that is, ~(~~B ∨ ~A) ∨ ~(~~B ∨ A ) 
∨ B. Now, by Lemma A.l we have ~B ∨ B, and then, by the negation 
rule, ~~~B ∨ B, and, by dilution and exchange,
	
a.	 ~~~B ∨ ~(~~B ∨ A ) ∨ B.
		
Similarly, we obtain ~~~B ∨ B ∨ ~~A and ~A ∨ B ∨ ~ ~A, and by 
De Morgan’s rule, ~(~  ~B ∨ A  ) ∨ B ∨ ~  ~A; then, by exchange,
	
b.	 ~ ~A   ∨ ~(~ ~B ∨ A  ) ∨ B.
	
	
From (a) and (b), by De Morgan’s rule, we have ~(~~B ∨ ~A   ∨ 
~(~~B ∨ A  ) ∨ B.
	
4.	A is (x)B(x) ⊃ B(t), that is, (~(x)B(x)) ∨ B (t). Then, by Lemma A.1, we 
have ~B (t) ∨ B (t); by the quantification rule, (~(x)B (x)) ∨ B(t).
	
5.	A  is (x)(B ⊃ C ) ⊃ (B ⊃ (x)C ), where x; is not free in B, that is, ~(x)(~B ∨ 
C (x) ∨ ~B ∨ (x)C  (x). Now, by Lemma A-1, for every natural number n, 
there is a proof of ~ (~
( ))
~
( )
B
C
B
C
∨
∨
∨
n
n .
Note that the ordinals of these proofs are bounded by 2k + 1, where k is the 
number of propositional connectives and quantifiers in ~B  ∨ C  (x).)
Hence, by the quantification rule, for each n, there is a proof of
	
~ ( )(~
( ))
~
( )
(
)
x
x
n
k
B
C
B
C
∨
∨
∨
≤
+
of ordinal
2
2
Hence, by exchange and infinite induction, there is a proof of
	
~ ( )(~
( ))
~
( ) ( )
(
)
x
B
C x
B
x C x
k
∨
∨
∨
≤
+
of ordinal
2
3



413
Appendix C: A Consistency Proof for Formal Number Theory
(S1) A  is t1 = t2 ⊃ (t1 = t3 ⊃ t2 = t3), that is, tl ≠ t2 ∨ tl ≠ t3 ∨ t2 = t3.
Apply Lemma A-2, with x; = t3 as A  (x), t1 as s, t2 as t.
(S2) A  is t1 = t2 ⊃ (t1)′ = (t2)′, that is, tl ≠ t2 ∨ (t1)′ = (t2)′. If t1 and t2 have the same 
value, then so do (t1)′ and (t2)′. Hence (t1)′ = (t2)′ is correct and therefore an 
axiom. By dilution, we obtain tl ≠ t2 ∨ (t1)′ ≠ (t2)′. If t1 and t2 have different 
values, t1 ≠ t2 is an axiom; hence, by dilution and exchange, t1 ≠ t2 ∨ (t1)′ = (t2)′ 
is provable.
(S3) A  is 0 ≠ t′. 0 and t′ have different values; hence, 0 ≠ t′ is an axiom.
(S4) A  is (t1)′ = (t2)′ ⊃ t1 = t2, that is, (t1)′ ≠ (t2)′ ∨ t1 = t2. (Exercise.)
(S5) A  is t + 0 = t. t + 0 and t have the same values. Hence, + 0 = t is an axiom.
(S6)–(S8) follow similarly from the recursion equations for evaluating close 
terms.
(S9) A  is B (0) ⊃ ((x)(B (x) ⊃ B (x′)) ⊃ (x)B (x)), that is,
	
~
( )
~ ( )(~
( )
( ))
( )
( )
B
B
B
B
0 ∨
∨
′ ∨
x
x
x
x
x
	
1.	Clearly, by Lemma A.l, exchange and dilution,
	
~ ( )
~ ( )(~ ( )
( ))
( )
B
x
B x
B x
B
0
0
∨
∨
′ ∨
is provable.
	
2.	For k ≥ 0, let us prove by induction that the following wf is provable:
	
~
( )
~ (~
( )
( ))
~ (~
( )
( ))
( ).
B
B
B
B
B
B
0
0
∨
∨
∨… ∨
∨
′ ∨
′
l
k
k
k
	
a.	 For k = 0, ⊢S
l
∞~ ~
( )
~
( )
( )
B
B
B
0
0
∨
∨
 by Lemma A.l, dilution, 
and exchange; similarly, ⊢S
l
l
∞~
( )
~
( )
( )
B
B
B
∨
∨
0
. Hence, by 
De Morgan’s rule, ⊢S
l
l
∞~ (~
( )
( ))
~
( )
( )
B
B
B
B
0
0
∨
∨
∨
 (l), and by 
exchange,
	
⊢S
l
l
∞~
( )
~ (~
( )
( ))
( )
B
B
B
B
0
0
∨
∨
∨
	
b.	 Assume for k:
	
⊢S
l
k
k
k
∞~
( )
~ (~
( )
( ))
~ (~
( )
~
( ))
( )
B
B
B
B
B
B
0
0
∨
∨
∨…
∨
∨
′ ∨
′
Hence, by exchange, negation, and dilution,
	
⊢S
k
l
k
k
k
∞~ ~
( )
~
( )
~ (~
( )
(( ))
~ (~
( )
~
( ))
(
)
B
B
B
B
B
B
B
∨
∨
∨
∨…
∨
∨
′ ∨
′′
0
0



414
Appendix C: A Consistency Proof for Formal Number Theory
Also, by Lemma A.l for B (
)′′
k , dilution and exchange,
	
⊢S
B k
B
B
B l
B k
B k
B k
∞~ (
)
~ ( )
~ (~ ( )
(( ))
~ (~ ( )
~ ( ))
(
)
′′ ∨
∨
∨
∨…
∨
∨
′ ∨
′′
0
0
Hence, by De Morgan’s rule,
	
⊢S
k
k
l
k
k
∞~ (~
( )
~
(
)
~
( )
~ (~
( ))
(( ))
~ (~
( )
~
( )
B
B
B
B
B
B
B
′ ∨
′′ ∨
∨
∨
∨…
∨
∨
′
0
0
)
(
)
∨
′′
B k
and, by exchange, the result follows for k + 1.
Now, applying the exchange and quantification rules k times to the result 
of (2), we have, for each k ≥ 0,
	
⊢S
x
x
x
x
x
x
k
∞~
( )
~ ( )
( )
( ))
~ ( )(~
( )
~
( ))
( )
B
B
B
B
B
B
0 ∨
∨
′
∨…
∨
∨
′ ∨
′
and, by consolidation, ⊢S
x
x
x
k
∞~
( )
~ ( )(~
( )
( ))
( )
B
B
B
B
0 ∨
∨
′ ∨
′ . Hence, together 
with (1), we have, for all k ≥ 0,
	
⊢S
x
x
x
k
∞~
( )
~ ( )(~
( )
( ))
( )
B
B
B
B
0 ∨
∨
′ ∨
Then, by infinite induction,
	
⊢S
x
x
x
x
x
∞~
( )
~ ( )(~
( )
( ))
( )
( )
B
B
B
B
0 ∨
∨
′ ∨
Thus, all the closed axioms of S are provable in S∞. We assume now that 
n > 0. Then, (i) A may arise by modus ponens from B and B ⊃ A, where 
B  and B ⊃ A  have smaller ordinals in the proof-tree. We may assume that 
B contains no free variables, since we can replace any such free variables by 
0 in B and its predecessors in the proof-tree.
Hence, by inductive hypothesis, ⊢S∞B  and ⊢S∞B
A
⊃
, that is, ⊢S∞~ B
A
∨
.
Hence, by a cut, we obtain ⊢S∞A . The other possibility (ii) is that A is (x)B(x) and 
comes by generalization from B(x). Now, in the proof-tree, working backward 
from B(x), replaces the appropriate free occurrences of x by n. We then obtain a 
proof of B ( )
n , of the same ordinal. This holds for all n; by inductive hypothesis, 
⊢S
n
∞B ( ) for all n. Hence, by infinite induction, ⊢S
x
x
∞( )
( )
B
, that is, ⊢S∞A .
Corollary A.4
If S∞ is consistent, S is consistent.



415
Appendix C: A Consistency Proof for Formal Number Theory
Proof
If S is inconsistent, then ⊢s0 ≠ 0. Hence, by Lemma A-3, ⊢s∞0
0
≠. But, ⊢s∞0
0
= , 
since 0 = 0 is correct. For any wf  A    of S∞, we would have, by dilution, 
⊢s∞0
0
≠
∨A , and, together with ⊢s∞0
0
= , by a cut, ⊢s∞A . Thus, any wf of S∞ 
is provable; so S∞ is inconsistent.
By Corollary A.4, to prove the consistency of S, it suffices to show the 
­consistency of S∞.
Lemma A.5
The rules of De Morgan, negation, and infinite induction are invertible, that is, from 
a proof of a wf that is a consequence of some premisses by one of these rules one can 
obtain a proof of the premisses (and the ordinal and degree of such a proof are no 
higher than the ordinal and degree of the original proof).
Proof
	
1.	De Morgan. A  is ~(B ∨ E ) ∨ D. Take a proof of A. Take all those 
subformulas ~(B ∨ E) of wfs of the proof-tree obtained by starting 
with ~(B ∨ E) in A and working back up the proof-tree. This pro-
cess continues through all applications of weak rules and through 
all strong rules in which ~(B ∨ E) is part of a side wf. It can end 
only at dilutions 
F
B
E
F
~ (
)
∨
∨
 or applications of De Morgan’s rule: 
~
~
~ (
)
.
B
F
E
F
B
E
F
∨
∨
∨
∨
 The set of all occurrences of ~(B ∨ E ) obtained by
 
this process is called the history of ~(B   ∨ E ). Let us replace all occur-
rences of ~(B   ∨ E ) in its history by ~B. Then we still have a proof-tree 
(after unnecessary formulas are erased), and the terminal wf is ~B   ∨ D. 
Similarly, if we replace ~(B   ∨ E ) by, ~E we obtain a proof of ~E ∨ D.
	
2.	Negation A   is ~ ~B  ∨ D. Define the history of ~ ~B as was done for 
~(B ∨ B ) in (1); replace all occurrences of ~ ~B in its history by B; the 
result is a proof of B  ∨ D.
	
3.	Infinite induction. A   is ((x)B (x)) ∨ D. Define the history of (x)B (x) as 
in (1); replace (x)B(x) in its history by B ( )
n  (and if one of the ­initial 
occurrences in its history appears as the consequence of an infi-
nite induction, erase the tree above all the premisses except the one 
involving n); we then obtain a proof of B
D
( )
n ∨
.
Lemma A.6
(Schütte 1951: Reduktionssatz). Given a proof of A  in S∞, of positive degree m and 
ordinal α, there is a proof of A  in S∞ of lower degree and ordinal 2α.



416
Appendix C: A Consistency Proof for Formal Number Theory
Proof
By transfinite induction on the ordinal α of the given proof of A., α = 0: this 
proof can contain no cuts and, hence, has degree 0. Assume the theorem 
proved for all ordinals < α. Starting from the terminal wf A, find the first 
application of a nonweak rule, that is, of a strong rule or a cut. If it is a strong 
rule, each premiss has ordinal α1 < α. By inductive hypothesis, for these prem-
isses, there are proof-trees of lower degree and ordinal 2
1
α. Substitute these 
proof-trees for the proof-trees above the premisses in the original proof. We 
thus obtain a new proof for A  except that the ordinal of A   should be taken to 
be 2α, which is greater than every 2
1
α.
The remaining case is that of a cut:
	
C
B
B
D
C
D
∨
∨
∨
~
If the ordinals of C  ∨ B and ~B  ∨ D are α1, α2, then, by inductive hypothesis, 
we can replace the proof-trees above them so that the degrees are reduced 
and the ordinals are 2
1
α, 2
2
α , respectively. We shall distinguish various cases 
according to the form of the cut formula B :
	
a.	B is an atomic wf. Either B or ~B  must be an axiom. Let K  be the 
non-axiom of B and ~B. By inductive hypothesis, the proof-tree 
above the premiss containing K   can be replaced by a proof-tree with 
a lower degree having ordinal 2
1
α(i = 1 or 2). In this new proof-tree, 
consider the history of K  (as defined in the proof of Lemma A-5). The 
initial wfs in this history can arise only by dilutions. So, if we erase 
all occurrences of K  in this history, we obtain a proof-tree for C  or for 
D of ordinal 2
1
α; then, by dilution, we obtain C   ∨ D, of ordinal 2α. The 
degree of the new proof-tree is less than m.
	
b.	B is C
E
E
D
C
D
∨
∨
∨
~
~ ~
	
	 There is a proof-tree for ~  ~E  ∨ D of degree < m and ordinal 2
2
α . By 
Lemma A-5, there is a proof-tree for E   ∨ D of degree < m and ordinal 
2
2
α  There is also, by inductive hypothesis, a proof-tree for C  ∨ ~E of 
degree < m and ordinal 2
1
α. Now, construct
	
Exchange
Exchange
Cut
Exchange
E
D
D
E
C
D
B
C
D
C
C
D
∨
∨
∨
∨
∨
∨





417
Appendix C: A Consistency Proof for Formal Number Theory
	
	 The degree of the indicated cut is the degree of ~E that is one less 
than the degree of ~~  ~E, which, in turn, is ≤m. The ordinal of D  ∨ C 
can be taken to be 2
2
α . Hence, we have a proof of lower degree and 
ordinal 2α.
	
c.	B is E
F
C
E
F
E
F
D
C
D
∨
∨
∨
∨
∨
∨
:
~ (
)
	
	 There is a proof-tree for~(E ∨ F  ) ∨ D of lower degree and ordinal 2
2
α . 
Hence, by Lemma A-5, there are proof-trees for ~E ∨ D and ~F    ∨ D of 
degree <m and ordinal 2
2
α . There is also a proof-tree for B  ∨ E  ∨ F  of 
degree <m and ordinal 2
1
α. Construct
	
C
E
F
F
D
C
E
D
C
D
E
E
D
C
D
D
∨
∨
∨
∨
∨
∨
∨
∨
∨
∨



~
~
Cut
Exchange
Cut
Consolidation
C
D
∨
	
	 The cuts indicated have degrees < m; hence, the new proof-tree has 
degree < m; the ordinal of C   ∨ E   ∨ D can be taken as 2
1
2
max(
,
)
α α  + 01 and 
then the ordinal C  ∨ D  ∨ D and C   ∨ D as 2α.
	
d.	B is ( )
:
( )
(~ ( ) )
x
x
x
E
C
E
E
D
C
D
∨
∨
∨
	
	 By inductive hypothesis, the proof-tree above C    ∨ (x)E  can 
be replaced by one with smaller degree and ordinal 2α1. By Lemma 
A.5 and the remark at the beginning of the proof of Lemma A.2, we 
can obtain proofs of C   ∨  E(t) of degree <m and ordinal 2α, for any 
closed term t. Now, the proof-tree above the right-hand formula 
(~(x)E)  ∨ D can be replaced, by inductive hypothesis, by one with 
smaller degree and ordinal 2
2
α . The history of ~(x)E  in this proof ter-
minates above either at dilutions or as principal wfs in applications 
of the Quantification rule:
	
~
( )
E
G
t
i
1 ∨
	
(~ ( )
x
i
E
G
∨



418
Appendix C: A Consistency Proof for Formal Number Theory
Replace every such application by the cut
	
C
E
E
G
∨
∨
( )
(~
( ))
t
t
i
1
1
	
C
G
∨
i
Replace all occurrences in the history of ~(x)E(x) by C. The result is still a 
proof-tree, and the terminal wf is C   ∨ D. The proof-tree has degree < m, 
since the degree of ~E(t1) is less than the degree of ~(x)E. Replace each old 
ordinal β of the proof-tree by 2
1
0
α
β
+
. If β was the ordinal of the premiss 
~(x)E(t1) ∨ Gi of an eliminated quantification rule application earlier, and if 
γ was the ordinal of the conclusion (~(x)E) ∨ Gi, then, in the new cut intro-
duced, C ∨ E(t) has ordinal 2
1
α , ~E(t1) ∨ Gi has ordinal 2
1
α , and the conclu-
sion C ∨ Gi has ordinal 2
2
2
1
1
1
0
0
α
α
α
γ
β
+
>
+
max(
,
). At all other places, the 
ordinal of the conclusion is still greater than the ordinal of the ­premisses, 
since δ <0 μ implies 2
1
α  + 0δ<0 2
1
α  + 0μ. Finally, the right-hand ­premiss 
(~(x)E) ∨ D (originally of ordinal α2) goes over into C ∨ D with ordinal 
2
2
2
2
2
2
2
1
2
1
2
1
2
1
2
1
0
0
0
α
α
α
α
α
α
α
α
α
α
+
≤
+
=
×
=
max(
,
)
max(
,
)
max(
,
)
max(
,
2
0 1
2
)
.
+
≤
α  If this 
is <02α, the ordinal of C ∨ D can be raised to 2α.
Corollary A.7
Every proof of A  of ordinal α and degree m can be replaced by a proof of A  of ordinal 
22
2 2
 (
)
α
 and degree 0 (i.e., a cut-free proof).
Proposition A-8
S∞ is consistent.
Proof
Consider any wf A  of the form (0 ≠ 0) ∨ (0 ≠ 0) ∨ … ∨ (0 ≠ 0). If there is a 
proof of A, then by Corollary A-7, there is a cut-free proof of A. By inspection 
of the rules of inference, A can be derived only from other wfs of the same 
form: (0 ≠ 0) ∨ … ∨ (0 ≠ 0). Hence, the axioms of the proof would have to be 
of this form. But there are no axioms of this form; hence, A   is unprovable. 
Therefore, S∞ is consistent.



419
Answers to Selected Exercises
Chapter 1
1.1	
A
B
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
F
1.2
	
A
B
A
A
B
A
B
A
¬
⇒
⇒
∨¬
(
)
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
F
F
F
F
F
F
T
T
T
1.3
	
((
)
)
A
B
A
⇒
∧
T
T
T
T
T
F
T
T
F
F
T
F
F
F
T
F
T
F
F
F
1.4	
a.	
A
B
A
B
⇒¬
(
) ∧
¬
⇒¬
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
	
c.	
(A ⇒ B),	
A: x is prime, B: x is odd.
	
d.	 (A ⇒ B),	
A: the sequence s converges,
	
B: the sequence s is bounded.
	
e.	
(A ⇔ (B ∧ (C ∧ D)))	
A: the sheikh is happy,
	
B: the sheikh has wine,
	
C: the sheikh has women,
	
D: the sheikh has song.
	
f.	
(A ⇒ B),		
A: Fiorello goes to the movies.
	
i.	
((¬A) ⇒ B),	
A: Kasparov wins today,
	
B: Karpov will win the tournament.
1.5 
(c), (d), (f), (g), (i), (j) are tautologies.



420
Answers to Selected Exercises
1.6	
(a), (b), (d), (e), (f) are logically equivalent pairs.
1.11	
All except (i).
1.13	
Only (c) and (e).
1.15	
a.	
(B ⇒ ¬A) ∧ C 	
(e) A ⇔ B ⇔ ¬(C ∨ D)
	
c.	
Drop all parentheses.	(g) ¬(¬¬(B ∨ C) ⇔ (B ⇔ C))
1.16	
a.	
(C ∨((¬A) ∧ B))	
(c) ((C ⇒((¬((A ∨ B) ⇒ C)) ∧ A)) ⇔ B)
1.17	
a.	
(((¬(¬A)) ⇔ A) ⇔ (B ∨ C)) (d) and (f) are the only ones that are not 
abbreviations of statement forms.
1.18	
a.	
∨ ⇒ C¬AB and ∨C ⇒ ∧B¬DC
	
c.	
(a) ∧ ⇒ B¬AC   (b) ∨A ∨ BC
	
d.	 (i) is not. (ii) (A ⇒ B) ⇒((B ⇒ C) ⇒ (¬A ⇒ C))
1.19	
f.	
is contradictory, and (a), (d), (e), (g)–(j) are tautologies.
1.20	
(b)–(d) are false.
1.21	
a.	
T (b) T (c) indeterminate
1.22	
a.	
A is T, B is F, and ¬A ∨ (A ⇒ B) is F.
	
c.	
A is T, C is T, B is T.
1.29	
c.	
(i) A ∧((B ∧ C) ∨ (¬B ∧ ¬C)) (ii) A ∧ B ∧ ¬C
	
	
(iii) ¬A ∨ (¬B ∧ C)
1.30	
a.	
If B is a tautology, the result of replacing all statement letters by 
their negations is a tautology. If we then move all negation signs 
outward by using Exercise 1.27 (k) and (l), the resulting tautology 
is ¬B ′. Conversely, if ¬B ′ is a tautology, let C  be ¬B ′. By the first 
part, ¬C ′ is a tautology. But ¬C ′ is ¬¬B.
	
c.	
(¬A ∧ ¬B ∧ ¬C) ∨ (A ∧ B ∧ ¬D)
1.32	
a.	
For figure 1.4:
B
A
1.33	
(a), (d) and (h) are not correct.
1.34	
a.	
Satisfiable: Let A, B, and C be F, and let D be T.
1.36	
For f,
	
(
)
(
)
(
)
(
)
A
B
C
A
B
C
A
B
C
A
B
C
∧
∧
∨¬
∧
∧
∨
∧¬ ∧
∨¬
∧¬ ∧¬
1.37	
For ⇒ and ∨, notice that any statement form built up using ⇒ and ∨ 
will always take the value T when the statement letters in it are T. In 
the case of ¬ and ⇔, using only the statement letters A and B, find all 



421
Answers to Selected Exercises
the truth functions of two variables that can be generated by applying 
¬ and ⇔ any number of times.
1.40	
a.	
24 = 16 (b) 22n
1.41	
h(C, C, C) = ¬C and h(B, B, ¬C) is B ⇒ C.
1.42	
b.	
For ¬(A ⇒ B) ∨ (¬A ∧ C), a disjunctive normal form is (A ∧ ¬B) ∨ (¬A 
∧ C), and a conjunctive normal form is (A ∨ C) ∧ (¬B ∨ ¬A) ∧ (¬B ∨ C).
	
c.	
(i) For (A ∧ B) ∨ ¬A, a full dnf is (A ∧ B) ∨ (¬A ∧ B) ∨ (¬A ∧ ¬B), and 
a full cnf is B ∨ ¬A.
1.43	
b.	 (i) Yes. A: T, B: T, C: F (ii) Yes. A: T, B: F, C: T
1.45	
b.	 A conjunction E of the form B
Bn
1
*
*
∧… ∧
, where each Bi
* is either Bi 
or ¬Bi, is said to be eligible if some assignment of truth values to 
the statement letters of B  that makes B  true also makes E  true. 
Let C  be the disjunction of all eligible conjunctions.
1.47 
b.	 1.	
C ⇒ D	
Hypothesis
	
	
2.	
B ⇒ C	
Hypothesis
	
	
3.	
(B ⇒ (C ⇒ D)) ⇒((B ⇒ C ) ⇒ (B ⇒ D))	 Axiom (A2)
	
	
4.	
(C ⇒ D) ⇒(B ⇒ (C ⇒ D))	
Axiom (A1)
	
	
5.	
B ⇒ (C ⇒ D)	
1, 4, MP
	
	
6.	
(B ⇒ C) ⇒ (B ⇒ D)	
3, 5, MP
	
	
7.	
B ⇒ D	
2, 6, MP
1.48	
a.	
1.	
B ⇒ ¬¬B	
Lemma 1.11(b)
	
	
2.	
¬¬B  ⇒ (¬B ⇒ C )	
Lemma 1.11(c)
	
	
3.	
B ⇒ (¬B ⇒ C )	
1, 2, Corollary 1.10(a)
	
	
4.	
B ⇒ (B ∨ C )	
3, Abbreviation
	
c.	
1.	
¬C ⇒ B	
Hypothesis
	
	
2.	
(¬C ⇒ B) ⇒ (¬B ⇒ ¬¬C )	
Lemma 1.11(e)
	
	
3.	
¬B ⇒ ¬¬C	
1, 2, MP
	
	
4.	
¬¬C ⇒ C	
Lemma 1.11(a)
	
	
5.	
¬B ⇒ C	
3, 4, Corollary 1.10(a)
	
	
6.	
¬C ⇒ B ⊢ ¬B ⇒ C	
1–5
	
	
7.	
⊢ (¬C ⇒ B) ⇒ (¬B ⇒ C )	
6, deduction theorem
	
	
8.	
⊢ (C  ∨ B) ⇒ (B ∨ C )	
7, abbreviation
1.50	
Take any assignment of truth values to the statement letters of B that 
makes B false. Replace in B each letter having the value T by A1 ∨ ¬A1, 
and each letter having the value F by A1 ∧ ¬A1. Call the resulting state-
ment form C. Thus, C is an axiom of L*, and, therefore, ⊢L*C. Observe 
that C always has the value F for any truth assignment. Hence, ¬C  is a 
tautology. So ⊢L ¬C  and, therefore, ⊢L* ¬ C.



422
Answers to Selected Exercises
1.51	
(Deborah Moll) Use two truth values. Let ⇒ have its usual table and 
let ¬ be interpreted as the constant function F. When B is F, (¬B ⇒ ¬A) 
⇒((¬B ⇒ A) ⇒ B) is F.
1.52	
The theorems of P are the same as the axioms. Assume that P is suitable for 
some n-valued logic. Then, for all values k, k * k will be a designated value. 
Consider the sequence of formulas B0 = A, Bj+1 = A  * Bj. Since there are nn 
possible truth functions of one variable, among B0, …, Bnn there must be 
two different formulas Bj and Bk that determine the same truth function. 
Hence, Bj  * Bk will be an exceptional formula that is not a theorem.
1.53	
Take as axioms all exceptional formulas, and the identity function as 
the only rule of inference.
Chapter 2
2.1	
a.	
(
)
(
)
(
)
∀
∧¬
(
)
(
)
(
)
x
A x
A x
1
1
1
1
1
1
2
 (b) 
(
)
(
)
(
)
∀
(
) ⇔
(
)
x A x
A x
2
1
1
2
1
1
2
	
d.	
(
) (
) (
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
(
)
(
)
(
) ⇒
∧¬
(
)
(
)
(
)
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
2.2	
a.	
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
∀
⇒
(
)
(
)∨∃
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
2.3	
a.	
The only free occurrence of a variable is that of x2.
	
b.	 The first occurrence of x3 is free, as is the last occurrence of x2.
2.6	
Yes, in parts (a), (c) and (e)
2.8	
a.	
(∀x)(P(x) ⇒ L(x))
	
b.	 (∀x)(P(x) ⇒ ¬H(x)) or ¬(∃x)(P(x) ∧ H(x))
	
c.	
¬(∀x)(B(x) ⇒ F(x))
	
d.	 (∀x)(B(x) ⇒ ¬F(x)) (e) T(x) ⇒ I(x)
	
f.	
(∀x)(∀y)(S(x) ∧ D(x, y) ⇒ J(y))
	
j.	
(∀x)(¬H(x, x) ⇒ H(j, x)) or (∀x)(P(x) ∧ ¬H(x, x) ⇒ H(j, x))
	
	
(In the second wf, we have specified that John hates those persons 
who do not hate themselves, where P(x) means x is a person.)
2.9	
a.	
All bachelors are unhappy. (c) There is no greatest integer.
2.10	
a.	
i.	
Is satisfied by all pairs 〈x1, x2〉 of positive integers such that 
x1 · x2 ≥ 2.
	
	
ii.	
Is satisfied by all pairs 〈x1, x2〉 of positive integers such that 
either x1 < x2 (when the antecedent is false) or x1 = x2 (when the 
antecedent and consequent are both true).
	
	
iii.	 Is true.



423
Answers to Selected Exercises
2.11	
a.	
Between any two real numbers there is a rational number.
2.12	
I.	 A sequence s satisfies ¬B if and only if s does not satisfy B. 
Hence, all sequences satisfy ¬B if and only if no sequence satis-
fies B; that is, ¬B is true if and only if B  is false.
	
II.	 There is at least one sequence s in Σ. If s satisfies B, B cannot 
be false for M. If s does not satisfy B, B cannot be true for M.
	
III.	 If a sequence s satisfies both B and B ⇒ C, then s satisfies C by 
condition 3 of the definition.
	
V.	 a.	 s satisfies B ∧ C if and only if s satisfies ¬(B ⇒ ¬C)
	
	 	
if and only if s does not satisfy B ⇒ ¬C
	
	 	
if and only if s satisfies B but not ¬C
	
	 	
if and only if s satisfies B and s satisfiesC
	
VI.	 a.  Assume ⊧M B. Then every sequence satisfies B. In particular, 
every sequence that differs from a sequence s in at most the 
ith place satisfies B. So, every sequence satisfies (∀xi)B; that is, 
⊧M (∀xi)B.
	
	 b.	 Assume ⊧M (∀xi)B. If s is a sequence, then any sequence that dif-
fers from s in at most the ith place satisfies B, and, in particular, 
s satisfies B. Then every sequence satisfies B; that is, ⊧M B.
	
VIII.	 Lemma. If all the variables in a term t occur in the list x
x
i
ik
1 ,
,
…
 
(k ≥ 0; when k = 0, t has no variables), and if the sequences s 
and s′ have the same components in the i1th, …, ikth places, then 
s* (t) = (s′)*(t).
	
	
Proof. Induction on the number m of function letter in t. Assume 
the result holds for all integers less than m.
	
	
Case 1. t is an individual constant ap. Then s*(ap) = (ap)M = (s′)*(ap).
	
	
Case 2. t is a variable xij. Then s
x
s
s
s
x
i
i
i
i
j
j
j
j
*(
)
( )*(
)
=
= ′ =
′
.
	
	
Case 3. t is of the form f
t
t
j
n
n
( ,
,
)
1 …
. For q ≤ n, each tq has 
fewer than m function letters and all its variables occur 
among x
x
i
ik
1 ,
,
.
…
 By inductive hypothesis s*(tq) = (s′)*(tq).
Then 
s
f
t
t
f
s
t
s
t
f
s
j
n
n
j
n
n
j
n
*
*
*
*
( ,
,
)
( ),
,
( )
(( )
1
1
…
(
) = (
)
…
(
) = (
)
′
M
M
 
( ),
, ( ) ( ))
( )
( ,
,
) .
t
s
t
s
f
t
t
n
j
n
n
1
1
…
′
=
′
…
(
)
*
*
	
	
Proof of (VIII). Induction on the number r of connectives and 
quantifiers in B. Assume the result holds for all q < r.
	
	
Case 1. B is of the form A t
t
j
n
n
( ,
,
)
1 …
; that is, r = 0. All the variables 
of each ti occur among x
x
i
ik
1,
,
…
. Hence, by the lemma, s*(ti) = 
(s′)*(ti). But s satisfies A t
t
j
n
n
( ,
,
)
1 …
 if and only if 〈s*(t1), …, s*(tn)〉 is 
in Aj
n
(
)
M—that is, if and only if 〈(s′)*(t1), …, (s′)*(tn)〉 is in Aj
n
(
)
M , 
which is equivalent to s′ satisfying A t
t
j
n
n
( ,
,
)
1 …
.



424
Answers to Selected Exercises
	
	
Case 2. B is of the form ¬C.
	
	
Case 3. B is of the form C ⇒ D. Both cases 2 and 3 are easy.
	
	
Case 4. B is of the form (∀xj)C. The free variables of C occur among 
x
x
i
ik
1 ,
,
…
 and xj. Assume s satisfies B. Then every sequence that 
differs from s in at most the jth place satisfies C. Let s# be any 
sequence that differs from s′ in at most the jth place. Let sb be 
a sequence that has the same components as s in all but the jth 
place, where it has the same component as s#. Hence, sb satisfies 
C. Since sb and s# agree in the i1th, …, ikth and jth places, it follows 
by inductive hypothesis that sb satisfies C if and only if s# satis-
fies C. Hence, s# satisfies C. Thus, s′ satisfies B. By symmetry, the 
converse also holds.
	
IX.	 Assume B is closed. By (VIII), for any sequence s and s′, s satis-
fies B if and only if s′ satisfies B. If ¬B is not true for M, some 
sequence s′ does not satisfy ¬B; that is, s′ satisfies B. Hence, 
every sequence s satisfies B; that is, ⊧M B.
	
X.	 Proof of Lemma 1: induction on the number m of function letters 
in t.
	
	
Case 1. t is aj. Then t′ is aj. Hence,
	s
t
s
a
a
s
a
s
t
j
j
j
*
*
*
*
( )
(
)
(
)
( ) (
)
( ) ( )
′ =
=
=
′
=
′
M
	
	
Case 2. t is xj, where j ≠ i. Then t′ is xj. By the lemma of (VIII), 
s*(t′) = (s′)*(t), since s and s′ have the same component in the jth 
place.
	
	
Case 3. t is xi. Then t′ is u. Hence, s*(t′) = s*(u), while (s′)*(t) = (s′)*(xi) = 
′si = s*(u).
	
	
Case 4. t is of the form f
t
t
j
n
n
( ,
,
)
1 …
. For 1 ≤ q ≤ n, let ′tq result 
from tq by the substitution of u for xi. By inductive hypothesis, 
s
t
s
t
q
q
*( )
( )*( )
′ =
′
. But
	
s
t
s
f
t
t
f
s
t
s
t
f
j
n
n
j
n
n
j
n
*
*
*
*
( )
,
,
,
,
′ =
′ …
′
(
)
(
) = (
)
′
( ) …
′
( )
(
)
= (
)
1
1
M
M ( ) ( ),
, ( ) ( )
( )
( ,
,
)
( ) ( )
′
…
′
(
) =
′
…
(
) =
′
s
t
s
t
s
f
t
t
s
t
n
j
n
n
*
*
*
*
1
1
	
	
Proof of Lemma 2(a): induction on the number m of connectives and 
quantifiers in B(xi).
	
	
Case 1. m = 0. Then B(xi) is A t
t
j
n
n
( ,
,
)
1 …
. Let ′tq be the result of sub-
stituting t for all occurrences of xi in tq. Thus, B(t) is A
t
j
n
n
1,
,
.
…
′
(
)  
By Lemma 1, s
t
s
t
q
q
*
*
′
( ) =
′
( ) ( ). Now, s satisfies B (t) if and only if 
〈
′
…
′ 〉
s
t
s
tn
*( ),
, *( )
1
 belongs to Aj
n
(
)
M, which is equivalent to 〈(s′)*(t1), …, 
(s′)*(tn)〉 belonging to Aj
n
(
)
M—that is, to s′ satisfying B (xi).



425
Answers to Selected Exercises
	
	
Case 2. B (xi) is ¬C (xi); this is straightforward.
	
	
Case 3. B (xi) is C (xi) ⇒ D (xi); this is straightforward.
	
	
Case 4. B (xi) is (∀xj) B (xi).
	
	
Case 4a. xj is xi. Then xi is not free in B (xi), and B (t) is B (xi). Since 
xi is not free in B (xi), it follows by (VIII) that s satisfies B (t) if and 
only if s′ satisfies B (xi).
	
	
Case 4b. xj is different from xi. Since t is free for xi in B (xi), t is also 
free for xi in C (xi).
	
	
Assume s satisfies (∀xj) C (t). We must show that s′ satisfies (∀xj) 
C (xi). Let s# differ from s′ in at most the jth place. It suffices to show 
that s# satisfies C (xi). Let sb be the same as s# except that it has the 
same ith component as s. Hence, sb is the same as s except in its jth 
component. Since s satisfies (∀xj) C (t), sb satisfies C (t). Now, since t is 
free for xi in (∀xj) C (xi), t does not contain xj. (The other possibility, 
that xi is not free in C (xi), is handled as in case 4a.) Hence, by the 
lemma of (VIII), (sb)*(t) = s*(t). Hence, by the inductive hypothesis 
and the fact that s# is obtained from sb by substituting (sb)*(t) for the 
ith component of sb, it follows that s# satisfies C (xi), if and only if sb 
satisfies C (t). Since sb satisfies C (t), s# satisfies C (xi).
	
	
Conversely, assume s′ satisfies (∀xj) C (xi). Let sb differ from s in 
at most the jth place. Let s# be the same as s′ except in the jth 
place, where it is the same as sb. Then s# satisfies C  (xi). As above, 
s*(t) = (sb)*(t). Hence, by the inductive hypothesis, sb satisfies C  (t) if 
and only if s# satisfies C (xi). Since s# satisfies C (xi), sb satisfies C (t). 
Therefore, s satisfies (∀xj)C (t).
	
	
Proof of Lemma 2(b). Assume s satisfies (∀xi)B (xi). We must show 
that s satisfies B (t). Let s′ arise from s by substituting s*(t) for the 
ith component of s. Since s satisfies (∀xi)B (xi) and s′ differs from s 
in at most the ith place, s′ satisfies B (xi). By Lemma 2(a), s satisfies 
B (t).
2.13	
Assume B is satisfied by a sequence s. Let s′ be any sequence. By (VIII), 
s′ also satisfies B. Hence, B is satisfied by all sequences; that is, ⊧M B.
2.14	
a.	
x is a common divisor of y and z. (d) x1 is a bachelor.
2.15	
a.	
i.	
Every nonnegative integer is even or odd. True.
	
	
ii.	
If the product of two nonnegative integers is zero, at least one 
of them is zero. True.
	
	
iii.	 1 is even. False.
2.17	
(a) Consider an interpretation with the set of integers as its domain. 
Let A x
1
1( ) mean that x is even and let A x
2
1( ) mean that x is odd. Then 
(
)
(
)
∀x A x
1
1
1
1  is false, and so (
)
(
)
(
)
(
)
∀
⇒∀
x A x
x A x
1
1
1
1
1
2
1
1  is true. However, 
(
)
(
)
(
)
∀
⇒
(
)
x
A x
A x
1
1
1
1
2
1
1  is false, since it asserts that all even integers 
are odd.



426
Answers to Selected Exercises
2.18	
a.	
[(∀xi) ¬B (xi) ⇒ ¬B (t)] ⇒ [B (t) ⇒ ¬(∀xi) ¬B (xi)] is logically valid 
because it is an instance of the tautology (A ⇒ ¬B) ⇒ (B ⇒ ¬A). By 
(X), (∀xi)¬B (xi) ⇒ ¬B (t) is logically valid. Hence, by (III), B (t) ⇒ 
¬(∀xi)¬B (xi) is logically valid.
	
b.	 Intuitive proof: If B is true for all xi, then B is true for some xi. 
Rigorous proof: Assume (∀xi)B ⇒ (∃xi)B is not logically valid. Then 
there is an interpretation M for which it is not true. Hence, there is 
a sequence s in ∑ such that s satisfies (∀xi)B and s does not satisfy 
¬(∀xi)¬B. From the latter, s satisfies (∀xi)¬B. Since s satisfies (∀xi)B, 
s satisfies B, and, since s satisfies (∀xi)¬B, s satisfies ¬B. But then s 
satisfies both B and ¬B, which is impossible.
2.19	
b.	 Take the domain to be the set of integers and let A u
1
1( ) mean that 
u is even. A sequence s in which s1 is even satisfies A x
1
1
1
(
) but does 
not satisfy (
)
(
)
∀x A x
1
1
1
1 .
2.21	
a.	
Let the domain be the set of integers and let A x y
1
2( , ) mean that x < 
y. (b) Same interpretation as in (a).
2.22	 a.	
The premisses are (i) (∀x)(S(x) ⇒ N(x)) and (ii) (∀x)(V(x) ⇒ ¬N(x)), 
and the conclusion is (∀x)(V(x) ⇒ ¬S(x)). Intuitive proof: Assume 
V(x). By (ii), ¬N(x). By (i), ¬S(x). Thus, ¬S(x) follows from V(x), and 
the conclusion holds. A more rigorous proof can be given along 
the lines of (I)–(XI), but a better proof will become available after 
the study of predicate calculi.
2.26	
a.	 (
)(
)
( )
( )
∃
∃
∧¬
(
)
x
y
A x
A y
1
1
1
1
2.27	
a.	
1.	 (∀x)(B ⇒ C)	
Hyp
	
	
2.	 (∀x)B	
Hyp
	
	
3.	 (∀x)(B ⇒ C) ⇒ (B ⇒ C)	
Axiom (A4)
	
	
4.	 B  ⇒ C	
1, 3, MP
	
	
5.	 (∀x)B ⇒ B	
Axiom (A4)
	
	
6.	 B	
2, 5, MP
	
	
7.	 C	
4, 6, MP
	
	
8.	 (∀x)C	
7, Gen
	
	
9.	 (∀x)(B ⇒ C), (∀x)B ⊢ (∀x)C	
1–8
	
	
10.	 (∀x)(B  ⇒ C) ⊢ (∀x)B ⇒ (∀x)C	
1–9, Corollary 2.6
	
	
11.	 ⊢ (∀x)(B ⇒ C) ⇒ ((∀x)B ⇒ (∀x)C)	
1–10, Corollary 2.6
2.28	
Hint: Assume ⊢K B. By induction on the number of steps in the proof of 
B in K, prove that, for any variables y1, …, yn (n ≥ 0), ⊢K#(∀ y1) … (∀ yn)B.
2.31 
a.	
1.	
(
)(
)
( , )
∀
∀
x
y A x y
1
2
	
Hyp
	
	
2.	
(
)
( , )
∀y A x y
1
2
	
1, Rule A4



427
Answers to Selected Exercises
	
	
3.	
A x x
1
2( , ) 	
2, Rule A4
	
	
4.	
(
)
( , )
∀x A x x
1
2
	
3, Gen
	
	
5.	
∀
(
) ∀
(
)
(
)
∀
(
)
(
)
x
y A
x y
x A
x x
1
2
1
2
,
,
⊢
	
1–4
	
	
6.	
⊢∀
(
) ∀
(
)
(
) ⇒∀
(
)
(
)
x
y A
x y
x A
x x
1
2
1
2
,
,
	 1–5, Corollary 2.6
2.33	
a.	
⊢ ¬(∀x)¬¬B ⇔ ¬(∀x)¬B by the replacement theorem and the fact 
that ⊢ ¬¬B ⇔ B. Replace ¬(∀x)¬¬B  by its abbreviation (∃x)¬B.
2.36	
b.	 (∃ε)(ε > 0 ∧ (∀δ)(δ > 0 ⇒ (∃x)(|x − c|< δ ∧ ¬|f(x) − f(c) |< ε)))
2.37	
a.	
i.	
Assume ⊢B. By moving the negation step-by-step inward to 
the atomic wfs, show that ⊢ ¬B* ⇔ C, where C is obtained 
from B by replacing all atomic wfs by their negations. But, 
from ⊢B it can be shown that ⊢C. Hence, ⊢ ¬B*. The converse 
follows by noting that (B*)* is B.
	
	
(ii)	 Apply (i) to ¬B ∨ C.
2.39	
1.	
(
)(
)
( , )
( , )
∃
∀
⇔¬
(
)
y
x
A x y
A x x
1
2
1
2
	
Hyp
	
2.	 (
)
( , )
( , )
∀
⇔¬
(
)
x
A x b
A x x
1
2
1
2
	
1, Rule C
	
3.	
A b y
A b b
1
2
1
2
( , )
( , )
⇔¬
	
2, Rule A4
	
4.	
C ∧ ¬C	
3, Tautology
	
(C is any wf not containing b.) Use Proposition 2.10 and proof by 
contradiction.
2.46	
a.	
In step 4, b is not a new individual constant. It was already used in 
step 2.
2.49	
Assume K is complete and let B and C  be closed wfs of K such that 
⊢K B ∨ C. Assume not-⊢K B. Then, by completeness, ⊢K ¬B. Hence, 
by the tautology ¬ A ⇒ ((A ∨ B) ⇒ B), ⊢K B. Conversely, assume K is 
not complete. Then there is a sentence B of K such that not-⊢K B and 
not-⊢K ¬B. However, ⊢K B ∨ ¬B.
2.50	
See Tarski, Mostowski and Robinson (1953, pp. 15–16).
2.55	 b.	 It suffices to assume B is a closed wf. (Otherwise, look at the 
closure of B.) We can effectively write all the interpretations on 
a finite domain {b1, …, bk}. (We need only specify the interpreta-
tions of the symbols that occur in B.) For every such interpreta-
tion, replace every wf (∀x) C (x), where C (x) has no quantifiers, 
by C  (b1) ∧ … ∧ C (bk), and continue until no quantifiers are left. 
One can then evaluate the truth of the resulting wf for the given 
interpretation.
2.59	
Assume K is not finitely axiomatizable. Let the axioms of K1 be B1, 
B2, …, and let the axioms of K2 be C 1, C 2, .… Then {B1, C1, B2, C2, …} is 
consistent. (If not, some finite subset {B1, B2, …, Bk, C1, …, Cm} is incon-
sistent. Since K1 is not finitely axiomatizable, there is a theorem B of 



428
Answers to Selected Exercises
K1 such that B1, B2, …, Bk ⊢ B does not hold. Hence, the theory with 
axioms {B1, B2, …, Bk, ¬B} has a model M. Since ⊢KB, M must be a 
model of K2, and, therefore, M is a model of {B1, B2, …, Bk, C 1, …, Cm}, 
contradicting the inconsistency of this set of wfs.) Since {B1, C1, B2, C2, …} 
is consistent, it has a model, which must be a model of both K1 and K2.
2.60	
Hint: Let the closures of the axioms of K be B1, B2, .… Choose a sub-
sequence Bj1, Bj2, … such that Bjn+1 is the first sentence (if any) after 
Bjn that is not deducible from B
B
j
jn
1 ∧… ∧
 Let Ck be B
B
B
j
j
jk
1
2
∧
∧… ∧
. 
Then the C k form an axiom set for the theorems of K such that ⊢Ck+1 ⇒ 
Ck but not-⊢Ck ⇒ Ck+1. Then {C 1, C 1 ⇒ C2, C2 ⇒ C3, …} is an independent 
axiomatization of K.
2.61	
Assume B is not logically valid. Then the closure C of B is not logi-
cally valid. Hence, the theory K with ¬C as its only proper axiom has 
a model. By the Skolem–Löwenheim theorem, K has a denumerable 
model and, by the lemma in the proof of Corollary 2.22, K has a model 
of cardinality m. Hence, C is false in this model and, therefore, B is not 
true in some model of cardinality m.
2.65	
c.	
1.	 x = x 	
Proposition 2.23(a)
	
	
2.	 (∃y)x = y 	
1, rule E4
	
	
3.	 (∀x)(∃y)x = y 	
2, Gen
2.68	
a.	
The problem obviously reduces to the case of substitution for a single 
variable at a time: ⊢ x1 = y1 ⇒ t(x1) = t(y1). From (A7), ⊢ x1 = y1 ⇒ 
(t(x1) = t(x1) ⇒ t(x1) = t(y1)). By Proposition 2.23 (a), ⊢ t(x1) = t(x1). Hence, 
⊢ x1 = y1 ⇒ t(x1) = t(y1).
2.70	
a.	 By Exercise 2.65(c), ⊢ (∃y)x = y. By Proposition 2.23(b, c), ⊢ (∀y)
(∀z)(x = y ∧ x = z ⇒ y = z). Hence, ⊢ (∃1y)x = y. By Gen, ⊢ (∀x)(∃1y)
x = y.
2.71	
b.	 i.	
Let ∧1 ≤ i< j ≤ nxi ≠ xj stand for the conjunction of all wfs of the 
form xi ≠ xj, where 1 ≤ i < j ≤ n. Let Bn be (∃x1) … (∃xn) ∧1 ≤i <j ≤n 
xi ≠ xj.
	
	
ii.	
Assume there is a theory with axioms A1, …, An that has the 
same theorems as K. Each of A1, …, An is provable from K1 
plus a finite number of the wfs B1, B2, .… Hence, K1 plus a 
finite number of wfs B
B
j
jn
1 ,
,
…
 suffices to prove all theorems 
of K. We may assume j1< ⋯ <jn. Then an interpretation whose 
domain consists of jn objects would be a model of K, contra-
dicting the fact that Bjn +1 is an axiom of K.
2.74	
For the independence of axioms (A1)–(A3), replace all t = s by the 
statement form A ⇒ A; then erase all quantifiers, terms and associ-
ated commas and parentheses; axioms (A4)–(A6) go over into state-
ment forms of the form P ⇒ P, and axiom (A7) into (P ⇒ P) ⇒ (Q ⇒ Q). 



429
Answers to Selected Exercises
For the independence of axiom (A1), the following four-valued logic, 
due to Dr D.K. Roy, works, where 0 is the only designated value.
A
B
A
B
A
B
A
B
A
B
A
B
A
B
A
B
A
A
⇒
⇒
⇒
⇒
¬
0
0
0
1
0
0
2
0
0
3
0
0
0
1
0
1
1
1
1
0
2
1
0
3
1
1
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
3
2
1
2
0
0
3
1
1
3
0
2
3
0
3
3
0
3
0
	
When A and B take the values 3 and 0, respectively, axiom (A1) takes 
the value 1. For the independence of axiom (A2), Dr Roy devised the 
following four-valued logic, where 0 is the only designated value.
A
B
A
B
A
B
A
B
A
B
A
B
A
B
A
B
A
A
⇒
⇒
⇒
⇒
¬
0
0
0
1
0
0
2
0
0
3
0
0
0
1
0
1
1
1
1
0
2
1
0
3
1
0
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
3
2
1
2
0
0
3
1
1
3
0
2
3
0
3
3
0
3
0
	
If A, B, and C take the values 3, 0, and 2, respectively, then axiom (A2) 
is 1. For the independence of axiom (A3), the proof on page 36 works. 
For axiom (A4), replace all universal quantifiers by existential quanti-
fiers. For axiom (A5), change all terms t to x1 and replace all universal 
quantifiers by (∀x1). For axiom (A6), replace all wfs t = s by the negation 
of some fixed theorem. For axiom (A7), consider an interpretation in 
which the interpretation of = is a reflexive nonsymmetric relation.
2.83	
a.	
∀
(
) ∃
(
)
∃
(
)
…
(
) ∧
(
)
(
) ⇒∃
(
)
(
x
y
z
z x y
y
A
x y z
z
B
, , ,
,
, ,
1
3
 (B(z, y, x, …, x) 
∧ z = x))
2.84	
a.	 (
)(
)(
)
( )
( , )
( )
( , )
∃
∀
∃
⇒

⇒
⇒


(
)
z
w
x
A x
A x y
A w
A y z
1
1
1
2
1
1
1
2
2.87	
S has the form (
)(
)(
)
( , )
( )
( )
∃
∃
∀
⇒

⇒
(
)
x
y
z
A x y
A x
A z
1
2
1
1
1
1
. Let the 
domain D be {1, 2}, let A1
2 be <, and let A u
1
1( ) stand for u = 2. Then S  is 
true, but (
)(
)
( , )
∀
∃
x
y A x y
1
2
 is false.
2.88	
Let g be a one–one correspondence between D* and D. Define:
a
a
f
b
b
f
b
b
j
j
j
n
n
j
n
n
( )
=
( )
(
) (
)
…
(
) =
(
)
(
) …
(
)
(
)

∗
∗
M
M
M
M
g
g
g
g
;
,
,
,
,
1
1
1
−



…


(
) …
(
)


;
,
,
,
,


M*
M
if and only if
A
b
b
A
b
b
j
n
n
j
n
n
1
1
g
g



430
Answers to Selected Exercises
2.95	
Hint: Extend K by adding axioms Bn, where Bn asserts that there are at 
least n elements. The new theory has no finite models.
2.96	
(a) Hint: Consider the wfs Bn, where Bn asserts that there are at least 
n elements. Use elimination of quantifiers, treating the Bns as if they 
were atomic wfs.
2.101	 Let W be any set. For each b in W, let ab be an individual constant. Let 
the theory K have as its proper axioms: ab ≠ ac for all b, c in W such that 
b ≠ c, plus the axioms for a total order. K is consistent, since any finite 
subset of its axioms has a model. (Any such finite subset contains only 
a finite number of individual constants. One can define a total order 
on any finite set B by using the one–one correspondence between B 
and a set {1, 2, 3, …, n} and carrying over to B the total order < on 
{1, 2, 3, …, n}.) Since K is consistent, K has a model M by the general-
ized completeness theorem. The domain D of M is totally ordered by 
the relation <M; hence, the subset Dw of D consisting of the objects (ab)M 
is totally ordered by <M. This total ordering of Dw can then be carried 
over to a total ordering of W: b <w c if and only if ab <M ac.
2.103	 Assume M1 is finite and M1 ≡ M2. Let the domain D1 of M1 have n ele-
ments. Then, since the assertion that a model has exactly n elements 
can be written as a sentence, the domain D2 of M2 must also have n 
elements. Let D1 = {b1, …, bn} and D2 = {c1, …, cn}.
Assume M1 and M2 are not isomorphic. Let φ be any one of the 
n! one–one correspondences between D1 and D2. Since φ is not an 
­isomorphism, either: (1) there is an individual constant a and an ele-
ment bj of D1 such that either (i) b
a
j =
M1 ∧ φ (b
a
j) ≠
M2 or (ii) b
a
j ≠
M1 ∧ 
φ(bj) = aM2; or (2) there is a function letter fk
m and b b
b
j
jm
ℓ,
,
,
1 …
 in D1 
such that
	
b
f
b
b
b
f
b
b
k
m
j
j
k
m
j
j
m
m
ℓ
ℓ
= (
)
…
(
)
≠(
)
(
) …
(
)
(
)
M
M
and
1
1
2
1
,
,
(
)
,
,
ϕ
ϕ
ϕ
	
or (3) there is a predicate letter Ak
m and b
b
j
jm
1 ,
,
…
 in D1 such that either
	
i.	
M1
1
A
b
b
k
m
j
jm
,
,
…

 and M2
1
¬A
b
b
k
m
j
jm
ϕ
ϕ
(
) …
(
)


,
,
 or
	
ii.	
M1
1
¬A
b
b
k
m
j
jm
,
,
…

 and M2
1
A
b
b
k
m
j
jm
ϕ
ϕ
(
) …
(
)


,
,
. Construct a 
wf B φ as follows:
	
Bϕ is
if 1 i holds
if 1 ii holds
if
x
a
x
a
x
f
x
x
j
j
k
m
j
jm
=
≠
=
…
( ) ( )
( ) ( )
(
,
,
)
ℓ
1
( )
(
,
,
)
( ) ( )
(
,
,
)
( ) (
2 holds
if 3
i holds
if 3
i
A
x
x
A
x
x
k
m
j
j
k
m
j
j
m
m
1
1
…
¬
…
i holds
)











431
Answers to Selected Exercises
	
Let φ1, …, φn be the one–one correspondences between D1 and D2. Let 
A  be the wf
	
∃
(
) … ∃
(
)
≠
∧
∧
∧… ∧




∧
≤< ≤
x
x
x
x
n
i j n
i
j
n
1
1
1
2
B
B
B
ϕ
ϕ
ϕ
	
Then A  is true for M1 but not for M2.
2.104	 a.	 There are ℵα sentences in the language, of K. Hence, there are 
2ℵα sets of sentences. If M1 ≡ M2 does not hold, then the set of 
sentences true for M1 is different from the set of sentences true 
for M2.
2.105	 Let K* be the theory with ℵγ new symbols bτ and, as axioms, all sen-
tences true for M and all bτ ≠ bρ for τ ≠ ρ. Prove K* consistent and apply 
Corollary 2.34.
2.108	 a.	 Let M be the field of rational numbers and let X = {−1}.
2.110	 Consider the wf (∃x2)x2 < x1.
2.111	 a.	 ii.	
Introduce a new individual constant b and form a new theory 
by adding to the complete diagram of M1 all the sentences 
b ≠ t for all closed terms t of the language of K.
2.112	 If ∅ ∉ F, F  ≠ P (A). Conversely, if ∅ ∈ F, then, by clause (3) of the defini-
tion of filter, F  = P (A).
2.113	 If F  = FB, then ∩C ∈F C = B ∈ F. Conversely, if B = ∩C∈F C ∈ F, then 
F   = F B.
2.114	 Use Exercise 2.113.
2.115	 a.	 A ∈ F, since A = A − ∅.
	
b.	 If B = A − W1 ∈ F  and C = A − W2 ∈ F, where W1 and W2 are finite, 
then B ∩ C = A − (W1 ∪ W2) ∈ F, since W1 ∪ W2 is finite.
	
c.	 If B = A − W ∈ F, where W is finite, and if B ⊆ C, then C = A − 
(W − C) ∈ F, since W − C is finite.
	
d.	 Let B ⊆ C. So, B = A − W, where W is finite. Let b ∈ B. Then W ∪ 
{b} is finite. Hence, C = A − (W ∪ {b}) ∈ F. But, B ⊈ C, since b ∉ C. 
Therefore, F ≠ FB.
2.118	 Let F   ′ = {D|D ⊆ A ∧ (∃C)(C ∈ F ∧ B ∩ C ⊆ D)}.
2.119	 Assume that, for every B ⊆ A, either B ∈ F  or A − B ∈ F. Let G be a 
filter such that F   ⊂ G. Let B ∈ G − F . Then A − B ∈ F . Hence, A − B ∈ G. 
So, ∅ = B ∩ (A − B) ∈ G and G is improper. The converse follows from 
Exercise 2.118.
2.120	 Assume F  is an ultrafilter and B ∉ F, C ∉ F. By Exercise 2.119, A − B 
∈ F and A − C ∈ F. Hence, A − (B ∪ C) = (A − B) ∩ (A − C) ∈ F. Since F 
is proper, B ∪ C ∉ F. Conversely, assume B ∉ F ∧ C ∉ F  ⇒ B ∪ C ∉ F. 



432
Answers to Selected Exercises
Since B ∪ (A − B) = A ∈ F, this implies that, if B ∉ F, then A − B ∈ F. Use 
Exercise 2.119.
2.121	 a.	 Assume FC is a principal ultrafilter. Let a ∈ C and assume C ≠ {a}. 
Then {a} ∉ FC and C − {a} ∉ FC. By Exercise 2.120, C = {a} ∪ (C − {a}) 
∉ FC, which yields a contradiction.
	
b.	 Assume a nonprincipal ultrafilter F   contains a finite set, and let B 
be a finite set in F   of least cardinality. Since F   is nonprincipal, the 
cardinality of B is greater than 1. Let b ∈ B. Then B − {b} ≠ ∅. Both 
{b} and B − {b} are finite sets of lower cardinality than B. Hence, 
{b} ∉ F   and B − {b} ∉ F. By Exercise 2.120, B = {b} ∪ (B − {b}) ∉ F, 
which contradicts the definition of B.
2.124	 Let J be the set of all finite subsets of Γ. For each Δ in J, choose a model 
MΔ of Δ. For Δ in J, let Δ* = {Δ′|Δ′ ∈ J ∧ Δ ⊆ Δ′}. The collection G of all 
Δ*s has the finite-intersection property. By Exercise 2.117, there is a 
proper filter F  ⊇ G. By the ultrafilter theorem, there is an ultrafilter 
F ′ ⊇ F  ⊇ G. Consider 
M /
∆
∆∈
∏
′
J
F . Let B ∈ Γ. Then {B}* ∈ G ⊆ F ′. 
Therefore, {
}
|
B
G
B
F
* ⊆
∈
∧
{
}∈
′
∆∆
∆
M
. By Loś’s theorem, B is true 
in 
M /
∆
∆∈
∏
′
J
F .
2.125	 a.	 Assume W    is closed under elementary equivalence and ultraprod-
ucts. Let Δ be the set of all sentences of L that are true in every 
interpretation in W. Let M be any model of Δ. We must show that 
M is in W.  Let Γ be the set of all sentences true for M. Let J be the 
set of finite subsets of Γ. For Γ′ = {B1, …, Bn} ∈ J, choose an interpre-
tation NΓ′ in W   such that B1 ∧ … ∧ Bn is true in NΓ′. (If there were 
no such interpretation, ¬(B1 ∧ … ∧ Bn), though false in M, would 
be in Δ.) As in Exercise 2.124, there is an ultrafilter F′ such that 
N
N /
* =
′
′
′∈
∏
Γ
Γ
J
F  is a model of Γ. Now, N* ∈ W. Moreover, M ≡ 
N*. Hence, M ∈ W.
	
b.	 Use (a) and Exercise 2.59.
	
c.	 Let W   be the class of all fields of characteristic 0. Let F   be a nonprin-
cipal ultrafilter on the set P of primes, and consider M
/ .
=
∈∏
p P
P
Z
F  
Apply (b).
2.126	 R# ⊆ R*. Hence, the cardinality of R* is ≥ 2ℵ0. On the other hand, Rω 
is equinumerous with 2ω and, therefore, has cardinality 2ℵ0. But the 
­cardinality of R* is at most that of Rω.
2.127	 Assume x and y are infinitesimals. Let ε be any positive real. Then 
|x| < ε/2 and |y| < ε/2. So, |x + y| ≤ |x| + |y|<ε/2 + ε/2 = ε; |xy| = 
|x||y|<1 ⋅ ε = ε; |x − y| ≤ |x| + |−y|<ε/2 + ε/2 = ε.
2.128	 Assume | x| < r1 and |y| < ε for all positive real ε. Let ε be a posi-
tive real. Then ε/r1 is a positive real. Hence | y| < ε/r1, and so, |xy| = 
|x|| y|< r1(ε/r1) = ε.



433
Answers to Selected Exercises
2.130	 Assume x − r1 and x − r2 are infinitesimals, with r1 and r2 real. Then 
(x − r1) − (x − r2) = r2 − r1 is infinitesimal and real. Hence, r2 − r1 = 0.
2.131	 a.	 x − st(x) and y − st(y) are infinitesimals. Hence, their sum (x + y) − 
(st(x) + st(y)) is an infinitesimal. Since st(x) + st(y) is real, st(x) + 
st(y) = st(x + y) by Exercise 2.130.
2.132	 a.	 By Proposition 2.45, s*(n) ≈ c1 and u*(n) ≈ c2 for all n ∈ ω* − ω. 
Hence, s * (n) + u*(n) ≈ c1 + c2 for all n ∈ ω* − ω. But s*(n) + u*(n) = 
(s + u)*(n). Apply Proposition 2.45.
2.133	 Assume f continuous at c. Take any positive real ε. Then there is a 
positive real δ such that (∀x)(x ∈ B ∧ |x − c|< δ ⇒ |f(x) − f(c) |< ε) 
holds in R. Therefore, (∀x)(x ∈ B* ∧ |x − c|< δ ⇒ |f*(x) − f(c) |< ε) holds 
in R *. So, if x ∈ B* and x ≈ c, then |x − c| < δ and, therefore, |f*(x) − 
f(c)|< ε. Since ε was arbitrary, f*(x) ≈ f(c). Conversely, assume x ∈ B* ∧ 
x ≈ c ⇒ f*(x) ≈ f(c). Take any positive real ε. Let δ0 be a positive infini-
tesimal. Then (∀x)(x ∈ B* ∧ |x − c| < δ0 ⇒ |f*(x) − f(c) | < ε) holds for 
R  *. Hence, (∃δ)(δ > 0 ∧ (∀x)(x ∈ B* ∧ |x − c| < δ ⇒ |f′(x) − f(c) |< ε)) holds 
for R  *, and so, (∃δ)(δ > 0 ∧ (∀x)(x ∈ B ∧ |x − c| < δ ⇒ |f(x) − f(c) |< ε)) 
holds in R.
2.134	 a.	 Since x ∈ B* ∧ x ≈ C ⇒ (f*(x) ≈ f(c) ∧ g*(x) ≈ g(c)) by Proposition 2.46, 
we can conclude x ∈ B* ∧ x ≈ c ⇒ (f + g)*(x) ≈ (f + g)(c), and so, by 
Proposition 2.46, f + g is continuous at c.
2.139	 a.	 i.	
¬
∀
∨
(
) ⇒
∀
(
)∨∀


(
)
( )
( )
(
)
( )
(
)
( )
x
A x
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
	
	
ii.	
(
)
( )
( )
∀
∨
(
)
x
A x
A x
1
1
2
1
	
(i)
	
	
iii.	
¬
∀
(
)∨∀


(
)
( )
(
)
( )
x A x
x A x
1
1
2
1
	
(i)
	
	
iv.	
¬ ∀
(
)
( )
x A x
1
1
	
(iii)
	
	
v.	
¬ ∀
(
)
( )
x A x
2
1
	
(iii)
	
	
vi.	
(
)
( )
∃
¬
x
A x
1
1
	
(iv)
	
	
vii.	
(
)
( )
∃
¬
x
A x
2
1
	
(v)
	
	
viii.	 ¬A b
1
1( ) 	
(vi)
	
	
ix.	
¬A c
2
1( )	
(vii)
	
	
x.
	
A b
A b
1
1
2
1
( )
( )
∨
↙
↘
	
(ii)
	
	
xi.	
A b
A b
1
1
2
1
( )
( )	
(x)
	
	
xii.
	
×
∨
A c
A c
1
1
2
1
( )
( )
↙
↘	
(ii)
	
	
xiii.
	
A c
A c
1
1
2
1
( )
( )
×
	
(xii)



434
Answers to Selected Exercises
	
	
No further rules are applicable and there is an unclosed branch. 
Let the model M have domain {b, c}, let A1
1
(
)
M hold only for c, 
and let A2
1
(
)
M hold for only b. Then, (
)
( )
( )
∀
∨
(
)
x
A x
A x
1
1
2
1
 is true 
for M, but (
)
( )
∀x A x
1
1
 and (
)
( )
∀x A x
2
1
 are both false for M. Hence, 
(
)
( )
( )
(
)
( )
(
)
( )
∀
∨
(
) ⇒
∀
(
)∨∀
x
A x
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
 is not logically 
valid.
Chapter 3
3.4	
Consider the interpretation that has as its domain the set of polynomi-
als with integral coefficients such that the leading coefficient is non-
negative. The usual operations of addition and multiplication are the 
interpretations of + and ·. Verify that (S1)–(S8) hold but that Proposition 
3.11 is false (substituting the polynomial x for x and 2 for y).
3.5	
a.	 Form a new theory S′ by adding to S a new individual constant b 
and the axioms b
b
b
b
n
≠
≠
≠
…
≠
…
0
1
2
,
,
,
,
,
 Show that S′ is con-
sistent, and apply Proposition 2.26 and Corollary 2.34(c).
	
b.	 By a cortège let us mean any denumerable sequence of 0s and 1s. 
There are 2ℵ0 cortèges. An element c of a denumerable model M of 
S determines a cortège (s0, s1, s2, …) as follows: si = 0 if ⊧M pi|c, and 
si = 1 if ⊧M ¬(pi|c). Consider now any cortège s. Add a new constant 
b to S, together with the axioms Bi(b), where Bi(b) is pi|b if si = 0 and 
Bi(b) is ¬(pi|b) if si = 1. This theory is consistent and, therefore, has 
a denumerable model Ms, in which the interpretation of b deter-
mines the cortège s. Thus, each of the 2ℵ0 cortèges is determined 
by an element of some denumerable model. Every denumer-
able model determines denumerably many cortèges. Therefore, 
if a maximal collection of mutually nonisomorphic denumerable 
models had cardinality m < 2ℵ0, then the total number of cortèges 
represented in all denumerable models would be  ≤ m × ℵ0 < 2ℵ0. 
(We use the fact that the elements of a denumerable model deter-
mine the same cortèges as the elements of an isomorphic model.)
3.6	
Let (D, 0, ′) be one model of Peano’s postulates, with 0 ∈ D and ′ the 
successor operation, and let (D#, 0#,*) be another such model. For 
each x in D, by an x-mapping we mean a function f from Sx = {u|u ∈ 
D ∧ u ≤ x} into D# such that f(0) = 0# and f(u′) = (f(u)) * for all u < x. 
Show by induction that, for every x in D, there is a unique x-mapping 
(which will be denoted fx). It is easy to see that, if x1 < x2, then the 
restriction of fx2 to Sx1 must be fx1. Define F(x) = fx(x) for all x in D. Then 
F is a function from D into D# such that F(0) = 0# and F(x′) = (F(x))* 



435
Answers to Selected Exercises
for all x in D. It is easy to prove that F is one–one. (If not, a contra-
diction results when we consider the least x in D for which there is 
some y in D such that x ≠ y and F(x) = F(y).) To see that F is an iso-
morphism, it only remains to show that the range of F is D#. If not, 
let z be the least element of D# not in the range of F. Clearly, z ≠ 0#. 
Hence, z = w* for some w. Then w is in the range of F, and so w = F(u) 
for some u in D. Therefore, F(u′) = (F(u))* = w* = z, contradicting the 
fact that z is not in the range of F.
The reason why this proof does not work for models of first-order 
number theory S is that the proof uses mathematical induction and 
the least-number principle several times, and these uses involve prop-
erties that cannot be formulated within the language of S. Since the 
validity of mathematical induction and the least-number principle in 
models of S is guaranteed to hold, by virtue of axiom (S9), only for wfs 
of S, the categoricity proof is not applicable. For example, in a nonstan-
dard model for S, the property of being the interpretation of one of the 
standard integers 0 1 2 3
, , , , … is not expressible by a wf of S. If it were, 
then, by axiom (S9), one could prove that 0 1 2 3
, , , , …
{
} constitutes the 
whole model.
3.7	
Use a reduction procedure similar to that given for the theory K2 on 
pages 114–115. For any number k, define k · t by induction: 0 · t is 0 and 
(k + 1) · t is (k · t) + t; thus, k · t is the sum of t taken k times. Also, for any 
given k, let t ≡ s(mod k) stand for (∃x)(t = s + k · x ∨ s = t + k · x). In the 
reduction procedure, consider all such wfs t ≡ s(mod k), as well as the 
wfs t < s, as atomic wfs, although they actually are not. Given any wfs 
of S+, we may assume by Proposition 2.30 that it is in prenex normal 
form. Describe a method that, given a wf (∃y)C, where C contains no 
quantifiers (remembering the convention that t ≡ s(mod k) and t < s are 
considered atomic), finds an equivalent wf without quantifiers (again 
remembering our convention). For help on details, see Hilbert and 
Bernays (1934, I, pp. 359–366).
3.8	
b.	 Use part (a) and Proposition 3.6(a)(i).
	
c.	 Use part (b) and Lemma 1.12.
3.13	
Assume f(x1, …, xn) = xn+1 is expressible in S by B(x1, …, xn+1). Let 
C  (x1, …, xn+1) be B(x1, …, xn+1) ∧ (∀z)(z < xn+1 ⇒ ¬B(x1, …, xn+1)). Show 
that C  represents f (x1, …, xn) in S. [Use Proposition 3.8(b).] Assume, 
conversely, that f (x1, …, xn) is representable in S by A (x1, …, xn+1). Show 
that the same wf expresses f (x1, …, xn = xn+1 in S.
3.16	
a.	 (∃y)u<y<vR(x1, …, xn, y) is equivalent to (
)
(
,
,
,
),
(
)
∃
…
+
+
< −
+
z
x
x
z
u
z v
u
n

1
1
1
R
 
and similarly for the other cases.
3.18	
If the relation R(x1, …, xn, y): f(x1, …, xn) = y is recursive, then CR is recur-
sive and, therefore, so is f(x1, …, xn) = μy(CR(x1, …, xn, y) = 0). Conversely, 
if f (x1, …, xn) is recursive, CR(x1, …, xn, y) = sg|f(x1, …, xn) − y | is recursive.



436
Answers to Selected Exercises
3.19
	
n
y
y
n
n
C
y
y n
y n

=
>
(
)
=
(
)
≤+
≤
∏
∑
δ µ
1
2
(
)
( )
( )
sg
Pr
3.20	
[
]
(
!
!
!)
ne
n
n
=
+ +
+
+
+




1
1
1
2
1
3
1

, since n
n
n
n
1
1
1
2
1
(
)!
(
)!
!.
+
+
+
+



<

 
Let 1
1
1
2
1
+ +
+
+
=
!
!
( )
! .

n
g n
n
 Then g(0) = 1 and g(n + 1) = 
(n + 1)g(n) + 1. Hence, g is primitive recursive. Therefore, so is 
[
]
( )
!
( !,
( )).
ne
ng n
n
n ng n
= 


= qt
3.21	
RP(y, z) stands for (∀x)x≤y+z(x|y ∧ x|z ⇒ x = 1).
	
ϕ( )
( , )
n
C
y n
y n
=
(
)
≤∑sg
RP
3.22	
Z
Z y
U
y Z y
( )
, (
)
, ( )
0
0
1
2
2
=
+
=
(
) .
3.23	
Let v = (p0p1 … pk) + 1. Some prime q is a divisor of v. Hence, q ≤ v. But 
q is different from p0, p1, …, pk. If q = pj, then pj|v and pj|p0 p1 … pk would 
imply that pj|1 and, therefore, pj = 1. Thus, pk+1 ≤ q ≤ (p0 p1…pk) + 1.
3.26	
If Goldbach’s conjecture is true, h is the constant function 2. If 
Goldbach’s conjecture is false, h is the constant function 1. In either 
case, h is primitive recursive.
3.28	
List the recursive functions step by step in the following way. In the 
first step, start with the finite list consisting of Z(x), N(x), and U x
1
1( ) . At 
the (n + 1)th step, make one application of substitution, recursion and 
the μ-operator to all appropriate sequences of functions already in the 
list after the nth step, and then add the n + 1 functions U
x
x
j
n
n
+
+
…
1
1
1
(
,
,
) 
to the list. Every recursive function eventually appears in the list.
3.29	
Assume fx(y) is primitive recursive (or recursive). Then so is fx(x) + 1. 
Hence, fx(x) + 1 is equal to fk(x) for some k. Therefore, fk(x) = fx(x) + 1 for 
all x and, in particular, fk(k) = fk(k) + 1.
3.30	
a.	 Let d be the least positive integer in the set Y of integers of the form 
au + bv, where u and v are arbitrary integers—say, d = au0 + bv0. 
Then d|a and d|b. (To see this for a, let a = qd + r, where 0 ≤ r < d. 
Then r = a − qd = a − q(au0 + bv0) = (1 − qu0)a + (− qv0)b ∈ Y. Since d 
is the least positive integer in Y and r < d, r must be 0. Hence d|a.) 



437
Answers to Selected Exercises
If a and b are relatively prime, then d = 1. Hence, 1 = au0 + bv0. 
Therefore, au0 ≡ 1 (mod b).
3.32	
a.	 1944 = 2335. Hence, 1944 is the Gödel number of the expression ().
	
b.	 49 = 1 + 8(2131). Hence, 49 is the Gödel number of the function 
­letter f1
1.
3.34	
a.	 g f1
1
49
(
) =
 and ɡ(a1) = 15. So, g f
a
1
1
1
49
3
15
5
2 3 5 7
(
)
(
) =
.
3.37	
Take as a normal model for RR, but not for S, the set of polynomials 
with integral coefficients such that the leading coefficient is nonnega-
tive. Note that (∀x)(∃y)(x = y + y ∨ x = y + y + 1) is false in this model 
but is provable in S.
3.38	 Let ∞ be an object that is not a natural number. Let ∞′ = ∞, ∞ + 
x = x + ∞ = ∞ for all natural numbers x, ∞ · 0 = 0 · ∞ = 0, and ∞ · x = x · 
∞ = ∞ for all x ≠ 0.
3.41	
Assume S is consistent. By Proposition 3.37(a), G is not provable in S. 
Hence, by Lemma 2.12, the theory Sg is consistent. Now, ¬G  is equiva-
lent to (∃x2)Pf (x2, ⌜G⌝). Since there is no proof of G in S, Pf (k, q) is false for 
all natural numbers k, where q = ⌜G⌝. Hence, ⊢s ¬Pf (k q
, ) for all natural 
numbers k. Therefore, ⊢sg ¬
k q
Pf
,
(
). But, sg ∃
(
)
(
)
x
x
q
2
2
Pf
,
. Thus Sg is 
ω-inconsistent.
3.45	
(G. Kreisel, Mathematical Reviews, 1955, Vol. 16, p. 103) Let B(x1) be a 
wf of S that is the arithmetization of the following: x1 is the Gödel 
number of a closed wf B such that the theory S + {B} is ω-inconsistent. 
(The latter says that there is a wf E(x) such that, for every n, E n
( ) is 
provable in S + {B}, and such that (∃x)¬E (x) is provable in S + {B}.) By 
the fixed-point theorem, let C be a closed wf such that ⊢S C ⇔ B(⌜C⌝). 
Let K = S + {C}. (1) C is false in the standard model. (Assume C true. 
Then K is a true theory. But, C ⇔ B (⌜C⌝)) is true, since it is provable 
in S. So, B (⌜C⌝) is true. Hence, K is ω-inconsistent and, therefore, K is 
not true, which yields a contradiction.) (2) K is ω-consistent. (Assume 
K ω-inconsistent. Then B (⌜C⌝) is true and, therefore, C is true, contra-
dicting (1).)
3.46	
a.	 Assume the “function” form of Church’s thesis and let A be an 
effectively decidable set of natural numbers. Then the characteris-
tic function CA is effectively computable and, therefore, recursive. 
Hence, by definition, A is a recursive set.
	
b.	 Assume the “set” form of Church’s thesis and let f (x1, …, xn) be any 
effectively computable function. Then the relation f (x1, …, xn) = y 
is effectively decidable. Using the functions σ
σ
k
i
k
,
 of pages 184–185 
let A be the set of all z such that f
z
z
z
n
n
n
n
n
σ
σ
σ
1
1
1
1
1
+
+
+
+
…
(
) =
( ),
,
( )
( ). 
Then A is an effectively decidable set and, therefore, recursive. 
Hence, f x
x
z C
z
n
n
n
A
(
,
,
)
( )
1
1
1
0
…
=
=
(
)
(
)
+
+
σ
µ
 is recursive.



438
Answers to Selected Exercises
3.48	
Let K be the extension of S that has as proper axioms all wfs that are 
true in the standard model. If Tr were recursive, then, by Proposition 
3.38, K would have an undecidable sentence, which is impossible.
3.49	
Use Corollary 3.39.
3.50	
Let f (x1, …, xn) be a recursive function. So, f (x1, …, xn) = y is a recursive 
relation, expressible in K by a wf A (x1, …, xn, y). Then f is representable 
by A (x1, …, xn, y) ∧ (∀z)(z < y ⇒ ¬A (x1, …, xn, z)), where z < y stands for 
z ≤ y ∧ z ≠ y.
3.53	
a.	 ⊢ 0 = 1 ⇒ G. Hence, ⊢ Bew(⌜
⌝
0
1
=
) ⇒ Bew(⌜G⌝) and, therefore, 
⊢¬Bew(⌜G⌝) ⇒ ¬Bew(⌜
⌝
0
1
=
). Thus, ⊢G ⇒ ¬Bew(⌜
⌝
0
1
=
).
	
b.	 ⊢ Bew(⌜G ⌝) ⇒ Bew(⌜Bew(⌜G ⌝) ⌝). Also, ⊢ ¬G ⇔ Bew(⌜G ⌝), and so, 
⊢ Bew(⌜¬G ⌝) ⇔ Bew(⌜Bew(⌜G ⌝) ⌝). Hence ⊢ Bew(⌜G ⌝) ⇒ Bew(⌜¬G ⌝). By 
a tautology, ⊢ G ⇒ (¬G ⇒ (G ∧ ¬G)); hence, ⊢ Bew(⌜G ⌝) ⇒ Bew(⌜¬G ⇒ 
(G ∧ ¬G)⌝). Therefore, ⊢ Bew(⌜G ⌝) ⇒ (Bew(⌜¬G ⌝) ⇒ Bew(⌜(G ∧ ¬G)⌝)). It 
follows that ⊢ Bew(⌜G ⌝) ⇒ Bew(⌜(G ∧ ¬G)⌝). But, ⊢G
G
∧
⇒
=
¬
0
1; so, 
⊢ Bew(⌜(G ∧ ¬G)⌝) ⇒ Bew(⌜
⌝
0
1
=
). Thus, ⊢ Bew(⌜G ⌝) ⇒ Bew(⌜
⌝
0
1
=
), 
and ⊢ ¬Bew(⌜
⌝
0
1
=
) ⇒ ¬Bew(⌜G ⌝). Hence, ⊢ ⌜Bew(⌜
⌝
0
1
=
) ⇒ G.
3.56	
If a theory K is recursively decidable, the set of Gödel numbers of the-
orems of K is recursive. Taking the theorems of K as axioms, we obtain 
a recursive axiomatization.
3.58	
Assume there is a recursive set C such that TK ⊆ C and RefK ⊆C;. Let 
C be expressible in K by A (x). Let F, with Gödel number k, be a fixed 
point for ¬A (x). Then, ⊢K F  ⇔ ¬A (k). Since A (x) expresses C in K, 
⊢K A (k) or ⊢K ¬A (k).
	
a.	 If ⊢K A (k), then ⊢K ¬F. Therefore, k
C
∈
⊆
RefK
. Hence, ⊢K ¬A ( k ), 
contradicting the consistency of K.
	
b.	 If ⊢K ¬A (k ), then ⊢K F.   So, k ∈ TK ⊆ C and therefore, ⊢K A (k), con-
tradicting the consistency of K.
3.60	
Let K2 be the theory whose axioms are those wfs of K1 that are prov-
able in K*. The theorems of K2 are the axioms of K2. Hence, x
T
∈
K2 if 
and only if FmlK
K
1( )
x
x
T
∧
∈
∗. So, if K* were recursively decidable—
that is, if TK∗ were recursive—TK2 would be recursive. Since K2 is a con-
sistent extension of K1, this would contradict the essential recursive 
undecidability of K1.
3.61	
a.	 Compare the proof of Proposition 2.28.
	
b.	 By part (a), K* is consistent. Hence, by Exercise 3.60, K* is essentially 
recursively undecidable. So, by (a), K is recursively undecidable.
3.62	
b.	 Take (
)
( )
∀
⇔
=
(
)
x
A x
x
x
j
1
 as a possible definition of Aj
1.
3.63	
Use Exercises 3.61(b) and 3.62.
3.64	
Use Corollary 3.46, Exercise 3.63, and Proposition 3.47.



439
Answers to Selected Exercises
Chapter 4
4.12	
(s) Assume u ∈ x × y. Then u = 〈v, w〉 = {{v}, {v, w}} for some v in x and w 
in y. Then v ∈ x ∪ y and w ∈ x ∪ y. So, {v} ∈ P (x ∪ y) and {v, w} ∈ P (x ∪ y). 
Hence, {{v}, {v, w}} ∈ P(P(x ∪ y)).
	
(t) X ⊆ Y ∨ Y ⊆ X
4.15	
a.	 D(x)⊆ ∪ ( ∪ x) and R(x)⊆ ∪ ( ∪ x). Apply Corollary 4.6(b).
	
b.	 Use Exercises 4.12(s), 4.13(b), axiom W, and Corollary 4.6(b).
	
c.	 If Rel(Y), then Y ⊆ D(Y) × R(Y). Use part (b) and Corollary 4.6(b).
4.18	
Let X = {〈y1, y2〉|y1 = y2 ∧ y1 ∈ Y}; that is, X is the class of all ordered 
pairs 〈u, u〉 with u ∈ Y. Clearly, Fnc(X) and, for any set x, (∃v)(〈v, u〉 ∈ X 
∧ v ∈ x) ⇔ u ∈ Y ∩ x. So, by axiom R, M(Y ∩ x)
4.19	
Assume Fnc(Y). Then Fnc(x  Y) and D(x  Y) ⊆ x. By axiom R, M (Y″x).
4.22	
a.	 Let ∅ be the class {u|u ≠ u}. Assume M(X). Then ∅ ⊆ X. So, ∅ = ∅ ∩ X. 
By axiom S, M (∅).
4.23	 Assume M(V). Let Y = {x|x ∉ x}. It was proved above that ¬M(Y). But 
Y ⊆ V. Hence, by Corollary 4.6(b), ¬M(V).
4.27	
b.	 grandparent and uncle
4.30	
c.	 Let u be the least ∈-element of X − Z.
4.33	
a.	 By Proposition 4.11(a), Trans(ω). By Proposition 4.11(b) and 
Proposition 4.8(j), ω ∈ On. If ω ∈ K1 then ω ∈ ω, contradicting 
Proposition 4.8(a). Hence, ω ∉ K1.
4.39	
Let X1 = X × {∅} and Y1 = Y × {1}.
4.40	
For any u ⊆ y, let the characteristic function Cu be the function with 
domain y such that ′
= ∅
C w
u
 if w ∈ u and ′
=
C w
u
1 if w ∈ y − u. Let F be 
the function with domain P (y) such that F′u = Cu for u ∈ P (y). Then 
P
x
F
y
( )≅
≅
2
4.41	
a.	 For any set u, D (u) is a set by Exercise 4.15(a).
	
b.	 If u ∈ xy, then u ⊆ y × x. So, xy ⊆  P  (y × x).
4.42	
a.	 ∅ is the only function with domain ∅.
	
c.	 If D (u) ≠ ∅, then R (u) ≠ ∅.
4.43	
Define a function F with domain X such that, for any x0 in X, F(x0) is 
the function ɡ in X{u} such that ɡ′u = x0. Then X
X
F
u
≅
{ } .
4.44	 Assume X
Y
F≅
 and Z W
G≅
. If ¬M(W), then ¬M(Z) and XZ = YW = ∅ 
by Exercise 4.41(a). Hence, we may assume M(W) and M(Z). Define 
a function Φ on XZ as follows: if f ∈ XZ, let Φ ′f = F ⚬ f ⚬ G−1. Then 
X
Y
Z
W
≅
Φ
.



440
Answers to Selected Exercises
4.45	
If X or Y is not a set, then ZX∪Y and ZX × ZY are both ∅. We may assume 
then that X and Y are sets. Define a function Φ with domain ZX∪Y as 
follows: if f ∈ ZX∪Y, let Φ ′f = 〈X  f, Y  f〉. Then Z
Z
Z
X
Y
X
Y
∪≅
×
Φ
.
4.46	
Define a function F with domain (xy)z as follows: for any f in (xy)z, let F′f 
be the function in xy×z such that (F′f)′〈u, v〉 = (f′v)′u for all 〈u, v〉 ∈ y × z. 
Then (
)
x
x
y z
F
y z
≅
× .
4.47	
If  ¬ M(Z),(X × Y)Z = ∅ = ∅ × ∅ = XZ × YZ. Assume then that M(Z). 
Define a function F:XZ × YZ → (X × Y)Z as follows: for any f ∈ XZ, ɡ ∈ 
YZ, (F′〈f, ɡ〉)′z = 〈f′z, ɡ′z〉 for all z in Z. Then X
Y
X
Y
Z
Z
F
Z
×
≅
×
(
) .
4.48	
This is a direct consequence of Proposition 4.19.
4.54	
b.	 Use Bernstein’s theorem (Proposition 4.23(d)).
	
c.	 Use Proposition 4.23(c, d).
4.55	
Define a function F from V into 2c as follows: F‘u = {u, ∅} if u ≠ ∅; F′∅ = 
{1, 2}. Since, F is one-one, V ≼ 2c. Hence, by Exercises 4.23 and 4.50, ¬M(2c).
4.56	
(h) Use Exercise 4.45.
	
i.	
2x≼2x + cx≼2x + c2x = 2x × 2 ≅ 2x × 21 ≅ 2X + 
c
1 ≅ 2x.
	
Hence, by Bernstein’s Theorem, 2x +cx ≅ 2x.
4.59	
Under the assumption of the axiom of infinity, ω is a set such that (∃u)(u ∈ 
ω) ∧ (∀y)(y ∈ ω ⇒ (∃z)(z ∈ ω ∧ y ⊂ z)). Conversely, assume (*) and let b be a 
set such that (i) (∃u)(u ∈ b) and (ii) (∀y)(y ∈ b ⇒ (∃z)(z ∈ b ∧ y ⊂ z)). Let 
d = {u|(∃z)(z ∈ b ∧ u ⊆ z)}. Since d ⊆ P  ( ⋃ (b), d is a set. Define a relation 
R = {〈n, v〉|n ∈ ω ∧ v = {u|u ∈ d ∧ u ≅ n}}. Thus, 〈n, v〉 ∈ R is and only 
if n ∈ ω and v consists of all elements of d that are equinumerous with n. 
R is a one–one function with domain ω and range a subset of P (d). Hence, 
by the replacement axiom applied to R−1, ω is a set and, therefore, axiom I 
holds.
4.62	
a.	 Induction on α in (∀x)(x ≅ α ∧ α ∈ ω ⇒ Fin(P(x))).
	
b.	 Induction on α in (∀ x)(x ≅ α ∧ α ∈ ω ∧ (∀ y)(y ∈ x ⇒ Fin(y)) ⇒ Fin(⋃ x)).
	
c.	 Use Proposition 4.27(a).
	
d.	 x ⊆ P  (⋃ x) and y ∈ x ⇒ y ⊆ ⋃ x.
	
e.	 Induction on α in (∀x)(x ≅ α ∧ α ∈ ω ⇒ (x ≼ y ∨ y ≼ x))
	
g.	 Induction on α in (∀x)(x ≅ α ∧ α ∈ ω ∧ Inf(Y) ⇒ x ≼ y)
	
h.	 Use Proposition 4.26(c).
	
j.	
xy ⊆ P (y × x)
4.63	
Let Z be a set such that every non-empty set of subsets of Z has a mini-
mal element. Assume Inf(Z). Let Y be the set of all infinite subsets of Z. 
Then Y is a non-empty set of subsets of Z without a minimal element. 
Conversely, prove by induction that, for all α in ω, any non-empty sub-
set of P (α) has a minimal element. The result then carries over to non-
empty subsets of P (z), where z is any finite set.



441
Answers to Selected Exercises
4.64	
a.	 Induction on α in (∀x)(x ≅ α ∧ α ∈ ω ∧ Den(y) ⇒ Den(x ∪ y)).
		
b.	 Induction on α in (∀ x)(x ≅ α ∧ x ≠ ∅ ∧ Den(y)⇒Den(x × y))
		
c.	 Assume z ⊆ x and Den(z). Let z
f≅ω. Define a function g on x as fol-
lows: g′u = u if u
x
z g u
f
f u
∈
= (
) (
)
(
)
−
′
′
′
′
;
⌣
 if u ∈ z. Assume x is 
Dedekind-infinite. Assume z ⊂ x and x
z
f≅. Let v ∈ x − z. Define a 
function h on ω such that h′∅ = v and h‘(α‘) = f‘(h‘α) if α ∈ ω. Then h 
is one–one. So, Den (h′′ω) and h′′ω ⊆ x.
	
f.	
Assume y ∉ x. (i) Assume x ∪ {y} ≅ x. Define by induction a function g 
on ω such that ɡ′∅ = y and ɡ′(n + 1) = f′(ɡ′n). ɡ is a one–one func-
tion from ω into x. Hence, x contains a denumerable subset and, by 
part (c), x is Dedekind-infinite. (ii) Assume x is Dedekind-infinite. 
Then, by part (c), there is a denumerable subset z of x. Assume 
z
f≅ω. Let c0 = (f −1)′∅. Define a function F as follows: F′u = u for 
u ∈ x − z; F′c0 = y; F′u = (f −1)′(f′u−1) for u ∈ z − {c0}. Then x
x
y
F≅
∪{ }. 
If z is {c0, c1, c2, …}, F takes ci+1 into ci and moves c0 into y.
	
g.	 Assume ω ≼ x. By part (c), x is Dedekind-infinite. Choose y ∉ x. By 
part (f), x ≅ x ∪ {y}. Hence, x +c 1 = (x × {∅}) ∪ {〈∅, 1〉} ≅ x ∪ {y} ≅ x.
4.65	
Assume M is a model of NBG with denumerable domain D. Let d be 
the element of D satisfying the wf x = 2ω. Hence, d satisfies the wf ¬(x ≅ ω). 
This means that there is no object in D that satisfies the condition of 
being a one–one correspondence between d and ω. Since D is denu-
merable, there is a one–one correspondence between the set of “ele-
ments” of d (that is, the set of objects c in D such that ⊧M c ∈ d) and the 
set of natural numbers. However, no such one–one correspondence 
exists within M.
4.68	
NBG is finitely axiomatizable and has only the binary predicate letter 
A2
2. The argument on pages 273–274 shows that NBG is recursively 
undecidable. Hence, by Proposition 3.49, the predicate calculus with 
A2
2 as its only non-logical constant is recursively undecidable.
4.69	
a.	 Assume x ≼ ωα. If 2 ≼ x, then, by Propositions 4.37(b) and 4.40, 
ωα ≼ x ∪ ωα ≼ x × ωα ≼ ωα × ωα ≅ ωα. If x contains one element, use 
Exercise 4.64(c, f).
	
b.	 Use Corollary 4.41.
4.70	
a.	 P  (ωα ) × P  (ωα ) ≅ 2ωα × 2ωα ≅ 2ωα +cωα ≅ 2ωα ≅ P(ωα)
	
b.	
P
P
ω
ω
α
ω
ω
ω
α
α
α
α
(
)
(
) ≅(
) ≅
≅
≅
(
)
×
x
x
x
2
2
2
4.71	
a.	 If y were non-empty and finite, y ≅ y +c y would contradict Exercise 
4.62(b).
	
b.	 By part (c), let y = u ∪ v, u ∩ v = ∅, u ≅ y, v ≅ y. Let y
v
f≅. Define a func-
tion ɡ on P(y) as follows: for x ⊆ y, let ɡ′x = u ∪ (f″x). Then ɡ′x ⊆ y and 
y ≅ u ≼ ɡ′x ≼ y. Hence, ɡ′x ≅ y. So, ɡ is a one–one function from P  (y) 
into A = {z|z ⊆ y ∧ z ≅ y}. Thus, P (y) ≼ A. Since A ⊆ P (y), A ≼ P  (y).



442
Answers to Selected Exercises
	
e.	 Use part (d): {z|z ⊆ y ∧ z ≅ y} ⊆ {z|z ⊆ y ∧ Inf(z)}.
	
f.	
By part (c), let y = u ∪ v, u ∩ v = ∅, u ≅ y, v ≅ y. Let u ≅ fv. Define f 
on y as follows: f′x = h′x if x ∈ u and f′x = (h−1)′x if x ∈ v.
4.72	
a.	 Use Proposition 4.37(b).
	
b.	 i.	 Perm y
y
y
y
y
y
y y
y
( ) ⊆
(
) ≅
≅
≅
( )
×
⪯2
2
2
P
.
	
	
ii.	 By part (a), we may use Exercise 4.7 (c). Let y = u ∪ v, u ∩ v = 
∅, u ≅ y, v ≅ y. Let u
v
H≅
 and y
u
G≅. Define a function F: P(y) → 
Perm(y) in the following way: assume z ∈ P(y). Let ψz: y → y be 
defined as follows: ψz′x = H′x if x ∈ G″z; ψz′x = (H−1′x if (H−1′x ∈ 
G″z;  ψz′x = x otherwise. Then ψz ∈ Perm(y). Let F′z = ψz. F is 
one–one. Hence, P(y) ≼ Perm(y).
4.73	
a.	 Use WO and Proposition 4.19.
	
b.	 The proof of Zorn ⇒ WO in Proposition 4.42 uses only this special 
case of Zorn’s Lemma.
	
c.	 To prove the Hausdorff maximal principal (HMP) from Zorn, 
consider some ⊂-chain C0 in x. Let y be the set of all ⊂-chains C 
in x such that C0 ⊆ C and apply part (b) to y. Conversely, assume 
HMP. To prove part (b), assume that the union of each nonempty 
⊂ -chain in a given non-empty set x is also in x. By HMP applied to 
the ⊂ -chain ∅, there is some maximal ⊂ -chain C in x. Then ⋃ (C) 
is an ⊂ -maximal element of x.
	
d.	 Assume the Teichmüller–Tukey lemma (TT). To prove part (b), 
assume that the union of each non-empty ⊂ -chain in a given non-
empty set x is also in x. Let y be the set of all ⊂ -chains in x. y is 
easily seen to be a set of finite character. Therefore, y contains a 
⊂-maximal element C. Then ∪ (C) is a ⊂ -maximal element of x. 
Conversely, let x be any set of finite character. In order to prove TT 
by means of part (b), we must show that, if C is a ⊂ -chain in x, then 
∪ (C) ∈ x. By the finite character of x, it suffices to show that every 
finite subset z of ∪ (C) is in x. Now, since z is finite, z is a subset of 
the union of a finite subset W of C. Since C is a ⊂ -chain, W has a 
⊂-greatest element w ∈ x, and z is a subset of w. Since x is of finite 
character, z ∈ x.
	
e.	 Assume Rel(x). Let u = {z|(∃v)(v ∈ D(x) ∧ z = {v} x}; that is, z ∈ 
u if z is the set of all ordered pairs 〈v, w〉 in x, for some fixed v. 
Apply the multiplicative axiom to u. The resulting choice set 
y ⊆ x is a function with domain D(x). Conversely, the given 
property easily yields the multiplicative axiom. If x is a set of 
disjoint non-empty sets, let r be the set of all ordered pairs 〈u, v〉 
such that u ∈ x and v ∈ u. Hence, there is a function f ⊆ r such 
that D(f) = D(r) = x. The range R(f) is the required choice set 
for x.



443
Answers to Selected Exercises
	
f.	
By trichotomy, either x ≼ y or y ≼ x. If x ≼ y, there is a function with 
domain y and range x. (Assume x
y
y
f≅
⊆
1
.) Take c ∈ x. Define ɡ′u = c 
if u ∈ y − y1, and ɡ′u = (f−1′u  if  u ∈ y1.) Similarly, if y ≼ x, there is 
a function with domain x and range y. Conversely, to prove WO, 
apply the assumption (f) to x and H  ′(P (x)). Note that, if (∃f)(f:u→v ∧ 
R(f) = v), then P (v) ≼ P (u). Therefore, if there were a function f from 
x onto H  ′(P  (x)), we would have H
P
P H
P
P
′
( )
(
)
′
( )
(
)
(
)
( )
x
x
x
≺
≺
 
contradicting the definition of H  ′(P (x)). Hence, there is a function 
from H  ′(P (x)) onto x. Since H  ′(P (x)) is an ordinal, one can define 
a one–one function from x into H  ′(P (x)). Thus x ≺ H  ′(P (x)) and, 
therefore, x can be well-ordered.
4.76	
If < is a partial ordering of x, use Zorn’s lemma to obtain a maximal 
partial ordering <* of x with < ⊆ <*. But a maximal partial ordering 
must be a total ordering. (If u, v were distinct elements of x unrelated 
by <*, we could add to <* all pairs 〈u1, v1〉 such that u1 ≤* u and v ≤* v1. 
The new relation would be a partial ordering properly containing <*.)
4.79	
b.	 Since x × y ≅ x +cy, x × y = a ∪ b with a ∩ b = ∅, a ≅ x, b ≅ y. Let r be 
a well-ordering of y. (i) Assume there exists u in x such that 〈u, v〉 
∈ a for all v in y. Then y ≼ a. Since a ≅ x, y ≼ x, contradicting ¬(y ≼ x). 
Hence, (ii) for any u in x, there exists v in y such that 〈u, v〉 ∈ b. 
Define f: x → b such that f′u = 〈u, v〉, where v is the r-least element 
of y such that 〈u, v〉 ∈ b. Since f is one–one, x ≼ b ≅ y.
	
c.	 Clearly Inf(z) and Inf(x +c z). Then x +c z ≅ (x +c z)2 ≅ x2 +c 2 × 
(x × z) +c z2 ≅ x +c 2 × (x × z) +c z
	
	
Therefore, x × z ≼ 2 × (x × z) ≼ x +c 2 × (x × z) +c z ≅ x +c z. Conversely, 
x +c z ≼ x × z by Proposition 4.37(b).
	
d.	 If AC holds, (∀y)(Inf(y) ⇒ y ≅ y × y) follows from Proposition 4.40 
and Exercise 4.73(a). Conversely, if we assume y ≅ y × y for all 
infinite y, then, by parts (c) and (b), it follows that x ≼ H ′ x for any 
infinite set x. Since H ′x is an ordinal, x can be well-ordered. Thus, 
WO holds.
4.81	
a.	 Let 〈 be a well-ordering of the range of r. Let f′∅ be the 〈-least ele-
ment of R (r), and let f′n be the 〈-least element of those v in R (r) 
such that 〈 f′n, v〉 ∈r.
	
b.	 Assume Den(x) ∧ (∀ u)(u ∈ x ⇒ u ≠ ∅). Let ω≅
g x. Let r be the set of 
all pairs 〈a, b〉 such that a and b are finite sequences 〈v0, v1, …, vn〉 
and 〈v0, v1, …, vn + 1〉 such that, for 0 ≤ i ≤ n + 1, vi ∈ ɡ′i. Since R (r) ⊆ 
D (r), PDC produces a function h: ω → D (r) such that 〈h′n, h′(n′)〉 ∈ r 
for all n in ω. Define the choice function f by taking, for each u in 
x, f′u to be the (ɡ′u) th component of the sequence h′ (ɡ′u).
	
c.	 Assume PDC and Inf(x). Let r consist of all ordered pairs 〈u, u ∪ {a}〉, 
where u ∪ {a} ⊆ x,Fin(u ∪ {a}), and a ∉ u. By PDC, there is a function 



444
Answers to Selected Exercises
f: ω → D(r) such that 〈 f′n,f′(n′)〉 ∈ r for all n in ω. Define g: ω → x 
by setting g′n equal to the unique element of f′(n′) − f′n. Then ɡ is 
one–one, and so, ω ≼ x.
	
d.	 In the proof of Proposition 4.44(b), instead of using the choice 
function h, apply PDC to obtain the function f. As the relation r, 
use the set of all pairs 〈u, v〉 such that u ∈ c, v ∈ c, v ∈ u ∩ X.
4.82	
a.	 Use transfinite induction.
	
d.	 Use induction on β.
	
(e)–(f) Use transfinite induction and part (a).
	
h.	 Assume u ⊆ H. Let v be the set of ranks ρ′x of elements x in u. Let 
β = ∪ v. Then u ⊆ Ψ′ β. Hence u ∈ P (Ψ′β) = Ψ′(β) ⊆ H.
4.83	
Assume X ≠ ∅ ∧  ¬ (∃y)(y ∈ X ∧ y ∩ X = ∅). Choose u ∈ X. Define a 
function ɡ such  that ɡ′ ∅ = u ∩ X, ɡ′(n′) = ∪ (ɡ′n) ∩ X. Let x = ∪ (R(ɡ)). 
Then x ≠ ∅ and (∀ y)(y ∈ x ⇒ y ∩ x ≠ ∅).
4.88	
Hint: Assume that the other axioms of NBG are consistent and that the 
Axiom of Infinity is provable from them. Show that Hω is a model for 
the other axioms but not for the Axiom of Infinity.
4.89	
Use Hω
ω
+°
4.95	
a.	 Let C = {x|¬(∃y)(x ∈ y ∧ y ∈ x)}.
Chapter 5
5.1	
q0|Bq0
	
q0BRq1
	
q1||q0
	
q1BRq2
5.2	
a.	U2
3  b. δ(x)
5.7	
Let a Turing machine F  compute the function f. Replace all occur-
rences of q0 in the quadruples of F  by a new internal state qr. Then 
add the quadruples q0 ai ai qr for all symbols ai of the alphabet of F. 
The Turing machine defined by the enlarged set of quadruples also 
computes the function f.
5.8	
ρ finds the first non-blank square to the right of the initially scanned 
square and then stops; if there is no such square, it keeps moving to 
the right forever. λ’s behavior is similar to that of ρ, except that it moves 
to the left.
5.10	
a. N(x) = x + 1  b. f(x) = 1 for all x  c. 2x



445
Answers to Selected Exercises
5.12	
a.	
(K2)2 1a01
K3C
ra0r
1
0
C
0
1
5.14	
a. The empty function  b. N (x) = x + 1  c. Z(x)
5.16	
If f(a1) = b1, …, f(an) = bn, then
	
f x
y
x
a
y
b
x
a
y
b
n
n
( )
(
)
(
)
=
=
∧
=
∨
∨
=
∧
=


µ
1
1

5.20	
Let ɡ(z, x) = U(μyT1(z, x, y)) and use Corollary 5.11. Let v0 be a number 
such that ɡ(x, x) + 1 = ɡ(v0, x). Then, if ɡ(v0, v0) is defined, ɡ(v0, v0) + 1 = 
ɡ(v0, v0), which is impossible.
5.21	
g x
x
h
x
x
C
x
x
n
n
R
n
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
…
(
) =
…
(
)⋅
…
(
)
(
) +
+
sg

	
h x
x
C
x
x
k
n
R
n
k
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
…
⋅
…
(
)
sg
5.22	
a.	 Assume that h(x) is a recursive function such that h(x) = μyT1(x, x, y) 
for every x in the domain of μyT1(x, x, y). Then (∃y)T1(x, x, y) if and 
only if T1(x, x, h(x)). Since T1(x, x, h(x)) is a recursive relation, this 
contradicts Corollary 5.13(a).
	
b.	 Use Exercise 5.21.
	
c.	 Z(μyT1(x, x, y)) is recursively completable, but its domain is {x|(∃y)
T1(x, x, y)}, which, by Corollary 5.13(a), is not recursive.
5.29	
Let T     be a Turing machine with a recursively unsolvable halting prob-
lem. Let ak be a symbol not in the alphabet of T. Let qr be an internal 
state symbol that does not occur in the quadruples of T. For each qi 
of T  and aj of T, if no quadruple of T  begins with qi aj, then add the 
quadruple qi aj ak qr. Call the new Turing machine T*. Then, for any 
initial tape description α of T, T  *, begun on α, prints ak if and only if 
T   is applicable to α. Hence, if the printing problem for T  * and ak were 
recursively solvable, then the halting problem for T  would be recur-
sively solvable.
5.31	
Let T     be a Turing machine with a recursively unsolvable halting prob-
lem. For any initial tape description α for T,   construct a Turing machine 
Tα that does the following: for any initial tape description β, start T  on 
α; if T   stops, erase the result and then start T  on β. It is easy to check 
that T  is applicable to α if and only if Tα has a recursively unsolvable 
halting problem. It is very tedious to show how to construct Tα and to 
prove that the Gödel number of Tα is a recursive function of the Gödel 
number of α.



446
Answers to Selected Exercises
5.33	
Let v0 be the index of a partial recursive function G(x) with non-empty 
domain. If the given decision problem were recursively solvable, so 
would be the decision problem of Example 1 on page 340.
5.34	 By Corollary 5.16, there is a recursive function ɡ(u) such that 
ϕ
µ
g u
x
x
yT u u y
( ) ( ) =
⋅
(
)
1
1
, ,
. Then ϕg u
( )
1
 has an empty domain if and 
only if ¬(∃y)T1(u, u, y). But, ¬(∃y)T1(u, u, y) is not recursive by 
Corollary 5.13(a).
5.39	
a.	 By Corollary 5.16, there is a recursive function ɡ(u) such that 
ϕ
µ
g u
x
y x
u
y
x
( ) ( ) =
=
∧
=
(
)
1
. The domain of ϕg u
( )
1
 is {u}. Apply the 
fixed-point theorem to ɡ.
	
b.	 There is a recursive function g(u) such that ϕ
µ
g u
x
y x u y
( ) ( )=
≠∧
=
(
)
1
0 . 
Apply the fixed-point theorem to ɡ.
5.42	
a.	 Let A = {x|f(x) ∈ B}. By Proposition 5.21(c), B is the domain of a 
partial recursive function ɡ. Then A is the domain of the composi-
tion ɡ ⚬ f. Since ɡ ⚬ f is partial recursive by substitution, A is r.e. by 
Proposition 5.21(c).
	
b.	 Let B be a recursive set and let D be the inverse image of B under 
a recursive function f. Then x ∈ D if and only if CB(f(x)) = 0, and 
CB(f(x)) = 0 is a recursive relation.
	
c.	 Let B be an r.e. set and let A be the image {f(x)|x ∈ B} under a partial 
recursive function f. If B is empty, so is A. If B is nonempty, then B is 
the range of a recursive function ɡ. Then A is the range of the partial 
recursive function f(ɡ(x)) and, by Proposition 5.21(b), A is r.e.
	
d.	 Consider part (b). Given any natural number x, compute the value 
f(x) and determine whether f(x) is in B. This is an effective pro-
cedure for determining membership in the inverse image of B. 
Hence, by Church’s thesis, B is recursive.
	
e.	 Any non-empty r.e. set that is not recursive (such as that of 
Proposition 5.21(e)) is the range of a recursive function ɡ and is, 
therefore, the image of the recursive set ω of all natural numbers 
under the function ɡ.
5.43	
The proof has two parts:
	
1.	 Let A be an infinite recursive set. Let ɡ(i) = μx(x ∈ A ∧ (∀j)j<i (x ≠ ɡ(j)). 
Then ɡ(i) = h(i, ɡ#(i)), where h(i, u) = μx(x ∈ A ∧ (∀j)j < i (x ≠ (u)j)). 
h is recursive, and ɡ is recursive by Preposition 3.20. ɡ is strictly 
increasing and its range is A. (This proof is due to Gordon 
McLean, Jr.)
	
2.	 Let A be the range of a strictly increasing recursive function ɡ. 
Then ɡ(x) ≥ x for all x (by the special case of Proposition 4.15). 
Hence, x ∈ A if and only if (∃u)u≤xɡ(u) = x. So, A is recursive by 
Proposition 3.18.



447
Answers to Selected Exercises
5.44	
Assume A is an infinite r.e. set. Let A be the range of the recursive 
function ɡ(x). Define the function f by the following course-of-values 
recursion:
	
f n
y
z
y
f z
y
z
y
f
n
z n
z n
z
( ) =
∀
(
)
( ) ≠
( )
(
)
(
) =
∀
(
)
( ) ≠
( )
(
)
(
)
(
)
<
<
g
g
g
g
µ
µ
#
	
Then A is the range of f, f is one–one, and f is recursive by Propositions 
3.18 and 3.20. Intuitively, f(0) = ɡ(0) and, for n > 0, f(n) = ɡ(y), where y is 
the least number for which ɡ(y) is different from f(0), f(1), …, f(n − 1).
5.45	
Let A be an infinite r.e. set, and let A be the range of the recursive 
function ɡ. Since A is infinite, F(u) = μy(ɡ(y) > u) is a recursive func-
tion. Define G(0) = ɡ(0), G(n + 1) = ɡ(μy(ɡ(y) > G(n))) = ɡ(F(G(n))). G is 
a strictly increasing recursive function whose range is infinite and 
included in A. By Exercise 5.43, the range of G is an infinite recursive 
subset of A.
5.46	
a. By Corollary 5.16, there is a recursive function ɡ(u, v) such that
	
ϕ
µ
g u v
x
y T u x y
T v x y
,
, ,
, ,
.
(
) ( ) =
(
)∨
(
)
(
)
1
1
1
5.47	
Assume (∇). Let f(x1, …, xn) be effectively computable. Then the set 
B = {u|f((u)1, …, (u)n) = (u)n+1} is effectively enumerable and, there-
fore, by (∇), r.e. Hence, u ∈ B ⇔ (∃y)R(u, y) for some recursive rela-
tion R. Then
	f x
x
v
v
x
v
x
R
v
v
n
n
n
(
,
,
)
( )
( )
( ) ,( )
1
0 1
1
0
0
1
0
…
=
(
) =
∧… ∧(
) =
∧
(
)
(
)


(
)
µ
n+1
	
So, f is recursive. Conversely, assume Church’s thesis and let W be an 
effectively enumerable set. If W is empty, then W is r.e. If W is non-
empty, let W be the range of the effectively computable function ɡ. By 
Church’s thesis, ɡ is recursive. But, x ∈ W ⇔ (∃u)(ɡ(u) = x). Hence, W is 
r.e. by Proposition 5.21(a).
5.48	
Assume A is r.e. Since A ≠ ∅, A is the range of a recursive function ɡ(z). 
So, for each z, U(μyT1(ɡ(z), x, y)) is total and, therefore, recursive. Hence, 
U(μyT1(ɡ(x), x, y)) + 1 is recursive. Then there must be a number z0 such 
that U(μyT1(ɡ(x), x, y)) + 1 is recursive. Then there must be a number 
z0 such that U(μyT1(ɡ(x), x, y)) + 1 = U(μyT1(ɡ(z0), x, y)). A contradiction 
results when x = z0.
5.49	
(a) Let φ(n) = n for all n.



448
Answers to Selected Exercises
5.50	
Let ϕ
σ
µ
σ
σ
σ
( )
,
( ),
( )
( )
z
y T z
y
y
y
z
=
(
) ∧
>


(
)
1
2
1
1
2
2
2
1
2
2
, and let B be the 
range of φ.
5.55	
b.	 Let A be r.e. Then x ∈ A ⇔ (∃y)R(x, y), where R is recursive. Let R(x, y) 
express R(x, y) in K. Then k
A
y
k y
∈
⇔
∃
(
)
(
)
⊢K
R
,
.
	
c.	 Assume k
A
k
∈
⇔
( )
⊢K A
 for all natural numbers k. Then k ∈ A ⇔ 
(∃y)BA(k, y) and BA is recursive (see the proof of Proposition 3.29 on 
page 201.
5.56	 a.	 Clearly TK is infinite. Let f(x) be a recursive function with range 
TK. Let B0, B1, … be the theorems of K, where Bj is the wf of K 
with Gödel number f (j). Let ɡ(x, y) be the recursive function such 
that, if x is the Gödel number of a wf C, then ɡ(x, j) is the Gödel 
number of the conjunction C ∧ C ∧ … ∧ C consisting of j conjuncts; 
and, otherwise, ɡ(x, j)=0. Then ɡ( f(j), j) is the Gödel number of 
the j-fold conjunction Bj ∧ Bj ∧ … ∧ Bj. Let K′ be the theory whose 
axioms are all these j-fold conjunctions, for j = 0, 1, 2, … Then K′ 
and K have the same theorems. Moreover, the set of axioms of K′ 
is recursive. In fact, x is the Gödel number of an axiom of K′ if 
and only if x ≠ 0 ∧ (∃y)y≤x(ɡ(f(y), y) = x). From an intuitive stand-
point using Church’s thesis, we observe that, given any wf A, one 
can decide whether A is a conjunction C ∧ C ∧ … ∧ C; if it is such 
a conjunction, one can determine the number j of conjuncts and 
check whether C  is Bj.
	
b.	 Part (b) follows from part (a).
5.58	
a.	 Assume B(x1) weakly expresses (
)
TK * in K. Then, for any n, 
⊢K B n
( ) if and only if n
T
∈(
)
K *.  Let p be the Gödel number of 
B(x1). Then ⊢K B p
( ) if and only if p
T
∈(
)
K *. Hence, ⊢K B(p) if and 
only if the Gödel number of B(p) is in TK; that is, ⊢K B(p) if and only 
if not-⊢K B(p).
	
b.	 If K is recursively decidable, TK is recursive. Hence, TK is recursive 
and, by Exercise 5.57, (
)
TK * is recursive. So, (
)
TK * is weakly express-
ible in K, contradicting part (a).
	
c.	 Use part (b); every recursive set is expressible, and, therefore, 
weakly expressible, in every consistent extension of K.
5.59	
a.	 i.	
δ(x).
	
	
ii.	
x
x
1
2
−
	
	
iii.	 The function with empty domain.
	
	
iv.	 The doubling function.
	
b.	 i.	
f
x
x
1
2
1
1
0
(
, ) =
	
	
	
f
x
x
1
2
2
2
0
( ,
) =
	
	
	
f
x
x
f
x x
1
2
1
2
1
2
1
2
(
) ,(
)
(
,
)
′
′
(
) =



449
Answers to Selected Exercises
	
	
ii.	
f
x
x
1
2
1
1
0
(
, ) =
	
	
	
f
x
x
f
x x
1
2
1
2
1
2
1
2
,(
)
(
,
)
′
(
) = (
)′
	
	
	
f
x
2
2
1 0
0
(
, ) =
	
	
	
f
x
x
f
f
x x
x
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
,(
)
(
,
),
′
(
) =
(
)
	
	
iii.	 f1
1 0
1
( ) =
	
	
	
f
x
1
1
1
0
(
)′
(
) =
	
	
	
f2
1 0
0
( ) =
	
	
	
f
x
f
f
x
2
1
1
1
1
2
1
1
(
)
(
)
′
(
) =
(
)
5.61	
a.	 Any word P is transformed into QP.
	
b.	 Any word P in A is transformed into PQ.
	
c.	 Any word P in A is transformed into Q.
	
d.	 Any word P in A is transformed into n, where n is the number of 
symbols in P.
5.62	
a.	 α ξ → · Λ (ξ in A)
	
	
α → · Λ
	
	
Λ → α
	
b.	 α ξ → ξ α (ξ in A)
	
	
ξ α → · Λ (ξ in A)
	
	
α → · Λ
	
	
Λ → α
	
c.	 ξ → Λ (ξ in A)
	
	
α α → · Λ
	
	
Λ → · α
	
d.	 ξ η β → η β ξ (ξ, η in A)
	
	
α ξ → ξ β ξ α (ξ in A)
	
	
β → γ
	
	
γ → Λ
	
	
α → · Λ
	
	
Λ → α
5.63	
α ai → Qi α (i = 1, …, k)
	
α ξ → ξ α (ξ in A − {a1, …, ak})
	
α → · Λ
	
Λ → α



450
Answers to Selected Exercises
5.64	
d.	 | B|→ B
	
	
B →|
	
e.	 |B|→ |
	
f
Let
,
and
be new symbols.
B
.
|
|
|
|
α β
δ
β
β
α
βα
α
Λ
δ
δα
δ
δ
δ
δ
δ
β
→
→
→
→
→
→
→
→
→
→


δ



451
Bibliography
Listed here are not only books and papers mentioned in the text but also 
some other material that will be helpful in a further study of mathematical 
logic. We shall use the following abbreviations:
AML	
for Annals of Mathematical Logic
AMS	
for American Mathematical Society
Arch.	
for Archiv für mathematische Logik und Grundlagenforschung
FM	
for Fundamenta Mathematicae
HML	
for Handbook of Mathematical Logic, Springer-Verlag
HPL	
for Handbook of Philosophical Logic, Reidel
JSL	
for Journal of Symbolic Logic
MTL	
for Model-Theoretic Logics, Springer-Verlag
NDJFL	 for Notre Dame Journal of Formal Logic
NH	
for North-Holland Publishing Company
ZML	
for Zeitschrift für mathematische Logik und Grundlagen der Mathematik 
(since 1993, Mathematical Logic Quarterly)
Ackermann, W. (1928) Zum Hilbertschen Aufbau der reellen Zahlen. Math. Ann., 99, 
118–133.
Ackermann, W. (1937) Die Widerspruchsfreiheit der allgemeinen Mengenlehre. 
Math. Ann., 114, 305–315.
Ackermann, W. (1940) Zur Widerspruchsfreiheit der Zahlentheorie. Math. Ann., 117, 
162–194.
Ackermann, W. (1954) Solvable Cases of the Decision Problem. North-Holland.
Andrews, P. (1965) Transfinite Type Theory with Type Variables. North-Holland.
Andrews, P. (1986) An Introduction to Mathematical Logic and Type Theory: To Truth 
through Proof. Academic.
Barwise, J. (1985) Model-theoretic logics: Background and aims. Model-Theoretic Logics 
(eds. J. Barwise and S. Feferman), Springer, pp. 3–23.
Baudisch, A., D. Seese, P. Tuschik, and M. Weese (1985) Decidability and Quantifier 
Elimination, MTL. Springer, pp. 235–268.
Beall, J. (ed.) (2008) The Revenge of the Liar. Oxford University Press.
Becker, O. (1930) Zur Logik der Modalitäten. Jahrbuch für Philosophie und 
Phänomenologische Forschung., 11, 497–548.
Behmann, H. (1992) Beiträge zur Algebra der Logik, insbesondere zum 
Entscheidungsproblem, Math. Ann., 86, 163–229.
Bell, J.L. (1977) Boolean-Valued Models and Independence Proofs in Set Theory. Oxford 
University Press.
Ben-Ari, M. (2012) Mathematical Logic for Computer Science. Springer Verlag.
Bergelson, V., A. Blass, M. Di Nasso, and R. Jin (2010) Ultrafilters across Mathematics, 
Vol. 530. Contemporary Mathematics.



452
Bibliography
Bernardi, C. (1975) The fixed-point theorem for diagonalizable algebras. Stud. Logica, 
34, 239–252.
Bernardi, C. (1976) The uniqueness of the fixed-point in every diagonalizable algebra. 
Stud. Logica, 35, 335–343.
Bernays, P. (1937–1954) A system of axiomatic set theory. I. JSL, 2, 65–77.
Bernays, P. (1941) A system of axiomatic set theory. II. JSL, 6, 1–17.
Bernays, P. (1942) A system of axiomatic set theory. III. JSL, 7, 65–89.
Bernays, P. (1942) A system of axiomatic set theory. IV. JSL, 7, 133–145.
Bernays, P. (1943) A system of axiomatic set theory. V. JSL, 8, 89–104.
Bernays, P. (1948) A system of axiomatic set theory. VI. JSL, 13, 65–79.
Bernays, P. (1954) A system of axiomatic set theory. VII. JSL, 19, 81–96.
Bernays, P. (1957) Review of Myhill (1955). JSL, 22, 73–76.
Bernays, P. (1961) Zur Frage der Unendlichkeitsschemata in der axiomatischen 
Mengenlehre. Essays on the Foundations of Mathematics, Jerusalem, Israel, pp. 3–49.
Bernays, P. (1976) On the problem of schemata of infinity in axiomatic set theory. Sets 
and Classes, North-Holland.
Bernstein, A.R. (1973) Non-standard analysis. in Studies in Model Theory, Mathematical 
Association of America, pp. 35–58.
Beth, E. (1951) A topological proof of the theorem of Löwenheim–Skolem–Gödel. 
Indag. Math., 13, 436–444.
Beth, E. (1953) Some consequences of the theorem of Löwenheim–Skolem–Gödel–
Malcev. Indag. Math., 15, 66–71.
Beth, E. (1959) The Foundations of Mathematics. North-Holland.
Bezboruah, A. and J.C. Shepherdson (1976) Gödel’s second incompleteness theorem 
for Q. JSL, 41, 503–512.
Black, R. (2000) Proving Church’s thesis. Philos. Math., 8, 244–258.
Bolc, L. and P. Borowik (1992) Many-Valued Logics. Vol. I: Theoretical Foundations, 
Springer.
Boolos, G. (1979) The Unprovability of Consistency: An Essay in Modal Logic. Cambridge 
University Press.
Boolos, G. (1984) Trees and finite satisfiability: Proof of a conjecture of Burgess. 
NDJFL, 25, 193–197.
Boolos, G. (1989) A new proof of the Gödel incompleteness theorem. Not AMS, 36, 
388–390.
Boolos, G. (1993) The Logic of Provability. Cambridge University Press.
Boolos, G.S., J.P. Burgess, and R.C. Richard (2007) Computability and Logic, 5th edn. 
Cambridge University Press.
Boone, W. (1959) The word problem. Ann. Math., 70, 207–265.
Bourbaki, N. (1947) Algèbre. Hermann, Paris, France, Book II, Chapter II.
Britton, J.L. (1963) The word problem. Ann. Math., 77, 16–32.
Brouwer, L.E.J. (1976) Collected Works. Vol. 1, Philosophy and Foundations of 
Mathematics. North-Holland.
Brunner, N. (1990) The Fraenkel–Mostowski method revisited. NDJFL, 31, 64–75.
Burali-Forti, C. (1897) Una Questione sui numeri transfinite. Rendiconti del Circolo 
Matematico di Palermo, 11, 154–165 and 260.
Calude, C., S. Marcus, and I. Tevy (1979) The first example of a recursive function 
which is not primitive recursive. Hist. Math., 6, 380–384.
Carnap, R. (1934) Die Logische Syntax der Sprache, Springer (English translation, The Logical 
Syntax of Language, Routledge & Kegan Paul, 1937; text edition, Humanities, 1964.).



453
Bibliography
Chaitin, G. (1992) Information-Theoretic Incompleteness. World Scientific.
Chang, C.C. and H.J. Keisler (1973) Model Theory, 2nd edn. North-Holland.
Chang, C.C. and H.J. Keisler (1990) Model Theory, 3rd edn. North-Holland.
Cherlin, G. (1976) Model Theoretic Algebra, Selected Topics. Springer.
Chimakinam, J.O. (2012) Proof in Alonzo Church’s and Alan Turing’s Mathematical Logic: 
Undecidability of First-Order Logic. Author House.
Ciesielski, K. (1997) Set Theory for the Working Mathematician. London Mathematical 
Society Student Texts.
Chuquai, R. (1972) Forcing for the impredicative theory of classes. JSL, 37, 1–18. 
Chuquai, R. (1981) Axiomatic Set Theory: Impredicative Theories of Classes. North-Holland.
Church, A. (1936a) A note on the Entscheidungsproblem. JSL, 1, 40–41; correction, JSL, 
101–102 (reprinted in Davis, 1965).
Church, A. (1936b) An unsolvable problem of elementary number theory. Am. J. 
Math., 58, 345–363 (reprinted in Davis, 1965).
Church, A. (1940) A formulation of the simple theory of types. JSL, 5, 56–68. 
Church, A. (1941) The Calculi of Lambda Conversion. Princeton University Press (second 
printing, 1951).
Church, A. (1956) Introduction to Mathematical Logic. I. Princeton University Press.
Chwistek, L. (1924–1925) The theory of constructive types. Ann. de la Soc. Polonaise de 
Math., 2, 9–48.
Chwistek, L. (1924–1925) The theory of constructive types. Ann. de la Soc. Polonaise de 
Math., 3, 92–141.
Cohen, P.J. (1963) A minimal model for set theory. Bull. Am. Math. Soc., 69, 537–540.
Cohen, P.J. (1963–1964) The independence of the continuum hypothesis. Proc. Natl. 
Acad. Sci. USA, 50, 1143–1148.
Cohen, P.J. (1963–1964) The independence of the continuum hypothesis. Proc. Natl. 
Acad. Sci. USA, 51, 105–110.
Cohen, P.J. 1966. Set Theory and the Continuum Hypothesis. Benjamin, Germany.
Collins, G.E. (1955) The modeling of Zermelo set theories in New Foundations, PhD 
thesis, Cornell, NY.
Cook, R.T. (2010) The Arché Papers on the Mathematics of Abstraction. Springer.
Cooper, S.B. (2004) Computability Theory. CRC Press.
Copeland, B.J. (ed.) (2004) Alan Mathison Turing: The Essential Turing. Oxford 
University Press.
Corcoran, J. (1980) Categoricity. Hist. Philos. Log., 1, 187–207.
Corcoran, J. (1987) Second-order logic, Proceedings Inference OUIC 86 (eds. D. Moates 
and R. Butrick), Ohio University Press, pp. 7–31.
Corcoran, J. (1998) Second-order Logic. Logic, Meaning and Computation: Essays in 
Memory of Alonzo Church (eds. C.A. Anderson and M. Zeleny), Kluwer.
Corcoran, J. (2006) Schemata: The concept of schema in the history of logic. Bull. Symb. 
Log., 12, 219–240.
Craig, W. (1953) On axiomatizability within a system. JSL, 18, 30–32.
Cucker, F., L. Blum, and M. Shub (1997) Complexity and Real Computation. Springer.
Curry, H. (1942) The inconsistency of certain formal logics. J. Symb. Log., 7, 115–117.
Curry, H.B. and R. Feys (1958) Combinatory Logic. I. North-Holland.
Curry, H.B., J.R. Hindley, and J. Seldin (1972) Combinatory Logic. II. North-Holland.
Davis, M. (1958) Computability and Unsolvability. McGraw-Hill (Dover, 1983).
Davis, M. (ed.) (1965) The Undecidable: Basic Papers on Undecidable Propositions, 
Unsolvable Problems, and Computable Functions. Raven Press.



454
Bibliography
Davis, M. (1973) Hilbert’s tenth problem is unsolvable. Am. Math. Mon., 80, 233–269.
Davis, M. (1977a) Applied Nonstandard Analysis. Wiley.
Davis, M. (1977b) Unsolvable problems. HML, 567–594.
Davis, M. (1982) Why Gödel didn’t have Church’s thesis. Inform. Control, 54, 3–24.
Davis, M., H. Putnam, and J. Robinson (1961) The decision problem for exponential 
Diophantine equations. Ann. Math., 74, 425–436.
de Bruijn, N.G. and P. Erdös (1951) A colour problem for infinite graphs and a prob-
lem in the theory of relations. Indag. Math., 13, 369–373.
Dedekind, R. (1901) Essays on the Theory of Numbers. Open Court (Dover, 1963).
Dekker, J.C.E. (1953) Two notes on recursively enumerable sets. Proc. AMS, 4, 495–501.
Dekker, J.C.E. (1955) Productive sets. Trans. AMS, 78, 129–149.
Dekker, J.C.E. and J. Myhill (1960) Recursive equivalence types. Univ. Calif. Publ. 
Math., 3, 67–213.
Denyer, N. (1991) Pure second-order logic. NDJFL, 33, 220–224.
Dershowitz, N. and Y. Gurevich. (2008) A natural axiomatization of computability 
and proof of Church’s thesis. Bull. Symb. Log., 14, 299–350.
Detlefsen, M. (2001) Pillars of computer science: Gödel’s 2nd theorem, Philos. Math., 
37–71.
Dreben, B. (1952) On the completeness of quantification theory. Proc. Natl. Acad. Sci. 
USA, 38, 1047–1052.
Dreben, B. and W.D. Goldfarb (1980) Decision Problems, Solvable Classes of Quantificational 
Formulas. Addison-Wesley.
Drucker, T. (ed.) (2008) Perspectives of the History of Mathematical Logic. Springer.
Dummett, M. (1977) Elements of Intuitionism. Oxford University Press.
Easton, W.B. (1970) Powers of regular cardinals. AML, 1, 139–178.
Ehrenfeucht, A. (1957) On theories categorical in power. FM, 44, 241–248.
Ehrenfeucht, A. (1958) Theories having at least continuum non-isomorphic models in 
each infinite power (abstract). Not. AMS, 5, 680.
Ehrenfeucht, A. and S. Feferman (1960) Representability of recursively enumerable 
sets in formal theories. Arch. fur Math. Logik und Grundlagenforschung, 5, 37–41.
Enayat, A. and R. Kossak (ed.) (2004) Nonstandard Models of Arithmetic and Set Theory. 
American Mathematical Society.
Engeler, E. (1968) Formal Languages: Automata and Structures. Markham.
Engeler, E. (1973) Introduction to the Theory of Computability. Academic.
Erdös, P. and A. Tarski (1961) On some problems involving inaccessible cardinals. 
Essays on the Foundations of Mathematics, Magnes, Jerusalem, Israel, pp. 50–82.
Ershov, Yu., I. Lavrov, A. Taimanov, and M. Taitslin (1965) Elementary theories. Russ. 
Math. Surv., 20, 35–105.
Evans, T. (1951) The word problem for abstract algebras. J. London Math. Soc., 26, 
64–71.
Feferman, S. (1957) Degrees of unsolvability associated with classes of formalized 
theories. JSL, 22, 165–175.
Feferman, S. (1960) Arithmetization of metamathematics in a general setting. FM, 49, 
35–92.
Feferman, S. (1962) Transfinite recursive progressions of axiomatic theories. JSL, 27, 
259–316.
Felgner, U. (1971a) Models of ZF-Set Theory. Springer.
Felgner, U. (1971b) Comparisons of the axioms of local and universal choice. FM, 71, 
43–62.



455
Bibliography
Felgner, U. (1976) Choice functions on sets and classes. Sets and Classes, North-
Holland, pp. 217–255.
Ferreiros, J. (2007) Labyrinth of Thought. A History of Set Theory and its Role in Modern 
Mathematics, 2nd edn. Birkhauser.
Fischer, P.C. (1965) On formalisms for Turing machines. J. Assoc. Comp. Mach., 12, 
570–580.
Fitting, M. (1983) Proof Methods for Modal and Intuitionistic Logics. Reidel.
Fitting, M. and R. Mendelsohn. (1998) First-Order Modal Logic. Kluwer.
Forster, T.E. (1983) Quine’s New Foundations (An Introduction), Cahiers du Centre de 
Logique 5, Université Catholique de Louvain.
Forster, T.E. (1992) Set Theory with a Universal Set: Exploring an Untyped Universe. 
Oxford University Press.
Fraenkel, A.A. (1922a) Zu den Grundlagen der Cantor-Zermeloschen Mengenlehre. 
Math. Ann., 86, 230–237.
Fraenkel, A.A. (1922b) Der Begriff ‘definit’ und die Unabhängigkeit des 
Auswahlaxioms. Sitzungsberichte der Preussischen Akademie der Wissenschaften, 
Physikalisch-mathematische Klasse, 253–257.
Fraenkel, A.A. (1928) Einleitung in die Mengenlehre, 3rd edn. Springer.
Fraenkel, A., Y. Bar-Hillel, and A. Lévy. (1973) Foundations of Set Theory. North-Holland 
(second revised edition).
Frayne, T., A. Morel, and D. Scott. 1956. Reduced direct products. FM, 51, 195–228.
Frege, G. (1893, 1903) Grundgesetze der Arithmetik, Begriffschriftlich Abgeleitet, Vols. 1–2. 
Jena (partial English translation in The Basic Laws of Arithmetic: Exposition of the 
System, University of California Press, 1964).
Gabriel, P. (1962) Des catégories abéliennes. Bull. de la Soc. Math. de France, 90, 
323–448.
Gandy, R. (1988) The confluence of ideas in 1936. The Universal Turing Machine—​
A Half-Century Survey (ed. R. Herken), Oxford University Press, pp. 55–111.
Garey, M.R. and D.S. Johnson. (1978) Computers and Intractability: A Guide to the Theory 
of NP-Completeness. Freeman.
Garland, S.J. (1974) Second-order cardinal characterizability. Axiomatic Set Theory, 
Proceedings   of the Symposia in Pure Mathematics, Vol. XIII, Part II. American 
Mathematical Society, pp. 127–146.
Gentzen, G. (1936) Die Widerspruchsfreiheit der reinen Zahlentheorie. Math. Ann., 
112, 493–565.
Gentzen, G. (1938) Neue Fassung des Widerspruchsfreiheitsbeweises für die reine 
Zahlentheorie. Forschungen zur Logik, 4, 5–18.
Gentzen, G. (1969) Collected Papers, (ed. M.E. Szabo), North-Holland.
George, A. and D.J. Velleman. (2001) Philosophies of Mathematics. Wiley-Blackwell.
Gillies, D.A. (1982) Frege, Dedekind, and Peano on the Foundations of Arithmetic. 
Van Gorcum.
Gillies, D.A. (1992) The Fregean revolution in logic. Revolutions in Mathematics (ed. 
D.A. Gillies), Oxford University Press, pp. 265–305.
Gödel, K. (1930) Die Vollständigkeit der Axiome des logischen Funktionenkalküls, 
Monatsh. Math. Phys., 37, 349–360 (English translation in Van Heijenoort, 1967, 
582–591).
Gödel, K. (1931) Ueber formal unentscheidbare Sätze der Principia Mathematica und 
verwandter Systeme. I. Monatsh. Math. Phys., 38, 173–198 (English translation in 
Davis, 1965).



456
Bibliography
Gödel, K. (1933) Zum intuitionistischen Aussagenkalkül; Zur intuitionistischen 
Arithmetik und Zahlentheorie. Ergeb. Math. Koll., 4, 34–38 and 40 (translation 
in Davis, 1965).
Gödel, K. (1934) On undecidable propositions of formal mathematical systems, 
Lecture Notes, Institute for Advanced Study, Princeton University Press, 
(reprinted in Davis, 1965, 39–73).
Gödel, K. (1938) The consistency of the axiom of choice and the generalized con-
tinuum hypothesis. Proc. Natl. Acad. Sci. USA, 24, 556–557.
Gödel, K. (1939) Consistency proof for the generalized continuum hypothesis. Proc. 
Natl. Acad. Sci. USA, 25, 220–226.
Gödel, K. (1940) The Consistency of the Axiom of Choice and the Generalized Continuum 
Hypothesis with the Axioms of Set Theory. Princeton University Press.
Gödel, K. (1947) What is Cantor’s continuum problem? Am. Math. Mon., 54, 515–525.
Gödel, K. (1986, 1990, 1995) Collected Works, Volume I, Publications 1929–1936; Volume 
II, Publications 1938–1974; Volume III, Unpublished Essays and Lectures, 
Oxford University Press.
Goldfarb, W. (1990) Herbrand’s theorem and the incompleteness of arithmetic. Iyyun: 
A Jerusalem Philos. Q., 39, 45–69.
Grelling, K. and L. Nelson. (1907/1908) Bemerkungen zu den Paradoxien von Russell 
und Burali-Forti. Abhandlungen der Fries’schen Schule N.F., 2, 301–324.
Hailperin, T. (1944) A set of axioms for logic. JSL, 9, 1–19.
Hailperin, T. (1953) Quantification theory and empty individual domains. JSL, 18, 
197–200.
Hajek, P. (1993) Metamathematics of First-Order Arithmetic. Springer.
Hajek, P. and P. Pudlak (1992) Metamathematics of First-Order Arithmetic. Springer.
Hale, B. and C. Wright. The Reason’s Proper Study: Essays Toward A Neo- Fregean 
Philosophy of Mathematics. Oxford University Press.
Hall, M., Jr. (1949) The word problem for semigroups with two generators. JSL, 14, 
115–118.
Halmos, P. (1960) Naive Set Theory. Van Nostrand (Springer, 1974).
Halmos, P. (1962) Algebraic Logic. Chelsea.
Halmos, P. (1963) Lectures on Boolean Algebra. Van Nostrand (Springer, 1977).
Halmos, P. and H. Vaughn (1950) The marriage problem. Am. J. Math., 72, 214–215.
Halpern, J.D. (1964) The independence of the axiom of choice from the Boolean prime 
ideal theorem. FM, 55, 57–66.
Halpern, J.D. and A. Lévy (1971) The Boolean prime ideal theorem does not imply the 
axiom of choice. Proc. Symp. Pure Math., 13 AMS, 83–134.
Hamkins, J.D. and A. Lewis. (2000) Infinite time Turing machines. J. Symb. Log., 65, 
567–604.
Hartmanis, J. (1989) Computational Complexity Theory. American Mathematical Society.
Hartogs, F. (1915) Über das Problem der Wohlordnung. Math. Ann., 76, 438–443.
Hasenjaeger, G. (1953) Eine Bemerkung zu Henkin’s Beweis für die Vollständigkeit 
des Prädikatenkalküls der ersten Stufe. JSL, 18, 42–48.
Hasenjaeger, G. and H. Scholz (1961) Grundzüge der mathematischen Logik. Springer.
Hatcher, W. (1982) The Logical Foundations of Mathematics. Pergamon.
Hellman, M. (1961) A short proof of an equivalent form of the Schröder–Bernstein 
theorem. Am. Math. Mon., 68, 770.
Henkin, L. (1949) The completeness of the first-order functional calculus. JSL, 14, 
159–166.



457
Bibliography
Henkin, L. (1950) Completeness in the theory of types. JSL, 15, 81–91.
Henkin (1955) On a theorem of Vaught. JSL, 20, 92–93.
Henkin, L., J.D. Monk, and A. Tarski. (1971, 1985) Cylindric Algebras, Vol. I (1971), 
Vol. II (1985). North-Holland.
Herbrand, J. (1930) Recherches sur la théorie de la démonstration. Travaux de la Société 
des Sciences et des Lettres de Varsovie, III, 33, 33–160.
Herbrand, J. (1971) Logical Writings. Harvard University Press and Reidel.
Hermes, H. (1965) Enumerability, Decidability, Computability. Springer (second edition, 
1969).
Heyting, A. (1956) Intuitionism. North-Holland (third revised edition, 1971).
Higman, G. (1961) Subgroups of finitely presented groups. Proc. R. Soc., Series A, 262, 
455–475.
Hilbert, D. and W. Ackermann (1950) Principles of Mathematical Logic. Chelsea.
Hilbert, D. and P. Bernays (1934, 1939) Grundlagen der Mathematik, Vol. I (1934), Vol. II 
(1939). Springer (second edition, 1968, 1970).
Hintikka, J. (1955a) Form and content in quantification theory. Acta Philos. Fennica, 
11–55.
Hintikka, J. (1955b) Notes on the quantification theory. Comment. Phys.-Math., Soc. Sci. 
Fennica, 17, 1–13.
Hirohiko, K. (2010) The Modal Logic of Gödel Sentences. Springer.
Howard, P.E. (1973) Limitations on the Fraenkel–Mostowski method. JSL, 38, 
416–422.
Hrbacek, K. and T. Jech (1978) Introduction to Set Theory. Academic (third edition, CRC 
Press, 1999).
Hughes, G.E. and M.J. Creswell (1968) An Introduction to Modal Logic. Methuen.
Isbell, J. (1966) Structure of categories. Bull. AMS, 72, 619–655.
Jaśkowski, S. (1936) Recherches sur le système de la logique intuitioniste. Acta Sci. 
Ind., Paris, 393, 58–61.
Jech, T. (1973) The Axiom of Choice. North-Holland, (Dover, 2008). Set Theory. Academic 
(third edition, Springer, 2006).
Jech, T. (2010) Multiple Forcing. Cambridge University Press.
Jensen, R.B. (1968–1969) On the consistency of a slight (?) modification of Quine’s 
New Foundations. Synthese, 19, 250–263.
Jeroslow, R.G. (1971) Consistency statements in formal theories. FM, 72, 17–40. 
Jeroslow, R.G. (1972) On the encodings used in the arithmetization of mathematics, 
unpublished manuscript.
Jeroslow, R.G. (1973) Redundancies in the Hilbert–Bernays derivability conditions for 
Gödel’s second incompleteness theorem. JSL, 38, 359–367. 
Jeroslow, R.G. (1976) Consistency statements in formal theories. FM, 72, 17–40.
Jones, J. (1982) Universal Diophantine Equations. J. Symbolic Logic, 47, 549–571.
Joyal, A. and I. Moerdijk. (1995) Algebraic Set Theory. Cambridge University Press.
Kalmár, L. (1935) Über die Axiomatisierbarkeit des Aussagenkalküls. Acta Sci. Math., 
7, 222–243.
Kalmár, L. (1936) Zuruckführung des Entscheidungsproblems auf den Fall von 
Formeln mit einer einzigen binären Funktionsvariablen. Comp. Math., 4, 137–144.
Kamke, E. (1950) Theory of Sets. Dover.
Kanamori, A. (1994) The Higher Infinite. Springer.
Kanamori, A. (2003) The empty set, the singleton, and the ordered pair. Bull. Symb. 
Log., 9, 273–298.



458
Bibliography
Kanamori, A. (2008) Cohen and set theory. Bull. Symb. Log., 14, 351–378.
Kaye, R. (1991) Models of Peano Arithmetic. Oxford University Press.
Kaye, R. (1994) Automorphisms of First Order Structures. Oxford University Press.
Keisler, H.J. (1976) Elementary Calculus: An Approach Using Infinitesimals. Prindle, 
Weber & Schmidt (second edition, 1985).
Kelley, J. (1955) General Topology. Van Nostrand (Springer, 1975).
Kemeny, J. (1949) Type theory vs. set theory, PhD thesis, Princeton, NJ.
Kirby, L. and J. Paris (1977) Initial segments of models of Peano’s axioms, Proceedings 
of the Bierutowice Conference 1976, Lecture Notes in Mathematics, Springer, 
pp. 211–226.
Kirby, L. and J. Paris (1982) Accessible independence results for Peano arithmetic. 
Bull. London Math. Soc., 14, 285–293.
Kleene, S.C. (1936a) General recursive functions of natural numbers. Math. Ann., 112, 
727–742 (reprinted in Davis, 1965).
Kleene, S.C. (1936b) λ-definability and recursiveness. Duke Math. J., 2, 340–353.
Kleene, S.C. (1943) Recursive predicates and quantifiers, Transactions of the AMS, 53, 
41–73 (reprinted in Davis, 1965).
Kleene, S.C. (1952) Introduction to Metamathematics. Van Nostrand.
Kleene, S.C. (1955a) Hierarchies of number-theoretic predicates. Bull. AMS, 61, 
193–213.
Kleene, S.C. (1955b) Arithmetical predicates and function quantifiers. Trans. AMS, 79, 
312–340.
Kleene, S.C. and E.L. Post (1954) The upper semi-lattice of degrees of recursive 
unsolvability. Ann. Math., 59, 379–407.
Kleene, S.C. and R.E. Vesley (1965) The Foundations of Intuitionist Mathematics. 
North-Holland.
Koslow, A. (1992) A Structuralist Theory of Logic. Cambridge University Press.
Kossak, R. and J. Schmerl. (2006) The Structure of Models of Peano Arithmetic. Oxford 
University Press.
Kreisel, G. (1976) The continuum hypothesis and second-order set theory. J. Philos. 
Log., 5, 281–298.
Kreisel, G. and J.-L. Krivine (1967) Elements of Mathematical Logic. North-Holland.
Kripke, S. (1975) Outline of a theory of truth. J. Philos., 72, 690–716.
Krivine, J.-L. (1971) Introduction to Axiomatic Set Theory. Reidel.
Kruse, A.H. (1966) Grothendieck universes and the super-complete models of 
Shepherdson. Comp. Math., 17, 86–101.
Kunen, K. (1980) Set Theory: An Introduction to Independence Proofs. Elsevier.
Kuratowski, K. (1921) Sur la notion d’ordre dans la théorie des ensembles. FM, 
2, 161–171.
Lambek, J. (1961) How to program an infinite abacus. Can. Math. Bull., 4, 295–302; 
5, 297.
Langford, C.H. (1927) Some theorems on deducibility. Ann. Math., I, 28, 16–40; II, 
28, 459–471.
Leinster, T. (2014) Basic Category Theory. Cambridge University Press.
Leivant, D. (1994) Higher order logic. Handbook of Logic in Artificial Intelligence and 
Logic Programming, Vol. 2 (eds. D.M. Gabbay, C.J. Hogger, and J.A. Robinson), 
Clarendon Press, pp. 229–321.
Lévy, A. (1960) Axiom schemata of strong infinity. Pacific J. Math., 10, 223–238.



459
Bibliography
Lévy, A. (1965) The Fraenkel–Mostowski method for independence proofs in set 
theory, The Theory of Models, Proceedings of the 1963 International Symposium at 
Berkeley, North-Holland, pp. 221–228.
Lévy, A. (1978) Basic Set Theory. Springer.
Lewis, C.I. and C.H. Langford (1960) Symbolic Logic.  Dover (reprint of 1932 edition).
Lewis, H.R. (1979) Unsolvable Classes of Quantificational Formulas. Addison-Wesley.
Lindenbaum, A. and A. Mostowski (1938) Über die Unabhängigkeit des Auswahl-
axioms und einiger seiner Folgerungen. Comptes Rendus Sciences Varsovie, III, 
31, 27–32.
Lindström, P. (1969) On extensions of elementary logic. Theoria, 35, 1–11.
Lindstrom, P. (2003) Aspects of Incompleteness, 2nd edn. Association for Symbolic Logic.
Link, G. (2004) One Hundred Years of Russell’s Paradox: Mathematics, Logic, Philosophy. 
De Gruyter.
Löb, M.H. (1955) Solution of a problem of Leon Henkin. JSL, 20, 115–118.
Loś, J. (1954a) Sur la théorème de Gödel sur les theories indénombrables. Bull. de l’Acad. 
Polon. des Sci., III, 2, 319–320.
Loś, J. (1954b) On the existence of a linear order in a group. Bull. de l’Acad. Polon. des 
Sci., 21–23.
Loś, J. (1954c) On the categoricity in power of elementary deductive systems and 
some related problems. Coll. Math., 3, 58–62.
Loś, J. (1955a) The algebraic treatment of the methodology of elementary deductive 
systems. Stud. Log., 2, 151–212.
Loś, J. (1955b) Quelques remarques, théorèmes et problèmes sur les classes 
definissables d’algèbres. Mathematical Interpretations of Formal Systems, North-
Holland, pp. 98–113.
Löwenheim, L. (1915) Ueber Möglichkeiten im Relativkalkül. Math. Ann., 76, 447–470.
Luxemburg, W.A.J. (1962) Non-Standard Analysis. Caltech Bookstore, Pasadena, CA.
Luxemburg, W.A.J. (1969) Applications of Model Theory to Algebra, Analysis, and 
Probability. Holt, Rinehart and Winston. 
Luxemburg, W.A.J. (1973) What is non-standard analysis? Papers in the Foundations 
of Mathematics. Am. Math. Mon., 80(6), Part II, 38–67.
Machtey, M. and P. Young (1978) An Introduction to the General Theory of Algorithms. 
North-Holland.
MacLane, S. (1971) Categorical algebra and set-theoretic foundations, Proceedings of 
the Symposium of Pure Mathematics, AMS, XIII, Part I, pp. 231–240.
Maclaughlin, T. 1961. A muted variation on a theme of Mendelson. ZML, 17, 57–60.
Maddy, P. (2013) Defending the Axioms: On the Philosophical Foundations of Set Theory. 
Oxford University Press.
Magari, R. (1975) The diagonalizable algebras. Boll. Un. Mat. Ital., (4), 12, 117–125.
Malinowski, G. (1993) Many-Valued Logics. Oxford University Press.
Mancosu, P. (1997) From Brouwer to Hilbert: The Debate on the Foundations of Mathematics 
in the 1920s. Oxford University Press.
Mancosu, P. (2010) The Adventure of Reason: Interplay Between Philosophy of Mathematics 
and Mathematical Logic, 1900–1940. Oxford University Press.
Mancosu, P. (ed.) (2011) The Philosophy of Mathematical Practice. Oxford University 
Press.
Manzano, M. (1996) Extensions of First Order Logic. Cambridge University Press.
Margaris, A. (1967) First-Order Mathematical Logic. Blaisdell (Dover, 1990).



460
Bibliography
Markov, A.A. (1954) The Theory of Algorithms, Tr. Mat. Inst. Steklov, XLII (translation: 
Office of Technical Services, U.S. Department of Commerce, 1962).
Matiyasevich, Y. (1970) Enumerable sets are Diophantine. Doklady Akademii Nauk 
SSSR, 191, 279–282 (English translation, Soviet Math. Doklady, 1970, 354–357).
Matiyasevich, Y. (1993) Hilbert’s Tenth Problem. MIT Press.
McKenzie, R. and R.J. Thompson (1973) An elementary construction of unsolvable 
word problems in group theory. Word Problems (eds. W.W. Boone, F.B. Cannonito, 
and R.C. Lyndon), North-Holland.
McKinsey, J.C.C. and A. Tarski (1948) Some theorems about the sentential calculi of 
Lewis and Heyting. JSL, 13, 1–15.
Melzak, Z.A. (1961) An informal arithmetical approach to computability and compu-
tation. Can. Math. Bull., 4, 279–293.
Mendelson, E. (1956a) Some proofs of independence in axiomatic set theory. JSL, 21, 
291–303. 
Mendelson, E. (1956b) The independence of a weak axiom of choice. JSL, 350–366.
Mendelson, E. (1958) The axiom of Fundierung and the axiom of choice. Archiv für 
mathematische Logik und Grundlagenforschung, 4, 65–70.
Mendelson, E. (1961) On non-standard models of number theory. Essays on the 
Foundations of Mathematics, Magnes, Jerusalem, Israel, pp. 259–268.
Mendelson, E. (1961b) Fraenkel’s addition to the axioms of Zermelo. Essays on the 
Foundations of Mathematics, Magnes, Jerusalem, Israel, pp. 91–114.
Mendelson, E. (1970) Introduction to Boolean Algebra and Switching Circuits. Schaum, 
McGraw-Hill.
Mendelson, E. (1973) Number Systems and the Foundations of Analysis. Academic. 
(reprint Krieger, 1985).
Mendelson, E. (1980) Introduction to Set Theory. Krieger.
Mendelson, E. (1990) Second Thoughts about Church’s thesis and mathematical 
proofs. J. Philos., 225–233.
Meredith, C.A. (1953) Single axioms for the systems (C,N), (C,O) and (A,N) of the 
two-valued propositional calculus. J. Comp. Syst., 3, 155–164.
Monk, J.D. (1976) Mathematical Logic. Springer.
Montagna, F. (1979) On the diagonalizable algebra of Peano arithmetic. Boll. Un. Mat. 
Ital., 5, 16-B, 795–812.
Montague, R. (1961a) Semantic closure and non-finite axiomatizability. Infinitistic 
Methods, Pergamon, pp. 45–69.
Montague, R. and R.L. Vaught (1959) Natural models of set theories. FM, 47, 219–242.
Moore, G.H. (1980) Beyond first-order logic: The historical interplay between math-
ematical logic and set theory. Hist. Philos. Log., 1, 95–137.
Moore, G.H. (1982) Zermelo’s Axiom of Choice: Its Origin, Development and Influence. 
Springer.
Moore, G.H. (1988) The emergence of first-order logic. History and Philosophy of 
Modern Mathematics (eds. W. Aspray and P. Kitcher), University of Minnesota 
Press, pp. 95–135.
Morley, M. (1965) Categoricity in power. Trans. AMS, 114, 514–538.
Morse, A. (1965) A Theory of Sets. Academic.
Mostowski, A. (1939) Ueber die Unabhängigkeit des Wohlordnungsatzes vom 
Ordnungsprinzip. FM, 32, 201–252.
Mostowski, A. (1947) On definable sets of positive integers. FM, 34, 81–112.
Mostowski, A. (1948) On the principle of dependent choices. FM, 35, 127–130.



461
Bibliography
Mostowski, A. (1951a) Some impredicative definitions in the axiomatic set theory. 
FM, 37, 111–124 (also 38, 1952, 238).
Mostowski, A. (1951b) On the rules of proof in the pure functional calculus of the first 
order. JSL, 16, 107–111.
Murawski, R. (1998) Undefinability of truth. The problem of the priority: Tarski vs. 
Gödel. Hist. Philos. Log., 19, 153–160.
Murawski, R. (2010) Recursive Functions and Metamathematics: Problems of Completeness 
and Decidability, Gödel’s Theorems. Springer.
Myhill, J. (1955) Creative sets. ZML, 1, 97–108.
Nerode, A. (1993) Logic for Applications. Springer.
Neumann, J. von (1925) Eine Axiomatisierung der Mengenlehre. J. für Math., 154, 
219–240 (also 155, 128) (English translation in Van Heijenoort, 1967, 393–413).
Neumann, J. von (1928) Die Axiomatisierung der Mengenlehre. Math. Z., 27, 669–752.
Nicod, J.G. (1917) A reduction in the number of primitive propositions of logic. Proc. 
Camb. Philos. Soc., 19, 32–41.
Novak, I.L. (Gal, L.N.) (1951) A construction for models of consistent systems. FM, 
37, 87–110.
Novikov, P.S. (1955) On the algorithmic unsolvability of the word problem for group 
theory, Tr. Mat. Inst. Steklov, 44 (Amer. Math. Soc. Translations, Series 2, 9, 1–124).
Oberschelp, A. (1991) On pairs and tuples. ZML, 37, 55–56.
Oberschelp, W. (1958) Varianten von Turingmaschinen. Archiv für mathematische Logik 
und Grundlagenforschung, 4, 53–62.
Odifreddi, P. Classical Recursion Theory: The Theory of Functions and Sets of Natural 
Numbers. North-Holland, 1992.
Olszewski, A., J. Wolenski, and R. Janusz (eds.) (2006) Church’s Thesis after 70 Years. 
Ontos Verlag.
Olszewski, A., J. Wolenski, and R. Janusz (eds.) (2007) Church’s Thesis After 70 Years. 
Ontos Verlag.
Orey, S. (1956a) On ω-consistency and related properties. JSL, 21, 246–252.
Orey, S. (1956b) On the relative consistency of set theory. JSL, 280–290.
Parikh, R. (1971) Existence and feasibility in arithmetic. JSL, 36, 494–508.
Paris, J.B. (1972) On models of arithmetic, Conference in Mathematical Logic—London, 
1970, Springer, pp. 251–280.
Paris, J.B. (1978) Some independence results for Peano arithmetic. JSL, 43, 725–731.
Paris, J. and L. Harrington. (1977) A mathematical incompleteness in Peano arithme-
tic. HML (ed. J. Barwise), North-Holland, pp. 1133–1142.
Peano, G. (1891) Sul concetto di numero. Rivista di Math, 1, 87–102.
Péter, R. (1935) Konstruktion nichtrekursiver Funktionen. Math. Ann., 111, 42–60.
Péter, R. (1967) Recursive Functions. Academic.
Pincus, D. (1972) ZF consistency results by Fraenkel–Mostowski methods. JSL, 37, 
721–743.
Poizat, B. (2012) A Course in Model Theory: An Introduction to Contemporary Mathematical 
Logic. Springer.
Ponse, A., M. de Rijke, and Y. Venema. (1995) Modal Logic and Process Algebra, 
a Bisimulation Perspective. CSLI Publications.
Post, E.L. (1921) Introduction to a general theory of elementary propositions. Am. J. Math., 
43, 163–185.
Post, E.L. (1936) Finite combinatory process-formulation 1. JSL, 1, 103–105 (reprinted 
in Davis, 1965).



462
Bibliography
Post, E.L. (1941) The Tw-Valued Iterative Systems of Mathematical Logic. Princeton 
University Press.
Post, E.L. (1943) Formal reductions of the general combinatorial decision problem. 
Am. J. Math., 65, 197–215.
Post, E.L. (1944) Recursively enumerable sets of positive integers and their decision 
problems. Bull. AMS, 50, 284–316 (reprinted in Davis, 1965).
Post, E.L. (1947) Recursive unsolvability of a problem of Thue. JSL, 12, 1–11 (reprinted 
in Davis, 1965).
Post, E.L. (1994) Solvability, Provability, Definability: The Collected Works of Emil L. Post 
(ed. M. Davis), Birkhäuser.
Priest, G. (2001) An Introduction to Non-Classical Logic. Cambridge University Press.
Presburger, M. (1929) Ueber die Vollständigkeit eines gewissen Systems der 
Arithmetik ganzer Zahlen in welchem die Addition als einziger Operation her-
vortritt, Comptes Rendus, 1 Congres des Math. des Pays Slaves, Warsaw, 192–201, 
395.
Putnam, H. (1957) Decidability and essential undecidability. JSL, 22, 39–54.
Putnam, H. (2000) Nonstandard models and Kripke’s proof of the Gödel theorem. 
Notre Dame J. Formal Logic, 41, 53–58.
Quine, W.V. (1937) New foundations for mathematical logic, Am. Math. Mon., 44, 
70–80.
Quine, W.V. (1951) Mathematical Logic. Harvard University Press (second revised 
edition). 
Quine, W.V. (1954) Quantification and the empty domain. JSL, 19, 177–179 (reprinted 
in Quine, 1965, 220–223).
Quine, W.V. (1963) Set Theory and its Logic. Harvard University Press. (revised edition, 
1969).
Quine, W.V. (1965) Selected Logical Papers. Random House.
Rabin, M. (1958) On recursively enumerable and arithmetic models of set theory. JSL, 
23, 408–416.
Rabin, M. (1977) Decidable theories. HML, 595–629.
Ramsey, F.P. (1925) New foundations of mathematics. Proc. London Math. Soc., 25, 
338–384.
Rasiowa, H. (1956) On the ε-theorems. FM, 43, 156–165.
Rasiowa, H. (1974) An Algebraic Approach to Non-Classical Logics. North-Holland.
Rasiowa, H. and R. Sikorski (1951) A proof of the completeness theorem of Gödel. 
FM, 37, 193–200. 
Rasiowa, H. and R. Sikorski (1952) A proof of the Skolem–Löwenheim theorem. FM, 
38, 230–232.
Rasiowa, H. and R. Sikorski (1963) The Mathematics of Metamathematics. Państwowe 
Wydawnictwo Naukowe.
Rescher, N. (1969) Many-Valued Logics. McGraw-Hill.
Rescorla, M. (2007) Church’s Thesis and the conceptual analysis of computability. 
Notre Dame J. Formal Logic, 48, 253–280.
Rice, H.G. (1953) Classes of recursively enumerable sets and their decision problems. 
Trans. AMS, 74, 358–366.
Richard, J. (1905) Les principes des mathématiques et le problème des ensembles. 
Revue générale des sciences pures et appliqués, 16, 541–543.
Robinson, A. (1951) On the Metamathematics of Algebra. North-Holland.



463
Bibliography
Robinson, A. (1952) On the application of symbolic logic to algebra. International 
Congress on Mathematicians, Vol. 2. Cambridge, MA, pp. 686–694.
Robinson, A. (1966) Non-Standard Analysis. North-Holland.
Robinson, A. (1979) Selected Papers, Vol. 1, Model Theory and Algebra, North-Holland; 
Vol. 2, Nonstandard Analysis and Philosophy, Yale University Press.
Robinson, J. (1947) Primitive recursive functions. Bull. AMS, 53, 925–942.
Robinson, J. (1948) Recursion and double recursion. Bull. AMS, 54, 987–993.
Robinson, J. (1949) Definability and decision problems in arithmetic. JSL, 14, 98–114. 
Robinson, J. (1950) Anessentially undecidable axiom system, Proceedings of the 
International Congress Mathematicians, Vol. 1. Cambridge, MA, pp. 729–730.
Robinson, J. (1950) General recursive functions. Proc. AMS, 1, 703–718.
Robinson, J. (1952) Existential definability in arithmetic. Trans. AMS, 72, 437–449.
Robinson, J.A. (1965) A machine-oriented logic based on the resolution principle. 
J. Assoc. Comp. Mach., 12, 23–41.
Robinson, R.M. (1937) The theory of classes. A modification of von Neumann’s sys-
tem. JSL, 2, 69–72.
Rogers, H., Jr. (1959) Computing degrees of unsolvability. Math. Ann., 138, 125–140.
Rogers (1967) Theory of Recursive Functions and Effective Computability. McGraw-Hill.
Rosenbloom, P. (1950) Elements of Mathematical Logic. Dover.
Rosser, J.B. (1936) Extensions of some theorems of Gödel and Church. JSL, 87–91 
(reprinted in Davis, 1965).
Rosser, J.B. (1937) Gödel theorems for non-constructive logics. JSL, 2, 129–137. 
Rosser, J.B. (1939) An informal exposition of proofs of Gödel’s theorem and Church’s 
theorem. JSL, 53–60 (reprinted in Davis, 1965). 
Rosser, J.B. (1942) The Burali-Forti paradox. JSL, 7, 1–17.
Rosser, J.B. (1953) Logic for Mathematicians. McGraw-Hill (second edition, Chelsea, 1978).
Rosser, J.B. (1954) The relative strength of Zermelo’s set theory and Quine’s New 
Foundations, Proceedings of the International Congress on Mathematicians, 
Amsterdam, the Netherlands, III, pp. 289–294.
Rosser, J.B. (1969) Simplified Independence Proofs. Academic.
Rosser, J.B. and A. Turquette (1952) Many-Valued Logics, North-Holland (second edi-
tion, 1977, Greenwood).
Rosser, J.B. and H. Wang (1950) Non-standard models for formal logics. JSL, 15, 
113–129.
Rotman, J.J. (1973) The Theory of Groups, 2nd edn. Allyn & Bacon.
Rubin, H. and J. Rubin (1963) Equivalents of the Axiom of Choice. North-Holland.
Rubin, J. (1967) Set Theory for the Mathematician. Holden-Day.
Russell, B. (1906) Les paradoxes de la logique. Revue de métaphysique et de morale, 14, 
627–650.
Russell, B. (1908) Mathematical logic as based on the theory of types. Am. J. Math., 
30, 222–262.
Ryll-Nardzewski, C. (1953) The role of the axiom of induction in elementary arithme-
tic. FM, 39, 239–263.
Sambin, G. (1976) An effective fixed point theorem in intuitionistic diagonalizable 
algebras. Stud. Log., 35, 345–361.
Sereny, G. (2004) Boolos-style proofs of limitative theorems. Math. Log. Q., 50, 211–216.
Schütte, K. (1951). Beweistheoretische Erfassung der unendlichen Induktion in der 
Zahlentheorie. Math. Ann., 122, 368–389.



464
Bibliography
Scott, D. and D. McCarty. (2008) Reconsidering ordered pairs. Bull. Symb. Log., 14, 
379–397.
Shannon, C. (1938) A symbolic analysis of relay and switching circuits. Trans. Am. Inst. 
Elect. Eng., 57, 713–723.
Shapiro, S. (1988) The Lindenbaum construction and decidability. NDJFL, 29, 208–213. 
Shapiro, S. (1991) Foundations without Foundationalism: A Case for Second-order Logic. 
Oxford University Press.
Shapiro, S. (ed.) (2007) The Oxford Handbook of Philosophy of Mathematics and Logic. 
Oxford University Press.
Shepherdson, J.C. (1951–1953) Inner models for set theory. JSL, 1, 16, 161–190; II, 17, 
225–237; III, 18, 145–167.
Shepherdson, J.C. (1961) Representability of recursively enumerable sets in formal 
theories. Archiv für mathematische Logik und Grundlagenforschung, 5, 119–127.
Shepherdson, J.C. and H.E. Sturgis (1963) Computability of recursive functions. J. Assoc. 
Comp. Mach., 10, 217–255.
Sher, G. (ed.) (2010) Between Logic and Intuition: Essays in Honor of Charles Parson. 
Cambridge University Press.
Shoenfield, J. (1954) A relative consistency proof. JSL, 19, 21–28.
Shoenfield, J. (1955) The independence of the axiom of choice, Abstract. JSL, 20, 202.
Shoenfield, J. (1961) Undecidable and creative theories, FM, 49, 171–179.
Shoenfield, J. (1967) Mathematical Logic. Addison-Wesley.
Shoenfield, J. (1971a) Unramified forcing, Proceedings of the Symposium on Pure 
Mathematics, Vol. 13. AMS, pp. 357–381.
Shoenfield, J.R. (1971b) Unramified forcing, Axiomatic set theory, Proceedings of 
Symposia in Pure Mathematics, Vol. 13. American Mathematical Society, pp. 357–381.
Sierpinski, W. (1947) L’Hypothèse généralisée du continu et l’axiome du choix. FM, 
34, 1–5.
Sierpinski, W. (1958) Cardinal and Ordinal Numbers. Warsaw.
Sikorski, R. (1960) Boolean Algebra. Springer (third edition, 1969).
Skolem, T. (1919) Untersuchungen über die Axiome des Klassenkalküls und über 
Produktations- und Summationsprobleme, welche gewisse Klassen von 
Aussagen betreffen. Skrifter-Vidensk, Kristiana, I, 1–37.
Skolem, T. (1920) Logisch-kombinatorische Untersuchungen über die Erfüllbarkeit oder 
Beweisbarkeit mathematischer Sätze. Skrifter-Vidensk, Kristiana, 1–36 (English 
translation in Van Heijenoort, 1967, 252–263).
Skolem, T. (1923) Einige Bemerkungen zur axiomatischen Begründung der 
Mengenlehre. Wiss. Vorträge gehalten auf dem 5. Kongress der skandinav. 
Mathematiker in Helsingförs, 1922, 217–232 (reprinted in Van Heijenoort, 1967, 
290–301).
Skolem, T. (1934) Ueber die Nicht-Characterisierbarkeit der Zahlenreihe mit-
tels endlich oder abzählbar unendlich vieler Aussagen mit ausschliesslich 
Zahlenvariablen. FM, 23, 150–161.
Smoryński, C. (1977) The incompleteness theorems. HML, 821–866.
Smoryński, C. (1981) Fifty years of self-reference. NDJFL, 22, 357–374.
Smoryński, C. (1985) Self-Reference and Modal Logic. Springer.
Smoryński, C. (1991) Logical Number Theory I. Springer.
Smullyan, R. (1961) Theory of Formal Systems. Princeton University Press.
Smullyan, R. (1968) First-Order Logic. Springer (reprint Dover, 1995).
Smullyan, R. (1978) What is the Name of This Book. Prentice Hall.



465
Bibliography
Smullyan, R. (1985) To Mock a Mockingbird. Knopf.
Smullyan, R. (1992) Gödel’s Incompleteness Theorems. Oxford University Press.
Smullyan, R. (1993) Recursion Theory for Metamathematics. Oxford University Press.
Smullyan, R. (1994) Diagonalization and Self-Reference. Oxford University Press.
Smullyan, R. (1976) Provability interpretations of modal logic. Israel J. Math., 25, 
287–304.
Sonner, J. (1962) On the formal definition of categories. Math. Z., 80, 163–176.
Specker, E. (1949) Nicht-konstruktiv beweisbare Sätze der Analysis. JSL, 14, 145–148.
Specker, E. (1953) The axiom of choice in Quine’s ‘New Foundations for Mathematical 
Logic’. Proc. Natl. Acad. Sci. USA, 39, 972–975.
Specker, E. (1954) Verallgemeinerte Kontinuumhypothese und Auswahlaxiom. Archiv 
der Math., 5, 332–337.
Specker, E. (1957) Zur Axiomatik der Mengenlehre (Fundierungs- und Auswahlaxiom). 
ZML, 3, 173–210.
Specker, E. (1958) Dualität. Dialectica, 12, 451–465.
Specker, E. (1962) Typical ambiguity, Logic, Methodology and Philosophy of Science, 
Proceedings of the International Congress, 1960, Stanford, CA, pp. 116–124.
Stone, M. (1936) The representation theorem for Boolean algebras. Tran. AMS, 40, 
37–111.
Stroyan, K.D. and W.A.J. Luxemburg (1976) Introduction to the Theory of Infinitesimals. 
Academic.
Suppes, P. (1960) Axiomatic Set Theory. Van Nostrand (Dover, 1972).
Szmielew, W. (1955) Elementary properties of abelian groups. FM, 41, 203–271.
Takeuti, G. and W.M. Zaring (1971) Introduction to Axiomatic Set Theory. Springer.
Takeuti, G. and W.M. Zaring (1973) Axiomatic Set Theory. Springer.
Tao, T. (2006) Solving Mathematical Problems: A Personal Perspective. Oxford University 
Press.
Tarski, A. (1923) Sur quelques théorèmes qui equivalent à l’axiome de choix. FM, 5, 
147–154. 
Tarski, A. (1925) Sur les ensembles finis. FM, 6, 45–95. 
Tarski, A. (1933) Einige Berachtungen über die Begriffe der ω-Widerspruchsfreiheit 
und der ω-Vollstandigkeit. Monatsh. Math. Phys., 40, 97–112.
Tarski, A. (1936) Der Wahrheitsbegriff in den formalisierten Sprachen. Stud. Philos., 1, 
261–405 (English translation in Tarski, 1956).
Tarski, A. (1938) Ueber unerreichbare Kardinalzahlen. FM, 30, 68–89.
Tarski, A. (1944) The semantic conception of truth and the foundations of semantics. 
Philos. Phenom. Res., 4, 341–376.
Tarski, A. (1951) A Decision Method for Elementary Algebra and Geometry. Berkeley, CA. 
Tarski, A. (1952) Some notions and methods on the borderline of algebra and meta-
mathematics, International Congress on Mathematics, Cambridge, MA, 1950, 
AMS, pp. 705–720. 
Tarski, A. (1956) Logic, Semantics, Metamathematics. Oxford University Press (second 
edition, 1983, J. Corcoran (ed.), Hackett).
Tarski, A., A. Mostowski, and R. Robinson (1953) Undecidable Theories. North-Holland.
Tarski, A. and R.L. Vaught (1957) Arithmetical extensions of relational systems. Comp. 
Math., 18, 81–102.
Tennenbaum, S. (1959) Non-archimedean models for arithmetic. (Abstract) Not. Am. 
Math. Soc., 270.
Torkel, F. (2005) Gödel’s Theorem: An Incomplete Guide in Its Use and Abuse. CRC Press.



466
Bibliography
Troelstra, A.S. (1969) Principles of Intuitionism. Springer.
Troelstra, A.S. and D. van Dalen. (1988) Constructivism in Mathematics, Vols. 1–2. 
Elsevier.
Turing, A. (1936–1937) On computable numbers, with an application to the 
Entscheidungsproblem. Proc. London Math. Soc., 42, 230–265; 43, 544–546.
Turing, A. (1937) Computability and λ-definability. JSL, 2, 153–163.
Turing, A. (1948) Practical forms of type theory. JSL, 13, 80–94.
Turing, A. (1950a) The word problem in semigroups with cancellation. Ann. Math., 52, 
491–505 (review by W.W. Boone, Ann. Math., 1952, 74–76).
Turing, A. (1950b) Computing machinery and intelligence. Mind, 59, 433–460.
Ulam, S. (1930) Zur Masstheorie in der allgemeinen Mengenlehre. FM, 16, 140–150.
van Atten, M. (2003) On Brouwer. Wadsworth.
van Atten, M., P. Boldini, M. Bourdeau, and G. Heinzmann (2008) One Hundred Years 
of Intuitionism. Birkhäuser.
van Benthem, J. and K. Doets. (1983) Higher-order logic. HPL, I, 275–330.
van der Waerden, B.L. (1949) Modern Algebra. Ungar.
van Heijenoort, J. (ed.) (1967) From Frege to Gödel (A Source Book in Mathematical Logic, 
1879–1931). Harvard University Press.
Väth, M. (2007) Nonstandard Analysis. Birkhauser.
Vaught, R.L. (1954) Applications of the Löwenheim–Skolem–Tarski theorem to prob-
lems of completeness and decidability. Indag. Math., 16, 467–472.
Voevodski, V. (2013) Univalent Foundations and Set Theory. Association for Symbolic 
Logic.
Wajsberg, M. (1933) Untersuchungen über den Funktionenkalkül für endliche 
Individuenbereiche. Math. Ann., 108, 218–228.
Wang, H. (1949) On Zermelo’s and von Neumann’s axioms for set theory. Proc. Natl. 
Acad. Sci. USA, 35, 150–155. 
Wang, H. (1950) A formal system of logic. JSL, 15, 25–32.
Wang, H. (1957) The axiomatization of arithmetic. JSL, 22, 145–158.
Weston, T.S. (1977) The continuum hypothesis is independent of second-order ZF. 
Notre Dame J. Formal Logic, 18, 499–503.
Whitehead, A.N. and B. Russell (1910–1913) Principia Mathematica, Vols. I–III. 
Cambridge University Press.
Wiener, N. (1914) A simplification of the logic of relations. Proc. Camb. Philos. Soc., 17, 
387–390 (reprinted in Van Heijenoort, 1967, 224–227).
Yanofsky, N.S. (2003) A Universal approach to self-referential paradoxes, incomplete-
ness and fixed points. Bull. Symb. Log., 9, 362–386.
Yasuhara, A. (1971) Recursive Function Theory and Logic. Academic.
Zach, R. (1999) Completeness before Post: Bernays, Hilbert, and the development of 
propositional logic. Bull. Symb. Log., 5, 331–366.
Zeeman, E.C. (1955) On direct sums of free cycles. J. London Math. Soc., 30, 195–212.
Zermelo, E. (1904) Beweis, dass jede Menge wohlgeordnet werden kann. Math. Ann., 
59, 514–516 (English translation in Van Heijenoort, 1967, 139–141). 
Zermelo, E. (1908) Untersuchungen über die Grundlagen der Mengenlehre. Math. 
Ann., 65, 261–281 (English translation in Van Heijenoort, 1967, pp. 199–215).
Zuckerman, M. (1974) Sets and Transfinite Numbers. Macmillan.



467
Notations
Y	
xiv
P (Y)	
xiv, 240
∈, ∉	
xvii, 231
{x|P(x)}	
xvii
⊂, ⊆	
xvii, 232
=, #	
xvii, 93
∪, ∩	
xvii
0	
xvii, 234
x − y	
xvii
{b1, …, bk}	
xvii
{x, y}, {x}	
xvii, 235
〈b1, b2〉, 〈b1, …, bk〉	
xvii, 235–236
Xk	
xvii, 240
Y × Z	
xvii, 240
R−1	
xviii
ω	
xviii, 253
IX	
xviii
[y]	
xviii
f(x), f(x1, …, xn)	
xix
fZ	
xix
f ○ g	
xix
1 − 1	
xix
X ≅ Y	
xix
ℵ, 2ℵ
0
0	
xx
¬, ∧	
1
T, F	
1
∨, ⇒	
1, 2
⇔	
3
↓, |	
21, 22
dnf, cnf	
23
Res(A  )	
25
wf	
27
⊢	
28
L	
28
MP	
29
Hyp	
31
L1 – L4	
39
(∀x), (∃x)	
41
A
f
a
k
n
k
n
j
,
,
	
42



468
Notations
A
f
a
j
n
j
n
j
(
)
(
)
( )
M
M
M
,
,
	
49
Σ	
56
s*	
59
⊨M A	
57
⊨M A  [b1, …, bk]	
58
Gen	
67
A4, E4	
74
⊢C	
78
g	
84, 192, 329
K1, K2	
96
G, GC, F, RC, F<	
96, 97
(∃1x)	
98
(∃nx)	
100
ι	
105, 132
≈	
111, 137
K2, Kn	
112
M1 ≡ M2	
123
K∞	
123
M1 ⊆ M2	
124
M1 ≤e M2	
125
∏
∈
j J
j
D 	
131
=ℱ, fℱ	
131
Π
j J
j
D
∈
/	
131
{cj}j∈J	
131
Π
j J
j
D
∈
/	
132
Nj/ℱ	
132
c#, M#	
134
R, ℛ	
136
R*, ℛ*, R#, ℛ#	
136
st(x)	
137
×	
141
f	
147
pp#	
148
PPS#	
147
ETH	
148
∀P	
149
ℒA	
149
S, t′, +, 0	
153
PA	
154
n	
159
<, ≤, >, ≥	
162
t|s	
166
S+	
169



469
Notations
Z	
171
N, Uj
n	
171
CR	
173
μ	
175
δ, −	
177
|x – y|	
177
sg, sg	
177
min, max	
177
rm, qt	
177
Σ
Σ
Π Π
y z y z y z y z
>
≤
>
≤
,
,
,
	
177
Σ
u y v
< < 	
179
τ(x)	
179
(∀y)y<z, (∀y)y≤z, (∃y)y<z, (∃y)y≤z	
179
μyy<z	
180
Pr	
180
px	
181
(x)j, ℓh(x)	
182
x * y	
182
n

, Π(n), RP(y, z)	
183
σ2, σ1
2, σ2
2 	
184
σk, σi
k 	
185
f#	
185
β, Bt	
187
IC, FL, PL	
193
EVbl, EIC, EFL, EPL	
194
ArgT, ArgP, Gd	
194
MP(x, y, z), Gen(x, y), Trm(x)	
194
Atfml, Fml	
195–196
Subst, Sub	
196
Fr, Ff, Axj	
196–198
LAX, Neg, Cond, Clos	
198
Num, Nu, D	
199
PrAx, Ax, Prf, Pf	
199–200
RR, Q	
203
R	
204
⌜𝒞⌝	
205
𝒢	
205
ℛ	
211
Tr	
214
𝒞onK, ℬew	
215
(HB1)−(HB3)	
216
ℋ	
216
TK	
218
PF, PP, PS	
223



470
Notations
PMP	
225
NBG	
231
M, Pr	
232
∩, X, 𝒟, ∪, V, −	
237
Rel	
240
∪(Y), 𝒫(Y)	
240, 241
{〈x1, …, xn〉|φ}	
241
I, 
⌣
Y	
241, 242
ℛ(Y)	
242
∪v∈x v	
243
Fnc	
245
X: Y → Z	
245
Y ↓ X	
245
X′Y, X″Y, Fnc, (X)	
245
Irr, Tr, Part, Con, Tot, We	
247
Sim	
248
Fld, TOR, WOR	
249
E, Trans, SectY, SegY	
249–250
Ord, On	
250
1	
251
<0, ≤0	
252
x′	
253
Suc, K1	
253
2, 3	
254
Lim	
254
+0, ×0, exp	
257
EX	
257
≅
F,≅	
260
XY	
261
≼, ≺	
262
X +c Y	
265
Fin	
266
Inf, Den, Count, Dedfin, DedInf	
268
ℋ′x	
271
Init	
271
ωα	
273
AC, Mult, WO, Trich, Zorn	
282
UCF	
285
Reg	
286
TC(u)	
286
PDC, DAC	
287
Ψ	
287
H, Hβ	
288
ρ′x	
288



471
Notations
GCH	
292
MK	
294
ZF, Z	
295
ST	
298
NF	
300
ST−, NFU, ML	
302–303
UR	
303–304
RegUR	
308
Λ	
312
α
β
↠
T
	
314
AlgT	
314
|, B	
315
k, k
kn
1,
,
…
(
)	
315
fT, 1	
315
fT, n	
315
r, l, aj, P, ∧, ρ	
319, 320
λ, S	
320
~, W, X	
321
ℛ	
321
ℒ, T, σ, C	
321, 322
K, Kn	
322, 323
ST	
327
IS, Sym, Quad, TM, TD, NTD	
330–331
Stop, Comp, Num, TR, U, Tn	
331–332
φz
n	
338
Sn
m	
338
Σ
Π
k
n
k
n
,
	
342
r.e.	
349
Wn	
351
HG	
356
Eqt, Syst, Occ, Cons1, Cons2	
360–362
Ded, Sn, U	
361
→, → ·	
362
𝕬: P ⊐	
363
𝕬:P ⊢ R	
363
𝕬(P) ≈ 𝔅(P)	
367
𝔖𝔅	
368
𝔅 ο 𝕬, 𝕹B	
369
ψ𝔅	
370
L1C	
379
L2C, Σ2	
379, 380
L2	
381
COMP, FUNDEF	
383
Gen 2a, Gen 2b	
383



472
Notations
PC2	
384
AR2	
384
L2A	
386
SV	
386
Cont	
388
∑Z
H 	
389



K23184
w w w . c r c p r e s s . c o m
TEXTBOOKS in MATHEMATICS
Mathematics
The new edition of this classic textbook, Introduction to Mathemati-
cal Logic, Sixth Edition explores the principal topics of mathematical 
logic. It covers propositional logic, first-order logic, first-order number 
theory, axiomatic set theory, and the theory of computability. The text 
also discusses the major results of Gödel, Church, Kleene, Rosser, 
and Turing.
The sixth edition incorporates recent work on Gödel’s second incom-
pleteness theorem as well as restoring an appendix on consistency 
proofs for first-order arithmetic. This appendix last appeared in the 
first edition. It is offered in the new edition for historical considerations. 
The text also offers historical perspectives and many new exercises 
of varying difficulty, which motivate and lead students to an in-depth, 
practical understanding of the material.
I N T R O D U C T I O N  T O 
MATHEMATICAL LOGIC
SIXTH EDITION
