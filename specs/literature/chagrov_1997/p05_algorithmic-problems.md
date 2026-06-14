<!-- Source: Chagrov & Zakharyaschev (1997). Modal Logic (Oxford Logic Guides 35). Part V: Algorithmic Problems — decidability and complexity (Ch 16+). BibKey: ChagrovZakharyaschev1997 -->

Algorithmic problems 
In this part we consider logics and their properties from the algorithmic point 
of view, i.e., we are interested in the existence of algorithms which are able to 
decide mass problems concerning them. Almost all algorithmic problems we have 
dealt with so far were solved positively by means of presenting concrete decision 
procedures. However, the “real algorithmic science” appears only when we need 
to prove that there is no algorithm deciding a particular problem and to estimate 
the efficiency of existing algorithms. 

16 
THE DECIDABILITY OF LOGICS 
The first and perhaps most important algorithmic question arising immediately 
after creating a logic is the question of its decidability: is there an algorithm 
which is capable of deciding, given an arbitrary formula, whether it belongs to 
the logic or not? 
16.1 	Algorithmic preliminaries 
So far when we considered algorithmic problems—mainly the decidability 
problem for various logics—we could do without a precise definition of the concept of 
algorithm, simply presenting some informal decision procedures. In any case the 
reader will most likely agree that those procedures can be realized as computer 
programs. But now we will be also interested in obtaining “negative” algorithmic 
results which assert that there are no algorithms deciding such-and-such 
problems. Clearly in this case we must formulate exactly what objects we are going 
to prove as not existing. 
Of course, our intuitive idea of algorithm is too vague (and perhaps has 
too many traits of a rather psychological nature) to be transformed directly 
to a formal definition. However, many decades of using various formal versions 
of the notion of algorithm show that most people have more or less the same 
algorithmic intuition, because all of them turned out to be in a sense equivalent. 
So intuitive algorithmic constructions may be regarded as precisely those which 
can be realized in terms of one of such formalizations. This statement, known as 
Church’s thesis, is clearly unprovable (though it can be disproved in principle). 
By accepting Church’s thesis we gain in two respects: 
• to show that an algorithm exists, it suffices to present its convincing and 
intuitively clear description without being involved in details of any specific 
formalization; 
• to show that an algorithm does not exist, it suffices to prove that no 
algorithm in a specific formal system can perform the desirable actions, i.e., to 
prove the absence of a mathematical object. 
In this book we will use only one algorithmic formalism which is called Minsky 
machines. It has been chosen for purely technical reasons as the most convenient 
(from our standpoint) for being simulated by modal and intuitionistic formulas. 
The reader not familiar with algorithm theory and not willing to take on trust 
the facts formulated below without proofs should consult first a good textbook, 
say Cutland (1980) or Mal’cev (1970). 

492 
THE DECIDABILITY OF LOGICS 
Algorithmically computable arithmetical partial functions are called partial 
recursive functions. The word “partial” here means that the domain of a 
function may be smaller than the whole set of natural numbers. Completely defined 
partial recursive functions are called total recursive functions or simply recursive 
functions. We will regard the terms “algorithm” and “partial recursive function” 
as synonymous. The fact that we consider only arithmetical functions is not 
essential. For there are various ways of reducing algorithmic operations on 
constructive objects (e.g. formulas or derivations) to those on natural numbers—we 
mean effective enumerations. However we prefer to deal with syntactical and 
semantic objects directly. In the former case we will assume that our languages are 
based on the set Var = {po,Pi> • • •} of variables and in the latter that frames, 
relations, valuations, etc. are defined by algorithms (we shall make this more 
precise if required). Thus we allow using such terms as “a partial recursive function 
from the set of pairs (formula, frame) into {0,1}” and similar. 
A set X is called recursive (or decidable) if there is an algorithm which, given 
an object x from the class under consideration, recognizes whether x € X or 
not. X is said to be recursively enumerable if one of the following equivalent 
conditions is satisfied: 
• X is the domain of a partial recursive function; 
• X is either the range of a total recursive function or empty. 
The latter condition justifies the term “enumerable” in the sense that a 
recursive function, say /, enumerates the members of non-empty X, possibly with 
repetitions: X = {/(0), /(1), /(2),...}. 
We have already used the fact that there are recursively enumerable sets (of 
natural numbers) which are not recursive; concrete examples will be shown later 
on. These two kinds of sets are connected as follows: X is recursively enumerable 
iff it can be represented in the form X = {x : 3y (x,y) € Y}, for some recursive 
set Y of pairs. We also have the following simple proposition which may be used 
for proving the decidability of logics. 
Proposition 16.1 Suppose Y is a recursive set andX C Y. ThenX is recursive 
iff both X and Y — X are recursively enumerable. 
Proof (=>) Change a decision algorithm for X in such a way that instead of 
the answer “no” (for the input elements from Y — X) it would give no answer at 
all entering, for instance, an endless loop. The domain of the resulting algorithm 
will then coincide with X, which means that X is recursively enumerable. By 
inserting in the original algorithm an endless loop instead of the answer “yes” 
we clearly obtain an algorithm whose domain is Y — X. 
(<=) Here is a decision procedure for X. First check whether a given object 
x is in Y. If it is, run two algorithms enumerating X and Y - X, respectively, 
and wait until x appears. □ 
Now we define the algorithmic formalism that will be used in what follows 
for establishing various undecidability results concerning modal and si-logics. 

ALGORITHMIC PRELIMINARIES 
493 
A Minsky machine is a finite set (program) of instructions for transforming 
triples (s,ra,n) of natural numbers, called configurations. The intended meaning 
of the components in the current configuration (s,ra,n) is as follows: s is the 
number (label) of the current machine state or, which is the same, the number of 
the instruction to be executed at the next step, and m, n represent the current 
state of information. Each instruction has one of the four possible forms: 
*-(f,l,0), s-M, 1), 
5 - (t, -1,0) ((t\ 0,0)), s —* (t, 0, -1) ((*', 0,0)). 
The last of them, for instance, means: transform (s, m, n) into (£, m, n — 1) if n > 
0 and into (t', m, n) if n = 0. The meaning of the others is defined analogously. 
If P is a Minsky machine then the notation P : (s,ra,n) —> (t,k,l) means 
that starting with (s, m, n) and applying the instructions in P, in finitely many 
steps (possibly, in 0 steps) we can reach the configuration (£, fc, /). In particular, 
we always have P : (s,ra,n) —> (s,ra,n). If the relation P : (s,ra,n) —> (£,&,/) 
does not hold, we write P : (s,ra,n) (£, fc,/). 
Of all possible states of a machine two are distinguished: si is regarded as 
the only initial state, at which the machine starts working, and sq as the only 
final state, at which the machine halts. Of course, the program contains no 
instruction with the number sq. If no instruction can be applied to a current 
non-final configuration then we will think of our machine as working forever (or 
being out of order and returning no result). All Minsky machines are assumed to 
be deterministic, i.e., they may not contain distinct instructions with the same 
numbers. 
Now, which arithmetical partial functions are computable by Minsky 
machines? The answer is the following statement which, in view of our definition of 
partial recursive functions and the known fact that Minsky machines are 
equivalent to any other universal algorithmic formalism, can be called the Church- 
Minsky thesis: 
• an arithmetical partial function f(x) is a partial recursive function iff there 
is a Minsky machine P such that, for every natural x, if f(x) is defined then 
P : (si,2x,0) —> (s0,2^x),0) and if f(x) is undefined then the machine, 
having started at (si,2x,0), never comes to the final state. 
Using this statement, by the standard argument we can prove the 
undecidability of various problems concerning Minsky machines. First we have the 
undecidability of the configuration problem: 
Theorem 16.2 There is no algorithm which, given a program P and 
configurations (s,m,n) and (t,k,l), can decide whether P : (s,m, n) —> (t,k,l) holds. 
This theorem may be used for establishing a lot of our further undecidability 
results, but not all of them. It will be much more convenient to use a variant of 
the configuration problem with fixed suitable P and (s,m,n), called the second 
configuration problem: 

494 
THE DECIDABILITY OF LOGICS 
Theorem 16.3 There exist ti program P and a configuration (s,ra,n) such that 
there is no algorithm which is capable of deciding, given a configuration (t,k,l), 
whether P : (s, m, n) —> (t,k,l). 
Proof Let X be a recursively enumerable non-recursive set and g(x) a recursive 
function enumerating X, with g{0) = a. Define a partial recursive function f(x) 
as follows. Given x, we compute g(0),g(l),... until we get x = g(mi) for some 
number m\ and then continue computing g(rn\ +1), g{m\ + 2),... until #(7712) 
• • • 5 <7(mi)} for some m2. When (and if) this process stops, we put f(x) = 
g(m2) (otherwise f(x) is undefined). Clearly f(x) is a partial recursive function 
and X = {a, /(a), /(/(a)),...}. 
Let P' be a Minsky program computing f(x). Define another program P by 
renaming so in P' into s' (not occurring in P') and adding two new instructions: 
s' -» (s", 0,1), s" - (Sl, 0, -1) «S!,0,0», 
where sft is a new state. Notice that P does not have a final state and, having 
started at the configuration (si,2a,0), it works forever. But more important is 
that 
X = {a} U {x : P : (su 2a, 0) — (s', 2®, 0)}. 
Thus, if the second configuration problem for P and (si,2a,0) were decidable, 
the set X would be recursive. □ 
We shall also require two variants of the halting problem. 
Theorem 16.4 There is a Minsky machine P such that no algorithm can 
recognize, given an arbitrary configuration (s,m,n), whether P comes to the final 
state having started at (s,m,n). 
Theorem 16.5 There is a configuration (s,m, n) such that no algorithm can 
recognize, given a Minsky machine P, whether P comes to the final state having 
started at (s, m, n). 
To prove Theorem 16.4 it suffices to take a recursive function enumerating a 
non-recursive set and use the Church-Minsky thesis. As to Theorem 16.5, one 
can exploit the following statement. 
Call a property of Minsky machines non-trivial if there are machines both 
with this property and without it. A property is called invariant if equivalent 
machines have (or do not have) the property simultaneously. Here by equivalent 
machines we mean those which, having started at the same initial configuration, 
come to the same final configuration or never stop. Thus an invariant property 
depends not on the intrinsic organization of programs, but on what they 
compute. 
Theorem 16.6. (The Rice-Uspensky theorem) For every non-trivial 
invariant property of Minsky machines, there is no algorithm which, given an 
arbitrary program, can decide whether is satisfies the property or not 

PROVING DECIDABILITY 
495 
16.2 	Proving decidability 
Observe first that “most logics” are undecidable. For there are “only” countably 
many algorithms (they may be considered as words in a fixed finite alphabet) 
but uncountably many logics. Moreover, for the same reason “most logics” are 
not even recursively enumerable. Fortunately the “most interesting logics” form 
a countable family and so this cardinality argument does not go through for 
them. 
In this section we analyze from the recursion-theoretic point of view the 
method of proving decidability we have used so many times before. 
To begin with, we enumerate formulas. Every formula in YotMC may be 
regarded as a word (a string of symbols) in the alphabet 
p, A, V, ±, D, |, (, ) 
where | is a symbol for generating subscripts: po is represented as p, pi as p|, P2 
as p||, etc. Of course, using two or moire special signs instead of | we could write 
formulas shorter. But in principle this does not matter: for any finite alphabet we 
can effectively determine whether a given string of symbols is a formula. Writing 
down all possible strings—first of length 1, then of length 2, etc.—and discarding 
those that are not formulas, we can effectively enumerate all formulas in ForMC 
or For£. Thus we obtain 
Lemma 16.7 EoyMC and For£ are recursively enumerable (without 
repetitions). Moreover, these sets are recursive. 
Now we consider enumerations of formulas in logics. 
Lemma 16.8 Every logic L with a recursively enumerable set of axioms is also 
recursively enumerable. 
Proof Notice first that every derivation in L may be regarded as a word in 
the alphabet A of L’s language with the extra symbol “,” used for separating 
formulas in derivations. So we have a recursive enumeration of L’s axioms, say, 
and a recursive enumeration wq,wi,W2,--- of all words in A. Now, 
for every n > 0 we select from wo,..., wn all those derivations in L which use only 
axioms in the list <po, • • • > (To check whether a formula ^ is a substitution 
instance of an axiom <p, it suffices to write down all the substitution instances of 
if of length not greater than that of xp and compare them with xp.) Since every 
derivation uses only finitely many axioms, sooner or later it will be found. Thus 
we recursively enumerate all the derivations in L and thereby L itself. □ 
Strange as it may seem at first sight, there is no difference between recursively 
enumerable axiomatizations and recursive ones. 
Lemma 16.9 Every recursively enumerable logic L is recursively axiomatizable 
(i.e., has a recursive set of axioms). 

496 
THE DECIDABILITY OF LOGICS 
Proof Let ipi, <p2,. ■ • be a recursive enumeration of L. For every n > 1, put 
= (fn A ... A (pn . 
' 
n 
Since the rules p/p A p and p A p/p are admissible (and derivable) in all modal 
and si-logics, {xpn : 1 < n < uj} is a set of axioms for L. This axiomatization 
is recursive because to verify whether a formula x/j is an axiom it suffices to 
represent ^ as a conjunction Xi A ... A Xk in all possible ways (there are finitely 
many of them), generate pk and compare xj) with xpk- □ 
Putting together Lemmas 16.8 and 16.9 we obtain 
Theorem 16.10. (Craig’s theorem) For every logic L the following 
conditions are equivalent: 
(i) L has a recursively enumerable set of axioms; 
(ii) L has a recursive set of axioms; 
(iii) L is recursively enumerable. 
Remark It should be clear that Theorem 16.10 remains true if we take axiom 
schemes rather than axioms. Also we can consider in Theorem 16.10 axiomati- 
zations of L over some fixed recursively enumerable logic Lo C L; without the 
requirement of recursive enumerability only (i) and (ii) are equivalent. 
To apply Proposition 16.1 for establishing the decidability of a logic L we 
must be able to enumerate recursively not only L itself but also its 
complementation, i.e., the set of formulas which do not belong to L. In the majority of the 
decidability proofs above we managed to do without this, using effective 
characterizations of (finite) frames for L, upper bounds for the size of minimal frames 
separating L from formulas out of L and the following: 
Theorem 16.11 Suppose a logic L is characterized by a recursive class C of 
finite frames and there is a recursive function f(x) such that every p L is 
refuted in a frame $ € C with 1^1 < f(l(p)). Then L is decidable. 
Proof Given ip, we construct all finite frames with < f(l(p)) points, discard 
those that are not in C and check whether p is refuted in at least one of the 
remaining frames. □ 
However, actually we do not need upper bounds to establish decidability. 
Usually even finite approximability is enough. For we clearly have 
Lemma 16.12 (i) The class of all finite algebras (matrices, frames) is 
recursively enumerable. 
(ii) If L is characterized by a recursively enumerable class of finite algebras 
(matrices, frames) then the set of formulas which do not belong to L is recursively 
enumerable. 
Using this observation we obtain 

PROVING DECIDABILITY 
497 
Theorem 16.13. (Harrop’s theorem) Every finitely axiomatizable and 
finitely approximable logic L is decidable. 
Proof By Theorem 16.10, L is recursively enumerable. Prom the recursively 
enumerable sequence of all finite frames we can remove all those that are not 
frames for L simply by checking whether they validate L’s axioms. Thus L is 
characterized by a recursively enumerable class of finite frames and so L’s 
complementation is recursively enumerable too. □ 
Theorem 11.19 (ii) shows that the requirement of finite axiomatizability in 
Harrop’s theorem cannot be replaced with that of recursive axiomatizability: 
there are undecidable recursively axiomatizable subframe logics. The reason for 
this phenomenon is that the class of finite frames characterizing a given 
recursively axiomatizable subframe logic is not necessarily even recursively 
enumerable. On the other hand, the single requirement that a logic is characterized by 
a recursive class of finite frames does not mean that the logic is decidable either. 
Theorem 16.14 There is a logic which is characterized by a recursive set of 
finite frames and which is not recursively enumerable. 
Proof We require the following: 
Lemma 16.15 There is a recursive set X of natural numbers such that the set 
{\x — y\ : x,y € X, x ^ y} is not recursive. 
Proof Let f(x) be a recursive function whose range is not recursive. Notice 
that the set 
Y = {10lo/<n>+1 : n < u) 
is recursively enumerable but not recursive. Put 
X = {104n+1,104n+1 + 10lo/<")+1 : n < w}. 
It is not hard to see that X is decidable. On the other, hand we have 
Y = {\x - y\ : x,y e X, x ^ y} C) {10n : n < uj}. 
Since the intersection of recursive sets is also recursive, it follows that the set 
{|x — y\ : x, y E X, x ^ y} cannot be recursive. □ 
Now take the set X constructed in the proof of Lemma 16.15 and, for every 
n < cj, define a frame $n as is shown in Fig. 16.1, where {z, ...,j} = {x E 
X : x < n}. Clearly the set C = {$n n < uj} is recursive. We show that 
the logic L = LogC is not recursively enumerable. By Lemma 16.12 (ii) and 
Proposition 16.1, it suffices to prove that L is not decidable. 
For every n < cj, we put 
<Pn = -‘(0(02l/> A -iO(OV> A -i02l/>)) A 0(02Xn A ->0(<>Xn A -'02Xn))), 

498 
THE DECIDABILITY OF LOGICS 
do 
ai 
Fig. 16.1. 
where r/j = p A D-ip and Xn = A -iOn+1?/>. The reader can readily check that 
<Pn € L iff n e {\x - y\ : x,yel, x / y}. 
By Lemma 16.15, it follows that L is undecidable. □ 
However, we do not know whether the class of all finite frames for the logic 
constructed in the proof above is recursive. In this connection the following result 
is worth noting. 
Theorem 16.16 Suppose L is a recursively axiomatizable finitely approximable 
logic in NExtK4 or Extint. Then L is decidable iff the class of all finite frames 
for L is decidable. 
Proof (<*=) follows from Theorem 16.10 and Lemma 16.12 and (=>) is a 
consequence of the fact that a finite rooted frame $ validates L iff ^(5,1) ^ L 
(0*(&-L )*L). □ 
Lemma 16.12 (ii) can be extended to logics characterized by classes of frames 
or algebras effectively determined by algorithms. Say that a (pseudo-Boolean or 
modal) algebra is recursive if its universe is a recursive set and the operations 
are realized by some algorithms (in particular, there are algorithms computing 
T and .L). Thus a recursive algebra may be thought of as a suitable collection of 
algorithms. A class of recursive algebras is called recursively enumerable if there 
is an algorithm enumerating the collections of algorithms corresponding to those 
algebras. A matrix (21, V) is recursive if both 21 and V are recursive. Recursive 
frames can be defined in the same manner. 
Lemma 16.17 If a logic L is characterized by a recursively enumerable class C 
of recursive algebras (matrices, frames) then the set of formulas that are not in 
L is also recursively enumerable. 
Proof Let </?o > </>i > • • • be an effective enumeration of formulas, 2lo,2li,... an 
effective enumeration of algebras in C and, for every i < uj, let alQ, a\,... be an 
effective enumeration of elements in 21*. An algorithm enumerating all formulas 
that are not in L may be as follows. For every n < uj and every i,j < n we 

LOGICS CONTAINING K4.3 
499 
compute the value of <pi in 21j under all possible assignments of the elements 
aj,... ,aJn to <pi s variables. And if this value is different from T, the algorithm 
returns </?* as its next value. □ 
Using this lemma we obtain the most general criterion of decidability. 
Theorem 16.18 A logic is decidable iff it is recursively axiomatizable and 
characterized by a recursively enumerable class of recursive algebras (matrices). 
Proof (<*=) follows from Theorem 16.10 and Lemma 16.17. And to prove (=>) 
it suffices to observe that the Tarski-Lindenbaum algebra for a decidable logic is 
also decidable (we can fix an effective enumeration of all formulas and construct 
the universe of 21l from the formulas <p such that <p has the smallest number in 
MU). □ 
16.3 	Logics containing K4.3 
Now we use the observations of the preceding section to show how a good 
completeness result can be used for establishing decidability even in the absence of 
finite approximability. 
We consider the class NExtK4.3 of normal modal logics of width 1. According 
to Theorem 6.2, not all of them are finitely approximable, and so the standard 
way of proving decidability by using Harrop’s theorem does not go through for 
logics in the class. Let us recall, however, that the essential point in the proof 
of Harrop’s theorem was not that a logic is complete with respect to the class 
of finite frames but that (i) this class is recursively enumerable and (ii) we can 
always check effectively whether a frame in the class validates a given formula. By 
Fine’s theorem of Section 10.4, all logics in NExtK4.3 are complete for the class 
of Kripke frames of width 1 without infinite ascending chains, i.e., Noetherian 
chains of clusters. This class does not meet the conditions (i) and (ii). What we 
are going to prove below is that it contains a subclass which satisfies both (i) 
and (ii) and is still big enough to ensure completeness. 
We will use the apparatus of canonical formulas. Each logic L £ NExtK4.3 
can be represented in the form 
L = K4.3 ® {a(&, 2),, 1) : % £ /}, (16.1) 
where all are chains of clusters. For a finitely axiomatizable L representation 
(16.1) with finite I can be constructed effectively, given a finite set of L’s axioms. 
The following simple example explains in terms of canonical formulas why 
logics of width 1 are not necessarily finitely approximable. 
Example 16.19 Let us consider the logic L = K4.3 ® a(#, {{1}}, _L) and the 
formula a(Sr, _L) where # is the frame depicted in Fig. 16.2 (a). The frame 0 
shown in Fig. 16.2 (b) separates a(Sr, _L) from L. Indeed, ^ is a cofinal subframe 
of 0 which, by the refutability criterion (Theorem 9.39), gives 0 j^= a(3r, _L). To 
establish that 0 \= a(3r, {{1}}, _L), suppose / is a cofinal subreduction of 0 to #. 

500 
THE DECIDABILITY OF LOGICS 
O 
f 
• 
f 
I 
f 
1 
• 
f 
o2 
1 
• 
f 
I' 
I 
O 
f 
<>1 
1 
* 
1 
T 
o0 
<& o 
Si lo 
01 • 
(a) 
(b) 
(c) 
(d) 
FIG. 16.2. 
Then /-1(1) contains only one point, say x; /_1(0) also contains only one point, 
namely the root of 0. So the whole infinite set of points between x and the root 
is outside of dom/, which means that / does not satisfy (CDC) for {{1}}. 
On the other hand, if fj is a finite refutation frame (of width 1) for a(Sr, _L) 
then Sf contains a non-degenerate cluster C having an irreflexive immediate 
successor x, and by mapping C to 0, x to 1 and all the points above x to 2 we 
obtain a cofinal subreduction of fj to $ satisfying (CDC) for {{1}}, from which 
S)£L. 
Returning to our completeness problem, let us observe that the refutability 
criterion for canonical formulas may be somewhat simplified if we deal only with 
Noetherian chains of clusters. Say that a subreduction / of one frame to another 
is injective if /(x) ^ f(y) for every distinct x, y £ dom/. 
Theorem 16.20 For any Noetherian chain of clusters 0 and any canonical 
formula a($, S), J.), 0 £*(#, 2),-L) iff there is an injective cofinal subreduction 
g of 0 to satisfying (CDC) for 2). 
Proof (=4>) Suppose 0 £*({?, 2), -L). Then there is a cofinal subreduction / of 
0 to ^ satisfying (CDC) for 2). We reduce / to a map g so that g~l(x) will be a 
singleton for every point x in #. Observe first that /-1(x) must be a singleton if 
x is irreflexive (here we use the fact that 0 is a chain of clusters.) Suppose now 
that x is a reflexive point in {?. Since 0 coiitains no infinite ascending chains, 
f~1(x) has a finite cover and so there is a reflexive point ux £ /-1(x) such that 
/_1(x) C ux[. Fix such a ux for each reflexive x in $ and define g by taking, for 
any y in 0, 
{f(y) if either f(y) is irreflexive or 
f(y) is reflexive and y = u/(y) 
undefined otherwise. 
It should be clear from the definition that g is an injective cofinal subreduction 
of 0 to #. 
Suppose y £ dom^t and g(y|) = x| for some {x} £ 2). Then x is irreflexive 
and we must have y £ dom/|, f{y]) = x|, from which y £ dom/, since / 
satisfies (CDC) for 2). It follows that f(y) is irreflexive (for otherwise x £ f(y)| 

LOGICS CONTAINING K4.3 
501 
and there is z € y] such that f(z) = f(y) which together with /(y|) = x] 
implies f(y) G x|, contrary to x being irreflexive) and so ye doirnj. Thus g 
satisfies (CDC) for 2). 
(<*=) follows from the refutability criterion. □ 
Theorem 16.20 may be interpreted in the following way. Every Noetherian 
chain of clusters refuting i.) can be obtained from # by inserting some 
Noetherian chains of clusters just below clusters C(x) in such that {x} ^ 2) 
and by enlarging some non-degenerate clusters in 
We show now that if a formula a(S, S, -L) is not in L € NExtK4.3 then it can 
be separated from L by a frame constructed from $ by inserting in open domains 
between its adjacent clusters either finite descending chains of irreflexive points 
possibly ending with a reflexive one or infinite descending chains of irreflexive 
points and without using the operation of enlarging ^’s non-degenerate clusters. 
Let 2), J.) be a canonical formula built upon a chain of clusters $ and 
C(xo),..., C(xn) all distinct clusters in $ = {W,R} ordered in such a way that 
C{xo) C C(xi)| C ... C C{xn)[. By a type for a(3f2),_L) we will mean any 
n-tuple t = ($i,..., £n) such that, for i £ {1,..., n}, either & = m or & = m-h, 
for some m < uj, or & = uj, with & = 0 if {Xi} £ 2). 
Given a type t = (£i,... , £n) for a(Sr, 2), .1), we define a t-extension of as 
the frame 0 that is obtained from by inserting between each pair C(xi-1), 
C(xi) of S’s adjacent clusters either a descending chain of m irreflexive points, 
if & = m < uj, or a descending chain of m + 1 points of which only the last 
(lowest) one is reflexive, if & = m-h, or an infinite descending chain of irreflexive 
points, if & = uj. More formally the t-extension 0 = (V, S) of may be defined 
as follows. For 1 < i < n, we first put 
{{a1- : 0 < j < m} if & = m < uj 
{aj, b* : 0 < j < m} if & = ra+ 
{aj : 0 < j < uj} if & = cj, 
- {<4 , <44) , (4,4) : b\ a), 4 e Vi, j > k}. 
And then 
n 
V = W U (J Vi 
1=1 
and 5 is the transitive closure of the relation 
n n 
RU (JSiU lj{(xi_i,x),(x,xi) : xeV;}. 
1=1 1=1 
Example 16.21 The frame 0 in Fig. 16.2 (b) is the t-extension of # in Fig. 16.2 
(a), for every t = (uj, n), 0 < n < cj, which clearly is a type for a(Sr, _L). 0i in 
Fig. 16.2 (d) is the (0, l+)-extension of #1 in Fig. 16.2 (c), with (0,1+) being a 
type for a(3i, {{1}}, -L). 

502 
THE DECIDABILITY OF LOGICS 
It should be clear that, for every type t for a(Sr, 2), J_), the ^-extension of # 
refutes a(Sr, 2), -L). 
The following trivial observation will be used several times below. 
Lemma 16.22 Suppose a(Sr, 2),-L) is a canonical formula and f a cofinal 
subreduction of a frame 0 to # satisfying (CDC) for 2). Suppose also that ft is a 
subframe of 0 containing dom/. Then f is also a cofinal subreduction of ft to # 
satisfying (CDC) for 2). 
Proof Exercise. □ 
Theorem 16.23 Suppose L € NExtK4.3 and £*({?, 2), J.) L. Then £*(#,2), J.) 
is separated from L by the t-extension of$, for some type t for a/#, 2), _L). 
Proof Since £*(#, 2), J_) L, we have a Noetherian chain of clusters 0 = (V, S) 
separating a(Sr,2),.±) from L. By Theorem 16.20, there is an injective cofinal 
subreduction / of 0 to ^ satisfying (CDC) for 2). By the generation theorem, 
without loss of generality we may assume that / maps the root of 0 to the root 
offf. 
Let 0o = (Vo, So) be the (cofinal) subframe of 0 obtained by removing from 
0 all those points that are not in dom/ but belong to clusters containing some 
points in dom/, or formally 
V0 = V- U (C'(x)-dom/) 
x€domf 
and So is the restriction of S to Vo- By Lemma 16.22, the very same map / 
is an injective cofinal subreduction of 0o to satisfying (CDC) for 2), and so 
0o ft a(Sr,2),.L). It should be also clear that 0o is a reduct of 0, and hence 
0o ft L. 
Let C(xo),.. • ,C(xn) be all the distinct clusters in 0o such that 
n 
dom/ = (J C(Xi) 
t=0 
and C(xq) C C(xi)| C ... C C(xn)[. By induction on i we define now a sequence 
of frames 0o 2 • • • 2 ®n such that, for each i < n, 
(a) / is an injective cofinal subreduction of 0* to # satisfying (CDC) for 2); 
(b) between C(xi-i) and C{xi) the frame 0* contains either a finite 
descending chain of irreflexive points possibly ending with a reflexive one or an infinite 
descending chain of irreflexive points; 
(c) 0* |= L. 
Suppose 0*_i = (Vi_i, Si_i) has been already constructed and i < n. Take 
the chain <£* = (Wi,Ri) of clusters located between C(xi-1) and C(x^), i.e., 
Wi = C(xi)i - (C(xi)UC(Xi-i)i) and Ri is the restriction of 5^-1 to tV*. Three 
cases are possible. 

LOGICS CONTAINING K4.3 
503 
Case 1. <£* is a finite chain of irreflexive points. Then nothing should be done 
with <&i-1: we just put 0* = (5i- \. 
Case 2. (£* contains a non-degenerate cluster C{x) having only finitely many 
distinct successors j/i,..., j/m in (£*, all of them being irreflexive. Then we put 
(Si = (Vi, S'*), where = (V^_! - Wi) U {yi,..., ym, x} and Si is the restriction 
of Si_i to Vi. The conditions (a) and (b) are clearly satisfied by (Si. To show (c) 
it suffices to observe that (Si is a reduct of <Si_i (just map all the points in (Si to 
themselves and those removed from <Si_i to x) and use the reduction theorem. 
Case 3. Suppose Cases 1 and 2 do not hold. Then, since (B* is a Noetherian 
chain of clusters, it must contain an infinite descending chain Y of irreflexive 
points such that every point in Wi — Y sees all the points in Y. 
Put (Si = (Vi, Si) where Vi = (Vi-1 — Wi) UY and Si is the restriction of Si-1 
to Vi. Again (Si clearly satisfies (a) and (b). To prove (c) suppose (Si ^ ce(i}, (S, -L) 
for some a(fi, (B, -L) £ L. Then there is an injective cofinal subreduction g of (Si 
to 9) satisfying (CDC) for (B. Consider g as a cofinal subreduction of (Si_i to 9) 
and show that it also satisfies (CDC) for (B. Indeed, the closed domain condition 
could be violated only by a point in Wi — Y. So suppose z e Wi — Y and 
g(zJ\) = w|, for some {w} £ (B. Since g~1(w) is a singleton and Y C zj, there 
is a point y £ Y such that g(yJ\) = and y gL dom#, contrary to g satisfying 
(CDC) for € as a subreduction of (Si to 9). It follows from the definition that <Sn 
is the ^-extension of #, for some type t for a(Sr,®, -L). Hence <Sn a(Sr,®, _L). 
Besides, we have <Sn |= L. □ 
Thus, a frame separating a formula J_) ^ L from L £ NExtK4.3 
can be found in the class of ^-extensions of $ (t being a type for a(Sr,®,_L)), 
which is clearly recursively enumerable. We show now that there is an algorithm 
which, given a formula a(9), (£, _L) and a type t for a(Sr,®, J_), decides whether 
a(Sj, <E, -L) is valid in the ^-extension of $. 
Let k be the number of irreflexive points in 9), t = (£i,... ,£n) a type for 
a(Sr, ®, _L) and 0 the ^-extension of $ formed according to the formal definition 
above. Construct a cofinal subframe (Sfc of 0 by “cutting off” the infinite 
descending chains inserted in $ (if any) just below their k + 1th points and let X 
be the set of all these k + 1th points. In other words, 0^ is the s-extension of {?, 
the type s = (Cl? • • •, Cn) defined by 
* _ f k + 1 if & = uj 
\ & otherwise, 
and X = {a\+1 : & = cj}. It follows from the definition that 0^ is finite. 
Theorem 16.24 0 \/= a(Sj, (B, 1) iff there is an injective cofinal subreduction f 
of (5k to 9) satisfying (CDC) for (B and such that X n dom/ = 0. 
Proof (=>) Let 0 £*(#, (B, -L). By Theorem 16.20, there is an injective cofinal 
subreduction / of 0 = (V, S) to 9) satisfying (CDC) for (B. By Lemma 16.22, 
without loss of generality we may assume that if & = uj then VJ n dom/ = 

504 
THE DECIDABILITY OF LOGICS 
{a\,... ,<2^}, for some m < k. Now, by “cutting off’ all the infinite descending 
chains for & = u, just below oj^+1, we obtain <3*,, with / being an injective 
cofinal subreduction of <3* to 9) satisfying (CDC) for 3 and X D dom/ = 0. 
(<S=) If / is an injective cofinal subreduction of 3k to 9) satisfying (CDC) for 3 
and X fl dom/ = 0 then clearly / is also an injective cofinal subreduction of 3 to 
9). We show that it satisfies (CDC) for 3 as well. Only the points in the “cut off’ 
tails of infinite descending chains V* = {a\, al2l...} should be verified. So suppose 
m> h +1 and f{alm|) = set, for some {x} £ 3. Since {oj[.+1,..., alm}ndomf = 0, 
we must then have /(aj.+11) = set and, by (CDC), a\+l e dom/, contrary to 
X D dom/ = 0. □ 
Thus, given a type t for a(Sr, 2), _L) and a canonical formula a(fj, <£, _L), only 
finitely many steps is required to verify whether the ^-extension of # refutes 
a(Sj, <E, _L), and so we can prove the decidability of finitely axiomatizable logics 
in NExtK4.3 using Harrop’s argument. 
Theorem 16.25 All finitely axiomatizable normal extensions of K4.3 are 
decidable. 
Proof Exercise. □ 
16.4 	Undecidable calculi and formulas above K4 
We are going to construct an undecidable finitely axiomatizable logic in NExtK4 
by simulating the behaviour of Minsky machines in frames, describing points in 
those frames by modal formulas and using the undecidability of the configuration 
problems. 
With each Minsky program P and configuration (s,m,n) we associate the 
transitive frame $ depicted in Fig. 16.3. The meaning of points in $ is as 
follows. Its subframe consisting of the points bo (the only reflexive point in #), 
b\,..., 64 and r will be used for characterizing all points in # by variable free 
formulas. The points of the form e(t,fc,Z) represent configurations (t, k,l) such 
that P : (s,m,n) —► (t,fc,Z); e(£,fc,Z) sees the points a*, a£, of representing the 
components of (£, fc, l). Note that # contains the points aj for any i = 0,1,2 and 
j > -1, but only those e(£, fc, l) for which P : (s, m, n) —► (£, fc, l). 
Here are variable free formulas characterizing points in $ in the sense that 
each of these formulas, denoted by Greek letters with subscripts and/or 
superscripts, is true in $ only at the point denoted by the corresponding Roman letter 
with the same subscripts and/or superscripts: 
fio = OT A DOT, ft = □!, /?2 = OT A D2±, 
/?3 = 0/3lo A OPi A —102/3i , /?4 = 0/32 A 0/?3 A —«<C>2/?2 A —i<^>2/?3 , 
p = 0/?4, 71 = 0/?2 A ->02/32 A ->0/33, 72 = O71 A -i027i A ->0/33, 
73 = O72 A ~i0272 A “’0^3, <$1 = O/33 A “«02^3 A —>0/32, 

UNDECIDABLE CALCULI AND FORMULAS ABOVE K4 
505 
Fig. 16.3. 
62 = 06, A ~A ~'0/02, ^3 = O62 A -<0^62 A ~,0/32, 
ali = <>7i+i A 0(5i+i A ->027j+i A -i02<5»+i (i € {0,1,2}), 
aj = OaLi A f\ -iOa* ! A O^aLj A -.Oi+1at_1 (* € {0,1,2}, j > 0). 
i^k 
The formulas characterizing the points e(£,fc,Z) are denoted by €(t,a\,af) and 
defined as 
t 
e(t, al,af) = f\ Oa° A ->Oa?+1 A Oa£ A ->02a^ A Oaf A -<02af. 
i=0 
Lemma 16.26 For every triple (t,k,l) of natural numbers, 
(ii) y t= p A Oe(s, a*,, a2) -► Oe(t, a£, af) iff P : (s, m, n) 
(f,fc,i) 
-»• (t,k,l). 
Proof Straightforward. □ 
By Theorem 16.3, it follows immediately that, for appropriate program P 
and configuration (s,m,n), the logic of $ is undecidable. This fact, however, is 
not so interesting because such examples are easily obtained by the cardinality 

506 
THE DECIDABILITY OF LOGICS 
argument. What we really need is an undecidable calculus, and the connection 
of $ with P and (s,ra,n) will help us to construct one. 
As in Sections 6.1 and 6.3, we should be able to describe by means of formulas 
the movement down the chains aj, aj,... and a^,a\, — To this end we require 
the following formulas representing an arbitrary fixed position in these chains: 
7Ti = OaL1 A ->Oa°_1 A ->Oatl Api A -<Opi, n2 = 7ri(Opi/pi), 
n = Oc*2 x A A ~^Oa1_l Ap2A -iOp2, r2 = ri(Op2/p2). 
Lemma 16.27 For every valuation in # and every point x, 
(i) if x |= 7Ti then, for some i>0, 
{y = y 1= *i} = {«}}. {y ■ y\=*2} = {a*+1}; 
(ii) if x |= n2 then, for some i > 1, 
{y- y\=*2} = K1}, {y. y |= *1} = K-i}; 
(iii) if x |= Ti then, for some i> 0, 
{y: y f= n} = {a?}, {y ■ y h ^2} = {af+J; 
(iv) 	if x \= r2 then, for some i> 1, 
{y- y h T2} = {<*?}, {y ■ y hn} = {a?.,}. 
Proof Follows directly from the definition. □ 
Now, using 7Ti, 7T2, ti, t2 we define formulas representing an arbitrary fixed 
configuration: for t > 0 and i,j e {1,2}, 
t 
e(t,7Ti, Tj) = Oq:^ A -iOaJ+1 A A -nO2^ A Or^ A -i02Tj, 
k=o 
t 
e(t, 7Ti, qiq) = Oo:° A nOa°+1 A Oni A -<027ri A Ooq A -<02a:o, 
k=0 
t 
e(t, aj, ri) = Oa£ A -iOa*+1 A OaJ A ->02o:o A Ot\ A -><02ri. 
k=o 
The first formula represents an arbitrary configuration provided that for i = 2 
(or j = 2) its second (respectively, third) component is not 0. The other two 
formulas represent configurations whose second and third components are equal 
to 0, respectively. 
The meaning of these formulas in $ should be clear from the construction 
and Lemma 16.27; their syntactic meaning is clarified by 

UNDECIDABLE CALCULI AND FORMULAS ABOVE K4 
507 
Lemma 16.28 For all formulas p and let p = mean that p e K and 
<p* = <p{Okal/pi,Olal/p2}. Then 
(i) < =al, tt| = al+1; 
(ii) t* = of, r2* = af+1; 
(iii) (e(t,nuTj))* = <*?+(•,_!)), fori,j e {1,2}; 
(iv) (e(«,7ri,a§))* = e(i,a£,o£); 
(v) (e(t,al,n))* =e(t,ocl,af). 
Proof Exercise. □ 
We are in a position now to write down formulas Axl simulating instructions 
I of Minsky machines: 
• If I has the form t —> (£',1,0) then we put 
Axl = p A Oe(t,tti.ti) -»• Oe(£',7r2,ri); 
• If / is f —+ (t',0,1) then 
Ax/ = p A Oe(f,7ri,Ti) —► Oe(t', 71-1,72); 
• If / is t —► (f',—1,0) ((f",0,0)) then 
Axl = (pA Oe(t,7T2,T1) —► Oe(t',7Ti,Ti)) A 
(pAOe(t,aQ,Ti) -► Oe(t",aJ,ri)); 
• If / is t (t',0,-1) ((t",0,0)) then 
Ar/ = (/> A Oe(£,7Ti,T2) —► <>€(£', 7Ti, ri)) A 
(p A Oe(t,7rx,a0) Oe(t",7Ti,ag)). 
The formula simulating P as a whole is 
AxP = /\ Ax/. 
I€P 
Lemma 16.29 Suppose P : (s,ra, n) —► (£,fc,Z). Then 
p A Oe(s, a^, a2) -► Oe(f, ajt, of) 6 K4 © AxP 
Proof The proof proceeds by induction on the number of instructions used to 
compute (£, fc, Z) starting from (s, ra, n). The basis of induction is trivial and the 
step of induction follows from Lemma 16.28, according to which 
p A Oe(s', a^,, a£,) -+ Oe(f', a*,, a2) € K4 © AxP 
whenever {t',k',l') is obtained from {s',m',n') by applying a single instruction 
in P. □ 

508 
THE DECIDABILITY OF LOGICS 
To obtain the converse of Lemma 16.29, it suffices to observe that the 
following lemma holds: 
Lemma 16,30 # \= AxP. 
Proof Straightforward using Lemma 16.26. □ 
As a consequence of Lemmas 16.26, 16.29 and 16.30 we derive 
Lemma 16.31 For every P, (s,m,n) and (t, k, l), 
p A Oe(s,aJ„,a^) Oe(t,al,af) € K4 @ AxP iff P : (s,m,n) -> (t,k,l). 
Recall now that we have effectively constructed our formulas for given 
arbitrary P and (s,m,n). So Theorem 16.2 provides us with 
Theorem 16.32 (i) There is no algorithm which, given modal formulas ip and 
\p, could decide whether \p e K4 0 ip. 
(ii) There is no algorithm which, given ip and 'ip, could decide whether ip is 
valid in all transitive Kripke frames validating (p. 
This result can be considerably strengthened by fixing appropriate ip or ip. If 
we take P and (s,m,n) for which the second configuration problem is undecid- 
able then, by Lemma 16.31, we obtain the following: 
Theorem 16.33 There is a program P such that the calculus K4 0 AxP is 
undecidable; besides, there is no algorithm which, given a formula 'ip, could decide 
whether ip is valid in all Kripke frames for K4 0 AxP. 
Say that a formula xp is undecidable in (N)ExtL if no algorithm can recognize, 
for an arbitrary (p, whether \p e L + (p (respectively, \p e L 0 ip). To find an 
undecidable formula in NExtK4 we require two more lemmas. 
Lemma 16.34 For every triple (t,k,l) such that P : (s,m,n) (t,k,l), 
3 t= (pAOeis^^al) -» Oe(t, at, a?)) -» ^p. 
Proof Follows immediately from Lemma 16.26. □ 
Lemma 16.35 P : (s,m,n) —> (t,k,l) iff 
-<p e K4 e AxP ®{p A Oe(s, a^, o£) -► Oe(t, a\, a?)) -* ~^p. 
Proof (=>) follows from Lemma 16.31 by modus ponens and (<$=) from Lemmas 
16.30, 16.34 and the fact that r ->p. □ 
As a direct consequence of Lemma 16.35 and Theorem 16.3 we obtain 
Theorem 16.36 The formula -*p is undecidable in NExtK4. 
Remark According to Theorem 16.36, even variable free formulas may be 
undecidable in NExtK4. However, there is no undecidable calculus in NExtK4 

UNDECIDABLE CALCULUS AND FORMULA IN EXTINT 
509 
with variable free axioms. The undecidable calculus in Theorem 16.33 was 
constructed by adding to K4 an axiom in two variables p\ and P2- In fact even 
one variable is enough: we can identify pi and P2 and change the substitution in 
Lemma 16.28 to (O+aJ —► Okal) A (O+oio —► O^qj^/pi. 
It is worth noting that in ExtK4 even the formula _L turns out to be 
undecidable (though it is clearly decidable in NExtK4). Indeed, declare the root r in 
the frame $ to be its only actual world. Then we have 
Lemma 16.37 For every triple (t,k,l) such that P : (s,ra,n) (t,k,l), 
(S,r) \= (/)AOe(s,al,,aJ) -> O->1. 
Using this result we obtain 
Lemma 16.38 P : (s,ra,n) —► (t,k,l) iff 
1 	€ K4 + AxP + (pAOe(s,a^,a£) -> Oe(t,al,af)) -» _L. 
Using once again the undecidability of the second configuration problem we 
finally arrive at 
Theorem 16.39 The formula _L is undecidable in ExtK4, i.e., no algorithm 
can recognize, given a formula ip, whether the logic K4 + ip is consistent 
The only property of _L we used while proving Theorem 16.39 was that it is 
refuted at r. This means that any formula refutable at r is undecidable in ExtK4. 
In particular, undecidable are all formulas <p such that K4+<p D S4. By replacing 
r with a reflexive actual world (which is not essential for our construction), we see 
that all formulas <p axiomatizing over K4 extensions of GL are also undecidable 
in ExtK4. 
16.5 	Undecidable calculus and formula in Extint 
This section should be considered as a system of instructions for transferring 
the results of the preceding one to superintuitionistic logics. We confine 
ourselves only to describing the construction, formulating lemmas and theorems 
and pointing out their modal prototypes. The reader who has understood the 
construction of the undecidable modal calculus should encounter no fundamental 
difficulties in the intuitionistic case. 
Fix an arbitrary Minsky machine P and an arbitrary configuration (s,m, n) 
and let $ be the intuitionistic Kripke frame depicted in Fig. 16.4, with the point 
e(t,k,l) occurring in it iff P : (s,m,n) —► (t,k,l). To characterize the points in 
# we require the following formulas: 
<*-3 = P6 -L, P-3 = 96 -► -L, 
2 	=P5->P6Va°3, 0°_2 = q5 -> q6 V 3, 

510 
THE DECIDABILITY OF LOGICS 
r 
Fig. 16.4. 
<*L3 =P4 ->P5 Va“2, Pl3 = qA -► q5 V /3°2, 
<*l-2 =P3 ->P4 VaL3, P-2 = 93 94 V /3i3, 
a-3 =P2 ^P3 Vai2, /£3 = 92 -» 93 V /3i2, 
a?.2 = Pi ^ P2 V a?.3, /3* 2 = 9i -> 92 V /£3, 
7 = -'96 ->Pi V al2, 6 = -.p6 -► qi V pl2, 
p = /y V (5. 
It is not hard to see that a Kripke frame refutes p iff it contains a subframe of the 
form shown in Fig. 16.5 such that the points c and d have no common successors 

UNDECIDABLE CALCULUS AND FORMULA IN EXTINT 
511 
a2 n2 nl n1 n° n° 
U_ 2 (*_ 3 a_2 u_2 ^—3 
o HD HD HD HD HD 
■HD HD HD HD HD HD 
b2_2 b2_z bl__2 b]_ 3 6^.2 ^—3 
Fig. 16.5. 
in it. Clearly, # contains only one (up to the evident symmetry) subframe of that 
sort: its points are denoted by the same symbols as the corresponding points of 
the frame in Fig. 16.5. So if p is refuted in $ under some valuation, the points 
in $ can be characterized as follows: 
{x : x\Y- a)} = {a}}, {x : x \ &)} = {&}} (i G {0,1,2}, j > -3), 
{x : x 7} = {g}, {x : x 6} = {d}, 
where x |^= —► -0 means a: |= and a; -0, and for j > —2, t, fc, l > 0, 
«°+i = # - V #_lf #+1 = a?-/3°v alu 
oij+i = a2-3 A /?-3 A $ -» v $-1 V alig V /?i3, 
/3)+i = a£3 A 013 Aaj^ p) V a)_x V ai3 V /?i3, 
a2j+1 = 7 A tf A P2 -> o?, V v a* 3 V /£3, 
$+i = 7 ASA<rf->P?V a2j_x V a£3 V /3i3, 
c(*. “fc>«?) = «?+i A /3?+i A <4+1 A /4+i A <4+1 A A+i -» 
a? V V aj V $ V a? V tf. 
(In fact, the first two conjuncts and the last two disjuncts in a} and /?}, for 
z = l,2, are redundant; they are added only to simplify the proof a bit.) 
The intuitionistic counterparts of the formulas 7r* and t* from the preceding 
section are: 
7T_2 = f, 7t'_2 = 5, 7T_i = p, 7T^_x = q, 
7Ti+i = a?.3 A /?^3 A < -+ 7Ti V <_! V ai3 V /?i3, 
7T-+1 = a£3 A P2 3 A 7Ti -*■ 7r' V 7Ti_i V al_3 V /?I3, 

512 
THE DECIDABILITY OF LOGICS 
T-2 = r', t'_2 = s', r_! = p', t'_1 = q', 
ri+i =7 AS At< -> nV T'_j v a£3 V f32_ 3, 
Ti+i = 7 A 6 A n -> rt' V Tj_i V a£3 V @2_3 (i > -1). 
Using them we define, for £ {1,2} and t > 0, 
e(t, 7Ti, Tj) = oPt+l A /3t°+1 A 7Ti+i A tt'+1 A rj+i A rj+1 -► 
V /3° V 7rt V tt' V V rj, 
e(t, 7Ti, a^) = a°t+1 A /3t°+1 A tt2 A tt2 A a\ A f3\ -► 
a°t V /3t° V 7Ti V Tr[ Vq§V /?§, 
e(f, <*o, n) = a?+i A $+1 A aj A /3| A r2 A r2 —> 
a? V /3t° V aj V $ V n V r(. 
Finally, we define the formulas simulating the instructions I of a Minsky machine 
P: 
• if I is of the form t —» (t', 1,0) then 
Ac/ = e({')ir2,ri) -> €(t,7ri,ri) Vp; 
• if / is £ —> (t', 0,1) then 
Axl = e(t',7ri,T2) -> e(t,7Ti,Ti) Vp; 
• if / is t —> (t', —1,0) ((t",0,0)) then 
Axl = (c(tr,TTi,Ti) ► c(t, 7T2, Ti) V p) A 
(«(<", <*o> T0 e(<, <*0. n) V p); 
• if I is t —> (t', 0, — 1) ((t", 0,0)) then 
Axl = (e(f',7ri,Ti) -+ e(t,iti,T2) V p) A 
(e(t",ni,al) e(t,ni,al) V p), 
and the formula simulating the behavior of P itself: 
AxP = Axl, 
ieP 
Denote by <p* the result of substituting the formulas a}_3, /?*_3, 2, /3*_2> 
(Xj_3) 3, a^_2, /?J-2 instead of the variables r, s, p, <7, r', s', p', qf in <p, 
respectively. 

SEMANTICAL CONSEQUENCE ON FINITE FRAMES 
513 
Lemma 16.40 The following equivalences are in Int: 
(i) {e(t,7rk,Ti))* «-> €(t,al1+fc_1,a?+i_1); 
(ii) (c(<,7ri,a§))* e{t,a},al); 
(iii) (e(«,Q!o.'ri))* <-► e(t,<4,a]). 
Lemma 16.41 $ f= AxP. 
As a consequence of these two lemmas we have 
Corollary 16.42 e(t, a?) —> e(s, o^V p E Int + AxP if and only if 
P : (s,ra,n) —► (t,k,l). 
Now if we take a machine P for which the configuration problem is 
undecidable, Corollary 16.42 will mean that the calculus Int + AxP is also undecidable. 
Thus we obtain 
Theorem 16.43 There is a program P such that the calculus Int + AxP is 
undecidable; besides, there is no algorithm which, given a formula 0, could decide 
whether 0 is valid in all Kripke frames for Int + AxP. 
Observe also that the following statement holds. 
Lemma 16.44 For every triple (t, fc, l) such that P : (s, m, n) (t, k, l), 
5 1= (e(*» <4. Olf) -> £(5> «m. «n) V P) -> P- 
From this and the preceding lemmas in the same way as Lemma 16.35 we 
derive 
Lemma 16.45 P : (s,m,n) —► (t,k,l) iff 
P G Int + AxP + (e(t, al,aj) -> e(s, a^, a2n) V p) -> p. 
Thereby, we prove 
Theorem 16.46 The formula p is undecidable in Extint. 
16.6 	The undecidability of the semantical consequence problem on 
finite frames 
When constructing undecidable calculi in Sections 16.4 and 16.5, we were forced 
to use infinite frames simply because every finitely approximable calculus is 
decidable. So for the present nothing can be said about the decidability of the 
semantical consequence on finite frames, i.e., about the decidability of the 
relation (p |=fin 0, which means that 0 is valid in all finite frames validating <p. 
In this section we modify the construction of Section 16.4 to prove the 
undecidability of f=/m- For purely technical reasons it will be more convenient for us 
to deal with only finite transitive irreflexive frames, i.e., to consider the relation 
Id A <p [=/in 0* 
Let $ be the transitive irreflexive frame shown in Fig. 16.6. Its intended 
meaning will be defined a bit later and meanwhile we introduce some formulas 

514 
THE DECIDABILITY OF LOGICS 
Fig. 16.6. 
characterizing points in (We do not actually need # in this part of the proof, 
but it is helpful to have it at hand.) Put 
p' = m2J_ -4 DpV D-ip, p = □ pf, 
Clearly x ^ p and y p' under some valuation in £ iff x = r, y = rf and either 
&o N p or b\ ^ p, b\ (= p. For the reason of symmetry we will consider 
only the former case. Now we put 
Po = D-L Ap, p\ = □! A ->p, 
p{ = D*± A O^pl A ^Opl_i (i G {0,1}, 1 < j < 6), 
al = OPi+3 A 0/3j+3 A Di+4± (0 < i < 3), 
a} = A -0^+1a^ A f\ (0 < i < 3, j > 0), 
k^i 
t 
e(t, al,atj) = f\Oaf A nOaf+1 A Oa£ A 02al A Oaf A ->02af 
i=0 
where £, /c, l > 0 and again the Greek letters, denoting formulas, correspond to 
the Roman letters for points in #. The formulas describing an arbitrary position 

SEMANTICAL CONSEQUENCE ON FINITE FRAMES 
515 
in the chains al0, a\,..for i = 1,2,3, and an arbitrary configuration are defined 
in the same way as in Section 16.4: 
m = O+aJ A ^Oao A ->OaQ A -iOal A pi A -iOpi, 
7T2 = OaJ A -iOqq A -iOao A A A ->02pi, 
T\ = 0+ao A -iOao A A ^ao A P2 A -|<>P2, 
T2 = Ockq A -iOao A —»<C>o:q A -iOajj A Op2 A -|02p2, 
<ji = A -iOao A -iOaJ A —lOot^ A P3 A -iOp3, 
<72 = OcHq A ~~1 A 1 A ~~1 A ^P3 A ~~1 ^2p3 5 
t 
e(t,7Ti,Tj) = ^ Oajj! A -iOaJ+1 A A ->027r* A Or^ A -i027j, 
k=o 
t 
e(t, 7Ti,ao) = /\ Oa^l A -iOaJ+1 A <>7ri A -i027Ti A Oao A ->02ao, 
k=o 
t 
e(t,aJ,Ti) = /\ Oa° A ^Oa£+1 A OaJ A -n02aj A Ot\ A -i02ri, 
k=o 
where t > 0, i,j E {1,2}. The following lemma is proved in the same way as 
Lemma 16.28. 
Lemma 16.47 For all formulas <p and ip, let <p = xp mean that IH+(<p +-> ip) G 
GL and ip* = <p{Okal/pi, 01Oq/p2, <$mao/p3}- Then 
(i) ■kI = a\, -k\ = a\+l; 
(ii) t* = of, r2* = of+1; 
(iii) = C$n, *2 = «m+l/ 
(iv) (e(t,7r,,Tj))* = fori,j <E {1,2}; 
(v) (e^.TTi.ag))* = e(t,a^,ag); 
(vi) (e^.aj.n))* =e(t,al,af). 
The formulas Axl simulating instructions we are going to use now have an 
essential difference from those in Section 16.4: they not only reflect the 
transformation of configurations but also calculate the number of steps in computations. 
They are as follows: 
• If I is t —> (£', 1,0) then we put 
Axl = ->p A 0(e(t,7Ti,ri) A 0<ji A -i02<7i) A 0(72 —> 
0(e(t', 7r2, Ti) A Ocr2 A -h02<72); 

516 
THE DECIDABILITY OF LOGICS 
• If / is t —> (tf, 0,1) then 
Axl = ip A 0(€(£,7Ti,Ti) A 0(71 A ->02<7i) A 0(72 
0(e(t', 7Ti, T2) A 0(72 A ->02(72); 
• If / is t -> (£', -1,0) ((£", 0,0)) then 
Ax/ = (“ip A 0(c(t, 7T2, Ti) A 0(71 A ->02(7l) A 0(72 
0(e(t',7Ti,Ti) A 0(72 A ->02(72)) a 
(-<p A 0(e(£, aj, ti) A 0(71 A ->02(7i) A 0(72 —► 
0(e(t", aj, Ti) A 0(72 a --02(72)); 
• If / is t —> (£', 0, —1) ({£", 0,0)) then 
Ax/ = (->p A 0(e(£, 7Ti, 72) A Oai A -«02(7i) A 0(72 —► 
0(6(t/,7Ti,T2) A 0(72 A ~<02(72)) A 
(-ip A O(e(£,7ri,ao) A Oai A ->02(7i) A 0(72 —3► 
0(c(t",7Ti,ao) A 0(72 A -<02(72)). 
And again for a Minsky program P we define AxP = /\iGP But this time 
we are after another fish. What we really need is the following two formulas: 
<p(P) = la A AxP A A A v, 
and 
*0(51, m, n) = ipA 0(e(si, a^, a2) A Oaf A ->02af) —> 
->O(6(S0,7Tl,n) A 0(71 A ~'02(71), 
where 
A = _,(~'P A 0(0qq A -nOao A ^OaJ A "■OaQ A □+r A —*q) A 
0(0qq A -<Oao A -<Oao A ->OaQ A □ A —*r)), 
v = —*(—*p A 0(g A 0(71 A ~<02(71 A OaJ A Oqq A Oqq) A 
0(-># A 0(71 A -i02(7i A OaJ A Oqq A Oqq)) 
and si and sq are the initial and final states, respectively. The meaning of A is 
that if a frame validates la A A and at a point x the formula p is false under some 
valuation then the set of points in x| at which Oaj) A ->Oao A ->Oao A ->Oao 
is true is strictly linearly ordered by the accessibility relation of the frame. Our 
main technical result is 

SEMANTICAL CONSEQUENCE ON FINITE FRAMES 
517 
Lemma 16.48 <p(P) \=fin V>(si>m,n) iff Pro9ram Pj having started with 
the configuration (si,m,n), never comes to the final state so. 
Proof Let us begin with (*£=); it is this part of the lemma that uses specific 
features of finite frames. Suppose the machine P starts at (si,ra, n) and works 
forever. To show that <p(P) \=fin assume otherwise. Then there is a 
finite frame 0 = (V, S) such that 
0 |= v*p) 
(16.2) 
but, for some a € V under some valuation in 0, a ^ ^;(si,m,n), i 
i.e., 
<2 p, 
(16.3) 
a |= 0(e(si,aj„,a£) A OaJ A -^02a?), 
(16.4) 
a |= O(e(so, tti, 'J'l) A Oai A ->02<ri). 
(16.5) 
(16.4) means that there is b G a] such that 
b |= e(si,a4,a:2), 
(16.6) 
b |= 
(16.7) 
b ft 02af, 
(16.8) 
while (16.5) implies that for some c € a|, 
c |= e(so,7ri,n), 
(16.9) 
c |= Oai, 
(16.10) 
c ft 02ai. 
(16.11) 
It follows from (16.7) that there is a point, call it af, such that bSa\ and a? |= af, 
I.C., 
ai N O<*0 A —'Oqq A ~'OaJ A —'Oa^, 
(16.12) 
al£02al 
(16.13) 
Similarly, by (16.10) we have a point x e c\ such that x |= <7i, i.e 
*> 
x |= Oqq A ~>Oao A ~>Oao A ->Oao, 
(16.14) 
x |= P3 A ->Op3* 
(16.15) 
By (16.2), (16.3) and the property of A mentioned above, the set of points 
accessible from a at which the conditions of the form (16.12), (16.14) are satisfied 
form a strict chain ... Sa^Saf, whose last point is, by (16.13), af. The 

518 
THE DECIDABILITY OF LOGICS 
points in the chain may be characterized by the formulas af in the sense that 
af f= af and af ^ Oaf, for 1 < i < k. 
By (16.14), x = af for some l G {l,...,fc}, and so, by (16.14), (16.15) and 
(16.11), af (= (Ji, c |= Oaf, c ^ 02af. Thus, we have managed to identify x 
with some af and now, using the conjuncts of </?(P) and the finiteness of 0, we 
will go down step by step from af to x = af. 
Suppose P starts working at (si, m, n) and produces the infinite computation 
(si,m, n) - (si,rai,ni), (s2)m2,n2), (53,m3,n3),... in which s* = s0 for no 
z > 0. In this computation only the first l steps are of importance for us. Notice 
that for every z G {1,..., k - 1}, (16.2) yields 
a |= 0(e(sj,a£,.,a£.) A Oaf A ->02af) 
0(e(si+1,a^.+1,a2.+1) A Oa3+1 A ->02q;3+1). 
Using (16.4) and MP, we obtain then, for 1 < i < k — 1, 
a |= 0(e(sm,ail.+1,a2.+1) A Oaf+1 A -■02af+1) 
and in particular 
a \= 0(e(s/,a^ni,o;2J) A Oaf A -.O2af). 
The latter condition means that there is a point d G a] such that 
^ N e(si>aTOj>Q:n,)> (16.16) 
d 1= Oaf, (16.17) 
d £ 02af. (16.18) 
It follows from (16.17) and (16.18) that dSaf and -idSaf+1. Since among af,..., af, 
there is only one point where is true, with the help of (16.14) and (16.15) we 
obtain that d |= Ocri A -•02<ji. 
Now let us put the conditions we need together. From (16.9), (16.10) and 
(16.11) we derive 
c (= 0(71 A ->02a\ A OaJ A Oao A Oao (16.19) 
and from (16.16) and (16.17) 
d f= 0(71 A -i02(7i A OaJ A Oa^ A Oa^. 
Since by (16.9) and (16.16), 
c\= f\Oaf A-*Oa°So+1, d \= f\ Oaf A -.Oa° 
7=0 7=0 
(16.20) 

ADMISSIBLE AND DERIVABLE RULES 
519 
and si ^ Sq, the points c and d must be distinct. Therefore, we may define a 
valuation in 0 so that c f= q, d ^ q. Together with (16.19), (16.20) and (16.3) 
this gives a ^ v, contrary to (16.2). Thus indeed we have <p(P) f= fin xp(s\,m, n). 
Now we prove the contraposition of (<=). Suppose that P starts at (si, m, n) 
and reaches the final state So via the computation 
(si,m,n) = (si,mi,m),... ,(sk,mk,nk) = (so,mk,nk) ■ 
We are going to separate <p(P) from xp(s\,m,n) by the finite frame $ shown 
in Fig.16.6, where s = max{si,..., s^}, m' = max{mi,..., rrik} and m! — 
max{ni,... First, it is readily checked that # |= </?(P). On the other 
hand, we can define a valuation 93 in # so that 9J(p) = {6j}, 2J(pi) = 
2J(P2) = {flraj, 2J(P3) = {ak} and then r ¥=■ ^(si,»71, n), i.e., ^ ^ tp{si,m,n). 
□ 
Now recall that we associated ip(P) and ^(si, m, n) with a program P and a 
configuration (si,m, n) in an effective way. So Theorems 16.4 and 16.5 provide 
us with the following results. 
Theorem 16.49 (i) There is a formula <p such that the problem of recognizing, 
for an arbitrary formula ip, whether ip \=fin *0 is algorithmically undecidable. 
(ii) There is a formula ip such that the problem of recognizing, for an arbitrary 
formula tp, whether p\=.^in^p is algorithmically undecidable. 
Thus the semantical consequence problem on finite frames is undecidable. 
Moreover, since the set {(</?, xp) : </? \/=fin } is clearly recursively enumerable, we 
also have 
Corollary 16.50 (i) The set {(</?, xp) : ip |=/m } is not recursively enumerable. 
(ii) There is a formula <p such that the set {xp : <p \= fin xp} is not recursively 
enumerable. 
(iii) There is a formula xp such that the set {</?: ip |=/m *0} is n°t recursively 
enumerable. 
16.7 	Admissible and derivable rules 
Admissible and derivable rules are used for simplifying the construction of 
derivations. Derivable rules may replace some fragments of fixed length in derivations, 
thereby shortening them linearly. Admissible rules, which are not derivable, in 
principle may reduce derivations even more drastically. In this section we 
consider the algorithmic problem of recognizing whether a given inference rule is 
admissible or derivable in certain modal and si-logics. 
To begin with, let us observe that even in tabular logics the admissibility 
problem is not trivial. 
Example 16.51 Let L = Log(oo). We show that L is not structurally complete, 
namely that the inference rule Op A 0->p/_L is admissible but not derivable in 
the tabular logic L. 

520 
THE DECIDABILITY OF LOGICS 
Since L is consistent, this rule is admissible iff 0</?A0-k/? ^ L for any formula 
(p. Suppose on the contrary that 0<pA0-i<p e L for some <p. Since L C Triv, both 
formulas Oip and O -up are in Triv and so <p, -up E Triv because Op ->pE Triv, 
contrary to Triv being consistent. Thus our rule is admissible. 
By the deduction theorem for S4 C L, the rule Op A 0-p/_L is derivable iff 
0(D->pV Dp) E L, which is not the case because 0(D-ip V Dp) is clearly refuted 
in the two point cluster. 
Thus the decidability of a logic and the deduction theorem cannot help us in 
general to recognize admissible rules. Yet the admissibility problem for tabular 
logics turns out to be decidable. 
Theorem 16.52 For every tabular logic L, there exists an algorithm deciding 
whether a given inference rule is admissible in L. 
Proof We consider only L E NExtK; other logics are treated analogously. That 
a rule <p(pi,... ,Pn)/^(Pi, • • • ,Pn) is not admissible in the logic L determined by a 
finite algebra 21 means that there are formulas Xi(<7i> • • • > Qm), • • •, Xn{Qu • • •, Qm) 
such that 
= ¥>(xi»---,x») € L, ip’ = &L, (16.21) 
i.e., 211= <p' and 21 Without loss of generality we may assume m < |2l| (for 
otherwise we could identify some of the variables <7i,... ,<7m). Since 21 is finite, 
there are only finitely many pairwise non-equivalent in L formulas in < |2l| 
variables, and we can effectively construct them. Therefore, trying all possible 
n-tuples Xi> • ■ • > Xn of these formulas, we either satisfy (16.21), and then p/'i/j is 
not admissible, or do not satisfy it, which means that the rule is admitted by L. 
□ 
Notice that the criterion of admissibility for tabular logics used in the proof 
above can be clearly extended to arbitrary logics in the following way. 
Theorem 16.53 A rule ip/ip is admissible in a logic L in NExtK or Extint iff 
the quasi-identity <p = T —> -0 = T is true in 21^(n) for every n < u> iff for any 
n <oo and any valuation 2J in 21 l(^); = T implies 2J(*0) = T. 
Proof Exercise. □ 
In general this criterion is not effective. However, we can try to “effectivize” 
it using the effective description of the upper part of the universal frames $L{n) 
obtained in Section 8.7, at least for some well-behaved logics. 
First we show that dealing with normal modal logics, it is sufficient to 
consider inference rules of a rather special form. Let <p(#i,... ,#2n+2) be a formula 
containing no □ and O and represented in the full disjunctive normal form (see 
Exercise 1.2). Say that an inference rule is reduced if it has the form 
<P(Po,Pi, ■ ■ • ,Pn, Opo, Opi,..., Opn)/p0. 

ADMISSIBLE AND DERIVABLE RULES 
521 
Theorem 16.54 For every rule p/'ip one can effectively construct a reduced rule 
p'/vp' such that p/'ip is admissible in a logic L £ NExtK iff p'/'ip' is admissible 
in L. 
Proof Observe first that if p and 'ip do not contain p then p/'ip is admissible 
in L iff p A ('ip p)/p is admissible in L. So we can consider only rules of the 
form <p/po- Besides, without loss of generality we may assume that p does not 
contain □ (recall that Op = ->□-></?). 
With every non-atomic subformula x of (/? we associate the new variable px. 
For convenience we also put px = pi if \ = Pi and Px — -L ^ X = -L. We are 
going to show now that the rule 
P<paA{Px ^Pxi ©Px2 : X = Xi © X2 € Suby?, ©€ {A,V,->}}A 
A {Px ” °Pxi : X = Oxi e Sub(/j}/p0 (16.22) 
is admissible in L iff ip/po is admissible in L. For the sake of brevity denote the 
antecedent of (16.22) by p". 
(=>) Since every substitution instance of <p"/po is admissible in L, the rule 
p A /\x€ subv>(x x)/Po (obtained from it by replacing each px with \) and so 
p/po are also admissible in L. 
(<£=) Suppose p/po is admissible in L and a substitution instance p"s of p" 
is in L. Let s = {olx/px : x £ Sub<p}. By induction on the construction of \ 
one can readily show that ax \8 £ L. Indeed, the basis of induction is trivial 
and the step of induction follows immediately from the equivalent replacement 
theorem. Therefore, a<p is equivalent in L to ps. Since pns £ L, we must have 
in particular p^s = £ L, from which ps £ L and so p0s £ L. Thus p"/po is 
admissible in L. 
The rule <p"/po is not reduced, but it is easy to make it so simply by 
representing p" in its full disjunctive normal form p', treating subformulas Op* as 
variables. □ 
From now on we will deal with only reduced rules different from -L/po (which 
is clearly admissible in any logic). Let Vj <Pj/Po be a reduced rule, in which each 
disjunct pj is a conjunction of the form 
-ioPo A ... A ->mpm A -i°Op0 A ... A ->mOpm, (16.23) 
where each and is either blank or It will be convenient for us to identify 
such conjunctions with the sets of their conjuncts. Now, given the non-empty set 
W of conjunctions of the form (16.23) occurring in the premise of the rule under 
consideration, we define a frame # = (W, R) and a model 9Jt = (#, 9J) on it by 
taking 
PiRpj iff Vfc G {0,..., m}(-iOpfc £ pi —> -iOpk £ pj A -pfc £ Pj) A 
3k £ {0,..., m}(iOpfc G Pj A Opk £ pi), 

522 
THE DECIDABILITY OF LOGICS 
®(Pfc) = Pk € ¥>»}• 
It should be clear that $ is finite, transitive and irreflexive. 
We are in a position now to formulate a criterion for admissibility of reduced 
rules in GL. 
Theorem 16.55 A reduced rule Vj <Pj /Po is n°t admissible in GL iff there is 
a model DJI = (#, 93) defined as above on a set W of conjunctions of the form 
(16.23) and such that 
(i) -ip0 G ipi, for some ipi G W; 
(ii) (Pi\=y>i, for every w G W; 
(iii) for every antichain a in $ there is (pj G W such that, for each k G 
{0,..., m}, ipj |= Opk iff <pi |= 0+pk for some <pi G a. 
Proof (=>) Suppose 0o>..., 0m are formulas in variables q\,..., qn such that 
Vj <Pj € GL and pj i GL, where x* denotes the formula xi^o/Po, ■ • •, ipm/Pm}- 
This is equivalent to 93lGL(n) 1= Vj <Pj an<i ®^GL(n) W Po (recall that 9JIgl (n) 
is the n-universal model for GL introduced in Section 8.7). Define W to be the 
set of those disjuncts ipj in \Jj <pj whose substitution instances </?!■ are satisfied 
in 9ftGL(n)- Clearly W ^ 0. Let us check conditions (i)-(iii). 
(i) Take a point x in DJIq^u) which p£ is false. Since \J ■ </?!• is true in 
9JlGL(n)? we must have x |= <p* for some i. One of the formulas pj$ or ->Pq is a 
conjunct of <p*. Clearly it is not p£. Therefore, ->p0 G </?*. 
(ii) It suffices to show that, for every cpi eW and k G {0,..., m}, (pi |= Opk 
iff Opk G <pi (that <pi |= pk iff Pk £ <pi follows from the definition of 93). Suppose 
<Pi i= Opk. Then there is </?j G W such that ipiRipj and </?j |= pk. By the 
definition of 93, this means that pk G <Pj and so, by the definition of R, Opk G <p*. 
Conversely, suppose that Opk G ty. Then x \= <p* and, in particular, x |= Op£ 
for some x in 9ftGL(n)- Let V be a final point in the set {z G x\ : z |= p£}. Since 
97tGL(n) ls irreflexive, we have y (= pj^, y Op£ and y (= <p!• for some ipj G W. 
It follows that ipiRipj and ipj |= p^, from which </?* (= Opk. 
(iii) Let a be an antichain in $. For every <p* G a, let Xi be a final point in the 
set {y G WglM : p |= <p*}. It should be dear that the points {#* : </?* G a} 
form an antichain b in SrGL(n) an<i so, by the construction of SrGL(n)5 there is a 
point y in SrGL(n) such that y]= b|. Then the formula tpj G W we are looking 
for is any one satisfying the condition y |= </?!•, as can be easily checked by a 
straightforward inspection. 
(<*=) Let DJI be a model meeting (i)-(iii). To prove that \fj <Pj/Po is not 
admissible in GL we require once again the n-universal model 9JlGL.(n)> hut this 
time we take n to be the length (the number of symbols) of the rule. By 
induction on the depth of points in SDT one can readily show that DJI is a generated 
submodel of 93lGL.(n) (recall that we defined DJI as a model of the language with 
the variables Po, • • • ,pm)- 
Our aim is to find formulas 0o,..., 0m such that 9#GL(n) f= \fj<Pj and 
9Kgl(™) ^ Po (here aSain X* = x{0o/po, • • • ,0m/Pm})- Loosely, we are going 
to extend the properties of DJI to the whole model DJIq^u). We take the sets 

ADMISSIBLE AND DERIVABLE RULES 
523 
{p{} in SglM and augment them inductively in such a way that we could 
embrace all points in and retain the property (ii). 
Fix any point pio of depth 1 in the model DJI and denote by p®0 the set 
(^GL(n) “ t?"1) u {<A0}- For the remaining pi in W, we put p? = {</?*}. This is 
the basis of our inductive construction. 
Suppose we have already constructed sets p\ for l > 0. Take any set X of 
l -f 1 points in W and associate with it a single formula pj satisfying (iii) for 
the antichain consisting of all the first (minimal) points in X with respect to R. 
Define an auxiliary set [X] as follows. Using the abbreviation 
X1 = - (J n P| <p\ 1 n - |J <p\i, 
<Pi£W iPi€X v>i&X 
we put [X] — X^ if the condition 
Vfc G {0,..., m}(-nOpfc G pj -> ~-pk G pj) (16.24) 
holds and [X] = — X^ [ otherwise. Now we define p1*1 by adding to </?*• all 
sets [X] with which pj was associated (if pj was not associated with any set 
then </?*+1 = (fj). Clearly this process terminates as far as all possible subsets of 
points in W are exhausted, i.e., in N = \W\ steps. 
It follows directly from the construction that we have 
Lemma 16.56 (i) plj C p1^1 for any pj G W and l < N; 
(ii) plj G PqlW for any pj eW and l < N; 
(iii) p\ fl plj = 0 for any distinct pi} pj G W and l < N. 
Lemma 16.57 For every x in DJIq^u) and every l < N, if x & p| Plj ^ien 
x ^ PU* for some set X of l + 1 points in W. 
Proof The proof proceeds by induction on l. Suppose l = 0 and x g p| Vj- 
By the definition of p®0 and p? for i ^ z0, all points in are in Vj- 
So x is of depth > 1. But then x sees a point of depth 1, say y G p® for some 
Pi G W, from which x G p®j. 
Let us assume now that the claim of our lemma holds for l < N — 1 and 
x & ^+1* By Lemma 16.56 (i), it follows that x £ H^gw Vj and so> 
the induction hypothesis, x G p|^.GX f°r some set X of l -f 1 points in W. 
Let pj be the point associated with X and consider the set [X]. 
Suppose (16.24) holds for pj. This means that if x £ plk[ for all pk & X then 
x G [X] and so x G p1^1, which is a contradiction. Therefore, x G plkl for some 
Pk & X. Put Y = X U {pk}- Then we have x G p|^.Gy <p\l and, by Lemma 16.56 
(0) x e f\,i€yv4+1l- 
Suppose now that (16.24) does not hold. If x ^ plk[ for all pk & X then 
either x G [X], which as we know leads to a contradiction, or x G XU, ie., there 
is y G x| such that y U^gwV^, V € p\[ for all pi G X and y <£ p\[ for 

524 
THE DECIDABILITY OF LOGICS 
(fi £ X. Of all possible y with these properties we take a final one with respect 
to RqBy the definition of [X], we have y £ [X] and so y £ <p^+1. Then 
x £ <p1^11 and, since <pj is associated with X and does not satisfy (16.24), there 
is pk such that pk £ <pj but pk ^ for all <p* £ X, i.e., <pj & X. Therefore, we 
can put Y = X U {</?,}, which provides x £ f|Vi€y £ fl^ey □ 
Lemma 16.58 Wql(«) = • 
Proof Take any x £ WglC71)* K x £ then, by Lemma 16.56 (i), 
x £ U(pdew and we are done. So suppose that x (J<pdew Then by 
Lemma 16.57, x £ Let us consider [W] and suppose that for <pj 
associated with W condition (16.24) is satisfied. Then clearly x £ [W] and so 
x £ (pj1. Suppose now that (16.24) does not hold. As in the proof of Lemma 
16.57, we then have pk, for some k < m, such that -iOpk £ Pfc £ <Pj and, by 
(iii), -ipk £ <Pi for all <pi £ W, which is a contradiction. □ 
According to Lemma 16.56 (ii) and (iii), the sets <p^ can be represented as 
®GL(n)(ai) f°r some formulas a* in n variables such that distinct a* and otj 
cannot be true at any point in SDTglM simultaneously. For i < m we put 
A = \/{aj ■ <Pj €W, pi e <pj}. 
Lemma 16.59 For every point x in p1?, x \= <Pj- 
Proof The routine induction on the minimal l such that x £ is left to the 
reader as an exercise. □ 
We are ready now to complete the proof of Theorem 16.55. It follows from 
Lemma 16.59 that, for every x in , x f= Vj Vj and so, by Lemma 16.58, 
^Gh(n) |= VjV’j* ie-> £ GL. And by (i), there is <pj £ W such that 
-ipo £ <pj. Therefore, x |= -ipo f°r x € ^ and so pj & GL, which means that 
the rule \j ■ Pj/po is not admissible in GL. □ 
A remarkable feature of the criterion we have just proved is that it can be 
effectively checked. Thus we have 
Theorem 16.60 There is an algorithm which, given an inference rule, can 
decide whether it is admissible in GL or not 
The effective admissibility criteria similar to Theorem 16.55 can be proved for 
many other logics. We confine ourselves here only to formulating such a criterion 
for Grz. 
Suppose a reduced rule r = Pj/po is given. First we delete from its 
antecedent all disjuncts containing -lOp* and Pk for some fc. The resulting rule r' 
will be admissible in Grz iff r is admissible in Grz because, for any p, x/j, %, 
p V (^ A -iOx A x) € K 0 Dp —► p. 

ADMISSIBLE AND DERIVABLE RULES 
525 
Now, if r' = _L/po then everything is clear. Otherwise we take a non-empty set W 
of disjuncts in r' and construct the frame # = (W, R) and the model VUl = (#,2J) 
in almost the same way as above: the only difference is that now we take 
<PiR<Pj iff (Vfc G {0,..., m}(-^Opk ~'Opk G Vj) A 
G {0,..., m}(^Opk G Vj A Opk G (pi)) V 
Vi = Vj- 
Theorem 16.61 A reduced rule r = V. Vj/Po> which is different from _L/po and 
has no disjuncts containing both -iOpk and pk for some k, is not admissible in 
Grz iff there is a model 9Jt = (#, $J) defined as above on a set W of disjuncts in 
r and such that 
(i) -’Po G (p^ for some <pi G W; 
(ii) (pi \= (pi, for every & G W; 
(iii) for every antichain din? there is <pj G W such that, for each variable 
pk in r, (pj 1= Opk iff Vi 1= 0+Pfc for some (pi G a. 
Proof The proof is conducted by the same scheme as the proof of 
Theorem 16.55. □ 
As a consequence we obtain 
Theorem 16.62 The admissibility problem in Grz is decidable. 
We show now that the admissibility problem in Int can be reduced to the 
same problem in Grz and so is also decidable. To this end we require the following 
generalization of Theorem 3.83 in which we assume for simplicity that the Godel 
translation T prefixes □ to every subformula of a given intuitionistic formula (see 
Exercise 3.25). 
Theorem 16.63 A rule (p/'ijj is admissible in Int iff the rule T((p)/T(ijj) is 
admissible in Grz. 
Proof (<=) Let pi,... ,pn be all variables in (p and Suppose that the rule 
T(<p)/T(^) is admissible in Grz and v(Xu • • •»Xn) G Int. Then by Theorem 
3.83, T(<p(xi,.. •, Xn)) G Grz. Since DDp Dp G Grz, we have 
T(<p(xi,---,Xn)) ^T(<p){T(xi)/pi,...,T(xn)/Pn} G Grz. 
It follows that T(^(xi,. •., Xn)) G Grz and so, again by Theorem 3.83, we obtain 
^(Xi,.--,Xn) G Int. 
(=>) This part of the proof requires two auxiliary lemmas. 
Lemma 16.64 For every modal formula v(Pu • • • ,Pn) there is an intuitionistic 
formula ^(pi,... ,pn) such that 
□^(□pi,..., Upn) T(^) G Grz. 

526 
THE DECIDABILITY OF LOGICS 
Proof The proof proceeds by induction on the construction of <p. The basis 
of induction is clear because DDp Dp g Grz. The same concerns the step 
of induction for tp = □</?'. So suppose <p = </?'(□</?!,..., D<pm,pi,... ,pn) and 
<p' contains no occurrence of □. Then putting = Pi and using the fact 
that DDp <-* Dp g Grz, the equivalent replacement theorem and the induction 
hypothesis, we obtain that 
CV(Dpi,...,apn) <-> □v>/(T(V'i), • • • ,T(i/>m+n)) e Grz, 
for some intuitionistic formulas ^i,..., i)m+n in the variables pi,... ,pn. Now 
we transform <p' into its conjunctive normal form and get either T = ->JL or 
Ai(Vj “lPj v VfcPfc)- the former case we have 
□</?(Dpi,...,Dpn) ^T(-nl) G Grz 
and in the latter 
□v>( Dpi. •••.□?«) AD(AT(^) VT^fe)) € Grz 
i 3 fc 
and so □¥>(□?!,..., Op„) <-> T(Ai(Aj V'j V* V'fc)) e Grz. □ 
Lemma 16.65 Suppose that <p(pi, •. • ,pn) ^ Grz. T/ien exist formulas 
such that <p(xi,---,Xn) £ Grz, where Xi = 
Xi(^9l> • • • > ^9m)* 
Proof Follows from the fact that Grz is finitely approximable and that every 
set of points in a finite partially ordered frame can be represented as a Boolean 
combination of upward closed sets. □ 
We are in a position now to complete the proof of Theorem 16.63. Suppose 
a rule <p/ty is admissible in Int, pi,... ,pn are all the variables in it and assume 
also that, for some xi»• ■ ■»Xn, 
T(^)(xi(«i. • • •. 9m), ■ • •, Xn{qii • • ■, 9m)) £ Grz. 
By Lemma 16.65, there are substitution instances x'i °f Xi such that 
T(VO(xi(ari,...,Dr*0,...,xUDn,---,°rfe)) g Grz. 
In accordance with Lemma 16.64, for each x[ we choose an intuitionistic formula 
Xi such that 
nXi(Dn,---,Drfe) <-»T(x"(r-i,...,rfe)) € Grz. 
Since every variable in T(^) is “boxed” and DDp Dp £ Grz, we then have 
TW{T(x'i')/Pi. • • •, T(x")/Pn} * Grz 

ADMISSIBLE AND DERIVABLE RULES 
527 
and so T(V>(Xi, • • •, Xn)) & Grz, from which V>(Xi»• • •» Xn) & ^nt and hence 
<p(Xu • • • » Xn) ^ Int. Now we apply the same chain of arguments but in the 
reverse order to <p(xu • • • > Xn) and hnahy get 
T(^)(xi (91, • • • ,9m), • • • , Xnfal, • • • , Qm)) £ Grz, 
which establishes the admissibility of T(<p)/T(^) in Grz. □ 
As a consequence of Theorems 16.62 and 16.63 we obtain 
Theorem 16.66 The admissibility problem for inference rules in Int is 
decidable. 
For the logics considered above and many others as well the derivability 
problem for inference rules is solved trivially using the deduction theorem. We remind 
the reader that according to Theorem 3.51 and Exercise 3.5, if necessitation RN 
is not a postulated inference rule in a logic L then 
T,<p \~L ip iff r \~L <p -* *i> 
and if L £ NExtK4 and RN is a postulated rule in L then 
r,<^h^iffrhL 
Thus, in these cases the derivability problem for inference rules reduces to the 
decidability problem, i.e., we have 
Theorem 16.67 (i) If the rule RN is not postulated in a logic L then the 
derivability problem for inference rules in L is decidable iff L is decidable. 
(ii) The derivability problem for inference rules in a logic L € NExtK4 is 
decidable iff L is decidable. 
The same result holds of course for modal logics containing tran, for some 
n < uj. In general, in view of the existential quantifier in the deduction theorem 
for logics in NExtK, the situation is more complicated. However, for some 
systems the deduction theorem can be “effectivized”, as was done in Theorem 3.57. 
Another method of establishing the decidability of the derivability problem in a 
logic L is to show that L is globally finitely approximable. Using one of these 
ways one can prove the following: 
Theorem 16.68 The derivability problem for inference rules is decidable in the 
logics K, D, T, T 0p —► DOp. 
Proof Exercise. □ 
Algorithms recognizing admissible or derivable inference rules in a logic L can 
be used as decision algorithms for L as well: (p e L iff the rule T/<p is admissible 
in L iff T/ip is derivable in L. However, the converse does not hold. The aim of 
the rest of this section is to present corresponding examples 

528 
THE DECIDABILITY OF LOGICS 
C 
a 
tm ►« • • • • 
. . . «. 
bn ^n—1 ^1 
bo d b 
Fig. 16.7. 
Let X be a recursive set of pairs of natural numbers such that the projection 
X' = {n : 3m(m,n) £ X} is not recursive. Denote by ^{m^n) the transitive 
frame shown in Fig. 16.7 and consider the normal modal logic 
Theorem 16.69 (i) The derivability problem for inference rules in L\ is 
decidable. 
(ii) The admissibility problem for inference rules in L\ is undecidable. 
Proof (i) Since L\ D K4, it suffices, by Theorem 16.67, to show that L\ is 
decidable. And this is a consequence of the following: 
Lemma 16.70 For every formula p, <p £ L\ iff$(rn,n) ^ p for some m and n 
such that max{m,n} < l(p) + 1 and #(771,71) (= L\. 
Proof In Section 18.3 we will be proving similar results in full details. So we 
leave this one to the reader as an exercise. A little hint is that all frames of the 
form #(z,2n) and #(2m, z) validate L\. □ 
(ii) We require the following variable free formulas: 
7 = Oa A -i02o: A “■<>/?, 6 = Oa A 0(3 A ->02a 
which characterize, respectively, the points a, 6, c, d in #(ra,n). Now put 
pn(p) = ~l(0(—iO<$ A O7 Ap) A —iC>(—iO6 A 0(07 Ap)) A 
0(-i<>7 A O2n+16) A -iO(-i<>7 A <02n+2<$)), 
= —1(—iO6 A O7 A p). 
Since the rule rn is defined effectively by n, (ii) will follow from the fact that X' 
is not recursive and 
a = Dl, (3 = OT A DOT 
rn = <Pn{p)/i>{p) 
where 

ADMISSIBLE AND DERIVABLE RULES 
529 
Fig. 16.8. 
Lemma 16.71 The rule rn is admissible in L\ iffng Xf. 
Proof Suppose n £ X'. This means that there is m such that (m, n) £ X and 
so #(ra, n) is not a frame for L\. It is not hard to see then that <pn(02m+1~f) £ L\. 
However, ^(02m+17) ^ L\ because this formula is refuted in all frames #(2fc,z) 
for sufficiently big k (e.g. k = 2m + 4). Thus rn is not admissible in L\. 
Now let n $ X' and show that rn is admissible in L\. Suppose -0(x) ^ £i for 
some formula %. Then for some m and k such that (22^, ^ X and some 
valuation, -»0(5 A O7 A % is true at a point x in ^(m, fc). It follows that x = a* 
for some z. Let z be the minimal number for which a* |= -tO<5 A O7 A x- 
Since n ^ X', ^(z, 2n -f 1) is a frame for L\. Define a valuation in this frame 
so that the same variables be true at the points of the set a^t in ^(z, 2n 4-1) and 
^(m, fc). Then we shall have #(z, 2n + 1) ^ <pn(x) and so <Pn{x) L\. □ 
This completes the proof of Theorem 16.69. □ 
Let us consider now the frame 0 = (V, S) depicted in Fig. 16.8. 0 is not 
transitive; the arrows show all the accessibilities in it. Chains of points a*, &*, c* 
and di satisfy the following conditions. If (m, n) £ X then 0 contains a chain of 
the form 
bm+lSbmS • • • Sb— 1 So>2n-\-1 $ • • • ScL\ScLq 
and besides, for every pair (fc, i), 0 contains a chain of the form 
di+iSdiS... Sd-\Sc2h+2S... SciScq. 
Put L2 = Log0. 
Theorem 16.72 (i) L2 is decidable. 
(ii) The derivability problem for inference rules in L2 is undecidable. 
Proof (i) (Sketch) It is not hard to observe that although 0 is infinite (and L2 
is not finitely approximable), in order to refute a formula # L2 it is sufficient to 
consider only the part of 0 with the chains of a*, 6*, Ci and di of length <l(<p) + l 

530 
THE DECIDABILITY OF LOGICS 
and, since X is recursive, we can effectively check whether 0 contains chains of 
that sort. 
(ii) We introduce formulas characterizing points in 0 (follow the diagram of 
0): 
a= p = OT AD21, 
7 = Oa A 02a A -><>/?, <5 = Oa A Op A O7, e = 06, 
Aq = Op A “i(5, Ai+i = OA^ A “iOa, A^_j_i = OA^ A Oct (i > 0). 
Now put 
rn = □-.A/2n+2/D-.<5 
and show that the rule rn is derivable in L2 iff n £ X'. 
Suppose rn is derivable in Z^- By the deduction theorem, we then have some 
m < u) such that 
m 
A °^A2n+2 -► € L2 
i= 1 
or, which is equivalent, 
m 
0 N 06^ \/ OiA2n+2- 
i=l 
Since e is the only point in 0 at which 06 is true, e |= VS=i ^*^2n+2 and so 
we have a chain eSfy+iSfr/S... Sb-iSd2n+iS ■ • • Sa\Sao for some l < m. By the 
construction of 0, this means that (Z,n) £ X, from which n £ X'. 
It is easy to see that all the steps in this argument are reversible. 
Consequently, rn is admissible in L2 whenever n £ X'. □ 
16.8 	Exercises and open problems 
Exercise 16.1 Show that all logics in NExtK4.3 containing denn for some 
n < u) are finitely approximable. 
Exercise 16.2 Show that there are undecidable recursively axiomatizable logics 
in NExtK4.3. 
Exercise 16.3 For k < u, say that a type t = (£1,...,£n) for a(#,33,J_) is 
a k-type if, for every £* such that £* = m < uj or £* = ra+, we have m < 
k. Suppose L is a finitely axiomatizable normal extension of K4.3 and k the 
maximal number of irreflexive points in the frames underlying the formulas in 
some finite canonical axiomatization of L. Prove that, for any canonical formula 
a(#, 33, J_), a(#, 33, J_) £ L iff for every fc-f 1-type t for a (#,33, J_), the ^-extension 
of # is not a frame for L. 
Exercise 16.4 Let ip =f%n 0 mean that p and 0 are valid in the same finite 
frames. Prove the analogues of Theorem 16.49 and Corollary 16.50 for the relation 
—fin• 

NOTES 
531 
Exercise 16.5 Show that there is a purely implicative undecidable formula in 
Extint. 
Exercise 16.6 Prove an analog of Theorem 16.14 for si-logics. 
Exercise 16.7 Prove that (p —j► q) V (q —> p) and all formulas in one variable 
are decidable in Extint, and all variable free formulas are decidable in NExtGL 
and ExtGL. 
Exercise 16.8 Prove that the normal modal logic of the two point irreflexive 
chain is not structurally complete. 
Exercise 16.9 Prove that every structurally complete normal modal logic either 
contains D = K 0 OT or coincides with K 0 □ _L. 
Exercise 16.10 Give an example of a structurally incomplete tabular si-logic. 
Exercise 16.11 Show that the rule Dp/p is admissible but not derivable in GL. 
Exercise 16.12 Prove the decidability of the derivability problem for inference 
rules in every tabular logic. 
Problem 16.1 Are finitely axiomatizable modal and si-logics of finite width 
decidable? 
Problem 16.2 Can Theorem 16.16 be extended to logics in NExtK? 
Problem 16.3 Are the realizability logic and ML decidable? 
Problem 16.4 Is the admissibility problem in K decidable? 
16.9 	Notes 
The material of Section 16.2 is rather standard and mostly well known (not only 
to modal logicians). Say, Craig’s (1953) theorem holds in a very wide class of 
formal systems; counterexamples for it have been found only among equational 
logics having no relation to “real” logics. 
Till the end of the 1960s the decidability of various non-tabular logics was 
established mainly with the help of Theorem 16.11, i.e., by proving the finite ap- 
proximability with an effective upper bound for the size of the minimal refutation 
frames (algebras, matrices). Harrop’s theorem is more general. However, its 
deficiency is that now we cannot a priory estimate the effectiveness of the algorithm 
it provides. The examples of finitely approximable recursively axiomatizable 
logics that are not decidable, presented earlier in the book, and Theorem 16.14, 
proved in Chagrov (1994a), answer the natural questions concerning possible 
generalizations. The last theorem of Section 16.2 is the strongest (and so 
practically useless) generalization of Harrop’s theorem. Some results on the connection 
between the decidability of finitely approximable logics and recursive bounds of 
the size of refutation models can be found in Ulrich (1982, 1983, 1984). 
At the end of the 1960s a method of embeddings into various rich and yet 
decidable theories was developed to prove the decidability of modal and si-logics 

532 
THE DECIDABILITY OF LOGICS 
that are not finitely approximable; consult Gabbay (1971a, 1975, 1976). The 
most popular tools were Rabin’s (1969) and Buchi’s (1962) theorems. Gabbay 
(1975) used Rabin’s theorem to establish the decidability of K 0 OnDp —» Dp, 
K 0 Up —► Dnp, K 0 DnOp —> Op and some other logics. One of the strongest 
results obtained by this method is Sobolev’s (1977a) theorem, according to which 
all si-calculi of width 2 and all si-calculi of finite width containing the formula 
(((p -*• q) -> p) -*• p) v (((q ->p)-*q)^<i) 
are decidable. Note, however, that such decidability results can be proved also 
without using rich theories. The proof that all calculi in NExtK4.3 are decidable, 
taken from Zakharyaschev and Alekseev (1995), shows an alternative way to 
establish decidability by proving first a good completeness result. Wolter (1996c) 
extended Theorem 16.25 to tense linear calculi (which in general are not even 
Kripke complete). 
The question on the approximability of logics by recursive algebras was raised 
by Kuznetsov in the 1960s. The fact that recursive pseudo-Boolean algebras are 
not enough to characterize all si-logics was discovered by Chagrov and Tsytkin 
(1987), and Chagrov (1994a) strengthened this result to si-logics of widths 3 and 
to other types of recursive semantics; for example, he showed that there is a si- 
logic of width 3 (by Fine’s theorem, it is Kripke complete) which is characterized 
neither by recursive algebras, nor by recursive Kripke frames. These results were 
obtained by using the cardinality argument (see Notes to Chapter 4). They give 
no solution to the analogous problems concerning calculi. The following problems 
raised by Kuznetsov are still open: 
• Is it true that every (si-) calculus is characterized by recursive algebras? 
• Is it true that every (si-) calculus characterized by recursive algebras is 
decidable? 
It would be of interest also to clarify the relation between recursive algebras and 
frames. In general, however, this field of studies remains still terra incognita. 
The first undecidable modal and si-calculi were constructed by Thomason 
(1975c), Isard (1977) and Shehtman (1978b). Shehtman (1982) gave examples of 
undecidable bimodal and tense calculi whose axioms are reductions of modalities. 
He notes also that the decidability problem for normal modal calculi axiomatiz- 
able by modal reduction principles is open. 
Since undecidable calculi can be used as a base for obtaining “negative” 
solutions to various algorithmic problems, it is of interest to find the simplest 
possible calculi of that sort. For example, Chagrov (1994c) constructed 
undecidable calculi in Extint, NExtS4 and NExtGL with axioms in four, three and 
one variable, respectively. For comparison we remind the reader that all calculi 
in NExtS4 with one-variable axioms are finitely approximable and so decidable 
(see Section 11.6). On the other hand, Sobolev (1977b) constructed a si-calculus 
with two-variable axioms that is not finitely approximable, and Shehtman (1977) 
even an incomplete one. It is unknown whether there exist undecidable si-calculi 

NOTES 
533 
with axioms in two or three variables; the same concerns calculi in NExtS4 with 
two-variable axioms. 
Having used Minsky machines to construct undecidable calculi, we followed 
the idea of Isard (1977), developed further by Chagrova (1989a, 1989b) who gave 
an example of an undecidable elementary si-calculus. 
The notion of undecidable formula was introduced in Chagrov (1994c), where 
numerous examples of such formulas in various classes of logics were given. Here 
is the simplest known undecidable formula in Extint: 
-i(p A q) V -»(-»p A q) V ->(p A —>q) V -»(-»p A -»#). 
The algorithmic problem of semantical consequence on finite frames was 
solved negatively by Chagrov (1990a) practically for all natural classes of frames, 
including intuitionistic ones. The presentation of Section 16.6 follows Chagrov 
and Chagrova (1995). 
Note by the way that the decidability problem for such interesting logics as 
the realizability logic and ML is still open in spite of numerous attempts to solve 
it. 
Thomason (1975a) showed that there is a modal formula <p such that the set 
of formulas which are valid in all frames for <p is nj-complete. Note, however, 
that this result as well as similar results of Thomason (1975b) essentially use 
nontransitive frames. It would be of interest to transfer them to the transitive 
and intuitionistic cases. 
One of the reasons to study admissible and derivable in a given logic 
inference rules are various applications. We have already mentioned the possibility of 
using such rules to shorten derivations. Another application is connected with 
the problem of finite axiomatizability, because it essentially depends on the set 
of postulated inference rules. Without going into details, note, for instance, that 
although Medvedev’s logic is not finitely axiomatizable, as was shown by 
Maksimova et al. (1979), there is still a hope to find a finite axiomatization for it 
by adding some sort of (non-structural) rules; see (Medvedev, 1979). An active 
study of non-structural rules was initiated by Gabbay (1981b); see (Venema, 
1993). 
The decidability of the admissibility problem for inference rules in GL, Grz 
and Int was proved by Rybakov (1984b, 1985a, 1985b, 1986a, 1986b, 1987a, 
1987b, 1989, 1990a, 1990b, 1990c, 1993). For other logics similar results were 
obtained in Rybakov (1981, 1984c, 1984a). In particular in the latter paper it 
was shown that the admissibility problem is decidable in all extensions of S4.3, 
which is a generalization of Fine’s (1971) result according to which all these 
logics are decidable. The same ideas have been recently extended by Rybakov 
(1994) to K4 and some of its extensions. 
The key role in all these papers is played by the universal models, which, as 
we saw in Chapter 8, have a clear structure in the case of finitely approximable 
logics in NExtK4 and Extint. We know no other logic for which the admissibility 
problem has been solved positively. Even for K, whose universal models can be 

534 
THE DECIDABILITY OF LOGICS 
described in some way, this problem has not been solved yet. Another open 
problem here is to construct a decidable calculus the admissibility problem for 
which is undecidable. 
A decidable logic whose admissibility problem is undecidable was constructed 
by Chagrov (1992b). We know nothing about examples of that sort in Extint. 
Spaan (1993) proved that the logic 
Alt2 0 /\ OOpi -+ \J OO(pi A pj) 
l<i<4 l<i<j<4 
is decidable (actually, it is a subframe logic; see Exercise 11.21) but the deriv- 
ability problem for inference rules in it is undecidable. Kracht and Wolter (1997) 
showed that the derivability problem for inference rules is undecidable in the 
class of decidable logics. 

17 
THE DECIDABILITY OF LOGICS’ PROPERTIES 
In this chapter we return to the main question of Part IV—how to determine 
whether a given logic satisfies a given property—and consider it from the 
algorithmic point of view. 
17.1 	A trivial solution 
The ideal solution to the algorithmic problem of recognizing a property V of 
logics in a given family should present an algorithm which, given an effective 
definition of a logic L in the family, could determine whether L satisfies V or 
not. In this case it is appropriate to call the property V decidable in that family. 
As we saw in Section 16.2, there are distinct (though equivalent and effectively 
related with each other) algorithmic ways of defining logics: an algorithm 
enumerating a logic’s formulas, an algorithm enumerating its axioms, an algorithm 
recognizing them. So without loss of generality we can speak only about 
recursively axiomatizable logics, but freely use any of these ways. 
Unfortunately, this “ideal solution” is inaccessible, as is shown by the 
following: 
Theorem 17.1. (Kuznetsov’s theorem) No non-trivial property of 
recursively axiomatizable logics is decidable in any lattice of logics considered above. 
Proof We will use the undecidability of the halting problem for Minsky 
machines. Also we need an effective procedure enumerating pairs of natural 
numbers. Recall that l(n) and r(n) denote the left and the right components of the 
pair with number n, respectively (i.e., n is the number of the pair (Z(n), r(n))). 
Let V be a non-trivial property of logics in some lattice. Since V is not 
trivial, the lattice contains a logic different from the inconsistent one. Suppose for 
definiteness that the inconsistent logic satisfies V and a logic L with a recursive 
enumeration <£o> <£i» ■ • ■ of its formulas does not have V. 
Now, given an arbitrary program P, we define an effective procedure for 
enumerating axioms t/>o> Vh, • • • of some logic L'\ 
<pn if P does not halt after 
l(n) steps on the input r(n) 
_L otherwise. 
Then we have the following implications: 

536 
THE DECIDABILITY OF LOGICS’ PROPERTIES 
P does not halt on any input 
'ipn = </>n for every n 
$ 
L! — L 
U 
L' does not have V 
and 
P halts on some input 
4 
_L is an axiom of V 
V is inconsistent 
4 
V satisfies V. 
Thus, if we could effectively recognize V then we would also be able to decide 
the undecidable halting problem. □ 
Theorem 17.1 prompts us to change the definition of decidable property. We 
call a property V decidable in the lattice of logics (N)ExtL if there exists an 
algorithm which, given a finite set T of axioms, can determine whether L + T 
(respectively, L 0 T) satisfies V or not. 
In the next section we shall see that the decidability problem for properties 
in this sense, i.e., for properties of calculi, is not so trivial and frustrating. 
17.2 	Decidable properties of calculi 
In this section we have collected those properties the decidability of which follows 
easily from the results obtained in Part IV. 
We begin with the consistency problem in NExtK. According to Makinson’s 
theorem, the logic K01 has exactly two immediate predecessors in NExtK, 
viz., Logo and Log». Hence, K0(/?/K0liff(^G Logo or <p € Log». So to 
decide whether a logic K 0 </> is consistent it suffices just to check the conditions 
o |= (p and • |= </>, which can be done in finitely many steps. If at least one of 
them is satisfied then K 0 <p is consistent, otherwise it is inconsistent. Thus we 
obtain 
Theorem 17.2 The property of consistency is decidable in NExtK. 
Let us generalize this observation. In fact, the algorithm described above 
decides the problem of coincidence with a fixed logic, namely, the inconsistent 
one. And almost the same scheme works for recognizing the coincidence with 
any decidable logic L having in the lattice under consideration finitely many 
decidable immediate predecessors, say, Li,...Ln. Indeed, a logic V coincides 
with L iff V C L, V % Li,..., V $7 Ln, which can be effectively checked if Lf is 
finitely axiomatizable. Using this scheme together with Theorems 12.7, 12.9 we 
obtain 

DECIDABLE PROPERTIES OF CALCULI 
537 
Theorem 17.3 The property of coincidence with a fixed tabular logic in NExtK4 
(Extint, ExtS4j is decidable. 
This scheme is not applicable immediately to tabular logics in ExtGL. Yet, 
it can be “pressed out” to produce 
Theorem 17.4 The property of coincidence with a fixed tabular logic in ExtGL 
is decidable. 
Proof Exercise (see the proof of Theorem 17.6). □ 
Sometimes a similar argument can be used for proving the decidability of 
tabularity. Let us consider this property in Extint. As we saw in Section 12.3, 
every non-tabular si-logic is contained in one of the three pretabular logics in 
Extint, call them Li, L<i and L3. So a calculus Int + p is tabular iff p Li, 
ip Z/2 and p £ L3, which can be checked effectively, because Li, L2 and L3 are 
decidable. Analogous tabularity criteria hold for NExtS4 and ExtS4. Thus we 
have 
Theorem 17.5 The property of tabularity is decidable in NExtS4, ExtS4 and 
Extint. 
To extend this result to NExtGL and ExtGL a more sophisticated argument 
is required. 
Theorem 17.6 Tabularity is decidable in NExtGL and ExtGL. 
Proof We consider only ExtGL and leave the easier case of NExtGL to the 
reader. 
Observe first that if Dn_L G GL + p for no n < uj then L — GL + p is not 
tabular. Indeed, otherwise, by Corollary 12.3, the logic L + {OnT : n < u} 
would be tabular, which is a contradiction, because it is consistent and does not 
have finite frames at all. 
Suppose now that we have succeeded in establishing that Dn_L G L for some 
n < a;, i.e., L G Ext(GL + Dn±). According to Exercises 12.6-12.8, there are 
finitely many pretabular logics in Ext(GL + CPI.) and all of them are decidable. 
So we may use the scheme above to check whether L is tabular. Thus, our problem 
reduces to the problem of verifying in an effective way whether Dn_L G L for some 
n <uj. 
In Exercise 13.13 we described the Post complete extensions of GL. Let us 
denote them here by Lp. for i < u>, Li is the logic of z-point irreflexive chain with 
the distinguished root and Lu = GL.3 + re is the logic of the matrix of finite 
and cofinite sets in the frame (a;, >) whose ultrafilter of distinguished elements 
consists of cofinite sets. It is not hard to see that nn_L G GL + p for some n 
iff p Lu- Indeed, if p G Lu then Lw G ExtL, and so Dn_L L for any n, 
because otherwise Dn_L G Lw, which is impossible. And if p Lu then either 
L is inconsistent or it is consistent and its Post complete extensions are of the 
form Li for i < u>. Now observe that if L had infinitely many Post complete 
extensions then, by Theorem 13.22, Lu would also be an extension of L. So L 

538 
THE DECIDABILITY OF LOGICS’ PROPERTIES 
has only finitely many extensions of the form L*, say, L^,... , L*m. But then 
□n_L G L, where n > max{zi,..., zm}, for otherwise L + OnT is consistent, 
contrary to OnT ^ L^,..., OnT ^ Lim. To complete the proof, it remains to 
recall that, by Theorem 11.38, Lw is decidable. □ 
The part of the proof above concerning the problem whether Dn_L G GL + 
for some n < u may be treated as determining whether GL + <p is locally tabular. 
The local tabularity of GL + ip is also equivalent to the existence of n < u such 
that □n_L G GL0<p, which in turn is equivalent to <p GL.3 (see Section 12.4). 
And the letter can be checked effectively because GL.3 is decidable. In the same 
way one can recognize the local tabularity of calculi in NExtS4 and ExtS4. Thus 
we obtain 
Theorem 17.7 Local tabularity is decidable in the classes NExtGL, ExtGL, 
NExtS4, ExtS4. 
The final decidability result in this section is left to the reader as an exercise: 
Theorem 17.8 The interpolation property is decidable in the classes Extint 
and NExtS4. 
Proof Use results of Section 14.4. □ 
17.3 	Undecidable properties of modal calculi 
In fact, in Section 16.4 we already met with undecidable properties. Such was the 
property of coincidence with the undecidable calculus or with the (finitely ap- 
proximable and so decidable) calculus axiomatizable by the undecidable formula 
p. And the most important undecidable property found there was the consistency 
in ExtK4. The latter result can be extended to 
Theorem 17.9 Let L be a tabular extension of K4. Then the problem of 
coincidence with L is undecidable in ExtK4. 
Proof Consider the logic 
L' = K4 + AxP + (-ii/ A Oe(s,a^,a£) -> Oe(t,al,a?)) -* v, 
where v axiomatizes L over K4 (by Theorem 12.4, L is finitely axiomatizable) 
and contains no occurrences of pi, p%, and the remaining formulas result from 
those in Section 16.4 by replacing every occurrence of p with 
Lemma 17.10 (i) P : (s,m,n) —> (£,fc,Z) implies V — L. 
(ii) If P : (s,m, n) (t,k,l) then V is not tabular and so V ^ L. 
Proof (i) In the same way as in the proof of Lemma 16.29 one can show that 
if P : (s, m, n) —> (t, fc, l) then 
ni/AOefs.aJ,,^) -* Oe(t,a\,a?) € L'. 
It follows by MP that K4 + v C I/. The converse inclusion is clear because all 
additional axioms of V are either of the form ~^v A ^ or of the form (p —> v. 

UNDECIDABLE PROPERTIES OF MODAL CALCULI 
539 
(ii) It suffices to observe that if P : (s,m,n) {t,k,l) then all Z/’s axioms 
are valid at the point r in the frame shown in Fig. 16.3, where all the formulas 
/?n, defined in Section 12.1, are refutable, and so, by Theorem 12.1, V is not 
tabular. □ 
Theorem 17.9 follows immediately. □ 
Another consequence of Lemma 17.10 is 
Theorem 17.11 The property of tabularity is undecidable in ExtK4. 
Now we consider the tabularity problem in NExtK. Let # be the nontransitive 
frame which is obtained from the (transitive) frame in Fig. 16.3 by making r 
reflexive and putting b\Rr. 
Theorem 17.12 For every formula v refutable at any point in # save 60 and 
such that OT ^ K 0 i/, the problem of coincidence with K is undecidable in 
NExtK. 
Proof Without loss of generality we may assume that pi and P2 do not occur 
in v. In all formulas from Section 16.4 we replace every occurrence of /?o with 
/?0AO2DJ_, p with -i v and every formula of the form O e(t, 7r, r) with O 3e(£, 7r, r). 
For instance, the axiom Ax(t —► (£', 1,0)) will look now like 
-.1/ A 03e(t, 7Ti, n) -> 03e(t/, 7r2, ti). 
Using the former notations for the new formulas, we put 
L = K0 AxP®(~iv AO3^,^,^) —► O3e(t,a\,af)) —► v. 
Lemma 17.13 (i) P : (s,m,n) —► (t,k,l) implies L = K0i/. 
(ii) // P : (s,m,n) (t,k,l) then $ \= L. In particular, v £ L and so 
L^K0za 
Proof (i) is proved analogously to (i) in Lemma 17.10. To prove (ii) one can 
observe that after all the changes Lemma 16.30 still holds (here we use the fact 
that the set of points in S', where v is refutable, coincides with the set of those 
points that see “in three steps” (via r) every point of the form e(tf, kl,V)). Details 
are left to the reader as an exercise. □ 
Theorem 17.12 is a direct consequence of Lemma 17.13. □ 
This rather general theorem has a number of interesting consequences. 
Corollary 17.14 Let V be a tabular normal modal logic such that OT ^ L'. 
Then the problem of coincidence with L' is undecidable in NExtK. 
Proof Observe that from every point in S save 60 arbitrary long chains are 
accessible. Therefore, by Theorem 12.1, the axiom of I/, call it u, satisfies the 
condition of Theorem 17.12. □ 

540 
THE DECIDABILITY OF LOGICS’ PROPERTIES 
Corollary 17.15 The tabularity problem is undecidable in NExtK. 
Proof It suffices to take v as in the previous proof, L as in the proof of 
Theorem 17.12 and use Lemma 17.13. □ 
Corollary 17.16 Let L be a finitely axiomatizable consistent normal extension 
of GL (e.g., GL itself GL.3, Log^. Then the problem of coincidence with L is 
undecidable in NExtK. 
Proof Exercise. □ 
Let us consider now other standard properties of modal logics. In the rest of 
this section we will be dealing only with the lattice NExtGL. From now on the 
notations will have a different meaning; a resemblance with the previous ones 
merely emphasizes an analogy. 
To understand the axioms of the logic to be introduced below it is useful 
to bear in mind the (transitive) frame $ = (W, R, P) whose underlying Kripke 
frame is shown in Fig. 17.1 and P is the family of finite and cofinite subsets of W. 
As before, $ contains only those points e(t, k, l) for which P : (s, m, n) —► (t, k, l). 
P and (s,m,n) are chosen in accordance with Theorem 16.3, so that the second 
configuration problem is undecidable for them. 
It is easily checked that # |= GL. Notice also that r is the only point in # 
where the formula 
u = -> Dp V Dip) 
is refuted: this happens iff bo \= p, b\Y^p or bo ^ p, 61 (= p. 

UNDECIDABLE PROPERTIES OF MODAL CALCULI 
541 
Suppose now that v is really refuted in $ under some valuation. Since 60 
and b\ are symmetrical in #, without loss of generality we may assume that the 
valuation satisfies the former of the alternatives above. It is easy to see then that 
the points aj in # are characterized by the formulas: 
(*0 = 0(Oi+2(Dl Ap) A-.Oi+3(D± Ap) AiO(Oi A-ip)) A 
0(0<+2(Dl A -.p) A iOi+3(D± Ap) A -.0(D± A p)) A 
-.02(0i+2(Dl A p) A -.Oi+3(D± A p) A iO(a± A -.p)) A 
-i02(0i+2(D± A ip) A iO<+3(D± a ->p) a iO(a_L Ap)), 
a* = O’a* A nOi+'aj A f\a* (i e {0,1,2}, j > 1). 
i^k 
Using them, in exactly the same way as in Section 16.4 we define e(t, a*.,a2), 7Ti, 
7T2j ri, T2, e(f, 7Ti, Tj), e(£, 7Ti , aj)), e(t,ao,ri) and then ArP with ~^v instead of p 
and prove the literal analogues of Lemmas 16.26-16.31. 
We require also the formulas 
z/ = □(□3± -> □(□21 A OT —► q) V □(□21 AOT-4 -.g)), 
Ai = gi A D-igi A 05(D _L Ap) A iO(Dl A -ip), 
Mi = <72 A D-ig2 A 05(D1 A ip) A iO(D_L Ap), 
A2 = Ai{Ogi/gi}, p2 = Mi{^2/42}, 
«i = OAi A O/ii A i02A* A iO2pi (i e {1,2}). 
Now, given a configuration (t, fc, /), we define a logic L by taking 
L = GL 0 ArP 0 (11/ A Oe(s, a2) —► Oe(£, a*., a2)) —► v 0 
v V z/ 0 z/ V (0«! —> 0(0«2 A iO+«i)). 
Lemma 17.17 Suppose P : (s,ra,n) (t,k,l). Then: 
(i) L = GL 0 v; 
(ii) L is axiomatizable in NExtGL by a GL-conservative formula; 
(iii) L is finitely approximate; 
(iv) L is decidable; 
(v) L is Kripke complete; 
(vi) L has the interpolation property; 
(vii) L has the disjunction property. 
Proof (i) proved in the same way as (i) in Lemma 17.10, (ii) follows from (i) by 
the argument in the proof of Lemma 14.28. By Exercise 11.4, (iii) is a consequence 
of (ii); (iv) and (v) follow from (iii) and (vi) from (ii) by Theorems 14.5 and 14.25. 
Finally, one can easily obtain (vii) by describing the class of finite frames for L 
and using (iii); we leave this to the reader as an exercise. □ 

542 
THE DECIDABILITY OF LOGICS’ PROPERTIES 
Lemma 17.18 Suppose P : (s,m,n) (t,k,l). Then: 
(i) L C GL 0 v; 
(ii) L is not axiomatizable in NExtGL by a GL-conservative formula; 
(iii) L is not finitely approximate; 
(iv) L is undecidable; 
(v) L is Kripke incomplete; 
(vi) L does not have the interpolation property; 
(vii) L does not have the disjunction property. 
Proof It is sufficient to establish only (iv), (v), (vi) and (vii). To prove (iv), 
observe that # |= L, which together with the analog of Lemma 16.29 yields the 
following analog of Lemma 16.31: for every configuration (tl, kl, /'), 
P : (s,m,n> -> {') iff -v A Oe(s, 0:^,0;^) -> Oe(t', a{,, a?,) £ L. 
It remains to recall that the second configuration problem is undecidable for P 
and (s,ra,n). 
To justify (v) we use the last axiom of L, i.e., v V (O/^i —► 0(0^2 A-iO+/si)). 
If we try to refute the formula 1/ V O^i in a Kripke frame for L, then this axiom 
will require an infinite ascending chain of distinct points (as in Section 6.3), 
which will contradict la G L. On the other hand, with the help of # one can 
show that v V Ok\ L. 
(vi) 	is proved analogously to Theorem 14.27 by considering the axiom v V i/ 
(which is equivalent to —► ur). In the same manner one proves that v $ L 
(using #) and uf ^ L (using the frame in Fig. 14.9), which in view of v V v* G L 
gives (vii). □ 
As an immediate consequence of Lemmas 17.17 and 17.18 we obtain 
Theorem 17.19 The following properties are undecidable in NExtGL: 
decidability, finite approximability, Kripke completeness, the interpolation property, 
the disjunction property, the axiomatizability by GL-conservative formulas, the 
property of coincidence with GL 0 □(□2_L Dp V D-^p). 
Incidentally we have also got 
Theorem 17.20 The formula □(□2_L —► □pVCHp) is undecidable in NExtGL. 
17.4 	Undecidable properties of si-calculi 
Here we confine ourselves only to demonstrating that the same scheme of 
proving the undecidability of calculi’s properties is applicable to superintuitionistic 
logics as well. All the notations used below correspond to those introduced in 
Section 16.5. 
Theorem 17.21 The following properties are undecidable in Extint: 
decidability, finite approximability, axiomatizability by disjunction free formulas. 
Proof Consider the logic 

EXERCISES AND OPEN PROBLEMS 
543 
L = Int + AxP + (e(t, a\, a?) -> e(s, a^, a£) V p) -+ p 
introduced at the end of Section 16.5. If P : (5, m,n) —* (t,k,l) then, as in 
Lemma 17.10 (i), we have L = Int+p, where p contains only positive occurrences 
of V. Therefore, by Exercise 4.11, L is axiomatizable by a disjunction free formula 
and so, by McKay’s theorem, it is finitely approximable and decidable. And if 
P : (s,m,n) (t,kj) then using the frame in Fig. 16.4 one can show that L 
is undecidable (see the analogous proof of (iv) in Lemma 17.18) and so it is not 
finitely approximable and not axiomatizable by disjunction free formulas. □ 
Corollary 17.22 The properties of decidability and finite approximability are 
undecidable in NExtGrz. 
Proof Follows from Theorem 17.21 and the preservation theorem. □ 
17.5 	Exercises and open problems 
Exercise 17.1 Extend the proof of Theorem 17.1 to the following classes of 
logics: (a) consistent si-logics; (b) consistent (normal) extensions of S4; (c) 
consistent normal extensions of GL. 
Exercise 17.2 Show that, for every modal formula (p, 
A (Dip —► -0) —► <p G GL.3. 
□■0eSub v? 
Exercise 17.3 Prove that (a) every non-trivial property of recursively 
axiomatizable logics in the family {Logo, Log^} is decidable; (b) every non-trivial property 
of recursively axiomatizable logics in {Logo, Log», Log(o + •)} is undecidable. 
Exercise 17.4 Prove that the following properties are decidable: 
(i) Hallden completeness in NExtGL. 
(ii) The “weak disjunction property”, i.e., if <p V xj; G L then -r^p G L or 
-11-0 G L, in Extint. 
(iii) The property “to be a modal companion of Int” in the classes NExtS4 
and ExtS4. 
(iv) The axiomatizability by Int-conservative formulas in Extint and by 84- 
conservative formulas in NExtS4. (Hint: see Theorem 17.8.) 
(v) The pretabularity in Extint, NExtS4, NExtGL, ExtGL. 
(vi) The antitabularity in ExtGL. 
Exercise 17.5 Prove that Hallden completeness is undecidable in the classes 
Extint, NExtS4, ExtS4, ExtGL. 
Exercise 17.6 Prove that the property “to be a modal companion of Int” is 
undecidable in NExtK4. 
Exercise 17.7 Prove the decidability of coincidence with D in NExtK. 
Generalize this result to all finite union-splittings of NExtK. 

544 
THE DECIDABILITY OF LOGICS’ PROPERTIES 
Exercise 17,8 Prove the decidability of the following formulas: 
(i) the formulas in one variable in Extint; 
(ii) the variable free formulas in NExtGL. 
Exercise 17,9 Prove that the property “to be a modal companion of Int -f ip” 
is decidable in NExtS4 iff Int -f <p is decidable and p is decidable in Extint. 
Exercise 17,10 Prove that the property of axiomatizability by variable free 
formulas is undecidable in NExtK4. 
Exercise 17.11 Prove that in ExtS the interpolation property and Hallden 
completeness are undecidable. 
Exercise 17.12 Prove that the problem of first order definability of modal 
formulas is undecidable. (Hint: use for instance the formula 
AxP© ((pAOefs.aJ,,^) _> O-*• ->p) A 
(-.pV(D(Op->p) -+ Op)) 
where the formulas AxP, p and e are taken from Section 16.3; in the case when 
P : (s, m, n) —► (t, k, l) this formula is equivalent to the variable free “■/?, which is 
certainly first order definable; and if P : (s, ra, n) •/» (t,k,l) then this formula is 
valid in the frame shown in Fig. 16.2, from the root of an ultrapower of which an 
infinite ascending chain is accessible and so p V (IH(Op —► p) —> Up) is refutable 
in it.) 
Exercise 17.13 Prove that Kripke completeness and the axiomatizability by 
purely implicative formulas are undecidable in Extint. 
Exercise 17.14 (i) Prove that the set of inconsistent calculi in ExtK4 is not 
recursively enumerable. 
(ii) Prove that the set of non-tabular calculi in NExtK is not recursively 
enumerable. 
Problem 17.1 Does Theorem 17.1 hold for the classes of consistent logics in 
ExtK, ExtK4, ExtGL ? 
Problem 17.2 Is there an algorithm which, given an effective procedure 
enumerating the complement of a logic L in Extint (NExtK, ExtK, etc.), decides 
whether or not L satisfies a given non-trivial property? 
Problem 17.3 Is the property “to be a (un)decidable formula” decidable in 
Extint, NExtK, etc. ? 
Problem 17.4 Is local tabularity decidable in Extint? 
Problem 17.5 Is structural completeness decidable in Extint and NExtK4? 
Problem 17.6 Are the sets of modal (in various standard classes) and si-calculi 
with (or without) the properties like Kripke completeness, finite approximability, 
etc. recursively enumerable? 

NOTES 
545 
17.6 	Notes 
The jump from considering individual modal and si-logics to big classes of them 
gave rise to new settings of problems, in particular, algorithmic ones. When 
dealing with a separate logic, we are searching for answers to some standard list of 
questions: whether the logic is decidable, Kripke complete, finitely approximable, 
tabular, etc. For classes of logics these questions become mass algorithmic 
problems. 
The pioneer paper in which such kinds of algorithmic problems were brought 
in sight and solved “negatively” was Linial and Post (1949), where it was shown 
in essence that the property “to be an axiomatization of Cl” is undecidable. 
Kuznetsov (1963) significantly extended this result: for every si-calculus C, the 
problem of recognizing, given an arbitrary list of formulas, whether it axiomatizes 
C with the rules MP and Subst (and without axioms of Int) is algorithmically 
undecidable. By a proper choice of C we can get various undecidable properties of 
propositional calculi. In particular, undecidable are the properties of consistency, 
completeness with respect to the classical truth-table (i.e., the property “to be 
an axiomatization of Cl”) and some other properties which can be formulated 
in the form of the deductive equivalence to a certain fixed si-calculus. Note that 
Kuznetsov’s theorem of Section 17.1 was not published by the author. We are 
grateful to L. Maksimova for informing us about it. 
Until the late 1970s the efforts in the algorithmic direction of studies in modal 
logic were oriented mainly to obtaining positive results. To prove that a property 
is decidable one has, as a rule, to investigate deeply enough the property itself. 
One such property was tabularity. Kuznetsov’s idea to use pretabular logics (first 
they were called “quasi-tabular”) helped Maksimova (1972) to demonstrate that 
the property of tabularity is decidable in the class of si-logics, which became an 
impetus to consider the tabularity problem in other classes of logics. Another 
remarkable (with respect to its algorithmic behavior) property—the interpolation 
in Extint and NExtS4—was examined by Maksimova (1977, 1979, 1980). Note 
that for NExtS4 it was shown only that a decision algorithm exists; its concrete 
form depends on the set of logics with the interpolation property in NExtS4, 
which is not completely characterized yet. 
Only a few properties, besides those mentioned in Section 17.2 and exercises, 
are known to be decidable. One of them is “to have the same negation free 
fragment as Int” :* according to Jankov (1968a), it is equivalent to the property 
“to be included in KC”, which is decidable in view of the decidability of KC. 
We do not know, however, whether the property “to have the same implicative 
fragment as Int” is decidable. 
It is worth noting that there is an interesting correlation between the 
decidability of a formula </?, say in Extint, and the decidability of the calculus 
axiomatizable by </?: the property of coincidence with L = Int -f ip is decidable 
iff both L and </? are decidable. 
The first paper specially devoted to obtaining results on the undecidability of 
properties of calculi in NExtK was Thomason (1982), which, besides establishing 

546 
THE DECIDABILITY OF LOGICS’ PROPERTIES 
that Kripke completeness is undecidable, shows in fact that the finite approxima- 
bility in NExtK and the consistency of normal bimodal calculi are undecidable 
as well. The next step was made by Chagrova (1989d), who used the results 
of Chagrova (1989a, 1989c) to prove some theorems on the undecidability of 
properties of intuitionistic formulas related to their first order definability. She 
showed, for instance, the undecidability of the first order definability on 
countable frames and of the property “to be first order definable on countable frames 
but not on all frames”; see also Chagrov and Chagrova (1995). The main result 
asserting that the first order definability of intuitionistic formulas (or si-calculi) 
is undecidable was proved in a somewhat different way in Chagrova (1991). 
Further progress in this direction was connected with the discovery of a 
general scheme for proving undecidability results of that sort. First it was applied in 
Chagrov (1990b, 1990c) and explicitly formulated in Chagrov and Zakharyaschev 
(1993). We followed this scheme in Sections 17.3 and 17.4. The results 
concerning the undecidability of tabularity are taken from Chagrov (1996), where it is 
proved, in particular, that the problem of coincidence with a fixed consistent 
tabular logic in NExtK is undecidable. Moreover, by combining the technique 
of Chagrov (1996) and the proof of Blok’s theorem one can show that if L is 
a finitely axiomatizable consistent normal modal logic different from a 
unionsplitting then the problem “K ® </? = L?” is undecidable. For more applications 
of that scheme in various situations see Chagrov (1994c). 
Another approach was taken by Kracht and Wolter (1997). Here the 
undecidability of properties is first shown for bimodal logics using word problems. Then, 
drawing on the simulation technique developed by Thomason (1974b, 1975c), 
the results are transferred to logics in NExtK similar to Thomason (1982). 
Problem 17.4 was posed by Maksimova. As for Problem 17.5, Tsytkin (1987) 
and Rybakov (1995) proved that the property of hereditary structural 
completeness is decidable in Extint and NExtK4. Cresswell (1985) showed that no 
recursively enumerable family of algorithms consists only of decision algorithms 
for all decidable normal modal logics. 

18 
COMPLEXITY PROBLEMS 
Suppose we have managed to construct a decision algorithm for a given modal 
or si-logic. Then we are facing the following questions. What are the complexity 
parameters (say, the required time and memory) of this algorithm? Does there 
exist a simpler algorithm? Since it is a priori impossible to estimate the efficiency 
of the decision procedure provided by Harrop’s theorem, and the use of Biichi’s 
and Rabin’s theorems reduces the decision problem for a propositional logic to 
that for a second order theory (which is known to be very complicated), we 
consider here only those decision algorithms that are based on estimating the 
size of minimal frames separating formulas from logics. 
18.1 	Complexity function. Kuznetsov’s construction 
In Section 4.3 we introduced the notions of exponential, polynomial and linear 
approximability. More generally, for a finitely approximable logic L we consider 
the function 
fL(n) = max min |ff|, 
$|=L 
where l(ip) is the length of (p, i.e., the number of subformulas in <p. /^(n) is called 
the complexity function of L. The exponential, polynomial and linear 
approximability of L mean then that there are positive constants ci, c2, c3, respectively, 
such that the following conditions hold: 
h{n) < 2Cl'n, fL{n) < nC2, fL(n) <c3-n. 
A necessary condition for an algorithm to be regarded as “acceptable” or 
“sufficiently efficient” is, as is well known, its polynomial parameters. Without 
going into details (consult Garey and Johnson, 1979) we accept this claim as a 
working thesis. 
The simplest consistent modal and si-logics are the tabular ones, and among 
them Cl, Triv and Verum as the logics characterized by single-point frames. 
Although nobody knows if there exists a polynomial time decision algorithm for 
at least one of them, other tabular logics seem to be even more complex. To make 
our discussion more concrete, we introduce a notion of polynomial reducibility 
of one logic to another. 
Say that a logic Li is polynomially reducible to a logic L2 if there is a function 
g from the language of L\ into that of L2 which is computable by a polynomial 
time algorithm (of the length of the input formula) and such that 

548 
COMPLEXITY PROBLEMS 
(p € L\ iff <?(</?) € L2. 
Notice that Cl is polynomially reducible to any consistent modal or si-logic. In 
the former case one can use the identity function g(ip) = ip and in the latter, by 
Glivenko’s theorem, g(<p>) = -i-n/?. 
We say also that L\ and L<i are polynomially equivalent (with respect to 
their decision algorithms) if they are polynomially reducible to each other. It is 
easy to see that every two tabular logics are polynomially equivalent (consult 
Exercises 18.1 and 18.2). Polynomially equivalent logics may be regarded as 
similar as far as the complexity of their decision algorithms is concerned. 
Example 18,1 As we showed in Section 4.3, LC is linearly approximable. This 
provides us with a decision algorithm for LC that works exponential time of the 
length of the input formula. 
Thus, both Cl and LC are decidable by algorithms requiring exponential 
time. But are they polynomially equivalent? In Section 18.5 we shall show how 
questions of that sort can be answered in an easy, though indirect way. Here we 
give a direct construction for obtaining such results. 
Let us recall that Cl, in spite of all the criticism against it, works perfectly well 
as far as finite objects are concerned. For instance, if we need to check whether 
a formula is true in a finite model, we can base our arguments on the laws of Cl. 
Let us formalize this observation as was proposed by Kuznetsov (1979). As an 
example we will consider LC and indicate the points where specific properties 
of this logic are essential. 
Let ip be a formula of length n. According to Example 4.15, p> £ LC means 
that # ^ <p for some linearly ordered frame # containing at most n -I- 1 points. 
We describe this by means of classical formulas, understanding their variables 
in the following way. Suppose we have a model DJI = (#,21) and x, y, z, for 
1 < x,y,z <n + l, are names (numbers) of points in #. With every pair (x, y) of 
points in # we associate a variable pxy whose meaning is “x sees 2/” • And with 
every subformula tp of p> and every point x we associate a variable q£ which 
means “xp is true at x”. Denote by a the conjunction 
It means that ip is true in DJI. And let f3 be the conjunction of the following 
formulas under all possible values of their subscripts: 
PxX 5 
Pxy A Pyz ► Pxzi 
Pxyhqt -> q$, 
Qx ~ -L. 
q$Ax~qt A<£, 

LOGICS THAT ARE NOT POLYNOMIALLY APPROXIMABLE 
549 
(The first two formulas say that R is reflexive and transitive and the rest simulate 
the truth-relation in 971.) Finally, we define a formula saying that our frame is 
linear: 
7= f\{Pxy V Pyx)- 
x^y 
The formula /(</?) = /? A 7 —>■a is of length < 1997 • l3{p) (perhaps the reader 
can reduce the constant) and can be clearly constructed by an algorithm working 
at most linear time of the length of </?. It is readily seen that the following lemma 
holds: 
Lemma 18.2 ip € LC iff /(</?) € Cl. 
As a consequence we obtain 
Theorem 18.3 LC and Cl are polynomially equivalent. 
Later on in the same way we shall establish more general results. But now 
let us have a closer look at the construction we used. Notice that the properties 
of LC were essential only at the following two points: 
• we estimated the size of the frame refuting ip as not exceeding l(ip) -f 1; 
• in the conjunct 7. 
So, if we want to apply such a construction, say to Int instead of LC, then 
we need a polynomial upper bound for the complexity function of Int and do 
not need the conjunct 7 at all (for other logics we may need another formula 
7). Thus we obtain the following conditional “theorem”: if Int is polynomially 
approximable then it is polynomially equivalent to Cl. 
18.2 	Logics that are not polynomially approximable 
In fact, Kuznetsov’s construction was originally created for Int, but it turned 
out that just for Int it cannot be used. We are going to show now that this logic, 
as well as many others, is not polynomially approximable. 
Consider the sequence of formulas 
n— 1 
Pn= f\((->Pi+i -> qi+1) v (pi+i -> qi+1) -+ qi) -> (ipi -> qi) V (pi -> qi). 
i—1 
It should be clear that l(f3n) = O(n)12. We show that every refutation frame 
# = (W, R) for (3n contains at least 2n points. Suppose that under some valuation 
in # the formula (3n is refuted at a point x. Then we have, for 1 < i < n — 1, 
12We write f(n) = 0(g(n)) if there is a constant c > 0 such that /(n) < c • g(n), for all 
n > 0. 

550 
COMPLEXITY PROBLEMS 
Fig. 18.1. 
x ¥= (“'Pi <h) v (Pi -> 9i), 
x |= (-'Pi+i -> qi+i) V (pi+1 -» ft+i) -> ft. 
(18.1) 
(18.2) 
It follows from (18.1) that there are points Xo and X\ for which xRxo, xRxi, 
x0 ft qu xi ft Qi, f= “•Pi, and X\ ft p\. The later two conditions say that 
Xo and xi do not have common successors in Thus (18.1) gives us the binary 
tree of depth 2; see Fig. 18.1. 
Now let us use condition (18.2) for i = 1. Since Xo ft Qi and xi ft #i, we 
have xo ft (~'P2 —> (Z2) V (p2 —> (Z2), ^1 (“*P2 —► <72) V (p2 —> <72) and so there 
are points xoo, #oi, 2:10, £11 such that XiRxij, Xij ft <72, x^o f= “'P2, xn h= P2 for 
all z, j e {0,1}. It follows in particular that no pair of these points has common 
successors in Thus, # contains the full binary tree of depth 3 depicted in 
Fig. 18.1. Continuing in the same way, in n steps we shall extract from # the full 
binary tree of depth n + 1 having 2n final points. 
It remains to observe that (3n is indeed refuted in such a tree, and so /3n $ Int 
(we leave this to the reader as an exercise). Thus, we obtain 
Lemma 18.4 There is a constant n > 0 such that fint{ri) > 2cn. 
As is well known, an exponential function with base > 1 grows more rapidly 
than any polynomial. Therefore, Int cannot be polynomially approximable. Given 
arithmetic functions f(n) and #(n), we write f(n) x g(n) if /(n) = 0(g(n)) and 
g(n) = 0(/(n)). In view of the exponential upper bound for fint(n) obtained in 
Theorem 2.32, we then have 
Theorem 18.5 log2 /int(n) x n- 
Notice that the formulas used in the proof of Lemma 18,4 contain only 
positive occurrences of V which, by Exercise 4.11 and Corollary 15.12, do not belong 
to any consistent si-logic with the disjunction property. Thus we obtain a rather 
unexpected 
Theorem 18.6 No consistent si-logic with the disjunction property is 
polynomially approximable. 
In some cases we can obtain even stronger results. Notice that the proof of 
Lemma 18.4 establishes in fact that the minimal frame refuting (3n contains 
exponentially many final points. Let us have a look now at the interval [KP, ML]. 
As follows from Exercise 2.10, finite rooted frames for logics in it have the 
following property: for every partition of the set of final points in such a frame into 

POLYNOMIALLY APPROXIMABLE LOGICS 
551 
two non-empty sets, there is a point in the frame which sees all points in one 
set and no point in the other. Together with the fact that (3n does not belong to 
ML this gives 
Theorem 18.7 There is a constant c > 0 such that for every logic L in the 
interval [KP,ML], 
„ V O C'tl 
fUn) > 2 • 
Since one can extract from the proof of Theorem 5.44 a twice exponential 
upper bound for /Kp(n)> we ^ave 
Corollary 18.8 log2 log2 /Kp(n) x n- 
Now let us turn to modal logics. The translations we used to embed Int into 
S4, GL, K4 transform /3n into modal formulas with similar semantic properties 
and the length < c • Z(/?n), for some c > 0. Thus, we have the exponential lower 
bound for the complexity functions of all finitely approximable modal logics into 
which the si-logics considered above are embeddable. Taking into account the 
exponential upper bounds for these functions provided by the filtration method, 
we obtain, in particular, the following 
Theorem 18.9 If L € {S4, Grz, S4.1, S4.2, GL, K4} then log2 /x,(n) x n. 
In this theorem we used the fact that frames for all logics under consideration 
are transitive. For K the same construction does not work. However, if in the 
modal translation of f3n we replace subformulas of the form □</? by Ai=o n V then 
the resulting sequence of formulas will again possess the required property with 
the only exception: now the length of formulas in the sequence is not a linear 
but a square function of n. Using the fact the functions of the form 2v/^7™ still 
grow faster than polynomials, we obtain then 
Theorem 18.10 K is not polynomially approximable. 
18.3 	Polynomially approximable logics 
As follows from the results of the preceding section, a necessary condition for a 
logic to be polynomially approximable is that its frames do not contain arbitrarily 
big full finite binary trees. The simplest kinds of logics satisfying this condition 
are logics of finite depth and finite width. In this and the next sections we study 
the complexity of them. We begin with modal logics and then use the fact that 
their si-fragments cannot be more complex. 
First we establish a fact the easy proof of which contains the main features 
of the other proofs in this section. 
Lemma 18.11 Suppose DJX is a transitive model, x a point in DJI and (p a 
formula. Then there is a submodelDJV of DJI containing x and satisfying the following 
properties: 
• the skeletons of DJI and DJI' are isomorphic (more precisely, every cluster 
in DJI has a representative in DJI'); 

552 
COMPLEXITY PROBLEMS 
• each cluster in 971' contains at most l(ip) + 1 points; 
• for every xjj € Sub</? and every y in 9JI', (97t, y) f= tp iff (97t', y) f= 
Proof Let Ufa, • • •, □t/'n be all “boxed” subformulas of <p (we remind the reader 
that O was defined as an abbreviation). Clearly n < /(</?). As the worlds of 971' 
we take x and, for every i e {1 and every cluster C in 971, a point 
in C refuting fa, if any. Besides if a cluster in 971 contains no points of that 
sort, we put in 971' its arbitrary representative. The reader can readily verify 
by induction on the construction of <p that the resulting submodel satisfies the 
required properties. □ 
Thus, we can always assume that the size of clusters in the frames under 
consideration does not exceed the length of the refuting formula (-hi, if 
necessary). It follows immediately that S5 is linearly approximable. But in fact a more 
general result holds. 
Theorem 18.12 (i) Every logic L e {K4BDn, S4 ® bdn : n < w} is 
polynomially approximable, with the power of the corresponding polynomial < n. 
(ii) Every logic L e {Grz ® bdn,GL ® bdn,BDn : n < uj} is polynomially 
approximable, with the power of the corresponding polynomial < n — 1. 
Proof The proofs are similar for all the types of modal logics mentioned in 
the formulation of the theorem, and the result for BDn follows from that for 
Grz ® bdn. So we consider only the case L = K4BDn. 
Suppose <p # K4BDn and let Ufa, for 1 < i < m, be all “boxed” subformulas 
of <p. Then there is a model 971 of depth < n refuting <p at its root x. Now, starting 
with C(x), we mark by some labels some clusters in 971. Namely, if C is a marked 
cluster then, for every i G {l,...,m}, we mark exactly one cluster which is 
accessible from C and contains a point refuting fa, if it exists. It should be clear 
that the total number of marked clusters does not exceed l-hm-hm2-h.. .+mn~1. 
Let 971' be the submodel formed by the marked clusters. One can readily prove 
by induction that 971' refutes ip at x and contains at most n • (i(</?) + l)n points. 
□ 
Let us consider now extensions of some Standard logics with the formulas 
bwn bounding width. 
Theorem 18.13 All logics K4BWn, S4®btun, Grz®btun, GL®btun, BWn, 
for n < UJ, are linearly approximable. 
Proof Again we consider only the modal case. Let L be one of the modal logics 
mentioned in the formulation of our theorem and gL L. Then ip is refuted at the 
root x of a model 971 based upon a finite frame (for L) of width < n. Let Ufa, 
for 1 < i < m, be all “boxed” subformulas of ip. For each i, we fix a maximal 
antichain of points in 971 that refute fa and do not see points from other clusters 
at which fa is false. Now we form the submodel 971' of 971 by putting into it 
x and all points from the selected antichains. It is not hard to check that the 
underlying frame of 971' validates L, 971' refutes <p and the number of points in 
971' is not greater than n • l(<p) + 1. □ 

EXTREMELY COMPLEX LOGICS OF FINITE WIDTH AND DEPTH 553 
A logic, all (normal) extensions of which are polynomially (exponentially, 
quadratically, linearly) approximable, is called hereditarily polynomially 
(respectively, exponentially, quadratically, linearly) approximable. For example, 
hereditarily exponentially approximable are K4BD3 and BD3, which follows from 
the description of the universal frames of finite rank for these logics given in 
Section 8.7. (In the next section we shall see that they are not hereditarily 
polynomially approximable.) Examples of hereditarily polynomially approximable 
logics are provided by the following: 
Theorem 18.14 (i) S4.3 is hereditarily polynomially approximable. 
(ii) S4 0 bds 0 T(wem) is hereditarily quadratically approximable. 
(iii) S4 0 bd<i is hereditarily quadratically approximable. 
Proof We prove only (i) leaving (ii) and (iii) to the reader. As was shown in 
Section 11.3, every extension of S4.3 is characterized by a class of finite chains 
of (non-degenerate) clusters. Let L G ExtS4.3 and ip # L. Then there is a model 
971 based upon a finite chain of clusters for L such that <p is false at its root. 
Using the same strategy as in the proof of Theorem 18.13 we select points in 971 
refuting “boxed” subformulas of ip and form the submodel based upon the set 
of selected points augmented by a point from the final cluster in 971. The reader 
can readily check that the constructed submodel separates ip from L. □ 
18.4 	Extremely complex logics of finite width and depth 
As follows from the description of the universal frames for logics of finite depth 
(see Section 8.7), an upper bound for the complexity function of a logic of depth 
fc > 2 is 
for some constant c > 1. Is it possible to reduce it? The answer is provided by 
the following theorem and its corollary: 
Theorem 18.15 For every k > 2, there is a si-logic L of depth k such that 
Proof For a set X, we denote by V^X the collection of subsets of X containing 
at least two elements and by VX the standard power-set of X. Put V^X = 
V2(V?~lX), with V\X = V2X- VmX is defined analogously. 
Let us consider the intuitionistic Kripke frames = (Wn, Rn) in which, for 
n > 2, 
Wn = {a,ai, • • • ,an} U {bsx : x € .. • ,n}, 1 < s < k - 2}, 
and Rn is the reflexive and transitive closure of the relation R' defined by 
k-2 
cR'd iff 3x, y,i,s (c = a V (c = b\. A d = at A i e x) V 

554 
COMPLEXITY PROBLEMS 
(c = byf 1 Ad = bsxAy£xAl<s<k- 3)). 
The logic characterized by the class of these frames is denoted by L. To show 
that L is as required we shall use the formulas 
a(m) = 0i{m) -> #2(171), 
where 
0i (m) = \f 7x-2) 
xevk~2{l 
7x = A “'(P* A “’Pi-1 A • • • A “’Pi A 9l) A 
i&x 
(Pk-2 -» Pfc-1 V Vfc-l) A Wk-2 -» «k-l V -» 
V “'(p* A “'Pi-1 A ... A -ipi A gi) V -’p*_1 V — 
iex 
for x € P{1,..., ra}, and for other subscripts, 
7x+1 = A A (pLi-i Pfe-iv (pi.-* Pfc-iv Vk-i) • • •)A 
y&x 
(q'k-i-i — «fc-< V (q£_i 9fc_i V -ig£_x) 
V v (Pfe-i -♦ Pfc-i+i v (Pfc-i+i -»•••“» Pfc-i v Vk-i) • • •) V 
yex 
(qLi -»9*-i+iv (fl4-i+i -»•••-» 9k-iv -’fli-i) • • •). 
/32(rn) = V pi V q[ V (gx A -pi A ... A —'P>*._x A ->gi A ... A -» 
92 V (g2 • • • -» Qk—2 V (9fc-2 A (px —> p2) A ... A (pm_x -> pm) -» 
-.px V -i(p2 A -px) V ... V -i(pm A -pm-x))...) V 
(pi A ->qi A —>^i A ... A -'q'k-i -> 
P2 V (pi — • • • -> Pfc-x V Vfc-i)) • ■ •) v 
(«i A ->9x A Vi A ... A -p*._i -> 
4 V (?(, — ... -> 9(._x V -tfk_x))...). 
By a straightforward, though somewhat tedious inspection, one can prove 
Lemma 18.16 For every m > 2, a(m) € L. 
Besides, we have 
Lemma 18.17 For every m> 2, 02{m) $ L. 

EXTREMELY COMPLEX LOGICS OF FINITE WIDTH AND DEPTH 555 
Proof We must show that, for some n, there is a valuation in 5n under which 
fi'iijn) is false at the root of 5n• Put n = m + 6 and let c\ = bx~2, d\ = bx~2, 
ei = bx~2, where 
x^Vk2-2{\ 
£2 £ T^2 2{^ 4~ 1, tyi + 2, m + 3}, 
£3 G P2fc"2{m 4- 4, m 4- 5, m 4- 6}. 
The point c\ is chosen so that it could see the point b1^^ my Then there are 
C2,..., c*;_2 = such that ciRnC2Rn • • • RnCk^RnO'i, for 1 < z < ra. 
Besides, there are c/2,..., dfc_i and e2,..., ejt-i, for which diRnd2Rn • • • Rndk-1, 
eii?ne2i*n • • • Rn^k-i and all points mentioned above are pairwise distinct. 
Notice also that the choice of £2, £3 ensures that the sets of successors of c 1, 
di, e\ are disjoint. 
Define a valuation in $n in such a way that c\ |= q\,..., Ck-2 |= Qk-2, \= Vj» 
4 |= pi,...,4_i |= pjb_1, ei |= gi,...,efc_i |= 4_!, where 1 < i < j < m. It 
is not hard to check that under this valuation 4(m) is refuted at the root of 
3n. □ 
Lemma 18.18 Let $ = (W7, R) be a frame for L refuting bhijn)■ Then 
2m > 
\W\ > 22 jk~2. 
Proof By Lemma 18.16, S )f=- f3i(m) and so there are points in # at which 
the disjuncts of (3i(m) are not true. It is easy to see that distinct disjuncts are 
refuted at distinct points. □ 
To complete the proof of Theorem 18.15, it remains to observe that the length 
of (m) is 0(m). □ 
Corollary 18.19 (i) For every k > 2, there is a logic L G NExtGrz of depth k 
such that 
2n 1 
h(n)> 22 )fc‘2. 
(ii) For every k > 2, there is a logic L € NExtGL of depth k such that 
2n 1 
/l(u)>22' }fe-2. 
For finitely approximable logics of finite width we have no a priory upper 
bounds for their complexity functions. And this is no accident. We are going to 
show now that there are finitely approximable logics of finite width whose 
complexity functions grow more rapidly than an arbitrarily given increasing 
arithmetic function. 

556 
COMPLEXITY PROBLEMS 
Fig. 18.2. 
Theorem 18.20 For every arithmetic function f(n), there is a finitely 
approximate si-logic L of width 2 such that /i,(n) > /(n). 
Proof Without loss of generality we may assume f(n) to be a monotone 
nondecreasing function. Fix a sufficiently big constant c, say 1996, and define L to 
be the si-logic characterized by the class of finite frames $n shown in Fig. 18.2. 
Clearly, L is of width 2. Consider the formulas 
7(m) = 6i(m) —> ^(m), 
where 
62(m) = a\ V Pi V ^(ra), 
6'2(m) = (pi A f\ q'i -► p'2 V (p'2 -4 ... —► p'n V ->p'n) ...)V 
i=1 
n 
Wl A /\ pi -» q'2 V («£ -» ... — q'n V -<) ...), 
i= 1 
ai = r —> p V -p, Pi = -ir —> p V -«p, 02 = Pi —> ai V —1—«p, 
ft =ai->AV -ip, ai+i = pi-totiV Pi-1, /?i+i =qh-> piV 1, 
c-/(m) 
^i(m) = \/ (a* V Pi). 
1=1 
The following lemma is similar to Lemma 18.16, but its proof is not so 
cumbersome. 

ALGORITHMIC PROBLEMS AND COMPLEXITY CLASSES 
557 
Lemma 18.21 For every m> 2, 7(m) G L. 
Proof Let us try to refute 6i(m) —> 62(171), for m > 2, in a frame $n. If 62(171) 
is not true at x then x must see two incomparable chains of > m points (they 
are required to refute 62(i7i)). By the definition of they are subchains of 
ci,..., cn and rfi,..., dn (from which m <n). Besides, to refute aq V fa we must 
have two two-point chains accessible from x and having no common successors; 
these can be only ai, ao and 61,60• Now we prove by induction that ao, ai,..., 
ac /(m) and 60, 61,..., fcc /(m) are ^e final points refuting ao, ai,..., ac.y(m) and 
fa, ft,..., /?c/(m)5 respectively. Using the fact that f(m) is monotone, we see 
that 6i(m) is not true at x either. Thus $n \= 6i(m) —> 62(171). □ 
Lemma 18.22 Suppose $ = (W,R) is a frame for L refuting fa (to). Then 
\W\>2c-f(n). 
Proof As was shown in Lemma 18.21, 6\(m) is refuted in # and so # contains 
at least 2c • f(m) points. □ 
To complete the proof of our theorem, it remains to observe that the length 
of 62(171) is 0(m) and 62(m) £ L for any m.. □ 
Corollary 18.23 (i) For every arithmetic function f(n), there is a finitely 
approximate logic L G NExtGrz of width 2 such that /i,(n) > /(n). 
(i) For every arithmetic function f(n), there is a finitely approximable logic 
L G NExtGL of width 2 such that /x,(n) > /(n). 
18.5 	Algorithmic problems and complexity classes 
Now let us turn to the relationship between the complexity of algorithmic 
problems for modal and si-logics and some standard complexity classes. First we 
consider the class NP of problems that can be solved by polynomial time 
algorithms on nondeterministic machines. Note that here we deal with only 
algorithmic problems of recognizing sets (or properties), i.e., those problems that can 
be formulated as the question ux G XT, for some suitable set X. Such are, for 
instance, the problems “<p € L?” and “</? ^ L?” for a fixed logic L. 
We remind the reader that unlike deterministic machines (each next step of 
which is uniquely determined by the program and the current state of memory 
or configuration), a nondeterministic machine has in general an opportunity to 
choose its next step. For example, a nondeterministic Minsky machine may have 
two or more instructions with the same left part, and which of them will be 
executed is decided “by guess”. It is easy to show that, given such a machine, 
one can construct an equivalent machine whose work consists of two stages: first 
the machine writes by guess some auxiliary word and then it deterministically 
calculates the required result using the word obtained at the first stage, i.e., it 
checks whether the guessed word is suitable for our purpose. The work of the 
machine is regarded as successful if there is a word having guessed which the 
machine produces then a positive (in some sense) result. 

558 
COMPLEXITY PROBLEMS 
Let us consider for example the problem of finding a model for Cl satisfying a 
given formula, which is known as the satisfiability problem for propositional 
formulas. To solve it a standard deterministic algorithm (we do not distinguish here 
between algorithms and the machines realizing them) constructs (in one form or 
another) the truth-table for the formula and looks for T in the column under the 
main connective. Clearly, this is an exponential time algorithm (of the number of 
the formula’s variables). Now we describe a nondeterministic algorithm solving 
the same problem. At the first stage it guesses a suitable valuation of the 
variables and at the second checks whether the formula is true under this valuation. 
Only quadratic time is required for this operation. Thus, the nondeterministic 
algorithm turns out to be much faster. 
Although the concept of nondeterministic algorithm is just an abstraction, it 
is quite useful to understand how complex the problems requiring the exhaustive 
search are. 
Denote by P the class of problems that can be solved by polynomial time 
deterministic algorithms. As we saw above, the satisfiability problem for Boolean 
(classical) formulas is in NP. Does it belong to P? This question is of great 
importance for complexity theory. As is shown by Cook’s theorem below, it is 
equivalent to the question “P = iVP?”, known as the problem of eliminating 
the exhaustive search and regarded often as one of the main problems in this 
theory. 
In spite of its boundlessness, the class NP contains problems that are in a 
sense most representative from the “polynomial point of view”. Call a problem 
“x e XT N P-complete if 
• it belongs to NP and 
• every problem uy e YT in NP is polynomially reducible to the problem 
“x e XT, i.e., there is a polynomial time function (algorithm) f(y) such 
that y e Y iff f(y) e X. 
It is clear that if a problem “x G XT is in NP and some NP-complete problem 
is polynomially reducible to it (in which case “x G XT is called NP-hard) then 
“x G XT is also NP-complete. Besides, to prove that a problem belongs to 
iVP, it is sufficient to reduce it polynomially to some problem in NP. 
For a detailed discussion of the given definitions the reader can consult the 
introduction to complexity theory (Garey and Johnson, 1979) where it is proved in 
particular that the satisfiability problem for Boolean formulas is NP-complete. 
This result is known as Cook’s theorem. It follows immediately that the non- 
derivability problem for Cl, i.e., “<p £ Cl?” is NP-complete too. 
iVP-completeness of the satisfiability problem partly justifies our changing 
from the original problem of searching for a polynomial time decision algorithm 
for a given logic to the problem of establishing its polynomial equivalence to Cl. 
Indeed, if P = NP then Cl as well as any logic polynomially equivalent to Cl 
is decided by a polynomial time algorithm and vice versa. Thus, to justify the 
dubious equality P = NP it would be sufficient to present a polynomial time 
decision algorithm for at least one logic that is polynomially equivalent to Cl. 

ALGORITHMIC PROBLEMS AND COMPLEXITY CLASSES 
559 
However, in any case we know that Cl and all logics poly normally equivalent to 
it are decided by polynomial time nondeterministic algorithms. 
Using the fact, observed in Section 18.1, we see that to establish 
NP-completeness of the nonderivability problem for a consistent logic L it suffices to prove 
that the problem “<p £ L?” belongs to NP. Notice that Theorems 18.12 and 
18.13 yield the following: 
Lemma 18.24 Suppose L is one of the logics K4BDn, S4 0 bdn, Grz 0 bdn, 
GL 0 bdn, BDn, K4BWn, S4 0 bwn, Grz 0 bwn, GL 0 bwn, BWn. Then 
the problem of nonderivability in L is in NP. 
Proof Exercise. (Hint: use suitable modifications of Kuznetsov’s construction.) 
□ 
As a consequence we obtain 
Theorem 18.25 Let L be one of the logics K4BDn, S4 0 bdn, Grz 0 bdn, 
GL 0 bdn, BDn, K4BWn, S4 0 bwn, Grz 0 bwn, GL 0 bwn, BWn. Then 
the problem of nonderivability in L is NP-complete. 
Another complexity class we consider here is the class of problems that can 
be solved by polynomial space (whether deterministic or nondeterministic, see 
Garey and Johnson, 1979) algorithms. It is denoted by PSP ACE. Call a 
problem “re e XT PSP ACE-complete if 
• it belongs to PSP ACE and 
• any problem “y e Y7” in PSP ACE is polynomially reducible to the 
problem “x E XT', i.e., there is a polynomial time function f(y) such that 
y € Y iff f(y) e X. 
It is known that NPC.PSPACE. In particular, both problems “ip € Cl?” 
and “ip £ Cl?” are in PSP ACE (check!). This is not so clear for the logics 
considered in Section 18.2. However, the (non)derivability problem for many of 
them not only belongs to PSP ACE but is also PSPACE-comp\ete. The first 
step to show this is 
Lemma 18.26 Let L e {GL,Grz,Int}. Then the problem “<p € L?” is in 
PSPACE. 
Proof Suppose L = GL. The proof of Theorem 14.25 provides us with a 
decision algorithm for GL. Indeed, ip e GL iff the formula -up —> _L has an inter- 
polant in GL, and to check if this is the case, it is sufficient to construct a finite 
tree model according to the rules supplied by that proof. In general, this 
procedure requires exponential space because it constructs a tree of depth 0(l(ip)) 
and branching 0(l(ip)). However, we need not construct the whole tree at once: 
it is enough to demonstrate that each of its branches can be constructed. This 
can be done as follows. 

560 
COMPLEXITY PROBLEMS 
Let us consider the transition from a tableau (I\ l_Lj) to its immediate 
successors (I\, l_Lj), for 1 < i < ra, where 
ri = r{Xi,nXi,n(^y^: Dxerji 
and Oxi,..., <>Xm are all formulas in T of the form 0%. We need not accomplish 
this transition simultaneously to all these tableaux. First we can pass to (Ti, lIj) 
and try to realize it alone. Having succeeded, we then “clean” the memory and 
pass to (r2,L_L_j), etc. Clearly, we again obtain a decision procedure for GL 
requiring 0(l3(ip)) memory: 0(l2(ip)) for writing and processing each tableau, 
the total number of which does not exceed /((/?). 
The logics Grz and Int may be treated in a similar way, or one can use the 
embeddings of them into GL defined in Section 3.9. □ 
Thus, to complete the proof that the derivability problem in the logics under 
consideration is PSPACE-complete, it remains to show that some PSPACE- 
complete problem is reducible to it, i.e., that it is PS PACE-hard. To this end 
we use the PS PACE-complete truth problem for QBF (quantified Boolean 
formulas): given a Boolean formula <p(pi,... ,pn) and a prefix Qipi... QnPn, where 
each Qi is either V or 3, to check whether the formula Qipi... QnPnViPi, • • •,pn) 
is true. (The formulas Vp^(p) and 3p^(p) are regarded to be true iff ^(T) Aip(F) 
and ^(T) V ip(F) are true, respectively.) It should be clear that it is sufficient 
to consider formulas that are in conjunctive normal form (note however that 
the transformation to this or other standard form can substantially change the 
length of the formula). 
Let ip = Qipi... QnPn'ip(pi, • • • ,Pn) be a Boolean formula with quantifiers 
and 
m it jt 
v- = A(V^*v V 
t=l s=l s=it +1 
(we assume that pst is always in {px,... ,pn}). Now we construct an implicative 
formula <p*. To simulate quantifiers, we require the formulas 
A(tfi, 92,43,44,4) = (Qi A 42 -> 43) A (01 A q2 -* 44) A {qx -> q) A (q2 -+ 4) -* 4, 
E(4i, 42,43,44,4) = (4i A q2 -+ 43) A (qr A q2 -> q4) A {qx A q2 q) q. 
The variables Pi will be simulated by the formulas of the form 6i = qi —> r*, 
= ri_~* Qi- Their intended meaning is as follows: if <5* is refuted then Pi = T 
and if <5* is refuted then pi = F. To refute A (Si, Si, Sj,Sj,q), we need a point, say 
x, at which q is false. Then x sees two points, say x\ and x2, such that x\ |^= Si 
and a2 |^= Si (i.e., we check all the truth-values of Pi), which is ensured by the 
third and fourth conjuncts of the premise. The first and second conjuncts ensure 
that the sets of points above x refuting Si and Si are upward closed. The case of 
refuting E(<5*, 6il Sj, 6j, q) is described analogously but replacing and by or (i.e., 
only one truth-value of pi is chosen). 

ALGORITHMIC PROBLEMS AND COMPLEXITY CLASSES 
561 
With the prefix Qipi... QnPn we associate the formula Qn(fi1, <5i, •..,<5n, 6n) 
in the following way: 
if Qi = V then Qi(<5i,«i) = A(Slj6lj62j62jq); 
if Qi = 3 then Qi(6i,6i) = E(<5i, 61, <52,62, <?); 
if Qn = V then 
Qn(^l5 fill • • • » fin) = (A(fin, fin, <5n_|_i, (5n_|_i, <5n_i) ► ^n—l) A 
(A((5n, <5n, (5n+i, (5n+i, fin-l) y fin— l) * 
Qn—l(fil i fi 1 ? • • • 5 1 ? fin— l) 5 
if Qn = 3 then 
Qn(^l 5 ^15 • • • ? fin) = (E(<5n, fin, (5n_|_i, <5n+l, (5n_i) ► (5n_i) A 
(E((5n, (5n, (5n_|_i, (5n_|_i, (5n_i) ► ^n_i) ► 
Qn—l(fih fill • • • 5 fin— 1? fin— l)j 
Now consider ip(pi,... ,pn) and construct a formula ipk by induction on k: 
*i 31 
(/?! = ( j\^ 6S1 A <^sl ► 6n A <5n) ► Qn(^15 ^15 • • • 5 fim fin)i 
s=l s=ii + l 
ik 3k 
tpk = ( fisk A ^ y fin A fin) ► cpk—i. 
s=l s=ik +1 
Finally, we put (/?* = </?m. The properties of the constructed formulas we need 
are described by the following 
Lemma 18.27 l(p*) = 0(l(ip)) and ip is true iff p* £ Int. 
Proof Exercise. □ 
Using this lemma we easily obtain 
Lemma 18.28 For every logic L £ {GL,Grz,Int}, the problem llp £ L?” is 
PSPACE-hard. 
As a consequence of Lemmas 18.26 and 18.28 we finally have 
Theorem 18.29 For every logic L £ (GL, Grz, Int}, the problem “p £ L?” is 
PS PACE-complete. 
Note that along with Lemma 18.28 we obtain the following analog of 
Theorem 18.6. 
Theorem 18.30 The problem of derivability in any consistent si-logic with the 
disjunction property is PSPACE-hard. 

562 
COMPLEXITY PROBLEMS 
18.6 	Exercises and open problems 
Exercise 18.1 Prove that the polynomial equivalence of logics is an equivalence 
relation, i.e., it satisfies the conditions of reflexivity, transitivity and symmetry. 
Exercise 18.2 Prove that every consistent tabular logic is polynomially 
equivalent to Cl. 
Exercise 18.3 Prove that log2/kc(n) ^ n an<3 that no logic in the interval 
[Int,KC] is polynomially approximable. 
Exercise 18.4 Show that one cannot reduce the power of the polynomials in 
Theorem 18.12. (Hint: consider the intuitionistic formulas 
n—1 
e(m) = y\ 04 -*• bds) - 
S=1 
where, for 1 < m < n, 
m—1 
em= /\ (Pi_1 -» Pi+l) — (Pl_1 “» M,_i) V 
t= 1 
(P2_1 A "’Pi-1 -» bds-1) V ... V (pa~l A p*~\ -» 
and prove that to refute e{m) a frame must contain the full m-ary tree of depth 
n. In the modal case add to the premise of the suitable translation of e(m) the 
conjunct 
m m— 1 
d(A 0(ri A_,n-i) /\Ori A A n(fi-i -► n))-) 
i=2 i—2 
Exercise 18.5 Let an be the formula introduced in Section 12.1. Show that 
the logic K 0 an is polynomially approximable and estimate the power of the 
corresponding polynomial. 
Exercise 18.6 Show that all pretabular logics in Extint and NExtK4 
considered in Chapter 12 are linearly approximable. 
Exercise 18.7 Show that all modal companions of tabular and pretabular si- 
logics are polynomially approximable and estimate the power of the 
corresponding polynomials. 
Exercise 18.8 Prove that every normal finitely approximable extension of the 
logic K4.3 0 DOT is linearly approximable. 
Exercise 18.9 Prove that for every arithmetic function f(n) there is a finitely 
approximable normal extension L of K4.3 such that /l(^) /(n). (Hint: use 
the logic of the frames shown in Fig. 18.3.) 
Exercise 18.10 Show that there is a constant c > 0 such that, for every cofinal 
subframe logic L, /l(p) < 2c n. 

EXERCISES AND OPEN PROBLEMS 
563 
a\ a 2 <13 an b\ 62 6/(n) 
• . • • • • • • • 
Fig. 18.3. 
Exercise 18.11 (i) Prove that there is a logic L e NExtS4 of depth k > 2 such 
that 
2n 1 
h(n)>22' )k~2 
and the si-fragment of L is polynomially approximable. 
(ii) Prove that for every arithmetic function f(n) there is a finitely 
approximable logic L £ NExtS4 of width 2 such that /^(n) > /(n) and pL is linearly 
approximable. 
Exercise 18.12 The diameter of a finite transitive frame # is max{n, m, &}, 
where n is the size of the maximal cluster in m the length of the longest chain 
of points from distinct clusters in # and k the maximal number of immediate 
successors of points in #. Prove that for every logic L in the list K4, S4, Grz, 
S4.1, S4.2, Int, KC, if ip L then ip is separated from L by a frame whose 
diameter does not exceed l(ip). 
Exercise 18.13 Prove that the derivability problem for the logics K, K4, S4 
and KC is PSP ACE-complete. 
Problem 18.1 Prove or disprove the “preservation theoremn: for every si-logic 
L, L is polynomially approximable iffrL is polynomially approximable iff aL is 
polynomially approximable. 
Problem 18.2 Are Int and KP polynomially equivalent? Does KP belong to 
PSPACE? 
Problem 18.3 Is there a recursive upper bound for /ml ? Is there a recursive 
upper bound for the size of the minimal refutation Medvedev frame? 
Problem 18.4 One can easily show that Int in the language with one variable 
is linearly approximable. Is Int in the language with two variables linearly (or 
polynomially) approximable? Is this logic polynomially decidable? What about 
S4, Grz and other standard modal logics in the language with one variable? 
Problem 18.5 Do there exist finitely axiomatizable and finitely approximable 
logics which are more complex than KP ? 
Problem 18.6 Prove that if L is a consistent si-logic different from Cl and 
axiomatizable by formulas in one variable then log /l(^) x n. What is the 
complexity of logics of the form S4 0 ip(p) ? 
Problem 18.7 How does the addition of an essentially negative axiom or □<>- 
axiom do a logic affect its complexity function? 

564 
COMPLEXITY PROBLEMS 
Problem 18.8 Do there exist logics (or calculi) with the C-complete (non) 
derivability problem, where C is an arbitrary member of the hierarchy of Meyer- 
Stockmeyer (for the definition consult Garey and Johnson, 1979)? 
Problem 18.9 Is it true that every polynomially approximable calculus is 
polynomially equivalent to Cl? Or, which is equivalent, is it true that the nonderiv- 
ability problem for such a calculus is NP-complete? 
18.7 	Notes 
The study of complexity problems is a relatively new direction in modal logic. 
Although upper bounds for the size of refutation algebras and frames were found 
for a number of standard logics, usually this was just an intermediate aim in the 
proofs of their decidability. Complexity problems for si-logics were first explicitly 
mentioned by Kuznetsov (1975). Approximately at the same time the studies of 
logical foundations of computer science stimulated some interest in complexity 
aspects of modal logics. 
One of the questions raised by Kuznetsov (1975) was the problem of 
polynomial approximability of Int and its pretabular extensions (Kuznetsov himself 
observed that LC is linearly approximable). Kuznetsov (1979) showed that if this 
problem is solved positively for Int then Int and Cl are polynomially equivalent 
(see Section 18.1). 
The result of Statman (1979), who proved that the derivability problem in 
Int is PS PACE-complete and so a positive solution to Kuznetsov’s question 
would imply that NP = PSP ACE, gave to the complexity direction in modal 
logic another impetus. Ladner (1977) showed that the derivability problem in the 
logics K, T and S4 is PS PACE-complete. He proved also NP- completeness 
of the satisfiability problem in S5 and that S5 is linearly approximable. 
It is to be noted that Statman (1979) and Ladner (1977), defining the length 
of formulas, took into account not only the number of propositional variables 
and connectives in them (i.e., the number of subformulas) but also the length 
of indices: compare for instance the formulas p —> q V r and P1997 —► P19971997 V 
P199719971997- Sometimes calculating the lepgth of indices is redundant. We mean 
logics formulated in languages with finitely many variables. Unfortunately, very 
little is known about the complexity of such logics. We will mention here only one 
question. The Rieger-Nishimura lattice provides us with a linear time decision 
algorithm for Int in the language with one variable. However, nothing is known 
about Int in the languages with two or more variables. On the one hand, to prove 
the lower bound for /int(n) or that the derivability problem in Int is PSPACE- 
hard we used formulas involving infinitely many variables, which suggests that 
the fragments of Int with finitely many variables are possibly much simpler. 
On the other hand, even Int in two variables is rather rich: every negation free 
formula nonderivable in Int (observe that proving the lower bounds we could use 
only negation free formulas; we did not use -1 to construct various “negative” 
examples either) has a substitution instance in two variables that is not in Int. 
And four variables are enough to construct an undecidable si-calculus. 

NOTES 
565 
So we think it would be of interest to study the two-variable fragment of 
Int with respect to both its complexity function and its relation to the standard 
complexity classes P, NP, PSP ACE, etc. The same concerns one-variable 
fragments of modal logics, in particular, S4, Grz. When constructing “very 
complex” logics we were forced to use infinitely many variables. For logics of 
finite depth that was stipulated by their local tabularity. But we do not have 
this restriction in the case of finite width logics and so one can conjecture that 
these logics in finite languages are polynomially (linearly) approximable. It would 
be of interest also to estimate the complexity of KP and ML with finitely many 
variables. 
Note also that instead of polynomial reducibility Statman (1979) and Ladner 
(1977) used the (stronger) log-space reducibility. Whether these two types of 
reducibility are different in this context is an open problem. In any case, we 
do not know any examples of PSP ACE- complete problems with respect to 
polynomial but not log-space reducibility. 
Kuznetsov (1975) claimed that if a si-calculus is polynomially approximable 
then it is polynomially equivalent to Cl. In February 1984 Kuznetsov (he died 
few months later) confessed to one of the authors that he could not reconstruct 
the proof and-had doubts whether his original proof in 1974 was correct. That is 
why we formulate this claim as an open problem. For all polynomially 
approximable calculi known to us (including tense logics of Ono and Nakamura, 1980) 
Kuznetsov’s claim holds. Namely, one can modify in a suitable way the 
construction in Section 18.1 by replacing in it the question about validity with that of 
satisfiability. This incidentally suggests that if NP — coNP then Kuznetsov’s 
problem is solved positively. Is the converse true, i.e., is this problem as hopeless 
as “NP = coNPT'l 
Let us return to the questions raised by Kuznetsov (1975). That Int is not 
polynomially approximable was proved in Zakharyaschev and Popov (1979). 
Chagrov (1983) somewhat strengthened this result and proved also that 
minimal logics of finite width and depth as well as all modal companions of tabular 
and pretabular si-logics are polynomially approximable. The material of 
Sections 18.4 and 18.5 was taken from Chagrov (1985a). Note that the extremely 
complex logics constructed in Section 18.4 are not finitely axiomatizable. 
Moreover, KP is the most complex calculus we know. 
A discussion of complexity problems in modal logics used in artificial 
intelligence can be found in Halpern and Moses (1992). Exercise 18.12) is due 
to Darjania (1979). Complexity aspects of polymodal logics are considered by 
Spaan (1993). 

BIBLIOGRAPHY 
Aczel 1968. P. Aczel. Saturated intuitionistic theories. In H.A. Schmidt, 
K. Schiitte, and H. Thiele, editors, Contribution to Mathematical Logic, pages 
1-11. North-Holland, Amsterdam, 1968. 
Amati and Pirri 1994. G. Amati and F. Pirri. A uniform tableau inethod for 
intuitionistic modal logics I. Studia Logica, 53:29-60, 1994. ) 
Anderson and Belnap 1975. A.R. Anderson and N.D. Belnap. Entaij,ment. The 
Logic of Relevance and Necessity. I. Princeton University Press, (Princeton, 
1975. \ 
Anderson 1972. J.G. Anderson. Superconstructive propositional calhuli with 
extra axiom schemes containing one variable. Zeitschrift fur Mathematische 
Logik und Grundlagen der Mathematik, 18:113-130, 1972. ^ 
Anisov 1982. A.M. Anisov. Axiomatizing classical propositional logic using n 
independent axioms. In Proceedings of the VIHth USSR Conference uLogic 
and Methodology of Science”, Vilnius, pages 5-8, 1982. 
Artemov 1980. S.N. Artemov. Arithmetically complete modal theories. 
Semiotics and Information Science, 14:115-133, 1980. (Russian). 
Artemov 1985. S.N. Artemov. Modal logics axiomatizing provability. 
Mathematics of the USSR, Izvestiya, 49:1123-1154, 1985. (Russian). 
Artemov 1987a. S.N. Artemov. On logical axiomatization of provability. In 
Proceedings of the 8th International Congress of Logic, Methodology and 
Philosophy of Science, pages 7-10, Moscow, 1987. 
Artemov 1987b. S.N. Artemov. Superintuitionistic logics having a provability 
interpretation. Soviet Mathematics Doklady, 34:596-598, 1987. 
Artemov 1995. S.N. Artemov. Operational modal logic. Technical Report 95- 
29, MSI, Cornell University, 1995. 
Baker 1977. K.A. Baker. Finite equational bases for finite algebras in a 
congruence distributive equational class. Advances in Mathematics, 24:207-243, 
1977. 
Balbiani and Herzig 1994. P. Balbiani and A. Herzig. A translation from the 
modal logic of provability into KA. Journal of Applied Non-Classical Logics, 
4:73-78, 1994. 
Banaschevski 1983. B. Banaschevski. The Birkhoff theorem for varieties of finite 
algebras. Algebra Universalis, 17:360-368, 1983. 
Beeson 1985. M. Beeson. Foundation of Constructive Mathematics. 
Mathematical Studies. Springer-Verlag, Berlin, 1985. 
Beklemishev 1989. L.D. Beklemishev. A provability logic without Craig’s 
interpolation property. Mathematical Notes, 45:12-22, 1989. (Russian). 
Beklemishev 1990. L.D. Beklemishev. On the classification of propositional 
provability logics. Mathematics of the USSR, Izvestiya, 35:247-275, 1990. 

568 
BIBLIOGRAPHY 
Bellissima and Mirolli 1989. F. Bellissima and M. Mirolli. A general treatment 
of equivalent modalities. Journal of Symbolic Logic, 54:1460-1471, 1989. 
Bellissima 1984. F. Bellissima. Atoms in modal algebras. Zeitschrift fur Math- 
ematische Logik und Grundlagen der Mathematik, 30:303-312, 1984. 
Bellissima 1985a. F. Bellissima. An effective representation for finitely 
generated free interior algebras. Algebra Universalis, 20:302-317, 1985. 
Bellissima 1985b. F. Bellissima. A test to determine distinct modalities in the 
extensions of 54. Zeitschrift fur Mathematische Logik und Grundlagen der 
Mathematik, 31:57-62, 1985. 
Bellissima 1988. F. Bellissima. On the lattice of extensions of the modal logic 
K.Altn. Archive of Mathematical Logic, 27:107-114, 1988. 
Bellissima 1989. F. Bellissima. Infinite sets of nonequivalent modalities. Notre 
Dame Journal of Formal Logic, 30:574-582, 1989. 
Bellissima 1990. F. Bellissima. Post complete and 0-axiomatizable modal logics. 
Annals of Pure and Applied Logic, 47:121-144, 1990. 
Bellissima 1991. F. Bellissima. Atoms of tense algebras. Algebra Universalis, 
28:52-78, 1991. 
Belnap et ai 1963. N.D. Belnap, H. Leblanc, and R.H. Thomason. On not 
strengthening intuitionistic logic. Notre Dame Journal of Formal Logic, 4:313- 
320, 1963. 
Bessonov 1977. A.V. Bessonov. New operations in intuitionistic calculus. 
Mathematical Notes, 22:503-506, 1977. 
Beth 1956. E.W. Beth. Semantic construction of intuitionistic logic. Med- 
edelingen der Koninklijke Nederlandse Akademie van Wetenschappen, Afd. 
Letterkunde, 19:357-388, 1956. 
Beth 1959. E.W. Beth. The Foundation of Mathematics. A Study in the 
Philosophy of Science. North-Holland, Amsterdam, 1959. 
Birkhoff 1935. G. Birkhoff. On the structure of abstract algebras. Proceedings 
of the Cambridge Philosophical Society, 31:433-454, 1935. 
Birkhoff 1973. G. Birkhoff. Lattice Theory. American Mathematical Society 
Colloquium Publications, Rhode Island, 1973. 
Blok and Dwinger 1975. W. Blok and P. Dwinger. Equational classes of closure 
algebras. Indagationes Mathematicae, 37:189-198, 1975. 
Blok and Kohler 1983. W. J. Blok and P. Kohler. Algebraic semantics for quasi- 
classical modal logics. Journal of Symbolic Logic, 48:941-964, 1983. 
Blok 1976. W.J. Blok. Varieties of interior algebras. PhD thesis, University of 
Amsterdam, 1976. 
Blok 1977. W.J. Blok. The free closure algebra on finitely many generators. 
Indagationes Mathematicae, 39:362-379, 1977. 
Blok 1978. W.J. Blok. On the degree of incompleteness in modal logics and 
the covering relation in the lattice of modal logics. Technical Report 78-07, 
Department of Mathematics, University of Amsterdam, 1978. 
Blok 1979. W.J. Blok. An axiomatization of the modal theory of the veiled 
recession frame. Studia Logica, 38:37-47, 1979. 
Blok 1980a. W.J. Blok. The lattice of modal algebras is not strongly atomic. 

BIBLIOGRAPHY 
569 
Algebra Universalis, 11:285-294, 1980. 
Blok 1980b. W.J. Blok. The lattice of modal logics: an algebraic investigation. 
Journal of Symbolic Logic, 45:221-236, 1980. 
Blok 1980c. W.J. Blok. Pretabular varieties of modal algebras. Studia Logica, 
39:101-124, 1980. 
Boole 1947. G. Boole. The mathematical analysis of logic, being an essay toward 
a calculus of deductive reasoning. Blackwell, Oxford, 1947. 
Boolos and Sambin 1991. G. Boolos and G. Sambin. Provability: the emergence 
of a mathematical modality. Studia Logica, 50:1-23, 1991. 
Boolos 1979. G. Boolos. The Unprovability of Consistency: An Essay in Modal 
Logic. Cambridge University Press, 1979. 
Boolos 1980. G. Boolos. On systems of modal logic with provability 
interpretations. Theoria, 46:7-18, 1980. 
Bowen 1978. K.A. Bowen. Model Theory for Modal Logic. Reidel, Dordrecht, 
1978. 
Bozic and Dosen 1984. M. Bozic and K. Dosen. Models for normal intuitionistic 
logics. Studia Logica, 43:217-245, 1984. 
Brouwer 1907. L.E.J. Brouwer. Over de Grondslagen der Wiskunde. PhD 
thesis, Amsterdam, 1907. Translation: “On the foundation of mathematics” in 
Brouwer, Collected Works, I, (A. Heyting ed.), 1975, North-Holland, 
Amsterdam, pp.11-101. 
Brouwer 1908. L.E.J. Brouwer. De onbetrouwbaarheid der logische principes. 
Tijdschrift voor Wijsbegeerte, 2:152-158, 1908. Translation: The unreliability 
of the logical principles, Ibid, pp.107-111. 
Biichi 1962. J.R. Biichi. On a decision method in restricted second order 
arithmetic. In Logic, Methodology and Philosophy of Science: Proceedings of the 
1960 International Congress, pages 1-11. Stanford University Press, 1962. 
Bull and Segerberg 1984. R.A. Bull and K. Segerberg. Basic modal logic. In 
D. Gabbay and F. Guenthner, editors, Handbook of Philosophical Logic, vol. 
II, pages 1-88. Reidel, Dordrecht, 1984. 
Bull 1966. R.A. Bull. That all normal extensions of 54.3 have the finite model 
property. Zeitschrift fur Mathematische Logik und Grundlagen der Mathe- 
matik, 12:341-344, 1966. 
Bull 1967. R.A. Bull. On the extension of 54 with CLMpMLp. Notre Dame 
Journal of Formal Logic, 8:325-329, 1967. 
Burgess 1984. J.P. Burgess. Basic tense logic. In D.M. Gabbay and F. 
Guenthner, editors, Handbook of Philosophical Logic, volume 2, pages 89-133. Reidel, 
Dordrecht, 1984. 
Buss 1990. S.R. Buss. The modal logic of pure provability. Notre Dame Journal 
of Formal Logic, 31:225-231, 1990. 
Byrd 1978. M. Byrd. On the addition of weakened L-reduction axioms to the 
Brouwer system. Zeitschrift fur Mathematische Logik und Grundlagen der 
Mathematik, 24:405-408, 1978. 
Carnap 1942. R. Carnap. Introduction to Semantics. Harvard University Press, 
Cambridge, 1942. 

570 
BIBLIOGRAPHY 
Carnap 1947. R. Carnap. Meaning and Necessity. A Study in Semantics and 
Modal Logic. The University of Chicago Press, Chicago, 1947. 
Chagrov and Chagrova 1995. A.V. Chagrov and L.A. Chagrova. Algorithmic 
problems concerning first order definability of modal formulas on the class of 
all finite frames. Studia Logica, 55:421-448, 1995. 
Chagrov and Tsytkin 1987. A.V. Chagrov and A.I. Tsytkin. On the approx- 
imability of varieties of pseudo-Boolean algebras. In Proceedings of the XIXth 
USSR Algebraic Conference, L’vov, page 385, 1987. (Russian). 
Chagrov and Zakharyaschev 1991. A.V. Chagrov and M.V. Zakharyaschev. 
The disjunction property of intermediate propositional logics. Studia Logica, 
50:63-75, 1991. 
Chagrov and Zakharyaschev 1992. A.V. Chagrov and M.V. Zakharyaschev. 
Modal companions of intermediate propositional logics. Studia Logica, 51:49- 
82, 1992. 
Chagrov and Zakharyaschev 1993. A.V. Chagrov and M.V. Zakharyaschev. 
The undecidability of the disjunction property of propositional logics and other 
related problems. Journal of Symbolic Logic, 58:49-82, 1993. 
Chagrov and Zakharyaschev 1995a. A.V. Chagrov and M.V. Zakharyaschev. 
On the independent axiomatizability of modal and intermediate logics. 
Journal of Logic and Computation, 5:287-302, 1995. 
Chagrov and Zakharyaschev 1995b. A.V. Chagrov and M.V. Zakharyaschev. 
Sahlqvist formulas are not so elementary even above 54. In L. Csirmaz, D.M. 
Gabbay, and M. de Rijke, editors, Logic Colloquium’92, pages 61-73. CSLI 
Publications, 1995. 
Chagrov 1981. A.V. Chagrov. Superintuitionistic fragments of non-normal 
modal logics. In Mathematical Logic and Mathematical Linguistics, pages 144- 
162. Kalinin State University, Kalinin, 1981. (Russian). 
Chagrov 1982. A.V. Chagrov. On non-normal modal companions of Int. In 
Automata, Algorithms, Languages, pages 133-148. Kalinin State University, 
Kalinin, 1982. (Russian). 
Chagrov 1983. A.V. Chagrov. On the polynomial approximability of modal and 
superintuitionistic logics. In Mathematical Logic, Mathematical Linguistics 
and Algorithm Theory, pages 75-83. Kalinin State University, Kalinin, 1983. 
(Russian). 
Chagrov 1985a. A.V. Chagrov. On the complexity of propositional logics. In 
Complexity Problems in Mathematical Logic, pages 80-90. Kalinin State 
University, Kalinin, 1985. (Russian). 
Chagrov 1985b. A.V. Chagrov. Varieties of logical matrices. Algebra and Logic, 
24:278-325, 1985. 
Chagrov 1986. A.V. Chagrov. The lower bound for the cardinality of 
approximating Kripke frames. In M.I. Kanovich, editor, Logical Methods for 
Constructing Effective Algorithms, pages 96-125. Kalinin State University, 
Kalinin, 1986. (Russian). 
Chagrov 1989. A.V. Chagrov. Nontabularity—pretabularity, antitabularity, co- 
antitabularity. In Algebraic and Logical Constructions, pages 105-111. Kalinin 

BIBLIOGRAPHY 
571 
State University, Kalinin, 1989. (Russian). 
Chagrov 1990a. A.V. Chagrov. Undecidability of the finitary semantical 
consequence. In Proceedings of the XXth USSR Conference on Mathematica Logic, 
Alma-Ata, page 162, 1990. (Russian). 
Chagrov 1990b. A.V. Chagrov. Undecidable properties of extensions of 
provability logic. I. Algebra and Logic, 29:231-243, 1990. 
Chagrov 1990c. A.V. Chagrov. Undecidable properties of extensions of 
provability logic. II. Algebra and Logic, 29:406-413, 1990. 
Chagrov 1992a. A.V. Chagrov. Continuality of the set of maximal superintu- 
itionistic logics with the disjunction property. Mathematical Notes, 51:188- 
193, 1992. 
Chagrov 1992b. A.V. Chagrov. A decidable modal logic with the undecidable 
admissibility problem for inference rules. Algebra and Logic, 31:53-55, 1992. 
Chagrov 1993. A.V. Chagrov. Four intervals of irreducible logics. Bulletin of 
the Section of Logic, 22:167-168, 1993. 
Chagrov 1994a. A.V. Chagrov. On the recursive approximability of modal and 
superintuitionistic logics. In Algebraic and Logical Constructions, pages 91-97. 
Tver State University, Tver, 1994. (Russian). 
Chagrov 1994b. A.V. Chagrov. Some remarks about generalized 
Postcompleteness of extensions of KA. Bulletin of the Section of Logic, 23:27-29, 
1994. 
Chagrov 1994c. A.V. Chagrov. Undecidable properties of superintuitionistic 
logics. In S.V. Jablonskij, editor, Mathematical Problems of Cybernetics, 
volume 5, pages 67-108. Physmatlit, Moscow, 1994. (Russian). 
Chagrov 1995. A.V. Chagrov. One more first-order effect in Kripke semantics. 
In Proceedings of the 10th International Congress of Logic, Methodology and 
Philosophy of Science, page 124, Florence, Italy, 1995. 
Chagrov 1996. A.V. Chagrov. Tabular modal logics: algorithmic problems. 
Manuscript, 1996. 
Chagrova 1986. L.A. Chagrova. On the first order definability of intuitionistic 
formulas with restrictions on occurrences of the connectives. In M.I. Kanovich, 
editor, Logical Methods for Constructing Effective Algorithms, pages 135-136. 
Kalinin State University, Kalinin, 1986. (Russian). 
Chagrova 1987. L.A. Chagrova. An algorithm for constructing first order 
equivalents for disjunction free formulas. In Yu.M. Gorchakov, editor, Logical 
and Algebraic Constructions, pages 96-100. Kalinin State University, Kalinin, 
1987. (Russian). 
Chagrova 1989a. L.A. Chagrova. First order definability of some 
superintuitionistic calculi simulating Minsky’s machines. Technical report, Kalinin State 
University, 1989. (Russian). 
Chagrova 1989b. L.A. Chagrova. On the problem of definability of propositional 
formulas of intuitionistic logic by formulas of classical first order logic. PhD 
thesis, Kalinin State University, 1989. (Russian). 
Chagrova 1989c. L.A. Chagrova. A superintuitionistic calculus simulating 
Minsky’s machine. Technical report, Kalinin State University, 1989. (Russian). 

572 
BIBLIOGRAPHY 
Chagrova 1989d. L.A. Chagrova. Undecidable problems related to the first 
order definability of intuitionistic formulas. Technical report, Kalinin State 
University, 1989. (Russian). 
Chagrova 1990. L.A. Chagrova. On the preservation of first order properties 
under the embedding of intermediate logics into modal logics. In Proceedings of 
the Xth USSR Conference for Mathematical Logic, page 163, 1990. (Russian). 
Chagrova 1991. L.A. Chagrova. An undecidable problem in correspondence 
theory. Journal of Symbolic Logic, 56:1261-1272, 1991. 
Chang and Keisler 1990. C.C. Chang and H.J. Keisler. Model Theory. North- 
Holland, Amsterdam, 1990. 
Chellas 1980. B.F. Chellas. Modal Logic: An Introduction. Cambridge 
University Press, 1980. 
Church 1956. A. Church. Introduction to Mathematical Logic. Part I. Princeton 
University Press, 1956. 
Craig 1953. W. Craig. On axiomatizability within a system. Journal of 
Symbolic Logic, 18:30-32, 1953. 
Craig 1957. W. Craig. Three uses of the Herbrandt-Gentzen theorem in relating 
model theory and proof theory. Journal of Symbolic Logic, 22:269-285, 1957. 
Cresswell 1967. M.J. Cresswell. A Henkin completeness theorem for T. Notre 
Dame Journal of Formal Logic, 8:186-190, 1967. 
Cresswell 1972. M.J. Cresswell. The completeness of 51 and some related 
systems. Notre Dame Journal of Formal Logic, 13:485-496, 1972. 
Cresswell 1983. M.J. Cresswell. KM and the finite model property. Notre Dame 
Journal of Formal Logic, 24:323-327, 1983. 
Cresswell 1985. M.J. Cresswell. The decidable normal modal logics are not 
recursively enumerable. Journal of Philosophical Logic, 14:231-233, 1985. 
Cutland 1980. N. Cutland. Computability. An introduction to recursive function 
theory. Cambridge University Press, 1980. 
Czelakowski 1982. J. Czelakowski. Logical matrices and the amalgamation 
property. Studia Logica, 41:329-341, 1982. 
Czermak 1976. J. Czermak. Distinct modalities are not equivalent in T. 
Zeitschrift fur Mathematische Logik und Grundlagen der Mathematik, 22:123- 
125, 1976. 
Dale 1983. A.J. Dale. The non-independence of axioms in a propositional 
calculus formulated in terms of axiom schemata. Logique et Analyse, 26:91-98, 
1983. 
Darjania 1979. G.K. Darjania. On the complexity of countermodels for the 
intuitionistic propositional calculus. Bulletin of the Academy of Sciences of 
the Georgian SSR, 95:17-20, 1979. 
de Jongh and Troelstra 1966. D.H. J. de Jongh and A.S. Troelstra. On the 
connection of partially ordered sets with some pseudo-Boolean algebras. Indaga- 
tiones Mathematicae, 28:317-329, 1966. 
de Jongh 1968. D.H.J. de Jongh. Investigations on the intuitionistic 
propositional calculus. PhD thesis, University of Wisconsin, Madison, 1968. 
de Jongh 1980. D.H.J. de Jongh. A class of intuitionistic connectives. In K.J. 

BIBLIOGRAPHY 
573 
Barwise, H.J. Keisler, and K. Kunen, editors, The Kleene Symposium, pages 
103-111. North-Holland, Amsterdam, 1980. 
de Rijke 1993. M. de Rijke. Extending Modal Logic. PhD thesis, Universiteit 
van Amsterdam, 1993. 
Diamond and McKinsey 1947. A.H. Diamond and J.C.C. McKinsey. Algebras 
and their subalgebras. Bulletin of the American Mathematical Society, 53:959- 
962, 1947. 
Diego 1966. A. Diego. Sur les algebres de Hilbert. Gauthier-Villars, Paris, 1966. 
Doets 1987. K. Doets. Completeness and definability. PhD thesis, Universiteit 
van Amsterdam, 1987. 
Dosen 1985. K. Dosen. Sequent-systems for modal logic. Journal of Symbolic 
Logic, 50:149-159, 1985. 
Dosen 1988. K. Dosen. Duality between modal algebras and neighbourhood 
frames. Studia Logica, 48:219-234, 1988. 
Dosen 1990. K. Dosen. Normal modal logics in which the Heyting propositional 
calculus can be embedded. In P. Petkov, editor, Mathematical Logic, pages 
293-303. Plenum Press, New York, 1990. 
Drabbe 1967. J. Drabbe. Une propriety des matrices caracteristiques des 
systemes 51, 52, et 53. Comptes Rendus de VAcademie des Sciences, Paris, 
265.-A1, 1967. 
Dragalin 1979. A.G. Dragalin. Mathematical Intuitionism. Introduction to 
Proof Theory. Nauka, Moscow, 1979. (Russian). 
Drugush 1982. Ya.M. Drugush. Union of logics modeled by finite trees. Algebra 
and Logic, 21:97-106, 1982. 
Drugush 1984. Ya.M. Drugush. Finite approximability of forest superintuition- 
istic logics. Mathematical Notes, 36:755-764, 1984. 
Dugundji 1940. J. Dugundji. Note on a property of matrices for Lewis and 
Langford’s calculi of propositions. Journal of Symbolic Logic, 5:150-151, 1940. 
Dummett and Lemmon 1959. M.A.E. Dummett and E.J. Lemmon. Modal 
logics between 54 and 55. Zeitschrift fiir Mathematische Logik und Grundlagen 
der Mathematik, 5:250-264, 1959. 
Dummett 1977. M. Dummett. Elements of Intuitionism. Clarendon Press, 
Oxford, 1977. 
Dziobiak 1978. W. Dziobiak. A note on incompleteness of modal logics with 
respect to neighbourhood semantics. Bulletin of the Section of Logic, 9:136- 
140, 1978. 
Ehrenfeucht 1961. A. Ehrenfeucht. An application of games to the completeness 
problem for formalized theories. Fundamenta Mathematicae, 49:128-141,1961. 
Epstein 1990. R.L. Epstein. The Semantic Foundations of Logic. Volume 1: 
Propositional Logics. Kluwer Academic Publishers, 1990. 
Esakia and Meskhi 1977. L.L. Esakia and V.Yu. Meskhi. Five critical systems. 
Theoria, 40:52-60, 1977. 
Esakia 1974. L.L. Esakia. Topological Kripke models. Soviet Mathematics Dok- 
lady, 15:147-151, 1974. 
Esakia 1979a. L.L. Esakia. On varieties of Grzegorczyk algebras. In A. I. 

574 
BIBLIOGRAPHY 
Mikhailov, editor, Studies in Non-classical Logics and Set Theory, pages 257- 
287. Moscow, Nauka, 1979. (Russian). 
Esakia 1979b. L.L. Esakia. To the theory of modal and superintuitionis- 
tic systems. In V.A. Smirnov, editor, Logical Inference. Proceedings of the 
USSR Symposium on the Theory of Logical Inference, pages 147-172. Nauka, 
Moscow, 1979. (Russian). 
Esakia 1985. L.L. Esakia. Hey ting Algebras I: Duality Theory. Metsniereba, 
Tbilisi, 1985. (Russian). 
Ewald 1986. W.B. Ewald. Intuitionistic tense and modal logic. Journal of 
Symbolic Logic, 51:166-179, 1986. 
Ferrari and Miglioli 1993. M. Ferrari and P. Miglioli. Counting the maximal 
intermediate constructive logics. Journal of Symbolic Logic, 58:1365-1408, 
1993. 
Ferrari and Miglioli 1995a. M. Ferrari and P. Miglioli. A method to single out 
maximal propositional logics with the disjunction property. I. Annals of Pure 
and Applied Logic, 76:1-46, 1995. 
Ferrari and Miglioli 1995b. M. Ferrari and P. Miglioli. A method to single out 
maximal propositional logics with the disjunction property. II. Annals of Pure 
and Applied Logic, 76:117-168, 1995. 
Feys 1965. R. Feys. Modal logics. Gauthier-Villars, Paris, 1965. 
Fine 1971. K. Fine. The logics containing 54.3. Zeitschrift fur Mathematische 
Logik und Grundlagen der Mathematik, 17:371-376, 1971. 
Fine 1972. K. Fine. Logics containing 54 without the finite model property. 
In W. Hodges, editor, Conference in Mathematical Logic-London’70, pages 
98-102. Springer-Verlag, Berlin, 1972. 
Fine 1974a. K. Fine. An ascending chain of 54 logics. Theoria, 40:110-116, 
1974. 
Fine 1974b. K. Fine. An incomplete logic containing 54. Theoria, 40:23-29, 
1974. 
Fine 1974c. K. Fine. Logics containing KA, part I. Journal of Symbolic Logic, 
39:229-237, 1974. 
Fine 1975a. K. Fine. Normal forms in modal logic. Notre Dame Journal of 
Formal Logic, 16:31-42, 1975. 
Fine 1975b. K. Fine. Some connections between elementary and modal logic. 
In S. Kanger, editor, Proceedings of the Third Scandinavian Logic Symposium, 
pages 15-31. North-Holland, Amsterdam, 1975. 
Fine 1985. K. Fine. Logics containing KA, part II. Journal of Symbolic Logic, 
50:619-651, 1985. 
Fischer-Servi 1977. G. Fischer-Servi. On modal logics with an intuitionistic 
base. Studia Logica, 36:141-149, 1977. 
Fischer-Servi 1980. G. Fischer-Servi. Semantics for a class of intuitionistic 
modal calculi. In M. L. Dalla Chiara, editor, Italian Studies in the 
Philosophy of Science, pages 59-72. Reidel, Dordrecht, 1980. 
Fischer-Servi 1984. G. Fischer-Servi. Axiomatizations for some intuitionistic 
modal logics. Rend. Sem. Mat. Univers. Polit., 42:179-194, 1984. 

BIBLIOGRAPHY 
575 
Fitch 1973. F.B. Fitch. A correlation between modalreduction principles and 
properties of relations. Journal of Philosophical Logic, 2:97-101, 1973. 
Fitting 1969. M. Fitting. Intuitionistic Logic, Model Theory and Forcing. 
North-Holland, Amsterdam, 1969. 
Fitting 1983. M. Fitting. Proof Methods for Modal and Intuitionistic Logics. 
Reidel, Dordrecht, 1983. 
Font 1986. J. Font. Modality and possibility in some intuitionistic modal logics. 
Notre Dame Journal of Formal Logic, 27:533-546, 1986. 
Gabbay and de Jongh 1974. D.M. Gabbay and D.H.J. de Jongh. A sequence 
of decidable finitely axiomatizable intermediate logics with the disjunction 
property. Journal of Symbolic Logic, 39:67-78, 1974. 
Gabbay and Guenthner 1984. D.M. Gabbay and F. Guenthner, editors. 
Handbook of Philosophical Logic. Reidel, Dordrecht, 1984. 
Gabbay 1970a. D.M. Gabbay. The decidability of the Kreisel-Putnam system. 
Journal of Symbolic Logic, 35:431-436, 1970. 
Gabbay 1970b. D.M. Gabbay. Selective filtration in modal logic. Theoria, 
30:323-330, 1970. 
Gabbay 1971a. D.M. Gabbay. On decidable, finitely axiomatizable modal and 
tense logics without the finite model property. I, II. Israel Journal of 
Mathematics, 10:478-495, 496-503, 1971. 
Gabbay 1971b. D.M. Gabbay. Semantic proof of the Craig interpolation 
theorem for intuitionistic logic and extensions, I, II. In R.O. Gandy and C.M.E. 
Yates, editors, Logic Colloquium ’69, pages 391-401, 403-410. North Holland, 
Amsterdam, 1971. 
Gabbay 1972a. D.M. Gabbay. Craig’s interpolation theorem for modal logics. 
In W. Hodges, editor, Proceedings of logic conference, London 1970, volume 
255 of Lecture Notes in Mathematics, pages 111-127. Springer-Verlag, Berlin, 
1972. 
Gabbay 1972b. D.M. Gabbay. A general filtration method for modal logics. 
Journal of Philosophical Logic, 1:29-34, 1972. 
Gabbay 1975. D.M. Gabbay. Decidability results in non-classical logics. Annals 
of Mathematical Logic, 8:237-295, 1975. 
Gabbay 1976. D.M. Gabbay. Investigations into Modal and Tense Logics, with 
Applications to Problems in Linguistics and Philosophy. Reidel, Dordrecht, 
1976. 
Gabbay 1977. D.M. Gabbay. On some new intuitionistic propositional 
connectives. 1. Studia Logica, 36:127-139, 1977. 
Gabbay 1981a. D.M. Gabbay. An irreflexivity lemma with application to ax- 
iomatizations of conditions on linear frames. In U. Monnich, editor, Aspects 
of Philosophical Logic, pages 67-89. Reidel, Dordrecht, 1981. 
Gabbay 1981b. D.M. Gabbay. Semantical Investigations in Heyting’s 
Intuitionistic Logic. Reidel, Dordrecht, 1981. 
Galanter 1990. G.I. Galanter. A continuum of intermediate logics which are 
maximal among the logics having the intuitionistic disjunctionless fragment. 
In Proceedings of 10th USSR Conference for Mathematical Logic, page 41, 

576 
BIBLIOGRAPHY 
Alma-Ata, 1990. (Russian). 
Gentzen 1934 35. G. Gentzen. Untersuchungen liber das logische Schliessen. 
Mathematische Zeitschrift, 39:176-210, 405-431, 1934-35. 
Gerson 1975a. M. Gerson. An extension of 54 complete for the neighbourhood 
semantics but incomplete for the relational semantics. Studia Logica, 34:333- 
342, 1975. 
Gerson 1975b. M. Gerson. The inadequacy of the neighbourhood semantics for 
modal logic. Journal of Symbolic Logic, 40:141-147, 1975. 
Gerson 1976. M. Gerson. A neighbourhood frame for T with no equivalent 
relational frame. Zeitschrift fur Mathematische Logik und Grundlagen der 
Mathematik, 22:29-34, 1976. 
Ghilardi and Meloni 1997. S. Ghilardi and G. Meloni. Constructive canon^ity 
in non-classical logics. Annals of Pure and Applied Logic, 1997. To appear. 
Glivenko 1929. V. Glivenko. Sur quelques points de la logique de M. Brouwer. 
Bulletin de la Classe des Sciences de VAcademie Roy ale de Belgique, 15:183- 
188, 1929. 
Goad 1978. C.A. Goad. Monadic infinitary propositional logic: a special 
operator. Reports on Mathematical Logic, 10:43-50, 1978. 
Godel 1932. K. Godel. Zum intuitionistischen Aussagenkalkiil. Anzeiger der 
Akademie der Wissenschaften in Wien, 69:65-66, 1932. 
Godel 1933a. K. Godel. Eine Interpretation des intuitionistischen Aus- 
sagenkalkiils. Ergebnisse eines mathematischen Kolloquiums, 4:39-40, 1933. 
Godel 1933b. K. Godel. Zur intuitionistischen Arithmetik und Zahlentheorie. 
Ergebnisse eines mathematischen Kolloquiums, 4:34-38, 1933. 
Godel 1958. K. Godel. Uber eine bisher noch nicht beniitzte Erweiterung des 
finiten Standpunktes. Dialectica, 12:280-287, 1958. Translation: Journal of 
Philosophical Logic vol.9 (1980), pp.133-142. 
Goldblatt and Thomason 1974. R.I. Goldblatt and S.K. Thomason. Axiomatic 
classes in propositional modal logic. In J. Crossley, editor, Algebraic Logic, 
Lecture Notes in Mathematics vol. J±50, pages 163-173. Springer, Berlin, 1974. 
Goldblatt 1975. R.I. Goldblatt. First-order definability in modal logic. Journal 
of Symbolic Logic, 40:35-40, 1975. 
Goldblatt 1976a. R.I. Goldblatt. Metamathematics of modal logic, Part I. 
Reports on Mathematical Logic, 6:41-78, 1976. 
Goldblatt 1976b. R.I. Goldblatt. Metamathematics of modal logic, Part II. 
Reports on Mathematical Logic, 7:21-52, 1976. 
Goldblatt 1978. R.I. Goldblatt. Arithmetical necessity, provability and intu- 
itionistic logic. Theoria, 44:38-46, 1978. 
Goldblatt 1979. R. Goldblatt. Topoi. The categorial analysis of logic. Studies 
in Logic, vol.98. North-Holland, Amsterdam, 1979. 
Goldblatt 1982. R. Goldblatt. Axiomatizing the Logic of Computer 
Programming, volume 130 of Lecture Notes in Computer Science. Springer-Verlag, 
1982. 
Goldblatt 1987. R.I. Goldblatt. Logics of Time and Computation. Number 7 
in CSLI Lecture Notes. CSLI, 1987. 

BIBLIOGRAPHY 
577 
Goldblatt 1989. R.I. Goldblatt. Varieties of complex algebras. Annals of Pure 
and Applied Logic, 38:173-241, 1989. 
Goldblatt 1991. R.I. Goldblatt. The McKinsey axiom is not canonical. Journal 
of Symbolic Logic, 56:554-562, 1991. 
Goldblatt 1993. R.I. Goldblatt. Mathematics of Modality. Number 43 in CSLI 
Lecture Notes. CSLI, 1993. 
Goncharov and Sviridenko 1985. S.S. Goncharov and D.I. Sviridenko. £- 
programming. In Logical and Mathematical Problems of MOZ, number 107 
in Computing Systems, pages 3-29. Novosibirsk, 1985. (Russian). 
Goranko and Gargov 1993. V. Goranko and G. Gargov. Modal logic with 
names. Journal of Philosophical Logic, 22:607-636, 1993. 
Goranko and Passy 1992. V. Goranko and S. Passy. Using the universal 
modality: Gains and questions. Journal of Logic and Computation, 2:5-30, 1992. 
Goranko 1985. V. Goranko. The Craig interpolation theorem for propositional 
logics with strong negation. Studia Logica, 44:291-317, 1985. 
Goranko 1990. V. Goranko. Modal definability in enriched languages. Notre 
Dame Journal of Formal Logic, 31:81-105, 1990. 
Gratzer 1978. G. Gratzer. General Lattice Theory, volume 75 of Pure and 
Applied Mathematics. Academic Press, New York, 1978. 
Gratzer 1979. G. Gratzer. Universal Algebra. Springer-Verlag, Berlin- 
Heidelberg-New York, 1979. 
Grzegorczyk 1964. A. Grzegorczyk. A philosophically plausible formal 
interpretation of intuitionistic logic. Indagationes Mathematicae, 26:596-601, 1964. 
Grzegorczyk 1967. A. Grzegorczyk. Some relational systems and the associated 
topological spaces. Fundamenta Mathematicae, 60:223-231, 1967. 
Gudovschikov and Rybakov 1982. V.L. Gudovschikov and V.V. Rybakov. The 
disjunction property in modal logics. In Proceedings of 8th USSR Conference 
“Logic and Methodology of Science”, pages 35-36, Vilnius, 1982. (Russian). 
Gurevich 1977. Yu. Gurevich. Intuitionistic logic with strong negation. Studia 
Logica, 36:49-59, 1977. 
Hacking 1963. I. Hacking. What is strict implication? Journal of Symbolic 
Logic, 28:51-71, 1963. 
Hallden 1949. S. Hallden. On the decision problem of Lewis’ calculus 55. Norsk 
Matematisk Tidsskrift, 31:89-94, 1949. 
Hallden 1951. S. Hallden. On the semantical non-completeness of certain Lewis 
calculi. Journal of Symbolic Logic, 16:127-129, 1951. 
Halpern and Moses 1992. J. Halpern and Yo. Moses. A guide to completeness 
and complexity for modal logics of knowledge and belief. Artificial Intelligence, 
54:319-379, 1992. 
Harel 1984. D. Harel. Dynamic logic. In D. M. Gabbay and F. Guenthner, 
editors, Handbook of Philosophical Logic, volume 2. Reidel, Dordrecht, 1984. 
Harrop 1958. R. Harrop. On the existence of finite models and decision 
procedures for propositional calculi. Proceedings of the Cambridge Philosophical 
Society, 54:1-13, 1958. 
Heyting 1930. A. Heyting. Die formalen Regeln der intuitionistischen Logik. 

578 
BIBLIOGRAPHY 
Sitzungsberichte der preussischen Akademie von Wissenschaften, pages 42-56, 
1930. 
Heyting 1956. A. Heyting. Intuitionism. An Introduction. North-Holland, 
Amsterdam, 1956. 
Hintikka 1957. J. Hintikka. Quantifiers in deontic logic. Societas Scientiarum 
Fennica, Commentationes humanarum litterarum, 23:1-23, 1957. 
Hintikka 1961. J. Hintikka. Modality and quantification. Theoria, 27:119-128, 
1961. 
Hintikka 1962. J. Hintikka. Knowledge and Belief. An introduction into the 
logic of the two notions. Cornell University Press, Ithaca, 1962. 
Hintikka 1963. J. Hintikka. The modes of modality. Acta Philosophica Fennica, 
16:65-82, 1963. 
Hodges 1983. W. Hodges. Elementary Predicate Logic. In D. M. Gabbay and 
F. Guenthner, editors, Handbook of Philosophical Logic, volume 1, pages 1- 
131. Reidel, Dordrecht, 1983. 
Horn 1962. A. Horn. The separation theorem of intuitionistic propositional 
logic. Journal of Symbolic Logic, 27:391-399, 1962. 
Hosoi and Ono 1970. T. Hosoi and H. Ono. The intermediate logics on the 
second slice. Journal of the Faculty of Science, University of Tokyo, 17:457- 
461, 1970! 
Hosoi and Ono 1973. T. Hosoi and H. Ono. Intermediate propositional logics 
(A survey). Journal of Tsuda College, 5:67-82, 1973. 
Hosoi 1966a. T. Hosoi. Algebraic proof of the separation theorem on Dummett’s 
LC. Proceedings of the Japan Academy, 42:693-695, 1966. 
Hosoi 1966b. T. Hosoi. On the separation theorem of intermediate propositional 
calculi. Proceedings of the Japan Academy, 42:535-538, 1966. 
Hosoi 1966c. T. Hosoi. The separation theorem on classical system. Journal of 
the Faculty of Science, University of Tokyo, 12:223-230, 1966. 
Hosoi 1967. T. Hosoi. On intermediate logics. Journal of the Faculty of Science, 
University of Tokyo, 14:293-312, 1967. 
Hosoi 1969. T. Hosoi. On intermediate logics. II. Journal of the Faculty of 
Science, University of Tokyo, 16:1-12, 1969. 
Hosoi 1974. T. Hosoi. On intermediate logics III. Journal of Tsuda College, 
6:23-38, 1974. 
Hosoi 1976. T. Hosoi. Non-separable intermediate propositional logics. Journal 
of Tsuda College, 8:13-18, 1976. 
Hughes and Cresswell 1968. G.E. Hughes and M.J. Cresswell. An Introduction 
to Modal Logic. Methuen, London, 1968. 
Hughes and Cresswell 1982. G.E. Hughes and M.J. Cresswell. K 1.1 is not 
canonical. Bulletin of the Section of Logic, 11:109-114, 1982. 
Hughes and Cresswell 1984. G.E. Hughes and M.J. Cresswell. A Companion to 
Modal Logic. Methuen, London, 1984. 
Hughes 1990. G.E. Hughes. Every world can see a reflexive world. Studia Logica, 
49:173-181, 1990. 

BIBLIOGRAPHY 
579 
Isard 1977. S. Isard. A finitely axiomatizable undecidable extension of K. 
Theoria, 43:195-202, 1977. 
Jablonskij 1979. S.V. Jablonskij. Introduction to Discrete Mathematics. Nauka, 
Moscow, 1979. Translation: Mir Publishers, Moscow, 1983. 
Jankov 1963a. V.A. Jankov. Realizable formulas of propositional logic. Soviet 
Mathematics Doklady, 4:1146-1148, 1963. 
Jankov 1963b. V.A. Jankov. The relationship between deducibility in the in- 
tuitionistic propositional calculus and finite implicational structures. Soviet 
Mathematics Doklady, 4:1203-1204, 1963. 
Jankov 1963c. V.A. Jankov. Some superconstructive propositional calculi. 
Soviet Mathematics Doklady, 4:1103-1105, 1963. 
Jankov 1967. V.A. Jankov. Finite validity of formulas of a special form. Soviet 
Mathematics Doklady, 8:648-650, 1967. 
Jankov 1968a. V.A. Jankov. The calculus of the weak “law of excluded middle”. 
Mathematics of the USSR, Izvestiya, 2:997-1004, 1968. 
Jankov 1968b. V.A. Jankov. The construction of a sequence of strongly 
independent superintuitionistic propositional calculi. Soviet Mathematics Doklady, 
9:806-807, 1968. 
Jankov 1968c. V.A. Jankov. On the extension of the intuitionistic propositional 
calculus to the classical calculus, and the minimal calculus to the intuitionistic 
calculus. Mathematics of the USSR, Izvestiya, 2:205-208, 1968. 
Jankov 1969. V.A. Jankov. Conjunctively indecomposable formulas in 
propositional calculi. Mathematics of the USSR, Izvestiya, 3:17-35, 1969. 
Jaskowski 1936. S. Jaskowski. Recherches sur le systeme de la logique intu- 
itioniste. In Actes Du Congres Intern. De Phil. Scientifique. VI. Phil. Des 
Mathematiques, Act. Sc. Et Ind 393, Paris, pages 58-61, 1936. 
Jonsson and Tarski 1951. B. Jonsson and A. Tarski. Boolean algebras with 
operators. I. American Journal of Mathematics, 73:891-939, 1951. 
Jonsson and Tarski 1952. B. Jonsson and A. Tarski. Boolean algebras with 
operators. II. American Journal of Mathematics, 74:127-162, 1952. 
Jonsson 1967. B. Jonsson. Algebras whose congruence lattices are distributive. 
Mathematica Scandinavica, 21:110-121, 1967. 
Jonsson 1994. B. Jonsson. On the canonicity of Sahlqvist identities. Studia 
Logica, 53:473-491, 1994. 
Kalicki 1980. C. Kalicki. Infinitary propositional intuitionistic logic. Notre 
Dame Journal of Formal Logic, 21:216-228, 1980. 
Kanger 1957a. S. Kanger. The Morning Star paradox. Theoria, 23:1-11, 1957. 
Kanger 1957b. S. Kanger. A note on quantification and modalities. Theoria, 
23:131-134, 1957. 
Khomich 1979. V.I. Khomich. Separability of superintuitionistic propositional 
logics. In A. A. Markov and V.I. Khomich, editors, Studies in Algorithm Theory 
and Mathematical Logic, pages 98-115. Nauka, Moscow, 1979. (Russian). 
Kirk 1979. R.E. Kirk. Some classes of Kripke frames characteristic for the 
intuitionistic logic. Zeitschrift fur Mathematische Logik und Grundlagen der 
Mathematik, 25:409-410, 1979. 

580 
BIBLIOGRAPHY 
Kirk 1980. R.E. Kirk. A characterization of the classes of finite tree frames 
which are adequate for the intuitionistic logic. Zeitschrift fiir Mathematische 
Logik und Grundlagen der Mathematik, 26:497-501, 1980. 
Kirk 1982. R.E. Kirk. A result on propositional logics having the disjunction 
property. Notre Dame Journal of Formal Logic, 23:71-74, 1982. 
Kleene 1945. S. Kleene. On the interpretation of intuitionistic number theory. 
Journal of Symbolic Logic, 10:109-124, 1945. 
Kleene 1967. S. Kleene. Mathematical Logic. John Wiley & Sons, Inc., New 
York, 1967. 
Kleyman 1984. Yu.G. Kleyman. Some questions in the theory of varieties of 
groups. Mathematics of the USSR, Izvestiya, 22:33-65, 1984. 
Kolmogorov 1925. A.N. Kolmogorov. On the principle tertium non datur. 
Mathematics of the USSR, Sbomik, 32:646-667, 1925. Translation in: From 
Frege to Godel: A Source Book in Mathematical Logic 1879-1931 (J. van 
Heijenoord ed.), Harvard University Press, Cambridge 1967. 
Kolmogorov 1932. A.N. Kolmogorov. Zur Deutung der intuitionistischen Logik. 
Mathematische Zeitschrift, 35:58-65, 1932. 
Kracht and Wolter 1991. M. Kracht and F. Wolter. Properties of independently 
axiomatizable bimodal logics. Journal of Symbolic Logic, 56:1469-1485, 1991. 
Kracht and Wolter 1997. M. Kracht and F. Wolter. Normal monomodal logics 
can simulate all others. Journal of Symbolic Logic, 1997. To appear. 
Kracht 1990. M. Kracht. An almost general splitting theorem for modal logic. 
Studia Logica, 49:455-470, 1990. 
Kracht 1993a. M. Kracht. How completeness and correspondence theory got 
married. In M. de Rijke, editor, Diamonds and Defaults, pages 175-214. 
Kluwer Academic Publishers, 1993. 
Kracht 1993b. M. Kracht. Prefinitely axiomatizable modal and intermediate 
logics. Mathematical Logic Quarterly, 39:301-322, 1993. 
Kracht 1993c. M. Kracht. Splittings and the finite model property. Journal of 
Symbolic Logic, 58:139-157, 1993. 
Kracht 1995. M. Kracht. Highway to the danger zone. Journal of Logic and 
Computation, 5:93-109, 1995. 
Kreisel and Putnam 1957. G. Kreisel and H. Putnam. Eine Unableitbarkeitsbe- 
weismethode fiir den intuitionistischen Aussagenkalkiil. Zeitschrift fur 
Mathematische Logik und Grundlagen der Mathematik, 3:74-78, 1957. 
Kripke 1959. S.A. Kripke. A completeness theorem in modal logic. Journal of 
Symbolic Logic, 24:1-14, 1959. 
Kripke 1963a. S. Kripke. Semantical analysis of modal logic, Part I. Zeitschrift 
fur Mathematische Logik und Grundlagen der Mathematik, 9:67-96, 1963. 
Kripke 1963b. S. Kripke. Semantical considerations on modal logic. Acta Philo- 
sophica Fennica, 16:83-94, 1963. 
Kripke 1965a. S.A. Kripke. Semantical analysis of intuitionistic logic. I. In J.N. 
Crossley and M.A.E. Dummett, editors, Formal Systems and Recursive 
Functions. Proceedings of the 8th Logic Colloquium, pages 92-130. North-Holland, 
1965. 

BIBLIOGRAPHY 
581 
Kripke 1965b. S.A. Kripke. Semantical analysis of modal logic II: Non-normal 
modal propositional calculi. In J.W. Addison, L. Henkin, and A. Tarski, 
editors, The Theory of Models, pages 206-220. North-Holland, Amsterdam, 1965. 
Kuznetsov and Gerchiu 1970. A.V. Kuznetsov and V.Ya. Gerchiu. Superintu- 
itionistic logics and the finite approximability. Soviet Mathematics Doklady, 
11:1614-1619, 1970. 
Kuznetsov and Muravitskij 1977. A.V. Kuznetsov and A.Yu. Muravitskij. Ma- 
gari’s algebras. In Proceedings of the 14th USSR Algebraic Conference, Part 
II, pages 105-106. Institute of Mathematics, Novosibirsk, 1977. (Russian). 
Kuznetsov and Muravitskij 1980. A.V. Kuznetsov and A.Yu. Muravitskij. 
Provability as modality. In Actual Problems of Logic and Methodology of 
Science, pages 193-230. Naukova Dumka, Kiev, 1980. (Russian). 
Kuznetsov and Muravitskij 1986. A.V. Kuznetsov and A.Yu. Muravitskij. On 
superintuitionistic logics as fragments of proof logic extensions. Studia Logica, 
45:77-99, 1986. 
Kuznetsov 1963. A.V. Kuznetsov. Undecidability of general problems of 
completeness, decidability and equivalence for propositional calculi. Algebra and 
Logic, 2:47-66, 1963. (Russian). 
Kuznetsov 1965. A.V. Kuznetsov. Analogs of the “Sheffer stroke” in 
constructive logic. Soviet Mathematics Doklady, 6:70-74, 1965. 
Kuznetsov 1971. A.V. Kuznetsov. Some properties of the structure of varieties 
of pseudo-Boolean algebras. In Proceedings of the Xlth USSR Algebraic 
Colloquium, pages 255-256, Kishinev, 1971. (Russian). 
Kuznetsov 1975. A.V. Kuznetsov. On superintuitionistic logics. In Proceedings 
of the International Congress of Mathematicians, pages 243-249, Vancouver, 
1975. 
Kuznetsov 1979. A.V. Kuznetsov. Tools for detecting non-derivability or non- 
expressibility. In V.A. Smirnov, editor, Logical Inference. Proceedings of the 
USSR Symposium on the Theory of Logical Inference, pages 5-23. Nauka, 
Moscow, 1979. (Russian). 
Kuznetsov 1985. A.V. Kuznetsov. Proof-intuitionistic propositional calculus. 
Doklady Academii Nauk SSSR, 283:27-30, 1985. (Russian). 
Ladner 1977. R.E. Ladner. The computational complexity of provability in 
systems of modal logic. SIAM Journal on Computing, 6:467-480, 1977. 
Lemmon and Scott 1977. E.J. Lemmon and D.S. Scott. An Introduction to 
Modal Logic. Oxford, Blackwell, 1977. 
Lemmon 1957. E.J. Lemmon. New foundations for Lewis’s modal systems. 
Journal of Symbolic Logic, 22:176-186, 1957. 
Lemmon 1966a. E.J. Lemmon. Algebraic semantics for modal logic. I. Journal 
of Symbolic Logic, 31:46-65, 1966. 
Lemmon 1966b. E.J. Lemmon. Algebraic semantics for modal logic. II. Journal 
of Symbolic Logic, 31:191-218, 1966. 
Lemmon 1966c. E.J. Lemmon. A note on Hallden-incompleteness. Notre Dame 
Journal of Formal Logic, 7:296-300, 1966. 

582 
BIBLIOGRAPHY 
Levin 1969. V.A. Levin. Some syntactic theorems on the calculus of finite 
problems of Yu.T. Medvedev. Soviet Mathematics Doklady, 10:288-290, 1969. 
Lewis and Langford 1932. C.I. Lewis and C.H. Langford. Symbolic Logic. 
Appleton-Century-Crofts, New York, 1932. 
Lewis 1918. C.I. Lewis. A Survey of Symbolic Logic. University of California 
Press, Berkeley, 1918. 
Linial and Post 1949. S. Linial and E.L. Post. Recursive unsolvability of the 
deducibility, Tarski’s completeness and independence of axioms problems of 
the propositional calculus. Bulletin of the American Mathematical Society, 
55:50, 1949. 
Lukasiewicz 1920. J. Lukasiewicz. On three-valued logic. Ruch Filozoficzny, 
5:169-171, 1920. Translation: in Polish Logic 1920-39, (S. McCall ed.), 1967, 
Clarendon Press, Oxford, pp.16-18. 
Lukasiewicz 1952. J. Lukasiewicz. On the intuitionistic theory of deduction. 
Indagationes Mathematicae, 14:202-212, 1952. 
Makinson and Segerberg 1974. D.C. Makinson and K. Segerberg. Post 
completeness and ultrafilters. Zeitschrift fur Mathematische Logik und Grundlagen 
der Mathematik, 20:385-388, 1974. 
Makinson 1966. D.C. Makinson. On some completeness theorems in modal 
logic. Zeitschrift fur Mathematische Logik und Grundlagen der Mathematik, 
12:379-384, 1966. 
Makinson 1969. D.C. Makinson. A normal modal calculus between T and 54 
without the finite model property. Journal of Symbolic Logic, 34:35-38, 1969. 
Makinson 1970. D.C. Makinson. A generalization of the concept of a relational 
model for modal logic. Theoria, 36:331-335, 1970. 
Makinson 1971. D.C. Makinson. Some embedding theorems for modal logic. 
Notre Dame Journal of Formal Logic, 12:252-254, 1971. 
Maksimova and Rybakov 1974. L.L. Maksimova and V.V. Rybakov. Lattices 
of modal logics. Algebra and Logic, 13:105-122, 1974. 
Maksimova et al. 1979. L.L. Maksimova, V.B. Shehtman, and D.P. Skvortsov. 
The impossibility of a finite axiomatization of Medvedev’s logic of finitary 
problems. Soviet Mathematics Doklady, 20:394-398, 1979. 
Maksimova 1972. L.L. Maksimova. Pretabular super intuitionistic logics. 
Algebra and Logic, 11:308-314, 1972. 
Maksimova 1975a. L.L. Maksimova. Modal logics of finite slices. Algebra and 
Logic, 14:188-197, 1975. 
Maksimova 1975b. L.L. Maksimova. Pretabular extensions of Lewis 54. Algebra 
and Logic, 14:16-33, 1975. 
Maksimova 1977. L.L. Maksimova. Craig’s theorem in superintuitionistic logics 
and amalgamable varieties of pseudo-Boolean algebras. Algebra and Logic, 
16:427-455, 1977. 
Maksimova 1979. L.L. Maksimova. Interpolation theorems in modal logic and 
amalgamable varieties of topological Boolean algebras. Algebra and Logic, 
18:348-370, 1979. 

BIBLIOGRAPHY 
583 
Maksimova 1980. L.L. Maksimova. Interpolation theorems in modal logics. 
Sufficient conditions. Algebra and Logic, 19:120-132, 1980. 
Maksimova 1982a. L.L. Maksimova. Failure of the interpolation property in 
modal companions of Dummett’s logic. Algebra and Logic, 21:690-694, 1982. 
Maksimova 1982b. L.L. Maksimova. Lyndon’s interpolation theorem in modal 
logics. In Mathematical Logic and Algorithm Theory, pages 45-55. Institute 
of Mathematics, Novosibirsk, 1982. (Russian). 
Maksimova 1984. L.L. Maksimova. On the number of maximal intermediate 
logics having the disjunction property. In Proceedings of the 7th USSR 
Conference for Mathematical Logic, page 95. Institute of Mathematics, Novosibirsk, 
1984. (Russian). 
Maksimova 1986. L.L. Maksimova. On maximal intermediate logics with the 
disjunction property. Studia Logica, 45:69-75, 1986. 
Maksimova 1987. L.L. Maksimova. On the interpolation in normal modal logics. 
Non-classical Logics, Studies in Mathematics, 98:40-56, 1987. (Russian). 
Maksimova 1989a. L.L. Maksimova. A continuum of normal extensions of 
the modal provability logic with the interpolation property. Sibirskij 
Matematiceskij Zumal, 30:122-131, 1989. (Russian). 
Maksimova 1989b. L.L. Maksimova. Definability theorems in normal extensions 
of the provability logic. Studia Logica, 48:495-507, 1989. 
Maksimova 1989c. L.L. Maksimova. Interpolation in the modal logics of the 
infinite slice containing the logic K4. In Mathematical Logic and Algorothmic 
Problems, pages 73-91. Nauka, Novosibirsk, 1989. (Russian). 
Maksimova 1992a. L.L. Maksimova. The Beth properties, interpolation, and 
amalgamability in varieties of modal algebras. Soviet Mathematics Doklady, 
44:327-331, 1992. 
Maksimova 1992b. L.L. Maksimova. Definability and interpolation in classical 
modal logics. Contemporary Mathematics, 131:583-599, 1992. 
Maksimova 1992c. L.L. Maksimova. Temporal logics with “the next” operator 
do not have interpolation or the Beth property. Siberian Mathematical Journal, 
32:989-993, 1992. 
Maksimova 1995. L.L. Maksimova. On variable separation in modal and super- 
intuitionistic logics. Studia Logica, 55:99-112, 1995. 
Mal’cev 1970. A.I. Mal’cev. Algorithms and Recursive Functions. Wolters- 
Noordhoff, Groningen, 1970. 
Mal’cev 1973. A.I. Mal’cev. Algebraic Systems. Springer-Verlag, Berlin- 
Heidelberg, 1973. 
Mardaev 1984. S.I. Mardaev. The number of prelocally tabular superintuition- 
istic propositional logics. Algebra and Logic, 23:56-66, 1984. 
Mardaev 1987. S.I. Mardaev. Embeddings of implicative lattices and superin- 
tuitionistic logics. Algebra and Logic, 26:178-205, 1987. 
Mardaev 1992. S.I. Mardaev. Fixed points of modal schemes. Algebra and 
Logic, 31:493-498, 1992. (Russian). 
Mardaev 1993a. S.I. Mardaev. Least fixed points in the Godel-Lob logic. 
Algebra and Logic, 32:683-689, 1993. (Russian). 

584 
BIBLIOGRAPHY 
Mardaev 1993b. S.I. Mardaev. Least fixed points in the Grzegorczyk logic and 
intuitionistic propositional logic. Algebra and Logic, 32:519-536, 1993. 
(Russian). 
McCullough 1971. D.P. McCullough. Logical connectives for intuitionistic 
propositional logic. Journal of Symbolic Logic, 36:15-20, 1971. 
McKay 1968. C.G. McKay. The decidability of certain intermediate logics. 
Journal of Symbolic Logic, 33:258-264, 1968. 
McKay 1971. C.G. McKay. A class of decidable intermediate propositional 
logics. Journal of Symbolic Logic, 36:127-128, 1971. 
McKenzie 1972. R. McKenzie. Equational bases and non-modular lattice 
varieties. Transactions of the American Mathematical Society, 174:1-43, 1972. 
McKinsey and Tarski 1944. J.C.C. McKinsey and A. Tarski. The algebra of 
topology. Annals of Mathematics, 45:141-191, 1944. 
McKinsey and Tarski 1946. J.C.C. McKinsey and A. Tarski. On closed 
elements in closure algebras. Annals of Mathematics, 47:122-162, 1946. 
McKinsey and Tarski 1948. J.C.C. McKinsey and A. Tarski. Some theorems 
about the sentential calculi of Lewis and Heyting. Journal of Symbolic Logic, 
13:1-15, 1948. 
McKinsey 1939. J.C.C. McKinsey. Proof of the independence of the 
primitive symbols of Heyting’s calculus of propositions. Journal of Symbolic Logic, 
4:155-158, 1939. 
McKinsey 1940. J.C.C. McKinsey. Proof that there are infinitely many 
modalities in Lewis’ system 52. Journal of Symbolic Logic, 5:110-112, 1940. 
McKinsey 1941. J.C.C. McKinsey. A solution of the decision problem for the 
Lewis systems 52 and 54, with an application to topology. Journal of Symbolic 
Logic, 6:117-134, 1941. 
McKinsey 1944. J.C.C. McKinsey. On the number of complete extensions of 
the Lewis systems of sentential calculus. Journal of Symbolic Logic, 9:42-45, 
1944. 
McKinsey 1953. J.C.C. McKinsey. Systems of modal logic which are not 
unreasonable in the sense of Hallden. Journal of Symbolic Logic, 18:109-113, 
1953. 
Medvedev 1962. Yu.T. Medvedev. Finite problems. Soviet Mathematics Dok- 
lady, 3:227-230, 1962. 
Medvedev 1963. Yu.T. Medvedev. Interpretation of logical formulas by means 
of finite problems and its relation to the realizability theory. Soviet 
Mathematics Doklady, 4:180-183, 1963. 
Medvedev 1966. Yu.T. Medvedev. Interpretation of logical formulas by means 
of finite problems. Soviet Mathematics Doklady, 7:857-860, 1966. 
Medvedev 1979. Yu.T. Medvedev. Transformations of information and calculi 
that describe them: types of information and their possible transformations. 
Semiotics and Information Science, 13:109-141, 1979. (Russian). 
Mendelson 1984. E. Mendelson. Introduction to Mathematical Logic. Van 
Nostrand, New York, 1984. 
Meredith 1953. C.A. Meredith. Single axioms for the system (C, N), (C,0) 

BIBLIOGRAPHY 
585 
and (A, N) of the two-valued propositional calculus. Journal of Computing 
Systems, 1:155-164, 1953. 
Meskhi 1983. V.Yu. Meskhi. Critical modal logics containing the Brouwer 
axiom. Mathematical Notes, 33:65-69, 1983. 
Minari 1986. P. Minari. Intermediate logics with the same disjunctionless 
fragment as intuitionistic logic. Studia Logica, 45:207-222, 1986. 
Mints 1974. G.E. Mints. Lewis’ systems and T (a survey 1965-1973). In Feys, 
Modal Logic, pages 422-509. Nauka, Moscow, 1974. (Russian). 
Montague 1968. R. Montague. Pragmatics. In R. Klibansky, editor, 
Contemporary Philosophy. A Survey. I, pages 102-122. La Nuova Editrice, Florence, 
1968. 
Muravitskij 1985. A.Yu. Muravitskij. Correspondence of proof-intuitionistic 
logic extensions to provability logic extensions. Soviet Mathematics Doklady, 
31:345-348, 1985. 
Muravitskij 1988. A.Yu. Muravitskij. Embedding of extensions of the Grze- 
gorczyk logic into extensions of provability logic. In Proceedings of the IVth 
Soviet-Finland Symposium for Mathematical Logic, pages 74-80, Tbilisi, 1988. 
(Russian). 
Nadel 1978. M.A. Nadel. Infinitary intuitionistic logic from a classical point of 
view. Annals of Mathematical Logic, 14:159-192, 1978. 
Nagle and Thomason 1985. M.C. Nagle and S.K. Thomason. The extensions of 
the modal logic Kb. Journal of Symbolic Logic, 50:102-108, 1985. 
Nagle 1981. M.C. Nagle. The decidability of normal AT5-logics. Journal of 
Symbolic Logic, 46:319-328, 1981. 
Nelson 1947. D. Nelson. Recursive functions and intuitionistic number theory. 
Transactions of the American Mathematical Society, 61:307-368, 1947. 
Nishimura 1960. I. Nishimura. On formulas of one variable in intuitionistic 
propositional calculus. Journal of Symbolic Logic, 25:327-331, 1960. 
Novikov 1977. P.S. Novikov. Constructive Mathematical Logic from the Point 
of View of Classical Logic. Nauka, Moscow, 1977. (Russian). 
Ono and Nakamura 1980. H. Ono and A. Nakamura. On the size of refutation 
Kripke models for some linear modal and tense logics. Studia Logica, 39:325- 
333, 1980. 
Ono 1970. H. Ono. Kripke models and intermediate logics. Publications of 
the Research Institute for Mathematical Science, Kyoto University, 6:461-476, 
1970. 
Ono 1971. H. Ono. On the finite model property for Kripke models. Publications 
of the Research Institute for Mathematical Science, Kyoto University, 7:85-93, 
1971. 
Ono 1972. H. Ono. Some results on the intermediate logics. Publications of 
the Research Institute for Mathematical Science, Kyoto University, 8:117-130, 
1972. 
Ono 1977. H. Ono. On some intuitionistic modal logics. Publications of the 
Research Institute for Mathematical Science, Kyoto University, 13:55-67, 1977. 

586 
BIBLIOGRAPHY 
Orlov 1928. I.E. Orlov. The calculus of compatibility of propositions. 
Mathematics of the USSR, Sbomik, 35:263-286, 1928. (Russian). 
Parry 1939. W.T. Parry. Modalities in the Survey system of strict implication. 
Journal of Symbolic Logic, 4:137-154, 1939. 
Pitts 1992. A.M. Pitts. On an interpretation of second order quantification in 
first order intuitionistic propositional logic. Journal of Symbolic Logic, 57:33- 
52, 1992. 
Prior 1957. A. Prior. Time and Modality. Clarendon Press, Oxford, 1957. 
Rabin 1969. M.O. Rabin. Decidability of second order theories and automata 
on infinite trees. Transactions of the American Mathematical Society, 141:1- 
35, 1969. 
Rafter 1994. J. Rafter. A partial characterization of canonical conjugate 
varieties of modal algebras. PhD thesis, Vanderbilt University, 1994. 
Rasiowa and Sikorski 1963. H. Rasiowa and R. Sikorski. The Mathematics of 
Metamathematics. Polish Scientific Publishers, 1963. 
Rasiowa 1974. H. Rasiowa. An Algebraic Approach to Non-classical Logics. 
North-Holland, Amsterdam, 1974. 
Ratsa 1982. M.F. Ratsa. Functional completeness in intuitionistic propositional 
logic. In S.V. Jablonskij, editor, Problems of Cybernetics, volume 39, pages 
107-150. Nauka, Moscow, 1982. (Russian). 
Rautenberg 1977. W. Rautenberg. Der Verband der normalen verzweigten 
Modallogiken. Mathematische Zeitschrift, 156:123-140, 1977. 
Rautenberg 1979. W. Rautenberg. Klassische und nichtklassische Aussagen- 
logik. Vieweg, Braunschweig-Wiesbaden, 1979. 
Rautenberg 1980. W. Rautenberg. Splitting lattices of logics. Archiv fur 
Mathematische Logik, 20:155-159, 1980. 
Rautenberg 1983. W. Rautenberg. Modal tableau calculi and interpolation. 
Journal of Philosophical Logic, 12:403-423, 1983. 
Reidhaar-Olson 1990. L. Reidhaar-Olson. A new proof of the fixed-point 
theorem of provability logic. Notre Dame Journal of Formal Logic, 31:37-43, 
1990. 
Rennie 1970. R. Rennie. Models for multiply modal systems. Zeitschrift fur 
Mathematische Logik und Grundlagen der Mathematik, 16:175-186, 1970. 
Rieger 1949. L. Rieger. On the lattice of Brouwerian propositional logics. Acta 
Universitatis Carolinae. Mathematica et Physica, 189, 1949. 
Rodenburg 1986. P.H. Rodenburg. Intuitionistic correspondence theory. PhD 
thesis, University of Amsterdam, 1986. 
Rose 1953. G.F. Rose. Propositional calculus and realizability. Transactions of 
the American Mathematical Society, 75:1-19, 1953. 
Routley 1970. R. Routley. Extensions of Makinson’s completeness theorems in 
modal logic. Zeitschrift fur Mathematische Logik und Grundlagen der 
Mathematik, 16:239-259, 1970. 
Ruitenburg 1984. W. Ruitenburg. On the period of sequences (An(p)) in the 
intuitionistic propositional calculus. Journal of Symbolic Logic, 49:892-899, 
1984. 

BIBLIOGRAPHY 
587 
Rybakov 1976. V.V. Rybakov. Hereditarily finitely axiomatizable extensions of 
the logic 54. Algebra and Logic, 15:115-128, 1976. 
Rybakov 1977. V.V. Rybakov. Noncompact extensions of the logic 54. Algebra 
and Logic, 16:321-334, 1977. 
Rybakov 1978a. V.V. Rybakov. A decidable noncompact extension of the logic 
54. Algebra and Logic, 17:148-154, 1978. 
Rybakov 1978b. V.V. Rybakov. Modal logics with LM-axioms. Algebra and 
Logic, 17:302-310, 1978. 
Rybakov 1981. V.V. Rybakov. Admissible rules in the pretabular modal logics. 
Algebra and Logic, 20:291-307, 1981. 
Rybakov 1984a. V.V. Rybakov. Admissible rules for logics containing 54.3. 
Siberian Mathematical Journal, 25:795-798, 1984. 
Rybakov 1984b. V.V. Rybakov. A criterion for admissibility of rules in the 
modal system 54 and intuitionistic logic. Algebra and Logic, 23:369-384, 1984. 
Rybakov 1984c. V.V. Rybakov. Decidability of admissibility problem in modal 
logics of finite slices. Algebra and Logic, 23:75-87, 1984. 
Rybakov 1985a. V.V. Rybakov. Bases of admissible rules of the logics 54 and 
Int. Algebra and Logic, 24:55-68, 1985. 
Rybakov 1985b. V.V. Rybakov. The elementary theories of free topological 
Boolean and pseudo-Boolean algebras. Mathematical Notes, 37:435-438, 1985. 
Rybakov 1986a. V.V. Rybakov. Equations in a free topological boolean algebra 
and the substitution problem. Soviet Mathematics Doklady, 33:428-431, 1986. 
Rybakov 1986b. V.V. Rybakov. Equations in the free topological Boolean 
algebra. Algebra and Logic, 25:109-127, 1986. 
Rybakov 1987a. V.V. Rybakov. Bases of admissible rules of the modal system 
Grz and of intuitionistic logic. Mathematics of the USSR, Sbomik, 56:311-331, 
1987. 
Rybakov 1987b. V.V. Rybakov. The decidability of admissibility of inference 
rules in the modal system Grz and intuitionistic logic. Mathematics of the 
USSR, Izvestiya, 28:589-608, 1987. 
Rybakov 1989. V.V. Rybakov. Admissibility of inference rules in the modal 
system G. Mathematical Logic and Algorithmical Problems, Mathematical 
Institute, Novosibirsk, 12:120-138, 1989. (Russian). 
Rybakov 1990a. V.V. Rybakov. Admissibility of inference rules and logical 
equations in modal logics axiomatizing provability. Mathematics of the USSR, 
Izvestiya, 54:357-377, 1990. 
Rybakov 1990b. V.V. Rybakov. Logical equations and admissible rules of 
inference with parameters in modal provability logics. Studia Logica, 49:215-239, 
1990. 
Rybakov 1990c. V.V. Rybakov. Problems of substitution and admissibility in 
the modal system Grz and intuitionistic calculus. Annals of Pure and Applied 
Logic, 50:71-106, 1990. 
Rybakov 1992. V.V. Rybakov. A modal analog for Glivenko’s theorem and its 
applications. Notre Dame Journal of Formal Logic, 33:244-148, 1992. 

588 
BIBLIOGRAPHY 
Rybakov 1993. V.V. Rybakov. Rules of inference with parameters for intuition- 
istic logic. Journal of Symbolic Logic, 58:1803-1834, 1993. 
Rybakov 1994. V.V. Rybakov. Criteria for admissibility of inference rules. 
Modal and intermediate logics with the branching property. Studia Logica, 
53:203-226, 1994. 
Rybakov 1995. V.V. Rybakov. Hereditarily structurally complete modal logics. 
Journal of Symbolic Logic, 60:266-288, 1995. 
Sahlqvist 1975. H. Sahlqvist. Completeness and correspondence in the first 
and second order semantics for modal logic. In S. Kanger, editor, Proceedings 
of the Third Scandinavian Logic Symposium, pages 110-143. North-Holland, 
Amsterdam, 1975. 
Sambin and Vaccaro 1988. G. Sambin and V. Vaccaro. Topology and duality 
in modal logic. Annals of Pure and Applied Logic, 37:249-296, 1988. 
Sambin and Vaccaro 1989. G. Sambin and V. Vaccaro. A topological proof of 
Sahlqvist’s theorem. Journal of Symbolic Logic, 54:992-999, 1989. 
Sambin and Valentini 1980. G. Sambin and S. Valentini. Post completeness 
and free algebras. Zeitschrift fur Mathematische Logik und Grundlagen der 
Mathematik, 26:343-347, 1980. 
Sasaki et al 1994. K. Sasaki, S. Shundo, and T. Hosoi. The simple substitution 
property for the normal modal logics. SUT Journal of Mathematics, 30:107- 
128, 1994. 
Sasaki 1989. K. Sasaki. The simple substitution property of the intermediate 
propositional logics. Bulletin of the Section of Logic, 18:94-99, 1989. 
Sasaki 1992. K. Sasaki. The disjunction property of the logics with axioms of 
only one variable. Bulletin of the Section of Logic, 21:40-46, 1992. 
Schumm 1981. G. Schumm. Bounded properties in modal logic. Zeitschrift fur 
Mathematische Logik und Grundlagen der Mathematik, 27:197-200, 1981. 
Schiitte 1962. K. Schiitte. Der Interpolationssatz der intuitionistischen 
Pradikatenlogik. Mathematische Annalen, 148:192-200, 1962. 
Schiitte 1968. K. Schiitte. Vollstandige Systeme modaler und intuitionistischer 
Logik. Springer Verlag, Berlin, Heidelberg &; New York, 1968. 
Scott 1970. D. Scott. Advice on modal logic. In K. Lambert, editor, 
Philosophical Problems in Logic. Some Recent Developments, pages 143-174. Reidel, 
Dordrecht, 1970. 
Scroggs 1951. S.J. Scroggs. Extensions of the Lewis system 55. Journal of 
Symbolic Logic, 16:112-120, 1951. 
Segerberg 1968. K. Segerberg. Decidability of 54.1. Theoria, 34:7-20, 1968. 
Segerberg 1970. K. Segerberg. Modal logics with linear alternative relations. 
Theoria, 36:301-322, 1970. 
Segerberg 1971. K. Segerberg. An essay in classical modal logic. Philosophical 
Studies, Uppsala, 13, 1971. 
Segerberg 1972. K. Segerberg. Post completeness in modal logic. Journal of 
Symbolic Logic, 37:711-715, 1972. 
Segerberg 1974. K. Segerberg. Proof of a conjecture of McKay. Fundamenta 
Mathematicae, 81:267-270, 1974. 

BIBLIOGRAPHY 
589 
Segerberg 1975. K. Segerberg. That all extensions of 54.3 are normal. In 
S. Kanger, editor, Proceedings of the Third Scandinavian Logic Symposium, 
pages 194-196. North-Holland, Amsterdam, 1975. 
Segerberg 1976. K. Segerberg. The truth about some Post numbers. Journal 
of Symbolic Logic, 41:239-244, 1976. 
Segerberg 1980. K. Segerberg. Applying modal logic. Studia Logic, 39:275-295, 
1980. 
Segerberg 1982. K. Segerberg. Classical Propositional Operators. Clarendon 
Press, Oxford, 1982. 
Segerberg 1986. K. Segerberg. Modal logics with functional alternative 
relations. Notre Dame Journal of Formal Logic, 27:504-522, 1986. 
Segerberg 1994. K. Segerberg. A model existence theorem in infinitary 
propositional modal logic. Journal of Philosophical Logic, 23:337-367, 1994. 
Sendlevski 1984. A. Sendlevski. Some investigations of varieties of N-lattices. 
Studia Logica, 43:257-280, 1984. 
Shavrukov 1991. V.Yu. Shavrukov. On two extensions of the provability logic 
GL. Mathematics of the USSR, Sbomik, 69:255-270, 1991. 
Shavrukov 1993. V.Yu. Shavrukov. Subalgebras of diagonalizable algebras 
of theories containing arithmetic. Dissertationes Mathematicae (Rozprawy 
Matematyczne, Polska Akademia Nauk, Instytut Matematyczny)y Warszawa, 
1993. 
Shehtman 1977. V.B. Shehtman. On incomplete propositional logics. Soviet 
Mathematics Doklady, 18:985-989, 1977. 
Shehtman 1978a. V.B. Shehtman. Rieger-Nishimura lattices. Soviet 
Mathematics Doklady, 19:1014-1018, 1978. 
Shehtman 1978b. V.B. Shehtman. An undecidable superintuitionistic 
propositional calculus. Soviet Mathematics Doklady, 19:656-660, 1978. 
Shehtman 1979. V.B. Shehtman. Kripke type semantics for propositional modal 
logics with the intuitionistic base. In V.A. Smirnov, editor, Modal and Tense 
Logics, pages 108-112. Institute of Philosophy, USSR Academy of Sciences, 
1979. (Russian). 
Shehtman 1980. V.B. Shehtman. Topological models of propositional logics. 
Semiotics and Information Science, 15:74-98, 1980. (Russian). 
Shehtman 1982. V.B. Shehtman. Undecidable propositional calculi. In 
Problems of Cybernetics. Nonclassical logics and their application, volume 75, pages 
74-116. USSR Academy of Sciences, 1982. (Russian). 
Shehtman 1983. V.B. Shehtman. On the countable approximability of 
superintuitionistic and modal logics. In A.I. Mikhailov, editor, Studies in Nonclassical 
Logics and Formal Systems, pages 287-299. Nauka, Moscow, 1983. (Russian). 
Shehtman 1990a. V.B. Shehtman. Derived sets in Euclidean spaces and modal 
logic. Preprint X-90-05, University of Amsterdam, 1990. 
Shehtman 1990b. V.B. Shehtman. Modal counterparts of Medvedev logic of 
finite problems are not finitely axiomatizable. Studia Logica, 49:365-385, 1990. 
Shimura 1993. T. Shimura. Kripke completeness of some intermediate predicate 
logics with the axiom of constant domain and a variant of canonical formulas. 

590 
BIBLIOGRAPHY 
Studia Logica, 52:23-40, 1993. 
Shimura 1995. T. Shimura. On completeness of intermediate predicate logics 
with respect to Kripke semantics. Bulletin of the Section of Logic, 24:41-45, 
1995. 
Shum 1985. A.A. Shum. Relative varieties of algebraic systems, and 
propositional calculi. Soviet Mathematics Doklady, 31:492-495, 1985. 
Skvortsov 1979. D.P. Skvortsov. On some propositional logics connected with 
the concept of Yu.T. Medvedev’s types of information. Semiotics and 
Information Science, 13:142-149, 1979. (Russian). 
Skvortsov 1983. D.P. Skvortsov. On the intuitionistic propositional calculus 
with an additional logical connective. In A.I. Mikhailov, editor, Studies in Non- 
classical Logics and Formal Systems, pages 154-173. Nauka, Moscow, 1983. 
(Russian). 
Smetanich 1960. Ya.S. Smetanich. On completeness of a propositional calculus 
with an additional unary operation. Proceedings of Moscow Mathematical 
Society, 9:357-371, 1960. (Russian). 
Smorynski 1973. C. Smorynski. Investigations of Intuitionistic Formal Systems 
by means of Kripke Frames. PhD thesis, University of Illinois, 1973. 
Smorynski 197& C. Smorynski. Beth’s theorem and self-referential sentences. 
In Logic Colloquium 77, pages 253-261. North-Holland, Amsterdam, 1978. 
Smorynski 1985. C. Smorynski. Self-reference and Modal Logic. Springer Ver- 
lag, Heidelberg h New York, 1985. 
Sobolev 1977a. S.K. Sobolev. On finite-dimensional superintuitionistic logics. 
Mathematics of the USSR, Izvestiya, 11:909-935, 1977. 
Sobolev 1977b. S.K. Sobolev. On the finite approximability of 
superintuitionistic logics. Mathematics of the USSR, Sbomik, 31:257-268, 1977. 
Solovay 1976. R. Solovay. Provability interpretations of modal logic. Israel 
Journal of Mathematics, 25:287-304, 1976. 
Sotirov 1984. V.H. Sotirov. Modal theories with intuitionistic logic. In 
Proceedings of the Conference on Mathematical Logic, Sofia, 1980, pages 139-171. 
Bulgarian Academy of Sciences, 1984. 
Spaan 1993. E. Spaan. Complexity of Modd Logics. PhD thesis, Department 
of Mathematics and Computer Science, University of Amsterdam, 1993. 
Statman 1979. R. Statman. Intuitionistic propositional logic is polynomial- 
space complete. Theoretical Computer Science, 9:67-72, 1979. 
Stone 1937. M.H. Stone. Application of the theory of Boolean rings to general 
topology. Transactions of the American Mathematical Society, 41:321-364, 
1937. 
Takeuti 1975. G. Takeuti. Proof Theory. North-Holland, Amsterdam, 1975. 
Tarski 1938. A. Tarski. Der Aussagenkalkiil und die Topologie. Fundamenta 
Mathematicae, 31:103-134, 1938. 
Tarski 1954. A. Tarski. Contributions to the theory of models I,II. Indagationes 
Mathematicae, 16:572-588, 1954. 
Taylor 1979. W. Taylor. Equational logic. Houston Journal of Mathematics, 
Survey, 5:1-83, 1979. 

BIBLIOGRAPHY 
591 
Thomason 1969. R.H. Thomason. A semantical study of constructive falsity. 
Zeitschrift fur Mathematische Logik und Grundlagen der Mathematik, 15:247- 
257, 1969. 
Thomason 1972a. S. K. Thomason. Noncompactness in propositional modal 
logic. Journal of Symbolic Logic, 37:716-720, 1972. 
Thomason 1972b. S. K. Thomason. Semantic analysis of tense logic. Journal 
of Symbolic Logic, 37:150-158, 1972. 
Thomason 1974a. S. K. Thomason. An incompleteness theorem in modal logic. 
Theoria, 40:30-34, 1974. 
Thomason 1974b. S. K. Thomason. Reduction of tense logic to modal logic I. 
Journal of Symbolic Logic, 39:549-551, 1974. 
Thomason 1975a. S. K. Thomason. The logical consequence relation of 
propositional tense logic. Zeitschrift fur mathematische Logik und Grundlagen der 
Mathematik, 21:29-40, 1975. 
Thomason 1975b. S. K. Thomason. Reduction of second-order logic to modal 
logic. Zeitschrift fur mathematische Logik und Grundlagen der Mathematik, 
21:107-114, 1975. 
Thomason 1975c. S. K. Thomason. Reduction of tense logic to modal logic II. 
Theoria, 41:154-169, 1975. 
Thomason 1980. S. K. Thomason. Independent propositional modal logics. Stu- 
dia Logica, 39:143-144, 1980. 
Thomason 1982. S. K. Thomason. Undecidability of the completeness 
problem of modal logic. In Universal Algebra and Applications, Banach Center 
Publications, volume 9, pages 341-345, Warsaw, 1982. PNW-Polish Scientific 
Publishers. 
Troelstra 1969. A. Troelstra. Principles of Intuitionism. Lecture Notes in 
Mathematics, 95, Springer-Verlag, Berlin, 1969. 
Tsytkin 1987. A.I. Tsytkin. Structurally complete superintuitionistic logics and 
primitive varieties of pseudo-Boolean algebras. Mathematical Studies, 98:134- 
151, 1987. (Russian). 
Ulrich 1982. D. Ulrich. Answer to a question raised by Harrop. Bulletin of the 
Section of Logic, 11:140-141, 1982. 
Ulrich 1983. D. Ulrich. The finite model property and recursive bounds of the 
size of counter models. Journal of Philosophical Logic, 12:477-480, 1983. 
Ulrich 1984. D. Ulrich. Answer to a question suggested by Schumm. Zeitschrift 
fur mathematische Logik und Grundlagen der Mathematik, 30:113-130, 1984. 
Umezawa 1955. T. Umezawa. Uber die Zwischensysteme der Aussagenlogik. 
Nagoya Mathematical Journal, 9:181-189, 1955. 
Umezawa 1959. T. Umezawa. On intermediate propositional logics. Journal of 
Symbolic Logic, 24:20-36, 1959. 
Urquhart 1974. A. Urquhart. Implicational formulas in intuitionistic logic. 
Journal of Symbolic Logic, 39:661-664, 1974. 
Urquhart 1981. A. Urquhart. Decidability and the finite model property. 
Journal of Philosophical Logic, 10:367-370, 1981. 
Vakarelov 1977. D. Vakarelov. Notes on N-lattices and constructive logic with 

592 
BIBLIOGRAPHY 
strong negation. Studia Logica, 36:109-125, 1977. 
van Benthem and Blok 1978. J.A.F.K. van Benthem and W. J. Blok. 
Transitivity follows from Dummett’s axiom. Theoria, 44:117-118, 1978. 
van Benthem and Humberstone 1983. J.A.F.K. van Benthem and I.L. Humber- 
stone. Hallden-completeness by gluing Kripke frames. Notre Dame Journal of 
Formal Logic, 24:426-430, 1983. 
van Benthem 1975. J.A.F.K. van Benthem. A note on modal formulas and 
relational properties. Journal of Symbolic Logic, 40:85-88, 1975. 
van Benthem 1976a. J.A.F.K. van Benthem. Modal formulas are either 
elementary or not EA-elementary. Journal of Symbolic Logic, 41:436-438, 1976. 
van Benthem 1976b. J.A.F.K. van Benthem. Modal reduction principles. 
Journal of Symbolic Logic, 41:301-312, 1976. 
van Benthem 1978. J.A.F.K. van Benthem. Two simple incomplete modal 
logics. Theoria, 44:25-37, 1978. 
van Benthem 1979a. J.A.F.K. van Benthem. Syntactic aspects of modal 
incompleteness theorems. Theoria, 45:63-77, 1979. 
van Benthem 1979b. J.F.A.K. van Benthem. Canonical modal logics and 
ultrafilter extensions. Journal of Symbolic Logic, 44:1-8, 1979. 
van Benthem 1980. J.A.F.K. van Benthem. Some kinds of modal completeness. 
Studia Logica, 39:125-141, 1980. 
van Benthem 1983. J.A.F.K. van Benthem. Modal Logic and Classical Logic. 
Bibliopolis, Napoli, 1983. 
van Benthem 1984. J.A.F.K. van Benthem. Correspondence theory. In D.M. 
Gabbay and F. Guenthner, editors, Handbook of Philosophical Logic, volume 2, 
pages 167-247. Reidel, Dordrecht, 1984. 
van Benthem 1989. J.A.F.K. van Benthem. Notes on modal definability. Notre 
Dame Journal of Formal Logic, 39:20-39, 1989. 
van Dalen 1986. D. van Dalen. Intuitionistic Logic. In D.M. Gabbay and 
F. Guenthner, editors, Handbook of Philosophical Logic, volume 3, pages 225- 
339. Reidel, Dordrecht, 1986. 
Varpakhovskij 1965. F.L. Varpakhovskij. The nonrealizability of a disjunction 
of nonrealizable formulas of propositional logic. Soviet Mathematics Doklady, 
6:568-570, 1965. 
Varpakhovskij 1973. F.L. Varpakhovskij. A class of realizable propositional 
formulae. Journal of Soviet Mathematics, 1:1-11, 1973. 
Venema 1991. Y. Venema. Many-Dimensional Modal Logics. PhD thesis, Uni- 
versiteit van Amsterdam, 1991. 
Venema 1993. Y. Venema. Derivation rules as anti-axioms in modal logic. 
Journal of Symbolic Logic, 58:1003-1034, 1993. 
Visser 1984. A. Visser. The provability logics of recursively enumerable 
theories extending Peano arithmetic and arbitrary theories extending Peano 
arithmetic. Journal of Philosophical Logic, 13:97-113, 1984. 
Vorob’ev 1952a. N.N. Vorob’ev. A constructive propositional calculus with 
strong negation. Doklady Akademii Nauk SSSR, 85:465-468, 1952. (Russian). 
Vorob’ev 1952b. N.N. Vorob’ev. The problem of deducibility in the constructive 

BIBLIOGRAPHY 
593 
propositional calculus with strong negation. Doklady Akademii Nauk SSSR, 
85:689-692, 1952. (Russian). 
Vorob’ev 1972. N.N. Vorob’ev. A constructive calculus of statements with 
strong negation. American Mathematical Society. Translations. Series 2, 
99:40-82, 1972. 
Wajsberg 1938. M. Wajsberg. Untersuchungen fiber den Aussagenkalkfil von 
A. Heyting. Wiadomosci Matematyczne, 46:45-101, 1938. 
Wang 1992. X. Wang. The McKinsey axiom is not compact. Journal of 
Symbolic Logic, 57:1230-1238, 1992. 
Wansing 1996. H. Wansing. Proof Theory of Modal Logic. Kluwer Academic 
Publishers, 1996. 
Whitman 1943. P. Whitman. Splittings of a lattice. American Journal of 
Mathematics, 65:179-196, 1943. 
Wojtylak 1983. P. Wojtylak. Collapse of a class of infinite disjunctions in intu- 
itionistic propositional logic. Reports on Mathematical Logic, 16:37-49, 1983. 
Wolter and Zakharyaschev 1996. F. Wolter and M. Zakharyaschev. On the 
relation between intuitionistic and classical modal logics. Algebra and Logic, 
1996. To appear. 
Wolter and Zakharyaschev 1997. F. Wolter and M. Zakharyaschev. 
Intuitionistic modal logics as fragments of classical bimodal logics. In E. Orlowska, 
editor, Logic at Work. Kluwer Academic Publishers, 1997. In print. 
Wolter 1993. F. Wolter. Lattices of Modal Logics. PhD thesis, Freie Universitat 
Berlin, 1993. Parts of this paper will appear in Annals of Pure and Applied 
Logic under the title “The structure of lattices of subframe logics”. 
Wolter 1994. F. Wolter. Solution to a problem of Goranko and Passy. Journal 
of Logic and Computation, 4:21-22, 1994. 
Wolter 1995. F. Wolter. The finite model property in tense logic. Journal of 
Symbolic Logic, 60:757-774, 1995. 
Wolter 1996a. F. Wolter. Completeness and decidability of tense logics closely 
related to logics containing K4. Journal of Symbolic Logic, 1996. To appear. 
Wolter 1996b. F. Wolter. Properties of tense logics. Mathematical Logic 
Quarterly, 1996. To appear. 
Wolter 1996c. F. Wolter. Tense logics without tense operators. Mathematical 
Logic Quarterly, 42:145-171, 1996. 
Wolter 1997. F. Wolter. A note on atoms in polymodal algebras. Algebra 
Universalis, 1997. To appear. 
Wronski 1973. A. Wronski. Intermediate logics and the disjunction property. 
Reports on Mathematical Logic, 1:39-51, 1973. 
Wronski 1974. A. Wronski. Remarks on intermediate logics with axioms 
containing only one variable. Reports on Mathematical Logic, 2:63-75, 1974. 
Wronski 1976. A. Wronski. Remarks on Hallden completeness of modal and 
intermediate logics. Bulletin of the Section of Logic, 5:126-129, 1976. 
Yashin 1985. A.D. Yashin. Semantic characterization of intuitionistic logical 
connectives. Mathematical Notes, 38:157-167, 1985. (Russian). 

594 
BIBLIOGRAPHY 
Yashin 1986. A.D. Yashin. Semantic characterization of modal logical 
connectives. Mathematical Notes, 40:519-526, 1986. (Russian). 
Yashin 1989. A.D. Yashin. Semantic characterization of some sets of intuition- 
istic logical connectives. Mathematical Notes, 45:103-113, 1989. (Russian). 
Yashin 1994. A.D. Yashin. The Smetanich logic T^ and two definitions of a new 
intuitionistic connective. Mathematical Notes, 56:135-142, 1994. (Russian). 
Zakharyaschev and Alekseev 1995. M. Zakharyaschev and A. Alekseev. All 
finitely axiomatizable normal extensions of K4.3 are decidable. 
Mathematical Logic Quarterly, 41:15-23, 1995. 
Zakharyaschev and Popov 1979. M.V. Zakharyaschev and S.V. Popov. On the 
complexity of Kripke countermodels in intuitionistic propositional calculus. In 
Proceedings of the 2nd Soviet-Finland Logic Colloquium, pages 32-36, 1979. 
(Russian). 
Zakharyaschev and Popov 1980. M.V. Zakharyaschev and S.V. Popov. On the 
cardinality of countermodels of intuitionistic calculus. Technical Report 85, 
Institute of Applied Mathematics, Russian Academy of Sciences, 1980. 
(Russian). 
Zakharyaschev 1981. M.V. Zakharyaschev. Certain classes of intermediate 
logics. Technical Report 160, Institute of Applied Mathematics, Russian Academy 
of Sciences, 1981. (Russian). 
Zakharyaschev 1983. M.V. Zakharyaschev. On intermediate logics. Soviet 
Mathematics Doklady, 27:274-277, 1983. 
Zakharyaschev 1984a. M.V. Zakharyaschev. Normal modal logics containing 
54. Soviet Mathematics Doklady, 28:252-255, 1984. 
Zakharyaschev 1984b. M.V. Zakharyaschev. Syntax and semantics of superin- 
tuitionistic and modal logics. PhD thesis, Institute of Applied Mathematics, 
Moscow, 1984. (Russian). 
Zakharyaschev 1987. M.V. Zakharyaschev. On the disjunction property of su- 
perintuitionistic and modal logics. Mathematical Notes, 42:901-905, 1987. 
Zakharyaschev 1988. M.V. Zakharyaschev. Syntax and semantics of modal 
logics containing 54. Algebra and Logic, 27:408-428, 1988. 
Zakharyaschev 1989. M.V. Zakharyaschev. Syntax and semantics of 
intermediate logics. Algebra and Logic, 28:262-282, 1989. 
Zakharyaschev 1991. M.V. Zakharyaschev. Modal companions of superintu- 
itionistic logics: syntax, semantics and preservation theorems. Matematics of 
the USSR, Sbomik, 68:277-289, 1991. 
Zakharyaschev 1992. M.V. Zakharyaschev. Canonical formulas for KA. Part I: 
Basic results. Journal of Symbolic Logic, 57:1377-1402, 1992. 
Zakharyaschev 1993. M.V. Zakharyaschev. A sufficient condition for the finite 
model property of modal logics above K4. Bulletin of the IGPL, 1:13-21, 
1993. 
Zakharyaschev 1994. M.V. Zakharyaschev. A new solution to a problem of 
Hosoi and Ono. Notre Dame Journal of Formal Logic, 35:450-457, 1994. 
Zakharyaschev 1996a. M.V. Zakharyaschev. Canonical formulas for K4. Part 
II: Cofinal subframe logics. Journal of Symbolic Logic, 61:421-449, 1996. 

BIBLIOGRAPHY 
595 
Zakharyaschev 1996b. M.V. Zakharyaschev. Canonical formulas for modal and 
superintuitionistic logics: a short outline. In M. de Rijke, editor, Advances in 
Intensional Logic, pages 191-243. Kluwer Academic Publishers, 1996. 
Zakharyaschev 1996c. M.V. Zakharyaschev. The greatest extension of S4 into 
which intuitionistic logic is embeddable. Manuscript, 1996. 
Zakharyaschev 1997. M.V. Zakharyaschev. Canonical formulas for K4. Part 
III: the finite model property. Journal of Symbolic Logic, 62, 1997. To appear. 
Zeman 1973. J.J. Zeman. Modal Logic. The Lewis-Modal Systems. Clarendon 
Press, Oxford, 1973. 

INDEX 
X-approximability, 120 
A*, 116 
actual world, 154, 240 
actual world condition, 319 
admissible rule, 16 
algebra, 193 
Boolean, 206 
closure, 247 
degenerate, 194 
diagonalizable, 214 
for a logic, 198, 214 
free of rank X, 222 
Grzegorczyk, 214 
Heyting, 198 
interior, 247 
Magarian, 214 
modal, 214 
of formulas, 195 
of open elements, 247 
pseudo-Boolean, 198 
complete, 202 
quotient, 224 
recursive, 498 
subdirectly irreducible, 231 
Tarski-Lindenbaum, 197 
topological Boolean, 214, 247 
transitive, 214 
well-connected, 455 
Altn, 116 
altn, 82 
alternative world, 63 
alternativeness relation, 63 
amalgamability, 451 
antichain, 43 
n-stable, 406 
stable, 406 
antisymmetry, 25 
antitabularity, 431, 441 
arithmetic interpretation, 94 
atom, 212 
in a frame, 249 
AWC, 319 
axiom, 9 
additional, 110, 113 
extra, 110, 113 
axiom scheme, 12 
axiomatic basis, 118 
axiomatization, 115 
finite, 110, 113 
independent, 16 
recursive, 117 
recursively enumerable, 117 
Bn, 112 
balloon, 103 
reflexive, 104 
66b, 44 
6Cn, 43 
BDn, 112 
tan, 42> 81 
bidual, 243, 245 
bisimulation, 54 
Boolean function, 19 
branching, 44 
inner, 423 
outer, 423 
BTWn, 112 
btUin, 55 
bulldozing, 72 
BWn, 112 
bu)n, 43, 80 
calculus, 115 
canonical formula, 310 
intuitionistic, 310 
negation free, 310 
normal modal, 310 
negation free, 310 
quasi-normal, 320 
negation free, 320 
CDC, 298 
chain, 32 
ascending, 32 
descending, 32 
chain logic, 119 
characteristic formula, 329 
Church’s thesis, 491 
Church-Minsky thesis, 493 
Cl, 6, 112 
class of frames 
closed under subframes, 383 
intuitionistically definable, 121 
modally definable, 121 
Cl, 9 
classical calculus, 9 

598 
INDEX 
classical logic, 6 
classical model, 5 
closed domain, 302 
closed domain condition, 298 
closure operation, 247 
cluster, 68 
degenerate, 68 
final, 70 
last, 70 
proper, 68 
simple, 68 
codepth, 166 
cofinal set, 295 
cofinal subframe formula, 313 
cofinal subframe logic, 380 
quasi-normal, 391 
completeness, 14, 45, 91 
functional, 58 
structural, 16 
truth-functional, 20, 58 
complexity function, 547 
can, 80 
conclusion, 4 
configuration, 493 
configuration problem, 493 
congruence, 224, 262 
congruence rule, 17, 89 
conjunct, 4 
conjunction, 1, 3 
connectedness, 80 
strong, 40 
conservative formula, 449, 468 
consistency, 16 
countermodel, 5, 26 
cover, 70 
CST, 380 
cut, 409 
cyclic set, 269 
d-, 269 
degenerate, 269 
non-degenerate, 269 
deductively equal formulas, 115 
degree of Kripke incompleteness, 364 
derin, 80 
density, 79 
n-, 79 
deontic necessity, 62 
depth of a frame, 43, 81 
depth of a point, 267 
derivable rule, 16, 88 
derivation, 11, 84, 110 
from assumptions, 12, 84, 110 
length of, 11 
substitutionless, 12 
deterministic machine, 557 
diagram of a frame, 27, 66 
diameter, 563 
dir, 80 
direct product, 220, 249 
directedness, 80 
downward, 350 
strong, 42 
disjoint union, 34, 265, 267 
disjunct, 4 
disjunction, 1, 3 
repeatless, 111 
weak, 59 
disjunction property, 19, 471 
modal, 90, 471 
weak, 543 
distinguished element, 194 
distinguished point, 240 
distinguished world, 99 
downward closed set, 26 
dual of a frame, 205, 214, 236, 240 
dual of a matrix, 216, 245 
dual of an algebra, 211, 216, 243, 244 
Dum, 116 
dam, 104 
Dum.3, 157 
Dummett formula, 36 
Dummett logic, 119 
D, 93 
^-persistence, 354 
D, 93, 116 
D4, 94 
D4Gi, 116 
D5, 94 
da, 36 
dead end, 65 
decidability, 6 
of a property, 536 
decidable set, 492 
elementarily 
C-, 340 
elementary 
class of frames, 166 
logic, 166 
embedding, 46, 194 
quasi-, 389 
epistemic necessity, 62 
equivalence, 4 
polynomial, 548 
equivalence relation, 93 

INDEX 
599 
equivalent 
calculi, 115 
formulas, 19 
modalities, 90 
euc, 80 
Euclidean, 80 
exponential approximability, 119 
hereditary, 553 
expressibility, 58 
expression, 58 
ExtL, 112, 113 
extension of a logic, 15, 112 
normal, 113 
extension of a matrix, 227 
Extint, 112 
falsehood, 3 
filter, 207 
critical, 230 
generated, 208 
maximal, 211 
normal, 223 
prime, 210 
principal, 208 
proper, 207 
filtration, 140 
coarsest, 141 
finest, 141 
Lemmon, 142 
selective, 149 
final state, 493 
finite approximability, 49, 119 
global, 121 
strict, 361 
finite base over a model, 142 
finite cofinal quasi-embedding property, 389 
finite cover property, 354 
finite depth logic, 272 
finite embedding property, 385 
finite frame property, 49, 119 
finite model property, 119 
first order frame, 282 
focus, 406 
For, 112, 116 
For/:, 4 
ForMC, 61 
formula, 1, 3 
□ O-, 379 
antimonotone, 20 
atomic, 3 
classically established, 59 
conservative, 449, 468 
derivable, 11 
derivable from assumptions, 12 
disjunction free, 293 
dual, 20 
essentially negative, 378 
false at a point, 65 
false in a model, 5 
intuitionistically established, 59 
monotone, 20 
negation free, 293 
negative, 103, 352 
positive, 103, 350 
prime, 118 
realizable, 53 
Sahlqvist, 353 
satisfied in a frame, 26 
satisfied in a model, 26 
strongly positive, 348 
true at a point, 26, 64 
true in a model, 5, 26 
undecidable, 508 
uniform, 374 
untied, 352 
variable free, 4 
frame, 238 
X-generated, 260 
atomic, 249 
canonical, 133 
with distinguished points, 155 
compact, 251 
cycle free, 362 
descriptive, 250, 258 
differentiated, 251 
finitely generated, 260 
for a set of formulas, 91 
intransitive, 65 
irreflexive, 65 
quotient, 263 
recession, 184 
recursive, 498 
reduced, 357 
refined, 251 
reflexive, 65 
rooted, 28 
simple, 474 
tight, 251 
top-heavy, 268 
universal of rank x, 260 
frame formula, 312 
negation free, 312 
Godel number, 94 
Godel translation, 96 
Godel’s second theorem, 1 

INDEX 
600 
90, 80 
Gabbay rule, 102 
SOfcJmn. 79 
Geach formula, 80 
general frame 
associated with a model, 237 
intuitionistic, 236 
modal, 236 
with distinguished points, 240 
generator, 260 
GL, 95 
GL, 94, 116 
GL.3, 157 
Goldbach’s conjecture, 1 
greatest lower bound, 202 
Grz, 93 
Grz, 93, 116 
grz, 74 
Grz.3, 157 
Grzegorczyk formula, 74 
Grzegorczyk logic, 93 
Hallden completeness, 19, 471 
halting problem, 494 
Harrop formula, 56 
Henkin construction, 131 
bin, 103 
Hintikka formula, 103 
Hintikka system, 37, 75 
for a tableau, 37, 76 
homomorphic image, 221 
inverse , 221 
homomorphism, 194 
ideal, 208 
generated, 209 
prime, 210 
identity, 194 
true in an algebra, 194 
implication, 1, 3 
independent axioms, 16 
independent connective, 56 
inference rule, 9 
reduced, 520 
infimum, 202 
initial state, 493 
injection, 194 
interior operation, 247 
interpolant, 17, 446 
interpolation property, 17, 446 
for derivability, 455 
Lyndon, 469 
uniform, 470 
weak, 469 
Int, 45 
Int, 28 
intuitionistic calculus, 45 
intuitionistic logic, 28 
invariant property, 494 
isomorphic 
algebras, 194 
frames, 26, 236 
matrices, 194 
models, 27 
isomorphism, 26, 194 
O-, 291 
dual, 217 
Jaskowski’s frame, 56 
Jankov formula, 332 
Jankov-Fine formula, 332 
K, 83 
K n, 100 
K, 69 
K4, 92 
K4 n,m» 116 
K4, 92, 116 
K4.1, 116 
K4.2, 116 
K4.3, 116 
K4Altn, 116 
K4B, 116 
K4BDn, 116 
K4BWn, 116 
K4H, 116 
K4Z, 116 
K5, 116 
KB, 116 
KC, 112 
kernel, 154 
KP, 112 
fep, 55 
Kreisel-Putnam formula, 55 
Kripke completeness, 120 
global, 121 
strong, 121 
strict, 361 
strong, 120 
Kripke frame, 238 
intuitionistic, 25 
modal, 64 
with distinguished points, 154 
Kripke inconsistency, 156 
Kripke model 
intuitionistic, 25 

INDEX 
601 
modal, 64 
with distinguished points, 154 
C, 3 
C-formula, 3 
Lob formula, 67 
la, 67 
lattice, 201 
complete, 202 
distributive, 204 
of filters, 209 
of normal modal logics, 113 
of quasi-normal modal logics, 113 
of si-logics, 112 
Rieger-Nishimura, 223 
Law 
of the excluded middle 
weak, 42 
de Morgan’s, 10 
Duns Scotus’, 10 
Frege’s, 10 
of absorption, 10 
of adjunction, 10 
of associativity, 10 
of commutativity, 10 
of contraposition, 10 
of distributivity, 10 
of double negation, 10 
of exportation, 10 
of idempotency, 10 
of importation, 10 
of simplification, 10 
of syllologism, 10 
of the excluded middle, 5, 10 
Pierce’s, 6 
LC, 112 
least upper bound, 202 
Lemma 
Blok’s, 232 
Esakia’s, 350 
intersection, 350 
Jonsson’s, 232 
Konig’s, 54 
Lindenbaum’s, 131 
reflexivization, 98 
skeleton, 96, 246 
Zorn’s, 213 
length of a formula, 119 
limit, 264 
linear approximability, 119 
hereditary, 553 
linear order, 32 
local finiteness, 19 
local tabularity, 19, 426 
LogC, 110, 114 
Log#, 110, 114 
logic, 1, 2, 15, 87 
X-complex, 338 
n-atomic, 284 
canonical, 135 
characterized by frames, 91, 118, 237 
strongly, 120 
characterized by matrices, 194 
cofinal subframe, 380 
compact, 168 
locally, 185 
elementary, 166, 354 
equational, 233 
intermediate, 109 
modal, 61 
of a class of frames, 110, 114 
of depth n, 272 
of width n, 354 
poly modal, 100 
pretabular, 421 
prime, 118 
subframe, 380 
superintuitionistic, 109 
uniform, 375 
universal, 385 
logical connective, 1 
logical necessity, 62 
ma, 68 
main connective, 4 
Maksimova completeness, 487 
matrix, 20, 194 
characteristic, 194 
degenerate, 194 
maximal, 439 
modal, 216 
quotient, 226 
reduced, 226 
Tarski-Lindenbaum, 197 
McKinsey condition, 82 
McKinsey formula, 68 
md(ip), 65 
Medvedev’s logic, 53 
Minsky machine, 491, 493 
MC, 61 
MC-formula, 61 
ML, 53 
modal companion, 322 
modal degree, 65 
modal logic 
inconsistent, 113 

602 
INDEX 
normal, 113 
quasi-normal, 113 
finitely axiomatizable, 113 
modal reduction principle, 89 
modality, 89 
affirmative, 89 
irreducible, 90 
negative, 89 
model 
canonical, 133 
with distinguished points, 155 
classical, 5 
compact, 134 
differentiated, 133 
for a formula, 5 
of C, 236 
of ML, 236 
quotient, 263 
refined, 134 
tight, 134 
universal, 20, 272 
with distinguished points, 240 
modus ponens, 11 
MP, 11 
monotonicity, 350 
NDjt, 112 
necessity operator, 1, 62 
negation, 4 
negative occurrence, 104 
neighborhood, 101 
neighborhood frame, 101 
normal, 101 
NExtL, 113 
nfn, 223 
Nishimura formulas, 223 
NLn, 112 
Noetherian frame, 83 
non-trivial property, 494 
nonderivability problem, 558 
nondescending sequence, 355 
nondeterministic machine, 557 
normal form, 375 
L-suitable, 377 
D-suitable, 377 
conjunctive, 19 
full, 20 
disjunctive, 19 
full, 20 
of degree n, 375 
normal world, 99 
7VP-completeness, 558 
TVP-hardness, 558 
omniscience paradox, 100 
open domain, 302 
open element, 247 
operation, n-ary, 193 
opremum, 230 
p-morphism, 30 
partial, 287 
partial order, 25 
strict, 72 
Peano arithmetic PA, 94 
persistence 
C, 337 
V-, 354 
point, 25, 64 
E-remaindered, 306 
n-stable, 406 
accessible, 25, 64 
by n steps, 65 
deep, 355 
distinguished, 154 
eliminable, 356 
final, 29, 70 
irreflexive, 65 
last, 29, 70 
least, 28 
maximal, 29 
of minimal range, 153 
of type n, 425 
redundant, 404 
reflexive, 65 
stable, 406 
static, 355 
stationary, 355 
polynomial approximability, 119 
hereditary, 553 
polynomial equivalence, 548 
polynomial reducibility, 547 
positive occurrence, 104 
possibility operator, 62 
possible world, 63 
possible world semantics, 63 
Post completeness, 16, 436 
general, 436 
predecessor, 29, 64 
immediate, 29, 64 
proper, 29, 64 
premise, 4 
pretabular logic, 421 
prime element, 210 
primitive symbols, 3 
principle of duality, 20, 103 
proof interpretation, 23 

INDEX 
603 
proposition, 1 
atomic, 1 
compound, 1 
propositional 
connective, 3 
constant, 1, 3 
language, 3 
logic, 1 
modal language, 61 
variable, 1, 3 
J?SJ?i4iCE-completeness, 559 
PS PACE- hard ness, 560 
QCST, 391 
QST, 391 
quantified Boolean formula, 560 
quasi-identity, 194 
true in an algebra, 194 
quasi-order, 68 
quasi-tree, 71 
re, 78 
realizability logic, 53 
recursive function, 492 
partial, 492 
total, 492 
recursive set, 492 
recursively enumerable class of algebras, 
498 
recursively enumerable set, 492 
reducibility, 432 
m-, 432 
0-, 16 
reduct, 30 
reduction, 30, 31, 261, 262, 265 
refinement, 254 
reflexive and transitive closure, 71 
reflexive closure, 98 
reflexivity, 25 
reflexivization, 98 
refutability criterion, 311 
refutation, 5, 26 
regularity rule, 89 
relativization, 329 
RN, 84 
root, 28, 70 
rule of necessitation, 84 
S, 95 
52, 99 
53, 99 
54, 92 
S4, 92, 116 
S4.1, 116 
54.2, 116 
54.3, 94 
54.3, 94, 116 
55, 93 
55, 93, 116 
56, 99 
SO, 40 
Sahlqvist formula, 353 
satisfiability problem, 558 
saturation rule, 9, 39, 77 
sc, 73 
Scott formula, 40 
Scott rule, 50 
second configuration problem, 493 
second greatest element, 230 
semantic tableau method, 6 
separability, 58 
separable, 464 
ser, 79 
seriality, 79 
set of formulas 
complete, 118 
independent, 118 
set of possible values, 235, 236 
ST, 380 
si-logic, 109 
finitely axiomatizable, 110 
inconsistent, 109 
E-equivalent points, 140, 268 
similar algebras, 193 
simple substitution property, 411 
skeleton, 68, 246 
of a model, 96, 246 
Skvortsov formula, 56 
SL, 112 
am, 55 
SmL, 112 
soundness, 14, 45, 91 
span, d-, 269 
splitting, 360 
formula, 332 
pair, 360 
union-, 360 
Stone 
isomorphism, 242 
lattice, 242 
space, 242 
strict implication, 105 
structural completeness, 17 
Sub(/?-equivalent tableaux, 140 
subalgebra, 219 
O-, 291 
x-generated, 219 

604 
INDEX 
generated, 219 
subformula, 4 
Subcp, 4 
subframe, 28, 65, 287, 289 
cofinal, 295, 395 
generated, 28, 259, 261 
induced, 287 
induced by a set, 66 
subframe formula, 313 
subframe logic, 380 
quasi-normal, 391 
sublogic, 15, 112 
submatrix, 220 
submodel, 29, 65 
generated, 29, 259 
induced, 306 
induced by a set, 66 
Kripke, induced, 306 
subreduct, 287. 
cofinal, 295 
subreduction, 287, 289 
E, 305 
cofinal, 295 
dense, 293 
injective, 500 
quasi-, 319 
substitution, 11 
Subst, 11 
subtableau, 8 
successor, 29, 64 
immediate, 29, 64 
proper, 29, 64 
sum of logics, 110 
superamalgamability, 454 
superintuitionistic fragment, 322 
supremum, 202 
surjection, 194 
syrrii 78 
symmetry, 78 
T, 91 
Tn, 112 
T, 91, 116 
tabn, 417 
tableau, 8, 37, 75 
L-consistent, 131 
p-prime, 146 
complete, 18, 446 
consistent, 14, 46, 86 
disjoint, 8, 37, 75 
extension of, 8 
inseparable, 446 
maximal, 86, 131 
realizable, 8, 37, 76 
saturated, 8, 37, 75 
separable, 18 
tabularity, 49, 119, 417 
local, 19, 426 
pre-local, 427 
tense logic, 100 
tense necessity, 62 
term, 194 
R-, 348 
t-extension, 501 
Theorem 
Birkhoff’s, 227 
Blok’s, 366 
Blok-Esakia, 325 
bulldozer, 72 
canonical model, 133 
compactness, 15, 46, 86 
completeness for Extint, 313 
completeness for NExtK4, 313 
Craig interpolation, 18 
Craig’s, 496 
deduction, 13, 45, 85 
Diego’s, 146 
disjoint union, 34 
equivalent replacement, 17, 89 
filtration, 141 
Fine’s, 358 
Fine-van Benthem, 344 
generation, 29, 70 
Glivenko’s, 47 
Harrop’s, 497 
Jonsson-Tarski representation, 245 
Kuznetsov’s, 535 
Los’, 231, 232 
Makinson’s, 262 
McKay’s, 202 
, modal companion, 323 
preservation, 328 
reduction, 31, 71 
Rice-Uspensky, 494 
Sahlqvist’s, 352 
Scroggs’, 155 
Segerberg’s, 272 
soundness and completeness 
of Cl, 14 
ofInt, 45 
of K, 86 
Stone’s representation, 242, 243 
strong completeness 
of Cl, 15 
of Int, 46 
of K, 86 

INDEX 
605 
Tarski’s, 227 
Weak Kreisel-Putnam formula, 297 
Tarski’s criterion, 116 
theory, 118 
topological space, 247 
tra, 78 
tran, 79 
transitivity, 25 
n-, 79 
translation, 46 
tuera, 42 
width, 43 
wkp, 297 
WKP, 112 
world, 64 
Z, 103 
zero element, 209 
standard, 122 
tree, 32, 71 
n-ary, 33 
full, 33 
of clusters, 71 
Triv, 116 
truth, 4 
truth problem for QBF, 560 
truth-relation, 26, 64 
truth-table, 4, 5 
type, 501 
ultrafilter, 211 
ultrafilter extension, 341 
ultraproduct, 231, 232 
uniform formula, 374 
of degree n, 374 
uniform logic, 375 
union-splitting, 360 
unit element, 208 
universal frame, 237 
with distinguished points, 240 
universal relation, 63, 93 
universe, 193 
unravelling, 72 
UpW, 25 
upper bound, 50 
upward closed set, 25 
upward closure, 28 
validity 
classical, 5 
in a frame, 26 
valuation, 20, 25, 64, 194, 236 
standard, 196 
value of a formula, 194 
Varc/?, 4 
VarC, 3 
variety 
characteristic, 217 
generated, 218 
of algebras, 216 
of modal matrices, 218 
Verum, 116 

