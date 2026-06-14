<!-- Source: Chagrov & Zakharyaschev (1997). Modal Logic (Oxford Logic Guides 35). Part III: Adequate Semantics — algebraic and relational semantics, canonical formulas (Ch 7-9). BibKey: ChagrovZakharyaschev1997 -->

Adequate semantics 
As we saw in the previous chapter, not all modal and superintuitionistic logics 
may be characterized by Kripke frames. There is nothing extraordinary in this 
unpleasant fact. After all the Kripke semantics was constructed initially just for 
several particular systems and only after that were we trying it on arbitrary 
modal and si-logics. 
In this part we introduce an adequate semantics for the logics under 
consideration. First, in Chapter 7 we translate the language of logic into the language of 
algebra and arrive at the algebraic semantics—modal and pseudo-Boolean 
algebras. Although this semantics gives no sensible interpretation for logical 
connectives, it enables us to take advantage of the developed apparatus of universal 
algebra. Then in Chapter 8, basing on Stone’s representation of distributive lattices, 
we obtain a relational representation of modal and pseudo-Boolean algebras— 
the so called general frames—which combine in themselves the merits of both 
algebras and Kripke frames. 

7 
ALGEBRAIC SEMANTICS 
Algebraic semantics abstracts from the intended meaning of logical connectives 
and interprets them just as operations on an arbitrary set A of objects, some 
of which are regarded as distinguished. Each formula <p(pi,... ,pn) gives rise 
to a function f^{x i,...,xn) on A, and we may consider <p(pi, • • • ,Pn) to be 
valid in this “interpretation” if /^(ai,..., an) is a distinguished object, for every 
a\,..., an £ A. It is not hard to see that all our logics are complete with respect to 
this highly abstract semantics. But to use it profitably, we should know something 
about the constitution of algebras corresponding to modal and superintuitionistic 
logics. 
7.1 	Algebraic preliminaries 
The aim of this section is to introduce the basic algebraic notions and notations 
to be used in what follows. 
Let A be a non-empty set. For n > 1, by an n-ary operation on A we mean 
any map o from An into A; a 0-ary operation on A is an element in A. For 
example, the truth-table in Section 1.1 defines A, V, —> and <-* as 2-ary or binary 
operations on the set {F,T}, ^ as a 1-ary or unary operation, and _L may be 
regarded as a 0-ary operation on {F,T}, namely F. 
A universal algebra or simply an algebra is a set A, called the universe of the 
algebra, together with some operations oi,..., on on it. We denote the algebra by 
21 = (A,Oi,..., on). For instance, the truth-table for Cl determines an algebra 
of the form 21 = ({T,F}, A, V, —<-*, _L). 
Two algebras 21 = (A, oi,..., on) and © = (B, ..., o'm) are said to be 
similar if n = m and, for every i £ {1,..., n}, the operations Oi and o' are of the 
same arity. As a rule, corresponding operations in similar algebras are denoted 
by the same symbols, though sometimes different ones may be preferable. 
Mostly we shall consider algebras with operations denoted by A, V, —> 
(binary) , _L (0-ary) and □ (unary). It will always be clear from the context whether 
we deal with algebraic operations or logical connectives. Although on the other 
hand the set ForMC of modal formulas with the formula formation rules may 
be regarded as an algebra (YoyMC, A, V, —_L, □). 
Algebras of the types 21 = (A, A, V, —_L) and 21 = (A, A, V, —_L, □) are 
called C- and MC-algebras, respectively. Each formula <p(pi,... ,pn) in the 
language C (or MC) gives rise to an n-ary operation in an C- (MC-) algebra 21 
if we interpret (p’s connectives as the corresponding operations in 21 and the 
propositional variables pi,... ,pn as variables over A. A formula <p considered 
as the definition of such an operation in C- (MC-) algebras is called a term 

194 
ALGEBRAIC SEMANTICS 
or an C- (MC-) term, to be more exact. For ai,...,an £ A, we denote by 
<p(ai,..., an) the result of applying the operation associated with ip in 21 to the 
arguments ai,..., an. Given a map 23 from Var£ in A, called a valuation in 21, 
23(<p) = y>(2J(pi),..., 23(pn)) is the value of (p in 21 under 23. 
An expression of the form <p = tp, and ip terms, is called an identity. It is 
true in an algebra 21 if the operations in 21 determined by ip and ip are the same, 
i.e., 23(ip) = 23 (VO for any valuation 23 in 21. An expression of the form 
<Pl = Vh A . . . A ipn = tpn <^0 = V'O, 
in which all <pi and ipi are terms, is called a quasi-identity. It is true in 21 if 
for every valuation 23 in 21, 23(<^o) = 23(V>o) whenever 23(<^i) = 23(^) for all 
i = 1,... ,n. 
For an algebra 21 = (A, oi,..., on) and a non-empty subset V of A, the pair 
(21, V) is called a matrix and V its set of distinguished elements. If 21 is an C- 
(MC-) algebra then (21, V) is an C- (MC-) matrix. An C- (MC-) formula ip is 
said to be valid in an C- (MC-) matrix (21, V) if the value of ip is in V under 
every valuation in 21. We write (21, V) |= (p to mean that (p is valid in (21, V). As 
in the case of the Kripke semantics, we say a logic L is characterized by a class 
C of matrices (or C is characteristic for L) if L coincides with the set of formulas 
that are valid in all matrices in C. 
We shall often deal with C- and A4£-matrices (21, V) in which V contains 
only one element T = _L —> _L. In this case instead of (21, V) \= cp we write 21 \= <p 
and say that ip is valid in 21. Clearly, 21 \= cp iff the identity ip = T is true in 21. 
An algebra is finite if its universe is finite. An algebra whose universe contains 
only one element is called degenerate. A matrix is degenerate if its set of 
distinguished elements coincides with its universe. It should be clear that all identities 
and quasi-identities are true in every degenerate algebra and all formulas are 
valid in every degenerate matrix. 
Suppose 21 = (A, oi,..., on) and 25 = (5, oi,..., on) are similar algebras. A 
map / from A into B is called a homomorphism of 21 in 25 if / preserves the 
operations in the following sense: for every operation o* in 21 of arity m and every 
&!?•••> ^ A, 
• • • ,«m)) = Oi(/(oi),.. . , /(om)). 
A homomorphism / of 21 in 25 is an isomorphism or embedding of 21 in 25 if / is 
an injection, i.e., a ^ b implies /(a) ^ f(b). And if an isomorphism / of 21 in 
25 is also a surjection, that is a map “onto”, then / is called an isomorphism of 
21 onto 25. In this case 21 and 25 are said to be isomorphic. 
Matrices (21, V) and (25, V') are isomorphic if there is an isomorphism / of 
21 onto 25 such that /(V) = V'. 
We will not distinguish between isomorphic algebras or isomorphic matrices. 

THE TARSKI-LINDENBAUM CONSTRUCTION 
195 
7.2 	The Tarski-Lindenbaum construction 
It is very easy to find a characteristic matrix for every modal or si-logic. Indeed, 
suppose L G ExtK (si-logics are treated in exactly the same way simply by 
omitting □) and consider the matrix (2l^£,L) where 
2lM£ = (ForMC, A, V, _L, □) 
is the algebra of formulas in which, for O £ {A, V,—>}, 0(<£,^) = p O ^ and 
D(</>) = Dtp. 
Theorem 7.1 (21 mc,L) is a characteristic matrix for L. 
Proof Suppose that p(pi, -.. ,pn) £ £ and 23 is a valuation in 21^. Then 
23(<p) = <p{%3(pi)/pi, • • • , 23(pn)/pn} G L, since L is closed under Subst. Thus, 
(21 mc,L) |= ip. 
Suppose p L. Define a valuation 23 in 21 mc by taking 23(p) = p for every 
variable p. The value of p under 23 is clearly p itself and so (2l^£,L) p. 
□ 
Of course this theorem conveys nothing else but the fact that L is closed 
under substitution. Let us now recall another useful fact, namely that equivalent 
formulas in normal modal and si-logics are interchangeable. 
Theorem 7.2 Every normal modal and si-logic has a characteristic matrix with 
a single distinguished element 
Proof We consider only L G NExtK. Define an algebra 
2lL HI|ForATC||L, A, V, ->,!,□) 
by taking 
||ForA4£||L = {|MIl ' V € ForATC}, 
\\p\\l = bP £ EorMC : p <-> G L}, 
IMU a Ml = \\<p\\l v Ml = \\<pv ^Wl, 
Ml ^ Ml = \\<p-+1>\\l, -L = ll-Llk, n\\ip\\L = \\Op\\L. 
The correctness of this definition is ensured by the equivalent replacement 
theorem for L according to which the definition of the operations above does not 
depend on the choice of formulas in the equivalence classes \\p\\l and \\^\\l: for 
example, 
IMIl = W\\l and Ml = ||V>'||l imply ||y? A rp\\L = ||p' A ip'\\L. 
As a distinguished element in 21l we take ||T||l = ||_L —> _L||l- Let us prove 
that the matrix (21l, {||T||l}} characterizes L. First, by induction on the 
construction of p(pi,... ,pn) one can readily show that, for any formulas cpi,..., pni 

196 
ALGEBRAIC SEMANTICS 
Now, suppose (p(pi,... ,pn) G L. Then clearly ip <-* T G L. So for all formulas 
we have <p(y>i,... ,<pn) hTgL, i.e., 
lk(^l,...,^n)||L = ||T||l. 
Let 23 be a valuation in 21/, under which 23(p*) = ||<£i||/, for 1 < i < n. Then 
9%) = IbnlU) = lb(^i,...,^n)IU = ||T||l, 
from which (21/,, {||T||/,}) f= <£• 
Suppose that ... ,pn) ^ L- This is equivalent to <-* T ^ L, i.e., 
Ml/, 7^ I|T||l- Define a valuation 23/, in 21/,, called the standard valuation in 21/,, 
by taking 23/, (p) = \\p\\l for every variable p. Then we have 
= ¥>(||Pi||l, • ■ ■ , \\Pnh) = \\<p(pu • • • ,Pn)\\l ~f~ ||T||l, 
from which (21/,, {||T||/,}) ft <p- □ 
Since this proof uses no specific features of normal modal and si-logics except 
the equivalent replacement theorem, the result above can clearly be extended to 
other logics for which this theorem holds. However, this cannot be done in the 
case of quasi-normal modal logics. 
Theorem 7.3 If a logic L G ExtK is characterized by a matrix with a single 
distinguished element then L is normal. 
Proof Let (21, {T}) be a characteristic matrix for L. We show that L is closed 
under necessitation. 
Suppose cp G L. Then the identity <p = T is true in 21 and so Dtp = DT is 
also true. Since DT G K C L, DT = T in 21, from which Dip is identically equal 
to T, i.e., (21, {T}) \= Dtp and Dip e L, because (21, {T}) characterizes L. □ 
Theorem 7.2 can be generalized to quasi-normal logics in the following way. 
Theorem 7.4 Suppose L G NExtK, V G ExtL and 21/, is the algebra defined in 
the proof of Theorem 7.2. Then V is characterized by the matrix (21/,, V) where 
V = {|MU: <peL'}. 
Proof Suppose that <p(p\,... ,pn) G V and 23 is a valuation in 21/, such that 
®(Pi) = ||¥’i|U,.-.,9J(Pn) = ||¥>n|| L- Since ... ,tpn) € U, we then have 
• • •, Vn)Wl € V. Therefore, (2lL, V) (= <p. 
Conversely, suppose <p(pi, • • • ,Pn) & L'. Then 
= <p(\\pi\\L, • • • , IbnlU) = |MPl> • • • ,Pn)\\L & V, 
from which (21l, V) <P- 
□ 

PSEUDO-BOOLEAN ALGEBRAS 
197 
Corollary 7.5 Under the conditions of Theorem 7.4 for every formula p, p £ V 
iff^L(p)eV. 
The matrices (21^, ||T||x,) and (21^, V) defined in the proofs of Theorems 7.2 
and 7.4 are called the Tarski-Lindenbaum matrices for L and L', respectively. If 
the Tarski-Lindenbaum matrix for L has only one distinguished element then it is 
called the Tarski-Lindenbaum algebra for L. The Tarski-Lindenbaum matrix for 
a quasi-normal modal logic V constructed in the proof of Theorem 7.4 depends 
of course on the choice of L. To define the matrix uniquely we may take as L 
the maximal normal logic contained in L', that is kerL'. 
By the definition, the Tarski-Lindenbaum matrices have countably many 
elements. So we have 
Corollary 7.6 (i) Every normal modal and si-logic is characterized by a 
countable algebra. 
(ii) Every quasi-normal modal logic is characterized by a countable matrix. 
Tarski-Lindenbaum matrices and algebras characterize not only logics 
themselves but also the inference rules admissible in them. 
Theorem 7.7 (i) A rule p\,... ^Pm/p is admissible in a logic L £ NExtK or 
L £ Extint iff the quasi-identity pi = T A ... A pn = T —> p = T is true in the 
Tarski-Lindenbaum algebra 21^. 
(ii) Let V £ ExtK and (21^, V) be the Tarski-Lindenbaum matrix defined in 
Theorem 7.4. A rule p\}... ,Pm/p is admissible in V iff for every valuation 23 
in 21l, 23(p) £ V whenever 23(<pi) £ V,... ,23(pm) £ V. 
Proof Since (i) is a special case of (ii) (take V = L), we prove only the latter. 
Let pi,... ,pn be all the variables in pi,..., pmiP- 
(=>) Suppose 23 is a valuation in 21l, 23(p*) = ||Xi||l> for 1 < i < n, and 
<^(||Xi||L,-.-,||Xn||L) € V, for 1 < j < m. Then \\pj\xu • • •, Xn)h € V, from 
which Pj(xi, • • • > Xn) € Lf. Since the rule pi,..., pm/p is admissible in L', 
<£(Xi,---,Xn) € V and so 23(</?) = Mxi,• • •,Xn)h € V. 
(^=) Suppose pi,..., pm/P is not admissible in V. This means that there 
are formulas Xi» • ■ •»Xn such that pi(xu • • • >Xn) £ L',..., pm(Xu • • •, Xn) € L', 
but <p(xi,...,Xn) i Lf. Then 23{pi) = ^(||xi||l, . • •, llXnlk) G V, 1 < i < m, 
and 23(p) = ^(||xi||l» • • •, llXnllz,) i V, which is a contradiction. □ 
7.3 	Pseudo-Boolean algebras 
The Tarski-Lindenbaum algebras, being a direct translation of logics into the 
algebraic language, are too complicated to be a good semantic instrument. Even 
for Cl, which was initially defined as the set of formulas valid in a two-element 
algebra, the Tarski-Lindenbaum algebra is infinite (if, of course, the language 
is infinite). However, just as canonical models are only representatives, though 
very important, of the class of Kripke models, Tarski-Lindenbaum algebras are 
members of a wider class of algebras validating formulas in Int and K. In this 
section we consider the algebras suitable for superintuitionistic logics. 

198 
ALGEBRAIC SEMANTICS 
In fact, all we need is ^-algebras 21 = (A, A, V, —_L) in which the identity 
(p = ip is true whenever <£«->?/>£ Int. Such algebras are called pseudo-Boolean 
algebras or Heyting algebras. A pseudo-Boolean algebra 21 is said to be an algebra 
for a si-logic L if 21 \= L. By Theorem 7.2, the Tarski-Lindenbaum algebra 21l 
for every si-logic L is a pseudo-Boolean algebra for L. 
Theorem 7.8 For each si-logic L and each formula p, ip G L iff p is valid in 
every pseudo-Boolean algebra for L. 
Proof (=>) is trivial and (4=) is a consequence of the fact that 21l is a pseudo- 
Boolean algebra characterizing L. □ 
Example 7.9 The algebra ({T,F}, A, V, —J_) whose operations are defined by 
the truth-table in Section 1.1 is a pseudo-Boolean algebra because Int C Cl. 
The definition above is not convenient for determining if a given £-algebra is 
a pseudo-Boolean one. The next theorem provides a simpler characterization of 
pseudo-Boolean algebras. 
Given an algebra 21 = (A, A, V, —JL), define a binary relation < on A by 
taking, for every x, y G A, 
x <y iff x A y — x. 
As will be shown in Theorem 7.13 below, for a pseudo-Boolean 21 the relation < 
turns out to be a partial order on A. So we can use the terminology introduced 
in Section 2.3 for partial orders, for instance, the greatest element in 21, the least 
element, etc. 
Theorem 7.10 An algebra 21 = (A, A, V, —J_) is a pseudo-Boolean algebra iff 
the following conditions hold in 21 for every x, y G A: 
(1) x Ay = y Ax, xVy = t/Vx (commutativity of A and V); 
(2) x A (y A z) = (x A y) A z, x V (y V z) = (x V y) V z (associativity of A and 
vj; 
(3) (x A y) V y = y, x A (x V y) = x (absorption); 
(4) z A x < y iff z < x —► y (x —> y is the greatest element in the set 
{z e A : z A x < y}); 
(5) _L < x (L is the least element in 21 
Proof (=>) Only (4) needs a proof because the other conditions correspond 
to suitable intuitionistically valid formulas in Table 1.1 (J_ < x corresponds to 
p A _L <-* JL). So suppose z Ax <y, i.e., z Ax Ay = z Ax. Since 
p+-*p/\(q^>q/\p)e Int, 
pA(q^>qAp/\r)+-*p/\(q-j>r)e Int, 
we then have 
z = z A (x x A z) = z A (x x A z Ay) — z A(x y), 
from which z < x y. 

PSEUDO-BOOLEAN ALGEBRAS 
199 
Suppose now that z < x —> y, i.e., z A (x —> y) = z. Since 
pAgAr ^pAgA(p->r) G Int, 
we then have 
xAzAy = xAzA(x^y) = xAz. 
(<£=) The proof in this direction is much harder. First we require 
Lemma 7.11 If (l)-(5) hold in an algebra 21 = (A, A, V, _L) then the 
following conditions are also satisfied in 21 for all x,y G A: 
(6) x Ax = x, x V x = x (idempotency of A and V); 
(7) 	x—>x = ?/—>?/ = _L—►_!_ (= T); 
(8) x A (y —► y) = x (= x A T); 
(9) x A (y —> x) = x; 
(10) x A (x —> y) = x A y; 
(11) x = y iff x < y and y < x; 
(12) x < y iffx ->y = T; 
(13) x Ay = T iffx = y = T; 
(14) x = y iffx *-> y = T; 
(15) if x = T and x —> y = T then y = T; 
(16) x < y iff xV y = y; 
(17) x < z and y < z iff xV y < z; 
(18) x A (y V z) = (x A y) V (x A z) (distributivity). 
Proof (6) We use the laws of absorption: 
xAx = xA(xV(xA x)) = x, xVx = xV(xA(xV x)) = x. 
(7) By (6) we have (x —> x) A y A y = (x —> x) Ay, i.e., (x —> x) A y < y, 
from which by (4), x x < y y, i.e., (x —> x) A (y —> i/) = x —> x. By the 
same argument we obtain (x x) A (y y) = y y. Hence x x — y y 
for every y e A, in particular, ?/ = _L. 
(8) By (6) we have x Ay < y and by (4) x < y —> ^/, i.e., x A (y y) = x. 
(9) By (6) and (4), x Ay < x and x < y —> x, whence xA (y —> x) = x. 
(10) Again, by (6) and (4) we have x y < x y, (x —> y) Ax < y and so, 
using (9), (x —> y) A x = (x —> y) A x A y = x A y. 
(11) if x — y then, by (6), x < y and y < x. Conversely, if x < y and y < x 
then, by the definition of <, we have x = x A y = y. 
(12) Suppose that x —> y = T. Then using (10) and (8), we obtain x Ay = 
xA(x—>y) = xAT = x, i.e., x < y. Suppose x < y. Then, in view of (8), 
x A T <y, from which by (4), T < x —> y, i.e., (x —> y) AT = T. On the other 
hand, by (8), (x y) AT = x —> y, and hence x —> y = T. 
(13) If x = y = T then, by (6), x A y = T. Suppose x A y = T. Since by (6) 
x A y < x, we then have T < x, i.e., T A x = T which together with T A x = x 
(by (8)) gives x = T. The equality y = T is proved analogously. 

200 
ALGEBRAIC SEMANTICS 
(14) x = y iff x < y and y < x (by (11)) 
iff x -> y = y -> x = T (by (12)) 
iff x <-> y = T (by (13)). 
(15) Ifx = x^>y = T then using (6), (8) and (10) we obtain y = y Ax A (x —> 
y) = x A (x —> y) = T A T = T. 
(16) Suppose x < y, i.e., x = x A y. Using the laws of absorption, we then 
obtain x\/y = y\/{xAy) = y. li xV y = y then, by the same laws, x A y = 
x A (x V y) = x, i.e., x < y. 
(17) If x < z and y < z then, by (16), xV z = z = yV z, whence xV y\/ z = z, 
i.e., x\l y <z. Suppose x\l y < z, i.e., by (16), x\l y\l z = z. Using (6), we then 
obtain xM z = x\l y\l z = z, i.e., x < z. In the same way we get y < z. 
(18) According to (11), we need to prove two inequalities: 
(x A y) V (x A z) < x A (y V z) 
and 
x A (y V z) < (x A y) V (x A z). 
By (6) and (16), we have y < y V z and so x A y < x A (y V z). By the same 
argument we obtain x A z < x A (y V z). In view of (17), this establishes the 
former inequality. 
Let us prove the latter. By (16) and (6), we have x Ay < (x A y) V (x A z) 
and x A z < (x A y) V (x A z), from which by (4), y < x —> (x A y) V (x A z) and 
z < x —► (x A y) V (x A z). Therefore, by (17), y V z < x —> (x A y) V (x A z) and 
so, using (4) once again, we obtain x A (y V z) < (x A y) V (x A z). □ 
We can now continue proving Theorem 7.10. We need to show that if an 
equivalence if) «-> x is in Int and an algebra 21 satisfies (l)-(5) and so, by Lemma 7.11, 
(6)-(18) as well, then the identity = x 1S ^rue m 21- In view of (14), it is 
sufficient to establish that ip £ Int implies 211= ip. 
We prove this by induction on the length of a derivation of p in Int. The 
step of induction is already justified: indeed, it is obvious for Subst and (15) 
establishes it for MP. So it remains only to check that the axioms of Int are 
valid in 21. 
(Al) By (9) we have x A (y —> x) = x, i.e., x < y —> x and so, by (12), 
x -> (y -> x) = T. 
(A2) By applying (10) and (6) several times, we obtain 
x A (x —> y) A (x —> (y —> z)) A z = x A y A (y —> z) A z = 
x A y A (y -> z) = x A (x -> y) A (x -> (y -> z)), 
i.e., x A (x —> y) A (x —> (y —> z)) < z, which in view of (4) implies x —> (y —> 
z) < {x —> y) —> (x —> z) and, by (12), 
(x (y -> z)) ((x ^y)^{x-> z)) = T. 

PSEUDO-BOOLEAN ALGEBRAS 
201 
(A3) By the laws of absorption, we have x A (x V y) = x, i.e., x < x V y and 
by (12), x —► x V y = T. 
(A4) follows from x—> £ V y = T by the commutativity of V. 
(A5) By (6), x Ay < x Ay which, by (4), gives x < y —» x Ay and so, by (12), 
x —* (y —* x A y) = T. 
(A6) By (6) we have x Ay < x and by (12) x A y —> x = T. 
(A7) is proved in the same way. 
(A8) Using (18) and (10), we have 
(x V y) A (x —» z) A (y —» z) A z = 
(a; A (x —> z) A (y —> z) A z) V (y A (x —> 2) A (y —> z) A z) = 
{x A {x z) A (y z)) V (y A (x z) A (y -+ z)) = 
(x Vy) A (x -+ z) A (y z), 
from which (x V y) A (x -+ z) A (y -+ z) < z. Now we apply (4), then (12) and 
obtain x —> z < (y —> z) —> (x V y —> z), and hence 
(^z)->((y->z)-^(a:Vy^ z)) = T. 
(A9) follows from (5) and (12). □ 
As a consequence of Theorem 7.10 we derive an interesting 
Corollary 7.12 Suppose that (A, A, V, —>1, _L) and (A, A, V, ->2, -L) are pseudo- 
Boolean algebras with the same universe and the same operations A, V and _L. 
Then x —>1 y = x —>2 y, for every x,y e A. 
Proof According to (4) in Theorem 7.10, the implication in a pseudo-Boolean 
algebra is completely determined by A. □ 
An algebra of the form 21 = (A, A, V) satisfying the conditions (l)-(3) of 
Theorem 7.10 is called a lattice (we already used this notion in Sections 4.1 and 
4.2 when discussing intersections and sums of logics). Pseudo-Boolean algebras 
may be considered as lattices with two additional operations —> and _L. 
Theorem 7.13 In every lattice (A, A,V) the relation < defined by 
x < y iff x A y = x, for x,y e A, 
is a partial order on A; besides, for every x,y € A, 
x <y iff xV y = y. 
Proof Notice first that the conditions (6), (11) and (16) in Lemma 7.11 do not 
depend on (4) and (5) and so hold in every lattice. 
The reflexivity of < follows from (6). As to the transitivity, if x < y and 
y < z, i.e., x = x Ay and y = y A z, then x — xAy = xAyAz = xAz, from 
which x < z. The antisymmetry follows immediately from (11). 

202 
ALGEBRAIC SEMANTICS 
The fact that < can be defined via V is a consequence of (16). □ 
Given a partial order (A, <) and a subset X C A, an element a € A is called 
the supremum or least upper bound of X if X C a[ (i.e., x < a for every x € X) 
and a < b whenever X C a is the infimum or greatest lower bound of X if 
XCaT (i.e., x > a for every x € X) and a > b whenever X C 6|. The supremum 
and infimum of X, if they exist, are denoted by \J X and /\X, respectively. In 
pseudo-Boolean algebras we clearly have \/ 0 = _L and /\0 = T. 
Example 7.14 It is not difficult to see that for every lattice (A, A, V) and every 
oi,...,anGA(n> 0), 
V{°1>" • >an} = fli V. - Van, A(ai>---.an} = ai A ... Aan. 
It follows that in a finite lattice the supremum and infimum do exist for every 
set of elements. However, in general this is not so, witness the following: 
Example 7.15 Let 21 = (A, A, V) be the algebra in which 
A = {1/n, —1/n: n = 1,2,3,...} 
and A and V are defined by 
x A y = min{x, y}) x V y = max{a;, y}, for every x,y G A. 
The reader can readily verify that 21 is a lattice but \J{—l/n : n = 1,2,...} and 
/\{1 jn : n = 1,2,...} do not exist in 21. 
A lattice, in particular a pseudo-Boolean algebra, is complete if /\ JX and \J X 
exist in it for every set X. 
It is useful to observe that the partial order relation < defined in 
Theorem 7.13 completely determines the lattice operations A and V. 
Theorem 7.16 Suppose (A, <) is a partial order such that /\{x, y} and \/{x, y} 
exist for every x, y € A. Then the algebra (A, A, V), with A and V defined by 
X A y = f\{x, y} and x Vy = \J{x, y}, 
is a lattice and 
x <y iff x /\y = x iff x V y = y. 
Proof Exercise. □ 
We use the developed algebraic technique to prove the following remarkable 
result, which is based upon Diego’s theorem from Section 5.4. 
Theorem 7.17. (McKay’s theorem) Every si-logic L axiomatizable by 
disjunction free formulas is finitely approximable and so decidable if the number of 
its extra axioms is finite. 

PSEUDO-BOOLEAN ALGEBRAS 
203 
(a) (b) 
o 
o o 
t 
o 
o 
O 
(c) 
Fig. 7.1. 
Proof Suppose ip £ L. Take any pseudo-Boolean algebra 21 for L in which 
7^ T for some valuation 23 and let B be the closure of the set (23(V>) : 
€ Sub</?} under the operations —>, A, _L in 21. By Diego’s theorem, there 
are finitely many pairwise non-equivalent in Int disjunction free formulas with 
< |Sub^?| variables. Consequently, B is finite. 
Define an operation V* on B by taking, for x,y E B, 
where < is the lattice order in 21. (Since B is finite, /\ in the right-hand part 
always exists.) Clearly, x V* y is the supremum of x and y in B with respect to 
<, x Ay is the infimum and so, by Theorems 7.16 and 7.10, 23 = (B, A, V*, —JL) 
is a pseudo-Boolean algebra. In general, x V y < x\T y (23 is not necessarily a 
subalgebra of 21), but if x Vy E B then we obviously have x Vy = x V* y. It follows 
that the value of ip in 23 under 23 coincides with that in 21 and so is different 
from T. On the other hand, since A and —> in 23 are the restrictions of A and 
—> in 21, and 21 validates all extra axioms of L (which are disjunction free), 23 
must also validate them. Thus, 23 is a finite pseudo-Boolean algebra separating 
(p from L. Using Theorem 7.30, one can construct a finite frame refuting ip and 
validating L. □ 
In Sections 4.1 and 4.2 we saw that the set of (normal) extensions of a logic 
L is a complete lattice with respect to the intersection and sum of logics. The 
partial order relation < in this lattice is the set-theoretic inclusion C, its least 
element is L and greatest one is the inconsistent logic L + JL. Now we introduce 
two more operations on ExtL and NExtL. For every Li,L2 € ExtL, put 
L\ —L/2 = L + {(p : V?/? (%j) E L\ —> E T2)}, 
L\ —>2 L2 = L © {cp : \A/> (V> € L\ —> Vi, j (DVYDji> € T2))}, 
where V is the repeatless disjunction defined in Section 4.1. 
Theorem 7.18 (i) For every modal or si-logic L, (ExtL, n, +, —>1, L) is a 
complete pseudo-Boolean algebra. 
xV*y = A{z € B : x,y < z] 

204 
ALGEBRAIC SEMANTICS 
oT 
(a) (b) 
Fig. 7.2. 
(ii) For every normal modal logic L, (NExtL, Pi, ©, —>2, L) is a complete 
pseudo-Boolean algebra. 
Proof (i) It is sufficient to establish (4) in Theorem 7.10. 
Suppose Ls fi L\ C L2 and ip € L3. Since L3 Pi L\ is axiomatizable by the 
formulas of the form <pV?/>, for <p e L3, ^ G Li, we then have ip € L\ —>1 L2 and 
so L3 C L\ —>1 L2. 
Now suppose that L3 C L\ —>1 L2 and p e L$C\Li. It follows that pV'i/j € L2 
for every %/j £ L\. In particular, we have pVjp € L2 and so ip € L2. Therefore, 
L3 n L\ c L2. 
(ii) is proved in exactly the same way. □ 
A lattice 21 = (A, A, V) is called distributive if the identities 
p A (q V r) = (p A g) V (p A r) and p V (g A r) = (p V g) A (p V r) 
are true in 21. Since these identities correspond to the laws of distributivity 
which are in Int, every pseudo-Boolean algebra is a distributive lattice. As a 
consequence of Theorem 7.18 we obtain 
Corollary 7.19 The lattice of (normal) extensions of every modal or si-logic is 
distributive. 
Since the lattice operations A and V as well as the implication —> and the least 
element _L in pseudo-Boolean algebras are uniquely determined by the partial 
order <, we will represent lattices and pseudo-Boolean algebras in pictures as 
intuitionistic frames (A, <). For example, the lattices shown in Fig. 7.1 (a), 
(b), (c) are pseudo-Boolean algebras, whereas those in Fig. 7.1 (d), (e)—the so 

PSEUDO-BOOLEAN ALGEBRAS 
205 
Fig. 7.3. 
called pentagon and diamond—are not, because these lattices are not distributive. 
By the way, one can prove (see, for instance Gratzer (1978), Theorem 1 in §1, 
Chapter 2) that a lattice is distributive iff it contains neither the pentagon nor 
the diamond as its sublattice. 
Another example of a lattice, this time infinite, is shown in Fig. 7.2 (a). We 
recommend the reader to check that this lattice is a pseudo-Boolean algebra. 
Now we present an important method of constructing pseudo-Boolean 
algebras by associating them with intuitionistic frames. 
Given an intuitionistic frame # = (W,R), define an algebra 
S+ = (Upiy,n,u,D,0), 
where UpW, as before, is the set of upward closed subsets in W, Pi and U are 
the set-theoretic intersection and union and, for every X,Y E UpW, 
XdY = {xeW: Vy (xRy A y E X -> y E Y)} 
(compare this operations with the definition of the truth-relation in intuitionistic 
models in Section 2.2). Notice that a valuation in $ is at the same time a valuation 
in the algebra 3r+. 
Theorem 7.20 (i) For every intuitionistic frame is a pseudo-Boolean 
algebra. 
(ii) If 03 is a valuation in $ (and so in $+) and Wl = (#,9J) then, for every 
formula <p, the value of ip in #+ under is {x : (3Dt, x) f= p>}. In particular, 
$ b V 1= V5- 
Proof Exercise. □ 
The algebra #+ defined above is called the dual of Fig. 7.3 and Fig. 7.4 
show several examples of intuitionistic frames (on the left) and their duals (on 
the right). As an exercise, we invite the reader to check also that the algebra in 
Fig. 7.2 (a) is the dual of the frame in Fig. 7.2 (b). 

206 
ALGEBRAIC SEMANTICS 
The completeness results of Chapter 2 together with Theorem 7.20 and the 
obvious fact that |#+| < 2^' yield us 
Theorem 7.21 The following conditions are equivalent for any formula <p: 
(i) (p e Int; 
(ii) ip is valid in every pseudo-Boolean algebra; 
(iii) ip is valid in every finite pseudo-Boolean algebra; 
(iv) <p is valid in every pseudo-Boolean algebra containing < 22,Subv’1 elements. 
A pseudo-Boolean algebra is called a Boolean algebra if it validates the 
formula p V (p —;► _L) or, equivalently, if the identity p V (p —* JL) = T is true in it. In 
other words, Boolean algebras are those pseudo-Boolean algebras that validate 
all formulas in classical logic Cl. 
Theorem 7.22 The following conditions are equivalent for any formula ip: 
(i) V € Cl; 
(ii) ip is valid in every Boolean algebra; 
(iii) tp is valid in some non-degenerate Boolean algebra. 
Proof Exercise. (Hint: show that the two-element Boolean algebra, determined 
by the truth-table for Cl, can be embedded in every non-degenerate Boolean (and 
even pseudo-Boolean) algebra.) □ 
As follows from Proposition 2.38, all Kripke frames for Cl are of depth 1, 
that is are disjoint unions of single-point frames. Theorem 7.20 provides us then 
with the following examples of Boolean algebras: (2^,0, U, D, 0, ), where D may 
be defined by X D Y = (X D 0)UY = (W-X)UY. For finite W, these algebras 
can be represented as n-ary Boolean cubes shown (for n < 4) in Fig. 7.5. Recall 
that in Section 2.9 we used these cubes without the top elements as the Kripke 
frames characterizing Medvedev’s logic ML. 
7.4 	Filters in pseudo-Boolean algebras 
In this section we consider an algebraic analog of a set of formulas that is closed 
under modus ponens. It will be one of the main links connecting the algebraic 
and relational semantics. 

FILTERS IN PSEUDO-BOOLEAN ALGEBRAS 
207 
Fig. 7.5. 
Let 21 = .(A, A, V, —>, _L) be a pseudo-Boolean algebra. A set V C A is called 
a filter in 21 if 
• T e V and 
• for every x, y € A, if x € V and x —> y € V then y € V. 
Trivial examples of filters in 21 are {T} and A. A filter different from A is called 
proper. 
Equivalent definitions of filter, which do not involve —» and T and so are 
suitable for arbitrary lattices, are formulated in 
Theorem 7.23 Suppose 21 = (A, A, V, —», JL) is a pseudo-Boolean algebra and 
VC A Then the following conditions are equivalent: 
(1) 
(2) 
(3) 
(4) 
V is a 
filter in 21; 
(2a) 
and 
(2b) 
x 6 V and 
y € V iff x Ay eS/, for every x, y € A; 
(3a) 
V^0, 
(3b) 
if xev, y 
e V 
then x A y e V, 
(3c) 
if xeV,y 
€ 4 
then x V y € V, /or even/ x,y € A, 
(4a) 
V^0, 
(4b) 
i/ieV, y 
€ V 
then x A y e V, 
(4c) 
if x € V, x 
< y 
then y € V, /or even/ x, y 6 A. 
Proof We establish the implications (1) => (2) => (3) => (4) => (1). 
(1) => (2). Suppose that x,y € V. Since x (y x A y) = T € V, 
by the definition of filter we then have x Ay € V. The converse follows from 
x A y x = T e V and x Ay y = T G V. 
(2) => (3). Suppose ieV and y € A. By the law of absorption, we then have 
x = x A (x V y) € V and so, by (2b), x V y e V. 
(3) => (4). Ifx€ V and x < y then y = x\/ y and so, by (3c), y € V. 
(4) => (1). Let x be an element in V. Since x < T, (4c) yields us T e V. 
Suppose now that x e V and x —» y € V. By (4b), x A (x —» t/) 6 V and since 

208 
ALGEBRAIC SEMANTICS 
x A (x —* y) = x A y, we have x A y E V, from which y € V because x Ay < y. 
□ 
A set V of elements in a lattice 21 = (A, A, V) is a filter if it satisfies one of 
the conditions (2), (3), (4) in Theorem 7.23. The reader can readily show that 
these conditions are equivalent in every lattice. 
The condition (4) shows a way of constructing the smallest filter to contain 
a given non-empty set X of elements in a lattice 21 = (A, A, V). That such a 
filter exists—call it the filter generated by X—follows from the evident fact that 
the intersection of an arbitrary family of filters containing X is again a filter 
containing X. Put 
[X) = {y € A: Xi A ... A xn < y) for some Xi,... , xn E X}. 
Theorem 7.24 For every X ^ 0, [X) is the filter generated by X in 21. 
Proof First we show that [X) satisfies (4). Indeed, clearly [X) ^ 0. Suppose 
x, y E [X). Then there are xi,..., xn, t/i,..., ym £ X such that X\ A ... A xn < x 
and yi A ... A ym < y. It follows that 
Xi A ... A xn A yi A ... A ym < x A y 
and so x Ay € [X), which proves (4b). Finally, (4c) holds because < is transitive. 
Now, by Theorem 7.23, every filter V containing X contains also [X). 
Therefore, [X) is the smallest filter containing X. □ 
If a lattice 21 has the greatest element T, often called the unit of 21, then 
we may put [0) = {T}. If X is a singleton {x} then instead of [{x}) we write 
simply [x) and say that this filter is generated by x. A filter generated by a single 
element is called principal Every filter in a finite lattice is principal, because it 
is generated by the conjunction of its elements. 
In view of the duality between the lattice operations A and V we can define 
a notion dual to the notion of filter. Say that a set A of elements in a lattice 
21 = (A, A, V) is an ideal if one of the following conditions (2'), (3'), (4') holds, 
for every x, y < 
E A: 
(2'a) 
Ik 
<1 
\z ) 
(2'b) 
x E A and yEAiffxVt/EA; 
(3'a) 
A^0, 
(3') 
(3'b) 
if x, y E A then x V y E A, 
(3'c) 
if x E A and y E A then x A y E A; 
(4'a) 
A^0, 
(4') 
(4'b) 
if x, y E A then x V y e A, 
(4'c) 
if y € A and x < y then x E A. 

FILTERS IN PSEUDO-BOOLEAN ALGEBRAS 
209 
We leave to the reader proving the fact that these conditions are equivalent. The 
reader can readily show also that the smallest ideal to contain a non-empty set 
X—the ideal generated by X—is the set 
(X] = {y G A : y < x i V... V xn, for some X\,... ,xn G X}. 
If 21 has the least element _L, often called the zero of 21, then we put (0] = _L. 
Proposition 7.25 Suppose 21 is a pseudo-Boolean algebra and V a filter in 21. 
Then the set of filters in 21 containing V forms a complete distributive lattice 
with the infimum and supremum defined by 
/\{Vj : V{V*: i€/} = [ljvi). 
i£/ iGJ 
Proof Exercise. □ 
The lattice of filters in 21 containing V = {T} is called the lattice of filters in 
21. 
Theorem 7.26 (i) Suppose L is a normal modal (or si-) logic. Then the 
lattice (NExtL, Pi, ©, L) (respectively, (ExtL, Pi, +, L)) is embedded in the lattice of 
filters in the Tarski-Lindenbaum algebra 21l by the map f defined by 
f(L') = {Ml: <peL>}. 
The isomorphism f preserves infimums and supremums in the sense that the 
equalities 
Hf\x) = /\f(X), f(\Jx) = \ff(x) 
hold for every X C NExtL (X C ExtL). 
(ii) Suppose that L is a quasi-normal modal logic and (21l0, V) its Tarski- 
Lindenbaum matrix for some normal Lq C L. Then (ExtL, Pi, +, L) is embedded 
in the lattice of filters in 21 l0 containing V by the map f defined by 
f(L') — {IMUo : veL'} 
and preserving infimums and supremums. 
Proof There is no essential difference between the proofs of (i) and (ii). We 
confine ourselves to proving (ii). 
That / is an injection follows from Theorem 7.4. So it suffices to establish 
that / preserves /\ and V- Let X = {Li : i G 1} C ExtL. 
If IMUo £ /(A*)then ^ £ fliei Li- If follows that |M|l0 £ /(Li), for every 
i G /, and so \\ip\\Lo G A f(X) = (]ieI /(L<). Conversely, if ||<p||Lo € A /PO then 
Mlo € /(Li), for every i e I. So we have <p e Li, from which G Hie/ Li and 
IMUo e mieILi) = f{/\X). Thus, /(f\X) = f\f(X). 

210 
ALGEBRAIC SEMANTICS 
To establish f(\/X) = V f(X), suppose first that |M|l0 € f(\/X), i.e., 
ip G Li- Since every derivation contains only finitely many formulas and 
by the deduction theorem, there are J = Q I and formulas ipj G 
L%., for j = 1,... ,n, such that ipi A ... A ipn —► ip G L. But then we have 
llvillio A.. • A ||v?„||l0 -*■ ||v?||l0 e V, llvillio € f{Lij,... ,\\<pn\\Lo e /(£*„) and 
so ||<Pi||lo A ... A ||<p„||l0 € V/W. from which |M|z,0 €\/f(X). 
Now let IMUo € V f(X). Then there are J = {n,. J and ||^||l0 € 
/(Tij), for j = 1,..., n, such that ||<^i||l0 A... A ||v?„||l0 < ll^lUo- It follows that 
ipi A ... A ipn —> ip € L$. Since ipj G , for every j = 1,..., n, we then have 
¥> G Ej€j ^ and so |M|x,0 6 /(Ei6/ ^i) = /(V *)• □ 
Our next aim is to prove the conversion of Theorem 7.20 for finite algebras. 
In other words, we are going to show that every finite pseudo-Boolean algebra 
is (isomorphic to) the dual of some intuitionistic frame. 
The main role in this representation of pseudo-Boolean algebras is played by 
prime filters. A filter V in a lattice is said to be prime if it is proper and xVy G V 
implies x G V or y G V. An ideal A is called prime if it is proper and with every 
element of the form x A y it contains also either x or y. 
Proposition 7.27 Suppose V and A are disjoint sets in a lattice (A, A, V) such 
that V U A = A. Then V is a prime filter iff A is a prime ideal. 
Proof Exercise. □ 
Since all filters in a finite lattice are principal, we associate with every filter 
in such a lattice the element generating it. Say that an element a in a lattice is 
prime if a ^ _L and a = bV c implies either a = b or a = c. 
Lemma 7.28 A principal filter in a distributive lattice is prime iff it is generated 
by a prime element. 
Proof (=>) follows directly from the definitions. 
(4=) Suppose V is generated by a prime element a and let b V c G V. Then 
a = a A (b V c) = (a A b) V (a A c), from which either a = aAi)G Vora = aAcG V 
and so, by (2b), either b G V or c G V. □ 
As an exercise, we recommend the reader to find all prime filters in the 
pseudo-Boolean algebras shown in Fig. 7.2 and 7.3. 
Lemma 7.29 If a is a prime element in a distributive lattice and a < 6Vc then 
a < b or a < c. 
Proof We have a = a A (b V c) = {a A b) V (a A c) from which a = a A b or 
a = a A c, i.e., either a < b or a < c. □ 
Theorem 7.30 Every finite pseudo-Boolean algebra is isomorphic to the dual 
of some finite intuitionistic frame. 

FILTERS IN PSEUDO-BOOLEAN ALGEBRAS 
211 
Proof Suppose 21 = {A, A, V, —_L) is a finite pseudo-Boolean algebra and W 
the set of its prime elements. Define a partial order R on W by taking, for every 
x,y eW, 
xRy iff y < x, 
where < is the lattice partial order in 21, and let *5 = (W,R). We are going to 
show that 21 is isomorphic to Sr+. 
Notice first that every a G A is represented as \J{b e W : 6 < a}, in 
particular, _L = \J 0. Define a map / from A into UpW by taking, for every 
ae A, 
f(a) = {beW: b<a}e Up W 
and show that / is an isomorphism of 21 onto Sr+. 
Since every element a in 21 is completely determined by the prime elements 
that are < a, / is an injection. To show that / is a surjection, take any element 
X G UpW and let a = \J{b : b e X}. It follows from the definition of / that 
X C /(a). The converse inclusion is a consequence of Lemma 7.29. 
Let us check now that / preserves the operations. By Corollary 7.12 and 
Theorem 7.20, it suffices to show that / preserves A, V and ±. 
If c G f(a A b) then c < a A b and so c < a and c < 6, from which c G /(a), 
c G f(b) and c G f(a) fl /(&). Conversely, if c G f(a) fl f(b) then c < a, c < b and 
hence c < a A 6, i.e., c G f(a A b). Therefore, f(a A b) = f(a) n /(&). 
Suppose now that cG f(a V b). Then c < a V b which, by Lemma 7.29, means 
that either c = cAaorc = cA6, in other words, either c < a or c < b. It follows 
that c G f(a) or c G f{b) and so c G /(a) U /(&). Conversely, if c G /(a) U /(&) 
then c G /(a) or c G /(&). Suppose for definiteness that c G f(a). Then c e W, 
c < a, hence c < a V b and finally c G f(a V 6). 
That /(-L) = 0 follows immediately from the definition of /. □ 
The frame # constructed in the proof of Theorem 7.30 is called the dual of 
21; it will be denoted by 21+. 
The following notions will be used mostly for Boolean algebras. A proper 
filter V in a lattice 21 is called maximal if it is not contained in a proper filter 
in 21 different from V. A proper filter V in a pseudo-Boolean algebra 21 is an 
ultrafilter if, for every element a in 21, either a G V or -<a = a —► _L G V. 
Theorem 7.31 For every filter V in a pseudo-Boolean algebra the following 
conditions are equivalent: 
(i) V is a maximal filter; 
(ii) V is an ultrafilter. 
Proof IfV is an ultrafilter then it cannot be extended to another proper filter 
because for every a V, we have -<a G V and so _L G [V U {a}). The implication 
(i) => (ii) is a consequence of the following lemma. □ 
Lemma 7.32 For every proper filter V and every element a in a pseudo-Boolean 
dlgebra, at least one of the filters [V U {a}) or [V U {~ia}) is proper. 

212 
ALGEBRAIC SEMANTICS 
Proof If [V U {a}) is not proper then 1 G [VU {a}) and so cAa < 1, for some 
c G V. It follows that c < -■ a, i.e., [V U {~ia}) = V is a proper filter. □ 
For Boolean algebras Theorem 7.31 can be generalized to 
Theorem 7.33 For every filter V in a Boolean algebra 21 the following 
conditions are equivalent: 
(i) V is a maximal filter; 
(ii) V is an ultrafilter; 
(iii) V is a prime filter. 
Proof By Theorem 7.31, it is sufficient to show that (i) => (iii) and (iii) => (ii). 
To prove the former implication, suppose V is a maximal filter. If V is not 
prime then there are elements a and b in 21 such that aVf>eV,a^V and 
b V. By Theorem 7.31, we then have -«a G V, -*b G V and hence, since 
-*p —> (-*q —> -i(p V q)) G Int, -i(a V b) G V, contrary to V being a proper filter. 
The latter implication follows from the fact that in Boolean algebras aV-ia = T, 
for every element a, and so every prime filter must contain either a or -■a. □ 
As a consequence of Theorems 7.30 and 7.33 we derive 
Corollary 7.34 Every finite Boolean algebra 21 is isomorphic to an algebra of 
the form (2W, fi, U, D, 0) where X D Y = (W - X) U Y, for every X,Y C W. 
Proof Suppose 21+ = (W,R), i.e., 21 is isomorphic to (UpW, fi, U, D, 0) where 
X D Y = {x G W : Vy{xRy A y G X —► y G Y}. We show that the frame 21+ is 
of depth 1. Indeed, if xRy, for some x,y e W, then, by the construction of 21+, 
[z) 	S [y). And since the filters [x) and [y) are prime, they are maximal and so 
[x) = [*/), i.e., x = y. Therefore, UpW = 2W and X dY = {x eW : x e X —> 
xeY} = (W-X)\JY. □ 
It is not difficult to characterize principal ultrafilters in pseudo-Boolean 
algebras. Say that an element a/.L in such an algebra 21 is an atom if, for every 
x in 21, x < a implies x = _L or x = a; in other words, a is a minimal element 
among those different from the zero. 
Theorem 7.35 (i) An element in a Boolean algebra is prime iff it is an atom. 
(ii) A principal filter in a pseudo-Boolean algebra is an ultrafilter iff it is 
generated by an atom. 
Proof Exercise. □ 
However, infinite Boolean algebras contain non-principal ultrafilters. 
Example 7.36 Let # = (W, =) be an infinite frame (of depth 1). Then the 
set V C 2W containing all cofinite subsets of W is clearly a proper filter in 
the Boolean algebra Sr+. It is non-principal, because the intersection of sets in 
V is empty, and moreover, according to Theorem 7.35, it cannot be extended 
to a principal ultrafilter (for otherwise the principal ultrafilter containing V is 
generated by a point x G W, whereas W — {x} G V). On the other hand, as will 
be shown below, every proper filter is contained in an ultrafilter. 

FILTERS IN PSEUDO-BOOLEAN ALGEBRAS 
213 
To this end we require the well known 
Lemma 7.37. (Zorn’s lemma) If the points of every chain in a partial order 
$ have a common successor then every point in $ sees a final point. 
We can apply Zorn’s lemma to the partially ordered (by C) set of filters or 
ideals in an arbitrary lattice. For we clearly have 
Lemma 7.38 The union of any chain of proper filters (or ideals) in a lattice 
with zero (respectively, unit) element is again a proper filter (ideal). 
Putting these two lemmas together, we obtain 
Theorem 7.39 Every proper filter (ideal) in a lattice with zero (unit) element 
can be extended to a maximal filter (ideal). In particular, every proper filter in a 
pseudo-Boolean algebra is contained in an ultrafilter. 
Corollary 7.40 Every proper filter in a Boolean algebra is the intersection of 
all ultrafilters containing it. 
Proof Let V be a proper filter in a Boolean algebra 21 and a $ V. Then the filter 
[VU{-ia}) is also proper, for otherwise there is b G V such that bA-^a < _L and so 
b < -i-ia, which is a contradiction because -i-ia = a and a $ V. By Theorem 7.39, 
[Vu{-ia}) can be extended to an ultrafilter Va. Therefore, V = P|agv □ 
In pseudo-Boolean algebras every maximal filter is prime, but not the 
converse (see Fig. 7.3). The following useful result on the existence of prime filters 
plays in the algebraic semantics the same role as Lindenbaum’s lemma plays in 
the Kripke semantics. 
Theorem 7.41 Suppose V (A) is a filter (ideal) in a distributive lattice 21 and 
a ^ V (a £ A). Then there is a prime filter V' (prime ideal A1) in 21 such that 
V C V' and a & V' (respectively, A C A' and a £ Af). 
Proof By Zorn’s lemma and Lemma 7.38, there exists a maximal filter V' in 
21 which contains V and does not contain a. We shall show that V' is prime. 
Suppose otherwise. Then there are elements c and d in 21 such that cVdG V', 
V' and d £ V'. Let Vc = [V' U {c}), Vd = [V' U {d}). Since Vc and are 
different from V', we then have a G Vcfl Vd and so there are elements fq, b<i G V' 
such that bi A c < a and 62 A d < a. It follows that b\ A 62 A c < a, 61 A 62 A d < a 
and so, by Lemma 7.11 (17), (61 A 62 A c) V (61 A 62 A d) < a. Using distributivity 
we then obtain (61 A 62) A (c V d) < a. And since fq A 62 £ V', c V d G V', we have 
{b 1 A 62) A(cVd) G V', whence a G V', which is a contradiction. 
By duality we obtain the proof for ideals. □ 
Corollary 7.42 Suppose that a and b are elements in a distributive lattice such 
that b a. Then there exists a prime filter V' (prime ideal A') such that a $ V' 
and b G V' (respectively, a G A' and b £ Af). 
Proof It is sufficient to take V = [b) and use Theorem 7.41. 
□ 

214 
ALGEBRAIC SEMANTICS 
7.5 	Modal algebras and matrices 
In this section we consider algebras and matrices corresponding to normal and 
quasi-normal modal logics. 
An algebra 21 = (A, A, V, —>, _L, □) is called a modal algebra if the identity 
<p = ^ is true in 21 for every modal formulas <p and -0 such that y? <-► 0 E K. If 
we replace in this definition K with a normal modal logic L then 21 is called an 
algebra for L or an L-algebra; in particular, all modal algebras are K-algebras. 
Some modal algebras have their specific names: for instance, K4-algebras are 
sometimes called transitive algebras, S4-algebras topological Boolean algebras, 
Grz-algebras Grzegorczyk algebras, GL-algebras diagonalizable or Magarian 
algebras. 
By Theorem 7.2, the Tarski-Lindenbaum algebra for every normal modal 
logic L is an L-algebra characterizing L, and so we have 
Theorem 7.43 For each normal modal logic L and each formula (p, (p E L iff 
<p is valid in every modal algebra for L. 
Theorem 7.44 An algebra 21 = (A, A, V, —>, _L, □) is modal iff it satisfies the 
following conditions: 
(i) (A, A, V, —>, _L) is a Boolean algebra; 
(ii) for every x,y E A, □(# Ay) = Ox A Oy; 
(iii) DT = T. 
Proof The implication (=>) follows from Cl C K, 0(p A q) <-► Op A Oq e K 
and OT hTgK. 
(<^=) As in the proof of Theorem 7.10, it suffices to show that 211= <p for every 
(p E K, which can be done by induction on the length of a derivation of <p in 
K. The induction step is clear—Subst and MP were considered in the proof of 
Theorem 7.10 and the implication 21 \= (p => 21 \= Oip follows from (iii). 
So it remains to justify the basis of induction. The axioms of Cl are valid in 21 
because it is a Boolean algebra. As to the modal axiom of K, for every x, y E A we 
have (x —> y) Ax Ay = (x —> y) Ax (since 21 is a Boolean algebra), whence D((x —► 
y) Ax Ay) = □((x —> y) Ax) and, by (ii), □(# y) AOx AOy = n(x —> y) A Ox. 
Therefore, D(x —► y) A Ox < Dy, from which we obtain D(x —> y) < Ox —> Oy 
and finally D(x —> y) —► (□# —> Oy) = T. □ 
Corollary 7.45 Suppose L — K 0 {<pi : i e I}. Then an MC-algebra 21 is an 
L-algebra iff it satisfies (i)-(iii) in Theorem 7.44 and 
(iv) 211= ipi, for every i e I. 
The following construction, connecting modal algebras and frames, provides 
us with multiple examples of concrete modal algebras. 
Given a modal frame = (W, JR), we define an algebra 
5+ = (2vv,n,u,D,0, □), 
called the dual of *$, by taking, for every X, Y C W, 

MODAL ALGEBRAS AND MATRICES 
215 
XdY = (W-X)UY, 
nx = {xew : Vy (xRy ->yel)} 
(compare these operations with the definition of the truth-relation in modal 
models in Section 3.2). 
Theorem 7.46 (i) For every modal frame #, its dual #+ is a modal algebra; 
(ii) If 03 is a valuation in # (and so in $~*~) and 9Jt = (#,93) then, for every 
formula ip, the value of (p in #+ under 93 is {x : (931, x) |= <p}. In particular, 
S' (= <P iff$+ (= <P- 
Proof Exercise. □ 
This result is a modal counterpart of Theorem 7.20, while Theorem 7.30 is 
analogous to 
Theorem 7.47 Every finite modal algebra is isomorphic to the dual of some 
finite modal frame. 
Proof Let 21 = (A, A, V, —>, _L, □) be a finite modal algebra. Since the algebra 
(A, A, V, —_L) is Boolean, by Corollary 7.34 it is isomorphic to the algebra 
(2W, fl, U, D, 0), where W is the set of atoms in 21, an isomorphism being the 
map / defined by f(a) = {b eW : b < a}. 
Define a binary relation R on W by taking, for every x,y eW, 
xRy iff Vz E A (x < Oz —> y < z) 
and let # = (W, R). We prove that / is an isomorphism of 21 onto #+. It should be 
clear from the considerations above that it suffices to show only that / preserves 
□. 
Suppose x E /(Da). Then x E W and x < Da. By the definition of □ in 
#+, we need to show that Vy (xRy —> y e f(n)). So suppose xRy. Then by the 
definition of R, y < a and so y e f(a). 
Conversely, assume x E L]/(a) and show that x < Da. The element Dv = 
/\{Du : x < Du} = □ /\{u : x < Du} is clearly the least “boxed” element in 
the set {Du : x < Du} and so we have x < Uu iff Dv < Du. By the definitions 
of R and /, the condition x e n/(a) means that 
Vy e W (Vz E A (x < Oz —> y < z) —> y < a), 
which, according to our choice of v, is equivalent to 
Vy E W (y < v —» y < a). (7.1) 
It follows that v < a. Indeed, if v ^ a then, by Corollary 7.42, v A ~^a belongs to 
an ultrafilter generated by some y0 E W such that yo < v and yo ^ a, which in 
view of (7.1) is a contradiction. From v < a we obtain Uv < Da and so x < Da, 
i-e., x E /(Da). □ 

216 
ALGEBRAIC SEMANTICS 
The frame # defined in the proof above is called the dual of the algebra 21 
and denoted by 21+. 
Let us now turn to modal logics that are not necessarily closed under the rule 
of necessitation. If 21 is a modal algebra and V a filter in 21 then the pair (21, V) 
is called a modal matrix. We say that (21, V) is a matrix for a quasi-normal logic 
L or simply an L-matrix if (21, V) |= L. Since the Tarski-Lindenbaum matrix for 
L, as defined in Theorem 7.4, characterizes L, we have the following: 
Theorem 7.48 Suppose L is a quasi-normal modal logic and ip a modal formula. 
Then p e L iff ip is valid in every modal matrix for L. 
Given a modal frame # = (W, R) with a set D of distinguished points, define 
the dual (#, D)+ of (#,£>) as the matrix (5r+,D+) in which 
D+ = {XCW: D Cl}. 
Theorem 7.49 (i) If (#, D) is a modal frame with distinguished points then 
($, D)+ is a modal matrix. 
(ii) For every formula <p, (#, D) |= ip iff (#, D)+ (=</?. 
Proof Exercise. □ 
Theorem 7.50 Every finite modal matrix is isomorphic to the dual of some 
finite modal frame with distinguished points. 
Proof Let (21, V) be a modal matrix, / the isomorphism of 21 onto the dual of 
21+ = {W, R) defined in the proof of Theorem 7.47. Suppose also that the filter 
V is generated by an element a in 21. As a set of distinguished points in 21+ we 
take 
D = f(a) = {x e W : x < a) 
and show that x e V iff f(x) e Z5+, for every element x in 21. 
If x G V, i.e., a < x then f(a) C /(x) and so D C f(x) or, equivalently, 
f(x) e D+. Conversely, if f(x) e D+ then D = f(a) C /(x), from which 
a = V f(a) < V f(x) = x and so x e [a) = V. □ 
7.6 	Varieties of algebras and matrices 
We defined pseudo-Boolean, Boolean and modal algebras as algebras validating 
some (infinite) collections of identities. In general, the class of all algebras (of 
the same similarity type), in which all identities in a given set T are valid, is 
called a variety of algebras (of this type) and denoted by VarT. If T is a set of 
C- or A4£-formulas then by VarT we mean the variety of C- or, respectively, 
A4£-algebras generated by the identities <p = T such that tp G T. 
Conversely, given a class C of (pseudo-Boolean or modal) algebras, it is 
natural to consider the set LogC of formulas that are validated by every algebra in 
C. The abbreviation Log here is not accidental. For it is quite easy to see that 
the following is true: 

VARIETIES OF ALGEBRAS AND MATRICES 
217 
Theorem 7.51 If C is a non-empty class of pseudo-Boolean or modal algebras, 
then LogC is a superintuitionistic or, respectively, normal modal logic. 
As a consequence of Theorems 7.8 and 7.43 we obtain 
Theorem 7.52 Suppose V is a variety of pseudo-Boolean or modal algebras and 
L a superintuitionistic or, respectively, normal modal logic. Then 
VarLogV = V, LogVar L = L. 
The variety VarL is called the characteristic variety for the logic L. 
Theorem 7.52 states in essence that the relation “logic <-► its characteristic variety” 
is a 1-1 correspondence between the classes of superintuitionistic and normal 
modal logics and the classes of varieties of pseudo-Boolean and modal algebras, 
respectively. In fact this correspondence catches much subtler properties of the 
classes under consideration. 
In the classes of varieties of pseudo-Boolean and modal algebras we define 
lattice operations A and V by taking, for any varieties Vi and V2, 
Vi A V2 = Vi fl V2 and Vi V V2 = VarLog(Vi U V2). 
Theorem 7.53 Suppose L is a normal modal or si-logic. Then the class of all 
varieties of L-algebras is a complete lattice with respect to the operations A and 
V defined above. 
Proof Exercise (for details see the proof of Theorem 7.56 below). □ 
Suppose 21 = (A, A, V) and 23 = (£?, A,V) are lattices. A bijection (i.e., 
simultaneously injective and surjective map) / from A onto B is said to be a 
dual isomorphism of 21 onto 23 if it dually preserves the lattice operations in the 
following sense: for every x,y G A, 
f(x A y) = f(x) V f(y), f(x Vy) = f(x) A f(y) 
(or equivalently, if / dually preserves the lattice partial order, i.e., x < y iff 
f(x) > f(y)). Lattices 21 and 23 are dually isomorphic if there is a dual 
isomorphism of 21 onto 23. It should be clear that dually isomorphic lattices are 
complete or incomplete simultaneously and that a dual isomorphism / of a 
complete lattice 21 onto a lattice 23 dually preserves infimums and supremums, i.e., 
for every X C A, 
f(/\X) = \/f(X), f(\/X) = /\f(X). 
Theorem 7.54 Suppose L is a normal modal or si-logic. Then the map “logic 
its characteristic variety” is a dual isomorphism of the lattice NExtL or, 
respectively, ExtL onto the lattice of all varieties of L-algebras. 
Proof Exercise (for details see the proof of Theorem 7.56 below). 
□ 

218 
ALGEBRAIC SEMANTICS 
Using this theorem, problems concerning normal modal and si-logics 
maybe reformulated in terms of varieties of corresponding algebras, which is 
sometimes very helpful because we can take advantage of the developed apparatus of 
universal algebra. 
Now we extend the notion of variety from algebras to modal matrices. Since 
it is always clear from the context whether we deal with algebras or matrices, we 
will use for varieties of matrices the same notations as for varieties of algebras. 
A variety of modal matrices is the class of all modal matrices validating the 
formulas in a given set T; as before it is denoted by VarT. The set of formulas 
validated by all matrices in a class C is also denoted by LogC. Instead of VarLogC 
we will write VarC and say that the variety VarC is generated by the class of 
matrices C. The same concerns varieties of algebras as well. 
The following theorems are matrix counterparts of Theorems 7.51-7.54. 
Theorem 7.55 (i) IfC is a class of modal matrices then LogC is a quasi-normal 
modal logic. 
(ii) If V is a variety of modal matrices and L a quasi-normal logic then 
VarLogV = V, LogVar L = L. 
The variety VarL of matrices is called the characteristic variety of matrices 
for the quasi-normal logic L. The lattice operations A and V on varieties of 
matrices are defined in exactly the same way as on varieties of algebras. 
Theorem 7.56 Suppose L is a quasi-normal modal logic. Then 
(i) the class of varieties of modal matrices for L is a complete lattice with 
respect to A and V; 
(ii) the map “quasi-normal logic —> its characteristic variety” is a dual 
isomorphism of the lattice ExtL onto the lattice of varieties of L-matrices. 
Proof Since (ExtL, fi, +) is a complete lattice, it is sufficient to show that the 
map / defined by f(L') = VarL', for L' G ExtL, is a dual isomorphism. 
That / is a bijection follows from Theorem 7.55. Let us prove that it preserves 
the lattice operations, i.e., for Li,L2 G ExtL, 
Var(Li n L2) = VarLi V VarL2 = Var(VarLi U VarL2), 
Var(Li -f L2) = VarLi A VarL2 = VarLi fi VarL2. 
Suppose first that (21, V) G Var(Li PiL2), i.e., (21, V) |= L\ PiL2, but (21, V) & 
VarLi VVarL2. The latter assumption means that there is a formula ip G Li PiL2 
such that (21, V) ^ from which (21, V) ^ Li fi L2, contrary to the former 
assumption. Therefore, Var(Lx flL2) C VarLi V VarL2. To establish the converse 
inclusion, suppose (21, V) G VarLi V VarL2. This means that (21, V) |= ip, for 
every <p G Li 0 L2, and so (21, V) G Var(Li n L2). 
Suppose now that (21, V) G Var(Li -f L2) but (21, V) ^ VarLi fl VarL2. Then 
there is a formula <pt G Li, for some i G {1,2}, such that (21, V) ]/= <pi. However, 

OPERATIONS ON ALGEBRAS AND MATRICES 
219 
Li Q Li 4- L2 and so we must have (21, V) |= </?*, which is a contradiction. Thus, 
Var(Li -f L2) C VarLi A VarL2- 
Finally, let (21, V) G VarLi A VarL2- To establish (21, V) G Var(Li 4- L2) we 
must show that (21, V) |= tp for every formula ip G L1+L2. So assume </? G L1+L2. 
Then there are formulas </?i,..., pn G Li U L2 such that </?i A ... A pn —> p G L. 
Since (21, V) validates all formulas in L\ and L2, we have (21, V) (= y?i A...Apn. 
And since (21, V) is an L-matrix, we obtain (21, V) |= y?i A ... A y?n —> </? and 
hence (21, V) (= </?. □ 
7.7 	Operations on algebras and matrices 
In this section we consider three fundamental algebra and matrix constructing 
operations, namely, forming subalgebras and submatrices, direct products of 
algebras and matrices and their homomorphic images. If we regard pseudo-Boolean 
and modal algebras (at least some of them) as duals of Kripke frames then it 
turns out that these operations are algebraic analogues of the frame-theoretic 
operations of forming reducts, disjoint unions and generated subframes. In full 
detail this correspondence will be studied in the next chapter as a part of general 
duality theory. Here it is our main source of examples. 
Suppose 21 = (A, 01,..., on) is an algebra and B a subset of A closed under 
the operations in 21 (i.e., the result of applying any o* to elements in B is again an 
element in B; in particular, if 21 is a pseudo-Boolean algebra then _L G B). In this 
case the algebra 25 = (B, 01,..., on), whose operations are the restrictions of 2l’s 
operations to B, is said to be a subalgebra of 21. For X C A, the subalgebra of 21 
with the smallest universe containing X is called the subalgebra generated by X. 
(That such a subalgebra exists follows from the obvious fact that the intersection 
of subalgebras is again a subalgebra.) In particular, if this subalgebra is 21 itself 
then we say that 21 is generated by X. In the case when the algebra 21 is generated 
by 0 it is called 0-generated (if it is a pseudo-Boolean algebra then A is the closure 
of {_!_} under A, V and —>). More generally, the subalgebra of 21 (in particular, 
21 itself) generated by a set of cardinality x is said to be x-generated. 
Example 7.57 Let #+ = (2W, fl, U, D, 0, □) be the dual of a modal frame # 
and 23 a valuation in 3r. Then the set P C defined by 
P = {*0(<p) : <p G ForMC} 
is closed under the operations in #+ because, for all formulas ip and 0 = 2J(-L), 
23((/?) n23(ip) = 23((^ A V>), 93(y>) U93(^>) = 23(<^ V-0), 2J(p) d 23(-0) = 23(<^ —► -0), 
□23(<^) = 23(□</?). The same, of course, concerns intuitionistic frames. Thus, 
every valuation in a frame determines a subalgebra of its dual. 
Example 7.58 Suppose / is a reduction of a modal frame # = (W, R) to a 
frame 0 = (V, S). Then it is not hard to check (for details see Section 8.5) that 
the set A = {f~1(X) : X C V} is closed under the operations in 3r+. Let 21 be 
the subalgebra of #+ with the universe A. The map g from 2V into 2W defined 

220 
ALGEBRAIC SEMANTICS 
by g(X) = f~1(X) is an embedding of 0+ in #+ and an isomorphism of 0+ 
onto 21. 
As to submatrices, we say that a modal matrix (212, V2) is a submatrix of a 
modal matrix (2li, Vi) if 2I2 is a subalgebra of 2li and V2 is the intersection of 
Vi with 2l2’s universe (see Exercise 7.11). 
Let C be a class of algebras (or matrices). Denote by SC the class of all 
subalgebras (respectively, submatrices) of algebras (matrices) in C. The following 
proposition is a direct consequence of the definitions above: 
Proposition 7.59 (i) If a formula <p is valid in an algebra 21 (matrix (21, V)J 
then ip is valid in every subalgebra (submatrix) of 21 (respectively, (21, V)J. 
(ii) 	SC C VarC for every class C of algebras or matrices. 
Suppose 21 = (A,oi,... ,on) and 25 = (£?,oi,... ,on) are similar algebras. 
The direct product of 21 and 25 is the algebra 
in which the operations 01,... ,on are defined component-wise, i.e., if Ok is an 
ra-ary operation, a\,..., am £ A and 61,. • •, bm £ B then 
0fc((&l> ^l) » • • • > (flmi bm)) = (Ofc(tti, • • • , #771)5 °k{p1> • • ■ » ^m)) • 
In particular, if 21 and 25 are pseudo-Boolean algebras then the zero element 
in 21 x 25 is _L = (_L, _L). It should be clear from the definition that, for every 
pseudo-Boolean or modal algebras 21 and 25 and every formula </?, 21 x 25 |= tp iff 
211= (p and 25 \= ip. 
In the same way one can define the direct product 2li x ... x 2ln of similar 
algebras 2li,..., 2ln. More generally, by observing that any n-tuple (x\,..., xn) £ 
XiX ... x Xn may be interpreted as the function / : {1,..., n} —> UILi ^ suc^ 
that f(i) = Xi € Xi, for every i = 1,..., n, we can extend the definition of direct 
product to arbitrary families of algebras. 
Given a family {21* = (A*, cq,..., on) : i e 7} of algebras, the direct product 
of {21* : i € 1} is the algebra 
in which Eke/ Ai is the set of all functions / from I into U*eJ such that 
f(i) e At and ofc(/i,..., /m) is a function g e Y[iei A defined by 
for every /1,..., /m G Hi€I Ai and every i £ I. 
Example 7.60 Let {& : i £ 1} be a family of modal (or intuitionistic) frames. 
We invite the reader to show that (X^€/a?i)+ is isomorphic to (f°r 
details see Section 8.5). 
21 x 25 = (A x B,oi,... ,on) 
g(i) — 0fc(/i(z), • • •, fm{i)) £ Ai, 

OPERATIONS ON ALGEBRAS AND MATRICES 
221 
The direct product of a family of modal matrices {(21*, Vi) : i 6 1} is the 
matrix l\ieI = <21, V) in which 21 = and V = fl^/ ^ (the 
reader should check that V is a filter in 21; see also Exercise 7.12). 
For a class C of algebras (or matrices), denote by PC the class of all possible 
direct products of C’s subclasses. Then we clearly have 
Proposition 7.61 (i) If a formula p> is valid in every algebra (or matrix) in 
some family C then ip is valid in the direct product of C. 
(ii) 	PC C VarC for every class C of algebras or matrices. 
The third operation we need—the formation of homomorphic images—was 
introduced in Section 7.1. If / is a homomorphism of 21 = (A, oi,..., on) in 
05 = ... ,on) then the set f(A) is clearly closed under the operations in 
05 and so (/(A),oi,... ,on) is a subalgebra of 05. We call it the homomorphic 
image of 21 (under the homomorphism /) and denote it by /(2l); 21 is called an 
inverse homomorphic image of /(21). If C is a class of algebras then HC is the 
class of all homomorphic images of algebras in C. Since every homomorphism 
preserves the unit element of pseudo-Boolean algebras, we have 
Proposition 7.62 (i) If a formula p> is valid in a pseudo-Boolean or modal 
algebra 21 then tp is valid in every homomorphic image of 21. 
(ii) HC C VarC for every class C of algebras. 
Example 7.63 Suppose 0 = (V, S) is a generated subframe of a modal frame 
S = (W,R). We invite the reader to prove that the map / from 2W onto 2V 
defined by f(X) = X fi V, for X C W, is a homomorphism of #+ onto 0+ (for 
details consult Section 8.5). 
The following observation provides us with another important example of 
homomorphism. Let L be a superintuitionistic or normal modal logic and 21l its 
Tarski-Lindenbaum algebra. Suppose also that 21 is an algebra for L generated 
by a set X such that \X\ < |Var£|. Then any map / from {||p||l ' P € VarC} 
onto X can be extended inductively to a homomorphism of 21l onto 21 by taking, 
for all formulas <p and 
/(IMU © Ml) = f(Ml) © /(IMil), for © € {A, V, ->}, 
/(□MU) = □/(IMU), /(IWU) = JL- 
Remark The reader may (and should) wonder now, where it was used that 21l 
and 21 belong to the same variety (i.e., validate the same formulas). Why could 
not we define such a map, say, from 21^1 onto 2lint? 
The problem here is that in this case / is not well-defined because it depends 
now on the choice of p> and ^ in the equivalence classes |MIl and H^Hl- Indeed, 
we have \\p —> p\\c\ = \\p V -^Hcl but on the other hand f(\\p —> p||ci) = 
Up -* plllnt differs from /(||p V ->p||ci) = ||p V ->p||int. The assumption that 
21 \= L makes / well-defined. For if \\p\\L = \\iP\\l then <p e L and hence 
21 |= ip «-> -0; so if pi,... ,pn are all the variables in ip and ^ and f(\\pi\\L) = 

222 
ALGEBRAIC SEMANTICS 
(i = 1,..., n) then <p(ai,..., an) = ^(ai,..., an) in 21, from which we obtain 
/(IMIl) = /(Ml). 
An algebra 21 in a variety V is said to be a free algebra in V of rank x if 21 is 
generated by a set X of cardinality x and every map of X into an algebra 23 e V 
can be extended to a homomorphism of 21 in 23. The Tarski-Lindenbaum algebra 
21l for L = LogV is a free algebra in V of rank |Var£|. Now we generalize the 
Tarski-Lindenbaum construction to produce a free algebra in V of an arbitrary 
given rank. 
Let X be an arbitrary set. Define a set ForX—the set of “formulas” or 
words over the set of “variables” or letters X—as the smallest set to contain 
X, J_ and such that with every words x and y it contains also the words x A y, 
x V y, x —> y and Ox. (Of course in the intuitionistic case □ should be omitted.) 
The fact that every letter occurring in a word <p e ForX is contained in a set 
{xi,..., xn} C X is denoted by (p(x\,... ,xn). Two words <p(xi,... ,xn) and 
^(xi,,xn) are called equivalent in a superintuitionistic or normal modal logic 
L if <p(pu ... ,pn) <-> V>(pi, • • • ,Pn) € L, where tp(plf... ,pn) and ip(plt... ,pn) 
are obtained from <p(xi,... ,x„) and rp(xi,....xn) by replacing xt with (real) 
variables pi. The class of all words that are equivalent to a word ip in L is 
denoted by \\(p\\l- Now we can define operations A, V, —>, _L and □ on ||ForX||L = 
{\\<p\\l : G ForX} in exactly the same way as in the proof of Theorem 7.2. 
The resulting algebra will be denoted by 21l(X) or even 21 l{x), where k — |X|, 
since we consider algebras up to isomorphism. 
The apparent similarity between 21l(X) and the Tarski-Lindenbaum algebra 
for L provides us with the following theorems whose proofs are left to the reader 
as an easy exercise. 
Theorem 7.64 (i) For every normal modal or si-logic L and every formula (p 
with < x variableSj 
ipe L ijff 2lL(x) |= <p. 
(ii) 21 l(x) is a free algebra in VarL of rank x. 
Theorem 7.65 Suppose L G NExtK, V e ExtL and (p is a formula with < x 
variables. Then 
<peLiff( »lM,V)|=¥> 
where V is the filter in 21 l(x) containing all the elements in 21 l(^) generated 
by words that are equivalent to T in Lf. 
We shall study the constitution of free algebras of finite rank in varieties of 
pseudo-Boolean and modal algebras—their relational counterparts, to be more 
exact—in Section 8.7. Here we consider only one: 
Example 7.66 Let us construct the algebra 2lint(l)- To this end we require the 
following sequence of formulas nfi1i< a;, in one variable: 
nfw = T, nfo = _L, nfl = p, nf2 = ->p, 

OPERATIONS ON ALGEBRAS AND MATRICES 
223 
n/2n+3 — 'H'f 2n+l V n/2n+2> nf 2n+4 ~ nf 2n+3 ~* n/2n+l* 
These formulas, called the Nishimura formulas, are ascribed to the elements 
of the pseudo-Boolean algebra in Fig. 7.2 (a), known as the Rieger-Nishimura 
lattice. And this is no accident. If we define a valuation 03 in the algebra so that 
03(p) be the element marked by nfx = p, then clearly 03(nfi) is the element 
marked by n/i? for every i <u). Moreover, the reader can readily check that for 
any O E {—>, A, V} and any z,j, k <u), 
03(n/i O nf j) = 03(nfk) iff {nfi O nfj) <-> nfk E Int. 
For instance, we have 
^(n/2n+2 -> n/2n+l) = ^(nf2n+4) 
and 
(n/2n+2 —* n/2n+l) n/2n+4 ^ I*1*, 
^(n/2n+3 A nf2n+i) = ^(nf2n+l) 
and 
(«/2n+3 A nf2n+4) «"► «/2n+l € Int. 
A conclusion from this observation may be formulated as 
Theorem 7.67 (i) Every formula in one variable is equivalent in Int to one of 
the Nishimura formulas. 
(ii) Ifi^j then nf{ nfj Int. 
(iii) Olint(l) is isomorphic to the pseudo-Boolean algebra in Fig. 7.2 (a). 
(iv) There are countably many si-logics axiomatizable by formulas in one 
variable. 
Before we extend the notion of homomorphism to modal matrices, let us 
consider a connection between homomorphisms of pseudo-Boolean and modal 
algebras and their filters. 
Theorem 7.68 (i) Let f be a homomorphism of a pseudo-Boolean algebra 21 in 
03 and V a filter in 03. Then the set /_1(V) = {x : f(x) E V} is a filter in 21. 
If in addition V is prime then /_1(V) is also prime. 
(ii) Suppose f is a homomorphism of a pseudo-Boolean or modal algebra 21 
onto 03. Then for every formula <p, 
iff 
Proof Exercise. □ 
Say that a filter V in a modal algebra 21 is normal if x E V implies Dx E V, 
for every element x in 21. 

224 
ALGEBRAIC SEMANTICS 
Proposition 7.69 If f is a homomorphism of a modal algebra 21 m 23 then 
/_1(T) is a normal filter in 21. 
Proof Suppose x € f~1(T), i.e., f(x) = T. Then /(Ox) = D/(x) = DT = T 
and so Dx € /-1(T). □ 
Let V be a filter (normal filter) in a pseudo-Boolean (respectively, modal) 
algebra 21. Define a relation =v in 21 by taking 
x =v y iff x <r-> y G V. 
It is not hard to see that =v is an equivalence relation in 21. Besides, the relation 
=v possesses one more important property. 
An equivalence relation ~ in an algebra 21 = (A, oi,..., om) is said to be a 
congruence if, for every n-ary operation o* and every xi,..., xn, ..., yn in A, 
Xi ~yi,...,x„ ~t/n imply Oi(xi,...,x„) ~ 0,(2/!,..., t/n). 
Theorem 7.70 Suppose that V is a filter (normal filter) in a pseudo-Boolean 
(modal) algebra 21. Then the relation =v is a congruence in 21. 
Proof Let © € {A, V, —>}, x\ =v yi and X2 =v 2/2- Since the identities 
(x <-> y) —> (z © x <-> z © y) = T, (x <-> y) —> (x © z y © z) = T 
hold in every pseudo-Boolean algebra, by the definition of filter we then obtain 
£i©X2 =v 2/i 0^2 =v 2/i02/2 and so, by the transitivity of =v, xi©x2 =v 2/i02/2- 
If 21 is modal then the identity D(x <-> y) —> (Dx <-> Dy) = T is true in it. 
And since V is normal, we then have Dx =v n2/ whenever x =v 2/- □ 
Theorem 7.70 is an algebraic counterpart of the equivalent replacement 
theorem, which was used essentially in the proof of Theorem 7.2. We give now an 
algebraic analog of that proof. 
Let 21 be a pseudo-Boolean (modal) algebra with a universe A and V a 
(normal) filter in 21. Denote by ||x||v the equivalence class (with respect to =v) 
generated by an element x in 21, i.e., \\x\\^ = {y G A : x =v 2/}? and define on 
the set ||A||v = {||x||v : x € A} of these classes operations A, V, —J_, □ by 
taking, for every x, y € A, 
\\X\W O II2/IIv = I|z O 2/11V) for O G {A, V, ->}, 
JL = ||±||v, DIMIv = ||n^l|v- 
Since =v is a congruence, this definition does not depend on the choice of 
representatives x and y in the classes ||x||v and ||2/||v- The resulting algebra 
(||A||v, A, V, —J_) (respectively, (|| A||v, A, V, —_L, □)) is called the quotient 
algebra of 21 with respect to the filter V and denoted by 21/V. 

OPERATIONS ON ALGEBRAS AND MATRICES 
225 
Theorem 7.71 (i) Suppose f is a homomorphism of a pseudo-Boolean or modal 
algebra 21 onto 23 and V = /-1(T). Then the map g defined by 
9{f{x)) = |M|v 
is an isomorphism o/23 onto 21/V. 
(ii) Suppose V is a (normal) filter in a pseudo-Boolean (modal) algebra 21. 
Then the map f defined by 
/(*) = IMIv 
is a homomorphism of 21 onto 21/V with /“1(T) = V. 
Proof Exercise. □ 
Corollary 7.72 There are countably many 1-generated algebras in the variety 
of pseudo-Boolean algebras. 
Proof Follows from Theorems 7.71, 7.67 and the fact that all the filters in 
2lint(l) are principal. □ 
We use the developed technique to characterize algebraically the consequence 
relations in modal and si-logics. 
Theorem 7.73 (i) Let L G NExtK. Then T hl ip iff for any 21 G VarL, any 
ultrafilter V and any valuation 23 in 21, 23(y>) G V whenever 23(,0) G V for all 
^GT. 
(ii) Let L G ExtK. Then T )rL iff for any (21, Vo) G VarL, any ultrafilter 
VO Vo and any valuation 23 in 21, 23(</?) G V whenever 23(,0) G V for all xjj G T. 
(iii) Le£ L G NExtK. Then T \r*L (both MP and RN are allowed) iff for 
any 21 G VarL and any valuation 23 in 21, 23(</?) = T whenever 23(,0) = T /or all 
\l> g r. 
(iv) Le£ L g Extint. Then T \~l <p iff for any 21 G VarL and any valuation 
23 in 21, 23(</>) = T whenever 23(,0) = T /or all G T. 
Proof (i) The implication (=*>) follows from the definition of filter. To prove the 
converse, suppose T\fnp and consider the Tarski-Lindenbaum algebra 21l with 
the standard valuation 23l- Let V' be the filter generated by (23l('0) : ^ £ r}. 
Clearly, 23l(<p) i V'. By Theorem 7.41, there is a prime filter (= ultrafilter) V 
in 21l such that V' C V and 23l(<p) i V, which is a contradiction. 
(ii) is proved analogously to (i). 
(iii) Again (=*>) is clear. To prove (4=), assume T\f*L(p and consider once more 
21l with 23l- Let V be the smallest normal filter containing (23l('0) : ^ £ L}. 
Then 23l(<p) V, for otherwise we would have T \~*L g>. Now take the algebra 
21 = 21l/V. By Theorem 7.71 and Proposition 7.62, we then have a valuation 
23 in 21 G VarL such that 23(xjj) = T for all ^ G T and 23(<p) ^ T, which is a 
contradiction. 
(iv) is proved in the same way as (iii). □ 
A map / is called a homomorphism of a modal matrix (2li, Vi) in a matrix 
(2l2> V2) if / is a homomorphism of 2li in 2I2 and Vi = /_1(V2). If / is a 

226 
ALGEBRAIC SEMANTICS 
surjection, (2l2, V2) is said to be a homomorphic image of (2li, Vi). For a class C 
of matrices, denote by HC and H~lC the classes of all homomorphic images and 
inverse homomorphic images of matrices in C, respectively. As an easy exercise 
we invite the reader to prove the following: 
Proposition 7.74 (i) 7/(2l2, V2) is a homomorphic image o/(2li, Vi) then, for 
every formula ip, 
(^i,V1)h^^(2l2,V2)h^ 
and so 
Log (»i, Vi) = Log (02, V2). 
(ii) HC C VarC, H_1C C VarC for every class C of matrices. 
As follows from this theorem, the main difference between homomorphisms 
of matrices and algebras is that forming a homomorphic image of a matrix does 
not change the set of formulas valid in it, whereas for algebras this is not so. 
If / is a homomorphism of a matrix (21, V) then V' = /_1(T) is a normal 
filter contained in V, and the homomorphic image of (21, V) under / can be 
represented as 
(21, V) /V' = (2l/V',V/V') 
where V/V' = {||x||v' : x £ V}. A matrix of this form is called the quotient 
matrix of (21, V) with respect to the normal filter V'. A matrix (21, V) is said to 
be reduced if {T} is the only normal filter contained in V. 
Theorem T.T5 Every matrix is an inverse homomorphic image of some reduced 
matrix. 
Proof We require two lemmas. 
Lemma 7.76 The set of normal filters in a modal algebra 21 is a complete 
sublattice of the lattice of filters in 21. 
Proof The intersection of any family {V* : i £ 1} of normal filters is clearly a 
normal filter. We show that \/ieI{^i : i G 1} is also a normal filter. 
Let a £ : ^ £ /}• Then there are a\ £ V^,... ,an £ V*n, for some 
{zi,..., in} C J, such that a\ A ... A an < a and so Dai A ... A Dan < Da. 
Since all filters V* are normal, we have Dai £ V^,..., Dan £ V*n, from which 
□a £ ® ^ ^ 
Lemma 7.77 An (inverse) homomorphic image of a normal filter is also a 
normal filter. 
Proof Let / be a homomorphism of 21 onto 23, V a normal filter in 23 and 
show that /_1(V) is a normal filter in 21. If a £ /_1(V) then f(a) £ V and so 
□ /(a) = f(Da) £ V, from which Da £ /_1(V). 
Suppose now that V is a normal filter in 21 and b £ /(V), i.e., b = f(a) for 
some a £ V. Since Da £ V, we then have f(Da) = Df(a) = □& £ /(V). □ 

INTERNAL CHARACTERIZATION OF VARIETIES 
227 
We are in a position now to prove Theorem 7.75. Let (21, V) be a modal matrix 
and V' a maximal (with respect to C) normal filter contained in V, which exists 
by Zorn’s Lemma and Lemma 7.76. By Theorem 7.71 (ii), (2l/V',V/V') is a 
homomorphic image of (21, V) and by Lemma 7.77, the latter is reduced. □ 
Thus, homomorphisms of matrices as compared with homomorphisms of 
algebras are in a sense deficient. For example, every homomorphism between reduced 
matrices is an embedding. To compensate this deficiency, we introduce one more 
matrix operation. 
Say that a matrix (21, V') is an extension of a matrix (21, V) if V C V'. 
Denote by EC the class of all extensions of matrices in a class C. Immediately 
from this definition we obtain 
Proposition 7.78 EC C VarC for every class C of matrices. 
7.8 	Internal characterization of varieties 
By an internal characterization of a variety V of algebras or matrices we mean 
such a representation of V which does not involve identities, characterizing 
varieties externally, but uses only purely algebraic tools such as various kinds of 
operations on algebras and matrices. 
The following two results are well known in universal algebra under the names 
“Birkhoff’s theorem” and “Tarski’s theorem”; their proofs can be found in any 
good textbook on universal algebra, say (Gratzer 1979). Although we will not 
prove them here, the reader can easily reconstruct the proofs by himself, 
consulting the proofs of similar theorems for varieties of matrices. 
Theorem 7.79. (Birkhoff’s theorem) A non-empty class C of algebras is a 
variety iff SC C C, PC C C, HC C C. 
Theorem 7.80. (Tarski’s theorem) For every non-empty class C of algebras, 
VarC = HSPC. 
The next result may also me called Birkhoff’s Theorem for varieties of 
matrices. 
Theorem 7.81 A non-empty class C of modal matrices is a variety iff SC C C, 
PC CC, HCC C, H_1C CC, ECC C. 
Proof (=>) follows from Propositions 7.59 (ii), 7.61 (ii), 7.74 (ii) and 7.78, 
because in this case VarC = C. 
(<=) We need to show that if (21, V) € VarC then (21, V) € C. So suppose a 
matrix (21, V) is in VarC. 
Take any set I such that \I\ = max{|2l|, K0}. Let X be the class of all matrices 
in C of cardinality < \I\. Since C is non-empty and closed under the formation 
of submatrices, it contains a O-generated matrix, which clearly is countable. 
Therefore, X ^ 0. 
Let ^21, be a matrix in X and / a map from I into 21. Denote by (21/, V/) 
the submatrix of (21, V) generated by /(/). Since X is closed under the formation 

228 
ALGEBRAIC SEMANTICS 
of submatrices, (21/, V/) £ X and /(/) is a set of 2l/’s generators. Suppose now 
that T is the set of all maps as defined above for all ^21, £ X and consider 
the direct product 
(* v) = <»/.*/>€ PS* CPSC. (7.2) 
/€*• 
For every z £ /, a* = {/(z) : / £ T} is an element in 21 and the set of all 
these elements characterizes LogC in the sense that if <p(pi,... ,pn) is a formula 
and ^(oij,..., ain) £ V, for some set {zi,..., zn} C J, then </? £ LogC. Indeed, 
suppose otherwise, i.e., there is a matrix (21', V') £ C such that ... ,6n) i 
V', for some elements &i,..., bn in 21'. Take the submatrix (21", V") of (21', V') 
generated by &i,..., bn. Since this submatrix is finitely generated, it is countable 
and so belongs to X\ besides, we have (21", V") ^ </>• Let g be a map in T 
such that g(ii) = b\,... ,g{in) = bn. Then (21",V") = (2lp,Vp) is a factor 
in the product ^21, V^. By the definition of direct product, ^(a^,... , a^) = 
M/(ii)»---»/(*n)) : / eT} and since <p($(ii),... ,£(in)) = <p(&i,... i Vp, 
we have ,..., ain) ^ V, which is a contradiction. 
Let us consider the algebra 21k CO- By Theorem 7.64 (ii), 21 is a homomorphic 
image of 21k (0 under some homomorphism h and so the matrix (21, V) is a 
homomorphic image of (21k(0> /i“1(V)), i.e., 
<a,v)€H{(aK(/U-1(V)>}. (7.3) 
We show now that (2lK(/), h_1(V)) € EH-1S{(a, V^}. 
Put g(i) = a*, for z £ /, and extend p to a homomorphism of 21k(0 onto a 
subalgebra 21' of 21 generated by the set {a* : z £ /}, i.e., for every x and y in 
21rCO, wo put 
g(x Qy) = g(x) © y(y), for © € (A, V, -»}, 
g(-L) = -L, y(Da;) = □y(i). 
Denote by V' the intersection of V with the universe of 21' and show that 
Let a £ g 1(V'). Then there are zi,... ,zn £ I and a formula ... ,pn) 
such that a = </?(zi,... ,zn) and 
g{a) = y(^(ii,..., i„)) = <p(g(h), ■ ■ ■ ,g(in)) = <p(ai,, ■ • • >o*J e V' c V. 
As was proved above, this means that <p £ LogC. Since (21, V) £ VarC, we have 
(21, V) |= (p and so h(a) = ..., h(in)) £ V, i.e., a £ /i-1(V). 

EXERCISES 
229 
Thus, we have shown that the matrix (21k(7), h *(V)) is an extension of 
It follows that 
(2lK(/)^_1(V)> € E{(2lK(/),p-1(V/)>} C 
C EH-1 {(21', V')} C EH_1S{(a, v)}. (7.4) 
Now, putting together (7.2), (7.3) and (7.4), we finally obtain 
(21, V) € HEH_1SPSC C C. 
□ 
Thus, given a non-empty class C of matrices, we can construct the variety 
VarC by taking the closure of C under the operators S, P, H, H-1, E. Moreover, 
as a consequence of the proof above we obtain 
Corollary 7.82 For every non-empty class C of modal matrices, 
Var C = HEH_1SPSC. 
We can even improve the latter equality by observing that PSC C SPC, for 
every class C of matrices (prove the inclusion by yourself). The following result 
may be called Tarski’s Theorem for varieties of matrices. 
Theorem 7.83 For every non-empty class C of matrices, 
Var C = HEH-1SPC. 
Proof By Corollary 7.82, it suffices to establish the equality HEH-1SPC = 
HEH-1SPSC. The inclusion C is trivial because C C SC. And the inclusion 
PSC C SPC gives us HEH-1SPSC C HEH-1SSPC = HEH-1SPC. □ 
7.9 	Exercises 
Exercise 7.1 Prove that all non-degenerate matrices for S have infinite sets of 
distinguished elements. (Hint: show that in such matrices T, OT,..., OnT,... 
belong to the set of distinguished elements.) 
Exercise 7.2 Show that the quasi-identity 
</>l = ^1 A ... A ipm = —+ ip = ifc 
is true in the Tarski-Lindenbaum algebra 21 l iff the rule 
<P 1 ^ 
is admissible in L. 

230 
ALGEBRAIC SEMANTICS 
Exercise 7.3 Show that a lattice is distributive iff one of the laws of distribu- 
tivity is true in it. 
Exercise 7.4 A filter V is called critical in a pseudo-Boolean algebra 21 if there 
is an element a in 21 such that a ^ V, but a e V' for every filter V' D V. Show 
that a principal filter is prime iff it is critical. 
Exercise 7.5 Prove that every finite pseudo-Boolean algebra 21 is isomorphic 
to its bidual (21+)+. 
Exercise 7.6 Prove that every finite intuitionistic frame # is isomorphic to its 
bidual (£+)+. 
Exercise 7.7 Show that the prime elements in #+ are exactly the rooted 
generated subframes of #. 
Exercise 7.8 Show that an intuitionistic Kripke frame # is rooted iff #+ 
contains a second greatest element, i.e., an element a ^ T such that b < a, for every 
b in different from T. 
Exercise 7.9 Show that a modal Kripke frame # is rooted iff there is an element 
a / T in #+ (called an opremum) such that, for every b in Sr+ different from T, 
there exists n < u) for which Dnb < a. 
Exercise 7.10 For a class C of algebras (or matrices), prove that VarC is the 
smallest variety to contain C and that it is the intersection of all varieties 
containing C. 
Exercise 7.11 Let (21, V) be a modal matrix and 23 a subalgebra of 21. Prove 
that the intersection of V with the universe of 23 is a filter in 23. 
Exercise 7.12 Show that if Vi and V2 are prime filters in pseudo-Boolean 
algebras 2li and 212, respectively, then Vi x V2 is a prime filter in 2li x 2I2. 
Exercise 7.13 Prove the converse of Proposition 7.61 (i). 
Exercise 7.14 Prove that the variety VarL of every normal logic L such that 
S4 C L C Grz 0 bws has a continuum of 1-generated algebras. 
Exercise 7.15 Show that if a modal logic L does not contain tran, for any 
n < u, then 21l(1) is infinite. 
Exercise 7.16 Show that a modal algebra 21 is an S4-algebra iff for every 
element x in 21, Dx < x and DDx = Dx. 
Exercise 7.17 Show that a filter V in a Boolean algebra 21 is an ultrafilter iff 
21/V is the two-element Boolean algebra. 
Exercise 7.18 Suppose that 21 = (A, A, V) is a distributive lattice and B, C are 
non-empty subsets of A such that 61 A... A bn ^ c, for any b\,..., bn e B, c e C, 
and for all ci, C2 G C there is c e C for which c\ V C2 < c. Prove that there exists 
a prime filter V in 21 such that B C V and C C1 V = 0. 

EXERCISES 
231 
Exercise 7.19 Give an example of a distributive lattice that is not a pseudo- 
Boolean algebra. 
Exercise 7.20 Show that a filter (ideal) in a pseudo-Boolean algebra is 
generated by a finite set iff it is principal. 
Exercise 7.21 Show that condition (4) in the formulation of Theorem 7.10 can 
be replaced by a finite list of identities. 
Exercise 7.22 Say that an identity is derivable from a set of identities if it 
can be obtained starting from those identities and p = p (as axioms) using the 
following inference rules: substitution of a term instead of a variable and 
v = i> <p = ^ = x v = *P 
*P = p' p = x x = xr 
where x! is the result of replacing (some occurrences of) p in x by xp. Let T be 
any set of identities. Show that p = xp is derivable from F iff p = xp is true in 
every algebra in which all identities in F are true. 
Exercise 7.23 Call a modal or pseudo-Boolean algebra 21 subdirectly irreducible 
if it contains an element a ^ T such that h(a) = T(= /i(T)), for every non-trivial 
(i.e., different from an isomorphism) homomorphism h from 21. Prove that 
(i) 21 is subdirectly irreducible iff among its non-trivial (i.e., different from 
{T}) (normal in the modal case) filters there exists a smallest one; 
(ii) a finite algebra is subdirectly irreducible iff the frame $ is rooted but 
(iii) for infinite algebras this does not hold; generalize (ii) to infinite algebras 
(see Exercise 7.9). 
Exercise 7.24 (Birkhoff’s theorem on subdirect irreducibles) Say that 
an algebra 25 is a subdirect product of algebras 2b, i e /, if there is a 
homomorphic embedding / of 25 into Y\ieI 21 i such that if 7r^, j e /, are the natural 
projections of Hie/ 2b onto 21j then TXj o / is a surjection. Prove that 
(i) every algebra can be represented as a subdirect product of some subdirect 
irreducible algebras; 
(ii) every variety of modal algebras is generated by its subdirectly irreducibles. 
Exercise 7.25 (Los’ theorem for algebras) Let 2b, i € /, be a family of 
modal algebras and V an ultrafilter in the Boolean algebra (27, D, U, D, 0, ) (an 
ultrafilter over I for short). Form an algebra 25 = (J3, A, V, —>, _L, □) by taking 
B = {||:r|| : X € where INI = {2/ € ni€iAi : : = 2/W} e V}, 
and 
INI © Ibll = ||z©y|| for © € {A, V, —>}, ± = H-L-ll, 0||a:|| = jjOa:||. 
25 is called the ultraproduct of the family {2b : i E 1} over the ultrafilter V 
and denoted by • Prove that for every first order sentence (p in the 
language with the functional symbols A, V, —_L, □ and the predicate =, 

232 
ALGEBRAIC SEMANTICS 
JI^/V h <t> iff {* : a* N 0} 6 V. 
iei 
Exercise 7.26 (Los’ theorem for frames) Let #* = (W*,#*), i G J, be a 
family of frames and V an ultrafilter over I. Form a frame # = (W,R) by taking 
w = {||x|| : x e riig/ W<}» where ||x|| = {?/ 6 n»<=/ wi'■ {*'■ *(*) = S/(*)} <= V}, 
and 
IMI^IMI iff {i: x{i)Riy{i)} € V. 
$ is called the ultraproduct of the family {#* : i G 1} over V and denoted by 
ni€/ fo/V. Prove that for every first order sentence </> in the language with the 
predicates R and =, 
i€J 
Exercise 7.27 (Jonsson’s (1967) lemma) Prove that if 21 is a subdirectly 
irreducible modal algebra in VarC then 21 G HSPyC, where P\jC is the class of 
ultraproducts of algebras in C. 
Exercise 7.28 (Blok’s (1980a) lemma) Let {21* : i e 1} be a family of modal 
algebras and, for i e /, = (W*,#*) a frame such that 21* G S(Sr^_). Prove that 
for any 21 G Pu({^b : * ^ /}) there is J = (W,R) G PuCi^i : i ^ /}) and 
21' G S(Sr+) such that 21 is isomorphic to 21'. Furthermore, if for every i € I and 
w G W*, {w} G 21* then for every w G W, {w} G 21'. 
7.10 	Notes 
Chronologically, the first semantics for non-classical logics was the algebraic one. 
Attempts to generalize the truth-functional semantics for Cl led naturally to 
many-valued tables in which both “truth” and “non-truth” are not necessarily 
unique. Although these tables (whose exterior form resembled of a usual matrix 
of numbers, which probably was the reason to call them logical matrices) were 
first constructed in a rather ad hoc manner mainly to distinguish between, say 
modal systems as in Lewis and Langford (1932) or to define modal logics as in 
Lukasiewicz (1920), shortly they became one of the most important tools for 
studying logics. 
The algebraic semantics for si-logics and extensions of S4 was constructed 
and systematically used by McKinsey (1941), McKinsey and Tarski (1944, 1946, 
1948), Dummett and Lemmon (1959). Lemmon (1966a, 1966b) introduced modal 
algebras for many other modal systems. 
In this chapter we presented only that minimum of results on the algebraic 
semantics which will be required in the sequel. The field of studies in (pseudo-) 
Boolean algebras and Boolean algebras with operators itself is so extensive that 
it is practically impossible to indicate a reasonably short list of references 
covering it comprehensively. The book where the reader can find a good many results 
on pseudo-Boolean and topological Boolean algebras together with references 

NOTES 
233 
to their sources is Rasiowa and Sikorski (1963). The methods of this book were 
extended by Rasiowa (1974) to other types of algebras and the corresponding 
logics. Methodologically, these books reflect the algebraic approach to non-classical 
logics of the mid-1960s: the central problem (from the point of view of 
studying logics rather than an intrinsic algebraic problem) was to establish the finite 
approximability together with an upper bound for the number of elements in 
the minimal refutation algebra or matrix. This approach culminated in Lemmon 
(1966a, 1966b). Its essential component were representation theorems for finite 
algebras (like Theorems 7.30 and 7.47 above) which made it possible to prove 
first the finite approximability of a logic in algebraic terms and them transfer 
it to frames. In particular, we obtain that the properties of approximability by 
finite algebras, finite frames and finite models are equivalent. (That is why we 
prefer the term “finite approximability” rather than the connected with models 
and frames well known notions of the finite model and finite frame property.) 
Our definitions of pseudo-Boolean and modal algebras are somewhat different 
from the standard ones: usually pseudo-Boolean algebras are defined by a small 
set of conditions, for instance those in Theorem 7.10. Our approach here is 
similar to that in Part I where we began with a set of acceptable (for some reasons) 
formulas and then showed that one can select in it a short list of formulas 
(axioms) from which the rest are derived by certain inference rules. A little defect 
(in this sense) of the conditions in Theorem 7.10 is that condition (4) is not an 
identity. However, one can easily replace it with a finite number of identities; see 
Exercise 7.21. This similarity is not only an external one. In fact, starting from 
the finite list of identities mentioned above and p = p all other identities that are 
true in all pseudo-Boolean algebras are derivable using the inference rules given 
in Exercise 7.22; cf. Birkhoff (1935). Note that pseudo-Boolean algebras and Int 
were taken here only as an example. The same holds for L-algebras, where L is 
any si- or normal modal logic. Thus, those logics and the corresponding algebras 
can be considered as part of the so called equational logic and/or its model- 
theoretic counterpart—the theory of varieties of algebras—along with groups, 
rings, lattices and other conventional algebraic objects (see the survey Taylor, 
1979). Many problems concerning our logics (say axiomatizability, 
approximability, decidability, etc.) turn out to be of interest for other algebraic equational 
theories, and as a result a considerable algebraic apparatus for solving them has 
been developed. 
Theorem 7.17 on the finite approximability of si-logics with disjunction free 
extra axioms was proved by McKay (1968). Theorem 7.67 describing the 
construction of 2lint(l) is due to Rieger (1949) and Nishimura (1960). 
The theory of varieties is connected primarily with universal algebras; 
varieties of matrices are not standard objects in it. The problem here is that when 
considering matrices we deal with not the condition of identical equality to a 
distinguished element but the predicate of belonging to a set of distinguished 
elements. Although the notion of variety is easily extended to algebraic systems 
in which we regard as identities not only expressions of the form ip = xjj but 
also P(<pi,... , <pm), where P is a predicate of the language under consideration 

234 
ALGEBRAIC SEMANTICS 
(cf. Mal’cev, 1973), this yields no immediate effect because the set of 
distinguished elements in a matrix (as it was defined in this book) is a filter, i.e., we 
are interested in algebraic systems of the form (A, A, V, —_L, □, V) in which not 
only standard identities (saying that (A, A, V, —_L, □) is an L-algebra, for some 
modal logic L) and conditions of belonging to V hold, but also quasi-identities 
of the form 
</?eVA (</?-> VO £V=m/>£V 
(guaranteeing that V is a filter) must be true. Of course, one could deal with 
quasi-varieties instead of varieties but this does not agree with the fact that we 
do not change the postulated inference rules, and so the lattices of logics under 
consideration are not in general dually isomorphic to lattices of quasi-varieties 
of matrices. 
That it is not hard to modify the algebraic semantics by introducing a rather 
natural concept of variety of matrices was observed independently in several 
papers; cf. for instance Blok and Kohler (1983), Chagrov (1985b), Shum (1985). 
One of the most powerful algebraic tools for investigating nonclassical logics 
is Jonsson’s (1967) lemma (see also Gratzer, 1979), which makes it possible to 
establish in a rather easy way some facts about lattices of logics and the 
constitution of logics and the corresponding varieties of algebras as well. As examples 
we mention here two results which can be obtained as immediate consequences 
of Jonsson’s lemma: 
• every tabular logic has a finite number of extensions, and they are also 
tabular; 
• if two finite subdirectly irreducible algebras determine the same logic then 
they are isomorphic. 
Numerous examples of applications of Jonsson’s lemma to modal logics can be 
found in Blok (1980b). Analogues of Jonsson’s lemma for varieties of matrices 
and algebraic systems were proved by Blok and Kohler (1983) and Shum (1985). 
It is to be noted that in this book we give purely semantical proofs for a number 
of results that were originally proved with the help of Jonsson’s lemma (see for 
instance the proof of Blok’s theorem in Sectibn 10.5). 

8 
RELATIONAL SEMANTICS 
Having solved the completeness problem, the algebraic semantics, introduced in 
the previous chapter, deprives us, however, of that transparent interpretation of 
logical connectives which made it possible to construct models for formulas by 
analyzing step by step their subformulas and adding new points, if necessary. In 
other words, we have lost that thread which connected the structure of formulas 
with the “geometry” of their models. Fortunately, this is not that case when 
“gaining in force we lose in distance”. In this chapter we define a more general 
concept of frame, combining in itself the merits of both algebras and Kripke 
frames. 
8.1 	General frames 
There are two ways leading to the general frames. One of them originates from 
Theorem 5.5 according to which every superintuitionistic and normal modal logic 
L is characterized by some (for instance, canonical) model DJI = (#, 03). If L is 
Kripke incomplete then # L, i.e., there is another model = (#,11) refuting 
some (p e L. So, if we do not want to give up the idea of the Kripke semantics 
entirely and yet have completeness, we should impose some restriction on possible 
valuations in # which would allow us to construct 03 and DJI, but forbid 11 and 
01. Let us denote by P the family of all formula truth-sets in # under 03, i.e., put 
P = {O3(V0 • *l> e ForC (or </> € For.M£)}, 
and call P a set of possible values in #. Then ii(pi) & P for some variable 
Pi E Sub</?. For otherwise with every pi e Sub</?, i = 1,..., n, we can associate 
a formula fa such that 11 (p^ = 03(fa), and then il(</?) = 03(</?s) where s = 
{fa/pi,... ,^n/pn}, whence DJI ^ ips, contrary to ips e L. Thus, if we require 
that the valuation 11 in # should satisfy the condition 
11 (p) e P, for every variable p, 
then 01 = (#, 11) will necessarily be a model for L. 
In fact sets P of possible values in # can be defined without any connection 
with models on #. Indeed, let DJI = (#,03) be a model of MC. Then, as was 
shown in Example 7.57, the algebra (P, fl, U, D, 0, □), where fl and U are the 
set-theoretic intersection and union, and D and □ are defined as in Section 7.5, 
is a modal algebra, a subalgebra of #+ = (2WU, D, 0, □) to be more exact. If 
DJI is an intuitionistic model then (P, n, U, D, 0), with D defined as in Section 7.3, 

236 
RELATIONAL SEMANTICS 
is a pseudo-Boolean algebra which is a subalgebra of = (UpW, n, U, D, 0). So 
we can define a set of possible values in $ simply by taking as P the universe of 
some (modal or pseudo-Boolean) subalgebra of 3r+, in particular the universe of 
3+ itself. Thus, we arrive at the following definitions. 
A modal general frame is a triple 3 = (W, R, P) in which (W, R) is an ordinary 
Kripke frame and P, a set of possible values in is a subset of 2W containing 0 
and closed under fl, U and the operations D and □ which are defined as follows: 
for every X, Y C W, 
XdY = (W-X)UY, 
DX = {xeW: \fyeW (xRy y e X)}. 
It follows from the duality of □ and O that the closure under □ can be replaced 
with the closure under the operation O: 
OX = Xl = {yeW: 3xeXyRx}. 
And since X D 0 = W — X, the set P is also closed under complementation in 
the space W. 
We denote by the algebra (P, fl, U, D, 0, □) and call it the dual of Sr. 
Proposition 8.1 The dual of every modal general frame is a modal algebra. 
Proof Exercise. □ 
An intuitionistic general frame is a triple 3 = (W, P, P) where (W, R) is an 
intuitionistic Kripke frame and P, a set of possible values in is a subset of 
UpW containing 0 and closed under D, U and the following operation D: for 
every X, Y QW, 
X D Y = {x eW : VyeW {xRy A yeX^yeY)} 
= □((w-x)uy). 
3r+, the dual of is the algebra (P, fl, U, D, 0). 
Proposition 8.2 The dual of each intuitionistic general frame is a pseudo- 
Boolean algebra. 
Proof Exercise. □ 
General frames # = (W, P, P) and 0 = (V, 5, Q) are isomorphic (£ = 0 in 
symbols) if there is an isomorphism / of (W, P) onto (V, 5) such that X e P 
iff /(X) £ Q, for every X C W. As before, we do not distinguish between 
isomorphic frames. 
Let $ = (W,P, P) be an intuitionistic (or modal) general frame. A model 
of the language C (respectively, MC) on 3 is a pair VJl = (#, 9J) where 03, a 
valuation in #, is a map from Var£ in P, i.e., 03(p) £ P for every variable p. 
The truth-relation |= in VUl is defined in exactly the same way as in Sections 2.2 

GENERAL FRAMES 
237 
and 3.2 for ordinary Kripke models; as before DO (ip) = {x e W : x \= </?}. Note 
that 2J(_L) = 0 and 9J(T) = W. 
The definitions of truth, validity, countermodel, etc., and the corresponding 
notations, given in Sections 2.2 and 3.2, can be extended to general frames 
without changes. In particular, we say a logic L is characterized (or determined) by 
a class C of general frames if L coincides with the set of formulas that are valid 
in all frames in C. 
It should be clear that semantically there is no big difference between # and 
: every valuation QJ in ^ is also a valuation in and vice versa; the truth-set 
of a formula ip in # under 2J coincides with the value of ip in under 23, in 
particular, # (= ip iff (= ip. 
Given a modal or intuitionistic model DJI = (#, 23) based on a Kripke frame 
$ = (W, R), the general frame <S = (W,R,P) with 
P = (23(</?) : (p € ForMC (or ip e For£)} 
is called the general frame associated with DJI. 
The general frame, associated with the canonical model DJIl = for 
a logic L, is denoted by 73T = (Wl,Rl,Pl)- We will call 7the universal 
(general) frame for L. The canonical (Kripke) frame Sl for L is obtained from 
the universal one by omitting Pj> 
Theorem 8.3 For every superintuitionistic or normal modal logic L, the Tarski- 
Lindenbaum algebra 21l for L is isomorphic to the dual 7#J of the universal 
frame 73T for L, an isomorphism being the map f defined by /(||^||l) = 
for every formula ip. 
Proof Clearly / is a surjection. Suppose that ||</?||l ^ II^IIl* i-e., ip <-► ip ^ L. 
Then 23l(<p) ^ 23for otherwise DJIl (= ip <-► ij), from which ip <-► ip e L. 
Therefore, / is an injection. 
Now we must show that / preserves the operations in 21l- The following 
equalities as well as the similar ones for V and —> are straightforward 
consequences of the definitions of 21 l and DJIl and need no comments: 
/(||-L||l)=®l(-L)=0, 
/(IMIz, a Ml) = fi\\<p A V’IIl) = %l{<P A VO = 
= ®Lfc) n 3JlW>) = /(Ml) n /(Ml), 
/(dMl) = f(\\a<fih) = »£(□¥») = °®l(v) = □/(MU). 
□ 
Remark The only property of 7$l used in the proof above is that DJIl 
characterizes L. So 21 l is isomorphic to the dual of the general frame associated with 
any model characterizing L. 

238 
RELATIONAL SEMANTICS 
Since is a characteristic algebra for L, we immediately obtain the 
following completeness theorem which, of course, is also a direct consequence of 
Theorem 5.5. 
Theorem 8.4 Every consistent normal modal or si-logic L is characterized by 
some class of general frames, for instance, by the single universal general frame 
7#l for L or by the class of all general frames for L. 
The set of formulas which are valid in all general frames in some class C is 
obviously a logic. We will denote it, as before, by LogC or Log# if C = {#}. The 
set of all general frames for L is denoted by FrL. 
Corollary 8.5 (i) For every superintuitionistic or normal modal logic L, 
L = Log7and L = LogFrL. 
(ii) For every intuitionistic or modal general frame #, 
LogS = LogS+. 
Thus, each general frame is an interlacing of the two structures: an ordinary 
Kripke frame and a modal or pseudo-Boolean algebra of subsets of this frame. A 
reasonable compromise is achieved: we retain the Kripke interpretation of logical 
connectives and, due to the introduction of the algebraic component, acquire the 
completeness. 
The following examples will help the reader to develop some intuition in 
dealing with general frames. 
Example 8.6 The simplest modal general frames are the frames of the form 
# = (W,R,2w) in which the set of possible values contains all subsets of W, 
i.e., there are no restrictions on valuations in #. From the semantic point of view, 
such a general frame # does not differ from the Kripke frame k# = (W,R) in the 
sense that the same valuations can be defined in them and the same formulas are 
true in them at each point x E W. All this of course concerns intuitionistic general 
frames # = (W, R, UpW) and their underlying Kripke frames k# = (W, R). 
From now on we shall deal with only general frames which henceforth will 
be called simply frames. The frames of the form # = (W,R,2w) and # = 
(W, R, UpW) will be called Kripke frames and denoted as before by # = (W, R). 
If # = (W,R,P) is a frame then we denote by k# its underlying Kripke 
frame, i.e., k# = (W,R). It should be clear that #+ is a subalgebra of k#+. 
Example 8.7 Another boundary case of intuitionistic frames are frames of the 
form # = {W, R, P) where the set P contains only the two sets: 0 and W. Since 
under every valuation in # each variable is either true at all points in # or true 
nowhere, this frame is semantically equivalent to the single-point frame o, i.e., 
Log# = Cl. Observe that # and o have isomorphic duals, viz., the two-element 
Boolean algebra. 

GENERAL FRAMES 
239 
o 2 
<> 1 
o 0 
(c) 
The same (except the last equality, of course) is true for reflexive modal 
frames. However if {W,R} contains a final irreflexive point, e.g., is of the form 
depicted in Fig. 8.1 (a), then the triple (W, R, {0, W}) is not a modal frame, 
because the set {0, W} is not closed under □: D0 = {a}. We invite the reader to 
prove that there is only one set of possible values in this frame, namely 2W. 
Example 8.8 Let us consider the frame # = (W, R, P) whose underlying 
(transitive) Kripke frame is depicted in Fig. 8.1 (b) and P consists of 0, W, all 
finite sets of natural numbers and complements to them in the space W. Or, in 
other words, P is the union of two sets X and y: the elements of X are all the 
finite sets of natural numbers, while each element in y is the union of a set in X 
and the infinite set {n, n + 1,... ,<j}, for some n < u. The fact that P is closed 
under the Boolean operations is evident and UX e X, for every X e P different 
from W, since if n ^ X then m ^ dAT, for all m such that n < m < u. 
Note by the way that (#, oj) f= Up —> p in spite of the fact that u) is irreflexive. 
Indeed, if u f= Dp and u ^ p under some valuation 53 in # then from the former 
relation we obtain 03(p) = W, contrary to the latter one. Recall however that 
(k$,cj) ^ Dp —i► p, since we may put 0J(p) = W - {(j} ^ P. (We recommend 
the reader to compare this example with Example 5.60.) 
Example 8.9 Let $ = (W, R, P) be the modal frame such that k$ has the 
form as in Fig. 8.1 (c) and P consists of all finite and cofinite (i.e., having finite 
complements) subsets of W. P is clearly closed under D, U and D. As to □, it is 
not hard to see that DAT is either empty or cofinite, for every X C W. 
Now we show that although $ contains an infinite ascending chain, the Grze- 
gorczyk formula grz is valid in 5r. Suppose otherwise. Then, by Example 3.24, 
there is an infinite chain xoRyoRxiRyi... in ^ such that, for some valuation 03, 
{yo5 2/i, • • •} C 03(p) and {a?o, #i, • • •} Q W-03(p). But this is impossible, because 
^3(p) is infinite, has an infinite complement in W and so does not belong to P. 
Let us recall however that, by Proposition 3.48, grz. 
Having constructed the adequate relational semantics for normal modal 
logics, we can extend it to quasi-normal ones simply by adding to general frames 
sets of actual worlds. Indeed, as we know from Section 5.6, every logic L e ExtK 
is characterized by its canonical model (9Jtker l, Dl) with distinguished points in 
the sense that for any e ForM.C, 
r 
I 
(a) 
Fig. 8.1. 

240 
RELATIONAL SEMANTICS 
<p € L iff Dl C OJkerL^)- 
Then, by the definition of the universal general frame 7Sker l for kerL, we have 
ip € L iE.Dl C D3{ip) for every valuation 53 in 7Sker L- So if we regard the points 
in Dl as the only actual worlds in 7SkerL and consider ip to be true in 7SkerL 
if it is true at all actual worlds then the pair (7Sker l,Dl) will characterize L. 
This observation motivates the following definitions. 
A frame with distinguished points is a pair (S, D) such that S = (W, R, P) is 
a (general) frame and D a subset of W whose elements are called distinguished 
points or actual worlds in S- A model with distinguished points based on (S, D) 
is a pair (97t, D), where DJI is a model based on S- (DJl,D) |= ip means, as 
in Section 5.6, that (DJl,x) J= ip for all x € D, and (S, D) |= ip means that 
{DJI, D) |= ip for all {DJI, D) based on (S, D). 
The frame (7SkerL, Dl) is called the universal frame (with distinguished 
points) for L. 
Every frame (S, D) with distinguished points gives rise to the modal matrix 
(S+, D+) where S+ is the dual of S = (W, R, P) and 
D+ = {X eP : DCX} 
is a filter in S+- We call (S+,L>+) the dual of (S,-D). It is clear that (#, .D) is 
semantically equivalent to (Sr+,J9+). 
Theorem 8.10 Tfte Tarski-Lindenbaum matrix (2lkerL> Vl) /or a quasi-normal 
logic L is isomorphic to (7Skerl^l)> an 'Isomorphism being the map f defined 
by /(IMIkerZ,) = Sheer l{p>) /or euen/ formula ip. 
Proof By Theorem 8.3, / is an isomorphism of SlkerL onto 7SkerL- S° we 
must show that /(Vl) = £>£. Suppose ||^||kerL C Vl- Then ip e L, from 
which Dl C 53kerZ,(<£) and so SlkerL(^) € DJ. Conversely, if X € then 
AT = SIker l(v>) for some formula ip, Dl C 53ker l{p>) and so ip e L, \\ip\\ker l € Vl 
and /(IMIkerZ,) = X. □ 
As a consequence of Theorems 7.4 and 8.10 we obtain the following: 
Theorem 8.11 Every consistent logic L € ExtK is characterized by some class 
of frames with distinguished points, for instance, by the single universal frame 
(7Skerl,Dl) for L. 
Since (S, D) |= ip iff (S, {d}) f= ip for every d E D, we derive one more 
completeness result. 
Theorem 8.12 Every consistent logic L € ExtK is characterized by some class 
of frames having a single distinguished point. 
Example 8.13 Let S be the frame constructed in Example 8.8. We show that 
by choosing uj as the single actual world in S', we obtain a frame for S = GL + 
Up —> p. Since S is transitive, irreflexive and Noetherian, kS |= GL, and hence 
S |= GL, in particular, (S,i^) |= GL. It remains to recall that, as was shown in 
Example 8.8, (S,^) |= Up —j► p. So (S,o>) \= Up p and (S,o>) |= S. 

THE STONE AND JONSSON-TARSKI THEOREMS 
241 
8.2 	The Stone and Jonsson-Tarski theorems 
Another way, using which we also come to the general frames, has its starting 
point in the realm of algebra. We have already taken one step along this way, 
having represented (in Sections 7.4 and 7.5) every finite pseudo-Boolean and 
modal algebra as the dual of some finite Kripke frame #. It is impossible 
to extend this result to infinite algebras, witness the following cardinality 
argument: the dual of an infinite modal frame # contains at least a continuum 
of elements, although, as we saw in Section 7.2, the Tarski-Lindenbaum algebra 
for a logic in a denumerable language has only countably many elements. 
This section shows however that every pseudo-Boolean and modal algebra 21 
is isomorphic to the dual of some general frame #, be., to a subalgebra of k&s 
dual. 
As was shown in the previous section, the Tarski-Lindenbaum algebra 21l for 
a (superintuitionistic or normal modal) logic L is isomorphic to the dual 7#^ of 
the universal frame 7for L. So to understand how, given an arbitrary algebra 
21, to construct its relational representation it may be useful to see in more 
detail what the relation between 21^ and 7is. Recall first that the elements 
in 21l are the classes \\<p\\l = {V> : <p ^ ^ E. L}, while the points in 7are 
the maximal L-consistent tableaux (T, A). The set T in such a tableau has the 
following properties: 
• TgT; 
• T is closed under modus ponens, in particular, together with every ip it 
contains the whole class |M|l; 
• ip V -0 G r only if ip 6 T or -0 6 T. 
This means that the set {\\<p\\l : 6 T} is a prime filter in 21l- (Note by 
the way that {|M|l ip £ A} is a prime ideal in 2lj>) And conversely, each 
prime filter V in 21l induces a maximal L-consistent tableau, namely (I\A) 
with T = {ip e For : \\^p\\l £ V}, A = For - T. (Here For is the set of all 
formulas in the language of L.) Thus we can consider points in 73x as prime 
filters in 21l- 
Recall also that for a superintuitionistic L we defined Rl in 7by taking 
tiRLt2 iff Ti C r2, for any = (Ti, Ax) and t2 = (r2,A2) in WL. If Vi, V2 are 
the prime filters in 21l corresponding to t\ and t2, respectively, then 
tiRht2 iff Vi C V2. 
For modal L we defined Rl by taking tiRit2 iff {ip : □</? € ^1} Q F2, which 
means that 
tiRLt2 iff for every \\(p\\L in 2lL, U\\<p\\L e Vi implies \\<p\\L e V2. 
And finally, Pl = {2Jl(^) : ^ € For}. By Theorem 5.4, 2Jl(^) is the set 
{(r, A) G Wl : ip 6 T} or, algebraically, 2Jl(^) ls the set of all prime filters V 
in 2lL containing ||<p||l- 

242 
RELATIONAL SEMANTICS 
Thus we have a method which, given the Tarski-Lindenbaum algebra 21l for 
L, constructs the universal frame 7for L whose dual 7#^ is isomorphic to 
2lL. What if we apply it to an arbitrary pseudo-Boolean or modal algebra? 
In fact this method is a generalization, discovered by Jonsson and Tarski 
(1951), of Stone’s (1937) set-theoretic representation of distributive lattices and 
Boolean algebras which is well-known in lattice theory We present first Stone’s 
construction for distributive lattices and then extend it to pseudo-Boolean and 
modal algebras. 
Suppose 21 = (A, A, V) is a distributive lattice. We shall use the following 
notation and terminology. 1, the Stone space for 21, is the set of all prime 
filters in 21; /a, the Stone isomorphism, is the map from A in 2W* defined by 
/21(a) = {V G : a G V}; 
and Pa, the Stone lattice for 21, is the range of /a, i.e., 
P21 = {/21(a) : aeA}. 
Theorem 8.14. (Stone’s representation) Every distributive lattice 21 is 
isomorphic to (Pa,n,U), a set ring of the Stone space Wa, with /a being an 
isomorphism. 
Proof By the definition, /a is a surjection. Let us show that it is also an 
injection, i.e., /a(a) = f21(b) only if a — b. Suppose a ^ b. Then either a ^ b 
or 6 ^ a. In the former case, by Corollary 7.42, there is a prime filter V in 21 
such that a G V and b £ V, whence /a(a) ^ f21(b). The latter one is considered 
analogously. Thus, /a is a bijection from A onto Pa, and it remains to show that 
/a preserves the lattice operations. 
Suppose that V G /a(a V 6), i.e., a V b G V. Since V is prime, we then have 
either a G V or b G V and so V G /a(a) U /21(b). Conversely, if V G /a(a) U /a(b) 
then either a G V or b G V and so, by Theorem 7.23, aVb G V, i.e., V G /a(aV6). 
Hence /a(a V b) = /a(a) U /*(&). 
Now suppose that V G /a(a A 6), i.e., a A 6 G V. Then a G V, 6 G V and so 
V G /21(a) n /a(&). On the other hand, if V G /a(a) n /a(&) then a G V, 6 G V 
and a A 6 G V, i.e., V G /a(a A 6). Thus, /a(a A 6) = /21(a) Pi/a(6) • □ 
It should be clear that the lattice order < in (Pa, Pi, U) is the ordinary set- 
theoretic inclusion C. 
A pseudo-Boolean algebra 21 = (A, A, V, —_L) is a distributive lattice and as 
such it is isomorphic to the Stone lattice (Pa, Pi, U). Since _L does not belong to 
any prime filter in 21, /a(-L) = 0 and so 0 is the zero element in the Stone lattice 
for 21. By Corollary 7.12, the operation —> is uniquely determined by the lattice 
order C. Now recall that our goal is to represent 21 as a subalgebra of for 
some intuitionistic Kripke frame #. So what we need is to define a partial order 
Pa on Wa such that (i) all sets in Pa would be upward closed with respect to 
Pa and (ii) Pa would be closed under the standard operation D on (Wa,P2t)- 

THE STONE AND JONSSON-TARSKI THEOREMS 
243 
Then £a = (Wa, Pa, Pa) would be an intuitionistic general frame whose dual 
= (Pa? H, U, D, 0) is isomorphic to 21. 
Let us define Pa as is prescribed by our method: 
ViPaV2 iff Vi C V2, for all Vi, V2 6 Wa- 
Lemma 8.15 Every set X G Pa is upward closed in (Wa, Pa)- 
Proof Suppose X = /a(u), for some a G A, V G X and VPaV'. Then a G V, 
VC V' and so V' G /a (a). □ 
Let D be the standard implication in the dual of (Wa, Pa), he., for every 
X,y C Wa 
X D Y = {V G Wa : VV' G Wa (VPaV' AV'gX^V'g y)}. 
Lemma 8.16 Pa is closed under D. 
Proof Let X,Y G Pa, X = /a(a) and y = /a(&), for some a,b € A. We show 
that XdF = /a(& —^► 6) G Pa- 
Suppose V G /a(& —> 6), i.e., a —> 6 G V, VPaV' and V' G X, i.e., a G V'. 
Then V C V', a —► b G V' and so, by the definition of filter, b G V', which means 
that V' G /a(&)- Therefore, V G X D 7. 
Conversely, let V G X D y and show that a —> 6 G V. If 6 G V then clearly 
a —» 6 G V. So suppose that 6 ^ V. Let Va be the filter in 21 generated by the 
set {a} U V. It follows from Theorem 7.24 that 
Va = {x G A : 3z G V z A a < x}. 
We are going to show now that b G Va. Then we shall have z A a < 6, for some 
z G V, whence, by Theorem 7.10, z < a —> b and so a —► b G V. 
Suppose 6 ^ Va. Then, by Theorem 7.41, there is a prime filter V' such that 
Va C V' and b £ V'. But this leads to a contradiction, since VPaV', V' G X 
and so V' G Y, i.e. 6 G V'. □ 
Thus the triple (Wa, Pa, Pa) is an intuitionistic general frame. We call it the 
dual o/2l and denote it by 21+. 
Our observations at the beginning of this section yield 
Theorem 8.17 The dual (21 l)+ of the Tarski-Lindenbaum algebra for a si-logic 
L is isomorphic to the universal frame 73x for L. 
As a consequence of Theorem 8.14, Corollary 7.12 and Lemmas 8.15, 8.16 we 
obtain 
Theorem 8.18. (Stone’s representation) Every pseudo-Boolean algebra 21 
is isomorphic to its bidual (21+)with /a being an isomorphism. 
Corollary 8.19 Every pseudo-Boolean algebra 21 is (isomorphic to) a subalgebra 
of (W%,R<n}+ = («2l+)+. 

244 
RELATIONAL SEMANTICS 
According to Theorem 8.18, every Boolean algebra 21 = (A, A, V, —_L) is 
isomorphic to the dual of the frame 21+ = (Wa, Pa, Pst). Since prime filters in 
Boolean algebras are ultrafilters, Ra is just the identity relation and so D in 21+ 
is defined by 
XDY = {VeWx: V G X -> V G Y} = {W* - X) U Y. 
Thus we obtain the following: 
Theorem 8.20 Every Boolean algebra 21 is isomorphic to (Pa,n,U, 0,0), a set 
field of the Stone space Wa, with /a being an isomorphism. 
Corollary 8.21 Every Boolean algebra 21 is isomorphic to a subalgebra of the 
field (2^, fl, U, 0,0) of all subsets of the Stone space W%. 
Now let us turn to modal algebras. Given such an algebra 
21 = (A, A, V, —_L, □), 
define a relation Pa on Wa as was described at the beginning of the section, i.e., 
for Vi, V2 6 Wa, we put 
ViPaV2 Iff V:r G A (□£ G Vi —► x G V2). 
Lemma 8.22 For every a G A, /a(Da) = □/21(a) where □ in the right-hand 
part is the standard necessity operation in the frame (Wql,Rq1). 
Proof Let V G /a(Oa), i.e., Da G V, and let VPaV'. Then by the definition of 
Pa, a G V', i.e., V' G /21(a). Therefore, V G D/a(a). Conversely, let V G D/a(a), 
i.e., for every V' G W21, VPaV' implies V' G /21(a). Suppose that V ^ /a(Da) 
and consider the set 
X = {x G A : DxG V}. 
Since DT = T G V, X is non-empty. Let [X) be the filter generated by X. 
Then a [X). For otherwise, by Theorem 7.35, x\ A ... A xn < a for some 
£1,..., xn G X, whence Dxi A ... A Uxn < Da and so Da G V, contrary to our 
assumption. By Theorem 7.41, there is an ultrafilter V' such that [X) C V' and 
a ^ V'. But then VR%Vf and so V' G /21(a), i.e., a G V', which is a contradiction. 
□ 
It follows immediately from this lemma that Pa = {/&(&) : a G A} is closed 
under □ in the frame (Wa, P2t)- So (Wa,P2t,Fa) is a modal general frame. We 
call it the dual of 21 and denote it by 21+. Clearly, we have 
Theorem 8.23 The dual (21 l)+ of the Tarski-Lindenbaum algebra for a normal 
modal logic L is isomorphic to the universal frame 7Sl for L. 
Combining together Theorem 8.20 and Lemma 8.22 we obtain 

FROM MODAL TO INTUITIONISTIC FRAMES AND BACK 
245 
Theorem 8.24. (The Jonsson-Tarski representation) Every modal 
algebra 21 is isomorphic to its bidual (2l+)+, with fat being an isomorphism. 
Corollary 8.25 Every modal algebra 21 is (isomorphic to) a subalgebra of the 
algebra (W%i,Rvi)+ = (k21+)+. 
And one more algebraic structure needs a relational representation: we mean 
modal matrices. Suppose that (21, V) is such a matrix. By Corollary 7.40, every 
proper filter in 21 is the intersection of all ultrafilters in 21 containing it. Define 
a set V+ C Wat by taking 
V+ = {V'eWa: V C V'}. 
The general frame (21+, V+) with distinguished points will be called the dual of 
(21, V). 
Theorem 8.26 Every modal matrix (21, V) is isomorphic to ((2l+)+, (V+)+), 
with fai being an isomorphism. 
Proof In view of Theorem 8.24, it suffices to show that fat(V) = (V+)+. This 
is clear if V = A. So suppose that V is a proper filter in 21. If a G V then 
/a(o) = {V'6 Wqi : a 6 V'} D {V' 6 W* : V C V'} 
and so /21(a) G (V+)+. Conversely, if X G (V+)+ then there is a € A such that 
X = /21(a) and V+ C /a(o), i.e., 
(V' G : a G V'} D {V' G W31: VC V'}. 
So a G V, since V = f]{Vf G W% : VC V'}, and /21(a) = X. □ 
Our last result in this section provides a relational characterization of the 
consequence relations in modal and si-logics. It follows immediately from 
Theorem 7.73 and the representation theorems proved above. 
Theorem 8.27 (i) For L G NExtK, T \~L <p iff for any model 971 based on a 
frame for L and any point x in 971, x |= T implies x \= <p. 
(ii) For L e ExtK, TV-up iff for any model (971, D) based on a frame (#, D) 
for L and any point x € D, x \=T implies x f= p. 
(iii) For L G NExtK, T \-*L <p iff for any model 971 based on a frame for L, 
2711= T implies 9711= <p. 
(iv) For L G Extint, T \~l <p iff for any model 971 based on a frame for L, 
2711= T implies 2711= (p. 
8.3 	From modal to intuitionistic frames and back 
So far we have considered modal and intuitionistic frames separately. However, 
as was shown in Section 3.9, every modal Kripke model 971 = (#, 93) based on a 
quasi-ordered frame # induces in a natural way an intuitionistic model, namely 

246 
RELATIONAL SEMANTICS 
the skeleton p9Jt = (p#, pQ3) of 9Jt, such that for any intuitionistic formula <p 
and any point x in #, 
(pOJl,C(x))h^ iff 
where T, the Godel translation, prefixes □ to every subformula of <p. 
The operator p can be easily extended to general frames. Given a modal 
quasi-ordered frame # = we define an intuitionistic frame p# = 
(pW, pR, pP), called the skeleton of #, by taking 
pP={pX: XePAX = BX} = {pX: XeP AX = X]}, 
where pX = {C(x) : x G X}. To verify that p# is really an intuitionistic frame, 
it suffices to observe that, for any upward closed X,Y G P, 
p(X) n p(Y) = p(X n Y), 
p(X)Up(Y) = p(XUY), 
p(X) D p(Y) = p(a(X D Y)). 
(Here D in the left-hand side is intuitionistic and that in the right-hand one is 
Boolean.) 
If DJI = (foQJ) is a model on $ then p9Jl = (pff, pQJ), the skeleton of 9JI, is 
the intuitionistic model with pQJ defined, as before, by 
pQJ(p) = p(QJ(Dp)), for every variable p. 
Using the equations above, one can readily prove the following obvious 
generalization of Lemma 3.81. 
Lemma 8,28. (Skeleton) For every model Wl based on a quasi-ordered frame 
every intuitionistic formula <p and every point x in 
(pm,C(x))\=<p iff (®t,a:)|=T(V) 
and so 
P3\=<P iff $ N Tfa). 
Let us now clarify the algebraic meaning of the operator p. Observe first that 
the operation □ in a quasi-ordered modal frame 'S = {W, R, P) has the following 
properties: for every X, Y C W, 
(11) D(XnF) = nxnny; 
(12) ax c X- 
(13) aax = DX; 
(14) uw = W. 

FROM MODAL TO INTUITIONISTIC FRAMES AND BACK 
247 
A set W with an operation □ on 2W satisfying these four properties is usually 
called a topological space and □ an interior operation in this space. The dual 
operation O, defined by OX = -□ — X (where —X = W - X), is called the 
closure operation in the topological space. That is why the modal algebras 21 = 
(A, A, V, —_L, □) whose box □ satisfies (II)—(14) (in which X, Y, C and W 
should be replaced by a, 6, < and T, respectively) are known as topological 
Boolean (or interior, or closure) algebras. According to Exercise 7.16, a modal 
algebra 21 is a topological Boolean algebra iff 21 |= S4. Borrowing the topology 
terminology, we say that an element a in such an algebra is open if a = Da. 
Proposition 8.29 For every topological Boolean algebra and all open elements 
a and b in it, 
a V b = n(a V b). 
Proof Since a < a V 6, we have a = Ua < D(a V b). Likewise b < n(a V b) and 
so aV6 < □(aVi>). The desired equality follows then from (12). □ 
By the definition, the dual 3r+ of a quasi-ordered frame # is a topological 
Boolean algebra. And conversely we have 
Proposition 8.30 The dual 21+ of a topological Boolean algebra 21 is a quasi- 
ordered frame. 
Proof We must show that the accessibility relation R% in 21+ is reflexive and 
transitive. Let V E W% and Ua E V. By (12), Ua < a and so a E V. Therefore, 
VP&V. Suppose now that V1P21V2P21V3 and Ua E Vi. By (13), UDa E Vi, 
whence DaE V2 and a E V3, which means that V1P21V3. □ 
Given a topological Boolean algebra 21 = (A, A, V, —_L, □), we define an 
algebra p2l = (pA, A, V, —>□, _L) by taking pA = {a E A : a — Da} and 
a —>□ b = D(a —> 6), for any a, b E pA. (By (II) and Proposition 8.29, pA is 
closed under A and V.) p2l is called the algebra of open elements of 21. 
Proposition 8.31 For every quasi-ordered modal frame $ = (W,R,P), (p#)+ 
is isomorphic to p(3r+). So the algebra p2l of open elements of any topological 
Boolean algebra 21 is a pseudo-Boolean one; more exactly, p2l = (p(2l+))+. 
Proof It easy to verify that the function mapping pX to X, for every upward 
closed X E P, is an isomorphism of (p#)+ onto p(3r+). The dual 21+ of a 
topological Boolean algebra 21 is a quasi-ordered frame whose dual, by Theorem 8.24, 
is isomorphic to 21. So p2l = p((2l+)+) = (p(2l+))+. □ 
What is more important, the converse statement, i.e., that each pseudo- 
Boolean algebra (or intuitionistic frame) is an algebra of open elements 
(respectively, a skeleton) of some topological Boolean algebra (quasi-ordered modal 
frame), also holds. We will prove it first for general frames and then transfer, by 
duality, to algebras. 
Given an intuitionistic frame # = (W, R, P), the simplest way of constructing 
a modal frame from it is to take the closure aP of P under the Boolean operations 
H, U and — 

248 
RELATIONAL SEMANTICS 
Lemma 8.32 For every X C W, X is in <tP iff 
X = (-*! u Yi) n... n (~xn u Yn) 
for some X\,Y\,... ,Xn, Yn e P and n > 1. 
Proof (=») By Exercise 1.1, we can represent each X e crP as 
n 
f)(-?7ju...U-^iUV*U...U^) 
i—1 
for some U1-, Vj <G P. Then, taking 
_ f U{ n... n Ulk. if ki > 0 
A< \w ‘ if ki = 0 
and 
v r ^ U... U w. if fci > 0 
y‘ = {« if = 0 
we obtain the representation we need. 
(4=) is trivial. □ 
Now we observe that aP is closed under □ in (W, R) and that P coincides 
with the set of open (= upward closed) sets in crP. More exactly, the following 
lemma holds. 
Lemma 8.33 Suppose X e crP is represented as in Lemma 8.32. Then 
DX = {X1DY1)n...n {Xn DYn)eP c o-p, 
where the operations in the right-hand part of = are intuitionistic. 
Proof By (II), it suffices to verify that for every X, Y € P, 
□ (-XU Y) = XdY. 
We leave this to the reader as an exercise. □ 
Thus, (W,R,<rP) is a partially ordered modal frame; we shall denote it by 
o-S. 
Theorem 8.34 Every intuitionistic frame $ = (W, P, P) is the skeleton of some 
quasi-ordered modal frame. For instance, $ — p&$. 
Proof We must show that paP = P. Suppose X € pcrP. By Lemma 8.33, 
we then have X = DX € P. Thus pcrP C P. The converse inclusion follows 
immediately from the definitions of p and a. □ 

FROM MODAL TO INTUITIONISTIC FRAMES AND BACK 
249 
Notice that if DJI = (#, 93) is an intuitionistic model then aDJl = (a#, 93) is a 
modal model having DJI as its skeleton. So by the skeleton lemma, we have 
(9Jt, x) \= (p iff (aDJl,x) |=T((^), 
for every intuitionistic formula <p and every point x in #. 
Given a pseudo-Boolean algebra 21, we denote by a21 the topological Boolean 
algebra (<t(21+))+. 
Corollary 8.35 Every pseudo-Boolean algebra 21 is isomorphic to the algebra 
of open elements of some topological Boolean algebra. For instance, 21 = p<r2l. 
Proof By Theorem 8.34, 21+ = p<r(2l+) and so, by Theorem 8.18 and 
Proposition 8.31, 21 ^ (2l+)+ “ (po-(2l+))+ “ p((<r(2l+))+). □ 
It is worth noting that if # = (W,R, UpW) is a finite intuitionistic Kripke 
frame then is also a Kripke frame, i.e., cr$ = (W,R,2W). Indeed, by the 
finiteness of #, it suffices to show that {x} e <rUpW for every x € W. But this 
is evident, since {x} = x| Hxj, and xj is the complementation of an upward 
closed set. The latter equality holds of course for infinite frames as well. 
Let us say a point x in a modal frame # = (W, R, P) is an atom if {x} e P. 
If # is intuitionistic then we call x e W an atom if 
W - xj G P and {x} U (W - xj) e P. 
A (modal or intuitionistic) frame J is atomic if every point in J is an atom. It 
should be clear that any finite atomic frame is a Kripke frame. 
The observation above means that if J is an intuitionistic Kripke frame then 
tis atomic. However, for an infinite J, <7$ is not in general a Kripke frame. 
To see this, consider the intuitionistic frame (3 shown in Fig. 8.1 (c). It is not 
hard to check that cr<& is exactly the frame defined in Example 8.9, where we 
observed that a<& \= Grz, while kct<5 ^ Grz. On the other hand, it follows 
from Lemma 8.33 that x is an atom in <7$ only if x is an atom in J. 
The operator a is not the only one which, given an intuitionistic frame #, 
returns a modal frame whose skeleton is isomorphic to J. As an example, we 
define now an infinite class of such operators. 
For Kripke frames J = (W, R) and (5 = (V, 5), we denote by J x 3 the direct 
product of # and 3, i.e., the frame (W xV,RxS) in which the relation Rx S 
is defined component-wise: 
(zi,2/i) (R x S) (x2,2/2) iff xiRx2 and y\Sy2- 
Let 0 < k < u. We will regard k as the set {0,..., k — 1} if k < u and as 
{0,1,...} if k = u. Denote by an operator which, given an intuitionistic frame 
# = (W,R,P), returns a quasi-ordered modal frame = (kW,kR,kP) such 
that 

250 
RELATIONAL SEMANTICS 
oo 
V t2S (oo) 
Fig. 8.2. 
(i) (kW,kR) is the direct product of the fc-point cluster (k,k2) and {W,R) 
(in other words, (kW, kR) is obtained from (W, /?) by replacing its every point 
with a fc-point cluster; see Fig. 8.2); 
(ii) prk$ * ff; 
(iii) I x X e kP, for every / C k and X G <rP. 
For instance, we can take as kP the Boolean closure of the set 
{I x X : iCk, X e aP}. 
To show that kP is closed under □ in (kW,kR), it suffices, by Lemma 8.32 and 
the fact that k xW — I x X = (k — I) xXUkx (W — X), to prove the inclusion 
□ x Xi) e kP for every finite J and every Ii C k, Xi € aP. And this 
follows from the equality 
□ (J (Ii x Xi) = fc x (□ (J{ P| Xi : J' C J, (J It = fc}), 
z€J' 
from which, using Lemma 8.33, we can also derive (ii). 
For a Kripke frame J = (W, R, UpLF) we can, of course, take kP = 2kw and 
then Tk$ = (fcW, fci?, 2fciy). 
8.4 	Descriptive frames 
The relationship between general frames and algebras, which was established in 
Sections 8.1 and 8.2, lacks some symmetry. Indeed, the representation theorems 
assert that every pseudo-Boolean and modal algebra 21 is isomorphic to its bidual 
(21+)+, or in symbols 
21 = (2l+)+. (8.1) 
But on the other hand, Example 8.7 shows that there are non-isomorphic frames 
having isomorphic duals. So the relation 
£=(3+)+ (8.2) 
does not generally hold. 
Those frames J that satisfy (8.2) are called descriptive. Taking into account 
(8.1), we obtain an equivalent definition: a (modal or intuitionistic) frame is 
descriptive iff it is isomorphic to the dual of some (modal or, respectively, pseudo- 
Boolean) algebra. 

DESCRIPTIVE FRAMES 
251 
In this section we give a subtler characterization of descriptive frames. This 
result is important not only from the aesthetic point of view. For, dealing with 
logics in Extint and ExtK, we are interested in finding possibly smaller classes 
of frames which are enough to determine all these logics. 
Theorem 8.36 Every logic in Extint and NExtK is characterized by a class 
of descriptive frames. 
Proof Follows from Theorems 8.17, 8.23 and 8.4. □ 
To characterize the constitution of descriptive frames, let us consider once 
again the universal frames, which are descriptive according to Theorems 8.17 
and 8.23. In Section 5.1 we observed that every canonical model is differentiated, 
tight and compact. Adapting these notions to general frames, we arrive at the 
following definitions. 
A frame # = (W, JR, P) is differentiated if for any x,y e W, 
x = y iff VX eP (xeX ^yeX). 
An intuitionistic # is tight if for any x,y eW, 
xRy iff VX G P (x e X -> y e X). 
Since in an intuitionistic frame $ the relation R is antisymmetric, S' is tight only 
if S is differentiated. 
A modal frame S is tight if for any x,y eW, 
xRy iff \/X eP (xenx ye X) 
or, dually, if 
xRy iff VXeP(yeX->xe XI). 
Those frames that are both differentiated and tight are called refined. Finally, 
a frame S is said to be compact if, for any families X C P and y C P = {W — X : 
XeP}, 
f](X uy) = {i: VXe XW e y (x € X A x e y)} + 0 
whenever p|(X' U yf) ^ 0 f°r finite subfamilies X' C X, yf C y. For modal 
frames, in which together with any X the set P contains its complement —X = 
W — X, this definition is equivalent to the more familiar one: S is compact iff 
every subset X of P with the finite intersection property (i.e., with f] Xf ^ 0 for 
any finite subset X' of X) has non-empty intersection. 
Denote by VT, T, CM., 71, V the classes of all differentiated, tight, 
compact, refined and descriptive frames, respectively. We are going to show that the 
combination of the first three properties is characteristic for descriptive frames, 
i.e., 
V = VPn TnCM. 
But before that let us take a closer look at those properties. 

252 
RELATIONAL SEMANTICS 
o° 
o 1 
o 2 
ouj 
° oj + 1 
(a) 
o 0 
O 1 
o 2 
o° 
O 1 
o 2 
u u + 1 
rtf © 
(b) 
Fig. 8.3. 
. LJ 
0 o 
w + 1 
o 
(C) 
For a frame # = (W, JR, P) and a point x G TF, put 
Px = {XgP: xeX}, Px = {XeP: xeX}. 
If # is modal then clearly we have Px = Px. 
Proposition 8.37 For every frame $ = (W, P, P) and every x G W, Px is a 
prime filter in . 
Proof Exercise. □ 
Proposition 8.38 A frame $ = (W, P, P) zs differentiated iff\ for every x G W, 
npx U Px) = {x}. 
Proof Exercise. □ 
Proposition 8.39 If $ is a differentiated intuitionistic frame then cr$ is also 
differentiated. However, the operator p does not in general preserve differentiate 
edness. 
Proof The former claim follows from the definition. To prove the latter one, 
let us consider the modal frame $ = (W, P, P) whose underlying Kripke frame 
is shown in Fig. 8.3 (a) and P = Xf U Xc U U Xu+i where 
• Xf contains all finite sets of natural numbers; 
• Xc contains all the complements (in the space W) of the sets in Ay; 
• consists of all sets of the form {u;}U{2n : n > m}UX, where u > m > 0 
and X G Xj\ 
• Xu+i = {{ct; + 1} U {2n + 1 : n > m} U X : lj > m> 0, X e Xf}. 
It is not hard to verify that # is a differentiated modal frame and that every 
upward closed (= open) set in P is either W or consists of all natural numbers 
in some interval [0, n\. Therefore, the points u and u 4-1 cannot be separated by 
any set in pP = {X G P : X = X}} and so p$ is not differentiated. □ 
Every Kripke frame is clearly differentiated. Moreover, for finite frames the 
converse is also true. 

DESCRIPTIVE FRAMES 
253 
Proposition 8.40 Every finite differentiated frame $ = (W, P, P) is a Kripke 
frame. 
Proof In the modal case it suffices to show that {x} e P for any x G W. 
But this follows from Proposition 8.38 and the finiteness of #. If # is a finite 
differentiated intuitionistic frame then <j$ is a finite differentiated modal frame. 
Ergo both cr$ and pcr$ = $ are Kripke frames. □ 
Proposition 8.41 A frame $ = (IV, JR, P) is tight iff for every x G W, 
x| = p|{XeP: xjCX}. 
Proof (=>) Suppose # is intuitionistic and y G f]{X G P : x| C I}. Then, 
since all X G P are upward closed, y G X for every X e P containing x, and so, 
by the definition of tightness, y G x]. If $ is modal then x] C X is equivalent to 
x G DX and so y G f]{X G P : C X} means that y G X for every X e P 
such that x G DX, whence y e x|. 
(<=) Straightforward. □ 
Corollary 8.42 Both operators p and a preserve tightness and refinedness. 
Example 8.43 The frame #, constructed in the proof of Proposition 8.39, is 
not tight, since 
P|{X€P: wTCX} = {u; + l}T. 
Also not tight is the differentiated intuitionistic frame 0 = (V, 5, Q) whose 
underlying Kripke frame is depicted in Fig. 8.3 (c) (u and u + 1 see all natural 
numbers) and Q = {V, 0} U {x|: 0 < x < u}. 
All Kripke frames are certainly tight. Moreover, by Proposition 8.40, every 
finite tight intuitionistic frame is a Kripke frame. 
Example 8.44 Finite tight modal frames are not in general Kripke frames, as is 
demonstrated by the frame consisting of the cluster with points 1, 2 and the set 
of possible values {0, {1,2}}. This frame is clearly tight, but not differentiated. 
Thus, every Kripke frame is refined and every finite refined frame is a Kripke 
frame. 
Given an arbitrary frame # = (IV, JR, P), we can construct a refined frame 
r$ = (rIV, rP, rP), having the same (modulo isomorphism) dual as by 
identifying some points in IV and adding new arrows between them. First, define an 
equivalence relation ~ on IV by taking 
X~y iff VX G P {x G X 4-» y G X). 
Then we let [x] = {y G IV : x ~ y}, for x G IV, rX = {[x] : x G X}, for X C IV 
and rP = {rX : X G P}. Notice that x G X implies [x] C X, for any X G P. 
Finally, we define a relation rR on rW by taking, for every [x], [y\ G rIV, 

254 
RELATIONAL SEMANTICS 
[x]rR[y\ iff VX eP (xeXye X) 
in the intuitionistic case and 
[x]rR[y] iff VX eP (xenx ye X) 
in the modal one. Clearly this definition does not depend on the choice of x in 
w- 
We denote (rW, rJR, rP) by r$ and call it the refinement of 
Proposition 8.45 The refinement r$ of any frame $ is a refined frame and 
S+ =r£+. 
Proof The map r defined by r(X) = rX, for X e P, is clearly a bijection from 
P onto rP. We show that r preserves fl, U, D, □. The first three operations in 
the modal case present no difficulties. For instance, 
[x] e rX fl rY iff [x] e rX and [x] e rY 
iff x e X and x e Y 
i ftxeXHY 
iff [x] er(XnY). 
Suppose now that # is intuitionistic, X,Y e P and [x] e rX D rY. Then 
y[y] e rW {[x]rR[y] A [y] e rX —> [y] e rY). (8.3) 
Since xRy implies [x]rJR[y], it follows that 
Vy e W (xRy A y e X y e Y), 
i.e., x e X DY and so [x] e r(X D Y). 
Conversely, let [x] e r(X D Y) and show (8.3). Suppose otherwise, i.e., there 
is y e W such that [x]rR[y], y e X but y $Y. Then y $ X D Y and so, by the 
definition of rJR, x $ X D Y which is a contradiction. 
The modal operation □ is considered analogously. 
Thus, r$ is really a general frame and r is an isomorphism of onto r$+. 
The fact that r$ is refined follows immediately from the definition. □ 
Example 8.46 The refinement r$ of the frame #, considered in the proof of 
Proposition 8.39, has the underlying Kripke frame as in Fig. 8.3 (b) and rP = P. 
The refinement of the frame 0 from Example 8.43 has the underlying Kripke 
frame as in Fig. 8.3 (a) and again rQ = Q. Finally, the refinement of the frame, 
considered in Example 8.44, is o. 
Using the refinement we can show that the notions of finite approximability 
and finite model property are equivalent. 
Theorem 8.47 A modal or si-logic L is finitely approximable iff it has the finite 
model property. 

DESCRIPTIVE FRAMES 
255 
Proof The implication (=>) is trivial. To show the converse, suppose that <p £ L. 
Then there is a finite model 97t such that 97t |= L and Wl (p. Let 3 be the 
general frame associated with 97t. Clearly, 3 validates L and refutes p. But then 
r3 separates from L as well. It remains to recall that a finite differentiated 
frame is a Kripke frame. □ 
Now let us consider compact frames. 
Proposition 8.48 A frame 3 = (W, JR, P) is compact iff every prime filter V 
in S+ is of the form Px for some x e W. 
Proof (=>) Let A = P — V. Since V is a prime filter, by Proposition 7.27, A 
is a prime ideal. Therefore, V has the finite intersection property and A has the 
finite union property, i.e., |J Z ^ W for any finite subset Z of A. 
Now we take X = V and y = {W — X : X e A}. Suppose Xi,..., Xn e X, 
Y\,..., Ym e y and consider the set 
z = Xi n... n xn n Yx n... n Ym. 
Let X = Xi D ... D Xn and Y = Y\ D ... n Ym. Clearly X e X and, since 
W - Y = (W - Yi) U ... U (W - Ym) G A, we have also Y G y. Suppose Z = 0. 
Then X C W - Y e A and so, since A' is a filter, W — Y e X, which is a 
contradiction. 
Thus, XU y has the finite intersection property and, by the compactness of 
$, there is an x G f](X U ^)- 
We show now that V = Px. Clearly V C Px. So suppose X e P and x E X. 
By the definition, X is either in V or in A. If X e V then we are done. But in 
fact this is the only possibility, for if X e A then W - X e y and so x £ 
which is a contradiction. 
(4=) Suppose X C P, y C P and X U y has the finite intersection property. 
We must show that the intersection of all sets in X U y is not empty. 
Let V be the filter in $+ generated by X and A the ideal generated by 
{W — Y : Ye ^}- Then V D A = 0. For otherwise there are X = f]Xf and 
Y = for some finite X' C X and / C such that X C W - Y, whence 
X (1Y = 0, contrary to X U y having the finite intersection property. Hence, by 
Exercise 7.18, there is a prime filter V' for which V C V' and V' D A = 0. 
Let V' = Px for some x e W. Then x e Z for any Z e V and x £ Z for any 
Z e A, whence x e X and x e Y for all X G A', V e y, and so f](X U y) ^ 0. 
□ 
Proposition 8.49 The operators p and cr preserve compactness. 
Proof That p preserves compactness follows immediately from the definition. 
Indeed, if 3 — (W, JR, P) is a compact quasi-ordered modal frame, X C pp, 
y Q pP and X U y has the finite intersection property then 
X'U yf = {z eP : {z = Z] A pZ e x) v (z = Z{ A pZ e y)} 
also possesses this property in 3• Hence f\(X' U y') ^ 0 and so f](X uy)^0. 

256 
RELATIONAL SEMANTICS 
To prove that a preserves compactness, we use Proposition 8.48. Suppose 
# = (W, P, P) is a compact intuitionistic frame, V is a prime filter in (cr#)"1" and 
show that V G crPx, for some x G W. Observe first that 
V; = {X G V : X = X1} 
is a prime filter in 3r+. By Proposition 8.48, there is x G W such that V' = Px. 
We show that V = crPx, i.e., V = {X G aP : x G X}. 
Suppose X G V, but x $ X. As we know, X can be represented in the form 
x = {-Xi u Yx) n... n (~xn u Yn), 
for some Xi, Yi G P. But then there is i G {1,..., n} such that x £ —Xi U 1*, i.e., 
x G Xi and x &Yi. On the other hand, — Xi U Yi G V and so either — Xi G V or 
Yi G V, since V is prime. In the former case Xi £ V and consequently Xi $ V', 
which is a contradiction, because x G Xi. And in the latter Yi G V', which is 
again a contradiction, since x then must be in Yi. Thus, V C {X G crP : x G X}. 
To prove the converse inclusion, assume that x G X G <rP, but X $ V. Since 
V is an ultrafilter, we then have -X G V and so, as we have just established, 
x G —X, which is a contradiction. □ 
Proposition 8.50 No infinite Kripke frame is compact. 
Proof Suppose first that # = (W,R,2w) is an infinite modal Kripke frame. 
Then the set X — {X C W : W—X is finite} has the finite intersection property, 
but no point x is in f]X, since W — {x} G X. 
Now let $ = (W, P, UpW) be an infinite intuitionistic Kripke frame. Then, 
according to Exercise 2.3, one of the following three cases holds. 
Case 1. # contains an infinite descending chain ... Ryn ... Ry2Ryi of distinct 
points. Then we take 
3> = {y4: i = i,2,...}cupr, * = {w-p|;y}cupw. 
It is clear that y has the finite intersection property and 
yieydn(w-f)y). 
However, by the definition, f\X U 30 = 0- 
Case 2. # contains an infinite ascending chain ... of distinct points. 
In this case we take 
X = {Xit: i = l,2,...}CUpW, y= {W-(]X} C VpW. 
Again XU y has the finite intersection property, but f](X U = 0. 
Case 3. # contains an infinite antichain Z. Consider the sets 
X = {XX C Z and Z — X is finite} C UpW, 

DESCRIPTIVE FRAMES 
257 
y = {Yj: Y C Z and Z — Y is finite} C UpW. 
Clearly, XU y has the finite intersection property. However, f)(X U y) is empty. 
□ 
We are now in a position to prove the main result of this section. 
Theorem 8.51 A frame $ = (W, P, P) is descriptive iff it is differentiated, tight 
and compact. 
Proof (=>) It suffices to show that the dual 21+ = (W<&, P&, P&) of every 
pseudo-Boolean and modal algebra 21 is differentiated, tight and compact. 
If Vi and V2 are distinct prime filters in 21 then there is an element a 
contained in only one of them, say in Vi- Then Vi G /a(a) G Pa and V2 ^ Ma)* 
So 21+ is differentiated. 
The fact that 21+ is tight follows directly from the definition of P&. 
To prove that 21+ is compact, recall that /a is an isomorphism of 21 onto 
(21+)"1". So every prime filter in (21+)+ is of the form 
MV) = {/a(a) : V G /a(a)} = PaV, 
for some prime filter V in 21, and we can use Proposition 8.48. 
(<=) We must show now that # = (#+)+. By Proposition 8.37, Px is a 
prime filter in and so we can define a map /$ from W into W$+ by taking 
/$(x) = Px, for any x G W. By Proposition 8.48, 
W*+ = {Px : x G W}. 
So /$ is a surjection. Moreover, /$ is an injection, since # is differentiated. 
If $ is intuitionistic and x,y G W then, since # is tight, 
xRy iff Px C Py iff PxR$+Py. 
If # is modal then again, by the tightness of #, we obtain 
xRy iff VIgP (UX e PxX e Py) iff PxRd+Py. 
Thus, it remains to show that, for any X C W, X G P iff f$(X) ePd+. 
RecaU that Pff+ = {fa (X) : X € P} and fa (X) = {Px : xe X}. So if X e P 
then f$(X) = {Px : x G X} = f$+(X) G P$+. Conversely, if f$(X) G P$+ then 
f$(X) = {Py : y G Y} = /#(Y), for some Y G P, whence X = Y, since /# is a 
bijection. □ 
Example 8.52 Let # = (W, P, P) be the frame whose underlying Kripke frame 
is shown in Fig. 8.4 (a; + 1 sees only u and the subframe generated by w is 
transitive) and P = {Xi U X2 U X3 : Xi G X^ i — 1,2,3}, where 
• X\ contains all finite sets of natural numbers including 0, 

258 
RELATIONAL SEMANTICS 
nontransitive 
' ~ transitive 
u) \ Xjj 2 1 0 • 
Fig. 8.4. 
• X2 contains 0 and all intervals {x : n < x < u;}, for n = 0,1,.. 
• A3 = {0> + !}}• 
It is easy to see that P is closed under D, - and j (in fact S is generated by 
0). Clearly, S is refined. Suppose A' is a subset of P with the finite intersection 
property. If X contains a finite set (from X\ or A3) then obviously f] X ^ 0. 
And if A consists of only infinite intervals from A2 then u G f\X. Thus, S is 
descriptive. 
We invite the reader to check that the frames S and 0 considered in 
Example 8.43 are compact (differentiated but not tight); so their refinements r$ and 
r0 are descriptive. 
As a consequence of Theorem 8.51, Proposition 8.49 and Corollary 8.42 we 
obtain 
Theorem 8.53 The maps p and r preserve descriptiveness. 
It is not hard to extend the results established above a bit further, namely, to 
modal matrices and frames with distinguished points. A frame with distinguished 
points (S, D) is called descriptive if S = (W, P, P) is descriptive and 
D = f){XeP: DCX}. (8.4) 
Theorem 8.54 Every descriptive frame ($,D) with distinguished points is 
isomorphic to its bidual (($+)+, (D+)+). 
Proof By the proof of Theorem 8.51, the map /#, defined by f$(x) = Px, 
is an isomorphism of S' onto (S"1")-}-- We show that f$(D) = (D+)+. Indeed, 
D+ = {X eP:D Cl}, (£>+)+ = {Px : D+ C Px} = {Px : x G f|{* G P • 
D C X}} and so, by (8.4), (£>+)+ = {Px : x e D} = f$(D). □ 
Theorem 8.55 The dual (21+, V+) of every modal matrix (21, V) is descriptive. 
Proof Exercise. □ 
As a consequence we obtain the following 
Theorem 8.56 Every logic in ExtK is characterized by a class of descriptive 
frames with distinguished points. 
8.5 	Truth-preserving operations on general frames 
To complete the fragment of duality theory suitable for the aims of this book, 
we will find out what operations on general frames correspond to the three 

TRUTH-PRESERVING OPERATIONS ON GENERAL FRAMES 
259 
fundamental algebraic operations of forming homomorphic images, subalgebras 
and direct products. In fact all we need is to extend the notions of generated 
subframe, reduction and disjoint union from Kripke frames to general ones. 
A frame 0 = (V, 5, Q) is a generated subframe of S = (W, R, P) (notation: 
0 C S) if <= and Q = {X n V : X G P}. 
Theorem 8.57 If h is an isomorphism of 0 = (V,S,Q) onto a generated sub- 
frame of$= (W,R,P) then the map h+ defined by 
h+(X) = h~l{X) = {xeV: h(x) e X}, for every X e P, 
is a homomorphism of S'"1" onto 0"1". 
Proof Without loss of generality we may assume h to be the identity map. 
Then 0 is a generated subframe of S and h+(X) = X D V. 
Clearly, /i"1" is a surjection. We show that it preserves U, - and j, assuming 
0 and S to be modal frames, and leave the intuitionistic case to the reader. Let 
X,Y e P. Then we have 
h+(X U Y) = (X U Y) n V = (X n V) U (Y n V) = h+(X) U fc+(y); 
h+(w - X) = (w - X) n v = v - (x n v) = v - /i+(X); 
h+(X[R) = X[RH V = (xn V)|S = h+(X)[S. 
The only non-trivial passage here is the middle = in the last line where we use 
the fact that V is upward closed in S- □ 
Observe that proving this theorem we used only that V is upward closed in S 
and Q = {Xn V : X e P}; the fact that Q is closed under modal or intuitionistic 
operations was redundant. This means that, given a frame S' = (W, P, P) and 
a set Y C W, we can take V = Yf’R, S = R n V2, Q = {X n V : X e P} 
and then the triple 0 = (V, 5, Q) will be a general frame which is a generated 
subframe of S- We call it the subframe of$ generated by Y. 
A model 91 = (0,il) on a frame 0 = (V, 5, Q) is a generated submodel of a 
model 97t = (S, 93) (notation: 91C 371) if 0 C $ and 11 (p) = 93(p) D V for every 
variable p. As a consequence of Theorem 8.57 we immediately obtain that the 
generation theorems in Sections 2.3 and 3.3 and their corollaries (Theorems 2.7, 
3.11 	and Corollaries 2.8, 2.9, 3.12) hold for general frames as well. Of course 
the same results can easily be derived directly from those theorems. Besides, we 
clearly have 
Theorem 8.58 Every superintuitionistic and normal modal logic is 
characterized by the class of its rooted general frames. 
Now we prove a theorem which is dual to Theorem 8.57. 
Theorem 8.59 Suppose h is a homomorphism of a mod^al or pseudo-Boolean 
algebra 91 onto a modal or, respectively, pseudo-Boolean algebra 93. Then the map 

260 
RELATIONAL SEMANTICS 
/i+ defined by /i+(V) = h 1(V), for every prime filter V m 23, is an isomorphism 
o/23+ onto a generated subframe of 21+. 
Proof By Theorem 7.68, h+ is a injection from W® into W&. Consider the set 
W = {V; G W<x : h~1(T) C V;}. 
Clearly W is upward closed in W% (in the modal case this follows from the fact 
that DT = T). We show that h+ is an isomorphism of 23+ onto the subframe 
# = (W, P, P) of 21+ generated by W. Notice that X e P iff, for some element 
a in 21, X = {V' G W : a G V'}. 
First we prove that ft+ is a bijection from W® onto W. Since every filter 
contains T, /i+(V) G W for all V G W®. Suppose V' G W and show that 
V' = Indeed, clearly we have V' C On the other hand, if 
a G h~1h(Vf) then h(a) = h(b), for some b G V'. And since h is a homomorphism, 
h(b —» a) = /i(£>) —> ft(a) = T, from which b —> a G V' and so a G V'. Thus, for 
every element a in 21 and every V' G W, 
a G V' iff ft(a) G fc(V'). (8.5) 
It follows that ft(V') is a prime filter in h is a bijection from W onto W® 
and is a bijection from W® onto W. It follows also that, for any X C W®, 
X G P® iff h+(X) G P. 
It remains to show that ViP®V2 iff ft+(Vi)P2t^+(V2). This is fairly easy 
for pseudo-Boolean algebras, since ViP®V2 means Vi C V2. So let us consider 
the modal case. Suppose that ViP®V2, i.e., Db G Vi implies b G V2, for all b in 
and that Da G ft+(Vi) for some a in 21. Then h(Da) = Dh(a) G Vi, whence 
h(a) G V2 and a G ft+(V2). Therefore, ft+(Vi)iiaft+(V2). Conversely, suppose 
ft+(Vi)Paft+(V2). Then for all a in 21, Da G ft+(Vi) implies a G ft+(V2). By 
(8.5), if h(a) = b and Db G Vi then Da G ft+(V 1), hence a G ft+(V2) and so 
?> G V2. Therefore, ViP®V2- □ 
For a cardinal x, a frame # is said to'be x-generated if its dual y-1" is an 
x-generated algebra. ^ is finitely generated if it is n-generated, for some n < u. 
Generators of y-1" will be regarded as generators of # as well.11 The dual of the 
free algebra of rank x in the variety VarL of a logic L is called the universal 
frame of rank x for L\ it will be denoted by 3x(^)- Clearly, for every cardinal 
x, there is only one (up to isomorphism) universal frame So 3x(R0) is 
the universal frame 73x for L defined in Section 8.1. 
Theorem 8.60 Every descriptive x'-generated frame for a logic L is 
(isomorphic to) a generated subframe of$L(x), for any x > xf. 
Proof Follows from Theorems 7.64 and 8.59. □ 
11 Thus, we have two ways of “generating” frames: relational (i.e., forming generated sub- 
frames) and algebraical. It will always be clear from the context which of them is used. 

TRUTH-PRESERVING OPERATIONS ON GENERAL FRAMES 
261 
According to Theorem 8.12, every quasi-normal modal logic L is characterized 
by the class of all frames for L with a single distinguished point. Using the 
generation theorem, we can somewhat refine this result. 
Theorem 8.61 Every consistent quasi-normal modal logic L is characterized by 
the class of all frames (#, {d}) for L with root d. 
As to generated subframes of modal frames with distinguished points, let 
us recall first that h is a homomorphism of a matrix (21, V') onto a matrix 
(35, V") if h is a homomorphism of 21 onto 35 and /i~1(V") = V'. This means 
in particular that /i-1(T) C V' and so the set V+ of distinguished points in 21+ 
(which consists of all ultrafilters in 21 containing V') is a subset of W defined 
in the proof of Theorem 8.59. Moreover, /i+(V") = V+, i.e., roughly speaking 
the distinguished points in 35+ are exactly the same as in 21+. This observation 
motivates the following definition. 
A modal frame (0, E) with distinguished points E is a generated subframe of 
a modal frame ($,D) with distinguished points D (notation: (0,75) C ($,D)) 
if 0 £ S’ and E = D. 
The next two theorems are left to the reader as an exercise. 
Theorem 8.62 Suppose 0 = (V, S, Q) and & = (W, 72, P) are modal frames, 
E and D are their distinguished points and (0,75) C ($,D). Then the map h+ 
defined by h+(X) = X fl V, for every X e P, is a homomorphism of (#+, D+) 
onto (0+,75+). 
Theorem 8.63 Suppose that h is a homomorphism of a modal matrix (21, V') 
onto (35, V"). Then the map /i+ defined by /i+(V) = /i-1(V), for every ultrafilter 
V in 35, is an isomorphism o/(35+, V+) onto a generated subframe o/(2l+, V+). 
It is clear that every frame with distinguished points is semantically 
equivalent to its every generated subframe. The following result which shows the 
relational meaning of extensions of matrices is also left to the reader. 
Theorem 8.64 (i) If E C D then (£+,£7+) is an extension of (£+, D+). 
(ii) 7/(21, V') is an extension of (21, V) then V'+ C V+. 
The relational counterpart of the notion of subalgebra is that of reduct. Given 
frames £ = (W,R,P) and 0 = (V,5, Q), we say a map / from W onto V is a 
reduction of $ to 0 if the following three conditions are satisfied, for all x, y G W 
and X G Qi 
(Rl) xRy implies f(x)Sf(y)\ 
(R2) f(x)Sf(y) implies 3z e f(z) = f(y)\ 
(R3) f-'iX) e p. 
For Kripke frames this definition is equivalent to the old one given in Section 2.3. 
Theorem 8.65 If f is a reduction of $ = (W, R, P) to 0 = (V, 5, Q) then the 
map /+ defined by f*(X) = f~1(X), for every X G Q, is an isomorphism of 
0+ in Sr+. 

262 
RELATIONAL SEMANTICS 
Proof Clearly /+ is an injection. So it suffices to show that /+ preserves all the 
operations in (3+. We consider only the modal case and leave the intuitionistic 
one to the reader. Let X, Y G Q- Then we have 
f+(X n Y) = f+{X) n f+(Y)- 
f+(v-x) = w-f+(xy, 
f+(XiS) = f+(X)lR. 
Only the last equality needs a justification. Suppose y G /+(X|5). Then there 
is x G X such that f(y)Sx. By (R2), there is z G y] for which f(z) = x. So 
y G f+(X)lR. Conversely, if y G f+(X)lR then yRx for some x G f~1(X), 
whence by (Rl), f{y)Sf(x) which means that y G f+(X[S). □ 
A reduction / of ^ to (3 is called a reduction of a model DJI = (#, 93) to a model 
DX = (<3,il) if 93 (p) = /_1(il(p)), for every variable p. It follows immediately 
from Theorem 8.65 that the reduction theorems in Sections 2.3 and 3.3 and 
their corollaries (Theorems 2.15, 3.15 and Corollaries 2.16, 2.17, 3.16) hold for 
general frames as well. 
Proposition 8.66 If fi is a reduction of a frame (or a model DJI\) to $2 
(DJI2) and f2 a reduction of $2 (DJI2) to £3 (DJI3) then the composition /2/1 is a 
reduction of$i (DJI\) to #3 (DJI3). 
Proof Exercise. □ 
As a simple example of the use of the reduction and generation theorems we 
prove the following: 
Theorem 8.67. (Makinson’s theorem) Every consistent normal modal logic 
L is contained either in Verum = Log# or in Triv = Logo. 
Proof We must show that either • |= L or o |= L. Since L is consistent, 
there exists a frame ^ for L, which either contains • as a generated subframe 
or is reducible to o (see the proof of Proposition 3.17). Therefore, either • or o 
validates L. □ 
The reductions of frames and models can be defined in somewhat 
different terms, namely as the quotient frames and models under some congruence 
relations. Suppose ^ = (W,R,P) is a frame and ~ an equivalence relation 
on W. We denote by [x] the equivalence class under ~ generated by x, i.e., 
[x] = {y G W : x ~ y}, and let [X] = {[x] : x G X} for any X C W. We say ~ 
is a congruence on # if xRy implies [x] C [y]l and [x] C X for every X G P and 
X G X. 

TRUTH-PRESERVING OPERATIONS ON GENERAL FRAMES 
263 
Given a congruence relation ~ on S', define a frame [S] = ([W], [R], [P]), the 
quotient frame of S under by taking 
[R] = {<[*], [y]) : [x] C [y]l), [P] = {[X] : X e P}. 
The fact that [P] is closed under the modal or intuitionistic operations follows 
from the equalities: [X O Y] = [X] 6 [T], for O E {A, V, —»}, and [DX] = D[X], 
which hold for every X,Y E P (the reader can readily verify them by himself). If 
ffl = (S,9J) is a model on S then by putting [9J](p) = [9J(p)], for every variable 
p, we obtain a model [97t] = ([S], [9J]) which is called the quotient model of Wl 
under 
Theorem 8.68 (i) If ~ is a congruence on S then the map f from W onto [W], 
defined by f(x) = [x\, is a reduction of$ to [S] and ofWl to [9JI]. 
(ii) Suppose that f is a reduction of S = (W,R,P) to (5 = (V,S,Q) and 
P' = {f~1(X) : X G Q}. Then the relation ~ on W defined by 
x~y iff fix) = f(y) 
is a congruence on & = (W, P, P') and [S'] is isomorphic to <5, with the map 
h([x]) = f(x) being an isomorphism. 
Proof Exercise. □ 
With the help of Theorem 8.68 we can prove the following: 
Theorem 8.69 7/S = (W,R,P) is a finite (modal or intuitionistic) frame then 
the refinement map r is a reduction of S to r$. In particular, every finite model 
is reducible to a refined model 
Proof Let us consider first the modal case. The relation ~ defined by 
x ~ y iff VX eP(xeX<^>yeX) 
is a congruence on S- Indeed, that [x] C X for all X € P and x e X follows 
immediately from the definition. So suppose that xRy. Since S is finite, [y] = 
P|{X € P : y € X} e P and so all the points in [x] must belong to [p]j. Thus, by 
Theorem 8.68, the map x y-> [x] is a reduction of S to [S]- It remains to observe 
that [x]rR[y] iff [x][B][y]. 
Now let S be intuitionistic. By Propositions 8.45 and 8.40, we then have 
r# = (3r+)+- The map f(x) = [x] ([x] is clearly the same in both # and <7^) is a 
reduction of cr$ to ((<73r)+)+ = <7((3r+)+) and so of 5 to (3r+)+ too. □ 
Example 8.46 shows, however, that Theorem 8.69 does not hold for infinite 
frames and models. 
The notion of congruence enables us to define the limit of an infinite chain 
of reductions. Suppose that, for every i < w, we have a reduction fi of fo = 
(Wi, Ri, Pi) to &+i = (Wm,Pm,Pm), or symbolically 

264 
RELATIONAL SEMANTICS 
So 4 ffi 4 fo ^ ■ • ■ • (8.6) 
By Proposition 8.66, the composition gi = fi-ifi-2 ... /o is a reduction of Jo to 
Ji- Let = {g~1(X) : XePJ and Q = Qi- Since, by Theorem 8.65, all 
Qi are closed under the operations in J^ , Q is also closed under them. Let ~i be 
the congruence on {Wo,Ro,Qi) corresponding to Clearly, ~i+1 for every 
i < u. It is not hard to verify that IU is a congruence relation on 
0 = (Wo, #o, Q). And now we can define the limit of the chain (8.6) of reductions 
as the reduction f(x) = [x] of 0, and so of Jo? to the quotient frame [0] of 0 
under If we have a sequence 
= (3o,2Jo> = (3i,2Ji) 4 ... 
of reductions of models then / is also a reduction of 9JIo to the quotient model 
[<0.*o>]. 
To prove a theorem which is dual to Theorem 8.65, we require the following: 
Lemma 8.70 Suppose that S = (£, A, V) is a sublattice of a distributive lattice 
21 = (A, A, V). Then every prime filter V in S can be extended to a prime filter 
V' in 21 such that V = V' fl B. 
Proof Let A be the prime ideal in S dual to V, i.e., A = B — V. Then by 
Exercise 7.18, there is a prime filter V' in 21 such that VC V' and V' fl A = 0, 
whence V = V' fl B. □ 
Theorem 8.71 If f is an isomorphism of a modal or pseudo-Boolean algebra 
in 21 then the map /+ defined by /+(V) = / X(V), for every V E W^, is a 
reduction of 21+ to S+. 
Proof To simplify notation, we assume ® to be a subalgebra of 21 and so / is 
the identity map and /+(V) = V fl B, for every V E Wqt- (Here and below A 
and B denote the universes of 21 and S, respectively.) It should be clear that if 
V is a prime filter in 21 then /+(V) is a prime filter in S. So, by Lemma 8.70, 
/+ is a map from Wi* onto W©. 
Suppose ViR2tV2, for some Vi,V2 E W^. In the intuitionistic case this 
means Vi C V2, whence /+(Vi) C /+(V2) and /+(Vi)R<b/+(V2). In the modal 
case we have: Da E Vi implies a E V2, for every a in 21. Since S is a subalgebra 
of 21, it follows that 
□6 E Vi D B implies b E V2 fl B, for every b E B, (8.7) 
i.e., again /+(Vi)R<b/+(V2). Thus, /+ satisfies (Rl). 
Now suppose that /+(Vi)-&b/+(V2) which in the modal case is equivalent 
to (8.7). Let us consider the filter Vo in 21 generated by the set 
{<x E A : □<! E Vi} U (V2 n B) 

TRUTH-PRESERVING OPERATIONS ON GENERAL FRAMES 
265 
and the ideal Ao in 21 generated by B — V2. Observe that Vo n Ao = 0. For 
otherwise there are elements a e A, for which Da e Vi, b e V2HP and c e £—V2 
such that a A b < c. Then a < b —> c, Da < □ (& —> c) and hence □(& —> c) G Vi- 
On the other hand, □(& —> c) G P and so, by (8.7), 6 —> c e V2 fl P, whence 
cG V 2 H £?, which is a contradiction. 
By Exercise 7.18, there is a prime filter V' in 21 such that Vo C V' and 
Ao D V' = 0. By the definition, ViP^V' and V' fi B = V2 fl P, i.e., /+(V') = 
/+(V2). Thus, in the modal case /+ satisfies (R2). The intuitionistic one is 
considered analogously. 
It remains to show that /+ satisfies (R3). Let X e P®, i-e., there is b in 23 
such that X = {V € W* : be V}. But then f^{X) = {V' € W* : be V'} 
and so f+x(X) e Pst- □ 
As to general frames with distinguished points, a reduction / of 5 to 0 is 
called a reduction of (5,1?) to (0, J3) if f~1(E) = D. 
We invite the reader to prove the following two theorems as an exercise. 
Theorem 8.72 If f is a reduction of (S,D) to (0,P) then /+ is an 
isomorphism o/(0+,P+) in (5+,D+). 
Theorem 8.73 If a modal matrix (23, V') is a submatrix of (21, V") then the 
map /+ defined by /+(V) = VHP, for every V e W%, is a reduction of (21+, V+ ) 
to(<B+,V'+>. 
It remains to define the relational counterpart of the direct product of modal 
and pseudo-Boolean algebras. 
The disjoint union of a family {& = (W*, P*, P*) : i e 1} of pairwise disjoint 
frames is the frame ^2ieI Si = (W, R, P) where W = |J-€/ W*, P = (Ji€/ P* and 
P = {Ui£j : Xi e Pi, for all i e I}. The fact that ^2ieI Si is really a general 
frame follows from the equations below which hold for every Xi,Yi e Pi, i e I 
(to establish them, only the disjointness of Si is required): 
(J Xi © (J Yi = {J(Xi © Yi), for © e {n, U, D}; 
i£l i£l i£l 
DUX* = U 
By the definition, every Si is a generated subframe of ^2ieI Si- 
The disjoint union ^2ieI 271* of a family of models {271* : i e 1} is defined 
in exactly the same way as in Section 2.3. Again 271* is a generated submodel 
°f J2iej 271* and so, using the generation theorem, we can easily extend 
Theorem 2.23 and Corollary 2.24 from Kripke frames to general ones. 
Theorem 8.74 Suppose {5i = (Wi,Ri,Pi) : i e 1} is a family of descriptive 
frames. Then ^2ieI Si = (W, P, P) is descriptive iff I is finite. 

266 
RELATIONAL SEMANTICS 
Proof (<=) It suffices to prove that 3i + #2 is compact if both Si and S2 are 
compact. Let V be a prime filter in (Si +S2)+- Then V» = {Xn Wi : X G V} is 
a filter in #+, for i = 1,2. Moreover, Vi is prime if it is proper. Observe now that 
only one of the filters Vi and V2 is proper. Indeed, let X\ U X2 G V for some 
X\ G Pi and X2 € P2. Since V is prime, either X\ G V or X2 6 V. Suppose 
for definiteness that X\ G V. Then, by the definition of filter, Xi U X G V for 
every X e P2 and so V2 = W2 and V = {X U Y : X G Vi, Y G P2}- By 
Proposition 8.48, Vi = P\x for some x G W\, whence V = Px. So, by the same 
proposition, Si + S2 is compact. 
(=>) Suppose now that I is infinite and let y = {W -Wi : i G 1} C P. 
Clearly, y has the finite intersection property, but f] y = 0. □ 
Theorem 8.75 Let {Si = (Wi,Ri,Pi) : i G 1} be a family of frames and 
P) their disjoint union. Then the map f defined by f(X)(i) = 
X fl Wiy for every X G P and i G I, is an isomorphism of ($^iG/Si)+ onto 
Proof By the definition, f(X) is an element of Yliei^ti i-e*> a function from 
I into Uiei Pi with f(X){i) £ Pu for all i G I. It should be clear that / is a 
bijection. Using the fact that the operations in Yiiei are defined 
componentwise, one can show that / preserves all the operations in (Yiiei fo)+* □ 
According to Theorem 8.74, the dual to Theorem 8.75 does not hold for 
infinite families of algebras. We have only the following 
Theorem 8.76 Suppose 2li and 2I2 are modal or pseudo-Boolean algebras. Then 
the map f defined by 
/(V1) = {(oi,a2) G Ax x A2 : a1 G Vi, a2 G A2}, for every Vi G W^, 
and 
/(V2) = {(ai,a2) G A1 x A2 : a 1 G A1, a2 G V2}, for every V2 6 W%2, 
is an isomorphism of%li+ + 2I2+ onto (2li x ^2)+- 
Proof It is easy to see that / is an injection. To show that it is a surjection, 
suppose V is a prime filter in 2li x 2I2 and V* = {a* : (ai,a2) G V}, for i = 1,2. 
Then Vi either is a prime filter or coincides with the universe of 21 i. And since 
(ai, <22) = (ai, JL) V (JL, 02), only one of Vi, V2 may be proper, say Vi. But then 
v = /(vo. 
Suppose that V', V" G U Wqi2 and V'iJV", where .R is the accessibility 
relation in 2li+ + 2I2+. Since 211 and 2I2 are generated subframes of 2li+ + 2I2+, 
V', V" G W2^ for some i G {1, 2}. So if 2li and 2I2 are modal and □ (ai, 02) = 
(□ai, Ud2) G /(V') then Da* G V', whence a* G V" and (01,02) € /(V"). Thus, 
/(VO^x^/CV"). 
Conversely, suppose that /(V^-R^x^/CV") for some V' G and V" G 
Wqtj U W<2i2. Assume also that Dai G V' for some ai G A\. Then □ (ai,_L) = 

POINTS OF FINITE DEPTH IN REFINED FRAMES 
267 
(□ai, □_!_) G /(V'), whence (ai,_L) G /(V") and so a\ G V" G W^. Thus, 
V'P^+V" and hence V'PV". 
The case of pseudo-Boolean 2li and 2I2 is left to the reader. 
Suppose now that X G P, where P is the set of possible values in 2li+ + 912+- 
Then X = /^(ai) U M2{a2), for some a\ G <22 G A2, i.e., 
X = {Vi G Wgtj : Gti G Vi} U {V2 G W2t2 : <22 G V2}, (8.8) 
and so, by the definition of / and the property of prime filters in 211 x 2I2 
established above, 
f(X) = {V G W%tlX2t2 : (ai,a2) G V} G PmlX2t2- (8.9) 
Conversely, if /(X) G Pmixm2 then, for some (ai,a2) G Ai x A2, /(-X”) is of 
the form (8.9). Since / is a bijection, X has the form (8.8) and so X G P. □ 
The disjoint union of the family {(&,£)*) : i G /} of frames with 
distinguished points is the frame (J2ieI Si, Ui€/ A)- The following two theorems are 
left to the reader as an exercise. 
Theorem 8.77 Let {(Si,Di) : i G 1} be a family of general frames with 
distinguished points and Si, Ui€/ ^eir disjoint union. Then the map f 
defined by f(X)(i) = X n Wi} for every X G P and i G I, is an isomorphism of 
<(£*/&) + ,(U€/ A)+> onto rlieI($t,Dt)- 
Theorem 8.78 Suppose (2ti,V') and (2l2,V") are modal matrices. Then the 
map f defined as in Theorem 8.76 is an isomorphism of (2li+, V'+) + (2I2+, 
onto ((2l1,V/)x(a2)V//))+. 
8.6 	Points of finite depth in refined finitely generated frames 
Every modal and si-logic L is characterized by the class of its finitely generated 
descriptive frames. Indeed, by Theorem 8.36, for any formula <p(pi,... ,pn) ^ L 
there are a descriptive frame S for L and a valuation 93 under which <p is refuted in 
S• The subalgebra 91 of S* generated by the elements 93(pi),..., 93(pn) is then 
an algebra for L refuting ip and so ip is separated from L by the n-generated 
descriptive frame 9l+. 
In this section we study the constitution of an upper part of finitely generated 
refined transitive frames, namely, the part containing points of finite depth. And 
in the next section we shall use the results to be obtained here to penetrate into 
the structure of the universal frames of finite rank for some modal and si-logics. 
Say that a point x and the cluster C(x) in a transitive frame S are of depth d, 
for d < u or d = 00, if the subframe of kS generated by x is of depth d. This fact 
will be denoted by d(x) — d(C(x)) = d. We reckon 00 as being greater than any 
d < lj. W=d and W-d are the sets of all points in S — (W, P, P) of depth d and 
< d, respectively; W<d, W>d and W-d are defined analogously. The subframe 
of S generated by W-d is denoted by S~d- 

268 
RELATIONAL SEMANTICS 
I I 
I I 
Fig. 8.5. 
In general, a transitive frame may contain no points of finite depth at all 
(see, for instance, Fig. 8.1 (c)). But this is not the case if the frame is finitely 
generated and refined. In fact, we shall see that every such frame $ = (W, R, P) 
can be represented as depicted in Fig. 8.5. More exactly, for each natural d such 
that 0 < d < d($), the set W=d is non-empty and contains a finite number of 
finite clusters Cd,..., Cfd \ all points in W=d turn out to be atoms in #, and W=d 
is a cover for the set W-d, i.e., 
W= W=11 
= W=1UW=2l 
= W=1 U ... U W=m U W=m+1I 
Frames with such properties are called top-heavy. To prove this result, we require 
some auxiliary notions. 
Suppose # = (W, P, P) is a refined modal or intuitionistic transitive frame 
generated (as modal or, respectively, pseudo-Boolean algebra) by some sets 
Gi,..., Gn e P, 0 < n < u. Define in # a valuation 9J of the language MCn 
or Cn with the set of variables E = {pi,... ,pn} by taking %3(pi) = G», for each 
i = 1,... ,n. Thus, 
P = {2J(<p) : (p e ForMCn (or (p e For£n)} 
and we can work with formulas as well as with sets in P. As in Section 5.3, we 
regard two points x,y e W as E-equivalent in # and write x y if the same 
formulas in E are true at them under 9J; [x]u is the E-equivalence class generated 
by x. Sets X, Y C W are called E-equivalent in X Y for short, if every 

POINTS OF FINITE DEPTH IN REFINED FRAMES 
269 
point in X is E-equivalent to some point in Y and vice versa. 
A non-empty set X C W is said to be cyclic in $ (relative to 93) if either 
Vx, y E X 3z E X (xRz A z y) (8.10) 
(which is equivalent to Vx E X x| H X ^ X) or 
Vx,t/€l (x ~xy A -ixRy). (8.11) 
These two conditions are mutually exclusive. If the former one is satisfied, X 
is called a non-degenerate cyclic set, while if the latter condition holds we say 
X is a degenerate cyclic set. It should be clear that all cyclic sets in a reflexive 
(in particular, intuitionistic) frame are non-degenerate and that all clusters are 
cyclic. 
Given d such that 0 < d < d($) and a point x E W>d, we define the d-span 
of x in # as the set spd(x) = {y e W-d : xRy}. By the definition, sp°(x) = 0 
for every x in #. A cyclic set X is called d-cyclic if 
X = Xl DW>d (8.12) 
and 
Vx, y € X (spd(x) = spd(y)). (8.13) 
Every non-empty upward closed in W>d subset of a d-cyclic set is also d-cyclic. 
Lemma 8.79 Suppose x and y are E-equivalent points in a d-cyclic set X. Then 
x |—ip iffy\=(f, for every formula ip in For MCn or For Cn. 
Proof We consider only the modal case, leaving the intuitionistic one to the 
reader. The proof proceeds by induction on the construction of <p. 
The basis of induction is ensured by x Vi and the cases of <p = 0 A x, 
0 V x and -0 —> x are trivial. So suppose x ^ D0. Then z ^ 0 for some z e x|. 
If z 6 W-d then z e y], since spd(x) = spd(y), from which y ^ D0. If z E W>d 
then, by (8.12), z e X and so X is non-degenerate. By (8.10), there is u E y^\ 
such that u z, whence by the induction hypothesis, u ^ 0 and so y ^ D0. 
The symmetrical argument shows that y ^ D0 implies x D0. □ 
Using the fact that # is refined, we obtain a stronger result. 
Lemma 8.80 Suppose $ is a refined n-generated frame, 0 < d < d($) and X is 
a d-cyclic set in Then 
(i) x = y, for every E-equivalent points x, y E X; 
(ii) X is a non-degenerate cluster of cardinality <2n, if X is non-degenerate, 
and 
(iii) X is an irreflexive singleton, if X is degenerate. 
Proof (i) follows immediately from Lemma 8.79 and the differentiatedness of 
(iii) is a direct consequence of (i). So let us establish (ii). Observe first that there 

270 
RELATIONAL SEMANTICS 
are at most 2n pairwise non-E-equivalent points in #, whence by (i), \X\ < 2n. 
Now suppose x, y e X and prove that xRy. By the tightness of 8, it suffices 
to show that (in the modal case—the intuitionistic one is left to the reader) for 
every p € ForMCn, x f= Up implies y f= p. Assuming otherwise, we must have 
some p for which x |= Up and y ^ <p- By (8.10), there is z e X such that xRz 
and z y and so, by Lemma 8.79, z p% which is a contradiction. 
Thus, xRy for all x,y e X. It remains to observe that all points in a cluster 
are of the same depth and that X is upward closed in W>d, i.e., X cannot be a 
proper subset of a cluster. □ 
As a consequence of Lemma 8.80 we obtain the following characterization of 
clusters of depth d + 1 in 8- 
Lemma 8.81 Suppose that $ is a refined finitely generated transitive frame and 
d < d(8)- Then C is a cluster of depth d+1 in 8 iff C is a d-cyclic set in 8- 
Proof (=>) It is clear that C is cyclic. It is d-cyclic, since all points in C 
are of the same d-span and besides C has no proper successors in W>d, i.e., 
c = c]_r\w>d. 
(<£=) follows from Lemma 8.80. □ 
It follows, in particular, that a d-cyclic set in a refined finitely generated 
frame has no proper d-cyclic subsets and so clusters C(x) and C(y) of depth 
d+1 coincide if x and y are of the same d-span and C(x) C(y). Using this 
observation, we can estimate the number of clusters of depth d + 1 in 8, if any. 
Theorem 8.82 Suppose $ is a refined n-generated transitive frame and d < 
d(8)- Then the number of distinct clusters of depth d + 1 in $ is not greater than 
cn(d + 1) which is defined recursively as follows: 
cn( l)=2"+22“-l; 
Cn(d + 1) = cn(l)2c”^+"+c"^. 
If 3 is irreflexive or partially ordered then one can take cn(l) = 2n. Every proper 
cluster in 8 contains at most 2n points. 
Proof There are at most 2n pairwise non-E-equivalent points and 22” — 1 
pairwise non-E-equivalent non-empty sets of points in 8- So there are at most 2n 
degenerate and 22” - 1 non-degenerate clusters of depth 1 in 8• If 'S is irreflexive 
or partially ordered then all clusters in 8 are singletons and hence the number 
of clusters of depth 1 in such a frame is not greater than 2n. 
Distinct clusters of depth d + 1 may be E-equivalent, but then they have 
distinct d-spans, the total number of which does not exceed the number of all 
sets of clusters of depth < d. The size of clusters was estimated in Lemma 8.80. 
□ 
Theorem 8.83 Suppose 8 is a refined finitely generated transitive frame. Then 
every point of finite depth in 8 is an atom. 

POINTS OF FINITE DEPTH IN REFINED FRAMES 
271 
Proof Observe first that the intuitionistic case reduces to the modal one. 
Indeed, if # = (W,R,P) is an intuitionistic n-generated refined frame then 
(= (W,R,aP) is a modal n-generated refined frame. So if x is an atom 
in cr$, i.e., {x} e crP, then W - x| G crP and {re} U (W - xj) e crP and hence 
the sets W — x{ and {x} U (W - x j) are in P, since both of them are upward 
closed and P = pcrP. 
Now we prove our theorem for a modal # by induction on depth. Suppose 
that u is a point in # = (W, P, P) of depth d + 1 and that all points of smaller 
depth, if any, are atoms in It follows from this assumption and the finiteness 
of W^d that W>d e P. 
For x € W>d, we denote by Gd the set 
(f|{Gi : xeGi}- (J{Gi: x $ G,}) n W>d € P. 
(We remind the reader that Gi,... ,Gn generate $.) It is clear that, for every 
y,z e W>d, y z hf Gd = Gd. So it suffices to show that C(u) e P, since by 
Lemma 8.80, {u} = C(u) D Gd. 
Let us consider the following two cases. 
Case 1: The cluster C(u) is non-degenerate. Then we form the set 
x = w>d n 
( f| U Gxl)n 
x€C( u) G£nC(u)=0 
( fi yi- U (814) 
y€spd(u) y(E.W^d — spd(u) 
which is in P, since there is only a finite number of pairwise distinct sets G^, for 
x e W>d. By the definition, X consists of all points x of depth > d such that (a) 
xt C\W>d C(u) and (b) spd(x) = spd(u). Therefore, C(u) C X. Now, taking 
the upward closed in W>d part of X, i.e., D(X U W-d) D X G P, we obtain 
a d-cyclic set which contains C(u) and so, by Lemma 8.81, must coincide with 
G(u). 
Case 2: The cluster C(u) is degenerate, i.e., u is irreflexive and C(u) = {u}. 
By Lemma 8.80, we then have 
C(u) = Gdn (w>d - w>dI) n (8.15) 
( n ~ U y^ 
y(Espd(u) y€.W-d — spd(u) 
and so again C(u) G P. □ 
Although we have already learned much about clusters of finite depth in 
refined finitely generated transitive frames, we do not know still whether they 
really exist. 

272 
RELATIONAL SEMANTICS 
Pi 
• • 
Pi 
o o 
Fig. 8.6. 
Theorem 8.84 Suppose $ is a refined finitely generated transitive frame and 
0 < d < d($). Then for every point x G W>d there is a cluster C of depth d + 1 
such that x G C[. In other words, W=d+1 is a (finite) cover for W>d. 
Proof If the set X = x]_ D W>d is d-cyclic then, by Lemma 8.81, £ is a point 
of depth d + 1. Otherwise either (8.10) or (8.13) does not hold for X. So there is 
a point y G D W>d such that either the number of pairwise non-E-equivalent 
points in y| D W>d is smaller than that in X or spd(y) C spd(x). In exactly 
the same manner we consider now the point y, etc. Since there is only a finite 
number of pairwise non-E-equivalent points in # and W-d is also finite, we shall 
eventually find a point 2 G D W>d for which zj D W>d is d-cyclic. Ergo C(z) 
is a cluster of depth d-1-1 and x G C{z)[. □ 
The results obtained above will find many applications later on in the book. 
Here we show only one immediate consequence. 
Say that a logic L in ExtK4 or Extint is of depth n < a; if it contains the 
formula bdn and does not contain. bdm for any m < n; L is of finite depth if it is 
of depth n for some n < lj. This terminology is explained by the following: 
Theorem 8.85. (Segerberg’s theorem) Every logic of depth n < lj is 
characterized by the class of its finite Kripke frames of depth < n. 
Proof It suffices to show that every formula <p(pi, •.. ,pm) & E is separated 
from L by a finite Kripke frame of depth < n. Let # be an m-generated refined 
frame for L refuting <p. By Theorems 8.82 and 8.83, $-n is a finite Kripke frame. 
And since bdn G L (and in view of Propositions 2.38 and 3.44), $ contains no 
points of depth n-hi and so, by Theorem 8.84, $ = $-n. □ 
8.7 	Universal frames of finite rank 
The most complete information about logics is contained in their universal 
frames. In this section we give an effective description of the upper part—the 
points of finite depth—in the universal frames of finite rank for a few standard 
modal and si-logics and get some general impression of how those frames for 
other logics may look. 
We begin with K4. Let MCn be the modal language with n < lj variables, 
say pi,... ,pn and E = VarMCn. As before, we assume that G\,... ,Gn are 
generators of the universal frame a?K4(n) and define a valuation 2lK4(n) of MCn 
in a?K4(n) by taking 2?K4(n)(Pi) = G*, for i = 1,..., n (recall that 2JK4(n) maY 
be regarded also as a valuation in 5lR4(n) such that 2Jk4(n)(Pi) = llPiIIk4)- 
^K4(n) — (?K4(n)j%4(n)) is called the n-universal model for K4. 
Since SrK4(n) Is a refined n-generated transitive frame, its generated subframe 
^K4(n) depth 1 consists of clusters with at most 2n points, with distinct points 

UNIVERSAL FRAMES OF FINITE RANK 
273 
in each cluster, distinct degenerate clusters as well as distinct non-degenerate 
ones being pairwise non-E-equivalent. The maximal number of such clusters is, 
as we know, 2n + 22*1 — 1. On the other hand, since i?K4(n) is the universal 
frame of rank n and in view of Theorem 8.60, it must contain as a generated 
subframe any descriptive n-generated frame of depth 1, in particular the frame 
®K4^n) associated with the model 9t|^(n) of depth 1 containing all possible 2n 
pairwise non-E-equivalent degenerate clusters and all possible 22*1 — 1 pairwise 
non-E-equivalent non-degenerate clusters of < 2n non-E-equivalent points. The 
model 9^4(1) is shown in Fig. 8.6, where p\ near a point x means that x \= pi\ 
otherwise x Pi- Since 9tfc4(rc) is finite, to verify that ®|c4(n) is descriptive, it 
suffices to establish its atomicity. We shall do this a bit later, when considering 
points of arbitrary depth d < uj. Meanwhile, under the assumption that this is 
the case, we can conclude that a?^4(n) is isomorphic to ®K4(n). 
Suppose now that 0 < d < uj and we have already constructed a model 
^K4^n) depth, d whose associated frame ®f^4(n) is isomorphic to ®K4(n)* 
Define ^K4+1(n) by adding to 91^4 (n) a number of clusters of depth d 4- 1. 
Namely, for every antichain X of points in 9tf^4(w) containing at least one point 
of depth d and different from reflexive singletons (i.e., X ^ {re}, for any reflexive 
x), we add to ^1^4 (n) coPies °f all the 2n + 22^ — 1 clusters of depth 1 with 
the same valuation so that they would be inaccessible from each other and could 
see only the points in X and their successors. And for every reflexive singleton 
X = {re} of depth d, we add to 9^4 (n) coPies °f those clusters of depth 1 
which are not E-equivalent to any subset of C(x) so that again they would be 
mutually inaccessible and could see only x and its successors in ^^4 (n)- is 
be emphasized that we do not distinguish between two antichains whose points 
generate the same clusters.) The resulting model is denoted by ^K4+1(n)- ^ 
fragment of 9^4 W *s s^own in Fig- 8.7. 
The frame ®K4+1(n) associated with ^K4+1(n) ls n-generated and 
descriptive. Indeed, as was observed above, the descriptiveness of a finite frame follows 
from its atomicity. We prove that ®K4+1(n) at°mic by induction on depth. Let 
®K4+1(n) = (F, S, Q) and suppose that all points in V-m are atoms in ®K4+1(n) 
and u is a point of depth m + 1. Since ®K4+1(n) is finite, it follows in particular 
that V-m and V>m are in Q. As in the proof of Theorem 8.83, for x G V>m 
we denote by G™ the set of points in V>m which are E-equivalent to x. Clearly 

274 
RELATIONAL SEMANTICS 
Fig. 8.9. 
we have G™ € Q and to show that {u} G Q it is sufficient to establish that 
C(u) G Q because {u} = C(u) D G 
If C(u) is a non-degenerate cluster then it is a subset of the set X G Q defined 
by (8.14) with d replaced by m. Since for every point v G y=m+1 belonging to a 
cluster different from C(u), either C(v) is not E-equivalent to C(u) or spm(v) ^ 
spm(u), we have X D y=m+1 = C(u). And since there is no point v in y=m+2 
such that C(v) is E-equivalent to a subset of C(u), C{v)| D y=m+1 = C(u) and 
spm(v) = spm(u), we have □ (X U V-m) D X = C(u) and so C(u) G Q. 
In the case when C(u) is a degenerate cluster it may be represented in the 
form (8.15) with d replaced by m. Therefore, again C(u) G Q. 
It follows that ®K4+1 (n) is a generated subframe of a?K4(n)- On the other 
hand, the results of the preceding section show that SrK4(n) contains no clusters 
of depth d + 1 different from those in ®K4+1(n) an(^ so ^K4+1(n) is isomorphic 
to ®K4+1(n)- 
Let ^K4 (n) the union of all models 9^4 (n) ^or ^ < cj, i.e., its set 
of worlds, accessibility relation and truth-relation are the unions of those in 
^K4 (n)’ We arrive then at the following: 
Theorem 8.86 The frame ®K4 (n) associated with ^K4 (n) *s isomorphic to 
®K4 (n)' 
Since K4 is finitely approximable, every formula in ForA4£n that is not 
in K4 is refuted by some n-generated descriptive finite frame which must be 
a generated subframe of 3^4 (n)- Therefore, both the model ^^4 (n) an(^ the 
frame ^K4 (n) characterize K4nForA4£. 

UNIVERSAL FRAMES OF FINITE RANK 
275 
Fig. 8.11. 
The universal frame 3x(n) for an arbitrary consistent logic L in NExtK4 
is a generated subframe of SrK4(n)- It can be constructed by removing from 
3x4 (n) those points at which some formulas in L are refuted (under 27x4 (n))- 
For example, 3g!°(n) is obtained by removing from 3k4 (n) all the irreflexive 
points and their predecessors. In other words, 3g!°(n) can be constructed in 
the same way as 3^4 (n) but using only non-degenerate clusters, 
corresponding model, to be more exact) is shown in Fig. 8.8, where V denotes 
the cluster with two points at one of which pi is true. To construct 3q^ (n) 
and SqlM) we take only simple clusters and degenerate clusters, respectively. 
3rQrZ(I) and are depicted in Fig. 8.9 (a), (b). Fig. 8.10 (a), (b) and 
Fig. 8.11 show the upper parts of the universal frames of rank 1 for the logics 
S4.3, Grz.3 and GL.3, respectively. The universal frames of rank n for logics 
of finite depth L = V 0 bdd (L' G NExtK4, d < lj) are obtained by removing 
from $L,°°(n) all the points of depth > d, i.e., Sl(^) is isomorphic to the finite 
frame 
3gl(°) is Just an infinite descending chain of irreflexive points. Its points are 
characterized by the formulas of the form = CP+1_L A OlT, for i > 0. Since 
GL is finitely approximable, every variable free formula ip GL is refuted in 
this frame. Let n be the minimal number such that V- Then clearly 
GL 0 (p = GL 0 □n_1_L. Thus we have 
Theorem 8.87 (i) For every variable free formula ip, there are i\,... ,in such 
that 

276 
RELATIONAL SEMANTICS 
ip <-» _L V <pix V ... V ipin e GL or <p <-» -i(± V ^ V ... V y>in) G GL. 
(ii) Every variable free formula is deductively equal in NExtGL either to T 
or to lHnJL, for some n > 0. 
Proof Exercise. (Hint: (i) is proved by induction on the construction of ip.) 
□ 
It is worth noting that if a logic L in NExtK4 or Extint is finitely 
approximate then its universal frame 3r,(x) of rank x is completely determined by 
3l°°(x)- For the m°del (SrL°0(x)’^L°0(x))’ where ®^°°(x) is the restriction of 
53l(x) to characterizes the logic L (in the language with x variables) 
and besides we have the following: 
Proposition 8.88 Suppose L is a normal modal or si-logic in a language with 
x variables, $ an x-generated (but not x/ -generated, for any xf < x) frame, 53 
a bisection from the set of variables onto the set of $’s generators and the model 
(#,53) characterizes L. Then #+ is isomorphic to 51 l(x). 
Proof Let / be the bijection from the set of generators in 51 l(x) onto the set 
of generators in #+ such that /(||p||l) = 53(p), for every variable p. Since 51 l(x) 
is a free algebra in VarL, / can be extended to a homomorphism h of 51 l(x) 
onto #+ such that /&(|M|l) — 53(<£>). In fact, the map h turns out to be the 
isomorphism we need. To see this, it suffices to establish that h is an injection. 
So suppose ||^||l and \\x/)\\l are distinct elements in 51 £,(x). Then ip <-» ^ ^ L 
and hence ip <-» -0 is refuted in (#,53), from which /i(||^||l) 7^ MII^IIl)- □ 
Corollary 8.89 The universal frame #l(x) of rank x for a finitely 
approximate logic L in NExtK4 or Extint is isomorphic to the bidual o/Sr^°°(x). 
The upper part °f the universal frame #int(n) f°r Int can be 
constructed in the same spirit as 3^4 (n) but taking into account specific features 
of intuitionistic frames, namely that they are partially ordered and their sets of 
possible values consist of upward closed sets of points. First we form a model 
93^. (n) depth 1 by taking 2n distinct non-E-equivalent reflexive points which 
do not see each other. (As before, E = {p\,... ,pn}.) Suppose now that we have 
already constructed a model 93^. (n) of depth d < w. For every antichain X in 
^Rit(n) with — ^ points at least one of which is of depth d, we add to 93^. (n) 
copies of all points y of depth 1 (with the same valuation) such that, for any 
x e X and p E E, y |— p implies x f= p. Those copies are arranged so that 
they would not be accessible from each other and could see only the points in 
the corresponding antichain and their successors. For a singleton X = {x} the 
added copies of y must satisfy one more condition : x '/'£ V- 93j^(n) is defined as 
the union of 93^. (n) for all d < uo and is the n-generated intuitionistic 
frame associated with 53j^(n). 
Theorem 8.90 #f~(n) ** 0f~(n). 
Proof Exercise. 
□ 

UNIVERSAL FRAMES OF FINITE RANK 
277 
P\,P2 - Pi P2 
Fig. 8.12. 
The model *s s^own in Fig. 8.12 and ^1^(1) in Fig. 8.13. Notice by 
the way that the following proposition holds. 
Proposition 8.91 For every point k in ^1^(1) and every Nishimura formulas 
nf 2n a.ndnf2n_l9 n > 1, 
k nf2n iff k € n[ iff k = n or k >n 4-2; 
k ¥= nf2n-i iff k € {n + 1, n + 2}j iff k > n + 1. 
Proof This claim can be easily proved either directly by induction or using the 
observations of Example 7.66 and the fact that the dual of is isomorphic 
to the free 1-generated algebra 2lint(l) depicted in Fig. 7.2 (a). □ 
Using this proposition, we can obtain a characterization of descriptive frames 
refuting the Nishimura formulas. Denote by Sjn the subframe of the frame in 
Fig. 8.13 generated by n. 
Theorem 8.92 For every descriptive frame 
(i) $ ^ nf2n iff there is a generated subframe of$ reducible to $)n; 
(ii) # \/= nf2n_1 iff there is a generated subframe of $ reducible either to 
f)n+1 or to 5}n+2- 
Proof We establish only (i), because (ii) is proved in the same way. 
(=>) Suppose # refutes nf2n under a valuation 53. Then nf2n is refuted 
in the subalgebra of generated by 53(p) and so in its dual 0, to which, by 
Theorem 8.71, # is reducible by some map /, under the corresponding valuation 
il. Since 0 is a 1-generated descriptive frame, it is (isomorphic to) a generated 
subframe of 3int(l)> &(p) = {1} and so, by Proposition 8.91, 0 contains as a 
generated subframe. Therefore, /_1(^n) is a generated subframe of # reducible 
(<*=) follows from Proposition 8.91, and the generation and reduction 
theorems. □ 

278 
RELATIONAL SEMANTICS 
1 
3 
5 
7 
9 
»£t(l) 
Fig. 8.13. 
Figures 8.14 and 8.15 illustrate the frames and Sxc^), respectively. 
(For typographical reasons instead of p\, p2, ps in the latter figure we write their 
subscripts.) Observe that *s isomorphic to »Ec(3)- 
Unfortunately, this method of constructing universal frames of finite rank 
does not go through for logics with nontransitive frames. However, for some 
particular systems it can be appropriately modified. We show such a modification 
for K. 
Again we construct a model 91^°° (n) as a “limit” of a sequence of models 
^K*(n)» f°r d < w. Every point x in this model is characterized by a formula 
X(x)- ^R1(n) is Just the antichain of 2n non-E-equivalent irreflexive points. For 
these points x we put 
x(x) = D-L A f\ Pi A f\ -'Pi- 
x\=pi x\£pi 
Suppose now that the model and the corresponding formulas x(^) have 
been already constructed. This model is extended to *n the following 
way. For every set X of points in 9t|^(n) containing at least one point that does 
not belong to we add an antichain of 2n non-E-equivalent irreflexive 
points so that they could see only the points in X and nothing else. The formulas 
X(x) for the new points x look like this: 
X(x) = Dd± A /\ Ox(y) A /\ -iOx(y), 
yex yev 
where Y is the complementation of X in 9t|^d(n). Finally, let 9t^°°(n) be the 
union of all models ^^(n) for d <uj. 
Using two facts—that every point x in 9t^°°(n) is characterized by the 
corresponding formula x{x) and that K is determined by the class of finite intransitive 

EXERCISES AND OPEN PROBLEMS 
279 
Pi > P2 Pi P2 
trees (see Corollary 3.29)—one can prove that ^^(n) characterizes K and so, 
by Proposition 8.88, 21k (n) is isomorphic to the dual of the frame associated 
with ^^(n). 
8.8 	Exercises and open problems 
Exercise 8.1 Show that a modal frame $ is tight iff for every k > 1 and all 
ni,...,nk > 1, 
ZiTni u... U xkTk = f|{X € P : Xitni U...U xk\nk Cl}. 
Exercise 8.2 Show that for any family X of sets in a modal frame 
□n*= nDx> °{Jx= u 
xex xex 
Is it possible to replace here p| by (J and (J by p|? 
Exercise 8.3 Show that a modal frame 5 = (W, i?, P) is compact iff, for any 
X C P, (J X = W only if there is a finite subset X' of X such that (J Xr = W. 
Is this true for intuitionistic frames? 
Exercise 8.4 Show that the classes VP and T are closed under the formation 
of generated subframes, i.e., every generated subframe of a differentiated or tight 

280 
RELATIONAL SEMANTICS 
frame is differentiated or tight itself. What about CM? (Hint: consider the frame 
in Example 8.8.) 
Exercise 8.5 Show that the class CM is closed under reductions, while VT and 
T are not. 
Exercise 8.6 Show that the classes VT and T are closed under disjoint unions. 
Exercise 8.7 Show that if 0 and # are quasi-ordered modal (intuitionistic) 
frames and 0 C $ then p0 C (<j0 C ag). Prove the analogous results for 
reductions and disjoint unions. 
Exercise 8.8 Prove that the class of finite intransitive trees is closed under 
finite disjoint unions, reductions and generated subframes but is not modally 
definable. (Hint: show that o validates all formulas validated by all frames in the 
class.) 
Exercise 8.9 Prove that the model 9t^°°(n) constructed at the end of the 
previous section is n-universal for K. 
Exercise 8.10 Show that there is a continuum of 1-generated Grz-algebras and 
a continuum of 1-generated GL-algebras. 
Exercise 8.11 Show that if h is an isomorphism of a descriptive frame 0 onto 
a generated subframe of a descriptive frame # then = /$ft, and if 
h is a homomorphism of a modal or pseudo-Boolean algebra 21 onto 05 then 
(h+)+/2i = /©ft. 
Exercise 8.12 Show that if / is a reduction of a descriptive frame J to a 
descriptive frame 0 then (/+)+/y = /$/, and if / is an isomorphism of 05 in 21 
then (/+)+/© = /a/. 
Exercise 8.13 Will Theorem 8.87 hold if we replace in it deductive equality by 
equivalence? 
Exercise 8.14 Show that if / reduces # to 0 then d(x) > d(f(x)) for every 
point x in 
Exercise 8.15 For every point x in 3^4 (n) construct a formula <p in n variables 
such that a descriptive frame # refutes (p iff there is a generated subframe of # 
reducible to the subframe of 3^4 (n) generated by x. Do the same for *»(»)• 
Exercise 8.16 Show that every consistent si-logic either coincides with Cl or 
is contained in SmL. 
Exercise 8.17 Prove that the dual of the limit of the chain (8.6) is isomorphic 
to the intersection of all 
Exercise 8.18 Show that for every 3r = (W, R, P) the refinement r3r is 
isomorphic to the frame (V,S,Q) in which V = {Px : x G W}, PxSPy iff Px C Py 
in the intuitionistic case and VX G P (DAT G Px —► X G Py) in the modal one, 
and Q = {{Px : x G X} : X G P}. 

EXERCISES AND OPEN PROBLEMS 
281 
Exercise 8.19 Show that □(□+p —> q) V □(□+# —> p) is not deductively equal 
in NExtK4 to any formula in one variable. 
Exercise 8.20 Let L2 = K4®{axl, ax2, ax3, ax4, axb.'ijj : 0 G {a,/3,7}}, where 
arrl = ao V 0+ai, ax2 = 7 —> O7, ax3 = 7 —> O7', 
ax4 = O/?' A Oa" —> O7, aa;5.0 = □+(# —> ->'0) V E+(-ig —> -.0), 
a = p A —>Op, a' = a(Op/p), a" = a'(Op/p) = a(02p/p), 
a> = a(0*T/p), a<+1 - a'^T/p), ai+2 = a'^T/p), 
/3 = Oa A -iO+a', /?' = 0{Op/p), 
Pi = P(0iT/p) = 0aiA-^0+ai+u 
Pi+i = ^'(O'T/p) = Oai+i A -0+a*+2, 
7 = O/?' A Oa" A -iOjS, 7' = 7(Op/p), 
7i+i = 7(OlT/p) = 0/?<+1 A Oai+2 A -lOft, 
7i+2 = V(0*T/p) = 0/?i+2 A Oai+3 A -iO/3<+1 (i > 0). 
Show that if $ = (W, R, JP) is a rooted differentiated frame for L2 then (W, JR) 
is isomorphic to a rooted generated subframe of the frame shown in Fig. 8.16, 
with all {a*}, {bj} and {c^} being in P. (Hint: use the following substitution 
instances of L2’s axioms: 
ax2.i = ji —» O7i = ax2(OlT/p), 
axS.i = 7i —> <>7i+i = ax3(OlT/p), 
ax4.i = 0/% A Oai+i —i► O7* = ax4(OlT/p) (i > 1), 
axb.cti = □+(g —> -la*) V □+(-ig —> -la*) = ax5.a(OzT/p), 
ax5.ft = □+(g -+ -ift) V □+(-ig -> -ift) = az5./3(0*T/p), 
ax5.7i+i = D+(g -> -.74+1) V □+(-»g 174+1) = ax5.7(OzT/p), (i > 0).) 

282 
RELATIONAL SEMANTICS 
ao 
a i 
o b\ 
a 2 CL 3 
O b2 
ob3 
0&4 
. V 
I 
0 64 • • • 1 
Fig. 8.17. 
Exercise 8.21 Let C\ be the class of all differentiated frames for L2 whose 
underlying Kripke frames have the form shown in Fig. 8.17 and L\ = LogCi. 
Prove that L\ has no immediate predecessor in the interval [L2,L\\. (Hint: use 
the result of the preceding exercise.) 
Exercise 8.22 Prove that the logic L\ in the preceding exercise does not have 
an independent axiomatization. (Hint: see Section 4.5.) 
Exercise 8.23 Show that for every normal logic L € [S3,Grz] and every intu- 
itionistic formula T(r) \~*L T(<£>) iff T bint ip. 
Problem 8.1 Are all si-logics complete with respect to topological spaces? 
8.9 	Notes 
The approach to constructing the adequate semantics for non-classical logics 
presented in Section 8.1 (it should be clear that it works for, say various kinds of 
polymodal logics) is similar to Henkin’s approach to establishing completeness 
of higher order classical predicate calculi. The reader can find details of Henkin’s 
method and references in Church (1956). Here we note only that by imposing 
restrictions on possible valuations in models we in fact introduce interpretations 
for the unary predicates representing the truth-sets of propositional variables— 
for that reason general frames are sometimes called first order frames. This makes 
impossible various “negative” effects of Chapter 6 because we are not able any 
more to change arbitrarily valuations. Moreover, it is not hard to prove the 
following analog of the Lowenheim-Skolem theorem: for every general frame # 
and a point a; in it, one can select a countable general subframe 0 of # containing 
x such that 0 validates the same formulas as # and a formula is refutable at x 
in 0 whenever it is refutable at x in #. 
The approach outlined in Section 8.2 was developed first by Jonsson and 
Tarski (1951, 1952). In fact, their results were much more general; for 
example, they added to Boolean algebras collections of arbitrary n-ary operations 
satisfying some natural properties like conditions (ii) and (iii) in Theorem 7.44. 
However, chronologically (even in spite of Kripke’s (1963a) claim that he had 
independently obtained the main result of Jonsson and Tarski (1951)) the 
semantics of general frames for modal logics was explicitly formulated only by 
Makinson (1970). Thomason (1972b) proved completeness theorems for tense 

NOTES 
283 
(and so modal) logics with respect to this semantics (which he called first 
order) and introduced the notion of refined frame and the operation of refinement. 
Goldblatt (1976a, 1976b) contains an extensive and systematical study of the 
semantics of general frames: first order frames, subframes, homomorphisms, 
disjoint unions, ultraproducts, compactness and semantical consequence, descriptive 
frames, the categories of descriptive frames and modal algebras, inverse limits 
of descriptive frames, modal axiomatic classes, d-persistent formulae, first order 
definability—these are a few titles of sections in Goldblatt (1976a, 1976b) 
showing the directions of investigations. Many results in Sections 8.4 and 8.5 were 
taken from this paper. It is hard to say who was the first to introduce explicitly 
general intuitionistic frames—in any case it was not too difficult having at hand 
duality theory for modal logics and the connection between pseudo-Boolean and 
topological Boolean algebras discovered by McKinsey and Tarski (1946) (we 
discussed it in Section 8.3). The earliest references we know are Esakia (1974) and 
Rautenberg (1979). 
A topological approach to the Stone-Jonsson-Tarski representation and 
duality theory was developed by Esakia (1974, 1979b, 1985) and Sambin and Vaccaro 
(1988). Note also that general frames can be introduced in the case of 
neighborhood semantics; see Dosen (1988). 
In view of the duality between algebras and descriptive frames (and the 
truth-preserving operations on them), Birkhoff’s theorem opens a way for 
solving the problem of characterizing modally and intuitionistically definable classes 
of (Kripke, general, refined, etc.) frames. Goldblatt and Thomason (1974), van 
Benthem (1975, 1989), Goldblatt (1976a, 1976b) found various conditions (of 
closure under certain operations) for a class of frames to be modally definable. 
For example, as was shown by Goldblatt and Thomason (1974), if a class C of 
Kripke frames is closed under elementary equivalence then C is modally definable 
iff C is closed under the formation of generated subframes, disjoint unions and 
reductions, while its complement is closed under ultrafilter extensions (for the 
definition see Section 10.2). The case of finite frames is of special interest here. 
Birkhoff’s theorem (for a “finitized” variant of it see Banaschevski, 1983) 
suggests that as a condition for the modal definability of a class of finite frames one 
should take the closure of the class under finite disjoint unions, reductions and 
generated subframes. However, Example 8.8 shows that this is not enough. It is 
not hard to see that essential in this example is the fact that the frames under 
consideration are not transitive. Indeed, as was shown by Rodenburg (1986) (for 
intuitionistic frames) and van Benthem (1989), in the case of transitive frames 
the conditions above are enough (see Exercise 9.34). In the general case we need 
also the condition of closure under so called local p-morphic images; see van 
Benthem (1989). Much less is known about modal definability of classes of frames 
with actual worlds, although the available variants of Birkhoff’s theorem for this 
case (in particular, Theorem 7.81) give some hope for a progress in this 
direction too. For definability of frame classes by formulas in richer languages see, for 
instance, Goranko (1990). 
The description of finitely generated universal frames for K4, presented in 

284 
RELATIONAL SEMANTICS 
Sections 8.6 and 8.7, was obtained in essence by Segerberg (1971) and after 
that was rediscovered in various forms. An important step in understanding 
the constitution of such frames was made by Shehtman (1978a) who gave a 
general method of constructing the universal frames of finite rank for finitely 
approximable logics with transitive frames and illustrated it for S4, Grz and 
Int. Similar results were obtained by Bellissima (1985a). 
Needless to say that if we know the detailed structure of the universal frames 
for a logic, we have a powerful instrument for studying both the logic itself and 
the lattice of its extensions. We shall take advantage of it in further chapters. In 
particular, the solution to the admissibility problem for inference rules, obtained 
in Section 16.7, would not be possible without this instrument. And the results 
on m-reducibility in Section 13.1 are based in essence upon considering the form 
of the upper part of the m-universal frames for the corresponding logics. 
However, there are still a lot of open problems concerning universal frames. 
Actually, the picture is more or less clarified only for extensions of K4 and Int. 
And even here the behavior of the universal frames for logics that are not finitely 
approximable may turn out to be rather unexpected; see, for instance, Chagrov 
(1994b). In the “nontransitive” case, only for very few logics, in particular K, 
universal models have been described. A perspective (though not easy) direction 
is to consider the constitution of the universal frames for some extensions of 
K 0 tran, while for extensions of KTB = K 0 re 0 sym this problem seems 
to be very hard. It is no accident that so little is known of ExtKTB. One of 
the strongest facts here is that there are infinitely many pretabular logics in 
NExtKTB. It is known, for instance, that the universal frame of rank 2 for 
KTB © □ 2p -> D3p is infinite (Byrd 1978), and we have no information about 
its universal frame of rank 1. 
The problem of describing universal frames of finite rank for polymodal and 
tense logics is much more complicated. Even in the transitive case the situation 
here resembles that in NExtK. 
Another interesting problem is to describe atoms (the corresponding 
formulas, to be more precise) of n-generated free algebras in varieties of modal (tense, 
etc.) algebras. In accordance with atomicity, atomless of such algebras we call 
the corresponding logics n-atomic, n- atomless, etc. Here are some examples: 
• K is n-atomic, for every n; 
• D is n-atomless, for every n > 0 (there are no 0-atomless modal logics); 
• there are normal modal logics which, for any n > 0, are neither n-atomic 
nor n-atomless. 
These results were obtained by Bellissima (1984). For finitely approximable logics 
in NExtK4, he proved also that all of them are n-atomic for every n. However, 
it is not clear whether the finite approximability is essential here. Bellissima 
(1991) considers similar problems for tense logics. Recently Wolter (1997) has 
connected atomicity of finitely generated free algebras for polymodal logics with 
splittings of the corresponding lattices of logics (see Section 10.5). In particular, 

NOTES 
285 
he proved that if all finitely generated free algebras for L are atomic then L is 
characterized by the class of frames that split NExtL. 
Theorems 8.67, 8.85 and 8.92 were proved by Makinson (1971), Segerberg 
(1971) and Anderson (1972), respectively. 

9 
CANONICAL FORMULAS 
In Sections 2.5 and 3.5 we characterized the geometry of Kripke frames validating 
some intuitionistic and modal formulas by imposing first order conditions on 
their accessibility relations. However, as was shown in Section 6.2, there exist 
formulas which have no first order equivalents. In this chapter we try another, 
purely frame-theoretic approach to the characterization problem which uses such 
notions as subframe, reduction, etc. Unfortunately, this approach is not universal 
either. But its limitation is of a different kind: it characterizes only transitive 
general frames, but for every modal and intuitionistic formula. So all frames in 
this chapter are assumed to be transitive. 
The characterization to be obtained below can be roughly described as 
follows. Given a modal or intuitionistic formula ip, one can effectively construct 
finite rooted frames Si? • ■•,3n such that a general frame 0 refutes ip iff there 
is a (not necessarily generated) subframe of 0 which is reducible to one of 
and satisfies some other natural conditions. Conversely, with every finite rooted 
frame # we can associate a formula—call it canonical—explicitly saying: “I am 
refuted in a frame iff it contains a subframe reducible to $ and satisfying those 
conditions”. As a result, we obtain a powerful language of canonical formulas: 
they axiomatize all logics in ExtK4 and Extint and bear explicit information 
about the constitution of their refutation frames. 
9.1 Subreduction 
In this section and the next one we give a few examples revealing certain 
fundamental principles of the constitution of transitive refutation frames for modal 
and intuitionistic formulas. 
Example 9.1 Let us consider once more the Grzegorczyk formula grz (which, 
as was shown in Section 6.2, is not first order definable). In Examples 3.22 and 
3.24 we constructed its two simplest transitive countermodels on the frames • 
and (oo). On the other hand, Proposition 3.48 asserts that a Kripke frame # 
refutes grz iff it contains either an irreflexive point or a proper cluster or an 
infinite ascending chain of distinct points. Since every infinite ascending chain is 
reducible to the two point cluster (see Example 3.14), we can reformulate this 
observation as follows: # 9rz Iff there is a subframe of # that is reducible 
either to • or to (°°). 
In order to extend this characterization to general frames, we require the 
following definition. 

SUBREDUCTION 
287 
Given modal frames # = (W, P, P) and (5 = (V,S,Q), a partial (i.e., not 
completely defined, in general) map / from W onto V is called a subreduction 
(or a partial p-morphism) of $ to (5 if it satisfies the conditions (R1)-(R3) in 
Section 8.4 for all x and y in the domain of / and all X G Q. In this case we 
say also that / subreduces $ to (5, $ is subreducible to (5 (by /) and (5 is an 
(f-) subreduct of #. The domain of / will be denoted by dom/. If # and (5 are 
Kripke frames then the subreducibility of $ to (5 means that there is a subframe 
of 'S which is reducible to (5. Note also that if (5 is a finite Kripke frame then 
(R3) is equivalent to 
(R4) \/z eV f~1(z) g P. 
A frame (5 = (V,S,Q) is called a subframe of $ = (W, P, P) if V C W and the 
identity map on V is a subreduction of J to (5, i.e., if S is the restriction of R 
to V and Q C P. Note that a generated subframe (5 of $ is not in general a 
subframe of since V need not be in P; however, if V G P then (5 is a subframe 
of #. More generally, suppose V is a non-empty subset of W in # = (W1P, P) 
such that V e P and S is the restriction of R to V. Define a set of possible 
values Q in the space V by taking 
Q = {XCV: XeP}. 
Q is obviously closed under the Boolean operations and for every X e Q, 
Xis = VDXlReQ, 
so that 0 = (V,S,Q) is really a modal frame. Since by the definition, Q C P, 
the frame (5 is a subframe of #. We call it the subframe of # induced by V. Thus, 
an /-subreduct of # is a reduct of the ft’s subframe induced by dom/. 
Example 9.2 Let $ = {W,R) and (5 be the Kripke frames shown in Fig. 9.1. 
Then the map / defined by 
{a if i is even 
b if z is odd 
undefined if i = u 
is a subreduction of $ to (5. Observe that # is not reducible to (5. If we define 
in J the set P of possible values consisting of finite sets of natural numbers 
and complements to them in the space W, then the frame $ = (W,R,P) is not 
subreducible to (5. For otherwise, when, say, / is a subreduction of $ to 0, we 
would have /-1(a) G P and /_1(6) G P, which is impossible because /_1(a) and 
/_1(6) are disjoint and infinite. 
Proposition 9.3 A general frame $ refutes grz iff $ is subreducible either to 
• or to (oo). 

288 
CANONICAL FORMULAS 
• 3 
62 
1 
S oO 
Fig. 9.1. 
Proof (=>) Suppose grz is refuted in # = (IT, R, P) under some valuation. 
Then the set X = {x G IT : x ^ grz} G P is non-empty. Let us consider the 
set X — XI G P which consists of all final irreflexive points in X, if any. 
If X — XI 7^ 0 then the map / defined by 
for every a; € IT, is a subreduction of $ to •. If X — X j = 0 then for every 
x € X, there is x' G fi X. Hence xf |= 0(p —» Dp) —» p, x' ^ p and so 
x' ^ 0(p —» Dp). But then the set 
Y = {y eW : y\= 0(D(p -+ Op) -> p), y ft p, y ft DP} 6 P 
is non-empty, Y C X[ and IC Y[. Therefore, the map / defined by 
for every x G IT, is a subreduction of # to the cluster with two points a and b. 
(<S=) Suppose / subreduces $ to •. Then dom/ G P is an antichain of 
irreflexive points. Define a valuation 2J in # by taking 2J(p) = IT — dom/. The reader 
can easily check that grz is false under 2J at every point x G dom/. 
Suppose now that / is a subreduction of $ to the cluster with two points a 
and b. Then we define a valuation 2J in # by taking, for instance, 
We show that $ ft □ (□(p —> Op) —► p) —► p, for every x G /_1(a;). By the 
definition, we have x ^ p. Suppose that x ft D(D(p Op) —» p). Then there 
is y G such that y |= □ (p —» Dp), y ft p and so y G /_1(a). By (R2), there 
is z G yT such that z G /_1(6). But then z |= p —» Dp, z |= p and so z |= Dp, 
• if x G X - XI 
undefined otherwise 
f(x) = { b 
a if x G X 
b if x G Y 
undefined otherwise 
a 
%(p) = W-r1(a). 

SUBREDUCTION 
289 
n + 1 
Fig. 9.2. 
which is impossible, since by (R2), there is xf G z\ Of 1(a) and we must have 
simultaneously both x' \= p and x' P* □ 
In the same manner one can establish the characterizations presented in 
Table 9.1, where each * is to be replaced by • and o (for instance I represents four 
frames: • , o , • , £ ). To be more exact, we have 
Proposition 9.4 A transitive modal frame $ refutes a formula in the left-hand 
side of Table 9.1 iff'S is subreducible to one of the frames in the same line of the 
right-hand side. 
Proof Exercise. • □ 
In the intuitionistic case the definition of subreduction becomes somewhat 
more complicated. Given intuitionistic frames $ = (W,R,P) and 0 = (V,S,Q), 
a partial map / from W onto V is called a subreduction of $ to 0 if it satisfies 
(Rl) and (R2), for all x,y G dom/, and also the following condition: 
(R3') yx eQ f~1(X)leP 
where Q = {V — X : X G Q} and P = {W — X : X G P}. For a completely 
defined / satisfying (Rl) and (R2) the condition (R3') is clearly equivalent to 
(R3) and so every reduction is also a subreduction. If (5 is a finite Kripke frame 
then (R3') is equivalent to 
(R4') Vzg V /^WlGP. 
& is a subframe of J if k(5 is a subframe of and the identity map on V is a 
subreduction of J to (5. 
Proposition 9.5 An intuitionistic frame $ refutes a formula in the left-hand 
side of Table 9.2 iff $ is subreducible to one of the frames in the same line of the 
right-hand side. 
Proof We consider only bwn = —► VjViPj) an(i leave the other 
formulas to the reader. 
(=>) Suppose $ = (W,R,P) refutes bwn under some valuation. Define a 
partial map / from W onto the set of points in the frame (5 in Fig. 9.2 by taking 
{0 if x y=. bwn 
i ii 0 < i < n + 1, x \= Pi and x Y=. Pj 
undefined otherwise. 

290 
CANONICAL FORMULAS 
Table 9.1 Characterizing refutation frames: subreduction. 
Formula ip 
£ ^ (p iff £ is subreducible 
to one of the following frames 
T 
□ 
• 
□ (□p —> p) —> Dp 
0 
p —> DOp 
I (4 frames) 
dp) -»p) -»p 
• © 
v 
* (6 frames) 
v ? 
¥ * (8 frames) 
□ (□+p —» g) V □ (□+# —> p) 
□ (□p —► #) V □ (□<7 —> p) 
ODp —> Dp 
I £ <\/> (4 frames) 
□p » p 
0 
• £ © 
? 
□p 
o • 
I v 
o • (4 frames) 
□ (□p —> p) A ODp —» Dp 
□ (□(p —> Dp) —» p) A ODp —» p 
i i 
• o (oo) (6 frames) 
p —> D(Op —> p) 
* (oo) (9 frames) 
n+1 
bwn 
V? 
¥ (2n + 4 frames) 
j n 
|1 
bdn 
10 (2n+1 frames) 
rooted frames with n + 1 distinct 
Gblt'ri 
points accessible from their roots 

SUBREDUCTION 
291 
Table 9.2 ‘Characterizing refutation frames: subreduction. 
Formula ip 
£ ^ (p iff £ is subreducible 
to one of the following frames 
< 
J 
^3 
o 
* 
hq -> p) -> (((p ->q) -> p) ->• p) 
V i 
(p -> q) v (q ->p) 
V 
o 
5 n 
bdn 
i1 
o 0 
n+1 
bwn 
o P- o 
V 
bcn 
rooted frames with n + 1 points 
Since for allz e {1,..., n + 1}, if x bwn then x Pi and there exists yi e x] 
such that yi |= Pi and ^ Pj for j ± i, / is a surjection satisfying (Rl) and (R2). 
Besides, we have /_1(0)| = {x : x\A bwn} e P and for every i e {1,..., n + 1}, 
f~l{i)i = {x : x pi —> \f j^iPj} e P. So f satisfies (R4') as well. 
(<=) Suppose / is a subreduction of ^ to 0. Define a valuation 23 in # by 
taking, for every i G {1,..., n + 1}, 
W(pi) = W-{Jr1(j)leP. 
Since by (Rl), f~1{i) H f~1{j) | = 0 for every i ^ j, we have x \= Pi and 
x ^ VjjkiPj f°r each x € whence x pi —> \f j^Pj- And since by (R2), 
/_1(0) Q PC? /_1(0we have x ^ bwn for all x e /_1(0). □ 
In the intuitionistic case there is a nice algebraic counterpart of the notion 
of subreduction. Given two pseudo-Boolean algebras 21 = (A, A, V, —_L) and 
23 = (B, A, V, —_L) and a non-empty set O C {A, V, —_L}, an injection / from 
B into A is called an O-isomorphism of 23 in 21 if / preserves all the operations 
in O. If B C A and the identity map on B is an O-isomorphism of 23 in 21 then 
we call 23 an O-subalgebra of 21. In this case the operations from O in 23 are just 
the restrictions of the corresponding operations in 21 to 23. 
The same notions of O-isomorphism and O-subalgebra may be defined of 
course for modal algebras, but this time O C {A, V, —_L, □}. Denoting the 

292 
CANONICAL FORMULAS 
operations A, V, —_L, □ by the letters C, D, I, N, B, respectively (N stands for 
“negation”, B for “box”), we shall write “IC-isomorphism” instead of “{—>, A}- 
isomorphism”, etc. 
Example 9.6 Let 21 be the pseudo-Boolean algebra shown in Fig. 9.3. Then 
the algebra 23 in Fig. 9.3 is an IC-subalgebra of 21, but neither an ICN- nor 
an ICD-subalgebra, since 21 and 23 have distinct zero elements and distinct V. 
Fig. 9.3 shows also that the dual 21+ of 21 is subreducible (but not reducible) to 
the dual 23 + of 23. 
Theorem 9.7 Suppose $ = (W,R,P) and 0 = {V,S,Q} are intuitionistic 
frames and f a subreduction of$ to 0. Then the map /+ defined by 
f+(x) = w-ri(v-x)i 
for every X G Q, is an IC-isomorphism o/0+ in Sr+. 
Proof Observe first that by (R3'), /+(X) G P for every X € Q. Notice also 
that for every x G W and X G Q, 
x G /+(X) iff Vy G dorn/ (xRy - f(y) G X). (9.1) 
It follows from (9.1) and (Rl) that for every X G Q and y £ X, we have 
f~x(X) C /+(X) and f~1(y) fl /+(X) = 0. Therefore, /+ is an injection from 
Q in P. 
Let us show now that /+ preserves D and D, i.e. suppose X, Y G Q and prove 
that 
f+{X n Y) = f+(X) n f+(Y) 
and 
f+(XDY) = f+(X)Df+(Y). 
The former equality follows from the definition of /+. (Note by the way that 
/+ does not preserve U; in general we have only /+(X U Y) 3 /+(X) U /+(T). 
Besides, /+(0) may be non-empty.) 
Let x G /+(X D y). By (9.1), this is equivalent to 
Wy ex T D dom / Vu G f(y) | (u G X -> u G Y). (9.2) 
Suppose that xRz, z G /+(X) and show that z G /+(T). Indeed, otherwise we 
must have some y G z] such that f(y) is defined, but is not in T, which by 
(9.1) and (9.2), is impossible. Therefore, z G /+(T) and so x G /+(X) D /+(T). 
Conversely, suppose x G /+(X) D /+(T), i.e., 
Vz G xt (z G f+(X) -> z G /+(T)), (9.3) 
and prove (9.2). Let y e xT H dom/, u G /(y)| and u G X, but u $Y. Then by 
(R2), there is z e y^ such that /(z) = u, i.e., /(z) G X and f(z) $ Y. As we 

SUBREDUCTION 
293 
Fig. 9.3. 
have already observed, this means that z G f*(X) and z gL /+(F), contrary to 
(9.3). □ 
As a consequence we obtain the following truth-preservation result for intu- 
itionistic IC-formulas, i.e., formulas containing no occurrences of V and 1; such 
formulas are called also disjunction and negation free formulas. If a formula has 
no occurrences of V (of _L) then it is called a disjunction (respectively, negation) 
free formula. It should be emphasized that O was defined via _L; so negation 
free modal formulas contain no diamonds. 
Corollary 9.8 Suppose $ and 0 are intuitionistic frames and $ is subreducible 
to (5. Then $ |= ip implies <5 \= </? for every disjunction and negation free formula 
<P- 
Using the method developed for the proof of Theorem 8.71, one can prove a 
theorem that is dual to Theorem 9.7 (see Exercise 9.2). The algebraic meaning 
of the notion of subframe in the modal case is explained in Exercise 9.5. 
Given intuitionistic or modal frames # = (W,R,P) and (5 = (V,S,Q), a 
subreduction / of # to (5 is called dense if dom/f H dom/j = dom/, i.e., if 
Vx G W Vy, z G dom/ (yRxRz —> x G dom/). 
Theorem 9.9 Suppose # = (W,R,P) and 0 = (V,S, Q) are intuitionistic or 
modal frames, f is a dense subreduction of$ to (5 and W = domf |. Then there 
is an ICD- or, in the modal case, ICDB-isomorphism /+ o/0+ in Sr+. 
Proof Let us consider first the modal case. Define a map /+ from Q into P by 
taking, for every X G Q, f*{X) = W — f~l(V — X). It follows from (R3) that 
/+(X) G P. Since for every x G W and every X G Q, 
x G /+(A) iff x £ dom/ or f(x) G X, (9.4) 
/+ is an injection. Using (9.4), one can readily check that /+ preserves n, U and 
D. Suppose X G Q and show that /+(DX) = D/+(A). If x G /+(DX) then, by 

294 
CANONICAL FORMULAS 
(9.4), either x ^ dom/ or x G dom/ and z G X for every z G f(x) j. Take an 
arbitrary y G x| and show that y G /+(X). If x # dom/ then y $ dom/, since 
5 is generated by dom/ and / is dense, and so y G /+(X). If x G dom/ and 
G dom/ then, by (Rl), we have f(x)Sf(y), whence f(y) G X and y G /+(X). 
Conversely, suppose x G D/+(X), i.e., for every y G x|, either 2/ ^ dom/ or 
/(p) G X. It follows by (R2), that either x $ dom/ or x G dom/ and z £ X for 
every z G f(x)Therefore, x G /+(DX). 
As to the intuitionistic case, we define /+ as in Theorem 9.7. So it suffices 
to verify that for all X, Y G Q, /+(X U7) = /+(X) U /+(T). The inclusion 
/+(Xuy) 3 /+(X)U/+(y) follows directly from (9.1). Suppose x G /+(Xuy). 
If x ^ dom/ then, by the density of /, we have 2/ ^ dom/ for every y G x|, and 
so x is in /+(X) as well as in /+(T). And if x G dom/ then, by (9.1), /(x) G X 
or /(x) G y, whence x G /+(X) U /+(T). □ 
As a consequence we obtain one more truth-preservation result. 
Corollary 9.10 If $ is densely subreducible to 0 then for every negation free 
formula tp, $ \= tp implies (5 (= ip. 
9.2 Cofinal subreduction and closed domain condition 
Transitive refutation frames for the formulas in Tables 9.1 and 9.2 have a rather 
simple structure. Roughly, to construct all refutation frames for such a formula, 
we can first take the frames reducible to one of its refutation patterns in the 
table and then insert into them new points at any places we want, provided, of 
course, that the accessibility relation between the old points remains the same. 
However, there are modal and intuitionistic formulas whose refutation frames 
are constructed in a more complex way. 
Example 9.11 Let us analyze the constitution of transitive refutation frames 
for the McKinsey formula ma = DOp —» OUp. It follows from Proposition 3.46 
that the simplest Kripke frames refuting it are again the degenerate cluster • and 
the two point cluster R. And again its every refutation frame is subreducible 
either to • or to ©. Indeed, suppose that ma is false in 5 = (W,R,P) under 
some valuation and let 
is obviously a subreduction of $ to •. And if X - X[ = 0 then we define a map 
/ from $ onto the frame 0 in Fig. 9.1 by taking 
X = {xeW: x ma) G P. 
If X — X[ ^ 0 then the map / defined by 
• if x G X - XI 
undefined otherwise 
/(x) = { b 
a 
if x ^ ma and x p 
if x ^ ma and x |= p 
undefined otherwise. 

COFINAL SUBREDUCTION AND CLOSED DOMAIN CONDITION 
295 
It is clear that / satisfies (Rl) and (R3), and the fact that it satisfies also (R2) 
follows from the considerations in Section 3.5. 
However, the subreducibility of ^ to • or © is only a necessary condition 
o 
for $ ma, but not a sufficient one. For the frame (°o) is subreducible to R 
but, according to Proposition 3.46, validates ma. 
Let us take a closer look at the subreductions / defined above. In the former 
case dom/ contains some final points in #, dead ends, to be more exact (for if 
x G X - X[ is not a dead end then xRy, for some y G W, whence y (= DOp, 
y ODp and so y € X, which is a contradiction). In the latter one points in 
dom/ are not necessarily final in #, but the whole set dom/ behaves itself like 
a final point in the sense that there is no point in W which is seen from dom/ 
and does not see dom/ itself. 
This observation motivates the following definitions. Given a modal or 
intuit ionistic frame # = (W, R, P), a set X C W is said to be cofinal in # if X|C X[. 
A subframe 0 of # is cofinal in # if its set of worlds is cofinal in #. A 
subreduction / of $ to 0 is called co final if, for every point x in #, x G dom/j implies 
x G dom/j, i.e., if dom/ is cofinal in #. If there is a cofinal subreduction of $ to 
0 then we say # is cofinally subreducible to 0 or 0 is a cofinal subreduct of Sr. 
o 
Example 9.12 (°°) is a subframe of @, but not cofinal. The frame # in Fig. 9.1 
is subreducible to R, but not cofinally, since uj $ dom/j for any subreduction 
/ of £ to (°°). 
Proposition 9.13 A frame $ = (W,R,P) refutes the McKinsey formula iff it 
is cofinally subreducible either to • or to R. 
Proof (=>) was actually established in Example 9.11. 
(4=) Suppose / is a cofinal subreduction of # to •. Then dom/ is a non-empty 
set of dead ends in $ and so ma is false at any point in dom/ under any valuation 
in 
Suppose now that / is a cofinal subreduction of # to the cluster with two 
points a and b. Define a valuation 2J in # by taking 
V3(p) = W-f-1(a). 
Then for each x G /-1(a), we have x |= DOp, x ODp and so x ma. For 
otherwise either x ^ DOp or x |= ODp. In the former case y Op for some 
y G #T, from which z ^ p for all z G yj, i.e., y| C f~1(a). It follows that 
yT H /_1(6) = 0 and hence, by (R2), y]_n dom/ = 0, contrary to / being cofinal. 
In the latter case y |= Dp for some y G x] and so z |= p for all z G yT, i.e., 
pT H f~1(a) = 0, which is again a contradiction. □ 
In the same manner one can prove the following proposition; we leave it to 
the reader. 

296 
CANONICAL FORMULAS 
Table 9.3 Characterizing refutation frames: cofinal subreduc- 
tion. 
Formula <p 
S ^ <p iff S is cofinally subreducible 
to one of the following frames 
a. 
O 
T 
a, 
□ 
• 
□Op —> ODp 
• © 
0(Dp A q) —> D(Op V q) 
t £ (8 frames) 
I 'Ni/14 (8 frames) 
ODp —► DOp 
—ip V —i—ip 
V 
o 
n+1 
btwn 
o 6 
V 
Proposition 9.14 A transitive modal (or intuitionistic) frame # refutes a 
formula in the left-hand side of Table 9.3 iff # is cofinally subreducible to one of 
the frames in the same line of the right-hand side. 
In the intuitionistic case the notion of cofinal subreduction has a clear 
algebraic meaning. 
Theorem 9.15 Suppose that $ = (W,R,P) and (5 = (V,S,Q) are 
intuitionistic frames and f is a cofinal subreduction of $ to 3. Then there is an ICN- 
isomorphism f+ of 3+ in a homomorphic image of$+. 
Proof Let = (W\,R\,P\) be the subframe of $ generated by domf. It is 
clear that / is a cofinal subreduction of Si to 3. By Theorem 9.7, the map /+ 
defined by f+(X) = Wi~ f~l(V — X)l, for every X £ Q, is an IC-isomorphism 
of 3+ in #+. Moreover, f+ preserves 0 because the set domf = f~1(V) is cofinal 
in #!. So f+ is an ICN-isomorphism. It remains to recall that, by Theorem 8.57, 
is a homomorphic image of $+. □ 
Corollary 9.16 Suppose S and 3 are intuitionistic frames and S is cofinally 
subreducible to 3. Then for every disjunction free formula ip, S \= ip implies 
® b <p- 
The constitution of refutation frames for the formulas in Table 9.3 can be 
roughly described as follows. First we construct the frames S that are reducible 
to one of the refutation patterns for the given formula shown in the table and 
then insert into S new points at any places we want, but not above $. 

COFINAL SUBREDUCTION AND CLOSED DOMAIN CONDITION 
297 
Our next example shows that some places inside frames may also be “closed” 
for inserting new points. 
Example 9.17 Let us try to characterize the class of intuitionistic refutation 
frames for the weak Kreisel-Putnam formula: 
wkp = (~>p —> -*q V -ir) —> (-ip —> -iq) V (-ip —> ->r). 
Using, for instance, the semantic tableau technique, we first construct its simplest 
countermodel as depicted in Fig. 9.4. Then we observe that every frame # refuting 
wkp is cofinally subreducible to the frame 0 underlying this countermodel by 
the map / which is defined as follows: 
f{x) = 
0 if x |= -ip —> ->q V -ir, x (-■ p —> -*q) V (-ip 
1 if x |= -ip —> -yq V —ir, x\= -<p and x |= q 
<2 if x |= ->p —> -*q V -ir, x |= -ip and x )= r 
3 if x |= p or x |= -ip A -ig A -T 
undefined otherwise. 
.r) 
(The cofinality of / follows from the fact that / 1(i), for i = 1,2,3, is upward 
closed and /_1(0)TC |J<=1 Z""1 W1-) 
However, the cofinal subreducibility to 0 turns out to be only a necessary 
condition for $ ^ wkp. For the frame shown in Fig. 9.5 is cofinally subreducible 
to 0, but does not refute wkp. Indeed, suppose otherwise. Then there is a 
valuation in this frame such that ao |= ->p —> ->q V -ir, ai |= —«p, ai ^ 
a2 |= -*p and a2 T, whence a |= ->p —> -<(/ V -<r, a V -<r and soa^ —«p, 
i.e., there must be a point x G a| such that x |= p, but such a point does not 
exist. 
This argument shows in fact that the cofinal subreduction / of $ to 0 defined 
above satisfies the condition ->3x G dom/T /(x|) = {1,2}, which turns out to 
be the sufficient condition we need. For if / is a cofinal subreduction of $ = 
(W, R, P) to 0 in Fig. 9.4 satisfying it then we define 2J in # by taking 2J(p) = 
W - f-1({1,2})i, <B(q) = w- f~l{{2,3»x, fO(r) = W - /^({l, 3})|. It is easy 
to see that under this valuation x ^ -«p —► -<(/, y -ip —* -*r and z \= p, for every 
x G /_1(1), y G /_1(2) and z G /-1(3). Therefore, u (-<p —> -<q) V (-ip —> -<r) 
for every u G /-1(0). We must also have u |= -ip —> ->g V -ir, because otherwise 

298 
CANONICAL FORMULAS 
a i <22 as 
there is v G u] such that v \= and v V t, which is a contradiction, 
since the former means v ^ /-1(3)j and the latter implies, by the cofinality of 
/, that v G /-1(l)j n/_1(2)j, from which /(uf) = {1,2}. 
Thus, we can construct all refutation frames for wkp by taking first the 
frames 9) that are reducible to 0 by some / and then inserting into them new 
points anywhere but (i) not above 9) and (ii) not at such places where both 
/_1(1) and /-1(2) are seen, while /_1(3) is not seen. Figuratively speaking, the 
place or domain just below 1 and 2 in 0 is closed for inserting new points, while 
all other domains (e.g. below 1 or below 2 and 3) are open. 
Example 9.18 # refutes the density axiom □□ p —> □ p iff there is a subreduc- 
t° 
tion / of ^ to the frame A such that -Gx G dom/f /(x|) = {0}. (An equivalent 
characterization: # ^ deni iff there is a dense subreduction of $ to I). This 
time the domain just below 0 is closed for inserting. 
These examples motivate the following definition. Let 0 be a finite frame and 
2) a (possibly empty) set of antichains in 0. We say a subreduction / of # to 0 
satisfies the closed domain condition for 2) if 
(CDC) -0x G dom/T - dom/ 3d G 2) /(xT) = 
or, which is equivalent, if 
(CDC) x G domf] and /(x|) = Dj for some d G 2) imply x G dom/. 
Note that, by the definition, every subreduction satisfies (CDC) for 2) = 0. We 
denote by 2)^ the set of all antichains in 0. It follows also from the definition 
that a subreduction / of # to 0 satisfies (CDC) for iff / is dense. As an 
exercise we invite the reader to prove the following two propositions. 
Proposition 9.19 A modal transitive frame $ refutes a formula in the left side 
of Table 9.4 iff there is a cofinal subreduction (simply a subreduction for the first 

COFINAL SUBREDUCTION AND CLOSED DOMAIN CONDITION 
299 
Table 9.4 Characterizing refutation frames: closed domain condition. 
Formula ip 
S V iff $ is (cofinally) subreduci- 
ble to one of the following frames, 
with (CDC) for 2) being satisfied 
{ m 
Dnp —> □ mp (n > m > 1) 
t1 
• 0 35 = S“ 
DDp —> □(□+£> —> q) V □(□+(/ —> p) 
'V2 
V ® = {{1 >, {1,2}} 
□OT A □(□+p V □+“|p) —> Dp V D-ip 
v 
V 2) = & 
0 n 
0 • • • 0 
□OT A □ V”=0 °+(Pj A Aw -ft) ^ 
V?=0 D-(ft A A-Pi) 
V*-*. 
two formulas) of $ to one of the frames in the corresponding row of the right 
side, which satisfies (CDC) for 2) shown near the frame. 
Proposition 9.20 An intuitionistic frame S refutes a formula in the left side 
of Table 9.5 iff there is a cofinal subreduction (a plain subreduction for the first 
formula) of $ to one of the frames in the corresponding row of the right side, 
which satisfies (CDC) for 2) shown near the frame. 
In the next section we will show that in the same manner one can characterize 
transitive refutation frames for every modal or intuitionistic formula. But before 
that we obtain some simple general results on subreductions. 
Theorem 9.21 Suppose Si = {Wi,Ri,Pi), for i = 1,2,3, are modal or 
intuitionistic frames, fi is a (cofinal) subreduction of Si to S2 and f2 a (cofinal) 
subreduction of S2 to #3. Then the composition /3 = f2f\ is a (cofinal) 
subreduction of Si to S3 • 
Proof Since f\ and /2 are surjections, their composition is also a surjection. If 
x,y e dom/2/1 and xRiy then, by (Rl), f1(x)R2f{y) and f2fi{x)Rshfi(y)- If 
/2/1 {x)R$z for some x G W\ and z e W3 then, by (R2), there are v G W2 and 
y eWi such that fi(x)R2v, f2(v) = z and xRiy, fi(y) = v, i.e., /2/i(y) = z. 
Thus /2/i satisfies (Rl) and (R2). 
If our frames are modal and X G P3 then, by (R3), ffl(X) G P2 and 
fi1{f21{X)) = Jj2fi)~1{X) G Pi. In the_intuitionistic case, for X G P3 we 
have ff1(X)ie P2 and /f 1(/o’1(-X’)i)| € Pi- And using (R2), one can readily 
show that fil(f2l(X))l = /f (f21(X)l)l. Thus /2/1 satisfies also (R3) and so 
is a subreduction. 

300 
CANONICAL FORMULAS 
Table 9.5 Characterizing refutation frames: closed domain condition. 
Formula ip 
$ ^ tp iff $ is (cofinally) subreduci- 
ble to one of the following frames, 
with (CDC) for 2) being satisfied 
n+1 
bb„ 
2) = 2)» 
((—>—>3? —> p) —► p V =p) —> ->p V —i—<p 
2) = 2)“ 
Mr 2) = m.2U Mr 
(-.p^9Vr)-*(^->9)V(^-^r) V 2) = {{1,2}} 
3.1 92 
1 ft 
o- • • o o 
(-'P -> Vi=i _'9») -*• VLiC-'P -*• -,9») 
«-» Vi^iPj) -»viup* 
V ... V' 
2) = {{1,2}} 25 = {{!,...,*}} 
n+1 
o — o 
2) =2)# 
Now suppose /i, /2 are cofinal, x € Wi and yR\x for some y £ dom/2/i. 
Since /i is cofinal, we have either x £ dom/i or xPiZ for some z £ dom/i. In the 
former case /i(^)P2/i(x) and so, by the cofinality of /2, either fi(x) £ dom/2, 
i.e., x £ dom/2/i, or fi(x)R2V for some v £ dom/2, and then, by (R2), there is 
u £ such that xPitt and f\(u) = u, whence u £ dom/2/i. The latter case is 
considered analogously. □ 
Theorem 9.22 Suppose # = (W,iZ, P) and 3 = (V, 5, Q) are quasi-ordered 
modal frames and f is a (cofinal) subreduction of$ to 3 satisfying (CDC) for a 
set 2) o/ antichains in 3. Then there is a (cofinal) subreduction pf of p$ to p3 
satisfying (CDC) for p/D, where p2) = {pD : D £ 2)} and pD = {C(x) : x £ D}. 
Proof We define pf by taking, for any cluster C in #, 
f(C\ — I ^(/(x)) ^ x £ C an(f x £ dom/ 
^~ 1 undefined if C D dom/ = 0. 
(This definition does not depend on the choice of x £ C, since, by (Rl), C(f(x)) = 
C(f(y)) for every x,y € C D dom/.). Clearly, p/ is a partial map from pW 
onto pV satisfying (Rl) and (R2) and the cofinality condition as well, 
provided / is cofinal. Suppose X £ pQ. Then there is Y = Y | £ Q such that 

COFINAL SUBREDUCTION AND CLOSED DOMAIN CONDITION 
301 
X = pY. By (R3), rl{V -Y) G P, whence W - f~l{V -Y)leP and so 
pW - (pf)~l(pV - pY) I = p(W - rl{V - y)|) G pP. Thus, pf satisfies (R3') 
and it remains to verify that it satisfies (CDC) for p£). Suppose C e domp/f 
and p/(C|) = pD| for some pD G p£). Take any x G C. Then x G dom/| and 
/(x|) = whence by CDC), x G dom/ and so C G dompf. □ 
Theorem 9.23 Suppose that $ = (W, P, P) is a quasi-ordered modal frame, 
0 = (V, S) a finite intuitionistic frame and f a (cofinal) subreduction of pS to 
© satisfying (CDC) for a set D of antichains in 0. Then there is a (cofinal) 
subreduction h of a generated subframe of$ to <70 satisfying (CDC) for 2). 
Proof Let = (W7, P', Pf) be the subframe of $ generated by the set of points 
{x G W : C(x) G dom/}. With each v G V we associate the set 
= /(<?(</)) = v}l - U {yew'-. f{C(y)) = *}| . 
x€.V— 
Since by (R4'), pWf — / 1(x)| G pP' for every x G V, we have 
^-{i/Gr: /(C(y)) = x}i G Pf 
and so, by the finiteness of V, Xv G P'. 
Now we define a partial map h from Wl onto V by taking, for every x G Wf, 
, , v = f v if x G Xv 
' ' ~~ \ undefined otherwise. 
It should be clear that h is a subreduction of to <70; moreover, it is cofinal if 
/ is cofinal. Suppose 0 G !D and /i(x|) = $T- Then C(x) G dom/| and, by the 
definition of h, /(C(x))T= $T- Therefore, by (CDC), we have C(x) G dom/ and 
so x G Xf{C(x)) Q dom/i. □ 
Theorem 9.24 Suppose $ = (W, P,P) is an intuitionistic frame, 0 = (V,S) a 
finite quasi-ordered modal frame, 2) a set of antichains in 0 and f a (cofinal) 
subreduction of $ to p0 satisfying (CDC) for p£). 7%en £/&ere is a (cofinal) 
subreduction h of a generated subframe of to 0 satisfying (CDC) for 2), 
w/iere k == max{|C(x)| : x G V}. 
Proof According to the preceding theorem, there are a generated subframe 
= (W',Rf,Pf) of cr# and a (cofinal) subreduction g of to <7p0 satisfying 
(CDC) for p£). Let = (fcW', fcP', fcP') be the subframe of rgenerated 
by k x W'. Define a partial map h from kW' onto V as follows. If x G domp, 
g(x) = C G pU and C = {ai,..., an} C V then we take, for every i G A:, 

302 
CANONICAL FORMULAS 
(We remind the reader that n < k.) And if x £ domg then we regard h((x,i)) 
as undefined for every i e k. It is not difficult to verify now that h is a (cofinal) 
subreduction of rkS' to 0 satisfying (CDC) for 2). □ 
9.3 Characterizing transitive refutation frames 
This section shows how, given a modal or intuitionistic formula p, to construct 
a finite number of finite rooted frames 3i,..., &i and to select sets 2)i,..., Dn 
of antichains in them so that an arbitrary transitive frame # refutes p iff there 
is a cofinal subreduction of # to fo, for some i G {1,..., n}, satisfying the closed 
domain condition for 2)*. 
Let us begin with selecting closed domains. Suppose p is a modal or intu- 
itionistic formula and 01 = (0,11) a model. We say a non-empty antichain a in 
0 is an open domain in 01 relative to p if there is a disjoint saturated tableau 
ta = (rfl, Aa) with Ta U Aa = Subp and such that in the modal case, for every 
Oip e Suby?, 
(ODmI) Hip e ra implies ip G Ta; 
(ODm2) O'lp e Ta iff a 1= D+ip for all a G a; 
and in the intuitionistic case, for every %p G Suby?, 
(ODi) ip G Ta iff a |= ip for all a G a. 
Otherwise a is called a closed domain in 01 relative to p. 
The motivation behind this definition is as follows. Imagine that we have 
inserted a new (reflexive or irreflexive) point x just below an antichain a in 0, 
i.e., x sees only the points in a| and is accessible from some of those points in 0 
that see a. Is it possible to extend the valuation 11 to x so that the truth-values 
of p's subformulas remain the same at the old points in 0 under the extended 
valuation? The openness of a is just a natural sufficient condition for the existence 
of such an extension no matter what points in 0 see x (cf. Theorem 9.30 below). 
It is of importance that, given p and a finite antichain a, we can always effectively 
decide whether a is open or closed in finite 91 relative to p. 
Example 9.25 The antichain {1,2} is the only closed domain in the 
countermodel for tufep, depicted in Fig. 9.4. 
Example 9.26 Let us show that in any intuitionistic model every antichain is 
open relative to every disjunction free formula. Suppose that 91 = (0,11) is an 
intuitionistic model, p a disjunction free formula and a a non-empty antichain 
in 0. Let (ra, Aa) be the disjoint tableau defined by (OD/). We show that it is 
saturated. For A we have 
ipAx€Faift\/aeaa^=ipAx 
iff Va G a (a |= ip A a |= x) 
iff </> G ra and X e Ta. 
Suppose now that 'ip -h► x € Ta, but %p G Ta and x € Aa. Then a |= 'ip for every 
a G a and b ^ x f°r some b G a, whence b ^ 'ip —> x> which is a contradiction. 

CHARACTERIZING TRANSITIVE REFUTATION FRAMES 
303 
Proposition 9.27 Suppose 9t = (0,11) is a model and a, b are antichains in 0 
such that a| = b|• Then for every formula ip, a is open in 9t relative to ip iff b 
is open in 01 relative to <p. 
Proof One can take ta — t^. □ 
In view of this proposition we will not distinguish between antichains a and 
b such that aj_ = b| (he., the points in a generate the same clusters as those in 
b). 
Proposition 9.28 Every reflexive singleton a = {x} is an open domain in every 
model 01 relative to every formula ip. 
Proof The tableau ta = {{xp G Suby? : x |= xp}, {p G Suby? : x xp}) is clearly 
disjoint, saturated and satisfies (ODa/T) and (ODa/2) in the modal case and 
(ODj) in the intuitionistic one. □ 
Proposition 9.29 Suppose 01 = (0,11) is a modal model based on a quasi- 
ordered frame 0 and a is an antichain in 0. Then for every intuitionistic formula 
ip, a is open in 01 relative to T{ip) iff pa is open in pOt = (p0, pH) relative to ip. 
Proof (4=) Observe first that every subformula of T{p) is either an atom or 
has the form T{xp) for some ip G Sub ip or the form T{xp) —> T{x) for some 
ip —► x € Suby?. Now, given an intuitionistic tableau tpa — (Tpa, A pa) satisfying 
(OD/) for ip, we define a modal tableau ta = (rfl, Afl) as follows. First we put 
all ip's variables in Ta, then put T{xp) in Ta if 'ip eTp* and in Aa if xp e A pa, 
and finally we put T{xp) —> T{x) i*1 Aa if T{xp) G Ta, T{x) G Aa and put it in Ta 
otherwise. Clearly, ta is a disjoint saturated tableau and Ta U Aa = SubT{p). 
Suppose Uxp* e Ta. Then either 'ip' is a variable or 'ip' = T{xp) —> T(x). By 
the definition, in the former case xp' G Ta. As to the latter one, assume xp' G Afl, 
which means that xp G Tpa and x £ ^pa- Therefore, a ft xp —> x for some 
a G pa, and so xp —> x £ Apa, whence T(xp —> x) = £ Aa, which is a 
contradiction. Thus, xpf G Ta and ta satisfies (ODmI)- To establish (ODa/2), 
suppose Uxpf = T{xp) for some xp G Suby?. Then we have 
Dxp' G Ta iff xp e Tpa by the definition 
iff Va G pa a ]= xp by (OD/) 
iff Va G a a ]= T{xp) by Lemma 8.28 
iff Va G a a |= D+xp' since 0 is reflexive. 
(=>) Now, given a modal tableau ta = (ra,Aa), we define an intuitionistic 
tableau tpa = {Tpa, A pa) by taking, for every xp G Suby?, xp G iff T{xp) G Ta 
and A pa = Suby? - Tpa. One can readily verify that tpa is saturated. To prove 
that tpa satisfies (OD/), it suffices, by Lemma 8.28, to show that T(xp) G Ta iff 
Va G a a \= T{xp), which can easily be done by induction on the construction of 
xp. □ 
Now we prove a theorem which shows that the notion of closed domain is 
consistent with the closed domain condition. 

304 
CANONICAL FORMULAS 
Theorem 9.30 Suppose 01 = (0,11) is a finite (modal or intuitionistic) model, 
ip a (modal or intuitionistic) formula and 2) the set of all closed domains in 01 
relative to ip. Then for any (modal or intuitionistic) frame $ = (W, R, P), which 
is cofinally subreducible to 0 = (V, S) by some map f satisfying (CDC) for'D, 
there is a model OH = (#, 03) such that, for any x G dom/ and any xp G Sub(p, 
(OH, x)\=rp iff (01, f(x)) |= xp. 
Proof First we reduce the intuitionistic case to the modal one. Given an 
intuitionistic model 01 = (0,11), we construct the modal model <791 = (<70,il). 
By Proposition 9.29, the set of closed domains in <791 relative to T(ip) 
coincides with 2). By Theorem 9.23, there is a cofinal subreduction ft, of a generated 
subframe of cr# to <70 satisfying (CDC) for 2) and such that f(x) = h(x), for 
every x G dom/. So if we prove our theorem for the modal case, we shall have 
a model 9H based on <7# such that, for every x G dom/ and every xp G Sub<p, 
(9H, x) |= T(xp) iff (<791, f{x)) |= T(xp), and so, by Lemma 8.28, (p9H, :r) |= xp iff 
(<*,/(*)) 
Now, considering the modal case, without loss of generality we may assume 
that dom/t = W. Define a valuation 93 in # as follows. If x G dom/ then we 
take x |= p iff f(x) |= p, for every p G Var<p. If x £ dom/ then /(x|) ^ 0, 
since / is cofinal. Let a be an antichain in 0 such that a| = f{x |). By the 
closed domain condition, a is an open domain in 91 and so there is a tableau 
ta = (ra,Aa) satisfying (OD^l) and (ODm2). Then we take y |= p iff p G Ta, 
for every y £ dom/ such that /(p|) = f(xf). 
Let us first prove that 93 is well-defined, i.e., 93(p) = {x G W : x |= p} is in P 
for every variable p. 93(p) can be represented as the union of the following two 
sets X and Y: 
X = {x G dom/ : x (= p}, Y = {x £ dom/ : x\= p}. 
According to (R4), we have X G P. By the definition of 93, if x,y £ dom/ 
and /(x|) = /(p|) then x f= p iff y f= p. So, since 0 is finite, there is only a 
finite number of points pi,..., yn & dom/ such that Y = Z\ U ... U Zn, where 
= {z £ dom/ : /(z|) = /(piT)}. Let A{ = and Bi = V - A{. Then we 
have 
Zi = D n - U r\b)l n - dom/ € p. 
a€Ai b€Bi 
Therefore, Y G P and 93(p) = X U Y G P. 
Now by induction on the construction of xp G Sub(p we show that 
• for x G dom/, x ]= xp iff f(x) |= xp; 
• for re ^ dom/, x ]= xp iff xp G Ta, where a is the open domain in 91 associated 
with x. 
The only non-trivial case is xp = Let x G dom/. If x ^ then y ^ x f°r 
some y G x]. Suppose y G dom/. Then, by the induction hypothesis, /(p) ^ x 
and so f(x) ^ □%, since f(x)Sf(y). Suppose y ^ dom/ and b is the open 

CHARACTERIZING TRANSITIVE REFUTATION FRAMES 
305 
domain in 01 associated with y. By the induction hypothesis, x € A& and so, 
by (ODmI), Ox € At, and, by (ODa/2), 6 ft Q+x for some 6 e b. Therefore, 
/(x) ^ because f(x)Sb. Conversely, if f(x) ft Dx then there is z e V such 
that f(x)Sz and z ft X- By (R2), there is y G x| for which /(y) = z\ hence 
y ft x and so x ft Dx- 
Suppose now that x $ dom/ and a is the open domain in 01 associated with 
x. If x f= Dx then y f= x for all V € Therefore, by the induction hypothesis, 
z |= x for aH 2 € at, and so a |= D+x for every a e a, i.e., dx G Ta. To 
prove the converse, suppose Dx G Ta but x ^ dx- Then there is y e x| such 
that y ^ x* R V € dom/ then /(y) ^ X and so o ^ n+x for some a G a, 
which is a contradiction. If y £ dom/ then, as we have seen, z ft d+x for some 
2 € /(yt) £ /(x|), and so again a ft d+x for some a e a, contrary to dx G Ta. 
□ 
When p is negation free there is no need to require / to be cofinal. 
Theorem 9.31 Suppose 01 = (0,11) is a finite model, a negation free formula 
and 2) set of all closed domains in 01 relative to p. Then for any frame 
$ = (W,R,P), which is subreducible to 0 = (V, S) by some f satisfying (CDC) 
for 2), there is a model OJt = (#,07) such that, for any x G dom/ and any 
G Subp, (071, x) f= iff (01, f(x)) ft i). 
Proof The only difference from the proof of Theorem 9.30 concerns the 
definition of 07, since this time x $ dom/ does not imply /(x|) ^ 0. If f(xT) = 0 then 
we put x ft p for all variables p. The definition remains correct: 
{x $ dom/ : /(x|) = 0} = W - dom/| G P. 
Moreover, since p is negation free, it should be clear that if f(x T) = 0 then 
xft'ipiox every G Sub</?. □ 
Thus, if 01 = (0,U) is a finite countermodel for a formula p and 2) the set 
of all closed domains in 01 relative to p then # ft p for every frame # which is 
cofinally subreducible to 0 by some partial map satisfying (CDC) for 2). Now we 
shall go in the reverse direction and show that, given an arbitrary counter model 
071 = (£,07) for p, one can construct a finite countermodel 01 = (0,U) for p 
such that there is a cofinal subreduction of # to 0 satisfying (CDC) for the set 
2) of all closed domains in 01. To this end we require two definitions and two 
propositions. 
Let E be a non-empty set of formulas closed under subformulas. Given 
models OJt = (#,07) and 01 = (0,11), we say a subreduction / of 5 to 0 is a E- 
subreduction of OJt to 01 if 
(i) for each x G dom/, (071, x) (01, f(x)) and 
(ii) for each point x in # there is y G x| fl dom/ which is E-equivalent to x 
in 071. 
It is worth noting that, by (ii), every E-subreduction is cofinal. 

306 
CANONICAL FORMULAS 
Proposition 9.32 Suppose that f\ is a E-subreduction of DJli = (#i,2*i) to 
DJI2 = (#2,2*2) and /2 a E-subreduction of DJI2 to 2% = (#3,2*3). Then the 
composition /2/1 is a E-subreduction of DJI 1 to 9Jt3. 
Proof By Theorem 9.21, /2/1 is a subreduction of #1 to #3. Clearly, it satisfies 
(i). To show (ii), suppose x is a point in #1. Then, by (ii), there is y G ndom/i 
for which x y. Using (ii) again, we can find a point z G fi(y)]_ 0 dom/2 such 
that fi(y) z. By (R2), there is u G such that fi(u) = z. It remains to 
observe that u G dom/2/1 and that, by (i), u x. □ 
Our second definition is connected with the condition (ii) of the preceding 
one. Given a model DJI = (#, 2J) based on a frame # = (W, iZ, P) and a subset 
V C W, we say a point x G W is E- remaindered in V if x y for some 
y G nU. Thus, a subreduction / of # to 0 is a E-subreduction of DJI to 21 iff 
it satisfies (i) and every point in # is E-remaindered in dom/. 
The meaning of this notion is clarified by the following observations. Suppose 
again that we have a model DJI = (#, 2*) on a frame $ = (W, iZ, P) and VC W. 
Taking the restrictions S and 11 of, respectively, R and 2* to V, we obtain the 
model 21 = (0,11) on the Kripke frame 0 = (V,S), which is called the Kripke 
submodel of DJI induced by V. If Q is the set of possible values in 21 and the 
frame 0' = (V, S, Q) turns out to be a subframe of $ then 21' = (0',U) is called 
a submodel of DJI induced by V. 
Proposition 9.33 Suppose 21 = (0,11) is the Kripke submodel of DJI = (#, 2*) 
induced byVCW and every point in $ is Y,-remaindered in V. Then, for each 
x G V, (DJl,x) (21, x). So if, in addition, 21 is a submodel of DJI then the 
identity map on V is a E-subreduction of DJI to 21. 
Proof The latter claim is an immediate consequence of the former one, which 
is proved by induction on the construction of formulas (/?gE. We will consider 
only the modal case, leaving the intuitionistic one to the reader. 
The basis of induction and the cases of(^ = 't/>Ax, anc* V7 ~^ X are 
trivial. So suppose that ip = Dip. If (DJl,x) ft D'lp then there is y G x] such 
that (DJI, y) ft 'ip. Since y is E-remaindered in V, there must be a z G fl V 
for which (DJI, z) ft ip. By the induction hypothesis, we then have (21, z) ft ip 
and so (21, x) ft Dip. Conversely, if (21, x) ft Dip then (21, y) ft ip for some 
point y G x T flF, whence, by the induction hypothesis, (DJI, y) ft ip and so 
(DJl,x)ftDip. □ 
We are in a position now to prove the main result of this section. 
Theorem 9.34 Suppose E is a finite set of formulas closed under subformulas. 
Then there is a constant such that every model DJI = (#, 2J) is Y-subreducible 
to some finite model containing at most c£ points. 
Proof Note at once that the intuitionistic case reduces to the modal one. For, 
given a finite set E of intuitionistic formulas and an intuitionistic model DJI = 
(#, 21), we can first take the closure II of {T(<p) : ip G E} under subformulas 

CHARACTERIZING TRANSITIVE REFUTATION FRAMES 
307 
and the model crDJl = (cr3,2J). Then we construct a II-subreduction / of crDJl 
to some model 01 = (0,11) containing at most cn points and, finally, take the 
skeleton pDfl = (p0,pil). By Theorem 9.22, pf is then a subreduction of 3 to 
p0 satisfying, by Lemma 8.28, the conditions (i) and (ii) for E. 
Thus, we may consider only the modal case. Suppose O = {pi,...,pn} is 
the set of variables in E. Clearly^ without loss of generality we may assume 3 = 
(W, ii, P) to be generated by 2J(pi),..., 2J(pn). The process of E-subreducing DJI 
to a finite model can be described by the slogan “refine and remove”. First we 
take DJlo = (3o>2Jo) = SOT and refine only that upper part of 3o which gives us 
the points of depth 1 in the refinement of 3b • Then we remove from the resulting 
frame all those points of depth > 1 that have E-equivalent successors of depth 
1. Thus we obtain a model SDTi = (3i,2Ji) which turns out to be a E-subreduct 
of SDTo- After that we refine the part of 3i which gives the points of depth 2 and 
remove all the points of depth > 2 having E-equivalent successors of depth 2, 
thereby obtaining a E-subreduct DJI2 of SDTi, and so on. Since there are at most 
2lEl pairwise non-E-equivalent points, this process of refining and removing must 
eventually terminate, i.e., we shall construct a E-subreduct DJlm = (3m»®m) of 
DJI whose frame is of depth m. According to Theorem 8.82, the number of points 
2|s| 
in 3m does not exceed 2n cn(i) and so we can take to be equal to this 
constant. 
Now we describe this construction in full details. Let DJIq = DJI and suppose 
that we have already constructed a E-subreduct DJli = (3i, 2Ji) of DJI (based upon 
3» = (Wi,Ri,Pi)) such that: 
• 3i is generated by 2J*(pi),... ,2J;(pn); 
• for every d < i (d ^ 0), W=d is a cover for W?d\ 
• every point in Wfl is an atom in 3* and 
• \Wrd\ < 2ncn(d), for every d < i (d ^ 0). 
If W>1 = 0 then DJli = is the desirable E-subreduct of DJI. Otherwise 
take all distinct maximal z-cyclic sets Xi,...,Xk in 3* = (Wi,Ri,Pi). Unlike 
Section 8.6, this time 3i is not necessarily refined, and so z-cyclic sets are not 
in general clusters of depth i + 1. What we are going to show is that they can 
be reduced to clusters of depth i + 1. It follows from the definition of z-cyclic set 
that every Xj, for j = 1,..., fc, is uniquely determined by any x G Xj\ more 
precisely, 
Xj = {y G fi W^1 is non-degenerate z-cyclic, 
y]_ fl W>1 n Wand spl(x) = spl(y)} 
if Xj is non-degenerate and 
Xj = {y e W?1 : y ~© x, j/tn = 0 and sp\x) = sp\y)} 
if Xj is degenerate. So all Xj are pairwise disjoint and k < cn(i + 1). Using the 
same kind of arguments as in the proofs of Theorems 8.84 and 8.83, we can show 

308 
CANONICAL FORMULAS 
that X\ U ... U Xk is a cover for W>1 and Xj G Pi for all j = 1,..., k. So, for 
each x G Xj, {y G Xj : x y} G Pi. Recall also that, by Lemma 8.79, the 
very same formulas (of variables in O) are true in DJli at ©-equivalent points in 
Now we define an equivalence relation ~ on Wi by putting 
x ~ y iff either x = y or x, y G Xj, for some j G {1,..., fc}, and x ~© y. 
Let [x] be the equivalence class under ~ generated by x and [X] = {[x] : iGl} 
for X G Pi. By the definition of i-cyclic set, xRiy iff [x] C [y] j for all x,y e Wi. 
Moreover, since, as we have already observed, the same formulas are true in 971* 
at all points in [x], every X G Pi is closed under ~ and so ~ is a congruence in 
Therefore, by Theorem 8.68, the quotient model [DJli] = ([#*], [2J*]) under ~ 
is a reduct (in particular, a E-subreduct) of DJli. Notice also that the reduction 
x [x] of $i to [#*] only “folds” the i-cyclic sets Xj into clusters of depth i + 1 
and leaves other points in untouched. Every point of depth i + 1 is clearly an 
atom in [#*]. 
For x G [Wi], let ipx be the conjunction of all formulas xp G E which are true 
at x and all formulas such that x € E and x ^ x- Denote by X the set of 
points of depth > i + 1 in [#*] which are E-remaindered in [Wi]=l+1, i.e., 
Let 1 = (Wi+i, i?i+i, Pj+i) be the subframe of [&] induced by [Wi\—X G [Pi] 
and 971*+1 = (#i+i,2J*+i) the submodel of [DJli] based on #*+1. Every point 
in [Wi] is E-remaindered in Wi+i and so, by Proposition 9.33, 97t*+i is a E- 
subreduct of [971*]. Finally, using Proposition 9.32, we can conclude that 97t*+i 
As a consequence of this result we obtain 
Theorem 9.35 For every formula ip, there is a constant c^ such that a frame # 
refutes ip only if there are a rooted countemriodel 91 = (6,11) for p with at most 
Cy points and a cofinal subreduction f of $ to <5 satisfying (CDC) for the set 2) 
of all closed domains in 91 relative to (p. 
Proof Let E be the set of ip's subformulas, DJI = (#,2J) a countermodel for ip 
based on # and g a E-subreduction of DJI to some model 91' = (6', 11') whose 
frame 6' has at most c^ = cs points. By the definition of E-subreduction, 91' is 
a countermodel for p. If it is not rooted, we take a submodel 91 = (6,11) of 91' 
generated by some point in 91' at which p is not true. Then the partial map / 
from # onto 6 = (V, S) defined by 
x = U 04 n [»,](*>,)) - [w^i+1 
xelWi}^1 
is a E-subreduct of DJli and hence of 9Jto = DJI as well. 
□ 
is clearly a cofinal subreduction of ^ to 6. 

CHARACTERIZING TRANSITIVE REFUTATION FRAMES 
309 
It remains to verify that / satisfies (CDC) for the set 2) of all closed domains 
in 01. Suppose x G dom/| and x $ dom/. By (Rl), x $ domg. Since x is E- 
remaindered in domg, it is also E-remaindered in dom/, i.e., there is a point 
y G x] fl dom/ such that x y. Now, let D be an antichain in © such that 
f(xT) = We show that D is open in 01. Indeed, let = {ip G E : x ]= rp}, 
A 0 = {^gE: x ft tp} and let £*> = (T*,, A*>). Then in the modal case, t$ satisfies 
(ODmI), since xRy and x y, and the “only if’ part of (ODjtf2). To prove the 
“if’ part, suppose that a |= D+ip for all a G D. Then f(y) |= D+rp as well, since 
f(y) G D|, and so x |= U\pm The intuitionistic case is considered analogously. 
□ 
Now, combining Theorems 9.30, 9.31 and 9.35, we obtain the frame-theoretic 
characterization of transitive refutation frames for modal and intuitionistic 
formulas, mentioned at the beginning of the section. 
Theorem 9.36 (i) There is an algorithm which, given a formula ip, returns a 
finite number of finite rooted frames Si, • • •, Sn and sets'!) i,..., 2)n of antichains 
in them such that, for any frame S, S P iff there is a cofinal subreduction of 
S to Si, for some 1 < i < n, satisfying (CDC) for 2)*. If p is an intuitionistic 
disjunction free formula then 2)* = 0 for alii = 1,..., n. 
(ii) There is an algorithm which, given a negation free formula ip, returns a 
finite number of finite rooted frames Si ,..., 3n and sets 2)i,..., 2)n of antichains 
in them such that, for any frame S, S ^ P iff there is a subreduction ofS to Si, 
for some 1 < i < n, satisfying (CDC) for!)i. If, in addition, ip is an intuitionistic 
disjunction free formula then 2)* = 0 for alii = 1,..., n. 
Proof (i) Let be the constant mentioned in Theorem 9.35. Construct all 
possible rooted countermodels Dili = (Si, 2Ji),..., f°r wRh 
< points. Let 2)* be the set of all closed domains in Dili relative to ip. Note 
that, by Example 9.26, 2)* = 0 if <p is an intuitionistic disjunction free formula. 
The rest of the proof follows immediately from Theorems 9.30 and 9.35. 
(ii) is proved in exactly the same way, but using Theorem 9.31 instead of 
9.30. □ 
One more interesting result follows from the proof of Theorem 9.34. 
Theorem 9.37 Suppose 9JI = (J?,®) is a model of a modal or intuitionistic 
language with a finite set of variables. Then 9JI is reducible to a model 91 = (©,11) 
based upon a top-heavy frame ©. Moreover, ifS is of finite depth then © is finite. 
Proof Construct a sequence of models 9Jto = £3DT, SDTi,... in almost the same 
way as in the proof of Theorem 9.34. The only difference is that now we do not 
remove any points from frames, just refining S level by level. More exactly, using 
the terminology of that proof, we define 971*+1 as just [971*]. Of course, in general 
the new construction will not necessarily terminate, unless S is of finite depth. 
But then we have an infinite chain of reductions 97to ^ 97ti A ... and can take 
the limit 91 = (©,11) of this chain. As we know, 91 is a reduct of 971 and clearly, 
<3 is top-heavy. □ 

310 
CANONICAL FORMULAS 
9.4 Canonical formulas for K4 and Int 
The characterization of refutation frames, found in the preceding section, 
provides us with a powerful frame-theoretic tool for handling modal and superintu- 
itionistic logics. 
Example 9.38 As a simple illustration of its capacity, we show how it can be 
applied for proving, say, the finite approximability of the Grzegorczyk logic Grz. 
According to Proposition 9.3, a frame refutes grz iff it is subreducible either to 
• or to (°°). Let ip be an arbitrary modal formula. By Theorem 9.36, we can 
construct finite frames Si, • • • ,3n and choose sets 2)i,... , 2)n of antichains in 
them so that a frame S refutes ip iff there is a cofinal subreduction of S to fo, for 
some i G {1,... , n}, satisfying (CDC) for 2)*. Now, if each Si is subreducible to 
• or © (i.e., contains one of them as a subframe, since Si is finite) then every 
frame refuting ip refutes, by Theorem 9.21, grz as well, and so ip E Grz. And 
if at least one Si is subreducible neither to • nor to © then it is a frame for 
Grz refuting ip. (Note, by the way, that the same argument establishes the finite 
approximability of all logics in Extint and NExtK4 axiomatizable by formulas 
in Tables 9.1-9.3.) 
An important feature of Theorem 9.36 is its invertibility in the sense that with 
each finite rooted frame $ and each set 2) of antichains in $ one can associate 
a formula which is refuted in a frame 0 iff there is a cofinal subreduction of 0 
to $ satisfying (CDC) for 2). Indeed, let $ = (W, R) be a finite transitive rooted 
frame, ao,..., an its points, with ao being the root. Suppose also that 2) is some 
(possibly empty) set of antichains in S different from reflexive singletons. The 
normal modal canonical formula £*(#, 2),_L) associated with S and 2) looks as 
follows: 
n 
Qf(3r»®»-L)= /\ tyij A A^a A V* A (p± —> Po, 
diRdj i=0 
where 
Vij = D+(aPj ~>Pi), 
n 
Vi = °+(( A apk A A ^ 
-idiRdk 
n 
<p* = °+( A apjA Api V dpj)> 
diew-Q t »=o dj€d 
n 
V± = °+(A -*-)• 
i=0 
Denote by a(Sr, 2)) the result of deleting the conjunct from a(Sr, 2), _L); it is 
called the normal modal negation free canonical formula for S and 2). 
With intuitionistic S and 2) we associate the intuitionistic canonical formula 
0(S, 2), _L) and the intuitionistic negation free canonical formula 0(S, 2)), namely 

CANONICAL FORMULAS FOR K4 AND INT 
311 
/?(£, 2), _L) = /\ ipij A /\ xfo A </>x Po 
diRdj 
where 
V'ij = ( A Pk.~^Pj)^Pu 
•*fa = A ( A Pk->Pi)^ \J pj, 
n 
vu. = A( A -1’ 
i=0 -idiRdk 
and (3($, *3) is obtained from /?(#, 2), JL) by deleting the conjunct z/>x- 
The following two results will be referred to as the refutability criteria for 
canonical formulas. 
Theorem 9.39 For any modal transitive frame 0 = (V,S,Q), 
(i) 	0 a(5',D,_L) iff there is a cofinal subreduction of 0 to $ satisfying 
(CDC) for 2); 
(ii) 0 ^ (*(#,2)) iff there is a subreduction of 0 to S' satisfying (CDC) for 
Proof Let us first prove (i). 
(=>) Suppose 2),_L) is refuted in a model 01 = (0,il). Denote by <p the 
premise of a(5', 2), _L) and define a partial map / from V onto W by taking 
We show that / is a cofinal subreduction of 0 to S' satisfying the closed domain 
condition for 2). Clearly, / is a function, since x |= and x^ Pi imply x |= pj, 
for all j ^ i. 
Let xSy, /(x) = a* and f(y) = aj. Then aiRaj, for otherwise x (= Dpj (since 
->aiRaj, x |= ipi and x ^ pi) and so p (= pj, contrary to /(p) = a^. 
Let /(x) = a* and aiRaj. Then x (= (p^-, x ^ p*, whence x ^ Dpj and so 
there is y G x| such that y ^ Pj- Since x |= <p and x5p, we have y (= <p. Therefore, 
f{y) — a>j- It follows, in particular, that / is a surjection, since /_1(ao) ^ 0 and 
cioRaj for all j ^ 0. 
By the definition, f~1(ai) = {x G V : x^->Pi}GQ. Thus, / satisfies 
(Rl)-(R3) and so is a subreduction of 0 to S- 
Suppose x G dom/T. Then x |= <p, x |= ip± and hence x ^ p* or x ^ Dp* for 
some z. In the former case x G dom/ and in the latter one there is z G x| such 
that z \= ip, z ^ Pi and so z G dom/. Thus, / is cofinal. 
Let x G dom/t and /(x|) = t)| for some t) G 2). Then x |= <p, x |= <p5 and 
x Dpj for all aj G D. Therefore, either x ^ Dp* for some a* G W —flf, or x ^ p* 
a* if x ft <p —► Pi 
undefined otherwise. 

312 
CANONICAL FORMULAS 
for some i. In the former case a* G f(x|), which is a contradiction, whereas the 
latter means f(x) = athat is, x G dom/. Thus, / satisfies (CDC) for 2). 
(<*=) Suppose that / is a cofinal subreduction of 0 to S satisfying (CDC) for 
2). Define a valuation il in 0 by taking il(pf) = V-/-1 (a*), for every i = 0,..., n, 
and show that in the resultant model = (0,il) we have x a(S, 2),_L) for 
each x G f~l(ao). 
Let /(x) = ao- Then x ^ po, and we must prove that the premise of 
a(S,2), _L) is true at x. Suppose x ^ for diRdj. Then y (= Dpj and y ^ Vi 
for some y G x|, whence /(p) = a*. By (R2), there is z G p| such that f(z) = aj> 
and so 2 ^ Pj> contrary to y |= Dpj and p5z. 
If x ^ <p* then there is y G x| such that /(p) = a* and either y ^ Dp* with 
-<diRdk, or p ^ pj for some j ^ L It is clear that neither case can hold, since 
the former implies z ^ Pk for some z G p|, and so diRdk, while the latter means 
/(p) = dj\ that is, j = i. 
In the same way we can show that the assumption x ^ <pa, for some t) G 2), 
contradicts (CDC) and x ^ <px is inconsistent with the cofinality condition. 
A proof of (ii) can be extracted in the obvious way from that of (i). □ 
In the same manner one can prove 
Theorem 9.40 For dny intuitionistic frdme 0, 
(i) 0 ^ /?(S,2),_L) iff there is a cofindl subreduction of 0 to S satisfying 
(CDC) for 2); 
(ii) 0 Y=- /?(S,®) iff there is a subreduction of 0 to S satisfying (CDC) for 
2). 
In general, with a frame S we can associate several canonical formulas by 
choosing various sets of closed domains: from a(S, 0, _L) to a(S, 2)tt,_L) and from 
a(S, 0) to a(S, 2>**), where 2>** is the set of all antichains in S different from 
reflexive singletons. These boundary formulas will play a particular role in the 
sequel, and we give them proper names. 
The formulas of the form a(S, 2)N,_L) and ^(ff, 2>**, JL) are called the (modal 
and intuitionistic, respectively) frame formulds for S; we denote them by _L) 
and /?**(£, _L). The formulas a(S, 2)^) and /?(S,2)^) are called the negation free 
frume formulds for S and denoted by a^(S') and /?H(S). 
Proposition 9.41 (i) 0 aH(S, _L) (i3 /^(S, 1.)) iff d genemted subframe of 
0 is reducible to S'. 
(ii) 0 ^ att(S) ((5 ¥=■ ${%)) iff 0 is densely subreducible to S'. 
Proof We consider only the formula $($) and leave the other cases to the 
reader. Suppose that 0 ^ /?**(#). Then there is a subreduction g of 0 to S 
satisfying (CDC) for 2)tt. If g is not dense then there is a point x in the set 
dompj n dompj, — domp. By (CDC), p(x|) = axt for some point dx in S'. The 
dense subreduction / we need can be defined by extending g as follows: 

CANONICAL FORMULAS FOR K4 AND INT 
313 
{g(x) if x e domg 
ax if x e doing | fi domg j — domg 
undefined otherwise. 
The converse implication follows from the refutability criterion. □ 
The formulas a(S, 0) and /?(S, 0) are called the subframe formulas for S and 
denoted by a(S) and (3($). Finally, the formulas a(S, 0, _L) and /?(S, 0, _L) are 
called the cofinal subframe formulas for S and denoted by a(S, _L) and (3($, _L). 
Clearly, we have 0 ^ a(S, -L) (0 /?(S, -L)) iff 0 is cofinally subreducible to S 
and 0 a (S') (0 (3(3)) iff 0 is subreducible to S'. 
Proposition 9.42 For any sets 2) and (£ of antichains in S such that 2) C 0, 
K4 0a«(S,-L) C K4 0a(S,0,_L) C K4 0a(S,2), _L) C K4 0a(5,l) 
in in in in 
K4 0a»(S) c K4 0a(S,0) C K4 0a(S,2)) C K4 0a(S), 
Int + /?*(& -L) C Int 0 /?(S, 0, -L) C Int + /?(S,2), _L) C Int + /?(& _L) 
in in in in 
Int 0/?«(£) c Int 0/?(£,£) C Int 0/?(&©) C Int 0/?(£). 
Proof Exercise. □ 
Another important feature of the canonical formulas is that they can axiom- 
atize all logics in NExtK4 and Extint. For combining Theorems 9.36, 9.39 and 
Proposition 9.28, we obtain the following completeness theorem for NExtK4. 
Theorem 9.43 (i) There is an algorithm which, given a modal formula p, 
returns canonical formulas a(Si,2)i, -L),... , a(Sn,2)n, -L) such that 
K4 0 p = K4 0a(Si,2)i, _L) 0 ... 0a(Sn,2)n, _L). 
So the set of normal modal canonical formulas is complete for the class NExtK4. 
(ii) There is an algorithm which, given a negation free p, returns negation 
free canonical formulas a(Si,2)i), • • • ,a(Sn,Sn) such that 
K4 0 p = K4 0 o(Sl> 2)i) 0 . . . 0 o(Sn) ®n)- 
The combination of Theorems 9.36 and 9.40 yields the completeness theorem 
for Extint. 
Theorem 9.44 (i) There is an algorithm which, given an intuitionistic p, 
returns canonical formulas /J(Si,2)i, _L),... ,/3(3n,®n, -L) such that 
Int 0 p = Int 0 /3($i, 2)i, _L) 0 ... 0 2)„, _L). 
So the set of intuitionistic canonical formulas is complete for Extint. 

314 
CANONICAL FORMULAS 
(ii) There is an algorithm which, for a negation free ip, returns negation free 
canonical formulas 2) 1),..., /?(3n>®n) such that 
Int ip — Int + (3($i,®i) + • • • + 
(iii) There is an algorithm which, given a disjunction free ip, returns cofinal 
subframe formulas _L),..., /3(3vi> -L) such that 
Int 4- ip = Int + (3(31, (3(3n> -L). 
(iv) There is an algorithm which, given a negation and disjunction free ip, 
returns subframe formulas (3(3i),..., (3(3n) such that 
Int + ip = Int 4- (3(3i) 4-... 4- /J(3n)- 
As an illustration of these completeness theorems, Tables 9.6 and 9.7 show 
canonical representations of some standard normal modal and si-logics. In fact, 
these representations can be derived from Propositions 9.4, 9.5, 9.14, 9.19 and 
9.20. 
Theorem 9.45 Every si-logic L with extra axioms in one variable can be 
represented either as 
L = Int + nf2n = Int + 0\Sjn, ±) 
or as 
L = Int + nf2n_1 = Int + /3i(Sjn+1,±) + 0*{fin+2, -L), 
where 9)n, i3n+i, i3n+2 o,re the subframes of the frame in Fig. 8.13 generated by 
the points n, n-hi and n + 2, respectively. 
Proof By Theorem 7.67, L is axiomatizable by the Nishimura formulas. By 
Theorem 8.92, 
Int + nf2n = Int + -L), 
Int + nf2n_x = Int + /3^(Sjn+i, _L) + 0t(f)n+2, -I-)- 
That only two additional axioms of that sort is enough follows from the obvious 
inclusion (3^{9)m, _L) G Int + _L) which holds for every m > n + 2. □ 
It follows from the completeness theorem that as far as such properties of 
logics as the decidability, completeness or finite approximability are concerned 
we can deal only with the canonical formulas. Indeed, suppose a logic L and a 
formula ip are given. By Theorem 9.43, L is axiomatizable by a set of canonical 
formulas, which is finite if L is finitely axiomatizable. Besides, we can effectively 
construct canonical formulas a\,...,an such that 
K4 0 ip = K4 0 ai 0 ... 0 an. 
Therefore, we have ip e L iff a* G L for every i G {1,..., n}, and so L is decidable 
iff there is an algorithm which is capable of deciding, given an arbitrary canonical 

CANONICAL FORMULAS FOR K4 AND INT 
315 
Table 916 Canonical axioms of standard modal logics 
D4 = K4©a(*,l) S4 = K4 0a(*) 
GL = K4 0 a(o) For = K4 0 a(*) (2 axioms) 
Grz = K4 0a(t)0a(©) S4.1 = S4 0 a((°°), _L) 
K4.1 = K4 0a(t,l)0a(©,l) 
o 
Triv = K4 0 «(•) 0 a(R) 0 a( £) 
Verum = K4 0 a(o) 0a(!) 
o 
= S4 0 a( £ ) 
v 
= S4 0a( o , X) 
1# #2 
Y. 
S5 
S4.2 
A* 
K4.2 
K4.3 
K4Z 
K4B = K4 ® a( I) (4 axioms) 
V 
S4.3 = S4 © a{ o ) 
= GL © a( V , {{1}, {1,2}}) 
! • w 
K4 © a( i , ±) © a( £ , ±) © a( * , ±) (8 axioms) 
V, 
= K4 © a( ¥ ) (6 axioms) 
• o y y 
= K4©a( o) ©a( I) ©a( • )©a( V) 
R p | 
Dum = S4 © a( o ) © a((°°)) 
D4G, 
K4H 
K4Altn 
K4BW„ 
K4BD„ 
K4„ 
v 
D4©atl( V ,_L) 
K4 © a( * ) © a(©) (9 axioms) 
K4 0 (a(S') : n + 1 points are seen from the root of S'} 
n-f 1 
K4 0 a( V) (2n + 4 axioms) 
j n 
K4 0 a( 
t1 
K4 0 oft( lO) 
: 0) (2n+1 axioms) 
j m 

316 
CANONICAL FORMULAS 
formula a, whether or not a e L. It follows also from this equality that for every 
frame S, S H= <p iff S ^ for some i e {1,... ,n}. Thus, L is complete with 
respect to a class C of frames iff for every canonical formula a $ L there is a 
frame J G C validating L and refuting a. (The same, of course, concerns logics 
in Extint.) 
Having proved that the set of canonical formulas is axiomatically complete, 
it is natural to ask whether it is an axiomatic basis (i.e., contains no proper 
complete subsets) and if it is not, to find such a basis. It turns out, however, 
that neither of the classes NExtK4 and Extint has an axiomatic basis. By 
Proposition 4.14, to show this it suffices to find prime modal and intuitionistic 
formulas and to check whether the set of them is axiomatically complete. 
Theorem 9.46 (i) p is prime in NExtK4 iff it is deductively equal in NExtK4 
to a frame formula X), i.e., K4 0 p = K4 0 X). 
(ii) 	p is prime in Extint iff Int+ p = Int+/?H(S, X), for some frame formula 
Proof We consider only the modal case, since the intuitionistic one is proved 
in exactly the same way. The proof proceeds via two lemmas. 
Lemma 9.47 (i) a^S', X) e K4 0 {a(0f, 2)*,X) : i € 1} iff, for some i e I, 
S' ft a(0i,2)i,X). 
(ii) /?«(£, X) e Int 0 1)9(0*, 2)*, X) : i e 1} iff S ft /?(<$*, ®i,X) for some 
iel. 
Proof The implication (=>) is clear because S ft c^(S} X). 
(<=) Suppose S V* a(0f,2)i,X) for some iel. Then there is a cofinal 
subreduction / of S to 0* satisfying (CDC) for 2)*. Now, if ft is an 
arbitrary frame refuting a^(S, X) then a generated subframe & of f) is reducible 
to S by some g. The composition h = fg is a cofinal subreduction of to 
<£>i which clearly satisfies (CDC) for 2V Therefore, f) ft a(0*,2)i,X) and so 
a«(S,X) GK4 0a(0i,2)i,X). □ 
Corollary 9.48 (i) att(S, X) e K4 0 {a(0j,2V X) : iel} iff, for some iel, 
att(S, X) e K4 0a(0f,2)i,X). 
(ii) /Jtt(S,X) e Int + {0(0*,2)*,X) : iel} iff, for some index iel, 
/?H&-L)€lnt + /?(0i#2)i,X) 
It follows from this corollary that each frame formula a^S, X) is prime. 
Indeed, if L — K4 0 a^(S, X) = K4 0 {a(0i, 2)*, X) : iel} then there is iel 
such that L = K4 0 a(0f, 2)*, X) and so L cannot be decomposed into a sum of 
logics different from L. 
Now, by the completeness theorem, to prove that each prime formula p is 
deductively equal to some frame formula, it suffices to consider only the case 
of canonical p. So suppose p = a (S', 2),X) and construct the countermodels 
VRi = (Si,®i),... ,97tn = (Sn,®n) for <P such that |S| < \3i\ < c<p, where c^ is 
the constant mentioned in Theorem 9.36. Let 2)i,... ,2)n be the sets of closed 
domains in OTi,..., 97tn relative to p. 

CANONICAL FORMULAS FOR K4 AND INT 
317 
Table 9.7 Canonical axioms of standard superintuitionistic logics 
For 
Cl 
LC 
= Int + /?(o) 
O 
= Int + j8(i) 
\/ * 
SmL = Int + /3( o ) + (3( i) 
KC = Int + /?( Y 
,-L) 
V 
Int + /?( o ) 
SL 
KP 
WKP = 
NDfc . = 
BD„ = 
BWn = 
BTW„ = 
T„ 
Int + )9*( « ,1) 
o^f2° 
Int + (3( If , {{1,2}}, ±)+0{ 
ol o2 o 
IxA + ftTf ,{{1,2}}, ±) 
Ol oy 0...0 o 
Int + /?( <-> , {{1,2}}, -L) + ... + /?( 
j n 
Int + (3( i 0) 
71+1 
o — o 
,{{1,2}},!) 
1 k 
o- • • o 
■v' 
{{1 *}},!) 
Int + /?( o ) 
72+1 
O — O 
Int + /?( <5 ,_L) 
71+1 
O — O 
Int + ^^N/'') 
71+1 
O — O 
Bn = Int + 0* ( 
,Y> 

318 
CANONICAL FORMULAS 
Lemma 9.49 (i) For every modal canonical formula a(S, 2), X), 
K4 © a(£ 2), -L) = K4 © J.) © 2)i, -L) © ... © a(3n,®n, -L). 
(ii) For every intuitionistic canonical formula X), 
Int + /?(& 2), J.) = Int + /?»(& _L) + /?(&,®lt 1) + ... + 2)„, 1). 
Proof By Theorem 9.30 and Lemma 9.47, the logic in the right-hand part is 
contained in that in the left-hand part. To show the converse inclusion, suppose 
91 = (0,il) is a countermodel for X). Let / be the cofinal subreduction 
/ of 0 to # defined in the proof of Theorem 9.39. Two cases are possible. 
Case 1: dom/ = dom/|. Then / is a reduction of the subframe of 0 generated 
by dom/ to S and so 0 ^X). 
Case 2: dom/ C dom/|. Then the number of pairwise non-Sub</?-equivalent 
points in 91 is greater than \S\ and so, by Theorem 9.34, 91 is Sub</?-subreducible 
to 971 i for some i E {1,... ,n}, which, as we know, implies 0 ^ a($i, S3*, X). 
Thus, in both cases 0 is not a frame for the logic in the right-hand part and 
hence a(S, 2), X) belongs to it. □ 
We can now complete the proof of Theorem 9.46. Suppose a(Sr, 2), X) is prime. 
By Lemma 9.49, 
K4 0 a(Sr, J), X) = K4 0 X) 0 a(3i,2)i, X) 0 ... 0 a(3rn,2)n, X) 
with jfol > \S\. It follows from these inequalities and the refutability criterion 
that a(Sr, 2), X) ^ K4 0 a(3i,2)i, X) 0 ... 0 a(Sn, 2)n, X). But then we have 
K4 0a(5,2),X) = K4 0al*(5, X), since a(Sr, 2),X) is prime. □ 
Thus, we have characterized the sets of prime formulas in NExtK4 and 
Extint. However, they are not complete for these classes. For we have 
Proposition 9.50 Let S be the frame depicted in Fig. 9.6 (a). Then neither 
K4 0 a(S, X) nor Int + /?(#, X) can be axiomatized only by frame formulas. 
Proof Suppose otherwise. Then K4 0 «(#, X) = K4 0 {a^fo, X) : i G 1} for 
some frames Si- Let 0 be the Kripke frame shown in Fig. 9.6 (b). Since 0 is 
cofinally subreducible to #, it refutes a(S, X). Then 0 refutes X) for some 
i G /, and so it is reducible to Si by some reduction /. Clearly, Si is partially 
ordered and of width > 4. Let a = {ai, <22, <23, <24} be an antichain in Si such 
that, for any antichain b of four points in a C b| implies a = b. Such an 
antichain certainly exists, since Si is finite. Without loss of generality we may 
assume that, for some k < u>, /(c{) = ai, /(c*) = <22, f(c3) = a3 and /(C4) = a4. 
Suppose /(c*+1) = bj for j = 1,2,3. By the definition of reduction, 61, 62 and 63 
do not see each other in Si, are different from <21, <22, <23 and a C {61,625 63, <24}!, 
whence {<21, <12,03} = {61,62,63}, which is a contradiction. □ 
As a consequence of Theorem 9.46 and Propositions 4.14 and 9.50 we derive 
Theorem 9.51 NExtK4 and Extint have no axiomatic bases. 

QUASI-NORMAL CANONICAL FORMULAS 
319 
Fig. 9.6. 
9.5 	Quasi-normal canonical formulas 
Theorem 9.35, characterizing the constitution of refutation frames for a given 
formula by subreducing them to some fixed finite pattern frames, does not take 
into account at what point in a frame the formula is refuted. As a result, the 
set of normal modal canonical formulas turns out to be too small to axiomatize 
all quasi-normal extensions of K4, which are not supposed to be closed under 
necessitation. To see the reason for this, let us recall that logics in ExtK4 are 
characterized by frames with distinguished points, with a formula ip being refuted 
in (0, w) iff ip is false at w under some valuation in 0. According to the proof of 
Theorem 9.39, (0,tu) refutes a(#,2),_L) iff there is a cofinal subreduction / of 
0 to # satisfying (CDC) for 2) and the following actual world condition as well: 
(AWC) f(w) is the root of Sr. 
Now, consider the frame 0 = (V, 5, Q), whose underlying Kripke frame is shown 
in Fig. 8.1 (b) and where Q consists of all finite sets of natural numbers and 
their complements in the space V. Let u be the actual world in 0. Since each 
set X 6 Q containing u is infinite and has a dead end, it is impossible to reduce 
X to o or •, and so (0,u;) validates all normal canonical formulas. On the other 
hand, we clearly have (0,u;) ^ bdn for every n > 1. It follows in particular that 
the logics K4BDn cannot be axiomatized by normal canonical formulas without 
the postulated necessitation. 
To get over this obstacle and retain the idea of the canonical formulas we are 
forced to modify the definition of subreduction so that such sets as X above may 
be “reduced” at least to irreflexive roots of frames. Given a frame 0 = (V,S,Q) 
with an irreflexive root u and a frame # = (W, R, P), we say a partial map / from 
W onto V is a quasi-subreduction of # to 0 if it satisfies (Rl) for all x, y E dom/ 
such that f(x) ^u or f(y) ± u, (R2) and (R3). 
Thus, we may map all points in the frame 0 in Fig. 8.1 (b) to •, and this 
map will be a quasi-subreduction of 0 to • satisfying (AWC). Moreover, every 

320 
CANONICAL FORMULAS 
frame is quasi-subreducible to •. 
Now, given a finite frame 3 with an irreflexive root ao and a set 2) of antichains 
in 3, we define the quasi-normal canonical formula a* (#,2), X) as the result of 
deleting Dpo from ipo in a(Sr,2), X) (which says, in particular, that ao is not self- 
accessible); the quasi-normal negation free canonical formula a* (3,2)) is defined 
in exactly the same way, starting from a(5',2)). 
Theorem 9.52 Suppose w is the actual world in a frame 0. Then 
(i) (0,u;) a(3, ®,X) iff there is a cofinal subreduction of<& to $ satisfying 
(CDC) for 2) and (AWC); 
(ii) (0,w) <*(#, 2)) iff there is a subreduction o/0 to 3 satisfying (CDC) 
for 2) and (AWC); 
(iii) (0,tt;) ^ a*(3, ®,X) iff there is a cofinal quasi-subreduction of 0 to 3 
satisfying (CDC) for 2) and (AWC); 
(iv) (0,w) ^ a#(3, ®) iff there is a quasi-subreduction of 0 to 3 satisfying 
(CDC) for 2) and (AWC). 
Proof Follows from the proof of Theorem 9.39. ' □ 
Theorem 9.53 (i) There is an algorithm which, given a modal formula (p, 
constructs a finite set A of normal and quasi-normal canonical formulas such that 
K4 + </? = K4 + A. 
(ii) 	There is an algorithm which, given a negation free (p, constructs a finite 
set A of normal and quasi-normal negation-free canonical formulas such that 
K4 + ip = K4 + A. 
Proof (i) We put c = + 1 and construct all possible rooted models 9Jti = 
(3i,2Ji), • • •, k = (3fc,®fc) refuting <p at their roots w\,... ,Wk, respectively, 
and containing < c points. Let 2)* be the set of all closed domains in 9Jtf. If 
Wi is irreflexive and, for every e Suby?, Wi (= only if Wi (= -0, then we 
associate with 9Jtf the quasi-normal canonical formula a*(3^,2)*, X). Otherwise 
we construct the normal canonical formula <*(#*, 2)*, X). Denote by A the set of 
all resultant canonical formulas and show that K4 + ip = K4 + A. 
Suppose that {$,w) ip, i.e., there is a model 9Jt = (3,®) on the frame 
3 = (W,R,P) with root w such that w <p. Let 91 = (0,il) be the Sub<p- 
subreduct of 9Jt constructed in the proof of Theorem 9.34 and / the corresponding 
cofinal subreduction. Two cases are possible. 
Case 1: w € dom/. Then 0 is rooted and contains < c points. So 91 = DJli 
for some i € {1,..., fc}, and / is a cofinal subreduction (in particular, a 
quasisubreduction) of 3 to 3* satisfying (CDC) for 2)* and (AWC). Therefore, ($,w) 
refutes the canonical formula associated with 9Jlf. 
Case 2: w dom/. Consider the set 
x = ( n /_1(j/)in {xeW : x ~Subv «>}) - dom / 
y€V 
consisting of all those points in W — dom/ that are Sub</?-equivalent to w and see 
/-inverse images of all points in 0. Since 0 is finite, X G P. Clearly, w G X and, 

QUASI-NORMAL CANONICAL FORMULAS 
321 
for any Dtp g Suby?, w |= implies w |= ip because w is Sub<^-remaindered in 
dom/ (although w may be irreflexive). 
Construct a frame ©' = (V',Sf) by adding to © the new root u, which is 
reflexive iff X C Xj, and extend il to u so that u ~Sub<^ w• Since |U'| < c, the 
constructed countermodel for p coincides with 9JT*, for some i G {1,..., k}. Let 
/' be a partial map from W onto Vf defined by 
If X C X l or X = {w} then /' is clearly a cofinal subreduction of # to 
(in particular, this is the case if 'S is reflexive). But if X contains a dead end 
different from w, /' is only a cofinal quasi-subreduction of # to 3i- In both cases 
/' satisfies (CDC) for 2)* and (AWC), and so (#, w) refutes the canonical formula 
associated with 9Jli. 
Thus, K4 + p C K4 + A. The converse inclusion and (ii) are established in 
the same manner as in the proof of Theorem 9.36, taking into account the fact 
that in the models DJI*, whose associated canonical formulas are quasi-normal, 
Wi 1= □ ip implies Wi |= for every xp e Suby? (this is essential for proving an 
analog of Theorem 9.30). □ 
As an easy exercise, we invite the reader to prove that 
Theorem 9.53 and its proof provide us also with the following results: 
Theorem 9.54 (i) There is an algorithm which, given a modal formula ip, 
constructs a finite set A of normal canonical formulas built on reflexive frames such 
that S4 p = S4 H- A. 
(ii) There is an algorithm which, given a negation free p, constructs a finite 
set A of normal negation free canonical formulas built on reflexive frames such 
that S4 p — S4 H- A. 
Proof Each quasi-normal logic L containing S4 is characterized by the class 
{(©,u;) : © is reflexive and (©,w) 1= L}. Therefore, all frames in the proof 
of Theorem 9.53 may be regarded as reflexive and so quasi-normal canonical 
formulas are redundant. □ 
As a consequence of Theorem 9.54 we obtain 
Theorem 9.55 ExtS4.3 = NExtS4.3. 
Proof We must show that every logic L e ExtS4.3 is normal, i.e., p G L only if 
G L, for every formula p. Suppose otherwise. Then there is p such that p G L 
and □ p & L. By Theorem 9.54, p is deductively equal in ExtS4 to a conjunction 
of some (normal) canonical formulas, and so there exists otifS, 2), T) G L such 
f(x) if x G dom/ 
u if x G X 
undefined otherwise. 
S = (K4 ® la) + re = K4 + a(o) + a(#). 

322 
CANONICAL FORMULAS 
that □<*($, 2), ±) £ L. Let (0,tt;) be a frame with root w validating L and 
refuting □a(Sr,2),±). Since 0 |= S4.3, 0 is a chain of non-degenerate clusters. 
And since it refutes a(Sr,2),±) there is a cofinal subreduction / of 0 to S'. It 
follows, in particular, that S is also a chain of non-degenerate clusters and so 
2) = 0. Let a be the root of S- Define a map g by taking 
It should be clear that g cofinally subreduces 0 to S and g(w) = a. Consequently, 
9.6 	Modal companions of superintuitionistic logics 
As we saw in Section 3.9, the Godel translation T embeds Int into S4 in the sense 
that, for any intuitionistic formula ip, ip e Int iff T(^) G S4. Using only this 
fact and the relationship between intuitionistic and modal frames, established in 
Section 8.3, one can reduce various problems concerning Int (e.g. proving the 
completeness, finite approximability, disjunction property, etc.) to those for S4 
and vice versa. But in fact, it turns out that each logic in Extint is embedded 
via T into some logics in NExtS4, and for each logic in NExtS4 there is one in 
Extint embeddable in it. 
We say a modal logic M G NExtS4 is a modal companion of a si-logic L if L 
is embedded in M by T, i.e., if for every intuitionistic formula ip 
If M is a modal companion of L then L is called the superintuitionistic fragment 
of M and denoted by pM. The reason for denoting the operator “modal logic 
t-> its superintuitionistic fragment” by the same symbol we used for the skeleton 
operator is explained by the following: 
Theorem 9.56 For every M G NExtS4, pM = {ip G For£ : T(ip) G M}. 
Moreover, if M is characterized by a class C of modal frames then pM is 
characterized by the class pC = {pS : J G C} o/ intuitionistic frames. 
Proof It suffices to show that {ip G For£ : T(y?) G M} = LogpC. Suppose 
T(ip) G M. Then S |= T(ip) and so, by the skeleton lemma, p$ |= ip for every 
5 G C, i.e., ip G LogpC. Conversely, if pS (= ip for all S G C then, by the same 
lemma, T(ip) is valid in all frames in C and so T(ip) e M. * □ 
Thus, p is a map from NExtS4 into Extint. The following simple observation 
shows that actually p is a surjection. Given a logic L G Extint, we put 
f(x) if x G dom/ 
a if x G f~1(a)i — dom/ 
undefined otherwise. 
(0, w) ^ a($, -L), which is a contradiction. 
□ 
ip e L iff T(ip) G M. 
tL = S4 0 (T(<p) : ip G L}. 

MODAL COMPANIONS OF SUPERINTUITIONISTIC LOGICS 
323 
Theorem 9.57 For every si-logic L, tL is a modal companion of L, i.e., L = 
prL. 
Proof Clearly, L C prL. To prove the converse inclusion, suppose (p s/L L, i.e., 
there is an intuitionistic frame # for L refuting <p. Then, using the skeleton lemma 
and Theorem 8.34, we obtain cr'S |= tL and cr'S T{ip). Therefore, T{p>) tL 
and so <p £ prL. □ 
Corollary 9.58 For every superintuitionistic logic L, tL is the least modal 
companion of L, i.e., the least (with respect to C) logic in p~l(L). 
With the help of the canonical formulas we will obtain now a general 
characterization of the set p~1(L) of all modal companions of a given si-logic L. First 
let us prove a lemma. 
Lemma 9.59 Suppose $ is a finite rooted intuitionistic frame, 2) a set of 
antichains in # and 0 a modal quasi-ordered frame. Then 
0|=a($,35,_L) itfpCMtoS.-L) 
and 
«l= <*(&») tfpeMto®)- 
Proof Follows from the refutability criteria for the canonical formulas and 
Theorems 9.22 and 9.23. □ 
This lemma means that the formulas a({?, 2), _L) and a({?, 2)) behave like the 
Godel translations of /?(#, 2), _L) and /?(#, 35), respectively. More exactly, we have 
Corollary 9.60 For every canonical formulas /3(#,35,_L) and /3(#,35), 
S4 ® T(/J(Sr,2), 1)) = S4 0 a(£, 35,1) 
and 
S4 0 T(/J(Sr, 35)) = S4 0 a(ff, 35). 
Proof Follows from Lemmas 9.59 and 8.28. □ 
Theorem 9.61. (Modal companion) A logic M G NExtS4 is a modal 
companion of a si-logic 
L = Int+ {/?(&,35<,±): i e 1} 
iff M can be represented in the form 
M = S4©{a(&,35i,±): i G /} 0 {afo, 35,-, _L) : j G J}, 
where every frame , for j G J, contains a proper cluster. 

324 
CANONICAL FORMULAS 
Proof (<=) We must show that for every intuitionistic formula ip, ip € L iff 
T(</?) G M. Suppose T(ip) £ M. Then for some quasi-ordered frame |— M 
and $ ^ T((^). By Lemmas 9.59 and 8.28, we then have p$ [= L, p$ ^ ip and 
so (p £ L. The converse implication is more complicated. Suppose that <p £ L 
and # = (W, R, P) is an intuitionistic frame separating ip from L. We will show 
that cr$ = (W, ii, crP) separates T(y?) from M. First, by the skeleton lemma and 
Theorem 8.34, cr$ T(ip). Second, by Lemma 9.59, we have cr$ |= _L) 
for any i G I. So it remains to show that cr$ |= £*(3^, Dj, -L) for every j G J. 
Suppose otherwise. Then, for some j G J, we have a subreduction / of cr$ 
to $j. Let ai and «2 be distinct points belonging to the same proper cluster 
in $j. By the definition of subreduction, /-1(ai) C f~1(a2)! and f~1(a2) C 
/-1(aiH> and so there is an infinite chain x\Ry\Rx2Ry2R• • • in such that 
{rci, rc2, • • •} Q /-1(a 1) and {2/1,3/2, - - •} C /_1(a2)- And since i? is a partial 
order, all the points Xi and are distinct. 
The set /-1(a 1) is in o\P. By Lemma 8.32, we can represent it in the form 
f~1(a 1) = {—X\ U Y{) n...n {-Xn U Yn), where X*, Yi e P for any i = 1,.. n, 
which means in particular that X* = and = Y*T. Since /-1(ai)n/_1(a2) = 
0, for every point yi there is some number n* such that yi G XUi and yi £ YUi. 
But then, for some distinct l and m, the numbers n/ and nm must coincide, and 
so if, say, yiRym then xm g YUrn and xm G Xni (for yiRxmRym). Therefore, 
xm $ 1), which is a contradiction. 
(=>) Suppose that 
M = S4®{a(3*,35fc,±): k G K} ©{<*(£,•,25,, 1) : j G J}, 
where all frames 3^, for k e K, are partially ordered and all frames #7, for j G J, 
contain proper clusters. By (<=), we have 
L = pM = Int + {/3(fo,®fc,±) : fc G K} = Int+ {/?(&,©<, ±) : i G /} 
and so S4 ® ±) : i G /} = S4 © {£*(3^, -L) : fc G AT}, as it follows 
from Lemma 9.59. □ 
It is worth noting that Theorem 9.61 can be presented in a somewhat more 
general form. Namely, the very same proof gives us 
Theorem 9.62 M G NExtS4 is a modal companion of 
L = Int + {/?(&, -L) : i G /} + : j £ J} 
iff M can be represented in the form 
Af = S4©{a(&,®i,±) : iG/}®{a(5j,®j) : j G J} © 
1) : k G if} © {a(3n,£>n) : n € A'} 
where all frames 3^ and $n, for k € K and n € N, contain proper clusters. 

MODAL COMPANIONS OF SUPERINTUITIONISTIC LOGICS 
325 
Example 9.63 According to Theorem 9.62 and Tables 9.6, 9.7, we have the 
following equalities: 
pS4 == pS4.1 = pDum = pGrz = Int, 
pS4.2 = p(S4.2 ® grz) = KC, 
pS4.3 = p(S4.3 © grz) = LC, 
pS5 = p(S5 © grz) = Cl. 
Corollary 9.64 For every superintuitionistic logic 
L = Int+ {/?(&,±): i€/} + {/?(Si,S)i): j € J}, 
the set p_1(L) of its modal companions forms the interval in NExtS4 of the 
form 
p~l(L) = [tL, tL © a((°°))] = {Me NExtS4 : tLQM CtL® Grz} 
where tL = S4©{<*(&,2)*, -L) : i € 7}©{a(5j,S)j) : j € J}. If L is consistent 
then this interval contains an infinite descending chain of logics. 
Proof Notice first that a(#,2),_L) and a({?,2)) are in Grz iff # contains a 
proper cluster. So p-1(L) C [rL, tL © a((°°))]. On the other hand, the si- 
fragments of all logics in this interval are the same, namely L. It follows that 
p-1(£) = [rL,rL©a((°°))]. 
Now, if L is consistent then (3(o) ^ L and so we have 
tL C ... C tL © a(£n) C ... C tL © a(^) C tL © a(£i) = ForMC, 
where <ti is the non-degenerate cluster with i points. □ 
Thus, all modal companions of every si-logic L are contained between the least 
companion tL and the greatest one, viz., tL © a((°°)), which will be denoted 
by crL. 
Corollary 9.65 There is an algorithm which, given a modal formula cp, returns 
an intuitionistic formula ijj such that p(S4 © <p) = Int + 
Proof Follows from Theorems 9.43 and 9.61. □ 
The following theorem describes lattice-theoretic properties of the maps p, r 
and cr. 
Theorem 9.66 (i) The map p is a homomorphism of the lattice NExtS4 onto 
the lattice Extint. 
(ii) The map r is an isomorphism of Extint into NExtS4. 
(iii) (The Blok—Esakia theorem) The map a is an isomorphism of the 
lattice Extint onto NExtGrz. 
All these maps preserve infinite unions and intersections of logics. 

326 
CANONICAL FORMULAS 
Proof Exercise. □ 
Now we give frame-theoretic characterizations of the operators r and or. First 
let us note some evident relations between frames for si-logics and their modal 
companions. 
Lemma 9.67 (i) For every intuitionistic frame # and logic M E NExtS4, 
$\= pM iffor$\=M. 
(ii) For every intuitionistic frame # and logic L E Extint, 
$\=L iffor$^aL. 
(iii) For every quasi-ordered frame # and superintuitionistic logic L, 
p$ \= L iff $ [= tL. 
(iv) For every intuitionistic frame si-logic L and every k, 0 < k < uj, 
d\=LiffrkS\=rL. 
Proof (i) Suppose $ |= pM but cr$ ^ M. In view of our previous results, it 
should be clear that cr$ |= rpM and so cr$ refutes some canonical axiom of 
M built on a frame with a proper cluster, which, as was shown in the proof of 
Theorem 9.61, is impossible. The converse implication follows from Theorem 8.34 
and the skeleton lemma. 
(ii) It suffices to put M = crL in (i) and use the fact that pcrL = L. 
(iii) and (iv) are left to the reader as an exercise. □ 
Theorem 9.68 A si-logic L is characterized by a class C of intuitionistic frames 
iff orL is characterized by the class crC = {cr$ : # E C}. 
Proof (=>) According to Lemma 9.67 (ii), we must show that any modal 
formula tp £ orL is refuted by some frame in crC. And by Theorem 9.43, we may 
assume <p to be a canonical formula, say, (*(#,2), ±). Besides, we know from the 
proof of Corollary 9.64 that £ is partially ordered. Therefore, /?(#, 2),±) ^ L, 
i.e., there is $ E C refuting /3(Sr, S>, ±) and so, by Lemma 9.59, cr$ ^ 2), _L). 
(<=) is straightforward. □ 
To characterize r we require one more lemma. 
Lemma 9.69 For every canonical formula a(J, 2), ±) built on a quasi-ordered 
frame a($,2),±) E S4 © a(p$, p2), 1). 
Proof Let 0 be a quasi-ordered frame refuting £*(#, 2), _L). Then there is a 
cofinal subreduction / of 0 to $ satisfying (CDC) for 2). The map h from £ onto 
p$ defined by h(x) = C(x), for every x in £, is clearly a reduction of £ to p$. So 
the composition hf is a cofinal subreduction of 0 to and it is easy to verify 
that it satisfies (CDC) for p2). □ 

MODAL COMPANIONS OF SUPERINTUITIONISTIC LOGICS 
327 
Theorem 9.70 A si-logic L is characterized by a class C of frames iff tL is 
characterized by the class Uo<k<uT^’ where TkC = • $ £ C}. 
Proof (=>) By Lemma 9.67 (iv), if # is a frame for L then TkS is a frame for rL. 
So suppose that a formula 2), ±), built on a quasi-ordered frame # = (W, R), 
does not belong to rL and show that it is refuted by some frame in Uo<fc<u; 
By Lemma 9.69, a(pSr, p2), ±) gL rL and so 0(p$, p2), -L) L. Hence there is a 
frame 0 = (V, S, Q) in C which refutes /3(p#, p2), J_). But then, by Lemmas 9.67 
(ii) and 9.59, cr<3 f= rL and cr& a(p$, p2), ±). Let / be a subreduction 
of cr(& to p$ satisfying (CDC) for p2) and let k = max{|C(x)| : x e W}. 
Define a partial map h from = (kV,kS,kQ) onto # as follows: if x e V, 
y0 e W, f(x) = C(y0) and C(y0) = {y0,.. • ,yn} then we put h((i,x)) = yu for 
i = 0,..., n. By the definition of (see Section 8.3), for any i e {0,..., n} we 
have 
h 1(yi) = {{i,x) : xef 1(C(y0))} = {i} x f 1(C(y0))ekQ. 
Now, one can readily prove that h is a cofinal subreduction of to # satisfying 
(CDC) for 2). Therefore, a({?,2), ±). 
(4=) is obvious. □ 
It is worth noting that this proof will not change if we put in it /c = (j. So we 
have 
Corollary 9.71 A logic L e Extint is characterized by a class C of frames iff 
rL is characterized by the class r^C. 
The following theorem gives a deductive characterization of the maps r and 
Theorem 9.72 For every si-logic L and every canonical formula a({?,2),J_) 
built on a quasi-ordered frame 
(i) a(S,2>,l)erL iff 0(p$, p2), _L) E L; 
(ii) (*(#, 2), _L) G orL iff either $ is partially ordered and /?(#, 2), ±) e L or # 
contains a proper cluster. 
Proof (i) The implication (=>) was actually established in the proof of 
Theorem 9.70, and the converse one follows from Lemmas 9.69 and 9.59. 
(ii) Suppose (*(#, 2), ±) e orL. Then either # is partially ordered, and so 
0(3,2), ±) G L, or 5 contains a proper cluster. The converse implication follows 
from (i) and the fact that (*(£, 2), ±) e Grz for every frame # with a proper 
cluster. □ 
The results obtained in this section not only establish some structural 
correspondences between logics in Extint and NExtS4 and their frames, but may be 
also used for transferring various properties of modal logics to their si-fragments 
and back. A few results of that sort are collected in Table 9.8; we shall cite 
them as the preservation theorem. The preservation of decidability follows from 

328 
CANONICAL FORMULAS 
Table 9.8 Preservation theorem 
Property of logics Preserved under 
p 
T 
cr 
Decidability 
Yes 
Yes 
Yes 
Kripke completeness 
Yes 
Yes 
No 
Strong completeness 
Yes 
Yes 
No 
Finite approximability 
Yes 
Yes 
Yes 
Tabularity 
Yes 
No 
Yes 
Pretabularity 
Yes 
No 
Yes 
P-persistence 
Yes 
Yes 
No 
Local tabularity 
Yes 
No 
No 
Disjunction property 
Yes 
Yes 
Yes 
Hallden completeness 
Yes 
No 
No 
Interpolation property 
Yes 
No 
No 
Elementarity 
Yes 
Yes 
No 
Independent axiomatizability 
No 
Yes 
Yes 
the definition of p, Theorem 9.72 and the completeness theorem for the 
canonical formulas. That p preserves Kripke completeness, finite approximability and 
tabularity is a consequence of Theorem 9.56. The map r preserves Kripke 
completeness and finite approximability, since we can define Tk in Theorem 9.70 so 
that Tk (W,R) = {kW,kR); however, r does not in general preserve tabularity, 
because rCl = S5 is not tabular. The preservation of finite approximability and 
tabularity under a follows from Theorem 9.68; Theorem 6.27 shows on the other 
hand that a does not preserve Kripke completeness. The rest of the preservation 
results in Table 9.8 will be proved later on, when we shall be considering the 
corresponding properties, or left to the reader as an exercise. 
9.7 	Exercises and open problems 
Exercise 9.1 Show that the classes VT, T and CM (and so 1Z and V) of 
(not necessarily transitive) modal or intuitionistic frames are closed under the 
formation of subframes. 
Exercise 9.2 Suppose a pseudo-Boolean algebra 23 is an IC-subalgebra of a 
pseudo-Boolean algebra 21. Prove that the map /+ defined by 
- /yx _ f V fl B if VflB G W<q 
J + ^ undefined otherwise 
for every V G W%, is a subreduction of 21+ to 23+. 
Exercise 9.3 Prove that if a pseudo-Boolean algebra 23 is an ICN-subalgebra 
of a pseudo-Boolean algebra 21 then 21+ is cofinally subreducible to 23+. 
Exercise 9.4 (S. Aanderaa) Let nOTift = DT —> □?/>, □ = p A □?/> and 
<pOT (<pAp) be the result of replacing every □ in by □DT (respectively, DAp), 

EXERCISES AND OPEN PROBLEMS 
329 
where p ^ Varp. Denote for convenience S2DT = T, S3DT = S4. Prove that for 
i G {2,3}, 
p G Si iff p -> pAp G SiDT, <p G SiDT iff pDT G Si. 
Exercise 9.5 Let 21 = (A, A, V, _L, □) be a modal algebra and a G A. Define 
21a = (Aa, Aa, Va, —>a, _L, □“), the relativization of 21 with respect to a, by taking 
Aa = {x n a : x G A}, 
(x fl a) ©“ (yDa) = (xOy)n a, for O E {A, V, —>}, 
Ua(x fl a) = D(a —> x) Pi a. 
Show that 21“ is a modal algebra and that 21“ is isomorphic to the subframe of 
21+ induced by fy(a). Prove also that for every subframe 0 of a modal frame # 
induced by V, 0+ = (3r+)v. 
Exercise 9.6 For a formula (p and a variable p not occurring in (p, define pp 
inductively by taking 
qp = q a p, q an atom, 
o x)P = V © Xp, for © € {A, V, —>}, 
(□V>)p = D(p->ipp)Ap. 
Show that for every subframe 0 of a modal frame # induced by V and valuations 
23 in $ and il in 0 such that 23(p) = V and il(g) = 23(g) Pi V, for all q different 
from p, 23(pp) = il(<p). 
Exercise 9.7 Let ps* = p —> pp, where p is a variable having no occurrences in 
p. Show that a frame # validates p3^ iff all subframes of # validate p. 
Exercise 9.8 Show that the si-logic characterized by the frame in Fig. 9.6 (b) 
is not finitely approximable. 
Exercise 9.9 Let 0 be the frame depicted in Fig. 9.6 (a). Show that the logic 
K4 0 {c^(#, -L) : $ is not subreducible to 0} is not finitely approximable. 
Exercise 9.10 Let a logic L G NExtK4 or L G Extint be finitely approximable. 
Show that NExtL or, respectively, ExtL has an axiomatic basis iff all logics in 
the class are finitely approximable. 
Exercise 9.11 Let 21= (A, A, V, —>, _L) be a finite pseudo-Boolean algebra with 
the second greatest element T'. Show that the formula 7(21), called the 
characteristic formula for 21 and defined by 
7(21) = (p_I <-► 1) A /\{pa OPb^PaQb : a,b e A, © € {A,V,-»}} ->pT'> 
is deductively equal to /^(2t+, _L) in Extint. 

330 
CANONICAL FORMULAS 
Exercise 9.12 Suppose # = (W, R) is a finite rooted transitive frame, a0,..., an 
are all its points and do is a root. Show that the conjunction of the formulas po» 
D(pi —> -ipj) for i ^ j, D(pi —> Opj) for diRdj, D(pi —> ->Opj) for ->diRdj is 
deductively equal in NExtK4 to a(Sr) and that by adding to it the conjunct 
□ (p0 V ... V pn) we obtain a formula that is deductively equal to a# (#, J_). 
Exercise 9.13 Prove that GL cannot be axiomatized by frame formulas over 
K4. 
Exercise 9.14 Show that K4 and Int have no immediate successors in NExtK4 
and Extint, respectively 
Exercise 9.15 Show that every interval of the form [K4, L], where L is a proper 
normal extension of K4, contains a continuum of logics. Show the same for 
extensions of Int. 
Exercise 9.16 Show that there is a continuum of logics in NExtK4.3. (Hint: 
consider the formulas a**({?n> -L), where $n is the chain of n points of which only 
the root is reflexive, and prove that a**({?n, -L) £ K4.3 0 a^Jm, -L) iff n = m.) 
Exercise 9.17 Prove that KC is the greatest si-logic containing the same 
negation free formulas as Int. (Hint: prove that (a) f3($,'D) £ KC for any # and (b) 
/?(#, 2), J_) £ KC iff # contains a last point iff /3(j, 2), _L) is deductively equal to 
mm 
Exercise 9.18 Prove that KC is the smallest si-logic in which every formula is 
deductively equal to a negation free formula. 
Exercise 9.19 Let ip e Cl. Prove that Int + ip = Cl iff ip is refuted by the two 
o 
point chain iff (p is deductively equal to /3( J). 
Exercise 9.20 Prove that Int + p = KC iff p is refuted by the frame 
and 
validated by 
Exercise 9.21 Let <£[n be the n-point cluster. Show that 
P-1(C1) = {S5 © a(£l2), S5 © o(CI3),..., S5 © <*(£[„),..., S5}. 
Exercise 9.22 Construct a finitely axiomatizable modal companion of Int that 
is not finitely approximable. (Hint: use the frames in Fig. 9.6 in which C4 and 
one of the final points in (a) are replaced by two-point clusters.) 
Exercise 9.23 Construct a non-compact modal companion of Int. 
Exercise 9.24 Show that the lattice ExtL can be embedded into the lattice 
p_1L, for every si-logic L. 

EXERCISES AND OPEN PROBLEMS 
331 
Exercise 9.25 Prove that if a si-logic L is tabular then all logics in p lL are 
finitely approximable and finitely axiomatizable. 
Exercise 9.26 Show that A* is the greatest logic in NExtGL into which Grz 
is embeddable by + . 
Exercise 9.27 Show that Grz 0 □</? is not embeddable into A* 0 (□</?)+ by + , 
where = a( o ). (Hint: consider the formula D(Dp —> Dq) V OfDq —> Dp).) 
Exercise 9.28 Show that Grz + a^( o , _L) is a modal companion of Int. 
Exercise 9.29 Let M* be the quasi-normal modal logic characterized by the 
Kripke frame with actual world o which is defined inductively 
as follows. Let (Wo,Ro) be the disjoint union of all finite rooted intuitionistic 
frames, and 2)*, for i > 1, the set of all antichains in We then 
let Wi = Wi-i U {ca : a E 2)*}, R% be the reflexive and transitive closure of 
Ri-1 U {(ca,a) : a E a} and, finally, 
Wu = U wi u W, R» = U Ri u {(o, a) : a € Wu}. 
i<u> i<uf 
Show that M* is the greatest modal companion of Int in ExtS4. 
Exercise 9.30 Prove that L E ExtS4 is a modal companion of Int iff it can be 
represented in the form 
L = S4 + {a(fo,£h,_L) : i e 1} + _L) : j E J}, 
where, for each i E /, there is an antichain a E S* such that x]= {x} U a| for no 
x in # and, for each j G J, $j contains a proper cluster. 
Exercise 9.31 Show that not all logics in ExtD4.3 are normal. (Hint: consider 
the logic characterized by the chain of three points 0, 1, 2 of which only 1 is 
irreflexive and 0 is the actual world.) 
Exercise 9.32 Which of the standard modal and si-logics can be axiomatized 
by frame formulas? 
Exercise 9.33 Show that S4.l' = S4 -f a(©, _L). 
Exercise 9.34 Prove that the class of finite transitive Kripke frames is modally 
definable iff it is closed under finite disjoint unions, reductions and generated 
subframes. (Hint: use the frame formulas.) 

332 
CANONICAL FORMULAS 
Problem 9.1 What is the structure of modal formulas p such that $ |= p 
implies (5 |= p, for every $ and every (cofinal) subframe <5 of $? 
Problem 9.2 Is it true that, for a si-logic L, ExtL contains an undecidable logic 
(an incomplete logic, a logic that is not finitely approximable) iff p~lL contains 
a logic with the same “negative” property? 
Problem 9.3 Is it true that, for a si-logic L, ExtL is continual iff p~xL is 
continual? 
Problem 9.4 Is M* finitely axiomatizable? 
Problem 9.5 Characterize the class of all (not necessarily transitive) refutation 
frames for a given modal formula and define “canonical” formulas for ExtK. 
9.8 	Notes 
The first frame-based (algebra-based, to be more precise) formulas were 
introduced by Jankov (1963b). With every finite pseudo-Boolean algebra 21 having 
a rooted dual he associated a formula, called the characteristic formula for 21, 
which is deductively equal to the frame formula /?t,(2l+, _L) (see Exercise 9 11). 
Jankov (1968b) used the characteristic formulas to construct the first (infinitely 
axiomatizable) si-logic that is not finitely approximable. He showed also that 
there is a continuum of logics in Extint. Jankov (1969) characterized the prime 
formulas in Int (Theorem 9.46 (ii)). 
In the modal case formulas deductively equal to _L) were introduced 
by Fine (1974a), who called them the frame formulas and used for the same 
purposes as Jankov (1968b) (see Exercise 9.12). The frame formulas are known 
also as Jankov or Jankov-Fine or splitting formulas (see also de Jongh, 1968). 
Blok (1978) noticed in fact that the logics in NExtK4 and Extint 
axiomatizable by a single frame formula are splittings (see Section 10.5) of these lattices 
and can be used for studying their structure. An example of such a use is 
Exercise 9.14. Other applications can be found in Chapter 12. For more references 
concerning splittings see Section 10.7. 
Fine (1985) introduced the subframe formulas (see Exercise 9.12) and studied 
the logics in NExtK4 axiomatizable by them. For details see Section 11.3. 
The apparatus of the canonical formulas was developed in a series of papers 
(Zakharyaschev 1983, 1984a, 1988, 1989, 1992) first for Extint, then for NExtS4 
and finally for ExtK4. (Theorem 9.44 (iii) and (iv) was proved in Zakharyaschev 
(1981).) It is not known whether it can be extended to ExtK. A positive 
solution to Problem 9.5 would provide us not only with a much deeper understanding 
of logics in ExtK but also of polymodal logics, as has been recently shown by 
Kracht and Wolter (1997). (There are, however, many obstacles to such a 
solution: frames for K have no clear upper and bottom parts, not all finite rooted 
frames give rise to splittings, the notion of subframe reflects the accessibility only 
“in one step”, and so forth; compare also Exercises 8.8 and 9.34.) Theorem 9.55 
is due to Segerberg (1975). 

NOTES 
333 
The Godel embedding of logics in Extint into those in NExtS4 was first 
considered by Dummett and Lemmon (1959) who defined the map r and showed 
that tL is a modal companion of L. A few years before the Kripke semantics 
was constructed they conjectured that if a si-logic L is characterized by a Kripke 
frame # = (W, R) then rL is characterized by = (wW,ujR). 
A systematic study of the relationship between Extint and NExtS4 was 
started by Maksimova and Rybakov (1974), Blok and Dwinger (1975), Blok 
(1976) and Esakia (1979a, 1979b). Maksimova and Rybakov introduced the maps 
p and <j (the latter only in an algebraic form), proved Theorems 9.56, 9.66 (i), 
(ii) and 9.68 and showed that p~lL = [tL,<jL]. That pS5 = Cl was first noted 
by Hallden (1949). 
Blok (1976) and Esakia (1979a, 1979b) established that aL = tL 0 Grz 
and proved Theorem 9.66 (iii). The semantic characterization of r, giving in 
particular a positive solution to the conjecture of Dummett and Lemmon, was 
obtained by Zakharyaschev (1989, 1991); the modal companion theorem and 
Theorem 9.72 were also proved there. 
The embeddings of logics in NExtGrz into those in NExtGL via the 
translation +, and thereby the embeddings of si-logics into normal extensions of GL via 
T+, were considered by Kuznetsov and Muravitskij (1986). They defined a map 
p from NExtGL into NExtGrz by taking pL = {<p : G L} and proved that 
p is a surjective semilattice 0-homomorphism (but not a lattice homomorphism, 
since in general we do not have p{L\®L\) = pLi®pL2)- Muravitskij (1988) 
observed that GL0T is the smallest logic in /x_1(Grz0r). As to the greatest one, 
Artemov (1987b) discovered that Grz is embedded by + into a proper normal 
extension of GL. Shavrukov (1991) proved that A* and S + A* are the greatest 
logics in NExtGL and ExtS, respectively, into which Grz is embedded by +. 
(That + embeds Grz into S was proved by Boolos (1980).) Both these logics 
turn out to be decidable, though are not finitely approximable. However, as was 
observed in Chagrov and Zakharyaschev (1992), the analog of the Blok-Esakia 
theorem does not hold in this case; for details see Exercise 9.27. 
By Shavrukov’s result, A* is the greatest companion of Int in NExtGL with 
respect to T+. This contrasts to Chagrov’s (1990b) result, according to which 
there is a continuum of maximal T+-companions of Int in ExtS. 
Chagrov (1985b) observed that there is a modal companion of Int in ExtS4 
which contains Grz properly (see Exercise 9.28.) Zakharyaschev (1996c) gave a 
characterization (in terms of canonical formulas) of the set of quasi-normal 
companions of Int and constructed both syntactically and semantically the greatest 
logic M* in this set. Like A*, M* is decidable but not finitely approximable 
(see Exercises 9.29 and 9.30). For a survey of results concerning embeddings of 
si-logics into modal logics consult Chagrov and Zakharyaschev (1992). 
Exercises 9.5-9.7 were taken from Kracht (1990) and Wolter (1993). The 
result of Exercise 9.10 was also proved by Wolter (1993). Exercises 9.17-9.20 are 
due to Jankov (1968a) and Exercises 9.23, 9.24 to Rybakov (1976, 1977). The 
results of Exercise 9.25 were obtained by Maksimova and Rybakov (1974) and 
Rybakov (1976). 

Part IV 
