<!-- Source: Chagrov & Zakharyaschev (1997). Modal Logic (Oxford Logic Guides 35). Part I: Introduction — classical logic, intuitionistic logic, modal logics (Ch 1-4). BibKey: ChagrovZakharyaschev1997 -->

Introduction 
The word “logic” is used in this book in two senses. In the broader sense logic 
or better mathematical logic is the discipline studying mathematical models of 
correct human reasoning. While constructing such models, it is usually assumed 
that reasoning consists of propositions, that is sentences whose content may be 
evaluated as true or not true. For example, Goldbach’s conjecture 
Every even number that is greater than 2 can be represented as the sum of two prime 
numbers, 
Godel’s second theorem 
If the formula 0 = 1 is not provable in formal Peano arithmetic PA, then the statement 
“0 = 1 is not provable in PA” is not provable in PA, 
and Winnie-the-Pooh’s song1 
If Rabbit 
Was bigger 
And fatter 
And stronger, 
Or bigger 
Than Tigger, 
If Tigger was smaller, 
Then Tigger’s bad habit 
Of bouncing at Rabbit 
Would matter 
No longer, 
If Rabbit 
Was taller 
are propositions. GodePs second theorem and Winnie-the-Pooh’s song provide us 
with examples of compound propositions: they can be constructed from simpler 
propositions such as 0 = 1, Rabbit is bigger than Tigger, etc., with the help of 
logical connectives which are expressed by the words like “and”, “or”, “if... then 
...”, “not”, “provable in PA”, “no longer”. In this sense Goldbach’s conjecture 
is an elementary or atomic proposition. 
If the intrinsic structure of atomic propositions is of no concern to us then we 
are in the realm of propositional logic which studies schemes of correct reasoning 
on the base of how propositions are constructed from atoms regardless of their 
content. “If then or /0” is a simple example of a propositional scheme which 
is valid for all concrete propositions ip and 
Propositional logic deals with formal languages containing propositional 
variables whose values may be arbitrary propositions, propositional constants like 
“truth” and “falsehood” and formulas constructed from variables and constants 
using logical connectives. In this book we will consider only languages with the 
constant “falsehood” (_L), the connectives “and”, “or”, “if ... then ...”, which 
are denoted by A, V, —> and called conjunction, disjunction and implication, 
respectively, and the modal connective □ called the necessity operator which, 
depending on the context, is read as “it is necessary” or as “it is obligatory” or 
as “it is provable” or “it is true now and always will be true”, etc. 
1A.A. Milne. The house at Pooh corner. 

2 
INTRODUCTION 
In the narrower sense, by a logic in a given propositional language we will 
mean simply the set of all formulas in the language representing propositional 
schemes which are valid from a certain point of view. Different logics appear not 
only because of the possibility of varying the language, i.e., on account of the 
desire to study various logical connectives, but also for the reason that the same 
connectives may be interpreted in different ways. 
In this part we briefly consider a few most important propositional logics 
which give rise to those big families of logics we shall deal with in the sequel. 

1 
CLASSICAL LOGIC 
Classical propositional logic was created by Boole about 150 years ago (see Boole, 
1947). It holds the central position among propositional logics not only due to 
its venerable age. In fact, it represents the simplest model of reasoning based 
upon the assumption that every proposition is either true or false. Many other 
logics are either contained in the classical one or built on its basis by enriching 
the language with new connectives. 
1.1 	Syntax and semantics 
Fix the propositional language £ whose primitive symbols (alphabet) are: 
• the propositional variables po,Pu • • 
• the propositional constant _L (falsehood); 
• the propositional connectives: A (conjunction), V (disjunction), —> 
(implication); 
• the punctuation marks: ( and ), 
and the formulas of £ (or £-formulas, or simply formulas if £ is understood) are 
defined inductively: 
• all the variables in £ and the constant _L are atomic £-formulas (or simply 
atoms); 
• if (p and 0 are £-formulas then (</? A 0), {if V 0) and {ip —> 0) are also 
^-formulas; 
• a sequence of primitive symbols in £ is a formula iff2 this follows from the 
two preceding items. 
Example 1.1 The following sequence of symbols is a formula: 
(((p0 -*■ -1) v Pi) -» ((pi Ap2) Ap3)). 
We will denote propositional variables by the small Roman letters p, q, r, 
possibly with subscripts or superscripts; the small Greek letters </?, 0, x and 
maybe some others are reserved for formulas, and capital Greek letters like T, 
A, E are used for denoting sets of formulas. 
The set of all variables in £ is denoted by Var£. Unless otherwise indicated, 
we will assume Var£ to be countable. This restriction is of not so great 
importance, and almost all the results to be obtained below can be generalized (in one 
way or another) to languages with finitely or uncountably many variables. 
2Iff is the standard abbreviation for “if and only if’. 

4 
CLASSICAL LOGIC 
The set of all C-formulas is denoted by ForC. The formulas used in the 
construction of a formula p according to the definition above as well as p itself are 
called subformulas of p. Sub<^ is the set of all </?’s subformulas and Varp is the set 
of all variables in Sub<^. If Vary = 0 then p is called a variable free formula. We 
use the notation p(q\,..., qn) to reflect the fact that Woxp C {qi,..., qn}- We 
rely upon the reader’s common sense and give no exact definition of occurrence 
of a subformula in a formula. 
The propositional connectives -> (negation), (equivalence) and the constant 
T (truth) can be defined as abbreviations: 
= (v -+ 
(V++ r/>) = (<p $) A {ip -* <p), 
T = (1 -> X). 
If a formula p is of the form or (ip © x), for © € {A, V, —>, <->}, then -> or, 
respectively, © is called the main connective of p. The formula %p is said to be 
the premise of the implication (ip —> x) and X l^s conclusion. 
We shall use the following standard conventions on representation of formulas: 
we assume -> to connect formulas stronger than A and V, which in turn are 
stronger than —> and <->, and omit those brackets that can be recovered according 
to this priority of the connectives. We shall also write p\ V p^ V ps V ... V pn or 
VIU Vi instead of (... ((pi V p2) V p3) V ... V pn) and pi A p2 A p$ A ... A pn 
or K=i V* instead of (... {(<px A <p2) A ^3) A... A </?„); Vi60 <Pi and Ai€0 <Pi mean 
X and T, respectively. Each '*pl in a formula of the form V”=i ‘ri or hi=i Vi is 
called a disjunct or a conjunct of the formula, respectively. 
With the help of these abbreviations and conventions, the formula in 
Example 1.1 can be now written much more briefly: 
"•Po V pi -> pi A p2 A p3. 
We have introduced the syntax of classical logic and now turn to its semantics, 
i.e., define the classical interpretation of the language C. 
The fundamental semantic assumption characterizing classical logic is as 
follows: 
• each atomic proposition is either true or false (but not simultaneously), 
with _L being always false; 
• the truth-values of compound propositions are uniquely defined by the 
following truth-table, where T and F stand for “true” and “false”, respectively: 
X 
ip Ax 
F 
F 
F 
F 
T 
T 
T 
F 
T 
F 
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
F 
T 
T 
T 
T 
T 
F 
T 

SYNTAX AND SEMANTICS 
5 
Thus, according to this truth-table, “false” means just “not true”. 
Starting from the assumption above, we can give now an exact definition of 
classical model of the language C. 
A classical model of C is any subset DJI of Var£. Less formally this means 
that DJI contains those and only those atomic propositions that are regarded to 
be true. By induction on the construction of a formula p we define a relation 
DJI 1= p which is read either as “p is true in the model DJI” or as “DJI is a model 
for p”: 
not DJI 1= _L; 
DJI |= p iff p € SDt, for every p £ Var£; 
DJI \= 'ip Ax iffDJl\=,ip and DJI |= x\ 
DJl\= ip\J x iff |= or |= x; 
9DT )= -0 —► x iff 1= X whenever DJI [= rp. 
If DJI 1= p does not hold then we write DJI p and say that either p is false in 
DJI or DJI is a countermodel for p or DJI refutes p. 
Observe at once that truth or falsity of a formula p in a model DJI depends 
only on the truth-values of p’s variables in DJI. In other words, the following 
proposition holds. 
Proposition 1.2 Suppose that models DJI and 01 are such that 
m^piff<yi\=p 
for all variables p in some set Var C Var£. Then, for every formula p with 
Varp C Var, 
DJl\=piffDl\=p. 
Proof An easy induction on the construction of p. □ 
A model DJI is called a model for a set T of formulas (notation: DJI [= T) if all 
formulas in T are true in DJI. 
A formula p is said to be (classically) valid if it is true in all models of £; in 
this case we write \= p. 
Example 1.3 To show the validity of the formula 
P V (p-> -L), 
known as the law of the excluded middle, it suffices to construct the truth-table 
for p V (p —> 1), which looks like this 
V 
V 
( V 
-► 
-L ) 
F 
T 
F 
T 
F 
T 
T 
T 
F 
F 
and make sure of that the column under the main connective of our formula 
contains only T. 

6 
CLASSICAL LOGIC 
Example 1.4 The truth-table for (p A q —> _L) —> (p 
( P A q -> 
F F F T 
F F T T 
T F F T 
T T T F 
T 
T 
F 
F 
contains F in the column under the main connective, which means that this 
formula is not valid. 
Finally, we define classical logic in the language C as the set Cl/: of all valid 
^-formulas or in symbols 
Cl£ = {<p e ForC : |= <p}. 
Since C is always understood, we drop the subscript and write simply Cl. 
1.2 	Semantic tableaux 
Having defined classical or some other logic, we naturally face the problem of 
recognizing, given an arbitrary formula, whether it belongs to the logic or not. 
If there is an algorithm deciding this problem for a logic then the logic is called 
decidable. 
The decidability of classical logic becomes evident as soon as we observe 
that the truth-value of a formula <p(pi,... ,pn) depends only on the truth-values 
assigned to pi,... ,pn. A trivial decision algorithm is as follows: we just write 
down all 2n possible assignments of F and T to pi,..., pn and calculate the 
truth-value of <p for each of them; <p is in Cl iff all calculated values are T. 
Yet there are a dozen subtler ways of determining validity. Here we consider 
one of them, a variant of the semantic (or Beth) tableau method. Roughly the 
underlying idea is that instead of climbing bottom-up from the truth-values 
of (p’s variables to the truth-values of (p, we can move top-down, purposefully 
constructing a countermodel for (p. The semantic tableau method not only gives 
a more convenient tool for handling classical formulas (though in the worst case 
it works as ineffectively as the truth-table method). It is more important for us 
that the method can be extended to some other logics with different semantics 
which does not admit truth-tables. 
Let us start with examples. 
Example 1.5 Suppose we want to determine whether the formula 
v = Up q) -> p) -»■ p, 
known as Pierce’s law, is valid or not. To solve this problem let us try to construct 
a countermodel for (p. 
We begin the construction with forming a tableau consisting of two parts: in 
the left one we put those subformulas of <p which we want to be true, while the 

SEMANTIC TABLEAUX 
7 
right part contains subformulas which are to be made false. Since we want ip to 
be false, it should be put in the right part. The truth-table for —> tells us that 
cp is false iff (p —► q) —> p is true and p is false; so we put the former formula in 
the left and the latter in the right part of the tableau: 
(p q) p 
Now, to make (p —j► q) —^► p true we h 
p true or to make p —> q false. So the 
((p^q)^p)^p 
p 
ave two possibilities, namely, either to make 
tableau above can be extended in two ways: 
(p->q)-*p 
P 
(ip -► q) -► p) -> p 
p 
(p^q)-+p 
p 
((p q) ~^p)^p 
p 
p-+q 
Q 
But then we arrive at a contradiction: both tableaux require p to be 
simultaneously true and false. This means that there is no countermodel for <p, and 
hence 
((p-»g) ->p) ci. 
Example 1. 
for 
6 Now let us use the same technique to construct a countermodel 
<p = r A (-ip V -iq) —► r A (p V -iq). 
The first four lines in the tableau are clear: 
r A (-ip V -iq) —> r A (p V ->#) 
r A (-ip V -iq) 
r 
-'P V -i q 
r A (p V -iq) 
But now there are two ways to make r A (p V -iq) false: to put r in the right part 
or to put p V -ig there. Thus we obtain two extensions of the tableau: 
(a) 
r A (-p V -iq) 
r A (-p V -i q) ->rA(pV q) 
r A (p V -iq) 
r 
> 
p- 
r 

8 
CLASSICAL LOGIC 
(b) 
r A (-p V -iq) 
r A (-ip V -iq) —* r A (p V ->q) 
r A (p V ~*q) 
r 
r 
> 
?• 
< 
J 
►Q 
Q 
The requirements of the tableau (a) are inconsistent. And (b) again has two 
extensions: to make -«p V true, we can put in the left part either -« p or ->q. 
The latter alternative leads immediately to a contradiction, while the former one 
gives us the tableau 
r A (-ip V -iq) —* r A (p V ->q) 
r A (-ip V -*q) 
r A (p V ->q) 
r 
4 
< 
J 
< 
J 
q 
-'Q 
-.p 
whose requirements can be satisfied by assigning F to p and T to q and r. Hence 
<p is false in every model 9Jt such that DJI \= q, DJI \= r and DJI ^ p. 
Now we present this procedure of juggling with formulas as a formal system 
and show that applying it to an arbitrary given formula, in a finite number of 
steps we shall either construct a countermodel for it or establish its validity. 
We will represent a tableau as a pair of sets of formulas: one of them contains 
all the formulas in the left part of the tableau and the other those in the right 
part. Thus, a semantic tableau in the language £ is just a pair t = (r, A) with 
r, A C For£. 
A tableau (T, A) is called (downward) saturated in Cl if, for all formulas 
</>, X € For£, 
(SI) 
ip A X € r 
implies 
V>er 
and 
X€l\ 
(S2) 
Ax € A 
implies 
Ip £ A 
or 
xe A, 
(S3) 
tpvxeT 
implies 
V>er 
or 
xer, 
(S4) 
Ip V x € A 
implies 
ip € A 
and 
X € A, 
(S5) 
V> x € r 
implies 
ip € A 
or 
xeT, 
(S6) 
ip —■> x € A 
implies 
and 
X€ A. 
(r, A) is disjoint if T Pi A = 0 and _L I\ Say that a tableau tf = (r', A') is an 
extension of a tableau t = (r, A) (or t is a subtableau of t') and write t C tf if 
r C T and A C A'. 
A tableau t = (r, A) is called realizable if there is a model DJI such that 
DJI |= xjj for all ^ € T and DJI X for all x € A; 

CLASSICAL CALCULUS 
9 
in this case DJI is said to realize t. 
Proposition 1.7 A tableau t = (r, A) is realizable iff it can be extended to a 
disjoint saturated tableau tf = (P, A'). 
Proof (=>) Suppose 9Jt is a model realizing t. Put Tf = {(p € ForC : 3DT |= <p} 
and A' = {<p £ For£ : DJI ^ </?}■.It is clear that Tf D A' = 0, _L ^ T', T C P 
and A C A'. Comparing conditions (S1)-(S6) with the definition of the truth- 
relation 1= in Section 1.1, it is easy to see that t' satisfies those conditions and 
so is saturated. 
(<=) It suffices to show that every disjoint saturated tableau (P, A') is 
realizable. Define a model DJI by taking 97t = T' n Var£. By induction on the 
construction of <p one can readily establish that <p € Tf implies DJI \= ip and 
<p € A' implies 9Jt ^ □ 
Proposition 1.7 provides us in fact with an algorithm for verifying realizability 
of finite tableaux. Indeed, conditions (S1)-(S6) can be read as the saturation 
rules: 
(SRI) if ^ A x € T then add ^ and x to T, 
(SR2) if ^ A x € A then add ^ or x to A, 
etc. 
And then we obtain 
Proposition 1.8 A finite tableau t\ is realizable iff there is a sequence ti,..., tn 
such that tn is a disjoint saturated tableau and each ti+\ is obtained from ti by 
applying to it one of the saturation rules. 
Proof Exercise. □ 
As another exercise we invite the reader to prove that all formulas in Table 1.1 
are in Cl. In what follows we will use those formulas without any comments. 
1.3 	Classical calculus 
Classical logic can be represented as a formal axiomatic system, i.e., as a calculus, 
in several ways. Since in this book we are not going to deal with proof theory, 
we consider here only a Hilbert-type calculus which is rather convenient for 
theoretical constructions but not for practical use. 
Classical propositional calculus Cl in the language C contains the following 
axioms and inference rules: 
Axioms: 
(Al) po -> (pi -► p0), 
(A2) (Po -> (pi -> p2)) -> ((po -> Pi) -> (po -> P2)), 
(A3) Po Api —► po, 
(A4) Po Api —> pi, 
(A5) Po -► (Pi ->Po Api), 
(A6) Po —> Po V pi, 

10 
CLASSICAL LOGIC 
Table 1.1 A list of classically valid formulas 
Formula 
Name 
p A p p, p\f p p 
p Aq q Ap, p Vq «-* g Vp 
p Al^l, p A T <-> p 
p V 1 ^ p, p V T T 
-L -► P> P -► T 
p A -ip —> g 
p A (g A r) (p A g) A r 1 
p V (q V r) (p V q) V r J 
(p A g) V q *-+ q, p A (p V g) p 
p A (q V r) «-* (p A q) V (p A r) 1 
p V (g A r) *-+ (p V q) A (p V r) J 
p->(q^p) 
(p ->q)-> ((q ->r)->(p-> r)) 
(p-> (q-> r)) ->• ((p -► 9) -► (p -> r)) 
pAq-^p, p-^pWq 
(p V </) A (p V -ig) «-* p 
p—*(q—*phq) 
(p (q r)) *-* (pAg-» r) 
The laws of idempotency 
The laws of commutativity 
Duns Scot us’ law 
The laws of associativity 
The laws of absorption 
The laws of distributivity 
The law of simplification 
The law of syllologism 
Frege’s law 
The law of adjunction 
The law of importation and 
exportation 
(P q) ^ ((P —►?")—> (p —► 9 A r)) 
(p —> q A r) «-* (p —► g) A (p —► r) 
(P -► «) A (p' -> q') -» {p V p' -» q V q') 
(p->q) A (p' -> g') -► (p Ap' -» q A g') 
(p-*r)->((g-»r)^(pVg-> r)) 
->(p V q) +-> -p A -iq 1 
->(p A 9) <-» -ip V -<q J 
(p-> q) -*p V q 
(p->q) *-> ->(p A ->9) 
((p -► q) -» p) -» p 
p V -ip 
(P 9) «-» (^9 -» ->p) 
P «-* —1—ip 
(pA^) V(pA -»g) «-* p 
De Morgan’s laws 
Pierce’s law 
The law of the excluded middle 
The law of contraposition 
The law of double negation 

CLASSICAL CALCULUS 
11 
(A7) pi —> po V pi, 
(A8) (p0 -> p2) -> ((pi -»•P2) -*• (po Vpi —> p2)), 
(A9) -L —> poj 
(A10) po V (p0 -» -L); 
Inference rules: 
Modus ponens (MP): given formulas p and p —► ip, we obtain xjj, 
Substitution (Subst): given a formula <p, we obtain ps, 
where s, a substitution, is a map from Var£ to For£ and ps is defined by 
induction on the construction of p: ps = s(p) for every p £ Var£, ±8 = 1. and 
O x)s = ^0 X*h for O € {A, V, ->}. 
A substitution s such that s(p) = ij),...,s(q) = X and s(r) = r, for all 
variables r different from p, ...,q, will be denoted by {^>/p,..., x/q}- Given 
substitutions s' and s", we denote by s's" their composition, i.e., the substitution 
s such that ps = (ps^s” for every variable p. 
A formula p is said to be derivable in Cl if there is a derivation of pin Cl, i.e., 
a sequence pi,..-,pn of formulas such that pn = p and for every i, 1 < i < n, 
Pi is either an axiom or obtained from some of the preceding formulas in the 
sequence by one of the inference rules; the number n is called the length of this 
derivation. If p is derivable in Cl then we write \~ci P or simply b p when this 
does not involve ambiguity. 
Example 1.9 The following sequence is a derivation of p —► p, for any formula 
p: 
(1) 
(po -» (pi -»Pi)) -» ((po -> Pi) (po -*• P2)) 
(A2) 
(2) 
(<p ->■ ((<p -+<p)-> <p)) -*• 
(by Subst 
((<p (<p ->■ <p)) ->(</?->• <p)) 
from (1)) 
(3) 
Po -> (pi -*• Po) 
(Al) 
(4) 
->• ({9 f) -*•<p) 
(by Subst 
from (3)) 
(5) 
(<p (<p -*• <p)) (<p -*• <p) 
(by MP 
from (2), (4)) 
(6) 
<p ->• W -*■<p) 
(by Subst 
from (3)) 
(7) 
(by MP 
from (5), (6)). 
Example 1.10 Below is a derivation of p V ^ —► xjj V p, for any formulas p and 
: 

12 
CLASSICAL LOGIC 
(1) Pi^PoVpi (A7) 
(2) po -► po V pi (A6) 
(3) ip —> ^ V <p (by Subst 
from (1)) 
(4) 'ijj —> 'ijj V </? (by Subst 
from (2)) 
(5) (po -» P2) ((pi P2) -> (po V pi -> p2)) (A8) 
(6) (<p —> xj; V <p) —> (('i/; —>'0V<p)-^(</?V'0—►'i/'N/ <p)) (by Subst 
from (5)) 
(7) (^ —► ^ V <p) —► (<p V ^ ^ V </?) (by MP 
from (3), (6)) 
(8) <p V ip —> xjj V <p (by MP 
from (4), (7)). 
As an exercise we invite the reader to construct a derivation of an arbitrary 
formula of the form (<p V ^>) V x <p V V x)- 
Observe that in the derivations above the rule Subst was applied only to 
axioms. We call such kind of derivations substitutionless. 
Proposition 1.11 Each formula ip derivable in Cl has a substitutionless 
derivation in Cl. 
Proof The proof proceeds by induction on the length of a derivation of ip. The 
basis of induction is trivial, since in this case ip is an axiom. 
Suppose now that the claim of the proposition holds for all formulas having 
derivations of length < n, for some n > 1, and let <pi,..., <pn be a derivation of 
ip = ipn. If <pn is the result of applying MP to and ipj, for 1 < i,j < n, then 
we can readily construct a substitutionless derivation of ip from substitutionless 
derivations of ipi and ipj, which exist by the induction hypothesis. 
Suppose that ipn = ipiS. Let be a substitutionless derivation 
of ipi = 'ijjm and aU the axioms occurring in it. Then the sequence 
Xi, • • •, Xui> is5 • • •, mS is a substitutionless derivation of <pn, which follows from 
the fact that (^ —> x)s = -+ Xs and = </>(s's), for all formulas ^>, x 
and every substitution s'. □ 
Proposition 1.11 shows that classical calculus can be defined without using 
Subst. We can, for instance, replace po, Pi, P2 in axioms (Al)-(AIO) with the 
symbols <po, <Pi, <P2 in our metalanguage and regard the resulting expressions as 
axiom schemes representing in fact the infinite set of substitution instances of 
(Al)-(AIO). 
Let T be a set of formulas. A sequence <pi,..., <pn is called a derivation of ip 
from the set of assumptions V if <pn = ip and for every z, 1 < i < n, ipi is either 
an axiom or an assumption in T or obtained from some of the preceding formulas 
by one of the inference rules, with Subst being applied only to axioms. If there 
is a derivation of <p from T, we say that ip is derivable from V and write V bci 
or simply r b ip if understood. By Proposition 1.11, Y- ip iff 0b ip. For brevity we 

CLASSICAL CALCULUS 
13 
will write instead of TU {0i, ..., 0n} P and r, A b p instead 
of T U A b p. It follows immediately from the definition that 
T b p and T C A imply A b p, 
r b ► 0 and A b p imply r,Ahf 
Now we prove a theorem which turns out to be very useful for establishing 
derivability. 
Theorem 1.12. (Deduction) IfT, 0 b p then r b 0 —> </?. 
Proof Let <£i,..., pn be a derivation of p = pn from TU {0}. By induction on 
i we show that T b 0 —► pi for every z G {1,..., n}. 
If pi is an axiom or a formula in T then the sequence 
(!) <Pi 
(2) po -► (Pi -> Po) (Al) 
(3) pi —► (0 —► </?*) (by Subst from (2)) 
(4) 0 —> </?* (by MP from (1) and (3)) 
is a derivation of 0 —► pi from T. 
If pi = 0 then, as was shown in Example 1.9, b 0 —► p^ and so T I- ^ 
If pi is obtained from pj and pk = Pj —> Pi by MP then, by the induction 
hypothesis, T b 0 —► (</?.,• —► </?*), T b 0 —► pj, and using (A2), Subst and twice 
MP we obtain T h ^ 
Finally, if pi = then ^ is an axiom and the derivation of 0 —► pi from 
T we need is the sequence pj, (1),..., (4). □ 
The following examples show how the deduction theorem can be used for 
proving derivability. 
Example 1.13 For every formulas p, 0, we have 
i- (W> -+x)-+(<p^ x))- 
Indeed, by the deduction theorem it suffices to show that 
0 	-> x, X 
which can be done simply by applying MP twice. 
Example 1.14 Let us prove that 
r h TpV p and r,ph ip imply r b 0. 
By the deduction theorem, T b p —► 0. Besides, as we know, b 0 —► 0. By Subst 
and (A8), we have 
b (0 —► 0) —> ((p —0) —> (0 V p —► 0)) 
from which, using MP thrice, we obtain T b 0. 

14 
CLASSICAL LOGIC 
Example 1.15 Now we show that, for every ^ and x> 
i- v (v> —► x)- 
We have: 
b ^ V (</> _> x) 
(by Subst 
from (A6)) 
(by MP) 
(by Subst 
from (A9)) 
^ > _L, 'p P -L 
b-L-^X 
^-►-Lb^V^-^x) 
b (i/^ —> -L) —> V (i/; —> x) 
ip —► _L b *0 —> x 
(by MP and 
deduction theorem) 
(by (A7) and MP) 
(by deduction 
h (ip -» V V (V> -» x)) -► (((V1 
v (V> -*• x)) -► v (-tp -> _l) ->tp v (V> -> x))) 
theorem) 
(by Subst 
from (A8)) 
whence using (A10), Subst and MP thrice we obtain b ^ V (^ —► x)- 
Calculus Cl is said to be sound if b ip implies |= <p, for all ip G For£, and 
complete if the converse implication holds. Thus, the soundness and completeness 
of Cl means that the set of derivable formulas coincides with the set of valid 
formulas. 
Theorem 1.16. (Soundness and completeness of Cl) For each formula ip, 
•" <P iff \= <P- 
Proof (=>) To prove the soundness it suffices to verify that all axioms of Cl are 
valid and the inference rules preserve the validity. We leave this to the reader. 
(<=) Suppose \/ <p and show that the tableau to = (0, {</?}) is realizable, which 
means that ^ ip. 
Say that a tableau (T, A) is consistent in Cl if T bci V ... V ipm holds for 
no ^i,..., 'ipm G A, ra > 0. We remind the reader that the disjunction of the 
empty set of formulas is _L, and so the consistency of (T, A) means in particular 
that T _L. Since \/ ip and I/ _L, the tableau to is consistent. 
Let ..., ipn be a list of all formulas in Sub ip. Define a sequence of tableaux 
to = (r0, A0),..., tn = (rn,An) by taking 
. _ f (r„A, U {<^i+i}) if (ri, Ai U {<^i+i}) is consistent 
1+1 \ (1^ U {y>i+i}, Aj) otherwise. 
Notice that Tn U An = Suby>. Let us show that tl+\ is consistent whenever tt 
is consistent. Indeed, otherwise using Example 1.10 and axioms (A6)-(A8) we 
could find formulas 1, • • •, Wm € Aj such that 
h V'l V. . . V V'm V <pi+l, 

BASIC PROPERTIES OF CL 
15 
r<,^i+i b </>l V... V^m- 
But then, by Example 1.14, T* b \pi V ... V contrary to the consistency of 
ti. Thus tn is consistent. 
Now we show that the tableau tn is disjoint and saturated. By Proposition 1.7, 
it will follow that to is realizable. Since tn is consistent, )- \p \p and b _L —► xp 
for every formula 'ip, tn is disjoint. * 
To verify condition (SI), suppose that 'ip A x £ Pn and 'ip G An. However 
by (A3), 'ip A x b 'ip, which is a contradiction, since tn is consistent. Conditions 
(S2)-(S5) are checked analogously with the help of axioms (A5)-(A7) and 
Example 1.9. 
As for (S6), suppose that ip —> x € An, but either \p £Tn or x ^ An. Then 
either x € Tn or xp G An. Both these cases contradict the consistency of tn, 
since, by (Al), x b xp —► x and, as was shown in Example 1.15, h ip v (V> -> x). 
Observe by the way that axiom (A10) was used only in the proof of (S6). 
□ 
Corollary 1.17 Cl = {</? G For£ : \~ci v?}. 
Thus, validity is a semantic counterpart of derivability in Cl. The following 
generalization of Theorem 1.16 provides a semantic counterpart for the notion 
of derivability from assumptions. 
Theorem 1.18. (Strong completeness of Cl) Every tableau (T, A) 
consistent in Cl is realizable. In particular, for every T and every ip, T \r <p iff DJI \= T 
implies DJl\= tp, for every model DJI. 
Proof The proof proceeds by the same scheme as the proof of (<=) in 
Theorem 1.16. The only difference is that now the process of saturating (r, A) may 
be infinite (cf. the proof of Lindenbaum’s lemma in Section 5.1). □ 
The same technique yields 
Theorem 1.19. (Compactness) A tableau (T, A) is realizable iff every tableau 
(r', A') with finite Tf C T and A' C A is realizable. In particular, a set of 
formulas has a model iff its every finite subset has a model. 
Proof (=>) is trivial and to prove (4=) it is enough to observe that every 
derivation involves only finitely many formulas and use Theorem 1.18. Details are left 
to the reader. □ 
1.4 Basic properties of Cl 
In this section we formulate a number of important syntactical properties of 
logics in the language C and prove or disprove them for classical logic Cl. 
By a logic in the language C we mean here an arbitrary set L C For£ which 
is closed under the inference rules modus ponens and substitution. Derivations 
in L are defined in the same way as in Cl with the exception that axioms now 
are not those of Cl but all formulas in L. If Li, L2 are logics and L\ C I/2 then 
L2 is called an extension of L\ and L\ a sublogic of L2. 

16 
CLASSICAL LOGIC 
Consistency. A logic L is called consistent if L ^ For£. If L contains 
formula (A9) then it is consistent iff _L ^ L. And if L accepts the law of Duns 
Scot us (see Table 1.1) then L is consistent iff p G L and -up G L for no formula 
p. Since j^= _L, we have 
Theorem 1.20 Cl is consistent. 
Decidability. As was already observed in Section 1.2, we have 
Theorem 1.21 Cl is decidable. 
Post completeness. A logic is said to be Post complete if it is consistent 
and has no proper consistent extension. 
Theorem 1.22 Cl is Post complete. 
Proof Suppose L is a logic such that Cl C L and P g L—Cl for some p G For£. 
Let DJI be a model refuting p. Define a substitution s by taking 
/Tif DJl\=Pi 
^lS \ _L otherwise. 
Then ps is obviously false in every model. Therefore, ps —► _L G Cl and, since 
ps G L, we obtain by MP that _L G L. But this means that L is inconsistent. 
□ 
We say a logic L is 0-reducible if, for every formula p ^ L, there is a variable 
free substitution instance ps & L. As a consequence of the proof of Theorem 1.22 
we immediately obtain 
Theorem 1.23 Cl is 0-reducible. 
Independent axiomatizability. A logic L in the language £ is 
independently axiomatizable by a set (of independent axioms) F C For£ if the closure of 
T under MP and Subst is L but no proper subset of T possesses this property. 
Theorem 1.24 Cl is independently axiomatizable. 
Proof Follows from Theorem 1.16 according to which Cl i6 the closure under 
MP and Subst of a finite set of formulas. In fact one can show that (Al)-(AlO) 
is a set of independent axioms for Cl. .□ 
Structural completeness. Let pi,..., pn, p be some formulas. We will 
understand the figure 
• • • > Vn (11) 
as the inference rule which, for every substitution s, derives ps from the formulas 
pis,..., pns. Rule (1.1) is called admissible in a logic L if, for every substitution 
s, ps G L whenever p\8,... ,pns G L. By definition, the rule p,p —► q/q (i.e., 
modus ponens) is admissible in any logic. We say also that rule (1.1) is derivable 

BASIC PROPERTIES OF CL 
17 
in L if there is a derivation of p in L from the set of assumptions {p\,..., pn}. 
It should be clear that every derivable rule in L is also admissible in L. 
By the deduction theorem and the law of importation and exportation, (1.1) 
is derivable in Cl iff p\ A ... A pn —► p £ Cl. A logic L is called structurally 
complete if every admissible rule in L is derivable in L. 
Theorem 1.25 Cl is structurally complete. 
Proof Suppose rule (1.1) is admissible in Cl but not derivable, i.e., 
pi A ... A pn —> Cl. 
By Theorem 1.23, there is a variable free formula p\S A... A pns —> ps which is 
false in every model. This means that the formulas p\s,..., pns are valid, while 
ps is not. Therefore, p\8,... ,pns € Cl but (ps $ Cl, which is a contradiction. 
□ 
It follows from Theorem 1.25 and the decidability of Cl that there is an 
algorithm which can recognize whether an arbitrary given rule is admissible in 
Cl. In other words we obtain 
Corollary 1.26 The admissibility problem for inference rules in Cl is decidable. 
As examples of admissible inference rules in Cl we present here the following 
congruence rules: 
p<->q 
p A r <-> q A r 
p<->q 
r Ap <-> r A q 
p<->q 
p V r <-> q V r 
p<->q 
rVp^rVq 
p <-> q p <-> q 
(jp—> r) <-> (q r) (r —► p) <-> (r —> q) 
Taken together these rules yield the following theorem which is useful for the 
equivalent transformation of formulas. 
Theorem 1.27. (Equivalent replacement) Let iffy) be a formula 
containing an occurrence of a formula xp and <p{x) obtained from (f(xp) by replacing this 
occurrence with an occurrence of a formula y. Then, for every logic L in which 
the congruence rules are admissible, xp <-> \ € L implies ip(xp) <-+ <p(x) € 
Proof An easy induction on the construction of tp using the admissibility of 
the congruence rules above is left to the reader as an exercise. □ 
Craig interpolation property. Say that a logic L has the Craig 
interpolation property if, for every formula p —> xp € L, there is a formula x> whose 
variables, if any, occur both in <p and xp, such that p —> \ € L and x ^P € £; 
the formula x is called then an interpolant for p and xp in L. 

18 
CLASSICAL LOGIC 
Theorem 1.28. (Craig interpolation) Cl has the Craig interpolation 
property. 
Proof Suppose formulas (p and ip have no interpolant. Our aim is to show 
that in this case the tableau to = ({<p}, {^j) is realizable, and so tp ip qt. 
Cl. The proof below resembles the saturation technique used in the proof of 
Theorem 1.16, though it is based on somewhat different principles. 
Say that a tableau (T, A) is separable (relative to (p and ip) if there is a formula 
X such that Varx Q Var<p fl Yarip and both tableaux (T, {x}) and ({x}, A) are 
not realizable (= inconsistent). According to our assumption, to is not separable. 
Call (T, A) complete (relative to <p and ip) if, for every £ Sub<^, ipf £ Sub ip, 
one of the formulas <// or -«// is in T and one of the formulas ip1 or -*ip' is in 
A. Starting from to we will construct a complete inseparable extension of to and 
then show that it is realizable. 
Let </?i,..., (fk and ip\,..., ipm be lists of all s and ip’s proper subformulas, 
respectively. Define a sequence to = (To, Ao),..., tn = (Tn,An), where n = 
k + m, by taking, for i < k and j < ra, 
. _ f (I\ U {</?i+i}, A0) if (I\ U {</?i+i}, Ao) is inseparable 
1+1 \ (I\ U {-k^+i}, Ao) otherwise, 
, f (rfe, Ak+j u {ipj+1}) if (Tfc, Ak+j U {ipj+1}) is inseparable 
fc+j+i | (rfc, Ak+j U {-^ipj+1}) otherwise. 
Clearly, tn is complete. We show that, for i < fc, ti+i is inseparable whenever 
ti is inseparable. Indeed, otherwise we would have two formulas xi and X2> 
whose variables are in Var</?nYarip, such that the tableaux (T* U {<Pi+1}, {xi}), 
({Xi}, Ao), (Ti U {X2}) and ({X2}? A0) are not realizable. But then the 
tableaux (Ti, {xi V X2}) and ({xi V X2}> Ao) are not realizable either, contrary 
to ti being inseparable. In a similar way one can show that, for j < ra, tfc+j+i is 
inseparable if tk+j is so. 
Thus, tn is complete and inseparable. Define a model 9Jt by taking, for every 
p £ Var£, 
p £ SDT iff p £ Tn or ip £ An. 
We show that 9Jl realizes tn and so to as well. Namely, by induction on the 
construction of x we prove that 
X £ Tn iff DJI [= x, for x ^ Sub<p, 
X £ An iff 9JI ^ x, for x £ Subip. 
The basis of induction is obvious. Suppose x = Xi ~^► X2, X € Sub<p, x £ Tn 
and x* Then SDt f= x1, X2 and so, by the induction hypothesis, 
Xi £ rn and -<X2 £ rn, contrary to the inseparability of tn, since in that case 
both (Tn, {JL}) and ({JL}, An) are not realizable. Thus x £ Tn implies 9DT |= x* 
To prove the converse suppose ffl f= x and x ^ Tn- Then -<(xi —> X2) £ Tn, from 

EXERCISES 
19 
which xi € and -1^2 € rn, for otherwise (rn, {-J-}) would be not realizable, 
contrary to the inseparability of tn. So, by the induction hypothesis, 9JI |= xi 
and 97t \/= X2> whence 97t ^ x> which is a contradiction. 
The other cases are considered analogously. We leave them to the reader. 
□ 
Local tabularity. Formulas ~p and ip are said to be equivalent in a logic 
L if *0 £ L. A logic L is called locally tabular (or locally finite) if, for 
every natural n > 0, L contains only a finite number of pairwise nonequivalent 
formulas built from variables q\,..., qn. 
Theorem 1.29 Cl is locally tabular. 
Proof With every formula p{qi,..., qn) we associate the n-ary Boolean 
function F<p which maps n-tuples of T and F to the set {T, F} in accordance with 
the truth-table for p(qi,..., qn). It is clear that the formulas p(qi,..., qn) and 
ip(qi, • • • > Qn) are equivalent in Cl iff Fp = F^. And since there are exactly 22 
distinct n-ary Boolean functions, the number of pairwise nonequivalent formulas 
of the variables q\,..., qn is also 22*1. □ 
Hallden completeness. A logic L is said to be Hallden complete if, for 
every formulas p and ip containing no common variables, pV ip € L iff p € L or 
ip € L. 
Theorem 1.30 Cl is Hallden complete. 
Proof Suppose p and ip have no variables in common, p $ Cl and ip ^ Cl. 
Then there are models 97ti and 9712 refuting p and ip, respectively. Define a 
model 971 by taking, for each variable p, p £ 971 iff either p £ Sub</? and p £ 97ti 
or p £ Sub ip and p £ 9712- By Proposition 1.2, we then have 971^^,971^^, 
whence 971 ^ p V ip and pV ip ^ Cl. 
The converse implication is trivial. □ 
Disjunction property. A logic L is said to have the disjunction property 
if, for every formulas p and ip, p V ip £ L iff p £ L or ip £ L. Since classical logic 
accepts the law of the excluded middle p V we obviously have 
Theorem 1.31 Cl does not have the disjunction property. 
1«5 Exercises 
Exercise 1.1 A formula p is said to be in disjunctive (conjunctive) normal 
form if p = ipi V ... V ipn (respectively, p = ip\ A ... A ipn) where n > 1 and 
each ipi is a conjunction (disjunction) of atoms or negations of atoms. Show that 
every formula can be effectively transformed to an equivalent (in Cl) formula 
which is in disjunctive (conjunctive) normal form. (Hint: use the equivalence 
(p —> q) <-> V q, de Morgan’s laws, the law of double negation, the laws of 
distributivity and the equivalent replacement theorem.) 

20 
CLASSICAL LOGIC 
Exercise 1.2 A formula <p(gi,..., gn) is m fuM disjunctive (conjunctive) 
normal form if it is either J_ (T) or a disjunctive (conjunctive) normal form whose 
every disjunct (conjunct) contains exactly one occurrence of each of the 
variables qi,... ,qn. Show that every formula can be effectively transformed to an 
equivalent (in Cl) formula which is in full disjunctive (conjunctive) normal form. 
(Hint: with each line in the truth-table for (p(qi,... ,gn), in which it has value 
T, associate the conjunction Xi A ... A Xn> where Xz = Qi If Qi Is true in the line 
and Xz = -'Qi otherwise, and take the disjunction of all these conjunctions.) 
Exercise 1.3 Show that each of the following sets {A,-i}, {V, —<}, {—>,_]_} is 
truth-functionally complete in the sense that every Boolean function (i.e., a 
function from {F, T}n to {F,T}) can be represented as F^, for some formula ip 
containing only connectives and constants in the set; in particular, every C-formula 
is equivalent in Cl to such a formula. 
Exercise 1.4 (Principle of duality) Let ip be a formula whose connectives 
are only A, V and -i. The dual of ip is the formula ip* which is obtained by 
replacing simultaneously every A, V, _L, T in ip with V, A, T, _L, respectively. 
Show that for all formulas ip and ip, ip(pu •.. ,pn) ”,<£*(”'PiJ • • •, ->pn) € Cl 
and that ip ^ ip e Cl iff </?*<-> ip* £ Cl. In particular, ip £ Cl iff -up* e Cl. 
Exercise 1.5 Let a = (ai,..., an) and b = (&i,..., bn) be n-tuples of F and T 
and let a* < bi iff ai = F or bi = T. Put a < b iff ai < bi for every i € (1,..., n}. 
A formula <p(pi,... ,pn) is called monotone if F^a < F^b whenever a <b. Show 
that every formula containing only the connectives A, V and the constants _L, T 
is monotone. 
Exercise 1.6 Show that every monotone formula is equivalent in Cl to a 
formula in the language with the connectives A, V and the constants _L and T. 
Exercise 1.7 Say that a formula ip(pi,... ,pn) is monotone relative to Pi if 
(q-*r) -» (</>(...,Pi-!,q,Pi+1,...) Pi-1,r,pi+i,...)) € Cl 
and antimonotone relative to Pi if 
(q r) Pi-1,r,pi+1,...) -np{...,Pi-i,q,Pi+i,...)) € Cl. 
Prove that (i) a formula is monotone iff it is monotone relative to its every 
variable; (ii) p —> q is monotone relative to q and antimonotone relative to 
p; (iii) every formula ip is monotone or antimonotone relative to each variable 
occurring at most once in ip. 
Exercise 1.8 A matrix for £ is a structure 21 = (A, A, V, —>, _L, D), where A is a 
non-empty set, D its non-empty subset, A, V, —> are binary operations on A and 
_L £ A. A valuation in 21 is a map 21 from Var£ to A. Considering the connectives 
as the corresponding operations on A, we can extend inductively 21 to a map 
from For£ to A. The pair DJI = (21,21) is an n^universal model for a logic L if 

NOTES 
21 
p 6 L iff %3(p) e D, for every formula p(pi,... ,pn)« For each n <u, construct a 
finite n-universal model for Cl. (Hint: take 21 = (A, A, V, —►, ||±||, {||T||}), where 
A consists of the sets 
MPl, • • • ? Pn) || = WPl, ■ • • ,Pn) * ^ *l> € Cl}, 
IMI © M = ||p © </>l|, for © £ {A, V, ->}, 
INI if 1 < * < n 
||±|| otherwise.) 
Exercise 1.9 Prove that, for every n > 1, one can axiomatize Cl in the language 
with the connectives —► and -• using n independent axioms and the rules Subst 
and MP. (Hint: for n = 1, take the axiom 
/? = ((((Po -»■ Pi) (~P2 -» ->P3)) -»■ P2) P4) ((P4 Po) -»■ (P3 -*■ Po)) 
and for n > 1, use the axioms 
oil 	= ->->(p-yp), 
c*i - ->2t(p -*p), 1 < i < n - 1, 
<*n = -’“’(P P) ->(••• -»• (-i2(n_1)(p -+p)-+(})...), 
where -«n is the string of n negations.) Is it possible to extend this result to the 
language used in this book? 
1.6 	Notes 
This chapter contains only those basic facts concerning classical logic that will be 
used in the sequel. We did not touch upon, for instance, Gentzen-style systems or 
Post’s theory of Boolean functions. A more comprehensive exposition of classical 
propositional logic can be found in other textbooks on mathematical logic, say 
in Church (1956), Kleene (1967), Mendelson (1984) or Takeuti (1975). 
There are several ways of proving the completeness theorem for CL We took 
that one which can be easily extended to other logics to be considered in the 
book. In fact, it goes back to Beth (1959), though the notion of semantic tableau 
we use here is somewhat different from the standard one, say that in Fitting 
(1983). Usually a semantic tableau is defined as a sort of derivation from a given 
pair t = (r, A) using inference rules like (SR1)-(SR6). This yields an alternative 
proof system for Cl. We apply essentially the same method but for constructing 
countermodels. All we need is just one disjoint saturated pair obtained from t 
with the help of those rules. Since we do not require tableaux to be finite, our 
completeness proof can be easily extended to the standard Henkin construction 
used for establishing completeness; cf. e.g. Chang and Keisler (1990). 
Cl is the simplest logic among those to be considered in this book. Some of 
its properties (e.g. Hallden completeness) are trivial and were presented only for 

22 
CLASSICAL LOGIC 
comparison with properties of non-classical logics. Although everything seemed 
to be known about Cl in the 1940s, from time to time new results continue to 
appear. Hodges (1983) claims that Craig’s (1957) interpolation theorem was the 
last important achievement. That Cl is structurally complete was also observed 
not so long ago; see Belnap et al (1963). Anisov (1982) showed that for any 
n > 1, Cl can be axiomatized by n independent axioms, with Subst and MP 
being the inference rules (see Exercise 1.9 the formula (3 in which was found by 
Meredith (1953)). Note also that if we do not use the rule of substitution (even 
in axioms) then there is a little hope to get an independent axiomatization, see 
Dale (1983). In this connection one more result deserves mentioning. Diamond 
and McKinsey (1947) constructed an algebra which is not Boolean itself but its 
all subalgebras generated by two elements are. It follows in particular that one 
cannot axiomatize Cl by axioms containing < 3 variables. 

2 
INTUITIONISTIC LOGIC 
From the set-theoretic point of view intuitionistic propositional logic is a subset 
of the classical one: it can be defined by the calculus which is obtained from Cl 
by discarding the law of the excluded middle (A10). It is Brouwer’s (1907, 1908) 
criticism of this law that intuitionistic logic stems from. However, the 
philosophical and mathematical justifications of these two logics are fundamentally 
different. 
2.1 	Motivation 
The law of the excluded middle allows proof of disjunctions ip V ip such that 
neither ip nor ip is provable. It is equivalent in Cl to the formula -•-•p —> p 
justifying proofs by reductio ad absurdum, which make it possible to prove the 
existence of an object (having some given properties) without showing a way 
of constructing it. Proofs of that sort are known as non-constructive. The aim 
of intuitionistic logic is to single out and describe the laws of “constructive” 
reasoning. 
The main principle of intuitionism asserts that the truth of a mathematical 
statement can be established only by producing a constructive proof of the 
statement. So the intended meaning of the intuitionistic logical connectives is defined 
in terms of proofs and constructions. The notions “proof’ and “construction” 
themselves are regarded as primary, and it is assumed that we understand what 
a proof of an atomic proposition is. 
• A proof of a proposition ip A ip consists of a proof of ip and a proof of ip. 
• A proof of ip V ip is given by presenting either a proof of ip or a proof of ip. 
• A proof of ip —> ip is a construction which, given a proof of ip, returns a 
proof of ip. 
• J_ has no proof and a proof of -vp is a construction which, given a proof of 
ip, would return a proof of J_. 
This interpretation, given by Brouwer, Kolmogorov3 (1932) and Heyting (1956), 
can hardly be reckoned as a precise semantic definition and used for constructing 
intuitionistic logic, as it was done for Cl. Nevertheless, it is not difficult to see 
that the first nine axioms of classical calculus Cl are entirely acceptable from 
the intuitionistic point of view, while the law of the excluded middle must be 
3Kolmogorov treated formulas as schemes of solving (or posing) problems; for example, 
—-► “0 means the problem: given any solution to the problem <p, find a solution to the problem 
ip. 

24 
INTUITIONISTIC LOGIC 
rejected (indeed, we cannot present now a proof of Goldbach’s conjecture or that 
P = NP, etc., nor are we able to show that these statements do not hold). 
Intuitionistic logic was first constructed in the form of calculus by Heyting 
(1930). This calculus (an equivalent one, to be more exact) is obtained from Cl 
by discarding axiom (A10). 
As to the interpretation above, it can be made more precise in various ways. 
Two of them—Kleene’s realizability interpretation and Medvedev’s finite 
problem interpretation—will be briefly discussed in Section 2.9. Another way, 
connected with the explicit introduction of a new provability operator, will be 
considered in Section 3.9 of Chapter 3 dealing with modal logic. 
More suitable for the practical use strict and philosophically significant 
definitions of semantics for intuitionistic logic were given by Beth (1956) and Kripke 
(1965a) (see also Grzegorczyk, 1964). Their semantics does not exploit the 
notions of proof and construction; instead, it explicitly expresses an epistemic 
feature of intuitionistic logic. We will give now some informal motivation of the 
Kripke semantics; the corresponding formal definitions will be introduced in the 
next section. 
By accepting the fundamental semantic assumption of classical logic—each 
proposition is either true or false—we completely abstract from the fact that 
actually it may be a priori unknown whether this or that proposition is true 
or false. We do not know now, for instance, if Goldbach’s conjecture is true, if 
the equality P = NP holds, whether there are rational beings in the Archer 
constellation, and so forth. But it is quite possible that we can know about this 
in the future, acquiring new information on mathematics and the world around 
us. 
It is this epistemic aspect of the notion of truth that intuitionistic logic, as 
opposed to the classical one, takes into account. 
Let us imagine that our knowledge is developing discretely, nondeterministi- 
cally passing from one state to another. When at some state of knowledge (or 
information) x, we can say which facts are known at x and which are not 
established yet. Besides, we know what states of information y are possible in the 
future. Of course, this does not mean that we shall necessarily reach all these 
possible states (for instance, we can imagine now not only a course of events 
under which Goldbach’s conjecture will be proved, but also such a situation when 
it will remain unproved or will be refuted). It is reasonable also to assume that 
while passing to a new state y all the facts known at x will be preserved, and 
some new facts will possibly be established. 
It is natural to regard an atomic proposition, established at a state x, to be 
true at x; it will remain true at all further possible states. A proposition which 
is not true at x cannot be in general regarded as false, for it may become true 
at one of the subsequent states. 
The truth of compound propositions can be defined now as follows. 
• Aip is true at a state x if both and ^ are true at x. 
• ip V ^ is true at x if either (p or ip is true at x. 

KRIPKE FRAMES AND MODELS 
25 
• p ip is true at a state x if, for every subsequent possible state y, in 
particular x itself, p is true at y only if ip is true at y. 
• J_ is true nowhere. 
It follows from this definition that the negation ->p = p —► J_ is true at x if p 
is true at no subsequent possible state. A proposition p may be regarded to be 
false at x if ~^p is true at x. 
All axioms (Al)-(A9) (under every substitution of concrete propositions 
instead of variables) turn out to be true at all conceivable states, which cannot be 
said about (A10), i.e., po V (po -J-). Indeed, if a proposition p is not true at a 
state x, but becomes true at a subsequent state y, then -\p is not true at x and 
so neither is p V ~^p. 
2.2 	Kripke frames and models 
As in Section 1.1, let us fix the propositional language C with the connectives A, 
V, —► and the constant J_. Starting from the informal interpretation above, we 
give now a precise definition of an intuitionistic model for C. 
An intuitionistic Kripke frame is a pair # = (W, R) consisting of a 
nonempty set W and a partial order R on W, i.e., # is just a partially ordered set. 
We remind the reader that a binary relation R on W is called a partial order if 
the following three conditions4 are satisfied for all x,y,z £ W: 
xRx (reflexivity), 
xRy A yRz —► xRz (transitivity), 
xRy A yRx —► x = y (antisymmetry). 
The elements of W are called the points of the frame # and xRy is read as “y is 
accessible from x” or “x sees y”. 
A valuation of C in an intuitionistic frame # = (W, R) is a map 93 associating 
with each variable p £ Var£ some (possibly empty) subset 93(p) C W such that, 
for every x £ 2J(p) and y £ W, xRy implies y £ 2J(p). Subsets of W satisfying 
this condition are called upward closed. The set of all upward closed subsets of 
W will be denoted by UpW. Thus, a valuation in $ is a map 2J from Var£ into 
UpW. 
An intuitionistic Kripke model of the language £ is a pair 9Jt = (#, 2J) where 
5 is an intuitionistic frame and 2J a valuation in 5. 
In the terminology of the preceding section points in a frame # = (W,R) of 
a model 971 = (#, 93) represent states of information; if we are now at a state x 
then in the sequel we may reach a state y such that xRy. An atomic proposition 
p is regarded to be true at x if x £ 93(p). Since 93(p) is upward closed, all atomic 
propositions that are true at x remain true at all subsequent possible states. 
4Here and below, to represent various properties of frames we use the language of classical 
predicate logic with the predicates R and =. 

26 
INTUITIONISTIC LOGIC 
Let 971 = (#, 27) be an intuitionistic Kripke model and x a point in the frame 
# = (W, i^). By induction on the construction of a formula p we define a relation 
(971, a;) |= p, which is read as up is true at a; in 971”: 
(an,*) 
b p 
iff 
x € 2J(p); 
(an, as) 
b Mx 
iff 
(®T, x) b tp and (®T, x) \= x; 
(an, a:) 
T 
■e* 
< 
iff 
{m,x) b ^ or (9Jt,x) f= x; 
(m,x) 
b ^ -»• x 
iff 
for all y £ W such that xRy, 
(9JI, y)\=rj) implies (9Jt, y) |= x; 
(m,x) 
b-L- 
It follows from this definition that 
(971, a:) f= -»V> iff for all y £ W such that xRy, (971, y) ^ ifr. 
If 971 is understood we write x f= p instead of (971, x) f= p. The truth-set of p in 
971 = (#, 27), i.e., the set {x : x f= p}, will be denoted by 27(</?). 
Notice that an intuitionistic model 971 = (#, 27) on the frame # containing 
only a single point, say a;, is in essence the same as the classical model 
9t = {p £ VarC : x £ 27(p)}, 
because (971, x) |= p iff 9t |= p, for every formula p. 
Proposition 2.1 For every intuitionistic Kripke model on a frame # = (W, R), 
every formula p and all points x, y £ W, ifxj=p and xRy then y [= p. 
Proof An easy induction on the construction of p is left to the reader as an 
exercise. □ 
In other words, Proposition 2.1 states that the set of points where p is true 
is upward closed. On the contrary, the set of points at which p is not true may 
be called downward closed, since x)/= p and yRx imply y p. 
We say a formula p is satisfied in a model 971 = (#, 27) if x \= p for some point 
x in #. p is true in 971 if x \= p for every x in #; in this case we write 971 f= p. If 
p is not true in 971 then we say that p is refuted in 97t or 97t is a countermodel 
for </?, and write 971 ^ p. 
A formula p is satisfied in a frame # if p is satisfied in some model based on 
#. p is true at a point x in # (notation: (#, x) f= p) if p is true at x in every 
model based on #. p is called valid in a frame #, # |= p in symbols, if p is true in 
all models based on #. Otherwise we say that p is refuted in # and write # p. 
If every formula in a set T is true at a point x in a model 971, we write 
(971, x) |= T or simply x f= T. 971 f= T and # f= T mean that all formulas in T are 
true in 971 and are valid in #, respectively. 
Frames # = (W, R) and 0 = (V, S) are said to be isomorphic if there is a 1-1 
map / from W onto V such that xRy iff f(x)Sf(y), for all x,y eW. The map / 
is called then an isomorphism of # onto 0. Models 971 = (#,27) and 91 = (0,11) 

KRIPKE FRAMES AND MODELS 
27 
are isomorphic if there is an isomorphism / of # onto 0 such that, for every 
p e Var£, il(p) = /(93(p)), i.e., for every x € W, 
(971, z) [= p iff (91, f(x)) \= p. 
In this case we say that / is an isomorphism of 9Jt onto 91. 
The following two propositions are direct consequences of the given 
definitions. 
Proposition 2.2 If f is an isomorphism of a model 9Jt onto a model 91 then, 
for every point x in 9Jt and every formula <p, 
This gives us the ground not to distinguish between isomorphic models as 
well as isomorphic frames. 
Proposition 2.3 Suppose 9Jt = (#,93) and 91 = (#,il) are models on a frame # 
such that the valuations 93 and il coincide on the variables in some set Var C 
Var£. Then for every point x in $ and every formula (p with Var<p C Var, 
Thus, if we want to construct a countermodel for a formula <p on a frame 
#, it suffices to define a valuation 93, refuting <p, only on the variables in <p; the 
values of 93 on other variables have no effect on the truth of <p at points in #. 
We shall often represent intuitionistic frames in the form of diagrams by 
depicting points as circles o and drawing an arrow from x to y if xRy. To avoid 
awkwardness, we will not draw those arrows that can be uniquely reconstructed 
by the properties of reflexivity and transitivity. For technical reasons it is 
sometimes impossible to connect x and y with an arrow; we then connect them with 
a (broken) line, and the fact that xRy is reflected by placing y higher than x. 
When representing models, we shall sometimes write some formulas near points: 
on the left side of a point x we write those formulas that are true at x and those 
that are not true are written on the right. 
Example 2.4 Suppose # = (W, R) is the frame in which W = {a, &}, R = 
{(a,a), (a, b), (6, b)} and let 93(p) = {b} and 93(g) = {a, b} for all q € Var£ 
different from p. Then the formula p V (p —» _L) is true at b and not true at a in 
the model 9Jl = (#, 93). This situation is represented graphically in Fig. 2.1. Thus, 
P v (p —» -L) is satisfied as well as refuted in #. The formula ((p —* ±) —» _L) —» p 
is also refuted in 931, since a |= (p —> _L) —> _L and a p. 
Example 2.5 The formula p —» ((p —> _L) —» _L) is valid in all intuitionistic 
frames. Indeed, suppose otherwise. Then there is a model on a frame # = (W, R) 
such that x |= p and x ^ (p —> _L) —> ± for some x e W, and so there is y e W 
for which xRy and y |= p —> ±. By the definition of valuation, we must have 
V |= p, whence y ft p —» ±, which is a contradiction. 

28 
INTUITIONISTIC LOGIC 
b 
p p —► ± 
pv(p->l) 
V 
4 
flpVfp-^l) 
Fig. 2.1. 
We define intuitionistic propositional logic Int^ in the language C as the set 
of all /^-formulas that are valid in all intuitionistic frames, i.e., 
Int£ = {<p G ForC : S |= (p for all frames S'}. 
Usually we will drop the subscript C and write simply Int. 
Since the classical validity is nothing else but the validity in the single-point 
intuitionistic frame, we obtain the inclusion 
Int C Cl. 
And since p V ~^p is in Cl but does not belong to Int, this inclusion is proper. 
2.3 	Truth-preserving operations 
In comparison with classical models intuitionistic ones are much more complex 
structures. So before proceeding to the study of Int let us develop some notions 
and technical means for handling them. In this section we introduce three very 
important operations on intuitionistic models and frames which preserve truth 
and validity. 
A frame 0 = (V, S) is called a subframe of a frame S = (W, R) (notation: 
0 C S) if V C W and S is the restriction of R to V (S = R \ V, in symbols), i.e., 
S = Rf) V2. The subframe 0 is a generated subframe of # (notation: 0 C 5) if 
V is an upward closed subset of W. 
Example 2.6 Let $ be the frame depicted in Fig. 2.2 (a). Then the frames 
shown in Fig. 2.2 (a)-(g) are (isomorphic to) subframes of #, with (a), (d), (e) 
and (f) being the only pairwise non-isomorphic generated subframes. 
If 0 = (V, S) is a generated subframe of S' = (W,R) and V is the upward 
closure of some set X C W, i.e., V is the minimal upward closed subset of W to 
contain X, then we say that V and 0 are generated by the set X. Notice that 
since R is reflexive and transitive, 
V = {x e W : 3y e X yRx}. 
If S is generated by a singleton {#} then S is called rooted and x is called the root 
(or the least point) of S- All frames in Fig. 2.2, except (d) and (g), are rooted. 

TRUTH-PRESERVING OPERATIONS 
29 
We introduce special notations for the operations of upward and downward 
closure. Namely, if # = (W,R) is a frame and X C W then we let 
R = {xeW:3yeX yRx}, 
X[R = {xeW:3yeX xRy}. 
If # is understood then we drop R and write simply X| and X[; we also write x\ 
and x[ instead of {x}T and {x}|, respectively. All the points in x| (x|) are called 
successors (predecessors) of x\ a successor (predecessor) y of x is proper if x b y. 
A proper successor (predecessor) y of x is an immediate successor (respectively, 
immediate predecessor) of x if xRzRy (yRzRx) implies z = x ox z = y, for every 
z £ W. A point a; is a final (or maximal) point in # if x] = {x}; x is the last (or 
greatest) point in # if x[ = W. More generally, a point x £ X C W is called final 
(or maximal) in X if no proper successor of x is in X. 
Thus, 0 = (V,S) is a subframe of # = (W, JR) generated by a set X if 
V = X|R and S = RnV2-, x is the root of 0 if V = x]S. Using arrows, instead 
of xRy we can write now either y £ x| or x £ y[. 
A model Dl = (0,11) is a submodel of a model DJI = (#, 2J) (notation: Dl C DJI) 
if 0 = (V, S) is a subframe of # = (W, jR) and, for every p £ Var£, 
ii(p) = D3(p) H V. 
In the case when 0 C # the model 91 is called a generated submodel of DJI 
(notation: Dl C DJI). 
The formation of generated submodels is the first truth-preserving operation 
of the three mentioned above. 
Theorem 2.7. (Generation) Suppose Dl = (0,11) is a generated submodel of 
DJI = (#, 2J). Then for every formula <p and every point x in 0, 
(% x) \=(p iff (DJI, x) (=</?. 
Proof The proof proceeds by induction on the construction of ip. The basis of 
induction is obvious. Let = -0 —> # = (W, R) and 0 = (V, S). Then we have: 
(Dl,x) b if iff Vy e xT5 ((91, y) b ^ - (91, y) b X) 
iff Vy 6 xJR ((DJl,y) b </> - (0K,y) b X) 
iff (DJI, x) b <£• 

30 
INTUITIONISTIC LOGIC 
Here the second equivalence is justified by the induction hypothesis and the fact 
that x]S = x]R, for every point x E V. 
The cases p = ^ A \ and P = ^ V X are trivial. □ 
The generation theorem means that the truth-values of formulas at a point 
x are completely determined by the truth-values of their variables at the points 
in xt and do not depend on other points in the model. 
Corollary 2.8 If 0 G # then, for every formula p, 
(i) (0, x)\= p iff (#, x) |= p, for all points x in 0; 
(ii) £ |—p implies 0 |= p. 
Proof (i) Suppose (0,x) ^ p■ Then (91,x) ^ p for some model 9T = (0,il). 
Define a valuation 2J on # by taking 
2J(p) = il(p) for all p € Var£. 
Then 91G 9Jt = (#,03) and so, by the generation theorem, (97t, x) ^ p. 
Therefore, (#, x) |= p implies (0,x) |= p. The converse implication is a direct 
consequence of the generation theorem. 
(ii) follows from (i). □ 
We draw two more simple consequences of the generation theorem. 
Corollary 2.9 For every frame # and every formula p, the following conditions 
are equivalent: 
(i) £ b v; 
(ii) 0 |= p, for every 0 G 
(iii) 0 |= p, for every rooted 0 G 
Corollary 2.10 Int£ = {p € For £ : # |= p for all rooted frames #}. 
Our second truth-preserving operation is defined in a slightly more 
complicated way. 
Suppose we have two frames $ = {W, R) and 0 = (V, 5). A map / from W 
onto V is called a reduction of$ to 0 if the following conditions hold for every 
x, y E W: 
(Rl) xRy implies f(x)Sf(y); 
(R2) f(x)Sf(y) implies 3 z eW (xRz A f(z) = /(y)). 
In this case we say also that / reduces # to 0 or 0 is an f-reduct (or simply a 
reduct) of # or # is f-reducible (or simply reducible) to 0. Such a map / is often 
called a pseudo-epimorphism or just a p-morphism as well. 
Proposition 2.11 A one-to-one reduction of$ to 0 is an isomorphism between 
$ and 0. 
Proof Exercise. 
□ 

TRUTH-PRESERVING OPERATIONS 
31 
Fig. 2.3. 
Example 2.12 The frame in Fig. 2.3 (a) is reducible to all frames (a)-(f), but 
not to (g). 
Proposition 2.13 Let f be a reduction of'S = (W,R) to (5 = (V,5), X £ UpW 
and Y £ UpV\ Then f(X) £ UpV and f~l{Y) £ UpW. 
Proof Suppose that f{x)Sy for some x £ X and y £ V. Then, by (R2), there 
is z £ x] such that f(z) = y. Since X is upward closed, z £ X and so ye f(X). 
Hence f{X) £ UpV. 
Now let xRy, for some x £ f~1(Y) and y £ W. Then, by (Rl), f(x)Sf(y), 
whence f(y) £ Y and y £ f~1(Y). So f~1(Y) £ UpW. □ 
Proposition 2.14 If f is a reduction of $ to <& and g a reduction of 0 to 9) 
then the composition gf is a reduction of $ to $). 
Proof Exercise. □ 
A reduction / of ^ to (5 is called a reduction of a model 931 = (#, 03) to a 
model 01 = if, for every p £ Var£, 
Q3(p) = r\!d(p)), 
i.e., if for every point x in #, 
(vn,x) b p iff (91, /(*)) b p■ 
Theorem 2.15. (Reduction) If f is a reduction of a model 931 = (#, 03) to a 
model 01 = (®,il) then, for every point x in $ and every formula p, 
(m,x)^<piff(%f(x))^<p. 
Proof We conduct the proof by induction on the construction of ip. The basis 
of induction is trivial. Let ip — -0 —» x- 
If (971, x) ^ ip then there is a point y £ x | such that (931,2/) 1= ^ and 
(931, y) ^ x• By the induction hypothesis, (01,/(y)) |= xjj and (01, f(y)) ^ x> and 
by (Rl), f(x)Sf(y). Therefore, (01 ,f(x)) ^ ip. 
Conversely, suppose (01, f{x)) ^ ip, i.e., there is a point u £ f(x)j such that 
(01,u) |= \t> and (01,u) ^ x- Since / is a map “onto”, there is y £ /-1(u). Then 
f(x)Sf(y). By (R2), there is z £ x\ such that f(z) — /(y) = u. By the induction 
hypothesis, (931, z) [= ip and (931, z) ^ x> whence (931, x) ip. 

32 
INTUITIONISTIC LOGIC 
Fig. 2.4. 
The cases <p = ip A x and = present no difficulties. □ 
Corollary 2.16 Let f be a reduction of$ to 0. Then, for every formula p and 
every point x in 
(£,#) |= p implies (0,/(x)) |= p. 
Proof Assuming otherwise, we have a model 01 = (0,H) in which f(x) \/= p. 
Construct a model 9Jt = (#,93) by taking, for all p e Var£, 
®Cp) = /-'(itCp))- 
By the reduction theorem, we must then have (SDt, x) which is a 
contradiction. □ 
Corollary 2.17 //# is reducible to 0 then, for every formula <p, 
# p implies 0 |= p. 
As an example of the use of the reduction theorem we will show that every 
formula p £ Int is refuted in a frame having the tree form. 
Say that a frame # = (W,R) is a tree if 
• # is rooted and 
• for every point x e W, the set x[ is finite and linearly ordered by R. 
We remind the reader that a set X of points in a frame # = (W,R) is linearly 
ordered by R if xRy or yRx, for every distinct x, y € X. In such a case X is also 
called a chain in #. In particular, a sequence xi,X2,... of (distinct) points in # 
is a (strictly) ascending chain if X1RX2R... and a (strictly) descending chain if 
... RX2RX1. 
Example 2.18 The frames shown in Fig. 2.4 (a), (b) are trees (the latter one 
is an infinite ascending chain), while those in Fig. 2.4 (c), (d) are not trees (the 
latter one is an infinite descending chain). 
Theorem 2.19 Every rooted frame 0 = (V, S) is a reduct of some tree # = 
(W, R)} which is finite if 0 is finite. 

TRUTH-PRESERVING OPERATIONS 
33 
^3 
vx 
V2 
Vo 
0 
(VOjVuVs) (vo,v2,v3) 
(v0,V3) 
Fig. 2.5. 
Proof Suppose Vo is the root of 0. Define W as the set of all finite strictly 
ascending chains of the form (vo, Vi,..., vn-i,vn) in 0 and put 
(vo,..., vn) R (uo, • • •, um) iff n < ra and for i = 0,..., n. 
Clearly R is a partial order on W. (See Fig. 2.5.) 
We show first that # = (W, R) is a tree. Indeed, (vo) is the root of # and the 
set (vo,i;i, • • • ,vn-i,vn)l is the finite chain 
(v0) R (v0, vi)R...R (v0, vu • • •, vn-i) R (vo, vi,. -., vn-i,vn). 
Now we define a map / from W onto V by taking f((vo,...,vn)) = vn. 
Let x,y G W and xRy. Then, by the definition of R, x = (vo, ...,vn), y = 
(v0, • • •, Vn, vn+i,..., vm) and so vnSvn+iS... Svm-iSvm, whence, by the 
transitivity of 5, vnSvm, i.e., f(x)Sf(y). Therefore, / satisfies (Rl). 
Let /(a;) = (i.e., a; = (v0,..., vn)), f(y) = vm and vnSvm. If then 
obviously xRx and f(x) = f(y). Otherwise, for z = (i;q, ..., vn, vm), we have 
xRz and f(z) = vm. Thus / satisfies (R2) and so is a reduction of the tree # to 
0. 	□ 
Corollary 2.20 Int = {<p e ForC : # |= tp for every tree #}. 
A tree # is said to be n-ary, for n > 1, if every non-final point in # has exactly 
n immediate successors. If, for some m < a;, every strictly ascending chain in 
a finite n-ary tree # can be extended to a strictly ascending chain of length m 
then we say # is the full n-ary tree of depth ra. And if an n-ary tree has no final 
points at all then it is called the full n-ary tree. It is clear that, for each n > 1, 
there is only one full n-ary tree (modulo isomorphism, of course); we denote it 
by Xn. Every rooted generated subtree of Xn is isomorphic to Tn, i.e., is again 
the full n-ary tree. 
Theorem 2.21 Every finite tree # = (W,R) is a reduct of%n, for each n > 2. 

34 
INTUITIONISTIC LOGIC 
Fig. 2.6. 
Proof We proceed by induction on the number of points in #. If S is a singleton 
then the map of Xn to S is clearly a reduction. 
Suppose now that S contains k + 1 points, v is the root of S and vq,. .. ,vm 
are all its distinct immediate successors. Denote by Si = (Wi,Ri) the subtree of 
S generated by u*, for i = 0,..., m. 
Let us represent Tn as is shown in Fig. 2.6. Here X^, i = 1,2,..., are disjoint 
isomorphic copies of Xn. By the induction hypothesis, for each i > 1, there is a 
reduction /* of X^ to 3modm+i(i)- Define a map / from Xn onto S by taking, for 
every point x in Xn, 
v _ f v if x = Xi, for i > 0 
HX) ~ \ fi(x) if x is a point in X^. 
It should be clear that / is a reduction of Xn to #. □ 
Corollary 2.22 Every finite rooted frame is a reduct of%n, for each n > 2. 
Proof Follows from Proposition 2.14 and Theorems 2.19 and 2.21. □ 
Our third truth-preserving operation is the disjoint union of frames. 
Let {Si = (Wi,Ri) : i € 1} be a family of frames such that W* D Wj = 0, for 
all i 7^ j. The disjoint union of the family (fo : i € 1} is the frame Si = 
(Ui€/Wi,U i£IRi). If the set I is finite, say I = {l,...,n}, then along with 
Si we write also Si 4-... -f Sn- We obtain a diagram of Si by drawing 
side by side the diagrams of all frames Si, for i e /, and regarding them as one 
big diagram. It is clear that every Si is a generated subframe of ^2ieISi- 
The disjoint union of the family of models (SUt* = (fo,®*) : i € 1} with 
pairwise disjoint frames is the model where 
(J2i£i^i){p) = f°r every p € VarC. Obviously, each model SUt* 
is a generated submodel of Yhiei SDTi- 
Theorem 2.23. (Disjoint union) Let^2iej^i be the disjoint union of a 
family {9K* : i G /}. Then for every i e I, every point x in -EUli and every formula 
V, 
(£ JWi,s) H ¥>#(!*«<,a) 
iei 

HINTIKKA SYSTEMS 
35 
Proof Follows from the generation theorem. □ 
Corollary 2.24 Let &e ^e disjoint union of a family {& : i € I}. 
Then, for every formula p, fo b iffBi h for aM i € I- 
The following proposition is left to the reader as an exercise. 
Proposition 2.25 Every frame is a reduct of the disjoint union of some family 
of rooted frames. 
We use the reduction and disjoint union theorems to show that, as in Cl, 
there are only two non-equivalent variable free formulas in Int. 
Proposition 2.26 For every variable free formula p, either p T e Int or 
p ± E Int. 
Proof If p € Int then clearly p T e Int. We show that if p & Int then 
p _L e Int. Since _L —> p e Int, it suffices to prove that ->p is in Int. Suppose 
otherwise. Then we have two models 9Jti and 9Jl2 refuting p and -></?, respectively. 
Since p is variable free, by Proposition 2.3 we may assume that no variable is 
true at any point in or 9JI2. The single-point model refuting all variables 
is then a reduct of 97ti -f 97t2, and therefore p and VI which is a 
contradiction. □ 
Corollary 2.27 For every variable free formula p, p £ Int iff p e Cl. 
Proof (=>) is trivial. Suppose p € Cl. By Proposition 2.26, either p T e Int 
or p _L e Int. In the former case p e Int. And the latter means that -*p £ Int 
and so ~^p £ Cl, contrary to the consistency of Cl. □ 
Corollary 2.28 Int is not O-reducible. 
Proof Take any formula p € Cl — Int. Then every variable free substitution 
instance of p is in Cl and so in Int. □ 
2.4 	Hintikka systems 
We have defined both classical and intuitionistic logics as sets of formulas which 
are valid in some frames. The fundamental difference between these two 
definitions is, however, that Cl is the set of formulas which are valid in a single finite 
frame, while Int contains formulas that are valid in all frames, including infinite 
ones. In other words, to answer the question “p € Cl?”, it suffices to fulfill a 
finite number of computations, whereas for a positive solution to the problem 
up £ Int?” we must produce a proof of the validity of p in all frames. 
In this section we will develop an apparatus of semantic tableaux for 
intuitionistic logic and show that for every formula p Int one can construct a 
countermodel containing at most 2'Sut><pl points. (Here and below \X\ denotes 
the cardinality of the set X.) Thus, the validity of p in all frames is completely 
determined by its validity in the frames of cardinality < 2lSubv5L 
Let us again begin with examples. /* 

36 
INTUITIONISTIC LOGIC 
to 
(p->q)V(q-> p) 
q 
P 
p\q 
to 
(b) 
(a) 
Fig. 2.7. 
Example 2.29 Suppose that we want to determine whether the formula 
known as the Dummett formula (or axiom), is in Int. To this end let us try to 
construct a countermodel for it using the same idea as was exploited in Section 1.2 
for finding countermodels in Cl. 
First we form a tableau to by putting da in its right part, indicating thereby 
that we wish this formula to be not true at the point to in the model to be 
constructed. Since a disjunction is not true at a point x iff both of its disjuncts 
are not true at x, we must put in the right part of to two more formulas: p —* q 
and q —* p. An implication is not true at x iff there is a point y accessible 
from x, where the premise of the implication is true and the conclusion is not 
(in particular y may coincide with x). So we form two new tableaux t\ and t<i 
accessible from to: ti contains p in the left part, q in the right and t^, conversely, 
p in the right part and q in the left. (See Fig. 2.7 (a).) 
Now we construct a frame # = (W,R) and a model 9Jt = (#, 2J) on it in 
accordance with our system of tableaux, i.e., by taking 
(The diagram of # is depicted in Fig. 2.7 (b).) Then we shall have: t\ |= p,t\ ^ q 
and so to p —» q\ t<i |= q, t<i p and so to \/= q —» P- Hence (SDt, to) da. 
Example 2.30 Let us consider now the formula m 
As before, we form a tableau to by putting this formula in its right column. Then 
both p2 and p2 —► pi V ->pi must also be put in the same column. To make the 
da = (p —* q) V (q p), 
W - {to,ti,t2}, 
R = {(to,ti) ,(to,t2) : i = 0,1,2}, 
®(P) = {*i}, ®(9) = {*2>- 
P2V(P2 -»Pl Vipi). 

HINTIKKA SYSTEMS 
37 
£o 
P2 V (P2 Pi V -ipi) 
P2 
P2 -► Pi V ipi 
(a) (b) 
Fig. 2.8. 
latter formula not true at £o> we form a new tableau t\ accessible from to, which 
contains P2 in the left part and p\ V ->pi, and hence pi and —in the right. Now 
to ensure that ->pi is not true at ti, we again form a new tableau t2 accessible 
from ti where p\ is true, i.e., stands in the left column. We should not forget 
either that all the formulas which are true at t\ must be true at t2 as well; so we 
put P2 in the left part of t2. (See Fig. 2.8 (a).) 
Now we construct a frame # = (W, R) and a valuation 53 in it by taking 
tl 
J* 0 
P2 
Pi v -ipi 
^ Pi 
Pi 
P2 
6 
->P1 
W = {to,ti,t2}, 
R={{ti,tj): z, j = 0,1,2 and i < j}, 
®(Pi) = {*2}, W{p2) = {tiM}- 
(The diagram of # is shown in Fig. 2.8 (b).) The reader can readily check that 
all formulas in the left part of the tableau U are true at the point ti in the model 
DJI = (#,93), while those in the right part are not true. Therefore, (9Jt,£o) 
P2 V (p2 -► Pi V -npi). 
Our next aim is to show that the refutation procedure described above always 
succeeds: after a finite number of steps we shall either construct a counter model 
for a given formula <p or establish its irrefutability, i.e., that p € Int. 
As before, a tableau is a pair t = (T, A) with T, A C For£. A tableau t is 
called saturated in Int if it satisfies the conditions (S1)-(S5) in Section 1.2. Thus, 
every tableau which is saturated in Cl is saturated in Int as well; the converse 
does not hold, as follows from the examples above. A saturated tableau (T, A) 
is disjoint if T fl A = 0 and JL ^ T. 
A Hintikka system in Int is a pair 9) = (T, S) consisting of a non-empty set 
T of disjoint saturated tableaux and a partial order 5 on T and satisfying the 
following conditions: 
(HS/1) if t = (r, A), t' = (r', A') are in T and tSt' then T C T'; 
(HS/2) if t = (T, A) is in T and x/j —> \ € A then there is t' = (T', A') in 
T such that tSt', x/j e T' and x € A'. 
We say 9) = (T, 5) is a Hintikka system for a tableau t if t C tf for some tf eT. A 
tableau t = (T, A) is called realizable in Int if there are an intuitionistic model 
and a point x in such that * 

38 
INTUITIONISTIC LOGIC 
(9DT, x) 1= ip for every ip G T and (9DT, x) x f°r every \ € A. 
Proposition 2.31 A tableau t is realizable in Int iff there is a Hintikka system 
So fort. 
Proof (=>) Suppose that £ is realizable in a model 971 based on a frame # = 
(W,R). With each x G W we associate the tableau tx = (rx, Ax), where 
rx = {p e ForC : a; |= <p}, Ax = {p e ForC : x ^ 
and define a partial order 5 on the set T = {tx : x G W} by taking 
txSty iff xRy. 
It follows immediately from the definition of intuitionistic model and 
Proposition 2.1 that So = (T, S) is a Hintikka system. Besides, t C tx for some x G W. 
(«<=) Let So = (T,S) be a Hintikka system for t. We will regard So as an 
intuitionistic frame. Define a model 97t = (So, 93) on it by taking, for every variable 
P, 
9J(p) = {u = (r, A) : u G T and p G T}. 
(HS/1) ensures that 9J(p) G UpT. By induction on the construction of p we show 
that for any tableau u = (r, A) in T 
p eT implies (3Jt,u) |= p, 
p e A implies (971,-u) ^ <p. 
The basis of induction is obvious and the formulas p = ip Ax and p = ip V x 
are considered in the same way as in Cl. So let p = ip —> x* 
Suppose G T but u ^ p. Then there is a point v = (n, E) in T such that 
wSv, v \= ip and v x- By (HS/1), y? G n and by (S5), either x € n or ip e E. 
Then, by the induction hypothesis, we must have either v |= x or v 1^ which 
is a contradiction. Hence u |= p. 
Now suppose that p e A. Then, by (HS/2), there is a tableau v = (n, E) 
such that 'uSu, ip G n and x £ E. Using the induction hypothesis, we obtain 
u |= ip and v x> whence u ^ ip —> x« □ 
As follows from Proposition 2.31, ^ Int iff there exists an (infinite, in 
general) Hintikka system for the tableau t = (0, {</?}). However, in fact we can 
obtain a much stronger result if observe that when constructing in the proof of 
Proposition 2.31 a Hintikka system for £, we may deal only with subformulas of 
p. The number of distinct tableaux, corresponding to points in #, will then be 
finite, will not exceed 2lSub(/?l to be more exact, and an accessibility relation on 
the tableaux can always be defined in such a way that the conditions (HS/1) and 
(HS/2) are satisfied. 
More generally, we have the following 

HINTIKKA SYSTEMS 
39 
Theorem 2.32 A tableau t is realizable in Int iff there is a Hintikka system 
= (T, S) for t such that |T| < 2^, where E is the set of all subformulas of the 
formulas in t. 
Proof (=>) We will modify the “only if’ part of the proof of Proposition 2.31 
according to the idea above. This time we associate with every point x G W the 
tableau tx = (1^, A*) in which 
Fx = {p £ £ : x |= <p}, Ax = {p G E : x p}. 
Putting T = {tx : x G W}, we clearly have \T\ < 2^. Define a relation 5 on T 
by taking, for tableaux tx = (T^, A^) and ty = (Ty, Ay), 
txSty iff Tx C Ty. 
To show that fj = (T, S) is a Hintikka system for £, it suffices to verify only 
(HS/2). Let tx = (r^, A^ be a tableau in T and ^ —> x £ Then x ^ —> x 
and so there is a point p such that xRy, ^ G ry and x € Ay. By Proposition 2.1, 
Q r^, and hence txSty. 
The proof of (<£=) remains the same as in Proposition 2.31. □ 
Corollary 2.33 (i) For every formula p ^ Int there is a rooted frame refuting 
p and containing at most 2l^ub(^ points. 
(ii) For every p Int there is a finite tree refuting p. 
(iii) For every n>2, Int = {<p G For £ : Xn \= p}. 
Proof Follows from Theorems 2.32, 2.19 and Corollaries 2.9, 2.17, 2.22. □ 
Example 2.34 We show that 
-ip <-» -i-i-ip G Int. 
Suppose otherwise. Then, in view of -ip —> —i—•—«p G Int (see Example 2.5), there 
is a finite model Wl = (#, 23) and a point x in # such that x |= —*p and x ->p. 
Take a point y G x[ where y |= —i—»—«p and p |= p. Since $ is finite, there is a final 
point 2 G p|- Clearly, 2 |= —ip and 2 |= p. But then z «p and, since is 
final, 2; |= —ip, whence 2 p, which is a contradiction. 
Theorem 2.32 means in particular that starting with the tableau (0, {p}) and 
using saturation rules (SRl)-(SR5) in Section 1.2 and 
(SR76) if t = (r, A) and xjj —> x £ A then either add $ to P and x to A' 
in some t' = (P, A') accessible from £ or construct a new tableau 
tf = (r', A') accessible from t by taking P = T U {?/>}, A' = {x}, 
in a finite number of steps we shall either construct a Hintikka system for (0, {<p}), 
and so a counter model for <p, or show that there is no Hintikka system for (0, {p}) 
with < 2lSub(/?l tableaux, and so no Hintikka system for the tableau at all, i.e., 
p G Int. 

40 
INTUITIONISTIC LOGIC 
We will not formulate here a procedure of constructing countermodels for 
intuitionistic formulas in full details. It will be more useful for the reader who is 
not experienced in intuitionistic logic to have a good informative example. 
Example 2.35 Let us try to find a countermodel for the formula 
sa = ((_i_ip —> p) —> V V ~*p) —5► ""■p V _i_ip, 
which is known as the Scott formula (or axiom). 
The attempt of constructing a Hintikka system for (0, {sa}) shown in Fig. 2.9 
(a) failed. However, applying (SR5) to (—*—*p -* p) -* p\/ -*p in the left column 
of to, we may not only put p V on the left, but also -i-i p —► p on the right. 
And this alternative way succeeds, as is shown in Fig. 2.9 (b). 
Taking now the frame $ = (W,R) depicted in Fig. 2.9 (c) and defining a 
valuation 93 in it by 93(p) = $2» we, according to Proposition 2.31, obtain the 
countermodel 971 = (#, 93) for the Scott formula. 
As an easy exercise we invite the reader to show that all the formulas in the 
upper part of Table 1.1 including the first de Morgan’s law are in Int, while all 
those below this law do not belong to Int. 
2.5 	Intuitionistic frames and formulas 
In the preceding section we used the method of semantic tableaux for 
constructing a countermodel for a given formula <p or proving that such a countermodel 
does not exist, i.e., ip e Int. Now we touch on a more general problem: given a 
formula to characterize in some non-trivial way the class of all frames 
validating ip. This problem turns out to be rather complicated. It will play an important 
role in the sequel. But here we consider it only for a few concrete formulas just 
to gain more experience in handling Kripke models. 
For the beginning let us take again the Dummett formula da. It follows 
from Example 2.29 that in every Hintikka system for (0, {da}) there must be 
(extensions of) three tableaux to, t\ and £2 shown in Fig. 2.7. It is clear that in 
this situation t\ is not accessible from t2, for otherwise q must belong to the left 
part of t\. Likewise, t\ does not see t<i- 
This observation gives us a necessary criterion for da to be refuted in a 
frame $ = (W, R), which can be represented as the following classical first-order 
condition on R: 
3x, y, z (xRy A xRz A -1 yRz A -1 zRy).  So,So, by the law of contraposition, the Dummett formula is valid in $ if the 
following condition holds: 
Vx, y, z (xRy A xRz —> yRz V zRy). 
A frame $ satisfying this condition is called strongly connected. Notice that every 
rooted strongly connected frame is a chain. 

INTUITIONISTIC FRAMES AND FORMULAS 
41 
to 
(—i—*p —> p) —> p V -ip 
((—'—'p —► p) —> p V -ip) —> -«p V -i-ip 
-ip v —«p 
p V -«p 
-np 
-'-'P (= -.p -► 1) 
p 
h 
-p 
-L, P 
(“■“■P -» p) -» p V -.p 
pV-ip 
p 
(a) 
to 
(—«—«p —► p) —► p V -ip 
((—1—<p —► p) —> p V ->p) —> -ip V —<p 
-ip V —1—»p 
-ip 
1 'P (= ^P -*• -L) 
-.-.p-vp 
-np 
(-,-,p p) p V 
P 
P 
-.-np 
(-1-ip —> p) —► p V -ip 
p V -ip 
*3 
-.p 
(-i-ip —> p) —> p V -ip 
p V ->P 
(b) 
Fig. 2.9. 

42 
INTUITIONISTIC LOGIC 
Proposition 2.36 A frame $ validates da iffS is strongly connected. 
Proof (=>) Suppose # = (W, R) validates (p-»g)V(g-> p) but is not strongly 
connected. Then there are points x, y, z G W such that xRy, ->yi?2 and 
-'zRy. Define a valuation 93 on $ by taking 
93(p) = y| and 93(g) = z\. 
Then y[£p—>g, and so x da, which is a contradiction. 
(4=) has been already established above. □ 
Now let us consider the formula 
wem = -ip V —1— 
which is known as the weak law of the excluded middle, and again try to find 
first a necessary condition for its refutability, and thereby a sufficient condition 
of its validity. 
Suppose -ip V -1-1 p is not true at a point x in a frame $ — (W, R) under 
some valuation. Then x and x Hence there are points y, z e x] 
such that y j= p and 2; |= -1 p. It should be clear that y and 2 do not see each 
other. The necessary refutability condition thus obtained does not differ from 
that for the Dummett formula. However, now it is too weak to be a sufficient 
one. For the frame in Fig. 2.2 (a) satisfies the condition and validates -1 p V —1—ip. 
The problem is that the points y and z not only do not see each other but have 
no common successors at all. Indeed, if yRu and zRu then, by Proposition 2.1, 
u |= p, u |= and so u \f= p, which is impossible. 
Thus, as a sufficient condition for the validity of -1 p V in a frame $ = 
(W, R) we can take the following one: 
V:r, y, 2 (xRy A xRz —> 3u (yRu A zRu)). 
A frame $ satisfying it is called strongly directed or convergent. A rooted frame 
is strongly directed iff every two points in it have a common successor. 
Proposition 2.37 A frame $ validates wem iff$ is strongly directed. 
Proof Again only the (=>) part needs a proof. If $ = (W, R) is not strongly 
convergent then there are points x,y,z E W such that xRy, xRz and there is 
no point u accessible from both y and 2. Define a valuation 93 in $ by taking 
93(p) = y|. Then z [= —«p, for otherwise there is u e z] such that u |= p, whence 
u e yt, which is a contradiction. Therefore, z Besides, y ^ ->p and so 
2^-ipV □ 
We define now inductively a sequence of formulas bdn: 
bdi = pi V -ipi, 

INTUITIONISTIC FRAMES AND FORMULAS 
43 
6dn+i — Pn+1 V (Pn-1-1 * bdn). 
The formulas bd\ and bd<i were already considered in Examples 2.4 and 2.30, 
from which it follows that to refute bd\ a frame must contain a chain of two 
points and to refute hcfc a three-point chain is required. In general, by induction 
on n one can readily show that $ bdn only if there is a chain of n + 1 points 
in #. 
We say a frame $ is of depth n < uj, d($) — n in symbols, if there is a chain of 
n points in # and no chain of more than n points. If for every n < u, $ contains 
an n-point chain then # is said to be of infinite depth oo. 
Proposition 2.38 A frame $ = (W,R) validates bdn iff d($) < n, i.e., iff $ 
satisfies the following condition 
n—1 
Vx0, • • •, xn ( f\ XiRxi+i -+\f Xi= Xj). 
i=0 i^j 
Proof Exercise. □ 
After depth let us introduce a notion of width of frames. A set of points 
X C W is called an antichain in a frame # = (W, R) if, for every x, y £ X, xRy 
implies x = y. In other words X is an antichain if distinct points in X do not 
see each other. We say a frame $ is of width n if it contains an antichain of n 
points and there is no antichain of greater cardinality. 
Are there any intuitionistic formulas which bound the width of a frame as 
bdns bound the depth? The frame ({0,1,2,...}, =) shows that such formulas do 
not exist, since it is the disjoint union of u single-point frames and so validates 
all formulas in Cl. However, we can bound the width of rooted frames by taking, 
for instance, the following formulas 
n 
bwn = \J(jPi V Pj), n> 1. 
i=0 j^i 
Notice that bw\ is the Dummett formula (modulo renaming the variables). We 
invite the reader to investigate the structure of refutation frames for bwn and 
prove 
Proposition 2.39 A frame $ = (W, R) validates bwn iff every rooted subframe 
of $ is of width < n, i.e., iff 
n 
Vx,x0,... ,xn {f\ xRxi —> XiRxj). 
i=0 i^j 
The following formulas bound the cardinality of rooted frames: 
bCn =Po V (po -► Pi) V ... V (j>0 A ... A Pn—l Pn), U > 1. 

44 
INTUITIONISTIC LOGIC 
Proposition 2.40 A frame $ = (W, R) validates bcn iff each rooted subframe 
of$ contains < n points, i.e., 
n 
\/x0,xi,...,xn (f\x0Rxi ->\JXi = Xj). 
i=1 i^j 
Proof (=>) Suppose $ contains n + 1 distinct points xo,xi,... ,xn such that 
{xi,..., xn} C xot- Without loss of generality we may assume that these points 
are indexed in such a way that XiRxj implies i < j. Define a valuation in $ 
by taking, for i = 0,..., n, 
V3(Pi) = {x e W : -ixRxi} — W — Xil. 
Then we shall have Xo po and, for i > 0, Xi \= po A ... A p*_i and Xi Pi. 
Indeed, otherwise either Xi f= pi, contrary to XiRxi, or Xi Pj for some j < i, 
whence XiRxj, contrary to our indexing of points. Therefore, since Xo sees all 
points xi,..., xn, we obtain xo bcn. 
(4=) Suppose bcn is false at a point xq in # under some valuation. Then 
x0 po and, for every i, 0 < i < n, there is a point Xj G io t such that 
|= po A ... A pi-1, Xi Pi. Clearly, the points xo,..., xn are distinct and so 
the subframe of $ generated by Xo contains > n + 1 points. □ 
To conclude this section we consider one more interesting family of formulas, 
namely, 
n n 
bbn = A ((Pi V Pj) V Pj) -Vp*. n - L 
1=0 i=0 
It turns out that their arbitrary validating frames cannot be characterized by 
first order conditions on the accessibility relation (see Chapter 6). However, their 
finite frames are quite manageable. 
Say that a finite frame $ is of branching < n if every point in # has at most 
n distinct immediate successors. 
Proposition 2.41 A finite frame $ = (W, R) validates bbn iff$ is of branching 
< n. 
Proof (=>) Suppose otherwise. Then there is a point x in # having at least 
n + 1 distinct immediate successors, say, xo,... ,xn. Define a valuation in # 
by taking 
®(ft) = W- (J Xjl 
and show that bbn is not true at x under 2J. Indeed, we have Xi Pj for all 
j / i, and sox ^ V?=o Suppose now that the premise of bbn is not true at 
x. Then there are y G x| and i G {0,... , n} such that y |= Pi —* V^jPj and 
y \JwPj, from which we obtain y ^ Pi- By the definition of 2J, this means 

INTUITIONISTIC CALCULUS 
45 
that y sees at least two distinct points among xo,... ,xn, which is possible only 
if y = x. But then we have x» j= pu Xi ViftPj an(^ so V Vi 
which is a contradiction. Thus, x bbn. 
(<*=) Suppose $ is a finite frame of branching < n, but # bbn under 
some valuation. Let x be a maximal point in $ where bbn is not true. Then 
we have x 1= /\"=0{{Pi -*• M^Pj) -» Vi&Pj) and x ^ \Jni=0Pi- Therefore, 
x Y1 Pi —► Pji f°r alH = 0,..., n, and so there are Xi G x| such that X* (= p* 
and Xi ^ V</j Pj- ^ follows that Xi and Xj do not see each other if i / j. Since # 
is of branching < n, x has a proper successor y seeing at least two distinct points 
Xi and Xj. But then y ft V"=oPi and> since V N A"=o ((Pi ^ Vi^Pj) -*• Vi&Pj), 
we have p ^ 66n, contrary to x being a maximal point in $ refuting bbn. □ 
Remark By Corollary 2.22, Proposition 2.41 cannot be generalized to infinite 
frames. 
The reader can find more examples among the exercises at the end of this 
chapter. The general problem of characterizing frames validating (or refuting) 
an arbitrary given formula will be considered in Chapter 9. 
2.6 	Intuitionistic calculus 
The Hilbert-type intuitionistic propositional calculus Int in the language £ is 
defined by axioms (Al)-(A9) and the inference rules MP and Subst of Section 1.3. 
The notions of derivation and derivation from assumptions are defined in exactly 
the same way as for classical calculus Cl. The fact of derivability of a formula <p 
in Int is denoted by h/nt <p, and r h/nt p means that p is derivable in Int from 
a set of assumptions T. If there is no danger of confusion, we write simply b p 
and TV-ip. 
In this section we show that Int is sound and complete with respect to the 
Kripke semantics introduced above. First we observe that when proving the 
deduction theorem for Cl, we used only axioms (Al) and (A2), and so this 
theorem holds for Int as well. 
Theorem 2.42. (Deduction) \~int then T h/nt ^ —► ip. 
The soundness and completeness of Int is proved by the same scheme as 
Theorem 1.16. 
Theorem 2.43. (Soundness and completeness of Int) For any formula p, 
•“int iff $ (= p for every frame #. 
Proof (=>) It suffices to verify that (i) axioms (Al)-(A9) are valid in all 
intuitionistic frames and (ii) the inference rules MP and Subst preserve the validity. 
Using the apparatus of semantic tableaux, the reader will easily establish (i). 
The fact that MP preserves the validity follows immediately from the definition 
of the truth-relation f=. 
Let us consider Subst. Suppose that |= p but y=- ps for some substitution 
s. Then there is a countermodel 9Jt = (#, 2J) for ps. Define a new valuation il in 

46 
INTUITIONISTIC LOGIC 
£ by taking ii(p) = 9J(pa), for all p G Var£, and put 9t = (£,11). Then clearly we 
have (9t,:r) |= <p iff (9Dt,x) |= </>s, for all x in £. Therefore, is a countermodel 
for p, contrary to our assumption. 
(4=) Suppose I-fint <P- We show then that there is a Hintikka system f) = (T, S) 
for the tableau (0, {</>}), and so p. 
Call a tableau (r, A) consistent in Int if T b int ^1 V... V^n holds for no 
formulas ^1,..., G A. Thus, the tableau (0, {<p}) is consistent. 
Let to = (r0, Ao) be a consistent tableau such that To, Ao C Subp. In exactly 
the same way as in the proof of Theorem 1.16 we show that to can be extended 
to some disjoint saturated (in Int) and consistent (in Int) tableau tn = (rn, An) 
such that rnUAn = Sub</>. But this time tn does not in general satisfy condition 
(S6). 
Denote by T the set of all disjoint saturated consistent tableaux (r, A) such 
that T U A = Sub p. T is clearly non-empty. Define a partial order 5 on T by 
taking, for any t = (r, A) and tf = (r', A'), 
tSt' iff T C T' iff A D A'. 
We show now that fj — (T, S) is a Hintikka system. It is clear that only (HS/2) 
requires verification. Suppose t = (I\A) G T and x/j —> x £ A. Consider the 
tableau to = (rc{^}, {x})- It is consistent, for otherwise we would have T, xjj b x 
and so, by the deduction theorem, T h ^ —> x» contrary to the consistency of 
t. Therefore, to can be extended to a disjoint saturated consistent tableau t' = 
(r', A') which belongs to T. Since T C T', we have tSt'. And by the definition, 
rj) G T' and x € A'. 
Thus, Sj = (T, S) is a Hintikka system for (0, {</>}). By Proposition 2.31, this 
means that 9) ^ ip. Notice by the way that \T\ < 2lSub^l> □ 
Corollary 2.44 Int = {</> G For£ : bjnt </?}. 
The following two theorems are proved by the same argument as 
Theorem 2.43, although applied to infinite tableaux (for details see Section 5.1). 
Theorem 2.45. (Strong completeness) Each tableau consistent in Int is 
realizable. In particular, T bint <p iff (9DT, x) |= ip for every model 9Jt and every 
point x in DJI such that (DJt,x) |= T. 
Theorem 2.46. (Compactness) A tableau is realizable in Int iff its every 
finite subtableau is realizable in Int. 
2.7 	Embeddings of Cl into Int 
In this section we will consider some connections between classical and intuition- 
istic propositional logics. As we know, Int C Cl. On the other hand, we can try 
to embed Cl into Int in the following sense. 
Let L\ and L2 be some logics, possibly in distinct languages C\ and £2, 
respectively. An effective function Tr from For£i into For£2 is called an 
embedding (or a translation) of L\ into £2 if, for all ip G For£i, 

EMBEDDINGS OF CL INTO INT 
47 
(p 6 Li iff Tr(ip) G L2. 
(In general, this definition is too extensive, for it admits, for instance, such a 
trivial “embedding” of Cl into Int as 
Tif^eCl 
1 if tp i Cl. 
However, we are not going to develop here a theory of embeddings and confine 
ourselves to considering only a number of concrete ones. For more elaborate 
definitions of translations preserving the structure of formulas see, e.g. Epstein, 
1990.) 
Embedding operations may be useful at least in two respects. First, sometimes 
they make it possible to interpret logical connectives in in terms of those in C2. 
And second, embeddings may preserve various properties of logics; for example, 
if Li is embeddable into a decidable logic L2 then Li is also decidable. 
A simple embedding of Cl into Int is provided by the following: 
Theorem 2.47. (Glivenko’s theorem) For every <p, <p G Cl iff -*-up G Int. 
Proof (=>) Suppose otherwise, i.e., <p G Cl and -i-up ^ Int. Then there are a 
finite model 971 and a point x in 971 such that x ^ Hence there is y G x] 
for which y f= -kp. Let z be some final point in the set y|. By Proposition 2.1, 
z \= -up and so z ^ -*-up. Let 97li be the submodel of 971 generated by z, 
i.e., (97ti, z) \= p iff (971, z) [= p, for every variable p. According to the generation 
theorem, 97ti refutes -*-up. But since this model contains only one point, it follows 
that -i-iip ^ Cl, which, by the law of double negation, is a contradiction. 
(<^=) -i-iip e Int implies -i-up G Cl, whence, using that law again, we obtain 
<p G Cl. Gl 
Corollary 2.48 The map Tr\ defined by XVi(<p) = -i-^, for every formula ip, 
is an embedding of Cl into Int. 
Corollary 2.49 For every formula ip, -up G Cl iff-up 6 Int. 
Proof According to Example 2.34, -up <-► —i—»—»(p G Int. The rest follows from 
Glivenko’s theorem. □ 
Corollary 2.50 For every formula (p = ^ <p G Cl iff (p G Int. 
Proof xj; —> -ix is the abbreviation for the formula ^ > (x —► -L), which is 
equivalent in Int to x/jAx —> -L, i.e., _i('0Ax)« And by Corollary 2.49, _i('0Ax) ^ Cl 
iff -i(x/; Ax) G Int. □ 
Corollary 2.51 For every formula ip containing no connectives different from 
A and tp G Cl iff p G Int. 
Proof If (p contains neither —^ nor V then it can be represented in the form 
<P = <pi A ... A <pn where each pi is either an atom or has the form -ixpi for some 

48 
INTUITIONISTIC LOGIC 
fa. By axioms (A3) and (A4), <p E Cl implies <pi E Cl for alH = 1,..., n. Since 
atoms are outside of Cl, ip E Cl only if <pi = -ifa E Cl for alii = 1,..., n, and 
so, by Corollary 2.49, ipi E Int. Now, applying (A5), we obtain <p E Int. □ 
Corollary 2.51 gives rise to another embedding of Cl into Int. Indeed, let TV2 
be a map from C to C defined as follows: 
Tr2(p) = </?, for all atomic </?, 
XV2('0 A x) =Tr2(fa ATr2(x), 
Tr2('0 V x) = ~'(-'Tr2(fa A-iTr2(x)), 
Tr2{xj) -> x) = ~'(Tr2(fa A -1 Tr2(x)). 
Corollary 2.52 XV2 25 an embedding of Cl into Int. 
Proof By induction on the construction of <p it is not hard to show that <p 
Tr2(<p) E Cl. It remains to observe that Tr2(p) contains neither V nor —> and 
use Corollary 2.51. □ 
Theorem 2.53 If a formula <p contains no V and every occurrence of a variable 
in <p is in the scope of some -> then <p +-> -*-np E Int. 
Proof As follows from Example 2.5, <p —> E Int for every <p. So we prove 
only that -\-«p —> p E Int. We will do this by induction on the construction of 
</?, regarding <p as constructed from formulas of the form and _L with the help 
of —> and A. The basis of induction follows from Example 2.34. 
Suppose that <p = —> x an(i ► x) —► x) i Int. Then there 
is a finite model 971 such that x f= ->->('0 —> x)> x H ^ and x ^ X for some 
point x in DJI. By the induction hypothesis, x -1-1X £ Int and so x ^ -i-ix- 
Hence y ^ x> f°r some final point y E We also have yf=-i-i(^—>x)> whence 
V V1 -1('0 ~* X) and so, since y is final, y f= —> x- And since y f= we get 
y [= x? which is a contradiction. 
The case of <p = A x is considered analogously. □ 
We recommend the reader to analyze <p = V to make sure that 
Theorem 2.53 cannot be extended to formulas containing V. 
Using Theorem 2.53, we can construct one more embedding of Cl into Int. 
Theorem 2.54 The map Tr3 defined by the equalities 
Trs{±) = _L, 
Tr3(p) = —*p, for all p E Var£, 
Tr3(^Ax) =Tr3(fa ATr3(x), 
Tr3(^ V x) = “,(“,Tr3('0) A -.Tr3(x)), 
2>3(^ -> X) = 2>3(^) -> Tr3(x) 
25 an embedding of Cl into Int. 
Proof It is not hard to see that <p +-> Tr3(<p) E Cl for every formula <p. Besides, 
by Theorem 2.53, we have Tr3(p) «-> -1-1Tr3(<p) E Int. Therefore, by Glivenko’s 
theorem, </? E Cl iff Tr3{p) E Int. □ 

BASIC PROPERTIES OF INT 
49 
2.8 	Basic properties of Int 
Now we shall see which of the properties considered in Section 1.4 hold for Int 
and introduce some more. 
Consistency. Int is consistent, since Int c Cl c For£. 
Decidability. 
Theorem 2.55 Int is decidable. 
Proof According to Theorem 2.32, <p ^ Int iff there is a Hintikka system 
9) = (T, 5) for (0, {ip}) with \T\ < 2lSub<^. So a decision algorithm for Int 
may be as follows. We form all partially ordered sets containing at most 2lSub<^ 
tableaux (F, A) such that T, A C Sub<p. If at least one of them is a Hintikka 
system for (0, {ip}) then ip ^ Int; otherwise ip e Int. □ 
The difference between the decision algorithms for Cl and Int is that in 
the former case we check if a given formula ip is valid in a single finite frame, 
while in the latter one we have to check its validity in all frames with < 2lSub<^ 
points, and so the longer ip is, the more complicated frames must be considered. 
Is that unavoidable? Couldn’t one find a finite intuitionistic frame $ such that 
Int = {</?£ For£ : # \= </?}? 
Tabularity. A logic L is called tabular if there is a finite frame $ such that 
L — {ip e ForC : # f= ip}. 
By the definition, classical propositional logic is tabular. 
Theorem 2.56 Int is not tabular. 
Proof Suppose otherwise. Then there is a finite frame #, containing, say, n 
points, which refutes all formulas that do not belong to Int, in particular, 6dn+i, 
6u;n_|_i and bcn+i defined in Section 2.5, contrary to Propositions 2.38, 2.39 and 
2.40. □ 
Thus, no finite frame is able to characterize Int. However, the set of all finite 
frames or the set of all finite trees can do this. 
Finite approximability. A logic L is said to be finitely approximable (or 
to have the finite frame property) if there is a class C of finite frames such that 
L = {ip e ForC : e C 5 h </>}• 
Theorem 2.57 Int is finitely approximable. 
Proof Follows from Theorem 2.32. □ 
The property of finite approximability plays a very important role in non- 
classical logic, since, as we shall see in Section 16.2, by proving the finite 
approximability of a finitely axiomatizable logic, we thereby establish its decidability 
as well. 

50 
INTUITIONISTIC LOGIC 
Notice by the way that in fact Theorem 2.32 not only yields the finite ap- 
proximability of Int but also indicates an upper bound for the number of points 
in a minimal refutation frame for ip ^ Int. This upper bound determines the 
complexity of the decision algorithm presented in the proof of Theorem 2.55, 
and so we are naturally interested in its reduction. A detailed discussion of this 
and other questions concerning complexity theory can be found in Chapter 18. 
POST completeness. Int is not Post complete, since it has at least one 
proper consistent extension, namely Cl. It is of interest, however, that the 
following result holds. 
Theorem 2.58 Cl is the only Post complete extension of Int. 
Proof Suppose L is a Post complete extension of Int different from Cl. Then 
there is a formula p e L — Cl. By Theorem 1.23, we can find a variable free 
substitution instance 0 of p which is not in Cl. But then -i0 G Cl and, by 
Corollary 2.49, ->0 G Int, whence ->0 G L, contrary to 0 G L and L being 
consistent. □ 
Independent axiomatizability. 
Theorem 2.59 Int is independently axiomatizable. 
Proof Follows from the fact that Int is finitely axiomatizable. A subtler 
argument shows that axioms (A1)-(A9) are independent. □ 
Structural completeness. It is not difficult to verify that the 
congruence rules in Section 1.4 are both admissible and derivable in Int, and so the 
equivalent replacement theorem holds for Int as well. However, unlike Cl, Int 
is not structurally complete: 
Proposition 2.60 The Scott rule 
(—■—»p —> p) —> p V ->p 
-ip V -i-ip 
is admissible but not derivable in Int. 
Proof The fact that this rule is not derivable follows from the deduction 
theorem and Example 2.35, where a countermodel for the Scott formula was 
constructed. Let us show now that the Scott rule is admissible in Int. 
Suppose that -><p V ->->p ^ Int for some formula <p. Then, according to (A6) 
and (A7), -*p ^ Int and ->-«p ^ Int. By Corollary 2.49, -up ^ Cl and -*-«p ^ Cl. 
So there are single-point models 93li = (ffi,9Ji) and 9DT2 = refuting 
-up and respectively. Let aq be the point in Si and x2 the point in $2• 
Construct a new frame S whose diagram is shown in Fig. 2.10 and define a 
valuation 03 in it by taking, for every variable p, 
®(p) = *i(p)uaj2(p). 
9Jti and 93t2 are obviously generated submodels of DJI = (S, 03), and so (931, aq) 
-><p, (DJt,x2) whence {DJI, x\) f= p, {DJl,x2) \= ~*p and (DJl,x2) p. 

BASIC PROPERTIES OF INT 
51 
Xi x2 
Xo 
Fig. 2.10. 
Then Xo <p, xo ^ "1^, and hence xo <p V -«p. On the other hand, we have 
x0 |= —> ip. Indeed, otherwise Xi f= ->-np and Xi <p for some i G {0,1,2}. 
Clearly, i ^ 1,2. And if i = 0 then, by Proposition 2.1, x2 f= which is a 
contradiction. 
Thus, 9DT refutes the formula (->-><p —> cp) —> <pV-«p, and so it does not belong 
to Int. □ 
Theorem 2.61 If an inference rule is admissible in Int then it is derivable in 
Cl. 
Proof Suppose on the contrary that a rule <pi,... ls admissible in Int 
but <pi A ... A (pn —> <p Cl. By Theorem 1.23, a variable free formula of the 
form (fis A ... A (pns —> <ps is not in Cl, from which <pi s A ... A <pns G Cl and 
<ps Cl. By Corollary 2.27, we then have p\S A ... A <pns G Int and <ps Int, 
which is a contradiction. □ 
The structural completeness and decidability of Cl provide us with an 
algorithm for recognizing whether a given rule is admissible in Cl or not. However, 
for Int the admissibility problem turns out to be much more complicated. We 
shall consider it in Section 16.7. 
Interpolation property. Int like Cl has the interpolation property. The 
proof of this fact can be obtained by generalizing the construction we used for 
proving Theorem 1.28. We postpone it till Section 14.1. 
Local TABULARITY. It will be shown in Section 7.7 that there exist infinitely 
many formulas of only one variable which are pairwise non-equivalent in Int. 
Thus, we have 
Theorem 2.62 Int is not locally tabular. 
Proof Follows from Example 7.66. □ 
Hallden COMPLETENESS. Clearly, Hallden completeness follows from the 
disjunction property. So the following theorem is an immediate consequence of 
Theorem 2.64, which is proved below. 
Theorem 2.63 Int is Hallden complete. 
Disjunction property. 
Theorem 2.64 Int has the disjunction property, i.e., for any formulas and 
(f V -0 G Int iff p € Int or ^ G Int. 

52 
INTUITIONISTIC LOGIC 
Fig. 2.11. 
Proof Suppose that <p and xp do not belong to Int and show that in this case 
ip\/ \j) Int. 
Let 9DTi = (3i,9Ji) and 9DT2 = ($2,^2) be countermodels for <p and xp based 
on disjoint frames #1 = (Wi,Ri) and S'2 = with roots x\ and X2, 
respectively. Construct a new frame S = (W, R) by adding root xo to Si + S2 
(see Fig. 2.11). In other words, W = {#0} U W\ U W2 and xRy iff x = Xo or 
xRiy or xR^y, for all x,y eW. Put 9J(p) = 9Ji(p) U 9?2(p), for every p e Var£, 
and consider the model 9DT = (S, 21). It is clear that 9DTi and 9DT2 are generated 
submodels of 971. Then (971, Xo) ip, (971, xo) xp and so (97t,x0) \£<pV xp. 
The converse implication follows from (A6) and (A7). □ 
2.9 	Realizability logic and Medvedev’s logic 
We conclude the discussion of intuitionistic logic by outlining two ways of refining 
the proof interpretation. 
Kleene (1945) formalized it by treating the intuitionistic connectives 
algorithmically: for example, 
• a proof of <pVxp is given by presenting a program establishing <p or a program 
establishing xp together with an effective test indicating which disjunct is 
established; 
• a proof of <p —> xp is given by presenting a program which transforms any 
program establishing <p into a program establishing 7/!>. 
Since programs in a fixed algorithmic language (say, the language of Minsky 
machines to be introduced in Section 16.1) can be effectively coded by the Godel 
numbers (see e.g. Mendelson, 1984), the above definition can be represented in 
the (first order) language of formal arithmetic. Namely, with every arithmetic 
sentence <p we associate a formula xr<p, which is read as “the number x realizes 
<pn, in the following way: 
xrxp = xp, xp atomic, 
xr(xp Ax) = 3y,z (x = 2y • 3Z A yrxp A zrx), 

REALIZABILITY LOGIC AND MEDVEDEV’S LOGIC 
53 
xrfy V \) = ((a: = 2° • 3y A yr0) V (a: = 21 • 3Z A zr*)), 
xr(xf -+ x) = Vy (yr^ -> /*(y)rx), 
xrVy^iy) = Vy (fx(y)rxf(y)), 
xr3yr/)(y) = 3u, z (x = 2U • 3* A ur^(z)), 
where /x is the program with the Godel number x (for a precise definition consult 
Mendelson, 1984). And now we call an £-formula </? realizable if the first order 
formula 3x(a:r(y>s)) is true for every substitution s of arithmetical sentences 
instead of the propositional variables in <p. 
It is not hard to see that the set of realizable ^-formulas is closed under MP 
and Subst; it is called realizability logic. Nelson (1947) proved that it contains 
Int. It turned out, however, that realizability logic is a proper extension of Int: 
Rose (1953) showed that it contains the formula sa{-^q V -<r/p} which does not 
belong to Int. Unfortunately, very little is known about realizability logic. One of 
a few established facts is that it has the disjunction property; see Varpakhovskij 
(1965). A class of realizable propositional formulas containing all known formulas 
of that sort was described by Varpakhovskij (1973). 
Another formalization of the proof interpretation (of Kolmogorov’s 
interpretation, to be more precise) was proposed by Medvedev (1962), who treated intu- 
itionistic formulas as finite problems. Formally, a finite problem is a pair (X, Y) 
of finite sets such that Y C X and X ^ 0; elements in X are called possible 
solutions and elements in Y solutions to the problem. The operations on finite 
problems, corresponding to the logical connectives, are defined as follows: 
(Xu Yi) A <X2, Y2) = (Xx x X2, Yi x Y2), 
(Xu Yi) V <X2, Y2) = (Xx U X2, Yx U Y2), 
(X1,Y1) -> (X2,Y2) = (x?\{f e X: /(Yi) C Y2}) , 
-L = <X,0). 
Here X U Y = (X x {1}) U (Y x {2}) (i.e., X U Y is the ordered union of X and 
Y) and XY is the set of all functions from X into Y. Note that in the definition 
of _L the set X is fixed, but arbitrary; for definiteness one can take X = {0}. 
Now we can interpret formulas by finite problems. Namely, given a formula </?, 
we replace its variables by arbitrary finite problems and perform the operations 
corresponding to the connectives in <p. If the result is a problem with a non-empty 
set of solutions no matter what finite problems are substituted for the variables 
in then ip is called finitely valid. One can show that the set of all finitely valid 
formulas is closed under MP and Subst and contains Int; it is called Medvedev’s 
logic and denoted by ML. 
In fact ML can be defined semantically, similarly to how Int was introduced. 
Let Wn be the family of non-empty subsets of a set with n > 0 elements and 
xRny mean y C x, for every x,y e Wn. The pair ?8n = (Wn,Rn) is clearly a 
Kripke frame; we call it a Medvedev frame. Medvedev frames have an elegant 

54 
INTUITIONISTIC LOGIC 
geometrical form: they look like n-ary Boolean cubes with the top point deleted 
(for n = 1,2,3,4 they are depicted in Fig. 2.12). Medvedev (1966) showed that 
ML coincides with the set of ^-formulas that are valid in all Medvedev frames. 
We offer the reader to check that ML contains the formulas sa and kp (see 
Exercise 2.10) which do not belong to Int. 
2.10 	Exercises 
Exercise 2.1 Show that, for any family {Xi : i G 1} of subsets of W in a frame 
$=(W,R), 
(Ux*)t = u™, ((J*<H = lto)’ 
i€l i€/ i€/ i€/ 
<n*)T£ri(*T>. 
iel i€l iel i€l 
Is it possible to replace C here with =? 
Exercise 2.2 Can the generation theorem be extended to not necessarily 
generated submodels? Does the operation of forming subframes preserve validity? 
Exercise 2.3 Show that an infinite frame contains either an infinite ascending 
chain or an infinite descending chain or an infinite antichain. (Hint: use Konig’s 
lemma, according to which every infinite tree of finite branching contains an 
infinite ascending chain.) 
Exercise 2.4 Let = (3i,9Ji) and DJl2 = (#2,^2) be two models based on 
frames #1 = (Wi.Ri) and #2 = (W2,R2), respectively. A non-empty binary 
relation 5 C W\ x W2 is said to be a bisimulation between 9DTi and dJl2 if the 
following conditions are satisfied: 
• if x\Sx2 then x\ f= p iff x2 f= p, for every variable p; 
• if xiSx2 and x\R\yi then there is y2 G W2 such that y\Sy2 and x2R2y2\ 
• if X\Sx2 and x2R2y2 then there is pi G W\ such that y\Sy2 and XiRiyi. 
Prove that if 5 is a bisimulation between fflli and ffll2 and X\Sx2, then x\ \= ip 
iff x2 f= (p, for every formula <p. Derive from this the generation, reduction and 
disjoint union theorems. 

EXERCISES 
55 
Exercise 2.5 Show that each finite frame of branching < n is a reduct of some 
finite n-ary tree. 
Exercise 2.6 Show that two finite rooted frames are isomorphic iff they validate 
the same formulas. 
Exercise 2.7 Give a purely syntactic proof of Proposition 2.26 (by induction 
on the construction of <p). 
Exercise 2.8 Prove that every formula <p £ Int is refuted by a tree of depth 
and branching < |Sub<p|. 
Exercise 2.9 Prove that every disjunction free formula <p £ Int is refuted by a 
finite binary tree. 
Exercise 2.10 Show that a frame # = (W,R) validates the Kreisel-Putnam 
formula 
kp = (-ip —> qW r) —> (-p —> q) V (->p —> r) 
iff $ satisfies the following condition 
\/x,y,z (xRy A xRz A -■yRz A -■zRy —► 3u (xRu A uRy A uRz A 
Vu (uRv —► 3w (vRw A (yRw V zRw))))). 
Exercise 2.11 Show that a frame $ = (W,R) validates the formula 
n 
btWn = A “’(“'Pi A "'Pj) V (_'Pi V 
0 <i<j<n i—0 j^i 
iff # satisfies the condition 
n 
Vx, X0, ■ ■ ■ , xn( A xRxi ^ V A xjRV))- 
i=1 
If # is rooted and finite, then this condition means that # has < n final points, 
i.e., btwn bounds the top-width of 
Exercise 2.12 Prove that # validates sa iff no generated subframe of # is 
reducible to the frame shown in Fig. 2.9 (c). 
Exercise 2.13 Show that a frame # = (W, R) refutes bbn iff there is a subframe 
® = (V, 5) of # such that xRyRz implies y E V whenever x,z G V and 0 is 
reducible to the n + 1-ary tree of depth 2. 
Exercise 2.14 Prove that ^ Ar=o(“*Pi -> iff there is a 
generated subframe of $ reducible to the n + 1-ary tree of depth 2. 
Exercise 2.15 Show that a rooted frame validates the formula 
sm = (-iq p) (((p q) ^p) ^p) 
iff it contains < 2 points. 

56 
INTUITIONISTIC LOGIC 
Exercise 2.16 Show that the Skvortsov formula 
(-i(p A q) —> -,(-1P A q) V -i(p A -iq)) —> A q) V -i(p A -ig) 
belongs to ML — Int. 
Exercise 2.17 Define by induction a sequence of finite trees 3n, known as 
Jaskowski’s frames: is the single-point frame and 3n+i is the result of adding 
a root to the disjoint union of n copies of 3n. Prove that 
Int = {(f e For £ : 3n \= V for every n > 0}. 
Exercise 2.18 Say that a connective O is independent in a logic L if there is no 
formula <p without occurrences of O such that p0q +-> <p G L (if O = _L then, of 
course, _L +-> <p G L). Prove that A, V, —> and _L are independent in Int. (Hint: to 
prove that A and V are independent use the disjoint union of one- and two-point 
rooted frames and the three-point rooted frame, respectively.) 
Exercise 2.19 Prove that for every set of formulas T and every formula <p, 
r hci V iff 2Y<(r) hJnt Tri(<p), 
where Tr*(r) = {Trj(^) : ^ G T} and i = 1,3. Does this equivalence hold for 
i = 2? 
Exercise 2.20 Define by induction the set H of Harrop formulas: (i) all 
variables are in H; (ii) if (p and ^ are in H then <p A ^ and x ^ are also in H, for 
every formula x* Prove that for any set T of Harrop formulas and all formulas <p 
and 
r h/nt V v ^ implies V h/n£ p or V \~Int 
Is this true for an arbitrary set of formulas T? 
2.11 	Notes 
Intuitionistic logic as a formal explication of Brouwer’s (1907, 1908) ideas was 
constructed in the form of Hilbert-style calculus by Kolmogorov (1925), Orlov 
(1928) and Glivenko (1929), who considered the propositional language, and 
then, for the predicate case, by Heyting (1930). For more detailed historical 
information about intuitionistic logic and its relation to intuitionism and 
constructivism the reader can consult TYoelstra (1969), Dummett (1977), Beeson 
(1985), van Dalen (1986). 
The intended meaning of the intuitionistic connectives was explained first in 
terms of the proof interpretation due to Brouwer, Kolmogorov and Heyting. It 
was not clear, however, how to construct a reasonable formal semantics 
consistent with this informal interpretation, or even just any semantics with respect 
to which Int would be complete (Godel had just proved his completeness 
theorem for classical predicate logic). The semantical studies of Int were started by 

NOTES 
57 
Godel (1932), who showed that it is not tabular. Jaskowski (1936) constructed a 
sequence of finite matrices characterizing Int (see Exercise 2.17 giving the frame 
variant of Jaskowski’s construction). In fact he was the first to prove that Int 
is finitely approximable. Stone (1937) and Tarski (1938) discovered a connection 
between the derivability in Int and topological spaces, which was developed by 
McKinsey (1941), McKinsey and Tarski (1944, 1946) into the algebraic semantics 
for Int to be considered in full detail in Chapter 7. For a category-theoretical 
generalization of the topological semantics see Goldblatt (1979). 
Note that in the 1940s and 1950s Novikov in his course on intuitionistic 
logic at Moscow University proposed an informal arithmetic interpretation of Int 
which also led to the topological completeness (much later these lectures were 
published as book Novikov, 1977). Loosely, the idea of Novikov’s interpretation 
is as follows. Atomic propositions are regarded as statements about comparing 
weights: t\ < £2, £1 > £2, ti = ^2* To check whether they are true or not, we have 
at our disposal an unlimited collection of arbitrarily precise (but not absolutely 
precise!) scales. So by a finite number of weighing we can prove or disprove 
propositions of the form £1 < £2, £1 > £2 but we can never establish that a 
proposition of the form t\ = £2 is true, though we may be able to refute it. 
Kolmogorov (1932) proposed to consider Int as a logic of problems but did 
not formalize his idea, which was partly fulfilled later by Kleene (1945), Godel 
(1958), Medvedev (1962), Artemov (1987b). Godel (1933a) gave an 
interpretation of the intuitionistic connectives via the corresponding classical ones by 
embedding Int into Lewis’ modal system S4 (based on classical logic) and 
treating its necessity operator as “it is provable” (for details see Section 3.9). Before 
Godel actually the same results were obtained by Orlov (1928). However, his 
paper remained unnoticed for a rather long time. This “classical” view on 
intuitionistic logic was developed further by Novikov (1977). Embeddings of Cl into 
Int were constructed by Glivenko (1929), Godel (1933b), Gentzen (1934-35) and 
Lukasiewicz (1952). 
The relational semantics we considered in this chapter was introduced by 
Kripke (1965a). In fact it can be traced back to Jonnson and Tarski (1951) who 
represented algebras for the modal logic S4, and hence implicitly for Int, in the 
form of frames, and to Dummett and Lemmon (1959) who did this explicitly 
for finite algebras. A somewhat different relational semantics was constructed by 
Beth (1956); a close interpretation of intuitionistic connectives was proposed by 
Grzegorczyk (1964). Semantics combining in themselves both Kripke and Beth 
frames are considered in Dragalin (1979). In general, the semantical apparatus 
for Int was developed after the corresponding apparatus for modal logics to be 
considered in the next chapter. Sometimes, however, new semantical concepts 
were first introduced for Int, witness a sort of p-morphism considered by de 
Jongh and Troelstra (1966). 
Our proof of completeness is similar to that of Fitting (1969), although again, 
as in the case of Cl, we define Hintikka systems as a tool for constructing 
countermodels rather than for obtaining a proof system for Int. There exist other 
proofs of completeness. For instance, one can extract from Dragalin (1979) a 

58 
INTUITIONISTIC LOGIC 
direct proof that Int is complete with respect to the full binary tree. This result 
was first obtained by Smorynski (1973); see also Kirk (1979) who showed that, 
for each n > 2, Int is characterized by the class of all n-ary trees. 
Gentzen (1934-35) represented Int as a system of natural deduction and as 
a calculus of sequents. In a purely syntactic way he proved that Int is decidable 
and has the disjunction property. A syntactic proof of the interpolation property 
can be found in Schiitte (1962). 
An interesting syntactical property of Int was discovered by Wajsberg (1938) 
(see also Horn, 1962) who constructed a variant of intuitionistic calculus to derive 
a formula p in which it is sufficient to use (Al), (A2) and only those axioms that 
contain connectives really occurring in p. Logics which can be represented by 
calculi with this property are called separable. Many extensions of Int were proved 
to be separable, in particular, Cl (see Hosoi, 1966c). It is unknown whether one 
can effectively recognize the separation property, given a finite set of axioms 
extending Int. Although it follows from Khomich (1979) that this can be done 
in the case of extra axioms in one variable, in general we conjecture that this 
algorithmic problem has a negative solution. The problem is not trivial even for 
tabular superintuitionistic logics. 
According to Exercise 1.3, the connectives in Cl are interconnected and they 
are enough to express all possible logical connectives which can be represented 
by truth-tables. This property is known as truth-functional completeness. The 
situation with the connectives in Int is much more complicated. First, as was 
noted by McKinsey (1939), they are independent (see Exercise 2.18). This result 
was developed then in two directions: expressing intuitionistic formulas in each 
other and adding new connectives to the language of Int. 
Since Int is not truth-functional, the notion of expressibility in Int is defined 
in the following way. Say that a finite sequence of formulas pi,-..,pn is an 
expression in Int via a list of formulas T if one of the following four conditions 
holds for each pi. 
• Pi is a variable; 
• Pi £ T; 
• there are j,k <i and a variable p such that pi = PkWj/p}', 
• there is l < i such that pi pi £ Int. 
A formula p is said to be expressible in Int via T if p is a member of some 
expression via T. Expressibility in Int turned out to be much more complicated 
than expressibility in Cl and many-valued logics (see Jablonskij, 1979). In any 
case, no algorithm is known to determine whether a formula is expressible in Int 
via a list of formulas. A significant result in this direction was obtained by Ratsa 
(1982), who gave a positive solution to the algorithmic problem of recognizing 
whether a given list of formulas is functionally complete in Int (and even in any 
superintuitionistic calculus!) in the sense that every formula is expressible via 
the list. Here are two examples of functionally complete sets in Int found by 
Kuznetsov (1965): 
{p-*(?A ->r) A (q' V r')}, 

NOTES 
59 
{((P V q) A -»r) V (-p A (g r))}. 
The following sequence is an expression via the latter formula containing all 
intuitionistic connectives (as formulas, of course): 
((pVg)A->r)V(^pA(g r)),p, q, r, ((pVg)A-ig)V(-ipA(g q)), 
(p A ^q) V -ip, (p A -ip) V ->p, -ip, (p A -i-ip) V -ip, p V ->p, ->(p V ->p), 
±, -i±, ((p V g) A -.X) V (^p A (g <-» X)), (p V g) V (-ip A ->g), 
((p V g) A -i-iX) V (-.p A (g <-> -.X)), -.p A g, -.g, -.p A ->g, -.p A r, 
-'(-‘P A -ig) A r, -i(-ip A -.g) A ((p V g) V (-ip A ->g)), p V g, ((X V 
g) A -ir) V (-iX A (g <-> r)), (g A t) V (g <-> r), (g A -ip) V (g <-> p), 
~'(~,pAq)Ar, ->(-<pAq) A ((gA->p) V (g <-» p)), p <-> g, (pVg) g, 
P^q,P^ (j>^Q),pAq. 
Functional incompleteness of the usual systems of connectives in Int made it 
possible to introduce various “new” connectives generalizing the standard ones 
(infinitary disjunctions, conjunctions, etc.; see for instance, Nadel (1978), Goad 
(1978), de Jongh (1980), Kalicki (1980), Wojtylak (1983)). On the other hand the 
language of Int was enriched by modal operators; we shall give some references 
in Section 3.12. An interesting connective U, called the weak disjunction, was 
introduced by Medvedev (1966) for ML and then considered by Skvortsov (1983) 
for Int and its extensions. Semantically U may be defined like this: 
(9K,x) |= (pUxp iff Vj/ (xRy -► ((97t,p) |= <p) V ((97t,p) |= ip) V 
3u, v (yRu A yRv A ((97t, u) |= ip) A ((971, u) (= ip) A 
Vu; (piiw —► V itfCv))), 
where aCb means 3z(aiiz A bRz). Skvortsov (1983) justifies the given definition 
by the following considerations. Let us understand points in frames as “reasons” 
or “arguments” in a controversy. Chains are regarded as possible ways of its 
development (or possible ways of researches, if we argue with nature). A point 
x in a model is a reason for ip if (971, x) |= ip. Say that ip is intuitionistically 
established at a point y by reason x if ((971, x) |= ip) A xRy\ tp is classically 
established at y by reason x if ((971, x) |= p) A xCy. 
The intuitionistic disjunction ip V ip is true at x if either p or ip is 
intuitionistically established at x. The classical disjunction (we use for it another 
symbol) ipVip = -i-i(y> V ip) is true at x if, for every initial development of 
the controversy, either ip or ip remains classically established (by some reasons) 
at any point. The relation (971, x) |= <p U ip can be represented in the form 
Vy(xRy —► (971, j/) {=' tpU ip), where the restricted quantifier Vy(xRy —► 
corresponds to an arbitrary initial development of the controversy and (971, y) \=' ipUip 
means that either the intuitionistic disjunction ipVip has been already established 
at y or (above x) there are two reasons for <p and ip, respectively, which alone 
establish the classical disjunction at x. Roughly speaking, the weak disjunction 
^ LI -0 reduces to the problem of classical establishing (p or ip by some unique, 
concrete reasons for them and not on the ground of the general distribution of 
truth-values of (p and ip. 

60 
INTUITIONISTIC LOGIC 
Note also that Medvedev (1979) and Skvortsov (1979) introduced some 
interesting variants of negation added to Int. Vorob’ev (1952a, 1952b, 1972) added to 
Int the so called strong negation; the resulting logic was investigated by Gurevich 
(1977), Vakarelov (1977), Sendlevski (1984), Goranko (1985). 
New intuitionistic connectives can be introduced semantically. Yashin (1985) 
used some ideas of McCullough (1971) to define an intuitionistic connective as 
a formula in the language of the elementary theory of Kripke models with one 
parameter satisfying the following conditions: the monotonicity with respect to 
accessibility; all quantifiers are of the form Vx > y or 3x > y\ a proposition with 
such a connective should not distinguish between two models one of which is 
obtained from the other using the operations of reduction and the formation of 
elementary equivalent models. It turns out that intuitionistic connectives in this 
sense are only the standard intuitionistic propositional formulas. A similar result 
for the modal case was obtained by Yashin (1986). Yashin (1989) described the 
connectives that result from relaxing the conditions above. 
Novikov (see Smetanich, 1960) and Gabbay (1977) gave syntactical definitions 
of new intuitionistic connectives. Let A be an extra unary connective and Int(X) 
a calculus obtained by adding to Int some new axioms describing A. According 
to Novikov, Int(A) defines a new connective if 
• Int(X) is conservative over Int, i.e., if Int(X) b (p and (p does not contain 
A, then Int b tp\ 
• Int(X) h (p q) —> (A(p) A(g)); 
• for every A-free formula </?, Int(X) 4- A(p) (p is not conservative over Int. 
According to Gabbay, Int(X) defines a new connective if 
• Int{A) is conservative over Int; 
• no explicit definition of A is derivable in Int(A); 
• Int(X) has the disjunction property; 
• some explicit definition of A is derivable in Int(X) 4- —> p; 
• the axioms of Int(X) define the meaning of A uniquely in the sense that 
Int{X) + Int{A') b A —► A'; 
• A is definable in the second order intuitionistic calculus. 
Smetanich (1960) showed that we get a new Novikov connective by adding to 
Int the axioms 
A (p) A {q), -.-iA (p), A (p) -*qV^q. 
Bessonov (1977) constructed a continuum of similar axiomatic systems defining 
new connectives and Yashin (1994) showed that the axioms 
-.-.A(p), A (p) ->gV-.g, 
define a new connective as well. 
The result of Exercise 2.9 is due to Segerberg (1974). 

3 
MODAL LOGICS 
When discussing in Section 2.1 the meaning of intuitionistic connectives, we 
used in our language—a metalanguage with respect to £—the undefined notion 
“proof’. Making the proof interpretation somewhat rougher, we can treat, for 
example, the intuitionistic formula p —► q V r as the proposition 
“it is provable (it is provable p —► it is provable q V it is provable r)” 
with the classical connectives —► and V. “Modalized” propositions of that sort, 
containing such operators as “it is provable”, “it is necessary”, “it is obligatory”, 
etc., are the subject of modal logic, another branch of mathematical logic. 
3.1 	Possible world semantics 
The expressive capacities of the language £ of classical (or intuitionistic) logic 
do not allow us to decompose such propositions as 
(A) 	It is possible that water boils at 70°C 
or 
(B) It is necessary that water boils at 70°C 
into a combination of simpler propositions. Like the proposition 
(C) Water boils at 70°C, 
they can be regarded only as atomic. So we are able to express correctly in 
£ neither the implications “if (B) then (C)” and “if (C) then (A)”, which are 
naturally considered to be true, nor the implications “if (C) then (B)” and “if 
(A) then (C)”, which are probably recognized to be false. 
The propositional modal language M£ is obtained by enriching the language 
£ with the new unary connective □ and the corresponding formula formation 
rule 
• if ip is an Af£-formula then (□</?) is also an A4£-formula, 
which is added to the rules in Section 1.1 (with £ being replaced with M.£, 
of course). The set of all A4£-formulas is denoted by YorM£ and the set of 
all variables in M£ by VarAf£. In addition to the conventions on formula 
representation, which were accepted in Section 1.1, we will assume □ to bind 
formulas stronger than A, V, —► and <-►. Thus, Up —> Uq V Ur is an abbreviation 
for ((Dp) -► ((Uq) V (Dr))). 

62 
MODAL LOGICS 
We define the connective O as dual to □, i.e., by taking 
Oip = ->□->(/?, for every ip £ ForMC, 
and consider it as strong as □ or -i. 
The connectives □ and O are usually read as “it is necessary” and “it is 
possible” and called the necessity and possibility operators, respectively So (A) 
and (B) above can be represented now as O(C) and □(C). However, the intended 
meaning of these connectives may vary. Here are only a few possible 
interpretations of □ and O. 
(i) □ is understood as logical necessity, i.e., as “it is necessary from the point 
of view of logical laws”, and O as logical possibility, i.e., “it does not contradict 
the logical laws”. 
(ii) □ may be regarded as epistemic necessity, i.e., as “it is known” (or “it is 
believed”). This interpretation seems to require some refinement, since at least 
two questions arise: “whom is this known to?” and “are the logical consequences 
of known propositions also known; say, is ^ known provided that ip and ip —► if) are 
known?”. We will assume that there is some ideal perceiving person, and the set 
of propositions which are known to him is closed under the logical consequence. 
In this case O may be read as “it does not contradict to anything that is known”. 
(iii) Another interpretation, closely related to (ii), is to understand □ as 
“it is (informally) provable (by an ideal mathematician) in some mathematical 
theory”; O means then “it does not contradict to the postulates of the theory”. 
(iv) □ may be also regarded as provability in some formal system, for instance, 
in formal Peano arithmetic PA. 
(v) One can understand □ as deontic necessity, that is as “it is obligatory”; 
O is then read as “it is permitted”. 
(vi) Sometimes □ is interpreted as tense necessity, that is as “it is true now 
and always will be true” and O as “it is true now or will be true afterwards”. 
Some modal formulas, which are acceptable under one interpretation of □, 
may turn out to be unacceptable under another one. For example, an arbitrary 
proposition of the form □ (□(£> —► ip) may be regarded as true in the cases (i), (ii), 
(iii) and (vi), but neither in (iv) nor in (v). Indeed, by accepting this principle 
for the formal provability in PA, we would then have that the formula D(0 = 
1) —► 0 = 1, and so its contraposition —*0 = 1 —► ->□(() = 1), are provable in PA5. 
And since the premise of the latter formula is provable in PA, the conclusion 
->□(0 = 1) must also be provable, contrary to GodePs second theorem, according 
to which the consistency of PA cannot be proved only by its own means. In 
the deontic case, Dip —► ip does not hold, since obligations may be not fulfilled. 
Another example: without stretching a point the principle Oip —► BOip can be 
accepted only for the logical necessity. 
On the other hand, all the interpretations of the operator □ listed above have 
many common traits. For instance, for all of them the principles 
5 How □ is formalized in PA is explained in Section 3.8. 

POSSIBLE WORLD SEMANTICS 
63 
□ (</? —► -0) —> (□</? —► D'tp) 
and 
□ ((/? A ip) <r-> Up A □?/> 
are acceptable. This makes it possible to consider them, at least to a certain 
extent, from a common standpoint by treating □ as some abstract necessity. 
Moreover, we shall see in the sequel that the differences in the interpretations 
we have just observed can be provided with a strict mathematical meaning. 
The interpretation of the modal language MC we are going to introduce now, 
first at the intuitive level and then, in the next section, in the form of precise 
definitions, is often called the relational or possible world semantics. Philosophers 
trace it back to Leibniz who understood necessity as truth in all possible worlds 
and possibility as truth in at least one possible world. 
As in classical logic, we assume that every proposition is either true or false. 
For example, it is natural to evaluate proposition (C) as false. However, it would 
be more exact to say that (C) is false under ordinary circumstances, in the 
ordinary world where we live. For we can imagine some other circumstances, 
another world in which water really boils at 70° C (in principle, we can even find 
ourselves in this world having climbed the summit of the Everest). That world 
where (C) becomes true may be called an alternative to our world or a possible 
world relative to it. Using Leibniz’s definition, we can say that proposition (A) 
should be recognized as true in our world, and (B), on the contrary, as false. 
In general, by abstracting from concrete details, we can imagine a system of 
worlds in which each world has some (possibly empty) set of alternatives. The 
alternativeness relation will be denoted by ii, so that xRy means that y is an 
alternative (or possible) world for x. Every world x “lives” under the classical 
laws: an atomic proposition is either true or false in it and the truth-values of 
compound non-modal propositions are determined by the usual truth-tables. A 
modal proposition Up is regarded to be true in a world x if p is true in all the 
worlds alternative to x\ Op is true in x if p is true at least in one world y such 
that xRy. 
Concrete properties of the alternativeness relation depend on the type of 
the modality under consideration. If we deal with the logical necessity then it is 
natural to regard any two worlds to be alternatives to each other; in other words, 
the alternativeness relation in this case is universal However, if we consider 
the tense necessity then possible worlds are states of our world (or some other 
developing process, e.g. a computer program) at different moments of time. The 
choice of a suitable alternativeness relation R depends then on our aims and 
views on the nature of time. For example, we may consider the course of time 
to be linear, and then R will be a linear ordering of the set of worlds, or we may 
think that time has a branching nature and take JR to be a tree-like ordering of 
possible worlds. 
Alternativeness relations for other interpretations of □ (say, epistemic, 
provability or deontic) may be not so clear. To characterize them, we should first 

64 
MODAL LOGICS 
describe more precisely the corresponding modalities, by defining them axiomat- 
ically, for instance. And after that, given a set of worlds, we can regard a world 
y as an epistemic (provability, deontic, etc.) alternative to x iff all that is known 
(respectively, provable, obligatory, etc.) at x is necessarily true at y. 
Epistemic, deontic, provability and a number of other modal logics will be 
introduced in Section 3.8. However, mostly in this chapter we will be considering 
the logic K of some abstract necessity describing those common properties that 
are characteristic for all interpretations of the operator □ above. 
3.2 	Modal frames and models 
In an intuitionistic frame $ = (W,R), which was used for representing possible 
states of information, the accessibility relation R between states was a partial 
order on W. We will represent systems of possible worlds with alternativeness 
relations between them in the form of frames as well, but for the present no 
conditions will be imposed on R. 
A modal Kripke frame $ = (W, R) consists of a non-empty set (of worlds) W 
and an arbitrary binary (alternativeness) relation R on W. Thus, intuitionistic 
frames are a special case of modal ones. Elements of W are called worlds or, as 
before, more neutrally, points. If xRy, we say that y is an alternative to x, or 
that y is accessible from x, or x sees y. Other synonyms and notations are: y is 
a successor of x, x is a predecessor of y, y 6 x|, x 6 y[. The notions of proper 
and immediate successor or predecessor are defined as in the intuitionistic case. 
Let us fix some propositional modal language MC. A valuation of MC in a 
frame $ = (W, R) is a map 2J associating with each variable p in VarMC a set 
D3(p) of points in W, i.e., 2J is a map from YarMC to 2W. 9J(p) is understood 
as the set of worlds at which p is true. 
A Kripke model of MC is a pair DJI = (#,9J) where $ = (W,R) is a frame 
and 2J a valuation in Let x be a point in By induction on the construction 
of ^ we define a truth-relation (DJI, x) |= ip, “ip is true at the world x in the model 
9JT, by taking 
(sro.x) 
b 
p 
iff 
X € ' 
27 (p), 
for every p £ "VarMC; 
(271, x) 
b 
ip Ax 
iff 
(971, 
x) |= 
'll) and (DJI, x) |= x\ 
(271, x) 
b 
<P vx 
iff 
(971, 
x) |= 
^ or (DJI, x) |= x\ 
(OR,*) 
b 
-* x 
iff 
(271, 
x) \= 
^ implies (DJI, x) |= \\ 
(971, x) 
b 
i; 
(971, x) 
b 
Dip 
iff 
(271, 
T 
xl) for all y e W such that xRy, 
and so 
(DJI, x) |= iff (9DT, x) 'ip 
(DJI, x) |= O'tp iff (DJI, y) |= -0 for some y £ W such that xRy. 

MODAL FRAMES AND MODELS 
65 
If (9Jt, x) b p then we say p is false at the world x in 9Jt. Instead of (9Jt, x) \= p 
and (SDt,x) ^we will write simply x \= <p and x b <p, if understood. The 
truth-set of </? in 3DT is denoted by %J{p). 
The definitions of satisfiability, truth, refutability and validity in modal frames 
and also those of isomorphism between frames and models remain the same as 
in Section 2.2. Propositions 2.2 and 2.3 can be transferred without any changes 
to the modal case as well. 
Proposition 2.3, stating that the truth-value of a formula depends only on the 
truth-values of its variables, can be somewhat strengthened by observing that if 
a formula p contains at most n nested modalities then the truth-value of p at a 
point x depends only on the truth-values of its variables at the points accessible 
from x by at most n steps. To formulate this more precisely, we require a few 
definitions. 
The modal degree md(p) of a formula p is defined inductively: 
md(p) =0, for every atomic p\ 
md(ip O x) = max{md(^), md(x)}, for O £ {A, V, —►}; 
md{Urp) = md(O^) = md(ip) 4-1. 
We denote by Unp and Onp the formulas U.. .Up and O. ..Op, respectively; 
n n 
by the definition, both U°p and O°p are just p. Thus, if p contains no modal 
operators at all then md(Unp) = md(Onp) = n. 
Let # = (W,R) be a frame and x,y £ W. Say that y is accessible from x by 
n > 0 steps and write xRny or y e x\n or x £ y[n if there exist (not necessarily 
distinct) points zi, ■.., zn-\ in W such that xRz\Rz2... Rzn-\Ry. We shall also 
understand xR°y, y e xt° and x £ y[0 as x = y. If R is transitive then clearly 
xRny implies xRy, for every n > 0, and if R is also reflexive then the converse 
holds as well. A point x is called reflexive if xRx\ for such an x, xRnx holds 
for every n > 0. A frame is (ir)reflexive if all points in it are (ir)reflexive. A 
frame $ = (W, R) is said to be intransitive if Vx, y, z (xRy A yRz —► -*xRz). An 
intransitive frame is clearly irreflexive. 
It is not difficult to see that the definition of the truth-relation for the modal 
operators can be generalized as follows: 
Proposition 3.1 For every n > 0, 
(m, x) b iff (m, y) b ^ for all y e xf1, 
(9Jt, x) b iff (9Jt, y) \= ip for some y e x\n. 
It follows that if xRny does not hold for any point y in a frame #, i.e., 
x\n— 0, then (#,x) b and (5,^) b for every formula p. In particular, 
“everything is necessary” and “nothing is possible” at a point without successors. 
Such a point is called a dead end. 
The notions of subframe and submodel are defined as in the intuitionistic case. 
Each non-empty set X of points in a frame $ determines in the unique way the 

66 
MODAL LOGICS 
P, Op 
Up • Up —> p 
a Dp —> Op 
Fig. 3.1. 
□p —► p p, Dp 
□(□p p) ° □(□p -> p) -► op 
(a) 
Fig. 3.2. 
subframe of # and the submodel of 97t = (#,93) with the set of worlds X; they 
are called the subframe and the submodel induced by X. 
Proposition 3.2 Let 97t be a model, x a point in 97t, n > 0 and 91 the sumbodel 
of DJI induced by the set x|° U .. .Ux]n. Then, for every formula <p with md(<p) < 
n, 
(DJI, x)\f=ip iff (91, x) |= <p. 
Proof By induction on the construction of ip with md(ip) < n. The basis of 
induction and the cases of <p = %p Q x, for 0 G {A, V, —>}, are trivial. 
Suppose that ip = Uip. Then (DJI, x) b iff there is y in DJI such that y £ x\ 
and (DJI, y) b On the other hand, (91, x) b iff there is y in 91 such that 
y £ x T and (91, y) b Construct the submodel 91' of DJI (or 91) induced by 
the set 2/t° U... U t/Tn_1- Since md(xp) < n — 1, by the induction hypothesis 
we have (971, y) b ^ iff (91', y) b ^ iff (91,?/) b Therefore, (971, x) b iff 
(9l,x) b°^- □ 
Drawing a frame # = (W, ii) in the form of diagram, we will represent irreflex- 
ive points in # by bullets • and reflexive ones by circles o (in the intuitionistic 
frames all points were reflexive). We draw an arrow from x to y if x b V and 
xRy. Unless otherwise stated, the frames represented by diagrams are assumed 
to be transitive. In such cases we do not draw an arrow from x to z if there are 
arrows from x to y and from y to z. In the diagrams of nontransitive frames all 
arrows are shown explicitly. 
When depicting models, alongside their points we shall sometimes write 
formulas: those that are true at a point are written to the left of it and those that 
are false to the right. 
Example 3.3 Let # = (W, R) be the frame consisting of a single irreflexive point 
a, i.e., W = {a}, R = 0, and let 93(p) = 0. Then both Up —> p and Up —► Op are 
false at a under 93, since a b DP> a b P and a b Op. This situation is shown 
graphically in Fig. 3.1. 
v 
• p 
(b) 

MODAL FRAMES AND MODELS 
67 
c 
r 
I &n 
p i Dp 
p I DOp 
□p * Dp —> DOp 
nontransitive 
Fig. 3.3. 
Example 3.4 Suppose now that # = (W, R) consists of a single reflexive point 
a, i.e., W = {a}, R = {(a, a)}, and let again DJ(p) = 0. Then the formulas 
dp —> p and Dp —> Op are true at a under 2J, while the formula 
la = □(□p —> p) —> Dp, 
known as the Lob formula (or axiom), is false (see Fig. 3.2 (a)), la is false also 
at every point in the (transitive) model shown in Fig. 3.2 (b) and consisting of 
a strictly ascending chain of irreflexive points. (The definition of ascending and 
descending chains remains the same as in the intuitionistic case.) 
Example 3.5 Now consider the intransitive frame # = (W,R) in Fig. 3.3, i.e., 
W = {a,b,c}, R = {(a,b), (b,c)} (a does not see c!), and put, as shown in 
Fig. 3.3, 2J(p) = {a, 6}. Then it is easy to see that the formula Up —> UUp is 
false at a. Notice that by replacing • in Fig. 3.3 with o, i.e., by taking R = 
{(a, b), (b, c), (a, a), (b, b), (c, c)} we again obtain a countermodel for that formula. 
However, this will not be the case if we take the transitive closure of the depicted 
accessibilities. For then we shall have aRc from which a 
An important property of models built upon transitive frames is the following: 
Proposition 3.6 Suppose 9JT is a model on a transitive frame. Then for every 
point x in DJI and every formula <p, 
(i) (DJl,x) |= Uip implies (DJl,y) f= U<p, for every y e x\; 
(ii) (DJl,x) |= 0(p implies (DJl,y) f= Oip, for every y € x[. 
Proof (i) If we assume that (DJI, y) \f=- U(p for some y e x\ then there is z G y\ 
such that (DJI, z) (p. Since # is transitive, we must then have z £ x\, contrary 
to x |= Up. 
(ii) 	is proved analogously. □ 
It follows that in a transitive model exactly the same formulas of the form 
□(p or Op are true at the points which see each other. We introduce for such 
points a special terminology. 
Let # = (W, R) be a transitive frame. Define on W an equivalence relation 
~ by taking, for every x,y eW, 
x rsj y iff either x = y or xRy and yRx. 

68 
MODAL LOGICS 
The equivalence classes with respect to ~ are called clusters. The cluster 
containing a point x will be denoted by C(x). In other words, C(x) contains x and 
all those points in # that are seen from x and see x themselves. 
Proposition 3.7 Suppose x is a point in a model 9JT built on a transitive frame 
and ip an arbitrary formula. Then for every y € C(x), 
{<m,x)\=ntpiff(im,y)\=n<p, 
(fm,x)\=o<piff(m,y)\=o<p. 
Proof Follows from Proposition 3.6. □ 
The quotient frame of a transitive frame # with respect to that is the 
frame (W/^,R/~), where 
W/„ = {C(x) : xeW} 
and 
C(x)R/~C(y) iff xRy, 
is called the skeleton of # and denoted by p$ = {pW, pR). It should be clear 
that the skeleton p$ of every frame # is antisymmetric, and if R is reflexive then 
p$ is partially ordered by pR. A reflexive and transitive binary relation is called 
a quasi-order (or preorder). 
We distinguish three types of clusters: 
• a degenerate cluster consisting of a single irreflexive point, 
• a simple cluster consisting of a single reflexive point, and 
• a proper cluster containing at least two (reflexive) points. 
We will represent a proper n-point cluster, for 2 < n < lj, as ® or as shown in 
Fig. 3.4 (a). Fig. 3.4 (b) and (c) show a frame with all these types of clusters 
and its skeleton, respectively. 
Example 3.8 Let $ = (W, R) be the frame shown in Fig. 3.5, i.e., W = {ai, 02}, 
R = {(ai,aj) : «, j = 1,2}, and let 2J(p) = {ui}. Then the formula 
ma = DO p —► OQp, 
known as the McKinsey formula (or axiom), is false under 9J at both a\ and 02- 

TRUTH-PRESERVING OPERATIONS 
69 
o 
di 
□p 
O Dp 
Op 
□ Op 
Fig. 3.5. 
nontransitive 
Fig. 3.6. 
And finally, we define the modal logic Kmc in the language MC as the set 
of all Af£-formulas that are valid in all modal Kripke frames, i.e., 
Kmc = {v € For At £ : # |= <p, fc>r all frames $}. 
As before, we drop the subscript MC and write, when understood, simply K. It 
follows from the given definition that 
Clc C Kmc- 
Once again we emphasize that the operator □ in K should not be understood as 
some meaningful necessity. From the set-theoretic point of view K is the minimal 
logic among all those modal logics that are considered in this book. In Section 3.8 
we shall construct modal logics for various meaningful interpretations of □ by 
adding new formulas to K which convey specific traits of these interpretations. 
3.3 	Truth-preserving operations 
The definitions of the truth-preserving operations—generating subframes, 
reduction and disjoint union—which were introduced in Section 2.3 may be used 
without any changes in the modal case as well. To refresh them in mind, we just give 
some examples displaying specific features of modal frames. 

70 
MODAL LOGICS 
Example 3.9 Let us consider once again the intransitive frame in Fig. 3.3. We 
have: a\— {&}, although the upward closure of {a}—the minimal set to contain 
a and all successors of its points—is {a, 6, c}; aj,= 0. 
This example shows that | and | are not upward and downward closure 
operations in nontransitive or irreflexive frames. So we generalize them as follows. 
For a frame = (W, R) and X C W, we put 
xr= U *tn> x^>= U x^> 
n> 1 n> 1 
xf = X U X = X U for 1 < £ < u. 
Using this notation, we can now represent the upward closed set generated by 
X in $ as X]^. A point a; is a root of $ if the subframe of # generated by x 
is $ itself. Notice also that the cluster C(x) generated by a point x is x]_ D x[. 
If $ is transitive, we say x is a final point and C(x) a final cluster in X if 
rcj n X = C(x) D X\ x is a last point and C(x) the last cluster in X if X C 
A set X C W is called a cover for a set Y C W if Y C X[. 
Example 3.10 Let ^ = (W, R) be the (nontransitive) frame depicted in Fig. 3.6 
(a). # is generated by a as well as by 6; so is rooted, with both a and b being 
its roots. All rooted subframes of $ (modulo isomorphism) are of the form shown 
in Fig. 3.6 (a)-(f), for n > 0. The disjoint union of (e) and (f) gives an example 
of S’s subframe without a root. The frames (a) and (b) are the only generated 
subframes of Sr. 
Theorem 3.11. (Generation) If $1 is a generated submodel of DJI then, for 
every point x in DX and every modal formula (p, 
(9t,x) 1= ip iff(m,x) 1= p. 
Proof We leave the proof, which is similar to that of Theorem 2.7 or 
Proposition 3.2, to the reader as an exercise. □ 
Corollary 3.12 If (3 C £ then, for every x in 3 and every formula <p, 
(i) (6,x) |= p iff ($, x) |= p; 
(ii) implies <5 \= (p. 
Corollary 3.13 K = {<p € ForMC :#)=</? for all rooted frames $}. 
Example 3.14 The transitive irreflexive frame shown in Fig. 3.7 (a) is reduced 
to the frame (b) by the map /(n) = mod2(n) and to the frame (c) by the map 
g(n) = 0, for all n. However, if we do not presuppose taking the transitive closure, 
then (a) is not reducible to (b), but is reducible to (c). It is worth noting also 
that, by (Rl), no reflexive point can be mapped by a reduction to an irreflexive 
one. 

TRUTH-PRESERVING OPERATIONS 
71 
• 2 
, 
fo o') 
0 
in 
\0 V 
0 
(a) 
(b) 
(c) 
Fig. 3.7. 
Theorem 3.15. (Reduction) If f is a reduction of a model 9JT to a model 
then, for every point x in Wl and every formula ip, 
(m, x) \= <p iff (m, f(x)) (= ip. 
Proof Similar to the proof of Theorem 2.15. □ 
Corollary 3.16 If f is a reduction of ^ to 3 then, for every point x in $ and 
every modal formula (p, 
(i) ($,x) |= p implies {<3,f{x)) (= <p; 
(ii) # |= ip implies 3 f= ip. 
Propositions 2.11, 2.13 and 2.14 remain true for the modal case as well. 
Proposition 3.17 If a modal formula ip is valid in some frame then it is also 
valid either in o or in •. 
Proof Suppose $ \= ip. If $ contains a dead end, say x, then {{x}, 0), i.e. •, is a 
generated subframe of $ which, by Corollary 3.12, validates tp. Otherwise every 
point in $ has a successor and so the map / defined by 
f(x) = o, for all points x in #, 
is a reduction of $ to the frame o. By Corollary 3.16, this means that o validates 
<p. □ 
A modal frame # = (W,R) is called a tree if the reflexive and transitive 
closure R* of R (i.e., for every x,y € W, xR*y iff y € x]^) is a tree partial 
order on W. For instance, the frames in Fig. 3.6 (b), (c), (e) and (f) are trees, 
while those in (a) and (d) are not, since both of them contain a proper cluster. A 
transitive frame $ is a tree of clusters (or quasi-tree) if its skeleton p# is a tree. 
Slightly modifying the proof of Theorem 2.19 we obtain 
Theorem 3.18 Every rooted modal frame 3 = (V,S) is a reduct of some 
intransitive tree. 
Proof Suppose vo is a root of 3. Define a set W and a relation R on W by 
taking 
W = {(v0jvi,...,vn-i,vn) : v0SviS ...Svn-iSvn}, 

72 
MODAL LOGICS 
1 
1 
(a) 
(b) 
Fig. 3.8. 
(v0, ...,vn)R (uo, • • • 5 um) iff m = n + 1 and for i = 0,..., n. 
Clearly # = (W,R) is an intransitive frame with root (vo)- Moreover, $ is a 
tree, since (vo, v\,..., vn) is finite and linearly ordered by the transitive and 
reflexive closure of R as follows: 
(vo) R(vo,vi)R...R(vo,vi,.. .,vn-i)R(vo,Vi,... ,vn_i,t;n). 
We leave to the reader to verify that the map / from W onto V defined by 
f((vo, vi,..., vn)) = vn is a reduction of # to 3. □ 
Corollary 3.19 K = {<p € ForAf£ : |= (p for all intransitive trees #}. 
Unlike the intuitionistic case, the tree $ constructed in the proof above may 
be infinite even if 3 is finite. For example, suppose (3 consists of only one reflexive 
point; then # will have the form shown in Fig. 3.7 (a). However, for finite (3, 
every point in the corresponding tree # has finitely many successors. 
The tree $ constructed in the proofs of Theorems 3.18 and 2.19 is said to 
be obtained by unravelling (3. To “unravel” a transitive frame (3 without loss 
of transitivity, we should take the transitive closure of R in Sr. There is also 
another technique of “flattening out” clusters in a transitive (3, which is known 
as bulldozing (3: roughly, each non-degenerate cluster in (3 is “bulldozed” into an 
infinite ascending chain of irreflexive points. Recall that an irreflexive transitive 
binary relation is called a strict partial order. More exactly bulldozing is defined 
in the proof of the following: 
Theorem 3.20. (Bulldozer) (i) Every transitive frame is a reduct of some 
strictly partially ordered frame. 
(ii) Every quasi-ordered frame is a reduct of some partially ordered frame. 
Proof (i) Suppose 3 = (V, S) is a transitive frame. With each point x € V we 
associate a set which is {(#, i) : i = 0,1,...} if C(x) is non-degenerate and 
the singleton {(x,0)} if C(x) is degenerate. Let W be the union of all x+. Fix 
some well-ordering #o, #i, of every cluster C in 0 and define a relation 
R on W by taking 
{x£,i) R (x£,j) iff either i < j or £ < £ and i = j 

HINTIKKA SYSTEMS 
73 
to 
□ (□p —► q) V □ (□<? —► p) 
n(D^ -+P) 
Fig. 3.9. 
if C(x^) = C(x$) and, for distinct C(x) and C(y), 
(x,i) R (y,j) iff xSy. 
It is easy to see that R is transitive and irreflexive, i.e., it is a strict partial order. 
We show that (3 is a reduct of $ = {W,R). 
Define a map / from W onto V by taking /({#, i)) = £, for every (x, i) € W. 
By the definition, / is a map “onto” satisfying (Rl). Suppose now that xSy. 
If C(x) = C(y) then (x,i) R(y,i 4-1), for every i > 0. And if x and y are in 
distinct clusters then (x,i) R{y,j) for all possible i and j. Thus / satisfies (R2) 
and so is a reduction of ^ to (3. 
(ii) 	The only difference from (i) is that in the definition of R we take < 
instead of <. □ 
Observe, however, that the result of bulldozing is not in general a tree. For 
instance, by bulldozing the frame in Fig. 3.8 (a), we obtain the frame in Fig. 3.8 
(b), which is not a tree, since an infinite ascending chain precedes its last point. 
The disjoint union of modal frames behaves exactly like the disjoint union of 
intuitionistic ones. 
3.4 	Hintikka systems 
In this section we extend the semantic tableau method to the modal case. As 
before, this method will not only provide us with a convenient tool for 
constructing countermodels but also help us proving the completeness theorem for 
the calculus K in Section 3.6. Again we begin with a few examples. 
Example 3.21 Suppose that we want to construct a countermodel for the 
formula 
sc = □(□ p —► q) V □(□# —► p). 

74 
MODAL LOGICS 
□ (□(p —> Dp) —» p) 
_*0 
□ (□(p —> Dp) —> p) p 
V 
to 
• P 
(a) 
Fig. 3.10. 
(b) 
Then we form the tableau to = (0, {sc}). Its purpose is, as before, to describe the 
desirable distribution of the truth-values over (some) subformulas of sc in one 
world of the model to be constructed. By the saturation rule (SR4), we should 
add D(Dp —» q) and □ (□<? —» p) to the right part of to. Recall now that a formula 
is false at a point x iff there is a point y accessible from x at which xft is false. 
So we form two new tableaux t\ and £2 and put to their right parts Dp —» q and 
Uq —► p, respectively; we regard these tableaux as accessible from to- The only 
thing that is left to do is to apply to ti and £2 rule (SR6), which again is correct, 
since —> is classical. All steps of this construction are shown in Fig. 3.9 (a). 
It is not hard to check that sc is refuted at the point to in the model shown 
in Fig. 3.9 (b). Nothing prevents us from joining t\ and t2 into one tableau, say 
t, and then we obtain another countermodel for sc which is depicted in Fig. 3.9 
(c). Observe that if we need a reflexive countermodel for sc then we must add 
p and q to the left parts of ti and t2, respectively. However, this does not go 
through for the countermodel in Fig. 3.9 (c). 
Example 3.22 Now let us use this method of constructing countermodels for 
the formula 
grz = □(□(p —> Dp) —> p) —> p 
which is known as the Grzegorczyk formula (or axiom). Only one application 
of rule (SR6) (see Fig. 3.10 (a)) yields the simplest countermodel for grz built 
upon the single-point irreflexive frame shown in Fig. 3.10 (b). 
Example 3.23 Suppose, however, that we are interested only in reflexive 
countermodels for grz. In this case to in Fig. 3.10 must be self-accessible, and so 
we should put □ (p —> Dp) —> p to its left part, which completely changes the 
matter. Indeed, after that we, in accordance with (SR5), put D(p —» dp) to the 
right part of to and then, to make this formula false at to, form a new tableau 
ti which is accessible from to and contains p —> Dp in its right part. So p should 
be added to the left part of ti and Dp to the right one. But that is not enough: 
to ensure that □ (□(p —> Dp) —> p) is true at to, we must put D(p —> Dp) —> p to 
the left part of t\. 
Our next step is to form a tableau t2 accessible from ti and put p in its right 
part, which guarantees the falsity of Dp at ti. Notice that to does not see t2. All 
these steps are shown in Fig. 3.11 (a). The reflexive nontransitive countermodel 
for grz corresponding to this tableau system is depicted in Fig. 3.11 (b). 

HINTIKKA SYSTEMS 
75 
to 
□ Dp) ->p) 
□ Dp) -tp) ->p 
□ (p —> Dp) —► p 
P 
□(P °P) 
t\ 
p —> Dp 
V 
□p 
□ (p —► Dp) —> p 
p o 
IV 
(a) (b) 
Fig. 3.11. 
Example 3.24 Now suppose that we need a reflexive and transitive (i.e., quasi- 
ordered) countermodel for grz. Then we should take the transitive closure of 
the accessibility relation between t0) h and t2 in Fig. 3.11 and so, according to 
Proposition 3.6, copy the left part of to to the left parts of t\ and t2. But then, 
by (SR5), D(p —► Dp) should be written in the right part of t2, which actually 
returns us to the same situation as was in to. Thus we obtain an infinite sequence 
of tableaux to —► t\ —3' t2 —> ..., in which t2i is a copy of to and t2*+1 a copy of 
ti, for i = 1,2,— The reflexive and transitive countermodel corresponding to 
this tableau system is depicted in Fig. 3.12 (a). 
We can avoid the infinite chain of alternating tableaux if instead of 
constructing t2 we just draw an arrow from t\ to to, thus getting a system of two tableaux 
seeing each other. The corresponding countermodel is shown in Fig. 3.12 (b). 
Observe that the map /(t») = £mod2(i) is a reduction of the model (a) to the 
model (b). 
Now we present these considerations in a more formal way. A tableau in the 
language MC is any pair t = (T, A) of subsets of ForMC. It is saturated if 
conditions (S1)-(S6) in Section 1.2 are satisfied; t is disjoint if T n A = 0 and 
-L*T. 
A Hintikka system in K is a pair 9) = (T, 5), where T is a non-empty set of 
disjoint saturated tableaux and S a binary relation on T satisfying the following 
two conditions: 
(HSmI) if t = (T, A), tf = (T', A') and tStf then € Tf for every □ € T; 

76 
MODAL LOGICS 
p o 
6 p 
p o 
P 
a) 
Fig. 3.12. 
(HSm2) if t = (I\A) and Dtp e A then there is t* — (T', A') in T such 
that tSt' and ip € A'. 
Say that Sy is a Hintikka system for a tableau t if t C tf for some tf in Sy. 
A tableau (T, A) is realized in (a point x of) a model 9JT if (9JT, x) |= ip, for 
every (p € T, and (971, x) tp, for every xp € A. A tableau t is called realizable in 
K if it is realized in some model. 
In the same way as was done in the proof of Proposition 2.31, given a Hintikka 
system Sy, one can construct a model based on the frame Sy in which every point 
t realizes the tableau t and conversely, given a model 971 realizing t, one can 
construct a Hintikka system for t. Thereby we obtain 
Proposition 3.25 A tableau t is realizable in K iff there is a Hintikka system 
for t. 
Corollary 3.26 If Sy is a Hintikka system for (0, {</?}) then Sy ip. 
To construct a Hintikka system for a tableau t, we can deal only with 
subformulas of formulas contained in t. This observation gives an upper bound for 
the number of tableaux in a minimal Hintikka system for t. 
Theorem 3.27 A tableau t is realizable in K iff there is a Hintikka system for 
t containing at most 2^ tableaux, where E is the set of all subformulas of the 
formulas in t. 
Proof (=>) Suppose t is realized in 9Jt = (#, 93). For every point x in the frame 
$ = (W,R), we form a tableau tx = (T^, A^) by taking 
r® = {<P € £ : % \= Az = {(p e E : x \f=- ip}. 
Let Sy = (T, 5), where T = {tx : x € W] and, for every tx = (1^, A^) and 
ty = (Ty, Ay) U1 T, 
txSty iff Dip € rx implies ip € for all Dip £ E. 
This definition guarantees that (HS^T) is satisfied. We show that (HSm2) also 
holds. 

MODAL FRAMES AND FORMULAS 
77 
Let tx = {TX,AX) and Up e Ax. Then (9JI,x) Dip and so there is a point 
y e W such that xRy and (9Jt, y) \f=- p. By the definition of f=, y f= *0 whenever 
x |= So txSty and y? belongs to the right part of ty. 
Thus, S) is a Hintikka system for t. It is also clear that the number of tableaux 
in T does not exceed the number of subsets in £. 
(<^=) follows from Proposition 3.25. □ 
Corollary 3.28 (i) For every formula p K there is a rooted frame refuting <p 
and containing at most 2^ub¥?l points. 
(ii) Every (p £ K is refuted in some finite intransitive tree. 
Proof (i) follows from Theorem 3.27, since (0, {<^}) is realizable in K. 
(ii) 	Take a finite frame ft refuting p and apply to it the unravelling procedure 
described in the proof of Theorem 3.18, thus obtaining an intransitive tree # = 
('W,R) which is reducible to 9) and so, by the reduction theorem, refutes p. 
Although # may be infinite, every point in it has finitely many successors. 
Suppose md(p) = n and DJt = (#,21) is a model such that (9Jt, x) \f=- p, for 
some point x. By Proposition 3.2, the submodel 21 of 9Jt, induced by the set 
xf0 U ... U x]n, also refutes p. It remains to notice that 21 is based upon a finite 
intransitive tree. □ 
Corollary 3.29 
K = {p G ForMC : # |= p for all finite intransitive trees #}. 
So, by applying saturation rules (SR1)-(SR6) to each individual tableau and 
also rules 
(SRm?) if t = (r, A) and Up e T then add p to the left part of every t' 
such that tSt'\ 
(SRm8) if t = (r, A) and Up e A then either add p to the right part of 
some tableau accessible from t or form a new tableau t' = (r', A') 
by taking T' = {*0 : U%j) e T}, A' = {p} and put tStf 
we can always construct a finite Hintikka system for each finite realizable tableau. 
As an easy exercise we invite the reader to show that all the formulas in 
Table 3.1 are in K. 
3.5 	Modal frames and formulas 
Having got some experience in constructing countermodels, let us try now to find 
characterizations of frames validating a number of important modal formulas we 
shall deal with in the sequel. 
First we observe that Example 3.3 suggests the following: 
Proposition 3.30 A frame # validates Up —► p iff $ is reflexive. 
Proof If # = (W,R) is not reflexive then ->xRx, for some x G W. So we can 
put 2J(p) = W — {x}, which gives us x f= Up and x ^ p, whence x ^ Up —► p. 

78 
MODAL LOGICS 
Table 3.1 A list of modal formulas in K 
□m(pi A ... A pn)^> Dmpi A ... A Dmpn, 
Om(pi v ... Vpn) <-> Ompi V ... V Ompn, 
□mPi v... v Dmpn -+ nm(p! v... vpn), 
Om(pi A ... Apn) -> Ompi A ... A Ompn, 
□m(p -> g) -> (nmp -> nmg), 
□m(p -►«)-► (Omp -4 0"*«), 
nmp A Omq Om(p A q), 
□ n_L nmjL^ 
OmT -+ OnT, 
T «-> DmT, 
j_ ^ <>mJ_, 
(□Op —► ODp) <-» 0(0p —► Dp) 
for n > 0, m > 0 
for n > 0, m > 0 
for n > 0, m > 0 
for n > 0, m > 0 
for m > 0 
for m > 0 
for m > 0 
for m > n 
for m > n 
for m > 0 
for m > 0 
Conversely, if 5 is reflexive then 5 |= Dp —> p, for otherwise there is a model VJl 
on 5 such that (3D%x) |= Up and (3Dt,x) ^ P, for some x e W; but since xRx, 
we must also have (3DT, a?) |= p, which is a contradiction. □ 
Likewise, Example 3.5 suggests 
Proposition 3.31 5 validates Dp —► DDp ijf$ is transitive. 
Proof Exercise. □ 
We will denote the formulas Dp —► p and Dp —► DDp by re and tra, 
respectively. 
Let us consider now the formula p —► DOp and suppose that 3DT = (5,21) is 
a countermodel for it based on a frame 5 = (W,R). Then x \= p and x ^ DOp, 
for some £ G W, and so there is a successor y of x such that y ^ Op. Observe 
also that x\= p and p Op imply -iyRx. 
Thus, a necessary condition for 5 P —>> OOp is 3x, y(xRy A -<yRx) and so 
a sufficient condition for the validity of p —► DOp in 5 is 
Vx,p (xRy —► pita). 
A frame 5 satisfying this condition is called symmetric. 
Proposition 3.32 5 validates sym = p —> DOp ijf$ is symmetric. 
Proof Only (=») requires a proof. If 5 = (W, i?) is not symmetric then there 
are x,p G W such that xi7p and -iyRx. Define a valuation 2J in 5 by taking 
2J(p) = {x}. Then we have x f= p, y Op, whence x DOp and x P —► OOp. 
□ 

MODAL FRAMES AND FORMULAS 
79 
Our next example is the formula Dp —► Op. Let 9JI = (#, 9J) be its 
countermodel on a frame # = (W, R). Then x \—Up and x ^ Op for some x G W. The 
only conclusion we can derive from this piece of information is that x is a dead 
end in #, for if xRy for some y G W then y \= p and y ^ p, which is a 
contradiction. Therefore, a necessary condition for # ^ Up —► Op is 3xsiy-^xRy. And a 
sufficient condition for $ |= ^P —► Op is then the seriality condition \/x3y xRy. 
Proposition 3.33 $ validates ser = Dp —► Op iff # is serial. 
Proof Exercise. □ 
Let us consider now the family of formulas of the form 
9aklmn = Okalp^DmOnp, 
where fc, Z, m, n are arbitrary natural numbers, possibly equal to 0. All formulas 
we have already dealt with in this section are in this family. 
Suppose Wl = (#, 9J) is a countermodel for OkDlp —► □mOnp, i.e., x |= OkUlp 
and x □mOnp for some x in $ = (W, R). By Proposition 3.1, there are y,z eW 
such that xRky, y f= nlP and xRmz, z Y=- Onp. Notice also that y |= Dlp and 
z Y=- ^nP tell us that there is no point u in # which is accessible from y by l steps 
and from z by n steps. These observations lead to the following 
Proposition 3.34 # = (VF, R) validates 9dkimn iff 
Vx, p, z (xRky A xRmz —► 3u (yRlu A zRnu)). 
Proof Again, only (=») requires a proof. Suppose otherwise. Then there are 
x,y,z G W such that xRky, xRmz and for every u G VF, either -iyRlu or 
-i.zRnu. Define a valuation in $ by taking 2J(p) = {v G W : yRlv} and show 
that x |= OkDlp and x ^ □mOnp. Indeed, by Proposition 3.1, y \= Ulp and, 
since there is no point u G W for which u \= p and zRnu, we have z Y= ^nP, 
whence x |= OkDlp and x □mOnp. □ 
Even more extensive families of formulas can be found in Exercise 3.22 and 
Section 10.3. Propositions 3.30-3.33 are just special cases of Proposition 3.34. 
Here are a few more useful consequences. 
Call a frame # = (VF, R) n-transitive if 
Vx, y {xRnJrly —► xRy V xR?y V ... V xRny), 
which is read: if it is possible to reach y from xby n+1 steps then one can do this 
by < n steps as well. 1-transitivity is nothing else but the standard transitivity. 
Corollary 3.35 # validates tran = Ar=o ^P ~* °n+1P iff'S is n-transitive. 
A frame $ = (W, R) is said to be dense if Vx, y \xRy —► xR2y). More generally, 
# is n-dense if Vx, p (xRny —► xRn+1p). 

80 
MODAL LOGICS 
Corollary 3.36 $ validates denn = □ n+1p —► nnp iff$ is n-dense. 
A frame $ is called Euclidean if Vx, y, z (xRp A xRz —► yRz). 
Corollary 3.37 validates euc = ODp -h► Dp iff$ is Euclidean. 
Corollary 3.38 # [= ODp —> DOp «jff # is strongly directed. 
Thus, the formula 
ga = OUp —> DOp, 
known as the Geach formula (or axiom), is similar to the weak law of the 
excluded middle in Int. However, this analogy is not completely perfect. For 
reflexive frames the condition of strong directedness is equivalent to the directedness 
condition 
\/x, y, z (xRy A xRz Ay^z-> 3u(yRu A zRu)), 
which in general is weaker. For example, the two-point irreflexive frame is 
directed but not strongly directed. 
A simple modification dir = O(DpAg) —> □(OpVg) of ga is valid in directed 
frames and only in them. 
Proposition 3.39 $ |= dir iff$ is directed. 
Proof Exercise. □ 
A similar situation is with the condition of strong connectedness, which in 
the intuitionistic case corresponds to da. 
Proposition 3.40 $ validates sc = □(□p —► q) V □(□# —j► p) iff $ is strongly 
connected. 
Proof Exercise. □ 
For reflexive frames the condition of strong connectedness is equivalent to 
that of connectedness 
Wx, y, z (xRy A xRz A y ^ z —> yRz V zRy), 
which is weaker in general. 
Proposition 3.41 # validates con = D(p A Dp —> q) V D(q A Dq —> p) iff $ is 
connected. 
Proof Exercise. □ 
The connectedness of a frame means that no point in it has two distinct 
successors which do not see each other. Let, for n > 1, 
n 
bwn = A Opt -> V 0(pi A (pj V Opj)). 
i—0 0<i^j<n 

MODAL FRAMES AND FORMULAS 
81 
Proposition 3.42 # validates bwn iff each point in $ has at most n successors 
which do not see each other. 
Proof Exercise. □ 
Using the notion of width, defined in Section 2.5, for transitive frames this 
result can be formulated similar to Proposition 2.39. 
Corollary 3.43 A transitive frame $ validates bwn iff every rooted subframe of 
# is of width < n. 
The notion of depth loses its initial meaning when arbitrary modal frames 
are considered, since they may contain circles of the form 
XqRxiR ... RxnRx0. 
However, if we restrict ourselves only to transitive frames then the depth of a 
frame $ can be defined as the depth of its skeleton p$ in the sense of Section 2.5. 
So we say that a transitive frame # = (W, R) is of depth n, d(3r) = n, if there 
is a chain X\Rx2R- -Rxn of points from distinct clusters in # (which means 
that -iXi+iRxi) and there is no chain of greater length satisfying this condition. 
# is of depth oo if, for every n < a;, it contains a chain of n points belonging to 
distinct clusters. 
As modal analogues of the formulas bdn “restricting” the depth of intuition- 
istic frames we can take the modal formulas bdn which are defined as follows: 
bdi = ODpi ->pi, 
frdn+l — ^(^Pn+1 A —ibdn) ► Pn+1* 
Proposition 3.44 A transitive frame $ validates bdn iff d{f$) < n. 
Proof (=») is proved by induction on n. The basis of induction follows from 
Proposition 3.34. Suppose # = (W,R) is of depth n + 1. Then there is a chain 
XqRxiR. .. Rxn of points from distinct clusters in Consider the subframe 
0 = (V,S) of $ generated by x\. Then 0 is of depth n and by the induction 
hypothesis, there is a model = (0,il) such that x\ ^ bdn-\. Without loss of 
generality we may assume that il(pn) = V. Define a valuation on $ by taking 
®(Pn) = W- {x0} and V3(Pi) = lX(pi), for 1 < i < n. Let m = ($, 93). Then W is 
a generated submodel of and, by the generation theorem, (97t,a?i) Y=- bdn-1, 
(931, Xi) |= □ pn, whence (931, xi) |= Upn A -ibdn_i and so (931, xo) |= O(Dpn A 
nMn-i)- It remains to recall that xq ¥=■ Pn, which gives us x0 bdn. 
(^=) An easy induction is left to the reader. □ 
The following formulas are similar to the intfiitionistic formulas bcn bounding 
the cardinality of rooted frames (see Section 2.5): 

82 
MODAL LOGICS 
altn = Dpi V D(pi -► p2) V ... V D(pi A...Apn-> pn+i), ^ > 0. 
However in the modal case frames may be nontransitive, and so altn bounds 
only the number of alternatives of every point in a frame validating it. 
Proposition 3.45 A frame £ = (W, R) validates altn iff each point in $ has at 
most n distinct alternatives, i. e., 
It is much more difficult to characterize frames for the conversion of the 
Geach formula, i.e., for the McKinsey formula ma = DOp —» OUp. We shall get 
a characterization of only transitive frames validating ma. 
Let VJl = (#, 9J) be a countermodel for ma on a transitive frame $ = (W, R)} 
i.e., xo |= and O^P for some xq G W. Then either xo is a dead 
end or there is a point X\ G W accessible from xo and so X\ f= Op, x\ \f=- Dp. 
Hence there are successors X2 and x$ of x\ such that x<i |= p, £3 ^ p. Clearly, 
X2 ^ x3- Since x2 and x$ are accessible from xo, we can apply to them the same 
argument as to X\. As a result we arrive at the following necessary condition for 
the refutability of ma: 
(The case when xq is a dead end is evidently covered by this condition.) Since 
R is transitive, the condition can be somewhat simplified: 
Thus, a sufficient condition for the validity of ma in a transitive $ is the following 
McKinsey condition: 
Proposition 3.46 A transitive frame $ validates ma iff $ satisfies the 
McKinsey condition. 
Proof Only (=») requires a proof. Suppose the McKinsey condition does not 
hold in # = (W, R). Then there is a point x G W such that either it is a dead end 
or every successor of x has its own proper successor. In the former case x ^ ma 
under any valuation in $. So let us consider the latter one. Using transfinite 
induction, we can choose a subset Y of X = x] such that 
Proof Exercise. 
□ 
3 xWy (xRy —► 3 u, v (yRu A yRv Au ^ v)). 
3 x\/y (xRy —► 3 z (yRz Ay ^ z)). 
Vx3y (xRy A Vz (yRz —► y = 2)), 
which can be read as: each point in # sees a final simple cluster. 
Vu G X3v G Y3w G X — Y(uRv A uRw). 

CALCULUS K 
83 
Define a valuation 2J in 5 by taking 2J(p) = Y. By the choice of Y, we must 
have u \= Op and u ft Dp, for all u G X, whence x f= DOp and x ft OUp, i.e., 
x OOp —► ODp. □ 
Now let us consider once again the Lob formula 
la = D(Dp —i► p) —)► Dp. 
Suppose 9Jt = (5,21) is a countermodel for la based on a frame 5 = (W, R), i.e., 
there is x G W such that x |= □(□p —> p) and x ft Op. Then there exists a 
successor y of x for which y ft p, y 1= Op —► p, and hence p ft Op. So we must 
have a successor z of y such that z ft p. (We emphasize that the points x, p, z 
are not necessarily distinct.) If x does not see z, then all we can say about 5 is 
that it is not transitive. But if 5 is transitive then z 1= Op —► p, whence z ^ Dp, 
and we can apply to z the same argument as to p. 
Thus, a necessary condition for $ ft la is the nontransitivity of 5 or the 
existence of an infinite ascending chain xqRx\R... of not necessarily distinct 
points in 5- Taking the negation of this proposition, we obtain a sufficient 
condition for the validity of la in 5* 5 must be transitive, irreflexive and contain 
no infinite ascending chains. A frame without infinite strictly ascending chains 
is called Noetherian. 
Proposition 3.47 A frame validates la iff it is a Noetherian strict partial order. 
Proof Exercise. □ 
It is worth noting that unlike the other properties we met in this section, the 
absence of infinite ascending chains cannot be expressed by a first order condition 
on the accessibility relation. For details see Section 6.2. 
We recommend the reader to analyze (using Examples 3.22-3.24) the 
constitution of countermodels for the Grzegorczyk formula and prove the following: 
Proposition 3.48 A frame validates grz iff it is a Noetherian partial order, 
i.e., iff it is reflexive, transitive, antisymmetric and contains no infinite ascending 
chains of distinct points. 
Proof Exercise. □ 
3.6 	Calculus K 
The modal propositional calculus K in the language MC, which, as will be shown 
in this section, is sound and complete with respect to the possible world 
semantics, has the following axioms and inference rules. 
Axioms: (A1)-(A10) of Cl (see Section 1.3) and one more proper modal 
axiom 
(All) D(po -► Pi) -► (dpo - Dpi); 
Inference Rules: modus ponens (MP), substitution (Subst) of modal 
formulas instead of variables and the rule of 

84 
MODAL LOGICS 
Necessitation (RN): given a formula </?, we infer Dip. 
The definition of derivation in K is analogous to that in Cl and Int; the only 
difference is that now we have more axioms and inference rules. The fact of 
derivability of a formula ip in K is denoted by bk P- 
Example 3.49 Let us show that, for every formulas ip and ip, 
b# tp ip implies \~k 
We have: 
hit <p —*► 
(given) 
hK n((p 
-*• lj)) 
(by RN) 
1~K CS(<p 
—> ip) ► (Clip —► Clip} 
(from (All)) 
bK °<P - 
-» Clip 
(by MP). 
Example 3.50 Now we show that, for any ip and ip, 
bk ^(p A ip) <-* Dip A Dip. 
Indeed, we have: 
a) 
b k p Alp p 
(from (A3)) 
(2) 
bjc D(ip A ip) —> Dip 
(by Example 3.49) 
(3) 
b k P A xp —► ip 
(from (A4)) 
(4) 
\~K □(</? A ip) —> Dip 
(by Example 3.49) 
(5) 
\-K □ (<£ A ip) —> Dip A Dip 
(from (2), (4)) 
(6) 
\~K P~* pAlp) 
(from (A5)) 
(7) 
\~K Dip —> □('0 ip Alp) 
(by Example 3.49) 
(8) 
\-K □ (ip —> y? A ip) —> (D^ —> 
D(ip A ip)) (from (All)) 
(9) 
b# □<£ —> (D^ —> □ (</? A -0)) 
(from (7), (8)) 
(10) 
b# □</? A Dip —y D(ip A ip) 
(from (9)) 
(11) 
bk □(</? A ip) <-» □<£ A 
(from (5), (10)). 
More generally, by induction on n the reader can readily prove that 
b/c D(Pl A ... A pn) <-> Dipi A ... A Dipn. 
Since Proposition 1.11 on substitutionless derivations is obviously extended 
to K, we can define the notion of derivation from assumptions in K in the same 
manner as in Cl and Int: T \~k p if there is a sequence p\,..., pn such that 
pn = ip and each ipi is either a substitution instance of an axiom of K or an 
assumption in T or obtained by MP or RN from some of the preceding formulas. 
However, the deduction theorem, as it was formulated for Cl and Int, should 
not hold for K if we want K to be sound with respect to the Kripke semantics. 
For by RN, we have p bk But on the other hand, p —> Up is false at the 
point b in the model shown in Fig. 3.3. 
To formulate a modal version of the deduction theorem, we require the 
following definition. Let ipi,..., ipn be a derivation from assumptions. Say that a 

CALCULUS K 
85 
formula ipk depends on a formula <pi in this derivation if either k = i or ipk is 
obtained by MP or RN from formulas, at least one of which depends on <fi. 
Theorem 3.51. (Deduction theorem for K) Suppose F,ip b# ip and there 
exists a derivation of cp from the assumptions ru{^} in which RN is applied to 
formulas depending on ip m>0 times. Then 
rhK dVa... 
Proof The proof is conducted by the same scheme as for Cl: we consider a 
derivation ipi,..., ipn of (p from T U {ip}, in which RN is applied to formulas 
depending on ip m times, and show by induction on i that 
r p# □ °ip a ... a nlip —> <pi, (3.1) 
where l is the number of applications of RN to formulas depending on ip in the 
derivation y?i,..., The cases when cpi is a substitution instance of an axiom or 
belongs to TU {ip} are justified in the same way as in the proof of Theorem 1.12: 
we get T bk ip —> and so (3.1). 
Suppose <pi is obtained from ip^ = <Pj —> <Pi and cpj by MP, and RN is 
applied to formulas depending on ip in <^i,..., cpk and <£i,..., (pj l\ and I2 times, 
respectively. Then, by the induction hypothesis, 
r \-K □ °tp a ... a ahrjj -> (ipj -> ipi), r \-K □> a ... a ni2v> ->■ v, 
and we obtain (3.1), since I1J2 < l- 
Thus, it remains to consider only one case: <pi is obtained from by RN. If 
ipj does not depend on ip then there is a derivation of Oipj from T which clearly 
yields F bk ip —► <Pi and so (3.1). 
Suppose now that cpj depends on ip and RN is applied l\ < l times to formulas 
depending on ip in <^i,..., ipj. By the induction hypothesis, we then have 
ri-x n°ip a ... a —■><pj 
and so, by Examples 3.49 and 3.50, 
r hK □V' a ... a □<i+1v> -> atpj, 
which implies (3.1). □ 
Corollary 3.52 Suppose F,ip b# (p and there exists a derivation of <p from the 
assumptions F U {ip} in which RN is not applied to formulas depending on ip. 
Then F bk ip <p. 
In the sequel we will be distinguishing between derivations in which the rule 
RN is applied exceptionally to formulas that depend only on axioms and 
derivations without this restriction. For the former we shall use the usual “turnstile” 

86 
MODAL LOGICS 
b; the deduction theorem for it is simplified and formulated like that for Cl and 
Int: bk V implies V b# ^ —> ip. The latter kind of derivability will be 
denoted by b*. 
Theorem 3.53. (Soundness and completeness of K) \~k <p iff $ f= ^ for 
all frames #. 
Proof (=^>) All the axioms of K are valid in every frame and the inference rules 
preserve the validity 
(<=) Suppose \/k <p- Our aim is to construct a Hintikka system Si for the 
tableau (0, {</?}). Having succeeded in this, we, by virtue of Corollary 3.26, shall 
establish thereby that S) ^ ip. 
Say that a tableau t = (r, A) is consistent in K if F b# <pi V ... V <pn for no 
y?i,..., <pn G A, n > 0. Since \/k (0, {</?}) is consistent. The tableau t is called 
maximal (relative to ip) if F U A = Sub ip. 
By the same argument as in the proof of Theorem 1.16 we can show that 
every consistent tableau consisting of some subformulas of ip can be extended to 
a maximal consistent tableau satisfying (S1)-(S6). 
Now take the set T of all maximal (relative to ip) consistent tableaux and 
define a binary relation 5 on it by putting, for every t = (r, A) and t' = (T', A') 
in T, 
tStf iff ^ G T' whenever D^eT. 
The condition (HSmI) is satisfied by the definition. So it remains to verify that 
(HSm2) also holds. 
Let t — (T, A) G T and □?/> G A. Consider the tableau t' = (r', {?/>}) 
where T' = {\ : G T}. We show that it is consistent in K. Indeed, 
assuming otherwise, we would have T' bk and so, by the deduction theorem, 
I-~k Xi ^ • A Xn ^ where Xi» • • •»Xn are all distinct formulas in Tf. Then, 
using Examples 3.49 and 3.50, we obtain bk nXi A ... A Dxn —► and 
□Xi > ■ • •, \~k contrary to the consistency of t. Thus, t' is consistent 
and so it is contained in some maximal consistent tableau t" = (r", A") G T. 
By the definition of t', we must then have tSt" and ^ G A". 
Therefore, Si = (T, 5) is a Hintikka system for (0, {</?}), from which S) ^ ip. 
Notice by the way that \T\ < 2lSub<^l. □ 
Corollary 3.54 K = {ip G ForML : ip}. 
By applying the same kind of argument as in the proof of Theorem 3.53 to 
infinite consistent tableaux, one can prove the following theorems (for details see 
Section 5.1). 
Theorem 3.55. (Strong completeness) Every tableau consistent in K is 
realizable. In particular, T bk W iff, for every model and every point x in 9JI, 
(OT, x) |= T implies (9Jt, x) |= ip. 
Theorem 3.56. (Compactness) A tableau is realizable in K iff its every finite 
subtableau is realizable in K. 

BASIC PROPERTIES OF K 
87 
Now we use the completeness theorem for K to obtain an upper bound for 
the parameter m in the deduction theorem. 
Theorem 3.57 Suppose that ty \-*K </?. Then hk ^°ty A ... A Dmty —> where 
m = 2lSub^uSubv?|> 
Proof Suppose otherwise. By Theorem 3.53 and Corollary 3.29, we then have 
a model 9ft = based on a finite intransitive tree # = (W, R) and refuting 
/\™0 —» ip at its root v. With every point x in 9ft we associate the tableau 
tx = (FX,AX) where 
Tx = {x £ Subty U Subp : x |= x}> 
Aj; = {x G Subty U Sub ip : x x}- 
Now construct a new model 9t = on a frame (5 = (V, 5) in the following 
way. V is the set of all points x in # such that for no distinct y, z in the chain 
do we have ty = tz. Let 5" be the restriction of jR to V\ The frame (V, S') 
is clearly an intransitive tree in which every point is accessible from v by < m 
steps and so (9ft, x) (= ty for all x € V\ If x € F has a successor y € W — V then 
there must be a point 2 € xj^ such that ty =tz. In this case we draw an arrow 
from x to z, i.e., add (x, z) to S'. The resulting relation is denoted by S. Finally, 
we define it as the restriction of 9J to V. 
By induction on the construction of x C Subty U Sub</? we show now that, 
for every x £ V, (9ft, x) |= x Iff (9t,x) |= x- The basis of induction and the 
cases of non-modal connectives are trivial. Let x = 1=1X7- If (9ft, x) ^ Dx7 then 
(9ft, y) x' f°r some y € W such that xRy. By the construction, there is a point 
z e V for which tz = ty in 9ft and xSz. By the induction hypothesis, we then 
have (91, z) x', from which (91, x) Ox7- Conversely, assume (91, x) \/= Dx7, 
i.e., (91, y) x! f°r some successor y of x in 91. By the construction of (5, we can 
find then a point z in 9ft such that xRz and ty —tz. Consequently, (9ft, z) ^ x! 
and (9ft, x) Dx7. 
Thus, (91, v) $= tp and, for every x £ V, (91, x) (= ip. So we must have 
(91, v) 0°ty A ... A Onty —* cp 
for every n < u, contrary to the deduction theorem and the soundness of K. 
□ 
3.7 	Basic properties of K 
In this section we mean by a logic any set L of Ad£-formulas containing K and 
closed under MP, Subst and RN. Derivations in L may use any formulas in L as 
axioms. The tabularity, finite approximability and other properties are defined 
for such logics in the same way as for logics in the language C. 
Consistency. K is consistent, since the constant _L is false at every point 
in every model. 

88 
MODAL LOGICS 
Decidability. The decidability of K is proved analogously to the 
decidability of Int using Theorem 3.27. 
Theorem 3.58 K is decidable. 
Tabularity. Since the formulas bwn and altn, defined in Section 3.5, are 
not in K and each frame refuting one of them contains > n points, we have 
Theorem 3.59 K is not tabular. 
Finite approximability. The fact that K is finitely approximable is an 
immediate consequence of Theorem 3.27. 
Theorem 3.60 K is finitely approximable. 
Post completeness. As we shall see later, K has a continuum of proper 
consistent extensions. Here we construct only one of them. 
Theorem 3.61 K is Post incomplete. 
Proof Let L be the smallest set of formulas containing K, the formula m_L and 
closed under MP, Subst and RN. By the definition, m_L is valid in the frame $ 
consisting of a single irreflexive point. And since all formulas in K are also valid 
in $ and the inference rules preserve validity, we obtain $ |= L, which means 
that L is consistent. Thus, L is a proper consistent extension of K. □ 
Theorem 3.62 K is not 0-reducible. 
Proof The formula 
□ (□_L->p) V □(□!-> -np). 
does not belong to K because it is refuted by the frame in Fig. 3.9 (b). On the 
other hand, □(□T —* p>) V □(□T —> -»</?) e K for every variable free formula ip. 
For to refute this substitution instance a frame must contain two dead ends such 
that at one of them <p is true and at another false, which is impossible. □ 
Independent axiomatizability. Since K is finitely axiomatizable, we have 
Theorem 3.63 K is independently axiomatizable. 
Structural completeness. The definitions of admissible and derivable 
rules as well as that of structural completeness remain the same as in Section 1.4. 
It is to be noted, however, that in the modal case we can use RN and so a rule 
(pi,..., vWv? is derivable in a logic L if </?i,..., ipn b-*L <p. Since K is decidable 
and in view of Theorem 3.57, we can always recognize whether a given rule is 
derivable in K. However, it is unknown whether the admissibility problem for 
inference rules in K is decidable. 
Theorem 3.64 K is not structurally complete. 
Proof Consider the rule □_L/-L. Since D_L ^ K, it is admissible in K. On the 
other hand, for any m > 1, the formula □_!_ A... A IHm_L —> _L is not in K because 
it is refuted in the frame consisting of a single irreflexive point. □ 

BASIC PROPERTIES OF K 
89 
All the congruence rules in Section 1.4 are clearly admissible and even 
derivable in K. Example 3.49 establishes in fact the derivability in K of the regularity 
rule 
Up -> Dq, 
and so of the congruence rule 
\3p \3q 
which gives us the following: 
Theorem 3.65. (Equivalent replacement) Suppose (p^) is a modal formula 
containing an occurrence of a subformula ^ and ip(x) is obtained from by 
replacing this occurrence of'i/j with an occurrence of a formula x- Then, for every 
logic L in the language MC in which the congruence rules for A, V, —□ are 
admissible, xj; x € L implies ip(i/>) <p(x) € L. 
Proof An easy induction on the construction of ip(i/j) is left to the reader as 
an exercise. □ 
Interpolation property. The following theorem will be proved in 
Section 14.1. 
Theorem 3.66 K has the interpolation property. 
Reductions of modalities. A modality is a (possibly empty) string of □, 
O, -i. Since the formulas of the form -»□</? <>-»</?, “■<>ip «-► □-»</? and ->-»</? «-► ip 
are in K, we may assume that every modality M contains at most one symbol 
-> which is the last one in M. A modality M is called affirmative (negative) if 
-> does not occur (occurs) in M. By a modal reduction principle we mean any 
formula of the form Mp —* Np with distinct affirmative modalities M and N. 
Theorem 3.67 No modal reduction principle is in K. 
Proof Let (p = M\p —» M2P be a modal reduction principle. Consider two 
possible cases. 
Case 1: md(M\p) = md(M2p)- Since Mi / M2, <p can be represented 
either as MUN\p —* MON2P or as MON\p —* The former formula 
is refuted (under every valuation) at the root of the frame shown in Fig. 3.13 (a), 
where m > 0 is the length of the string M. And the latter one is refuted at the 
root of the frame shown in Fig. 3.13 (b) under the valuation 2J(p) = {a}, since 
m \= ONip and m ^ CIIV2P. 
Case 2: md(Mip) ^ md(M2p). Let m = max{md(Mip), md(M2p)} and 
k = md(Mip). Then ip is refuted at the root of the frame in Fig. 3.13 (a) under 
the valuation 2J(p) = {&}. □ 
This result can be easily extended to 
Theorem 3.68 If M and N are distinct modalities then Mp —* Np ^ K. 

90 
MODAL LOGICS 
m nontransitive 
• 1 
• 1 
• 0 
(a) 
(b) 
Fig. 3.13. 
Proof Exercise. 
□ 
Modalities M and N are equivalent in a logic L if Mp Np e L. M 
is said to be irreducible in L if it is not equivalent to any modality N with 
md(Np) < md(Mp). 
Corollary 3.69 No distinct modalities are equivalent in K. All modalities are 
irreducible in K. 
Local tabularity. 
Theorem 3.70 K is not locally tabular. 
Proof Follows from Corollary 3.69. □ 
Hallden completeness. 
Theorem 3.71 K is Hallden incomplete. 
Proof Let us consider the formula OT V DJ_. Since • ^ OT and o DJ_, 
neither of its disjuncts is in K. However, OT V □ J_ is in K, since it is equivalent 
to the formula ->D_L VD J_ which is a substitution instance of (AlO) and so belongs 
to K. □ 
Disjunction property. K, as well as all other modal logics to be considered 
in this book, contains all the axioms of Cl including po V ->po and so does not 
have the disjunction property. The disjunction property, as it was formulated 
in Section 1.4, served as some measure of constructivity of the connectives in 
the language C. In the modal case, especially when □ is interpreted as “it is 
provable”, a somewhat different formulation is of interest. 
We say that a modal logic L has the modal disjunction property if, for all 
formulas </?i,..., </?n, Dipi V ... V D<pn e L iff w G L for some i G {1,..., n}. 
Theorem 3.72 K has the modal disjunction property. 
Proof (<=) is clear. To prove (=>) suppose that y?i,...,y?n ^ K. Then there 
are models DJli = (fo,®*), for i = 1 ,...,n, based on disjoint rooted frames 
Si = (Wi, Ri) such that <pi is false at the root Xi of ^i. Now we form a new frame 
S = (W,R) by adding the root x0 to he., put 
W = {x0} U Wl U ... U Wn, 

A FEW MORE MODAL LOGICS 
91 
R = {(xo,Xi) : i = 1,... , n} U R\ U ... U Rn. 
Define a valuation 2J in $ by taking 2J(p) = 2?i(p)U.. .U2Jn(p), for every variable 
p, and let 99t = (#,93). It is clear that every 991* is a generated submodel of 991. 
By the generation theorem, we have (991, Xi) <Pi, for any i — 1,..., n, and so 
xo ^ V ... V D(pn. Therefore, Dcpi V ... V n<pn £ K. • □ 
3.8 	A few more modal logics 
In this section we define a few more modal logics. They are of different origin. 
Some of them, like S4, S5, GL, were created to characterize various 
interpretations of the operator □, while others, such as K, T, K4, originated for purely 
technical reasons. We must warn the reader that he should not look for a deep 
sense or a system in the names of modal logics. Some were given to logics in 
honor of the logicians whose work led to their creation (for instance, Godel- 
Lob, Kripke, Solovay), D stands for deontic\ however, in many cases the names 
are rather arbitrary. 
Most of the logics to be presented here will be defined, like Cl, Int and K, 
semantically, i.e., as the sets of formulas valid in certain frames. But sometimes, 
as was observed at the end of Section 3.1, preferable is a syntactical definition 
of a logic in the form of calculus. The following notions are intended to bridge 
these two methods. 
A calculus (axiomatic system) C is said to be sound with respect to a class 
C of frames if, for every formula cp, be <p implies $ \= <p for all # € C. C is called 
complete with respect to C (or C- complete) if <p is derivable in C whenever it is 
valid in every frame in C. 
The same logic can be defined by different classes of frames. For instance, K 
was defined as the set of formulas which are valid in all frames. On the other 
hand, as follows from Corollary 3.29, it is determined by the class of all finite 
trees. Say that a logic L is characterized (or determined) by a class of frames C 
if 
L = {(peForMC: € C $ \= <p}. 
A frame $ validating all formulas in L is called a frame for L. 
Being equipped with these notions, we can proceed now to defining our modal 
logics. 
Logic T. Semantically the logic T in the language MC is determined by the 
class of all reflexive frames: 
T = {cp € ForA4£ : $ (= cp, for every reflexive frame #}. 
Syntactically T can be defined by the calculus T which is obtained by adding to 
K one more modal axiom re = Up —► p. 
Proposition 3.73 T is sound with respect to the class of reflexive frames. 
Proof Follows from Proposition 3.30. □ 

92 
MODAL LOGICS 
The completeness of T with respect to the class of reflexive frames will be 
established in Section 5.2 (but we recommend the reader to try to modify the 
proof of Theorem 3.53 for T and other calculi to be considered in this section). 
Thus, T can be obtained by adding re to K and taking the closure under MP, 
Subst and RN. In symbols this fact will be written as 
T = K 0 Dp —► p. 
Prom the set-theoretic point of view T is an extension of K, i.e., KCT, Since 
re is refuted in any frame containing an irreflexive point, this inclusion is proper. 
LOGIC K4 is characterized by the class of all transitive frames: 
K4 = {</?€ ForMC : # (= </?, for every transitive frame $}. 
The corresponding calculus KA is obtained by adding to K the transitivity axiom 
tra = Dp —* tump. 
Proposition 3.74 K4 is sound with respect to the class of transitive frames. 
Proof Follows from Proposition 3.31. □ 
The completeness of K4 relative to the same class is proved in Section 5.2. 
Thus, we have 
K4 = K 0 Dp —► □ Dp. 
It is clear that K C K4 (see Example 3.5). However, T and K4 turn out to be 
incomparable by inclusion, since re ^ K4 and tra $ T (why?). 
The modal logics above are of rather technical than philosophical interest: 
they simply correspond to some natural mathematical structures. Our next logic 
S4 is also characterized by a class of very natural structures, viz., quasi-ordered 
sets; however, it can be regarded also as a variant of epistemic logic or a logic of 
informal provability.6 
LOGIC S4 is determined by the class of all quasi-ordered frames, i.e., 
S4 = {up £ ForMC : # |= <p, for every quasi-ordered frame #}. 
The calculus 54 is K plus two additional axioms re and tra. The following 
proposition is an immediate consequence of the preceding ones. 
Proposition 3.75 54 is sound with respect to the class of quasi-ordered frames. 
In Section 5.2 we shall prove the completeness of 54 relative to this class. 
Therefore, 
S4 = K 0 re 0 tra = T 0 tra = K4 0 re. 
It should be clear that Tc S4 and K4 C S4. 
6Recently Artemov (1995) has shown that S4 coincides with the logic of proofs, for some 
natural understanding of the concept of proof. 

A FEW MORE MODAL LOGICS 
93 
If we impose on a quasi-order R on W the symmetry condition, then R 
will be an equivalence relation on W. When all elements in W are in the same 
equivalence class, i.e., if Vx, y xRy, the relation R is called universal Every frame 
$ = (W, R) with an equivalence relation R is the disjoint union of some frames 
= (Wi,Ri) with universal Ri. 
Logic S5, determined by the class of frames with universal alternativeness 
relations, can be regarded as the logic of “logical necessity”. The corresponding 
calculus 55 is obtained by adding to 54 the symmetry axiom sym = p —* DOp. 
Proposition 3.76 55 is sound with respect to the class of frames with universal 
alternativeness relations. 
Proof Follows from Proposition 3.32. □ 
We recommend the reader to show that S4 c S5. In Section 5.2 we shall 
prove that 
S5 = S4 0 p -> DOp. 
Logic Grz, the Grzegorczyk logic, can be connected as S4 with the proof 
interpretation of □. Semantically Grz is determined by the class of Noetherian 
partial orders, i.e., quasi-ordered frames without proper clusters and infinite 
ascending chains. Syntactically it may be defined by the calculus Grz which is 
obtained by adding to K (or KA or 54) the Grzegorczyk axiom grz. 
Proposition 3.48 immediately provides us with 
Proposition 3.77 Grz is sound with respect to the class of Noetherian partial 
orders. 
The completeness of Grz with respect to that class will be established in 
Section 5.5, so we have 
Grz = K® grz = K4 0 grz = S4 0 grz. 
Grz is clearly a proper extension of S4 incomparable with S5. 
Logic D. The deontic logic D (the minimal deontic logic, to be more exact) 
is usually defined by the calculus D obtained by adding to K the seriality axiom 
ser = Up —* Op, which can be read as “what is obligatory is also permitted”. 
The logic 
D = K 0 Up —► Op 
(i.e., the set of all formulas derivable in D) is characterized, as we shall see in 
Section 5.2, by the class of serial frames. One part of this result is an immediate 
consequence of Proposition 3.33. 
Proposition 3.78 D is sound with respect to the class of serial frames. 
D is located between K and T: K c D G T. 
Further refinements of the modality “it is obligatory”, e.g. obligation in the 
moral sense or obligation expressed by sentences in the imperative mood, can 

94 
MODAL LOGICS 
lead to stronger deontic logics such as D4 = D0tra and D5 = D0sym, which 
are called deontic S4 and deontic S5, respectively. 
Logic S4.3. If we understand □ as “it is true now and always will be true” 
and time is considered to be linear, then the logic 
S4.3 	= {</?€ For MC : $ \= </?, for every linearly ordered frame #} 
can be regarded as the logic of the tense necessity. The corresponding calculus 
54.3 	is obtained by adding to 54 the strong connectedness axiom sc (which is 
equivalent in S4 to the connectedness axiom con). 
Proposition 3.79 54.3 is sound with respect to the class of linearly ordered 
frames. 
Proof Follows from Theorem 3.40. □ 
The completeness of 54.3 with respect to linearly ordered frames is proved 
in Section 5.2. Thus, we have 
S4.3 	= S4 0 U(Up ~^q)W □(□? -» p). 
It is easy to see that S4 C S4.3 C S5. 
LOGIC GL. Now let us consider the necessity operator □ as provability in 
formal Peano arithmetic PA. Unlike the previous interpretations of □, which had 
after all a more or less vague character, the provability interpretation of modal 
formulas can be defined in a quite precise manner. To this end we need some 
facts concerning Godel’s numbering of arithmetic formulas (the reader can find 
the details in every serious textbook on mathematical logic). 
All syntactical constructions of the arithmetic language (terms, formulas, 
derivations, etc.) can be effectively coded by natural numbers; the code r0n of 
an arithmetic formula 0 is called the Godel number of 0. Godel constructed a 
formula Pr(x) with a single free variable x such that, for every natural n, 
\-PA Pr(n) iff n = r0n and b-PA 0 for some arithmetic formula 0. 
Here n is the term representing the number n. In other words, Pr(r0“>) asserts 
that the formula 0 is provable in PA. 
By an arithmetic interpretation of the language MC of modal logic we mean 
any map * from For MC to the set of arithmetic sentences such that 
• 1* is 0 = I; 
• ((p O 0)* = <p* © 0*, for © e {A, V, —►}; 
• (□</?)* = Pr(r <p*n). 
The main properties of the provability predicate Pr(x) are as follows: 
(i) b-pA 0 implies \-PA Pr(r0“i); 

A FEW MORE MODAL LOGICS 
95 
(ii) bPA Pr(r<t> -0'n) - (Pr(r0n) Pr(r0'n)); 
(iii) hpA Pr(^0n) Pr(rpr(r0n)n); 
(iv) bPj4 Pr(rPr(r0n) -> 0"1) -> Pr(r0n). 
(The last one is a formalization of Lob’s theorem: V~pa Pr(r0“>) —* 0 implies 
bpA 0.) In any case, these properties are enough to prove Godel’s incompleteness 
theorems for PA. 
The apparent similarity of (i) with the rule RN, (ii) with axiom (All), (iii) 
with tra and (iv) with the Lob axiom la gives rise to the calculus GL which 
is obtained by adding la to K4. And it turns out that the modal propositional 
calculus GL adequately describes the properties of the predicate Pr(x) which are 
provable in PA. Namely, as was established by Solovay (1976), for every modal 
formula <P Iff ^~pa <p* f°r all arithmetic interpretations *. 
As a consequence of Proposition 3.47, we have 
Proposition 3.80 GL is sound with respect to the class of Noetherian strict 
partial orders. 
In Section 5.5 we shall show that GL is complete with respect to that class. 
Thus the provability logic 
GL — K4 0 la — K 0 la 
is characterized by the class of Noetherian strict partial orders. 
It should be clear that K4 c GL and that GL is incomparable by inclusion 
with T, S4, S5, Grz, D, S4.3. 
The last (but not the least) logic to be considered in this section is 
Logic S. The necessity operator □ is understood in it as in GL, but the 
purpose of S is to describe those properties of the provability predicate that 
are true in the standard model of PA (according to Godel’s first incompleteness 
theorem, there are sentences which are true in the standard arithmetic model, 
but not derivable in PA). 
Syntactically S can be obtained by adding to GL the reflexivity axiom re 
and then taking the closure under MP and Subst only (so that RN is not applied 
to re). In symbols this will be written as 
S = GL -F re = (K4 0 la) -f re, 
i.e. -F, unlike 0, presupposes taking the closure only under MP and Subst. 
By Solovay’s (1976) second theorem, for every modal formula </?,</?€ S iff, 
for all arithmetic interpretations *,</?* is true in the standard model of PA. 
The semantics of S is a bit mysterious. Indeed, re claims that frames for S are 
reflexive, while Za, on the contrary, requires the frames to be irreflexive. It follows 
that there is no Kripke frame validating all formulas in S. We will not develop 
a semantics for S here, leaving this question for a more serious consideration in 
Sections 5.6 and 11.4. 

96 
MODAL LOGICS 
3.9 	Embeddings of Int into S4, Grz and GL 
As was noticed in the preceding section, the operator □ in the logic S4, 
characterized by the class of quasi-ordered frames, may be understood as “it is 
provable”. So we can try to formalize the proof interpretation of the intuitionistic 
connectives in Section 2.1 simply by replacing the words “proof’ and 
“construction” in it with □. Thus we come to the following translation T of intuitionistic 
^-formulas into modal A4£-formulas: for all p € Var£ and all <p, ^ € For£, 
• T(p) = □ p; 
• T(±) = □!; 
• T(<pAil>) = T(<p) AT(^); 
• T(<pVil>) = T(<p) V T(V>); 
. T(y> - i>) = □(T(V>) - T(V>)). 
The intuitionistic connectives are transformed by T into the corresponding 
classical ones, but they are understood now in the context of “provability”. 
We are going to show now that the map T : For£ —* For MC, known as the 
Godel translation, is an embedding of Int into both S4 and Grz. 
Let DJI = (#, 2J) be a modal model on a quasi-ordered frame Sr. Define in the 
skeleton p$ of 3 (which is partially ordered) an intuitionistic valuation pDJ by 
taking, for every p € Var£, 
p2J(p) = {C(x) : (Tt,x) |= Op}. 
By Proposition 3.6, this definition does not depend on the choice of x and the set 
pD3(p) is upward closed in p$. We call the model pDJl = (pj, p2J) the skeleton 
of the model DJI. 
Conversely, if 91 = (pS^il) is an intuitionistic model based on the skeleton of 
a quasi-ordered frame $ = (W, R), then by taking for every p e VarMC 
D3(p) = {xeW : (%C(x)) \=p} 
we get a modal model DJI = (#,21) whose skeleton is (isomorphic to) 21. In 
particular, if all clusters in $ are simple and so $ is isomorphic to p$, the model 
DJI is also isomorphic to its skeleton 21. 
Lemma 3.81. (Skeleton) For every model DJI of MC based on a quasi-ordered 
frame, every point x in DJI and every C-formula <p, 
(pWl, C(x)) I=<p iff (art, X) |= T(<p). 
Proof By induction on the construction of <p. The basis of induction follows 
from the definitions of pDJl and T(^). Suppose <p = ^ —* x* Then 
(pan, C(x)) ^ ip iff 3y € xt ((pan, c(y)) |= and (pan, c(y)) p x) 
iff 3y € x| ((3rt, y) 1= T(V') and (3rt,y) ^ T(x)) 
iff (art, x) £ 0{T{rf>) - T(x)), i.e., (3rt, x) T(<p). 

EMBEDDINGS OF INT INTO S4, GRZ AND GL 
97 
For p = -0 V x we have ' 
(pm, c(x)) |= iff (pm, c(x)) |= tp or (pan, c(x)) (= x 
iff (an, x) [= t(v>) or (an, x) |= t (x) 
iff (an,x) (=T(v>). 
The case p = A x is considered in the same way. □ 
Corollary 3.82 For every quasi-ordered frame $ and every C-formula p, 
P$ N iff $ ^ 
Theorem 3.83 The Godel translation T is an embedding of Int into both S4 
and Grz. 
Proof We must show that, for every ^-formula <p, 
p £ Int iff T(p) £ S4 and p £ Int iff T(y>) £ Grz. 
Suppose T(p) S4 (or T(p) ^ Grz). Then there is a quasi-ordered frame $ 
such that # T(y>). According to Corollary 3.82, p%\^p and so p & Int. 
Conversely, suppose p ^ Int. Then, by Theorem 2.57, there is a finite in- 
tuitionistic frame refuting p. As was observed above, it can be treated as a 
modal frame isomorphic to its skeleton. Therefore, by Corollary 3.82, S T(y>), 
from which T (p) ^ S4 and T (p) ^ Grz (since $ contains neither proper clusters 
nor infinite ascending chains). □ 
Remark The proof of the skeleton lemma will not change if we replace T by 
the translation prefixing □ to every subformula of a given intuitionistic formula 
(see also Exercise 3.25). So this translation embeds Int into S4 and Grz too. 
The results above not only give a classical interpretation of the intuitionistic 
connectives but also have purely technical applications. 
Corollary 3.84 Neither S4 nor Grz is tabular. 
Proof Suppose that S4 or Grz is characterized by a finite frame Sr. Then Int 
is characterized by p#. Indeed, if p $ Int then, by Theorem 3.83, T(p) ^ S4 (or 
T(p) ^ Grz) and so S T(p), from which, by Corollary 3.82, p$ p. Thus, 
Int is tabular, contrary to Theorem 2.56. □ 
Corollary 3.85 Neither S4 nor Grz is locally tabular. 
Proof Exercise. □ 
For other uses of the Godel translation T see Section 9.6. 
A frame-theoretic counterpart of T is the operator p which squeezes proper 
clusters into reflexive points. Noetherian strictly ordered frames $ = (W,R), 

98 
MODAL LOGICS 
which characterize GL, can also be easily transformed into partially ordered 
ones—we should only take the reflexive closure Rr of R: 
xRry iff x = y or xRy. 
Given a modal frame S = (W,R) and a model DJI = (#, 2J) on it, the frame 
$r = (W,Rr) and the model 9JT = (3^21) are called the reflexivizations of 3 
and DJI, respectively. 
A syntactic analog of the reflexivization operator r is the following translation 
+ of modal formulas into modal formulas. Let U+p be an abbreviation for the 
formula p A □ p. Then, for every p € ForMC, we denote by p^ the result of 
simultaneous replacing all occurrences of □ in p with □+. 
Lemma 3.86. (Reflexivization) For every model DJI of MC, every point x in 
DJI and every MC-formula p, 
(®t> x) |= <p+ iff{<mr,x) \=y. 
Proof By induction on the construction of p. The basis of induction follows 
from the fact that DJI and DJlr share the same valuation. Suppose p = D0. Then 
(971, a:) f= p+ iff (971, a:) f= 0+ A D0+ 
iff (971, x) |= 0+ and \fy e x\ (971, y) f= 0+ 
iffVyGxt (DJT,y)t=0 
iff (DJT,x) |= D0. 
The cases <^ = 0—<^ = 0Ax and p = 0 V x are trivial. □ 
Corollary 3.87 For every frame 3 and every MC-formula p, 
iff Ft*. 
Provided that GL, as was claimed in Section 3.8, is characterized by the class 
of Noetherian strict partial orders, we obtain now 
Theorem 3.88 The translation + is an embedding of Grz into GL. 
Proof Our aim is to show that, for every modal formula p, 
p e Grz iff p+ e GL. 
Suppose p+ ^ GL. Then there is a Noetherian strict partial order 3 refuting 
p^. The reflexivization 3r of 3 is clearly a Noetherian partial order which, by 
Corollary 3.87, refutes p. So p $ Grz. 
Conversely, if p gL Grz then 3 ft p, for some Noetherian partial order 3 = 
(W,R). Take its “irreflexivization” 3zr = (W,Rir), i.e., put 
xRiry iff x ^ y and xRy. 

OTHER TYPES OF MODAL LOGICS 
99 
Clearly, $'ir is a Noetherian strict order and (3rzr)r is isomorphic to #. Therefore, 
by Corollary 3.87, $'ir ^ from which ^ GL. □ 
Putting together Theorems 3.83 and 3.88, we immediately obtain that Int is 
embeddable into GL. 
Theorem 3.89 The translation T+ defined by T+(y>) = (T(<^))+, for every C- 
formula cp, is an embedding of Int into GL. 
Corollary 3.90 GL is neither tabular nor locally tabular. 
Proof Exercise. □ 
3.10 	Other types of modal logics 
The modal logics presented in the previous sections by no means exhaust the 
existing formalizations of various modal operators. Not trying to list all of them 
here, we just point out some other kinds of modal logics which are in a sense 
(mainly in the style of their semantic definitions) close to those we considered 
above. 
First of all, it should be emphasized that our choice of K as the basic system 
is explained by its “purity”—in essence it is a usual mathematical practice to 
abstract from some details in order to clarify the nature of the object under 
consideration. In principle, there is a wide spectrum of other modal systems that 
could be chosen as basic ones. From the semantical point of view this would 
mean to extend our class of frames and models. 
For example, sometimes it is useful to consider frames as quadruples $ = 
(W, AT, R, D), where (W, R) is a usual Kripke frame, N C W is a set of so called 
normal worlds and D C W a set of distinguished worlds. A valuation in such a 
frame is, as before, a function 03 from YarMC into 2W, and the pair 971 = (#, 03) 
is a model. However, the truth-relation for □ is defined now as follows: 
(971, x) \= iff £ £ AT and (971, y) \= ^ for all y £ W such that xRy, 
and a formula is regarded to be true in 971 if it is true at all points in D. We get 
usual Kripke frames if D = N = W. By imposing various conditions on R, N 
and D we can define many modal logics known in the literature. For instance, 
• the set of formulas that are valid in all reflexive frames with D C N is 
known as the logic S2; 
• the set of formulas that are valid in all quasi-ordered frames such that 
D C N is the logic S3; 
• the set of formulas that are valid in all reflexive frames such that D C N 
and V# £ D3y eW - N xRy is S6. 
The logic Si can be defined analogously but using a somewhat more complicated 
definition of the truth-relation for □. The reader can find it in Cresswell (1972). 
There are other generalizations of the notion of frame. For example, 
applications in computer science and linguistics often require more than one operator 

100 
MODAL LOGICS 
of the type “it is necessary”. We consider then polymodal logics with several 
operators □*, for i = 1,... ,n, each of which is interpreted by its own 
accessibility relation Ri in frames. The set of formulas that are valid in all frames 
(W, #1,..., Rn) (with arbitrary binary relations Ri) is denoted by Kn and called 
the minimal normal n-modal logic. Of course, these frames can also be enriched 
by non-normal and distinguished worlds. 
Modal operators and Hj can interact, which is reflected by some 
connection between Ri and Rj, and by axioms containing both □* and Dj. For instance, 
if we want R2 to be the conversion of Ri (meaning that a moment x is earlier 
than a moment y iff y is later than x) then we should accept the formulas 
P di<>2P, p °2<>ip, 
where Oi and <>2 are the dual operators for D1 and CI2, respectively. More 
precisely, we have 
(W,Ri,Rq) |= (p -► nxo2p) A (p -> □2Oip) 
iff Vx,y e W (xRiy <-» yR2x). We can denote then D2 as D]"1 (using this 
notation for the dual operators as well), R2 as R^1 and drop the subscripts if 
n = 2. In view of the clear tense character of such an interaction between the 
modal operators and the corresponding accessibility relations the set of bimodal 
formulas that are valid in all frames of the form $ = (W, P, P""1) is called the 
minimal normal tense logic, and the symbols □, CT1, O, O-1 are replaced by 
G, H, future), P(ast), respectively. 
Other operations on binary relations provide us with other examples of 
interaction between modal operators. Here are two of them. Consider a frame 
$ = {W, Pi, P2, Rs}- Then 
$ |= 03P «-> OiP A D2p iff R3 = R\ U R2, 
$ |= 03P w Oin2P iff P3 = Ri 0 P2, 
where Pi o R2 is the composition of R\ and R2, i.e., xR\ o R2y iff xR\zR2y for 
some z e W. 
Models with several accessibility relations appear also in the study of modal 
logics on the intuitionistic base. In this case models may contain three relations: a 
partial order for the intuitionistic connectives and two relations for the operators / 
□ and O, which are not supposed to be dual from the intuitionistic point of view. \ 
Another source of generalizations and even completely different semantical 
constructions is the problem of formalizing the epistemic necessity. If we deal 
with modal operators like “it is known that”, “an agent A knows that” then some 
postulates of modal logic, acceptable in other situations, may turn out to be ndjt 
justified. For example, the axiom m(p ► q) —> (Dp —> Hq) and the inferenclp 
rule <p/D<p claim that we (or agent A) know(s) all logical consequences of our 
(his) knowledge—the so called omniscience paradox. There are various ways to 

EXERCISES 
101 
avoid such kind of danger. We show here only one of them: the neighborhood 
semantics. 
A neighborhood frame is a pair S = (W, N) where W, as before, is a 
nonempty set (of worlds or points) and N a function associating with every x G W 
a family N(x) of subsets of W, called neighborhoods of x. A valuation and the 
truth-relation in such a frame are defined as usual with only one exception: 
(971, x) |= Oif iff {y e W : y |= if} £ N(x). 
It is easy to construct a neighborhood model refuting (All). In fact, one can show 
that it is valid in a neighborhood frame $ = (W, N) iff the following conditions 
are satisfied: 
• the intersection of two neighborhoods of a point is again its neighborhood; 
• if WDX'DXe N{x) then Xf e N(x). 
These conditions mean that the set N(x), for every x € W, is a filter in the 
Boolean algebra of all subsets of W (for the definition of filter consult Chapter 
7). We call such frames normal 
We shall not continue describing possible generalizations further. To conclude 
our discussion we would like just to attract the reader’s attention to two points: 
• modal logic contains much more various systems than one is able to 
consider in one book; 
• the ideas and methods studied in this book can be extended in a natural 
way to other systems, though possibly with some modifications. 
As to the latter, from time to time we shall illustrate it in exercises and 
commentaries. 
3.11 	Exercises 
Exercise 3.1 Let K' be the calculus whose axioms are those of Cl, two modal 
axioms DT, Dp A Oq —> D(p A ^) and the inference rules are MP, Subst and 
the regularity rule —> if/Dip —> Dif. Prove that’for every formula Y~k iff 
\~K' <P- 
Exercise 3.2 Show that D = K 0 OT. 
Exercise 3.3 Prove syntactically that the different-axiomatizations of Grz and 
GL presented in Section 3.8 really define the same logics. 
Exercise 3.4 Prove that every formula <p £ K is refuted by an intransitive tree 
of branching and depth < |Sub</?|. 
Exercise 3.5 (Deduction theorem for KA and 54) Show that 
I\ <p \~*KA if implies T \-*K4 U+<p -> 
r, p) Pif implies T i-CD(p —► if. 

102 
MODAL LOGICS 
Exercise 3.6 Show that the inference rules in K are independent (i.e., none of 
them can be deleted without changing the set of derivable formulas). 
Exercise 3.7 Show that the rules p —> #/Op —> Oq and p <-» q/Op <-» Oq are 
derivable in K. 
Exercise 3.8 Show that the rules Up —> Uq/p —> q and Up —> p/p are admissible 
in K. Are they derivable in K? 
Exercise 3.9 Do Exercise 2.4 for the modal case. 
Exercise 3.10 (i) Show that for no set T of modal formulas, $ |= T iff $ is 
irreflexive. 
(ii) Show that for no set T of modal formulas, $ |= T iff # is intransitive. 
(iii) Show that for no set T of modal formulas, S |= T iff is antisymmetric. 
(iv) Show that for no set T of modal formulas, $ |= T iff # is a tree. 
(v) Prove that the Gabbay rule (Up —> p) V y?/y?, for p qL Vary?, holds in a 
frame $ (in the sense that for every formula y? and every variable p not occurring 
in y?, y? is valid in $ whenever (Up —> p) V y? is valid in Sr) iff $ is irreflexive. Show 
also that K is closed under this rule. 
Exercise 3.11 (i) Prove that K4 is characterized by the class of strict partial 
orders and S4 by the class of partial orders. 
(ii) Prove that K4 and S4 are not characterized by the classes of finite strict 
partial orders and finite partial orders, respectively. 
Exercise 3.12 Show that every rooted strict partial order $ is a reduct of some 
strictly ordered tree, which is finite if $ is finite. 
Exercise 3.13 Show that every formula My?, M a modality, is equivalent in S5 
to one of y?, ->y?, □</?, Oy?, CHy?, O-iy?. (Hint: the formulas U2p <-» Dp, 02p <-» Op, 
□Op <-» Op, ODp <-» Up are in S5.) 
Exercise 3.14 Show that every non-empty modality is equivalent in S4 to one 
of □, O, On, no, non, ono, -i, O-.', on-., no-., non-., ono-., which 
are not equivalent to each other. 
Exercise 3.15 Show that the equivalences m02p «-» UOp, OU2p <-> OUp, 
□OnOp w nOp, OUOUp w Onp are in K4. 
Exercise 3.16 Show that every formula is equivalent in K to the conjunction 
of formulas of the form 
VJVO^VD*! V... VDx„, (3.2) 
where y? contains neither □ nor O. 
Exercise 3.17 Show that if a formula of the form (3.2) (where y? contains no □ 
and O) is in K then either y? e K or t/> V \i € K for some i e {1,..., n}. 

EXERCISES 
103 
Exercise 3.18 (Principle of duality) Let p be a modal formula whose 
connectives are only _L, T, A, V, □, O and -i. The dual of ip is the formula p* which 
is obtained by replacing simultaneously every A,V,D,0,_L,Tin<p with V, A, 
O, □, T, _L, respectively. Show that for all formulas p and p <-> ip G K iff 
p* <-> -0* e K. In particular, ip e K iff -up* £ K. 
Exercise 3.19 Show that every variable free formula is equivalent in D either 
to _L or to T. 
Exercise 3.20 Let p(... ,p*,...) be a modal formula containing only (some of) 
the connectives _L,T,A,V, □, O. Show that for every frame # and all valuations 
2J and il in $ such that 2J(pj) = il(pj) if i ± j and 2J(pi) C il(p*), we have 
W(<p)CU(<p). 
Exercise 3.21 Modal formulas containing only _L, T, A, V, □, O are called 
positive. If a formula <p(pi,... ,pn) is positive then <p(-ipi,..., -ipn) is negative. 
Show that if <p(-ipi,..., -«pn) is negative then -^(-^Pi,..., -ipn) is equivalent in 
K to a positive formula, namely, to <p*(pi,... ,pn). 
Exercise 3.22 For an affirmative modality M = D^O-71 ... and n > 0, 
denote by xRM'ny the first order formula 
V^i (yRllz —> 3u\ (ziR^ui A 
Wz2 (uiRl2z2 -^ ... 3uk (ZkRjkuk A xRnUk).. .)))■ 
Prove that a frame # = (W, R) validates the Hintikka formula 
hin = OmiDnipi A ... A OmkUnkpk -> 
a^O^(M\Pl A...AMlpk)V... 
... V □*' 0*‘ (M[pi A ... A Mlkpk) 
with affirmative modalities M*•, i = 1,...,/, j = 1,..., fc, iff it satisfies the 
condition 
Vx, yi,..., yk (xRmiyi A ... A xRmkyk -> 
V^i (xRSlZi —> 3ui (^iR^Ui A piiiMll’niUi A ... A PfeiiM^nfcUi)) V ... 
... V \/zt (xRSlzt -> 3ui (ztRtlui A A ... A pfeiiM*’nfcu/))). 
Exercise 3.23 A finite transitive frame is called a balloon if it is a chain of 
clusters of which only the last one is non-degenerate. Show that a finite transitive 
frame $ validates the formula 
z = □(□p —> p) A OUp —> Up 
iff $ is either irreflexive or a balloon. 

104 
MODAL LOGICS 
Exercise 3.24 A finite quasi-order is a reflexive balloon if it is a chain of 
(nondegenerate) clusters of which only the last one is proper. Show that a finite 
quasi-order # validates the formula 
dum = □(□(£> —> Op) —> p) A ODp —> p 
iff $ is either a partial order or a reflexive balloon. 
Exercise 3.25 Let Ti and T2 be the translations of C into MC prefixing □ to 
every subformula and every proper non-atomic subformula of a given formula, 
respectively. Prove that both Ti and T2 are embeddings of Int into S4 and 
Grz. (Hint: one way of proving is to show that, for every intuitionistic formula 
p, T(tp) <-» Ti(<p) £ S4 and T(p) <-» jOT2(p) £ S4.) 
Exercise 3.26 Let p be a modal formula. Define by induction the notions of 
positive and negative occurrences of subformulas in p. The occurrence of p in p 
is positive. If D0 or 0 O x, for Q e {A, V}, occurs in p positively (negatively) 
then the occurrences of 0 and x in them are also positive (negative) in p. And 
if 0 —> x occurs in p positively (negatively) then the occurrence of 0 in it is 
negative (positive) in p and that of x is positive (negative). 
Provided that GL is characterized by the class of Noetherian strict partial 
orders, show that the translation t of MC into MC replacing each positive 
occurrence of Up in a given formula with □(□<£—> p^) and leaving other subformulas 
intact is an embedding of GL into K4. 
Exercise 3.27 Show that a formula all occurrences of variables in which are 
positive (negative) is equivalent in K to a positive (respectively, negative) 
formula. Is this true for Int? 
Exercise 3.28 Show that the truth-values of modal formulas at points in a 
model with non-normal worlds will remain the same if we arbitrarily change the 
set of points that are accessible from non-normal worlds, in particular, we can 
always assume that those worlds are dead ends. 
Exercise 3.29 Prove that 
(i) if p £ S2 then S2 + □□ p = T; 
(ii) if p £ S3 then S2 -f □ □<£> = S4. 
Exercise 3.30 Prove that S3 can be represented as the calculus with axioms 
(A1)-(A10), D(p —> q) —> □(□£—> Dq) and the inference rules MP, Subst and 
the rule of necessitation applicable only to the axioms of S3. 
Exercise 3.31 Prove that the Godel translation T is an embedding of Int into 
S3. Show that S3 + {Ti(y>) : p e Int} = S4. 
Exercise 3.32 Prove that K 0 {T(y>) : p £ Int} = K 0 D(Dp <-» DDp). 
Exercise 3.33 Prove that 
(i) NExt(K0D(Dp <-» □□£>)) contains a continuum of maximal (with respect 
to C) logics into which Int is embeddable by T; 

NOTES 
105 
(ii) Ext(K 0 □ (□p <-» Hump)) contains a continuum of logics Lfor i e /, 
such that Li + Lj = ForA^L if i ^ j, and each L* has a continuum of maximal 
extensions into which Int is embeddable by T. 
Exercise 3.34 Show that for every tense frame # = (W,R, iZ-1), (i) $ 
validates Op —> 0_10p iff R is transitive, (ii) # f= Op —> □(0“1pVpV Op) 
iff $ |= 0_10p —> (0_1p V p V 0_1p) iff S satisfies the condition of right 
linearity V£,p,z (xRy A xRz —> y = z V piiz V zRy), (iii) # validates the 
formula (p A D_1p) —> OD_1p iff 5 satisfies the conditions of right 
succession and right discreteness Vx3y (xRy A Vz (zRy —► z = a: V zifa;)), and (iv) 
the Hamblin axiom p A Gp —> PGp (i.e., D+p —> 0_1Dp) is valid in # iff 
(yRx A Vz (yRz ->x = zV xRz)). 
Exercise 3.35 Prove that there is a tense formula <p such that # f= <p iff # is a 
disjoint union of finite partially ordered trees. 
3.12 	Notes 
The main object of studies in this book—modal logics resulting from adding to 
classical logic one modal operator together with axioms and inference rules 
describing its properties—was originally created for solving problems that were not 
directly connected to modal logic. We mean here primarily the Lewis systems 
S1-S5 of Lewis and Langford (1932). The first system in the series, namely S3, 
was formulated by Lewis (1918) as a logic without the so called paradoxes of 
material implication, i.e., formulas like (Al), which asserts that a true 
proposition follows from any other proposition even if they speak of entirely different 
things. His idea was to consider the strict implication m(<p —► ip) instead of 
the usual material implication <p —> x/>. However, this solution was not 
completely satisfactory because all Lewis systems contain other types of paradoxical 
formulas—paradoxes of strict implication—like □(□p —> □(</ —> p)). (It is worth 
noting also that there is a converse approach, when one first formulates a non- 
mo dal system axiomatizing some implication => without “paradoxes” and then 
introduces a necessity operator, for instance by taking n<p = (<p => <p) => <p. 
We shall not consider systems of that sort and refer the reader to Anderson and 
Belnap (1975).) The history of the development of (philosophical) modal logic 
before Lewis is discussed in Lemmon and Scott (1977). 
We will not present here axioms of the Lewis systems; the reader can find 
them as well as formulations in the form of Gentzen-style calculi, say in Feys 
(1965) and Zeman (1973). Note only that the modern way of axiomatizing modal 
logics is quite different from that in Lewis and Langford (1932). After Godel 
(1933a), the majority of existing modal calculi were constructed by adding to a 
non-modal basic calculus (say Cl or Int) a number of modal axioms and rules 
which do not change the non-modal basis. 
The semantical approach to defining logics as the sets of formulas that are 
valid in frames from certain classes is now also generally accepted. And even if 
some authors prefer axiomatic systems, they try to formulate modal axioms and 
inference rules in such a way that the desirable properties of the corresponding 

*106 
MODAL LOGICS 
frames were quite clear, and the first results that are established for such 
systems are completeness theorems. Sometimes, however, new logics are formulated 
purely syntactically without any connection to their relational semantics. Such 
were, for instance, the provability logics GL and S (Solovay 1976), the 
provability semantics of which (see Smorynski, 1985) is of much more import than the 
relational one, or Grzegorczyk’s (1967) logic Grz. 
The relational semantics for modal logics, presented in this chapter, was 
created by a number of philosophers and mathematicians. Carnap (1942, 1947) 
constructed a semantics for S5 which was actually the same as Kripke models 
with the universal accessibility relation (although Carnap did not mention any 
relation). Jonsson and Tarski (1951) explicitly introduced (generalized) frames 
as relational representations of modal algebras (see Chapter 8). However, at 
that time this very important paper was not noticed. For instance, Dummett 
and Lemmon (1959) constructed analogous representations of finite algebras for 
S4 apparently not knowing about the work of Jonsson and Tarski. Prior (1957) 
considered frames of the form (a;, <) for interpreting tense operators. And then 
Ranger (1957a, 1957b), Hintikka (1957, 1961, 1963) and Kripke (1959, 1963a, 
1963b, 1965b) developed finally the concept of relational model and proved 
completeness theorems for a few particular systems. The neighborhood semantics 
(briefly discussed in Section 3.10) was constructed by Montague (1968) and Scott 
(1970). 
The truth-preserving operations on frames were introduced by Segerberg 
(1968, 1970, 1971). The technique of unravelling was developed by Dummett and 
Lemmon (1959) and Sahlqvist (1975); the bulldozer theorem is due to Segerberg 
(1970). The connection between modal formulas and first (and higher) order 
properties of their frames is the subject of van Benthem (1983, 1984). Although 
the deduction theorem was known long ago, Theorem 3.57 seems to be quite 
new; we were informed about it by M. Kracht. 
In Section 3.7 we considered examples of properties that are usually 
investigated for various kinds of logics. One of them—the problem of reducing 
modalities—is specifically modal; it is connected with the problem of using and 
understanding iterated modalities in natural languages. In fact, one of the first 
achievements of mathematical studies in modal logic was the famous result of 
Parry (1939) according to which S3 contains precisely 42 irreducible modalities. 
It follows in particular that all extensions of S3 have finitely many irreducible 
modalities. It is to be noted that to find a complete solution to the problem of 
reducing modalities in a given modal logic, i.e., to find a set of pairwise 
nonequivalent irreducible modalities such that any other modality is reducible to 
one of them, may be rather difficult. For example, although the fact that T 
has infinitely many non-equivalent irreducible modalities had been known for a 
rather long time—the proof of the similar result for S2 given by McKinsey (1940) 
goes through for T as well—only Mints (1974) proved that distinct modalities 
are not equivalent in T (see Exercise 5.26). It may be of interest to note in this 
connection that, as was observed by Bellissima (1989), the set of logics in which 
no distinct modalities are equivalent contains at least two maximal (with respect 

NOTES 
107 
to C) logics; see Exercise 5.26. One can show in fact that this set, as well as the 
set of logics with infinitely many irreducible modalities, contains a continuum of 
maximal logics, and that no algorithm can recognize, given a formula </?, whether 
Kbelongs to one these classes. To conclude the discussion of this topic (we will 
not return to it later), we mention two more results. Bellissima (1985b) presents 
a test which gives a complete solution to the problem of reducing modalities in 
a finitely approximable normal extension of S4. Of course, this test cannot be 
effective, since there is a continuum of such extensions. However, it is not hard to 
construct an algorithm which solves this problem for finitely axiomatizable (not 
necessarily finitely approximable) normal modal logics containing S4. Bellissima 
and Mirolli (1989) introduce the functions fi(P(L)) = \{V : jP(Z/) = P(L)}|, 
A(n) = \{L : \P(L)\ = n}|, n(n) = \{P(L) : \P(L)\ = n}|, where P(L) is the set 
of classes of L-equivalent modalities, study their possible behavior for normal 
extensions L of K and leave as an open problem to investigate it in the class of 
normal extensions of D. 
We do not discuss here other properties of modal logics; they will be 
considered in further chapters. In the Handbook of Philosophical Logic (Gabbay and 
Guenthner 1984) the reader can find brief introductions to deontic, epistemic, 
tense and provability logic with further references to textbooks and monographs. 
In the 1970s different people using different methods (details are in Smorynski, 
1985) proved the fixed point theorem of the provability logic GL: for any modal 
formula <p(p, qi,... , gn), where p occurs only within the scope of □, there is a 
formula VKtfi? • ■ •, Qn) such that 
v>(ip(qi,...,qn),qi,---,qn) -> ip(qi,---,qn) e GL. 
A rather simple semantic proof of this theorem was given by Reinhaar-Olson 
(1990). Its various arithmetic applications (in‘particular in the proofs of Godel’s 
theorems) can be found in Smorynski (1985). 
Note by the way that the idea of interpreting the necessity operator as 
provability in Peano arithmetic was proposed also by Kripke (1963b). Buss (1990) 
realized this idea; the resulting set of modal formulas contains in particular the 
logic S4.1. Kuznetsov and Muravitskij (1980), Kuznetsov (1985) and Murav- 
itskij (1985) developed an approach to describing provability in PA from the 
standpoint of intuitionistic propositional logic enriched by a modal provability 
operator, and established a connection of the resulting logic and its extensions 
with extensions of GL. 
Artemov (1980, 1985) considered the problem of describing the modal 
logics having the arithmetic provability interpretation; a complete solution to this 
problem was found by Beklemishev (1990). 
Although the following notion resembles the fixed point theorem above, its 
true origin is in the concept of the so called E-programming (see Goncharov 
and Sviridenko, 1985). Mardaev (1992, 1993a, 1993b) calls a positive (modal or 
intuitionistic) propositional scheme any set 

108 
MODAL LOGICS 
Pi — <Pl(Pl> • • • 5 Pm 5 (7l? • • • 5 Qn)i • • • 5 Pm <Pm(Plj • • • iPmi Qli • • • ? Qn)i 
where all <p*(pi, ... ,pm, Qi, • • •, qn) are (modal or intuitionistic) formulas with 
only positive occurrences of the variables pi,... ,pm. Identifying a formula in a 
model DJI with its truth-set, we say that a tuple Pi,..., Pm is a /ixed point of 
this scheme under given values Q* of qi if the following holds in 9Jt: 
Pi = <pl(Pl> •••>Pm>Qlj**-5 Qn)? • • • j Pm = <Pm(P!.>■••> Pm? Ql? • • • » Qn)- 
In the cited papers Mardaev solves the problem of finding such fixed points in 
models for S4, Grz, GL and Int. For intuitionistic formulas in one variable 
similar problems were considered by Ruitenburg (1984). 
That Int can be embedded in S4 and so can be considered from a “classical” 
point of view was noticed by Orlov (1928) and Godel (1933a). (In fact, Orlov 
(1928) introduced a provability operator, described the axioms of provability, 
which were the same as Godel’s axioms for S4, and treated the intuitionistic 
validity of a proposition in the context of its provability. Besides, he introduced 
the first system of relevant logic.) It is of interest that the first Lewis system 
S3 turned out to be a “modal companion” of Int too, as was shown by Hacking 
(1963) and strengthened by Chagrov (1981). Kuznetsov and Muravitskij (1977, 
1980), Goldblatt (1978) and Boolos (1980) observed independently that Grz is 
embedded by + into GL and T+ embeds Int into GL. The embedding * of 
GL into K4 in Exercise 3.26 is due to Balbiani and Herzig (1994). For more 
information and references see Chagrov and Zakharyaschev (1992). 
The Godel embedding of Int into S4 can be extended to an embedding of 
modal logics on the intuitionistic base into classical polymodal logics; see Fischer- 
Servi (1977), Shehtman (1979) and Wolter and Zakharyaschev (1996, 1997). For 
further references concerning intuitionistic modal logics the reader can consult 
Sotirov (1984) or Bozic and Dosen (1984). 

4 
FROM LOGICS TO CLASSES OF LOGICS 
We have already met with sufficiently many concrete logics to make some 
generalizations. Instead of proving the same sort of theorems for each logic separately, 
we can consider big classes of logics and try to develop general methods for 
investigating their properties en masse. In this chapter we introduce rather abstract 
concepts of superintuitionistic and modal logics and discuss the general settings 
of problems associated with them to be examined in the rest of the book. 
4.1 	Superintuitionistic logics 
All the logics considered in the first two chapters have the same type of language 
and from the set-theoretic point of view are extensions of Int. Besides, all of 
them are closed under MP and Subst. This observation motivates the following 
definition. 
A superintuitionistic logic (si-logic, for short) in the language C is any set L 
of ^-formulas satisfying the conditions: 
• Int C L; 
• L is closed under modus ponens, i.e., (p £ L and p —> ^ € L imply ^ G L, 
for every p, ij) £ For£; 
• L is closed under uniform substitution, i.e., p e L implies ps e L, for 
every p € For£ and every substitution s. 
According to the given definition, the set For£ of all ^-formulas is a si-logic; we 
call it the inconsistent si-logic. Clearly, For£ is the greatest si-logic with respect 
to inclusion and Int is the smallest one. Moreover, it follows from the proof of 
Theorem 2.58 that we have 
Theorem 4.1 For every consistent si-logic L, Int CL C Cl. 
For this reason consistent si-logics are often called intermediate logics. (In 
the propositional case these two notions are practically identical. However, for 
first order logics and theories on superintuitionistic bases Theorem 2.58 as well as 
many other results connecting intuitionistic and classical variants (say, Glivenko’s 
theorem) fail and the term “intermediate logic” becomes almost meaningless.) 
Theorem 4.2 For every family {Li : i e /} of si-logics, the intersection f]ieI Li 
is also a si-logic. 
Proof Follows immediately from the definition of si-logics. 
□ 

110 % 
FROM LOGICS TO CLASSES OF LOGICS 
We introduced Cl, Int and ML semantically, as sets of formulas that are 
valid in certain frames. Many other si-logics can be constructed in a similar way. 
For we have 
Theorem 4.3 Let C be an arbitrary class of intuitionistic frames. Then the set 
of C-formulas that are valid in all frames in C is a si-logic. 
Proof Exercise. □ 
The si-logic defined in Theorem 4.3 will be called the logic of the class C 
and denoted by LogC. If C consists of a single frame # then instead of LogC we 
write Log^ and call this logic the logic of S- For example, by Corollary 2.33, 
Int = LogTn, for each n > 2. It is to be noted that Theorem 4.3 does not hold if 
instead of frames we take models (the set of formulas that are true in a model is 
not necessarily closed under Subst; see Exercise 4.1). Besides, nothing guarantees 
that every si-logic is the logic of some class of frames (see Section 6.5). 
Another way of constructing si-logics follows directly from the definition: 
we can take any set of formulas T, add it to Int and then close the result 
under MP and Subst. The si-logic L thus obtained is denoted by Int + T; the 
formulas in T are called additional or extra axioms of L over Int and L itself the 
extension of Int with F. If F = {p\,..., pn} then along with Int + F we write 
also Int + ipi + ... + pn. For example, Cl = Int -f p V —*p, For£ = Int + p. 
If a si-logic L can be represented as L = Int + F with a finite set F then L is 
said to be finitely axiomatizable. Notice that, by the soundness and completeness 
theorem, the first condition in the definition of si-logics can be replaced by the 
following one: 
• L contains the formulas (Al)-(A9). 
By the axioms (A3)-(A5) we clearly have 
Int + Pi + ... + pn = Int + pi A ... A pn, 
i.e., a si-logic is finitely axiomatizable iff it is axiomatizable by a single extra 
axiom. 
Given logics L\ = Int + F\ and L2 = Int -f T2, the logic L = Int + Fi U F2 is 
called the sum of L\ and L2. If in the definition of Int + F we replace Int with 
a si-logic L then the resulting si-logic 1/ = L + F is the extension of L with T; 
in this case we say that the formulas in F are additional or extra axioms of 1/ 
over L. V is finitely axiomatizable over L if V = L -f F for some finite set F. The 
sum of Li and L2 can be represented now as L\ -f L2 or L2 + L\. The sum of a 
family of si-logics {Li : i E /}, i.e., the closure of Ui€/ ^* under MP and Subst, 
is denoted by ^*• 
Derivations in a si-logic L = Int 4- F are defined similarly to derivations in 
Int: the only difference is that now together with the axioms of Int we can use 
the extra axioms in F. If ip is derivable in L then we write I~l <P- Clearly, p E L iff 
\~l p. In the same way as in Section 1.3 we can define a derivation of p in L from 
a set of assumptions T (notation: F p) and prove the following generalization 
of the deduction theorem for Int: 

SUPERINTUITIONISTIC LOGICS 
111 
Theorem 4.4 I\ ^ he, fcjff T \~l ^ —> </?• 
It should be clear that </? £ L iff L hjnt </?. Since the congruence rules (for 
A, V, —>) are derivable in Int, they are derivable in every si-logic too. So the 
equivalent replacement theorem of Section 1.4 holds for all si-logics as well. 
To axiomatize the sum of si-logics, we can simply join their axioms. It is 
somewhat more difficult to axiomatize the intersection. Call the formula 
TiPli • • • iPn) V V;(Pn+1? • • • »Pn+m) 
the repeatless disjunction of the formulas p(pi,... ,pn) and ^(pi,... ,pm) and 
denote it by ip\Pip. 
Theorem 4.5 Let L\ = Int + {</?* : i £ 1} and L2 = Int + : j £ J}. Then 
Li fl L2 = Int + {tpiVtfj : i € I,j € J}. 
Proof Suppose x € £1 H L2. By the deduction theorem and the properties of 
A, we have Int and f\je Jt ^ —> X £ Int for some finite /' and 
J' such that every ^ and for 2 £ j £ J', are substitution instances of 
some and ^/, for k £ 7, l £ J, respectively. Using the axiom (A8) and the law 
of distributivity, we obtain then 
A (^i v x e Int, 
ierjeJ' 
from which \ £ Int + {ipiVipj : 2 £ J, j £ J} because V is a substitution 
instance of 
Conversely, assume that x £ Int + {ipiVipj : 2 £ J, j £ J}. Then x is derivable 
in Int from some finite set of substitution instances V of axioms of this 
logic. Using (A6) and (A7), we can also derive x from the set of as well as 
from the set of Consequently, x £ 7u C L2. □ 
Clearly, Int in the formulation of Theorem 4.5 can be replaced with any other 
si-logic. 
Although the sum of logics differs in general from the union of them (see 
Exercise 4.3), they have a few important common properties. 
Theorem 4.6 The sum of si-logics is idempotent, commutative, associative and 
distributes over the intersection; the intersection of si-logics distributes over the 
(infinite) sum. 
Proof We show only that 
LnJ2Li = Y,(LnLi) 
iei iei 
and leave the rest to the reader. Suppose L = Int + T and Li = Int + A*, for 
2 £ I. Then we have 

112 
FROM LOGICS TO CLASSES OF LOGICS 
Table 4.1 A list of standard superintuitionistic logics 
For = Int 4- p 
Cl — Int 4- p V -ip 
SmL = Int + (-.g -> p) -> (((p -> g) -► p) p) 
KC = Int 4- -<p V ->-ip 
LC = Int 4- (p —> q) V (q —> p) 
SL = Int 4- ((—«—«p —> p) —> p) —► -p V -n-np 
KP = Int + (->p —> q V r) —» (-«p —> g) V (-<p —> r) 
WKP = Int + (-ip —> V -ir) —> (-p —> ->g) V (-p —> -nr) 
NDjt = Int 4- (-ip -» -<0! V ... V -pfc) —> 
( 'P —> ^l) v ... V (-ip -» -pfc), k > 2 
BDn = Int 4- 6dn 
BW„ = Int + Vto (Pi^V&iPj) 
BTWn = Int 4- Ao<*<j<n “‘(“’Pt A -'Pi) -> V"=o("’P* -*■ V_,Pj) 
Tn = Int + A”=o((Pi -♦ V*i Pj) “♦ Pj) vr=0Pi 
Bn = Int + ALo(^Pi ~ Vi#jPj) -» VLoPi 
NLn = Int + ra/n, where 
n/o = J-, nf j = p, n/2 = -.p, n/w = T 
nf2m+3 = nf 2m+\ ^ nf 2m+2> 
n/2m+4 = n/2m+3 n/2m+l 
L n 53ie/ Li — (Int + T) D (Int + (Jie/ A*) 
= Int + {<pVt/>: <p e r, ip € Ui€/ Ai} 
= Int + Ui6/{^ : <p € T, ^ € Ai} 
= Eie/(Int + {‘PYV’: <P <= r, t/> 6 Ai}) 
= Ei€/((Int + 0 n (Int + Ai)). 
□ 
Note, however, that in general the sum does not distribute over the infinite 
intersection, i.e., L 4- p|i€/ ^ maY differ from f]ieI(L 4- Li) (see Exercise 6.16). 
The family of si-logics together with the operations f) and 4- is called the 
lattice of si-logics7 and denoted by Extint. More generally, if L, 1/ £ Extint 
and L C V then we call V an extension of L, L a sublogic of V and denote the 
family of L’s extensions by ExtL. 
A list of standard superintuitionistic logics is presented in Table 4.1. 
7 For a definition of lattice see Section 7.3. 

MODAL LOGICS 
113 
4.2 	Modal logics 
All the modal logics we met with in Chapter 3 (except those in Section 3.10) 
contain the logic K and are closed under MP and Subst. All of them except S 
are also closed under the rule of necessitation RN. 
A quasi-normal modal logic in the language MC is any set L of M^-formulas 
such that 
• KCL; 
• L is closed under MP and Subst. 
The smallest (with respect to inclusion) quasi-normal modal logic is K and the 
greatest one is the inconsistent modal logic ForA4£. 
A quasi-normal modal logic L is called normal if 
• L is closed under RN, i.e., <p £ L implies Dip £ L, for every formula ip. 
Every quasi-normal logic L can be represented in the form 
L = K + r, (4.1) 
where F C ForMC and -f means, as before, the closure (of KUT) under MP 
and Subst. Every normal logic L is represented as 
L = Ker, (4.2) 
where 0 means the closure under MP, Subst and RN. 
The formulas in F in the representation (4.1) are called the additional or 
extra axioms of L over K; a quasi-normal logic L is finitely axiomatizable if it 
can be represented in the form (4.1) with a finite F. The corresponding notions 
are defined for normal logics by replacing (4.1) with (4.2) and dropping the 
prefix “quasi”. It is to be noted that a finitely axiomatizable normal logic is 
not necessarily finitely axiomatizable if we consider it as a quasi-normal one 
(see Exercise 4.6). Replacing K in (4.1) and (4.2) by an arbitrary (normal or 
quasi-normal) modal logic L, we get the notions of axiomatizability over L. 
As in the case of si-logics, the intersection of (quasi-) normal modal logics is 
again a (quasi-) normal modal logic. The sum can be defined now in two ways: 
• ^2iei Li is the closure of (Ji€/ Li under MP and Subst, and 
• Li is the closure of (Ji€/ Li under MP, Subst and RN. 
The reader can easily check that K -f <£i -f ... -f <£n = K + ^i A...A y?n, 
K 0 pi 0 ... 0 (pn = K 0 pi A ... A pn. 
The family of normal (quasi-normal) modal logics, containing a logic L, 
together with the operations Pi and 0 (+) is called the lattice of normal (quasi- 
normal) extensions of L and denoted by NExtL (respectively, ExtL). 
The two kinds of modal logics—the two ways of forming the closure under 
inference rules, to be more exact—give us two variants of derivations from 
assumptions: with RN and without it. In the same way as in Section 3.6 one can 
prove the following generalization of the deduction theorem for K (in which b* 
means the derivability with RN and b without it). 

114 
FROM LOGICS TO CLASSES OF LOGICS 
A 
a i 
& 
° a3 
Theorem 4.7 For et;en/ L £ ExtK, 
(i) T^Y-l ip iffT i-L </> -* P>; 
(ii) T, %/) <p iff there is m> 0 such that T \-*L D0^ A ... A Dm<0 —» ip. 
If L £ NExt(K 0 tran) then we can clearly take m = n. Moreover, 
Exercise 4.13 gives a sort of conversion of this observation. 
The semantical way of constructing modal logics analogous to that in 
Theorem 4.3 provides us with only (some) logics in NExtK. 
Theorem 4.8 Let C be a class of modal frames. Then the set LogC of MC- 
formulas that are valid in all frames in C is a normal modal logic. 
Proof Exercise. □ 
LogC is called the logic of the class C. If C consists of a single frame # then 
the logic of C is denoted also by Log#. 
A Kripke semantics for quasi-normal modal logics will be introduced in 
Section 5.6. Here we only note that for every frame # and every point x in it, the 
set 
Log {S', {x}) ={ipe ForMC : (S, x) \= y>} 
is a quasi-normal but not necessarily normal modal logic. 
Example 4.9 Let #i, #2 and #3 be the transitive frames shown in Fig. 4.1. 
Then the quasi-normal logics Li = Log {#*, {a*}), for i = 1,2, 3, are not normal. 
Indeed, consider the formulas 
3 3 
= OT, ip2 = f\Oipi -> \J 0(f\Oxpj A-iOtpi), <p3 = Ogrz, 
i= 1 i= 1 izjLj 
where ^1 = D(p A g), ^2 = □ (“•p A g), ^3 = D(pA ->g). The reader can check 
that ipi £ Li but □ ipi Li, for 2 = 1,2,3. 
Since the congruence rules for A, V, —» and □ are derivable in K, the 
equivalent replacement theorem holds for all logics in NExtK. However, this is not the 
case for logics in ExtK. For we have 
Theorem 4.10 A quasi-normal logic L is normal iff p q/^p Cg is an 
admissible rule in L (or, which is equivalent, iff the equivalent replacement theorem 
holds for L). 

‘THE ROADS WE TAKE5 
115 
Proof The implication (=>) is clear. To show (<=), suppose that p £ L. Then 
p T £ L and so Up «-> DT £ L, from which □<£ £ L, since DT «-> T £ K. 
□ 
Analogously to Theorem 4.5 one can prove the following: 
Theorem 4.11 (i) Let L\ = K -f {<£* : i £ 1} and L2 = K -f : j £ J}. Then 
Li n Z/2 = K -f • i € /, j £ J}. 
(ii) Li = K 0 : i £ 7} and L2 = K 0 {^j : j € J}. Then L\ Pi L2 = 
K ® {DViVaVj I,j € J,k,l> 0}. 
Proof Exercise. □ 
The reader can easily check also that Theorem 4.6 holds for both types of 
sum of modal logics. 
A few standard normal modal logics are listed in Table 4.2. 
4.3 	“The roads we take” 
The act of abstraction we made in the two previous sections is aimed mainly to 
work out a general theory which would provide us with tools for dealing with 
arbitrary modal and si-logics and methods allowing to solve problems not for 
each logic individually, but for big classes of them at once. In this section we 
discuss the most important directions in which this theory will be developed. 
Let us begin with methods of constructing logics. We have met with two 
of them: the syntactical or axiomatic method which defines a logic by means of 
indicating its axioms and inference rules, and the semantical one which describes 
a logic as the set of formulas that are “valid” (in one sense or another) in some 
“model structures” like truth-tables, Kripke frames or models. 
Constructing a logic axiomatically, its creator is trying to select a possibly 
minimal list of axioms and inference rules which reflect his ideas of what 
principles of reasoning should be included in the logic. Int, S4, S5, GL and many 
Other logics were constructed in this way. To aim at minimality or laconicity of 
axiomatic systems means the desire to present them in the simplest and clearest 
manner (besides, it is often an interesting mathematical problem). 
We can distinguish, for instance, between finitely and infinitely axiomatizable 
logics. A finitely axiomatizable logic, its finite set of axioms and inference rules, 
to be more precise, will be called, as before, a calculus. Dealing with a calculus, 
we have at hand only its axioms and inference rules; the logic represented by 
the calculus is what is deducible in it. The very same logic can be represented 
by different calculi. This leads to the (algorithmic) problem of deciding whether 
two given calculi are equivalent, i.e., axiomatize the same logic. A closely related 
problem is to recognize if two given formulas p and ^ are deductively equal in 
ExtL (NExtL) in the sense that L -f p = L -f ^ (respectively, L0^ = L0^i). 
As we shall see later, far from all modal and si-logics can be represented 
by calculi. The following criterion is useful for proving that a given logic is not 
finitely axiomatizable. 

116 
FROM LOGICS TO CLASSES OF LOGICS 
Table 4.2 A list of standard normal modal logics 
D 
= 
K 0 Dp —> Op 
T 
= 
K 0 □ p —► p 
KB 
= 
K0p-> DOp 
K4 
= 
K0Dp-^ DDp 
K5 
= 
K 0 ODp —> Dp 
Alt„ 
= 
K © Dpi V D(pi -> p2) V ... V d(pi A ... A pn -+ pn+1) 
D4 
= 
K4 © OT 
S4 
= 
K4 0 Dp —» p 
GL 
= 
K4 0 D(Dp —► p) —> Dp 
For 
= 
K4 0p 
Grz 
= 
K 0 D(D(p —> Dp) —> p) —> p 
K4.1 
= 
K4 0 DOp —» ODp 
K4.2 
= 
K4 0 O(p A □ q) —> D(p V Oq) 
K4.3 
= 
K4 0 D(D+p -► q) V D(D+g -► p) 
S4.1 
= 
S4 0 DOp —> ODp 
S4.2 
= 
S4 0 ODp —> DOp 
S4.3 
= 
S4 0 D(Dp —> q) V D(Dg —> p) 
Triv 
= 
K4 0 Dp <-» p 
Verum 
= 
K4 0 Dp 
S5 
= 
S4 0p —> DOp 
K4B 
= 
K4 0p —> DOp 
A* 
= 
GL 0 DDp —> D(D+p —> g) V D(D+g —> p) 
K4Z 
= 
K4 0 D(Dp —► p) —> (ODp —> Dp) 
Dum 
= 
S4 0 D(D(p —> Dp) —> p) —> (ODp —> p) 
D4GX 
= 
D4 0 D(D+p V D+-ip) —> Dp V O-ip 
K4H 
= 
K4 0p-> D(Op —> p) 
K4Altn 
= 
K4 0 Dpi V D(px —> p2) V ... V D(px A ... A pn —> pn+i) 
K4BW„ 
= 
K4 0 Ai=0 Vo<i^j<n ^ (Pj V ^Pj)) 
K4BD„ 
= 
K4 0 bdn 
K4nm 
= 
K4 0 Dnp -► Dmp, for 1 < m < n 
Theorem 4.12. (Tarski’s criterion) Let Lo be a superintuitionistic or 
quasinormal modal logic in a countable language. A logic L e ExtLo is not finitely 
axiomatizable over Lo iff there exists an infinite sequence of logics L\ C L<i C 
I/3 ... in ExtLo such that L = ]T^>o ^ 'modal logic L e NExtLo is not finitely 
axiomatizable over Lo iff there is an infinite sequence of logics L\ C L^ C L3 ... 

“THE ROADS WE TAKE” 
117 
nontransitive 
i + 1 
% 
2 
Fig. 4.2. 
in NExtLo such that L = ®i>0Li- 
Proof (=>) Let ^i,^,... be an enumeration of all formulas in the language 
of Lo. Define a sequence as follows: pi is the first formula in this 
enumeration that belongs to L — Lo> and for i > 1, Pi+i is the first formula in 
the list ^2> • ■ • that belongs to L but not to Li = Lo + pi + ... 4- Pi- As a 
result we have Li C Li+i and L = ^2i>0Li. In the case of normal modal logics 
it suffices to replace + in the proof above by 0. 
(4=) If we assume that L is finitely axiomatizable then there must be i such 
that Li contains all axioms of L and so Li = L, which is a contradiction. □ 
We demonstrate the use of this criterion by the following: 
Example 4.13 According to Theorems 4.5 and 4.11, the intersection of two 
finitely axiomatizable quasi-normal or si-logics is finitely axiomatizable too. 
However, this is not the case for logics in NExtK. Consider, for instance, the logics 
L\ — K 0 OT and L2 = K 0 Up V D->p and show that L\ Pi L2 is not finitely 
axiomatizable as a normal logic. 
By Theorem 4.11, L\ H L^ — K 0 {D^OT V Dl(Dp V : fc, l > 0} and so 
Li n L2 = Uz>0 where 
Thus, according to Theorem 4.12, it is enough to show that the formula CP+1OT V 
□l+1 (□pVD->p) is not in L\ To this end one can use the frame # shown in Fig. 4.2. 
Indeed, it is easy to see that # |= Ll and # □l+1OT V □l+1(Dp V CU-ip). It 
should be clear, however, that the intersection of finitely axiomatizable logics in 
NExtK4 is finitely axiomatizable as well (see Exercise 4.12). 
The next level of complexity in axiomatic representations of logics is the so 
called recursive axiomatization, which means that there is an algorithm 
recognizing axioms, and the recursively enumerable axiomatization, when there is an 
algorithm generating a sequence of all axioms. In Section 16.2 we shall see that 
in fact these two notions are equivalent. Besides an effective description of 
axioms of a logic L a recursive axiomatization provides an algorithm enumerating 
(generating) precisely all the formulas in L. 
U = K 0 {DkOT V Dl(Dp V Dip) : 0 <k,l<i}. 

118 
FROM LOGICS TO CLASSES OF LOGICS 
However, there are more logics than algorithms: later on we shall meet with 
various continual families of modal and si-logics, while there are “only” 
countably many algorithms. Another important characteristic of a “simple” infinite 
axiomatization is its independence. 
To understand the structure of the class (N) ExtTo it may be useful to find 
a set r of formulas which is complete in the sense that its formulas are able to 
axiomatize all logics in the class and independent in the sense that it contains 
no complete proper subsets. Such a set (if it exists) may be called an axiomatic 
basis of (N) ExtTo. Its role is comparable with the role of a basis in a vector 
space. The existence of an axiomatic basis depends on whether every logic in the 
class can be represented as the sum of “indecomposable” or prime logics. A logic 
L e (N)ExtLo is said to be prime in (N)ExtTo it tor any family {T* : i e 1} of 
logics in (N)ExtLo, T = Yhiei ^ (respectively, L = ®-€/ Li) implies L = Li for 
some i € I. A formula (p is prime in (N)ExtTo if To + ^ (To 0 p) is prime. 
Proposition 4.14 Suppose a set of formulas T is complete for (N)ExtTo and 
contains no distinct deductively equal in (N)ExtTo formulas. Then T is an 
axiomatic basis for (N)ExtTo iff every formula in T is prime. 
Proof We consider only the class ExtTo. 
(=>) If (p € T is not prime then Lo + ip = T0 + Ai + A2 for some sets 
Ai,A2 C T such that T0 + A* cT0 + ^,i = 1,2. Consequently, ip g Ai U A2 
and so T — {p} is complete for ExtTo, which is a contradiction. 
(<=) Suppose otherwise. Then for some formula tp G T, the set V — {p} is 
complete for ExtTo and so there is a finite set A C T such that tp qL A and 
Lq + (p = T0 -F A. But then To + <p = To -f ip, for some ip e A, which is a 
contradiction. □ 
Let us turn now to the semantical way of constructing logics. Until now we 
have operated with two semantical structures: Kripke frames and models. In the 
sequel we shall consider also logical matrices, algebras and general frames. As 
before we say that a logic T is characterized (or determined) by a class C of such 
kind of structures if T coincides with the set of formulas (in the language of T) 
that are valid in all members of C. We can also divide the notion of 
characterization into the two parts: soundness and completeness. The soundness means that 
all structures in C validate T and the completeness that any formula that is not 
in T is separated from T by a structure in C. 
Dealing with the Kripke semantics, we can try to characterize logics by classes 
of models or by classes of frames. Neither of these ways is perfect. As we shall see 
in the next part, all logics under consideration are determined by suitable classes 
of models. However, Kripke frames fail to do this. On the other hand, not every 
class C of models determines a logic: the set of formulas that are true in C is 
not necessarily closed under Subst. Such sets of formulas are called theories, and 
models are their semantical counterparts. Frames, as we saw, determine logics. 
Moreover, being properly generalized, they can determine all of them and so can 
be regarded as semantical counterparts of logics in Extint and ExtK. 

THE ROADS WE TAKE5 
119 
The same logic can be characterized by different classes of structures. For 
example, Int is determined by the class of all Kripke frames or the class of finite 
frames or that of finite trees. Of course, we are interested in finding the simplest 
(in one sense or another) classes of structures characterizing a given logic. One 
possible measure of complexity is the cardinality. For Kripke frames we can define 
then the following hierarchy of modal and si-logics. 
The simplest in this sense are tabular logics each of which is characterized by 
some finite frame. These logics are very nice to deal with: the key problem of 
recognizing whether a formula p belongs to a tabular logic L is decided by the 
routine inspection of all possible valuations of p’s variables in the finite frame 
characterizing L. Other important properties of tabular logics will be considered 
in Chapter 12. A good example of a non-trivial class of tabular logics is ExtS5: 
each logic in it except S5 itself is characterized by a finite cluster. However, the 
majority of interesting logics are not tabular. 
The next in our hierarchy is the class of finitely approximable logics which 
are characterized by (infinite in general) classes of finite Kripke frames. The 
reason for this name is that every such logic L is the intersection of tabular logics 
(those determined by the frames in the class characterizing L), i.e., can be 
“approximated” by a descending sequence of tabular logics. The finite approximable 
logics are known also as the logics with the finite frame property. In Section 8.4 
we shall see that the finitely approximable logics are exactly the logics having 
the finite model property, i.e., those that are complete with respect to classes of 
finite Kripke models. 
The class of finitely approximable logics is of great importance. First, it 
contains almost all standard modal and si-logics. And second, all finitely axiom- 
atizable logics in this class turn out to be decidable, as follows from Harrop’s 
theorem to be proved in Section 16.2 (the reader can easily find a decision 
algorithm himself). Note, however, that proving the decidability of Int and K we 
used not the finite approximability in general but the fact that to separate a 
formula p from Int or K it suffices to consider frames with < 2|Subvl points. 
The number of subformulas in p may be called the length of p\ we denote it by 
l(p). And a logic L such that every p ^ L is separated from L by a frame of 
cardinality < 2is called exponentially approximable. In this connection the 
questions arise whether it is possible to reduce the exponential approximability 
to the polynomial or even linear one, and what kind of lower bounds for the 
complexity of refutation frames we can expect in general for finitely approximable 
logics. Complexity problems of that kind will be discussed in Chapter 18. 
Meanwhile, we just show an example of a linearly approximable (but not tabular) 
logic. 
Example 4.15 Let L be the si-logic determined by the class of finite linearly 
ordered frames. (In the next chapter we shall see that L coincides with LC = 
Int -f (p —> q) V (q —» p), known as the Dummett logic or the chain logic.) If 
P & L then p is refuted in a model 9Jt = (S, 93) based on a finite linear frame S- 
Construct a submodel 91 = (0,11) of DJI by putting into it only the final point 

120 
FROM LOGICS TO CLASSES OF LOGICS 
in #, the final points in the sets {x : x p} for p G Vary? and taking the 
restriction it of 2J to 0. One can readily prove by induction on the construction 
of ^ G Suby? that for every point x in 0, (91, x) \= rp ifi (DJI, x) \= ip and that if 
(DJl,x) \f=- for some x in # then there is y e x| in 0 such that (91, x) ip. It 
follows that 0 y? and |0| < /(</?), i.e., L is linearly approximable. 
As we shall see in Chapter 6, not all logics are finitely approximable. So 
the next level in our hierarchy is the family of logics characterized by countable 
frames. More generally, for an infinite cardinal x, we may say a logic is x- 
approximable if it is determined by frames of cardinality < x. That this division 
makes sense is also shown in Chapter 6. 
Finally, we call a logic just Kripke complete if it is characterized by some class 
of Kripke frames. We already know an example of a Kripke incomplete logic: it 
is Solovay’s S which has no Kripke frames at all. In Chapter 6 we shall construct 
incomplete logics in NExtK4, NExtS4, and Extint. 
In view of these incompleteness results we are facing the problem of finding 
more powerful semantical instruments than Kripke frames. One way of 
constructing an adequate semantics for modal and si-logics is to look at them from the 
algebraic standpoint. As a result of the algebraization, carried out in Chapter 
7, with each logic under consideration we associate a variety of nice algebraic 
structures—Boolean algebras with an additional operator (which is similar to 
the topological interior operator), and pseudo-Boolean algebras (closely related 
to the algebras of open sets in topological spaces). Another way of recovering 
completeness is to impose a restriction on possible valuations in Kripke frames, 
which leads us to the so called general frames. A remarkable result, discovered by 
Jonsson and Tarski (1951) (a few years before the creation of Kripke semantics) is 
that general frames are relational representations of the corresponding algebras, 
naturally generalizing Stone’s representatipn of Boolean algebras as set fields. 
We shall consider general frames and duality theory, studying the relationship 
between algebras and general frames, in Chapter 8. 
So far we have considered semantical characterizations of logics, i.e., of the 
formulas derivable in them. But there is one more fundamental syntactical notion 
for which we should also find a semantical counterpart, namely, that of deriv- 
ability from assumptions. Dealing with the Kripke semantics and the relation h 
(allowing only MP), we say a normal modal or si-logic L is strongly characterized 
(or determined) by a class C of Kripke frames if for any set of formulas T and 
any formula <p (in the language of L), T cp iff for every model DJI based on 
a frame in C and every point x in DJI, (DJI, x) |= T implies (DJI, x) \= cp. A logic 
that is strongly characterized by some class of Kripke frames is called strongly 
Kripke complete. An equivalent definition of strong completeness is provided by 
the following: 
Proposition 4.16 A logic^L e NExtK or L e Extint is strongly Kripke 
complete iff every L-consistent tableau is realizable in a model based on a Kripke 
frame for L. 

‘THE ROADS WE TAKE’ 
121 
Proof The implication (<=) is clear: ilY \fnp then there is a model DJI based 
on a frame for L realizing (T, {<p}), i.e., there is a point x in DJI such that 
(DJI, x) |= T and (DJI, x) p- To prove the converse, suppose a tableau (T, A) 
is L-consistent and let p be a variable not occurring in it. We claim that the 
tableau (T U {p —> p : p G A}, {p}) is L consistent too. For suppose otherwise. 
Then 
n m 
^ f\(<Pi P) P € L 
i=l i=1 
for some fa e T and pi e A. It follows by Subst that 
n m m m 
A V’t a “*■ V w) ->■ V Vie L 
i= 1 i=1 j=1 j = l 
and so /\”=1 fa —► Vjli <Pj € contrary to (V, A) being L-consistent. (Note 
that in the modal case instead of p one can use _L.) Since L is strongly complete, 
we have a model DJI based on a frame for L and a point x in it such that 
x \= T U {p p : p e A} and x p, from which x \f= p for all p G A. □ 
Strongly Kripke complete logics are known also as compact ones; however, we 
shall use the term “compactness” in another sense. 
For the consequence relation h* (allowing both MP and RN) we seem to 
need a somewhat different semantical counterpart. Say that a logic L in NExtK 
is globally Kripke complete if for any finite T and p, V p iff for every model 
DJI based on a Kripke frame for L,DJl\=T implies DJI (= p. L is strongly globally 
complete if this holds for arbitrary (not necessarily finite) sets of formulas T. 
However, we shall prove in Section 10.1 that actually for logics in infinite 
languages the notions of strong completeness and strong global completeness are 
equivalent. Of course, global Kripke completeness can be relativized to finite 
frames, in which case we talk about global finite approximability. 
It is worth mentioning here that to formalize the notion “p logically entails 
'0” is one of the central problems in logic. Syntactically one can explicate it as 
p —> 0 € L, or U(p —► 0) € L, or p \~*L 0 for some suitable logic L. At the 
semantical level it is of interest to consider the relation p \=c 0 which means 
that 0 is valid in all those frames in the class C that validate p, or the local, i.e., 
point-wise variant of this relation. 
Neither the syntactical nor the semantical way of constructing logics is 
satisfactory if taken alone. 
Given a class C of frames (or other semantical structures), we may wish to 
find a simple axiomatization of the logic determined by C. A challenge in this 
direction is to find a recursive axiomatization of the Medvedev logic, determined 
by the rather transparent class of “topless” Boolean cubes. Or we may need first 
to elucidate whether C is modally (or intuitionistically) definable in the sense 
that it coincides with the class of all frames for LogC. (Notice that because of 
incompleteness there may exist different, non-equivalent axiomatizations of C, 

122 
FROM LOGICS TO CLASSES OF LOGICS 
and only one of them generates LogC.) For example, the class of reflexive frames 
is defined by Up —» p, while that of all irreflexive frames is not modally definable 
(see Exercise 3.10). 
On the other hand, given a formula (an axiom of a logic), we are facing 
the problem of characterizing the class of frames (or other model structures) 
validating it. Of course, much depends here on the language in which we want 
to formulate such a characterization. For example, one can easily describe the 
class of Kripke models for a formula <p(pi,... ,pn) using the first order language 
with the monadic predicate symbols P\,..., Pn and the binary predicate symbol 
R. Indeed, define a first order formula ST(ip) with one free individual variable x 
by induction on the construction of ip: 
ST(pi) = Pi(x), ST(±.) = _L; 
ST(iP Ox) = ST(4>) O ST(X), for © G {A, V, 
ST(Uil>) = My (xRy - ST(i>){y/x}), 
where y is an individual variable not occurring in 5T('0). In the intuitionistic 
case the definition of ST (ip —> x) should be replaced with 
ST(rP -^X)=Vy (xRy - (ST(V>) - ST(x)){y/*}). 
The first order formula ST (ip) is called the standard translation of ip. 
Example 4.1T 
ST (Up —> DOp) = My (xRy —> P(y)) —► My (xRy —» Mz (yRz —» P(z))). 
Every Kripke model 9JI = (#, 93) based on a frame # = (W, R) can be 
regarded then as a classical model of this first order language: W is the domain 
for individual variables, Pi,..., Pn are interpreted as 93(pi),..., 93(pn) and R as 
the accessibility relation on #. 
Proposition 4.18 For every formula p, every model VJl and every point a in 
Wl, 
(m,a)t=piff9Jl^ST(p)[al 
m^=p iffDJl\= MxST(p). 
Proof An easy induction on the construction of ip. □ 
ST(p) is a first order equivalent of p as far as models are concerned. If we 
deal with frames then Pi are interpreted as arbitrary monadic predicates on the 
(upward closed, in the intuitionistic case) sets of worlds, and so p corresponds to 
the second order formula VPi... MPnST(p). More exactly, we have the following: 
Proposition 4.19 For every formula p(pi,... ,pn), every Kripke frame # and 
every point a in 
(M \=piff^\=MPx...MPnST(p)[a|, 
$ b iff 3 H= VxVP!... MPnST(p). 

EXERCISES AND OPEN PROBLEMS 
123 
This trivial solution to the characterization problem is hardly satisfactory. 
However, as we saw in Sections 2.5 and 3.5, for many standard modal and in- 
tuitionistic formulas the second order equivalents can be improved to nice first 
order conditions in the language with R and =. These observations lead 
naturally to the general problem of correspondence between modal (intuitionistic) 
formulas and modally (intuitionistically) definable classes of frames, on the one 
hand, and formulas of first or higher order predicate logic and classes of frames 
definable by them, on the other. In this book we shall touch upon only a small 
fragment of correspondence theory; for a more complete presentation the reader 
is referred to van Benthem (1983, 1984). 
In Chapter 6 we shall see, however, that not all modal and intuitionistic 
formulas correspond to first order conditions on the accessibility relation. For 
example, the Lob axiom la has none. (This means that in a sense propositional 
modal and intuitionistic formulas can be more expressive then classical first order 
ones.) Yet, there are other ways to characterize frames for la. It is not hard to 
see that a transitive frame # refutes la iff there is a (not necessarily generated) 
subframe of # reducible to the single reflexive point. In Chapter 9 we develop 
a universal frame-theoretic language giving a solution to the characterization 
problem on transitive (general) frames. 
A characterization of model structures for a formula tp serves often as the first 
step in investigating various properties of the logic axiomatized by ip. Dealing 
with classes of logics, we are interested naturally in finding sufficiently general 
methods of establishing the decidability, completeness, finite approximability, 
etc., and describing (in a syntactical and/or semantical way) families of logics 
with this or that property. Classical examples here are the method of canonical 
models for proving Kripke completeness and Bull’s theorem claiming that all 
logics in NExtS4.3 are finitely approximable. For syntactical properties of 
logics, such as the disjunction or interpolation property, first we should find their 
semantical equivalents. Many results of that kind can be found in Parts II and 
IV. 
The problem of recognizing whether a calculus enjoys a given property can 
be also looked at from the algorithmic point of view. Decidable and undecidable 
properties of calculi in various classes of logics are considered in Chapter 17. 
One more interesting problem, to which we shall turn from time to time in 
this book, is to clarify the structure of the lattices of extensions of various logics 
and to connect it with properties of logics. 
4.4 	Exercises and open problems 
Exercise 4.1 Show that Theorems 4.3 and 4.8 do not hold if instead of frames 
we take models. 
Exercise 4.2 Give an example of a model in which the set of true formulas is 
a si-logic (e.g. Cl). Show that every model of that sort is infinite if the language 
C is infinite. Give an example of a finite model determining a si-logic in a finite 
language. 

124 
FROM LOGICS TO CLASSES OF LOGICS 
Exercise 4.3 Show that the union of two si-logics (or modal logics) is also a 
si-logic (respectively, modal logic) iff one of them is contained in another, and 
only in this case the union and the sum of logics coincide. 
Exercise 4.4 Check that C is a partial order on (N)ExtL and that f) and ^ 
(or ®) are, respectively, the supremum and infimum in the resulting partially 
ordered set. 
Exercise 4.5 Show that © does not in general distribute over infinite 
intersections of modal logics. (Hint: consider D and K 0 Dn_L, for 1 < n < w.) 
Exercise 4.6 Prove that it is impossible to represent K by a calculus with MP 
and Subst as the only inference rules. 
Exercise 4.T Show that each derivation in a normal logic may be reconstructed 
in such a way that the rule of necessitation is applied only to axioms. 
Exercise 4.8 Show that K 0 □ _L = K + DJL 
Exercise 4.9 Show that D is not finitely axiomatizable as a quasi-normal logic. 
Which of the standard normal modal logics are finitely axiomatizable without 
the postulated RN? Show that if such a logic contains tran, for some n > 0, 
then it is finitely axiomatizable as a quasi-normal logic. 
Exercise 4.10 Show that Yliei Li (®i€ / Li) is the smallest quasi-normal 
(normal) modal logic containing (JieI L^. 
Exercise 4.11 Prove that every intuitionistic formula without negative 
occurrences of V (or JL) is deductively equal to some disjunction (respectively, JL-) 
free formula. Show also that every finitely axiomatizable si-logic can be axiom- 
atized over Int by a single conjunction free formula. (Hint: use the formulas 
(p —► q A r) <-> (p —► q) A (p —» r), (p A q —» r) <-> (p —» (q —» r)) that are in Int, 
and ipi A ... A <pn, (<p\ A ... A <pn p) —» p (in which p does not occur in </?*) 
that are deductively equal in Int.) 
Exercise 4.12 Let L\ = K4 0 {</?* : i e 1} and L2 = K4 0 {ipj : j e J}. Show 
that L\ fl L2 — K4 0 {n+(pivn+'ipj : % e /, j G J}. Extend this result to logics 
containing tran. 
Exercise 4.13 Prove that for a modal logic L there exists a formula x(p»q) such 
that, for all <£>, ^ and T, 
r^i-l^iffrKL xfav) 
iff tran € L for some n <u. (Hint: apply the deduction theorem to x(p, q)»P Q 
and take q = [Dm+1p.) 
Exercise 4.14 Show that if a logic L is finitely axiomatizable then any set of 
formulas axiomatizing L contains a finite subset generating L as well. 
Exercise 4.15 Give an example of two modal (si-) logics which are not finitely 
axiomatizable themselves, but whose sum is. 

NOTES 
125 
Exercise 4.16 Prove Tarski’s criterion without stipulating that the language is 
countable. 
Exercise 4.IT Prove that for no modal or intuitionistic formula cp the first order 
formula Vp xRy is equivalent to ST(cp). (Hint: consider the disjoint union of two 
reflexive points.) 
Exercise 4.18 Show that the notions of global and “local” completeness (finite 
approximability) coincide for modal logics containing tran, for some n < uj. 
Exercise 4.19 Show that if Li is characterized by a class C* of frames, for i G /, 
then pji€/ Li is characterized by (J-6/ C*. In particular, Kripke completeness and 
finite approximability are preserved under intersections of logics. 
Exercise 4.20 Show that ip e L, L a si- or modal logic, iff there is a derivation 
of (p in L all variables in which occur in (p. 
Exercise 4.21 Prove that Cl is the only O-reducible consistent si-logic. 
Exercise 4.22 Show that every logic in NExtK with infinitely many pairwise 
non-equivalent modalities is contained in a maximal normal modal logic with 
infinitely many non-equivalent modalities. 
Exercise 4.23 (i) Prove that for every modal formula ip there is a formula ^ 
such that md('0) < 1 and (p <-* xp G S5. 
(ii) Prove that the sets of formulas of modal degree < 1 in logics from the 
interval [T; S5] coincide and that this is not so for any proper extension of the 
interval. 
Exercise 4.24 Prove that for every logic L G NExtK4 and every formula (p 
there is a formula xp with mdfy) < 2 such that L®(p = L®rp. Show that this 
does not hold for K, T, T0p-> DOp. 
Exercise 4.25 Prove that if L\ and L2 are consistent normal modal logics with 
the necessity operators Di and respectively, then the smallest normal bimodal 
logic L containing L\ U L2 is a conservative extension of both L\ and L<i (i.e., 
for every formula (p in the language with □*, i = 1,2, <p G L only if <p G Li). 
Problem 4.1 Is it possible to axiomatize every logic in ExtK by an independent 
set of axioms (with the rules MP and Subst)? 
4.5 	Notes 
Godel (1932) noticed that there are infinitely many logics between Int and Cl. 
Developing this observation, Umezawa (1955,1959) started considering the whole 
class of super intuitionistic logics, which he called “intermediate logics”. The 
notion of normal modal logic, as it is understood in this book, was introduced by 
Lemmon and Scott (1977). The term “normal” is due to McKinsey and Tarski 
(1948), who showed in particular that there are non-normal extensions of S4 
closed under MP and Subst. Segerberg (1971) called such logics quasi-normal. 

126 
FROM LOGICS TO CLASSES OF LOGICS 
There are two main reasons for considering big families of modal logics and 
developing a general theory for them. First, there exist so many concrete modal 
systems in the literature that generalizations and various kinds of classifications 
become inevitable. The second reason (of course connected with the first one) 
is typical in mathematics and science in general: having analyzed a number of 
particular objects of the same nature, we turn to studying the “nature” itself, 
acquiring at this higher level new knowledge of the phenomena we are 
interested in. Recall, for instance, that the notions of straight line, plane and three 
dimensional space led to the general concept of vector space, and group theory 
originated from the study of permutations of n-tuples of natural numbers. 
The following example should be closer to the reader of this book. Suppose 
that we want to prove a theorem according to which all pretabular logics in 
NExtS4 are finitely approximable. There are two ways to do this: (i) to 
analyze each of the five pretabular logics in NExtS4 individually or (ii) to use 
Corollary 12.12 which concerns all pretabular logics in NExtK4. In case (i) the 
theorem turns out to be our brilliant observation, while (ii) explains why this 
observation holds. 
That modal logic is not just a collection of individual systems, that a general 
mathematical theory of modal logics is required was clearly recognized in the 
late 1960s. Even before that modal logicians from time to time dealt with classes 
of extensions of some logics. For instance, Scroggs (1951) described the lattice 
NExtS5, Umezawa (1955, 1959) started investigating si-logics, Dummett and 
Lemmon (1959) considered logics between S4 and S5 and embedded si-logics 
into them, Hosoi (1967) classified si-logics by means of dividing them into slices. 
However, the mainstream of studies in modal logic was to examine individual 
systems and construct new ones with given properties. Moreover, during a rather 
long time there was a hope to find a complete description of the lattices of modal 
and si-logics. If this hope were realized and the class of, say si-logics, turned out to 
be countable and describable in a visual way, then the “individualistic” approach 
would certainly be enough. The turning point was probably the discovery of 
Jankov (1968b) that there exists a continuum of si-logics and the subsequent 
constructions of modal and si-logics with various “negative” properties. 
It would be difficult now to give a complete list of logicians whose work led to 
the creation of the general theory of modal and si-logics, but undoubtedly E.J. 
Lemmon and A.V. Kuznetsov were among the pioneers. 
To illustrate how this theory can help to solve “individual” problems, we 
present here two interesting examples. For many years the problem of 
independent axiomatizability of modal and si-logics resisted all attempts to solve it. A 
way to construct a logic without an independent axiomatization was opened by 
the following observation of Kleyman (1984) which is reformulated here in terms 
of modal logics (Kleyman’s paper deals with varieties of groups). 
Proposition 4.20 Suppose a normal modal logic L\ has an independent 
axiomatization. Then, for every finitely axiomatizable normal modal logic L<i C L\, the 
interval of logics [L2, Li] = {L 6 NExtK : L2 C L C L\} contains an immediate 

NOTES 
127 
predecessor of L\. 
Proof If L\ is finitely axiomatizable then the existence of an immediate 
predecessor of L\ in [L2,Li] follows from Zorn’s lemma (see Section 7.4). 
Suppose now that L\ has an infinite independent set of axioms {pi : i < u>}. 
Since L2 is a finitely axiomatizable sublogic of Li, there is n < uo such that L2 is 
contained in the logic with the axioms • • • > W Let L3 be the logic with the 
axioms • • • i<Pm<Pn+2i ^n+3, — Since the set of Li’s axioms is independent, 
L2 C L3 C L\ and (pn+1 ^ L3. And now again Zorn’s lemma provides us with 
an immediate predecessor of L\ in the interval [L3,Li]. □ 
With the help of this proposition Chagrov and Zakharyaschev (1995a) 
constructed concrete modal and si-logics without independent axiomatizations. The 
reader can fulfill the construction by himself following the hints in Exercises 8.20- 
8.22. Note, by the way, that the problem of independent axiomatizability of 
quasi-normal logics still remains open. 
Another example of that kind is connected with attempts to describe big 
families of logics. A hypothetical way to do this may be illustrated by the following 
observation. As we shall see later, the class Ext(Int + 6d3) contains a continuum 
of logics. But, according to Segerberg’s theorem (to be proved in Section 8.6), 
all of them are finitely approximable and so there is a countable sequence of 
frames (of depth < 3) such that every logic in the class is characterized by one of 
its subsequences. What if logics in bigger classes can be determined in a similar 
way? However, the following proposition holds. 
Proposition 4.21 Suppose a logic L in some class of logics has a continuum 
of immediate predecessors in the class. Then there is no countable sequence C 
of semantical structures such that its subsequences characterize all logics in this 
class. 
Proof Suppose otherwise and let L*, for i £ /, be all distinct immediate 
predecessors of L in our class. Then, as is easy to see, for every i e I there is &t e C 
such that &i |= Li and 6* Lj for j e I — {z}, contrary to C being countable. 
□ 
This proposition, which also follows from Kleyman (1984), was applied to 
modal and si-logics by Chagrov and Tsytkin (1987) and Chagrov (1994a). 
Maksimova et al. (1979) proved that ML is not finitely axiomatizable; She- 
htman (1990b) extended this result to all normal modal companions of ML in 
NExtS4. 
Exercise 4.25 is due to Thomason (1980). 

Part II 
