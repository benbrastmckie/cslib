<!-- Source: Burgess, J.P. (1982). Axioms for Tense Logic. I. "Since" and "Until". Notre Dame Journal of Formal Logic 23(4):367-374. BibKey: Burgess1982I -->

# Axioms for Tense Logic. I. "Since" and "Until"

**Note**: Verbatim OCR extraction from PDF. Mathematical symbols may appear as substitutes due to OCR limitations.

---

367
Notre Dame Journal of Formal Logic
Volume 23, Number 4, October 1982
Axioms for Tense Logic
I. "Since" and "Until"
JOHN P. BURGESS
1 Preliminaries 
In his thesis [1], H. Kamp enriched tense logic by the
addition of two new binary connectives, the since operator S and the until
operator U. Some time afterward, he announced axiomatizability results for
the S, £/-tense logics of various classes of linear orders. His completeness proofs
were (in his own words) "by no means simple", and have never been published,
though a manuscript treating certain classes of linear orders is in existence. We
will present below axiomatizations for the classes of arbitrary linear orders and
of dense and discrete orders, with and without first and last elements. Our
completeness proofs, although not entirely trivial, are (relatively) simple
modifications of the usual proofs for ordinary tense logic without S and £/,
using maximal consistent sets.
LI Formal syntax 
We start with a stock of propositional variables pi for
/ = 0, 1, 2, . . ., writing p, q, r, s for the first few of them. Formulas are built up
from the p\ using negation (~), conjunction (A), until (£/)> and since (S). We
reserve a, fi, y, 8 to range over formulas, and A, B, C, D to range over sets of
formulas. The mirror image of a is the result of replacing each occurrence of U
in a by S, and vice versa. In the usual way, inclusive disjunction (v), material
conditional (D), material biconditional (=), constant true (T), and constant
false (1) can be introduced as abbreviations. Further abbreviations, with their
suggested readings ('it—the case that') include:1
Fa 
for£/(a,T) 
will be
Pa 
for S(a, T) 
was
Ga 
for ~F~a 
is always going to be
Ha 
for ~P~a 
has always been
G'a 
for U(J ,ot) 
is for some time going to be uninterruptedly
Received April 3, 1981

---

368 
JOHN P. BURGESS
H'OL 
for S(J,a) 
has for some time been uninterruptedly
F'a 
for ~ G' ~a 
will arbitrarily soon be
P'oc 
for ^H'~a 
has arbitrarily recently been.
1.2 Formal semantics 
A valuation in a linear order (X,<) is a function K
assigning each pt a. subset of X. Intuitively, X can be thought of as the set of
instants of time, < as the earlier/later relation, and V as telling us when the
tensed statement p; was/is/will be true. V is extended inductively to all formulas
thus:
V(~a) 
=X- V(a)
Via A ]3) = Via) n K(]3)
V(Uia,p)) = \x: 3y(x <yAye V(a) A \/Z(X <z<yDze 
Vifi)))\
ViSia,P)) ={x:3y(y<xAye 
Via) A Mz(y <z <x D z e K(0)))|.
Intuitively, Uip,q) means that there will be a future occasion of p's truth up
until which q is going to be uninterruptedly true. The formal semantics of the
more familiar connectives G, H works out to what it should be:
ViGa) 
= \x: \fyix<yDye Via))}.
We say a is valid for iX9<) if Via) = X for all valuations, and satisfiable if
K(ce) T£ <f> for some valuation. If ?60 is the class of all linear orders, we say a is
valid (over fl£0) if it is valid for every iX,<) e %/0, and satis fiable if it is satisfi-
able for some iX,<). Alternatively, satisfiability is the failure of validity for the
negation.
1.3 Axiomatic system 
Our basic axiomatic system Jo takes as axioms all
truth-functional tautologies, plus the following together with their mirror
images (the latter being labeled Alb-A7b):
Ala 
G(pDq)D(U(p,r)DU(q,r))
A2a 
G(pDq)D(U(r,p)DU(r,q))
A3a 
p A Uiq, r) D Uiq A Sip, r), r)
A4a 
Uip, q) A -£/(p, r) D Uiq A ~r, q)
A5a 
Uip,q)DUip,qAUip,q))
A6a 
Uiq A Uip, q\ q) D Uip, q)
A7a 
U i p , q ) A Uir,s) D Uip A r, q A S ) V Uip AS, q A s ) y Uiq A r, q A S).
As rules of inference for Jo we take Substitution, Modus Ponens (MP), plus
Temporal Generalization (TG): From a to infer Ga and Ha. The purport of
this last is that logical truth is timeless.
As usual, a deduction (in Jo) is a finite string of formulas each of which is
either an axiom (of Jo) or follows from earlier items by a rule of inference. A
thesis is anything appearing as the last item in a deduction. We do not define
deductions-from-hypotheses, but say that /3 is a consequence of A if there exist
al9 . . ., an e A such that (c^ A , . . ., A an D ]3) is a thesis. Taking n = 0, every
thesis is a consequence of A. A is consistent if 1 is not a consequence of A.
These notions apply to a single formula a by taking A = \a\. A is deductively
closed if it contains all its consequences. We will be interested in deductively
closed sets (DCSs), and in maximal consistent sets (MCSs), and assume famil-

---

AXIOMS FOR TENSE LOGIC I 
369
iarity with their basic properties from ordinary G, //-tense logic or elsewhere.
For instance, a DCS is an MCS iff it has the property: ~ a e A iff a ^ A.
Our main goal is to prove that a formula a is valid (over %/0) iff it is a
thesis (of Jo).
1.4 Soundness 
Every thesis of Jo is valid over %0.
Proof: Inductive. It must be verified that each axiom is valid, and that each
rule of inference preserves validity. For the reader familiar with ordinary
G, //-tense logic, this is a tedious but routine exercise.
1.5 Completeness 
Every formula consistent with Jo is satisfiable over 96 &
Proof: Given below.
1.6 Variants 
By adding extra axioms to Jo we can get sound and complete
axiomatizations for the S, £/-tense logics of various subclasses of %s0, char-
acterized by additional postulates on the order relation <. We tabulate the
results:
Postulates on < : 
Axioms for S, U:
Density 
FfJ
Discreteness 
G'l A Hi
First Element 
FPHL
Last Element 
PFGL
No First Element 
PT
No Last Element 
FT.
For the reader familiar with ordinary G, //-tense logic, the adaptation of our
work below to prove these variants is a routine exercise.
/. 7 Decidability 
The recursive decidability of the set of valid formulas is
an immediate consequence of Rabin's theorem on the decidability of the
monadic second-order theory of the rational order. We omit details.
2 The completeness proof 
We must show that any formula consistent
(with Jo) is satisfiable (over 960). We need several preliminary lemmas.
2.1 Replacement Lemma 
/ / a = j5 is a thesis, then so is 0(a/pz) = 0(j3/p/),
where the slash (/) denotes substitution. In particular, if </>((*/Pi) is a thesis, so
is vW/Pil
Proof: Resembles that of the corresponding result in ordinary G, H-tense logic,
and proceeds by induction on the complexity of the context 0. As a sample we
treat the case 0 = U(\jj,x)- Assuming a. = |3 is a thesis, we have the following
outline of a deduction, where in the interests of perspicuity we omit the 7p*-'"-
(i) 
*(«) D HP) 
| _ I n d u c t i o n Hypothesis
(n) 
x(a)=>x(0) 
I
(iii) 
GbKa) 3 ^03)) 
i, TG
(iv) 
G(X(a) 3 x(J8)) 
", TG
(v) 
*/(*(«), x(«)) => £W(P), X(«)) 
iii-Ala
(vi) 
£/(^03), x(«)) => U(W), X(0)) 
iv, A2a
(vii) 
(j>(<x) D 0(j3) 
v, vi, Truth-Functional Logic

---

370 
JOHN P. BURGESS
The converse is of course similar. Below 2.1 will be used tacitly.
2.2 Consistency Criterion 
/ / A is an MCS and U(y,8) e A, then y is
consistent.
Proof: If 7 is inconsistent, then ~7 is a thesis, so G~y = ~F^~y is a thesis by
TG, so ~U(y, T) = ~Fy is a thesis by 2.1, so ~U(y,8) is a thesis using A2a, and
U(y,8) is inconsistent, and so cannot belong to the MCS A.
2.2 has a mirror image, proved the same way: If A is an MCS and
5(7,6) e A, then 7 is consistent. In the future we leave the formulation of such
obvious mirror images to the reader.
2.3 Lemma 
Let A, C be MCSs. The following are equivalent for any p:
(a) \/yeC(U(y,P)eA)
(b) \/aeA(S(a,P)eC).
Proof: We show that (a) implies (b): Assume (a) and suppose for contra-
diction that a e A is a counterexample to (b). That is, ~S(a,P) e C. By (a),
U(~S(a9P),P) eA.Ky A3a, U(~S(a,p) A S(a,j3),|3) eA9 contrary to 2.2.
We write r(A,p,C) to indicate that A, C are MCSs related as in 2.3. We
write r{A,B,C) to indicate that B is a DCS and that r(A,P,C) holds for all
j3 e B. We write R(A,B,C) to indicate that B is maximal with respect to the
property r(A,—,C); i.e., r{A,B,C) holds, but r(A,B',C) never hokis for any
proper extension Bf of B. Note that whenever r(A,B,C) holds, so does
r(A,B',C) 
where B' is the set of consequences of B. Note that whenever
R(A,B, C) holds and 6 ^ 5 there must exist a |3 e 5 such that rC4,|3 A S,C) does
not hold (else consider B1 = consequences of B U i5j). Hence in this case for
some 7 e C, U(y,j3 A 6) ^ A.
Intuitively, an MCS represents a complete description of a possible state
of affairs. R(A,B, C) then means that a state of affairs of the sort described by
A could be followed by one of the sort described by C, with B being a complete
description of everything that remains true throughout the entire intervening
period. Keeping this intuition in mind, the following lemmas should not appear
unreasonable.
2.4 Lemma 
Let A be an MCS and suppose U(y,P) e A. Then there exist
B, Csuch that j3 e B, 7 e C, and R{A,B, C) holds.
Proof: Let Co = {7} U {5(a,j3): a e A \. We claim Co is consistent. Now Ala, A2a
easily yield S(a A a\0) D 5(a,j3) A 5(a',j8), and A being an MCS it is closed
under A. Hence it will suffice to show that any particular formula 7 A S(a,j3)
with a e A is consistent. But when <xe A, since U(y,P) e A by hypothesis, A3a
yields U(y A S(OL,P),P) e A, whence 2.2 yields the consistency of 7 A 5(a,]3),
completing the proof of the consistency of Co.
Now let C be any MCS extending Co. We have r(A,P,C) by construction,
using criterion 2.3b for r. So it suffices to let B be maximal with respect to the
properties that P e B and r(A,B, C) to complete the proof.
2.5 Lemma 
Suppose we have R(A,B,C), r(A,B',D), r(D,B",C) and B C
B' C\Dn B". Then in fact B = B' n D n B".

---

AXIOMS FOR TENSE LOGIC I 
371
Proof: By the maximality property of B it suffices to show that r(A,B+, C)
holds where B+ = Bf HD C\B". Using criterion 2.3a for r, it suffices to consider
5 6 B+, y e C and show £7(7,6) e ,4.
Well, since 6 e B" and r(D,B", C) we have £7(7,5) e D. Since also 5 e D, we
have 6 A £7(7,5) e D. Since 8 e 5 ' and r(A,B',D) we have 17(8 A £7(7,5), 5) e A.
Then A6a yields the desired conclusion £7(7,5) e A.
2.6 Lemma 
Suppose we have R(A,B,C) 
and 5 4 B. Then there exist
B', D, B" such that ~8 e D andR(A,B',D\ 
R(D,B",C) and B = Br nDn B".
Proof: Let D0 = \S{u,P): a e A, p e B\ U 5 U i - 5 ! u \U(y,P): 7 e C, 0 e Bi. We
claim Do is consistent. Much as in the proof of 2.4 it suffices to show that any
particular
f = S(aJ)Aj8A-8A£/(7,j3)
with a e A, p e B, y e C is consistent. To that end we note that by an earlier
remark there exist 0O e B, y0 e C with ~U(yo,po A 6) e A. We may suppose
(replacing 0, 7 by 0 A 0O, 7 A 7O, respectively, if necessary) that ~£7(7,0 A 5) e A
But £7(7,0) e A by hypothesis rG4,£, C), and so 1/(7,|8 A £7(7,0)) e v4 using A5a.
Now A4a applies and tells us that £7Q3 A U(y,fi) A ~S,/3) e ^4. Using A3a we then
have U(fi A U(y,fi) A ~§ A 5(a,j3),j3) e ^4, from which the consistency of f follows
by 2.2, proving our claim.
Now let D be any MCS extending Z)o, and let B', B" be maximal with
respect to the properties B C B' A r(A,B',D) and B C B" /\ r(D,B",C) respec-
tively. Note we have B = £ ; n D n B'; by 2.5 to complete the proof.
2.7 Lemma 
Suppose we have R(A,B,C) and U{%,r\) e A and 77 4 B. Then
there exist B\ D, B" such that r\ e B', £ e A arcd R(A,Bf,D), 
R{D,B",C) and
B = B; O D O B " .
Proof: Much as in the proof of 2.6 the problem reduces to proving the con-
sistency of the set of formulas of form
f = S(a,]3A77)A/3A£A£7(7,/3)
for a e A, p e B, 7 e C, or what comes to the same thing, of each particular such
f. To this end we note that there are poe B, yoe C with ~U(yo,po A 17) e A, and
we may suppose Po = P, y0 = 7. But U(y,P), £7(f ,17) e ^ by hypothesis, whence
£7(7,0 A £7(7,0)), £7(£,?7 A £7(£,T?)) e -4 using A5a. Now letting 0 = 0 A £7(7,0) A
£ A £7(£,T?), A7a applies to tell us that one of the following must belong to
A: U(y A Ul 
U(yAVr^ U(Z,r)),d), or Utf * U(y,P) A {,0). Since ~{/(T,(3 AT?) e
^4, using Ala and A2a the first two candidates can be ruled out, so it must be
the third. Using A3a we then get £7(f,0 A 77) e A, whence the consistency off
follows, completing (our account of) the proof.
2.8 Lemma 
Suppose we have R(A,B,C) 
and £7(£,T?) e A and ~(£ v (77 A
k^ 7?))) € C. Then the conclusion of 2. 7 holds.
Proof: The proof of 2.7 needs only slight modification. Given a e A, 0 e B,
7 e C, to prove the consistency of f as above, we apply A7a to £7(7 A 7',
0 A £7(7 A 7',0)) € A and £7(£,T? A £7(£,T?)) e 4 , where 7' = ~(£ v (77 A £7(£,T?))) e C

---

372 
JOHN P. BURGESS
We obtain three disjuncts, one of which, must belong to A. Again we can rule
out two candidates and are left with the third, from which the consistency off
follows using A3a. Details are left to the reader.
These preliminaries out of the way, we can turn to the heart of the com-
pleteness proof. Let <? be the set of all pairs (f,g) satisfying:
(CO) 
/ is a function from a subset of the rational numbers to the set of all
MCSs.
(CO') 
The domain, dom f of f is finite.
(Cl) 
g is a function from \(x,y): x, y e dom f A X < y\ to the set of all
DCSs.
(C2) 
Whenever x, y e dom f and x < y, then r(f(x), g(x,y), f(y)) holds.
(C2') 
Whenever x, y e dom f and x immediately precedes y in dom f then
R(f(x),g(x,y)J(y)) 
holds.
(C3) 
Whenever x, y, z e dom f and x < y < z, then g(x,z) = g(xfy) n
f(y)ng(y,z).
Recall that one function extends another if its domain is larger and the two
agree wherever both are defined. We say (f,g) e <f extends (fg) e <f if /'
extends / and g extends g. Intuitively, (fg) e <f should be thought of as a
chronicle describing part of the course of history. Here f(x) tells us what
went on/is going on/will go on at time x, while g(x,y) tells us what remained
true/is to remain true throughout the whole period between x and y. A total
chronicle ought to have the following additional properties, as well as their
mirror images (denoted C4b, C5b):
(C4a) 
Whenever x, y e dom f and x < y and ~U(y,8) e f(x) and y e f(y),
there is some z e dom f with x < z <.y and ^8 e f(z).
(C5a) 
Whenever x e dom f and £/(£,T?) e f(x), there is some y e dom fwith
x<y and £ e f(y) and 77 e g(x,y).
A finite chronicle cannot in general satisfy all cases of C4, C5, but we have the
following:
2.9 Counterexample Lemma 
Let (fg) e <F and suppose x, y, 7, 5 con-
stitute a counterexample to C4a for (fg). Then there exists an extension
(f ,g) e <? of (fg) for which x, y, 7, 5 do not constitute a counterexample
to C4a.
Proof: What we claim is that it is possible to add a single point z lying between
x and y to dom /, and extend / and g to functions /' and g1 on this enlarged
domain, in such a way that ~5 e f(z), and all the conditions for membership in
cf are satisfied by (f',g). We prove this by induction on the number n of
elements of dom / lying between x and y.
Case n = 0. By C2; we have R(f(x), g(x,y), f(y)) and so we can apply 2.6 to
A =f(x),B = g(x,y),C = f(y) to obtain B', D, B". Let z = x + y/2. Set/'(z) = D.
Set g(x,z) = B', g'(z,y) = Bn', and let C3 determine the other values of g(w,z)
and g(z, w).

---

AXIOMS FOR TENSE LOGIC I 
373
Case n = m+ 1. Let x immediately succeed x in dom/. lf~U(y,8) e/(x'), we
can reduce to the case n = m by replacing x by x'. If U(y,8) e fix'), note first
that we must have 8 e fix1), else x, y, 7, 5 would not be a counterexample. Let
7' = 5 A U(y,8) e f(xr). Using A3a we see ~U(y',8) e /(x), so we can reduce to
the case # = 0 by replacing 7 by 7' and y by x'.
2.10 Counterexample Lemma 
Let (fg) e <f and suppose x, £, 77 constitute
a counterexample to C5a for (fg). Then there exists an extension (f\g) e <?
of(fg) for which x, £, 17 do not constitute a counterexample to C5a.
Proof: What we claim is that it is possible to add a single point y lying after x
to dom/, and extend / and g to functions/' and g! on this enlarged domain, in
such a way that £ e f(y), 7? e g(xfy), and all the requirements for membership
in <f are satisfied by (f ,g). We prove this by induction on the number n of
elements of dom / lying after x.
Case n = 0. We can apply 2.4 to A = f(x) obtaining B, C Set y = x + 1, f(y) =
C #'(•*> jO = B, and let C3 determine the other values of g'(w,y).
Case n = m+ 1. Let c immediately succeed x in dom /. If (i) both r\ A £/(£,T?) e
/(x') and 17 e g(x,xf), then we can reduce to the case n = m by replacing x by x'.
If (i) fails, note also that we cannot have (ii) both £ e f(x) and r\ e g(x,xl); else
x, £, r\ would not be a counterexample. But if (i) and (ii) both fail, then the
hypotheses either of 2.7 or else of 2.8 must hold for A = /(*), B - g(x,x'),
C = f(x'). So we can obtain B\ D, B" as in the conclusion of 2.7. Set z =
x + x'/2, f'(z) = D, g(xyz) = B\ g'(z,xr) = B'\ and let C3 determine the other
values of g'(w,z) and g'(z,w). As in 2.9, the details of the verification that
(f >g) e <f a r e left to the reader.
These lemmas out of the way, we are ready to finish the proof of the
completeness of Jo for 760. Let a0 be any consistent formula, to find a linear
order (X,<) in which a0 is satisfiable. We fix an MCS AQ with a0 e Ao, and
define (/0,g0) e ^ by letting dom f0 = iOi, /0(0) = A0,g0 = empty function. We
wish to form a sequence (fn,gn) of elements of J^, each extending the one
before, in such a way that whenever we have a counterexample to C4a or b, or
C5a or b for a given (/m,gm), there will eventually be an (fn,gn) with n> m for
which it is no longer a counterexample. This is accomplished by repeated
application of 2.9 and 2.10 and their mirror images to handle C4a and C5a and
their mirror images, respectively. Since the construction closely resembles one
used in ordinary G, //-tense logic, we omit details. We now let X be the union
of the sets dom fn, and / and g the unions of the fn and gn respectively. Then
(fg) satisfies C0-C5. We define a valuation V in (X,<)~the order being the
usual order on the rationals—by letting the following hold for any x e X and a =
Pi-
(+) 
xe V(a)iffoi€f(x).
2.11 Claim 
(+) in fact holds for all a.
Proof: By induction on the complexity of a. As a sample we treat the case
a = U(P,y). Ifae /(x), then by C5a there is a y e X with x < y and 7 e f(y) and

---

374 
JOHN P. BURGESS
]3 e g(x,y). If z e X and x < z < y, then by C3 we have g(x,y) C/(z), whence
j8 e/(z). By induction hypothesis >> e V(y) and z e K(j3) for any z with x < z < j / ,
whence x e K(o:). If instead ^a e f(x), then for any y e X with x < y and
>> e F(7), we have by induction hypothesis 7 e /(j>), and hence by C4a there
must b e a z e l with x < z < y and ~]8 e/(z), whence by induction hypothesis
z 4 V(fi). It follows that x 4 V(a) as required.
Now since a0 e /(0), (+) tells us that K(a0) ¥= ^, so a0 is satisfiable, com-
pleting the proof.
REFERENCE
[1] Kamp, J. A. W., Tense Logic and the Theory of Linear Order, doctoral dissertation,
University of California at Los Angeles, 1968.
Department of Philosophy
Princeton University
Princeton, New Jersey 08544