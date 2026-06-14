<!-- Source: Burgess, J.P. (1982). Axioms for Tense Logic. II. Time Periods. Notre Dame Journal of Formal Logic 23(4):375-383. BibKey: Burgess1982II -->

# Axioms for Tense Logic. II. Time Periods

**Note**: Verbatim OCR extraction from PDF. Mathematical symbols may appear as substitutes due to OCR limitations.

---

375
Notre Dame Journal of Formal Logic
Volume 23, Number 4, October 1982
Axioms for Tense Logic
II. Time Periods
JOHN P. BURGESS
The latest fashion in tense logic is for systems based on time periods
rather than durationless instants. The present note provides an axiomatizability
result for the period-based tense logic of the rationals and the reals, inspired by
the work of P. Roper [1].
1 Structures
L1 Instant-based case 
Here we work with structures % = (X, <) where X is
a nonempty set, < a binary relation on X. Intuitively, X represents the set of
instants of time, and < the earlier/later relation. In the present note we will
consider only those % that are dense linear orders without first or last element.
This of course takes in the usual orders on the rational and real numbers,
denoted !L and ^ , respectively. Let VO be the class of all such orders. For
% = (X, <) e % the order relation < on X determines also a topology on X,
having as basis the open intervals ]xfy[ = \z\ x < z < y\ of %. Thus such
topological notions as regular open set and nowhere dense set can be applied to
subsets of X.
1.2 Period-based case 
Here we work with structures 1f = (T, C, <) where
Y is a nonempty set, C and <d binary relations on Y. Intuitively, Y represents
the set of all nonempty finite uninterrupted periods of time, and C and <I the
inclusion and earlier/later relations among such periods. For % - (X, <) e % we
introduce the structure I{%) = ^ = (F,C,<) given by:
Y = the set of nonempty open intervals ]x,y[ oi%
C = the usual set-theoretic inclusion relation
<l = the natural order relation induced by <, namely:
]x,y[< ]z,w[ iffy <z
Received April 3, 1981

---

376 
JOHN P. BURGESS
Let JL be the class of all /(%) for % e 96, and 7)v the closure of -£ under iso-
morphism. In the present note we will consider only those If = (Y,C,<\) that
belong to Ths. An intrinsic characterization of such \ is provided by 1.3
below; other such characterizations are known, and form part of the folklore
of period-based tense logic.
We make use of the defined notion oi abutment:
a\b iff a < b A ~3c(a 
<c<b).
1.3 Proposition 
A structure 1f = (Y,C,<1) belongs to Thy iff it satisfies the
following postulates:
(PO) 
atbAatb'Aa'lbDa'tb'
(PI) 
3c(a t c A c t 6 ) = 3 d 3 e ( a 
i d A d t e A e l b )
(P2) 
-(a t b A b t a)
(P3) 
3a(at b)A3c(b tc)
(P4) 
atbAbtcAatb'Ab'tcDb 
= br
(P5) 
^ t Z ? A c t c / D ( a t < i v c t Z ? v 3e(fl t e A e t rf) v 3e(c t e A e t 6))
(QO) 
a<fr=tft6v 3c(a tcActft)
(Ql) 
aCZ? = Vc(c<!6 Dc<fl)AVc(^<c3fl<c).
Proof: The necessity of the postulates is a routine exercise. For the sufficiency,
suppose 1f satisfies P0-P5, QO, and Ql. Let W be the set of all pairs (a, b) from
Y satisfying a t b. Define a relation on W by: (a,b) ^ (a', 6') iff a t 6'. PO
implies that « is an equivalence relation. Denote by (a, Z?> the ^-equivalence
class of (a, b), and by X the set of all (a, b). Define a relation on X by: (a, b) <
{c,d) iff 3e(a t e A e t cf). PO implies that < is well-defined (independent of
choice of equivalence class representatives). PI then implies that < is transitive,
and together with P2 that < is antisymmetric. P5 then implies that < is a linear
order. PI then implies that this order is dense, and P3 that it has no first or last
element, so % = (X,<) e 96. Define a function / from Y to the open intervals of
% by sending b to ] (a, b), (b, c)[ for some/any a and c with a t b and b t c (such
exist by P3). It is easily seen that / is well-defined and bijective, injectivity
using P4. Moreover, under / the relation t on Y corresponds to the abutment
relation in I(%). QO, Ql then imply that / is an isomorphism between 1f and
1{%) as required to show 1f eTh/.
2 Valuations
2.1 The p r o b l e m of interpretation 
W e fix a s t o c k p , q , r, . . . o f variables.
A valuation in a structure is a function assigning each variable a subset of the
universe of the structure. In instant-based tense logic, given a valuation V in
% = (X,<), say belonging to 96, we think of each variable o: as representing a
statement that is tensed and whose truthvalue may thus vary from time to
time, and of V(a) as giving us the set of times when a is true. In period-based
tense logic, given a valuation W in 1f - (^,C,<), say belonging to Tfts, we think
of W(a) as giving us the set of periods with respect to which a is true. But what
is truth 'with respect to' a period? This is the central problem of interpretation
for period-based tense logic.
To approach a partial solution, we consider for any valuation V in % =
(X,<) e 96 two derived valuations 1(V), J{V) in I{%) = f = (Y9C9<) e JL

---

AXIOMS FOR TENSE LOGIC II 
377
defined by letting the following hold for all variables a:
(/(F))(a) = \]x,y[ e Y: ]x,y[ - V(a) is empty!
(J(V))(a) = \]xty[ e Y: ]x,y[ - V(a) is nowhere dense}.
Now if a valuation W in If is of form /(F), we can with some plausibility
interprets e W(a) as meaning that a is always true during period a. And if W is
of form J(V), we can interpret it as meaning that a is almost always true during
period a, provided we take 'except for a nowhere dense set of instants' as our
reading of 'almost'. More generally, if 1f e 9?i/9 we can adopt the 'always'
(respectively, 'almost always') reading of a e W(a) provided there is an iso-
morphism of 1f with an element I(%) of «£ under which W corresponds to a
valuation of form I(V) (respectively /(F)). It is also possible to give more
intrinsic characterizations, but this requires some preliminaries.
2.2 Definitional preliminaries 
Let If = (Y,C9<) e 9^ and A C Y. We say
a, c e Y meet if 3e(e C a A e C c). We say c, d e Y weakly split A if c <3 d and:
3a e A(a, c meet) A 3a e A{ay d meet) A ^3a e A(a, c meet A a, d meet).
We say c, d e Y strongly split A if 3e(c <\ e A e < d) and the above condition
holds. We say b e A covers A if \/a e A(a C b) and exactly covers A if further
\/bf(bf covers A D Z? C bf). We say Z? unites A if b exactly covers A and A
cannot be weakly split. We say b sums A if b exactly covers A and A cannot be
strongly split, which last condition reduces to:
Vbf Cb 3a e A (£'meets a).
Now consider a valuation W in 1f. We say W is distributive (or persistent)
if the following holds for all variables a:
(Cl) 
MaVbia e W(a) AbCaDbe 
W(a)).
We say W is weakly cumulative 
if:
(C2) 
VACY 
\fb(A C H/(oO AZ? am'to 4 3 6 e W(a)).
We say H^ is strongly cumulative if:
(C3) 
MA C 7 VfeU C W/(a) A Z? 5wm5 ^4 D 6 e H/(a)).
We say W is homogeneous if it is distributive and strongly cumulative. We say
W is generic if:
(C4) 
Vs(VZ? C a 3c C 6(c e «/(«)) D a e W/(a)).
A valuation V m % - (X, <) e %> will be said to be open (respectively,
regular open) if for each variable a it is the case that V(a) is an open (respec-
tively, regular open) set. Let now % = (X,<) e 96,1{%) = 1f = (Y,C,<) e JL.
2.3 Proposition 
For any valuation W in If the following are equivalent:
(a) W - /(V) for some open valuation V in %
(b) W ~ /(V) for some valuation V in %
(c) W is distributive and weakly cumulative.

---

378 
JOHN P. BURGESS
2.4 Proposition 
For any valuation W in 1f the following are equivalent:
(a) W = I(V) for some regular open valuation V in %
(b) W = /(V) for some valuation V in %
(c) W = J(V) for some regular open valuation V in %
(d) W is homogeneous
(e) W is distributive and generic.
Proofs: Let us see what the definitions of 2.2 amount to in this context. Let
A C Y, and let \JA C X be the set-theoretic union of the elements of A.
Clearly a, c e Y meet iff they have nonempty intersection. Also, A can be
weakly split iff \JA is not convex (i.e., there exist x <y <z with*, z e \JA
and y 4 UA). Similarly, A can be strongly split iff there exist x <z <w <y
with x, y e \JA and ]z,w[ n \JA empty. Further, clearly b covers A if
\j A C b, and b exactly covers A if b is the smallest interval containing \JA.
Finally, b unites A if b = \JA, and b sums A iff \jA C b and no subinterval of
b is disjoint from \jA, which last condition reduces to: b is the smallest
regular open set containing U^4- (We write XA for the smallest regular open
set containing \JA.)
Now in 2.3, (a) trivially implies (b), and (b) easily implies (c). So assume
(c) to prove (a). Define an open valuation Fin % by V(a) = U^O*). Trivially,
if b e W(a), then b C V{ot). Coversely, if b e V(a), then by distributivity A =
\a: a C b A a e W(a)\ satisfies b = U A So by weak cumulativity, b e W(a). This
shows W - I(V), proving (a).
Now in 2.4, (a), (b), and (c) are equivalent by the elementary topological
fact that for any valuation V in % we have J(V) = l(V') where:
V'(a) = interior (closure (interior V(a))).
In particular, if V is already a regular open valuation, V1 = Kand/(F) = /(K).
Also (a) implies (d) and (b) implies (e), in each case distributivity being
trivial. To get strong cumulativity from (a), use our characterization of 'b sums
A* as meaning b = 2,A. To get genericity from (b), use the observation that
\/bCa3cCbce 
W(a) iff U W(a) is dense in a.
Conversely, (d) implies (a) and (e) implies (b), in each case considering the
open valuation defined by V(a) = U ^ a ) . Assuming (d) we have W = J(V)
much as in the proof of 2.3 just given. Assuming (e) the observation just made
above shows that if LW(cO is dense in a, then genericity applies to give us
a e W(a); we then have W = J(V).
The equivalence of 2.4(d) and 2.4(e) is true for any If e 7h/ Gust consider
an isomorphic element of IS).
For the remainder of the present note we will work only with homoge-
neous valuations. Intuitively, one way to justify the restriction to such valua-
tions is to read a e W(a) as 'a is almost always true during the period a\
Another way would be to read it as 'a: is always true during period a' and argue
somehow that 'anything that goes on in time and that we might wish to

---

AXIOMS FOR TENSE LOGIC II 
379
describe' occupies a suitably 'regular open' portion of time. The latter is, in
fact, argued in [1], and the example given there is instructive: Roper says,
"If it is cloudy all morning and cloudy all afternoon, then it is cloudy all day
long". The assumption made here is that it couldn't clear up for just an instant
at the very stroke of noon.
3 Connectives
3.1 Basic definitions 
We now consider formulas built up from our variables
by the binary connective of conjunction (A) and the singulary connectives of
negation (~), strong future (G), and strong past (H). We treat disjunction (v),
conditional (D), weak future (F= ~G~), and weak past (P = ~H~) as abbrevia-
tions in the usual way.
Given a homogeneous valuation W in 1f = (T,C,<l) e 7ft/ we extend W to
a function defined not just on variables but on all formulas—but by abuse of
notation still denoted W—inductively as follows:
W(pc A |3) = W(pt) n W(fi)
W(~a) 
=\a: Mb C a{b i W(a))\
W(Gu) 
= \a: Mb\/c(b Ca/\b<cDce 
W(a))}
W{Ha) 
= \a: Mb\fc(b Ca/\c<bDce 
W(ct))l
The reader may wish to expand the definitions of W(a v (5), W(a D (3), W(Fa\
W(Pa) to see what they work out to. The expression for Wipe D (3) can be
simplified (using homogeneity) to:
Wipe O>(3) = [a: Mb C a(b e W(a) D b e 
W(0))}.
A formula a will be called valid for a subclass 9i/of7ft/ (which may consist
of a single structure, e.g., 1_ or &) provided W(a) = Y for all homogeneous
valuations W in all ^ e 71/. A formula a will be called satisfiable in 71/ if
W{a) ^ (f> for some homogeneous valuation in some If e 71/, or equivalently if
~a is not valid for 7u.
It would be more or less pointless to restrict ourselves to homogeneous
valuations were 3.2 below not true. (And it would not be true had we defined,
say:
W(~a) =Y- W(a)
W(Ga) = \a\ Mb(a <bDbe 
W(a))\.
This explains our choice of connectives!)
3.2 Lemma 
Let W be a homogeneous valuation in 1f e 7?iy. Then condi-
tions Cl and C4 in fact hold not just for variables but for all formulas.
Proof: A routine verification. The hypothesis If e 7ft/ is not really needed.
3.3 Lemma 
All truth-functional tautologies are valid for 7ft/.
Proof: Let W be a homogeneous valuation in If = (Y,C9<) e Tfts. Then (F,C)
can be viewed as a Kripke model for intuitionistic logic, since the definitions of
W(a A |3) and W(~ot) are precisely those of Kripke semantics. This means that
every thesis of intuitionistic logic will be valid. But a celebrated theorem of

---

380 
JOHN P. BURGESS
Godel tells us that for formulas involving only A and ~, intuitionistic and
classical logic agree. The hypotheses that W is homogeneous and If e 7ft/ are
not really needed.
4 
Axiomatizability
4.1 The axioms 
As is well known, the following system J provides a sound
and complete axiomatization for the instant-based tense logic of dense linear
orders without first or last element: As axioms of J we take all truth-functional
tautologies plus the following and their 'mirror images'. (The mirror image of a
formula is the result of replacing each occurrence of G by H and vice versa.)
(Al) 
G(p D q) D (Gp D Gq)
(A2) 
PGp D p
(A3) 
Gp D GGp
(A4) 
Fp A Fq D F(p A Fq) v F(p A g) v F(Fp A q).
As rules of inference of J we take Substitution, Modus Ponens, and Temporal
Generalization (TG): From a to infer Ga. and Ha.
Let us now consider the extension S of J obtained by adding the follow-
ing extra axiom, together with its mirror image:
(A5) 
GpDp.
Our goal is to show that S gives a sound and complete axiomatization for the
period-based tense logic of !L and of -^, subject to our homogeneity restric-
tion.
But first we consider a slight variant &' of 4T obtained by replacing A4
and A5 by:
(A6) 
G(Gp Dq)v G(Gq Dp).
^T1 was used by Roper in [1], where it is shown that A5 is a thesis of £T\ It
can also be shown that A4 is a thesis of ^T'. (Indeed, the negation of the
consequent of A4 yields G(p D G^q) A G(q D G~p). But A6 yields G(G~q D
~p) v G(G~p 3 ~q). Combining these we get G(p D ~p) v G(q D ~q), and so
get the negation of the antecedent of A4.)
Conversely, it can be shown that A6 is a thesis of &. (Indeed, A5 allows
us to drop the middle disjunct in the consequent of A4. Then substituting
Gp A ~q for p and Gq A ~p for q in the modified A4, the negation of A6
implies:
F(Gp A ~q A F(Gq A ~p)) v F(Gq A ~p A F(Gp A ~q))
which is refutable in J.) Thus the two systems are equivalent. £T better
exhibits the relation between instant- and period-based tense logic; 3~' is a
neater formulation if one is interested only in period-based tense logic.
4.2 Soundness Theorem 
Every thesis of ^T is valid for 7h/.
Proof: A stronger result (soundness for a wider class than 7?i/) can be found in
[1] (except that no proof of 3.3 is provided there). That tautologies are valid
is the content of 3.3. It is a routine exercise to verify the validity of each of

---

AXIOMS FOR TENSE LOGIC II 
381
A1-A5 (this is actually done in [1] for A1-A3 and A6). That substitution
preserves validity follows from 3.2. That Modus Ponens preserves validity is
proved much like 3.3. That Temporal Generalization preserves validity is trivial.
4.3 Completeness Theorem 
Every formula consistent with ^T is satisfiable
inl(JL).
Proof: A weaker result (completeness for a class of structures properly includ-
ing 7?v) is in [ 1 ]. Suppose r\ is consistent with ^T, and so a fortiori with J. The
usual completeness theorem for instant-based tense logic provides us with a
valuation V in J such that 0 e V{r\). Define a function T from the rationals to
the class of all maximal-consistent sets of formulas by:
(0) 
T(x) = {(3: x e V((3)\.
Then T is readily verified to satisfy the following for all rationals and all
formulas:
(1) (a) 
GPenx)Ax<y->PeT(y)
(b) 
HP e T{x) /\y<x->Pe T(y).
(2) (a) 
GP 4 T(x) -> 3y(x < y A p 4 T{y))
(b) 
HP 4 T(x) -> 3y(y < X A ^ T(y)).
Now using the fact that 77 is actually consistent with S, it is possible to obtain
V and T so that we further have:
(3) (a) 
GPeT(x)DPeT(x)
(b) 
Hj3 e T(x) Dpe T(x).
(Indeed, let Lp = Hp A p A Gp, and let A be the set of all L|3 where |3 is any
substitution instance of A5 or its mirror image. Since 77 is ^-consistent, the set
H = {r}\ U A is S-consistent, and the original V and T could have been chosen
to have H C 7X0), from which (3) follows.)
Let now 3J1 be the set of pairs of rational numbers equipped with the
lexicographic order: (x,y) < (x',yf) iff x < x' or (x = x' and y <y'). Define a
valuation V' in ^ 2 by letting the following hold for any variable a:
V'(a)=\(x,y):xe V(a)\.
Define a function Tf from pairs of rationals to maximal consistent sets of
formulas by T'(x,y) = T(x). Then Tf inherits property (2) from T9 and has
property (1) because T had properties (1) and (3). Using (1) and (2) for T1 it is
readily verified that (0) holds with V\ T' in place of V, T. In particular,
(O,O)eK'(77).
Now JL2, being a countable dense linear order without first or last ele-
ment, is isomorphic to 1 by a celebrated theorem of Cantor. Pulling back V'
under an isomorphism i: JL2 ~* X, we see that we could have chosen the
original valuation V to satisfy:
(4) 
x e V(p) D 3y 3z(y < x < z A VW(>> <w<zDwe 
F(0)))
because V' has the corresponding property.
Note that (4) implies that for any variable a, V(a) is both open and closed,

---

382 
JOHN P. BURGESS
and in particular, is a regular open set. Thus W = I{V) is a regular open valua-
tion in I(2J). To complete the proof it suffices to apply 4.4 below to any
sufficiently small interval h containing 0, to show that h e W(r}) and 77 is
satisfiable in 1(2J) as required.
4.4 Claim 
For all intervals and formulas we have:
(5) 
]y,z[e W(0) iffVx(y<x<z 
Dxe F(<3)).
Proof: By induction on the complexity of /}, the case |3 a variable being im-
mediate from the definitions, the induction step for A being trivial, and that for
~ an easy application of (4). The cases /J = Gy and |8 = Hy are similar, and we
treat the former.
In case we have x e V(Gy) for all x e a = ]y,z[, given any b C i 
and
& <l c, consider any w e e . For any x e b we have x e FXG7) by the case
hypothesis; and x < w. So w e F(7), and by induction hypothesis it follows
that c e W(y). This shows a e W(Gy) as required in this case.
In case we have x 4 V(Gy) for some x e a, there is a w with x < w and
w 4 V(y). Letz' = min(z,x + w/2), b = ]y,z'[,c= 
]z',w+ l[.Then6 C a, b < c,
but by induction hypothesis c 4 W(y). This shows a i W(Gy) as required in this
case.
4.5 Completeness Theorem 
Every formula consistent with £T is satisfiable
inl(&).
Proof: We retain the notation used above. Here a, b, c will denote open
intervals in JL, and A, B, C open intervals in &. For any a, a* denotes the A
having the same endpoints as a. The valuation W+ inlffi) 
is defined by letting
the following hold for all variables:
(6) 
A e W+(cc) = \fa(a
+ 
C A D a e 
W(a)).
Clearly W+ is distributive. To prove W+ generic and hence homogeneous,
assume \/B C ABC CB(C e W+(a)) to prove A e W+(a). By genericity of W it
suffices to prove Va+ C A 3c C a (c e W(a)). Well, if B = a+ C A, then by hy-
pothesis 3C C B(C e W+(a)). Taking any'c"1* C C we have c Ca and c e W(a) as
required.
We now claim that the following holds for all a and all formulas:
(7) 
a+eW+((3) = aeW(P).
(7) clearly will suffice to complete the proof. (7) itself is proved by induction
on the complexity of |8, it being immediate from the definitions for |8 a
variable, and a routine exercise using (6) for the induction steps. We omit
details.
In closing we remark that the extent of our dependence on Roper's work
is insufficiently apparent from the few citations of [ 1 ] above. In fact most of
our crucial notions (in particular, that of a homogeneous valuation) have been
taken over from him. The only respect in which we have definitely improved
on [ 1 ] is that our models I(JL) and / ( ^ ) , unlike the 'canonical models' of [ 1 ]

---

AXIOMS FOR TENSE LOGIC II 
383
satisfy:
a<b D~3c(c Ca AC Cb).
This does seem to us important if we want our models 'to achieve some
resemblance to the intuitive order of time'.
REFERENCE
[1] Roper, P., "Intervals and tenses," Journal of Philosophical Logic, vol. 9 (1980),
pp. 451-469.
Department of Philosophy
Princeton University
Princeton, New Jersey 08544