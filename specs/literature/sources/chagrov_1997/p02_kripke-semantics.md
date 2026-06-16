<!-- Source: Chagrov & Zakharyaschev (1997). Modal Logic (Oxford Logic Guides 35). Part II: Kripke Semantics — canonical models, filtration, incompleteness (Ch 5-6). BibKey: ChagrovZakharyaschev1997 -->

Kripke semantics 
Proceeding to the systematic study.of superintuitionistic and modal logics, first 
of all we are interested in finding good semantic instruments. To begin with, 
let us try to manage with what we already have, namely, Kripke frames and 
models. So the main questions we address in this part are whether logics in 
Extint and NExtK are characterized by suitable classes of Kripke frames and 
whether they are finitely approximable. First we generalize the completeness 
proofs of Sections 2.6 and 3.6 and show that this approach works for a good 
many other logics. 

5 
CANONICAL MODELS AND FILTRATION 
In this chapter we consider two best known methods of obtaining completeness 
results. One of them—the method of canonical models—given a consistent logic 
L in Extint or NExtK, constructs a canonical Kripke model Wti = ($l,%3l) 
characterizing L. Sometimes the frame turns out to be a frame for L, and 
then we can say at once that L is Kripke complete. Another method, known 
as filtration, is intended for establishing the finite approximability by means of 
extracting from the canonical models finite refutation frames. 
5.1 	The Henkin construction 
Suppose L is a superintuitionistic or normal modal logic, and we want to find a 
class of Kripke models characterizing L. The proofs of the completeness theorems 
for Int and K above provide us with a method of constructing models refuting 
formulas outside of L. However formulas in L need not be true in them. So 
let us try to modify this method in such a way that it would ensure not only 
completeness but also soundness. 
Recall that the worlds in those models are tableaux t = (r, A) consistent in 
Int and K, with the truth-relation in them being chosen so that t \= ip, for all 
ip G T, and £ ^ -0, for all ^ G A. The condition guaranteeing in this situation 
that all formulas in L are true in all worlds is, of course, the inclusion LCT. 
Now we restore this construction in full detail. It is often called the Henkin 
construction in view of its conceptual closeness to the construction used by 
Henkin for proving the completeness of first order classical calculus. 
So, let L be a consistent si-logic in the language C or a normal modal logic 
in the language MC. A tableau t = (r, A) in the language of L is said to be 
L-consistent if for no ip\,..., ipn in A do we have T \~l ip\ V ... V ipn. t is called 
maximal if TU A is the set of all formulas in the language of L. It should be clear 
that every maximal L-consistent tableau is saturated in Int or K (for details see 
the proof of Theorem 1.16). 
The following two lemmas guarantee that if we succeed in constructing 
(according to our plan) a model whose points are all maximal L-consistent tableaux 
then all formulas in L will be true in this model, while all those outside of L will 
be refuted by it. 
Lemma 5.1. (Lindenbaum’s lemma) Every L-consistent tableau t = (T, A) 
can be extended to a maximal L-consistent tableau. 

132 
CANONICAL MODELS AND FILTRATION 
Proof Let y?i, y?2,... be some enumeration of all formulas in the language of L. 
Define a sequence of tableaux to = (To, Ao), t\ = (ri, Ai),... by taking to = t 
and, for i > 0, 
, _ f (r<, Ai U {(Pi}) if (Ti, Ai U {ifi}) is L-consistent 
\ (Ti U {pi}, Ai) otherwise. 
In exactly the same way as in the proof of Theorem 1.16 one can show that 
L-consistency of ti entails the L-consistency of U+i. Thus all the constructed 
tableaux to,t\, • • • prove to be L-consistent and for every formula p there is i 
such that either p G or p G A*. 
Let us consider now the tableau t* = (T*, A*) where 
r* = L)ri> a* = Ua*• 
i<u> i<u> 
It is clear that T* U A* contains all the formulas in the language of L and so t* 
is maximal. To prove that it is L-consistent, suppose otherwise. Then for some 
ip i,pn G A*, there is a derivation of ipi V... \/pn from the set T* in L. Since 
this derivation uses only a finite number of assumptions in T*, there exists i such 
that (pi,..., ipn G Ai and Ti bL ipi V ... V y?n, contrary to ti being L-consistent. 
□ 
Lemma 5.2 Suppose A is a set of formulas and ip a formula in the language of 
L. Then A \~l ip iff, for every maximal L-consistent tableau t = (T, A), ip G T 
whenever ACT. In particular, (p e L iff (p eT for every maximal L-consistent 
tableau t = (T, A). 
Proof (=>) If A C T and p ^ T, for some maximal L-consistent tableau t = 
(T, A), then, by the maximality of t, p G A. Since A bl p, it follows that t is 
not L-consistent, which is a contradiction. 
(4=) Suppose A \/l p. Then the tableau t = (A, {p}) is L-consistent. By 
Lindenbaum’s lemma, t is contained in a maximal L-consistent tableau, which 
is a contradiction. □ 
Remarks (1) When proving Lemmas 5.1 and 5.2, we did not use the rule of 
necessitation. So these lemmas hold for quasi-normal modal logics as well. 
(2) 	It should be clear that with the help of transfinite induction the lemmas 
above can easily be extended to logics in uncountable languages. And certainly 
they hold for logics in finite languages. 
Now we can construct the mode] we are looking for. First we form a frame 
= (Wl,Rl) by taking Wl to be the set of all maximal L-consistent tableaux 
and, for any t\ = (Ti, Ai) and t2 = (r2, A2) in WL, 
t\RL^2 iff Ti C r2 iff Ai D A2, if L g Extint 
and 

THE HENKIN CONSTRUCTION 
133 
fiiWiff W : Uip G Ti} C r2, if L € NExtK. 
The frame is called the canonical frame for L. 
Lemma 5.3 w a Hintikka system in Int, if L £ Extint, and in K, if L £ 
NExtK. 
Proof Follows from the proofs of Theorems 2.43 and 3.53 and Lindenbaum’s 
lemma. □ 
Define a valuation 2Jl in by taking, for every variable p, 
<0L(p) = {(r,A)eWL: per}. 
The resulting model 971^ = is called the canonical model for L. 
Theorem 5.4. (Canonical model) Let L be a consistent superintuitionistic 
or normal modal logic and DJIl = ($l,%3l) its canonical model on the frame 
Sl = (Wli Rl)• Then for every formula <p and every tableau t = (T, A) in Wl, 
(i) <p E T implies (DJlL,t) |= <p, 
(ii) (p £ A implies (DJlz,,t) ^ ip 
and so 
(in) (fmL,t)\=tpifftper. 
Proof By Lemma 5.3, ^ is a Hintikka system. It remains to observe that the 
valuation 2Jl was defined in exactly the same way as in the proofs of 
Propositions 2.31 and 3.25, where the implications (i) and (ii) were established. □ 
Theorem 5.5 Suppose L is a consistent logic in Extint or NExtK. Then every 
L-consistent tableau is realized in WIl- In particular, A \~l <p iff, for every point 
x in WIl, x |= A implies x \= ip, and <p e L iff^flL 1= <P- 
Proof Follows from Lemmas 5.1, 5.2 and Theorem 5.4. □ 
Of course, it seems unlikely that a completeness result of such generality can 
be used as a technical tool for deciding whether a given formula is in L. Indeed, 
the model was defined via the derivability in L and so it is nothing more than 
a model-theoretic reformulation of L. The role of canonical models is different: 
they give us that starting point from which we can develop a model-theoretic 
approach to investigating the logics under consideration. In the next sections of 
this chapter we shall use canonical models to prove the Kripke completeness and 
finite approximability of many superintuitionistic and modal logics. But before 
that we observe some important properties of canonical models which will be 
required in the sequel. 
A model DJI = (#, 2J) for Int or K is said to be differentiated if, for any two 
points x, y in #, x = y whenever exactly the same formulas are true at x and y. 
As a direct consequence of the canonical model theorem we obtain 
Proposition 5.6 Every canonical model is differentiated. 

134 
CANONICAL MODELS AND FILTRATION 
A model 9X1 = (#, 2J) for Int on a frame # = (W, R) is called tight if, for any 
x,y G W, xRy whenever x \= ip implies y |= ip for every ip G Foi\C. A model 
9X1 for K is tight if, for any x, y G W, xRy whenever x \= Uip implies y |= ip for 
every ip G For M.C. It follows immediately from the definition of 9X1 l that the 
following proposition holds: 
Proposition 5.7 Every canonical model is tight. 
A model is called refined if it is both differentiated and tight. Notice that in 
the intuitionistic case differentiatedness follows from tightness. 
Corollary 5.8 Every canonical model is refined. 
In the modal case Propositions 5.6 and 5.7 can be generalized as follows: 
Proposition 5.9 Suppose 9JIl = (Sl^l) is the canonical model for a normal 
modal logic L. Then for any x,y G Wl and any n > 0, xRJfy iff x \= Onip 
implies y |= ip for every modal formula ip. 
Proof (=») Follows from Proposition 3.1. 
(<=) is proved by induction on n. The case n = 0 means nothing else but that 
9X1 l is differentiated. 
Suppose now that our proposition holds for n and let x |= Dn+V imply 
y |= ip for every ip G ForMC. We must prove is that there is z such that xRlz 
and zRJfy. Consider the tableau t = (T, A) where 
T = {ip : x |= □</?}, A = {nnV>: y ft V>} 
and show that it is L-consistent. Suppose otherwise. Then 
bL ipl A ... A ipk -> □"V'l V ... V □n'0m? 
for some y?i,..., pk € T and • • •, nnVVn C A, whence, by Examples 3.49 
and 3.50, 
I“l D(Pi A ... A D(pk —► □(□n'0i V ... V 
Therefore, x |= U{Un'ipl V ... V Unx/jm) and so x f= □n+1('0i V ... V r/jm). But 
then y |= V ... V %/jm, whence y |= fa for some z, contrary to € A. 
By Lindenbaum’s lemma, t is contained in some maximal L-consistent tableau 
t* = (r*, A*). By the definition of T, we must have xRtf*. Furthermore, by the 
definition of A, t* |= Unip implies y |= ip, for every </?, and so, by the induction 
hypothesis, t^R'fy. □ 
Corollary 5.10 For all points x and y in the canonical model for a normal 
modal logic L and every n > 0, xRfy iff y |= ip implies x |= Onip, for all 
<p G ForMC. 
A model 9X1 is called compact if a tableau t is realizable in 9X1 whenever every 
finite subtableau of t is realizable in 9X1. For modal models 9X1 this definition is 
clearly equivalent to the more familiar one: 9X1 is compact if a set of formulas E 
is satisfied in 9X1 whenever every finite subset of E is satisfied in 9X1. 

COMPLETENESS THEOREMS 
135 
Proposition 5.11 Every canonical model is compact. 
Proof Exercise. □ 
5.2 	Completeness theorems 
According to Theorem 5.5, all formulas that do not belong to a superintuitionistic 
or normal modal logic L are refuted in the canonical frame #£. So if we prove 
that is a frame for L, then the Kripke completeness of L will be established. 
Moreover, in this case L will be even strongly complete. 
A logic L with |= L is called canonical For example, Int and K are 
obviously canonical. Using this notion, the observation above can be formulated 
as follows: 
Theorem 5.12 Every canonical superintuitionistic or normal modal logic is 
strongly Kripke complete. 
In fact, sometimes we can derive a much more useful result than simply strong 
Kripke completeness. Suppose that we have already proved the soundness of L 
with respect to the class of frames satisfying some property V. If now we succeed 
in proving that satisfies P, then we shall establish not only that L is canonical 
but also that it is characterized by the class of frames satisfying V. 
For instance, Proposition 3.73 asserts that the calculus T or, equivalently, 
the logic L = K ® Up —► p, is sound with respect to the class of reflexive frames. 
To prove the completeness of this logic, it suffices to establish the reflexivity of 
its canonical frame 'Sl — (Wl,Rl)• Suppose otherwise. Then there is a tableau 
t = (r,A) G Wl such that not tR^t. By the definition of Rl, this is possible 
only if Uip G T and ip G A, for some formula ip. But then, by Lemmas 5.2 and 
5.3, Dip —► ip <£ L, which is a contradiction. 
Note by the way that in this argument we have used only that re belongs to 
L. So actually we have proved the following: 
Theorem 5.13 Suppose a logic L G NExtK is consistent and contains re. Then 
the canonical frame for L is reflexive. 
Corollary 5.14 The calculus T is complete with respect to the class of reflexive 
frames. 
If we recall that the logic T was defined as the logic characterized by the class 
of reflexive frames, then as a consequence of Proposition 3.73 and Corollary 5.14 
we immediately derive 
Corollary 5.15 (i) T = K ® re. 
(ii) T is canonical. 
By the same scheme we can prove the canonicity of the logics in Extint 
and NExtK axiomatizable by the formulas which were supplied by first order 
equivalents in Chapters 2 and 3. 

136 
CANONICAL MODELS AND FILTRATION 
Theorem 5.16 Suppose L is a consistent superintuitionistic or normal modal 
logic and p G L, for some formula p in the list da, wem, bdn, bwn, bcn, 
btwn, kp or, respectively, tran, sym, ser, gakimn, euc, denn, sc, con, ga, 
dir, bwn, bdn, altn. Then the canonical frame for L satisfies the condition 
corresponding to ip. 
Proof We will consider only three formulas, leaving the others to the reader as 
an exercise. 
(i) Let OkUlp —> DmOnp G L, for some k,l,m,n > 0, and show that the 
canonical frame = {Wl,Rl) satisfies the condition 
Vx, y, z (xR^y A xRffz —► 3u (yRlLu A zR^u)). 
Let ti = (Ti,Ai), for i = 0,1,2, be some tableaux in Wl such that toR^ti 
and toR™t2- In order to show that there exists a tableau t = (T, A) for which 
t\RlLt and t2Rrft, we should prove, by Lindenbaum’s lemma, Proposition 5.9 and 
Corollary 5.10, that the tableau 
*' = ({*: Onip € A2}) 
is L-consistent. Suppose otherwise. Then x ^ C L for some formulas ^ Ti 
and On,ip G A2• Applying the regularity rule l times, we obtain Dlx —> □*?/> G L, 
whence G Ti and so OkUlfif e To- Since Oknlip —► DmOnijj G To, we have 
also □mOn^ G To- But then Onip G r2, contrary to i2 being L-consistent. 
(The reader can find a more general result in Exercise 5.25, while the strongest 
generalization, known as Sahlqvist’s theorem, will be proved in Section 10.3.) 
(ii) Suppose now that □ (□+p —> q) V □ (□+# —> p) e L and show that is 
connected, i.e., satisfies the condition 
Vx,y,z (xRLy AxRLz Ay ± z -> yRLz V zRLy). 
Suppose otherwise. Then we have three tableaux ti = (T*, A*) in Wl, for i = 
0,1,2, such that (a) (b) £o#l^2, (c) t\ ^ £2, (d) not and (e) not 
^2^l^i- By (d), there is p\ G A2 such that Upi G Ti, while by (c), we have some 
Xi G Ti fl A2. Let p — p\ V xi- Then U+p G Ti and p G A2. By using (e) and 
(c) in exactly the same way, we can find ^G Ai such that D+rj; g T2. Therefore, 
□ (□+y? —► ip) V □ (□+^ —> p) e Ao, which is a contradiction. 
(iii) Finally, we consider a si-logic L containing the Kreisel-Putnam formula 
kp = (-1 p —> qV r) —> (-1 p —► q) V (~^p —> r) 
and prove that 3L satisfies the condition 
Vx, y, z (xRlP A xRlz A -<pRlz A -<zRlP —► 3u (xRlu A uRLy A A 
Vv (uRlv —> (vRluj A (yRLW V zi^it;))))). 

COMPLETENESS THEOREMS 
137 
Suppose t\ = (Ti, AiJ, £2 = (r2,A2), £3 = (r3, A3) are points in Wl such that 
tiRLh, hRLh and ~^t2RLh, Rl^ Form a tableau £ = (T, A) by taking 
r = riU{-.<^: -•(/?€ r2nr3}, 
A = A2 U A3 
and show that £ is L-consistent. Indeed, if this is not the case then (using the 
first de Morgan law which belongs to Int) we would have 
i-Lv x, 
for some G T2 H 1^3, xjj G A2, \ G A3, and so, by fcp, 
Fi I~l (“•¥> VO V (->(/? -> x)- 
Therefore, either -«/? —► xj) G Ti or —► x £ Fi. In the former case we would 
then have G T2 and in the latter \ G 1^3, contrary to the L-consistency of t2 
and £3. 
Thus, £ is L-consistent and, by Lindenbaum’s lemma, it can be extended to 
a maximal L-consistent tableau, say, £4 = (T4, A4). By the definition, tiR^, 
^aRl^2 and £4/^3- It remains to show that every successor of £4 has a common 
successor with £2 or £3. Suppose otherwise, i.e., some successor £' = (T', A') of £4 
has no common successors with £2 and £3. Then there are formulas -iy?2 G T2 and 
-■y?3 G T3 such that y?2, y?3 G T'. Indeed, the tableau (T2 UT', 0) is L-inconsistent 
(for otherwise £2 and £' would have a common successor) and so (p, y?2 Pl _L, for 
some G T2, ip2 G T', from which -k^2 and hence -xp2 gT2. 
Therefore, ->(/?2 V -k/?3 and so ->(p2 A (^3) are in T2 H T3. But then, since 
£4#l£', we have ->((/>2 A (^3) G T'. On the other hand ip2 A (£3 G T', contrary to 
the L-consistency of £'. □ 
As a consequence of Theorem 5.16 we immediately obtain 
Theorem 5.17 Every logic L in Extint and NExtK axiomatizable by some of 
the formulas mentioned in Theorem 5.16 is canonical, with the canonical frame 
satisfying the first order conditions corresponding to the axioms of L. 
In particular we have the following completeness results: 
Corollary 5.18 (i) The calculus K4 is characterized by the class of transitive 
frames. 
(ii) 54 is characterized by the class of quasi-ordered frames. 
(iii) 55 is characterized by the class of frames with universal alternativeness 
relations. 
(iv) D is characterized by the class of serial frames. 
(v) 54.3 is characterized by the class of connected quasi-orders and by the 
class of linear partial orders. 

138 
CANONICAL MODELS AND FILTRATION 
Proof (i), (ii), (iv) and the first part of (v) are immediate consequences of 
Theorem 5.17 and the soundness results in Section 3.8, (iii) follows from these 
and the generation theorem. As to the completeness of 54.3 with respect to linear 
partial orders, suppose 1/54.3 p. Then p is refuted in a connected quasi-order 
and so, by the generation theorem, in a frame which is a chain of clusters. By 
bulldozing this chain (see the proof of Theorem 3.20), we can construct a linear 
order which is reducible to it and so, by the reduction theorem, also refutes p. 
□ 
For S5 Theorem 5.17 yields an even better result. 
Corollary 5.19 S5 is locally tabular and characterized by the class of finite 
frames with universal alternativeness relations. 
Proof For n > 0 let MCn be a modal language with n variables. By 
Theorem 5.17, the logic S5(n) = S5PiForA4£n is canonical and 5rss(n) is the disjoint 
union of clusters. Since 9JTg5(n) is differentiated and by Proposition 3.7, each of 
these clusters may contain at most 2n points and the total number of clusters 
does not exceed 22™. So $S5(n) is finite. Therefore, there are only finitely many 
pairwise non-equivalent formulas with n variables in S5 and each of them that 
is not in S5 is refuted in Sss^)- □ 
Unfortunately the method of establishing completeness using canonical 
models is far from being universal: there are normal modal and superintuitionistic 
logics which are Kripke complete but not canonical, witnesses GL, Grz, SL (see 
Section 6.2) and the McKinsey logic 
KM = K ® DOp —> OUp. 
It also turns out that the axioms of these logics do not correspond to any first 
order condition on their Kripke frames. 
As to the McKinsey axiom ma, we saw in Section 3.5 that in the class of 
transitive frames it corresponds to the McKinsey condition. Moreover, we will 
show now that the canonical frame for every normal extension of 
K4.1 = K4 0 DOp —> OUp 
satisfies it. To this end we require the following: 
Lemma 5.20 —► □</?*) £ K4.1, for any formulas p\,...,pn. 
Proof Observe first that since (DOp —> OOp) <-» 0(0p —► □ p) £ K (see Table 
3.1), 0(00 —> Up) e K4.1 for any p. Let 0* = Opi —> □</?*, i = 1,... , n. Then 
0-01,.. •, O0n £ K4.1. By RN, OO0i, 00-02 € K4.1 and so OD02 € K4.1. By 
using twice Up A Oq —> 0(p A q) in Table 3.1, we get OO(0i A fa) £ K4.1 and 
so O(0i A fa) £ K4.1, since OOp —> Op is in K4. Now by applying the same 
argument to O(0i A fa) and 003, we obtain O(0i A fa A fa) £ K4.1 and so 
forth. Eventually we shall have O(0i A ... A 0n) £ K4.1. □ 

THE FILTRATION METHOD 
139 
Theorem 5.21 Suppose L E NExtK4 is consistent and contains ma. Then 
3x = (Wl,Rl) satisfies the McKinsey condition 
Vx3y (xRLy AVz (yRLz -» y = z)). 
Proof Let to = (ro, A0) be a tableau in Wl■ Consider the tableau t' = (T', 0) 
with 
T' = {p: Dip E To} U {Op Op : p E ForMC} 
and show that it is L-consistent. Suppose otherwise. Then 
<P, Opi -> Opu • • • , Opn -> Upn hL _L, 
for some Up e To and pi,.",pn € For MC. By the deduction theorem and the 
regularity rule, it follows that 
n 
\-L Up -» f\(Opi -» Opt), 
i—1 
and so 
n 
-•O f\{Opi —> E To, 
i= 1 
contrary to Lemma 5.20. 
Now take a maximal L-consistent extension t\ = (Fi,Ai) of t'. Clearly 
toRLh• We are going to show that either t\ itself or any € tit bas no proper 
successors. Indeed, otherwise we have three tableaux ti = (I\, A^) in Wl, for 
2 = 1,2,3, such that t2 ^ t$ and But then there is a formula p such 
that peT2 H A3 and so, by the transitivity of Rl, E T1 and Dy? E Ai, 
whence Op —> Dy? E Ai, contrary to t\ being L-consistent. □ 
As a consequence of this theorem and results in Section 3.5 we derive 
Corollary 5.22 (i) K4.1 = K4 0 UOp —> OUp is canonical, with 3x4.1 being 
transitive and satisfying the McKinsey condition. 
(ii) S4.1 = S4 0 UOp —► OUp is canonical, with 3rS4.1 being a quasi-order 
satisfying the McKinsey condition. 
5.3 	The filtration method 
The canonical model for a consistent logic L refutes all the formulas which do 
not belong to L. It is very big (contains continuum many points, to be more 
exact) and complicated. On the other hand, the examples of Int and K show 
that each formula p & L may be separated from L by a finite frame. Provided 
that L is finitely axiomatizable, this immediately yields the decidability of L (for 
details consult Section 16.2). 

140 
CANONICAL MODELS AND FILTRATION 
The filtration method is intended to establish such completeness results and 
sometimes it may succeed even if the method of canonical models fails to prove 
canonicity. 
To establish the finite approximability of a logic L, we need to prove that for 
every formula p there is a frame 5 satisfying the following three conditions: (1) 
5 p, (2) 5 is finite, (3) 5 J= L. By Theorem 5.5, to ensure (1) it suffices to take 
the canonical frame 5l for L. It is somewhat more difficult to satisfy (2), but, as 
we saw in Sections 2.4 and 3.4, also possible. Since we are interested only in truth- 
values of p, all the formulas which are not subformulas of p may be discarded 
from the tableaux in Wl. Or better we shall regard tableaux t\ = (Ti, Ai) and 
£2 = (r2,A2) in Wl as Snbp-equivalent if T1 D Subp = T2 Pi Subp. And then 
we see that modulo the Sub<£-equivalence tableaux in Wl mostly duplicate each 
other. More exactly, there are at most 2lSubv?l pairwise non-Sub<£-equivalent 
tableaux in Wl- Is it possible to construct from them some Hintikka system 
fj = (T, 5)? To do this it suffices to define an accessibility relation S so that 
the conditions (HS/1) and (HS/2), if L E Extint, and (HSmI) and (HSm2), 
if L E NExtK, are satisfied. The former of these two conditions can always be 
satisfied, for instance, by taking it as a necessary condition for S. To meet the 
latter, we can use the fact that 3x satisfies it and simply put £iS£2 if 
for some t^t^ £ Wl that are Sub<£-equivalent to t\ and £2, respectively. The 
restrictions thus obtained give in general a spectrum of suitable S. And this is 
very much to the point, since we still need to take care of the condition (3). 
Whether (3) can be met by a proper choice of S depends on the particular logic 
L. So let us first consider in more detail the construction sketched above and 
then apply it to establish the finite approximability of a few superintuitionistic 
and modal logics. 
Suppose we have a model Wl = (5,21) of the language C or MC on a frame 
5 = (W, R) and let E be a set of (£- or MC-) formulas closed under subformulas, 
i.e., Subp C E whenever p e E. We say points x,y E W are E-equivalent in 
and write x y if 
(QJl, x) |= p iff (9Jt, y) |= p, Tor every p £ E. 
Clearly is an equivalence relation on W. Denote by [x]e the equivalence class 
generated by x, i.e., put [z]e = {y € W : x y}- As a rule we will drop the 
subscript E and write simply [x] and x ~ y if this does not involve ambiguity. ‘ 
A filtration of Wl through E is any model 21 = (0,11) based on a frame 
0 = (V, S) such that 
(i) V = {[x] : x G W}; 
(ii) it(p) = {[x] : x G 2J(p)}, for every variable p G E; 
(iii) xRy implies [x]5[t/], for all x,y E W; 
(iv) if [x]5[y] then y \= p whenever x f= □(/?, for x, y G W and Op e E, 
in the modal case and 

THE FILTRATION METHOD 
141 
(iv') if [x]S[y] then y\=p whenever x |= p, for all x, y £ W and 
in the intuitionistic one. 
Theorem 5.23. (Filtration) Let be a filtration of a model DJI through a set 
of formulas E. Then for every point x in DJI and every formula p e E, 
W,x) ^p iff (%[x\) h^- 
Proof The proof proceeds by induction on the construction of p. The basis of 
induction follows from (ii). Now let p == D0 £ E and x |= p. To prove [x] \= p, 
we need to show that [y] |= 0 for every successor [y] of [x]. So suppose [x]5[t/]. 
Then, by (iv), y |= 0 and, by the induction hypothesis, [y] |= 0. Conversely, let 
[x] 	|= D0. Take any y £ x\. Then, by (iii), [x]5[t/] and so [y] |= 0, whence, by 
the induction hypothesis, y f= 0. The induction step for p = 0 A x, P — 0 V x 
and p = 0 —> x ln the modal case follows immediately from the truth-definition 
and the induction hypothesis. 
The intuitionistic case is considered analogously by using (iv') instead of (iv). 
□ 
In general, the conditions (iii) and (iv) (or (iv')) do not determine S uniquely. 
Actually, they allow us to choose any relation S in the interval S C S C 5, where 
S = {([x], [j/]) : 3x',j/' £ W {xf ~x A yf ~ y Ax'Ry')}, 
S = {(Mi [y]) : Vn<^ G E (x |= Hip -> y |= <p)} 
or, in the intuitionistic case, 
S = {(M, [y]) : Vp eYi(x\=p-^y\= p)}. 
Indeed, if [x]S[y] holds then, by (iv) and (iv'), [x]5[t/]. And if [x]5[t/] then x'Ry', 
for some xf £ [x], yf £ [y], and so, by (iii), [x]5[t/]. The fact that 5 satisfies (iv) 
or (iv') and S satisfies (iii) follows directly from the truth-definition in modal 
and intuitionistic models. 
For this reason the filtration on the frame 0 = (V, 5) is called the finest or 
the least filtration of DJI through E, while the filtration on the frame 0 = (V, S) 
is called the coarsest or the greatest 
It is to be noted that a relation S between 5 and S may be nontransitive 
even if the original R is transitive, in particular, not all S in this interval give 
rise to filtrations of intuitionistic models. To construct a transitive relation we 
can take the transitive closure S_ of 5, i.e., put 
5 = {([x],[y]>: 3n > 0 [*]£"[»]}. 
Clearly 5 satisfies (iii). To prove (iv), suppose [x]S[y] and x |= □</?, for some 
x, y in DJI and Up in E. Then there is a finite sequence of points [u],..., [u] 

142 
CANONICAL MODELS AND FILTRATION 
such that [x]5[u]5... S[v]S[y]. By the definition of S, x'RvI for some x' and 
u' that are E-equivalent to x and u, respectively. Since R is transitive and by 
Proposition 3.6, we then have u' |= U+p and so u |= U+p. Using the same 
argument for the sequence u,..., v, y, we shall eventually obtain y |= U+p. The 
intuitionistic models are considered analogously. Observe that in this case 5 as 
well as S are partial orders. 
Alternatively we can define a transitive filtration = (0,il) of a transitive 
modal model 9ft through E by taking, for any x and y in 9ft, 
[x]5[t/] iff y |= U+p whenever x |= Up, for all Up E E. 
It should be clear that the frame 0 = (V, S) is transitive and that is a filtration 
of 9ft. It is called the Lemmon filtration o/9ft through E. 
A very important property of filtrations is that they are finite whenever the 
“filter” E is finite. Moreover, a filtration may be finite even if the filter E is 
infinite. Say that a set E is finitely based over a model 9ft if there is a finite set 
of formulas A, a finite base of E over 9ft, such that 
V-0 E E 3x £ A 9ft |= xjj «-* x- 
For example, since Cl is locally tabular (see Theorem 1.29), the Boolean closure, 
i.e., the closure under A, V, —_L of every finite set of modal formulas is finitely 
based over any model. (However, this is not so in the intuitionistic case.) 
Proposition 5.24 Suppose 9^ is a filtration of a model 9ft through a set E which 
is finitely based over 9ft and A is a finite base of E. Then 9^ contains at most 
2^AI points. 
Proof Clearly, two points are E-equivalent in 9ft iff they are A-equivalent. So 
the number of pairwise non-E-equivalent points in 9ft is not greater than the 
number of subsets in A. □ 
As a consequence of Theorem 5.23 and Proposition 5.24 we obtain 
Corollary 5.25 Suppose 9H is a countermodel for p and E a finitely based over 
9ft set of formulas closed under subformulas. Then every filtration of 9ft through 
E is a finite countermodel for p. 
Thus, to prove the finite approximability (the finite model property, to be 
more precise) of a logic L, it suffices to show that for every formula p £ L there 
is a filtration 9^ of some countermodel 9ft for p through some finitely based (over 
9ft) filter E containing p such that 9^ |= L. If this is really the case then we say 
that L admits filtration. 
Corollary 5.26 If a logic L admits filtration then L is finitely approximable. 
The following two remarks are relevant here. First, if a logic L is sound with 
respect to the class of frames satisfying a property V, then to prove that L 
admits filtration it is sufficient to show that for every p £ L there is a filtration 

THE FILTRATION METHOD 
143 
= (0,11) of DJlL (or some other countermodel for p) through some finitely 
based E containing p such that 0 satisfies V. Second, it turns out that when 
filtrating the canonical model DJIl, we have no real choice for S. For the following 
proposition holds: 
Proposition 5.27 Suppose = (0,11) is a filtration of the canonical model 
DJIl = (S'x/j^l) through E such that Dl \= L. Then is the finest filtration of 
DJIl through E. 
Proof Let 0 = (V,S). We need to show that S C 5, i.e., for any [x], [y] e V 
such that [x]S[y], there are xr,yr £ Wl for which x' ~ £, y' ~ y and x'R^y’. 
Consider the tableaux t\ = (Ti, Ai) and t<i = (T2, A2), where 
ri = {¥J: (91,[*]) (= ¥>}, Ai = {¥>: (%[x)))£<p}, 
r2 = {^: (9t,[y]) |= <p}, A2 = W- (9l,[y])^<^}. 
Since |= L, both t\ and t2 are L-consistent and so belong to Wl. And since 
[x]S[y], we must have t\RLt2- □ 
We are in a position now to prove the finite approximability of a few modal 
and superintuitionistic logics using the filtration method. 
First of all, since our basic logics Int and K are characterized by the class of 
all frames, they trivially admit filtration. 
Next, let us observe that, by (iii), every filtration of a reflexive or serial model 
is reflexive or serial too. More generally, if the underlying frame of a model DJI 
satisfies some condition expressed by first order formulas (with R and = as their 
only predicates), containing no occurrences of —> and _L—such formulas are called 
positive—then (iii) guarantees that the underlying frame of every filtration of DJI 
also satisfies this condition, which can readily be proved by induction on the 
construction of the first order positive formulas. In fact, this is a consequence 
of the result in classical model theory according to which positive formulas are 
stable under homomorphisms (see Chang and Keisler, 1990, Theorem 3.2.4). 
Thus we have 
Theorem 5.28 If a normal modal or superintuitionistic logic L is characterized 
by the class of frames satisfying some first order positive formulas in R and = 
then L admits filtration and so is finitely approximable. 
Proof The detailed proof is left to the reader as an exercise. □ 
Corollary 5.29 The logics D, T and S5 are finitely approximable and 
decidable. 
Proposition 5.30 The finest filtration of every symmetrical model is also 
symmetrical. 
Proof Suppose Dl = (0,11) is the finest filtration of a model DJI based on a 
symmetrical frame £ = (W,R) and [x]S[y], for some points [x], [y\ in 0. Then 

144 
CANONICAL MODELS AND FILTRATION 
by the definition of 5, there are x' E [x] and y' E [y\ such that x'Ry', from which 
y'Rx' and so, by (iii), [y]S[x]. □ 
As a consequence of Proposition 5.30 and Theorem 5.17, according to which 
KB is characterized by symmetrical frames, we obtain 
Corollary 5.31 KB admits filtration and so is finitely approximable and 
decidable. 
Using the transitive closure of the finest filtration or the Lemmon filtration 
and the fact that K4, D4 and S4 are characterized by the classes of transitive 
frames, serial transitive frames and quasi-orders, respectively, we immediately 
obtain 
Corollary 5.32 The logics K4; D4; S4 admit filtration and so are finitely 
approximable and decidable. 
Also we have 
Theorem 5.33 The logics K4.2, K4.3, S4.2, S4.3, KC, LC admit filtration 
and so are finitely approximable and decidable. 
Proof We show how to establish this result only for K4.2. The other logics are 
considered analogously. 
By Theorem 5.17 and the generation theorem, K4.2 is characterized by the 
class of rooted transitive directed frames. So it suffices to show that, for every 
model DJI based on such a frame $ = (W,R) and a finite filter E, there is a 
filtration of DJI through E which is also based on a transitive directed frame. 
Take the transitive closure of the finest filtration of DJI through E. Let S 
be the accessibility relation in 01 and let [x]5[t/] and [x]5[z], for some points [x], 
[y], [z] in 01 such that [y] ± [z]. Then uRy', vRz', for some y' ~ y, zf ~ z, u and 
v. Clearly, yf ^ zf. Since # is rooted and transitive, both yf and zf are seen from 
the root of $ and so, by the directedness condition, there is w such that y'Rw 
and z'Rw, from which [y]S[w] and [z}S[w]. □ 
Remark It is worth noting that although S4.3 is characterized by the class of 
linear partial orders, it is not characterized by the class of finite linear partial 
orders. For example, the Grzegorczyk formula is refuted by a proper cluster or 
an infinite ascending chain and so does not belong to S4.3. On the other hand, 
it is valid in every finite partial order. It follows in particular that by filtrating 
linear orders we may obtain chains with proper clusters. 
Our next two results are a bit more complicated. They demonstrate situations 
when we have to filtrate models through sets which are bigger than the set of 
subformulas of the refuted formula. 
Theorem 5.34 The logics K4.1 and S4.1 admit filtration and so are finitely 
approximable and decidable. 
Proof We consider only K4.1, leaving S4.1 to the reader as an exercise. 
According to Corollary 5.22, K4.1 is characterized by the class of transitive frames 

THE FILTRATION METHOD 
145 
satisfying the McKinsey condition. So, given a countermodel DJI for ip on such a 
frame #, we must construct a transitive filtration 91 of DJI through some finite 
set E D Sub(p such that every final cluster in 91 is simple. Observe at once 
that, by (iii) and the McKinsey condition, no filtration of DJI contains dead ends. 
Thus, our only problem is to avoid final proper clusters in 91. We recommend the 
reader first to try filtrating DJI through Subip to understand that under such a 
filtration two final simple clusters in DJI may be put into one proper cluster in 91. 
To prevent this, we should take a smaller accessibility relation in our filtration 
which can be done by choosing a bigger filter E. 
Define E as the closure under subformulas of the set 
{□0-0, OD0 : 0 G Sub(^} 
and let 91 be the transitive closure of the finest filtration of DJI through E. Suppose 
[x] and [y] belong to a final cluster in 91 and show that [x] = [y]. According to 
the filtration theorem, it suffices to establish that [x] ~ [y]. 
Take a formula 0 G E. If 0 = U\ or 0 = Ox then, by Proposition 3.6, [x] |= 0 
iff [y] |=0. So the only remaining case is 0 G Sub<p. Suppose [x] |= 0. Then 
00 is true in 91 at every point in the cluster containing [x]; so [x] |= DO0 and 
x |= DO0. Since DJI is a model for K4.1, we must then have x |= OD0 and hence 
[x] |= OD0. Therefore, there is a point [z] in the cluster under consideration such 
that [z] |= D0 and so [y] |= 0. □ 
Theorem 5.35 The logic K5 admits filtration and so is finitely approximate 
and decidable. 
Proof By Theorem 5.17, K5 = K©0Up —> Up is characterized by the class of 
Euclidean frames. Let DJI be a countermodel for a formula ip based on a Euclidean 
frame. Again, a filtration of DJI through Sub(p need not be Euclidean. So let us 
try a bigger filter, say, 
E = Sub(p U {OD0 : CU0 G Sub<^}. 
Let 91 be the coarsest filtration of DJI through E. We show that its underlying 
frame 0 = (V, S) is Euclidean. 
Suppose [x]S[y] and [x]5[^], for some [x], [y], [z] G V, and prove that [t/]5[;z]. 
By the definition of 5, we need to show that [y\ |= D0 implies [z] |= 0, for every 
□0 G E. So let D0 G E and [y] |= D0. Then [x] |= OD0 and, by the filtration 
theorem, x J= OD0, from which x \= D0, since DJI is a model for K5. Therefore, 
[x] |= D0 and [z] |= 0. □ 
Remark Since K5 has finitely many distinct modalities (see Exercise 5.10), 
the modal closure, i.e., the closure under prefixing □ and O, of every finite set 
of formulas is finitely based over any model for K5. So instead of E in the proof 
above we might use the modal closure of Sub ip. 
Theorem 5.36 For every variable free formula 0, the logic K 0 0 admits 
filtration and so is finitely approximate and decidable. 

146 
CANONICAL MODELS AND FILTRATION 
Proof Since ip contains no variables, every flirtation of a model for K ® ip 
refuting p through SubpUSubi/j is also a model for K®^ in which p is refuted. 
□ 
It should be clear that instead of K in Theorem 5.36 we can take any other 
logic considered in this section. 
5.4 	Diego’s theorem 
The bigger the filter, the more properties of the initial model will be inherited 
by its filtration and the more chances that the filtration will be a model for the 
logic under consideration. In this section we show that the closure of every finite 
set of intuitionistic formulas under A, —> and _L (or -») is finitely based over 
any intuitionistic model and so can be exploited as a filter for establishing the 
finite approximability of superintuitionistic logics. This very useful result is an 
immediate consequence of the following: 
Theorem 5.37. (Diego’s theorem) For every n > 0, the set Sn of formulas, 
constructed from the variables pi,... ,pn using A, —> and _L, contains only finitely 
many pairwise non-equivalent in Int formulas. 
Proof The proof proceeds via a number of lemmas and requires some auxiliary 
definitions. 
To begin with, we form the coarsest filtration 9Jt = (#,93) of the canonical 
model for Int through En. We will regard points t in # = (W,R) as tableaux 
t = (T, A) such that 
r={^eH„: A = {<peEn: 
For an atomic p e Sn, call such a tableau t = (T, A) p-prime (relative to En) if 
p e A and, for every p e Sn, either per or p —> p er. 
Lemma 5.38 For any atomic p e Sn, any t = (T, A) e W and any p e Sn, if 
p —> p e A then there is a p-prime successor t* = (T*, A*) oft in # such that 
<peT*. 
Proof Since <p —> p e A, there must be a point t\ = (Ti, Ai) accessible from 
t in # for which p e Ti, p e A\. Let X be a maximal chain of points in # 
refuting p and such that t\ e X. Put T* = U(r',A')€X F', A* = Sn - T* and 
t* = (T*, A*). The tableau t* is, Int-consistent, for otherwise we would have 
Pi A ... A Pk —» ipi V ... V ipi e Int, for some pi,...,pk G P\ ip\,...,ipi G A*. 
But then, since X is linearly ordered and by (HS/1), there exists t' = (T', A') e X 
such that pi,... ,pk e T', ipi,..., ipi e A', contrary to the Int-consistency of tf. 
Therefore t* is a point in #. In fact, it is the final point in X. Besides, we clearly 
have peT* and tRt*. It remains to observe that t* is p-prime. Indeed, by the 
definition, p e A* and if ^ and ^ > p are in A* then there is a successor tf of 
t* such that t' |= ip, t* p, from which tf = t*, for otherwise we can extend the 
chain X by adding t' to it, contrary to its maximality. □ 

DIEGO’S THEOREM 
147 
Let V be the set of all p-prime tableaux in W, for all atomic p G Sn, S the 
restriction of R to V and 0 = (V, S). 
Lemma 5.39 For any t = (T, A) G W and any p e A, there is a tableau 
t* = (r*, A*) in V such that tRt* and p G A*. 
Proof Observe first that, by the intuitionistic equivalences 
P *-* ((-1- -L) ~*P), (P (q-> r))(p A q r) 
and 
(p —* q hr) *-* (p q) A (p r), 
p is equivalent in Int to a formula of the form f\i(fa —♦Pi), for some atomic 
Pi G En and fa G Sn. Therefore, fa —»pi G A, for some z, and so, by Lemma 5.38, 
there is ap^-prime tableau t* = (T*, A*) accessible from t and such that fa G T*. 
It follows immediately that p G A*. □ 
As a consequence we readily derive that 0 = (V, S) is a Hintikka system 
characterizing En in the sense that, for every <p G Sn, <p is in Int iff <p G T, for 
all (T, A) in V. 
Our goal now is to show that 0 is finite. 
Lemma 5.40 If t = (T, A) is a p-prime tableau and tf = (r',A') a proper 
successor oft in 0 then p G T'. 
Proof Since t ^ t' and tStf, there must be some p G P — T. And since t is 
p-prime, —> p G T. Therefore, (p —> p G P and so p G T'. □ 
Suppose t = (r, A) is a p-prime tableau in 0, for some p^pn, and pn G T. 
Form a tableau t' = (P, A') by taking 
r' = {p G r : Pn ^ Sub(p}, A' = {p G A : pn ^ Sub<p}. 
Clearly t' is a p-prime tableau relative to Sn-i. It turns out that t is uniquely 
determined by tf and pn in the following sense. 
Lemma 5.41 T = {p G Sn : r',pn bInt p}. 
Proof It suffices to show that r',pn ^~int for every p G T. So let p be an 
arbitrary formula in T and p' = p{T/pn}. By the strong completeness theorem 
for Int, we have pn bint pf p. It follows that pf G T. Hence pf G T' and so 
I'' 5 Pn p. Ql 
We are in a position now to prove the crucial 
Lemma 5.42 0 is finite. 
Proof The proof proceeds by induction on n. If n = 0 then, according to 
Corollary 2.27, 0 contains only one point. 
Suppose now that n > 0. By the induction hypothesis and Lemma 5.41, there 
are finitely many tableaux (T, A) in 0 such that p G T, for some atomic p G Sn. 

148 
CANONICAL MODELS AND FILTRATION 
(The variables may be renamed to use Lemma 5.41.) So it is sufficient to show 
that there is a finite number of tableaux t = (T, A) in 0 containing all pi,... ,pn 
in A. By Lemma 5.40, every such point t has no predecessors in 0. And by the 
generation theorem and the fact that all pi are in A, t is uniquely determined by 
the set of its proper successors in 0. Since, as we have already established, only a 
finite number of such sets exists, there are only finitely many distinct t = (T, A) 
with Pi,... ,Pn € A. □ 
It is not difficult now to complete the proof of Diego’s theorem. Since 0 
characterizes Sn, for any G Sn we have 0 £ Int iff for every (T, A) 
in 0, (p and 0 simultaneously belong either to V or to A. Ergo the number of 
pairwise non-equivalent in Int disjunction free formulas built from _L,pi,... ,pn 
is not greater than the number of subsets in V, that is 2^v\. □ 
As a direct consequence of Diego’s theorem we obtain 
Corollary 5.43 Suppose E is a finite set of intuitionistic formulas. Then the 
closure of E under A, —> and _L contains finitely many pairwise non-equivalent 
in Int formulas and so is finitely based over any intuitionistic model. 
We take advantage of this result to establish the finite approximability of 
the Kreisel-Putnam logic KP. In Section 7.3 we shall use it to prove the finite 
approximability of an infinite family of si-logics. 
Theorem 5.44 The Kreisel-Putnam logic 
KP = Int -f (-»p —> q V r) —► (-»p —» q) V (-»p —> r) 
admits filtration and so is finitely approximable and decidable. 
Proof Suppose p £ KP and Wl is a model for. KP refuting (p. Let E be the 
closure of Subp under —A and _L, and A a finite base of E over 9JI. 
Construct the coarsest filtration 9t = (0,11) of 9JI through E. By Proposition 5.24, 
Corollary 5.43 and the filtration theorem, 9t is a finite countermodel for p. 
To prove that 0 = (V, S) is a frame for KP, we show that it satisfies the 
first order condition for kp given in Exercise 2.10. Suppose otherwise. Since 0 
is finite, we then have points [x], [y], [z] £ V such that [x]5[t/], [x]5[^], [y] and [z] 
do not see each other and every successor [u] of [x], seeing both [y] and [z] (in 
particular [x] itself), sees a final point [w] in 0, which is not accessible from [y] 
and [z]. Let [uq],..., [wn] be all the final points in 0 that are seen from [x] and 
are not seen from [y] and [z]. According to our assumption, n > 0. 
For a point [v] G V, denote by yv the conjunction of all the formulas in A 
that are true at [v] and by 6V the disjunction of those formulas in A that are false 
at [v] in 91. Put 7 = Vr=i an(^ consider the following substitution instance 
of kp: 
« = ("*7 —> 8y V 6z) —> (->7 Gy) V (“O' 6z)- 
Since ffll \= KP, we have (971, x) f= k. Also we must have x -17 —> Sy and 
x Sz. Indeed, if for instance x |= -17 —» Vi 0*» where 0* are the formulas 

SELECTIVE FILTRATION 
149 
in A that are false at [y], then by using kp a sufficient number of times we 
obtain that x \= VO and so x f= -<7 —> for some i. And since -17 is 
equivalent in Int to /\^=1 -<7w. G E, we conclude by the filtration theorem that 
[x] |= ~<7 —> 'ipi- On the other hand, we have [y] \= -17, for otherwise there is a 
point [v] accessible from [y] and such that [v] |= 7Wi, for some z, and so [u;i]S[?;], 
which is possible only when [wi] = [v], since [wi\ is final in 0. It follows that 
[y] |= which is a contradiction. 
Therefore, x -<7 —► 6y V 6Z and so there is u G x] such that u f= -17 and 
u ^ Sy V 6Z. Then [a;] S'[it], [it] |= -<7 and [u] ^ SyV 6z, from which [it]S[y] and 
[it]S[z], since is the coarsest filtration of DJI. Take a point [wi\ G [it]|. Clearly 
[m] |= Iwi and so [u] ft -<7^, contrary to [u] |= AILi □ 
Remark In Section 18.2 we shall show that there are formulas p £ KP whose 
smallest refutation frames validating KP contain at least 22'Sub<^ points. This 
means that by filtrating DJI through Subp we could not establish the finite 
approximability of KP. 
5.5 	Selective filtration 
If we want to use the filtration method for establishing the finite approximability 
of a logic L without knowing any non-trivial completeness results for it, we have 
no other choice but to filtrate the canonical model DJIl through some set of 
formulas E. However, this may yield no result no matter what E we choose, even 
if L is really finitely approximable. For example, as we shall see below, GL is 
characterized by the class of finite strict orders, but the canonical frame #gl 
contains a reflexive point, and so by (iii) in Section 5.3, every filtration of 9JIgl 
has a reflexive point as well. 
When filtrating a model or better a Hintikka system S) through E, we divide 
the tableaux in into E-equivalence classes, identify the tableaux in each class 
and try to project the accessibility relation in S) to the resulting finite set of 
tableaux so that we again could obtain a Hintikka system. Yet there is another 
way of constructing finite Hintikka systems starting from $)\ instead of factorizing 
^ we may try to extract a finite subsystem of S) by selecting some suitable 
points in the E-equivalence classes in accordance with the rules for constructing 
Hintikka systems. This method is known as selective filtration. We use it here to 
establish the finite approximability of GL, Grz and Tn. (By the way, none of 
these logics, except Ti, is canonical.) 
A general scheme of selective filtration, which will be enough for our purposes, 
may be described as follows. Suppose L is a modal or superintuitionistic logic 
and p £ L. Then there is a model DJI = (#, 2J) separating p from L, i.e., DJI p 
and DJI |= L. Suppose also that a set of formulas E is finitely based over DJI, 
closed under subformulas and contains p. We may think of # as the Hintikka 
system $ = (W, R), with points t £ W being the tableaux t = (T, A), where 
T = {V>€E: (DJl,t) bV'}, A = {V>eE: {DJl,t) if}. 

150 
CANONICAL MODELS AND FILTRATION 
We start our selective filtration of 9Jt through E by selecting a tableau t = 
(T, A) in W such that p € A. The tableau t will be the root of the finite Hintikka 
system we are going to extract from *Dl. It may turn out that the pair S) = (T, S), 
where T = {t} and S is the restriction of R to T, is already a Hintikka system. In 
this situation we are done. Otherwise there are formulas D0 G A (0 —> X £ A, 
in the intuitionistic case) such that either 0 ^ A or not tSt (respectively, 0 ^ T). 
Denote by 0* the set of all formulas of that sort. Now, at the second step for 
each D0 G 0* (respectively, 0 —> x € 0*), we select a tableau t' = (T', A') in W 
such that tRt' and 0 G A' (respectively, 0 G T' and x € A'). Denote by Tt the 
set of all selected successors of t. Then we add Tt to T, thus obtaining a set T', 
take the restriction S' of R to T' and check whether ft' = (T', S') is a Hintikka 
system. If this is not the case then, for each t' G Tt, we consider formulas in 
0*/, select a set Tt> of suitable successors of t', add it to T', and so on till we 
reach tableaux t* with 0** = 0. If we succeed then the resulting Hintikka system 
$)* = (T*,S*) will certainly refute ip. 
Two points are essential in this construction. First, we must ensure somehow 
that the process will eventually terminate. For example, we may try to select 
successors t' of each tableau t in such a way that 0*/ contains less formulas than 
0*. And second, to separate ip from L, $)* must be a frame for L. In that respect 
the definition of the accessibility relation in $)* as the restriction of R to T* may 
be too severe. For in fact, to obtain a Hintikka system, it is sufficient to define on 
T* any relation S in the interval 5* C S C 5*, where tS*t' iff either t — t' and 
tRt' or t' G Tt (of course, in the intuitionistic case S must be a partial order). 
We now apply this scheme to prove the finite approximability of 
GL = K4 © □(□;p -+p)-+ Op. 
Using the selective filtration, we will extract from the canonical model QJIql a 
finite submodel that refutes ip GL and contains only irreflexive points, which, 
by Proposition 3.47, is enough to ensure that the model validates the Lob axiom 
la. 
The following observation is the key to the filtration. 
Lemma 5.45 Suppose x ^ D0 for some point x in a model 9JI for GL. Then 
there is an (irreflexive) point y G x] such that y ^ 0 and y f= D0. 
Proof Since every substitution instance of the Lob axiom is true in 9JI, we have 
x |= □(□0 —> 0) —> D0. Therefore, x ^ □(□ 0 —> 0) and so there is y G x] such 
that y |= D0 and y ^ 0. Clearly, y is irreflexive. □ 
Theorem 5.46 GL is characterized by the class of finite strict partial orders. 
Proof It suffices to show that every formula ip ^ GL is refuted by some finite 
strict partial order 0 = (V,5). We construct it according to the scheme above 
by filtrating through E = Sub ip. 
Observe first that there is an irreflexive point Xo in QJIql suc^ xo W- 
For there must be x in QJIgl refuting ip, and if x is reflexive then x ^ Up and 
we can use Lemma 5.45. 

SELECTIVE FILTRATION 
151 
We define 0 by induction. Put Vo = {xo} and 0Xo = {□'0 G E : xo \£ a0}* 
Suppose now that Vn = {xi,... , xm} has been already constructed. If @Xi = 0 
for alH = 1,..., ra, then let V = (J”=0 V? and & restriction of Rql 
Otherwise, for each x» with 0X. ^ 0 and each D-0 G 0Xi, we select according to 
Lemma 5.45 an irreflexive point y G xf\ such that y ^ 0 and t/ |= Let V^+i 
be the set of the selected points y. 
Since |0y| < |0XJ (because #gL is transitive) and E is finite, we must 
eventually reach a set Vk whose points validate all the boxed formulas in E, i.e., 
Qx = 0 for every x G V^. By the construction, the resulting frame 0 is a strict 
partial order and 0 ^ p. □ 
Corollary 5.47 (i) GL is characterized by the class of Noetherian strict orders. 
(ii) GL is characterized by the class of finite strictly ordered trees. 
Proof Follows from Theorem 5.46, Proposition 3.47, Exercise 3.12 and the 
reduction theorem. □ 
It is somewhat more difficult to prove the finite approximability of the Grze- 
gorczyk logic 
Grz = K© U(U(p —> Op) —5► p) —5► p. 
First we observe that the canonical frame for Grz satisfies two good properties: 
Proposition 5.48 $gtz reflexive and transitive. 
Proof Suppose there is x in #Grz such that x ^ x|. By the definition of 
canonical model, this means that x f= Up and x ^ p, for some formula p. But 
then x □ (□(</? —► □<£>) —► p) —*► <p, contrary to WIqrz 1= Grz. Thus, TIqtz is 
reflexive. 
Now let us prove that Up —► map g Grz. By Theorem 5.16, it will follow 
that #Grz is transitive. Suppose otherwise. Then x ^ Up —► DOp and so x p, 
where p = (p A -'□p) V OOp, for some point x in SDlcrz* We will show that in 
this case x f= □ (□(<£> —> Up) —► p). 
Suppose otherwise. Then there exists y G x| such that y |= U(p —> Up), 
y \= Up and y UUp (for if y ^ p then x ^ Dp, which is a contradiction). 
Besides, there is z G y] for which z \= p —> Up, z \= p and z ^ Up. Therefore, 
z |= p and z f= Up. Now we have u G z\ such that u f= (p A -'□p) V DDp 
and u p. By the reflexivity, u UUp and hence u f= p A -idp, which is a 
contradiction. 
Thus x ^ □ (□(</? —5► E<p) —J► <p) ~^ <P, contrary to SDlcrz being a model for 
Grz. □ 
Corollary 5.49 Grz = K4 0 grz = S4 0 grz. 
According to Proposition 3.48, to establish the finite approximability of Grz, 
given a formula p Grz, we need to extract from 9D?Grz a finite partially 
ordered countermodel for p. The following lemma shows in particular that when 
filtrating 9JIqtz through E = Sub<p we may choose successors of a point x in 
clusters different from C(x). And if two or more successors appear in the same 

152 
CANONICAL MODELS AND FILTRATION 
non-degenerate cluster, we simply shall not take into account the accessibility 
relation between them. 
Lemma 5.50 Suppose e E, x f= ^ and x for some point x in WlGrz. 
Then there is a point y £ xj such that y i/j and z x for no z £ yj\. 
Proof Suppose otherwise. Then for every y £ x| such that y ^ there is a 
point z £ y] which is E-equivalent to x and so z |= ip and z ^ Uif). It follows 
that x |= □(□(^ —> U^) —> ^;). 
Sihce x ^ CIV>, there is y £ x\ such that y and since #Grz is transitive, 
y |= □(□(^ —> D^) —> tf))^ contrary to QJlcrz H Grz. □ 
We are in a position now to prove 
Theorem 5.51 Grz is determined by the class of finite partial orders. 
Proof Given a formula p $ Grz, take E = Sub p and use the selective filtration 
through E to extract from TIqtz a finite partially ordered frame 0 = (V, S) 
refuting ip. We construct 0 by induction. 
To begin with, we take some point x in OJlcrz such that x p and put 
(So = (Vb,So), where V0 = {x}, S0 = {(a;,a;)}, and 0X = {D^ G E : x ft 
□</> and x |= ty}. Suppose now that we have already constructed a partially 
ordered frame 0n = (VniSn) with Vn C WGtz, Sn C RGrz. Let Xn be the set 
of final points x in <5n such that Qx ^ 0. If Xn = 0 then put 0 = 0n. 
Otherwise for each a; G and each Uif) £ 0X, fix a point y(x, D^) G such 
that y{x1Urijj) ^ xjj and -<3z G y(x,D^)| 2: £ (that such a point exists is 
guaranteed by Lemma 5.50). Put 
Vn+i = VnU {y(x, Dr/)) : x £ Xn and □?/> G 0*}, 
define Sn+1 to be the reflexive and transitive closure of the relation 
Sn u {(a;, y(x, D^)) : x £ Xn and Urf) £ 0n} 
and let 0n+i = (V^+i, 5n+i). It should be clear that 5n+1 C RGrz (but Sn+1 is 
not in general the restriction of Rqtz to Vn+i). 
Notice that 0n+i is a partial order. Indeed, otherwise we would have a cluster 
in 0n+i containing both x and y(x, D^), for some x £ Xn and £ Sx. But 
then y(x, OVO-^Grz^ contrary to our choice of y(a:, D^). 
Since no chain in 0n+i contains distinct E-equivalent points and since E 
is finite, at some step m we shall have Xm = 0, and so our selection process 
will terminate. If we regard points x in 0 as the tableaux tx = (Tx, Ax) with 
rx = {V> € E : (SttGrzjS) 1= V>} and Ax = € E : (TlGrzix) ^ then 0 
will clearly be a Hintikka system. Therefore, <5 p. □ 
Corollary 5.52 (i) Grz is characterized by the class of Noetherian partial 
orders. 
(ii) Grz is characterized by the class of finite partially ordered trees. 

SELECTIVE FILTRATION 
153 
Proof Follows from'Theorems 5.51, 2.19 and Proposition 3.48. □ 
Let us consider now the si-logics 
n n 
T« = Int + /\{(Pi -»• \J Pj) -»• \J Pj) -*• V Pu for n - 1> 
i—0 i^j z=0 
and prove that all of them are finitely approximable. By Proposition 2.41, Tn 
is sound with respect to the class of finite frames of branching < n. We shall 
use the selective filtration to show that Tn is also complete with respect to this 
class. 
Theorem 5.53 Tn is characterized by the class of finite frames of branching 
< n. 
Proof Suppose p ^ Tn and DJI = (5,91) is a model for Tn refuting ¥>• By 
Theorem 2.19 and the reduction theorem, without loss of generality we may 
assume that # = {W, R) is a tree. Let E = Sub p and Tx = {^ £ E : x f= ^}, 
for every point x in Sr. 
Given x in #, put rg(x) = {[y] : y £ x|} and say that x is of minimal range 
if rg(x) = rg(y) for every y £ [x] flxf. Since there are only finitely many distinct 
E-equivalence classes in DJI, every y £ [x] sees a point z £ [x] of minimal range. 
We are in a position now to extract from DJI a finite refutation frame 0 = 
(V, S) for p of branching < n. To begin with, we select some point x of minimal 
range at which ip is refuted and put Vo = {x}. 
Suppose now that Vk has already been defined. If \rg(x)\ = 1 for every x £ Vk, 
then we put 0 = {V,S) where V = U£=o and S is the restriction of R to V. 
Otherwise, for each x £ Vk with \rg(x)\ > 1 and each [y] £ rg(x) different 
from [x] and such that Tz C Ty for no [z] £ rg(x) — {[x]}, we select a point 
u £ [y]n x | of minimal range. Let Ux be the set of all the selected points for 
x and Vfc+i = (JXUX. It should be clear that Tx C Tu (and rg(x) D rg(u)), for 
every u £ Ux, and so the inductive process must terminate. Using the standard 
tableau argument one can readily show also that 0 p. 
It remains to establish that 0 f= Tn, i.e., 0 is of branching < n. Suppose 
otherwise. Then there is a point x in 0 with > n 4- 1 immediate successors 
Xq, ..., xm, which are evidently in Ux because # is a tree. We are going to 
construct a substitution instance of Tn’s axiom bbn which is refuted at x in DJI. 
Denote by 6i the conjunction of the formulas in TXi. Since all of them are 
true at x* in DJI, we have x* |= 6$; and since I\ C Tj for no distinct i and j, we 
have Xj ^ Si if i ^ j. Put Xi — for 0 < i < n, Xn = bn V ... V Sm and consider 
the truth-value of the formula ^ = bbn{xo/Po, • • •, Xn/Pn} at x in DJI. 
Since xRxi for every i = 0,..., m, we have x ^ VILo Xi- Suppose, however, 
that x ^ ASLo((Xi VijijXj) -*• Vi/jXj)- Then y |= x» -+ and 
2/ ^ Vi/j Xj» for some y £ xf and some 2 € {0,, n}, and hence y ^ Xi- Since 
#i 1= Xi and Xi Vz/j Xj) 2/ sees no points in [x^] and so y fa x (for otherwise 

154 
CANONICAL MODELS AND FILTRATION 
x would not be of minimal range). Therefore, TXj C Yy for some j E {0,..., ra}, 
and then y \= \j if j < n and y f= Xn if j > ft, which is a contradiction. 
It follows that x |= A"=o((x» ^ Vi#jXj) V^jXj), from which x ft ip, 
contrary to SJt being a model for bbn. □ 
As a consequence of Theorem 5.53 we obtain the following completeness result 
justifying, by the way, the name Tn of the logics under consideration. 
Corollary 5.54 Tn is characterized by the class of finite n-ary trees. 
Proof Exercise (use the reduction theorem and Exercise 2.5). □ 
5.6 	Kripke semantics for quasi-normal logics 
The Kripke semantics for modal logics we have dealt with so far is suitable 
only for normal extensions of K. Now we use the concept of canonical model 
to introduce in a rather natural way a Kripke semantics for all logics in ExtK, 
including quasi-normal ones. 
Suppose L is a consistent quasi-normal logic. Then the set of formulas 
M = {p e ForMC : Vn > 0 Dnp e L} 
is clearly a normal logic, the greatest one among all normal logics contained in 
L, to be more exact. We call M the kernel of L and denote it by kerL. 
Let DJIm = be the canonical model for M. Each maximal L- 
consistent tableau t is also a maximal M-consistent tableau, and so t is a point 
in - Denote by Dl the set of all maximal L-consistent tableaux. Then by 
Lemma 5.2 which, as we observed, holds for quasi-normal logics as well, we have 
A hl V iff for every (T, A) E Dl, ACT implies ip E T. 
Therefore, by Theorem 5.4, for any A and y?, 
A \~l iff for every t E Dl, (SDTm,^) b A implies (3DTm,£) b (P- 
Of course, instead of M we can take any other normal logic contained in L. 
This result can be interpreted as follows. We distinguish in a set of 
points, namely Dl, and regard them as the only “actual worlds” in 9JIm* A 
formula tp is then assumed to be true in WIm if it is true at all the actual worlds. 
Thus we arrive at the following Kripke semantics for quasi-normal logics. 
A Kripke frame with distinguished points is a pair (Sr, D) where # = (W,R) is 
a Kripke frame and D C W. The points in D are called the distinguished points 
or the actual worlds in Sr. A model with distinguished points (based on (#, D)) 
is a pair (SDt, D) where 9Jt = (Sr, 9J) is an ordinary Kripke model based on Sr. A 
formula (p is said to be true in (SDt, D) (notation: (SDt, D) f= (p) if (9Jt, x) \= (p for 
all x E D. p is valid in (#, D) (notation: (5, D) f= p) if p is true in all models 
based on (#, D). 

KRIPKE SEMANTICS FOR QUASI-NORMAL LOGICS 
155 
Clearly, # f= <p iff* (#, W) |= <p, so a frame # may be identified with (#, VF). 
As to the other extreme case, it follows from the definition that all formulas, 
even J_, are valid in (#, 0). 
The model (9Jtkerl,Dl) and the frame ($kerl,Dl), constructed at the 
beginning of this section, are called the canonical model and the canonical frame 
(with distinguished points) for L, respectively. 
What we have established so far can be summarized as the following: 
Theorem 5.55 Each consistent quasi-normal logic L is strongly characterized 
by its canonical model (9JtkerZo Dl), i-o., for every A and ip, 
A \-Lip iffVx € Dl (x |= A -> X f= ip), 
in particular, 
(p £ L iff (SHkerZo DL) |= (p. 
It is worth noting that a formula ip is true in (SUt, D) iff ip is true in every 
model in the class {(9JI, {d}) : d G D}. So we obtain 
Theorem 5.56 Every consistent quasi-normal logic is strongly characterized by 
a class of models having a single distinguished point 
Given a class C of frames with distinguished points, denote by LogC the set 
of modal formulas that are valid in all frames in C; if C = {(#, D)} then we write 
simply Log(Sr, D). As an easy exercise we invite the reader to prove the following: 
Proposition 5.57 For every class C of frames with distinguished points, LogC 
is a quasi-normal logic. 
To illustrate the introduced semantics for quasi-normal logics we give some 
examples. 
Example 5.58 The first known quasi-normal, but not normal extension of S4 
was 
S4.1' = S4 4- DOp -> OOp. 
To understand why S4.1' is not normal, let us consider the frame $ shown in 
Fig. 5.1 (a) with actual world 0. Since $ does not satisfy the McKinsey condition, 
it refutes ma and so (#, 0) ^ Dma. However, (#, {0}) f= ma, for otherwise we 
would have (under some valuation) 1 ^ ma, which is impossible. Therefore, 
S4.1' C Log^, {0}). On the other hand, Dma ^ Log^, {0}), which means 
that S4.1' is not closed under necessitation. 
Theorem 5.59. (Scroggs’ theorem) All logics in ExtS5 are normal. 
Proof It is enough to show that every quasi-normal extension L of S5(n) in the 
language with n < u variables is normal. According to Theorem 5.55, L is 
characterized by (9Dls5(n)> Dl), which in view of Corollary 5.19 is finite. Using the dif- 
ferentiatedness and finiteness of ^sscn) it is readily shown (see Exercise 5.3) that 
L is characterized by the frame (tfsscn)* Dl)- Let £ be the subframe of £35(n) 

156 
CANONICAL MODELS AND FILTRATION 
1 
3 Vo 
(a) 
0 ouj 
(b) 
Fig. 5.1. 
generated by Dl- Then L = Log (#, Dl) and so, as is easy to see, L = Log#. 
Example 5.60 As we observed in Section 3.8, there is no Kripke frame 
validating all formulas in Solovay’s logic S = GL + Op —> p. It follows in particular 
that S has no consistent normal extensions. For the same reason no Kripke 
frame with distinguished points can validate S. Logics with this property may 
be called Kripke inconsistent All consistent extensions of S, if any, are clearly 
Kripke inconsistent. 
Moreover, there is no (normal) Kripke model for S. For by Lemma 5.45, every 
model DJI for GL contains a final irreflexive point x. (Indeed, if y is not a dead 
end in DJI then y □_!_ and so x \= □_!_ for some x G y].) But then x □_!_ —> _L. 
We construct now a model with a distinguished point for S, which shows by 
the way that S is consistent. Let 0 = (V, S) be the (transitive) frame depicted 
in Fig. 5.1 (b), or formally 
Define a valuation it in 0 by taking it(p) = V, for every variable p. Observe first 
that all substitution instances of the Lob axiom are true in the (normal) model 
DJI = (0,il). Indeed, all of them are clearly true at all irreflexive points in DJI. As 
to u, one can readily prove by induction op the construction of (p that if u \= ip 
(or u \f= ip) then there is some n < u such that m \= ip (respectively, m j^= <p), 
for all m G {n, n + 1,... ,u;}. So if a substitution instance of the Lob axiom is 
false at u then it is also false at some irreflexive point n which, as we know, is 
impossible. 
Thus, DJI |= GL. Now, let us observe that (DJl,w) \= □(/? —> <p, for every 
formula <p, simply because u is reflexive. So if we distinguish u as the only 
actual world in DJI then we obtain that (DJI, {a;}) |= S. 
We use this observation to prove the following: 
Theorem 5.61 For every modal formula ip, 
□ 
<& = {{i: i < w},{(w,w) ,(j,i) : 0<i<j<w}). 
<p € S iff A (Uijj —► \jj) —► <p g GL. 
□•0€Sub<^ 

EXERCISES 
157 
Proof The implication (<=) is evident. To prove (=>), suppose 
A VO -*• <P $ GL. 
nipeSub <p 
Since GL is finitely approximable, this formula is refuted at the root x of some 
finite frame # = (W, R) for GL under some valuation. Construct a new frame 
0 by adding to $ the infinite chain depicted in Fig. 5.1 (b) so that it could see 
all points in # and define a valuation in 0 in such a way that the truth-value 
of each variable remains the same at all points in # and at points in the added 
chain it coincides with that at x. By induction on the construction of xe Sub ip 
and using the fact that x |= An^eSub—5► VO one can show that y \= x 
iff x \= X) for every y £ x{. Since the root of 0 is reflexive, it follows that 
An^GSub^C^ —► VO —► ip is false at it. And that every substitution instance of 
la is true there is checked in the same way as in Example 5.60. □ 
5.7 	Exercises 
Exercise 5.1 Show that K ® ma = D ® ma. 
Exercise 5.2 Construct modal and intuitionistic models that are not 
differentiated (tight, compact). 
Exercise 5.3 Show that if DJI = (#, 21) is a differentiated finite model for a logic 
L then # is a frame for L. Use this to prove that a logic is finitely approximable 
iff it has the finite model property. 
Exercise 5.4 Show that GL.3 = GL ® con is characterized by the class of 
finite strict linear orders and by the frame (u, >). 
Exercise 5.5 Show that K4Z = K4®z is characterized by the class consisting 
of finite irreflexive frames and balloons. 
Exercise 5.6 Show that D4Z.3 = D4 ® z ® con is characterized by the frame 
(<*>,<). 
Exercise 5.7 Show that Dum = S4 ® dum is characterized by the class 
consisting of finite partial orders and reflexive balloons. 
Exercise 5.8 Show that Grz.3 = Grz®sc is characterized by the frame (u, >). 
Exercise 5.9 Show that Dum.3 = Dum ® sc is characterized by the frame 
(w,<>. 
Exercise 5.10 (i) Show that frames for K5 are 3-transitive. 
(ii) Prove that there are finitely many pairwise non-equivalent modalities in 
K5. 
(iii) Prove that all logics in NExtK5 are locally tabular and finitely axioma- 
tizable. 
Exercise 5.11 Show that D4Gi is finitely approximable. 

158 
CANONICAL MODELS AND FILTRATION 
Exercise 5.12 (i) Prove that extensions of S4 may have only 14, 10, 8, 6, 2 or 
1 pairwise non-equivalent modalities. 
(ii) Show that both S4.1 and S4.2 have exactly 10 pairwise non-equivalent 
modalities, and S4.1 ® S4.2 has only 8 of them. 
Exercise 5.13 Show that Int = Hi>i and that 
Int C ... C Tn C ... C T2 C Ti. 
Exercise 5.14 Prove that each Tn, for n > 2, has the disjunction property. 
Exercise 5.15 Prove that all logics Altn, for n < uj, are finitely approximable. 
Exercise 5.16 Prove that all logics in NExtAlti are finitely approximable. 
Exercise 5.17 Say that a logic L strongly admits filtration if for every generated 
submodel 9Jt of SJti, and every finite set of formulas E closed under subformulas, 
there is a filtration of 9JI through E based on a frame for L. Prove that if L 
strongly admits filtration then L is globally finitely approximable. Use this to 
show that the logics K, D, T, KB are globally finitely approximable. 
Exercise 5.18 Show that Log(Sr, D) = f]xeD Log (& {z})- 
Exercise 5.19 Show that K4 = Hn>i K4BDn = f]n>i K4BWn. 
Exercise 5.20 Prove that Alt 3 ® re ® sym has infinitely many non-equivalent 
modalities. (Segerberg (1971) conjectures that no proper normal extension of 
Alt3 ® re © sym has this property.) 
Exercise 5.21 Show that K4H = K4 ® p —» D(Op —► p) is canonical, with its 
canonical frame satisfying the condition 
xRy A yRz —> x = y V y = z. 
Prove that every L G NExtK4H is finitely approximable. 
Exercise 5.22 Show that S4 ® DOp —► (p —► Dp) is characterized by the class 
of quasi-orders satisfying the condition 
x 7^ z A xRz A xRy —► yRz. 
Exercise 5.23 Show that S4 ® □(□£> —► q) V (ODq —> p) is characterized by the 
class^Bf quasi-orders satisfying the condition 
xRz A -izRx A xRy —► yRz. 
Exercise 5.24 Show that D(p —> q) —> (Dp —► Oq) G D. 
Exercise 5.25 Prove that if a normal modal logic L contains the formula hin 
of Exercise 3.22 then satisfies the first order condition given in that exercise. 

NOTES 
159 
Exercise 5.26 Show that no distinct modalities are equivalent in the logics T 
and K ® Op —> Dp. Derive from this that there are at least two maximal logics 
in NExtK in which no distinct modalities are equivalent. 
Exercise 5.27 Show that the logic S4 + Ogrz is not normal. 
Exercise 5.28 Prove that S4+{□</?* : i € 1} = S4® {□</?* : i e /}. Is it possible 
to replace S4 in this equality by K4? 
Exercise 5.29 Prove that (i) NExtS4.3 = ExtS4.3, 
(ii) NExt(S4.2 ® bds) = Ext(S4.2 ® bds) and 
(iii) NExt(S4 ® bd%) ^ Ext(S4 ® bc^). 
Exercise 5.30 Show that the reflexive point in the frame considered in 
Example 5.60 can be replaced by an irreflexive one. 
Exercise 5.31 Show that kerL in Theorem 5.55 can be replaced with any 
normal logic U C L (for instance, K). 
Exercise 5.32 Show that KP C ML. 
Exercise 5.33 (M. Abashidze) Let ipn be the result of replacing every □ in (p 
by Dn. Prove that for every n > 0 and every <p, 
<p e GL iff (pn e GL. 
5.8 	Notes 
The construction of the canonical models is conceptually close to that used in the 
Henkin-style completeness proofs for classical first and second order calculi (see 
(Church 1956) and (Chang and Keisler 1990)) and to the Tarski-Lindenbaum 
algebras (see Chapter 7). The method of canonical models was introduced by 
Lemmon and Scott (1977)8 and Makinson (1966); cf. also Cresswell (1967) and 
Schiitte (1968). The canonical model of Lemmon and Scott (1977) seems to have 
its roots in the relational representation of Boolean algebras with modal 
operators (in particular, the Tarski-Lindenbaum algebras for modal logics), studied 
by Lemmon (1966a, 1966b). The canonical model of Makinson (1966) is an 
“improvement” of the tableau construction of Kripke (1963a). Perhaps these different 
sources explain why Lemmon and Scott (1977) introduce the filtration method, 
while the construction of the canonical model in Makinson (1966) is combined 
with selecting (using a sort of selective filtration) from it a countable submodel, 
which gives an analog of the Lowenheim-Skolem’s theorem (see Theorem 6.29). 
Approximately at the same time the canonical model for intuitionistic (predicate) 
logic was constructed by Aczel (1968), Fitting (1969) and Thomason (1969). 
The method of canonical models turned out to be a powerful tool in non- 
classical logic. It was applied systematically to prove completeness theorems for 
a good many normal modal logics by Lemmon and Scott (1977), who obtained 
8 This book was written in 1966. 

160 
CANONICAL MODELS AND FILTRATION 
in particular Corollary 5.22 and the result of Exercise 5.25, and by Segerberg 
(1971). Routley (1970) extended the ideas of Makinson (1966) to wide classes 
of weak modal systems. Rennie (1970) noticed that the method of canonical 
models works for polymodal logics too. Smorynski (1973) used it for si-logics. 
Later the method was applied to a great many other types of logics; see for 
instance Goldblatt (1982) and Segerberg (1994). 
The filtration method was introduced simultaneously with the canonical 
models by Lemmon and Scott (1977); the filtration theorem is due to Segerberg 
(1968). However, the algebraic variant of filtration goes back to McKinsey (1941) 
and Lemmon (1966a, 1966b). In modal logic various forms of filtration were used 
by Bull (1967), Segerberg (1968, 1971), Gabbay (1970b, 1972b, 1976) who 
developed selective filtrations, Nagle and Thomason (1985), Shehtman (1990a) and 
many others. Smorynski (1973), Gabbay (1970a), Ono (1972), Gabbay and de 
Jongh (1974), Ferrari and Miglioli (1993) and others applied it to si-logics. The 
results and proofs concerning the finite approximability, presented in this 
chapter, were taken from the cited papers and books. The observation of Exercise 5.17 
is due to Goranko and Passy (1992). Diego’s theorem was first proved by Diego 
(1966); the proof above is due to Urquhart (1974). Sobolev (1977b) somewhat 
generalized Diego’s theorem and used it to establish the finite approximability 
of a wide class of si-logics. Unfortunately, even the formulation of this result is 
too complicated to be presented here. A consequence of Sobolev’s theorem—that 
all si-logics with extra axioms in one variable are finitely approximable—will be 
proved by another method in Section 11.6. An interesting result was obtained by 
Drugush (1984): using a variant of selective filtration of Gabbay and de Jongh 
(1974) he proved that every si-logic characterized by a class of trees is finitely 
approximable. Note also that according to Drugush (1982) the union of si-logics 
characterized by finite trees is determined by finite trees too, i.e., the family of 
such logics is a sublattice of Extint. The completeness results of the preceding 
section concerning logics with linear frames are due to Segerberg (1970). 
The semantics for quasi-normal modal logics was developed by Segerberg 
(1971). Example |*58 and Exercise 5.28 are due to McKinsey and Tarski (1948). 
Scroggs’s Theorem appeared in Scroggs (1951) and Theorem 5.61 was first proved 
by Solovay (1976). 
Quite recently Shehtman has proved that every Kripke complete si-logic 
and every logic in NExtS4 characterized by partially ordered Kripke frames 
is strongly complete with respect to the neighborhood semantics. 

6 
INCOMPLETENESS 
In the preceding chapter we saw that many standard superintuitionistic and 
normal modal logics are Kripke complete, even finitely approximable and so 
decidable. Many of them turned out to be canonical and hence strongly Kripke 
complete, with their canonical frames satisfying good first order properties. Now 
we are facing the natural question: isn’t it possible to extend these completeness 
results to all logics in Extint and NExtK? To present examples of incomplete 
(in one sense or another) logics in these classes and elucidate to some extent the 
origin of the incompleteness is the main aim of this chapter. 
6.1 	Logics that are not finitely approximable 
As follows from the hierarchy in Section 4.3, the incompleteness with respect 
to the classes of finite frames accompanies some other incompleteness results, 
say Kripke incompleteness. So in a sense this section is redundant. However, the 
stronger the incompleteness result, the more complex logic is involved. Here we 
construct rather simple normal modal and si-logics that are not finitely 
approximable (in particular, Kripke complete), so that the origin of this phenomenon 
will be quite clear. 
We begin with modal logics. Let us consider once again the frame 0 shown 
in Fig. 5.1 (b). The root u) is clearly the only point in 0 capable of refuting the 
Lob axiom la = D(Dp —> p) —> Up. Another characteristic property of u) is that 
it sees infinitely many points. More precisely, u) is the only point in 0 such that 
if i is accessible from it, for some i < w, then i 4- 1 is also accessible. This may 
be expressed by modal formulas in the following way. Since i is obviously the 
only point in 0 at which the formula a* = D**1 J_ A OzT is true, u is the unique 
world where Oao and all the formulas Oa* —> Oa^+i, for i < u, are true. 
Thus, 0 |= -ila/\Octi —> -<ZaAOa^+i, for all i < u, and 0 ^ la\Z^Oa0. And 
if we notice also that all Oa^ may be simultaneously satisfied only in an infinite 
frame then we can immediately conclude that Log0 is not finitely approximable. 
Moreover, this observation can be developed into a much stronger result. 
Put 
L\ = K4 + {-ila A Oa^ —> -iZa A Oa^i : i < a>}, L2 = Log0. 
Since 0 |= Li, we have L\ C L2. 
Theorem 6.1 (i) No logic in the interval 
[Li, L2] — {L G ExtK : L\ C L C L2} 

162 
INCOMPLETENESS 
is finitely approximate. 
(ii) There is a continuum of normal logics in [Li,!^]. 
(iii) There are infinitely many finitely axiomatizable normal logics in [Li, Z^]* 
Proof (i) It is sufficient to show that la V -iOao is not in L2 and cannot be 
separated from L\ by a finite model. The former is clear, since 0 la V ->Oao- 
Suppose 971 is a model with actual world w such that (971, {w}) |= L\ and 
(971, {u;}) ^ la V -iOa0- By the definition of Li, we then have w |= Oaiy for 
every i < u, and so there are points Xi in 971 such that Xi |= a*. We show that 
Xi 7^ Xj whenever i 7^ j. 
Suppose otherwise, that is Xi = Xj for some i > j. Then we have Xj |= □■7'+1_L 
and since □J+1_L —► □*_!_ G L\ (because K4 C Li), Xj |= □*_!_, contrary to 
Xi = Xj and Xi |= OzT or, equivalently, Xi ^ □* J_. 
(ii) Let us consider the logics 
Lj — L\ 0 {ipi : i G /} 
where I C u and pt = □ (a* —> p) V □(«* —> ->p). Since a* is true in 0 only at 
one point, 0 f= (fi (to refute pi we need two points at which oti is true: at one 
p is true while at the other p is false). So Lj is a normal logic in the interval 
[Li, L2], for every I Cu. 
If j $ I then the frame fi in Fig. 6.1 validates piy for every i e I, and all the 
axioms of Li as well, because fi \= la. On the other hand, fi clearly refutes pj 
under every valuation such that f |= p and j" ^ p. Therefore, pj £ Lj and so 
Lj 7^ Lj if I 7^ J. It follows that the cardinality of the set {Lj : I C u} is that 
of continuum. 
(iii) Let us consider the logic L3 = K4 0 where 
t/> = -ila A 0(—i(jf A □ q) —► ->Za A 0(-iDq A □ □<?), 
and show that it belongs to the interval 
If (under some valuation) -1 la A 0(-iq A □ q) is true at a point x in 0 then 
clearly x = u. Besides, u |= 0(->q A □<?) means that there is y G u] such that 
y |= —*q A Uq. Therefore, y is irreflexive and so y = i for some i < u. Since i ^ q 
and j \= q for every j < i, we have i 4- 1 ^ Uq and i + 1 |= □ □<?, from which 
u) |= —'la A 0(—1 Uq A □ □<?). Thus, 0 |= xj) and L3 C L2. 
To prove the inclusion L\ C L3 it is sufficient to observe that 

LOGICS THAT ARE NOT FINITELY APPROXIMABLE 
163 
d as a2 a\ ao 
A_/q) <-> (-»Za A Oa* —► -<Za A Oai+i) G K. 
Infinitely many other examples of finitely axiomatizable logics in the interval 
[Li, L2} can be constructed from L3 by adding to it formulas ipi from the proof 
of (ii). □ 
It is worth noting that the frame 0 in Fig. 5.1 (b) is of width 1, and so 
Li C L3 © bwi C L2- Thus, as a consequence of Theorem 6.1 we obtain 
Theorem 6.2 There is a finitely axiomatizable normal modal logic of width 1 
(i.e.y an extension of K4.3J that is not finitely approximable. 
Intuitionistic frames are homogeneous in the sense that all their points are 
reflexive. So we cannot directly use the construction above to define si-logics 
that are not finitely approximable. (As we shall see in Section 11.6, all si-logics 
of width 1 are finitely approximable.) Yet the general idea may be realized in 
the intuitionistic case as well. 
Instead of 0 we use the intuitionistic frame # shown in Fig. 6.2. It consists of 
two parts: the first one, containing the points a* and for i < a;, simulates the 
irreflexive part of 0 and the remaining points c, d, ei, e2, e3, seeing all points in 
the first part, simulate u. Formally, # = (W,R) is defined as follows: 
W = {ai,bi,c,d,ej : i <u, j = 1,2,3}, 
R = {(x,x),(c,x),(d,afc),(d,6fc),(e/,afc), 
(el > frfc) > (e/ > era) , ii &k) > (bk+ii ^k) > i-f 2> > 
(&fc+t+2,afc) : X G VF, k,i <u, 1 < l < m < 3}. 
Instead of the Lob axiom and a* above we take the intuitionistic formulas 
a = (p 9) V (q -> pi V {pi -> p2 V (p2 p))) 
and 
where, for i < a;, 
Pi i 
c*! = r —► r' V V, /3i = -»r 
r' V -ir', 

164 
INCOMPLETENESS 
o>i as a2 a\ ao 
Fig. 6.3. 
«2 = A ^ «i V -i-ir, /?2 = ^ /?i V -»r, 
<2i-j-3 — Pi+2 —5► <2i+2 V /?i+lj ft+3 — &i+2 “► fii+2 V C^+i. 
Put 
Li = Int 4- {a V ai+i V ft+i —► a V a* V ft : i > 2}, L2 = Log#. 
Theorem 6.3 (i) No si-logic in the interval 
[Li, Lq\ — {L c Extint : L\ C L C Z/2} 
is finitely approximate. 
(ii) There are a continuum of si-logics in [Li,L2]. 
(iii) There are infinitely many finitely axiomatizable logics in [Li,L2]. 
Proof We give here only a sketch of the proof and invite the reader to fill the 
gaps. 
(i) The formula a V a2 V ft is not in L2 and cannot be separated from L\ by 
a finite model. 
(ii) For i > 2, we put 
(Pi — 0^+1 A ft-f 1 ► V ft. 
It is not hard to verify that # f= tpi, for every i > 2. Using the subframe of # 
depicted in Fig. 6.3, one can show also that ipi £ L\ 4- {<Pj : j >2, i ^ j}. 
(iii) As an example of a finitely axiomatizable logic in one can take 
the logic 
Ls = Int 4 Oi V 72 —► a V 71, 
where 
71 = ((P2 -► Pi V g2) ->P 1 v (pi -»P2 V 9i)) V ((pi -»P2 V Qi) -»• 
P2 v (p2 -►Pi V 92)), 
72 = (((pi -► P2 V gi) -»• P2 V (p2 -► PI V q2)) -> ((P2 -» Pi V q2) -► 
Pi V (pi -> P2 V gi)) V (p2 -> pi V q2))V 

LOGICS THAT ARE NOT CANONICAL AND ELEMENTARY 
165 
(((P2 ->P 1 V q2) -> pi V (pi -> ^2 V 91)) -> ((pi -»• p2 V qi) -> 
P2 V (p2 -> Pi V 52)) V (pi -> p2 V <?2)). 
The inclusion L\ C L3 follows from the equalities 
ll{Pi-3/quOti-3/q2,Pi-2/Pl,ai-2/P2} = Oii V ft, 
'l2{Pi-3/qi,ai-3/q2,Pi-2/pi,oii-2/p2} = a%+1 Vft+2. 
And to prove L3 C L2 it suffices to verify that # |= a V 72 —► a V 71. 
Infinitely many other finitely axiomatizable logics in [.£,1,1,2] can be 
constructed by adding formulas cpi to L3. □ 
Since # is of width 2, we have bw2 € Log#. So, as a consequence of 
Theorem 6.3 we obtain 
Theorem 6.4 There is a finitely axiomatizable superintuitionistic logic of width 
2 that is not finitely approximable. 
6.2 	Logics that are not canonical and elementary 
Most of the logics considered in Chapter 5 proved to be Kripke complete simply 
because they are characterized by their canonical frames. However, canonicity 
is only a sufficient condition for Kripke completeness. Although the canonical 
frame for a logic L refutes all the formulas that are not in L, it may also 
refute some of L’s axioms. In other words, L is not necessarily sound with respect 
to #x, witness the following simple example. 
Theorem 6.5 GL is not canonical. 
Proof Recall that a frame validates the Lob axiom iff it is a Noetherian strict 
order, in particular it contains no reflexive points. We are going to show that 
there are reflexive worlds in #gl- 
As was established in Example 5.60, Solovay’s logic S = GL -f dp —► p is 
consistent. Therefore, by Lindenbaum’s lemma, the tableau 
(GL U {□</? —► ip : ip e ForAl£}, 0) 
can be extended to a maximal GL-consistent tableau (T, A), which is the 
reflexive point in 3gl we need, since □</? € T implies ip e T. □ 
In fact we have even a stronger result. 
Theorem 6.6 GL is not strongly Kripke complete. 
Proof Let oti = □ (pi —> Opi+i A -<0pi) and T = {Opi,ai : 1 < i < u}. We 
show that the tableau (I\0) is GL-consistent but not realizable in any model 
based upon a frame for GL. To prove the former it is enough to observe that 
the formula Op\ A ol\ A ... A an is true at the root 0 in the model (#, 9J), where 
£ = ({0,..., n 4-1}, <) and %3(pi) = {z}, which is clearly a model for GL. And 
the latter claim follows from the fact that to make T true at a point we need an 
infinite ascending chain starting from it. □ 

166 
INCOMPLETENESS 
Say that a class C of Kripke frames is elementary if there is a set <3> of first 
order sentences in R and = such that, for every Kripke frame #, $ € C iff $ is a 
(classical) model for <3>. A logic L is elementary if the class of all Kripke frames 
for L is elementary. 
To prove that GL is not elementary we use the compactness theorem from 
classical model theory (see Chang and Keisler, 1990, Theorem 1.3.22). 
Theorem 6.7 GL is not characterized by an elementary class of frames. In 
particular, GL is not elementary. 
Proof Suppose GL is characterized by a class C of Kripke frames (by 
Proposition 3.47, all of them are Noetherian strict partial orders) and show that C is 
not elementary. 
Assume otherwise. Then C consists of all classical models for some set <3> of 
first order formulas with R and = as their only predicates. By Theorem 5.46, 
GL is characterized by the class of finite strict orders. Since the formulas bdn 
are refuted by transitive frames of depth > n (see Proposition 3.44), none of 
them is in GL. Therefore, for every n < u, C contains a frame of depth > n. 
Let us consider now the first order formulas 
071 — A (aiRaj A -lajRxii) 
l<i<j<n 
(here a* are individual constants of the first order language). Clearly, a strict 
partial order $ satisfies 0n iff $ is of depth > n. So every finite subset of the set 
$U{0n : 1 < n < u;} has a model, for instance, a frame in C of depth > m where 
m is the maximal subscript of 0ns in the subset. By the compactness theorem, 
the whole set 4>U{0n : 1 < n < oj} has a model as well, say, a strict order #, which 
is in C because it satisfies 4>. But to satisfy all 0n, £ must contain an infinite 
ascending chain a\Ra2Ra%R... of distinct points, which is a contradiction, since 
$ 1= GL and so £ is Noetherian. □ 
In exactly the same way one can prove 
Theorem 6.8 Grz is not strongly complete and it is not characterized by an 
elementary class of frames. In particular, Grz is neither canonical nor 
elementary. 
In fact the notions of canonicity and elementarity turn out to be closely 
related: in Section 10.2 we shall prove that every logic in NExtK and Extint is 
canonical whenever it is characterized by an elementary class of frames. So by 
proving that a Kripke complete logic is not strongly complete we establish also 
that it is not elementary. 
Theorem 6.9 T2 = Int 4- 662 is not strongly complete. Moreover, no si-logic 
in the interval [Int,T2], save Int, is strongly complete. 
Proof Let X2 be the full binary tree. Say that a point a in X2 is of codepth n 
(■cd(a) = n, in symbols) if the chain aj contains n 4-1 points. With every point 
a in X2 and every i > 0 we associate the variables pa and qi, respectively. 

LOGICS THAT ARE NOT CANONICAL AND ELEMENTARY 
167 
By the type of the root do in X2 we mean the tableau tao = (0, {pao }). And if 
the type of a point a in X2 is (©, {pa}), and 6, c are the immediate successors of 
a with cd(b) = cd(c) = n then the types of b and c are % = (© U {pai qn}, {pb}) 
and tc = (© U {pa, ->qn}, {Pc}), respectively. 
Now let us consider the tableau t = (T, {pao}) in which T consists of all 
formulas of the form 
a = (/\0 -> Pb) -> Pa 
such that b is a proper successor of a and t& = (©, {p*,}), 
(3 = (/\Q -> pc) -> paVpb 
such that a|D 6| = 0, c[ = a|D and tc = (0, {pc}), and 
7 = (A S -> Pb) ^ v (A © Pa) 
such that cd(a) > 0, ta = (0, {pa}), <P is the conjunction of all formulas of the 
form qi and ->qi in 0 and b is the immediate predecessor of a with the type 
tb = (£,{P6». 
It is a matter of routine to check that every finite subtableau of t is realizable 
in a model based on a sufficiently deep finite binary tree, which is a frame for 
T2 (it suffices to put a |= pb iff b £ a\ and a |= qi iff qi belongs to the left part 
of ta). Thus, t is L-consistent, for any L € [Int,T2]. 
We are going to show now that if t is realized in a model 971 = (#, 97) then 
a generated subframe of $ = (W,R) is reducible to any finite tree and so, by 
Corollary 2.33 and the reduction theorem, refutes all the formulas that are not 
in Int, i.e., # L for any proper extension L of Int. 
Without loss of generality we may assume that # is rooted and t is realized 
at its root. For every a in X2, put 
Ya = {x € W : x realizes ta}. 
Notice that if a point x sees some Ya but does not belong to any Ya itself, then 
the set Z = {a : x € Ya[} has a root (with respect to the partial order in X2). 
Indeed, otherwise there are two distinct minimal points a, b € Z. Let c[= a|Pi6| 
and tc = (0, {pc})- Since x |= (/\ © —► pc) —> pa V Pb and x € Ya[nY^I, we have 
x pa Vpb and so x /\ © —► pc. It follows that Yc is accessible from x, which is 
a contradiction. Denote the root of Z by ax and put Xa = YaU{x e W : a = ax}. 
Thus, 
\J Xal= [j xa = w. 
(1^X2 0,^X2 
Observe also that if a] n b]= 0 in X2 then Xa| n Xrf = 0 in To show this 
suppose ip and ^ are the conjunctions of all the qi and in the left parts of ta 
and tb, respectively. By the definition, ip is true at all points in Ya. And if ip is 

168 
INCOMPLETENESS 
not true at a point x £ Xa — Ya then, since all formulas of the form 7 are true 
at x, x must see the set Yc corresponding to the immediate predecessor c of a, 
which is a contradiction. Therefore, p is true everywhere in Xa. By the same 
reason ^ is true everywhere in Xb. It remains to notice that p and cannot be 
true at a point simultaneously. 
Using this observation and the formulas of the form a it is not hard to check 
that the map g defined by g(x) = a iff x £ Xa is a reduction of the subframe 
= (W\R\W') of # to %2 (we leave this to the reader; some details can be 
found in the proof of Theorem 9.39). 
Let 0 be an arbitrary finite tree. By Theorem 2.21, there is a reduction h of 
X2 to 0. The composition /' = hg is then a reduction of to 0. So our aim 
now is to extend it to a reduction / of # to 0. For every x £ W — W', the set 
ff(x[) is a chain in 0 (for otherwise Xa\ nAVT^ 0 for some a and b in X2 without 
common successors). Let u be a final point in 0 accessible from the last point in 
this chain. Then we put f(y) = u for all y £ W - Wr such that /'(xj) = f'{y[). 
And for x £ Wf let f(x) = ff(x). It should be clear from the construction that 
/ reduces $ to 0, which proves our theorem. □ 
6.3 	Logics that are not compact and complete 
The compactness theorem from classical model theory, used in Section 6.2, may 
be formulated as follows: if every finite subset of a set of formulas E has a model 
refuting a formula p then the whole set E also has a model refuting p. 
We say a modal or si-logic L is compact (relative to Kripke frames) if each 
formula p L is separated from L by a Kripke frame whenever p is separated 
by a Kripke frame from every finitely axiomatizable sublogic V C L. Clearly, 
Kripke completeness implies compactness. 
Let us consider the logic 
L\ = K4 ® {7i —► 07i+i : i < u} ® 6, 
where 
7o = OPo A Oc*i, 7<+i = Oft+i A Oai+2 A ^0+7*, 
Pi = OOcti A -iOai+i, a0 = □!, a»+i = Oa» A-lOOa* (i < u), 
6 = -*(p A -iq A (p A -*<7 —► 0(p A q)) A (p A q —► 0(-*p A <7)) A 
AD+ (pp A q —> 0(p A -w?))). 
(We remind the reader that D+p = p A Op, O+p = pV Op.) 
Theorem 6.10 L\ is not compact. 
Proof Let us first clarify the semantic meaning of Li’s axioms. To understand 
the (variable free) axioms 7* —> 07i+i it is useful to take a look at the frame 
depicted in Fig. 6.4. The only point in this frame, at which ao is true, is clearly ao- 
Then by induction on i one can readily show that a* is the only point at which at 

LOGICS THAT ARE NOT COMPACT AND COMPLETE 
169 
<2o ai ' a2 as <2fc_i ak 
•-< -• • • • •-« • 
( 
o6° ( 
H ( 
»6l c 
MH 
162 < 
CO 
-0 
»-« i 
\h-1 < 
• ►( 
> ►< 
► ... < 
► 
Co Cl C2 Cs Ck-1 Ck 
Fig. 6.4. 
is true. It follows immediately that {x : x (= /?*} = {bi} and {x : x (= 7*} = {c*}, 
for i <u. 
Thus, 7i —► <>7i+i may be understood as “in the frame under consideration 
Ci sees Ci+i”. 
The meaning of 6 can be expressed more precisely. 
Lemma 6.11 A transitive frame 3 validates 6 iff 3 contains neither an infinite 
ascending chain of distinct points nor a cluster with > 3 points. 
Proof Exercise. □ 
We are in a position now to prove Theorem 6.10. Namely, we are going to 
show that, for every finitely axiomatizable logic LCLi, (a) there exists a frame 
3 such that $ \= L and 3 -*70, but (b) -170 cannot be separated from Li by 
any Kripke frame. 
Suppose L is a finitely axiomatizable sublogic of L\. Since derivations of L’s 
axioms involve only a finite number of Li’s axioms, there is k < u such that 
L C K4 ® {7i —* C>7i+i • — 1}®<5. 
So, to prove (a) it suffices to show that, for every k <uo, there is a frame 3fc such 
that 
3fc |= K4 © {7i —► <>7i+i : 0<i<fc — 1}©<5, (6.1) 
V2 _l7o- (b-2) 
Define 3fc = (Wk,Rk) by taking 
Wk = {ai, bi, Ci : 0 < i < A;}, 
Rk {{a%, aj), (6/, b[), (6/, ai), {bi, aj), (c/, bi), 
(cj, bi), (Cj,a), i 0 < j i < A;, 
In other words, 3fc is the subframe of the frame in Fig. 6.4 containing the first 
k rectangles. (6.1) and (6.2) are now direct consequences of the properties of 7i 
discussed above and Lemma 6.11. 

170 
INCOMPLETENESS 
To establish (b), suppose # is a frame for L\ refuting -170. Then t/o |= 7o for 
some t/o in Since # |= 70 —► O71, there exists y\ € t/oT such that y\ [=71. By 
the definition of 7*+i, it follows in particular that y\ |= -1O70, and so t/o ^ t/iT* 
With the help of the axiom 71 —► O72 in exactly the same way we show that 
there is t/2 € t/i T such that t/i ^ etc. As a result we construct an infinite 
ascending chain of distinct points in #, contrary to Lemma 6.11 and # \= 6. 
□ 
It is worth noting that the proof above shows incidentally that the logic 
K4 0 {7i —► 07^+1 : i < u} is not finitely approximable. Thus we have got 
Theorem 6.12 There is a normal extension of K4 with variable free additional 
axioms that is not finitely approximable. 
This result does not hold for ExtS4 and Extint because in both S4 and 
Int every variable free formula is equivalent to T or 1 (see Proposition 2.26 
and Exercise 3.19). As we shall see in Section 8.7, each variable free formula 
is deductively equal in NExtGL to one of the formulas T, (i < (j). Since 
□ZJL —► CPJL € K4 C GL, for i < j, all normal extensions of GL with variable 
free formulas are finitely axiomatizable and so finitely approximable, as follows 
from 
Theorem 6.13 Suppose p is a variable free modal formula and L G NExtK 
is globally Kripke complete (globally finitely approximable). Then L@p is 
globally complete (globally finitely approximable) as well. If L G NExtK4 and L is 
decidable then L @<p is also decidable. 
Proof Let M = L 0 p and T \f*M -0 for some finite T. Then T, p \f \ 'tp and so 
there is a Kripke (finite) frame # for L such that under some valuation ruW 
is true in # and is refuted. Since p is variable free, $ \= M. □ 
Theorem 6.14 GL + {OlT : i < uj} is not finitely approximable. 
Proof This logic is consistent because it is, contained in S, but does not have 
finite models at all. □ 
On the other hand we clearly have 
Theorem 6.15 Every (normal) extension of a canonical logic with variable free 
additional axioms is also canonical. 
6.4 	A calculus that is not Kripke complete 
The incomplete logic Li, constructed in the preceding section, is not finitely 
axiomatizable (why?), and all the axioms 7* —> 07^+1 were used essentially in 
the incompleteness proof. Here we show that a single additional axiom is enough 
to get a Kripke incomplete logic. The idea of replacing the infinite set of axioms 
with a single formula is similar to that in the proof of Theorem 6.1 (iii). 

A CALCULUS THAT IS NOT KRIPKE COMPLETE 
171 
We continue using the notations introduced in Section 6.3. Define a logic L2 
as follows: 
L/2 — K4 ® e ® <5, 
where 
e = A0 —► 0(Ai A -iO+A0), \v= Opi A pi = OOvt A 
vo = V A -'Op, = ^o{Ozp/p}- 
Theorem 6.16 The calculus L2 is not Kripke complete. 
Proof We are going to show that -*70 & £2, but -*70 is valid in every frame for 
L2* The proof is similar to the proof that -170 cannot be separated from L\ by a 
Kripke frame. In that proof we used the triple of formulas ai, fa, 7* characterizing 
in the frame depicted in Fig. 6.4 the triple of points ai} 6*, c* (with the same 
subscripts). The triple Vi, pi, A * is also intended for determining in this frame a 
triple of points <2j, bj, Cj, possibly with i ^ j\ and if this is the case then it turns 
out that the triple Pi+k, \+k determines the triple <2^+*,, Cj+fc, for 
k < uj. That is in essence the single formula e will play the role of the infinite 
set {7i -> <>7i+i : i < w}. 
Lemma 6.17 For every frame if$\= L2 then # |= ->70. 
Proof Observe first that 
<*» = ^{T/*>}, ^ = m{T/p}, 
7o = A0{T/p}, 7i+i = (Ai+i A -iO+Aj){T/p), 
Ai —» 0(Ai+i A ->0+Aj) = e{0*p/p}, 
7i - <>7i+i = (A* - 0(Ai+1 A _|0+Aj)){T/p} = e{OlT/p}. 
It follows that 7i —> <>7^1 € L2, for all i < u, and so L\ C L2. It remains to use 
the proof of Theorem 6.10. □ 
Thus, to complete the proof of our theorem it suffices to establish 
Lemma 6.18 -170 ^ £2* 
Proof We need the transitive frame # = (W, R) shown in Fig. 6.4; here is its 
formal definition: 
W — . i a)}, 
R , {bj, bj), ipi^af), (bj,aj), {cj,bf), 
, {cj,a^j, (c^ci) . 0 ^ j <c 
Define a model = (#, 93) by taking 93(p) = 0, for every variable p. Since $ 
contains an infinite ascending chain, by Lemma 6.11 we have # 6. However, 
931 does not “feel” the chain. More exactly, the following holds. 

172 
INCOMPLETENESS 
Lemma 6.19 DJI f= <5* for every substitution instance 6* of 6. 
Proof Observe first that we have 
Lemma 6.20 For every formula </?, the set (<p) is either finite or cofinite. 
Proof The proof proceeds by induction on the construction of </?. The basis of 
induction and the cases when s main connective is not modal are trivial. So 
let us consider p = □?/>• 
Suppose 2J(-0) is finite. Then there is a* such that a* -0. This means that 
{aj,bj,ck: i < j, k < u} C W - 93(D^), 
i.e., W — is cofinite and so %J(p) is finite. 
Suppose now that 2J(V>) is cofinite. Two cases are possible: (a) there is a* 
such that ai ^ -0 and (b) a* |= ^ for every z < u. In Case (a), as before, 93(CI^) 
is finite. So let us consider Case (b). 
Since the set W — 9J(V>) is finite, there is k > 0 such that 
{ai,bj,Cj : i < u, j > k} C 93(-0). 
Then 
{ai,6j,Cji z < a;, j > k} C 93(CI^), 
and hence 93(111^) is cofinite. □ 
We are in a position now to prove Lemma 6.19 by reductio ad absurdum. 
Suppose 6* — b{<p/p,'ip/q} and t/o f°r some point yo in SDt. Then we have 
2/o h ^ A 
yo 1= D+(V? A —> 0(y> A V')), 
yo |= D+(v’ a ip -*• o(-.^ a v>)), 
yo 1= □+(->v3 A V» -> 0(<£ A -iV’))- 
Using the same argument as in the proof of Lemma 6.11, we can construct an 
infinite ascending chain y$Ry\Ry2R... in J such that, for every k < u, 
V3k |= <P A ->i>, V3k+1 t= <P A i>, V3k+2 \=-'<pAip. 
Since # contains no proper clusters, it follows that yi ^ yj if z ^ j. Therefore, 
the sets 
{y3fc,y3fc+i: k <u>} CV3(ip) 
and 
{y3fc+2 : k < u) c w - V3(<p) 
are infinite, contrary to Lemma 6.20. 
□ 

A CALCULUS THAT IS NOT KRIPKE COMPLETE 
173 
Lemma 6.21 # |= e. In particular, DJI \= e* for every substitution instance e* 
of e. 
Proof Suppose otherwise. Then under some valuation in #, e is false at some 
point t/, i.e., 
y |= A0, (6.3) 
1/£0(A1A-.0+Ao). (6.4) 
It follows from (6.3) that there is z € t/ T at which both OOv$ and -»0^i 
are true. This means that we can reach from 2 by two steps a point u at which 
= p A -»0p is true. Therefore, u is irreflexive and so u € {a*, c* : i < u}. On 
the other hand, 2 does not see an irreflexive point v € uj, which is possible only 
if 2 = bi, for some i > 0. But then u = a 
It follows also from (6.3) that there is a point x e y T at which v\ is true. 
Since a* |= z^o, the only point where v\ may be true is <2*+1, whence pitai+i. 
Then, according to the construction of y = Cj for some j < i. 
Thus, we have y = Cj and yRci+1. Besides, as we have already established, 
ai |= z^o* It is not difficult to see now (by induction on k) that, for every k < u, 
{x : x\=uk} = {ai+fc} 
and so 
{x \ X |= /ifc} = {&i+fc}. 
It follows that ci+1 |= Ai A -»O+A0, contrary to yRci+1 and (6.4). □ 
By Lemmas 6.19 and 6.21, DJI is a model for L2. It remains to observe that 
c0 |= 7q and so -*70 ^ This completes the proof of Lemma 6.18. □ 
Theorem 6.16 follows immediately. □ 
In fact the proofs of Theorems 6.10 and 6.16 provide us with a big family of 
incomplete logics. Indeed, denote by Ls the set of modal formulas that are true 
in all models (#, il) such that, for every variable p, il(p) = 2J(<p) for some formula 
<p. It is not hard to see that L3 € NExtK4. We then have: L\ C L2 C L3, -»7o is 
not in L3 and cannot be separated from L\ by a Kripke frame. Therefore, all the 
logics between L\ and L3 are Kripke incomplete. Using the formulas <pi from the 
proof of Theorem 6.1, we can show that the cardinality of the interval [Li,L^\ 
is that of continuum. And by adding (/?* to L2 we can construct infinitely many 
finitely axiomatizable logics in this interval. 
Let us fix these observations as 
Theorem 6.22 (i) No logic in the interval [Li,!^] is Kripke complete. 
(ii) There is a continuum of normal logics in [Li,!^]. 
(iii) There are infinitely many finitely axiomatizable normal logics in [Li, L3]. 
Using the fact that every finite irreflexive chain validates L3, we can obtain 
one more interesting result: 

174 
INCOMPLETENESS 
Theorem 6.23 No normal logic between K4 0<5 and L% is strongly Kripke 
complete. 
Proof Similar to the proof of Theorem 6.6. □ 
6.5 	More Kripke incomplete calculi 
Now we realize the idea of constructing incomplete calculi, developed in the 
previous section, to find Kripke incomplete extensions of Grz, GL and Int. 
Since we use the same method, the most part of technical details in the proofs 
is left to the reader as exercises, sometimes far from being trivial. 
For two cases—Grz and Int—we use the (transitive) frame shown in Fig. 6.5; 
for GL all the reflexive circles in it should be replaced with irreflexive “bullets”. 
Its similarity with the frame in Fig. 6.4 is emphasized by the worlds’ names. 
We require the following intuitionistic formulas: 
<*-i =p, all=q, al = q^>p, aft = p -> q, 
^n+l ^ 1? ^n+l ^ ^ X? 
Ai = <*n+i A <*n+i — ai V a2n, (n < w) 
A =/?o-►/?i V/J2, p = (30VPi, e = A->/i, <• =/?i-► /?o V 
Theorem 6.24 (i) Grz®T(e) is Kripke incomplete. 
(ii) GL 0 T+(e) is Kripke incomplete9. 
Proof We will establish only (i); (ii) is proved in the same way. The proof 
consists of two lemmas. 
9Here T and T+ are the embeddings of Int into Grz and GL defined in Section 3.9. 

MORE KRIPKE INCOMPLETE CALCULI 
175 
Lemma 6.25 If $ is a frame such that # |= Grz 0 T(e) then # |= T(fi). 
Proof (Sketch) Proving the lemma by reductio ad absurdum, we suppose that 
# |= Grz 0 T(e) and # ^ T(p) and show, as in the proof of Lemma 6.17, that 
in this case # contains an infinite ascending chain of distinct points, contrary to 
# |= Grz. 
For n > 1, let 
70 = 7n = nWn-2 V «n-l/p, <*n-l V <*n-2M 
and suppose that, under some valuation in #, T(fi) is not true at some point t/o5 
i.e., t/o y=- T(7o). Since # validates T(e), we can use the substitution instances 
eiah-2 v an-i/P5an-i v an-2/^} °f e to hud first a point 2/1 € t/oT such that 
Vi f= T(7o) and yx ¥= T(7i), then y2 € t/iT such that y2 h t(7i) and y2 ^ T(72), 
and so on. □ 
Lemma 6.26 T(/i) ^ Grz0T(e). 
Proof (Sketch) Let DJI be a model based on the frame in Fig. 6.5 and such that 
x |= p iff x = a\ and x |= q iff x = Oq. In the same manner as in the proofs of 
Lemmas 6.19 and 6.21, one can show that DJI |= □(□(</? —> □</?) —> </?) —> and 
9JI |= T(e){<p/p, -0/<gr}, for every formulas </? and -0. On the other hand, we have 
c0 V* t(m). □ 
This completes the proof of Theorem 6.24. □ 
Given a si-logic L, we put 
J(L) = {J(p): <peL}, T+(L) = {T+(<p): <p € L}. 
Theorem 6.27 There is a superintuitionistic logic L such that 
(i) L is Kripke complete; 
(ii) Grz0T(L) is not Kripke complete; 
(iii) GL0T+(L) is not Kripke complete. 
Proof Define L as the si-logic of the frame in Fig. 6.5, so that (i) holds by 
the definition. Let DJI be the model on this frame introduced in the proof of 
Lemma 6.26. Then DJI p. On the other hand, e is valid in our frame, i.e., e € L. 
By Lemma 3.81, we then have T(p) & Grz0T(L) and T(e) € Grz0T(L). The 
incompleteness of Grz 0T(L) follows now immediately from Lemma 6.25. 
(iii) is proved in the same way. □ 
The proof above may be interpreted as that there are no intuitionistic 
analogues of the Grzegorczyk and Lob formulas, or 6 in Section 6.3, which “feel” the 
presence of infinite ascending chains. Yet, the proof of Theorem 6.9 shows that 
for the same purpose one can use the formula bb2. 
Theorem 6.28 The si-logic Int + e -f l 4- bb2 is Kripke incomplete. 

176 
INCOMPLETENESS 
Proof (Sketch) One can show similar to Lemma 6.25 that if a frame validates 
e and t and refutes p then it also refutes 662, i.e., fi is valid in every frame for 
the logic L = Int -f e + t + 662- On the other hand, all substitution instances of 
€, b and 662 are true in the model defined in the proof of Theorem 6.27, from 
which 9Jt \= L, 9Jt p and so fi £ L. □ 
6.6 	Complete logics without countable characteristic frames 
The Lowenheim-Skolem theorem of classical model theory (see Chang and Keis- 
ler, 1990, Corollary 2.1.6) states that if a first order theory (in a countable 
language) has an infinite model then it has also a countable model. Canonical 
models for modal and superintuitionistic logics contain, by the definition, a 
continuum of points. However, most of these points may be safely removed, as is 
shown by the following 
Theorem 6.29 Every consistent logic in ExtK and Extint has a countable 
characteristic Kripke model 
Proof We construct a countable characteristic model for a consistent logic L 
in NExtK. Quasi-normal modal logics and si-logics are considered analogously. 
Let 9Jt = (#, 93) be an arbitrary characteristic model for L (for instance, the 
canonical model) and # = (W, R). A countable characteristic model we need can 
be extracted from in a manner similar to the selective filtration method. Let 
E = For ME - L. 
Step 0. For every ip € E, fix a point in Wl at which (p is false. Let Wo be the 
set of all the fixed points. Clearly, Wo is countable. 
Step n + 1. Suppose we have already constructed a countable set Wn C W. 
Now, for every x € Wn and every ^ G E we fix a point y € x\ in 9Jt, if any, 
at which ip is false. Let Wn+1 be the union of Wn and the set of all new fixed 
points. Again Wn+1 is countable. 
Finally, define a model 91 = (<S,U) on a countable frame 0 = (V, S) by taking 
V = (J Wi, s = Rnv2, 
i<oj 
il(p) = 93(p) fl V, for every p e VarMC. 
By induction on the construction of a formula (p one can readily show that, for 
every x € V, 
(9Tt,x) 1= (p iff (91, x) 1= ip. 
It follows that 91 characterizes L. □ 
Needless to say that this result does not hold for Kripke frames (for there 
are logics without characteristic Kripke frames at all). Moreover, even if a logic 

LOGICS WITHOUT COUNTABLE CHARACTERISTIC FRAMES 
177 
is Kripke complete it may have no countable characteristic frame as is 
demonstrated by the following theorem, in which cardinal numbers 2% are defined by 
transfinite induction on ordinals £: 
(No if£ = ° 
3{ = {23< if e = C + l 
( U<<£ 3c if £ is a limit ordinal. 
Theorem 6.30 There is a logic L € NExtK4 which is characterized by a Kripke 
frame of cardinality 2^, but is not approximable by frames of smaller cardinality. 
Proof Define L as the logic of the transitive frame 3 = (W, R) shown in Fig. 6.6. 
A formal definition of 3 may look like this: 
W = {a,6,c,d,a_i,6_i,e',e} U : i < u} U 
: i <u;}U{/i^,/4\/42 : 1 < i < w, X € V*u} 
(where VY is the power set of Y, V(]Y = Y and Pl+1 = V(VlY)) and R is the 
transitive closure of the following binary relation S on W\ for every x,y € W, 
xSy iff 
(x — e/\y^e)y(x = bl\y=^b)\J 
(x = c A y = a) V {x = d A (y = a V y = b)) V 
(x = a-1 A y = c) V (x = 6_i A y = d) V (x = e' A (y = c V y = d)) V 
(x = ao A (y = a_i V y = d)) V (x = A (3/ = 6_i V 3/ = c)) V 
3* 
3X,Y ((x = cii A y = 
0*1—1) V (x 
= bi Ay = 
= *i-x) 
V 
(x 
= ai+1A y = 
a') V (x 
< 
T—l 
^cT 
II 
— b'i) V 
(x 
= h°i A (y = h 
h’1 V y - 
= C2))V 
(x 
II 
O 
> 
II 
a-iVy- 
= ao)) V 
(x 
= h°i'2A(y = 
biV y - 
= 6o))V 
(x 
II 
x- 
> 
II 
hlx V y 
> 
3-x 
-cs 
II 
(x 
II 
< 
3x 
-cs 
II 
a'i v (v 
,0,1 A • 
= V At 
e X) v (» 
A* ^ X))) V 
(x 
— hx A (y — 
b[ V (y 
= hJ’1 A t < 
£X)V(y 
= h°i’2 
A i € 
= X)))V 
(x 
= I#1’1 A (y 
= <+i 
< 
II 
at ex) 
V(y = 
= 42 
a y*x)))’ 
(x 
= #1,2a (y 
= K+1■ 
5-x 
II 
> 
AY £ X) 
y(y = 
ii,2 
■ tl-y 
Arex)))) 
By the 
given definition, |?| 
II 
eU 
in 
0 
we must 
show 
that 
L = Log? 
approximable by frames of cardinality < 2^. 
Although the frame 3 looks rather cumbersome (which is justified by our 
purpose, of course), its constitution can be made quite clear. Our next aim is to 
describe points in 3 by means of modal formulas. 

178 
INCOMPLETENESS 
(22 <2l CLq CL—I cab 
Nk' 
Fig. 6.6. 
Let us begin with J’s points that are characterized by variable free formulas. 
The reader can easily verify that the formulas 
a = OL, ft = OT A DOT, 7 = □□.]_ A OT, 
6 = Ocx A 0/3 A —OOa, e/ = O7 A O6 A —1OO7 A —iOO<5, e = Oe^ 

LOGICS WITHOUT COUNTABLE CHARACTERISTIC FRAMES 
179 
a_i = O7 A —1007 A —'0/3, (5-\ — 08 A —*008 A —>07, 
ctQ = Oa_i A 08 A —'OOa-i A —iOO<$, /% = Oft_i A O7 A A —>OO7, 
a* = Oa^-i A ->OOai_i A ->0<5, ft = Oft_i A -nOOft.i A -><>7, 
a'+1 = Oa' A -lOO'ai A ~^0(5-\, $+1 = 0(5[ A ->OOft' A -^Oa_i, 
X?’1 = A “’00^2 A Oqq, x?’2 = Oft A -^OOft A 0/?q, 
X? = Ox?’1 A 0X?’2 A -.OOx?’1 A -00X?’2, 
for i > 0, are such that a is true in $ only at a, (5 at b, 7 at c, <5 at d, c' at e', e at 
e and the formulas denoted by a, ft x with subscripts and superscripts are true 
only at the points in $ denoted by a, b, h, respectively, with the corresponding 
indices. 
Before we continue characterizing ^’s points by modal formulas, let us observe 
that the following holds. 
Lemma 6.31 (i) -ie ^ L; more exactly, {x : x \= e} = {e}. 
(ii) 6 —► Ox? 6 L, for every i < u. 
(iii) Xi -*• _,<>Xj’1 A -•Ox,’2 e L, for i, j < u, i ^ j. 
Now define three more sequences of formulas, for i > 1: 
X*’1 = Oa’i A -iOOaJ A (Oa0 V Ofo), 
X*’2 = Oft A -lOO/Jf A (Oa0 V O/30), 
X* = Ox*’1 A Ox*’2 A -iOOx*’1 A -iOOx*’2- 
These variable free formulas characterize in $ not single points but sets of points, 
namely, 
{* : x |= XiA} = {41 : X £ PM> 
{* : x |= x"’2} = {hf : X € VM, 
{x : as 1= x*> = {h*x ■■ X € *>*«}• 
To characterize the relation between the points in £ involved in representing 
sets in for % > 1, we require a few more formulas: 
tt»(p) = X* -*■ (0(xia Ap) V 0(x*’2 Ap)) A-.(0(xt’1 Ap) A 0(x’’2 Ap)), 
o-j(p) = e A 071-* (p) -> Ocr'(p), 
= Xt+1 A 0(xt+1,1 A □(x1’1 V x1’2 P)) A 
0(x*+1,2 A □(x1’1 v x*’2 -► -,p)), 
Pi(p, Q, r) = p~ (p, q, r) -+ pf (p, q, r), 
pr (P. q,r) = eA Dtt^p) A 0(q A p A (x*’1 V x*’2)) A 

180 
INCOMPLETENESS 
0(r A -<p A (xhl V X*’2)) A 
D((XM V x1’2) A ->p —> -19) A □((x*’1 V x*’2) A p —> -t), 
pf(p,q,r) = □(<r'(p) -> 
□(Xi+1,1 0(9 A (xM V xil2)) A -iO(r A (xM V X*’2))) A 
D(X*+1,2 0(r A (xU V x’’2)) A ~^0(q A (xU V X1’2))))- 
Lemma 6.32 (i) <Ji(p) G L for every i <uj. 
(ii) pi(p, q,r) G L /or ererp z < a;. 
Proof (i) We need to show that if, under some valuation in the frame we 
have x f= e A Dtt^p) then x f= Ocr-(p). So suppose x f= e A □tt^ (p). Then by 
Lemma 6.31, x — e and so e |= Dn^p). This means that, for every X G 
either 
h'x \= V, h'x ¥= V or ^x ^ ^x2 1= P- 
Let y = {X : /i^1 |= p}. Then clearly we have Y — {X : h^ p}. By the 
construction of there are points fty-1, hy’1'1, such that 
^ (X€rA/ = i)v(x^yA/ = 2), 
iff {X G y A j = 2) V {X # Y A / = 1). 
Then we have 
^Hx^A^V^-p), 
fey1,2 b Xi+1’2 A □(XU V Xil2 -♦ -p), 
which together with hy1Rhly1’1, hy1Rh$'1’2, hy1 b Xl+1 yields e |= Oo-'(p). 
(ii) Suppose now that, under some valuation in x f= p^(p><Z>r) and sh°w 
that x |= pf(p, q,r). Since x |= e A D^^), we may assume that we are in the 
same situation as in the proof of (i), in particular, x = e and hlyl f= cr-(p), with 
hlyl being that only point at which, under the given valuation, a[(p) is true. It 
follows also from the first assumption that 
e b ^(9 A p A (x*’1 V X*’2))) (6-5) 
e b 0(r A ->p A (x*’1 v X1’2)), (6.6) 
e b ^(X1’1 Vx1’2) A-.p-» -19), (6.7) 
eb°((x<llVxi>2)Ap--.r). (6.8) 
Suppose e ^ pf (p, q, r). Then one of the following holds: 
hy1,1 bO(gA(xi’1 Vxil2)), 
(6-9) 

LOGICS WITHOUT COUNTABLE CHARACTERISTIC FRAMES 181 
h\ h? h}x h\r hy 
Fig. 6.7. 
J#MhO(r A^V**-2)), (6.10) 
tty1'2 ^ 0(r A (x*’1 V xi,2))i (6.11) 
My1,2 |= 0(q A (x*’1 V X*’2))- (6.12) 
If (6.9) holds then q is false at all points hlp accessible from Hy1,1. But according 
to the definition of Y (see the proof of (i)), Zip'1’1 sees only those hy at which 
p is true. By (6.5), this set must contain a point where q is true, which is a 
contradiction. Therefore, (6.9) does not hold. 
Assume now that (6.10) holds. This means that among the points accessible 
from hly1,1 there is a point hat which r is true. Then by (6.8), hljf p. On 
the other hand, hy’1*1 sees only those points h%£ where p is true, which is again 
a contradiction. 
In the same way (6.11) and (6.12) combined with (6.7) and (6.8) lead to a 
contradiction. □ 
Lemma 6.33 Every frame 0 = (V, 5) for L refuting -ie contains at least 
points. 
Proof Suppose e is true at some point e in 0 validating L. By Lemma 6.31 
(ii) 	, for every i < cj, there are points hi, h\, h? in 0 forming the diagram shown 
in Fig. 6.7 (a) and such that hi f= h\ |= X?’1* f= Xi>2- Using Lemma 6.31 
(iii) 	, one can readily prove that the points hi, h], h? are not accessible from hj, 
h), h$, for i ± j. 
Given X e Vu), define a valuation in 0 in the following way. Suppose hi, h\, 
hf\ is a triple found above. Put 
hl 1= P, p if i € X, 
H V=V, hf |= p if i £ X. 
Under this valuation e f= □tto(p) and, by Lemma 6.31 (i), e f= Ocro(p). Therefore, 
there are points hx, hlx, h2x in 0 forming the diagram as in Fig. 6.7 (b) and 
such that 

182 
INCOMPLETENESS 
hx |= X1 ) 
hlx 1= X1’1 A □(x0,1 V x0,2 ~>P) > (6-13) 
hX 1= X1’2 A □(x0,1 V x0’2 -> -<p) J 
We show that points in distinct triples of the form ftx, hx, h2x do not see each 
other. Indeed, suppose Xi,X2 G Vuj and X\ ^ X2. This means that there is 
i < u such that either i G X\, i X2 or i qL Xi, i G X2- Assume for definiteness 
that i e X1 and i X2. 
Take the triple hi, ft*, ft? determined above and define a valuation in 0 by 
putting 
x |= q iff x = ft*, 
x |= r iff x = ft?. 
It is not difficult to verify that, under this valuation, p~(pi, <7, r) is true at e and 
so, by Lemma 6.32 (ii), e f= pf (pi, <7, r), where pi is the variable used for finding 
the triple ftx15 ft^ j h2Xi. Using (6.13) with pi instead of p, we obtain: 
hx1 \= aix1’1 -> 0(9 A (x0,1 v X0,2)) a ->0(r A (x0,1 V X°’2))), (6.14) 
f= □(X1’2 - 0(r A (x0'1 V x°'2)) A A (x0’1 V x°’2))), (6.15) 
hx, |= 0(9 A (x0,1 V x0,2)) A ->0(r A (x0,1 V x°’2)). (6-16) 
h2Xl (= 0(r A (x0'1 V x°'2)) A -O(q A (x0’1 V X°’2)). (6.17) 
In exactly the same way, using pi(p2,<7,0 instead of pi(pi,<7,r), where p2 is 
the variable involved in finding the triple ftx2, ftx2> ^x2> we obtain: 
hx2 \= □(X1,1 0(r A (x0,1 V x0,2)) A ->0(q A (x0,1 V x°’2))). (6-18) 
hx2 \= D(X1,2 0(9 A (x0,1 V X0,2)) A ->0(r A (x0,1 V x°’2))), (6.19) 
hlX2 N 0(r A (x0'1 V x0’2)) A -0(g A (x0’1 V x°'2)), (6.20) 
hX2 N 0(9 A (x0,1 V x0,2)) A ->0(r A (x0,1 V x°’2))- (6.21) 
Suppose that a point in the triple hxx, hXi, h2Xi sees a point in the triple 
ftx2, ftx2i ^x2- Then by the transitivity, ftxiS^x2 or hxxSh2X2. In the former 
case we arrive at a contradiction between (6.20) and (6.14), and in the latter one 
between (6.21) and (6.15). Other possibilities are considered analogously. 
It follows that there are 3i distinct points of the form ftx, ftx, ftx> f°r 
X G Vuj. 
Suppose now that we have already proved that, for every X G V1uj, there 
exist points hx, hx, h2x forming the diagram as in Fig. 6.7 (b) and such that 
hx f= X\ ftx 1= hx |= xi>2. Suppose also that points in distinct triples of 
that form do not see each other. Using Lemma 6.32, in the same way as before 
we obtain that, for every Y G Vt+1w, there are points fty, fty, fty forming the 
diagram as in Fig. 6.7 (c) and such that fty |= xl+1> h\ |= x*+1,1> hy \= Xl+1>2- 

EXERCISES AND OPEN PROBLEMS 
183 
Besides, points in distinct triples of the form /iy, /iy, hy do not see each other. 
Therefore, there are 3*+! points of this sort. Thus, for each i <uj, the cardinality 
of 0 is greater than 3* and so |0| > 3^. □ 
This completes the proof of Theorem 6.30. □ 
Slightly modifying the argument-above, we can prove 
Theorem 6.34 There is a Kripke complete quasi-normal extension L of K4 
such that every frame for L contains at least points. 
Proof It suffices to take L = Log(3r, {e}), where $ is the frame in Fig. 6.6. 
□ 
Of course this result does not hold for ExtS4 and Extint (why?). However 
we still have 
Theorem 6.35 There are logics in NExtS4 and Extint that are characterized 
by Kripke frames of cardinality but are not approximate by frames of smaller 
cardinality. 
The idea of the proof is similar to that of Theorem 6.30 but technically it is 
somewhat more complicated. 
6.7 	Exercises and open problems 
Exercise 6.1 Show that the canonical model for GL contains a continuum of 
reflexive points. (Hint: prove that the sets 
GL U {Dip —> ip : ip e For.A/f£}U 
{pi G VarMC : i G 1} U {-^pi : pi G VarMC, i 1} 
are GL-consistent for every I Co;.) 
Exercise 6.2 Show that the canonical frames for the logics GL and Grz are 
not Noetherian. 
Exercise 6.3 Prove that the canonical frame for Grz contains a proper cluster. 
(Hint: show that the tableaux (I\0) and (A, 0), where 
T = {p} U {-'Dip : ip ^ Grz}, A = {-•p} U {-'Dip : ip ^ Grz}, 
are Grz-consistent and all extensions of them in the canonical model see each 
other.) 
Exercise 6.4 Show that K40<$ is not strongly complete, where <5 is the formula 
defined in Section 6.3. 
Exercise 6.5 Show that GL in the language with one variable is not strongly 
complete. 

184 
INCOMPLETENESS 
Exercise 6.6 Show that GL.3 is neither strongly complete nor characterized 
by an elementary class of frames. 
Exercise 6.7 Show that the set of formulas which are true in the model Wl 
defined in Section 6.4 is not closed under Subst. 
Exercise 6.8 Show that Dum and SL are not strongly complete. 
Exercise 6.9 Prove that the logic T ® □(□2p —> D3p) —* (Dp —> D2p) is not 
finitely approximable. (Hint: show that every intransitive frame for this logic is 
infinite and that tra does not belong to it; to prove the latter use the frame 
5H = (a;, R), where nRm iff m > n — 1, which is known as the recession frame.) 
Exercise 6.10 Show that there is no finitely approximable logic in the interval 
[K © □(□2p -> D3p) -> (Dp -+ □2p),Log£R]. 
Exercise 6.11 Show that T©DpAg —► 0(D2p/\0q) is not finitely approximable. 
Exercise 6.12 Prove that K © ODp V □(□(□# —> q) —> q) is incomplete. (Hint: 
show that the formula ODp V Dp does not belong to this logic and cannot 
be separated from it by a Kripke frame; to prove the former use the frame 
(u) U {a;, u) + 1}, R) where xRy iff either x, y E uj U {a;} and x>y ox x = uj + \ 
and y = u.) 
Exercise 6.13 Show that the formula ODp V □(□(□<? —* q) —> q) is valid in a 
frame $ = (W, R) iff $ satisfies the condition 
Vx (~^3y xRy V 3z (xRz A ->3u zRu)). 
Exercise 6.14 Show that the logic K©0Dp\jDp is canonical, with its canonical 
frame satisfying the condition in the previous exercise. 
Exercise 6.15 Prove that K©D(Dp p) —> Dp is incomplete. (Hint: tra does 
not belong to this logic.) 
Exercise 6.16 Does the equality L -I- P|-€/ Li = f)ieJ(L -I- Li) hold in Extint? 
(Hint: assuming that it holds, prove that all si-logics are finitely approximable.) 
Exercise 6.17 Show that T © D(D(p Dp) —> D3p) —> p is neither complete 
nor elementary. 
Exercise 6.18 Construct a logic in NExtKB which is not finitely approximable. 
Exercise 6.19 Construct a normal modal logic with arbitrarily large finite 
rooted frames but without infinite ones. 
Exercise 6.20 Construct a complete (finitely approximable) logic L e NExtK 
and a variable free formula such that L © <p is not complete (finitely 
approximable) . 
Exercise 6.21 Construct a logic in NExtAlt2 that is not finitely approximable. 

NOTES 
185 
nontransitive 
Fig. 6.8. 
Exercise 6.22 Prove that the class NExtAlti is countable and NExtAlt2 is 
continual. 
Exercise 6.23 Prove that the set of tense formulas that are true in the model 
(#, 27), where $ = (u>) and 2J is a bijection from the set of variables onto the 
family of all finite and cofinite subsets of u;, is a consistent tense logic10 but has 
no Kripke frames. 
Problem 6.1 Call a logic L locally compact if every fragment of L with n < u 
variables is compact Are there locally compact logics that are not compact? 
6.8 	Notes 
The results of investigating modal and si-logics in the first half of the 1960s gave 
no reason to doubt that all modal and (especially) si-logics can be characterized 
by Kripke frames. Actually, there were no doubts that these logics are a sort of 
fragments of classical first order logic. However, in the late 1960s and early 1970s 
a series of “negative” results appeared, started by Jankov’s (1968b) example of a 
si-logic which is not finitely approximable and modal and si-calculi of that kind 
constructed by Makinson (1969), Kuznetsov and Gerchiu (1970) and Fine (1972). 
(The result of Exercise 6.21 is due to Bellissima (1988) and that of Exercise 6.18 
to Wolter (1993).) 
In fact the “negative” results presented in this chapter show that the 
languages of modal and si-logics with the frame interpretation have a rather strong 
expressive power, in some respects stronger than the classical first order 
language. Moreover, Thomason (1975b) showed that in a sense classical second 
order logic can be effectively embedded into a propositional modal logic with the 
frame interpretation. Note, however, that no analogous result has been proved 
for si-logics, though Thomason’s (1975b) idea seems to be enough to justify it. 
The first modal formula without a first order equivalent on frames—the McK- 
insey formula ma—was found by van Benthem (1975) and Goldblatt (1975), 
10Recall that tense logics are closed under the rules ip/Gip, ip/Hip. 

186 
INCOMPLETENESS 
though their proofs were different: the former used countable elementary 
submodels (i.e., the Lowenheim-Skolem theorem), and the latter ultraproducts. 
Notice that it is not hard also to prove this result with the help of the compactness 
theorem in the same manner as in Section 6.2. Later Doets (1987) showed that 
ma does not have a first order equivalent even on the class of finite frames; 
see also van Benthem (1989). Indeed, it is easy to see that ma is valid in the 
frames 3n shown in Fig. 6.8, where n is the number of final points, iff n is odd. 
Now, if ma is first order definable then, according to van Benthem (1976a), it 
has a single (!) first order formula as its equivalent, and using the technique of 
Ehrenfeucht (1961) games (see also Exercise 1.3.15 in Chang and Keisler (1990) 
which does not use the game terminology) one can show that for every first order 
formula 0 there is m such that 0 is valid in all 3n for n > m or is refuted in 
all such frames no matter whether n is even or odd. Goldblatt (1991) proved 
that K © ma is not canonical and Wang (1992) showed that it is not strongly 
Kripke complete. Observe, by the way, that both la and grz are clearly first 
order definable on finite frames. According to Boolos and Sambin (1991), Fine 
and Rautenberg were the first to notice that GL is not strongly complete, and 
Goldfarb proved this using formulas in one variable. Exercise 6.3 is due to Hughes 
and Cresswell (1982). 
One more interesting example of Doets (1987): the Fine formula 
OD(p V q) —* O(Dp V Dq) 
is equivalent on countable frames to the following first order condition: 
Vx, y (xRy —> 3z (xRz A Vu (zRu —> yRu) A Vu, v (zRu A zRv —> u = v))) 
but on the class of all frames it does not have a first order equivalent. The latter 
is proved with the help of the intransitive frame # which consists of a root seeing 
all points represented by infinite subsets of natural numbers, which in turn see 
exactly the natural numbers contained in them. It is not hard to check that S' 
validates the Fine formula but does not satisfy the first order condition above, 
which, by the Lowenheim-Skolem theorem, means that the formula is not first 
order definable. Intuitionistic formulas with similar properties were constructed 
by Chagrova (1989b). However, the following problem of Doets (1987) is still 
open: which is the least cardinal x such that a formula is first order definable 
whenever it is definable on frames of cardinality < xl 
First examples of intuitionistic formulas—sa and bbn—without first order 
equivalents were given by van Benthem (1984) and Rodenburg (1986). In 
Section 6.2 we established this result for bbn using Shimura’s (1995) theorem 
(Theorem 6.9) that no logic in the interval [Int,T2] save Int is strongly Kripke 
complete and the fact (to be proved in Section 10.2) that Kripke completeness 
and elementarity imply canonicity. The Scott axiom may also be treated in the 
same way using another result of Shimura (1995): no si-logic in the interval 
[SL, SL + bds) is strongly complete. (Note by the way that SL in any language 

NOTES 
187 
an+2 
with finitely many variables is canonical, as has been recently observed by Ghi- 
lardi, Meloni and Miglioli.) Here we outline a direct proof due to van Benthem 
(1984) and Rodenburg (1986), which is based on the compactness theorem. 
For the Scott axiom sa we consider frames of the form shown in Fig. 6.9 
and describe them by means of first order formulas in the same manner as in 
the proof of Theorem 6.7. Now, by the compactness theorem, if sa is first order 
definable then it must be valid in a frame $ of the form depicted in Fig. 6.10, 
where points in the “box” W' are incomparable with a*s and 6*s. On the other 
hand, a valuation in # such that p is true only at a*, for all i < u), refutes sa, 
which is a contradiction. 
To prove that bbns are not first order definable one can use in the same 
way the frames in Fig. 6.11. In view of the result of Doets (1987) according to 
which only a finite number of Nishimura formulas are first order definable (and 
the remaining are not first order definable even on the class of finite frames), 
it seems that Shimura’s (1995) theorem can be extended to almost all si-logics 
with extra axioms in one variable. 
An interesting example was found by Hughes (1990). He showed that the 
logic KMT = K0 {0((Dpi —> pi) A ... A (Dpn —> pn)) : n > 1} is characterized 
by the class of frames satisfying the condition \/x3y (xRy A yRy), it is finitely 
approximable and decidable but not finitely axiomatizable and elementary. 

188 
INCOMPLETENESS 
bi 62 h bn bn+1 
0 c 
> c 
> c 
> c 
> 
‘ 1 1 
1 1 
! w' ! 
1 1 
0 
} ►( 
} ... c 
} ►( 
... L ' 
fli a 2 013 ^n+i 
Fig. 6.11. 
In general, for modal and intuitionistic formulas with the frame semantics 
one can refute practically all properties typical for first order formulas. However, 
there are partial exceptions. For instance, according to Corollary 2.1.5 of Chang 
and Keisler (1990), if a theory has arbitrarily large finite models, then it has an 
infinite model. Of course, in our case we should speak about rooted frames. Here 
is an example of a tense logic with arbitrarily large finite frames but without 
infinite ones: it suffices to extend the minimal tense logic by the axioms of GL.3 
for both □ and D”1. It is easy to see that rooted frames for this logic are of 
the form ({1,... ,n}, <). It turns out, however, that for logics in NExtK4 and 
Extint an analog of Corollary 2.1.5 in Chang and Keisler (1990) holds; see 
Chagrov (1995). 
The effect of Kripke incompleteness was first discovered by Thomason (1972b) 
for tense logics (see Exercise 6.23), and then Thomason (1972a) constructed 
a non-compact modal logic in NExtT. Rybakov (1977, 1978a) and Shehtman 
(1980) extended the latter result to NExtGrz and Extint. It is worth noting that 
the non-compact logic of Rybakov (1978a) is decidable and that of Shehtman 
(1980) is axiomatizable by formulas in two variables. Kripke incomplete normal 
modal calculi were first constructed by Fine (1974b) and Thomason (1974a), 
and an incomplete si-calculus by Shehtman (1977). Other examples of that sort 
can be found in Blok (1978) (see Section 10.5), van Benthem (1978, 1979a), 
Boolos (1980). Usually incomplete logics in NExtK are constructed with the 
help of various modifications of the so called “recession frame” first used by 
Makinson (1969); it is defined in Exercise 6.9. Note by the way that the logic of 
the recession frame was (finitely) axiomatized by Blok (1979). In NExtK4 and 
Extint all known constructions of incomplete logics are based upon modifications 
of the frame of Fine (1974b); for another application of this frame see Chagrov 
and Zakharyaschev (1995a). 
Every Kripke complete logic is complete with respect to the neighborhood 
semantics. However, the converse does not hold, as was discovered by Gerson 
(1975a). Nevertheless it does not guarantee completeness either: Gerson (1975b) 
constructed the first example of a modal logic that is not complete with respect 
to the neighborhood semantics and Shehtman (1980) extended this result to the 
class NExtGrz. In Section 6.5, written on the material of Shehtman (1977, 1980), 
we saw that this does not provide us with si-logics that are not complete with 
respect to the neighborhood semantics. The question on the existence of such 

NOTES 
189 
logics, raised by Kuznetsov (1975), is still open. Problem 6.1 is due to Shehtman 
(1980). 
Another variant of the completeness problem is connected with transferring 
the Lowenheim-Skolem theorem to modal and si-logics. Are countable frames 
enough to characterize all Kripke complete modal and si-logics? This question 
was raised by Hosoi and Ono (1973). A negative solution to it for tense logics was 
obtained by Thomason (1975a) and for modal and si-logics by Shehtman (1983). 
Theorem 6.30 is due to Chagrov (1986). It is not known, however, what is the 
minimal cardinality of frames that are enough to characterize all Kripke complete 
logics. This problem was formulated by Kuznetsov; see Shehtman (1983). Note 
that all logics of finite width are characterized by countable frames, as will be 
shown in Section 10.4. In the case of quasi-normal and polymodal logics examples 
of Kripke complete logics all frames of which contain at least a continuum of 
points were constructed by Thomason (1975a) and Chagrov (1985b). 
Two more open questions concerning the cardinality of frames also deserve 
mentioning. All the examples above were constructed semantically, and so 
nothing is known about the cardinality problem for calculi. Besides, we do not know 
any results of that sort for the neighborhood semantics. Note that these 
problems are closely related to similar problems for second order logic, which are also 
far from a complete solution. 

Part III 
