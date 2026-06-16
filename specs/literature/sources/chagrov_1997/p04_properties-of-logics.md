<!-- Source: Chagrov & Zakharyaschev (1997). Modal Logic (Oxford Logic Guides 35). Part IV: Properties of Logics — Kripke completeness, finite approximability, tabularity, interpolation (Ch 10-15). BibKey: ChagrovZakharyaschev1997 -->

Properties of logics 
Having laid in Part III a solid semantic foundation for investigating modal and 
superintuitionistic logics, we are in a position now to attack more concrete 
problems. The main question of this part is the following one: given a modal or 
superintuitionistic logic, how can we recognize whether it has such and such 
desirable properties? We have already seen how such properties as decidability, 
Kripke completeness, finite approximability, disjunction property, etc., can be 
proved for a few particular systems. Now we try to find general methods for 
proving these properties which cover wide families of logics. 

10 
KRIPKE COMPLETENESS 
Perhaps the most desirable property of a logic is its decidability. However, the 
main tool for proving it (at least in the realm of modal and superintuitionistic 
logics) is Harrop’s theorem, according to which the decidability of a finitely 
axiomatizable logic follows from its finite approximability. Likewise, to prove 
many other properties of a logic, it is desirable first to establish its completeness 
with respect to some good class of frames, the simpler the better. 
That is why we begin our study of logics’ properties with general completeness 
results. We are going to descend the stairs of the hierarchy in Section 4.3, starting 
from Kripke completeness. 
10.1 The method of canonical models revised 
The essence of the method of canonical models is to show that the canonical 
(Kripke) frame 3T of a given logic L validates L\ if this is the case then L is 
Kripke complete. Now, being equipped with general frames, we can generalize 
the method in the following way. 
Given a class C of (general) frames, we say L is C-persistent if, for every JG C, 
# |= L implies \= L (recall that the operator k gives the underlying Kripke 
frame of $). We denote by kC the class {k$ :JgC} and put C* = C U kC. 
Proposition 10.1 If a logic L is both C-complete and C-persistent then L is 
kC-complete and in particular Kripke complete. 
Proof Since L is C-complete, it is characterized by some subclass C' of C. Since 
L is C-persistent, it is sound with respect to kC. And since every formula refuted 
by a frame # is also refuted by k#, L is characterized by kC'. Hence L is kC- 
complete. □ 
Since, as we know from Section 8.4, every modal and superintuitionistic logic 
is VT-, T-, 1Z-, CM- and D-complete, we immediately obtain the following: 
Corollary 10.2 If a logic L is VP-persistent (respectively, T-, 1Z-, CM- or 
V-persistent) then L is Kripke complete. 
As an illustration let us prove 
Theorem 10.3 Each L E NExtAltn is VP-persistent, for any n <uj. 
Proof The key observation in the proof is that for every finite set of points 
X = {xi,... ,xm} in a differentiated modal frame $ = (W,R,P) there are 
disjoint sets ..., Xm e P such that Xi n X = {x^}, for i = 1,..., m. 

338 
KRIPKE COMPLETENESS 
Suppose # is a differentiated frame for L but L, Notice first that 
each point xo in # has < n distinct alternatives. For if there are distinct points 
xi,..., xn+i accessible from xq then we can put X = {xi,... ,xn+i} and define 
a valuation 23 in # by taking 23(p*) = W - Xi, where Xi E P are disjoint and 
Xi fl X = {xi}. It is readily checked that altn is false at xq under 23, which is a 
contradiction. 
Now, let a formula p € L be refuted at x in under some valuation 23. Put 
X = x|° U... U xT^, where d = md(p). Since no point in # has more than n 
successors, X is finite, say, X = {xi,... , xm}. Take disjoint sets Xi € P such 
that Xi fl X = {xi} and define a valuation it in ^ so that for every y E Xi and 
every variable p, y E il(p) iff Xi E 23(p), i = 1,... ,ra. Thus, the valuations 23 
and it coincide on the points in X and so, by Proposition 3.2, p is false at x 
under il, contrary to # |= L. □ 
Clearly, VF-, T-, 1Z-, CM- and ^-persistence are preserved under sums of 
logics. Moreover, the operators p and r preserve all these properties save VT- 
persistence. Indeed, suppose a logic M E NExtS4 is P-persistent and ^ is a 
descriptive frame for pM. By Theorem 8.53, <j$ is a descriptive modal frame 
which, by Lemma 9.67, validates M. Since K(T$ = k#, we then have |= M and 
so k# (= pK$) is a frame for pM. Suppose now that L e Extint is D-persistent 
and let ^ be a descriptive frame for tL. Then p$ is a descriptive frame for L and 
so pK^S (= npB) validates L. Therefore, by Lemma 9.67, |= tL. The same 
argument shows that p and r preserve T-, 1Z- and CA^-persistence. However, 
the operator <j does not preserve them, witness the couple Int and <7lnt = Grz, 
in which only Int is P-persistent. 
The following observation may be also of interest. 
Proposition 10.4 A modal or superintuitionistic logic L is V-persistent iff it 
is UL-persistentj where Ul is the class of universal frames for L. 
Proof The implication (=>) follows from Ul C V. To show (<£=) suppose # is 
a descriptive x-generated frame for L. Then by Theorem 8.60, # is a generated 
subframe of And since k$l{x) |= L, we must also have |= L. □ 
Each P-persistent logic is clearly canonical and so strongly Kripke complete. 
We give now a semantic characterization of strongly complete logics in NExtK 
and Extint. Say that a normal modal or si-logic L is x-complex, x a cardinal, 
if every modal (respectively, pseudo-Boolean) algebra for L with < x generators 
is a subalgebra of Sr+ for some Kripke frame # validating L. 
Theorem 10.5 For every logic L E NExtK in an infinite language with x 
variables the following conditions are equivalent: 
(i) L is strongly Kripke complete; 
(ii) L is x-complex; 
(iii) L is strongly globally Kripke complete. 
Proof (i) => (ii) Let 21 be a modal algebra for L with < x generators and 23 a 
valuation in 21 such that the set of all 23(p), p a variable in the language of L, 

THE METHOD OF CANONICAL MODELS REVISED 
339 
generates 21. (One can consider 93 as a homomorphism of 21l(x) onto 21.) Let V 
be a prime filter in 21 and A its complement prime ideal. The pair t = (V', A'), 
where 
V' = {if : 9%) G V}, A' = {ip : 9%) G A}, 
is then a maximal L-consistent tableau (for otherwise we would have a G V 
and be A such that a —> b = T, which is impossible). Since L is strongly 
complete, there is a rooted model 9Jtv = (i?v>2Jv) based upon a Kripke frame 
5v for L and such that t is realized at its root xv- Consider the disjoint union 
9Jt = (5,U) of all such 9Jtv By the disjoint union theorem, the Kripke frame 5 
validates L. Let 0 = (W, P, P) be the general frame associated with 9Jt. Clearly 
0+ is a subalgebra of 5+- We show now that the map 93(<p) i—> il(<p) is an 
isomorphism from 21 onto 0+. It follows immediately from the definition that 
this map is a surjective homomorphism. So, by Theorem 7.71, it remains to show 
that 93(<p) = T iff il(<p) = W, for every formula <p. In the modal case we have 
9%) = T iff Vn < u) 93(DrV) = T 
iff Vn < o;VV G Wa 93(DrV) G V 
iff Vn < o;VV G Wqi Oncp e V' 
iff Vn < uVV G W<2t xv |= 
iffil(^) = W. 
(ii) => (iii) Suppose T </?. Then by Theorem 7.73, there is an algebra 21 
for L and a valuation 2J in it such that 9J(V>) = T, for all ^ € T, and 9J(</?) ^ T. 
Without loss of generality we may clearly assume 21 to have < x generators. 
Since L is x-complex, there is a Kripke frame 5 = (W, R) for L such that 21 is 
(isomorphic to) a subalgebra of 5+ and we can consider 2J as a valuation in 5- 
Put 2R = (5,23). But then SDT (= T and 2JI ^ tp. 
(iii) => (i) Suppose T is an L-consistent set of formulas and p a variable not 
occurring in T (here we use the fact that x is infinite). Put 
A = {p} U {On(p —></?):</? G T, n < u} 
and show that A is L-consistent too. Indeed, let A' be a finite subset of A. 
Without loss of generality we may assume that A' consists of p and the formulas 
of the form Dn(p —> </?), where n < m and G T', for some m < uj and finite 
T' C T. Since T is L-consistent, there is a model 9Jt = (5,93) based on a frame 
for L and such that x |= T for some x in 5- Define a new valuation it in 5 by 
taking il(p) = 23(/\r') and il(^) = 93(g) for q ^ p. Under it we clearly have 
x \= Af. Consequently, A is L-consistent. 
By the deduction theorem, it follows that {p —> (p : (p e T} \/*L ->p. Since L 
is strongly globally complete, there is a model 93 based on a Kripke frame for 
L and such that 93 f= p —></?, for all tp G T, and (93, x) f= p, for some x in 93. 
Therefore, x |= T, which completes the proof. □ 

340 
KRIPKE COMPLETENESS 
In the intuitionistic case this theorem reduces to 
Corollary 10.6 A si-logic in a language with x variables is strongly Kripke 
complete iff it is x-complex. 
As another consequence we show that the operator r preserves strong 
completeness. Suppose L is a strongly complete si-logic in the infinite language with 
x variables and $ a descriptive frame for tL with < x generators. Then p$ is 
a descriptive frame for L with < x generators. Since L is x-complex, there is a 
Kripke frame 0 for L such that p#"1" is a subalgebra of 0+. Let x' be a cardinal 
which is bigger than |$\. Then the Kripke frame x/0 (obtained from 0 by 
replacing its points with x'-point clusters) validates tL and it is not hard to check 
that Sr+ is a subalgebra of (x'0)+. Thus, tL is x-complex and so strongly 
complete. That p preserves strong completeness can be proved using a syntactical 
argument; we leave this to the reader. 
To establish that the canonical frame validates L, we showed in Section 5.2 
that satisfies some first order sentence (j) which characterizes the class of 
Kripke frames for L. Of course, nothing prevents us from trying to characterize 
classes of general frames by such kind of sentences. Given a class C of general 
frames, we say a logic L is C-elementary if there is a set $ of first order sentences 
(in the language with R and = as its only predicates) such that, for every J G C, 
# is a frame for L iff # is a (classical) model for $. A first order sentence (j) in 
R and = says nothing about sets of possible values, and so a general frame # 
satisfies (j> iff satisfies <f. Therefore, we have 
Proposition 10.7 If a logic L is C*-elementary then it is C-persistent. 
And now, combining Propositions 10.1 and 10.7, we arrive at 
Theorem 10.8 If a logic L is C-complete and C*-elementary then L is kC- 
complete and in particular, Kripke complete. 
Thus, to prove the Kripke completeness of a logic L, it suffices to find a first- 
order characterization of frames for L in some class C* which is big enough to 
ensure C-completeness of L. For instance, one can take as C any of the classes 
mentioned in Corollary 10.2. 
Example 10.9 Suppose Lo € NExtK is T- (or 1Z- or V-) persistent (and so 
Kripke complete). With the help of Theorem 10.8 we can prove that the logic 
L = Lo 0 Op —► □ Up is also Kripke complete. 
Take the class C of all tight (or, respectively, refined or descriptive) frames for 
Lo and establish that L is C*-elementary. In fact, we show that, for every J G C*, 
# |= L iff # is transitive. Indeed, suppose # = (W,R,P) validates Up —> UUp 
but there are points x, y, z in 3 such that xRyRz and -ixRz. By the tightness 
of #, we then have a set X e P for which x G UX and z & X. Define a valuation 
2J on # by taking 9J(p) = X. Then, under this valuation, x\= Up but x Y=- UUp, 
since z ^ p, which is a contradiction. The converse implication follows directly 
from Proposition 3.31. 

^-PERSISTENCE AND ELEMENTARITY 
341 
• 
• 
(a) 
(0) 
(b) 
FIG. 10.1. 
But how to find a first order equivalent of a given formula, if any, modulo 
some appropriate class of frames? In Sections 2.5 and 3.5 we used ad hoc 
techniques for obtaining first order equivalents of several particular formulas in the 
class of Kripke frames. However, it turns out that for an extensive family of 
modal formulas there is a purely mechanical procedure effectively constructing 
first order equivalents (in R and =) in the class P*, which immediately gives 
us P-persistence, canonicity and strong Kripke completeness plus a first order 
characterization of Kripke frames. This result, known as Sahlqvist’s theorem, will 
be proved in Section 10.3. But before that we establish a deep connection 
between the notions of elementarity, completeness and P-persistence, which shows 
that the method of canonical models is applicable to all logics characterized by 
elementary classes of Kripke frames. 
10.2 P-persistence and elementarily 
We consider first the modal case and then use the preservation theorem to 
transfer the main result to superintuitionistic logics. 
The difference between ordinary Kripke frames and the underlying Kripke 
frames of descriptive frames is that the latter may be regarded as the sets of 
ultrafilters over the world spaces of the former. Given a Kripke frame # = (W, i?), 
the Kripke frame k($+)+ is called the ultrafilter extension of # and denoted by 
i? = (w,R^. We remind the reader that W is the set of ultrafilters in Sr+ (i.e., 
in the Boolean algebra with the universe 2W) and, for all ui,U2 £ W, u\Ru2 iff 
VIC w (nx e m -> X G u2). 
Example 10.10 Let # = (W,il) be the frame depicted in Fig. 10.1 (a). Then 
# is of the form shown in Fig. 10.1 (b), i.e., # can be obtained from # by 
adding to it a continual root cluster. Indeed, the set W consists of two types 
of ultrafilters: principal and non-principal. Principal ultrafilters are sets of the 
form a = {X C W : aGl}, where a eW. Every non-principal ultrafilter must 
contain all cofinite subsets in W\ such ultrafilters will be denoted by the letters 
u and v. 
Observe first that, for every u, v and a, we have uRa and uRv. For suppose 
RX G u. Since 0 ^ n, the set HX is not empty. Hence, UX must be infinite 

342 
KRIPKE COMPLETENESS 
(because every non-principal ultrafilter contains only infinite sets) and so there 
is only one possibility: DX = W, from which X = IT, X G a and X G v. It is 
easily seen that aRb iff aRb. That the root cluster in # contains a continuum of 
points is proved in the next theorem. 
Clearly, every finite frame is isomorphic to its ultrafilter extension. However, 
the ultrafilter extensions of infinite frames are essentially different. 
Theorem 10.11 If a frame $ is denumerable then $ is continual. 
Proof It is sufficient to show that over a denumerable set W there is at least 
a continuum of ultrafilters. Let W = {a$,a\,a2,...}. Construct the sets Xq = 
{ao, a2,04,...}, X\ = {a\, as, <25,...}. Notice that they cannot belong to the 
same ultrafilter, since Xq = W — X\. 
Suppose now that we have already constructed infinite sets 
> Xi\i2 > • • • 5 *^1 
l\l2 •■•Ik 
such that X-i^ ID X.^^^ ID ... ID ^^i\i2...ik and 
--ik = {.ajo'>a3na32'> * * •}» 30 < jl < 32 < • • • • 
Consider the sets 
- {.ajo 1 aj2 » aj4 >•••}» Xi1i2...ik 1 {aji ’ a3z ’ a35 »•••}• 
Since they are disjoint, they cannot belong to the same ultrafilter. 
Let 21^3 ■ • • and jij2j3 • • • be distinct infinite words in the alphabet {0,1}. 
By the construction, the sets 
> Xi\i2 ) Xi1i2i3 ,•••}, {^j\ > Xjxj2 , Xjlj2j3 , • . •} 
cannot belong simultaneously to the same ultrafilter. It remains to notice that 
there are a continuum of sets of that sort, each of them has the finite intersection 
property and so belong to an ultrafilter over W. □ 
On the other hand, we obviously have 
Proposition 10.12 A frame $ is isomorphic to a subframe of$, with the map 
x i-> x being an isomorphism. 
Of course, in general # is not a generated subframe of #. Take, for instance, 
the frame # = (u,<). Then every point in u sees a point in IT. In the 
ultrafilter extensions of (Q, <) and (R, <) “old” and “new” points are heavily mixed. 
However, in some cases we can determine the position of # in # perfectly well. 
Theorem 10.13 Suppose # = (W, R) is a transitive frame all points in which 
are of finite depth and, for every d < uj, W=d is finite. Then $ is (isomorphic 
to) a generated subframe of$, with W = W<0° = W<OQ. 

D-PERSISTENCE AND ELEMENTARITY 
343 
Proof Let u be a non-principal ultrafilter over W and a a principal one, for 
a G W. Clearly, a G □(a|) G a. Since a\ is finite, a]$ u and so a does not see u 
in $. Therefore, in view of Proposition 10.12, # is a generated subframe of *$. 
We show that every non-principal ultrafilter u in # sees points from $ of any 
finite depth. Let us begin with points of depth 1. Suppose a\,..., an are all such 
points and u sees none of them. This means that there are sets X\,..., Xn C W 
such that DXi G u (and so □(Xi fl... D Xn) G u), but Xi ai, i.e. a* g Xi, for 
1 <i <n. Let X = X\ fl... D Xn. By the definition, DX is infinite and a* ^ X. 
Therefore, there are infinitely many points in which see only points in X. It 
follows that X ^ 0, for otherwise would contain infinitely many dead ends. 
But if a point x in DX sees any point in X then (by transitivity) xRai, for some 
i < n, and so ai € X, which is a contradiction. 
Let us prove now that u sees points a of an arbitrary finite depth. Suppose 
otherwise, i.e., u does not see points of depth > m, and let ai,... ,an be all the 
points in of depth m + 1. Suppose also that X\,..., Xn are such that DX G u 
and ai X, for 1 < i < n, where again X = Xi D ... D Xn. The set X consists 
of points of depth < m, for otherwise a point in DX would see one of ai, which 
means that ai € X. By the definition, there are finitely many points seeing only 
points of depth < m. So the set DX is finite, contrary to u being a non-principal 
ultrafilter. □ 
The requirement of finiteness of W=d in Theorem 10.13 is essential. Without 
it the result does not hold: the ultrafilter extension of (u;, 0) is just a continual 
set of mutually inaccessible points. However, we clearly have 
Corollary 10.14 If a Kripke frame is transitive and each of its points has a 
finite number of successors then $ C 
Theorem 10.15 If $ is a transitive rooted frame then $ is also rooted. 
Proof Suppose # = (W, R) and a\ = W. We show that aRx for every x G W. 
If x = b, for some b G W, then aRb follows from Proposition 10.12. Let u be 
a non-principal ultrafilter over W. Take any set DX in a. Then a G OX, from 
which X = W or X = W — {a}. In both cases X is in u (as well as in any other 
non-principal ultrafilter). Therefore, aRu. □ 
The following example demonstrates that the requirement of transitivity was 
essential in Theorem 10.15. 
Example 10.16 Let # = (w,R), where R = {(n,n + 1) : n G u}. We show 
that 5 is not rooted. Observe first that there is no point x in 5 such that xRO. 
Indeed, since — {0}) = u, we have D(cc; — {0}) G x for every x in 5; however, 
^ {^} ^ 0. Thus, if # is rooted then 0 is its root. 
Now we show that, for every n < u, nRx implies x = n + 1. Since D{n +1} = 
{n}, we have D{n + 1} G n and then nRx means {n + 1} G x, i.e., x = n + 1 (if 
an ultrafilter contains a singleton then it is generated by the singleton). Hence 
0 Rn x means x — n. Ergo 0 cannot be a root of 5, because the cardinality of # 
is that of the continuum. 

344 
KRIPKE COMPLETENESS 
After clarifying to some extent the relation between frames and their 
ultrafilter extensions, let us return to modal logics. 
Proposition 10.17 For every Kripke frame S and every logic L,S |= L implies 
S |= L- 
Proof According to Corollary 8.25, is a subalgebra of (#)+. □ 
It follows immediately from the definition of ultrafilter extension that for a 
D-persistent logic the converse is also true. 
Proposition 10.18 For every Kripke frame S and every V-persistent logic L, 
S \= L implies S |= L. 
We are in a position now to prove the main result of this section. 
Theorem 10.19. (The Fine-van Benthem theorem) If a logic L G NExtK 
is characterized by an elementary class C of Kripke frames then L is V-persistent 
Proof We consider here only the case of elementary L, i.e., C is assumed to be 
the class of all Kripke frames for L. The general case is left to the reader (for a 
hint see Exercise 10.11). 
Let $ be a set of first order sentences in the language C\ with R and = as 
its only predicate symbols such that, for every Kripke frame S, S £ C iff S f= 
Take any S = (W, R) in C and enrich the language C\ with the unary predicate 
Px, for every X C W} and the individual constant ca, for every a G W. We 
will interpret Px(x) in S as x G X, ca as a and instead of ca write simply a if 
understood. Let be the set of sentences in the enriched language C[ that are 
true in #. Clearly, we have $ C <£' and for every sentence <j> in £'l5 either 0 G 
or -*0 G (in particular, if 0 is a sentence in C\ and 0 $ then -*0 G $'). 
After that we again extend our first order language in the following way. Let 
II be a set of formulas in with one free variable x such that, for each finite 
subset II' of II, there is a point a in S at which all the formulas (f)(x) G II' 
are satisfied, i.e., S 1= 0(&)* We associate with each such II a new individual 
constant c, add it to thus obtaining a language and add 0(c) to for 
every 0(x) G II, thus obtaining a new set 
Note that for each ultrafilter u over W7 we have introduced a new constant— 
denote it by cu—such that Px(cu) £ for all X G u. Indeed, since u has 
the finite intersection property, for every finite subset {Px 1{x), • • •, Pxn{%)} of 
{Px{x) : X G u}, there must be a point a G W such that a G Xi fl... D Xn, 
i.e., S |= Px1 n...nxn(a) or, in other words, S b Pxx{p),... \= Pxn(a)• 
Since every finite subset of has a model (e.g. #), by the compactness 
theorem of classical model theory, also has a model, say S' = (W,iR/). 
Clearly, S' G C and S C y. _ 
Define a map / from W' into W by taking, for each a G Wf, 
f(a) = {XCW: S'[= Px(x)[a}} 
and show that / is a reduction of S' to S, from which it will follow that $ \= L. 

D-PERSISTENCE AND ELEMENTARITY 
345 
Let us check first that /(a) is an ultrafilter over IT, i.e., it satisfies the 
conditions (4a)-(4c) in Theorem 7.23 and, for every X C IT, either X or W — X 
is in f(a). (4a) follows from S' |= Pvv(a) (since Vx Pw(x) G $'); (4b) is 
ensured by S' 1= Px{p) A Py(a) PxnY(a). S' (= Px(a) Py(a), for any 
icy, implies (4c). Finally, suppose X /(a), i.e., S' |= ^Px(a). Then, using 
S' (= ^Px(a) <-► Pw-x(a), we obtain S' |= Pw-x\a) and so W - X e f(a). 
Now we show that / is a surjection. Let u G IT. If u is a principal ultrafilter, 
i.e., u = a for some a G IT, then clearly /(a) = a. And if u is not principal then 
we have 5' |= Px(cu) iff I G u, and so u = f(cu). 
It remains to verify the reduction conditions (Rl) and (R2). Suppose aR'b 
and OX G /(a), i.e., S' 1= Pdx(g). Since the formula 
VxVy (Pax(x)/\xRy -► Px(y)) 
is true in S, it must be also true in S'• Therefore, 5' |= Px(b), i.e., X G /(&), and 
so f(a)Rf(b). Thus, (Rl) holds. To verify (R2), suppose f(a)Rf(b) and show 
that there is a point c in S' such that aR'c and /(c) = f(b). Consider the set 
of conditions Px(z), for X G /(&), and aRz. Every finite subset of this set, say 
(Pxi(z), •.., Pxn(z),aRz}, or equivalently {Px(z),aRz}, for X = XiH.. .DXn, 
is satisfied in # at some point z. Indeed, suppose that S Px(z) A aRz for any 
z G IT, i.e., S \=Vz (aRz —► ->Px(z)). Then 5 |= Vz (aRz —► Pw-x(z)), whence 
□ (W — X) G /(a) and so, since f(a)Rf(b), we have IT — X G /(&), contrary to 
X G /(&). By the definition of S', there is c G IT' such that aR'c and S' 1= Px(c), 
for all X G /(&). It remains to establish f(c) = f(b). The inclusion f(b) C f(c) 
is evident. Suppose X G /(c), i.e., 5' |= Px(c). If X ^ /(&) then IT - X G /(&) 
and so S' 1= Pvv-x(c), contrary to S' (= Px(c) and /(c) being a proper filter. 
Therefore, /(c) C /(&). 
Thus, we have showed that S G C whenever # G C. To complete the proof 
of the Fine-van Benthem theorem, suppose 0 is a descriptive frame for L and 
show that k0 |= L. 
Algebraically 0 |= L means that 0+ G VarL and so, by Tarski’s theorem 
(Theorem 7.80), 0+ G HSPC+, where C+ = {S* : # G C}. Clearly, C is closed 
under disjoint unions and so, by Theorem 8.75, C+ is closed under direct 
products, i.e., PC+ = C+. Hence, 0+ G HSC+. This means that 0+ is a homomorphic 
image of an algebra 21 which, in turn, is a subalgebra of some 23 G C+. By 
Theorem 8.59, 0 is a generated subframe of 21+ and, by Theorem 8.71, 21+ is a reduct 
of 23+. Since 5 G C implies 5 G C, we may assume that 23+ is isomorphic to a 
descriptive frame f) such that nfi |= L. Then k21+ is a reduct of from which 
«2l+ |= L by the reduction theorem, and k<& is a generated subframe of «2l+, 
from which K0 |= L by the generation theorem. □ 
To transfer the Fine-van Benthem theorem to si-logics we require one more 
preservation theorem. 

346 
KRIPKE COMPLETENESS 
Theorem 10.20 If a logic L G Extint is characterized by an elementary class 
of Kripke frames then tL is also characterized by an elementary class of Kripke 
frames. 
Proof Suppose L is characterized by a class C of intuitionistic Kripke frames 
and $ is a set of first order formulas (in = and R) such that, for any Kripke 
frame $ G C iff # |= $. Of course, we may assume $ to contain the axioms 
of partial order. By Theorem 9.70 (in which we take (W,R) = (kW,kR)) 
and the skeleton lemma, tL is characterized by the class Cf of all quasi-ordered 
Kripke frames 3 such that p3 G C. We show that Cf is elementary, namely Cf 
is the class of models for the set = {(/)' : (j) G $} of first order formulas, 
where (j.V is obtained from (j) by replacing every subformula of the form x = y 
with xRy A yRx. Indeed, under this transformation the axioms of partial order 
become the axioms of quasi-order. Besides, by induction on the construction of 
<f>(xi,...,xn) it is easy to prove that, for every quasi-order 3 and all points 
ai,...,a„ in <8, <8 |= 0'(ai,... ,an) iff p3 |= 0(C(ai),..., C(an)). It follows 
immediately that 3 G Cf iff p3 G C iff p3 \= $ iff 3 |= □ 
Corollary 10.21 If a si-logic is elementary then its smallest modal companion 
is also elementary. 
With the help of this result and the fact that the operators p and r 
preserve D-persistence we can easily prove the intuitionistic variant of the Fine-van 
Bent hem theorem. 
Theorem 10.22 If a si-logic L is characterized by an elementary class of Kripke 
frames then L is V-persistent. 
Proof According to Theorem 10.20, tL is characterized by an elementary class 
of Kripke frames and so, by the Fine-van Benthem theorem, it is £>-persistent. 
By the preservation theorem, prL = L is D-persistent too. □ 
The question as to whether the converge of the Fine-van Benthem 
theorem holds (in both modal and intuitionistic cases) remains open. Of course, 
^-persistence implies Kripke completeness; but we need the completeness with 
respect to an elementary class. There is an example of a logic (see Exercise 10.10) 
which is D-persistent but not elementary; yet, it is characterized by an 
elementary subclass of the whole class of its Kripke frames. On the other hand the 
following remarkable result holds: 
Theorem 10.23 If a (normal modal or superintuitionistic) logic is IZ-persistent 
then it is elementary. 
We leave it here without a proof because too much classical model theory is 
involved in it. As is shown by Exercise 10.4, the converse of Theorem 10.23 does 
not hold. 

SAHLQVIST’S THEOREM 
347 
10.3 	Sahlqvist’s theorem 
In this section we consider a method which, given a modal formula <p in a rather 
big family, constructs effectively a first order formula in R and = characterizing 
descriptive and Kripke frames validating (p. 
First we remind the reader that, given a formula <p(pi,... ,pn) (whose 
variables are listed among pi,... ,pn), a frame # = (W, R, P) and sets Xi,..., Xn in 
P, we denote by <p(Xi,..., Xn) the set of points in # at which (p is true under the 
valuation 2J defined by 2J(p*) = X*, for i = 1,..., n, i.e., <p(Xi,..., Xn) = 2J(<p). 
Using this notation, we can say that 
(3,x) |= tpipi,. ■. ,Pn) iff VXi,...,Xn € P x € <p(XXn), 
3 \= <p(Pi,---,Pn) iff Vx € WVXi,...,Xn € P x € y>(Xi,. ..,Xn). 
Example 10.24 Let us imagine that we do not yet know anything about first 
order equivalents of the formula Dp —► p in the class of, say, tight frames and 
let us try to extract such an equivalent directly from the equivalences above and 
properties of those frames. Then for any tight frame # = (W, P, P) we shall have: 
(ff,x) |= Up -► p iff VX G P x G (DX ^ X) 
iflFVXGP(xGDX^xGX) 
iflFVX G P (x| C X —► x G X), 
since, as we know, for every n > 0, x G DnX iff x\nC. X. 
We are now at a crucial point. To eliminate the variable X ranging over P, 
we can use two simple observations. The first one is purely set-theoretic: 
VX € P (Y C X - x € X) iff x € p){X G P : Y C X}. (10.1) 
And the second one is the characteristic property of tight frames formulated in 
Proposition 8.41: 
ri{*« P: x\ C X} = x\. (10.2) 
With the help of (10.1) and (10.2) we can continue the chain of equivalences 
above with two more lines: 
(ff, x) \= Dp->p iff ... 
iffxGfl {XeP: x\ C X} 
iff x G x\. 
Therefore, # (= Dp —p iff Vx x G x|. It remains to notice that the last formula 
means nothing else but the reflexivity and can be rewritten in the more familiar 
way as Vx xRx. 
It would be strange if such a nice technique could not be extended to some 
other formulas. In fact, it can be considerably generalized. 

348 
KRIPKE COMPLETENESS 
Recall first that, by Exercise 8.1, we can replace x\ in (10.2) with any term 
of the form x\\ni U... U Xk\Uk, thus obtaining the equality 
P|{X € P : XiTni U ... U xkrk QX} = Xitni U ... U xfctnfc (10.3) 
which holds for every tight frame # = (W, R, P), every xi,..., Xk G W and every 
m,...,nfc > 0. 
A frame-theoretic term x\ Tni U...Uxjt |nfc with (not necessarily distinct) 
world variables xi,... , x*; will be for brevity called an R-term. In this section 
we reserve the letter T for denoting P-terms. Observe that the relation x E T 
on # = (W, P, P) is first order expressible in the predicates P and =. Indeed, if 
T = xiTni U...U XfcTnfe, k > 0 and ni,..., > 0 then 
X € T iff 3y\,... ,ylni-i{xiRy\ A y\Ry\ A ... A yl^Rx) 
V... V 
. • • •, A J/i-%2 A ... A y*fc_xi2x); 
if some is 0 then the corresponding disjunct has the form x = x* and when 
k = 0 we have x e T iff x E 0 iff x ^ x. This observation gives us the following 
Lemma 10.25 Suppose ip(pi,... ,pn) is a modal formula and Ti,..., Tn are R- 
terms. Then the relation x E <^(Ti,... ,Tn) ^ expressible by a first order formula 
(in R and =) having x as its only free variable. 
Proof By induction on the construction of ip. The basis of induction follows 
from the observation above, and first order equivalents of compound formulas 
are constructed in the same way as in the definition of the standard translation 
ST in Section 4.3. □ 
Syntactically, P-terms with a single world variable correspond to modal 
formulas of the form nmip1 A... A Umkpk with not necessarily distinct propositional 
variables pi,... ,p/fe. Such formulas are called strongly positive formulas. 
Lemma 10.26 Suppose <p(pi,... ,pn) is a strongly positive formula containing 
all the variables p\,... ,pn and # = (W, P, P) is a frame. Then one can effectively 
construct R-terms Ti,... ,Tn (of one variable x) such that for any x E W and 
any X\,..., Xn E P, 
xE ¥>(*!,..., Xn) iffT1CX1A...ATnCXn. 
Proof The proof proceeds by induction on the number of conjuncts in ip. If 
<p(pi) = nmPi then we have 
x E tp(Xi) iff x E nmXi 
iff x|mC X\. 

SAHLQVIST’S THEOREM 
349 
Suppose now that y>(pi,... ,pn) = ^(pi, • • • ,Pn) A nmPi where V>(Pi> • • • ,Pn) is 
a strongly positive formula with < k conjuncts and 1 < i < n. Then we have 
P-terms T\,..., Tn of one variable x such that 
xEip(X i,...,Xn) iflfTi CXi A... AT„ CX„ AxTmCXi 
iff Ti C Xi A ... A Ti U x|mC Xi A ... A Tn C Xn. 
□ 
Now, trying to extend the method of Example 10.24 to a wider class of 
formulas, we see that it still works if we replace the antecedent Up in Up —► p with 
an arbitrary strongly positive formula As to generalizations of the consequent, 
let us take first an arbitrary formula x instead of p and see what properties it 
should satisfy to be handled by our method. 
Thus, for a modal formula (V> —► x)(Pi> • • • ,Pn) with strongly positive ^ and 
a tight frame $ = (W, R, P), we have: 
(M h - x iff vXx,... ,xn e p (X e 1>(XU... ,xn) - 
xGX(Ai,...,Xn)) 
(by Lemma 10.26) iff VXi,..., Xn E P (Ti C Xi A ... A Tn C Xn —► 
xEX(Ai,...,Xn)) 
iff VXx,..., Xn _x E P (Ti C Xx A ... A Tn _ i C Xn_x ^ 
VXn E P (Tn c Xn ^ X E X (A1, . . . , Xn )) ). 
(10.1) does not help us here, but we can readily generalize it to 
VX E P (Y C X -► X E x(..., A,...)) iff 
*€p|{x(--YCXeP}. (10.4) 
So 
(ff, *) N V- -» X iff vxlf..., Xn_i € F (Ti c Xi A ... A T„_! c Xn_i -» 
x € f|{x(*i, ...,Xn): TnCXne P}). 
(Note that if pn does not occur in ?/>, and so the conjunct Tn C Xn is missing, 
we can always insert the new conjunct Xn C Xn.) But now (10.2) and (10.3) are 
useless. In fact, what we need is the equality 
p|{x(...,*,•••): TCXeP}=x(- -,f]{XeP: TCI},...) (10.5) 
which, with the help of (10.3), would give us 
p|(x(. TCXeP}=x(...,T,...). 
(10.6) 

350 
KRIPKE COMPLETENESS 
Of course, (10.5) is too good to hold for an arbitrary x, but suppose for a moment 
that our x satisfies it. Then we can eliminate step by step all the variables 
Xi,... ,Xn like this: 
($,x) (= $ - x iff VXl5... ,Xn_i G P (Ti C Xi A ... ATn_i C Xn_i - 
x € X(*i, • • •»Xn— i, Tn)) 
iff ... (by the same argument) 
iff x G x(2i,...,Tn). 
And the last relation can be effectively rewritten in the form of a first order 
formula </>(x) in R and = having x as its only free variable. So finally we shall 
have # |= t/' —► X iff </>{x). 
Now, to satisfy (10.5) x should have the property that all its operators could 
be distributed over intersections. Clearly, —► and -i are not suitable for this goal. 
But all the other operators, as it will be shown below, turn out to be good enough 
at least in descriptive and Kripke frames. So we can take as x any positive modal 
formula which may contain only _L, T, A, V, □ and O. The main property of an 
arbitrary positive formula <p(... ,p,...) is its monotonicity in every variable p, 
which means that, for all subsets X,Y of worlds in a frame #, X C Y implies 
<p(..., X,...) C <p(..., V,...) (see Exercise 3.20). 
To prove that all positive formulas satisfy (10.5) in the class V* of descriptive 
and Kripke frames, we require a lemma. A family X of non-empty subsets of 
some space W is called downward directed if for every X,Y e X there is Z G X 
such that Z C X C\Y. Note that every downward directed family has the finite 
intersection property. 
Lemma 10.27. (Esakia’s lemma) Suppose $ = (W, R, P) is a descriptive 
frame. Then for every downward directed family X C P, 
(D n w)- 
xe* xex 
Proof The inclusion (flxGX’^)i - 1S clear. So suppose that 
x G DxGX'^i’ be., x G XI and so x| Pi X ^ 0 for every X G X. It follows 
that the family {xt} U X has the finite intersection property. Since $ is tight, 
x| = G P : x| C X} and so the family {X G P : x| C X} U X has 
the finite intersection property as well. By the compactness of #, we then have 
xt nplxe* X ± 0) fr°m which x G (fixe* -^01- a 
This lemma means that O in every tight and compact frame $ = (W, R, P) 
distributes over the intersection of any downward directed subset of P. And as 
we already know (see Exercise 8.2), the necessity operator □ distributes in every 
frame over the intersection of an arbitrary family {Xi : i G 1} of subsets of W, 
that isU(\eIXi = r\ieiUXi. 

SAHLQVIST’S THEOREM 
351 
Lemma 10.28. (Intersection) Suppose (p(p,..., q,..., r) is a positive formula 
and $ = (W, R, P) G V*. Then for every Y CW and allU,... ,V G P, 
f){<p(U,...,X,...,V): YCXeP} = 
<p(U,...,f){XeP: Y CX},...,V). (10.7) 
Proof If $ is a Kripke frame then the variable X ranges over all subsets of W 
containing Y and so, by the monotonicity of </?, both sides of (10.7) are simply 
So suppose $ is descriptive and prove our claim by induction on the 
construction of tp. The basis of induction is trivial. Let ip = if) V x and suppose that a 
point x does not belong to the right side of (10.7), i.e., 
xt *(...,[) {XeP: YCX},...)UX(...,f]{XeP: YCX},...). 
By the induction hypothesis, we have x ^ • •, X,...) :Y C X G P} and 
x D(X(. • • , X,...) : Y C X G P}. So there are sets X',X" G P such that 
fci'n X", x g V>(..., X',...) and x £ x(- • • > X",...). By the monotonicity 
of and X) we then have x ^ t/»(..., X' fl X",.-..) and x x(- • • > X' fl X",...), 
whence x ^ f){('0 V x)(- • •, X,...) : Y C X G P}. Thus, the set in the left-hand 
side of (10.7) is a subset of that in the right-hand side. To prove the converse 
inclusion, we observe first that 
PlWVxX..YCXeP}2 
P|(V>(..YCXeP}Up|{x(---,*,---): Y C X G P}, 
as follows from the set-theoretic inclusion 
flCXiUXjDflXiUDX, 
iel iel i€l 
and then we use the induction hypothesis. 
The case (p = ^ Ax is considered analogously. Let (p = Uty. As was mentioned 
above, □ distributes over intersections. So we obtain 
P|{Dtf YCX eP} = af){i>(...,X,...) : Y C X € P} 
and then use the induction hypothesis. 
The case (p = O%[) is treated similarly, but this time we use Esakia’s lemma 
and the fact that {t/>(..., X,...) : Y C X G P} either contains 0, and so both 
sides of (10.7) become 0, or is downward directed. (Indeed, if X',X" G P, Y C 
X' and y C X" then X' fl X" G P, y C X' fl X" and, by monotonicity, 
^(...,x' n X",...) c <0(...,x',...) n t/>(...,X",...).) □ 

352 
KRIPKE COMPLETENESS 
It follows from this lemma and considerations above that, given a modal 
formula ip = 0 —> x with strongly positive 0 and positive we can construct 
a first order formula <j)(x) (in R and =) with one free individual variable x such 
that, for every descriptive or Kripke frame # and every point a in #, (3, a) (= <p 
iff 4>{x) is satisfied in # at a, or in symbols, # |= <l>(x)[a]- We will not, however, 
present this result as a theorem because by purely syntactic manipulations with 
modal and first order formulas we can get a stronger one. 
Notice that using the monotonicity of positive formulas, the equivalence 
(10.4) 	can be generalized to the following one: for every # = (W,R,P), every 
positive Xi(- •. ,p,.. .), * = 1? • • •,n, and every x\,... ,xn G W, 
vxeP(Ycx-+\J iff 
i<n 
V*i€r|{Xi(-YCX&P}. (10.8) 
i<n 
Say that a modal formula 0 is untied if it can be constructed from negative 
formulas and strongly positive ones using only A and O. (We remind the reader 
that negative formulas are built from the negations of variables with the help of 
_L, T, A, V, □ and O. If v(p\,... ,pn) is negative then -i*/(pi,... ,pn) is equivalent 
in K to a positive formula, namely to ^*(->Pi,... ,-pn); see Exercise 3.21.) 
Lemma 10.29 Let 0(pi, • • • ,pn) be an untied formula and # = (W,R,P) a 
frame. Then for every x G W and all X\,..., Xn G P, 
X e i>(xXn) iff3yi,...,yi($A /\TiCXiA f\ Zj e Uj(Xi,... ,Xn)) 
i<n j<m 
where the formula in the right-hand side, effectively constructed from ij.), has only 
one free individual variable x, $ is a conjunction of formulas of the form uRv, 
Ti are suitable R-terms and Vj(jpi,... ,pn) are negative formulas. 
Proof An easy induction on the construction of ^ from negative and strongly 
positive formulas is left to the reader. □ 
We are now in a position to formulate and prove the main result of this 
section. 
Theorem 10.30. (Sahlqvist’s theorem) Suppose that <p is a formula which 
is equivalent in K to a conjunction of formulas of the form □fc('0 —► x)> where 
k > 0, x is positive and $ is constructed from propositional variables and their 
negations, JL and T with the help of A, V, □ and O in such a way that no -0’s 
subformula of the form 0i V 02 or O0i, containing an occurrence of a variable 
without -i, is in the scope of some □. Then one can effectively construct a first 
order formula <p(x) in R and = having x as its only free variable and such that, 
for every descriptive or Kripke frame $ and every point a in $, 
(J, a) |= ip iff $ |= <t>{x)[a}. 

SAHLQVIST’S THEOREM 
353 
Proof Since for (p = ip\ A ... A (pm we have (#, a) |= <p iff (#, a) |= cpi for every 
i G {1,..., ra}, we may begin with finding first order equivalents for <pi and then 
take the conjunction of them. 
To construct a first order equivalent for a formula Uk(%j) —> \) defined in the 
formulation of our theorem, we observe first that one can equivalently reduce 
^ to a disjunction ^ V...V of untied formulas, and hence Uk(ij) —> \) Is 
equivalent in K to Qfc(V>i - x) A... A □fc(^m -► X). So all we need is to find 
a first order equivalent for an arbitrary formula Uk(ip —> \) with untied ^ and 
positive X’ Let pi,.. .pn be all the variables in and x and # = (W,R,P) a 
descriptive or Kripke frame. Then, for any x E W, we have: 
(ff, X) 1= Ofc(t/> - x) iff VXi, ...,XnePxe - x)(Xi, ...,xn) 
iff VXi,Xn G P Vy (xRky —> 
(by Lemma 10.29) iff VXi,..., Xn G P Vy (xRky —► (3yi,..., yi (i? A 
f\Ti C Xi A A 2j € ^(Xi,..., Xn)) —+ 
i<n j<m 
yex(Xi,...,Xn))) 
iffVX1,...,XnePVy,y1,...,y/ (0' A /\ T, C X* A 
i<n 
A ^ i> • • • > Xn) —> y £ • • • > -^n)) 
j<m 
where = xRky A $. 
Let 7Tj(pi,... ,pn) = *'J*(-,Pi> • • •, -«Pn) (recall that z/* is the dual of z/j and 
7Tj is a positive formula). Then, by the laws of classical predicate logic, we can 
continue this chain of equivalences as follows: 
iff Vy,yi,... ,y, (0; - VXlf... ,X„ e P (A Ti C X, - 
i<n 
V 2je7Ti(X1,...,Xn))) 
J <771+1 
(where ^.^(p!,... ,pn) = x(Pi,- ■ ■ ,Pn) and zm+1 = y) 
iff Vy,yi,... ,yi (•&'—* \f zj G TTj(T1}... ,T„)), 
j <771+1 
as follows from (10.8), the intersection lemma and (10.3). The rest is an 
immediate consequence of Lemma 10.25. □ 
The formulas cp described in the formulation of Theorem 10.30 are called 
Sahlqvist formulas. As a consequence of this theorem we obtain our first general 
completeness result for modal logics. 

354 
KRIPKE COMPLETENESS 
Theorem 10.31 Suppose that L is a V-persistent normal modal logic and T 
any set of Sahlqvist formulas. Then the logic L ® T is also V-persistent. Besides, 
if L is elementary then L ® T is elementary as well. 
This result can easily be extended to quasi-normal logics. Let us call a logic 
L e ExtK V-persistent if for every descriptive frame S' with actual world w, 
(S, w) \= L implies (/cff, w) \= L. L is elementary if there is a set $ of first order 
formulas (in R and =) with only one free variable x such that, for every Kripke 
frame S with actual world w, (S, w) h L iff S \= </>{x)[w\ for all 0 G 4>. It should 
be clear that Theorem 10.31 will hold if we replace in it ® by + and regard L 
as a quasi-normal modal logic. 
10.4 	Logics of finite width 
Our second completeness result holds for both normal modal and superintuition- 
istic logics. However, in the modal case it concerns only logics with transitive 
frames, i.e., extensions of K4, and so all frames in this section are assumed to be 
transitive. We will prove it first for modal logics and then use the preservation 
theorem to transfer it to superintuitionistic ones. 
This result can be formulated both syntactically and semantically. Its 
syntactical form states simply that, for every n > 1, all normal extensions of the 
logic K4BWn are Kripke complete. In order to reformulate this semantically, 
we observe that Corollary 3.43 can be generalized to refined frames. Namely, we 
have 
Proposition 10.32 A rooted refined frame S = (W, R, P) validates bwn iff S 
is of width < n. 
Proof (=>) Suppose otherwise. Then S contains an antichain xo,... ,xn. Since 
S is differentiated, there exist disjoint sets Xb,..., Xn G P such that, for every 
i,j € {0,..., n}, Xi G Xj iff i = j. Using the tightness of S, one can show that 
there are sets Yq, ... ,Yn e P such that Xi G 1* and Y* fi Yjj= 0 for every j ^ i. 
Now we put Zi = Xi fl Yi G P and define a valuation on S by taking, for 
every i = 0,..., n, %J(pi) = ZUsing the fact that Zq, ..., Zn are disjoint and 
do not see each other, the reader can readily show that bwn is false under at 
the root of S> which is a contradiction. 
(4=) follows from Corollary 3.43. □ 
Thus, a semantic counterpart of the completeness result formulated above 
may look like this: a modal logic is Kripke complete whenever it is characterized 
by a class of transitive general frames of width < n, for some n > 1. If a logic L 
satisfies this condition and is not characterized by any class of frames of width 
< n then L is said to be of width n. K4BWn is the smallest logic of width n. 
We are going to prove this result in three moves. First we show that every 
finite width logic is characterized by a class of Noetherian frames of finite width. 
Frames of this sort have the finite cover property in the sense that every set of 
points in them has a finite cover. Then, removing some points from these frames, 
we establish that every finite width logic is AHJ-complete, where ATC is the 

LOGICS OF FINITE WIDTH 
355 
class of all atomic transitive frames with the finite cover property. And finally 
we observe that every normal modal logic above K4 is AFC-persistent, which 
together with the preceding statement gives the Kripke completeness of all logics 
of finite width. 
To justify the first move, we require the following generalization of Konig’s 
lemma. Say that a sequence xo,xi,... of points in # = (W, R) is nondescending 
if XiRxj for no i and j such that i> j. 
Lemma 10.33 Suppose a frame $ = (W, R) has no infinite antichains. Then 
every infinite nondescending sequence of distinct points in # contains an infinite 
ascending subsequence. 
Proof Let xo, xi, • ■ ■ be an arbitrary infinite nondescending sequence of distinct 
points in #. Observe first that there must exist some i such that the subsequence 
Xi = {xj : j > i and XiRxj} is infinite. For otherwise, if there is no such 
z, we can inductively define an infinite antichain x^x^,... in # by putting 
io = 0,... ,ifc+i = 1 + max{{zfc} U {i: x< G Xik}}, etc. 
Now we construct by induction an infinite ascending subsequence xio, xix,... 
of xo,Xi, Let xio be the first point in the original sequence with infinite Xi0, 
and if x*n has been already defined in such a way that Xin is infinite, then we let 
Xin+1 be the first point in the (infinite nondescending) sequence Xin with infinite 
xl+1. □ 
Theorem 10.34 Every finitely generated differentiated frame without infinite 
antichains is Noetherian. 
Proof Let £ = {W, R, P) be a finitely generated differentiated frame without 
infinite antichains. Call a point x0 G W deep if there is an infinite ascending 
chain xo,£i,... of distinct points in #. So our goal is to prove that # contains 
no deep points. Suppose otherwise. 
For each x G W, let Ux be the set of points accessible from x which are not 
deep. Call a point x static if Ux = Uy for every deep y G xf. It follows from 
Lemma 10.33 that every infinite ascending chain contains a static point. Indeed, 
otherwise there is a chain xqRxiR. .. for which UXo D UXl D ..., and so we can 
construct a sequence yo, yi, •.. such that y* G UXi — UXi+1. It should be clear that 
the sequence is nondescending and so contains an infinite ascending subsequence, 
contrary to all yi being not deep. 
Let Q = {G\,..., Gn} be a set of P’s generators. We write x ~g y if, for every 
i = 1,... ,n, x G Gi iff y G Gi, and denote by [x]g the set {y G W : x y}. 
For x G W, let Vx = {[y]g : xRy and y is deep}. Say that a deep point x is 
stationary if Vx = Vy for every deep y G x|. Since Vx D Vy whenever xRy and 
each Vx is finite (\VX\ < 2n, to be more exact), every infinite ascending chain in 
# contains a stationary point. 
It follows that J contains a point x which is both static and stationary, 
he., Ux = Uy and Vx = Vy for every deep y G x|. Now, by induction on the 
construction of a set X G P from Gi,... ,Gn using, say, fi, — and | it is not 
hard to show that y G X iff z G X for every deep y, z G x] such that y ~g z. (The 

356 
KRIPKE COMPLETENESS 
only nontrivial case is X = YJ,. Suppose y G wi for some w G Y. If w is not deep 
then z G w[C Yj, since Uy = £/*. And if w is deep then, since Yy = Vz, there is 
a deep v G z| such that w u, from which, by the induction hypothesis, v G Y 
and so again zG Y|.) But this leads to a contradiction. Indeed, x sees infinitely 
many deep points. Hence at least two of them, say y and z, are (/-equivalent and 
so VX G P(y G X <-> z G X), contrary to # being differentiated. □ 
As a consequence of Theorem 10.34 we obtain 
Theorem 10.35 Every differentiated finitely generated frame without infinite 
antichains has the finite cover property and contains no infinite clusters. 
Proof Suppose # is a differentiated finitely generated frame and X a non-empty 
set of its points. By Theorem 10.34, # contains no infinite ascending chains, and 
so every cluster in # is finite and every point in X sees a final point in X or 
is final in X itself. Therefore, any subset of X containing one representative of 
each cluster generated by a final point in X is a cover for X. It is finite because 
it is an antichain. □ 
Each logic L G NExtK4, as we know, is characterized by its finitely generated 
refined frames whose clusters are finite. If L is of finite width then these frames 
turn out to possess one more nice trait: they have the finite cover property. Our 
second move is to prove that atomic frames with the finite cover property and 
without infinite clusters are enough. To this end we will show first that certain 
points in general frames are practically useless and may be safely thrown out. 
Let # = (W,R,P) be an arbitrary frame. A point x G W is said to be 
eliminable in # if it has a proper successor in every set X G P containing x. 
If # has the finite cover property then each eliminable point in #, if any, has a 
noneliminable successor in every set in P it belongs to. But actually, this fact 
holds for every descriptive frame 
Theorem 10.36 Suppose that # = (W, i?, P) is a descriptive frame and X G P. 
Then the set of final points in X is non-empty and forms a cover for X. In 
particular, every eliminable point in X has a noneliminable successor in X. 
Proof Suppose otherwise. This means that some x in X sees no final point in 
X. Let U be a maximal chain in X starting from x (i.e., for every chain Y C X 
beginning with x, U C Y implies U = Y); its existence can be readily proved 
with the help of Zorn’s lemma. Of course, U has no maximal point. 
Now consider the family X of all sets Y G P such that Y contains all the 
points in U above some y G U\ more exactly, we let 
X = {Y G P : 3y G U n U C Y}. 
Clearly, X is not empty, since X G Af, and has the finite intersection property. 
Hence, there isauGfl^- But then u is a maximal point in U. Indeed, u G X 
and so what we need is to establish that yRu for every y G U. By the tightness 
of it suffices to show that VY G P (y G OY —> u G Y), which is quite clear, 
since y G OY implies Y G X. 

LOGICS OF FINITE WIDTH 
357 
Thus we arrive at a contradiction which proves our theorem. □ 
Now, given a frame $ = (W, i?, P) in which each eliminable point x has a 
noneliminable successor in every set X E P containing x, we construct a new 
frame 0 = {V, S', Q) by taking 
V — {x E W : xis noneliminable in #}, 
S = Rnv2, Q = {Xn7: XeP}. 
The fact that Q is closed under the Boolean operations and j follows from the 
equalities (10.9)-(10.11) below which hold for every X, Y E P: 
(X n Y) n v = (X n v) n (Y n v), (10.9) 
(w - X) n v = v - (x n v), (10.10) 
xiRnv = {Xnv)is. (10.11) 
The first two of them are trivial and (10.11) is proved like this. Suppose that 
x G X[Rf\V, i.e., x is a noneliminable point in # having a successor y in X. Let 
z be a noneliminable successor of y in X. Then 2 G X Pi F, x G yi C 4 and so 
xG (In U) |S\ The converse inclusion is obvious. 
It follows from (10.9)-(10.11) that the map X 1—> X fl V, for X e P, is a 
homomorphism of onto 0+. Moreover, if X ^ Y then X fl V ^ Y fl V for 
every X, Y G P. (For if x e X -Y G P then there is a noneliminable point in 
X — Y.) Thus, = 0+. It is easy to see also that 0 is refined, though not 
necessarily compact. Clearly 0 contains no eliminable points. Frames with this 
property are called reduced. As a consequence of Theorem 10.36 we then obtain 
Proposition 10.37 Every logic L E NExtK4 is characterized by the class of its 
finitely generated reduced refined frames. 
Proposition 10.38 Suppose $ — (W, i?, P) is a refined reduced frame with the 
finite cover property and without infinite clusters. Then $ is atomic. 
Proof Let x be an arbitrary point in #. Since $ is reduced, x is a final point 
in some X E P. Using the fact that # is differentiated and C(x) is finite, one 
can construct a set Xo E P which contains x and does not contain points from 
C(x) - {x}. 
Let be all the final points in the set X - C(x). By the same 
argument there is a set Yo £ P such that x E Yq and y\,..., ym ^ Yq. Moreover, 
since x sees none of y\,..., ym, using the tightness of # we can find a set Y E P 
containing yi,..., ym and such that x ^ 
Now consider the set Z — (XC\Xq D Yo) — which clearly belongs to P and 
contains x. Suppose z is a point in Z different from x. Since z is final neither in 
X nor in X — C(x), it must see at least one of yt. But then z 6 Yj, which is a 
contradiction. Therefore, Z = {x}. □ 

358 
KRIPKE COMPLETENESS 
As a consequence of Theorem 10.35 and Propositions 10.32, 10.37 and 10.38 
we obtain 
Theorem 10.39 Every finite width logic is characterized by a class of finitely 
generated refined atomic frames with the finite cover property. 
Remark Taking finitely generated universal frames, we see that in the 
preceding theorem a countable class of at most countable frames is enough. 
Our final move is to show that every logic in NExtK4 is persistent with 
respect to the class of atomic frames having the finite cover property This result 
is a direct consequence of the following lemma and Theorem 9.43. 
Theorem 10.40 Suppose that 0 = (V, S', Q) is an atomic frame with the finite 
cover property validating a canonical formula a(5, 2), _L). Then validates 
0(^,2), _L) as well 
Proof Suppose otherwise. Then there exists a cofinal subreduction of ft0 to 
5 = (W,R) satisfying (CDC) for 2). For every point x E W we fix a finite cover 
Vx for f~1(x) in 0. Since 0 is atomic, Vx E Q for all x E W. 
Now we define a new partial map g from V onto W by putting 
x if y G Vx 
undefined otherwise. 
In other words, g is obtained from / by restricting dom/ to the set [jxeW Vx. It 
is easy to check that g is a cofinal subreduction of 0 to 5 satisfying (CDC) for 
2). Therefore, 0 a(5,S, J-), which is a contradiction. □ 
Since every normal extension of K4 is axiomatized by canonical formulas, we 
immediately derive 
Theorem 10.41 Every logic in NExtK4 is persistent with respect to the class 
of atomic frames having the finite cover property. 
Putting together Theorems 10.39 and 10.41, we finally obtain the desirable 
completeness result. 
Theorem 10.42. (Fine’s theorem) Every finite width logic is Kripke 
complete. More precisely, every modal logic of width n is characterized by a class of 
Noetherian Kripke frames of width < n. 
In fact, using the remark above, we can derive even a somewhat stronger 
theorem. 
Theorem 10.43 If a logic L E NExtK4 is characterized by a class of frames 
without infinite antichains then it is also characterized by an at most countable 
class of at most countable Kripke frames. * 
It is worth noting that unlike Theorem 10.31, Fine’s theorem speaks only 
about Kripke completeness. Finite width logics are not necessarily canonical and 

LOGICS OF FINITE WIDTH 
359 
characterized by elementary classes of frames, witness the logic GL.3 (whether 
in finite or infinite language), for which the proofs of Theorems 6.5 and 6.7 
go through. If the language is infinite then the proof of Theorem 6.6 shows that 
GL.3 is not strongly complete either. It is of interest, however, that the following 
theorem holds. 
Theorem 10.44 Every finite width logic L in a finite language is strongly Kripke 
complete. 
Proof Suppose that the language of L has m < uj variables and t is an 
L-consistent tableau. Then t is realized at a point a in the canonical model 
OTlN = (#L(wO,9JL(m)). Let 
V — {a} U {x G Wl(tu) : ai?L(ra)x and x is noneliminable in 3x(w0}, 
S = RL(m) H V2, and it(p) - ®L(m)(p) n V. We claim that <5 - (V,S) is a 
(Kripke) frame for L and t is realized at a in 91 — {(5,il). 
First, by induction on the construction of (p we show that (9Jt, x) |= p iff 
(91, x) |= p, for every x G V. The basis of induction and the cases of p = ip O X 
for Q G {—>,A,V} are trivial. So suppose p = Dip. If (9Jt,x) ft then there 
is a noneliminable point y G x] such that (9Jt, y) ft ip, whence y G V and, by 
the induction hypothesis, (91, y) ft ip, from which (91, x) ft Dip. The converse 
implication is evident. It follows in particular that t is realized at a in 91. 
So if a is noneliminable then we are done. Let a be eliminable. Then the 
cluster C(a) is simple in (5 (see Exercise 10.18). Suppose that (5 ft p for some 
p G L. By Theorem 9.43, there is a(3r,®,±) such that 0 ft a($, 2), _L) and 
f) ft p whenever ft a($, 2), _L), for every frame fy By Theorem 9.39, there is 
a cofinal subreduction / of (5 to ^ satisfying (CDC) for 2). Since (5 has the finite 
cover property, we may assume f~1{x) to be a finite antichain, for every x in 
# = {W, R). Let b be the root of #. Since C(a) is a simple cluster, C(b) is simple 
as well. For otherwise a(3r, 2), _L) and so p are refuted in the generated subframe 
(S' of (5 consisting of only noneliminable points, which is a contradiction. So we 
may assume that /_1(6) = {a}. Let a C f~1(W) be a finite antichain such that 
f~1(W - {6}) C a|. Since all points in a are noneliminable and a C a|, there 
must be a noneliminable point c G a\ such that a C c|. But then we can extend 
/ by putting /(c) = b and get again a cofinal subreduction of (5 to $ satisfying 
(CDC) for 2). This means that a(3r,2), _L) and so p are refuted at c in (S', which 
is a contradiction. Thus, (5 |= L. □ 
In the intuitionistic case the definition of logic of width n remains the same 
as in the modal one. It is not hard to see that a superintuitionistic logic L is 
of width n iff bwn G L and bwn+\ $ L\ so BWn = Int + bwn is the minimal 
si-logic of width n. 
If L is a si-logic of width n then, as follows from Theorems 9.68 and 9.70, both 
rL and crL are also of width n. Moreover, by Theorem 9.56, if M G NExtS4 is 
of width n then its si-fragment pM is of the same width. Thus we obtain the 
following intuitionistic variant of Fine’s theorem: 

360 
KRIPKE COMPLETENESS 
Theorem 10.45 Every superintuitionistic logic of width n is characterized by a 
class of Noetherian Kripke frames of width < n. 
Of course, the intuitionistic counterparts of Theorems 10.44 and 10.43 also 
hold. 
10.5 	The degree of Kripke incompleteness of logics in NExtK 
So far, when dealing with Kripke completeness, we were interested only in 
whether a given logic is complete or not. Yet, there is another natural question 
concerning this property. If a logic L (in NExtK or Extint) is Kripke incomplete 
then at least two distinct logics have the same Kripke frames, namely L and the 
logic characterized by the class of Kripke frames for L. The problem is to 
determine how many distinct logics may share the same class of Kripke frames. In 
this section we obtain a complete solution to this problem for logics in NExtK. 
It is based on the lattice-theoretic notion of splitting. 
Say that a logic L\ in a complete lattice £ of logics (e.g. NExtK) splits £ if 
there is L<i in £ such that, for every L in £, either L C Zq or L D L<i (but not 
both, i.e., 1,2 % Zq). Clearly, the logic Z^, if it exists, is determined uniquely by 
Zq; we call it the splitting of £ by L\ and denote it by £/Zq. Of course, L\ is 
also uniquely determined by Z^; (Zq,!^) is called a splitting pair in £. 
In fact splittings were already introduced in Sections 4.3 and 9.4 under the 
name of prime logics. Indeed, we have the following: 
Proposition 10.46 A logic L2 is a splitting of £ iff L2 is prime in £. 
Proof For definiteness we assume £ to be a complete lattice of normal modal 
logics. 
(=>) Suppose Z/2 = 0*6/ L i and Z/2 = £/Zq. For each z G Z, we have either 
Li C L\ or Li O Z^. If Li D L2 for some z, then we are done, because in this case 
Li = Z/2- Otherwise, Li C Zq for all z, whence L2 C Zq, which is a contradiction. 
(<=) Put Zq = ®{Z/ G £ : V 2 Z/2} and show that (Zq,Z/2) is a splitting 
pair. Take any L in £. If L 2 L2 then, by the definition, Z C Li. So suppose 
L\ D L D Z/2. Then L2 = L2 fl ®{Z/ G £ : L' fb Z^}. By Theorem 4.6, we have 
Z/2 = ®{Z/2HZ/ : V 2 Z/2}, from which L2 = Z^nZ/ for some V fb Z/2, because 
Z/2 is prime. But then l2 c l>, which is again a contradiction. □ 
Example 10.47 (1) D = K ® OT = NExtK/Log». Indeed, if • is a frame for 
L G NExtK then L C Log^. Otherwise (by the generation and disjoint union 
theorems, see the proof of Makinson’s theorem) OT G Z and so D C Z. 
(2) 	By Proposition 10.46 and Theorem 9.46, a logic is a splitting of NExtK4 
or Extint iff it can be represented in the form K4 0 _L) or Int + /^(ff, _L), 
respectively. 
If each logic in a family {Li : z G 1} C £ splits the lattice £ then the logic 
L — ®iei £/Li (L = ^2ieI £/Li in the intuitionistic case) is called a unio%- 
splitting of £ and denoted by L = £/{Z/* : z G Z}. In this case for every V in £ 
we clearly have V 2 L iff V % Li for all z G Z. 

THE DEGREE OF KRIPKE INCOMPLETENESS 
361 
Example 10.48 It is easy to check that S4 = K4 ® <*(•) = K4 ® «**(•, _L) ® 
• ,_L) = NExtK4/{Log»,Log • }. By Example 10.47, the frame logics and 
only they are union-splittings of NExtK4 and Extint. 
The connection of splittings with finite rooted frames revealed by the 
examples above is not mere chance. 
Theorem 10.49 Suppose a logic Lo G NExtK is finitely approximable and L 
splits NExtLo. Then there is a finite rooted frame # such that L = Log#. 
Proof Let C be the class of all finite rooted frames for Lo- Since Lo is finitely 
approximable, we have Lo = p|{Log# : # G C} C L. And since NExtLo/L % L, 
there is # G C such that Log# C L. As will be shown in Section 12.1, all extensions 
of a tabular logic are also tabular. Therefore, L can be represented as P|”=1 Log#*, 
for some finite rooted #*, and so, by the same argument, there is i such that 
L = Log#*. □ 
To simplify our notation and terminology, we will write Lo/# instead of 
NExtLo/Log# and say that # splits NExtLo and Lo/# is the splitting of NExtLo 
by #. The union-splitting NExtLo/{Log# : # G J7} will be denoted by L§jT. 
The semantic meaning of (union-) splittings is quite clear: 
Proposition 10.50 Lq/J7 is the smallest normal extension o/Lo without frames 
in T. 
This observation and the next theorem show why splittings may be of great 
importance for solving our problem. Say that a Kripke complete (finitely 
approximable) logic L is strictly Kripke complete (respectively, strictly finitely 
approximable) in a lattice of logics £ if no other logic in £ has the same Kripke (finite) 
frames as L. 
Theorem 10.51 Every Kripke complete (finitely approximable) union-splitting 
L = Lq/J7 is strictly Kripke complete (or, respectively, strictly finitely 
approximable) in NExtLo- 
Proof Let V be a logic in NExtLo with the same Kripke (finite) frames as L. 
Then obviously V C L. On the other hand, the frames in T do not validate V 
and so, by Proposition 10.50, L C V. □ 
The following property of splittings will be useful in Section 12.2. 
Theorem 10.52 Suppose that L = Lq/J7 for some class T of finite rooted 
frames. Then all immediate predecessors of L in NExtLo are contained in the 
set {L H Log# : # G J7}. Moreover, z/# G T does not validate Log(5 for any 
® G T — {#}, then L fl Log# is an immediate predecessor of L in NExtLo- 
Proof If V is an immediate predecessor of L in NExtLo then, by 
Proposition 10.50, # f= L' for some # G T. Therefore, V C L D Log# C L and so 
L' = L D Log#. 

362 
KRIPKE COMPLETENESS 
Suppose now that # ^ Log® for any ® e T — {#}, and L fi Log# C V C L. 
Then, since L = Lo/F, we have V C Log#' for some #' e J7. Hence #' = # and 
U — L n Log#. Q 
As we saw above, any finite rooted frame splits NExtK4. Now let us find out 
which frames may split NExtK. To this end we need some more frame-based 
formulas. Suppose # = (W,R) is a finite frame with root r. Let 
<$(#) = /\{px -+ Opy ■ xRy} A /\{px -» ~'Op2/ : -ixRy} A 
f\{Px -*-‘Py- x^yjA \j{px : xeW) 
and, for every m < cj, 6m($) = AiLo D*<$(#). The meaning of the formulas <5m(#) 
is that a frame ® satisfies the set {<5m($),pr : m < u>) at a point x iff there is a 
generated subframe & of 3 reducible to #. Indeed, the implication (4=) is clear 
and to prove (=>) it suffices to notice that the map / from & to # defined by 
f(v) = y iff v |= py is a reduction. 
Say that a frame # is cycle free if x € x^ for no x in #, i.e., the diagram of 
# contains no cycles, including reflexive points. Clearly, a finite frame # is cycle 
free iff # \= Qn-L for some n < cu. 
Theorem 10.53 A finite rooted frame # splits NExtK iff$ is cycle free. 
Proof (=>) Suppose that # splits the lattice NExtK. By Corollary 3.29, we 
have K = p|{Log(5 : 3 is a finite rooted cycle free frame}. Then there is a finite 
rooted cycle free 3 such that Log® C Log# and so # |= Dn_L for some n < uj. 
(<=) Let # |= DnJ_. We show that (Log#, K ® DnJ_ A <5n-1(#) —> ~^pr) is a 
splitting pair. Denote it for brevity by (Li,!^). Take any logic L e NExtK and 
a frame ® characterizing it. Clearly # contains no chains of length > n. Then 
we have L2 % L iff Dn_L A <5n-1(#) A pr is satisfied in ® at some point x iff the 
subframe ®' of ® generated by x is reducible to #. Thus we have either L2 C L 
or # |= L and so L C L\. □ 
Theorem 10.54 Every union-splitting of NExtK is finitely approximable. 
Proof We prove the finite approximability of L = K/F, T a class of finite 
rooted cycle free frames, using a variant of filtration. 
Suppose <p(pi,... ,pn) ^ L. We are going to filtrate the canonical model 
2ft = (#,23) for L in the language with the variables pi,...,pn- To select a 
suitable “filter”, let us first consider points in 2ft at which Dm_L is true and 
□m_i_L is false for some m <u. We call them points of type m (having in mind 
that the maximal ascending chain starting from such a point is of length m). 
The key observation in the proof is 
Lemma 10.55 For every m > 1, there are finitely many points of type m in, 2ft. 
Proof The proof proceeds by induction on m. Clearly, 2ft contains < 2n points 
of type 1 (= dead ends); for otherwise 2ft would not be differentiated. And if 

THE DEGREE OF KRIPKE INCOMPLETENESS 
363 
I2 
ol 
t 
i 
5 oO 0 o 
(a) (b) 
Fig. 10.2. 
there are k points of type < l then, by the same reason, we may have at most 
2n+/e points of type l + 1. □ 
Let A C Sub ip. We consider two cases, (a) All the points in 9Jt, at which of 
all formulas in Sub<^ only those in A are true, are of type < m, for some m <u. 
In this case we put = m. (b) Case (a) does not hold, i.e., for every m there is 
a point x in 9Jt such that, for every ^ e Sub<^, x f= ^ iff ^ G A and x (= OmT; 
then we put m& = 0. Finally, put 
k = max{mA : A C Sub^} and E = Sub(</? A □fc_L). 
We are ready now to filtrate 9Jt, a part of it to be more exact. Namely, we divide 
# = (W, R) into two parts: W\ containing all the points in # of type < k and 
W2 = W — W\. By Lemma 10.55, W\ is finite. For every x,y e W, put x ~ y 
if either x,y e W\ and x = y or x,t/ € W2 and x y. Having defined the 
equivalence classes [x] = {y G W : x ~ y} for x G W, we can construct the 
corresponding finest filtration 01 = (0,il) of DJI as was done in Section 5.3 (in 
fact we filtrate only points in W2 and leave those in W\ untouched) and prove 
that, for every ^ e E, (9Jl,x) (= ^ iff (01, [x]) (= V^ Thus we have a finite model 
01 refuting ip. 
It follows also that a point [x] in 01 is of type m < k iff x has type m in 971. 
Moreover, it turns out that 01 contains no [x] of type l > k. Indeed, otherwise 
x ^ Dk± and so Case (a) does not hold for A — {'ip e Sub<^ : x \= /ip}. 
This means that for every m < uj there is y £ [x] such that y |= OmT and so 
arbitrary long chains (of not necessarily distinct points) start from [x], contrary 
to [x] being of type L 
Thus 0 contains two parts: the upper part consisting of points of type < fc, 
which is clearly the generated subframe {Wi,R \ Wi) of #, and the lower one 
consisting of points without types, i.e., involved in some cycles. It follows that 
® |= L. For otherwise, according to the proof of Theorem 10.53, we have 0 ^ 
□n_L A ^n_1(3r/) —► ~^pr for some £ T (r being the root of $') and n = d(3r/)? 
which means that the subframe 0' of 0 generated by some x is reducible to 
Sr/. But then either 0' is a generated subframe of #, contrary to # |= L, or 0' 
contains a cycle, contrary to being cycle free. □ 
It is to be noted that Theorem 10.54 does not hold for NExtK4. 

364 
KRIPKE COMPLETENESS 
nontransitive 
\ transitive! 
Fig. 10.3. 
Example 10.56 Let us consider the logic L = K4 0 &#(#, _L) and the formula 
a(5, J_), where $ is the frame depicted in Fig. 10.2 (a). The frame 0 shown 
in Fig. 10.2 (b) separates a(#, J_) from L. Indeed, $ is a cofinal subframe of 
0 which, by Theorem 9.39, gives 0 ^ &(#, _L). To show that 0 (= J_), 
suppose / is a cofinal subreduction of 0 to #. Then, by (Rl), /-1(1) contains 
only one point, say x; by (R2), /-1(0) also contains only one point, namely, the 
root of 0. So the whole infinite set of points between x and the root is outside 
of dom/, which means that / does not satisfy (CDC) for {{1}}. 
On the other hand, suppose 9) is a finite rooted frame refuting a($, J_) at 
its root. Then all final points in 9) are reflexive. Besides, 9) must contain a 
nondegenerate cluster C having an irreflexive immediate successor x. So by mapping 
C to 0, x to 1 and all the other points above C to 2 we obtain a reduction of the 
subframe of 9) generated by C to #, from which 9) L. 
It follows that L is not finitely approximable. Moreover, the very same 
argument shows that K4.3 0 0^(5, J-) is not finitely approximable either. 
We are in a position now to prove the main result of this section. Say that 
a logic L € £ has degree of Kripke incompleteness x in £ if exactly x distinct 
logics in £ have the same Kripke frames as L. Strictly complete logics are those 
having degree of incompleteness 1. By Theorems 10.54 and 10.51, every 
unionsplitting is strictly Kripke complete. All the other logics in NExtK turn out to 
have degree of incompleteness 2**°. Before proving this in general it is useful to 
consider two special cases, namely the logics Log# and Logo (why are they not 
union-splittings?). 
Example 10.57 We are going to construct a continual family of logics Lj, for 
1 C oj — {0}, the only rooted Kripke frame for which is •. Define Lj to be the 
logic of the frame #/ = (Wj, Rj, Rj) with the underlying Kripke frame shown in 
Fig. 10.3, where the subframes in dashed boxes are transitive, ao sees all points e» 
and e'-, for i < u, j G /, e[ G Wi iff i G /, and Pj consists of the sets of the form 
XU Y such that X is a finite or cofinite subset of {a_i, c, e», e': : i < uj,j 6 7} 
and Y is either a finite subset of {a* : i < a;} or is of the form {6} U Y\ where 
Y' is a cofinite subset of {a* : i < uj} (check that Pj is closed under —, n and |). 

THE DEGREE OF KRIPKE INCOMPLETENESS 
365 
Observe that all points in #/ save b are characterized by variable free formulas, 
for instance: 
Oi— i — □ J_, ctQ — ODJ_, 
= Octi A -«02ai, 7 = O2a0 A -<Oa0, 
€0 = O7, ci+i = Otj A -'02ei, e'+1 = Oej A -.0+ei+i 
(oti is true only at a*, 7 at c, e* at e*, e' at e'). It follows in particular that #/ 
is O-generated. Let i e I — J. Then -<e' e Lj — Lj and so there is a continuum 
of distinct Lj. 
Since • is a generated subframe of for every J, we have • (= Lj. We show 
now that if J is a rooted Kripke frame for Lj then J is •. Suppose otherwise. 
Then root u of $ sees at least one point. Since 
ot—\ Vao V Oao V O2ao V O3ao £ Lj, 
we have u (= ao V Oao V O2ao V O3ao and so there is a point in $ at which ao is 
true. Using the fact that ao —► 02j e Lj, we can find a point x in $ such that 
x |= 7. Now observe that 
7 -► □(□o(n0p -► p) -► p) £ Lj, 
where Do<p — □ (Oao —» <p). (Here we use the fact that each X £ Pj contains 
some a*, for i > 0, whenever b £ X.) So x (= □ (□o(DoP —+ p) —* p) for any 
valuation in #. By the definition of 7, there is y £ x] such that y (= Oao and 
also y |= ^(noP -* p) p. Define a valuation 93 in # by taking 93(p) — y]. 
Then clearly y (= noC^oP —* p), from which y (= p and so y £ y|. Now define 
another valuation 93' so that 93'(p) = y\ — {y}. Since y is reflexive, we again have 
y |= □o(DoP —> p), whence y (= p, which is a contradiction. 
Thus • is the only rooted Kripke frame for Lj and Log# has degree of Kripke 
incompleteness 2**° in NExtK. 
Example 10,58 To prove that Logo also has degree of Kripke incompleteness 
2K°, we take the logics L\ of the frames $'j = (Wj^R^Pj) in which R'j — 
Ri U {(a_i,a_i)}, i.e., the dead end in Fig. 10.3 is replaced by a reflexive point. 
This replacement makes it impossible to use variable free formulas. We overcome 
this obstacle with the help of the formulas 
6 6 6 6 
O0 	= (O A°V-A D<«) v (O A D<_,9 A " A 
i=0 i=0 i=0 i=Q 
ai+1 = Oa» A -i02ai, 7 = ^2ao A -iOao> 
€o = 07, ci+i = Oct A -.O2€i, e-+1 = Oti A -.O+Cj+i, 

366 
KRIPKE COMPLETENESS 
nontransitive 
Xi 
xl 
/v.fc 1 /y.fc 
X J Xj 
Xl 
X2 
sy. ^v» 1 nf. 1 
xn xi X2 
xi 
n 
X1 
x2 
0— 
-►0 • • 
• 0 ►O 
. • • . 
• • 
■ 
(a) (b) 
Fig. 10.4. 
4 4 
s = -1 yy □ iq a -i yy 
2=0 2=0 
and by observing that /\i=o ^ £/■ The f°rmulas above characterize 
points in 3/ in the sense that if, under some valuation, <5 is true somewhere in 
3/ then a*, 7, e* and e' are true only at the points a*, c, e*, e', respectively; a_i 
is characterized by -><5. It follows that 
6 —► 7 V O7 V 027 V 037 £ L/, 7 —» □(□o(DoP —* p) —* p) £ £/. 
Since -<e' £ Z/j - Z/7, for j £ I - J, there is a continuum of Z/7. 
Let us show that o is the only rooted Kripke frame for L7. Suppose otherwise, 
i.e., there is a rooted Kripke frame 3 for I7 different from o. Clearly 3/ •, 
because OT £ L\. Therefore, 3 contains a root, say u, and some other point 
besides. Putting 2J(q) = {u}, we have u (= <5 and so there is a point x in 3 
such that x (= □ (□0(n<)P —> p) —> p) under any valuation for p. The rest of the 
argument is the same as in Example 10.57. 
Theorem 10,59• (Blok’s theorem) Suppose L is a normal modal logic. If 
L — ForMC or L is a union-splitting in NExtK then L is strictly Kripke 
complete. Otherwise L has degree of Kripke incompleteness 2**° in NExtK. 
Proof Suppose that L is not a union-splitting and V is the greatest 
unionsplitting (the sum of all union-splittings) contained in L. By Theorem 10.54, 
V is finitely approximable and, since V ^ L, there is a finite rooted frame 
3 = (W, i?) validating V and refuting some ip £ L. Clearly, 3 can be chosen to 
be minimal in the sense that its every proper generated subframe is a frame for 
L. It should be also clear that 3 is not cycle free (for otherwise V would not 
be the greatest union-splitting contained in L). Let X1RX2R... RxnRx\ be the 
shortest cycle in 3 and k = md(ip) -f 1. 
We construct a new frame 3r by extending the cycle xi,..., xn, x\ as is shown 
in Fig. 10.4 ((a) for n = 1 and (b) for n > 1). More precisely, we add to 3 copies 
xj,... , x-2 of x^ for each i £ {1,... ,n}, organize them into the nontransitive 
cycle shown in Fig. 10.4 and draw an arrow from x\ to y £ W - {xi,... ,Xn} 
iff XiRy. Denote the resulting frame by 3r = (Wf,Rf) and let x' = x£. By the 
construction, 3 is a reduct of 3'- It follows from Proposition 3.2 that for all 
models DJI = (3,2J) and DJlf — (3',20 such that 

THE DEGREE OF KRIPKE INCOMPLETENESS 
367 
Fig. 10.5. 
9J'(p) = 9j(p) U {x{ : Xi € 9J(p), j < fc}, p G Vary), 
and for every x eW, xp e Sub<^, (9Jt,x) |= xp iff (9Jt',x) |= xp. In particular, we 
can hook some other model on x', and points in W will not feel its presence by 
means of ip's subformulas. 
The frame to be hooked on xf is similar to those in Examples 10.57 and 10.58. 
It depends on whether • |= L or o |= L. We consider only the former alternative 
leaving the latter to the reader as an exercise. 
Fix some m > \W'\. For each I Co; — {0}, let #/ = (Wi,Rj,Pj) be the 
frame whose diagram is shown in Fig. 10.5 (do sees the root of all points e* 
and e'j, for i < lj, j G /, and is seen from x'; the subframes in dashed boxes are 
transitive, e\ 6 Wj iff i G I) and Pj consists of sets of the form XUY such that 
X is a finite or cofinite subset of Wj — {&, a* : i < lj} and Y is either a finite 
subset of {(li : i < u} or is of the form {b} U Yf, where Yf is a cofinite subset 
of {di : i < lj}. It is not hard to see that the points a*, c, e* and e' in #/ are 
characterized by the following variable free formulas: 
<*o = 0(<5m A 0(<5m_i A ... A O<5o) • • •) A -»02(<5m A 0(<5m_i A ... A O<5o) • • •)> 
OLi+1 = Ooti A -*02Q!i, 7 = O2a0 A --Oao, 
€0 = <>7, e*+i = Od A ->02ej, e'+1 = Oa A ->0+ei+i, 
where 
S0 — ODJ_, 6\ = O<5o A -i6oj ^2 = 0<5i A —«6i A -'O~*"6o> 
Sk+i — 0<5fc A -i6fc A -«0+^_i A ... A -»0+6o* 
(Here we use the fact that m > |W'|.) Define Lj as the logic of all frames for L 
and #/. Since -»(e- A Om+6-»<p) e Lj - Lj for i e I - J (<p is refuted at the root 
of #'), the cardinality of the family {Lj : I Clj — {0}} is that of the continuum. 
Let us show now that Lj shares the same Kripke frames with L. Clearly, 
Li C L and so we must prove that every Kripke frame for Lj validates L. 
Suppose otherwise. Then we have a rooted Kripke frame (5 such that (5 \= Lj 
but (5 \/= 4*1 for some xp G L. Since xp is in L, it is valid in all frames for L, 

368 
KRIPKE COMPLETENESS 
in particular, • |= And since ^ L/, i/j is refuted in #/. Moreover, by the 
construction of £j, it is refuted at a point from which the root of can be 
reached by a number of steps. Therefore, the following formulas are valid in #/ 
and so belong to Lj and are valid in (5: 
i 
-> V<>*7, 
i=0 
(10.12) 
i 
-> A D*(7 - D(Do(aoP -> p) -> p)), (10.13) 
2=0 
where the variable p does not occur in ?/> and l is a sufficiently big number so that 
any point in #/ is accessible by < l steps from every point in the selected cycle 
and every point at which ^ may be false, and as before Dqx = □ (Oao —> x)- 
According to (10.12), (5 contains a point at which 7 is true. By the 
construction of 7, this point has a successor at which, by (10.13), □0(DoP —■> p) —■> p and 
Oao are true. Thus, we find ourselves in exactly the same contradictory situation 
as in Example 10.57, which proves that (= L. □ 
This construction can be used to obtain one more important result. 
Theorem 10.60 Every union-splitting "K/J7 has x < N0 immediate 
predecessors in NExtK, where x is the number of frames in T which are not reducts 
of generated subframes of other frames in J7. Every consistent logic different 
from union-splittings has 2**° immediate predecessors in NExtK. (ForMC has 
2 immediate predecessors in NExtK.) 
Proof The former claim follows from Theorem 10.52. As to the latter, we 
demonstrate the idea of the proof assuming that L C Log# and L is finitely 
axiomatizable over Lj constructed in the proof of the preceding theorem (which 
in fact is always the case). The general case is left to the reader. 
By Zorn’s lemma, NExtLj contains an immediate predecessor L'j of L. 
Besides, Lj 0 Lj = L whenever J ^ J. Indeed, 
Li 0 LJ = (L n LogS/) ® (L fl LogSj) = L fl (Log® LogSj) 
and if i G I — J then, for every x £ L and a sufficiently big Z, 
1 
-1 V X € Logff/, ->e' € LogSj, 
k=0 
from which x £ Log0 Logand so L C Log$1 0 Log'Sj. It follows that 
Lj ^ Lj whenever I ^ J. * □ 
It is worth noting that tabular logics, proper extensions of D and extensions 
of K4 are not union-splittings in NExtK. 

EXERCISES AND OPEN PROBLEMS 
369 
10.6 	Exercises and open problems 
Exercise 10.1 Show that canonicity is preserved under sums of logics. 
Exercise 10.2 Show that canonicity is preserved under p and r. 
Exercise 10.3 Show that Kripke completeness is not preserved under sums. 
(Hint: see Section 6.5.) 
Exercise 10.4 Show that S4.1 is not 7£-persistent. (Hint: consider the general 
frame associated with the model ((a;, <) ,93), where 93(pi) — {n : i < n}.) 
Exercise 10.5 Describe the ultrafilter extensions of the frames (u;, >), (u;, <), 
(Z,<), (Q, <). 
Exercise 10.6 Show that for a Kripke frame #, $ is a reduct of some ultrapower 
of y. 
Exercise 10.7 Show that, for every i e /, Si is a generated subframe of the 
ultrafilter extension of ^2ieIdi- 
Exercise 10.8 Prove that the logics L = K©{Dp —► p, □ (□p —► Dq) V □ (□# —> 
□p), Op A D(p —> Dp) —► p, DOp —► ODp} and Triv = K ® Dp +-> p are distinct, 
but their classes of Kripke frames are defined by the same first order condition 
VxVp [xRy <-> x — p), with respect to which Triv is complete. Therefore, L is 
elementary, though neither Kripke complete nor D-persistent. 
Exercise 10.9 Show that the interval between the logics of the preceding 
exercise contains infinitely many logics. 
Exercise 10.10 Let <p = OD(p V q) —► 0(Dp V Dp) and 
cj) = VxVp(xRp —► 3z(xRz A Vu(zRu —► yRu) A 'ivNv{zRu A zRv —+ u — v))). 
Prove that 
(i) 5? |= </> implies £ |= <p; 
(ii) <p and (j) are equivalent on the class of at most countable Kripke frames; 
(iii) <p and (j) are equivalent on the class of descriptive frames; 
(iv) <p is not first order definable. 
Exercise 10.11 Give a complete proof of the Fine-van Benthem theorem. (Hint: 
Let # be an arbitrary Kripke frame for L and u an ultrafilter over W. Define 
as the union of 4> (see the proof of Theorem 10.19) and all formulas of the form 
Px(x), for X e u (x is a fixed individual variable), 
Vp (xK*y -> (Pw-x(y) <-> ~^Px(y))), 
Vp (xRny -► (Pxny(y) Px(y) A Py(p))), 
Vp (xRny -► (Pxi(y) <-> (pRz A Px(z)))). 
Check that has a model, say, a frame £* e C, define for #* the set as in the 
proof of Theorem 10.19, take a frame in which <E>" is satisfied at a point a and 
then show that the subframe of generated by a is reducible to the subframe 
of £ generated by u.) 

370 
KRIPKE COMPLETENESS 
Exercise 10.12 Prove the following variant of Sahlqvist’s theorem. Let p be 
a formula constructed from variables, their negations, T and J_ using A, V, □, 
and O in such a way that either (1) no positive occurrence of a variable is in a 
subformula of the form ipA\ or Uip within the scope of some O, or (2) no negative 
occurrence of a variable is in a subformula of the form ^ Ax or within the 
scope of some O. Then one can effectively construct a first order equivalent for 
p. If L is X>-persistent then L 0 p is also X>-persistent, and if L is elementary 
then so is L ® p. 
Exercise 10.13 Construct a continuum of logics above S4 axiomatizable by 
Sahlqvist formulas. (Hint: consider the formulas 
OL-\— □(“To A “'Sq)j 
cto = □(-!£ A -Ti) A ro A Oa_i, /3o = A -iSi A So), 
ot\ = D(p A -i q) At A Oao A n, (3\ = D(-ip A q) A t A O/?0 A s±, 
OLi+2 = OQ!i+i A OPi A □isi+1 A ri+2, 
A+2 = O0i+1 A oOLi A □-iri+1 A si+2, 
In = OD(p A q) A an, 6n = OD(-np A -rq) A f3n, en = <>^n A OSn.) 
Exercise 10.14 Show that the intersection of Sahlqvist logics is also a Sahlqvist 
logic. 
Exercise 10.15 Show that the McKinsey formula ma is not first order definable 
on the class of finite frames. 
Exercise 10.16 Prove that frame formulas are first order definable on the class 
of irreflexive transitive frames. Show, however, that this is not the case on the 
class of all transitive frames. 
Exercise 10.17 Show that the reduced frame of $Grz(n) contains no proper 
clusters and 3rGL(n) contains no reflexive points. 
Exercise 10.18 Let $ be a refined finitely generated frame of finite width. Show 
that for every point x in #, either all points in C(x) are noneliminable or all points 
in C(x) are eliminable and x is reflexive. 
Exercise 10.19 Suppose L is the decidable union-splitting of NExtLo by a finite 
set of finite frames. Show that in this case we can effectively decide, given a 
formula p, whether L = Lq 0 p. 
Exercise 10.20 Prove that if L = Lq/J7 is finitely axiomatizable then L has 
finitely many immediate predecessors in NExtLo and that otherwise there are 
precisely No immediate predecessors. 
Exercise 10.21 Show that NExtL has an axiomatic basis iff every logic in 
NExtL is a union-splitting of NExtL. 

NOTES 
371 
Exercise 10.22 Suppose a logic Lo £ NExtK4 is finitely approximate. Prove 
that the following conditions are equivalent: 
(i) all union-splittings of NExtLo are finitely approximable; 
(ii) all logics in NExtLo are finitely approximable; 
(iii) all logics in NExtLo are union-splittings of NExtLo; 
(iv) NExtLo has an axiomatic basis. 
Exercise 10.23 Show that for each logic L 6 NExtK, a finite rooted frame # 
for L splits NExtL iff there is m < oj such that, for every (general) frame 0 for 
L, Sm(S) ^Pr is satisfied in 0 only if <5n(3r) A pr is satisfied in 0 for all n < u. 
In this case L/{? = L® (S771^) —■> ->pr. 
Exercise 10.24 Prove that if tram £ L, for some m < uj, then all finite rooted 
frames for L split NExtL. 
Exercise 10.25 Prove that every normal modal logic containing Dn_L is locally 
tabular. 
Exercise 10.26 Show that T is not a splitting of NExtK. 
Exercise 10.27 Prove that o is the only finite rooted frame that splits NExtT. 
Exercise 10.28 Show that the logics Lj constructed in Example 10.57 are 
immediate predecessors of Log® in NExtK. 
Exercise 10.29 Prove that every consistent normal extension of T has degree 
of incompleteness 2**° in NExtT. 
Exercise 10.30 Construct a continuum of Post complete quasi-normal modal 
logics having no Kripke frames at all. 
Problem 10.1 Are canonical logics V-persistent? 
Problem 10.2 Are canonicity and V-persistence preserved under intersections 
of logics? 
Problem 10.3 Does the converse of the Fine-van Benthem theorem hold? 
Problem 10.4 Are finitely axiomatizable Sahlqvist logics in NExtK4 decidable? 
Problem 10.5 What is the degree of Kripke incompleteness of logics in the 
lattices NExtK4, NExtS4, Extint ? 
10.7 	Notes 
In this chapter we considered only results concerning the completeness with 
respect to (infinite, in general) Kripke frames. The completeness with respect to 
finite frames is the subject of the next chapter. 
Theorem 10.3 was proved by Bellissima (1988); later on we shall mention 
some other results from this paper. Theorem 10.5 belongs to Wolter (1993). The 
notion of complex logic was introduced by Goldblatt (1989). 
That every Kripke complete and elementary logic is X>-persistent was first 
proved by Fine (1975b). Theorem 10.19 also appeared first in Fine (1975b), 

372 
KRIPKE COMPLETENESS 
but the proof contained a little gap. The presentation in Section 10.2 follows 
van Benthem (1979b, 1980), where the notion of ultrafilter extension was 
introduced and the proof of Theorem 10.19 was completed (see Exercise 10.11). 
Theorem 10.20 is due to Chagrova (1990), Theorem 10.23 and Exercises 10.4, 
10.10 to Fine (1975b). Exercises 10.6-10.8 and 10.15-10.16 were taken from van 
Benthem (1989, 1978). 
Theorems 10.30 and 10.31 were proved by Sahlqvist (1975). The starting 
point of Sahlqvist’s research was the conjecture of Lemmon and Scott (1977) 
that formulas of the form 
OmiDnipi A ... A OmkDnkpk -+ <p, 
where ip is positive, axiomatize logics that are complete with respect to first 
order conditions which can be “read off’ from the axioms. Independently a 
solution to this conjecture was obtained by Goldblatt (1976b). Other proofs of 
Sahlqvist’s theorem were given by van Benthem (1983) (who formulated it as 
in Exercise 10.12), Sambin and Vaccaro (1989), Kracht (1993a) (who 
characterized also the elementary conditions corresponding to Sahlqvist formulas), and 
Jonsson (1994). Here we followed the proof by Sambin and Vaccaro; Lemma 10.27 
is due to Esakia (1974). The result of Exercise 10.13 was obtained in Chagrov 
and Zakharyaschev (1995b) where a Sahlqvist calculus above S4 which is not 
finitely approximable was also constructed. Above T a calculus of that sort was 
presented by Hughes and Cresswell (1984) (see Exercise 6.11). Exercise 10.14 
is due to Kracht (1995). It is not hard to construct an undecidable polymodal 
Sahlqvist calculus; the transfer theorem of Kracht and Wolter (1997) provides 
us then with an undecidable Sahlqvist calculus in NExtK. 
Venema (1991) extended Sahlqvist’s theorem to logics with non-standard 
inference rules like Gabbay’s (1981) irreflexivity rule. An intuitionistic analog of 
Sahlqvist’s theorem has been proved by Ghilardi and Meloni (1997). We present 
here a somewhat simplified version of their result. Let p, q, r, s denote tuples 
of propositional variables and ^>, x tuples of formulas of the same length as r 
and s, respectively. Suppose ^(p,g,r,s) is an intuitionistic formula in which the 
variables r occur positively and the variables s occur negatively, and which does 
not contain any except for negations and double negations of atoms, in the 
premise of a subformula of the form <p' —► <p". Assume also that ^>(p,g) and 
X(p, q) are formulas such that p occur positively in ^ and negatively in x> while 
q occur negatively in ip and positively in x- Then the logic 
Int + q>(p,q,ip(p,q),x{p,q)) 
is canonical. 
The material of Section 10.4 was taken mainly from Fine (1974c), where the 
method of dropping points from the canonical models was developed in order 
to prove Theorems 10.42 and 10.44. Si-logics of finite width were studied by 
Sobolev (1977a). Some decidability results concerning logics of finite width can 
be found in Chapter 16. As follows from Theorem 10.44, there are strongly 

NOTES 
373 
complete modal logics that are not persistent. But these logics are formulated 
in finite languages. Recently Wolter [1996b] has constructed a logic of that sort 
in the infinite language. 
The question concerning the degree of Kripke incompleteness was raised by 
Fine (1974b) and solved for the lattices NExtK, NExtD and NExtT by Blok 
(1978, 1980b). Similar results concerning the degree of incompleteness with 
respect to neighborhood frames were obtained by Dziobiak [1978] for NExtT and 
NExt(D0Dnp —► □n+1p), and quite recently Chagrova has proved that the 
situation with the degree of neighborhood incompleteness in the whole class NExtK 
is exactly the same as in Blok’s theorem. Theorem 10.60 is also due to Blok 
(1978). 
The notion of splitting was introduced in lattice theory by Whitman (1943). 
McKenzie (1972) considered splitting varieties of lattices. In modal logic 
splittings were used by Blok (1978), Rautenberg (1977, 1979, 1980), Kracht (1990, 
1993c) and Wolter (1993). The result of Exercise 10.19 was proved by Jankov 
(1968a) and Rautenberg (1979), that of Exercise 10.23 by Kracht (1990). 
Exercises 10.21 and 10.22 are due to Wolter (1993) and Exercise 10.24 to 
Rautenberg (1980). Rafter (1994) gave a partial characterization of canonical union- 
splittings. Later he showed that a continuum of union-splittings are canonical 
and as many are not. 

11 
FINITE APPROXIMABILITY 
Let us now go one step down the hierarchy of frame classes and consider a 
stronger form of completeness, viz., completeness with respect to the class of 
finite frames or, in other terms, finite approximability. We have already met with 
one way of proving this property—the filtration method, requiring a special ad 
hoc technique in each particular case. Now we will show a few other methods 
which provide us in fact with general syntactical and semantic sufficient 
conditions of finite approximability. 
11.1 	Uniform logics 
We begin with two results connecting the finite approximability of modal logics 
with the distribution of the operators □ and O over their axioms. The first result 
to be obtained in this section concerns those normal extensions of deontic logic 
D whose additional axioms are uniform in the following sense. 
We say p is a uniform formula of degree 0 if md(p) = 0, i.e., p contains no 
modal operators at all. (p is a uniform formula of degree n + 1 if there are a 
uniform formula 'ipipi, • • • >Pm) of degree 0 and uniform formulas Xi,..., Xm of 
degree n such that p = ^(OiXi? • • •, OmXm) where each O* is either □ or O. 
In other words, a uniform formula of degree n*f 1 is a Boolean combination of 
formulas of the form or Ox such that x is a uniform formula of degree n. 
For example, both the McKinsey and Geach formulas are uniform formulas of 
degree 2, while the Lob and Grzegorczyk ones are not uniform. 
The set of all uniform formulas of degree n is denoted by Un and U, the set 
of uniform formulas, is the union of all Un. 
A remarkable property of uniform formulas of degree n is that their truth- 
values at a point x in a model are completely determined by the truth-values 
of their variables at the points accessible from x by n steps. More exactly, the 
following proposition holds (compare it with Proposition 3.2). 
Proposition 11.1 Suppose p is a uniform formula of degree n and 9DT, 01 are 
models based upon the same frame and such that, for some point x, (9Jt, y) |= p iff 
(91, y) |= p for any y e xtn and any p e Varp. Then (9Jt, x) |= p iff (91, x) |= ip. 
Proof The proof proceeds by induction on n. The basis of induction is trivial, 
and the inductive step is justified by another induction on the construction of 
the uniform formula p of degree n = m -f 1. The basis of the second induction is 
the case when p = Uip or p = Oip with ip € Um. Let p = Dip. Then we haVe: 
(97t, x) |= p iff Vz G xt (9DT, z) |= rp 

UNIFORM LOGICS 
375 
iff Vz € x\ (91, z) \= ip 
iff (91, x) |= cp. 
The only nontrivial transition here (from the first line to the second) is ensured 
by the induction hypothesis of the first induction and the fact that z]mC xtm+1 
for every z e x|. The case cp = Oip is considered analogously. The inductive step 
of the second induction presents no difficulty. □ 
A normal modal logic L is called uniform if it can be represented in the form 
L = D 0 T where T C U. In this section we prove that all uniform logics are 
finitely approximable. 
To construct a finite frame separating a uniform logic L from a formula cp $ L, 
we reduce -«p to a form which is analogous to the full disjunctive normal form 
in Cl (see Exercise 1.2) and gives in fact a description of some finite models for 
-.</?. 
Let Var = {pi,... ,pr} be a finite set of propositional variables. By induction 
on n we define a set NFn of normal forms (in Var) of degree n: NFo is the set 
of all formulas of the form 
-UPl A ... A -ypr, 
where each ->*, for i = 1,..., r, is either blank or and NFn+i is the set of all 
formulas of the form 
9 A —i\09i A ... A —is09s, 
where 9 € NFo, 9i,..., 9S are all the distinct normal forms in NFn and each 
is either blank or NF, the set of normal forms in Var, is the union of all NF* 
for i < uj. 
Theorem 11.2 Every modal formula cp with Var cp C Var and md(cp) < n is 
equivalent in K either to ± or to a disjunction of normal forms in Var of degree 
n. 
Proof We proceed by induction on n. The basis of induction is simply the 
theorem on the full disjunctive normal forms in Cl (see Exercise 1.2). 
Now, suppose md(cp) < fc-f 1. Replacing each □ in cp with —»0—«, we can reduce 
cp to an equivalent formula which is a Boolean combination of propositional 
variables and formulas Oxp with md(ip) < k. By the induction hypothesis and 
the K-equivalences OJ_ _L and O(pVq) OpVOq, each such Oip is equivalent 
either to T or to a disjunction O0i V... VOOm where 9\,..., 0m are normal forms 
of degree k. Therefore, cp is equivalent to a formula of the form 
^(Pi, • • • ,Pr, qu • ■ ■, Qa){OOi/qu • • •. O08/q8}, 
where xp contains no modal operators and 0i,..., 9S are all the distinct formulas 
in NFfc. Finally, reducing ^(pi,.. .pr,(7i, • • • ,qs) to the full disjunctive normal 
form and substituting O0i,..., 098 for #i,..., q8 in it, respectively, we obtain 
an equivalent formula which is either lor a disjunction of normal forms in Var 
of degree k + 1. □ 

376 
FINITE APPROXIMABILITY 
It is worth noting that for any distinct normal forms 0' and 0" (in Var) of the 
same degree the implication O' —► -i6" is true in every model and so belongs to 
K. It follows that for every normal form 6 in Var of degree n and every modal 
formula <p with Var<p C Var and md((p) < n we have either 6 —> (p G K or 
6 —► -><p G K. Indeed, by Theorem 11.2, p is equivalent in K either to JL, in 
which case 6 —► -up G K, or to a disjunction 6 of normal forms of degree n. If 6 
is a disjunct of 6 then 9 —► <p G K; otherwise 9 —► -up G K. 
Of course, normal forms are too lengthy to be used in practice: each 9 in 
NFn+i contains |NFn| + r conjuncts and |NFn| is calculated recursively as 
|NF0| = 2r and |NF„| = |NF0| 2|NF"-1L 
However, they provide us with another theoretical tool for constructing models. 
First we define a binary relation < on NF by putting 9' < 9n iff O9* is a 
conjunct of 0", for every 0', 9" G NF. We write 9' <n 9" if there are 0i,..., 0n-1 
such that 9f < 9\ < ... < 0n_i < 0"; 0' <° 0" means 0' = 0". Now, with each 
normal form 0 we associate a model Tie = (Se,^e) on a frame Se — (We, Re) 
which are defined as follows: 
We = {9f G NF : 0' <n 0, for some n > 0}, 
9'Re9n iff 0' > 0", 
(p) = {0' € W0 : p is a conjunct of 0'}. 
Theorem 11.3 For each normal form 9 and each 0' € W#, 0') f= 0'. 
Proof An easy induction on the degree of 0' is left to the reader as an exercise 
(see also the proof of Theorem 11.6.) □ 
Note that Theorem 11.3 yields another proof of the finite approximability of 
K. Indeed, if (p K then we reduce -«p to a disjunction of normal forms. Since 
-><p is not equivalent to _L (for otherwise (p would be equivalent to T, contrary 
to tp K), this disjunction is not empty. Let 0 be one of its disjuncts. Then, 
according to Theorem 11.3, we have (pJle,9) f= 0 and so (Tie, 9) <P- However, 
this proof does not go through for logics L D K, because $$ is not in general a 
frame for L. For example, no frame #0 validates D, since it is finite and all its 
points are irreflexive. 
For D the argument above will remain correct, if we somewhat modify the 
definitions of normal form and the model Tie- Observe first that the following 
proposition holds. 
Proposition 11.4 Suppose that, for some n > 0, NFn = {0i,...,0a}. Then 
O0i V ... V O0S € D. 
Proof The formula 9\ V... V 9s is valid in Cl and so O01 V... V 09s G D, since 
O0i V ... V O9S O(0i V ... V 9S) G K and OT G D. □ 

UNIFORM LOGICS 
377 
It follows that every normal form 0 A -»O0i A... A -iO0S is equivalent to _L in 
D, and so we can define ID-suitable normal forms like this. Every normal form of 
degree 0 is D-suitable, and a normal form 0 of degree n > 0 is D-suitable if every 
0' < 0 is D-suitable and there is at least one 0' < 0. Alternatively, this means 
that in the inductive step of the original definition of normal form we require at 
least one -»* to be blank. The next theorem is proved similarly to Theorem 11.2, 
using Proposition 11.4. 
Theorem 11.5 Every modal formula cp urith Varcp C Var and md(cp) < n is 
equivalent in D either to 1. or to a disjunction of ID-suitable normal forms in 
Var of degree n. 
As to the frame 'Sq, we can make it serial by adding to it a reflexive point 
accessible from the final points in Wq. More exactly, given a normal form 0, 
define a model Wig = (00,110) on a frame 00 = (V0, Sq) by taking 
Vo = We U {T}, 
0%0" iff either O'RqO" or md(0') = 0 and 0" = T, 
ilo(p) = 2J#(p). 
It should be clear that if 0 is D-suitable, T is the reflexive last point in 00, and 
so 00 is serial. 
Theorem 11.6 For every normal form 0 and every 0' e Vo, (010,0') |= O'. 
Proof By induction on the degree of O'. The basis of induction is trivial. 
Suppose 0' = 0oA-uO0i A... A-isO0s is of degree n+1. By the definition of U0, 
(91$, O') f= 0o. If -»i is blank then 0* < O', whence O'SqOi and (OI0, O') f= O0*, since, 
by the induction hypothesis, (910,0*) f= 0*. And if ->* is -> then (910,0') f= -»00*, 
for otherwise O'SqO" and (910,0") f= 0* for some 0" e Vq. By the definition of 
Sq, 0" is either a normal form of degree nor T. The former case means 0" = 0*, 
since, by the induction hypothesis, (910,0") f= 0" and since distinct normal 
forms cannot be simultaneously true at the same point; but this contradicts the 
definition of <. And in the latter case md(0') = 0, which is also impossible. 
□ 
Thus, the argument used above for proving the finite approximability of K 
remains valid for D too. Moreover, we will show now that it goes through for all 
uniform logics as well. 
Suppose L is a uniform logic. Call a normal form 0 L-suitable if 00 is a 
frame for L. It should be clear that this definition agrees with the definition of 
D-suitability. 
Theorem 11.7 Suppose L is a uniform logic. Then every modal formula cp with 
Varcp C Var and md(cp) < n is equivalent in L either to 1. or to a disjunction 
of L-suitable normal forms in Var of degree n. 

378 
FINITE APPROXIMABILITY 
Proof By Theorem 11.5, p is equivalent in D to 1 or a disjunction of D- 
suitable normal forms of degree n. So it suffices to show that every D-suitable 
normal form 9 such that 6 —► JL ^ L is L-suitable. (If ->0 £ L then 6 is equivalent 
to JL in L.) 
Suppose otherwise. Let 6 be an L-consistent and D-suitable normal form of 
the least possible degree under which it is not L-suitable. Then a uniform formula 
0 £ L of some degree m is refuted at the point 6 in 0#, i.e., there is a model 
= (0#,2J) such that (9Jt, 9) ft 0. 
For every p £ Var0, let Tp = {9' £ 9 |m: (9Jt, 9f) f= p} and let 8p be the 
disjunction of all the formulas in Fp (if Fp — 0 then Sp = J_). Observe that for 
every 9f £ 9]m we have: 
(91#, 9f) |= Sp iff 9f is a disjunct of Sp 
iff 9' £Tp 
iff (SDM') ftp. 
Therefore, by Proposition 11.1, the formula 0' = ip{8p/p : p £ Var0} is false at 9 
in 91#. Now, if rad(0') > n then m> n and so Sp — JL for every p £ Var0, i.e., ipf 
is variable free. But according to Exercise 3.19, ip* is then equivalent in D to T or 
JL, contrary to 0# ^ ip* an(l the consistency of L. And if md{xpl) < n then, as we 
have observed, either 9 —► xpf £ K, which is impossible, since (91#, 0) )/= 9 xpf, 
or 9 —> -•'0' £ K, from which 0' —► -»0 £ K and so ->0 £ L, contrary to the 
L-consistency of 9. □ 
As a consequence of this theorem we obtain our final result. 
Theorem 11.8 Every uniform logic is finitely approximable. 
In particular, the McKinsey logic K 0 DOp —► ODp = D 0 DOp —► ODp 
turns out to be finitely approximable. 
11.2 	Si-logics with essentially negative axioms and modal logics with 
□O-axioms 
A formula is said to be essentially negative if every occurrence of a variable in it 
is in the scope of some For example, the Skvortsov formula in Exercise 2.16 
is essentially negative. The following three facts: 
• Glivenko’s theorem, 
• the local tabularity of Cl, and 
• a possibility of transforming a derivation of any formula <p in any logic in 
such a way that it should not contain variables having no occurrences in (p 
enable us to reduce the derivability problem in a superintuitionistic logic with 
a finite set of essentially negative additional axioms to the derivability 
problem in Int. Indeed, suppose 0 is an essentially negative formula, i.e., 0 = 
0'(-*Xl, ■ • • ? ~'\n) for some formulas 0'(<?i,..., qn), Xu • • •, Xn, and p is an 
arbitrary formula. How can we decide whether or not <p £ Int + 0? 

ESSENTIALLY NEGATIVE AND DO-AXIOMS 
379 
Let Pi,... ,pm be all the variables in <p. If <p E Int + ip then there exists 
a substitutionless derivation of <p in Int -f ip in which substitution instances 
of the axiom ip contain no variables different from pi,...,pm. Each of these 
substitution instances has the form ^,(”,Xiwhere every x*, for z = 
1,..., n, is some substitution instance of Xi containing only (some of) pi,... ,pm. 
By Glivenko’s theorem (Corollary 2.49, to be more exact) and in view of the local 
tabularity of Cl, there are < 22 pairwise non-equivalent in Int such substitution 
instances of -»Xi» f°r each ^ = 1,..., n. Therefore, there exist only finitely many 
pairwise non-equivalent in Int substitution instances of ip containing pi,... ,pm, 
say ipi,..., ipk, and we can effectively construct them. Then, by the deduction 
theorem, 
<p E Int + ip iff ipi,..., ipk b/nt <p iff ipi A ... A ipk —> <p E Int 
and so we obtain a decision algorithm for Int + ip, because Int is decidable. 
Let us observe now that in the argument above we used only two specific 
properties of Int, namely its decidability and Glivenko’s theorem, which holds 
for every consistent si-logic. Thus, actually we have proved 
Theorem 11.9 Suppose L is a decidable si-logic and ip an essentially negative 
formula. Then the logic L + ip is also decidable. 
The proof of Theorem 11.9 can be easily supplemented to a proof of the 
following: 
Theorem 11.10 Suppose L is a finitely approximable si-logic and ip an 
essentially negative formula. Then the logic L + ip is also finitely approximable. 
Proof We continue the argument above, taking L instead of Int. Suppose <p ^ 
L + ip. Then ipiA...Aipk —► <p & L and so there is a finite model DJI = (S', 2J) with 
root x such that DJI f= L, x f= ipi A ... A ipk, and x ^ <p. As was shown above, 
every formula in L + ip of the variables Pi,... ,pm belongs to L + A... 
Therefore, changing (if necessarily) the valuation 2J in 9DT so that 2J(g) = 2J(pi) 
for every variable q different from pi,... ,pm, we obtain that x f= ip and so DJI is 
a finite model for L -f ip refuting <p. □ 
It follows in particular that the si-logics, obtained by adding to Int Rose’s 
non-realizable formula (see Section 2.9) or the Skvortsov formula or both, are 
decidable and finitely approximable. 
Results similar to Theorem 11.9 and 11.10 hold for extensions of K4 as well. 
However, in this case instead of essentially negative formulas we take so called 
DO -formulas in which every occurrence of a variable is in the scope of a modality 
DO. Instead of Cl we take S5, which is locally tabular by Corollary 5.19. Finally, 
instead of Glivenko’s theorem we use 
Lemma 11.11 For every modal formulas <p and ip, 
0(p <-> O ip E S5 iff DO(p <r+ DO ip E K4. 

380 
FINITE APPROXIMABILITY 
Proof It suffices to show that Otp —> Oip e S5 iff □<></? —> DOip e K4. (<=) is 
a consequence of K4 C S5 and Op DOp e S5. 
(=>) Suppose DOtp —► DO^; £ K4. Then there is a finite model SDt, based on 
a transitive frame, and a point x in it such that x f= □<></? and x ^ DOt/j. It 
follows from the former relation that every final cluster accessible from x, if any, 
is non-degenerate and contains a point where <p is true. The latter relation means 
that x sees a final cluster C at all points of which xp is false. Now, taking the 
generated submodel of Wt based on C, we clearly obtain a model for S5 refuting 
Oip —► Oxp. □ 
Thus, we have everything that is required to prove the following two theorems. 
Theorem 11.12 Suppose L is a decidable normal (or quasi-normal) extension 
of K4 and xp a DO-formula. Then the logic L©^ (respectively, L + xp) is also 
decidable. 
Proof Similar to the proof of Theorem 11.9 with the help of Theorem 4.7 and 
Exercise 3.5. □ 
Theorem 11.13 Suppose L is a finitely approximable normal (or quasi-normal) 
extension of K4 andxp a UO-formula. Then the logic L(Bxp (respectively, L + xp) 
is finitely approximable too. 
Proof Similar to the proof of Theorem 11.10 (in the normal case <p ^ L®xp 
means that □+('0i A ... A xpk) —> <p L). □ 
It follows in particular that the quasi-normal logics K4 + DOp -> ODp = 
K4 + DOp —v -iDO-ip and S4.l' are decidable and finitely approximable. It is to 
be noted that extending a finitely approximable logic with infinitely many □<>- 
axioms does not in general preserve finite approximability (see Exercise 11.3). 
11.3 	Subframe and cofinal subframe logics 
Another way towards general completeness results is to use the information about 
logics’ frames which is contained in their canonical axioms. In Section 7.3 we 
saw that si-logics with disjunction free extra axioms are finitely approximable. 
According to Theorem 9.44, all these logics are axiomatizable by canonical 
formulas without closed domains—we called them subframe and cofinal subframe 
formulas. Now we consider modal logics in NExtK4 with canonical axioms of 
that sort. With the help of the modal companion and preservation theorems the 
results obtained below can readily be transferred to the corresponding si-logics. 
A logic L € NExtK4 is called a subframe logic if it can be represented in the 
form 
L = K4 0 (a(S'i) : i e I}. 
The class of all subframe logics is denoted by Sf. A logic L of the form 
L = K4 ® {a(fo, _L) : i € 1} 
is called a cofinal subframe logic, and the class of all such logics is denoted by 
CST. 

SUBFRAME AND COFINAL SUBFRAME LOGICS 
381 
Example 11.14 As is shown by Table 9.6, the majority of the standard modal 
logics are in ST or CST. Every extension of S4.3 is axiomatizable by canonical 
formulas which are based on chains of non-degenerate clusters and so have no 
closed domains. Therefore, NExtS4.3 = ExtS4.3 is a (proper) subclass of CST. 
Theorem 11.15 (i) Suppose L = K4 ® {c^fo, _L) : i € I}. Then for every 
canonical formula a(S',S), _L); _L) € L iff $ a(S'i, _L) for some i £ I, 
i.e., iffB is cofinally subreducible to for some i € I. 
(ii) Suppose that L = K4 ® (a(S'i) : i € I}. Then for every a(S',®, _L); 
a($,2),_L) € L iff a(S',D) € L iff S' ¥= Oi($i) for some i e I, i.e., iff'S is 
subreducible to Si for some i € I. 
Proof (i) If 0(5,2), _L) € L then S ^ a(Si,-L) for some i € /, since clearly 
SM=*(S,»,JL). 
Now suppose that S' ^ a(Si> -L) for some i € /, i.e., there is a cofinal 
subreduction / of S to Si- Suppose also that 0 is a frame refuting a(S, ®,-L). Then 
there is a cofinal subreduction g of 0 to S- By Theorem 9.21, the composition 
fg is a cofinal subreduction of 0 to Si and so, by the refutability criterion 
(Theorem 9.39), 0 a(Si,-L). Thus, a(S, ®,-L) is valid in every general frame for 
L, and hence a(S,2), -L) € L. 
(ii) is proved analogously. □ 
As an immediate consequence of Theorem 11.15 and the completeness 
theorem for the canonical formulas (Theorem 9.43) we obtain 
Corollary 11.16 Every finitely axiomatizable subframe or cofinal subframe logic 
is decidable. 
Moreover, this result may be generalized to 
Theorem 11.17 Suppose L € NExtK4 (or L € Extint) is recursively axioma- 
tizab'le by subframe or cofinal subframe formulas. Then L is decidable. 
Proof Let L be recursively axiomatizable by some cofinal subframe formulas. 
According to Theorem 11.15, a(0,2), _L) € L iff there is a cofinal subreduct S of 
0 such that a(S, -L) is an axiom of L. So our decision algorithm may be as follows. 
Given a formula a(0,2), _L), we construct all rooted cofinal subreducts 3i, • • •, 3n 
of 0 and then check whether at least one of the formulas a(3i, _L),..., a(S'n5 -*-) 
is an axiom of L. If the outcome of this check is positive then a(0,2), _L) € L\ 
otherwise a(0,2), _L) ^ L. 
The case of a subframe L is considered in the same manner. □ 
However, there are undecidable recursively axiomatizable logics in ST and 
CST. Let 3n = (Wn, Rn), for n = 3,4,..., be the sequence of frames shown in 
Fig. 11.1. 
Lemma 11.18 For no n ^ m, $n is subreducible to $m. 
Proof Clearly $n is not subreducible to Sm if n < m. So suppose that n > m 
and / is a subreduction of $n to $m. Since both a\ and b\ have three pairwise 

382 
FINITE APPROXIMABILITY 
inaccessible successors in every point in f~1(a\) and f~l{bi) must see an 
antichain of three points as well. Therefore, without loss of generality we may 
assume that f~l{a{) = {a\} and /-1(i>i) = {i>i}. It should be clear also that 
/_1(a) = {a} and /_1(i>) = {b}. Since aiRma2 and not biRma2, we must have 
f~1(a2) = {<^2}; symmetrically, /-1(i>2) = {£>2}- And by the same argument, for 
each i such that 1 < i < m, f~1(ai) = {a*} and f~l{bi) — {bi}. But then we 
come to a contradiction. For bm-1 does not see c in while in $n bm-1 sees 
all the points which are accessible from am except am itself, and so no point in 
$n can be mapped by / to c without violating (Rl). □ 
As a consequence of Lemma 11.18 and Theorem 11.15 we obtain the following: 
Theorem 11.19 (i) The cardinality of both ST andCST is that of the 
continuum. 
(ii) 	There is a continuum of undecidable logics in ST andCST, with infinitely 
many of them being recursively axiomatizable (but not by canonical formulas). 
Proof (i) Let I be a set of natural numbers, Lj = K4 © {a(3^) : i e 1} and 
n I. Clearly, $n a(3n)- On the other hand, by Lemma 11.18, $n |= a($i) 
for every i € I. Therefore, a(S'n) ^ Lj and so Lj ^ Lj whenever I ^ J. 
(ii) Take any recursively enumerable set I of natural numbers which is not 
recursive. The logic Lj is then undecidable, for otherwise, since a(S'n) € Lj iff 
n € /, the set I would recursive. By Craig’s theorem (see Section 16.2), Lj is 
recursively axiomatizable. □ 
Since all the frames 3n are partial orders, Theorem 11.19 holds for the classes 
of si-logics with implicative and disjunction free extra axioms. It means in 
particular that there is a continuum of si-logics axiomatizable by purely implicative 
formulas. 
Another immediate consequence of Theorem 11.15 is the following: 
Theorem 11.20 All subframe and cofinal subframe logics are finitely 
approximate. 
Proof Suppose L is in ST or CST and 2), _L) ^ L. Then by Theorem 11.15, 
$ is a frame for L and, as we know, $ ^ 2), _L). □ 

SUBFRAME AND COFINAL SUBFRAME LOGICS 
383 
The terms “subframe logic” and “cofinal subframe logic” are justified by the 
following frame-theoretic characterization of these logics. Say that a class C of 
frames is closed under (cofinal) subframes if every (cofinal) subframe of # is in 
C whenever $ e C. 
Theorem 11.21 (i) A logic in NExtK4 is a subframe logic iff it is characterized 
by a class of frames that is closed'under subframes. 
(i) A logic in NExtK4 is a cofinal subframe logic iff it is characterized by a 
class of frames that is closed under cofinal subframes. 
Proof (ii) Suppose L is a cofinal subframe logic. We show that the class of all 
frames for L is closed under cofinal subframes. Let 0 be a frame for L and 9) 
a cofinal subframe of 0. Then f= L, since otherwise 9) ^ (*(#, _L) for some 
1) e L and so, by Theorem 9.21 and the refutability criterion, 0 &(#, _L) 
which is a contradiction. 
Now suppose that L is characterized by some class of frames C that is closed 
under cofinal subframes. We show that L = V where 
V = K4 0 {<*(#, !.):#[£ L}. 
Indeed, if # is a finite rooted frame and $ L then a(Sr, _L) e L, for otherwise 
(5 ^ 1) for some 0 E C, and hence there is a cofinal subframe fj of 0 which 
is reducible to but 9) e C and so, by the reduction theorem, # is a frame for 
L, which is a contradiction. Thus, L' C L. 
To prove the converse inclusion, suppose -L) e L. Then $ L, and 
hence &(#, -L) E Lf. Therefore, by Theorem 11.15, E Lf. 
(i) is proved analogously. □ 
Corollary 11.22 If a logic L e NExtK4 is characterized by a class of frames 
that is closed under cofinal subframes then L has the finite model property. 
Corollary 11.23 ST C CST. 
Proof The fact that ST C CST is an immediate consequence of Theorem 11.21. 
However, there is a continuum of cofinal subframe logics that are not subframe 
ones. Indeed, there is a continuum of logics axiomatizable by canonical formulas 
of the form _L), where is the frame defined in Fig. 11.1. And none of 
them is a subframe logic, since the class of frames for such a logic is not closed 
under subframes. For if we add to a new point which is seen from all the 
points in and denote the result by 0* then clearly 0* f= a($j, _L) for any j, 
but fo, being a subframe of 0*, refutes a(fo, _L). □ 
Corollary 11.24 CST is a complete sublattice o/NExtK4. ST is a complete 
sublattice of CST. 
Proof Suppose Li € CST for i e I. Then for each i G /, there is a set A* of 
cofinal subframe formulas such that Li = K40A*. Therefore, we have ©ie/ii = 
K4 © \JieI Ai e CST. 

384 
FINITE APPROXIMABILITY 
Fig. 11.2. 
As to the intersection L = f]ieI Li, it is clear that L is characterized by the 
class : $ H which is closed under cofinal subframes. Therefore, by 
Theorem 11.21, L € CST. 
The class ST is considered analogously. □ 
Translating Theorem 11.21 into si-logics we obtain a nice frame-theoretic 
criterion of axiomatizability by implicative and disjunction free formulas. 
Theorem 11.25 (i) A si-logic is axiomatizable by implicative formulas iff it is 
characterized by a class of frames closed under subframes. 
(ii) A si-logic is axiomatizable by disjunction free formulas iff it is 
characterized by a class of frames closed under cofinal subframes. 
Now we give a frame-theoretic criterion of elementarity, ^-persistence and 
strong Kripke completeness of logics in ST and CST. 
Let Sc — {Wc,Rc) be a frame containing a cluster C. For an ordinal £, 
0 < £ < u), we denote by = (w^,R1^ the frame that is obtained from Sc 
by replacing C with an ascending chain of £ irreflexive points. More exactly, we 
put 
Ws = (W - C) U {i : 0 < i < £} 
and, for all x,y € W$, 
xR£ry iff xRcy or 
3i,j < £ (x = i A y = j A i < j) or 
3i < £3z e C (x = i A zRcy) or 
3i < £3z € C (y = i A xRqz). 
S^ = (w^,R0 is the result of replacing C in Sc with an ascending chain 
containing £ reflexive points, i.e., 
R£ = Rfu{(i,i) : 0 < i < £}. 
Fig. 11.2 illustrates the given definition. 

SUBFRAME AND COFINAL SUBFRAME LOGICS 
385 
We say that a logic L has the finite embedding property if a Kripke frame S 
validates L whenever each finite subframe of # is a frame for L. L is said to be 
universal if there is a set 4> of universal first order sentences in R and = (which 
are of the form Vx... Vy 0, where 0 contains no quantifiers) such that, for every 
Kripke frame #, S f= L iff S f= 4>. 
Theorem 11.26 The following conditions are equivalent for each subframe logic 
L: 
(1) L is universal; 
(2) L is elementary; 
(3) L is V-persistent; 
(4) L is IZ-persistent; 
(5) L is canonical; 
(6) L is strongly Kripke complete; 
(7) for every finite rooted frame Sc with a non-degenerate cluster C 
V£ < u) |= L implies Sc |= L 
and 
V£ < u) 3^ |= L implies Sc N 
(8) L has the finite embedding property. 
Proof The implication (1) => (2) is trivial and (2) => (3) follows from 
Theorems 10.19 and 11.20. 
(3) 	=> (4). Let 5 be a refined frame for L. According to the proof of 
Theorem 8.51, kS is (isomorphic to) a subframe of k(S+)+- Since S L and L is 
XLpersistent, we then have (#+)+ |= L and k(S+)+ |= L, from which, by the 
proof of Theorem 11.21, kS |= L. 
The implications (4) => (5) and (5) => (6) are obvious. 
(6) => (7). Suppose that Sc — (Wc,Rc) is a finite rooted frame with a 
non-degenerate cluster C and V£ < u) Sl{ |= L. We must prove that Sc |= 
Let {ai : i € 1} be all the points in Wu. With each a* we associate a variable 
Pi different from pj for any j ^ i and construct from them the canonical formulas 
Oi(Sl£) for all £ such that 0 < £ < u. Now take the tableau 
(0,{a(Sf):O <£<«,}) 
and show that it is L-consistent. Suppose otherwise. Then we have some £ < uj 
for which 
«(8lr)Va(ffj,)V...Va(S|r)eL. 
But on the other hand, since Sl£ is a subframe of S%r, for C<<£, and by the proof 
of Theorem 9.39, there is a valuation 93 in S'|r such that all the formulas a(^r), 
for £ < £, are false at the root of under 23, which is a contradiction because 
N l. 

386 
FINITE APPROXIMABILITY 
By (6), there is a model DJI on a Kripke frame 0 = (V, S) such that all o;(Sr|r), 
for 0 < £ < u, are simultaneously false at some point in DJI and 0 f= L. Define 
a map / from V onto Wu by taking 
Using the proof of Theorem 9.39, it is not hard to check that / is a subreduction 
of 0 to On the other hand, we can easily construct a reduction g of 3£T to 
3c- Indeed, if C = {bo,..., bn} then we may take 
By Theorem 9.21, there is a subreduction of 0 to 3c and so 3c \= L, for 
otherwise 0 ^ L, which is a contradiction. 
The case with 3£ is considered in exactly the same way. 
(7) => (8). Suppose otherwise, i.e., there is a Kripke frame 0 such that every 
finite subframe of 0 validates L but 0 L. Then there exists a subreduction / 
of 0 to a finite rooted frame 3 = (W^, R) such that 3 ^ L- Starting with 3 we 
construct by induction a finite rooted frame which is not a frame for L but is 
embeddable in 0, contrary to our assumption. At the very beginning we mark by 
some signs all the clusters in 3? which means that all of them are to be analyzed 
in the sequel. 
Suppose now that we have already constructed a finite rooted frame 9) = 
(V, S) and a subreduction g of 0 to 9) such that 9) L and g~l(x) is a singleton 
for each x belonging to an unmarked cluster in 9). (At the first step 9) = 3-) 
Let C = {ao,... ,a^} be a marked cluster in 9) all immediate predecessors 
Ci,..., Cm of which are unmarked and let &i € Ci,..., bm € Cm. By the 
induction hypothesis, g~l(bi) = {a:*} for some xi,... ,xm in 0. Choose a minimal 
number of disjoint sets A\,..., An of points in 0 such that 
• for each i € {1,..., m} there is j € {1,..., n} such that Aj C Xi\ 
and, for each i € {1,..., n}, either 
• Ai = {ycb ••• ?*/*;}, g{Vj) = dj for j = 0, ...,fc, and A* is a subset of a 
cluster in 0 
• Ai is an infinite ascending chain yo, Vi,... all the points of which are either 
simultaneously irreflexive or simultaneously reflexive and g(yj) € C for 
The existence of such ..., An follows from the fact that g is a subreduction 
of 0 to 9). (See Fig. 11.3.) Our next action depends on the number of these 
AAn. Notice by the way that 1 < n < m. 
Case l.n = l. 
/(*) = 
! 
undefined otherwise. 
if x ^ pi and, for each £ < u, the 
premise of o:(3|r) is true at x 
x if x € Wc - C 
bi if x = m and i = modn+i(m). 
or 

SUBFRAME AND COFINAL SUBFRAME LOGICS 
387 
Fig. 11.3. 
1.1. 	If A\ — {yo,... i.e., if A\ is a part of a cluster in 0, then we put 
= 53, mark in 9)' all the clusters that were marked in 9) except C and define 
a partial map gf from 0 onto $)' by taking 
Q'tx\ = / 9(x) if a: € (doing - g 1(C)) U Ai 
^ ' 1 undefined otherwise. 
It is clear that 9)' L, gf is a subreduction of 0 to 9)' and g'~1{x) is a singleton 
for each x belonging to an unmarked cluster in 9)'. Notice also that the number 
of marked clusters in 9)' is less than that in 9). 
1.2. 	Suppose A\ is an infinite ascending ch?dn yo,yi,... of irreflexive points. 
Then C is non-degenerate and, since 9) = 9)c ^ there is, by (7), some £ < u 
such that 9)gr L. In this case we put 9)' = fj|r, mark in 9)' all the clusters that 
were marked in 9) (the new points 0, ...,£ — 1 remain unmarked) and define a 
partial map gf from 0 onto 9)' by taking 
{g(x) if x e domg - g^iC) 
i if x = yu 0 < i < £ 
undefined otherwise. 
Again g' is a subreduction, 9)' L, g' x(x) is a singleton for each x belonging 

388 
FINITE APPROXIMABILITY 
to an unmarked cluster in 9)f and the number of marked clusters in 9)' is less 
than that in 9). 
1.3. 	The case when A\ is an ascending chain of reflexive points is considered 
in the same way but using the second part of (7), i.e., 9)^ instead of 9)1^. 
Case 2. Suppose now n > 1. Then we first form a new frame 9f = (V",S") 
by taking (see Fig. 11.3) 
V" = (V -C)UC1U...UCn, 
where 
C1 = (4,...,4}, i = 
and, for all x,y € V7', 
xS"y iff x, y € V - C A xSy or 
3i,j (x = a1- A ajSy) or 
3i,jJ (y = alj A x e biJ A Ai C xjT) or 
3i,jJ(x = aj A y = a\ A C is non-degenerate). 
Mark in 9)" all the clusters that were marked in 9) and C1,..., Cn as well. After 
that we define a map g" from 0 onto 9f by taking 
(g{x) if x e domg - g_1 (C) 
a) if x - yi e Ai and modfc+1(i) = j 
undefined otherwise. 
It is not difficult to see that gn is a subreduction of 0 to 9)". Moreover, 9f f^= L, 
since 9)n is reducible to 9), and g"~x(x) contains only one point if C(x) is an 
unmarked cluster in 9)". But the number of marked clusters in 9f has become 
greater than that in 9). However, we need not worry. For we can now analyze the 
new clusters C1,..., Cn, which clearly satisfy the condition of Case 1 and so we 
shall eventually construct a frame 9)' having all the desirable properties and less 
marked clusters than 9). Fig. 11.3 will help the reader to complete the details. 
The implication (8) => (1), completing the circle, is a consequence of the 
well known theorem of Tarski (1954) from classical model theory. Roughly, it is 
proved in the following way. Let C be the set of all finite rooted frames which do 
not validate L. With each ^ € C we can associate a universal first order sentence 
4>$ such that a Kripke frame 0 is a (classical) model for <j)$ iff # is not a subframe 
of 0. It is easy to see now that a Kripke frame 0 validates L iff 0 is a (classical) 
model for the set {0$ : ^ € C}. □ 
Example 11.27 Grz = K4 ® &(•) ® a(R) is neither elementary nor V- 
persistent nor strongly complete, since every finite linearly ordered reflexive 
frame validates Grz, while the two point cluster is not a frame for it. Neither 
GL = K4®a(o) meets this properties. For each finite linearly ordered irreflexive 
frame validates GL, while any non-degenerate cluster does not. 

SUBFRAME AND COFINAL SUBFRAME LOGICS 
389 
Fig. 11.4. 
Theorem 11.26 can be generalized in two directions. First, we can extend it 
to the class CST. Say that a subreduction / of a frame 0 to a finite frame S 
is a quasi-embedding of S in 0 if f~x(x) is a singleton for every point x whose 
cluster C(x) is not final in #. In such a case S is called quasi-embeddable in 0. 
For example, the frame S in Fig. 11.4 is quasi-embeddable in 0 and cofinally 
quasi-embeddable in ft. 
A logic L has the finite cofinal quasi-embedding property if a Kripke frame S 
validates L whenever every finite frame which is cofinally quasi-embeddable in 
S validates L. 
Theorem 11.28 The following conditions are equivalent for each cofinal sub- 
frame logic L: 
(1) L is elementary; 
(2) L is V-persistent; 
(3) L is canonical; 
(4) L is strongly Kripke complete; 
(5) for every finite rooted frame Sc with a non-degenerate non-final cluster 
C, V£ < u) S1^ [= L implies Sc f= L and V£ < u J= L implies Sc f= L; 
(6) L has the finite cofinal quasi-embedding property. 
Proof The implications (1) => (2) => (3) => (4) => (5) => (6) are proved in the 
same way as the corresponding implications in Theorem 11.26. 
(6) => (1). Given a finite rooted frame #, one can construct a first order 
formula cj) (in R and =) with the free variables xi,...,xn such that a Kripke 
frame 0 satisfies <\> iff S is cofinally quasi-embeddable in 0 (for details see 
Exercise 11.12). Then 0 L iff there is a finite rooted frame S ^ L which is cofinally 
quasi-embeddable in 0 iff 0 |= 3x\... 3xn(j>. □ 
Example 11.29 The logic K4.1 = K4 ® a(»,_L) ® a((°o),_L) is elementary, 
P-persistent and strongly complete. Indeed, let Sc be a finite frame with a 
nonfinal non-degenerate cluster C. Then Sc &(•, _L) iff Sc has a dead end iff both 
Slf[ &(•, -L) and #£ &(•, _L) hold for any finite £. Similarly, Sc V1 <*((£2), -L) 

390 
FINITE APPROXIMABILITY 
iff 3c has a final proper cluster iff both 3£r g((oo), _L) and 3£ q((^), -L) 
hold for any finite £. 
Remark Note that elementary logics in CST are not necessarily universal, and 
D-persistent logics in CST are not necessarily 7^-persistent, witness S4.1 (see 
Exercise 10.4). 
As an immediate consequence of Theorems 11.26, 11.28 and the preservation 
theorem we obtain 
Theorem 11.30 Every si-logic L with disjunction free extra axioms is 
elementary (universal, if L is axiomatizable by implicative formulas), V-persistent and 
strongly complete. 
Another way of generalizing Theorem 11.26 is to extend it to the class of 
subframe logics in NExtK, which may be defined just as logics that are 
characterized by classes of (general) frames closed under subframes. (Such are, for 
instance, the logics T, KB, K5, Altn in Table 4.2.) 
Theorem 11.31 The following conditions are equivalent for each subframe logic 
L € NExtK: 
(1) L is universal and Kripke complete; 
(2) L is elementary and Kripke complete; 
(3) L is V-persistent; 
(4) L is IZ-persistent; 
(5) L is strongly Kripke complete; 
(6) L has the finite embedding property and is Kripke complete. 
Proof We give only a sketch of the proof; details are left to the reader. All 
the implications except (5) => (6) are established in the same way as in 
Theorem 11.26. Suppose L is strongly Kripke complete but does not have the finite 
embedding property. Then there is a rooted Kripke frame 0 = (V, S) such that 
0 L and all finite subframes of 0 validate L. One can show that without 
loss of generality we may assume 0 to be countable. Let a*, i < u, be all the 
points in 0 and ao the root. Consider the tableau t = (r, 0), where T consists of 
all formulas of the form p0, °n(Pi -> Opj) if aiSaj, Dn(pi —> -iOpj) if -<aiSaj, 
□n(p* ~* ~^Pj) f°r i 7^ j- Since every finite subframe of 0 is a frame for L, t is 
L-consistent and so realizable in a Kripke frame S) for L. It is not hard to check 
that in this case f) is subreducible to 0, which is a contradiction. □ 
It turns out, however, that subframe logics in NExtK are not in general 
finitely approximable and even Kripke complete. 
Example 11.32 Let L be the logic of the frame 3 constructed in Example 8.52. 
Since every rooted subframe 0 of 3 is isomorphic to a generated subframe of 3, 
0 |= L and so L is a subframe logic. We show now that L has the same Kripke 
frames as the logic 

QUASI-NORMAL SUBFRAME AND COFINAL SUBFRAME LOGICS 391 
Suppose 0 is a rooted Kripke frame for GL.3 refuting a formula p € L. Then 
clearly 0 contains a finite subframe refuting p. Since is a finite chain of 
irreflexive points, it is isomorphic to a generated subframe of 3- Therefore, 3 p 
contrary to our assumption. Thus 0 |= L. 
Conversely, suppose 0 is a Kripke frame for L. Then 0 is irreflexive. For 
otherwise 0 refutes the formula p = n2(Dp —> p) A □ (□p —> p) —> Dp which 
is valid in 3- Let us show now that 0 is transitive. Suppose otherwise. Then 0 
refutes the formula Dp —> □ (□p V (□# —> #)) which is valid in 3, because a; is a 
v 
reflexive point. Finally, since 0 |= <p, 0 is Noetherian and since 3 h= a( • ), 
we may conclude that 0 is a frame for GL.3. 
It follows that the subframe logic L is Kripke incomplete. Indeed, it shares 
the same class of Kripke frames with GL.3 but is different from it, because 
□p-> nnpe GL.3 — L. 
11.4 	Quasi-normal subframe and cofinal subframe logics 
Let us now briefly consider quasi-normal logics containing K4 which can be 
axiomatized by normal and quasi-normal canonical formulas without closed 
domains. Those quasi-normal logics that can be represented in the form 
(K4 0 (a(3i) : » € /}) + {<*($,■) : j € J} + (a#(3k) : k € K} (11.1) 
are called, as in the normal case, (quasi-normal) subframe logics and those of the 
form 
(K4 0 {a(3i, -L) : i € I}) + {a(3j, -L) : j € J} + {a*(3fc? -L) : k € K} (11.2) 
are called (quasi-normal!) cofinal subframe logics. The classes of quasi-normal 
subframe and cofinal subframe logics are denoted by QST and QCST, 
respectively. The example of Solovay’s logic S = K4 + a(o) + a(#) shows that 
Theorem 11.20 cannot be extended to QST and QCST. Yet we are going to prove 
that all finitely axiomatizable quasi-normal subframe and cofinal subframe logics 
are decidable. 
We use the following notation. For a frame 3 = (W, R) with irreflexive root 
u and 0 < £ < u, 3£r and 3£ denote the frames that are obtained from 3 by 
replacing u with the descending chains 0,... , £ — 1 of irreflexive and reflexive 
points, respectively; = (wV+i)-, R^j+1y, ) denotes the frame 
that is obtained from # by replacing u with the infinite descending chain 0,1,... 
of irreflexive points and then adding the irreflexive root cj, with P^+i)* 
containing all subsets of W — {u}, all finite subsets of natural numbers {0,1,...}, all 
(finite) unions of these sets and all complements to them in the space 
(see Fig. 11.5). Note that if uj € X € -P^+i)* then X contains all natural 
numbers starting from some n > 0. Observe also that 3 is a quasi-reduct of every 
frame of the form 3|r, 3£ or 3^+1),. 

392 
FINITE APPROXIMABILITY 
Fig. 11.5. 
The following theorem characterizes the canonical formulas belonging to 
logics in QST and QCST. Its proof, as that of Theorem 11.15, uses Theorem 9.21, 
which can be readily generalized to compositions of (cofinal) quasi-subreductions. 
Theorem 11.33 Suppose L is a subframe or cofinal subframe quasi-normal 
logic. Then 
(i) for every finite frame # with root u, _L) € L iff ($,u) L and 
(ii) for every finite $ with irreflexive root u, a*($, 2), _L) € L iff ($,u) ^ L, 
(afijO) ^ L and ^ L- 
Proof (i) is proved similarly to Theorem 11.15. Details are left to the reader, 
(ii) If _L) € L then none of (#, u), (#1,0) and validates 
L, since all of them are quasi-reducible to (#,u) and so, by the refutability 
criterion, refute a* (#,2), -L). 
To prove the converse suppose that a frame 0 = (V, 5, Q) with actual world 
w (which is the root of 0) refutes a*(#, 2),_L) and show that (0,iu) ^ L. By 
the refutability criterion, there is a cofinal quasi-subreduction / of 0 to # such 
that f{w) — u. Consider the set U = f~x{u) € Q. Without loss of generality we 
may assume that U = U[. There are three possible cases. 
Case 1. The point w is irreflexive and {w} € Q. Then the restriction of / to 
dom/ — (U — {w}) is a cofinal subreduction of 0 to # satisfying (AWC) and so, 
by the refutability criterion and Theorem 9.21, (0, w) L. 
Case 2. There is a subset X C U such that w e X e Q and, for every ieI, 
there exists y € X Pi x\. Then the restriction of / to dom/ - (U — X) is clearly 
a cofinal subreduction of 0 to satisfying (AWC) and so again (0,w) L. 
Case 3. If neither of the preceding cases holds then, for every X C U such 
that w € X e_<2, the set Dx = X — X[ of dead ends in X is a cover for X, 
i.e., X C Dxi, and w e X — Dx € Q. Indeed, since Case 1 does not Jiold, 
w Dx, for otherwise {tu} = Dx € Q. And if we assume that X — Dx 1 ^ $ 
then Y = (X - Dxi)| C U, w € Y € Q and Y — Yj, i.e., Case 2 holds, which 
is a contradiction. Put 
Xq = Du, • • •, Xn+1 = Dc/_(Xou...ux„)» • • 
,xu = u- (J*c- 
Z<U> 

QUASI-NORMAL SUBFRAME AND COFINAL SUBFRAME LOGICS 393 
Each of these sets, save possibly is an antichain of irreflexive points and 
belongs to Q. Besides, X^ C Xn[ = Un<$<w ^ f°r everY n <(^<u. Therefore, 
the map g defined by 
ifxeV-U 
if x G X%, 0 < £ <u> 
is a cofinal quasi-subreduction of 0 to 3^+1)* satisfying (AWC). 
Suppose for definiteness that L is represented in the form (11.1). Since 
does not validate L, it refutes at least one of its axioms, and again 
we have to consider three possible cases. 
(a) #(L+i)* ^ <*(3i) f°r some i G /, i.e., there is a subreduction h of 3^+!)* 
to Since {u} P^+i)*, either u # domh or the root h(u) of Si is reflexive. 
Then the composition hg is a subreduction of 0 to Si, from which 0 a(Si) 
and so (0,w) □a(3ri), i.e. (0,w) L. 
(b) (3&+1).,u;) oc(Sj) for some j G J, i.e., there is a subreduction h of 
^(L+i)*3j satisfying (AWC). Then h(u) is reflexive and so hg is a subreduction 
of 0 to Sj satisfying (AWC). Therefore, (0,w) &{Sj)- 
(c) (3 (L+i)*’^) ^ a*(3fc) f°r some k € K, i.e., there is a quasi-subreduction 
h of 3^+1)„ to 3rfc satisfying (AWC). But then hg is a quasi-subreduction of 0 
to Sk satisfying (AWC), whence (0,w) a* (3*) and (0,w) L. 
Thus, every frame with actual world refuting a*(3r, ©, -L) is not a frame for 
L, which means that a*(3r,©, _L) G L. □ 
Corollary 11.34 A// subframe and cofinal subframe quasi-normal logics above 
S4 are finitely approximate. 
Example 11.35 As an illustration let us use Theorem 11.33 to characterize 
those normal and quasi-normal canonical formulas that belong to Solovay’s logic 
S. 
Clearly, either a(o) or a(#) is refuted at the root of every rooted Kripke 
frame. So all normal canonical formulas are in S. Every quasi-normal formula 
a*(3r,2),_L) associated with S containing a reflexive point is also in S, since 
□a(o) is refuted at the roots of 3r, S\ and 3(£,_f_i)*- But no quasi-normal formula 
a*(3,©,-L) built on irreflexive S belongs to S, because 3(£,+1)«. |= a(o) (for 
3(L+i)* contains neither an infinite ascending chain nor a reflexive point) and 
(3^+1)*-^) b <*(•), since {w} £ P^+iy- 
The obtained characterization together with the completeness theorem for 
the canonical formulas provide us with another decision algorithm for S. Notice 
also that incidentally we have proved the following completeness theorem for S. 
Theorem 11.36 S is characterized by the class 
{(zt+iy , : 3: is a finite rooted irreflexive frame}. 

394 
FINITE APPROXIMABILITY 
Theorem 11.33 reduces the decision problem for a logic L in QST or QCST 
to the problem of verifying, given a finite frame 3r with root u, whether or not the 
frames (#,11), (3^,0) and ^3(£,+1)«.,^ refute at least one axiom of L. The first 
two frames present no difficulty for a finitely axiomatizable L. And our aim now 
is to show that the condition ^3(^+1)*,^ ^ L can also verified in finitely 
many steps. 
Lemma 11.37 Suppose L is a quasi-normal (cofinal) subframe logic represented 
in the form (11.1) (respectively, (11.2)^ and 3 = (W,R) is a finite frame with 
irreflexive root u. Then ^ L iff one of the following conditions is 
satisfied: 
(i) 37 is (cofinally) subreducible to 3z for some i G I and some £ < 13^1; 
(ii) for some j G J, $j has a reflexive root and 3r is (cofinally) subreducible 
to 3j; with (AWC) being satisfied; 
(iii) 3^r is (cofinally) quasi-subreducible to 3rfc for some k G K and some 
£ < |3fc|, with (AWC) being satisfied. 
Proof Let us suppose for definiteness that L is represented in the form (11.2); 
the form (11.1) is considered analogously. 
(=$►) If 3(£,+i)* «(3rz» -L) for some i G /, then there is a cofinal subreduction 
/ of 3^+1)* to 3r». The map 
/ x f f(x) if x belongs to a final cluster in f~1(f(x)) 
' \ undefined otherwise 
is also a cofinal subreduction of 3(^+i)* to 3rz, with p(£) ^ g(C) for any distinct 
£,£ < u>. Let 3r/ be the result of removing from 3r([,+1). all those points £ < u 
that are not in domp. Clearly, 3r/ is isomorphic to 3^r for some ^ < |3z| and g is 
a cofinal subreduction of 3r/ to 3rz- 
If (^(L+i)*’^) V2 a(3j-,-L) for some j G J, then there is a cofinal 
subreduction / of 3([,+1)* to 3) satisfying (AWC). Since {u} £ P(w+i)*, the root 
v = f(u>) of 3 j is reflexive and so f~1(v) contains a reflexive point which belongs 
to W — {u}. But then the map 
g(x) = lf{x) if*e 
w if x — u 
is a cofinal subreduction of 3r to 3j satisfying (AWC). 
Finally, if ^3([,+1)*,^ a*(3fc, -L) for some k G K, then there is a cofinal 
quasi-subreduction / of 3(£,+1)* to 3rfc satisfying (AWC). Let v be the root of 3te- 
By the definition of 3^+!)., every X G -P^+i)* containing to also contains some 
£ < u;. Let £ be the minimal number such that f(() = v. Then the map 

THE METHOD OF INSERTING POINTS 
395 
{v if x = C 
f(x) if x belongs to a final cluster in f~1(f(x)) 
undefined otherwise 
is a cofinal quasi-subreduction of 3l{+\ to 3 k satisfying (AWC). It remains, as we 
have already done before, to remove from all those points £ < £ that are 
not in domp, thus obtaining a frame which is isomorphic to some 3|r, £ < |3fc|, 
and cofinally quasi-subreducible by g to 3k with g(£ - 1) = v. 
(<=) If the first condition holds then refutes □a(3ri,_L). The 
cofinal subreduction / of the second condition can be extended to the map 
//(*) XxeW-{u} 
9K) \v ifx = £<u 
(v is the reflexive root of 3j) which is a cofinal subreduction of 3*^+1)* to 3j with 
g(u) = v, and hence a(3rJ-,±). And the third condition gives in 
the same way a cofinal quasi-subreduction of 3^+1)* ^fc satisfying (AWC), 
from which ^ a*($k,-L)- □ 
As a consequence of Theorem 11.33, Lemma 11.37 and the completeness 
theorem for the canonical formulas we obtain 
Theorem 11.38 All finitely axiomatizable subframe and cofinal subframe 
quasinormal logics are decidable. 
It is not hard also to give a frame-theoretic characterization of the classes 
QST and QCST similar to Theorem 11.21. Let us say that a frame 3 with actual 
world u is a (cofinal) subframe of a frame 0 with actual world w if 3 is a (cofinal) 
subframe of 0 and u = w. 
Theorem 11.39 L is a (cofinal) subframe quasi-normal logic iff L is 
characterized by a class of frames with actual worlds that is closed under (cofinal) 
subframes. 
Proof Exercise. □ 
11.5 	The method of inserting points 
We conclude this chapter with two more sufficient conditions for finite approx- 
imability. Unlike the results of the two preceding sections, they concern logics 
whose canonical axioms may contain closed domains. 
The first condition is based upon the observation that no subreduction can 
map a reflexive point to an irreflexive one and also upon the following: 
Lemma 11.40 Suppose a(3r, Q, _L) and a(0, 0, _L) are canonical formulas such 
that 
• there is a cofinal subreduction f of 0 to 3 satisfying (CDC) for ® and 

396 
FINITE APPROXIMABILITY 
• an antichain e C dom/t is in 0 whenever /(e|) = for some D G D. 
Then a(0, 0, 1)gK4® a(S,33, ±). 
Proof Let # be a frame refuting a(0, 0, _L). Then there exists a cofinal 
subreduction g of 9) to 0 satisfying (CDC) for 0. We show that the composition 
h = /p, which is a cofinal subreduction of fj to S, satisfies (CDC) for £). 
Suppose D G £), x G dom/it and h(x |) = D]\ Let e be an antichain in 0 
such that g(x|) = e]\ Then we have e C dom/t, /(eT) = and so e G 0. 
Therefore, by (CDC), x G domg. But then g(x) G dom/| and f(g(x)T) = Dt> 
since p(x|) = g(x)|. So by (CDC), g(x) G dom/ and hence x G dom/i. Thus, h 
satisfies (CDC) for 2), which implies 9) a/#,2),_L). Since 9) was an arbitrary 
refutation frame for a(0,0,_L), it follows that a(0,0,_L) G K4®a(5,D,l). 
□ 
Remark In the proof above we did not use the cofinality condition. 
Consequently, Lemma 11.40 will remain true if we replace a(Sr,D, _L) and a(0, 0, _L) 
in it with a(Sr, D) and a(0, 0), respectively, and regard / as a plain subreduction. 
Theorem 11.41 A logic 
L = K4 0{a(&,2)*,-L) : * G 1} 0 {a(SrJ-, Dj) : j G J} 
is finitely approximate provided that either 
(i) for every i G / U J, all points in Si ote irreflexive 
or 
(ii) for every i G IU J, all points in Si ore reflexive. 
Proof (i) Suppose that all points in Si, for every i G / U J, are irreflexive 
and a(0,0,_L) is an arbitrary canonical formula. We construct from 0 a new 
finite frame 9) by inserting into it new reflexive points. Namely, suppose e is an 
antichain in 0 such that e ^ 0. Suppose also that Ci,..., Cn are all the clusters 
in 0 such that e C Cf\ and e fl C* = 0, for i = 1,..., n, but no successor of CV in 
0 possesses this property. Then we insert in 0 new reflexive points xi,..., xn so 
that each X* could see only the points in e and their successors and could be seen 
only from the points in Ci and their predecessors. The same we simultaneously 
do for all antichains e in 0 of that sort. The resulting frame is denoted by 9) 
(see Fig. 11.6). Since no new point was inserted just below an antichain in 0, 

THE METHOD OF INSERTING POINTS 
397 
the inversion of the natural embedding of 0 in 9) is a cofinal subreduction of 9) 
to 0 satisfying (CDC) for <£. So 9) ft a(0, (£, _L). 
Suppose now that a(0, <£,±)$L and show that 9) is a frame for L. If this 
is not the case then either 9) -L)» for some i G I, or 9) ft a(Sj,3)j), 
for some j G J. We consider only the former case, since the latter one is treated 
similarly. 
Thus, we have a cofinal subreduction / of 9) to Si satisfying (CDC) for 
Since all the points in Si are irreflexive, no point that was added to 0 belongs 
to dom/. So / may be regarded as a cofinal subreduction of 0 to Si satisfying 
(CDC) for 2)*. We clearly may assume also that the subframe of 0 generated by 
dom/ is rooted (for otherwise we can take a suitable restriction of /). 
Let e be an antichain in 0 belonging to dom/| and such that /(e|) = for 
some D G 2)*. If e ^ (£ then there is a reflexive point x in 9) such that x G dom/f 
and x sees only e| and, of course, itself. But then f(xT) = /(e|) = and so, by 
(CDC), x G dom/, which is impossible. Therefore, e G (£ and so, by Lemma 11.40, 
a(0, <£, _L) G L, contrary to our assumption. 
Thus, if a(0, <£, _L) & L then the finite frame 9) validates all the axioms of L 
and refutes a(0, (£, _L), which means that L is finitely approximable. 
(ii) Once again, given a canonical formula a(0, (£, _L), we construct in the 
same way the frame 9j, the only difference being that this time we insert into 0 
not reflexive but irreflexive points. And again we clearly have 9) )/=■ a(0, (£, _L). 
Suppose now that 9) a/fo,©*, ±) for some i G /, i.e., there is a cofinal 
subreduction / of 9) to Si satisfying (CDC) for ©*. The difference between this 
case and (i) is that now new irreflexive points may belong to dom/. But if x 
is such a point and f(x) = y then there is z G x| such that f(z) = y, since 
y is reflexive. So there must be a reflexive point z in 0 such that z G x| and 
f(x) = f(z), for otherwise we could construct an infinite chain of irreflexive 
points in 9), contrary to its finiteness. Therefore, the restriction of / to 0 is a 
cofinal subreduction of 0 (as well as of 9f) to Si satisfying (CDC) for ©*. The 
situation now is the same as in the previous case and so we are done. □ 
Example 11.42 According to Theorem 11.41 (i) the logic 
is finitely approximable. However, Artemov’s logic A* = L 0 GL = L 0 a(o) 
does not enjoy this property, because the formula a( ) is separated from it by 
the frame shown in Fig. 11.7, but every finite irreflexive frame refuting a( ) 
refutes a( , {{1}, {1,2}}) as well. So the finite approximability is not in 
general preserved under sums of logics. 

398 
FINITE APPROXIMABILITY 
I 
I 
V 
Fig. 11.7. 
The scope of the method developed above is not bounded only by canonical 
axioms associated with homogeneous (i.e., irreflexive or reflexive) frames. Now 
we use the technique of inserting new points to prove that every normal extension 
of K4 with modal reduction principles is finitely approximable. 
We remind the reader that a modal reduction principle is a formula of the 
form Mp —» Np, where M and N are strings of □ and O. By Exercise 3.15, 
every modality Mp is equivalent in K4 to a formula having one of the following 
six types: 
□nODp, UnOp, Unp, OnDOp, OnDp, Onp. 
Using this fact, K4’s formulas Up —> D2p, 02p —> Op and the equivalences of 
Exercise 3.15, we prove 
Lemma 11.43 For every set T of modal reduction principles there is a finite 
subset ACT such that K4 ®T = K4 0 A .In other words, every normal 
extension of K4 with modal reduction principles is finitely axiomatizable. 
Proof If T is infinite then it contains infinitely many modal reduction principles 
of the same type. Suppose, for instance, that the set E of all formulas in T of 
the type 
<£>(n,ra) = OnUp —> □mOp, 
for m, n > 0, is infinite. Define a partial order < on E by taking 
ip(n, m) < <p(k, l) iff n < k and m <1. 
Clearly, the set © of minimal elements in E with respect to < is finite. We show 
that K4 0 E = K4 0 0. Suppose y?(fe, l) G E. Then there is <£>(n, m) G 0 such 
that <p{n,m) < <p(k,l). Using Up —> U2p and O2p —> Op, it is not hard to 
construct a derivation of UlOp in K4 from the assumptions ip(n,m) and OkUp. 
Hence K4 0 E C K4 0 0. The converse inclusion is trivial. In the same way we 
consider the other modal reduction principles whose premises begin with O and 
conclusions with □. 
Suppose now that we have an infinite set E of formulas of the type * 
(p(n,m) = UnOp —► O771 Up. 

THE METHOD OF INSERTING POINTS 
399 
Since <p(n, m) is refuted in any frame with dead ends, D4 C K4 0 <p(n, m) and 
so 
□ (p -> q) -> (Dp -> Oq) € K4 0 <p(n, m). (11.3) 
Again, let © be the set of minimal formulas in E with respect to < defined 
above. As before, to prove K4 0 E C K4 0 © we take ip(k,l) € E and choose 
<p(n,m) € © such that <p(n,m) < <p(fc,/). Using (11.3) we derive from <p(n,m) 
a formula ip(kfJ') > ip(k,l). Then, assuming mfcOp, we ascend to Uk Op, get 
O1'Up and descend to 0*Dp. The rest types of modal reduction principles of the 
form UMp —* ONp are treated in exactly the same way. 
If T contains an infinite subset E of formulas of the type 
<p(n, m) = DnOp —* Dmp, for n > m, 
then, as in the previous case, we have K4 0 E = K4 0 ©, where © is the (finite) 
set of minimal elements in E with respect to <. To prove this it suffices to show 
that, for every k > n > m, 
<p(fc, m) € K4 0 <p(n, m). (11.4) 
Observe first that <p(n + (n - m), n) € K 0 (p(n, m), which together with 
Exercise 3.15 yields ip(n + (n — m), m) € K4 0(p(n, m). Therefore, in view of n > m, 
we can find l > k such that <p(l,m) € K4 0 <p(n,m) and then, using the axiom 
of K4, easily derive (11.4). 
Finally, if there is an infinite subset E C T of formulas of the type 
<p(n, m) = mnOp —> nmp, for n < m, 
then we define < on E by taking (p(n, m) < ip(k, l) iff n < fc, m < l and m — n< 
l — k and proceed as before. The remaining cases are considered analogously. 
□ 
Now let us elucidate the constitution of refutation frames for those modal 
reduction principles that are not DO-formulas. In the following lemmas we denote 
t1 
by the frame oO , by <£m the chain of m + 1 irreflexive points and by the 
set of all antichains in (£m. Cm denotes the (finite) class of all rooted 1-generated 
Kripke frames 0 such that 
• there is at most one reflexive point in 0 and it is of depth 1; 
• the longest chain of irreflexive points in 0 is of length m + 1. 
For m > n > 0, is the subclass of Cm whose frames 0 satisfy one more 
condition: 
• every chain of n + 1 irreflexive points has a reflexive successor in 0. 
Given 0 € Cm, we denote by £)b the set of all antichains D in 0 such that the 
subframe of 0 generated by D contains an irreflexive point of depth 1. 

400 
FINITE APPROXIMABILITY 
Lemma 11.44 (i) If n> m> 0 then 
K4 © nnOnp -► Dmp = K4 0 a(9t, 1) © {a(0, 2>\ 1) : 0 € Cm}. 
(ii) Ifm>n> 0 then 
K4 © □nODp -> □ mp = K4 © a(9t, 1) © {a(0, 1) : 0 € C£}. 
(iii) If n> m> 0 then 
K4 © □ nOp -> = K4 © a((°°), 1) © a(9t, 1) © {a(0, 1) : 0 € Cm}. 
(iv) If m > n > 0 then 
K4 © □ nOp -» □ mp = K4 © a((°°), 1) © a(9t, 1) © {a(0, S1”, 1) : 0 € C"}. 
(v) If n> m> 0 
K4 © □> —» Omp = K4 © 
Proof (i) Suppose CPODp —> Dmp is refuted under a valuation 23 at the root of 
a refined frame 3r = (W, P, P), generated by the set 23(p), and show that 3r also 
refutes one of the axioms in the right-hand part of the equality to be established. 
Consider two cases. 
Case 1. There is a cofinal subreduction of 3r to fH. Then # a(9t, J_). 
Case 2. Assume now that 3r is not subreducible cofinally to fH. Then # contains 
at most one reflexive point of finite depth and it is of depth 1. Indeed, it follows 
from our assumption that every reflexive point x of finite depth > 1 has an 
irreflexive successor y of depth 1. But then, since x f= DO Dp, we must have also 
y |= ODp, which is impossible. So all reflexive points of finite depth, if any, lie 
at depth 1, and since p is true at all of them and J-1 is a generated subframe 
of there exists at most one point of that type. 
In this situation, to refute □nODp —> D^p the frame 3r must contain at least 
one chain of ra + 1 irreflexive points. Take a minimal generated subframe 0 of 
3 containing such a chain. Then clearly we have 0 € Cm and 3r ^ a(0, £)b, ±). 
Thus we have proved that 
K4 © □"ODp □ mp C K4 © a(«H, 1) © {a(0,£1\ 1) : 0 € Cm}. 
To establish the converse inclusion, suppose first that a frame 3r refutes a(9t, _L). 
This means that there is a cofinal subreduction / of # to Without loss of 
generality we may assume that / is a reduction of a generated subframe of 3 to 
Define a valuation 23 in 3r by taking 23(p) = /-1(1). Then it is easy to check 
that x OnOOp —> □ mp, for every x £ /-1(0). 
Suppose now that $ ^ _L), for some 0 e Cm. Then without loss 
of generality we may assume that there is a cofinal subreduction / of 3 to 0 

THE METHOD OF INSERTING POINTS 
401 
satisfying (CDC) for & and such that the root y of # is in dom/. Let ao,..., am 
be a longest chain of irreflexive points in 0. Clearly, f(y) = ao. Define a valuation 
in # so that x ft p iff x G and prove that then we shall have y ft 
□nODp —> □ mp. Notice first that y ft an(3 so it suffices to show that 
y |= DnODp. Suppose otherwise. Then there is an ascending chain y, yi,..., yn 
such that yn ft OD p. Since n> m and by (CDC), this is possible only if /(ynT) 
contains the reflexive point in 0 (for otherwise yi,... ,yn are irreflexive points 
in dom/ and so /(yi),..., f{yn) is a chain of irreflexive points in 0). But then 
yn [= ODp, which is a contradiction. 
The remaining items are proved analogously; we leave them to the reader as 
an exercise. □ 
For points x and y in a frame # = (W, R) such that xRy, let 
i(x, y) = sup{fc + 1 : 3xi,... ,x* G IF xi?xi... i?x^i?y}. 
If there are arbitrarily long chains (of not necessarily distinct points) connecting 
x and y, in particular, if x or y or a point between them is reflexive, then 
l(x,y) = oo. 
It is not hard to see that the following lemma holds. 
Lemma 11.45 For every Kripke frame $ ft a(0m,®m) iff there are points 
x and y in $ such that m < i(x, y) < oo. 
The crucial step in establishing the finite approximability of logics whose 
axioms are modal reduction principles is 
Lemma 11.46 Every logic L G NExtK4 axiomatizable by modal reduction 
principles of the types DnODp —> □ mp, DnOp —> □ mp, □ np —> Dmp is finitely 
approximable. 
Proof We use virtually the same technique of inserting reflexive points as in 
the proof of Theorem 11.41. 
By Lemma 11.44, L can be axiomatized by canonical axioms of the form 
a(9t, _L), a(R, -1), a(0,Db,_L) and a(0m,®m) (where 0 G Cm, for some m). 
Fix such an axiomatization. By Theorem 11.41 and Lemma 11.44, L is finitely 
approximable if all its axioms are of the form □ np —> Dmp. So let us assume that 
L D K4 0 a(9t, _L). Take an arbitrary canonical formula a(i^, 0, ±). 
For every antichain e in S) such that e 0 and e| contains an irreflexive 
point of depth 1, we insert new reflexive points between e and its immediate 
predecessors in the same way as was done in the proof of Theorem 11.41. We are 
going to show now that either a(fi, 0,1) G L or the constructed finite frame— 
call it —separates a(f), 0, _L) from L. Clearly $)f ft a(f), 0, _L). So if S)' |= L 
then we are done. Suppose $jf is not a frame for L. Then three cases are to be 
considered. 
Case l. ft ft a(91, -L), i.e., there is a cofinal subreduction / of ft to 9t. Then 
P) is also cofinally subreducible to 9t, because every new reflexive point has an 
irreflexive successor of depth 1 and so cannot belong to dom/. By Theorem 11.15, 

402 
FINITE APPROXIMABILITY 
it follows that a(fj, 0, ±) G L. For the same reason, if a(©, ±) is an axiom of 
L and ft a(©, 1) then a(9), 0, ±) G L. 
Case 2. Suppose that a(0,2)b,±) is an axiom of L, for some 0 G Cm, and 
ft ^ a(0,®b, ±). This means that there is a cofinal subreduction / of to 0 
satisfying (CDC) for ®b and such that the subframe of ft generated by dom/ 
is rooted. Since the only reflexive point in 0, if any, is of depth 1, no new 
reflexive point is in dom/ and so the map / may be considered as a cofinal 
subreduction of 9) to 0 satisfying (CDC) for 2)b. Let e be an antichain in 9) such 
that e C dom/t and /(e|) = D|, for some D G 2)b. Since for every closed domain 
D G 2)b, contains an irreflexive point of depth 1 in 0, e| must also contain a 
final irreflexive point. So if e ^ 0 then there is a reflexive point in ft just below 
e, contrary to / satisfying (CDC) for 2)b. Hence e G 0 and, by Lemma 11.40, 
a(i}, 0, _L) G L. 
Case 3. If ft a(0m,©5ri) then, by Lemma 11.45, there are points a and 
b in 9) such that l(a,b) = m in both 9) and ft. By the construction of ft, this 
means, in particular, that every antichain e C a|, having a point in 6j, is in 0 
whenever e| contains an irreflexive point of depth 1. Using our assumption that 
a(91, ±) G L, we show that in this case a(9), 0,1) G L as well. 
Suppose otherwise. Since 
K4 0 □nODp -> Dmp = K4 0 Omp -> OnDOp, 
L is a Sahlqvist logic. So it is D-persistent and there is a finitely generated refined 
frame such that its underlying Kripke frame $ = (W, R) validates L and refutes 
a(i3, 0, ±). Let h be a cofinal subreduction of # to 9) satisfying (CDC) for 0. Our 
aim now is either to subreduce cofinally # to 91 or to find points x, y in $ with 
m < i(x, y) < oo, which will mean that either $ )/= a(9l, _L) or # a(0m, 2)^). 
Let us consider first the maximal generated subframe of # whose final 
points are reflexive. If there is a reflexive point of depth > 1 or an infinite 
ascending chain of irreflexive points in then clearly # is cofinally subreducible 
to 91. So suppose this is not the case. If there is a point in of depth > m + 1 
then, by Lemma 11.45, we are done. 
Thus y is of depth < m + 1. We show that, for every x G /i_1(a), there 
is y G /i_1(6) fl x| such that m < l(x,y) < oo. Take any x G h~1(a). By the 
definition of subreduction, we clearly must have some y G ft-1 (6) fl x] with 
m < Z(x, y). Suppose Z(x, y) = oo. Then there is a chain xRxi... RxnRy such 
that all Xi are not in $ and n exceeds the number of points in 9). Let e* be 
an antichain in 9) such that h(x{ |) = e* T- Since X{ sees an irreflexive point of 
depth 1, a also sees or contains such a point and so e* G 0. Therefore all are 
in dom/i, which is possible only if h(xi), for some i, is reflexive, i.e., we have' a 
reflexive point between a and b. But then Z(a, b) = oo, which is a contradiction. 
In fact, the modal reduction principles that do not belong to the scope of 
Lemma 11.46 either axiomatize logics of finite depth or are deductively equal to 

THE METHOD OF INSERTING POINTS 
403 
□O-formulas. This follows from the next two lemmas. 
Lemma 11.47 For every n > 0, K4 0 OnDOp —> □ mp, K4 0 OnDp —> □ mp 
and K4 0 Onp —> Dmp are logics of finite depth. 
Proof It is enough to show that the axioms of these logics are refuted in an 
arbitrary finite rooted frame £ of depth max{m, n} + 2. Define a valuation in 
such an £ so that x |= p iff x is of depth 1. It should be clear that under this 
valuation Dmp is false at the root 2 of By the definition, there is a point y of 
depth 1 which is accessible from z by n steps. And since y |= □ Op A Dp A p, it 
follows that 2 |= OnDOp A OnDp A Onp. □ 
Lemma 11.48 (i) For evety n, ra > 0, 
K4 0 DnODp -> Omp =K4 0 nnOp -> Omp = K4 0 □ np -> Omp = 
K4 0 <*(•, 1) = K4 0 OT = D4. 
(ii) For every n, m > 0, 
K4 0 □ np -> DmODp = K4 0 □ np -> DmOp = K4 0 DmOT. 
Proof (i) follows from the obvious fact that the modal reduction principles 
under consideration are refuted by frames with dead ends and validated by finite 
serial frames. 
(ii) We prove only the latter equality Clearly, it is sufficient to show that 
□np DmOp € K4 0 DmOT. 
Since the logic K4 0 DmOT is finitely approximable, we take a finite frame £ 
for it and prove that £ \= QTlP —^ DmOp. Suppose otherwise, i.e., under some 
valuation x (= Dnp and x ^ DmOp, for some x in Then there is a point y of 
depth 1 accessible from x by m steps and such that y ^ Op. Since y |= □ np, y is 
irreflexive. But then we must have x ^ DmOT, which is a contradiction. □ 
Now we have everything we need to prove 
Theorem 11.49 Every logic L e NExtK4 axiomatizable by modal reduction 
principles is finitely approximable and decidable. 
Proof Observe first that 
K4 0 Omp -> OnDOp = K4 0 nnonp nmp, 
K4 0 DnODp -> OmDp = K4 0 DmOp -> OnDOp, 
etc. So L is (finitely, by virtue of Lemma 11.43) axiomatizable by modal reduction 
principles mentioned in Lemmas 11.46, 11.47 and DO-formulas (OT, as well as 
any other variable free formula, is also a DO-formula). The claim of our theorem 
follows then from Lemmas 11.46, 11.47 and Theorems 11.13, 8.85. □ 

404 
FINITE APPROXIMABILITY 
11.6 	The method of removing points 
Unlike Theorem 11.41 and Lemma 11.46, the sufficient condition of the finite ap- 
proximability to be obtained in this section is proved by the more conventional 
technique of removing points from, say, universal models. Such a technique was 
used in the selective filtration method and Fine’s method of maximal points 
(Section 10.4). Another example of that sort is the method of step-wise refinement 
with removing E-remaindered points, exploited in the proof of Theorem 9.34, 
which actually establishes the finite approximability of cofinal subframe logics. 
Here we are going to tune this method by adopting a subtler strategy of removing 
points to cover a wider class of canonical axioms with a rather complex structure 
of closed domains. 
Suppose we have a logic 
L = K4©{a(<5*,2h,±):ie/} 
and a canonical formula a = a(i},<£,J_) which is not in L. Then there exists 
a rooted frame 3 = (W,R,P) for L such that 3 ^ a, i.e., there is a cofinal 
subreduction ft of 3 to S) satisfying (CDC) for <£. Construct the countermodel 
97t = (£,9?) for a as it was done in the proof of Theorem 9.39. Without loss of 
generality we may assume that 
• domftt = domftj = W\ 
• if a is a reflexive point in 9) then a point x £ W is in ft'1 (C(a)) whenever 
h(x T) = at; 
• 3 is generated by the sets %3(pi), Pi a variable in a. 
Let E = Suba. It is easy to check that all points x, y domft such that ft(x|) = 
ft(yf) are E-equivalent in 971. Now we construct a sequence 
3Ho = 3K,..., 3R< = <&, ®<), aK*+i = (&+1, ®<+i), - • • 
of models in almost the same way as in the proof of Theorem 9.34. The only 
difference concerns removing points. Suppose we have already constructed 97U 
and its reduct [971*] (we use the same notations as in the proof of Theorem 9.34). 
Now we throw away points of two sorts. 
First, for every proper cluster C of depth i + 1 such that some x £ C is 
E-remaindered in [fo]-1, we remove from C all the points except x. It should be 
clear from the construction of 971 that every removed point is also E-remaindered 
in [fo]-1 and that the set of all such points is in [Pi]. Let [971J] = ([3*], [9JJ]) be 
the resulting submodel of [971*]. 
Second, we call a point x in [W/]>t+1 redundant in [97tj] if it is E-remaindered 
in [3*]-z+1 and, for every j G I and every cofinal subreduction g of [3^]-z+1 to 
the subframe of <&j generated by some U £ Sj such that U C g{x|) and g satisfies 
(CDC) for 3)j, there is a point y £ x\ in such that <7(2/T) = Let 
X be the maximal set of redundant points in [971J] which is upward closed in 
[W7]>1+1. Since is finite and every point in it is an atom, it is not hard 

THE METHOD OF REMOVING POINTS 
405 
to see that X G [P/] (this is left to the reader). We define = (5t+i,2J»+i) 
as the submodel of [3DTJ] induced by the set of points in [£'] different from those 
in X. 
It should be clear that 9Jli (and hence 9Jto) is E-subreducible to and 
so 1 a. Besides, as follows from the definition of redundant points, if 
5i+i ^ a(0j,Sj,.L), for some j G /, then 5i ^ a(0j,Sj,J_). Hence 5i+i \= L. 
So the finite approximability of L will be established if we manage to prove 
that our modified process of refining and removing eventually terminates (i.e., 
= 0 for some i > 0). 
It is not hard to see that for some 5> L and a the process never stops, even 
though L is finitely approximable. On the other hand, there are many axioms 
a(0, S, J-) such that too deep points in fo cannot be mapped to points in closed 
domains in S by cofinal subreductions to 0, which induces eventual halting of 
the process. Here is a simple example illustrating this phenomenon. 
Example 11.50 Let L be the smallest modal companion of the Scott logic SL, 
2o 
1 I 
i.e., L = S4 © a(0, {{1,2}}, _L), where 0 is the frame o . Suppose also that 
a = a(i}, 0, ±) ^ L, 5 separates a from L and that our “algorithm”, when being 
applied to 5, & and L, works infinitely long. Then the frame 5a; = (Ww,^w)> 
where 
Wu = (J w?, Ru = U Rr> 
0 <i<uj 0 <i<uj 
is of infinite depth. By Konig’s lemma, there is an infinite descending chain 
. . . XiR^Xi—l • • • RijjXQ'RijjXx 
in So; such that Xi is of depth i, for every i < to. Since there are only finitely 
many pairwise non-E-equivalent points in 3DT, there must be some n > 0 such 
that, for every k > n, each point in C(xk) is E-remaindered in 5^k. And since 
5p is finite, there is m > n starting from which all Xi see the same points of 
depth 1. 
Let us consider now the frame 5m and ask ourselves why points in the m- 
cyclic set X, folded at step m + 1 into C(xm+i), were not removed at step m. 
X is upward closed in W>m and every point in it is E-remaindered in 5^m- So 
the only reason for keeping some x G X in the frame is that 5^m is cofinally 
subreducible to 0-1, x sees inverse images of both points in 0-1 but none of its 
successors in 5^m does. By the cofinality condition, these inverse images can be 
taken from 5p- But then they are also seen from £m, which is a contradiction. 
Thus sooner or later our algorithm will construct a finite frame separating L 
from a, which proves that both L and SL are finitely approximable. 

406 
FINITE APPROXIMABILITY 
Theorem 11.52 to be proved below is based essentially upon the same idea as 
Example 11.50, though it uses a more sophisticated construction. To formulate 
it we require some new notions. 
A point i in a frame 0 is called a focus of an antichain a in 0 if x a and 
xt = {#} U a|. 
Suppose 0 is a finite frame and 2) a set of closed domains in 0. Define by 
induction on n the notions of an n-stable point in 0 (relative to 2)) and an n- 
stable antichain in 2). A point x is 1 -stable in 0 iff either x is of depth 1 in 0 or 
the cluster C(x) is proper. A point x is n + 1 -stable in 0 (relative to 2)) iff it is 
not m-stable, for any m < n, and either there is an n-stable point in 0 (relative 
to 2)) which is not seen from £ or £ is a focus of an antichain in 2) containing 
an n — 1-stable point and no n-stable point. And we say an antichain D in 2) is 
n-stable iff it contains an n-stable point in the subframe 0' of 0 generated by U 
(relative to 2)) and no m-stable point in 0' (relative to 2)), for m > n. A point 
or an antichain is stable if it is n-stable for some n. 
It should be clear from the definition that if a point in an antichain is stable 
then the remaining points in the antichain are also stable. 
Example 11.51 (1) Suppose 0 is a finite rooted generated subframe of one of 
the frames shown in Fig. 11.8 (a)-(c). Then, regardless of 2), each point in 0 
different from its root is n-stable where n is the number located near the point. 
Every antichain D in 0, containing at least two points, is also n-stable, with n 
being the maximal degree of stability of points in U. 
(2) If 0 is a rooted generated subframe of the frame depicted in Fig. 11.8 
(d) 	and 2) is the set of all two-point antichains in 0 then every point in 0 is 
n-stable (relative to 2)), where n stays near the point. However, for 2) = 0 no 
point in 0, save those of depth 1, is stable. 
(3) If 0 is a finite tree of clusters then every antichain in 0, different from a 
non-final singleton, is either 1- or 2-stable in 0 regardless of 2). More generally, 
if no point in U sees all the points of depth 1 in D|, in particular, if U has no 
upper bound in 0, then U is also either 1- or 2-stable. Every antichain containing 
a point x with proper C(x) is 1- or 2-stable, as well, whatever 0 and 2) are. 
(4) Every antichain is stable in every irreflexive frame 0 relative to the set 
2)N of all antichains in 0. However, this is not so if 0 contains reflexive points, 
because reflexive singletons are open domains and do not belong to 2)11. For 
instance, the antichains {a} in o and {1,2} in are not stable. 
Now we are in a position to make a crucial step in the justification of our 
method. 
Theorem 11.52 Suppose L = K4 ® {a(0j,2)i,-L) : i e 1} and there is dr > 0 
such that, for any i € I, every closed domain D € 2)i is n-stable in 0* (relative 
to /8i), for some n < d. Then L is finitely approximable. 
? 
?fl 

THE METHOD OF REMOVING POINTS 
407 
(a) 
Proof It is enough to show that the algorithm defined above comes to a stop 
for every a = a(i}, <£, J_) ^ L and £ separating a from L. Suppose otherwise, i.e., 
given some a $ L and #, the algorithm works infinitely long. Then the frame 
defined as in Example 11.50, is of infinite depth. 
For each point x in 3u,, we denote by N(x) the number of pairwise non-E- 
equivalent points in x\. Since N(x) cannot exceed 2'EI, there exist k < 2^ and 
n\ > 1 such that, for every n > ni, contains at least one point x of depth n 
with N(x) = k and no point y of depth n with N(y) < k. Indeed, let ln be the 
minimal number N(x) among all x in of depth n. The sequence Zi, I2,... is 
clearly non-decreasing and so there must be ni such that all li starting from lni 
are the same. Then we can take k = lni. 
Put 
X\ = {xG W>ni : N(x) = k}. 
It follows from the given definition that every point in X\ is E-remaindered in 
W£ni and that if x € yj, for some x € X\ and y of depth > m, then y e X\. 
Now we define by induction an infinite descending sequence of non-empty 
sets X\ D X2 D ... and an infinite ascending sequence of integers n\ <ri2 < 
Let.Xr and nr be already defined and, for each x in 3^, let 
JVr(x) = |{2/e*T: yewj"'}|. 
Since Sr^7lr is finite, there exist k and nr+1 > nr such that, for each n > nr+1, 
Su, contains at least one point x € Xr of depth n with Nr(x) = k and no point 
y e Xr of depth n with Nr(y) < k. Then we put 
Xr+i = {xe W>n'+' : x e Xr and Nr{x) = k}. 
By transitivity, we obviously have that if 2; € y 1, for some x € Xr+i and 
y € Wu r+1, then y € Xr+i, with x and y seeing exactly the same points of 
depth < nr. 
Our construction is completed now, and we are ready to derive a 
contradiction. Take s = n^+i + 1, where d is the constant supplied by the assumption of 
our theorem, and consider an arbitrary point x € Xd+1 of depth s 4-1. The 
question leading to a contradiction is why the set Y, folded at step s + 1 into C(x), 

408 
FINITE APPROXIMABILITY 
was not removed at step s. Y is upward closed in W>s and its every point is 
E-remaindered in 3jni. So the only reason why a point y € Y was not removed 
at step s is that there exists a cofinal subreduction g of $fs to the subframe of 
some <&i generated by some U € 2)*, i € /, such that U C y(y|) and (CDC) for 
2)* is satisfied, but there is no 2 € y| of depth < s with U C g(z\). 
Let / be the restriction of g to yf. If should be clear that / is also a cofinal 
subreduction of $f8 to satisfying (CDC) for 2)*. 
By induction on r we show now that, for each r-stable point a (relative to 
2)i) in t>T and each u € /_1(a), there exists a point v € of depth < nr such 
that f(v) = a. In other words, this means that /-1(a) has a cover in $fnr. 
The point a is 1-stable iff it is of depth 1 or the cluster C(a) is proper. In 
the former case has a cover in 3p because / is cofinal. As for the latter 
case, observe first that since a point u € Xm, for m > 1, is E-remaindered in 
3^ni, the cluster C(u) cannot be proper. So, as follows from the definition of 
reduction, in the case when C(a) is proper /_1(a) also has a cover in $fni. 
Suppose our claim holds for points whose degree of stability in is < r, a 
is an r 4- 1-stable point in (relative to 2)*) and f(u) = a but u is of depth 
> nr+1. Since u e yt? we must have u e Xr+i. So u sees the same points of depth 
< nr as y, in particular, inverse /-images of all r-stable points in (relative to 
Si). But then a sees all r-stable points in Uf and so the only possibility for a to 
be r + 1-stable is to be a focus of an antichain e € S* whose points are at most 
r - 1-stable. By the induction hypothesis, u sees inverse /-images of all points 
in e located in 3^nr-1, and they are seen also from any successor v of u of depth 
nr+1, which certainly exists. But then, by (CDC), f(v) = a. 
Thus all the points in U have inverse /-images in $fnd- Take any point z € y| 
of depth s. Since z sees the same points of depth < rid as y, we must then have 
D C /(^T), which is a contradiction. □ 
Using the modal companion and preservation theorems we can transfer this 
result to si-logics: 
Theorem 11.53 If, for some d > 0, a logic L e Extint can be axiomatized by 
a (finite or infinite) set of intuitionistic canonical formulas /?(3,2), J_) in which 
every closed domain D € 2) is n-stable in 3 (relative to 2)J for some n < d, then 
L is finitely approximable. 
As an immediate consequence we obtain 
Corollary 11.54 If a logic L e NExtK4 (or L e Extint) is finitely axioma- 
tizable by canonical formulas a(3,2),_L) (or, respectively, /?(3,®,-L)J in which 
every U £ 2) is stable in 3 (relative to 2)), then L is finitely approximable and 
decidable. 
Example 11.51 shows a number of applications of these results. For instance, 
we get the following 
Theorem 11.55 Every normal extension of a cofinal subframe logic with 

THE METHOD OF REMOVING POINTS 
409 
• canonical formulas, every closed domain in which contains a point 
generating a proper cluster and/or 
• canonical formulas based upon reflexive trees of clusters and/or 
• a finite number of frame formulas based upon irreflexive frames 
is finitely approximate. 
Now we use Corollary 11.54 to prove that every normal extension of S4 with 
a formula in one variable is finitely approximate. To this end we require two 
lemmas. Until the end of this section we will assume all frames to be quasi-orders. 
A pair (a, b) of antichains in a frame 3 is called a cut of 3 if b consists of 
focuses for a and, for every point x in £, either x € a\ or x € bj. For example, 
every pair (a, b), where a and b contain the points labeled by n and n + 2, 
respectively, is a cut of the frame in Fig. 11.8 (d). 
Lemma 11.56 Suppose $ is a finite frame generated by an antichain D and 2) 
a set of antichains in 3 containing U. J/U is not stable in 3 relative to 2) then 
there is a cut (a, b) of 3 such that a ^ 2) and all clusters C(x), for x € b j, are 
simple. 
Proof Let b be a point in 3 such that it is not stable itself but has only stable 
immediate successors relative to 2). It must exist, since points in U are not stable, 
while the final points in 3 are stable. Take an antichain a for which b is a focus. 
Then, for any x in £, either x € a\ or x € aj. Indeed, suppose otherwise. Since 
x a|, x must be stable in 3, because the points in a are stable. And since 
x a|, we have also x & 6|, and so b must be stable, which is a contradiction. 
Let b be a maximal antichain of focuses for a containing b and let £ be a 
point in 3 such that x ^ a|. Then, as was shown above, x € a j —a. To prove 
that x e bj, suppose otherwise. Since no focus of a is accessible from x, there is 
a point y € x]—of which does not see all the points in a and so is stable. But 
this leads to a contradiction, since b does not see y and so must be also stable. 
Since b is a focus for a and not stable, a ^ 2). And if the cluster C(x), for 
some x £ bj, is proper then b must be 1- or 2-stable, contrary to its choice. 
□ 
Lemma 11.57 For every formula ip(p), one can effectively construct canonical 
formulas a(fo,2)i, 1), i = 1,... , n, such that 
S4©<^ = S4©{a(fo,S*,±) : t = l,...,n} (11.5) 
and every antichain in 2)* is stable in 3i relative to 2)*. 
Proof According to Theorem 9.34, the logic S4 © ip can be effectively 
represented in the form (11.5), with all ±) being associated with refined 
1-generated finite models DJli based on quasi-ordered frames 3i- We show that 
an arbitrary antichain U € 2)* is stable in 3i relative to 2)*. 
Suppose otherwise. Then, by Lemma 11.56, there is a cut (a, b) of the sub- 
frame 0 of 3i generated by a D € 2)* such that a ^ 2)* and the clusters in bj are 
simple. Consider two cases. 

410 
FINITE APPROXIMABILITY 
b\ 62 b\ 62 £>2 
(a) (b) (c) 
Fig. 11.9. 
Case 1: b contains only one point, say, b. Then, since Si is 1-generated and 
refined, b may have only one immediate predecessor, which in turn has at most 
one immediate predecessor, etc. In other words, bj is a chain in 0 and so D is a 
reflexive singleton, which is a contradiction. 
Case 2: b contains at least two points. In fact, in this case, since Si is 1- 
generated and refined and there are no proper clusters in b j, b consists of exactly 
two points, say, 61 and 62- Since a ^ 2)*, the antichain a is an open domain in 
SDli, which means that we can insert a new point x between a and b (see Fig. 11.9 
(a), (b)) and extend to it the valuation in Wli in such a way that the truth-values 
of all <p’s subformulas at all points in Si will remain the same as before. Without 
loss of generality we may assume that x f= p, 61 |= p and 62 ^ p. It follows that 
in the extended model x and 61 are Sub<p-equivalent and so we can draw an 
arrow from 62 to 61 in the model 9D% (see Fig. 11.8 (c)) without changing the 
truth-values of (p’s subformulas, i.e., for every point y in the resulting model 90^ 
and every 'ip € Sub<p, we shall have 
Let 91 be the submodel of 90^ generated by U and 91' the refinement of 91. 
Since 91 is finite and in view of Theorem 8.69, it is reducible to 91' by a reduction 
/. Clearly, the pair (/(a), {/(&i)}) is a cut of 91' and so we find ourselves in the 
framework of Case 1, i.e., /(6i)| is a chain in 91'. By the reduction theorem and 
the definition of open domains, it follows immediately that U is an open domain 
in 9DT*, which is a contradiction. □ 
As a consequence of Corollary 11.54 and Lemma 11.57 we obtain 
Theorem 11.58 Every normal extension of S4 axiomatizable by a finite number 
of formulas in one variable is finitely approximable and is decidable. 
Corollary 11.59 Every si-logic axiomatizable by formulas in one variable is 
finitely approximable and decidable. 
Proof Follows from Theorems 7.67,11.58 and the preservation theorem. □ 
Exercises 11.27 and 11.28 show that Theorem 11.58 is the best possible result 
as far as the number of variables in logics’ axioms is concerned. 

EXERCISES AND OPEN PROBLEMS 
411 
11.7 	Exercises and open problems 
Exercise 11.1 Show that for every formula p with md(p) < n there is a unique 
disjunction of normal forms of degree n which is equivalent to p (_L is assumed 
to be the empty disjunction). 
Exercise 11.2 Show that Op € S5 iff DOT —> DOp € K4. 
Exercise 11.3 Show that in general Theorem 11.13 does not hold if we add to 
L infinitely many DO-axioms. (Hint: consider the formulas 
ao = □<>p A nO-»r, fa = nOq A DO-t, 
oc\ = DO-i^ A -iDO-t A -iDO-ip, (3\ = DO-ip A -iDO-ir A 
<*n+2 = 0<*n+l A Of3n A ->0/3n+i, ftn+2 = <>Pn+i A Oan A -.Oan+i, 
Tn := A 0/3n+i A —'0(Xn+2 A “'0/3n^-2? 
6 = □ (aq —> Oao A -iO/?o) A □ (/3i —> 0/?o A -iOao), 
= ~1<^'7n—1 A A pn =6 > 0(^n > 
(see Fig. 6.5) and show that the logic Grz 0 {pn : n < u} is not compact.) 
Exercise 11.4 (i) A logic L = Lo+p (or L = Lo(&p) has the simple substitution 
property if for every tp(pi,... ,pn), £ L iff p\ A ... A <pm —> xjj € L, where 
<pi,..., <pm are all possible substitution instances of p obtained by replacing its 
variables by some of pi,... ,pn. Show that if Lq is finitely approximable then L 
is finitely approximable as well. 
(ii) Prove that if p is a conservative in NExtL formula (see Section 14,1) and 
L is finitely approximable then L 0 p is finitely approximable too. 
Exercise 11.5 Show that a logic L € NExt(S4 0bdn) has the simple 
substitution property iff \J i<j<rn n(Pi Pj) € L for some m. 
Exercise 11.6 Show that if a logic L € NExtS4 is finitely approximable then 
L 0 Grz is finitely approximable too. 
Exercise 11.7 Prove that (i) L is a cofinal subframe logic iff, for every canonical 
formula a(Sr, S, J_), a(#, _L) € L whenever a(#, 2), J_) € L, and that (ii) L is a 
subframe logic iff, for every a(3r, S, J_), a(#) € L whenever a(#, 2), J_) € L. 
Exercise 11.8 Show that (i) a(Sr,S, _L) € K40{a(fo, _L) : i € 1} iff «(?,£), _L) 
is in K40a(3ri, -J-) for some i € /, and that (ii) <*(#,2), _L) € K40{a(fo) : i € 1} 
iff a^,®, _L) e K4 0 a(fo) for some i € /. 
Exejrcise 11.9 Using Corollary 11.22 prove that if p is a Boolean combination 
of modalities then S4 0 p is finitely approximable. Does this result hold if we 
replace S4 by K4? 
Exercise 11.10 Prove that all logics in ExtS4.3 are finitely axiomatizable. 

412 
FINITE APPROXIMABILITY 
Exercise 11.11 Show that K4Z and Dum are not elementary, while K4H is. 
Exercise 11.12 Let 3 = {W.R) be a finite rooted frame and oo,...,an all 
the points in 3- With each a, in a non-final cluster or in a final one having no 
predecessors associate the individual variable xu and if the final cluster C(at) has 
the immediate predecessors C(aj),C(ak) then associate with a* the variables 
The variables thus associated with points in 3 will be denoted by x-, 
where s is either blank or 0 < s <n. Let 
= 3j/i. • .3yk(f\yi ± yj A R{x,y{) A R(yi, j/2) A ... A R(yk-i,yk)) 
(which means “x sees a chain of k distinct points”) and 
0(x) = ^3yR{x,y) V 3z{R(x,z) A -*3yR(z,y)) 
(which means “x is a final irreflexive point itself or sees such a point”). 
Define (/>$ to be the conjunction of the following formulas under all admissible 
values of their parameters: 
(0) R(xi,xSj): diRdj, s is either blank or s = i and the cluster C(a*) is not 
final in #; 
(1) -iR(xl,Xj): not diRdj; 
(2) xl ^ xlj\ j,0<i <j < n; 
(3) C(di) is a final non-degenerate cluster in £ containing k points; 
(4) -i3x /\a.eX R(x*,x): X is an antichain in # such that X = 0, where 
X = {y:X C ii}; 
(5) Vx(/\a.€X R(x*,x) —> t?fc(x)): X is an antichain in # such that all final 
clusters in X are non-degenerate and the smallest of them contains k > 1 points; 
(6) Vz(/\a.€X R(xf,x) —> tf(x)): X is an antichain in £ such that each final 
cluster in X is degenerate; 
(7) Vx(/\a,eX R(x?,x) —> tf(x) V $fc(z)): X is an antichain in S such that X 
contains both degenerate and non-degenerate clusters and k is the number of 
points in the smallest non-degenerate one. 
Prove that a Kripke frame 0 satisfies the formula </>$ iff # is cofinally quasi- 
embeddable in 0. 
Exercise 11.13 Show that every cofinal subframe logic is elementary on the 
class of finite frames. 
Exercise 11.14 Show that all subframe and cofinal subframe logics whose 
canonical axioms are built on irreflexive frames are elementary, and the cardinality 
of this class is that of the continuum. 
Exercise 11.15 Show that there is a continuum of cofinal subframe logics of 
depth 3. 

EXERCISES AND OPEN PROBLEMS 
413 
Exercise 11.16 Prove that every (cofinal) subframe logic can be axiomatized 
by an independent set of (cofinal) subframe formulas, and such an axiomatization 
is unique. 
Exercise 11.17 Prove that a logic in CSJ7 n NExtGrz is elementary iff it is of 
finite depth, and that the classes {L £ SJ7 : K4 CLC GL} and {L £ SJ7 : 
S4 c L C Grz} contain only non-elementary logics. 
Exercise 11.18 Given an intuitionistic disjunction free formula, construct a 
first order equivalent for it with the prefix of the form V3. 
Exercise 11.19 Prove that a (cofinal) subframe logic L is elementary iff, for 
every Kripke frame #, $ (= L implies # |= L. 
Exercise 11.20 Show that T = SNExtK/Log#, where SNExtK is the lattice 
of subframe logics above K. 
Exercise 11.21 Show that every subframe logic in NExtAltn is finitely 
approximate. 
Exercise 11.22 Let L = Alt3 ® p —> DOp ® Dq A ->q —> -•(Op A O-»p) and 
Xi = Qi A ~^q2 A -.g3, X2 = ^Qi A q2 A -.93, X3 = "'Qi A ~^q2 A q3, 
ip = A -15 A Xi> *l> = (Xi -*• OX2) A (X2 -*• 0X3) A (X3 -*• Oxi). 
Show that \/*L -1 <p, but for every finite model 9Jt based on a frame for L, 9Jt |= ^ 
implies 9JI |= -up. (Hint: consider the frame 
Exercise 11.23 Show that the following logics are not finitely approximable: 
by a Sahlqvist formula. 
Exercise 11.24 Prove that the modal logic of the frame shown in Fig. 8.1 (b) 
is not finitely approximable and finitely axiomatizable, but all its proper normal 
extensions are. 
(cu, {(m, m) : m > 0} U {(m, n) : \m - n\ = 1}).) 
K4 ® oft ( i ) 

414 
FINITE APPROXIMABILITY 
Exercise 11.25 Let Su be the frame shown in Fig. 11.10 (a). Denote by {fo : 
i < u} the class of its finite subframes such that each Si contains a;, the cluster C 
and a finite generated subframe of the “Nishimura ladder” including the points 
a, 6, c. For example, the smallest subframe of Su of that sort—call it #0—is 
depicted in Fig. 11.10 (b). Fix a point in C, say d, and denote by the set of 
all non-trivial antichains in #0 containing d. And, for every i < u;, let be the 
set of all non-trivial antichains in Si- Show that 
(i) 	for each i < u, there is a formula pi in one variable such that 
S4©a(3ri,2)i,-L) = S4 0 pi\ 
(ii) 	for every distinct i,j <u,Si\= 
Exercise 11.26 Prove that 
(i) there is an infinite ascending chain of logics in NExtS4, each of which is 
axiomatizable by a formula in one variable; 
(ii) there is a logic in NExtS4 which is not finitely axiomatizable but has an 
infinite set of one variable axioms; 
(iii) the cardinality of the class of logics in NExtS4 with one variable axioms 
is that of the continuum. 
Exercise 11.27 Show that there is a logic in NExtS4 which is axiomatizable 
by formulas in one variable and not finitely approximable. 
Exercise 11.28 Construct a modal formula p in two variables such that S40<p 
is not finitely approximable. 
Problem 11.1 Can one replace finite approximability in Theorems 11.10 and 
11.13 with Kripke (or some other kind of) completeness? 
Problem 11.2 Are the logics of the form K0Dnp —> Dmp andK®tran finitely 
approximable? 
Problem 11.3 Are the logics in NExtK axiomatizable by modal reduction 
principles finitely approximable, decidable? 

NOTES 
415 
11.8 	Notes 
The method of constructing models from the normal forms was developed by Fine 
(1975a); Section 11.1 presents the main results of this paper. Cresswell (1983) 
modified Fine’s method to prove the finite approximability of the McKinsey logic 
KM using the canonical models. 
The essentially negative axioms were considered by McKay (1971), who used 
Glivenko’s theorem to show that the addition of such an axiom preserves the 
decidability of si-logics. Rybakov (1978b, 1992) proved the modal analog of 
Glivenko’s theorem (Lemma 11.11) and applied it to DO-axioms. That infinitely 
many DO-axioms do not preserve finite approximability (Exercise 11.3) was 
shown by Rybakov (1978b). Logics with the simple substitution property 
(Exercise 11.4) were introduced by Sasaki (1989). The characterization of finite depth 
logics in NExtS4 with this property (Exercise 11.5) was obtained in Sasaki et 
al. (1994). The result of Exercise 11.4 (ii) was proved by Maksimova (1987). 
The subframe logics in NExtK4 were introduced and studied by Fine (1985). 
The cofinal subframe logics in NExtK4, ExtK4 and Extint were considered in 
Zakharyaschev (1996a). Wolter (1993) investigated subframe logics in NExtK 
(Theorem 11.31, Example 11.32 and Exercises 11.20, 11.21 were taken from his 
dissertation). Recently he has constructed a finitely axiomatizable subframe logic 
which is not decidable using the bimodal logic of this sort found by Spaan (1993). 
Exercises 11.7-11.17 are due to Zakharyaschev (1996a, 1997). The finite 
approximability of logics in NExtS4.3 was first established by Bull (1966) with the help 
of the algebraic technique; Fine (1971) gave a semantic proof and showed that 
all these logics are finitely axiomatizable and so decidable. That intuitionistic 
disjunction free formulas are V3-definable (Exercise 11.18) was proved by Cha- 
grova (1986) and Rodenburg (1986); Shimura (1993) gave a direct proof that 
the si-logics with this kind of axioms are canonical. Exercise 11.19 is due to van 
Benthem (1989) and Exercise 11.22 to Wolter (1994). Theorem 11.36 was 
actually proved by Visser (1984) (in terms of so called tail models); see also Chagrov 
(1985b). Minimal tense extensions of cofinal subframe logics were investigated 
by Wolter (1995, 1996a). 
The methods of proving finite approximability presented in Sections 11.5 and 
11.6 	were developed by Zakharyaschev (1993, 1997). However, some of the results 
in these sections were obtained earlier using different techniques. That finite 
approximability is not in general preserved under sums of si-logics was observed by 
Blok (1976). Modal reduction principles were studied by van Benthem (1976b) 
who showed that all of them are first order definable on transitive frames and 
described those that are first order definable on the class of all frames. 
Problem 11.2, as far as we know, was raised by Segerberg. That extensions of GL 
by a finite number of frame formulas are finitely approximable was proved 
independently by Kracht (1993c). Moreover, he showed that the addition of such 
formulas preserves the finite approximability in NExtGL. Exercise 11.24 is due 
to Kracht (1993b). The finite approximability of si-logics with extra axioms in 
one variable was first established by Sobolev (1977b), who gave in fact a rather 

416 
FINITE APPROXIMABILITY 
general syntactical sufficient condition of the finite approximability of si-logics 
and also constructed a si-logic with a two-variable axiom which is not finitely 
approximate. An extension of Grz with infinitely many one-variable axioms which 
is not finitely approximable and even not compact was constructed by Shehtman 
(1980). Earlier Shehtman (1977) presented incomplete calculi in NExtGrz and 
Extint with axioms in two variables. An example of a finitely axiomatizable 
Sahlqvist logic above S4 that is not finitely approximable (see Exercise 11.23) 
was given in Chagrov and Zakharyaschev (1995b). 

12 
TABULARITY 
Now we consider tabular and locally tabular modal and superintuitionistic logics. 
The main question we try to answer here is how to determine whether a given 
logic is tabular or locally tabular. 
12.1 	Finite axiomatizability of tabular logics 
First we establish that every tabular modal (no matter normal or not) and si- 
logic is finitely axiomatizable. This will be done with the help of a syntactic 
criterion of tabularity which uses the following formulas: 
<*n = -<(¥>1 A 0(v?2 a 0(v?3 A ... A Oipn)...)), 
n—1 
/?n = A A ... A Oipn), 
m—0 
where for 1 < i < n, ipi = pi A... Api-i A-»p* Api+i A.. .A pn. The reader can check 
that a frame # = (W, R) refutes an at a point Xi iff a chain of length n starts 
from a?i, i.e., x\Rx2R... Rxn for some distinct x\,..., xn. # refutes (3n at x\ iff 
there is a chain X1RX2R... Rxm of length m < n such that xm is of branching 
n, i.e., xmRyi,... ,xmRyn for some distinct yi,... ,yn. The conjunction an A/3n 
will be denoted by tabn. 
Theorem 12.1 (i) A logic L € ExtK is tabular iff, for some n < u, tabn € L. 
(ii) There is a recursive function f(n) such that every rooted frame validating 
tabn contains < f(n) points. 
Proof (i) Suppose L is tabular, i.e., L = Log# for some finite frame # of 
cardinality n — 1. Then clearly # |= tabn, from which tabn € L. 
Suppose now that tabn € L. This means that only chains of length < n — 1 
can start from every point (every distinguished point, if L is not normal) in the 
canonical model for L, and each point in those chains is of branching < n — 1. 
Indeed, let X\R... Rxn be a chain starting from a (distinguished) point X\. Since 
Xi ^ Xj, for 1 < i < j < n, by the definition of the canonical model, there are 
formulas tpij such that Xi |= 4>ij and Xj ^ 'iftij. Then taking Aj=i we 
have, for 1 < i < n, 
Xi h Xi A ... A Xi-1 A ->Xz A Xi+i A ... A *n, 
and so 

418 
TABULAR.ITY 
Xx \= A O(<p'2 A 0(^3 A ... A Otp'J ...), 
where ^ = <pt{xi/Pi, • • •, Xn/Pn}- Therefore, xx \= an{xi/pi, • • •, Xn/Pn}, which 
is a contradiction. The claim concerning branching is proved analogously. 
It follows immediately that the number of points in every subframe generated 
by a (distinguished) point in the canonical model for L does not exceed the 
number of points in the n — 1-ary tree of depth n — 1, that is 
f(n) = 1 + (n - 1) + (n - l)2 + ... + (n - l)n"2. 
So L is complete with respect to a class of finite models of cardinality < /(n), 
which means (see the proof of Theorem 8.47) that L is characterized by a finite 
class of finite frames, i.e., tabular. 
(ii) It suffices to take the function f(n) defined above. □ 
Corollary 12.2 (i) L £ NExtK is tabular iff altn Atran £ L, for some n <lj. 
(ii) L € Extint is tabular iffL is of finite width and depth, i.e., bwnAbdn £ L 
for some n < lj. 
Proof Exercise. □ 
Corollary 12.3 Every tabular modal or si-logic L has finitely many extensions 
and all of them are tabular. 
Proof That all these extensions are tabular follows from Theorem 12.1 (i). And 
by (ii), there exist only finitely many distinct rooted frames for L and so only 
finitely many extensions of L. □ 
We can prove now the main results of this section. 
Theorem 12.4 (i) Every tabular logic L £ ExtK is finitely axiomatizable. 
(ii) Every tabular si-logic is finitely axiomatizable. 
Proof (i) According to Theorem 12.1 (i), L is an extension of K + tabn, for 
some n < lj. By Corollary 12.3, we have a chain 
K + tabn = Li C L2 C .C Lfe_i C Lk = L 
of logics such that 
{Lf £ ExtK : Li C L' C Li+1} = 0, 
for every i = 1,..., A; — 1. It remains to notice that if V is finitely axiomatizable, 
V C L" and there is no logic located properly between V and L" then L" is 
also finitely axiomatizable (e.g. L" = V + (p, for any tp £ L" — V). 
(ii) is proved analogously. □ 
12.2 	Immediate predecessors of tabular logics 
Let L be a tabular logic and Lf an arbitrary logic. The question we consider in 
this section is how to determine whether L = Lf. To be more specific, we always 

IMMEDIATE PREDECESSORS OF TABULAR LOGICS 
419 
Fig. 12.1. 
will assume that all our logics are finitely axiomatizable (normal or quasi-normal) 
extensions of some basic logic Lo (in particular, Lf = Lo 0 or V = L0 + <£>)• 
Since L is tabular, it is not difficult to check the inclusion L'CL (at least, 
in principle). The converse inclusion is more problematic. To verify it after 
establishing V C L we may use the following simple observation. 
Suppose L has only finitely many immediate predecessors (in NExtLo or 
ExtLo), say Li,..., Ln, and all of them are tabular. Then L = Lf iff V C L and 
V Li,... ,L' Ln, which reduces our question to the decidability problem 
for tabular logics. 
For example, by Makinson’s theorem, the logic K®1 has exactly two 
immediate predecessors in NExtK, namely K®D1 = Log# and K 0p <-► □ p = Logo, 
which are tabular. Therefore, we obtain an algorithm for deciding whether a 
modal formula axiomatizes the inconsistent logic. However, in the class NExtK 
this is the only known positive result of that sort. By Theorem 10.60, every 
consistent tabular logic has a continuum of immediate predecessors in NExtK. In 
particular, we have the following: 
Theorem 12.5 The logic K 0 □_!_ has infinitely many tabular immediate 
predecessors in NExtK. 
Proof Let L be the logic of the frame $ = (W, R, P), where 
W = {a, b} U {n : n < a;}, 
R = {(m, a), (m, b), (6, m), (m, n) : n < m < u} 
(see Fig. 12.1 in which the subframe containing the natural numbers and u is 
transitive) and P is the family of finite subsets of W without u and cofinite 
subsets of W containing u. Notice that $ is descriptive and each of its points 
except u is definable by a variable free formula. Namely, for n < u, we have 
{a} = {x: xh=D-L}, {b} = {x: x |= -.(□! V ODJ_)}, 
{0} = {x : x |= <>{&} A -»00{a}}, 
{n -f 1} = {x : x\= 0{n} A “■<>(-»{&} A 0{n})}. 
It follows that $ is the 0-generated universal frame for L. 

420 
TABULARITY 
Now take any proper normal extension Lf of L and consider its O-generated 
universal frame 0. Clearly, 0 is (isomorphic to) a generated subframe of But 
£ has no generated subframe different from itself and •. Therefore, either L = V 
or V = Log® = K 0 Since the former alternative is impossible, L is an 
immediate predecessor of K 0 
To construct an infinite sequence of tabular immediate predecessors of K0D JL 
it suffices to take the logics of the frames ({a, 6,0,1,..., n}, R\{a,b, 0,1,..., n}). 
□ 
Similar results can be proved for tabular logics in the class ExtK4 (see 
Exercises 12.4 and 12.5). We show, however, that in NExtK4 our criterion works 
perfectly well. To this end we require the following: 
Theorem 12.6 (i) Each finitely axiomatizable logic L € NExtK4 of finite depth 
is a finite union-splitting, i.e., can be represented in the form 
L = K4 ©{<*#(&,!) : i€l} 
with finite I. 
(ii) Each finitely axiomatizable logic L € ExtS4 of finite depth can be 
represented in the form L = S4 + {a^fo, JL) : i £ 1} with finite I. 
Proof (i) Let L = K40<p be a logic of depth n and m the number of variables 
in (p. We show that L coincides with the logic 
n-f 1 
L' = K4®{a»(0,±): |0] < £ 2mcm(i), © £ V>} 
i—1 
(the function Cm(i) was defined in Theorem 8.82). Indeed, the inclusion L D L' 
is obvious. Suppose now that (p V. Then there is a rooted refined m-generated 
frame $ for V refuting tp. Clearly, $ is of depth < n, since otherwise 0^(0, J_) 
is an axiom of V for every rooted generated subframe 0 of $ of depth n + 1 ((p 
is refuted in such frames because L is of depth n), and so 3 ^ L', which is a 
contradiction. But then J-) is an axiom,of L', contrary to our assumption, 
(ii) A similar proof is left to the reader as an exercise. □ 
We are in a position now to prove 
Theorem 12.7 (i) Every tabular logic L e NExtK4 has finitely many 
immediate predecessors and they are also tabular. 
(ii) Every tabular logic L £ ExtS4 has finitely many immediate predecessors 
and they are also tabular. 
Proof (i) Suppose L is the logic of a finite transitive frame #. By Theorem 12.6, 
L is a finite union-splitting. Take any independent axiomatization of L by frame 
formulas, say 
L = K4® {<*“(&,!) : i = 1,. ■ ■ ,n}. 
By Theorem 10.52 the logics Li = Log(# + fo), for i = 1,... ,n, are all the 
distinct immediate predecessors of L. By the definition, they are tabular. 

PRETABULAR LOGICS 
421 
(ii) is proved in the same way. □ 
Moreover, we have the following lattice-theoretic criterion of tabularity in 
NExtK4 and ExtS4: 
Theorem 12.8 (i) A logic in NExtK4 is tabular iff it has finitely many normal 
extensions. 
(ii) A logic in ExtS4 is tabular iff it has finitely many extensions. 
Proof Exercise. * □ 
With the help of the Blok-Esakia theorem and the fact that the map p 
preserves tabularity we immediately obtain 
Theorem 12.9 (i) Every tabular si-logic has finitely many immediate 
predecessors and they are also tabular. 
(ii) A si-logic is tabular iff it has finitely many extensions. 
12.3 	Pretabuiar logics 
The tabularity criteria, obtained so far, are not effective and moreover, as will be 
shown in Section 17.3, no effective tabularity criterion exists in general. However, 
for sufficiently strong logics, e.g. those in NExtS4 and Extint, the tabularity 
problem turns out to be decidable. The effective criterion to be proved below 
uses the following notion. 
We say that a logic L € (N)ExtLo is pretabuiar in the lattice (N)ExtLo, 
if L is not tabular but every proper extension of L in (N)ExtLo is tabular. In 
other words, a pretabuiar logic in (N)ExtLo is a maximal non-tabular logic in 
(N)ExtLo. 
Theorem 12.10 In the lattices ExtK, NExtK and Extint, every non-tabular 
logic is contained in a pretabuiar one. 
Proof By Theorem 12.1 and Corollary 12.2, a logic is non-tabular iff it does 
not contain the formula tabn (bwn A bdn in the intuitionistic case), for any 
n < u. It follows that the union of an ascending chain of non-tabular logics is a 
non-tabular logic as well. The standard use of Zorn’s lemma completes the proof. 
□ 
Thus, pretabuiar logics provide typical, in a sense, examples of non-tabular 
logics in a given lattice. 
If there is a good description of all pretabuiar logics in a lattice, we have at our 
disposal an effective (modulo the description) tabularity criterion for the lattice. 
Indeed, take for definiteness the lattice NExtK4. How can we determine, given a 
formula <p, whether K40<p is tabular? We may launch two parallel processes: one 
of them generates all derivations in K4 0 p and stops after finding a derivation 
of to6n, for some n < uj\ another process checks if <p belongs to a pretabuiar 
logic in NExtK4 and stops if this is the case. The termination of the first process 
means that K4 0 p is tabular, while that of the second one shows that it is not 
tabular. 

422 
TABULARITY 
o 
o 
o 
© 
rgU) rgu) ) 
t>l x>2 U3 
m 
3S 
Fig. 12.2. 
Unfortunately, it is impossible to describe in an effective way all pretabular 
logics in (N)ExtK and even (N)ExtK4: in Section 13.2 we shall construct a 
continuum of them. However, for smaller lattices like NExtGL or NExtS4 such 
descriptions can be found. We shall use the following: 
Theorem 12.11 Every non-tabular logic L € NExtK4 has a non-tabular finitely 
approximable normal extension. 
Proof Since L is non-tabular and characterized by the class of its rooted finitely 
generated refined frames, we have either a sequence fo, i ~ 1,2,..., of rooted 
finite frames for L of depth i, ora sequence 3i of rooted finite frames for L of 
width > i. In both cases the logic Loglfo : i < u} D L is non-tabular and 
finitely approximable. □ 
As an immediate consequence we obtain 
Corollary 12.12 Every pretabular logic in NExtK4 is finitely approximable. 
Let us begin with pretabular normal extensions of S4. 
Theorem 12.13 There are exactly five pretabular logics in NExtS4, viz., the 
logics of the frames depicted in Fig. 12.2 (where © is an u-point cluster). 
Proof First we show that the logics of the frames in Fig. 12.2 are really 
pretabular. For 0 < n < u, we denote by 3\ a chain of n simple clusters, by 3% a cluster 
with n points; 3$, 3% and 3$ are defined analogously by restricting the infinite 
cluster and antichains in the frames , #4 and 3t i*1 Fig- 12.2 to n-point cluster 
and antichains, respectively. 
Let L = LogSY- Clearly, L is not tabular. Denote by V a normal 
pretabular extension of L. By Corollary 12.12, V is finitely approximable. And since 
v 
q:((oq)) € L and a( o ) e L, finite rooted frames for Lf are of the form for 
n < LJ.lt follows immediately that the same canonical formulas belong to L and 
L', from which L = V. 
Suppose now that L = Logg^. Since a(£ln) L, for any cluster £ln with 
n <u points, L is not tabular. What are finite rooted frames for L? Every such 
frame is either a single point or a chain of two clusters, the last one being simple. 

PRETABULAR LOGICS 
423 
o 
V { 
This follows from the fact that the formulas a( o ), a( 5) and g(@, _L) are 
valid in S3 and so belong to L. And since L is finitely approximable (as a logic 
of depth 2) and is reducible to S3, any proper extension of L is tabular. 
The logics of the frames S2, 3Y and #5 are considered in the same manner. 
Let us show now that NExtS4 contains no other pretabular logics than those 
mentioned above. Suppose L is a normal pretabular extension of S4. If L is of 
infinite depth then among its frames there are finite chains (of simple clusters) 
of any length n < uj, from which L C LogSY- Since L is pretabular, it follows 
that L = LogSY- 
Suppose that L is a logic of finite depth. If for any n < uj there is a frame for L 
containing a final cluster with > n points then, by the generation and reduction 
theorems, every finite cluster validates L and so, in view of its pretabularity, 
L = LogSY • If f°r any n < uj, frames for L contain non-final clusters with > n 
points, then we can reduce their subframes generated by such clusters to frames 
of the form S3, n < Hence, L = LogSf. 
It remains to consider the case when all clusters in finite rooted frames for L 
(of finite depth) contain < n points, for some n < cu. Then in these frames there 
must be points of branching > n, for every n < cv. Say that a point x in a finite 
frame S is of outer (inner) branching n if n is the number of pairwise inaccessible 
immediate successors of x belonging to final (respectively, non-final) clusters in 
S- Two cases are possible now. 
Suppose first that finite rooted frames for L contain points of outer branching 
> n, for every n < u). Clearly, we can reduce their subframes generated by such 
points to frames of the form #4, which means that L = LogS^. And if finite 
rooted frames for L have points of arbitrarily great inner branching then these 
points generate subframes that are reducible to #5, n < u), and so L = LogSY- 
□ 
It is not difficult to axiomatize the logics of the frames in Fig. 12.2. 
Corollary 12.14 The following logics and only they are pretabular in the lattice 
NExtS4: 
LogSY 
LogSY 
LogS^ 
LogS? 
S4 © a() © a(@), 
O 
S4 0 a( i), 
o 
V I 
S4 0a( o ) 0a( 4) 0a((£2), ±), 
t 
S4©a( £)©“(©)> 

424 
TABULARITY 
where 0f)4 is a chain of four points. 
Proof Exercise. □ 
Using the Blok-Esakia theorem and the fact that the maps p and a preserve 
tabularity (and so pretabularity), we obtain a description of pretabular si-logics. 
Theorem 12.15 There are three pretabular logics in Extint, namely 
LogS? = Int + /J( 
Log£? = Int + /?( 
0 
1 
h 
Log3£ = Int + p( 
Let us consider now pretabular logics in the lattice NExtGL. 
Theorem 12.16 The set of pretabular logics in NExtGL is denumerable. It 
consists of the logics Log0CJ and Log0" n, form > 0, n > 1, where 0^ and 0^>n 
are the frames depicted in Fig. 12.3. If (m,n) ^ (kj) then Log0£in j=- Log0£j. 
Proof That all these logics are not tabular and Log0CJ is pretabular can be 
proved in the same way as in the proof of Theorem 12.13. We show only that 
Log02,2 *s pretabular; other logics Log0^ n are considered analogously. Denote 
by 02,2 the frame obtained from 0^2 (shown in Fig. 12.3) by deleting the points 
bi for i > n. 0£ t is defined in the same way. For n < a>, let 
7n = □n+1l A OnT. 

PRETABULAR LOGICS 
425 
Then for all points a* and bk in 0^2) we have: 
Q*i \=z 'Yii T7 if 0 — ^ — 4, J 
bk 1= 72) bk j^= 7/ if k — ^ 7^ 
For a variable free formula y>, put 
t>(<£?) = □+(<^ —i► p) V 0+(<£> —> -ip). 
The meaning of this formula is that v(cp) is valid in a rooted transitive Kripke 
frame ^ iff ^ contains at most one point where cp is true. It should be clear that 
the following formulas are valid in 02 2 and so belong to Log02 2: 
4 
«(o), D5!, □+ V 7i, «(7i) (0 < * < 4, » ± 2), ^+(73 -» vfo)). 
i—0 
If we call a point at which 7* is true a point of type z, then this means that every 
rooted frame for Log02}2 Is irreflexive and of depth < 5; each of its points is of 
one of the types 0,1,2,3,4, where a point of type i ^ 2, if any, is unique, and a 
point of type 3, if any, sees only one point of type 2. 
It follows that the class C of finite rooted frames for Log02}2 consists of 
irreflexive chains of length < 5 and the frames 0£ 2> for n = 1,2, Since 0^2* 
is reducible to 0^2 and the chains of length < 4 are generated subframes of 
02 2) every non-tabular finitely approximate normal extension of Log02}2 must 
have C as the class of its finite rooted frames. And since Log02}2 is finitely 
approximable itself (as a logic of finite depth), it is pretabular. 
Now take any pretabular logic L 6 NExtGL. If L is of infinite depth then 
clearly L = Log0CJ. 
Suppose L is of finite depth. What are finite frames characterizing it? Observe 
first that L is characterized by a class of finite rooted frames of the same depth. 
Indeed, suppose {& : i < u} is a sequence of pairwise non-isomorphic finite 
rooted frames such that L = Log{fo : i < uj} and let d = max{d(Sri) : i < u)} 
(so that Dd~1± & L). If the sequence contains only finitely many frames of depth 
d, then the rest of the frames in it determine a non-tabular extension Lf of L. 
And since Dd~1± e L', we arrive at a contradiction with the pretabularity of L. 
Therefore, the sequence contains infinitely many frames of depth d. Let L” be 
the logic determined by these frames. Clearly, L" is not tabular (otherwise the 
frames of depth < d determine a non-tabular proper extension of L), from which 
L = L". 
Now we use the classification of points in frames by means of the formulas 7* 
introduced above. 
Lemma 12.17 Suppose L is a pretabular logic in NExtGL characterized by a 
class {$k • k < cu} of finite rooted frames of depth d. Then 
(i) for every i < d - 1 except possibly only one j < d - 1, each frame $k, 
k < uj, contains exactly one point of type i and 

426 
TABULARITY 
(ii) all the points of type j, except one of them, are accessible only from the 
root o/Sfc. 
Proof Since d($k) = d, for all k < lj, every point in is of one of the types 
0,1,..., d - 1 and for each i < d — 1, there is a point in 3* of type i. And since 
these frames are pairwise non-isomorphic, at least for one j < d — 1 and every 
n < u;, there is 3fc containing > n points of type j. 
Observe that for every i < d — 1, there is n < u such that every point of type 
i in every 3fc sees at most n points of type j. For otherwise we could take the 
infinite subsequence of the (non-isomorphic) rooted subframes of 3fc, generated 
by points of type z, and then the logic determined by this subsequence would be 
a non-tabular proper extension of L. 
Notice also that for every i < d — 1 different from j, each 3fc contains only 
one point of type z, and if 3fc contains a point of type j that is seen not only 
from the root (which means j < d — 2), then this point is unique. Indeed, if this 
is not the case then v(ji) $ L, for some i ^ j. On the other hand, using the 
observation above, we can construct an infinite sequence of non-isomorphic reducts 
of containing arbitrarily many points of type j and satisfying the desirable 
properties. This sequence determines then a non-tabular proper extension V of 
L, since t>(7i) £ V, which is a contradiction. □ 
Now, returning to the proof of our theorem, we see that all finite rooted 
frames for L have the form &lm n for some fixed m > 0 and n > 1. Therefore, 
L = Log0^ n. The last claim of the theorem is obvious. □ 
Using the semantic description of pretabular logics in NExtGL, it is not hard 
to find finite sets of (canonical) formulas axiomatizing them. 
Theorem 12.18 All pretabular logics in NExtGL are finitely axiomatizable and 
w decidable. 
Proof Exercise. □ 
The technique developed in the proofs of Theorems 12.13 and 12.16 can be 
used for finding pretabular logics in NExtD4. We invite the reader to prove the 
following: 
Theorem 12.19 There exist ten pretabular logics in NExtD4, viz., the logics 
of the frames depicted in Fig. 12.2 and 12.4• -AW these logics are finitely 
axiomatizable and so decidable. 
Other applications of this technique for describing pretabular logics in the 
classes (N)ExtK4BDn, ExtGL can be found among the exercises in Section 12.5. 
12.4 	Some remarks on local tabularity 
The notion of local tabularity turns out to be much more complex than the close 
notion of tabularity and, besides, it is not so well studied. The title of this section 
corresponds to our moderate knowledge in this area. 
Let us consider first modal logics. Observe at once that we have 

SOME REMARKS ON LOCAL TABULARITY 
427 
Fig. 12 
Proposition 12.20 A logic L = ExtK is locally tabular iffkevL G NExtK is 
locally tabular. 
Proof Follows from Theorem 7.4. □ 
So we confine ourselves to considering here only normal modal logics. Using 
the results of Section 8.6, we can easily obtain the following criterion of local 
tabularity in the lattice NExtK4. 
Theorem 12.21 A logic L G NExtK4 is locally tabular iffL is of finite depth. 
Proof (=>) Suppose L is a logic of infinite depth, i.e., it has finite frames of 
any depth < lj. Consider the sequence of formulas an defined by 
Oil = P, Oin+i =pVD(p-> Dan) 
and show that these formulas are pairwise non-equivalent in L. Take any distinct 
n and m, say n > m, and any finite frame # = (W,R) of depth 2n — 1. Let 
X2n-iR • • • Rxi be a chain of points in # from distinct clusters. Define a valuation 
in # so that x p iff x = X2k-i for some k < n. Then clearly we have that for 
every z, k < n, X2k-i ^ a* iff k > i and so X2m-i ft am, £2m-i ft otn. Therefore, 
Oim Oin L. 
(<*=) According to the results of Section 8.6, finitely generated descriptive 
frames for logics of finite depth are finite. Therefore, is finite for every 
n < a;, which means that L is locally tabular. □ 
Since the formulas an in the proof above contain only one variable, we have 
Corollary 12.22 A logic L G NExtK4 is locally tabular iff the algebra 21l(1) 
is finite. 
Every logic L G NExtS4, which is not locally tabular, is clearly validated by 
the infinite descending chain of reflexive points. And since this chain characterizes 
Grz.3, we arrive at 
Theorem 12.23 A logic L G NExtS4 is not locally tabular iffLC Grz.3. 
v 
The logic Grz.3 = S4®a(@) ®a( o ) is decidable, and so we can always 
effectively determine, given a formula </?, whether S4® is locally tabular. Since 
Grz.3 is not locally tabular itself but all its proper extensions possess this 
property, we may call it a pre-locally tabular logic. Of course, pre-local tabularity as 
well as pretabularity depends on the choice of a lattice of logics. 

428 
TABULARITY 
Thus, we have the following facts: in the class NExtS4 there is only one 
pre-locally tabular logic and every normal extension of S4 that is not locally 
tabular is contained in the pre-locally tabular logic. The latter fact can probably 
be extended to the class NExtK4 (this is our conjecture). As to the former one, 
we have 
Theorem 12.24 There is a continuum of pre-locally tabular logics in NExtK4. 
Proof All the logics constructed in the proof of Theorem 13.15 are pre-locally 
tabular. □ 
The situation with locally tabular and pre-locally tabular logics in Extint 
turns out to be quite different from that in NExtS4. First, there is no connection 
between the local tabularity and finite depth, though all finite depth si-logics are 
locally tabular, of course. For instance, the logic pGrz.3 = LC is locally tabular 
(see Section 8.7). And second, there is a continuum of pre-locally tabular logics 
in Extint (see Exercise 12.14). 
12.5 	Exercises and open problems 
Exercise 12.1 Show that, for every n < w,K® tabn = K + tabn. 
Exercise 12.2 Show that tabular logics form filters in the lattices Extint, 
NExtK, and ExtK. 
Exercise 12.3 Prove analogues of Theorem 12.1, Corollary 12.3 and 
Theorem 12.4 for m-modal logics, m < lj. (Hint: use the formulas an and (3n defined 
as follows: an is the conjunction of all formulas of the form 
{<Pi A Oix{ip2 A Oi2((/?3 A ... A Oinipn+i)...)), 

EXERCISES AND OPEN PROBLEMS 
429 
for ij e {1,... ,m}, 1 < j < n, and /?n is the conjunction of all formulas of the 
form 
-,OjJk... Ojfc (Ojfc+1y?i A ... A 
^^fc+n+1 ¥>n+l), 
for k < m, ij e {1,..., m}, l<j<fc + n + l, where 
<Pi = Pi A ... A Pi-, i A ^ A pi+i A ... A pn+i. 
Exercise 12.4 Prove that every tabular consistent normal modal logic has 
infinitely many tabular normal immediate predecessors. 
Exercise 12.5 Prove that every tabular logic in ExtK4 (ExtK) has infinitely 
many tabular immediate predecessors in ExtK4 (ExtK). 
Exercise 12.6 Prove that GL.3 + Dp —> p is the only pretabular logic of infinite 
depth in ExtGL. 
Exercise 12.7 Show that the set of pretabular logics of finite depth in ExtGL 
is denumerable and consists of the logics of the frames shown in Fig. 12.5 (a) 
with distinguished roots, where /, m, n > 0 are fixed for each logic. 
Exercise 12.8 Prove that every pretabular logic in ExtGL is finitely axioma- 
tizable. 
Exercise 12.9 Show that the sets of pretabular logics in NExtGL and ExtGL 
are disjoint. 
Exercise 12.10 Show that the set of pretabular logics in (N)ExtK4BDn is 
finite for every n <cu and that all of them are finitely axiomatizable. 
Exercise 12.11 Prove that all extensions of every pretabular logic L in NExtS4 
are normal and so L is also pretabular in ExtS4. 
Exercise 12.12 Show that besides the logics mentioned in the preceding 
exercise, there is only one pretabular logic of finite depth in ExtS4, namely the logic 
of the frame in Fig. 12.5 (b) with distinguished root. 
Exercise 12.13 Show that there are countably many pre-locally tabular logics 
in NExtK4.3, namely the logics of each of the frames in Fig. 12.5 (c). 
Exercise 12.14 Show that there is a continuum of pre-locally tabular logics in 
Extint. 
Exercise 12.15 Show that KC is the intersection of all pre-locally tabular si- 
logics. 
Exercise 12.16 Prove the analog of Theorem 12.23 for NExtGL. 
Problem 12.1 Is it true that every non-locally tabular logic in NExtK (Extint) 
is contained in a pre-locally tabular one? 
Problem 12.2 Is the problem “K4 0<p is of finite depth” decidable? 
Problem 12.3 Is the problem “K4 0<p is of finite width” decidable? 

430 
TABULARITY 
12.6 	Notes 
The problem of determining whether a given logic is tabular has attracted 
logician’s attention since Godel (1932) proved that Int is not tabular and Dugundji 
(1940), using the same idea, demonstrated the non-tabularity of all Lewis’ logics. 
(The term “tabularity”, as far as we know, was introduced by Kuznetsov in view 
of the fact that tabular logics can be defined by “truth-tables” similar to that 
for Cl.) Later, analogous facts were discovered by Drabbe (1967) with respect 
to the filters of distinguished elements in matrices characterizing logics: Lewis’ 
systems S1-S3 cannot be determined by matrices with a fixed finite number of 
distinguished elements. 
The finite axiomatizability of tabular superintuitionistic and normal (poly) 
modal logics follows from a rather general algebraic result of Baker (1977). Note, 
however', that for si-logics this was proved (but not published) in the mid 1960s 
by de Jongh. That all tabular quasi-normal modal logics are finitely axiomati- 
zable was first established by Blok and Kohler (1983). The idea of the proof of 
Theorem 12.1 can be easily extended to polymodal, in particular tense logics; 
see Chagrov (1996). 
That every tabular logic in Extint has a finite number of immediate 
predecessors, with all of them being also tabular, was discovered by Kuznetsov (1971). 
The same fact for NExtK4 is proved analogously; see Blok (1980c). Blok (1978) 
proved that every consistent tabular logic in NExtK has a continuum of 
immediate predecessors. 
The idea of using pretabular logics for constructing effective criteria of 
tabularity of si-logics was proposed by Kuznetsov. Maksimova (1972, 1975b) found 
all pretabular logics in Extint and NExtS4; for the latter class the same result 
was obtained by Esakia and Meskhi (1977). Pretabular logics in NExtK4 were 
investigated by Blok (1980c); some discrepancies in this paper were corrected in 
Chagrov (1989, 1996), where pretabular logics in ExtS4 and ExtGL were also 
considered. We used ideas of the latter paper for presenting the material of 
Section 12.3. A rather difficult problem is to describe pretabular logics in the class 
of normal extensions of the Brouwerian system T 0p —► DOp; it is known only 
that there are infinitely many of them; see Meskhi (1983). 
That all (not necessarily normal) modal logics of finite depth are locally 
tabular was proved by Segerberg (1971). Maksimova (1975a) showed the converse. 
Corollary 12.22, asserting that to disprove local tabularity formulas in one 
variable are enough, was noticed by Maksimova (1989c). 
The problem of local tabularity for si-logics turns out to be much more 
complicated: unlike NExtS4, where there is only one pre-locally tabular logic, Extint 
contains a continuum of them, as was proved by Mardaev (1984). Mardaev (1987) 
strengthened this result. He showed that, for every tabular si-logic L 2 KC, 
there is a continuum of pre-locally tabular logics {Li : i € 1} and a continuum 
of finitely pre-approximable logics {Mi : i € 1} such that KC C Li C Mi C L, 
for i € I. That KC is involved here is explained by the fact, discovered by 
Kuznetsov, that every pre-locally tabular si-logic is an extension of KC; see 

NOTES 
431 
Tsytkin (1987). These results show that the notions of pre-local tabularity and 
finite pre-approximability in Extint cannot be used to obtain effective criteria 
of local tabularity and finite approximability. As we shall see in Section 17.3, the 
property of finite approximability turns out to be undecidable, and nothing is 
known about algorithms recognizing local tabularity. 
One more interesting property—an antipode of tabularity—is antitabularity: 
we call a consistent logic antitabular if all models (frames, algebras, matrices) 
for it are infinite. Although there are no such logics in Extint and NExtK, in 
general there exists a lot of them. For instance, all logics used in the proof of 
Theorem 13.15 are antitabular. It is easy to construct a continual family of 
normal antitabular tense logics; Chagrov (1982) showed that there are antitabular 
modal companions of Int containing S3. 

13 
POST COMPLETENESS 
This chapter considers some properties of modal and superintuitionistic logics 
connected with Post completeness. 
13.1 	m-reducibility 
A logic L is said to be m-reducible if, for every formula ... ,qn) ^ L, there 
exist formulas ^i(pi,... ,pm),...,^n{Pu • • • rPm) such that 
■ ■ ■ ,Pm), • ■ • , V’nCPl, • • • iPm.)) £ L. 
A logic is called reducible if it is m-reducible for some m < u). 
Theorem 13.1 The following conditions are equivalent for every logic L in 
NExtK (Extint or ExtK,): 
(i) L is m-reducible; 
(ii) L is characterized by the algebra 21l(^) (by one of its m-generated Tarski- 
Lindenbaum matrices, if L G ExtK); 
(iii) every proper (normal, if L G NExtK,) extension of L contains a formula 
in m variables that is not in L. 
Proof The equivalence of (i) and (ii) is clear. 
We prove the implications (ii) => (iii) and (iii) => (ii) only for L G ExtK. Let 
L = Log (2lz/(m), Vl), where L' is a normal logic contained in L, and let L" be 
a proper extension of L. Suppose that every formula in m variables in V belongs 
to L. Then the matrix (21 z/(ra)> Vl") is isomorphic to (2lL'(m), Vl), whence 
L C L" C Log(2Mm), VL"> = Log<aL,(m), VL) = L, 
which is a contradiction. 
Suppose now that (iii) holds but L ^ Log (21//(m), Vl), for any normal logic 
L' contained in L. Then Log (2lz/(m), Vl) is a proper extension of L. On the 
other hand, by the definition, it contains no formula in m variables that is not 
in L, contrary to (iii). □ 
Remark This theorem has an unexpected consequence: if L is a normal logic 
every proper normal extension of which contains a formula in m variables that 
is not in L, then all (not only normal!) proper extensions contain formulas in m 
variables that are not in L. 

M-REDUCIBILITY 
433 
Theorem 13.2 No logic in the intervals 
[K4, S5], [K4,Grz®6d2], [K,GL®6d2], [Int, Int + bd2) 
is reducible. 
Proof Let us consider first the interval [K4, S5]. To show that logics in it are 
not m-reducible for any m < u, it is sufficient to find formulas (pm £ S5 all 
substitution instances in m variables of which are in K4. Denote by (£ln the 
n-point cluster and put (pm = a(£l2m+1, JL). Clearly <pm ^ S5. However, <pm is 
valid in the universal frame of rank m for K4, because all final clusters in it 
contain < 2m points. 
For the other intervals we use in the same manner the formulas 
2m+i \ / 
a( * .-L), ->( /\ 0(DlA-.piA /\pj)) and £( o ,1), 
»=1 j^i 
respectively, where in the first formula n = 22m + 2m and in the last one n = 
2m + 1. □ 
This trick with final clusters in the universal frames does not go through for 
KC = Int + ->p V -r-rp. 
Theorem 13.3 KC is 2-reducible. 
Proof We require some auxiliary facts. 
Lemma 13.4 Every finitely generated pseudo-Boolean algebra 21 is generated by 
a finite chain of elements in 21. 
Proof The proof is conducted by induction on the number of 2Ts generators. 
The basis of induction is trivial. 
Suppose the claim of our lemma holds for m — 1-generated algebras and 
consider a pseudo-Boolean algebra 21 with generators ai,..., am. By the induction 
hypothesis, the subalgebra © of 21, generated by ai,... ,am_i, is generated also 
by a chain &i < &2 < ... < bn ^ T. Put 6n+i = T and show that 21 is generated 
by the chain 
b\ A am ^ b\ 5* b\ V (62 A um) 5^ &2 ^ ^ bn ^ bn V (&n+1 A flm). 
Since this chain contains all b\,..., 6n, it generates ©. So it suffices to prove that 
it generates the element am as well. 
Observe that, for 1 < i < n, we have 
(pi Y (bi+\ A Q-7ti)) A (pi > bi A OfYi) — A 

434 
POST COMPLETENESS 
Fig. 13.1. 
Taking z = 1, we obtain that the chain generates the element 
(&1 V (b2 A am)) A (&1 -> h A am) = b2 A am. 
Using it in the equality above for i = 2, we then get 
(b2 V (b3 A am)) A (62 -> 62 A am) = 63 A am, 
etc. Thus in n steps we shall generate 6n+1 A am = am. □ 
Corollary 13.5 Suppose a finitely generated pseudo-Boolean algebra 51 refutes 
a formula <p(pi,... ,pm). T/zen £/zere exist formulas 
Xi(Qi, ■ ■ ■ ,Qn), ■ ■ ■ ,Xm(qu ■ ■ ■ ,qn) 
and a valuation 53 in 21 szzc/z that cp(x 1,... ,Xm) w refuted under 53 in 21 and 
53(#i),..., 53(gn) zs a chain of elements generating 51. 
Now we are in a position to prove Theorem 13.3. By Theorem 5.33, KC 
is characterized by the class of finite rooted frames with last elements. Let 
3 = (W,R) be such a frame refuting a formula <p{pi,... ,pm) under a 
valuation 53. By Corollary 13.5, we have formulas Xi(Qi> • • •, Qn)> i = 1,..., m, such 
that (p(x 1,..., Xm) is refuted in the model 9Jt = (#, 53) and the sets Xi = 53(#i), 
for z = l,...,n, form a chain with respect to C. Without loss of generality 
we may assume that X\ C X2 C ... C Xn ^ W. Construct from # and Xi, 
1 < z < n, a new frame 0 as is shown in Fig. 13.1. Here a\ and b\ see all the 
points in X\, and every point in Xi — Xi-\ sees a*_ 1 and bi-\ but not and bi, 
for z > 2. The points an and bn are seen only from the points in W — Xn. Put 
U = {ai, bi : 1 < z < n}. 
Take the formulas in the two variables p and q “describing” the points in U 
as in Section 6.5: 

M-REDUCIBILITY 
435 
&o=q, Po = P, oti=p-+q, Pi = q p, 
^n+l = Pn * &n V Pn— 1, Pn+l = &n * Pn V &n— 1 (fl > 1) 
and define a valuation il in 0 by putting 
it(p) = {ai} UI1= axT, Ufa) = {&i} Ul1= 6XT . 
Then by induction on i > 1 we can show that in the model 91 = (0,11) 
{x : x ^ OLi] = ad, {x: x ^ Pi} = 6*1 • 
Finally, we define the formulas in the variables p and q which will be substituted 
instead of qi,... ,qn: 
7i = ot-i+1 A ft+i pi, for 1 < i < n - 1, 
'In = &n V Pn • 
Denote by <5* the result of replacing the variables qi in a formula 6 with 7*. 
Lemma 13.6 For every formula 6 in the variables q\,..., qn, 
(i) there is x £ W such that (91, x) f= 6* iff (91, y) f= <5* for all y £ U; 
(ii) for every x £ W, (9Jl,x) |= 6 iff (VI, x) f= 6*. 
Proof We prove (i) and (ii) by simultaneous induction on the construction of 
6. The basis of induction and the cases 6 = 61 A 62 and <5 = <5i V 62 are obvious. 
Let 6 = <5i —► 62. 
First we establish (i). Suppose x \=6* for some x G W, but there is y G U 
for which y ^ <5*, i.e., there is a point 2 G yl such that z \= 6% and z ^ 6^ Then 
either 2 G U or 2 G X\. 
If z £ U then <5i is true at the last point in 0 (which belongs to W). Since 
x \= <$*, the formula 6% is also true at the last point in 0, which is a contradiction, 
because by the induction hypothesis, we should then have z \= 6%- If z £ Xi then 
we may assume 2 to be the last point in 0. (For as is easy to verify by induction, 
every formula in p and q has the same truth-values at all points in X\ under il.) 
But this is impossible, since x \= 6* implies z \= 6*. 
The converse implication is trivial because the last point in 0 belongs to W. 
Let us now prove (ii). If (9Jt,x) ^ 6 then (91,x) ^ 6* follows immediately 
from the induction hypothesis. Suppose (91, x) ^ <5* for some x G W. Then there 
is y G x] such that (91, y) f= and (91,y) ^ 63. If y £ W then (9Jt,x) ^ 6 
is a direct consequence of the induction hypothesis. Let y £ U. Then by the 
induction hypothesis for (i), (91, z) |= <5i and (91, z) 62, where 2 is the last 
point in 0. Therefore, by the induction hypothesis for (ii), (9Jt,x) ^ <5. □ 
Thus, by Lemma 13.6, we have 

436 
POST COMPLETENESS 
from which y>(xi(7i> ■ •. ,7n)» • • •»Xm(7i»• • • >7n)) & KC> since ® N KC- It; re" 
mains to observe that this formula contains no variable different from p and q. 
□ 
Theorem 13.7 KC is not 1-reducible. 
Proof Suppose otherwise. Then by Theorem 13.1, KC is the logic of 3xc(l) 
(see Fig. 8.14 displaying the universal frame for KC of rank 2). Since 3kc(1) 
of depth 2, we must have bd2 G KC, which is impossible. □ 
Theorem 13.8 KC + bd2 is not reducible. 
Proof Assuming otherwise, we would have that KC + bd2 is tabular, which 
certainly is not the case, because for every n > 1, f3(3%) KC + bd2, where #5 
is shown in Fig. 12.2. □ 
Let us now briefly consider the reducibility of modal companions of si-logics. 
According to Theorem 13.2, for every consistent si-logic L its smallest modal 
companion tL is not reducible, i.e., r does not preserve the reducibility. However, 
(T does. 
Theorem 13.9 If L is an m-reducible si-logic then <tL is also m-reducible. 
Proof Let M be a proper normal extension of crL. Then pM D L and so, by 
Theorem 13.1, there is y?(pi,... ,pn) G pM - L. It follows that T(ip) G M - crL. 
By Theorem 13.1, this means that crL is m-reducible. □ 
Corollary 13.10 Grz.2 is 2-reducible. 
13.2 	O-reducibility, Post completeness and general Post completeness 
O-reducible logics are “almost the same” as Post complete ones. Recall that a 
logic L is called Post complete in a lattice of logics (containing L) if L is 
consistent and does not have proper consistent extensions in the lattice. Of course, 
Post completeness of L depends essentially on the chosen lattice of logics (it 
corresponds to the coatomicity of L in the lattice). The following generalization 
of the notion of Post completeness is not connected with the choice of a lattice; 
it is an intrinsic property of logics. 
Say that a logic L is generally.Post complete if it is consistent and does 
not have proper consistent extensions closed under the inference rules that are 
admissible in L. It should be clear that every Post complete logic, say in the 
lattices ExtK, NExtK, Extint, is generally Post complete. 
The following two theorems give various characterizations of generally Post 
complete and simply Post complete logics. 
Theorem 13.11 For every consistent modal or si-logic L, the following 
conditions are equivalent: 
(i) L is O-reducible; 
(ii) L is characterized by one of its 0-generated Tarski-Lindenbaum matrices; 
(iii) L is characterized by some 0-generated matrix; 

O-REDUCIBILITY AND POST COMPLETENESS 
437 
(iv) an inference rule is admissible in L iff all variable free substitution 
instances of it are admissible in L; 
(v) L is generally Post complete. 
Proof Notice first that the equivalence of (i) and (ii) was proved in 
Theorem 13.1. The condition (i) is also a special case of (iv), because any formula 
ip G L may be regarded as the rule JL —> ±/(p admissible in L. The equivalence 
(ii) (iii) follows from the almost obvious fact that every O-generated matrix 
characterizing L is isomorphic to the O-generated Tarski-Lindenbaum matrix for 
L. The implication (ii) => (iv) is also clear (see the proof of Theorem 7.7). 
So it remains to establish that (iii) 4^ (v). Suppose L is generally Post 
complete. Take the O-generated submatrix (21, V) of the Tarski-Lindenbaum matrix 
for L. Since quasi-identities are clearly preserved under the formation of 
submatrices and the quasi-identities corresponding to the admissible rules in L are 
true in the Tarski-Lindenbaum matrix for L (see Theorem 7.7), we then have 
L = Log (21, V). 
Conversely, let L = Log (21, V) for some non-degenerate O-generated matrix 
(2t, V). As was observed above, we may assume that (21, V) is the O-generated 
Tarski-Lindenbaum matrix for L. Suppose L' is a consistent extension of L 
inheriting all the admissible rules in L. Then we have L C V C Log (21, V'), 
where V' = {|M|l : ip G L'}. Clearly, V C V'. Suppose V' ^ V, i.e., there 
is |M|l G V' - V. Then the rule ip/A. is admissible in L and so in L' as well. 
It follows that ip & L', which is a contradiction. Thus, LCL'C Log (21, V') = 
Log (21, V) = L and so V — L. □ 
Theorem 13.12 For every modal or si-logic L, the following conditions are 
equivalent: 
(i) L is Post complete in ExtK (or Extint); 
(ii) L is consistent and the variety of matrices for L is generated by any of 
its non-degenerate matrices; 
(iii) L is characterized by a O-generated matrix (21, V) in which V is an 
ultrafilter. 
Proof (i) => (ii). Suppose otherwise, i.e., (21, V) is a non-degenerate matrix for 
L but Var (21, V) ^ VarL. Since _L V, Log (21, V) is then a proper consistent 
extension of L, contrary to L being Post complete. 
(ii) => (iii). Let (21, V) be a non-degenerate O-generated matrix in VarL, say 
the O-generated submatrix of some non-degenerate matrix for L, which must 
exist because L is consistent. We show that V is an ultrafilter in 21. Suppose 
otherwise. This means that for some variable free formula tp, we have ip £ L and 
-i(p £ L. Then, by the deduction theorem, L + tp is a proper consistent extension 
of L any Tarski-Lindenbaum matrix of which is non-degenerate and does not 
generate VarL, contrary to (ii). 
(iii) => (i). Suppose L is characterized by a O-generated matrix (21, V) with an 
ultrafilter V and y?(pi,... ,pn) £ L, i.e., (21, V) ft y>(pi,... ,pn). Then there are 
variable free formulas • • •, such that ip(%j)i,..., \jjn) is refuted by (21, V), 

438 
POST COMPLETENESS 
i.e., (fi'tp i,..., ipn) & V. Since V is an ultrafilter, we have -k/?(^i,..., ^>n) G V and 
so -Hpfyi,..., ^n) € T- It follows that L + </?(V>i> • • • ’ ^n) is inconsistent. Thus, 
L has no proper consistent extension. It remains to notice that since _L V, L 
is consistent and so Post complete. □ 
This theorem shows, in particular, the place of Post complete logics among 
generally Post complete ones. Another indication to the place is given by 
Theorem 13.13 For every generally Post complete modal logic L, L is Post 
complete in ExtK iff L is structurally complete. 
Proof Exercise. (Hint: the implication (=>) is established with the help of the 
proof of Theorem 1.25; to show (4=), use Theorem 13.11 (ii) and Theorem 13.12 
(iii) 	in order to find a variable free inference rule which is admissible but not 
derivable in L.) □ 
The results about Post completeness above concerned only ExtK. The 
reason is that there are very few Post complete logics in Extint and NExtK. As 
we already know, Cl is the only Post complete (and the only generally Post 
complete—check!) extension of Int. As to NExtK, as a consequence of Makin- 
son’s theorem we have 
Theorem 13.14 There are only two Post complete logics in NExtK, viz., Logo 
and Log*. 
Let us consider now the family of (generally) Post complete logics in the 
lattice of extensions of an arbitrary quasi-normal logic L. By Theorem 13.11, the 
logic of the matrix (2lz/(0), Vl(0)), where V = kerL, is the smallest generally 
Post complete extension of L. The generally Post complete extensions of L are 
the logics of the matrices of the form (21^(0), V), where V is a proper filter 
containing Vl(0), while the Post complete extensions of L are the logics of the 
matrices (21^(0), V) in which V is an ultrafilter containing Vl(0). Using this 
observation, we can prove 
Theorem 13.15 (i) There is a continuum of generally Post complete logics in 
NExtK4. 
(ii) There is a continuum of Post complete logics in ExtK4. 
Proof (i) For iVCw, denote by $(N) the transitive Kripke frame of the form 
shown in Fig. 13.2 in which the only reflexive points are 2m +1, 4m + 2, 4n + 4, 
for m < u, n G N. (The frame in Fig. 13.2 corresponds to N such that 0,2 ^ N 
and 1 G N.) The reader can readily check that 3(N) is a generated subframe 
of ^3k4(0)- Denote by 2l(iV) the 0-generated subalgebra of 3(N)+. Since each 
point in 3k4(0) is definable by a variable free formula, Log2l(iVi) = Log2l(iV2) 
only if N\ = N2. Thus, the cardinality of the class of generally Post complete 
logics in NExtK4 is that of the continuum. 
(ii) Let V(iV) be a non-principal ultrafilter in 2l(iV). It is easy to see that 
such an ultrafilter is unique: it is the set of all cofinite subsets in $(N) (since 
2l(iV) consists of finite and cofinite subsets in S^iV), this set is an ultrafilter; on 

O-REDUCIBILITY AND POST COMPLETENESS 
439 
1 
0 
3 
2 
5 
4 
7 
6 
9 
8 
11 
10 
13< 
12 
Fig. 13.2 
the other hand, any non-principal ultrafilter must contain all cofinite subsets in 
$(N)). Take distinct N2 C u and i = 4n+4, for n € N2-Ni (or n € Ni~N2). 
Suppose the reflexive point i in $(N2) is defined by a variable free formula 
(fi. Then -<0^ G Log (2l(iVi), V(iVi)) and Ocpi G Log (%l(N2), V(iV2)), i.e., the 
logics Log(2t(iVi), V(iVi)) and Log <2t(AT2), V(iV2)) are distinct if Ni ^ N2- It 
follows that there is a continuum of Post complete quasi-normal extensions of 
K4. □ 
Which logics have exactly one Post complete extension? The importance of 
such logics is emphasized by 
Theorem 13.16 Every consistent logic L e ExtK is the intersection of some 
logics having only one Post complete extension in ExtK. 
Proof Observe first that the following simple result holds. 
Lemma 13.17 A modal logic L has exactly one Post complete extension iff, for 
every variable free formula (p, either ip G L or -«p G L. 
Proof (=>) Suppose L and ~^<p L, for some variable free <p. Then the 
logics L + -»<£ and L + have distinct Post complete extensions. 
(4=) Follows from Theorem 13.12 (iii). □ 
Call a matrix (21, V) maximal if V is an ultrafilter in 21. As a consequence 
of Lemma 13.17 we obtain that a logic characterized by a maximal matrix has 
only one Post complete extension. 
The crucial step in the proof of our theorem is 
Lemma 13.18 Every non-degenerate non-maximal matrix (21, V) is a submatrix 
of the direct product of maximal extensions of (21, V). 

440 
POST COMPLETENESS 
Proof For each a V, denote by V(a) some ultrafilter in 21 such that V C V(a) 
and a £ V(a), and form the direct product ]lagv (2l> V(a)). The reader can 
readily check that the matrix (21, V) is embedded in this product by the map 
b fbi where /*> maps {a : a £ V} to b. □ 
To complete the proof of Theorem 13.16, suppose L is a consistent logic and 
(21, V) its characteristic matrix in which V is not an ultrafilter. By Lemma 13.18, 
(21, V) is a submatrix of the direct product Yliei ^s maximal 
extensions. Therefore, 
L = Log (21, V) D Log J] (21, Vi) = f) Log (21, Vi). 
iei iei 
On the other hand, we clearly have Log (21, V) C Log (21, V») for every i e /, and 
so 
LC p|Log(21,Vi). 
iei 
It follows that L = p|i€/ Log (21, Vi) and, as was observed above, every Log(2l, Vi) 
has only one Post complete extension. □ 
Remark According to Lemma 13.18, every non-degenerate variety of matrices 
is generated by its maximal matrices. 
Theorem 13.16 shows that the study of any modal logic reduces, in a sense, 
to the study of logics having in ExtK a single Post complete extension. So it is 
worth considering classes of logics having exactly one Post complete extension 
in ExtK, which is common for all of them. The following theorem shows that 
such a class always contains a smallest logic. 
Theorem 13.19 Suppose Lr is a Post complete extension of L in ExtK. Then 
the logic L + {<p £ L' : ip is variable free} is the smallest logic among those 
extensions of L that have V as their only Post complete extension. 
Proof Follows from the fact that two modal logics have the same Post complete 
extensions in ExtK iff they contain the same variable free formulas. □ 
Above K4, Theorem 13.19 can be strengthened in the following way. 
Theorem 13.20 Suppose V is a tabular Post complete extension in ExtK of 
a logic L 2 K4. Then there is a variable free formula <p such that L + is the 
smallest logic among the extensions of L having V as their only Post complete 
extension. 
Proof Suppose V is characterized by a finite matrix (21, V). By Theorem 13.12, 
we may assume (21, V) to be O-generated. Let </?i,... ,<pn be some variable free 
formulas such that (a) = _L, (b) </?*, for i > 2, are constructed from previous 
formulas in this sequence using one of the connectives A, V, —□, (c) for 
1 < i < n, have different values ai in 21 and (d) |2i| = n. In other words, these 

O-REDUCIBILITY AND POST COMPLETENESS 
441 
formulas describe a process of generating 21 from JL. Now we define p as the 
conjunction of the following formulas, for 1 < i, j, k < n: 
D+(^i <Pj © Pk) if ai = aj 0 &k, 0 € {A, V -*}, 
D+(^i D^) if a* = 
if a% € V. 
By the definition, [</?) = V and, in particular, (21, V) |= p. 
Given a variable free formula ip with value a< in 21, put 
Lemma 13.21 For every variable free ip, D+(ip* <-> ip) G L -f p. 
Proof The proof proceeds by induction on the construction of ip. The basis of 
induction is trivial. Suppose ip = ipi © ip2, for Q € {A, V,—>}, □+(V>i V>i) € 
L + p, □+(V;2 ^2) € L + y>, ip* = Pi, ip{ = Pj, 1P2 = and a* = a7- © a*,. In 
particular, we have □+(?/>* *-> 0^2) ^ So to prove □+(?/>* ip) e L+p, 
it is sufficient to show that 
□+(V>1 0 V>2 ^1 0 ^2) € L + p, 
which is established using the induction hypothesis and the formulas 
□+(pi *-> P2) A 0+(p3 ++ Pa) -* D+(Pi 0P3 ++ P2 0 P4) 
belonging to K. 
Suppose now that ip = D^i, D+(V>i ++ ipi) € L + p, ip* = pi, and 
a* = Daj. In particular, □+(?/>* <-* □V>i) G L 4- and so to prove n+((Dipi)* *-> 
□^1) G L 4- p, it suffices to show that 
□+(n^ *-> uip{) eL + p. 
The latter is established using the induction hypothesis and the formula 
□+(pi *-> p2) -* □+(Epi *-> °P2) 
which is in K4. □ 
It follows that for every variable free formula ip, we have (21, V) f= ip iff 
ip e L + p. Indeed, if (21, V) |—ip then ip* — p± for some ai G V. By the 
definition of p, we then have ip* eL + p, from which ip e L + p. Conversely, 
suppose ip e L+p. Then ip* e L+p and, by the deduction theorem, p —► ip* e L. 
Therefore, (21, V) |= p —► ip* and, since [p) = V, we obtain (21, V) |= ip*, and 
hence (21, V) |= ip. 
Thus, L + p contains the same variable free formulas as V, which means that 
L + p has the unique Post complete extension V. □ 
Call a logic antitabular if it is consistent but does not have finite models. 
It should be clear that a consistent logic is antitabular iff all its Post complete 
extensions are not tabular. Using Theorem 13.20 we obtain 

442 
POST COMPLETENESS 
Theorem 13.22 If a logic L O K4 has infinitely many Post complete extensions 
then it also has an antitabular extension. 
Proof Observe first that every Post complete logic is either tabular or 
antitabular. Let Lj, for i G I C u, be all the distinct tabular Post complete extensions 
of L. If I is finite then we are done. Suppose I is infinite. By Theorem 13.20, 
there are variable free formulas pi such that L + pi is the smallest extension of L 
having Li as its only Post complete extension. Note that -^pj G L + (pi for i ^ j. 
Now define V = L + {-'Pi : i G I}. If V is consistent then, as any other 
logic, it has a Post complete extension which, by the definition of pi, must be 
different from all Li. Therefore, L' is antitabular. 
Suppose that V is inconsistent, i.e., there is a derivation of _L in V. Then 
we have -*pi,..., -^pn \~l -L for some n, whence, by the deduction theorem, 
Pi V ... V pn G L and so p\ V ... V pn G Ln+i* On the other hand, we have 
”■<£1 € Tn+i, ..., -"Pn € Tn+i, and hence ~'(p\ V ... V pn) G Ln+i, contrary to 
Ln+1 being consistent. □ 
Unlike 2-reducibility (see Theorem 13.8), O-reducibility turns out to be 
inherited by finitely approximable extensions of a given logic above K4. 
Theorem 13.23 Every finitely approximable extension of a generally Post 
complete logic in ExtK4 is also generally Post complete. 
Proof We consider only normal logics because for quasi-normal ones the proof 
is analogous. The observations at the beginning of this section show that every 
generally Post complete logic L G NExtK4 is characterized by a 0-generated 
algebra and extends the logic Log3K4(0)- Since here we are interested in finitely 
approximable logics, let us consider finite frames for Log3K4(0)- 
Let a*, i < a;, be some enumeration of points in 3^4 (0) and a variable 
free formula defining a* in 3k4(0) (he., x 1= ai iff x = a*). Put 
v(ai) = -+ p) V -+ -’p). 
The meaning of v(a.i) is that it is valid precisely in those transitive rooted frames 
that contain at most one point where ai is true. Then clearly 3k4(0) h= ^(^0 
for every i < u. This observation provides us with the following: 
Lemma 13.24 (i) No finite rooted frame for Log3rK4(0) has non-trivial reducts. 
(ii) The class of finite rooted frames for Log3rK4(0) coincides with the class 
of rooted generated subframes of 3k4 (0) • 
(iii) Every normal finitely approximable extension of Log ^4(0) is 
characterized by a class of rooted generated subframes 0/3^4 (0) closed under the 
formation of rooted generated subframes, with this correspondence being 1-1. 
Thus, if L 2 Log3rK4(0) is finitely approximable then it is characterized 
by a class of finite frames in which every point is definable by a variable free 
formula. It follows that L is 0-reducible and so, by Theorem 13.11, generally 
Post complete. □ 

EXERCISES AND OPEN PROBLEMS 
443 
Exercise 13.12 shows that the requirement of finite approximability in 
Theorem 13.23 is essential. 
Lemma 13.24 has one more interesting application. Together with the 
construction of Theorem 13.15 it provides us with a continuum of pretabular logics 
in NExtK4. 
Theorem 13.25 There is a continuum of pretabular logics in NExtK4. 
Proof It suffices to show that the logics L = Log2l(iV), defined in the proof of 
Theorem 13.15 (i), are pretabular in NExtK4. It should be clear that they are 
not tabular. Suppose 1/ is a pretabular extension of L in NExtK4. By 
Corollary 12.12, V is finitely approximable and, since Ql(N) is O-generated, all its 
finite rooted frames are, by Lemma 13.24, generated subframes of ^(iV). Since 
V is not tabular, it has finite frames of any depth. By the construction of #(iV), 
its every generated subframe of depth n contains all $(Nys generated subframes 
of depth < n — 2. Therefore, the classes of finite rooted frames for L and V 
coincide and so, since L is finitely approximable by its definition, L = I/. □ 
13.3 	Exercises and open problems 
Exercise 13.1 Show that, for every logic L in the intervals mentioned in 
Theorem 13.2 and every m < u, the logic Log2lL(ra) is not n-reducible for any 
n <m. 
Exercise 13.2 Prove or disprove that <rKC is 1-reducible. 
Exercise 13.3 Show that Grz.3 is 1-reducible. 
Exercise 13.4 Prove that if there are variable free formulas i < u, such 
that A ... A (fin —» <pj L for j ^ {ii,... , in}, then L has a continuum of 
generally Post complete extensions. 
Exercise 13.5 Prove that if there are variable free formulas <p*, i < a;, such 
that <ph A ... A ipin -»^V...V <pjm <£ L for {ii,..., in} n {ju... ,jm} - 0, 
then L has a continuum of Post complete extensions. 
Exercise 13.6 Prove that the intersection of generally Post complete logics is 
also generally Post complete. Is this true for sums of logics? 
Exercise 13.7 Show that every logic L in the interval [K4.3, GL.3] has 
countably many Post complete extensions in ExtL and a continuum of generally Post 
complete extensions. 
Exercise 13.8 What is the number of (generally) Post complete (normal) 
extensions of K 0 Dn_L and K4BDn? 
Exercise 13.9 Prove that a modal logic has n < u Post complete extensions in 
ExtK iff it has 2n — 1 generally Post complete extensions. 
Exercise 13.10 Give an example of a logic which is characterized by a maximal 
matrix but is not Post complete. 

444 
POST COMPLETENESS 
Exercise 13.11 Prove that all logics in ExtGL.3 are generally Post complete. 
Exercise 13.12 Construct a generally Post complete logic having a normal 
extension which is not generally Post complete. 
Exercise 13.13 Prove that GL has the same Post complete extensions as GL.3, 
namely, the logics of the roots of finite irreflexive transitive chains and also 
= GL.3 -f* re. 
Problem 13.1 Prove or disprove that Int+VlLi “1Pj) ^s m-reducible 
for m = [log2n] + 1. 
Problem 13.2 Does the map crL L preserve m-reducibility? 
Problem 13.3 Are there logics with countably many generally Post complete 
extensions? 
Problem 13.4 Do Theorems 13.20 and 13.22 hold for logics above K? 
Problem 13.5 Does the equation Log5rK4(0) = K4 0 {^(ai) : i < oj} hold? 
13.4 	Notes 
The notion of reducibility appeared first in McKinsey and Tarski (1948), where 
it was proved that S4, S5 and Int are not reducible. Later similar facts were 
established for a few other logics. Theorem 13.2 is due to Chagrov (1993). That 
KC is 2-reducible was noted by Mardaev (1987) and the key lemma in the proof 
of this result (Lemma 13.4) was proved by Blok (1977). 
Although the lattices NExtK and Extint are similar as far as the number 
of Post complete logics in them is concerned, the algorithmic problem of 
determining, given a formula </?, whether K 0 ip is Post complete is undecidable 
(Chagrov 1996), while the problem of Post completeness in Extint turns out to 
be decidable. 
In view of Makinson’s theorem, when dealing with Post complete modal 
logics we primarily consider logics without the postulated rule RN. The first results 
concerning Post completeness of modal logics were obtained by McKinsey (1944), 
who proved that S4 has only one Post complete extension and above S2 there 
are infinitely many of them. The main problem of many subsequent papers 
concerning Post completeness was to determine the set of Post complete extensions 
of certain logics and estimate its cardinality. Some results of that sort can be 
found among the exercises in Section 13.3; see also Segerberg (1972, 1976) and 
Blok and Kohler (1983). 
A considerable step in understanding the nature of Post complete logics was 
made by Makinson and Segerberg (1974), who established a connection between 
the number of Post complete extensions of a given logic and the number of 
ultrafilters in the modal algebras determining it. A similar observation was made 
in Sambin and Valentini (1980). The most complete exposition of the current 
researches of Post completeness, in particular computing the number of Post 
complete extensions of normal modal logics can be found in Bellissima (1990). 

NOTES 
445 
Note that in the polymodal case the method of studying Post completeness is 
basically the same, however the description of Post complete logics is of course 
more complicated. 
The notion of generally Post complete logic was introduced and investigated 
in Chagrov (1985b); the theorems characterizing Post complete and generally 
Post complete logics in Section 13.2 were taken from this paper. The 
remaining results in this section were proved in Chagrov (1989, 1994b), where it is 
shown, in particular, that the requirement of finite approximability is essential 
in Theorem 13.23. 

14 
INTERPOLATION 
Recall that a logic L is said to have the Craig interpolation property if, for every 
implication a —> /3 in L, there exists a formula 7, called an interpolant for a —» (3 
in L, such that a —> 7 G L, 7—> /? G L and Var7 C Varan Var/3. In this chapter 
we present the most important semantic methods of proving and disproving the 
interpolation property of modal and superintuitionistic logics. 
14.1 Interpolation theorems for certain modal systems 
First we extend the construction used in the proof of Craig’s interpolation 
theorem for Cl in order to prove the interpolation property of a few standard modal 
logics. As in that proof, our plan is, given that a —> 7 and 7 —> 0 are not in 
L for any 7 with Var7 C Vara D Var/3, to “saturate” the inseparable tableau 
to = ({a}, {/?}) to complete inseparable tableaux which describe a model for L 
realizing to. The difference is that for Cl it was sufficient to construct a 
single complete inseparable extension of to, while in the modal case to define the 
Kripke model we need, a set of such tableaux with an accessibility relation 
between them may be required. We should warn the reader that although we use 
the same terminology as in the proof of Theorem 1.28, some notions will be 
defined in a slightly different way. 
Theorem 14.1 S4 has the interpolation property. 
Proof Suppose a —> 7 ^ S4 and 7 —> (3 $ S4 for any formula 7 whose variables 
occur in both a and /?, and show that in this case a —> ^ S4. 
We shall be considering tableaux of the form t = (T, A) in which all formulas 
in T contain only variables occurring in a and formulas in A contain only 
variables from /?. Say that t is inseparable (relative to a and /?) if there is no formula 
7 such that Var7 C Varan Var/? and A*Li <Pi 7 € S4, 7 —* V^Li € S4 for 
some (pi,..., <pn G T, ipi,..., G A. The tableau t is called complete (relative 
to a and /?) if for every cp and -0 with Varcp C Vara and Var0 C Var/3, one of 
the formulas cp and ~^p is in T and one of 0 and -i0 is in A. 
Lemma 14.2 Every inseparable tableau to = (To, Ao) can be extended to a 
complete inseparable tableau. 
Proof Let pi,P2,--- and 0i,02, ••• be enumerations of all formulas whose 
variables occur in a and /?, respectively. Define tableaux t'n = (r^,A,^) and 
tn+i = (rn+i,An+i) inductively by taking, for n = 0,1,..., 
f (rnu{^n},An) 
\ (rn u {-i</?n}, An 
if this pair is inseparable 
) otherwise, 

INTERPOLATION THEOREMS FOR CERTAIN MODAL SYSTEMS 
447 
^n+1 
(r' , A' U {tin}) if this pair is inseparable 
(Tn, K U HM) Otherwise. 
Finally, we put t* = (r*, A*), where V* = Un<u, rn> A* = \Jn<UJ An. 
We show now that the tableau t* is complete and inseparable relative to 
a and /?. That t* is complete follows directly from the definition. Suppose t* 
is separable. Then for some formulas <pi,...,<pn € r*, t/q,..., G A* and 
some formula 7 containing only those variables that occur in both a and /?, we 
have AILi Vi 7 ^ S4 and 7 —► VUi £ S4. Since n,m < a;, there exists 
k < u such that <pi,..., <pn G Tfc and ^1,..., ^m G Afc, which means that tk is 
separable. 
So it remains to show that if t = (r, A) is inseparable, Var<p C Vara and 
Var^ C Var/? then 
• one of the tableaux (I? U {</?}, A) or (r U {-«p}, A) is inseparable and 
• one of the tableaux (r, A U or (r, A U {-''&}) is inseparable. 
We prove only the former claim, leaving the latter to the reader. Suppose, on 
the contrary, that both tableaux are separable, i.e., there are formulas 71, 72 
in variables occurring in both a and /? such that, for some <pi,...,<pn € T, 
^1,..., £ A, we have 
Vi A ... A <pn A <p -> 71 G S4, 71 ^1 V ... V € S4, 
<pi A ... A <pn A -*<p —> 72 G S4, 72 -> ^1 V ... V G S4. 
Then we obtain 
(Vi A ... A <pn A v?) V (</?i A ... A <pn A -i<p) -> 71 V 72 G S4, 
7i V 72 -> ^1 V ... V </>m G S4, 
which in view of 
(<Pi A ... A <pn A <p) V (</?i A ... A <pn A -iy>) <pi A ... A <pn G S4 
gives us 
<pi A ... A <pn —» 71 V 72 G S4, 71 V 72 —> ^1 V ... V G S4. 
Since Var7i V 72 C Vara D Var/?, this contradicts t being inseparable. □ 
Now we define a frame # = (W, iJ) by taking W to be the set of all 
complete and inseparable extensions of the inseparable tableau ({a},{/?}) and, for 
tableaux ti = (I?i, Ai), £2 = (r2, A2) in W, t\Rt2 iff UV £ Fi implies <p G I?2. 
Using the axioms Dp —> p and □ p —> DDp of S4, one can readily check that R 
is a quasi-order on W, i.e., $ is a frame for S4. 
Define a valuation QJ in ^ by taking for every variable p G Var (a —> /?), 
3J(p) = {(r, A) G W : either p G T or p G Var/? and p ^ A}. Put 9JI = (#, 2J). 

448 
INTERPOLATION 
Lemma 14.3 For every t = (T, A) in $ and all formulas ip and with Var<p C 
Vara, Vart/> C Var/3, 
(<m,t)t=ipiffiper, (aMj^tfiKA. 
Proof By induction on the construction of ip and t/>. The basis of induction 
follows from the definition of 2J and the completeness and inseparability of t. 
The cases of the Boolean connectives present no difficulty. So suppose ip = D<pi. 
If t |= D<pi then, for every tf = (]?', A') E 1|, we have £' |= ip\ and so, by 
the induction hypothesis, ip\ E T'. Suppose D<pi ^ I\ Then, since t is complete, 
-lUipi € T. Consider the tableau to = (ITo, Ao), where 
r0 = {-^1} U {x : nx € r}, A0 = {->x : -’nX € A}. 
We show that to is inseparable. Suppose otherwise. Then there is a formula 7 
with Var7 C Vara Pi Var/3 such that, for some formulas Dxi,..., DXn € T, 
-'°Xn+l,---,-|DXm € A, 
-»P1 A Xi A ... A Xn -+ 7 e S4, 7 -* -'Xn+l V ... V -iXm € S4. 
Using now the formulas 
□ (p A qi A ... A qn -* r) -> (Op A □#! A ... A Dgn -* Or), 
□ (r -* pi V ... \fpk) -* (Or -* Opi V ... V Opk), 
belonging to every modal logic and the fact that S4 is closed under necessitation, 
we obtain 
ipi A Dxi A ... A □ Xn —> O7 E S4, 
<>7 -> -iDXn+l V ... V “'□Xm € S4, 
contrary to t being inseparable. 
Let t' = (r', A') be a complete inseparable extension of to. By the definition 
of t0, we have tRt' and so ip\ E T', contrary to -i<pi € To C ]?' and t' being 
inseparable. 
Suppose now that D<pi e T. Then for every t' = (r',A') such that tJ?t', 
we have ip\ E V and so, by the induction hypothesis, t' f= <pi. Consequently, 
t |= Uip1. 
The formula is treated in the dual way. □ 
To complete the proof of our theorem, it remains to observe that, in view of 
Lemma 14.3, 9Jt ^ a —> /? and so a —► /3 & S4. □ 
Notice that specific properties of S4 were used in the proof above only to 
establish that £ is a frame for S4. The rest of our considerations is suitable 
for any other normal modal logic (the normality was exploited in the proof 
of Lemma 14.3). Therefore, if we exclude using the axioms □ p —> p and/or 
□p —> ODp then by the same argument we shall obtain 

INTERPOLATION THEOREMS FOR CERTAIN MODAL SYSTEMS 
449 
Theorem 14.4 The logics K, K4, T have the interpolation property. 
Observe also that the construction of the models in the proof of Theorems 14.1 
and 14.4 resembles the construction of the canonical models. For instance, we 
could use them to establish the Kripke completeness of the logics under 
consideration. Indeed, if <p $ L then T —> ip $ L and so T —> ip does not have an inter- 
polant in L; the constructed model will be then a model for L E {S4, K, K4, T} 
refuting cp. Moreover, using a somewhat subtler argument we could construct 
finite models and prove thereby the finite approximability of those logics. Such 
a construction will be described in Section 14.5, where we establish the 
interpolation property of GL. 
For a logic L E ExtK (L E Extint), we say that a formula a(p) is conservative 
in ExtL if 
a(±) A a(p) A a(q) —> a(p —> q) A a (Dp) E L 
(in the intuitionistic case the conjunct a(Dp) should be replaced with the formula 
a(p A q) A a(p V q)). If L E NExtK4, we call a(p) conservative in NExtL if 
□+(a(±) A a(p) A a(q)) —> a(p —> q) A a (Dp) E L. 
Theorem 14.5 (i) IfL has the interpolation property and formulas ai, fori E I, 
are conservative in ExtL, then L+{ai : i E 1} also has the interpolation property. 
(ii) If L E NExtK4 has the interpolation property and formulas ai, for i E I, 
are conservative in NExtL, then L 0 {a* : i E 1} also has the interpolation 
property. 
Proof We prove only (ii); the proof of (i) can be obtained by omitting all □+ 
and replacing all 0 with +. Suppose p —> ^ E L 0 {a* : i E I}. Then there is 
a finite JC /, say J = {1,..., /}, such that <p —> xj; E L 0 {at : i E J} and so, 
as easily follows from the definition of conservative formulas (see Exercise 14.1) 
and the deduction theorem for K4, 
i 
°+M ajil) A aj(pi) A ... A aj(pn)) -► (<p -»ip) € L, 
i=i 
where pi,... ,pm,Pm+i, • • • ,Pk and pm+i,... ,Pk,Pk+1, • • • ,Pn are all the vari- 
ables in <p and respectively. It follows that 
i 
°+A< Oj(±) A aj(pi) A ... A OLj(pk)) A <p —» 
i 
(□+ /\ (^(pm+i) A ... A aj(pn)) -up) € L. 
3 = 1 
Since L has the interpolation property, there is x(Pm+i, •.. ,Pfe) such that 

450 
INTERPOLATION 
l 
□+ /\(<x,(±) A otj(pi) A ... A aj(pk)) A <p —> x € L 
3 = 1 
and 
i 
x -* (□+ f\(aj(pm+1) A .. • Aaj(pn)) -*• ip) € L, 
3 =1 
which is equivalent to 
i 
D+A< ajipm+1) A ... A aj(p„)) -> (x -*• VO € L. 
3 = 1 
Then we obtain ip —> x € L 0 {a* : z € 1} and \ —> ^ € L © {a* : i € /}, i.e., x 
is an interpolant for ip —> x/j in L 0 {a* : z € I}. □ 
Corollary 14.6 There is a continuum of logics in NExtK4 having the 
interpolation property. 
Proof According to Theorem 13.15, there are a continuum of logics in NExtK4 
axiomatizable by variable free formulas which clearly are conservative. □ 
Lemma 14.7 The formulas □<>p —> OUp, DOp <-* ODp and Up <-* Op are 
conservative in NExtS4. 
Proof Exercise. □ 
As a consequence of Theorem 14.5 and Lemma 14.7 we obtain another 
Corollary 14.8 The logics S4.1, S4 0 UOp <-* OUp and Triv have the 
interpolation property. 
The following result shows that the interpolation property is preserved while 
passing from a modal logic in NExtS4 to its superintuitionistic fragment. 
Theorem 14.9 If L E NExtS4 has the interpolation property then pL has this 
property as well. 
Proof Suppose that a —> (3 E pL. Then T(a) —> T(/3) E L and so there 
is an interpolant 7' for T(a) —> T(/3) in L, which means that T(a) —> 7' € 
L and 7' —► T(/3) E L. Since T(<p).<-* □T((/?) E S4 (see Exercise 3.25) and 
T(v?(pi, • •. ,Pn)) T(<p(Dpi,..., Upn)) E S4 for every intuitionistic formula 
<p(pi, • • • we have T(a) —► U^n £ L and CI7" —► T(/3) E L, where 7" is 
obtained from 7' by prefixing □ to each of its variables. By induction on the 
construction of a modal formula • • • >Pn) one can readily show also that 
there exists an intuitionistic formula ip(pi,... ,pn) such that 
,...,Dpn) T((p(pi,... ,pn)) € S4. 
Now take an intuitionistic formula 7 such that Uy,f <-* T(7) E S4 and Var7 = 
Var7". Then we obtain T(a) —> T(7) E L and T(7) —> T((3) E L, from which 

SEMANTIC CRITERIA OF THE INTERPOLATION PROPERTY 
451 
□ (T(a) -> T(7)) G L and D(T(7) -> T(/?)) G L, and finally, a 7 e pL and 
7 —> /? G pL. □ 
Since pS4 = Int, p(S40DOp <-* ODp) = KC, pTriv = Cl, as a consequence 
of Theorems 14.1, 14.9 and Corollary 14.8 we obtain 
Corollary 14.10 The logics Int, KC and Cl have the interpolation property. 
14.2 Semantic criteria of the interpolation property 
Say that a class C of algebras is amalgamate if for every algebras 2io, 2ii, 212 in 
C such that 2lo is embedded in 211 and 2l2 by isomorphisms f\ and f2, 
respectively, there exist 21 G C and isomorphisms g\ and g2 of 2ii and 2i2 into 21 with 
ffi(ffa)) = 02(/2(a)), for any x in 2l0. 
Theorem 14.11 A si-logic L has the interpolation property iff the variety VarL 
is amalgamate. 
Proof (=>) Suppose L has the interpolation property and /1, f2 are 
isomorphisms of 2io into 2ii and 2l2, respectively, 2lo, 2li, 2i2 pseudo-Boolean algebras 
for L (with universes Ao, Ai, A2). Without loss of generality we will assume 
2lo to be a subalgebra of 2ii and 2l2, i.e., that fi and f2 are the identity maps: 
fi(x) = f2(x) = x for all x G Aq. With each element a G A*, i = 0,1,2, we 
associate a variable pla in such a way that, for a G Aq, p® = pla = p\. Denote 
by Li the (intuitionistic) language with the variables pla, for a G A*, i = 0,1,2, 
and let £ = £\ U C2. We will not distinguish between terms and formulas in the 
languages we have just introduced and denote them by the same symbols. Also 
we will assume that £ is the language of our logic L. 
Let us fix the valuation 2J* of £i in 2lif defined by 23i(pla) = a, and put, for 
^ = 1,2, 
E* = {ip G ForA : ID fa) = T}. 
It is clear that L D ForA C E* and that E* is closed under modus ponens. Let 
E be the closure of Ei U E2 U L under modus ponens. We show that, for every 
ip G For£i, xj; G For£j such that {i, j) = {1,2}, 
ip —> ^ G E iff 3\ G For£0 E^). (14.1) 
The “if’ part of (14.1) is obvious, since E is closed under MP and so under the 
rule ip -> x, X 
Suppose now that ip —► xj; G E. This means that there is a substitutionless 
derivation of ip —> xfr in L from some finite sets of assumptions C E* and 
Tj C By the deduction theorem, we then have 
Al\ A Ar*->(*>-> 10 GL 
and so 

452 
INTERPOLATION 
Since L has the interpolation property, there is a formula \ € ForLo such that 
/\Fi A ip —> x ^ f\Tj —* (x ^) € L, 
from which, by MP, ip —> x € £» and x —► ^ This establishes the “only if’ 
part of (14.1). 
Notice, by the way, that putting <p = T in (14.1), we obtain that EnForLj = 
Ej, for j = 1,2. 
Now we construct an algebra 21 by taking the set {||</?|| • <p € E} as its universe 
A, where |M| = ^ € E} and putting _L = jj_L||, \\(p\\ © ||^|| = ||<p © ^||, 
for 0 G {A, V,—>}. This definition is correct because Int C L C E. It should be 
also clear that 21 G VarL. 
Define maps gi from 21* into 21, for i = 1,2, by taking <7* (a) = ||p* ||. By the 
definition, gi is an injection. Let us show that gi is a homomorphism. First, we 
have <7i(-L) = ||pj_|| = ||_L|| = _L, because 2J*(pj_) = _L. Second, suppose c = a 0 b 
in 21*, for 0 G {A, V, -*}. Then 2J*(p* 0p£) = 2J*(pj.) and so 
0i(« © b) = IbaGtll = Ibi ©pill = bill © bill = 9i(a) © 9i(b). 
Thus, gi is an embedding of 21* in 21. And for a G Ao, we have 
0i(/i(a)) = 01 (ffl) = ball = 02(a) = 02(/2(a)). 
(4=) Assuming VarL to be amalgamate, we show that L has the interpolation 
property. To this end we require the following: 
Lemma 14.12 Suppose 2lo is a subalgebra of pseudo-Boolean algebras 2li and 
2I2, a G Ai, b G A2 and there is no c G Ao such that a <1 c <2 6 (where <* is 
the partial order and A* the universe in 21*/ Then there are prime filters Vi in 
2li and V2 in 2I2 such that a G Vi, 6 ^ V2 and Vi Pi Ao = V2 n Ao- 
Proof We remind the reader that a set of elements in 21* is a filter (ideal) iff it 
can be represented in the form [X)i (respectively, (X]*) for some X C A*. Take 
the sets 
X = {x G A0 : a <1 x}, y = {y G A0 : y <2 6}. 
By the condition of the lemma, X Pi Y = 0. We are going to extend Y to some 
ideal A2 in 2I2 in such a way that b G A2 and X n A2 = 0. To this end consider 
the family 
/*2 = {AC A2: A = (A]2, {b}uY C A, XnA = 0}. 
is not empty, because (6)2 € /*2- The union of any chain (with respect to C) 
of T<i s elements is again in So, by Zorn’s lemma, T2 contains a maximal 
element, which we denote by A2. 

SEMANTIC CRITERIA OF THE INTERPOLATION PROPERTY 
453 
The ideal A2 turns out to be prime, i.e., xAy £ A2 implies x £ A2 or y e A2. 
Indeed, suppose x A y £ A2 but x £ A2 and y £ A2. Since A2 is maximal in F2, 
we then have 
X fl ({x} U A2]2 7^ 0 7^ X H ({y} U A^2? 
i.e., A2 contains elements u and v such that a <1 x V u, a <1 y V u, with x V u 
and y V v being in 2lo- It follows that 
a <1 (x V u) A (y V v) = (x A y) V (x A u) V (u A y) V (u A u) € A2. 
And since (x V u) A (y V u) is in 2lo, it belongs to X, contrary to X fl A2 = 0. 
By Proposition 7.27, V2 = A2 — A2 is a prime filter in 212- Put Vo = V2 fl Ao 
and Ao = A2DA0. By the definition, we have X C Vo, Y C Ao and Vofi Ao = 0. 
Now we extend the set {a} U Vo to obtain the filter Vi we need. Consider the 
family 
Ti = {vai: V = [V)i, {a}UV0CV, VnA0 = 0}. 
To prove that it is not empty, it suffices to show that [{a}uVo)i £ T\, which in 
turn follows from [{a} U Vo)i fl Ao = 0. So suppose that x £ [{a} U Vo)i fl Ao- 
Then for some z £ Vo, we have a A z <1 x, i.e., a <1 z —> x and x £ Aq. By the 
definition ofX,z—> x £ X C Vo, which together with z £ Vo yields x £ Vo- 
Therefore, x £ Vo n Ao, which is a contradiction. 
Thus, T\ is not empty. The union of any chain of .TVs elements also belongs 
to So by Zorn’s lemma, contains a maximal (with respect to C) element. 
Denote it by Vi and show that the filter Vi is prime. Suppose x V|/ £ V1 but 
x£ Vi and y £ Vi. Then 
[{x} U Vi)i D A0 ^ 0 7^ [{2/} U Vi)i n A0, 
i.e., Vi contains ux and uy such that, for some vx,vy £ Ao, we have 
x A ux i/j, y A Uy Uy* 
It follows that 
(x A ux) V (y A uy) <1 vx V vy £ A0. 
The left part of this inequality can be transformed in the following way: 
(x A ux) V (y A uy) = (x V y) A (x V uy) A (ux Vy) A (ux V uy). 
Here every conjunct belongs to Vi and so the whole conjunction is in Vi, from 
which vxWvy £ Vi. Thus, we have obtained that vxWvy £ Vi fl Ao, contrary to 
Vi fl Aq — 0. 
Observe now that, by the definition, a £ Vi and b ^ V2* So it remains to 
check that Vi fl Ao = V2 fl Ao. Suppose x £ Vi fl Ao* Then x ^ Ao, whence 
x ^ A2 and so x £ V2 n A0. Conversely, if x £ V2 n A0 then x £ Vo and so 
x £ Vi, because Vo Q Vi, from which x £ Vi fl Aq. □ 

454 
INTERPOLATION 
We are in a position now to prove the part (<=) in Theorem 14.11. Suppose 
tp{pu and i/>(qu..., qn, ri,..., n) are formulas for which there 
is no formula x(<7i> • • •, <Zn) such that ip —► x € L and x € L or, which is the 
same, 21 f= cp -h► x and 211= x —»f°r any 21 £ VarL. We show that in this case 
there exists an algebra 21 € VarL refuting (p —> -0. 
Let 21q, 2l'x and 2l2 be the free algebras in VarL generated by the sets 
{ci,..., cn}, {al5..., om,d,..., Cn} and {ci,..., c*, 61,..., bt}, respectively 
According to this definition, 21q is a subalgebra of both 21* and 2l2. By Lemma 14.12, 
there are prime filters Vi in 21^ and V2 in 2l2 such that (p(a 1,..., am, C\,..., cn) € 
Vi and ^(ci,..., Cn, 61,..., 6/) £ V2. Put 2li = Bi/Vi, 2l2 = 2l2/V2. Then 
l|(^(Qrl, . . • , dfn? ^1 j • • • > On)|| Vi ||^(^1? • • • » ^15 • • • ? bl) || V2 7^ 
Construct an algebra 2lo by taking Ao = {||a|| Vi • a € A^}. By the definition, 2lo 
is a subalgebra of 2li, i.e., is embedded in 2li by the map fi{x) = x. We show 
that 2lo is embedded in 2l2 by the map /2GWIV1) = IMIv2- 
For every © € {A, V, —»} and every ||a||va, ||6||Vi £ Ao we have 
/2(||a||vi O IHIvj) = /2(||a©6||v1) = \\d © fr|| v2 = 
IWIv2 © ||&||v2 = /2GHV1) © /a(IHIvJ- 
Besides, /2(||_L||vi) = ||JL||v2 = -L € A2. Thus, /2 is a homomorphism. Let us 
show that it is injective: 
IMIvi = ll&llvi iff a «-► 6 € Vi 
iff a «-► 6 € V2 (since Vi n A^ = V2 n A'0) 
iff ||a||v2 = ||6||va, i-e., /2(||o||Vi) = ^GI&llvJ- 
Since VarL is amalgamable, there are an algebra 21 for L and isomorphisms 
gi and g2 of 2li and 2l2 into 21, respectively, such that gi(fi(x)) = ^2(/2(^))> for 
every x € Aq. Define a valuation 2J in 21 by taking 
®(Pi) = Si(IWIvi), for i = 
2%) = SidMvJ = 52(l|c,i|va), for j = 1,... ,n, 
*(rfc) = fladlMka), for k = 1,... ,1. 
Then 
W(<P(Pi,--->Pm,qi,---,qn)) = T, W(ip(qi,...,qn,ri,...,n)) ± T, 
from which 21 ^ ip —> ^ and so <p ip £ L. □ 
It is worth noting that the property of amalgamability can be strengthened 
without violating Theorem 14.11. Say that a class C of algebras is superamal- 
gamable if the condition of amalgamability is satisfied in C for every 2lo, 2li, 2l2, 
/1, /2, and if x € A*, y € Aj, {ij} = {1,2}, then 

INTERPOLATION IN LOGICS ABOVE LC AND S4.3 
455 
9i(x) < 9j(y) implies 3z € A0 (x << fi(z) and fj(z) <jy). 
Let us supplement the proof of (=>) in Theorem 14.11 to establish that VarL 
is superamalgamable. Suppose a £ Ai,b £ Aj, {i,j} = {1,2}, and gi(a) < gj(b). 
Then &(a) -> gj(b) = T and so \\fa —*■ pj|| = T, i.e., pi -> pj e E. By (14.1), 
we have x € For£o with 2J(x) = c such that a <* c = fi(c) and c = fj(c) <j b. 
Thus, we obtain 
Theorem 14.13 A si-logic L has the interpolation property iffV&TL is 
superamalgamable. 
Observe also that in the proof of (<*=) in Theorem 14.11 we actually used the 
amalgamability of the class of Vs algebras satisfying the condition 
x V y = T implies x = T or y = T. 
Such algebras are called well-connected. (The condition was ensured by the fact 
that the filters Vi and V2 were prime.) Thus, we have another variant of the 
criterion for the interpolation property. 
Theorem 14.14 A si-logic L has the interpolation property iff its class of well- 
connected pseudo-Boolean algebras is amalgamable. 
Let us now turn to modal logics. The situation here is a bit more complicated. 
First of all, we have 
Theorem 14.15 A normal modal logic L has the interpolation property iffVaxL 
is superamalgamable. 
Proof Similar to the proofs of Theorems 14.11 and 14.13. □ 
However, the amalgamability corresponds to a different variant of the 
interpolation property. Say that a normal modal logic L has the interpolation property 
for derivability if, for every formulas ip and -0 such that p \~*L -0, there is a 
formula x containing only common variables in tp and -0 and such that <p\~*Lx and 
xn ^ 
Theorem 14.16 A normal modal logic L has the interpolation property for 
derivability iffVaxL is amalgamable. 
Proof Similar to the proof of Theorem 14.11. □ 
In Section 14.4 we shall see examples of logics which have the interpolation 
property for derivability but do not have the Craig interpolation property. 
14.3 	Interpolation in logics above LC and S4.3 
In this section we give a complete description of “linear” modal and si-logics 
with the interpolation property and in the next one extend it to the whole classes 
Extint and NExtS4. First we consider si-logics with linear frames. 
Theorem 14.17 The logic LC = Int + (p —■► q) V (q —> p) has the interpolation 
property. 

456 
INTERPOLATION 
Proof According to Theorem 14.14, it suffices to show that the class of well- 
connected algebras in VarLC is amalgamable. This class coincides with the class 
of all linearly ordered pseudo-Boolean algebras. Indeed, if (a —> b) V (b —> a) = T 
in a well-connected algebra then a —> 6 = T or 6 —> a = T, i.e., either a < b or 
b < a. 
Let 2lo be a subalgebra of linear algebras 211 and 212- If one of these algebras is 
degenerate then the rest are also degenerate and the condition of amalgamability 
is trivially satisfied. So suppose these algebras are non-degenerate. 
We construct 21 in the following way. As its universe A we take A\U A2. Since 
the operations in a pseudo-Boolean algebra are completely determined by the 
partial order < in it, it suffices to define < in 21 so that (A, <) be a linear order 
with greatest and least elements and (Ai,<i), (A2y<2) could be embedded in 
(A, <)* preserving T and _L. For x,y € A, put 
x <' y iff (x, y e A\ A x <1 y) V (x, y e A2 A x <2 y) V 
(x £ Ai A y e A2 A 3z e Ai n A2 (x <1 z a z <2 y)) v 
(x € A2 A y e Ai A 3z € Ai n A2 (x <2 z A z <1 y)). 
It is easily checked that (A, <') is a partial order with the greatest and least 
elements T and _L and, for every x, y £ A*, i = 1,2, we have x <' y iff x <* y. 
Now we supplement <' to a linear order <. This can be done, for instance, like 
this: take any well-ordering of A x A and, starting with <', add to it by transfinite 
induction the next pair (x,y) from Ax A if x and y are still incomparable after 
the preceding step and then form the transitive closure of the new relation. The 
resulting linear order will clearly satisfy the properties we need. □ 
Denote by LCn the logic of the n-point linear frame (= the logic of the 
n + 1-element linear pseudo-Boolean algebra). 
Theorem 14.18 LC2 has the interpolation property. 
Proof There are only two well-connected non-degenerate LC2-algebras, namely 
2- and 3-element chains. A simple direct check of all possible cases (see, for 
example, Fig. 14.1 in which dash arrows show embeddings) establishes that this 
class of algebras is amalgamable. □ 
Thus, we have four “linear” si-logics (including the inconsistent one) having 
the interpolation property. And it turns out that that is all. 
Theorem 14.19 Any logic L £ ExtLC different from LC, LC2, Cl and For£ 
does not have the interpolation property. 
Proof Suppose L has the interpolation property and differs from LC2, Cl and 
For£. We show then that L = LC. 
It follows from our assumption that there is a well-connected algebra for L 
containing at least 4 elements and so there is a 4-element algebra (e.g. a suitable 
subalgebra of the former one). We are going to prove by induction on n that 

INTERPOLATION IN LOGICS ABOVE LC AND S4.3 
457 
a2 
< 
2l^x 
\ 
v v > 
/ o 
/ 
a, 
Fig. 14.1. 
VarL contains n-element well-connected algebras for every n < u. This is true 
for n = 1,2,3,4. 
Suppose VarL contains an n-element linear algebra (and so m-element ones 
as well, for 1 < m < n) and show that an n 4- 1-element linear algebra belongs 
to VarL too. Let 2lo, 211, 212 be the pseudo-Boolean algebras defined by the 
following linear orderings of their elements: 
• 2lo is _L < a < T, 
• 2li is 1 < a < b < T, 
• 2I2 is _L < ci < ... < cn_3 < a < T. 
By the definition, 2lo is a subalgebra of both 2li and 2I2- Since L has the 
interpolation property, there must be a well-connected algebra 21 for L containing 
2li and 2I2 as its subalgebras. This means that 21 contains an n + 1-element 
subalgebra determined by the order 
1 	< ci < ... < cn_3 < a < b < T. 
Thus, the class of all finite linear algebras, characterizing LC, is contained in 
VarL. It follows that L C LC and so L — LC. □ 
Let us consider now extensions of S4.3. By Theorem 14.9 and the results of 
this section, of all'logics in NExtS4.3 only modal companions of LC, LC2, Cl 
and For£ may have the interpolation property. 
Theorem 14.20 No logic in p~lLC has the interpolation property. 
Proof We show that there is a formula a —> (3 which belongs to all logics in 
p~lLC = [S4.3, Grz.3] but does not have an interpolant in any of them. Let 
a(p, q, r) = D((p —► Dr) A (□(<? —► Dr) —> Dr) A (Dr —> p V q)), 
f3(p, q, r') = □((<? —► Dr') A (D(p —► Or') —^ Dr') A (Dr' —> p V q)) —^ p V q. 

458 
INTERPOLATION 
It is not difficult to verify that a —> (3 is valid in every finite frame for S4.3 and 
so belongs to S4.3. It remains to show that there is no formula 7(p, q) such that 
a —> 7 e Grz.3 and 7 —> (3 e Grz.3. Let £ = (W, R) be the frame depicted in 
Fig. 8.3 (a) and = (W',R') its subframe obtained by removing the point lj. 
Clearly, both £ and are frames for Grz.3. Put 2lo = 2li = 2I2 = and 
define embeddings fi of 2lo in 21*, for z = 1,2, as follows. 
Let Vi, V2 be non-principal ultrafilters in 2lo such that a = {2n : n < lj} G 
Vi — V2. To show that such ultrafilters exist, consider the filter V of cofinite 
sets in 2l0. The filters [V U {a}) and [V U - {a}) are then non-degenerate. (For 
otherwise, if say 0 £ [V U {a}), we would have b n a = 0 for some cofinite set 
b in 2lo, which is impossible.) And we can take as Vi and V2 any ultrafilters 
containing [Vu{a}) and [VU-{a}), respectively, which clearly are non-principal 
and satisfy the property we need. 
Define fi by taking, for any x in 2lo, 
f(r) f*UM if X € Vi 
Jt' ' ^ x otherwise 
and show that it is an embedding of 2lo in 21*. Clearly, fi is an injection. So it 
suffices to prove that it preserves n, - and □. 
Consider fi(x n y), for x,y C Wr. If x n y e Vi then x € Vi and y € Vi, i.e., 
fi(x) = xU {cj}, fi(y) =yU{u} and so 
fi{x n y) = (x n y) U M = (x U {w}) n (y U {w}) = fi(x) n fi(y). 
And if x n y £ Vi then x £ Vi or y ^ Vi, i.e., either uj £ fi(x) = x or 
w £ fi(y) = V, and so fr(x fi y) = x n y = fi(x) n fi{y). 
Now take fi(W' — x), x C W'. IfW'-x e Vi then x £ Vi, i.e., uj £ fi(x) = x. 
Then fi(W' - x) = (W' - x) U {lj} = W - x = W - fi(x). And if Wf - x Vi 
then x e Vi, i.e., fi(x) = x U {cj}, and so 
fi(W’ - x) = Wf - x = W - (x U {lj}) =W- fi(x). 
Finally, consider fi(O0x), for x C W' (here the subscript near □ indicates in 
which algebra this □ operates). There are three types of elements of the form 
□o£ in 2lo: {lj + 1, m : m < u}, {m : m < lj}, and {0,1,..., n} (n < lj). The 
former two sets x are cofinite and besides x = Doa;. In this case we have 
fi(O0x) = D0x U {lj} = Di(xU {lj}) = □iZi(x). 
If Do# = {0,... ,n} then n + 1 ^ x. Therefore, Oxx = Di(x U {cj}) = {0,... ,n} 
and so /i(D0x) = □i/i(x) no matter whether x is in Vi. 
Define valuations 23i in the algebras 2li, for i = 0,1,2, by taking 
9Jo(p) = {2n + 1 : n < lj}, 2Jo(g) = {2n : n < ct;}(= a), 

INTERPOLATION IN LOGICS ABOVE LC AND S4.3 
459 
9Ji(p) = {2n + 1 : n < w}, ^(p) = {2n + 1 : n < w} U {w}, 
2Ji(q) = {2n : n < a;} U {w}, %f2(q) = {2n : n < w}, 
51i(r) = {n : n < w}, = {n: n < w}. 
Notice that 
/i(®o(p)) = ®i(p), /i(aJo(«)) = 
/2(®o(p)) =®2(p), /2(®o(9)) = ®2(fl) 
and so, for any formula <p(p,q), we have 
/iCQJoCv’Cp.«))) = 9?i(v>(p.g)), /2(9Jo(v>(p.9))) = W2(<p(p,q))- 
Suppose now that y(p,g) is an interpolant for a —► (3 in Grz.3, i.e., a —> 7 £ 
Grz.3 and 7 —> (3 £ Grz.3. Then both formulas must be valid in the algebras 
under consideration, in particular, 
®i(a) - 
□i((®i(p) =>i °i9Ji(r)) H Di DAW) D □ i©i(r)))n 
(□i®i(r) Di%i(p)V%i(q)) = 
□ 1 (W H (Di(W - {a;}) Di □ iQJi(r)) fl W) = 
□ i((W - {a;,a; + 1}) D (W — {u,u + 1})) = W C ^(7), 
i.e., ©1(7) = W, and 
9J2(7) C ©2(/?) = 
®2(0((g —► &s) A (D(p Ds) -> □$) A (□$ ->pV <?))) D2 2*2(p V q) = 
W D2 5J2(p Vg) = W2{pVq) = W-{lj + 1}^W, 
i.e., ©2(7) 7^ W. Since /* is an embedding, we have ©0(7) = = 
frx(W) = W' and so 9J2(7) = /2(©0(7)) = /2(W") = IV, contrary to ©2(7) ^ 
W. □ 
Remark Note that the formula a used in the proof above was “boxed”. This 
means that in fact we have established a stronger result: no logic in p_1LC has 
the interpolation property for derivability. 
Let us consider now the set p~lCl = {Log(£ln : 1 < n < uj} and p~lLC2 = 
{Log<£lJ^ : 1 < n, m < cj}, where <£[n is the n-point cluster and is the chain 
of two clusters, the first with m and the last with n points. We remind the reader 
that Log(£lw = S5, Log(£li = Triv. 
Theorem 14.21 In p~lCl only S5, Log(£l2 and Triv have the interpolation 
property. In p“1LC2 only Log<£[* and LogClJ, for n = 1,2,<j, have the 
interpolation property. 

460 
INTERPOLATION 
Fig. 14.3. 
Proof The proof involves neither new ideas nor methods as compared with 
the proofs of Theorems 14.17-14.19. For example, in the same way as in the 
proof of Theorem 14.19 we constructed n-point linear frames with the help of 
the 3-point one and the amalgamation* property (for n = 4 the construction 
is shown in Fig. 14.2 (a), where <£t)n is the linear frame with n points and 
dash arrows indicate reductions), starting with the 3-point cluster and using 
the (super)amalgamability we can “grow” arbitrary finite clusters (see Fig. 14.2 
(b)). □ 
14.4 	Interpolation in Extint and NExtS4 
Now we describe all si-logics and normal extensions of S4 with the interpolation 
property. Since the proofs are of the same sort as those of Theorems 14.17-14.19 
(though technically somewhat more involved), we confine ourselves here only to 

INTERPOLATION IN EXTINT AND NEXTS4 
461 
Fig. 14.4. 
a rough sketch, hoping that the interested reader will be able to complete the 
details. 
Theorem 14.22 A si-logic has the interpolation property iff it is one of 
Int, KC, Int + 6^2, Int + 6c£2 + 
/?( 
) = Log 
LC, LC2, Cl, For£. 
Proof The fact that all these logics have the interpolation property was partly 
already proved (see Corollary 14.10 and Theorems 14.17, 14.18). The 
interpolation property of Int + &d2 = Log#!* and Log#! (see Fig. 12.2) is established in 
the same way as Theorems 14.17 and 14.18. (Here and below we use the notations 
introduced in Section 12.3.) 
Suppose now that L is a si-logic with the interpolation property different 
from the eight logics listed above. By Theorem 14.19, L ^ ExtLC and so at least 
one of the frames or £§ in Fig. 12.2 validates L. 
Suppose £4 |= L and consider two cases: (£l)3 ^ L and <£f)3 f= L. In the former 
case L is of depth 2 and, since L ^ {Cl, Log^l, For£}, must be a frame for 
L. By the standard amalgamation argument we can prove then that £4 (= L for 
every n < uj. For n = 4 the construction is shown in Fig. 14.3 (of course, we do 
not obtain £4 immediately; first we get a (general) frame $ \= L reducible to 
both copies of £4 in the proper way and then show that 5 is reducible to £4)- 
But then L = Log#!* = L 4- bd,2, which is a contradiction. 
Thus (£f)3 |= L holds. Notice that starting with and (£()3 and using the 
amalgamation property we can construct #4 and so 3^, for every n < u. Indeed, 
first we obtain the frame 0i as is shown in Fig. 14.4, then 02 as in Fig. 14.5 and 
finally 63 as in Fig. 14.6, which is clearly reducible to £4- And using <tf)3 and #4, 
n < uj, we can construct any finite tree (which can easily be shown by induction 

462 
INTERPOLATION 
fi(bo) = 0,0 
h({bi,b2,b3}) = ai 
f2(co) = o0 
M{ci,c2}) = ax 
9i(do) = bo 
9i({di,d3}) = b2 
9i(.d2) = bi 
9i(d4) = b3 
92{do) = co 
g2(di) = ci 
92({d2,d3,d4}) = c2 
Fig. 14.5. 
on the number of points in trees). But the class of finite trees characterizes Int, 
i.e., L = Int, which is again a contradiction. 
It follows that #§ |— L and so <£f)3 |= L, because <£f)3 is a reduct of 3$. 
Therefore, the class of frames for L contains all finite chains <£f)n, n < u. From 
<£f)3 and by the amalgamation property we can construct #5 (see Fig. 14.7). 
Now observe that and #5 are obtained from <£f)3 and #4 by adding to them 
last points. And if we add last points to the frames in Fig. 14.3-14.6 and connect 
them by reduction arrows then we can construct arbitrary finite trees with an 
added top point. This means that L C KC. But since £4 L, we must have 
L = KC, contrary to our choice of L. 
We have considered all possible cases and everywhere arrived at a 
contradiction. Therefore, such a logic L does not exist. □ 
Let us turn now to NExtS4. For a si-logic L and n,m < a>, we denote by 
M(L, m, n) the modal logic above S4 characterized by the class of frames $ such 
that p$ is a finite frame for L, final clusters in $ contain at most m points and 
the remaining (non-final) clusters at most n points. Although the following two 
theorems, presented here without proofs, do not give an exhaustive description of 
logics in NExtS4 with the interpolation property (for derivability), they provide 
us with finite lists of logics containing all of them. 
Theorem 14.23 (i) The following logics have the interpolation property: 
M(Int,n,<j), Af(KC,n,w), 
M(Int + bd,2,n, 1), M(Int + bd,2, l,n), 
M (Log^f ,n, 1), M(Log<\/>, l,n), 
M(LC2,n,l), M(LCa, for n = 1,2,u/, 

INTERPOLATION IN EXTENSIONS OF GL 
463 
?&4 
©2 °^frl \ 
T>bo 
°^3 oc4 
°^1 0 
02 
C2 
CO 
Pi(^o) = fy) 
9i(di) = 6i 
9i({d2,d5}) = 64 
#1(^3) = fr2 
Pl(^4) = fr3 
^2(^0) = Co 
g2(di) = Ci 
92({d2,ds}) = C3 
^2(^3) = C2 
02 (^4) = C4 
/l(fro) = Go, /l({frl,fr3» = «2, /l(fr2) = ai, /l(fr4) = «3 
/2(co) = ao, /2({ci,C4}) = <23, /2(C2) = «1, /2(C3) = &2 
Fig. 14.6. 
S5, Log£[2, Triv, Grz, Grz.2, ForA4£. 
(ii) Each normal logic above S4 having the interpolation property and different 
from the logics mentioned in (i) is contained in the following list: 
M(Int, 1,2), M(Int,2,1), Af(Int,2,2), Af(Int,o;, 1), Af(Int,o;,2), 
M(KC, 1,2), M(KC,2,1), M(KC,2,2), M(KC>,1), M(KC,u;,2). 
Theorem 14.24 (i) The following logics have the interpolation property for 
derivability, but do not have the (plain) interpolation property: 
M(Int -f bd,2, m, n), M(Log 
m,n), 
Af(LC2,ra,n), 
where m,n € {2,a;}. 
(ii) Each normal extension of S4 having the interpolation property for 
derivability and different from the logics mentioned in (i) is contained in the list of 
Theorem 14-23 (ii). 
14.5 	Interpolation in extensions of GL 
Theorem 14.25 GL has the interpolation property. 
Proof Suppose a —► f3 has no interpolant in GL. Our goal is to construct a 
finite irreflexive transitive frame refuting a —► (3. 
Let £ = (r,A)bea finite tableau all formulas in which are constructed from 
variables and their negations using the connectives A, V, □, O. Without loss 

464 
INTERPOLATION 
/i(M = ao 
9i{do) = bo 
9i(di) — b 1 
9i{{dz,di}) = bz 
h({bM) = a2 
9i(d2) - b2 
/1 (^2) = a\ 
92(do) = Co 
f2(co) = ao 
g2{d2) - ci 
/2({C2,C3}) = a2 
92({di,d4}) = c3 
f2(ci) = a\ 
92{dz) = c2 
Fig. 14.7. 
of generality we will assume a and /? to be formulas of that sort. Say that t is 
separable (relative to a and (3) if there is a formula 7 with Var7 C Varafl Var/? 
such that /\ T —► 7 € GL and 7 —► V A G GL. 
It should be clear that if t = (T, A) is a finite inseparable tableau then taking 
the closure of it under the saturation rules (SR1)-(SR4) (see Section 1.2) we can 
obtain a finite inseparable tableau satisfying (S1)-(S4). It will be denoted by 
W = ( rr^,LAj). 
Now we construct by induction a finite rooted model for GL refuting a —► (3. 
As its root we take the tableau (raH, l/?j). If we have already put in our model a 
tableau t = (T, A) and it has not been considered yet, then for every Oip e T and 
every Dip e A, we add to the model the tableaux t\ = (Ti, Ai) and 12 = (T2, A2) 
in which 
Ti = r{x, ox, □(->¥>)', 9 ■ Dx e rp, Ai = l{x, Ox •. Ox e A}j , 
r2 =r{x,Ox: DX e r}i, A2 = l{x,0x,0(-.V,),)^ : OxeA}j, 
where (-»</?)' and (->'0)' are formulas equivalent to -«/? and -1 -0, respectively, and 
containing -< only prefixed to variables (and no —►, of course). 
Lemma 14.26 Iftis inseparable then t\ and £2 are also inseparable. 
Proof We consider only t\, because £2 is treated in the dual way. Suppose t\ is 
separable, i.e., there is a formula 7 containing only common variables in a and 
(3 and such that f\T\ —5► 7 £ GL and 7 —► V^i € GL. Then with the help of 
the formulas D(p A q —> r) —► (Dp A Oq —► Or) and D(p —j► q) —► (Op —> Oq) 
belonging to any modal logic, we obtain 
0 /\{x, DX : DX6r}A 0(D-1V? A <p) -> O7 G GL, 
O7 —► o V(x,Ox: 0X € A} € GL. 

INTERPOLATION IN EXTENSIONS OF GL 
465 
And since 0(m-i<p A p), m(x A □*) and 0(x V Ox) are equivalent in GL to the 
formulas Op, and Ox, respectively, we have 
/\{DX : DX € r} A Oi/J —> O7 € GL, O7 -» \f{0X : 0X G A} G GL, 
whence f\ T —> O7 e GL and O7 —» V A e GL, contrary to t being inseparable. 
□ 
Put tR'ti and tR't2- The process of adding new tableaux must eventually 
terminate, since each step reduces the number of formulas of the form Op and 
in the left and right parts of tableaux, respectively: having appeared once 
such a formula vanishes at the next step and in view of □(-!(/?)', 0(-i-0)' and 
Lemma 14.26 cannot appear again. Let W be the set of all tableaux constructed 
in this way and R the transitive closure of R'. Clearly, the resulting frame 5 = 
(W, R) is transitive and irreflexive and so 5 H GL. Define a valuation DJ in 5 by 
taking, for each variable p, 
qj(p) = {(r,A)gW: per}. 
To show that DJI = (5,2J) refutes a —> (3, by induction on the construction of p 
one can readily prove that, for every t = (T, A) e W, if p € T then (DJl,t) |= p 
and if p e A then (DJI, t) p. □ 
Unlike NExtS4, there are much more logics with the interpolation property in 
NExtGL. More precisely, we have the following strengthening of Corollary 14.6: 
Theorem 14.27 NExtGL contains a continuum of logics with the interpolation 
property. 
Proof By Theorems 14.25 and 14.5, it suffices to present a continuum of logics 
in NExtGL axiomatizable by conservative formulas. For i <u, we put 
ai = n+(Oi+1T A Di+2_L -> Di+1p V □i+1-<p). 
Lemma 14.28 Each formula a* is conservative in NExtGL. 
Proof We need to show that 
□+ck(-L) a D+Oitp) A D+ai(q) Oi(p -+q) € GL, (14.2) 
□+ai(l) A a+ai(p) -» ai(Dp) € GL. (14.3) 
Suppose (14.2) does not hold, which means that this formula is false at a point 
x in some model for GL, i.e., 
x (= 0+ai(±) A □+ai(p) A □+ai(g) 
x on(p -► q). 
(14.4) 
(14.5) 

466 
INTERPOLATION 
Cl C2 Cj_i Cj 
cj+1 
bi 62 frj-i frj 
Fig. 14.8. 
frj+1 
It follows from (14.5) that there is y G :c| such that 
y (= Oi+1T A □i+2_L, 
(14.6) 
and so, for some yi, j/2 € t/Tl+1, we have 
(14.7) 
yi\=p, yiftq 
(14.8) 
and y2 ^ “1(P -► <?), he., 2/2 ^ P or 2/2 |= If 2/2 b V then, by (14.6) and (14.8), 
we must have x ^ c*i(p), contrary to (14.4). And if 2/2 |= £ then, using (14.6) 
and (14.8), we obtain x |b oii{q), which is again a contradiction. 
To prove (14.3) it is sufficient to notice that a*(dp) € GL. Indeed, we have 
□*+2_l_ □<+!Qp G GL and so 0<+1T A ni+2± -► Di+1Dp V Di+1^Dp e GL. 
□ 
For every N C cj, put 
GL(iV) = GL © {a* : i e N}. 
Since the model DJI = (5,®), where 5 is the frame shown in Fig. 14.8, j £ 
N and DJ(p) = {6J+i}, separates olj (refuted at a) from GL(iV), GL(iVi) ^ 
G\j{N2) whenever N\ / iV2. Thus, we have a continuum of normal extensions 
of GL which, by Lemma 14.28, Theorems 14.5 and 14.25, have the interpolation 
property. □ 
On the other hand we have 
Theorem 14.29 NExtGL contains a continuum of logics without the 
interpolation property. 
Proof Let a^, for i < a;, be the formulas introduced in the proof of 
Theorem 14.27. For N C uj - {0,1,2,3,4}, we put 
GL(N) = GL © {ai : i G N} © 0 V 7, 
where 

467 
INTERPOLATION IN EXTENSIONS OF GL 
/? = □+(D31 -» □(□21 AOT^p)V A OT —* ->p)), 
7 = □+(D4! -> □ (□3J_ A 02T -> q) V □ (□3_L A 02T -► -.g)). 
Observe that the frames of the form shown in Fig. 14.8 validate both f3 and 7 
and so, for every j ^ N, j > 4, we have otj GL(iV). Therefore, GL(iVi) ^ 
GL(iV2) whenever N\ ^ iV2. It remains to prove that GL(N) does not have the 
interpolation property. 
We show that the formula ——> 7, which clearly is in GL(iV) (because it 
is equivalent to (3 V 7) has no interpolant in GL(iV). Suppose otherwise. Then 
there is a variable free formula 6 such that 
GL(iV), <5 —> 7 G GL(iV). 
According to the classification of the variable free formulas in GL given in 
Theorem 8.87, 6 has one of the forms 
6 = -L V ipix V ... V (pin or 6 = V (ph V ... V y?<n), 
where <fi = CP+1_L A OlT. 
Supposed = -LVy^V.. .Vy?in. Then the model 93Ti = (3i, 2Ji), where £1 is the 
frame in Fig 14.9 (a) with m = max{zi,..., in} -f 32 and 2J(q) = {ar2}, separates 
the formula 6 —> 7 (refuted at am) from GL(iV), which is a contradiction. And 
if 6 = -«(!. V V... V (fin) then the model WI2 = (£2, ^2), where g2 is shown in 
Fig 14.9 (b) with m = max{ii,..., in} -f 33 and 2J(p) = {a'x}, separates -«5 —> /? 
from GL(iV), which is again a contradiction. □ 
Now let us consider extensions of S. 
Theorem 14.30 S has the interpolation property. 
Proof Although the axiom Up —► p of S is not conservative in ExtGL (check 
this!), the proof is similar to that of Theorem 14.5 (i). 
Suppose <p —> 'ip e S. Then by Theorem 5.61, we have 
A (°x - x) - (v> - tf) G GL 
□xeSub (v?—*>,0) 
and so 

468 
INTERPOLATION 
A (Dx -> x) a <p -> ( A (Dx -> x) -> i>) e GL. 
□x^Suby? DxGSub-0 
By Theorem 14.25, this formula has an interpolant a in GL, i.e., 
A (°X X) A ¥> « € GL, A (DX -> x) -> (a -> VO e GL, 
□x^Suby? Dx^Sub^ 
from which tp —> a € S and a —> -0 G S. 
□ 
Theorem 14.31 ExtS contains a continuum of logics with the interpolation 
property. 
Proof Exercise. (Hint: use the formulas a* which were defined in the proof of 
Theorem 14.27). □ 
Theorem 14.32 Suppose L is a modal logic with the interpolation property and 
having only one Post complete extension. Then L is Hallden complete. 
Proof Suppose that formulas (p and if) have no common variables and pW'ip e L. 
Then —> ip € L and so there is a variable free formula x such that -* <P € L 
and x ^ € L. Since L has only one Post complete extension, we must have 
either x £ L or -,X £ T- Therefore, <p € L or ip G L. □ 
As a consequence of Theorems 14.31 and 14.32 we obtain 
Corollary 14.33 There is a continuum of Hallden complete logics in ExtS. In 
particular, S itself is Hallden complete. 
Theorem 14.34 ExtS contains a continuum of logics which are not Hallden 
complete and so a continuum of logics without the interpolation property. 
Proof Exercise. (Hint: use the proof of Theorem 14.29 and Theorem 14.32). 
□ 
14.6 	Exercises and open problems 
Exercise 14.1 Suppose L € ExtK or L € Extint and a(p) is a conservative 
formula in ExtL. Show that for every formula <p(pi,... ,pn) € L -f a, 
a(_L) A a(pi) A ... A a(pn) -> tp € L. 
(Hint: consider a substitutionless derivation of ip in L -f ol containing only the 
variables occurring in ip.) 
Exercise 14.2 Say that a formula a(p) is conservative in NExtL C NExtK if, 
for some n, 
f\ □l(a(-L) A a(p) A aq) —> a(p —► q) G L, □*(a(_L) A a(p)) —> a(Dp) € L. 
i<n i<n 
Prove Theorem 14.5 (ii) for L e NExtK. 

NOTES 
469 
Exercise 14.3 Say that a logic L E NExtS4 has the weak interpolation property 
if every formula a —> /? E L has an interpolant in L whenever each occurrence 
of a variable in it is prefixed by □. Prove that L has the weak interpolation 
property iff pL has the (plain) interpolation property. 
Exercise 14.4 Show that the class of finite algebras for Grz.3 is superamal- 
gamable. 
Exercise 14.5 Give canonical axiomatizations of the logics mentioned in 
Theorems 14.23 and 14.24. 
Exercise 14.6 Say that a logic L has the Lyndon interpolation property if for 
every a —> (3 E L, there exists 7 such that a: —> 7 E L, 7 —> a: E L and 
the variables occurring in 7 positively (negatively) have also positive (negative) 
occurrences in both a and /?. Show that K, K4, T and S4 have the Lyndon 
interpolation property. 
Exercise 14.7 Prove that a pseudo-Boolean algebra is subdirectly irreducible 
iff it is well-connected. 
Problem 14.1 Do the si-logics LC, BD2, BD2 4- (p —> q) V (q —> p) V (p <-► -kf) 
have the Lyndon interpolation property? 
Problem 14.2 Which of the logics in NExtS4 with the Craig interpolation 
property do have the Lyndon interpolation property? 
Problem 14.3 Which logics in Theorems 14-23 and 14-24 (ii) do have the 
interpolation property and the interpolation property for derivability, respectively? 
Problem 14.4 Construct a continuum of Hallden complete extensions of S 
without the interpolation property. 
Problem 14.5 Describe the logics with the interpolation property in the classes 
NExtD, NExtD4, ExtD4, ExtS4. 
14.7 	Notes 
The interpolation theorems for K, K4, T, S4 are due to Gabbay (1972a). Gabbay 
(1971b) gave semantic proofs of the interpolation property of Int and some of its 
extensions. The proofs presented in Section 14.1 are slight modifications of the 
proofs given by Maksimova (1982b) to show that the predicate variants of these 
logics have the (stronger) Lyndon interpolation property; see Exercise 14.6. This 
property was established also for some si-logics. Problem 14.1 lists the si-logics 
for which the situation is still unclear. Maksimova (1982b) gave also examples of 
logics in NExtS4 which have the Craig interpolation property but do not have 
the Lyndon interpolation property. Here is one of them. 
Example 14.35 Let L be the logic of the cluster CI2 with points a and b. By 
Theorem 14.21, it has the Craig interpolation property. Consider the formula 
Op A -»p A □(-ip V q) —> -iq V Dq 

470 
INTERPOLATION 
which is clearly in L. Suppose 7 is a Lyndon interpolant for this formula in 
L. Then 7 contains only one variable q, and it occurs only positively Define a 
valuation in £U so that all variables are true at a and false at b. It is easy to 
check that this valuation refutes one of the formulas 
Op A -ip A □(-'P V q) —> 7, 7 —> -*q V Dq. 
The rest of the material in Section 14.1 was also taken from Maksimova 
(1982b). However, the term “conservative” appeared first in Maksimova (1987). 
The result of Exercise 14.3 was announced in Maksimova (1980) and that of 
Exercise 14.4 was proved by Maksimova (1982b). 
The semantic criteria of the interpolation property of Section 14.2 were taken 
from Maksimova (1977, 1979). Maksimova used those criteria to describe all si- 
logics with the interpolation property and to estimate the number of such logics 
in NExtS4. Theorem 14.16 was proved by Maksimova (1979) only for normal 
extensions of S4; later it was considerably generalized by Czelakowski (1982). 
Theorem 14.20 was proved by Maksimova (1982a). This proof was generalized 
in Maksimova (1989c) to show that no logic in NExtK4 of finite width and 
infinite depth, for instance GL.3, has the interpolation property. 
That variable free formulas can be used to construct modal logics with the 
interpolation property seems to be noticed first by Rautenberg (1983). Maksimova 
(1987) generalized considerably this observation by introducing the conservative 
formulas. She also noticed that the addition of a finite set of conservative 
formulas preserves finite approximability, and that finiteness here is essential. The 
“positive” part of Section 14.5 is due to Smorynski (1978) (Theorem 14.25) and 
to Maksimova (1989a) (Theorem 14.27), and the “negative” one was obtained 
using some observations of Chagrov (1990b). 
To conclude, we note two open directions of studies concerning the 
interpolation property. First, the big (continual) families of logics with this property were 
constructed with the essential help of variable free formulas. In this connection 
it would be of interest to investigate the interpolation property in the classes 
NExtD and NExtD4. Another direction is to describe quasi-normal extensions 
of S4 or D4 with the interpolation property. 
Pitts (1992) used the cut-elimination technique to prove the so called 
uniform Craig interpolation theorem for Int which means that, for every formula 
a(pi,... ,Pk,qu... ,qi) there is a unique (up to the equivalence in Int) 
formula /?(<?i,.. • ,#/) such that a —> /? e Int and if a —> 7(^1,...,^) € Int 
and 7 —> 6(q\,... ,<#,77,... ,rm) € Int, then Int. Using semantical 
methods Shavrukov (1993) proved the uniform Craig interpolation theorem for 
GL. Beklemishev (1989) gave a complete description of provability logics with 
interpolation. 
In Maksimova (1992a, 1992b) the reader can find more results concerning 
interpolation and some other related properties. It is proved in particular that a 
normal modal logic has interpolation iff it has the Beth definability property. 

15 
THE DISJUNCTION PROPERTY AND HALLDEN 
COMPLETENESS 
Recall that a modal logic L has the (modal) disjunction property if, for every 
n > 1 and all formulas p\,..., pn, 
□y?i V ... V D(pn e L implies pi £ L, for some i £ {1,..., n}. 
A si-logic L has the disjunction property if, for all p and 
pV 'ip e L implies p £ L or £ L. (15.1) 
And a (modal or superintuitionistic) logic L is said to be Hallden complete if 
(15.1) holds for all p and *ip containing no common variables. 
15.1 	Semantic equivalents of the disjunction property 
First we prove a semantic criterion of the modal disjunction property for logics 
in NExtK. 
Theorem 15.1 Suppose a logic L £ NExtK is characterized by a class C of 
descriptive rooted frames closed under the formation of rooted generated sub- 
frames. Then L has the disjunction property iff, for every n > 1 and every 
3l> • • • > 3Vi € C with roots x\,..., xn, there is a rooted frame 5 for L with root 
x such that 5i + • • • + 3Vi is (isomorphic to) a generated subframe of # with 
, . . . , Xn j Q . 
Proof (=>) Let = (Wl,Rl,Pl) be a universal frame for L, big enough to 
contain Si + • • • + 3n as its generated subframe. Assuming that is associated 
with a suitable canonical model for L, we show that there is a point t in such 
that = Wl• 
Consider the tableau 
*0 = (Map: 3(r, A) e Wl <p € A}). 
Clearly, it is L-consistent (for otherwise □</?! V ... V Dpn e L for some formulas 
Pi, ...,y?n ^ L, contrary to L having the disjunction property). Let t be a 
maximal L-consistent extension of By the definition of Rl, we then have 
tRLtf, for every tf e Wl- 
(<$=) Suppose otherwise. Then there are formulas pi,... ,ipn gL L such that 
Dpi V ... V Dpn £ L. Take frames 3l,..., ffn € C refuting Pi,.. - ,pn at their 

472 THE DISJUNCTION PROPERTY AND HALLDEN COMPLETENESS 
roots, respectively, and let 5 be a rooted frame for L containing 5i + • • • + 3n 
as a generated subframe and such that its root x sees the roots of Si, • • • , 3n- 
Then all the formulas d^i,..., D(pn are refuted at x and so Dtpi V... V Utpn g L, 
which is a contradiction. □ 
It should be clear that if we need to use only the sufficient condition of 
Theorem 15.1 then the requirement that frames in C are descriptive is redundant. 
Remark Since D<pi V n<p2 V ... V D(pn —> n<pi V U(Uip2 V ... V D(pn) € K4, a 
logic L G NExtK4 has the disjunction property iff, for all <p and Uip\JUij) G L 
implies <p G L or ip G L. So, for such L we may assume that in Theorem 15.1 
n < 2. And clearly a logic L G NExtS4 has the disjunction property iff, for all 
<p and -0, D(p V Dxp e L implies D<p e L or D-0 G L. 
As a direct consequence of the proof above we obtain 
Corollary 15.2 A consistent logic L G NExtK has the disjunction property iff 
the canonical frame = (Wl,Rl) contains a point x such that x]= Wl. 
Corollary 15.3 If a logic L G NExtK has the disjunction property then the rule 
□p/p is admissible in L. 
Theorem 15.1 is a good tool for proving and disproving the disjunction 
property of logics with transparent semantics. 
Example 15.4 (i) Let 3i, • • •, 3n be serial Kripke frames with roots xi,..., xn. 
Then the frame obtained from 5i + • • • + 3n by adding to it a point x seeing all 
xi,..., xn is also serial. Therefore, D has the modal disjunction property. 
(ii) Since no rooted symmetrical frame can contain a proper generated sub- 
frame, no consistent logic in NExtKB has the disjunction property. 
The reader can find more examples in the next section and among the 
exercises in Section 15.5. 
Similarly to Theorem 15.1 and Corollary J5.2 one can prove the following 
semantic equivalents of the disjunction property for si-logics. 
Theorem 15.5 (i) Suppose a si-logic L is characterized by a class C of 
descriptive rooted frames. Then L has the disjunction property iff, for every $2 € C, 
Si 4- $2 is a generated subframe of a rooted frame for L. 
(ii) A si-logic has the disjunction property iff its canonical frame is rooted. 
Example 15.6 The disjoint union of two Medvedev frames ®n and is 
clearly a generated subframe of ®n+m. So Medvedev’s logic ML has the 
disjunction property. 
A more interesting and complex example is provided by 
Theorem 15.7 The Kreisel-Putnam logic KP has the disjunction property. 

SEMANTIC EQUIVALENTS OF THE DISJUNCTION PROPERTY 
473 
Proof We remind the reader that KP is characterized by the class of finite 
rooted frames S = (W, R) satisfying the condition 
Vx, y, z (xRy A xRz A ->yRz A -izRy —► 3u (xRu A uRy A uRz A 
Vv (uRv —> 3w (vRw A (yRw V zRw))))). (15.2) 
If S is such a frame then, as is easy to see, for each non-empty X C W-1, the 
generated subframe of S based on the set W — (W-1 — X)l is rooted; we denote 
its root by r(X). 
Let Si = and #2 = (W2,i?2) be finite rooted frames satisfying 
(15.2). We construct from them a frame S = (W, iJ) by taking 
W = Wi U W2 U U, 
where U = {X1l)X2: Xx C X2 C^1, Xx,X2 ^ and, for every 
x,y eW, 
xRy iff (x, y eWi A xi^y) V (x, y € U A x D y) V 
(x = Xi U X2 € u A y € Wi A r^i^y). 
It follows from the given definition that Si + S2 is a generated subframe of 
Wi U W2 is a cover for S and Wf1 U Wfl is its root. So our theorem will be 
proved if we show that (15.2) holds. 
Suppose x, y, 2 eW satisfy the premise of (15.2). Since (15.2) holds for Sh S2 
and since Si we can assume that x = XiUX2 € U. Let YiUY2 and Zil)Z2 be 
the sets of final points in y| and z\, respectively, with Yi, Zi C Wi, z = 1,2. By the 
definition of R, we have Yi, Z* C Xi. Consider the point u = (Yi U Zi) U (Y2 U Z2). 
Clearly xRu, uJJy and uRz. Suppose now that v € u\. Let w be any final point 
in Then v G {Y\ U Z\) U (Y2 U Z2) and so either yRw or zRw. □ 
To transfer the disjunction property from modal logics to their si-fragments 
and back we prove the following: 
Theorem 15.8 The maps p, r and a preserve the disjunction property. 
Proof That p preserves the disjunction property follows from the obvious fact 
that for every modal companion M of a si-logic L, G L iff T(^V^) G M 
iff T(ip) V T(0) £ M (recall that T((p) and T(0) may be regarded as boxed). 
Suppose now that a si-logic L has the disjunction property and is 
characterized by a class C of rooted descriptive frames. By Theorem 9.68, aL is 
characterized by the class aC. Let Si and S2 be arbitrary frames in C and S a frame 
for L containing Si. + #2 as a generated subframe. Then, by Lemma 9.67, 0‘S 
is a frame for crL in which <tSi + <rS2 is a generated subframe as easily follows 
from the definition of <rS. Hence aL has the disjunction property. 
To prove that the disjunction property is preserved under r, we define an 
operator as follows. Given an intuitionistic frame S = (W,R,P), it returns 
the frame r^S = (wW, uR, uP) in which (ujW,ujR) is the direct product of 

474 THE DISJUNCTION PROPERTY AND HALLDEN COMPLETENESS 
(W, R) and the appoint cluster (a;, a;2) and u)P is the Boolean closure of the set 
{I x X : I C(jj,X € crP} (see Section 8.3). 
If L is characterized by a class C of descriptive rooted frames then, by 
Corollary 9.71, tL is characterized by rwC. Let = (<wWi,u)Ri,u)Pi), for i — 1,2, 
be any frames in rwC and 3 = (W, R, P) a rooted intuitionistic frame 
containing 3i + #2 as a generated subframe. Clearly the underlying Kripke frame of 
Tudi + rj$2 is a generated subframe of the Underlying Kripke frame of tJ3- 
So it remains to show that for i = 1,2, uPi = {X fl uWi : X £ a>P}. But this 
follows from the definition of ljP and the equalities wWi —X — {uW—X^HujWi, 
X n Y = {X* n Y') n uWi which hold for every X, Y C uWi and X', Yf C 
such that X = X' n wWi, Y = Yf n □ 
15.2 	The disjunction property and the canonical formulas 
In this section we use the apparatus of the canonical formulas to prove 
several sufficient and necessary conditions of the disjunction property for logics in 
NExtS4 and Extint. First we obtain a complete description of cofinal subframe 
logics in NExtS4 with the disjunction property. We assume that every logic 
L € CSJ* fl NExtS4 is represented by its independent canonical axiomatization 
L = S4® {<*(&,!.): i€/}. (15.3) 
All frames in this section are assumed to be quasi-orders. 
Say that a finite rooted frame 3 with > 2 points is simple if its root cluster 
and at least one of the final clusters are simple. 
Suppose 3 = (W, R) is a simple frame, ao, ai,..., am, am+i,..., an are all 
its points, with ao being the root, C(ai),. -. , C(am) all the distinct immediate 
cluster-successors of ao and an a final point with simple C(an). For every k = 
1,..., n, we define a formula ipk by taking 
n 
■>Pk = f\ <Pij A /\ <Pi A <p'± -* pk 
aiRa,j,i^0 i= 1 
where ipi were defined in Section 9.4 and = 0(/\^=1 DPi -L)- Now 
we associate with 3 the formula 7(#) = Dpo V if m = 1, and the formula 
7(3) = Ofa V ... V □ V>m if m > 1. 
Lemma 15.9 For every simple frame 3, 7{3) € S4 © a(3, -1). 
Proof By Theorem 11.20, it suffices to show that 0 7(3) implies 0 
a(3r, ±), for any finite frame 0. So suppose 7(3) is refuted in a finite frame 0 
under some valuation. Define a partial map / from 0 onto 3 by taking, for any 
x in 0, 
fa0 if x ^ 7(3) 
f(x) = < ai if x ijji, 1 < i < n 
[ undefined otherwise 
and show that it is a subreduction of 0 to 3> 

THE DISJUNCTION PROPERTY AND THE CANONICAL FORMULAS 475 
Suppose f(x) = di and diRdj. If i Y 0 then in exactly the same way as in 
the proof of Theorem 9*39 we can find y G x\ such that f(y) = aj. And if i = 0, 
j Y 0 then there is k £ {1,..., m} such that akRdj. Since x we have a 
point z € xT such that /(z) = ak and then, as was shown above, there is y £ z] 
with f(y) = aj. It follows in particular that / is a surjection. 
Now let f(x) = a*, f(y) = dj and y G x{. If i = 0 then clearly diRdj. So 
suppose i Y 0. If j Y 0 then in the same way as in the proof of Theorem 9.39 
we show that diRdj. But in fact this is the only possible case. Indeed, if j = 0 
then, for m = 1 we have x f= Dp0 (because x \= ip% and do # dk}), contrary to 
V Op0, and if m > 1 then there is fc G {1,... ,m} such that dk ait but, 
since aoRak, we must have a point z € y | with f(z) = ak, which leads to a 
contradiction between x J= Dpk and z^Pk- 
Thus / is a subreduction of 0 to Sr. However it is not necessarily cofinal. 
50 we extend / by putting f(x) = an, for every x of depth 1 in 0 such that 
f(xl) = {do}. Clearly the improved map is still a subreduction of 0 to #, and 
using the formula (p*± it is easy to show that it is cofinal. 
It follows that 0 Y1 a(Sy -L) and so 7(30 G S4 0 a(3r, -L). □ 
Lemma 15*10 Suppose i G {1,... ,m} and 0 is the subframe of 3r generated by 
di. Then o:(0, J.) £ S4 0 0*. 
Proof Exercise. □ 
We are in a position now to prove a criterion of the disjunction property for 
the cofinal subframe logics in NExtS4. 
Theorem 15.11 A consistent cofinal subframe logic L € NExtS4 has the 
disjunction property iff no frame 'Si in its independent axiomatization (15.3) is 
simple, for i G J. 
Proof (=>) Suppose on the contrary that Si is simple, for some i G /. Since 
the axiomatization (15.3) is independent, every proper generated subframe of Si 
validates L (for otherwise there would be an axiom a(Sj, -L) of L, for j Y h with 
51 being subreducible cofinally to Sj, which is a contradiction). By Lemma 15.9, 
7(3ri) € L and so, by virtue of L having the disjunction property, either po € L 
or 'ijjj £ L. However, both alternatives are impossible: the former means that L 
is inconsistent, while the latter, by Lemma 15.10, implies a(0, _L) £ L where 0 
is the subframe of Si generated by an immediate successor of Si s root. 
(4=) Given two finite rooted frames 0i and 02 for L, we construct the frame S 
as shown in Fig. 15.1. Clearly, 0i + 02 S- So to apply Theorem 15.1, it suffices 
to show that S \= L. Suppose otherwise, i.e., there exists a cofinal subreduction 
/ of S to Si, for some i £ I. Let Xi be the root of Si• Since 0i and 02 are 
not subreducible cofinally to Si and since L is consistent, f~l(xi) = {x}. By 
the cofinality condition, it follows in particular that y £ dom/. But then Si is 
simple, which is a contradiction. □ 
Using the preservation theorem and Theorem 9.44, we immediately obtain 

476 THE DISJUNCTION PROPERTY AND HALLDEN COMPLETENESS 
Fig. 15.1. 
Corollary 15.12 No consistent proper extension of Int with disjunction free 
axioms has the disjunction property. 
It is worth noting that the proof of Theorem 15.11 provides us with a 
somewhat stronger result. In fact the proof of (=>) yields 
Proposition 15.13 If L e NExtS4, $ is a simple frame, a(S, _L) € L and 
a(0, _L) ^ L for any proper 0 C S then L does not have the disjunction property. 
Transferring this observation to the intuitionistic case, we obtain 
Theorem 15.14 If a consistent si-logic L has the disjunction property then the 
disjunction free fragments of L and Int are the same. 
Now we prove two simple sufficient conditions of the disjunction property for 
si-logics whose canonical axioms may contain closed domains. These conditions 
are far from being optimal and can be extended in various directions. First we 
use the simplest possible construction. 
Theorem 15.15 Suppose a si-logic L can be axiomatized by canonical formulas 
or 2)) such that the set X of immediate successors of %’s root 
contains > 3 points and D G S, for every antichain D containing a subset of X 
with > \X\ /2 points. Then L has the disjunction property. 
Proof Let #1 = (Wi, JRi, Pi) and S2 = (W2, P2,P2) be rooted frames for L. 
Construct a frame So = (Wo, Po, Po) by adding to #1 + S2 a root a0 and defining 
Po as the pseudo-Boolean closure of {Y\ U Y2 : Yi € Pi, Y2 £ P2}. By induction 
on the construction of a set Y € Po one can readily show that Y fi Wi G Pi, for 
2 = 1,2, and so #1 + S2 is a generated subframe of So- 
To show that #0 |= suppose otherwise. Then #0 refutes an axiom /?(#, 2), _L) 
(or /?(#, 2))) of L, i.e., there is a cofinal (or plain) subreduction / of #0 to S 
satisfying (CDC) for 2). Let a be the root of S- Since Si f= L, for i = 1,2, 
/-1(«) = {flo}- 
Now take that i for which Wi contains inverse /-images of all points in some 
antichain a C X with |a| > \X\ /2 and let d be the antichain in S such that 
f(Wi) = f)|. By the condition of our theorem, D 6 2) and so, by (CDC), the root 
ai of Si must be in dom/. But then /(a*) = a, which is a contradiction. □ 

MAXIMAL SI-LOGICS WITH THE DISJUNCTION PROPERTY 
477 
Corollary 15.16 Every si-logic axiomatizable by formulas /3tt(J, _L) (or 
formulas $($)) such that the root o/J sees > 3 immediate successors has the 
disjunction property. 
The second sufficient condition uses a more complicated construction. 
Theorem 15.17 Suppose a si-logic L is axiomatized by formulas /?(J, 2), _L) with 
J of depth > 3 and 2) containing an antichain D C J-1 having no focus in J. 
Then L has the disjunction property. 
Proof Let Ji = (Wi,Pi,Pi) and J2 = be rooted finitely 
generated refined frames for L. With each antichain a in (#1 -f J2)-1 such that |a| > 2 
we associate a new point xa\ the set of all such points is denoted by V. Construct 
a frame Jo = (Wo, Po, Po) by taking 
W0 = {a0} U W\ U W2 U V, 
xRoy iff x = ao V 3i e {1,2} (x, y £ W» A xIUy)V 
3xa ev (x = xa A (y = xa v y e xa)) 
and defining Po as the pseudo-Boolean closure of {Y\ U Y2 : Y\ € Pi, I2 £ P2}- 
Ji + J2 is then a generated subframe of Jo- Moreover, since the original frames 
are finitely generated and refined, (Ji -f J2)-1 is a cover for Jo- 
Assume now that Jo refutes an axiom /?(J,2),_L) of L. Let / be a cofinal 
subreduction of Jo to J satisfying (CDC) for 2). Since J is of depth > 3 and 
Ji |= L for i = 1,2, the root ao is in domf. Take an antichain D G S having 
no focus in J and consisting of only points of depth 1. Let a be an antichain in 
Jjp such that /(a) = d. Since xa is a focus for a, we must have, by (CDC), that 
xa € domf. But then f(xa) is a focus for D, which is a contradiction. 
Thus Jo |= L and so L has the disjunction property. □ 
15.3 	Maximal si-logics with the disjunction property 
The disjunction property of a si-logic means that formulas in the logic represent 
only constructive principles of reasoning. Since Cl is not constructive in this 
sense, it is of interest to find maximal (consistent) si-logics with the disjunction 
property. That they exist follows from Zorn’s lemma (see Exercise 15.8). Here is 
a concrete example of such a logic. 
Theorem 15.18 The Medvedev logic ML is a maximal si-logic with the 
disjunction property. 
Proof Suppose on the contrary that there exists a proper consistent extension 
L of ML having the disjunction property. Then we have a formula (p € L- ML. 
We show first that there is an essentially negative substitution instance ip* of p 
such that p* £ ML. 
Since p{pi,... ,pn) ^ ML, there is a Medvedev frame 93m refuting p under 
some valuation 93. With every point x in 93m we associate a new variable qx and 

478 THE DISJUNCTION PROPERTY AND HALLDEN COMPLETENESS 
extend 93 to these variables by taking V3(qx) to be the set of final points in 93m 
that are not accessible from x. By the construction of 93m, we have y |= -■qx iff 
y £ from which 
V -9*) = ®(Pi)- 
x€%}(pi) 
Let ip* = j(Pl) _19i, • • •»Vxe»(P„) “’ft)-It; follows 51O*) = ®(¥>) and 
so ip* £ ML. 
Thus, we may assume that is an essentially negative formula. Recall now 
that KP C ML (see Exercise 5.32) and so ML contains the formulas 
ndk = (-*p -> -*qi V ... V —•^r*) -+ (-*p —> -*gi) V ... V (-*p —> -»£*), 
which, as is easy to see, belong to KP. Let us consider the logic 
ND = Int -f {ndk ‘ fc > 1}. 
It should be clear that ND C KP C ML (in fact both inclusions here are 
proper). Using the fact that the outermost —► in ndk can be replaced with <-► 
and that (->p —► ->q) -i(-»p A q) G Int, one can readily show that every 
essentially negative formula is equivalent in ND to the conjunction of formulas 
of the form -»xi V ... V -»xz* 
So L — ML contains a formula of the form -»xi V ... V —*xz • Since L has 
the disjunction property, -»x< € L for some i. But then, by Glivenko’s theorem, 
—»Xi € ML, which is a contradiction. □ 
It turns out, however, that ML is not the unique maximal logic with the 
disjunction property in Extint. Moreover, the following result holds. 
Theorem 15.19 There is a continuum of maximal si-logics with the disjunction 
property. 
Proof It is sufficient to show that there is a continuum of si-logics such that (i) 
each of them has a consistent extension with the disjunction property and (ii) no 
pair of them has a common consistent extension with the disjunction property. 
For each n > 8, let 
n . 7 
<Pn = V(ft V (ft ft v (q2 -► 93 V (q3 -► ->x")))), V>n = A -+ ^8 > 
i= 1 1 
n 
x?=pi a A -'Pi* V’" = -> A -,x?> 
i=l 
w= A ( A -Xfc - -x? v , 
where 

MAXIMAL SI-LOGICS WITH THE DISJUNCTION PROPERTY 
479 
n 4 
= (A^xs-> V — 
fe=5 fe=l 
4 
(-X? V A -x?) A (-x? V (-X? A -*?)) A 
2=2 
A ( A -*?->-x?v^v-x2), 
l<i<i<fc<4 tg{i,j,fc} 
$? = ( A -’x2-»-x5v-xJv-x?)-» 
fcg{2,4,5} 
(-'Xi V ->*3 ->X2 V ->X4). 
V -x2--x?v^, 
fcg{l,5} 
n—3 
v>6 = A (( A ^x* v “,x?+iv -,x?+2) -*■ 
i=4 fcg{i-l,i+l,*+2} 
-,X"-1 V ->X?+l) A (->Xn -♦ “’Xn-3 V “,Xn-l)> 
n —4 n 
W = (/\-xnk^ V -x2)->-x^2v^, 
fc=l k=n—3 
n 4 
w = (f\-xnk->y-xnk)v-xn5. 
fc=5 fc=l 
Observe that, as follows from the construction of </?n, no consistent si-logic 
containing </?n has the disjunction property. 
For each set N of natural numbers > 8, let 
L(N) = Int + {</>n -* <pn : n E AT} + {</>n : n<£N, n> 8}. 

480 THE DISJUNCTION PROPERTY AND HALLDEN COMPLETENESS 
a\ a 2 as a± a5_3 a5_2 a5-i as 
Fig. 15.3. 
Lemma 15.20 If N\ ^ N2, then L(N\) and L(N2) ftave no common consistent 
extension with the disjunction property. 
Proof Without loss of generality we may assume that there is n G N\ — N2. 
Then 0n —> </?n G L(N\) and ttpn G L(N2). It follows that (pn G L(Ni) -f- L(N2) 
and so no consistent extension of L(Ni) -f- L(N2) has the disjunction property. 
□ 
Lemma 15.21 L(N) has a consistent extension with the disjunction property. 
Proof Let $m he the frame of the form shown in Fig. 15.2 with m > 1 final 
points. For every s G N and every s + 1-tuple (a, ai,..., a8) of points in such 
that ai,..., a8 are distinct and final in a|, we add to $m new points &i,..., bs-\ 
and extend the accessibility relation to them by drawing the arrows shown in 
Fig. 15.3. The resulting frame is denoted by 
Now we put 
L = Log{Sm{N) : m < u). 
Since 3m{N) + $k{N) is clearly a generated subframe of {?m+fc(A0, by 
Theorem 15.5 L has the disjunction property. So it remains to show that L(N) C L, 
i.e., that all axioms of L(N) are valid in all frames of the form 3>n(./V). 
Suppose that 0n is refuted in 3rn(iV) under some valuation. Then there is a 
point x such that x |= 0-1, for i = 1,.. *., 7, and x ty1 V#• We are going to show 
that in this case n G N and so 0n cannot be an axiom of L(N). 
Notice first that x does not belong to #m. For otherwise, since x , 
we would have five distinct final points ai,...,as G xf such that aj |= Xj> 
for j = 1,..., 5. Since x |= each final successor of x validates x? for some 
i G {1,... ,n}. Therefore, there are two adjacent final points c and d in at 
which distinct x? and Xj are true. But then 

MAXIMAL SI-LOGICS WITH THE DISJUNCTION PROPERTY 
481 
X\ #2 x3 x4 x5 
Fig. 15.4. 
where e is the immediate predecessor of c and d in Since e G x| and x [= ^, 
we arrive at a contradiction. 
Now let us take a closer look at the condition x . It means that there 
are points xi,..., x5, y in 3m(N) which together with x form the diagram shown 
in Fig. 15.4. Comparing it with Fig. 15.3 and recalling that x does not belong 
to we conclude that x can be identified only with bi in Fig. 15.3. Using this 
observation we show that n = 5, from which n € N, as required. 
Among • • •, bs-i only &2 and 1 have four successors and can refute the 
first disjunct in . Let us first assume that 
n 4 
ba-l (= f\ ~<Xk> bs-l ^ V "’X*' 
k=5 fc=l 
Then each of the formulas Xi > • • •, X4 1S true at exactly one of a5_3,..., as and 
so 
h-2^ A ( A -» -*? V -X? V -*£)• 
Since &i |= ^3 , we obtain then 
^ A ^*2 -> v 
fe=5 fc=l 
which is impossible, because bs-2 has only three successors. 
Thus we are forced to conclude that 
n 4 
b2 b= A -x2, ^ V -x2- 
fc=5 fc=l 
As before, it follows that exactly one of x?, • • •, X4 1S true at each a*, 1 < i < 4. 
Now consider 63. Since it has only three successors, the condition bi |= V# 
leaves only one possibility: 63 ^ -1X2 v -,X4 and &3 |= -»Xi v _,X3 • But then the 
conclusion of is not true at 63 and so 63 must refute the premise. It follows 
that a5 |= X5 • 
Observe now that either Xi or X3 is true at <13. Since bi |= xfrV; and n > 8, 
we may have only 0,3 (= x?* Then 64 -<X3 V ->X5- By virtue of &i (= V#, we 
also have 64 ^ X6 > which is possible only if a6 \= Xe- Iu the same way, using the 

482 THE DISJUNCTION PROPERTY AND HALLDEN COMPLETENESS 
condition &i (= 0g, we can show that |= for i = 7,..., n - 1. And the last 
conjunct of 0£ ensures that bn_2 sees a final point x at which Xn is true. Since 
no distinct xf and Xj can be simultaneously true at a point, s > n. It follows 
also that b^—2 ^ ^s—l and so x — an. 
Since 6n_i sees both an and an_2, we have bn_i ->Xn-2 v “'Xn- And since 
bx (= 07, we then have also bn_ 1 Vfe=n-3 which means that 6n_i sees at 
least four distinct final points. So bn-1 = &5_i and consequently n = s. 
It remains to show that 3^ (AT) \= 0s —► for every m < u and every 
s € N. Suppose that p>8 is refuted at some x in $m(N) under some valuation. 
This means that s chains of length > 4 start from x and at their final points 
ai,..., a8 the formulas xf, • • •, Xss are true, respectively. It follows also that x is 
a point in $m which sees the configuration shown in Fig. 15.3. It is not hard to 
check now that in such a situation b\ 05, from which x 05. □ 
It follows from Lemmas 15.20 and 15.21 that there is a continuum of logics 
satisfying (i) and (ii) and so a continuum of maximal si-logics with the disjunction 
property. □ 
15.4 	Hallden completeness 
In this section we show various methods for establishing Hallden completeness 
of logics in ExtK and Extint. Let us begin with a lattice-theoretic criterion of 
this property. 
Theorem 15.22 A superintuitionistic or quasi-normal modal logic L is Hallden 
incomplete iff there are logics Li,L2 E ExtL such that L\ % L2, L2 % L\ and 
L = L\ n L2. 
Proof (=>) If L is Hallden incomplete then there are formulas <pi,<P2 & L with 
Var<£i fiVar<^2 = 0 and V<p2 E L. Consider the logics L* = L + y?i, for i = 1,2. 
Clearly, L\ and L2 are incomparable with respect to C and L C Li C\ L2. To 
prove the converse inclusion, take any formula 0 E L\ D L2. Then there are 
substitution instances ip\ and (p2 °f ¥>i and respectively, for i — l,...,m, 
j — 1,..., n, such that 
A ¥>1 € L, A vi -* V’ G L. 
i<m -j<n 
It follows that 
(A pi)v (A ^2) -1, ^G L 
i<m j<n 
and so 
A (*4 v ^2) -♦ e l. 
i<m,j<n 
Since p>\ and p2 have no common variables, ip\ V p2 e L. Hence 0 E L. 

HALLDEN COMPLETENESS 
483 
(<*=) If L\ % L2, L2 ^ Li and L = L\C\L2 then there are formulas tpi £ L1-L2 
and (p2 € L2 — L\ without common variables. Then we clearly have (pi,(fi2 & L 
and ifi V ip2 £ L. □ 
Example 15.23 Since the lattices ExtS5, ExtLC, ExtBD2 are linearly ordered 
by inclusion, all logics in them are Hallden complete. 
It is to be noted, however, that Theorem 15.22 does not hold if we consider 
only normal modal logics and take NExtL instead of ExtL (see Exercise 15.16). 
Now we obtain a semantic criterion. 
Theorem 15.24 Suppose a logic L £ ExtK is characterized by a class C of 
descriptive rooted frames with distinguished roots. Then L is Hallden complete 
iff> for every frames (3i,di) and ($2^2) in C, there is a frame (#, d) for L 
reducible to both (3i,di) and ($2^2)- 
Proof (=>) Suppose the frames #1 and #2 are x'- and ^''-generated, 
respectively. Then they are (isomorphic to) generated subframes of the universal x'- 
and x"-generated frames 0i and 02 for kerL. Without loss of generality we 
may assume that 0i and 62 are associated with the canonical models for kerL 
in disjoint languages MC\ and MC2, respectively. The frames 0i and 62 are 
reducts of the universal (x' 4- x")-generated frame 0 for kerL, associated with 
the canonical model for kerL in the language MC = MC\ U MC2. Let <7*, for 
i = 1,2, be the natural reduction of 0 to 0*, i.e., for every t = (I\A) in 0, 
gi(t) = (T D ForMCi, A 0 ForMCf). 
Consider the points d\ = (Ti, Ai) and c?2 = (1^, A2) in 01 and 02, 
respectively. Put 6! = (T1 ur2,Ai U A2) and show that this tableau is L-consistent. 
Suppose otherwise. Then there are formulas </?i £ Ti, g>2 £ 1^, V>i € Ai, 
i/>2 € A2 such that (pi A ip2 —■► V>i V V>2 € L. But this is (classically) 
equivalent to (</?i —> Vh) V (<p2 —■► ^2) € L. Since (pi —> Vh and <£2 V>2 have no 
variables in common, we must then have <pi —> € L or <£2 —* ^2 € L, contrary 
to (ffijdi) and ($2^2) validating L. 
Let d be a maximal L-consistent extension of d' in the language AAC. Then 
clearly gi(d) = di for i = 1,2. So the restriction fa of gi to the subframe 5 of 0 
generated by d is a reduction of 5 to with /^(d) = di. It remains to observe 
that (#, d) validates L. 
(<=) Suppose that <p\ # L and </?2 L, for some formulas ipi and </?2 with 
no variables in common. Let for i = 1,2, be a frame in C refuting <pi 
under a valuation 2J* of <pi s variables. Take a frame (#, d) for L reducible to 
both (3i,di) and ($2^2) by reductions fa and /2- Define a valuation 2J in # by 
taking, for p £ Var$J(p) = /^(^(p))- Then fa is a reduction of the model 
(S', 93”) (restricted to </Vs variables) to and so, by the reduction theorem, 
we have d V </?2- Therefore, </?i V </?2 ^ L. □ 
Notice that the proof of (4=) does not use the fact that #1 and $2 are 
descriptive and rooted. So if we need only the sufficient condition of Theorem 15.24, 
the requirement that frames in C are descriptive and rooted is redundant. 

484 THE DISJUNCTION PROPERTY AND HALLDEN COMPLETENESS 
Theorem 15.25 A consistent logic L € ExtK is Hallden complete iff it is 
characterized by a frame with a single distinguished point 
Proof (=>) Consider the tableau t' = (0, A) where A is a set of formulas 
such that (a) L Pi A = 0, (b) every formula that is not in L can be obtained 
from a formula in A by renaming its variables and (c) distinct formulas in A 
have distinct variables. Since L is Hallden complete, t' is L-consistent and has a 
maximal L-consistent extension t. Then the frame (SkerL,(v),t) characterizes L. 
(<=) follows from Theorem 15.24 □ 
For normal modal logics the proof of Theorem 15.24 yields the following: 
Theorem 15.26 Suppose a logic L € NExtK is characterized by a class C of 
descriptive rooted frames closed under the formation of rooted generated subframes. 
Then L is Hallden complete iff\ for all frames S11S2 € C and with roots x\, X2, 
respectively, there is a frame S for L reducible to Si and S2 by reductions f\ and 
f2, respectively, such that fi(x) = x\ and f2{x) = X2 for some x in S- 
Example 15.27 S4.3 is characterized by the frame (Q, <), Q the set of 
rational. Since for every x, y £ Q, there is an isomorphism / of (Q, <) onto itself 
with f(x) = y, S4.3 is Hallden complete. 
For si-logics Theorems 15.26 and 15.25 transform into 
Theorem 15.28 (i) Suppose a si-logic L is characterized by a class C of rooted 
descriptive frames. Then L is Hallden complete iff, for every frames Si >#2 € C, 
there is a rooted frame S for L containing generated subframes reducible to Si 
and #2- 
(ii) A si-logic L is Hallden complete iff it is characterized by a rooted frame. 
Proof Exercise. □ 
Hallden completeness is obviously preserved while passing from a modal logic 
in NExtS4 to its si-fragment. However, this is not so in the case of the converse 
transition even for the maps r and a. 
Theorem 15.29 There is a Hallden complete si-logic having no Hallden 
complete modal companions. 
Proof Consider the si-logic of the frame S shown in Fig. 15.5. By 
Theorem 15.28, it is Hallden complete (but, as any other tabular logic, does not 
have the disjunction property). Let M € p~lL. Construct the formulas a(3i, -L) 
and afl(S2, -L), for Si and #2 depicted in Fig. 15.5 so that they would not have 
common variables. Since S \= crL D M, S ^ ot(Su -L) and S <^(#2, -L), neither 
of those formulas is in M. 
On the other hand, by Corollary 9.71, the smallest modal companion tL C 
M of L is characterized by the frame (lj,lj2) x S• Since it clearly validates 
at(Si, -L) V afl(S2, -L), this disjunction is in M and so M is not Hallden complete. 
□ 

EXERCISES AND OPEN PROBLEMS 
485 
t?l ° 
o 
o 
Fig. 15.5. 
We conclude this section with two sufficient conditions of Hallden 
completeness for logics in NExtGrz formulated in terms of the canonical 
formulas. Recall that every logic L £ NExtGrz can be represented in the form 
L = Grz 0 {o(Si,®i, -!) : i € 1} with partially ordered Si- 
Theorem 15.30 If a Kripke complete logic L £ NExtGrz can be axiomatized 
by canonical formulas a(S,®,-L) such that the root o/S has only one immediate 
successor then L is Hallden complete. 
Proof Suppose Si = (Wi,i2i) and S2 = (^2, #2) are partially ordered Kripke 
frames for L with roots a\ and a2, respectively. Construct a frame So = (Wo? Ro) 
by gluing a\ and a2 into a single point a, i.e., by taking 
It should be clear that So is reducible to both Si and S2 (here essential is that 
these frames are Noetherian partial orders). So to apply Theorem 15.26 we must 
show that So validates L. 
Assume that So refutes an axiom a(S,2),-L) of L. Then there is a cofinal 
subreduction of So to S satisfying (CDC) for 2). Since Si and S2 are frames for 
L, /(a) is the root of S- Suppose Si contains an inverse /-image of the immediate 
successor of /(a). Then the restriction of / to Si is clearly a cofinal subreduction 
of Si to S satisfying (CDC) for 2), whence we have Si a(S,®, -L), which is a 
contradiction. □ 
Theorem 15.31 Suppose a normal extension L of Grz can be axiomatized by 
canonical formulas a(S, 2), _L) ora(S,3D) such that the set X of immediate 
successors o/S^s root contains > 3 points andD £ 2) for every antichainQ containing 
a subset of X with > \X\ /2 points. Then L is Hallden complete. 
Proof Similar to the proof of Theorem 15.15. □ 
15.5 	Exercises and open problems 
Exercise 15.1 Reformulate Theorem 15.1 for quasi-normal modal logics and 
use it to show that S and S4.1' have the disjunction property. 
Exercise 15.2 Find a formula violating the disjunction property in all 
consistent logics in NExtKB. 
Wo = {a} U (Wx - {ax}) U (W2 - {a2}) 
xRoy iff x = a V 3i € {1,2} (x, y £ Wi A xRty). 

486 THE DISJUNCTION PROPERTY AND HALLDEN COMPLETENESS 
Exercise 15.3 Which of the standard modal and si-logics have the disjunction 
property? Which of them are Hallden complete? 
Exercise 15.4 Show that the logics of finite depth or of finite width do not 
have the disjunction property and that there is a continuum of such logics. 
Exercise 15.5 Prove that the logics NDfc and ND have the disjunction 
property. 
Exercise 15.6 Show that the class of si-logics with the disjunction property is 
not closed under intersections and sums. Show that the class of Hallden complete 
si-logics is not closed under intersections and sums. 
Exercise 15.7 Prove that the interval [Int, L] contains a continuum of logics 
with the disjunction property and as many without it, for every L D Int. 
Exercise 15.8 Prove that every consistent logic with the disjunction property 
is contained in a maximal consistent logic with the disjunction property. 
Exercise 15.9 Prove that every logic with the disjunction property is the 
intersection of an infinite descending chain of logics and has no immediate successors. 
Exercise 15.10 Show that the implication free fragment of every si-logic with 
the disjunction property coincides with that of Int. 
Exercise 15.11 Construct a Kripke incomplete and an undecidable si-calculi 
with the disjunction property. (Hint: use the following observations. Suppose 
that 
L = Int + {/?(&, ©i) : i = 1,..., n) 
is a Kripke incomplete or undecidable si-logic. Then the logic 
L = Int + {/3(&,$>i,±) :i = l,...,n}, 
where Wi = W{ U {0,1,2,3}, Ri is the reflexive and transitive closure of the 
relation 
Ri U {(x,0) :xeWi} U {(0, j) : 1 < j < 3} 
and U {{1,2}}, has the disjunction property and retains the “negative” 
property of L.) 
Exercise 15.12 Show that Int is the only consistent si-logic having the 
following generalized disjunction property: for any n > 2 and any formulas pi, tyu 
1 > i > n, if AILiC^i -»'Pi) -► V"=i Vi then A"=i(Vi 'Pi) Vi for some i. 
Exercise 15.13 Show that each consistent si-logic with the disjunction property 
has infinitely many modal companions without the disjunction property. 
Exercise 15.14 Show that a normal modal logic L is Hallden complete iff, for 
all modal algebras Ql and 03 for L, there are an algebra <£ for L and embeddings / 
and g of 21 and 03 in (£, respectively, such that f(a) < g{b) for no a in 01 different 
from _L and 6 in 03 different from T. 

EXERCISES AND OPEN PROBLEMS 
487 
Exercise 15.15 Show that every Post complete logic in Extint and (N)ExtK 
is Hallden complete. 
Exercise 15.16 Show that the modal logic of the frame $ in Fig. 15.5 is not 
represented as an intersection of two incomparable normal logics. 
Exercise 15.17 Let DP and HC denote the classes of logics that have the 
disjunction property and are Hallden complete, respectively. Show that there is a 
continuum of logics in each of the following classes: Extint fl DP, Extint flHC fl 
-DP, Extint - HC, NExtGrz fl HC fl DP, NExtGrz fl -HC fl DP, NExtGrz fl 
HC n -DP, NExtGrz 0 -HC n -DP. 
Exercise 15.18 Show that all normal consistent extensions of GL except Log* 
are Hallden incomplete. 
Exercise 15.19 Show that S is Hallden complete. 
Exercise 15.20 Say that a si-logic L has the property DP* if, for all formulas 
<p and V V £ L implies -\-\<p £ L or £ L. Show that L has DP* iff 
p V -i->p ^ L. 
Exercise 15.21 Say that a logic L is Maksimova complete if, for every formulas 
ipi —* V>i and </?2 —* V>2 with no variables in common, <pi A (f2 —* 'ipi V fa £ L 
implies <pi —* fa € L or </?2 —* fa € L. (It should be clear that a modal 
logic is Hallden complete iff it is Maksimova complete.) Show that a si-logic is 
Maksimova complete iff for any two rooted descriptive frames for L there exists 
a rooted frame for L reducible to both of them. 
Exercise 15.22 Show that if formulas <p and have no variables in common 
then, for every si-logic L, <p —* ^ £ L implies -*<p £ L or i/j £ L. 
Problem 15.1 Does there exist a decidable maximal si-logic with the disjunction 
property? 
Problem 15.2 Does there exist a finitely axiomatizable maximal si-logic with 
the disjunction property? 
Problem 15.3 Is it true that a si-logic has an extension with the disjunction 
property iff its disjunction free fragment coincides with that of Int ? 
Problem 15.4 Is it true that tL is Hallden complete iff crL is Hallden 
complete? 
Problem 15.5 Suppose L is Kripke complete and C the class of rooted frames 
for L. Is it true that in Theorems 15.1 and 15.5 we can always take $ to be a 
Kripke frame ? 
Problem 15.6 Are si-logics with extra axioms in one variable Hallden 
complete? 

488 THE DISJUNCTION PROPERTY AND HALLDEN COMPLETENESS 
15.6 	Notes 
The study of the disjunction property of si-logics was started by Lukasiewicz 
(1952) who conjectured that this property is a characteristic one for Int in the 
sense that no proper consistent extension of Int is constructive. The conjecture 
was refuted by Kreisel and Putnam (1957) who proved that both KP and SL 
have the disjunction property (the proof of Theorem 15.7 is due to Gabbay 
(1970a)). Medvedev (1963) and Varpakhovskij (1965) showed that ML and the 
realizability logic are constructive too. Gabbay and de Jongh (1974) constructed 
an infinite family of si-logics with the disjunction property, namely the logics 
Tn of finite n-ary trees. Ono (1972) showed that all Bn posses this property as 
well. Anderson (1972) described the constructive si-logics with extra axioms in 
one variable: he proved that among the consistent logics of that sort only those 
of the form Int + ro/2n+2> for n > 5, n ^ 6, and possibly Int 4- n/14, have 
the disjunction property. Wronski (1974) completed the picture by showing that 
Int + n/14 is constructive. (Another proof of this result was found by Sasaki 
(1992).) Finally, Wronski (1973) showed that there is a continuum si-logics with 
the disjunction property. 
Theorem 15.1 was in essence proved in Hughes and Cresswell (1984); an 
algebraic variant of Theorem 15.5 is due to Maksimova (1986). That p and 
r preserve the disjunction property was noted by Gudovschikiv and Rybakov 
(1982) and Zakharyaschev (1991). The material of Section 15.2 was taken from 
Zakharyaschev (1987) and Chagrov and Zakharyaschev (1993). Theorem 15.14 
was independently proved by Minari (1986); a purely semantic proof can be 
found in Zakharyaschev (1994). Problem 15.3 was formulated by Minari (1986). 
That ML is a maximal si-logic with the disjunction property was proved 
by Levin (1969); the proof of Theorem 15.18 is due to Maksimova (1986). Kirk 
(1982) noted that there is no greatest consistent si-logic with the disjunction 
property. Maksimova (1984) showed that there are infinitely many maximal 
constructive si-logics, and Chagrov (1992a) proved that in fact there is a continuum 
of them; see also Ferrari and Miglioli (1993, 1995a, 1995b). Galanter (1990) 
claims that each si-logic characterized by the class of frames of the form 
({W:W C{l,...,n}, \W\tN},D), 
where n = 1,2,... and N is some fixed infinite set of natural numbers, is maximal 
in the class of consistent si-logics with the disjunction property. 
Theorem 15.22 was proved by Lemmon (1966c), Theorems 15.25 and 15.28 
(ii) by Wronski (1976). The sufficient condition of Theorem 15.26 (formulated 
in terms of Kripke frames) was used by van Benthem and Humberstone (1983). 
Theorems 15.29-15.31 are taken from Chagrov and Zakharyaschev (1993). 
Exercise 15.14 is due to Maksimova (1995) who proved also algebraic characterizations 
for some other properties closely related to Hallden completeness. More results 
and references can be found in Chagrov and Zakharyaschev (1991). 

Part V 
