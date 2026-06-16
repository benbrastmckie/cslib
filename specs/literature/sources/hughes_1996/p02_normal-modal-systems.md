<!-- Source: Hughes & Cresswell (1996). A New Introduction to Modal Logic. Routledge. Part II: Normal Modal Systems (Chapters 7-12, pages 133-230). -->

Part II 
NORMAL MODAL 
SYSTEMS 


7 
CANONICAL MODELS 
In the last chapter we introduced canonical models for normal modal 
systems and used them to prove the completeness of the systems we had 
been studying in Part I. As we remarked there there are many more 
normal modal systems, and in this part of the book we shall have a look 
at some of them with a view to illustrating some general techniques and 
properties of them. This chapter will be concerned to look at some 
features of canonical models. We first introduce three other systems: 
S4.3, S4M and S4.2, and include completeness proofs for them using 
canonical models. We shall then look at the structure of the frames of 
canonical models for a selection of systems, and finally we will discuss 
some limitations of the canonical model technique for proving 
completeness by looking at a system where the frame of its canonical 
model does not validate all its theorems. 
Temporal interpretations of modal logic 
In order to motivate the next two systems we shall look at what can be 
called temporal interpretations of modal logic. These systems have a 
special interest in connection with an issue raised by A. N. Prior in Time 
and Modality.1 Prior was thinking of propositions as things which could 
change their truth-values (could become true or become false) with the 
passage of time, and he wanted to be able to interpret Lp to mean 'It is 
and always will be the case that p'. He therefore suggested that we think 
of time as a series of moments, at each of which a given proposition 
could have the value 1 (true) or the value 0 (false), without prejudice to 
127 


A NEW INTRODUCTION TO MODAL LOGIC 
its value at any other moment; and he defined the value of Lp at any 
given moment as 1 if p has the value 1 at that moment and at every 
subsequent moment, and otherwise as 0. A formula can then be said to 
be valid iff it has the value 1 at every moment, irrespective of the values 
assigned to its variables at any moment. 
The problem is to find an axiomatic system whose theorems shall 
coincide with the formulae which are valid by this criterion. In Time and 
Modality Prior made the conjecture that S4 was the required system,2 but 
this was discovered to be incorrect and he abandoned it shortly 
afterwards.3 One reason why S4 is too weak is because Prior's 
interpretation requires that the moments are all connected in the following 
sense. Suppose we have a point (world) w. A relation R is connected iff 
it holds, in one direction or the other, between every pair of worlds that 
w can see. Using the language of the lower predicate calculus (see Part 
III) we can say that a frame (W,R) is connected iff 
Conn 
VwVw'Vw"((wRw' A wRw") D (w'Rw" V w"Rw')) 
Conn means that if w can see both w' and w" then either w' can see w" 
or w" can see w'; in other words no world can see two incomparable 
worlds. One kind of frame in which it would be natural to think of R as 
connected over W would be one in which the members of W are moments 
of time and R is the relation 'either contemporaneous with or earlier 
than'; for we normally think of the moments of time as all lying, so to 
speak, on a single straight line. And in fact if we require that R be 
reflexive, transitive and connected over W we obtain an account of 
validity for the 'temporal' system S4.3.4 S4.3 is S4 with the addition of 
the axiom 
Dl 
L(Lp D q) V L(Lq D p) 
The method of semantic diagrams can easily be adapted to the system 
S4.3. As an illustration, we show how to prove the validity of L(Lp D q) 
V L(Lq D p) when R is connected (as well as reflexive and transitive). 
The T-diagram for this formula (which shows it to be invalid in T) is: 
128 


CANONICAL MODELS 
L(Lp D q) V L{Lq :>/») 
0 
0 0 
* 
* 
/ 
\ 
* 
Lq D p 
11 0 0 
* 
I p D 4 
11 0 0 
Clearly this is the only kind of T-diagram which could falsify the 
formula. If, however, we require that R be connected, then one thing that 
will follow is that we must have either w2Rw3, or w3Rw2. If we have the 
former then p must be assigned 1 in w3, thus making it inconsistent. If we 
have the latter, then for a similar reason q must be assigned 1 in w2, 
making it inconsistent. 
This establishes the soundness of S4.3 with respect to (reflexive and 
transitive) connected frames. We now proceed to establish completeness. 
Since S4.3 contains S4, we know from the proof of theorem 6.9 on p. 
120 that R is reflexive and transitive in its canonical model. So all that 
remains to prove completeness is to prove that R is also connected. In 
other words we have to show that it is impossible to have the following 
situation for any w1, w2, w3 in the canonical model for S4.3: 
/ 
\ 
w2 
/ "^ 
w3 
(where w -* w' means that wRw', and w -£ means that not wRw'). 
The proof is this. Suppose that such a situation were to obtain 
somewhere in the canonical model of S4.3. Then, since w2 cannot see w3, 
there must be some wff α such that 
(1) Lα G w2 but α £ w3. 
129 
wx 
^h-


A NEW INTRODUCTION TO MODAL LOGIC 
Similarly, since w3 cannot see w2 there must be some wff β such that 
(2) Lβ € w3 but β & w2. 
Putting (1) and (2) together we have 
(3) Lα D β £ w2 and 
(4) Lβ D α £ w3. 
But since w1Rw2 and w1Rw3, (3) and (4) give us 
(5) L(Lα D β) £ w1 and 
(6) L(Lβ D α) g w1. 
So 
(7) L(La D β) V L(Lβ D α) £ w1. 
This however is impossible since this wff is a substitution instance of Dl 
and therefore must be in every world in the canonical model of S4.3. So 
the situation envisaged cannot arise. This establishes the completeness of 
S4.3. 
Although this proof does yield completeness with respect to the class 
of connected frames as defined above it does not on its own give 
completeness for frames which reflect linear time. This is because 
connected models allow what Krister Segerberg calls clusters.5 In a 
cluster every world can see every other world in the same cluster, and in 
the case of time this would mean that you could have a cluster of distinct 
but contemporaneous moments; and this would contradict the fact that 
time is usually imagined to be antisymmetrical, in that if wRw' and w'Rw 
then w = w'. To obtain a linear frame from a connected frame Segerberg 
uses an operation he calls bulldozing.6 This consists of ordering each 
cluster in some arbitrary way and replacing the cluster by an infinite chain 
of copies of that cluster. Where a world used to see another world which 
is now above it in the same cluster it no longer does so, but instead sees 
a copy of that other world in a copy of the cluster lower (i.e. further on) 
in the chain that replaces the cluster. 
130 


CANONICAL MODELS 
Ending time 
In a temporal interpretation, whether or not we conceive of time as linear, 
another question which might be raised is whether time has an end. With 
L meaning 'It is and always will be that', then a final point will be one 
in which, because there is no future, everything that is the case both is 
and always will be. In terms of frames a final point will be one which can 
only see itself, and the claim that time has an end will be the claim that 
every point can see a final point. Without linearity there need be no 
unique final point, but the claim that time ends could still perhaps be that 
every world (i.e. every moment of time) can see a final world. The 
appropriate system for this is S4 + F, where F is the wff 
F (LMp Λ LMq) D M(p Λ q) 
Although F on its own captures the idea that time has an end, in the 
presence of S4 we can in fact use a weaker axiom. S4M is S4 with the 
addition of the wff 
M 
LMp D MLp7 
It is interesting to note that if M were added to S5 rather than merely to 
S4 then the resulting system would collapse into PC; i.e. it would be 
Triv, since in S5 LMp is equivalent to Mp and MLp is equivalent to Lp. 
However, when added to S4 we obtain a system which is characterized 
by the condition on frames that in addition to reflexiveness and transitivity 
every world can see at least one world that can see only itself. This 
condition was called (moo) by EJ.Lemmon.8 As far as we can tell it has 
no recognized name so we shall call it finality. (In modal systems with a 
temporal interpretation it can express the idea that time has an end — a 
final point.) The condition can be expressed formally as 
Fin Vw3w'(wRw' Λ Vw"(w'Rw" D w' = w")) 
It is not hard to check that M is valid on all final frames and we now use 
the canonical model method to prove its completeness. In fact the 
completeness proof goes more straightforwardly in S4 + F, since F 
corresponds exactly to Fin. But in the presence of S4, F can be derived 
from M. We first prove a theorem of K: 
K14 
(Lp Λ Mq) D M(q Λ p) 
131 


A NEW INTRODUCTION TO MODAL LOGIC 
PROOF 
K[~q/q] 
(1) L(p D ~q) D (Lp D L~q) 
(1) × PC X Eq 
(2) 
L~(q Λ p) D (Lp D L~q) 
(2) × LMI 
(3) 
~M(q Λ p) D (Lp D ~Mq) 
(3) × PC 
(4) 
(Lp Λ Mq) D M(q Λ p) 
Q.E.D. 
The PC-principle used in getting from (3) to (4) is (~p D (q D ~r)) D 
((q Λ r) D p) with M(q Λ p)/p, Lp/q and Mq/r. 
Proof of F in S4M: 
M X PC 
(1) 
(LMp Λ LMq) D (LMp Λ MLq) 
Kl4[Mp/p,Lq/q] 
(2) 
(LMp Λ ML^r) D M(Lq Λ M/>) 
Kl4[q/p,p/q] 
(3) 
(L? Λ M/?) D M(p Λ q) 
(3) X DR3 
(4) 
M(Ltf Λ Mp) D MM(p Λ ^) 
R3a[p Λ ^/p] 
(5) 
MMO? Λ q) D M(p Λ tf) 
(1)(2)(4)(5) X PC 
(6) 
(ZJlfp Λ LAf^f) D M(p Λ q) 
Q.E.D. 
The following rule is an immediate consequence of F: 
DR5 
[-Ma, \-M0 -* hM(« A 0) 
DR5 obviously generalizes to more than two wff, so that we have 
DR5' 
hAfa„ ... , h ^ « k "* h ^ ( « i 
A ••• A «k) 
From T2 (p. 42), since S4M contains T, we have, for 1 ≤ i ≤ k, 
\- Mfa D Lad 
and so, by DR5', 
S4M(1) 
M((ax D La{) A ... A (ak D Lak)) 
To prove the completeness of S4M with respect to final transitive and 
reflexive frames it is sufficient to show that its canonical model satisfies 
Fin. We first prove a lemma. Say that w is SL final world in a frame iff 
Vw'(wRw' D w = w'). Then the following holds for every world w in 
the canonical model of any normal modal system: 
132 


CANONICAL MODELS 
LEMMA 7.1 
w is final iff a D La E w for every wff a. 
Proof: First suppose that a D La is in w for every wff a, and suppose 
that wRw' but w ≠ w'. If w ≠ w' then there is a wff β with β E w but 
0 £ w'. But since β D Lβ £ w then Lβ E w and so β E w'. which 
would make w' inconsistent. And if there is some α D Lα not in w, then 
α E w but Lα £ w. So there is some w' such that wRw' and — a E w'. 
So there is some w' such that wRw' and w ≠ >w'. This proves lemma 7.1. 
We now show that the canonical model of S4M satisfies Fin. It will be 
sufficient to prove the following: 
THEOREM 7.2 
If w is any world in the canonical model of S4M, then 
L-(w) U {α D Lα: α any wff} is consistent in S4M. 
We shall first explain why theorem 7.2 gives us the result we want. If 
L-(w) U {α D Lα:α any wff} is consistent then it will have an extension 
w' in the canonical model of S4M. Since L~(w) Q w' we have wRw', 
and since a D Lα E w' for every wff a, w' is final. So, as a result of 
the theorem, every world in the canonical model of S4M can see a final 
world. 
Proof of theorem 7.2: 
Suppose L-(w) U {α D Lα: α any wff} were not 
consistent. Then there would be α,, ... ,αn, β1, ... ,βk such that Lα 1, ... , 
Lαn E w and 
hs4M -(α1 Λ ... Λ αn Λ (0, D Lβ1) Λ ... Λ (βk D Lβk)) 
so 
hs4M (α1 Λ ... Λαn)D ~((β1 D Lβ1) Λ ... Λ (βk D Lβk)) 
so, by principles of K, 
h4M 
(Lα, Λ ... Λ Lαn) D ~M((β1 D Lβ1) Λ ... Λ (βk D Lβk)) 
But (Lα, Λ ... Λ Lαn) E w, and so ~M((β1 D Lβ1) ΛΛ ... Λ (βk D 
Lβk)) G w. But by S4M(1) 
\-M((px DLft) A ... A (fik 
DL0J) 
133 


A NEW INTRODUCTION TO MODAL LOGIC 
which would make w inconsistent. 
Convergence 
Our third example is the system S4.2 which is S4 with the additional 
axiom 
Gl MLp D LMp9 
Gl is in fact the converse of M and the relevant class of frames is the 
class of frames which are reflexive transitive and convergent where a 
frame (W,R) is convergent iff R satisfies the condition that for any wlt w2 
and w3 in W, if w1Rw2 and w1Rw3, there is some w4 such that w2Rw4 and 
w3Rw4. (Connected reflexive frames are convergent frames in which w4 
is either w2 or w3.) Soundness is straightforward. To prove completeness 
we show that the canonical model of S4.2 is convergent. This means that 
we have to show that wherever the following pattern occurs in the 
canonical model for S4.2 
w1 
/ 
\ 
W-y 
Wo 
there is always a world w4 in the model which continues the pattern in 
this way: 
/ 
\ 
H>2 
H>3 
\ 
/ 
W4 
To prove this it is sufficient to show that the set of wff 
(A) L-(w2) U L-(w3) 
is S4.2-consistent. For then theorem 6.3 guarantees the existence of a 
world w in the canonical model such that Λ Q w. It might be worth 
134 


CANONICAL MODELS 
remarking on this way of using the canonical model. For it may easily 
happen, as here, that we need to show that there is in the canonical model 
a world w which has a certain property, and we may be able to express 
that property by saying that w has to contain a certain set of wff, say the 
set A. It is here that theorem 6.3 comes to our aid, for it says that 
provided A is consistent then it is included in a set which is maximal 
consistent, with respect to the system in question, and therefore included 
in a world in the canonical model of that system. 
Suppose then that A is not S4.2-consistent. Then there are wff Lα1 
... , Lαn in w2 and wff Lβl, ... , Lβm in w3 such that 
h ~(a, A ... A aB A ft A... A (3J 
If we let α denote αl Λ ... Λ αn and β denote βl Λ ... Λ βm, then 
lemma 6.1c (on p. 114) and L-distribution (p. 28) tell us that Lα G w2, 
and Lβ G w3, and 
h ~(<* A 0) 
By PC this gives us 
h a D ~0 
And hence by DR3 (p. 35) and LMI (p. 33) 
(1) Ma D ~L(3 
We now note that since wlRw2 and La G w2, MLΑ G W,. (It is not hard 
to see quite generally that if wRw' and y G w' then My G w. For if not, 
by lemma 6.1a and LMI, L~y 
G w and then ~y G w' making w' 
inconsistent.) So by Gl and lemma 6.2b, LMa G w,, and since w1Rw3, 
Ma G w3. So by (1) ~Lβ G w3, making w3 inconsistent. 
This means that A is S4.2-consistent and so is contained in some w in 
its canonical model. Clearly this w will serve as the required w4. This 
establishes the completeness of S4.2.10 
It should be noted that in our proof that R is convergent in the 
canonical model of S4.2 (as also in our proof that it is connected in the 
canonical model of S4.3) we appealed only to Gl (Dl) in addition to 
principles common to all normal systems, and made no use of any 
theorems that depend on T or 4. This shows that K + Gl is complete for 
135 


A NEW INTRODUCTION TO MODAL LOGIC 
frames in which R is convergent, and K + Dl is complete for frames in 
which R is connected, irrespective of whether it is also reflexive or 
transitive. 
The frames of canonical models 
The canonical model for a given modal system, like any other model, is 
based on a certain frame. So far we have said a good deal about canonical 
models, but very little about the frames on which they are based, except 
to note that, although every normal system is characterized by its 
canonical model, it does not follow that every such system is 
characterized by the frame of its canonical model, because that frame may 
not be a frame for the system at all. (Obviously, if the frame of the 
canonical model for S is a frame for S, then that frame characterizes S.) 
We shall now say something more about the frames of canonical models. 
Although it is obvious that the frame of the canonical model is a frame 
it can be easy to forget just what that implies. In the canonical model the 
worlds are sets of wff and a wff α is true in a world w iff α G w. Now 
where a world is a set of wff it is so natural to think that a wff is true in 
a set of wff, just in case it is a member of that set, that we might forget 
that you could, for instance, elect to set a variable p as true in a world iff 
p was not a member of that world. Or even, if the variables were 
arranged in a determinate order you could put V(pi,w) = 1 if i is odd and 
pi G w, or if i is even and p1 £ w, and there is no limit to the 
assignments that could be made. An examination of the members of a 
world would of course not then give you any clue about whether a wff is 
true or not at that world. 
In order to look more closely at frames it will be useful to introduce 
the ideas of an R-step in an R-chain. We say that every world w is 0 R-
steps from itself, i.e. wR°w' iff w = w'. We then say that there is an 
n+l-step R-chain from w to w' (written wRn+1w') iff there is some w" 
such that wRnw and w"Rw'. The idea is simple. If w1Rw2 then w2 is one 
R-step from w,, and if w2Rw3 then w3 is two R-steps from w1,. Notice that 
w3 might also be only one R-step from w,, as it will be if R is transitive. 
If R is reflexive then every world will be n R-steps from itself for 
arbitrarily large (finite) n. Sometimes we don't even care about the 
direction of a relation. Thus in the frame 
136 


CANONICAL MODELS 
w, 
w2 
\ J 
w3 
you can't get from w1 to w2 by a sequence of R-steps, though you can if 
you are allowed to go backwards as well as forwards. Now some frames 
are composed of a number of parts, each completely isolated from any of 
the others. For example the frame 
o 
o 
1 
0 
o 
o 
is like this. We shall call such frames non-cohesive frames. By contrast 
a cohesive frame is one in which each world can see each other world in 
a number of forward or backward R-steps. For many purposes a non-
cohesive frame is most conveniently thought of as a collection of the 
cohesive frames of which it is composed. Nevertheless it is certainly a 
frame and in some contexts it is important to think of it as a single 
frame.11 
When we look at the frames of canonical models we see that the 
frames of some of them are not cohesive. An extreme example is 
provided by the Verum system. We showed on p. 121 that in the 
canonical model for this system each world is a dead end. The frame of 
this model therefore consists of a collection of worlds none of which is 
related to itself or to any of the others, and is thus as radically 
non-cohesive as any frame could be. We may, indeed, feel that it is more 
natural to regard it as a collection of distinct frames than as a single 
frame; and in fact the Verum system is characterized not only by the 
frame of its canonical model but also by the frame which consists of a 
single dead end. There is, however, this important difference between 
these two frames, that whereas there is a model based on the former (viz. 
the canonical model) which characterizes Ver, there can be no model 
based on the latter which characterizes it. The reason is that in any model 
based on a one-world frame, either p is true in every world or else ~p 
is true in every world; yet neither p nor ~p is a theorem of Ver. The 
case of the Trivial system is analogous. The frame of the canonical model 
for Triv consists of a collection of worlds each of which can see itself but 
137 
w, 
w2 
w3 


A NEW INTRODUCTION TO MODAL LOGIC 
none of the others. Triv is characterized both by this frame and by a 
one-world reflexive frame; but, for the same reason as in the case of Ver, 
it is characterized by a model based on the former, but not by any model 
based on the latter. 
Another canonical model whose frame is not cohesive is the canonical 
model for S5. This is not as obvious as for Ver or Triv, but in fact the 
frame of this model is split up into a number of disjoint sets of worlds, 
each isolated from all the others. The relation R is universal within each 
such set (i.e. each world is related to every world in its own set), but it 
is not universal over the whole frame. How do we know that the frame 
of the canonical model for S5 is like this? One simple proof is this: p is 
an S5-consistent wff, and therefore is true in some world in the canonical 
model for S5. Now if R were universal in that model, then Mp would be 
true in every world in it; and therefore, by corollary 6.6, it would be a 
theorem of S5. But we know that it is not. 
At this point one might perhaps begin to suspect that the frame of the 
canonical model for a normal modal system is never a cohesive frame. 
But in fact, for a quite wide range of systems we can prove that the 
frames of their canonical models actually contain a world that can see 
every world. For this to happen it will be sufficient to show, for a given 
system S, that { ~Lα:-| s α} is consistent. If this set is consistent then the 
canonical model of S will contain a world w* such that Lα G w* only 
when α is a theorem of S. But when α is α theorem it is a member of 
every world, and so if Lα G w* then a G w for every w G W, and so 
w*Rw. 
How can we prove that this does happen for a given system S? One 
way is as follows.12 We take the canonical model of S, and we extend it 
in the following way. We form a new model for S (call it (W+,R+,V+)) 
containing a world w* such that if V(Lα,w*) = 1 then 
s α. Let 
(W,R,V) be the canonical model of S and let (W+,R+,V+> be defined as 
follows: Choose some w* g W and let W+ = W U {w*}, R+ = R U 
{(w*,w):w G W}. For w G W, V+(p,w) = V(p,w). V+(p,w*) is 
arbitrary. Since every w G W can see by R+ all and only the worlds it 
can see by R an easy induction establishes that for all α and all w G W, 
V(α,w) = V+(α,w), 
(A) If V(La,w*) = 1 then |-s a; 
(B) <W+,R+,V+) is a model for S. 
138 


CANONICAL MODELS 
Proof of A: 
If V+(Lα,w*) = 1 then V+(α,w) = 1 for all w € W. So 
V(α,w) = 1 for all w E W and so, since (W,R,V) is the canonical model 
for S, |-s α. 
The proof of (B) is specific to S. In some cases it is easy. If S is K 
then the extended frame (W+,R+) automatically validates all K theorems, 
and therefore so does (W+,R+,V+). If S is T then by making w*R+w*, 
(W+,R+) is reflexive and so (W+,R+,V+) validates all T theorems, and 
so on. But of course if no w G W can see w* then R cannot be 
symmetrical. And if we made it so we might well change the truth-values 
of wff in worlds in W since such worlds can now see worlds they could 
not see before. That is not surprising in view of such results as that the 
canonical model of S5 is not cohesive. 
Since there is a model for S satisfying (A) then {~ Lα:-\ s α} is S-
consistent and so there is in its canonical model a world w such that for 
any wff a if Lα G w then |-s a. In that case α € w and so L~(w) Q w, 
i.e. wRw. Note that even if R+ is defined so that not w*R+w*, if 
V+(Lα,w*) = 1, V(α,w*) = 1, since \-s α and (W+,R+,V+) is a model 
for S. So if it were allowed that w*Rw* the values of all wff in 
(W+,R+,V+) would remain the same. Notice also that although in 
(W+,R+,V+) w* is not in the canonical model of S yet a result of the 
construction is that { ~ Lα: -\ s α} is S-consistent and so there must be a 
world w already in the canonical model whose only necessities are 
theorems, and which therefore can see every world, including itself, 
whether or not we set w* to see itself. 
A non-canonical system 
In this section we introduce a system, KW, which will appear from time 
to time in this part of the book. This system is K + 
W 
L(Lp D p) D Lp 
We give it Segerberg's name,13 though it is frequently called G after 
Gödel since it has been widely studied as the modal logic of 'provability'. 
If L means 'it is provable that' then one way of interpreting one of 
Gödel's incompleteness theorems is that if you could prove the 
consistency of arithmetic, which might be described by saying that you 
could prove that whatever is provable is true, i.e. L(Lp D p), then you 
could prove anything, i.e. Lp. At any rate it is possible to give a precise 
interpretation to L which has the consequence of validating exactly the wff 
139 


A NEW INTRODUCTION TO MODAL LOGIC 
which are theorems of KW. (We trust that the use of W as the name of 
a wff will cause no confusion with the use of W for the set of worlds in 
a frame.) In this book we will not discuss the provability interpretation of 
KW, but it turns out that KW is a very interesting modal system in that 
it lacks many features that we have come to expect in modal systems. 
The first of these features is that it is not what is called 
canonical.14 
Recall what happened in proving the completeness of T. We showed that 
the frame of the canonical model of T is reflexive. That means that not 
only is every theorem of T valid in the canonical model itself — that fact 
holds of every modal system — but it remains valid however bizarre a 
value-assignment we give to the variables on that frame. That includes 
assignments like the one mentioned above, where pi is true in a world if 
i is odd and pi is a member of that world, or i is even and pi is not a 
member of that world. We call a system S canonical iff the frame of S's 
canonical model is a frame for S. In the case of KW, although every 
theorem is (obviously) valid on the canonical model itself, this does not 
remain true when we vary the assignments on that same frame. 
We show this as follows. We first use the technique described above 
to show that where (W,R,V) is the canonical model of KW then (B) 
holds. This establishes that the frame of the canonical model of KW 
contains a world that can see itself. We then show that W is not valid on 
any frame that contains such a world. First, then, to prove (B) for KW. 
Since (W,R,V) is a model for KW then for any wff β, V(L(Lβ D β) D 
Lβ,w) 
= 1 and so V+(L(Lβ D β) D Lβ,w) = 1. So it is sufficient to 
show that V+(L(Lβ D β) D Lβ,w*) 
= 1. Suppose V+(L(Lβ D β),w*) 
= 1. Then, by A, 
kw Lβ D β. So by N, 
kw 
L(Lβ 
^ β)> so by W 
|-KW Lβ and so 
|-kw β and so V(β,w) 
= 1 for all w € W, and so 
V+(β,w) 
= 1 for all w such that w*R+w. So V+(L(3,w*) = 1. 
Now to show that W fails on every frame containing a world that can 
see itself. Let »^be such a frame and w* such a world, and consider a 
model (<^",V) in which V(p,w*) = 0 and V(/?,w) = 1 for every w E W 
other than w*. Then clearly 
(1) 
V(L/?,w*) = 0 
and so 
(2) 
V(Lp D p,w*) = 1. 
140 


CANONICAL MODELS 
But since p is true at all worlds other than w* we also have 
(3) 
V(Lp D p,w) = 1 
for every w E W other than w*. Hence by (2) and (3) we have 
V(Lp D p,w) = 1 for every w £ W, and therefore 
(4) 
V(L(Lp D p),w*) = 1. 
But (4) and (1) mean that W is false at w*, and thus that it fails on ^. 
Since the only assumption we have made about i^is that it contains a 
world that can see itself, and since the canonical model for KW contains 
such a world, we have shown that W is not valid on the frame of its 
canonical model. That is we have proved that KW is not canonical. 
Exercises — 7 
7.1 
Use canonical models to prove the completeness of the systems 
which result by adding to K the axiom listed, with respect to the 
conditions indicated: 
(a) 
MV MLp V Lp 
(Every world is or can see a dead end) 
(b) 
Rl 
MLp D (p D Lp) 
(If wRw' and w ≠w' then if wRw", w"Rwf) 
(c) 
p D LMMp 
(If wRw' then w'R2w) 
(d) 
MLp D Mp 
(If wRw' then there is some w" such that wRw" and w'Rw".) 
(e) 
ML{p A ~p) V (q D LMq) 
(Either w can see a dead end or if wRw' then w'Rw.) 
7.2 Prove that T + 
Mk L(LLp D Lq) D (Lp D q) 
is characterized by reflexive frames which satisfy the condition 
C Vw13w2(w1Rw2 A w2Rw, A Vw3(w2R2w3 D w,Rw3)) 
7.3 Use canonical models to prove the completeness of the systems 
which result by adding to K4 the axiom listed, with respect to transitive 
frames which satisfy the conditions indicated: 
Lem0 
L({j) A Lp) D q) V L((q A Lq) D p) 
(If wRw' and wRw" and w' ≠ w" then w'Rw" or w"Rw') 
141 


A NEW INTRODUCTION TO MODAL LOGIC 
HI p D L(Mp D p) 
(If wRw' and w'Rw" then either w = w' or w' = w") 
G0 
M(p A Lq) D L(p V Mq) 
(If w1Rw2 and w1Rw3 and w2 ≠ w3 then there is some w4 such 
that w2Rw4 and w3Rw4) 
7.4 KAltn is K + 
Altn LPl V L(p1 D p2) V ... V L((p1 A ... A Pn)D 
pn+]) 
Prove that KAltn is characterized by the class of frames in which every 
world can see at most n worlds. 
7.5 Prove that S5 is characterized by a single cohesive frame. 
7.6 Prove that no consistent system containing B has a canonical model 
based on a cohesive frame. 
7.7 Prove that KB + (Lp A p) D LLp is characterized by frames in 
which 
(i) 
if wRw' and w ≠ w" and w'Rw" then wRw" 
(ii) 
wRw' iff w ≠ w' 
7.8 RD (the 'rule of disjunction') is the rule that if |- Lα, V ... V Lαn 
then either |- a1 for some 1 ≤ i ≤ n. Prove that if RD is a rule of S 
then the canonical model of S contains a world that can see every world. 
7.9 Prove that K, T, S4, and KW provide the rule of disjunction. 
7.10 Prove that B, S4.2 and S5 do not provide the rule of disjunction 
7.11 Prove that Kl.l (S4 + Jl, L(L(p D Lp) D p) D p) is not 
canonical. (Hughes and Cresswell 1982.) 
Notes 
1 Prior 1957, Chapter 2. For a later and fuller introduction to the whole topic of 
the temporal interpretation of modal logics see Prior 1967. 
2 Prior 1957, p. 23. See also Prior 1955b. 
3 Prior 1958. 
4 The name S4.3 comes from Dummett and Lemmon 1959, p. 252. See also 
Kripke 1963a, p. 95. The completeness of S4.3 is proved (algebraically) in Bull 
142 


CANONICAL MODELS 
1965a. See also Prior 1962. 
5Segerberg 1971, p. 75 
6 Segerberg 1971, p. 78. Hughes and Cresswell 1984, pp. 84-86. The 
completeness of S4.3 when time has the structure of the rational numbers or the 
real numbers with R as < is proved in Segerberg 1970. When time has the 
structure of the natural numbers the system required is stronger than S4.3. (It is 
S4.3.1, see p. 180.) Where L means 'it always will be the case that' (so that R 
is irreflexive) the required system is K4.3, i.e. K4 + LemoL((P Λ Lp) D q) V 
L((q Λ Lq) D p). 
7 The name M is given in Lemmon and Scott 1977, p. 74 after a system discussed 
in McKinsey 1945 and called by him S4.1. This name is misleading since S4M 
is not a subsystem of S4.2. Further, Sobocinski 1964a, 1964c has used the name 
S4.1 for a system between S4 and S4.2. (See Hughes and Cresswell 1968, pp. 
265—67.) Sobocinski's name for S4M is Kl. The derivation of F in S4M is on 
p. 75. 
8 Lemmon and Scott 1977, p. 74. 
9 Gl was so named (see Dummett and Lemmon 1959, p. 252) after P.T. Geach, 
who had suggested it as an addition to S4 to reduce the number of distinct 
modalities and order them linearly. S4.2 is S4, i.e. K + T ( = L p D p) + 4 ( = 
Lp D LLp), + Gl. 
10 Examples of further extensions of K4 (i.e K + Lp D LLp) with a fairly 
extensive discussion may be found in volume 2 of Segerberg 1971. He also 
contains a discussion of the Alt systems mentioned in exercise 7.14. For a 
discussion of modalities in the Alt logics added to B see Ullrich and Byrd 1977 
and Byrd 1978. 
11 Cohesive frames allow chains to go forwards or backwards. For some purposes 
we might want to consider what are called generated frames. A frame (W,R) is 
generated iff there is some w* E W such that every w E W is on an R-chain 
from w* — i.e., if w 6 W then w*Rnw for some n ≥ 0. Where (W,R) is any 
frame, generated or not, and w* E W then (W*,R*) is called the subframe of 
(W,R) generated by w* iff (i) w E W* provided i E W and w*Rnw for some 
n > 0, and (ii) for w, w' E W*, wR*w>' iff wRw'. Where (W,R,V) is any model 
and (W*,R*) is the subframe of (W,R) generated by w* then (W*,R*,V*) is 
called the sub-model of W,R,V) generated by w* iff for w E W*, V*(p,w) = 
V(p,w). A straightforward induction establishes that for w E W* and any wff a, 
V*(α,w) = V(a,w). From this it follows that a wff is valid on a frame iff it is 
valid on all its generated subframes, and so any class of frames can be replaced 
by a class of generated frames. See Hughes and Cresswell 1984, pp. 77-81. 
Generated frames are used in Segerberg 1980 to formalize the logic of 
'elsewhere' (where R is ≠) mentioned in von Wright 1979. See exercise 7.7 and 
Jansana 1994. 
12 This proof is a variation of that given on p. 96 of Hughes and Cresswell 1984 
that the canonical model of any system which provides the rule of disjunction (see 
143 


A NEW INTRODUCTION TO MODAL LOGIC 
p. 71) has a world which can see every world. This result was obtained by a 
different method in van Benthem 1979a. 
13 Segerberg 1971, p. 84. It is called G in Boolos 1979. For a more recent survey 
of the history of provability logic see Boolos and Sambin 1990. The system dates 
at least from Lob 1966. 
14 The use of 'canonical' in this sense is due to Fine 1975a. 
144 


8 
FINITE MODELS 
The finite model property 
So far all our completeness proofs have been based on canonical models, 
and the technique has been to show that for any system S which is to be 
proved complete with respect to a class ^of frames, the frame of S's 
canonical model is in £! This gives an immediate completeness result 
since only the theorems of S are valid in S's canonical model. But we saw 
at the end of the last chapter that you can have systems where the frame 
of the canonical model cannot be in any class of frames which 
characterizes S, since not all theorems are valid on that frame. In this 
chapter we shall look at the question of when a system can be 
characterized by a class of finite frames. It will turn out that the standard 
systems, including KW, are so characterized, but that not every system 
is. Systems for which we can prove soundness and completeness with 
respect to a class of finite frames are said to have the finite model 
property. 
Establishing the finite model property 
Now the canonical model of a system S proved very useful because in a 
single model you have as valid all and only the theorems of S. But that 
is a stronger result than we need for completeness. Look at it this way. 
We need to show that for any wff a, if α is invalid then |-s α. Put in an 
equivalent way we need to show that if-| s α, then there is a model based 
on a frame in ^in which α is not valid. And this in turn can be shown 
if we can show that for any S-consistent set of the form {α} there is a 
model (W,R,V) where (W,R) G ^and for some w € W, V(α,w) = 1. 
It is clear that the frame of the canonical model is not finite, but in 
145 


A NEW INTRODUCTION TO MODAL LOGIC 
producing a model to falsify α we do not need to consider all the wff of 
modal logic, since the truth-value of α depends only on the truth-values, 
in the worlds of the model, of its well-formed parts, i.e. its sub-formulae. 
The idea of a wf part of a wff α should be clear. If α is 
L(p V ~L(~p V q)) V ~q, 
its wf 
parts 
are α 
itself and 
L(p V ~L(~p 
V q))t 
~q, 
(p V ~L(~p V q)), 
~L(~p V q), 
L(~p 
V q), (~p V q), ~p, p and q. Note that α is always a wf part 
of itself. If we wish to exclude this we speak of a proper part of α. 
For a given wff α then the idea is that we make a kind of 'mini 
canonical model' using only the wf parts of a. For each α this model will 
be finite, but otherwise it will behave just like the real canonical model, 
and we can use it to establish the finite model property for many 
systems.1 In the case of KW we shall be able to use it to establish a 
completeness result where the canonical model method does not work. 
We define the mini canonical model based on a wff α as follows. Let 
$ a be the set {0:0 is a sub-formula of α} and let $^ be <J>a U { ~β:β G 
<£a}. Clearly both $a and <i>a
+ are finite. Say that a set T of wff is α-
maximal S-consistent (for short mc) iff T Q <l>a
+ and 
(i) For all 0 G $ a either ^ G T o r - ^ G r (α-maximality) 
(ii) Where T = {γ l, ... , γ n} then not h ~(γ i Λ ... Λ γn) (S-
consistency) 
[Note that (ii) is equivalent to the 'regular' definition - viz there is no 
subset Λ c r, where Λ = {γl , ... , γn} and \-s ~(γ, Λ ... Λ γn).] 
The results which follow parallel those obtained in chapter 6 except that 
the sets here are mc only in $a
+. 
LEMMA 8.1 If β G $ a then exactly one of β and -β G T. 
Proof: By maximality at least one is and by consistency both cannot be, 
since \-s —(β Λ —β). 
LEMMA 8.2 If β V γ e $a then β V γ G T iff either β G T or γ £ 
r. 
Proof: If β V γ G T but β g T and γ £ T then if β V γ G $ a so are 
0 and γ and so -β G T and ~ 7 G T. But then {~β, ~γ, β V γ} £ 
T and h s ~ ( ~ i β Λ ~ γ Λ ( β V γ ) ) s o r would not be consistent. If 
146 


FINITE MODELS 
β V γ g T then since β V γ G $ a, -(β V 7) G I\ but if β G I\ 
{-(β V 7), β} c r, but h ~ ( ~ ( β V 7) A β) so β g T and if 7 G 
r then {-(β V 7),T} c r, but \-s ~ ( ~ ( β V 7) A 7) so 7 £ T. 
LEMMA 8.3 If A Q $^ and A is S-consistent then there is an mc T such 
that A c r. 
Proo/i Construct T as follows. Order the wff of $+, β„ ... , βn. Let T0 
= A and for 0 < k < n let Tk+1 = Tk U {βk+l) if this is consistent and 
Tk U {~βk+l} 
otherwise. If neither is consistent then where β0 is the 
conjunction of wff in A, we have |-s (β0 A ... Aβk) D βk+1 and |-s (β0 
A ... Aβk) D ~βk+1, and so f-s ~(βO A ... Aβ,), i.e. Tk is 
inconsistent. So given that T0 is consistent so is Tn. But Tn is mc. 
Given that a is not a theorem of S the aim is to construct a model 
based on a frame in if in which a is false. Call this model (Wa,Ra,Va), 
though unless it matters we may speak simply of (W,R,V). W is the set 
of all a-maximal S-consistent sets of wff. Where S is K, T or D, we let 
R be defined as in the canonical model. To be specific, for w, w' G W, 
wRw' iff for allZ/y G w, 7 G w', i.e. iffL~(w) Q w'. For p G $ a, let 
V(p,w) = 1 iff/? G w. For p £ $ a the definition is arbitrary. 
THEOREM 8.4 
For β G $a and w G W, V(0,w) = 1 iff β G w. 
Proof: The result is defined to hold for the variables. Consider ~jS G 
$ a. Since — j(? G $ a then so is β, and we may assume the result for β. 
So V(~β,w) = 1 iff V(β,w) = 0, iffβ £ w iff ~β G w. Consider β 
V 7. If jS V 7 G $ a then so are β and 7 and we may assume the result 
for both β and 7. So V(β V T,w) = 1 iff V(β,w) = 1 or V(T,w) - 1, 
iff jS G w or 7 G w. But 0 V 7 G $ a. So by lemma 8.2 this last holds 
iff (β V 7) G w. 
SupposeLβ G w and wRw', then β G w', and so 0 G 3>a, so V(/J,w') 
= 1. So V(L0,w) = 1. 
Suppose Lβ £ w but L/J G <J>a. Then — Lβ G w. Lemma 6.4 on p. 
117 guarantees that {7: Ly G w} U {~0} is S-consistent. Now note that 
every member of {7: L7 G w} U {—/?} is in $ a except possibly ~/J. 
But —(3 G $^. So if {7: Z/y G w} U { — (3} is consistent then by lemma 
8.3 there will be an mc w' with wRw', and —/? G w'. So 0 $: w'. But 
jS G $ a since L0 G $ a and so V((3,w') = 0 and so V(L(3,w) - 0. This 
proves theorem 8.4. 
This immediately gives us the fact that K has the finite model property 
147 


A NEW INTRODUCTION TO MODAL LOGIC 
since (Wa,Ra) is certainly a frame, and in the case of K, ^is the class of 
all frames. 
For T we must show that (Wa,Ra) is reflexive, and for D that it is 
serial. In the case of T we have to show that for any w G W and any L/? 
G w, if L(3 G w then (3 G w. (Obviously if L(3 G $a then 0 G $a.) 
Note that there may not be any wff at all of the form L/J in w, as for 
instance if a contains no modal operators. In that case L~(w) would be 
empty, and trivially L~(w) Q w. If L~(w) £ w then there would have to 
be some (3 G <f>a such that L(3 G w but 0 g w. Since 0 G $a but (3 g 
w, ~(3 G w. But then {L(3,~(3} Q w, and since \-T ~(LjS A ~/3), w 
would be inconsistent. In the case of D, if R were not serial there would 
have to be a w G W such that there is no w' such that L~(w) Q w'. But 
this means that L~(w) is inconsistent. So there are L/J,, ... , L(3n G w 
such that 
h> -(/?, A ... A 0J 
So by N, 
h D L ~ ( ^ A ... A 0J 
so by D 
|-D - 1 ( 0 , A ... A jSJ 
so 
|-D ~(Lj3, A ... A L/3J. 
But {LjS,, ... ,LjSn} ^ w, and this would make w inconsistent. 
Even in these cases it can be seen that the proofs need to be a little 
more complicated than in the case of the proofs by canonical models, for 
the worlds in these frames are made up using only sub-formulae of a or 
their negations. When we move to S4 this becomes even more of a 
problem. For recall how we proved that R in the canonical model of S4 
is transitive. We reasoned that since L(3 G w then (by Lp D LLp) LL(3 
G w. However we now have no guarantee that LL(3 will be in <f>a just 
because L(3 is, and so we cannot use this method. There are a number of 
ways around this problem. The simplest is to change the definition of R.2 
Instead of saying that wRw' if wherever Lfi G w then (3 G w' we say 
that wherever L0 G w thenL/J G w'. (If we use L(w) for {L(3: L(3 G w} 
148 


FINITE MODELS 
then we could say that wRw' iff L(w) Q w'.) Now it is clear that R as so 
defined is transitive. It is also clear that theorem 8.4 holds in respect of 
the variables and the truth-functional operators. But because we have 
changed the definition of R we now have to establish the induction for L: 
SupposeLj3 € wand wRw', then L(3 G w'. SinceL(3 G $ a, (3 G 3>a 
and so by the T-axiom (3 G w' (since otherwise ~/J would be, making 
w' inconsistent). So V(0,w') = 1. So V(L(3,w) = 1. Suppose L(3 £ w but 
L(3 G $a. Then ~L(3 G w. We show that the following set is S-
consistent: 
A = {Ly.Ly 
G w} U {-(3} 
Note that every member of A is in $a except possibly — 0. But (3 G $a. 
So if A is consistent then by lemma 8.3 there will be an mc w' with A Q 
w'. For such a w' we have wRw'. Let L7l, ... , L7n be all the wff 
beginning with L in w. Then if A were inconsistent 
|-S4 ~(Z/y, A ... A L7n A ~0) 
so 
h 4(^Ti A ... A LyR)D 
(3 
so 
h* L(L7l A ... A L7n) D L0 
so 
hs4(^7i A ... A LLyJ D L(3 
so, since (-S4 L/? s LLp, 
\-SA(Lyl A ... A L7n) DL0 
so |-S4 ~tf<Yi A ... A L7n A ~L0). 
But {L7l, ... , L7n, ~L/?} <= w, and so w would be inconsistent. Since 
wRw' and ~ 0 G w' then (3 g w'. But (3 G $a since L0 G $a and so 
V(/?,w') = 0 and so V(LP,w) = 0. This proves that theorem 8.4 also 
holds in the case of S4. Since -| s a then { ~a} is consistent and so, since 
a G $ a, ~ a G w for some w G W. So V(a,w) = 0. Thus S4 has the 
finite model property. 
We can adapt the result to K4 by defining wRw' iff L(w) U Lr(u>) Q 
w'. For B we have wRw' iff L~(w) Q w' and L~(w') Q w; for S5 wRw' 
149 


A NEW INTRODUCTION TO MODAL LOGIC 
iff L(w) = L(w'), and so on. What is of course specific to each system 
is the definition of R. Given any system S, to prove by this method that 
S has the finite model property, we must find a definition of R which (a) 
makes the resulting frame a frame for S, and (b) enables us to prove the 
analogue for S of theorem 8.4 - i.e. the theorem that establishes that truth 
at a world is equivalent to membership of that world. And this is a non-
trivial task, which must be attempted system by system.3 
The completeness of KW 
We showed in the last chapter that KW is not canonical. Nevertheless it 
is complete, and its completeness can be proved by the methods of the 
present chapter.4 For KW the relevant class if of frames is frames which 
are finite, irreflexive and transitive. It is not hard to see that W is valid 
on all such frames, and therefore that KW is sound with respect to & 
validity. We now prove completeness. We note first that 4 - Lp D LLp 
- is a theorem of KW. The proof is as follows: 
p D ((Lp A LLp) D (p A Lp)) 
Lp D L((Lp A LLp) D (p A Lp)) 
Lp D L(L(p A Lp) D (p A Lp)) 
Lp D L(p A Lp) 
Lp D LLp 
Q.E.D. 
We assume the methods of the previous section, but will prove the 
appropriate version of theorem 8.4 explicitly for KW. We proceed as 
follows. Given that a is not a KW-theorem the aim is to construct a finite 
irreflexive and transitive model in which a is false. W is the set of all a-
maximal KW consistent sets of wff. For w, w' G W, wRw' iff 
(i) For all Ly G w, Ly, y G w' 
(ii) There is some L0 G w' such that Lfi £ w. 
Note that if Ly G w and L(3 G w' then Ly G <£>a and L(3 G <£>a. For p 
G <i>a, let V(/?,w) = 1 iff/? G w. For/? £ <l>a the definition is arbitrary. 
THEOREM 8.4' 
For 0 G $a and w G W, V(0,w) = 1 iff 0 G w. 
Proof: As before the result is defined to hold for the variables and is 
preserved by — and V. 
Suppose L(3 G w and wRw'. Then (3 G w', and so 0 G $ a, so 
PC 
(1) 
(1) X DR1 
(2) 
(2) X K3 
(3) 
(3) X W 
(4) 
(4) X Kl x PC 
(5) 
150 


FINITE MODELS 
V(P,w') = 1. So V(L/?,w) = 1. Suppose^ g w but L0 G <S>a. Then 
~L/? G w. We show that the following set is KW consistent: 
A = {Ly: Ly G w} U {7: Ly G w} U {L0, - 0 } 
Note that every member of A is in $a except possibly ~/?. But 0 G $ a. 
So if A is consistent then by lemma 8.3 there will be an mc w' with A Q 
w'. For such a w' we have 
(i) IfL 7 G wthenZ/y G w' 
(ii) If L 7 G w then y G w' 
(iii) L/J G w' but L/J g w. 
These three conditions ensure that wRw'. Let LY,, ... , Lyn be all the wff 
beginning with L in w. Then if A were inconsistent 
hew ~(^7i A ... AL7n A 7 l A ... A 7 n A L(3 A ~0) 
so 
hcw(^7i A ... A L7n A 7 l A ... A 7n) D (L0D0) 
so 
I - K W ^ T I A ... A Lyn 
A 7 l A ... A 7n) D I(L0 
D 0) 
so 
K w (LL7l A ... A LLyn A L7l A ... A L7n) D L(L0 D 0) 
so, since |-KW Lp D LLp, 
Kw(^Ti A ... A L7n) D L(L(3 D (3) 
so, by W, 
hew (^7i A ... A L7n) DL0 
so 
Kw ~(£<Yi A ... A L7n A ~L0). 
But {L7l, ... , L7n, ~L/?} Q w and so w would be inconsistent. Since 
wRw' and ~ 0 G w' then 0 £ w'. But 0 G $ a since L0 G $ a and so 
V(0,w') = 0 and so V(L(3,w) = 0. This proves theorem 8.4'. 
Since a G <£a and -| KW a then { ~ a} is consistent and so ~ a G w 
for some w G W. So V(a,w) = 0. It is clear that (Wa,Ra,Va> is finite, 
151 


A NEW INTRODUCTION TO MODAL LOGIC 
irreflexive and transitive, so a fails in such a model. 
The word 'finite' here is crucial. The system characterized by all 
transitive irreflexive frames is K4. That does not mean that K4 lacks the 
finite model property - in fact we proved on p. 149 that K4 has that 
property. But although K4 is characterized by the class of all finite 
transitive frames and by the class of all transitive and irreflexive frames 
it is not characterized by any class of finite transitive and irreflexive 
frames. 
Decidability 
A system S (not necessarily a modal system) is said to be decidable iff 
there is an effective procedure whereby, for any given wff a, it can be 
determined in a finite number of steps whether or not a is a theorem of 
S. Some systems of logic are known to be decidable, others are known 
not to be decidable, and of yet others it is not known whether they are 
decidable or not. This is so for modal as well as for non-modal systems. 
There is no effective procedure for determining, for an arbitrary system 
of logic, even for an arbitrary normal modal system, whether or not it is 
decidable. 
There is, however, a certain connection between possession of the 
finite model property and decidability. We shall now prove that this 
connection holds.5 
THEOREM 8.5 
If S is a finitely axiomatizable normal modal system 
which has the finite model property, then S is decidable. 
Proof: Let S be a system of the kind described. To say that S is finitely 
axiomatizable (see p. 50) is to say that there is a finite collection A of wff 
such that the theorems of S are precisely those wff which can be derived 
from the formulae in A, together with PC-tautologies and K, by the rules 
US, MP and N. This means that any frame ^ i s a frame for S iff every 
wff in A is valid on &. Moreover, if ^ i s finite, there will be a finite (and 
obviously effective) procedure for checking whether or not all the (finitely 
many) wff in A are valid on J^ and thus whether or not ^ i s a frame for 
S. Now it is not difficult to see that, if we disregard isomorphic 
duplicates, there is an effective procedure for generating all finite frames 
in some definite order, and therefore for generating all the finite frames 
for S in some definite order (since each finite frame can be effectively 
checked for whether or not it is a frame for S). Since S has the finite 
model property, if a is not a theorem of S then it is invalid on some finite 
152 


FINITE MODELS 
frame for S; and therefore, in our effectively generated sequence of finite 
frames for S there will (eventually!) appear one on which α is invalid. If 
α is a theorem of S, then of course a frame on which it is invalid will 
never appear in the sequence we have described. There is, however, also 
an effective procedure for generating all the proofs of theorems of S in 
some definite order. (A proof of a theorem α of S is a finite sequence of 
wff in which each wff is either a PC-tautology, or K, or a member of A, 
or a wff derived from some earlier wff in the sequence by US, MP or N, 
and in which α is the last member, α is a theorem of S iff there is such 
a proof of α.) Hence if a is a theorem of S, a proof of α will (again, 
eventually!) appear in this generated sequence of proofs. Since any wff 
α either is or is not a theorem of S, therefore, either a frame on which 
α is invalid will appear in a finite number of steps in the first sequence, 
or a proof of α will appear in a finite number of steps in the second 
sequence (but not, of course, both). In the former case, α is not a 
theorem of S; in the latter case it is. 
This gives an effective procedure for determining of any wff whether 
or not it is a theorem of S, and so proves the theorem. (We are not, of 
course, suggesting that the procedure we have described would be of 
much use in actual practice for discovering whether some particular 
formula is a theorem of S or not. For some of the best-known systems 
more practical procedures are described in Chapter 4, and the methods 
explained there can easily be adapted for many other systems as well.) 
It is important to notice what theorem 8.5 does not say as well as what 
it does. First, it is only for finitely axiomatizable systems that possession 
of the finite model property guarantees decidability. There are, in fact, 
systems which have the finite model property but are undecidable, though 
of course they are not finitely axiomatizable.6 Second, even if we confine 
our attention to finitely axiomatizable systems, possession of the finite 
model property, although a sufficient condition of decidability, is not a 
necessary one. There are, in fact, finitely axiomatizable systems which 
are decidable but which lack the finite model property. Third, theorem 
8.5 does not say that every decidable system with the finite model 
property is finitely axiomatizable. There are in fact systems of this kind 
which are not.7 
Systems without the finite model property 
That a system has the finite model property is by no means a trivial fact, 
for there are systems which lack this property. The first published proof 
that a normal propositional modal system lacks the finite model property 
153 


A NEW INTRODUCTION TO MODAL LOGIC 
was given by David Makinson and we shall adapt his proof.8 The system 
we shall discuss may be called Mk and is T with the addition of the single 
extra axiom. 
Mk L(LLp D Lq) D {Lp D q) 
Mk is characterized by the class of reflexive frames which satisfy the 
condition 
C 
y/wl3w2(wlRw2 A w2Rwx A >/w3(w2K2w3 D vv,Rn>3)) 
where w2R2w3 means that there is some w such that w2Rw and wRw3. C 
says that every world can see some world which (a) can see it in return, 
and (b) is such that whatever it can see in two steps, the original world 
can see in one. It is easy to check that Mk is sound with respect to 
models satisfying C, and it is also straightforward to establish that the 
canonical model of Mk satisfies C, thus yielding completeness. 
Our present task however is to establish that Mk does indeed lack the 
finite model property. We shall do this by showing that every finite 
reflexive frame on which Mk is valid is transitive. So if ifis any class of 
finite frames for Mk, Lp D LLp would be in valid; and so if such a class 
were to characterize Mk, Lp D LLp would have to be a theorem. But we 
shall show that Lp D LLp is not a theorem of Mk, and so Mk does not 
have the finite model property. 
First then to show that every finite reflexive frame on which Mk is 
valid is transitive. If (W,R) is any frame then we say that w,, ... , wn 
form a non-transitive chain of length n (for n > 3) iff for 1 < i < n, 
WjRwi+1, where w-x 5^ wi for 1 < i 5^ j < n, and not WjRvV; for any i > 
2. A non-transitive chain looks like this 
w, -* w2 ... -* wn 
where each w{ is distinct and w{ cannot see any other world in the chain 
besides itself and w2. If (W,R) is non-transitive then it has at least one 
non-transitive chain, and if it is finite it will have a maximal non-
transitive chain, where a maximal chain is a chain of length n and there 
is no non-transitive chain of greater length in the frame, though there may 
be other chains of equal length. 
Given that (W,R) is a finite non-transitive reflexive frame and that wlf 
... , vvn is a maximal non-transitive chain, we show that Mk is not valid 
154 


FINITE MODELS 
on (W,R) by showing that it can be falsified at w,. Let (W,R,V) be a 
model based on (W,R) in which p is true everywhere except at vv3, ... , 
vvn, and q is true everywhere except at w{. Then Lp D q is false at wx. 
Now consider L(LLp D Lq) and consider any w such that WjRvv. (a) If 
not wRw„ then V(Lq,w) = 1 since q is only false at w,, and so in this 
case V(LLp D Lqyw) = 1. (b) If wRw; for any 1 < i < n, V(LLp,w) = 
0 and so again V(LLp D Lq,W) = 1. So, if V(LLp D Lq,w) = 0, then, 
from (a) and (b), if w,Rw then wRw, but not wRw{ for 1 < i < n. But 
if wRwj and not wRw{ for 1 < i < n, then w, wlt ... ,wn will be a non-
transitive chain of length greater than n, contradicting the fact that w,, ... 
,wn is a maximal chain. (Reflexiveness is needed for the case i = n.) So 
V(LLp D Lq,w) = 1 for every w such that w,Rw and so W(L(LLp D 
Lq),wx) — 1 so Mk is false at wx. 
It only remains to show that Lp D LLp is not a theorem of Mk. For 
that purpose we produce a reflexive and non-transitive infinite frame on 
which Mk is valid. Since Lp D LLp fails on any non-transitive frame this 
will show that Lp D LLp is not a theorem of Mk. The frame we shall use 
is called the recession frame.9 Its worlds are just the natural numbers 0, 
1, ... etc. Each number can see (a) itself, (b) its immediate predecessor 
and (c) each greater number. Formally we say that wRw' iff w < w' +1. 
So let (W,R) be the recession frame and suppose that Mk is false at some 
n. Then 
(i) V(L(LLp D Lq),n) = 1 
(ii) V(Lp9n) = 1 
(iii) V(</,n) = 0 
From (ii) we have that V(p,k) = 1 for every k > n — 1, and thus V(L/?,k) 
= 1 for every k > n, and thus 
(iv) V(LL/?,n+l) = 1 
so from (i) 
(v) V(L</,n+l) = 1 
But this contradicts (iii), and so establishes, by reductio ad absurdum, the 
validity of Mk on the recession frame. Since 2R1 and 1R0 but not 2R0, 
then the recession frame is non-transitive. In fact Lp D LLp fails at 2 
155 


A NEW INTRODUCTION TO MODAL LOGIC 
when p is false at 0 but true everywhere else. 
This establishes that Mk lacks the finite model property.10 
Exercises — 8 
8.1 A modality is an unbroken sequence, possibly empty, of monadic 
operators ( ~ , L, M). For any wff a, let $£* be the set of all wff A(3 
where (3 is any sub-formula of a and A is any modality. Let (W,R,V) be 
the mini canonical model for S4 based on $J? with R defined so that 
wRw' iff for every Ly G w, y £ w'. Show that R is reflexive and 
transitive, and explain why this shows that S4 has the finite model 
property. 
8.2 Prove that the systems S4.2, S4.3, S4M all have the finite model 
property. 
8.3 Prove that KW + Lem0 (L((p A Lp) D q) V L((q A Lq) D p)) is 
characterized by frames in which W is a finite initial segment of the 
natural numbers and R is > . 
8.4 
Prove that K l . l (i.e. K + J l : L(L(p D Lp) D p) 
D p)) is 
characterized by finite frames in which W is reflexive, transitive and 
antisymmetrical. (You may assume that 4 is a theorem of Kl.l.) 
8.5 
Let (W,R) be the following frame: 
(i) W is the set of all pairs (n,m) of natural numbers; 
(ii) (n,m)R(j,k)iffn < j . 
Prove that (W,R) characterizes S4.3. 
8.6 
Prove that every proper extension of S5 is SSAlt^ for some n. (This 
is a difficult exercise. See Segerberg 1971, pp. 122-128.) 
8.7 
Mk* is T + L(LLp D LLLp) D (Lp D LLp). Prove that Mk* lacks 
the finite model property. 
8.8 
Prove that K3.1 (i.e. K l . l + Lem0) is characterized by frames in 
which W is a finite initial segment of the natural numbers and R is > . 
Notes 
1 The method described in the text shows how to give a direct construction of a 
finite model. A more widely used method is found in Lemmon and Scott 1977. 
156 


FINITE MODELS 
This method has become known as the method of 'filtrations' and consists in 
taking a model together with a wff a and making a finite model which is 
equivalent to it in respect of sub-formulae of a, or in respect of some nominated 
set of wff. An exposition of this method is found on pp. 136-145 of Hughes and 
Cresswell 1984. (Note that the completeness proof given for KW on pp. 145-148 
of that work is defective. A correct proof appears in Hughes and Cresswell 1986.) 
The term 'filtration' appears to be due to Segerberg 1968a. The method of 
filtrations is also described and used to prove that a system has the finite model 
property in Segerberg 1971, Gabbay 1976 and Chellas 1980. A method of proving 
that a system has the finite model property without using filtrations may be found 
in Fine 1975b. Fine's method uses normal forms, and may be applied to all the 
systems discussed in this section. He is also able to use his method to prove that 
the system KM (i.e. K + the wff M discussed on p. 131 above) has the finite 
model property. Fine's method can be modified to yield a completeness proof for 
KM which has affinities with the mini canonical model type of completeness proof 
used in the present chapter (see Cresswell 1983a). The earliest proofs of the finite 
model property were obtained algebraically. See McKinsey 1941 (for S2 and S4), 
Bergmann 1949 (for S5), Bull 1964, 1965b (for various extensions of S4). Every 
extension of S5 not only has the finite model property but is characterized by a 
single finite frame. In fact it is Altn for some n. See Segerberg 1971, pp. 122-128 
and Scroggs 1951. S5 itself is not so characterized; see Dugundji 1940. 
2 For some systems we may also need to extend $ +. (See Cresswell 1983b.) 
3 An even stronger result is known about S4.3. It was proved long ago, in Bull 
1966, that not only S4.3 itself, but every normal extension of it, has the finite 
model property. Bull's proof was algebraic, but the same result has more recently 
been proved semantically in Fine 1971, Segerberg 1973a and Gabbay 1976. (See 
also Goldblatt 1987, pp. 60-63.) Fine, op. cit., has also proved that every normal 
extension of S4.3 is finitely axiomatizable. Another result which has been proved 
about S4.3 (in Segerberg 1975) is that in any system which contains all the 
theorems of S4.3 and has the rules US and MP, we can obtain N as a derived 
rule. In that sense, N would be a redundant item in an axiomatic basis for such 
a system. Bellissima and Mirolli 1983 show how to provide an axiomatization of 
the modal logic characterized by any particular finite frame. 
4 A completeness proof for KW is given on pp. 86-88 of Segerberg 1971 and in 
Chapter 7 of Boolos 1979. Boolos also provides a decision procedure for KW in 
the style of Chapter 4 above and extracts a completeness proof from it. (Indeed 
the techniques of that chapter yield alternative proofs of the finite model property 
for the systems treated there.) The proof of 4 given here is adapted from Boolos 
1979, p. 30. 
5 This theorem is proved in Segerberg 1971, pp. 34-36. Note, however, that 
Segerberg uses the term 'axiomatizable' to mean what we mean by 'finitely 
axiomatizable', and uses 'finitely axiomatizable' to mean finitely axiomatizable 
without using N. In our terminology a (normal) logic S would be said to be 
157 


A NEW INTRODUCTION TO MODAL LOGIC 
axiomatizable iff there is some effectively specifiable set A of wff such that S is 
K + A. The system presented in Urquhart 1981 can be adapted so that its axioms 
correspond to an arbitrary non-recursively enumerable set of numbers, and the 
resulting system will not be axiomatizable in the sense we are using. 
6 Urquhart 1981 has produced an example of such a system. Although it is not 
finitely axiomatizable, its axioms are effectively specifiable. Kracht 1991 provides 
a similar example which is an extension of S4. Conversely, there are finitely 
axiomatizable undecidable systems (which of course lack the finite model 
property). See Isard 1977. 
7 See the proof of this for the system BSeg in Cresswell 1979. (BSeg is (MMpx 
A ... A MMpn) D M{Mpx A ... A Mpn), forn > 1. See Hughes and Cresswell 
1975.) 
8 Makinson 1969. Makinson's system is in fact slightly weaker than Mk. It is T 
+ L(LLp D LLLp) D (Lp D LLp). Interestingly no completeness proof appears 
to have been provided for this system. An extension of S4 without the finite 
model property is provided in Fine 1972. 
9 This name appears to be due to van Benthem 1978, p. 30. Blok 1979 
axiomatizes the logic characterized by the recession frame in which the 'truth 
sets' of wff are finite or cofinite. (See p. 162.) 
10 As Gabbay 1976, pp. 258-265 shows, the fact that a system lacks the finite 
model property does not stop it from being decidable. See also Cresswell 1984. 
158 


9 
INCOMPLETENESS 
In previous chapters we have proved the completeness of a number of 
systems of modal logic, but always relative to some given class % of 
frames. In this chapter we show that there exist systems which are 
incomplete in the sense that there is no class ^fof frames such that their 
theorems are precisely the ^valid wff. But we must first make some 
remarks about the difference between frames and models. 
Frames and models 
If we were to pose the question of completeness in terms of models, that 
is to say if we were to ask whether, for a given system S, there is always 
a class ^ o f models such that a is ^ valid iff |-s a, the answer would 
have to be (trivially) yes. For the class consisting of the canonical model 
on its own would do the trick. But as we remarked on p. 112 validity in 
models may not be quite the appropriate notion. In fact validity in models 
lacks an important property: it is not preserved by all the transformation 
rules. In other words just because all members of a set A of wff of modal 
logic are valid in a model (W,R,V), it does not mean that all theorems of 
K + A are. It is, indeed, easy to show that MP and N are 
validity-preserving in a single model. For if both a and a D /? are true 
in every world in W, then by [VD] so is /J. And if a is true in every 
world in W, then a fortiori it is true in every world that any world in W 
can see; so La will also be true in every world in W. The same, 
however, does not hold for US. For to say that US is validity-preserving 
in a single model would be to say that if a wff a is true in every world 
in a model, then so is every substitution-instance of a; and it is easy to 
159 


A NEW INTRODUCTION TO MODAL LOGIC 
see that this does not hold generally. To take the simplest case, it is a 
straightforward matter to define a model in which p is true in every world 
but q is not; yet q is certainly a substitution-instance of/?. Of course, p 
is not an axiom of any normal modal system (at least not of any consistent 
one), but the same situation obtains even for a wff that is such an axiom. 
There is no difficulty, for instance, in defining a model in which Lp D 
p is true in every world but Lq D q is not. An example would be a 
model consisting of only two worlds, wx and vv2, where we have w1Rw2 
but neither world is related to itself, and in which/? is true in both worlds 
and q is false in w, and true in w2. 
So we cannot be sure that if a collection of wff are all valid in a given 
model, all the wff derived from them by US, MP and N are also valid in 
that model. What we can be sure of, however, is that these derived wff 
will be valid in the model if not only they themselves but all their 
substitution-instances are valid in it. This result can be stated as follows: 
THEOREM 9.1 
If every substitution-instance of every member of a set 
A of wff is valid in a model (W,R,V) then every 
theorem of K + A is valid in (W,R,V). 
We outline how this theorem can be proved, but leave the details to the 
reader. Suppose we have a model (W,R,V). Let us say that a wff is 
generalizable iff all its substitution-instances are valid in (W,R, V). Then 
the hypothesis of the theorem is that all the axioms of S, i.e. all wff in A, 
are generalizable. The proof then takes the form of showing that any wff 
that is obtained from generalizable wff by any of the transformation rules 
(including US) is itself generalizable. 
An incomplete modal system 
KH is K with the addition of the single wff 
H 
L(Lp = p) D Lp 
We show that KH is incomplete, i.e. that it is not characterized by any 
class of frames.1 In order to show the incompleteness of KH it will be 
sufficient to show two things: 
A 
If H is valid on ^"then so is Lp D LLp. 
B 
Lp D LLp is not a theorem of KH. 
160 


INCOMPLETENESS 
First we must show why this establishes the incompleteness of KH. To 
say that KH is complete is to say that there is a class ^of frames such 
that 
C 
(i) If I-KH a then a is valid on every &" G &. 
(ii) If a is valid on every & G £J then J-^ OL. 
We show that C together with A and B leads to a contradiction. For 
consider any & £ %. Since [-KH H, then by C(i) H is valid on iT But 
then, by A, Lp D LLp is valid on &. So by C(ii) 1-^ Lp D LLp. This 
contradicts B. 
Proof of A: 
We prove A by contraposition. I.e. we show that if 
Lp D LLp is not valid on & neither is H. Since Lp D LLp is valid on 
every transitive frame, if Lp D LLp is not valid on &~, there must be w,, 
vv2, vv3, such that w,Rw2, w2Rw3 but not H>,RW3. 
Divide the worlds into two classes as follows. If there is an R-chain 
(see p. 136) leading from w to w>3, let V(/?,w) = 0. (In accordance with 
the definition of an R-chain given on p. 136 assume that there is a 0-step 
R-chain leading from vv3 to itself, and so put V(p,w3) = 0.) If there is no 
such chain let V(p,w) = 1. First consider a w from which there is an R-
chain leading to w3. Now, unless w is w3 itself, if w is on an R-chain to 
vv3, it can see at least one world w' also on an R-chain to w3. So V(p,w) 
= 0 and V(p,w') = 0, and so V(Lp,w) = 0. Thus V(Lp = /?,w) = 1. 
Now consider a w from which there is no R-chain to w3. If there is no 
such chain from w then there is also no such chain from any w' that w 
can see. So V(p,w) = 1 and V(p,w>') = 1. So V(L/>, w) = 1 and so V(Lp 
= p, w) = 1. 
This means that V(Lp = py w) — 1, for every w except possibly u>3. 
But Wj cannot see w>3, and so V(Lp = p, w) = 1 for every w such that 
WjRw. So V(L(Lp = p),wx) = 1. But w2 is on a chain to w3 and so V(p, 
w2) = 0. So V(L/?, Wj) = 0 since w1Rw2. So H fails at w>j in this frame, 
and thus every frame for H must be transitive, and must in consequence 
validate Lp D LLp. This establishes A. 
Now theorem 9.1 guarantees that if a is any wff (here H) then any 
model which validates every substitution-instance of a, validates every 
theorem of K + a. So, to establish B we must produce a model (W,R, V) 
on which every instance of H is valid, but Lp D LLp is not. 
161 


A NEW INTRODUCTION TO MODAL LOGIC 
Proof of B: 
Let ^"be the following frame: W consists of two parts. One 
part consists of the 'ordinary' natural numbers 0, 1, 2, ... etc. The other 
part is in fact the recession frame introduced in the last chapter and 
consists of a copy of the natural numbers, 0*, 1*, 2*, ... etc. Call the 
'ordinary' part N, and the 'starred' part N*. Then W = N U N*. 
R is defined as follows: 
(i) For n, m G N, nRm iff n > m. 
(ii) For n*, m* G N*, n* Rm* iff n < m+1. 
(iii) For m G N, n* G N*, n*Rm. 
It might be easiest to imagine &*(= (W,R)) as follows: 
0* 1*2* .... n* 
m... 2 1 0 
N* 
N 
The members of N, the 'ordinary' numbers can see only numbers less 
than themselves, and each member of N*, each starred number, can see 
itself, its immediate predecessor, all greater starred numbers (that is what 
(ii) says) and all 'ordinary' numbers. 
We now define a model (SF, V) based on ^ . For every variable /?, let 
V(p,0*) = 0 and for every w * 0*, let V(p,w) = 1. 
LEMMA 9.2 
V(Lp D LLp, 2*) = 0 
Proof: Since 1*R0*and V(p,0*) = 0, then V(Lp,l*) = 0. Since 2*R1*, 
V(LL/?,2*) = 0. But since not 2*R0*, then V(p,w) = 1 for every w such 
that 2*Rw. So V(Lp,2*) = 1. Thus V(Lp D LLp,2*) = 0. 
The hard part is now to prove that every instance of H is valid in 
(^,V) in the sense of being true at every world in W. To do this we first 
show that all wff have a certain property. We use | a | to denote the 'truth 
set' of a: 
\a\ = {w € W: V(a,w) = 1} 
The truth set of a wff a is simply the set of worlds, in this model, at 
which a is true. Let us say that a subset A Q W is cofinite iff its 
complement W—A (i.e. {w G W: w £ A}) is finite. 
LEMMA 9.3 
For any wff a, |a| is finite or cofinite. 
162 


INCOMPLETENESS 
Proof: The proof is by induction on the construction of a. If a is a 
variable, then by definition | a\ = W —{0*}, since every variable is true 
everywhere except at 0*. So |or| is cofinite. Obviously if |a| is finite 
then | —of | is cofinite, and vice versa. \a V (3\ is |a| U \(3\. If both 
| a | and | @ | are finite then so is | or | U | jS |. If either one is cofinite 
then so is | a | U |/?|. 
For La, suppose first that V(a,n) = 0 for some n € N. Where w E 
N and w > n, or where w E N*, V(La,w) = 0, and so \La\ is finite. 
If V(a,n) = 1 for all n E N, then |a| is certainly not finite. So it must 
be cofinite, and since it is true throughout N, there must be a highest n* 
for which V(a,n*) = 0. But then V(La,w) = 1 for w = m* with m > 
n+1, and for all w E N. So |La| is cofinite. (Obviously if |a| = W 
then also |La| = W.) 
This proves lemma 9.3. To prove B all that remains is to prove the 
following theorem: 
THEOREM 9.4 
For every wff a, L(La = a) D La is valid in {&> V> 
Proof: First note that if V(a,w) = 1 for all w G W, then V(La, w) = 
1 for all w G W, and so (every instance of) H holds in this case. So 
suppose that V(a,w) = 0 for some w £ W. 
First suppose that V(a,n) = 0 for some n E N. (Possibly n = 0.) 
Without loss of generality we may suppose n to be the least number such 
that V(a,n) = 0. Then for all m < n, V(a,m) = 1 and so V(La,m) = 
1 for all m < n, and so H is true at all such worlds. Since V(a,n) = 0, 
and V(La,n) = 1 then V(La = a,n) = 0. So, where w E N and w > 
n, or where w E N*, V(L(La = a), w) = 0. So H is true at all these 
worlds also. So H is true at every world if V(a,n) = 0 for some n E N. 
Finally consider the possibility that V(a,n) = 1 for all n E N. Then 
| a | is not finite, and so by lemma 9.3, | a \ is cofinite. But also it is true 
throughout N, and so there must be a highest n* E N* for which 
V(a,n*) = 0. But then for all m > n+1, V(La,m*) = 1 and for all m 
E N, V(La,m) = 1. Thus H is true at all such worlds. But 
V(La,(n+l)*) = 0, while V(a,(n+1)*) = 1. So V(La = a,(n+l)*) = 
0, and so for all m < n+1, V(L(La = a),m*) = 0, and so H is true at 
all these worlds also. This proves the theorem and establishes the 
incompleteness of KH. 
Notice how when a fails at n E N, it is L(La D a) which fails, while 
when a fails at n* E N* it is L(a D La) which fails. The equivalential 
antecedent is thus crucial. 
163 


A NEW INTRODUCTION TO MODAL LOGIC 
It might be instructive to see what happens to the result in A when we 
look at j?~. In proving that Lp D LLp fails on & the wl, w2, vv3 of A are 
2*, 1*, and 0*. The worlds on an R-chain leading to 0* are precisely the 
worlds in N*, while the worlds not on such a chain are the worlds in N. 
But then, to get H to fail we would have to make/? true throughout N and 
false throughout N*, and so \p\ would be neither finite nor cofinite, and 
would not be the truth set of any wff in the particular model we have put 
upon SF. And of course we have shown that H is valid in this model. 
KHandKW 
There is an interesting connection between KH and KW, for it turns out 
that the system characterized by the class of all frames for KH is 
precisely KW. We establish this by showing that KH + 4 = KW. We 
first prove \-KH + 4 W. (4 is the wff Lp D LLp.) 
PC 
(1) 
(qD r)D ((q D p) D ((r A q) m (q A p))) 
(l)[Lp/q,LLp/r] (2) 
(Lp D LLp) D ((Lp D p) D 
((LLp A Lp) m (Lp A p))) 
4 (2) MP 
(3) 
(Lp D p) D ((LLp A Lp) = (Lp A p)) 
(3) L-dist,Eq 
(4) 
(Lp D p) D (L(Lp A p) = (Lp A p)) 
(4) DR1 
(5) 
L(Lp D p) D L(L(Lp A p) s (Lp A p)) 
H 
(6) L(Lp = p) D Lp 
(6) [Lp A pip] (1) 
L(L(Lp A p) » (Lp A p)) D L(Lp A p) 
(5)(7) Syll 
(8) 
L(Lp D p) D L(Lp A p) 
PC 
(9) 
(q A p)D p 
(9) [Lp/q] 
(10) (Lp A p) D p 
(10) DR1 
(11) L(Lp A p) D Lp 
(8)(11) Syll 
(12) L(Lp D p) D Lp 
Q.E.D. 
The proof that KW contains 4 is on p. 150. Here is a proof that |-KW H: 
PC 
(1) 
(q=p)D 
(qD p) 
(1) [Lp/q] 
(2) 
(Lp mp)D 
(Lp D p) 
(2) DR1 
(3) 
L(Lp = p) D L(Lp D p) 
W 
(4) 
L(Lp D p) D Lp 
(3)(4) Syll 
(5) 
L(Lp = p) D Lp 
Q.E.D. 
These two results establish that where ^ i s the class of frames for KH 
then a is ^valid iff 
[~KW a. For suppose 1-,^ a. Then 
|-KH+4 a, and 
164 


INCOMPLETENESS 
since every frame in % is a frame for KH + 4, (by (B) above) a is %-
valid. If H KW a then, from the completeness of KW established in the last 
chapter, a fails on a frame for KW. But since KW contains KH a frame 
for KW is also a frame for KH and so a is not ^valid. 
H is a formula of modal degree 2 (see p. 97). It is known2 that any 
system whose axioms are of degree 1 is complete, so in a sense this is a 
'best possible' incompleteness result. 
Completeness and the finite model property 
There is one class of systems for which completeness follows 
automatically, that is systems with the finite model property. As we 
defined the finite model property on p. 145 this is trivial, for we said that 
S has the finite model property iff for every wff a which is not a theorem 
of S there is a finite frame for S on which a is not valid, and this has the 
consequence that where % is the class of all finite frames for S then % 
characterizes S. 
But there is a less trivial result. To see why look at the difference 
between frames and models in the matter of completeness. Every system 
S has a canonical model, in which all and only S's theorems are valid. 
Thus S is characterized by the class consisting of just that model, or 
indeed by any class of models for S, i.e. models in which every S-
theorem is valid, which contains the canonical model. This holds even if 
S is not complete — even if S is not characterized by any class of frames. 
So one might expect that a system S could be characterized by a class of 
finite models without being characterized by a class of finite frames, or 
indeed without being characterized by any class of frames at all. 
This, however, is not so. Any system S which is characterized by a 
class of finite models is also characterized by a class of finite frames. The 
proof of this, due to Krister Segerberg,3 proceeds by showing that if a 
fails on a finite model which is a model for S, then that model can easily 
be converted into a model based on a finite frame for S. 
So suppose that V(a,w) = 0 for some w E W in some model 
(W,R,V) on which all theorems of S are valid. Our first step is to make 
sure that W contains no worlds w and w' which are 'duplicates' in the 
sense that for every wff a, V(a,w) = V(a,w').4 If w and w' are 
duplicates we simply leave one of them out, and if w has many duplicates 
we get rid of all but one. Let (W*,R*,V*) be the model obtained from 
(W,R,V) as follows. W* is obtained from W by dropping all but one 
member of any class of duplicates. For R*, given any w and w' E W*, 
we let wR*w' iff there is a duplicate w" of w' such that vvRvv". For V*, 
165 


A NEW INTRODUCTION TO MODAL LOGIC 
V*(p,w) = V(p,w) for every w G W*. An induction on the construction 
of a then establishes that V*(a,w) = V(a,w) for every w G W*. This 
means that if (W,R,V) is a model for S then so is (W*,R*,V*), and that 
if a wff a fails on (W,R, V) then it also fails on (W*,R*, V*) and so if a 
fails on a finite model of S it also fails on a (finite) model with no 
duplicates.5 
Consider a finite model for S with no duplicates. It is not hard to show 
that in such a model for every world w there is a wff fiw such that 
V*(jSw,w') = 1 iff w = w' — i.e. j8w is true at w and w alone. The reason 
is this. If W* contains no duplicates then for each w and each w' there is 
a wff yw, such that V*(7w,,w) = 1 and V*(7w,,w') = 0. So if (3W is the 
conjunction of all these 7s then (3W is true at w and w alone. This of 
course depends on the fact that W* is finite, since otherwise there could 
be infinitely many 7s, and we could not form their conjunction. 
We now show that not only is (W*,R*,V*) a model for S, but (W*,R*> 
is a frame for S. Suppose it is not. Then there is a model (W*,R*,V) 
based on (W*,R*) in which, for some w* E W* and some theorem a of 
S, V'(OJ,W*) = 0. Where p is any variable then there will be a finite 
collection of worlds, w,, ... , vvn such that V(p,w) = 1 if w is one of w,, 
... , wn, and 0 otherwise. Then, where /?_ is fiw V ... V (3W , V'(p,w) = 
" 
1 
n 
V*(/3p,H>) for every w G W*. What this means is that p has the same 
values in (W*,R*,V) as (3p does in the original (W*,R*,V*>. Now let 6 
be any sub-formula of a and let 6' be the result of uniformly replacing 
each variable p in 6 by (3p. A straightforward induction on the 
construction of wff establishes that V'(6,w) = V*(5',w) for every w G 
W*. In particular when b is a itself we have, given that V'(a,w*) = 0, 
V*(a',w*) = 0. But a' is a substitution-instance of a, and so, since |-s a 
then f-s a'. So (W*,R*,V*) would not after all be a model for S. 
A consequence of this is that any incomplete system, such as KH, lacks 
the finite model property, even if this is defined in terms of models rather 
than frames. But of course a complete system can lack it too, since Mk 
discussed on p. 154 is complete, and indeed characterized by frames 
satisfying a reasonably simple relational condition. 
General frames 
In proving that Lp D LLp is not a theorem of KH we made essential use 
of a model in which | a | is either finite or cofinite. There is, however, 
another way in which we could look at what is going on. Instead of 
thinking of ourselves as starting from a frame as a structure consisting 
166 


INCOMPLETENESS 
only of a set W and a relation R, we could think of ourselves as starting 
from a structure consisting of these together with a set P of 'allowable' 
sets of members of W; and we could then think of a model as being 
derived from such a structure by adding to it any value-assignment to the 
variables which satisfies the condition that, for every variable p, \p\ is 
one of the sets in P. Such a structure (W,R,P), though not a frame in the 
sense in which we have been using the term 'frame', would be better 
described as a frame than as a model, since it would contain no value-
assignment and therefore would not determine the values of wff in various 
worlds. In order to ensure that (W,R,P) could yield the sort of proof we 
gave in lemma 9.3 however, we should have to require that P should be 
so selected that once we were given that \p\ G P for every variable/?, 
we could be sure that \a\ € P for every wff a. To achieve this, we have 
to require that P should be so chosen that whenever any set of worlds, A, 
is in P, then so is A's complement (for the sake of the induction on ~ ) , 
that whenever A and B are both in P, then so is their union (for the sake 
of the induction on V), and that whenever A is in P, so is the set of all 
worlds that can see only members of A (for the sake of the induction on 
L). A structure (W,R,P) in which P satisfies these conditions is called a 
general frame by van Benthem.6 
The formal definition is this: (W,R,P) is a general frame iff 
(a) 
W is a non-empty set; 
(b) 
R is a dyadic relation defined over W; 
(c) 
P is a set of sets of members of W (i.e. P Q (PW) satisfying the 
following conditions: 
(i) If A G P, thenW-A G P, 
(ii) If A G P and B G P, then A U B G P, and 
(iii) If A G P, then {w G W :Vw' G W(wRw' D w' G A)} G 
P. 
A model based on a general frame (W,R,P) will then be any structure 
(W,R,P,V), where V is a value-assignment to the variables which makes 
I/?| G P for every variable/?. The standard rules [V~], [V V] and [VL] 
are assumed to hold. (In lemma 9.3, P would of course be the set of all 
finite or cofinite subsets of W.) We shall then say, by a natural extension 
of our earlier definitions, that a wff is valid on a given general frame iff 
it is valid in (true in every world in) every model based on that general 
frame; that a general frame is a general frame for a system S iff every 
theorem of S is valid on that general frame; and that S is characterized by 
167 


A NEW INTRODUCTION TO MODAL LOGIC 
a class ^of general frames iff, for every wff a, a is a theorem of S iff 
a is valid on every (general) frame in &. 
Now suppose we consider the frame (W,R) of the canonical model for 
any normal modal system S, and suppose we define the set P of allowable 
sets of worlds by saying that A is an allowable set iff there is some wff 
a which is true in that canonical model in every world in A but in no 
other world. (I.e. P = {A Q W:3a(A = |a|)}.) Then it is not hard to 
show that (W,R,P), as so defined, is a general frame which characterizes 
S. And this has the consequence that every normal modal system is 
characterized by the class of all the general frames for that system. Thus 
if we were to suggest, as a third possible account of the completeness of 
a system in some absolute sense, that a system should be said to be 
complete iff it is characterized by some class of general frames, then this 
would have the consequence that every normal modal system is complete. 
General frames are like models in that each normal modal system is 
characterized by some class of them, and indeed each is characterized by 
a single frame. But general frames are unlike models in that if any wff is 
valid on a general frame, so are all its substitution-instances. Ordinary 
frames (which are sometimes called Kripke frames in contexts in which 
it is important to distinguish them from general frames) of course also 
have this property; but many models do not, as we observed on p. 112. 
It is this last-mentioned fact which suggests that an intuitively satisfactory 
account of validity for a modal system should be in terms of frames, of 
one kind or another, rather than in terms of models. Of the two kinds of 
frames we have discussed, Kripke frames, unlike general frames, lead to 
an account of completeness which yields a real distinction between 
systems which are complete and ones which are not; but general frames 
sometimes enable us to construct independence proofs where neither 
Kripke frames nor models would be of service. 
What might we understand by incompleteness? 
The incomplete system KH which we have discussed in this chapter is 
certainly one which has a very simple axiomatic basis, but it is difficult 
to get an intuitive grasp of just how it is incomplete — that is, of how it 
can be that the system cannot precisely match any condition on a frame 
and yet can match such a condition if it is combined with a restriction on 
the permitted value-assignments. (This, indeed, seems also to be true of 
the other incomplete systems that have been described in the literature.) 
We may, however, be helped in this matter by comparing KH with an 
incomplete system of tense logic which has been produced by S.K. 
168 


INCOMPLETENESS 
Thomason.7 Tense logic will be discussed briefly on p. 218, though it lies 
outside the scope of this book since it contains two 'necessity' operators, 
one for the past and one for the future; nevertheless it seems worthwhile 
to mention Thomason's system here, since it seems possible to get an 
intuitive 'feel' for the source of its incompleteness. One of the 
consequences of Thomason's axioms, given the interpretation he intends 
them to have, is that time never comes to an end. Another of their 
consequences is that every proposition eventually takes on an unvarying 
truth-value (though, since time is never-ending, there need be no specific 
moment after which all propositions have unvarying truth-values). 
Thomason is able to prove that there are no Kripke frames at all for his 
system and hence, of course, it is not characterized by any class of 
frames; and we may well feel, intuitively, that this is not a surprising 
result, for this reason: if we give the elements in a frame a temporal 
interpretation (e.g. by taking the 'worlds' as moments of time and R as 
the relation is earlier than), then a frame, or a class of frames, can be 
thought of as expressing a possible structure for time; but it is very hard 
to see how the mere structure of (non-ending) time could by itself be 
sufficient to ensure that every proposition will eventually have a constant 
truth-value. It is, however, not difficult in principle to conceive that the 
structure of time together with some restriction on permitted value-
assignments might have just such an effect. The analogy with the 
semantics for KH is this: our definition of the class of allowable sets of 
worlds has the effect of ensuring that, for any wff α, either α itself or 
~ α will be true at only a finite number of worlds; and this means that for 
every wff a, except for a finite, possibly empty, portion at each end of 
the frame, α has an unvarying truth-value. It again seems intuitively 
reasonable (as it did with Thomason's system) to expect that a system 
characterized by such a class of models would not be determined solely 
by a condition on a Kripke frame, but only by this in conjunction with a 
restriction on value-assignments. 
Exercises — 9 
9.1 Prove theorem 9.1. 
9.2 Let VB be K + VB, MLp V L(L(Lq D q) D q). Show (A) that 
every frame for VB is also a frame for MV, MLp V Lp, but (B) that 
MV is not a theorem of VB. Explain why this shows the incompleteness 
of VB. 
169 


A NEW INTRODUCTION TO MODAL LOGIC 
9.3 
Prove that K together with the following axioms is not complete: 
(i) LMq D L(Lp D p) 
(ii) L(L(Lp Dp)D 
Lp) 
9.4 Let MV be K + MV: 
(a) Prove that VB is a theorem of the system MV. 
(b) Prove that MV is precisely the system characterized by the class of 
all frames for VB. 
9.5 
Prove that if there is a p-morphism (see note 5) from (W,R) to 
(W*,R*> then if a is valid on (W,R), a is valid on (W*,R*). 
9.6 
Set out fully the proof that every normal modal system is 
characterized by a class of general frames. 
Notes 
1 The incompleteness of this system is proved in Boolos and Sambin 1985. The 
proof given in the text is essentially the simplification of the proof they give 
which appears in Cresswell 1987. The earliest incomplete logics appeared in Fine 
1974b and S.K. Thomason 1974a. Other examples occur in van Benthem 1978, 
1979b and Boolos 1980. Ming Xu, 1991, has shown that, for each n, the system 
KHn, which is K + L"(L(Lp = p) D Lp) is a distinct system, with KHn included 
in KHm for n > m, but that, for each of them, the class of frames is just the class 
of frames for KW. Analogous results are obtained for other systems. Blok 1980 
shows by algebraic means that either there are none or non-denumerably many 
incomplete systems whose frames are just those of any given complete system. 
Fine (op. cit., p. 28) notes that a method which he uses in Fine 1974c will 
produce non-denumerably many incomplete extensions of S4. The incompleteness 
of one of the systems discussed in van Benthem 1979b is proved in Chapter 4 of 
Hughes and Cresswell 1984. 
2 Lewis 1974. 
3 Segerberg 1971, p. 33. 
4 Segerberg 1971 p. 29 calls models with no duplicates 'distinguishable' models. 
5 This way of making a new model from an old one in such a way that it may be 
guaranteed to satisfy exactly the same formulae is an example of what Segerberg 
1968a, p. 13f., calls a pseudo-epimorphism, or for short a p-morphism. Briefly 
a p-morphism from a frame (W,R) to a frame (W*,R*) is a function/ from W 
onto W* such that for w, w' E W, if wRw' then^(vv)R*y(w'), and for w, v E 
W*, if wR*v, then for every w E W such that J{w) — u there is some w' E W 
such that wRw' andy(w') = v. Provided that for every variable p and every w E 
W, V(p,w) = V*(pJ{w)) then for every wff a, V(a,w) = V*(/(w)). In the present 
example of course^w) is simply the representative of all the duplicates of w. 
170 


INCOMPLETENESS 
6 Van Benthem 1978. (The term 'general', as used here, is derived from its much 
earlier use in Henkin 1950 in connection with an analogous situation in higher-
order predicate logic.) Makinson 1970 calls such structures relational frames, and 
S.K. Thomason 1972a, p. 151, calls them first-order structures. Thomason (op. 
cit., p. 154) then imposes two extra conditions on such structures to obtain what 
he calls refined structures. These conditions are (a) that if w ^ w', then there is 
an allowable set A such that w E A but w' fc A; and (b) that if not wRw', then 
there is an allowable set A such that w E A but w' fc A. Goldblatt 1976, Part 
1, p. 64, imposes still further conditions to obtain what he calls descriptive 
frames. (Descriptive frames link with canonical models.) 
7 S.K. Thomason 1972a, pp. 153f. 
171 


10 
FRAMES AND SYSTEMS 
Frames for T, S4, B and S5 
By a frame for a normal modal system S we mean a frame on which 
every theorem of S is valid (i.e. true in every world in every model based 
on it). We showed, on pp. 39-41, that validity on a frame is preserved 
by the rules US, MP and N. This means that a frame is a frame for S iff 
each axiom of S is valid on that frame; and in fact we need only consider 
the modal axioms other than K, since K is valid on every frame 
whatsoever. 
In our soundness and completeness proofs in Chapters 2 and 6 we were 
able to show that the system T and the class of reflexive frames match 
each other in the sense that any wff is a theorem of T iff it is valid in 
every reflexive frame. That is certainly one connection between T and the 
class of all reflexive frames. The question we now want to ask, however, 
is whether the class of all frames for T is the same as the class of all 
reflexive frames. The answer is that in fact it is. We have, indeed, proved 
one half of this already. For in proving the soundness of T we showed 
that every theorem of T is valid on every reflexive frame; and that is just 
another way of saying that every reflexive frame is a frame for T. But we 
have not yet proved the other half, namely that every frame for T is 
reflexive. It is, however, quite easy to do so. 
THEOREM 10.1 Every frame for T is reflexive. 
Proof: The proof is by contraposition; i.e. we shall show that if any 
frame & is not reflexive, then some theorem of T - in fact Lp D p - is 
not valid on &. Suppose then that & is not reflexive. This means that 
172 


FRAMES AND SYSTEMS 
some w G Wis not related to itself. Let w* be such a world. Then let 
( ^ V ) be a model based on «^"m which V(p,w*) = 0 but V(p,w) = 1 for 
every w G W except w*. Since w* is not related to itself, this will make 
p true in every world to which w* is related. Thus V(Lpyw*) = 1. But 
V(p,w*) = 0. Hence V(Lp D /?,w*) = 0. So Lp Dp is not valid in this 
model, and therefore is not valid on &. 
This completes the proof of theorem 10.1. It and the soundness of T 
then give us 
COROLLARY 10.2 ^"is a frame for T iff ^"is reflexive. 
It is important to note that theorem 10.1 holds only for frames, not for 
models. That is, it is not the case that every model for T is reflexive, 
even though every reflexive model is a model for T. To see this, consider 
a frame (W,R) in which W = {w1,w2} and R = {(w,,w>2 ),(w2,w1)} - i.e. 
a two-world frame in which neither world can see itself but each can see 
the other. We could picture the frame in this way: 
o 
^ " ^ 
o 
w, 
w2 
Now consider any model based on this frame in which each variable has 
the same value in both worlds, i.e. any model in which V(p,wx) = 
V(p,w2) for each variable p. It is not hard to prove, by induction on the 
construction of a wff, that for every wff a, V(a,w,) = V(a,w2). We now 
show that for any wff a, V(La D a,w,) = 1. For suppose that 
WiLa^) 
= 1. Then since w,Rw2 we have V(a,w2) = 1; and hence, since a has the 
same value at both worlds, V^w,) = 1. Clearly an exactly similar 
argument will show that V(La D a,w2) = 1. This means that every 
substitution-instance of T is valid in the model in question, and therefore, 
by theorem 9.1 on p. 160, that it is a model for T. But clearly it is not 
a reflexive model. 
Theorem 10.1 and corollary 10.2 should be compared with theorem 6.7 
on p. 120. That theorem, in conjunction with the soundness of T, 
establishes that T is characterized by the class of all reflexive frames. But 
this by itself does not give us corollary 10.2. For, as we saw in Chapter 
8, T is characterized by the class ^of all finite reflexive frames, and also 
by another class £** which contains just the frame of T's canonical 
173 


A NEW INTRODUCTION TO MODAL LOGIC 
frames still leaves open the possibility that it might also be characterized 
by some class of frames which contains, or even consists solely of, 
non-reflexive ones. And it is this which corollary 10.2 assures us cannot 
be so. For the proof of theorem 10.1 shows that Lp D p fails on every 
non-reflexive frame, and therefore that no such frame can be a member 
of any class which characterizes T. In other words, every class of frames 
which characterizes T must consist solely of reflexive frames. 
Theorem 10.1, therefore, establishes something that theorem 6.7 does 
not. Does this mean that it is stronger than theorem 6.7, that it proves all 
that that theorem proves and more besides? If it did, that would indeed be 
gratifying, since the proof of theorem 10.1 is a great deal simpler than a 
completeness proof by canonical models. Unfortunately, however, there 
is no short cut to a completeness proof by this method. Certainly, if T is 
characterized by any class of frames at all, then it will be characterized 
by the class of all frames for T, and then corollary 10.2 assures us that 
in that case it is characterized by the class of all reflexive frames. But the 
hypothesis here is that T is characterized by some class of frames; and 
that is something that corollary 10.2 does not tell us, and which we need 
a separate proof to establish. 
To make the position clearer, consider again the incomplete system 
KH. What we proved in Chapter 9 is that the system characterized by the 
class of all frames for KH is stronger than KH itself, because it contains 
the wff 4, which is not a theorem of KH. We also proved that a frame is 
a frame for KH (a frame on which every theorem of KH is valid) iff it is 
a frame for KW - which gives us an analogue of corollary 10.2 for KH. 
But it is not true that KH is characterized by the class of all such frames, 
since this class validates the non-theorem 4. 
What all this means is that the fact that the frames for a certain system 
are precisely the frames which have a certain property, is neither a 
necessary nor a sufficient condition of that system's being characterized 
by the class of all frames which have that property. The case of KH 
shows that it is not a sufficient condition; and the fact that T is 
characterized by the class of all finite reflexive frames but that not all 
frames for T are finite shows that it is not a necessary condition either. 
The most that we can say is that if a. system S is complete, in the sense 
of being characterized by some class of frames, and if the frames for S 
are precisely those that possess a certain property, then the class of all 
frames with that property is one of the classes of frames (and in fact the 
largest of them) which characterize S. 
We have gone through the situation in some detail for T. For S4, B 
174 


FRAMES AND SYSTEMS 
and S5 we shall merely survey the analogous results. These are that the 
frames for S4 are precisely those that are reflexive and transitive, that the 
frames for B are precisely those that are reflexive and symmetrical, and 
that the frames for S5 are precisely those that are reflexive, transitive and 
symmetrical. S4, of course, is T + 4 (Lp D LLp); B is T + B 
(~p D L~Lp); and S5, although in Chapter 2 we axiomatized it as T + 
E, can equally well be axiomatized as T + 4 + B. So, since we have 
already proved the soundness of these systems, all that we still have to do 
is to prove that every frame on which 4 is valid is transitive, and that 
every frame on which B is valid is symmetrical. 
THEOREM 10.3 Every frame on which Lp D LLp is valid is transitive. 
Proof: Let & be any non-transitive frame. This means that there are 
worlds w„ w2 and vv3 in W such that w,Rw2 and w2Rw3 but not WjRw3. Let 
(^~,V) be a model based on «^in which V(p,w3) = 0 but V(p,n>) = 1 for 
every w E W other than w3. Then clearly V(L/?,w,) = 1. However, 
V(L/?,w2) = 0 and hence V(LLp,w,) = 0. So V(Lp D LLp,wx) = 0, 
which means that Lp D LLp is not valid on &. 
THEOREM 10.4 Every frame on which ~p 
D L~Lp 
is valid is 
symmetrical. 
Proof: Let ^ b e any non-symmetrical frame. This means that there are 
worlds w{ and w2 in W such that w,Rw2 but not w2Rw{. Let (^~,V) be a 
model based on ^ i n which V(p,w,) = 0 but V(p,w) = 1 for every w G 
W other than w,. Then (a) V(~p>w{) = 1. But since w2 is not related to 
wl9 p is true in every world to which w2 is related. So we have V(Lp,w2) 
= 1, and therefore V^Lp^w^ 
= 0. Hence, since WjRw^ we have 
(b) V(L~Lp,wx) 
= 0. (a) and (b) then give us the result that 
V(~p D L~Lpywx) 
= 0, and so ~p D L~Lp is not valid on &*. 
We can prove analogous results for many other formulae and systems 
than the ones we have just dealt with. For example, we can prove that 
every frame on which Dl (see p. 128) is valid is connected. The proof is 
that if any frame contains worlds wlf w2 and w3 such that w1Rw2 and 
WJRH^ but neither w2Rw3 nor W3RH>2, then a model based on that frame 
which makes p false at vv3 but true everywhere else, and q false at vv2 but 
true everywhere else, will make Dl false at w,. Likewise with the finality 
condition for S4M. For suppose that in a transitive and reflexive frame 
175 


A NEW INTRODUCTION TO MODAL LOGIC 
there is a world w which cannot see an endpoint. Then, firstly, w must 
be able to see a world distinct from itself, and, secondly, no world that 
w can see can see an endpoint either. Thus there must be a chain 
(possibly a finite but repeating chain) of at least two distinct worlds where 
each can see all later members. By having p alternately true and false 
(though not necessarily consecutively) on this chain we may falsify M. So 
every frame for S4M is final. 
Irreflexiveness 
We have seen that not only is T characterized by reflexive frames, but 
that all frames for T are reflexive. But we also saw, on p. 173, that there 
are irreflexive models for T. The procedure we used for constructing the 
irreflexive model on p. 173 can in fact be generalized.1 For if we take 
any reflexive world in any model, i.e., any world which can see itself, 
and replace it by a pair of worlds each able to see the other but neither 
able to see itself, and we give each variable the same value in each world 
in the new pair as it had in the original world, then the new (irreflexive) 
model will validate exactly the same wff as the original. If we apply this 
procedure to the canonical model of K we can therefore falsify any non-
theorem of K in a model based on an irreflexive frame, and thereby show 
that the system characterized by irreflexive frames is simply K itself. 
There is another way of looking at the connection between a system 
and the class of all its frames. In the case of T what we have in fact 
proved is that any frame ^validates the wff T iff ^ i s reflexive. Put this 
way the connection is not so much a connection with the system T as with 
the wff T. This connection can be described by saying that the modal wff 
T corresponds with reflexiveness. The result described above concerning 
irreflexiveness shows that irreflexiveness does not correspond with any 
modal wff. For suppose there were a modal wff a such that a frame &" 
validates a iff & is irreflexive. Then a must be a theorem of K, for 
otherwise the class of all irreflexive frames would characterize K + a 
where this would be different from K, and we showed above that the class 
of irreflexive frames characterizes K. But if a is a theorem of K then 
every frame validates a, not just irreflexive frames. 
Although irreflexiveness does not correspond to a modal formula 
Gabbay2 has shown that it does, in a sense, correspond to a rule. We note 
first that any irreflexive frame preserves the rule 
Gabb 
\- a, D L(a2 D ... L(an D {Lp D /?))...) -* 
\- 
a, D L(a2 D ... L~a n) 
176 


FRAMES AND SYSTEMS 
where p does not occur in any of a,, ... , aa. This may be proved as 
follows. Suppose that ^ i s an irreflexive frame and that a, D L(ct2 D ... 
L — a J fails on &. Then there is a model ( ^ V ) based on ^ s u c h that 
V(a, D L{a2 D ... L~a„),w,) 
= 0 for some Wj G W. If so there is a 
chain w,, ... , vvn in which V(ak,wk) = 1 for 1 < k < n. Let (^,V*) be 
a model based on the same ^ 
in which V* is just like V except that 
V^jVvJ = 0, and V*(p,w) = 1 unless w = wn. Since/? does not occur 
in a,, ... , an we have V*(akiwJ = V ^ w J = 1. But since & is 
irreflexive then not wnRwn and so V*(Lp D p.w^ = 0. So V*(aj D L(a2 
D ... L(an D (L/? D p))...),Wi) = 0, and so ax D L(a2 D ... L(an D 
(Lp D /?))...) fails on &. 
Gabbay proves a lemma3 from which it follows that if a normal modal 
system S contains the rule Gabb then for any a such that -| s a, there is 
a sub-model of the canonical model of S in which R is irreflexive and a 
is false, and in that sense the rule Gabb may be said to correspond with 
irreflexiveness. There are however some differences between the way in 
which Gabb corresponds to a condition on frames and the way in which 
a modal formula does. If a condition corresponds to a wff a then that 
condition defines the class of all frames for K + a. But although 
irreflexiveness corresponds with the rule Gabb there is no system that 
Gabb determines. For Gabb is a rule of K (though not of any extensions 
of T) because K is characterized by irreflexive frames; yet K certainly has 
frames which are not irreflexive, since all frames are K frames, even 
reflexive ones. Further, Gabb is preserved by at least some frames which 
are not irreflexive. For consider the irreflexive frame obtained from the 
canonical model of K by 'duplicating' every reflexive world in K's 
canonical model and giving every variable the same value in each 
duplicate. Since this model is irreflexive it certainly validates Gabb, but 
also validates only theorems of K. Now add to this model a reflexive 
world that can see at least one world in the irreflexive model. The new 
model, and therefore the new frame, also validates only K theorems and 
so, since Gabb is a rule of K, validity on the new frame is preserved by 
Gabb. But the new frame contains a reflexive world. 
Compactness 
In this section we shall look at our old friend KW again as a propositional 
modal logic which turns out to have a number of interesting features. 
The first is that, in a certain sense of that word, KW is not compact.4 
To see what is meant here look at what the canonical model does. 
Suppose that -| s a. What this means is that { — a} is S-consistent. Let ^ * 
177 


A NEW INTRODUCTION TO MODAL LOGIC 
= (W,R), where (W,R,V) is the canonical model of S. Then for some w 
G W, V(~ a,w) = 1. But the canonical model theorem can be used to 
produce a stronger result. For it shows not just that any single S-
consistent formula is S-satisfiable (in the sense of being true at some 
world in a model for S) but more generally that if A is any S-consistent 
set of wff then A is simultaneously S-satisfiable, in the sense that there is 
some w G W such that for every a € A, V(a,w) = 1. So if ^ * is a 
frame for S we have the result that any S-consistent set of wff is 
simultaneously satisfiable in a frame for S.5 We call S compact iff every 
S-consistent set of wff is satisfiable in a frame for S. 
Using a set A suggested to the authors by Kit Fine it can be shown that 
KW is not compact. We will first establish certain facts about frames for 
KW. 
LEMMA 10.5 
If & is a frame for KW then ^ i s (a) irreflexive and (b) 
transitive. 
Proof, (a) was proved on p. 140. (b) If ^ i s not transitive there are some 
Wi, H>2, w3 G W with WjRu^, w2Rw3, but not w,Rw3. Let V(p,w) = 0 iff 
w = w2 or w = w3. Then, since w,Rw2, V(Lp,w,) = 0. Now consider 
every w such that w,Rw. w cannot be w3 since not w,Rw3. If w = w2 then 
since w2Rw3 and V(p,w3) = 0, V(L/?,w2) = 0, and so V(Lp D /?,w2) = 
1. If w is any other world w{ can see we have V(p,w) = 1 and so V(Lp 
D pyw) = 1. So V(L(Lp Dp)ywx) = 1. So W fails in a non-transitive 
frame. 
For the next theorem we define a chain, in a frame (W,R) to be a 
sequence wl9 ... ,wiy ... such that WiRwi+1. By an infinite chain we mean 
a chain in which every term has a successor. 
THEOREM 10.6 No frame for KW contains an infinite chain. 
Proof: Suppose there is an infinite chain C in &. Call its terms w,, w2, 
... etc. Define V so that V(p,w) = 1 iff w i C. Now consider any w{ G 
C. Since C is infinite there is some wi+1 G C and, by definition V(/?,wi+1) 
= 0. So V(L/?,Wi) = 0. Now consider any w that w; can see. If w G C 
we have \{Lp,w) 
= 0 and so V(Lp D p,w) = 1. If w £ C we have 
V(p,w) = 1 and so here too \(Lp D p,w) = 1. So V(L(Lp D p),w) = 
1. Thus W fails at w{. 
Notice that it is crucial that C be infinite. For if C has a last term then 
178 


FRAMES AND SYSTEMS 
it must be some wn for which there is no w such that wnRw. In other 
words wn must be a dead end. Dead ends are characterized by the fact 
that La. is true for every a, even L1 is true. So by making p false at wn 
we have Lp D p false there, and so L(Lp D p) is false further up the 
chain. 
Now consider the following set A of wff, where the propositional 
variables are/?0, /?,, ... etc. 
A = {Mp0} U {Lip, D MA+1)} (1 ^ 0) 
To show that A is KW-consistent it will be sufficient to show that any 
finite subset of it is consistent and to do that it will suffice to show that 
every finite subset of A is satisfiable on a frame for KW. (Note that this 
can be used to give a purely model-theoretic version of non-compactness 
that there is a set of wff each finite subset of which is simultaneously 
satisfiable on a frame for the logic, but which is not itself so satisfiable.) 
Every finite subset of A will also be a subset of some 
An = {Mp0, L(p0 D Mpi), ... , L(pn D Mpn+l)} 
Let ^n = ({0, ... , n + 2}, <). It is easy to check that W is valid on ^ n. 
Now consider the following model (^,V). For i < n + 2 let V(p;,i +1) = 
1, and for all w T* i + 1, V(p;,w) = 0. (For i > n + 2, V(pi,w) can be 
defined arbitrarily.) So V(Mp0, 0) = 1. Further V(p- D Mpi+l, i + 1) = 
1, and so, since W(piyw) = 0 for all w ^ i+1, V(pt D Mpl+l,w) = 1 for 
all w < n + 2. So V(L(p; D Mpl+l), 0) = 1 and so A„ is simultaneously 
satisfiable on ^n. 
But for A as a whole to be satisfiable on an irreflexive and transitive 
frame the frame would need to have an infinite chain. For suppose all 
members of A are true at some vv0. Then p0 must be true at some w, and 
supposing some px is true at wi+1 then Mp1+l must be too, which means 
that/?i+1 must be true at some wi+2. Since R is transitive and irreflexive, 
and since there is no limit on i, this can only be so if the frame has an 
infinite chain. But in that case theorem 10.6 assures us that it is not a 
frame for KW. 
S4.3.1 
In Chapter 7 we spoke of temporal interpretations of modal logic, and in 
particular of Prior's desire to think of L as meaning 'it is and always will 
179 


A NEW INTRODUCTION TO MODAL LOGIC 
be the case that'. We noted that when R is interpreted so that wRw' iff w 
is no later than w', the class of frames required is those which are 
transitive and connected. But the problem is further complicated by the 
fact that the criterion of validity can be taken in two ways, depending on 
whether time is regarded as discrete or continuous. To regard time as 
discrete is to think of it in such a way that given one moment we can 
speak of the next moment, the next again, and so forth. To regard time 
as continuous is to suppose that between any two moments there is a 
third, and then it will make no sense to speak of the next moment after 
a given one. This distinction is important since it turns out that there are 
formulae which are not valid when time is taken to be continuous but 
which are valid when time is taken to be discrete. The stronger system is 
one Prior called D,6 but that name has already been used for a quite 
different system, and the less confusing name of the system we require 
is S4.3.1. S4.3.1 is obtained by adding to S4.3 the following extra axiom: 
Nl 
L(L(p D Lp) D p) D (MLp D p) 
A frame (W,R) for discrete time can be considered to be a frame in 
which W is the natural numbers, or some finite subset of them, with R 
as < . This gives us a definition of validity for the system S4.3.1. We 
shall not give a completeness proof for S4.3.1. It is quite complicated.7 
The reason is that the canonical model method cannot be used because 
S4.3.1 is not compact, and it is this latter fact that we shall now prove. 
The proof is similar to that given for KW except that in place of A we 
use another set ty* To define V we let a; be p{ D M{~p0 A ... A 
~P\ A P\+\)- Then ^ is 
(¥) {MLp0, ~p0t M(~p0 A />,)} U {La, : i > 1} 
Our proof will have the same structure as that for KW; i.e. we shall show 
that (1) any finite subset of ^ is simultaneously satisfiable on a frame for 
S4.3.1 but that (2) ^ as a whole is not. 
For (1) we merely observe that where Lan is the highest of the La{s in 
a particular finite subset of ^ then the S4.3.1 frame (W,R), where W = 
{1, ... , n + 2} and R = <, will satisfy ^ when/?0 is true at n + 2 only 
and each p, (1 < i < n + 1) is true just at i. 
Since S4.3.1 contains both T and 4 we know that any frame for S4.3.1 
will be both reflexive and transitive. So to prove (2) suppose that ^ is 
true at some world vv0 in a model (W,R,V) based on a reflexive and 
180 


FRAMES AND SYSTEMS 
transitive frame. Since MLp0 is true at w0, w0 must see some world w* at 
which Lp0 is true, and since ~/?0 is true at w0, w* cannot see vv0. Since 
M(~p0 
A /?i) is true at w0, vv0 must be able to see some world w, at 
whichpQ is false but px is true. But given a chain of worlds wlt ... , vvn 
such that WJRWJ for 0 < i < j < n, and that each px (1 < i < n) is true 
at H>i, the truth of Lan at w0 requires that an is true at wn, and therefore 
that wn can see a world wn+1 at whichpQ+l is true and each of/?,, ... , pa 
is false. Since each wu ... , wn has at least one of these true wn+1 must 
be distinct from each of H>, , ... , wn; and so there must be an infinite 
chain of worlds beginning with vv0 throughout which pQ is false. Since Lp0 
is true at w* this means that u>* cannot see any world in this infinite 
chain. (Think of w* as coming after all the worlds in the infinite chain.) 
Now consider a (possibly different) model based on this same frame at 
which p is false at w0, alternately true and false through the chain and true 
everywhere else in the frame. Then 
(i) p is false at vv0. 
(ii) Since w* cannot see any world in the chain (including vv0) then 
Lp is true at w* and so MLp is true at vv0. 
(iii) If w is any world in the model and p is true at w then so is L(p 
D Lp) Dp. If p is false at w then w must be in the chain and there must 
be a world w' that w can see at which p is true, but which can in turn see 
a world at which/? is false. This means that/? D Lp is false at w' and so 
Lip D Lp) is false at w and so Lip D Lp) D p is true at w. So L{Lip D 
Lp) D p) is true at w0 and so Nl is false at w0, and so fails on this frame. 
So no reflexive and transitive frame which satisfies ^ is a frame for 
S4.3.1. So no frame for S4.3.1 satisfies ^. This establishes the non-
compactness of S4.3.1. 
First-order definability 
Consider again the class of frames for the system T. That class is the 
class of all reflexive frames, by which is meant the class of frames (W,R) 
which validate the condition that for every w G W, wRw. Using the 
notation of the lower predicate calculus (LPC) to be introduced in Part III 
we can express reflexiveness in terms of a wff of LPC, the wff VxxRx. 
In this wff the italicized R is a two-place predicate whose interpretation 
is the relation R of (W,R). In Chapter 7 we spoke of the possibility of 
describing classes of frames by wff of the lower predicate calculus (first-
order logic) and our next task is to pursue this theme a little further. This 
section is designed for those who already know a little about first-order 
181 


A NEW INTRODUCTION TO MODAL LOGIC 
logic. Others may like to consult what we say about the lower predicate 
calculus in Chapter 13. The class of frames for T may be said to be first-
order definable in the sense that it is the class of those and only those 
structures which satisfy VxxRx. Frames for T are definable by a single 
closed wff of LPC, but we can allow an infinite set of such wff, and 
allow identity as a logical predicate.9 
We shall first mention some general characterization theorems. These 
are theorems which show how to take any modal wff of a certain general 
kind and 'translate' it into a wff of LPC in such a way that the system 
formed by adding any number of such modal wff to K will be 
characterized by precisely those frames which satisfy all the conditions 
expressed by the corresponding wff of LPC. The first characterization 
theorem is due to Lemmon and Scott.,0 It covers all wff of the form 
G' 
WUp D VAfy 
where m, n, j and k are natural numbers including 0. Thus for instance 
T is the case where n = 1 and m = j = k = 0. 4 where m = 0, n = 1, 
j = 2 and k = 0, D where n = k = 1 and m = j = 0 , and so on. The 
condition corresponding to G' is 
C: 
VxVyVzdxITy A x&z) D 3v(yiTv A zRkv)) 
What C means is that if we have four worlds w,, w>2, w3 and w4 (not 
necessarily distinct) and w2 is m steps from w,, and w3 is j steps, then 
there is a w>4 which is n steps from w2 and k steps from vv3. The proof of 
this result is a generalization of the completeness proof for S4.2 on pp. 
134-135. 
The other theorem to which we shall refer generalizes a conjecture 
made by Lemmon and Scott, and has been proved by Sahlqvist.11 The 
formulae covered by it are all those of the form 
Sahl 
Ln(a D 0) 
where n > 0 and a and (3 are any wff which satisfy the following 
conditions: a is a wff in which (i) no operators occur except L, M, V , 
A and ~ , (ii) ~ occurs only immediately before a variable, and (iii) no 
occurrence of M, V or A lies within the scope of any L. 0 is a wff in 
which no operators occur except L, M, V and A (~ is not permitted). 
Although Sahl covers all systems covered by G' there are instances of 
182 


FRAMES AND SYSTEMS 
Sahl which cannot be expressed by any instances of G'. Thus Ver can be 
axiomatized as K + q D Lp, and S4.3 as S4 + M(Lp A q) D L(Mq V 
p). The condition R which corresponds to Sahl is quite complicated, and 
we shall not state it here, but simply refer the interested reader to 
Sahlqvist's paper. Our reason for referring to these results is simply to 
make the point that the problem of characterizing systems by means of a 
condition on R which is expressible in LPC has been definitively solved 
for an extremely wide range of systems. Nevertheless, there are systems 
which cannot be so characterized. The simplest is the system obtained by 
adding the wff M discussed on p. 131 not to S4 but directly to K. K + 
M gives a system for which no condition on R describes a class of frames 
which characterizes it. We shall not here prove that K + M cannot be 
characterized by a first-order condition,12 but we shall prove that any 
system which can be so characterized is compact. From this will follow 
immediately that non-compact systems like KW and S4.3.1 cannot be 
characterized by any collection of wff of LPC. 
To prove this theorem we first note that, given a frame (W,R), the 
intended interpretation of R is the relation R of (W,R). A first-order 
description of frames involves a language X whose only predicates are R 
and =. We shall say that a model (D*,V*) for £ (see p. 238) 
corresponds with a frame (W,R) iff D* = W and V*(R) = R. (D*,V*) 
is completely determined by (W,R) and so nothing is lost if we speak as 
though it is (W,R) which is the LPC interpretation. To describe a model 
we add, as one-place predicates, the symbols which also constitute the 
propositional variables of modal logic. We call the augmented first-order 
language i£+, and use it to show that any modal system which can be 
characterized by a class of frames defined by a collection of sentences of 
i£ must be compact. From this and the non-compactness of KW, it 
follows that KW cannot be characterized by any first-order definable class 
of frames. 
In order to prove that first-order characterization implies compactness 
we first show how to translate any wff a of modal logic into a wff r(a) 
of ££+ containing one free variable x. 
Tip) = px 
r(~a) = ~r(a) 
r(a V /J) = (r(a) V r(0)) 
r(La) = Vy(xRy D r{a[ylx\) 
(where y is the first variable after x for which x is free in r(a), and 
183 


A NEW INTRODUCTION TO MODAL LOGIC 
r{a)\ylx\ is T(OL) with y replacing free x. See p. 241). 
Any model (W,R,V) for modal logic assigns a subset of W to each 
propositional variable. This means that we may define a corresponding 
LPC model (D*,V*> by requiring that D* = W, V*(/?) = R, and that 
V*(p) = {w G W:V(/?,w) = 1}. Since (W,R,V) completely determines 
(D*, V*) then (W,R, V) may be regarded as providing an interpretation for 
r(a) as well as for a. Let a be a wff of LPC containing only one free 
variable, say x. For w € W let V* denote V*, where fi is an assignment 
to the variables of ££ (see p. 238) such that fi(x) = w. Thus V*(<r(a)) = 
1 means, in effect, that r(a) is true in (W,R,V) for an assignment which 
gives x the value w. Then an easy inductive argument establishes that V^ 
r(a) = V(a,w). 
THEOREM 10.7 If S is characterized by a class of frames defined by a 
collection of closed wff of ££ then S is compact. 
Proof: Let ^ b e a class of frames which characterizes S, and suppose 
that A is a (possibly infinite) collection of closed wff of ££ such that & G 
^iff, for every 6 G A, 6 is valid in ^ ( i n the ordinary first-order sense). 
Now let A be any S-consistent collection of modal wff and let r(A) = 
{r(a):a € A}. Consider any finite subset 0 of A. Let 6 be the 
conjunction of all the members of 0. Since 0 is S-consistent ~6 is not 
a theorem of S, and so 0 is true for some w G W in some (.^V) based 
on some & G £1 So, for every 6 G A, where (D*,V*) corresponds with 
(^,V), V*(5) = 1 and V*(r(0)) = 1. But this means that every finite 
subset of A U r(A) is satisfiable, and so, by the compactness of first-
order logic (see p. 262), A U T(A) is satisfiable. So there is some 
(W,R,V) based on a frame &' (= (W,R)) for which there is a w G W, 
and a corresponding (D*,V*) such that V*(6) = 1 for 6 G A and 
V*(r(a)) = 1 for a G A. So V(a,w) = 1 for a G A and since d is a 
closed wff of i£, 6 is valid on &' 
and so &' 
G %. So A is 
simultaneously satisfiable on a frame for S; so S is compact. 
If S is any complete system then S is characterized by the class of all 
its frames, and so if S is not compact the class of all its frames is not 
first-order definable. Where S is not complete then S is not characterized 
by any class of frames and so, a fortiori, not by any first-order definable 
class of frames. Nevertheless it is possible that the class of all frames for 
an incomplete logic is first-order definable. An example is the system 
VB.13 This system is K + 
184 


FRAMES AND SYSTEMS 
VB 
LMT 
D L(L(Lp D p) D p) 
VB is not characterized by any class of frames, but the class of all its 
frames is defined by the condition VJC(~ lyxRy V 3y(xRy A ~ 3z yRz)). 
This condition says that every world either is or can see a dead end, and 
characterizes the system K + 
MV LMT 
D L± 
The incompleteness of VB is established by showing that MV is valid on 
every frame for VB, but is not a theorem of VB. 
So a system's frames can be first-order definable without the system's 
being first-order characterizable. And the converse can happen too. A 
simple example of this is the following,14 though it is not quite as general 
as it could be as it speaks only of definability by a single LPC sentence. 
The system in question is characterized by the single condition that every 
world can see a reflexive world: 
(*) 
Vx3y(xRy A yRy) 
Curiously enough this system, called KMT, is not finitely axiomatizable. 
It is K together with, for every n > 1 
MTn 
M((LPl D Pl) A ... A (Lpn D Pn)) 
THEOREM 10.8 KMT is characterized by frames satisfying (*). 
Proof: If any world w can see a reflexive world w' then LPl D Pl is true 
at w' for all i and so every MTn is true at w. Thus KMT is sound with 
respect to the class in question; and it is not difficult to see that every 
world in its canonical model can see a reflexive world, for if not 
L~(w) U {La D a: a any wff} 
would be inconsistent. And if this were the case then for some L(3ly ... , 
L(3k G w and some a,, ... ,an we would have 
!-(/?, A ... A ft) D -((La, D a,) A ... A (Lan DaJ) 
and so by DR1, K3 and LMI 
185 


A NEW INTRODUCTION TO MODAL LOGIC 
[-(Ljff, A ... A Lft) D ~M((Lax D a,) A ... A (Lan DaR)) 
which would make w inconsistent in KMT. 
Although frames satisfying (*) are sufficient to characterize KMT, they 
are not all the frames for KMT. One other frame is (Nat, <), but more 
important for our purposes are what can be called non-identity frames. 
(W,R) is a non-identity frame (Nl-frame for short) iff it satisfies the 
condition 
VxVy(xRy = x^y) 
In other words every world can see every other world but cannot see 
itself. Since non-identity frames are irreflexive they do not satisfy (*). 
Non-identity frames have the property that an Nl-frame is a frame for 
KMT iff it is infinite. To prove this we proceed as follows: 
THEOREM 10.9 If & = (W,R) is an Nl-frame where W has n+1 
members, then KMTn fails on &. 
Proof: Let the members of W be w,, ... ,wn+1. For 1 < i < n, put 
V(pi,Wj) = 1 but for w ?* Wj put V ^ w ) = 0. Then Lpx D px fails at wx 
and so 
(LPl D Pl) A ... A (Lpn D Pn) 
fails at every wx (1 < i < n). But these are the only worlds wn+1 can see, 
and so KMTn fails at wn+l. 
It is easy to see that if MTn is valid on a frame so is MTm for m < n, 
since MTm can be obtained from MTn by identification of variables. So 
theorem 10.9 shows that if KMTn fails on ^ , so does KMTm for m > n. 
In other words KMTn fails on & provided & has no more than n+1 
members. 
LEMMA 10.10 La D a is false in at most one world in an Nl-frame. 
Proof: For La D a to be false at w, La must be true and a false. So a 
is true at every w' 5* w and so La Da is true at every w' ?* w. 
THEOREM 10.11 
If ^=(W,R) is an Nl-frame where W has more 
than n+1 members, then KMTn is valid on &. 
186 


FRAMES AND SYSTEMS 
Proof: From lemma 10.10 we have that La D a is false in at most one 
world in an Nl-frame. So 
(t)(LPl 
DPl) 
A ... A 
(LpnDPr) 
can be false in at most n worlds. But since .^has more than n +1 worlds 
there must be at least two worlds at which (f) is true. But in an Nl-frame 
any two worlds can between them be seen by the whole frame and so 
MTn is valid on &. 
Theorems 10.9 and 10.10 have the consequence that the MTns produce 
a strictly ascending chain of systems whose union is KMT. By a standard 
argument15 this shows that KMT is not finitely axiomatizable with US, N 
and MP as sole rules of inference. 
THEOREM 10.12 
An Nl-frame is a frame for KMT iff it is infinite. 
This follows immediately from theorems 10.9 and 10.11. 
THEOREM 10.13 
There is no sentence of LPC which characterizes 
the class of all KMT frames. 
Proof: Suppose that 6 were such a sentence. For n > m, let (3n be defined 
as 
xn 5* x0 A ... A xn * *n., 
and let A be the set 
{0n: n > 1} U {-dyxVyxRy 
s x * y) 
Now any finite subset of A is satisfiable in a finite Nl-frame which (by 
theorem 10.12) will not be a frame for KMT and will therefore satisfy 
~6. So A will be simultaneously satisfied in some frame &. But any 
frame satisfying the whole of A will have to be an infinite Nl-frame. By 
theorem 10.12 it will be a KMT frame and so will validate 5, thus 
contradicting the fact that ~6 E A. 
Although theorem 10.13 does not show that no infinite class of first-
order sentences characterizes the frames for KMT, it does nevertheless 
provide a simple example of a system which can be characterized by a 
single first-order sentence, but whose class of frames cannot be so 
187 


A NEW INTRODUCTION TO MODAL LOGIC 
characterized. 
Second-order logic 
In first-order predicate logic the quantifiers only use individual variables. 
Second-order logic is obtained by allowing predicate variables to be put 
in quantifiers. This section is intended for those who know a little about 
second-order logic, and is intended to show that in a certain sense 
classical modal propositional logic, from a semantical point of view, 
belongs with second-order logic and not with first-order logic.16 
We first recall the translation function r which takes every wff of 
modal propositional logic to a wff of a language i£+ of predicate logic. 
Now this translation did not make any use of quantifiers over predicate 
variables and it may appear that it is a translation into first-order logic. 
If we stick to truth at a world in a model this is indeed so, since a model 
for modal propositional logic does give particular values to the 
propositional variables, and so can equally be regarded as giving values 
to their translations in i£+. But when we are interested in validity on a 
frame - and that remember was always the basic sense of validity -
although the frame supplies a domain W and an interpretation for /?, the 
modal wff is valid on the frame iff it is true for every assignment to the 
propositional variables. In other words, where r(a) is the translation of 
a modal wff a containing propositional variables /?,, ... , /?n we are 
considering the truth in (W,R) of V/?, ... V/?nr(a). We can illustrate this 
using the wff T, Lp Dp. r(T) is 
Vx(Vy(xRy D py) D px) 
but of course given a frame (W,R) the validity of T on (W,R) 
corresponds to the truth in (W,R), considered as a structure to interpret 
second-order logic, of 
VpVx(Vy(xRy D py) D px) 
In the case of T, corollary 10.2 on p. 173 tells us that any frame (W,R) 
is a frame for T iff R is reflexive. In terms of the second-order translation 
this means that we need to show the following: 
VxxRx = VpVx(Vy(xRy D py) D px) 
We prove the implication in both directions. The first direction does not 
188 


FRAMES AND SYSTEMS 
involve an essential use of second-order logic: 
Vy(xRy D py) D (xRx D px) 
xRx D (Vy(xRy D py) D px) 
VxxRx D Vx(Vy(xRy D py) D px) 
VxxRx D VpVx(Vy(xRy D py) D px) 
The other direction involves the second-order equivalent of the principle 
we shall call Vl in our discussion of LPC in Part III. In the present case 
we shall use the fact that if every property p is true of an individual then 
the property of being able to be seen by some particular individual x is 
also true of that individual. To be specific we have, as an instance of that 
principle 
VpVx(Vy(xRy D py) D px) D Vx(Vy(xRy D xRy) D xRx) 
We then proceed as follows: 
Vx(Vy(xRy D xRy) D xRx) D VxxRx 
VpVx(Vy(xRy D py) D px) D VxxRx 
Contrast T with KW. The translation of W is 
Vp(Vy(xRy D {VziyRz D pz) D py)) 3 VtfxRy D py)) 
From the fact that KW is not first-order definable it follows that the 
second-order formula just mentioned is not equivalent to any wff of first-
order logic. 
Exercises — 10 
10.1 
(a) Prove that every frame for D is serial. 
(b) 
Prove that every frame for S4.2 is convergent. 
10.2 Prove that every frame for Kl.l (K + L(L(p D Lp) D p) D p) is 
transitive. 
189 


A NEW INTRODUCTION TO MODAL LOGIC 
10.3 
Prove that K is characterized by the class of 
(a) 
all irreflexive frames; 
(b) 
all asymmetrical frames; 
(c) 
all intransitive frames. 
10.4 
Prove that KB is characterized by the class of all irreflexive 
symmetrical frames. 
10.5 
Prove that K4 is characterized by the class of all irreflexive 
transitive frames. 
10.6 
Prove that KG' is characterized by condition C (p. 182). 
10.7 
Prove that if (W,R) is a frame for KG' then R satisfies C. 
10.8 
Prove that the second-order translations of the axioms for S4, B, 
S4.2, S4.3 and S4M correspond to the first-order conditions which 
characterize those systems. 
Notes 
1 See Hughes and Cresswell 1984, pp. 47-51. Other results of this kind are found 
in Sahlqvist 1975. 
2 Gabbay, 1981. The name 'Gabb' is ours. 
3 Gabbay's result has the consequence that if S is canonical then any non-theorem 
is rejected by an irreflexive frame, and so S is characterized by a class of 
irreflexive frames. (There are of course non-canonical systems which are 
characterized by a class of irreflexive frames, for instance KW.) The lemma that 
Gabbay actually proves is more general since it covers systems with more than 
one modal operator. In particular he is interested in applying it to tense logic, 
where there are two operators, G and H, meaning, respectively, 'it always will 
be that', and 'it always has been that'. 
4 Fine 1974a, p. 40. 
5 Conversely, if S is a system for which there exists a A which is S-consistent but 
is not satisfiable in any frame for S then, inter alia, &* cannot be a frame for S. 
We call S canonical iff ^"* is a frame for S. From what we have said canonicity 
implies compactness. (Rob Goldblatt has informed us that some results obtained 
by Dov Gabbay for tense logic can be adapted to show that compactness does not 
always imply canonicity.) 
6 Prior 1967, p. 29. Although Nl appears on p. 293 of Dummett and Lemmon 
1959 the names Nl and S4.3.1 appear to be due to Sobosinski 1964b. (See 
Hughes and Cresswell 1968, p. 263.) Another proof that S4.3.1 is not canonical 
may be found in van Benthem 1980 (where Nl is referred to as Dum). That 4 
190 


FRAMES AND SYSTEMS 
follows from Nl is proved in van Benthem and Blok 1978. 
7 The first completeness proof (by algebraic methods) is in Bull 1965a. Model-
theoretic proofs of this and related results are given in Segerberg 1970. 
8 In fact, the result, as shown in Hughes and Cresswell 1986, can be generalized 
to show the non-compactness of any system between S4.1 (which is S4 + Nl) 
and K3.1, which is S4.3 + J l 
L(L(Lp 
D Lp) D p) D p. (See Hughes and 
Cresswell 1968, p. 266.) The reason is that the finite model described in the text 
to establish (1) is based on a frame for K3.1. K3.1 is the logic of finite linear 
frames, i.e. finite (reflexive and transitive) frames in which each world has a 
unique immediate successor. The system characterized by frames in which W is 
the natural numbers and R is < is K4.3 (i.e. K4 + Lem0, see p. 141) + Z, 
L(lp D p) D (MLp D Lp). More non-compact logics are presented in Fine 1974a 
and Schumm 1987. A different sense of compactness is used in S.K. Thomason 
1972b. 
9 These issues form an area of modal logic called correspondence 
theory. A fuller 
discussion may be found in van Benthem 1983 and 1984. 
10 Lemmon and Scott 1977, pp. 151ff. See also Chellas 1980, pp. 85-90. 
11 Sahlqvist 1975, pp. 121ff. Lemmon and Scott's conjecture was less general in 
that they considered only the cases in which n = 0 and a has the form 
AT 1^ 1/?, A ... A 
ATWpt 
See also Goldblatt 1975b. 
12 Goldblatt 1976, Part II, pp. 40-42. That the class of all frames for KM is not 
first-order definable is proved in Goldblatt 1975a and in van Benthem 1975. A 
proof that S4M and K4M are first-order definable is in Lemmon and Scott 1977, 
p. 75. Goldblatt 1991 proves that KM is not canonical, and Wang 1992 that it is 
not compact. 
13 See Chapter 4 of Hughes and Cresswell 1984. 
14 Hughes 1990. Fine 1975a establishes that every system which is first-order 
definable is canonical. Note, however, that Fine's own sense of the term 'first-
order definable', and therefore the way in which he himself expresses his result, 
is not the same as ours. In our sense, every first-order definable system is 
automatically complete. In Fine's sense, a system S is first-order definable if the 
class of all the frames for S is first-order definable, and in that sense the first-
order definability of a system does not guarantee its completeness. Fine therefore 
states his result by saying that every complete system which is 
first-order 
definable is canonical. In Fine's sense, though not in ours, the system VB is 
therefore first-order definable. 
15 See Lemmon 1965a. The argument is as follows: To say that K -I- A is not 
finitely axiomatizable is to say that there is no finite set 0 such that K + A = K 
4- 0 . (See p. 50.) To prove this it is sufficient to show that A is a set whose 
members form a sequence a,, <x2 ••• e t c- such that where An = {a.u ... ,an} then 
an+1 is not a theorem of K 4- An. (In the example in the text o^ is MTn.) Suppose 
there were a finite 0 such that K + 0 = K + A. Let (3 be the conjunction of the 
191 


A NEW INTRODUCTION TO MODAL LOGIC 
members of 6. Then /8 is a theorem of K 4- A. So there is a proof of (3 in K + 
A. But a proof uses only finitely many wff and so there will be a proof of β in 
some K + An. So K + A will be included in K 4- Λn. But this is impossible since 
αn+1 is a theorem of K + A but not a theorem of K + Λ„. 
16 The connection between second-order logic and modal logic is quite strong. 
S.K.Thomason 1974a, 1975a, 1975b, shows that the consequence relation of 
second-order logic can be expressed in propositional modal logic. 
192 


11 
STRICT IMPLICATION 
Historical preamble 
Modal logic was discussed by several ancient authors, notably Aristotle,1 
and also by mediaeval logicians; their work, however, lies outside the 
scope of this book. The subject then appears to have been almost 
completely neglected until fairly recent times. In fact the first steps 
towards modern modal logic seem to have been taken by Hugh MacColl 
towards the end of the 19th century. MacColl introduces the operations 
of disjunction (a + b), negation (a') and implication (a : b).2 He then 
asserts as a valid principle 
(a : b) : a' + b 
but denies the validity of 
(a : b) = a' + b 
on the ground that if a means 'He will persist in his extravagancy' and b 
means 'He will be ruined', then the negation of a : b is 'He may persist 
in his extravagancy without necessarily being ruined', while the negation 
of a' + b is 'He will persist in his extravagancy and he will not be 
ruined'. MacColl objects to the identification of these precisely because 
the first asserts only possibility while the second asserts something more. 
What this amounts to is that he regards a : b as expressing necessary 
implication, and a' + b as expressing material implication. In later 
papers, and in his book entitled Symbolic Logic and its Applications, this 
becomes even clearer: for he explicitly denies that his implicational 
193 


A NEW INTRODUCTION TO MODAL LOGIC 
connective can be given a truth-functional interpretation, and he defines 
(A : B) as (A' + B)G (or alternatively as (AB')"), where G and " 
represent necessity and impossibility respectively.3 
But MacColl does not give any axioms4 and his system can hardly be 
called a modal logic of the distinctively modern kind with which this book 
is concerned. For that we have to wait until shortly after the publication 
in 1910 of Principia Mathematical a work which did more than any other 
to establish the axiomatic method in logic. Beginning in 1912 C.I. Lewis 
published a series of articles and books6 in which he expressed 
dissatisfaction with the notion of material implication found in Principia. 
The grounds of his dissatisfaction were very much the same as those of 
MacColl, but he had the great advantage of being able to use an axiomatic 
method based on that of Principia itself, and he used it to construct a 
system (or rather a series of systems) in which material implication no 
longer played the dominant role. It is the work of Lewis which marks the 
beginning of modern modal logic properly so called. 
The 'paradoxes of implication' 
In the system of Principia Mathematica — indeed in any standard system 
of PC — there are found the theorems: 
(1) 
pD 
(qD p) 
(2) 
~pD 
(pD q) 
The sense of (1) is often expressed by saying that if a proposition is true, 
any proposition whatsoever implies it: that of (2) by saying that if a 
proposition is false, it implies any proposition whatsoever. Together they 
are often called the 'paradoxes of (material) implication'. Moreover, since 
for any proposition/?, either the antecedent of (1) or the antecedent of (2) 
must be true, it is easy to derive from (1) and (2) the further theorem: 
(3) 
(pD q) V (qD p) 
i.e. in any pair of propositions, either the first implies the second or the 
second implies the first. 
Lewis did not wish to reject these theorems. On the contrary, he 
argued (and surely correctly) that (1) and (2), when properly understood, 
are 'neither mysterious sayings, nor great discoveries, nor gross 
absurdities', but merely reflect the truth-functional sense in which 
Whitehead and Russell were using the word 'imply'. But he also 
194 


STRICT IMPLICATION 
maintained that there is another, stronger, sense of 'imply', a sense in 
which when we say that/? implies q we mean that q follows from p; and 
that in this sense of 'imply' it is not the case that every true proposition 
is implied by any proposition whatsoever, nor that every false proposition 
implies any proposition whatsoever. Moreover in this stronger sense of 
'imply' there are pairs of propositions neither of which implies the other. 
Lewis was thus led to draw the distinction between an implication which 
holds materially and one which holds necessarily or strictly,1 and to make 
analogous distinctions for disjunction and equivalence. Before examining 
Lewis's modal logic we shall have something to say about the relation 
between propositions that he was attempting to capture. 
The symbol Lewis used for strict implication was -3, and he 
interpreted p -3 q to mean that it is impossible that p should be true 
without g's being true too. An alternative way of expressing the fact that 
it is impossible for p to be true without q also being true is to say that it 
is necessary that if p is true so is q, i.e. that L(p D q) is true. In view of 
this equivalence we shall not have to take -3 as primitive but can define 
it as follows: 
[Def-3] 
(a^(3)=DfL(aD 
(3) 
If instead of L we had taken M as primitive we could have defined a -3 (3 
as ~M(a A ~0). 
When two propositions strictly imply each other we say that each is 
strictly equivalent to the other. We use = as the strict equivalence sign 
and introduce it by the definition: 
[Def =] 
(a = 0) =Df ((a -6 0) A ((3 -3 a))8 
Material and strict implication 
It is not hard to see how replacing D with -3 affects formulae like 
(1) —(3) on p. 194. Important differences between strict and material 
implication can be brought out, even in the system K, by comparing 
certain pairs of formulae. Sometimes a formula containing occurrences of 
D is a theorem, but when D is replaced by -3 the formula ceases to be 
a theorem. (Of course in any normal system this will never be the case 
when the only occurrence of D so replaced is the main operator, for then 
either both formulae are theorems or neither is.) For example, in each of 
the following pairs the first formula is a theorem but the second is not: 
195 


A NEW INTRODUCTION TO MODAL LOGIC 
(la) (pD q) V (qD p) 
(lb) (p ^q) 
V (q -3p) 
(2a) (p A q)D (p D q) 
(2b) (p A q) D (p S q) 
Moreover, sometimes we have an equivalence which is a theorem, but 
when D is replaced by -3 the resulting formula is provable as an 
implication only. For example, 
(3a) ((pD r) V (q D r)) s (fp A q) D r) 
is a theorem, but while 
(3b) (fp S r) V (q -3 r)) D {fp A q) -3 r) 
is also a theorem, its converse is not. Here are some further theorems 
involving strict implication. They are numbered in sequence with the K 
theorems in Chapter 2. 
K8 
(~/> -5p) s Lp 
PROOF 
PC 
(1) 
(~pDp)=p 
(1) X DR2 
(2) 
L(~p D p) = Lp 
(2)Def -3 
(3) 
(~p Sp) 
= Lp 
Q.E.D. 
Just as whenever we have f- a D jS we also have \- a -3 /?, so 
whenever we have |- a = @ we also have \- a = (3). I.e., K8 and all 
other equivalential theorems are also provable as strict equivalences. 
K9 
(p-3 ~p)= 
L~p 
The proof is similar to that for K8. 
K10 
iiq^p) 
A ( ~ * - 3 / 0 ) 
=LP 
PROOF 
PC 
(1) 
((q Dp) A (qD 
~p)) m p 
(1) X DR2 
(2) 
L((q D p) A (~q D ~p)) D Lp 
(2)K3fa D p/p,~q 
D p/q] X Eq: 
196 


STRICT IMPLICATION 
(3) 
(L(q D p) A L(~q D p)) m Lp 
(3)Def -3 
(4) 
((</ ^ />) A (~<? -3 p)) = L/> 
Q.E.D. 
Kll 
((p -3 0 
A (p -3 ~<?)) = L~/> 
Proof as forKlO. 
K8-K11 express important facts about non-contingent propositions (i.e. 
propositions which are either necessary or impossible). K8 says that a 
necessary proposition is one which is strictly implied by its own negation. 
K9 says that an impossible proposition is one which strictly implies its 
own negation. K10 says that a necessary proposition is one which is 
strictly implied both by another proposition and by the negation of that 
other proposition. Kll says that an impossible proposition is one which 
strictly implies both another proposition and the negation of that other 
proposition. 
K12 
LpD {q -3 p) 
PROOF 
PC 
(1) 
PD(qDp) 
(1) X DR1 
(2) 
Lp D Uq D p) 
(2)Def -3 
(3) 
LpD (q -3 p) 
Q.E.D 
K13 
L~pD(p^q) 
Proof as for K12. 
K12 and K13 should be compared with (1) and (2) on p. 194. We will 
come back to them on pp. 202-204, since they have been the occasion of 
a large amount of controversy, but our immediate task is to return to 
Lewis's development of modal logic. 
The 'Lewis' systems 
In his early articles Lewis sometimes took strict disjunction as primitive, 
sometimes strict implication, sometimes logical impossibility; and in his 
book A Survey of Symbolic Logic,9 he set out an axiomatic system (the 
Survey system) in which he again took logical impossibility as the 
primitive modal operator (along with conjunction and negation as 
primitive truth-functional operators). In 1930 Oskar Becker10 proposed 
some additional axioms for the Survey system and showed that they 
enable all modalities to be reduced (see p. 52) to a small number of non-
197 


A NEW INTRODUCTION TO MODAL LOGIC 
equivalent ones. But the first comprehensive treatment of systems of strict 
implication (or indeed of systems of modal logic at all) appeared in 1932 
in Lewis and Langford's book Symbolic Logic. Here possibility is taken 
as the primitive modal operator, and two axiomatic systems of strict 
implication (called S1 and S2 respectively) are developed in considerable 
detail. In an appendix several other systems are outlined as well: one of 
these is the system of the Survey (S3); two others, which contain certain 
of Becker's reduction postulates, are called S4 and S5. 
Since Lewis assumed that what is necessary is true it is not to be 
expected that K would be one of his systems, but in fact T is not either. 
Nevertheless for purely first-degree wff, of the kind we have just been 
discussing, there is no difference between T and any of the Lewis 
systems. We shall set out these systems in the form in which they occur 
in Symbolic Logic, except that we shall use the notation and terminology 
employed in Chapter 1 of this book.11 
The system SI 
Primitive symbols12 
py q, r, ... 
[Propositional variables] 
~, M 
[Monadic operators] 
A 
[Dyadic operator] 
(, ) 
[Brackets] 
Formation rules 
1. A propositional variable is a wff. 
2. If a is a wff, so are ~ a and Ma. 
3. If a and 0 are wff, so is (a A (3). 
Definitions13 
[Def V] 
(a V P)=« ~(~a 
A 
~fi 
[Def -6] 
(a -3 0) =df ~M(a A ~0) 
[Def =] 
(a = P) =df ((a S 0) A {fi -6 a)) 
[Def L] 
La =df 
~M~a 
Axioms14 
AS1.1 (p A q) S(q 
A p) 
AS1.2 (p A q) -3 p 
AS1.3 p -3 (p A p) 
AS1.4 ((p A q) A r) S ip A (q A r)) 
AS1.5 ((p -3 q) A (q S r)) -3 (p -3 r) 
198 


STRICT IMPLICATION 
AS1.6 (p A (p -3 q)) -3 q 
Transformation rules 
1. Uniform Substitution, as in the systems in Part I. 
2. Substitution of strict equivalents: If \-a, and /? differs from a only in 
having some wff, 6, at one or more places where a has a wff 7, then if 
1-7 = 8, 1-0. 
3. Adjunction: \- a, |- 0, -* (- a A /3. 
4. Modus Ponens (Detachment): \- a, |- a -3 0, -* |-j3. 
There is one striking difference between the above basis for S1 and any 
of the bases discussed in earlier chapters, and that is that it is not 
constructed as an extension of PC.15 In fact none of the axioms of SI is 
a wff of PC at all. Moreover, while the rule of Uniform Substitution 
belongs to PC, the SI Modus Ponens rule is stated for strict implication, 
not for material implication as for PC. (We shall often call it the rule of 
Strict Detachment, and the corresponding PC rule, the rule of Material 
Detachment.) As a result proofs of theorems in SI are apt to have a 
somewhat different 'style' from those in, say, T, since we are not free to 
help ourselves to any theorem of PC which seems likely to be useful. 
Nevertheless, SI contains PC; i.e., every theorem of PC is a theorem of 
SI. It is easy to introduce the operators D and = (as Lewis himself 
does16) by the definitions: 
[Def D] 
(a D (3) = D f ~(ot A ~0) 
[Def = ] 
(a = 0) = D f ((a D (3) A (0 D a)) 
The axiom AS1.6 is interdeducible with Lp -3 p. If it is omitted we 
have a system called Sl°, which stands to SI rather as K stands to T.17 In 
comparing SI with T we first notice that the basis of SI is certainly 
contained in T. Further, SI contains the whole of the basis of T except 
for the rule of necessitation. In fact SI has no theorems of the form LLa 
at all, and if so much as one is added the other rules enable the derivation 
of N, and increase SI to T.18 
Lemmon's basis for SI 
It is in fact possible to axiomatize SI by making additions to non-modal 
PC as we did in earlier chapters. The following basis is due to EJ. 
Lemmon.19 Lemmon's basis for SI consists of the following axioms: 
199 


A NEW INTRODUCTION TO MODAL LOGIC 
(1) 
every PC-tautology; 
(2) 
Lp D p; 
(3) 
(L{p D q) A L(q D r)) D L(p D r). 
The transformation rules are Uniform Substitution, Modus Ponens (for 
D), and two extra rules. The first is a restricted form of Necessitation: 
N' 
If a is a PC-tautology or an axiom then |- La. 
The second is a rule for the substitution of proved strict equivalents: 
Eq' If a differs from (3 only in having a wff y in some of the places 
where 0 has 6, and |- y = 6, then \- a = (3. 
The system S2 
SI was not in fact Lewis's preferred system. The system he designated 
as the correct system is one called S2, obtained from SI by adding 
AS2.1 M(p A q) -3 (Mp A Mq) 
Lewis calls this the Consistency Postulate. Its sense is that only a possible 
(or consistent) proposition can be a term in a consistent conjunction. S2 
can also be axiomatized in the style of Lemmon. We replace (3) with the 
wff K from p. 25 
K 
L(p D q) D (Lp D Lq). 
We keep N' (now of course applied to K rather than (3)) and we replace 
Eq' with a rule called Becker's Rule.™ 
BR 
|- L(a D (3) -* \- L(La D Lfi) 
(Using S BR can be written as \- a -3 (3 ^ 
\- La -3 L(3.) 
The system S3 
Although Becker's rule belongs to S2 the formula 
(4) 
(p -3 q) -3 (Lp -6 Lq) 
which might be confused with it, is not a theorem of S2. Nevertheless it 
200 


STRICT IMPLICATION 
could be added to S2, and if it is we obtain a system deductively 
equivalent to the system Lewis presented in his 1918 book. This system 
is called S3.21 
Lewis also discussed S4 and S5. Although axiomatized differently, 
these systems are deductively equivalent to the S4 and S5 studied in Part 
I of this book. 
Validity in S2 and S3 
One reason why we shall have to make a substantial change in our earlier 
definitions of validity if we are to deal with S2 and S3 is that these 
definitions — i.e. those for T, S4, S5 and the like — all satisfy the rule 
of Necessitation. That is to say, if any wff, a, is valid in terms of any of 
these definitions, La is also valid. But as we have observed, the rule of 
Necessitation does not hold, at least unrestrictedly, in S2 and S3. 
Another, related, feature of S2 and S3 is that they are compatible with 
(though they do not contain) the axiom MMp.22 This means that they are 
compatible with (though they do not commit us to) the view that every 
proposition is 'possibly possible'. And this suggests an idea which is in 
fact the key to S2- and S3-models, that there might be some 'worlds' in 
which every proposition without exception — even one of the form 
p A ~p — is possible. Kripke23 calls such worlds non-normal worlds, 
and we shall follow him in this terminology. Worlds of the kind that 
occur in the frames of normal modal systems are by contrast called 
normal worlds. The rules for evaluating non-modal formulae in non-
normal worlds are the same as in normal worlds — thus even in a non-
normal world we never have p A ~p true for example — but for modal 
formulae in non-normal worlds Ma is always true and La is always false. 
In this respect non-normal worlds are the reverse of dead ends in normal 
modal logics. 
In an S2 frame there must be at least one normal world, and there may 
(but need not) be one or more non-normal worlds.24 Every normal world 
can see itself, and every non-normal world can be seen by at least one 
normal world. Otherwise the accessibility relations can be as we please. 
In an S3 frame there is the additional requirement that the accessibility 
relation be transitive. A formula will be said to be S2-(S3-)valid iff it is 
true in every normal world in every model based on an S2- (S3-) frame.25 
More exactly expressed, an S2 frame26 is a triple (W,R,N) where W 
is a set of objects (worlds), N is a proper subset of W, i.e. N Q W but 
N ^ W , and R is a relation such that (a) R is reflexive over N, i.e. if w 
G N then wRw, and (b) for every w' G W there is some w' G N such 
201 


A NEW INTRODUCTION TO MODAL LOGIC 
that WRw'. (W,R,N,V) is an S2-model iff (W,R,N> is an S2 frame and 
V is a value-assignment as on p. 38, except that [VL] should be changed 
to read that for any wff, a, and for any w G W, V(La,w) = 1 if w G 
N and for every w' such that wRw', V(a,w') = 1. Otherwise V(La,w) = 
0. (The effect of this is that if w is normal, V(La>w) is computed as in a 
T-model; but if w is non-normal, V(La,w) = 0 in every case — and 
hence, incidentally, V(Ma,w) = 1 in every case.) 
A wff a is valid on an S2 frame (W,R,N) iff in every S2-model 
(W,R,N, V) based on (W,R,N), V(a,w) = 1 for every w G N. A wff is 
S2-valid iff it is valid on every S2 frame. An S3 frame is defined in the 
same way as an S2 frame, except that we add the condition that R is 
transitive. A wff a is S3-valid iff it is valid on every S3 frame. 
For those who prefer the approach via the parlour games of Chapter 
1, the S2-game is the modal game with the following modifications. Some 
of the sheets of paper are, say, white, others pink. In every S2-setting at 
least one player must have a white sheet; but some of the players may 
have pink sheets instead. No player with a pink sheet may see any other 
player, but every such player must be seen by at least one player with a 
white sheet. The rules for responding to calls are, for players with white 
sheets, exactly as in the modal game. For players with pink sheets, rules 
1—3 are as in the modal game, but rules 4 and 5 (those covering calls 
with L and M) are replaced by the following: 
4'. If a call is of the form La, do not raise your hand. 
5'. If a call is of the form Ma, raise your hand. 
A call is an S2-successful call iff in every S2-setting it would lead every 
player with a white sheet to raise his or her hand. A formula is S2-valid 
iff it would form an S2-successful call. The S3-game will be the S2-game 
with the added rule that in every setting the seeing-relation must be 
transitive. S3-successful calls and S3-validity are then defined as above, 
with 'S3' replacing 'S2' throughout. 
S2 and S3 may be shown to be sound and complete with respect to this 
semantics.27 The soundness result also enables us to establish that they are 
distinct systems, and that neither contains S4. T contains S2 but neither 
contains nor is contained in S3. SI is not susceptible of this kind of 
treatment and the only known semantics for it is unintuitive.28 
Entailment 
An important modal notion is that of entailment. By this we understand 
202 


STRICT IMPLICATION 
the converse of the relation of following logically from (when this is 
understood as a relation between propositions, not wff) i.e. to say that a 
proposition, /?, entails a proposition, q, is simply an alternative way of 
saying that q follows logically from p, or that the inference from p to q 
is logically valid.29 It is clear from the writings we have already referred 
to that Lewis wished to interpret -3 as 'entails'. Now there has been a 
good deal of philosophical controversy about the correct analysis of 
entailment and in particular K12 and K13 on p. 197 are sometimes known 
as the 'paradoxes of strict implication',30 and are often considered 
problematic when -3 is interpreted as 'entails'. We shall look at them and 
some associated formulae in the following forms: 
(1) 
(p A ~p) 
Sq 
(2) 
q -6 (p V ~p) 
(3) 
~MpD 
(p^ 
q) 
(4) 
LqD 
(p-3 q)* 
When -3 is interpreted as 'entails', (1) means that from any proposition 
of the form (p A ~/?) any proposition whatever can be deduced, and (2) 
means that from any proposition whatever there can be deduced any 
proposition of the form (p V ~ p). (3) and (4) are more general: (3) 
means that from any logically impossible proposition (whether of the form 
(p A ~p) or not) any proposition whatever can be deduced, and (4) 
means that every necessary proposition (whether of the form (p V ~ p) 
or not) can be deduced from any proposition whatever. 
If these are not sound principles of deducibility, that would of course 
tell against the claim of the standard modal systems to be correct logics 
of entailment. But in order to decide whether they are sound principles of 
deducibility or not we have to look into what we take ourselves to be 
asserting when we assert that one proposition is deducible from another. 
Now one plausible account is that to say that q is deducible from p is 
to say that it is logically impossible for p to be true but q false. 
Deducibility is after all the relation which obtains between the conclusion 
and the premiss(es) of a valid deductive inference, and what we require 
in a valid inference is the logical guarantee that we shall not have the 
premiss(es) true but the conclusion false. Now by this account the 
'paradoxes' are sound principles of deducibility; and hence it is not their 
presence in but their absence from a system which would tell against its 
claim to be a correct logic of entailment. To take the case of (1): to say 
that (p A ~p) entails q is on this account to say that it is logically 
203 


A NEW INTRODUCTION TO MODAL LOGIC 
impossible for (p A ~p) to be true but q false, i.e. it will amount to 
saying that (p A ~p A ~ q) is logically impossible; but since (p A ~ p) 
is itself impossible, so is (p A ~p A ~q). Similar comments will apply 
to the other 'paradoxes'. Moreover, this account will guarantee that -3 
can be interpreted as 'entails'; for in all the standard systems a -3 0 is 
defined as ~ M(ct A ~p) (or, what comes to the same thing, as 
L(a D /?)), where M is interpreted as 'it is logically possible that'. 
No one is likely to deny that the logical impossibility of (p D q) is a 
necessary condition of qys deducibility from/?, but it has been suggested 
that it is not a sufficient condition on the ground that a further condition 
of g's deducibility from p is that there should be some connection of 
'content' or 'meaning' between p and q. But even those who are inclined 
to accept this further requirement for deducibility, however, have to face 
the following argument. On any account we shall have to regard q as 
deducible from p when it can be derived from p by some valid principle 
or principles of deductive inference. Now the following principles seem 
intuitively to be valid:32 
A. Any conjunction entails each of its conjuncts. 
B. Any proposition, p, entails (p V q), no matter what q may be. 
C. The premisses (p V q) and ~p together entail the conclusion q (the 
principle of the disjunctive syllogism). 
D. Whenever p entails q and q entails r, then/7 entails r (the principle 
of the transitivity of entailment). 
C.I. Lewis has shown that by using these principles we can always derive 
any arbitrary proposition, q, from any proposition of the form (p A —/?), 
in the following way: 
(i) p A ~p 
From (i), by A: 
(ii) p 
From (ii), by B: 
(iii) p V q 
From (i), by A: 
(iv) 
~p 
From (iii) and (iv), by C: 
(v) cf3 
By D we then have the result that (p A ~p) entails q. This derivation 
shows that the price which has to be paid for denying that (p A ~p) 
entails q is the abandonment of at least one of A-D. 
The most fully developed formal response to these 'paradoxes' consists 
204 


STRICT IMPLICATION 
of abandoning C, the principle of disjunctive syllogism. Logics which do 
this are called relevance logics and there is now an enormous body of 
literature on them.34 These systems are well beyond the scope of the 
present book, and in fact relevance logics differ from all the logics we 
have so far considered in that they require a non-standard interpretation 
of the PC symbols, in particular of negation. 
Exercises — 11 
11.1 
Prove that adding LL(p D p) to SI gives T. 
11.2 
Prove that Lemmon's basis for S1(S2) on pp. 199-200 is 
equivalent to Lewis's. 
11.3 
Where S7 is S3 + MMp, prove that (-S3 a iff |-S4 a and |-S7 a. 
11.4 
Let E2 be {a:La G S2}. 
(a) 
Prove that N is not a rule of E2. 
(b) 
Prove that E2 is sound with respect to the class of S2 frames but 
with the definition of validity changed so that a wff is E2-valid iff it is 
true in all worlds, not just normal worlds, in every frame. 
(c) 
Give completeness proofs for E2 and S2 by defining a canonical 
model in which W is the set of all maximal E2-consistent sets of wff and 
w G N iff L{p D p) G w. 
11.5 
Show that E2 can be axiomatized by PC, T, K, and the rules US, 
MP and R*: |- a D (3 -* \-La D Lj3. 
11.6 
Where E3 is E2 with L(p D q) D L(Lp D Lq) show that E3 is 
characterized by S3 frames when validity is truth in all worlds in every 
S3 frame. 
11.7 
S3.5 is S3 + Up D LMp (see note 27). Where an S3.5 frame is 
an S3 frame in which R is symmetrical over N (i.e. if w, w' G N and 
wRw' then w'Rvv) show that S3.5 frames characterize S3.5. 
11.8 
SO.5 is just like T except that N is replaced by the rule: 
N' 
If a is a PC-valid wff then |- a. 
A model for SO.5 consists of a set of worlds, of which one, w>*, is a 
'distinguished' world. For w*, V(La,w*) = 1 iff V(a,w) = 1 for every 
w G W. For every other world La has an arbitrary value. A wff a is 
205 


A NEW INTRODUCTION TO MODAL LOGIC 
S0.5-valid iff V(a,w*) = 1 in every S0.5 model. 
(a) 
Prove that SO. 5 is sound with respect to this definition of validity. 
(b) 
Prove that N is not a rule of S0.5. 
(c) 
Prove that Eq is not a rule of SO.5. 
11.9 
Construct a canonical model for SO.5 in which w* is a set of 
maximal S0.5-consistent sets of wff and every other world is a maximal 
PC-consistent set of wff (i.e. w is maximal and there is no set {«}, 
... ,an} such that each of a,, ... ,an is in w and ~(«i A ... A a j is a 
substitution-instance of a PC-tautology). Use this to prove the 
completeness of SO.5. 
Notes 
1 Aristotle, 350 BC, 29b29-40bl6. An attempt to formalize Aristotle's modal logic 
will be found in McCall 1963. For a general history of ancient and mediaeval 
modal logic see Kneale and Kneale 1962, pp. 81-96, 117-138, 212, 232, 236, 
243, or Bochenski 1961, pp. 81-88, 101-103, 114-115, 224-230. 
2 MacColl 1880, pp. 50-55. 
3 MacColl 1903, 1906a, 1906b, (see especially 1903, pp. 356-7. 
4 He does give (1906a, p. 8) a list of 'self-evident formulae' and it would be 
interesting to know which of the more recent modal systems is the weakest in 
which all these are true. 
5 Whitehead and Russell 1910. 
6 Lewis 1912, 1913, 1914a, 1914b, 1918. Lewis and Langford 1932. 
7 As far as we have been able to discover, the term 'strict implication' first occurs 
in Lewis 1912, p. 526 n. 1. The symbol 3 appears in Lewis 1918. 
8 = as defined here and =Df should not be confused. The former is an operator 
which occurs in wff of a modal system; the latter is a metalogical symbol which 
never occurs in wff but is used only in discoursing about a system. 
9 Lewis 1918, ch. 5 (emended in Lewis 1920). 
10 Becker 1930. 
11 These names ('SI' etc.), by which the systems have since become generally 
known, are given on pp. 500-501 of Appendix II (written by Lewis) in Lewis and 
Langford 1932. They do not occur in Chapter 6, where SI and S2 are developed 
(unless we count a brief reference to 'System 1' and 'System 2' on pp. 177-178). 
Lewis's S4 and S5 are deductively equivalent to the S4 and S5 of Part I of this 
book, though they have different bases. S4 and S5 appear in Lewis and Langford 
1932 only in the appendix on p. 500f., and are rejected by Lewis as acceptable 
systems of strict implication. S3 is the system of Lewis 1918, and SI and S2 are 
the systems developed in Chapter 6 of Lewis and Langford 1932. For a more 
detailed survey of the axioms, theorems and rules of the various Lewis systems 
see Feys 1965, Chapters 12 and 13 of Hughes and Cresswell 1968, and Zeman 
206 


STRICT IMPLICATION 
1973. 
12 Lewis uses ~ for negation, juxtaposition for conjunction, and O for M. 
13 We write these definitions in the style adopted in Part I. Lewis writes them as 
strict equivalences, using propositional variables. Lewis does not have a single 
symbol for necessity, but writes — O ~ throughout. (His O = ourAf). However, 
the abbreviation provided by this definition is an obvious convenience. 
14 Our numbering of these axioms is not the same as that of Lewis and Langford. 
Moreover we omit the axiom p 3 
p since this was shown to be non-
independent in McKinsey 1934. Instead of AS1.6 we may have ~M/? 3 ~p, or 
p 3 Mp. 
15 The first axiomatization of modal logic starting from a PC basis and adding 
extra axioms and rules to it (as in Part I) appears to be that in Godel 1933. 
16 Lewis and Langford 1932, p. 13ff. 
17 Feys 1965, p. 43. 
18 Yonemitzu 1955. 
19 Lemmon 1957. Lemmon also considers a weaker system, which he calls SO.5, 
in which (3) is replaced by K, and N' by the rule N" that if a is a PC-tautology 
then |- La. Interestingly SO.5 does not satisfy the rule Eq, even for proved strict 
equivalents. (See Hughes and Cresswell 1968, pp. 286-288.) By omitting Lp D p 
we obtain SO.5°. In Lemmon 1959, p. 31, there is the suggestion that in SO.5 the 
necessity operator might mean 'it is tautologous by truth tables that ... '. 
20 Becker 1930. The name 'Becker's Rule' was given in Churchman 1938. 
21 S3 was subsequently discovered to be stronger than S2, but Lewis in 1932 (p. 
496) had no proof of this and declared that if S2 should turn out to contain S3 he 
would fall back on SI, which he knew to be weaker than S2. Parry 1939 proves 
that S3 has only 42 distinct affirmative modalities. The systems which result from 
S3 by adding all possible modality reduction laws are classified in Pledger 1972 
and given a possible-worlds semantics in Goldblatt 1973. 
22 This wff is called C13 on p. 497 of Lewis and Langford 1932. 
23 Kripke 1965b, p. 208 uses a slightly different axiomatization based on an 
infinite (though effectively specifiable) set of axioms with material detachment as 
the only primitive rule of inference. His axiomatic basis may be easily shown 
equivalent to Lemmon's and for our purposes there is nothing to choose between 
them though, unlike the bases we are using, Kripke's basis allows the addition of 
LL(p D p) to S2 without obtaining the unrestricted rule of Necessitation and 
permits an infinity of systems to be generated by the axioms Ln(p D p) (for each 
n). For some suggestions for interpreting S2 see Cresswell 1967b. A canonical 
model completeness theorem for S2 appears in Cresswell 1982. 
24 If we insist that there must be at least one non-normal world then MMp 
becomes valid. S2 + MMp has been called S6 (Alban 1943) and S3 + MMp S7. 
(Hallden 1949a, Hughes and Cresswell 1968, pp. 281-284.) S3 is the intersection 
of S4 and S7. S3 -I- LMMp is called S8. In S8 frames every normal world can see 
a non-normal world. 
207 


A NEW INTRODUCTION TO MODAL LOGIC 
25 If we define validity as truth in all worlds we get a semantics for the 'E-
systems' of Lemmon 1957 (see Hughes and Cresswell 1968, pp. 302f). In these 
systems N is replaced by the rule R* |- a D (3 -* \- La D L(3. Unlike normal 
systems, which contain N, these systems have no theorems of the form La, and 
their canonical models contain maximal consistent sets with no wff of that form. 
Segerberg 1971, Chapter 4, calls such systems 'regular' and calls systems like S2 
and S3 'quasi-regular'. That Chapter shows how to apply techniques from normal 
modal logic to regular and quasi-regular logics. One can also study logics in 
which all worlds are normal but in which validity is defined as truth in a 
designated subset of worlds. Chapter 3 of Segerberg 1971 calls these 'quasi-
normal' systems. They all contain (all the theorems of) K, and the rules US and 
MP, but not the rule of necessitation. An example of a quasi-normal system is 
studied in Langholm 1987. It is K 4- p D LnMp and is intended to formalize a 
system of logic advocated in Smith 1936. 
26 Kripke 1965b does not take N as primitive but defines it via R. He calls R 
'quasi-reflexive' provided that for any u>, w' E W, if wRw' then wRw (i.e. a 
world which can see anything can see itself) and then defines a world as normal 
iff wRw. We have used N to make the semantics easier to follow. (Also using N 
generalizes more easily to systems where R is not reflexive over normal worlds.) 
27 Where a normal system S is characterized by a class of frames there is of 
course the non-normal system characterized by the class of all frames obtained 
from frames for S by the addition of non-normal worlds with the condition that 
every non-normal world can be seen by a normal world. All such systems will be 
extensions of the system Feys 1950, 1965, p.68, calls S2°, i.e., in Lemmon's 
axiomatization, S2 without Lp D p. This system is characterized by frames in 
which no restrictions are placed on R, except that every non-normal world can be 
seen by a normal world. S2° corresponds to K as S2 corresponds to T and S3 to 
S4. Corresponding to S5 is a system called S3.5, which is obtained by adding E 
to S3 (Aqvist 1964). Note that the strict form of E, L(Mp D LMp) strengthens 
S3 to S5. A completeness theorem for S3.5 is found in Cresswell 1967a. For S3.5 
we may also prove a conjunctive normal form theorem (Cresswell 1969a). The 
system corresponding to B is S2 + B. (S3 + B is S3.5.) S3.5 + MMp has been 
called S9. (See Hughes and Cresswell 1968, pp.172 and 285f.) 
28 Cresswell 1995a. 
29 This use of 'entails' has for some time been standard in philosophy. It derives 
from Moore 1919 (reprinted in his Philosophical Studies; see esp. p. 291). It is 
important at this point to stress that we are here thinking of a relation between 
propositions rather than wff. For there is a quite different, though equally 
legitimate, use of the term 'logically follows from', whereby a wff j8 'logically 
follows from' a wff a in a logical system S iff |-s a. D 0. The distinction 
between these two senses of 'logically follows from' parallels the distinction 
between validity and necessary truth. We shall have more to say on this on p. 
225. 
208 


STRICT IMPLICATION 
30 Tendentiously; for those on the other side in the controversy regard the 
formulae as expressing perfectly sound principles of deducibility, and on anyone's 
account they express sound and quite unparadoxical truths about strict implication. 
The 'paradoxes' seem to have been first stated (and incidentally accepted as 
unparadoxical) in modern logic by MacColl 1906b, p. 613. For some information 
about mediaeval anticipations of them see Kneale and Kneale 1962, pp. 281ff. 
31 In S2 and stronger systems we can also prove ~Mp 3 (p 3 q) and Lq 3 (p 3 q). 
Two early attempts to formalize a relation which does not lead to the 'paradoxes' 
(Emch 1936 and Vredenduin 1939) avoided them in the S2 forms but contained 
our (1) and (2) as theorems. 
32 To say that q may be derived from p by some valid principle(s) of inference is 
(as noted in Lewis and Langford 1932, pp. 252-255) not the same as saying that 
it may be derived by the principles of a given system, or by principles we have 
already established up to a given point in the development of a system. Rather it 
is to say that the principles which enable us to pass from p to q are sound ones, 
whether they occur in any particular system or not. See Pollock 1966, pp. 
184-185, for a discussion of this confusion in writers later than Lewis. 
33 Cf. Lewis and Langford 1932, pp. 250-251, where there is also found an 
analogous derivation, relevant in a similar way to our (2), of —<y V q from p. 
For a mediaeval anticipation of Lewis's derivation of q from p A ~p see Kneale 
and Kneale 1962 and Kneale 1956, pp. 239-240. It is also possible to derive the 
result that (p A —/?) entails ~q (a simple and equally general variant of the 
'paradox' in question) by starting from the principle that (p A ~q) entails p and 
applying to it the principle of antilogism, viz. that if (p A q) entails r then 
(p A ~r) entails ~q (see Lewis 1914a, p. 246n, and Moh Shaw-Kwei 1950, p. 
70). 
34 A survey of relevance logic is found in Dunn 1986. 
209 


12 
GLIMPSES BEYOND 
Our aim in earlier chapters has been to set out as much modal 
propositional logic as we can in the space at our disposal. But of course 
there is much more to modal logic than we have been able to cover, and 
there are many directions in which the ideas involved in modal logic can 
be extended. In this chapter we shall try to give a few hints of some of 
these. Nothing we say here is at all complete or definitive, and much of 
it reflects our own ideas of what topics may be of interest and 
importance. In most cases all we can do is suggest topics that can be 
further pursued elsewhere and we shall try to indicate some other works 
where this can be done.1 
Axiomatic PC 
In the axiomatic presentation of modal systems in this book our axioms 
have included all valid PC wff. It would have been possible, had our aim 
been to study the propositional calculus, to have presented even PC 
axiomatically. For instance instead of the schema PC we could have used 
a variant of the axiomatic system of Principia Mathematics and replaced 
PC by 
PCA1 (p V p) D p 
PCA2 q D (p V q) 
PCA3 (p V q) D (q V p) 
PCA4 (q D r) D ((p V q) D (p V r)) 
With the rules US and MP the whole of PC may be obtained, and so any 
modal system K + A may be axiomatized by PCA1—PCA4, K, every 
210 


GLIMPSES BEYOND 
member of A, and the rules US, MP and N. 
Natural deduction 
We have defined a modal system as a set of formulae called its theorems. 
There is however another way of looking at a system of logic, and that 
is to think of it as a system of rules whereby a conclusion may be 
deduced from a number of premisses. Where A is a set of premisses and 
a the conclusion, the fact that a may be derived from A in a system S 
can be written as A \-s a. For a system containing the classical 
propositional calculus — and all the modal systems discussed in this book 
do — there is no extra power to be gained by this notation since we may 
define A |-s a to hold iff either A is empty and |-s a, or there are (3^ 
... , (3n G A such that 
h ( 0 , A ... A ft) D a 
Given this definition we have that A (- a D (3 iff A U {a} \- (3. For 
clearly there will be 7,, ... ,yn G A such that 
(i) 
|-s(7i A ... A 7n) D (a D (3) 
iff there are 7 , , . . . , yn, a G A U {a} such that 
(ii) 
f-s (7. A ... A 7 n A a) D (3 
This fact is often called the deduction theorem and it is tempting to read 
the expression A f-saas meaning that there is a proof of a in which the 
members of A are treated as axioms. However, if this is done we need to 
be very careful since a proof in a modal system may appeal to three 
transformation rules, US, MP and N. Of these, only MP applies to 
A \-s a. If S is consistent then we cannot have {p} |-s q, so US cannot 
be allowed; and if S is not Triv or Ver or their intersection we cannot 
have {p} \-s Lp, and so N cannot be allowed. 
Since A |-s a can be defined in terms of theoremhood in S, the 
notation A |-s a has not appeared in earlier chapters. There is however 
an approach to logic in which A |- a is taken as basic. This approach can 
be implemented in a variety of ways, and we shall refer to them all as 
systems of natural deduction. We shall show how natural deduction 
methods may be incorporated into modal logic, but we shall not be 
specific, except by way of illustration, about the particular form a system 
211 


A NEW INTRODUCTION TO MODAL LOGIC 
of natural deduction might take. 
A system of natural deduction is an axiomatic system in which the 
axioms and theorems are no longer single wff, but pairs of the form (A,a) 
in which A is a set of wff and a is a wff. Such a pair is called a sequent. 
Where a sequent (A,a) is a theorem of such an axiom system we write 
A |- a.3 Just which axioms and rules are taken as basic is a matter for 
the system in question. Since we are not interested in axiomatizing the 
propositional calculus, either directly or via natural deduction, we shall 
content ourselves with indicating how the method works in the case of 
PC, and how it may be extended to deal with modal systems. The 
following rules are based on those given by E.J. Lemmon.4 We will 
illustrate the ones he gives for wff involving only D. There is one axiom 
schema: 
A 
(Assumption) {a} \- a for any wff a 
There are three rules. 
Add 
(addition of assumptions) If A \- a and A Q T then T \- a. 
MPP 
(Modus Ponens for natural deduction) If A \- a and A \- a D 
0 then A |-0. 
CP 
(conditional proof) If A U {a} \-(3 then A \-a D (3. 
The PC-tautologies on this account will turn out to be just those wff a 
such that 0 
|- a, where 0 is the symbol for the empty set. As an 
example we show how to establish 
Syll' 
0 
h (q D r) D (fp D q) D (p D r)) 
A 
(1) M 
\-p 
A X Add 
(2) 
{p D qy p} f- p D q 
(1) X Add (2) X MPP (3) 
{p D q, p) 
\-q 
A X Add 
(4) 
{q D r, p D q, p} [- q D r 
(3) X Add (4) X MPP (5) 
{q D r, p D q, p) 
\-r 
(5) X CP 
(6) 
{q D r,p D q) \- p D r 
(6) X CP 
(7) 
{q D r} \- {{p D q) D (p D r)) 
(7) X CP 
V8) 
0 
h (q => r) 
D ((pD q)D (qDr) 
Q.E.D. 
Lemmon in fact sets out proofs a little differently. He would set out this 
212 


GLIMPSES BEYOND 
proof of syll as 
Syll" 
1 
(i) 
P 
1 2 
(2) p D q 
1 2 
(3) 
1 
1 2 4 
(4) 
q D r 
1 2 4 
(5) 
r 
2 4 
(6) pDr 
4 
(7) 
(pDq)D(pD 
r) 
(8) 
(qD r)D((pD 
q) 
A 
A 
1 2MPP 
A 
3 4MPP 
5 CP 
6 CP 
D (p D r)) 
7 CP 
In this way of setting out the proof of syll' the numbers to the left of the 
parentheses serve to identify the wff which make up the set of 
assumptions on which the wff on that line depends. Thus 2 4 refers to the 
set {(2),(4)}, i.e. to {p D q, q D r} and so on. So line (6), say, 
abbreviates the sequent {p D q, q D r} \- p D r which of course is 
exactly the same as line (6) in syll'. A system adequate for deriving all 
and only tautologies (in ~ , D, V , A and =) is given by Lemmon as 
A, Add, MPP and CP, together with the following additional rules: 
MTT 
If A |- a D 0 and A f- ~ 0 then k \- ~ct. 
Al 
If A |- a and A |- 0 then A \- a A 0. 
AE 
UA\-aA0 
then A |- a and A 
\-0. 
VI 
If A |- a then A |- a V 0y and if A (- 0 then A |- a V 0. 
VE 
If A |- a V 0 and A U {a} f- 7 and A U {0} \- y then 
A hT-
RAA 
If A U {a} \- 0 A -/?, then A |- ~a. 
DN 
If A I 
a then A |- a. 
To extend this, or some other adequate system of natural deduction for 
PC, to the language X of modal logic we add a version of US: 
US' If A \- a and A' and a' result from the simultaneous and uniform 
substitution of wff for the variables of A and a, then A' 
[-a'. 
From here on we shall assume our PC basis includes US'. Lemmon's 
rules are given by way of example only since it is not our intention to be 
committed to any particular natural deduction basis for PC. A complete 
set of rules for PC will have the consequence that where A is a set of PC 
213 


A NEW INTRODUCTION TO MODAL LOGIC 
wff and a is a PC wff then A |- a iff every assignment of truth-values 
which makes all members of A true also makes a true. Given such a 
natural deduction basis for PC it may be extended to a system for normal 
modal logic by the addition of one new rule. To formulate this let L+(A) 
be {La:a € A}. Then the rule is 
LR If A |- a then L+(A) \- La. 
Now consider any modal system S and let AS be a set of wff which 
provides an axiomatic basis for S. (I.e. S = K + AS.) We add as extra 
axioms 
NDS 
If a € AS then 0 
f-a. 
What NDS means in natural deduction terms is that any axiom of S may 
be introduced at any stage on the basis of no assumptions. This is in 
contrast to the axiom A which means that any wff whatsoever may be 
introduced, but only on the basis of itself as an assumption. Different 
notations for natural deduction signal the dependence of a wff on a set of 
assumptions in different ways, so the precise terminology according to 
which NDS is presented will depend on which method of signalling 
dependence is used. Where S is a system of normal modal logic let NDS 
denote the natural deduction system formed from it in the way described 
above. To avoid confusion in what follows we shall write |-NDS to 
indicate the |- defined by the basis of NDS. We shall write |-s as usual 
to indicate theoremhood in S, and A |-s a to mean that either |-s a or 
there exist /?,, ... , (3n E A such that 
(i) 
h(ft 
A .» A « 
3«. 
Our aim is to show A |-NDS a iff A |-s a. We shall prove this in each 
direction. 
THEOREM 12.1 If A |-NDS a then A f-s a. 
We shall prove this by induction on the proof of sequents in NDS. Say 
that a sequent A \-uDS a satisfies \-s iff A \-s a. We show that any 
axiomatic sequent, i.e. instance of A or AS, satisfies |-s, and that if a set 
of sequents satisfies |-s then so does any sequent obtainable from them 
by an application of the transformation rules of NDS. For A we need to 
214 


GLIMPSES BEYOND 
show that {a} \-s a. Since a D a is a PC-tautology we have, by PC and 
US, \-s a D a and so {a} \-s a. For AS we note that if a is an axiom 
of S then |-s a and so 0 
(-s a. We now turn to the transformation rules 
of NDS. For Add if A Q V and there are 0„ ... , (3n G A such that (i) 
obtains then there are /?,, ... , /?n € T such that (i) obtains and so T \-
a. We noted on p. 211 that if A \-s a and A \-s a D (3 then A |-s /?, 
and that if A U {a} \-s /? then A |-s a D j3. In a similar way we may 
show that any new sequents obtained by application of the other PC rules 
from sequents which satisfy |-s must themselves satisfy |-s. 
For LR suppose that A \-s a. Then (i) holds. So as in the proof of 
lemma 6.4 on p. 117 we have 
(ii) 
h PA A ... A L0J D La 
and so L+(A) |-s La. This proves theorem 12.1. 
THEOREM 12.2 If A \-s a then A f-NDS a. 
It will be sufficient to prove the following lemma: 
LEMMA 12.3 If |-s a then 0 
|-NDS a. 
We first show that theorem 12.2 follows from lemma 12.3 and then we 
shall prove lemma 12.3. Assume lemma 12.3 and suppose that A |-s a. 
Then there are /?,, ... ,(3n G A such that (i) holds. So 
(iii) Kft 3 WH.:a)...) 
so by lemma 12.3 
(iv) 0 
[-NDS01 ^ (."(ft => «)...) 
so by repeated applications of CP 
(v) 
{/J„ 
... ,/?„} 
K D S « . 
But { f t , . . . J j Q A and so by Add, A \-ms a. 
Proof of lemma 12.3: 
The proof is by induction on the proof of a in S. If a is a PC-tautology 
215 


A NEW INTRODUCTION TO MODAL LOGIC 
then, since we are assuming that the natural deduction rules are complete 
for PC we have 0 
\-NDS a. If a € AS then 0 f-NDS a by NDS. For K 
proceed as follows: 
A x Add 
(1) 
{p,pDq} 
\-p 
A x Add 
(2) 
{p,pDq} 
\-p D q 
(1) (2) x MPP (3) 
{p,pDq} 
\-q 
(3) x LR 
(4) 
{Lp,L(p D q)} 
\-Lq 
(4) x CP 
(5) 
{L{p Dq)} 
\-Lp 
DLq 
(5) X CP 
(6) 
0 
\-L(p 
D q) D (Lp DLq) 
US obviously follows from US'. For N if 0 
\^m 
a then, by LR, 
L +(0) r-Nos La; but L +(0) = 0 . For MP if 0 
|~NDS « and 0 |-NDS 
a D (3 then, by MPP 0 
|-NDS (3. This proves lemma 12.3, and therefore 
theorem 12.2. 
In this natural deduction formulation of modal logic we have achieved 
generality at a cost. For in every case the natural deduction rule 
corresponding to a proper axiom a of S, is simply 0 
|- a. In some 
cases this rule may be replaced with one which looks more like a regular 
kind of natural deduction rule. If a special axiom of S has the form a D 
(3 then we may add either the axiomatic sequent 
or the rule 
If A \- a then A \-(3. 
So, for instance, T could be axiomatized by adding {La} \- a or 
If A |- La then A \- a. 
Other possible natural deduction bases are not so predictable from the 
axioms. For instance S4 can be axiomatized by adding to T the following 
rule and omitting LR. 
NDS4 IfL+(A) |-« t h e nL +(A) 
[-La. 
(K4 can be axiomatized by adding NDS4 to K, keeping LR.) 
If we define M+(A) to be {Ma: a G A}, then B may be obtained by 
216 


GLIMPSES BEYOND 
adding to T: 
NDB 
IfM+(A) |-a then A 
[-La. 
S5 may be obtained by adding to T the following rule and omitting LR: 
NDS5 If A \-a then A [- La provided every variable in every member 
of A is inside the scope of a modal operator. 
Multiply modal logics 
All the systems so far considered in this book have involved only one 
(primitive) necessity operator. It is possible to have logics which involve 
more than one. A language i£k of multi-modal (propositional) logic 
contains a family of operators L,, ... , Lk, with the formation rules being 
extended so that if a is a wff then so is Lna for each Ln (n < k). A frame 
for a multi-modal logic consists of a pair (W,R) where W is a set (of 
worlds) and R is a function from a natural number n < k to a relation Rn 
between members of W. A model based on (W,R) is a triple (W,R,V) in 
which everything is as for ordinary modal logic except that for Ln we 
have 
[VLJ 
V(Lna,w) = 1 if V(a,w) = 1 for every w' such that wB^w', and 
0 otherwise. 
Obviously Mna may be defined as ~ Ln~a. 
In any system of multi-modal logic we have the result that where a is 
a theorem of K in ordinary modal logic and a„ results from a by the 
replacement of every L by Ln, then a„ is valid in every frame. We let Kk 
denote the system defined as any collection of wff of !£k which contains 
every PC-tautology, every instance for n < k of, 
K„ 
LR(p D q)D 
(Lj> D Lnq) 
and is closed under US, MP and Nn ( |- a -* \- Lna) for every n < k. 
For every such system we may define, in the usual way, a canonical 
model by letting wR^' iff for every wff a, if Lna € w then a G w'. 
The canonical model will characterize the system in question for the same 
reasons as in the ordinary case. So much is relatively unexciting. The 
interest in multi-modal logics comes when we have relations between 
different necessity operators. For instance we might have a necessity 
217 


A NEW INTRODUCTION TO MODAL LOGIC 
operator Ll9 say, which is stronger than L2 in the sense that Lj? D L^p. 
The canonical model for such a system would obey the restriction that for 
all w, w' G W, if wR,w' then wR2w'. 
One particularly important class of multi-modal systems is the class of 
tense logics.5 A tense logic has two operators, Lx and L2, where L, means 
'it always will be the case that' and L2 means 'it always has been the case 
that'. In frames for a tense logic Rj and R2 are so related that one is the 
converse of the other, i.e. wRjW' iff w'R2w. Alternatively we may think 
of a frame for tense logic as the same as for ordinary modal logic, a pair 
(W,R) where R is just a relation, and in a model (W,R,V) based on 
(W,R) we have 
[VL,TL] 
V(L,a,w) = 1 if V(a,w') = 1 for all w' such that wRw' and 
0 otherwise. 
[VL2TL] V(L2a,w) = 1 iff V(a,w') = 1 for every w' such that w'Rw 
and 0 otherwise. 
(In a tense logic L, and L2 are often written G and H with their possibility 
versions as P, for ~ / / ~ , and F, for ~G~.) 
To guarantee that R2 is the converse of Rt we need the axioms 
TL1 ~p D L, -Ltf 
TL2 ~p D L2~Lj9 
It is not hard to see that TL1 and TL2 are valid in every model satisfying 
[VLjTL] and [VL2TL]. Further, in the canonical model for any system 
containing TL1, one may prove that if wRjw' then w'R2w, and for any 
system containing TL2 if wR2w' then w'RjW. We shall prove the former. 
Suppose that in the canonical model (i) wRjw' but (ii) not w'R2w. From 
(ii) there is a wff a such thatL2a G w' but a £ w. So — a G w and so, 
by TL1, LX~L2OL G w. So by (i) ~L2a G w' making w' inconsistent. 
The proof of the case for TL2 is exactly analogous. 
An interesting class of temporal logics are those called omnitemporal 
logics. These are ordinary modal logics in which the rule for L is 
[VLO] V(La,w) = 1 iff V(a,w') = 1 for every w' such that either 
wRw' or w'Rw or w = w'. 
218 


GLIMPSES BEYOND 
L interpreted by [VLO] means 'it was, is now, and always will be the 
case that'. One can equally describe it as governed by its own 
accessibility relation R+ where wR+w' iff wRw' or w = w' or w'Rw. If 
time is linear in both directions then the appropriate omnitemporal logic 
is S5. If no conditions are imposed on R the correct logic is B. If R is 
transitive it is still B. An interesting case is where R is linear in the past 
but allowed to branch in the future. Then the correct logic6 is B + 
Lp D (Mq D L(Lp V Mq)) 
Tense logic is a whole topic in itself and is beyond the scope of this 
book. 
The expressive power of multi-modal logics 
From the point of view of modal logic one of the interesting features of 
multi-modal systems is their expressive power. In one recent study Lloyd 
Humberstone7 discusses logics where R2 is the complement of R, in the 
sense that wR2n>' iff not vvRjw'. The minimal logic of such frames, i.e. 
the system determined by the class of all frames (W,R) in which R2 is the 
complement of R,, may be axiomatized as follows. Define an operator • 
as 
Da =df (L{a A L2a) 
Now add to K2 all instances of the S5 axioms for • . I.e. 
Up Dp 
-Up D n~Up 
This system is called K~. As an example of the extra expressive power 
of bi-modal logic we recall from p. 176 that there is no wff of ordinary 
modal logic which, when added to K, imposes irreflexiveness on a frame. 
When we move to K~, however, the situation is different. We may think 
of a frame for K~ either as a frame with two relations or alternatively as 
a frame in which L2 has a non-standard evaluation, 
[VL~] V(L2a,w) = 1 iff V(a,w') = 1 for every w' G W such that not 
wRw'. 
Now if we add to K~ the axiom 
219 


A NEW INTRODUCTION TO MODAL LOGIC 
T~ 
L2P D p 
We can see that, just as T imposed reflexiveness on R, T~ imposes it on 
R2. But wR2w' iff not wR,w\ So if R2 is reflexive, R, is irreflexive. 
Using [VL~] this means that R is irreflexive. Similarly asymmetry can be 
expressed by p D L^Mtf and intransitivity by L-p D LJL$. 
Propositional symbols 
Another way of increasing the expressive power of propositional modal 
logic is to add new propositional symbols. An example of this is 
connected with the fact noted on p. 187 that there is no modal wff which 
can define the class of frames in which every world can see a reflexive 
world. Valentin Goranko suggests adding a symbol loop such that 
V(loop,w) = 1 iff vvRw.8 Obviously Mloop will be valid in a frame iff 
every world can see a reflexive world. 
A second example of a propositional symbol is a special kind of 
variable. Patrick Blackburn investigates a class of propositional symbols 
he calls nominate.9 Where n is a symbol of this kind the rule is that in 
every model there is some w such that 
V(/i,w') = 1 iff w = w' 
This means that a nominal is true in exactly one world. It is easy to see 
that n D L~n, where n is a nominal, is valid on a frame iff that frame 
is irreflexive. 
Dynamic logic 
In the presentation of multiply modal logics we have assumed that the 
necessity operators L,, L2, ... etc. are indexed by the natural numbers. 
Another way of indexing them is suggested by a possible interpretation of 
modal logic in computer science. In this interpretation the 'worlds' are 
states in the running of a program. If TT is a computer program then [7r]a 
means that after program TT has been run a will be true. If w is any 
'world' then wRTw' means that state w' results from the running of 
program TT. This interpretation of modal logic is called dynamic logic.10 
What gives dynamic logic its interest is the possibility of combining 
simple programs to get more complex ones. Thus if 7r, and ir2 are two 
programs then the expression iri'tTr2 refers to the program 'first do irl and 
then do ir2, and [7r,;7rja means that a will be true if this is done. The 
relation corresponding to [TIJTTJ may be defined to hold between w and 
220 


GLIMPSES BEYOND 
w' iff lu(wRV{u A wR^vv'). 
Other complex programs include: 
irx U 7r2: 'do either 7T, or 7r2' (its relation is RTi U R ) 
7r*: 
'do 7r finitely many times' (3n wR>>') 
[a?]/?: 
'/? is true provided a is' (wR[al]w' iff w = w' and V(a,w) 
= 1) 
Other constructs may be introduced by definition. 
Goldblatt shows that a system he calls PDL (propositional dynamic 
logic) is complete with respect to this interpretation.11 Using 7r,, 7r2, ... 
etc., as schematic letters for simple or complex programs PDL may be 
specified as the smallest normal multi-modal logic containing 
Comp [7Ti;7r2]/? = 
[ir^lir^ 
Union [TT1 U 7rJ/? = ([7^]/? A [irjp) 
Test 
[al]p = (a D p) 
Mix 
[7r*]p D (p A [ir][ir*]p) 
Ind 
[TT*](P D Wp) 
D (p 3 [7r*]p) 
Neighbourhood semantics 
In this section we look at the most general kind of possible-worlds 
semantics compatible with keeping the classical truth-table semantics for 
the truth-functional operators. 
The idea is based on that of the 'truth set' of a formula. In any model 
we can define |a| as {w G W: V(a,w) = 1}. Now in evaluating La in 
a world w all the input that we require is to know which set of worlds 
forms the truth set of a. Whatever L means, what it has to do is to 
declare La true at w for some truth sets and false for others. So the 
meaning of L must specify which sets of worlds form acceptable truth sets 
in world w. These sets of worlds are called the neighbourhoods12 of w, 
and a neighbourhood frame for a language i£ of (mono-) modal 
propositional logic is a pair (W,R) in which W is a set (of worlds) and R 
is a 'neighbourhood relation'. A neighbourhood relation is a relation 
between a world w and a subset A of W and A is a neighbourhood of w 
iff wRA. The rule for L in such a frame is 
[VLfl 
V(La,w) = 1 iffwR|a| 
221 


A NEW INTRODUCTION TO MODAL LOGIC 
A frame of the kind assumed in the rest of this book in which R is a 
relation between worlds is often called a relational frame, and it is not 
difficult to see that every relational frame is a special case of a 
neighbourhood frame. To be precise, a relational frame is a 
neighbourhood frame in which for every w E W there is a set B of those 
and only those worlds which are accessible to w (i.e. B is the set of 
worlds w can 'see') and wRA iff B Q A. What this means is that a's 
truth set is a neighbourhood of w iff it contains all the worlds accessible 
from W, which is of course precisely what the truth of La in a relational 
frame amounts to. 
As an example of a neighbourhood frame which is not a relational 
frame let W consist of the natural numbers and let the neighbourhoods of 
all worlds be the set of odd numbers or the set of even numbers. Then we 
can easily falsify such K-theorems as Lp D L(p D p) — by making, say, 
p true just at the odd numbers. 
The logic characterized by the class of all neighbourhood frames is 
very simple. Its axioms are the valid PC-wff and its rules are US, MP 
and the single rule 
RE 
\-a = (3^ \-La = L(3 
This rule will also be a rule of all logics determined by any class of 
neighbourhood frames provided validity is defined as truth in every world 
in every model based on that frame.13 
Neighbourhood frames give the appropriate generality for operators 
whose semantics are provided by a non-standard evaluation rule. For 
instance Humberstone14 discusses the logic of an operator whose semantics 
is 
V(Lcx,w) = 1 iff, for every w' € W, V(a,w') = 1 iff wRw' 
(where R is now an ordinary accessibility relation). He interprets L to 
mean 'a is true in all and only accessible worlds'. Here A is a 
neighbourhood of w iff A = {wf: wRw'}. 
Another interesting class of logics which can be studied by 
neighbourhood frames are logics which have been called 'non-
aggregative' logics.15 In these logics the accessibility relation R is 
replaced by an n-place relation for some n > 1. For 3 the evaluation rule 
is: 
222 


GLIMPSES BEYOND 
V(La,w) = 1 iff for every w', w" such that wRw'w", V(a,w') = 1 or 
V(a,w") = 1. 
In such logics K, and therefore K2 ((Lp A Lq) D L(p A q)) does not 
hold, although 
K2' (L/> A Lq A Lr) D L((p A q) V (p A r) V (q A r)) 
Along with PC, US, MP and the rule R* ( f- a D 0, |- La D 10), K2' 
provides an axiomatization for this logic. The frames for this logic can be 
thought of as neighbourhood frames in which A is a neighbourhood of w 
iff for every w' and w" G W such that wRw'w", either w' G A or w" 
G A. The case involving a three-place relation can be generalized to any 
n. 
Neighbourhood semantics can of course be devised for systems with 
more than one necessity operator, and even for systems with operators 
taking more than one argument. A philosophically important example here 
is the logic of counterfactuals as developed in the late 60s and early 70s. 
We shall present a version of David Lewis's semantics.16 Counterfactual 
logic is based on a dyadic operator O-* where a D-* 0 is to mean that if 
a were to be the case then 0 would be the case. Lewis's idea is that, 
given a possible world w, some worlds are closer to w than others. If we 
write w' <w w" to mean that w' is closer to w than w" is then the 
semantics for D-> will be that a D-* 0 is to be true in w iff either a is 
not true at any world or there is a world w' at which a and 0 are both 
true which is closer to w than any world w" at which a is true but 0 is 
not. A counterfactual frame can be described as a neighbourhood frame 
in the following way. Since Q-» is dyadic its neighbourhood relation R 
will relate worlds to pairs (A,B) where A Q W and B Q W. The 
standard rule for dyadic operators will of course be 
V(a D-*0,w) = 1 iffwR(|cx|,|0|) 
A frame (W,R) will be a counterfactual frame iff it is based on a nearness 
relation < in such a way that wR(A,B) iff either 
(a) 
A = 0 or 
(b) 
There is some w' such that w' € A O B and for every w", if 
w" G A PI -Bthenvv' 
<ww". 
223 


A NEW INTRODUCTION TO MODAL LOGIC 
Which counterfactual logic you get will depend on what kind of conditions 
you put on < . For instance, under the plausible assumption that the 
closest world to w is w itself you get a frame which validates the wff 
p D ((p O * q) m q) 
By contrast, on any plausible account of nearness, many wff which are 
valid for D or for -3 fail for Q-*. For instance in standard systems of 
counterfactual logic neither 
((pHh>q) A (qD->r)) D (p\3+ r) nor 
(pC^q) 
D (~qB-> 
~p) 
are valid. 
A logic may be said to be neighbourhood complete if it is characterized 
by a class of neighbourhood frames. It is known that there are normal 
incomplete modal logics which are neighbourhood complete and others 
which are not neighbourhood complete.17 
Intermediate logics 
In Chapter 11 we introduced the symbol -3 in such a way that a -3 jS can 
be defined as L(a D /?). Many valid PC-wff become invalid if D is 
replaced by -3, and so one could regard a propositional logic in which D 
is replaced by -3 as a weaker version of PC. Indeed one might even 
argue that Lewis thought of it in just this way. Other versions of 
propositional logic can be studied like this, and they are often called 
intermediate logics, the principal example being intuitionistic logic. The 
intuitionistic propositional calculus IC treats V and A as in classical PC, 
but interprets negation and implication differently. We shall use "» for 
intuitionistic negation and -* for intuitionistic implication. A set of axioms 
for IC is the following:18 
HI p -* (p A p) 
H2 
(p A q) -* (q A p) 
H3 
(p -» q) -> ((p A r) -* (q A r)) 
H4 
«p ^ q) A (q -» r)) ^ (p -» r) 
H5 
p-+(q+p) 
H6 
(p A 
(p^q))-»q 
H7 p-+(p 
V q) 
224 


GLIMPSES BEYOND 
H8 
(p V q) + {q V p) 
H9 
((p -* r) A (q -* r)) - «p V <?) -* r) 
H10 
^p-^ip^q) 
Hll ((p -* ?) A (p -» -iq)) -* •"•/? 
The most notable omissions from IC are p V -»/? and -> -»/> -* /?. 
(However, /? -> -> ->/? is a theorem.) 
To understand IC we bear in mind that it is intended to formalize 
intuitionistic mathematics in which truth means established truth and ~>a 
means that a has been established to be false. Thus, since a may neither 
be established to be true, nor established to be false it is not surprising 
that a V ~>a should fail to be valid. IC can be interpreted in modal logic 
by the definitions: 
Def ->: 
~>a =df L ~ a 
Def->: 
a - » 0 =d{L(a D 0) 
With these definitions IC becomes a subsystem of S4 in the sense that, 
provided every variable p is replaced by Lp, then any wff will be a 
theorem of IC iff the result of such replacements (using Def -> and Def 
-*) is a theorem of S4. 
The standard semantics for S4 can then be used to provide a direct 
interpretation for IC, in which, if V(p,w) = 1 then V(/?,w') = 1 for 
every w' such that wRw', V(-<a,w) = 1 iff V(a,w') = 0 for every w' 
such that wRw', and V(a -> /J,w) = 1 iff for every w' such that wRw', 
either V(a,w') = 0 or V(0,w') = 1. 
If we interpret the language of IC in S5 rather than S4 it turns out that 
we get classical PC. If we interpret it in systems between S5 and S4 we 
can get extensions of IC. Thus, in S4.3 (p -> q) V (q^>p) becomes 
valid.19 Such intermediate logics form an interesting application of modal 
logic. 
'Syntactical' approaches to modality 
This book has been concerned to present the semantics of modal logic by 
means of possible worlds. That technique has proved by far the most 
valuable in terms of the generality of its applicability. It is however not 
the only way of studying modal logic semantically. Many philosophers are 
suspicious of the idea of a possible world when thought of as an 
alternative to our actual world. While such suspicions give rise to 
important debates in metaphysics we have been at pains to insist that from 
225 


A NEW INTRODUCTION TO MODAL LOGIC 
the point of view of modal logic it does not in the least matter what the 
worlds are. For instance in the canonical model of a normal modal system 
the worlds are maximal consistent sets of wff. Seen in this way possible-
worlds semantics is the most neutral of semantic frameworks since many 
'alternatives' to it are better seen as implementations of it, provided by 
giving an account of what possible worlds might be held really to be. 
However, even a semantics which might in the end turn out to be of this 
form can be worth looking at to see just how the implementation works. 
One very powerful idea behind modal logic is the connection between 
necessity and validity. The rule of necessitation makes it clear that if a 
is valid then this is necessarily so, since La is then also valid. The 
version of this approach that we shall discuss is a generalization of one 
presented by Brian Skyrms,20 though the idea of treating modality 
'syntactically' by thinking of necessity as a property of wff has a longer 
history. However, we have to be careful since validity is a property of wff 
while necessity is a property of propositions. The importance of this 
distinction may be easily seen. The variable p is certainly not valid. So 
if we identified validity with necessity it would seem that Lp should 
always be false, or that ~ Lp should always be true. But obviously if 
—Lp were a theorem of any normal modal system we would have, by 
US, ~L(p D p) and since L(p D p) is a theorem of every normal system 
the resulting system would be inconsistent. The idea underlying Skyrms's 
account is this. Although the variable/? is not valid in the sense that it is 
not true in every PC model, yet it might well be true in a more restricted 
class of models. In the present section we shall use the notion of an 
extensional model. An extensional model is simply an assignment of truth-
values to the wff of propositional modal logic which respects the standard 
truth-tables; specifically it is an assignment m such that 
(i) m( ~ a) = 1 if m(a) = 0 and 0 otherwise; 
(ii) m(a V (3) = 1 if m(a) = 1 or m(ff) = 1 and 0 otherwise. 
We say that a family M of extensional models is a modal family iff there 
is a relation R* between members of M such that for m G M, for every 
wff a of ^ , 
(iii) m(La) = 1 iff m'(a) = 1 for every m' E M such thatmR*m'. 
It should not be difficult to see that every 'ordinary' model (W,R,V) 
226 


GLIMPSES BEYOND 
which contains no duplicates (in the sense described on p. 165) may be 
represented by a modal family M in which each member m of M can be 
indexed by a world w in such a way that mw(a) = V(a,w). And of course 
every modal family may be considered to be a model (W,R,V) in such a 
way that W is simply M, R is R*, and V(a,m) = m(a). 
In the case of S5 (which is the system that Skyrms considered) we can 
in fact do better. Recall that an S5-model may be considered to be simply 
a pair (W, V) in which W is a set of worlds and [VL] is amended to 
[VLS5] V(La,w) = 1 iff V(a,w') = 1 for every w' G W. 
[VLS5] has the consequence that any wff of the form La is either true 
throughout the model or false throughout the model. And this means that 
any two worlds which coincide on the values to the variables, coincide on 
the values to all wff. So the extensional models in the corresponding 
modal family in this case need give values only to the variables. This 
procedure will not work in general. Consider for instance a model in 
which there are two worlds, wx and w2, where w, is a dead end while w2 
is not. In such a case a model in which every variable has the same value 
in H>! as in w2, will still not give every wff the same value in both these 
worlds since Lip A ~p) will be true in w, but false in w2. 
Another 'syntactic' interpretation is to think of L as meaning 'is a 
theorem'. Skyrms shows how to give an interpretation for S4 in which L 
has this meaning.21 Care must be taken here too since we have already 
observed (p. 140) that if 'provable' means 'provable in the language of 
arithmetic' the correct logic is KW, and if we add the wff Lp D p as an 
extra axiom to KW, by N we have L(Lp D p) and so by W, Lp and thus 
by Lp Dp we have p and the inconsistent system.22 
Probabilistic semantics 
Another alternative to possible-worlds semantics involves probability 
theory. Instead of assigning truth-values in possible worlds a probability 
function Pr assigns values from the interval of real numbers from 0 to 1 
(including 0 and 1 themselves as limiting cases). Where Pr(a,/J) = r is 
read as 'the probability of a given (3 is r', a probability function, for PC, 
may be defined as satisfying the following:23 
PR1 0 < Pr(«,/J) < 1 
PR2 Pr(a,a) = 1 
227 


A NEW INTRODUCTION TO MODAL LOGIC 
PR3 If Pr(0,S) = Pr(7,6) for every wff 6 then Pr(a,0) = Pr(a,y) for 
every wff a. 
PR4 If there is at least one wff 7 such that Pr(7,/J) ?* 1, then for every 
wff a, Pr(~a,/3) = 1 - Pr(a,0). 
PR5 Pr(a A /?,>) = Pr(a,0 A 7) X Pr(0,7) 
PR6 Pr(a A 0,7) = Pr(0 A a,T) 
A wff a is called probabilistically valid iff Pr(a,/J) = 1 for every wff /?. 
The probabilistically valid PC-wff are precisely the PC-valid wff. Charles 
Morgan24 extends this account to modal logic by adding the following 
conditions: 
PR7 If Pr(a,7) < ?r((3,y) for every wff 7 then Pr(La,7) < Pr(L0,7) for 
every wff 7. 
PR8 Pr(L(a A P),y) = Pr(La A L(3,y) 
PR9 There is at least one wff a such that Pr(La,/3) = 1 for every wff (3. 
It is not difficult to see that these conditions mimic the axiomatic basis of 
K, and Morgan is able to provide a soundness and completeness result. 
Other systems may be obtained by adding conditions which correspond 
analogously with their axioms. Thus a probabilistic semantics for T is 
obtained by adding 
PR10 
Pr(La,0) < Pr(a,0) 
and for S4 
PR11 
Pr(La,jS) < ?r(LLa,(3) 
and so on. 
Morgan's is not the only way to present a probabilistic semantics for 
modal logic. For those who prefer a semantics which does more than 
simply mimic the axioms. Charles Cross25 has a semantics for modal logic 
in which the role played by possible worlds in standard treatments is 
played by probability functions. Using an accessibility relation between 
probability functions, and requiring that the value of La conditional on /J 
for a given probability function be less than the value of a conditional on 
(3 for all accessible probability functions, Cross is able to prove soundness 
for T, B, S4 and S5. The use of degenerate functions whose values are 
0 or 1 enables standard completeness results to apply to his semantics. 
228 


GLIMPSES BEYOND 
Algebraic semantics 
An algebra is a set of 'elements' together with operations on them. An 
especially important kind of algebra is called a Boolean Algebra. The 
most intuitive way to link Boolean Algebra with modal logic is to think 
of the elements as sets of worlds and the operations as intersection, union 
and complementation. The accessibility relation R then defines a further 
operation O on sets of worlds such that where A is a set of worlds, O(A) 
is the set {w: Ww'(wRw' D w' € A)}, i.e. 0(A) is the set of worlds in 
which A is 'necessary' — and w is such a world iff every world 
accessible to it is in A. In speaking this way we are thinking of A as the 
truth set of a wff.26 
The study of frames and models as algebraic structures provides an 
insightful way of looking at modal logic for those who want to link it with 
mathematics. Such a study is beyond the scope of the present book.27 
Exercises — 12 
12.1 
Prove that A \-a in NDS4, NDB and NDS5 iff A \-S4 a, h, a 
and |-S5 a respectively. 
12.2 
Provide an axiomatization for tense logic in which time is 
(a) 
connected in both directions, 
(b) 
connected in the past but branching in the future. 
12.3 
Prove that B is omnitemporally characterized by frames in which 
time is transitive but permitted to branch in both directions. 
12.4 
Prove that the system axiomatized by PC, US, MP and RE is 
characterized by the class of all neighbourhood frames. 
12.5 
(open problem) Is KH complete for neighbourhood frames? 
12.6 
Show that in standard systems of counterfactual logic neither 
((p Q* q) A (q D^ r)) D (p O 
r) 
nor 
is valid. 
12.7 
Show that the following are valid in the intermediate logics based 
on the following extensions of S4: 
->p V ->->/? 
[S4.2] 
229 


A NEW INTRODUCTION TO MODAL LOGIC 
(P^q)V(g-»p) 
[S4.3] 
All PC-tautologies 
[S5] 
Notes 
1 A standard reference work for most topics mentioned in this chapter may be 
found in Gabbay and Guenthner 1984. 
2 Whitehead and Russell 1910 have a basis consisting of the four axioms listed in 
the text together with one subsequently found to be derivable from the others. The 
basis given here was assumed for modal logic in Hughes and Cresswell 1968. 
3 Strictly speaking it might be more correct to write |- (A,a), since the sequent 
itself is the pair (A,a). However we shall frequently use the notation A \- a to 
refer to the sequent itself rather than to the fact that the sequent is a theorem. Our 
development is based on Lemmon 1965b but natural deduction methods go back 
to Gentzen 1934 and are found in many logic texts. One of the earliest natural 
deduction systems for modal logic is in Fitch 1952, though Fitch did not aim for 
or achieve the generality we assume here. For a survey of natural deduction 
methods in modal logic see Fitting 1983. Other discussion occurs in Hawthorn 
1990. We do not make a distinction between a system of natural deduction and 
a sequent calculus, since we regard the latter as a way of making the former 
precise and explicit. Different systems of natural deduction are in effect different 
notations for keeping track of the premisses (i.e. the members of A) on which the 
wff a depends. Some systems use vertical lines starting under a wff to be assumed 
as part of A. Others box subproofs, and so on, but what they all have in common 
is that they are establishing a relation between a wff and a set of wff. 
4 Lemmon 1965b, pp. 9-15. Lemmon does not explicitly state the rule Add but 
it is in fact required. (Or else A and Add can be combined into a single axiom 
A+: If a e A then A \- a.) 
5 An introduction to tense logic is found in Burgess 1984. 
6 See Hughes 1975 and 1982. Logics of this kind are there called 'omnitemporal 
logic'. 
7 Humberstone 1983. Such logics are also discussed in Goranko 1990, and the 
axiom system we provide in the text is his. 
8 loop is found on p. 102f. of Goranko 1990. 
9 Blackburn 1993. Bull 1970 had already introduced the same idea for tense logic. 
See also Gargov and Goranko 1993. 
10 This section summarizes material presented at greater length in Chapter 10 of 
Goldblatt 1987. Further references to the literature may be found in that volume. 
11 It is also possible to develop dynamic predicate logic. For an introductory 
survey see Part III of Goldblatt 1987. 
12 For some remarks on the history of neighbourhood semantics see Segerberg 
1971, pp. 72f. 
13 If, as in S2 and S3 as described on p. 201 we define validity as truth only in 
every 'normal' world (however this may be defined) then RE may no longer hold. 
230 


GLIMPSES BEYOND 
(We observed on p. 46 that a rule may hold in a system but may fail in an 
extension of that system.) The semantics for SI given in Cresswell 1995a uses an 
accessibility relation for normal worlds, but for non-normal worlds uses an 
arbitrary neighbourhood relation R* satisfying the restriction that if wR*A and 
wR*B then (i) w E A and w € B and (ii) A U B *• W. 
14 Humberstone 1987. The operator in this paper is a sort of fusion of the 
operators that appeared in Humberstone 1983. 
15 Schotch and Jennings 1980. 
16 Lewis 1973. The same idea is also found in Stalnaker 1968 and Aqvist 1973. 
17 See Bull and Segerberg 1984, p. 72 and the references listed there. (Also 
Gerson 1975 and Gabbay 1975.) 
18 These axioms are given in Heyting 1930. The connection between IC and S4 
seems to have first been noticed in Godel 1933 and is stated explicitly in 
McKinsey and Tarski 1948. A connection of a different kind between modal logic 
and IC is noted in Becker 1930 (see p. 70). The intuitionist predicate calculus is 
studied in Kripke 1965a. See also Fitting 1983. A survey of intuitionistic logic is 
found in van Dalen 1986. 
19 See Dummett and Lemmon 1959. 
20 Skyrms 1978. Skyrms's ideas are generalized to propositional languages with 
propositional operators having neighbourhood semantics in Cresswell 1985. The 
idea that a necessary proposition is one which has the form of a valid wff is found 
in McKinsey 1945. Kripke 1959 for S5 predicate logic treats worlds as value 
assignments. Further development of Skyrms's approach, including a discussion 
of how it works in modal predicate logic, may be found in Schweizer 1992, 1993 
and elsewhere. 
21 Skyrms 1978, pp. 375-382. 
22 Montague 1963 shows that when L is a predicate applicable to sentences of 
formal arithmetic then Lp D p cannot be consistently added to any normal modal 
logic. (In fact even SI is inconsistent.) Skyrms 1978, pp. 382-387, points out that 
Montague's argument need not apply to weaker languages. 
23 We have used the definition presented in Morgan 1982, p. 445. Morgan takes 
— and A as the basic PC-operators and we have followed him in this. 
24 Morgan 1982, p. 445f. 
25 Cross 1993. 
26 An early algebraic study of modal logic is found in McKinsey 1941. See also 
McKinsey and Tarski 1944 and Jonsson and Tarski 1951, and Lemmon 1960a. 
A fuller survey is found in Lemmon 1966a and 1966b, and a more introductory 
survey in Chapter 17 of Hughes and Cresswell 1968. 
27 A modal algebra turns out to look more like the general frames described on 
p. 167 since not every set of worlds need be an element. 
231 


Part III 
