<!-- Source: Hughes & Cresswell (1996). A New Introduction to Modal Logic. Routledge. Part III: Modal Predicate Logic (Chapters 13-19, pages 233-408). -->

MODAL 
PREDICATE LOGIC 


13 
THE LOWER PREDICATE 
CALCULUS 
In this part of the book we shall examine what happens when modal logic 
is combined with the Lower Predicate Calculus. We shall assume that 
readers are familiar with the ordinary non-modal LPC (as we shall refer 
to it) but we shall make our development self-contained, and explain all 
our terminology as we proceed.1 In essence the predicate calculus extends 
the propositional calculus by the addition of symbols which enable us to 
speak about 'all' or 'some' things which satisfy a certain condition. These 
symbols are called quantifiers. The symbol V is used to say that 
everything satisfies a certain condition and is called the universal 
quantifier, while the symbol 3 is used to say that there exists something 
which satisfies a certain condition and is called the existential quantifier. 
Each can be defined in terms of the other, and we shall set out a version 
of LPC which takes V as primitive. 
Primitive symbols and formation rules of non-modal LPC 
In what follows we shall have occasion to extend the language of LPC by 
adding extra symbols. We shall therefore define what is to count as a 
language ££ of LPC. Where we have a fixed language in mind we shall 
usually omit explicit reference to X. A language ££ of (non-modal) LPC 
takes as primitive the following symbols. 
(1) 
For each natural number n (> 1) a set (possibly finite but at 
most denumerably infinite) of n-place predicates. We refer to 
these as <£, i/s x> ••• etc. 
235 


A NEW INTRODUCTION TO MODAL LOGIC 
(2) 
A denumerably infinite set of individual variables, which we 
refer to as x, y, zf ••• etc. 
(3) 
The five symbols ~, V , V, (, and). 
The formation rules are these: 
FRl Any sequence of symbols consisting of an n-place predicate followed 
by n (not necessarily distinct) individual variables is a wff. (Such a 
wff is called an atomic wff.) 
FR2 If a is a wff so is — a. 
FR3 If a and (3 are wff so is (a V (3). 
FR4 If a is a wff and x is an individual variable then Wxa is a wff. 
We adopt the definitions of A , D and = used in propositional logic, and 
add the definition 
[Def 3] 
Ixct =df ~VJC~« 
As we said above V and 3 are called quantifiers. More strictly we should 
say that V or 3 followed by a variable is the quantifier since Vx and Vy 
have different meanings. In a wff of the form Vxa, a is said to be the 
scope of the quantifier Vx. An occurrence of a variable x in a wff a (not 
as part of a quantifier) is said to be free or bound in a. If it does not lie 
within the scope of any quantifier which contains x it is said to be free in 
a. Otherwise it is said to be bound in a; and if x is free in a it is said to 
be bound by V* in Vxa. Thus in the wff 
(1) V*(0* V yfry) 
the x occurring immediately after <j> is bound (by the quantifier VJC at the 
beginning) but y is free. Note however that even when we are speaking 
of (1) we say that x is free in (<f>x V \j/y) since no quantifier containing 
x occurs in that expression, though of course x is not free in (1) itself. 
Note also that it is occurrences of variables that are bound or free, and 
that the same variable may occur both bound and free in the same 
formula, as, e.g., x does in Vx<j>x D <j>x. Note thirdly that in a wff like 
VJC(</>JC V Vjti/a) the first occurrence of x is bound by the outermost 
(initial) quantifier, and the second by the innermost quantifier. 
236 


THE LOWER PREDICATE CALCULUS 
In Chapter 17 we shall consider languages of LPC which have 
individual constants and function symbols. For the present we do not have 
these. 
Interpretation 
In order to see how to interpret wff of LPC we shall look at the kind of 
things such a language can be used to say which go beyond the resources 
of PC. Suppose we wanted to express the fact that all cats are animals. 
If we interpret the one-place predicates <j> and \p as, respectively, 'is a cat' 
and 'is an animal' then we can express this fact by the wff 
(1) VJC(^ D i/tf). 
(1) says that for every x, if x is a cat then x is an animal. At least it does 
this on the assumption that Vx means 'for every xy or perhaps 'no matter 
what x may be'. 
If we were to keep the predicate <f> to mean 'is a cat', but re-interpret 
\p to mean 'is black' then we could express the fact that some cats are 
black by the wff 
(2) ixdbx A \px) 
where 3JC may be read as 'there exists an x such that'. If <j> is a two-place 
predicate and is interpreted as 'admires' then we can express 
(3) everyone admires someone 
as 
(4) Vx3ycj>xy. 
(4) allows each person to admire someone different. If (3) is understood 
to imply that there is someone whom everyone admires we would have 
to use 
(5) 3yVx<j>xy. 
In (4) and (5) we have used V and 3 to mean 'everyone' and 'someone'. 
That is to say we have understood ourselves to be restricting the things 
we are speaking about to people. In general, whenever we use quantifiers 
we have in mind what is often called a 'universe of discourse' or in 
technical terms a domain. The quantifiers are then said to range over the 
237 


A NEW INTRODUCTION TO MODAL LOGIC 
domain. This means that they refer to everything or to something from 
the domain in question. So to interpret a wff of LPC we must first specify 
a domain D. 
Given a domain D we must now interpret the predicates. Consider (1). 
If D is a domain which includes animals then some subset of D will be 
those which are cats. If A is the set of those members of the domain 
which are cats, then A will be the interpretation of the predicate <f> when 
<j> means 'is a cat'. And if B is the set of animals in D then B will be the 
interpretation of the predicate \p when \p means 'is an animal'. For a two-
place predicate it is a little more complicated. If <f> means 'admires' then 
we need to consider pairs from the domain. If C is the set of pairs (w,v) 
where u and v are both in D and u admires v, then C will be the 
interpretation of <j> when it means 'admires'. To get a model for a 
language ££ of LPC we form the pair (D,V) where D is any class of 
objects we please, and V is a function such that where <j> is an n-place 
predicate in i£ then V(</>) is a class of n-tuples from D. The idea is that 
(«!, ... ,«n) G V(<£) iff Wj, ... ,wn (in that order) stand in the n-place 
relation which is the meaning of <f>. 
We must now give rules for evaluating wff of i£. In defining (D, V) we 
have made no mention of the individual variables. The reason is this. The 
kind of LPC wff that we are ultimately interested in are those like (1), 
(2), (4) and (5) in which there are no free variables. Such wff are called 
closed wff, or sometimes sentences. The simplest kind of closed wff is a 
wff like 
(6) 
Vx</>x. 
In any interpretation (D,V) (6) will be true if V(<£) = D, and false 
otherwise and this fact does not depend on the value of x. By contrast 
consider a wff with a free variable, say 
(7) 
cj>x. 
Is (7) true or false? Well, it depends on what x is. We could of course 
require V to give values, from D, to the individual variables as well as 
to the predicates. But in obtaining the value of (6) from (7) we need to 
refer to all the possible values x might have. For this reason it is 
convenient to separate the value-assignment to the individual variables 
from the model itself. So where (D,V) is an LPC model we say that fi is 
a value-assignment based on (D,V) provided that, for every variable* in 
238 


THE LOWER PREDICATE CALCULUS 
i£, fi(x) is a member of D. We shall then write 
V » = 1 
to mean that a is true in the model (D,V) when the individual variables 
are given the values assigned them by fi. Thus for atomic wff we have 
[V<£] 
V^x,...^) = 1 if (n(xx), ... ,ii(xj) € V(0) and 0 otherwise. 
What [V</>] means is that </>*,...xn is true, with respect to JU, iff the n-
tuple made up from the individuals \k assigns to xx, ... ,jcn, is in the set of 
n-tuples that V assigns to <f>. For ~ and V the procedure is obvious. 
[V~] 
VM(~a) = 1 if V^a) = 0 and 0 otherwise. 
[VV] 
VM(a V 13) = 1 if either VM(o) = 1 or VM(0) = 1 and 0 
otherwise. 
The complexity comes with the quantifiers. For we want V^Vxa) to be 
true not only when V^(a) = 1, but when Vp(a) = 1 for whatever value 
from D p may assign to x. But we must be careful. For consider the wff 
Vx</>xy. In evaluating this wff with respect to \i we permit p to give any 
value whatsoever to x, but we need to keep the same value for y as /*. 
gives, since y remains free in Vx<j>xy. So we say that p is an x-alternative 
of fi iff for every variable )> except (possibly) x, p(y) = /i(y). We then say 
[VV] 
V^Vjca) = 1 if Vp(a) = 1 for every x-alternative p of /*, and 0 
otherwise. 
By Def 3 this means that we have 
[V3] V/i(3xa) = 1 if there is an jc-alternative p of \x. such that Vp(a) = 1, 
and 0 otherwise. 
A wff a is said to be valid in a model (D,V) iff V^a) = 1 for every 
assignment JX in (D,V) to the individual variables of i£. A wff which is 
valid in every model is said to be universally valid or sometimes LPC-
valid or just plain valid. 
239 


A NEW INTRODUCTION TO MODAL LOGIC 
The principle of replacement 
In order to motivate this important principle of LPC we shall look at 
some examples of LPC-valid wff which depend on the meaning of the 
quantifiers. Consider the wff 
(1) 
Vx<f>x D 4>y. 
(1) expresses the principle that if <f> is true of everything in D then it will 
be true of whatever member of D is assigned to y. Now (1) should be 
expected to hold not only of atomic wff, but also of complex wff. 
Consider 
(2) 
Vx(<j>xx A Ixcpxy) D {<f>yy A lx<j>xy). 
In (2) we notice first that every x free in <f>xx A 3x<j>xy has been replaced 
by y. The x bound by 3JC however has been left alone. (Recall that 
although x cannot be free in Vx(<j>xx A 3x<f>xy) it can be, and is, free in 
(f>xx A 3x<j>xy). Second we notice that the fact thaty already occurs in <j>xx 
A lx<j>xyy does not affect the validity of (2). Readers should convince 
themselves that (2) is indeed valid. The general form of (2) is 
Vl 
Vxa D a\y/x] 
where a\ylx\ is a with y replacing every free x in a. 
This is almost right, but in order to rule out an unwanted instance we 
must impose another restriction. For, suppose <j> means 'is less than'. 
Then the following would appear to be an instance of Vl 
(3) 
Vx3y<j>xy D 3y<j>yy. 
This says that if everything is less than something then something is less 
than itself, and this is false in the domain of natural numbers. 
The problem with (3) is that although x is free in 3y<f>xy, the y that 
replaces it becomes bound. So we must require that a\ylx\ has free y 
where a has free x. Now in 3y<f>xyy the fact that we have a y quantifier is 
accidental in the following sense. 3y<j)xy simply says that x is related by 
<f> to something, and in place of 3y<j>xy we could equally have Izfaz. And 
now there is no problem. For we certainly have as valid 
(4) 
Vx3y</>xy D 3z<f>yz . 
240 


THE LOWER PREDICATE CALCULUS 
^y<j>xy and 3z<l>xz are called bound alphabetic variants. More strictly a and 
/? (in primitive notation) are bound alphabetic variants iff they differ only 
in that a has a wf part Vxy where (3 has VyS and 7 and 6 differ only in 
that 7 has free x where and only where 5 has free y. We then let a[y/x] 
be the result of taking a bound alphabetic variant of a in which there is 
no y quantifier, and then replacing every x free in the resulting variant by 
y. The validity of Vl then follows from the principle of replacement: 
PR 
Let a be any wff, x and y any variables, (D,V) any model for ££, 
and fx any assignment to the variables. Then, where p is just like fx 
except that p(x) = /x(y), Vp(o) = 
V^aly/x]). 
PR is a standard result in non-modal predicate logic. 
The other principle we require is that where fi and p agree on all the 
variables free in a wff a then VM(a) = Vp(a). We can call this the 
principle of agreement, PA. PA has the consequence that where a 
contains no free variables then VM(a) = Vp(a) for every JU, and p. 
Axiomatization 
Our style of axiomatization will differ from that used in Part I in that we 
will not have any rule of uniform substitution. This means that all our 
axioms will be stated as axiom schemata, i.e. general principles to the 
effect that any wff of a certain form is an axiom. Parallel to axiom 
schemata we shall frequently prove theorem schemata. Even in Part I we 
stated PC as a schema which provided infinitely many axioms. For LPC 
we define an LPC substitution-instance of a PC-wff a as any expression 
which results from uniformly replacing every propositional variable in a 
by a wff of i£. The axioms of LPC, for a given language ££ are 
PC 
Any LPC substitution-instance of a valid wff of PC is an axiom of 
LPC. 
Vl 
If a is any wff and x and y any individual variables then 
Vxa D a[y/x] is an axiom of LPC. 
The transformation rules of LPC are first, Modus Ponens. 
MP 
\-a, 
\-a D 0 -* \-(3 
and second 
241 


A NEW INTRODUCTION TO MODAL LOGIC 
V2 
\-a D 0 -* \- a D VJC/3, provided x is not free in a. 
It is routine to prove that every instance of PC and Vl is valid in every 
model, and that MP and V2 preserve validity in a model. (We shall in fact 
go through this proof for the modal extensions of LPC.) From this it 
follows that every LPC theorem is universally valid. 
Some theorems of LPC 
We list here some theorems of LPC (in the form of schemata) and rules 
which will be useful in later developments. We omit proofs, which are in 
any case quite standard. Where a rule is proved here that rule will hold 
in all the modal extensions of LPC which are based on the present 
axiomatization of LPC. a and 0 are any wff and x, y and z any individual 
variables. 
UG 
\-ct-* 
\-Vxa 
VGD 
\- a D (3 -* f- Vxa D V*j3 
UG= 
\- a a p -> |- Vjca = Vx(3 
UGS, in conjunction with the PC principles listed on p. 32, enables the 
proof of a rule of substitution of equivalents: 
Eq 
If \- a = (3 and 7[a] differs from y[fi] only in having a at 0 or 
more places where y[(3] has /?, then (- 7[a] = y[@]. 
RBV 
Vxa = Vy(3 where a and /J differ only in that a has free x where 
and only where 0 has free y. 
Vjca and Vy@ are bound alphabetic variants (see p. 241). RBV shows that 
bound alphabetic variants are equivalent, and so by Eq we may replace 
them in any wff, and the result of the replacement will give a wff 
provably equivalent to the original. Such replacement is often called 
relettering of bound variables. 
LPC1 
VJC(« D (3) D (Vxa 
D 
Vx0) 
LPC2 Vx(a D ff) D (a D Vx(l) provided x is not free in a 
LPC3 3;y(a[y/;c] D Vjca) provided y is not free in V*a. 
QI 
~ l c ~ a = Vjca 
QI is a principle of quantifier interchange and generalizes to strings of 
242 


THE LOWER PREDICATE CALCULUS 
quantifiers in exactly the same way that K5 on p. 33 generalizes to LMI. 
We shall refer to such generalizations also as QI. 
Modal LPC 
A language ££ of modal LPC is simply the language formed out of LPC 
by the addition of the modal operator L and by changing FR2 to 
FR2' 
If a is a wff of i£ then so are ~ a and La. 
The interpretation of modal LPC is the obvious generalization of that for 
LPC.2 A model for modal LPC now consists of a quadruple (W,R,D,V) 
in which (W,R) is a frame and D is a domain of 'individuals'. In 
interpreting the predicates each n-place predicate must now be given a set 
of n-tuples from D in each world;3 or, what comes to the same thing, 
must be assigned a set of n +1-tuples, in each of which the first n terms 
are from D and the final term is from W. To say that {ul9 ... ,un,w) G 
V(0) is to say that in world w, <j> is true of «,, ... ,wn (in that order.) We 
can sum this up by defining explicitly a model for a language i£ of modal 
LPC. 
Semantics for modal LPC 
A model for a language !£ of modal LPC is a quadruple (W,R,D,V) in 
which W is a set (of 'worlds'), R a relation on W, D another set and V 
a function such that, where 0 is an n-place predicate, V(<£) is a set of 
n+1-tuples each of the form (uu ... ,un,w) for ul9 ... ,wn E D and w G 
W. In such a model an assignment /A to the variables is a function such 
that, for each variable*, /X(JC) € D. Where p is also an assignment to the 
variables \k and p are x-alternatives iff for every y except possibly x, p(y) 
= fi(y). Every wff has a truth-value at a world relative to an assignment 
/x as follows: 
[V0] 
V^Xl...xa,w) 
= 1 if Oxfe), -. ,MCO,w> e V(0) and 0 
otherwise. 
[V~] 
V„(~a,w) = 1 if Vp(a,w) = 0, and 0 otherwise. 
[VV] 
VM(a V jS,w) = 1 if VM(a,w) - 1 or V^,w) = 1, and 0 
otherwise. 
[VL] 
V^(La,w) = 1 if Vf£a,w') = 1 for every w' such that wRw', 
and 0 otherwise. 
[VV] 
V^VxayW) = 1 ifVp(a,w) = 1 for every ^-alternative p of/x, 
and 0 otherwise. 
243 


A NEW INTRODUCTION TO MODAL LOGIC 
A wff is valid in <W,R,D,V) iff V^(a,w) = 1 for every w € W and 
every assignment /*. A wff is valid on a frame (W,R) iff it is valid in 
every model based on (W,R). Among valid principles of modal LPC are 
the obvious generalizations of PR and PA. 
Systems of modal predicate logic 
Where S is a system of normal modal propositional logic then LPC + S 
is defined as follows, where the wff are now wff of a language X of 
modal LPC: 
S' 
If a is an LPC substitution-instance of a theorem of S then a is an 
axiom of LPC + S. 
Vl 
If a is any wff and x and y any variables and ot[y/x] is a with free 
y replacing every free JC, then Vxa D ctly/x] is an axiom of LPC + 
S. 
N 
If a is a theorem of LPC + S then so is La. 
MP If a and a D 0 are theorems of LPC -1- S then so is /?. 
V2 
If a D (3 is a theorem of LPC + S and x is not free in a then 
a D V*j3 is a theorem of LPC + S. 
An additional principle is known as the Bar can Formula, which may be 
stated by the schema 
BF VxLa D LVxa 
S + BF is LPC + S with the addition of BF. BF has the rather curious 
property that for some choices of a propositional system S, e.g. B or S5, 
BF is a theorem schema of LPC + S, while for other choices, e.g. K, T 
or S4, it is not. For uniformity, we shall in this chapter consider only 
systems which contain the Barcan Formula. 
Theorems of modal LPC 
Many theorems of modal LPC are of course obvious instances of 
theorems of propositional modal logic, e.g. L(yx<j>x D Ixxf/x) D 
{LVx<l>x D L3x\px), while others are instances of theorems of non-modal 
LPC, e.g. VxLcfrx D L<f>y. However the interest of modal predicate logic 
lies mainly in 'mixed' principles which exhibit interrelations among modal 
operators and quantifiers which cannot be stated in propositional modal 
logic or non-modal LPC alone. One of these we have already mentioned, 
the Barcan Formula.4 In order to see BF at work we shall look at how to 
244 


THE LOWER PREDICATE CALCULUS 
generalize LPCl. 
LPCl Vx(a D (3) D (Vxa D VJC0). 
As we saw in Chapter 11, in the early days of modal logic an important 
concern was to study principles involving strict implication. If we use the 
symbol -3 as in Chapter 11 in such a way that a -3 (3 is defined as 
L(a D (3) then the appropriate generalization of LPCl would seem to be 
(1) 
VJC(« -3 0) D (VJCCX -3 VJC0). 
Although (1) seems intuitively valid its proof requires BF. If we write (1) 
out without using -3 we notice that it is 
(2) 
V*L(a D 0) D L(Vjta D VJC/J). 
This looks like a combination of LPCl and K, but in the antecedent the 
modal operator is within the scope of the quantifier, while in the 
consequent the quantifiers are within the scope of the modal operator, and 
it is this feature which prevents it being derivable without BF. What we 
can prove quite easily in LPC + K is 
(3) 
LVJC(« D (3) D L(Vxa D Vx(3) 
but to get from (3) to (2) we require 
(4) 
VJCL(« D ]3) D LV;c(a D /J). 
(4) is of course the special case of BF in which a is a D (3. So (2) may 
be derived using BF. We leave it as an exercise to show that BF may be 
derived from (2). In Chapters 15 and 16 we shall say a little about the 
controversy which surrounds BF. 
The converse of the Barcan formula is provable in LPC + K as it 
stands. 
BFC 
LVxa D VxLa 
PROOF 
VI 
(1) Vxct D a 
(1) x DR1 
(2) Lixct D La 
245 


A NEW INTRODUCTION TO MODAL LOGIC 
(2) X V2 
(3) LVjca D VJCLCX 
Q.E.D. 
(Clearly x cannot be free in Lixa. and so the application of V2 in 
obtaining (3) from (2) is legitimate.) 
Hence if we had the Barcan Formula we could easily derive 
LVjca = VjcLa 
and from this by LMI and QI 
M^xa, = 3xMa. 
Two related theorems which may be easily proved without the Barcan 
formula are 
(5) 
3xLa D Llxa 
and 
(6) 
MVJCCX D VxMa 
Their converses however are not provable, and in fact are not valid. 
Consider the converse of (5). 
(7) 
Llx<j>x D 3xL<f>x. 
To see that (7) is not valid under the intended interpretation let <j>x be lx 
is the number of the planets'. Then the antecedent is true, for there must 
be some number which is the number of the planets (even if there were 
no planets at all there would still be such a number, viz. 0); but the 
consequent is false, for since it is a contingent matter how many planets 
there are, there is no number which must be the number of the planets. 
It is equally easy to see that the converse of (6) is not valid. (See, 
however, pp. 332-333) 
As we shall see on p. 276 there are many modal systems S, among 
them S4, and so a fortiori K, T, and D, such that the Barcan Formula is 
not a theorem of LPC + S. It is however a theorem of LPC + S where 
S contains the Brouwerian system B. Such systems contain MLp D p (p. 
62) and the rule DR4 (p. 62). The proof of BF is as follows:5 
246 


THE LOWER PREDICATE CALCULUS 
VI 
(1) 
VxLa D La 
(1) x DR3 
(2) 
MVxLa D MLa 
MLp D p 
(3) 
MLa D a 
(2) (3) X PC 
(4) 
MVxLa D a 
(4) X V2 
(5) 
MVxLct D Vxa 
(5) X DR4 
(6) 
VxLa D LVxa 
Q.E.D. 
Validity and soundness 
Our definition of validity for modal LPC will be exactly analogous to our 
definition for propositional modal systems. Since the modal LPC models 
defined on p. 243 all validate the Barcan Formula we shall often speak of 
them as BF models. If («^D,V) is a BF model and «^is the frame (W,R), 
we say that a wff a of modal LPC is valid in («^,D, V) iff V(a,w) = 1 for 
every w € W. We say that a model («^,D,V) is based on the frame 
^ 
and that a is valid on ^"iff it is valid in every BF model based on &. We 
say that ^ i s a frame for a system S + BF iff every theorem of S -I- BF 
is valid on &*> and that a class £*of frames characterizes S + BF iff, for 
every wff a of modal LPC, a is valid on every frame in ^iff it is a 
theorem of S + BF. A frame in a BF model, of course, is just the same 
kind of thing as a frame in a propositional model; so we can speak of one 
and the same frame as being a frame for a modal propositional system or 
a frame for a modal predicate system. Our first two theorems state 
important connections between propositional and predicate systems. 
THEOREM 13.1 Suppose that ^ i s a frame for a normal propositional 
modal system S. Then ^ i s a frame for S + BF. 
Proof: Let £*be the class of all BF models based on &. We prove the 
theorem by showing that each instance of the axiom schemata of S + BF, 
viz. S, Vl and BF, is valid in every model in £*, and then that the 
transformation rules MP, N and V2 preserve the property of being valid 
in every such model. 
(1) For the axiom schema S, we have to verify that if jS is a wff of 
modal LPC obtained by substituting modal LPC wff y,, ... , yn for 
propositional variables/?,, ... , pn in some theorem a of S, then (3 is valid 
in every model in #! Suppose that (3 is not valid in every such model, i.e. 
that for some (^,D,V) € & some JJL and some w € W, V^/^w) = 0. 
Let («^*,V) be a model for propositional modal logic in which & is 
precisely the same frame as in (.5^,D,V) and in which, for every w £ W 
and every p{ (1 < i < n), V(pi,w) = V (y^w). Then a straightforward 
247 


A NEW INTRODUCTION TO MODAL LOGIC 
inductive proof will show that V'(a,w) = 0, i.e. that a is invalid in 
(«^,V). Since by hypothesis «^"is a frame for S, this means that a is not 
a theorem of S. Thus if a is a theorem of S, /? is valid in every model in 
(2) For Vl, suppose that for some w £ W in some BF model, 
V^(Vjca,w) = 1. Let p be the jc-alternative of/x in which p{x) = /x(y). By 
[VV] Vp(a,w) = 1, and so by PR V^ctlylx^w) = 1. This shows that 
every instance of Vl is valid in every BF model, and hence in every 
model in £! 
(3) For BF, suppose that for some w G W and some assignment [i, 
VM(VjcLa,w) = 1. Let p be any ^-alternative of /x, and let wRw'. By [VV] 
Vp(La,w) = 1, and hence by [VL], Vp(a,w') = 1. Since this holds for 
every ^-alternative p of \x. we have VM(Vjca,w') = 1; and since this holds 
for every w' such that wRw' we finally have V(LVJCCK,VV) = 1. This shows 
that every instance of BF is also valid in every BF model, and so in every 
model in £! 
(4) MP and N are validity-preserving in a model for the same reasons 
as in propositional modal logic. 
(5) Finally, for V2 we assume that a D (3 is valid in every model in 
£*, and show that in that case so is a D Vx(3 (where x is not free in a). 
We prove (5) by contraposition. Suppose a D Vx(3 is not valid in some 
model (W,R,D,V). Then there is some assignment /x, in (W,R,D,V) such 
that V^(a,w) = 1 and Vh(Vx@,w) = 0. So there is some .^-alternative p 
of fi such that Vp(a,w) = 0. Now x is not free in a and so by PA on p. 
241, V„(a,w) = V^(a,w) = 1. But then Vp(a D 0,w) = 0, contradicting 
the assumption that a D (3 is valid in (W,R,D,V). 
This completes the proof of theorem 13.1. The next theorem is the 
converse of the previous one. 
THEOREM 13.2 If & is a frame for S + BF, then «^is a frame for S. 
Proof: Suppose that ^"is not a frame for S. Then there is some model 
(«^,V), based on &, such that for some wff a which is a theorem of S, 
and some w* G W, V(a,w*) = 0. Let /?„ ... , pn be the propositional 
variables in a; let </>,, ... , <f>n be n distinct one-place predicate letters and 
x some individual variable; and let (3 be the wff of modal LPC which is 
obtained from a by uniformly replacing plt ... , pn by <£,*, ... , (j>jc 
respectively. Clearly (3 is a substitution-instance of a, and is therefore a 
theorem of S + BF. To show that ^"is not a frame for S -I- BF it is 
clearly sufficient to exhibit a BF model (*^",D, V), based on J^ in which, 
248 


THE LOWER PREDICATE CALCULUS 
for some /x, V^(/?,w*) = 0. This can be accomplished by letting D be any 
domain whatsoever and, for any u € D, let (u,w) be in V(<f>d iff V(piyw) 
= 1, for each w G W and each i (1 < i < n). By [V0] this will ensure 
that fa is true in w in (^,D,V), for any assignment jti, at precisely those 
worlds at which px is true in («^",V). Since (3 contains no quantifiers, it is 
built up from <j>xxy ... , <f>jc by —, V and L in precisely the same way as 
a is from/?!, ... , pn . Hence at any w G W, (3 will have the same truth-
value in (^,D,V) as a has in (ST,V); and in particular, V^(/J,w*) = 0. 
Thus «^is not a frame for S + BF. 
This proves the theorem. Theorems 13.1 and 13.2 give us 
COROLLARY 13.3 
^ i s a frame for S iff «^is a frame for S -I- BF. 
We have defined a frame for modal LPC in the same way as for modal 
propositional logic, as a pair (W,R). It could however be argued that D 
is really part of the frame rather than the model, since it does not depend 
on the assignment V to the predicates of i£. In ordinary LPC the choice 
of D can affect validity. Thus if D has only one member 0JC D <j>y is 
valid, but not if D has more. If D has two members ((<j>x A <f>y) A 
(\j/x A ~\l/y)) D <t>z is valid, but not if D has more, and so on. However, 
this fact does not affect theorems 13.1 and 13.2. Obviously, by theorem 
13.1, if & is a frame for S then ( ^ D ) is a frame for S -I- BF for every 
D. If ^ i s not a frame for S then the proof of theorem 13.2 shows that 
(«^,D) is not a frame for S + BF, whatever D may be. Thus, for any D, 
«^*is a frame for S iff («^,D) is a frame for S + BF. 
It follows immediately from theorem 13.1 that every theorem of K + 
BF is valid on every frame. Moreover, the soundness results we proved 
in Chapter 1, together with this theorem, show that each of the following 
systems is sound with respect to the class of frames listed beside it: 
T 4- BF: 
reflexive frames 
K4 + BF: 
transitive frames 
KB + BF: 
symmetrical frames 
54 + BF: 
reflexive transitive frames 
B + BF: 
reflexive symmetrical frames 
55 + BF: 
equivalence frames 
Theorem 13.1, in fact, provides us with a general soundness result to the 
effect that whenever a normal propositional modal system S is sound with 
respect to a certain class of frames, so is the corresponding predicate 
249 


A NEW INTRODUCTION TO MODAL LOGIC 
system S + BF. 
Theorem 13.2, however, although it is the converse of theorem 13.1, 
does not give us a corresponding general completeness result, nor does 
corollary 13.3 give us a general characterization result. What theorems 
13.1 and 13.2 together tell us about T + BF, for example, is that the 
class of all frames for T + BF is precisely the class of all reflexive 
frames — given, that is, the result that we established in Chapter 10, that 
the frames for T itself are precisely the frames that are reflexive. But as 
we explained on p. 174, that result does not prove that T is complete with 
respect to the class of all such frames; and for just the same reasons, our 
present result does not give us a completeness result for T -f BF either. 
In fact we shall see in the next chapter that there are complete 
propositional systems S such that S + BF is not characterized by the class 
of frames that characterize S, and so not characterized by any class of 
frames. I.e. S is complete but S 4- BF is not. 
De re and de dicto 
When we look at the 'mixed' principles which are proper to modal 
predicate logic, and not merely generalizations of modal propositional 
logic or of non-modal predicate logic we notice a significant fact. We can 
illustrate this with the formula 
(1) 
Llx<j>x D 3*L<£x 
discussed above as (7) on p. 246. We noted that although the converse of 
this is a theorem of LPC + S for any normal system S yet (1) is not. The 
feature of modal LPC that makes (1) interesting may be seen by 
contrasting its antecedent and consequent. In the consequent there is a 
variable x free inside the scope of the modal operator L, while in the 
antecedent there are no free variables inside L. To see the importance of 
this difference look at the meanings of these two wff. 3xL<j>x says that 
there is a thing (in Latin a res) and concerning this thing (de re) it, the 
very same thing, is <f> in every accessible world. L3x<j>x does not carry this 
implication. It says that in every accessible world the proposition (dictum) 
that something (not necessarily the same thing in each world) is <j> is true. 
Whether or not the Latin descriptions are accurate the fact remains that 
wff of modal predicate logic divide into those called de dicto, in which 
no variable occurs free within the scope of a modal operator, and those 
called de re, in which some do. 
Now some de re wff are equivalent to de dicto wff in every S + LPC. 
250 


THE LOWER PREDICATE CALCULUS 
For instance Vx(L<j>x D L(j>x) A L3x<j>x is always equivalent to Llx<j>x. 
Other wff are sometimes so. For instance VxL<f>x is equivalent to LVx<f>x 
in systems with BF, but not otherwise. So the question arises as to 
whether there are modal systems in which all de re wff are equivalent to 
de dicto wff. The answer is no, unless the system is Triv or Ver. We 
shall first prove the result for S5 + BF by looking at the simplest kind 
of S5 model in which there is more than one world and show that the wff 
3xL<j)x is not equivalent to any de dicto wff.6 
The technique we shall use is this. We shall show that de dicto 
formulae do not depend on just how we match up an individual in one 
world with an individual in another. Consider the following two models, 
which coincide in W, R and D, but differ in the interpretation to the 
predicates. In each case W = {w,,w2}, R = W2 (i.e. every world can see 
every world) and D = {w,,w2}. In the first model, (W,R,D,V), V is as 
follows: For any predicate \p except for <j>, V(^) = 0 , i.e., these 
predicates hold of nothing in any world. V(<£) = {{ux,wx)y{u{yw^}. 
In the 
second model <W,R,D,V*), V*ty) = V(^) = 0 , but V*(0) = 
{(MI,W1),(M2,W2)}. In other words, in w{ ux is <f> in both models, but in vv2 
it is «! which is <f> in the first model, and u2 which is <j> in the second 
model. The idea behind the proof which follows is that for de dicto wff 
a model which 'switches' ux and u2 in w2 is equivalent, from the point of 
view of w,, to one which does not. This means that the difference 
between the models cannot be shown up by a de dicto wff, but can be 
shown up by a de re wff. 
We note that since these two models have the same D then the class of 
assignments to the variables is the same in each. Given an assignment \x, 
we let /x* denote the 'anti-assignment' such that for every variable x> /i(jc) 
5* H*(x). (In other words if /X(JC) = ux then n*(x) = w2, and vice versa.) 
THEOREM 13.4 If a is de dicto then V^/c^vv,) = VjJXa,^) and V^(o;,w2) 
= V ( a , w 2 ) . 
Proof: The proof is by induction on the construction of formulae. For 
atomic wff the theorem clearly holds for every wff i/'jc,.. .xn, for every 
predicate except <j>. So consider <f>x. 
VM(tf*,Wl) = 1 iff 
to,w,) 
G V ( « , iff ti(x) = ulf iff OI(*),H>,> € 
V*(*)iffV*(0*, W l) = 1. 
V M(^,w 2) = 1 iff </4*:),H>2) <E V(0) iff ii(x) = ult iff n*(x) - u2> iff 
(/x*W,w2) G V*(0) iff V*(cj>x,w2) = 1. 
251 


A NEW INTRODUCTION TO MODAL LOGIC 
The induction is clearly preserved for ~ and V . Consider Vxa. Note that 
if Vjca is de dicto then so is a. So VM(Vjcor,w>,) = 1 iff for every x-
alternative p of /x, Vp(a,Wj) = 1, iff (by the induction hypothesis) 
V*(a,w,) = 1 for every ^-alternative p of/x, i.e., iff Vj(VjCGf,w,) = 1. 
Vft,(Vxayw2) = 1 iff for every jc-alternative p of/x, Vp(a,w2) = 1, iff 
(by the induction hypothesis) Vp?(a,w2) = 1. Now every ^-alternative v 
of /x* will be p* for some ^-alternative p of /x, and so Vp(a,w2) = 1 for 
every jc-altentative p of it iff V^(a,w2) = 1 for every jc-altentative v of 
H*, i.e. iffVM*(Vjca,W2) = 1. 
For L we note that if La is de dicto then a must contain no free 
variables and so, by PA, Vh(a9w) = Vp(a,w) and V*(a,w) = V*(a,w) 
for every /x, p and w. Now for any w G W, 
(1) 
VM(Ia,w) = 1 iff 
(2) 
V>,w,) = 1 and 
(3) 
V>,w 2) = 1. 
By the induction hypothesis (2) holds iff 
(4) 
VjCor.w,) = 1 
and (3) holds iff 
(5) 
V > , w 2 ) = 1. 
But a is closed and so (5) holds iff 
(6) 
V*(cx,w2) = 1. 
So (6) holds iff (3) does. Thus (2) and (3) hold iff (4) and (6) hold. But 
(4) and (6) hold iff 
(7) 
V*(L«,w) = 1. 
So (1) holds iff (7) holds. This gives the result immediately for w = wx. 
For w = w2, since La is closed (7) holds iff 
252 


THE LOWER PREDICATE CALCULUS 
(8) 
VM*(Lo,W2) = 1. 
This proves theorem 13.4. 
We now show that 3JCL0JC is not equivalent in S5 + BF to any de dicto 
wff. We note first that both (W,R,D,V) and (W,R,D,V*) are models 
which satisfy all theorems of S5 + BF. So suppose there were some de 
dicto wff a such that |-S5+BF 3xL<j>x = a. Then for every /i and every w, 
Vh(lxL<j>x,w) = V^otyW) and 
V*(3*L<£x,w) = V*(a,w). 
But a is de dicto and so, by theorem 13.4, 
V>,H.,) = V*(a)H.,) 
and so 
But it is easy to see that 
V^lxL^w,) = 1 and 
VfQxLfaw) = 0. 
So lxL(j>x is not equivalent to any de dicto formula in S5 + BF, and so 
a fortiori not equivalent to any de dicto formula in any weaker system. It 
is not hard to see how to generalize the result. The key feature of the 
models we used is that W,RH>2 and w{ ^ w2. So any system S whose 
frames include at least one where this is so will have no de dicto wff 
equivalent to 3xL<j>x. And in fact, as we have observed, this will include 
all systems S + BF, unless S is Triv or Ver or their intersection. 
In the proof of theorem 13.4 a crucial role is played by the 'anti-
assignment' jLt* of fi. In a model with more than two individuals there 
would not be a unique anti-assignment and one would have to require that 
H* be based on a permutation ir of the domain, i.e. a function such that 
for every u G D, ir(u) €E D, and for every v G D, there is some u € 
D such that TT(U) = v, and where u ?* v then ir(u) ?± 7r(v). For any 
253 


A NEW INTRODUCTION TO MODAL LOGIC 
assignment /x the /x* based on 7T would have to be such that for any 
variable JC, JH*(JC) = ir(fi(x)). V* would be required to be such that (7r(wj), 
... ,T(I0.W> G V*(0) iff («,, ... ,wn,w) G V(<j>). Fine7 has shown that 
not only is a de dicto formula unaffected by such permutations, but that 
only de dicto formulae are unaffected, in that if any formula is unaffected 
then it is equivalent, in the system in question, to a de dicto formula. 
Exercises — 13 
In Part III exercises marked with * are ones for which we have not 
ourselves obtained a solution. Where solutions are known to us to have 
been obtained by others we have indicated this. Some of the remaining 
starred exercises may be regarded as open research problems. 
13.1 
(a) 
Derive BF from (2) on p. 245. 
(b) 
Prove Mlxa s 3xMce in K + BF. 
(c) 
Prove (5) and (6) on p. 246 
13.2 
Prove the following in S + BF, where S satisfies the conditions 
indicated: 
(i) VxL(a D /?) D L(3JC« D lc/3) 
(S is any normal system) 
(ii) lyLM{<f>y D Vx<j>x) 
(S contains B) 
(iii) 
3JCL(L0JC V \[/y) = Llx(L<j>x V \j/y) 
(S contains S5) 
(iv) 3yLVx(L<j>x D ML<j>y) 
(S contains S4.2) 
13.3 
S4.4 is S4 + p D (MLp D Lp). Prove the following in 
54.4 + BF: 
(C) 
~L(yxML<j>x A lx~<j>x) 
13.4 Devise a model to show that Llx<j>x D 3xL<j>x is not valid in 
S5 + BF. 
13.5 
Show that none of the following are valid in S5 + BF: 
(a) 
3JC~L<£JC D MVx~<f>x 
(b) 
(Llx<j>x A VxM\l/x) D Mlx(<j>x A ^c) 
(c) 
V*(L0JC V L~<j>x) V Wx(M(j>x A M~<j>x) 
13.6 
Establish the validity of the wff in 13.1 and 13.2 with respect to 
the appropriate definition of validity. 
254 


THE LOWER PREDICATE CALCULUS 
13.7 
Show that Vx(L<f>x V L~<j>x) V 3x(M<j>x A M~<j>x) is valid in 
both the models on p. 251. Then show that so is its schematic form Pr 
V;c(La V L ~ a ) 
V 3x(Mct A M~a) 
provided this contains no free 
variables. 
Notes 
1 The predicate calculus is also known as the Functional calculus. The terms 
'lower' and 'first-order' are used interchangeably and refer to the fact that only 
individual variables appear in quantifiers. First-order logic is sometimes referred 
to as first-order quantification theory. Chapters 3 and 4 of Church 1956 still 
provide the fullest development. 
2 The definitions which follow are adapted from Kripke 1963b, though Kripke's 
own semantics, as we shall see in Chapter 16 differs in certain important respects. 
Other early semantics for modal predicate logic may be found in Kanger 1957a, 
1957b, Bayart 1958, Montague 1960 and Hintikka 1961. 
3 Following the terminology of Carnap 1947 the set of n-tuples which satisfy 0 
in a world w is sometimes called the extension of <f> in w, and the whole set of 
n + 1-tuples which is V(0) in a model as defined in the text is called the intension 
of 0. Because of their ability to distinguish between intensions and extensions 
modal languages are sometimes called intensional languages. In non-modal LPC 
the values of predicates are simply extensions, and the language of non-modal 
LPC is sometimes called an extensional language. 
4 The Barcan Formula appears first as axiom 11 on p. 2 of Barcan 1946, the first 
study of modal predicate logic, though in a slightly different form stated with O 
(M) and the symbol -3 referred to on p. 245. 
5 Prior 1956 proves this when S is S5, and in 1967, p. 146 credits the first proof 
of BF when S is B to E.J. Lemmon. 
6 This was proved in Tichy, 1973. (The purported proof in Cresswell 1969b is 
defective.) On p. 184 of Hughes and Cresswell 1968 the elimination of de re 
modalities was linked to a principle due to von Wright 1951 called the Principle 
of Predication. The schematic version of the principle of predication stated on p. 
185 of Hughes and Cresswell 1968 as Pr is too strong. From it one may derive 
VxVy(M(0:c = <f>y) D L(<f>x = #y)). This is certainly strong enough for the 
elimination of all de re modalities. (Broido 1975. Broido also proves that the truth 
of SxLct = L3xa is a necessary and sufficient condition for the elimination of de 
re modalities in the sense of Hughes and Cresswell 1968, p. 184 — a sense 
attributed to Prior 1955a — though McKay, 1978, questions this sense.) If one 
restricts Pr so that it has no free variables, which is possibly what von Wright 
intended because Vx(L<f>x V L~<f>x) V VJC(M0A: A M~<f>x) is an instance of this, 
then the proof given in the text shows that de re modalities are not eliminable, 
even with Pr. This is because both the models described there satisfy Pr when so 
restricted. 
7 Fine 1978. 
255 


14 
THE COMPLETENESS OF 
MODAL LPC 
In this chapter we shall extend the canonical model technique introduced 
in Chapter 6 to LPC. We shall show how to define, for each modal 
system S, a canonical model for S + BF, relative to some language ££ of 
modal LPC, which will have the property that for any wff a of ££, |-s 
a iff a is valid in that model. We shall then look at the consequences of 
this for the completeness of systems of modal LPC. In particular we shall 
look at the relation between the completeness of a propositional system S 
and the completeness of S 4- BF.1 
Canonical models for modal LPC 
As in the case of a propositional modal system the worlds in the canonical 
model of a system of modal predicate logic will be maximal consistent 
sets of wff. As before we assume some system S (more strictly S + BF) 
to be fixed throughout the discussion and will simply say consistent rather 
than S-consistent. In the case of LPC we have in addition to say what the 
domain D of individuals is. The answer is simple: D will consist of the 
individual variables. It may seem strange that elements of the language, 
the individual variables, should themselves appear as the values over 
which they range, but the definition of a model did not put limits on what 
D could be any more than it put limits on what W could be, and the 
whole idea behind canonical models is to use the language itself to 
provide the constituents of the model. 
We cannot let the worlds just be maximal consistent sets, they have to 
have another property as well. To see this recall that the 'hard' part of the 
256 


THE COMPLETENESS OF MODAL LPC 
canonical model theorem for modal propositional logic was to show that 
if La € w then there is some W such that wRw' and a £ w'. We have 
a similar problem in the predicate case when we have Vxa £. w. Here we 
don't want to go to another world to make a false. But what we do need 
to do is to ensure that if Vxa is not true in a world then there is some 
individual (often called a 'witness') which makes this so. If Vxa is false 
then a should be false of something, and if the 'things' in the domain of 
individuals are individual variables this means that a[y/x] will need to be 
false in w for some y. 
Here we run into a problem. For consider the set 
Q = {~v*<£x, <f>yl9 <j>y2, ...} 
I.e. Q consists of ~\/x<j>x together with <j>y for every individual variable 
y. 0 is consistent, since every finite subset obviously is, and so Q has a 
maximal consistent extension. But that extension cannot have a witness to 
the falsity of VX0JC, for no wff of the form ~ <f>y can be consistently added 
to Q. 
The worlds of the canonical model must not only be maximal 
consistent. They must be sets which have what we call the V-property. A 
set A has the V-property iff for every wff a and every individual variable 
JC, there is some individual variable y such that a\ylx\ D Vxa E A. If T 
is maximal-consistent and has the V-property then if VJCCK £ T there must 
be a 'witness' y such that a\y/x] £ T. For since T has the V-property 
there is ay such that a[y/x] D Vxct E I\ and if a\y/x] E T then Vxct E 
r. 
But if the worlds in the canonical model of S + BF all have the V-
property what are we to do about poor 0? Clearly U does not have the V-
property. Nor could it consistently be given it. It is consistent, and yet it 
seems unsatisfiable. The answer actually is quite easy. We simply extend 
the language by adding infinitely many new (individual) variables. 
To make this precise assume that we have two languages i£ and f£+ of 
modal predicate logic. They each satisfy the formation rules of p. 236 and 
they share the same predicates. The only difference is that i£+ not only 
has all the infinitely many variables that i£ has but it has infinitely many 
new ones as well. It is a standard (though not entirely trivial) fact about 
LPC, whether modal or non-modal, that if A is a consistent set of wff of 
i£ then it remains consistent when i£ is extended to f£+. We are now in 
a position to state the basic theorem about the V-property: 
257 


A NEW INTRODUCTION TO MODAL LOGIC 
THEOREM 14.1 If A is a consistent set of wff of ££ then there is a 
consistent set of wff of X+ with the V-property such that 
A c A. 
The reason the definition of the V-property is given in the form it is is 
that once a set A has the V-property then any set (in the same language) 
of which A is a subset still has the V-property. In particular theorem 6.3 
on p. 115 guarantees that since A is consistent there is a maximal-
consistent set T such that A Q T, and so since A has the V-property T 
does also. 
Proof: We assume that all wff of the form Vxa for any wff a of 5£+ and 
any variable x are enumerated so that we can speak of the first, the 
second, and so on. We define a sequence of sets AQ, A,, ... etc. as 
follows: 
AQ is A 
An+1 is An U {a[y/x] D Vxa} 
where Vjca is the n+ 1th wff in the enumeration of wff of that form and 
y is the first variable not in A„ or in a. Since A0 is in ££ and A„ has been 
formed from it by the addition of only n wff there will be infinitely many 
variables from !£+ left over to provide such a y. 
\ 
is assumed consistent so we shall show that Aa+l is if A,, is. Suppose 
not. Then there will be /J,, ... ,0k in An such that 
(i) 
\-((3, A ... A (30 D a[y/x]md 
(ii) 
|-(0i A ... A 0J D ~Vxa. 
Since y does not occur in An it is not free in (0, A ... A fi^) and so from 
(i) by V2 
(iii) 
|-(ft A ... A ^ 
D 
Vya\y/x\. 
And since y does not occur in a, \fya\y/x] is a bound alphabetic variant 
of Vxa, and so, by RBV on pp. 242, 
(iv) 
K f t A ... A ^ D 
Vxa. 
258 


THE COMPLETENESS OF MODAL LPC 
But (ii) and (iv) give 
(V) h ~(0, A ... A ft) 
and (v) makes An inconsistent contrary to hypothesis. Let A be the union 
of all the AnS. It is easy to see that A is consistent and has the V-property. 
This proves theorem 14.1. 
As noted A has a maximal-consistent extension T in ££+ with the V-
property. Theorem 14.1 holds in any system (modal or not) which 
contains a standard axiomatic basis for LPC. In constructing the canonical 
model for S + BF our aim is to show that for any consistent set A of wff 
of a language i£ of modal predicate logic there is a world in the canonical 
model at which all of A's members are true. Because of sets like Q the 
worlds in the canonical model must be maximal-consistent in the extended 
language ££+. What we must now show is that where w is such a world 
and La is false in w, then there is a world w' such that wRw' and a is 
false in w'. But this means showing that w' is maximal consistent (in 
i£+), has the V-property, and contains L~(w) U { ~ a } . To do all this we 
need a theorem. Unlike theorem 14.1 which holds for all systems 
containing LPC the following theorem concerns normal modal systems, 
and in particular requires the Barcan Formula.2 
THEOREM 14.2 If T is a maximal-consistent set of wff in some language 
(say ££+) of modal predicate logic, and T has the V-
property, and a is a wff such that La & T, then there is 
a consistent set A of wff of !£+ with the V-property such 
thatL-(T) U {-a} 
Q A. 
Proof: We define a sequence of wff y0, y,, y2, ... etc. y0 is — a. Given 
yn we define yn+1 as follows. Let VxS be the n-(- 1th wff of that form and 
let y be the first variable such that 
(*) 
L~(T) U {yn A {b\ylx\ D Vxb)} is consistent. 
Let Yn+i be yn A (b\y/x\ D Vxb). In order for this construction to 
succeed we have to be sure that there always will be a y satisfying (*). 
Since y0 is ~ a , L_(r) U {y0} is consistent from lemma 6.4 on p. 117. 
We show that provided L~(r) U {yn} is consistent there will always be 
a y which satisfies (*). 
Unlike the situation in theorem 14.1, we cannot here assume that y is 
259 


A NEW INTRODUCTION TO MODAL LOGIC 
a new variable, since all the variables of ££+ will already occur in L~(r). 
Nevertheless we can show that there always will be an appropriate y. 
Suppose there were not. Then for every variable y of !£+ there will exist 
some {LjSj, ... ,L/3k} Q L~(r) such that 
|-(P, A ... A /?„) D (7n D ~(b\y/x] D Vxb)) 
so, by DR1 and L-distribution, 
(i) 
h (Lft A ... A L&) D L(7n D ~(6[y/x] D Vxb)) 
But T is maximal consistent and L(2lf ... ,Lj3k €i T, and so L(yn D 
~(b\y/x] D VJCS)) E T. 
Now this is so for every variable y> and T has the V-property. What 
this means is this. Let z be some variable not occurring in b or in yn, and 
consider VzL(yn D ~(b[z/x] D Vxb)). Since T has the V-property there 
will be a variable y such that 
(ii) L(Tn D (~(b[y/x] D Vxb)) D 
VzL(7n D ~(b[z/x] DVxb)) 
is in T. But we have already noted that L(yn D ~(6[y/jc] D Vxb)) is in 
T for every y. And so 
(iii) VzL(ya D ~(b[z/x] D Vxb)) 
is in T. But T is maximal S + BF-consistent and so, by BF, 
(iv) LVz(yn D ~(b[z/x] D Vxb)) 
is in T. Since z does not occur in yn or 6 then by LPC2 we have in T 
(v) L(7n D Vz~{b[zlx\ D Vxb)) 
But by LPC3, 
h 
3Z(S[Z/JC] D 
Vxb) 
But then L ~ 7 n G T and so ~ 7 n € L~(r) which would make An 
260 


THE COMPLETENESS OF MODAL LPC 
inconsistent. 
Let A be the union of L~(r) and all the 7ns. Since each L~(r) U {yn} 
is consistent, and since |- ym D yn for m > n, so is their union A. A has 
all the required properties and so theorem 14.2 is proved. 
The canonical model then for a system S + BF in a language i£ with 
an extension !£+ is a quadruple (W,R,D,V) where W is the set of all 
maximal consistent sets with the V-property in i£+; and wRw' iff for 
every La G w, a G w' (i.e. L~(w) Q w'). D is the set of variables in 
£+ 
and (JC„ ... ,*n,w) G V(<£) iff <j>xx...xn G w. Finally take the 
'canonical' value-assignment a to be the assignment such that o(x) = JC, 
for every variable x in D. We prove the following theorem: 
THEOREM 14.3 For any w G W, and any wff a G ££+, Va(a,w) = 1 iff 
a G w. 
The proof is by induction on the construction of wff. 
(a) 
First consider any atomic wff <j>xx...xn. Va(<£xi...*n,w>) = 1 iff 
<*(*,), ... ,crCO,w) G V(<£), iff (xly ... ,*n,w) G V(0), iff 
<l>xx...xn G w. 
(b) 
Va(~a,w>) = 1 iff Vff (a9w) = 0, iff a g w, iff ~ a G w. 
(c) 
Va(a V 0,w) = 1 iff Va(a,w) = 1 or Va(0,w) = 1 iff a G w or 
j8 G w, iff a V /? G w. 
(d) 
Suppose Vjca G w. Let p be any ^-alternative of a. This means 
that y(jc) = v for some variable y in i£+. Now, by Vl, a\y/x] G 
w. So V0(aty/jc],w) = 1. So by PR, V„(a,w) = 1. Since v is any 
jc-alternative of a, Va(Vjta,w) = 1. 
(e) 
Suppose Vxa £ w. Then ~Vxa G w and so, since w has the V-
property in i£+, there is some v in i£+ such that ~a\y/x] G w>. 
So a\y/x] £ w and so Va(a[jy/;cj,w) = 0. So by the validity of 
VI, Vff(Vxa,w) = 0. 
(f) 
Suppose La G w and wRw'. Then a G w', and so Va(a,w') = 
1, and since this is so for every w' such that wRw', Va(La,w) 
= 1. 
(g) 
Suppose La £ w. Then —La G w. But then by theorem 14.2 
there is some w' G W with the V-property such that ~ a G w'. 
So a £ w', and so Va(a,w) = 0. But wRw' and so Va(La,w) = 
0. 
This proves theorem 14.3. 
A consequence of theorem 14.3 is the completeness of non-modal 
261 


A NEW INTRODUCTION TO MODAL LOGIC 
LPC. A set of non-modal wff will be S 4- BF-consistent for any normal 
modal logic S iff it is LPC-consistent, and therefore any consistent set A 
of non-modal wff is true at some world w in S's canonical model 
(W,R,D,V), and w can provide an LPC interpretation (D*,V*) in which 
V*(a) = V(a,w) = 1 for every a G A. Further, if every finite subset of 
A is true in some model then, by the soundness of LPC, every finite 
subset is consistent. (Otherwise, where a is the conjunction of all its 
members | 
a, and so —a would be valid, contradicting the fact that 
a is true in some model.) So, by the definition of consistency, A is 
consistent, and therefore has a model. This gives us the compactness of 
LPC, a fact used on p. 184 in discussing propositional modal systems. 
Since every theorem of S + BF is in every world in the canonical 
model for S + BF, theorem 14.3 means that every such theorem is valid 
in the canonical model. Moreover, theorem 14.1 and the definition of W 
show that every S + BF-consistent wff is a member of some world, and 
therefore, by Theorem 14.3, true in some world in the canonical model; 
and this in turn means that every non-theorem of S + BF is false in some 
world in that model. So, to parallel corollary 6.6 on p. 119, we have 
COROLLARY 14.4 Any wff a is valid in the canonical model for S 4- BF 
iff h + BF «• 
Completeness in modal LPC 
On p. 249 we were able to reach a general soundness result connecting 
the soundness of a normal propositional modal system S with the 
soundness of the corresponding predicate system S + BF. In this section 
we shall enquire whether, and subject to what qualifications, we can 
obtain 
any 
analogous general 
results about completeness 
and 
characterization. 
Our first result is that if S is incomplete (in the absolute sense 
explained in Chapter 9) then S + BF is incomplete too. As a preliminary 
to proving this, we shall introduce some new terminology and prove a 
lemma. Suppose that a is any wff of modal LPC, and that /? is an 
expression which results from a by deleting all quantifiers and individual 
variables, and uniformly replacing each distinct predicate letter by a 
distinct propositional variable. Then clearly /? is a wff of modal 
propositional logic; and we shall call it a propositional transform of a iff 
it is derived from a in this way. Next, let plf p2, • •• , etc., <£,, <f>2, ... , 
etc. and xl9 x2, ... , etc. be enumerations of the propositional variables, 
262 


THE COMPLETENESS OF MODAL LPC 
the one-place predicate letters, and the individual variables respectively. 
Then we shall say that a wff 7 of propositional modal logic and a wff b 
of modal LPC are mates iff 6 is the result of uniformly replacing each px 
in 7 by <£#. Clearly, each wff 7 of propositional modal logic will have 
a unique mate 6, and y will be a propositional transform of 6. 
Our lemma is 
LEMMA 14.5 Suppose that 
f-s+BF « a n^ that (3 is a propositional 
transform of a. Then |-s (3. 
Proof: Since |~S+BF a> there is a proof of a in S + BF. The lemma is 
then proved by induction on the proof of a in S + BF. For if any wff in 
the proof of a is an instance of the axiom schema S, then its propositional 
transforms are theorems of S. If it is an instance of Vl or BF, then its 
propositional transforms are substitution-instances of p Dp, and are 
therefore also theorems of S. The rules MP and N operate in exactly the 
same way in S and in S + BF. And if a wff y' is derived from y by V2, 
the propositional transform of y' is simply identical with that of 7. This 
shows that a parallel proof of (3 can be given in S, and hence that |-s (3, 
which proves the lemma. 
COROLLARY 14.6 If 7 and 6 are mates then if |-S+BF ^> K 7-
THEOREM 14.7 Suppose that a normal propositional modal system S is 
incomplete. Then so is S + BF. 
Proof: Since S is incomplete, there is some wff 7 of propositional modal 
logic which is valid on every frame for S but is not a theorem of S. Let 
6 be the wff of modal LPC which is the mate of 7. Since 6 is a 
substitution-instance of 7, it is also valid on every frame for S. Therefore 
by corollary 13.3 on p. 249, 6 is valid on every frame for S + BF. But 
by corollary 14.6 8 is not a theorem of S + BF. So S + BF is 
incomplete. This completes the proof. 
We know, then, that if S is not characterized by any class of frames, 
neither is S + BF. So the remaining question is: if S is characterized by 
some class of frames, what can we deduce from that about the 
characterization of S -f BF? More precisely, is it the case that whenever 
S is characterized by the class of all the frames for S, then S + BF is 
also characterized by the class of all the frames for S? The answer is no 
- as we shall prove in the next section. 
263 


A NEW INTRODUCTION TO MODAL LOGIC 
We proved in corollary 13.3 on p. 249, that the frames which are 
frames for S are precisely the frames which are frames for S + BF. But 
this does not of course give us completeness. Here it may help to recall 
again the discussion of the systems KW and KH on pp. 164-165. We 
were able to prove that precisely the same frames were frames for these 
two systems, yet it turned out that the class of these frames characterized 
one of them but did not characterize the other. Corollary 13.3 does, 
however, easily give us this conditional answer: 
COROLLARY 14.8 If S + BF is complete, then it is characterized by the 
class of all frames for S. 
The proof is simply that any complete system, i.e. any system 
characterized by any class of frames, is characterized by the class of all 
the frames for that system, and that by corollary 13.3 the frames for S + 
BF are precisely the frames for S. So if a system S + BF is complete, we 
know of at least one class of frames which characterizes it. 
Our next result gives us another conditional answer. 
THEOREM 14.9 Suppose that the frame of the canonical model for S + 
BF is a frame for S. Then S + BF is characterized by 
the class of all frames for S. 
Proof: Suppose first that a is a theorem of S + BF. Let ^ b e any frame 
for S. By theorem 13.1 on p. 247, ^ i s also a frame for S 4- BF, and 
therefore a is valid on it. So a is valid on every frame for S. Suppose 
now that a is not a theorem of S + BF. Then —a is S + BF-consistent, 
and therefore is in some w € Win the canonical model for S + BF. So 
by theorem 14.3, V(a,w) = 0. But by hypothesis the frame of the 
canonical model is a frame for S. Therefore a fails on some frame for S. 
This means that, given the hypothesis of the theorem, any wff a of 
modal LPC is valid on all frames for S iff |-S+BF a, which is what the 
theorem states. 
COROLLARY 14.10 
If the frame of the canonical model for S + BF is 
a frame for S, then S + BF is characterized by any 
class of frames for S which contains the frame of 
the canonical model for S + BF. 
Theorem 14.9 allows us to establish the completeness of particular 
264 


THE COMPLETENESS OF MODAL LPC 
systems. The completeness of K is immediate since the frame of the 
canonical model of K + BF is certainly a frame, and the completeness of 
many other systems follows exactly as in the case of propositional modal 
logic by proving that the frames of their canonical models are in the 
required class. As an example, take T -I- BF. By corollary 14.10, if we 
wish to prove that T + BF is complete with respect to the class of all 
reflexive frames all we need to show is that the frame of the canonical 
model for T + BF is reflexive. This is easily accomplished, in the same 
way as the parallel result for T was on p. 120. For since Lp D p is a 
theorem of T, La D a is a theorem of T + BF for every wff a of modal 
LPC. So every such La D a is in every world w in the canonical model 
for T + BF, and hence whenever La G w, we have a G w. Thus Lr(vv) 
Q w; i.e. wRw. We also showed on p. 249 that T + BF is sound with 
respect to the class of reflexive frames. It is therefore characterized by 
this class. Clearly, analogous results can be obtained in the same way for 
many of the other systems we have mentioned, including all those listed 
on p. 249. 
Incompleteness 
We shall now address the question posed on p. 263. Suppose that S is in 
fact complete. Does it follow that S + BF is also complete? The answer 
is no. Furthermore, a point worth noting is that, unlike incomplete 
propositional logics like KH, which often look as if they have been 
'cooked up' simply to provide examples of incomplete logics, these 
incomplete predicate logics are based on propositional logics which have 
a history going back to the late fifties or early sixties. One of these is the 
system S4M that we discussed on pp. 131 and 175.3 This system is 
characterized by the class of frames which are reflexive, transitive and 
final, where finality is the condition that every world can see an end 
world - a world that can only see itself. Further, as we noted on p. 175, 
every frame for S4M is of this kind, and so if S4M + BF were complete 
it would be characterized by this class of frames. Therefore, to show the 
incompleteness of S4M + BF it will suffice to produce a wff of modal 
predicate logic which is 
(I) valid on every reflexive, transitive and final frame; 
(II) not a theorem of S4M + BF. 
Such a wff is 
265 


A NEW INTRODUCTION TO MODAL LOGIC 
(*) 
L3x<j>X D M3xL<f>X 
LEMMA 14.11 
(*) satisfies (I) 
Proof: Let ^ b e reflexive, transitive and final, and suppose that for some 
w G W, where ^ i s (W,R), and some model (W,R,V) based on (W,R) 
and some assignment \L to the variables of i£, V^Llxfa^w) 
= 1. Now w 
can see a final world w', and so VJ^xfa^w') 
= 1. So there is some x-
alternative p of fi such that Vp(<f>x,w') = 1. Since w' is final Vp(L<j>x,w') 
= 1. So Wtl(3xL(f>xiw') = 1 and hence V^(M3XL</>JC,H>) = 1, which 
establishes (I). 
To establish (II), that (*) is not a theorem of S4M + BF, we produce 
a model (W,R,D,V) in which every theorem of S4M + BF is valid but 
(*) is not. Here is the model: 
Both W and D are the set of natural numbers. I.e. where Nat = {0, 
1, 2, ... etc.} then W = D = Nat. It may seem strange that worlds and 
individuals are the same but there is nothing in our definition of a model 
which prevents this. An alternative would be to index the worlds and 
individuals by the natural numbers and let the worlds be wlf vv2, ... etc. 
and the individuals uly u2, ... etc. This would not change the nature of the 
proof which follows but would make it a little more difficult to 
comprehend. R is simply <, i.e. i can see j provided j is no less than i; 
i.e., all numbers can see themselves and bigger numbers. 
For any predicate \p except </>, V(^) = 0 . That is any wff \j/xx.. .xn will 
be false for any assignment when \p is not <f>. For <£, V(0) = {(i,i): i £ 
Nat}. What this means is that, at world i, <f> is true of the individual i, 
and i alone. (If worlds and individuals are distinct one would require V(<£) 
to be {(witu-j) : i & Nat}.) 
We prove two things 
(A) (*) fails at 0 in (W,R,D,V); 
(B) For every wff a of modal LPC LMa D MLa. is valid in 
(W,R,D,V). 
Since (W,R,D,V) is reflexive and transitive we know that all the other 
axioms of S4M + BF are valid in it, and since all the transformation 
rules of S + BF preserve validity in a model, (A) and (B) will together 
guarantee that (*) is not a theorem of S4M + BF. 
The proof of (A) is straightforward. Let fi be any assignment to the 
266 


THE COMPLETENESS OF MODAL LPC 
variables. For any n G Nat, where p is the jc-alternative of fx in which 
p(x) = n, Vp((f>x,n) = 1, and so V^Bjc^n) = 1 for every n € W. So 
V^LdxfayO) = 1. But consider any n G Nat and let p be any x-
alternative of fx. Choose some m > n with m ^ p(x). Then Vp(0jt,m) = 
0, and so Vp(L^c,n) = 0 for every ^-alternative p of fi. So V^(3JcL<£;c,n) 
= 0. Since this is so for every n G Nat we have Wli(M3xL<j>x,0) = 0. 
Thus VM((*),0) = 0 and so (*) fails in (W,R,D,V). 
The proof of (B) is more complex, although the idea behind it is really 
not too difficult. What LMa D MLa says is that every proposition 
eventually settles down to a constant truth-value. If LMa is true this 
means that a is always going to be true. MLa says that in that case there 
will come a point at which it is true forever. Once a proposition has 
settled to a constant truth-value then as far as that proposition is 
concerned time has come to an end and if each of a finite number of 
propositions settles to a constant truth-value there must come a time at 
which they have all settled. 
But in LPC it could easily happen that, although for any particular 
individual, the proposition that it is <j> settles to a constant truth-value, 
there is always another individual which has not yet done so, and if there 
are infinitely many individuals we need never reach a world at which they 
have all settled, and so time need never come to an end. That is precisely 
what happens in this model. Each <j>\ settles to the value false in worlds 
greater than i, but at no stage has this been settled for all individuals. So 
although each wff comes to have a constant value there are others which 
have not yet done so. First consider an atomic wff. If \j/ is not <f> then 
^jCi..jcn is always false, whatever world we are in. For <f>x then if ix(x) is 
i, <j>x will be false at every j > i. Suppose that we have two assignments 
fji and p, suppose JX{X) = n and p(x) = m. Now consider worlds k > n 
and h > m. V ^ ^ k ) = 0 and Vp(<f>x,h) = 0. This has the consequence 
that, at least for atomic formulae, and, in fact, as we shall show in a 
moment for all wff, once we get to worlds greater than the values 
assigned to their free individual variables y their truth-values become 
constant. It is this fact which will enable us to validate LMa D MLay 
since if a is always going to be true, and eventually comes to have a 
constant truth-value, then there will come a world at which it will be 
necessary. 
This feature of atomic wff of course has to be shown to hold of all 
wff. It does indeed hold of all wff, and we will be able to prove that it 
does by induction on the construction of wff, but the presence of 
267 


A NEW INTRODUCTION TO MODAL LOGIC 
quantifiers relies on an additional feature of wff in this model. 
Note that V^x^n) 
= 1 iff /x(x) = n. Now consider some m < n, and 
some assignment p such that p(x) = n—m. Then Vp(<£jc,m) = 1 iff p(x) 
= m. This has the consequence that VM(</>jc,n) = Vp(0jc,m) where 
/x(x) — p(x) = n—m. In other words, given two worlds, an assignment 
which 'shifts' the individuals along the difference between these two 
worlds preserves the truth-value of the wff. 
These two properties, stated for the single variable x in the case of the 
atomic wff <j>x generalize to an arbitrary wff a with respect to the 
variables free in a. This may be expressed in the following lemma. 
LEMMA 14.12 
Given a wff a, suppose n > m and /* and p are so 
related that for every x free in a either 
(i) fi(x) < n and p(x) < m 
or 
(ii) fi(x)-p(x) = n - m 
Then VM(a,n) = Vp(a,m). 
(In this lemma (i) may hold of some variables and (ii) of others.) Given 
lemma 14.12 we have, for the special case where p = y, and (i) holds 
COROLLARY 14.13 
If m > n(x) for every x free in a, and n > m then 
V>,n) = V>,m). 
We first show that, given corollary 14.13, LMa D MLa is valid in 
(W,R,D,V) for every wff a. Suppose V^LMa.w) = 1. Consider some 
w* > w such that fi(x) < w* for every x free in a. Clearly V^A/o^w*) 
= 1, and so V^a, m) = 1 for some m > w*. Since w* > ii(x) for 
every x free in a then m > /i(jc) also for every such x. So by corollary 
14.13 for every n > m, V^(a,n) = 1, and so VM(La,m) = 1 and so 
V^(MLa,n>) = 1 as required. 
Now to prove lemma 14.12. The proof is by induction on the 
construction of a. If a is atomic then if a is \pxx...xn for any \p except </>, 
V^(a,w) = 0 for every w E W and every p, and so the lemma holds 
trivially. Suppose a is <f>x. If /X(JC) < n and p(x) < m then V^(0jc,n) = 
0 and Vp(</>x,m) = 0. So the lemma holds for atomic wff in case (i). For 
case (ii) suppose fi(x)—p(x) = n — m. Then 
V ^ n ) = lifr>(*) = n 
268 


THE COMPLETENESS OF MODAL LPC 
iff fi(x) — m = n —m 
iff fi(x)-m = fi(x)-p(x) 
iff p(x) = m 
iff Vp(<£x, m) = 1 
so the lemma holds for atomic wff in case (ii) also. 
It should be clear that if (i) or (ii) holds of every x free in ~ a and of 
every x free in a V 0 then it holds for every x free in a and /?, and so, 
by the induction hypothesis from (i) and (ii) we have 
VM(a,n) = Vp(a,m) and 
V„(0,n) = Vp(0,m) and so 
V,X~of,n) = Vp(~a,m) and 
VM(a V 0,n) = Vp(a V 0,m). 
Suppose (i) and (ii) hold for La. Note that any x free in La is also free 
in a, and so (i) and (ii) also hold for a in respect of n and m. 
Now suppose VM(La,n) = 1 and suppose k > n, so that nRk. Then 
VM(a,k) = 1. Now every h such that m < h, i.e. every h such that mRh, 
will be such that for some k > n, k—h = n — m. (i.e. k will be as much 
above h as n is above m). Consider every such pair k and h and any x 
free in a. 
(i') 
If JLI(JC) < n and p(x) < m, then certainly fi(x) < k and p(x) < 
h. 
(ii') If fi(x)-p(x) = m-n then ix(x)-p(x) = k-h. 
This means that if (i) and (ii) hold of a in respect of n and m they also 
hold in respect of k and h, and so, by the induction hypothesis V^(a,k) 
= Vp(a,h). But VM(a,k) = 1 and so Vp(a,h) = 1. Since there is an 
appropriate k for every h > m we have Vp(La,m) = 1. 
Suppose VM(La,n) = 0. Then V/i(a,k) = 0 for some k > n, and by the 
same argument as before, where h is the number such that k—h = n—m 
we have Vp(a,h) = 0 for some h > m, and so Vp(La,m) = 0. So the 
induction holds for L. 
Suppose now that V^Vxc^n) = 0. Then V„(a,n) = 0 for some x-
alternative v of jti. We may assume that for every y free in Vjca, i.e. for 
269 


A NEW INTRODUCTION TO MODAL LOGIC 
every y free in a except possibly x> either (i) or (ii) holds. 
Let o be the ^-alternative of p in which v{x)—a(x) = n—m. Then v and 
a satisfy (i) or (ii) in respect of n and m, and so, by the induction 
hypothesis 
Va(a,m) = V„(a,n) = 0 
so 
Vp(V*a,m) = 0. 
If Vp(V;ca,m) = 0 then Va(a,m) = 0 for some jc-alternative a of p. Let 
v be the x-alternative of fi in which v{x) — o(x) = n—m. As before, 
V„(a,n) = Va(a,m) = 0, and so VM(V;ca,n) = 0. This completes the 
inductive proof of lemma 14.12. 
THEOREM 14.14 
S4M + BF is not complete. 
Proof: From lemma 14.12 we have corollary 14.13, from which we 
know that LMa D MLOL is valid in (W,R,D,V) for every wff a. Since 
(W,R,D,V) is reflexive and transitive this means that every theorem of 
S4M + BF is valid in it. But we proved at (A) above that (*) is not valid 
in (W,R,D, V) and so this establishes (II) that (*) is not a theorem of S4M 
+ BF. However, by lemma 14.11, (*) is valid on every frame for S4M, 
and so (*) is valid on every frame for S4M + BF. So not all S4M + BF-
valid wff are theorems, which is to say that S4M + BF is not complete. 
Other incompleteness results 
We mentioned above that incomplete predicate logics are often based on 
modal propositional logics with a long history. Our second example is 
KG1, which is K + 
Gl 
MLp D LMp 
As we mentioned on p. 134 S4 + Gl is called S4.2, and S4.2 + BF will 
be discussed in a moment. We shall first consider the result of adding Gl 
directly to K. KG1 is characterized by the class of convergent frames, i.e. 
frames satisfying 
Vw0Vw1Vw2((w0Rw, A WQRW2) D 3W3(W1R>V3 A w2Rw3)), 
the condition that if a world can see two worlds those two can together 
270 


THE COMPLETENESS OF MODAL LPC 
see a world. Any frame is a frame for KGl iff it is convergent. 
KGl + BF is formed out of KGl in the way described on p. 244 
above. From corollary 13.3 on p. 249, if KGl -f BF were complete it 
would be characterized by the class of convergent frames. So to establish 
the incompleteness of KGl + BF it will suffice to find a non-theorem 
which is valid on every convergent frame - or, what comes to the same 
thing, a consistent wff which cannot be satisfied on any convergent frame. 
Such a wff is 
M(yx(<j>x D L<f>x) A L~VJC0JC) A MVx(<j>x V L<j>x) 
A Vx(M<j)X D L<f>x) 
For S4.2 itself we have to use a different wff. S4.2 (see p. 134) is S4 + 
Gl. It is characterized by frames which are reflexive, transitive and 
convergent, and all its frames have these properties.4 The incompleteness 
of S4.2 + BF follows from the fact that 
M{lx<j>x A VJC(0JC D L\j/x) A L~Vx\px) 
A MVx(<j>x V L\px) 
A Vx(M<i>x D L(3JC0* D <px)) 
is not satisflable on any convergent frame but is consistent in S4.2. We 
shall not give the proofs of these results. The general strategy is the same 
as we used for S4M. 
The monadic modal LPC 
Non-modal LPC is not decidable. That is to say there is no effective 
procedure for deciding, of an arbitrarily presented wff, whether or not it 
is valid, or equivalently, in view of the completeness of LPC, whether or 
not it is a theorem. Nevertheless there are decidable fragments of which 
the most significant is the fragment that contains only one-place 
predicates.5 By contrast the monadic modal LPC is in almost every case 
not decidable. Kripke has in fact proved the undecidability of the monadic 
fragment of any modal LPC whose class of frames contains one with a 
world that can see infinitely many worlds.6 The idea is simple. Suppose 
i£* is a language of non-modal LPC with just a single two-place predicate 
<f>. It is known that logical validity in this language is undecidable. Let i£ 
be a language of modal LPC containing just two monadic predicates \p 
and x and let S be a system which has at least one frame with a world 
which can see infinitely many worlds. Where a is any wff of i£* let its 
translation r(a) in X be obtained by replacing every atomic wff <j>xy by 
271 


A NEW INTRODUCTION TO MODAL LOGIC 
M(\f/x A xy)- First suppose r(a) is not valid in some model (W,R,D,V) 
for S. If a fails at w then let (D*,V*) be a model for i£* in which D* = 
D and (w,v) G V*(0) iff for some \x. such that fi(x) = u and jti(y) = v, 
V^Mtyx A xy)'^) = 1- A straightforward inductive proof establishes 
that V*(a) = 0. Now suppose that V*(a) = 0 in some model (D*,V*) 
for i£* where D* is of the same (infinite) size as the class W of the 
worlds that w* can see in a frame (W,R) for S in which w* can see 
infinitely many worlds. Let 7r be a 1-1 correspondence between W and 
D*, and let (W,R,D*,V) be a model for i£ based on (W,R) in which 
<M,W> G V(i/0 
iff <M,TT(W)) G V*(0) 
and (u,w) 
G V(X) 
iff TT(VV) = 
u. 
Then for every w G W , V^i/a A XV»W) = 1 iff (/iW,w) G V(iZ') and 
M(y) = TT(W). SO V M ( M ( ^ A xy),w*) = 1 iff (/x(jc),/x(y)) € V*(0), iff 
V*(<^>jcy) = 1. A straightforward induction then shows that V*(a) = 0. So 
if we could decide S + BF we could decide the dyadic LPC. 
Exercises — 14 
14.1 
Given that S contains S4, prove that if A is a maximal S + BF-
consistent set of wff with the V-property, then {La:La G A} can be 
extended to a consistent set with the V-property. 
14.2 
Prove the completeness of S4.3 + BF with respect to connected 
frames. 
14.3 
Prove that K + BF is not characterized by the class of finite 
frames. 
*14.4 
Is S4.3.1 + BF complete? 
14.5 (a) Prove that KW -I- BF is not canonical. 
*(b) Is KW + BF complete? 
14.6 
Prove that the wff on p. 134 are unsatisfiable on a convergent 
frame. 
*14.7 
Axiomatize the system characterized by convergent frames. 
Notes 
1 The use of maximal consistent sets to prove the completeness of non-modal LPC 
dates from Henkin 1949. 
2 The proof of theorem 14.2, and its use in completeness proofs for modal 
272 


THE COMPLETENESS OF MODAL LPC 
predicate logic, is due in its essentials to R.H. Thomason 1970a, though 
Thomason considers only S4. The present method replaces the rather elaborate 
construction involving EM-formulae which was given in Chapter 9 of Hughes and 
Cresswell 1968. A somewhat different kind of completeness proof for modal 
predicate systems will be found in Fine 1978, pp. 131-135. Fine proves 
completeness by what he calls the method of 'diagrams' whereby the falsifying 
model for a non-theorem is obtained by forming a maximal consistent set of wff 
annotated by indices which become the worlds of the model. (See also Gallin 
1975.) The earliest application of maximal consistent sets to proving completeness 
for modal predicate logic seems to have been that of Bayart 1959, though Bayart 
only considered S5. Kripke 1959 proves the completeness of modal predicate S5 
by a different method. The method used in Hughes and Cresswell 1968 first 
appeared in Cresswell 1967c and is a generalization of Bayart's method. 
3 The incompleteness of S4M + BF was announced as early as 1967 in Kripke 
1967. The proof we shall give is adapted from one which will appear in a 
forthcoming book by Kit Fine. 
4 The incompleteness of S4.2 -I- BF is stated in Shehtman and Skvorcov 1991, 
though no proof is given in their article in that volume. The incompleteness 
proofs of KGl + BF and S4.2 + BF based on the wff mentioned in the text are 
found in Cresswell 1995b. 
5 See Kalmar 1936 and Church 1936 and 1956, pp. 272-279. 
6 Kripke 1962. Kripke's proof is in fact for all subsystems of S5, but it is not 
difficult, as we show, to see that his method applies to any system whose frames 
contain a world that can see infinitely many worlds. There are of course modal 
systems, such as the Alt systems mentioned on p. 142, whose frames do not 
include such frames. 
273 


15 
EXPANDING DOMAINS 
Validity without the Barcan Formula 
The definition of validity which we gave for modal predicate calculi in 
Chapter 13 is one which makes (every instance of) the Barcan Formula 
come out as valid, and in Chapter 14 we showed how to define a 
canonical model for S + BF, whatever normal system of propositional 
modal logic S might be. We remarked however, although we did not 
prove this, that although for some choices of S, e.g. any S that contains 
B, BF is a theorem of LPC + S, for others it is not. The question 
therefore arises of how to give an account of validity for LPC + S which 
does not always validate the Barcan Formula. 
This is not a question with a merely formal interest, for a number of 
objections have been brought against the validity of the formula from an 
intuitive point of view.1 It is convenient here to consider the Barcan 
Formula as the wff 
VxLfa D LVx<j>x 
Under the standard interpretation what this means is that if everything 
necessarily possesses a certain property <f>, then it is necessarily the case 
that everything possesses that property. But now, it is sometimes argued, 
even if everything that actually exists is necessarily <f>, this does not 
preclude the possibility that there might have existed some other things 
which were not (j> — and in that case it would not be a necessary truth 
that everything is <j>. 
This objection to the Barcan Formula depends on the assumption that 
in various 'possible worlds', not merely might objects have different 
274 


EXPANDING DOMAINS 
properties from those they have in the actual world, but there might even 
be objects which do not exist in the actual world at all. Now it is at least 
plausible to think of the semantics we have given for modal predicate 
calculi as implicitly denying this assumption, for in each model we have 
had a single domain of individuals, the same for each world. The validity 
of the Barcan Formula is in fact connected with this feature of our 
semantics. And this suggests that we might obtain a semantics which does 
not bring the formula out as valid, by admitting models in which different 
domains are associated with different worlds. We shall now show how 
this can be done. 
For systems without the Barcan Formula a model is a quintuple 
(W,R,D,Q,V) in which W,R and D are as before, and Q is a function 
from members of W to subsets of D. Q(w), usually written D„, is the set 
of individuals which 'exist' in vv. Models satisfy the inclusion 
requirement, that if wRw' then Dw Q Dw,. But before we can look at the 
rules for assigning truth-values to wff in models for systems without BF 
we will have to look at the following question. In a wff like <px in which 
x is free what happens in a world vv in which x is assigned as a value an 
individual which is not in Dw? One way of avoiding this question would 
be to prohibit such assignments altogether and we shall look later at what 
kind of semantics you get when you do. But for now we shall take it that 
such cases can arise. Another way, which actually turns out to be 
equivalent, is to say that <j>x lacks a truth-value in such worlds.2 A third 
way, the way we shall choose,3 is to say that it is either true or false, just 
as when x is assigned something which is in Dw. Which of these values 
it has of course is up to the model, since the value of <j> will deliver in 
each world the set of things which satisfy <j>. So [V<£], [V ~ ] , [V V ] and 
[VL] remain as they are, but [Vv] becomes 
[Vv'] 
V^(V;ca,vv) = 1 if Vp(a,w) = 1 for every jc-alternative p of \x 
such that p(x) G Dw and 0 otherwise. 
A wff is valid in a model (W,R,D,Q,V) iff for every world vv €E W, 
V,i(a,w) = 1 for every assignment \k such that fi(x) G Dw for every 
variable x. a is said to be eligible at vv with respect to \x iff \x(x) G Dw 
for every x free in a. This means that another way of defining validity 
would be to say that a wff is true at every world at which it is eligible. 
The inclusion requirement guarantees that if a is eligible at vv with respect 
to ix it remains eligible at every world vv can see. Without this 
requirement such theorems as L(yx<f>x D <f>y) need not be valid. (We shall 
275 


A NEW INTRODUCTION TO MODAL LOGIC 
consider such systems in the next chapter.) Both PR and PA hold in these 
semantics for the same reasons as they hold for the semantics which 
validates BF. 
The proof that every theorem of LPC + S is valid in every model in 
which every instance of a theorem of S is valid is by induction on the 
proofs of theorems of LPC + S. Although straightforward it is necessary 
to take care at certain points. The validity of every substitution-instance 
of a theorem of S follows for the same reason as for systems with BF. 
The first hint of trouble comes with VI. Look first at the simplest instance 
of this schema 
(1) 
Vx<j>x D <f>y 
Consider a world w and some assignment fi such that fi(y) & Dw. 
Suppose that (u,w) G V(<j>) for every u € Dw, but that (ti(y),w) £ V(<£). 
Then (1) will be false at w. However, this possibility is ruled out by 
defining validity as truth in every world w, with respect to every 
assignment whose values are all in Dw. And if that condition is satisfied 
by ix then (1) will be true in every w, and so will be valid. For the 
general case suppose that V/t(Vjca,w) = l and that \x, gives values only 
from Dw. Let p be the ^-alternative of /i such that p(x) = /x(y). Since /x(y) 
E D„ then p{x) E D„, and so, by [ W ] , Vp(a,n>) = 1. So, by PR, 
VM(a[y/jc],w) = 1. Thus Vl is valid. 
MP preserves validity in a model of the present kind for the same 
reasons as it preserves validity in models for the systems which contain 
BF. 
For necessitationsuppose that V^La^w) — 0 for some wG Win some 
model (W,R,D,Q,V) where \K{X) E DW for every variable x. Then for 
some w' such that wRw', V^a.w') 
= 0. Since wRw' the inclusion 
requirement ensures that JLC(JC) G DW, for every variable x, and so a is not 
valid either in (W,R,D,Q,V). (Note that it is at this point that the 
inclusion requirement is invoked, for if fi(x) E Dw but /*(*) £ Dw, for 
some x, a might be valid. In fact without the inclusion requirement, 
although Vx<j>x D <f>y is valid, L(Vx<j)X D <j>y) is not.) 
Given PA, V2 is validity-preserving for the same reasons as in the 
semantics for systems with BF. 
So every theorem of LPC + S is valid according to the present 
criterion. Yet it is easy to see that BF is not always a theorem of LPC + 
S.4 Take S to be K and take the simplest instance of BF: 
276 


EXPANDING DOMAINS 
(2) 
VxL<j)X D LVx<j>X 
Consider the following model: 
W = {wi,w2}, w1Rw2> D = 
{ulyii2}, 
Q K ) = {«,}, Q(w2) = D, V(0) = «ifI,w1>, (ulyw2)}. 
This model may be pictured in the following way: 
Domain 
I 
W2 
(j>U{ 
{uuU2} 
In this model everything in Dw , i.e. w,, satisfies <f> in every world and so 
VxL<f>x is true there. But in w2 Vx(f>x is false and so in wl, D4x<j>x is false. 
To show this more formally let ix be any assignment whose values are all 
taken from Dw . In fact /i(y) will have to be w, for every variable y 
including x. And the only ^-alternative of /x whose values are all in Dw 
is \k itself. But by V(<£), V ^ ^ w , ) - 1 and VM(0JC,W2) = 1, and so 
VM(L<£;C,H>,) = 1, and so V^VJC^W,) = 1. So the antecedent of BF is 
true at w, in this model with respect to \k. But consider the jc-alternative 
p of \i such that p(x) = i^. Since u2 G D , p takes all its values from 
Dw , and so VJ\/x<f>x,w2) = 0. Since WJRH^, VM(LVJ:0JC,W,) = 0, and thus 
BF fails in this model. 
The model can be made a T-model, indeed an S4-model, by requiring 
that WjRw, and w2Rw2. This would not affect the proof. In conjunction 
with our soundness result this shows that BF is not a theorem even of 
LPC + S4. However if we move to B and require that R be symmetrical 
we cannot preserve the inclusion requirement. For if R is symmetrical 
then the inclusion requirement guarantees that if wRw' then Dw = Dw>, 
and this is enough to validate BF. (In fact it has the consequence that in 
any frame which is cohesive, in the sense of p. 137, Dw = Dw, for every 
w and w' G W.) 
Undefined formulae 
We have already mentioned the problem of what to do about wff which 
appear to refer to non-existent objects. And we have said that an atomic 
277 


A NEW INTRODUCTION TO MODAL LOGIC 
wff <£jc,...;cn is either true or false in a world w, i.e. it has a truth-value 
in w, whether or not the individuals assigned to xx, ... , xn are in Dw or 
not. Of course when we come to evaluate quantified wff in w, V speaks 
of everything in Dw and 3 of something in Dw. But it might be held that 
we ought not to be allowed even to speak of things which do not exist, so 
that e.g., if fi(x) is not in Dw then W^x^w) ought to be neither true nor 
false. It ought to have no value at all or to be undefined. We shall not 
take sides on whether this is or is not a philosophically reasonable reply, 
but what we shall do is show that, as far as the validity of wff of modal 
LPC is concerned, it makes no difference whether or not wff have truth-
values at worlds where their variables are assigned elements from outside 
the domain of that world. 
In order to prove this we need to be precise about how the values of 
wff are obtained when we allow undefined wff. We first note that a model 
for such a semantics will not differ in W, R, D, or Q from a model as 
defined on p. 275. Nor will an assignment V to the predicates, and nor 
will an assignment \L to the individual variables. What will differ is the 
way values are assigned to wff. So where (W,R,D,Q,V) is a model of the 
kind already defined we shall use the notation V^*(a,w) to mean the value 
assigned to a according to /i, when wff are undefined at a world w where 
not all their free variables are assigned values not in Dw. The rules for 
evaluating wff are as follows: 
[V*<£] V/i*(^1...jcnw) = 1 if each of JH(*J), ... , fi(xj € D„ and </i(x,), 
... , /x(>0,w) G V(</>). VM*(#z,....*n,w) = Oifeachof/x(Xj), ... , 
MW G DW, but (/x(*,), ... , ii(xj,w) 
£ V(0). Otherwise 
V,t*(<A*i> ••• yXQ,w) is undefined. 
[V*~] For any wff a, V ^ — c^w) = 1 if VM*(a,w) = 0 and 
V *(~of,w) = 0 if V^iciyW) = 1 and is undefined otherwise. 
[V*V] VM*(a V 0,w) is defined iff both VM*(a,w) and VM*(j8,w) are 
defined and if defined, V^*(a V 0,w) = 1 if either V^*(a,w) = 
1 or V *(jS,w) = 1 and 0 otherwise. 
[V*L] V/1*(La,w) is defined iff V/t*(a,w') is defined for every w' such 
that wRw'. If it is defined then V„*(La,w) = 1 iff VM*(a,w') = 
1 for every w' such that wRw', and 0 otherwise. 
[V*V] V^iVxetyW) = 1 iff Vp*(a,w) = 1 for every jc-alternative p of /x. 
such thatp(jc) € Dw. V^*(\/xa,w) = 0 if Vp*(a,w) = 0 for some 
jc-alternative p of (x such that p(x) G Dw, and is undefined 
otherwise. 
278 


EXPANDING DOMAINS 
We say that a is valid* iff for every w G W and every /x, V/i*(a,w) = 
1 whenever V/i*(a,w) is defined. What we have to show is that validity* 
is exactly equivalent to the more 'classical' account of validity for systems 
without BF. So let (W,R,D,Q,V) be a model. 
THEOREM 15.1 Let a be any wff, let w G W and let \K be any 
assignment. Then, if /X(JC) G Dw for every x free in a, 
(i) VM*(a,w) is defined 
and 
(ii) VM(a,w) = V ( a , w ) . 
The proof is by induction on the construction of a. First suppose a is 
atomic, say <f>xx...xn. Then by [V*<£], Vf*(<faxl...xn,w) is defined if fifa), 
... , /i^J are all in Dw, and so (i) holds. And by [V</>] and [V*<£] we 
have V/i(^1...^n,w) = 
1 iff 04*,), .- 
, MW,w) G V(tf) iff 
V/t*(#*,...*n,w) = 1 and V ^ , . . . * ^ ) = 0 iff </x(x,), ... ,n(xj,w) 
£ 
V(0) iff VM*(^x,...xn,w) = 0. So the theorem holds for atomic wff. 
Suppose the theorem holds for a and 0 in respect of a world w. Then 
by [V*~] V^i — oiyW) will be defined iff VM*(a,H>) is, and so will be 
defined if fi(x) G Dw for every JC free in a. For such a /*, we have by 
[V*~] and [V*V], and the induction hypothesis, V^(~a,w) = 1 iff 
V^(a,w) = 0 iff VM*(a,w) = 0 iff VM*(~a, w) = 1. VM(~a,u>) = 0 iff 
VM(a,w) = 1 iff V^*(a,w) = 1 iff V/C-a.w) = 0. 
For V we have that VM*(a V /?,w) is defined iff both V/i*(a,w) and 
V^*(j3,w) are defined. By (i) for a and /? this will be so if/X(JC) G Dw for 
every ;c free in a, and /x(x) G Dw for every x free in $. Since these are 
precisely the xs free in a V /J we have (i) in respect of a V /?. Given 
such a jLt, [V V ] and [V* V ] give the same results in a manner analogous 
to the case for ~ . 
Suppose that the theorem holds for a. This means that for any w G 
W, we may assume that it holds for a in respect of every w' such that 
wRw'. Now suppose that fi(x) G Dw for every x free in La. Consider any 
w' such that wRw' and any x free in a. If x is free in a then it is free in 
La and so JX(X) G Dw. So, by the inclusion requirement, [i(x) G D^, and 
so, by the induction hypothesis, V^*(a,w') is defined. Since this is so for 
every w' such that wRw', VM*(La,w) is defined and so (i) holds of La. 
Further, if VM*(a,w') is defined for every w' such that wRw' [VL] and 
[V*L] give the same results in a manner analogous to the case for —. 
Suppose that the theorem holds for a and consider Vxa. Suppose that 
279 


A NEW INTRODUCTION TO MODAL LOGIC 
n(y) G Dw for every y free in Vxa. Where p is any jc-alternative of /x 
such that p(x) G Dw, then p(y) G Dw for every v free in a, including *. 
So, assuming that the theorem holds for a, Vp*(a,w) is defined for every 
such p, and in that case [VV] and [V*V] give the same result. 
This means that in any model (W,R,D,Q,V) for any wff a and any w 
€ W, VM(a,w) = 1 for every [i such that /*(*) G Dw for every x, iff 
VM*(a,H>) = 1 for every \k such that /x(x) G Dw for every JC. In other 
words a is valid iff a is valid*. 
Canonical models without BF 
For systems without BF we form the canonical model as follows. As 
before we assume two languages ££ and i£+, the latter with infinitely 
many variables not in i£. But now we can allow the domains to vary, and 
we do this by letting each world w in the canonical model be a maximal 
consistent set of wff of a language !£w which contains all the variables of 
X and possibly some of the new variables of ££+, provided that there are 
infinitely many variables of X+ not in !£w. (From here on we shall use 
the following terminology. Where A Q B we shall say that A is an 
infinitely proper subset of B iff there are infinitely many members of B 
not in A. When we say that a language i^ is an infinitely proper 
sublanguage of a language ££' we mean that i£ and i£' contain the same 
predicates, and the variables of ££ are an infinitely proper subset of the 
variables of ££'.) 
THEOREM 15.2 If —La G w then there is a maximal consistent set w' 
with the V-property in a language Xw, containing ££w 
such that Lr(vv) U {-a} Q w'. 
Proof: Let 5Bw. be an infinitely proper sublanguage of X+ such that !£w is 
an infinitely proper sublanguage of ££w, containing infinitely many of the 
variables of i£+ not in !£w. Since w G W then !£w lacks infinitely many 
variables of i£ + . Now L~(w) U { — «} is consistent by lemma 6.4 on p. 
117, and further L~(w) U { — a} is taken from the language ££w. Since 
££„, contains infinitely many variables not in !£w then theorem 14.1 
guarantees that L~(w) U { ~ a} has a consistent extension A with the V-
property in ££w,. And by theorem 6.3 on p. 115, A has an extension w' 
which is maximal consistent. 
The canonical model then for a system LPC + S in a language X with 
an extension ££+ is a quintuple (W,R,D,Q,V) where W is the set of all 
maximal consistent sets with the V-property in some sublanguage of ££+; 
280 


EXPANDING DOMAINS 
and wRw' iff, for every La G w, a G w' (i.e. L~(w) Q w'). D is the 
set of variables in ££+ and Q(w), i.e. Dw , is the set of variables in Z£w. 
Where x € Dw then L(<£JC D <£;C) € w and so where wRw', <j>x D <}>x G 
w' and thus x € Dw, , i.e. i£w is a sublanguage of f£w, when wRw' and 
so the inclusion requirement is satisfied. (JCJ, ... ,*n,w>) G V(^)iff^Cj...jcn 
G w. 
Finally take the 'canonical' value-assignment a to be the assignment 
such that o(x) = JC, for every variable x in D. We prove the following 
theorem: 
THEOREM 15.3 For any w G W, and any wff a G i£w, Va(a,n>) = 1 iff 
a G w. 
The proof parallels that of theorem 14.3 on p. 261. However the 
members of W are all in different sublanguages of i£ + , and so care is 
needed in the various inductive steps. For that reason we shall set the 
proof out in full. First consider any atomic wff <f>xx...xn. 
(a) 
V0(^1...^n,w) = 
1 iff {o(xx\ 
... 
,O(JO,W) G V(<«, iff 
(*„ ... ,*n,w) G V(<£), iff <f>xx...xn G w. 
(b) 
Suppose ~ a G i£w. Then a G 56w, and then V0(~a,w) = 1 iff 
Va(a,w) = 0, iff a g w, iff ~ a G w iff Va(~a,w) = 1. 
[In (b) it is important that a G !£w since first, the induction hypothesis 
only applies to such wff, and second since w is maximal consistent only 
in 5£w, it is only ifa G i£w that we can guarantee that if a £ w then ~ a 
G w.] 
(c) 
Suppose a V 0 G ££„. Then a G i£w and 0 G ££„. Then, Va(a 
V 0,w) = 1 iff Va(a,w) = 1 or Va(0,w) = 1 iff a G w or /J G 
w, iff a V jS G w. [As with (b) it is crucial that a, (3 and a V 
0, all be in 2W.] 
(d) 
Suppose Vjca G w. Then Vjca G i£w. Now let v be any JC-
alternative of a such that v(x) G Dw. This means that v(x) = y 
for some variable y in ££w. So a[y/jc] G i£w, and so by Vl, 
a[y/x] G w. So Va(a[y/jc],w) = 1. So by PR, V,(a,w) = 1. 
Since J> is any ^-alternative of a, such that v{x) G Dw, Va(Vjta,w) 
(e) 
Suppose Vjca G i£w but V;ca ^ w. Then ~V;ta G w and so, 
281 


A NEW INTRODUCTION TO MODAL LOGIC 
since w has the V-property in ££„, there is some y in i£w such that 
~ a\y/x] G w. So a[y/x] & w and since a\ylx\ G ££„, 
Va(a[y/jc],w) = 0. So by the validity of Vl, Vff(Vxa,w) = 0. 
Suppose La G w and wRw'. Then a G w', and so a G Xw,. So 
Va(a,w') = 1, and since this is so for every w' such that wRw', 
Vff(La,w) = 1. 
Suppose La G i£w but La & w. Then since w is maximal 
consistent in !£w, —La G w. But then by theorem 15.2 there is 
some w' G W with the V-property such that — a G w' and 
wRw'. So a £ w'. But <£w, is an extension of ££w and a G i£w, 
so a G i£w, and so Va(a,w) = 0. But wRw' and so Va(La,w) 
= 0. 
This proves theorem 15.3. 
Completeness 
As a result of theorem 15.3 we know that for any wff a, a is valid in the 
canonical model of LPC + S iff (-LPC + s a. This construction can be 
carried out for any normal modal logic. As before completeness is 
forthcoming for all those systems S in which the frame of the canonical 
model for LPC + S, constructed as in the last section, is a frame for S. 
It is not difficult to see that this is so for K, D, T, S4, and a number of 
other systems we have discussed. 
The definition of R entails that if wRw' then Xw is a sublanguage of 
££w,. But also, at least some of the worlds w' such that wRw' will be in 
languages with additional variables, and in these cases we cannot have 
w'Kw. So R cannot be symmetrical. This means that for systems like 
extensions of the system B, in which the Barcan Formula is a theorem, 
the models produced will not be ones in which R is symmetrical, and so, 
although they will be models for these logics, they will not be based on 
frames for these logics, and so cannot be used to give completeness 
proofs for these systems.5 For extensions of B, BF is provable, and so the 
method of Chapter 14 can be used to establish completeness. There are 
however systems for which neither method on its own will work. 
Consider the system K + ML(p A ~p) V (q D LMq). This system is 
characterized by frames in which, for every world w, either w can see a 
dead end, or else if wRw' then w'Rw. In a frame whose only worlds are 
w, and w2 where w,Rw2 and w2 is a dead end BF can easily be falsified, 
and so the method of Chapter 14 will not work. But the method of the 
282 


EXPANDING DOMAINS 
present chapter will not work either since the consistency of LM(p D p) 
A p A ~Lp requires a pair of worlds w and w' in the canonical model 
with w 7* w', wRw' and vv'Rw, and that is what the method of the 
present chapter will not guarantee. 
Incompleteness without the Barcan Formula 
It is not hard to show that the analogues of theorems 13.1 on p. 247 and 
13.2 on p. 248 still hold for systems without the Barcan Formula. Our 
soundness result on p. 276 gives 13.1, and the proof of 13.2 remains the 
same, since the differing domains only become relevant in the 
interpretation of the quantifiers, and the wff a used in that theorem is 
quantifier free. To establish the incompleteness of a system we show that 
some wff valid on all frames for S is not a theorem of LPC + S. (Or that 
a wff unsatisfiable on every frame for S is nevertheless consistent in LPC 
+ S). 
Our first result is that LPC + S4M is incomplete. Clearly (*) on p. 
266 is not a theorem of LPC + S4M since it is not a theorem of S4M + 
BF. So all we have to show is that it is valid on every final frame. Look 
at the proof of (I) on p. 265. According to our present semantics, given 
that V^lxfayW') = 1 for some final world w', we have that Vp(0;c,w') = 
1, where p is some ^-alternative of ^ and p(x) G Dw>. Since w' is final 
Vp(L(f>x,w') — 1, and since no other world is involved p(x) is still in Dw,. 
Then the proof proceeds as before. So LPC + S4M is not complete 
either. 
The situation is different with S4.2. S4.2 + BF is, as we remarked, 
not complete. Yet LPC + S4.2 is complete,6 and it is not hard to see 
why. If you look at the completeness proof of S4.2 on p. 134 you will see 
that it proceeds by establishing that in the canonical model for S4.2 if 
W,RH>2 and w,Rw3 then L~(w2) U L~(w3) is consistent. This result still 
holds in predicate logic. However the problem is to give it a maximal 
consistent extension with the ^-property, and that is what cannot be done 
in S4.2 + BF. But for systems without BF we can use theorem 15.2. 
For, since L~(w2) U L~(w>3) is consistent it will certainly have a maximal 
consistent extension in a language with infinitely many new variables. 
And that fact is all that we need for LPC + S4.2. 
LPC + S4.4 (S4.9) 
The systems we now go on to consider provide examples in which the 
predicate extension is incomplete without the Barcan Formula, but 
complete with it,7 and include systems properly between S4.3 and S5. For 
283 


A NEW INTRODUCTION TO MODAL LOGIC 
definiteness we shall consider only two. One is the system S4.48 which 
is S4 + 
Rl 
p D (MLp D Lp) 
The other is one called S4.9.9 This is S4.4 + 
M18 
(MLp D p) V (LMq D MLq) 
54.9 has the property that there is no system properly between it and 
55.10 S4.4 is characterized by reflexive and transitive frames satisfying 
(1) 
(WjRWj A W, 5* W>2 A H>,Rw3) D VV3RW2 
Further, any reflexive and transitive frame is a frame for S4.4 iff it 
satisfies (1). 
It is not difficult to show that the canonical model for S4.4 + BF, 
constructed in the manner described on p. 261 above satisfies (1). For if 
wi 5* w2 then there must be a E wx such that a $. w2, and so ~ a E 
w2. And if not w3Rw2 then there must be some L0 E vv3 such that ~ /? E 
w2. Since L(3 E w3, L(a V /?) E w3 and so ML(a V ff) E w,. Since a 
E wl9 (a V (3) E w„ and so, by Rl, L(a V 0) E w,. But W!Rw2 and 
so a V /? E w2, contradicting the presence in w2 of —a and ~(3. 
For this proof to work we have to know that because a £ w2 and (3 $. 
w2 then —a £ w2 and — 0 E vv2. In the canonical models of systems 
without BF this cannot be guaranteed since, e.g., a may fail to be in w2 
because it contains a 'new' variable not in the language of w2, and so —a 
may not be in w2 either. And in fact we shall see that LPC + S4.4 is not 
complete, and nor is LPC + S4.9, and in fact no system properly 
between LPC + S4.3 and LPC + S5 is complete. To prove the 
incompleteness of LPC + S4.4 and LPC + S4.9 we shall show that the 
wff 
(C) L(VxML<j>x A lx~<j>x) 
is consistent in LPC + S4.9 (i.e. its negation is not a theorem) yet any 
transitive and reflexive frame on which it is satisfiable must satisfy the 
condition 
(2) 
awoVw^WoRwj D 3w2(wxRw2 A — w2Rw,)) 
284 


EXPANDING DOMAINS 
This will be shown in theorem 15.4. What (2) means is that in extensions 
of S4.3 the frame must contain an infinite chain of clusters. It is not hard 
to see that Rl fails on such a frame. For suppose we have even three 
worlds w,, w2 and w3 with WjRvVj iff i < j . Then, with V(p,H>!) = V(/?,w>3) 
= 1 and V(p,w2) = 0 we have Rl false at w,.11 
THEOREM 15.4 If (C) is satisfiable on a transitive and reflexive frame & 
then ^satisfies (2). 
Proof. Suppose that for some w0 G W in ^~, V^{LiyxML^x A lx~<j>x)y 
w0) = 1 and suppose that WQRVV, . Then 
(3) 
VflxMLfa 
A 3JC ~0JC, wx) = 1. 
So there is an jc-alternative p of n such that p(x) G Dw and 
(4) 
Vp(-</>*,w.) = 1. But 
(5) 
Vp(ML<t>x,wx) = 1 
and so there is some w2 with WJRH^ such that 
(6) 
V„(Ltf*,w2) = 1. 
Now suppose w2Rw,. Then Vp(0^,Wi) = 1, which contradicts (4). So not 
w2Rw,, as required for (2). 
Since no frame for Rl satisfies (2) (C) is unsatisfiable on every frame 
for S4.4. So the negation of (C) is valid on every frame for S4.4, and 
therefore also on every frame for S4.9. We now produce a model in 
which (C) is satisfiable, i.e., ~(C) is not a theorem, and in which the 
theorems of S4.9 are all valid. Since R will be transitive and reflexive it 
will be sufficient for the latter purpose to show that Rl and M18 are true 
at every world. The model © is defined as follows. W is a denumerable 
set and WJRWJ iff i < j . D consists of the natural numbers, and Q(Wj) = 
{0, ... ,i}. For any predicate \f/ except <f>, V(^) = 0 . For 0, (w,wn) E 
V(0) iff u < n. Thus the model looks like this: 
285 


A NEW INTRODUCTION TO MODAL LOGIC 
Domain 
w0: 
- 0 0 
{0} 
w,: 
00 
- 0 1 
{0,1} 
w2: 
00 
01 
- 0 2 
{0,1,2} 
etc 
THEOREM 15.5 (C) is true in (5 at vv0. 
Proof: It should be clear that at every world 3* — <f>x is true, since at vvn, 
n is in Dw but (n,wn) £ V(0). Further, for every u G Dw , for all m > 
n, (w,wm) € V(0) and so VJCML0JC is true at wn. This means that for every 
fx and every w G W, 
(7) 
V^VxMLfa 
A 3JC~0X,W) = 1. 
So, since w0Rw for every w G W, 
(8) 
V^LfrxMLfa 
A 3JC~0JC),WO) = 1. 
This proves theorem 15.5. 
Since R is reflexive and transitive, to show that (£ is an S4.9-model 
(and therefore an S4.4-model) it will suffice to show that both Rl and 
M18 are valid in (£. In order to do this we note that every wff has a 
certain property. Recall that we say that a wff a is ineligible in w with 
respect to /x. iff fi(x) £ Dw for some x free in a. Note that if a is eligible 
at a world with respect to an assignment, it remains eligible at all worlds 
that world can see, with respect to the same assignment. With respect to 
any given assignment JLI, any wff a gets at most one chance to change its 
truth-value, and that is immediately after the first world at which it 
becomes eligible. This may be proved by a somewhat tedious induction 
on the construction of wff. Given this we may conclude that Rl and Ml8 
are valid in (£. First consider an instance of Rl, a D (MLa D La). 
Suppose this is eligible at vvn with respect to some assignment /x and 
suppose that a is true at wn. Then either it is true from vvn on, or it is true 
at wn and false from then on. But if MLa is true at wn, a cannot be false 
at wm with m > n, and so a must be true from n on, making La true at 
286 


EXPANDING DOMAINS 
wn. For Ml8, ifLMa is true at wn then a can never become false forever 
and so, since it only gets one chance to change its truth-value as soon as 
it becomes eligible, it must eventually become true forever, and so MLa 
must also be true at wn. This means that Rl and M18 are true in this 
model whenever they are eligible, and so are valid in (£. Since (C) is 
satisfiable on this model its negation is not a theorem even of LPC + 
S4.9. Since the negation of (C) is valid in LPC + S4.4 neither LPC + 
S4.4 nor LPC + S4.9 is complete. 
Exercises — 15 
15.1 Explain why the model on p. 277 shows that BF is not a theorem of 
LPC + S when S is S4.9, KW, MV. 
15.2 Prove the completeness of LPC + S4.2 with respect to reflexive, 
transitive and convergent frames. 
15.3 Prove the completeness of LPC + S4.3 with respect to reflexive, 
transitive and connected frames. (Corsi, 1993.) 
15.4 Let S be K + ML(p A ~p) V (q D LMq): 
(a) Show that ML(Vxa A ~V;ca) V (VjcLa D LVxa) is valid on all 
frames for S. 
*(b) Is ML(Vxa 
A ~V;ca) V (VjcLa D LVxa) a theorem of 
LPC + S? 
*(c) Prove the completeness of LPC + S + ML(Vxa A ~V;ta) V 
(VxLa D LVxa) with respect to the class of frames in which for any w 
E W, either w can see a dead end or else for every w', if wRw' then 
w'Rw. 
15.5 Let S be K + p D LMMp: 
(a) Show that BF is valid on all frames for LPC + S. 
*(b) Is BF a theorem of LPC + S? 
Notes 
1 One of the earliest of these objections is found in Prior 1957, pp. 26-28 and 
passim. There is also a discussion in Hintikka 1961. For an objection of a 
somewhat different kind vide Myhill 1958, p. 80. For a defence of the formula 
vide Barcan (Marcus) 1962, pp. 88-90 and Cresswell 1991. 
2 That was the way we proceeded in Chapter 10 of Hughes and Cresswell 1968. 
It is discussed below on pp. 277-280. 
287 


A NEW INTRODUCTION TO MODAL LOGIC 
3 We are following Kripke 1963b. On p. 86n Kripke points out that it might be 
tempting to require that if (w,w) E V(<£) then u E Dw, but although this would 
make <f>x false for every atomic wff when JC has a value not in Dw it would make 
every ~ <f>x true for every such value. This requirement would have the curious 
consequence that, for instance, (<f>y A VJCQ:) D ot\ylx\ would always be valid but 
(~<f>y A Vxa) D a[y/x] would not. 
4 A proof that BF is not a theorem of LPC + S4 is found in Lemmon 1960b. 
5 Bowen 1979 contains completeness proofs for various modal systems along the 
lines of the present section. 
6 Corsi and Ghilardi 1989. 
7 These systems have been discussed in Ghilardi 1991 using methods from 
category theory. The proof summarized here appears in more detail in Cresswell 
1995b. See also Corsi and Ghilardi 1992. 
8 See Hughes and Cresswell 1968, p. 263. 
9 Zeman 1973, p. 266 
10 Zeman 1973, pp. 273-275. 
11 Ghilardi 1991 shows how to extend this result to all proper extensions of S4.3 
which are properly contained in S5. (This includes S4.3.1.) We shall however 
continue to focus on S4.4 and S4.9. In extensions of LPC + S4.3.1 weaker than 
S4.4 we would have axioms which would allow longer finite chains, but if a 
system allows finite chains of arbitrarily high length then it must be contained in 
LPC + S4.3.1. This shows that extensions of LPC + S4.3.1 contained in LPC 
+ S4.9 are all incomplete since they do not contain the negation of (C). For a 
proof of (C) in S4.4 + BF see the solution to exercise 13.4. 
288 


16 
MODALITY AND EXISTENCE 
Changing domains 
It is not hard to see that models for systems containing the Barcan 
Formula are a special case of models for systems without it. For a model 
will satisfy BF provided Q(w>) = D for every w € W. So if you want the 
quantifiers in each world to range only over the things that exist in that 
world, and you don't believe that the same things exist in every world, 
you would probably not want the Barcan Formula. However you would 
probably not want its converse either. For consider 
(1) 
LVx<j>x D VxL<j>x 
It could happen that in every world everything which exists in that world 
is <f>, but that something in our world fails to be <j> in some other world. 
Of course that other world will be a world in which the object in question 
does not exist. 
This situation does not of course satisfy the inclusion requirement, and 
it is the inclusion requirement which is responsible for the validity of the 
converse of the Barcan Formula. In terms of plausibility it might even be 
held that the converse of BF (BFC) is less plausible than BF itself. For 
it would seem not too difficult to point to something which actually exists 
and say that might not have existed. But it doesn't seem possible to point 
to something which doesn 't exist and say that might have existed; which 
means that it is more plausible to suppose that an accessible world could 
contain fewer individuals rather than more, and that is exactly the reverse 
of what the inclusion requirement dictates. So what we must do now is 
examine what happens if we abandon the inclusion requirement. 
289 


A NEW INTRODUCTION TO MODAL LOGIC 
The first thing we notice is that with the definition we have used up to 
now, abandoning the inclusion requirement means that the rule of 
necessitation no longer preserves validity. For although 
(2) 
Vx<j>x D <j>y 
is valid 
(3) 
L(Vx<j>x D <j>y) 
is not. For consider a model like this: 
Domain 
Wx 
<j>Ux 
<j)U2 
{Wi>«2} 
4 
w2 
<j>ux 
~<}>u2 
{ux} 
(This model is of course incompatible with the inclusion requirement.) 
Where fi(y) is u2 then (2) is false at vv2, and so (3) is false at w,. Since 
fi(y) G Dw this means that (3) is not valid. 
Perhaps we should insist that the variables of a should be assigned 
values from the domains of the evaluation world and all the worlds in the 
posterity of w, where this is defined to be the smallest set POSw such that 
(i) 
w e POSW. 
(ii) If w' E POSw and w'Rw" then w" € POSw. 
But that will not do either since, although such a semantics validates 
(4) 
LVx<j>x D L<f>y 
(because if y's value is in the domain of every world accessible from w 
and if Vx<}>x is true in every such world then L<j>y must be also), its 
universalized version 
(5) 
Vy(LVx<j>x D L<j>y) 
290 


MODALITY AND EXISTENCE 
is not valid, since despite (4)'s validity it can still be false when y is 
assigned something in Dw which is not in some accessible w' and which 
does not satisfy <f> in w' even though everything in Dw, is <f>, and that is 
enough to show the invalidity of (5). Now, one can save the situation by 
changing the evaluation rule for the quantifier so that it reads 
[VV"] Vxa is true at a world w iff a is true at w for all assignments to 
x which assign it some u which is in the domain of every world 
in the posterity of w. 
The reason this works is the following. Let us define D+ to be the set 
such that u G D+ iff u is in the domain of every world in the posterity 
of w. Then [VV"] is just the usual rule except that D+ is used as the 
domain instead of Dw. So although it may look as if Dw is the domain of 
things existing in w the real domain is D*, and when we look at D+ we 
notice an interesting fact. Suppose wRw'. Then if u is in the domain of 
every world in the posterity of w it is certainly in the domain of every 
world in the posterity of w'. In other words if wRw' then D+ Q Dwt. And 
that means that the + domains satisfy the inclusion requirement and we 
are back to the semantics given on p. 275. 
The semantics we are using at present requires all wff to be defined, 
i.e. to have a truth-value, at every world, even when their free variables 
are assigned values which do not exist in that world. We shall show that 
allowing undefined wff does not help when we drop the inclusion 
requirement. On pp. 277—280 we showed that, given the inclusion 
requirement, admitting undefined wff does not change the logic. We shall 
now show that even without the inclusion requirement the semantics given 
there for undefined wff validates (l).1 
Suppose that a model satisfies [V*<£] — [V*V] on p. 278 and that for 
some w E W and assignment /*, V/i*(LVjc</>jc,w) = 1 and V\*(yxL4>xyw) 
= 0. From the former, if wRw' then by [V*L], VM*(VJC<£JC,H>') = 1. From 
the latter by [V*V] there is an ^-alternative p of \i (with p{x) € DJ such 
that Vp*(L0;c,vv) = 0. So by [V*L] there is some w' such that wRw' and 
VP*(0JC,W') = 0. Further, Vp*(<f>x,w') is defined and so, by [V*0], p(x) 
G Dw.. So, by [V*V], VM*(VJC<0*,W') = 0, contradicting the fact that 
V*(lXx<t>x,w) = 1. 
One might be tempted to propose an alternative evaluation rule for V 
to cover the undefined cases. One might say that VxL<j>x is true provided 
L(j>x is true where defined for every value u of x taken from Dw. 
291 


A NEW INTRODUCTION TO MODAL LOGIC 
However, that would have the effect of invalidating 
(6) 
V*(</>JC A L<j>x) D </>y 
This will be false in a model with wRw' and v assigned some u G Dw but 
u & Dw,. For suppose u does not satisfy <j> in w, but every other 
individual satisfies <j> both in w and in every other world. This will mean 
that <f>y will be false at w. But <j>x A L<j>x will be undefined at w when x 
is assigned w, since <f>x is undefined at w' so by [V*L], L<j>x is undefined 
at w, so by [V* — ] and [V*V], <f>x A L0* is also undefined at w. But 
otherwise it is true, so it is true where defined for every member of Dw. 
So Vx(<f>x A L<j>x) is true at w, and so (6) is false at w and so not valid. 
Further (for what it is worth) VX(0JC A L<f>x) D Vx<j>x also fails, and so 
the problem cannot be blamed on the presence of free variables. 
Admitting truth-value gaps does not therefore seem a way of avoiding the 
problems which arise when you drop the Barcan Formula. 
The existence predicate 
The reason for defining validity by putting restrictions on /i is to preserve 
the validity of even the simplest instance of Vl, such as (2) above. For 
if everything in every world is <f> except for some u £ Dw then V^VJC^JC 
D <j>y,w) will be false if /x(y) = u. The problem with Vl is that y might 
be assigned something which does not exist, while the quantifiers are 
restricted to things which do. This suggests that we could make the 
restriction explicit by adding an existence predicate, i.e., a predicate E 
which has the semantics: 
[VE] 
(u,w) G V(£) iff u G Dw 
What [VE] means is that Ex is true in w iff x is assigned a member of D„. 
We then redefine validity to require that a valid wff be true in every 
world even for assignments whose values do not exist in that world. 
Models for these systems need not satisfy the inclusion requirement but 
in all other respects we shall keep the semantics set out on p. 275. For 
later use we note that both PR and PA are valid according to it. Vl will 
then, of course, not be valid since (2) can fail in such a model. With an 
existence predicate however we may replace (2) by 
(7) 
(VJC^JC A Ey) 
D <j>y 
292 


MODALITY AND EXISTENCE 
or, schematically 
VIE (VJC« A Ey) D a\y/x] 
VIE is the standard replacement for Vl in what is called free logic 
(meaning, as we understand it, logic 'free' of existential assumptions) and 
free logic is often considered the appropriate way to deal with quantified 
modal logic2. However, care is needed in taking free logic as our model. 
In a non-modal free logic it is tempting to think of the variable y> in those 
cases when [Vl] fails, as a 'non-denoting' term. This is because in non-
modal logic we don't normally have a class of things which don't happen 
to exist but might have. But in a modal semantics as we have been 
presenting it so far there are no non-denoting terms. Rather y in Vl 
denotes, but the thing it denotes does not exist in the world in which the 
sentence is being evaluated. 
Axiomatization of systems with an existence predicate 
Because we have to replace Vl with VIE we have to change other aspects 
of the LPC basis. In particular we cannot easily use V2 as it stands. For 
that reason we shall set out the basis explicitly. Where S is any normal 
system of propositional modal logic, LPCE + S is defined as follows. 
S' 
Any LPC substitution-instance of a theorem of S is an axiom of 
LPCE + S. 
VlE Where x and y are any individual variables, and a is any wff then 
(Vxa A Ey) D a[y/x] is an axiom of LPCE + S. 
VD 
Vx(a D jS) D (Vjca D VJC/J) (where a and /? are any wff and x is 
any variable). 
VQ a = Vxct provided x is not free in a. 
UE \/xEx 
The transformation rules are MP, N, 
UG 
\-a-+ 
\-Vxct 
and 
UGLV" 
[-a, D L(a2 D ... D L(an D I/?)...) -* |- a, D L(a2 D 
... D L(an D LVx/3)...), where x is not free in au ... ,an. 
293 


A NEW INTRODUCTION TO MODAL LOGIC 
The first thing to note is that V2, U G 3 , and therefore Eq (see p. 242), all 
follow from UG, VQ and VD. Given this basis we may prove a quantified 
form of Vl as follows: 
Vl' 
Where x and y are any individual variables, and a is any wff then 
|- Vy(Vxa D a[y/x\) 
PROOF 
VIE X UG 
(1) 
Vy((Vxa A Ey) D 
a\ylx\) 
(1) X PC X Eq 
(2) 
Vy(Ey D (Vxa D a\y/x])) 
(2) X VD 
(3) 
VyEy D Vy(Vxa D a[y/x\) 
UE 
(4) 
VyEy 
(3)(4) X MP 
(5) 
Vy(Vxa D a[y/x]) 
Q.E.D. 
In the completeness proof which follows we shall need a number of 
other results which are standard in ordinary LPC and which in fact were 
appealed to in Chapter 14. Since our present basis does not contain Vl we 
can no longer take any of these results for granted and so we shall prove 
them explicitly now. Where appropriate we shall give them the same 
names as in Chapter 13. 
RBV 
If a and /J differ only in that a has free x where and only where 
(3 has free y then 
|- Vxa s Vy(3. 
In the proof of this we note that 0 is a[y/x] and a is 0[x/y] and that y is 
not free in a nor x in (3. 
PROOF 
Vl' 
(1) 
Vy(V;ca D (3) 
VD 
(2) Vy(VJca D (3) D (VyVxa D Vy/3) 
(1)(2) X MP 
(3) 
VyVxa D Vy(3 
(3) x VQ 
(4) Vxa D Vy(3 
Q.E.D. 
The proof of Vy/? D Vxa is exactly analogous. 
QR 
~Vy~(a[y/x] 
D Vxa) 
294 


MODALITY AND EXISTENCE 
PROOF 
PC X UG D 
(1) 
Vy(a\y/x] 
A ~VJC«) D Vya\y/x] 
(1) X RBV 
(2) 
Vy(a[y/x] A -Vxet) 
D Vxa 
PC X UG 
(3) 
Vy(a\y/x] 
A -Vxct) 
D Vy-Vxa 
(3) x VQ 
(4) 
Vy(a[y/x] 
A -VJCCX) D ~V*a 
(2)(4) X PC X Eq 
(5) 
-Vy~(«tv/jc] D Vjca) 
Q.E.D. 
In this proof we rely on the fact that VQ is an equivalence, since the form 
we are using is in fact Vxa D a, where x is not free in a. 
VQD 
Vx(a D (3) D (a D Vx(3), where x is not free in a. 
PROOF 
VD 
(1) 
Vx(ct D » D (Vxa ^ » 
(1) X VQ(2) 
Vx(a D » 
D (a D V*0) 
Q.E.D. 
It is not difficult to see that this axiomatization is sound with respect 
to the given definition of validity. For VIE suppose V^VxctyW) = 1, 
V (Ey,w) = 1 but V^(a[3>/jc],vv) = 0. Let p be the jc-altentative of jit such 
that p(x) = fi(y). By PR, Vp(a,w>) = 0, and since VM(£>,w) = 1 then p(x) 
E Dw. So by [ W ] V^VJCC^W) = 0. VQ is stated as an equivalence. This 
assumes that each Dw is non-empty. VxEx may equally be seen to be 
valid, and the other axioms are completely standard. The only non-
standard transformation rule is UGLVn. Suppose that V/i(a1 D L(a2 D ... 
D L(an D LVJCJS)...),W) = 0. Then there is an R-chain wlf ... wn+1 with 
w = Wj and V/i(ai,wi) = 1 for 1 < i < n, and V/i(V^jS,wn+1) = 0, and 
so for some x-alternative p of/i with p(x) G Dw , Vp(j3,wn+1) = 0. Now 
x is not free in a and so, by PA, Vp(ai,wi) = V^(ai,wi) = 1, and so Vp(a, 
D L(a2 D ... D L(an D L0)...),w) = 0. Note that the fact that p(x) may 
not be in Dw does not prevent a! D L(a2 D ... D L(an D L@)...) from 
being false in w, and therefore being invalid — since the definition of 
validity has now been widened to all assignments to the variables. 
UGLVn is provable in all extensions of LPCE + B, since these all have 
the rule DR4 on p. 62 and its dual 
DR4' 
\-a D L(3 -* \-Ma D (3 
The derivation of UGLVn is as follows: Let af be Ma,, and let af+1 be 
Af(df A oi+I). Then if |- a, D L(a2 D ... D L(an D L0)...), by 
295 


A NEW INTRODUCTION TO MODAL LOGIC 
repeated applications of DR4' we obtain |- a* D /J, and so by V2 
|- a* D Vx/J, and so by repeated applications of DR4, |- a, D L(a2 D 
... D L(an D LVJCJS)...). Without DR4 the situation is less clear. 
Certainly UGLV1 is independent in at least some extensions of LPCE + 
S, since if we strengthen VIE to VI (or equivalently if we add Ex as an 
axiom) BF follows immediately by UGLV1 from VxLa D La — but we 
know from p. 277 that for appropriate choices of S, BF is not a theorem 
of LPC + S.3 However, derivable or not, UGLV" is validity-preserving 
in the current semantics and so must be present in one form or another 
in LPCE + S. 
Completeness for existence predicates 
In this section we assume that we are dealing with some arbitrary but 
fixed system LPCE + S. For completeness4 we proceed as in Chapter 14 
and assume that A is a consistent set of wff of a language i£ and that X 
is an infinitely proper sublanguage of ££+. Where A is a set of wff of ££+, 
say that A has the LV-property in 5£+ iff, 
(i) for every wff a o f ^ + and variable x there is some variable v (in 
i£+) such that£y A (a\y/x] D Vxa) G A.. 
(ii) for all wff of i£+, (3lf ... , 0n (n > 0) and a, and every variable 
x not free in jS,, ... , /Jn there is some variable z (in i£+) such 
thatL(0, D ...D L((3n D L(Ez D a[z/x]))...) D L(0x D ...D 
L(0n D IV*x)...) € A. 
THEOREM 16.1 If A is a consistent set of wff of X then there is a 
consistent set A of wff of i£+ with the LV-property, such 
that A Q A. 
Proof: A is constructed in a way similar to that used in the proof of 
theorem 14.1 as the union of a sequence \ , A,, ... etc. 
A0 = A 
Let Y and Z be two infinite disjoint sets of variables of ££+ not in i£, and 
assume the variables of Y and Z are enumerated. Assume a double 
enumeration of wff of i£+, first an enumeration of all wff of !£+ which 
begin with a universal quantifier, and second an enumeration of the set 9 
of all wff of the form L(yx D ... D L(yh D LVJC6)...) for h > 0, with 
296 


MODALITY AND EXISTENCE 
x not free in 7,, ... , 7h. Where Vsa is the n-t- l'th wff of !£+ beginning 
with a universal quantifier and L(yx D ... D L(yh D LVJC6)...) is the 
n + lth member of 9 and y is the first variable in Y and z is the first 
variable in Z not occurring in An or in a or in y{, ... , yh or in 6 then 
An+, is 
An U {Ey, ot[y/s] D Vsa, L(yx D ... D L(yh D L(Ez D 6[Z/JC])) D 
L(7l D ... D L(Th D LVx6))}. 
We show that An+1 is consistent if An is. Suppose An+1 were not 
consistent. Then for some ft, ... ,ft G An 
(i) 
h (ft A ... A ft A (Ey A (a[y/j] D V*x)) D 
L(Tl D ... D L(yh D L(Ez D 6[z/*])...))) 
and 
(ii) 
\-({3{ A ... A ft A (Ey A (a[y/s] D V*x») 3 
~L( 7 l D ... D L(7h D LVjcd)...) 
Now z does not occur free in An or in (Ey A (a[y/s] D Vsa)), and so 
from (i) by UGLVh+1 
(iii) 
|-(ft A ... A ft A (Ey A (a\y/s] D Vsa))) D 
L(yx D ... D L(yh D Diz(Ez D 6[z/x]))) 
and so by VD, K, PC and RBV, 
(iv) 
\-LNzEz 
D ((fix A ... A ft A (Ey A 
(a\y/s] D V«x)) D L(yx D ... D L(yh D LVxb))) 
So by UE and N, 
(v) 
[- 
(ft A ... A ft A (Ey A (a\y/s] D V*x))) D L(y{ D ... 
D L(Th D LVxb)) 
But (ii) and (v) give 
h(ft A ... A ft) D (£y D ~(aty/j] D V*x)) 
so by V2 
297 


A NEW INTRODUCTION TO MODAL LOGIC 
|- (0, A ... A ft.) D Vy(Ey D ~(a[y/s] D V*x)) 
so by VD 
f- (ft A ... A ft) D (Vy£y D Vy~(oty/j] D VMX)) 
and so by UE 
[-08, A ... A ft^ D Vj^(atv/5] D Vsa) 
But ;y does not occur in a, and so, by QR, 
|- 3y(a£yAy] D Vsa) 
and so 
h -(/?, A ... A ft) 
contradicting the assumed consistency of A„. Since each An is consistent 
so is A. And by construction A has the LV-property. 
THEOREM 16.2 If T is a maximal-consistent set of wff in some language 
(say X+) of modal predicate logic, and T has the LV-
property, and a is a wff such that La £ T, then there is 
a consistent set A of wff of !£+ with the LV-property 
such that Lr(r) U {-a} 
Q A. 
Proof: The proof is similar to (though a little more complicated than) 
that of theorem 14.2 on p. 259. Assume, as in the proof of theorem 16.1 
that 0 is the set of all wff of the form L(6l D ... D L(6h D LVxft)...), 
where x is not free in 0,, ... , 0h. We define a sequence of wff ylt y2, ... 
etc. as follows: 70 is —a. Given 7n we define 7n+1 in the following way: 
We first define a wff 7n
+, and then show how to extend 7n
+ to 7n+1. Let 
VxS be the n+ 1th wff of that form and let 3; be the first variable such that 
(*) 
L-(T) U {7n A (Ey A (6[y/x\ D Vxd))} is consistent. 
Let 7n
+ be yn A Ey A (d\y/x] D Vxd). In order for this construction 
298 


MODALITY AND EXISTENCE 
to succeed we have to be sure that there always will be a y satisfying (*). 
Since Y0 is — a, L~(r) U {Y0} is consistent from lemma 6.4 on p. 117. 
We show that provided L~(r) U {yn} is consistent there will always be 
a y which satisfies (*) and thus guarantees that L~(r) U {yn
+} is 
consistent. 
As in theorem 14.2, we cannot here assume that y is a new variable. 
Nevertheless we can show that there always will be an appropriate y. 
Suppose there were not. Then for every variable y of !£+ there will exist 
some {L0,, ... ,L/?J Q T such that 
[-(13, A ... Aft) D (ya D (Ey D ~(6[y/x] D V*5))) 
so, by DR1 and L-distribution, 
(i) 
|- (Ift A ... A LftJ D L(yn D (Ey D ~(6\y/x\ D Vxfi))) 
But T is maximal consistent and L/?,, ... ,L/?n € T, and so L(yn D 
~(d\y/x] D Vx8)) € T. And this is so for every variable y. 
Now r has the LV-property, and so there will be a variable y such that 
(ii) L(yn D ((Ey D ~(6[y/x] D v*6))) D 
LVz(7n D (Ey D ~(6[z/x] D v*5))) 
is in T, where z is chosen so that it does not occur in yn or in 6. And so, 
since L(yn D ~ (d[y/x\ D VJC6)) is in T for every y, 
(iii) LVz(7n D (£z 3 ~(6[Z/JC] D VJC6))) 
is in T. But T is maximal in LPCE + S and so, 
(iv) LVzEz D LVz(yn D ~(b[z/x] D v*6)) 
is in T. And so by UE, and N we have in T, 
(v) LVz(7n D -(6[Z/JC] D V*5)) 
But z does not occur in 7n or 6 and so by VQD we have in T 
(vi) L(Tn D Vz~(6[z/x] D Vx6)) 
299 


A NEW INTRODUCTION TO MODAL LOGIC 
But by QR 
|- 
3z(6[z/x] D VJCS) 
and so 
(Vii) h L~Yn 
But then L~yn 
G T and so ~y n G L r ( 0 which would make L~(r) U 
{yn} inconsistent. So L~(r) U {7/} is consistent if L-(T) U {yn} is. 
We now show how to extend yn
+ to yn+1. Let L(0, D ... D L(0h D 
Lv* £)...) be the nth wff in 9 and let z be the first variable such that 
(t) 
L"(T) U {7n
+ A (£(9, 3 ... 3 L(0h 3 L(Ez 3 $[z/x]))...) 3 
L(0, 3 ... 3 L(0h 3 
Lix®...))} 
is consistent. Let yn+l be 
7n
+ A (L(0, 3 ... 3 L(0h 3 UEz 3 flz/*]))...) 3 
Z,(0, 3 . . . D K P 
£V*f)...)). 
We may assume that x is not free in 7 / or in 0,, ... , 0h since if it is we 
may choose a bound alphabetic variant of Vx£ in which the variable that 
replaces x is not free in these wff. Suppose there were no z satisfying (|). 
Then for some ft, ... , ft G L~(r) 
(i) 
h 
(ft A ... A ft) D (7n
+ D ~(L(0, D ... D L(0h D (£z D 
ftz/*]))...) D L(0, D ... D L(0h D VxJ)...))) 
So 
(ii) 
h 
08, A ... A |8J D (Tn
+ D 1(0, D ... D L(0h D L(£z D 
{ft/*]))...)) 
and 
(iii) 
h 
(0, A ... A (8k) 3 (T„+ 
3 ~L0, 3 ... 3 £(0h 3 
From (ii) we have, by DR1 and L-distrib, 
300 


MODALITY AND EXISTENCE 
(iv) 
h 
(Lft A ... A Lft.) D L(7n
+ D L(6X D ... D L(6h D L(Ez 
3 Hz/*]))...)) 
Now L/3,, ... , L/?k are all in T and so from (iv) 
(v) Uyn
+ 
3 K ( , : . . . 3 L(0h D L(£z D ife/*]))-)) 
is in T for every variable z. So, since T has the LV-property, 
(vi) L(Tn
+ D L(0, D ... D L(0h D LV^f)...)) 
is also in T, and so 
(vii) 
Tn
+ D UBX D ... D L(0h D LV*D...) 
is in L~(r), which, together with (iii) would make L~(r) U {7/} 
inconsistent. So L~(r) U {7n+1} is consistent if L~(r) U {7/} is. Since 
L-(H U {7/} is consistent iflr(T) 
U {yR} is then L~(r) U {7n+1} is 
consistent if L~(r) U {yn} is. So L~(r) U {7J is consistent for every 
n. 
Let A be the union of L~(r) and all the 7ns. Since each L~(r) U 7n 
is consistent, and since |- ym D yn for m > n, so is their union A. By 
construction A has the LV-property and so theorem 16.2 is proved. 
The canonical model is defined as in Chapter 14 on p. 261 except that 
we require that x G Dw iff Ex G w. 
THEOREM 16.3 For any w G W and any a G i£+, Va(a,w) = 1 iff a 
G w. 
The proof then proceeds as in the case of theorem 14.3 on p. 261 except 
for the inductive step for V. If Vjca £ w, then by the V-property there is 
some y such that Ey G w (making y G Dw) and a\ylx\ £ w. Thus 
Vff(a[y/jc],w) = 0, and so when v is the ^-alternative of a with v(x) = 
o(y)> V„(a,w) = 0, and so, since aiy) G Dw, Va(Vxa,w) = 0. 
Suppose Vjca G w and let v be any ^-alternative of a such that p(x) = 
y for some y G Dw. Since y G Dw, then Ey G w. So by [VIE], a\y/x] 
G w, and so V0(aLy/.x],vv) = 1, and so V„(a,w) = 1. So Va(V*a,H>) = 
1. 
From theorem 16.3 it follows that the canonical model of LPCE + S 
301 


A NEW INTRODUCTION TO MODAL LOGIC 
validates all and only theorems of LPCE + S. Completeness with respect 
to all frames for S follows as in previous chapters for all systems in 
which the frame of the canonical model is a frame for S. That includes 
all the systems mentioned on p. 249. 
Incompleteness 
Since LPC + S contains LPCE + S, to establish that an incompleteness 
result for the former applies to the latter it is sufficient to show that the 
frames which validate non-theorems of LPCE + S still validate those 
same wff when the inclusion requirement is dropped. The result for 
LPCE + S4M holds for the same reasons as given in the case of LPC + 
S4M on p. 283. Theorem 15.4 on p. 285 still holds for systems which do 
not satisfy the inclusion requirement, and so the incompleteness results on 
pp. 283—287 hold also for such systems. 
Expanding languages 
In Chapter 15 we were able to prove completeness for a wide range of 
systems of modal predicate logic without the Barcan Formula. But the 
technique was restricted to systems which admitted frames without any 
looping back. It is a feature of the canonical models defined on pp. 
280—282 that when wRw', !£w is contained in !£w,. In the models of 
Chapter 15 Dw is simply the class of variables in ££w , and so these 
models satisfy the inclusion requirement. But when we introduce an 
existence predicate there arises the possibility that the set of y such that 
Ey E w does not include all the variables of i£w. This means that the 
technique used in Chapter 15 can be applied, without the need for UGLV, 
to systems whose models do not satisfy the inclusion requirement. 
Theorem 16.1 can be adapted in the following way. Say that A has the 
EV-property iff for every wff Vxct there is some variable y such that 
Ey A (a£y/jc] D Vxa) € A. Clearly the LV-property entails the £V-
property, and so theorem 16.1 guarantees that where a language ££' 
extends !£ by infinitely many new variables then any consistent A in i£ 
can be extended to a set A of ££' with the £V-property. So if we are 
permitted to extend the language infinitely in passing from w to an 
accessible w', then if L~(w) U { ~a} is consistent in ££w it has a maximal 
consistent extension w' in S£w.. However, though the models do not satisfy 
the inclusion requirement the languages on which they are based do, in 
that where wRw', $£w, is an extension of ££„. Since some of these 
extensions are proper these models cannot be based on symmetrical 
frames. 
302 


MODALITY AND EXISTENCE 
Possibilist quantification revisited 
As we said on p. 274, the philosophical plausibility of the Barcan 
Formula has been questioned. One way of construing it makes it look as 
though the validity of the BF reflects the view that the same things exist 
in all possible worlds. This looks like the view that everything is a 
necessary existent, and that makes the Barcan Formula look not only like 
a special case of a more general semantics, but in fact like an implausible 
special case. We have already mentioned (in note 1 on p. 287) that one 
of the earliest philosophers to get worried about BF was Arthur Prior in 
Time and Modality.5 Prior was concerned with a temporal interpretation 
of the necessity operator. He read La as 'it is and always will be that a' 
and he read BF as saying that if everything will always be <f> then always 
everything will be 0. And he thought this was false because even if 
everything now existing will always be <j> it does not follow that it will 
always be that everything then existing is <j>. 
But you don't have to interpret BF that way. You can interpret V as 
ranging over all past, present or future individuals, and if every one of 
them will always be <j> then it will always be that everything is <j>. 
Similarly in the modal case. Even if each world w has its own domain Dw 
of the things which exist in w there is no reason why all these Dws can't 
be collected into one single domain D. That at least is one way of 
defending BF. And if we have an existence predicate it is now easy to 
define a quantifier satisfying [Vv'] on p. 275 in terms of a quantifier 
satisfying [VV]. To avoid confusion we shall temporarily (i.e. in this 
section) use V for the 'possibilist' quantifier, that is the quantifier 
satisfying [VV] on p. 239 and ranging over the whole of D and will 
follow Prior's use of Lukasiewicz's symbol II for the 'actualist' 
quantifier, that is the quantifier satisfying [Vv'] and ranging over the 
domain of the world in question. It is then trivial to note that HC<£JC can 
be expressed as 
[Def n] 
Vx(Ex D <j>x) 
This means that systems without BF but which have an existence predicate 
emerge as subsystems of systems with BF. We can now see why VI is not 
valid for actualist quantifiers. Consider again 
(1) 
Ux<j>x D <j>y 
When translated this becomes 
303 


A NEW INTRODUCTION TO MODAL LOGIC 
(2) 
VJC(£JC D (j>x) D <j>y 
and if we consider an interpretation in which every member of D„ 
satisfies <f>y but y is assigned something which is not in Dw and does not 
satisfy <\> then (2) will be false, even in systems which contain BF for V. 
Of course (2) can be turned into a truth by replacing it with 
II1E 
(rLc0;t A Ey) D <j>y 
or schematically 
niE' 
(Ilea A Ey) D a\ylx\ 
because, when unpacked by defining II in terms of V we get 
(3) 
(Vx(Ex D a) A Ey) D a[y/x] 
which is indeed a truth of S + BF. So in a way we have come full circle, 
since if you begin with a system containing the Barcan Formula, and you 
are prepared to admit an existence predicate, then you can after all have 
all the advantages of the simplest version of the semantics and 
completeness proofs for modal LPC as set out in Chapters 13 and 14, and 
still use quantifiers which are restricted to things which actually exist. 
Kripke-style systems 
In 1963 Saul Kripke6 advocated a different way of axiomatizing systems 
whose semantics did not incorporate the inclusion requirement. Kripke's 
systems did not contain an existence predicate, so he could not respond 
to the problems caused by the axiom schema Vl in the way we have done 
so far. Kripke's way of dealing with this situation can be expressed as 
follows. Although (2) on p. 290 is invalid when V is an actualist 
quantifier, its universal closure, Vy(Vx<£jc D <j>y) is valid. This suggests 
weakening Vl along the lines of Vl' on p. 294, though for a reason to be 
explained Vl' itself will not quite do. Because these systems were first 
studied by Kripke we shall refer to them as 'Kripke-style' systems, and 
shall denote the version of LPC by LPCK, even though our 
axiomatization will not be exactly the same as Kripke's.7 Where S is any 
normal system of propositional modal logic LPCK + S is defined as 
follows: S', VD, VQ, N, UG and MP are as on p. 293, but VIE is 
replaced by 
304 


MODALITY AND EXISTENCE 
VlK Where x, y and z are any individual variables, and a is any wff then 
VyVz(Vxa D a\y/x\) is an axiom of LPCK + S. 
(UGLV is not part of this basis, though it is in fact validity-preserving. 
UG, RBV, QR and VQD may be proved as on pp. 294-295.) 
The semantics is as for systems with an existence predicate except that 
V(E) is no longer required. VlK may be easily seen to be valid, for 
suppose that for some w G W, and some assignment /*, 
VM(VyVz(Vjccx D a[y/x]),w) = 0 
Then for some y-z-al tentative p of fi (i.e. an assignment like \x except 
possibly at y or z) where p(y) and p(z) are both in Dw, 
(1) 
VP(VJC«,W) = 1 and 
(2) 
V,(ct\y/x]9w) = 0 
Let v be the ^-alternative of p in which v{x) = p(y). By PR and (2), 
V„(a,w>) = 0, and because p(y) G Dw so is J>(JC) and so Vp(Vjca,yn>) = 0, 
contradicting (1). 
The presence of Vz in VlK may seem a little curious, but in fact it is 
necessary to prove a result we shall need, viz. PV V;cVya D VyVxa. PV 
is a principle for permuting universal quantifiers.8 Vl' follows from VlK 
by choosing z not free in Vxa D a[y/x]. Note that 3IK may be derived 
from VIE as Vl' was. We prove PV as follows 
VlK 
(1) 
VyVjt(Vya D a) 
VD 
(2) 
Vx(Vya D a) D(VJcVya D Vxa) 
(2) X UG D 
(3) 
VyV;c(Vya D a) D Vy(V*Vya D Vxa) 
(1)(3) X MP 
(4) 
Vy(VjtVya D Vjca) 
(4) X VD 
(5) 
VyVxVya D VyVj:a 
VQ 
(6) 
VxVya D VyV^Vya 
(5)(6) X PC 
(7) 
VjeVya D VyV^a 
Q.E.D. 
We shall need the following generalization of PV: 
P V Vz1...VzhVy1...Vyka D Vy1...VykVz1...Vzha 
305 


A NEW INTRODUCTION TO MODAL LOGIC 
This may be proved by multiple applications of PV and UGD. We shall 
also need the following generalization of VlK: 
VlA Vj,..VMV^a, D afo/xj) 
A ... A ( V ^ k D 
cc&jxj)) 
and the following generalization of QR: 
QRA 
3y,...3Maityi/*il 3 V^a.) A ... A (ajyjxj 
D V^aJ) 
provided yx is not free in (Xj for 1 < j < i < h. The proofs of VlA and 
QRA are left as an exercise. They both require PV. 
Completeness of Kripke-style systems 
We turn now to the problem of defining canonical models for the Kripke-
style systems. In fact we shall restrict ourselves to producing models by 
the method of Chapter 15. It is convenient at this point to introduce an 
extension to the V-property which we shall call the extended V-property. 
Where A is a set of wff of a language i£ and Y is a set of variables of i£ 
we say that A has the extended V-property in X with respect to Y iff 
(i) 
A has the V-property with respect to Y, i.e. for every wff a and 
variable x of ££, there is a variable y G Y such that, a[3>/;t] D 
Vxa G A, and 
(ii) 
for every wff a and variable y of Y, Vjca D a\ylx\ € A. 
For systems with the unqualified Vl, maximal consistency 
automatically guarantees (ii), but for Kripke-style systems we don't have 
this axiom. We take each world w in the canonical model to be a maximal 
consistent set of wff of i£w with the extended V-property in !£w with 
respect to an infinitely proper subset Y of the variables of i£w. We can 
then let Dw be Y, and we take wRw' iff L~(w) c 
w'. 
The principal theorem required is an analogue of theorem 14.1 on p. 
258. Suppose that A is a consistent set of wff in a language ££ and 
suppose that X is an infinitely proper sublanguage of a language i£'. 
Then 
THEOREM 16.4 There is an infinitely proper subset Y of the variables of 
££' and a consistent set of wff of X' such that A Q T 
and T has the extended V-property in ££' with respect to 
306 


MODALITY AND EXISTENCE 
Y. 
Proof: Choose Y to be an infinitely proper subset of the variables of ££' 
containing infinitely many variables not in i£. Let 0 be the set of all wff 
of the form V.x/3 D @[y/x] where (3 is a wff of i£' and y G Y. Now form 
a sequence 7i*,72*, ...etc. as follows. Assume that the wff of i£' of the 
form Vsy have been enumerated. Where Ws]7, is the first of these take z, 
to be the first variable in Y not in Vsxyx and let 71* be yi[Z\ls{\ D V.syyi. 
Given 7;* let 7i+1* be (7;* A (yi+l[zl+l/s-l+l] 3 V*i+iYi+i))> where z5+1 is 
the first variable in Y not in 7;* or in 7i+1. 
Let A be the union of all the 7;*s. It is clear that any extension of A 
U 0 U A in i£' will have the extended V-property in ££' with respect to 
Y, so all that is required is to show that A U 0 U A is consistent. Let 
us first note two things about A: 
(a) 
Any finite subset of A will appear as the conjuncts of some 7h*. 
(b) 
For each h, each conjunct of 7h* will have the form yizjs^ 
D 
V^^i, where z-x does not appear in any wff in A or in any y. for j < i. 
Now suppose that A U 0 U A is not consistent. Then there must be 
wff a,, ... ,an, /?„ ... ,jSk, 7h* such that 
(1) 
a„ ... ,an € A 
(2) 
Vx^ D jSitVi/jcJ € 0, for 1 < i < k, where each y{ G Y. 
(3) 
7h* G A and 
(4) 
\- ~(a, 
A ... A an A ((V*,/?, D /?,[)>,/*,]) A ... A 
(Vxj3k D (3&M)) 
A 7h*) 
It may happen for some 1 < i < k, and for some 1 < j < h, that yx is 
Zp but since the c^s are all in A they do not contain any of the y{s or any 
of the ZjS. Let a denote «j 
A ... 
A an, and let (3 denote 
((Vx,/?, D jS.ty./jc,]) A ... A (VJCA D PJyJxJj). Then (4) yields 
(5) 
\-(3 D (a D ~7h*) 
So by UG, 
307 


A NEW INTRODUCTION TO MODAL LOGIC 
(6) 
h V ^ . - . V ) ^ D (a D ~7h*)) 
So, by multiple applications of UG3, 
(7) 
l-V^.-.V^ D Vyi...Vyk(a D ~7h*) 
So, by VIA and MP, 
(8) 
|-V^...Vjk(a D ~Th*) 
From (8) by UG, 
(9) 
|- Vz,... Vz^y,... Vjk(a D ~ 7h*) 
and so, by PV 
(10) yy1...V>kVz,...V^(o D ~7h*) 
But Zi, ... ,Zh are not free in a and so, by VQD, 
(11) 
j-Vy,...V>;k(a D Vz^-.VZh^Th*) 
But Zi does not occur in 7j for j < i and so by QRA, 
(12) 
h ~Vz,...Vzh~7h* 
So, from (11), 
(13) 
(-*)>,.-V^-a 
But ji, ... ,yk are not free in a, and so by VQ 
(14) 
h~<* 
which of course contradicts the supposition that A is consistent. 
By theorem 6.3 on p. 115, any A U 0 U A as defined in the present 
theorem can be extended to set T of wff which is maximal consistent in 
££' and has the extended V-property with respect to Y. We are now in a 
position to define canonical models for Kripke-style systems. We assume 
that each £w is an infinitely proper sublanguage of !£+ and that Dw is an 
308 


MODALITY AND EXISTENCE 
infinitely proper subset of the set of all variables of i£w. 
Then any w G W will be a set of wff maximal consistent in !£w and 
having the extended V-property with respect to Dw. Let wRw' iff L~(w) 
Q w'. Given some —La G w we know from lemma 6.4 on p. 117 that 
L~(H>) U { ~ a} is a consistent set of wff of !£w. So if !£w is the ££ of 
theorem 16.1, and L~(w) U { — a} is A, we know that A is consistent. 
Where !£w, extends !£w by the addition of infinitely many new variables, 
and where Dw, is the Y of theorem 16.1, we know from that theorem that 
there is a maximal consistent extension of w' in !£w, of L"(w) U { ~ a} 
which has the extended V-property in Xw, with respect to Dw,. So wRw' 
and w' G W. V is defined as on p. 281 and the theorem to be proved 
is, for every w G W and every a G !£w, 
THEOREM 16.5 Va(a,w) iff a G w. 
Note that the proof is for all wff in Xw and follows exactly the proof of 
theorem 15.3 on p. 281 except for the induction step for V. Where Wxa 
G w, in order to show that Va(V;ca,w) = 1 we need merely verify that 
V„(a,w) = 1 for every ^-alternative v of a such that v G Dw. This means 
that we need only consider y G Dw, and since w has the extended V-
property with respect to Dw then Vjca D a\ylx\ G w and so since Vxa G 
w then a[y/x] G w. 
Completeness follows as in Chapter 15 for all those cases in which the 
frame of the canonical model for LPCK 4- S is a frame for S. Although 
these models do not satisfy the inclusion requirement they cannot be based 
on symmetrical frames for the same reasons as given on p. 282. Thus we 
do not have completeness results for Kripke-style systems containing B. 
The methods used on pp. 296—301 do not obviously apply, since there 
seems no way to express Ey by a finite wff. Where Ey is true we need 
VJCOJ D a\y/x\ for every wff a, but that involves an infinite number of 
wff. As far as we are aware no completeness proofs for these systems 
have been published.9 
Exercises — 16 
16.1 Using [V*0]-[V*V] on pp. 278-278, prove that if R is reflexive 
then if VM(a,w) is defined and x is free in a, /X(JC) G D„. 
16.2 Where S is a logic which has as one of its frames the frame 
w\ ~* w2 ~* w3> prove that the following instance of BFC is not valid using 
309 


A NEW INTRODUCTION TO MODAL LOGIC 
the 'undefined' semantics: Ls/xL<J>x D VxLL<j>x. 
16.3 Using the semantics discussed on p. 291 in which V^Vxc^w) = 1 
provided Vp(a,w) = 1 for every jc-alternative of/x for which Vp*(a,w) is 
defined, show that MP is not validity-preserving. 
*16.4 
Where S is K + ML(p A ~p) 
V (q D LMq), prove the 
completeness of LPCE + S, without appealing to UGLV. 
16.5 Show that the axiom system complete for K with possibilist 
quantifier and an existence predicate is K + BF if empty domains are 
allowed and K + BF + 3xEx if they are not. 
16.6 Prove VIA and VQ A. 
16.7 Where C(a) is a preceded by Ls and Vs for all its variables in any 
order and LPCK* + S has as axioms C(a) for every axiom a of LPCK 
+ S, and as transformation rules UG and MP, prove that |-LPCK+S a iff 
ILPCK*+S C(a). 
*16.8 
Prove the completeness of LPCK + B o r LPCK + S5. 
Notes 
1 For systems containing T the proof generalizes to the schematic case 
LVxa D VJCLQ:, because of the fact that when R is reflexive if VM*(o:,w) is defined 
then fi(x) E Dw. (Correspondence with Giovanna Corsi helped us get clear about 
the connection between undefined wff and BFC.) 
2 See Garson 1984, p.261. Garson's article provides a helpful overview of a 
number of approaches to modal predicate logic. An existence predicate is 
introduced in Rescher 1959, and also assumed in Fine 1978. 
3 Parsons 1975 states that this rule is not needed in proofs from closed wff. The 
rule comes from R.H. Thomason 1970a. 
4 The proof given here is adapted from R.H. Thomason 1970a in the same way 
as our proof of completeness for systems with BF was in Chapter 14. Thomason's 
existence predicate is defined on p.57 in terms of identity. The rules we call 
UGLV first appear in Thomason's paper. 
5 Prior 1957, pp.26-28. 
6 Kripke 1963b. 
7 In Kripke 1963b, p.89, Kripke's own system (presented for T) is defined in 
terms of the closure of a wff a, meaning by that a preceded by any number of 
Ls and Vs in any order for all of a's free variables. If we replace all the axioms 
310 


MODALITY AND EXISTENCE 
of LPCK + S by their closures and use MP and UG as the only transformation 
rules then an induction on the proofs of theorems establishes that |~LPCK+S a iff 
the closure of a is provable in the resulting axiomatization. 
8 The need for some such device is shown in Fine 1983, who points out that 
Kripke's basis needs amending. The problem is really one of non-modal LPC, and 
Fine gives an interesting history of it. 
9 Certainly none is mentioned in Garson 1984. Fine 1978, p. 135, claims that the 
method he uses in that article for systems with an existence predicate will work 
for systems without one, but adds: "The construction of the canonical model is 
complicated rather, since it is necessary to keep an external check on which 
constants belong to which worlds." 
311 


17 
IDENTITY AND DESCRIPTIONS 
Identity in LPC 
Ordinary, non-modal, LPC may be augmented by the addition of a dyadic 
predicate to represent identity. This predicate may be referred to as <£=, 
though instead of 0=jcy it is customary to write x = v and to write x 5* 
y for ~<j>=xy. (Identity is frequently referred to as Equality, especially for 
systems of LPC whose intended interpretation is a mathematical one. Our 
frequent use of = as a metalogical symbol, as when we write V (of,w) = 
I to mean that the value assigned to a by V with respect to fi is 1, should 
not lead to any confusion.) In order to see how to interpret <J>= consider 
a model (D,V) for LPC. This will be a model for identity provided that 
V(<£=) consists of all and only pairs of the form (u,u) for i / G D . I.e. the 
interpretation of <j>= is the set of pairs with the same terms. A 
consequence of this is that for any assignment fi to the variables, and any 
w G W, 
Vtl(x = y)= 
1 iff p(x) = ii(y) 
With this interpretation a complete axiomatic basis for LPC with identity 
may be provided by adding the axiom 
II 
x = x 
and the axiom schema 
12 
x = y D (a D 0) 
312 


IDENTITY AND DESCRIPTIONS 
where a and /? differ only in that a has free x in 0 or more places where 
jS has free y. 
12 has to be stated as a schema, but II could be single formula since 
by UG we have Vx x = x and so by Vl, y = y, for every variable y. It 
is not difficult to see that both II and 12 are valid with this semantics. An 
easy consequence of II and 12 is 
13 
x = y D y = x. 
We can of course add identity to modal LPC. We shall, for simplicity, 
consider systems which satisfy BF. The extention of V(0=) to the modal 
case is simple. V(0=) is the set of triples (w,w,w) for u G D, and w E 
W. With this semantics II and 12 remain valid. We shall refer to S + BF 
with the addition of II and 12, as S + I. In these systems the wff a and 
(3 in 12 will now of course include wff containing modal operators. 
There is however a consequence which turns out to be a matter of 
some controversy. That is that all identity statements are necessary. We 
prove this as follows: 
LI 
x=yDLx=y 
PROOF 
12 
(1) x = 
yD(Lx=xDLx=y) 
(1) X PC 
(2) 
Lx = xD(x 
= 
yDLx=y) 
11 x N 
(3) 
L x = x 
(2)(3) x MP 
(4) x=yDLx=y 
Q.E.D. 
(In this proof (1) is obtained by taking a as L x — x and replacing the 
(free) second occurrence of x by free y.) 
What LI means is that whenever x and y are the same object it is a 
necessary truth that they are, or that every true statement of identity is 
necessarily true, or that there are no true contingent statements of 
identity. Now it seems easy to think of counter-examples to this. E.g., the 
sentence: 
(1) The person who lives next door is the mayor 
seems to assert an identity between the person who lives next door and 
the mayor; and if so we could rewrite (1), semi-formally, as: 
313 


A NEW INTRODUCTION TO MODAL LOGIC 
The person who lives next door = the mayor. 
Yet surely, it may be said, this is contingent, for it is logically possible 
that the person who lives next door might not have been the mayor. Or, 
to use a classic example,1 although the morning star is in fact the same 
body as the evening star, this is a contingent truth of astronomy and not 
a necessary truth of logic. So if we are to regard LI as valid we shall 
have to show that cases like these are not genuine counter-examples. 
In some systems, e.g. in all extensions of B, we may derive the same 
principle for non-identities. 
LNI 
x * y D Lx * y 
PROOF 
LI X PC 
(1) 
~L x = y D x 5* y 
(1) X LMI 
(2) 
Mx^yDx^y 
(2) X DR4 
(3) 
x 9* y D Lx * y 
Q.E.D. 
Whatever we think of LI it is at least arguable that intuitively LI and 
LNI stand or fall together, and that if a satisfactory modal system is to 
contain LI it should contain LNI as well. We first observe that both LI 
and LNI are valid on the interpretation given to <j>=. For suppose fi(x) = 
/x(y) then (n(x),ii(y),w) will be in V(<£=) for every w G W, and so 
V^L x = y,w) = 1. And if fi(x) ?* fi(y) then there will be no w G W 
such that (/*(*),/*(y),w) G V(</>=), and so, VM(L x ^ y,w) = 1. Because 
LNI is valid according to the semantics for identity that we are using at 
the moment we need to ensure that it forms part of the axiomatic basis. 
We shall see on p. 335 that for many choices of S, LNI is not a theorem 
of S + I. We use S + LNI to refer to the result of adding LNI to S + 
I, and in this chapter these are the systems we shall consider. 
Soundness and completeness 
We first establish the soundness of S + LNI. That is to say we establish 
that if every LPC substitution-instance of a theorem of S is valid in a 
model (W,R,D,V) then so is every theorem of S + LNI. (Where (W,R) 
is a frame for S then the argument used in the proof of theorem 13.1 on 
p. 247 still applies, and shows that every substitution-instance of every S-
theorem is valid in every model based on (W,R).) Vl is valid in all 
models (W,R,D,V) and so will still be valid in that sub-class of models 
which treat <f>= as identity. Further, the transformation rules preserve 
314 


IDENTITY AND DESCRIPTIONS 
validity in a model, and so all that is needed for soundness is to establish 
that II, 12 and LNI are valid. II is certainly valid since if fi(x) = w, then 
since (w,w,w) € V(0=) we have VM(JC = x,w) = 1. We have already 
shown that LNI is valid. The validity of 12 may be established by 
induction on the construction of a and /J, though because of the step for 
~ it is easier to prove it for 
12' 
x = y D (a = (3) 
Intuitively it should be clear that if n(x) = /i(y), and a and (3 differ only 
in respect of x and y, then V/t(a,w) = VM(/?,w) and so V^(a = (3,w) = 
1. 
We now show that each system S + LNI has a canonical model, in 
which all and only its theorems are valid. To establish this we need to 
vary slightly the definition of the canonical model given in Chapter 14. 
The worlds are still maximal consistent sets of wff which have the V-
property in some language i£+ of modal LPC. And as before wRw' iff for 
every wff La of i£+, if La G w then a G w'. The change comes in the 
definition of D. Our earlier plan was to let D be the set of all the 
(individual) variables of i£+. We then took a 'canonical' assignment fi(x) 
whereby (i(x) is x itself. But this plan will not work here, for if x and y 
are distinct variables then ^(x) and fi(y) would have to be distinct, 
regardless of whether or not x = y E w for some w in the canonical 
model. 
Our way of dealing with this problem is to choose one of them, say x, 
as the 'representative' of both x and y so that fi(x) = x and /i(y) = x. But 
before we describe this procedure, we need to make an observation about 
worlds in the canonical model. We observed on p. 137 that the frames of 
some canonical models for propositional systems are not cohesive, and the 
same is true of models for LNI systems. In proving that every S + LNI-
consistent set A of wff is true at some world we shall restrict ourselves 
to the cohesive part of the canonical model to which a world containing 
A belongs. 
As we said on p. 137 a cohesive part of a frame may be regarded as 
a complete frame in itself since the truth of wff in any world in any 
model based on it will not be affected by the values of wff outside that 
cohesive part. For this reason we shall think of the cohesive part of the 
canonical model of S + LNI which satisfies A as itself a cohesive model 
(W,R,D,V). The reason for this is that in a cohesive model for S + LNI 
every world contains exactly the same identity formulae, in the sense that 
315 


A NEW INTRODUCTION TO MODAL LOGIC 
for w, w' G W, and any x and y, x = y G w iff x = y G w'. 
It is easy to see that this is so, since consider any world w and any w' 
such that either wRw' or w'Rvv. If wRw' and x = y G w, then by LI, L x 
= y G w and so x — y G w'. If x = y G w and w'Rvv then if x = y & 
w', then x 5* y G w' and so by LNIL JC 5* y G w' and so, since w'Rvv, 
x 7* y G w, contradicting its consistency. Now if (W,R,D,V) is cohesive 
and w, w' G W, then w and w' are linked by a chain of backwards or 
forwards R-steps, and so if x = y G w then* = y G w ' and if * = y G 
w' then x = y G w. 
Given an S + LNI-consistent set A of wff of ££, we shall show how 
to construct a cohesive sub-model of the canonical model of S + LNI in 
which there is some world w such that A Q w. As before the members 
of W are all maximal consistent sets of wff of i£+ with the V-property in 
i£+, and wRw' iff L~(w) Q w'. Given some w* such that A Q w* we let 
W be the set of all and only those worlds which can be reached by a 
chain of forwards or backwards R-steps from w*. We define the domain 
D as follows. Assume that the individual variables of i£+ are enumerated 
in some fixed order and suppose that x is any variable. Then there is 
some variable y, perhaps x itself, which is the earliest variable in the 
enumeration of variables for which x = y G w. (Since exactly the same 
identity wff are in every w G W it makes no difference which w is 
selected for this purpose.) Let D consist of all variables x such that x is 
earlier than any other y for which x = y G W. For JC,, ... ,jcn in D and 
w G W, (JC,, ... ,Jcn,w) G V(0), for n-place predicate <j>, iff #*,...jcn 
G w. 
We must first show that with this definition V(<£=) really is the identity 
predicate. Suppose that x G D. Then certainly x = x G w, and so 
(x,x,w) G V(0=). Suppose that JC G D and y G D and JC and y are 
distinct variables. Then x must be earlier than any other z (including y) 
for which JC = z G w, and y must be earlier than any z including JC such 
that y = z is in w. If JC = y is in w, JC must be earlier than y, but by 13, 
y = JC is also in w and so y must be earlier than x. So if JC and y are 
distinct members of D then JC = y $: w and so (xyyyw) (£ V(<£=) as 
required. 
We define the 'canonical' assignment /x, in such a way that /X(JC) is the 
earliest variable y such that JC = y G w. By II we know that there always 
will be at least one appropriate y. In fact y will be the unique member of 
D for which x = y G w. 
316 


IDENTITY AND DESCRIPTIONS 
THEOREM 17.1 For every wff a of ££+ and every w G W, VM(a,w) = 
1 iff a € w. 
Proof: The proof is by induction of the construction of a. Let <j> be any 
n-place predicate, including </>=, let w G W, and consider <j>xx.. .xn. Now 
H(xx), ... ,/iW will be some^, ... , ya, where ylf ... ,yn G D, andy, = 
xlf ... ,yn = xn G w. Then 
VM(0x,...xn,w) = 1 
iff (life). - >/*(*n),H>) G V(«) 
iff(y„... ,yn,w) G V(</>) 
iff 0yj...yn G w. 
But^j = JCI, ... , yn = xn are all in w, and so, by repeated applications 
of 12 
<t>y\~-y* = ^i-.-^n € w 
and so 0Xj...xn G w iff ^y1 ...yn G w, which gives us the required result. 
The induction for —, V and L is as in the proof of theorem 14.3 on p. 
261. For V, if Vxa G w the argument is as for case (d) on p. 261. If 
~ Vxa G w then since w has the V-property there will be some y G i£ + 
such that ~ ct[y/x] G w. So there will be some z G D such that y = z G 
w, and so by 12, ~a[z/jc] G w. So C*[Z/JC] £ w, so VM(a[z/jc],w) = 0, 
and so, by the validity of Vl, VM(VJCCX,H>) = 0. Completeness follows as 
before for all systems S + LNI whose canonical model is based on a 
frame for S. 
These results carry over mutatis mutandis to systems without BF, and 
to systems with an existence predicate. In the case of these latter however 
we can now define E as2 
Ex =df 3y x = y 
This is because with an actualist quantifier V/t(3y x = y,w) = 1 iff there 
is a y-alternative p of fi in which p(y) G Dw and Vp(x = y,w) — 1. This 
last will be so iff p(x) = p(y), i.e. iff /X(JC) = p(y). I.e. V ^ y JC = y,w) 
is true iff there is a member of Dw that n(x) is identical with. Which is 
just to say that fi(x) G Dw, or that V^(£JC,W) = 1. 
317 


A NEW INTRODUCTION TO MODAL LOGIC 
Definite descriptions 
On p. 313 we used the sentence 
(1) 
The person next door = the mayor 
to motivate the idea that the principle 
LI x = y D L x ~ y 
might be found objectionable. One way of countering this objection would 
be to construe (1) in such a way that it did express a necessary truth. 
Now it is contingent that the person who is in fact the person who lives 
next door is the person who lives next door, for he or she might have 
lived somewhere else; that is, living next door is a property which belongs 
contingently, not necessarily, to the person to whom it does belong. And 
similarly, it is contingent that the person who is in fact the mayor is the 
mayor; for someone else might have been elected instead. But if we 
understand (1) to mean that the object which (as a matter of contingent 
fact) possesses the property of being the person who lives next door is 
identical with the object which (as a matter of contingent fact) possesses 
the property of being the mayor, then we are understanding it to assert 
that a certain object (variously described) is identical with itself, and this 
we need have no qualms about regarding as a necessary truth. This would 
give us a way of construing identity statements which makes LI perfectly 
acceptable: for whenever x = y is true we can take it as expressing the 
necessary truth that a certain object is identical with itself. 
An important feature of (1) is that it is not stated using variables but 
is stated using complex phrases like 'the person next door' and 'the 
mayor'. These phrases are often called definite descriptions and they pose 
problems even in non-modal predicate logic. One of the first to see this 
was Bertrand Russell3 whose celebrated example was 
(2) 
The present king of France is bald. 
Since there is no present king of France it would seem that (2) is false. 
But then it would seem that 
(3) 
The present king of France is not bald. 
is true. But (3) doesn't seem true either, for the same reason as (2). 
318 


IDENTITY AND DESCRIPTIONS 
Russell was worried about people who supposed that (2) or (3) had to be 
true because there was a non-existent individual who is the present king 
of France, about whom either baldness or non-baldness is predicated. 
Now we have seen that in modal logic there is no bar to having 
individuals which exist in some worlds but not others. And no doubt there 
are worlds in which there are objects which do not exist in our world, and 
some of them may, in their worlds, be kings of France. This is just how 
modal logic interprets the truth that there might have been a present king 
of France, and that king need not be anyone who actually exists. But that 
is not what (2) or (3) claim. For they do not speak of whether an 
individual who does not actually exist is or is not bald in some other 
world. (2), if about an individual which does not exist, would be claiming 
that that individual is actually bald, bald in the real world. And that won't 
do because the individual does not even exist in the real world. And (3), 
on at least one way of taking it, predicates lack of baldness, in other 
words having hair, in the real world, of a non-existent individual, and that 
won't do either. 
Even more blatant is the sentence 
(4) 
The present king of France does not exist. 
On Russell's view it is sheer nonsense to suppose that (4) predicates 
(truly) non-existence of a non-existent object. His claim was that the 
phrase 'the present king of France' does not function like a name at all. 
To see this let us go back to our example (1) of the person who lives next 
door, and let us use the predicate <j> to mean 'lives next door'. Let us use 
\j/ to mean 'is bald' and look at 
(5) 
The person who lives next door is bald. 
If we follow Russell, (5) makes three claims 
(6) 
At least one person lives next door; 
(7) 
At most one person lives next door; 
(8) 
Whoever lives next door is bald. 
In an LPC with identity these can be formalized as 
319 


A NEW INTRODUCTION TO MODAL LOGIC 
( 9 ) 
lX<j>X 
(10) VxVy((<f>x A <f>y) D x = y) 
(11) 
VJC(<£X D \PX) 
(9) and (10) together say that exactly onex is <f>. Sometimes this is written 
as 3lx<f>x or 3\x<f>x. (5) then is the conjunction of (9), (10) and (11). Now 
look at 
(12) The person next door is not bald. 
There are in fact two wff which can be argued to represent (12). The first 
is simply the negation of the conjunction of (9), (10) and (11). 
(13) 
~(3JC</>;C A VxVy((<fix A <j>y) D x = y) A Vx(<j>x D \px)) 
This way of negating (5) is sometimes called external negation because 
the negation sign is outside the rest of the formula. The other way of 
negating (5) is to regard 'not bald' as a predicate. On this interpretation 
(12) becomes 
(14) 3xcj>x A VxVy((<j>x A <j>y) D x = y) A Vx(<j>x D ~ypx) 
This is called the internal negation of (5) since the ~ is as far in as 
possible, negating only the wff \px. 
Now consider the claim 
(15) The person next door exists. 
This can be simply represented as the conjunction of (9) and (10) 
(16) 3*</>Jt A VxVy((<j>x A <f>y) D x = y) 
For Russell the sentence 
(17) The person next door doesn't exist 
would be true if there were two or more people next door as well as if 
there were none, since it would be 
320 


IDENTITY AND DESCRIPTIONS 
(18) ~(3x<f>x A VxVy((<j>x A <j>y) D x = y)) 
though it might be argued that (17) simply means that no one lives next 
door: 
(19) ~3x<j>x 
Finally let us return to (1) and now let us use \j/y not for 'is bald' as we 
have been doing, but for 'is the mayor'. On Russell's account (1) 
becomes the following conjunction: 
(20) ^X(j>x A lxx\px A VJC(<£JC D \//X) 
What we notice about (20) is that it does not use = at all, except of 
course in the unpacking of 31. We can express (20) using = by replacing 
the last conjunct with 
(21) VxVy((<f>x A \j/y) D x = y) 
In the presence of 3lx<f>x and 3'JC^JC, (21) is equivalent to 
(22) Vx(<j>x D \px) 
We come at last to the problem of LI, for we notice that just as in the 
case of ~ , there are two places for L to go. These are not usually called 
external necessity and internal necessity. The contrast is rather the de 
relde dicto contrast mentioned on p. 250, since we may either put the L 
outside all the quantifiers, to get the de dicto reading, or inside, to get the 
de re reading. Now (20) is true but not necessarily true, so putting L in 
front of the whole conjunction gives us a false sentence. And even if we 
replace (22) in (20) by (21), the wff is still false when an L is put in front 
of the whole conjunction. But LI certainly does not license the move from 
(20), in either form, to its necessitated version. What LI does allow is to 
move from (20), using (21) as its last conjunct, to 
(23) 3lx<j>x A llx\px A VxVy((<j>x A \py) D L x = y) 
and this gives us the interpretation we used when we defended LI on p. 
318. 
We even have the possibility of ambiguity in the simpler kind of wff 
321 


A NEW INTRODUCTION TO MODAL LOGIC 
like the conjunction we used to formalize (5). To get a more interesting 
case let <j> represent 
4is the number of planets' 
and \p represent 'is odd'. Then consider 
(24) The number of planets is necessarily odd. 
We shall assume there are nine planets. Then we may distinguish between 
(25) L{^X(j>x A VJC(0JC D fa)) 
and 
(26) 3lx<j>x A Vx(<f>x D L\px) 
(25) is the de dicto reading of (24) and is false, for although there happen 
to be nine planets this is not a necessary fact, and if there had only been 
eight their number would not have been odd. (26) is the de re reading and 
is true. For nine is the number of planets, and nine is odd by necessity, 
for that is a fact of arithmetic. 
Another place for the L to go would be as in 
(27) llx<j>x A LVx(<j>x D \px) 
This is still a de dicto formula, and in the case of (24) the important 
contrast is the de relde dicto contrast. However if we consider 
(28) The person next door necessarily lives next door 
and let <j> mean 'lives next door' and suppose that in fact exactly one 
person lives next door then 
(29) llx<j>x A LVx(<j>x D <j>x) 
is true, but neither 
(30) Ltfxfa 
A VJC(<£X D <j>x)) 
322 


IDENTITY AND DESCRIPTIONS 
nor 
(31) l
xx<t>x A V * ( 0 J C D L<t>x) 
is true. 
The ambiguity between (25) and (26) in the analysis of (24) is 
especially significant since it still arises even though 
(32) L3
lx</>x 
is true. The significance may be seen by comparing the modal case with 
the non-modal case. Compare (25) and (26) as revealing the ambiguity in 
(24) with (13) and (14) as revealing the ambiguity in (12). Although (13) 
and (14) differ in meaning yet, provided that llx<f>x is true, they are 
equivalent. So in the modal case one might expect that since 3lx<j>x is not 
merely true but necessarily true, then (25) and (26) would be equivalent. 
Yet they are not. The importance of this lack of equivalence will be made 
clear in the next section. 
The illustrations used so far in the chapter have involved only one-
place predicates. But it is not hard to think of sentences like 
(33) The height in metres of every house is necessarily odd. 
We suppose that in fact the height in metres of all the relevant houses is 
odd. If 0 means 'is a house', \j/ means 'the height in metres of x is y' and 
X means 'JC is odd', then the de dicto and de re readings of (33) become 
respectively 
(34) Lix(<f>x D (Jy^yx A Vztyzx D xz))) 
and 
(35) VJC(0JC D (3ly\Pyx A Vz(^zx D Lxz))) 
(35) is true, but (34) is not. 
Descriptions and scope 
It is a feature of Russell's theory of descriptions that there is no 
expression in the analysis of (5) on p. 319 which represents the phrase 
'the person next door'. What the conjunction of (9) —(11) does is provide 
323 


A NEW INTRODUCTION TO MODAL LOGIC 
what Russell called a contextual definition of the phrase 'the person next 
door'. That is to say it shows how to take a particular sentence in which 
that phrase occurs and represent it by a wff of LPC. And the recipe 
provides a way of doing this in every case. Despite this Russell does 
introduce a notation for definite descriptions. If we wish to use an 
expression for 'the person next door' we note that, in terms of the 
predicate, 'lives next door' the expression we require is 
(1) 
the x such that x lives next door. 
Russell uses the symbol 1 for this and with <j> for 'lives next door' and \p 
for 'is bald' would write (1) as ix<j>x and (5) as 
(2) 
\pix<j>x 
(2) of course merely labels the problem. It does not solve it. For 
Russell, the real analysis of (5) is given in (6)-(8) on p. 319. 
Nevertheless (2) allows us to see a parallel between definite descriptions 
and quantifiers. In our analysis of (12) on p. 320 in accordance with 
Russell's theory of descriptions we saw that ~ could be put in two 
different places in the formula. A similar ambiguity occurs in the sentence 
(3) 
Someone is not bald. 
If the domain is people then (3) may be represented as either 
(4) 
~3x\f/x or 
(5) 
3JC~\/* 
(Our concern here is not with the question of which of these wff is the 
more natural interpretation of (3). Probably it is (4) though a sentence like 
(6) 
Felicity wasn't here all winter 
would have to rely on such features as context or intonation to 
disambiguate.) 
The difference between (4) and (5) is a difference in the scope of the 
quantifier. In (4) the quantifier has narrow scope with respect to ~ since 
it is inside the ~, while in (5) it has wide scope since ~ is inside it. If 
324 


IDENTITY AND DESCRIPTIONS 
definite descriptions were taken as primitive, in Russell's account they 
would behave like quantifiers in having scope. Taking a cue from natural 
language, some philosophers4 have argued that (2) is really a quantifier-
like expression, and just as 3xa represents 'something satisfies a', and 
can be more explicitly read as 'there is an x such that a' so ix<j>xct can be 
read as 'the <f> satisfies a' or more explicitly 
(7) 
Concerning the x which is <£, a. 
(Strictly speaking, to accommodate cases like (33) on p. 323 we need to 
generalize ix<f>x to ix(3 to represent the unique x which satisfies some 
simple or complex condition /?, and use a[ix(3/x] to express the 
proposition that the unique x which satisfies /?, satisfies a. But our 
illustrations will be easier to follow if we stick with ix<j>x.) 
This enables us to mark the difference between 
(8) 
(?jc<£jc)~\/a and 
(9) ~(ix<j>xWx 
where ix<f>x is an operator which binds any JC free within its scope. Russell 
actually used a somewhat different notation, one which obscures the fact 
that ixcpx works like a quantifier. He treats the i expression itself as a 
complex expression which replaces a variable. Such expressions are often 
called terms. He then uses the 1 -expression in square brackets to indicate 
scope. So (8) and (9) would be written 
(10) [ 1 x<j>x\ ~ \j/( ix<J>x) and 
(11) ~[ix<j>xW(ix<f>x) 
Using scope indicators we can recover unambiguously the original wff in 
the underlying LPC (without i) that analyse (10) and (11). In non-modal 
LPC we have the following important fact. On the assumption that exactly 
one thing is <f> (10) and (11) are equivalent. That is to say, the following, 
on Russell's theory, is valid: 
(12) lxx<j>x D ([uc</>Jt]~\l/(ix<j>x) = ~[ix<}>x\\j/(ix<l)x)) 
When we say that (12) is valid on Russell's theory we mean that when 
325 


A NEW INTRODUCTION TO MODAL LOGIC 
unpacked into primitive notation in accordance with the theory of 
descriptions the resulting formula is valid in non-modal LPC with 
identity. 
Because of this it is customary in non-modal LPC to restrict the use of 
descriptions to cases in which uniqueness is assumed, and in these cases 
the scope indicator [IJC<£JC] can be dropped. The reason this would cause 
trouble in modal logic is of course that, despite Russell's notation, on 
Russell's theory it is really the scope indicator which marks the operator, 
not the occurrence of the description which replaces the variable. And this 
confusion, although it does no harm in non-modal LPC provided 
uniqueness is assumed, is what leads to problems in the modal case. 
As Arthur Smullyan showed,5 we can easily incorporate descriptions 
into modal LPC provided that we retain the scope indicator. If 
descriptions are regarded as quantifiers we can express (25) and (26) on 
p. 322 as 
(13) L(ix<f>x)\l/x and 
(14) (ix<j>x) Lxfrx 
In Russell's terminology these would be written 
(15) L[ix$x]\l/(ix<l>x) and 
(16) [ix<j>x] L\P(ix<t>x) 
In the case of a non-modal language scope does not matter provided that 
uniqueness is satisfied. But, as we remarked on p. 322, when <j> means 'is 
the number of planets' and \p means 'is odd', (15) and (16) are not 
equivalent, even though uniqueness is not merely true but is even 
necessarily true, it being necessary that, however many or few planets 
there are some unique number is their number. Given that the scope 
indicator cannot be dropped, if we want to retain expressions to represent 
definite descriptions, it seems clearer to use the (13)/(14) notation than 
Russell's (15)/(16) and to recognize that Russellian definite descriptions 
are like quantifiers, and only under certain restricted conditions, act like 
names. It is presumably the fact that these restricted conditions are often 
satisfied in non-modal LPC that has led to the assumption that definite 
descriptions are problematic in modal LPC. 
326 


IDENTITY AND DESCRIPTIONS 
Individual constants and function symbols 
It is possible to extend the language of LPC by the addition of individual 
constants and function symbols. We have not done this since, provided 
identity is present, Russell's theory of descriptions enables them to be 
eliminated. We shall discuss individual constants first. Individual 
constants a, b, c can occur in exactly the same positions in atomic wff as 
individual variables can. But they do not occur in quantifiers and their 
values are given by V, not \K. In non-modal LPC the values of individual 
constants are simply members of D, so that if a is an individual constant 
V(a) G D. Predicates are given values as before. It is convenient here to 
introduce explicitly the notion of a term. In a language with individual 
variables and constants a term is an individual variable or constant and 
where tlf ... ,tn are terms and 0 is an n-place predicate then <j>tx...tn is a 
wff. The value of a term differs according as it is a variable or a 
constant. We define VM(/), the value of t with respect to V and /i, as 
(i) If t is an individual constant then VM(f) = V(r). 
(ii) If t is an individual variable then VM(r) = /*(/). 
(iii) If 0 is an n-place predicate and tlt ... ,tn are terms, then 
V„(<^.../„,n.) = 1 iff (V„(/,), . . . . VfiJ.w) 
6 V(*) and 0 
otherwise. 
If this is to be applied to the modal case we must assume that a constant 
a is assigned just one member of D and that this does not change from 
world to world. 
It is not difficult to see that individual constants are theoretically 
dispensable. For we may associate with each constant a a one-place 
predicate <£a such that {u,w) € V(0J iff u = V(a). We may now define 
a as uc0ajc, and use Russell's theory of descriptions to eliminate any wff 
containing ixfax. In this elimination we make use of the fact that the 
scope distinctions embodied in (15) and (16) now make no difference. 
This is because not only is there a unique <£a in each world, but it is the 
same <j>, viz. V(a), which is <£a in each world. And when that happens the 
scope distinctions do indeed collapse and (15) and (16) become equivalent 
and so can be expressed simply as 
(26) 
L^ix^x) 
Function symbols may be illustrated by the mathematical symbol -f. 
In a model in which D is the natural numbers V( + ) is the function which 
327 


A NEW INTRODUCTION TO MODAL LOGIC 
takes any pair of numbers ux and u^ *° m eir s u m- I*1 m e general case, 
where 6 is an n-place function symbol and /,, ... , tn are terms then (6tx 
... Q is also a term. As before constants and variables also count as 
terms. V(0) will be a function from n-tuples from D into a member of D, 
and 
v,((0f,...O) = vwow,... ,^(0) 
We can represent 8 by the n+1-place predicate <f>$9 where <frjcl...xxy 
means thaty is the 6 of xu ... ,;cn. For K,, ... ,wn £ D, and w G W, (M1} 
... ,wn,v,w) € V(<£e) iff v = V(^)(MJ, ... ,w„). With this assignment, for 
any assignment fi to the variables it is the same value of y which satisfies 
Vi£<l>(pCi...xty9w) for every w. Thus there is no difference between 
(27) [ iy</v*,.. .^ny]L^( iy<j>e xx.. . ^ and 
(28) L[iy<j>ex]...xTy]\l/(iy<j>eK]...xay) 
For this reason the scope indicator may be removed and 6xl...xR may be 
defined as ly^fa.. .x^y. 
We must however be extremely careful in interpreting this result, since 
in a modal language most expressions which look like function 
expressions actually turn out not to be. Consider for instance the 
expression, 'the capital of x\ Even if this expression picks out a unique 
individual in each world for any given value of x it need not be the same 
one in each world, assuming it is a contingent matter what something's 
capital is, so that there would be a difference between (27) and (28). 
Where scope makes a difference it is tempting to conclude that 
expressions like 'the capital of x1 should not be treated as terms but 
should be regarded as 1-expressions and analysed according to Russell's 
theory of descriptions. For this reason it may well be preferable to avoid 
altogether the use of function symbols in modal predicate logic. 
Exercises — 17 
17.1 Assume 12 for atomic wff only and assume LI. Prove 12 for all wff. 
17.2 Prove the completeness of K + LNI but without BF. 
17.3 Let </> = 'is a mayor of Wellington', and use Russell's theory of 
descriptions to distinguish two meanings for the sentence 
328 


IDENTITY AND DESCRIPTIONS 
The mayor of Wellington might not have been a mayor of 
Wellington 
where one meaning is a logical contradiction but the other meaning is not. 
Represent each meaning by a wff of modal LPC, and explain why each 
wff has the meaning it does. 
17.4 Show how the view that definite descriptions are like quantifiers 
brings out the parallel between the following two arguments: 
(a) 
Every number is identical with some number 
If it is impossible that every number is even it is impossible that 
some number is even. 
(b) 
The square of 3 is identical with the number of planets 
If it is impossible that the square of three is even it is impossible 
that the number of planets is even. 
17.5 Suppose that definite descriptions are taken as primitive and that the 
logic contains T + BF and the following two principles: 
Vl? 
llxa 
D (VJC0 D 
(3[ixa/x\) 
DD 
llxa D 
a[ixa/x] 
Show that from this we may prove Lllxct D 3xLa. 
17.6 Show how scope-indicating devices enable a distinction to be made 
between the valid principle L3lx<j>x D L[ix<t>x]<j>(ix<f>x) and the invalid 
Lllx<f>x D [ix<f>x]L<f)(ix<f>x). 
Notes 
1 Although this example dates from Frege 1892 the difficulties for modal predicate 
logic to which it draws attention were first raised by Quine 1947. It is not our 
purpose to enter into a discussion of the philosophical problems with which this 
whole area bristles, and we shall confine any philosophical remarks we do make 
to those which bear directly on the interpretation of modal systems. LI is derived 
as a theorem in Barcan 1947. 
2 See Hintikka 1963, p. 70f. 
3 Russell 1905. The technical development of the theory discussed later in this 
chapter occurs in Whitehead and Russell 1910. 
4 For example Montague 1974, pp.61 f. and 249. Also Cresswell 1973, p.l30f. 
5 Smullyan 1948. 
329 


18 
INTENSIONAL OBJECTS 
The last chapter was concerned to show how the classical view of identity 
in modal predicate logic, according to which both LI and LNI on p. 314 
are valid, can accommodate such apparent counter-examples as (1) on p. 
313. In the present chapter we consider accounts of identity in which 
these wff are not valid. 
Contingent identity 
We have observed that LI and LNI might be thought unintuitive, and our 
next task is to see how we might adapt our semantics to avoid having 
them as valid. At first sight this might seem easy. For LI and LNI are 
surely consequences of the fact that for any w, (w,v,w) E V(<£=) iff u and 
v are the very same member of D. So why not say that this may hold for 
some worlds, but not others? 
Unfortunately this response has the consequence that it does not 
validate even the simplest instance of 12. 
(2) x = y D {<j>x D 0y) 
This will fail in a world w for which (w,v,w) G V(</>=) but u and v are 
distinct. We might try defining validity to rule such worlds out, but then 
necessitation would no longer be validity-preserving since provided a 
world w in which </>= is identity can see a world w' in which it is not then 
(3) L(x = y D (<f>x D <j>y)) 
330 


INTENSIONAL OBJECTS 
will fail to be valid. 
The upshot of this is that the problem is deeper than the question of 
what set of triples to assign to V(<£=). Look again at example (1) on p. 
313 (renumbered as (4)). 
(4) The person next door is the mayor. 
Suppose that we are in world w, and that there is some person u who in 
w, is both the mayor and the person next door. Since this fact is, 
presumably, contingent, there must be another world w2 in which the 
person next door and the mayor are not one and the same person. But that 
presumably means that there are a distinct pair of people v and v' such 
that, in w2, v is the person next door and v' is the mayor. And at most 
one of these, perhaps neither of them, will be u. 
Consider now the status of LI: 
LI 
x=yDLx=y 
with respect to an assignment fi to the individual variables. In the situation 
envisaged the antecedent is true in w because n(x) = u and it(y) = w, 
while the consequent is false because x = y is false in w' when [JL(X) = 
v and /x(y) = v\ But this requires /A to give contradictory values. The 
situation seems to be this. We can only falsify LI if we allow fi to give 
the variables different values in different worlds. In the present example 
letting x stand for 'the person next door' would mean requiring /x to 
assign to x in a world w whoever it is who in w lives next door and assign 
to y whoever it is who is the mayor. If we think in this way then of 
course fi(x) and fi(y) may coincide in wx but not in w2. 
For such a semantics1 a model remains a quadruple (W,R,D,V), 
exactly as defined on p. 243. However, an assignment \i is now world 
relative in that for every variable x and w G W, /*(JC,H>) € D. The rule 
for evaluating atomic wff is now 
W ] 
V ^ . ^ w ) 
= 1 iff bi(xltw), ... , /4*n,w),w) G V(0) 
V(</>=) is as before and so we have the result that V^^ = yyw) = 1 iff 
fi(x,w) = /i(y,w). [V ~ ] , [V V ] and [VL] also remain as before. For [VV] 
we need to generalize the notion of an ^-alternative so that /x and p are x-
alternatives iff for every variable y except, possibly, x, and every w € 
331 


A NEW INTRODUCTION TO MODAL LOGIC 
W, p(y,w) = ti(y,w). This semantics does not verify LI. For we need 
merely imagine an assignment jx such that for some w G W, fi(x,w) = 
Ai(y,H>), while for some w' such that wRw', fi(xfw') 5* /-t(y,w'). What the 
semantics does do however is validate all instances of 12, in which a and 
/? contain no modal operators. Systems in which 12 is weakened in this 
way are, for obvious reasons, called contingent identity systems. 
However, it is easy to show that the semantics so obtained would make 
the following schema valid: 
(5) Llxa D 3xLa 
For let (W,R,D,V) be any model, w any world, and /* any (world 
relative) assignment to the variables. For every w' such that wRw', 
VM(3*a,w') = 1. This means there is some ^-alternative, call it vw of \x, 
such that V„ ,(a,w') = 1. Define an jc-alternative p of /x as follows: For 
any w' such that wRw', let p(x,w') = *>„,(*, w'). But then Vp(a,w') = 1 
for every w' such that wRw' and so Vp(La,w) = 1. But p is an x-
alternative of/x, and so VM(3xLa,w) = 1. 
Now this formula (5) is one which we have encountered before (p. 
246), and we remarked then that it is not intuitively plausible. To adapt 
an example given by Quine,2 in certain games it is necessary that some 
player will win, but there is no individual player who is bound to win. 
There is, however, one way in which we could make (5) sound plausible, 
and that is by thinking of an expression such as 'the winner' as in a sense 
standing for a single 'object', though one which in a more usual sense of 
'object' may be one object in a certain situation but a different one in 
another. For in that case, if it is necessary that someone will win then 
there is someone, viz. the winner, who is bound to win. Now we do often 
use phrases of the form 'the so-and-so' in such a way as this. Consider, 
for example, the expression 'the top card in the pack', as it occurs in the 
rules of a card game. The rules may, without ambiguity, specify that at 
a certain point in the play the top card is to be dealt to a certain player; 
yet on one occasion the top card may be the Ace of Spades and on 
another it may be the Queen of Hearts. Thus the phrase 'the top card in 
the pack' does not designate any particular card (individual piece of 
pasteboard), except in the context of a particular state of the pack; yet we 
can in one sense think of it as standing for a single object, contrasted with 
the bottom card in the pack and so forth. 
Such 'objects' are often called intensional objects or individual 
concepts,3 and the rules we have been considering would seem to provide 
332 


INTENSIONAL OBJECTS 
a semantics for a logic in which the individual-variables range over all 
intensional objects. In such a logic, as the above discussion has indicated, 
(5) would be valid and we shall take up the question of this kind of logic 
on pp. 335-342 below. (Where <j>x means 'JC is at the top of the pack', 
and x ranges over intensional objects, then (5) will be true because if it 
must be the case that there is a card at the top of the pack, then although 
no individual piece of pasteboard is bound to be at the top of the pack, 
yet there is something, viz. the top card, which is bound to be at the top 
of the pack. This parallels what we said about the game in which it must 
be the case that someone will win.) 
However, (5) is not in fact a theorem of any of the contingent identity 
(CI) systems, since these are obtained by weakening the LNI systems and 
(5) is not a theorem of any of them. And this shows that what seemed to 
be the most natural semantics for the CI systems turns out not to 
characterize them after all. 
The fault seems to be that the semantics enables us to make an 'object' 
out of any string of members of D whatever. E.g., suppose there are two 
worlds, w, and vv2, then where ux and u2 are members of D we seem to 
be entitled to make up the 'object' which is w, in n>, and u2 in w>2. 
(Roughly, what (5) says is that any string of members of D each of which 
is <j> in some world accessible to w entitles us to assume the existence of 
an 'object' which is <f> in all of them.) 
When we look at the matter in this way we might think of the LNI 
systems as requiring that the only strings of members of D which count 
as objects are strings consisting of the same member of D in each world 
(i.e., the only objects recognized in these systems are the straightforward 
members of D themselves). It seems therefore that an adequate semantics 
for the CI systems would have neither to require that only strings 
consisting solely of a single member of D should count as objects, nor 
that any string whatever of members of D should count as an object. 
One way in which we might achieve such a semantics is to let the set 
of strings which are to count as objects be determined by each model; 
i.e., to let the model specify what assignments to individual-variables are 
to be permissible. Formally we can do this by letting the model contain 
a set I of 'allowable' intensional objects. An intensional object i is really 
a function from W into D. So if w G W, then i(w) is the member of D 
which i 'is' in w. So if i is the person next door then in world w, i(w) is 
whoever it is who is the person next door in world w. A model then 
becomes a quintuple (W,R,D,I,V). An assignment /A gives a value, not in 
D, but in I, and where we have written p(x,w) we shall now write 
333 


A NEW INTRODUCTION TO MODAL LOGIC 
JH(X)(W>), since fi(x) will be some / E I , and consequently fi(x)(w), will be 
i(w).4 The definition of an x-alternative now becomes simple again, p is 
an ^-alternative of /* iff for every y except possibly x, p(y) = /*(y). 
For atomic wff we have 
[V0"] 
V ^ . J ^ W ) = 1 iff <Mfe)(w), ... , , t W W ) 
€ 
V(0) 
and for V 
[W] 
V^(Vjca,w) = 1 iff Vp(a,w) = 1 for every ^-alternative p of /*. 
Note in this definition the differing role of I and D. As far as the 
interpretation to the predicates goes, they are sets of n+1-tuples from D, 
and W, not from I. But as far as assignments to the individual variables 
are concerned their values come from I. We note that both PR and PA 
are still valid. 
Contingent identity systems 
In order to obtain soundness and completeness for systems of contingent 
identity, we need to restrict 12 so that a and (3 contain no modal 
operators.5 In fact we can replace it by 
12" x = y D «>*,...*n = 4>yx...yn) 
where each xit for 1 < i < n either is the very same variable as ys, or 
else x{ is x and y{ is y. (In other words they are two atomic wff in which 
the first has (free) x in 0 or more places in which the second has (free) 
y.) 
In non-modal LPC 12" has the property that the full 12 may be deduced 
from it. (The proof is by induction on the construction of a and (3.) The 
induction will not, however, carry through for L unless we are entitled to 
assume LI, and in the contingent identity systems we do not have LI. It 
is not difficult to see that 12" is valid in the contingent identity semantics. 
For suppose that V^x = y,w) = 1. Then (/xW(w),/x(y)(w),vv) € V(<£=). 
So ix(x)(w) = ju(y)(w). Now by definition of <f>xx...xn and <fry{...yn, for 1 
< i < n, either JC; is yi9 in which case /i(JCj)(w) = fi(yd(w) or else x{ is x 
andy5 is y, in which case also fi(x-^(w) = n(yd(w), and so (yu,(jc,)(w), ... , 
H(xj(w),w) is the very same n+ 1-tuple as (/x(v,)(w), ... , ii(y^(w)fw) and 
soVlA<j>xl...xn,W) = VM(0y1...yn,w)andsoVM(0x1...xn = <i>yx...yn,w) = l. 
This establishes the validity of 12" in the contingent identity semantics. 
334 


INTENSIONAL OBJECTS 
By S + CI we shall denote S + BF with the addition of II and 12". What 
we have just done is establish the soundness of S + CI. The approach to 
completeness will be as before, to define a canonical model. We let D be 
the set of all variables and define I as follows. With each variable x we 
associate an intensional object ix as follows. 
Assume that the variables are in some determinate order and for any 
world w, let ix(x)(w) t>e t n e fifst y m t n e enumeration of variables such 
that x = y is in w. (By II at least x = JC, will be in w.) Let I be the set 
consisting of ix for every variable x, and let the canonical assignment /x 
be the assignment such that /A(JC) = ix. For n-place predicate <f>, and *,, 
... , xn G D, put {xl9 ... ,*n,w) in V(</>) iff <f>xx...xn G w. 
THEOREM 18.1 V„(a,H>) = 1 iff a G w. 
Proof: The proof is by induction on the construction of a. Suppose a is 
<^...*n. Then V^xx...xniw) 
= 1 iff (/i(x,)(w), ... ,/i(0(w),w> G V(0). 
Now (/x(^i)(w), ... ,/i(Xn)(w)) will be some (y,, ... , yj such that^ = y,, 
... , jcn = yn are all in w. By 12" this means that <j>xx...xn = <J>y\...yn is in 
w and so 0jCj...xn G w iff ^y,...^ G w. Now (y,, ... ,yn,w) G V(0) iff 
^,...y n G w. So (y„ ... ,yn,w> G V(<^) iff ^ , , ... ,jcn G w. But (y„ ... 
,yn,w> is (/i(^,)(w), ... ,/t(xJ(w),w) and so VM(^1...^n,w) = 1 iff ^,...x n 
G w. The remainder of the induction is as in theorem 14.3 on p. 261, 
since the fact that fi gives values in I rather than in D makes no 
difference. 
If we impose the requirement that where wRw' and ix(w) = i2(w) then 
/j(vv') = i2(w'), then we have a semantics which will always validate LI, 
but need not validate LNI, though it will validate LNI in all frames in 
which R is symmetrical. Thus some LI systems, e.g. where S is K, T or 
S4, will not contain LNI, while others will, e.g. if S contains B. 
Quantifying over all intensional objects 
On p. 332 we showed that if I consists of all intensional objects — all 
functions from W into D — then certain wff, such as L3x<j>x D 3xL<f>x, 
become valid. So the question arises of what axiomatic systems are 
correct for the logic of intensional objects based on an underlying 
propositional system S. The answer is that for most choices of S, an 
exception being S5, the logic of intensional objects based on S is 
unaxiomatizable. The unaxiomatizability result holds for such systems as 
B, S4.3.1 and all systems contained in either of them. In other words it 
335 


A NEW INTRODUCTION TO MODAL LOGIC 
includes almost every system discussed in this book except S5.6 
To make this claim precise we consider a propositional modal logic S. 
For simplicity we shall confine ourselves to complete propositional logics 
and will consider the class ^f of frames for S. Since I is now the class of 
all functions from W into D we may omit reference to I. So we say that 
a wff a is ^-valid for intensional objects iff V (a,w) = 1 for every w G 
W in every intensional objects model (W,R,D,V) based on some (W,R) 
G &. In what follows we shall assume that ^valid means ^valid for 
intensional objects. The claim then to be proved is that for a significant 
class of propositional systems S ^validity is not axiomatizable. 
We prove this by showing how to translate wff of second-order non-
modal logic into wff of a fragment of modal predicate logic in such a way 
that validity is preserved when the modal predicate logic is interpreted as 
quantifying over all intensional objects. We then use the non-
axiomatizability of second-order logic to establish the non-axiomatizability 
of intensional objects logic. 
We discussed second-order logic briefly on p. 188. The fragment i£ 
that we shall be concerned with contains only one-place predicate 
variables <f>, ^...etc. and a two-place predicate constant/?, usually written 
between its arguments. A model for X is just like a model for first-order 
non-modal logic except that the values of the predicate variables are given 
by fi and not by V. For one-place </>, /*(<£) Q D. Since R is the only 
predicate constant a model (D,V) provides a domain D and a relation 
V(/?) on D. For present purposes D is a set of worlds and V(R) is just the 
accessibility relation R. So we shall refer to D as W, and a model for this 
fragment of non-modal second-order logic is simply a frame for 
propositional modal logic. (Note that the italicized R is the two-place 
predicate of i£, while the unitalicized R is the relation which is its 
interpretation according to V.) An assignment /x, now gives values from 
W to all the individual variables, and subsets of W to the predicate 
variables. Where <f> is a predicate variable then p is a 0-altentative of /x 
iff p and n agree on all the individual variables and on all the predicate 
variables except possibly <j>. The rule for V is: 
[V0] V^(V</>a) = 1 iff Vp(a) = 1 for every ^-alternative p of fi. 
The idea behind what we are going to do is really quite simple. 
Consider first a rather special kind of intensional objects model in which 
D contains only two objects, say 1 and 0. Then we may consider these as 
the two truth-values. Where W is any class of objects every subset A of 
336 


INTENSIONAL OBJECTS 
W may be coded by the intensional object iA such that /A(w) = 1 if w G 
A and iA(w) = 0 if w $ A. 
We may relax this provision in two ways. First, there is no reason why 
in some worlds 1 might be the 'true' value while in other worlds it is 0. 
All we require is that w E A iff /A(w) is the appropriate 'true' value for 
the world w. Second, there is nothing to prevent there being many true 
values and many false values. Of course many different intensional 
objects might then code the same subset A of W since all that is required 
of an i which codes A is that i(w) is one of the 'true' values for 
wifwG 
A, and one of the 'false' values if w £. A. 
The way we stipulate which values are the true ones and which the 
false ones is to translate every wff a of i£ into a wff r(a) of a language 
i£* of modal predicate logic containing a single one-place predicate T, 
and it is those members of D which satisfy T in a world w which count 
as the 'true' values in w, and those which do not as the 'false' values in 
w. Our translation requires that the individual variables of ££* include all 
those of ££ and in addition an individual variable x^ for every predicate 
variable <j> of i£. We show how to translate every wff of ££ into ££* as 
follows: 
r(0x) = M(Tx A 23c,) 
r(xRy) = M(Tx A MTy) 
r(~a) = ~r(a) 
r(a V ff) = (7(a) V r(/3)) 
r(Vjca) = VJCT(CX) 
r(V0a) = V*0T(a) 
The atomic cases may look a little strange, and could do with some 
explanation. The idea is that where x in ££ is assigned a world w, then in 
££* it is assigned an intensional object true (i.e. satisfying 7) only in w, 
and where <j> in £ is assigned a subset A of W then in ££*, x^ is assigned 
an intensional object true in a world w iff w is in A. Then M(Tx A Tx^) 
will be true iff there is an accessible world at which both Tx and Tx^ are 
true. Since x is true only at the world assigned to it in i£, Tx A Tx^ will 
be true iff the world assigned to x in i£ is one of the worlds at which Tx^ 
is true, which means one of the worlds assigned to <j> in 
X. 
M(Tx A MTy) will be true iff there is an accessible world at which Tx 
and MTy are both true. And this will be so iff MTy is true at the world 
assigned to x in i£, and MTy will be true at that world iff it can see the 
337 


A NEW INTRODUCTION TO MODAL LOGIC 
world assigned to y. Note that r(a) is of modal degree at most 2. 
We make all this precise as follows. Where (W,R) is a frame, V 
(strictly V<w R>) will denote the value-assignment for i£ in which V(/?) = 
R. V(a) will then be a truth-value for a determined in accordance with 
the usual rules for non-modal second-order logic. Given any frame (W,R) 
and any intensional objects model (W,R,D,V*) for i£* based on (W,R) 
in which, for every w G W, there is some (u,w) G V*(7) and some 
(v,w) £ V*(7) then for any w G W and any assignment /x to the 
variables of i£ and /x* to the variables of ££* we say that JU. and /x* 
correspond iff for every w G W and every variable x or <f> of ££: 
(i) (/x*W(w),w) G V*(7) iff w = fi(x); 
(ii) </x*(^)(w),w) G V*(7) iff w G xx(0). 
The condition that for each world w, there must be at least one member 
of D which satisfies T in w, and at least one which does not is needed to 
ensure that for every /x there will exist a corresponding /x*. 
THEOREM 18.2 Where a is any wff of X and w G W and wR[i(x) for 
every variable JC, and it and /x* correspond, then V^(a) 
= V(7<a),w). 
The difficult cases are in fact the atomic wff. Take first <j>x. T(<I>X) is M(Tx 
A 7>:0), and V${M(Tx A 7>^),w) = 1 iff for some w' such that wRw' 
(1) 
V*(Fx,w') = 1 
and 
(2) 
V„*(7Vw') = 1 
(1) will hold iff (fji*(x)(w'),w) G V*(7), and, since /x and /x* correspond, 
then by (i), (1) will hold iff 
(3) 
w' = n{x) 
and (2) will hold iff (/X*(*0)(W'),H>') G V*(7). Since /x and /x* 
correspond, then by (ii), (2) will hold iff 
338 


INTENSIONAL OBJECTS 
(4) 
w' € /x(0) 
and clearly there will be a w' (accessible from w) for which (3) and (4) 
hold iff wRfji(x) and /X(JC) G /*(</>), i.e., given wRfi(x)y iff 
(5) 
V,««) = 1 
as required. Now consider xRy. V^{M{Tx A MTy),w) = 1 iff there is 
some w' such that wRw' and 
(6) 
V,*(7*,w') = 1 
and 
(7) 
V*(MTy,w') 
= 1 
Now (6) holds, as before, iff 
(8) 
w' = fji(x) 
And (7) will hold iff there is some w" such that w'Rw" and 
(9) 
V*(Ty,w») = 1 
But (9) holds iff 
(10) w" = n(y) 
And there will be a w' and w" accessible from w and with w'Rw" for 
which (8) and (10) hold iff WRJLI(X) and wR/x(y) and (i(x)Rfi(y), i.e., given 
wR/x(x) and wR/>t(y), iff 
(11) V^xRy) = 1 
as required. 
The induction clearly holds for ~ and V . For V, if V^Vjca) = 0 then 
there is an ^-alternative p of /x such that Vp(a) = 0. Let p* be any 
assignment which corresponds with p. Then by the induction hypothesis 
Vp?(r(a),w) = 0. But p* will be an jc-alternative of jit* and so 
339 


A NEW INTRODUCTION TO MODAL LOGIC 
VMf(V;cr(a),vv) = 0. Analogously if VMJ(V^r(a),w) = 0 then VM(Vjca) = 
0. If VM(V<£a) = 0 then there is a ^-alternative p of /x such that Vp(a) = 
0. Let p* correspond with p. Then Vfi(T(a),w) = 0. But p* will be an 
^-alternative of /** and so VM?(V^r(a),w) = 0. Analogously if 
V^(Vjc^r(a),w) = 0 then V^Vjca) = 0. This proves the theorem. 
We must now link up validity on a frame (W,R) with validity in the 
corresponding model (W,R,D,V*). In doing this we notice that the 
variables JC, y, etc. which occur also in ££ are assigned intensional objects 
which are true at exactly one world. So we need to be able to express the 
fact that a variable in effect denotes a single world. 
Wx =dfMTx A Vy(L(Tx D Ty) V L(Tx D ~Ty)) 
It might be wise to show that Wx really does mean what it is supposed to. 
Let /i* be an assignment to the variables of i£* in any model (W,R,D, V*) 
in which in every world some members of D satisfy T and some do not 
and let w* G W: 
LEMMA 18.3 V*(Wxyw*) = 1 iff there is some w such that w*Rw and 
<M*(*)(w')>W) G V*(7) iff w' = w. 
This of course is what it takes to ensure that /**(*) corresponds with an 
assignment within i£ in terms of the definition, since we may define the 
corresponding fi(x) as the unique w such that (fi*(x)(w),w) G V*(7). We 
prove the lemma as follows. 
(a) Suppose that w*Rw and (/X*(JC)(W'),W') G V*(7) iff w' = w. Then 
clearly Vjt(MTx,w) = 1. And if w' * W,VJ!(TK,W') 
= 0 and so V*(Tx 
D 7>,w') = 1 and V*(Tx D ~Ty,w') = 1. For w, if (n*(y)(w),w) G 
V*(7) then V*(Tx D Tyyw') = 1 and if n*(y)(w) g V*(7) then VMJ(23c 
D ~Tyyw') 
= 1. So either Vh*(L(Tx D Ty),w) = 1 or V*(L(Tx D 
~Ty)yw) = 1. 
(b) Suppose that VMJ(Hfr,w*) = 1. Then since V*(MTK,W*) 
= 1 there 
is some w such that w*Rw and (ti*(x)(w),w) G V*(7). So suppose there 
were also some w' 5* w such that w*Rw' and {n*(x)(w'),w') G V*(7). 
Let p be a ^-alternative of /** such that (p(y)(w),w) £ V*(7) but 
(p(y)(w'),W) G V*(7). Then Vj(23c D 7>,w) = 0, and so V*(L(Tx D 
Ty),w*) = 0 and V*(7x D ~7y,w') = 0 and so Vj(L(7* D ~7»,H>*) 
= 0. So V*(Vy(L(Tx D Ty) V L(Tx D ~Ty)),w*) 
= 0. Thus 
340 


INTENSIONAL OBJECTS 
V^f (Wx,w*) = 0, contradicting its assumed truth. This proves the lemma. 
The consequence of these results may be summed up in the following 
theorem; where (W,R) is any frame in which there is some w* such that 
w*Rw for every w G W. 
THEOREM 18.4 For any wff a of i£ and any frame (W,R), a is valid on 
(W,R) iff (L(lxTx A 3x~Tx) A Wxx A ... A WxJ D 
T(OC) is valid on every IO model (W,R,D,V*) based on 
(W,R), where xl9 ... , xn are the individual variables free 
in a. 
Proof: (a) Suppose (W,R) is a frame where w*Rw for all w G W, and 
suppose VM(a) = 0. Since w* can see every world then it can see each 
/A(JC). For definiteness let (W,R,D,V*) be an IO-model based on (W,R) 
in which D = {1,0} and V*(7) = {(l,w):w G W}. Then, where fi* is 
an assignment which corresponds with /i, V^(r(a),w*) = 0. But if /x* 
corresponds with /*, then Vj?(Wx,w*) = 1 for every variable* free in a. 
Further, for each world w, IxTx and 3JC ~ Tx must both be true in w, and 
so V*(L(3xTx A ax~23c),w*) = 1. So V*((L(lxTx A lx~Tx) 
A Wx{ 
A ... A WxJ 
D T(O),W*) 
= 0. 
(b) Suppose there is some w such that V*(((L(3JCZX A 3x~ Tx) A Wxx 
A ... A Wx^ D r(a)),w) = 0. Then there are wx...wn such that wRw,. 
for 1 < i < n and (jti*(x,)(w'),w'> G V*(7)' iff w' = w,. Let fi be an 
assignment to !£ such that 
(i) ji(x,.) = w,.. 
and, for any w' such that wRw', 
(ii) w' G /i(0) iff (/x*(^),w') G V*(7). 
Since Vjt(L(3xTx A 3*~ 7JC),W) = 1 and wRw', there must be some u G 
D such that (u,w') G V*(7) and some v G D such that (v,w') g V*(7), 
and so there will be a /x satisfying (ii), and since Wflt(Wxl A ... A 
Wcn,w) = 1, lemma 18.3 guarantees that there is a it satisfying (i). But 
then /x and /x* correspond and so since VMJ(r(a),w) = 0 and wRwt then 
v>) = o. 
This proves the theorem. 
The unaxiomatizability of IO systems now follows from the 
341 


A NEW INTRODUCTION TO MODAL LOGIC 
unaxiomatizability of the corresponding second-order logics, since if the 
IO systems were axiomatizable we could effectively enumerate the valid 
wff of i£ by generating their translations. So we will get an 
unaxiomatizability result for an IO system for ^validity in any class & 
of strongly generated frames (i.e. frames where some w* can see every 
world) for which the corresponding second-order logic is not 
axiomatizable. In particular any subsystem of S4.3.1 will be 
unaxiomatizable since the generated frames of such systems will include 
some in which R has a first member and is linear, transitive and discrete. 
Such frames enable a successor predicate to be defined and enable the 
statement of the Peano axioms for second-order arithmetic by a finite set 
of wff whose conjunction we may refer to as Ax. So where S is contained 
in S4.3.1 and £*is the class of all frames for S, then Ax D a will be #• 
valid iff a is a truth of arithmetic. Since second-order arithmetic is not 
axiomatizable then neither is ^validity. Fine has also obtained this result 
for all systems contained in the Brouwerian system B.7 
The unaxiomatizability result is in fact very strong since it applies to 
that fragment of i£* which contains only a single one-place predicate. 
(Obviously if that fragment is unaxiomatizable so is the full language.) 
The fragment need not even contain an identity predicate. 
Intensional objects and descriptions 
There is a natural connection between definite descriptions and intensional 
objects. Take the example of the number of planets. In each possible 
world there is one and only one number which is the number of planets, 
but in different worlds it is different numbers. In the case of the number 
of the planets then the intensional object corresponding to it would be the 
function which in each world has as its value the number which is the 
number of planets in that world. The problem is how to use intensional 
objects to bring out the difference between (13) and (14) on p. 320. 
Recall that intensional objects were introduced as things to be the values 
of the individual variables to prevent the validity of LI. So consider what 
happens to the wff 
(1) 
L^x 
when xp means 'is odd' and /x, assigns to x the intensional object which is 
the number of the planets. 
V^Lxf/XyW) = 1 iff for every w' such that wRw', V^(^JC,W') = 1. And 
this will be so iff (fi(x)(w'),w') G V(^). Now whether a number is odd 
342 


INTENSIONAL OBJECTS 
or not does not depend on which world we are in and so (ii(x)(w'),w') 
will be in V(\^) iff n(x)(w') is odd. Assuming a sense of necessity in 
which there are accessible worlds in which there are an even number of 
planets there will be some worlds w' accessible to w in which fi(x)(w'), 
the number of planets in w', is not odd, and so (1) is false in w. That 
gives us the sense represented by (13) on p. 320. To get (14) we would 
assign to x the number which is the number of planets in the actual world 
w that we begin with, say 9. Or rather we assign the function whose value 
in every world, is the number of planets in this world. So in every world, 
however many planets there are in that world, it is 9 which is claimed to 
be odd. And since 9 is odd in every world this is true. 
It is not difficult to see that, as it stands, this solution is inadequate. 
For consider a frame (W,R) in which W = {W,,H>2} and w,Rw2 and 
w2Rw{. I.e. there are two worlds and each can see the other but neither 
can see itself. In such a frame the principle 
LL 
a = LLa 
is valid, no matter what values are assigned to any symbols in a. In 
particular where (W,R,D,I,V) is any model based on (W,R) and /x, is any 
assignment to the variables and <f> any one-place predicate and w £ W, 
(2) 
V,M*,HO = VM(LL^,w) 
But now consider the model in which D = {ulfu2} and V(</>) = {(wi,w,), 
("2^2)} a nd consider the wff which would be expressed on the Russellian 
account by 
(3) 
L(ix<t>x)L(j>x 
It is clear that 
(4) 
(ix<j)x)<l>x 
is true, and true in each world. For in each world exactly one thing is <f>, 
and it is indeed <j>. But (3) is false. For in w, it says that in w2 the thing 
which is <f> there, in w>2, is also <j> in wlt and that is false. But if we try to 
formalize (3) as 
343 


A NEW INTRODUCTION TO MODAL LOGIC 
(5) 
LL<}>x 
and capture the ambiguity by different assignments to x the validity of LL 
will make sure that (5) is always equivalent to <j>x. 
We shall describe a way out of this problem taken by Thomason and 
Stalnaker,8 though we shall not present it in exactly the same form that 
they do. The aim is to keep ix<j>x as a term expression, i.e. an expression 
which can replace a variable in a wff. This contrasts with the Russellian 
account which, at least in a modal LPC, treats definite descriptions as 
quantifiers (though of course defines them ultimately in terms of the 
resources of ordinary modal LPC with identity.) However they do not 
want the individual variables to range over intensional objects. So LI and 
LNI are true for variables in the form 
LI 
x=yDLx=y 
and 
LNIx ?* y D Lx r* y 
But we do not have 
(6) 
ix<j>x = ix\px D L(ix<f>x = ix\px) 
or the corresponding version of LNI. ix<f>x is assigned as its value the 
intensional object whose value in each world is the unique individual 
which satisfies <f> in that world. Where <f> is not true of a unique individual 
in each world ix<f>x can denote some arbitrary intensional object. 
Given that the variables now range only over ordinary objects we may 
express the distinction between (13) and (14) on p. 320 as 
(7) 
IiKutfx) 
and 
(8) 
ly(y = (ix<j>x) A LM 
Intensional predicates 
A feature of the CI semantics is that while the individual variables range 
over I, the predicates still apply to D. Given that the domain of 
344 


INTENSIONAL OBJECTS 
quantification is I a plausible alternative would seem to be to allow the 
predicates to apply to members of I. And in fact if our models admit 
intensional objects there would seem to be no philosophical objection to 
this. Members of D can then qualify as 'degenerate' intensional objects, 
where i(w) = i(w') for every w and w' G W. So let us now say that 
where <f> is an n-place predicate, V(<£) is now a set of n+ 1-tuples (/,, ... , 
/n,w) where /,, ... , in are taken from I rather than from D. 
This however raises a question as far as identity is concerned. Under 
what conditions do we want x = y to be true in a world w? One 
suggestion is that V^JC = y,w) = 1 iff [x(x)(w) = /i(y)(w). But this has 
the consequence that even 12" is no longer valid. For let i, and i2 be two 
distinct intensional objects whose values coincide in w but not in all other 
worlds. Then let 0 be a one-place predicate such that {iltw) G V(<f>) but 
(i2,w) £ V (</>). Since predicates now apply to members of I, and since /, 
and i2 are distinct, this is a possible assignment. Now suppose that ix(x) 
= i, and n(y) = i2. Then V^* = y,w) = 1, W^x.w) 
= 1, but VJ^y.w) 
= 0. And this falsifies 12" at w. 
And in fact given that the predicates now apply to members of I, it 
seems that the identity predicate ought to also, and in that case we should 
let V(0=) be the set of all and only triples (/,/,w) for i G I and w G W. 
This certainly validates 12", but it also validates LI, and therefore the full 
12. It also validates LNI, and in fact it is not difficult to see that with this 
semantics for </>= we are back with the LNI systems. For suppose that we 
begin with a model (W,R,D,I,V). We define the corresponding model 
<W',R\D',V) by letting W = W, R' = R, D' = I, V = V, and 
dropping all reference to D. Since an assignment \k in (W,R,D,I,V) gives 
values from I, and since the predicates are assigned n-tuples from I and 
W, we need make no other changes in moving from (W,R,D,I,V) to 
(W,R,D',V), and an obvious induction establishes that for all w G 
W(W') and all assignments /i, VM(a,w) = V^cXjW). 
Moving in the other direction, given a model (W,R,D,V) we may 
move to a model (W',R',D',I,V) by letting W = W, R' = R, D' = D, 
and I be the set of all functions from W into D (i.e. the set of all 
intensional objects based on W and D). Let I - Q I be the set of constant 
functions /„ for u G D, such that iu(w) = u for every w G W. For V 
proceed as follows: Nominate some i* G l~ and, for any i G I, if i G 
l~ let i' be i and if i G I—1~ let V be /*. What this means is that /' is i 
if i is a constant function, and /' is i* if i is not a constant function. The 
idea is that i* will be the representative in I - of each non-constant 
345 


A NEW INTRODUCTION TO MODAL LOGIC 
function in I. Each /' will therefore be iu for some u G D, and we put 
(/„,, ... ,i vw) G V'(<£) iff (w„ ... ,wn,w> G V(0). Since each V G I" is 
iM for some w, V'(<£) will be completely determined. For an assignment 
fi with (W,R,D,V) we let \i! be the corresponding assignment such that 
fi'(x)(w) = pipe) for every w G W. A straightforward induction makes 
V^c^w) = V (o,w) for every wff a and every w G W. What this 
means is that a wff will be valid according to the intensional-object 
semantics in which predicates can apply to these objects iff it is valid 
according to the original LNI semantics. 
This result holds for systems without identity, and even for systems 
with identity if <f>= is merely required to respect II, 12 and LNI. But of 
course in this model V'(0=) need not be identity even though V(<£=) is, 
and the question is whether there is an equivalent full model in which it 
is identity. One way of showing that there is is to adapt the completeness 
proof in Chapter 14 so that it applies to non-denumerable languages. For 
one can map the domain of all intensional objects based on D and W onto 
any model whose domain of individuals is the cardinality of all functions 
from W into D. The changes required in the proof of theorem 14.2 on p. 
259 are in fact non-trivial, and lie beyond the scope of this book. 
It is worth reflecting a little at this point on the philosophical 
interpretation of (W,R,D,I,V) models with intensional predicates. In these 
models the predicates apply to members of I and the assignments to the 
variables apply to members of I. So these models may be held to 
represent a philosophical or metaphysical decision to regard the 'objects' 
about which the predicates speak and over which we quantify as 
themselves made up from more basic objects. While this may be 
significant from a metaphysical point of view it does not affect the logic. 
The (W,R,D,V) models after all do not have anything to say about what 
D may be, and there is nothing at all to prevent D being a class of 
intensional objects based on another class of more basic primitive 
objects.9 
It might be instructive to see why the proof of unaxiomatizability on 
pp. 335—342 does not carry over to systems with intensional predicates. 
Look for instance at the induction for V<£a in the proof of theorem 18.2. 
It is required that there be a p* in i£* corresponding to an assignment p 
in i£. This means that p*(fy) is some intensional object i such that for any 
w G W, {i(w),w) G V*(7) iff w G p(<£). On the assumption that in 
every world w there is a u G D such that (u,w) G V*(7) and a v G W 
such that (v,w) £ V*(7) we can let i(w) be u or v as appropriate. This 
puts no constraints whatsoever on V*(7) except that at each world it 
346 


INTENSIONAL OBJECTS 
satisfy 3JC7X A 3x~Tx. But consider what happens if V*(7) is an 
intensional predicate. Then we would need to require that {i,w) G V*(7) 
iff w G /*(<£), and the problem is that there may be no such i. For 
instance suppose there are two worlds w, and w2, and two intensional 
objects i, and i2 with (i„w,) € V*(7) and (i2,w2) € V*(7), but (i,w,) £ 
V*(7) for every i except /,, and (/,w2) £ V*(7) for every i except i2. 
Then where p(</>) = {w,,w2} there is no i such that (p*(i),w) E V*(7) iff 
w € p(<£). 
If we have a coincidence predicate, « , meaning by that a predicate 
true of a pair (/,,/2) at w iff j,(w) = i2(w) then the argument of pp. 
335—342 will apply as before to yield a non-axiomatizability result, for 
we may nominate some variable JC* to denote the 'true' and define Tx as 
x * JC*.10 
Exercises — 18 
18.1 Produce a CI model in which L3x<f>x D 3xL<j>x fails. 
18.2 Show that Vx3y(x = y A Vz{x = zDL(x=yDx 
= z))) is valid 
in IO-models in which I is all intensional objects. 
18.3 Prove that LNI is not a theorem of S4 + I. 
18.4 Show how to express arithmetic in propositional modal logic with 
propositional quantifiers. 
*18.5 
Prove that the logic of S5 with quantification over all intensional 
objects is S5 + CI + the two schemata Llxa D IxLa and VJC3J(JC = y A 
VZ(JC = zDL(x 
= yDx 
= z))). 
*18.6 
Set out a semantics for the approach to definite descriptions 
attributed to Thomason and Stalnaker on p. 344. Provide an axiomatic 
system for it and prove completeness. 
18.7 Show that adding intensional predicates validates LI (in its 
unrestricted form) and LNI. 
18.8 Show that if (W,R,D,V> is a model in the sense of Chapter 13 in 
which D has as many members as functions from the set of variables into 
W then there is an IO-model (W,R,D,I,V*) in which I is the set of all 
functions from D into W and any wff a is valid in (W,R,D,I, V*) iff it is 
347 


A NEW INTRODUCTION TO MODAL LOGIC 
valid in (W,R,D,V). 
18.9 Carry out the proof that if we have a coincidence predicate, « , 
meaning by that a predicate true of a pair (il9Q at w iff/,(w) = i2(w) then 
the argument of pp. 335 — 342 will yield a non-axiomatizability result for 
IO systems with intensional predicates. 
Notes 
1 See Kanger 1957b. 
2 Quine 1953, p. 148, where however the example is used to illustrate a somewhat 
different point. 
3 See Carnap 1947, p. 47, and Frege 1892. 
4 Such a semantics is presented in Parks 1974. The change from fi(x,w) to n(x)(w) 
is not entirely trivial. See Parks and Smith 1974. 
5 Kanger 1957b, Hintikka 1961, 1963. 
6 The history of this problem is somewhat obscure in that the result has been 
'known' for some time though without making it into the literature. R.H. 
Thomason 1970b, p. 132 claims that David Kaplan informed him of the result but 
that it is unpublished and appears only in Kaplan's PhD dissertation, and Garson 
1980 refers to a mimeographed report by Kamp of work by Scott and Kripke. As 
far as we can tell the first published proof of the unaxiomatizabihty of this 
semantics is in Garson 1984. Kripke 1992, p. 72 points out that the problem of 
axiomatizing quantification over intensional objects may be reduced to that of 
axiomatizing quantification over propositions, for which Fine 1970, p. 343 claims 
that an unaxiomatizabihty result obtains via a translation into second-order 
arithmetic. This is elaborated on pp. 284 — 302 of Garson 1984 where a system 
of arithmetic is developed by means of prepositional quantifiers, and the 
unaxiomatizabihty of quantification over intensional objects is reduced to it. For 
S5 with a coincidence predicate Kripke 1992, p. 72 adds to S5 4- CI the two 
schemata L3xa D IxLa and Vjc3y(jt = y A Vz(x = z D L(x = y D x = z))). 
7 Fine 1970, p. 343. 
8 Thomason and Stalnaker 1968, Stalnaker and Thomason 1968. 
9 Among the intensional objects are those mentioned on p. 345 in which the value 
of i is a constant function whose value is the same individual in every world. 
Such functions are sometimes called 'individual essences'. It is also possible to 
follow Plantinga 1976 and take individual essences as basic. Plantinga does this 
because he does not believe that there are individuals in non-actual possible 
worlds. In place of other-worldly individuals he substitutes individual essences. 
What the present paragraph points out is that whatever the metaphysical 
importance of this distinction, it does not affect the logic. 
10 Kripke 1992, p. 73, points out that in this case, even for S5, with intensional 
predicates we obtain the same degree of incompleteness as full second-order logic. 
348 


19 
FURTHER ISSUES 
This chapter discusses some further issues in modal predicate logic. Like 
Chapter 12 it is not intended to be in any way complete. 
First-order modal theories 
In discussing the notation A |- a we observed on p. 211 that there were 
dangers in interpreting it as meaning that there is a proof using the 
members of A as additional axioms of a. When we move to the predicate 
calculus the same care is needed. In fact even more care is needed 
because of the use of first-order predicate logic as a language for a first-
order theory. Consider for instance a (non-modal) theory of a predicate 
P which is intended to mean that x and y are causally connected, and 
suppose that we are working in a scientific theory in which it is assumed 
that there are pairs of things not causally connected. Then among the 
axioms might be 
(1) 
lxly~Pxy 
Any collection A of axioms determines a first-order theory and, provided 
the axioms are all closed wff, there is no problem in defining A f- a by 
saying that there is a proof in LPC of a from A where the axioms and 
rules are those of LPC (PC, Vl, V2, and MP) together with the members 
of A. When we move to the modal case the situation is more complicated. 
Consider a theory in which (1) is an axiom. On the assumption that (1) 
is true but not necessary we cannot allow N as a rule of inference, for 
using it we could derive the false wff Llxly—Pxy. 
For that reason the idea of a first-order theory is less useful in modal 
349 


A NEW INTRODUCTION TO MODAL LOGIC 
predicate logic than in non-modal predicate logic. We can of course 
define A |- a as on p. 211 by saying that it holds iff there are (Su ... , 
/?n G A such that (for some given system of modal LPC) 
h(/J, A ... A fij D a 
and then there is no problem. Or equally one could set out a natural 
deduction system for modal LPC. 
One case in which a modal first-order theory would cause less trouble 
would be where the axioms are supposed to be necessary. For instance 
if P means 'is less than' such wff as Vx~Pxx or VjcVyVz((/>xy A Pyx) D 
Pxz) are not merely true but necessary. Of course to satisfy N they must 
be not merely necessary but necessarily necessary and so on. For if say 
VJC — PXC is an axiom then by N LVx~Pxx is a theorem, and so is 
LLVx~Pxx, and so on. 
Multiple indexing 
Consider how to formalize the sentence 
(1) 
It might have been that everyone actually happy was sad. 
Use <J> to mean 'is happy' and \p to mean 'is sad'. Obviously we cannot 
represent (1) by 
(2) 
MVJC(0JC D 
fx) 
for that envisages a possible world in which all those happy are sad, and 
this can only be so if no one at all is happy. (1) speaks about another 
world in which those who are happy in the actual world are sad. Nor can 
(1) be expressed as 
(3) 
Vx(<f>x D Mfx) 
(3) is closer but it does not require a world in which all those actually 
happy are sad. For each actual happy person there is a world in which 
that person is sad, but it need not be a world in which the other actually 
happy people are sad. Consider 
(4) 
Every loser might have won 
350 


FURTHER ISSUES 
which could be true even in a game which permits no more than one 
winner. In this case 
(5) 
It might have been that every actual loser won 
would be false. Among the ways of dealing with this problem is to 
introduce what is often called an 'actually' operator, A. (1) is then 
formalized as 
(6) MVx(A<f>x D i/tt) 
The problem with (6) is to give a semantics for A. We begin in a world 
Wj, and move to an accessible world w2. But even though we are 
evaluating A<f>x in w2 we are interested in those who are happy in w,. The 
solution is to evaluate wff at more than one index. In (6) when we come 
to evaluate 
(7) Vx(A<j>x D fa) 
w2 is called the evaluation index and w, the reference index. Every wff is 
now evaluated at a pair of worlds, though in most cases the second world 
(the reference index) is simply carried along as a parameter. In particular 
for an atomic wff the rule would be 
[V02] V^xMw)) 
= 1 iff G*to,wi> G V(0). 
As an example of how * ordinary' operators behave look at what the rule 
for M becomes in a double-indexed semantics: 
[VM2] V/i(Ma,(w1,w2)) = 1 iff there is some w3 such that w,Rw3 and 
V » 3 , n > 2 ) ) = 1. 
This means that M operates only on the evaluation world. Assume the PC 
operators and the quantifiers do too. A, however, has the following 
semantics: 
[V^] 
VJAaM.wJ) 
= 1 iff V>,(w2,w2» = 1 
I.e. A turns the reference world into the evaluation world. We can 
illustrate this in the case of (6). We begin with a world wx which we 
351 


A NEW INTRODUCTION TO MODAL LOGIC 
assume to be both evaluation world and reference world. 
(8) \((6)M^i)) 
= 1 
iff there is a world w2 accessible from w, such that 
(9) V„((7),Kw,» = 1 
iff for every ^-alternative p of fx 
(10) Vp(A<J>x D ^,(w2,w,)) = 1 
And (10) will hold iff either 
(11) Wp(A<f>X,(w2iW,)) = 0 
or 
(12) Vp(+x,(w2,wx)) = 1 
(12) will hold iff {p(pc)) e V(^), i.e. iff p(x) is sad in w2. By [V^] (11) 
will hold iff 
(13) Vp«*,<Wi,Wi» = 0 
and (13) holds iff p(x) is not happy in u>,. So (6) does indeed hold in w, 
iff there is some accessible world w2 such that everyone who is happy in 
w, is sad in w2. 
It is clear that corresponding to A there are a variety of other doubly 
indexed operators. The locus classicus of propositional logics of these is 
in a paper by Krister Segerberg.1 Segerberg considers the following 
operators. 
• , 01, B, ©, 0 , <8). 
His semantics for these operators may be expressed by the following 
principles: 
V(Da,(w1,w2)) = 1 iff V(a,(w>3,w4)) = 1 for every vv3, vv4 E W 
V(Q]a,(H'I,w2)) = 1 iff V(a,(w,w2)) = 1 for every w € W 
352 


FURTHER ISSUES 
V(Ba,(w„W2)) = 1 iff V(a,(w,,w)) = 1 for every w E W 
V(©a,(Wl,w2» = 1 iff V ^ ^ w , ) ) = 1 
V O o , ^ , ^ ) = 1 iff V(a,(w2,w2» = 1 
V(®a,(wuw2)) 
= 1 iff V ^ K w , ) ) = 1 
Segerberg then produces a system with 6 schemata which hold for various 
selections of wff with just one of these operators, and then a further eight 
principles which relate various combinations of operators. He then uses 
the method of canonical models to prove completeness. • — B are, as 
he notes, S5 modalities, while 0 — <g> are 'very strong K-modalities of 
rather unusual kinds'. 
Doubly indexed logics can be extended to logics having even more 
indices, even infinitely many and have applications in the semantics of 
natural languages.2 
Counterpart theory 
We saw in Chapters 15 and 16 that the Barcan formula could be 
interpreted as expressing the view that exactly the same objects exist in 
all possible worlds. At the other extreme is the view, taken by David 
Lewis, that each world has its own domain of individuals and that these 
never overlap.3 The semantics for modal predicate logic assumed in 
Chapters 13 — 17 makes essential use of the fact that the same individual 
can exist in more than one world and so the question arises of how to 
incorporate Lewis's view in a modal LPC. 
One way to incorporate it is to use intensional objects, for then the 
domain of quantification is functions from W into D, and that domain can 
remain constant even if the value of an intensional object in one world is 
never the same as the value of an intensional object in another world. In 
this case we would use a (W,R,D,I,V) model, or rather a (W,R,D,Q,I,V) 
model since we want each world to have its own domain of individuals. 
We should require that when w ^ w' then Dw H Dw, = 0 . If we use 
this technique we can see that it will make no difference to the logic since 
the domain of quantification is not D but I, and we may define an 
equivalent model (W',R',D',V), by letting D' = I and omitting both D 
and Q. As we remarked on p. 346 the nature of D' in (W',R',D',V), 
however important it may be in metaphysics, has no effect on the logic. 
Looked at in this way Lewis's metaphysical views can be incorporated 
into modal systems with both LNI and BF. 
However, this is not the approach Lewis takes. Lewis himself only 
provides a semantics for modal LPC indirectly, by giving a translation 
353 


A NEW INTRODUCTION TO MODAL LOGIC 
procedure for converting every wff of modal LPC into an extensional 
non-modal LPC in which there are variables for possible worlds and 
accessibility is represented by a two-place predicate. But this translation 
trivially induces a direct interpretation to a language of modal LPC. 
One feature of Lewis's semantics is worth commenting on since it 
affects the interpretation of the predicates. Let us consider a one-place 
predicate <f>. So far V(<£) has been a set of pairs of the form (u,w) with 
u € D and w E W. But if u can exist only in one world and we restrict 
our predicates to things which exist in that world then we can assign to 
<f> simply a set of individuals. Where V*(0) is a set of individuals then 
V(</>) will be the set of pairs (w,w) such that u £ Dw and u G V*(</>). 
Conversely we put u £ V*(0) iff (u,w) £ V(<£), where w is the unique 
world such that u G Dw. Obviously this procedure would not work if u 
could be in more than one world, since it might be <f> in w but not in w'. 
The [V</>], [V~], [VV] and [VV] which are induced by Lewis's 
translation all remain the same, but [VL] requires modification. A model 
for interpreting Lewis's theory may be defined as a 6-tuple 
(W,R,D,Q,C,V) in which (W,R,D,Q,V) is a model as for the systems in 
Chapter 16, but with the restriction that the domains of distinct worlds 
have no common members. C is a relation on D, where uCu' means that 
u' is a counterpart of u in another world. C satisfies the constraint that 
if u and «' are both in Dw then uCu' iff u = u'. Lewis's idea is that when 
we talk about what happens to an individual u in some other world, as we 
might when we say for instance that a particular table might have looked 
better nearer the window, we are not really referring to the very same 
individual in that other world, but are referring to its counterpart, to the 
thing in that other world which corresponds most closely with the thing 
in this world. The rule then is 
[VL'] 
VM(La,w) = 1 iff Vp(a,w') = 1 for every w' such that wKw' and 
for every assignment p such that for every x free in a fi(x)Cp(x) 
and p(x) G Dw,. 
We say that a is valid in such a model if it is true in every world for 
every assignment taken from the domain of that world. 
What modal logic do we get with this semantics? Well, that depends 
on what conditions the counterpart relation C satisfies. The most stringent 
condition is that C is an equivalence relation, and that every individual 
has one and only one counterpart in every world. With this requirement 
it turns out that we get precisely the same semantics as for the LNI 
354 


FURTHER ISSUES 
systems. For suppose that we have a model (W,R,D,Q,C,V). We define 
an equivalent model (W',R\D\V'> as follows. W = W and R' = R. 
For D' proceed as follows. Choose some world w* in W, and let D' be 
D ^ (i.e. Q(w*)). For ul9 ... ,wn G D ' a n d w G W let (uu ... ,un,w) G 
V'(0) iff, where v,, ... ,vn are the unique members of Dw such that WjCvj 
for 1 < i < n, (vj, ... ,vn) G V(</>). What this means is that we take the 
individuals of the new model to be the members of some selected world 
w*, and stipulate that they are to do in another world w what their 
counterparts in w do in the original model. 
In what follows we shall use /A and v for assignments within 
(W,R,D,Q,C,V) and p and a for assignments within (W',R',V). Given 
any w G W we shall say that p corresponds with fi in w provided that for 
every variable x, p(x) is the unique v G Dw such that fi(x)Cv. 
LEMMA 19.1 Where a is any wff and w G W, and /x and p are any 
assignments which correspond in w, then V^(a,w) = 
V>,w). 
Suppose a is <j>xx...xn. Then Wp(<i>xl...xn,w) = 1 iff 
(i) 04*,), - ,MW,W) G V(«) 
Now if fi and p correspond in u>, each p(x-X for 1 < i < n, will be the 
unique v; such that ^(x^Cv;. But then (i) will hold iff 
(ii) (,(*,),... ,PW) G V ( « 
and (ii) holds ifVfl(<j>xl...xn,w) = 1. 
So the lemma is proved for atomic wff. The induction for ~ and V 
is straightforward. So consider V and suppose that p corresponds with /x 
in w. 
Suppose V^(yxoiyW) — 0. Then there is some jc-alternative v of /x such 
that V„(a,w) = 0. Let a be the ^-alternative of p such that o(x) is the 
unique u G w* (where w* is the arbitrarily chosen member of W whose 
domain is D') such that uCv(x). Since v{x) G Dw this means that v 
corresponds with o in w, and so Va(a,w) = 0. But a is an jc-alternative 
of p, and so V^(VJC«,W) = 0. 
Suppose Wp(Vxct,w) = 0. Then there is some ^-alternative a of p such 
that Wa(a,w) = 0. Let v be the jc-alternative of a such that i>(x) is the 
355 


A NEW INTRODUCTION TO MODAL LOGIC 
unique v E Dw such that a(x)Cv. Then v corresponds with a in w and so 
V„(a,H>) = 0. But v is an ^-alternative of JX and so V^VxctyW) = 0. 
Suppose VM(La,w) = 0. Then there is some w' such that wRw' and 
V„(a,w') = 0 where v corresponds with \L in w'. Now fi corresponds with 
p in w, and since C is transitive and v corresponds with y. in w' then v 
corresponds with p in w'. So V^(a,w') = 0 and so \'p(La,w) 
= 0. 
Suppose Wp(La,w) = 0. Then there is some w' such that wRw' and 
Vp,(a,w) = 0. Where v is an assignment which corresponds with p in w', 
then, by the induction hypothesis V„(a,H>') = 0. Now /* corresponds with 
p in w>, and so, since C is an equivalence relation, v corresponds with [K 
in w'. But then by [VZ/], V^Locw) = 0. 
Now it is clear, first that where (W,R,D,Q,C,V) and (W',R',D',V') 
correspond in the way described the lemma entails that any wff a is valid 
in one iff it is valid in the other. Second, as we have seen, given a 
(W,R,D,Q,C,V> you can define a (W',R',D',V), but also given a 
(W',R',D',V'> you can define an equivalent (W,R,D,Q,C,V) by taking 
D' and letting Dw be the set of pairs (w,w>) for each u € D, and letting 
(w,w)C(v,w') iff u = v. 
This is in fact the way Lewis himself imagined someone claiming that 
counterpart theory is just ordinary modal predicate logic in disguise. For 
what we have shown is that if C is an equivalence relation and every 
individual has a counterpart in every world then the modal predicate logic 
of counterpart theory is just that of ordinary modal logic with the Barcan 
Formula. Lewis's reply is that C need not be an equivalence relation.4 He 
wants it to be reflexive since everything is its own counterpart in its own 
world, and nothing else is its counterpart in its own world. If C is 
required to be reflexive but nothing else then, although T is valid, even 
such simple K-theorems as 
(1) 
L{<t>x A V*<£x) D LVx<j>x 
fail.5 For consider the following model (W,R,D,Q,C,V): 
W = {wl9w2}9 R = W2, D = {Wl,«2}, D 
= {«,}, D„2 = {u2} 
C = {<"„«!>, (W2,W2)}, V(0) = {«,} 
I.e., there are two worlds, each with one individual and no trans-world 
counterparts, and <f> is only true of «, in w,. Let fi be an assignment such 
that fi(x) E Dw , and consider any assignment p such that fi(y)Cp(y) and 
356 


FURTHER ISSUES 
p(y) G Dw for every y free in <f>x A Vx<f>x. In fact there is no such p, 
and so, by2[VL'], VM(L(#* A VJC<£JC),W,) = 1. But where a(y) = U2 for 
every y then V Jyx<j>x,w^) = 0, and (trivially) fi(y)Ca(y) and a(y) G Dw 
for every v free in VJC0*. SO V^LVJC^W,) = 0, and thus V^Ltyx A 
Vx<f>x) D LVx<}>x,wx) = 0 in this model. 
The matter is different for closed formulae. In the case of a closed 
formula [VZ/] reduces to [VL] since PA still holds in counterpart-theoretic 
semantics and the assignment to the variables does not affect the truth of 
closed wff. 
Counterparts or intensional objects? 
In counterpart theory the values assigned to individuals may change from 
world to world. Another way of realizing this possibility is by the 
assignment of intensional objects, and we shall now compare this with 
Lewis's semantics. We have seen that counterpart theory only becomes 
significant when the counterpart relation is not an equivalence relation, 
and then the rule for L requires that x be necessarily <j> only if in every 
accessible world all its counterparts in that world are <f>. 
When we look at the semantics for intensional objects we see that 
although each particular intensional object has just one counterpart in each 
world there is nothing to stop distinct intensional objects coinciding in one 
world but differing in another. Suppose then that i(w) and i'(w) are the 
same object, say w. Then if i(w') 5* i'(w') and i(w') is v and i'(w') is v' 
then we can say that v and v' are counterparts in w' of u. 
Suppose that fi(x) is i and fi(y) is /' in the intensional objects semantics. 
Then VM(L#x,n>) = 1 iff <j>x is true in all accessible worlds, and in w' this 
will be so if v satisfies <j> in w', while VM(L0v,w) = 1 iff <j>y is true in all 
accessible worlds, and in w' this will be so if v' satisfies <j> in w'. This 
feature of the intensional objects semantics embodies the assumption that 
it is the intensional object itself which determines what its counterparts 
are. For Lewis the range of the quantifier in each world is just the 
ordinary things in this world, and it is part of the model (and one might 
even say frame if you think that all but V should be part of the frame) to 
say what the counterpart relation is. 
On the assumption that the counterpart relation is symmetrical, though 
not necessarily transitive, one can express counterpart theory in CI 
systems as follows. Wherever Lewis has L<j>x this should be replaced by 
(1) 
Vy(x = v D L<t>y) 
357 


A NEW INTRODUCTION TO MODAL LOGIC 
This translation is of course under the proviso that the domain I of 
intensional objects is so restricted that all the D^s are disjoint and that 
where u G Dw and v G Dw, then wCv iff there is some i G I such that 
i(w) = u and i(w') = v. 
Lewis does not accept that C is in general symmetrical, but in the cases 
where it is this translation has the advantage that, being in a CI system 
with no extra logical symbols, all the principles of the propositional modal 
systems on which it is based carry over to S + CI. By varying the 
translation we can also express what it would be for some counterpart of 
x to be <j> in every world, viz., 
(2) 
1y(x = y A L<j>y) 
In order to express this in the modal logic of counterpart theory, we 
would need a different symbol, say L', satisfying 
[VL"] 
VM(L'a,w) = 1 iff for every w' such that wRw', there is some 
assignment p such that for every x in a, p(x) G D„,, and ix(x)C 
p(x). 
Notes 
1 Segerberg 1973b. Other work on multiply indexed logic has been done by 
Aqvist 1973 and Crossley and Humberstone 1977, Kuhn 1989 and others. The 
phenomenon was noticed for tense logic by Prior 1968 and discussed by Kamp 
1971, Vlach 1973 and Gabbay and Rohrer 1979 and, more recently, Venema 
1992. Theorems to the effect that 'actually' operators cannot be defined in 
ordinary modal predicate logic have been proved by Hazen 1976. See also Hodes 
1984a and 1984b and Hazen 1990. 
2 Kuhn 1979 shows how to use multiple indexing to express the predicate calculus 
as a normal (multi-) modal propositional logic. Applications in the philosophy of 
language are discussed in Forbes 1989 and Cresswell 1990. 
3 The view was originally put forward in D.K. Lewis 1968. A more recent 
defence of the metaphysics underlying it is found in D.K. Lewis 1986. 
4 D.K. Lewis 1968 p. 115. We read this passage as an acknowledgement that if 
the counterpart relation is an equivalence relation then there may be no more than 
a terminological difference between counterpart theory and the more standard 
semantics. 
5 We owe this point to Lin Woollaston, who is attempting to come up with a 
revision of [VL'] which would validate all of K and yet be acceptable to 
counterpart theorists. A discussion of counterpart-theoretic semantics for modal 
logic may also be found in Hazen 1979. 
358 


AXIOMS, RULES AND 
SYSTEMS 
In this book, we have discussed many modal systems. These systems have 
often been introduced to illustrate various properties that modal systems 
possess. Our aim in this appendix is to list the axioms and rules which 
define these systems and present them together all in one place. This will 
show the wide range of modal systems which have been studied, and will 
enable readers to see at a glance the place each system occupies in a map 
of modal systems. 
Axioms for normal systems 
We shall first list the axioms which define the normal systems we have 
discussed, and give them the names they have been given in the text. In 
a few cases (mainly in exercises) axioms or systems have been introduced 
without giving them names, and in these cases a name has been supplied 
here. In other cases the axiom has been referred to by name in the notes, 
but without identifying it. Such axioms also will be listed here. And 
finally there are a few axioms discussed in other works but not in our 
text. Where an axiom is not discussed in the text a work is cited in which 
it is discussed. We do not pretend to provide a complete survey of axioms 
which have been suggested for modal systems. 
Some axioms have alternative names. Mostly these derive from 
Lemmon and Scott 1977 and are used in Segerberg 1971, Chellas 1980 
and by other authors. These names have been given in parentheses. We 
are assuming a language of modal propositional logic as defined on p. 16 
in which L is taken as the primitive modal operator, and M is defined as 
~ L ~ . Axioms are listed in order of introduction except for a few cases 
359 


A NEW INTRODUCTION TO MODAL LOGIC 
in which the first mention does not give adequate information. 
K 
L(pD 
q)D (Lp D Lq) 
(p. 25) 
T 
Lp D p 
(p. 42) 
D 
Lp D Up 
(p. 43) 
4 
Lp D LLp 
(p. 53) 
E 
Mp D LMp 
(5, p. 58) 
B 
p D LMp 
(p. 62) 
Tc 
p D Lp 
(p. 66) 
Triv 
P • Lp 
(p. 65) 
Ver 
Lp 
(p. 67) 
Ex 
LMLp D p 
(p. 69) 
E2 
MLp D LMLLp 
(p. 69) 
Dc 
Mp D Lp 
(p. 123) 
Dl 
L(Lp D q) V L(Lq D p) 
(Lem, p. 128) 
F 
(LMp A LMq) D M(p A q) 
(p. 131) 
M 
LMp D MLp 
(P- 131) 
Gl 
MLp D LMp 
(p. 134) 
W 
L(Lp D p) D Lp 
(p. 139) 
MV 
MLp V Lp 
(p. 141) 
Rl 
MLp D (p D Lp) 
(p. 141) 
BM 
p D LMMp 
(p. 141) 
TM 
MLp D Mp 
(p. 141) 
BV 
ML(p A ~p) V (q D LMq) 
(p. 141) 
Lem0 
L((p A Lp) D q) V L((q A Lq) D p) 
(p. 141) 
HI 
p D L(Mp D p) 
(p. 142) 
Go 
M(p A Lq) D Lip A Mq) 
(p. 142) 
AIt„ 
Lp, V L(p, D p2) V ... V L(ipx A ... A ^ 3 P„+,)(p. 142) 
4t 
(Lp A p) D LLp 
(p. 142) 
J l 
L(L(p D Lp)D p)D 
p 
(Grz, p. 142) 
Mk 
L(LLp D Lq) D (Lp D q) 
(p. 154) 
Mk* 
L(LLp D LLLp) D (Lp D LLp) 
(p. 156) 
Segn 
(MMpx A ... A MMpJ D M(Mp, A .. . A MpJ 
(p. 158) 
H 
L(Lp = p) D Lp 
(p. 160) 
VB 
MLp V L(L(Lq D q) D q) 
(p. 169) 
KHn 
L\L(Lp =p)D 
Lp) 
(p. 170) 
Nl 
L(L(p D Lp) D p) D (MLp D p) 
(Dum, p. 180) 
G' 
MmL"p D Vfrfp 
(p. 182) 
MTn 
M((LPl D Pl) A ... A (Lpn D pj) 
(p. 185) 
360 


AXIOMS, RULES AND SYSTEMS 
B + 
Lp D (Mq D L(Lp V Mq)) 
(p. 219) 
Z 
L(Lp D p) D (MLp D Lp) 
(Segerberg 1971, p. 84) 
P 
MLMp D (p D Lp) 
(Segerberg 1971, p. 152) 
Zem 
LMLp D (p D Lp) 
(Segerberg 1971, p. 152) 
Sch 
L(MLp D Lp) V Lq V L(q D r) 
(Segerberg 1971, p. 159) 
M18 
(MLp D p) V (LMq D MLq) 
(p. 284) 
Some normal systems 
We define a system S as a class of wff whose members are called its 
theorems. We write |-s a for a G S. A normal system of modal 
propositional logic (see p. Ill) is a class S of wff of modal propositional 
logic which contains all PC-valid wff and K, (L(p D q) D (Lp D Lq), 
p. 25); and has the property that if a and /? are in S then so is anything 
obtainable from them by the use of the following rules: 
US: 
|-« - 
M/V/>i, .- ,fl/pj. 
MP: \- a, a D (3 -» 
\-(3. 
N: 
|- a -> 
\- La. 
The weakest normal modal system is called K (p. 24) and every normal 
system S may be expressed as K + A (see pp. 39, 111) where A is the 
set of proper axioms of S. Where A contains just a single wff a then S 
may be expressed as K + a. Where S is a system of modal logic we shall 
use the notations S + A or S + a analogously with K + A and K + a 
to denote the system obtained from S by adding the members of A as 
additional axioms. 
The following list identifies most of the normal modal systems which 
have been given names in the text, and a number of others as well. In 
addition, any normal modal system may be defined by means of a list of 
axioms. Thus, although this system has not, to the best of our knowledge, 
been studied, KHLemo would denote K + H + Lem0. In some cases, 
e.g. T + W, the resulting system will be inconsistent in the sense of 
containing all wff. (We shall denote the inconsistent system by !£.) Note 
that the same system can easily result from different combinations of 
axioms. Thus T + E = T + 4 + B. Where a system is characterized by 
a simple semantics this has been mentioned. 
(M, p. 41, reflexive frames) 
(p. 43, serial frames) 
(KT4, p. 53, reflexive transitive frames) 
(KTE, KT5, p. 58, equivalence frames) 
(KTB, p. 62, reflexive symmetrical frames) 
T 
K + T 
D 
K + D 
S4 
T + 4 
S5 
T + E 
B 
T + B 
361 


A NEW INTRODUCTION TO MODAL LOGIC 
(p. 64, transitive frames) 
(p. 64, symmetrical frames) 
(p. 64, serial reflexive frames) 
(p. 64, serial symmetrical frames) 
(pp. 65, 108, one reflexive world) 
(pp. 66, 108, one dead end) 
(p. 69, euclidian frames) 
E 
(symmetrical euclidian frames) 
(p. 70, one-world frames) 
(p. 70, If wR n +V then wRV) 
(p. 123, every world can see at most one world) 
(p. 139, finite irreflexive transitive frames) 
(p. 142, every world can see at most n-worlds) 
(1 < n) 
(p. 158) 
(p. 160, incomplete, KH frames characterize KW) 
(P- 219) 
An area of modal logic which was singled out for special study in earlier 
days was extensions of S4. Not all of the following are discussed in the 
present text. Details may be found in Sobocinski, 1964a—c. 
K4 
K + 4 
KB 
K + B 
KD4 
D + 4 
KDB 
D + B 
Triv 
K + Triv 
Ver 
K + Ver 
KE 
K + E 
KBE 
K + B + 
Tc 
K + Tc 
S4n 
K + 4n 
KDC 
K + Dc 
KW 
K + W 
KAltn 
K + Alt,, 
BSeg 
B + Segn 
KH 
K + H 
B + 
B + B+ 
S4.1 
S4 + Nl 
S4.2 
S4 + Gl 
(p. 134, convergent S4 frames) 
S4.2.1 S4.2 + Nl 
S4.3 
S4 + Dl 
(KT4Lem, p. 128, connected S4 frames) 
S4.3.1 S4.3 + Nl 
(D, p. 180, discrete time) 
S4.4 
S4 + Rl 
(p. 284, (w1Rw2 A w, ^ w2 A w,Rw3) D w>3Rw2) 
S4.9 
S4.4 + M18 
(p. 284) 
S4M 
S4 + M 
(Kl, S4.1, p. 131, reflexive final frames) 
(Kl is Sobocinski's name for S4M) 
Kl.l 
S4 + J l 
(p. 142, finite partial orderings) 
K1.2 
Kl + HI 
K2 
S4.2 + M 
K2.1 
K2 + J l 
K3.1 
S4.3 + J l 
(D*, p. 191, finite reflexive linear frames) 
K4' 
K2 + Rl 
(K4, S4.2MR1) 
(K4 is Sobocinski's name, see Hughes and Cresswell 1968, p. 266; K4' 
should not be confused with the K4 of p. 64.) 
Another area of study has been extensions of K4 not containing S4. 
(K4 here is K + Lp D LLp, not the system Sobocinski calls K4, which 
362 


AXIOMS, RULES AND SYSTEMS 
we have called K4\) In many cases these systems are characterized by 
transitive irreflexive frames which correspond with the reflexive frames 
which characterize extensions of S4. Thus, for instance, where S4.3 is 
characterized by reflexive connected frames K4.3 (K + Lenio) is 
characterized by transitive irreflexive frames in which for w ^ w', either 
wRw' or vv'Rw, and so on. These systems are discussed in Volume 2 of 
Segerberg 1971. Despite their names, they are not extensions of the 
Kl — K3.1 mentioned in the previous list. 
K4Z 
K4 + Z 
K4.2 
K4 + G0 
K4.2Z K4.2 4- Z 
K4.2W K4.2 + W 
K4.3 
K4 + Lem0 
K4.3Z K4.3 4- Z 
K4.3W K4.3 + W 
A diagram showing most of the normal modal systems listed here apears 
in Table I on p. 367. 
Non-normal systems 
Non-normal systems are systems which lack the rule of necessitation. In 
all other respects the ones that concern us are like normal systems. As 
described in Chapter 11 the earliest modal systems were in fact non-
normal. We shall follow Segerberg 1971 in dividing non-normal systems 
into 'quasi-normal', 'regular' and 'quasi-regular'. Quasi-normal systems 
are systems which contain all theorems of K, so that N applies to those 
wff, but contain extra axioms as well, to which N need not apply. 
Semantically these systems are studied by assuming a subset of 'normal' 
worlds and defining validity in terms of truth only in those worlds. In this 
book we have not been concerned with quasi-normal systems. (But see p. 
208, n25.) 
Regular systems are like normal systems except that N is replaced by 
the rule R* |- a D /J -* \-Lot D L(3. The weakest regular system may 
be called E2°, and its basis consists simply in replacing N by R*. 
Semantically its frames are as described on p. 208, n25, in which in 
addition to normal worlds there may be non-normal worlds in which La 
is false for every wff. If we insist that there must be such worlds we 
validate MMct (or ~LLa), and obtain a system we might call E6° by 
adding MMp as an additional axiom. If we insist that all worlds be non-
363 


A NEW INTRODUCTION TO MODAL LOGIC 
normal then we add Mp. E2 results from E2° by the addition of T and its 
frames are those in which R is reflexive over normal worlds. E3° is E2° 
+ L{p D q) D L(Lp D Lq) and E3 is E2° + T. In E3 frames R is 
transitive in normal worlds. 
Quasi-regular systems are those whose semantics involves regular 
frames in which validity is defined as truth in all normal worlds in all 
models based on the frame, and include the 'Lewis' systems S2 and S3 
described on pp. 200—202. For every regular system E there is a 
corresponding quasi-regular system E* defined as {La: a G E}. Thus S2° 
is E20*, S2 is E2*, etc. Axiomatic bases for these systems are described 
in Chapter 11. As before we may require that there be at least one non-
normal world by adding MMp as an axiom. 
All these systems may be listed as follows beginning from E2°. 
E2 
E2° + T 
E3° E2° + L(p D q) D LiLp D Lq) 
E3 
E3° + T 
E6° E2° + MMp 
E6 
E6° + T 
E7° E3° + MMp 
E7 
E7° + T 
E+ 
E2° + Mp 
S2° E2°* (i.e. {La : a € E20}) 
52 
E2* 
S30 E3°* 
53 
E3* 
S3.5 S3 + Mp D LMp 
S6° S2° + MMp 
56 
S2 + MMp 
S7° S30 + MMp 
57 
S3 + MMp 
58 
S3 + LMMp 
59 
S3.5 + MMp 
No non-normal system contains any normal system since they all lack 
LLip D p). A diagram of non-normal modal systems appears in Table II 
on p. 368. 
364 


AXIOMS, RULES AND SYSTEMS 
Modal predicate logic 
In this section we summarize the bases of the various systems we discuss 
in Part III. The formation rules for predicate logic are given on p. 236 
and for modal predicate logic on p. 243. Where S is a (normal) system 
of modal predicate logic LPC + S may be defined as on p. 244: 
S' 
If a is an LPC substitution-instance of a theorem of S then a is an 
axiom of LPC + S. 
Vl 
If a is any wff and x and y any variables and a[y/x] is a with free 
y replacing every free JC, then Vjca D a\y/x] is an axiom of LPC 4-
S. 
N 
If a is a theorem of LPC + S then so is La. 
MP If a and a D 0 are theorems of LPC + S then so is (3. 
V2 
If a D (3 is a theorem of LPC + S and x is not free in a then 
a D Vx(3 is a theorem of LPC + S. 
Where BF is the schema VjcLa D Dixa (p. 244) then S + BF is LPC + 
S + BF. Validity for BF systems is defined on p. 243. Its key feature is 
that there is a single domain of individuals for all worlds. A canonical 
model may be defined for S + BF as described in Chapter 14. If S + BF 
is complete it will be characterized by the class of all frames for S. The 
completeness of S + BF will follow in all cases where the frame of the 
canonical model for S + BF is a frame for S. In particular, where S is 
K, D, T, K4, D4, B, KB, DB, DE or S5 completeness follows 
immediately with respect to the class of frames for the propositional 
system. It is not automatic however and does not hold for S4M + BF, 
KG1 + BF or S4.2 + BF. For LPC + S domains are allowed to vary 
provided that if wRw', Dw Q DJ. 
(This is called the 'inclusion' 
requirement, p. 275.) For systems with an existence predicate E, LPCE 
+ S may be axiomatized as on p. 293: 
S' 
Any LPC substitution-instance of a theorem of S is an axiom of 
LPCE + S. 
VlE Where x and y are any individual variables, and a is any wff then 
(Vxa A Ey) D a[y/x] is an axiom of LPCE + S. 
VD 
Vx(a D 0) D (Vxa D Vx(3) (where a and (3 are any wff and x is 
any variable.) 
VQ a = Vjca provided x is not free in a. 
UE VxEx 
365 


A NEW INTRODUCTION TO MODAL LOGIC 
The transformation rules are MP, N, 
UG 
|- a -* |- VJCCX, and 
UGLV" 
|-a, D L(a2 D... D L(an D I/?)...) -* |- a, D L(a2 D... 
D L(an D LVJCJS)...), where JC is not free in a,, ... ,an. 
In the semantics for LPCE + S the inclusion requirement is not assumed. 
LPCE + S is contained in LPC + S. Without an existence predicate such 
systems may be axiomatized (as LPCK + S, p. 305) with S', VD, VQ, 
N and MP as before, but VIE is replaced by 
VlK Where JC, y and z are any individual variables, and a is any wff then 
VyVz(Vxa D ot\ylx\) is an axiom of LPCK + S. 
(UGLV is not part of this basis.) The converse of BF is not in general a 
theorem of any LPCE + S or LPCK + S. 
For identity add to S + BF the axiom II JC = x and the axiom schema 
12 JC = y D (a D 0) (p. 312) to obtain S + I. For S + LN1 add LNI 
X7*yDLx7*y(p. 
314). II and 12 can also be added to systems 
without BF. For contingent identity weaken 12 to 12" JC = y D (^...jcn 
= <j>y\...yn) (p. 334). In such systems the variables range over 
'intensional objects', functions from W to D. Where they range over all 
such objects the logic is in most cases unaxiomatizable. 
366 


AXIOMS, RULES AND SYSTEMS 
Table I: Normal Modal Systems 
The following diagram provides a map of most of the normal systems we 
have discussed. An arrow indicates (proper) containment in the sense that 
the system above the arrow contains all the theorems of the system below, 
but not vice versa. The inconsistent system is denoted by i£. Systems to 
the left of the line — contain D and systems to the right of the line 
— • — • — are eot tontained di Trivv .ystems setweee nhese eines sre 
contained in both Triv and Ver. 
Triv 
K4' 
(S4.4M) 
££ 
Ver 
Q^ 
S4.9 
K3.1 
KM 
Kl.l 
K3 
K2.1 
K2 
^S4M 
(Kl) 
KM 
S4.4 
S4.3.1 
S4.3 
S4.2.1 
S4.2 
S4.1 
S4< 
Mk 
S4n 
T 
D 
B+ 
BSeg 
B 
KD4 
KDE 
KBE 
KE 
K4.3Z 
K4.2Z 
K4Z 
K4 
KB 
K 
K4.3W 
K4.2W 
KW 
KH 
MV 
VB 
367 


A NEW INTRODUCTION TO MODAL LOGIC 
Table II: Non-normal Modal Systems 
The non-normal systems referred to in this appendix may be listed in the 
following chart. We have also included SI, Sl°, S0.5 and S0.50 which are 
mentioned on pp. 198, 199 and 207. Systems to the left of the line — 
contain N. Systems with a numerical index 6 or above would become 
inconsistent if N were added. 
S5 
S4 
T 
S9 
S8 
S3.5 
S7 
S3 
K4 
S6, 
S7° 
S30-
kS6° 
S2 
E3' 
S1 
K 
S0.5 
S2° 
kSl° 
S0.50 
E+ 
E7 
E3° 
E7 
E7° 
E6, 
E2° 
E6° 
368 


SOLUTIONS TO SELECTED 
EXERCISES 
Some solutions (mostly in Part I) are given in full, some are merely 
sketched or hinted at, and some are not given at all. 
Exercises — 1 (p. 21) 
1.1 
(c) 
It is sufficient to show that the implication is valid in both 
directions. If A's hand is raised for L(p A q) but not for Lp A Lq then 
it must be kept down for Lp or for Lq. So A must be able to see a player 
B whose hand is kept down for p or for q. So B's hand is kept down for 
p A q, contradicting the fact that A can see B and A's hand is raised for 
L(p A q). If A's hand is raised for Lp and Lq but not for L(p A q) then 
A must be able to see a player B whose hand is down for p A q. But if 
A can see B and A's hand is raised for Lp and for Lq then B's hand must 
be raised for p and for q, and so for p A q 
1.2 
Suppose A cannot see A. Let p be on every player's sheet except 
A's. Show that A's hand is kept down for Lp D p. 
1.3 
(c) 
There are two players, A and B. Each can see both, p is on 
B's sheet but not on A's. q is on neither sheet. 
(d) 
A can see B, B can see C, but A cannot see C. p is on A's sheet 
and on B's but not on C's. 
1.4 
(b) 
Suppose A can see B and C. Let/? be on B's sheet but not on 
C's. 
Exercises — 2 (p. 48) 
2.1 (a) 
PC, DR1,K2 
(b) 
K[~q/p,~p/q], 
Transp, Eq, Def M 
(d) 
DR3, K8, K7, Eq 
369 


A NEW INTRODUCTION TO MODAL LOGIC 
(f) 
PROOF 
K 
(1) 
(1) X PC 
(2) 
(2) X K3 x Eq 
(3) 
PC 
(4) 
(4) x DRl 
(5) 
(b)[q D r/p,p A r/q] 
(6) 
(3X5X6) X PC 
(7) 
(e) 
DR3, K7 
L(pD q)D (Lp D Lq) 
(Lip D q) A Lp) D (Lp A Lq) 
(Lip D q) A Lp) D Lip A q) 
ip A q)D ((qD r) D (p A r)) 
Lip A q)D L((q D r) D ip A r» 
L((qDr) D ipAr)) D (M(qDr) D M(pAr)) 
(Lp A M(qDr)) D (L(pDq) D MipAr)) 
Q.E.D. 
The PC principle used in getting from (1) to (2) is ip D (q D r)) D 
(ip A q) D (q A r))[Lip D q)lp,Lplq,Lqlr\ and in getting from (3), (5) 
and (6) to (7) is (ip A q) D r) D ((r D s) D ((s D (t D v)) D 
(ip A t) D (qD v)))) [Lip D q)lp ,Lp\q, Lip A q)lr, L((q D r) D 
ip A r))/s,M(q D r)/t, Mip A r)lv\. Three applications of MP are then 
required. The PC steps could have been done in several stages. For 
instance, (3), (5) and (6) could have been combined by Syll to get 
(L(p D q) A Lp) D (M(p D q) D Mip A r)). Imp would give 
(L(p D q) A Lp A Mip D q)) D Mip A r), and Exp would give 
(Lp A M(q D r)) D (Lip D q) D Mip A r)). 
2.3 It is sufficient to derive the basis of each system in the other. The 
basis of T* is contained in K except for K* and R*. K* is obtained in 
T from K by N, and R* is DRl. To obtain the basis of T in T* it is 
sufficient to prove K and N. 
Proof of Kin T*: 
J[Lip D q)D (Lp D Lq)/p] 
(1) 
L(L(p D q)D (Lp D Lq)) D 
(L(p D q)D (Lp D Lq)) 
(1)K* X MP 
(2) Lip D q) D (Lp D Lq) 
Q.E.D. 
Proof of N: 
Given 
(1) 
a 
(1) X PC 
(2) 
(L(p D q) D (Lp D Lq)) D a 
(2) X R* 
(3) 
L(L(p D q) D (Lp D Lq)) D La 
370 


SOLUTIONS TO SELECTED EXERCISES 
(3) K* X MP (4) 
La 
Q.E.D. 
2.6 
(a) 
N, K9 
(b) 
Where a and (3 are each p D p this rule allows the derivation of 
M(p D p), and therefore of D. But D was shown on p. 45 not to be a 
theorem of K. 
2.7 
(a) 
PC, N, Dl, K6 
(b) 
Prove M(M~p 
V Mp) and use LMI. 
2.8 A falsifying model may be constructed as follows. W has two 
worlds w, and w2. Each can see the other but neither can see itself. If p 
is true at wl and false at vv2 then M(p D Lp) is false at wx. 
2.9 Show that if a is not D-valid then neither is Ma. If V(a,w) = 0 in 
some D-model define a new model exactly like the old one except that 
it has an extra world w* which can see w and w alone. Show that this is 
a D-model in which V(Ma,w*) = 0. 
2.11 See Williamson 1988 
Exercises — 3 (p. 68) 
3.1 (a) 
PROOF 
K 
(1) L(pD q)D (Lp D Lq) 
(1) X N 
(2) L(L(p D q) D (Lp D Lq)) 
(l)[L(pDq)/p,Lp 
D Lqfq] 
(3) 
L(L(p D q)D (Lp D Lq)) 
D (LL(p D q) D L(Lp D Lq)) 
(2)(3) X MP 
(4) 
LL(p D q) D L(Lp D Lq) 
4 
(5) 
Lp D LLp 
(5)[pDp/p] 
(6) 
L(p D q) D LL(p D q) 
(6)(4) X MP 
(7) 
L(p D q) D L(Lp D Lq) 
Q.E.D. 
[The PC principle used in getting from (6) and (4) to (7) is (p D q) D 
((q D r)D (p D r))withL(p D q)lp,LL(p D q)/q,andL(Lp D Lq)/r.] 
(b) 
PC9, PC10, DR1, 4. 
371 


A NEW INTRODUCTION TO MODAL LOGIC 
(c) 
PROOF 
T2[Mp/p] 
(1) 
M(Mp 2 ) LMp) 
S4(2)[Mp/p] 
(2) 
LMp = LLMp 
(1)(2) X Eq 
(3) 
M(Mp Z ) LLMp) 
(3) Def D X LMI (4) 
M(L~p V LLMp) 
K4[~p/p LMp/q] 
(5) 
(L~p V LLMp) D L(~p V LMp) 
(5) X DR3 
(6) 
M(L~p V LLMp) D ML( -pMLMp) 
(4)(6) X MP 
(7) 
ML(~p V LMp) 
(7) Def D 
(8) 
ML(p D LMp) 
Q.E.D. 
(d) 
S4(l) \p D q/pl K7 ,Eq. 
3.2 
Show that it holds for the case where A is just L or M. Then show 
that if it holds for A it holds for LA and for MA. Explain why this gives 
the result. 
3.3 Let K* denote the wff: L(p D q) D L(Lp D Lq) and call T with 
K* in place of K, S4*. It will be sufficient to prove K and the S4 axiom 
4 (Lp D LLp) in S4*, and to prove K* in S4. The proof of K* in S4 is 
exercise 3.1(a). 
Proof of K in S4*: 
K* 
(1) L(p D q) D L(Lp D Lq) 
T 
(2) Lp D p 
(2)[LpDLq/p] 
(3) L(Lp D Lq) D (Lp D Lq) 
(1)(3) X PC 
(4) 
Lip D q) D (Lp D Lq) 
Q.E.D. 
[The PC principle used in getting from (2) and (4) to (5) is ip D q) D 
((q D r) D (p D r))withL(p D q)/p,L(Lp D Lq)/qand(Lp 
D Lq)/r.] 
Proof of 4 in S4*: 
PC 
(1) p D ((pDp) 
Dp) 
(1) X DR1 
(2) 
Lp D L((pDp) D p) 
K*\pDplpyplq\ 
(3) 
L(ipDp) D p) D L(L(pDp) D Lp) 
(2)(3) X PC 
(5) 
Lp D L(L(pDp) D Lp) 
K[L(pDp)/p,Lp/q] 
(6) 
L(L(pDp) D Lp) D (LL(pDp) D LLp) 
(3)(6) X PC 
(7) 
LLipDp) D (Lp D LLp) 
372 


SOLUTIONS TO SELECTED EXERCISES 
PC 
(8) 
pDp 
(8) X N twice 
(9) 
LL(pDp) 
(7)(9) X MP 
(10) Lp D LLp 
Q.E.D. 
[The PC principle used in getting from (3) and (4) to (5) is (p D q) D 
((q D r) D (p D r)) with Lplp, L((p Dp) D p)lq and L((p Dp) D Lplr. 
The PC principle used in getting from (5) and (7) to (8) is (p D q) D 
((q D (rD s)) D (r D (p D s))) with Lp/p, L(L(pDp) D Lp)/q, 
LL(pDp)/r and LLpls. The PC wff used at (9) is pDp.] 
3.4 To show that Lp is stronger than LMLp use a two world frame 
where the first world can see both worlds but the second world can see 
only itself. Put p true at the second and false at the first. To show that 
MLMp is stronger than Mp put p true at the first and false at the second. 
For the remainder it is sufficient to show that neither MLp nor LMp imply 
each other, since then neither could imply LMLp or be implied by MLMp. 
To show that MLp does not imply LMp use a three world frame in which 
the first world can see all worlds but each of the other two can only see 
itself. Put p true at one of these and false at the other. To show that LMp 
does not imply MLp use a two-world frame in which both worlds can see 
both worlds and put p true in one but not in the other. 
3.5 It is sufficient to show that Lap D Ln+lp is not a theorem of T. For 
suppose n 5* m. If n < m then repeated applications of T (or of PC for 
the case m = n + 1) give |-p Lmp D Ln+lp, and so if K Lnp = Lmp 
then 
f-r Lnp D Ln+lp. 
If m 
< 
n the same argument yields 
h- Lmp D Lm+lp. To prove that Lnp D Ln+lp is never a theorem of T 
choose a frame with n + 2 worlds, w,, ... ,wn+2, and for 1 < i < j < 
n + 2, let W;RvVj. Put p true at every world but wn+2, and show that 
Ln D Ln+lp is false at w,. Then use the soundness of T. 
3.7 
(a) 
Prove L(Lp D Lq) = (Lp D Lq) from S5(5) and then use 
ipD q) V (qD p). 
(b) 
First prove L(Mp D Lq) D Lip D Lq) (Tl, DR1, PC) and then 
prove L(Mp D q) D L(Mp D Lq) (S5(4) Def D). For the converse 
implication prove Lip D Lq) D L(Mp D Lq). 
373 


A NEW INTRODUCTION TO MODAL LOGIC 
3.10 
S5(4)[Mp/p,~p/q] 
(1) 
L(Mp V L~p) 
PC 
(2) 
~p\l 
p 
(2)[L~p/p]DQfM 
(3) 
Up V L~p 
(3) x N 
(4) 
L(Mp V L~p) 
(1)(4) X MP 
(5) 
LMp V L~p 
(5) X PC 
(6) 
~L~p 
D LMp 
(6)DefM 
(7) 
Mp D LMp 
D (LMp V L~p) 
Q.E.D. 
So E can be derived from S5(4) using only principles in T. Thus S5(4) 
added to T gives S5. 
3.12 (b) 
B 
(1) p D LMp 
i\)[~plp\ 
(2) 
~pDLM~p 
(2) X LMI 
(3) 
~p D ~MLp 
(1)(3) X PC 
(4) 
MLp D LMp 
Q.E.D. 
The PC principle used in getting from (1) and (3) to (4) is (pDq) 
D((~pD 
~r) D(rDq)) with LMplq and MLplr. 
3.14 LetabeM(p D p) 
3.15 It is sufficient to show that the addition to T of 
(*) 
(Lp D Lq) DL(pD 
q) 
would cause the resulting system to collapse into PC. 
PC 
(1) 
(pD 
~p)D 
~p 
(1) X DR1 
(2) Lip D ~p) D L~p 
(*){~plq\ 
(3) 
(Lp D L~p) D L(p D ~p) 
(2)(3) X Syll 
(4) 
{Lp D L~p) D L~p 
PC 
(5) 
((pDq)Dq)D 
(~q D p) 
(5)[Lp/p,L~plq] 
(6) 
(4) D (7) 
(4)(6) x MP 
(7) 
—L~ p D Lp 
(l)DefM 
(8) 
Mp D Lp 
(8) Tl x Syll 
(9) p D Lp 
Q.E.D. 
3.10 It is sufficient to prove/? D Lp. 
374 


SOLUTIONS TO SELECTED EXERCISES 
Given 
(1) LMp D MLp 
S5(l) 
(2) 
MLp D Lp 
(1)(2) X Syll 
(3) LMp D Lp 
E 
(4) 
Mp D LMp 
Tl 
(5) p D Mp 
(3)(4)(5) X Syll 
(6) p D Lp 
Exercises — 4 (p. 92) 
4.1 (a) 
K-valid. 
(b) 
Invalid in K, D-valid. 
(c) 
K-valid. 
(d) 
Invalid in K, D-valid. 
(e) 
K-valid. 
(f) 
Invalid in D, T-valid. 
(h) 
Invalid in D, valid in T. 
(i) 
Invalid in T 
Q.E.D. 
4.3 (b) 
See p. 129. Since the diagram ends without contradiction the 
wff is not T-valid. 
A falsifying model is: W = 
{wl9w2,w3}, 
w,Rw,,w1Rw2, w2Rw2,w2Rw3, w>3Ru>3 
V<p,w,) = 1* Vfer,w,) = 1* 
V(p,w2) = 1 
V(g,wJ = 0 
V(p,w3) = 0 
V(q,w3) = 1 
* optional values 
4.4(a) 
w, 
MLp D LMp 
1 
0 0 
* 
* 
• 
\ k 
* 
* 
Lp 
^ 2 
Mp 
11 
00 
w3 
Wff is not S4-valid. Falsifying S4-model is: W = {w1,w2,w3}, w{Rwi, 
WjRw2, w2Rw2, W!Rw3, W3RW3. VipyWi) = 1 (optional), V(p,w2) = 1, 
V(p,w3) = 0 
375 


A NEW INTRODUCTION TO MODAL LOGIC 
(b) 
Consider the diagram in (a) and suppose that we were to add a 
world w>4 which could be seen by both w2 and w3. Then the truth of Lp 
in H>2 would require that p = 1 in w4 and the falsity of Mp in w3 would 
require that/? = 0 in w4, which is contradictory. [This also shows that the 
wff is S5-valid since all S5-models satisfy this condition, though not all 
models satisfying the condition are S5-models.] 
Exercises — 5 (p. 110) 
5.1 
(a) Lip V q) A {Lip V r) V Ls) 
Invalid. 
(b) 
{Lp V L~{pA 
q) V Mq) A L~{p 
A q) V M ( ~ g V q)) Valid. 
(c) 
(L(~/> V q) V L(~/> V ~tf) V Mip A #)) A 
(L(~/> V q) V L{~p 
V ~#) V M(/? A - # ) ) 
Valid. 
(d) 
{Lr V M(p V q) V M ~ ( p V #)) A 
( ~ r V L(/> D p) V M(p V g)) 
Valid. 
(e) 
( L ~ p V Lp V M{q V (p A - # ) ) A 
( L ~ p V Lp V L~p 
V Lp V M{p A ~#) 
Invalid. 
(f) 
( ~ # V L{p D r) V M/?) A ( ~ # V L{p D r) V M~{q 
D r)) 
Invalid. 
(h) 
( L ~ p V Lp V L/? V M~/?) A (Lp V M ( ~ p V -/>)), 
Valid. 
(i) 
(L(L(/> D <?) D q) D p) D M{Lq D p) 
~{~L{~L{pDq) 
V q) V p) V M(~L# V /?) 
[Def D] 
{L{~L{p 
D q) V q) A ~p) 
V M(~Ltf V p) 
[De M] 
{L{M~{p 
D q) V q) A ~p) 
V M{M~q 
V /?) 
[LMI] 
{{M~{p 
D q) V Z^)A ~p) V ( M ~ # V M/?) 
[L(M/> V ^) = (M/? V Lq), M{Mp V <?) = (Mp V M#)] 
(M~(p D q) V Lq V M~q 
V M/>) 
A ( ~ p V M~q 
V M/?) 
[Distrib] 
Wff now in MCNF. To test for S5-validity first obtain an ordered 
MCNF. We use the principle Mip V q) = {Mp V Mq) and PC re-
ordering principles to obtain 
{Lq V M{~{p 
D q) V ~q 
V /?)) A {~p 
V M ( ~ # V /?)). 
The wff will be valid iff each conjunct is. The first conjunct is valid 
because q V ~ {p D q) V ~q V pis PC-valid; and the second conjunct 
is valid because ~p V ~q V p is PC-valid. 
(j) 
L(L(L/> D L<?) DLipD 
q)) 
L{~L{~Lp 
V L#) V Lip D q)) 
[Def D] 
376 


SOLUTIONS TO SELECTED EXERCISES 
L(M~(~Lp 
V Lq) V Lip D q)) 
[LMI] 
L(M(LpA -Lq) 
V Lip D q)) 
[DeM] 
L(M(LpAM~q) 
V L{p D q)) 
[LMI] 
M(LpAM~q) 
V Lip D q) 
[L(Mp V Lq) = (M/> V Lq)] 
(LpAM~q) 
V Lip D q) 
[M(LpAMq) s 
(LpAMq)] 
(Lp V Lip D q))AiM~q 
V Lip D q)) 
[Distrib] 
(L/? V Lip D q))AiLip Dq) V M~#) 
[Com] 
Wff now in (ordered) MCNF. The original wff will be S5-valid iff the 
MCNF is, and the MCNF will be valid iff each conjunct is. Consider the 
first conjunct. This will be S5-valid iff either p or p D q is PC-valid. But 
neither is, so the conjunct is not S5-valid, and so the whole wff is not 
either. The following PC assignments may be used. 
V,(p) = 0 
V,(g) = 1 (optional) 
V2(p) = 1 
V2(<?) = 0 
Define an S5-model on this basis by letting W = {w^Wj}. 
V<p,w,) = V,(W = 0, W(q,w{) = VM 
= 1 
V(p,w2) = V2(p) = 1, V(q,w2) = V2(q) = 0 
Since V(p,Wj) = 0 then V(Lp,Wj) = 0 and since V(p,w2) = 1 and 
V(tf,w2) = 0, then VipDq,w2) 
= 0, and so V(L(pD^,w2) = 0. So 
V(LpVL(pDq),Wi) 
= 0, showing that the conjunct, and therefore the 
whole wff is not S5 valid. 
5.2 
Consider two models, each with the same set of three worlds, w,, 
vv2, w3. w, can see both w2 and vv3, and all worlds can see themselves. In 
the first model w2 can see w3, but in the second model it cannot. In both 
models p is true only at w2. Thus: 
(WLRLV,) 
<W2,R2>V2> 
wx 
p = 0 
wx 
p = 0 
• 
\ 
/ 
\ 
vv2 
-> 
vv3 
w>2 
w 3 
p = 1 
/? = 0 
P = 1 
/> = 0 
Let every other variable be true in all worlds in both models. Both models 
are S4 models so if Mip A M~p) is equivalent in S4 to a first-degree 
wff a, thenV,(M(p A M~/?),w,) = V,(a,w,) and V2(M(p A M~p),wx) 
= V2(a,w,). Now if a is of first degree then V^c^w,) = V2(a,w>j). (The 
377 


A NEW INTRODUCTION TO MODAL LOGIC 
proof relies on the fact that if /? is any wff of degree 0 then Vi(jG,w) = 
V2(j8,w) 
for 
every 
w 
E 
W.) 
So 
V,(M(p A M~p),w, 
= 
V2(M(p 
A M~p). 
But 
Vj(M(/? A M - / ? ) , ^ ) 
= 
1 
and 
V2(M(p AM~p),Wj) = 0. So M(p A M~p) is not equivalent in S4 to 
any first degree formula. 
Exercises — 6 (p. 122) 
6.1 First suppose that T is maximal consistent and suppose that T U {a} 
is consistent. Now if a & T then, by maximal consistency — a E T. But 
in that case T U {a} is not consistent. So if T U {a} is consistent then 
a E T, and this is enough to make T maximal consistent*. Now suppose 
that T is maximal consistent* and suppose that there is some wff a such 
that neither a nor — a is in T. Then both V U {a} and T U { — a} are 
inconsistent. But then T would be inconsistent by the argument on p. 115. 
6.2 
Suppose a D j8 E T. Then, if we don't have either a £ T or /? E 
T, we have a E T and fi £ T. But since T is maximal consistent, we 
have a E T and ~ 0 E T. But {a, —/?, a D 0} is inconsistent. For the 
converse, suppose ~ a E T. Then since | 
a D (a D /?), a D (3 E 
T by lemma 6.2b on p. 114. And suppose /? E T. Then, since \- @ D 
(a D (3), a D 0 E T, also by lemma 6.2b. 
6.3 
Suppose A Q T but A ^ T. Then there exists a E T but a £ A. 
Since A is maximal then by lemma 6.1a on p. 114 — a E A and so ~ a 
E T. But then T would be inconsistent. 
6.4 
Suppose {Ma: a E A} £ T. Then there exists a E A with Ma £ 
T. But T is maximal, so - M a E T, and so L ~ a E T. And A is 
consistent so — a £ A, and so {a: La E T} $ A. Suppose {a: La E T} 
£ A. Then there exists La E T with a £ A. So —a E A. But T is 
consistent and La E T so —La £ T so M —a £ T, so {Ma: a E A} 
«r. 
6.7 
Suppose {Ly,, ... ,Lyn} is not consistent. Then (as in the proof of 
lemma 6.4 on p. 117) 
h ( L 7 , A... A LTn) D 0 
so 
h ( ^ T i A... A LLyQ) D L(3. 
Since S contains S4 then \-Lyx D LLy,, ..., \-Lyn D LLyn and so 
htf/y, A... A L7n) DL0. 
378 


SOLUTIONS TO SELECTED EXERCISES 
So {Lylf ... yLyn>~L@} is not S-consistent. 
6.8 
Suppose wx can see two distinct worlds, w2 and w3. Since w2 9* vv3 
there is some a G w2 with ~ a G vv3. So Ma G Wj. So by Mp D Lp, 
Lot G wlt and so a G w3 contradicting w3's consistency. 
6.9 For completeness it is sufficient to show that where (W,R,V) is the 
canonical model of W2 then R satisfies the condition. Suppose there is 
some w , G W such that wlRw2y w1Rw3 and w, j* w2, wx ^ w3 and w2 5* 
vv3. Since w2 5* w3 there is some a G w2 such that ~ a € w3. Since w, 
5* vv2 there is some 0 G w, with ~|8 G n>2. Since w, 5* vv3 there is 
some 7 G w, with —7 G w3. So 
(a) 
7 G w„ 0 G w, 
(b) 
a G vv2, ~/J G w2 
(c) 
- a G w3, - 7 G w3. 
From (b) ((a V 7) A —/?) G vv2, and since W>IRH>2, M((a V 7) A ~0) 
G vvt. From (a) a V 7 G w, and so 
(d) 
((a V 7) A (3 A M((a V 7) A ~0)) G w,. 
So by W2 L(a V 7) G w,. But w1Rw3 and so a V (3 G w3. But then 
{a V 7, ~ a , —7} Q vv3, which contradicts its consistency. 
6.11 If w is not a dead end and can see a world besides itself then there 
is a world w' with w 5^ w' and wRw'. So there is some a G w with ~ a 
G w'. But La G w> and so a G w', which contradicts its consistency. 
Exercises — 7 (p. 141) 
7.1(b) See p. 284 (S4.4 + BF) 
7.2 For completeness establish the consistency in Mk of 
(A) L-(w) U {~L0 : ~ 0 G w} U {LL7 : Ly G w) 
for any w G W, and explain why this is sufficient. 
7.6 First note that the canonical model of any normal extension of KB 
will be symmetrical, and that in a cohesive symmetrical frame, for any 
H>, w' G W, there is some n > 0 such that wRV. Consider the set A = 
{Ln/?:n>0}. A is clearly consistent for if not then 
h ~(P A Lp A ... A Lkp) 
for some k. But with p D pip we then obtain 
h ~((p D p) A L(pD p) A ... A Lk(p D p)) 
379 


A NEW INTRODUCTION TO MODAL LOGIC 
making S inconsistent. So let w* be a world in the canonical model at 
which all members of A are true. If the frame of this model is cohesive 
then any w G W will be such that for some n, w*Rnw and so V(p,w) = 
1. So p will be valid in S's canonical model, and so \-sp, making S 
inconsistent. 
7.8 For (ii), given any non-theorem a, let w* be a world in the 
canonical model of the system in which a is false. Let (W*,R*,V*) be 
that part of the canonical model generated (see p. 143) by w* (i.e. its 
worlds are those to which there is an R-chain from w*) and let R* be 5*. 
Let V*(p,w) = V(/?,w) for w G W*. Use the fact that R satisfies (i) to 
shew that V*(a,n>*) = V(a,w*) = 0 and that (W*,R*, V*) is a model for 
the system. 
7.8 Show that if S provides RD then {—La : -| s a} is S-consistent. 
Explain why this gives the result. 
7.9 
Suppose none of a,, 
... 
,an is a theorem of S. Then 
{~La,,...~Lan} Q {~L(3 : H s /?}. So if {~L(3 : -\ s /?} is consistent 
so is {—Lojj,... —Lan}, and so-| sLa, V ... V Lan. We proved on p. 139 
that { ~LjS : -| 
s} is consistent where S is T or K, and on p. 140 where 
S is KW. The case of S4 is similar. 
7.10 Use the fact that LM~p 
V Lp, LM~p V LMp and LM~p 
V Lp 
are theorems of, respectively, B, S4.2 and S5. 
7.11 Prove that Kl.l provides the rule of disjunction in the following 
form: where a{> ... ,an are any wff and ft is a wff of PC then if |- Lax 
V... V Lan V /J then either |- a} for some 1 < i < n or \- (3. Then 
shew that the canonical model of K.l. can see a pair of distinct worlds 
that can see each other, but that no frame for Kl.l contains such a pair. 
Exercises — 8 (p. 156) 
8.2 
Base the mini-canonical model on the set <£^+ of all wff of modal 
degree no more than one greater than the degree of a which are made up 
from the variables of a. Let wRw' iff for all L(3 G w, L@ G w' and 
prove the analogue of theorem 8.4 for all 7 G <i>a. Then shew how to 
adapt the completeness proofs given for these systems in Chapter 7. 
380 


SOLUTIONS TO SELECTED EXERCISES 
8.3 
Show that the completeness proof for KW still holds when $+ is 
replaced by $™+, and shew that Lem0 imposes linearity. Then shew that 
any finite irreflexive transitive linear frame can be mapped onto an initial 
segment of the natural numbers with R as >. 
8.4 
Base the mini-canonical model on the set of all wff of modal degree 
no more than two greater than the degree of a which are made up from 
the variables of a. Let wRw' iff either w = w' or else 
(i) IfLjS e wthenL/J E w' 
(ii) There is some Ly € w' such that Ly (£ w. 
8.5 
Show that each generated sub-frame of the finite canonical model 
based on $™+ consistes of a finite sequence of clusters. Arbitrarily order 
the members of each cluster and let (n,m) denote the n'th world in the 
m'th cluster. Show that R, as defined in the exercise, is equivalent to R 
in the original finite model. 
Exercises — 9 (p. 169) 
9.2 
(This solution is amplified in Chapter 4 of Hughes and Cresswell 
1984.) For (A) first shew that a frame is a frame for MV iff every world 
either is or can see a dead end. Then suppose a frame in which this is not 
so and let w>* be a world which is not a dead end and cannot see one. Let 
v* be a world that w* can see. Put p false everywhere and q false at v* 
but true everywhere else. Show that this falsifies VB. For (B) use a frame 
in which W is all the finite natural numbers together with the two infinite 
numbers co and co + 1. o> + 1 can see co and co alone, co and all the 
natural numbers can see numbers less than themselves. Every variable is 
false everywhere. This falsifies MV but validates every instance of VB. 
(Use the fact that | a | for any wff a is finite without co or cofinite with 
CO.) 
9.3 Derive VB from the two axioms given. Then use exercise 9.2 to 
establish (A). For (B) shew that the frame used in 9.2 validates (i) and 
(ii). 
Exercises — 10 (p. 189) 
10.2 Suppose w,Rw2, w2Rw3 but not WjRwg. Put/? false at wx and n>3 but 
true everwhere else. 
In Part III exercises marked with * are ones for which we have not 
381 


A NEW INTRODUCTION TO MODAL LOGIC 
ourselves obtained a solution. Where solutions are known to us to have 
been obtained by others we have indicated this. Some of the remaining 
starred exercises may be regarded as open research problems. The few 
solutions which follow are mostly proofs of wff in systems of modal LPC 
in an abbreviated form. The full proofs will need to be reconstructed from 
these. 
Exercises — 13 (p. 254) 
13.1 (a) Use (2) in the form VxL((a D a) D a) D L(VJC(« D a) D 
Vjca). 
13.2 (ii) 
ly(<j>y D VJC0JC) 
(<j>y D Vx<]>x) D LM((j>y D Vx<px) 
ly(<j>y D Vx<}>x) D 3yLM((j>y D Vx<l>x) 
3yLM(<j>y D Vx<j>x) 
13.3 Proof of ~(C) in S4.4 + BF 
Choose y to be a variable distinct from x. 
VxVy((<j>x D <j>y) D (ML(<j>x D <j>y) D L(<f>x D <j>y))) 
~3xly((<f>x D <j>y) A ~L(<f>x D <f>y) A ML(<f>x D <j>y)) 
~3xly(~<l>x 
A M(<j>x A ~<£y) A ML<j>y) 
~3JC(~<£JC A 3yM(<j>x A ~<j>y) A VyML<j>y) 
~ 3 * ~ < £ J C A Vjc3yM(0Jc A ~<j>y) A VyML<j>y 
~lx~<t>x 
A VxMly(<j>x A ~<j>y) A VyML<j>y 
~lx~<j>x 
A VxM(<j>x A 3JC~<£JC) A VxML<f>x 
~lx~<t>x 
A Vx(M<j>x A Llx~<f>x) 
A VxML<j>x 
~L(yxML<f>x 
A 3*~</>JC) 
13.5 (b) and (c): 
Show that the wff fail in the following models 
(W,R,V), (W,R,V> where W = {w„w2}, R is universal and D = 
{w„w2}: 
(b) 
V(«) = {{uuwx),{u2,w2))y V(« = { M ) , ( « i ^ } 
(c) 
V«>) = {(ii1>Wl)} 
Exercises — 14 (p. 272) 
14.5(b) Montagna 1984 proves that for systems without BF the wff 
3xM<f>x A Vx3yL(<j>x D M<j>y) is unsatisfiable on all KW frames but is 
consistent in (i.e. its negation is not a theorem of) LPC + KW. He leaves 
it as an open question whether the result still holds in KW + BF. 
[Rl X UG] 
[X BF] 
382 


SOLUTIONS TO SELECTED EXERCISES 
Exercises — 17 (p. 328) 
17.3 The first of the two meanings may be expressed by the 
wff: M3x(<f>x A Vy(<l>y D x = y) A ~ <j>x). This wff says that it might 
have been that there be exactly one thing which is a mayor of Wellington 
and not a mayor of Wellington. This meaning is contradictory. The 
second meaning may be expressed by 3*((</>JC A Vv(<£y D x = v)) A 
M~<l>x). This wff says that there is exactly one thing which is a mayor 
of Wellington and, concerning that thing, it is possible that it might not 
have been a mayor of Wellington. This wff is not contradictory. 
17.5 3lxa D (yx~La 
D ~La[ixa/x\) 
[Vli, where (3 is -La] 
3lxa D (La[ixa/x] D IxLa) 
L3lxa D (La[ixa/x] D IxLa) 
[ X T] 
Lllxa D La[ixa/x] 
[DD X DR1] 
Lllxa D IxLct 
Exercises — 18 (p. 347) 
18.1 Take I to be the set of constant functions (i.e. for i € I there is 
some u E D such that i(w) = u for all w € W) and then use the fact that 
L^x<l>x D 3xL<J>x fails in ordinary modal LPC. 
18.2 Where fi(x) = i, choose /*(y) to be a function such that /i(y)(w) = 
i(w) but jn(y)(w') 5* i(w') for all w 5* w'. Show that this choice of fi(y) 
satisfies the formula provided there are at least two individuals. (Explain 
why the formula is also true if there is only one individual.) 
383 


BIBLIOGRAPHY 
Each item is followed by a list of numbers of the notes in which it is referred to. 
Thus (4.3) indicates note 3 to Chapter 4 and so on. 
Alban, M.J., 1943, 'Independence of the primitive symbols of Lewis' calculi of 
propositions', The Journal of Symbolic Logic, 8, 24-6 (11.24). 
Anderson, A.R., 1954, 'Improved decision procedures for Lewis's calculus S4 
and Von Wright's calculus M', The Journal of Symbolic Logic, 19, 201-14 
(Correction in ibid 20, 150) (4.1). 
Aqvist, L., 1964, 'Results concerning some modal systems that contain S2', The 
Journal of Symbolic Logic, 29, 79-87 (11.27). 
1973, 'Modal logic with subjunctive conditionals and dispositional predicates', 
Journal of Philosophical Logic, 2, 1-76 (12.16, 19.1). 
Aristotle, BC350, Prior Analytics (tr. R.Smith, Indianapolis, Hackett Publishing 
Co, 1989) (11.1). 
Barcan, (Marcus) R.C., 1946, 'A functional calculus of first order based on strict 
implication', The Journal of Symbolic Logic, 11, 1-16(1.2, 14.3). 
1947, 'The identity of individuals in a strict functional calculus of second 
order', The Journal of Symbolic Logic, 12, 12-5 (17.1). 
1962, 'Interpreting quantification', Inquiry, 5, 252-9 (15.1). 
Bayart, A., 1958, 'La correction de la logique modale du premier et second ordre 
S5' Logique et Analyse, 1, 28-44 (1.3, 13.2). 
Bayart, A., 1959, 'Quasi-adequation de la logique modale de second ordre S5 et 
adequation de la logique modale de premier ordre S5', Logique et Analyse, 
2, 99-121 (6.1, 14.2). 
Becker, O., 1930, 'Zur Logik der Modalitaten', Jahrbuch fiir Philosophie und 
Phanomenologische Forschung, 11, 497-548 (1.3, 3.3, 3.5, 11.10, 11.20, 
12.18). 
Bellissima, F., 1989, 'Infinite sets of non-equivalent modalities', Notre Dame 
Journal of Formal Logic, 30, 574-82 (3.1). 
Bellissima, F., and M. Mirolli, 1983, 'On the axiomatization of finite K-frames', 
Studia Logica, 383-8 (8.3). 
Benthem, J.F.A.K. van, 1975, 'A note on modal formulae and relational 
properties', The Journal of Symbolic Logic, 40, 55-8 (10.12). 
1978, 'Two simple incomplete logics', Jlieoria, 44, 25-37 (8.9, 9.1, 9.6). 
1979a, 'Canonical modal logics and ultrafilter extensions', The Journal of 
384 


BIBLIOGRAPHY 
Symbolic Logic, 44, 1-8 (7.12). 
1979b, 'Syntactic aspects of modal incompleteness theorems', Theoria, 45, 
63-77 (9.1). 
1980, 'Some kinds of modal completeness', Studia Logica, 39, 125-41 (10.6). 
1983, Modal Logic and Classical Logic, Naples, Bibliopolis (10.9). 
1984, 'Correspondence theory', Handbook of Philosophical Logic, ed. D.M. 
Gabbay and F. Guenthner, Dordrecht, Reidel, Vol. II, Ch. 4, 167-247 
(10.9). 
Benthem, J.F.A.K. van, and W.J. Blok, 1978, 'Transitivity follows from 
Dummett's axiom', Theoria, 44, 117f (10.6). 
Bergmann, G., 1949a, 'The finite representations of S5', Methodos, 1, 217-19 
(8.1). 
Blackburn, P, 1993, 'Nominal tense logic', Notre Dame Journal of Formal Logic, 
34, 56-83 (12.9). 
Blok, W.J., 1979, 'An axiomatization of the veiled recession frame', Studia 
Logica, 38, 37-47 (8.9). 
1980, 'The lattice of modal logics: an algebraic investigation', The Journal of 
Symbolic Logic, 44, 221-36 (9.1). 
Bochenski, I.M., 1961, A History of Formal Logic, (Translated and edited by Ivo 
Thomas) Notre Dame, University of Notre Dame Press (11.1). 
Boolos, G., 1979, The Unprovability of Consistency, Cambridge, Cambridge 
University Press (7.13, 8.4). 
1980, 'On systems of modal logic with provability interpretations', Theoria, 46, 
7-18 (9.1). 
Boolos, G., and G. Sambin, 1985, 'An incomplete system of modal logic', 
Journal of Philosophical Logic, 14, 351-8 (9.1). 
1990, 'Provability: the emergence of a mathematical modality', Studia Logica, 
50, 1-23 (7.12). 
Bowen, K.A., 1979, Model Theory of Modal Logic, Dordrecht, Reidel (15.5). 
Broido, J., 1975, 'von Wright's principle of predication - some clarifications', 
Journal of Philosophical Logic, 4, 6-16 (13.6). 
Bull, R.A., 1964, 'A note on the modal calculi S4.2 and S4.3', Zeitschrift fur 
mathematische Logik und Grundlagen der Mathematik, 10, 53-5 (8.1). 
1965a, 'An algebraic study of Diodorean modal systems', The Journal of 
Symbolic Logic, 30, 58-64 (7.4, 10.7). 
1965b, 'A class of extensions of the modal system S4 with the finite model 
property', Zeitschrift fur 
mathematische Logik und Grundlagen der 
Mathematik, 11, 127-32(8.1). 
1966, 'That all normal extensions of S4.3 have the finite model property', 
Zeitschrift fur mathematische Logik und Grundlagen der Mathematik, 12, 
341-4 (8.3). 
1970 'An approach to tense logic', Theoria, 36, 282-300 (12.9). 
Bull, R.A., and K. Segerberg, 1984, 'Basic modal logic', Handbook of 
385 


A NEW INTRODUCTION TO MODAL LOGIC 
Philosophical Logic, ed. D.M. Gabbay and F. Guenthner, Dordrecht, Reidel, 
Vol. II, Ch. 1, 1-88(12.17). 
Burgess, J.P., 1984, 'Basic tense logic', Handbook of Philosophical Logic, ed. 
D.M. Gabbay and F. Guenthner, Dordrecht, Reidel, Vol. II, Ch. 1 89-133 
(12.5). 
Byrd, M., 1978, The extensions of BAltj - revisited', Journal of Philosophical 
Logic, 7, 407-13 (7.10). 
Carnap, R, 1946, 'Modalities and quantification', The Journal of Symbolic Logic, 
11,33-64(1.3,5.1). 
1947, Meaning and necessity, Chicago, University of Chicago Press (13.6). 
Chellas, B.F., 1980, Modal Logic: An Introduction, Cambridge, Cambridge 
University Press (Exercise 2.10, 2.7, 3.4, 3.6, 8.1, 10.10). 
Chellas, B.F., and K. Segerberg, 1994, 'Modal Logics with the Macintosh Rule', 
Journal of Philosophical Logic, 23, 67-86 (3.6). 
Church, A., 1936, 'A note on the Entscheidungsproblem', The Journal of 
Symbolic Logic, 1, 40-1 (correction in ibid 101-2) (14.5). 
1956, Introduction to mathematical logic Vol. 1, Princeton, Princeton University 
Press (1.1, 13.1, 14.5). 
Churchman, C.W., 1938, 'On finite and infinite modal systems', The Journal of 
Symbolic Logic, 3, 77-82 (11.20). 
Corsi, G., 1993, 'Quantified modal logics of positive rational numbers and some 
related systems', Notre Dame Journal of Formal Logic, 34,263-283 (Exercise 
15.3). 
Corsi, G., and S. Ghilardi, 1989, 'Directed frames', Archive for Mathematical 
Logic, 29, 53-67 (15.6). 
1992, 'Semantical aspects of quantified modal logic', Knowledge, Belief and 
Strategic Action, Ed. C. Bicchieri and M.L. Dalla Chiara, Cambridge, 
Cambridge University Press, 167-95 (15.7). 
Cresswell, M.J., 1967a, 'Note on a system of Aqvist', The Journal of Symbolic 
Logic, 32, 58-60 (11.27). 
1967b, 'The interpretation of some Lewis systems of modal logic', Australasian 
Journal of Philosophy, 45, 198-206 (11.23). 
1967c, 'A Henkin completeness theorem for T', Notre Dame Journal of Formal 
Logic, 8 186-90 (14.2). 
1969a, 'A conjunctive normal form for S3.5', The Journal of Symbolic Logic, 
34 253-5 (11.27). 
1969b, 'The elimination of de re modalities', T\\e Journal of Symbolic Logic, 
34 329-30 (13.6). 
1973, Logics and Languages, London, Methuen (17.4). 
1979, 'BSeg has the finite model property', Bulletin of the Section of Logic, 
Polish Academy of Sciences, 8, 154-60 (8.7). 
1982, 'A canonical model for S2', Logique et Analyse, 97, 3 (11.23). 
1983a, 'KM and the finite model property', Notre Dame Journal of Formal 
386 


BIBLIOGRAPHY 
Logic, 24, 323-7 (8.1). 
1983b, The completeness of KW and Kl.l', Logique et Analyse, No 102, 
123-7 (8.2). 
1984, 'An incomplete decidable modal logic', The Journal of Symbolic Logic, 
49, 520-7 (8.10). 
1985, 'We are all children of God', Analytical Philosophy in Comparative 
Perspective (ed. B.K. Matilal and J.L. Shaw), Dordrecht, Redel (10.20). 
1987, 'Magari's theorem via the recession frame', Journal of Philosophical 
Logic, 16, 13-5 (9.1). 
1988, 'Necessity and contingency', Studia Logica, 47, 146-9 (1.2). 
1990, Entities and Indices, Dordrecht, Kluwer (19.2). 
1991, 'In defence of the Barcan Formula', Logique et Analyse, No 135-6, 
271-82 (15.1). 
1995a, 'SI is not so simple', Modality, Morality, and Belief, Cambridge, 
Cambridge University Press, 29-40 (11.28, 12.13). 
1995b, 'Incompleteness and the Barcan Formula', Journal of Philosophical 
Logic 24, 379-403 (14.4, 15.7). 
Cross, C.B., 1993, 'From worlds to probabilities: a probabilistic semantics for 
modal logic', Journal of Philosophical Logic, 22, 169-92 (12.25). 
Crossley, J.N., and I.L. Humberstone, 1977, 'The logic of "Actually"', Reports 
on Mathematical Logic, No 8, 11-29 (19.1). 
Dalen, D. van, 1986, intuitionistic logic', Handbook of Philosophical Logic, ed. 
D.M. Gabbay and F. Guenthner, Dordrecht, Reidel, Vol. Ill, Ch. 4, 225-39 
(12.18). 
Dugundji, J., 1940, 'Note on a property of matrices for Lewis and Langford's 
calculi of propositions', The Journal of Symbolic Logic, 5, 150-1 (8.1). 
Dummett, M.A.E. and E.J. Lemmon, 1959, 'Modal logics between S4 and S5', 
Zeitschrift fur mathematische Logik und Grundlagen der Mathematik, 5, 
250-64 (7.4, 7.9, 10.6, 12.9). 
Dunn, J.M., 1986, 'Relevance logic and entailment', Handbook of Philosophical 
Logic, ed. D.M. Gabbay and F. Guenthner, Dordrecht, Reidel, Vol. Ill, Ch. 
3, 117-224(11.34). 
Emch, A.F., 1936, 'Implication and deducibility', The Journal of Symbolic Logic, 
1, 26-35, and 58 (11.31). 
Feys, R., 1937, 'Les logiques nouvelles des modalites', Revue Neoscholastique 
de Philosophie, 40, 517-53, and 41, 217-52 (2.7). 
1950, 'Les systemes formalises Aristoteliciennes', Revue Philosophique de 
Louvain, 48, 478-509 (1.2, 11.27). 
1965, Modal Logics, Louvain, E. Nauwelaerts (11.11, 11.17, 11.27). 
Fine, K., 1970, 'Prepositional quantifiers in modal logic', Theoria, 36, 336-46 
(18.6, 18.7). 
1971, 'The logics containing S4.3', Zeitschrift fur mathematische Logik und 
Grundlagen der Mathematik, 17, 371-6 (8.3). 
387 


A NEW INTRODUCTION TO MODAL LOGIC 
1972, 'Logics containing S4 without the finite model property', in Hodges, W. 
(ed), Conference in Mathematical Logic - London '70, Berlin, Springer-
Verlag, 98-102 (8.8). 
1974a, 'Logics containing K4, Part I', The Journal of Symbolic Logic, 39, 
31-42 (10.4, 10.8). 
1974b, 'An incomplete logic containing S4', Theoria, 40, 23-9 (9.1). 
1974c, 'An ascending chain of S4 logics', Theoria, 40, 110-6 (9.1). 
1975a, 'Some connections between elementary and modal logic', in Kanger, 
S. (ed), Proceedings of the Third Scandinavian Logic Symposium, 
Amsterdam, North Holland, 15-39 (7.14, 10.14). 
1975b, 'Normal forms in modal logic', Notre Dame Journal of Formal Logic, 
16, 229-37 (8.1). 
1978, 'Model theory for modal logic, Part I, the de re/de dicto distinction', 
Journal of Philosophical Logic, 1, 125-56. (Part II 277-306) (13.714.2, 
16.2, 16.9). 
1983, 'The permutation principle in quantificational logic', Journal of 
Philosophical Logic, Yl, 33-7 (16.9). 
Fitch, F.B., 1952, Sympolic Logic; An Introduction, New York, Ronald Press Co 
(12.3). 
Fitting, M.C., 1983, Proof Methods for Modal and Intuitionistic Logics, 
Dordrect, Reidel, 1983 (12.3, 12.18). 
Forbes, G., 1989, Languages of Possibility, Oxford, Basil Blackwell (19.2). 
Frege, G., 1892, 'Uber Sinn und Bedeutung', Zeitschrift fur Philosophie und 
Philosophische Kritik, 100, 25-50 (English translation: 'On sense and 
reference', Translations from the writings ofGottlob Frege, P.T. Geach and 
M Black, Oxford, Basil Blackwell, 1952) (17.1). 
Gabbay, D.M., 1975, 'A normal logic that is complete for neighbourhood frames 
but not for Kripke frames', Tlieoria, 41, 148-53 (12.17). 
1976, Investigations in Modal and Tense Logics with Applications to Problems 
in Philosophy and Linguistics, Dordrecht, Reidel (8.1, 8.3, 8.10). 
1981, 'An irreflexivity lemma with applications to axiomatizations of 
conditions on tense frames', Aspects of Philosophical Logic, ed. U. 
Monnich, Dordrecht, Reidel, 67-89 (10.2, 10.3). 
Gabbay, D.M., and F. Guenthner, 1984, Handbook of Philosophical Logic, 
Dordrecht, Reidel (four volumes) (12.1). 
Gabbay, D.M., and Ch. Rohrer, 1979, 'Do we really need tenses other than 
future and past?', Semantics From Different Points of View, (ed. R. Bauerle 
et ai), Berlin, Springer, 15-20 (19.1). 
Gallin, D, 1975, Intensional and Higher-Order Modal Logic, Amsterdam, North 
Holland (14.2). 
Gargov, G., and V. Goranko, 1993, 'Modal logic with names', Journal of 
Philosophical Logic, 22, 607-36 (12.9). 
Garson, J.W., 1980, 'The unaxiomatizability of a quantified intensional logic', 
388 


BIBLIOGRAPHY 
Journal of Philosophical Logic, 9, 59-72 (18.6). 
1984, 'Quantification in modal logic', Handbook of Philosophical Logic, ed. 
D.M. Gabbay and F. Guenthner, Dordrecht, Reidel, Vol. II, Ch. 5, 249-307 
(16.2, 16.9, 18.6). 
Gentzen, 
G., 
1934, 
'Untersuchungen 
iiber 
das 
logische 
Schliessen', 
Mathematische Zeitschrift, 39, 176-210, 405-13 (12.3). 
Gerson, M. 1975, 'The inadequacy of the neighbourhood semantics for modal 
logic', The Journal of Symbolic Logic, 40, 141-8 (12.17). 
1975a, 'An extension of S4 complete for the neighbourhood semantics but 
incomplete for the relational semantics', Studia Logica, 34, 333-342 (12.17). 
Ghilardi, G., 1991, 'Incompleteness results in Kripke semantics', The Journal of 
Symbolic Logic, 56, 517-38 (15.7, 15.11). 
Godel, K., 1933, 'Eine Interpretation des intuitionistischen Aussagenkalkiils', 
Ergebnisse eines mathematischen Kolloquims 4, 34-40 (2.7, 11.15, 12.18). 
Goldblatt, R.I., 1973, 'A model-theoretic study of some systems containing S3', 
Zeitschrift fur mathematische Logik und Grundlagen der Mathematik, 19, 
75-82 (11.21). 
1975a, 'First-order definability in modal logic', The Journal of Symbolic Logic, 
40, 35-40 (10.12). 
1975b, 'Solution to a completeness problem of Lemmon and Scott', Notre 
Dame Journal of Formal Logic, 16, 405-8 (10.11). 
1976, 'Metamathematics of modal logic', Reports on Mathematical Logic, 6, 
41-77 (part I); 7, 21-52 (part II) (10.12). 
1987, Logics of Time and Computation, Stanford, CSLI (12.10, 12.11). 
1991, 'The McKinsey axiom is not canonical', Vie Journal of Symbolic Logic, 
56, 554-62 (10.12). 
Goranko, V., 1990, 'Modal definability in enriched languages', Notre Dame 
Journal of Formal Logic, Vol. 31, 81-105 (12.7, 12.8). 
Hallden, S., 1949a, 'Results concerning the decision problem of Lewis's calculi 
S3 and S6', The Journal of Symbolic Logic, 14, 230-6 (11.24). 
1949b, 'A reduction of the primitive symbols of the Lewis calculi', Portugaliae 
Mathematica, 8, 85-8 (1.2). 
Hanson, W.H., 1966, 'On some alleged decision procedures for S4', The Journal 
of Symbolic Logic, 31, 641-3 (4.1). 
Hawthorn, J., 1990, 'Natural deduction in normal modal logic', Notre Dame 
Journal of Formal Logic, 31, 263-73 (12.3). 
Hazen, A., 1976, 'Expressive incompleteness in modal logic', Journal of 
Philosophical Logic, 5, 25-46 (19.1). 
1979, 'Counterpart-theoretic semantics for modal logic', The Journal of 
Philosophy, 76, 319-38 (19.5). 
1990, 'Actuality and quantification', Notre Dame Journal of Formal Logic, 31, 
498-508 (19.1). 
Henkin, L., 1949, 'The completeness of the first-order functional calculus', The 
389 


A NEW INTRODUCTION TO MODAL LOGIC 
Journal of Symbolic Logic, 14, 159-66(6.2, 14.1). 
1950, 'Completeness in the theory of types', Vie Journal of Symbolic Logic, 
15, 81-91 (9.6). 
Heyting, A., 1930, 'Die formalen Regeln der intuitionistischen Logik', 
Sitzungsberichte 
der 
Preussischen 
Akademie 
der 
Wissenschqften, 
Physikalische-mathematischeKlasse, 42-56 (12.18). 
Hintikka, K.J.J., 1961, 'Modality and quantification', Theoria, 27, 110-28 (13.2, 
15.1). 
1963, 'The modes of modality', Acta Philosophica Fennica - Modal and 
Many-valued Logics, 65-81 (17.2). 
Hodes, H.T., 1984a, 'Some theorems on the expressive limitations of modal 
languages', Journal of Philosophical Logic, 13, 13-26(19.1). 
1984b, 'Axioms for actuality', Journal of Philosophical Logic, 13, 27-34 
(19.1). 
Hughes, G.E., 1975, 'B(S4.3,S4) unveiled', Vieoria, 41, 85-8 (12.6). 
1980, 'Equivalence relations and S5', Notre Dame Journal of Formal Logic, 
21, 577-84 (Exercise 3.8). 
1982, 'Some strong omnitemporal logics', Synthese, 53, 19-42 (12.6). 
1990, 'Every world can see a reflexive world', Studia Logica, 49, 175-81 
(10.13). 
Hughes, G.E. and M.J. Cresswell, 1968, An Introduction to Modal Logic, 
London, Methuen, (reprinted with corrections, 1972) (7.7, 10.6, 10.8, 
11.11, 11.24, 11.25, 12.2, 12.6, 13.6, 14.2, 15.2, 15.8). 
1975, 'Omnitemporal logic and converging time', Theoria, 41, 11-34 (8.7). 
1982, 'Kl.l is not canonical', Bulletin of the Section of Logic, Polish Academy 
of Sciences, 11, 109-13 (Exercise 7.12). 
1984, A Companion to Modal Logic, London, Methuen (4.2, 7.11, 7.12, 8.1, 
9.1, 10.1). 
1986, 'A Companion to Modal Logic - some corrections', Logique et Analyse, 
No 112,41-51 (8.1). 
Humberstone, I.L., 1983, 'Inaccessible worlds', Notre Dame Journal of Formal 
Logic, 24, 346-52 (12.7, 12.14). 
1987, 'The modal logic of "all and only"', Notre Dame Journal of Formal 
Logic, 28, 177-88 (12.14). 
Isard, S., 1977, 'A finitely axiomatizable undecidable extension of K\ Jlieoria, 
43, 195-202(8.6). 
Jansana, R., 1994, 'Some logics related to von Wright's logic of place', Notre 
Dame Journal of Formal Logic, 35, 88-98 (7.10). 
Jennings, R.E., 1981, 'A note on the axiomatisation of Brouweresche modal 
logic', Journal of Philosophical Logic, 10, 341-3 (Exercise 3.13). 
Jonsson, B, and A Tarski, 1951, 'Boolean algebras with operators', American 
Journal of Mathematics, 73, 891-939 (1.3, 12.26). 
Kalmar, L., 1936, 'Zuruckfiihrung des Entscheidungsproblems auf den Fall von 
390 


BIBLIOGRAPHY 
Formeln 
mit 
einer 
einzigenbinaren 
Funktionsvariablen', 
Compositio 
Mathematica, 4, 137-44 (14.5). 
Kamp, J.A.W., 1971, 'Formal properties of "now"', Theoria, 40, 76-109 (19.1). 
Kanger, S., 1957a, Provability in Logic, Stockholm, Almqvist & Wiksell (1.3, 
13.2). 
1957b, 'The morning star paradox', Theoria, 23, 1-11 (18.1, 18.5). 
Kaplan, D., 1966, 'Review of Kripke', The Journal of Symbolic Logic, 31, 120-2 
(6.1). 
Kneale, W.C., 1956, 'The province of logic', Contemporary British Philosophy, 
(ed. H.D.Lewis), London, George Allen and Unwin, 237-61 (11.33). 
Kneale, W.C. and M. Kneale, 1962, The development of logic, Oxford, 
Clarendon Press (11.1, 11.33). 
Kracht, M, 1991, 'A solution to a problem of Urquhart', Journal of Philosophical 
Logic, 20, 285-6 (8.6). 
Kripke, S.A., 1959, 'A completeness theorem in modal logic', The Journal of 
Symbolic Logic, 24, 1-14 (1.3, 6.1, 12.20, 14.2). 
1962, 'The undecidability of monadic modal quantification theory', Zeitschrift 
fiir mathematische Logik und Grundlagen der Mathematik, 8, 113-6 (14.6). 
1963a, 'Semantical analysis of modal logic I, normal propositional calculi', 
Zeitschrift fur mathematische Logik und Grundlagen der Mathematik, 9,67-96 
(1.3, 2.3, 4.2, 6.1, 7.4). 
1963b, 'Semantical considerations on modal logics', Acta Philosophica Fennica 
- Modal and Many-valued Logics, 83-94 (13.2, 15.3, 16.6, 16.7). 
1965a, 'Semantical analysis of intuitionistic logic I', Formal Systems and 
Recursive Functions (ed. J.N. Crossley, M.A.E. Dummett), Amsterdam, 
North Holland Publishing Co., 92-129 (12.18). 
1965b, 'Semantical analysis of modal logic II, non-normal modal propositional 
calculi', The Theory of Models (ed. J.W. Addison, L. Henkin, A. Tarski), 
Amsterdam, North Holland Publishing Co., 206-20 (11.23, 11.26). 
1967, 'Review of E.J. Lemmon; Algebraic semantics for modal logics II', 
Mathematical Reviews 34, 1022 (Review no. 5662.) (14.3). 
1992, 'Individual concepts, their logic, philosophy, and some of their uses', 
(abstract) American Philosophical Association, Eastern Division, Eighty 
second Annual Meeting, December 27-30 1992, 70-3 (18.6, 18.10). 
Kuhn, S.T., 1979, 'Quantifiers as modal operators', Studia Logica, 39, 145-58 
(19.1, 19.2). 
1989, 'The domino relation: Flattening a two-dimensional modal logic', Journal 
of Philosophical Logic, 18, 173-95 (19.1). 
Langholm, T, 1987, 'H.B. Smith on modality', Journal of Philosophical Logic, 
16, 337-46 (11.25). 
Lemmon, E.J., 1956, 'Alternative postulate sets for Lewis's S5', The Journal of 
Symbolic Logic, 21, 347-49 (Exercise 3.9). 
1957, 'New foundations for Lewis modal systems', The Journal of Symbolic 
391 


A NEW INTRODUCTION TO MODAL LOGIC 
Logic, 22, 176-86 (11.19, 11.27). 
1959, is there only one correct system of modal logic?', Aristotelian Society 
Supplementary Volume XXXIII, 23-40 (11.19). 
1960a, 'An extension algebra and the modal system T', Notre Dame Journal of 
Formal Logic, 1, 2-12 (12.26). 
1960b, 'Quantified S4 and the Barcan formula', (Abstract), The Journal of 
Symbolic Logic, 24, 391-2 (15.4). 
1965a, 'Some results on finite axiomatizability in modal logic', Notre Dame 
Journal of Formal Logic, 6, 301-7 (10.15). 
1965b, Beginning Logic, London, Van Nostrand (12.3, 12.4). 
1966a, 'Algebraic semantics for modal logics I', The Journal of Symbolic 
Logic, 31, 46-65(12.26). 
1966b, 'Algebraic semantics for modal logics II', ibid., 191-218 (12.26). 
Lemmon, E.J., and D.S. Scott, 1977, The 'Lemmon Notes': An Introduction to 
Modal Logic, ed. K. Segerberg, Oxford, Basil Blackwell (2.1, 2.3, 2.7, 2.8, 
3.4, 6.1, 7.8, 9.1, 10.10, 10.12). 
Lewis, C.I., 1912, implication and the algebra of logic', Mind, N.S. 21, 522-31 
(11.6, 11.7). 
1913, interesting theorems in symbolic logic', Journal of Philosophy, 10, 
239-42 (11.6). 
1914a, 'A new algebra of strict implication', Mind N.S. 23, 240-7 (11.6, 
11.33). 
1914b, 'The matrix algebra for implication', Journal of Philosophy, 11, 
589-600 (11.6). 
1918, A Survey of Symbolic Logic, Berkeley, University of California Press, 
(N.B. The chapter on strict implication is not included in the 1961 Dover 
reprint) (11.6, 11.7, 11.9, 11.11). 
1920, 'Strict implication. An emendation', Journal of Philosophy, 17, 300-2 
(11.9). 
Lewis, C.I., and C.H. Langford, 1932, Symbolic Logic, New York, Dover 
publications (1.2, 3.2, 3.5, 11.6,11.11,11.14,11.21,11.22,11.32,11.33). 
Lewis, D.K., 1968, 'Counterpart theory and quantified modal logic', The Journal 
of Philosophy, 65, 113-26 (19.3, 19.4). 
1973, Counterfactuals, Oxford, Basil Blackwell (12.16). 
1974, intensional logics without iterative axioms', Journal of Philosophical 
Logic, 3, 457-66(9.2). 
1986, On the Plurality of Worlds, Oxford, Basil Blackwell (19.3). 
Lob, M.H., 1966, 'Extensional interpretations of modal logics', The Journal of 
Symbolic Logic, 31, 23-45 (7.13). 
Loux, M.J., 1979, The Possible and the Actual: Readings in the Metaphysics of 
Modality, Ithaca, Cornell University Press (1.4). 
McCall, S., 1963, Aristotle's Modal Syllogisms, Amsterdam, North Holland 
Publishing Co (11.1). 
392 


BIBLIOGRAPHY 
MacColl, H., 1880, 'Symbolical reasoning', Mind, 5, 45-60 (11.2). 
1903, 'Symbolic reasoning V , Mind (N.S.) 12, 355-64 (11.3). 
1906a, Symbolic logic and its applications, London (11.3, 11.4). 
1906b, 'Symbolic reasoning VIII', Mind (N.S.) 15,504-18 (11.3,11.4,11.30). 
McKay, T.J., 1975, 'Essentialism in quantified modal logic', Journal of 
Philosophical Logic, 4, 423-38 (13.6). 
1978, 'The principle of predication', Journal of Philosophical Logic, 7, 19-26 
(13.6). 
McKinsey, J.C.C., 
1934, 'A reduction in the number of postulates for C.I. 
Lewis' system of strict implication', Bulletin of the American Mathematical 
Society, 40, 425-7(11.14). 
1941, 'A solution of the decision problem for the Lewis systems S2 and S4 with 
an application to topology', The Journal of Symbolic Logic, 6, 117-34 (8.1, 
12.26). 
1944, 'On the number of complete extensions of the Lewis systems of sentential 
calculus', T/ie Journal of Symbolic Logic, 9, 41-5 (3.7). 
1945, 'On the syntactical construction of systems of modal logic', 77**? Journal 
of Symbolic Logic, 10, 83-96(1.3, 7.7, 12.20). 
McKinsey, J.C.C., and A. Tarski, 1944, 'The algebra of topology', Annals of 
Mathematics, 45, 141-91 (12.26). 
1948, 'Some theorems about the sentential calculi of Lewis and Heyting', The 
Journal of Symbolic Logic, 13, 1-15 (12.18). 
Makinson, D.C., 1966a, 'There are infinitely many Diodorean modal functions', 
Vie Journal of Symbolic Logic, 31, 406-8 (5.2). 
1966, 'On some completeness theorems in modal logic', Zeitschrift fur 
mathematische Logik und Grundlagen der Mathematik, 12, 379-84 (6.1). 
1969, 'A normal modal calculus between T and S4 without the finite model 
property', Tlie Journal of Symbolic Logic, 34, 35-8 (8.8). 
1970, 'A generalisation of the concept of a relational frame for modal logic', 
Theoria, 36, 331-5 (9.6). 
1971, 'Some embedding theorems in modal logic', Notre Dame Journal of 
Formal Logic, 12, 252-4 (3.7). 
Marcus, Mrs J.A., vide Barcan, R.C. 
Meredith, C.A., 1956, Interpretations of Different Modal Logics in the 'Property 
Calculus', (cyclostyled) Christchurch, Philosophy Department, Canterbury 
University College (recorded and expanded by A.N. Prior) (1.3). 
Ming Xu, 1991, 'Some descending chains of incomplete logics', Journal of 
Philosophical Logic, 20, 265-83 (9.1). 
Moh Shaw-Kwei, 1950, 'The deduction theorems and two new logical systems', 
Methodos, 2, 56-75 (11.33). 
Montagna, F., 1984, 'The predicate modal logic of provability', Notre Dame 
Journal of Formal Logic, 25, 179-89 (Exercise 14.5). 
Montague, R.M., 1960, 'Logical necessity, physical necessity, ethics and 
393 


A NEW INTRODUCTION TO MODAL LOGIC 
quantifiers', Inquiry, 4, 259-269. (reprinted in Montague 1974 71-83) (1.3, 
13.2). 
1963, 'Syntactical treatments of modality', Acta Philosophica Fennica - Modal 
and Many-valued Logics, 153-66 (reprinted in Montague 1974, 286-302) 
(12.22). 
1974, Formal Philosophy, New Haven, Yale University Press (17.4). 
Montgomery, H.A., and F.R. Routley, 1966, 'Contingency and non-contingency 
bases for normal modal logics', Logique et Analyse, 9, 318-28 (1.2). 
Moore, G.E., 1919, 'External and internal relations', Proceedings of the 
Aristotelian Society (reprinted in Philosophical Studies, London, Kegan Paul, 
Trench, Trubner & Co., (subsequent reprints, Routledge and Kegan Paul) 
276-309 (11.29). 
Morgan, C.G., 1982, 'Simple probabilistic semantics for propositional K, T, B, 
S4 and S5', Journal of Philosophical Logic, 11, 443-58 (12.23, 12.24). 
Myhill, J.R., 1958, 'Problems arising in the formalization of intensional logic', 
Logique et Analyse, 1, (No.2) 74-83 (15.1). 
Ohama, S. 1982, 'Conjunctive normal forms and weak modal logics without the 
axiom of necessity', Notre Dame Journal of Formal Logic, 25, 141-51 (5.1). 
Parks, Z., 1974, 'Semantics for contingent identity systems', Notre Dame Journal 
of Formal Logic, 15, 333-4 (18.4). 
Parks, Z, and T.L. Smith, 1974, 'The inadequacy of Hughes and Cresswell's 
semantics for the CI systems', Notre Dame Journal of Formal Logic, 15, 
331-2(18.4). 
Parry, W.T., 1939, 'Modalities in the Survey system of strict implication', The 
Journal of Symbolic Logic, 4, 131-54 (3.3, 5.3, 11.21). 
Parsons, CD., 1975, 'On modal quantifier theory with contingent domains' 
(abstract), The Journal of Symbolic Logic, 40, 302 (16.3). 
Plantinga, A, 1976, 'Actualism and possible worlds', Theoria, 42, 139-60 
(reprinted in Loux 1979, 253-73) (18.9). 
Pledger, K.E., 1972, 'Modalities of systems containing S3', Zeitschriji fiir 
mathematische Logik und Grundlagen der Mathematik, 18, 267-83 (11.21). 
Pollock, J.L., 1966, 'The paradoxes of strict implication', Logique et Analyse, 
34, (Vol. 9) 180-96 (11.32). 
Prior, A.N., 1955a, Formal logic, Oxford University Press, Second Edition, 1962 
(Exercise 3.9, 13.9). 
1955b, 'Diodoran modalities', 77**? Philosophical Quarterly, 5, 205-13 (7.2). 
1956, 'Modality and quantification in S5', Jlie Journal of Symbolic Logic, 21, 
60-2 (13.5). 
1957, Time and Modality, Oxford University Press (3.3, 7.1, 7.2, 7.3, 15.1, 
16.5). 
1958, 'Diodorus and modal logic, a correction', TJie Philosophical Quarterly, 
8, 226-30 (a correction to Prior 1955b) (7.3). 
1962, 'Possible worlds', The Philosophical Quarterly, 12, 36-43 (7.4). 
394 


BIBLIOGRAPHY 
1967, Past, Present and Future, Oxford University Press (7.1, 13.5). 
1968, 'Now', Nous, 12, 191-207(19.1). 
Quine, W.V., 1947, 'The problem of interpreting modal logic', The Journal of 
Symbolic Logic, 12, 43-8 (17.1). 
1953, 'Reference and modality', From a Logical Point of View, Cambridge, 
Mass, Harvard University Press, 139-59 (18.2). 
Rescher, N., 1959, 'On the logic of existence and denotation', The Philosophical 
Review, 58, 157-80 (16.2). 
Russell, B.A.W., 1905, 'On denoting', Mind, 14, 479-93 (17.3). 
Sahlqvist, H., 1975, 'Completeness and correspondence in first and second-order 
semantics for modal logic', in Kanger, S. (ed), Proceedings of the Third 
Scandinavian Logic Symposium, Amsterdam, North Holland, 110-43 (10.1, 
10.11). 
Schotch, P.K., and R.E. Jennings, 1980, 'Modal logic and the theory of modal 
aggregation', Philosophia, 9, 265-78 (12.15). 
Schumm, G.F., 1975, 'Wajsberg normal forms for S5', Journal of Philosophical 
Logic, 4, 357-60 (5.1). 
1987 'Some noncompactness results for modal logic', Notre Dame Journal of 
Formal Logic, 30, 285-90 (10.8). 
Schweizer, P., 1992, 'A syntactical approach to modality', Journal of 
Philosophical Logic, 22, 1-31 (12.20). 
1993, 'Quantified Quinean S5', Journal of Philosophical Logic, 22, 589-605 
(12.20). 
Scroggs, S.J., 1951, 'Extensions of the Lewis system S5', The Journal of 
Symbolic Logic, 16, 112-20(8.1). 
Segerberg, K, 1968a, 'Decidability of S4.1', Theoria, 34, 7-20 (8.1, 9.5). 
1968b, Results in Non-classical Logic, Lund, Berlingska Boktryckeriet (2.3). 
1970, 'Modal logics with linear alternative relations', Theoria, 36, 301-22 (7.6, 
10.7). 
1971, An Essay in Classical Modal Logic (3 vols), Uppsala, Filosofiska studier 
(2.9, 7.5, 7.10, 7.13, 8.1, 8.4, 8.5, 9.3, 9.4, 12.12). 
1972, 'Post completeness in modal logic', The Journal of Symbolic Logic, 37, 
711-15(3.7). 
1973a, 'Franzen's proof of Bull's theorem', Ajatus, 35, 216-21 (8.2). 
1973b, 'Two-dimensional modal logic', Journal of Philosophical Logic, 2, 
77-96 (19.1). 
1975, 'That every extension ofS4.3 is normal', in Kanger, S. (ed), Proceedings 
of the Third Scandinavian Logic Symposium, Amsterdam, North Holland, 
194-6 (8.3). 
1980 'A note on the logic of elsewhere', Theoria, 46, 183-7 (7.11). 
Shehtman, V.B., and D.P. Skvorcov, 1991, 'Semantics of non-classical first-
order predicate logics', Mathematical Logic, Proceedings of Hey ting 88 at 
Chajka (Bulgaria) 1988, New York, Plenum Press (14.4). 
395 


A NEW INTRODUCTION TO MODAL LOGIC 
Skyrms, B., 1978, 'An immaculate conception of modality', Vie Journal of 
Philosophy, 75, 368-87 (12.20, 12.21, 12.22). 
Smith, H.B., 1936, 'The algebra of propositions', Philosophy of Science, 2, 
551-78 (11.25). 
Smullyan, A.F., 1948, 'Modality and description', The Journal of Symbolic 
Logic, 13, 31-7 (17.5). 
Sobocinski, B., 1953, 'Note on a modal system of Feys-von Wright', The Journal 
of Computing Systems, 1, 171-8 (2.7). 
1964a, 'Remarks about the axiomatizations of certain modal systems', Notre 
Dame Journal of Formal Logic, 5, 71-80 (7.7). 
1964b, 'Modal system S4.4', Notre Dame Journal of Formal Logic, 5, 305-12 
(7.6). 
1964c, 'Family K of the non-Lewis modal systems', Notre Dame Journal of 
Formal Logic, 5, 313-8 (7.1). 
Stalnaker, R.C. 1968, 'A theory of conditionals', Studies in Logical Vieory (ed. 
N. Rescher), Oxford, Basil Blackwell, 98-112 (12.16). 
Stalnaker, R.C, and R.H. Thomason, 1968, 'Abstraction in first-order modal 
logic', T/ieoria, 34, 203-7 (18.8). 
Sugihara, T., 1962, 'The number of modalities in T supplemented by the axiom 
CL2pL3p\ The Journal of Symbolic Logic, 27, 407-8 (3.1). 
Thomas, I, 1962, 'Solutions of five modal problems of Sobocinski', Notre Dame 
Journal of Formal Logic, 3 199-200. (1.3). 
1964, 'Modal systems in the neighbourhood of T', Notre Dame Journal of 
Formal Logic, 5, 59-61 (3.1). 
Thomason, R.H., 1970a, 'Some completeness results for modal predicate calculi', 
Philosophical Problems in Logic (ed K. Lambert), Dordrecht, Reidel, 
56-76 (14.2, 16.3, 16.4). 
1970b, 'Modality and metaphysics', Vie Logical Way of Doing Viings (ed. K. 
Lambert), New Haven, Yale University Press (18.6). 
Thomason, R.H., and R.C. Stalnaker, 1968, 'Modality and reference', Notts, 2, 
359-72 (18.8). 
Thomason, S.K., 1972a, 'Semantic analysis of tense logics', Vie Journal of 
Symbolic Logic, 37, 150-8 (9.6, 9.7). 
1972b, 'Noncompactness in propositional modal logic', Vie Journal of 
Symbolic Logic, 37, 716-20 (10.8). 
1974a, 'An incompleteness theorem in modal logic', Theoria, 40, 30-4 (9.1). 
1974b, 'Reduction of tense logic to modal logic', Vie Journal of Symbolic 
Logic, 39, 549-51 (10.16). 
1975a, 'The logical consequence relation of propositional tense logic', 
Zeitschrift fur malhematische Logik unci Grundlagen der Mathematik, 21, 
29-40 (10.16). 
1975b, 'Reduction of second-order logic to modal logic', Zeitschrift fiir 
malhematische Logik und Grundlagen der Mathematik, 21, 107-14 (10.16). 
396 


BIBLIOGRAPHY 
Tichy, P., 1973, 'On de dicto modalities in quantified S5', Journal of 
Philosophical Logic, 2, 687-92 (13.6). 
Ullrich, D., and M. Byrd, 1977, 'The extensions of BAlt3', Journal of 
Philosophical Logic, 6, 109-117 (7.10). 
Urquhart, A., 1981, 'Decidability and the finite model property', Journal of 
Philosophical Logic, 10, 367-70(8.5). 
Venema, Y., 1992, 'A note on the tense logic of dominoes', Journal of 
Philosophical Logic, 21, 173-82(19.1). 
Vlach, F., 1973, '"Now" and "then". A formal study in the logic of tense 
anaphora', PhD dissertation, UCLA. (19.1). 
Vredenduin, P.G.J, 1939, 'A system of strict implication', The Journal of 
Symbolic Logic, 4, 73-76 (11.31). 
Wajsberg, M., 1933, 'Ein erweiteter Klassenkalkiil', Monatsheftefiir Mathematik 
und Physik, Vol. 40, 113-26 (1.3, 5.1). 
Wang, X., 1992, 'The McKinsey axiom is not compact', The Journal of Symbolic 
Logic, 57, 1230-8 (10.12). 
Whitehead, A.N., 
and B.A.W. 
Russell, 1910, Principia 
mathematica, 
Cambridge, Cambridge University Press, 3 vols., First edition 1910-1913, 
Second edition 1923-1927 (11.5, 12.2, 17.3). 
Williamson, T, 1988, 'Assertion, denial and some cancellation rules in modal 
logic', Journal of Philosophical Logic, 17, 299-318 (3.6). 
1992, 'An alternative rule of disjunction in modal logic', Notre Dame Journal 
of Formal Logic, 33, 89-100 (3.6). 
1994, 'Non-genuine Macintosh Logics', Journal of Philosophical Logic, 23, 
87-101 (3.6). 
Wright, G.H. Von, 1951, An Essay in Modal Logic, Amsterdam, North Holland 
Publishing Co (2.7, 4.1, 13.6). 
1979, 'A modal logic of place', Vie Philosopliy of Nicholas Reseller (ed. E. 
Sosa), Dordrecht, Reidel, 63-73 (7.11). 
Yonemitzu, N., 1955, 'A note on the modal systems, von Wright's and Lewis's 
SI', Memoirs of the Osaka University of the Liberal Arts and Education 
Bulletin of Natural Science, no. 4, 45 (11.18). 
Zeman, J.J., 1973, Modal Logic: Vie Lewis Systems, Oxford, Clarendon Press 
(11.11, 15.9, 15.10). 
397 


INDEX 
a + b, MacColl 193 
A, actuality operator 351 
A, assumption axiom in natural 
deduction 212 
a 4, canonical model based on 
146, truth set of a, | a| 162, 221 
a-maximality 146 
a, = an 95 
CLWPU 
••• 
>PM25 
a\y/x] 241 
Absorption, by a modal operator 
99 
Accessibility relation, R 37 
Actualist quantifier, II 303 
Actuality operator, A 351 
Add, transformation rule in 
natural deduction 212 
Adjunction, law of 13, rule in SI 
199 
Affirmative modality 55 
Aggregation 222 
Agreement, principle of, PA 241 
Alban, M.J. 207 
Algebraic semantics for modal 
logic 229 
Allowable intensional objects 333, 
sets of worlds 167 
Alphabetic variants, bound 241 
Alternative, jc-alternative 239, 243 
Alternatives in a semantic diagram 
83 
Altn 142 
Anderson, A.R. 93 
Antecedent of an implication 7 
Antilogism, principle of 209 
Antisymmetrical relation 130 
Aqvist 
1964 208 
1973 231,358 
Aristotle 193, 206 
Assertion sign, |- 25 
Associative Laws 13, in 
equivalence transformations 95 
Assumption axiom in natural 
deduction 212 
Asterisks, rule for putting in 75 
Asymmetry, expressibility in 
bimodal logic 220 
Atom, in a CNF 96, in MCNF 97 
Axiom schema, PC, for LPC 241 
Axiom 23, additional 39, 293, 
Chellas's numbering of 50 
Axiom of Necessity 42 
Axiom schema 49, PC 25, 241 
Axiomatic PC 210 
Axiomatic system 23, 
completeness 36, proof in a 26, 
soundness 36, theorem of 26 
Axiomatizability 50, 158, finite 
50, 157, KMT 187, intensional 
objects 335-342, intensional 
predicates 346, S5 with 
intensional objects 348 
[a?]/3 221 
a', MacColl 193 
VI, LPC 240, 241, validity of for 
systems without BF 276, VIE, 
Vl with existence predicate 293, 
398 


INDEX 
VlK 305 
V2, rule in LPC 242 
B, Brouwerian system 62, all 
frames symmetrical 175, 
completeness of 121, frames 63, 
frames and models for LPC + B 
282, finite model property of 
149, independent of S4 63, 
natural deduction basis for 217, 
validity in 63, 4 not in 63 
B, Brouwerian axiom 62, not in 
S4 63, proof in S5 62 
B + BF, frames for 249 
0 4 
Barcan Formula, BF 244, 
converse 245, 289, proof in LPC 
-I- S5 247, philosophical 
objections 274, 303, soundness 
for systems without 276, 
temporal interpretation 303 
Barcan, R.C. (Barcan Marcus, R.) 
255 
1947 329 
1946 22 
1962 287 
Basing of a model on a frame 39 
Bayart, A. 
1958 22, 255 
1959 123, 273 
Becker, O. 22, 
70, 197, 206, 207, 231 
Becker's Rule, BR, 200, 207 
Bellissima, F. 70, 157 
Benthem, J.F.A.K. van 
1975 191 
1978 158, 167, 170, 171 
1979a 144 
1979b 170 
1983 191 
1984 191 
and Blok 1978 191 
Bergmann, G. 157 
BF, Barcan Formula 244, BF 
model 247, canonical model for 
systems without 280, 
completeness for systems without 
282, converse and undefined wff 
291-292, model to invalidate 
277, models for systems without 
275, not in LPC + S4 277, 
proof in S5 247, S + BF 244 
BFC, converse Barcan formula 
245, 289, validity definitions 290 
Blackburn, P. 220, 230 
Blok, W. 
1979 158 
1980 170 
and van Benthem 1978 191 
Bochenski, I.M. 206 
Boolos, G. 
1979 144, 157 
1980 170 
and Sambin 1990 144, 170 
Bound alphabetic variants 241 
Bound occurrence of a variable 
236, replacement of 242 
Bowen, K. 288 
BR, 200, 207 
Broido, J. 255 
Brouwer, L.E.J. 70 
Brouwerian axiom, B 62, system, 
B62 
Brouwersche Axiom 70 
Bull, R.A. 
1964 157 
1965a 142, 191 
1965b 157 
1966 157 
1970 230 
and Segerberg 1984 231 
Bulldozing 130 
Burgess, J.P. 230 
Byrd, M. 143 143 
C, counterpart relation 354, as an 
399 


A NEW INTRODUCTION TO MODAL LOGIC 
equivalence relation 354 
C, condition for G' 182 
C, condition for Mk 154 
C13, MMp 207 
Canonical model 112, based on a. 
146, finite 146, frames of 136, 
general frames 168, 
irreflexiveness (Gabb) 177, 
LPCE + S 301, mini 146, of 
Ver 121,ofTriv 121, R in 118, 
reflexiveness of R in 120, S + 
BF261,S + LNI315, S5 not 
cohesive 138, serialty of R in 
120, symmetry of R in 121, 
systems without BF 280, 
transitivity of R in 120, Triv, not 
cohesive 137, truth and 
membership 118, V in 118, Ver, 
not cohesive 137, W in 117, 
world that can see every world 
138 
Canonical system 140, 190 
Card, top 333 
Carnap, R. 
1946 22, 110 
1947 255,348 
Chain of rectangles 85, non-
transitive 154, repeating 90 
Characterization by a class of 
frames 40, by a class of models 
159, by finite models 165, by 
different classes of frames 173, 
by the class of all frames for S 
174, of S + BF by S frames 264 
Chellas, B.F. 50, 70, 71, 157, 
191 
Church, A. 
1936 273 
1956 22, 255, 273 
Churchman, C.W. 207 
Class inclusion 9 
113 
Closed wff of LPC 238 
Cluster 130 
CNF, Conjunctive Normal Form 
96, MCNF 97 
Coincidence predicate « 347 
Cofinite set of worlds 162 
Cohesive frame 137, part of an 
LNI frame 315 
Collapsing into PC 64, 65 
Commutative Laws, Comm 13 
Compactness of a modal system 
178, and first-order definability 
184, of non-modal LPC 262, 
non-compactness of KW 
178-179, non-compactness of 
S4.3.1 180 
Completeness 36, absolute 159, B 
121, class of all frames for S 
174, forT 173, D 120, first-
degree axioms 165, first-order 
definability 185, finite model 
property 165 — 166, 
incompleteness of S + BF 
262-271, K 120, KW 150-152, 
linear time 130, LNI systems 
314-317, LPC + S4.2 283, 
LPCE + S 296-301, LPCE + 
S with expanding languages 302, 
LPCK + S 306-309, 
neighbourhood frames 224, non-
modal LPC 261, S + CI 335, S 
+ BF 264, S4 120, S4.2 
134-135, S4.3 129-130, S4.4 
+ BF 284, S4M 132, S5, by 
MCNF 105-108, S5 121, 
systems without BF 282, T + BF 
265,T 120 
Composition law of, Comp 13 
Computer programs, logic of 220 
Concepts, individual 332 
Conditional proof, CP, rule in 
natural deduction 212 
Conjunct 7 
Conjunction 7, truth-table for 7, 
degenerate 96 
400 


INDEX 
Conjunctive normal form, CNF 
96, modal 97, for S3.5 208 
Connected frames 128, validity of 
Dl in 129, frames which validate 
Dl 175 
Consequent, of an implication 7 
Consequential values in a diagram 
76 
Consistency Postulate, Lewis 200 
Consistency, of a set of wff 113, 
of a system 46, of L~(A) U 
{ - a } 117, of {-La:-) sa} 
138 
Constant intensional object iu 345 
Constant wff 47, in D 66, false 
proposition 1 47, loop 220, true 
proposition T 48, individual 327 
Construction of a wff, proof by 
118, 123 
Containment between systems 24 
Contextual definition 324 
Contingent identity, invalidity of 
LI 332, 12" 334, semantics 332 
Continuous time 180 
Contradictions and entailment 204 
Convergence 134, and 
incompleteness of KG1 + BF 
270 
Converse Barcan Formula, BFC 
289, 245, and undefined wff 
2 9 1 - 2 9 2 , validity definitions 
290 
Correspondence theory 191, of a 
frame and an LPC-model 183, of 
a wff with a condition on a frame 
176, of fi and fi*, in IO 
semantics 338 
Corsi, G., 288, 288, 287, 310 
Counterfactual operator, D-» 223, 
logic 2 2 3 - 2 2 4 
Counterpart 354, and intensional 
objects 357 
Counterpart theory, model for 
354, and T 356 
Counterpart relation, as an 
equivalence relation 354 
CP, natural deduction rule 212 
Cresswell, M.J. 
1967a 208 
1967b 207 
1967c 273 
1969 208 
1973 329 
1979 158 
1983a 157 
1983b 157 
1984 158 
1985 231 
1987 170 
1988 22 
1990 358 
1991 288, 287 
1995a 208, 231 
1995b 273 
and Hughes 
1968 (IML) 22, 
143, 190, 191,206,207,208, 
230,231,255, 273,287,288 
1975 158 
1982 142 
1984 (CML) 93, 143, 
143, 157, 170, 190, 191 
1986 157 
Crossley, J.N. 
1977 358 
% class of frames, validity in 72, 
112 
D, system of modal logic 43, and 
Triv 65, 108, and Ver 108, 
completeness of 120, Constant 
wff in 66, finite model property 
of 148, rule P in 46, seriality of 
R in the canonical model of 120, 
soundness of 45, validity 45 
D, domain in a model 238 
D, Prior's name for S4.3.1 180 
401 


A NEW INTRODUCTION TO MODAL LOGIC 
D, axiom for D, Lp D Mp 43 
Dl, theorem of D 43 
Dl, axiom for S4.3 128, validity 
in connected frames 129, 
connectedness of frames which 
validate 175 
Dagger-operator 80, 83 
Dalen, D. van 231 
De dicto wff 250, reading of a 
definite description 321 
De re wff 250, reading of definite 
description 321 
De re and de dicto, non-
equivalence 251 —254 
De Morgan Laws 13, in CNF 
reduction 97 
Dead end 44 
Decidability 152, and the finite 
model property 152 — 153, lack 
of in monadic LPC 271 
Decision procedure 13 
Deducibility and S 203 
Deduction theorem 211 
Deductively equivalent systems 24 
Definability of L 15 
Definability of M 15, 54, 97 
Definite descriptions 318, de re 
and de dicto readings 321 
Definitions, of PC operators 6 
Def L, Lewis 198 
Def =, strict equivalence 195 
Def -i 225 
Def -», intuitionistic PC 225 
Def 3 236 
Def V , 6, 198 
Def -6 195 
Def n 303 
DefM 17 
Def A 6 
Def D 6, 198 
Def = 6 
Degenerate conjunction, 
disjunction 96 
Degree, modal, of a wff 97, 
reducibility 98 
Deontic necessity 14, 43 
Derived rule 29, 42, not always 
preserved in extensions 45 
Descriptions, definite 318, as 
quantifiers 325, intensional 
objects as values 342, Russell's 
theory of 318-323, scope of 324 
Descriptive frames 171 
Detachment, rule of (MP) 25, 29, 
LPC 241, strict 199 
Diagram, semantic 75, alternatives 
in a 83, and finite model 
property 157, chain in 85, 
consequential values 76, for T 
77, infinite 87, initial values 76, 
optional values in 79, rectangle 
in 75, repeating chain in 90, S4 
85-90, S5 91-92, short cuts in 
80, tree 93 
Discourse, universe of (domain) 
237 
Discrete time 180 
Disjunct 5 
Disjunction 5, degenerate 96, rule 
of, RD 71, 142, truth-table for 5 
Disjunctive syllogism, principle of 
204, 205 
Distinguishable model 170 
Distinct modalities 55 
Distribution, L 28, M 34 
Distributive Laws, PC23 95, in 
CNF reduction 97 
DN If A | - a then A | 
a 
213 
Domain, of discourse 237, Dw of 
world w 275 
Domains, overlapping 353 
Double index 351 
Double negation, DN 13 
DR1 30 
DR2 31 
402 


INDEX 
DR3 35 
DR4 62 
DR4' 295 
DR5 132 
DR5' 132 
Dugundji, J. 157 
Dum, name for Nl 190 
Dummett, M.A.E. 
142, 143, 190, 231 
Dunn, J.M. 209 
Duplicates, in a model 165 
D* , enlarged domain 291 
Dyadic operator 5 
Dynamic logic 220 
(D,V), LPC-model 238 
E, existence predicate 292, 
definition of with = 317 
E, axiom for S5 58, in S3.5 208, 
K + E 123, valid in S5 60, not 
in S4 59, name 70 
E-systems, Lemmon 1957 208 
Eligibility of a wff in a world 275 
Emch, A.F. 209 
Empty set 0 212 
Ending time 131, and 
incompleteness 169 
Entailment 202, and contradictions 
204, and -3 203, relation 
between propositions 203, 208, 
paradoxes of 202-204 
Eq, substitution of equivalents 32, 
for strict equivalents, in SI 
199, 200, in equivalence 
transformations 95, LPC 242, 
S0.5 207 
Equivalence, deductive 24, of 
modalities 55, of A |-NDS a and 
A h <* 214 
Equivalence, material 8, strict, = 
195 
Equivalence relation 61, 
counterpart relation as 354, class 
61, frames, S5 + BF 249 
Equivalence transformations 94, in 
role of Eq in 95 
Equivalents, substitution of 32, 
SO.5 207, in LPC 242, strict in 
SI 199, 200 
Essence, individual 345, Plantinga 
348 
Evaluation index 351 
Exactly one, a1* 320 
Existence predicate, E 292, 
axiomatization 39, 293 
Existential quantifier, 3 235, 
definition of 236 
Expressibility in multi-modal 
logics 219, asymmetry 220, 
irreflexiveness 220, 
irreflexiveness with nominals 220 
Extended V-property 306 
Extended language, X and X+ 
257, Xw 280 
Extension, maximal of a 
consistent set 115, for LPC 258, 
of L"(r) U {~a} in LPC 259, 
with the LV-property 296, 
without BF 280 
Extension of a predicate 255 
Extension, proper 24, T of K 43, 
S5 proper of S4 59 
Extensional language 255 
Extensional model 226, modal 
family M of 226 
Extensions of a system, derived 
rules in 45, finite model property 
in 157 
External negation 320 
£v-property 302 
F, finality axiom 131 
F, in tense logic 218 
Failing on a frame 40 
False proposition, 1 47 
Falsifying frame 40, model 40 
403 


A NEW INTRODUCTION TO MODAL LOGIC 
Feys, R. 
1937 50 
1950 22, 208 
1965 206,207,208 
Filtrations 157 
Final point in a frame 131, 132 
Finality condition, Fin 131, axiom 
F 131, of all frames for S4M 
175 
Fine, K. 178, 273 
1970 348 
1971 157 
1972 158 
1974a 190, 191 
1974b 170 
1974c 170 
1975a 144, 191 
1975b 157 
1978 255,273,310,311 
1983 311 
Finite and cofinite sets of worlds 
162 
Finite axiomatizability 50, 157, 
191, extensions of S4.3 157, 
KMT 187 
Finite canonical model 146 
Finite model property 145, B 149, 
characterization by 165, 
completeness 165 — 166, D 148, 
145, decidability 152-153, 
extensions of S4.3 157, K 147, 
K4 149, S4 148-149, S5 149, 
semantic diagrams 157, systems 
without 153-156, T 148, tree 
diagrams 93 
Finite non-transitive chain 154 
First-degree wff 97, and 
completeness 165, reducibility to 
in S5 98 
First-order logic 255, compactness 
262 
First-order definability 182, and 
compactness 184, and 
completeness 185 
First-order theory, 349, modal 
349 
Fitch, F.B. 22, 230 
Fitting, M.C. 230, 231 
Following from 202 
Forbes, G. 358 
Formation rules 3, LPC 236, 
modal propositional logic 16 
FR1 (PC) 3, LPC 236, modal 
propositional logic 16 
FR2 3, LPC 236, modal 
propositional logic 16 
FR2', LPC 243 
FR3 3, LPC 236, modal 
propositional logic 16 
FR4, LPC 236 
Frame, (W,R) for modal 
propositional logic 37, 
characterization by 40, by 
different classes of 173, 
completeness 159, 174, cohesive 
137, connected 129, convergent 
134, correspondence with an 
LPC-model 183, correspondence 
of a wff with a condition on 176, 
definability and completeness 
185, equivalence, S5 + BF 249, 
falsifying 40, final point in a 
131, 132, first use of 50, for S 
and S + BF 264, for a system 
40, 172, forB, 175, for T 173, 
for S + BF, all frames for S 
248, for T, all reflexive 172, for 
S and S + BF 247, for S + BF 
247, for S4, all transitive 175, 
Frame and IO model 338, 
general 166 — 168, irreflexive 
176, isomorphic duplicate 50, K4 
+ BF 249, KB + BF 249, 
Kripke 168, neighbourhood 221, 
non-identity 186, of canonical 
model 136, recession 155, 
404 


INDEX 
reflexive 43, S2 201, S2, validity 
in 201, S3 201, S4 57, serial 45, 
subordination 93, symmetrical 
60, 63, symmetrical and the 
inclusion requirement 277, T-
frame 43, transitive 57, tree 93, 
validity in a class of 72, validity 
on a 39, validity of 4 in frames 
for KH 161 
France, present king of 318 
Free logic 293 
Free occurrence of a variable 236 
Frege, G. 329, 348 
Function symbol, 6 328 
Function, modal 15, 54, 97 
Functional calculus 255 
Fundamental theorem for 
canonical models 118 
G, name for KW 139 
G, in tense logic 218 
G' 182 
G0 142 
Gl, axiom for S4.2 134 
Gabb, rule for irreflexiveness 176 
Gabbay, D.M. 176 
1975 231 
1976 157, 158 
1981 190 
1984 230 
and Rohrer 1979 358 
Gallin, D. 273 
Game, PC 9, setting of 9, 
successful wff in 10 
Game, modal 18, rule for L 18, 
rule for M 18, S2 202, seating 
arrangement 18, 37, setting 
18, 38, successful wff 19, 
validity in a seating arrangement 
19 
Gargov, G. 230 
Garson, J.W. 
1980 348 
1984 310, 311, 348 
Geach, P.T. 143 
General frames 166-168, 
(W,R,P) 167, and completeness 
168 
Generalizable wff in a model 160 
Generalization, universal 242, 293 
Gentzen, G. 230 
Gerson, M. 231 
Ghilardi, G. 288 
Goldblatt, R.I. 
1975b 191 
1976 171,191 
1987 157,221,230 
1991 191 
Goranko, V. 
1990 220,230 
and Gargov 1993 230 
Godel, K. 50, 139, 207, 231 
Guenthner, F. 230 
H, in tense logic 218 
H, axiom for KH 160, modal 
degree of 165, proof in KW 164 
HI 142 
Hallden, S. 
1949a 207 
1949b 22 
Hanson, W.H. 93 
Hawthorn, J. 230 
Hazen, A. 
1976 358 
1979 358 
1990 358 
Henkin, L. 
1949 123,272 
1950 171 
Heyting, A. 231 
Hintikka, K.J.J. 
1961 22, 255 
1963 329 
Hodes, H.T. 358 
Hughes, G.E. 
405 


A NEW INTRODUCTION TO MODAL LOGIC 
1968 157 
1975 230 
1982 230 
1990 191 
and Cresswell 
1968 (IML) 22, 
143, 190, 191,206, 207,208, 
230,231,255,273,287,288 
1975 158 
1982 142 
1984 (CML) 93, 143, 
143, 157, 170, 190, 191 
1986 157 
Humberstone, I.L. 
1977 358 
1983 219, 231 
1987 222, 230, 231 
Hypothesis of an induction 119 
I(M>), intensional object 333 
ix<f>xa, descriptions as quantifiers 
325 
iu, constant function 345 
[ix(f>x)~\j/(ix<f>x), scope indicator 
325 
I, set of allowable objects in an IO 
model 333, predicates applying 
to 345 
?, definite description 324 
II, identity axiom 312, 366 
12, identity axiom 312, 366 
12", 12 for contingent identity 334 
13, symmetry of identity 313 
IC, intuitionistic PC 224, and S4 
225 
Identity predicate, $ = 312, axioms 
for, II, 12 312,366, 12" 334, 
contingent 332, in modal LPC 
313, intensional predicates 345, 
interpretation of 312, necessity 
of, LI 313, symmetry of, 13 313 
Iff 4 
Implication, material 7, antecedent 
of 7, consequent of 7, 
intuitionistic 224, paradoxes of 
194, strict, -3 15, 195 
Importation, law of 13 
Impossibility 15 
Inclusion requirement 275, D* 
291, symmetrical frames 277 
Inclusion, 9 113 
Incompleteness 159, and ending 
time 169, intuitive understanding 
of 168, KG1 + BF 270-271, 
KH 160, LPC + S4.9 283-287, 
LPC + S4.4 283-287, LPC + 
S4M 283, LPCE + S 302, S + 
BF 262-271, S + BF when S is 
incomplete 263, S4M + BF 
265-270, without BF 283-287 
Index, evaluation 351, reference 
351 
Individual essence 345, Plantinga 
348 
Individual constants 327, 
dispensibility of 327, variables 
236 
Individual concepts 332 
Induction, proofs by 118, 123 
Inductive hypothesis 119 
Infinite diagram 87 
Infinitely proper subset 280 
Initial values, in a semantic 
diagram 76 
Intension of a predicate 255 
Intensional language 255 
Intensional object 332, allowable 
333, and overlapping domains 
353, and second-order logic 336, 
constant 345, counterparts 357, 
and second-order frame 338, S5 
348, unaxiomatizability 
335-342, values of descriptions 
342 
Intensional predicates 345, and 
unaxiomatizability 346, and 
406 


INDEX 
identity 345 
Intermediate logics 224-225 
Internal negation 320 
Intuitionistic PC, IC 224, 
implication, -» 224, negation, ~> 
224, and S4 225, and S4.3 225, 
and S5 225, predicate calculus 
231 
Irreflexive frames, expressibility 
in bimodal logic 220, K 
characterized by 176, irreflexive, 
finite, transitive frames, KW 
characterized by 150, irreflexive 
transitive frames, K4 
characterized by 152, model for 
T 173, nominals 220, rule for, 
Gabb 176 
Isard, S. 158 
Isomorphic duplicate of a frame 
50 
Iterated modalities 51, 98, 55 
I -, set of constant intensional 
objects 345 
Jansana, R. 143 
Jl 191 
Jennings, R.E. 
1980 231 
1981 69 
Jonsson B., and A. Tarski 22, 231 
K, system of modal logic 24, 
characterized by irreflexive 
frames 176, completeness of 120, 
finite model property of 147, K 
+ M, not first-order definable 
183, K + p D Lp 66, K-valid 
wff 20, 39, Lp Dp not K-valid 
20, Rule P in 46, soundness of 
39 
K + A 39, 111 
K + Dl 136 
K 4- E 123 
K + Gl 135 
K, axiom of K 25, in S2 200, 
natural deduction proof of 216, 
validity of 20, validity on a 
frame 39 
K~ 219 
K2, for non-aggregative logics 
223 
K3.1 191 
K4, system 64, K4 + BF, 
characterized by transitive 
irreflexive frames 152, finite 
model property 149, transitive 
frames 249 
Kalmar, L. 273 
KAltn 142 
Kamp, J.A.W. 348 
1971 358 
Kanger, S. 
1957a 22, 255 
1957b 255, 348 
Kaplan, D. 123, 348 
KB, system 64 
KB -I- BF, symmetrical frames 
249 
KD4, system 64 
KDB, system 64 
KG1 -I- BF, incompleteness of 
270-271 
KH, incomplete modal system 
160, 4 not a theorem 162, and 
KW 164 — 165, recession frame 
in 162, validity of 4 in frames 
for 161 
KH + 4, proof of W in 164 
KHn, system 170 
KM 157 
KMT 185, not finitely 
axiomatizable 187 
Kn 217 
Kneale, M. 206 
Kneale, W. 206, 209 
Kracht, M. 158 
407 


A NEW INTRODUCTION TO MODAL LOGIC 
Kripke, S.A. 49, 50 
1959 22, 123,231,273 
1962 271 
1963a 22, 93, 123, 142 
1963b 255, 288, 304, 310 
1965a 231 
1965b 207,208 
1967 273 
1992 348 
Kripke frame 168 
Kripke-style systems, for modal 
LPC 304-309, completeness 
306-309 
KTE, alternative name for S5 70 
Kuhn, S.T. 358 
KW 139, and KH 164-165, 
completeness of 150 — 152, non-
canonicity of 140 — 141, non-
compactness of 178 — 179, proof 
of H in 164, proof of 4 in 150, 
validity 150 
L, necessity operator 14, 
definability of 15, rule for in the 
modal game 18 
L"(A) (= {p:Lp E A}) 116 
L+(A) 214 
L-distribution 28 
|- La -* \- a, rule 71 
A, set of additional axioms 
39, 293 
A h « 211, 214 
A 
|-NDS<*214 
Langford, C.H. 22, 198, 204, 
194, 206, 207, 209 
Langholm, T. 208 
Lem0 143 
Lemmon, E.J. 131, 255 
1956 69 
1957 199, 207, 208 
1959 207 
1960a 231 
1960b 288 
1965b 191 
1965c 212, 230 1966a 231 
and Dummett 1959 
142, 143, 190, 231 
and Scott 1977 49, 50, 70, 
123, 143, 156, 182, 191 
Lemmon's basis for SI 199-200 
Length of a wff, proof by 
induction on 118 
Lewis, C.I. 
1912 194,206 
1913 194,206 
1914a 194,206,209 
1914b 194,206 
1918 (the Survey system), 
194, 206, first appearance of -3 
206 
1920 206 
and Langford 1932, 22 194, 
206, 207, 209 
Lewis, D.K. 
1968 353, 358 
1973 223,231 
1974 170 
1986 358 
Linear time, completeness for 130 
LI, necessity of identity 313, for 
variables and terms 344, 
invalidity in CI semantics 332, 
intensional predicates 345 
LL343 
LMI, rule of L—M Interchange 33 
LMp D MLp, testing in S4 
87, 93, axiom 131 
LNI, necessity of non-identities 
314, for variables and terms 344, 
intensional predicates 345 
LNI systems 314, soundness and 
completeness 314—317 
Lob, M.H. 144 
Logically following from 202 
loop, propositional constant 220 
Loux, M.J. 22 
408 


INDEX 
Lower predicate calculus, LPC 
235, axiom schema PC in 241, 
axiomatization of 241 —242, 
closed wff 238, definability of 
modal systems in 182, formation 
rules 236, interpretation of 237, 
intuitionistic 231, Kripke-style 
systems 304—309, modal, 
axiomatization 244, model, 
(D,V) 238, correspondence with 
a frame 183, models for systems 
without BF 275, monadic, 
undecidability of 271, non-
modal, completeness 261, non-
modal, compactness 262, 
substitution-instance 241, 
substitution of equivalents 242, 
translation into 183, validity in 
239, wff, propositional transform 
of 262 
Lp D LLp, 4 51 
LPC -I- S 244, canonical model 
without BF 280, completeness 
without BF 282, soundness 276 
LPC + S4, BF not in 277 
LPC + S4.9, incompleteness of 
283 
LPC + S4.2, completeness of 283 
LPC + S4.3.1 288 
LPC -I- S4.4, incompleteness of 
283 
LPC 4- S4M, incompleteness of 
283 
LPC + S5, frames and models for 
282, proof of BF in 247 
LPC + B, frames and models for 
282 
LPC1 242 
LPC2 242 
LPC3 242 
LPCE + S 293, canonical model 
301, completeness 296-301, 
completeness with expanding 
languages 302, incompleteness 
302, soundness 295 
LPCK + S, axiomatic basis 304, 
completeness 306-309, validity 
and soundness 305 
Lp D p, invalidity of in K 20 
LR, natural deduction modal rule 
214 
X and £+, LPC languages 257, 
^ w280 
LV-property 296 
(A,a), sequent in a natural 
deduction system 212 
L3x4>x D lxL<f>x 246, 322, 342 
M, alternative name for T 50, 93 
M, McKinsey axiom 131 
M, possibility operator 15, 
definability of 15, 54, 97, rule 
for in the modal game 18 
m{ot), extensional model 226 
(moo), finality condition 131 
M-distribution 34 
/*, value-assignment to variables 
238, world relative assignment 
JI(X,W) 331 
fi(x)(w) and n(x,w) 333 
M18, axiom for S4.9 284 
McCall, S. 206 
MacColl, H. 
1880 193 
1903 194 
1906a 194 
1906b 194 
McKay, T.J. 
1978 255 
McKinsey, J.C.C. 
1934 207 
1941 157, 231 
1944 71 
1945 22, 143, 231 
McKinsey axiom 131 
Makinson, D.C. 
409 


A NEW INTRODUCTION TO MODAL LOGIC 
1966a 110 
1966b 123 
1969 154, 158 
1970 171 
1971 71 
Mate, of an LPC wff 263 
Material equivalence 8 
Material implication 7 
Mathematical induction 123 
Maximal consistent set of wff 
113, all theorems in 114, 
extension of a consistent set 115, 
properties of 114, a-maximality 
146 
Maximal consistent* 122 
Mayor, the 314, 318,331 
MCNF, Modal conjunctive normal 
form 97, atom in 97, 
completeness of S5 by 105 — 108, 
for S3.5 208, ordered 103, 
reduction to in S5 101-103, 
validity test for S5 103-105 
Membership, G 50 
Meredith, C.A. 22 
Metalogical variables 4 
Metaphysical status of possible 
worlds 21 
Metaphysics and isomorphic 
frames 50 
Metatheorem and theorem 50 
Method of semantic diagrams 75 
Ming Xu 170 
Mini-canonical model 146 
Mirolli, M. 157 
Mk, system 154 
Mk, axiom for Mk 154 
MMp, as an axiom 201, 207 
Modal degree of a wff 97, 
reducibility 98, and completeness 
165 
Modal LPC, axiomatization 244, 
formation rules 243, identity in 
313, Kripke-style systems 
304-309, model for (W,R,D,V> 
243, models for systems without 
BF 275, validity in 244, [ V ~ ] 
243, \V<t>] 243, [VL] 243, [VV] 
243, [VV] 243 
Modal conjunctive normal form 
(MCNF) 97, atom in 97, 
completeness of S5 by 105 — 108, 
for S3.5 208, ordered 103, 
reduction to in S5 101-103, 
validity test for S5 103-105 
Modal family of extensional 
models 226 
Modal first-order theory 349 
Modal function 15, 54, 97, in S4 
97, reducibility in S5 98 
Modal game 18, rule for L in 18, 
rule for M 18, seating 
arrangement in a 18, 37, setting 
18, 38, successful wff in 19, 
validity in a seating arrangement 
19 
Modal logic, formal definition of 
validity 37, frame 37, frame for 
a system 40, 172, normal system 
40, temporal interpretations of 
127 
Modal operators 13 
Modal system, defined by 
theorems 111 
Modality 15, 54, 97, affirmative 
55, distinct 55, equivalent 55, in 
S3 207, in S4 55, in S5 59, , in 
T 56, iterated 51, 98, negative 
55, reducibility of 55, standard 
form 55 
Model, (W,R,V> for modal 
propositional logic 38, based on 
a frame 39, BF model 247, 
characterization by finite models 
165, characterization by a class 
of 159, duplicates in a 165, 
extensional 226, falsifying 40, 
410 


INDEX 
finite model property and 
completeness 165 —166, 
generalizable wff in 160, LPC, 
validity in 239, LPC, (D,V> 238, 
for T, irreflexive 173, for 
counterpart theory 354, on which 
BF fails 277, S2 202, truth set of 
a wff a in, | a | 162,221, US 
not validity-preserving in 159, 
validity in 112, validity-
preserving 160, (W,R,D,V) for 
modal LPC 243 (See also 
Canonical model.) 
Model structure 50 
Modus Ponens, rule of 25, in 
natural deduction, MPP 212, 
strict, in SI 199, validity-
preservingness of 40 
Moh Shaw-Kwei 209 
Monadic operator 5 
Monadic LPC, undecidability 271 
Montague, R.M. 
1960 22, 255 
1963 231 
1974 329 
Montgomery H.A. 22 
Moore, G.E. 208 
Moral necessity 14 
Morgan, C.G. 228, 231 
MP, Modus Ponens 25, LPC 241, 
strict, in SI 199 
MP-reductum (Carnap) 110 
MPP, Modus Ponens in natural 
deduction 212 
MTn 185 
MTT, Modus Tollens in natural 
deduction 213 
Multi-modal logic 217-221 
MV, system 185 
Myhill, J.R. 287 
N, rule of necessitation 25, in SI 
199, in a first-order theory 349, 
replaced by R* 208, validity-
preservingness without BF 276, 
validity-preserving 40 
n + 1-tuple (w,, ... ,un,w) 243 
N*, in incompleteness of KH 162 
Nl, axiom for S4.3.1 180 
Narrow scope, of a description 
324 
Natural deduction 211-217, f- in 
211, Add 212, assumption axiom 
212, axiom NDS 214, basis for B 
217, basis for S4 216, CP 212, 
modal rule, LR 214, MPP 212, 
proof of K 216, proof of syll 
212, sequent 212, uniform 
substitution in 213 
NDB, natural deduction basis for 
B217 
NDS, natural deduction axiom 
schema 214 
NDS4, natural deduction basis for 
S4 216 
Nearness of worlds 223 
Necessitation, rule of (N) 25, in a 
first-order theory 349, in SI 199, 
replaced by R* 208, validity-
preservingness of 40 
Necessity operator 14, axiom of 
42, and validity 226, of non-
identities 314 
Necessity of identity, LI 313 
Negation 5, truth-table for 5, 
external 320, internal 320, 
intuitionistic, -i 224 
Negative modality 55 
Neighbourhood of a world 221 
Neighbourhood semantics 
221-224, frame 221, frames and 
completeness 224, [VLt] 221 
New world, rules for 76 
Nominals, in tense logic 220 
Non-cohesive frame, canonical 
model for S5 138, for Triv 137, 
411 


A NEW INTRODUCTION TO MODAL LOGIC 
for Ver 137 
Non-aggregative logics 222 
Non-canonicity of KW 140-141 
Non-compactness of KW 
178-179, of S4.3.1 180 
Non-equivalence of de re and de 
dicto 251-254 
Non-finite axiomatizability 191 
Non-identity, ^ 312, necessity of 
314 
Non-identity frames 186 
Non-normal worlds 201 
Non-overlapping domains 353 
Non-theorem, -| 113 
Non-transitive chain 154 
Normal system of propositional 
modal logic 40, 111, canonical 
model for 112 
Notation, primitive 7 
Number of planets 246, 322, 342 
N' 200 
Q = {~Vx4>xy 
<f>yly <f>y2, . . . } , and 
the V-property 257 
Objects, intensional 332 
Occurrence, free or bound of a 
variable 236 
Ohama 110 
Omnitemporal logic, [VLO] 218 
One-world frames, 
characterization of Triv and Ver 
122 
Operator, proposition-forming 4, 
truth-functional 5 
Optional values in a diagram 79 
Ordered pair 50 
Ordered MCNF 103 
Ought 14 
Overlapping domains 353, and 
intensional objects 353 
p D Lp 65, 108, added to K 66 
P, class of allowable sets of 
worlds 167 
P, in tense logic 218 
P, rule, in K and D 46, not 
validity-preserving in T 42 
II, actualist quantifier 303, 
definition o f 3 0 3 , n i E 304 
7r*, do IT finitely many times 221 
[7Ti;7rJa, a is true after doing 
VX\-K2 220 
x, U 7r2, do either irx or ir2 221 
Trl;-w2, do 7r, then ir2 220 
0, \f/, predicate letters 235 
4>=, identity predicate 312 
3>a, {/8:J8 is a sub-formula of a} 
146 
* i > * * U { - 0 : 0 € * a } 146 
</>a, predicate for a 327 
PA, principle of agreement 241 
Pair, ordered 50, unordered 50 
Plantinga, A. 348 
Paradoxes, of implication 194, of 
entailment 202-204, Lewis's 
derivation of 204 
Parks, Z. 348 
Parry, W.T. 70, 110,207 
Parsons, C D . 310 
PC, propositional calculus 3, 
axiomatization of 210, collapsing 
into 64, 65, formation rules 3, 
game 9, successful wff in 10, in 
SI 199, intuitionistic, IC 224, 
operators, definitions of 6, 
primitive symbols 3, 
propositional variables 4, 
reductio method 11, setting 9, 
some valid wff 13, successful wff 
10, tautology 8, transform 65, 
T(OL) 66, unsatisfiable wff of 8, 
validity testing truth-table method 
10, validity 8, wff of 3 
PC, axiom schema 25, axiom 
schema for LPC 241, validity on 
a frame 39 
412 


INDEX 
PC1-PC21 13 
PC22, Distrib 95 
PC23, Distrib 95 
PC-CNF 96 
Permutation of quantifiers 305 
Person next door, the 
314,318,331 
Planets, number of 246, 322, 342 
Pledger, K.E. 207 
PM, axiomatic basis for PC 210 
p-morphism 170 
Pollock, J.L. 209 
Possibilist quantifiers 303 
Possibility 15, relative 37 
Possible worlds 21, 37, 
metaphysical status of 21, set W 
of 37 
Posterity of a world, POSw 290 
Pr, Probability function 227 
PR, principle of replacement 241 
Predicate 235, existence, E 292, 
extension of 255, of intensional 
objects 345 
Predication, principle of 255 
Primitive notation 7 
Primitive symbols of PC 3, of 
modal propositional logic 16 
Principia Mathematica 
194, 206, 230, axiomatic basis 
for PC in 210 
Principle of replacement, PR 241 
Principle of agreement, PA 241 
Principle of predication 255 
Prior, A.N. 127 
1955a 69, 255 
1955b 142 
1957 70, 142, 287, 303, 310 
1958 142, 255 
1962 143 
1967 142, 190, 255 
1968 358 
Probabilistic semantics for modal 
logic 227-228 
Probability function, Pr 227 
Proof, in an axiomatic system 26, 
method of setting out 26-31 
Proper containment 24, extension 
24, part of a wff 146, subset, 
infinitely 280 
Proposition 4, entailment between 
203, 208 
Proposition-forming operator 4 
Propositional calculus 3, 
axiomatically presented 210, 
intuitionistic, IC 224, symbols 
220 
Propositional constant, false 
proposition 1 47, true 
proposition T 48, loop 220 
Propositional modal logic, 
language of 16, logic, normal 
system 40, primitive symbols 16 
Propositional transform, of an 
LPC wff 262 
Propositional variables 4 
Pseudo-epimorphism, p-morphism 
170 
PV305 
PV 305 
Q(w), Dw, domain of world w 275 
QI, Quantifier interchange 242 
QR294 
QRA 306 
Quantifier 235, actualist, II 303, 
descriptions as 325, existential 3 
235, existential, definition of 
236, permutation of 305, 
possibilist 303, scope of 236, 
universal, V 235 
Quantifier interchange, QI 242 
Quasi-normal system 208 
Quasi-reflexive relation 208 
Quasi-regular systems 208 
Quine, W.V.O. 
1947 329 
413 


A NEW INTRODUCTION TO MODAL LOGIC 
1953 348 
R, accessibility relation 37, 
connected 128, convergent 134, 
in the canonical model of a 
propositional modal system 118, 
reflexiveness of in the canonical 
model of T 120, seriality of in 
the canonical model of D 120, 
symmetry of in a canonical 
model 121, transitivity in a 
canonical model 120 
R-chain 136 
R-step 136 
R*, |- a D 0 -» |- La D L0, 
replacement for N in Lemmon's 
E-systems 208 
Rl, axiom for S4.4 284 
R1-R4, reduction laws 52, proof 
in S5 59 
RAA, rule in natural deduction 
213 
RBV, replacement of bound 
variables 242 
RD, Rule of disjunction 71, 142 
RE, |- a s j8 -* \-La = L(S, in 
neighbourhood semantics 222 
Recession frame 155, and KH 162 
Rectangle in a diagram 75 
Reducibility of modalities 55, 
lower modal degree 98, modal 
functions in S5 98 
Reductio method 11, in modal 
logic 72-92 
Reduction law 52, CNF 96, in S5 
59, MCNF in S5 101-103, 
R1-R4 52, to first degree in S5 
98-101 
Reference index 351 
Refined structures 171 
Reflexive frame 43, all frames for 
T 172, in the canonical model of 
T 120, T + BF 249, (Wa,Ra) 
148 
Reflexive world 185 
Regular systems 208 
Relative possibility 37 
Relettering of bound variables 242 
Relevance logic 205 
Repeating chain 90 
Replacement of bound variables, 
RBV 242 
Replacement, principle of, PR 241 
Rescher, N. 310 
Rn 122, 136 
Rohrer, Ch. 358 
Routley, F.R. 22 
Rule for irreflexiveness, Gabb 176 
Russell, B.A.W. 194, 206, 230, 
329 
1905 329 
Russell's theory of descriptions 
318-323 
S, axiomatic system 23, LPC + S 
244, LPCE + S 293, frames for 
and S 4- BF 264, S-model 72 
S', axiom schema of modal LPC 
244 
S + BF 244, all frames for are 
frames for S 248, and frames for 
S 264, canonical model for 261, 
completeness 264, completeness 
and incompleteness 262-271, 
every frame for S a frame for 
247, frame for 247, incomplete 
when S is 263 
S + CI 335, completeness 335 
S + LNI 314, canonical model 
for 315 
S0.5 205, 207, and Eq 207 
SI 198, and PC 199, axiomatic 
basis (Lewis) 198-199, 
Lemmon's basis 199-200, 
necessitation in 199, 
neighbourhood frames for 231, 
414 


INDEX 
validity in 231 
S1-S5, nomenclature 206 
Sl° 199 
S2 198, 200, Lewis's 
axiomatization 200-200, frame 
201, game 202, Kripke's basis 
for 207, validity in 201-202 
S2° 208 
S3, the Survey system 198, 
axiomatic basis 200, frame 201, 
modalities in 207, validity in 
201-202 
S3.5 208, conjunctive normal 
form 208 
S4 53, all frames for are transitive 
175, and intuitionistic logic 225, 
B not in 63, completeness of 
120, diagrams 85-90, E not a 
theorem 59, finite model 
property of 148-149, frame 57, 
history 70, independent of B 63, 
Lewis 198, modal functions in 
97, modalities in 55, natural 
deduction basis for 216, S4 + 
BF, frames for 249, soundness of 
57, validity in 56 
S4.1, Sobocinski 143 
S4.1, McKinsey's name for S4M 
143 
S4.2 134, completeness of LPC + 
S4.2 283, completeness 134 
54.2 + BF, incompleteness of 
271 
54.3 128, completeness of 
129-130, connectedness of 
frames validating Dl 175, finite 
model property in extensions of 
157, finite axiomatizability of 
extensions of 157, intuitionistic 
logic 225, proper axiom Dl of 
128, soundness 129 
S4.3.1 180, not compact 180 
S4.4, incompleteness of LPC + 
S4.4 283-287 
S4.4 + BF, completeness of 284 
S4.9, incompleteness of LPC + 
S4.9 283-287 
S4M 131, completeness of 132, 
all frames final 175 LPC + 
S4M, incompleteness 283 
S4M + BF, incompleteness of 
265-270 
S4M1 132 
S4n70 
S5 58, completeness of 121, 
completeness by MCNF 
105-108, diagram 91-92, E valid 
in 60, finite model property of 
149, frame 61, frame of its 
canonical model not cohesive 
138, frames and models for LPC 
+ S5 282, history 70, intensional 
objects 348, intuitionistic logic 
225, Lewis 198, MCNF validity 
test 103-105, modalities in 59, 
proof of Barcan formula in 247, 
proof of 4 in 58, proof of R1-R4 
in 59, reduction laws 59, 
reduction theorem 98, reduction 
to MCNF in 101-103, validity 
61, validity in 60 
S5 + BF, frames for 249 
S5 + CI 348 
S6, S2 + MMp 207 
57 207 
58 207 
Sahl 182 
Sahlqvist, H. 182, 190, 191 
Sambin, G. 144, 170 
Schema, axiom 49 
Schotch, P.K. 231 
Schumm, G.F. 110, 191 
Schweizer, P. 231 
Scope, of a description 324, of a 
quantifier 236 
Scope indicator [cx(f>x] ~ \J/(ix<f>x) 
415 


A NEW INTRODUCTION TO MODAL LOGIC 
325 
Scott, D.S. 49, 50, 70, 
123, 143, 156,182,191,348 
Scroggs, S.J. 157 
Seating arrangement 18, 37, 
validity in a 19 
Second-order logic 188, and 
intensional objects 336 
Seeing relation, R in a frame 37 
Segerberg, K. 44 
1968a 157, 170 
1968b 50 
1970 143, 191 
1971 50, 130, 139, 143, 144, 
157, 165, 170, 208, 230 
1972 71 
1973a 157, 358 
1973b 352 
1975 157 
1980 143 
and Bull 1984 231 
and Chellas 1994 71 
Semantic diagram 75, alternatives 
in 83, and finite model property 
157, chain in 85, consequential 
values 76, for T 77, infinite 87, 
initial values 76, optional values 
in 79, rectangle in 75, repeating 
chain in 90, S4 85-90, S5 
91-92, short cuts in 80, tree 
diagram 93 
Semantics 24 
Sentence, closed wff of LPC 238 
Sequent, in a natural deduction 
system 212 
Serial frame 45 
Seriality, in the canonical model 
of D 120 
Set theory, (,) 50, membership E 
50, {,} 50 
Setting, in the PC game 9, in the 
modal game 18, 38 
Shehtman V.B. 273 
Short cuts, in a semantic diagram 
80 
Skvorcov D.P. 273 
Skyrms, B. 226, 231 
Smith, H.B. 208 
Smith, T. 348 
Smullyan, A.F. 326, 329 
Sobocinski, B. 70 
1953 50 
1964a 143 
1964b 190 
Soundness 36, B + BF 249, D 
45, K 39, K4 + BF 249, KB + 
BF 249, LNI systems 314, LPC 
+ S 276, LPCE + S 295, LPCK 
+ S 305, S + CI 335, S4 57, S4 
+ BF 249, S4.3 129, T + BF 
249, T 43 
Stalnaker, R.C. 
1968 231 
and Thomason 1968 344, 348 
Standard form of a modality 55 
Step in an R-chain 136 
Strength of a system 24 
Strict detachment 199 
Strict equivalence, = 195, 
substitution in SI 199, 200 
Strict implication 15, -3 195, first 
appearance, Lewis 1918 206, and 
entailment 203, and deducibility 
203 
String of objects, intensional 
object 333 
Sub-formula 146 
Subordination frames 93 
Subset, <= 113, infinitely proper 
280 
Substitution-instance, and validity-
preservation 160, LPC 241 
Substitution of equivalents 32, in 
equivalence transformations 95, 
in SO.5 207, of strict equivalents, 
SI 199, 200, LPC 242 
416 


INDEX 
Successful call, in PC game 10, in 
the modal game 19 
Substitution, uniform 25, 199 
Sugihara, T. 70 
Survey system, S3, Lewis 1918 
197 
Syllogism, law of syll 13, 
disjunctive 204, 205, natural 
deduction proof of 212, rule of 
30 
Symmetrical frame 60, 63, frames 
for B 175, KB + BF 249, and 
the inclusion requirement 277, in 
a canonical model 121, of 
identity, 13 313 
Syntactical approach to logic 24, 
to modality 225-227 
System of modal logic 23, 
axiomatic, soundness 36, 
axiomatic, proof in 26, 
axiomatic, completeness 36, 
canonical 140, 190, consistency 
of 46, containment between 24, 
deductive equivalence of 24, 
defined by theorems 111, frame 
for 40, 172, incomplete 160, K 
of propositional modal logic 24, 
Mk 154, normal 40, 111, 
canonical model for 112, proper 
containment 24, strength of 24, 
wff belonging to 24, wff theorem 
of 24 
T, system of modal logic 41, a 
proper extension of K 43, all 
frames for T are reflexive 172, 
and counterpart theory 356, class 
of all frames for and 
completeness 173, completeness 
of 120, diagram 77, finite model 
property of 148, frame 43, 
history of 50, irreflexive model 
for 173, modalities in 56, 
reflexiveness of R in the 
canonical model 120, soundness 
of 43, validity 43 
T, Lp D p, Axiom of Necessity 
42 
T + BF, completeness of 265, 
reflexive frames 249 
T, truth predicate in IO systems 
337 
T~, and irreflexiveness 220 
r, translation function, into IO 
language 337, into LPC 183, into 
second-order logic 188, PC-
transform 66 
Tarski, A. 231 
Tautology 8 
Temporal interpretations of modal 
logic 127, 179-181, Barcan 
Formula 303 
Tense logic 218, and 
incompleteness 169, [VL2TL] 
218, [VL,TL] 218, TL1, TL2 
218 
Term 325, 327, and variables in 
Thomason and Stalnaker 344 
Testing for validity in modal 
logic, 72-92, by MCNF for S5 
103-105 
0, function symbol 328 
Theorem and metatheorem 50 
Theorem, of an axiomatic system 
26, in all maximal consistent sets 
114, validity of in the canonical 
model 119 
Theory, first-order 349, modal 
349 
Thomas, I. 
1962 22 
1964 70 
Thomason, R.H. 
1970a 273, 310 
1970b 348 
and Stalnaker 1968 344, 348 
417 


A NEW INTRODUCTION TO MODAL LOGIC 
Thomason, S.K. 
1972a 169, 171 
1972b 191 
1974a 170 
1974b 192 
1975a 192 
1975b 192 
Tichy, P. 255 
Time, continuous 180, discrete 
180, ending 131 
TLl, TL2, tense logic axioms 218 
Top card 333 
Transform, PC 65, of an LPC wff 
262 
Transformation rule 23, derived 
rule 29, in natural deduction 212, 
Modus Ponens 25, in LPC 241, 
Necessitation 25, Uniform 
Substitution, rule of 25, 199, 
validity-preserving 24 
Transformations, equivalence 94, 
role of Eq in 95 
Transitive frame 57, all frames 
for S4 175, finite, irreflexive 
frames, KW characterized by 
150, in a canonical model 120, 
irreflexive frames, K4 
characterized by 152, K4 + BF 
249, S3 frame 201 
Transposition, law of, Transp 13 
Tree diagram 93 
Triv, trivial system 65, 108, 
characterized by the one-world 
reflexive frame 122, canonical 
model of 121, frame of its 
canonical model not cohesive 137 
True proposition, constant T 48 
True individuals in IO systems 
337 
Truth predicate in IO systems 337 
Truth-table method of PC validity 
testing 10 
Truth-table for ~ 5, for V 5, for 
D 7, for A 7, for = 8 
Truth and membership, in a 
canonical model 118 
Truth set of a wff a, | a | 
162, 221 
Truth-function 5, truth-functional 
operator 5 
Truth-value 4 
UE293 
UG, universal generalization 
242, 293 
UGLV" 293 
UG- 242 
UGD 242 
Ullrich, D. 143 
Unaxiomatizability of intensional 
objects logic 335-342, 
intensional predicates 346 
Undecidability of monadic modal 
LPC 271 
Undefined wff 277, rules for 278, 
and CBF 291-292 
Uniform Substitution, rule of 
25, 199, not validity-preserving 
in all models 159, in natural 
deduction, US' 213, validity-
preservingness of 40 
Universal generalization 242, 293 
Universal validity, LPC 239 
Universal relation 61 
Universal quantifier, V 235 
Universe of discourse (domain) 
237 
Unordered pair, {a,b}, 50 
Unsatisfiable wff of PC 8, 47 
Urquhart, A. 158 
US, rule of Uniform Substitution 
25, 199, not validity-preserving 
in all models 159, validity-
preservingness of 40 
US', natural deduction 213 
(ulf ... ,wn,w) 243 
418 


INDEX 
(«lf ... ,«n)238 
V, value-assignment in a model 
38, in an LPC-model 238, in the 
canonical model of a 
propositional modal system 118 
V(0), set of n-tuples 238, in 
modal LPC 243, Lewis 354, with 
intensional predicates 345 
V(</>=) interpretation of identity 
312, in modal LPC 313 
V(a) value of individual constant 
327 
VM(a) 239 
VM(0/1.../n,w), value-assignment 
for terms 327 
Validity in modal logic 17-21, 37, 
39, alternative definitions without 
BFC 290, and necessity 226, as 
truth in all worlds in S2, B 63, 
BF models 247, E in S5 60, in a 
class of frames 72, in a seating 
arrangement 19, in a model 112, 
K on a frame 39, K-validity 20, 
KW 150, LPC 239, LPCK + S 
305, modal LPC 244, PC on a 
frame 39, PC 8-10, S + BF 
theorems in S frames 247, SI 
231, S2 201, S3 208, S4 56, S5 
60, some valid wff of PC 13, 
substitution-instances 160, 
systems without BF 275, T 43, 
theorems in the canonical model 
119 
Validity-preservingness, of a 
frame 39, model 160, 
transformation rule 24 
Value-assignment to variables, /x 
238 
Value-assignment for terms 
V^(4>tl..Jn,w) 327 
Values in a semantic diagram, 
consequential 76, initial 76, 
optional in a diagram 79 
Variable, and terms in Thomason 
and Stalnaker 344, bound 
occurrence of 236, free 
occurrence of 236, individual 
236, metalogical 4, occurrence 
of, free or bound 236, 
propositional 4 
Variants, alphabetic, bound 241 
VB, system 169, 185 
Venema, Y. 358 
Ver, Verum system, 66, 108, 
characterized by the one-world 
dead end frame 122, extensions 
of K not in Ver contain D 108, 
frame of its canonical model not 
cohesive 137 
Vlach, F. 358 
VQ293 
VQD 295 
Vredenduin P.G.J. 209 
\VA], for actually operator 351 
[VL] 38, modal LPC 243 
[VL~] 219 
[VL,TL], tense logic 218 
[VL2TL], tense logic 218 
[VLJ 217 
[VLO], omnitemporal logic 218 
[VLS5] 61 
[VL'], in counterpart theory 354 
[VL|], neighbourhood semantics 
221 
[V*L] 278 
\VM] 39 
[V<£], LPC 239, modal LPC 243 
\V<f>"] 334 
[V0'], with world relative 
assignments 331 
[V*<t>] 278 
[V~] 38, LPC 239, modal LPC 
243 
[V*~] 278 
[VV] 38, LPC 239 
419 


A NEW INTRODUCTION TO MODAL LOGIC 
[V*V] 278 
[VA] 38 
[VD] 38 
[V=] 39 
[VV], LPC 239, modal LPC 243 
[VV] 275 
[VV] 291,334 
[V*V] 278 
[V3], LPC 239, modal LPC 243 
W, axiom for KW 139, proof in 
KH + 4 164 
W, set of 'worlds' 37, in the 
canonical model of a 
propositional modal system 117 
w,(i) 81 
W2, wff 123 
Wajsberg, M. 22, 110 
Wang, X. 191 
Well-formed formula, wff 3, 
belonging to a system 24, closed, 
LPC 238, consistent set of 113, 
constant 47, in D 66, 
correspondence with a condition 
on a frame 176, de dicto 250, de 
re 250, eligibility in a world 275, 
generalizable in 160, maximal set 
of 113, maximal consistent set of 
113, modal degree of 97, proof 
by induction on the construction 
of 118, 123, truth set of in a 
modell62, 221, undefined and 
CBF 291-292, undefined 
277-280 
Well-formed part of a wff 146, 
proper 146 
Whitehead, A.N. 194, 206, 230, 
329 
Wide scope, of a description 324 
Williamson, T., 71 
Witness, to a quantifier 257 
Woollaston, L.E. 358 
World, possible 21, 37, allowable 
sets of 167, cofinite set of 162, 
domain of 275, eligibility of a 
wff 275, metaphysical status of 
21, nearness of 223, non-normal 
201, posterity of, POSw 290, 
relative assignment, \i 331, set W 
of 37, that can see every 138 
Wright, G.H. von, 50, 93, 143 
wRW 122 
(W,R,D,I,V>, model for 
intensional objects 333 
(W,R,D,Q,C,V>, model for 
counterpart theory 354 
(W,R,D,Q,V), model for systems 
without BF 275 
(W,R,D,V), model for modal 
LPC 243 
(W,R,P,), general frame 167 
(W,R,V), model for propositional 
modal logic 38 
(W,R,V), validity in 112 
(W,R> 37 
x-alternative 239, 243 
Yonemitzu, N. 207 
Zeman, J.J., 206, 288 
420 


INDEX 
SYMBOLS 
Similar symbols are grouped together but otherwise listed in order of introduction. 
4, Lp D LLp 53, transitivity of 
frames which validate 175, 
invalidity in T 56, not in B 63, 
not a theorem of KH 162, proof 
inKW 150, proof in S5 58, 
proof of W inKH + 4 164, 
validity in transitive frames 57, 
validity in frames for KH 161 
5, alternative name for E 70 
- 3 , 5 
V 3, 6, 198 
VE213 
VI 213 
=df6 
A definition of 6, truth-table for 
7 
AE213 
AI 213 
D definition of 6, 198, truth-table 
for 7 
= definition of 6, truth-table for 
8 
• 22, 352 
O 22 
\-s a 25, as a E S 111 
-» 25, intuitionistic implication 
224 
T , constant true proposition 48 
1 , constant false proposition 47 
E, membership 50 
(,) angle brackets 50 
{,} curly brackets 50 
<=, class inclusion 113 
t 80 
t-operator 80, 83 
-j , non-theorem 1.13 
-3, strict implication 195, first 
appearance, Lewis 1918 206, and 
entailment 203, and deducibility 
203 =, strict equivalence 195, 
and =Df, 206 
f-, in natural deduction systems 
211 
0 , empty set 212, 0 
|- a 212 
D^-223 
< w, nearness of worlds 223 
->, intuitionistic negation 224 
V, universal quantifier 235 
V-property 257, extended 306 
VIA 306 
V3 293, 365 
VI' 294 
[V0] 336 
3, existential quantifier 235 
i'x, exactly one 320 
= , identity predicate, 0= 312, for 
intensional predicates 345 
;*, non-identity 312 
» , coincidence predicate 347 
B 352 
0 352 
0 352 
CD 352 
® 352 
421 
