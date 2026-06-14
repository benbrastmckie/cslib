<!-- Source: Church, A. (1956). Introduction to Mathematical Logic. Chapter III: Functional Calculi of First Order (pages 180-225). BibKey: Church1956 -->

The ju n c tio n a l calcu lu s of f ir s t order has or may have, in addition to no­
tations of the propositional calculus, also in d iv id u a l va ria b les, quantifiers 
with individual variables as operator variables (cf. §06), in d iv id u a l co n sta n ts, 
fu n c tio n a l va ria b les, fu n c tio n a l con stan ts.
Various different functional calculi of first order are distinguished accord­
ing to just which of these notations are introduced. But the individual 
variables are always included, and either some functional variables or some 
functional constants. And one or more quantifiers are always included, 
either the universal quantifier or one or more quantifiers which are (when 
taken together, and in the presence of the other primitive notations) 
d e fin itio n a lly  equ ivalen t to the universal quantifier in the sense that they 
can be obtained from the universal quantifier, and the universal quan­
tifier can be obtained from them, by abbreviative definitions (cf. §11, and 
footnote 168) which reproduce the requisite formal properties. Propositional 
variables are not necessarily included, but there must be a complete system 
of primitive connectives for the propositional calculus, or something from 
which such a complete system of sentence connectives can be obtained by 
abbreviative definitions so as to reproduce the requisite formal properties.
In this chapter we study a particular formulation of each of the functional 
calculi of first order, the various formulations being in their development so 
nearly parallel to one another that they can be treated simultaneously with­
out confusion or awkwardness. Where not necessary to distinguish the var­
ious different functional calculi of first order we speak just of “the func­
tional calculus of first order,” and the particular formulation of the func­
tional calculus of first order studied in this chapter is then called "F1," 
One of the functional calculi of first order is the p u r e  ju n c tio n a l c a lcu lu s of 
first o rd er (as explained in §80 below), and we call our formulation of it 
“Flp ” Thus “F1” is ambiguous among various logistic systems, one of which 
is Flp.
In Chapter IV we shall consider further the pure functional calculus of 
first order, introducing, in particular, an alternative formulation of it, F£p.

---


§30]
PRIMITIVE BASIS
169
30. The prim itive basis of F \ The primitive symbols of F1 are the 
eight improper symbols
[ = ] - ( . )  v
and the infinite list of individual variables
x 
y 
z xx 
yi zt 
x2 y2 z2 
. .
also some or all of the following, including either at least one of the infinite 
lists of functional variables or at least one functional constant:300 the infinite 
list of propositional variables
p 
q 
r s 
qx 
rx 
sx i>2 
. . .
and for each positive integer n an infinite list of «-ary functional variables, 
namely, the infinite list of singulary functional variables
F 1 
G1 H l F\ 
G\ 
H\ F\ 
. . .
and the infinite list of binary functional variables
F 2 
G2 H2 F \ 
G\ 
H \ F\ . . .
and so on, further any number of individual constants, any number of sin­
gulary functional constants, any number of binary functional constants, 
any number of ternary functional constants, and so on. We do not specify 
the particular symbols to be used as functional constants, but allow them 
to be introduced as required, subject to conditions (B) and (I) of §07 (as to 
(B), cf. also footnote 113).
In the case of each category of variables, the order indicated for them is 
called their alphabetic order.
The formation rules of F1 are:
30i. 
A propositional variable standing alone is a wff.301
30ii. 
If f is an «-ary functional variable or an n-ary functional constant,
and if a1( a2, . . 
a n are individual variables or individual constants 
or both (not necessarily all different), then f(ax, a2, . . 
an) is a wff. 
30iii. If r  is wf then ~ T  is wf.
30iv. If r  and A are wf then [T  zd A j is wf.
30v. 
If r  is wf and a is an individual variable then (Va)T is wf.
*°°We require that either all or none of the variables in any one category be included, 
e.g., either the entire infinite list of binary functional variables or none of them. But 
where individual or functional constants are present, their number may be finite.
aMOf course 30i may be vacuous in the case of certain systems F L, namely, if propo­
sitional variables are not included among the prim itive symbols. We m ight therefore 
have written, “ A propositional variable stanejing alone, if the system F1 contains such, 
is a wff.’' The added clause (between commas) increases clearness, but is not otherwise 
actually necessary.

---


170
FUNCTIONAL CALCULI OF FIRST ORDER [Chap. I ll
A formula of F1 is wf if and only if its being so follows from the formation 
rules. As in the case 
and P2 (see §§10, 20) there follows, for a particular 
given system F1, an effective test of well-formedness. The demonstration of 
this is left to the reader.
The wf parts A and B of a wff [A =3 B] are called the antecedent and 
consequent respectively, and the occurrence of rs between them is called the 
principal implication sign. That the antecedent and consequent and 
principal implication sign of any wff [A rs B] are unique is part of the 
metatheorem **312 of the next section,
The converse of [A rs B] is the wff [B rs A] obtained by interchanging 
the antecedent and consequent. The converse of
(Va,)(Va2) . . . (Van)[A =  B] is (Va^Va,) . . . (Va„)[B =  A],
The elementary parts of a wff are the parts which are wf according to 30i 
or 30ii, i.e., they are those wf parts which have either the form of a prop­
ositional variable alone or the form f(alt a2, .. 
a„) where f is an w-ary
functional variable or constant and a1( a2l.. 
an are individual variables 
or constants.
An occurrence of a variable a in a wff A is called a bound occurrence of a 
in A if it is an occurrence in a wf part of A of the form (Va)B; otherwise it 
is called a free occurrence of a in A. The bound variables of A are the variables 
which have bound occurrences in A; and the free variables of A are those 
which have free occurrences in A.302
From the definition of a wff of F1 it follows that all occurrences of prop­
ositional and functional variables are free occurrences. But an occurrence 
of an individual variable in a wff of F1 may be either free or bound.
A wff is an n-ary form if it has exactly n different free variables, a constant 
if it has no free variables. In F1, all forms are propositional forms, and all 
constants (wffs) are propositional constants or sentences. (Cf. note 117.)
In addition to the syntactical notations,
S?A|,
rft Al>
explained in §§10, 12, we shall use also the syntactical notation
S*A|
for the result of substituting T for all free occurrences of b in A, and
$ ^ r*:::r"A !
for the result of substituting simultaneously Fx for all free occurrences of
30*Compare the first four paragraphs of §08, and footnotes 28, 36, 96.

---


§30]
PRIM ITIVE BASIS
171
b2J 1*2 for all free occurrences of b2, . . 
r n f°r all free occurrences of bn, 
throughout A (the dot indicating substitution for free occurrences only).
In writing wffs of F1 we make use of the same abbreviations by omission 
of brackets that were explained in §11, including the same conventions 
about association to the left and about the use of heavy dots. We also ab­
breviate by omitting superscripts on functional variables—writing, e.g., F(x) 
instead of F*(a:), and F(x,y) instead of F*{x,y)—since the superscript required 
to make the formula wf can always be supplied in only one way (cf. 30ii).
Also we adopt for use in connection with F1 the definition schemata 
D3-12, understanding the ff~" which appears in them to be the primitive 
symbol ~  of F1. However, the brackets which appear as part of the notation 
[A, B, C] introduced by D12 must (unlike other brackets) never be omitted.
And we add further the following definition schemata, in which a, ax, 
a* .. . must be individual variables:
D13.303
(a)A -► (Va)A
D14.804
(3a)A -*■ ~(a)~A
Di5.s°s
tA 
B] 
( a ^ a ,) .. . (a „ ). A => B
n — 1, 2, 3, . . .
D16.30B
[A 
B] 
(a,) (a ,).. . (a„) . A =  B
n «: 1, 2, 3___
D17.
[A|„ B] -*■ (a) . A | B
In abbreviating wffs by omission of brackets, we use (as already stated) 
the convention of association to the left of §11. This convention is modified 
in the same way as in §11 by dividing bracket-pairs into categories, the 
same division into categories being used as before with the following ad­
ditions: (1) when one of the signs ro, =  , | is used with subscripts (according 
to D15--17), the bracket-pair that belongs with it is considered in the same 
category as if there were no subscripts; (2) the combinations of symbols 
(Va), (a), (3a) (simple quantifiers with operator variable) are placed along 
with the sign 
in a fourth and lowest category, in the same sense as already 
explained in §11 for
In stating the rules of inference and the axiom schemata of F1, we make 
use (for convenience) of the definition schemata and other conventions of 
abbreviation which have just been described.
in writing wffs we m ay as an abbreviation simply omit the symbol V.
Compare the discussion of the universal quantifier in §06.
“ ‘Compare the discussion of the existential quantifier in §06.
“ ‘Compare the discussion of formal implication and formal equivalence in §06.
The purely abbreviative definition schemata, D15 and D16, are to be distinguished 
from the semantical statem ents made in §06. The latter provide definitions of formal 
implication and formal equivalence rather in sense (2) of footnote 168, and they must 
apply to object languages in which the notations in question are truly present.

---


172
FUNCTIONAL CALCULI OF FIRST ORDER [Chap. Ill
The rules of inference are the two following:
*300. 
From A zd B and A to infer B. 
(Rule of modus ponens.)
*301. 
From A, if a is an individual variable, to infer (a)A,
(Rule of generalization.)
In an application of the rule of modus ponens, we call A =0 B the major 
premiss, and A the minor premiss. In an application of the rule of generali­
zation, we say that the variable a has been generalized upon.
The axioms of F1 are infinite in number, and are represented by means of 
five axiom schemata in the manner described in §27. These axiom schemata 
are as follows:
*302. 
A d . B d A
*303. 
A zd [ B d CJd . A d
B d
. A d C 
*304. 
-A  d  ~B zd . B zd A
*305. 
A roa B zd * A zd (a)B, where a is any individual variable which is 
not a free variable of A.
*306. 
(a)A zd S*A|, where a is an individual variable, b is an individual 
variable or an individual constant, and no free occurrence of a in 
A is in a wf part of A of the form (b)C.
In *305 and *306, we here meet for the first time with axiom schemata 
which, unlike those introduced in §27, have conditions attached to them 
(stated in the syntax language). For example, according to *305, not every 
wff A z>fl B zd m A z> (a) B is an axiom, but only those wffs of this form which 
satisfy the further condition that A contains no free occurrence of a.
The intention of *305 and *306 may be made clearer by giving some 
examples, for the sake of which we suppose that the propositional variables 
and the singulary and binary functional variables are included among the 
primitive symbols of F1.
Thus one of the wffs which is an axiom according to *305 is306
F(x) => *f=> (*) ■?■(*).
or, as we may write it if we do not use the abbreviation of D15,
(x)\j> zd F(a:)] z> up ZD (x)F(x).
(This may be called a basic instance of *305, in the sense that all other in-
*°*In this example, A is the wff p, a is the individual variable x. and B is the wff F(*).

---


§30]
PRIMITIVE BASIS
173
Stances of *305 may be obtained from it by means of rules of substitution 
to be discussed in §35, and that no shorter instance of *305 has this property.) 
Again the wff
(y)H(y)
is an axiom, an instance of *305 (though not a basic instance). And also 
an axiom by *305 is
F{x) =>„ [G{y, z) =3,H(z)] =3 . F[x) =3 .G{y, z) =3 vlH{z),
and so on, an infinite number of axioms altogether. But the following wff 
is not an instance of *305 and not an axiom:
F(cc) r )x G(a:) zd « F(x) zd (x)G(x)
Some wffs which are instances of *306 and therefore axioms are the follow­
ing (the first two are basic instances):307
(x)F(x) zd F(y)
(x)F(x) zd F(x)
F{x) z d x (y)G(y) zd „ F(y) zd {y)G{y)
F(x) =)x {x)G{x) zd . F(y) zd {x)G(z)
F{x, y) ZD x (z)G(xt z) zd wF(y,y) zd {z)G{y, z)
On the other hand the following wffs are not instances of *306 and not 
axioms:308
(x){y)F{x,y) zd {y)F{y, y)
= 3 *  (V ) G ( x , y )  zd .  F ( y )  zd (y ) G [ y , y)
As we did in connection with formulations of the propositional calculus, 
we shall place the sign b before a wff to express that it is a theorem.
Among the various functional calculi of first order, F1, whose primitive 
bases have now been stated, we distinguish certain ones by special names 
as follows. The pure functional calculus of first order, Fxp, is that in which the 
primitive symbols include all the propositional variables and all the func­
tional variables (singulary, binary, ternary, etc.), but no individual constants 
and no functional constants. The singulary functional calculus of first order, 
F1,1, is that in which the primitive symbols include all the propositional 
variables and all the singulary functional variables, but no other functional 
variables, no individual constants, and no functional constants; if to these 07 *
S07To state quite explicitly how these five wffs are instances of *306, we have, taking 
them in order: in the first one, A is F(#), a  is x, b is y; in the second one, A is F(.r), 
a is *, b  is x; in the third one, A is F(x) id (y)G(y), a is x, b is y: in the fourth one. 
A is F{x) id (x)G{x), a is x, b  is y, in the last one, A  is F[xt y) ^  (z)G{x, z), a is x, 
and b  is y.
“ •The first one of the two is, however, a theorem, as we shall see later (exercise 34.3).

---


174
FUNCTIONAL CALCULI OF FIRST ORDER [Chap. Ill
primitive symbols we add the binary functional variables we have the binary 
functional calculus of first order, F1-2; and so on. A functional calculus of 
first order in which the primitive symbols include individual constants or 
functional constants or both is an applied functional calculus of first order, 
if no propositional variables and no functional variables are included, it is a 
simple applied functional calculus of first order (in this case there must be 
at least one functional constant).
This terminology will be useful to us later. But in this chapter we shall 
often not need to distinguish different functional calculi of first order by 
name, because, as already explained, we treat the various functional calculi 
of first order simultaneously by giving a development which holds equally 
for any one or all of them.
The intended principal in terp retatio n s of the functional calculi of first order 
m ay be roughly indicated by saying th a t propositional variables and sentence 
connectives are to have the sam e m eaning as in the propositional calculus, the 
universal quantifier, (V ), is to hav e the m eaning described in §06, and the func­
tional variables are to have propositional functions of individuals as values 
(e.g., the range of a singulary functional variable is the singulary functions from  
individuals to truth-values, an d  sim ilarly for binary functional variables, etc.). 
For application of a function to its argum ent or argum ents the notation described 
in §03 is used. F or the individuals, i.e,, the range of th e  individual variables, 
various choices m ay be m ade, so th a t various different principal interpretations 
result, Indeed if no individual or functional constants are am ong the prim itive 
symbols, it is usual to allow th e individuals to be any w ell-defined non-em pty 
class.80* B u t if there are individual or functional constants, th e intended in ter­
pretation of these m ay lead to restrictions upon or a special choice of the class 
of individuals.
W e illustrate by stating the sem antical rules explicitly in tw o cases, nam ely 
th a t of the pure functional calculus of first order, F lp, and th a t of a sim ple 
applied functional calculus of first order, F u , w hich has tw o ternary functional 
constants, £  and 77, and no o th er functional constants or individual constants 
am ong its prim itive symbols.
In  the case of F lp, some non-em pty class m ust first be chosen as the individuals, 
and there is th en  one principal in terpretation, as follows:
a. 
T he individual variables are variables having th e  individuals as their 
range.310 09
S09The term "individual" was introduced by Russell in connection with the theory 
of types, to be discussed below in Chapter VI. A rather special meaning was given to 
the term by Russell, the individuals being described as things "destitute of complexity" 
{Russell, 1908) or as objects which "are neither propositions nor functions" (Whitehead 
and Russell, 1910). But in the light of Russell's recognition th a t only relative types are 
actually relevant in any context, it is now usual to employ "individual" in the way 
described in the text. Cf. Carnap, Abriss der Logistik (1929), p. 19.

---


§30]
PRIMITIVE BASIS
175
b0. The propositional variables are variables having the range t and f. 
bx. 
The singulary functional variables are variables having as their range the 
singulary (propositional) functions from individuals to truth-values 310
b,. 
The binary functional variables are variables having as their range the 
binary propositional functions whose range is the ordered pairs of individuals.310
b„. The «-ary functional variables are variables having as their range the 
n-ary propositional functions whose range is the ordered w-tuples of individuals.310
c0. 
A wff consisting of a propositional variable a standing alone has the 
value t for the value t of a, and the value f for the value f of a.
c H. 
Let f(a1# a2, . . . , a„) be a wff in which f is an n-ary functional variable, 
and a1# aa, . . . , a„ are individual variables, not necessarily all different. Let 
b„ . . . , 
be the complete list of different individual variables among
alf a2J . . . , a*. Consider a system of values, b of f, and b u 6............  6n of
b|, b2, . . . , bm; and let au a3, , . . , a n be the values which are thus given to 
&!, a2, . . . , a„ in order. Then the value of f(ax, aa, . . . , an) for the system of 
values 6, blf ba, . . . , bm of f, b1( b x, . . . , bm (in that order) is b(aI( atl 
, a„).an
d. 
For a given system of values of the free variables of ~A, the value of ~A 
is f if the value of A is t; and the value of ~A is t if the value of A is f.313
e. 
For a given system of values of the free variables of [A zd B), the value of 
[A zd B] is t if either the value of B is t or the value of A is f; and the value of 
[A=>B] is f if the value of B is f and at the same time the value of A is t.
f. 
Let a be an individual variable and let A be any wff. For a given system 
of values of the free variables of {Va)A, the value of (Va)A is t if the value of A 
is t for every value of a; and the value of (Va)A is f if the value of A is f for at 
least one value of a.313
3l05inec the individual and functional variables have values as variables, it might 
therefore be thought more natural to consider them wffs when standing alone and to 
provide semantical rules giving them values as forms (as rule c0 does in the case of the 
propositional variables). Also a similar remark might be thought to apply to individual 
and functional constants in an applied functional calculus of first order. For the logistic 
system of Chapter X  we shall indeed follow this idea. But for the functional calculi of 
first (and higher) order it is practically more convenient not to call a formula wf which 
consists of an individual or functional variable or an individual or functional constant 
standing alone. In adopting this terminology for the functional calculi, we shall never­
theless regard the individual and functional variables and the individual and functional 
constants as proper symbols (cf. footnote 80) and as having meaning in isolation. And 
in particular we shall speak of the individual and functional constants as having deno­
tations—which are given by the semantical rules.
m The same notation for application of a function to its arguments that we have intro­
duced in the object language is here used also in the meta-language. We shall follow 
this practice generally, not considering it a violation of the next-to-last paragraph of 
§08. For a rare case in which this might lead to am biguity in connection with autonymy, 
we hold in reserve the possibility of an appropriate circumlocution to render the mean­
ing unmistakable.
ailThis and following rules are to be understood according to the conventions (intro­
duced in §10) that: (1) to have a value for a null class of variables is to denote; (2) the 
value of a constant for any system of values of any variables is the denotation of the 
constant; (3) the value of a form for any system of values of any variables which include 
t h e  fyee variables of the form is the same as the value of the form for the given values of 
the free variables of the form (values of other variables being ignored).
m Note should be taken of the following special cases of rule f and rule £, in accordance 
with the conventions referred to in footnote 312. If A contains the individual variable

---


176
FUNCTIONAL CALCULI OF FIRST ORDER [Chap. Ill
For convenience of reference we have here indicated an  infinite list of rules 
b0, b1( b s, . . . an d  an infinite list of rules c0, c1( ca, . . .. These m ay, however, be 
condensed in statem ent into ju st tw o rules, b and c.*u
In the case of F Ib, the individuals shall be the natural numbers, i.e., the positive 
integers and 0. There is one principal interpretation, as follows:
a„. The individual variables are variables having a  non-em pty range Q. 
«x. T he range & of the individual variables is the n a tu ra l num bers, 
ft. Each of £  and I I  denotes a tern ary  propositional function of the 
members of S.
ft. 
£  denotes the ternary propositional function of n atu ral num bers whose 
value, for any natural num bers av a g, a 3 as argum ents (in th a t order), is t  or f 
according as a s is or is not the sum  of ax and a t.
I I  denotes the ternary propositional function of n atu ral num bers whose 
value, for an y  natural num bers a x, a t, a9 as argum ents (in th a t order), is t or f 
according as a a is or is not the product of ax and a t.
y. 
L et f be a ternary functional constant denoting the propositional function 
b, and let a lf a*, a g be individual variables, not necessarily all different. Then 
the value of f(a 1( a a, a 8) for a system  of values of th e individual variables is 
b{ax, a%, a3), w here ax, a%1 a3 are th e  respective values of a1( atJ aB.
6. 
Identical in wording to rule d above,
e. 
Identical in wording to rule e above.
£. 
Identical in wording to rule f above.313
EXERCISES 30
3 0 .0 . E xpress the following proposition by a wf of F lh (taking the principal 
interpretation of F lh): For all natural num bers a, b, c, if a +  b «  c, th e n fr-f a = c .
3 0 » I• Sim ilarly, express in F lh: F o r all natural num bers a, bt either a ^  b 
or b ^  a. (An abbreviative definition should first be introduced to represent the 
relation 
say [a ^  b] 
(3c)2?(a, c, b) where a an d  b are any individual 
variables an d  c  is the first individual variable in alphabetic order w hich is not 
the same as either a or b.)
a as its sole free variable, then (Va) A denotes t if the value of A is t  for every value of a, 
and (Va)A denotes f if the value of A is f for at least one value of a. If A does not con­
tain the individual variable a as a free variable, the value of (Va)A is the same as the 
value of A, for any system of values of the free variables. If A contains no free variables, 
and if a is any individual variable, (Va)A has the same denotation as A.
IUI.e., in an appropriate semantical metalanguage the two infinite lists of rules may 
be reduced to two rules, as described. It is beyond the scope of our present treatm ent to 
undertake the detailed formalization (of the meta-language) which would be necessary 
to answer the question, what is an appropriate semantical meta-language for this pur­
pose. We remark, however, using a terminology to be explained in later chapters, that 
such a semantical meta-language might with the aid of certain artifices be based on an 
applied functional calculus of sufficiently high (finite) order, functional constants being 
introduced to represent certain syntactical and semantical notions and axioms (postu­
lates) added concerning them.

---


§301
EXERCISES 30
177
3 0 .2 . Similarly, express in F lh: if two n atu ral num bers have a  product equal 
to 0, th en  one of them  is equal to 0 . (A notation, say Z 0(a), should first be in tro ­
duced by abbreviative definition to represent the propositional function, equality 
to 0. Use m ay then be m ade of the wff (3s) - I7(x , y, z )Z Q(z) to express th a t two 
natural num bers [values of x and y] have a product equal to 0.)
30 .3. Similarly, find in F lh wffs expressing as nearly as possible each of the 
following: (1) A n atu ral num ber rem ains the sam e if it is m ultiplied b y  1. 
(2) T he sum  of tw o odd num bers is an even num ber. (3) For every prim e num ber 
there exists a greater prim e num ber; (4) T he one an d  only even prim e num ber is 
2, (5) For ail natural num bers a, b, and all n atu ra l num bers c except 0, if ac g  be, 
then a  ^  6; (6) For all n atu ral num bers a , b, (a - f  6 )* * — (a2 4- b2) 
2ab.
3 0 .4 . Consider an applied functional calculus of first order, F * \ w hich has the 
functional constants 27 and JI, w ith the sam e m eaning as in F lh, and in addition 
has all propositional an d  functional variables. The principal in terp retatio n  m ay 
be tak en  as obvious by analogy w ith those given for F 1^ and F lb. the individuals 
being again the n atu ral num bers. In this functional calculus of first order, 
express as nearly as possible, by m eans of a wff containing free functional varia­
bles, each of the following assertions: (1) In  an y  non-em pty class of natural 
num bers there is a  least nu m b er.815 (2) If a non-em pty class of n atu ral num bers 
contains no greatest n atu ra l num ber, then for an y  given n atural num ber it 
contains a greater n atu ral num ber. (3) T he relation <  between n atu ral num bers 
is characterized by the three conditions;516 th a t it holds betw een 0 and every 
n atural num ber; th a t it does not hold betw een an y  natural num ber oth er than 
0 and 0 ; and th a t (for all n a tu ra l num bers a and 6) it holds betw een a +  1 and 
b 4- 1 if and only if it holds betw een a and b. (4) F o r every natural num ber k, the 
Bum of th e odd num bers less th an  %k is k2. [Suggestion: Given a  class C of natural 
num bers, the relation betw een a n atural num ber k and the sum  of th e  natural 
num bers of C which are less th a n  k is characterized by the three conditions: th a t 
it holds betw een 0 and 0 ; th a t it does not hold betw een 0 and any n atu ra l num ber 
other th a n  0; and th at, for all natural num bers a and b, it holds betw een a +  1 
and b if and only if there is a natural num ber c such th a t it holds betw een a and 
c, and b is equal to  c +  a or c according as a does or does not belong to C.)
(5) P erfect num bers ex ist.817
3 0 . 5 . Taking the individuals to be the odd perfect num bers,317 let an  in ter­
p retation of F l*> be given b y  th e  sam e sem antical rules a-f as for a principal 
interpretation. (1) If th ere are odd perfect num bers, the in terp retatio n  is a 
principal interpretation; on this hypothesis, show  th a t the in terp retatio n  is 
Sound. (2) On the hypothesis th a t there are no odd perfect num bers, show th at 
the interpretation is unsound. (On the latter hypothesis, observe th a t a wff 
containing free individual variables m ust be said to have the value t for all
8UKecall that, according to §04, a class is the same thing as a singulary propositional 
function.
•llOr in other words, a relation between natural numbers is the relation :£ if and 
Only if it satisfies these three conditions.
,17A perfect number is a natural number, other than 0, which is equal to the sum of 
its aliquot parts, he,, to the sum of the natural numbers less than itself by which it is 
exactly divisible.

---


178
FUNCTIONAL CALCULI OF FIRST ORDER [Chap. Ill
system s of values of its free variables, an d  also to have the value f for all system s 
of values of its free variables; b u t it m ust not be said th a t it has the value f for 
a t least one system  of values of its free variables.)
3°.6. T he operator, or quantifier, w hich is introduced by  abbreviative def­
inition in D17 m ay  of course also be used as a prim itive (singulary-binary) 
quantifier in a form ulation of the functional calculus of first order. For a form u­
lation of the p ure functional calculus of first order in  w hich this is th e  only 
prim itive sentence connective or quantifier, state the form ation rules; sta te  the 
sem antical rules for a principal in terp retatio n ; and supply definitions of the 
universal quantifier, im plication, an d  negation w hich will provide the appro­
priate agreem ent in m eaning of the kind explained in the sem antical paragraphs 
a t the end of §11.
3°-7- The intended principal in terp re tatio n  of the extended propositional cal­
culus (in the sense of §28) is inform ally indicated by th e  sem antical discussion 
in §§04-06, 28. F o r a form ulation of th e extended propositional calculus in which 
im plication is the one prim itive sentence connective, and th e  universal quantifier 
is the one prim itive quantifier, sta te  th e  form ation rules; an d  sta te  the sem anti­
cal rules for the principal in terp retatio n .
30.8. The intended principal in terp re tatio n  of protothetic (in the sense of §28) 
is inform ally indicated by the sem antical discussion in §§04-06, 28. For a  for­
m ulation of p ro to th etic in w hich equivalence is the one prim itive sentence 
connective, an d  th e universal quantifier is the one prim itive quantifier (which 
takes, however, either a propositional variable or a truth-functional variable as 
operator variable), state the form ation rules; sta te  the sem antical rules for the 
principal in terp retatio n ; and supply definitions of im plication an d  negation 
which will provide the appropriate agreem ent in m eaning.
31. Propositional calculus. If the primitive symbols of F1 include 
the propositional variables, then every theorem of the propositional calculus, 
in implication and negation as primitive connectives, is a theorem also of 
F1—as follows immediately from the results of §27, because the axioms of 
the system P of §27 are included among the axioms of F1 (in *302, *303, and 
*304) and the one rule of inference of P is a rule of inference also of F1.
Even if the propositional variables are not included among the primitive 
symbols of F1, we may draw a similar conclusion regarding substitution 
instances of theorems of the propositional calculus.
By a substitution instance of a wff A of any formulation of the propositional 
calculus we mean, namely, an expression or formula
A |.
where blt ba, . . 
bn is the complete list of (distinct) propositional vari­
ables of A, and Bt( B2, . .
Bn are any wffs of the logistic system under 
consideration in the particular context, in this chapter, the logistic system F1.

---


§31]
PROPOSITIONAL CALCULUS
179
It is clear, then, that a substitution instance of a wff of P is a wff of F1. 
Moreover, a substitution instance
C b , bj.-.bn A|
of a theorem A of P must be a theorem of F1. For every substitution instance 
of an axiom of P is an axiom of F1 (by *302-*304). And if a proof is given of 
A as a theorem of P, let bx, b2, . .., b„, cv c2, . .  ., cm be the complete list 
of (distinct) propositional variables occurring, choose arbitrary wffs 
Cn C2, . . 
Cm of F1, and substitute simultaneously 
for bx, B2 for b2, . . 
Bn for bnt Ct for ct, C2 for c2, , . ., Cm for cm throughout the given proof. 
The result of this substitution is a proof of
s
b
B, A|
as a theorem of F1—valid applications of the rule of modus ponens in P 
being transformed by the substitution into valid applications of the rule of 
modus ponens in Fl.
Since we know (by **235, *239, *270, **271) that the theorems of P are 
the same as the tautologies of P (in the sense of §15), we may, without loss, 
put the foregoing results in the following form;
*310. 
Every tautology of P is theorem of F1 if it is a wff of F1.
*311. 
Every substitution instance of a tautology of P is a theorem of F1.
In the foregoing, the arbitrary choice of the wffs Cv C2, . . 
Cm is easily 
replaced by a definite rule for their choice. For example, since n >  0, we 
might just make each of the wffs Cx, C2, . . 
Cm identical with B^ Thus the 
proof of *311 becomes effective, in the sense of §12, so that *311 (as well as 
*310) may be employed as a derived rule of inference.
The use of *311 as a derived rule is facilitated by the fact that there is an 
effective procedure to determine whether a given wff of F1 is or is not a 
substitution instance of a tautology of P—and to find a tautology of P of 
which it is a substitution instance, in case there is one. Details of this are 
now left to the reader. We shall rely on it in order to set down, whenever 
required, a wff of F1 as a substitution instance of a tautology of P, and to 
leave it to the reader to verify it as such.
We shall often make use of *311 as a derived rule of inference in this way. 
And ordinarily, as sufficient indication of such use of *311, either alone or 
followed by one or more applications of modus ponens, we shall write simply 
the words, “by P," or “use P /' or the like.

---


180
F U N C T I O N A L  C A L C U L I  O F  F I R S T  O R D E R  [Chap. I l l
We add here, for reference, the five following metatheorems:
**312 Every wff is of one and only one of the five following forms, and 
in each case it is of that forfn in one and only one way: a proposi­
tional variable standing alone; f(alf a3, . .
an), where f is anw-ary 
functional variable or «-ary functional constant and a1( aa, . . an 
are individual variables or individual constants or both; ~A; 
[Az^B]; (Va)A, where a is an individual variable.
**313. 
A wf part of ~A either coincides with ~A or is a wf part of A.
**314. 
A wf part of [A zd B] either coincides with [A zd B] or is a wf part 
of A or is a wf part of B.
**315. 
A wf part of (Va) A either coincides with (Va) A or is a wf part of A.
**316. 
If r  results from A by substitution of N for M at zero or more 
places (not necessarily at all occurrences of M in A), then T is wf.
These metatheorems are used in particular in the proof of **323, of *340, 
and of **390, below. Their proofs are analogous to those of **225-**228, 
and are left to the reader. 32
32. Consistency of F1. A wff of F1 is called q u a n tifie r-fre e  if it contains 
no quantifiers—or, what comes to the same thing, if it contains no occur­
rence of the symbol V. From any wff of F1 we obtain its a sso c ia te d  q u a n tifie r- 
free fo rm u la  (also wf) by deleting all occurrences of the universal quantifier 
—i.e„ by deleting the four symbols (Va), at every place where such four 
symbols occur consecutively.
From a wff of F1 we obtain an a sso c ia te d  fo rm u la  of the p r o p o s itio n a l ca l­
cu lu s (abbreviated “afp") by first forming the associated quantifier-free 
formula, and then, in the latter, replacing every wf part f(alf aa, . . an) by 
a propositional variable not previously occurring, in accordance with the 
following rule: two wf parts f(a1( aa, . . 
an) and g(bx, ba>. . 
bOT) are re­
placed by the same propositional variable if and only if f and g are the same 
functional variable or functional constant (as, of course, can happen only 
when m  — n ).
For example, in F*p, the wff G(a;) z>v H{y) zd . G(a;) zd (y)H(y) has as its 
associated quantifier-free formula G(x) zd H{y) zd « G(a:) z d H(y), and thus an 
afpis^ zd ? zd mp  zd q. The wff F(x, y) z d x [z)G(z, z) =>. F(y,y) => (z)G(y, *) 
has as its associated quantifier-free formula F{x, y) zd G{x, z) ZD • F[y, y ) 
zd G(y, z ), and therefore again an afp is 
mp'ZD q.

---


§32]
CONSISTENCY
181
Clearly, all the afps of a given wff of Fl are variants of one another in the 
sense of §13. Hence, if one of the afps of a given wff of F1 is a tautology, all 
of them are.
Now it is easily verified that every afp of an axiom of F1 is a tautology. 
In fact for any instance A d  ■ B d  A of axiom schema *302, an afp must 
have the form A0 zd . B0 zd A0, where A0and B0 are afps of A and B respec­
tively; and ^
3
»B0 3  A0 must be a tautology, because it is obtainable by 
substitution from the tautology p  ZD , q  ZD p . Similarly, afps of instances of 
axiom schemata *303-*305 must have, in order, the forms:
Aq ZD [B0 ZD C0] ZD rn A q zd B0 zd . A0 zd C0 
~ A q mmJ ~ B 0 ZD • B q 
A q
A0 
Bq zd . A0 => B0
And each of these is obviously a tautology because obtainable by substitu­
tion from a known tautology. In the case of *306, A and
S£A|
differ (if at all) only by the substitution of one individual variable or con­
stant for another, and therefore they must have the same afp A0. It follows 
that an afp of an instance of axiom schema *306 must have the form A0 ZD A0, 
which is obviously a tautology because obtainable by substitution from the 
known tautology £ 
p .
Moreover, the rules of inference of F1 preserve the property of having a 
tautology as afp, i.e., if the premiss or premisses of the rule have this prop­
erty, then the conclusion does also. In the case of *301, this is immediate. 
In the case of *300, we must make use of the remark that, if one afp of a 
wff is a tautology, then all are. Let A0 
B0 be an afp of the major premiss 
A = )B . Then A0 and B0 are afps of A and B respectively. Since A0 and 
AoD B o are tautologies, it follows that B0 is a tautology, in consequence of 
the4 truth-table of z d (compare the proof of **150).
Since the axioms all have the property of having a tautology as afp, and 
since the rules of inference preserve this property, there follows the meta­
theorem:
**320. 
Every theorem of F1 has a tautology as afp.
Now it is clear that if a wff A has a tautology as afp, its negation ~A  has 
as afp, not a tautology but a contradiction. Hence by **320, not both A

---


and ~Acan be theorems. Thus we have the consistency of F1 in the following 
senses:818
**321. 
F1 is consistent with respect to the transformation of A into ~A. 
**322. 
F1 is absolutely consistent.
This proof of the consistency of Fl differs from our proof of consistency 
of the propositional calculus (§17) in that it is not associated in the same 
way with a solution of the decision problem. In fact the converse of * **320 
fails, as we go on to show by giving an example of a non-theorem which 
has a tautology as afp. For this purpose we first establish the two following 
metatheorems:
**323. 
For every quantifier-free theorem of F1 there is a proof in which 
only quantifier-free formulas occur.
Proof. Let any proof be given of a quantifier-free formula C, and let 
clf c2, . . 
cn be the complete list of individual variables and individual 
constants occurring in the proof. Then replace every wff B occurring in 
the proof (i.e., occurring as one of the finite sequence of wffs which consti­
tutes the proof) by a quantifier-free formula BJ, according to the following 
procedure.
Choose individual variables blt b2, . . 
bn which are distinct among 
themselves and distinct from all of cv c2, . . cn; and throughout the wff B 
substitute b1( b2, . . 
bn for c1( c2, . . 
cn respectively. In the resulting wff 
B', a wf part (Vbr)A is to be replaced by the conjunction AxAa . . . An, 
where A* is
S ^ A |
(i =  1 ,2 ,..., n). If there is more than one wf part of B' of the form (Vbr)A, 
then the stated replacement is to be made first for one of the wf parts
182 
FUNCTIONAL CALCULI OF FIRST ORDER [Ch a p. Ill
31*If propositional variables are among the primitive symbols, it follows by the same 
methods that F1 is consistent in the sense of Post.
(A d d e d  %n  p ro o f.) The demonstration of consistency is here made in a form which 
could be applied also, with obvious modifications, to a formulation such as F |p (see §40) 
having a rule of substitution for functional variables as a primitive rule. However, 
as pointed out to me by John G. Kemeny, the argument leading up to **321 and
•*322 in the present section could be greatly simplified by using a more simply 
defined associated formula in the propositional calculus. Namely let the sin g u la ry  
associated fo r m u la  o f the p ro p o sitio n a l c a lc u lu s (abbreviated "sfp") be obtained from 
the associated quantifier-free formula of any wff of F* by replacing every elementary 
part bv the one propositional variable p . — It follows from this that, e.g., F(«) 3  G( y)  
could be added as an axiom to Flp without producing inconsistency, but could not be 
so added to FJp,

---


§32]
CONSISTENCY
183
(Vbr)A in which A is quantifier-free (obviously there must be one such); 
then in the resulting wff another wf part (Vbr)A is to be chosen in which 
A is quantifier-free, and the stated replacement is to be made again; and so 
on, the successive replacements being continued until B' has become a 
quantifier-free formula Bf. Then B | is to be the conjunction (in some 
specified order) of all the nn wffs
C b jb t ...b„Bf I
where dv d2, . . 
dn are any among the variables and constants cl( c2, . . c„, 
taken in any order, and not necessarily all different.
If B is an axiom, then BJ is a substitution instance of a tautology (of P) 
as the reader may verify by considering separately each of the schemata 
*302~*306. By *311, B£ is therefore a theorem of Fl, and in fact the method 
which we used in establishing *311 provides without difficulty a proof of 
B* in which only quantifier-free formulas occur.
If, in the given proof of C, B is inferred by *300 from premisses A d
B 
and A, then A$ is the conjunction of the nn wffs
S S & l ’ A f |,
and [A zd 
is the conjunction of the «n wffs
SSfti&At i zd S$ft:;:$;Bt i;
and therefore it is possible by a series of steps involving methods of the prop­
ositional calculus only (cf. §31) to infer each of the nn wffs
from [A ro B ]f and A$; and therefore by further steps involving propo­
sitional calculus only it is possible to infer B$. Specifically, what is needed 
is proofs of two substitution instances each, of the nn tautologies,
P iP t •••/>«"=> P i 
(* = 1 , 2 , . . . ,  n"),
and proof of an appropriate substitution instance of the tautology,
Pi ^
 
■ P2 ^
 
■ ■ 
-  
* Pnn~l ^
 
■ Pnn 
^
 P\P% • 
* 
• Pnn>
and a number of applications of modus ponens. By the method used in the 
demonstration of *311, all of this can be accomplished without use of other 
than quantifier-free formulas.
If, in the given proof of C, B is inferred from premiss A by generalizing 
upon the individual variable cT (thus by *301), then B+ is the conjunction 
of the n wffs

---


184
FUNCTIONAL CALCULI OF FIRST ORDER [Ch a p. Ill
Sc'At !
(i — 1,2, .. 
n), and A$ is the conjunction of the nn wffs
C b Aba...bn a a | 
d n ^ T  I-
Thus
At => SSj5j::S;Bt i
is a substitution instance of a tautology
PiPz • • • Pn* => PsJ>j% • ■ -Pin
(where the subscripts jv j2, , . 
jn are a certain n different ones among the 
subscripts 1 , 2 , . .  
nn), and therefore is a theorem of F1 by *311. Hence 
from AJ we may infer by modus ponens each of the wffs
C b ,b jt...bng 4 . i
’-5d 1d a...df, 
T li
and hence finally by a suitable substitution instance of the tautology 
PlZD mp,l 'Z> m . . . pnn 
P\P^ . . . £n«
and modus ponens we may infer BJ. Again by the method used in the dem­
onstration of *311, this can all be accomplished without use of other than 
quantifier-free formulas.
To sum up, we have now shown how the given proof of C can be trans­
formed into a proof of C$ in which only quantifier-free formulas occur. 
But by hypothesis C is quantifier-free. Therefore Cf is
SC,Co...C„ p i
and C$ is a conjunction of wffs one of which is C. By a further application 
of propositional calculus we can therefore go on to prove C, and by the 
method of *311 this can be done still without use of other than quantifier- 
free formulas.
**324. 
Every quantifier-free theorem of F1 is a substitution instance of a 
tautology of P.
Proof. Given a quantifier-free theorem C of Fl we can find, by **323, 
proof of C in which only quantifier-free formulas occur. In this proof of C, 
the only axioms used must be instances of the schemata *302, *303, *304, 
and therefore substitution instances of axioms of P; and the only rule of 
inference used must be modus ponens. Thus we have for each successive 
wff in the proof of C, as it is obtained, that it is a substitution instance of a 
theorem of P. Ultimately we have that C is a substitution instance of a 
theorem of P, and therefore a substitution instance of a tautology of P.

---


§32]
CONSISTENCY
185
We remark, in passing, that from **324 we have a new proof of the con­
sistency of F1. Indeed the absolute consistency of F1 follows from **324 upon 
giving one example of a quantifier-free formula which is not a substitution 
instance of a tautology. And the consistency of F1 with respect to the trans­
formation of A  into ~ A  then follows because, by *311 and the law of denial 
of the antecedent
~P zd - p z=> q,
if A  and 
were both theorems in any instance, then every wff would be 
a theorem. (This proof of the consistency of F1 again is not associated with 
any general solution of the decision problem of F1, but it does involve a 
solution of the decision problem for the special case of quantifier-free for­
mulas.)
Nowin particular, F(a;) zd F(y) is a quantifier-free formula of F*p which 
is not a substitution instance of a tautology, therefore it is a non-theorem, 
although it has a tautology as afp. Or, more generally, if f is an »~ary func­
tional variable or an w-ary functional constant, and if ax, a2, . . 
a„,
b1# b2, . . 
bfl are individual variables or individual constants, then
f(ax, a 2, . . 
an) n> f(bXJ b2, . . 
b n)
has a tautology as afp, but is not a theorem of F1 unless ax, a2, . . ., an are 
in order the same as bx, b2, . . 
bn.
The proof of **320 makes use of no property of the axioms of F1 except 
that every axiom has a tautology as afp. In consequence, the addition to F1 
of another axiom having a tautology as afp would not alter the property of 
the system that every theorem has a tautology as afp, and therefore would 
not destroy the consistency of the system. It follows that F1 is not complete 
in any of the senses of §18, and especially:
**325. 
F1 is not complete with respect to the transformation of A  into - A ,  
and is not absolutely complete.
However, in §44 we shall prove a completeness theorem for Fjp, and for 
the equivalent system Fgp, establishing their completeness in a weaker sense.
An explanation of the incom pleteness of F*p m ay  quickly be seen from  the 
point of view  of the in terp retatio n . The wff F(a*) 
F ( y ) ,  for exam ple, has the
value t for all values of its free variables, in the case of a principal in terp retatio n  
in which th ere is just one individual; also, regardless of th e  num ber of individuals, 
in an in terp retatio n  w hich is like a principal in terp retatio n  except th a t th e range 
of som e or all of the singulary functional variables, including the variable F ,  
is restricted to two particular singulary propositional functions of individuals,

---


186
FUNCTIONAL CALCULI OF FIRST ORDER [Ch a p. I l l
namely, the propositional function whose value is t for all arguments and the 
propositional function whose value is f for all arguments. (An interpretation of 
this latter kind, though not principal, is sound, as may readily be verified.) If 
only such interpretations as these were contemplated, it would be natural to 
expect F(x) rs F(y) as a theorem, and to add it as an axiom if it were not other­
wise a theorem. But in other principal interpretations of F*p, in which the num­
ber of individuals is greater than one, F{») za F(y) does not have the value t 
for all values of its free variables and therefore, for the sake of the soundness 
of the interpretation, must not be a theorem.
The completeness theorem of §44 will mean, semantically, that all those wffs of 
Fu> are theorems which have, in every principal interpretation, the value t for all 
values of their free variables. Hence the theorems of any functional calculus of 
first order may be described by saying that they are the wffs which, under the 
intended way of interpreting the connectives and quantifier, are true (1) for 
all values of the free variables, (2) regardless of the denotations assigned to the 
constants, and (3) independently of the nature and number of the individuals— 
provided only that there are individuals, that the values of the individual 
variables and the denotations of the individual constants are restricted to be 
individuals, that the values of the propositional variables are restricted to 
truth-values, and that the values of the «-ary functional variables and the de­
notations of the n-ary functional constants are restricted to be n-ary proposi­
tional functions of individuals.
33. Som e theorem  schem ata of F1, A theorem schema is a syntactical 
expression which represents many theorems (commonly an infinite number 
of different theorems) of a logistic system, in the same way that an axiom 
schema represents many different axioms. In the treatment of F1 we shall 
deal with theorem schemata rather than with particular theorems, and shall 
supply for each theorem schema, by means of a schema of proof, an effective 
demonstration that each particular theorem which it represents can be 
proved. As in the case of derived rules of inference (discussed in Chapter I), 
justification of this lies in the effectiveness of the demonstration, whereby 
for any particular theorem represented by a given theorem schema the 
particular proof can always be supplied on demand. Thus our procedure 
amounts not to an actual formal development of the system F1 but rather 
to giving effective instructions which might guide such an actual develop­
ment. It is important to remember that the theorem schemata are in fact 
syntactical theorems about F \ and only their instances, the particular 
theorems which they represent, are the theorems of F1,
*330. 
h §£A| id (3a)A, where a is an individual variable, b is an individual 
variable or an individual constant, and no free occurrence of a in A 
is in a wf part of A of the form (b)C.

---


§33]
S O M E  T H E O R E M  S C H E M A T A
187
Proof. By *306, b (a)~A 3  ~S“A[.
Hence by P,319 I- $£Aj 3  ~(a)~A.320
*331. 
b (a) A zd (3a) A.321
Proof. By *306, b (a) A 3  A.322
By *330, I- A ;d (3a)A.323
Then use the transitive law of implication.324
*332. 
b A :Da B d> . (a)A => B.
Proo/. By *306, b A =>a B d . A d  B .325 
Also by *306, b (a)A do A.326 
Then use P.32fl
*333. 
b A =>a B zd m (a)A id (a)B.
Proof. By *332 and generalization,327 b A=>a B zdb . (a)A zd B. 
Hence by *305, b A ZDa B d , (a)A zDa B.338 
By *305, b (a)A :Da B do . (a)A 3  (a)B.
Then use the transitive law of implication.324
*334, 
b A ==a B zd . (a)A == (a)B.
Proof. By P, b A = B D . A 3 B ,
,l,For explanation of the phrase "by P '1 (i.e., by propositional calculus) see the 
explanation which follows *311 in §31.
•“This final expression is identical with *330, the theorem schema to be proved 
(cf. D14). In such cases we shall not refer explicitly to the definitions or definition sche­
mata involved but shall merely leave it to the reader to see that the proof is complete.
*tlThe condition that a shall be an individual variable may be taken as obvious, since 
the formula would not otherwise be wf. We shall hereafter, in stating theorem schemata, 
systematically omit explicit statement of such conditions when obvious for this reason.
•“ This special case of *306 in which b is the same variable as a will be used frequently. 
In particular (by modus ponens) it provides the inverse of the rule of generalization, as 
a derived rule; and we shall later have occasion to use it in this way also.
•“ This is- the special case of *330, in which b is the same variable as a.
•“ Such a reference to a particular tautology of P by name will be employed as a more 
explicit substitute for the words "by P” or "then use P", thus as including a reference 
to *311 (cf. footnote 319).
•“Compare footnote 322.
•“ See the explanation in §31.
" TI.e., with *332 as premiss, the rule of inference *301 is applied.
•“More explicitly, we take as major premiss
A 
B z>a l(a)A 3  B] 3  . A Dfl B D . (ft) A :=)fl B, 
which is an instance of *305, and use modus ponens.

---


188
F U N C T I O N A L  C A L C U L I  O F  F I R S T  O R D E R  [Chap. I l l
Hence by generalization and *333,329 1- A = a B 3  . A 3 a B. 
Hence by *333 and the transitive law of implication,
F A S j B d , (a)A 3  (a)B.
Again, by P, h A =  B 3  . B 3  A.
And hence by a similar series of steps, b A = a B 3  . (a)B 3  (a)A. 
Then use P.
*335, 
b A 3  (a)B s  . A 3 a B, if a is not free in A.
Proof. By *306, b (a)B 3  B.
Hence by P, b A 3  (a)B 3  ■ A 3  B.
Hence by generalization and *305, b A 3  (a)B 3  . A 3 a B.
Then use *305 and P.
*336. 
b (a )(b )A s  (b)(a)A.
Proof. By *306, b (b)A 3  A.
Hence by generalization and *333, b (a)(b )A 3  (a)A.
Hence by generalization and *305, b (a )(b )A 3  (b)(a)A. 
Similarly, b (b)(a)A 3  (a)(b)A.
Then use P.
*337. 
b (a)A =  A, if a is not free in A.
Proof. By P, b A 3  A.
Hence by generalization and *305, b A 3  (a)A.
By *306, b (a)A 3  A.
Then use P.
*338. 
b~(3a)A  == (a)~A.
Proof. By P, b ^ j a ) 4 s  (a)~A.
*339. 
b (a) A =  (b)B, if there is no free occurrence of b in A, and no free 
occurrence of a in A is in a wf part of A of the form (b)C, and B is
s; a i.
Proof. By *306, b (a) A 3  B. Hence, by generalizing upon b and then
as#I.e., more explicitly, wc take
A s B s . A a B
as premiss, and generalize upon a (*301); then wc take the resulting wff as minor 
premiss, and an appropriate instance of *333 as major premiss, and use modus ponens.

---


m
S U B S T I T U T I V I T Y  O F  E Q U I V A L E N C E
189
using *305, we have that F (a)A 3  (b)B. Now the given relation between 
the wffs (a)A and (b)B is reciprocal, i.c., there is no free occurrence of a in 
B, and no free occurrence of b in B is in a wf part of B of the form (a)D, 
and A is SaB|. Therefore in the same way we have that F (b)B 3  (a)A. 
Therefore by P, F (a )A =  (b)B.
34. Substitutivity of equivalence. In this section we establish the 
rule of substitutivity of equivalence (*342) and some related derived rules of 
inference. (Compare *158, *159, 15.3 in the propositional calculus.)
*340. 
If B results from A by substitution of N for M at zero or more places 
(not necessarily at all occurrences of M in A), and if ai( a2, . . 
an 
is a list of individual variables including at least those free variables 
of M and N which occur also as bound variables of A, then 
F Ms *  
0 N d , A = B ,
P r o o f. In a manner analogous to that of the proof of *229, we proceed by 
mathematical induction with respect to the total number of occurrences 
of the symbols 
V in  A.
We consider first the two special cases, (a) that the substitution of N 
for M is at zero places in A, and (b) that M coincides with A and the sub­
stitution of N for M is at this one place in A. In case (a), B is the same as 
A, and therefore F M = ttja8_afi N ^  . A =  B by P. In case (b), A and B 
are the same as M and N respectively, and therefore by n  uses of *306,330 
and the transitive law of implication, F M = a a a N ^ . A ™B .
Now if the total number of occurrences of the symbols zd, 
V in A is 0,
we must have one of the special cases (a), (b), and the result of *340 then 
follows quickly, as we have just seen. Consider then a wff A in which this 
total number is greater than 0; the possible cases are the three following:
Case 1: A is of the form A x :z> A2. Then (unless we have the special case 
(b) already considered) B is of the form Bx 3  B2, where 
and B2 result 
from A2 and A2, respectively, by substitution of N for M at zero or more 
places. By hypothesis of induction,
M  =
a,a!...a„N  => ■ A , =  B j,
I" M = a,a,...a„N => • A2 =  B2.
Hence we get the result of *340 by P, using an appropriate substitution 
instance of the tautology,
*30Again this is the special case ol *300 in which a and b are the same variable.

---


190
F U N C T I O N A L  C A L C U L I  O F  F I R S T  O R D E R  [Chap. I l l
Case 2: A is of the form ~AX. Then (unless we have the special case (b) 
already considered) B is of the form 
where Bx results from Ax by sub­
stitution of N  for M at zero or more places. By hypothesis of induction,
1-M s a.a
N d . A j s Bj.
Hence we get the result of *340 by P, using an appropriate substitution in­
stance of the tautology,
[ ^
D
. y
s
r ] D
. ^
3
. ^
f S
<
Case 3: A is of the form (a)Alt Then (unless we have the special case (b) 
already considered) B is of the form (a)B1, where Bx results from Ax by 
substitution of N for M at zero or more places. By hypothesis of induction,
bM
N =>. A» s  Bj.
Hence by generalizing upon a and then using *305,331 we have that
bM== aja^.a, N ro . Ax 
Bj.
Hence we get the result of *340 by using *334 and the transitive law of 
implication.
Thus the proof of *340 by mathematical induction is complete.
The two remaining metatheorems of this section follow as corollaries:
*341. 
If B results from A by substitution of N  for M at zero or more 
places (not necessarily at all occurrences of M in A), and if b M — N, 
then FA =  B.
Proof. By *340, *301, and *300.
*342. 
If B results from A by substitution of N  for M at zero or more places 
(not necessarily at all occurrences of M in A), if 1M  =  N  and 
b A, then b B. 
(Rule of substitidivity of {material) equivalence.)
Proof. By *341 and P.
m At this step it is essential that a is not a free variable of
This is secured by the hypothesis th at among a1( a* . . , , a„ are all the free variables 
of M and N which have bound occurrences in A.

---


§35]
D E R I V E D  R U L E S  O F  S U B S T I T U T I O N
191
EXERCISES 34
34.0. 
With aid of the results of §32, show that the following are non- 
theorems of F^:
Show that any proof of a wff (a) A as a theorem of F1 must contain 
an application of the rule of generalization (*301) in which the variable 
that is generalized upon is a.332
3 4 . 
Z. In *340, to what extent may the hypothesis be weakened that 
among a*, a2, . . ., art are all the free individual variables of M and N 
which occur as bound variables in A?
Establish the following theorem schemata of F1, using methods and results of 
§§30-34, but not those of any later section:
34-3- The theorem schema of which (x)(y)F(x, y) 
{y)F(y} y) is a basic 
instance.
34 .4 . t- B d „ A d  . (3a)B 3  A, if a is not free in A.
3 4 .5 . I-Ad ^
d , (3a)A 3  (3a)B.
34 .6 . l - A = a B D ,  (3a) A =  (3a)B.
35. Derived rules of substitution. By taking advantage of the device 
of axiom schemata, as discussed in §27, we have formulated the system F1 
without use of rules of substitution as primitive rules of inference. And 
indeed this way of doing it seems to be the only possibility in the case of a 
simple applied functional calculus of first order. But if there is a sufficient 
apparatus of variables, an alternative formulation is possible in which there 
are primitive rules of substitution (in addition to the rules of modus ponens 
and generalization) and the number of axioms is finite—as we shall see in 
§40.
In this section, the rules of substitution in question are obtained as derived 
rules of Fl. In doing this no distinction need be made of different kinds of 
functional calculi of first order, as the rules in fact all hold even in the case 
of a simple applied functional calculus of first order. But in a case in which 
variables of a particular kind are not present, of course a rule of substitution 
for variables of this kind reduces to something trivial.
*MIn consequence of the metatheorem of this exercise, the treatment of the deduction 
theorem for F1 is unsound as it appears in Chapter II of the 1944 edition of Introduction 
to Mathematical Logic, Pari I. An amended treatm ent of the deduction theorem appears 
in §36 below.
(1) 
F(x) :dxG{x) =3 (3a;) . F{x)G(x)
(2) 
(3a;) F{x) =3 (a:) F(x)
(3) 
F(x) =>* . F(y) =>„ [G(x) => G(y)} V (*)F(*)

---


192
F U N C T I O N A L  C A L C U L I  O F F I R S T  O R D E R  [Chap. I l l
*350. 
If a is an individual variable which is not free in N and b is an 
individual variable which does not occur in N, if B results from A 
by substituting S£N| for a particular occurrence of N in A, if 1- A, 
then b B.
[Rule of alphabetic change of bound {individual) variable.)
Proof. By *339 and *342 (the various wf parts of N of the form (a)A< 
being taken one by one in left-to-right order of their initial symbols).
*351. 
If a is an individual variable and b is an individual variable or an 
individual constant, if no free occurrence of a in A is in a wf part of 
A of the form (b)C, if b A, then b${JA!.
{Rule of substitution for individual variables.)
Proof. By *301 and *306.
In order to state rules of substitution for propositional and functional 
variables we introduce a new substitution notation for which we use the 
letter S.
If p is a propositional variable, the notation
§ b A|
shall stand for333 A unless the condition is satisfied that (1) no wf part of A 
of the form (b)C, where b is a free variable of B, contains a free334 occurrence 
of p; and, if this condition is satisfied, it shall stand for333
5b a|.
If f is an w-ary functional variable and xx, x 2, . . 
x n are distinct indi­
vidual variables, the notation
shall stand for 335 A unless the two conditions are satisfied that: (1) no wf 
part of A of the form (b)C, where b is a free variable of B other than 
x1( x 2, .. 
x n> contains a free336 occurrence of f; and (2) for each ordered
for any particular propositional variable p and any particular wffs A and B, 
the syntactical notation in question denotes the wff A if the condition (1) is not satis­
fied, and, if the condition (I) is satisfied, it denotes the wff which results by substituting 
B for all free occurrences p in A.
M4In connection with F1 the word "free" here is superfluous. It is included because 
we shall wish to use the same substitution notation also in connection with other systems 
(without changing the wording of the definition).
S35Compare footnote 333.
m The restriction to free occurrences of f is superfluous in connection with F1, be­
cause in a wff of F1 every occurrence of f is a free occurrence. As before, the restriction 
is included for the sake of use of the same notation in connection with other logistic 
systems.

---


§35]
D E R I V E D  R U L E S  O F  S U B S T I T U T I O N
193
n-tuple a1( a2, . . 
an of individual variables or individual constants (or 
both, not necessarily all distinct) for which 
a2, . . 
an) occurs in A in 
such a way that the occurrence of f is a free occurrence,335 the wf parts of B, 
if any, that have the forms (aJC, (a2)C, . . 
(an)C contain no free occur­
rences of x 1( x2, . . ., x„ respectively.337 And, if these two conditions are 
satisfied, the notation shall stand for335 the result of replacing f(alf a2,
. . 
at all of its occurrences in A at which f is free,335 by
•aiaa,,,a» 1
this replacement to be carried out simultaneously for all ordered w-tuples 
a1( a2, . . ., an of individual variables or individual constants (or both, not 
necessarily all distinct) such that f(alf a2, . . 
an) has an occurrence in A 
at which f is free.
*3520. 
If p is a propositional variable, if I- A, then
h §&A|.
(Rule of substitution for propositional variables.)
*352„. 
If f is an w-ary functional variable and x1( x 2, . . 
x n are distinct 
individual variables, if h A, then
I- 5£x>’x..... X->A|.
(Rule of substitution for n-ary functional variables.)
Proof. The proof of *3520, *352n is analogous to that of **271.
We make use of a wff B ; which differs from B by alphabetic changes of 
the bound and free individual variables of B in such manner that: (i) the 
individual variables occurring in B' are none of them the same as individual 
variables occurring anywhere in the given proof of A; and (ii) the same 
variable occurs at two places in B' if and only if the variables occurring at 
the two corresponding places in B are the same. Let y, (i — 1, 2, . . 
n) 
be the variable which occurs in B' in place of the variable x, in B; or if 
x,- does not occur in B, choose y* to be an individual variable not occurring 
otherwise.
We'observe that, if E is any axiom occuring in the given proof of A, then
or 
Sf^ ' y..... y->Ei
(as the case may be) is again an axiom.
w In other words, to satisfy condition (2), if 
a#I . . . , a ft) has an occurrence in 
A at which f is free, and (a JC  is a wf part of B, then (a^C shall contain no free occur­
rence of xx; if f(a„ a2, . . . , a*) has an occurrence in A at which f is free, and (aa)G is 
a wf part of B, then (af)C shall contain no free occurrence of xg; and so on.

---


194
FUNCTIONAL CALCULI OF FIRST ORDER [Ch a p. Ill
Moreover, in any application of the rule of modus fattens in the given 
proof of A, let the premisses and conclusion be G s D ,  C, D, Then
$ * C = > D |, 
§J.C |. 
$ b«D|
or
(as the case m ay be) are also premisses and conclusion for an application of 
the rule of modus ponens.m
Again, in any application of the rule of generalization in the given proof 
of A. let the premiss and conclusion be G, (b)G, Then
Of
are also premiss and conclusion for an application of the rule of generali­
zation.339
If, therefore, in the given proof,
Aj, A2, • . 
Api,
of A we replace each wff A* (i =  1 , 2 , . . . ,  m) by
S '.A ,| 
or 
S S '" * .....'■’A.l,
we obtain a proof of
SJ,A , 
or 
§ ,<r>’y- - ' y",A|
(as the case m ay be).
In order to obtain the required proof of the wff
§ ba I 
or 
Sg*!'*»....X*>A|
(unless this is the same wff as A, in which case the m atter is trivial) we use 
the proof just found of
§B'Ai 
or 
S « r -y’.....y,)A|
and add to it a series of steps in which the required alphabetic changes of
***The reason for introducing the wff B ' m ay be seen in this paragraph of the proof. 
Namely, it is necessary to employ B ' instead of B for substitution in C and C d D, 
because of the possibility that the numbered conditions, (l), or (1) and (2), though 
holding for the §-substitution of B in D m ay fail for the §-substitution of B  in C and 
in G 3  0 .
**• Again in this paragraph of the proof the necessity of employing B ' instead of B 
is seen, because of the possibility that b might be a free variable of B,

---


§35]
EXERCISES 35
195
bound individual variables are accomplished by means of *339 and *342 (as 
in the proof of *350) and the required substitutions for free individual 
variables are accomplished by means of *301 and *306 (as in the proof of 
*351).340 To make matters definite we may specify that first the required 
alphabetic changes of bound variables shall be made in alphabetic order 
of the variables to be changed, and, for any one variable, in left-to-right 
order of the relevant occurrences of B'; and that then the required sub­
stitutions shall be made in alphabetic order of the variables to be substituted 
for.
This completes the proof of *3520, *352n, except that, in order to make it 
possible to use these metatheorems as derived rules, it is necessary to fix 
explicitly how the individual variables of B' and the individual variables 
Yi> Y& ■ . ■, yn shall be chosen. We do this by taking the different individual 
variables of B in order of their first occurrence in B, then after them the 
remaining variables (if any) among x v x 2, . . ,# x„, in order. To each of these 
in turn, as corresponding variable (in B' or among y^ y2, .. 
yn), is assigned 
the first individual variable in alphabetic order which occurs nowhere in 
the given proof of A and which has not previously been assigned.341
EXERCISES 35
35* ° *  In *350, to what extent may the conditions be weakened that a 
is not free in N and that b does not occur in N: (1) if the remainder of the 
metatheorem is to remain unchanged; and (2) if instead of S£N| is used 
the result of substituting b for the bound occurrences of a throughout N?
35- 1 * In each of the following cases, write the result of the indicated 
substitution;
(1) 
=>G(»,v}](3a:)(y)F (2/' x ) => 
z )\
(2) 
V) (z)F(x) =3 F{y) |
(3) 
§ 5 g<5 = G(jof  (*> z) => $y)F{V’ z)\
“ °It ia here that the numbered conditions, (1), or (1) and (2), in the definition of the 
notation 5 are essential, in order to assure that in this added series of steps constituting 
the final part of the proof nothing is required except alphabetic changes of bound 
individual variables and substitutions for free individual variables in accordance with 
•350 and *351 respectively.
841Notice that the derived rules of *350 and *351, and our proofs of them, will con­
tinue to hold for a system obtained from F1 by adjoining any additional axioms. But 
•352 will continue to hold only if the additional axioms are such as to maintain the sit­
uation that the result of an 5-substitution in any axiom is again an axiom, or at least 
a theorem.

---


196
FUNCTIONAL CALCULI OF FIRST ORDER [Chap. Ill
(4) 
y)
(3z)F(x, *)|
(5) 
§ g£ *)= , (v)G(v, t)F (V‘ 2) 
y) =>» ■ p iy .z ) => 
y)I
(6) 
§ ; s  z) =P P(«, v](x)F{z, x ) v (y) F ( y ,  z) =j F(*, *)|
35-2- In order to verify the necessity for each of the numbered conditions,
(1) and (2 ), in the definition of the notation
.... X*)^|
show by examples that *352x would fail if either of these numbered condi­
tions were omitted.
36. The deduction theorem . We shall now establish a deduction theorem
for F1, analogous to that for the propositional calculus (cf. §13).
The notion of a variant of a wff, introduced in §13 for the system P1# 
may be extended in obvious fashion to wffs of F1 or of other formulations 
of the functional calculus of first order: namely, a variant B' of a wff B 
differs from B only by alphabetic changes of the variables of B of all kinds 
(bound or free, individual, propositional, or functional), in such a way that 
the same variable occurs at two places in B' if and only if the variables 
occurring at the two corresponding places in B are the same. In connection 
with the deduction theorem for F1, we need only observe that every variant 
of an axiom is also an axiom. But in other cases, such as, e.g., the formula­
tions of functional calculi of first order introduced in §40, this will not hold; 
and in such cases the notion of a variant must play a role in the treatment 
of the deduction theorem analogous to that which it had in §13.
A finite sequence of wffs, Bx, B2, , . 
Bm, of F1 is called a proof from the 
hypotheses Av A2, . . 
A„ if for each * either: (I) Bf is one of A1( A2, . . .,An; 
or (2) Bt is an axiom; or (3) Bt- is inferred according to *300 from major 
premiss 
and minor premiss B*, where / <  i, k <  i ; or (4) B{ is inferred 
according to *301 (the rule of generalization) from the premiss By, where 
/ <  i, and where the variable that is generalized upon does not occur as a 
free variable in Ax, A2, . . An; or (5) Bi is inferred by an alphabetic change 
of bound variable, according to *350,342 from the premiss B,, where / <  i\ 
or (6) Bt is inferred according to *351,342 by substitution in the premiss By, 
where j <  i, and where the variable, a, that is substituted fordoes not occur 
as a free variable in A1( Aa,. .
An; or (7) B, is inferred according to *352,348 
by substitution in the premiss By, where j <  it and where the variable,
M,Or, more exactly, according to *350—or *351—or *352, as these would be restated 
to make them read as primitive rules of inference.

---


§30]
THE DEDUCTION THEOREM
197
p or f, that is substituted for does not occur as a free variable in Ax, A2l
• * *» ^n*
Such a finite sequence of wffs, Bm being the final formula of the sequence, 
is called more explicitly a proof of Bm from the hypotheses Ai( A2, . . 
A„.
And we use the (syntactical) notation
^ 2' * * *» 
I-
to mean: there is a proof of Bm from the hypotheses A1( Aa, . . 
An.
The special case that n — 0 is not excluded. It is true that, because of 
clauses (5), (6 ), (7) in the foregoing definition, a proof from the null class 
of hypotheses is not the same thing as a proof. But we shall hereafter use 
the notation, H Bm, indifferently in the sense of §30, to mean that there is a 
proof of the wff in question, and in the sense of the present section, to mean 
that there is a proof of it from the null class of hypotheses—relying on the 
metatheorems *350-*352 to enable us to obtain (effectively) a proof of 
any wff whenever we have a proof of it from the null class of hypotheses.343
*360. 
If Aj, A2j . . 
An h B, then A1( A2, . . 
A„_x F A „ d  B.
(The deduction theorem.)
Proof. Let Bj, B2, . . . .  Bm be a proof of B from the hypotheses A1( A2, 
.. 
A„ (Bw being therefore the same as B). And construct the finite se­
quence of wffs An ro Bu An z> Ba, . . 
An r> Bm. We shall show how to 
insert a finite number of additional wffs in this sequence so that the resulting 
sequence is a proof of A„ z> BmJ i.e., of An ro B, from the hypotheses
^ 2? * * »i
In fact consider a particular A„ ro Bit and if i >  1 suppose that the in­
sertions have been completed as far as A„ r> B,-^. The eight following cases 
arise:
Case la: Bt- is An. Then An ro B, is An r> An, a substitution instance of 
the tautology p 
p. Therefore insert before An ro 
the wffs needed to 
make up the proof of it that is obtained by the method used in the demon­
stration of *311. (No substitutions or generalizations appear in this.)
Case lb; B* is one of Av Aa, . . 
A n_v say Ar. Then Ar ro * An ro Bi is 
an axiom, an instance of *302. Therefore insert before A„ro B, the two wffs
•‘•The ambiguity of sense will lead to no confusion, in the contexts in which the nota­
tion will actually be used, because we know that (-B in one sense if and only if f- B in the 
other sense. However, the ambiguity may be removed if desired by agreeing that when 
hypotheses are explicitly w ritten (as in, e.g., "p \- q 
p” or "A ^ Aa, . . . , A n (- B ro") 
the notation shall be understood in the sense of the present section—and in such a case 
as “A lt Af, 
A „ (* B mM this shall not be affected by the possibility of assigning the 
value 0 to n. But when the sign (- is written actually without hypotheses appearing 
before it (as, e.g., "(-£ = 3  
it shall be understood in the sense of §30.

---


198
FUNCTIONAL CALCULI OF FIRST ORDER [Chap. Ill
Ar zd  m An Z3 B,- and Ar, from which A„ zd By is inferred by *300 [modus 
ponens).
Case 2: By is an axiom. Then By 
. A„ zd By is an axiom, an instance of 
*302. Therefore insert before A„ zd By the two wffs By zd .  An zd By and By, 
which both are axioms, and from which An zd By is inferred by modus ponens.
Case 3: By is inferred by modus ponens from major premiss By and minor 
premiss Bk, where j <  i, h <  i. Then By is Bk zd B(. Insert before An zd By 
first the wff An zd By zd « An zd B a zd . A„ zd By (which is an axiom, an in­
stance of *303) and then the wff Art zd Bfc zd . An zd By (which can be inferred 
by modus ponens, and from which then An 
By can be inferred by modus 
ponens, since the necessary minor premisses, An zd By and An zd Bfcl are 
among the earlier wffs already present in the sequence being constructed).
Case 4: By is inferred by the rule of generalization from the premiss By, 
where j <  i. Then B, is (a) By, where a is an individual variable which does 
not occur as a free variable in \ v Aa, . .
An. Insert before An zd By first 
the wff An ZDa By z d  . A„ zd By (since a is not a free variable of AnJ344 this is 
an axiom, an instance of *305), and then the wff An roa By (which can be 
inferred by generalization344 from the earlier wff An zd By already present in 
the sequence being constructed, and from which then An z d  By can be in­
ferred by modus ponens).
Case 5: By is inferred by an alphabetic change of bound variable, according 
to *350, from the premiss By, where j <  i. In this case a corresponding 
alphabetic change of bound variable suffices to infer An zd By from An z d  By.
Case 6: By is inferred according to *351, by substitution in the premiss By, 
where j <  i, and where the (individual) variable that is substituted for 
does not occur as a free variable in A1( Aa, . . 
An. In this case the same sub­
stitution suffices to infer A„ zd By from A„ zd By.345 * *
Case 7: By is inferred according to *352, by substitution in the premiss 
By, where / <  i, and where the (propositional or functional) variable that 
is substituted for does not occur as a free variable in A1( Aa, . . , ,  An. In 
this case the same substitution suffices to infer An zd By from An Z3 By.348
This completes the proof of the deduction theorem. From the special case 
of it in which n =  1 we have the corollary:
*361. 
If A b B, then 1- A d  B.
>44Notice here the role of the condition that a does not occur aa a free variable in
Aj, A j,. . . , A b (clause (4) in the definition of proof from hypotheses a t the beginning
of this section).
MSNotice, in particular, the role of the condition that the variable which is substituted
for does not occur as a free variable in A n.

---


§36]
T H E  D E D U C T I O N  T H E O R E M
199
In what follows we shall often use the deduction theorem as a derived 
rule in establishing theorems or theorem schemata. For this purpose it is 
essential that our proof of it is effective.346 It is left to the reader to verify 
this, after supplying a definite particular proof of the wff A„ rd A„ to be 
used for the case la.
The following metatheorems, *362 and *363,347 are also needed in con­
nection with use of the deduction theorem as a derived rule. Tacit use will 
often be made especially of *363.348
*362. 
If every wff which occurs at least once in the list Ax, A2, . . 
An 
also occurs at least once in the list Cv C2, . . 
Cr, and if 
A2, 
. .
An H B, then Cv C2, . . 
Cr H B.
Proof. Let au a2, . . ., a£ be the complete list of those variables of all kinds 
(individual, propositional, functional) which occur as free variables in 
CXl C2, .. 
Cr but do not occur as free variables in A1( A2, . . ., An (though 
some of them may perhaps occur as bound variables in A1? Aj,,. .., AJ.Then, 
if the given proof of B from the hypotheses \ v A2, . . 
A„ is not also a proof 
of B from the hypotheses Cv C2, . .
CT, it can only be because it involves 
generalizations upon or substitutions for some of the variables alf a2, . . 
a£.
Therefore let q , c,, , . ,, c£ be variables which are all distinct and which 
do not occur in Cj, C2, . . ., Cr or in the given proof of B from the hypotheses 
Ax, A2, . . 
A„, Cj being a variable of the same type (individual, proposi­
tional, singulary functional, binary functional, etc.) as ax, c2 being a variable 
of the same type as aa, c3 a variable of the same type as a3, and so on. 
And throughout the given proof of B from the hypotheses A1; A2, . . ., An 
replace ax, a2, . . ., a£ by clt c2, . . ., c£ respectively. The result is a proof of
£*aiag...ajB|
from the hypotheses D£, Da, , . 
DfJ where Dlf D2, . . . ,  Dr differ from 
Cv Ca, . . ., Cf, respectively, at most by certain alphabetic changes of bound 
variables. This is changed into a proof of B from the hypotheses Du D2, 
. . Df by adding at the end, if necessary, an appropriate series of alpha­
betic changes of bound variables and substitutions (under clauses (5), (6), 
(7) in the definition of proof from hypotheses). Then finally a proof of B
•‘•Compare the discussion of derived rules of inference in §12, and the discussion at the 
end of §13 of the use of the deduction theorem for the propositional calculus.
•"Com pare *132-* 134.
•••For example, when *333 is used in the proof of *365, when *364 is used in the 
proof of *366, when *365 is used in the proof of *367, when *333 and *392 are used in 
the proof of *421.

---


200
F U N C T I O N A L  C A L C U L I  O F  F I R S T  O R D E R  [Ch a p. I l l
from the hypotheses C1( C2l. . . , C r is obtained by inserting, for various 
values of i, as necessary, wffs to constitute a proof of D* from C* by alpha­
betic changes of bound variables.
The foregoing construction has to be made more explicit at several places, 
in order to allow the metatheorem to be used as a derived rule. For example, 
definite instructions must be given as to the choice of the variables cx, Cg, 
.. 
cJ( so as to make it fully determinate. Details of this are obvious but 
cumbersome, and may be left to the reader.349
By taking n — 0 in *362, we have as a corollary:
*363. 
If b B, then C1( Ca, . . , C r FB.
We go on to establish a number of derived rules (*366-*369) that facilitate 
the use of the existential quantifier, in connection with the deduction 
theorem. As a preliminary to this, two theorem schemata (*364, *366) are 
demonstrated, with aid of the deduction theorem as a derived rule.
*364. 
b B Z3a A 
. (3a) B 3  A, if a is not free in A.
Proof. By *306, B ^ A F B d A.
Hence by P, B 3 a A b ~A  zd ~B.
Hence by generalization, B roa A b ~A 
<~B.3fi0 
Hence by *306, B 3 a A b ~A  ro (a)~B.
Hence by P, B n a A b~(a)~B Z3 A.
Then use the deduction theorem.
*365. 
b A r>a B => . (3a)A r> (3a)B.
Proof. By *306, A a a B b A D B .
Hence by P, A 3 a B b ~B  Z3 -A .
Hence by generalization, A roa B b~B  :na ~A.360 
Hence by *333, A r)a B b (a)~B r) (a)~A.
Hence by P, A j a B b  ~-(a)~A 3  ~(a)~B.
Then use the deduction theorem.
*366. 
If Ax, Aa, . . 
A„ b B, and a is an individual variable which does 
not occur as a free variable in Ax> Aa, . . An-l, B, then Aj, Ai#.. 
A*-i, (la)An h
swCorapare the last two paragraphs in the proof of *3152.
#MWhere generalization is thus used in connection with the deduction theorem, care 
must be taken that the variable n which is generalised upon does not ooour as a free 
variable in any of the hypotheses. It is left to the reader to verify this in each case.

---


§37]
D U A L I T Y
201
Proof. By the deduction theorem,
A1( A2, . . 
An-1 F An ID B.
Hence by generalizing upon a and then using *364, we have that 
Ax, A2j . . 
A„_! F (3a)An r> B.
Hence by modus fionens,
Av A*, . . 
A„„1( (3a)An F B.
*367. 
If Ax, A2, . . 
An F B, and a is an individual variable which does 
not occur as a free variable in A1( A2, . . 
An_lf then A1( A2, . . 
A„_i, (3a)An b (3a)B.
Proof. By the same method as the proof of *366, but with use of *365 
replacing that of *364,
*368. 
If A1# A2, . .
An F B, and a is an individual variable which does not 
occur as a free variable in A1( Aa, . . . ,  An-rf B, then Ax, A2j . .
r» (^*0 ■ 
r+2 * * ■ 
^
Proof. By P,
A1( A2, . .
An_r, An_r+1An„r+2. , . An F B.
Hence use *366.
*369. 
If A1( A2i 
A jjFB, and a is an individual variable which does not 
occur as a free variable in A1( A2, . . 
An„r, then Ax, A2, . . 
An_r, 
(3a) . AM tlA ,,.,rt ■ . • An b (3a)B.
Proof. By the same method as the proof of *368, but with use of *367 
replacing that of *366.
37. Duality. As in § 16, we begin by applying the process of dualization 
not to wffs but to expressions which are abbreviations of wffs in accordance 
with certain definitions. Namely, we allow abbreviation by D3-11 and D14, 
but not by other definition schemata352 and not by omissions of brackets.
SB1The case » =  I of *366 is proved as a inetatheorem of the functional calculus of 
first order by Hilbert and Bernays, Grundlagen der Mathematik, vol. 1 (1934), pp. 157-158. 
It may also be compared with theorems I and III of the w riter's "A Set of Postulates 
tjjFJh* fwndjww o$ u>ai©“ (in $h* 
§/ 
vwi. aa u m )f m  pp, aua,
with which, however, it in tar from identical, because the logistic system von* 
sidered in th a t paper is a quite different system from any of the functional calculi of 
first or higher order, and indeed is one which was afterwards shown by Kleene and 
Rosser (in the Annals of Mathematics, vol. 36 (1935), pp. 630-636) to be inconsistent.
•••Here D13 m ight well alio be allowed, but it simplifies the statem ent of the m atter 
Slightly if we exclude it. In order to allow D12, D16-17, we would havo to add duals

---


202
F U N C T I O N A L  C A L C U L I  O F  F I R S T  O R D E R  
[Ch a p. I l l
Of such an expression the dual is obtained by interchanging simultaneously, 
wherever they occur, each of the following pairs of connectives and quanti­
fiers (or better, each of the following pairs of symbols): 3  and <£, disjunction 
and conjunction, =  and 
c: and 
v and |, V and 3.
Of a wff of F1 a dual is obtained by writing any expression of the foregoing 
kind which abbreviates the wff, dualizing this expression, and then finally 
writing the wff which the resulting expression abbreviates. As a particular 
case, the given wff itself may be used in the role of the expression which 
abbreviates it, and when this is done the principal dual of the given wff is 
obtained.
By examining D3-11 and D14, it will be seen that any two duals of the 
same wff can be transformed one into the other by a series of steps of 
which each consists, either in replacing a wf part 
by N , or in replacing 
a wf part N by 
(i.e,, as we may say, either in deleting or in inserting 
a double negation). Hence by P and *341:
*370. 
If B and C are duals of A, then H B =  C.
In order to establish for F1 a principle of duality analogous to *161, we 
shall show for each axiom of F1 that the negation of any dual of it is a theo­
rem of F1; also for each rule of inference of F1 that, if we replace the premisses 
and conclusion by negations of duals of them, the inference still holds as a 
derived rule. It will then follow that the negation of a dual of a theorem of 
F1 is always a theorem of F1.
To begin with the rules of inference, consider first *300. Here the premisses 
are A 3  B  and A, the conclusion B. Let At be a dual of A, and Bj a dual of 
B . Then one of the duals of A 3  B is A3 
B1. By P, if b ~  . Aj 
and 
h-Aj, then h ~BV Hence by *370 and P, if the negation of any dual of 
A 3  B  and the negation of any dual of A are theorems, then the negation of 
every dual of B is a theorem.
Likewise consider *301. The premiss is A and the conclusion (a)A. From 
~Aj, the negation of any dual of A, we may infer first (a)~Ax by *301, and 
thence ~(3a)A! by *338 and P. This is the negation of one of the duals of 
the conclusion, and from it the negation of every other dual of the conclusion 
follows by *370 and P.
Turning now to the axioms, we see that one of the duals of any axiom 
which is an instance of *302, *303, *304 must have, in corresponding order,
of these definition schemata, inventing suitable notations for the purpose; but this 
seems not worth while, as the notations so introduced would hardly be used except in 
connection with the treatment of duality.

---


§37]
D U A L I T Y
203
the following forms (where Av Bx, Gx are duals of A, B, C respectively):
Aj <£ ■ Bjl 
Ajl
A-i 4- [®i 
^*i] 4- • A1 cf: B1 cf: . Ax c(: Gx
~A 3 4- ~B> 4 : ■ Bx c|: Ax
And the negation of each of these may be seen to be a substitution instance 
of a tautology, therefore a theorem by *311. That the negation of every 
other dual of the same axiom is also a theorem, then follows by *370 and P.
In the case of an axiom which is an instance of *306, one of its duals has 
the form
(3a)Aj c|: S^A,!,
where a is an individual variable, b is an individual variable or an individual 
constant, and no free occurrence of a in A x is in a wf part of Ax of the form 
(b)C 368 That the negation of this is a theorem follows by *330 and P. Hence 
by *370 and P, the negation of every dual of the axiom is also a theorem.
In the case of an axiom which is an instance of *305, in order to prove 
similarly that the negation of every dual of it is a theorem, we need only the 
following theorem schema of F1:
*371. 
b A 4: (3a)B 3  (3a) . A 4 : B, if a is not free in A.
Proof. By P, b B 3  A =  ~~ ■ B 3  A.
Hence by *364 and *342, b (a)~~[B 3  A] 3  « (3a)B 3  A.
Then use the law of contraposition (f223).
Thus we have shown that every axiom of F1 has the property that the 
negation of every dual of it is a theorem of F1, and that the rules of inference 
of Fl preserve this property. Hence every theorem of F1 has the property,
i.e,:
*372. 
If b A, and if Ax is a dual of A, then b - A x.
{Principle of duality.)
As in §16, two special principles of duality follow as corollaries, by P:
*373. 
If b A 3  B, and if A x and Bx are duals of A and B respectively, then 
b Bx 3  Ax.
{Special principle of duality for {material) implications.)
m In *300, the condition th at no free occurrence of a  in A is in a wf part of A of the 
form (b)C is clearly equivalent to the condition that no free occurrence of a in A is in 
a wf pari of A of either of the forms (b)C or (3b}C. In the latter form, it :s obvious that 
the condition is unchanged by dualization.

---


204
F U N C T I O N A L  C A L C U L I  O F  F I R S T  O R D E R  [Chap. Ill
*374. 
If b A =  B, and if Ax and Bx are duals of A and B respectively, then 
1- Ax =  Bv
{Special principle of duality for {material) equivalences.)
By the dual of a theorem schema or axiom schema of F1 we shall mean:
(1) if the schema has the form of an implication, the theorem schema ob­
tained from it by *373; (2) if the schema has the form of an equivalence, 
the theorem schema obtained from it by *374; (3) in other cases, the theorem 
schema obtained from it by *372. In case (1), the duaiization is to be per­
formed on the antecedent and consequent of the schema as actually written, 
and according to the instructions as given in the first paragraph of this 
section; similarly, in case (2) the duaiization is to be performed on the two 
parts of the schema as actually written, and in case (3) it is to be performed 
on the schema as actually written, again according to the instructions in the 
first paragraph of this section. Thus the dual of a theorem schema or axiom 
schema may differ according to what abbreviations are used in writing 
the schema, but it is unique for any schema as actually written^It is under­
stood that, before dualizing a schema, any abbreviations by omission of 
brackets or by D12, D13, D15-I7 are first to be withdrawn, restoration 
towards unabbreviated form proceeding thus far but no farther.
In writing the dual of a theorem schema or axiom schema, the subscripts 
1 on the bold capital letters to indicate duaiization—as we used them, e.g., 
in proving *372—may be omitted, on the ground that every wff is a dual of 
some wff. If verbally stated conditions are attached to a theorem schema or 
axiom schema (as for instance in the case of *305, *306, *339), the conditions 
must be dualized in an appropriate sense; but in most cases with which we 
shall meet in practice the verbally stated conditions are the same as or equiv­
alent to their duals and may therefore be left unaltered.354
To illustrate the duaiization of theorem schemata and axiom schemata, 
we may cite the following examples. The dual of *302 is the theorem schema 
which asserts that
b B cf: A ro A.
The dual of *304 is the theorem schema asserting that
b B 
A 
• -A  cf: ~B.
The dual of *305 is *371. The dual of *306 is *330. The dual of *330 is *306,
354Besides theorem schemata, we shall sometimes speak also of duals of other meta­
theorems, in the sense of corollaries of them  by *372, *373, *374. We do not attem pt to 
make this notion more precise, but shall use the terminology in this case only heuristi- 
cally or suggestively.

---


§38]
F U R T H E R  T H E O R E M  S C H E M A T A
205
or, more correctly, it is the theorem schema which is an immediate corollary 
of *306, asserting that every instance of *306 is a theorem. The dual of *331 
is *331, i.e., as we shall say, *331 is self-dual.
Again, the following theorem schemata are, in order, the duals of the 
theorem schemata *336, *337, *338, *339:
*375. 
b (3 a )(3 b )A s (3b)(3a)A.
*376. 
b (3a)A s  A, if a is not free in A.
*377. 
b ~(a)A =  (3a)~A.
*378. 
b (3a)A =  (3b)B, if there is no free occurrence of b in A, and no 
free occurrence of a in A is in a wf part of A of the form (b)C, and 
B is SJA|.
38. Som e further theorem  schem ata.
*380. 
b (3a)B 3  A == . B 3 a A, if a is not free in A.
Proof. By dualizing *335, b A 
(3a) B =  (3a) .A c}: B.
Hence by *377 and P, b A cf: (3a)B =  ~(a) . B 3  A.
Then use P.
♦381. 
b (a)A 3  (3a)B =5 (3a) * A 3  B.
Proof. By P, b ~A  3  « A 3  B.
Hence by generalization and *365, b (3a)~A 3  (3a) * A 3  B. 
Hence by *377 and P, b ~ ( a ) A 3  (3a) , A d B,
Also by *302, generalization, and *365, b (3a)B 3  (3a) . A 3  B 
Hence by P,366 b (a)A 3  (3a)B 3  (3a) . A 3  B.
By *306 and modus fionens, A 3  B, (a)A b B.
Hence by *367, (3a)[A 3  B], (a)A b (3a)B.
Hence by the deduction theorem, b ( 3 a ) [ A 3  B] 3  * (a)A 3  (3a)B.
Then use P.
*382. 
b A 3  (3a) B s  (3 a) . A 3  B, if a is not free in A.
Proof. By *381, *337, and *342.
*383. 
b (a)B 3  A s  (3a) « B 3  A, if a is not free in A.
Proof. By *381, *376, and *342.
“ •The tautology used is

---


206
F U N C T I O N A L  C A L C U L I  O F  F I R S T  O R D E R  [Chap. I ll
*384. 
h [~A D a C][B D a C] =  i A d B 3 a C.
Proof. By P,355 ~A 3  C, B 3
G I - A 3
B 3
G.
Hence by P and *306, [~A 3 a C][B 3 a G] h A => B 3  G. 
Hence by generalization, [~A 3 a G][B 3 a C ] F A d B 3 a G. 
Hence h [~A 3 a C][B =)a C ] D . A = ) B = > a G.
By *300 and P, A d
B ^ C F ^ - A d C.
Hence by generalization, A 3  B 3 a G h ~A  3 a G.
Again by *306, P, and generalization, A 3  B 3 B G I- B 3 B G. 
Hence by P, A 3  B =>a C I- [~A 3 a G][B 3 a C].
Hence b A 3  B 3 a C 3  [~A 3 a C][B 3 a G].
Then use P.
*386, 
I- (a)[A v B] =  A v (a)B, if a is not free in A.
Proof. By *335 and P, h (a)[~A 3  B] s  . ~A 3  (a)B.
Then use P and *342.
*386. 
I- (a)[B v A ] =  (a)B v A, if a is not free in A.
Proof. By *385, P, and *342.
*387. 
h A ==a B 3  . (3a)A =  (3a)B.
Proof. By *340 and *350.
*388, 
V A = a B 3 , A  =  (3a) B, if a is not free in A.
Proof. By *387, *376, and *342.
EXERCISES 38
38.0. For the proof of the deduction theorem, *360, case la, write out 
explicitly the full list of wffs that are to be inserted before A„ 3  B*.
3 8 . 1 . Write the duals of the theorem schemata *383-*388.
3 8 .2 . Establish the theorem schema *365 as a corollary of *333 by dual- 
ization.
3 8 .3 . Similarly establish the theorem schema *387 as a corollary of *334 
by dualization.
3 8 .4 . Similarly establish a corollary of *332 by dualization (in the ex­
pression of which, 
shall occur only through the abbreviation ''(3a)" 
for "~(a)~”I and, in particular, 
shall not occur).

---


§38]
E X E R C I S E S  38
207
38.5. Establish the following theorem schemata of F1:
(1) h (a)A(a)B =  (a). AB.
(2) h (a)A(3a)B 3 (3a) . AB.
(3) 
h (a) (3b) [A 3 B] s  (3b) (a ,. A 3  B, if a is not free in A and b is 
not free in B.
(4) h (a)(3b)[B 3 A] =  (3b) (a) . B 3  A, if a is not free in A and b is 
not free in B.
38.6. A formulation F11 of the intuitionistic functional calculus of first 
(trier may be given as follows. The primitive symbols are those of F \ with 
such additions to them as to make the existential quantifier primitive as 
well as the universal quantifier, and to supply all the primitive sentence 
connectives of the system 
(see 2618). The formation rules are those of 
F1, with the obvious added rules to correspond to the additional primitive 
symbols. The definition of bound and free occurrences of variables must be 
changed so that an occurrence of a in A is bound if it is in a wf part of A of 
either of the forms (Va)B or (3a)Bf otherwise free. Of the definition sche­
mata employed in connection with F1, only D13, D15, DIO are retained. The 
same abbreviations by omission of brackets are retained, including the same 
convention about the use of heavy dots, and also the abbreviation by omit­
ting superscripts on functional variables. The rules of inference are * *300 and 
*301, the same as for Fl. The axioms comprise all substitution instances of 
axioms of Pl2> and all instances of four additional axiom schemata which, 
with obviously necessary modifications, are the same as *305, *306, *330,
♦364,350
By the same or nearly the same proofs as for F1, the following hold (with 
obvious modifications) also for F1*: a modified form of *311 with theorems of 
Pg taking the place of tautologies of P; *331-*337; *339. Hence show that 
*365 and *340-*342 hold for Fl\
3 8 .7 . Show that the rule of alphabetic change of bound variable, *350, 
holds for F“ (Hence *351, *352, *360-*363, *366-*369 hold for Fu by the 
same proofs as for F1.)
•"Specifically, the changes to be made in *305, *306, *330, *364 are as follows:
*330 and *364 are to be modified to read as axiom schemata instead of theorem  sche­
mata; existential quantifiers occurring are to be read, not according to D14, b u t rather 
as involving the prim itive symbol 3 of Fxl; the term s "free occurrence" and "free 
variable" are to be construed according to the modified definition as just given for 
F11; and in *306 and *330 the last of the verbally stated conditions is to be altered to 
read, "and no free occurrence of a in A is m a wf part of A of either of the forms {Vb)C 
or {3b)C."

---


208
FUNCTIONAL CALCULI OF FIRST ORDER [Chap. Ill
3 8 ,8 * Assuming the results of the two preceding exercises, as well as 
results obtained in Exercises 26 regarding the intuitionistic propositional 
calculus, establish the following theorem schemata of Fu:
(1) 
b (3a)~A  r> ~(a)A.
(2) 
b ~ (3 a )A  =  (a)~A.
(3) 
b (3 a )~ ~ A  
~~ (3a)A .
(4) 
b ~~(a)A 
(a)— A.
(5) 
b ( 3 a ) ( 3 b ) A =  (3b)(3a)A .
(6) 
b (3a)A  =  A, if a is not free in A.
(7) 
b (3a)B  d
A j
. B  
A, if a is not free in A.
(8) 
b (3a) [B ^  A] :=> . (a)B 
A, if a is not free in A.
(9) 
b (3a) [A zo B] ^  . A 
(3a)B , if a is not free in 
A.
(10) 
b (3a)[A  v B ]  =  A v  (3a)B, if a is not free in A.
3809, A formulation F]* of the (ordinary, or non-intuitionistic) functional 
calculus of first order may be obtained from Fu by adding the axiom schema, 
A v -A . State and prove an appropriate metatheorem of equivalence be­
tween F]* and F1. (Compare 26.14.)
3 8 . 1 0 * A formulation Flm of the minimal functional calculus of first order 
may be obtained from F11 by omitting the axiom schema ~ A  ^  * A ^  B 
(with no other change). Of the results of 38.6-38.8 regarding F11, extend as 
many as possible to Flm.
3 8 . 1 1 . 
Another formulation, Fjm, of the minimal functional calculus of 
first order may be obtained from F11 by suppressing the primitive symbol 
introducing a new primitive symbol / (a propositional constant), and altering 
accordingly the formation rules, rules of inference, and axiom schemata. 
(The three axiom schemata which involve the symbol ~  explicitly are thus 
omitted; the other axiom schemata and rules of inference remain unaltered 
except in that the notion of a wff has been changed by the change in the 
formation rules; no now axiom schemata or rules of inference are added.) 
Establish the equivalence of Flm and Fjm in a sense like that of §23. (Compare 
26.19.)
3 8 . 1a. For every wff A of F'r let an associated wff A* bo defined, by re­
cursion as follows: if A is a propositional variable standing alone, or if A is

---


P REN  EX NORMAL FORM
209
m
of the form f(a2, aa, . . 
an) where f is an n~ary functional variable or con­
stant and a2, a2, . . 
an are individual variables or constants, then A* * is 
~~A; [ A d B]* is - [ A * D B * j ;  [ABj* is ~~[A*B*]; 
[A v B]* is 
~~[A* V B*]; [A == B]* is — [A* == B*]; if G is -A , then C* is -A*; 
if C is (Va)A, then C* is — (Va)A*; if G is (3a)A. then C* is ~~(3a)A*. 
Show that A is a theorem of F*r  if and only if A* is a theorem of Flm.357 
(This may be done by showing that the axioms of F}, have the property 
that the associated wff is a theorem of Flm, and that the rules of inference 
preserve this property*)
In a wff of F1 the elementary parts, as defined in §30, are those 
wf parts which have either the form of a propositional variable alone or the 
form f(a2) a2, . . ., a„) where f is an «-ary functional variable or constant 
and a1( as, . . 
an are individual variables or constants, Let A* be the wff 
obtained from A by replacing each elementary part E of A by ~~E. Show 
that A is a theorem of F1 if and only if A* is a theorem of Flul. (Use the 
result of 38.12, together with that of 26.20, and 38.8(4) as a theorem schema 
of Flm, and *342 as a inetatheorem of F lm.)
3 8 . 1 4 . Extend the result of 38.13 to wffs A of Flr which do not contain 
either disjunction or the existential quantifier.358
39. Prenex norm al form . If (Va)C or (3a)G appears as a wf part 
of a wff A, the scope of that particular occurrence of the quantifier, (Va) 
or (3a), in A is the particular occurrence of G immediately following that 
occurrence of (Va) or (3a).359
An occurrence of a quantifier, (Va) or (3a), in a wff is initially placed if 
either it is at the beginning of the wff (i.e., with no symbols preceding it,
M7This result is due in substance to Kolmogorofl in the papi-r cited in footnote 210.
( A d d e d  in  p ro o f.) A num ber of further results sim ilar to those ol '18.12, 38.13, 38.14, 
but for intuitionistic rath er than minimal functional calculus of first order, are in 
K leene's In tr o d u c tio n  to M eia m cU h em a U cs (1952), see p. 495.
•••This result, regarding th e minim al functional calculus ol first order, should be 
com pared w ith a result of G6dcl, regarding intuitionistic arithm etic, in his paper in 
E rg e b n is se  fi n e s  M a lh e m a tis c h e n  K ^ U c q u iu m s , no. 4 (1933), pp. 34-38.
•5BOn the analogy of D14, we are hero u^mg 
as abbreviation of
and "(3 ) '1 as an abbreviation of "-^(V 
Also in speaking of an occurrence of (V ) 
or of (3 ), we mean th a t the blank space shall be filled by a variable— so th a t, e.g., an 
occurrence of (V ) consists of one occurrence of each ol the three sym bols (, V, ), in 
that order, the three occurrences being consecutive except th a t a single symbol, a 
variable, m ust stand betw een the occurrence of V and th at of ).
Strictly speaking, an occurrence of the universal quantifier in an occurrum-'ii of (V ), 
and (in F 1) an occurrence of the existential quantifier is an occurrence of ~ ( V  )^. 
But we shall som etim es find it convenient to speak loosely, in a way th a t includes the 
operator variable in an occurrence of the universal or existential quantifier. Thus we 
speak here of occurrences of (Va) and (3a) as occurrences of the universal and existen­
tial quantifiers. Ami there Is a sim ilar intent In thu first paragraph of |3ii, in the stale* 
m ent of **391 below, and elsewhere.

---


210
FUNCTIONAL CALCULI OF FIRST ORDER [Chap. Ill
not even brackets) or it is preceded only by one or more occurrences of quan­
tifiers, (V ) and (3 ), each with its own operator variable.868
An occurrence of a quantifier, (V a ) or (3 a ), in a wff is called vacuous if 
its operator variable a  has no free occurrence in its scope. In the contrary 
case it is called non-vacuous.356
A wff is said to be in prenex normal form if it has no occurrences of quanti­
fiers otherwise than in initially placed non-vacuous occurrences of (V ) and 
(3 l.358
Thus a wff A is in prenex normal form if and only if it has the form
xijiig.. * n flM,
where M is wf and quantifier-free, where each II4 is either (Va,) or (3a,) 
(* =  1, 2, . .  
»), and where a x, a 2, . . 
a n are variables which are all differ­
ent and which all have at least one (free) occurrence in M. Then the formula
. . .  n fl
is called the prefix of A, and the wff M is called the matrix of A. (As a 
special case, we may have that « =  0 ; in this case the prefix is the null 
formula, and the matrix M coincides with A.)
In order to obtain what we shall call the prenex normal form of a wff A, 
we consider the following operations of reduction, applicable to a wff con­
taining quantifiers that are not initially placed:
(i) If (in left-to-right order) the first occurrence of a quantifier that is 
not initially placed is in a wf part ~ (Va)C, where C does not begin with 
then this wf part (i,e., this one occurrence of it) is replaced by (3 a )^ C . 
Cf. *377.
(ii) If the first occurrence of a quantifier that is not initially placed is in 
a wf part ~(3a)C, this wf part is replaced by (Va)~C. Cf. *338.
(iii) If the first occurrence of a quantifier that is not initially placed is 
in a wf part [{Va)C 3  Dl, this wf part is replaced by
(3 b )[S jC | ^  D ],
where b is either a , in case a  has no free occurrence in D , or otherwise the 
first individual variable in alphabetic order after a  which does not occur in 
C and has no free occurrence in D . Cf. *350, *383.
(iv) If the first occurrence of a quantifier that is not initially placed is in
a wf part [(3a)C 
D], this wf part is replaced by
(V b )[S * C | => D ],
where b is determined as in (iii). Cf. *350, *380.

---


§39
PRENEX NORMAL FORM
211
(v) If the first occurrence of a quantifier that is not initially placed is in a 
wf part [D ro (Va)G], where D is quantifier-free, then this wf part is re­
placed by
(Vb)[D rs S£C|],
where b is determined as in (iii). Cf. *350, *335.
(vi) If th e  first occurrence o f a q uan tifier th a t is n ot in itially placed is in 
a w f part [D  3  (3 a )C ], w here D  is quan tifier-free, th en  this w f part is re­
placed b y
(3b)[D => SjCj],
where b is determined as in (iii). Cf. *350, *382.
**390. 
By a finite number of successive applications of the reduction steps
(i)-(vi), any wff A of F1 can be reduced to a wff A' of F1 in which all 
quantifiers are initially placed. This process of reduction is effective, 
and the resulting wff A' is uniquely determined when A is given.
Proof. At each stage in the process, as long as there are any quantifiers 
not initially placed, one and only one of the reduction steps (i)-(vi) is 
possible and the result of making this reduction step is determined effectively 
and uniquely. It remains only to show that the process must terminate in 
a finite number of steps.
Let a particular occurrence of one of the signs ro or ^ be called external 
toa particular occurrence of a quantifier if: (1) it is not in the scope of that 
occurrence of the quantifier, and also (2) in case of an occurrence of (V ) 
with an occurrence of ~ both immediately before and immediately after it 
(or, in other words, in case of an occurrence of (3 ) ) it is not one of those 
two occurrences of ~ (which form part of that occurrence of (3 ) ).
Now each reduction step either diminishes the number of occurrences of 
quantifiers that are not initially placed, or else, while leaving this number 
unchanged, diminishes the total number of occurrences of the signs 
and ~ 
external to the first occurrence of a quantifier that is not initially placed. 
Since both numbers are of course finite in the given wff A, it follows that 
the process of reduction must terminate in the required wff A' whose 
quantifiers are all initially placed.
**391. 
Any wff A of F1 can be reduced to a wff B of F1 in prenex normal 
form, by first applying the reduction process of **390 to reduce A 
to a wff A' in which all quantifiers are initially placed, and then 
deleting all vacuous occurrences of quantifiers, (V a) or (3 a ), in A 1

---


212
F U N C T I O N A L  C A L C U L I  O F  F I R S T  O R D E R  [Chap. Ill
to obtain B. This process of reduction is effective, and the resulting 
wff B in prenex normal form is uniquely determined when A is given.
Proof. Obvious as a corollary of **390.
Definition. The wff B which is obtained from the wff A by the reduction 
process of **391 is called the prenex normal form of A.
*392. 
If B is the prenex normal form of A, h A =  B.
Proof. At each step of the reduction process of **390, the wff obtained is 
equivalent to the previous wff, in the sense that the material equivalence of 
the two wffs is a theorem of F1. Thus by the transitive law of equivalence, 
b A =  A', Again, in the reduction of A' to B by deleting vacuous occurren­
ces of quantifiers, the deletions may be performed one by one, and at each 
step the wff obtained is equivalent to the previous wff. Therefore, by the 
transitive law of equivalence, h A =  B.
The derived rule *341 here has to be used at each step, in establishing the 
equivalence of the wff obtained to the previous one. Given *341, the re­
quired equivalence follows, in the case of reduction step (i), by *377; in the 
case of reduction step (ii), by *338; in the case of (iii), by *350 and *383; 
in the case of (iv), by *350 and *380; in the case of (v), by *350 and *335; 
in the case of (vi), by *350 and *382; in the case of deletion of a vacuous 
occurrence of a quantifier, by *337 or *376.
Although the prenex normal form of a wff is unique, as we have here 
defined it, and although a wff is always equivalent to its prenex normal form 
(in the sense that the equivalence is a theorem of F1), it is not true in general 
that, if two wffs are equivalent to each other (in this sense), they therefore 
have the same prenex normal form. Counterexamples are obvious, and are 
left to the reader.
EXERCISES 39
39.0. Find the prenex normal form of each of the following:
(1)
— \y)F{y, z) n* — (3x)G{x, y, z)
(Answer: (z) (3iel)(3ar). — F{x1, z) i d  G(x, y, z).)
(2)
{y)F{x, y) i d  (y)F(x, x)
(3)
F{y) =>„ -  . {x)G{x, y) => (y)~F(y)
W
F{x) v ~{y)F{y)
(5)
(3x)F[x, y, z) =  {y)G{x, y, z).

---


§39]
EXERCISES 39
213
3 9 -i- Show that the matrix of the prenex normal form of a wff differs 
from the associated quantifier-free formula (in the sense of §32) at most 
by changes in the individual variables at certain places, and deletions of 
double negations
3 9 .2 . 
A formulation of the functional calculus of first order is to have 
negation, conjunction, and disjunction as its primitive sentence connectives, 
and the universal and existential quantifiers as its primitive quantifiers. 
Otherwise the primitive symbols are to be the same as for F1. (1) Write the 
formation rules for this formulation of the functional calculus of first order.
(2) Given that the rules of inference are generalization (*301) and m o d u s  
p o n e n s (in the form, from ~A v B and A to infer B), supply suitable axiom 
schemata—making them as few and as simple as feasible—and then dem­
onstrate equivalence of the system to F1 in an appropriate sense.
3 9 - 3 -  Extend the definition of f u l l  d is ju n c tiv e  n o r m a l  f o r m  (see exercise 
24.9) to quantifier-free formulas of the system introduced in 39.2. Show for 
this system that, if A and B are quantifier-free, then h A =  B if and only 
if A and B either have the same full disjunctive normal form or both have 
no full disjunctive normal form.
3 9 4 -  Define p r e n e x  n o r m a l  f o r m  in an appropriate way for the system of 
exercise 39.2, and demonstrate analogues of **390, **391, *392.
3 9 * 5 *  In the system of exercise 39.2, if the propositional variables are 
included among the primitive symbols, let a wff be said to be in p r e n e x - 
d is ju n c tiv e  n o r m a l  f o r m  if either it is p  ~ p  or: (I) it is in prenex normal form, 
and (II) the variables in its prefix are, in order of their occurrence in the 
prefix, and for some n , the first n  individual variables in alphabetic order, 
and (III) its matrix is in full disjunctive normal form. (1) Establish meta­
theorems about reduction to prenex-disjunctive normal form, analogous to 
those of 39.4 about reduction to prenex normal form. (2) Answer the ques­
tion whether it is true in general that, if b A =  B, then A and B have the 
same prenex-disjunctive normal form.
39.6. 
In the case of the singulary functional calculus of first order, with 
primitive basis as given in §30 (i.e., in the formulation F1,1), the process of 
bringing quantifiers forward by means of the reduction steps (i)-(vi) of 
this section can be in a certain sense reversed. The following reduction steps 
are used: (a) to delete a vacuous occurrence of a quantifier (3a) or (Va); 
(b) to replace a wf part (3a)~C by ~(Va)C; (c) to replace a wf part (Va)~C 
by ~(3a)C, if it is not immediately preceded by 
(d) to replace a wf part 
(3a)[C 3 D] by [(Va)C 3 (3a)DJ; (e) to replace a wf part (Va)[C 3 D] 
by [(3a)C 3 D], if a is not free in D; (f) to replace a wf part (Va) [C 3 D]

---


214
F U N C T I O N A L  C A L C U L I  O F  F I R S T  O R D E R  [Chap. I l l
by [C 3  (V a)D ], if a is not free in C; (g) to replace a wf part (Va^fCq ZD Cs] 
3  D ] by ~ [(V a)[~ C j 3  D] = > ^ (V a)[Ca3  D]]. By a series of applications 
of these reduction steps, together with steps which consist either in a 
transformation of a wf part by means of propositional calculus (and * *342) 
or in an alphabetic change of bound variable, show that every wff A of 
the singulary functional calculus of first order, F1,1, can be reduced to a 
wff B such that: (1) the only occurrences of quantifiers in B are in wf parts 
of the form (Vs) . Dj 3  . D2 ^  . .  . . 
3  Dn, where n may be 1 or great­
er,360 and where each 
separately is either f^x) or 
the functional
variables i v fB, . .
frt being all different in the case of any one particular 
such wf part of B ;381 and (2) \~ A  =  B .368
39*7. Apply the reduction process of the preceding exercises to the follow­
ing wffs of F1,1:
(1) 
(3x)(y). F(z) ■=> G{x) => . G(x) zd H{x) zd . F(y) zd H(y)
(2) 
(3x)(y){*) . F(a;) 3  G(y) 3  H(x) 3  . F(z) zd G(a:) ZD H(z)
(3) 
F(x) 
.  F(y) 3 , [G(x) id G(y)} v (z)F(s).
39.8. 
For a formulation of the singulary functional calculus of first order 
with primitive basis as in 39.2, supply the analogue of the reduction process 
and the metatheorem of 39.6. (In order to simplify the statement of the 
reduction process, make use of the full disjunctive normal form—cf. 39.3— 
and its dual, the full conjunctive normal form.)
3 9 -9 - For a formulation of the functional calculus of first order, let the 
primitive symbols be as described in exercises 30.6. And let there be two 
rules of inference, as follows (a and b being individual variables): from 
A |a . B |b C and A to infer C, if b is not free in C; from A jB B to infer 
§£A| |b $bB |, if no free occurrence of a in A or B is in a well-formed part of 
the form C |b D. Find axiom schemata (seek to make them as few and as 
simple as* possible) such that the system becomes equivalent to Fl in an 
appropriate sense, and carry the development far enough to establish this 
equivalence. (Use may be made of results previously obtained regarding the 
propositional calculus, including those of exercises 25.)
39.IO . Establish the equivalence to F1, in an appropriate sense, of the
MDIn case n is I, the wf part of B  in question is sim ply (VasJD^ i.e., either (V®)^®) 
or (VaO^fri®),
M1But the sam e functional variable or some of the sam e functional variables may 
occur in tw o or more different such w f parts of B.
*HThe result of this exercise is due to Heinrich Behm ann in a paper in the Mathe- 
matische Annalen, vol, 89 (1922), pp. 163-229 (see especially pp. 190-191).

---


§39]
E X E R C I S E S  39
215
following system F*b. The primitive symbols are the same as those of F1 
with the two additional primitive symbols, 3 and—*. The wffs are of two 
kinds, terms and sentences. Namely, the terms are given by the same forma­
tion rules as those of F1, with “wff' replaced by “term” (and “wf” by “a 
term” ) throughout, together with one additional rule; if T is a term and a is 
an individual variable, then (3a)T  is a term. The sentences are all formulas 
Tv r 2J . . 
r n- » A ;  where n is any natural number (not excluding 0 ), and 
Tx and r 2 . . . and T n and A  are terms. Thus no wff contains more than one 
occurrence of —>, and a wff is a sentence or a term according as it does or 
does not contain an occurrence of 
In a term, an occurrence of a variable 
a is bound if it is an occurrence in a wf part of either of the forms (Va)B or 
(3a)B; otherwise free. In a sentence all occurrences of variables are bound. 
There is one axiom schema, namely A —* A. where A is a term. And the rules 
of inference are the eleven following, where A0, A*, A2, . . 
A„, A, B, C are
terms, and a is an individual variable, and b is an individual variable or an 
individual constant: (I) from Al( A2, . . ., An—>- B to infer A0, A v A2, . . 
An-»  B ;383 (II) from A1( A2, . . 
AM , A*, Afc+1, Ak+2l . . 
An—► B to infer 
^-2) * • '• ^k—1> 
Aft, A^.+2) • * ■> 
—^ 
(HI) from Aj, Aj, A2, . .
An—> B to infer Alt A2, . . 
An—► B; (IV) from Av A2, . . 
An —* B to
infer AlP A2, . . 
Anwl—► A„ 3  B; (V) from A1( A2). . „  Aw- > A d
B and 
A v A2, . . 
An —► A to infer A1( A2, . . 
An —► B;364 (VI) from Ax, A2, . . 
An- » B  and A v A2, . . . .  A „ - ^ - B  to infer A 1. A2, .. 
Ari_1-^ ^ A n; (VII)
from A v A2, . . 
An—► 
to infer A1( A2, . . 
An—► B ;364 (VIII) from
A1# Az, . . 
An->- A to infer A1( A2, . . ., An-*  (Va)A, if a is not free in
Ax, A2, . . 
An;384 (IX) from A1( A2, . . 
An~* (Va)A to infer Av A2, . . .,
An —> SJA|P if no free occurrence of a in A is in a wf part of A of either of 
the forms (Vb)C or (3b)C ;364 (X) from A1? A2, . . 
An—► S£Ai to infer
A, , A ,.........A n- ( 3 a ) A  if no free occurrence of a in A is in a wf part of
A of either of the forms (V b)C  or (3b)C ;384 (XI) from A,, A2, .. 
A„—> B
to infer A v A2, . . 
A n„v (3a)A „—► B, if a is not free in Alf A2, . . 
A jM j
B. 386 (As a first step toward establishing the desired equivalence show that, 
if B is any term of 
and B' is the corresponding wff of F1, obtained from 
B by replacing (3 ) everywhere by ~ (V  )*, then —► B is a theorem of F*b 
if and only if B' is a theorem of F1.)
Also establish the equivalence to F1, in an appropriate sense, of
8MThe special case that n = 0 is not excluded, i.e., from -*> B to infer A-*B. 
M4Again, as a special case, n may be 0.
MSThe system of this exercise is intermediate between Gentzen's calculi NI< and LK 
(see his paper cited in footnotes 294-295), with a modification due to Bernays (Logical 
Calculus, 1935-1936).

---


216
F U N C T I O N A L  C A L C U L I  O F  F I R S T  O R D E R  [Chap. Ill
the following system F*380 The primitive symbols and the terms are the same 
as those of F*b (see the preceding exercise). The sentences ("Sequenzen”) are
a 11 formulas r 1( r 2, ....  r ^ A , ,  a 2........ Am; where m and « are natural
numbers (not excluding 0 ), and 1^ and T2 .. . and Tn and 
and A2 .. . 
and Am are terms.367 Thus no wff contains more than one occurrence of 
and a wff is a sentence or a term according as it does or does not contain 
an occurrence of —
Free and bound occurrences of variables are defined as 
in the preceding exercise. Again there is one axiom schema, A —► A, 
where A is a term. And the rules of inference are the following, where 
A0, Av A2, . . 
AnJ B0, B1( B2, . .
Bm, A, B, G are terms, and a is 
an individual variable, and b is an individual variable or an individual 
constant:
la. From Alf A2........An ->  Bx, B2..........Bm to infer A0, Alf A2, . . An~*
Bt, B2........ Bm.3a8
lb. From Ax, A2, . . An- »  Bv B 2, . . 
Bm to infer Av A*,.. 
An~*
Bo. Bj, B2.........Bm.388
Ha. From A1( A2, . . A*_1( A*, Ak+l, AM , . . , A n- > Bv Ba, .. 
Bm to 
infer Aj, A2, • • 
A*_^, A*+i, A*, Aj.^2, . . ., An —► Bj_, B 2, .. ., Bm.366
lib. From A1( A*........An~-> Blf B2, . .
B„ Bl+1, Bl+2..........Bm to
infer Ait Aa, . . 
A„ —► B1; B2, . . 
Bf_lf Bi+1, Bt, Bt+a» ■ • •» Bm-370
Ilia. From Ax, AXJ A* . . 
A n—>BV B2, . . Bm to infer AtJ A8. . . An—►
B
R  
R  
369
1, D 2, . . 
D m .
Illb. From Av A2j . . An- > Bt, BXJ B2(. . Bm to infer A1; A2, ..
A —* R R 
R  
370
/\n—► Dj, r>2, . . ,, x>m.
IVa. From A„ A2, . . An—► B to infer A„ A2, . . 
An_!-> An zo B.
IVb. From A t, A2, . . 
A,,—* A and B —► B1( B 2, . .
Bm to infer A„
A2, . 
An, A zo B-*- B,, B2, . . 
Bm.388
Va. From Av A........ . A„-»- B,, B2, .. 
Bm to infer A„ A , , . . A , . , - *
-A*, Bj, Ba........ Bm.a8fl
Vb. From A„ Aa, . . An- »  B„ B2> .. 
Bm to infer A1( A,, . . A„, 
~'B1->  Ba, Ba, . .
Bm.™
Via. From A,, A2, . . A„ —► A to infer A,, A„ . . An—► (Va)A, if a is 
not free in Aj, A2, . . A„.870
,MThis is Gentzens' calculus LK, with some obvious minor simplifications (which 
were not adopted by Gentzen because he wished to m aintain as close a similarity as 
possible between LI< and the intuitionistic calculus L J). Compare the discussion of 
Gentzen’s methods in §29.
s#7In particular, the arrow standing alone constitutes a sentence.
•••Here m or « or both may be 0.
•••Here m may be 0.
J70Here « may be 0.

---


§39]
EXERCISES 39
217
VIb. From B —> B V B 2, . . 
B m to infer ( 3 a ) B —* 8 ^ B 2, . . ,, B mi if a 
is not free in Bv  B 2, . . 
B m.36ft
V ila. From S “A | -► B v B 2i . . „ B W to infer ( V a ) A - *  B 1( B 2, . . 
B m, 
if no free occurrence of a  in A  is in a wf part of A  of either of the forms 
(V b )C  or (3 b )C .309
V llb. From Av  A a, . . 
A n ~->S|)Ai to infer A 1( A 2 l, .
A „ —► (3 a )A , if 
no free occurrence of a  in A  is in a wf part of A  of either of the forms (V b )C  
or (3 b )C .37°
VIII. From A v  A 2l . . 
A k-> C , Bv  B a, . . ., B , and A*+1, A *+a. . • 
A n, 
C - *  B (, B l+1-------, B m to infer Av A 2------- - A n ~ *  Bv B 2..........B m.371
39 *1 2 . Establish the equivalence to F* of the system F*h obtained by 
replacing the rule of inference VIII by the inverses of the two rules Va and 
Vb, and adding a rule of alphabetic change of bound variable—in the 
sense that the theorems of the two systems are identical.372
s,lHere we may have as special cases any or all of Jt ~  0, / — 0, k =  n, l =  m.
#,,This is Gentzen's "H auptsatz" for LK, as modified to conform to changes which 
we have made in the system. Gentzen’s method is to show first how to eliminate an 
application of V III from a proof, if such an application occurs only once and as the 
last step of the proof, and if C is not identical with any of the terms B x, Ba, . . .  B t, 
A*+l, A4+i, . . ., An. This is not done in one step, but rather the application of VIII 
in the given proof is replaced by one or two applications of V III which either come 
earlier in the proof or have a term  C that contains a smaller total number of occur­
rences of the symbols ZD, 
V, 3. Details of this, which involve a m athematical in­
duction of rather complex form, may be found in Gentzen's original paper. But the 
reader who is interested in following the m atter up is urged first to work this out for 
himself and then afterwards to look up Gentzen's treatm ent.

---


IV. The Pure Functional Calculus o f First Order
