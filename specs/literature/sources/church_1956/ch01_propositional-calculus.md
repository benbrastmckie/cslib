<!-- Source: Church, A. (1956). Introduction to Mathematical Logic. Chapter I: The Propositional Calculus (pages 69-118). BibKey: Church1956 -->

---


X. The Propositional Calculus
The name propositional calculus150 is given to any one of various logistic 
systems—which, however, are all equivalent to one another in a sense which 
will be made dear later. When we are engaged in developing a particular 
one of these systems, or when (as often happens) it is unnecessary for the 
purpose in hand to distinguish among the different systems, we speak of the 
propositional calculus. Otherwise the various logistic systems are distin­
guished as various formulations of the propositional calculus.
The importance of the propositional calculus in one or another of its for­
mulations arises from its frequent occurrence as a part of more extensive 
logistic systems which are considered in this book or have been considered 
elsewhere, the variables of the propositional calculus (propositional varia­
bles) being replaceable by sentences of the more extensive system. Because 
of its greater simplicity in many ways than other logistic systems which we 
consider, the propositional calculus also serves the purposes of introduction 
and illustration, many of the things which we do in connection with it being 
afterwards extended, with greater or less modification, to other systems.
In this chapter we develop in detail a particular formulation of the prop­
ositional calculus, the logistic system Px. Some other formulations will be 
considered in the next chapter.
10. The primitive basis of Prl5l) The primitive symbols of 
are 
three improper symbols
: 
=> 
i
(of which the first and third are called brackets) and one primitive constant
/
and an infinite list of variables
P 
9 
r s px 
ql 
rj 
s1 
p.2 q, 
■ • ■
(the order here indicated being called the alphabetic order of the variables). 
The variables and the primitive constant are called proper symbols.151 * 161
uoHistoricaI questions in connection with the propositional calculus will be treated 
briefly in the concluding section of Chapter 11.
161 Regarding the terminology, sec explanations in §07 and in footnote 117.

---


70
T H E  P R O P O S I T I O N A L  C A L C U L U S
[Ch a p. I
We shall hereafter use the abbreviations “wf” for '‘well-formed/' “wff” 
for ‘‘well-formed formula,” “wffs” for “well-formed formulas.” The for­
mation rules of P2 are:152
lOi. 
The primitive constant / standing alone is a wff.
lOii. 
A variable standing alone is a wff.
lOiii. 
If T and A are wf, then [T id A] is wf.153
To complete the definition of a wff of Pj we add that a formula is wf if 
and only if its being so follows from the three formation rules. In other 
words, the wffs of Px are the least class of formulas which contains all the 
formulas stated in lOi and lOii and is closed under the operation of lOiii.
Though not given explicitly in the definition, an effective test of well- 
formedness follows from it. If a wff is not of too great length, it may often 
be recognized as such at a glance. Otherwise we may employ a counting 
procedure in the following way. If a given formula consists of more than one 
symbol, it cannot be wf unless it ends with ] and begins with [. Then we 
may start counting brackets at the beginning (or left) of the formula, pro­
18tSystem atic methods of num bering theorems, axioms, etc. so as to indicate the sec­
tion in which each occurs were perhaps first introduced by Peano. The m ethod adopted 
here has some features in common with one th a t has been used by Quine.
We shall num ber sections by num bers of two or more digits in such a way th a t the 
num ber of the chapter in which the section occurs m ay be obtained by deleting the 
last digit. However, chapter num bers are given by Rom an numerals. Some chapters 
have a t the beginning a brief introductory statem ent not in any numbered section.
We shall num ber axioms, rules of inference, theorem s, and m etatheorem s by num bers 
of three or more digits in such a way th a t the num ber of the section in which they occur 
may be obtained by deleting the last digit. We place a dagger, f, before the num ber 
of an axiom  or theorem of the logistic system ; an asterisk, *, before the num ber of a 
(prim itive) rule of inference, axiom  schema, derived rule of inference, or theorem  
schema; and a double asterisk, **, before the num ber of other m etatheorem s. (The 
terminology, so far as not already explained in the introduction, will be explained in 
this and following chapters.) The num bers of axioms, axiom  schem ata, and prim itive 
rules of inference have 0 as the ncxt-to-last digit, and are thus distinguished from the 
num bers of theorems, theorem  schem ata, derived rules of inference, and other m etatheo­
rems.
In num bering formation rules we use the num ber of the section in which they occur 
and a sm all Roman numeral. Thus 10i, lOii, lOiii are the form ation rules in §10.
A collection of exercises has the same num ber as the section which it follows. For 
individual exercises in the collection we use the num ber of the collection of exercises, 
followed by a period, then another digit or digits. Thus 12.0, 12.1, and so on are the 
exercises which follow §12.
D efinitions and definition schem ata are numbered D l, D2, and so on, w ithout regard 
to the section in which they occur.
“ ■Concerning the use of bold letters as syntactical variables see §08. Also see the 
italicized statem ent near the end of §08.
W ithout the convention th a t juxtaposition is used for juxtaposition (see footnote 
137), we would have to state lOiii more lengthily as follows: If T  and A are wffs, then the 
form ula consisting of [, followed by the symbols of T  in order, followed by ID , followed 
by the sym bols of A in order, followed by ], is wf.

---


§10]
PRIMITIVE BASIS
71
ceeding from left to right, counting each left bracket, r, as - f l anti each 
right bracket, ], as —1, and adding as we go.154 When the count of 1 first 
falls either on a right bracket or on a left bracket with a proper symbol 
immediately after it,155 the next symbol must be the implication sign, ro, if 
the formula is wf.156 This is called the principal implication sign of the for­
mula, the part of the formula between the initial left bracket and the prin­
cipal implication sign is called the antecedent, and the part of the formula 
between the principal implication sign and the final right bracket is called 
the consequent. Then the given formula is wf if and only if both antecedent 
and consequent are wf. Thus the question of the well-formedness of the given 
formula is reduced to the same question about two shorter formulas, the 
antecedent and the consequent. We may then repeat, applying the same 
procedure to the antecedent and to the consequent that we did to the given 
formula. After a finite number of repetitions, either we will reach the ver­
dict that the given formula is not wf because one of the required conditions 
fails (or because we count all the way to the end of some formula without 
finding a principal implication sign), else the question of the well-formedness 
of the given formula will be reduced to the same question about each of a 
finite number of formulas consisting of no more than one symbol apiece. 
A formula in which the number of symbols is zero—the null formula—is of 
course not wf. And a formula consisting of just one symbol is wf if and only 
if that symbol is a proper symbol.157
Hereafter we shall speak of the principal implication sign, the antecedent, 
and the consequent, only of a wff, as indeed we shall seldom have occasion to 
refer to formulas that are not wf. If a formula is wf and consists of more
lMThe choice of left-to-right order is a concession to the habit of the eye. A like 
procedure could be described, equally good, m which the counting would proceed from 
right to left.
U5More explicitly, if the given formula is wf and consists of more than one symbol, 
then the first symbol m ust be 
and the second symbol must be either a proper symbol 
or [. If the second symbol is a proper symbol, the third symbol must be 13, and this third 
symbol is the principal implication sign. If the second symbol is [, then the count is 
made from left to right as described; when the count of I falls on a ], the next symbol 
must be :d , and this is the principal implication sign.
l6aHere [, ], and ZD are being used autonymously. Notice that in addition to the use 
of symbols and formulas of the object language, m the syntax language, as anfonymous 
proper names, i.e., as proper names of themselves isi the way explained jn §08. we shall 
also sometimes find it convenient to use them  as autonytnoits common names, i.e., as 
common names (see footnotes 4, 6) of occurrences of themselves.
When used autonymously, [ may be read orally as "left bracket," ] as "right bracket," 
and 13 as "implication sign" (or more fully, "sign of material implication").
In oral reading of wffs of P x (or other logistic system) the readings "left bracket" and 
"right bracket" may also occasionally be convenient for [ and ] respectively. But in 
this case, 13 should be read as "implies" or " i f ........ then," as in the table in §05.
**7In practice, the entire procedure may often be shortened by obvious devices.

---


72
THE PROPOSITIONAL CALCULUS
[Chap. I
than one symbol, it has the form [A d B] in one and only one way.168 And 
A  is the antecedent, B is the consequent, and the z i between A  and B is the 
principal implication sign.
By the converse of a wff [A 
B] we shall mean the wff [B o  A ].
In Px all occurrences of a variable in a wff are free occurrences', a wff is an 
n-ary form if it contains (free) occurrences-of exactly n different variables, 
a constant if it contains (free) occurrences of no variables; all forms are 
propositional forms; and all constants are propositional constants or 
sentences. (Cf> footnote 117.)
In order to state the rules of inference of Px, we introduce the notation 
"S 
i" for the operation of substitution, so that S^A] is the formula which 
results by substitution of B for each occurrence of b  throughout A.160 This 
is a notation for which we shall have frequent use in this and later chapters. 
It is, of course, not a notation of Px (or of any logistic system studied in this 
book) but belongs to the syntax language, just as the apparatus of syntac­
tical variables does: its use could always be avoided, though at the cost of 
some inconvenience, by employing English phrases containing the words 
'‘substitute," "substitution," or the like.
The rules of inference are the two following:160
*100. 
From [A ro B] and A  to infer B. 
(Rule of modus ponens.)
*101. 
From A, if b is a variable, to infer SgA].181 
(Rule of substitution.)
In the rule of modus ponens (*100) the premiss [A d  B] is called the major 
premiss, and A  is called the minor premiss. Notice the condition that the 
antecedent of the major premiss must be identical with the minor premiss; 
the conclusion is then the consequent of the major premiss.162 
The axioms of Pj are the three following:
1*102. 
[p => [q r? p]}
fl03. 
[[S 
?]] 3  [[S => p] 3  [s Z> q]]]
1*104. 
[ [ [ p ^ f ] = > f ] ^ p ]  * 180
U8 As explained m §08, the bold roman capitals have as values formulas (of the lo­
gistic system under consideration) which are wf. This makes it unnecessary to put in an 
explicit condition, “ where A and B are wf."
JWThe bold roman small letters, as “ b “ here, have proper symbols as values—see 
§08. When b does not occur in A, the result of the substitution is A itself.
180For brevity, we say simply “ infer" in stating the rules rather than “ immediately 
infer," which is the full expression as introduced in §07.
lB1It is meant, of course, that B may be any wff. The result of the substitution 
is wf, as may be proved by mathematical induction with respect to the number 
of occurrences of m in A.
m The terms modus ponens, major premiss, minor premiss, antecedent, consequent are 
irom Scholastic logic (as arc, of course, also premiss, conclusion).

---


§10]
PRIMITIVE BASIS
The first of these axioms (fl02), or its equivalent in other formulations of 
the propositional calculus (whether or not it is an axiom), is called the laiv 
of affirmation of the consequent. Similarly, the second axiom is called the 
self-distributive law of {material) implication. And the third axiom is called 
the law of double negation,163
In accordance with the explanation in §07, a proof in Pj is a finite sequence 
of one or more wffs each of which either is one of the three axioms, or is 
(immediately) inferred from two preceding wffs in the sequence by modus 
ponens, or is (immediately) inferred from one preceding wff in the sequence 
by substitution. A proof is called a proof of the last wff in the sequence,164 
and a wff is called a theorem if it has a proof.
In addition to the abbreviations "wf," "wff," we shall also use, in this and 
later chapters, the abbreviations "t" for "the truth-value truth" and "f” 
for “the truth-value falsehood."
T he intended principal interpretation of the logistic svstem  Pj has already 
been indicated im plicitly by discussion in §05 and m tin*, present chapter. We 
now m ake an explicit statem en t of the sem antical rules (in the .sense of §07) 
These are:
a. 
/  denotes f.
b. 
The variables are variables having the range t and f.
c. 
A form which consists of a variable a standing alone has the value t 
for the value t of a, an d  the value f for th e value f of a.
d. 
L et A and B be constants. Then [A 
B ] denotes t if either B denotes t 
or A  denotes f. O therw ise [A id B ] denotes f.
e. 
L et A be a form  and B a constant. If B  denotes t, then [A zd B] has the 
value t for all assignm ents of values to its variables. If B denotes f, then [A id B], 
for a given assignm ent of values to its variables, has the value f in case A has the
1MThe uncertainty as to whether the name law o} double negation shall be applied to 
1104 or to the wff which results from f 104 by interchanging antecedent and consequent 
is here resolved in favor of the former, and to the latter we shall therefore give the 
name converse law of double negation. Thus the law of double negation is the one which 
(through substitution and modus ponens) allows the cancellation of a double negation.
Also the self-distributive law of implication, 1103. (through substitution and modus 
ponens) allows the distribution of an implication over an implication. And the converse 
self-distributive law of (material) implication is the converse of flU3, which allows the 
inverse process to this.
If in f 103 and fl04 we replace the principal implication sign by the =  of D6 below 
(or by an equivalent =  in some other formulation of the propositional calculus), there 
result the complete self-distributive law of (material) implication and the complete law of 
double negation, as we shall call them respectively.
1840bserve that the definition of a proof allows any number of digressions and lr- 
relevancies, as there is no requirement that every wff appearing in a prooi must actually 
contribute to obtaining the theorem proved or th at the shortest way must always be 
adopted of obtaining a required wff from other wffs by a series of immediate inferences.
7,*i

---


74
THE PROPOSITIONAL CALCULUS
[Ch a p. I
value t  for th a t assignm ent of values to  the variables, an d  has the value t  in case 
A  has the value f for th a t assignm ent of values to the variables.
f. 
L et A  be a constant and B a form. If A denotes f, then [A rp B ] has the 
value t for all assignm ents of values to its variables. If A  denotes t, then 
[A i p  B ], f o r a  given assignm ent of values to its variables, has the sam e value 
th a t B has for th a t assignm ent of values to the variables.
g. 
L et A  and B be forms, an d  consider a given assignm ent of values to the 
variables of [A ip  B]. Then the value of [A rp B ] is t if, for th a t assignm ent of 
values to the variables, either th e value of B is t or the value of A is f. O therw ise 
the value of [A =5 B] is f.
This has been w ritten o u t a t tedious length for th e sake of illustration. Of 
course th e  last three rules m ay be condensed into a  single statem ent by in tro ­
ducing a convention according to which a constant has a value, nam ely, its 
denotation, for any assignm ent of values to any variables. And rule d m ay be 
included in th e  sam e statem en t b y  a further convention according to w hich 
having a value for a null class of variables is th e  sam e as denoting.
The reader should see th a t these rules have the effect of assigning a unique 
denotation to every constant (of P t), and a unique system  of values to every 
form.
As to the m otivation of the rules, observe th a t rule d ju st corresponds to the 
account of m aterial im plication as given in §05, nam ely, th a t everything im plies 
tru th , and falsehood implies everything, b u t tru th  does n o t im ply falsehood. 
Rules c, e, f, g are then ju st w h at th ey  have to be in view of th e account of 
variables and forms in §02.
Besides this principal in terp retatio n  of Pj oth er interpretations are also 
possible, and some of them  will be m entioned in exercises later.
The reader m ust bear in m ind th a t, in the form al developm ent of the system , 
no use m ay be m ade of any intended interpretation, principal or other (cf. §§07, 
09).
11. Definitions. As a practical matter in presenting and discussing the 
system, we shall make use of certain abbreviations of wffs of Px.
In particular the outermost brackets of a wff may be omitted, so that we 
write, e.g.,
p = > [ ? = >  p\
as an abbreviation of the wff |102. (Of course the expression p id [q id p] 
is a formula as it stands, but not wf; since we shall hereafter be concerned 
with wffs only, no confusion will arise by using this expression as an abbre­
viation of [p 3  [q 3  p]],)
We shall also omit further brackets under the convention that, in re­
storing omitted brackets, association shall be to the left. Thus
is an abbreviation of fl04, while

---


§11]
DEFINITIONS
75
p - > [ } z D f ] z D p  
is an abbreviation of the wff
HP 3  [/ 3  /]] 3  P).
Where, however, in omitting a pair of brackets we insert a heavy dot, . , 
the convention in restoring brackets is (instead of association to the left) 
that the left bracket, [, shall go in in place of the heavy dot, and the right 
bracket, ], shall go in immediately before the next right bracket which is 
already present to the right of the heavy dot and has no mate to the right 
of the heavy dot; or, failing that, at the end of the expression.165 (Here a 
left bracket is considered to be the mate of the first right bracket to the 
right of it such that an equal number, possibly zero, of left and right 
brackets occur between.) Thus we shall use
, p
 p
as an abbreviation of f l 02, and
[ pz Dmf z D( ] z Dp
as an alternative abbreviation of the same wff for which the abbreviation
p 3  [/ z> /] Z) p
was just given.
The convention regarding heavy dots may be used together with the pre­
vious convention, namely, that of association to the left when an omitted 
left bracket is not replaced by a heavy dot. Thus for |103 we may employ 
either one of the two alternative abbreviations:
S ZD [ j ) Z D q } Z D mS Z D p Z D . S ^ > q
[s ZD . p  ZD q] ZD • S ZD p  ZD . S ^  q
Similarly,
S, 3  [s2 3  .  p 3  [?, 3  q 2] 3  rj] 3  r, 
is an abbreviation of
[[*1 => [*« => HP => [?1 => 7*JJ => ’ll]] => »■*]-
As we have said, these abbreviations and others to follow are not part of 
the logistic system Px but are mere devices for the presentation of it. They
1MCompare the use of heavy dots in §06.
The use of dots to replace brackets was introduced by Peano and was adopted by 
Whitehead and Russell in Principia Mathematica. The convention here described for 
use of dots as brackets is not the same as that of Peano and Whitehead and Russell, 
but is an modification of it which the writer has found simpler and more convenient in 
practice.

---


76
THE PROPOSITIONAL CALCULUS
[Chap. I
are concessions in practice to the shortness of human life and patience, such 
as in theory we disdain to make. The reader is asked, whenever we write 
an abbreviation of a wff, to pretend that the wff has been written in full and 
to understand us accordingly.188 Indeed we must actually write wffs in full 
whenever ambiguity or unclearness might result from abbreviating. And if 
any one finds it a defect that devices of abbreviation, not part of the logistic 
system, are resorted to at all, he is invited to rewrite this entire book without 
use of abbreviations, a lengthy but purely mechanical task.
Besides abbreviations by omission of brackets, we employ also abbre­
viations of another kind which are laid down in what we call definitions. 
Such a definition introduces a new symbol or expression (which is neither 
present in the logistic system itself nor introduced by any previous defini­
tion) and prescribes that it shall stand as an abbreviation187 for a particular 
wff, the understanding being (unless otherwise prescribed in a special case) 
that the same abbreviation is used for this wff whether it stands alone or as 
a constituent in a longer wff.168
u6There will be a few exceptions, especially in this section and in §16, where abbre­
viations are used as autonyms in the strict sense, i.e., as names of the abbreviations 
themselves rather than to denote or to abbreviate the wffs. But we shall take care that 
this is always clear from the context.
U7In a few cases we may make definitions which fail to provide an abbreviation in 
the literal sense that the new expression introduced is actually shorter than the wff 
for which it stands. Use of such a definition may nevertheless sometimes serve a purpose 
cither of increasing perspicuity or of bringing out more sharply some particular feature 
of a wff.
16aDefimtions in this sense we shall call abbreviaiive definitions, in order to distinguish 
them from various other things which also are called or may be called definitions (in 
connection with a formalized language). These latter include:
(1) Explicative definitions, which are intended to explain the meaning of a notation 
(symbol, wff, connective, or operator) already present in a given language, and which 
are expressed in a sentence of that same language. Such an explicative definition may 
often involve a sign of equality or of material or other equivalence, placed between the 
notation to be explicated, or some wff involving it, and another wff of the language. 
(We do not employ here the traditional term real definition because it carries associations 
and presuppositions which we wish to avoid.)
(2) Statements in a semantical meta-language, giving or explaining the meaning of 
a notation already present in the object language. These may be either (primitive) 
semantical rules in the sense of §07, or what we may call, in an obvious sense, derived 
semantical rules.
(3) Definitions which are like those of (1) in form, except that they are intended to 
extend the language by introducing a new notation not formerly present in it. Since 
definitions in this sense are as much a part of the object language in which they occur as 
are axioms or theorems of it, the writer agrees with Le&niewski that, if such definitions 
are allowed, it must be on the basis of rules of definition, included as a part of the prim i­
tive basis of the language and as precisely formulated as we have required in the case 
of the formation and transformation rules (in particular, appropriate conditions of 
effectiveness must be satisfied—ef. §07). Unfortunately, authors who use definitions 
in this sense have not always stated rules of definition with sufficient care. And even 
Hilbert and Bernays's Grundlagen der Matkematik may be criticized in this regard (their 
account of the m atter in vol. 1, pp. 292-293 and 391-392, is much nearer than many to

---


§11.
DEFINITIONS
In order to state definitions conveniently, we make use of an arrow, “ 
to be read “stands as an abbreviation for” (or briefly, “stands for”). Thib 
arrow, therefore, belongs to the syntax language, like the term “wff” or 
the notation “S |” of §10. At the base (left) of the arrow we write the 
definiendum, the new symbol or expression which is being introduced by the 
definition. At the head (right) of the arrow we write the definiens, the wff 
for which the definiendum is to stand. And in so writing the definiens we 
allow ourselves to abbreviate it in accordance with any previous definitions 
or other conventions of abbreviation.
Our first definition is:
D l.
This means namely that the wff f/iD  /], the definiens, may be abbreviated 
as t, whether it stands alone or as a part of a longer wff. In particular, then, 
the wff which we previously abbreviated as
p => [/ => f) 
p
may now be further abbreviated as
pTD tTD p.
complete rigor, but fails to allow full freedom of definition, as provision is lacking for 
many kinds of notation that one might wish lor some pm pose lo introduce by dt*um- 
tion). On the other hand, once the rules of definition have been precisely formulated, 
they become at least theoretically superfluous, because it would always be possible to 
oversee in advance everything that could be introduced by definition, and to provide 
for it instead by primitive notations included in the primitive basis of the language. 
This remains true even when the rules of definition are broad enough to allow direct 
introduction of new notations for functions of positive integers or of non-negative in­
tegers by means of recursion equations, as is pointed out in effect, though not in these 
words, by Carnap in The Logical Syntax of Language, §22 (compare also Hilbert and 
Bernays, vol. 2, pp. 293-297).
Because of the theoretical dispensability of definitions iu sense (3), v.c prefer not to 
use them, and in defining a logistic system in §07 we therefore did not provide for the 
inclusion of rules of definition in the primitive basis. Thus wc avoid such puzzling 
questions as whether definitions of this kind should be expressed by means of the same 
sign of equality or equivalence that is used elsewhere in the object language or by means 
of some special sign of equality by definition such as “ —af“ ; and indeed whether these 
definitions do not after all (being about notations) belong to a meta-language rather 
than the object language.
Not properly in the domain of formal logic at all is the heuristic process of deciding 
upon a more precise meaning for a notation (often a word or an expression of a natural 
language) for which a vague or a partial meaning is already known, though the result 
of this process may be expressed in or may motivate a definition of one kind or another. 
Also not in the domain of formal logic is the procedure ol osienstve definition by winch 
a proper name, or a common name, is assigned to a concrete object by physically 
showing or pointing to the object.
(In connection with an unformalized meta-language we shall continue to speak of 
“definitions" in the usual, informal, way. It is intended that, upon formalization of the 
meta-language, these shall become abbreviative definitions )

---


78
THE PROPOSITIONAL CALCULUS
rcHAp, i
In stating definitions we shall often resort to definition schemata, which 
serve the purpose of condensing a large number (commonly an infinite 
number) of definitions into a single statement. For example, if A  is any 
wff whatever, [A => /] is to be abbreviated by the expression which consists 
of the symbol ~ followed by the symbols of A  in order. This infinite list of 
definitions is summed up in the definition schema:
D2. 
~ A  
A => /
Notice here, as in other examples below, that we use the same abbreviations 
and the same methods of abbreviation for expressions which contain syntactical 
variables and have wffs as values that we do for wffs proper. This is perhaps 
self-explanatory as an informal device for abbreviating expressions of the 
syntax language, and when so understood it need not be regarded as a 
departure from the program of §08 (cf. the last paragraph of that section).
We add also the following definition schemata;16*
D3. 
[A c£ B] 
~  „ B => A  
D4. 
[ A v B J ^ - A d B d B 
D5. 
[A B ] 
A cj: B  cj: B  
D6. 
[A 53 B] ^  [A => B ][B  3  A]
D7. 
[A ^ s B] 
[AcJ: B ] v [ B e t  A]
D8. 
[A c  B] 
B  z> A
D9. 
[ A ^  B] 
B c£ A
DIO. 
[A ?  B] -> ~ A ~ B  
Dll.  
[ A | B ] - * ~ A v ~ B
Of course it is understood that a wff may be abbreviated at several places 
simultaneously by the application of definitions. E.g.,
p t v ~ p
is an abbreviation of
[[[[[/ =>/]=> [[[/ 
/n  => [p => /]].
Also the conventions about omission of brackets which were introduced 
at the beginning of this section, for wffs not otherwise abbreviated, are to 
be extended to the case in which abbreviations according to D I-II are 
already present. (In fact we have done this several times above already; 
e.g., in D5 we have omitted, under the convention of association to the left,
16#Some of these receive little actual use in this book, but are included so as to be 
available if needed. The character V is employed, in place of the V with a vertical 
line across it, only in consequence of typographical difficulties.

---


§11]
DEFINITIONS
79
two pairs of brackets belonging with the two signs c£ according to D3, and 
in D6 we have omitted an outermost pair of brackets whicli would be present 
according to D5.)
Here the convention about restoring an omitted pair of brackets repre­
sented by a heavy dot remains the same as given before. For example,
p . p
 r
becomes, on restoring brackets,
[P [? =3 ']].
which in turn is an abbreviation of the wfl,
[ [[? =>r]=3 [Li? = > r ] = > p } = > /]] /].
The convention of association to the left is, however, modified as follows. 
The bracket-pairs appearing in wffs and in expressions abbreviating wffs 
are divided into three categories. In the highest category are bracket-pairs 
which belong with the sign z> according to lOiii or which belong with one of 
the signs c£, s , 
c:, dfr according to D3, DO, D7, D8, D9. In the second 
category are bracket-pairs belonging with one of the signs v, v, j according 
to D4, DIO, Dll. And in the third category are the bracket-pairs of D5. 
Among bracket-pairs of the same category, the convention of association 
to the left applies as before in restoring brackets. But bracket-pairs of higher 
category are to be restored first, without regard to those of lower category, 
and are to enclose those of lower category to the extent that results from 
this.170 The sign ~  has no brackets belonging with it, but it is of a fourth and 
lowest category in the sense that a restored left bracket (not represented 
by a heavy dot), if it falls adjacent to an occurrence of ~ or a series of succes­
sive occurrences of 
must be placed to the left thereof rather than the right.
For example, upon restoring brackets in p v qr, the result is [p v [qr]} 
rather than {[p v j] r]. Upon restoring brackets in
p ^  q v  ~ys ~  ~p v ~q v s,
the result is 
[[p r> [q V [~rs]]] s  [ [ v ~q] v sj].
When the convention regarding categories of bracket-pairs is used in 
conjunction with the convention regarding heavy dots, the procedure in
170A similar convention about restoring brackets or parentheses is familiar in reading 
equations of elementary algebra, where the brackets or parentheses with the sign of 
equality are in a highest category, those with the signs of addition and subtraction in a 
second category, and those with multiplication, in a third category, and where other­
wise the convention of association to the left applies. For example, xy — 3a; t  
=  
® — y — 4 is to be read as C(((a:i/] — (3x)) 
) — [{x — y) — 4)j, and not (e.g.J
as [(((sy) -  3)(* +  (2y ))) =  [x -  [y -  4))].

---


80
THE PROPOSITIONAL CALCULUS
[Chap. I
restoring brackets is as follows. In the case that there are no heavy dots 
occurring between a pair of brackets already present, we take the expression 
as broken up into parts by the heavy dots, restore the brackets in each of 
these parts separately (using the convention regarding categories of bracket- 
pairs, and among bracket-pairs of the same category the convention of 
association to the left), and then finally restore all remaining brackets as rep­
resented by the heavy dots. In the contrary case we first take a portion of 
the expression which occurs between a pair of brackets already present, and 
which contains heavy dots but contains no heavy dots between any pair of 
brackets already present within it; we treat this portion of the expression 
in the way just explained, so restoring all the brackets in it; and then we 
take another such portion of the resulting expression, and so continue until 
all brackets are restored. For example, upon restoring brackets in
p z> q m rs, 
p z> qr mr z> s,
p z> . q . rs} 
p z> mqr ur z> s,
S D
^
D
. p
^
V
. S D
^
n
. S D
^
) ,
the results are respectively
[[p => ?][«]], 
[IP z> [?r]][f => s]],
[*>=>[?[«]]], 
tP ^  [ M [ r  
s]]],
[[s => [p 3  [fa => r] V [s => «?]]]] => [s => ~p]]-
Finally we also allow ourselves, for convenience in abbreviating a wff, 
first to introduce extra brackets enclosing any wf part of it. Thus, for 
example, we use
p => q .r, 
p => q ,~ r t 
p =  q v  *~r
as abbreviations of wffs which would be written more fully as 
lip => ?M, 
[[p =5 q] -r], 
[{p 3 ? ] V  ~r].
The fact that the definienda in D2-11 agree notationally with sentence connec­
tives introduced in §05 is of course intended to show a certain agreement in 
meaning. Indeed in each definition schema the convention of abbreviation which 
is introduced corresponds to and is motivated by the recognition that a certain 
connective is already provided for, in the sense that there is a notation already 
present in P1 (though a complex one) which, under the principal interpretation 
of Pl( has the same effect as the required connective.
For example, giving Pj its principal interpretation, we need not add the 
connective ~  to Px because we may always use the notation [A m /] for the 
negation of a sentence A (or of a propositional form A). All the purposes of the 
notation ^A, except that of brevity, are equally served by the notation [A rs /], 
and wc may therefore use the tatter to the exclusion of the former.

---


§12]
THEOREMS
81
In  th e  sam e m anner, D4 corresponds to the recognition th a t [[A zd B ] zd B) 
m a y b e  used as th e (inclusive) disjunction of A  and B, so th a t it is unnecessary to 
provide separately for disjunction.171 * * The reader m ay  see this by observing th a t, for 
fixed values of the variables (if any), [[A  d B ] d
B ] is false174 if an d  only if 
[A zd B ] is tru e17* and a t th e  sam e tim e B  is false; but, B being false, [A 
B] 
is tru e if and only if A is false; thus [[A  
B ] r> B ] is false if and only if both A 
an d  B  are false (and of course is tru e otherw ise); b u t this last is exactly w hat we 
should have for the disjunction of A  and B.
Sim ilarly, the m otivation of th e definition D ) is th a t the wff abbreviated as 
t is a nam e of th e tru th -v alu e tru th  (according to  th e sem antical rule d of §10).
12. Theorems of Pr As a first example of a theorem of P1 we prove: 
|120. 
pZD p 
[Reflexive law of {material) implication.)
T he reader who has in m ind the principal in terp retatio n  of 
as given in §}i), 
m ay be led to rem ark th a t this proposed theorem  is not only obvious b u t more 
Obvious th a n  an y  of the axiom s. This is quite true, but it does n o t m ake un­
necessary a proof of th e theorem . For we wish to ascertain not m erely th a t tlic 
proposed theorem  is tru e b u t th a t it follows from  our axioms by our luies; and 
n o t m erely th a t it is tru e  under the one in terp retatio n  b u t under all sound 
in terp retatio n s.178
A proof of tl20 is the following sequence of nine formulas: 
s => [p => q] => . $ =>£=>■ s zd q
S D  
[ r  D  
3
 , S D  /  D  
,  S D  ?
S D [ r  
D?" D . S  ZD p
P ID 
[r ZD p] ZD m fi ZD r ZD mp ZD p
p ZD 
[q ZD p \ ZD , p ZD q ZD m p ZD p
p ZD 
DD p 
pDD qZD npZD p 
P ZD [q ZD p] ZD » p ZD p
P tdp
The wffs have here been abbreviated by conventions introduced in the 
preceding section, and in verifying the proof the reader must imagine them
171It would also be possible and pcs haps more natural to use ~A zd B  (i.e., [i.A 3  /] 
ro B ]) as the disjunction of A and B. We have chosen A D  B  d  B instead because
there is some interest in the fact that use- of the constant / (or of negation) can be avoid­
ed for this particular purpose. The definition ul A y B  as A D  B  d  B  is given by 
Bussell in The Principles of M ath mutics (1903), ami again mure formally, in the 
American Journal of Mathematics, vul. Js (ffioiij, p 20 J.
m As explained in §04, a sentence i.s true or false according as it denotes t or 
And 
for fixed values of the free variables we call a propositional form true or false according 
as its value is t or f.
l7sIneludmg interpretations that are sound m the geneialized seme of §19.

---


82
THE PROPOSITIONAL CALCULUS
[Chap. I
rew ritten in u n ab breviated form  (or, if necessary, m u st ex p licitly  so rew rite 
th em ).
I t is su fficien t th eoretically ju s t to  w rite th e p roof itse lf as ab ove, w ith o u t 
added  ex p la n a tio n , since there are effective m ean s o f verification . B u t for 
the p ractical assistance of th e reader w e m a y  ex p la in  in full, as follow s. T h e 
first w ff o f th e  nine is f l0 3 . T h e seco n d  w ff w e o b tain  from  th e first b y  *101, 
su b stitu tin g  r for p. A gain th e th ird  w ff is o b ta in ed  from  th e secon d b y  su b ­
stitu tin g  p for q. T he fou rth  on e is ob tain ed  from  th e th ird  b y  su b stitu tin g  
p for s. T h e fifth  is ob tain ed  from  th e fou rth  b y  su b stitu tin g  q for r. T h e 
sixth  w ff is f  102. T he sev en th  o n e results b y  modus ponens from  th e fifth  
one as m ajor prem iss an d  th e s ix th  as m inor prem iss. T h en  th e eig h th  w ff 
resu lts from  th e seven th  b y  a n o th er application of *101, q 3  p b ein g  su b ­
stitu te d  for q. F in a lly  p"Z> p r e su lts b y  modus ponens from  th e eig h th  a n d  
the six th  w ffs as m ajor p rem iss a n d  m inor prem iss resp ectively.
T h e fifth  w ff in th e proof m a y  co n v en ien tly  b e  lo o k ed  u p on  as o b ta in ed  
from  th e first b y  a simultaneous substitution, n a m e ly  th e su b stitu tio n  o f 
p, qt p for s, p, q resp ectively. A n d  th e  proof ex h ib its in  d eta il how  th e e ffe c t 
of th is sim u lta n eo u s su b stitu tio n  m a y  be ob tain ed  b y  m ean s o f four su cces­
sive sin gle su b stitu tion s.
W e e x te n d  th e n otation  for su b stitu tio n  in tro d u ced  in §10, so th a t
C b l b* - b n A)
shall be th e form ula w h ich resu lts b y  sim u ltan eou s su b stitu tio n  o f Bj, B #l 
. . . ,  B„ for b 1( b a, .
.
b n in A . T h e su b stitu tio n  is to  b e for all occu rren ces 
of bx» b a, . . 
b„ throughout A . I t is required th a t b 1( b 8, . . . ,  b n b e a ll 
different (else there is no resu lt o f th e su b stitu tio n ). B u t o f course it is n o t 
required th a t all, or even  a n y , o f b 1( b a, . . . ,  b n a c tu a lly  occur in A.
T h e effect o f th e sim u lta n eo u s su b stitu tio n ,
b , b«...b.
S MlM*
A|,
w here b 1( b 2, . . 
b„ are variab les an d  all differen t, m a y  alw ays b e o b ta in ed  
b y m ean s o f 2n successive sin g le su b stitu tio n s, i.e ., 2n su ccessive a p p lica ­
tions of *101. In  som e cases it m a y  b e possible w ith  few er th an  2»  sin g le 
su b stitu tio n s, b u t it is alw a y s p ossib le w ith  2n, a s fo llo w s. L e t Cj, c a, . . . ,  c n 
be th e first n variab les in a lp h a b etic order n ot occu rrin g in  a n y  of th e  w ffs 
Bj, B8j . .
B n, A (such w ill a lw a y s ex ist, b ecau se o f th e  a v a ila b ility  of an 
in fin ite list o f variab les). T h en  in  A su b stitu te su c c e ssiv e ly  Cj for bx, c a 
for b a, . .  
cn for b flI Bx for q , Ba for c* . .
B n for c n.
W e sh all u se th e sign b as a sy n ta c tic a l n o ta tio n  to  ex p ress th a t a w ff is  a

---


512]
THEOREMS
83
th eo rem  (of P Ul or, la te r , o f o th er lo g istic s y s te m ). T hus "H p r> p" m a y  be 
read  a s an a b b rev ia tio n  o f tfp z > p  is a th e o r e m /' etc. (Cf. fo o tn o te  66.)
W ith  th e aid o f th is n o ta tio n  w e m a y  s ta te  a s follow s th e m eta th eo rem  
a b o u t sim u lta n eo u s s u b stitu tio n  o f w h ich  w e h a v e  ju st sk e tc h e d  a proof:
*121. 
I f V A , th en  V S ^ b .-Ib ,  A |.
W e sh a ll m ake u se o f th is  m eta th eo rem  a s a  derived rule of inference. I.e., 
in  p r e sen tin g  p roofs w e  sh a ll pass from  A  im m ed ia tely  to
A |.
n o t g iv in g  d eta ils o f in term ed ia te step s b u t referring sim p ly  to  *121 (or to 
" sim u lta n eo u s s u b stitu tio n "  or to  " su b stitu tio n " ).
J u stific a tio n  for su ch  u se of d erived  ru les o f inference is sim ilar to  th a t for 
th e  u se o f d efin itio n s a n d  oth er a b b r e v ia tio n s (§11), n a m ely , a s a m ere 
d e v ic e  of p resen ta tio n  w h ic h  is fu lly  d isp en sa b le in principle. O n th is accou n t, 
h o w ev e r , it  is essen tia l th a t th e proof o f a d eriv ed  rule of in feren ce be effec­
tive (cf, § § 0 7 ,0 8 ) in  th e  sen se th a t an  e ffe c tiv e  m eth o d  is p ro v id ed  accord in g 
to w h ich  from  a g iv en  p ro o f o f th e p rem isses of th e derived rule it is  alw ays 
p o ssib le  to  o b ta in  a p r o o f o f th e con clu sion  of th e d erived  ru le.174 For we 
m u st b e sure th a t, w h e n e v e r  a proof p r e sen te d  b y  m ean s of d eriv ed  rules is 
ch a llen g ed , w e can  m e e t th e ch allen ge b y  a c tu a lly  su p p lyin g th e un ab rid ged 
p roo f. In  o th er w ord s w e  ta k e care th a t th ere is a m ech an ical p roced u re for 
su p p ly in g  th e u n a b rid g ed  p ro o f w h en ever c a lle d  for, and on th is b a sis, w hen 
a p ro o f o f a p a rticu la r th eo rem  of a lo g istic  sy ste m  is p resen ted  w ith  th e 
aid  o f d erived  ru les, w e ask  th e  reader to  im a g in e th a t th e p ro o f h as been 
w r itte n  in fu ll (an d , o n  occasion , a c tu a lly  to  su p p ly  it  in full for him self). 
T h e  p roof o f *121 is cle a r ly  effectiv e, as th e  reader w ill see o n  review in g it. 
W ith  th e aid o f *121 a s a d erived  ru le, a n d  som e oth er o b v io u s devices 
o f ab b rev ia tio n , w e m a y  n ow  presen t th e  p roof of |120 as follow s:
B y  sim u lta n eo u s su b stitu tio n  in 1 103:
t'pZ}[qZ3p]'=>,pZ>qzSup'=)p
B y  f l 0 2  and modus ponens:
B y  su b stitu tio n  o f q zd p for q:
b p z > [ q z > p ] z > . p z > p
m We shall later—in particular in Chapters IV and V—consider some metatheoreras 
whose proof is non-effective. But such m etatheorem s must not be used in the role of 
derived rules.

---


84
THE PROPOSITIONAL CALCULUS
[Ch a p. I
F in ally b y  f l 0 2  and modus ponens:
h p => p
(T hus a p resen ta tio n  of th e proof a n d  som e p ractical ex p la n a tio n  of it are 
condensed in to  a b o u t th e sam e sp ace as occupied a b o v e b y  th e unab ridged 
proof alone.)
W e now  go on to  proofs of tw o  fu rth er th eorem s o f P x. 
f l 22. 
/ = > £
B y  sim u ltan eou s su b stitu tio n  in f l0 2 ;
\ - p ^ f z Di ^ > p Z Du } Z Dn p ^ > j Z Df Z Dp  
B y  f l 0 4  an d  modus ponens:
(-/=> .p  id f => f=> p 
B y  sim u ltan eou s su b stitu tio n  in  f l0 3 :
t~ f 
[p ZS f 
f 
p] => 
ZS [p => {-=* f]ZD *f id p
B y  modus ponens:
( - / = > [ £ = > / = > / ] = > - / = > £
B y  sim u ltan eou s su b stitu tio n  in f 102:
! - / = > „ £ = > / = > /
H ence b y  modus ponens:
V f^ yp
1123. 
p => / => up => q
B y  sim u ltan eou s su b stitu tio n  in f l0 2 :
l - / n p . p  •/=>?
B y  su b stitu tio n  in  |1 2 2 ;*75
hf =>q
B y  modus ponens:
\ - p = >. f = >q
B y  sim u lta n eo u s su b stitu tio n  in f  103:
p => [f => q] =>. p => f => . p  => q 
H ence b y  modus ponens:
VpTDf => *p-=>q
( fl2 3  is know n as th e law of denial of the antecedent. N o tice  th a t it m a y  
be abbreviated b y  D 2 as ~p = > . p => q.) 175
175Thc entire proof of f 122 therefore enters at this point as part of the proof of f 123 
when written in full.

---


§12]
EXERCISES 1 2
85
EXERCISES 12
1 2 *0. Prove (as a metatheorem) that the effective test of well-formedness 
given in §10 does in fact constitute a necessary and sufficient condition that 
a formula be wf according to the formation rules lOi-iii. (Use mathematical 
induction with respect to the number of occurrences of 
in the formula.)
1 2 *1. Prove the assertion made in §10 that, if a formula is wf and consists 
of more than one symbol, it has the form [A zd B] in one and only one way. 
Also that any wf (consecutive) part of the formula is either the entire for­
mula or a wf part of A or a wf part of B.176 (For the proof, employ the same 
method of counting brackets as in the effective test of well-formedness, and 
again proceed by mathematical induction with respect to the number of 
occurrences of => in the formula.)
1 2 .2 . Let P3L be the logistic system which we obtain from P3 by a change
of notation, writing systematically C ________ in place of [____ =>____ ], in
the way described in footnote 91, and leaving everything else unaltered. 
State the primitive basis of PlL- State and prove the metatheorems about 
PlL which are analogues of those of 12.0 and 12.1.177
The following proofs are to he presented with the aid of *121 and in the same 
manner as is done in the latter part of §12. Do not use methods of later sections.
1 2 .3 . Proveq => r => »p => q => mp => rasa theorem of Pr Use this theorem 
in order to give proofs of f 122 and fl23 which are briefer than those above, 
in the sense that they can be more briefly presented.178
1 2 .4 . Use the result of 12.3 in order to prove the transitive law of {material) 
implication, p zd qD> ,q  ZD r zd mpD> r, as a theorem of Pv (One method is to 
apply the self-distributive law to the result of 12.3, then to use p => q zd . 
q=>r=> , p => q.)
l7,By a different method than th at indicated here, proved by S. C. Kleene in the 
Annals of Mathematics, vol. 35 (1934), pp. 531-532. Kleene's proof is carried out for a 
different logistic system than th at of the text, but the question involved is the same in 
alLessentials.
The first of the two metatheorems of this exercise is proved below as **143. and 
analogous metatheorems for the logistic s_\stem P* are proved in the next chapter. 
However, the reader should carry through the present exercise without looking forward 
at these later proofs. Or, alternatively, if the proofs given below are followed, they 
should be w ritten out more fully, and in particular, details should be given of the 
proof of the lemma which is used below in proving **143.
k ?Cf. Karl Meager in Ergebntsse eines maikemaiischen Kclloquiums, no. 3 (1932), 
pp. 22-23, Lukasiewicz in footnote 5 (credited to Jaskowski) of a paper in Comptes 
Rendus des Seances de la Societe des Sciences et ties Leltres de Varsovie, Classc III, vol. 24 
(1932), pp. 153-IH3; Karl Schrdterin Axiomahsierung dev Fregeschen Aussagenkalkule 
(1943).
l7*Not necessarily in the sense th at the proof written in full consists of a shorter 
sequence of wffs.

---


86
THE PROPOSITIONAL CALCULUS
[Chap. I
1 2 .5 . Prove p => 
p rD , p  z) f^Dp as a theorem of Px. (Use 1123,12.4.)
1 2 .6 . Prove Peirce's law, £ = > ? = > £ = > £  as a theorem of Px. (Apply the 
self-distributive law to p ^  
^  *p => /, and use the result of 12.5.)
1 2 .7 . L etP w be the logistic system which has the same primitive sym­
bols, formation rules, and rules of inference as Px and which has as its axioms 
the transitive law of implication, Peirce's law, fl02, and fl22. Prove the 
following in order, as theorems of Pw, and hence show that Px and Pw are 
equivalent systems in the sense that they have the same theorems;
[ £=>• £=> <7] =>- £=>?
p =>. p zd q => q 
{Law of assertion.)
[ £=>. #=> 
{Law of commutation.)
s 3 [ £ = x 7 J = > . s =>£=>. $ =>?
p ^ > t = > i = > p
Carry out the proofs in such a way that no use is made of the fourth axiom, 
f 122, except in the proof of the last theorem, p z> / z> / ^  p.
1 2 .8 . Prove as theorems of Pw, without making use of the fourth axiom, 
f 122: p r D r D . p p r D r ;  y 3  - p 3  . q => r; £ 3  r => r => .
p r o . ^ D p r o r .
1 2 .9 - For each of the three following interpretations of Pi (cf. §10), state the 
remaining semantical rules, and discuss the soundness of the interpretation in 
the sense of §07: (1) Rules a, b, c are retained, but [A z> B] denotes t if A and B 
are any constants. (2) Rules a, b, c are retained, but [A 
B] denotes tif A and 
B denote the same truth-value, [A z> B] denotes f if A and B denote different 
truth-values. (3) Rules a, d are retained, but the variables (so-called) are inter­
preted as constants denoting t.
13, The deduction theorem . A variant of a wff A of Px is a wff obtained 
from A by alphabetic changes of the variables of such a sort that two occur­
rences of the same variable in A remain occurrences of the same variable, 
and two occurrences of distinct variables in A remain occurrences of distinct 
variables. Thus if ax, aa, . .
an are distinct variables, and blf ba, . .., bn 
are distinct variables, and there is no variable among b1( b8(. . 
bn which 
occurs in A and does not occur among a^, aa> .. 
an, then
C aiaa - a n * I
^ b iV - b n
is a variant of A. (Variants of fl02, for example, are 
and q z> .
p ZD q, but not p z> mr z> r or p 3  *p zd p.)

---


§13]
THE DEDUCTION THEOREM
87
It is dear that if B is a variant of A, then A is a variant of B. And any 
variant of a variant of A is a variant of A. Also of course any wff A is a var­
iant of itself.
In many ways, two wffs which are variants of one another serve the same 
purposes. In particular, in view of *101, every variant of a theorem is a 
theorem. Also, if we alter the system P1 by replacing one or more axioms by 
variants of them, the theorems remain the same. In the case of theorems to 
which verbal names have been assigned (e.g., "the self-distributive law of 
implication/' "Peirce's law /’ etc.), we shall use the same name also for any 
variant of the theorem.
A finite sequence of wffs is called a variant proof if each wff is either a 
variant of an axiom or is immediately inferred from preceding wffs in the 
sequence by one of the rules of inference. Evidently the final wff in a variant 
proof is always a theorem, since every variant of an axiom is a theorem; and 
we shall call the variant proof a variant proof of its final wff.
A finite sequence of wffs, Bv B2, . . 
B m, is called a proof from the 
hypotheses Av A2, . . 
An if for each i either; (1) B* is one of Ax, A2, . . 
An; 
or (2) Bt is a variant of an axiom; or (3) B, is inferred according to *100 
from major premiss B, and minor premiss B k, where j <  i, k <  i; or (4) Bt 
is inferred, according to *101, by substitution in the premiss B,, where j <  i, 
and where the variable substituted for does not occur in Ax, A2, . . 
An. 
Such a finite sequence of wffs, B„f being the final formula of the sequence, is 
called more explicitly a proof of B m from the hypotheses Ax, A2, . . 
An; 
and we use the notation
■^
1 '  
^
2 » 
• 
• 
' i
to mean; there is a proof of B m from the hypotheses Ax, A2, . . 
A„.
Observe that the sign b is not a symbol belonging to the logistic system Px 
nor is it part of any schema of abbreviation of wffs of Px, but rather it belongs 
to the syntax language (like the notation "S |" or the abbreviation "wff") 
and is used in making statements about the wffs of Px.
The use of the sign b which was introduced in §12 may be regarded as 
amounting to a special case of the foregoing, namely the special case that 
n =  0. For a proof of B m from no hypotheses is the same as a variant proof 
of B?n; and we may now read the notation h B,„ either as meaning that 
there exists a variant proof of B1n or as meaning that B m is a theorem (the 
two being trivially equivalent).
In the definition of proof from hypotheses, the condition attached to (4) 
should be especially noted, that the variable substituted for must not be

---


88
THE PROPOSITIONAL CALCULUS
[Chap. I
one of the variables occurring in Ax, A2, ■ . 
An. For example, although 
q = ) / = ) / = >  / results from 9 => / =>/  by substitution of q 
/ for 
it is false 
that 
On the other hand it is true that
q zd f zd f b q, by *100 and an appropriate variant of •fl04.
After these preliminaries, we are ready to state and prove the meta­
theorem which constitutes the principal topic of this section:
*130. 
If Ax, Aa, . . 
An 1- B, then AXl A2, . . 
An_* 1- An ^  B.
[The deduction theorem.)
Proof. Let Bx, B2, . . ., Bm be a proof of B from the hypotheses Ax, A2, 
.. 
An (Bm being therefore the same as B). And construct first the finite 
sequence of wffs, An =) Bx, An => B2, ■ . 
An => Bm. We shall show how to 
insert a finite number of additional wffs in this sequence so that the resulting 
sequence is a proof of An zd Bm, i.e., of An zd B, from the hypotheses Ax, A2, 
. . 
An_x. The inserted wffs will be put in before each of the wffs An => B, 
in order in such a way that, after completing the insertions as far as a par­
ticular An 1d B,, the whole sequence of wffs up to that point is a proof of 
An zd B, from the hypotheses Ax, A2, . ■ 
An„x.179
In fact consider a particular An zd BfI and, if t >  1, suppose that the in­
sertions have been completed as far as An =d B,-„x. The following five cases 
arise:
Case la: Bt is An. Then An => B* is An => An. Insert nine wffs before 
An =3 B,, constituting namely a variant proof of an appropriate variant of 
1120 from which An zd B, can be inferred by substitution.
Case lb: B, is one of Ax, A2) . . 
An_x, say Ar. Then Ar i d  . An ^  B, is 
Ar = ) . An 1d  Ar. From an appropriate variant of f  102, Ar zd . An i d  B* can 
be inferred in two steps by substitution (*101). Before An => Bt insert first 
the three wffs which show this, then Ar. From the last two of these four wffs, 
namely Ar => . A n => B, and Ar, An => B, can be inferred by modus ponens 
(*100).
Case 2: B, is a variant of an axiom. Following the same plan as in case lb, 
insert four wffs before An zd B,, namely first a variant proof of B< =0 . An=> B t 
(in two steps by substitution from a variant of t ! 02), then B* (a variant of 
an axiom).
Case 3: B, is inferred by modus ponens from major premiss B, and minor 
premiss B*., where j <  i, k <  i. Then By is B* => B<. Before An => B f insert 
first the four wffs which show the inference of An => Bs => . An => Bfc => .
17BThus m effect the method of the proof is that of mathematical induction with 
respect to m (or i).

---


§13]
THE DEDUCTION THEOREM
89
A„ => Bt, b y  t h r e e  s u c c e s s iv e  s u b s t i t u t i o n s ,  f r o m  a v a r i a n t  o f -fl03; t h e n  
a f t e r  t h e s e  t h e  w ff An => Bfc i d  . An i d  B* ( w h ic h  c a n  b e  in f e r r e d  b y  modus 
ftonens, a n d  f r o m  w h ic h  t h e n  A n 
Bi c a n  b e  i n f e r r e d  b y  modus fionens, s in c e  
th e  n e c e s s a r y  m i n o r  p r e m is s e s , Art i d  B3 a n d  An i d  B*., a r e  a m o n g  t h e  e a r l i e r  
w ffs  a l r e a d y  p r e s e n t  in  t h e  s e q u e n c e  b e in g  c o n s t r u c t e d ) .
Case 4: B, is inferred, according to *101, by substitution in BJ(where 
j <  i and where the variable substituted for does not occur in Alt A2, . . ., An. 
No wffs need be inserted before An => Bt, as the same substitution suffices 
to infer An i d  Bf from An 
B3 (here, of course, it is essential that the vari­
able substituted for does not occur in An).
As the special case of the deduction theorem in which n — 1 we have the 
following corollary:
*131. 
If Al - B,  th e n  b A i d  B.
In connection with the deduction theorem we shall need also the three 
following metatheorems:
*132. 
If Ax, A2, .. ., An b B, then Cx, C2, . . 
Cr, Ax, A2, . . 
An b B.
Proof. Let av a2, . . ., a E be the complete list (in alphabetic order) of 
those variables which occur in Cx, C2, . .
Cr but not in Ax, A2, . . 
Art. 
If the given proof of B from the hypotheses Ax, A2, . . ., An is not also a 
proof ot B from the hypotheses Cx, C2, .. 
Cr, Ax, A2, , . Au, it can only 
be because it involves substitutions for some of the variables ax, a2, . . 
az. 
Therefore let cx, c 2, . . 
c E be variables which are all distinct and which do 
not occur in Cx, C2, . . 
Cr, Ax, A2, . . ., An or in the given proof of B from 
the hypotheses Ax, A2, .. 
An (to be specific, say that c x, c 2, .. 
c t are 
the first l such variables in the alphabetic order of the variables). And 
throughout the given proof of B from the hypotheses A,, A2, . . ., An replace 
ax, a 2, . .  
2lx by c x, c2, . . 
c £ respectively. The result is a proof from the 
hypotheses Cx, C2, . . ., Cr, Ax, A2, . . 
An of
c
a i a * - a ' B
|
° c 1ca ...c1
To obtain a proof of B from the same hypotheses, it is then necessary only to 
add l additional steps, substituting successively ax for cx, a 2 for c2, . . 
aj for c £.
*133. 
If b B, then Cx, C2, . . 
Cr b B.
Proof. This is the special case of *132 in which n — 0.

---


90
THE PROPOSITIONAL CALCULUS
[Chap. I
*134. 
If every wff which occurs at least once in the list A1; A*, .. 
An 
also occurs at least once in the list C v  Ca, . .
Cr, and if A v  A*, 
.. -i An h B, then Cx, C2, . . 
Cr b B.
P roof. Since it is clearly indifferent, in connection with proof from hypoth­
eses, in what order the hypotheses are arranged, or how many times a 
particular hypothesis is repeated, this is a corollary of *132.
Importance of the deduction theorem to the metatheory (syntax and seman­
tics) of the system P is clear—as a matter of showing the adequacy of the system, 
in a certain direction, for the purposes for which it is intended, namely for formal­
ization of the use of sentence connectives (see §05) and of inferences involving 
them.
It is also possible to make use of the deduction theorem in the role of a 
derived rule of inference (cf. §12), since the proof of the deduction theorem 
provides an effective method according to which, whenever a proof of B 
from the hypotheses A1, A2, . . An is given, it is possible to obtain a proof 
of An zd B from the hypotheses A v  Aa, . .
A n_t —hence by repetitions of 
the method to obtain a proof of Ax zd . A* ZD . . .  . An_* ^  ■ A„ ^  B.
As examples of this use of the deduction theorem as a derived rule, we 
present the following alternative proofs of the last two theorems of §12:
P roof of fl22. By simultaneous substitution in t!02.'
h f Z 3 . p = > f = > f
Hence by m odu s ponens:
f b p Z o f n f
Hence by fl04 and m odus ponens:
f t p
Hence by *131:
\ - } = > p
P roof of f 123. By m odus p o n en s:
P  => /. P  Y f
By the variant, / id q, of 1122 and m odus ponens-.
p z o f ,  p Y q
Hence by *130:
p  Z3 f b p = > q
Hence by *130 again (or, what comes to the same thing, by *131):
(-p  
f 
. p r o  q

---


§141 
FURTHER THEOREMS AND M ETATHEOREM S
91
14, Som e further theorem s and m etatheorem s of Pr We go on 
to prove three additional theorems of P1( using the deduction theorem in 
order to present proofs more briefly.
fl40.180 £ = > > ? = > / = > . £ = > ? = > /
By two applications of modus ponens:
p, q=>f,
By three applications of the deduction theorem:
fl41. 
pZD qz> *qZD r ZD *p 
r
By two applications of modus ponens:
p ro  q} q z > r t p Y r  
Hence by the deduction theorem:
l - p
p
. p
o
. p
r
(As already indicated in 12.4, f!41 is known as the transitive law of 
implication.)
fl42. 
p / D r n , p r n r
By the transitive law of implication (i.e., by substitution in fl41 or a 
suitable variant, and modus ponens)’.
pz >r ,  r -n f V p ■=> f
Hence by two applications of modus ponens:
£=>/=> r, p=>r, r = > f b f
Hence by the deduction theorem:
£ =>/ => r, p 
r V r 
f 
j
Hence by a variant of fl04 and modus ponens;
p ZD fZD r, p Z D r b r
imq ZD f may be read in words either as “ not q" or as “q is false" (where "is false" is 
of course not the semantical term  but merely a synonym of "not" or "im plies false­
hood"). 1140 may be read in words: "If p, if not q, then p does not imply q
Similarly 
we m ay read ’f 141 in words thus: "If p implies q, if q implies y, p implies r.*‘ And f 142 
thus: " If not p implies r, if p implies r, then vT

---


92
THE PROPOSITIONAL CALCULUS
[Chap. I
Hence by the deduction theorem:
VpZD fiD o
 mpiDriDr
We add also the following nietatheorem, which will be needed in the next 
section:
**143. 
If a formula is wf and consists of more than one symbol, it has the 
form [A i d  B] in one and only one way.
Proof. It is immediate, from the definition of a wff, that a wff of more 
than one symbol has the form [A i d  B] in at least one way. We must show 
that it cannot have this form in more than one way.
We use the same process of counting brackets which is described in §10. 
Namely we start at the beginning (or left) of a formula and proceed from 
left to right, counting each occurrence of [ as + 1  and each occurrence of ] 
as —1, and adding as we go. The number which we thus assign to an occur­
rence of a bracket will be called the number of that occurrence of a bracket 
in the formula.
It follows from the definition of a wff that, if a wff contains the symbol i d , 
it must begin with an occurrence of [ and end with an occurrence of ]; these 
we shall call respectively the initial bracket and the final bracket of the wff. 
By mathematical induction with respect to the total number of occurrences 
of i d  we establish the following lemma: The number of an occurrence of a 
bracket in a wff is positive, except in the case of the final bracket} which has the 
number 0 .
Now suppose that [A i d  B ] and [C i d  D ] are the same wff. Case 1: If A 
contains no occurrence of i d , it must consist of a single symbol, either a 
variable or /; since C begins with the same symbol as A, it follows that C 
has no initial bracket and therefore cannot contain the symbol i d ; therefore 
C must be identical with A. Case 2; If C contains no occurrence of i d , it 
follows by the same argument that A must be identical with C. Case 3: If 
A and C both contain the symbol i d , then the final bracket of A is the first 
occurrence of a bracket with the number 0 in A, and therefore is the second 
occurrence of a bracket with the number 1 in [A i d  B]; and the final bracket 
of C is the first occurrence of a bracket with the number 0 in C, and therefore 
is the second occurrence of a bracket with the number 1 in [C D  D]; this 
makes the final bracket of A and the final bracket of C coincide, and so 
makes A and C identical. Finally, since it follows in all three cases that A 
and C are identical, it is then obvious that B and D  must be identical.
We do not continue further with proofs of particular theorems of Plf

---


§14]
EXERCISES 1 4
93
although there are many more theorems of the propositional calculus which 
will be of importance in later chapters. For all such theorems can be ob­
tained by the more powerful method of the next section, to establish which 
the theorems and metatheorems that we already have are sufficient. Indeed 
in the next section we shall make direct use only of *100, *101, J102, +120, 
fl23, *130, f 140, f 142,**143— other axioms, theorems, and metatheorems 
being used only so far as they contribute to the proof of these.
EXERCISES 14
Z4.0. Rewrite f 140 and +142 in abbreviated form, using D2, D4, and D9.
1 4 .1 . From the hypotheses p  and p  zd q there is a proof of q> in one step
by modus p o n e n s. Hence by using the method provided in the proof of *130 
we may obtain a proof of the la w  o f a s s e r tio n , p  zd « p  zd  q z d  q. Simplify this 
proof by deleting all unnecessary repetitions of the same wff or variants of 
it, also by using |120an d f 102 in order to prove 
in a more direct
manner. Present the resulting proof of the law of assertion in the style of 
§12, without making use of the deduction theorem or of theorems whose 
proof has been presented only by means of the deduction theorem.
1 4 .2 . Present a proof of 1140 without making use of the deduction 
theorem or of theorems whose proof has been presented only by means of 
the deduction theorem. (The proof of §14 is impracticably cumbrous when 
presented without the aid of the deduction theorem; nevertheless we may 
make heuristic use of the idea of applying, to the proof of 1140 as presented 
in §14, the method provided in the proof of *130.)
Present proofs of the following theorems in the style of §14, making use of the 
deduction theorem and of any theorems and metatheorems which have been 
previously proved, either in the text or as exercises:
1 4 .3 . p Z D ^ q Z D r Z D . p Z D q z D r
14-4 .
14 .5 . pZDrzDrZD.p^ojzDr
14 .6 . P ID q ZD [r± ZD s] ZD m P ZD [r2 ZD s] ZD . r x ZD »r2 ZD s
14 .7 . p  v q ZD q V p
14 .8 . [p 3 q] v [q zd p ]
14 .9 . Establish the following four derived rules of Pt directly—without 
use of *130 or of the notion of a proof from hypotheses;
(1) If 1- B, then h Ax zd ■ A2 z d . .  . . An zd B.
(2) If every wff which occurs at least once in the list Ax, A2, . . ., An

---


94
THE PROPOSITIONAL CALCULUS
[Chap. I
also occurs at least once in the list Cv Ca, . . .  Cr, and if 1- Ax 
. A2 
» 
. . . A b d B, then 1- Cx 
. C2 zd . .  . . Cr =3 B.
(3) If B is one of AIf A2, . . An, then FA1 D , A 2 D l , . . A ftD B .
(4) If every wff which occurs at least once in the list Ax, A2, .. 
A„,
Bv Ba, .. 
Bm also occurs at least once in the list C1( C2, . . . ,  Cr, if 
1- Aj 
. A2 3  . .  .. An A and FB1 D , B p , , 11BmD 1A D B ,  then
1- Cj 3  . C2 zd m. . . Cr 
B.
Explain in detail how these derived rules may be used as a substitute 
for the deduction theorem in presenting proofs of theorems of Px. Illustrate 
by presenting proofs of the three theorems of §14 with the aid of these 
derived rules (and without the deduction theorem).181
15. Tautologies, the decision problem. Let B be a wff of Px, let
a1; a2, . . 
an be distinct variables among which are all the variables occur­
ring in B, and let av a2, . .
an be truth-values (each one either t or f). 
We define the value of B for the values alf az, 
of ax, a2, ..., an by a
recursion process which assigns values to the wf parts C of B, in order of 
increasing number of occurrences of zd in G, as follows. If C is /, the value of 
C is f; if C is a*, the value of C is a{; if C is [Cx z> C2], the value of C is t in 
case either the value of C2 is t or the value of Cx is f, and the value of C is f 
in case the values of Q  and C2 are t and f respectively. By repetitions of 
this process a value, t or f, is ultimately assigned to B, and this we call the 
value of B for the values alt a2, . . 
an of a1( aa, . . ., an.
The uniqueness of the value of B for a given system of values of its 
variables follows as a consequence of **143.
A wff B of Pj is called a tautology if its value is t for every system of 
values of its variables (the values being truth-values), a contradiction if its 
value is f for every system of values of its variables.
It will be seen that the foregoing recursion process, by which we obtain the 
value of B for a system of values of its variables, just follows the semantical 
rules given in §10 for the principal interpretation of P2. But in §10 we understood 
‘‘denoting" and ‘'having values" as known kinds of meaning, and we used the
1B,These derived rules have a simpler character than that of the deduction theorem in 
the role of a derived rule. For, like our primitive rules of inference, they require as 
premisses only certain asserted wffs, and, when these are given, the check of the inference 
is effective. But when the deduction theorem is used as a derived rule, it is necessary to 
submit a finite sequence of wffs not as asserted but as constituting a proof from hy­
potheses, and only then is an effective check available.
On the other hand these derived rules, 14.9 (l)-(4), may easily be made an efficient 
substitute for the deduction theorem as a means of abbreviating the presentation of 
proofs. Advantages of the deduction theorem in this role are largely psychological and 
heuristic.

---


§15]
T A U T O L O G IE S , T H E  D E C I S I O N  P R O B L E M
95
sem an tical rules in o rder to  assign an in te rp re ta tio n  to  Pj as a language designed
for m ean in g fu l co m m u n icatio n . On th e  o th e r h a n d  in th e  p resen t section we 
use th e  sam e rules, otherw ise su b sta n tia lly  un ch an g ed , in o rd er to d efine a b ­
stra c tly  a correspondence called "h av in g  v a lu e s ,” betw een w ffs (w ith given 
v a lu e s  o i th e ir variables) an d  tru th -v alu es. T he w ord "v a lu e s" a t its tw o italicized 
occurrences is m e a n t as a  new ly introduced te ch n ical term , w ith no reference 
to th e  id ea of m eaning, an d  th e  correspondence is defined a b stra c tly , or sy n ­
tactically , in th e  sense th a t it m ay  be used in d ep en d en tly  of w h at in te rp re ta tio n  
(if an y ) is assigned to  th e  logistic system  P x. C om pare footnote 143.
The process provided in the definition for obtaining the value of B for 
a given system of values of its variables is effective (see the discussion of 
the notion of effectiveness in §07, and footnotes 118, 119). Since a wff B 
can have only a finite number of variables, and hence only a finite number 
of systems of values of its variables, this leads to an effective process for 
deciding whether B is a tautology or a contradiction or neither. As an illus­
tration of this algorithm, we show the following verification that jT03 is 
a tautology, adopting a convenient arrangement of the work that is due to 
Quine:
s ZD [P ZD ?] ZD . s ZD P ZD . s ZD 9
t t
t t t
t
t t t t
t t t
t f
t f f
t
t t t
f
t f f
t t
f
t t
t
t f
f t
t t t
t t
f
t f
t
t f f
t
t f f
f t
t
t t
t
f t t
t
f t t
f t
t
f f
t
f t t t
f t f
f t
f
t t
t
f t f t
f t t
f t
f t f
t
f t f
t
f t f
In detail the work is as follows. First the wff f 103 is written on one line. The 
three variables occurring in it are s, p ,  q\ all possible systems of values of 
these variables are written down in the form of three columns of t's and f's, 
one column below the first occurrence of each of these variables in the wff. 
Then below each remaining occurrence of a variable in the wff is copied the 
same column of t’s and f’s that stands below its first occurrence. Then systems 
of values are assigned to the various wf parts of the entire wff, in order of 
increasing length of the parts, the system of values assigned to each part 
being written as a column of t's and f’s below the principal implication sign 
of that part. For example, the values assigned to [p  zd q] appear in the col­
umn below the second implication sign of the entire wff; the t at the top of

---


96
THE PROPOSITIONAL CALCULUS
[Chap. I
this column is obtained from the values t, t of 
qt in accordance with the 
rule given in the first paragraph of this section; the f next to the top of the 
column is obtained from the values t, f of fi, q, in accordance with the same 
rule; and so on. Again, the values assigned to s D  [/> D  g] appear in the col­
umn below the first implication sign of the entire wff; the t at the top of 
this column is obtained from the values t, t of p t 
and so on. The
reader should carry out the work in full and compare his result with that 
shown above. At the end of the work, the system of values of the entire 
wff appears in the column below its principal implication sign, and the fact 
that this column consists wholly of t’s shows the wff to be a tautology.
A table showing the value of p :d  q for every system of values of p, q is 
called a truth-table of r>. Like truth-tables may be calculated also for each 
of the notations introduced in D2-11; e.g., in accordance with D4, the truth- 
table of v will show the value oifizzq^q for every system of values of p, q, 
as this is worked out by the rule given in the first paragraph of this section. 
The complete list of truth-tables, including that of :d , is as follows:
p
f*p
p
P=>q p<£q p y q pq p =  q P $ q
p<=q P ^ q
<1
£1?
t
f
t
t
t
f
t
t
t
f
t
f
f
f
f
t
t
f
f
f
t
f
f
t
t
t
f
t
f
t
t
t
t
f
f
t
f
f
f
t
f
f
t
f
f
f
t
f
t
f
t
t
Though these truth-tables show explicitly, e.g., the value of p v q for 
given values of p and q, of course it is understood that they may be used 
with arbitrary wffs replacing the variables, e.g., to find the value of Cx v C2 
for given values of 
and C2.
When the above described algorithm for calculating the system of truth- 
values of a wff is to be applied to a wff abbreviated by means of D l-11, the 
wff may be first rewritten in unabbreviated form and the algorithm then 
applied. In theoretical discussions we shall assume that this is done. But in 
practice it is more efficient to leave the wff in abbreviated form and to use 
the complete foregoing list of truth-tables. For example, the verification that
t = > p y q = . p ^ q ^ p q = > f
is a tautology, using the abbreviated form of this wff, is arranged as 
follows:

---


§15]
T A U T O L O G I E S , T H E  D E C I S I O N  P R O B L E M
97
t Z2 p v q = . p ^ q ^ p
?=>/
t f t f t t
t f t t t t t f f
t f t f f t
t t f t t f f f f
t f f f t t
f t t t f f t f f
t t f t f t
f f f f f f f t f
We now prove the metatheorem:
**150. 
Every theorem of P2 is a tautology.
Proof. We first establish the following lemma: If 
a2, .. 
an, b are 
distinct variables among which are all the variables occurring in A and all those 
occurring in B, and if, for the values alt a2, . .
an, a of a1} a2, . . 
an, b, the 
value of B is b and the value of SgA| is c, then the value of A for the values 
a2, .. ., an, b of a1( a2, . .., an, b is c.
The lemma is obvious if A consists of a single symbol. And we then pro­
ceed by mathematical induction with respect to the total number of occur­
rences of 3  in A. If A is Ax 3  A2, then S£A| is S^A^ 3  S£A2|. Suppose 
that, for the values av a2, . . 
an> a of ax, a2, . .., an, b, the value of B is b, 
and the value of S£A| is c, and the value of S£AX| is cv  and the value of 
SgAjjl is c2. Then c is f, if q  is t and c2 is f; and c is t in all other cases. By the 
hypothesis of induction we have, for the values av  a2, . .., an, b of a2, a2l. . 
an, b, that the value of A1 is cx and the value of A2 is c2; hence the value of 
A is f if q  is t and c2 is f, and the value of A is t in all other cases; i.e., the 
value of A is c.
The lemma then follows by mathematical induction.—For the rule of 
substitution, *101, we have as an immediate consequence of the lemma that, 
if the conclusion S£A| has the value f for some system of values of the 
variables, then the premiss A must have the value f for some system of val­
ues of the variables. Therefore if the premiss A of *101 is a tautology, the 
conclusion S{JA| must be a tautology.
For the rule of modus ponens, *100, if the minor premiss A is a tautology, 
and if the conclusion B has the value f for some system of values of the 
variables (of A and B), then for the same system of values of the variables 
it follows directly from the definition of the value of a wff that the value 
of the major premiss A 3  B is f. Therefore if both premisses of *100 are 
tautologies, the conclusion must be a tautology.
We have thus shown that the two rules of inference of Px preserve tautol­
ogies, in the sense that, if the premiss or premisses are tautologies, the 
conclusion is a tautology. We leave it to the reader to verify that the three 
axioms of Px are tautologies. **150 then follows.

---


98
T H E  P R O P O S I T I O N A L  C A L C U L U S
[Chap. I
*151. 
Let B be a wff of P1# let ax, a2, . . an be distinct variables among 
which are all the variables occurring in B, and let av a9, 
be
truth-values. Further, let A,- be a, or a* 3  / according as at is t or f; 
and let B' be B or B D  / according as the value of B for the values 
av az, . . 
an of alt a2l . . 
art is t or f. Then A1( Aa, . . . ,  An H B'.
In order to prove that
(1) 
Aj, A2, . . . , A n f-B'
we proceed by mathematical induction with respect to the number of occur­
rences of 3  in B.
If there are no occurrences of 3  in B, then B is either f or one of the vari­
ables a*. In case B is /, we have that B' is / 3  /, and hence (I) follows by 
substitution in an appropriate variant of fl20. In case B is a*, we have that 
B' is the same wff as A*# and (1) follows trivially, the proof of B' from the 
hypotheses Ax, A2, . . An consisting of the single wff B*.
Suppose that there are occurrences of 3  in B. Then B is Bx 3  B2. By the 
hypothesis of induction,
(2) 
A1( A2, . .
An H Bj,
(3) 
k
k
 . . . a ^
b ;,
where B* is Bx or B* 3  / according as the value of Bx for the values av 
a2, . . an of slv a2, . .
an is t or f, and B2 is B2 or B2 3  /  according as the 
value of B2 for the values 
a2, . . ,, an of a1( aj , . . aB is t or f. In case 
B 'is B2l we have that B' is Bx 3  B 2, and (1) follows from (3) by substitution 
in an appropriate variant of f!02 and modus ponens. In case B[ is B1 3  /, 
we have again that B' is B1 3  Ba, and (I) follows from (2) by substitution in 
an appropriate variant of f 123 and modus ponens. There remains only the 
case that B* is Bx and B'z is B2 3  /, and in this case B' is B p B 23  /, and (1) 
follows from (2) and (3) by substitution in an appropriate variant of |140 
and two uses of modus ponens.
Therefore *151 is proved by mathematical induction.
The proof of *151 is effective in the sense that it provides an effective 
method for finding a proof of B' from the hypotheses A1( Aa, . . 
An. If 
B has no occurrences of 3 , this is provided directly. If B has occurrences of 
3 , the proof provides directly an effective reduction of the problem of finding 
a proof of B' from the hypotheses A1( Aj, , . 
An to the two problems of 
finding proofs of B{ and Bz from the hypothesis Ax> A2, . . 
An; the same 
reduction may then be repeated upon the two latter problems, and so on;

---


§15]
T A U T O L O G I E S , T H E  D E C I S I O N  P R O B L E M
99
after a finite number of repetitions the process of reduction must terminate, 
yielding effectively a proof of B' from the hypotheses Aj, A a, . . 
A n.
We now go on to proof of the converse of **150, which will also be effec­
tive.
*152. 
If B is a tautology, H B.
Proof. Let 
a2, . . ., a n be the variables of B, and for any system of
values Op a%, . . an of a1( a 2, . .., an let Av A 2, .. 
A n be as in *151. The 
B' of *151 is B, because B is a tautology. Therefore, by *151,
Aj, A 2, . .  ., A n 
B.
This holds for either choice of an, i.e., whether an is f or t, and so we have 
both
A ,, A 2.........A B_„ a„ =  / b B
and
Aj_, A a, . .
A n_j, a n I- B.
By the deduction theorem,
Alt A 2i .
.
A n_x h a n zd /  zd B,
Aj, A 2, . .  ,, A n„x 
a n ^  B.
Hence, by substitution in an appropriate variant of fl42 and two uses of 
modus ponens,
Aj, A g , . . ., A n_j f* B.
This shows the elimination of the hypothesis A n. The same process may 
be repeated to eliminate the hypothesis A n„j, and so on, until all the hypoth­
eses are eliminated.182 Finally we obtain (- B.
The decision problem of a logistic system is the problem to find an effective 
procedure or algorithm, a decision procedure, by which, for an arbitrary wff 
of the system, it is possible to determine whether or not it is a theorem (and 
if it is a theorem to obtain a proof of it188).
“ •Im plicitly, therefore, the m ethod of the proof is th a t of m athem atical induction 
w ith respect to «. Cf. footnote 179.
“ •This parenthetic p a rt of the problem will, in this book, always be included explic­
itly in solutions or p artial solutions of the decision problem of a system .
However, it m ight be dism issed as theoretically superfluous, on the ground th a t there 
always exists an effective enum eration of the proofs of a logistic system — as will appear 
in C hapter V III—and th a t once a  proof of a wff is known to exist, it m ay be found by 
searching through in order such an effective enum eration of all proofs. Possible objec­
tions to this are (I) th a t a procedure for finding som ething should not be called effective 
unless there is a predictable upper bound of the num ber of steps th a t will be required,

---


100
T H E  P R O P O S I T I O N A L  C A L C U L U S
[Ch a p. 1
The effective procedure for recognizing tautologies, as described at the 
beginning of this section, and the effective proofs which have been given 
of **150 and *152, together constitute a solution of the decision problem of 
the logistic system P1.
T his so lu tio n  o f th e  decision p ro b lem  of P : does n o t d e p e n d  on a n y  p a rtic u la r 
in te rp re ta tio n  o f P x. B eing p u rely  sy n ta c tic a l in  c h a ra c ter it m a y  be used u n d er 
a n y  in te rp re ta tio n  of P 1( o r even if no in te rp re ta tio n  a t  all is ad opted.
T he decision pro b lem  in th is sense we call m ore fully, th e  d e c is io n  p r o b le m  
fo r  p r o v a b ility , in a logistic system , o r in a form alized lan g u ag e o b tain ed  b y  
in te rp re ta tio n  of th e  logistic system .
In  th e case o f a form alized lan g u ag e th ere is also th e  s e m a n tic a l d e c is io n  
p r o b le m , as w e sh a ll call it, nam ely, to  find an  effective p ro ced u re for d eterm in in g  
of an  a rb itra ry  sen ten ce w h eth er it is tru e  in th e sem a n tic a l sense (§§04, 09), 
an d  of an a rb itra ry  propositional form  w h eth er it is tru e  fo r all values of its 
variables.184 F o r th e  form alized lan g u ag e w hich is o b ta in e d  b y  ad o p tin g  th e  
principal in te rp re ta tio n  of P l( th e  sem a n tic a l decision p ro b lem  is triv ial, because 
th e sem an tical rules, given a t th e  en d  of §10, d irectly  p ro v id e th e  requ ired  
effective p ro ced u re. T his triv ia lity  of th e  sem antical decision problem , how ever, 
b y  no m eans holds for form alized lang u ag es in general, as th e  definition of tru th  
contained in th e  sem antical rules is o ften  non-effective.
T he decision pro b lem  for p ro v a b ility , as we h av e seen, is n o n -triv ial even in 
th e  relativ ely  sim ple case of th e  sy ste m  Pj.
In view of the solution of the decision problem of P1( the explicit presenta­
tion of proofs of particular theorems of P2 is now no longer necessary. When­
ever we require a particular theorem of Pv it will be sufficient that we just 
write it down, leaving it to the reader to verify that it is a tautology and 
hence to find a proof of it by applying the procedure which is given in the 
proofs of *152 and *151. In particular we now add, on this basis, the five 
following theorems of Px:
and (2) that not only the decision procedure itself ought to be effective, but also the 
demonstration of it ought to be effective in the sense that it proceeds by effectively 
producing the proof of the wff (when the proof exists). B ut these objections are not easy 
to maintain. Indeed the restriction on the notion of effectiveness, as proposed in (1), is 
vague, and the writer does not know how to make it definite w ithout excluding proce­
dures that m ust obviously be considered effective by common (informal) standards. 
The requirement proposed in (2) is in the direction of m athem atical intuitionism — see 
Chapter X II— and m ust be regarded as radical from the point of view  of classical m athe­
matics.
1,4The writer once proposed the name "deducibility problem" for what If here celled 
the decision problem  for provability, the intention being to reserve the name "decision
problem" either for the semantical decision problem or for w hat is called in §46 the 
decision problem for validity. It seems better, however, to use "decision problem" as a 
general name for problem s to find an effective criterion (a decision procedure) forsom e- 
thing, and to distinguish different decision problems by means of qualifying adjectives 
or phrases.

---


m
TAUTOLOGIES, THE DECISION PROBLEM
101
fl53. 
t ZDp==p
fl54. 
— p =  p
fl55. 
p s  q ZD . q =  p
f 156. 
p =  q ZD mp ZD q
fl57. 
p ~ q Z D . q  =  r ZDap ~ r
|154 is the complete law of double negation (cf. footnote 163). |155 is the 
commutative law of {material) equivalence, and ^lS? is the transitive law of 
(material) equivalence.
Proofs of metatheorems of Pj are also often greatly simplified by the solu­
tion of the decision problem. This is true, for example, in the case of the 
following:
*158. 
If B results from A by substitution of N for M at one or more places 
in A (not necessarily for all occurrences of M in A), and if [■ M s  N, 
then H A s  B.
Proof. Let a1( aa, , . 
an be the complete list of variables occurring in 
A and B together. Since M — N is a theorem, it is a tautology. Therefore, 
by the truth-table of s ,  M and N have the same value for every system of 
values of a1( a2, .. 
an. Since B is obtained from A by substitution of N 
for M at certain places, it follows that A and B have the same value for 
every system of values of a*, a2l .. 
an (details of the proof of this, by 
mathematical induction with respect to the number of occurrences of zd in 
A, are left to be supplied by the reader, using the result of exercise 12.1). 
Therefore, by the truth-table of s ,  we have that A s  B is a tautology. 
Therefore by *152, F A = B .
As a corollary we have also:
*159. 
If B results from A by substitution of N for M at one or more places 
in A (not necessarily for all occurrences of M in A), if f- M — N 
and f-A, then h B. 
(Rule of substitutivity of equivalence.)
Proof. By *158, 1 - A s B .  Therefore by tl56» substitution, and modus 
ponenst h A rs B. Since f- A, we have by another use of modus ponens that 
h B.

---


102
T H E  P R O P O S I T I O N A L  C A L C U L U S
[Chap. I
EXERCISES 1 5
1 5 .0. Verify the following tautologies:
(1)
The wffs of 14.4 and 14.5.
(2)
The wff of 14.6.
(3)
[Law of exportation.)
(4)
IP =d . q z> r] 
. pq 3  r
(Law of importation.)
(5)
[f> => IMP = > r ] ^ . p = > q r
(Law of composition.)
(6)
p ZD q ZD m ~q 3  ~p
(Law of contraposition.)
(7)
p =  q ~ * q  =  p 
(Complete commutative law of equivalence.)
(8)
The transitive law of equivalence, fl57.
(9)
~ m fi ~p
(Law of contradiction.)
(10)
p v ~p
(Law of excluded middle.)
15*1 • Determine of each of the following wffs whether it is a tautology or 
a contradiction or neither:
( 1 )
(2) 
p id q ZD [ r z D s ] Z D u p Z D r z D mq Z D S
(3) 
/ ro / ZD • / =d / ZD /
(4) 
p  =  q =  p v q  =  ~ p v ~ q
1 5 *2 . Prove: If B results from A by substitution of N  for M at one or 
more places in A (not necessarily for all occurrences of M in A), then 
F M s
N d . A e
B.
*5-3. Present proofs of f 154 and fl56 in the style of §14, not using 
methods or results of §15.
1 5 .4 , 
A wff B which contains n  different variables is said to be in i m ­
p lic a tiv e  n o rm a l fo rm  if the following conditions are satisfied: (i) B has the 
form Ct id  m C2 id  . . .  . Cm id  /; (ii) each Ctf (i =  1 , 2 , . . . ,  m ) has the form 
Cn id  m CM i d  m. .. C<n id  /; (iii) each Cik (» =  1, 2, , .
m and k  =  1,
2 , . . . .  n) is either bfc or ~bfc, where bfc is the kib of the variables occurring 
in B, according to the alphabetic order of the variables (§10); (iv) the 
antecedents Cf are all different and are arranged among themselves according 
to the rule that, if Ctl, Cia, .
.
are the same as Cfl, Cy2, ■. Q ik-u re­
spectively, and C ik is bfc, and Cjfc is ~bfc, then i  <  /. Show that for every wff 
A there is a unique corresponding wff B (the im p lic a tiv e  n o rm a l fo rm  o f A) 
such that B is in implicative normal form, and each C, contains the same 
variables that A does, and F A s B .  (Make use of the values of the given wff 
A for the various systems of values of its variables, in order to determine B 
in such a way that A =  B is a tautology.)
What is the implicative normal form of a tautology containing the »

---


§15]
E X E R C I S E S  15
103
different variables b1( b2, . , 
brtJ and no other variables? Of a contradiction 
containing these variables and no others?
What are the possible implicative normal forms of a wff containing no 
variables? Of a wff containing just one variable? Of a wff containing just 
two (different) variables?
*5-5- Show that Px is a commutative ring, with equivalence as the ring 
equality, non-equivalence as the ring addition, and conjunction as the ring 
multiplication, in the sense that the following analogues of the ring laws 
are tautologies and therefore theorems of Px:
p ^ q = . q ^ p  
fiqzzqp
p $ [ q - £ r ] s =  . p - ^ q - ^ r  
p[qr] =  pqr
p ^ q = r  c . q  =  . p ^ r  
p[q =£ r] =  ,pq 
pr
Identify the ring subtraction (cf, the third law of those above). Also identify 
the zero element and the unit element of the ring.
1 5 .6 . 
In a like sense, show further that Pt is a Boolean ring by verifying 
the tautologies:185
p ^
p =  i 
pp =  p
1 5 -7 * In a like sense, show that Pj is a Boolean ring with equivalence as 
the ring equality, equivalence as the ring addition, and disjunction as the
w The reader must be careful not to misunderstand the assertions made in 15.5-15.8. 
In 15.0, e.g., it is m eant that, with equivalence in the role of equality, non-equivalence 
in the role of addition, and conjunction in the role of multiplication, the defining laws 
for a Boolean ring appear as theorems of Pl4 and hence also all laws of Boolean rings 
which are derivable from these by methods of the propositional calculus (including 
the rule of substitution, *101, and the rule of substitutivity of equivalence, *159). 
There is no question of a ring in the sense of a particular system of elements and opera­
tions on them obeying the ring laws, until we deal w ith a particular interpretation of P r  
If we allow interpretations th a t are sound in the generalized sense of §19, then many 
sound interpretations of P x do turn out to be Boolean rings (with equivalence in the 
role of equality, etc.) in the sense of a particular system of elements and operations; 
but it is not true th at every sound interpretation of P* is a Boolean ring in this sense—or 
better, in view of cases like those of exercises 19.11 and 19.12, it is not easy to decide 
on a generally satisfactory meaning for the italicized statement.
Under its principal interpretation, Pj is not merely a Boolean ring, but a two-element 
field, with addition and m ultiplication identified in the way described in 15.5. This 
remark, and its application to formal work in the propositional calculus, is due to 
J. J. G4galkine in Recueil Mathimatique de la SociiU Mathimatique de Moscou, vol. 
34 (1927), pp. 9-28. To any one familiar with the procedures of elementary algebra, 
it is indeed very convenient to rewrite all expressions of the propositional calculus in 
term s of non-equivalence and conjunction as fundamental connectives, using also 0 and 
1 as propositional constants, and writing the sign 4- instead of
The term Boolean ring, now standard, is due to M. H. Stone (1930).

---


104
T H E  P R O P O S I T I O N A L  C A L C U L U S
[Chap. I
ring multiplication. Identify the ring subtraction, and the zero element and 
the unit element of the ring.18®
*5-«. In a like sense, Pj is also a Boolean algebra, again with equivalence 
in the role of equality, and with disjunction and conjunction identified as 
the Boolean sum and Boolean product respectively.187 Verify the following 
tautologies that are implied in this statement: the complete distributive law 
of conjunction over disjunction; the complete distributive law of disjunction over 
conjunction; the two laws of absorption,
p vpq =  p,
PIP v q ] ~  p,
and the two laws of De Morgan,m
~[j>vq]=B ~p - q,
~[pq) =  ~pv~q.
15.9. Various works on traditional logic treat of certain kinds of inferences, 
known as hypothetical syllogisms, disjunctive syllogisms, and dilemmas. These 
are stated verbally, and include;18*
Hypothetical Syllogism 
Modus ponens: 
If A then B. 
A. 
Therefore, B.
Modus iollens: 
If A then B. 
Not B. Therefore, not A.
lMThis is the dual (in the sense of §16) of the remark of 16.6, 15.6. It was used by 
Jacques Herbrand in his dissertation of 1930, independently of G4galkine, and again 
by Stone in 1937. It provides another method, dual to that of the preceding footnote, 
by which procedures of elementary algebra may be utilized for propositional calculus; 
namely, all expressions of the propositional calculus are rewritten in terms of equiva­
lence and disjunction as fundamental connectives, together with the constants 0 and 1, 
and the usual signs of addition and multiplication are employed instead of 3  and v 
respectively. (Compare exercise 24.3.)
The laws p p s . p and its dual ace known as the laws of tautology, though this is quite 
a different sense of the word "tautology’* from that introduced in the text. From the 
point of view of ring theory they might also be called idempotent laws.
lB7This remark is implicit already in Peirce’s paper of 1885, cited in footnote 67. 
(''Peirce's law" of 12.6 is also found in this paper.)
U8Not these laws but the corresponding laws of the class calculus were enunciated 
by Augustus De Morgan in his Formal Logic of 1847.
In verbal formulation these laws of the propositional calculus were known already 
to the Scholastics, perhaps first to Ockham. Cf. a paper by Lukasiewicz in Erkenntnis, 
vol. 5 (1935), pp. 111-131, in which some rudiments of the propositional calculus are 
traced back not only to the Scholastics but to antiquity— material implication in partic­
ular, to Philo of Megaia. And concerning the history of the De Morgan laws among 
the Scholastics, see further Phiiotheus Boehner in Archiv fUr Philosophic, vol. 4 
(1951), pp. 113-146.
lslWe make no attem pt to enter into the history of the matter, but have merely 
compiled a representative list from a number of comparatively recent works of tradi­
tional character. Some discrepancies will be disclosed if parts (1) and (2) of the exercise 
are carried through. These may be attributed partly to uncertainties of meaning, partly 
to disagreements among different writers.

---


§15]
E X E R C I S E S  15
105
D isju n ctiv e Syllogism
M o d u s  to lle n d o  p o n e n s : 
A  or B. 
N o t A. 
Therefore, B.
M o d u s  p o n e n d o  to lle n s : 
A o r B. 
A. 
T h erefo re, n o t B.
D ilem m a
S i m p l e  c o n s tr u c tiv e : If A then. C. 
If B  th e n  C. 
A or B. 
T h erefore, C. 
S i m p l e  d e s tr u c tiv e : If A  th e n  B. If A th e n  C. N o t B, or n o t C. T herefore, n o t A. 
C o m p le x  c o n s tr u c tiv e : If A th en  B. If  C th e n  D. A or C. T h erefore, B  or D. 
C o m p le x  d e s tr u c tiv e : If  A th e n  B. If C th e n  D . N o t B, or n o t D . T herefore, 
n o t A, o r n o t C.
T h e  letters A, B, C, D  a re  here replaceable b y  sentences1*0— indeed we m ight 
h av e used bold le tte rs (u n d er th e  co n v en tio n s of §08) ex cep t for th e  lack of a 
d efin ite o b ject lan g u ag e to  w hich th e y  could be u nderstood to  refer. Som e 
w riters a re  in  d isa g re e m e n t am ong them selves, a n d  others are u n clear, (a) as 
to  w h eth er th e  w ords " if . . . th e n " m ean  m aterial im plication o r som e other 
k in d  of im plication, a n d  (b) as to w h eth er th e  w ord " o r"  m eans exclusive dis­
ju n ctio n  or inclusive d isju n ctio n . (Cf. §05.)
(1) O n th e  a ssu m p tio n  th a t "if . . . th e n "  m eans m aterial im p licatio n  and 
" o r"  m eans exclusive d isju n ctio n , th e  le a d in g  p r in c ip le  of, e.g., th e  sim ple de­
stru c tiv e  d ilem m a is
O n th is assum ption, w rite  in th e sam e m a n n e r th e  leading prin cip le of each of 
th e  k in d s of inference listed . Check each of th e  kinds of inference b y  ascertaining 
w h eth er its leading p rin cip le is a  tau to lo g y . (W herever possible, of course, m ake 
use of know n th eo rem s of P , in o rd er to  sh o rte n  th e w ork.)
(2) O n th e  assu m p tio n  th a t "if . . . th e n "  m eans m aterial im p licatio n  and 
" o r"  m eans inclusive d isju n ctio n , again w rite th e  leading prin cip le of each of 
th e  k in d s of inference, an d  check in th e  sam e w ay.1*1
W h en  S an ch o  P an za w as governor of B a ra ta ria , th e  follow ing case 
cam e before him  for decision. A certain  m a n o r w as divided b y  a  riv e r upo n  w hich 
w as a  bridge. T h e lord of th e  m an o r h ad  erected  a  gallow s a t one end of th e  
bridge an d  h ad  e n acted  a law  th a t w h o ev er w ould cross th e  b rid g e m u st first 
sw ear w h ith er he w ere going an d  on w h a t business; if he sw ore tru ly  he should 
be allow ed to pass freely ; b u t if he sw ore falsely and did th en  cross th e  bridge 
he should be han g ed  fo rth w ith  upon th e  gallow s. O ne m an, com ing u p  to the 
o th e r end of th e  b rid g e from  th e gallow s, w hen his o a th  w as req u ired  sw ore, 
" I  go to  be h an g ed  on y o n d e r gallow s," a n d  thereu p o n  crossed th e  bridge. T h e 
vexed  q uestion w h eth er th e  m an shall be h an g ed  is b ro u g h t to  S ancho P anza, 
w ho is holding c o u rt in  th e  im m ed iate v ic in ity , an d  who is of course obligated 
to  u phold th e  law  as v alid ly  enacted b y  th e  lord of th e  m a n o r.1*2
^ T h e  traditional assum ption that the sentences must have the subject-predicate 
form is om itted as irrelevant.
M1For the hypothetical and disjunctive syllogism s, the question of reproduction in 
the notation of the propositional calculus is discussed by S. K. Langer in an appendix 
to her Introduction to Symbolic Logic (1937).
m The story is here only very slightly modified from the original as given by Miguel 
de Cervantes (1615).

---


106
THE PROPOSITIONAL CALCULUS
[Chap. I
Let P, Q, R, S be constants expressing the propositions, respectively, that he 
[the man in the story] crosses the bridge, that he is hanged on the gallows, 
that the oath to which he swears is true, and that the law is obeyed. Use a formu­
lation of the propositional calculus containing these four propositional constants, 
as well as propositional variables. Then the given data are expressed in the three 
wffs: R =  PQ, Pt S 
,Q =  P ~R. (Notice in particular that to replace the 
third wff by 5 Z3 - P ~R z> Q would not sufficiently represent the data, since 
we must suppose that it is as much a violation of the law to hang an innocent 
man as it is to let a guilty one go free.)
Verify the tautology,
r =pqz >. pz>*sz >[q~p ~r] p  ~s,
and hence by substitution and modus ponens demonstrate that the law cannot 
be obeyed in this instance.
16.
Duality. The process of dualization is most conveniently applied,
not to wffs of Pj but to expressions which are abbreviations of wffs of Px 
in accordance with Dl-11 (but without any omissions of brackets). The dual 
of such an expression is obtained by interchanging simultaneously, wherever 
they occur, the letters i and /, and each of the following pairs of connectives: 
rs and cj:, disjunction and conjunction, — and 
c: and 
9 and |. The 
symbol (connective), 
is left unchanged by dualization, and is therefore 
called self-dual. The letters t and / are called duals of each other; likewise 
the connectives conjunction and disjunction; likewise zd and c£; etc.
Thus, e.g., the dual of the expression
is the expression
f
[qr]] =  [rv~fl]
A dual of a wff of Px is obtained by writing any expression of the foregoing 
kind which abbreviates the wff, dualizing this expression, and then finally 
writing the wff which the resulting expression abbreviates. It is not excluded 
that the wff itself may be used in the role of the expression which abbre­
viates it, and when this is done the principal dual of the wff is obtained. For 
example, the wff
[[p ZZ> ?] => /]
has as its principal dual the wff
[{p $  q] £  tl
i.e., the wff
[[[/ =>fl=> LLq =>/>]=> /]] => /];
but because the same wff,

---


§16]
DUALITY
107
[[p ■=> q] =D /],
may also be abbreviated as [q cj: p], it has also the wff
as a dual.
[9 ^ P ]
Except in the case of a wff consisting of a variable alone, the principal dual 
of the principal dual of a wff is not the same as the wff itself. However, of 
course the wff itself is always included among the various duals of any one of 
its duals. And any dual of a dual of a wff is equivalent to the wff in the 
sense of *160 below.
In order to minimize the variety of different duals of a given wff, Dl-11 
have been arranged as far as possible in pairs dual to each other. But this 
could not be done in the case of D l-3, and it is from these three that the 
possibility arises of different duals of the same wff. By examining D l-3, 
it may be seen that any two duals of the same wff can be transformed one 
into the other by a series of steps of the four following kinds: replacing a wf 
part t~z> N by N, replacing a wf part N by t 
N, replacing a wf part 
N 
by N, and replacing a wf part N by 
By fl53, fl54, fl55, *158, fl57 
(together with substitution and modus ponens) it therefore follows that any 
two duals of the same wff are equivalent in the following sense:
*160. 
If B and G are duals of A, (- B =  G.
In the truth-tables in §15 it will be seen that the truth-table for zd is 
transformed into that for cjr if t and f are interchanged throughout (in all 
three columns of the table). In fact, if t and f are interchanged, the truth- 
tables for 
and cj: are interchanged; likewise those for disjunction and con­
junction; likewise those for =  and 
likewise those for c  and 
likewise 
those for 9 and |; and the truth-table for ~ is transformed into itself. From 
this it follows that the dual of a tautology is a contradiction. Hence, in view 
of the truth-table for negation, there follows the metatheorem:
*161, 
If HA, if Ax is a dual of A, then b~A x. 
(Principle of duality.)
Two corollaries of *161, special principles of duality, are obtained by 
means of the tautologies:
fl62. 
-[/> <£ ?] 
• q => p
f!63. 
~\p =£ q] => . p =  q
These corollaries of *161 are:

---


108
THE PROPOSITIONAL CALCULUS
[Chap. I
*164. 
If h A 
B, if Ax and B x are duals of A and B respectively, then 
h B l D  Av 
{Special principle of duality for implications.)
*165. 
If V A =  B, if Aj and 
are duals of A and B respectively, then 
h Aj =  Bj. 
{Special principle of duality for equivalences.)
17. Consistency.
The notion of consistency of a logistic system is semantical in motivation, 
arising from the requirement that nothing which is logically absurd or self' 
contradictory in meaning shall be a theorem, or that there shall not be two theo­
rems of which one is the negation of the other. But we seek to modify this orig­
inally semantical notion in such a way as to make it syntactical in character 
(and therefore applicable to a logistic system independently of the interpretation 
adopted for it). This may be done by defining relative consistency with respect to 
any transformation by which each sentence or propositional form A is trans­
formed into a sentence or propositional form A', the definition (given below) 
being such that relative consistency reduces to the semantical notion of con­
sistency under an interpretation that makes A' the negation of A. Or we may 
define absolute consistency by the condition that not every sentence or propo­
sitional form shall be a theorem, since in the case of nearly all the systems with 
which we shall deal it is easy to see that, once we had two theorems which were 
negations of each other, every sentence and propositional form whatever could 
be proved (e,g., in the case of Pt this follows by 1123, substitution, and modus 
ponens). Or, following Hilbert, we might in the case of a particular system 
select an appropriate particular sentence and define the system as being con­
sistent if that particular sentence is not a theorem (e,g., we might call P* 
consistent on condition that / is not a theorem). Or if the system has prop­
ositional variables, we may define it as being consistent in the sense of Postwa 
if a wff consisting of a propositional variable alone is not a theorem.
Turning now to the purely syntactical statement of the matter, we have 
the following:
(a) A logistic system is consistent with respect to a given transformation 
by which each sentence or propositional form A is transformed into a sen­
tence or propositional form A', if there is no sentence or propositional form 
A such that h A and h A'.
(b) A logistic system is absolutely consistent if not all its sentences and 
propositional forms are theorems.
(c) A logistic system is consistent in the sense of Post {tenth respect to a
m E. L. Post in the A m e r ic a n  J o u r n a l o f M a th e m a tic s, vol. 43 (1921), see p. 177.
The notion of absolute consistency is, in view of the rule of substitution, closely 
related to that of consistency in the sense of Post; it seems to have been first used ex­
plicitly as a general definition of consistency by Tarski (M o n a lsh e fte  fu r  M a ih e m a tik  
u n d  P k y s ik , vol. 37 (1930), see pp. 387-388). A similar remark applies to the notion 
of absolute completeness (cf. Tarski, ib id ., pp. 390-391).

---


§18]
C O M P L E T E N E S S
109
certain category of primitive symbols designated as "propositional vari­
ables”) if a wff consisting of a propositional variable alone is not a theorem.
*♦170. 
Px is consistent with respect to the transformation of A into A d /.
Proof, By the definition of a tautology (and the truth-table of do), not 
both A and A ro / can be tautologies. In fact, if A is a tautology, then A =5 / 
is a contradiction. Therefore by **150, not both A and A =5 / can be theorems 
of Pj.
**171. 
Pj is absolutely consistent.
Proof. The wff / is not a tautology, and therefore by **150 it is not a 
theorem of Px.
**172. 
Pjl is consistent in the special sense that / is not a theorem.
Proof. The same as for **171.
**173. 
Px is consistent in the sense of Post.
Proof. A wff consisting of a propositional variable alone is not a tautology, 
because its value is f for the value f of the variable. Therefore by **150, 
it is not a theorem of Pv
18* Completeness.
A s in  th e  case of consisten cy , th e notion of c o m p le te n e s s of a logistic system  
has a sem an tical m o tiv atio n , consisting roughly in th e  in ten tio n  th a t th e  system  
shall h a v e  all possible th eo rem s n o t in conflict w ith  th e in te rp re ta tio n . As a 
first a tte m p t to fix th e  n o tio n  m ore precisely, w e m ight d em an d  of every 
sentence th a t eith er it o r its n eg atio n  shall be a th eo rem ; b u t since we allow  the 
assertio n  of propositional fo rm s (see th e concluding p arag rap h s of §06), th is m ay 
prove insufficient. T herefore, follow ing P o st.1,8 w e a re  led to  define a logistic 
system  as being com plete if, for every sentence o r propositional form  B , eith er 
k B or th e  system  w ould becom e in co n sisten t u p o n  adding B to  it as an axiom  
(w ith o u t o th e r change). T h is leads to  several p u rely  sy n tactical d efin itio n s of 
com pleteness, corresponding to  th e d ifferen t sy n tactical definitions of con­
sisten cy  of a system  as giv en  in th e  p receding section.
A n o th e r ap proach s ta rts  fro m  th e  idea th a t a sy stem  is com plete if th e re  is a 
sound in te rp re ta tio n  u n d e r w hich every  sentence th a t denotes tru th  is a th eo rem  
and ev ery  propositional form  th a t has alw ays th e  value tru th  is a  th eo rem —  
th en  seeks to  replace th e  n o tio n  of an in te rp re ta tio n  by som e su itab le sy n ta c tic a l 
notion. T h is approach, how ever, requires certain  restrictions on th e  c h a ra c ter 
of th e  in te rp re ta tio n  allow ed, an d  thus leads to  th e  intro d u ctio n  of m o d e ls in 
th e  sense of K em eny. I t  will be discussed briefly  in C hapter X.

---


110
T H E  P R O P O S I T I O N A L  C A L C U L U S
[Chap. I
As syntactical definitions of completeness we have, for the present, the 
following:
(a) A logistic system is complete with respect to a given transformation by 
which each sentence or propositional form A is transformed into a sentence 
or propositional form A', if, for every sentence or propositional form B, 
either h B or the system, upon addition of B to it as an axiom, becomes 
inconsistent with respect to the given transformation.
(b) A logistic system is absolutely complete if, for every sentence or prop­
ositional form B, either h B or the system, upon addition of B to it as an 
axiom, becomes absolutely inconsistent.
(c) A logistic system is complete in the sense of Post if, for every sentence or 
propositional form B, either h B or the system, upon addition of B to it as 
an axiom, becomes inconsistent in the sense of Post.
Let B be a wff of 'Pl which is not a theorem. Then by *152, B is not a 
tautology. I.e., there is a system of values of the variables of B for which the 
value of B is f.
If B is added to Px as an axiom, it becomes possible by *121 to infer the 
result of any simultaneous substitution for the variables of B. In particular, 
we may take one of those systems of values of the variables of B for which 
the value of B is f, and substitute for each variable a* either t or / according 
as the value a{ of that variable is t or f. Let E be the wff which is inferred in 
this way.
Since E contains no variables, the definition at the beginning of §15 
assigns one value to E, and because of the way in which E was obtained from 
B it follows that this value isf (the explicit proof of this by mathematical 
induction is left to the reader). Therefore by the truth-table of 3 ,  E id / is 
a tautology. Thus by *152, we have that E ^  / is a theorem of P1( therefore 
also a theorem of the system which is obtained by adding B to Px as an 
axiom.
In the system obtained by adding B to Px as an axiom we now have that 
both E and E zo / are theorems. Therefore by modus ponens we have that / 
is a theorem. Therefore by f 122 and modus ponens, p is a theorem. Thence 
by substitution we may obtain any wff whatever as a theorem, including, of 
course, with every wff A, also the wff A ^  /.
Thus we have proved the completeness of Px in each of the three senses:
**180. 
Px is complete with respect to the transformation of A into A ^  /. 
**181. 
Px is absolutely complete.
**182. 
Px is complete in the sense of Post.

---


EXERCISES x8
111
518]
EXERCISES 18
Discuss the consistency and completeness of each of the following logistic 
systems, in each of the senses of **170-**173, **I80-**I82:
18 .0 . The system obtained from Px by deleting the axiom f 104. (Show 
that a wff A containing occurrences of / is a theorem if and only if S[A\ 
is a theorem, where a is a variable not occurring in A.)
1 8 . 1. The primitive symbols and the formation rules are the same as 
those of Pj. There is one axiom, namely p. There is one rule of inference, 
namely *101 with the restriction added that B must not be /.
i 8 .a . The primitive symbols and the formation rules are the same as 
those of Pj. There is one axiom, p 3  q, and one rule of inference, *101.
1 8 .3 . The system Pg obtained from the system Pw of 12.7 by deleting / 
from among the primitive symbols, and making only such further changes 
as this deletion compels, namely, omitting the formation rule lOi and the 
fourth axiom, fl22. (Make use of the results of 12.7 and 12.8; prove an ana­
logue of *151 in which a variable r is selected, different from a1; a2, . . 
an, 
and A, is defined to be a* o r a p r  according as at is t or f, and B' is defined 
t o b e B D r o r o r B D r  according as the value of B for the values av aK, 
. . an of a1( aa, . . 
an is t or f; and hence prove that *152 holds for Pg. 
In place of **170 and **180, show that Pg is consistent and complete with 
respect to the transformation of A into A ^  a, where a is the first variable 
in alphabetic order not occurring in A.)
1 8 .4 . The system P£ having the same primitive symbols and wffs as Pg, 
the same rules of inference, and the single following axiom:
p = > q D * r z D mr z Dp D> . s Z Dp
(After verifying that this axiom is a tautology, we may prove the axioms 
of Pg as theorems of P£, and then use the results of 18.3. For this purpose, 
first establish the derived rules, that if h A zd B zd C, then 1- C d  A 3
, 
a 33 A, f-ar3 A 3DC^>. b^>C,  h B ^ C ;  then following Lukasiewicz, prove
px D>rzD [sZDp]ZDmr z D q z D p Z D msZDp, 
t ZDqz D[ s ZDp] ZDmr z D p Z D msZDp,
f ZD p ZD p ZD [sZDp]ZDmpZDqZDrZD*SZDp, 
p Z Dr ZDq Z Dq z y . q z Dr z D. p Z Dr ,  
pZDqZDmpZDrZDqZDq,
and the transitive law of implication, in order, as theorems of P^.)

---


112
T H E  P R O P O S I T I O N A L  C A L C U L U S
[Chap. I
1
8 -5 . By means of semantical rules similar in character to a-g of §10, supply 
sound interpretations of the systems of 18.0-18.3, and discuss for each system 
the possible variety of sound interpretations of this sort.
19. Independence.184 * An axiom A of a logistic system is called independ­
ent if, in the logistic system obtained by omitting A from among the axioms, 
A is not a theorem. A primitive rule of inference R of a logistic system is 
called independent if, in the logistic system obtained by omitting R from 
among the primitive rules, R is not a derived rule. Or equivalently, we may 
define an axiom or rule of inference to be independent if there is some theo­
rem which cannot be proved without that axiom or rule.186
It should not be regarded as obligatory that the axioms and rules of 
inference of a logistic system be independent. On the contrary there are 
cases in which important purposes are served by allowing non-independence. 
And if the requirement of independence is imposed, this is as a matter of 
elegance and only a part of the more general (and somewhat vague) require­
ment of economy of assumption.186
In this book we shall often ignore questions of independence of the axioms 
and rules of a logistic system. But for the sake of illustration we treat the 
matter at length in the case of Px.
In the propositional calculus a standard device for establishing the in­
dependence of axioms and rules is to generalize the method of §15 as follows. 
Instead of two truth-values, a system of two or more truth-values,
0 , 1 ,.. * t v,
is introduced,187 the first // of these,
0, 1,. . / / ,
1#4The reader who wishes to get on rapidly to logistic systems of more substantial 
character than propositional calculus may omit §19 and all of Chapter II except 
§§20-23, 27. Especially §§26, 28 and the accompanying exercises may well be post­
poned for study in connection with later chapters.
1MIn the case of rules of inference, the equivalence of the two definitions of independ­
ence depends on considerations like those adduced in footnote 183—to show th at the 
conditions of effectiveness which we demand of a primitive rule of inference are sufficient 
to ensure that, when the same rule is demonstrated as a metatheorem of some other 
system, the required conditions of effectiveness for derived rules of inference (§12) 
will therefore be satisfied. In what follows, we shall make use only of the second defini­
tion of independence of a rule of inference, viz., that the rule is independent it there is 
at least one theorem which cannot be proved without it.
Thepossibility should be noticed that a rule of inference not previously independent 
may become so when additional axioms are adjoined to a logistic system.
“ •The requirement of economy of assumption is usually understood to concern also 
the length and complication (or perhaps the strength, in some sense) of individual rules 
and axioms—in addition to merely the number of them.
” 7I t is convenient in practice to use numerals in this way to denote the truth-values, 
though analogy with the notation used in the case of two truth-values would suggest

---


§19]
I N D E P E N D E N C E
(where 1 
// <  v) being called designated truth-values.198 To each of the
primitive constants (if any) is assigned one of these truth-values as value, 
and to each primitive connective is assigned a truth-table in these truth- 
values. Analogously to the first paragraph of §15 is defined the value of a 
wff for given values of its variables, the possible values of the variables 
being the truth-values 0 , 1 , . .  
v, and a wff is called a tautology if, for every 
system of values of its variables, it has one of the designated truth-values as 
its value. If then every rule of inference has the property of preserving 
tautologies (i.e., that the conclusion must be a tautology when the premisses 
are tautologies) and every axiom but one is a tautology, it follows that the 
one axiom which is not a tautology is independent. Or if every axiom is a tau­
tology and every rule of inference except one has the property of preserving 
tautologies, and if further there is a theorem of the logistic system that is not 
a tautology, it follows that the exceptional rule of inference is independent.
In the case of Pj, it happens that we may establish the independence of 
each of the axioms and rules of inference, with the exception of the rule of 
substitution, by means of a system of three truth-values, 0, 1, 2, of which 
0 is the only designated truth-value, and 2 is assigned to the primitive 
constant / as a value. The required truth-tables of zo are as follows (the 
number at the head of each column indicating the axiom or rule whose 
independence is established by the table in that column).
1 13
p
*100 
P =>?
1102
P=>V
1103 
p=>q
tl04
p z ^ q
0
o
0
0
0
0
0
1
0
2
1
i
0
2
2
2
2
1
0
0
2
0
0
1
1
0
2
0
0
1
2
2
0
1
2
2
0
0
0
0
0
2
i
1 
1
0
0
0
2
2
1 
0
0
0
0
rather t lf t„ . . ., tp for the designated truth-values and fx, f*, . . .. f f o r  the non- 
designated truth-values.
Also in the work of verifying tautologies in the manner of §15, the numerals 0 and 1 
are often used instead of the letters t and f.
IMAn infinite number of truth-values may also be used, with either a finite or an 
infinite number of designated truth-values, and likewise of non-designated truth-values. 
In this case the direct process of verifying tautologies (in a manner analogous to that of 
§15) is no longer effective, but the notion of a tautology may neverthelessstill be useful.

---


114
T H E  P R O P O S I T I O N A L  C A L C U L U S
fCHAP. I
For the proof of independence of *100, it is necessary to supply also an 
example of a theorem of Px which is not a tautology according to the truth- 
table used. One such example is / r> p\ another is p r> [ p / j D / o ^ ,
The rule of substitution *101 is necessarily tautology-preserving for any 
system of truth-values and truth-tables, and hence its independence cannot 
be established by this method. However, the independence of *101 follows 
from the fact that without it no wff longer than the longest of the axioms 
could be proved. And in fact a like proof of the independence of the rule of 
substitution will continue to hold after the adjunction of any finite number 
of additional axioms (since examples are easily found of wffs of arbitrarily 
great length which are theorems of P*).
The foregoing method of finding independence examples by means of a 
generalized system of truth-values suggests also a generalization of the prop­
ositional calculus itself. Namely, we may fix upon a generalized system of 
truth-values as above, then introduce a number of connectives with assigned 
truth-tables, and possibly also a number of constants to each of which a 
particular truth-value is assigned as value. The wffs of a logistic system may 
be constructed by using variables and these connectives and constants, and 
we may supply a list of axioms which are tautologies (in the generalized 
system of truth-values) and rules of inference which preserve tautologies. 
Especially if this is done in such a way that every tautology is a theorem, 
the resulting logistic system is called a many-valued propositional calculus 
in the sense of Lukasiewicz.
The same considerations lead also to a generalization of the requirements 
imposed in §07 on an interpretation of a logistic system, these requirements 
being modified as follows when a generalized system of truth-values is used. 
The semantical rules must be such that the axioms either denote truth-values 
or have always truth-values as values and the rules of inference preserve this 
property. Only those wffs are capable of being asserted which denote truth- 
values or have always truth-values as values; and only those are capable of being 
rightly asserted which denote a designated truth-value or have only designated 
truth-values as values. An interpretation of a logistic system is called sound if, 
under it, all the axioms either denote designated truth-values or have only 
designated truth-values as values, and the rules of inference preserve this prop­
erty (in the sense that, if aU the premisses of an immediate inference either 
denote designated truth-values or have only designated truth-values as values, 
then the same holds of the conclusion).

---


EXERCISES zg
115
Il9j
EXERCISES 19
19*0. Carry out in full detail the proof of independence of the axioms and 
rules of P2 which is outlined in the text. (In showing that particular wffs are 
or are not tautologies in the generalized system of truth-values, use an ar­
rangement analogous to that described in §15.)
1 9 .I . Consider the possibility of demonstrating the independence of the 
axioms and rules of P2 by means of a system of only two truth-values. I.e., 
for each axiom and rule, either supply the required demonstration or show 
it to be impossible.
1 9 *2 . Similarly consider the possibility of demonstrating the independence 
of the axioms and rules of Pj by means of a system of three truth-values of 
which two are designated.
19-3- The truth-table given in the text for the independence of *100 
shows that there are theorems containing the symbol / which cannot be 
proved without use of *100, but is insufficient to show that there are any 
such theorems not containing /. Prove this statement. Devise another truth- 
table for the independence of *100, not having this defect.
1 9 .4 . Consider a logistic system whose wtfs are the same as those of P2, 
whose rules of inference are modus ponens and substitution, which has a 
finite number of axioms, and for which the metatheorem *152 holds. Prove 
that the rules of modus ponens and substitution are necessarily both inde­
pendent. (In the case of modus ponens. this can be done by exhibiting an 
infinite list of tautologies (in the sense of §15) no two of which are variants 
of each other, and proving that no one of them is obtainable by substitution 
from any tautology other than a variant of itself.)
1 9 .5 . Prove the independence of the axioms and rules of Pw (see exercise 
12.7). Except in the case of the rule of substitution, use the method of truth- 
tables.
1 9 .6 . Let P^be the system obtained from P2 by deleting / from among the 
primitive symbols, and making only such further changes as this deletion 
compels, namely, omitting the formation rule lOi and the axiom fl04. 
Prove that the system P+ is not complete. Determine which of the axioms of 
Pb (exercise 18.3) are theorems of P+ and which not.
X9 .7 . Discuss the independence of the rule of modus ponens in the system 
P+. Does this independence follow trivially from any result already estab­
lished (in text or exercises)? If not, how can it be shown?
1 9 *8 . Using modus ponens and substitution as rules of inference, find 
axioms for the following many-valued propositional calculus (due to

---


116
THE PROPOSITIONAL CALCULUS
[Chap. I
Lukasiewicz — cf. footnote 276). There are three truth-values, 0, 1, 2, of 
which 0 is designated. There are two primitive constants /* and fz, to which 
1 and 2 are assigned as values respectively. And there is one primitive con­
nective, i d , which is binary and to which the following truth-table is assigned:
p
1
9
| P = > 9
0
0
! 
0
0
1
1
0
2
2
1
0
1 
0
1
1
0
1
2
1
2
0
0
2
1
0
2
2
0
Prove a modified deduction theorem for this system,that if Av A3». . An i- B, 
then Ax, Az, .. „ An-l [■ An D . A Bn B ;  and hence prove analogues of 
**150 and *152.
1 9 .9 . Consider an interpretation of Px by means of four truth-values, 0, 1, 2, 
3, of which 0 is the only designated truth-value, and 3 is assigned to the constant 
/as value. For each of the following different truth-tables of i d , discuss the sound­
ness of the interpretation:
p
?
! 
(i)
1 P => q
(2)
P =>q
(3)
P=>q
w
p=»q
(6)
p=>q
(0)
p=>q
0
0
0
0
0
0
0
0
0
1
0
1
2
3
0
0
0
2
0
2
3
0
0
0
0
3
0
3
1
1
0
0
1
0
0
0
0
0
0
0
1
1
0
0
0
0
0
2
1
2
0
2
0
0
0
0
1
3
0
2
0
0
0
0
2
0
0
0
0
0
0
0
2
1
0
1
0
1
2
2
2
2
0
0
0
0
0
0
2
3
0
1
0
3
0
0
3
0
0
0
0
0
0
0
3
1
0
0
0
0
0
0
3
2
0
0
0
0
0
0
3
3
0
0
0
0
0
0

---


§19]
EXERCISES ig
117
IQ .IO - Itm a y  happen th a ta  sound interpretation of 
by means of a system  
of truth-values and tru th -tab les is reducible to the principal interpretation (§10) 
by replacing th e designated tru th -v alu es everyw here by t and the non-designated 
truth-values everyw here by f. Follow ing C arnap, let us call such a sound in ter­
pretation of P* a normal interpretation, and oth er interpretations of Ps, non- 
normal interpretations.m  T hen a norm al interpretation of Pt m ay be th ought of 
as differing from  the principal interpretation only in th at, after division of 
propositions into true and false in ordinary fashion, some further subdivision is 
made of one or both categories. B u t a sound non-norm al interpretation differs 
from th e principal interpretation in some m ore drastic way.
Of the sound interpretations of P i found in 19.9, determ ine which are norm al 
interpretations and which are non-norm al interpretations. Also determ ine which 
can be rendered norm al w ith o u t loss of soundness, by changing only the way in 
which th e truth-values are divided into designated and non-designated tru th - 
values.
IQ ’ I  I .  C onsideraninterpretation of P l by m eans of six truth-values, 0, 1, 2, 
3, 4, 5, of w hich 0 and 1 are th e  designated truth-values, and 5 is assigned to 
the constant /  as value, the tru th -tab le of id being as follows:
p
? 
1I p =>?
0
0 
!
0
0
1
0
0
2
0
0
3
4
0
4
4
0
5
4
1
0
0
1
1
0
1
2
2
1
3
3
1
4
4
1
5
4
p
?
1 P => q
2
0
1 
0
2
1
1
2
2
0
2
3
4
2
4
1 
4
2
5
3
3
0
0
3
1
1
3
2
0
3
3
0
3
4
0
3
5
2
p
?
I p => ?
4
0
I 
0
4
1
0
4
2
1 
o
4
3
1 
0
4
4
0
4
5
0
5
0
0
5
I
0
5
2
0
5
3
0
5
4 
'
0
5
5 
1i 
0
(1) Show th a t the in terp retatio n  is sound. (Suggestion: Let A  id B and A  be 
tautologies (in the six tru th -v alu es). I t follows im m ediately from the fourth, 
fifth, sixth, ten th , eleventh, an d  tw elfth entries in th e  table th a t B cannot have 
the value 3, 4, or 5 for any system  of values of its variables. Hence it follows th a t 
B cannot have the value 2 for a system  of values of its variables, because if it did,
WBThis is not Carnap’s terminology but an adaptation of it to the present context, the 
word "interpretation” being used by Carnap in a somewhat different sense from ours. 
The possibility of sound interpretations of the propositional calculus (in any one of its 
formulations) which are not normal was pointed out, in effect, by B, A. Bernstein in 
the Bulletin of the American Mathematical Society, vol. 38 (1932) pp. 390, 592; also 
independently by Carnap in his book, Formahzation of Logic (1943). Sec further a re­
view of the latter by the present writer in The Philosophical Review, vol. 53 (1944), 
pp, 493-498.

---


118
THE PROPOSITIONAL CALCULUS
[Chap. I
the value 3 would be obtained for B upon interchanging the values 2 and 3 in 
this system of values of its variables. Hence B is a tautology.)
(2) Use this interpretation as a counterexample to show that the following 
statement is false: "In a sound interpretation of Pt the truth-table of s  is 
symmetric in the sense that, if p =  q has a designated value for given values of 
p and q, it also has a designated value upon interchanging the values of p and q.n
(3) Discuss the question in what way or ways it is possible to weaken this 
statement so as to obtain a true metatheorem of interest.
Z 9 .I2 - Using an interpretation of Pt by means of the three truth-values 0, X, 
2, of which 0 and 1 are designated truth-values, and 2 is assigned to the constant 
/ as value, show that the following statement is false: “In a sound interpretation 
of Px, and for given values of p , q, and r, if p s  q and f s r  have designated 
truth-values, then p ~  r must have a designated truth-value.” {Suggestion: The 
most obvious method is to use for zs the truth-table of §15, with 0 and 2 in the 
roles of t and f respectively, and to give to p r> q the value 1 whenever either 
p or q has the value 1. A different method is suggested by a remark of Church 
and Rescher in their review of a paper by Z. P. Dienes, in The Journal of Sym­
bolic Logic, vol. 15 (1950), pp. 69-70.)

---


II. The Propositional Calculus (Continued)
