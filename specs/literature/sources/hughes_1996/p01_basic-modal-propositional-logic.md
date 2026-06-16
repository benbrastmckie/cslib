<!-- Source: Hughes & Cresswell (1996). A New Introduction to Modal Logic. Routledge. Part I: Basic Modal Propositional Logic (Chapters 1-6, pages 3-130). -->

THE BASIC NOTIONS 
In this chapter we introduce the basic notions of modal propositional 
logic. Modal logic is based upon the 'ordinary' (two-valued) Propositional 
Calculus, and when we use the expression 'Propositional Calculus' (or the 
abbreviation 'PC') simpliciter, it is to this non-modal system of logic that 
we shall be referring.1 The present chapter begins by outlining, in a very 
summary fashion, those elements of PC which we shall take for granted 
in what follows, and at the same time explains some of the terminology 
which we shall use throughout the book. 
The language of PC 
We take as primitive (or undefined) symbols of PC the following: 
A set of letters: p, q, r, ... (with or without numerical subscripts). We 
suppose ourselves to have an unlimited number of these. 
The following four symbols: ~, V , (, ). 
Any symbol in the above list, or any sequence of such symbols, we 
call an expression. An expression is either a formula — more exactly a 
well-formed formula (wff) — or else it is not. We are concerned only 
with expressions which are well-formed formulae (wff). The following 
formation rules of PC specify which expressions are to count as wff: 
FR1 
A letter standing alone is a wff. 
FR2 
If α is a wff, so is ~α. 
FR3 
If α and β are wff, so is (α V β). 
In these rules the symbols α and β are used to stand indifferently for any 
expressions. Thus the meaning of FR2 is: the result of prefixing ~ to any 
3 


A NEW INTRODUCTION TO MODAL LOGIC 
wff is itself a wff. Symbols used as α and (3 are used here are known as 
metalogical variables. They are not among the symbols of the system (PC 
in this case), but are used in talking about the system. 
Examples of wff are: p, ~ q, 
q, (p V ~ q), ((p V r) V ~ (q 
V ~ (~ r V /?))). For convenience, however, we allow ourselves to omit 
the outermost brackets round any complete wff (though not any 
subordinate part thereof). No ambiguity in interpretation or unclarity 
about what is permitted by the rules will result from this notational 
simplification. 
Interpretation 
We interpret the letters as variables whose values are propositions. We 
shall usually call them propositional variables. We assume that the reader 
is familiar with the notion of a proposition, and shall not enter into the 
philosophical issues which this notion raises. Rough synonyms of 
'proposition' are 'statement' and 'assertion', where these words are used 
to refer to what is stated or asserted, not to the act of stating or 
asserting. Every proposition is either true or false, and no proposition is 
both true and false. (Hence if something is neither true nor false, or is 
capable of being both true and false, it is not to count as a proposition in 
the present context.) Truth and falsity are said to be the truth-values of 
propositions. 
Now it is possible to form more complex propositions out of simpler 
ones. E.g., out of the proposition that Brutus killed Caesar we can form 
the proposition that it is not the case that Brutus killed Caesar. This is a 
proposition which is true if the original proposition is false, and false 
otherwise. In general, putting 'it is not the case that' in front of a 
sentence will result in a sentence which expresses a proposition which is 
true if the original sentence expresses one which is false, and a false 
proposition if it does not. 
Similarly, from the proposition that Brutus killed Caesar and the 
proposition that Cassius killed Caesar we may form the proposition that 
either Brutus killed Caesar or Cassius killed Caesar. This proposition will 
be true iff (if and only if) at least one of the original propositions is true, 
and therefore false iff both of these are false. 
'It is not the case that' and 'either ... or ...', when used in the way we 
have just described, may be said to be proposition-forming operators on 
propositions, because they make new propositions out of old ones. The 
propositions on which such an operator operates are called its arguments. 
4 


THE BASIC NOTIONS 
If an operator requires only a single argument, as 'it is not the case that' 
does, it is said to be monadic; if, like 'either ... or ...', it requires two, 
it is said to be dyadic. 
Our explanation of these operators, 'it is not the case that' and 
'either... or ...', showed that the truth-value of a proposition formed by 
means of either of them depends in every case only on the truth-value of 
the operator's argument or arguments. In other words, whenever we are 
given the truth-value of the argument or arguments, we can deduce the 
truth-value of the complex proposition. An operator which has this 
property is said to be a truth-functional operator, and the propositions it 
forms are said to be truth-functions of its arguments. Not all 
proposition-forming operators are of this kind. For example, given merely 
the truth or falsity of the proposition that Brutus killed Caesar we cannot 
deduce the truth or falsity of the proposition that Napoleon believed that 
Brutus killed Caesar; and given merely that two propositions are both true 
we cannot deduce from this either the truth or the falsity of the 
proposition that the first follows logically from the second (though if we 
are given that one proposition is false and another true, we can deduce 
from this that it is false that the first follows logically from the second). 
Hence although 'Napoleon believed that' and 'follows logically from' are 
proposition-forming operators on propositions (monadic and dyadic 
respectively), they are not truth-functional operators. 
We interpret ~ and V as 'it is not the case that' and 'either ... or ...' 
respectively, in the senses we have explained, and we usually read them 
simply as 'not' and 'or'. ~ so interpreted is called the negation sign; ~p 
is said to be the negation of p. Using 1 and 0 for the truth-values truth 
and falsity respectively, we can express the meaning we attach to ~ in 
the following basic truth-table for negation: 
~ 
1 
0 
0 
1 
Here the left-hand column tabulates the possible truth-values of a given 
proposition, and the right-hand column sets down the corresponding 
truth-values of the negation of that proposition. When interpreted in the 
way we have described, V is known as the disjunction sign and its 
arguments are called disjuncts; p V q is said to be the disjunction of p 
and q. The basic truth-table for disjunction is: 
5 


A NEW INTRODUCTION TO MODAL LOGIC 
V 
1 0 
1 
0 
1 1 
1 0 
The possible truth-values of the first disjunct are tabulated in the leftmost 
vertical column and those of the second in the topmost horizontal row. 
The truth-value of their disjunction is found by reading across and down. 
These basic truth-tables bring out clearly the truth-functional nature of 
the operators. In fact, not merely ~ and V , but all operators in PC, are 
truth-functional and for this reason PC is sometimes called the theory of 
truth-functions. We said earlier that we interpret/?, q, r, ... as variables 
whose values are propositions; but in view of the fact that the only feature 
of the arguments of the operators which is relevant to the truth-value of 
the complex propositions they form is their truth-value, it is equally 
satisfactory from a formal point of view to regard the variables as having 
as their range of values, not the whole infinite set of propositions, but 
simply the two truth-values 1 and 0. 
Further operators 
A number of other operators can be defined in terms of the primitive 
ones. We introduce three new operators, A , D and ≡, though it would 
be possible to have several others as well. The definitions are: 
[Def A] (α A β) =df ~ ( ~ α V ~β) 
[Def D] (α D β) = d f ( ~ αV β) 
[Def ≡] (α - β) =df ((α D β) A (β D α)) 
In these definitions a and 0 represent any wff of PC and the symbol 
' =df' is read as 'is defined as'. The meaning of the first definition is that 
whenever we have a wff of the form ~ ( ~ V 
), where the blanks 
are filled by any wff we please, we can replace this wff by an expression 
which consists of the wff which filled the first blank followed by a A 
followed by the wff which filled the second blank, the whole being 
enclosed in brackets. Analogous explanations apply to the two other 
definitions. Similarly, we can expand any expression of the form on the 
left into the corresponding expression of the form on the right. 
Expressions which can be transformed, by applying definitions, into 
wff as specified by the original formation rules, are themselves to count 
6 


THE BASIC NOTIONS 
as wff. When a wff contains no symbols except primitive ones it is said 
to be written in primitive notation. The definitions enable us to write all 
wff in primitive notation if we wish to do so. 
Interpretation of A, D and = 
The interpretation we have already given to ~ and V will determine the 
interpretation we give to the operators defined in terms of them. Thus, we 
can calculate the truth-values of p A q for all possible truth-values of p 
and q by calculating the appropriate truth-values of the wff of which it is 
an abbreviation, viz. ~ (~p V ~ q), and the basic truth-tables for ~ and 
V enable us to do this. It turns out that p A q will be true when both p 
and q are true, but false in all other cases. The basic truth-table for A 
will therefore be: 
A 
1 0 
1 
0 
1 0 
0 0 
When A is so interpreted, it is called the conjunction sign; it may be read 
as 'and'. A wff formed with A is known as a conjunction, and the 
arguments are called conjuncts. 
Similar considerations give the following basic truth-table for D: 
D 
10 
1 
0 
1 0 
1 1 
I.e. a proposition formed with D is false when the first argument is true 
and the second false, but true in all other cases. When so interpreted, D 
is known as the (material) implication sign. It may be read as 
'(materially) implies' or as 'if [the first argument], then [the second 
argument]'. The first argument is known as the antecedent, the second as 
the consequent. The precise relation of material implication to the various 
uses of the word 'if in English raises complex questions into which we 
shall not enter here. It may plausibly be claimed, however, that material 
implication represents the truth-functional component in the meaning of 
'if in at least a great many of its standard uses. 
The basic truth-table for ≡ works out as: 
7 


A NEW INTRODUCTION TO MODAL LOGIC 
= 
1 0 
1 
0 
1 0 
0 1 
I.e. a proposition formed with ≡ is true when both arguments have the 
same truth-value, false when they have different truth-values. When so 
interpreted, = is known as the (material) equivalence sign. It may be 
read as 'is (materially) equivalent to', or as 'if and only if. 
Clearly 
these new operators, 
like the primitive ones, 
are 
truth-functional. 
(We could have chosen other operators than ~ and V as primitive. 
Some authors, for example, take ~ and A as primitive and define V in 
terms of these. But whatever primitives we use, provided that all the 
operators can consistently be given the basic truth-tables listed above, the 
system of PC so obtained will be exactly equivalent to the one we have 
set down here.) 
Validity 
If we regard the variables, p, q, r, ... as taking the whole range of 
propositions as their values, we can say that a wff of PC becomes a 
proposition when all its variables are replaced by propositions. A wff is 
said to be valid iff the result of every such replacement is a true 
proposition. (It is assumed that the replacement is carried out uniformly, 
i.e. that two or more occurrences of the same variable are always 
replaced by the same proposition.) If, however, we speak instead of the 
variables taking simply the two truth-values 1 and 0 as their values, we 
shall say that a wff is valid iff it always has the value 1, no matter what 
truth-values are (uniformly) assigned to its variables. We shall normally 
choose to speak in this second way; since all the operators in PC are 
truth-functional, exactly the same formulae will turn out to be valid in 
each case. Simple examples of valid wff are p V ~p and (p A q) D p. 
(A valid wff of PC is often called a tautology or a PC-tautology.) 
A wff is said to be unsatisfiable iff it always has the value 0, no matter 
what truth-values are (uniformly) assigned to its variables. A simple 
example of an unsatisfiable wff is p A ~ p. Many wff, such as p D q, 
are of course neither valid nor unsatisfiable. 
Later in this chapter we shall extend this definition of validity to cover 
the formulae of modal logic, and to make the extended definition more 
8 


THE BASIC NOTIONS 
easily comprehensible we shall express it in the form of a parlour game. 
As a preliminary to this let us now consider how we might devise a 
simple game based on the definition of PC-validity which we have just 
mentioned. The game could take this form. We give a player a sheet of 
paper on which we have previously written a number of letters of the 
alphabet (preferably taken from the series, p, q, r, ... etc.). We shall 
refer to the player and the sheet as a setting of the PC game, or more 
succinctly a PC-setting. PC-settings will differ only in the list of letters 
on the sheet of paper. 
We then call out to the player wff of PC, to which the player is to 
respond by either raising his or her hand or keeping it down. But each 
call must be appropriately prepared for, in that before a wff α is called 
we must have previously called all the formulae which occur as parts of 
a, beginning with the variables. E.g., if (~ p V p) is to be called we 
must first call p, and then ~ p and only then may we call (~p V p). The 
player's instructions are as follows: 
1. If a single letter (variable) is called, raise your hand if that letter is 
on the sheet; keep it down if it is not. 
2. If ~ α is called (where α is a wff) raise your hand if you kept it 
down when α was called; keep it down if you raised it when α was 
called. (Remember that if —α has been appropriately prepared for, α 
must have already been called.) 
3. If (α V β) is called, raise your hand if you raised it for α or for β; 
keep it down if you kept it down for both α and β. 
Using the definitions of D, A and ≡ we can easily derive rules for 
responding to formulae containing these operators. Alternatively we can 
transform all formulae into primitive notation before we begin. It might 
be worth stating the rule for D explicitly: 
3a. If (a D β) is called, raise your hand if you kept it down for α or 
raised it for β; keep it down if you raised it for α and kept it down for 
It is not difficult to see that in any PC-setting the rules require the 
player to respond unambiguously to any PC formula, provided that it is 
appropriately prepared for. If the player in a PC-setting raises his or her 
9 


A NEW INTRODUCTION TO MODAL LOGIC 
hand when a PC wff α is called, we shall say that α is successful in that 
setting. Many formulae will be successful in some settings but not in 
others (depending of course on which letters appear on the sheet for a 
given setting). But there will be some formulae which will be successful 
in every PC- setting (e.g. p V ~p). These we call PC-successful. 
To make explicit what must be becoming an obvious parallel, let us 
call the sheet of variables an assignment of truth-values with the idea that 
a variable has the value 1 if it is on the sheet and 0 otherwise. On this 
understanding, when the player's hand is raised when a wff α is called it 
will mean that α has the value 1, and when the player's hand is kept 
down when α is called it will mean that α has the value 0. The rules 1, 
2 and 3 for responding to formulae when thus translated exactly reflect 
the basic truth-tables for ~ and V. A formula will be successful in a 
PC-setting iff it has the value 1 for the corresponding assignment of truth-
values to its variables. And a formula will be PC-successful iff it is has 
the value 1 for every PC-assignment. I.e., the PC-successful wff are 
precisely those which are PC-valid. 
Since for any wff α containing n variables we need only consider 
sheets which contain a selection (possibly all or possibly none) of those 
n variables (for clearly the responses to variables not in α cannot affect 
the response to a), we can set out all the relevantly different PC-settings 
on 2n sheets. So we could check whether a is valid by preparing such a 
set of sheets and calling α (with the appropriate preparatory calls) for 
each of them. This procedure can be codified by what is called the truth-
table method of testing for PC-validity. 
Testing for validity: (i) the truth-table method 
In this method of testing a PC formula, a, for validity, all possible PC 
value-assignments, i.e. all assignments of truth-values to the propositional 
variables in α, are tabulated, and for each such value-assignment, the 
basic truth-tables for the operators are used to calculate the truth-value of 
α as 1 or 0. The result is a column of Is and/or 0s. This column is known 
as the truth-table of the wff. If and only if it consists entirely of Is, the 
wff is valid. 
An example should make the procedure clear. Let α be ((p D q) A r) 
D ((~r V p) D q). Here we have three distinct variables and therefore 
eight PC value-assignments. The construction of the truth-table proceeds 
as follows: 
10 


THE BASIC NOTIONS 
p q r 
((P D q) A r) D « ~ r 
V P ) ?q) 
1 1 1 
1 
1 
0 
1 
l 
1 1 0 
1 
0 
1 
1 
l 
1 0 1 
0 
0 
0 
1 
0 
1 0 0 
0 
0 
1 
1 
0 
0 1 1 
1 
1 
0 
0 
1 
0 1 0 
1 
0 
1 
1 
1 
0 0 1 
1 
1 
0 
0 
1 
0 0 0 
1 
0 
1 
1 
0 
(1) 
(2) 
(6) (3) (4) 
(5) 
The complete list of value-assignments is set down to the left of the 
vertical line. The columns to the right are numbered in the order in which 
they are obtained. Thus column (1), for p D q, is obtained from the 
columns under p and q by the basic truth-table for D; column (2) is 
obtained from (1) and the column under r, by the basic truth-table for A ; 
... until finally column (6), the truth-table for the whole wff, is obtained 
from (2) and (5). Since (6) consists entirely of 1s α is PC-valid. 
Testing for validity: (ii) the Reductio method 
A formula can usually be tested more expeditiously by trying to find a 
falsifying value-assignment for it. The Reductio method enables us to find 
such a value-assignment if there is one. 
We begin by supposing that there is such an assignment for which α 
has 0. We express this supposition by writing 0 under the main operator 
of α. From this supposition certain consequences follow, by the basic 
truth-tables, about the values which must be assigned to certain 
well-formed parts of α; e.g., if α is of the form β D γ, it can only have 
0 if β has 1 and γ has 0. From these new values certain other 
consequences follow in the same way, and so on, until finally we either 
(i) reach a consistent value-assignment to all the variables in α (in which 
case a is invalid), or (ii) find that we cannot reach such a consistent 
value-assignment (in which case α is valid). 
As an example, let α be the formula we used to illustrate the 
truth-table method, viz. ((p D q) A r) D ((~r V p) D g). We set out 
the whole working immediately and then explain it. 
11 


A NEW INTRODUCTION TO MODAL LOGIC 
((p D q) Ar) D ((~ r Vp ) D q) 
0 10 
11 
0 
1 0 10 
00 
9 4 8 
25 
1 
11 12 6 10 
3 7 
The numerals under the truth-values indicate the order of the steps. Step 
1 is the initial assignment of 0 to a. Since α is of the form β D γ if α 
has 0, β must have 1 (step 2) and γ must have 0 (step 3). The Is at steps 
4 and 5 are required by the table for A since β is a conjunction and must 
have the value 1. The remaining steps should now be clear. We finally 
reach the conclusion (indicated by underlining) that if we are to have α 
with 0 r must have both the value 1 and the value 0. Hence a can never 
have 0, and is therefore valid. 
Other cases are sometimes not so simple. Suppose that α is the 
converse of the previous formula, 
viz. ((~ r V p) D 
q) D 
((p D q) A r). Steps 1, 2 and 3 can proceed as before, but the values at 
steps 2 and 3 do not determine further values uniquely. We can however 
list exhaustively the alternatives left open at step 2 by the assumption that 
((~r V p) D q) has 1, as follows: 
((~r Vp) D q)D ((p D q) A r) 
1 
0 
0 
2 
1 
3 
(a) 
1
1
1
0 
0 
(b) 
0 
1 1 0 
0 
(c) 
0 
1 0 0 
0 
(a), (b) and (c) represent all the value-assignments to (~ r V p) and q 
which are compatible with the truth of (( ~ r V p) D q).If each of these 
leads us to an inconsistency, α is valid; if even one of them is compatible 
with a consistent assignment to the variables, α is not valid. In fact (b) 
and (c) both lead to inconsistencies; but (a) does not - it is compatible 
with q = 1, r = 0 and p = 1 or 0. Hence the whole formula is not valid. 
Provided we consider in this way all alternative value-assignments as 
the need arises, we can test the validity of any wff of PC whatever by the 
Reductio method. We shall make considerable use of this method in 
Chapter 4. 
Each of the two methods we have described gives us an effective (i.e. 
12 


THE BASIC NOTIONS 
mechanical and finite) procedure for deciding of any given wff of PC 
whether it is valid or not. Another way of expressing this is by saying 
that each method gives us a decision procedure for PC. 
Some valid wff of PC 
We list here some valid PC wff which we shall use in the next few 
chapters. In some cases we give, in addition to a reference number, a 
name by which the formula is commonly known and an abbreviation by 
which we shall usually refer to it in this book. 
PC1 
(p A q) D p 
PC2 
(p A q) D q 
PC3 
(p D q)D ((p D r)D (pD (q A r))) 
[Law of Composition-Comp] 
PC4 
p D (q D (p A q)) 
[Law of Adjunction-Adj] 
PC5 
(pD q)D ((qDp)D 
(p = q)) 
PC6 
(p D q) D ((q D r) D (p D r)) 
[Law of Syllogism-Syll] 
PC7 
(p D (q D r)) D ((p A q) D r) 
[Law of Importation-Imp] 
PC8 
(p D q) D ((q D (rD s)) D ((p A r) D s)) 
PC9 
p D (p V q) 
PC10 
q D(p V q) 
PC11 
(pD q)D ((rD q) D ((p V r) D q)) 
PC12 p ≡ ~ ~ p 
[Law of Double Negation-DN] 
PC13 
(p V q) = ~ ( ~ p A ~q) } 
rrk . . 
. 
_. _,_ 
PC14 J A J , ~(~p V ~J) i 
[ 
^ 
LaWS~DeM] 
PC 15 
(p D q) = (~q D ~p) 
[Law of Transposition-Transp] 
PC16 
(p V q) m (q V p) 1 
PC17 
(p A q) s (q A p) J 
PC18 
((p V q) V r) = (p V (q V 
PC19 
((p A q) A r) = (p A (q A r)) 
PC20 p = (p V p) 
PC21 p = (p A p) 
[Commutative Laws—Comm] 
r))\ 
r [Associative Laws—Assoc] 
Basic modal notions 
On p. 5 we called attention to the distinction between truth-functional and 
non-truth-functional operators, and we noted that all the operators which 
we use in PC are interpreted purely truth-functionally. In modal logic, 
however, we are going to be concerned in addition with a number of non-
truth-functional concepts, and to express these we shall extend the 
13 


A NEW INTRODUCTION TO MODAL LOGIC 
language of PC by adding to it some new operators which we shall 
interpret in a non-truth-functional way. 
To begin with, we shall add to the language of PC a new monadic 
operator, L, with the formation rule that if α is a wff, so is Lα. We shall 
call L the necessity operator, and our intended interpretation of it is that 
it is to express, in the form of a proposition-forming operator on 
propositions, the notion which is commonly expressed by English words 
or phrases such as 'necessarily', 'must be', 'is bound to be'. In ordinary 
English such expressions, like the truth-functional 'not', are frequently 
found in the middle of a sentence rather than at the beginning; but just as 
it is possible, at the cost of a little artificiality, to replace an embedded 
'not' by the phrase 'it is not the case that' at the beginning of the 
sentence, and thereby bring out more clearly its nature as an operator on 
propositions, so we can, for example, re-cast a sentence of the form 'A 
is bound to be B' as 'It is bound to be the case that A is B'. Necessity is 
called a modal notion, presumably because being necessarily true has been 
thought of as a mode or manner in which a proposition can be true. 
We shall usually read Lp as 'Necessarily p'. But in doing so we do not 
intend to claim that our use of L will reflect all the standard English uses 
of 'necessarily' and the other expressions we have mentioned, any more 
than we could claim that the basic truth-table for conjunction provides an 
adequate analysis of all standard English uses of 'and'. On the other hand, 
we do not want to restrict its meaning to a single narrowly conceived 
sense of 'necessarily', etc. Very often, for example, when we say that 
something must be so, we can be taken to be claiming that it is so; and 
if we take L to express 'must be' in this sense, we shall want to have it 
as a principle that whenever Lp is true, so is p itself. On the other hand 
there are uses of words such as 'must' and 'necessary' in which they 
express not what necessarily is so but rather what morally ought to be so; 
and if we interpret L in accordance with these uses we shall want to allow 
the possibility that Lp may be true but p itself false, since people do not 
always do what they ought to do. As we shall see in the next chapter, it 
will prove possible to devise systems of modal logic which contain 'If Lp 
then/?' as a principle, and other systems which do not. In fact, one of the 
important features of modal logic is that out of the same basic material we 
can construct a variety of systems which reflect a variety of 
interpretations of L, within the range which can be indicated, somewhat 
loosely, by calling it a necessity operator. We shall even sometimes 
extend the interpretation of L a little beyond these limits; for fruitful 
systems of logic have been inspired by the idea of taking the necessity 
14 


THE BASIC NOTIONS 
operator to mean, for example, 'It will always be the case that...', 'It is 
known that...' or 'It is provable that...'. All this should become clearer 
as we proceed. 
One thing that should be clear already, however, is that in any of the 
interpretations we have referred to, the necessity operator is not a truth-
functional one: that is, the truth-value of p itself is not always sufficient 
to determine the truth-value of Lp. Hence we cannot define L in terms of 
any combination of the PC operators, and we therefore introduce it as a 
new primitive symbol. 
Another notion which leads, in a parallel way, to a monadic non-truth-
functional operator is one expressed by terms such as 'possibly', 'can be', 
'may be'. We shall use M as an operator with this meaning, and we shall 
usually read Mp as 'possibly p'. If we already have L in our logical 
language, however, we do not need to have M as a new primitive symbol; 
for to say that it is possible that p is equivalent to saying that it is not 
necessary that not-p, and we can therefore define Ma, for any α, as 
~L~α. 
Thus for every interpretation of L there will be a corresponding 
interpretation of M: if Lp means that p is necessarily true, Mp will mean 
that p is possibly true, if Lp means that it is morally obligatory that p, Mp 
will mean that it is morally permissible that p (not obligatory that not-p), 
if Lp means that it will always be the case that p, Mp will mean that it 
will sometime be the case that p, and so forth. (If we had chosen to take 
M as primitive we could have defined L as ~ M ~ . Whether to take L or 
M as primitive is a matter of taste. We shall continue to take L as 
primitive and M as defined.) Impossibility, along with necessity and 
possibility, is often also classified as a modal notion, but it does not call 
for special discussion here since there is no difficulty in expressing it by 
the operator ~M (or alternatively L~). Propositions which are neither 
necessary nor impossible are called contingent.2 
A relation between propositions that we may easily express with the 
tools at our disposal is that of necessary implication. Necessary 
implication is sometimes called strict, in contrast to material, implication, 
and we shall have more to say about it in Chapter 11. It is important not 
to confuse L(p D q), which means that the whole hypothetical 'if p then 
q' is a necessary truth, or that q follows logically from p, with p D Lq, 
which means that if p is true then q is a necessary truth. Unhappily, these 
are often confused in ordinary discourse, sometimes with disastrous 
results; and neglect of the distinction is made all the easier by the 
ambiguity of such common idioms as 'If ... then it must be (or is bound 
15 


A NEW INTRODUCTION TO MODAL LOGIC 
to be) the case that —'. To make things worse, the structure of such 
sentences is more closely analogous to that of p D Lq, but one suspects 
that most frequently what the speaker intends to assert (or at least all they 
are entitled to assert) is something of the form L(p D q). Thus someone 
who says, 'If it rains throughout December it is bound to rain on 
Christmas Day' probably means to assert that 'it will rain on Christmas 
Day' follows from 'it will rain throughout December' (which is true, 
since Christmas Day is in December); but they could be taken to be 
asserting that if it rains throughout December then it is a necessary truth 
that it will rain on Christmas Day (which, at least if it does rain 
throughout December, is false because, come what may about the 
weather, 'it will rain on Christmas Day' expresses a contingent 
proposition, not a necessary one). 
Perhaps no one, except in their dullest moments, would be taken in by 
this example. But people have, it appears, confused the necessary truth 
of 'If a thing is going to happen it is going to happen' with the view that 
whatever happens happens by logical necessity, or even argued for 
Fatalism by inferring illicitly from the former to the latter. And in 
epistemological discussions the fact (if it is a fact) that, of necessity, if 
someone knows that p then p is true has sometimes been held to show 
something which does not follow from it at all, viz. that only necessary 
truths can ever be known. This transition is facilitated if we express the 
premiss of the argument by the ambiguous but more colloquial 'If you 
know something, it must be true (can't be false)'. Even a little study of 
modal logic can protect us from pitfalls in philosophy and elsewhere. 
The language of propositional modal logic 
We are now in a position to be able to specify precisely the language we 
shall use for all the systems of propositional modal logic which we shall 
describe in later chapters. Its symbols and rules are: 
Primitive symbols 
p, q, r, ... 
[propositional variables] 
~ , L 
[monadic operators] 
V 
[dyadic operator] 
(, ) 
[brackets] 
Formation rules 
FR1 A propositional variable is a wff. 
FR2 If α is a wff, so are ~α and Lα. 
16 


THE BASIC NOTIONS 
FR3 If α and β are wff, so is (α V β). 
Definitions 
Def A, Def D, Def = as in PC (p. 6), plus 
[Def M] Mα =df ~L ~ α 
As we did for PC, we adopt the convention that brackets enclosing a 
complete wff may be omitted. 
Clearly every wff of PC is also a wff of modal logic. A few examples 
of wff of modal logic which are not wff of PC are: Lp D p; MLp D p; 
L(L(p V q) D Mq); (Lp A Mq) D L(Lp V Mq); (MLMp A p) ≡ Lp. 
Validity in propositional modal logic 
Which modal formulae are we to count as valid? It is easy to give a 
general, intuitive account of validity for modal formulae exactly as we 
initially did for PC formulae, by saying that a wff is valid iff it 'comes 
out true' for every uniform replacement of its variables by propositions. 
In PC, because of the truth-functional nature of all the operators, this 
initial account led directly to a quite simple formal definition of validity. 
In modal logic, however, things are not as straightforward; for modal 
operators are not truth-functional, and it is not at all clear at the outset 
under what conditions propositions containing them are to count as true 
or false. The method of defining validity for modal wff which has proved 
most fruitful and widely applicable is based on the following ideas, which 
we shall state informally at first but which we shall express more 
rigorously later on:3 
(a) Whereas determining the truth-value of a non-modal proposition 
involves only a consideration of how things actually are, determining the 
truth-value of a proposition of the form 'Necessarily p' or 'Possibly p' 
involves a consideration of how things might have been, of the nature of 
conceivable states of affairs alternative to the actual one. 
(b) For each conceivable state of affairs there is a range of states of 
affairs which are possible relative to that one. (This reflects the idea we 
sometimes express by saying that if things were different a new range of 
possibilities might be opened up, so that things that are not even possible 
as things stand might be possible then.) 
(c) In any given conceivable state of affairs, 'Possibly p' counts as true 
iff p itself would be true in at least one state of affairs which is possible 
relative to that one, and 'Necessarily p' counts as true iff p itself would 
17 


A NEW INTRODUCTION TO MODAL LOGIC 
be true in every such state of affairs. 
With these ideas in mind we shall now describe a more elaborate 
version of the PC game described on p. 9. We shall call this game the 
modal game. Whereas the PC game involved only one player, in the 
modal game there can be any number (provided that there is at least one). 
We are to envisage these players as being seated in some way which 
determines precisely which players, if any, each player is to be able to 
see during the course of the game. Screens or some other devices might 
be used for this purpose; but since in this context being able to see 
someone means no more than taking note of that person's responses, it 
will be sufficient to specify, for each player, which players are to be 
watched and which ignored. There are no restrictions whatsoever on what 
'seeing arrangement' among the players may be made: thus we may 
decide that no one is to be able to see anyone at all, or at the opposite 
extreme that everyone can see everyone, or we may specify any 
intermediate arrangement; we may decide that some players shall be able 
to see themselves while others shall not; if player A can see player B, B 
may or may not be allowed to see A; and so forth. Finally, before the 
game begins, each player is provided, as the single player in the PC game 
was, with a sheet of letters. 
We shall call the set of players together with the specification of who 
is to be able to see whom, a seating arrangement, and this together with 
the players' sheets a setting for the modal game, or simply a setting. 
The game proceeds by calling, to the whole set of players at once, any 
wff of modal logic we choose, provided that, as in the PC game, its well-
formed parts, beginning with the variables, are called first. (We can again 
assume that the wff are written in primitive notation, with all defined 
operators eliminated, though we shall, for clarity, state the rule for wff 
containing M explicitly.) 
The instructions for each player are those numbered 1, 2 and 3 in the 
PC game, together with the following two for calls involving L and M: 
4. If Lα, is called (where α is a wff of modal logic), raise your hand 
if every player you can see raised his or her hand when α was called; 
otherwise keep your hand down. 
5. If Mα is called, raise your hand if at least one of the players you 
can see raised his or her hand when α was called; otherwise keep your 
hand down. 
As with the PC game, it should be clear that in each setting each wff 
of modal logic (when appropriately prepared for) will get, from each 
player, a unique response. In a given setting the call of a formula may of 
18 


THE BASIC NOTIONS 
course lead some players but not others to raise their hands, but if it leads 
every player without exception to raise his or her hand we shall say that 
that formula is successful in that setting. 
How then should we use these games to define validity in propositional 
modal logic? We have said that our underlying intuitive idea is that a wff 
should count as valid iff it is true for all values of its variables. In the 
case of the PC game what this means is that the wff must be successful 
no matter what sheet is given to the player. Now if we compare the PC 
game with the modal game, it is not hard to see that the PC game is 
simply the modal game played in a seating arrangement with just one 
player and with only PC wff being called. (Strictly speaking there are two 
possible seating arrangements with one player, according to whether that 
player can see himself or herself or not; but although these seating 
arrangements can lead to different results for wff containing L or M, they 
cannot do so for wff of PC.) This suggests that an appropriate 
generalization of our notion of validity to make it cover modal wff is that 
of being valid in a seating arrangement, in this sense: that a wff a is 
valid in a given seating arrangement iff in that seating arrangement all the 
players would raise their hands for α, no matter what sheets were 
distributed to them - or, to put this in another way, iff α would be 
successful in all settings based on that seating arrangement. 
If validity is thought of in this way, one consequence is that there will 
be as many different kinds of validity for modal formulae as there are 
different seating arrangements, and hence that we can have no unique 
account of validity in modal logic. At first sight this may seem 
undesirable; yet on reflection a plurality of criteria of validity is just what 
our earlier discussion of modal notions would lead us to expect. If 
'necessarily' and 'possibly' can be used in a variety of different senses, 
then it is quite reasonable to suppose that corresponding to each of these 
senses there will be a different range of acceptable seating arrangements. 
In fact the possibility of having different kinds of seating arrangements is 
part of what gives modal logic its richness. 
A simple example of a wff which is valid in a certain seating 
arrangement is Lp D p. Imagine a seating arrangement in which there are 
only two players, A and B, and both can see themselves and each other. 
Take player A. If p is on A's sheet, A will raise his or her hand for p, 
and hence, by the rule for D, will also raise it for Lp Dp. If p is not on 
A's sheet, A's hand will not be raised for p, and hence, since A can see 
A, by the rule for L it will not be raised for Lp either. So, by the rule for 
D, it must be raised for Lp D p in this case also. This means that A 
19 


A NEW INTRODUCTION TO MODAL LOGIC 
must raise his or her hand for Lp D p, whether p is on A's sheet or not; 
and B must do likewise, for the same reason. 
But although Lp D p is valid in this seating arrangement, it is not valid 
in every seating arrangement. For imagine a seating arrangement just like 
the previous one except that A cannot see himself or herself, and consider 
a setting in this seating arrangement in which p is on B's list but not on 
A's. Since B is the only player A can see, A's hand will be raised for Lp, 
but it will not be raised for p. So it will not be raised for Lp D p, and 
this shows that this wff is not valid in this seating arrangement. 
The case of Lp Dp illustrates some of the richness of modal logic. 
For it is not difficult to see that this wff is valid not only in the seating 
arrangement described two paragraphs back, where A and B can see 
themselves and each other, but also in any seating arrangement in which 
all players can see themselves. And this means that any sense of 
'necessary' in which whatever is necessary is true can be reflected by 
restricting the seating arrangements to those in which all players can at 
least see themselves. 
There are, however, some wff which are valid in every seating 
arrangement. For reasons to be given in the next chapter we shall say that 
these wff are K-valid. It is easy to see that all PC-valid wff are K-valid: 
for in responding to a PC wff a player in the modal game takes no notice 
of any other players, and a PC-valid wff is precisely one which any sheet 
of letters whatsoever would lead a player to raise his or her hand. An 
example of a specifically modal wff which is K-valid is one which is often 
called K: 
K 
L(p D q) D (Lp D Lq) 
The proof that this wff is K-valid is this: If it were not K-valid then, 
by the rules for D, there would have to be a setting in which some 
player, say A, 
(i) raises a hand for Lip D q), 
(ii) raises a hand for Lp, 
but 
(iii) does not raise a hand for Lq. 
There cannot, however, be any such setting. For by (iii) there must 
be a player, say B, whom A can see and whose hand was kept down for 
q. By (ii), since A can see B, B's hand must have been raised for p. 
Hence since B's hand was raised for p but not for q, it must have been 
kept down forp D q. This, however, conflicts with (i); for since A can 
20 


THE BASIC NOTIONS 
see B, (i) means that B's hand was raised for p D q. 
We can think of the modal game in this way: In any setting the players 
represent conceivable states of affairs or, as they are often called, 
alternative possible worlds, as we spoke of these near the beginning of 
this section; the players each player is allowed to see represent the states 
of affairs which are possible relative to the state of affairs which that 
player represents; and the letters on a player's sheet represent the 
propositions that are true in that state of affairs. Raising a hand and 
keeping it down represent respectively truth and falsity in the state of 
affairs the player represents. Hence what the K-validity of a wff means 
is that that wff would turn out to be true in every conceivable state of 
affairs, no matter what propositions we were to replace its variables by, 
no matter what was true or false in that state of affairs, and no matter 
what states of affairs were possible relative to that one. 
One might at this point raise the question of just what a possible world 
or conceivable state of affairs really is.4 This is a matter of some 
importance and controversy in metaphysics and in the application of 
modal logic to theories of meaning for natural language. Luckily 
however, from the point of view of logic it makes no difference just what 
they are, as may be seen from our discussion of the modal game in which 
the 'worlds' are players. In this book therefore we shall take no position 
on the ontological status of possible worlds. 
Exercises — 1 
1.1 
Show that the following wff are valid in every seating arrangement: 
(a) 
L(p D p) 
(b) 
(Lp V Lq) D Lip V q) 
(c) 
Lip A q) m (Lp A Lq) 
(d) 
Mp D (Lq D Mq) 
(e) 
M(p D q) = (Lp D Mq) 
1.2 
Show that in any seating arrangement in which there is a player who 
cannot see himself or herself Lp D p is not valid. 
1.3 
For each of the following wff devise a seating arrangement in which 
it is not valid: 
(a) 
Lip V q) D (Lp V Lq) 
(b) 
Mip D p) 
(c) 
(Lp D Lq) D L(p D q) 
(d) 
Lp D LLp 
21 


A NEW INTRODUCTION TO MODAL LOGIC 
1.4 
(a) 
Consider a seating arrangement in which every player A can 
see at most one player (who may be A or may be another player). Show 
that in such a seating arrangement Mp D Lp is valid. 
(b) 
Consider a seating arrangement in which a player A can see 
more than one player. Show that in such a seating arrangement Mp D Lp 
is not valid. 
Notes 
1 Most current logic textbooks give an account of PC in more or less detail. 
Terminology and notation vary somewhat but this should not confuse the careful 
reader. Despite its age the fullest introduction to the propositional calculus is still 
probably found in Church 1956. 
2 The notation L and M for the necessity and possibility operators dates from Feys 
1950 (for L) and Becker 1930 (for M). For a history of notation see appendix 4 
of Hughes and Cresswell 1968 (pp. 347-349). The commonly used • for L is 
due to F.B.Fitch and first appears in Barcan 1946. O for M dates from Lewis and 
Langford 1932. Other primitives have been studied. Hallden 1949b has a triadic 
operator in terms of which both the modal operators and all the truth-functional 
operators can be defined. Montgomery and Routley 1966 use contingency v (or 
non-contingency, A) to define the modal operators, though their definitions are 
only applicable to some systems of modal logic. (See Cresswell 1988.) 
3 The ideas which underlie this account of validity appeared in the late 1950s and 
early 1960s in the works of Kanger 1957a, Bayart 1958, Kripke 1959 and 1963a, 
Montague 1960 and Hintikka 1961. Anticipations can be found in Wajsberg 1933, 
McKinsey 1945, Carnap 1946, Meredith 1956, Thomas 1962 and other works. 
An algebraic description of this notion of validity is found in Jonsson and Tarski 
1951, though the connection with modal logic was not made in that article. Some 
remarks about the earlier history of modal logic are found in Chapter 11 below. 
4 Some interesting perspectives on this question may be found in the essays in 
Loux 1979. 
22 


2 
THE SYSTEMS K, T AND D 
Systems of modal logic 
For the rest of Part I we shall be concerned with a number of systems of 
propositional modal logic. The present chapter will deal with the first 
three of these. Our way of expounding the systems will be by the 
axiomatic method. Historically, modal systems were presented in this way 
before the discovery of an appropriate way to define validity for modal 
logic, and that is one reason for proceeding as we do. But another, and 
perhaps more significant, reason is that the axiomatic method allows us 
to define a class of wff without any reference to their meanings. 
An axiomatic basis for a logical system consists of (a) a specification 
of the language in which the formulae of the system will be expressed -
i.e. a list of primitive symbols, together with any definitions that may be 
thought convenient, together with a set of formation rules specifying 
which strings of symbols are to count as wff; (b) a selected set of wff, 
known as axioms; and (c) a set of transformation rules, licensing various 
operations on the axioms, and also (normally) on wff obtained from the 
axioms by previous applications of the transformation rules. The wff 
obtained from the axioms in this way, together with the axioms 
themselves, are known as the theorems of the system. All the systems of 
propositional modal logic which we shall consider will have the same 
language, the one specified in the previous chapter on p. 16; so in stating 
their bases we shall merely list their axioms and transformation rules. An 
axiomatic basis must be formulated in such a way that we can determine 
effectively (i) of any arbitrary string of symbols whether or not it is a 
wff, (ii) of any wff whether or not it is an axiom, and (iii) of any 
purported application of a transformation rule whether or not it is a 
genuine application of that rule. We therefore take care that our 
formulation of formation and transformation rules, and indeed our 
specification of a system as a whole, can be understood without reference 
23 


A NEW INTRODUCTION TO MODAL LOGIC 
to the interpretation of the symbols; this is often a matter of considerable 
importance when we come to demonstrate that a system has certain 
properties. The approach of the last chapter did, by contrast, specify a 
class of formulae: the wff valid in a seating arrangement, in terms of their 
meaning, for, as we said on p. 20, the players in the games can represent 
possible worlds, and so the account of validity developed there concerns 
the relation between symbols and what they stand for. Such an approach 
is often called a semantical approach to logic. An axiomatic approach is 
then often referred to as a syntactical approach. 
All this, however, does not mean that in choosing the axioms for a 
system we ought to keep all thought of interpretation out of our minds. 
For although we could in theory take any wff whatsoever as axioms, in 
practice our reason for choosing certain wff as axioms will usually be 
either that they are valid by some criterion of validity that we have in 
mind, or at least that they are plausible or interesting in some way which 
leads us to want to explore their consequences; and these are matters 
which involve the interpretation we give to our symbols and formulae. 
Analogously, when we are constructing a system with a certain criterion 
of validity in mind, we see to it that its transformation rules are such that 
when they are applied to valid wff the theorems they yield are always 
valid too. Such transformation rules are said to be validity-preserving 
(with respect to that account of validity). 
It is convenient at this point to explain some more of the terminology 
we shall use in discussing logical systems. When a formula is a theorem 
of a given system we shall say that it belongs to, or is contained in, or 
simply is in, that system. If two axiomatic systems, S and S', have 
different bases but contain exactly the same theorems, we shall say that 
S and S' are deductively equivalent, or sometimes simply that they are 
equivalent. If every theorem of S is also a theorem of S' (whether or not 
S' contains other theorems as well) we shall say that S' contains S; thus 
two systems are deductively equivalent iff each contains the other. If S' 
contains all the theorems of S and other theorems as well, we say that it 
properly contains S, or is a proper extension of S, and that S' is the 
stronger and S the weaker of the two systems. 
The system K 
On p. 20 we introduced the notion of what we called K-validity. The first 
system we shall consider is one which will turn out to have as its 
theorems precisely those modal formulae which are K-valid. This is 
usually known nowadays as the system K.1 Its axioms consist of all valid 
24 


THE SYSTEMS K, T AND D 
wff of PC, i.e. all the wff specified by the following axiom schema, 
PC 
If α is a valid wff of PC, then α is an axiom2 
together with the single distinctively modal wff 
K 
L(p D q) D (Lp D Lq) 
and it has the following three primitive (i.e. initially given) transformation 
rules: 
US (The Rule of Uniform Substitution): The result of uniformly replacing 
any variable or variables p1, ... , pn in a theorem by any wff β1, ... , βn 
respectively is itself a theorem. 
MP (The Rule of Modus Ponens, sometimes also called the Rule of 
Detachment): If α and α D β are theorems, so is β. 
N (The Rule of Necessitation): If α is a theorem, so is Lα. 
Where convenient we shall in future use the following notation: 
1. Where p1, ... , pn are some or all of the variables occurring in a wff 
α, and β1, ... , βn are any wff, we use the expression α[β1/p1, ... , βn/pn] 
to denote the wff which results from α by replacing ply ... , pnuniformly 
by ft, ... , βn respectively. 
2. Where a is a wff and S is an axiomatic system, we write |-s α to 
mean that that α is a theorem of S. Where no ambiguity is likely to arise 
we often omit the subscript 'S'. 
3. We express the derivability of one wff from one or more other wff 
by the symbol 
. 
Using this notation we could express the transformation rules more 
succinctly in this way: 
US: \-α - hα[β1/p1, - ,βn/Pn]. 
MP: |- α, α D 
β 
(- β. 
N: 
\-α 
\-Lα. 
US and MP are not specifically modal rules. US in particular is a rule 
that it is plausible to require of any logical system with a class of symbols 
to be interpreted as propositional variables, and MP simply reflects the 
25 


A NEW INTRODUCTION TO MODAL LOGIC 
truth-functional meaning of D. It is easy to see that both these rules are 
validity-preserving with respect to K-validity, though we shall prove this 
formally later. N, which is a specifically modal rule, also preserves It-
validity, for this reason: Suppose α is K-valid - i.e. in every setting every 
player would raise a hand for α; then every player that any player can see 
would raise a hand for α; so by the rule for L, every player would raise 
a hand for Lα - i.e. Lα is K-valid. 
Proofs of theorems 
We have said that the theorems of a system are those wff which can be 
derived from its axioms by applying its transformation rules. To prove a 
theorem is therefore to derive it in this way. More precisely, a proof of 
a theorem α in a system S consists of a finite sequence of wff, each of 
which is either (i) an axiom of S or (ii) a wff derived from one or more 
wff occurring earlier in the sequence, by one of the transformation rules 
or by applying a definition, a itself being the last wff in the sequence. 
(Note that by this account of what constitutes a proof of a theorem, every 
wff in a proof is itself a theorem; and also that one reason why we count 
the axioms themselves as theorems is that any axiom can be thought of as 
a one-line proof of itself.) 
We shall set out proofs in the following way. At the outset we state the 
theorem to be proved and give it a reference number. Each line of the 
proof itself contains three items: (a) a wff; (b) a reference number for that 
wff, written immediately before it; and (c) a justification for writing the 
wff, written on the left. This justification must consist in showing that the 
wff satisfies either condition (i) or condition (ii) mentioned above. In case 
(i) the justification entry consists of the reference number or name of the 
axiom in question (in the case of an axiom falling under the schema PC, 
if it is listed on p. 13, we cite the name or number assigned to it there; 
otherwise we simply write 'PC'). In case (ii) the justification entry refers 
by number to the earlier wff being used and indicates which 
transformation rule or definition is being applied. The application of US 
will be indicated in accordance with the notation explained above, noting 
within square brackets each variable being replaced and the wff replacing 
it. The application of MP and N will be indicated by 'X MP' and ' X N' 
respectively. 
We shall first prove two theorems in full detail, and then describe 
some methods of abbreviating proofs. Theorems will be numbered using 
the name of the relevant system; thus Kl will be the first theorem we 
prove in K, and so on. 
26 


THE SYSTEMS K, T AND D 
Kl 
L(p A q) D (Lp A Lq) 
PROOF 
PC1 
(1) (p A q) D p 
(1) X N 
(2) L((p A q) D p) 
K 
(3) L(pD q)D (Lp D Lq) 
(3)[pAqlp,plq] 
(4) L((p A q) D p) D (L(p A q) D Lp) 
(2), (4) X MP 
(5) L(p A q) D Lp 
PC2 
(6) (p A q) D q 
(6) X N 
(7) L((p A q) D q) 
(3)[pAq/p] 
(8) L((p A q)D q) D (L(p A q) D Lq) 
(7), (8) X MP 
(9) L(p A q)D Lq 
PC3 
(10) (p D q) D ((p D r) D (p D (q A r))) 
(10)[L(p Aq)lp, Lp/q,Lq/r] 
(11) (L(p A q) D Lp) D ((L(p A q) D Lq) D 
(L(p A q)D (Lp A Lq))) 
(5), (11) X MP 
(12) (L(p A q)D Lq) D (L(p A q) 
D (Lp A Lq)) 
(9), (12) X MP 
(13) (L(p A q) D (Lp A Lq)) 
Q.E.D. 
K2 
(Lp A Lq) D L(p A q) 
PROOF 
PC4 
(1) p D (q D (p A q)) 
(1) X N 
(2) 
L(p D (q D (p A q))) 
K 
(3) 
L(pD q)D (Lp D Lq) 
(3)[q D (p A q)/q] 
(4) L(pD (q D(p A q))) D 
LpDL(qD 
(p 
A q))) 
(2), (4) X MP 
(5) LpDL(qD 
(p A q)) 
(3)[q/p,pAq/q] 
(6) L(q D (p A q)) D (Lq D L(p A q)) 
PC8 
(7) 
(pDq)D((qD(rD 
s)) D ((p A r) D s)) 
(7)[Lp/p, L(q D (p A q))lq, Lqlr, L(p A q)/s] 
(8) (Lp DL(qD(p 
A q))) D ((L(q D (p A q)) 
DLqDL(p 
A q))) D ((Lp A Lq) D L(p A q))) 
(5), (8) X MP 
(9) (L(q D (p A q)) D (Lq D L(p A q))) 
D ((Lp A Lq) D L(p A q)) 
(6), (9) X MP 
(10) (Lp A Lq) D L(p A q) 
Q.E.D. 
The proofs of these theorems satisfy exactly the requirements we listed 
27 


A NEW INTRODUCTION TO MODAL LOGIC 
for a proof in K. Setting out proofs at such length, however, can be not 
only tedious but sometimes actually a hindrance to understanding the 
principles which underlie them. We shall therefore introduce a number of 
conventions which will enable us to state proofs more briefly, while still 
providing all the information from which a full and rigorously formulated 
proof could be constructed. 
Note first that theorem K2 is the converse of Kl. Now we have 
defined equivalence as mutual implication, so we might expect to be able 
to use Kl and K2 to obtain L(p A q) ≡ (Lp A Lq) as a new theorem. 
And in fact PC5 will enable us to do this; for if we substitute L(p A q) 
for p and (Lp A Lq) for q in PC5, and then apply MP twice, using Kl 
the first time and K2 the second time, the result will be precisely Lip A 
q) ≡ (Lp A Lq). How shall we set all this out as a proof? If we are to 
adhere strictly to our criteria for a proof, we cannot use Kl (or K2) until 
we have written it down, and we are not allowed to write it down until 
we have derived it from axioms and earlier wff in the sequence which 
forms the proof; but this means that our proof of our new theorem will 
have to incorporate complete proofs of Kl and K2 before we begin to use 
these theorems in combination with PC5. Setting out the proof like this, 
however, involves a quite wasteful repetition of work that we have 
already done in proving Kl and K2 themselves. We shall therefore adopt 
the convention that after we have proved any theorem, we may write that 
theorem as a line in any subsequent proof, simply citing its reference 
number as its justification. The proof of our new theorem will then look 
like this: 
K3 L(p A q) ≡(Lp A Lq) 
PROOF 
Kl 
(1) L(p A q) D (Lp A Lq) 
K2 
(2) (Lp A Lq) D L(p A q) 
PC5 
(3) (p D q) D ((q D p) D (p ≡ q)) 
(3)[L(pAq)/p,LpALq/q] 
(4) 
(L(p A q) D (Lp A Lq)) D 
(((Lp A Lq) DL(p A q)) D (L(p A q) ≡(Lp A Lq))) 
(1), (4) X MP (5) ((Lp A Lq) D L(p A q)) D 
(L(p A q) ≡ (Lp A Lq)) 
(2), (5) X MP (6) L(p A q) ≡ (Lp A Lq) 
Q.E.D. 
K3 may be called the Law of L-distribution. 
28 


THE SYSTEMS K, T AND D 
Consider next how we used PC5 in the above proof. What we did was 
to make substitutions in it which produced, at line (4), an implicative wff 
whose antecedent was an already proved wff (Kl) and whose consequent 
had as its antecedent another already proved wff (K2). We then used MP 
twice to obtain the consequent of its consequent as a theorem. Now it 
should be clear that we can use PC5 in this way not only in the case of 
Kl and K2, but whenever we have already proved both a wff of the form 
α D β and its converse β D α; i.e. by substituting a for p and β for q 
in PC5 and applying MP twice, we can obtain α = β. We thus have a 
rule which could be expressed in this way: 
\-α D β, \-β D 
α 
\- α = β 
This rule is not part of the axiomatic basis of K. Nevertheless it is 
what we call a derived rule of K, in the sense that we may always use it 
as a transformation rule in a proof, since anything we can prove by using 
it we could also prove, though at greater length, from the axiomatic basis 
alone. To establish that a rule is a derived rule of a system we simply 
show how we could always do without it. In the present case we can do 
this as follows: 
Given: 
(1) 
α D β 
Given: 
(2) 
β D α 
PC5 
(3) 
(pD q)D ((qD p) D (p ≡ q)) 
(3)[α/p, β/q] 
(4) 
(αD β)D ((β D α)D (α ≡ β)) 
(1), (4) X MP 
(5) 
(β D α) D (α a β) 
(2), (5) X MP 
(6) 
α ≡ β 
Q.E.D. 
Since all we have used in establishing this rule (apart from US and MP) 
is PC5, we shall signal its use in justification entries simply by writing ' X 
PC5'. 
The procedure we have described for the use of PC5 will in fact enable 
us to derive a rule of K from any valid PC wff whose main operator is 
D. For if α is a valid PC wff, it is an axiom of K, and hence, by US, all 
its substitution-instances are theorems of K. So if we can make 
substitutions for the variables in α which will turn it into a wff whose 
antecedent is a wff we have already proved, we can use MP to detach its 
consequent and count that as a theorem too. (This is why MP is 
sometimes called Detachment.) In cases such as PC5 itself where the PC 
axiom has the overall form A D (B D C), if we can make substitutions 
29 


A NEW INTRODUCTION TO MODAL LOGIC 
which will turn both A and B into already proved wff, we can then use 
MP twice to obtain the result of these substitutions in C. A specially 
useful PC axiom of this kind is PC6, to which we gave the name Syll on 
p. 13. This gives us the rule 
\-αD β, [-β D 
γ 
[-α 
D γ 
which says that when we have proved two implicative wff in which the 
consequent of one is the antecedent of the other, we can count as a 
theorem the implicative wff whose antecedent is the antecedent of the 
former and whose consequent is the consequent of the latter. We shall 
indicate the application of this rule by 'X Syll', and give analogous 
indications, by name or number, of other rules similarly derived from PC 
axioms. In cases where the PC wff is not one we have listed we shall 
write simply X PC. 
Another way of shortening the statement of proofs is this. Line (3) in 
the proof of Kl is simply the axiom K itself, and line (4) is derived from 
this by US. The presence of K (without substitutions) is required by our 
definition of what counts as a proof; but it would be more economical, 
and still give all the information from which a detailed proof could be 
constructed, to omit line (3) altogether and give K with the appropriate 
substitutions as the justification for line (4). Similarly, we could omit line 
(10) and give PC3 with the appropriate substitutions as the justification 
for line (11). Somewhat analogously, we could omit line (1) and give 
'PCI × N' as the justification for immediately writing the present line 
(2). So we shall adopt the convention that citing any axioms or previously 
proved theorems by name or number and indicating the application of a 
transformation rule to them will be a sufficient justification entry for the 
wff obtained thereby. 
Finally, by using K together with N, US and MP, we can obtain a 
very useful derived rule. This is a specifically modal rule and we shall 
give it a special name as the first such rule we shall prove: 
DR1 
h α ^ 
β 
\-Lα 
D Lβ 
PROOF 
Given: 
(1) α D β 
(1) × N 
(2) L(α D β) 
K[α/p, 
β/q] 
(3) L(α D β) D (Lα D Lβ) 
(2), (3) × MP 
(4) Lα D 
Lβ 
Q.E.D. 
30 


THE SYSTEMS K, T AND D 
In the light of all this let us see how we can set out the proofs of 
K1-K3 in the abbreviated style which we shall use from now on: 
Kl 
L(p A q) D (Lp A Lq) 
PROOF 
PC1 X DR1 
(1) L(p A q) D Lp 
PC2 X DR1 
(2) L(p A q) D Lq 
(1), (2) X PC3 
(3) L(p A q) D (Lp A Lq) 
Q.E.D. 
K2 (Lp A Lq) D L(p A q) 
PROOF 
PC4 
×DR1 
(1) Lp D L(q D (p A q)) 
K[q/p,pAq/q] 
(2) L(q D (p A q)) D (Lq D L(p A q)) 
(1), (2) × PC8 
(3) (Lp A Lq) D L(p A q) 
Q.E.D. 
K3 L(p A q) = (Lp A Lq) 
PROOF 
Kl, K2 X PC5 (1) 
L(p A q) = (Lp A Lq) 
Q.E.D. 
We shall now prove some more theorems and derived rules of K. 
K4 (Lp V Lq) D L(p V q) 
PROOF 
PC9 X DR1 
(1) Lp D L(p V q) 
PC10 X DR1 
(2) Lq D L(p V q) 
(1), (2) X PC11 
(3) (Lp V Lq) D L(p V q) 
Q.E.D. 
Note that K4, unlike K3, is only an implication, not an equivalence. 
The converse of K4 is not a theorem of K, and in fact at the intuitive 
level is not a valid formula: it may be necessary that you are awake or 
asleep without its being necessary that you are awake or its being 
necessary that you are asleep. 
We next prove two further derived rules. The first of these is: 
DR2 
|- 
α 
≡β 
\-Lα 
= Lβ 
31 


A NEW INTRODUCTION TO MODAL LOGIC 
PROOF 
Given: 
(1) 
α ≡ β 
(1) × PC 
(2) 
α D β 
(2) × DR1 
(3) Lα D Lβ 
(1) × PC 
(4) 
β D α 
(4) × DR1 
(5) Lβ D Lα 
(3), (5) X PC5 
(6) 
Lα 
≡ 
Lβ 
Q.E.D. 
Note that in this proof we used purely PC principles to get from α ≡  
β at line (1) to both α D β and β D α at lines (3) and (5). Clearly we 
could do this with any theorem which has the form of an equivalence, and 
for this reason whenever we have proved a wff of the form α ≡ β we 
shall assume that we have proved both α D β and β D α; for example, 
if we have proved α ≡ β and α, we shall assume that (3 follows, and if 
we have proved α ≡ β and β , we shall assume that α follows, by MP in 
each case. 
Our next derived rule is that of Substitution of Equivalents, which we 
shall usually call Eq. What this states is that if α is a theorem and β 
differs from α only in having some wff, 6, at one or more places where 
α has a wff, 7, then if 7 ≡ 6 is a theorem, β is a theorem. In other 
words, if we have proved 7 ≡ 6, we can replace 7 by 6 in any theorem 
(not necessarily uniformly), and the result will also be a theorem. We 
now want to show that this rule holds in K. To do so we first note that 
the following are valid wff of PC, and therefore axioms of K: 
(P ≡ q) ^ (~P ≡ ~q) 
(p 
≡ q)D 
((p v r) ≡ (q V r)) 
(p ≡ q) D ((r V p) ≡ (r V q)) 
Suppose now that 7 = b is a theorem of K. Then by substitution in 
these three axioms, and MP, it follows that the following are also 
theorems of K, 
~γ≡δ 
(γ V ζ) ≡(δ v ζ) 
(ζ v γ) ≡ (ζ v δ) 
for any wff f. DR2, which we proved above, enables us to add to this list 
of consequences of 7 ≡ 6, Ly ≡ Lb. 
From this it follows that if a is any wff which is built up from 7 using 
32 
<x v D • (5 v j) 


THE SYSTEMS K, T AND D 
~ and L as the only monadic operators and V as the only dyadic one, 
and β is built up from 6 in exactly the same way as α is from 7, then if 
γ≡ δ is a theorem, so is α ≡ β; and therefore, if α is a theorem, then 
by MP so is β. Since every modal wff can be written with ~, L and V 
as its only operators, what we have just shown is that we can apply Eq 
unrestrictedly in K; i.e. whenever we have a theorem of K of the form 7 
≡ 6, we can replace γ by δ in any theorem a, no matter where 7 occurs 
in α, and the result will also be a theorem of K. 
Where an equivalential wff has a name, e.g. K3, and we are using Eq 
to replace an instance of one side of the equivalence by an instance of the 
other side in some wff, we shall indicate the application of Eq by (in this 
example) '× K3 × Eq', and analogously in other cases. A rich source of 
equivalential wff is of course provided by valid PC equivalences. 
L and M 
Our next theorem, which will help us to establish another extremely 
useful derived rule, is: 
K5 Lp ≡ ~M~p 
PROOF 
PC12 (DN) 
(1) p ≡ ~ ~p 
(l)[Lp/p] 
(2) Lp ≡ ~ ~Lp 
(2) × (1) × Eq: 
(3) Lp ≡ ~ ~L~ 
~p 
(3)Def M 
(4) Lp≡~M~p 
Q.E.D. 
Clearly K5, by Eq, will entitle us to replace L by ~M~ anywhere in 
a theorem; and by Def M we may replace M anywhere in a theorem by 
~ L ~ . (By saying that we are 'entitled' to do these things, or 'may' do 
them we simply mean that the result of doing them is itself a theorem.) 
The rule we are about to state is a kind of generalization of these 
procedures. We shall call it the Rule of L-M Interchange ('LMI' for 
short), and what it states is that in any sequence of adjacent monadic 
modal operators (Ls and Ms) in a theorem, L may be replaced by M and 
M by L throughout, provided that a ~ is either inserted or deleted both 
immediately before and immediately after the sequence. (Thus LM may 
be replaced by ~ ML ~, ~LLL by MMM~, MLLM~ by ~LMML, and 
so forth.) 
We shall now establish that this rule holds in K. Let A, ... An be a 
sequence of monadic modal operators (i.e. each A} is either L or M). For 
33 


A NEW INTRODUCTION TO MODAL LOGIC 
each Ai, let Ai' be M if Ai is L, and L if A; is M. We first show that 
(*) 
A 1... Anp ≡ ~ A 1 . . . An'~p 
is a theorem of K. To do so we begin with the following substitution-
instance of the PC valid wff p = p: 
(1) A 1...A np - 
A 1...A np 
Next, in the right-hand side of (1) we replace each M by ~L ~ (by 
Def M) and each L by ~M~ (by K5 and Eq). The result will be: 
(2) A x . . . A n p ≡ ~A 1'~ ~A 2'~ ... ~An-1'~ ~An'~ p 
We now use DN (p ≡~ ~p) and Eq to delete all occurrences of ~ ~ 
in (2), and the result is (*) as required. Appropriate substitutions for p in 
(*), and Eq, will then entitle us to replace any sequence A, ... A„by 
~A1' 
... An'— in any theorem. Finally, if the sequence before 
replacement was immediately preceded or followed by ~, the result of 
the replacement will give us~ ~at the beginning or the end of the new 
sequence, and this may be deleted by DN and Eq. We have thus shown 
that every application of LMI to a theorem of K results in a theorem of 
K - i.e. we have established LMI as a derived rule of K. 
Note that the sequence to which we apply LMI may have only a single 
member. Applications of K5 and Def M are thus themselves applications 
of LMI, and when convenient we shall indicate them too by ' × LMF. 
Note too that there is nothing to prevent us applying LMI only to part of 
a sequence; e.g. we may apply LMI to the first three operators in 
LMMLM, leaving the last two unaltered, and thus obtain ~ MLL~LM. 
K6 M(p V q) ≡ (Mp V Mq) 
PROOF 
K3 [~p/p,~q/q] 
(1) 
L(~p A -q) ≡ (L-p 
A L~q) 
(1) × LMI 
(2) 
~M~(~p 
A ~q) ≡ (~Mp A ~Mq) 
(2) × PC13 × Eq 
(3) 
~M(p V q) ≡ (~Mp A ~Mq) 
(3) × PC 
(4) 
M(p V q) ≡ (Mp V Mq) 
Q.E.D. 
K6 expresses the same kind of principle for possibility and disjunction 
as K3 does for necessity and conjunction; it may be called the Law of M-
34 


THE SYSTEMS K, T AND D 
distribution. 
K7 M(p D q) ≡ (Lp D Mq) 
PROOF 
K6[~p/p] 
(1) 
M(~p V q) ≡ (M~p V Mq) 
(1) × LMI 
(2) 
M(~p V q) ≡ (~Lp V Mq) 
(2) Def D 
(3) 
M(p D q) ≡ (Lp D Mq) 
Q.E.D. 
We now derive a rule which is like DRl except that M takes the place 
ofL. 
DR3 
\-α 
D β \-Mα D Mβ 
PROOF 
Given: 
(1) 
α D β 
(1) × PC15(Transp) (2) 
-β D 
-α 
(2) × DRl 
(3) 
L~β D L~α 
(3) × PC 
(4) 
~L~α D ~L~β 
(4)DefM 
(5) 
Mα D Mβ 
Q.E.D. 
Note that by repeated applications of DRl and/or DR3 we can prefix 
any sequence of modal operators to both sides of an implicative theorem. 
K8 M(p A q) D (Mp A Mq) 
We shall give two ways of proving K8. The first uses DR3 in the way 
that the proof of K4 used DRl, and the second obtains K8 from K4 in the 
same manner as K6 was obtained from K3. Here is the first: 
PROOF 
PCI × DR3 
(1) 
M(p A q) D Mp 
PC2 × DR3 
(2) 
M(p A q) D Mq 
(1), (2) × PC3 (3) 
M(p A q) D (Mp A Mq) 
Q.E.D. 
Here is the second proof: 
PROOF 
K4[~p/p,~q/q] 
(1) 
(L~p V L~q) D Lip V q) 
(1) × PC15 × Eq 
(2) 
~L(~p 
V ~q) D ~(L~p 
V L~q) 
35 


A NEW INTRODUCTION TO MODAL LOGIC 
(2) X LMI 
(3) 
M~(~p 
V ~q) D ~(~Mp 
V ~Mq) 
(3) X PC14 X Eq 
(4) 
M(p A q) D (Mp A Mq) 
Q.E.D. 
As was the case with K4, but in contrast with K6, the converse of K8 
is not a theorem of K. We do however have the following partial 
converse to K4: 
K9 L(p V q) D (Lp V Mq) 
PROOF 
K[~qlp, 
P/q] 
(1) L(~q ?P)^ 
(L~q D Lp) 
(1) Def D, X DN(PC12) 
(2) L(q V p) D (~L~q 
V Lp) 
(2)Def M, X Comm(PC16) (3) L(p V q) D (Lp V Mq) 
Q.E.D. 
Validity and soundness 
As we remarked earlier in this chapter, the theorems of the system K will 
turn out to be precisely those wff which are K-valid in the sense explained 
on p. 20. It is important to be quite clear that this is a substantive fact, 
and not something which is true by definition, as our use of the label 'K-
valid' might at first suggest. To be a theorem of K is to be derivable from 
the axioms of K by the transformation rules of K; to be K-valid is to be 
successful in every setting of the modal game. We have here two distinct 
concepts, and the fact that a wff is a theorem of K iff it is K-valid is 
something we have to prove, not something we can assume. We shall in 
fact come across many cases in which we have an axiomatic modal 
system defined without any reference to an account of validity, and a 
definition of validity formulated without any reference to theoremhood in 
a system, and yet the theorems of that system are precisely the wff which 
are valid by that definition; but this is something which has to be proved 
in every case, and it should be obvious that giving the system and the 
validity-definition the same name (as we shall often do) does nothing to 
prove it but serves to remind us of the connection once it has been 
proved. To show that there is a match of this kind between a system and 
a validity definition we have to prove two things: (A) that every theorem 
of the system is valid by that definition, and (B) that every wff valid by 
that definition is a theorem of the system. If (A) holds, we say that the 
system is sound, and if (B) holds we say that it is complete, in each case 
with respect to the validity-definition in question. The completeness of a 
system is usually more difficult to establish than its soundness, and we 
shall defer the task of proving the completeness of K till Chapter 6. Here, 
36 


THE SYSTEMS K, T AND D 
however, we shall give a proof of its soundness with respect to In-
validity. 
In a sense we have done this already; for on p. 20 we gave a proof that 
all valid wff of PC and the wff K (i.e. all the axioms of K) are K-valid, 
and earlier in the present chapter we at least sketched an argument to 
show that the transformation rules of K preserve K-validity. We shall 
now, however, give a more rigorous definition of validity for modal 
formulae and in terms of it a more formally exact proof of the soundness 
of K. 
Our account of the modal game on p. 18, though it was intended to 
make the idea of validity more immediately comprehensible, had both 
certain inessential features and also certain limitations, which we now 
want to remove. It ought not to be difficult to see that speaking of players 
at all, of some players being able or unable to see other players, and of 
the raising or non-raising of hands, is quite inessential to the logical 
structure of the test that is being applied to formulae. Instead of a set of 
human players we could have a collection of objects of any kind at all; 
but to reflect the idea, mentioned on p. 21, that the players represent 
alternative ways the world might be, these objects are sometimes called 
'possible worlds', or simply 'worlds', and this is the terminology that we 
shall usually employ in this book. Similarly, it does not matter what takes 
the place of the seeing-relation among the players, so long as it is some 
kind of dyadic relation, R, defined over the objects in question, in the 
sense that it is specified for every pair of these objects, w and w', 
whether or not wRw'. Sometimes R is called the accessibility-relation, 
and when wRw', w' is said to be accessible from w, or to be possible 
relative to w. (In this book we shall sometimes use this terminology, but 
we shall also, when convenient, carry over a metaphor derived from the 
modal game and speak of one world being able to see another. The point 
to be clear about is that, whatever terminology we use, from a formal 
point of view R is no more than a relation which may or may not hold 
between any pair of worlds.) 
In describing the modal game we called a set of players and a 
specification of which players could see which a seating arrangement. In 
our present more abstract account we call the pair (W,R), where W is a 
set of worlds and R is a specification of which of these is related to 
which, a frame.3 We note here one limitation involved in our description 
of the modal game, which we can now remove. In any 'real life' attempt 
to play the modal game, the number of players involved would have to be 
finite, and in fact in practice fairly small; but we need place no limits to 
37 


A NEW INTRODUCTION TO MODAL LOGIC 
the number of worlds in a frame - there may be only one, there may be 
17, there may be infinitely many. 
Within each seating arrangement in the modal game we could have any 
number of settings by giving each player a list of variables. As we also 
remarked on p. 21, this corresponds to the idea that those variables are 
true, or are assigned the value 1, in the state of affairs represented by the 
player in question, with the other variable being false, or assigned the 
value 0. Again, there is a limitation here if we take the game literally, 
since in practice any list of variables would have to be finite; but we do 
not wish to have any such restriction in the formal definition of validity 
which we are now constructing. We shall refer to an assignment of values 
within a frame as V, and where p is any propositional variable and w is 
any world in the frame (i.e. w G W),4 we shall write V(p,w) = 1 if V 
assigns the value 1 to p in w, and V(p,w) = 0 if it assigns the value 0 to 
it. Where (W,R) is a frame and V is a value-assignment within that 
frame, we call (W,R, V) a model, and more specifically a model based on 
the frame (W,R). Thus a model corresponds to a setting in the modal 
game. 
We can set out all this as follows: 
A frame is an ordered pair (W,R), where W is a non-empty set of 
objects (worlds), and R is a dyadic relation defined over the members of 
W, i.e. it is determinate for any (not necessarily distinct) w and w' in W 
whether or not wRw'. 
A model is an ordered triple (W,R,V) where (W,R) is a frame and V 
is a value-assignment satisfying the following conditions: 
1. For any propositional variable, p, and any w G W, either V(p,w) 
= 1 or V(p,w) = 0. 
2. [V~] For any wff, α, and any w G W, V(~α,w) = 1 if V(α,w) 
= 0; otherwise V(~α,w) = 0. 
3. [V V ] For any wff a and β, and for any w G W, V((α V β),w) = 
1 if either V(α,w) = 1 or V(β,w) = 1; otherwise V((α V β),w) = 0. 
4. [VL] For any wff α and for any w G W, V(Lα,w) = 1 if for every 
w' G W such that wRw', V(α,w' ) = 1; otherwise V(Lα,w) = 0. 
Although the conditions for the other operators we have introduced are 
strictly unnecessary, since all wff can be written in primitive notation, we 
give them here for ease of reference: 
[V A ] For any wff α and β, and for any w G W, V((α A β),w) = 1 
if both V(α,w) = 1 and V(β,w) = 1; otherwise V((α A (3),w) = 0. 
[VD] For any wff α and β, and for any w G W, V((α D β),w) = 1 
if either V(α,w) = 0 or V(β,w) = 1; otherwise V((α D 0),w) = 0. 
38 


THE SYSTEMS K, T AND D 
[V = ] For any wff α and β, and for any w G W, V((α = β),w) = 1 
if V(α,w) = V(β,w); otherwise V((α as β),w) = 0. 
[VM] For any wff α and for any w G W, V(Mα,w) = 1 if for some 
w' G W such that wRw' , V(α,w' ) = 1; otherwise V(Ma,w) = 0. 
A model (W,R,V) is said to be based on the frame (W,R). 
We now define validity on a frame by saying that a wff a is valid on 
a frame (W,R) iff, for every model (W,R,V) based on (W,R), and for 
every w G W, V(α,w) = 1. Finally we define K-validity by saying that 
a wff is K-valid iff it is valid on every frame. 
We are now in a position to prove the soundness of K with respect to 
K-validity as we have just defined this. Our method of doing so will in 
fact yield a more general result which we shall be able to use to prove the 
soundness of many other systems. 
THEOREM 2.1 
Every theorem of K is K-valid.5 
What we have to prove is that every wff derivable from the axioms of K 
by the transformation rules of K is valid on every frame. For this it is 
clearly sufficient to prove (1) that every axiom of K is valid on every 
frame, and (2) that the rules US, MP and N preserve validity on a frame 
- i.e. that if they are applied to wff which are valid on any given frame, 
the resulting wff are also valid on that frame. In stating the more general 
consequence which we mentioned above we shall use the following 
terminology: where A is any set of modal wff (which may have only one 
member or more than one - even infinitely many members), we let 'K + 
A' denote the axiomatic system obtained by adding to K, as extra axioms, 
all the wff in A (and retaining the transformation rules US, MP and N).6 
Our more general result is this: 
THEOREM 2.2 
If A is any set of modal wff and (W,R) is a frame on 
which each wff in A is valid, then every theorem of K + 
A is valid on (W,R>. 
As we have noted, the soundness of K with respect to K-validity 
(theorem 2.1) follows immediately from theorem 2.2. Theorem 2.2 
follows from the following two lemmas: 
LEMMA 2.3 If (W,R) is any frame, every valid PC wff is valid on 
(W,R), and so is the wff K. 
39 


A NEW INTRODUCTION TO MODAL LOGIC 
LEMMA 2.4 Where (W,R) is any frame, 
(i) if α is valid on (W,R), so is α[βxlp1, ... ,βn/pn] (i.e.α with β1 
... , βn uniformly replacing pl, ... ,pn respectively); 
(ii) if α and α D β are both valid on (W,R), so is β; 
(iii) if α is valid on (W,R), so is Lα. 
We shall prove the lemmas in a moment, but before doing so we shall 
note that theorem 2.2 is an immediate consequence of lemmas 2.3 and 
2.4, since by lemma 2.3 every axiom of K is valid on every frame, and 
by lemma 2.4 the transformation rules preserve validity on any frame 
whatsoever. The importance of theorem 2.2 can be indicated in this way. 
Apart from a few systems which we shall mention in Chapters 11 and 12, 
and which stand a little outside mainstream modal logic, K is the weakest 
of the modal systems we shall be discussing. Each of the other systems 
will be a proper extension of K (i.e. it will contain not only all the 
theorems of K but other theorems as well). Modal systems which contain 
K (including K itself) together with US, MP and N are commonly known 
as normal modal systems, and we shall usually present these other 
systems by adding one or more extra axioms to the basis of K. For each 
such system we shall also have (or at least we shall try to find) a 
definition of validity which matches it in the way that K-validity matches 
the system K; i.e., which is such that the theorems of the system are 
precisely the wff which are valid by that definition. Typically we shall 
produce such a definition by specifying a certain class ^of frames, and 
saying that a wff is valid with respect to ^(^-valid) iff it is valid on 
every frame in & And when a system S is both sound and complete with 
respect to a class ^of frames, so that the theorems of S consist of all and 
only those wff that are valid on every frame in ^ we say that S is 
characterized by &. To come at last to the importance of theorem 2.2: 
what it tells us is that if we have a system K + A and a class of frames 
#, then in order to prove that K + A is sound with respect to #, all we 
have to do is to show that every wff in A is valid on every frame in &. 
We note here some of the terminology we shall use in discussing 
frames and models. If every theorem of a system S is valid on a frame 
(W,R), we say that (W,R) is α. frame for S. If a wff α is not valid on a 
given frame we sometimes say that it fails on that frame, or that it can be 
falsified on that frame. A model in which α is false in at least one world 
is called α. falsifying model for α. 
So now what remains is to prove lemmas 2.3 and 2.4. 
40 


THE SYSTEMS K, T AND D 
Proof of lemma 2.3: (A) In any model, a PC wff is evaluated in any 
world without reference to any other world. Therefore, since a valid PC 
wff has the value 1 for every value-assignment to the variables, it has the 
value 1 in every world in every model, i.e. it is valid on every frame. (B) 
If K were not valid on every frame, there would have to be a model 
(W,R,V) in which for some w G W, (i) V(L(p D q),w) = 1, (ii) 
V(Lp,w) = 1, and (iii) V(Lq,w) = 0. There cannot, however, be any 
such model. For by (iii), there must be some w' € W such that wRw' 
and V(q,w') = 0; by (ii), since wRw', V(p,w') = 1; hence, by [VD], 
V((p D q),w' ) = 0; but then by [VL], since wRw', we have V(L(p D 
q)yw) = 0, which contradicts (i). 
Proof of lemma 2.4: 
(i) Suppose that (W,R) is a frame and α[$xlpu ... ,/3n//?J is not valid 
on (W,R). Then there is a model (W,R,V> based on (W,R) such that for 
some w* € W, V(α[β1/p1, ... ,βn/p],w*) = 0. Let (W,R,V*) be a model 
based on the same frame (W,R), in which V* is just like V except that 
for any w E W, and any 1 ≤ i ≤ n, V*(pi,w) = V(βi,vv). Then 
V*(α,w*) = 0, and so α is not valid on (W,R). (What this amounts to is 
simply that whatever model falsifies α[β1lp,, ... ,βn/pn], if we had given 
the variables that have been replaced the same values as the wff that have 
replaced them, then we could have falsified the original a, showing that 
it wasn't valid in the first place.) 
(ii) If both α and a D β are valid on (W,R), then in every world in 
every model based on (W,R), both α and α D β are true; hence by [VD] 
so is β; i.e., β is valid on (W,R). 
(iii) If α is valid on (W,R), then in every world in every model based 
on (W,R), α is true; hence for every such world, α is true in every world 
which it can see; so La is true in every such world - i.e., Lα is valid on 
(W,R). 
The system T 
On p. 20 we showed that the wff Lp D p is not K-valid. In the light of 
theorem 2.1, this means that it is not a theorem of K. We could, 
however, add it as an extra axiom to obtain a system stronger than K 
itself. Now what the formula means is that whatever is necessarily so is 
so, and we remarked on p. 14 that although there are some senses of 
'necessarily' for which this does not hold, there are others for which it 
does; we therefore have a motive for constructing a system or systems 
which will reflect these latter senses. The system obtained by adding Lp 
41 


A NEW INTRODUCTION TO MODAL LOGIC 
D p as a single extra axiom to K has had a long history in modal logic 
dating from 1937, and is usually referred to simply as T.7 We shall 
therefore give the name T to the formula itself. In other words, the 
system T is K + 
T 
Lp D p 
This axiom is sometimes called the Axiom of Necessity. 
All the theorems of K are of course still theorems of T. The derived 
rules DR1-DR3 and Eq also hold in T. In fact if we look back at how 
these rules were proved in K, we can see that they are bound to hold in 
all systems which contain K, provided that they retain the rules US, MP 
and N. We prove a couple of theorems of T which are not in K. 
Tl 
p D Mp 
PROOF 
T[~p/p] 
(1) 
L~PD 
~p 
(1) X PC 
(2) p D 
~L~p 
(2)DefM 
(3) p D Mp 
Q.E.D. 
T2 
M(p D Lp) 
PROOF 
Tl[Lp/p] 
(1) 
Lp D MLp 
Kl[Lp/q] 
(2) 
M(p D Lp) = (Lp D MLp) 
(1), (2) X Eq 
(3) 
M(p D Lp) 
Q.E.D. 
We leave it to the reader to show that neither Tl nor T2 is a theorem 
of K, by defining for each of them a model in which it is false in some 
world. 
The fact that T2 is a theorem of T shows that the following rule, which 
is a kind of possibility counterpart of N, is not a rule of T: 
P 
\-Mα 
[-α 
The reason is that if P were a rule of T, then from it and T2 we could 
derive p D Lp, but as we shall show in a moment, this is not a theorem 
of T. 
42 


THE SYSTEMS K, T AND D 
A definition of validity for T 
In discussing the modal game on p. 20 we showed that the wff Lp D p 
is valid in every seating arrangement in which all players can see 
themselves. Transposed into our present frame-theory, this means that T 
is valid on every frame (W,R) in which R is reflexive - i.e. in which, for 
every w E W, wRw. (We call such frames, for short, reflexive frames.) 
So by theorem 2.2, the system T is sound with respect to the class of all 
reflexive frames. We shall in fact be able to prove later that T is also 
complete with respect to this class of frames; so, anticipating this result, 
we shall say that a wff is T-valid iff it is valid on every reflexive frame, 
and we shall sometimes call a reflexive frame a T-frame. 
We said a couple of paragraphs back that we would prove that p D Lp 
is not a theorem of T. Now that we have shown that every theorem of T 
is valid on every reflexive frame, all that we need for this purpose is to 
find a reflexive frame in which p D Lp is not valid. And this is not 
difficult: imagine a world in which p is true and which can see a world 
in which p is false, each world being able to see itself. 
Since T is not K-valid, it is not a theorem of K, and this shows that K 
and T are distinct systems, with T being a proper extension of K. 
The system D 
We said on p. 20 that if we interpret L as expressing obligatoriness 
('moral necessity') we shall be unlikely to want to regard Lp D p as 
valid, since what it will then mean is that whatever ought to be the case 
is in fact the case. There is, however, a formula which, like Lp D p, is 
not a theorem of K but which with this interpretation it is plausible to 
regard as valid, and that is the wff Lp D Mp. For if Lp means that it is 
obligatory that p, then Mp will mean that it is permissible that p (not 
obligatory that not-p), and so Lp D Mp will mean that whatever is 
obligatory is at least permissible, which sounds reasonable enough. This 
interpretation of L is known as a deontic interpretation, and for that 
reason Lp D Mp is often called D, and the system obtained by adding it 
to K as an extra axiom is known as the system D;8 i.e. D is defined as K 
+ 
D 
Lp D Mp 
An easily derived theorem of D is 
Dl 
M(p D p) 
43 


A NEW INTRODUCTION TO MODAL LOGIC 
PROOF 
PC 
(1) p D p 
(1) × N 
(2) L(p > P) 
D[p D p/p] 
(3) 
L(p D p)D 
(2), (3)× MP (4) 
M(p Dp) 
M(p D p) 
Q.E.D. 
In fact Dl would provide an alternative axiom for D, since if we add 
it alone to K we can derive D in the following way: 
K7[p/q] 
(1) 
M(pD p) m (Lp D Mp) 
Dl, (1) X Eq 
(2) Lp D Mp 
Q.E.D. 
It is worth noting that if any wff α is a theorem of D, then so is Mα. 
For if α is a theorem, N gives Lα as a theorem; and then by D[α/p] and 
MP we obtain Mα. 
It is also worth noting that if any system which is an extension of K 
has any theorems of the form Ma, that system contains D. To prove this 
it is clearly sufficient to derive D1 in such a system, and we can do this 
as follows: 
Given: 
(I) Mα 
PC 
(2)qD 
(pD p) 
(2)[α/q] 
(3) α D (p D p) 
(3) X DR3 
(4) Mα D M(p D 
(1), (4) X MP (5) M(p D p) 
p) 
Q.E.D. 
In introducing the system D we mentioned that its axiom D is not a 
theorem of K. We shall prove this in a moment, and we shall also prove 
that T is not a theorem of D. D, however is a theorem of T, since it 
follows straightforwardly from T and Tl by Syll. What this means is that 
the system D is intermediate between K and T, in the sense that T is a 
proper extension of D, which in its turn is a proper extension of K. 
To find a definition of validity which will match the system D, and 
also to clarify the difference between D and K, we shall draw attention 
to a feature of some frames on which we have not so far laid stress. We 
have observed that not all worlds in a frame need see themselves; but in 
fact there is nothing in our definition of 'frame' to prevent there being 
some worlds in a frame which cannot see any world in that frame at all. 
Krister Segerberg has called such worlds dead ends,9 and we shall adopt 
this terminology in this book. Now the rule [VL] says that La is true in 
44 


THE SYSTEMS K, T AND D 
a world w iff α is true in every world that w can see, and we interpret 
this to mean that if there is no world at all that w can see, then Lα is 
(trivially) true in w, no matter what wff a may be (even if it is p A ~p). 
(It may be easier to see why we count La always true in a dead end by 
seeing why its negation —Lα is always false in such a world: for —Lα 
is equivalent to M~ α, and by [VM] any wff of the form Mβ can be true 
in w only if there is some world that w can see.) It should now be clear 
that if a frame contains any dead end w, then D is not valid on that 
frame, since in w Lp is true and Mp false, no matter what value is 
assigned to p there. Since there are such frames, D is not K-valid, and is 
therefore not a theorem of K. A more general consequence is that K has 
no theorems at all of the form Mα; for every wff of this form would be 
invalid on a frame containing any dead end. 
Suppose we now consider the class of frames which contain no dead 
ends, i.e. frames in which each world can see at least one world (itself 
and/or some other or others). In such frames R is said to be a serial 
relation, and we shall call them serial frames for short. In other words, 
(W,R) is a serial frame iff for every w E W, there is some w' E W 
such that wRw'. Now D must be valid on every serial frame: for if it 
were not, there would have to be a world w in a model based on a serial 
frame where (i) Lp is true and (ii) Mp is false; but since the frame is 
serial w must be related to some world w', and then by (i) and [VL] p 
must be true in w' and by (ii) and [VM] p must be false there, which is 
impossible. Since D is valid on every serial frame, theorem 2.2 assures 
us that every theorem of D is valid on every such frame, i.e. that D is 
sound with respect to the class of all serial frames. We shall be able to 
prove in Chapter 6 that D is also complete with respect to that class of 
frames; so, anticipating that result, we now define D-validity by saying 
that a wff is D-valid iff it is valid on every serial frame. 
It is now easy to show that T is not a theorem of D, and therefore that 
the system T is a proper extension of D. All we need to do is to exhibit 
a serial frame on which T is not valid, and an example of such a frame 
is one consisting of two worlds, w and w', where w cannot see itself but 
can see w', and w' can see itself. T is not valid on this frame, for if p is 
false at w but true at w', then T is false at w. 
A note on derived rules 
Earlier in this chapter we introduced the notation K + A to denote the 
result of adding all the wff in A to the basis of K. More generally, where 
S is any axiomatic modal system containing the transformation rules US, 
45 


A NEW INTRODUCTION TO MODAL LOGIC 
MP and N and A is any set of wff, we shall let S 4- A denote the system 
obtained by adding all the wff in A to the basis of S, while retaining the 
rules US, MP and N. It is a trivial fact that all theorems of S remain 
theorems of S + A, for the addition of new axioms cannot result in the 
loss of any theorems. With derived rules, however, the position is more 
complicated. We noted earlier on that the rules DR1-DR3 and Eq which 
we derived in K still hold in all extensions of K. But consider the rule we 
discussed above and showed not to be a rule of T: 
P 
[-Mα 
\-α 
Now K, as we observed, has no theorems at all of the form Ma; so P 
is (trivially) a rule of K. Less trivially, it is also a rule of D. So P is an 
example of a rule which holds in some systems but not in all their 
extensions, and this illustrates the care that must be taken with derived 
rules. If we look back at the way DR1-DR3 and Eq were proved to hold 
in K, we can easily see why they hold in all extensions of K: for they 
were derived by appealing only to elements in K (theorems and primitive 
transformation rules) which are still present in all its extensions. But P is 
a rule of K and D because of features of those systems which are not 
present in all their extensions - in the case of K because the system is too 
weak to have any theorem satisfying the antecedent of the rule. 
So if we are given merely that some rule is a rule of S and that S' is 
an extension of S, this does not by itself guarantee that it is also a rule of 
S'. This is just one of the pitfalls one may encounter in studying 
axiomatic systems and which should put us on our guard against jumping 
to conclusions too easily. 
Consistency 
We shall say that an axiomatic system is consistent iff not every wff is a 
theorem of that system. In other words, a system is inconsistent iff every 
wff is a theorem. Other definitions of consistency are sometimes given, 
but provided that the system contains the schema PC (or some other way 
of ensuring that every valid wff of PC is a theorem) and the rules US and 
MP, all the standard definitions of consistency are equivalent. One such 
definition is that a system is consistent iff no variable is a theorem. This 
is equivalent to our definition because (a) if a variable were a theorem, 
then by US every wff would be one, and (b) if every wff were a theorem, 
then since p is a wff it would be a theorem. Another definition is that a 
system is consistent iff no wff and its negation are both theorems. And 
46 


THE SYSTEMS K, T AND D 
this is also equivalent to the definition we have given because (a) if α and 
~α were both theorems, then by substituting α for p and any wff β for 
q in the PC-valid wff p D (—p D q) we could obtain any wff 
whatsoever as a theorem, and (b) if every wff were a theorem, obviously 
a wff and its negation would both be theorems. 
Now clearly the wff p (or any other variable) is not valid on any 
frame; so if a system is sound with respect to any (non-empty) class of 
frames whatsoever, p is not a theorem of that system, and so the system 
is consistent. Thus a proof of the soundness of a system is automatically 
a proof of its consistency. 
In Chapter 1 we introduced the notion of an unsatisfiable PC wff- i.e. 
one which has the value 0 for every value-assignment to its variables. It 
should be obvious that the addition of any unsatisfiable PC wff to any 
system which contains all valid PC wff and has the rules US and MP 
would make the system inconsistent; for if α is unsatisfiable, ~α is valid, 
and therefore a theorem of the system already, so we should have a wff 
and its own negation as theorems. But it is also worth noting that if any 
invalid PC wff at all were a theorem of such a system, the system would 
be inconsistent. To prove this it will be sufficient, in the light of what we 
have just said, to show that every invalid PC wff has a substitution-
instance which is unsatisfiable, and we can do this as follows: 
Let α be any invalid PC wff. The fact that α is invalid means that 
there is some assignment of truth-values to the variables occurring in it 
which will give the value 0 to α as a whole. Now let α' be α with p V 
~p replacing each variable to which that assignment gives the value 1 
and p A ~p replacing each variable to which it gives the value 0. Then 
since these two wff have the values 1 and 0 respectively for every value-
assignment, α' will have the value 0 for every value-assignment - i.e. 
will be unsatisfiable. But clearly α' is a substitution-instance of α. 
Constant wff 
In forming α' out of α in the previous paragraph we replaced every 
variable by a formula whose truth-value could be guaranteed to be 1 or 
0 as the case might be, irrespective of any value-assignment made to the 
variables. A wff of this kind we shall call a constant wff. Since the truth-
value of p A ~p does not depend on the truth-value of p (p A ~ p is 
always false) we may write it as 1 and interpret it as a 'constant false 
proposition'; and we then define a constant wff by saying that 1 is a 
constant wff, that if α is a constant wff, so are ~ α and La, and that if 
α and (3 are constant wff, so is α V /?. Finally, for convenience, we 
47 


A NEW INTRODUCTION TO MODAL LOGIC 
define the symbol T as ~ 1 , and hence interpret it as a constant true 
proposition, to be always assigned the value 1. 
A constant wff may or may not contain modal operators. A constant 
PC wff (i.e. one which contains no modal operators but is built up from 
T and/or 1 by truth-functional ones only) must have the same truth-
value for every value-assignment, and as a result every such wff will be 
either valid or unsatisfiable. In the case of a constant wff which contains 
modal operators, its truth-value in any world in a model will not depend 
on the value-assignment given to variables in that model, but only on how 
that world is related to other worlds (or to itself) in that model. We shall 
find further use for constant wff in later chapters. 
Exercises - 2 
2.1 
Prove in K: 
(a) 
(L(p D q) A L(q D r)) D L(p D r) 
(b) 
L(p D q) D (Mp D Mq) 
(c) (L(p D q) A M(p A r)) D M(q A r) 
(d) 
M(p D (qAr)) D ((Lp D Mq) A (Lp D Mr)) 
(e) 
M(p D p) D (Lq D Mq) 
(f) (Lp A M(q D r)) D (L(p D q) D M(p A r)) 
(g) 
(Lp A Mq) D M(p A q) 
2.2 
(a) 
Let the axiomatic basis of K* be the same as for K except that 
N is replaced by the axiom L T : L(p D p), and the rule 
R* 
\- α D 
β 
\- Lα D Lβ (R* is DR1 but taken as a primitive 
transformation rule). Show that K and K* have the same theorems. 
(b) 
Let K** be K but with N and K replaced by L T , R* and 
K2* (Lp A Lq) D Lip A q) (K2* is K2 but taken as an axiom). 
Show that K and K** have the same theorems. 
2.3 Let T* be the same as T except that in place of K, T* contains 
K* L(L(p D q)D (Lp D Lq)) 
and in place of N, T* contains R*. Show that T and T* have the same 
theorems. 
2.4 Prove that K has no theorems of the form LMα. 
2.5 Where T is exactly like T except that in place of T it has 
T' 
p D Mp, 
prove that T and T have the same theorems. 
48 


THE SYSTEMS K, T AND D 
2.6 
(a) 
Prove that the following is a rule of K: 
|- α V 
β 
[• Mα V Lβ 
(b) 
Prove that the following is a rule of D but not of K: 
|- α V 
β 
\- Mα V Mβ 
(c) 
Prove that the following is a rule of T but not D: 
|- α V 
β 
f- 
Mα 
Vβ 
2.7 
Prove in D 
(a) 
M~p 
V M ~ # V M(p V q) 
(b) 
~L(Lp 
A 
L~p) 
2.8 
Show that T2 is not a theorem of D. 
2.9 
Show that if Mα is D-valid then so is α. 
2.10 
Prove that 
\-Lα 
|- α is α rule of K and D. [Hint (Chellas 
1980, p. 124): For any wff a let o{α) be obtained from α by deleting 
every modal operator (L or M) which is not in the scope of another modal 
operator, and show that any proof of α in K (D) can be converted into a 
proof of α(α) in the same system.] 
2.11 
Let L be the rule 
\-Lα D 
Lβ 
f- α D β 
Show that L 
preserves validity in K and D but not in T. 
Notes 
1 This name, which has now become standard, was given to the system in 
Lemmon and Scott 1977, p. 29, in honour of Saul Kripke, from whose work the 
way of defining validity for modal logic which we have begun to describe and 
will elaborate later is mainly derived. We give the same name to the system and 
to the formula which is its characteristic axiom, and shall do so for some other 
systems also. In such cases we shall use bold-face type when referring to the 
formula, but roman type when referring to the system. 
2 An axiom is a specific wff; an axiom schema is a statement to the effect that 
any wff satisfying certain conditions is an axiom. The fact that the axiom schema 
PC gives us infinitely many axioms does not conflict with our requirements for 
a satisfactory set of axioms, since we have (in the truth-table method, for 
example), an effective way of determining whether any given wff is a valid wff 
of PC or not. Although PC appeals to a notion of validity it is only PC-validity 
and makes no reference to the modal operators. It is of course possible to study 
PC itself as an axiomatic system with a finite number of axioms. See p. 210 
49 


A NEW INTRODUCTION TO MODAL LOGIC 
below. 
3 The word 'frame' in this sense seems to have been first used in print in 
Segerberg 1968b, but Segerberg has informed us that the word was suggested to 
him by Dana Scott. Lemmon and Scott 1977 called frames 'world systems'. 
Kripke 1963a used the term 'model structure' in a related but not quite identical 
sense. At this point it might be worth stressing again that the nature of the 
'worlds' does not affect the logic. In fact if we take any frame and make an 
isomorphic 'duplicate', in which the duplicate worlds are related exactly as the 
originals are, we clearly validate exactly the same formulae. 
4 The symbol G simply means 'is a member of. This is a convenient use of set-
theoretical notation which we shall employ in this book. Another piece of notation 
we have been using is the angle brackets ( and ) as in (W,R) to indicate the 
ordered pair of W and R - W and R in that order - or an ordered triple as in 
(W,R,V) and so on. (This contrasts with the use of curly brackets as in {α,b} to 
denote the unordered class whose members are precisely α and b without 
commitment to any order. Thus {α,b} is the same class as {b,α}, {α,α} is the 
same class as {α}, and so on.) We shall explain other set-theoretical terminology 
as we proceed. 
5 In calling theorem 2.1 a theorem we must be careful not to confuse it with a 
theorem of K. The theorems of K are the wff which can be derived from the 
axioms of K by the transformation rules. Theorem 2.1 states a fact about K and 
we prove it by ordinary reasoning. Some authors would call it a metatheorem but 
no confusion ought to arise over the difference in status between theorems like 
K1-K9 say, and theorems like theorem 2.1. 
6 Where A is finite K 4- A is said to be, finitely axiomatizable. A system which 
is not finitely axiomatizable is discussed on p. 185. To call K + A axiomatizable 
it is often required that A be effectively specifiable. 
7 Feys 1937 (vide esp. pp. 533-535). Feys' own name for the system is 't' (it was 
first called T ' by Sobocifiski 1953). Feys derived the system by dropping one of 
the axioms in a system devised by Godel 1933 (p. 39), with whom the idea of 
axiomatizing modal logic by adding to PC originates. Sobociriski (op. cit.) showed 
that T is equivalent to the system M of von Wright 1951; for this reason 'M' is 
often used as an alternative name for T. In this book we shall usually refer to 
systems by names which have become standard, but it might be worth referring, 
at this point, to an alternative naming system found in Chellas 1980 in the spirit 
of Lemmon and Scott 1977. This consists in simply listing the axioms in 
sequence. So T would strictly speaking be KT. 
8 This name is found on p. 50 of Lemmon and Scott 1977. 
9 Segerberg 1971, p. 93. 
50 


3 
THE SYSTEMS S4, S5, 
B, TRIV AND VER 
In the previous chapter T was the strongest of the systems we discussed. 
We saw that there are senses of 'necessary' and 'possible' for which some 
of its theorems seem unacceptable. Nevertheless it seems plausible to hold 
that there is also a perfectly good and standard sense of these terms in 
which all the theorems of T are non-controversial and formulae which are 
not among its theorems - for instance Lp D LLp - are at least perplexing. 
Iterated modalities 
One feature of Lp D LLp and of many other formulae which makes them 
hard to pronounce on from an intuitive point of view is that they contain 
consecutive sequences of modal operators; Lp D LLp, for example, 
contains the sequence LL. Such sequences are known as iterated 
modalities. Now not all formulae containing iterated modalities raise 
difficulties. If we accept the validity of Lp Dp (T), for instance, we are 
not likely to have any qualms about LLp D Lp or LMp D Mp, since they 
are simply substitution-instances of it. But when we ask, informally, 
whether Lp D LLp is valid, the issue we are raising is this: is whatever 
is necessary necessarily necessary? when something is necessarily so, is 
the fact that it is necessarily so always itself something that is necessarily 
so? Now this is both a disputed question and one of some obscurity, for 
it is not at all clear under what conditions we should say that something 
is necessarily necessary. It is, however, at least a reputable and plausible 
view that in certain well-established senses of 'necessary' it should be 
answered in the affirmative; it is, for example, plausible to maintain that 
51 


A NEW INTRODUCTION TO MODAL LOGIC 
whenever a proposition is logically necessary, this is never a matter of 
accident but is always something which is logically bound to be the case. 
We do not, however, need to try to settle the issue definitely here; for 
what we have just said about Lp D LLp is enough to give us a motive for 
constructing a system stronger than T, in which that formula would be a 
theorem, and for seeing what such a system would be like. 
We have already noted that LLp D Lp is a substitution-instance of T, 
and is therefore a theorem of T and all its extensions; so the new system 
would have Lp ≡ LLp as a theorem. An equivalential theorem such as 
this, which entitles us to replace some sequence of modal operators by a 
shorter sequence, we shall call a reduction law of any system of which it 
is a theorem. Taking the reduction law Lp ≡ LLp as valid would be one 
way of resolving the perplexity about 'necessarily necessary', for we 
should then say that p is necessarily necessary whenever p is necessary, 
and not otherwise. An extension of T such as we are now contemplating 
would reflect, among other things, the decision to say just this. 
Of the various equivalences which could act as reduction laws and have 
a certain plausibility under many of our intended interpretations of L and 
M, the most important are the following: 
Rl 
Mp ≡ LMp 
R2 
Lp ≡ MLp 
R3 
MP≡ 
MMp 
R4 
Lp ≡ LLp 
We shall prove a little later that none of these is a theorem of T; in 
fact one important feature of T is that it contains no reduction laws 
whatsoever.1 If we want to have an extension of T in which R1-R4 are 
theorems, however, we do not need to go as far as adding them all as 
new axioms, for three reasons: 
1. As we have already mentioned, LLp D Lp and LMp D Mp are 
theorems of T itself, and obvious substitutions in Tl will giveL p D MLp 
and Mp D MMp. So one half of each equivalence is in T already, and it 
would therefore be sufficient to add the converses, viz. 
Rla 
Mp D LMp 
R2a 
MLp D Lp 
R3a 
MMp D Mp 
R4a 
Lp D LLp 
52 


THE SYSTEMS S4, S5, B, TRIV AND VER 
2. Secondly, from R4a we could derive R3a and vice versa, and from 
Rla we could derive R2a and vice versa. (These derivations are given 
below.) So it would be sufficient to add as axioms one from each pair, 
say Rla and R4a. 
3. Thirdly, R4a is derivable from Rla, though Rla is not derivable 
from R4a. (This derivation is also given below.) So we could obtain all 
four reduction laws by adding Rla to T, while by merely adding R4a we 
could obtain two of the reduction laws (R3 and R4) but not the other two. 
All this suggests the construction of two axiomatic systems, each 
stronger than T and one of them stronger than the other. The first of 
these, obtained by adding Lp D LLp (R4a) as a new axiom to T, is 
known as the system S4. The second, obtained by adding Mp D LMp 
(Rla) to T, is known as the system S5.2 
As in the previous chapter we number theorems using the name of the 
relevant system; but for theorems of S4 and S5, to avoid confusion, we 
enclose the theorem number in brackets, writing 'S4(l)' instead of 'S41' 
and so forth. 
The system S4 
The basis of S4 is that of T with the single extra axiom 
4 Lp D LLp 
We now prove some theorems. 
S4(l) 
MMp D Mp 
PROOF 
4[~p/p] 
(1) 
L~p D LL~p 
(1) X LMI 
(2) 
-Mp D 
-MMp 
(2) X PC15(Transp) (3) 
MMp D Mp 
Q.E.D. 
S4(2) 
Lp 
≡LLp 
[R4] 
PROOF 
T[Lp/p] 
(1) 
LLp D Lp 
4, (1) X PC5 
(2) Lp ≡ LLp 
Q.E.D. 
53 


A NEW INTRODUCTION TO MODAL LOGIC 
S4(3) 
Mp ≡ MMp [R3] 
PROOF 
Tl[Mp/p] 
(1) 
Mp D MMp 
(I), S4(l) X PC5 
(2) 
Mp ≡ MMp 
Q.E.D. 
S4(4) 
MLMp D Mp 
PROOF 
T[Mplp] 
(1) LMp D Mp 
(1) X DR3 
(2) 
MLMp D MMp 
(2), S4(l) X Syll (3) 
MLMp D Mp 
Q.E.D. 
S4(5) 
LMp D LMLMp 
PROOF 
Tl[LMp/p] 
(1) LMp D MLMp 
(1) X DR1 
(2) LLMp D LMLMp 
(2), S4(2) X Eq 
(3) 
LMp D LMLMp 
Q.E.D. 
S4(6) 
LMp ≡ LMLMp 
PROOF 
S4(4) X DR1 
(1) LMLMp D LMp 
S4(5), (1) X PC5 (2) 
LMp ≡ LMLMp 
Q.E.D. 
S4(7) 
MLp ≡ MLMLp 
PROOF 
S4(6)[~p/p] 
(1) LM~p ≡ LMLM~p 
(1) X LMI 
(2) -MLp ≡ ~MLMLp 
(2) X PC 
(3) 
MLp ≡ MLMLp 
Q.E.D. 
Modalities in S4 
We define a modality as any unbroken sequence of zero or more monadic 
operators (~, L, M). We express the zero case by writing '—'. Examples 
of modalities are: —; ~; L; M~; LL; ~ML~M. It is clear, however, 
that in any system containing LMI every modality can be expressed either 
without any negation signs at all or else with only one, and that at the 
54 


THE SYSTEMS S4, S5, B, TRIV AND VER 
beginning. We shall say that a modality expressed in this way is in 
standard form, and from now on we shall assume that all modalities are 
expressed in standard form. A modality is said to be an iterated modality 
iff it contains two or more modal operators; thus LL and ~MLM are 
iterated modalities, but ~ and ~L are not. A modality is affirmative if 
it contains no negation signs and negative if it does contain one. 
We say that two modalities, A and B, are equivalent in a given system 
iff the result of replacing A by B (or B by A) in any formula is always 
equivalent in that system to the original formula; otherwise we say that 
they are non-equivalent, or distinct in that system. In a system containing 
the rules US and Eq the modalities A and B are equivalent iff (Ap ≡ Bp) 
is a theorem of that system. If A and B are equivalent in a certain system, 
and A contains fewer modal operators than 5, then B is said to be 
reducible to A in that system. Clearly the formulae we have called 
reduction laws express the reducibility of certain modalities to others in 
systems of which they are theorems. 
We are now in a position to prove an important result about S4, viz. 
that in it every modality is equivalent to one or other of the following or 
their negations: 
( i ) - ; (ii)L; (iii) M; (iv) LM; (v) ML; (vi) LML; (vii) MLM 
The proof is straightforward. We ignore the negative cases to begin 
with. Then clearly (ii) and (iii) are the only one-operator modalities. Now 
theorems S4(2) and S4(3) entitle us to replace LL by L and MM by M; so 
if we add a modal operator to (ii) or (iii) we shall obtain either a modality 
equivalent to the original or else (iv) or (v), which are therefore the only 
irreducible two-operator modalities. In just the same way, if we add a 
modal operator to (iv) or (v), the only three-operator modalities we can 
obtain are (vi) and (vii). If, however, we add a modal operator to (vi) or 
(vii), the result is always equivalent either to the original as before, or 
else to (iv) or (v) by S4(6) or S4(7); hence there cannot be any 
irreducible modalities with four or more operators. 
Clearly the negative cases can be dealt with in the same way; so what 
we have shown is that there are at most fourteen distinct modalities in S4. 
In fact all fourteen are distinct from one another, though we are not yet 
in a position to prove this. 
If we prefix a modality to a wff, α, the result is of course itself a wff. 
The implication relations which hold (in S4) among the formulae thus 
obtained from (i)-(vii) are set out in the following diagram.3 (Implication 
55 


A NEW INTRODUCTION TO MODAL LOGIC 
is symbolized by an arrow for typographical convenience.) 
La 
/ 
LMLa 
\ 
/ 
\ 
MLa 
LMOL 
a. 
\ 
/ 
MLMa 
/ 
We can obtain an analogous diagram for the negative cases by negating 
all the formulae and reversing the direction of all the arrows. 
The situation is strikingly different in T. The absence of any reduction 
laws in that system means that no matter how many modal operators a 
modality may contain, we can always construct a longer one which will 
not be equivalent to it. T therefore contains an infinite number of distinct 
modalities. 
Validity for S4 
We remarked earlier, though without proof, that the S4 axiom 4 (Lp D 
LLp) is not a theorem of T. We shall now prove this. We have already 
shown that every theorem of T is T-valid, i.e. valid on every reflexive 
frame; so in order to show that Lp D LLp is not a theorem of T it is 
sufficient to describe a reflexive frame on which it is not valid. Here is 
one such frame: W consists of three worlds w,, w2 and w3. Each world 
can see itself, w, can see w2, w2can see w3, but w, cannot see w3. Now let 
p be true in w{ and w2 but false in w3. Then since wx can see only itself 
and w2, at both of which/? is true, V(Lp,w{) =1. But since vv2 can see w3, 
at which p is false, V(Lp,w2) = 0. Hence, since wx can see w2, V(Lp D 
LLp,wx) = 0. So 4 is invalid on at least one reflexive frame, and 
therefore is not a theorem of T. 
A feature of the frame we have just considered which was crucial to 
falsifying 4 on it was that although in it we had w,Rw2 and w2Rw3, we did 
not have w,Rw3; i.e. the frame was not a transitive one. (A frame (W,R) 
56 
Lα 
LMLα 
MLα 
LMα 
MLMα 
Mα 


THE SYSTEMS S4, S5, B, TRIV AND VER 
is transitive iff R is a transitive relation over W, i.e. iff for any three 
worlds w, w' and w" in W (distinct or identical), if wRw' and w'Rw", 
then wRw".) And in fact it is impossible to falsify 4 on any transitive 
frame. The proof is this. Suppose there is some transitive frame (W,R) 
in which for some w G W, V(Lp D LLp,w) = 0. Then by [VD], 
(i) V(Lp,w) = 1 
and 
(ii) V(LLp,w) = 0. 
From (ii), by [VL], there is some w' E W such that wRw' and 
(iii) V(Lp,w') = 0 
and from (iii) in turn there is some w" £ W such that w'Rw" and 
(iv) V(p,w") = 0. 
But since R is transitive, we have wRw", and therefore, from (i), 
(v) V(p,w") = 1 
which contradicts (iv). This proves that 4 is valid on every transitive 
frame. 
Now the system S4 is K with the two additional axioms T and 4. We 
showed earlier that T is valid on every reflexive frame, and we have now 
shown that 4 is valid on every transitive frame. So by theorem 2.2 on p. 
39, it follows that every theorem of S4 is valid on every frame which is 
both reflexive and transitive, i.e. that S4 is sound with respect to the class 
of all such frames. We shall prove in Chapter 6 that S4 is also complete 
with respect to that class, so we shall define S4-validity as validity on all 
reflexive and transitive frames, and we shall call any reflexive transitive 
frame an S4-frame. In terms of the modal game, this means that we shall 
count a wff as S4-valid iff it is valid in every seating arrangement in 
which whenever any player A can see a player B and B can see a player 
C, then A must be able to see C. 
57 


A NEW INTRODUCTION TO MODAL LOGIC 
The system S5 
The basis of S5 is that of T plus the additional axiom 
E Mp D LMp 
This is the formula we previously called Rla.4 The first three theorems 
of S5 are proved in the same way as S4(l)-S4(3), but using E instead of 
4, and we leave the proofs to the reader. These theorems are 
S5(l) 
MLp D Lp 
S5(2) 
Mp ≡ LMp 
[Rl] 
S5(3) 
Lp ≡ MLp 
[R2] 
The S4 axiom Lp D LLp is not an axiom of S5, but we now prove that 
it is a theorem of S5. Since the two systems have the rest of their bases 
in common, this constitutes a proof that S5 contains S4. 
4 
Lp D LLp i 
PROOF IN S5 
Tl[Lp/p] 
(i) 
Lp: D MLp 
S5(2)[Lp/p] 
(2) 
ML/; > ≡ LMLp 
•> 
(1), (2) × Eq 
(3) 
Lp : D LMLp 
(3), S5(3) × Ec 1 
(4) Lp '. D LLp 
S5(4) 
Lip V Lq) ≡ (Lp V ' Lq) 
PROOF 
K9[Lq/q] 
(1) L(p V Lq) D (Lp V MLq) 
(1), R2 × Eq 
(2) L(p V Lq) D (Lp V Lq) 
K4[Lry/<7] 
(3) 
(Lp V LLq) > L(p > V Lq) 
(3), R4 × Eq 
(4) 
(Lp V Lq) D L(p V Lq) 
(2), (4) × PC5 
(5) 
L(p V Lq) ≡ (Lp VLq) 
S5(5) 
L(p V Mq) ≡ (Lp > s/ Mq) 
PROOF 
S5(4)[Mq/q] 
(1) L(p v LMq) ≡ (Lp ' V LMq) 
(1), Rl X Eq 
(2) 
Up V Mq) ≡ (Lp V Mq) 
Q.E.D. 
Q.E.D. 
Q.E.D. 
58 


THE SYSTEMS S4, S5, B, TRIV AND VER 
S5(6) 
M(p A Mq) ≡ (Mp A Mq) 
PROOF 
S5(4)[ ~p/p,~q/q] 
(1) 
L{~p V L~q) = {L~p \l L~q) 
PC 
(2) 
(p ≡ q ) D ( ~ p ≡ ~q) 
(1) X (2) 
(3) 
~L(~p 
V L~q) ≡ ~{L~p 
V L~q) 
(3) X LMI 
(4) 
M~(~p 
V ~Mq) ≡ ~(-Mp V ~Mq) 
(4), Def A 
(5) 
M(p A Mq) ≡(Af/> A Mq) 
Q.E.D. 
S5(7) 
M(p A Lq) = (Mp A Lq) 
PROOF 
S5(6)[Lq/q] 
(1) 
M(p A MLq) s (Mp A MLq) 
(1), R2 X Eq 
(2) 
M(p A Lq) = (Mp A Lq) 
Q.E.D. 
We can also show that E is not a theorem of S4, and therefore that S5 
properly contains S4. To do this it is sufficient to produce a frame which 
is reflexive and transitive (and is therefore a frame for S4) on which E 
can be falsified. Such a frame is the frame (W,R) where W consists of 
two worlds, wl and w2; each can see itself, wx can see w2, but w2 cannot 
see W1. Now let V be a value-assignment which makes p true in wx but 
false in w2. Then by [VM], since w, can see itself and p is true there, 
V{Mp,w1) = 1. But since w2is the only world w2 can see and p is false 
there, [VM] gives us V(Mp,w2) = 0; so by [VL], since w{ can see w2, 
V(LMp,wx) = 0. Thus at w1 Mp is true but LMp is false, and hence Mp 
D LMp is false. So E is not a theorem of S4. 
Modalities in S5 
We have shown that all the four reduction laws mentioned earlier are 
theorems of S5. We repeat them here for convenience: 
Rl 
Mp ≡LMp [S5(2)] 
R2 
Lp ≡ MLp 
[S5(3)] 
R3 
Mp ≡ MMp [S4(3)] 
R4 
Lp ≡ LLp 
[S4(2)] 
A simple way of summarizing these laws is this: in any pair of adjacent 
modal operators we may delete the first. Since this procedure may be 
repeated indefinitely, we have the more comprehensive rule that in any 
59 


A NEW INTRODUCTION TO MODAL LOGIC 
sequence of modal operators we may (in S5) delete all but the last. 
It is a straightforward consequence of this that S5 contains at most six 
distinct modalities, viz. 
( i ) - ; (ii)L; (iii)M 
and their negations. In fact these six modalities are all distinct from one 
another. 
Validity for S5 
If we look back at the frame we used a few paragraphs back to falsify E, 
we can see that although it is reflexive and transitive, it contains a world 
W1 which can see a world w2, where w2 cannot see w,. This means that 
the frame is not a symmetrical one, since a relation is said to be 
symmetrical iff whenever it holds in one direction it also holds in the 
other. I.e., a frame (W,R) is symmetrical iff, for any w and w' in W, if 
wRw' then w' Rw. 
Now E cannot be falsified on any frame which is both transitive and 
symmetrical. For suppose there is a frame (W,R) of this kind on which 
E fails. This means that there is a model (W,R,V) based on this frame in 
which for some w G W, 
(i) V(Mp,w) = 1 
and 
(ii) V(LMp,w) = 0. 
From (i), by [VM], there is some w' G W such that wRw' and 
(iii) V(p,w' ) = 1 
and from (ii), by [VL], there is some w" G W such that wRw" and 
(iv) V(Mp,w") = 0. 
Now since wRw" and R is symmetrical, we have w"Rw; and then, since 
wRw' and R is transitive, we have w"Rw'. Hence by (iv) and [VM], we 
have 
(v)V(p,w') = 0 
60 


THE SYSTEMS S4, S5, B, TRIV AND VER 
which contradicts (iii). 
Now S5 is K with the two extra axioms T and E. Since we showed 
earlier that T is valid on every reflexive frame, and have now shown that 
E is valid on every transitive symmetrical frame, theorem 2.2 on p. 39 
shows that S5 is sound with respect to the class of all frames which are 
reflexive, transitive and symmetrical. A relation which is reflexive, 
transitive and symmetrical is known as an equivalence relation. Since we 
shall be able to prove that S5 is also complete with respect to this class 
of frames, we define S5-validity as validity on every equivalence frame, 
and an S5-frame as a frame of this kind. 
An everyday example of an equivalence relation is 'has the same height 
as', and this can be used to illustrate the fact that when such a relation is 
defined over a class of objects it divides them into a number (though 
perhaps only one) of self-contained 'equivalence classes'. Thus if 'has the 
same height as' is defined over a class of human beings, then for each 
height that any of them has there will be the 'equivalence class' of all and 
only those who have that height. Within each such equivalence class 
everyone will have the relevant relation to everyone, but no one will have 
that relation to anyone in any other equivalence class. To apply this to 
frames: if in a frame (W,R) R is an equivalence relation, this means that 
every world will be able to see every world in its own equivalence class 
but no world in any other equivalence class, and hence that we can 
equally well think of such a frame, not so much as a single frame but as 
a collection of separate frames, in each of which every world can see 
every world. And what this amounts to is that we could equally well, and 
equivalently, define S5-validity as validity on every frame in which R is 
a universal relation, i.e. one which holds between every pair (distinct or 
identical) of worlds in that frame. 
(In terms of the modal game, what this means is that in order to 
produce a seating arrangement appropriate for S5, we must either let 
every player see every player without restriction, or else divide the 
players into segregated groups, in each of which everyone can see 
everyone but no one can see anyone outside the group. But if we do the 
latter, we might as well be playing a number of distinct games 
simultaneously, in each of which everyone can see everyone.) 
In evaluating formulae in models based on frames of this kind, we 
could replace [VL] by the simpler rule 
[VLS5] V(Lα,w) = 1 if V(α,w' ) = 1 for every w' G W; otherwise 
V(Lα,w) = 0. 
61 


A NEW INTRODUCTION TO MODAL LOGIC 
However, since this simplification can be undertaken only in the case 
of S5, we shall for the sake of uniformity stick to [VL] and assume that 
in S5 frames R is an equivalence relation but not necessarily a universal 
one. 
The Brouwerian system 
A special interest attaches to the following pair of theorems of S5: 
S5(8) 
p D LMp 
PROOF 
Tl, E × Syll 
S5(9) 
MLp D p 
PROOF 
S5(8)[~p/p] 
(1) 
~p D LM~p 
(1) × LMI 
(2) 
~p 
D~MLp 
(2) × PC15(Transp) (3) 
MLp D p 
Q.E.D. 
Neither of these theorems is in S4. Indeed, if we were to add either as 
an extra axiom to S4 we should obtain a system at least as strong as S5. 
(In fact we should obtain exactly S5.) In the case of S5(8) we need only 
to substitute Mp for p and then apply R3 to obtain the S5 axiom E, and 
the case of S5(9) is not much more complicated. If, however, we were 
to add either of them to T instead of to S4 we should obtain not S5 but 
a system which is weaker than S5 and which neither contains nor is 
contained in S4. This system has been called the Brouwerian system, and 
S5(8) the Brouwerian axiom.5 We shall use 'B' to refer to the system and 
'B' (in bold face) to refer to the axiom. 
The following is a derived rule of B (and also, of course, in view of 
the way in which it is derived) of S5: 
DR4 
|- Mα D β -* \-α D Lβ 
PROOF 
Given: 
(1) 
Ma D β 
(1) X DR1 
(2) LMa D Lβ 
B[a/p] 
(3) α D LMα 
(3), (2) X Syll (4) α D 
Lβ 
Q.E.D. 
62 


THE SYSTEMS S4, S5, B, TRIV AND VER 
Yet another way of obtaining S5 would be to add DR4 as a primitive 
transformation rule to S4, without any new axioms; for then, since MMp 
D Mp (S4(l)) is a theorem of S4, DR4 would immediately give us Mp 
D LMp (i.e. E). 
Validity for B 
We show first that B is valid on every frame in which R is symmetrical. 
Let (W,R, V) be any model based on any symmetrical frame. Suppose that 
for some w E W, V(p,w) = 1. Now consider any w' such that wRw'. 
Since R is symmetrical, we also have w'Rw; and then, since V(p,w) = 
1, [VM] gives us V(Mp,w') = 1. Since this is so for every W such that 
wRw', V(LMp,w) = 1. Thus whenever p is true at any world, so is LMp, 
provided that R is symmetrical; and therefore p D LMp is valid on every 
symmetrical frame. 
We already know that T is valid on every reflexive frame; so, since 
the system B is K + T + B, theorem 2.2 gives us the result that B is 
sound with respect to the class of all frames which are both reflexive and 
symmetrical. Such frames we shall call B-frames, and we define B-
validity as validity on every B-frame. 
Now we have seen that adding B to S4 gives S5, and we have also 
seen that S4 is weaker than S5; and from this it follows that B is not in 
S4, and hence that S4 does not contain the system B. (In fact the model 
we used to show that E is not in S4 can also easily be used to show that 
B is not in S4.) Furthermore, B does not contain S4 either, since 4 fails 
on the following reflexive and symmetrical (but non-transitive) frame 
(W,R): W consists of three worlds, wl, w2 and w3. Each world can see 
itself, and in addition we have W1Rw2, w2Rw1, w2Rw3 and w3Rw2. It may 
help to visualize the frame like this: 
W
1** W2 ** W3 
- where the arrows represent the accessibility relation, and it is also 
assumed that each world is related to itself. If we now form a model on 
this frame by letting V(p,W1) = 1, V(p,w2) = 1 and V(p,w3) = 0, then 
4 fails in this model for just the same reasons as it fails in the model we 
used on p. 56 to show that 4 is not T-valid (Lp is true in wl, but it is false 
in w2 and so LLp is false in w,). The only difference between the two 
cases is that our present frame is symmetrical as well as reflexive, and we 
have shown that every theorem of B is valid on every such frame. 
So B and S4 are independent systems, in the sense that neither contains 
63 


A NEW INTRODUCTION TO MODAL LOGIC 
the other, and yet each lies between T and S5. 
Some other systems 
In later chapters we shall discuss other modal systems; we shall see that 
there are infinitely many of these, and we shall look at some of the 
general properties of modal systems. But even with the tools already at 
our disposal we can see how to define some other systems. For instance, 
instead of adding 4 to T to obtain S4, we could add it merely to K or to 
D. The resulting systems are often called K4 and KD4 respectively. If we 
define YA-frames as those which are transitive (whether or not they are 
reflexive), and KD4-frames as those which are both serial and transitive, 
then the results we have proved so far are sufficient to show that all the 
theorems of K4 are valid on all K4-frames and all the theorems of KD4 
are valid on all KD4-frames. It is not difficult to produce a serial and 
transitive frame on which T fails: the frame we used on p. 45 to prove 
that T is not a theorem of D was in fact such a frame. (It was, of course, 
not reflexive.) This shows that KD4 does not contain T; a fortiori, K4 
does not contain it either. We have also shown that 4 is not in T. Thus 
KD4 and T are independent of each other, and so are K4 and T. 
Moreover, KD4 is a proper extension of K4; for the frame which consists 
of a single dead end is (trivially) transitive and therefore a frame on 
which every theorem of K4 is valid; but as we saw on p. 45, D is not 
valid on any frame which contains a dead end. 
We can similarly add B to K or to D instead of to T, to obtain the 
systems KB and KDB, which can easily be shown to be sound with 
respect to the classes of symmetrical frames and serial and symmetrical 
frames respectively. It can then be shown, by arguments of the kind used 
in the previous paragraph, that each of KB and KDB is independent of 
each of K4, KD4 and T; but we leave this task to the reader.6 
Collapsing into PC 
We shall now look at a system which can be obtained by adding even to 
D, and a fortiori to any of the stronger systems we have mentioned, the 
extra axiom p D Lp. This formula is not even S5-valid, since it can 
easily be falsified on a two-world frame in which each world can see both 
worlds (and which is therefore an S5-frame), by letting p be true in one 
world but false in the other. Nevertheless adding it even to S5 would not 
result in an inconsistent system, for the following reason. Consider a 
frame in which there is only one world, w, and it is related to itself. This 
is clearly an S5-frame, butp D Lp is valid on it; for if V(p,w) = 1, then 
64 


THE SYSTEMS S4, S5, B, TRIV AND VER 
V(p,w') = 1 for every w' such that wRw', since there is only one such 
w', namely w itself, and so V(Lp,w) — 1. Every theorem of S5 + p D 
Lp is therefore valid on this frame; but p is not, since there is obviously 
a value-assignment which makes p false at w. So not every wff is a 
theorem of S5 + p D Lp ; i.e. the system is consistent. 
In this system the new axiom, together with D, immediately yields p 
D Mp (by Syll); from this (by [~p/p], Transp and LMI) we can obtain 
Lp D p, and then, by simple steps, Lp s p and Mp ≡ p. By the rules 
US and Eq every formula would be then equivalent to the result of 
deleting all its modal operators; so in any formula we could delete or 
insert Ls and Ms to our heart's content (provided we preserved well-
formedness), and the result would be equivalent to the original. In such 
a system, therefore, the modal operators would merely 'idle'; in 
interpreting the system we could draw no significant distinction between 
necessity, possibility and truth, and for all practical purposes it could be 
regarded simply as the Propositional Calculus itself, encrusted with Ls 
and Ms as mere typographical embellishments. The PC wff which results 
from deleting all the modal operators in a modal wff α is said to be the 
PC-transform of α A system such as the one we have just described, in 
which every wff is equivalent to its own PC-transform, may be said to 
collapse into PC. 
It is worth noting that although in the previous paragraph we appealed 
to the rule Eq, we could have obtained all our results from the new axiom 
and D alone (together with the axiom schema PC). We did not even need 
to have K as an axiom, nor did we need the rule of Necessitation. 
Moreover, the system would clearly contain S5, since the results of 
deleting all the modal operators in T and in E are PC theorems. 
If we add the stronger axiom p ≡ Lp even to K the resulting system 
similarly collapses into PC. The system D + p D Lp (or K + p ≡Lp) 
is known as the Trivial system (Triv for short), because in it the modal 
operators are trivial in the sense we explained earlier. The wff p ≡ Lp 
is itself sometimes called Triv. 
It is only in the very strong system Triv that every wff is equivalent to 
its PC-transform. Even in the much weaker system D, however (and in 
all systems containing it), there is a somewhat analogous relation between 
a certain class of wff and their PC-transforms. These are the wff which 
at the end of the previous chapter we called constant wff - wff constructed 
out of the constant true and false propositions T and 1 by truth-
functional and modal operators. The PC-transform of any constant wff is 
65 


A NEW INTRODUCTION TO MODAL LOGIC 
of course itself a constant PC wff, and we noted on p. 48 that every such 
wff is either PC-valid or PC-unsatisfiable. The relation is this: If a is any 
constant wff, then if its PC-transform is PC-valid, a itself is a theorem 
of D; otherwise (i.e. if its PC-transform is unsatisfiable) ~α is a theorem 
of D. Let us denote the PC-transform of any wff α by r(a); then we can 
state the result as the following lemma: 
LEMMA 3.1 Let a be any constant wff. Then if r(a) is PC-valid, |-Dα; 
otherwise f-D~α. 
Since every constant wff can be constructed from 1 by ~, V and L, 
in order to prove the lemma it is sufficient to show (i) that it holds for 1 , 
(ii) that if it holds for a wff α it also holds for — α, (iii) that if it holds 
for a it also holds for Lα, and (iv) that if it holds for a and for (3 it also 
holds for α V (3. 
To show (i) we need only remark that the PC-transform of 1 is 1 
itself, and that since 1 is unsatisfiable its negation, ~ 1 , is PC-valid and 
therefore a theorem of D. (ii) and (iv) hold by purely PC principles, and 
we omit the details of their proofs here. (They rely on the fact mentioned 
above that if α is a constant wff then T(α) is either PC-valid or PC-
unsatisfiable.) For (iii) the proof is this: (A) Suppose that T(Lα) is PC-
valid. Clearly T(La) is the same wff as r(α); so, since the lemma is 
assumed to hold for a, \-D α; hence by N, 
D Lα. (B) Suppose that 
T(Lα) is not PC-valid. As before, T(La) is the same wff as r(a), and the 
lemma is assumed to hold for α. Hence ho ~ α; hence (by N) |-D L ~ α; 
hence (by D) 
DM~α; 
hence (by LMI) |-D —Lα. 
We shall have a use for lemma 3.1 shortly. In the meantime, however, 
we shall consider another way in which a system can collapse into PC. 
We produced the system Triv by adding p D Lp to D. Adding it to K 
would not have been enough. For consider the frame which consists of a 
single dead end. It is easy to check that on this frame p D Lp is valid but 
Lp D p is not, so the latter is not a theorem of K + p D Lp. In that 
system, therefore, unlike Triv, p D Lp and Lp D p are not equivalent, 
even though they have the same PC-transform. 
The system we are about to consider, however, is not K + p D Lp but 
the even stronger system produced by adding the axiom Lp to K. From 
this axiom we can of course obtain by US every wff of the form Lα as 
a theorem - even LI. 
This system is known as the Verum system (Ver 
for short). It no doubt appears bizarre in many ways, and certainly seems 
to impose some strain on the attempt to interpret L as meaning 
66 


THE SYSTEMS S4, S5, B, TRIV AND VER 
'necessarily'. It is nevertheless a consistent system because Lp, and 
therefore every theorem of the system, is valid on the one-world dead end 
frame we have just referred to, but p is not. In Ver any wff will be 
equivalent not, as in Triv, to its own PC-transform, but to the wff which 
results from replacing every well-formed expression of the form La in it 
by T, and every one of the form Ma by 1 . Since the formula thus 
obtained will always be a PC wff, we could regard the Verum system as 
providing a different form of collapsing into PC. 
The reason for calling K + Lp the Verum system is that in interpreting 
it we think of La as always true. The wff Lp is sometimes itself called 
Ver. 
Triv and Ver are incompatible systems; i.e. the system K + Triv + 
Ver is inconsistent. For if both Lp and p = Lp are theorems, so is/?, and 
therefore by US every wff is a theorem. Hence Triv is not contained in 
Ver, nor is Ver in Triv. 
Two other results which can be proved about these two systems are: 
(1) Every normal modal system, in the sense explained on p. 40 (i.e. 
every consistent extension of K which retains the rules US, MP and N), 
is contained either in Triv or in Ver. (Some systems, of course, like K 
itself or K4 or KB, are contained in both.) 
(2) Each of Triv and Ver is a maximal system, in the sense that in the 
case of each of them, if any wff which is not already a theorem were 
added to it, the resulting system would be inconsistent.7 
The second of these results follows from the first. To show this, let us 
suppose that we have proved (1). Then to prove that Triv is a maximal 
system we take any wff α which is not a theorem of Triv. In that case, 
the system Triv + α is not contained in Triv, and so by (1) it must either 
be inconsistent or else be contained in Ver; but the latter would mean that 
Triv itself is contained in Ver, and we saw above that it is not. That Ver 
is also a maximal system follows from (1) in an exactly analogous way. 
So in order to prove both (1) and (2) it will be sufficient to prove (1). 
Our strategy for proving (1) will be to prove the following two 
lemmas, from which (1) clearly follows immediately: 
LEMMA 3.2 Every consistent extension of K which is not contained in 
Ver contains D. 
LEMMA 3.3 Every consistent system which contains D is contained in 
Triv. 
67 


A NEW INTRODUCTION TO MODAL LOGIC 
The proof of lemma 3.2 will be made easier by some techniques we 
shall introduce on p. 108, so we shall postpone it till then. Lemma 3.3, 
however, can be proved with our presently available resources, as 
follows: 
Proof of lemma 3.3: It is sufficient to show that if S is any system which 
contains D and has some theorem a which is not a theorem of Triv, then 
S is inconsistent. We show this as follows. Since α is not a theorem of 
Triv, its PC-transform T(α) is not PC-valid. Now precisely the same 
procedure which we used on p. 47 to show that every invalid wff of PC 
has a substitution-instance which is an unsatisfiable constant wff will also 
produce for any wff with an invalid PC-transform a substitution-instance 
which is a constant proposition whose PC-transform is an unsatisfiable 
wff. Let α' be such a substitution-instance of α. Then (1) by US, α' is 
a theorem of S. But by lemma 3.1, ~α' is a theorem of D, and hence, 
since S contains D, it is also a theorem of S. Thus both α' and ~α' are 
theorems of S, and S is therefore inconsistent. 
Exercises — 3 
3.1 Prove in S4: 
(a) 
L(p D q) D L(Lp D Lq) 
(b) 
(Lp V Lq) = L(Lp V Lq) 
(c) 
ML(p D LMp) 
(d) 
M(Lp D Mq) D M(p D q) 
3.2 Where A is any affirmative modality (i.e. a string of Ls and Ms) 
show that L(p D q) D L(Ap D Aq) is a theorem of S4. 
3.3 
Show that T with Lip D q) D L(Lp D Lq) in place of K is 
deductively equivalent to S4. 
3.4 Prove that the modalities listed on p. 55 are non-equivalent in S4. 
3.5 Prove that where Lnp is p with n Ls in front of it then for n ≠ m, 
Lnp ≡ Lmp is not a theorem of T. 
3.6 
S4.2 is S4 + the axiom 
Gl 
MLp D LMp 
Prove that S4.2 has only four proper (i.e. non-empty) affirmative 
modalities, L, ML, LM, and M and that in terms of strength they can be 
68 


THE SYSTEMS S4, S5, B, TRIV AND VER 
linearly ordered in the order listed here. 
3.7 
Prove the following in S5: 
(a) 
L(Lp D Lq) V L(Lq D Lp) 
(b) 
L(Mp D q) ≡ L(p D Lq) 
(c) 
MLp D (Mq D L(p A Mq)) 
3.8 
Show that S5 can be axiomatized as 
(a) 
D + B + E 
(b) 
S4 + B 
or as 
(c)K + 
Ei 
LMLp D p 
E2 
MLp D LMLLp 
(d) 
Show that neither K 4- E, nor K 4- E2 on its own gives T, KB 
(K + p D LMp) or K4 (K + Lp D LLp). (Hughes 1980). 
3.9 
Show that S5 can be axiomatized as PC, US, MP, T and 
\- a D jS -* a D L@y provided α is fully modalized, i.e. every 
variable in a is in the scope of a modal operator. (Prior 1955a, Lemmon 
1956). 
3.10 
Show that adding Lip V Lq) D (Lp V Lq) to T gives a system 
deductively equivalent to S5. 
3.11 
Prove that K + E is sound with respect to the class of frames in 
which if wRw' and wRw" then w'Rw". 
3.12 
Prove in B 
(a) 
(MLp A MLq) D LM(p A q) 
(b) 
MLp D LMp 
3.13 
Show that B can be axiomatized by dropping N and K and adding 
Band 
R* 
\-α 
D 0 
\-Lα 
D Lβ (Jennings 1981) 
3.14 
Show that 
\-La 
|- α is not a rule of KB (i.e. K + 
p D MLp). 
69 


A NEW INTRODUCTION TO MODAL LOGIC 
3.15 
Show that if K is strengthened to an equivalence (L(p D q) ≡ 
(Lp D Lq)) then T would collapse into PC. 
3.16 
Prove that the addition to S5 of the axiom LMp D MLp would 
make the resulting system collapse into PC. 
3.17 
Show that K + p D Lp is sound with respect to any class 
consisting of just two frames, each containing just one world. In one 
frame this world can see itself. In the other it is a dead end. 
3.18 
Set out fully the inductive steps for cases (ii) and (iii) in the proof 
of lemma 3.1 on p. 66. 
Notes 
1 See Bellissima 1989. Thomas 1964 cites as an unpublished result by Sobociriski 
the fact that for each n the system S4n, obtained by adding Up D Ln+lp (where 
Lnp is p preceded by n Ls) properly contains S4m when n < m. The result is easy 
to obtain using the obvious definition of validity for these systems (Exercise 3.5). 
Sugihara 1962 proves that T + LLp D LLLp contains infinitely many distinct 
modalities. 
2 The names 'S4' and 'S5', which have now for long been standard, derive from 
Lewis and Langford 1932 (p. 501), where systems deductively equivalent to these 
are the fourth and fifth in a series of modal systems. (For more on this see 
Chapter 11.) In the naming system referred to in note 7 on p. 50 S4 would be 
KT4, S5 would be KTE, and so on. 
3 This diagram is given in Prior 1957, p. 124. The results were originally 
obtained by Becker 1930 and Parry 1939. 
4 The name E for this wff is found on p. 50 of Lemmon and Scott 1977. It 
corresponds with a condition they call the euclidian condition. (See exercise 
3.11.) Chellas 1980, p. 6 calls it 5, and thus refers to S5 as KT5. 
5 This formula derives from Becker 1930, p. 509. An alternative version of B is 
of course ~p D L~Lp. Some authors have called B the Brouwersche axiom, and 
the system the Brouwersche system, perhaps because in Lewis and Langford 
1932, p. 497, Becker's German phrase 'Brouwersche Axiom' is quoted 
untranslated. The name derives from L.E.J. Brouwer, the founder of the 
intuitionist school of mathematics. In the intuitionist propositional calculus the law 
of double negation is not valid as an equivalence. More precisely, p D ~ ~p is 
valid but ~ ~ p D p is not. One way of making this sound reasonable has been 
to suppose that in this calculus ~ means something like 'it is not possible that', 
i.e. that it means what we usually mean by L ~ . Now if we replace ~ by L ~ 
then ~ ~p D p becomes L~L~ pD p, i.e. LMp D p, and p D ~ ~ p becomes 
p D LMp, i.e. B. On this view B therefore represents the intuitionistically 
70 


THE SYSTEMS S4, S5, B, TRIV AND VER 
acceptable direction of the double negation law, and so has a connection, albeit 
somewhat tenuous, with Brouwer. (For a discussion of the intuitionistic 
propositional calculus see pp. 224-225.) 
6 These systems have some interesting properties in the matter of derived rules. 
We mentioned on p. 45 that a derived rule may hold in a system but not always 
in a stronger system. Some interesting examples of this are provided on p. 181 f. 
of Chellas 1980. Thus the rule |- La 
|- α is a rule of K, D and KDB but not 
a rule of KB. (It is trivially a rule of every extension of T). Another example is 
what is called the 'rule of disjunction' that if |- Lα V L(S then either |- α or 
(- (3. This is a rule of K, D, T and S4 but not a rule of B or S5. (See Chellas 
1980, p. 181 and Hughes and Cresswell 1984, pp. 96-100. A weaker version of 
DR4 on p. 62, viz. 
|- Ma D 
α 
\- α D Lα, is studied in Chellas and 
Segerberg 1994 and Williamson 1994. Other studies of the effects of rules in 
systems of modal logic may be found in Williamson 1988 and 1992, where 
various philosophical interpretations of L are argued to fit certain rules. 
7 These results are obtained algebraically in Makinson 1971. See also Segerberg 
1972. For some early results of this kind see McKinsey 1944. 
71 


4 
TESTING FOR VALIDITY 
A wff α of modal logic is valid (with respect to a class ^of frames) iff, 
for every (W,R) G #, and every model (W,R.V) based on (W,R), 
V(α,w) = 1 for every w G W. In this chapter we shall show how to test 
wff for validity in K, D, T, S4 and S5, when the relevant classes of 
frames are the following: For K, & is the class of all frames without 
restriction. For D, ^is the class of all serial frames; for T, all reflexive 
frames; for S4, all reflexive and transitive frames and finally for S5, all 
equivalence frames, i.e. all frames which are reflexive, transitive and 
symmetrical. So let S be one of these systems, and let & be the 
appropriate class of frames. In what follows, by an S-model we shall 
mean a model based on a frame in the class of frames appropriate for S. 
In testing a PC formula for validity by the truth-table method outlined 
in Chapter 1 we list all the distinct PC-assignments with respect to the 
variables in the formula, and then check whether the formula is true for 
each of them. This method can in theory be applied to any PC formula 
whatsoever; and even for moderately complicated formulae it is a 
practical method since for a formula containing n variables there are only 
2n distinct value-assignments. The corresponding method for a system S 
would be to list all the relevantly different S-models for the formula with 
which we were concerned, and then check whether the formula was true 
in every world in each of them. Now, as we shall show in Chapter 8, for 
the systems we have just mentioned, though not for all modal systems, 
this would in theory be a sound procedure since, for any particular 
formula, a, only models with no more than a certain finite number of 
72 


TESTING FOR VALIDITY 
members of W (depending on the structure of α) need be considered, and 
for any finite number of members of W only a finite number of distinct 
S-models can be constructed. Nevertheless, the number of distinct 
S-models, though always finite for any formula, is apt to be extremely 
large, and this method would involve us in millions of calculations in 
order to test even a quite simple formula. 
Fortunately there are shorter methods. The one we shall describe1 is an 
extension of the Reductio test for PC-validity outlined on pp. 11 — 12, 
with which we shall assume that the reader is familiar. Briefly, we 
attempt to find, for a given wff, a, a falsifying S-model (i.e., an S-model 
in which, for at least one w G W, V(α,w) = 0). The method will enable 
us to construct such an S-model if this is possible, or else it will 
demonstrate the impossibility of there being such an S-model. In the 
former case of course, α is invalid; in the latter case, α is valid. 
Semantic diagrams 
We shall describe the method of testing for validity by working through 
a number of examples, and will concentrate initially on the system K. Our 
first example will be the wff K itself. Of course we have already 
established its validity on p. 20, and again on p. 41, but we will use it 
here to illustrate the method of testing. For variety we shall consider K 
in a form which is equivalent to it in PC. 
[1] 
(Lp A L(p D q)) D Lq 
We begin by supposing that in some K-model there is a world (say wx) 
such that V([l],w,) = 0. The rule [VD] then immediately gives 1 as the 
value (in wx) of the antecedent, and 0 as the value of the consequent; i.e. 
we have V(Lp A L(p D g),w,) = 1 and V(Lq,wx) = 0. [V A] then gives 
V(Lp,w>,) = 1 and V(L(p D q),w{) = 1. This is as far as purely PC 
methods can take us at this stage and they give us the following values in 
w,: 
(Lp AL(p 
D q)) DLq 
1 1 1 
0 0 
* 
At the places marked by asterisks we have a wff beginning with an L. If 
it has the value 1 it has an asterisk above it, while if it has the value 0 it 
73 


A NEW INTRODUCTION TO MODAL LOGIC 
has an asterisk below it. Now in K the fact that Lp and L(p D q) are both 
true in w, does not require that p and p D q are both true in w, (though 
in T this would be required). And the fact that Lq is false in w, does not 
require that q be false in w,. However it does require that there be some 
world, call it w2, that w1, can see at which q is false. And since w, can see 
w2 then p and p D q must be true at w2. We can set out the whole 
calculation diagrammatically as follows: 
w, 
* 
* 
(Lp AL(p D q)) ^Lq 
1 
11 
00 
* 
1 
q 
o 
p 
p D q 
1 
1 1 0 
A contradiction arises at the places underlined, which shows that the wff 
is K-valid. 
Our second example will involve the operator M. 
[2] M(p A Lq) D M(p A Mq) 
If we suppose V([2],w1) = 0 then the PC rules give us the following 
values (in w1): 
w1 
* 
M(p Λ Lq) 
M(p Λ Mq) 
1 
0 0 
* 
The asterisk under the first M indicates that we need a world, w2, 
accessible to w1, in which p Λ Lq is true. The asterisk over the second 
M indicates that in w2 p Λ Mq has to be false. The diagram is as 
follows: 
74 


TESTING FOR VALIDITY 
w1 
w2 
* 
M(p Λ Lq) DM(p Λ Mq) 
1 
0 0 
* 
* 
p ΛLq 
1 1 1 
* 
p ΛMq 
1 0 0 
At this point we have two wff with asterisks above their operators. What 
do we do? Well, if we are in K we need do nothing. For if w2 is a dead 
end then Lq will be true at w2 and Mq will be false. And this shows that 
[2] is not K-valid. 
When a diagram ends without an inconsistency this fact can be used to 
construct a model in which the wff being tested is false at some world. 
The present diagram leads to the following K-model. W = {w1,w2} 
w1Rw2. (w1 cannot see itself, and w2 is a dead end — it cannot see 
anything.) The values of p and q in w1 are arbitrary, since they do not 
make a difference to the value of the whole wff, and the value of q in w2 
is also arbitrary. We must have V(p,w2) = 1, and for definiteness, let us 
also put V(p,w1) = V(q,w1) = V(q,w2) = 1. Since w2 is a dead end 
V(Lq,w2) = 1 and V(Mq,w2) = 0 and so V(p Λ Lq,w2) = 1 and 
V(p Λ Mq,w2) = 0. Since w2 is the only world that w1 can see, 
V(M(p Λ Lq),w1) = 1 and V(M(p Λ Mq),w1) = 0, and that is enough 
to give V([2],w1) = 0. In the diagram each rectangle represents a world 
and the arrow represents the accessibility relation. 
We shall call a diagram of the kind we have just constructed a semantic 
diagram, and the whole method the method of semantic diagrams. Before 
proceeding to further examples we shall now set out explicitly the rules 
for constructing semantic diagrams. 
I Rule for putting in asterisks 
An asterisk is put above every L which has a 1 beneath it and above every 
M which has a 0 beneath it. An asterisk is put below every L which has 
a 0 beneath it and below every M which has a 1 beneath it. 
75 


A NEW INTRODUCTION TO MODAL LOGIC 
II Rules for a new world 
A. If in a world w there occurs a formula Lα with an asterisk above 
the L then, in every world accessible to w, α must be assigned 1. 
B. If in a world w there occurs a formula Mα with an asterisk above 
the M then, in every world accessible to w, α must be assigned 0. 
C. If in a world w there occurs a formula Lα with an asterisk below 
the L then there must be a world accessible to w in which α is assigned 
0. 
D. If in a world w there occurs a formula Mα with an asterisk below 
the M then there must be a world accessible to w in which α is assigned 
1. 
It should be clear that when we construct new worlds in accordance 
with these rules we do so in a way which complies with [VL] and [VM]. 
In terms of the diagrams a world, wi,is represented by a rectangle with 
'wi' written beside it; and when a world, wj, accessible to wi, is required 
in order to satisfy C or D, we draw a rectangle labelled 'wj', with an 
arrow to it from wi to represent accessibility. Certain formulae will have 
to be written in wj and certain values assigned to them as dictated by the 
rules in II (A—D). We shall refer to these values as the initial values in 
wj, values which we then have to assign to various well-formed parts of 
the formulae in wj in order to comply with the conditions for a value-
assignment we shall call consequential values in wj. 
Although [2] is not a theorem of K, it is a theorem of D. And the 
reason is not hard to see. In D-frames R is serial. In other words there 
can be no dead ends. This means that there must be a world w3, 
accessible to w2 in the semantic diagram for [2], and so the diagram must 
continue as follows: 
q 
q 
1 
0 
q must be given 1 in w3 because of the asterisk over the L in w2, and must 
be given 0 in w3 because of the asterisk over M. And this leads to a 
contradiction. 
Our third example is: 
[3] 
M(p D Lp) 
76 
w3 
D 


TESTING FOR VALIDITY 
This is T2 on p. 42 and we shall test it in D. 
w1 
M(p D Lp) 
0 
Seriality requires a w2 that w1 can see, and the asterisk over the M 
requires p D Lp to be false there : 
w2 
The asterisk under Lp requires a world w3 that w2 can see with p false. 
At this point all required values have been put in. However, seriality 
requires a world that w3 can see. If this had to be a world different from 
all that have gone before we should be in trouble, since we should have 
to be constructing new worlds endlessly, but to no purpose. However, 
there is nothing to stop the world w3 can see being w3 itself, and that is 
what we shall assume. The diagram then leads to the following D-model: 
W = {w1,w2,w3}, w1Rw2, w2Rw3, w3Rw3. 
V(p,w1) = V(p,w2) = 1, V(p,w3) = 0. 
The situation with [3] is, however, different in T. T-frames are reflexive, 
and this means that where an asterisk occurs over an L then the wff that 
follows L must be given 1 in that world, and where an asterisk occurs 
over an M the wff that follows the M must be false in that world. 
77 
* 
W3 
p 
0 


A NEW INTRODUCTION TO MODAL LOGIC 
* 
M(p DLp) 
0 1 001 
* 
The asterisk over M in w1 requires, in a T-diagram, that p D Lp be 0 in 
w1, which requires Lp to be false there. And so the asterisk under Lp 
requires a world w2 that w1 can see at which p is false. However the 
asterisk over M in w1 requires p D Lp to be false in w2, which would 
force p to be true there, resulting in an inconsistency. 
The next two examples will be tested in T. 
Fourth example 
[4] 
M(p Λ Mq) D (LMp D MLq) 
By steps which should now be obvious we reach the following: 
* 
* 
M(p Λ Mq) D (LMp D MLq) 
1 
0 1 1 
0 00 
* 
* 
* 
We have, as yet, no definite values for p, q, or Mq in w1. It is clear, 
however, that the value of (p Λ Mq) in w1 does not matter so long as 
there is some world (accessible to w1) in which its value is 1. Similarly, 
all that is required in the case of p and q is that in some world (accessible 
to w1) V(p) = 1, and that in some world (accessible to w1) V(q) = 0. 
In other words the fact that no further values have been assigned in w1 
does not in any way prevent the application of rules A—D. Continuing the 
procedure we get the following diagram which shows [4] to be invalid in 
T: 
78 
w1 
w2 
p 
p DLp 
0 
1 000 
* 
w1 


TESTING FOR VALIDITY 
w, 
w, 
* 
* 
M{p A Mq) D (LMp D MLq) 
1 
0 1 1 
0 00 
* 
* 
* 
/ 
\p A Mq \Mp W\ 
1 1 1 
* 
: ii 
J 
i • * 
1 
W-x [p \Mp LTH 
1 i n 
0 
L* 
1 
\ 
H>„ n? 
1 
1 
\Mp\ i ? 
0 : i : 00 
w< [U
w< S W7 0 
In this diagram the rules have been modified in the following way: In 
w2 no * has been put under the M in Mp. This is because p has already 
been given the value 1, and so no further world is required. Similarly no 
asterisk has been put under Mp in w3 or Lq in w4. In a T-diagram, where 
α has 0 in a rectangle then Lα must also have 0 in that rectangle and 
where α has 1 Mα must also have 1, and no new rectangle need be 
constructed, and no further action need be taken in respect of such Ls and 
Ms. Since the purpose of the * is to indicate that something needs to be 
done we leave them out in these cases. 
We can often shorten a diagram such as the one above, since instead 
of constructing a new rectangle whenever we need one we may find that 
a rectangle we have already constructed contains the values which are 
required in the new rectangle, or that it can be made to contain them by 
filling in values which, although not required in the already existing 
rectangle, are compatible with it. In this way our present diagram can be 
shortened to the following: 
w1 
* 
* 
M(p A Mq) D (LMp D MLq) 
1 1 1 11 0 1 11 0 001 
* 
* 
* 
* 
W2 
79 


A NEW INTRODUCTION TO MODAL LOGIC 
What has happened here is that we find that it is possible to let w1 itself 
take over the functions for which we previously constructed many new 
rectangles and that only one other rectangle is required. 
Although short cuts such as these can obviously save a lot of time in 
practice, we shall assume in our theoretical discussion of diagrams that 
no use has been made of them. In a diagram in which short cuts are not 
used no values will occur in any rectangle unless they are explicitly 
required by the rules of the method. 
Alternatives in a diagram 
Fifth example 
[5] L(Mp = Mq) D L(p = Lq) 
The first rectangle in the diagram for [5] will be: 
* L(Mp ^Mq) 
D L(p = Lq) 
1 
1 
0 0 
t 
* 
At the place marked by a t we have a situation which can also arise in 
the PC Reductio test (pp. 11 — 12): a truth-functional operator has a value 
under it, but we cannot determine unambiguously the values of its 
arguments. We shall call such an operator, for brevity, a t-operator. In 
the present case, the first = in [5] is a f-operator in w1 and by [V=], 
if Mp = Mq is to have the value 1 in w1, then Mp and Mq must have the 
same value in w1, but the assignment so far does not tell us which value 
this is. So we have two cases to consider, one in which Mp and Mq are 
both assigned 1, and one in which they are both assigned 0. We can 
represent these in this way: 
* 
L(Mp = Mq) D L(p = Lq) 
1 1 
1 1 
0 0 
* 
* 
* 
80 
W1(i) 


TESTING FOR VALIDITY 
w1(ii) 
* * 
* 
L(Mp - Mq) 3 L(p -Lq) 
1 0 
1 0 
0 0 
* 
As in the parallel cases in the PC Reductio test, it is only if each of these 
assignments leads to an inconsistency that [5] is valid; i.e., if either of 
them leads to a falsifying model, [5] is invalid. Now neither w1(i) nor 
w1(ii) contains any t-operators, so we can begin a diagram with each of 
them by our earlier rules. We take w1(ii) first, since it is the simpler. This 
does lead to an inconsistency, as the following diagram shows: 
W1(ii) 
* * 
* 
L(Mp = Mq) D L(p~= 'Lq) 
1 00 1 00 0 0 0 
* 
00 
* 
W2 
p =Lq 
0 0 0 0 
Mp = Mq 
1 
w1(i), however, gives us this: 
w, 
wi(i) 
* L(Mp mMq) DL(p = Lq) 
1 1 
1 1 
0 0 
* 
* 
* 
/ 
1 
1 
1 
\p \ Mp = Mq\ 
1 ! 1 1 1 1 
I 
w6 
q 
l 
wA 
q \Mp = Mq 
l \ 11 1 11 
! * 
* 
Wn 
VV< 
\ 
p 
0 
f 
Lq Mp = Mq 
1 
81 
4 
p 
1 


A NEW INTRODUCTION TO MODAL LOGIC 
Here, in w5, we find the same situation arising as in w1, viz. the 
occurrence of a t-operator. (In fact in ws we have two t-operators, 
though we have only put a t under one of them, in accordance with a rule 
which we shall state shortly.) By [V = ] if (p = Lq) is to have the value 
0 in ws, p and Lq must have different values in w5, but the assignments 
so far do not tell us what these values are to be. So we have two cases to 
consider for p and Lq in w5, exactly as we had for Mp and Mq in w1, and 
ws will count as containing an inconsistency iff each of these leads to an 
inconsistency. We represent the two cases as follows: 
* 
i 
\p = Lq Mp = Mq\ 
0 0 11 
10 
* 
1 11 
4 
\ 
\ 
7Vq\ 
111 
I 
I 
I 
I 
Neither ws(i) nor w5(ii) leads to an inconsistency, though of course in 
order to show that ws is not inconsistent it would have been sufficient for 
one of them not to lead to an inconsistency. So if we replaced w5 by 
either w5(i) or w5(ii) in the diagram beginning with w1(i), we could use the 
diagram so obtained to construct a falsifying model for [5] and thus show 
it to be invalid. We leave the reader to verify this. 
Note that in the present case neither w5(i) nor w5(ii) contains any f-
operators, since in each case the assignments to p and Lq enable us to 
give definite values to Mp and Mq, the arguments of the other f-operator 
in w5. But if this had not happened — if, e.g., in w5(i) we had not had 
definite values for Mp and Mq — we should have put a f under the = in 
Mp = Mq in that rectangle and constructed alternatives for it, which we 
should have called (w5(i))(i) and (w5(i))(ii). In general, if t-operators 
appear for whatever reason in any rectangle, wi, we put a | under one of 
them (let us say, for the sake of having a definite rule, the leftmost one) 
and construct alternatives in the way we have described. Since wi can 
contain only a finite number of truth-functional operators, the task of 
w5(i) \p = Lq Mp = Mq\ 
1 0 0 
1 1 1 1 
* 
* 
w, 
82 
w5(ii) 
w8 
w9 
o 
1 


TESTING FOR VALIDITY 
constructing alternatives, alternatives of alternatives, and so on, of wi is 
bound to be a finite one. 
We shall now state a general rule for dealing with any t-operators that 
may occur in the construction of a diagram. It may be as well to restate 
here what a t-operator is. A t~operator in a rectangle, wl is a 
truth-functional operator which has a value beneath it in wi but whose 
arguments do not have their values determined unambiguously in wi (If 
a modal operator has a value under it but we cannot determine the value 
of its argument unambiguously, we handle the case by the rule for 
asterisks below operators, not by constructing alternative diagrams.) Note 
that if we follow strictly the practice of putting a | under only one |-
operator in any given rectangle, the largest number of alternatives we can 
have for any rectangle is 3: this will occur when the operator in question 
is V or D with 1 beneath it, or A with 0 beneath it, and the values of 
both arguments are undetermined. In other cases there will be only two 
alternatives. 
Ill Rule for alternatives 
If a rectangle, wi, contains one or more f-operators, we place a f under 
the leftmost of them. We let wi(i) and wi(ii) (or wi(i), wi(ii) and wi(iii)) be 
the two (or three) rectangles, each of which reproduces wi exactly and in 
addition contains one of the value-assignments to the arguments of the 
operator below which the f appears in wi which are compatible with the 
value under that operator. We call these rectangles the alternatives of wi, 
and beginning with each of them in turn we construct a fresh diagram. Iff 
each of these diagrams contains an inconsistency we regard wi itself as 
inconsistent. 
In each alternative of wi the initial values are all the initial values in wi 
together with the values assigned in that alternative to the arguments of 
the operator under which the f appears in wi. 
N.B. No arrows are drawn from a rectangle containing a t-operator. 
In the case of wff involving alternatives it is often a good strategy to 
postpone dealing with them for as long as possible, since sometimes 
values elsewhere in the diagram may force values to wff left open by a 
t-operator. A simple example is 
(Lp V Lq) D Lip V q) 
83 


A NEW INTRODUCTION TO MODAL LOGIC 
We know this is K-valid since it is theorem K6 on p. 34. Look at what 
happens when we test it. 
w, 
ftp V 
1 
t 
Lq) DL(p 
00 
* 
V in 
The point about this wff is that, whatever we decide to do about the V 
with a t under it, the asterisk under the L requires a world w2 accessible 
to w1 as follows: 
w, 
(Lp V Lq) DL(p V q) 
1 
00 
* 
I 
P V q 
0 0 0 
Now w1 can see w2, and both p and q are false at w2. So both Lp and Lq 
are false at w1 and we end up with the following: 
w, 
{Lp V Lq) D L(p V q)\ 
0 
1 0 
0 0 
* 
i 
P V q 
0 0 0 
In this example what has happened is that the rule for 1 under an L (the 
overstar rule) has been used contrapositively. That rule says that if you 
have an L with a 1 under it the wff that follows the L must have 1 in all 
84 


TESTING FOR VALIDITY 
accessible worlds. So if it already has 0 in an accessible world the L must 
have 0 in the original world. In the present example this leads to 
contradiction without the need for alternatives. 
S4 diagrams 
We now show how to apply the method to S4, and then to S5. The 
frames for S4 and S5 are all T-frames, though of course not all T-frames 
are S4-frames, and not all S4-frames are S5-frames. The only difference 
between our definitions of T-validity and S4-validity is that in an 
S4-model the relation R must be transitive. 
Let us apply this to the diagrams. We shall say that in a semantic 
diagram a series of rectangles w1, ... ,wn form a chain if an arrow goes 
from each (except the last) to the next rectangle in the series. Thus in the 
diagram on p. 79, w1, w2, w5 form a chain, and so do w1, w2, w6 and so 
on. To take care of the transitivity requirement, an S4-diagram will differ 
from a T-diagram in the following way: an arrow must go from every 
rectangle to every other rectangle which occurs later in every chain to 
which the first belongs. This means that to satisfy rules A and B, 
whenever in any rectangle we have La = 1 (or Mb = 0) we must now 
write a with a 1 under it (or (3 with 0 under it), not only in the next 
rectangle in the chain but in every subsequent one as well. When a 
rectangle, wj contains a t> then each alternative of wj is regarded as 
belonging to the chain to which wj belongs: thus if an arrow goes from a 
rectangle, wi, to wj, arrows must be drawn from w1 to each of wj(i), wj(ii) 
and wj(iii). 
Clearly the transitivity requirement will make no difference in the case 
of a diagram in which no chain is more than two rectangles long. When, 
however, the T-diagram for a formula contains any longer chain than this, 
there will be a difference between its T-diagram and its S4-diagram. 
Consider, e.g., the formula: 
(1) 
L{p A q) D LL(Mp D Mq) 
Its T-diagram is 
85 


A NEW INTRODUCTION TO MODAL LOGIC 
* 
L(P A q) D LL(Mp D Mq) 
1 1 1 1 0 0 
11 
* 
1 11 
I 
\ p A q 
L(Mp D Mq) 
;2 
1 1 1 
0 11 1 11 
* 
I 
* 
Up D Mq 
11 0 00 
* 
In this diagram the understarred M in w3 has been satsified in w3 itself, 
allowing the procedure to end without contradiction, and showing the 
formula to be invalid in T. But the S4-diagram of the formula is: 
* 
L(P A q) D LL{Mp D Mq) 
1 1 1 1 0 0 
11 
* 
1 11 
1 
p A q LiMp D Mq) 
1 1 1 0 11 1 11 
1 
* 
p A q 
Mp D Mq 
1 1 1 
11 0 00 
* 
Here the assignment of the value 1 to L(p A q) in w1 requires the 
presence of p A q (= 1) not merely in w2 but in w3 as well. This kind of 
addition to the contents of rectangles creates new possibilities of 
\J 
86 
w3 
w, 
w2 
w, 
w2 
w3 


TESTING FOR VALIDITY 
inconsistencies in the diagrams. When we find an inconsistency in the 
S4-diagram of a formula but not in its T-diagram, that formula is S4-valid 
but not T-valid. (1), in fact, is a case in point, as the diagrams show. 
In order to show that the method of semantic diagrams provides a 
decision procedure for S4, we have to show that for every wff an 
S4-diagram of finite length can be constructed; or more exactly, that for 
every wff, a, we can construct an S4-diagram which will in a finite 
number of steps either (a) show a to be valid (by containing an 
inconsistency in some rectangle), or (b) enable us to construct a falsifying 
S4-model for a. 
Now it was easy to show that every T-diagram is finite. For in every 
chain in a T-diagram the number of modal operators is constantly 
diminishing. Hence every chain must at worst lead us to a rectangle 
containing nothing but PC formulae, and such formulae never generate 
further rectangles. This does not, however, apply to S4-diagrams. In fact 
in S4 the following tantalizing situation can arise. Consider the formula: 
(2) 
LMp D MLp 
This is not S4-valid but its S4-diagram (by our present rules) goes like 
this: 
* 
* 
LMp 3 
MLp 
1 1 
0 00 
* 
* 
^ 
/ 
1 1 « 
| 
i 
Lp i 
oi ! 
* 
1 
p 
l 
1 
V 
vv4 
Mp\ 
10l 
* 
1 
1 
Lp • 
00 I 
i 
p 
0 
V 
\ 
^ 6 
Mp\ 
u: 
i 
Lp\ 
oi ! 
* 
i 
p 1 
1 
^ 
s 
Lp \ p 
10 " 
1 * 
I oo! 
1 
0 
V 
Mp\ Lp \ p 
u ! 
i 
0 1 ! 
* 
1 
1 
I 
87 
w, 


A NEW INTRODUCTION TO MODAL LOGIC 
Here rectangle w6 is needed because of the asterisk in w4. But an arrow 
goes from w1 to w6 as well as from w4 to w6, and as a result the contents 
of w6 turn out to be identical with those of w2; hence we need yet another 
rectangle below w6 whose content will turn out to be the same as those of 
w4 and so on for ever. And the same situation obtains on the right-hand 
side of the diagram. Thus a falsifying model for (2) always seems to be 
within our grasp at the next step, but once we take that step seems to be 
one step further on still. Yet we never strike inconsistency in the diagram 
either.2 
Clearly this diagram is not giving us a decision for (2). A simple 
modification of it, however, will do so: we delete rectangle w6 altogether, 
and run the arrow from w4 upwards to w2 instead, and we treat the other 
side of the diagram in the same way. We then have a five-world falsifying 
model for (2), as we can easily check by a truth-table. The diagram will 
be this: 
Wo 
wA 
w, 
* 
* 
LMp D MLp 
1 1 
0 00 
* 
* 
Mp 
Lp ! P 
'2 
11 
01 ; 
* 
i 
1 
0 
Mp 
Lp i p 
u 
10 
* 
00 \ ° 
Mp ; 
LP : P 
10 \ 00 1 ° 
* 
1 
* 
Mp i LP \ p 
11 ! 01 ; 
1 
* 
' 
i 
That this diagram fulfils the conditions which previously looked as if they 
would lead us to an infinite diagram, can be seen as follows: 
1. We needed a world w6 (accessible to w4) in the first diagram to 
enable the initial values to be consistently assigned to the formulae in w4. 
Since the formulae in w2 and the values assigned to them there are the 
same as those in w6, making w2 accessible to w4 is equally satisfactory. 
2. The conditions for the assignment of the initial values in w6 were 
that it in turn should be succeeded by a further world in which certain 
88 


TESTING FOR VALIDITY 
value-assignments should obtain. But since w6 is identical with w2 these 
are precisely the conditions for the initial value-assignments in w2, and we 
have already provided for their fulfilment in making w4 accessible to w2. 
In short, instead of the endless chain, w1, w2, w4, w6 ... we have w1 
followed by w2 and w4 in endless alternation; and for this we only need 
three worlds. Exactly the same considerations apply to the right-hand side 
of the diagram. In the case of the present example we can in fact do 
better than this. Since w3 and w4 are identical, and w2 and w5 are too, we 
could abandon w4 and w5 altogether, and instead draw arrows from w2 to 
w3, and from w3 to w2. We then obtain a three-world falsifying model for 
(2). Indeed by using 'optional' values in w1 we can do better still and 
produce the following diagram which gives a two-world falsifying model: 
* 
* 
LMp D MLp 
1 1 
0 00 
* 
* 
* 
Mp ' Lp 
1 
p 
10 
00 
o 
* 
1 . 
1 
(Note that this, as will appear later, is an S5-diagram as well as an S4-
diagram, and shows that (2) is invalid in S5, not only in S4.) But these 
possibilities depend on special features of (2) and we cannot generalize 
from them. We now show how to generalize this procedure to avoid 
infinite diagrams in all cases. 
We note first of all that although in the above example the contents of 
w2 were exactly the same as those of w6, it would not have mattered if w2 
had contained some extra formulae as well. So long as all the formulae 
in w6 had occurred in w2 (with the same values assigned to them), it 
would have been equally satisfactory to lead the arrow back from w4 to 
w2; for all the conditions for the consistent assignment of the required 
values in w6 would be included in those for the assignment of the values 
in w2, and by hypothesis these are fulfilled by the successors of w2 in the 
chain. When all the formulae which occur in a rectangle, wj, also occur 
in a rectangle wi with the same values assigned to them we shall say that 
89 
w, 
w4 


A NEW INTRODUCTION TO MODAL LOGIC 
wj is contained in wi. 
A further point to notice is that the distance between w2 and w6 in the 
chain (the number of intervening rectangles) was irrelevant. Even had w6 
occurred much later in the chain than it did, we could with equal 
propriety have led the arrow from its predecessor back to w2, provided of 
course that at the same time we also directed to w2 all the arrows which 
would have gone to w6. We now state the following additional rule for 
S4-diagrams. 
Rule of repeating chains 
Whenever in any chain in an S4-diagram a rectangle, wj is contained in 
a rectangle, wi, which occurs earlier in that chain, we delete wj and lead 
every arrow which would have gone to wj to wi instead. We shall call a 
chain to which we have applied this rule, a repeating chain. 
Observing the rule of repeating chains will guarantee that every chain 
in an S4-diagram is of finite length, and hence that every diagram 
contains only a finite number of rectangles, for the following reason. It 
is clear from the rules for constructing the diagrams that in the diagram 
for a wff, α, every formula which occurs in any rectangle must be a 
well-formed part of α itself. Now α has only a finite number of 
well-formed parts; and hence there can be only a finite number of sets of 
formulae selected from these, and of course only a finite number of ways 
of assigning values to the formulae in any such set. So while the contents 
of the rectangles in a chain can vary a great deal, they cannot vary 
indefinitely; therefore in an infinite chain we must sooner or later come 
across a rectangle which is contained in an earlier rectangle, and to which 
we can therefore apply the rule of repeating chains. Once we have done 
so, of course, the chain will only contain a finite number of rectangles. 
Each chain in an S4-diagram, then, is finite. Now an S4-diagram 
consists of a set of chains each beginning with wl. Each rectangle (apart 
from w1) is generated, in accordance with rules C and D on p. 76, by a 
modal operator below which an asterisk appears in the immediately 
preceding rectangle in the chain; and since each rectangle only contains 
a finite number of modal operators, there can only be a finite number of 
chains in any S4-diagram. Hence every S4-diagram contains a finite 
number of rectangles. The presence of t-operators and the consequent 
construction of alternatives cannot affect this result, for the same reason 
as in the case of T. 
90 


TESTING FOR VALIDITY 
S5-diagrams 
The method of diagrams can be extended to provide a decision procedure 
for S5. In an S5-model every world stands in the relation R to every other 
world. The extra rule that has to be observed in constructing an 
S5-diagram is therefore that an arrow must go from every rectangle to 
every other one. This means that whenever we add a new rectangle in 
constructing an S5-diagram we must draw an arrow from it to every 
rectangle already in the diagram, as well as from all other rectangles to 
it, and then enter in these rectangles any formulae which the new arrows 
make necessary. In this way the possibilities of inconsistencies arising in 
rectangles are increased — as, of course, we should expect, since a 
formula can be S5-valid without being S4-valid. 
As an illustration take the following formula: 
L(Lp V q) D (Lp V Lq) 
We shall first show that this wff is not valid in S4, and then that it is 
valid in S5: 
Wn 
W, 
* 
L(Lp V q) D (Lp VLq) 
1 0 
1 I 0 0 
* 
001 
* 
\ 
\ Lp V q 
1 1 1 0 
4 
o 
This leads to the construction of a model with three worlds, w1, w2 and 
w3 where each world can see itself and w1 can see w2 and w3, and in w2 
p is false and q is true, while in w3 p is true and q is false. (Note that 
because p is false in w2 Lp must be false in w1, and so q must be true in 
w1. The value of p in w1 does not affect the value of the whole formula.) 
The frame of this model is an S4-frame since R is transitive, but it is not 
an S5-frame since R is not symmetrical. When we make R symmetrical 
we must have w3Rw1. But then transitivity requires that w3Rw2. But Lp is 
true in w3 and this would contradict the fact that p is false in w2. The S5 
91 
w3 


A NEW INTRODUCTION TO MODAL LOGIC 
diagram would look like this: 
* L(Lp V q) D (Lp \/Lq) 
1 0 
1 l 
0 0 
* 
00 1 
* 
w2 
Lp V q 
1 1 1 0 
4 
0 
w3 
Exercises — 4 
4.1 Test each of the following wff for validity in K. If a wff is not In­
valid use the diagram to construct a falsifying K-model and then test the 
wff for validity in D. If it is not D-valid construct a falsifying D-model 
and then test the wff for validity in T. If it is not T-valid construct a 
falsifying T-model. 
(a) 
(M(p Λ q) V M(p Λ r)) D Mp 
(b) 
LqD M(pD q) 
(c) 
(M(p D p) A Lq) D M(p D q) 
(d) 
M(p D p) D ~L(Lp A L~p) 
(e) 
L(p ≡ q)D (Lp ≡ Lq) 
(f) 
L(p D L(q D r)) 3 M(q D (Lp D Mr)) 
(g) 
((LMp D MLq) Λ L(Mq D -Mr)) D M(Lp D M~r) 
(h) 
M(Lp D p) D M(p D Lp) 
(i) 
M(Mp A ~q) V L(p D Lq) 
4.2 
K. 
Show that |- α D L(β D 
γ) 
|- β D L(α D γ) is not a rule of 
4.3 Test the following wff for validity in T. If a wff is not T-valid use 
the diagram to construct a falsifying T-model and then test the wff for 
validity in S4. If it is not S4 valid construct a falsifying S4-model and 
then test the wff for validity in S5. If it is not S5-valid construct a 
falsifying S5-model. 
(a) 
L(p D Mq) D (Mp D Mq) 
(b) 
L(Lp Dq)V 
L(Lq D p) 
92 


TESTING FOR VALIDITY 
(c) 
Upmq)m 
L{Lp a Lq) 
4.4 
(a) 
Show that MLp D LMp is invalid in S4. Give a falsifying 
model. 
(b) 
Consider a frame in which R satisfies the condition that if a 
world (say w1) can see two worlds (say w2 and w3) then there must be a 
world (say w4) that both w2 and w3 can see. Show that in that case the wff 
in (a) is valid. 
(c) 
Consider a frame in which R satisfies the condition that if a 
world w1 can see two worlds w2 and w3, then either w2Rw3 or w3Rw2. 
Show that in that case 4.3(b) is valid, and that if R in addition is 
transitive then L(Lp D Lq) V L(Lq D Lp) is also valid. 
(d) 
Consider a frame in which R satisfies the condition that if a 
world w1 can see two worlds w2 and w2 then these two worlds can see 
each other. Show that E, (Mp D LMp), is valid in such a case. Use this 
fact to show that KE is weaker than S5. 
Notes 
1 Our procedure is similar in essentials to the method of semantic tableaux found 
in Kripke 1963a and elsewhere. For other decision procedures for some of the 
systems discussed in this chapter, see von Wright 1951 and Anderson 1954 
(modified in Hanson 1966). 
2 Adapting a phrase from Kripke 1963a (p. 71), we might call diagrams 
constructed in accordance with our present rules 'tree' diagrams. Thus 
LMp D MLp cannot be falsified in a finite tree diagram. In T, however, every 
invalid formula can be falsified in a finite tree diagram. In fact, as we shall show 
on p. 131 the appropriate definition of validity for S4 + LMp D MLp will 
involve frames in which every world must be able to see a world which can see 
only itself. Every finite (reflexive) tree frame satisfies this requirement, but not 
every finite reflexive transitive frame. A study of tree frames (there called 
'subordination frames') may be found in Chapter 7 of Hughes and Cresswell 
1984. 
93 


5 
CONJUNCTIVE NORMAL FORM 
We have already proved the soundness of K, D, T, S4, B and S5, and 
given an indication of how to prove the soundness of a number of other 
systems, each with respect to an appropriate class of frames. In Chapter 
6 we shall introduce a technique for proving the completeness of a 
system, that is, for proving that every valid wff is a theorem — using of 
course the definition of validity appropriate to that system. This technique 
will be very general and very powerful. It will not, however, lead to a 
decision procedure for theoremhood in the system in question; it will not, 
that is, provide us with a method whereby, given any arbitrary valid wff, 
we can show how actually to construct a proof of it in that system. Nor 
will it provide a mechanical method of establishing whether any given wff 
is valid or not. 
The method of validity testing we described in the last chapter can also 
be adapted to give a completeness proof for each of the systems we have 
mentioned, and one of a kind which will show how, given any valid wff, 
we can construct mechanically a proof of it in the relevant system. The 
details of these completeness proofs are, however, quite complicated, and 
since we can much more easily establish completeness by another more 
general method, we shall not pursue them in this book. In the special case 
of S5, however, there is available a method which yields both a 
straightforward decision procedure and an easy completeness proof, and 
the main aim of this chapter is to set out this method. 
Equivalence transformations 
In our axiomatic presentation of modal systems we have made frequent 
use of the rule of Substitution of Equivalents (Eq). This rule states that if 
94 


CONJUNCTIVE NORMAL FORM 
α is any theorem of the system in question and we form β from α by 
replacing some well-formed part of it, γ, by a wff δ, where γ ≡ δ is a 
theorem, then β is also a theorem. But when we showed on p. 32 that Eq 
is a rule of K (and of all its normal extensions) we in fact proved 
something more general than this, viz. that if α is any wff at all, theorem 
or otherwise, and we form β from it in the way described, then α ≡ β 
is a theorem. And clearly we can make any number of moves of this 
kind, and the wff with which we begin will be equivalent to the one with 
which we end; for if we have a sequence of equivalential theorems 
α1 ≡ a2 
α2 ≡ α3 
αn-l ≡ αn 
we can use the PC-tautology (p s q) D ((q ≡ r) D (p ≡ r)) as often 
as necessary to obtain α1 ≡ αn as a theorem. This process may be 
described as the performing of an equivalence transformation of α into β 
(or of α, into αn. 
The method we are about to describe will enable us to take any modal 
wff α and convert it by equivalence transformations into a wff β which 
is of a special kind, for which we shall be able to give a straightforward 
effective test for whether or not it is a theorem of S5. All the 
equivalences used in these transformations will be theorems of S5, and 
hence α ≡ β will also be a theorem of S5. 
Some of the equivalences we shall need are PC-valid wff. These 
include some of the formulae listed on p. 13 - in particular PC12—21 -
and in addition the following, which we number in sequence with them: 
PC22 
(p Λ (q V r)) ≡ ((p A q) V (p A r)) 
PC23 
(p V (q A r)) ≡ ((p V q) A (p V r)) 
[Distributive Laws—Distrib] 
We shall also need some modal equivalences, which we shall list later 
on. 
Repeated applications of the Associative Laws enable us to re-group the 
disjuncts (or conjuncts) in any purely disjunctive (or conjunctive) wff, or 
in any substitution-instance of such a wff, in any way we please. In view 
95 


A NEW INTRODUCTION TO MODAL LOGIC 
of this, it is convenient to dispense with interior bracketing in such wff, 
writing, e.g., p V q V r V s to mean that at least one of p, q, r and s 
is true, and pΛqΛrΛsto 
mean that p, q, r and s are all true. Our 
formation rules do not at present permit such expressions, so we license 
them by the definitions: 
(α V β V γ) =Df ((α V β) V γ) 
(α Λ 0 Λ γ) =Df ((a 
Λβ) 
Λγ) 
Repeated applications of Comm (together with Assoc if necessary) enable 
us to rearrange disjuncts or conjuncts in any order. 
In virtue of PC20 and PC21, any wff is equivalent to the disjunction 
(or conjunction) of itself and itself. We shall therefore when convenient 
speak of any wff at all as a disjunction or conjunction with one argument, 
or alternatively as a degenerate disjunction or conjunction. 
Conjunctive normal form 
A wff is said to be in Conjunctive Normal Form (CNF) if it is a 
conjunction (possibly degenerate), each conjunct of which is a disjunction 
(again possibly degenerate) of wff of a kind which we shall call atoms. 
By specifying the wff which are to count as atoms in varying ways we 
can define a number of different types of CNF. In the simplest type, 
which is applicable to PC wff and which we shall call PC-CNF, the atoms 
consist only of propositional variables and their negations. Thus the 
following wff are in PC-CNF: 
(1)P 
(2)p Λ (q V p) 
0)p 
V q V r 
(4)(pV ~p V q) Λ (q V r V ~r) Λ (p V r V ~r). 
Wff in PC-CNF have this important property: they are valid iff every 
conjunct contains among its disjuncts some unnegated variable and also 
the negation of that variable. Thus of the examples given above, (4) is 
valid but the others are not. 
By using the equivalences referred to in the previous section we can 
transform any wff of PC, a, into an equivalent wff, α', which is in PC-
CNF, and α is then said to be reduced to (PC-)CNF. (We shall not give 
a formal proof of this here, but to see how such a proof might run 
consider the following: All operators other than ~, V and A can be 
96 


CONJUNCTIVE NORMAL FORM 
eliminated by their definitions; the De Morgan laws can be used to ensure 
that ~ occurs only immediately before variables; and conjunctions within 
disjunctions can be transformed into disjunctions within conjunctions, or 
vice versa, by the Distributive laws.) Since α and α' are equivalent PC 
wff, each will be valid iff the other is valid. Hence, since we have given 
a mechanical validity-test for wff in PC-CNF, reduction to CNF can be 
used as an alternative decision procedure for all wff of PC. 
The type of CNF in which we are chiefly interested here, however, is 
not this, but one which is applicable to modal wff and which we shall call 
Modal Conjunctive Normal Form (MCNF).1 We define it by specifying 
as atoms all PC wff and all wff of the form Lα or Mα, where α is a PC 
wff. Thus the following wff are in MCNF: 
(p V Lp) Λ q 
(M((p V q) D r) V Lp V (r Λ s)) Λ (M(p V q) V Lr) 
but the following are not: 
(M(p V q) A r) V s 
L(M(p V q) V r) Λ {Lp V Mq) 
Now it is not immediately obvious, and for systems weaker than S5 it 
is mostly not even true, that every wff is equivalent to a wff in MCNF. 
For instance, in S4 the wff M(p Λ M~p) is not equivalent to any such 
wff.2 But in S5 every wff is equivalent to some wff in MCNF, and our 
next main task will be to prove this. As a preliminary, however, we need 
to discuss the notion of the modal degree of a wff. 
Modal functions and modal degree 
Any wff which contains a modal operator is said to be a modal function 
of its variables (just as any wff of PC is a truth-function of its variables). 
If a wff contains one or more modal operators, but none of these is within 
the scope of any other modal operator, it is said to be a modal formula 
of first degree (or a first-degree formula, or a first-degree modal function 
of its variables). In general a formula of degree n is one in which at least 
one modal operator has an argument of degree n — 1 but no modal 
operator has an argument of any higher degree than n — 1. It is convenient 
to regard wff which do not contain any modal operators as modal 
formulae of degree 0, in much the same way as we have counted — and 
~ as modalities, and a precise definition of the modal degree of a 
97 


A NEW INTRODUCTION TO MODAL LOGIC 
formula can then be given as follows (it is assumed that formulae are 
written in primitive notation):3 
1. 
A propositional variable is of degree 0. 
2. 
If α is of degree n, then ~ α is of degree n. 
3. 
If α is of degree α and β is of degree m, then if n > m, (α V 
(3) is of degree n\ otherwise it is of degree m. 
4. 
If α is of degree w, then Lα is of degree n + 1. 
The notion of a modal function of degree n is wider than that of a 
formula containing a modality with n modal operators, and should not be 
confused with it. Certainly LLp and MLp D Mq are second-degree 
formulae, and are made so by the presence in them of the modalities LL 
and ML; but M(p D Lq) is also a second-degree formula, though it 
contains no iterated modalities at all. Any formula containing a modality 
with n modal operators will be of at least degree n; but a formula can be 
of degree n (however great n may be) without containing any modalities 
with n modal operators, or indeed any iterated modalities at all. 
If a formula of degree n is equivalent in a given system to some 
formula of lower degree than n, we say that it is reducible (in that 
system) to that formula. We have already seen that in S5 any wff which 
is of higher than first degree solely because of the presence in it of 
iterated modalities can be reduced to a first-degree formula by the 
reduction laws Rl — R4. It is possible, however, to prove the following 
much stronger result: 
S5 reduction theorem 
Every formula of higher than first degree is reducible in S5 to a first-
degree formula. 
We prove this theorem by describing an effective procedure for reducing 
any wff of higher than first degree to one of first degree by equivalence 
transformations. It will be sufficient to show how any second-degree wff 
can be reduced to first degree, since repetition of the procedure will then 
enable us to deal with wff of higher degree. The only equivalences 
required are the PC equivalences referred to earlier in this chapter, the 
equivalences given by LMI, the laws of L- and M-distribution (theorems 
K3 and K6), the reduction laws R1-R4, and theorems S5(4)-S5(7), 
which we repeat here for convenience: 
S5(4) 
L(p V Lq) ≡ (Lp V Lq) 
98 


CONJUNCTIVE NORMAL FORM 
S5(5) 
L(p V Mq) ≡ (Lp V Mq) 
S5(6) 
M(p Λ Mq) ≡ (Mp Λ Mq) 
S5(7) 
M(p Λ Lq) ≡(Mp Λ Lq) 
All are of course in S5. 
The law of L-distribution (L(p A q) = (Lp A Lq)) entitles us to 
distribute L over any conjunction whatsoever. If either conjunct already 
begins with a modal operator, the appropriate reduction law will enable 
us to delete the L when it meets that operator. Thus L(p A Mq) becomes 
not merely Lp A LMq by L-distribution but Lp Λ Mq by Rl. In such a 
case we shall say that the L has been absorbed by the M. S5(4) and S5(5) 
entitle us to practise the same kind of distribution and absorption when L 
precedes a disjunction, provided that at least one of the original disjuncts 
begins with a modal operator. (S5(4) and S5(5) are stated for two-
membered disjunctions only. If we want to practise L-distribution over an 
n-membered disjunction we must gather together all but one of the 
modalized members of the disjunction and treat them as a single disjunct. 
E.g., if we haveL(p V Mq V r V Ls), we form L((p V r V Ls) V 
Mq) and then distribute to get L((p V r) V Ls) V Mq and then again to 
get L(p V r) V Ls V Mq. We do not go to Lp V Mq V Lr V Ls.) The 
law of M-distribution (M(p V q) ≡ (Mp V Mq)) and S5(6) and S5(7) 
similarly allow us to practise distribution and absorption of M 
unrestrictedly over a disjunction and, subject to the same proviso as 
before, over a conjunction. These manoeuvres are key steps in the process 
of reduction to first degree. 
As we remarked earlier, it is sufficient to show how to reduce a 
second-degree formula to a first-degree one. There are four steps in this 
procedure, though of course not all will be needed in every case. The first 
three are straightforward and should by now be familiar. 
1. We first eliminate all operators except ~ ,L,M, 
V and A by using 
the appropriate definitions. 
2. We then eliminate every occurrence of ~ immediately before a 
bracket or a modal operator by the De Morgan laws and LMI. (As a 
result ~ will be prefixed only to PC wff.) 
3. We next reduce all iterated modalities to single modalities by the 
reduction laws Rl—R4. 
4. If the formula we have as a result of steps 1 —3 is still of second 
degree, this can only be because it, or some part of it, is of the form La 
or Ma, where α is of first degree and is either a conjunction or a 
99 


A NEW INTRODUCTION TO MODAL LOGIC 
disjunction. 
We consider the case of Lα. There are three possibilities: (a) α is a 
conjunction; in that case, since L distributes unrestrictedly over 
conjunctions, we distribute L over the conjuncts in α, letting it be 
absorbed by any modal operator it meets in the process, (b) α is a 
disjunction at least one of whose disjuncts begins with a modal operator; 
in that case we again distribute L and let that operator be absorbed, (c) α 
is a disjunction none of whose disjuncts begins with a modal operator. 
Since α is of first degree, this can only be because some disjunct in α is 
a conjunction with a modal operator inside it. To handle this case we 
transform α into a conjunction by the PC distributive law ip V (q Λ r)) 
≡ ((P v q) 
A (p V r)), and distribute L over the conjunction so 
obtained. E.g., if Lα is L(p V (q A Mr)), we transform this by Distrib 
into 
L((p V q) Λ (p V Mr)) 
and then by L-distribution into 
L(p V q) Λ L(p V Mr) 
We can then either proceed as in case (b), obtaining in the example just 
cited 
L(p V q) Λ (Lp V Mr) 
or else, if this is impossible, apply Distrib and L-distribution once more. 
Repetition of these moves will always allow the L to meet each modal 
operator, no matter how deeply it is embedded in a, and be absorbed by 
it. 
The case of Mα can be dealt with analogously, except that this time it 
is when a is a conjunction none of whose conjuncts begins with a modal 
operator that we cannot proceed directly, and that the PC distributive law 
we then need is 
(p A (q V r)) = (ip Λ q) V ip Λ r)) 
(To make all this clearer we shall give one or two examples of 
reduction to first degree on p. 102.) 
Every wff, then, is equivalent in S5 to some first-degree modal 
100 


CONJUNCTIVE NORMAL FORM 
function of its variables. (This is true even of a wff containing no modal 
operators; for any wff α is equivalent to α A (Lp V ~Lp), where p is 
some variable in α.) Now it is not difficult to see that there can be only 
a finite number of distinct first-degree modal functions of any finite set 
of variables. For every first-degree formula (written in primitive notation) 
is a truth-function of (i) propositional variables and (ii) wff consisting of 
L followed by a truth-function of propositional variables; and there is only 
a finite number of non-equivalent truth-functions of any finite number of 
formulae. Hence the S5 reduction theorem shows that in S5 there are only 
a finite number of non-equivalent modal functions of any finite number 
of variables. 
It is worth noting that in showing that there are only a finite number 
of distinct first-degree modal functions of a finite number of variables we 
do not make use of any principles belonging specifically to S5; this result 
holds equally for any other normal system. Moreover it can easily be 
generalized to show that there are only a finite number of distinct modal 
functions (of a finite number of variables) of any given finite degree. 
Hence if we had a system in which, although we could not reduce every 
wff (as in S5) to first degree, yet we could reduce them all to some 
specified degree (say, fourth), that would be enough to show that in that 
system there were only a finite number of distinct modal functions of any 
finite number of variables. 
Our aim, as we mentioned earlier when we defined modal conjunctive 
form, is to prove the following: 
MCNF theorem 
Any wff can be reduced in S5 to MCNF. 
What this means is that there is an effective procedure whereby for any 
wff, a, we can find a wff, α', such that α' is in MCNF and α = α' is 
a theorem of S5. 
Proof: (i) If α is a wff of PC, it is in MCNF already. 
(ii) If α is a first-degree formula, it is a truth-function of wff each 
of which is either a PC wff or one of the form Lβ or Mβ, where β is a 
PC wff. Taking each such wff as an atom we reduce the whole formula 
to CNF by PC methods. We then replace ~Land ~M everywhere by 
M ~ and L~ respectively. The resulting formula, α', is in MCNF. 
(iii) If α is of higher than first degree, we begin by reducing it to first 
degree by the method explained above, and then obtain α' by proceeding 
as in (ii). (In fact the only further step required in such a case will be the 
101 


A NEW INTRODUCTION TO MODAL LOGIC 
application of the PC distributive law, together with Comm if necessary.) 
Since the only transformations involved are licensed by equivalences 
which are in S5, α = α' is a theorem of S5 in every case. 
We give here some examples of reduction to MCNF. These will also 
illustrate reduction to first degree. 
EXAMPLE 1 
L(MMp D p) D L{p D Lp) 
We first reduce to first degree as follows: 
Step 1: ~L(~MMp 
V p) V L(~p V Lp) 
Step 2: M~(~MMp 
V p) V L(~p V Lp) 
M(MMp Λ ~p) V L(~ p V Lp) 
Step 3: M(Mp Λ ~p) V L(~p V Lp) 
Step 4: (Mp Λ M~p) V {L~p V Lp) 
We now have a first-degree formula. To put it into MCNF we apply 
Comm and Distrib and obtain 
(Mp V L~p 
V Lp) A (M~p V L~p V Lp) 
EXAMPLE 2 
L(L(p D (q A Mr)) D ~M(p Λ ~q Λ ~ Mr)) 
We again begin by reducing to first degree. 
Step 1: L(~L(~p 
V (q Λ Mr)) V ~ M(p Λ ~ q Λ ~ Mr)) 
Step 2: L(M~(~p 
V (q Λ Mr)) V L~(p Λ ~q Λ -Mr)) 
L(M(p Λ ~ (q Λ Mr)) V L(~p V q V Mr)) 
L(M(p Λ (~q V -Mr)) V L(~p V q V Mr)) 
L(M(p Λ (~q V L~r)) 
V L(~p V q V Mr)) 
Step 4: M(p Λ (~q V L~r)) 
V L(~ p V q V Mr) 
M((p Λ ~q) V (p Λ L~r)) 
V L((~p 
V q) V Mr) 
M(p Λ ~q) V M(p Λ L~r) V L(~p V q) V Mr 
M(p Λ ~q) V (Mp Λ L~r) V L(~p V q) V Mr 
This is a first-degree formula. Comm and Distrib now give us the 
102 


CONJUNCTIVE NORMAL FORM 
following formula in MCNF: 
(Mp V M(p Λ ~q) V L(~p V q) V Mr) 
Λ (L ~ r V M(p Λ ~ q) V L(~p V q) V Mr) 
We are shortly going to formulate a test which can be applied to wff 
in MCNF. In order to make this test simpler both to formulate and to 
apply, we make the following two modifications, where necessary, in the 
way a wff in MCNF is presented: 
1. In each conjunct we use Comm to arrange the disjuncts in the 
following order: first, all unmodalized disjuncts (i.e. PC wff); next, all 
disjuncts beginning with L; finally all disjuncts beginning with M. Since 
a disjunction of PC wff is itself a PC wff, each conjunct will then have 
the form: 
β V Lγ1 V ... V Lγn V Mδ, V ... V Mδm 
where n ≥ 0, m ≥ 0. β, all the γs and all the 6s are PC wff, and of 
course there may be no unmodalized disjunct β or no L7S or no Mδs. 
2. We then use the law of M-distribution to replace Mδx V ... V Mδm 
by M(δ{ V ... V δm. Since δ,, ... ,δmare all PC wff, their disjunction 
is also a PC wff, and can be referred to simply as 6. Each conjunct is 
therefore now of the form: 
(1) β V Lγ1 V ... V Zγn V Mδ 
where 0, 7,, ... , γn and δ are all wff of PC. 
When each conjunct in a formula in MCNF is in this form, we shall 
say that the formula is in ordered MCNF. We shall assume in what 
follows that MCNF formulae are in ordered MCNF. 
Testing formulae in MCNF 
We shall now state a test which can be applied to any wff in (ordered) 
MCNF. We shall then show that this test acts as a test for whether or not 
the wff (and any wff that can be reduced to it) is (a) S5-valid and (b) a 
theorem of S5. But we shall state the test itself first. 
Every wff in MCNF is of the form 
C, Λ ... Λ Ck 
103 


A NEW INTRODUCTION TO MODAL LOGIC 
where each Ci (1 ≤ i ≤ k) is of the form (1) above. For each Ci form 
n+1 disjunctions, each of which has δ as one disjunct and a distinct one 
of β , γl, ... , γn as the other. I.e., form the n+1 PC wff (β V δ), (γ{ V 
δ), ... , (γn V δ). C; passes the test iff at least one of these is PC-valid. 
(If there is no Mb then we simply test β and γ1, ... , γn.) The whole 
MCNF C, Λ ... Λ Ck passes the test iff each conjunct in it passes the 
test. 
As illustrations we consider the two formulae we reduced to MCNF 
earlier. The MCNF formula we arrived at in Example 1 was 
(Mp V L~p 
V Lp) A (M~p V L~p V Lp) 
In ordered MCNF this becomes 
(L~p V Lp V Mp) Λ (L~p V Lp V M~p) 
This will pass the test iff each conjunct does. In the first conjunct there 
is no β, since all disjuncts are modalized, γ, is ~p, γ2 is p, and δ is also 
p. Therefore this conjunct passes the test if either ~p V p or p V p is 
PC-valid, and clearly the former is. So this conjunct passes the test. The 
second conjunct passes the test iff either ~p V ~p or p V ~P is PC-
valid, and the latter is. Thus both conjuncts pass the test, and therefore 
so does the whole formula. 
In Example 2 we reached the formula 
(Mp V M(p Λ ~q) V L(~p V q) V Mr) 
Λ (L~r V M(p Λ ~q) V L(~p V q) V Mr) 
In ordered MCNF this is 
(L(~p V q) V M(p V (p Λ ~q) V r)) 
Λ (L~r V L(~p V q) V M((p A ~q) V r)) 
The first conjunct passes the test iff (~p V q) V (p V (p Λ ~q) V r) 
is PC-valid — which it is. The second passes the test iff either ~ r V ( ( p 
Λ ~q) V r) or (~p V q) V ((p Λ ~q) V r) is PC-valid, and in fact 
both are. So once more the whole formula passes the test. 
Neither of these examples contains any unmodalized formulae, so we 
add a third example which does: 
104 


CONJUNCTIVE NORMAL FORM 
(Lq V M~p V r V L~(p A r) V ((p Λ q) D r)) 
Λ (Mp V L~p) 
In ordered MCNF the first conjunct becomes 
(r V ((p A q) D r)) V Lq V L~(p A r) V M~p 
Here β is (r V ((p Λ q) D r)), γ, is q, γ2 is ~(p Λ r), and 6 is ~ p. 
This conjunct passes the test iff at least one of (i) (r V ((p A q) D r)) 
V ~ p, (ii) q V ~ p, or (iii) ~ (p A r) V ~ p is PC-valid, and in fact 
none of them is. Hence this conjunct does not pass the test, and therefore 
neither does the whole formula (we do not need to test the other 
conjunct). 
The completeness of S5 
We want to show that reduction to MCNF, together with the test we have 
just described, gives us a completeness proof for S5 — i.e. a proof that 
every S5-valid wff is a theorem of S5. 
We have already shown that for every wff α there is a wff α' in 
ordered MCNF such that α ≡ α' is a theorem of S5; and from this it 
follows by the soundness of S5 and [V≡] that α is S5-valid iff α' is S5-
valid. Now ex' is a conjunction of wff each of which is of the form 
(1) β V Lγ, V ... V Lγn V Mδ 
where β , γ,, ... , γn and δ are all wff of PC. By [V Λ ], a conjunction is 
S5-valid iff each of its conjuncts is, and by Adj if each conjunct of α' is 
a theorem so is a'. So in order to prove the completeness of S5 it will be 
sufficient to show that every S5-valid wff of the form (1) is a theorem of 
S5; and to show this, it will clearly be sufficient to prove the following 
two things: 
A: 
Every S5-valid wff of the form (1) passes the test. 
B: 
Every wff of the form (1) which passes the test is a theorem of 
S5. 
We prove A by contraposition; i.e. we prove that if (1) does not pass 
the test then it is not S5-valid. So let us assume that (1) does not pass the 
test, i.e. that none of (β V δ), (γ, V δ), ... , (γn V δ) is PC-valid. We 
105 


A NEW INTRODUCTION TO MODAL LOGIC 
show that in that case (1) is not S5-valid by showing how to construct a 
falsifying S5 model for it. Since we are dealing solely with S5 we may 
assume that every world can see every world, and dispense with reference 
to the accessibility relation R. The model will then be this: W is to consist 
of exactly n+1 worlds, w0, wlt ... , wn. With w0 we associate (β V δ), 
and with each of w,, ... , wn we associate a distinct one of (γl V δ), ... , 
(γn v δ), as indicated by the subscript to the 7. We define V as follows. 
In w0, V makes some value-assignment to the variables which will give 
V((β V δ),w0) = 0; and in each w; among w,, ... , wn, V makes some 
assignment to the variables which will give V((Y; V δ), w i) = 0. (Since 
each of (β V δ), (γ, V δ), ... , (γn V δ) is by hypothesis an invalid PC 
wff, there will be for each of them a PC-assignment which falsifies it. We 
simply let the V in our S5 model give in w0 the values given by one which 
falsifies (β V δ), and in each withe values given by one which falsifies 
(7i V 6).) 
We now show that in such a model, V((l),w0) = 0, and therefore that 
(1) is not S5-valid. By the way we have defined V, V((β V δ),wQ) = 0. 
Hence by [V V], V(β,w0) = 0 and V(δ,w0) = 0. Similarly, for each w1 
among wlt ... ,wn, V(γi,wi) = 0 and V(δ,wi) = 0. Thus for every w G 
W, V(6,w) = 0, and hence by [VM], W(Mδ,w0) = 0. Moreover, for each 
γi among γ1, ... , γa, there is some w G W (viz. Wi) such thatV(ΓI,WI) 
= 0; and hence by [VL], V(Lγiw0) = 0 in each case. Therefore each 
disjunct in (1) has the value 0 in w0, and so by [V V ], V((l),w0) = 0. 
(If (1) contains no unmodalized disjunct β, we omit w0 from the model. 
We can then prove by the same method that for any wi G W whatever, 
V((l), Wi) = 0. If (1) contains no LγS we omit w,, ... ,wn+1. If (1) 
contains no Mb the PC-invalidity of β and each γ; will guarantee that 
V((l),w0) = 0.) 
We can illustrate the construction of a falsifying S5 model in a 
particular case by the first conjunct in our third example above, which 
turned out to be invalid. This is: 
(r V ((p Λ q) D r)) V Lq V L~(p Λ r) V M~p 
Here β is (r V ((p Λ q) D r)), γ, is q, γ2 is ~(p Λ r), and δ is ~p. 
Now 
1. (r V ((p A q) D r)) V ~p is not PC-valid and is falsified by the 
following PC-assignment V1: 
106 


CONJUNCTIVE NORMAL FORM 
V1(p) = 1, V1(q) = 1, V,(r) = 0 
2. q v ~p is not PC-valid and is falsified by the assignment: 
V2(p) = 1, V2(q) = 0, V2(r) = 1 
3. ~(p A r) V — p is not PC-valid and is falsified by the assignment: 
V3(p) = 1, V3(q) = 1, V3(r) = 1 
We therefore construct the following S5-model: W = {w0,w1,w2}. 
V(p,w0) = V1(p) = 1, V(q,w0) = V1(q) = 1, V(r,w0) = V1(r) = 0. 
V(p,w2) = V2(p) = 1, V(q,w1) = V2(q) = 0, V(r,w1) = V2(r) = 1. 
V(p,w2) = V3(p) = 1, V(qw2) = V3(q) = 1, V(r,w2) = V3(r) = 1. 
From this it is easy to show that (a) V((r V ((p Λ q) D r)),w0) = 0; 
(b) V(q,w1) = 0, and hence V(Lq,w0) = 0; (c) V(~(p Λ r),w2) = 0, and 
hence V(L~(p A r),w0) = 0; (d) V(~p,w0) = v(~p,w1) = V(~p,w2) 
= 0, and hence V(M~p,w0) 
= 0. As a result, V((r V ((p Λ q) D r)) 
V Lq V L(p A r) V Mp),w0) = 0, and so this conjunct (and therefore 
the whole conjunction) is invalid. 
This completes the proof of A. We now turn to prove B. What we 
have to prove is that if any of (β V α), (γ, V δ) , ... ,(γn V δ) is PC-
valid, then 
(1) β V Lγ1 V ... V Lγn V Mδ 
is a theorem of S5. 
Suppose that (β V δ) is PC-valid. Then by the axiom-schema PC, |-s5 
(β V δ). By Tl, S5 (δ D Mδ). Hence by (q D r) D (p V q) D (p V 
r)) and MP, f-s5 (β V Mδ); and hence by PC10 and Comm, \-S5 (1). 
The same method will apply to the degenerate case when (1) is just Mδ, 
and δ is PC-valid. 
Suppose now that one of (γ, V δ), ... , (γn V δ), say (γj V δ), is PC-
valid. Then as before, S5 (γj V δ), and so by N, |-S5 L(γj V δ). Hence 
by K9, |-S5 (Lγj V Mδ). From this it follows as before that |-S5(1). If 
there is no Mδ N alone will take us from the PC-validity of γi to 
S5 Lγi 
This completes the proof of B, and with it the proof of the 
completeness of S5. 
107 


A NEW INTRODUCTION TO MODAL LOGIC 
The completeness proof that we have given does not merely assure us 
that if α is any S5-valid wff there is in principle a proof of α in the 
axiomatic system S5; it gives us an effective procedure for constructing 
such a proof. For we can proceed as follows. We reduce α to a wff α' 
in MCNF by using S5 equivalences. We then construct the proof by first 
deriving each conjunct in α' in the way we have just described, then 
conjoining these by Adj, and finally using Eq to retrace our steps back 
through the reduction to MCNF until we reach α itself. Such a proof may 
not be the most economical or elegant that could be devised, but it will 
be a correctly constructed one nevertheless. 
A decision procedure for S5-validity 
We have shown that any wff is S5-valid iff it is a theorem of S5. It 
follows that any effective procedure for determining whether or not a wff 
is a theorem of S5 will also be an effective procedure for determining 
whether or not it is S5-valid. So if we wish to test whether any wff α is 
S5-valid, all we have to do is to reduce it to a wff α' in MCNF, and then 
check whether or not a' passes the test described on p. 104. Clearly this 
is a finite and mechanical procedure in each case. 
Triv and Ver again 
At the end of Chapter 3 we gave a proof that every normal modal system 
is contained either in Triv or in Ver, except that we postponed the proof 
of lemma 3.2, which says that every consistent extension of K which is 
not contained in Ver contains D. We can now fill in this gap. 
Let S be any system which is a consistent extension of K and has some 
theorem α which is not a theorem of Ver. We have to prove that S 
contains D; and for this it will be sufficient to show that S has some 
theorem of the form Mβ since we proved on p. 44 that every normal 
system with any theorem of that form contains D. 
Every wff of propositional modal logic is a truth-function of wff, each 
of which is either (a) a wff of PC, or (b) a wff of the form La, or (c) a 
wff of the form Ma, where in cases (b) and (c) α is a modal wff which 
may be of any degree of complexity. A little reflection on the procedure 
for reducing PC wff to PC-CNF should make it clear that by using only 
PC equivalences we can reduce any such wff to a conjunction of 
disjunctions, each disjunct in which is either a PC wff or a wff of type (b) 
or type (c) or the negation of such a wff. Moreover, having done so, we 
can use LMI to eliminate ~ in front of any negation of a wff of type (b) 
or (c), and then use Comm and M-distribution to ensure that only one wff 
108 


CONJUNCTIVE NORMAL FORM 
beginning with M occurs in any one conjunct. Let us suppose that we 
have reduced our wff a (which is a theorem of S but not of Ver) to a wff 
a' of this kind. Then a' will be a conjunction 
C1 Λ ... Λ Cn 
where each Ci is either 
(1) a wff of PC, or 
(2) a disjunction containing a disjunct of the form Lα, or 
(3) a wff of the form Ma, or 
(4) a wff of the form β V Ma, where (3 is a wff of PC. 
Now since all the equivalences we have used in reducing a to a' are in 
K, α ≡ α' is a theorem of every normal system, and hence of both S and 
Ver. So α' is a theorem of S, and hence so is each Ci; but α' is not a 
theorem of Ver, and hence at least one Ci is not a theorem of Ver. So let 
us ask, what Ci in α' could be a theorem of S but not of Ver 
(remembering that S is a consistent system)? No wff of type (1) could 
satisfy this condition; for if it is PC-valid it is a theorem of Ver, and if 
it is not PC-valid, then, as we proved on p. 47, this would mean that S 
is inconsistent. Nor can any wff of type (2) satisfy the condition, since 
every wff of the form Lα is a theorem of Ver, and therefore so is every 
disjunction in which such a wff is a disjunct. So some wff of type (3) or 
(4) must be a theorem of S. If Ma is a theorem then S has a theorem of 
the form Ma. So suppose there is some wff β V Ma in which β is a PC 
wff and β V Ma is a theorem of S. In this wff β must not be PC-valid, 
since if it were, β V Ma would be a theorem of Ver. Now we showed 
on p. 47 that every invalid wff of PC has an unsatisfiable substitution-
instance. So let us make substitutions in β V Mα to obtain a wff β* V 
Mα* in which β* is unsatisfiable. By US, β* V Mα*, and therefore ~β* 
D Mα*, is a theorem of S. But since β* is unsatisfiable, ~β* is PC-
valid, and therefore a theorem of S. Hence by MP, \-s Mα*, and so in 
this case also S has some theorem of the form Ma, which is what we had 
to prove. 
This completes the proof that every consistent extension of K is 
contained either in Triv or in Ver. 
109 


A NEW INTRODUCTION TO MODAL LOGIC 
Exercises -— 5 
5.1 
Reduce the following wff to MCNF. Where a wff passes the test 
give a sketch proof using the method described on p. 107. Where it does 
not pass the test use the method described on pp. 105-107 to construct a 
falsifying S5-model. 
(a) 
L(p V (q Λ (r V Ls))) 
(b) 
M(p Λ q) D L(L(Lp D Lq) D Mq) 
(c) 
L(pD(qDL(pD 
q))) D (~L(p 
D q) D L(p D 
~q)) 
(d) 
L(~p 
Λ 
~q) D (L(L(p V q) D r) Λ (r D L(p D p))) 
(e) 
L(p D q) D L(M(p Λ ~Lp) 
D M(q Λ L(p D Lp))) 
(f) 
L(p D L(q D r)) D {q D L(p D r)) 
(g) 
L(L(p ≡q ) D Mq) D L(L(p ≡ q) D q) 
(h) 
L(L(p D Lp) D Lp) D (MLpD 
Lp) 
(i) 
(L(L(p 
D q)Dq)Dp)D 
M(Lq D p) 
(j) 
L(L(Lp D Lq) D L(p D q)) 
5.2 
Prove that Mip Λ M~p) 
is not equivalent in S4 to any first-degree 
wff. 
Notes 
1 The name 'modal conjunctive normal form' is ours, but the idea derives from 
Carnap 1946. Carnap calls the formula in MCNF to which a wff α can be 
reduced the MP-reductum of α. In Wajsberg 1933 a slightly more complicated 
normal form is described in which each disjunct consists of L or ~L followed by 
a disjunction of variables (negated or unnegated). Schumm 1975 points out that 
Wajsberg's method has to be adapted to deal with unmodalized disjuncts. One can 
apply the method of MCNF to some systems in which reduction to first degree 
is not possible by forming a CNF whose atoms are PC wff or wff of the form Lα 
or Mα, and then reducing α to a CNF with similar atoms and so on. See Ohama 
1982. 
2 Makinson 1966a uses a generalization of this wff to show that a system 
containing S4, and therefore S4 itself, has infinitely many non-equivalent modal 
functions of a single variable, with no upper limit therefore on their modal 
degree. 
3 This definition is given in Parry 1939, p. 144. 
110 


6 
COMPLETENESS 
In this chapter we shall prove the completeness of K, D, T, S4, B and 
S5. But the technique we use will generalize to all modal systems of a 
certain class, and we shall begin by making a few remarks about systems 
and validity in general. 
The first point to note is that we can define a modal system in two 
ways, in terms of its axiomatic basis, or in terms of its theorems. For 
instance, in our discussion of the system D we showed that in place of the 
wff D, (Lp D Mp), we could have chosen M(p D p), and have obtained 
exactly the same theorems. Although it would be possible to call the two 
different ways of axiomatizing D two different systems, for most purposes 
nothing is to be gained by this, and we shall say that S and S' are the 
same system iff they have the same theorems. In fact it is convenient to 
define a system S as simply a class of wff, and then 
s a and α G S, 
are just alternative ways of saying the same thing. 
Of course not just any collection of wff of modal logic will count as a 
system. We shall, in most of this book, be interested in extensions of K. 
This class of systems is the class of what are called normal systems. A 
normal system of modal propositional logic is a class S of wff of modal 
propositional logic which contains all PC-valid wff and K, and has the 
property that if α and (3 are in S then so is anything obtainable from them 
by the use of US, MP and N. 
This means that every modal system may be expressed as K + A, 
using the notation introduced on p. 39, since A could be simply S itself. 
But typically we can choose A to be much smaller, often a single wff (or, 
what comes to the same thing, a finite set of wff — since we may always 
form the single wff which is their conjunction). 
111 


A NEW INTRODUCTION TO MODAL LOGIC 
In defining validity for a system S we have done so in terms of a class 
^"of frames. Let us use the notation ^-valid, to mean, of a wff a, that 
for every (W,R) <E r, and every model (W,R,V) based on (W,R), 
V(a,w) = 1 for every w € W. 
Where (W,R,V) is a particular model, then it is convenient to say that 
α is valid in (W,R,V) iff V(α ,w) = 1 for all w G W. We must be 
careful about this use of Valid' since, e.g., there will be models in which 
the single variable p is valid, and if we wish validity to mean truth for 
every value of the variables then validity in a model will not capture this 
in all models. Despite this, we shall speak of validity in a model, and in 
fact many of the models we shall be using will have the property that if 
α is valid in that model so is every substitution-instance of α . 
The key result of the present chapter is that for every (consistent) 
normal modal system S there is a special kind of model, called the 
canonical model of S, which has the remarkable property that a wff α is 
valid in the canonical model of S iff |-s α . 
The connection between this fact and completeness is this. Suppose that 
we have a class ^ o f frames, and we wish to show that a wff α of a 
system S is ^-valid iff J-s α . We need to show first that S is sound with 
respect to If, i.e. that every theorem of S is ^-valid. This we do by 
showing that the axioms are ^-valid, for theorem 2.1 on p. 39 then 
assures us that all the theorems will be. Now suppose that we can 
establish that the frame of the canonical model of S is in &. If α is ^ 
valid then a will be valid on the frame of the canonical model for S, and 
so a fortiori valid in the canonical model itself. But that means that f-s a. 
So if α is ^-valid then |-s α , which is what the completeness of S with 
respect to %means. 
In all of this procedure the part that is specific to each system is to 
establish that the frame of the canonical model is indeed in %. For K this 
is immediate for ^in the case of K is the class of all frames. For D, % 
is the class of serial frames and so we must show that the frame of the 
canonical model for D is serial; for T we must show that it is reflexive; 
for S4, B, S5 that it is reflexive and, respectively, transitive, 
symmetrical, and both transitive and symmetrical. 
Although establishing that the frame of the canonical model is in ^is 
sufficient to give completeness it is not necessary in that ^need not 
contain the frame of the canonical model. Indeed we shall in Part II look 
at some systems where although, as guaranteed by the results of the 
present chapter, every theorem is valid on the canonical model itself, not 
every theorem is valid on the frame of the canonical model. 
112 


COMPLETENESS 
Be all that as it may, our task is now to construct, for any system S, 
the canonical model of S. As we observed on p. 37 the worlds in a model 
can be anything we please. One very tempting candidate is to make the 
worlds sets of wff. For then we could think of a wff as true in a world iff 
that wff is in the set of wff which constitutes that world. However, if we 
do this only certain sets will be able to count as worlds. For instance, 
since any wff α is either true or false at a world, and since —α is true iff 
α is false, then the set which is that world will have to contain either α 
or ~α , but not both. And it will have to contain α V (3 iff it contains at 
least one of α and /?. Sets like this are described in the next section. 
Maximal consistent sets of wff 
Where Λ is a set of wff of modal logic we say that Λ is S-inconsistent iff 
there are α1, ... ,α n G Λ such that 
S ~(αi Λ • • • Λ αn) 
The idea is that in S you can prove that a contradiction arises from the 
members of Λ. Λ is then consistent if there is no finite collection {α1, 
...αn} Q Λ, i.e. no α„ ... , αn G Λ, such that 
s ~(α1 Λ • • • Λ αn) 
In the case of a finite set, say {β1, ... ,βk} this definition simply means 
that 
-\ s -(0, A ... A /y 
(where -| means 'not |~'). In the case of a single wff 7, {7} is consistent 
iff —I s~γ. Thus { ~ γ} is consistent iff —| s ~ ~γ, i.e. iff —| s γ. (In the 
above definitions Q is the symbol for class inclusion. Where A and B are 
any classes then A Q B iff every α in A is also in B. I.e., if α G A then 
a G B. Q and G should not be confused. One important difference is 
that A Q A for every A, while A € A is false in most set theories.) 
A set T of wff is said to be maximal iff for every wff α either a G T 
or ~α G T. T is said to be maximal consistent with respect to a system 
S (or maximal S-consistent) iff it is both maximal and S-consistent. We 
now establish a lemma which shows that in respect of the PC-operators, 
a maximal consistent set of wff does indeed look like a world, at which 
the true wff are the wff in the set. 
113 


A NEW INTRODUCTION TO MODAL LOGIC 
LEMMA 6.1 Suppose that T is any maximal consistent set of wff with 
respect to S. Then 
6. la 
for any wff α, exactly one member of {α, ~α} is in T; 
6.1b 
α 
V 0 G T iff either α G T or 0 G T; 
6.1c 
a A β G T iff a G T and β G T; 
6.1d 
if α G T and α D β G T then β G I\ 
Proof: One half of 6. la, viz. that at least one member of {α, ~α} is in 
T, is directly given by T's maximality. The other half, that they are not 
both in T, follows directly from its consistency; for if both were in T, 
then {α, ~α} would be a subset of T; but {α,~ α} is inconsistent since 
|-s ~(α A ~ a), and therefore V itself would be inconsistent. To prove 
6.1b, suppose first that α V β is in T but that neither α nor β is. Then 
by 6.1a, ~α and ~/J would both be in T, and hence {α V β, ~α, ~β} 
would be a subset of T. But this would again make T inconsistent, since 
by PC, |-s ~((α V β) Λ ~ αΛ ~β). Suppose next that one of α and 
β, say α, is in T but that α V β is not. Then {a, ~(α V β)} would be 
a subset of T. But this would make T inconsistent since 
|-s 
~(α A ~(α V (3). The proof of 6.1c is analogous using the definition 
of a A β as ~ ( ~ a V ~ β). 6.1d holds because if we had α G T, 
a D β G T but not β G T then {α,α D β, ~β} would be a subset of T. 
But this would make T inconsistent since \-s ~(α Λ (α D β) Λ ~β). 
This proves lemma 6.1. 
The next lemma illustrates an important connection between maximal 
consistent sets and theorems of S. 
LEMMA 6.2 Suppose that T is any maximal consistent set of wff with 
respect to S. Then 
6.2a if f-s α then α G T; 
6.2b if α G T and \-s α D (3 then (3 G T. 
Proof: For 6.2a, if |-s a then { ~ α} is S-inconsistent. So ~α cannot be 
in T and so α must be. 6.2b follows immediately from 6.2a and 6. Id. 
This proves lemma 6.2. 
Maximal consistent extensions 
The idea behind the kind of model we are about to construct is this. The 
worlds of the model are maximal consistent sets of wff with respect to 
114 


COMPLETENESS 
some particular system S. Lemma 6.2a guarantees that if \-s α then α is 
in every maximal consistent set of wff. But we said that the canonical 
model validates all and only theorems of S. This means that if α is not a 
theorem of S then there ought to be a maximal S-consistent set T such 
that α $. T. Now if α is not a theorem of S then {~α} is S-consistent, 
since otherwise |-s~ ~ α and so |-s α. The result we are about to prove 
guarantees that every S-consistent set A, whether finite like {~α} or 
infinite, can be extended to a maximal S-consistent set T. So if {~ «} is 
consistent then there will be a maximal consistent T such that ~α G T, 
and so, by lemma 6.1a, α £ T. 
THEOREM 6.3 
Suppose that A is an S-consistent set of wff. Then there 
is a maximal S-consistent set of wff V such that A Q T , 
Proof: Let us assume that the wff of modal propositional logic are 
arranged in some determinate order and labelled a,, α2, ... and so on. 
The idea behind the proof is that we make the set maximal by adding in 
turn every wff or its negation. We define a sequence T0, r\, ... of sets of 
wff in the following way. 
(1) 
T0 is A itself. 
(2) 
Given Tn we let Tn+1 be Tn U {an+1} if this is S-consistent and 
let Tn+1 be Tn U {~an+1} otherwise. 
(The symbol U means that where A and B are classes A U B is their 
union, the class of things in either A or B. I.e. α G A U Biffa G A 
or a G B. So in the present case T U {an+1} means T together with 
an+1, and T U {~an+1} means T together with ~αn+1.) 
We next show that, for any n, if Tn is S-consistent then so is Tn+1. The 
proof is that if Tn+1 is not S-consistent this means that neither Tn 
U {an+1} nor Tn U {~an+1} is S-consistent. This in turn means that 
there are some wff (3{, ..., /?m in Tn such that 
h ~(0, A ... A 0m A an+I) 
(i) 
and also some wff Γ1 , ..., yk in rn such that 
h ~(7i A ... A yk A ~an+1) 
(ii) 
115 


A NEW INTRODUCTION TO MODAL LOGIC 
Now from (i) and (ii) it follows by PC that 
h ~(0, A ... A pm A 7 l A ... A 7 k) 
i.e. that {β1, ... ,βm,γ1, ... ,γk} is S-inconsistent. But this is a subset of 
Tn, and therefore Tn is itself inconsistent. 
Now let T be the union of all the Tns. Then (a) T is consistent. For if 
it were not then some finite subset of T would be inconsistent. But clearly 
every finite subset of T is a subset of some Tn, and we have shown that 
no Tn is inconsistent, (b) T is maximal. For consider any wff αi By the 
construction of ri, either αi G Ti or —αi G r;; and so, since Ti Q T, 
either αi G T or —αi G T. This completes the proof of theorem 6.3. 
Consistent sets of wff in modal systems 
All the results we have proved so far depend only on the fact that S 
contains PC. They therefore hold for any system, whether modal or not, 
which contains PC. We now go on to consider features of maximal 
consistent sets which have to do with their modal properties. In particular, 
in constructing a model in which the worlds are maximal consistent sets 
of wff we will have to specify when one world is accessible from another. 
Now if a set T is to see a set A then one thing that is required is that if 
a wff β is necessary in T, i.e., if Lβ G T, then β must be true in A, ie. 
β G A. In fact we shall use this as a definition of R in the canonical 
model. We shall say that TRA iff for every wff β, if Lβ G T, then β G 
A. In order to express this more succinctly we shall introduce some new 
notation. Suppose that A is any set of wff of modal logic. Then we write 
L-(Λ ) to denote that set consisting precisely of every wff β for which Lβ 
is in A. More formally expressed: 
L-(Λ ) = {(β:Lβ G Λ } 
where {α:Lα G A} denotes the class whose members are precisely the as 
such that La G A. Using this notation we can say that TRΔ iff L-(T) Q 
A. Our next lemma will depend on the modal properties of S. Its purpose 
is the following. If ~Lα is in a set A of wff, and that set is supposed to 
represent a world in a model, there had better be a set which represents 
an accessible world, and which contains ~α. We need a guarantee that 
it will always be consistent to suppose this, and that means that we need 
to know that L~(A) is consistent with ~α. The lemma can be stated as 
follows: 
116 


COMPLETENESS 
LEMMA 6.4 
Let S be any normal system of propositional modal logic, 
and let Λ be an S-consistent set of wff containing — Lα. 
Then L_(Λ) U { ~ α} is S-consistent. 
Proof: We prove the lemma by showing that if L~(Λ) U {—α} is not 
consistent then neither is Λ. So suppose that L~(Λ) U { ~ α} is not S-
consistent. This means that there is some finite subset {β1, ... ,βn} of 
L~(Λ) such that 
h ~(0, Λ ... Λ 0n Λ ~α) 
hence by PC 
s (β1 Λ ... Λ βn) D α 
So by DR1 (p. 30) 
h £ ( 0 i Λ ... Λ jSJ DLα 
So by L-distribution (K3, p. 28) and Eq (p. 32), 
h W i Λ ... Λ Z^) 
DLα 
and finally by PC, 
h ~(L0, Λ ... Λ L0n Λ ~Lα) 
But this means that {Lβ1, ... ,Lβn, —Lα} is not S-consistent; so, since it 
is a subset of Λ, Λ is not S-consistent, which is what we had to prove. (If 
Λ should happen to contain no wff of the form L(3 then L-(Λ) would be 
empty and so if L_(Λ) U { ~ α} is not consistent then |-s α. But then by 
N 
s Lα, and so A is inconsistent in this case also.) This ends the proof. 
In conjunction with theorem 6.3 lemma 6.4 guarantees that there will 
be a maximal consistent set T such that L~(Λ) Q T and ~α € T. This 
means that for any wff 0, if L0 G A then 0 € Y so if Λ is itself 
maximal consistent then ART. 
Canonical models 
The canonical model for S is, like any other model for a normal 
propositional modal system, a triple (W,R,V). W is the set of all sets of 
117 


A NEW INTRODUCTION TO MODAL LOGIC 
maximal S-consistent sets of wff. I.e. w G W iff w is maximal S-
consistent.1 If w and w' are both in W then wRw' iff for every wff β if 
Lβ G w then β G w' - using the L- notation wRw' iff L~(w) Q w'. 
Finally we define V in the canonical model for S by stipulating that 
V(p,w) = 1 iffp G w. I.e., a variable is true in a world in the canonical 
model iff it is a member of that world, i.e., a member of that set of 
formulae. 
Given the assignment to the variables, [V ~ ], [V V ] and [VL] then give 
a value in every world to every wff. Our aim is now to show that every 
wff — not merely every variable — is true in a world in the canonical 
model iff it is a member of that world. This will have the consequence 
that s α iff α is valid in the canonical model, since, as we observed on 
p. 115, α is a theorem of S iff it is a member of every maximal S-
consistent set. So α will be a theorem of S iff it is a member of every 
world in the canonical model of S. Therefore if being a member of w is 
equivalent to being true in w then α will be a theorem of S iff it is true 
in every world in the canonical model of S, i.e. iff it is valid in the 
canonical model of S. 
In the case of the variables the V in the canonical model of S was 
defined so that a variable is true in a world iff it is a member of that 
world. In the case of other wff this has to be proved, and our next 
theorem is sometimes called the fundamental theorem for canonical 
models. 
THEOREM 6.5 
Let (W,R,V) be the canonical model for a normal 
propositional model system S. Then for any wff α and 
any w G W, V(α ,w) = 1 iff α G w. 
Proof: The result is defined to hold for the propositional variables. To 
show that it holds for all wff it will be sufficient to show the following: 
(a) If the theorem holds for α then it holds for ~a; 
(b) If the theorem holds for a and β then it holds for a V β; 
(c) If the theorem holds for a then it holds for La. 
Since every wff (in primitive notation) is made up from the variables in 
one of the ways mentioned in (a) —(c) this will show that the theorem 
holds for all wff. This style of proof is often called a proof by induction 
on the construction of a wff (or sometimes on the length of a wff).2 The 
hypothesis that the theorem holds for a (and β) is called the hypothesis 
118 


COMPLETENESS 
of the induction or the inductive hypothesis. 
As we have observed, if α is a variable the theorem holds by 
definition. We now prove each of (a)—(c) in turn. 
(a) 
Consider a wff ~α and any w E W. By [V ~ ] we have 
V(~α,w) = 1 iff V(α,w) = 0. Since the theorem is assumed to hold for 
α we have V(α,w) = 0 iff α £ w. But by lemma 6.1a, α £ w iff ~ α 
E w. Hence finally we have V(~α,w) = 1 iff ~α E was required. 
(b) 
Consider next α V β. By [ W ] we have V(α V β,w) = 1 iff 
either V(α,w) = 1 or V(β,w) = 1. Since the theorem is assumed to hold 
for a and β we therefore have V(α V β,w) = 1 iff either α E w or β 
E W. Hence by lemma 6.1b we have V( 
V β,w) = 1 iff α V β E w, 
as required. 
(c) 
Consider finally Lα. (A) Suppose that Lα E w. Then by 
definition of R we have a E w' for every w' such that wRw'. Since the 
theorem is assumed to hold for a we therefore have V(α,w') = 1 for 
every w' such that wRw'. Hence by [VL], V(Lα,w) = 1. (B) Suppose 
now that Lα £ w. Then by lemma 6.1a, ~Lα E w. Hence by lemma 
6.4, L~(w) U { ~ α} is S-consistent. So by theorem 6.3 and the definition 
of W, there is some w' E W such that L~(w) U {~ α} Q w', and 
therefore such that (i) L~(w) Q w' and (ii) ~α E w'. Now (i) gives us 
wRw', by the definition of R, and by lemma 6.1a (ii) gives us α £ w'; 
and so, since the theorem is assumed to hold for α, V(α,w') = 0. So by 
[VL] we have V(Lα,w) = 0. 
This completes the proof of theorem 6.5. 
COROLLARY 6.6. Any wff a is valid in the canonical model of S iff |-s 
α. 
Proof: Let (W,R,V) be the canonical model of S. First suppose |-s α. 
Then by lemma 6.2a α is in every maximal S-consistent set of wff. Hence 
a is in every w E W, and so, by theorem 6.5, V(α,w) = 1 for every w 
E W; i.e. α is valid in (W,R,V). Suppose now that -| s α. Then {~α} 
is S-consistent and so, by theorem 6.3 there is some maximal S-consistent 
set — i.e. some w E W — such that — α E w and hence α £ w. So by 
theorem 6.5, V(α,w) = 0. So in this case α is not valid in (W,R,V). 
The completeness of K, T, D, B, S4 and S5 
Let us take stock of the position we have now reached. We assume we 
have a normal system S and a class & of frames. To say that S is 
119 


A NEW INTRODUCTION TO MODAL LOGIC 
complete with respect to #is to say that every ^valid wff a is a theorem 
of S; where a if-valid wff is a wff that is valid on every frame in &, 
which in turn means that where (W,R,V) is any model such that (W,R) 
G &, and w is any member of W, V(α,w) = 1. Now if the frame of the 
canonical model is in if then every in valid wff is valid on that frame, and 
therefore valid in the canonical model itself. But in that case, by corollary 
6.6, that wff will be a theorem of S. 
This should make it clear that in order to prove the completeness of S 
by the canonical model method it will be sufficient to prove that the 
canonical model of S is based on a frame in £! This means that we have 
immediately a completeness result for K, since in the case of K, £* is the 
class of all frames, and the frame of the canonical model in this case is, 
trivially, in &. 
THEOREM 6.7 T is complete with respect to the class of all reflexive 
frames. 
All we have to prove is that in the canonical model for T, R is reflexive, 
i.e. for every w G W, wRw. By the definition of R in the canonical 
model this means that we must prove that for any wff a, if La G w then 
α G w. But from T and US we have |-s La D α, and so the result 
follows by lemma 6.2b. 
THEOREM 6.8 D is complete with respect to the class of all serial 
frames. 
To prove that D is complete it is sufficient to prove that R in its canonical 
model is serial. By Dl M(p D p) is a theorem of D and so, for any w in 
the canonical model of D, M(p Dp) 
G w. So, by theorem 6.5 
V(M(p D p),w) = 1. So there must be some w' such that wRw', and so 
R is serial as required. 
THEOREM 6.9 S4 is complete with respect to the class of all reflexive 
and transitive frames. 
We prove that the canonical model of S4 is based on a frame which is 
reflexive and transitive. Since S4 contains T the proof of theorem 6.7 
establishes that it is reflexive. For transitivity suppose that wRw' and 
w'Rw". To show that wRw" we must show that for any wff α, if Lα G 
w then α G w". Now f-S4 Lα D LLα, and so, by lemma 6.2b, if Lα G 
120 


COMPLETENESS 
w then LLα G w, and then since wRw', by the definition of R, Lα G w' 
and so, since w'Rw", again by the definition of R, α G w" as required. 
(Note that this proof also gives us the result that the system K4, 
mentioned on p. 64, is complete with respect to the class of transitive 
frames, whether or not R in those frames is reflexive.) 
THEOREM 6.10 
B is complete with respect to the class of all reflexive 
and symmetrical frames. 
Reflexiveness is as for T. For symmetry suppose that wRw'. To show that 
w'Rw we must show that, for any wff α, if Lα G w' then α G w. So 
suppose α 3: w. Then ~ α G w, and, since \-B ~α D L~Lα, 
by 
lemma 6.2b, L~La 
G w, and since wRw', by the definition of R, ~Lα 
G w' and so Lα & w'. (The proof also establishes that KB is complete 
with respect to the class of all symmetrical frames, whether or not they 
are reflexive.) 
THEOREM 6.11 
S5 is complete with respect to the class of all 
equivalence frames. 
The presence in S5 of T, 4 and B means that the completeness of S5 
follows from the proofs of theorems 6.7, 6.9 and 6.10. 
Triv and Ver again 
At the end of Chapter 3 we mentioned the Trivial system and the Verum 
system. What we said there has the consequence that the Trivial system 
is sound with respect to reflexive one-world frames, and the Verum 
system is sound with respect to irreflexive one-world frames (or what 
comes to the same thing, one-world frames in which the world is a dead 
end). Now in fact the frame of the canonical model for neither of these 
systems is a one-world frame. However we can show, and quite easily 
too, that every world in the frame of the canonical model of Triv can see 
itself, and itself alone, and that every world in the canonical model of Ver 
is a dead end. Clearly if α is valid on every model based on a one-world 
reflexive frame then it will be valid on a frame all of whose worlds are 
like this, and so will be valid on the frame of the canonical model of 
Triv, and so |- α similarly if α is valid on every model based on a dead 
end it will be valid in the canonical model of Ver. 
It is easy to show that the canonical model of Triv contains only 
reflexive end points (i.e. worlds which can see themselves and themselves 
121 


A NEW INTRODUCTION TO MODAL LOGIC 
alone). From f- Lp ≡ p we have \- Lp D p and so the frame is 
reflexive, so suppose that in the canonical model for Triv there is a world 
w such that wRw' but w 5≠ w'. Then there will be a wff α such that α E 
w but α i. w'. Now a E w and (-αD Lα, so Lα € w. But wRw' and 
so a E w' which is a contradiction. For Ver we note that |~Ver L(p Λ 
~p). But that can only happen at a dead end, and so every world in the 
canonical model of Ver is a dead end. Each world in the canonical model 
of Triv can be thought of as based on the one-world reflexive frame, and 
each world in the canonical model of Ver as based on the one-world dead 
end frame and so these frames respectively characterize Triv and Ver. 
When we look at Triv and Ver in this way we see why it is that they 
collapse into PC. For in one-world frames there is no way of making a 
distinction between wff which are true in one world but false in another. 
Further, since there are only two one-world frames, one in which the 
single world can see itself, and one in which it cannot, we can see why 
it is that there are only two ways in which a normal modal system can 
collapse into PC. 
Exercises — 6 
6.1 
Call T maximal consistent* iff T is consistent and for every wff α, 
if T U {α} is consistent then α E T. Prove that T is maximal consistent* 
iff T is maximal consistent as defined in this chapter. 
6.2 Prove that if T is maximal consistent then 
αDβ 
Giff 
α&T 
or β E T. 
6.3 
Let T and A both be maximal consistent. Show that if Λ T then 
A = T. 
6.4 Show that if T and A are both maximal consistent then {α:Lα £ T} 
Q Λ iff {Mα:α E Λ} c r. 
6.5 
Show that if Λ is consistent and Mα E Λ then L~(Λ) U {α} is 
consistent. 
6.6 Let wRw mean that w can see w' in n R-steps. Where S is any 
normal modal system show that in the canonical model of S wRw iff 
{α:Lnα E w} c w' 
6.7 Where S contains S4 show that if {Lγ,, ... ,Lγn,~Lβ} is S-
122 


COMPLETENESS 
consistent, so is {Lγ1, ... , L γ n , ~ β } . 
6.8 
Show that K + Mp D Lp is complete with respect to the class of 
frames in which each world can see at most one world, itself or another. 
6.9 
Let W2 be T with the additional axiom 
W2 
(p Λ q Λ M(p Λ ~q)) 
D Lp 
Show that any wff α is a theorem of W2 iff it is valid in all models in 
which every world can see at most one other world besides itself. 
6.10 Show that K + L(Lp D q) V L{Lq D p) is complete with respect 
to the class of frames in which if w1Rw2 and w1Rw3 then either w2Rw3 or 
w3Rw2. 
6.11 Show that K + p D Lp is complete with respect to the class of 
frames in which every world is either a dead end or can see only itself. 
6.12 Show that K + E is complete with respect to frames which satisfy 
the condition stated in exercise 3.11. 
6.13 Consider the class of frames in which R is replaced by a subset N 
of W and V(Lα,w) 
= 1 iff V(α,w') = 1 for every w' G N. Prove that 
K + E is characterized by frames of this kind. 
Notes 
1 The use of maximal consistent sets in proving the completeness of systems of 
modal logic goes back at least as far as Bayart 1959. Other early works are 
Kaplan 1966, Makinson 1966b and Lemmon and Scott 1977. Completeness proofs 
of a different kind are found in Kripke 1959 and 1963a. The method was 
originally used for non-modal predicate logic in Henkin 1949. 
2 Although we have not used the word 'induction' before we have used this 
method of proof in earlier chapters, for instance in our proof of Eq on p. 32 and 
in the proof of lemma 3.1 on p. 66. A proof by induction, more precisely 
mathematical induction, applies when we have a class of objects made up from 
simple parts by a finite number of steps. So, for instance, the natural numbers are 
all obtained from 0 by the successor operation, the operation of adding 1, or as 
here any wff is obtained from the primitive symbols by successive operations of 
the formation rules. If we wish to show that every member of such a class has a 
certain property it is sufficient to show that the simple members of the class have 
123 


A NEW INTRODUCTION TO MODAL LOGIC 
it, and that anything made up from members which have the property also has the 
property. Other examples of inductive proofs are in soundness proofs such as that 
for K on pp. 39-41. 
124 


