A NEW INTRODUCTION 
TO MODAL LOGIC 


A NEW INTRODUCTION 
TO 
MODAL LOGIC 
G. E. Hughes 
Late Professor of Philosophy 
Victoria University of Wellington 
M. J. Cresswell 
Professor of Philosophy 
Victoria University of Wellington 
London and New York 


First Published 1996 
by Routledge 
2 Park Square, Milton Park, Abingdon, Oxon, 0X14 4RN 
Simultaneously published in the USA and Canada 
by Routledge 
270 Madison Ave, New York NY 10016 
Reprinted 1998. 200! 
Transferred to Digital Printing 2005 
Routledge is an imprint of the Taylor & Francis Group 
©1996 M.J. Cresswell and the estate of G.E. Hughes 
Typeset in Times by M.J. Cresswell 
All rights reserved. No part of this book may be reprinted or 
reproduced or utilized in any form or by any electronic, 
mechanical, or other means, now known or hereafter 
invented, including photocopying and recording, or in any 
information storage or retrieval system, without permission in 
writing from the publishers. 
British Library Cataloguing in Publication Data 
A catalogue record for this book is available from the British Library. 
Library of Congress Cataloguing in Publication Data 
A catalogue record for this book has been requested. 
ISBN 0-415-12599-5 (hbk) 
ISBN 0-415-12600-2 (pbk) 


CONTENTS 
Preface 
ix 
Part One: Basic Modal Propositional Logic 
1 The Basic Notions 
3 
The language of PC (3) Interpretation (4) Further operators (6) 
Interpretation of A , D and ≡ (7) Validity (8) Testing for validity: (i) the 
truth-table method (10) Testing for validity: (ii) the Reductio method (11) 
Some valid wff of PC (13) Basic modal notions (13) The language of 
propositional modal logic (16) Validity in propositional modal logic (17) 
Exercises — 1 (21) Notes (22) 
2 The Systems K, T and D 
23 
Systems of modal logic (23) The system K (24) Proofs of theorems (26) 
L and M (33) Validity and soundness (36) The system T (41) A definition 
of validity for T (43) The system D (43) A note on derived rules (45) 
Consistency (46) Constant wff (47) Exercises — 2 (48) Notes (49) 
3 The Systems S4, S5, B, Triv and Ver 
51 
Iterated modalities (51) The system S4 (53) Modalities in S4 (54) Validity 
for S4 (56) The system S5 (58) Modalities in S5 (59) Validity for S5 (60) 
The Brouwerian system (62) Validity for B (63) Some other systems (64) 
Collapsing into PC (64) Exercises — 3 (68) Notes (70) 
4 Testing for validity 
72 
Semantic diagrams (73) Alternatives in a diagram (80) S4 diagrams (85) 
S5-diagrams (91) Exercises — 4 (92) Notes (93) 
v 


A NEW INTRODUCTION TO MODAL LOGIC 
5 Conjunctive Normal Form 
94 
Equivalence transformations (94) Conjunctive normal form (96) Modal 
functions and modal degree (97) S5 reduction theorem (98) MCNF 
theorem (101) Testing formulae in MCNF (103) The completeness of S5 
(105) A decision procedure for S5-validity (108) Triv and Ver again (108) 
Exercises — 5 (110) Notes (110) 
6 Completeness 
111 
Maximal consistent sets of wff (113) Maximal consistent extensions (114) 
Consistent sets of wff in modal systems (116) Canonical models (117) The 
completeness of K, T, B, S4 and S5 (119) Triv and Ver again (121) 
Exercises — 6 (122) Notes (123) 
Part Two: Normal Modal Systems 
7 Canonical Models 
127 
Temporal interpretations of modal logic (127) Ending time (131) 
Convergence (134) The frames of canonical models (136) A non-canonical 
system (139) Exercises — 7 (141) Notes (142) 
8 Finite Models 
145 
The finite model property (145) Establishing the finite model property 
(145) The completeness of KW (150) Decidability (152) Systems without 
the finite model property (153) Exercises — 8 (156) Notes (156) 
9 Incompleteness 
159 
Frames and models (159) An incomplete modal system (160) KH and KW 
(164) Completeness and the finite model property (165) General frames 
(166) What might we understand by incompleteness? (168) Exercises — 
9 (169) Notes (170) 
10 
Frames and Systems 
172 
Frames for T, S4, B and S5 (172) Irreflexiveness (176) Compactness 
(177) S4.3.1 (179) First-order definability (181) Second-order logic (188) 
Exercises — 10 (189) Notes (190) 
vi 


CONTENTS 
11 
Strict Implication 
193 
Historical preamble (193) The 'paradoxes of implication' (194) Material 
and strict implication (195) The 'Lewis' systems (197) The system SI 
(198) Lemmon's basis for SI (199) The system S2 (200) The system S3 
(200) Validity in S2 and S3 (201) Entailment (202) Exercises — 11 (205) 
Notes (206) 
12 
Glimpses Beyond 
210 
Axiomatic PC (210) Natural deduction (211) Multiply modal logics (217) 
The expressive power of multi-modal logics (219) Propositional symbols 
(220) Dynamic logic (220) Neighbourhood semantics (221) Intermediate 
logics (224) 'Syntactical' approaches to modality (225) Probabilistic 
semantics (227) Algebraic semantics (229) Exercises — 12 (229) Notes 
(230) 
Part Three: Modal Predicate Logic 
13 
The Lower Predicate Calculus 
235 
Primitive symbols and formation rules of non-modal LPC (235) 
Interpretation (237) The Principle of replacement (240) Axiomatization 
(241) Some theorems of LPC (242) Modal LPC (243) Semantics for 
modal LPC (243) Systems of modal predicate logic (244) Theorems of 
modal LPC (244) Validity and soundness (247) De re and de dicto (250) 
Exercises — 13 (254) Notes (255) 
14 
The Completeness of Modal LPC 
256 
Canonical models for Modal LPC (256) Completeness in modal LPC 
(262) Incompleteness (265) Other incompleteness results (270) The 
monadic modal LPC (271) Exercises — 14 (272) Notes (272) 
15 
Expanding Domains 
274 
Validity without the Barcan Formula (274) Undefined formulae (277) 
Canonical models without BF (280) Completeness (282) Incompleteness 
without the Barcan Formula (283) LPC + S4.4 (S4.9) (283) Exercises — 
15 (287) Notes (287) 
vii 


A NEW INTRODUCTION TO MODAL LOGIC 
16 
Modality and Existence 
289 
Changing domains (289) The existence predicate (292) Axiomatization of 
systems with an existence predicate (293) Completeness for existence 
predicates (296) Incompleteness (302) Expanding languages (302) 
Possibilist quantification revisited (303) Kripke-style systems (304) 
Completeness of Kripke-style systems (306) Exercises — 16 (309) Notes 
(310) 
17 
Identity and Descriptions 
312 
Identity in LPC (312) Soundness and completeness (314) Definite 
descriptions (318) Descriptions and scope (323) Individual constants and 
function symbols (327) Exercises — 17 (328) Notes (329) 
18 
Intensional Objects 
330 
Contingent identity (330) Contingent identity systems (334) Quantifying 
over all intensional objects (335) Intensional objects and descriptions (342) 
Intensional predicates (344) Exercises — 18 (347) Notes (348) 
19 Further Issues 
349 
First-order modal theories (349) Multiple indexing (350) Counterpart 
theory (353) Counterparts or intensional objects? (357) Notes (358) 
Axioms, Rules and Systems 
359 
Axioms for normal systems (359) Some normal systems (361) Non-
normal systems (363) Modal predicate logic (365) Table I: Normal Modal 
Systems (367) Table II: Non-normal Modal Systems (368) 
Solutions to Selected Exercises 
369 
Bibliography 
384 
Index 
398 
V l l l 


PREFACE 
Modal logic is the logic of necessity and possibility, of 'must be' and 'may 
be'. By this is meant that it considers not only truth and falsity applied to 
what is or is not so as tilings actually stand, but considers what would be 
so if tilings were different. If we think of how tilings are as the actual world 
then we may think of how tilings might have been as how tilings are in an 
alternative, non-actual but possible, state of affairs - or possible world. 
Logic is concerned with truth and falsity, In modal logic we are concerned 
with truth or falsity in other possible worlds as well as the real one. hi this 
sense a proposition will be necessary in a world if it is true in all worlds 
which are possible relative to that world, and possible in a world if it is true 
in at least one world possible relative to that world. All this is explained in 
the first chapter of this book. 
Our ami in this book is to introduce readers to modal logic, and we 
assume that to begin with the reader knows nothing of modal logic. We 
have attempted to make the book self contained so that it could even be 
tackled by someone who had not studied any logic at all. However, we 
anticipate that most readers will already know a little about the (non-modal) 
propositional and predicate calculi, and will be able to use this knowledge 
as a foundation for understanding modal logic. 
This book is intended as a replacement for our earlier two books An 
Introduction to Modal Logic (Hughes and Cresswell, 1968, IML) and A 
Companion to Modal Logic (Hughes and Cresswell, 1984, CML) and we 
shall here say a little about the relation between it and the earlier books. 
Part I covers most of the ground covered in IML with two important 
changes. First, as in CML, we take the system K as basic rather than T. 
Second, as also in CML, we have (in Chapter 6) used the method of 
canonical models to prove completeness. We have retained (in Chapter 5) 
the method of modal conjunctive normal forms to prove the completeness 
of S5, but while (in Chapter 4) we have retained from IML the method of 
semantic diagrams for testing formulae, we have omitted the completeness 
proofs based on this method. 
Part II covers a range of topics in modal propositional logic, most of 
which are also discussed in CML. In the present work we have attempted 
to be particularly sensitive to its role as an introduction. Thus, to take one 
ix 


A NEW INTRODUCTION TO MODAL LOGIC 
example, our approach to finite models is one that we believe is easier to 
follow than the more standard method of filtrations which we used in CML. 
Although this part of the book may be seen as more of interest to specialists 
we have tried to present its topics in a way which should be easily 
accessible to the reader who has followed Part I. Part III of IML contained 
a survey of modal logic as it was in 1968. A comparable survey would be 
impossible today but we have attempted, in Chapter 11 of the present book, 
to give an outline of the more important developments in the earlier history 
of modal logic. Readers who need more may be referred to IML. 
Part III was the most difficult to write. Modal predicate logic is rightly 
regarded as the most philosophically important branch of modal logic, and 
although this is a book on fonnal logic not philosophical logic, we have 
attempted to discuss topics which have a bearing on such important 
philosophical questions as what to say about things which exist in one world 
but not another or about things claimed to be identical but not necessarily 
so. Unfortunately, the semantics of modal predicate logic is extremely 
complicated, and while we have tried to make our discussions as 
approachable as we can, we are conscious of the burden imposed on the 
reader. All we can say is that we have attempted to set out all technical 
material so that with patience a reader should be able to follow every proof 
without requiring more than is in this book. 
George Hughes died on 4 March 1994. At the time of his death we had 
completed the first five chapters. Chapter 6 and most of Part II has been 
adapted from CML, and we had discussed many issues in that area. In 
preparing the manuscript I have endeavoured, to the best of my ability, to 
write it as a joint work and present it in a style as close as I can to what 
would have emerged had George Hughes lived to see its completion. It is 
in Part III that I have felt the greatest lack of his collaboration, and I am 
grateful especially to Rob Goldblatt and Edwin Mares here in Wellington 
who have looked at and commented on many passages. We would also 
thank various readers, and colleagues from around the world, whose 'wish 
lists' we have not always been able to take as much note of as they would 
like. 
Our department secretary, Debbie Luyinda, put the initial manuscript into 
the computer, so that we could then play with it, and we would thank her 
for this, at times frustrating, work. 
Wellington, New Zealand 
January 1995 
x 


Part I 
BASIC MODAL 
PROPOSITIONAL 
LOGIC 


1 
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
