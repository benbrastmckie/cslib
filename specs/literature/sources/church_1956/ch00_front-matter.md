<!-- Source: Church, A. (1956). Introduction to Mathematical Logic. Front matter (title page, errata, table of contents). BibKey: Church1956 -->

# Introduction to Mathematical Logic

**Alonzo Church (1956)**


---


INTRODUCTION TO MATHEMATICAL LOGIC

---


VOLUM E I
INTRODUCTION TO 
MATHEMATICAL 
LOGIC
BY ALONZO CHURCH
PRINCETON, NEW JERSEY 
PRINCETON UNIVERSITY PRESS
1956

---


PUBLISHED 1956, BY PRINCETON UNIVERSITY PRESS
ISBN 0-691-07984-6
Sixth Printing, 1970
PRINTED IN THE UNITED STATES OF AMERICA

---


Errata
On page 66, in line 12, read: “Else there will be simple elementary true 
propositions . .
On page 142 it should have been pointed out that Wajsberg’s paper, cited 
in footnote 211, contains an error that is not easily set right. However, the 
metatheorem that is stated in the next-to-last paragraph of the text on page 
142, and a similar metatheorem for the formulation Fu of intuitionistic func­
tional calculus of first order, were proved by Curry in the Bulletin of the 
American Mathematical Society, vol. 45 (1939), pp. 288-293, and the proof 
is reproduced by Klcene in Introduction to Metamathematics.—Since Curry’s 
proof depends on Gentzen’s Hauptsatz for L/, the remark should be made 
that it is not the use of Gentzen’s Sequenzen but the Hauptsatz itself that ts 
essential, as the Sequenzen can of course be eliminated by the definitions on 
page 165 (with m =  1 for the intuitionistic case), and the Hauptsatz therefore 
proved in a form that is directly applicable to formulations of the ordinary 
kind without Sequenzen (compare Curry, loc. cit., and Kurt Schiitte in the 
Matkematische Annalen, vol. 122 (1950), pp. 47-65).
On page 150, the parenthetic explanation at the end of the statement of the 
metatheorem **272 must be changed to read as follows: “(i.t., every applica­
tion of the rule of substitution is one of a chain of successive substitutions 
that are applied to one of the axioms of Pa).”
On page 171, add after line 2: “These substitution notations will be used 
not only when T r r if r 2, . . 
r n are well-formed formulas, but when they 
are formulas consisting of variables or constants standing alone, and even 
possibly in other cases also. The condition that A shall be well-formed must 
be retained, at least in the case of the dotted S.“
On page 257, in connection with case X of the decision problem, it should 
have been pointed out that this case covers only a finite number of wffs that 
differ otherwise than by alphabetic changes of bound variable or transforma­
tions of the matrix by propositional calculus or both. This detracts somewhat 
from the interest of the case, as the decision problem of a finite class of wffs 
is always solvable in principle, by the trivial procedure of listing the valid

---


E R R A T A
and invalid formulas in the class. But in case X the finite number is large, 
and there is still an interest in finding a practicable decision procedure.
On page 269, after the word “which” at the end of line 11, insert the words 
“the premisses are inconsistent, as well as cases in which”; for although exer­
cise 46.22 is deliberately stated in such a way that some additional valid in­
ferences will be found, beyond the traditional categorical syllogisms, there is 
no point in including the inferences which are valid only because the premisses 
are inconsistent.
On page 299, replace the words “those of F*r” at the beginning of line 20, 
by “all variants, of the axioms of F
On page 335, the definition which is given in 55.14 requires the further 
condition that there is either at least one 0  or at least one 1 among the signs 
ai, a*, ■ • • , a*. For otherwise f(aa, a2, . . . , art) is already a wff, and may not 
without confusion be used to abbreviate another wff.
On page 336, the writer is indebted to Hugues Leblanc for pointing out that 
the results asserted in 55.16 and 55.18(1) are erroneous. The exercises may 
profitably be amended by asking the reader in each case to show the opposite, 
given the consistency of A0 and A;, given that completeness as to provability 
fails (compare the remark on page 329), and making use of **453 for A0 and 
48.7 for A'.
On page 352, in the seventh line of footnote 581, insert the word “are” before 
“added.”

---


Preface
This is a revised and much enlarged edition of Introduction to Mathematical 
Logic, Part 7, which was published in 1944 as one of the Annals of Mathe­
matics Studies. In spite of extensive additions, it remains an introduction 
rather than a comprehensive treatise. It is intended to be used as a textbook 
by students of m athem atics, and also within limitations as a reference work. 
As a textbook it offers a  beginning course in mathem atical logic, but 
presupposes som e substantial mathem atical background.
An added feature in the new edition is the inclusion of many exercises 
for the student. Som e of these are of elementary character, straightforward 
illustrations serving the purpose of practice; others are in effect brief sket­
ches of difficult developm ents to which whole sections of the main text might 
have been devoted; and still others occupy various intermediate positions 
between these extremes. No attem pt has been made to classify exercises 
system atically according to difficulty. But for routine use by beginning 
students the following list is tentatively suggested as a basis for selection:
12.3- 12.9, 14,0-14.8, 15.0-15,3, 15.9, 15.10, 18.0-18.3, 19.0-19.7, 19.9, 
10,10, 23.1-23.6, 24.0-24.5, 30.0-30.4 (with assistance if necessary), 34.0,
34.3- 34.6, 35.1, 35.2, 38.0-38.5, 39.0, 41.0, 43.0, 43.1, 43.4, 45.0, 45.1, 
48.0-48.11, 52.0, 52.1, 54.2-54.6, 55.1, 55.2, 55.22, 56.0-56.2, 57.0-57.2.
The book has been cut off rather abruptly in the middle, in order that 
Volume I m ay be published, and at m any places there are references forward 
to passages in the still unwritten Volume II. In order to make clear at least 
the general intent of such references, a tentative table of contents of Volume 
II has been added at the end of the table of contents of the present volume, 
and references to Volume II should be understood in the light of this.
Volume I has been written over a period of years, beginning in 1947, 
and as portions of the work were completed they were made available in 
manuscript form in the Fine Hall Library of Princeton University. The work 
was carried on during regular leave of absence from Princeton University 
from September, 1947, to February 1, 1948, and then under a contract of 
Princeton U niversity with the U nited States Office of N aval Research from 
February 1 to June 30,1948. To this period should be credited the Introduc­
tion and Chapters I and II —  although some minor changes have been made

---


VI
PREFACE
in this m aterial since then, including the addition of exercises 15.4, 18.3, 
19.12, 24.10, 26.3(2), 26.3(3), 26.8, 29.2, 29.3, 29.4, 29.5, as well as changes 
designed to correct errors or to take into account new ly published papers. 
The remainder of the work was done during 1948-1951 with the aid of 
grants from the Scientific Research Fund of Princeton U niversity and the 
Eugene H iggins Trust Fund, and credit is due to these Funds for m aking 
possible the writing of the latter half of the volum e.
For individual assistance, I am indebted still to the persons nam ed in 
the Preface of the edition of 1944, especially to C, A. Truesdell —  whose 
notes on the lectures of 1943 have continued to be of great value, both in the 
writing of Volume I and in the preliminary work which has been done towards 
the writing of Volume II, and notwithstanding the extensive changes which 
have been m ade from the content and plan of the original lectures. I am 
also indebted to m any who have read the new m anuscript or parts of it and 
have supplied valuable suggestions and corrections, including especially 
E. Adler, A. F. Bausch, W. W. Boone, Leon Henkin, J. G. Kem eny, Maurice 
L'Abbe, E. A. Maier, Paul Meier, I. L. Novak, and Rulon Wells.
Alonzo Church
Princeton,, New Jersey 
August 31, 1951
(Added November 28, 1955.) For suggestions which could be taken into 
account only in the proof I am indebted further to A . N. Prior, T. T. R obin­
son, H artley Rogers, Jr., J. C. Shepherdson, F. 0 . W yse, and G. Zubieta 
Russi; for assistance in the reading of the proof itself, to Michael Rabin and 
to Zubieta; and especially for their important contribution in preparing the 
indexes, to Robinson and Zubieta.
(Added January IT, 1958.) In the second printing, additional corrections 
which were necessary have been made in the text as far as possible, and those 
which could not be fitted into the text have been included in a list of Errata 
at the end of the book. For some of these corrections I am indebted to Max 
Black. S. C. Kleene, E. J. Lemmon, Walter Stuermann, John van Heijenoort; 
for the observation that exercise 55.3(3) would be better placed as 55.2(3). 
to D. S. Geiger; and for important corrections to 38.8(10) and footnote 550, 
to E. \Y. Beth. For assistance in connection with Wajsberg’s paper (see the 
correction to page 142) I am further indebted to T. T. Robinson.
A l o n z o  C h u r c h

---


Contents
PREFACE...........................................................................................................
V
INTRO DUCTIO N..........................................................................................
I
00.
Logic...........................................................................................................
1
01.
N a m e s ........................................... ...........................................................
3
02.
Constants and varia b les....................................................................
9
03.
Functions..................................................................................................
15
04.
Propositions and propositional functions......................................
23
05.
Improper symbols, connectives.......................................................
31
06.
Operators, quantifiers 
.........................................................................
39
07.
The logistic m eth o d .............................................................................
47
08.
S y n ta x ............................................................ ..........................................
58
09.
Semantics...................................................................................................
64
CHAPTER I. 
The Propositional C alculus...........................................
69
10.
The primitive basis of Px....................................................................
69
11.
D efin itio n s..............................................................................................
74
12.
Theorems of Px .....................................................................................
SI
Exercises 12..........................................................................................
85
13.
The deduction th eo rem .....................................................................
86
14.
Some further theorems and metatheorems of Px .....................
91
Exercises 14..........................................................................................
93
15.
Tautologies, the decision problem ...................................................
94
Exercises 15.........................................................................................
102
16.
D uality.......................................................................................................
106
17.
C onsistency..............................................................................................
108
18.
C om pleteness..........................................................................................
109
Exercises 18..........................................................................................
111
19.
Independence..........................................................................................
112
Exercises 19.........................................................................................
115
CHAPTER II. 
The Propositional Calculus (Continued).................
119
20.
The primitive basis of P2....................................................................
119
21.
The deduction theorem for P2
.......................................................
120

---


viu
TABLE OF CONTENTS
22.
Some further theorems and metatheorems of Pa . . . . .  .
121
23.
Relationship of Pa to Px ...................................................................
125
Exercises 23. . . . . . . .  ......................................
128
24.
Primitive connectives for the propositional calculus . . . . .
129
Exercises 24. ............................................. .....................................
134
25.
Other formulations of the propositional calculus . . . . . .
136
Exercises 25........................................................................................
138
26.
Partial systems of propositional calculus......................................
140
Exercises 26. . . ...........................................................................
143
27.
Formulations employing axiom schemata. ..................................
148
28.
Extended propositional calculus and p rototh etic.....................
151
Exercises 28................................. ......................................................
154
29.
Historical notes ....................................................................................
155
Exercises 2 9 . ...................................................................................
166
CHAPTER III. 
Functional Calculi of First O rder.........................
168
30.
The primitive basis of F1..................................................................
169
Exercises 30................................................. .....................................
176
31.
Propositional calculus . ...........................................................
178
32.
Consistency of F1 ...............................................................................
180
33.
Some theorem schemata of F1
..........................................
186
34.
Substitutivity of equivalence . 
.......................................................
189
Exercises 3 4 ......................................................
191
35.
Deriyed rules of substitution...........................................................
191
Exercises 35 
. ................................................................................
195
36.
The deduction theorem. ...................................................................
196
37.
Duality....................................................................................................
201
38.
Some further theorem schemata.......................................................
205
Exercises 38. . . .  ........................................................................
206
39.
Prenex normal form ..................................................
209
Exercises 39.......................................................................
212
CHAPTER IV. 
The Pure Functional Calculus of First Order . .
218
40.
An alternative formulation ...................................... ........................
218
Exercises 40. . . .  ........................................................................
220
41.
Independence............................. ..........................................................
220
Exercises 41.......................................................... .... .....................
223
42.
Skolem normal form ............................................................... ....
224
43.
Validity and satisfiability...................................................................
227
Exercises 43.......................................................................
231

---


TABLE OF CONTENTS 
ix
44.
Godel's completeness theorem...........................................................
233
45.
Lowenheim's theorem and Skolem's generalization.................
238
Exercises 45.........................................................................................
245
46.
The decision problem, solution in special cases.........................
246
Exercises 46.....................................................................................-
257
47.
Reductions of the decision problem ..............................................
270
Exercises 47........................................................... .............................
280
48.
Functional calculus of first order with equality. . . . . . .
280
Exercises 48. ,
................................................................................
CJ
00
<M
49.
Historical n o te s ................................................................................ .
288
CHAPTER V. 
Functional Calculi of Second Order.........................
295
50.
The primitive basis of F*..................................................
295
51.
Propositional calculus and laws of q u an tifiers.........................
297
52.
E q u a lity .................................................................................................
300
Exercises 52........................................................................................
302
53.
Consistency of F \ ...................................... ....
306
54.
Henkin’s completeness theorem .......................................... ....
307
Exercises 54............................................................................
315
55.
Postulate theory...................................... .............................................
317
Exercises 55.................................................................................... .
56.
Well-ordering of the individuals.......................................................
341
Exercises 56. . . . . . . . .  .........................
342
57.
Axiom of in fin ity ................................................................................
342
Exercises 57. . . . . . .  ...................................... ....
345
58.
The predicative and ramified functional calculi of second order
346
Exercises 58................................................................... .....................
354
59.
Axioms of reducibility........................................................................
354
Exercises 59........................................................................................
356
INDEX OF D E F IN IT IO N S ...................................................................
357
INDEX OF AUTHORS CITED...............................................................
373
E R R A T A .........................................................................................................
377

---


TENTATIVE TABLE OF CONTENTS OF VOLUME TWO
CHAPTER VI.
Functional Calculi of Higher Order.
CHAPTER VII.
Second Order Arithmetic. (The Logistic System AK)
CHAPTER VIII.
GodeTs Incompleteness Theorems.
CHAPTER IX.
Recursive Arithmetic.
CHAPTER X.
An Alternative Formulation of the Simple Theory of 
Types.
CHAPTER XI.
Axiomatic Set Theory.
CHAPTER XII.
Mathematical Intuitionism.

---


