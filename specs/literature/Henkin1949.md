## Page 1

The Completeness of the First-Order Functional Calculus
Author(s): Leon Henkin
Source: The Journal of Symbolic Logic, Vol. 14, No. 3 (Sep., 1949), pp. 159-166
Published by: Association for Symbolic Logic
Stable URL: http://www.jstor.org/stable/2267044 .
Accessed: 23/09/2014 10:38
Your use of the JSTOR archive indicates your acceptance of the Terms & Conditions of Use, available at .
http://www.jstor.org/page/info/about/policies/terms.jsp
 .
JSTOR is a not-for-profit service that helps scholars, researchers, and students discover, use, and build upon a wide range of
content in a trusted digital archive. We use information technology and tools to increase productivity and facilitate new forms
of scholarship. For more information about JSTOR, please contact support@jstor.org.
 .
Association for Symbolic Logic is collaborating with JSTOR to digitize, preserve and extend access to The
Journal of Symbolic Logic.
http://www.jstor.org 
This content downloaded from 195.113.26.195 on Tue, 23 Sep 2014 10:38:19 AM
All use subject to JSTOR Terms and Conditions


## Page 2

THE 
JOURNAL 
OF SYMBOLTC LOGIC 
Volume 14, Number 3, Sept. 1949 
THE COMPLETENESS OF THE FIRST-ORDER FUNCTIONAL CALCULUS 
LEON 
HENKIN' 
Although several proofs have been published showing the completeness of the 
propositional calculus (cf. Quine (1)2), for the first-order 
functional calculus only 
the original completeness proof of G6del (2) and a variant due to Hilbert and 
Bernays have appeared. Aside from novelty and the fact that it requires less 
formal development of the system from the axioms, the new method of proof 
which is the subject of this paper possesses two advantages. In the first place 
an important property of formal systems which is associated with completeness 
can now be generalized to systems containing a non-denumerable 
infinity of 
primitive symbols. While this is not of especial interest when formal systems 
are considered as logics-i.e., as means for analyzing the structure 
of languages- 
it leads to interesting 
applications in the field of abstract algebra. In the second 
place the proof suggests a new approach to the problem of completeness for 
functional calculi of higher order. Both of these matters will be taken up in 
future papers. 
The system with which we shall deal here will contain as primitive symbols 
( 
) 
D 
f, 
and certain sets of symbols as follows: 
(i) propositional 
symbols (some of which may be classed as variables, others as 
constants), 
and among which the symbol "f" above is to be included as a 
constant; 
(ii) for each number n = 1, 2, * a set of functional 
symbols 
of degree n (which 
again may be separated into variables and constants); and 
(iii) individual symbols 
among which variables must be distinguished 
from con- 
stants. The set of variables must be infinite. 
Elementary 
well-formed 
formulas are the propositional symbols and all formulas 
of the form G(xi, - - *, Xn) where G is a functional symbol of degree n and each 
xi is an individual symbol. 
Well-formed 
formulas (wffs) consist of the elementary 
well-formed 
formulas to- 
gether with all formulas built up from them by repeated application of the follow- 
ing methods: 
(i) If A and B are wffs so is (A D B); 
(ii) If A is a wif and x an individual variable then (x)A is a wif. Method (ii) 
for forming 
wffs is called quantification 
with respect to the variable x. Any occur- 
rence of the variable x in the formula (x)A is called bound. Any occurrence of 
a symbol which is not a bound occurrence of an individual variable according to 
this rule is called free. 
Received August 6, 1948. 
1 This paper contains results of research undertaken while the author was a National 
Research Council predoctoral fellow. The material is included in "The Completeness of 
Formal Systems," a thesis presented to the faculty of Princeton University in candidacy 
for the degree of Doctor of Philosophy. 
2 Numbers refer to items in the bibliography appearing at the end of the paper. 
159 
This content downloaded from 195.113.26.195 on Tue, 23 Sep 2014 10:38:19 AM
All use subject to JSTOR Terms and Conditions


## Page 3

160 
LEON 
HENKIN 
In addition to formal manipulation of the formulas of this system we shall be 
concerned with their meaning according to the following interpretation. The 
propositional constants are to denote one of the truth values, T or F, the symbol 
"f" denoting F, and the propositional variables are to have the set of these truth 
values as their range. Let an arbitrary set, 1, be specified as a domain of indi- 
viduals, and let each individual constant denote a particular element of this 
domain while the individual variables have I as their range. The functional 
constants (variables) of degree n are to denote (range over) subsets of the set of 
all ordered n-tuples of I. G(xi, * * *, x1n) 
is to have the value T or F according 
as the n-tuple (xi, * * *, xa) of individuals is or is not in the set G; (A D B) is to 
have the value F if A is T and B is F, otherwise T; and (x)A is to have the value 
T just in case A has the value T for every element x in 7.3 
If A is a wff, 
I a domain, and if there is some assignment of denotations to the 
constants of A and of values of the appropriate kind to the variables with free 
occurrences in A, such that for this assignment A takes on the value T according 
to the above interpretation, 
we say that A is satisfiable 
with respect to I. If every 
such assignment yields the value T for A we say that A is valid with respect to I. 
A is valid if it is valid with respect to every domain. We shall give a set of axioms 
and formal rules of inference adequate to permit formal proofs of every valid 
formula. 
Before giving the axioms, however, we describe certain rules of abbreviation 
which we use to simplify 
the appearance of wffs and formula schemata. If A is 
any wif and x any individual variable we write 
-A 
for (A Df), 
(3x)A 
for --(x)>-A. 
From the rules of interpretation 
it is seen that -,A has the value T or F accord- 
ing as A has the value F or T, while (3x)A denotes T just in case there is some 
individual x in I for which A has the value T. 
Furthermore 
we may omit outermost parentheses, replace a left parenthesis 
by a dot omitting its mate at the same time if its mate comes at the end of the 
formula (except possibly for other right parentheses), and put a sequence of wfs 
separated by occurrences of "D" when association to the left is intended. For 
example, 
A D B D . C D D D E for ((A D B) D ((C D D)) DE)), 
where A, B, C, D, E may be wffs or abbreviations of wffs. 
If A, B, C are any wffs, 
the following 
are called axioms: 
1. CD.BDC 
2. A DB D .A D (B DC) D .A DC 
3. A Df Df DA 
4. (x) (A D B) D . A D (x)B, where x is any individual variable with no free 
occurrence in A. 
8 A more precise, syntactical account of these ideas can be formulated 
along the lines of 
Tarski (3). But this semantical version will suffice 
for our purposes. 
This content downloaded from 195.113.26.195 on Tue, 23 Sep 2014 10:38:19 AM
All use subject to JSTOR Terms and Conditions


## Page 4

COMPLETENESS 
OF THE FIRST-ORDER 
FUNCTIONAL 
CALCULUS 
161 
5. (x)A D B, where x is any individual variable, y any individual symbol, and 
B is obtained by substituting 
y for each free occurrence of x in A, provided that 
no free occurrence of x in A is in a well-formed 
part of A of the form (y)C. 
There are two formal rules of inference: 
I (Modus Ponens). To infer B from any pair of formulas A, A D B. 
II (Generalization). To infer (x)A from A, where x is any individual variable. 
A finite sequence of wffs is called a formal proof from assumptions r, where 
r is a set of wffs, 
if every formula of the sequence is either an axiom, an element 
of r, or else arises from one or two previous formulas of the sequence by modus 
ponens or generalization, 
except that no variable with a free occurrence in some 
formula of r may be generalized upon. If A is the last formula of such a sequence 
we write r F A. Instead of { r, A } F B ( tr, A }denoting the set formed from 
r by adjoining the wff A), we shall write r, A F B. If r is the empty set we 
call the sequence simply a formal proof and write F A. In this case A is called 
a formal theorem. Our object is to show that every valid formula is a formal 
theorem, and hence that our system of axioms and rules is complete. 
The following theorems about the first-order 
functional calculus are all either 
well-known 
and contained in standard works, or else very simply derivable from 
such results. We shall use them without proof here, referring 
the reader to 
Church (4) for a fuller account. 
III (The Deduction Theorem). If r, A H B then r F A D B (for any wffs A, 
B and any set r of wffs). 
6. p B Df D . B D C 
7. pB D. CODf D.B 
DCDf 
8. F (x)(A Df) D . (3x)A Df 
9. 
(x)B O f :D . (3x) (B :Df). 
IV. If r is a set of wffs no one of which contains a free occurrence of the indi- 
vidual symbol u, if A is a wif and B is obtained from it by replacing each free 
occurrence of u by the individual symbol x (none of these occurrences of x being 
bound in B), then if r P A, also r P B. 
This completes our description of the formal system; or, more accurately, of a 
class of formal systems, a certain degree of arbitrariness 
having been left with 
respect to the nature and number of primitive symbols. 
Let So be a particular system determined by some definite choice of primitive 
symbols. A set A of wffs of So will be called inconsistent 
if A P f, otherwise 
consistent. A set A of wffs of So will be said to be simultaneously 
satisfiable 
in 
some domain I of individuals if there is some assignment of denotations (values) 
of the appropriate type to the constants (variables) with free occurrences in 
formulas of A, for which each of these formulas has the value T under the inter- 
pretation previously described. 
This content downloaded from 195.113.26.195 on Tue, 23 Sep 2014 10:38:19 AM
All use subject to JSTOR Terms and Conditions


## Page 5

162 
LEON HENKIN 
THEOREM. 
If A is a set of formulas of SO in which no member 
has any occurrence 
of a free individual variable, and if A is consistent, 
then A is simultaneously 
satisfi- 
able in a domain of individuals having the same cardinal number as the set of primi- 
tive symbols 
of So. 
We shall carry out the proof for the case where SO has only a denumerable 
infinity 
of symbols, and indicate afterward the simple modifications 
needed in 
the general case. 
Let ui (i, j = 1, 2, 3, * ) be symbols not occurring among the symbols of 
So. For each i (i = 1, 2, 3, ... 
) let Si be the first-order 
functional calculus 
whose primitive symbols are obtained from those of Si-, by adding the symbols 
uii (j = 1, 2, 3, * * ) as individual constants. Let Sew 
be the system whose sym- 
bols are those appearing in any one of the systems Si . It is easy to see that the 
wffs of Se, are denumerable, and we shall suppose that some particular enumera- 
tion is fixed on so that we may speak of the first, second, * 
, nth, * formula 
of Se. in the standard ordering. 
We can use this ordering to construct in So a maximal consistent set of 
cwffs, ro, which contains the given set A. (We use "cwff" to mean closed wff: 
a wff which contains no free occurrence 
of any individual variable.) ro is maximal 
consistent in the sense that if A is any cwff of So which is not in ro, then Fo, A 
Ff; but not ro 
o 
f. 
To construct ro let Foo be A and let B1 be the first (in the standard ordering) 
cwff A of So such that { roF, A I is consistent. Form roF by adding B1 to Foo . 
Continue this process as follows. Assuming that roi and Bi have been found, 
let Bijr be the first cwff A (of So) after Bi, such that { roF , A is consistent; 
then form rF0+j by adding Bi+j to roi. Finally let ro be composed of those 
formulas appearing in any roi (i = 0, 1, * * .). Clearly ro contains A. 
ro is 
consistent, 
for if ro F f then the formal proof of f from assumptions ro would be 
a formal proof of f from some finite subset of ro as assumptions, and hence for 
some i(i = O, 1, * 
* 
* ) roi 
P f contrary to construction of the sets of ro0. 
Finally, ro is maximal consistent because if A is a cwff of So such that { ro, A I 
is consistent then surely { roi0, A } is consistent for each i; hence A will appear 
in some roi and so in ro. 
Having obtained ro we proceed to the system S, and form a set r1 of its 
cwffs as follows. Select the first (in the standard ordering) cwff of ro which has 
the form (3x)A (unabbreviated: ((x) (A D f) D f)), and let A' be the result of 
substituting the symbol ull of S, for all free occurrences of the variable x in the 
wif A. The set { ro, A'} must be a consistent set of cwffs of S,. 
For suppose 
that ro, A' F f. Then by III (the Deduction Theorem), ro F A' D f; hence 
byiv, ro F A Df; byII, ro F (x)(A D f); and so by8andl, ro F (3x)A D 
f. But by assumption Fo F (3x)A. 
Hence modus ponens gives Fo F f con- 
trary to the construction 
of ro as a consistent set. 
We proceed in turn to each cwff of ro having the form (3x)A, and for the 
jth of these we add to ro the cwff A' of S, obtained by substituting 
the constant 
uj; for each free occurrence of the variable x in the wfF A. Each of these ad- 
junctions leaves us with a consistent set of cwffs of S, by the argument above. 
This content downloaded from 195.113.26.195 on Tue, 23 Sep 2014 10:38:19 AM
All use subject to JSTOR Terms and Conditions


## Page 6

COMPLETENESS 
OF THE FIRST-ORDER 
FUNCTIONAL 
CALCULUS 
163 
Finally, after all such formulas A' have been added, we enlarge the resulting 
set of formulas to a maximal consistent set of cwffs of S1 in the same way that 
Fo was obtained from A in So. This set of cwffs we call Fi . 
After the set rT has been formed in the system Si we construct ]i+,l in Si+, 
by the same method used in getting ri from Fo but using the constants ui+i; 
(j = 1, 2, 3, * * * ) in place of uij. 
Finally we let rP be the set of cwffs 
of Six 
consisting of all those formulas which are in any rF. It is easy to see that F,, 
possesses the following properties: 
i) rI. is a maximal consistent set of cwffs of So,. 
ii) If a formula of the form (3x)A is in F. then rP also contains a formula A' 
obtained from the wff 
A by substituting 
some constant ui for each free occurrence 
of the variable x. 
Our entire construction 
has been for the purpose of obtaining a set of formulas 
with these two properties; they are the only properties we shall use now in show- 
ing that the elements of IF are simultaneously satisfiable in a denumerable 
domain of individuals. 
In fact we take as our domain I simply the set of individual constants of 
Se, and we assign to each such constant (considered as a symbol in an inter- 
preted system) itself (considered as an individual) as denotation. It remains 
to assign values in the form of truth-values to propositional symbols, and sets 
of ordered n-tuples of individuals to functional symbols of degree n, in such a 
way as to lead to a value T for each cwff of rP . 
Every propositional symbol, A, of So is a cwff of S,; fiwe 
assign to it the value 
T or F according as F. F A or not. Let G be any functional symbol of degree 
n. We assign to it the class of those n-tuples (a1, * * *, a,) of individual 
constants such that F. F G(a1, * * *, a,) 
This assignment determines a unique truth-value for each cloWt of Si,, under 
the fundamental interpretation 
prescribed for quantification and "D". 
(We 
may note that the symbol "f" is assigned F in agreement with that interpre- 
tation since rF is consistent.) We now go on to show the 
LEIMMA: For each cwff A of S, the associated value is T or F according as 
IF, LA or not. 
The proof is by induction on the length of A. We may notice, first, that if 
we do not have P. F A for some cwff A of S. then we do have rF. A D f. For 
by property i) of P. we would have F.,, A F f and so rF, F A D f by III. 
In case A is an elementary cwff the lemma is clearly true from the nature of 
the assignment. 
Suppose A is B D C. If C has the value T, by induction hypothesis 
rF F c; 
then F, L B D C by 1 and I. This agrees with the lemma since B D C has 
the value T in this case. Similarly, if B has the value F we do not have rF. F B 
by induction hypothesis. Hence F. F B D f, and r. F B D C by 6 and I. 
Again we have agreement with the lemma since B D C has the value T in this 
case also. Finally if B and C have the values T and F respectively, so that 
(induction hypothesis) ]o,,, F B while Th. H C D f, we must show that rF, k B 
This content downloaded from 195.113.26.195 on Tue, 23 Sep 2014 10:38:19 AM
All use subject to JSTOR Terms and Conditions


## Page 7

164 
LEON HENKIN 
D C does not hold (since B D C has the value F in this case). But by 7 and 
two applications of I we conclude that r. P B D C D f. Now we see that if 
rP F 
B D C then r F f by I, contrary 
to the fact that rL is consistent (property 
i). 
Suppose A is (x)B. If rJ F (x)B then (by 5 and I) rF F B', where B' is 
obtained by replacing all free occurrences of x in B by some (arbitrary) individ- 
ual constant. That is, (induction hypothesis) B has the value T for every 
individual x of I; therefore 
A has the value T and the lemma is established in 
this case. If, on the other hand, we do not have r F (x)B, then rF F (x)B D f 
whence (by 9, I) r. F (3x) (B D f). Hence, by property ii of rF, for some 
individual constant uji we have rF F B' D f, where B' is obtained from B by 
replacing each free occurrence of x by uji. 
Hence for this uij we cannot have 
r, F B' else r. F f by I contrary to the fact that rF is consistent (property i). 
That is, by induction hypothesis, 
B has the value F for at least the one individual 
uij of I and so (x)B has the value F as asserted by the lemma for this case. 
This concludes the inductive proof of the lemma. In particular the formulas 
of rF all have the value T for our assignment and so are simultaneously satis- 
fiable in the denumerable domain I. Since the formulas of A are included among 
those of rP our theorem is proved for the case of a system S0 whose primitive 
symbols are denumerable. 
To modify the proof in the case of an arbitrary system S0 it is only necessary 
to replace the set of symbols uii by symbols uj , where i ranges over the positive 
integers as before but a ranges over a set with the same cardinal number as the 
set of primitive symbols of SO; and to fix on some particular well-ordering 
of 
the formulas of the new S. in place of the standard enumeration employed 
above. (Of course the axiom of choice must be used in this connection.) 
The completeness 
of the system S0 is an immediate consequence of our theorem. 
COROLLARY 1: If A is a valid wff of SO then F A. 
First consider the case where A is a cwff. Since A is valid A D f has the value 
F for any assignment with respect to any domain; i.e., A D f is not satisfiable. 
By our theorem it is therefore inconsistent: A D f F f. Hence F A D f D f 
by III and F A by 3 and I. 
The case of wff A' which contains some free occurrence of an individual varia- 
ble may be reduced to the case of the cwff A (the closure of A') obtained by pre- 
fixing to A' universal quantifiers with respect to each individual variable with 
free occurrences in A' (in the order in which they appear). For it is clear from 
the definition 
of validity that if A' is valid so is A. But then F A. From which 
we may infer FA' by successive applications of 5 and I. 
COROLLARY 2: Let S0 be a functional calculus of first order and m the cardinal 
number of the set of its primitive 
symbols. If A is a set of cwffs which is simul- 
taneously satisfiable 
then in particular A is simultaneously 
satisfiable 
in some do- 
main of cardinal m. 
This is an immediate consequence of our theorem and the fact that if A is 
simultaneously satisfiable it must also be consistent (since rules of inference 
This content downloaded from 195.113.26.195 on Tue, 23 Sep 2014 10:38:19 AM
All use subject to JSTOR Terms and Conditions


## Page 8

COMPLETENESS 
OF THE FIRST-ORDER 
FUNCTIONAL 
CLACULUS 
165 
preserve the property of having the value T for any particular assignment in 
any domain, and so could not lead to the formula f). For the special case where 
m is No this corollary is the well-known 
Skolem-Ldwenheim 
result (5). It should 
be noticed, for this case, that the assertion of a set of cwffs 
A can no more com- 
pel a domain to be finite than non-denumerably 
infinite: there is always a de- 
numerably infinite domain available. There are also always domains of any 
cardinality greater than No in which a consistent set A is simultaneously satis- 
fiable, and sometimes finite domains. However for certain A no finite domain 
will do. 
Along with the truth functions of propositional calculus and quantification 
with respect to individual variables the first-order 
functional calculus is some- 
times formulated so as to include the notion of equality as between individuals. 
Formally this may be accomplished by singling out some functional constant 
of degree 2, say Q, abbreviating Q(x, y) as x = y (for individual symbols x, y), 
and adding the axiom schemata 
El. x= x 
E2. x = y D . A D B, where B is obtained from A by replacing some free 
occurrence of x by a free occurrence of y. 
For a system SO of this kind our theorem holds if we replace "the same 
cardinal number as" by "a cardinal number not greater than," where the def- 
inition of "simultaneously satisfiable" must be supplemented by the provision 
that the symbol "= " shall denote the relation of equality between individuals. 
To prove this we notice that a set of cwffs A in the system SO may be regarded as 
a set of cwffs (A, E1, E2) in the system So, where E1 is the set of closures of 
axiomsEj (i = 1,2). 
SinceEl,E2 
- x = y Dy = x and E1,E2 F x = y D 
. y = z D x = z we see that the assignment which gives a value T to each formula 
of A, El, E2 must assign some equivalence relation to the functional symbol Q. 
If we take the domain I' of equivalence classes determined by this relation over 
the original domain I of constants, and assign to each individual constant (as 
denotation) the class determined by itself, we are led to a new assignment which 
is easily seen to satisfy A (simultaneously) in SIO. 
A set of wffs may be thought of as a set of axioms determining 
certain do- 
mains as models; namely, domains in which the wffs are simultaneously satis- 
fiable. For a first-order 
calculus containing the notion of equality we can find 
axiom sets which restrict models to be finite, unlike the situation for calculi- 
without equality. More specifically, 
given any finite set of finite numbers there 
exist axiom sets whose models are precisely those domains in which the number 
of individuals is one of the elements of the given set. (For example, if the set 
of numbers is the pair (1, 3) the single axiom 
(x) (y) (x = y) v . (3x) (3y) (3z) 
.-'(x= 
y) A - 
(x = z) 
A 
(y = z) A (t). t = X V t = y v t = z 
will suffice, where A A B, A v B abbreviate -(A D -B), A D B D B re- 
spectively.) However, an axiom set which has models of arbitrarily 
large finite 
This content downloaded from 195.113.26.195 on Tue, 23 Sep 2014 10:38:19 AM
All use subject to JSTOR Terms and Conditions


## Page 9

166 
LEON 
HENKIN 
cardinality must also possess an infinite model as one sees by considering the 
formulas 
Ci: 
(3Sx)(3X2) 
(3xi) . -(xi= 
X2) A 
(Xi 
= X2) 
A 
. 
-(Xi- 
= Xi). 
Since by hypothesis any finite number of the Ci are simultaneously satisfiable 
they are consistent. Hence all the Ci are consistent and so simultaneously 
satisfiable-which can happen only in an infinite 
domain of individuals. 
There are axiom sets with no finite models-namely, the set of all formulas 
Ci defined above. Every axiom set with an infinite model has models with 
arbitrary infinite cardinality. For if a, fi range over any set whatever the set 
of all formulas -x(xa = x#) for distinct a, fi will be consistent (since the assump- 
tion of an infinite 
model guarantees consistency for any finite set of these form- 
ulas) and so can be simultaneously 
satisfied. 
In simplified 
form the proof of our theorem and corollary 1 may be carried 
out for the propositional calculus. For this system the symbols uji and the 
construction 
of S. may be omitted, an assignment of values being made directly 
from ro. While such a proof of the completeness of the propositional calculus 
is short compared with other proofs in the literature the latter are to be pre- 
ferred since they furnish a constructive 
method for finding 
a formal proof of any 
given tautology, rather than merely demonstrate its existence. 
BIBLIOGRAPHY 
1. QUINE, 
W. V., Completeness of the propositional calculus, The journal of symbolic 
logic, vol. 3 (1938), pp. 37-40. 
2. GODEL, KURT, Die Vollstdndigkeit der Axiome des logischen Funktionenkalkuls, Mo- 
natshefte fur Mathematik und Physik, vol. 37 (1930), pp. 349-360. 
3. TARSKI, ALFRED, Der Wahrheitsbegriff 
in den Formalisierten Sprachen, Studia Philo- 
sophica, vol. 1 (1936), pp. 261-405. 
4. CHURCH, ALONZO, Introduction to Mathematical Logic, Part I, Annals of Mathematics 
Studies, Princeton University Press, 1944. 
5. SKOLEM, TH., Uber einige Grundlagenfragen der Mathematik, Skrifter utgitt av Det 
Norske Videnskaps-Akademi i Oslo, 1929, no. 4. 
PRINCETON 
UNIVERSITY 
This content downloaded from 195.113.26.195 on Tue, 23 Sep 2014 10:38:19 AM
All use subject to JSTOR Terms and Conditions
