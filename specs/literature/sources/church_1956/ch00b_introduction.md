<!-- Source: Church, A. (1956). Introduction to Mathematical Logic. Introduction (pages 1-68): logic, logistic method, historical overview. BibKey: Church1956 -->

Introduction
This introduction contains a number of preliminary explanations, which 
it seems are most suitably placed at the beginning, though many will be­
come clearer in the light of the formal development which follows. The 
reader to whom the subject is new is advised to read the introduction through 
once, then return to it later after a study of the first few chapters of the book. 
Footnotes may in general be omitted on a first reading.
00. Logic. Our subject is logic—or, as we may say more fully, in order 
to distinguish from certain topics and doctrines which have (unfortunately) 
been called by the same name, it is formal logic.
Traditionally, (formal) logic is concerned with the analysis of sentences 
or of propositions1 and of proof2 with attention to the form in abstraction 
from the matter. This distinction between form and matter is not easy to 
make precise immediately, but it may be illustrated by examples.
To take a relatively simple argument for illustrative purposes, consider 
the following:
I 
Brothers have the same surname; Richard and Stanley are brothers; 
Stanley has surname Thompson; therefore Richard has surname 
Thompson.
Everyday statement of this argument would no doubt leave the first of the 
three premisses3 tacit, at least unless the reasoning were challenged; but * *
*See §04.
*In the light both of recent work and of some aspects of traditional logic we must 
add here, besides proof, such other relationships among sentences or propositions as 
can be treated in the same manner, i.e., with regard to form in abstraction from the 
m atter. These include (e.g.) disproof, compatibility; also partial confirmation, which 
is im portant in connection with inductive reasoning (cf. C. G. Hempel in The Journal 
of Symbolic Logic, vol. 8 (1943), pp. 122— 143).
But no doubt these relationships both can and should be reduced to th at of proof, 
by making suitable additions to the object language (§07) if necessary. E.g., in reference 
to an appropriate formalized language as object language, disproof of a proposition or 
sentence may be identified with proof of its negation. The corresponding reduction of 
the notions of compatibility and confirmation to th at of proof apparently requires 
modal logic—a subject which, though it belongs to formal logic, is beyond the scope 
of this book.
^Following C. S. Peirce (and others) we adopt the spelling premiss fur the logical 
term to distinguish it from premise in other senses, in particular to distinguish the 
plural from the legal term  premises.

---


2
INTRODUCTION
for purposes of logical analysis all premisses must be set down explicitly. 
The argument, it may be held, is valid from its form alone, independently 
of the matter, and independently in particular of the question whether the 
premisses and the conclusion are in themselves right or wrong. The reasoning 
may be right though the facts be wrong, and it is just in maintaining this 
distinction that we separate the form from the matter.
For comparison with the foregoing example consider also:
II 
Complex numbers with real positive ratio have the same amplitude; 
i — V3/3 and co are complex numbers with real positive ratio; co has 
amplitude 2?r/3; therefore i — V3/3 has amplitude 2ts/3.
This may be held to have the same form as I, though the matter is different, 
and therefore to be, like I, valid from the form alone.
Verbal similarity in the statements of I and II, arranged at some slight 
cost of naturalness in phraseology, serves to highlight the sameness of 
form. But, at least in the natural languages, such linguistic parallelism 
is not in general a safe guide to sameness of logical form. Indeed, the 
natural languages, including English, have been evolved over a long 
period of history to serve practical purposes of facility of communication, 
and these are not always compatible with soundness and precision of 
logical analysis.
To illustrate this last point, let us take two further examples:
III 
I have seen a portrait of John Wilkes Booth; John Wilkes Booth 
assassinated Abraham Lincoln; thus I have seen a portrait of an 
assassin of Abraham Lincoln.
IV 
I have seen a portrait of somebody; somebody invented the wheeled 
vehicle; thus I have seen a portrait of an inventor of the wheeled 
vehicle.
The argument III will be recognized as valid, and presumably from the 
logical form alone, but IV as invalid. The superficial linguistic analogy of 
the two arguments as stated is deceptive. In this case the deception is quickly 
dispelled upon going beyond the appearance of the language to consider the 
meaning, but other instances are more subtle, and more likely to generate 
real misunderstanding. Because of this, it is desirable or practically necessary 
for purposes of logic to employ a specially devised language, a formalized 
language as we shall call it, which shall reverse the tendency of the natural 
languages and shall follow or reproduce the logical form—at the expense.

---


§01]
N A M E S
3
where necessary, of brevity and facility of communication. To adopt a 
particular formalized language thus involves adopting a particular theory 
or system  of logical analysis. (This must be regarded as the essential feature 
of a formalized language, not the more conspicuous but theoretically less 
im portant feature that it is found convenient to replace the spelled words 
of m ost (written) natural languages by single letters and various special 
sym bols.)
0 1 . N a m e s. One kind of expression which is familiar in the natural 
languages, and which we shall carry over also to formalized languages, is the 
proper name. Under this head we include not only proper names which are 
arbitrarily assigned to denote in a certain way- such names, e.g., as 
“ R em brandt/' “Caracas," “ Sirius," “ the Mississippi," “The Odyssey," 
“ eight"— but also names having a structure that expresses some analysis 
of the w ay in which they denote.4 As exam ples of the latter we m ay cite: 
“five hundred nine," which denotes a certain prime number, and in the way 
expressed by the linguistic structure, nam ely as being five times a hundred 
plus nine; “ the author of W a v e rle y which denotes a certain Scottish 
novelist, nam ely Sir W alter Scott, and in the particular way expressed by 
the linguistic structure, nam ely as having written Waverley; “ Rem brandt's 
birthplace"; “the capital of Venezuela"; “the cube of 2.”
The distinction is not alw ays clear in the natural languages betw een the 
two kinds of proper names, those which are arbitrarily assigned to have a 
certain meaning (prim itive proper names, as we shall say in the case of a 
form alized language), and those which have a linguistic structure of mean­
ingful parts. E.g., “The O dyssey" has in the Greek a derivation from 
"Odysseus," and it m ay be debated whether this etym ology is a mere 
m atter of past history or whether it is still to be considered in modern 
English that the name “The Odyssey" has a structure involving the name 
“ Odysseus." This uncertainty is removed in the case of a formalized 
language by fixing and making explicit the formation rules of the 
language (§07).
There is not yet a theory of the meaning of proper names upon which
*We extend the usual meaning of proper name in this manner because such alternative 
terms as singular name or singular term have traditional associations which we wish to 
avoid. The single word name would serve the purpose except for the necessity of 
distinguishing from the common names (or general names) which occur in the natural 
languages, and hereafter we shall often say simply name.
We do use the word term, b u t in its everyday meaning of an item of terminology, 
and not with any reference to the traditional doctrine of ‘‘categorical propositions’* 
or the like.

---


4
INTRODUCTION
general agreement has been reached as the best. Full discussion of the 
question would take us far beyond the intended scope of this book. But it 
is necessary to outline briefly the theory which will be adopted here, due in 
its essentials to Gottlob Frege.5
The most conspicuous aspect of its meaning is that a proper name always 
is, or at least is put forward as, a name of something. We shall say that a 
proper name denotes6 or names7 that of which it is a name. The relation 
between a proper name and what it denotes will be called the name relation,8
•See his paper, "Ueber Sinn und Bedeutung," in Z e its c h r ifi fu r  P h ilo so p h ie  u n d  
p h ilo so p h isch e K r it ik , vol. 100 (1892), pp. 25-50. (There are an Italian translation of 
this by L. Geymonat in G ottlob F reg e, A r itm e tic a  e L o g ic a (1948), pp. 215-252, and 
English translations by Max Black in T h e  P h ilo so p h ic a l R e v ie w , vol. 57 (1948), pp. 
207-230, and by H erbert Feigl in R e a d in g s  in  P h ilo so p h ic a l A n a ly s is  (1949), pp, 
85-102. See reviews of these in T h e  J o u r n a l o f S y m b o lic  L o g ic , vol. 13 (1948), pp. 
152-153, and vol. 14 (1949), pp. 184-185.)
A similar theory, but with some essential differences, is proposed by Rudolf Carnap 
in his recent book M e a n in g  a n d  N e c e s s ity (1947).
A radically different theory is that of Bertrand Russell, developed in a paper in 
M in d , vol. 14 (1905), pp. 479-493; in the Introduction to the first volume of P r in c ip ia  
M a th e m a tic a  (by A. N. Whitehead and Bertrand Russell, 1910); and in a number of 
more recent publications, among them Russell's book, A n  I n q u ir y  in to  M e a n in g  
T r u th  (1940). The doctrine of Russell amounts very nearly to a rejection of proper 
names as irregularities of the natural languages which are to be eliminated in constructing 
a formalized language. It falls short of this by allowing a narrow category of proper 
names which must be names of sense qualities that are known by acquaintance, and 
which, in Fregean terms, have B e d e u tu n g  but not S in n .
•In the usage of J. S. Mill, and of others following him, not only a singular name 
(proper name in our terminology) but also a common or general name is said to denote, 
with the difference th at the former denotes only one thing, the latter, many things. 
E.g., the common name “man" is said to denote Rembrandt; also to denote Scott; 
also to denote Frege; etc.
In the formalized languages which we shall study, the nearest analogues of the com­
mon name will be the va ria b le and the fo r m  (see §02). And we prefer to use a different 
terminology for variables and forms than th at of denoting—in particular because we 
wish to preserve the distinction of a proper name, or constant, from a form which is 
concurrent to a constant (in the sense of § 02), and from a variable which has one thing 
only in its range. In what follows, therefore, we shall speak of p r o p e r  n a m e s o n ly as 
denoting.
From another point of view common names may be thought of as represented in the 
formalized languages, not by variables or forms, but by proper names of classes (class 
constants). Hence the usage has also arisen according to which a proper name of a class 
is said to denote the various members of the class. We shall not follow this, but shall 
speak of a proper name of a class as denoting the class itself. (Here we agree with Mill, 
who distinguishes a singular collective name, or proper name of a class, from a common 
or general name, calling the latter a "name of a class" only in the distributive sense of 
being a name of each individual.)
7We thus translate Frege’s bedeuten by d en o te or n a m e . The verb to m e a n we reserve 
for general use, in reference to possible different kinds of meaning.
•The name relation is properly a ternary relation, among a language, a word or phrase 
of the language, and a denotation. But it may be treated as binary by fixing the language 
in a particular context. Similarly one should speak of the denotation of a name w ith  
respect to a la n g u a g e, omitting the latter qualification only when the language has been 
fixed or when otherwise no misunderstanding can result.

---


§01]
N A M E S
5
and the thing9 denoted will be called the denotation. For instance, the proper 
name "Rembrandt" will thus be said to denote or name the Dutch artist 
Rembrandt, and he will be said to be the denotation of the name "Rem­
brandt." Similarly, "the author of Waverley" denotes or names the Scottish 
author, and he is the denotation both of this name and of the name "Sir 
Walter Scott."
That the meaning of a proper name does not consist solely in its denotation 
may be seen by examples of names which have the same denotation though 
their meanings are in some sense different. Thus "Sir Walter Scott" and 
"the author of Waverley" have the same denotation; it is contained in the 
meaning of the first name, but not of the second, that the person named is 
a knight or baronet and has the given name "Walter" and surname "Scott";10 
and it is contained in the meaning of the second name, but not of the first, 
that the person named wrote Waverley (and indeed as sole author, in view 
of the definite article and of the fact that the phrase is put forward as a 
proper name). To bring out more sharply the difference in meaning of the 
two names let us notice that, if two names are synonymous (have the same 
meaning in all respects), then one may always be substituted for the other 
without change of meaning. The sentence, "Sir Walter Scott is the author of 
Waverley ” has, however, a very different meaning from the sentence, "Sir 
Walter Scott is Sir W alter Scott": for the former sentence conveys an important 
fact of literary history of which the latter gives no hint. This difference in 
meaning may lead to a difference in truth when the substitution of one name 
for the other occurs within certain contexts.11 E.g., it is true that "George IV 
once demanded to know whether Scott was the author of Waverley") but 
false that "George IV once demanded to know whether Scott was Scott."12
•The word thing is here used in its widest sense, in short lor anything namable.
10The term  proper name is often restricted to names of this kind, i.e., which have 
as part of their meaning th a t the denotation is so called or is or was entitled to be so 
called. As already explained, we are not making such a restriction.
Though it is, properly speaking, irrelevant to the discussion here, it is of interest to 
recall th at Scott did make use of ‘’the author of Waverley** as a pseudonym during the 
time th at his authorship of the Waverley Novels was kept secret.
“ Contexts, namely, which render the occurrences ol the names oblique in the sense 
explained below.
“ The particular example is due to Bertrand Russell; the point which it illustrates, 
to Frege.
This now famous question, put to Scott himself in the indirect form of a toast "to the 
author of Waverley,, at a dinner a t which Scott was present, was met by him with a flat 
denial, "Sire, I am not the author of Waverley.” We may therefore enlarge on the 
example by remarking th a t Scott, despite a pardonable departure from the truth, did 
not mean to go so far as to deny his self-identity (as if he had said "I am not I"). 
And his hearers surely did not so understand him, though some must have shrewdly 
guessed the deception as to his authorship of Waverley.

---


6
INTRODUCTION
Therefore, besides the denotation, we ascribe to every proper name an­
other kind of meaning, the S5w$£,13 saying, e.g., that "Sir Walter Scott" 
and "the author of Waverley” have the same denotation but different sen­
ses.14 Roughly, the sense is what is grasped when one understands a name,15 
and it may be possible thus to grasp the sense of a name without having 
knowledge of its denotation except as being determined by this sense. If, in 
particular, the question "Is Sir Walter Scott the author of WaverleyV1 is 
used in an intelligent demand for new information, it must be that the 
questioner knows the senses of the names "Sir Walter Scott" and "the 
author of Waverley” without knowing of their denotations enough to identify 
them certainly with each other.
We shall say that a name denotes or names its denotation and expresses16 * 
its sense. Or less explicitly we may speak of a name just as having a certain 
denotation and having a certain sense. Of the sense we say that it determines 
the denotation, or is a concept17 of the denotation.
Concepts17 we think of as non-linguistic in character—since synonymous 
names, in the same or different languages, express the same sense or concept 
—and since the same name may also express different senses, either in 
different languages or, by equivocation, in the same language. We are even
lsWe adopt this as the most appropriate translation of Frege’s S in n , especially since 
the technical meaning given to the word sen se thus comes to be very close indeed to the 
ordinary acceptation of the sense of an expression. (Russell and some others following 
him have used “meaning" as a translation of Frege's
UA similar distinction is made by J, S. Mill between the denotation and the connota­
tion of a name. And in fact we are prepared to accept c o n n o ta tio n as an alternative trans­
lation of S in n , although it seems probable that Frege did not have Mill's distinction in 
mind in making his own. We do not follow Mill in adm itting names which have denotation 
without connotation, but rather hold that a name m ust always point to its denotation 
in  so m e w ay, i.e., through some sense or connotation, though the sense may reduce in 
special cases just to the denotation's being called so and so (e.g., in the case of personal 
names), or to its being w hat appears here and now (as sometimes in the case of the 
demonstrative “this’’). Because of this and other differences, and because of the more 
substantial content of Frege’s treatment, we attribute the distinction between sense and 
denotation to Frege rather than to Mill. Nevertheless the discussion of names in Mill’s 
A  S y s te m  of L og ic (1843) may profitably be read in this connection.
u It is not meant by this to imply any psychological element in the notion of sense. 
Rather, a sense (or a concept) is a postulated abstract object, with certain postulated 
properties. These latter are only briefly indicated in the present informal discussion; 
and in particular we do not discuss the assumptions to be made about equality of senses, 
since this is unnecessary for our immediate purpose.
lflThis is our translation of Frege’s d riickt a u s. Mill’s term connotes is also acceptable 
here, provided that care is taken not to confuse Mill's meaning of this term with other 
meanings which it has since acquired in common English usage.
17This use of concept is a departure from Frege's terminology. Though not identical 
with Carnap’s use of co n cep t in recent publications, it is closely related to it, and was 
suggested to the writer by correspondence with Carnap in 1943. It also agrees well 
with Russell’s use of cla ss-co n cep t in T h e  P r in c ip le s  o f M a th e m a tic s (1903)—cf. §69 
thereof.

---


§01]
N A M E S
1
prepared to suppose the existence of concepts of things which have no name 
in any language in actual use. But every concept of a thing is a sense of 
some name of it in some (conceivable) language.
The possibility must be allowed of concepts which are not concepts of 
any actual thing, and of names which express a sense but have no denotation. 
Indeed such names, at least on one very plausible interpretation, do occur 
in the natural languages such as English: e.g., “Pegasus/'18 “the king of 
France in a.d. 1905." But, as Frege has observed, it is possible to avoid 
such names in the construction of formalized languages.19 And it is in fact 
often convenient to do this.
To understand a language fully, we shall hold, requires knowing the senses 
of all names in the language, but not necessarily knowing which senses 
determine the same denotation, or even which senses determine denotations 
at all.
In a well constructed language of course every name should have just one 
sense, and it is intended in the formalized languages to secure such univ-
18W h ile  th e  e x a c t s e n s e  o f t h e  n a m e  " P e g a s u s "  is v a r ia b le  o r u n c e r ta in , i t  is, w e ta k e  
it, r o u g h ly  t h a t  o f th e  w in g e d  h o r s e  w h o  to o k  s u c h  a n d  s u c h  a  p a r t  in  s u c h  a n d  su c h  
s u p p o s e d  e v e n ts — w h e re  o n ly  s u c h  m in im u m  e s s e n tia ls  o f th e  s to r y  a re  to  b e  in c lu d e d  as 
i t  w o u ld  b e  n e c e s s a ry  to  v e r if y  in  o r d e r  to  ju s t if y  s a y in g , d e s p ite  th e  c o m m o n  o p in io n , 
t h a t  " P e g a s u s  d id  a f te r  a ll e x i s t."
W e  a r e  t h u s  m a in ta in in g  t h a t ,  in  th e  p r e s e n t a c tu a l s t a t e  of th e  E n g lis h  la n g u a g e , 
" P e g a s u s "  is  n o t j u s t  a  p e r s o n a l n a m e , h a v in g  th e  s e n s e  of w h o  o r w h a t w a s  c a lle d  so  
a n d  so , b u t  h a s  th e  m o re  c o m p le x  s e n s e  d e s c rib e d . H o w e v e r, su c h  q u e s tio n s  r e g a r d in g  
th e  n a t u r a l  la n g u a g e s  m u s t n o t b e  s u p p o s e d  a lw a y s  to  h a v e  o n e  fin a l a n s w e r. O n  th e  
c o n tr a r y , th e  p r e s e n t a c tu a l s t a t e  ( a t a n y  tim e ) te n d s  to  b e in d e te r m in a te  in  a  w a y  to  
le a v e  m u c h  d e b a ta b le .
lf F o r  e x a m p le , in  th e  c a s e  o f a  fo rm a liz e d  la n g u a g e  o b ta in e d  fro m  o n e  o f th e  lo g is tic  
s y s te m s  o f C h a p te r  X  (o r of a  p a p e r  b y  th e  w r ite r  in  The Journal of Symbolic Logic, 
v o l. 5  (1 9 4 0 ), p p . 5 6 -0 8 ) b y  a n  in te r p r e ta t io n  r e ta in in g  th e  p r in c ip a l in te r p r e ta t io n  of 
th e  v a r ia b le s  a n d  o f th e  n o ta tio n s  A ( a b s tr a c tio n )  a n d  ( ) (a p p lic a tio n  of f u n c tio n  to  
a r g u m e n t) , i t  is  s u f fic ie n t to  ta k e  th e  fo llo w in g  p r e c a u tio n s  in  a s sig n in g  se n s e s  to  th e  
p r im itiv e  c o n s ta n ts . F o r  a  p r im itiv e  c o n s ta n t o f ty p e  o o r i th e  se n se  m u s t b e  s u c h  
a s — o n  t h e  b a s is  o f a c c e p te d  p r e s u p p o s itio n s — to  a s s u re  th e  e x is te n c e  of a  d e n o ta tio n  in  
th e  a p p r o p r ia t e  d o m a in , £) (o f tr u th - v a lu e s )  o r & (o f in d iv id u a ls ). F o r  a  p r im itiv e  
c o n s ta n t o f t y p e  a/? th e  s e n s e  m u s t b e  s u c h  a s — o n  th e  s a m e  b a s is — to  a s s u re  th e  e x i s t­
e n c e  o f a  d e n o ta tio n  w h ic h  is in  t h e  d o m a in  2193, i.e., w h ic h  is a  f u n c tio n  fro m  th e  (e n tire ) 
d o m a in  93 w h ic h  is ta k e n  a s  th e  r a n g e  o f v a r ia b le s  o f ty p e  f$, to  th e  d o m a in  21 w h ic h  is 
ta k e n  a s  th e  ra n g e  o f v a r ia b le s  o f ty p e  a.
T h e n  e v e r y  w e ll-fo rm e d  f o r m u la  w ith o u t fre e  v a r ia b le s  w ill h a v e  a  d e n o ta tio n , as 
in d e e d  i t  m u s t if su c h  in te r p r e ta t io n  o f th e  lo g is tic  s y s te m  is to  a c c o rd  w ith  fo rm a l 
p r o p e r tie s  o f th e  s y s te m .
A s in  th e  ca se , e.g ., o f (cc(0a), i t  m a y  h a p p e n  t h a t  th e  m o s t im m e d ia te  o r  n a t u r a lly  
s u g g e s te d  in te r p r e ta tio n  of a  p r im itiv e  c o n s ta n t o f ty p e  a/? m a k e s  i t  d e n o te  a  fu n c tio n  
fro m  a  p r o p e r  p a r t  o f th e  d o m a in  93 to  th e  d o m a in  21. I n  s u c h  a  ca se th e  d e f in itio n  of 
th e  f u n c tio n  m u s t b e e x te n d e d , b y  a r tif ic ia l m e a n s  if n e c e s s a ry , o v e r th e  r e m a in d e r  of 
th e  d o m a in  93, so a s  to  o b ta in  a  f u n c tio n  h a v in g  th e  e n tir e  d o m a in  93 a s  its  r a n g e . T h e  
se n s e  a s s ig n e d  to  th e  p r im itiv e  c o n s ta n t m u s t th e n  b e s u c h  a s  to  d e te r m in e  th is  l a t t e r  
f u n c tio n  a s  d e n o ta tio n , r a th e r  t h a n  th e  f u n c tio n  w h ic h  h a d  o n ly  a  p ro p e r p a r t  of SB 
a s  its  ra n g e .

---


8
INTRODUCTION
ocacy. But this is far from being the case in the natural languages. In par­
ticular, as Frege has pointed out, the natural languages customarily allow, 
besides the ordinary (gewohnlich) use of a name, also an oblique (ungerade) 
use of the name, the sense which the name would express in its ordinary use 
becoming the denotation when the name is used obliquely.20
Supposing univocacy in the use of names to have been attained (this 
ultimately requires eliminating the oblique use of names by introducing 
special names to denote the senses which other names express21), we make, 
with Frege, the following assumptions, about names which have a linguistic 
structure and contain other names as constituent parts: (1) when a con-
*°For example, in “ Scott is the author of W a v e r le y " the names “ S cott/' u W averley,** 
“the author of W a v e r le y ” have ordinary occurrences. But in “ George IV wished to 
know whether Scott was the author of W a v e r U y ” the same three names have oblique 
occurrences (while “ George IV" has an ordinary occurrence). Again, in “Schliemann 
sought the site of Troy" the names “Troy" and “the site of Troy" occur obliquely. 
For to seek the site of some other city, determined by a different concept, is not the 
same as to seek the site of Troy, not even if the two cities should happen as a m atter of 
fact {perhaps unknown to the seeker) to have had the same site.
According to the Fregean theory of meaning which we are advocating, “ Schliemann 
sought the site of Troy” asserts a certain relation as holding, not between Schliemann 
and the site of Troy (for Schliemann might have sought the site of Troy though Troy 
had been a purely fabulous city and its site had not existed), but between Schliemann 
and a certain concept, namely that of the site of Troy. This is, however, not to say that 
“ Schliemann sought the site of Troy" means the same as “Schliemann sought the con­
cept of the site of Troy." On the contrary, the first sentence asserts the holding of a 
certain relation between Schliemann and the concept of the site of Troy, and is true; 
but the second sentence asserts the holding of a like relation between Schliemann and 
the concept of the concept of the site of Troy, and is very likely false. The relation 
holding between Schliemann and the concept of the site of Troy is not quite that of 
having sought, or at least it is misleading to call it that—in view of the way in which 
the verb to seek is commonly used in English.
(W. V. Quine—in T h e J o u r n a l of P h ilo s o p h y , vol. 40 (1943), pp. 113-127, and else­
where—introduces a distinction between the “meaning" of a name and what the name 
“designates" which parallels Frege's distinction between sense and denotation, also a 
distinction between “ purely designative" occurrences of names and other occurrences 
which coincides in many cases with Frege’s distinction between ordinary and oblique 
occurrences. For a discussion of Quine's theory and its differences from Frege's see a 
review by the present writer, in T h e  J o u r n a l o f S y m b o lic  L o g ic, vol. 8 (1943), pp. 46-47; 
also a note by Morton G. White in P h ilo s o p h y  a n d  P h en o m en o lo g ica l R esea rch , vol. 9, 
no. 2 (1948), pp. 305-308.)
11 As an indication of the distinction in question we shall sometimes (as we did in the 
second paragraph of footnote 20) use such phrases as “the concept of Sir W alter Scott," 
“the concept of the author of W a v e r le y ,” “ the concept of the site of Troy" to d enote the 
same concepts which are exp ressed by the respective names “ Sir W alter Scott," “ the 
author of W a v e r le y ," “the site of Troy." The definite article “the" sufficiently distin­
guishes the phrase (e.g.) “ the concept of the site of Troy" from the similar phrase “a 
concept of the site of Troy," the latter phrase being used as a common name to refer to 
any one of the many different concepts of this same spot.
This device is only a rough expedient to serve the purpose of informal discussion. It 
does not do away with the oblique use of names because, when the phrase “ the concept 
of the site of Troy" is used in the way described, it contains an oblique occurrence of 
“the site of Troy."

---


§02]
C O N S T A N T S  A N D  V A R I A B L E S
9
stituent name is replaced by another having the same sense, the sense of the 
entire name is not changed; (2) when a constituent name is replaced by 
another having the same denotation, the denotation of the entire name is 
not changed (though the sense may be).22
We make explicit also the following assumption (of Frege), which, like 
(1) and (2), has been implicit in the foregoing discussion: (3) 'The denotation 
of a name (if there is one) is a function of the sense of the name, in the sense 
of §03 below; i.e.( given the sense, the existence and identity of the deno­
tation are thereby fixed, though they may not necessarily therefore be 
known to every one who knows the sense.
02. Constants and variables. We adopt the mathematical usage 
according to which a proper name of a number is called a constant, and in 
connection with formalized languages we extend this usage by removing 
the restriction to numbers, so that the term constant becomes synonymous 
with proper name having a denotation.
However, the term constant will often be applied also in the construction 
of uninterpreted calculi—logistic systems in the sense of §07—some of the 
symbols or expressions being distinguished as constants just in order to 
treat them differently from others in giving the rules of the calculus. Ordi­
narily the symbols or expressions thus distinguished as constants will in 
fact become proper names (with denotation) in at least one of the possible 
interpretations of the calculus.
As already familiar from ordinary mathematical usage, a variable is a 
symbol whose meaning is like that of a proper name or constant except that 
the single denotation of the constant is replaced by the possibility of various 
values of the variable.
Because it is commonly necessary to restrict the values which a variable 
may take, we think of a variable as having associated with it a certain non­
empty range of possible values, the range of the variable as we shall call it. 
Involved in the meaning of a variable, therefore, are the kinds of meaning 
which belong to a proper name of the range.23 But a variable must not be *
**To avoid serious difficulties, we m ust also assum e when a constituent nam e has no 
denotation th a t the entire nam e is then likewise w ithout denotation. In th e natural 
languages such apparent exam ples to the contrary as “ the m yth of P e g a s u s ,” "the 
search by Ponce de Leon for the fo u n ta in  o f y o u th ” are to  be explained as exhibiting 
oblique occurrences of th e italicized constituent nam e.
“ Thus th e distinction of sense and denotation comes to have an analogue for variables 
Two variables w ith ranges determ ined by different concepts have to be considered as 
variables of different kinds, even if the ranges them selves should be identical. However, 
because of the restricted v ariety  of ranges of variables adm itted, this question does not 
arise in connection w ith any of the formalized languages which are actually considered 
below.

---


10
INTRODUCTION
identified with a proper name of its range, since there are also differences 
of meaning between the two.24
The meaning which a variable does possess is best explained by returning 
to the consideration of complex names, containing other names as constit­
uent parts. In such a complex name, having a denotation, let one of the 
constituent names be replaced at one or more (not necessarily all) of its 
occurrences by a variable, say x. To avoid complications, we suppose that x 
is a variable which does not otherwise occur,25 and that the denotation of the 
constituent name which x replaces is in the range of x. The resulting expres­
sion (obtained from the complex name by thus replacing one of the constit­
uent names by a variable) we shall call a /orm.28 Such a form, for each value 
of x within the range of x, or at least for certain such values of x, has a value. 
Namely, the value of the form, for a given value of x, is the same as the 
denotation of the expression obtained from the form by substituting every­
where for x a name of the given value of x (or, if the expression so obtained * lo
14That such an identification is impossible may be quickly seen from the point of 
view of the ordinary mathematical use of variables. For two proper names of 
the range are fully interchangeable if only they have the same sense; but two 
distinct variables must be kept distinct even if they have the same range determined 
by the same concept. E.g., if each of the letters x and y is a variable whose range 
is the real numbers, we are obliged to distinguish the two inequalities x(x 
y) ^  0 
and x(x -f- x) ^  0 as different —indeed the second inequality is universally true, the 
first one is not.
u This is for momentary convenience of explanation. We shall apply the name form 
also to expressions which are similarly obtained but in which the variable x may other­
wise occur, provided the expression has at least one occurrence of a; as a free variable 
(see footnote 28 and the explanation in §06 which is there referred to).
‘•This is a different use of the word form from th at which appeared in §00 in the dis­
cussion of form and m atter. We shall distinguish the latter use, when necessary, by 
speaking more explicitly of logical form.
Our present use of the word form is similar to th at which is familiar in algebra, and in 
fact may be thought of as obtained from it by removing the restriction to a special kind 
of expressions (polynomials, or homogeneous polynomials), For the special case of 
propositional forms (see §04), the word is already usual in logic in this sense, indepen­
dently of its use by algebraists—see, e.gf, J. N. Keynes, Formal Logic, 4th edn., 1906, 
p. 53; Hugh MacColl in Mind, vol. 19 (1910), p. 193; Susanne K. Langer, Introduction
lo Symbolic Logic, 1937, p. 91; also Heinrich Scholz, Vorlesungen fiber Grundziige der 
Mathematischen Logik, 1949 (for the use of Aussageform in German).
Instead of the word form, we might plausibly have used the word variable here, by 
analogy with the way in which we use constant. I.e., just as we apply the term constant 
to a complex name containing other names (constants) as constituent parts, so we might 
apply the term variable to an appropriate complex expression containing variables aa 
constituent parts. This usage may indeed be defended as having some sanction in 
mathematical writing. B ut we prefer to preserve the better established usage according 
to which a variable is always a single symbol (usually a letter or letter with 
subscripts).
The use, by some recent authors, of the word function (with or without a qualifying 
adjective) for what we here call a form is, in our opinion, unfortunate, because it tends 
to conflict with and obscure the abstract notion of a function which will be explained 
in §03.

---


§02]
C O N S T A N T S  A N D  V A R I A B L E S
11
has no denotation, then the form has no value for that value of x) 2"7
A variable such as x, occurring in the manner just described, is called a 
free variable28 of the expression (form) in which it occurs.
Likewise suppose a complex name, having a denotation, to contain two 
constituent names neither of which is a part of the other, and let these two 
constituent names be replaced by two variables, say x and y respectively, 
each at one or more (not necessarily all) of its occurrences. For simplicity 
suppose that x and y are variables which do not occur in the original complex 
name, and that the denotations of the constituent names which x and y 
replace are in the ranges of x and y respectively. The resulting expression 
(obtained by the substitution described) is a form, with two free variables 
a; and y. For certain pairs of values of x and y , within the ranges of x and y 
respectively, the form has a value. Namely, the value of the form, for given 
values of x and y} is the same as the denotation of the expression obtained 
from the form by substituting everywhere for x and y names of their re-
17I t follows from assum ption (2), a t the end of §01, th a t the value thus obtained 
for the form  is independent of the choice of a particular nam e of the given value of x.
The distinction of sense and denotation is, however, relevant here. For in addition 
to a va lu e of the form in the sense explained in the tex t (we may call it more explicitly 
a d e n o ta tio n  va lu e), a complete account must m ention also wh*at we m ay call a sense 
va lu e of the form. Namely, a sense value of the form is determ ined by a concept of some 
value of x , and is the sam e as th e sense of the expression obtained from the form  by 
substitu tin g  everywhere for x  a nam e having this concept as its sense.
I t should also be noted th a t a form , in a particular language, may have a value even 
for a value of x  which is w ithout a nam e in th a t language: it is sufficient th a t th e given 
value of x  shall have a nam e in some suitable extension of the language— say, th a t 
obtained by adding to the vocabulary of the language a nam e of the given value of x , 
and allowing it to be substitutable for x  wherever x  occurs as a free variable. Likewise 
a form m ay have a sense value for a given concept of a value of x  if some suitable ex­
tension of the language contains a name having th a t concept as its sense.
I t is indeed possible, as we shall see later by p articu lar examples, to construct 
languages of so restricted a vocabulary as to contain no constants, but only variables and 
forms. B u t it would seem th a t th e  m ost natural way to  arrive at the m eaning of forms 
which occur in these languages is by contem plating languages which are extensions of 
them  and which do contain constants— or else, w hat is nearly the same thing, by 
allowing a tem porary change in the meaning of the variables ("fixing the values of the 
variables") so th a t they becom e constants.
“ W e ad o p t this term  from  H ilb ert (1922), W ilhelm Ackermann (1924), J. v. Neu­
mann (1927), H ilbert and A ckerm ann (1928), H ilbert and Bernays (1934). F or w hat we 
here call a free variable the term  re a l variable is also fam iliar, having been introduced 
by G iuseppe Peano in 1897 and afterw ard adopted by Russell (1908), but is less satis­
factory because it conflicts w ith the common use of "real variable" to mean a variable 
whose range is the real num bers.
As we shall see later (§06), a free variable m ust be distinguished from a b o u n d  varia b le 
(in the term inology of the H ilb ert school) or a p p a r e n t v a ria b le (Peano's term inology). 
The difference is th a t an expression containing x  as a free variable has values for various 
values of x , b u t an expression, containing a; as a bound or apparent variable only, has 
a m eaning which is independent of x — not in the sense of having the same value for 
every value of x , b u t in the sense th a t the assignm ent of particular values to x  is not a 
relevant procedure.

---


12
INTRODUCTION
spective values (or, if the expression so obtained has no denotation, then the 
form has no value for these particular values of x and y).
In the same way forms with three, four, and more free variables may be 
obtained. If a form contains a single free variable, we shall call it a singulary* 
form, if just two free variables, binary, if three, ternary, and so on. A form 
with exactly n different free variables is an n-ary form.
Two forms will be called concurrent if they agree in value—i.e., either 
have the same value or both have no value—for each assignment of values 
to their free variables. (Since the two forms may or may not have the same 
free variables, all the variables are to be considered together which have 
free occurrences in either form, and the forms are concurrent if they agree 
in value for every assignment of values to these variables.) A form will be 
called concurrent to a constant if, for every assignment of values to its free 
variables, its value is the same as the denotation of the constant. And two 
constants will be called concurrent if they have the same denotation.
Using the notion of concurrence, we may now add a fourth assumption, 
or principle of meaning, to the assumptions (l)-{3) of the last two para­
graphs of §01. This is an extension of (2) to the case of forms, as follows:
(4) In any constant or form, when a constituent constant or form is replaced 
by another concurrent to it, the entire resulting constant or form is con­
current to the original one.80 The significance of this principle will become 
clearer in connection with the use of operators and bound variables, explained 
in §06 below. It is to be taken, like (2), as a part of our explanation of the 
name relation, and thus a part of our theory of meaning.
As in the case of constant, we shall apply the terms variable and form 
also in the construction of uninterpreted calculi, introducing them by special 
definition for each such calculus in connection with which they are to be 
used. Ordinarily the symbols and expressions so designated will be ones 
which become variables and forms in our foregoing sense under one of the 
principal interpretations of the calculus as a language (see §07).
It should be emphasized that a variable, in our usage, is a symbol of a * 0
MWe follow W. V. Quine in adopting this etymologically more correct term, rather 
than the presently commoner "unary."
S0For completeness—using the notion of sense value explained in footnote 27 and 
extending it in obvious fashion to n-ary forms— we must also extend the assumption (1) 
to the case of forms, as follows. Let two forms be called sense-concurrent if they agree 
in sense value for each system of concepts of values of their free variables; let a form 
be called sense-concurrent to a constant if, for every system of concepts of values of its 
free variables, its sense value is the same as the sense of the constant; and let two con­
stants be called sense-concurrent if they express the same sense. Then: (5) In any con­
stant or form, when a constituent constant or form is replaced by another which issense- 
concurrent to it, the entire resulting constant or form is sense-concurrent to the original one.

---


§02]
C O N S T A N T S  A N D  V A R I A B L E S
13
certain kind31 rather than something (e.g., a number) which is denoted or 
otherwise meant by such symbol. Mathematical writers do speak of “variable 
real numbers/' or oftener “variable quantities/' but it seems best not to 
interpret these phrases literally. Objections to the idea that real numbers 
are to be divided into two sorts or classes, “constant real numbers'’ and 
“variable real numbers," have been clearly stated by Frege32 and need not 
be repeated here at length.33 * The fact is that a satisfactory theory has never 
been developed on this basis, and it is not easy to see how it might be done.
The m athem atical theory of real num bers provides a convenient source of 
exam ples in a system  of n o tatio n 84 whose general features are well established. 
T urning to this theory to illu strate the foregoing discussion, we cite as p articu lar 
exam ples of constants the ten expressions:
1
°. -  
«.
1 1  — 4 + 1  
n 
sin n jl
--- ---------------- 4$4 
g — g. — — , ------— .
2 n 
4te 
2ti 
Tip
L et us say th a t x and y are variables whose range is the real numbers, and m, n, r 
are variables whose range is the positive integers.35 The following are exam ples 
of forms:
•'Therefore, a variable (or more precisely, particular instances or occurrences of a 
variable) can be w ritten on paper— ju st as the figure 7 can be w ritten on paper, though 
the num ber 7 cannot be so w ritten except in the indirect sense of writing som ething 
which denotes it.
And sim ilarly constants and form s are symbols or expressions of certain kinds. I t is 
indeed usual to  speak also of num bers and physical quantities as “constants"— but 
this usage is not the sam e as th a t in which a constant can be contrasted with a variable, 
and we shall avoid it in this book.
“ See his contribution to F e s ts c h r ift L u d w ig  B o ltz m a n n  G ew id m et, 1904. (Frege's 
theory of functions as "ungesattigt," m entioned a t the end of his paper, is another m at­
ter, not necessarily connected w ith his im portant point about variables. It will not be 
adopted in this book, but rather we shall take a function— see §03—to be more nearly 
w hat Frege would call “ W erthverlauf einer Function.")
“ However, we m ention the following parallel to one uf Frege's examples. Shall we 
say th a t the usual list of seventeen nam es is a complete list of the Saxon kings of 
England, or only th a t it is a com plete list of the constant Saxon kings of England, and 
th a t account m ust be taken in addition of an indefinite num ber of variable Saxon 
kings? One of these variable Saxon kings would appear to  be a hum an being of a very 
striking sort, having been, say, a grown m an named Alfred in a .D. 876, and a boy nam ed 
Edw ard in a .d . 976.
According to the doctrine we would advocate (following Frege), there are ju st seven­
teen Saxon kings of England, from E gb ert to Harold, and neither a variable Saxon king 
nor an indeterm inate Saxon king is to be adm itted to swell the number. A nd th e like 
holds for the positive integers, for the real numbers, and for all other domains ab stract 
and concrete. V ariability or indeterm inacy, where such exists, is a m atter of language 
and attaches to sym bols or expressions.
*4We say "system  of notation" rath er than "language" because only the specifically 
numerical notations can be regarded as well established in ordinary m athem atical 
writing. They are usually supplem ented (for the statem ent of theorems and proofs) 
by one or another of the natural languages, according to the choice of the particular 
writer.
••Every positive integer is also a real num ber. I.e., the term s m ust be so understood 
for purposes of these illustrations.

---


14
I N T R O D U C T I O N
y> -
1
i
1
1 -
4
+
1
4ex, xe*t x*,
y ‘
i
X
2x
4x
x — x, n — n, —
X
y 
sin x
sin y
2 x ’
2 Y* 
X
i
Y
ye*
y
r
$  — m 
X
xy*
XY
mn
The forms on the first tw o lines aresingulary, each having one free variable, y ,x ,n , 
or r as the case m ay be. The forms on th e th ird  line are binary, th e first tw o having 
x and y as free variables, the third one x and r, the fourth one x and w .”  
T he constants
1
and
1 - 4 + 1
2n
4 n
are not identical, B u t th ey  are concurrent, since each denotes th e sam e num ber.87 
Sim ilarly the constants e — e and 0, though not identical, are concurrent because 
th e num bers e — e and 0 are identical. Sim ilarly — n/Zrc and — 1/2.
The form  xe*, for th e  value 0 of x, has th e  value 0. (Of course it is th e num ber 
0 th a t is here in question, not the constant 0, so th a t it is equally correct to  say 
th a t the form are*, for the value 0 of x, has th e value e — e; or th a t, for the value 
e — e of x, it has th e value 0; etc.) For the value 1 of x the form  xe* has the 
value e. For the value 4 of a: its value is 4e*, a  real num ber for w hich (as it happens) 
no simpler nam e is in standard use.
The form yex, for the values 0 and 4 of x and y respectively, has th e value 4.
s#To illustrate the rem ark of footnote 28, following are some exam ples of expressions 
containing bound variables:
The first two of these are constants, containing a; as a bound variable. The third is a 
singulary form, w ith 2 as a free variable and w  and « as bound variables.
A variable m ay have both free and bound occurrences in the sam e expression, An 
example is fix ^ d x , th e double use of th e letter x  constituting no am biguity. Other 
examples are the variable A x  in (D g sin z ) A x  and th e variable x  in x E  (A), if the notations 
D x s i n z  and 2i(A) are replaced by their equivalents
and
respectively.
*7W hether these two constants have the sam e sense (as well as the sam e denotation) 
is a question which depends for its answer on a general theory of equality of senses, 
such as we have not undertaken to discuss here—cf. footnote 16. I t is clear th a t Frege, 
though he form ulates no complete theory of equality of senses, would regard these two 
constants as having different senses. B ut a plausible case m ight be m ade out for sup­
posing that the two constants have the sam e sense, on some such ground as th a t the 
equation between them  expresses a necessary proposition or is tru e on logical grounds 
alone or the like. No doubt there is more than one meaning of “sense,” according to 
the criterion adopted for equality of senses, and the decision among them  is a m atter 
of convention and expediency.

---


For th e values 1 and l of a: and y it has the value l*1; or, w hat is the sam e thing, 
it has th e  value e.
The form  — yjxy, for th e values e and 2 of a: an d  y respectively, has the value
— l/e. F or the values e and e of a: and y, it has again the value — l/e. F o r the 
values e and 0 of a; and y it has no value, because of the non-existence of a quo­
tien t of 0 b y  0.
The form  — r/xr, for the values e and 2 of a; an d  r  respectively, has th e value
— l/e. B u t there is no value for th e values e an d  e of a: and r, because e is n o t 
in th e  range of y (e is not one of the possible values of y).
T he forms
§03] 
F U N C T I O N S
are concurrent, since they are both w ithout a value for the value 0 of x, and 
they have the sam e value for all other values of x. T he forms — 1/a: and — yjxy 
fail to b e concurrent, since th ey  disagree for th e value 0 of y (if the value of x 
is not 0). B u t the forms — \jx  and — yjxy are concurrent.
The form s — 1 jy and — 1/a: are not concurrent, as th ey  disagree, e.g., for the 
values 1 and 2 of a: and y respectively.
The form s x — x and w — w are concurrent to th e  sam e constant, nam ely 0,aB 
and are therefore also concurrent to each other.
The form s — xi2x and — y/2y are non-concurrent because of disagreem ent 
for the value 0 of x. The la tte r form, b u t not th e former, is concurrent to a 
constant, nam ely to — 1/2.
0 3 . F u n c t io n s . By a function—or, more explicitly, a one-valued singulary 
function—we shall understand an operation39 which, when applied to some­
thing as argument, yields a certain thing as the value of the function for that 
argument. It is not required that the function be applicable to every possible 
thing as argument, but rather it lies in the nature of any given function to 
be applicable to certain things and, when applied to one of them as argu­
ment, to yield a certain value. The things to which the function is applicable 
constitute the range of the function (or the range of arguments of the function) 
and the values constitute the range of values of the function. The function 
itself consists in the yielding or determination39 of a value from each argu­
ment in the range of the function.
As regards equality or identity of functions we make the decision which is
••Or also to any other constant which is concurrent to 0.
“ Of course the words "operation," "yielding," "determ ination" as here used are 
near-synonym s of "function" and therefore our statem ent, if taken as a definition, 
would be open to the suspicion of circularity. Throughout this Introduction, however, 
we are engaged in informal explanation rather th an  definition, and, for this purpose, 
elaboration by means of synonym s m ay be a useful procedure. U ltim ately, it seems, we 
m ust take the notion of function as prim itive or undefined, or else some related notion, 
such as th a t of a class. (We shall see later how it is possible to think of a class as a 
special case of a function, and also how classes m ay be used, in certain connections or 
for certain purposes, to replace and do the work of functions in general.)
1
and
2x
4a:

---


16
I N T R O D U C T I O N
usual in mathematics. Namely, functions are identical if they have the same 
range and have, for each argument in the range, the same value. In other 
words, we take the word ''function1' to mean what may otherwise be called 
a function in extension. If the way in which a function yields or produces 
its value from its argument is altered without causing any change either in 
the range of the function or in the value of the function for any argument, 
then the function remains the same; but the associated function concept, 
or concept determining the function (in the sense of §01), is thereby changed.
We shall speak of a function from a certain class to a certain class to mean 
a function which has the first class as its range and has all its values in the 
second class (though the second class may possibly be more extensive than 
the range of values of the function).
To denote the value of a function for a given argument, it is usual to 
write a name of the function, followed by a name of the argument between 
parentheses. And of course the same notation applies (mutatis mutandis) 
with a variable or a form in place of either one or both of the names. Thus 
if / is a function and x belongs to the range of /, then f(x) is the value of the 
function / for the argument a:.40
This is the usual notation for application of a function to an argument, 
and we shall often employ it. In some contexts (see Chapter X) we find it 
convenient to alter the notation by changing the position of the parentheses, 
so that we may write in the altered notation: if / is a function and x belongs 
to the range of f, then (fx) is the value of the function / for the argument x .
So far we have discussed only one-valued singulary functions (and have 
used the word "function" in this sense). Indeed no use will be made in this 
book of many-valued functions,41 and the reader must always understand
40This sentence exem plifies the use of variables to make general statem ents, which 
we assume is understood from  fam iliar m athem atical usage, though it has not yet been 
explained in this Introduction. (See the end of §06.)
41I t is the idea of a m any-valued (singulary) function th a t, for a fixed argum ent, 
there m ay be more th an  one value of the function. If a name of the function is w ritten, 
followed by a nam e of an argum ent between parentheses, the resulting expression is a 
common name (see footnote 6) denoting th e values of the function for th a t argum ent.
Though m any-valued functions seem to arise naturally in the m athem atical theories 
of real and complex num bers, objections im m ediately suggest them selves to the idea 
as }ust explained and are not easily overcome. Therefore it is usual to replace such m any­
valued functions in one w ay or another b y  one-valued functions. One m ethod is to 
replace a m any-valued singulary function by a corresponding one-valued binary prop­
ositional function or relation (§04). A nother m ethod is to replace th e  m any-valued 
function by a one-valued function whose values are classes, nam ely, th e value of the 
one-valued function for a given argum ent is the class of the values of th e m any-valued 
function for th a t argum ent. Still another m ethod is to change the range of the function, 
an argum ent for which th e function has « values giving w ay to « different argum ents 
for each of which the function has a different one of those « values (this is the standard 
role of the Riem ann surface in the theory of complex num bers).

---


§03]
F U N C T I O N S
17
“function" to mean a one-valued function. But we go on to explain functions 
of more than one argument.
A binary function, or function of two arguments,4Z is characterized by being 
applicable to two arguments in a certain order and yielding, when so applied, 
a certain value, the value of the function for those two arguments in that 
order. It is not required that the function be applicable to every two things 
as arguments; but rather, the function is applicable in certain cases to an 
ordered pair of things as arguments, and all such ordered pairs constitute 
the range of the function. The values constitute the range of values of the 
function.
Binary functions are identical (i.e., are the same function) if they have the 
same range and have, for each ordered pair of arguments which lies in that 
range, the same value.
To denote the value of a binary function for given arguments, it is usual 
to write a name of the function and then, between parentheses and separated 
by a comma, names of the arguments in order. Thus if / is a binary function 
and the ordered pair of x and y belongs to the range of /, then f{x, y) is the 
value of the function / for the arguments x and y in that order.
In the same way may be explained the notion of a ternary function, of a 
quaternary function, and so on. In general, an «-ary function is applied to 
n arguments in an order, and when so applied yields a value, provided the 
ordered system of n arguments is in the range of the function. The value of 
an n-ary function for given arguments is denoted by a name of the function 
followed, between parentheses and separated by commas, by names of the 
arguments in order.
Two binary functions <j> and yj are called converses, each of the other, in 
case the two following conditions are satisfied: (1) the ordered pair of z  and 
y belongs to the range of <j> if and only if the ordered pair of y and z  belongs 
to the range of yj; (2) for all z , y such that the ordered pair of z  and y belongs 
to the range of <£,43
y ) -- y>{y.x).
A binary function is called symmetric if it is identical with its converse. 
The notions of converse and of symmetry may also be extended to «-ary 
functions, several different converses and several different kinds of symme-
4aThough it is in common use we shall avoid the phrase "function of two variables" 
(and "function of three variables" etc.) because it tends to make confusion between 
arguments to which a function is applied and variables taking such arguments as values.
4aThe use of the sign — to express that things are identical is assumed fam iliar to 
the reader. We do not restrict this notation to the special case of numbers, b u t use it 
for identity generally.

---


18
INTRODUCTION
try appearing when the number of arguments is three or more (we need not 
stop over details of this).
We shall speak of a function of things of a certain kind to mean a function 
such that all the arguments to which it is applicable are of that kind. Thus 
a singulary function of real numbers, for instance, is a function from some 
dass of real numbers to some (arbitrary) class. A binary function of real 
numbers is a binary function whose range consists of ordered pairs of real 
numbers (not necessarily all ordered pairs of real numbers).
We shall use the phrase "____is a function o f _____filling the blanks
with forms,44 to mean what is more fully expressed as follows: "There 
exists a function / such that
____ -  /(_____)
for all____/' where the first two blanks are filled, in order, with the same
forms as before, and the third blank is filled with a complete list of the
free variables of those forms. Similarly we shall use "____is a function of
___ and_____filling the three blanks with forms, to stand for: "There
exists a binary function / such that
____ =  /(___________)
for all____where the first three blanks are filled, in order, with the same
forms as before, and the last blank is filled with a complete list of the free 
variables of those forms.45 And similar phraseology will also be used where 
the reference is to a function / of more than two arguments.
The phraseology just explained will also be used with the added statement
of a condition or restriction. For example, "____is a function o f____ and
___ i f _____/' where the first three blanks are filled with forms, and the
fourth is filled with the statement of a condition involving some or all of 
the free variables of those forms,46 stands for: "There exists a binary function 
/ such that
____ =  /(___________)
for a ll____for which____ ," where the first three blanks are filled, in order,
“ Our explanation assumes that neither of these forms has the particular letter / as 
one of its free variables. In the contrary case, the explanation is to be altered by using 
in place of the letter f as it appears in the text some variable (with appropriate range) 
which is not a free variable of either form.
“ The theory of real numbers again serving as a source of examples, it is thus true 
that a:* + y9 is a function of x •+• y and xy, But it is false that a?* -f 
— xy9 -f- y9 
is a function of x -f y and xy (as is easily seen on the ground that the form x9 +  z*y — 
xy9 +  y* is not symmetric). Again, x* -f y* +  ** +  4ar*y -f- 4xy9 +  4x9z +  4xz9 +  
-f- 4yz9 is a function of x -f- y -f * and xy -f xz +  yz. But x* +  y4 +  s4 is not 
a function of x +  V 4- z and xy +  xz -f yz.
“ Thus with a propositional form in the sense of §04 below.

---


§03]
F U N C T I O N S
19
with the same forms as before, the fourth blank is filled with a complete 
list of the free variables of those forms, and the fifth blank is filled in the 
same way as the fourth blank was before.47
Also the same phraseology, explained in the two preceding paragraphs, 
will be used with common names48 in place of forms. In this case the forms 
which the common names represent have to be supplied from the context. 
For example, the statement that “The density of helium gas is a function 
of the temperature and the pressure” is to be understood as meaning the same 
as "The density of his a function of the temperature of h and the pressure of h ” 
where the three italicized forms replace the three original italicized common 
names, and where A is a variable whose values are instantaneous bits of 
helium gas (and whose range consists of all such). Or to avoid introducing the 
variable h with so special a range, we may understand instead: “The density 
of b is a function of the temperature of b and the pressure of b if b is an 
instantaneous bit of helium gas.” Similarly the statement at the end of §01 
that the denotation of a name is a function of the sense means more explic­
itly (the reference being to a fixed language) that there exists a function / 
such that
denotation of N ~  /(sense of N)
for all names N for which there is a denotation.
It remains now to discuss the relationship between functions, in the ab­
stract sense that we have been explaining, and forms, in the sense of the pre­
ceding section (§02).
If we suppose the language fixed, every singulary form has corresponding 
to it a function / (which we shall call the associated function of the form) by 
the rule that the value of / for an argument x is the same as the value of the 
form for the value x of the free variable of the form, the range of / consisting 
of all x ’s such that the form has a value for the value x of its free variable.49
‘’Accordingly it is true, for example, that: x3 4- z ly — xy2 -f y* is a function of x 4- y 
and xy if x ^  y. For the special case that the variables have a range consisting of real or 
complex numbers, a geometric terminology is often used, thus: x* 4- x%y — xy* 4- y3 
is a function of x 4“ y and xy in the half-plane x ^  y.
"See footnotes 4, 0.
wFor example, in the theory of real numbers, the form £(** — e~x) determines the 
function sinh as its associated function, by the rule th at the value of smh for an argu­
ment x is 
— «-*). The range of sinh then consists of all x's (i.e., all real numbers x) 
for which tye* — c"*) has a value. In other words, as it happens in this particular case, 
the range consists of all real numbers.
Of course the free variable of the form need not be the particular letter x, and indeed 
it may be clearer to take an example in which the free variable is some other letter.
Thus the form i(«v — e~v) determines the function sinh as its associated function, 
by the rule that the value of sinh for an argument x is the same as the value of the form 
i ( 4 v _  e~>) for the value x of the variable y. (I.e., in particular, the value of sinh for

---


20
I N T R O D U C T I O N
But, still with reference to a fixed language, not every function is necessarily 
the associated function of some form.60
It follows that two concurrent singulary forms with the same free variable 
have the same associated function. Also two singulary forms have the same 
associated function if they differ only by alphabetic change of the free vari­
able,51 i.e., if one is obtained from the other by substituting everywhere 
for its free variable some other variable with the same range—with, however, 
the proviso {the need of which will become clearer later) that the substituted 
variable must remain a free variable at every one of its occurrences resulting 
from the substitution.
As a notation for {i.e., to denote) the associated function of a singulary 
form having, say, x as its free variable, we write the form itself with the 
letters he prefixed. And of course likewise with any other variable in place of 
x.52 Parentheses are to be supplied as necessary.53
the argument 2 is the same as the value of the form £(«?v — e~v) for the value 2 of the 
variable y; and so on for each different argument x that may be assigned.)
Ordinarily, just the equation
sinh (a:) — £(e® — e~*)
is written as sufficient indication of the foregoing. And this equation may even be called 
a definition of sinh, in the sense of footnote 168, (1) or (3).
“ According to classical real-number theory, the singulary functions from real num­
bers to real numbers (or even just the analytic singulary functions) are non-enumerable. 
Since the forms in a particular language are always enumerable, it follows th at there is 
no language or system of notation in which every singulary function from real numbers 
to real numbers is the associated function of some form.
Because of the non-enumerability of the real numbers themselves, it is even impossible 
in any language to provide proper names of all the real numbers. (Such a thing as, 
e.g., an infinite decimal expansion must not be considered a name of the corresponding 
real number, as of course an infinite expansion cannot ever be written out in full, or 
included as a part of any actually written or spoken sentence.)
#1E,g., as appears in footnote 49, the forms £(«* — c-’*) and 
— e~*) have the 
same associated function.
“ Thus the expressions Xx{\{e* — e~m))t Ay(£(ev “  e~v)), sinh are all three synony­
mous, having not only the same denotation (namely the function sinh), but also the 
same sense, even under the severest criterion of sameness of sense.
(In saying this we are supposing a language or system of notation in which the two 
different expressions sinh and Xx(i{ez — e~z)) both occur. However, the very fact of 
synonymy shows th at the expression sinh is dispensable in principle: except for con­
siderations of convenience, it could always be replaced by the longer expression 
kx(\{e* — $-*)). In constructing a formalized language, we prefer to avoid such dupli­
cations of notation so far as readily possible. See §11.)
The expressions Xx(\(ez — c- *)) and ky(\(e* — a- *)) contain the variables x and y 
respectively, as bound variables in the sense of footnotes 28, 36 (and of §06 below). 
For, according to the meaning just explained for them, these expressions are constants, 
not singulary forms. But of course the expression £(e* — e~m) is a singulary form, with 
x as a free variable.
The meaning of such an expression as Xx(yex), formed from the binary form yeB 
by prefixing Xx, now follows as a consequence of the explanation about variables and 
forms in §02. In this expression, a; is a bound variable and y is a free variable, and the

---


§03]
F U N C T I O N S
21
As an obvious extension of this notation, we shall also prefix the letters 
Xx {ky, etc.) to any constant as a notation for the function whose value is 
the same for all arguments and is the denotation of the constant, the range 
of the function being the same as the range of the variable r.54 This function 
will be called an associated singulary function of the constant, by analogy 
with the terminology "'associated function of a form," though there is the 
difference that the same constant may have various associated functions 
with different ranges. Any function whose value is the same for all argu­
ments will be called a constant function (without regard to any question 
whether it is an associated function of a constant, in some particular language 
under consideration).65
Analogous to the associated function of a singulary form, a binary form 
has two associated binary functions, one for each of the two orders in which 
the two free variables may be considered—or better, one for each of the two 
ways in which a pair of arguments of the function may be assigned as values 
to the two free variables of the form.
The two associated functions of a binary form are identical, and thus 
reduce to one function, if and only if they are symmetric. In this case the 
binary form itself is also called symmetric.™
Likewise an n-ary form has n\ associated n-ary functions, one for each 
of the permutations of its free variables. Some of these associated functions 
are identical in certain cases of symmetry.
Likewise a constant has associated m-ary functions, for m — 1, 2, 3, 
,
by an obvious extension of the explanation already made for the special 
case m =  I. And by a still further extension of this we may speak of the 
associated w-ary functions of an n-ary form, when m >  n. In particular a
expression is a singulary form whose values are singulary functions, From it, by pre­
fixing Xy, we obtain a constant, denoting a singulary function, and the range of values 
of this singulary function consists of singulary functions.
Ialn constructing a formalized language, the manner in which parentheses are to be 
put in has to be specified with more care. As a m atter of fact this will be done, as we 
shall see, not by associating parentheses with the notation Xx. but by suitable provision 
for parentheses (or brackets) in connection with various other notations which may 
occur in the form to which Xx is prefixed.
••Thus in connection with real-number theory we use Xx2 as a notation for the func­
tion whose range consists of all real numbers and whose value is 2 for every argument.
••Note should also be taken of expressions in which the variable after X is not the 
same as the free variable of the form which follows; thus, for example, Xy(\(e* — e~9)). 
As is seen from the explanation in §02, this expression is a singulary form w ith x as 
its free variable, the values of the form being constant functions. For the value 0 of x, 
e.g., the form Ay(i(e* — *“*)) has as its value the constant function Xy0.
In both expressions. Xy{i{e9 — e~x)) and XyO, y is a bound or apparent variable.
MWe have already used this term, as applied to forms, in footnote 45, assuming the 
reader's understanding of it as familiar mathematical terminology.

---


22
INTRODUCTION
singulary form has not only an associated singulary function but also 
associated binary functions, associated ternary functions, and so on. 
(When, however, we speak simply of the associated function of a singu­
lary form, we shall mean the associated singulary function.)
The notation by means of A for the associated functions of a form, as 
introduced above for singulary functions, is readily extended to the case of 
w-ary functions,” but we shall not have occasion to use such extension in this 
book. The passage from a form to an associated function (for which the 
A-notation provides a symbolism) we shall speak of as abstraction or, more 
explicitly, m-ary functional abstraction (if the associated function is w-ary).
Historically the notion of a function was of gradual growth in mathe­
matics, and its beginning is difficult to trace. The particular word "function1' 
was first introduced by G. W. v. Leibniz and was adopted from him by 
Jean Bernoulli. The notation f(x)t or fx, with a letter such as / in the role 
of a function variable, was introduced by A. C. Clairaut and by Leonhard 
Euler. But early accounts of the notion of function do not sufficiently sep­
arate it from that of an expression containing free variables (or a form). 
Thus Euler explains a function of a variable quantity by identifying it with 
an analytic expression,58 i.e., a form in some standard system of mathemat­
ical notation. The abstract notion of a function is usually attributed by 
historians of mathematics to G. Lejeune Dirichlet, who in 1837 was led by 
his study of Fourier series to a major generalization in freeing the idea of a 
function from its former dependence on a mathematical expression or law 
of circumscribed kind.59 Dirichlet's notion of a function was adopted by 
Bernhard Riemann (1851),®° by Hermann Hankel (1870),®1 and indeed by 
mathematicians generally. But two important steps remained to be taken by
*’This has been done by Carnap in Notes for Symbolic Logic (1937) and elsewhere.
IB“ Functio quantitatis variabilis est expressio analytica quomodocunque composita ex 
ilia quantitate variabili et numeris seu quantitatibus constantibus. Omnis ergo expressio 
analytica, in qua praeter quantitatem  variabilem g oranes quantitates illam expressio- 
nem componentes sunt constantes, erit functio ipsius z . . . Functio ergo quantitatis 
variabilis ipsa erit quantitas v ariabilisIntroductio in Analysin Infinitorum (1748), 
p. 4; Opera, ser. 1, vol. 8, p. 18. See further footnote 82.
wSee his Werke, vol. 1, p. 135. It is not im portant th a t Dirichlet restricts his state­
ment a t this particular place to continuous functions, since it is clear from other pas­
sages in his writings that the same generality is allowed to discontinuous functions. On 
page 132 of the same volume is his well-known example of a function from real numbers 
to real numbers which has exactly two values, one for rational arguments and one for 
irrational arguments.
Dirichlet's generalization had been partially anticipated by Euler in 1749 (see an 
account by H. Burkhardt in Jahresbericht der Deutscken Matkematiker~Vereinigung, 
vol. 10 p art 2 (1908), pp. 13-14) and later by J. B. J. Fourier (see his Oeuvres, vol. 1, 
pp. 207, 209, 230-232).
n Werke, pp. 3-4.
n In a paper reprinted in the Mathematische Annalen, vol. 20 (1882), pp. 83-112.

---


§04] 
P R O P O S I T I O N S  A N D  P R O P O S I T I O N A L  F U N C T I O N S  
23
Frege (in his Begriffssckrift of 1879 and later publications): (i) the elimina­
tion of the dubious notion of a variable quantity in favor of the variable as 
a kind of symbol;*2 (ii) the admission of functions of arbitrary range by 
removing the restriction that the arguments and values of a function be 
numbers. Closely associated with (ii) is Frege's introduction of the prop­
ositional function (in 1879), a notion which we go on to explain in the 
next section.
04. Propositions and propositional functions. According to gram­
marians, the unit of expression in the natural languages is the sentence, 
an aggregation of words which makes complete sense or expresses a 
complete thought. When the complete thought expressed is that of 
an assertion, the sentence is called a declarative sentence. In what follows 
we shall have occasion to refer only to declarative sentences, and the 
simple word "sentence” is to be understood always as meaning a declarative 
sentence.83
We shall carry over the term sentence from the natural languages 
also to the formalized languages. For logistic systems in the sense of 
§07—uninterpreted calculi—the term sentence will be introduced by special 
definition in each case, but always with the intention that the expres­
sions defined to be sentences are those which will become sentences in 
our foregoing sense under interpretations of the calculus as a formalized 
language.84
In order to give an account of the meaning of sentences, we shall adopt a 
theory due to Frege according to which sentences are names of a certain 
kind. This seems unnatural at first sight, because the most conspicuous 
use of sentences (and indeed the one by which we have just identified or
“ The passage quoted from Euler in footnote 58 reads as if his variable quantity were 
a kind of symbol or expression. But this is not consistent with statem ents made else­
where in the same work which are essential to Euler's use of the notion of function 
—e.g., "Si fuerii y junctio quaecunque ipsius z, turn vicissim z erii functio ipsius y" 
(Opera, p. 24), “Sed omnis transformatio consistit in alio modo eandem functionem 
exprimendi, quemadmodum ex Algebra constat eandem quantitatem  per plures 
diversas formas exprimi posse" (Opera, p. 32).
••The question may be raised whether, say, an interrogative or an imperative logic 
is possible, in which interrogative or imperative sentences and what they express 
(questions or commands) have roles analogous to those of declarative sentences and 
propositions in logic of ordinary kind. And some tentative proposals have in fact been 
made towards an imperative logic, and also towards an optative logic or logic of wishes. 
But these matters are beyond the scope of this book.
MCf. the explanation in §02 regarding the use in connection with logistic systems of 
the term s constant, variable, form. An analogous explanation applies to a number of 
term s of like kind to be introduced below—in particular, propositional variable, prop­
ositional form, operator, quantifier, bound variable, connective.

---


24
I N T R O D U C T I O N
described them) is not barely to name something but to make an assertion. 
Nevertheless it is possible to regard sentences as names by distinguishing 
between the assertive use of a sentence on the one hand, and its non-asser- 
tive use, on the other hand, as a name and a constituent of a longer sentence 
(just as other names are used). Even when a sentence is simply asserted, we 
shall hold that it is still a name, though used in a way not possible for other 
names.85
An important advantage of regarding sentences as names is that all the 
ideas and explanations of §§01-03 can then be taken over at once and applied 
to sentences, and related matters, as a special case. Else we should have to 
develop independently a theory of the meaning of sentences; and in the 
course of this, it seems, the developments of these three sections would be 
so closely paralleled that in the end the identification of sentences as a kind 
of names (though not demonstrated) would be very forcefully suggested as 
a means of simplifying and unifying the theory. In particular we shall require 
variables for which sentences may be substituted, forms which become 
sentences upon replacing their free variables by appropriate constants, and 
associated functions of such forms—things which, on the theory of sentences 
as names, fit naturally into their proper place in the scheme set forth in 
§§02-03.
Granted that sentences are names, we go on, in the light of the discussion 
in §01, to consider the denotation and the sense of sentences.
As a consequence of the principle (2), stated in the next to last paragraph 
of §01, examples readily present themselves of sentences which, though in 
some sense of different meaning, must apparently have the same denotation. 
Thus the denotation (in English) of "Sir Walter Scott is the author of 
Wav&rley” must be the same as that of "Sir Walter Scott is Sir Walter Scott/*
49To distinguish the non-assertive use of a sentence and the assertive use, especially 
in a formalized language, Frege wrote a horizontal line, — , before the sentence in the 
former case, and the character 
before it in the latter case, the addition of the vertical
line thus serving as a sign of assertion. Russell, and Whitehead and Russell in Principia. 
Mathematica, did not follow Frege’s use of the horizontal line before non-asserted 
sentences, but did take over the character 
in the role of an assertion sign.
(Frege also used the horizontal line before names other than sentences, the expression 
so formed being a false sentence. But this is a feature of his notation which need not 
concern us here.)
In this book we shall not make use of a special assertion sign, but (in a formalized 
language) shall employ the mere writing of a sentence displayed on a separate line or 
lines as sufficient indication of its assertion. This is possible because sentences used 
non-assertively are always constituent parts of asserted sentences, and because of the 
availability of a two-dimensional arrangement on the printed page. (In a one-dimen­
sional arrangement the assertion sign would indeed be necessary, if only as punctuation,)
The sign p which is employed below, in Chapter I and later chapters, is not the Frege- 
Russcll assertion sign, but has a wholly different use.

---


§04] 
P R O P O S I T I O N S  A N D  P R O P O S I T I O N A L  F U N C T I O N S
25
the name "the author of Waverley” being replaced by another which has 
the same denotation. Again the sentence "Sir Walter Scott is the author of 
Waverley” must have the same denotation as the sentence "Sir Walter 
Scott is the man who wrote twenty-nine Waverley Novels altogether/’ since 
the name "the author of Waverley” is replaced by another name of the same 
person; the latter sentence, it is plausible to suppose, if it is not synonymous 
with "The number, such that Sir Walter Scott is the man who wrote that 
many Waverley Novels altogether, is twenty-nine/' is at least so nearly 
so as to ensure its having the same denotation; and from this last sentence 
in turn, replacing the complete subject by another name of the same number, 
we obtain, as still having the same denotation, the sentence "The number of 
counties in Utah is twenty-nine.”
Now the two sentences, "Sir Walter Scott is the author of Waverley” 
and "The number of counties in Utah is twenty-nine,” though they have 
the same denotation according to the preceding line of reasoning, seem 
actually to have very little in common. The most striking thing that they 
do have in common is that both are true. Elaboration of examples of this 
kind leads us quickly to the conclusion, as at least plausible, that all true 
sentences have the same denotation. And parallel examples may be used in 
the same way to suggest that all false sentences have the same denotation 
(e.g,, "Sir Walter Scott is not the author of Waverley” must have the same 
denotation as "Sir Walter Scott is not Sir Walter Scott”).
Therefore, with Frege, we postulate68 two abstract objects called truth- 
values, one of them being truth and the other one falsehood. And we declare 
all true sentences to denote the truth-value truth, and all false sentences 
to denote the truth-value falsehood. In alternative phraseology, we shall 
also speak of a sentence as having the truth-value truth (if it is true) or 
having the truth-value falsehood (if it is false).87
The sense of a sentence may be described as that which is grasped when 
one understands the sentence, or as that which two sentences in different 
languages must have in common in order to be correct translations each of 
the other. As in the case of names generally, it is possible to grasp the sense * •
••To Frege, as a thoroughgoing Platonic realist, our use of the word ‘'postulate1' 
here would not be acceptable. It would represent his position better to say that the 
situation indicates that there are two such things as truth and falsehood (das Wahre 
and das Falsehe).
•rThe explicit use of two truth-values appears for the first time in a paper by C. S. 
Peirce in the American Journal of Mathematics, vol. 7 (1885), pp. 180-202 (or see his 
Collected Papers, vol. 3, pp. 210-238). Frege’s first use of truth-values is in his Funktion 
und Begriff of 1891 and in his paper of 1892 which is cited in footnote 5; it is in these 
that the account of sentences as names of truth-values is 'first put forward.

---


26
I N T R O D U C T I O N
of a sentence without therefore necessarily having knowledge of its denota­
tion (truth-value) otherwise than as determined by this sense. In particular, 
though the sense is grasped, it may sometimes remain unknown whether the 
denotation is truth.
Any concept of a truth-value, provided that being a truth-value is contained 
in the concept, and whether or not it is the sense of some actually available 
sentence in a particular language under consideration, we shall call a prop­
osition, translating thus Frege's Gedanke.
Therefore a proposition, as we use the term, is an abstract object of the 
same general category as a class, a number, or a function. It has not the 
psychological character of William of Ockham's propositio menialis or of 
the traditional judgment: in the words of Frege, explaining his term 
Gedanke, it is "nicht das subjective Thun des Denkens, sondem dessen 
objectiven Inhalt, der fahig ist, gemeinsames Eigenthum von Vielen zu 
sein."
Traditional (post-Scholastic) logicians were wont to define a proposition 
as a judgment expressed in words, thus as a linguistic entity, either a sen­
tence or a sentence taken in association with its meaning.®8 But in non­
technical English the word has long been used rather for the meaning (in 
our view the sense) of a sentence,60 and logicians have latterly come to 
accept this as the technical meaning of "proposition." This is the happy 
result of a process which, historically, must have been due in part to sheer 
confusion between the sentence in itself and the meaning of the sentence. 
It provides in English a distinction not easily expressed in some other 
languages, and makes possible a translation of Frege's Gedanke which is 
less misleading than the word "thought."70
According to our usage, every proposition determines or is a concept of
“ E.g., in Isaac W atts's Logiok, 1725: “A Proposition is a Sentence wherein two or 
more Ideas or Terms are joined or disjoined by one Affirmation or N egation.. . .  In 
describing a Proposition I use the Word Terms as well as Ideas, because when mere 
Ideas are join'd in the Mind without Words, it is rather called a Judgment; but when 
clothed with Words, it is called a Proposition, even tho' it be in the Mind only, as well 
as when it is expressed by speaking or W riting.” Again in Richard W hately's Elements 
of Logic, 1820; "The second p art of Logic treats of the proposition; which is, '/udgwtfw/ 
expressed in words.1 A Proposition is defined logically ‘a sentence indicative/ i.e. 
affirming or denying; (this excludes commands and questions,)” Here W hately is follow­
ing in part the Latin of Henry Aldrich (1691), In fact these passages show no im portant 
advance over Petrus Hispanus, who wrote a half dullennium earlier, but they are quoted 
here apropos of the history of the word ''proposition” in English.
“ Consider, for example, the incongruous result obtained by substituting the words 
"declarative sentence” for the word "proposition” in Lincoln's Gettysburg Address.
™For a further account of the history of the m atter, we refer to Carnap's Introduction 
to Semantics, 1942, pp. 235-236; and see also R. M. Eaton, General Logic, 1931,

---


§04] 
P R O P O S I T I O N S  A N D  P R O P O S I T I O N A L  F U N C T I O N S
27
(or, as we shall also say, has) some truth-value. It is, however, a somewhat 
arbitrary decision that we deny the name proposition to senses of such 
sentences (of the natural languages) as express a sense but have no truth- 
value.71 To this extent our use of proposition deviates from Frege's 
use of Gedanke. But the question will not arise in connection with the 
formalized languages which we shall study, as these languages will be 
so constructed that every name—and in particular every sentence—has 
a denotation.
A proposition is then true if it determines or has the truth-value truth, 
false if it has the truth-value falsehood. When a sentence expressing a prop­
osition is asserted we shall say that the proposition itself is thereby 
asserted.12
A variable whose range is the two truth-values—thus a variable for which 
sentences (expressing propositions) may appropriately be substituted—is 
called a propositional variable. We shall not have occasion to use variables
n By the remark of footnote 22, such are sentences which contain non-obliquely one 
or more names that express a sense but lack a denotation- -or so, following Frege, we 
shall take them. Examples are: "The present king of France is bald"; "The present king 
of France is not bald"; "The author of Pnncipia Matkematica was born in 1861." 
{As to the last example, it is true that the phrase "the author of Principia Mathematica“ 
in some appropriate supporting context may be an ellipsis for something like "the author 
of Principia Matkematica 
was just mentioned" and therefore have a denotation; but 
we here suppose that there is no such supporting context, so that the phrase can only 
mean "the one and only author of Principia Matkematica ’ and therefore have no 
denotation.)
To sentences as a special case of names, of course the second remark of footnote 22 
also applies. Thus we understand as true (and containing oblique occurrences of names) 
each of the sentences: "Lady Ham ilton was like Aphrodite in beauty"; "The fountain 
of youth is not located in Florida"; "The present king of France does not exist." 
Cases of doubt whether a sentence has a truth-value or not are also not difficult to 
find in this connection, the exact meaning of various phraseologies in the natural 
languages being often insufficiently determinate for a decision.
’•Notice the following distinction. The statem ent th at a certain proposition was 
asserted (say on such and such an occasion) need not reveal what language was used 
nor make any reference to a particular language. But the statement th at a certain 
sentence was asserted does not convey the meaning of the transaction unless it is added 
what language was used, For not only may the same proposition be expressed by differ­
ent sentences in different languages, but also the same sentence may be used to assert 
different propositions according to what language the user intends. It is beside the 
point th at the latter situation is comparatively rare in the principal known natural 
languages; it is not rare when all possible languages are taken into account.
Thus, if the language is English, the statement, "Seneca said that man is a rational 
animal," conveys the proposition that Seneca asserted but not the information what 
language he used. On the other hand the statem ent, "Seneca wrote. ‘Rationale enim 
animal est homo,' M gives only the information what succession of letters he set down, 
not what proposition he asserted. (The reader may guess or know from other sources 
that Seneca used Latin, but this is neither said nor implied in the given statem ent—for 
there are many languages besides Latin in which this succession of letters spells a de­
clarative sentence and, for all th at thou and T know, one of them may once have been 
in actual use.)

---


28
I N T R O D U C T I O N
whose values are propositions, but we would suggest the term intensional 
propositional variable for these,
A form whose values are truth-values (and which therefore becomes a 
sentence when its free variables are replaced by appropriate constants) is 
a propositional form. Usage sanctions this term73 rather than “truth-value 
form,” thus naming the form rather by what is expressed, when constants 
replace the variables, than by what is denoted.
A propositional form is said to be satisfied by a value of its free variable, 
or a system of values of its free variables, if its value for those values of its 
free variables is truth. (More explicitly, we should speak of a system of 
values of variables as satisfying a given propositional form in a given 
language, but the reference to the particular language may often be omitted 
as clear from the context.) A propositional form may also be said to be true 
or false for a given value of its free variable, or system of values of its free 
variables, according as its value for those values of its free variables is truth 
or falsehood.
A function whose range of values consists exclusively of truth-values, and 
thus in particular any associated function of a propositional form, is a 
propositional function. Here again, established usage sanctions “proposi­
tional function”74 rather than “truth-value function,” though the latter 
term would be the one analogous to, e.g., the term “ numerical function” for 
a function whose values are numbers.
A propositional function is said to be satisfied by an argument (or 
ordered system of arguments) if its value for that argument (or ordered 
system of arguments) is truth. Or synonymously we may say that a 
propositional function holds for a particular argument or ordered system 
of arguments.
From its use in mathematics, we assume that the notion of a class is 
already at least informally familiar to the reader. (The words set and 
are ordinarily used as synonymous with class, but we shall not 
follow this usage, because in connection with the Zermelo axiomatic set
7sCf. footnote 26,
74This statem ent seems to be on the whole just, though the issue is much obscured by 
divergencies among different writers as to the theory of meaning adopted and in the 
accounts given of the notions of function and proposition. The idea of the propositional 
function as an analogue of the numerical function of mathematical analysis originated 
with Frege, but the term ’‘propositional” function is originally Russell's. Russell’s 
early use of this term is not wholly dear. In his introduction to the second edition of 
Principia Mathemaiica (1926) he decides in favor of the meaning which we are adopting 
here, or very nearly that.

---


§04] 
P R O P O S I T I O N S  A N D  P R O P O S I T I O N A L  F U N C T I O N S  
29
theory78 we shall wish later to give the word set a special meaning, somewhat 
different from that of c&wrs.) We recall that a class is something which has 
or may have members, and that classes are considered identical if and only 
if they have exactly the same members. Moreover it is usual mathematical 
practice to take any given singulary propositional form as having associated 
with it a class, namely the class whose members are those Values of the free 
variable for which the form is true.
In connection with the functional calculi of Chapters III—VI, or rather, 
with the formalized languages obtained from them by adopting one of the 
indicated principal interpretations (§07), it turns out that we may secure 
everything necessary about classes by just identifying a class with a 
singulary propositional function, and membership in the class with 
satisfaction of the singulary propositional function. We shall consequently 
make this identification, on the ground that no purpose is served by 
maintaining a distinction between classes and singulary propositional 
functions.
We must add at once that the notion of a class obtained by thus identi­
fying classes with singulary propositional functions does not quite coincide 
with the informal notion of a class which we first described, because it does 
not fully preserve the principle that classes are identical if they have the 
same members. Rather, it is necessary to take into account also the range- 
members of a class {constituting, i.e., the range of the singulary propositional 
function). And only when the range-members are given to be the same is the 
principle preserved that classes are identical if they have the same members. 
This or some other departure from the informal notion of a class is in fact 
necessary, because, as we shall see later,78 the informal notion—in the pres­
ence of some other assumptions difficult to avoid—is self-inconsistent and 
leads to antinomies. (The sets of Zermelo set theory preserve the principle 
that sets having the same members are identical, but at the sacrifice of the 
principle that an arbitrary singulary propositional form has an associated 
set.)
Since, then, a class is a singulary propositional function, we speak 
of the range of the class just as we do of the propositional function 
(i.e., it is the same thing). We think of the range as being itself a class, 
having as members the range-members of the given class, and having the 
same range-members.
(In any particular discussion hereafter in which classes are introduced,
"Chapter XI.
TIIn Chapter VI.

---


30
INTRODUCTION
and in the absence of any indication to the contrary, it is to be understood 
that there is a fixed range determined in advance and that all classes have 
this same range.)
R e l a t i o n s  may be similarly accounted for by identifying them with binary 
propositional functions, the relation being said to h o ld  b e tw e e n  an ordered 
pair of things (or the things being said to s t a n d  i n  that relation, or to b e a r  
that relation one to the other) if the binary propositional function is satisfied 
by the ordered pair. Given that the ranges are the same, this makes two re­
lations identical if and only if they hold between the same ordered pairs, 
and to indicate this we may speak more explicitly of a r e l a ti o n  i n  e x t e n s i o n —  
using this term as synonymous with r e l a ti o n .
A p r o p e r t y , as ordinarily understood, differs from a class only or chiefly 
in that two properties may be different though the classes determined by 
them are the same (where the class determined by a property is the class 
whose members are the things that have that property). Therefore we 
identify a property with a c la s s  c o n c e p t, or concept of a class in the sense of 
§01. And two properties are said to c o in c id e  i n  e x t e n s i o n  if they determine 
the same class.
Similarly, a r e la tio n  i n  i n t e n s i o n  is a r e l a ti o n  c o n c e p t, or concept of a 
relation in extension.
To tu rn  once more for illustrative purposes to th e theory of real num bers and 
its notations, the following are exam ples of propositional forms:
sin x  =  0, 
sin x  =  2,
e x >  0, 
e z >  1, 
x  >  0,
e  >  0, 
e  <  0,
x* +  y *  
2 x y , 
x ^ y ,
\x  —  y \ <  /, 
\x — y \ <  e,
If \x  — y \ <  3  then (sin x  —  sin y \ <  e.
H ere we are using x , y , t as variables whose range is th e  real num bers, and e an d  <5 
as variables whose range is th e positive real num bers. T h e seven form s on th e  
first three lines are exam ples of singulary propositional forms, Those on th e 
fourth line are binary, on th e fifth  line ternary, while on th e  last line is an exam ­
ple of a q u atern ary  propositional form.
E ach of th e  singulary propositional forms has an associated class. T hus w ith 
th e form  sin x  =  0 is associated th e  class of those real num bers whose sine is 0, 
i.e„ the class whose range is th e real num bers and w hose m em bers are 0, n , — n , 
2n , — 2n , 3?r, and so on. As explained, we identify this class w ith the p ro p ­
ositional function ^x(sin x  =  0), or in other w ords th e  function from  real n u m ­
bers to tru th -v alu es which has for an y  argum ent x  th e value sin x  =  0.

---


§05]
I M P R O P E R  S Y M B O L S .  C O N N E C T I V E S
31
The two propositional forms e* >  1 and x >  0 have the sam e associated 
class, nam ely, the class whose range is th e  real num bers and w hose mem bers 
are the positive real num bers. This class is identified w ith eith er ).x(ex >  1) 
o r Xx(x >  0), these tw o propositional functions being identical w ith each other 
by the convention a b o u t id en tity  of functions adopted in §03.
Since the propositional form sin x =  2 has the value falsehood for every value 
of x, th e associated class &c(sin x =  2) has no members.
A class w hich has no m em bers is called a null class or an empty class. From  
our conventions ab o u t id en tity  of propositional functions and of classes, if the 
range is given, it follows th a t there is only one null class. B ut, o.g., the range of 
th e null class associated w ith the form  sin x =  2 and the range of the null 
class associated w ith th e  form s <  0 are n o t the sam e: the form er range is the 
real num bers, and the la tte r range is the positive real num bers.77 W e shall speak 
respectively of the “ null class of real num bers" and of the “ null class of positive 
real num bers."
A class w hich coincides w ith its range is called a universal clas> For example, 
th e  class associated w ith the form e x >  0 is the universal class of real num bers; 
an d  the class associated w ith the form  e >  0 is the universal class of positive 
real num bers.
The binary propositional forms x 3 *{■ y 3 = 3xy and x #  y are b o th  sym m etric 
and therefore each have one associated binary propositional function or relation. 
In  particular, the associated relation of the form  x 
y is the relation of diversity 
betw een real num bers; or in other words the relation which has th e pairs of real 
num bers as its range, w hich any two different real num bers bear to each other, 
and which no real num ber bears to itself.
The tern ary  propositional forms j.r — y x <  t and jr — y\ <  ? have each three 
associated tern ary  propositional functions7" (being sym m etric in x and y). All 
six of these propositional functions are different, bur an appropriately chosen 
p a ir of them , one associated w ith each form , will be found to agree in value for 
all ordered triples of argum ents which are in the range of both, differing only in 
th a t the first one has the value falsehood for certain ordered triples of argum ents 
w hich are n o t in th e range of the oth er
05. Improper symbols, connectives. When the expressions, especially 
the sentences, of a language are analyzed into the single symbols of which 
they consist, symbols which may be regarded as indivisible in the sense that
’’According to the informal notion that classes with the same members are identical, 
it would be true absolutely that there is only one null class. The distinction of null 
classes with different ranges was introduced by Russell in 1908 as a part of his theory 
of types (see Chapter VI). The same thing had previously been done by Ernst Schrbder 
in the first volume of his Algebra der Logih (1890), though with a very different moti­
vation.
7,We may also occasionally use the term ternary relation (and quaternary relation etc). 
But the simple term relation will be reserved for the special case of a binary relation, or 
binary propositional function.

---


32
INTRODUCTION
no division of them into parts has relevance to the meaning,79 we have 
seen that there are two sorts of symbols which may in particular appear, 
namely primitive proper names and variables. These we call proper symbols, 
and we regard them as having meaning in isolation, the primitive names as 
denoting (or at least purporting to denote) something, the variables as 
having (or at least purporting to have) a non-empty range. But in addition 
to proper symbols there must also occur symbols which are improper—or 
in traditional (Scholastic and pre-Scholastic) terminology, syncategorematic 
—i.e., which have no meaning in isolation but which combine with proper 
symbols (one or more) to form longer expressions that do have meaning 
in isolation.80 81
Conspicuous among improper symbols are parentheses and brackets of 
various kinds, employed (as familiar in mathematical notation) to show the 
way in which parts of an expression are associated. These parentheses and 
brackets occur as constituents in certain combinations of improper symbols 
such as we now go on to consider—either exclusively to show association and 
in connection with other improper symbols which carry the burden of show­
ing the particular character of the notation,61 or else sometimes in a way 
that combines the showing of association with some special meaning-pro­
ducing character.82
Connectives are combinations of improper symbols which may be used 
together with one or more constants to form or produce a new constant.
,BThe formalized languages are to be so constructed as to make such analysis into 
single symbols precisely possible. In general it is possible in the natural languages only 
partially and approximately—or better, our thinking of it as possible involves a certain 
idealization.
In written English (say), the single symbols obtained are not just the letters with 
which words are spelled, since the division of a word into letters has or may have no 
relevance to the meaning. Frequently the single symbols are words. In other cases they 
are parts of words, since the division, e.g., of "books*’ into "book" and "s" or of 
"colder" into "cold" and "er" does have relevance to the meaning. In still other cases 
the linguistic structure of meaningful parts is an idealization, as when "worse" is taken 
to have an analysis parallel to that of "colder," or "I went" an analysis parallel to that 
of "I shall go," or "had I known" parallel to that of "if I should hear." {Less obvious 
and more complex examples may be expected to appear if analysis is pressed more in 
detail.)
80Apparently the case may be excluded th at several improper symbols combine with­
out any proper symbols to form an expression th at has meaning in isolation. For the 
division of that expression into the improper symbols as parts could then hardly be said 
to have relevance to the meaning.
81Thus in the expression 
— (a? — y)) we may say that the inner parentheses serve 
exclusively to show the association together of the part x — y of the expression, and 
th at they are used in connection with the sign —, which serves to show subtraction.
a2In real number theory, the usual notation ] 
[ for the absolute value is an obvious
example of this latter. Again it may be held th at the parentheses have such a double 
use in either of the two notations introduced in §03 for application of a singulary func­
tion to its argument.

---


§05]
IMPRO PER  SYMBOLS, CONNECTIVES
Then, as follows from the discussion in §02, if we replace one or more of the 
constants each by a form which has the denotation of that constant among 
its values, the resulting expression becomes a form (instead of a constant); 
and the free variables of this resulting form are the free variables of all the 
forms (one or more) which were united by means of the connective (with 
each other and possibly also with some constants) to produce the resulting 
form. In order to give completely the meaning-producing character of a 
particular connective in a particular language, not only is it necessary to 
give the denotation83 of the new constant in every permissible case that the 
connective is used together with one or more constants to form such a new 
constant, but also, for every case that the connective may be used with forms 
or forms and constants to produce a resulting form, it is necessary to give 
the complete scheme of values of this resulting form for values of its free 
variables. And this must all be done in a way to conform to the assump­
tions about sense and denotation at the end of §01, and to the conventions 
about meaning and values of variables and forms as these were described in 
§02. Connectives may then be used not only in languages which contain 
constants but also in languages whose only proper symbols are variables.84
The constants or forms, united by means of a connective to produce a 
new constant or form, are called the operands. A connective is called sin- 
gulary, binary, ternary, etc., according to the number of its operands.
A singulary connective may be used with a variable of appropriate range 
as the operand (this falls under our foregoing explanation since, of course, 
a variable is a special case of a form). The form so produced is called an 
associated form of the connective if the range of the variable includes the 
denotations of all constants which may be used as operands of the connective 
and all the relevant values of all the forms which may be used as operands 
of the connective (where by a relevant value of a form used as operand is 
meant a value corresponding to which the entire form, consisting of con­
nective and operand, has a value). And the associated function of a sin­
gulary connective is the associated function of any associated form. The 
associated function as thus defined is clearly unique.
MIt is not necessary (or possible) to give the sense of the new constant separately, 
since the way in which the denotation is given carries with it a sense—the same phrase 
which is used to name the denotation must also express a sense.
Further questions arise if, besides constants, names having a sense but no denotation 
are allowed. Such names seem to be used with connectives in the natural languages and 
in usual systems of mathematical notation, and indeed some illustrations which we 
have employed depend on this. However, as already explained, we avoid this in the 
formalized languages which we shall consider.
«Cf. footnote 27.

---


34
INTRODUCTION
The n o tio n  of th e associated  fu n ctio n  of a sin g u la ry  co n n ectiv e is possib le 
also in the case of a language co n ta in in g  n o variab le w ith  a range o f th e kind 
required to  p rod u ce an a ssociated  form , n a m ely  w e m a y  con sid er an  e x te n ­
sion of th e la n g u a g e ob tain ed  b y  ad d in g su ch  a variab le.
In th e sa m e w a y  an n-ary co n n ectiv e m a y  be u sed  togeth er w ith  n 
different v a ria b les as operands to produce a form ; a n d  th is is called  an 
associated form of the co n n ectiv e if, for each variab le, th e range in clu d es 
b oth  th e d e n o ta tio n s of all c o n sta n ts and all relev a n t valu es of all form s 
w h ich m a y  be u sed  as operands at th a t place. T h e associated function of th e 
con n ective is th a t one of th e a sso cia ted  n -ary fu n ctio n s of an a sso cia ted  
form  w h ich  is ob tain ed  b y  assig n in g  the argu m en ts of th e fu n ction , in th eir 
order, as v a lu e s to the free v ariab les of th e form  in th eir left-to -rig h t order 
of occurrence in th e form.
In general th e m ean in g-p rod u cin g character of a co n n ectiv e is m o st 
readily g iven  b y  ju st g iv in g  th e a sso cia ted  fu n ction , th is b ein g  su fficien t 
to fix  th e u se of the co n n ectiv e co m p letely .85
In d eed  th ere is a close rela tio n sh ip  betw een  co n n ectiv es and functional 
constants or proper nam es of fu n ctio n s. D ifferences are th a t (a) a fu n ctio n a l 
co n sta n t denotes a fu n ction  w h ereas a co n n ectiv e is associated with a fu n ctio n , 
(b) a c o n n e c tiv e  is never replaced  b y  a variable, an d  (c) th e n o ta tio n  for 
ap p lication  of a function to its a rg u m en ts m a y  be p aralleled  b y  a differen t 
n otation  w h en  a corresponding co n n ectiv e ta k es th e p la ce of a fu n ctio n a l 
con stan t. B u t th ese differences are from  som e p o in ts o f v iew  la rg ely  n on - 
essen tial b ecau se (a) n otation s o f course h ave su ch  m ean in g as w e ch oose 
to give th em  (w ith in  lim itation s im p o sed  b y  req u irem en ts o f c o n siste n c y  
and a d eq u a cy ), (b) languages are possib le w h ich do n o t con tain  variab les 
w ith  fu n ctio n s as valu es an d  in w h ich  fun ction al c o n sta n ts are n ev er re­
placed b y  variab les, and (c) th e n o ta tio n  for a p p lica tio n  of a fu n ctio n  
to its a rg u m en ts m ay, like a n y  oth er, be ch a n g ed — or even  d u p lica ted
i6For example, the familiar notation ( — ) for subtraction of real numbers m ay be 
held to be a connective. That is, the combination of symbols which consists of a left 
parenthesis, a minus sign, and a right parenthesis, in that order, may be considered as 
a connective—where the understanding is that an appropriate constant or form is to 
be filled in at each of two places, namely immediately before and immediately after 
the minus sign. To give completely the meaning-producing character of this connective, 
it is necessary to give the denotation of the resulting constant when constants are filled 
m at the two places, and also to give the complete scheme of values of the resulting form 
when forms are filled in at the two places, or a form at one place and a constant a t the 
other. In order to do this in a way to conform to §§01, 02, it m ay often be most expedi­
tious first to introduce (by whatever means may be available in the particular context) 
the binary function of real numbers th at is called subtraction, and then to declare this 
to be the associated function of the connective.

---


§05]
IM PROPER SYMBOLS, CONNECTIVES
35
b y  in trod u cin g sev era l sy n o n y m o u s n o ta tio n s in to th e sam e la n g u a g e.86
In  th e case of a la n g u a g e h a v in g  n o ta tio n s for ap p lication  o f a fu n ctio n  to 
its argu m en ts, it is clear th a t a co n n ectiv e m a y  often  be e lim in a te d  or d is­
p en sed  w ith  a lto g eth er b y  em p lo y in g  in stea d  a nam e of th e a sso cia ted  fu n c­
tio n — b y  m o d ify in g  th e  lan gu age, if n ecessary, to  the e x te n t of a d d in g such 
a n a m e to its v o ca b u la ry . H ow ever, th e co m p lete elim in ation  of all con n ec­
tiv e s from  a lan gu age can n ever be a cco m p lish ed  in th is w a y . F or the no­
ta tio n s for a p p lica tio n  of a sin gu lary fu n ctio n  to its argum ent, for ap p lication  
of a b in ary fu n ction  to  its argu m en ts, and so on (e.g., the n o ta tio n s for these 
w h ich  w ere in tro d u ced  in  §03) are th e m se lv e s co n n ectiv es. A n d  th o u g h  
th e se  co n n ectiv es, lik e a n y  other, no d ou b t h a v e their a sso cia ted  fu n ctio n s,87 
n ev erth eless n ot all of th em  can ever be elim in a ted  b y  th e d ev ice in q u estio n .88
••Thus, to use once more the example of the preceding footnote, we may hold that 
the notation ( — ) is a connective and that the minus sign has no meaning in isolation, 
Or alternatively we m ay hold that the minus sign denotes (is a name of) the binary 
function, subtraction, and th at in such expressions as, e.g., (x — y) or (5 — 2) we have 
a special notation for application of a binary function to its arguments, different from 
the notation for this which was introduced in §03. The choice would seem to be arbitrary 
between these two accounts of the meaning of the minus sign. But from one standpoint 
it may be argued that, if we are willing to invent some name for the binary function, 
then this name might just as well, and would most simply, be the minus sign.
87As explained below, we are for expository purposes temporarily ignoring difficulties 
or complications which m ay be caused by the theory of types or by such alternative 
to the theory of types as m ay be adopted. On this basis, for the connective which is the 
notation for application of a singulary function to its argument, we explain the asso­
ciated function by saying th at it is the binary function whose value for an ordered pair 
of arguments }, x is f\x). But if a name of this associated function is to be used for the 
purpose of eliminating the connective, then another connective is found to be necessary, 
the notation, namely, for application of a binary function to its arguments. If the latter 
connective is to be eliminated by using a name of its associated function, then the no­
tation for application of a ternary function to its arguments becomes necessary. And 
so on. Obviously no genuine progress is being made in these attem pts.
(After studying the theory of types the reader will see that the foregoing statement, 
and others we have made, remain in some sense essentially true on the basis of that 
theory. It is only that the connective, e.g., which is the notation for application of a 
singulary function to its argument must be thought of as replaced by many different 
connectives, corresponding to different types, and each of these has its own associated 
function. Or alternatively, if we choose to retain this connective as always the same con­
nective, regardless of considerations of type, then there may well be no variable in the 
language with a range of the kind required to produce an associated form: an extension 
of the language by adding such a variable can be made to provide an associated form, 
but not so easily a name of the associated function. See Carnap, The L o g i c a l  S y n t a x  of 
Language (cited in footnote 131), examples at the end of §53, and references there given; 
also Bernard N otcutt’s proposal of "intertypical variables’’ in M i n d , n.s. vol. 43 (1934), 
pp. 63-77; and remarks by Tarski in the appendix to his Wahrheitsbegriff (cited in 
footnote 140).)
••There is, however, a device which may be used in appropriate context (cf. Chapter 
X) to eliminate all the connectives except the notation for application of a singulary 
function to its argument. This is done by reconstruing a binary function as a singulary 
function whose values are singulary functions; a ternary function as a singulary function 
whose values are binary functions in the foregoing sense; and so on. For it turns out

---


36
INTRODUCTION
Connectives other than notations for application of a function to its 
arguments are apparently always eliminable in the way described by a 
sufficient extension of the language in which they occur (including if nec­
essary the addition to the language of notations for application of a function 
to its arguments). Nevertheless such other connectives are often used— 
especially in formalized languages of limited vocabulary, where it may be 
preferred to preserve this limitation of vocabulary, so as to use the language 
as a means of singling out for separate consideration some special branch 
of logic (or other subject).
In particular we shall meet with sentence connectives in Chapter I. Namely, 
these are connectives which are used together with one or more sentences 
to produce a new sentence; or when propositional forms replace some or 
all of the sentences as operands, then a propositional form is produced rather 
than a sentence.
The chief singulary sentence connective we shall need is one for negation. 
In this role we shall use, in formalized languages, the single symbol 
which, 
when prefixed to a sentence, forms a new sentence that is the negation of 
the first one. The associated function of this connective is the function from 
truth-values to truth-values whose value for the argument falsehood is truth, 
and whose value for the argument truth is falsehood. For convenience in 
reading orally expressions of a formalized language, the symbol ~ may be 
rendered by the word "not” or by the phrase "it is false that.”
The principal binary sentence connectives are indicated in the table which 
follows. The notation which we shall use in formalized languages is shown 
in the first column of the table, with the understanding that each of the 
two blanks is to be filled by a sentence of the language in question. In the 
second column of the table a convenient oral reading of the connective is 
suggested, or sometimes two alternative readings; here the understanding 
is that the two blanks are to be filled by oral readings of the same two sen­
tences (in the same order) which filled the two corresponding blanks in the 
first column; and words which appear between parentheses are words which
that n-ary functions in the sense thus obtained can be made to serve all the ordinary 
purposes of ti-ary functions (in any sense).
The alternative device of reducing (e.g.) a binary function to a singulary function by 
reconslruing it as a singulary function whose arguments are ordered pairs is also useful 
in certain contexts (e.g., in axiomatic set theory). This device does not (at least prima 
facie) serve to reduce the number of connectives to one, as besides the notation for 
application of a singulary function to its argument there will be required also a con­
nective which unites the names of two things to form a name of their ordered pair 
(or at least some notation for this latter purpose). Nevertheless it is a device which 
may sometimes be used to accomplish a reduction, especially where other connectives— 
or operators (§06)—are available.

---


§05]
IM PROPER SYMBOLS, CONNECTIVES
37
may ordinarily be omitted for brevity, but which are to be supplied whenever 
necessary to avoid a misunderstanding or to emphasize a distinction. In 
the third column the associated function of the connective is indicated by 
means of a code sequence of four letters: in doing this, t is used for truth and 
f for falsehood, and the first letter of the four gives the value of the function 
for the arguments t, t, the second letter gives the value for the arguments 
t, f, the third letter for the arguments f, t, the fourth letter for the argu­
ments f, f. In many cases there is an English name in standard use, which 
may denote either the connective or its associated function. This is indicated 
in a fourth column of the table; where alternative names are in use, both are 
given, and in some cases where none is in use a suggested name is supplied.
[ 
V 
]
or 
for both).
tttf
(Inclusive) disjunction, 
alternation.
[ 
<= 
]
if 
.89
ttft
Converse im plication.
[ 
=> 
]
If 
then 
,89
tf tt
T he (truth-functional) 
conditional,00
(m aterially) implies 
89
(m aterial) im plication.
[ 
=  
]
if and only if 
T89
tfft
The (truth-functional) 
biconditional,00
is (m aterially) equi- 
valent to 
80
(m aterial) equivalence.
[ 
]
and
tfff
Conjunction.
[ 
1 
]
N ot both 
and
f ttt
N on-conjunction, 
Sheffer's stroke.
[ 
*  
]
or 
b u t no t both, 
is n o t fm a te ria lly  
equivalent to  
.89
fttf
Exclusive disjunction, 
(m aterial) non- 
equivalence.
[ 
]
b u t n o t
ftff
(M aterial) non-im plication
[ 
$
 
]
N ot 
b u t
fftf
Converse non-im plication
[ 
V  
]
N either 
nor
ffft
N on-disjunction.
wThe use of the English words " if /' "implies," "equivalent" in these oral readings 
roust not be taken as indicating th at the meanings of these English words are faithfully

---


38
INTRODUCTION
The notations which we use as sentence connectives—and those which we
use as quantifiers (see below)—are adaptations of those in Whitehead and
Russell’s Principia Mathematica (some of which in turn were taken from
Peano). Various other notations are in use,91 and the student who would
rendered by the corresponding connectives in all, or even in most, cases. On the con­
trary, the meaning-producing character of the connectives is to be learned with accuracy 
from the third column of the table, where the associated functions are given, and the 
oral readings supply at best a rough approximation.
As a m atter of fact, the words "if . . . then" and "implies" as used in ordinary non­
technical English often seem to denote a relation between propositions rather than 
between truth-values. Their possible meanings when employed in this way are difficult 
to fix precisely and we shall make no attem pt to do so. But we select the one use of the 
words "if . . . then" (or "implies"}—their material use, we shall call it—in which they 
may be construed as denoting a relation between truth-values, and we assign this 
relation as the associated function for the connective [ zd ].
As examples of the material use of "if . . . then," consider the four following English 
sentences:
(i) 
If Joan of Arc was a patriot then Nathan Hale was a patriot.
(ii) 
If Joan of Arc was a patriot then Vidkun Quisling was a patriot.
(iii) 
If Vidkun Quisling was a patriot then attar of roses is a perfume.
(ivj 
If Vidkun Quisling was a patriot then Limburger cheese is a perfume.
For the sake of the illustration let us suppose examination of the historical facts to
reveal that Joan of Arc and Nathan Hale were indeed patriots and th at Vidkun Quisling 
was not a patriot. Then (i), (iii), and (iv) are true, and (ii) is false; and to reach these 
conclusions no examination is necessary of the characteristics of either attar of roses or 
Limburger cheese. (If the reader is inclined to question the truth of, e.g., (iii) on the 
ground of complete lack of connection between Vidkun Quisling and attar of roses, 
then this means that he has in mind some other use of "if . . . then" than the material 
use.)
B0These terms were introduced by Quine, who uses them for "the mode of composition 
described in" the list of truth-values as given in the third column of the table—i.e., 
in effect, and in our terminology, for the associated function of the connective rather 
than for the connective itself. See his Mathematical Logic, 1940, pp. 15, 20.
We prefer the better established terms material implication and material equivalence, 
from which the adjective material may be om itted whenever there is no danger of con­
fusion with other kinds of implication or equivalence—as, for example, with formal 
implication and formal equivalence (§06), or with kinds of implication and equivalence 
(belonging to modal logic) which are relations between propositions rather than be­
tween truth-values.
BlWorthy of special remark is the parenthesis-free notation of Jan Lukasiewicz. In 
this, the letters N, A, C, E, K are used in the roles of negation, disjunction, implication, 
equivalence, conjunction respectively. Further letters may be introduced if desired 
{R has been employed as non-equivalence, D as non-conjunction). In use as a sentence 
connective, the letter is written first and then in order the sentences or propositional 
forms together with which it is used. No parentheses or brackets or other notations 
specially to show association are necessary. E.g., the propositional form
[[p =3 [q v r]] => ~p]
(where p, q, r are propositional variables) becomes, in the Lukasiewicz notation,
CCpAqrNp.
It is of course possible to apply the same idea to other connectives, in particular to 
the notation for application of a singulary function to its argument. Hence (see foot­
note 88) parentheses and brackets may be avoided altogether in a formalized language. 
The possibility of this is interesting. But the notation so obtained is unfamiliar, and 
less perspicuous than the usual one.

---


§06]
OPERATORS, QUANTIFIERS
39
compare the treatments of different authors must learn a certain facility 
in shifting from one system of notation to another.
The brackets which we indicate as constituents in these notations may in 
actual use be found unnecessary at certain places, and we may thou just omit 
them at such places (though only as a practically convenient abbreviation).
We shall use the term truth-function92 for a propositional function of truth- 
values which has as range, if it is n-ary, all ordered systems of n truth-values. 
Thus every associated function of a sentence connective is a truth-function. 
And likewise every associated function of a form built up from propositional 
variables solely by iterated use of sentence connectives.93
06. Operators, quantifiers. An operator is a combination of improper 
symbols which may be used together with one or more variables—the 
operator variables (which must be fixed in number and all distinct) —and one 
or more constants or forms or both—the operands—to produce a new con­
stant or form. In this new constant or form, however, the operator variables 
are at certain determinate places not free variables, though they may have 
been free variables at those places in the operands.
To be more explicit, we remark that, in any application of an operator, the 
operator variables may (and commonly will) occur as free variables in some 
of the operands. In the new constant or form produced we distinguish three 
possible kinds of occurrences of the operator variables, viz.: an occurrence 
in one of the operands which, when considered as an occurrence in that 
operand alone, is an occurrence as a free variable; an occurrence in one of 
the operands, not of this kind; and an occurrence which is an occurrence as an 
operator variable, therefore not in any of the operands. In the new constant 
or form, an occurrence of one of the two latter kinds is never an occurrence 
as a free variable, and each occurrence of the first kind is an occurrence as a 
free variable or not, according to some rule associated with the particular 
operator.94 The simplest case is that, in the new constant or form, none of the 
occurrences of the operator variables are occurrences as free variables. And 
this is the only case with which we shall meet in the following chapters
” We adopt this term from Principia Mathemaiica, giving it substantially the meaning 
which it acquires through changes in that work th at were made (or rather, proposed) 
by Russell in his introduction to the second edition of it.
“ For example, the associated function of the propositional form mentioned in foot­
note 01.
MWe do require in the case of each operator variable th at all occurrences of the first 
kind shall be occurrences as free variables or else all not, in any one occurrence of a 
particular operand in the new constant or form produced. For operators violating this 
requirement are not found among existing standard mathematical and logical notations, 
and it is clear that they would involve certain anomalies of meaning which it is prefer­
able to avoid.

---


40
INTRODUCTION
(though many operators which are familiar as standard mathematical 
notation fail to fall under this simplest case).
Variables thus having occurrences in a constant or form which are not 
occurrences as free variables of it are called bound variables of the constant or 
form.95 The difference is that a form containing a particular variable, say x, 
as a free variable has values for various values of the variable, but a constant 
or form which contains x as a bound variable only has a meaning which is 
independent of x—not in the sense of having the same value for every value 
of x, but in the sense that the assignment of particular values to x is not a 
relevant procedure.96
It may happen that a form contains both free and bound occurrences of 
the same variable. This case will arise, for example, if a form containing a 
particular variable as a free variable and a form or constant containing that 
same variable as a bound variable are united by means of a binary connec­
tive.97
As in the case of connectives, we require that operators be such as to con­
form to the principles (1)—(3) at the end of §01; also that they conform to the 
conventions about meaning and values of variables as these were described 
in §02, and in particular to the principle (4) of §02.88
An operator is called m-ary-n-ary if it is used with m distinct operator 
variables and n operands.99 The most common case is that of a singulary- 
singulary operator—or, as we shall also call it, a simple operator.
In particular, the notation for singulary functional abstraction, which
•* *Cf. footnote 28.
•“Therefore a constant or form which contains a particular variable as a bound variable 
is unaltered in meaning by alphabetic change of that variable, at all of its bound occur­
rences, to a new variable (not previously occurring) which has the same range. The 
condition in parentheses is included only as a precaution against identifying two varia­
bles which should be kept distinct, and indeed it may be weakened somewhat—cf. the 
remark in §03 about alphabetic change of free variables.
E.g., the constant [*xxdx (see footnote 36) is unaltered in meaning by alphabetic 
change of the variable * to the variable y\ it has not only the same denotation but also 
the same sense as
*7See illustrations in the second paragraph of footnote 36.
•®And also to the principle (5) of footnote 30.
••Thus, in the theory of real numbers, the usual notation for definite integration is a 
singulary-ternary operator. And in, e.g., the form ftx*dx (see footnote 36) the oper­
ator variable is * and the three operands are the constant 0, the form x, and the form a*.
Again, the large J"J (product sign), as used in the third example at the beginning of 
footnote 36, is part of a singulary-ternary operator. The signs 
above and below the 
fl are not to be taken as equality signs in the ordinary sense {namely that of footnote 
43) but as improper symbols, and also part of the operator. In the particular application 
of the operator, as it appears in this example, the operator variable is m and the 
operands are l,n , and
x — m +  1
mn

---


§06]
OPERATORS, QUANTIFIERS
41
was introduced in §03, is a simple operator (the variable which is placed 
immediately after the letter A being the operator variable). We shall call 
this the abstraction operator or, more explicitly, the singulary functional 
abstraction operator. In appropriate context, as we shall see in Chapter X, 
all other operators can in fact be reduced to this one.100
Another operator which we shall use—also a simple operator—is the 
description operator, (? ). To illustrate, let the operator variable be x. Then the 
notation (?a?) is to have as its approximate reading in words, "the x such 
that”; or more fully, the notation is explained as follows. It may happen 
that a singulary propositional form whose free variable is x has the value 
truth for one and only one value of x, and in this case a name of that value 
of a: is produced by prefixing (fa;) to the form. In case there is no value of x 
or more than one for which the form has the value truth, there are various 
meanings which might be assigned to the name produced by prefixing (?:c) 
to the form: the analogy of English and other natural languages would 
suggest giving the name a sense which determines no denotation; but we 
prefer to select some fixed value of x and to assign this as the denotation 
of the name in all such cases (this selection is arbitrary, but is to be made 
once for all for each range of variables which is used^
Of especial importance for our purposes are the quantifiers. These are 
namely operators for which both the operands and the new constant or form 
produced by application of the operator are sentences or propositional forms.
As the universal quantifier (when, e.g., the operator variable is x) we use
As another example of application of the same operator, showing both bound and free 
occurrences of m, we cite
m + n + 1
n
m = ro + l
x — m - j- 1
YYU l
Examples of operators taking more than one operator variable are found in familiar 
notations for double and multiple limits, double and multiple integrals.
It should also be noted that n-ary connectives may, if we wish, be regarded as 
0-ary-w-ary operators.
loaIn the combinatory logic of H. B. Curry (based on an idea due to M. Schdnfinkel) 
a more drastic reduction is attempted, namely the complete elimination of operators, 
of variables, and of all connectives, except a notation for application of a singulary 
function to its argument, so as to obtain a formalized language in which, with the 
exception of the one connective, all single symbols are constants, and which is neverthe­
less adequate for some or all of the purposes for which variables are ordinarily used. 
This is a m atter beyond the scope of this book, and the present status of the undertaking 
is too complex for brief statem ent. The reader may be referred to a monograph by the 
present writer, The Calculi of Lambda-Conversion (1941), which is concerned with a 
related topic; also to papers by Schdnfinkel, Curry, and J. B. Rosser which are there 
cited, to several papers by Curry and by Rosser in The Journal of Symbolic Logic in 1941 
and 1042, to an expository paper by Robert Feys in Revue Pkilosophique de Louvaxn, 
vol, 44 (1948), pp. 74-103, 237-270, and to a paper by Curry in Synthese, vol. 7 (1949), 
pp. 391-399.

---


42
INTRODUCTION
the n o ta tio n  (V x) or (3), p refixin g this to th e operand. T he u n iversal 
quan tifier is th u s a sim ple operator, and w e m a y  ex p la in  its m ean in g as
follow s (still using the particular variable *  as an  ex a m p le). (x)_____ is
true if th e v alu e o f _____is tru th  for all valu es o f x, an d  (x)_____ is false if
there is a n y  valu e of x for w h ich  th e value o f _____is falsehood. H ere th e
blank is to  be filled  b y a sin gu lary propositional form  con tain in g a; as a free 
variable, th e sam e one a t all four places. Or if as a sp ecial case w e fill th e
blank w ith  a sentence, th en  (a:)_____is true if an d  o n ly  i f _____ is true. (T he
m eaning in case th e blank is filled  b y  a propositional form  con tain in g other 
variables b esid es x as free variab les now  follow s b y  th e discu ssion of v ariab les 
in §02, an d  m a y  be supp lied b y  th e reader.)
L ikew ise th e  existen tial q u an tifier is a sim ple operator for w hich w e sh all 
use th e n o ta tio n  (3 ), filling th e b lan k  space w ith  th e operator variable an d  
prefixing th e w h ole to th e operand. T o take th e p articu lar operator variab le
a; as an exam p le, (3x)_____is tru e if th e valu e o f ______is truth for a t lea st
one valu e of x , an d  (3x)_____is false if th e value o f _____ is falsehood for all
values of x. H ere again th e blank is to  be filled b y  a sin gu lary propositional 
form  co n ta in in g  a; as a free variab le. Or if as a sp ecial case w e fill th e b lan k  
w ith a sen ten ce, th en  (3 x )_____ is true if an d  o n ly  if _____is true.
In w ords, th e notations 11 (a:)** an d  " (3 x )” m a y  be read resp ectiv ely  as 
“ for all x” (or “ for every x “ ) an d  "there is an  x  su ch  th a t.”
T o illu strate th e use o f th e u n iversal and e x isten tia l quantifiers, an d  in 
particular th eir iterated ap p lication , consider th e b in ary p ropositional form ,
[xy >  0],
where x an d  y are real variables, i.e., variables w h ose range is th e real 
num bers. T h is form  expresses a b o u t tw o real num bers x and y th a t th eir 
product is p o sitiv e, and th u s it com es to  express a particu lar proposition as 
soon as v alu es are given  to  x and y. If w e apply to  it th e  ex isten tia l q u an tifier 
w ith  y as operator variable, w e o b ta in  the sin gulary p ropositional form ,
(3y)[xy >  o],
or as w e m ay also w rite it, u sin g th e device (w hich w e sh all find freq u en tly 
convenien t later) of w riting a h e a v y  d ot to  stan d  for a brack et ex ten d in g , 
from th e p lace w here th e dot occurs, forward,
(3 y ) ■ xy >  0.
This sin gulary form  expresses ab ou t a real num ber x  th a t th ere is som e real 
num ber w ith  w h ich its product is p ositive; and it com es to  express a p artic­
ular proposition as soon as a valu e is given  to x. If w e a p p ly  to it th e u n i­

---


§06]
OPERATORS, QUANTIFIERS
43
versal quan tifier w ith  % a s operator variab le, w e obtain th e sen ten ce,
(*) (3y) . xy >  0.
T h is sen ten ce exp resses th e  proposition th at for every real n u m ber there is 
som e real num ber su ch  th a t th e product of th e tw o  is p o sitiv e. It m u st be 
d istin gu ish ed  from  th e sen ten ce,
(3y)(*> *%y >  o,
exp ressin g the p rop osition  th a t there is a real num ber w hose p rod u ct w ith 
every real num ber is p o sitiv e, th ou gh  it h a p p en s th at b oth  are fa lse.* 101 To 
bring o u t m ore sh a rp ly  th e  difference w h ich  is m ade b y  th e d ifferen t order 
of th e  quan tifiers, let u s rep lace product b y  sum  and con sid er th e tw o 
sen ten ces:
(* )(3 y ) mX +  y >  0 
(3 y){x) 
+  y > 0
Of th ese sen ten ces, th e first one is tru e an d  th e second one fa lse.102
I t sh ou ld  b e in form ally clear to  th e reader th a t not b oth th e u n iversal and 
th e ex isten tia l q u an tifier are a ctu ally n ecessary in a form alized lan gu age, if
n eg a tio n  is availab le. F o r it w ou ld  be p ossib le, in place of (3 as)_____, to
w rite alw a y s ~(z)~_____; or altern atively, in place of (a;)_____ , to  w rite
a lw a y s ~(3as)~____ . A n d  o f course likew ise w ith  an y  other variab le in place
o f th e  particular variab le as.
In  m o st trea tm en ts th e  u n iversal a n d  e x iste n tia l quantifiers, on e or both,
wlThe single counterexample, of the value 0 for x, is of course sufficient to render the 
first sentence false.
The reader is warned against saying that the sentence (a;)(3y) *xy >  0 is "nearly 
always true” or that it is "true with one exception" or the like. These expressions are 
appropriate rather to the propositional form (3y) . xy >  0, and of the sentence it must 
be said simply that it is false.
101A somewhat more complex example of the difference made by the order in which 
the quantifiers are applied is found in the familiar distinction between continuity and 
uniform continuity. Using x and y as variables whose range is the real numbers, and e 
and 8 as variables whose range is the positive real numbers, we may express as follows 
th at the real function / is continuous, on the class F  of real numbers (assumed to be an 
open or a closed interval):
. F{y) => . F{x) r> - \x -  y\ <  8 Z3 . \f{x) -  f(y)| <  s 
And we may express as follows that / is uniformly continuous on F:
(e)(3d)(*)(y) - F (y) z i >F(x) ■=> . \x -  y\ <  8 Z3 . \f(x) -  }{y)\ <  e
To avoid complications th at are not relevant to the point being illustrated, we have 
here assumed not only th at the class F  is an open or closed interval but also that the 
range of the function / is all real numbers. (A function with more restricted range may 
always have its range extended by some arbitrary assignment of values; and indeed it 
is a common simplifying device in the construction of a formalized language to restrict 
attention to functions having certain standard ranges (cf. footnote 19).)

---


44
INTRODUCTION
are made fundamental, notations being provided for them directly in setting 
up a formalized language, and other quantifiers are explained in terms of 
them (in a way similar to that in which, as we have just seen in the preceding 
paragraph, the universal and existential quantifiers may be explained, either 
one in terms of the other). No definite or compelling reason can be given for 
such a preference of these two quantifiers above others that might equally 
be made fundamental. But it is often convenient.
The application of one or more quantifiers to an operand (especially uni­
versal and existential quantifiers) is spoken of as quantification,103
Another quantifier is a singulary-binary quantifier for which we shall
use the notation [____3 ____ ], with the operands in the two blanks, and
the operator variable as a subscript after the sign 3 .  It may be explained by
saying that [____________] is to mean the same as (x)[____3 ____ ], the
two blanks being filled with two propositional forms or sentences, the same 
two in each case (and in the same order); and of course likewise with any 
other variable in place of the particular variable z. The name formal impli­
cation104 is given to this quantifier—or to the associated binary propositional 
function, i.e., to an appropriate one of the two associated functions of (say) 
the form[jF(«) 3 U G{u)], where u is a variable with some assigned range, 
and F and G are variables whose range is all classes (singulary propositional 
functions) that have a range coinciding with the range of u.
Another quantifier is that which (or its associated propositional function)
is called formal equivalence.10* For this we shall use the notation [____= ____],
with the two operands in the two blanks, and the operator variable as a sub­
script after the sign =  . It may be explained by saying that [____________]
is to mean the same as (a;)[____= ____ ], the two blanks being filled in each
case with the two operands in order; and of course likewise with any other 
variable in place of x.
We shall also make use of quantifiers similar in character to those just 
explained but having two or more operator variables. These (or their 
associated propositional functions) we call binary formal implication, binary 
formal equivalence, ternary formal implication, etc. E.g., binary formal im­
plication may be explained by saying that [____r>w ____ ] is to mean the
1MThe use of quantifiers originated writh Frege in 1879. And independently of Frege 
the same idea was introduced somewhat later by Mitchell and Peirce. (See the historical 
account in §49.)
lMThe names formal implication and formal equivalence are those used by Whitehead 
and Russell in Principia Mathematica, and have become sufficiently well established 
that it seems best not to change them—though the adjective formal is perhaps not very 
well chosen, and must not be understood here in the same sense th at we shall give it 
elsewhere.

---


§06]
OPERATORS, QUANTIFIERS
45
same as (ar)(y)[____^ ____ ], the two blanks being filled in each case with
the two operands in order; and likewise with any two distinct variables in 
place of x and y as operator variables. Similarly binary formal equivalence 
[____s
, ____ ], ternary formal implication [_____________ ], and soon.105
B e sid e s th e assertion  o f a  sentence* as co n tem p la ted  in §04, it is u su al also 
to a llo w  assertion  o f a p ro p o sitio n a l form , an d  to  treat such an a ssertio n  as 
a  p a rticu lar fixed  assertion  (in sp ite o f th e p resen ce of free variab les in the 
exp ressio n  asserted ). T h is is com m on esp ecia lly  in m ath em atical c o n tex ts; 
w here, for in stan ce, th e a ssertio n  o f th e e q u a tio n  sin  (x -f  2tz) =  sin  x  m ay
w‘W ith the aid of the notations th at have now been explained, we may return to §00 
and rewrite the examples I-IV  of th at section as they might appear in some appropriate 
formalized language.
For this purpose let a and b be variables whose range is human beings. Let v be a 
variable whose range is words (taking, let us say for definiteness, any finite sequence of 
letters of the English alphabet as a word). Let B denote the relation of being a brother 
of. Let S denote the relation of having as surname. L etg and a denote the human beings 
Richard and Stanley respectively, and let r  denote the word "Thompson.” Then the 
three premisses and the conclusion of I may be expressed as follows:
B (a, b) 
. S{a, v) —v 
v)
B (Q, a)
S{a, t)
S ( e ,  r )
Further, let z and w be variables whose range is complex numbers, and x a variable 
whose range is real numbers. Let R denote the relation of having real positive ratio, and 
let A denote the relation of having as amplitude. Then the premisses and conclusion 
of II m ay be expressed as follows:
R{z, w) 
* A{z, x) 
A (w, x)
U(i -  V'3/3,co)
A (to, 2n/3)
A (i -  V3/3, 2n/3)
Here it is obvious th at the relation of having real positive ratio is capable of being 
analyzed, so that instead of R(z, tv) we might have written, e.g..
(3x)[* >  0][z — xuj]
Likewise the relation of having as amplitude or (in I) the relation of being a brother of 
m ight have received some analysis. But these analyses are not relevant to the validity 
of the reasoning in these particular examples. And they are, moreover, in no way- 
final or absolute; e.g., instead of analyzing the relation of having real positive ratio, we 
might with equal right take it as fundamental and analyze instead the relation of being 
greater than, in such a way that, in place of x >  y would be written R(x — y, 1)
In the same way, for III and IV, we make no analysis of the singulary propositional 
functions of having a portrait seen by me, of having assassinated Abraham Lincoln, 
and of having invented the wheeled vehicle, but let them  be denoted just by P . L and 
W respectively. Then if p denotes John Wilkes Booth, the premisses and conclusion of 
III may be expressed thus;
P(P) 
L{fi) 
{la)iP{a)L [a))
And the premisses and fallacious conclusion of IV thus:
(3a)P(a) 
(3a)W {a) 
(3 a)[P{a)W [a)]
When so rewritten, the false appearance of analogy between III and IV disappears. 
It was due to the logically irregular feature of English grammar by which "somebody" 
is construed as a substantive.

---


46
INTRODUCTION
be used as a means to assert this for all real numbers x; or the assertion of the 
inequality x2 -j- y2 ^  2xy*may be used as a means to assert that for any real 
numbers x and y the sum of the squares is greater than or equal to twice the 
product.
It is clear that, in a formalized language, if universal quantification is 
available, it is unnecessary to allow the assertion of expressions containing 
free variables. E.g., the assertion of the propositional form
x2 +  y2 ^  2 xy
could be replaced by assertion of the sentence
(*)(y) 
+  y% ^  2xy.
But on the other hand it is not possible to dispense with quantifiers in a 
formalized language merely by allowing the assertion of propositional forms, 
because, e.g., such assertions as that of
~{x) (y) m sin (x +  y) — sin x +  sin y,106
or that of
(y)tN 5  \y\] =>*■* = 0,
could not be reproduced.
Consequently it has been urged with some force that the device of assert­
ing propositional forms constitutes an unnecessary duplication of ways of 
expressing the same thing, and ought to be eliminated from a formalized 
language.107 Nevertheless it appears that the retention of this device often 
facilitates the setting up of a formalized language by simplifying certain 
details; and it also renders more natural and obvious the separation of such 
restricted systems as propositional calculus (Chapter I) or functional cal­
culus of first order (Chapter III) out from more comprehensive systems of 
which they are part. In the development which follows we shall therefore 
make free use of the assertion of propositional forms. However, in the case 
of such systems as functional calculus of order co (Chapter VI) or Zermelo set 
theory (Chapter XI), after a first treatment employing the device in question 
we shall sketch briefly a reformulation that avoids it.
108This assertion (which is correct, and must sometimes be made to beginners in 
trigonometry) is of course to be distinguished from the different (and erroneous) 
assertion of
~  • sin (z +  y) =  sin x 4- sin y.
107The proposal to do this was made by Russell in his introduction to the second edi­
tion of Principia Matkematica (1925). The elimination was actuaUy carried out by 
Quine in his Mathematical Logic (1940), and simplifications of Quine’s method were 
effected in papers by F. B. Fitch and by G. D. W. Berry in The Journal of Symbolic 
Logic (vol. 6 (1941), pp. 18-22, 23-27).

---


S07]
THE LOGISTIC METHOD
47
07. The logistic method. In order to set up a formalized language 
we must of course make use of a language already known to us, say English 
or some portion of the English language, stating in that language the vocab­
ulary and rules of the formalized language. This procedure is analogous to 
that familiar to the reader in language study—as, e.g., in the use of a Latin 
grammar written in English108 *—but differs in the precision with which the 
rules are stated, in the avoidance of irregularities and exceptions, and in 
the leading idea that the rules of the language embody a theory or system of 
logical analysis (cf. §00).
This device of employing one language in order to talk about another is 
one for which we shall have frequent occasion not only in setting up formal­
ized languages but also in making theoretical statements as to what can be 
done in a formalized language, our interest in formalized languages being 
less often in their actual and practical use as languages than in the general 
theory of such use and in its possibilities in principle. Whenever we employ 
a language in order to talk about some language (itself or another106), we 
shall call the latter language the object language, and we shall call the 
former the meta-language.110
In setting up a formalized language we first employ as meia-language a 
certain portion of English. We shall not attempt to delimit precisely this 
portion of the English language, but describe it approximately by saying 
that it is just sufficient to enabLe us to give general directions for the manip­
IWIt is worth remark in passing that this same procedure also enters into the learn­
ing of a first language, being a necessary supplement to the method of learning by 
example and imitation. Some p art of the language must first be learned approximately 
by the method of example and imitation; then this imprecisely known part of the lan­
guage is applied in order to state rules of the language (and perhaps to correct initial 
misconceptions); then the known part of the language may be extended by further 
learning by example and imitation, and so on in alternate steps, until some precision 
in knowledge of the language is reached.
There is no reason in principle why a first language, learned in this way, should not 
be one of the formalized languages of this book, instead of one of the natural languages. 
(But of course there is the practical reason that these formalized languages are ill 
adapted to purposes of facility of communication.)
lMThe employment of a language to talk about that same language is clearly not 
appropriate as a method of setting up a formalized language. But once set up, a formal­
ized language with adequate means of expression may be capable of use in order to 
talk about that language itself; and in particular the very setting up ol the language may 
afterwards be capable of restatement in that language. Thus it may happen that object 
language and meta-language are the same, a situation which it will be im portant later 
to take into account.
II0The distinction is due to David Hilbert, who, however, speaks of “ M athematik” 
(mathematics) and “M etamathematik” (metamathematics) rather than ‘'object 
language" and "meta-language." The latter terms, or analogues of them in Polish or 
German, are due to Alfred Tarski and Rudolf Carnap, by whom especially (see footnotes 
131, 140) the subjects of syntax and semantics have been developed.

---


48
INTRODUCTION
ulation of concrete physical objects (each instance or occurrence of one of 
the symbols of the language being such a concrete physical object, e.g., a 
mass of ink adhering to a bit of paper). It is thus a language which deals 
with matters of everyday human experience, going beyond such matters 
only in that no finite upper limit is imposed on the number of objects that 
may be involved in any particular case, or on the time that may be required 
for their manipulation according to instructions. Those additional portions of 
English are excluded which would be used in order to treat of infinite classes 
or of various like abstract objects which are an essential part of the subject 
matter of mathematics.
Our procedure is not to define the new language merely by means of 
translations of its expressions (sentences, names, forms) into corresponding 
English expressions, because in this way it would hardly be possible to avoid 
carrying over into the new language the logically unsatisfactory features of 
the English language. Rather, we begin by setting up, in abstraction from 
all considerations of meaning, the purely formal part of the language, so 
obtaining an uninterpreted calculus or logistic system. In detail, this is done 
as follows.
The vocabulary of the language is specified by listing the single symbols 
which are to be used,111 These are called the primitive symbols of the lan­
guage,112 and are to be regarded as indivisible in the double sense that (A) in
m Notice that we use the term "language" in such a sense that a given language has 
a given and uniquely determined vocabulary. E.g., the introduction of one additional 
symbol into the vocabulary is sufficient to produce a new and different language. {Thus 
the English of 1849 is not the same language as the English of 1949, though it is con­
venient to call them  by the same name, and to distinguish, by specifying the date, only 
in cases where the distinction is essential.)
luThe fourfold classification of the primitive notations of a formalized language 
into constants, variables, connectives, and operators is due in substance to J. v. 
Neumann in the Malhematische Zeitschrift, vol. 2G (1927), see pp. 4r-6. He there adds a 
fifth category, composed of association-showing symbols such as parentheses and 
brackets. Our terms "connective" and "operator" correspond to his "Operation" and 
"Abstraction" respectively.
Though there is a possibility of notations not falling in any of von Neumann's cate­
gories. such have seldom been used, and for nearly all formalized languages that have 
actually been proposed the von Neumann classification of primitive notations suffices. 
Many formalized languages have primitive notations of all fouT (or five) kinds, but it 
does not appear th at this is indispensable, even for a language intended to be adequate 
for the expression of mathematical ideas generally.
As an interesting example of a (conceivable) notation not in any of the von Neumann 
categories, we mention the question of a notation by means of which from a name of a 
class would be formed an expression playing the role of a variable with that class as its 
range. Provision might perhaps be made for the formation from any class name of an 
infinite number of expressions playing the roles of different variables with the class as 
their range. But these expressions would have to differ from variables in the sense of 
§02 not only in being composite expressions rather than single symbols but also in the

---


§07]
THE LOGISTIC METHOD
49
setting up the language no use is made of any division of them into parts 
and (B) any finite linear sequence of primitive symbols can be regarded in 
only one way as such a sequence of primitive symbols.113 A finite linear 
sequence of primitive symbols is called a formula. And among the formulas, 
rules are given by which certain ones are designated as well-formed formulas 
(with the intention, roughly speaking, that only the well-formed formulas 
are to be regarded as being genuinely expressions of the language),114 Then 
certain among the well-formed formulas are laid down as axioms. And 
finally (primitive) rules of inference (or rules of procedure) are laid down, 
rules according to which, from appropriate well-formed formulas as prem­
isses, a well-formed formula is immediately inferred115 as conclusion. (So 
long as we are dealing only with a logistic system that remains uninterpreted, 
the terms premiss, immediately infer, conclusion have only such meaning as 
is conferred upon them by the rules of inference themselves.)
A finite sequence of one or more well-formed formulas is called a proof if 
each of the well-formed formulas in the sequence either is an axiom or is 
immediately inferred from preceding well-formed formulas in the sequence 
by means of one of the rules of inference. A proof is called a proof of the last 
well-formed formula in the sequence, and the theorems of the logistic system * 18
possibility that the range might be empty. A language containing such a notation has 
never been set up and studied in detail and it is therefore not certain just what is feasible. 
(A suggestion which seems to be in this direction was made by Beppo Levi in Cnivetsi- 
dad National de Tucumdn, Revista, ser. A vol. 3 no. 1 (194*2), pp. 13-78.)
The use in Chapter X of variables with subscripts indicating the range of the variable 
(the type) is not an example of a notation of the kind just described. For the variable, 
letter and subscript together, is always treated as a single primitive symbol.
118In practice, condition (B) usually makes no difficulty. Though the (written) 
symbols adopted as primitive symbols may not all consist of a single connected piece, 
it is ordinarily possible to satisfy (B), if not otherwise, by providing that a sequence of 
primitive symbols shall be written with spaces between the primitive symbols of fixed 
width and wider than the space at any place within a primitive symbol.
The necessity for (B), and its possible failure, were brought out by a criticism by 
StanisJaw Lesniewski against the paper of von Neumann cited in the preceding footnote. 
See von Neumann's reply in Fundamenta Maihematicae, vol. 17 (1931), pp. 331-334, 
and Lesniewski’s final word in the m atter in an offprint published in 1938 as from 
Collectanea Logica, vol. 1 (cf. The Journal of Symbolic Logic, vol. 5, p. 83).
lu The restriction to one dimension in combining the primitive symbols into ex­
pressions of the language is convenient, and non-essential. Two-dimensional arrange­
ments are of course possible, and are familiar especially in mathematical notations, but 
they m ay always be reduced to one dimension by a change of notation. In particular 
the notation of Frege's Begriffsschrift relies heavily on a two-dimensional arrangement; 
but because of the difficulty of printing it this notation was never adopted by any one 
else and has long since been replaced by a onc-dimensional equivalent.
115No reference to the so-called immediate inferences of traditional logic is intended. 
We term the inferences immediate in the sense of requiring only one application of a 
rule of inference—not in the traditional sense of (among other things) having only one 
premiss.

---


50
INTRODUCTION
are those well-formed formulas of which proofs exist.114 * * As a special case, 
each axiom of the system is a theorem, that finite sequence being a proof 
which consists of a single well-formed formula, the axiom alone.
The scheme just described—viz. the primitive symbols of a logistic 
system, the rules by which certain formulas are determined as well-formed 
(following Carnap let us call them the formation rules of the system), the 
rules of inference, and the axioms of the system—is called the primitive basis 
of the logistic system.117
In defining a logistic system by laying down a primitive basis, we employ 
as meta-language the restricted portion of English described above. In ad­
dition to this restriction, or perhaps better as part of it, we impose require­
ments of effectiveness as follows: (I) the specification of the primitive sym­
bols shall be effective in the sense that there is a method by which, whenever 
a symbol is given, it can always be determined effectively whether or not it 
is one of the primitive symbols; (II) the definition of a well-formed formula
“ •Following Carnap and others, we use the term "language" in such a sense that for 
any given language there is one fixed notion of a proof in that language. Thus the intro­
duction of one additional axiom or rule of inference, or a change in an axiom or rule of
inference, is sufficient to produce a new and different language.
(An alternative, which might be thought to accord better with the everyday use of 
the word "language," would be to define a "language" as consisting of primitive sym­
bols and a definition of well-formed formula, together with an interpretation (see below), 
and to take the axioms and rules of inference as constituting a "logic" for the language. 
Instead of speaking of an interpretation as sound or unsound for a logistic system (see 
below), we would then speak of a logic as being sound or unsound for a language. Indeed 
this alternative may have some considerations in its favor. But we reject it here, partly 
because of reluctance to change a terminology already fairly well established, partly 
because the alternative terminology leads to a twofold division in each of the subjects 
of syntax and semantics (§§08, 09)—according as they treat of the object language 
alone or of the object language together with a logic for it — which, especially in the 
case of semantics, seems unnatural, and of little use so far as can now be seen.)
lI7Besides these minimum essentials, the primitive basis may also include other 
notions introduced in order to use them in defining a well-formed formula or in stating 
the rules of inference. In particular the primitive symbols may be divided in some way 
into different categories; e.g., they may be classified as primitive constants, variables, 
and improper symbols, or various categories may be distinguished of primitive constants, 
of variables, or of improper symbols. The variables and the primitive constants together 
are usually called proper symbols. Rules may be given for distinguishing an occurrence 
of a variable in a well-formed formula as being a free occurrence or a bound occurrence, 
well-formed formulas being then classified as forms or constants according as they do or 
do not contain a free occurrence of a variable. Also rules may be given for distinguishing 
certain of the forms as propositional forms, and certain of the constants as sentences. 
In doing all this, the terminology often is so selected that, when the logistic system 
becomes a language by adoption of one of the intended principal interpretations (sec* 
below), the terms primitive constant, variable, improper symbol, proper symbol, free, 
bound, form, constant, propositional form, sentence come to have meanings in accord 
with the informal semantical explanations of §§02-06.
The primitive basis of a formalized language, or interpreted logistic system, is ob­
tained by adding the semantical rules (see below) to the primitive basis of the logistic 
system.

---


§07]
THE LOGISTIC METHOD
51
shall be effective in the sense that there is a method by which; whenever a 
formula is given, it can always be determined effectively whether or not it 
is well-formed; (III) the specification of the axioms shall be effective in the 
sense that there is a method by which, whenever a well-formed formula is 
given, it can always be determined effectively whether or not it is one of 
the axioms; (IV) the rules of inference, taken together, shall be effective in 
the strong sense that there is a method by which, whenever a proposed 
immediate inference is given of one well-formed formula as conclusion from 
others as premisses, it can always be determined effectively whether or not 
this proposed immediate inference is in accordance with the rules of infer­
ence.
(From these requirements it follows that the notion of a proof is effective 
in the sense that there is a method by which, whenever a finite sequence of 
well-formed formulas is given, it can always be determined effectively 
whether or not it is a proof. But the notion of a theorem is not necessarily 
effective in the sense of existence of a method by which, whenever a well- 
formed formula is given, it can always be determined whether or not it is 
a theorem—for there may be no certain method by which we can always 
either find a proof or determine that none exists. This last is a point to which 
we shall return later.)
As to requirement (I), we suppose that we are able always to determine 
about two given symbol-occurrences whether or not they are occurrences of 
the same symbol (thus ruling out by assumption such difficulties as that of 
illegibility). Therefore, if the number of primitive symbols is finite, the 
requirement may be satisfied just by giving the complete list of primitive 
symbols, written out in full. Frequently, however, the number of primitive 
symbols is infinite. In particular, if there are variables, it is desirable that 
there should be an infinite number of different variables of each kind 
because, although in any one well-formed formula the number of different 
variables is always finite, there is hardly a way to determine a finite upper 
limit of the number of different variables that may be required for some 
particular purpose in the actual use of the logistic system. When the number 
of primitive symbols is infinite, the list cannot be written out in full, but the 
primitive symbols must rather be fixed in some way by a statement of finite 
length in the meta-language. And this statement must be such as to conform 
to (I).
A like remark applies to (HI). If the number of axioms is finite, the re­
quirement can be satisfied by writing them out in full Otherwise the axioms 
must be specified in some less direct way by means of a statement of finite

---


52
INTRODUCTION
length in the meta-language, and this must be such as to conform to (III). 
It may be thought more elegant or otherwise more satisfactory that the 
number of axioms be finite; but we shall see that it is sometimes convenient 
to make use of an infinite number of axioms, and no conclusive objections 
appear to doing so if requirements of effectiveness are obeyed.
We have assumed the reader's understanding of the general notion of 
effectiveness, and indeed it must be considered as an informally familiar 
mathematical notion, since it is involved in mathematical problems of a 
frequently occurring kind, namely, problems to find a method of computa­
tion, i.e., a method by which to determine a number, or other thing, effec­
tively.118 We shall not try to give here a rigorous definition of effectiveness, 
the informal notion being sufficient to enable us, in cases we shall meet, 
to distinguish given methods as effective or non-effective.110
The requirements of effectiveness are (of course) not meant in the sense 
that a structure which is analogous to a logistic system except that it fails 
to satisfy these requirements may not be useful for some purposes or that 
it is forbidden to consider such—but only that a structure of this kind is 
unsuitable for use or interpretation as a language. For, however indefinite 
or imprecisely fixed the common idea of a language may be, it is at least 
fundamental to it that a language shall serve the purpose of communication. 
And to the extent that requirements of effectiveness fail, the purpose of 
communication is defeated.
Consider, in particular, the situation which arises if the definition of well-
118A well-known example from topology is the problem (still unsolved even for ele­
mentary manifolds of dimensionalities above 2) to find a method of calculating about 
any two closed simplicial manifolds, given by means of a set of incidence relations, 
whether or not they are homeomorphic—or, as it is often phrased, the problem to find 
a complete classification of such manifolds, or to find a complete set of invariants.
As another example, Euclid's algorithm, in the domain of rational integers, or in 
certain other integral domains, provides an effective method of calculating for any two 
elements of the domain their greatest common divisor (or highest common factor).
In general, an effective method of calculating, especially if it consists of a sequence of 
steps with later steps depending on results of earlier ones, is called an algorithm. (This 
is the long established spelling of this word, and should be preserved in spite of any 
considerations of etymology.)
lwFor a discussion of the question and proposal of a rigorous definition see a paper by 
the present writer in the American Journal of Mathematics, vol. 68 (1936), pp. 346-363, 
especially §7 thereof. The notion of effectiveness may also be described by saying that 
an effective method of computation, or algorithm, is one for which it would be possible 
to build a computing machine. This idea is developed into a rigorous definition by A. M. 
Turing in the Proceedings of the London Mathematical Society, vol. 42 (1936-1937), 
pp. 230-265 (and vol. 43 (1937), pp. 544—546). See further: S. C. Kleene in the Mathe- 
matische Annalen, vol. 112 (1936), pp. 727-742; E. L. Post in The Journal of Symbolic 
Logic, vol. 1 (1936), pp. 103-105; A. M. Turing in The Journal of Symbolic Logic, vol. 2 
(1937), pp. 153-163; Hilbert and Bernays, Grundlagen der Maihemaiik, vol. 2 (1939), 
Supplement II.

---


§07]
THE LOGISTIC METHOD
formedness is non-effective. There is then no certain means by which, when 
an alleged expression of the language is uttered (spoken or written), say as 
an asserted sentence, the auditor (hearer or reader) may determine whether 
it is well-formed, and thus whether any actual assertion has been made.120 
Therefore the auditor may fairly demand a proof that the utterance is well- 
formed, and until such proof is provided may refuse to treat it as constituting 
an assertion. This proof, which must be added to the original utterance in 
order to establish its status, ought to be regarded, it seems, as part of the 
utterance, and the definition of well-formedness ought to be modified to 
provide this, or its equivalent. When such modification is made, no doubt 
the non-effectiveness of the definition will disappear; otherwise it would be 
open to the auditor to make further demand for proof of well-formedness.
Again, consider the situation which arises if the notion of a proof is non- 
effective. There is then no certain means by which, when a sequence of 
formulas has been put forward as a proof, the auditor may determine wheth­
er it is in fact a proof. Therefore he may fairly demand a proof, in any 
given case, that the sequence of formulas put forward is a proof; and until 
this supplementary proof is provided, he may refuse to be convinced that the 
alleged theorem is proved. This supplementary proof ought to be regarded, 
it seems, as part of the whole proof of the theorem, and the primitive basis 
of the logistic system ought to be so modified as to provide this, or its 
equivalent.181 Indeed it is essential to the idea of a proof that, to any one 
who admits the presuppositions on which it is based, a proof carries final
1,0To say that an assertion has been made if there is a meaning evades the issue 
unless an effective criterion is provided for the presence of meaning. An understanding 
of the language, however reached, must include effective ability to recognize meaning­
fulness (in some appropriate sense), and in the purely formal aspect of the language, the 
logistic system, this appears as an effective criterion of well-formedness, 
lwPerhaps at first sight it will be thought that the proof as so mollified might con­
sist of something more than merely a sequence of well-formed formulas. For instance 
there might be put in at various places indications in the meta-language as to which 
rule of inference justifies the inclusion of a particular formula as immediately inferred 
from preceding formulas, or as to which preceding formulas are the premisses of the 
immediate inference.
But as a m atter of fact we consider this inadmissible. For our program is to express 
proofs (as well as theorems) in a fully formalized object language, and as long as any 
part of the proof remains in an unformalized meta-language the logical analysis must 
be held to be incomplete. A statement in the meta-language, e.g., that a particular 
formula is immediately inferred from particular preceding formulas—if it is not super­
fluous and therefore simply omissible—must always be replaced in some way by one or 
more sentences of the object language.
Though we use a meta-language to set up the object language, we require that, once 
set up, the object language shall be an independent language capable, without continued 
support and supplementation from the meta-language, of expressing those things for 
which it was designed.

---


54
INTRODUCTION
conviction. And the requirements of effectiveness (l)-(IV ) may be thought 
of as intended just to preserve this essential characteristic of proof.
After setting up the logistic system as described, we still do not have a 
formalized language until an interpretation is provided. This will require a 
more extensive meta-language than the restricted portion of English used 
in setting up the logistic system. However, it will proceed not by translations 
of the well-formed formulas into English phrases but rather by semantical 
rides which, in general, use rather than mention English phrases (cf. §08), 
and which shall prescribe for every well-formed formula either how it 
denotes122 (so making it a proper name in the sense of §01) or else how it has 
values122 (so making it a form in the sense of §02).
In view of our postulation of two truth-values (§04), we impose the re­
quirement that the semantical rules, if they are to be said to provide an 
interpretation, must be such that the axioms denote truth-values (if they 
are names) or have always truth-values as values (if they are forms), and 
the same must hold of the conclusion of any immediate inference if it holds 
of the premisses. In using the formalized language, only those well-formed 
formulas shall be capable of being asserted which denote truth-values (if
l8*Because of the possibility of misunderstanding, we avoid the wordings “what it 
denotes" and "what values it has."
For example, in one of the logistic systems of Chapter X  we may find a well-formed 
formula which, under a principal interpretation of the system, is interpreted as denoting: 
the greatest positive integer n such that 1 +  nr is prime, r being chosen as the least 
even positive integer corresponding to which there is such a greatest positive integer n. 
Thus the semantical rules do in a sense determine what this formula denotes, but the 
remoteness of this determination is measured by the difficulty of the mathematical 
problem which must be solved in order to identify in some more familiar manner the 
positive integer which the formula denotes, or even to say whether or not the formula 
denotes 1.
Again in the logistic system F lh of Chapter III (or A0 of Chapter V) taken with its 
principal interpretation, there is a well-formed formula which, according to the seman­
tical rules, denotes the truth-value thereof that every even number greater than 2 is 
the sum of two prime numbers. To say that the semantical rules determine what this 
formula denotes seems to anticipate the solution of a famous problem, and it may be 
better to think of the rules as determining indirectly what the formula expresses.
In assigning how (rather than what) a name denotes we are in effect fixing its sense, 
and in assigning how a form has values we fix the correspondence of sense values of 
the form (see footnote 27) to concepts of values of its variables. (This statement of the 
matter will be sufficiently precise for our present purposes, though it remains vague 
to the extent that we have left the meaning of "sense" uncertain—see footnotes 15, 37.)
It will be seen in particular examples below (such as rules a-g of §10, or rules a-f 
of §30, or rules a-£ of §30) that in most of our semantical rules the explicit assertion is 
that certain well-formed formulas, usually on certain conditions, are to denote certain 
things or to have certain values. However, as just explained, this explicit assertion is 
so chosen as to give implicitly also the sense or the sense values. No doubt a fuller treat­
ment of semantics must have additional rules stating the sense or the sense values ex­
plicitly, but this would take us into territory still unexplored.

---


§07]
THE LOGISTIC METHOD
55
th ey  are n am es) or have a lw a y s tru th -valu es as v a lu es {if th ey  are form s); 
and o n ly  th o se shall be cap ab le of b ein g righ tly asserted  w hich d en ote tru th 
(if th ey  are nam es) or h a v e a lw a y s th e value tru th  (if th ey are form s). Since 
it is in ten d ed  th a t proof o f a theorem  shall ju stify  its assertion, w e ca ll an 
in terp retation  of a logistic sy ste m  sound if, u nd er it, all the axiom s eith er 
denote tru th  or h ave a lw a y s th e  value truth, a n d  if further th e sam e th in g 
holds of th e  conclusion of a n y  im m ed iate inference if it holds of the prem isses. 
In th e con trary case w e ca ll th e in terp retation  unsound. A form alized lan ­
guage is ca lled  sound or u n so u n d  according as th e interpretation b y  w hich 
it is o b ta in ed  from  a lo g istic sy ste m  is sound or unsou nd. And an u nsou nd 
in terp retation  or an u n sou n d  language is to  be rejected.
(The requirem en ts, an d  th e defin ition  of sou n d n ess, in the foregoing p a ra ­
graph are b ased  on tw o tru th -v a lu es. T h ey are sa tisfa cto ry  for every form al­
ized lan gu age w hich w ill receiv e su b stan tial consid eration in this book. 
B u t th e y  m u st be m odified correspond ingly, in case th e schem e of tw o  tru th- 
valu es is m od ified — cf. th e rem ark in §19.)
T he sem a n tica l rules m u st in th e first in stan ce b e stated  in a presupposed 
and therefore unform alized m eta-langu age, here taken to be ord in ary 
E n glish . S u b seq u en tly, for th eir m ore ex a ct stu d y , w e m ay form alize the 
m eta-lan gu age (using a p resu p p osed  m eta-m eta-lan gu age and follow in g the 
m eth od  alread y described for form alizing th e o b ject language) and resta te 
th e sem a n tica l rules in th is form alized  langu age. (T his leads to  th e su b ject 
of semantics (§09).)
A s a con d ition  of rigor, w e require th at th e p roof of a theorem  (of th e o b ­
ject lan g u a g e) shall m ake n o reference to  or u se of an y in terp retation , b ut 
shall p roceed  purely b y th e rules of th e lo g istic sy stem , i.e., shall be a proo/ 
in th e sen se defined ab ove for logistic sy stem s. M otivation  for th is is th ree­
fold , th ree rath er different approaches issu in g in  th e  sam e criterion. In  the 
first p lace th is m ay be con sid ered  a m ore precise form ulation of th e trad i­
tion al d istin ctio n  b etw een  form  and m atter (§00) and of the p rin cip le th a t 
the v a lid ity  of an argu m en t depends only on th e form — th e form  of a 
proof in a logistic sy stem  b e in g  th ou gh t of as som eth in g com m on to  its 
m ean in gs under various in terp retation s of th e lo g istic system . In th e secon d 
place th is represents the sta n d a rd  m ath em atical requirem ent of rigor th at 
a proof m u st proceed p u rely from  th e axiom s w ith ou t use of a n y th in g  
(how ever su p p osed ly o b v io u s) w hich is not s ta te d  in the axiom s; b u t th is 
requirem en t is here m od ified  and exten d ed  as follow s: that a p roof m ust 
proceed p u rely from  th e a x io m s b y  th e rules of inference, w ith o u t use of 
a n y th in g  n ot sta ted  in th e a x io m s or any m eth od  of inference n ot v a lid a ted

---


56
INTRODUCTION
by the rules. Thirdly there is the motivation that the logistic system is 
relatively secure and definite, as compared to interpretations which we may 
wish to adopt, since it is based on a portion of English as meta-language so 
elementary and restricted that its essential reliability can hardly be doubted 
if mathematics is to be possible at all.
It is also important that a proof which satisfies our foregoing condition 
of rigor must then hold under any interpretation of the logistic system, so 
that there is a resulting economy in proving many things under one pro­
cess.123 The extent of the economy is just this, that proofs identical in form 
but different in matter need not be repeated indefinitely but may be sum­
marized once for all.124
Though retaining our freedom to employ any interpretation that may be 
found useful, we shall indicate, for logistic systems set up in the following 
chapters, one or more interpretations which we have especially in mind for 
the system and which shall be called the principal interpretations.
The subject of formal logic, when treated by the method of setting up a 
formalized language, is called symbolic logic, or mathematical logic, or logistic.1*6 
The method itself we shall call the logistic method.
1MThis remark has now long been familiar in connection with the axiomatic method 
in mathematics (see below).
1MThe summarizing of a proof according to its form may indeed be represented to a 
certain extent, by the use of variables, within one particular formalized language. 
But, because of restricted ranges of the variables, such summarizing is less comprehend 
sive in its scope than is obtained by formalizing in a logistic system whose interpretation 
is left open.
The procedure of formalizing a proof in a logistic system and then employing the 
formalized proof under various different interpretations of the system may be thought 
of as a mere device for brevity and convenience of presentation, since it would be pos­
sible instead to repeat the proof in full each time it were used with a new interpretation. 
From this point of view such use of the meta-language may be allowed as being in 
principle dispensable and therefore not violating the demand (footnote 121) for an in­
dependent object language.
(If on the other hand we wish to deal rigorously with the notion of logical form of 
proofs, this must be in a particular formalized language, namely a formalized meta­
language of the language of the proofs. Under the program of §02 each variable of this 
meta-language will have a fixed range assigned in advance, according, perhaps, with the 
theory of types. And the notion of form which is dealt with must therefore be cor­
respondingly restricted, it would seem, to proofs of a fixed class, taking no account of 
sameness of form between proofs of this class and others (in the same or a different 
language). Presumably our informal references to logical form in the text are to be 
modified in this way before they can be made rigorous—cf. §09.)
1MThe w riter prefers the term “ mathematical logic," understood as meaning logic 
treated by the mathematical method, especially the formal axiomatic or logistic method. 
But both this term and the term “symbolic logic" are often applied also to logic as 
treated by a less fully formalized mathematical method, in particular to the “algebra 
of logic," which had its beginning in the publications of George Boole and Augustus 
De Morgan in 1847, and received a comprehensive treatm ent in Ernst Schrtider's 
Vorlesungen iiber die Algebra der LogiM (1890-1905). The term “logistic" is more defi-

---


§07]
THE LOGISTIC METHOD
57
Familiar in mathematics is the axiomatic method, according to which a 
branch of mathematics begins with a list of undefined terms and a list of 
assumptions, or postulates involving these terms, and the theorems are to 
be derived from the postulates by the methods of formal logic.128 If the last 
phrase is left unanalyzed, formal logic being presupposed as already known, 
we shall say that the development is by the informal axiomatic method.127 
And in the opposite case we shall speak of the formal axiomatic method.
The formal axiomatic method thus differs from the logistic method only 
in the following two ways:
(1) In the logistic system the primitive symbols are given in two cate­
gories: the logical primitive symbols, thought of as pertaining to the under­
lying logic, and the undefined terms, thought of as pertaining to the particular 
branch of mathematics. Correspondingly the axioms are divided into two 
categories: the logical axioms, which are well-formed formulas containing 
only logical primitive symbols, and the postulates™* which involve also 
the undefined terms and are thought of as determining the special branch of 
mathematics. The rules of inference, to accord with the usual conception of
nitely restricted to the method described in this section, and has also the advantage that 
it is more easily made an adjective. (Sometimes "logistic" has been used with special 
reference to the school of Russell or to the Frege-Russcll doctrine that mathematics 
is a branch of logic—cf. footnote 545. But we shall follow the more common usage 
which attaches no such special meaning to this word.)
“ Logica mathematica" and “ logistica" were both used by G. W. v. Leibniz along 
with “calculus ratiocinator," and many other synonyms, for the calculus of reasoning 
which he proposed but never developed beyond some brief and inadequate (though 
significant) fragments. Boole used the expressions "mathematical analysis of logic," 
"mathematical theory of logic.” "Mathcmatische Logik" was used by Schroder in 
1877, "mat&natifi&skaa logika" (Russian) by Platon Poretsky in 1884, "logica matcina- 
tica" (Italian) by Giuseppe Peano in 1891. "Symbolic logic" seems to have been first 
used by John Venn (in The Princeton Review, 1880), though Boole speaks of "sym ­
bolical reasoning." The word "logistic" and its analogues in other languages originally- 
meant the art of calculation or common arithmetic. Its modern use for mathematical 
logic dates from the International Congress of Philosophy of 1904, where it was proposed 
independently by Itelson, Lalande, and Couturat. Other terms found in the literature 
are "logischer Calcul" (Gottfried Ploucquet 1766), "algoritlime logique" (G. F- Castillon 
1805), “calculus of logic" (Boole 1847), "calculus of inference" (Dc Morgan 1847), 
"logique algorithmique" (J. R. L. Delbueuf 1876), "Logikkalkul" (Schroder 1877), 
"theoretische Logik" (Hilbert and Ackcrmann 1928). Also "Boole's logical algebra" 
(C. S. Peirce 1870), "logique algebrique de Boole" (Louis Liard 1877), "algebra of 
logic" (Alexander Macfarlane 1879, C. S. Peirce 1880).
1MAccounts of the axiomatic method may of course be found in many mathematical 
textbooks and other publications. An especially good exposition is in the Introduction 
to Veblen and Young’s Projective Geometry, vol. 1 (1910).
lwThis is the method of most mathematical treatises, which proceed axiomatically 
but are not specifically about logic—in particular of Veblen and Young (preceding 
footnote).
lMThe words "axiom ,, and “postulate” have been variously used, either as synon­
ymous or with varying distinctions between them, by the present writer among others 
In this book, however, the terminology here set forth will be followed closely.

---


58
INTRODUCTION
the axiomatic method, must all be taken as belonging to the underlying 
logic. And, though they may make reference to particular undefined 
terms or to classes of primitive symbols which include undefined terms, 
they must not involve anything which, subjectively, we are unwilling to 
assign to the underlying logic rather than to the special branch of mathe­
matics.129
(2) 
In the interpretation the semantical rules are given in two categories. 
Those of the first category fix those general aspects of the interpretation 
which may be assigned, or which we are willing to assign, to the underlying 
logic. And the rules of the second category determine the remainder of the 
interpretation. The consideration of different representations or interpre­
tations of the system of postulates, in the sense of the informal axiomatic 
method, corresponds here to varying the semantical rules of the second 
category while those of the first category remain fixed.
08. Syntax. The study of the purely formal part of a formalized language 
in abstraction from the interpretation, i.e., of the logistic system, is called 
syntax, or, to distinguish it from the narrower sense of "syntax” as con­
cerned with the formation rules alone,130 logical syntax.m  The meta-language 
used in order to study the logistic system in this way is called the syntax 
language.131
We shall distinguish between elementary syntax and theoretical syntax.
The elementary syntax of a language is concerned with setting up the 
logistic system and with the verification of particular well-formed formulas,
1MOrdinarily, e.g., it would be allowed that the rules of inference should treat differ­
ently two undefined terms intended one to denote an individual and one to denote a 
class of individuals, or two undefined terms intended to denote a class of individuals 
and a relation between individuals; but not that the rules should treat differently two 
undefined term s intended both to denote a class of individuals. But no definitive con­
trolling principle can be given.
The subjective and essentially arbitrary character of the distinction between what 
pertains to the underlying logic and what to the special branch of mathematics is illus­
trated by the uncertainty which sometimes arises, in treating a branch of mathematics 
by the informal axiomatic method, as to whether the sign of equality is to be considered 
as an undefined term (for which it is necessary to state postulates). Again it is illustrated 
by Zermelo's treatm ent of axiomatic set theory in his paper of 1908 (cf. Chapter XI) 
in which, following the informal axiomatic method, he introduces the relation « of 
membership in a set as an undefined term, though this same relation is usually assigned 
to the underlying logic when a branch of mathematics is developed by the informal 
axiomatic method.
l*°Cf. footnote 116.
inThe terminology is due to Carnap in his Logische Syntax der Sprache (1934), trans­
lated into English (with some additions) as The Logical Syntax of Language (1937). In 
connection with this book see also reviews of it by Saunders MacLane in the Bulletin 
of the American Mathematical Society, vol. 44 (1938), pp. 171-176, and by S. C. Kleene 
in The Journal of Symbolic Logic, vol. 4 (1939), pp. 82-87.

---


§08]
SYNTAX
59
axiom s, im m ed iate in feren ces, and proofs as b ein g  such. T h e s y n ta x  lan gu age 
is th e restricted  p ortion  of E n g lish  w h ich  w as described in th e foregoing 
section , or a corresp on d in gly restricted  form alized  m eta-lan gu age, an d  the 
requirem en ts o f effectiv en ess, (I )-(I V ), m u st be observed. T h e d em on stra­
tion  o f d erived  rules an d  th eorem  sch em a ta , in th e sense of §§12, 33, and 
their a p p lica tio n  in p articu lar cases are also considered to  b elo n g  to ele­
m en ta ry  sy n ta x , p ro v id ed  th a t th e req u irem en t of effectiv en ess h o ld s w hich 
is ex p la in ed  in §12.
T h eoretical sy n ta x , on  th e other h an d , is th e  general m a th em a tica l th eory 
o f a lo g istic sy ste m  or sy ste m s a n d  is con cern ed  w ith  all th e con seq u en ces of 
their form al stru ctu re (in a b stra ctio n  from  th e in terp retation ). T h ere is no 
restriction  im p osed  as to  w h a t is availab le in th e sy n ta x  lan gu age, an d  re­
qu irem en ts of e ffectiv en ess are or m a y  be aban d on ed . In d eed  th e sy n ta x 
langu age m a y  b e ca p a b le of exp ressin g th e w h o le of e x ta n t m a th em a tics. B u t 
it m a y  also so m etim es b e desirable to  use a w eak er sy n ta x  la n gu age in order 
to ex h ib it resu lts as o b ta in ed  on th is w eak er basis.
L ike an y  branch of m a th em a tics, th eo retica l sy n ta x  m ay, an d  u ltim a tely  
m u st, be stu d ied  b y  th e a x io m a tic m eth od . H ere th e inform al an d  th e  form al 
axio m a tic m eth od  sh are 
th e im p ortan t ad v a n ta g e th a t th e particular 
character o f th e sy m b o ls an d  form ulas of th e o b ject language, as m ark s upon 
paper, sound s, or th e lik e, is ab stracted  from , and the pure th e o ry  of the 
structure of th e lo g istic sy stem  is d evelop ed . B u t th e form al a x io m a tic 
m eth o d — th e sy n ta x  la n g u a g e b ein g itse lf form alized  accord in g to  th e  pro­
gram  o f §07, b y  em p lo y in g  a m eta -m eta -la n g u a g e— has th e a d d itio n a l ad­
v a n ta g e of ex h ib itin g  m ore d efin itely  th e b asis on  w h ich resu lts are obtain ed , 
and of clarifyin g th e w a y  an d  th e e x te n t to  w h ich  certain resu lts m a y  be 
ob ta in ed  on a r e la tiv e ly  w eaker b asis.
In  th is b ook  w e sh all b e concern ed w ith  th e ta sk  of form alizin g an object 
lan gu age, an d  th eo retica l sy n ta x  w ill be trea ted  inform ally, p resu p p osin g 
in a n y  con n ection  su ch  gen eral k n ow led ge o f m ath em atics as is  necessary 
for th e w ork a t hand. T h u s w e do n ot a p p ly  even  the inform al a x io m a tic 
m eth o d  to  our trea tm en t of sy n ta x . B u t th e reader m u st a lw a y s und erstan d 
th a t sy n ta ctica l d iscu ssio n s are carried ou t in a sy n ta x  lan gu age w h ose for­
m alization  is u ltim a te ly  con tem p la ted , a n d  d istin ctio n s b ased  upon such 
form alization  m a y  b e relev a n t to th e d iscu ssion .
In  su ch  in form al d ev elo p m en t of sy n ta x , w e shall th in k  of th e sy n ta x  
lan gu age as b ein g a d ifferen t lan gu age from  th e  object la n gu age. B u t th e 
p ossib ility  is im p ortan t th a t a su fficien tly  a d eq u a te object lan gu age m ay be 
cap ab le of exp ressin g its o w n  sy n ta x , so th a t in this case th e u ltim a te for­

---


60
INTRODUCTION
malization of the syntax language may if desired consist in identifying it 
with the object language.132
We shall distinguish between theorems of the object language and theo­
rems of the syntax language (which often are theorems about the object 
language) by calling the latter syntactical theorems. Though we demonstrate 
syntactical theorems informally, it is contemplated that the ultimate formal­
ization of the syntax language shall make them theorems in the sense of §07, 
i.e., theorems of the syntax language in the same sense as that in which we 
speak of theorems of the object language.
We shall require, as belonging to the syntax language: first, names of the 
various symbols and formulas of the object language; and secondly, vari­
ables which have these symbols and formulas as their values. The former 
will be called syntactical constants, and the latter, syntactical variables.133
As syntactical variables we shall use the following: as variables whose 
range is the primitive symbols of the object language, bold Greek small 
letters (a, (3, y, etc.); as variables whose range is the primitive constants and 
variables of the object language—see footnote 117—bold roman small 
letters (a, b, c, etc.); as variables whose range is the formulas of the object 
language, bold Greek capitals (I\ A, etc.); and as variables whose range is 
the well-formed formulas of the object language, bold roman capitals (A, 
B, G, etc.). Wherever these bold letters are used in the following chapters 
the reader must bear in mind that they are not part of the symbolic appara­
tus of the object language but that they belong to the syntax language 
and serve the purpose of talking about the object language. In use of the 
object language as an independent language, bold letters do not appear 
(just as English words never appear in the pure text of a Latin author 
though they do appear in a Latin grammar written in English).
As a preliminary to explaining the device to which we resort for syntac­
tical constants, it is desirable first to consider the situation in ordinary
1*aCf. footnote 109. In particular the developments of Chapter V III show th at the 
logistic system of Chapter VII is capable of expressing its own syntax if given a suitable 
interpretation different from the principal interpretation of Chapter VII, namely, an 
interpretation in which the symbols and formulas of the logistic system itself are counted 
among the individuals, as well as all finite sequences of such formulas, and the functional 
constant S is given an appropriate {quite complicated) interpretation, details of which 
may be made out by following the scheme of Gddel numbers th at is set forth in Chapter 
VIII.
lMGiven the apparatus of syntactical variables, we conld actnally avoid the use of 
syntactical constants by resorting to appropriate circumlocutions in cases where syn­
tactical constants would otherwise seem to be demanded. Indeed the example of the 
preceding footnote illustrates this, as will become clear in connection with the cited 
chapters. But it is more natural and convenient, especially in an informal treatm ent of 
syntax, to allow free use of syntactical constants.

---


§08]
SYNTAX
61
English, with no formalized object language specially in question. We must 
take into account the fact that English is not a formalized language and the 
consequent uncertainty as to what are its formation rules, rules of inference, 
and semantical rules, the contents of ordinary English grammars and dic­
tionaries providing only some incomplete and rather vague approximations 
to such rules. But, with such reservations as this remark implies, we go on to 
consider the use of English in making syntactical statements about the 
English language itself.
Frequently found in practice is the use of English words antonymously (to 
adopt a terminology due to Carnap), i.e., as names of those same words.134 
Examples are such statements as “The second letter of man is a vowel," 
“Man is monosyllabic," "Man is a noun with an irregular plural." Of course 
it is equivocal to use the same word, man, both as a proper name of the 
English word which is spelled by the thirteenth, first, fourteenth letters of 
the alphabet in that order, and as a common name (see footnote 6 ) of 
featherless plantigrade biped mammals135- - but an equivocacy which, like 
many others in the natural languages, is often both convenient and harmless. 
Whenever there would otherwise be real doubt of the meaning, it may be 
removed by the use of added words in the sentence, or by the use of quotation 
marks, or of italics, as in: "The word man is monosyllabic"; " ‘Man' is 
monosyllabic"; "Man is monosyllabic."
Following the convenient and natural phraseology of Quine, we may 
distinguish between use and mention of a word or symbol. In "Mari is a 
rational animal" the word "man" is used but not mentioned. In "The Eng­
lish translation of the French word homme has three letters" the word "man" 
is mentioned but not used. In "Man is a monosyllable" the word "man" is 
both mentioned and used, though used in an anomalous manner, namely 
autonymously.
Frege introduced the device of systematically indicating autonymy by 
quotation marks, and in his later publications (though not in the Bcgvijfs- 
schrift) words and symbols used autonymously are enclosed in single quota­
tion marks in all cases. This has the effect that a word enclosed in single
m In the term inology of the Scholastics, use of a word as a name of itself, i e , to de­
note itself as a word, was called s u p p o s i U u  m a t e r i a l 's Opposed to this ns s n p p v s i t w  
formalis was the use of a noun in its proper or ordinary meaning. This term inology is 
sometim es still convenient.
The various further distinctions of s u p p o s i t i o n s  are too cumbrous, and too uncertain, 
to be usable. All of them , like th a t between s u p p o s itio  m a te ria lis and fo r m a lis , refer to 
peculiarities and irregularities of meaning which are found in many natural languages 
but which have to be elim inated in setting up a formalized language.
184To follow a definition found in T h e  C e n tu r y  D ictio n a ry.

---


62
I N T R O D U C T I O N
quotation marks is to be treated as a different word from that without the 
quotation marks—as if the quotation marks were two additional letters in 
the spelling of the word—and equivocacy is thus removed by providing two 
different words to correspond to the different meanings. Many recent writers 
follow Frege in this systematic use of quotation marks, some using double 
quotation marks in this way, and others following Frege in using single 
quotation marks for the purpose, in order to reserve double quotation marks 
for their regular use as punctuation. As the reader has long since observed, 
Frege's systematic use of quotation marks is not adopted in this book.136 
But we may employ quotation marks or other devices from time to time, 
especially in cases in which there might otherwise be real doubt of the 
meaning.
To return to the question of syntactical constants for use in developing the 
syntax of a formalized object language, we find that there is in this case 138
138Besides being rath er awkward in practice, such system atic use of quotation m arks 
is open to some unfortunate abuses and m isunderstandings. One of these is the misuse 
of quotation m arks as if they denoted a function from things (of some category) to 
names of such things, or as if such a function m ight be em ployed a t all w ithout some 
more definite account of it. Related to this is the tem ptation to use in the role of a 
syntactical variable the expression obtained by enclosing a variable of an object lan ­
guage in quotation m arks, though such an expression, correctly used, is not a variable 
of any kind, and not a form but a constant.
Also not uncom m on is the false impression th a t trivial or self-evident propositions 
are expressed in such statem ents as the following: 1 'Snow is w hite' is true if and only 
if snow is w hite' (Tarski's exam ple); ‘ ‘Snow is white' m eans th a t snow is w hite';
‘Cape Town' is the [or aj name of Cape Tow n.'
This last m isunderstanding may arise also in connection with autonym y. A useful 
method of com batting it is th at of translation into another language (cf. a rem ark by 
C. H. Langford in T h e  J o u r n a l oj S y m b o lic  L o g ic, vol. 2 (1937), p. 63). For exam ple, 
the proposition th a t 'Cape Town' is the nam e of Cape Town would be conveyed thus 
to an Italian (whom we m ay suppose to have no knowledge of English): ‘ ‘Cape Town' 
e il nome di C itta del Capo.' Assuming, as we may, th a t the Italian  words have exactly 
the same sense as the English words of which we use them  as translations— in particular 
th a t 'C itta del Capo' has the same sense as ‘Cape Town' and th a t ' 'Cape Town' ' has 
the same sense in Italian  as in English— we see th a t the Italian sentence and its English 
translation m ust express the very same proposition, which can no more be a triviality 
when conveyed in one language th an  it can in another.
The foregoing exam ple may be clarified by recalling the rem ark of footnote 8 th a t 
the name relation is properly a ternary relation, and may be reduced to a binary re­
lation only by fixing th e language in a particular context. Thus we have the more ex­
plicit English sentences; ' 'Cape Town’ is the English name of Cape Tow n'; ' 'C itti del 
Capo' is the Italian nam e of Cape Town.' The Italian translations are: ' ‘Cape Town' b 
il nome inglese di Cittei del Capo'; ‘ 'CitteL del Capo’ b il nome italiano di C itta del Capo.' 
Of the two propositions in question, the first one has a false appearance of obviousness 
when expressed in English, the illusion being dispelled on translation into Italian; 
the second one contrariw ise does not seein obvious or trivial when expressed in English, 
but on translation into Italian acquires the appearance of being so.
(In the three preceding paragraphs of this footnote, we have followed Frege's syste­
matic use of single quotation marks, and the paragraphs are to be read w ith th a t under­
standing, As explained, we do not follow this usage elsewhere.)

---


§08]
SYNTAX
63
nothing equivocal in using the symbols and formulas of the object language 
autonymously in the syntax language, provided that care is taken that no 
formula of the object language is also a formula of the syntax language in 
any other wise than as an autonym. Therefore we adopt the following 
practice:
The primitive symbols of the object language will be used in the syntax 
language as names of themselves, and juxtaposition will be used for juxta­
position.137
This is the ordinary usage in mathematical writing, and has the advantage 
of being self-explanatory. Though we employ it only informally, it is also 
readily adapted to incorporation in a formalized syntax language138 (and in 
fact more so than the convention of quotation marks).
As a precaution against equivocation, we shall hereafter avoid the 
practice—which might otherwise sometimes be convenient—of borrowing 
formulas of the object language for use in the syntax language (or other 
metalanguage) with the same meaning that they have in the object 
language. Thus in all cases where a single symbol or a formula of 
the object language is found as a constituent in an English sentence, 
it is to be understood in accordance with the italicized rule above, i.e., 
autonymously.
Since we shall later often introduce conventions for abbreviating well- 
formed formulas of an object language, some additional explanations \frill 
be necessary concerning the use of syntactical variables and syntactical 
constants (and concerning autonymy) in connection with such abbreviations. 
These will be indicated in §11, where such abbreviations first appear. But, 
as explained in that section, the abbreviations themselves and therefore 
any special usages in connection with them are dispensable in principle, 
however necessary practically. In theoretical discussions of syntax and in 
particular in formalizing the syntax language, the matter of abbreviations 
of well-formed formulas may be ignored.
187I.e., juxtaposition will be used in the syntax language as a binary connective having 
the operation of juxtaposition as its associated function. Technically, some added no­
tation is needed to show association, or some convention abo u t the m atter, such as 
th a t of association to the left (as in §11). B ut In practice, because of the associativity 
of juxtaposition, there is no difficulty in this respect.
15BThis is, of course, on the assum ption th a t the sy n tax  language is a different lan­
guage from the object language.
If on the contrary a form alized language is to contain nam es of its own form ulas, 
then a nam e of a form ula m ust ordinarily not be th a t formula. E .g., a variable 
of a language m ust not be, in th a t sam e language, also a nam e of itself; for a proper 
name of a variable is no variable b u t a constant (as already rem arked, in another con­
nection, in footnote 136).

---


64
I N T R O D U C T I O N
09. Sem antics. Let us imagine the users of a formalized language, 
say a written language, engaged in writing down well-formed formulas of 
the language, and in assembling sequences of formulas which constitute 
chains of immediate inferences or, in particular, proofs. And let us imagine 
an observer of this activity who not only does not understand the language 
but refuses to believe that it is a language, i.e., that the formulas have 
meanings. He recognizes, let us say, the syntactical criteria by which for­
mulas are accepted as well-formed, and those by which sequences of well- 
formed formulas are accepted as immediate inferences or as proofs; but he 
supposes that the activity is merely a game—analogous to a game of chess 
or, better, to a chess problem or a game of solitaire at cards—the point of 
the game being to discover unexpected theorems or ingenious chains of 
inferences, and to solve puzzles as to whether and how some given formula 
can be proved or can be inferred from other given formulas.139
To this observer the symbols have only such meaning as is given to them 
by the rules of the game—only such meaning as belongs, for example, to 
the various pieces at chess. A formula is for him like a position on a chess­
board, significant only as a step in the game, which leads in accordance 
with the rules to various other steps.
All those things about the language which can be said to and understood 
by such an observer while he continues to regard the use of the language as 
merely a game constitute the (theoretical) syntax of the language. But those 
things which are intelligible only through an understanding that the well- 
formed formulas have meaning in the proper sense, e.g., that certain of them 
express propositions or that they denote or have values in certain ways, 
belong to the semantics of the language.
Thus the study of the interpretation of the language as an interpretation 
is called semantics.1*0 The name is applied especially when the treatment is
lMA comparison of the rules of arithm etic to those of a game of chess was made by 
J. Tliomae (1898] and figures in the controversy between Thom ae and Frege (1903- 
1908). The same comparison was used by H erm ann Weyl (1924) in order to describe 
Hilbert's program  of metamatkemalics or syntax of a m athem atical object language.
U0The name (or its analogue m Polish) was introduced by Tarski in a paper in 
Przeglc^d FUozoficzny, vol. 39 (1936), pp. 50-57, translated into Germ an as "Grundle- 
gung der wissenschaftlichen Sem antik” in Actes du Congrds International de Philosophic 
Scientijique (1936). Other im portant publications in the field of sem antics are: Tarski's 
Po]§cie Prawdy w Jgzykach Nauk Dedukcyjnych (1933), afterw ards translated into 
German (and an im portant appendix added) as “ Der W ahrheitsbegriff in den forma- 
lisierten Sprachen" in Studia Philosophica, vol. 1 (1936) pp. 261-405; and Carnap's 
Introduction to Semantics (1942). Concerning Carnap's book see a review by the present 
writer in The Philosophical Review, vol. 52 (1943), pp. 298-304.
The word semantics has various other meanings, m ost of them  older than th a t in 
question here. Care m ust be taken to avoid confusion on this account. B ut in this book 
the word will have always the one meaning, intended to be the sam e (or substantially

---


§09]
S E M A N T I C S
65
in a formalized meta-language. But in this book we shall not go beyond some 
unformalized semantical discussion, in ordinary English.
Theorems of the semantical meta-language will be called semantical theo­
rems, and both semantical and syntactical theorems will be called metatheo­
rems, in order to distinguish them from theorems of the object language.
As appears from the work of Tarski, there is a sense in which semantics 
can be reduced to syntax. Tarski has emphasized especially the possibility 
of finding, for a given formalized language, a purely syntactical property 
of the well-formed formulas which coincides in extension with the semantical 
property of being a true sentence. And in Tarski's Wahrheitsbegriff141 the prob­
lem of finding such a syntactical property is solved for various particular 
formalized languages.142 But like methods apply to the two semantical con­
cepts of denoting and having values, so that syntactical concepts may be found 
which coincide with them in extension.143 Therefore, if names expressing
so) as th a t in which it is used by Tarski, C. W. M orns [Foundations of (he Theory of 
Signs, 1938), Carnap, G. D. W. Berry [Harvard University, Summaries of Theses 1942, 
pp. 330-334).
m Cited in the preceding footnote.
U8T arski solves also, for various particular form alized languages, the problem  of 
finding a syntactical relation which coincides in extension with the sem antical relation 
of satisfying a propositional form.
In  a paper published in Monatshefte fiir Mathematik and Physik, vol. 42, no. 1 (1935), 
therefore later than T arski's Poj§cie Prawdy but earLier than tlie G erm an translation 
and its appendix, Carnap also solves both problem s (of finding syntactical equivalents 
of being a true sentence and of satisfying a propositional form) lor a particular formal­
ized language and in fact for a stronger language than any for which this had previously 
been done by Tarski. C arnap's procedure can be simplified in the light of Tarski's 
appendix or as suggested by Kleene in his review cited in footnote 131.
On the theory of m eaning which we are here adopting, the sem antical concepts of 
being a true sentence and of satisfying a propositional form are reducible to those of 
denoting and having values, and these results of Tarski and Carnap are therefore 
im plicit in the statem ent of the following footnote.
1<8More explicitly, this m ay be done as follows. In  §07, in discussing the semantical 
rules of a formalized language, wc thought of the concepts of denoting and of having 
values as being known in advance, and we used the sem antical rules for the purpose 
of giving meaning to the previously uninterpreted logistic system. B ut instead of this it 
•would be possible to give no m eaning in advance to the words ‘'denote" and "have 
values" as they occur in the sem antical rules, and then to regard the sem antical rules, 
taken together, as constituting definitions of "denote" and "have values" (in the same 
way th a t the form ation rules of a logistic system  constitute a definition of " well- 
form ed"). The concepts expressed by "denote" and "have values" as thus defined 
belong to  theoretical syntax, nothing sem antical having been used in their definition. 
B ut they coincide in extension with the sem antical concepts of denoting and having 
values, as applied to the particular formalized language.
The situation m ay be clarified by recalling th at a particular logistic system  may be 
expected to have m any sound interpretations, leading to many different assignments 
of denotations and values to its well-formed formulas. These assignments of denotations 
and values to the well-formed formulas may be m ade as abstract correspondences, so 
th a t their treatm ent belongs to theoretical syntax. Semantics begins when we decide 
the m eaning of the well-formed formulas by fixing a particular interpretation of the 
system . The distinction betw een semantics and sy n tax  is found in the different signif-

---


66
I N T R O D U C T I O N
these two concepts are the only specifically semantical (non-syntactical) 
primitive symbols of a semantical meta-language, it is possible to transform 
the semantical meta-language into a syntax language by a change of inter­
pretation which consists only in altering the sense of those names without 
changing their denotations.
However, a sound syntax language capable of expressing such syntactical 
equivalents of the semantical concepts of denoting and having values—or 
even only a syntactical equivalent of the semantical property of truth— 
must ordinarily be stronger than the object language (assumed sound), in 
the sense that there will be theorems of the syntax language of which no 
translation (i.e., sentence expressing the same proposition) is a theorem of 
the object language. Else there will be simple elementary propositions about 
the semantical concepts such that the sentences expressing the correspond­
ing propositions about the syntactical equivalents of the semantical con­
cepts are not theorems of the syntax language.144
For various particular formalized languages this was proved (in effect) 
by Tarski in his Wahrheitsbegriff. And Tarski's methods146 are such that they 
can be applied to obtain the same result in many other cases—in particular 
in the case of each of the object languages studied in this book, when a 
formalized syntax language of it is set up in a straightforward manner. No 
doubt Tarski’s result is capable of precise formulation and proof as a result 
about a very general class of languages, but we shall not attempt this.
The significance of Tarski’s result should be noticed as it affects the ques­
tion of the use of a formalized language as semantical meta-language of 
itself. A sound and sufficiently adequate language may indeed be capable
icance given to one particular interpretation and to its assignm ent of denotations and 
values to the well-formed formulas; but w ithin the domain of formal logic, including 
pure syntax and pure semantics, nothing can be said about this different significance 
except to postulate it as different.
Many similar situations are fam iliar in m athem atics. For instance, the distinction 
between plane Euclidean metric geometry and plane projective geom etry may be found 
in the different significance given to one particular straight line and one particular 
elliptic involution on it. And it seems not unjustified to say th a t the sense in which 
semantics can be reduced to syntax is like th a t in which Euclidean m etric geometry 
can be reduced to projective geometry.
All this suggests that, in order to m aintain the distinction of sem antics from syntax, 
"denote" and "have values" should be introduced as undefined term s and treated by the 
axiomatic m ethod. Our use of semantical rules is intended as a step towards this. And in 
fact Tarski's W a k r h e its b e g n d  already contains the proposal of an axiom atic theory of 
truth as an alternative to that of finding a syntactical equivalent of the concept of truth.
m A more precise statem ent of this will be found in Chapter V III, as it applies to the 
special case of the logistic system of Chapter VII when interpreted, in the m anner 
indicated in footnote 132, so as to be capable of expressing its own syntax.
U5Related to those used by K urt Godel in the proof of his incompleteness theorems, 
set forth in C hapter V III.

---


§09]
S E M A N T I C S
67
of expressing its own syntax (cf, footnote 132) and its own semantics, in 
the sense of containing sentences which express at least a very comprehen­
sive class of the propositions of its syntax and its semantics. But among 
these sentences, if certain very general conditions are satisfied, there will 
always be true sentences of a very elementary semantical character which 
are not theorems—sentences to the effect, roughly speaking, that such and
such a particular sentence is true if and only i f ___ , the blank being filled
by that particular sentence.148 Hence, on the assumption that the language 
satisfies ordinary conditions of adequacy in other respects, not all the se­
mantical rules (in the sense of §07), when written as sentences of the lan­
guage, are theorems.
On account of this situation, the distinction between object language and 
meta-language, which first arises in formalizing the object language, re­
mains of importance even after the task of formalization is complete for 
both the object language and the meta-language.
In concluding this Introduction, let us observe that much of what we 
have been saying has been concerned with the relation between linguistic 
expressions and their meaning, and therefore belongs to semantics. However, 
our interest has been less in the semantics of this or that particular language 
than in general features common to the semantics of many languages. And 
very general semantical principles, imposed as a demand upon any language 
that we wish to consider at all, have been put forward in some cases, notably 
assumptions (1), (2), (3) of §01 and assumption (4) of §02.* 147
We have not, however, attempted to formalize this semantical discussion, 
or even to put the material into such preliminary order as would constitute 
a first step toward formalization. Our purpose ha? been introductory and 
explanatory, and it is hoped that ideas to which the reader has thus been 
informally introduced will be held subject to revision or more precise for­
mulation as the development continues.
From time to time in the following chapters we shall interrupt the rig­
orous treatment of a logistic system in order to make an informal semantical 
aside. Though in studying a logistic system we shall wish to hold its inter­
pretation open, such semantical explanations about a system may serve in
148 A more careful statem ent is given by TausUi.
By the results of Gbdel referred to m the preceding footnote (or alternatively by 
T arski's reduction of sem antics to syntax), true syntactical sentences which are not 
theorem s must also be expected. But these are of not quite so elem entary a character. 
And the fundam ental syntactical rules described in §07 may nevertheless all be theorems 
when w ritten as sentences of the language.
147And assum ption (5) of footnote 30.

---


68
INTRODUCTION
particular to show a motivation for consideration of it by indicating its 
principal interpretations (cf. §07). Except in this Introduction, semantical 
passages will be distinguished from others by being printed in smaller type, 
the small type serving as a warning that the material is not part of the formal 
logistic development and must not be used as such.
As we have already indicated, it is contemplated that semantics itself 
should ultimately be studied by the logistic method.
But if semantical passages in this Introduction and in later chapters are 
to be rewritten in a formalized semantical language, certain refinements 
become necessary. Thus if the semantical language is to be a functional 
calculus of order a> in the sense of Chapter VI, or a language like that of 
Chapter X, then various semantical terms, such as the term "denote” 
introduced in §01, must give way to a multiplicity of terms of different 
types,148 and statements which we have made using these terms must be 
replaced by axiom schemata149 or theorem schemata149 with typical ambi­
guity.149 Or if the semantical language should conform to some alternative 
to the theory of types, changes of a different character would be required. 
In particular, following the Zermelo set theory (Chapter XI), we would have 
to weaken substantially the assumption made in §03 that every singulary 
form has an associated function, and explanations regarding the notation A 
would have to be modified in some way in consequence.
148All the expressions of the language—formulas, or well-formed formulas—may be 
treated as values of (syntactical) variables of one type. But terms "denote" of different
types are nevertheless necessary, because in "____denotes_____after filling the first
blank with a syntactical variable or syntactical constant, we may still fill the second 
blank with a variable or constant of any type.
Analogously, various other terms that we have used have to be replaced each by a 
multiplicity of terms of different types. This applies in particular to "thing," and the 
consequent weakening is especially striking in the case of footnote 9—which must 
become a schema with typical ambiguity.
See also the remark in the last paragraph of footnote 87.
UflThe terminology is explained in §§27, 30, 33, and Chapter VI. (The typical am bi­
guity required here is ambiguity with respect to type in the sense described in footnote 
578, and is therefore not the same as the typical ambiguity mentioned in footnote 585, 
which is ambiguity rather with respect to level.)

