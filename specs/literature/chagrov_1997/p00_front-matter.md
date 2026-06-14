<!-- Source: Chagrov & Zakharyaschev (1997). Modal Logic (Oxford Logic Guides 35). Front matter including Table of Contents and Preface. BibKey: ChagrovZakharyaschev1997 -->

OXFORD LOGIC GUIDES: 35 
General Editors 
DOV GABBAY 
ANGUS MACINTYRE 
DANA SCOTT 

OXFORD LOGIC GUIDES 
1. Jane Bridge: Beginning model theory: the completeness theorem and some 
consequences 
2. Michael Dummett: Elements of intuitionism 
3. A.S. Troelstra: Choice sequences: a chapter of intuitionistic mathematics 
4. J.L. Bell: Boolean-valued models and independence proofs in set theory (1st edition) 
5. Krister Seberberg: Classical propositional operators: an exercise in the foundation 
of logic 
6. G.C. Smith: The Boole-De Morgan correspondence 1842-1864 
7. Alec Fisher: Formal number theory and computability: a work book 
8. Anand Pillay: An introduction to stability theory 
9. H.E. Rose: Subrecursion: functions and hierarchies 
10. Michael Hallett: Cantorian set theory and limitation of size 
11. R. Mansfield and G. Weitkamp: Recursive aspects of descriptive set theory 
12. J.L. Bell: Boolean-valued models and independence proofs in set theory 
(2nd edition) 
13. Melvin Fitting: Computability theory: semantics and logic programming 
14. J.L. Bell: Toposes and local set theories: an introduction 
15. R. Kaye: Models of Peano arithmetic 
16. J. Chapman and F. Rowbottom: Relative category theory and geometric 
morphisms: a logical approach 
17. Stewart Shapiro: Foundations without foundationalism 
18. John P. Cleave: A study of logics 
19. R.M. Smullyan: GodeTs incompleteness theorems 
20. T.E. Forster: Set theory with a universal set: exploring an untyped universe 
21. C. McLarty: Elementary categories, elementary toposes 
22. R.M. Smullyan: Recursion theory for metamathematics 
23. Peter Clote and Jan Krajicek: Arithmetic, proof theory, and computational 
complexity 
24. A. Tarski: Introduction to logic and to the methodology of deductive sciences 
25. G. Malinowski: Many valued logics 
26. Alexandre Borovik and Ali Nesin: Groups of finite Morley rank 
27. R.M. Smullyan: Diagonalization and self-reference 
28. Dov M. Gabbay, Ian Hodkinson, and Mark Reynolds: Temporal logic: 
Mathematical foundations and computational aspects ( Volume 1) 
29. Saharon Shelah: Cardinal arithmetic 
30. Erik Sandewall: Features and fluents: Volume I: A systematic approach to the 
representation of knowledge about dynamical systems 
31. T.E. Forster: Set theory with a universal set: exploring an untyped universe 
(2nd edition) 
32. Anand Pillay: Geometric stability theory 
33. Dov. M. Gabbay: Labelled deductive systems 
34. Raymond M. Smullyan and Melvin Fitting: Set theory and the 
continuum problem 
35. Alexander Chagrov and Michael Zakharyaschev: Modal logic 

Modal Logic 
ALEXANDER CHAGROV 
Tver State University 
and 
MICHAEL ZAKHARYASCHEV 
Moscow State University 
and 
Institute of Applied Mathematics 
Russian Academy of Sciences 
CLARENDON PRESS • OXFORD 
1997 

Oxford University Press, Great Clarendon Street, Oxford 0X2 6DP 
Oxford New York 
Athens Auckland Bangkok Bogota Bombay 
Buenos Aires Calcutta Cape Town Dar es Salaam 
Delhi Florence Hong Kong Istanbul Karachi 
Kuala Lumpur Madras Madrid Melbourne 
Mexico City Nairobi Paris Singapore 
Taipei Tokyo Toronto 
and associated companies in 
Berlin Ibadan 
Oxford is a trade mark of Oxford University Press 
Published in the United States 
by Oxford University Press, Inc., New York 
© Alexander Chagrov and Michael Zakharyaschev, 1997 
All rights reserved. No part of this publication may be 
reproduced, stored in a retrieval system, or transmitted, in any 
form or by any means, without the prior permission in writing of Oxford 
University Press. Within the UK, exceptions are allowed in respect of any 
fair dealing for the purpose of research or private study, or criticism or 
review, as permitted under the Copyright, Designs and Patents Act, 1988, or 
in the case of reprographic reproduction in accordance with the terms of 
the licences issued by the Copyright Licensing Agency. Enquiries concerning 
reproduction outside those terms and in other countries should be sent to 
the Rights Department, Oxford University Press, at the address above. 
This book is sold subject to the condition that it shall not, 
by way of trade or otherwise, be lent, re-sold, hired out, or otherwise 
circulated without the publisher’s prior consent in any form of binding 
or cover other than that in which it is published and without a similar 
condition including this condition being imposed 
on the subsequent purchaser. 
A catalogue record for this book is available from the British Library 
Library of Congress Cataloging in Publication Data 
Data available 
ISBN 0 19 $53779 4 
Typeset by the authors 
Printed in Great Britain by 
Booker aft (Bath) Ltd 
Midsomer Norton, Avon 

To our wives 
Lilia and Olga 

PREFACE 
Modal logic is a branch of mathematical logic studying mathematical models of 
correct reasoning which involves various kinds of necessity-like and 
possibilitylike operators. 
The first modal systems were created in the 1910s and later by Lewis (cf. 
Lewis and Langford, 1932) who used the operators “it is necessary” and “it is 
possible” for analyzing other logical connectives, in particular implication. Orlov 
(1928) and Godel (1933a) constructed modal systems with the operator “it is 
provable” and exploited them to interpret Heyting’s intuitionistic logic. More 
recently numerous modal systems have originated from different sources. They 
include: 
• Philosophy, which studies the categories of necessity, contingency, 
causality, etc., and gives rise to logics with alethic (“it is necessary” and “it is 
possible”), deontic (“it is obligatory” and “it is permitted”), epistemic (“it 
is known” and “it does not contradict to what is known”), tense (“at all 
future times” and “eventually”), and some other modal operators; 
• Foundations of mathematics, in which intuitionistic logic and provability 
logic (with the modal operators “it is provable in a given formal theory, 
say Peano arithmetic” and “it is consistent with the theory”) were created; 
• Computer science, which developed dynamic logic (with operators like 
“after every execution of the program” and “after some execution of the 
program”) and temporal logic (with “henceforth”, “sometimes” and other 
temporal operators) for describing the behavior of computer programs; 
• Cognitive science, in which nonmonotonic modal logics, default and au- 
toepistemic logics (with the operators “it is believed” and “it is consistent 
with the current knowledge base”) were designed; 
• Linguistics studying modalities in natural languages. 
(This list is by no means complete; modal logics may have rather unexpected 
sources, for instance, quantum mechanics.) Although created in different fields 
and for different purposes, all these systems (their fragments with the 
corresponding necessity-like and possibility-like operators, to be more exact) have so 
much in common that can be definitely attributed to the same family of logics. 
This family turns out to be very extensive, and not only because there are many 
kinds of modal operators. Each particular operator may be explicated in different 
ways, which gives rise to subfamilies of deontic logics, epistemic logics, etc. For 
example, one application may require a temporal logic of discrete linear time, 
while another a temporal logic of branching continuous time. 
Modal logic is not just a collection of systems of that sort: in fact they 
are subjects of more special disciplines. Modern modal logic—at least as it is 

PREFACE 
viii 
understood in this book—abstracts from those particular systems and considers 
a general notion (or notions) of modal logic as a set of formulas in a certain 
language containing certain axioms and closed under certain inference rules. In 
other words, it deals with a class of extensions of a certain minimal modal system 
and its main concern is to develop general methods for investigating properties 
of logics in the class. It is this step of abstraction, made in the 1950s and 1960s, 
that distinguished modal logic as a separate discipline within mathematical logic 
and clearly formulated its object of studies. 
There are several degrees of freedom in the choice of the minimal modal 
system. We can choose between a propositional language and a predicate one, 
between a language with a single basic modal operator and a polymodal one. We 
should decide which non-modal basis—classical, intuitionistic, or some other—is 
preferable. And of course there is a wide choice of modal axioms and inference 
rules. (For a detailed classification of modal logics consult Segerberg (1982).) 
In this book our minimal system is the well known propositional unimodal 
classical logic K, and we consider the class of its quasi-normal (i.e., closed 
under modus ponens and substitution) extensions. This choice is motivated by two 
reasons. First, almost all important modal systems belong to this class or are 
reducible in one sense or another to its logics, or can be handled by a similar 
technique. It is this class that has mostly attracted modal logicians’ attention, 
and for which sufficiently general methods have been developed. And second, 
modal operators behave, in a sense, like quantifiers and so even the 
propositional modal language turns out to be very rich and expressive. The class under 
consideration contains logics with any conceivable combination of properties and 
clearly demonstrates principal difficulties and problems in modal logic. 
Another important family of propositional logics considered in this book is 
the class of superintuitionistic (or intermediate) logics which are extensions of 
Heyting’s intuitionistic logic Int. From the technical and even philosophical point 
of view superintuitionistic logics are closely related to modal ones, and we use 
this opportunity to present a theory of such logics, at least in the background. 
The purpose of the book is to give a systematic treatment of the most 
important methods and results concerning these two kinds of logics. 
There exist three general ways of manipulating logics: syntactical, semantic 
and algebraic. The syntactical way, which uses various kinds of proof systems, 
like Gentzen-style calculi, natural deduction, semantic tableaux, etc., is hardly 
suitable for our aims. Although such systems have been constructed for a few 
particular modal and superintuitionistic logics, they are too special to be extended 
to big classes. The most widely used semantic way, exploiting “geometrical” 
features of Kripke frames, comes across the effect of Kripke incompleteness. We 
will go along this way as far as possible and then combine it with the universal 
algebraic way (which lacks geometrical insight) by adding to Kripke frames the 
algebraic component and considering general frames. Since the end of the 1970s, 
when duality theory started by Jonsson and Tarski (1951) was finally developed, 
this approach to modal (and other non-classical) logics has become 
dominating, having reconciled thereby “Kripkeans” and “algebraists” and laid a solid 

PREFACE 
IX 
mathematical base under the edifice of modal logic. 
The existing textbooks on modal logic reflect the state of the discipline as it 
was in the mid-1970s. From the technical point of view, they practically do not 
go further than applying the methods of canonical models and filtration to a few 
particular systems. The modern algebraic semantics (varieties of modal algebras 
and matrices), duality theory, general completeness results, investigations into 
metalogical properties of logics, algorithmic and complexity problems remain still 
scattered over numerous journals and proceedings of conferences. (Partially this 
situation is mitigated by books in boundary fields, for instance, correspondence 
theory, logic of time, provability logic, and the handbook series.) 
We believe this book will make understandable these important methods, 
tools and results of modal logic to students specialized in mathematics or 
computer science as well as in philosophy or linguistics. It should be useful for both 
novices without any previous knowledge of modal logic and specialists in the 
subject. We start with the very basic definitions and gradually advance to the 
front line of the current researches. Each chapter ends with a brief commentary 
and exercises, often supplemented with open problems. 
Modal logic is too extensive a field to be covered comprehensively only by one 
book. Besides, it can be looked at from different points of view. For instance, from 
the algebraic standpoint modal logics can be considered as equational theories 
of Boolean algebras with operators. Also, one can look at modal formulas as a 
language for describing classes of relational structures and compare it with other 
languages, say, the classical first order language. In this book our main object 
of studies are modal logics per se\ algebras and relational structures provide 
us with the relevant technical tools. Facing the problem of selecting material, 
we gave priority to ideas and methods rather than facts concerning individual 
systems. A number of interesting results are presented as exercises. On the other 
hand, sometimes it was very difficult to resist the temptation to include in the 
text quite new theorems, especially if we felt that otherwise the picture would 
be incomplete. We understand the danger of mixing genres and yet hope that 
we have managed to find a reasonable compromise between a textbook and a 
monograph. 
Now a few words about the content of the book. Part I introduces in full 
detail the syntax as well as the semantics of basic superintuitionistic and modal 
systems and studies their properties. In fact it illustrates in miniature what kinds 
of problems are to be considered later for big classes of logics. Technically one of 
the central points here is the construction of Kripke countermodels for a given 
formula, which is the first step in understanding the “geometry” of arbitrary 
(refutation) frames for the formula, and also the truth-preserving operations on 
frames. 
In Part II we first consider the method of canonical models for proving Kripke 
completeness and various forms of filtration for establishing the finite model 
property, which is called in this book the finite approximability. And then we 
present a series of “negative” results giving examples of logics lacking the finite 
approximability, canonicity, compactness, elementarity and Kripke completeness. 

X 
PREFACE 
Part III introduces adequate semantics for modal and superintuitionistic 
logics. We translate the language of logic into the language of algebra and arrive 
at varieties of modal and pseudo-Boolean algebras. Using the Stone-Jonsson- 
Tarski representation, we convert these algebras into general frames and study 
the relationship between the'algebraic and generalized Kripke semantics. Then 
we develop a frame-theoretic language in terms of which one can characterize 
the constitution of transitive refutation frames for a given modal or intuitionistic 
formula. 
Part IV studies various properties of modal and superintuitionistic logics. 
Here we deal with different forms of completeness (raising problems like “what 
is the structure of frames for a given logic?”, “what is the simplest class of 
frames characterizing it?”), and touch upon correspondence theory. We consider 
also lattice-theoretic and metalogical properties (e.g. Post completeness, 
interpolation, the disjunction property). 
Finally, Part V is devoted to algorithmic and complexity problems. Our 
concern here is not only the traditional problem of the decidability of logics. We 
are also interested in the decidability of logics* properties and the decidability 
of the admissibility and derivability problems for inference rules. In complexity 
theory we focus our attention mainly on estimating the size of minimal refutation 
frames for finitely approximable logics. 
Acknowledgments. We are indebted to Dov Gabbay for initiating the project 
of writing this book. We are also grateful to Sergei Artemov, Wim Blok, Johan 
van Benthem, Silvio Ghilardi, Carsten Grefe, Tsutomu Hosoi, Yurij Janov, Dick 
de Jongh, Max Kanovich, Marcus Kracht, Larisa Maksimova, Hiroakira Ono, 
Wolfgang Rautenberg, Mefodij Ratsa, Vladimir Rybakov, Valentin Shehtman, 
Tatsuya Shimura, Dmitrij Skvortsov, Alexander Tsytkin, Frank Wolter, Vladimir 
Zakharov for stimulating discussions. Thanks are due to Lilia Chagrova, who used 
the first version of the book for her course in modal logic at Tver University, 
and to Ivan Zakharyaschev for drawing numerous diagrams of frames in 
(in fact, that was his first experience in geometry). 
In different periods the work on the book was supported by the Russian 
Fundamental Research Foundation, Soros Foundation and Alexander von Humboldt 
Foundation. 
Tver State University, Russia 
Moscow State University, Russia 
Freie Universitat Berlin, Germany 
A. C. 
M. Z. 

CONTENTS 
I 	Introduction 
1 Classical logic 3 
1.1 Syntax and semantics 3 
1.2 Semantic tableaux 6 
1.3 Classical calculus 9 
1.4 Basic properties of Cl 15 
1.5 Exercises 19 
1.6 Notes 21 
2 Intuitionistic logic 23 
2.1 Motivation 23 
2.2 Kripke frames and models 25 
2.3 Truth-preserving operations 28 
2.4 Hintikka systems 35 
2.5 Intuitionistic frames and formulas 40 
2.6 Intuitionistic calculus 45 
2.7 Embeddings of Cl into Int 46 
2.8 Basic properties of Int 49 
2.9 Realizability logic and Medvedev’s logic 52 
2.10 Exercises 54 
2.11 Notes 56 
3 Modal logics 61 
3.1 Possible world semantics 61 
3.2 Modal frames and models 64 
3.3 Truth-preserving operations 69 
3.4 Hintikka systems 73 
3.5 Modal frames and formulas 77 
3.6 Calculus K 83 
3.7 Basic properties of K 87 
3.8 A few more modal logics 91 
3.9 Embeddings of Int into S4, Grz and GL 96 
3.10 Other types of modal logics 99 
3.11 Exercises 101 
3.12 Notes 105 

xii CONTENTS 
4 From logics to classes of logics 109 
4.1 Superintuitionistic logics 109 
4.2 Modal logics 113 
4.3 “The roads we take” 115 
4.4 Exercises and open problems 123 
4.5 Notes 125 
II Kripke SEMANTICS 
5 Canonical models and filtration 131 
5.1 The Henkin construction 131 
5.2 Completeness theorems 135 
5.3 The filtration method 139 
5.4 Diego’s theorem 146 
5.5 Selective filtration 149 
5.6 Kripke semantics for quasi-normal logics 154 
5.7 Exercises 157 
5.8 Notes 159 
6 Incompleteness 161 
6.1 Logics that are not finitely approximable 161 
6.2 Logics that are not canonical and elementary 165 
6.3 Logics that are not compact and complete 168 
6.4 A calculus that is not Kripke complete 170 
6.5 More Kripke incomplete calculi 174 
6.6 Complete logics without countable characteristic frames 176 
6.7 Exercises and open problems 183 
6.8 Notes 185 
III 	Adequate semantics 
7 Algebraic semantics 193 
7.1 Algebraic preliminaries 193 
7.2 The Tarski-Lindenbaum construction 195 
7.3 Pseudo-Boolean algebras 197 
7.4 Filters in pseudo-Boolean algebras 206 
7.5 Modal algebras and matrices 214 
7.6 Varieties of algebras and matrices 216 
7.7 Operations on algebras and matrices 219 
7.8 Internal characterization of varieties 227 
7.9 Exercises 229 
7.10 Notes 232 

CONTENTS 
xiii 
8 Relational semantics 235 
8.1 General frames 235 
8.2 The Stone and Jonsson-Tarski theorems 241 
8.3 Prom modal to intuitionistic frames and back 245 
8.4 Descriptive frames 250 
8.5 Truth-preserving operations on general frames 258 
8.6 Points of finite depth in refined finitely generated frames 267 
8.7 Universal frames of finite rank 272 
8.8 Exercises and open problems 279 
8.9 Notes 282 
9 Canonical formulas 286 
9.1 Subreduction 286 
9.2 Cofinal subreduction and closed domain condition 294 
9.3 Characterizing transitive refutation frames 302 
9.4 Canonical formulas for K4 and Int 310 
9.5 Quasi-normal canonical formulas 319 
9.6 Modal companions of superintuitionistic logics 322 
9.7 Exercises and open problems 328 
9.8 Notes 332 
IV 	Properties of logics 
10 Kripke completeness 337 
10.1 The method of canonical models revised 337 
10.2 D-persistence and elementarily 341 
10.3 Sahlqvist’s theorem 347 
10.4 Logics of finite width 354 
10.5 The degree of Kripke incompleteness of logics NExtK 360 
10.6 Exercises and open problems 369 
10.7 Notes 371 
11 Finite approximability 374 
11.1 Uniform logics 374 
11.2 Si-logics with essentially negative axioms and modal logics 
with DO-axioms 378 
11.3 Subframe and cofinal subframe logics 380 
11.4 Quasi-normal subframe and cofinal subframe logics 391 
11.5 The method of inserting points 395 
11.6 The method of removing points 404 
11.7 Exercises and open problems 411 
11.8 Notes 415 
12 Tabularity 417 
12.1 Finite axiomatizability of tabular logics 417 

XIV 
CONTENTS 
12.2 Immediate predecessors of tabular logics 418 
12.3 Pretabular logics 421 
12.4 Some remarks on local tabularity 426 
12.5 Exercises and open problems 428 
12.6 Notes 430 
13 Post completeness 432 
13.1 m-reducibility 432 
13.2 O-reducibility, Post completeness and general Post 
completeness 436 
13.3 Exercises and open problems 443 
13.4 Notes 444 
14 Interpolation 446 
14.1 Interpolation theorems for certain modal systems 446 
14.2 Semantic criteria of the interpolation property 451 
14.3 Interpolation in logics above LC and S4.3 455 
14.4 Interpolation in Extint and NExtS4 460 
14.5 Interpolation in extensions of GL 463 
14.6 Exercises and open problems 468 
14.7 Notes 469 
15 The disjunction property and Hallden 
completeness 471 
15.1 Semantic equivalents of the disjunction property 471 
15.2 The disjunction property and the canonical formulas 474 
15.3 Maximal si-logics with the disjunction property 477 
15.4 Hallden completeness 482 
15.5 Exercises and open problems 485 
15.6 Notes 488 
V 	Algorithmic problems 
16 The decidability of logics 491 
16.1 Algorithmic preliminaries 491 
16.2 Proving decidability 495 
16.3 Logics containing K4.3 499 
16.4 Undecidable calculi and formulas above K4 504 
16.5 Undecidable calculus and formula in Extint 509 
16.6 The undecidability of the semantical consequence problem 
on finite frames 513 
16.7 Admissible and derivable rules 519 
16.8 Exercises and open problems 530 
16.9 Notes 531 

CONTENTS 
XV 
17 
The decidability of logics’ properties 
535 
17.1 
A trivial solution 
535 
17.2 
Decidable properties of calculi 
536 
17.3 
Undecidable properties of modal calculi 
538 
17.4 
Undecidable properties of si-calculi 
542 
17.5 
Exercises and open problems 
543 
17.6 
Notes 
545 
18 
Complexity problems 
547 
18.1 
Complexity function. Kuznetsov’s construction 
547 
18.2 
Logics that are not polynomially approximable 
549 
18.3 
Polynomially approximable logics 
551 
18.4 
Extremely complex logics of finite width and depth 
553 
18.5 
Algorithmic problems and complexity classes 
557 
18.6 
Exercises and open problems 
562 
18.7 
Notes 
564 
Bibliography 
567 
Index 
597 

Part I 
