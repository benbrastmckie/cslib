<!-- Source: Hughes & Cresswell (1996). A New Introduction to Modal Logic. Routledge. Front matter including Preface and Table of Contents. -->

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
