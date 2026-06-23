# Basic Proof Theory — Front Matter (lines 1-315)
This Page Intentionally No Longer Blank
Basic Proof Theory
      Second Edition




     A.S. Troelstra
   University of Amsterdam


   H. Schwichtenberg
    University of Munich




         CAMB RID GE
     7.1r UNIVERSITY PRESS
PUBLISHED BY THE PRESS SYNDICATE OF THE UNIVERSITY OF CANIBRIDGE
     The Pitt Building, Trumpington Street, Cambridge, United Kingdom
                      CAMBRIDGE UNIVERSITY PRESS
 The Edinburgh Building, Cambridge CB2 2RU, UK http://www.cup.cam.ac.uk
  40 West 20th Street, New York, NY 10011-4211, USA http://www.cup.org
            10 Stamford Road, Oakleigh, Melbourne 3166, Australia
                   Ruiz de Alarcón 13, 28014 Madrid, Spain

                  © Cambridge University Press 1996, 2000

           This book is in copyright. Subject to statutory exception
        and
                                          may take place without
            the written permission of Cambridge University Press.

                              First published 1996
                              Second edition 2000

      Printed in the United Kingdom at the University Press, Cambridge

     Typeset by the author in Computer Modern 10/13pt, in D.TEX2E [EPC]

      A catalogue record of this book is available from the British Library

              Library of Congress Cataloguing in Publication data

                        ISBN 0 521 77911 1 paperback
Contents

Preface                                          ix

1   Introduction                                  1
    1.1   Preliminaries                           2
    1.2   Simple type theories                  10
    1.3   Three types of formalism              22

2 N-systems and H-systems                       35
    2.1 Natural deduction systems               35
    2.2 Ni as a term calculus                   45
    2.3 The relation between C, I and M         48
    2.4 Hilbert systems                         51
    2.5 Notes                                   55

3 Gentzen systems                               60
    3.1   The Gl- and G2-systems                61
    3.2   The Cut rule                          66
    3.3   Equivalence of G- and N-systems       68
    3.4   Systems with local rules              75
    3.5   Absorbing the structural rules        77
    3.6   The one-sided systems for C           85
    3.7   Notes                                 87

4 Cut elimination with applications             92
    4.1 Cut elimination                         92
    4.2 Applications of cutfree systems         105
    4.3 A more efficient calculus for Ip        112
    4.4 Interpolation and definable functions   116
    4.5 Extensions of Gl-systems                126
    4.6 Extensions of G3-systems                130
    4.7 Logic with equality                     134
vi                                                  Contents

     4.8   The theory of apartness                       136
     4.9   Notes                                         139

5 Bounds and permutations                                147
     5.1 Numerical bounds on cut elimination             148
     5.2 Size and cut elimination                        157
     5.3 Permutation of rules for classical logic        164
     5.4 Permutability of rules for Gli                  171
     5.5 Notes                                           176

6 Normalization for natural deduction                   178
     6.1 Conversions and normalization                   178
     6.2 The structure of normal derivations             184
     6.3 Normality in G-systems and N-systems            189
     6.4 Extensions with simple rules                    197
     6.5 E-logic and ordinary logic                      199
     6.6 Conservativity of predicative classes           203
     6.7 Conservativity for Horn clauses                 205
     6.8   Strong normalization for -1\Ini and A,        210
     6.9  Hyperexponential bounds                        215
     6.10 A digression: a stronger conversion            217
     6.11 Orevkov's result                               219
     6.12 Notes                                          223

7 Resolution                                            230
     7.1   Introduction to resolution                    230
     7.2   Unification                                   232
     7.3   Linear resolution                             236
     7.4   From Gentzen system to resolution             243
     7.5   Resolution for Ip                             246
     7.6   Notes                                         255

8    Categorical logic                                  258
     8.1  Deduction graphs                               259
     8.2 Lambda terms and combinators                    264
     8.3 Decidability of equality                        271
     8.4 A coherence theorem for CCC's                   274
     8.5 Notes                                           281

9 Modal and linear logic                                283
     9.1   The modal logic S4                            284
Contents                                          vii

   9.2  Embedding intuitionistic logic into S4   288
   9.3  Linear logic                             292
   9.4 A system with privileged formulas         300
   9.5 Proofnets                                 303
   9.6 Notes                                     313

10 Proof theory of arithmetic                    317
   10.1 Ordinals below eo                        318
   10.2 Provability of initial cases of TI       321
   10.3 Normalization with the omega rule        325
   10.4 Unprovable initial cases of TI           330
   10.5 TI for non-standard orderings            337
   10.6 Notes                                    342

11 Second-order logic                            345
   11.1 Intuitionistic second-order logic        345
   11.2 Ip2 and A2                               349
   11.3 Strong normalization for Ni2             351
   11.4 Encoding of A2 Q into A2                 357
   11.5 Provably recursive functions of HA2      358
   11.6 Notes                                    364

Solutions to selected exercises                  367

Bibliography                                     379

Symbols and notations                            404

Index                                            408
Preface

Preface to the first edition
The discovery of the set-theoretic paradoxes around the turn of the century,
and the resulting uncertainties and doubts concerning the use of high-level
abstractions among mathematicians, led D. Hilbert to the formulation of his
programme: to prove the consistency of axiomatizations of the essential parts
of mathematics by methods which might be considered as evident and reliable
because of their elementary combinatorial ("finitistic" ) character.
   Although, by Gödel's incompleteness results, Hilbert's programme could
not be carried out as originally envisaged, for a long time variations of
Hilbert's programme have been the driving force behind the development of
proof theory. Since the programme called for a complete formalization of the
relevant parts of mathematics, including the logical steps in mathematical ar-
guments, interest in proofs as combinatorial structures in their own right was
awakened. This is the subject of structural proof theory; its true beginnings
may be dated from the publication of the landmark-paper Gentzen [1935].
   Nowadays there are more reasons, besides Hilbert's programme, for study-
ing structural proof theory. For example, automated theorem proving implies
an interest in proofs as combinatorial structures; and in logic programming,
formal deductions are used in computing.
   There are several monographs on proof theory (Schiitte [1960,1977], Takeuti
[1987], Pohlers [1989]) inspired by Hilbert's programme and the questions
this engendered, such as "measuring" the strength of subsystems of analy-
sis in terms of provable instances of transfinite induction for definable well-
orderings (more precisely, ordinal notations). Pohlers [1989] is particularly
recommended as an introduction to this branch of proof theory.
   Girard [1987b] presents a wider panorama of proof theory, and is not easy
reading for the beginner, though recommended for the more experienced.
  The present text attempts to fill a lacuna in the literature, a gap which
exists between introductory books such as Heindorf [1994], and textbooks
on mathematical logic (such as the classic Kleene [1952a], or the recent van
Dalen [1994]) on the one hand, and the more advanced monographs mentioned
above on the other hand.
  Our text concentrates on the structural proof theory of first-order logic and
                                      ix
                                                                          Preface

its applications, and compares different styles of formalization at some length.
A glimpse of the proof theory of first-order arithmetic and second-order logic
is also provided, illustrating techniques in relatively simple situations which
are applied elsewhere to far more complex systems.
 As preliminary knowledge on the part of the reader we assume some fa-
miliarity with first-order logic as may be obtained from, for example, van
Dalen [1994]. A slight knowledge of elementary recursion theory is also help-
ful, although not necessary except for a few passages. Locally, other prelimi-
nary knowledge will be assumed, but this will be noted explicitly.
  Several short courses may be based on a suitable selection of the material.
For example, chapters 1, 2, 6 and 10 develop the theory of natural deduc-
tion and lead to a proof of the "classical" result of Gentzen on the relation
between the ordinal 60 and first-order arithmetic. A course based on the
first five chapters concentrates on Gentzen systems and cut elimination with
(elementary) applications.
   There are many interconnections between the present text and Hindley
 [1997]; the latter concentrates on type-assignment systems (systems of rules
for assigning types to untyped lambda terms) which are not treated here. In
our text we only consider theories with "rigid typing", where each term and
all of its subterms carry along a fixed type. Hindley's book may be regarded
as a companion volume providing a treatment of deductions as they appear
in type-assignment systems.
   We have been warned by colleagues from computer science that references
to sources more than five years old will make a text look outdated. For readers
inclined to agree with this we recommend contemplation of the following
platitudes: (1) a more recent treatment of a topic is not automatically an
improvement over earlier treatments; (2) if a subject is worthwhile, it will
in due time acquire a history going back more than five years; (3) results of
lasting interest do exist; (4) limiting the horizon to five years entails a serious
lack of historical perspective.
   Numbered exercises are scattered throughout the text. These are immedi-
ately recognizable as such, since they have been set in smaller type and have
been marked with the symbol 4.
   Many of these exercises are of a routine character ("complete the proof of
this lemma"). We believe that (a) such exercises are very helpful in famil-
iarizing the student with the material, and (b) listing these routine exercises
explicitly makes it easy for a course leader to assign definite tasks to the
students.
   At the end of each chapter, except the first, there is a section called "Notes".
There we have collected historical credits and suggestions for further reading;
also we mention other work related to the topic of the chapter. These notes
do not pretend to give a history of the subject, but may be of help in gaining
some historical perspective, and point the way to the sources. There is no
Preface                                                                     xi

attempt at completeness; with the subject rapidly expanding this has become
well-nigh impossible.
   The references in the index to names of persons concern in the majority of
cases a citation of a publication. In case of publications with more than one
author, only the first author's name is indexed. Occurrences of author names
in the bibliography have not been indexed. There is a separate list, where
symbols and notations of more than local significance have been indexed.
   The text started as a set of course notes for part of a course "Introduction
to Constructivism and Proof Theory" for graduate students at the University
of Amsterdam. When the first author decided to expand these notes into a
book, he felt that at least some of the classical results on the proof theory
of first-order arithmetic ought to be included; hence the second author was
asked to become coauthor, and more particularly, to provide a chapter on
the proof theory of first-order arithmetic. The second author's contribution
did not restrict itself to this; many of his suggestions for improvement and
inclusion of further results have been adopted, and a lot of material from his
course notes and papers has found its way into the text.
   We are indebted for comments and information to K. R. Apt, J. F. A. K. van
Benthem, H. C. Doets, J. R. Hindley, G. E. Mints, V. Sanchez, S. V. Solovjov,
A. Weiermann; the text was prepared with the help of some useful Latex
macros for the typesetting of prooftrees by S. Buss and for the typesetting of
ordinary trees by D. Roorda. M. Behrend of the Cambridge University Press
very carefully annotated the near-final version of the text, expunging many
blemishes and improving typographical consistency.

A msterdam/Miinchen                                            A. S. Troelstra
Spring 1996                                                H. Schwichtenberg

Preface to the second edition
In preparing this revised edition we used the opportunity to correct many
errata in the first edition. Moreover certain sections were rewritten and some
new material inserted, especially in chapters 3-6. The principal changes are
the following.
   Chapter 1: section 1.3 has been largely rewritten. Chapter 2: the material
in 2.1.10 is new. Chapter 3: more prominence has been given to a Kleene-style
variant of the G3-systems (3.5.11), and multi-succedent versions of G3[mi]
are defined in the body of the text (3.5.10). A general definition of systems
with local rules (3.4) is also new. Chapter 4: the proof of cut elimination
for G3-systems (4.1.5) has been completely rewritten, and a sketch of cut
elimination for the systems m-G3[mi] has been added (4.1.10). There are new
sections on cut elimination for extensions of G3-systems, with applications
to predicate logic with equality and the intuitionistic theory of apartness.
Chapter 5: a result on the growth of size of proofs in propositional logic
xii                                                                     Preface

under cut elimination (5.2) has been included. Chapter 6: extensions of N-
systems with extra rules, with an application to E-logic, are new; the section
on E-logic replaces an inadequate treatment of the same results in chapter
4 of the first edition. Chapter 11: a new proof of strong normalization for
A2. New are also the "Solutions to selected exercises" ; these are intended
as a help to those readers who study the text on their own. Exercises for
which a (partial) solution is provided are marked with *. The updating of
the bibliography primarily concerns the parts of the text which have been
revised.
  In a review of the first edition it has been noted that complexity-theoretic
aspects are largely absent. We felt that this area is so vast that it would
require a separate monograph of its own, to be written by an expert in the
area. Another complaint was that our account was lacking in motivation and
philosophical background. This has not been remedied in the present edition,
although a few words of extra explanation have been added here and there.
A typically philosophical problem we did not deal with is the question: when
are two proofs to be considered equal? We doubt, however, whether this
question will ever have a simple answer; it may well be that there are many
answers, depending on aims and points of view.
   One terminological change deserves to be noted: we changed "contraction"
(in the sense of a step in transforming terms of type theory and proofs in natu-
ral deduction), into "conversion". Similarly, "contracts to" and "contractum"
have been replaced by "converts to" and "conversum" repectively. On the
other hand "contraction" as the name of a structural rule in Gentzen systems
is maintained. See under the remarks at the end of 1.2.5 for a motivation.
   We are again indebted to many people for comments and corrections, in par-
ticular H. van Ditmarsch, L. Gordeev, J. R. Hindley, R. Matthes, G. E. Mints,
and the students in our classes. Special thanks are due to Sara Negri, who
unselfishly offereI to read carefully a large part of the text; in this she has
been assisted by an von Plato. Their comments led to many improvements.
For the remaining defects of the text the authors bear sole responsibility.

Amsterdam/Miinchen                                              A. S. Troelstra
March 2000                                                  H. Schwichtenberg
