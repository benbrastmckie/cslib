arXiv:2310.01916v1  [cs.LO]  3 Oct 2023
Joint proceedings of the Third International Workshop
on Logics for New-Generation Artiﬁcial Intelligence and
the International Workshop on Logic, AI and Law,
B. Bentzen, B. Liao, D. Liga, R. Markovich,
B. Wei, M. Xiong, T. Xu (eds.), pp.36–48, 2023
https://www.collegepublications.co.uk/LNGAI/?00003
Veriﬁed completeness in Henkin-style
for intuitionistic propositional logic
Huayu Guo, Dongheng Chen, and Bruno Bentzen
School of Philosophy, Zhejiang University, Hangzhou, China
{guohuayu,chen dongheng,bbentzen}@zju.edu.cn
Abstract
This paper presents a formalization of the classical proof of completeness in Henkin-style
developed by Troelstra and van Dalen for intuitionistic logic with respect to Kripke models.
The completeness proof incorporates their insights in a fresh and elegant manner that is
better suited for mechanization. We discuss details of our implementation in the Lean the-
orem prover with emphasis on the prime extension lemma and construction of the canonical
model. Our implementation is restricted to a system of intuitionistic propositional logic
with implication, conjunction, disjunction, and falsity given in terms of a Hilbert-style ax-
iomatization. As far as we know, our implementation is the ﬁrst veriﬁed Henkin-style proof
of completeness for intuitionistic logic following Troelstra and van Dalen’s method in the
literature. The full source code can be found online at https://github.com/bbentzen/ipl.
1
Introduction
Troelstra and van Dalen [17] propose a completeness proof in Henkin-style for full intuitionistic
predicate logic with respect to Kripke models. Despite being a fairly standard result in the
literature, this completeness proof has yet to be formally veriﬁed in a proof assistant. In this
paper, we describe a formalization for intuitionistic propositional logic using the Lean theorem
prover [13].
Our main goal is to document some challenges encountered along the way and the design
choices made to overcome them to obtain a formalized proof that is elegant, intuitive, and
better suited for mechanization using the speciﬁc techniques available in the Lean program-
ming language, in particular, the encodable.decode and insert code methods developed by
Bentzen [1].
To the best of our knowledge, our implementation is the ﬁrst veriﬁed Henkin-style proof of
strong completeness for intuitionistic logic following Troelstra and van Dalen’s method in the
literature. As far as its propositional fragment is concerned, the main ingredient of Troelstra
and van Dalen’s Henkin-proof is a model construction based on a consistent extension of sets of
formulas, which is achieved by going through all disjunctions of the language [17, lem 6.3]. To
carry out this extension, they assume an enumeration of disjunctions with inﬁnite repetitions,

---

Veriﬁed completeness in Henkin-style for intuitionistic propositional logic
H. Guo, D. Chen, and B. Bentzen
also remarking that an alternative approach in which at each stage we treat the ﬁrst disjunction
not yet treated. This variant appears in Van Dalen [5, lem 5.3.8]. Our implementation is based
on a third variant of the consistent extension method, which we developed to better suit our
needs of formalization.
Each propositional formula is only listed once in the enumeration,
but we carry out the extension for each of them inﬁnitely many times.
The formalization
consists of roughly 800 lines of code and encompasses the syntax and semantics of intuitionistic
propositional logic, along with the soundness and strong completeness theorems. We adopt a
Hilbert-style proof system due to its simplicity. The full source code can be found online at
https://github.com/bbentzen/ipl.
1.1
Related work
The formal veriﬁcation of completeness proofs for intuitionistic logic can be traced back to
Coquand’s [3] use of ALF to mechanize a constructive proof of soundness and completeness
with respect to Kripke models for the simply typed lambda-calculus with explicit substitu-
tions. Heberlin and Lee [9] give a constructive completeness proof of Kripke semantics with
constant domain for intuitionistic logic with implication and universal quantiﬁcation in Coq.
Recently, Hagemeier and Kirst [8] formalize a constructive proof of completeness for intuition-
istic epistemic logic based on a natural deduction system. They also provide a classical Henkin
proof using methods similar to those in Bentzen [1], but they do not present a formalization
of the approach of Troelstra and van Dalen [17] as is done in this paper. Bentzen [1] formal-
izes the Henkin-style completeness method for modal logic S5 using Lean and From formalizes
in Isabelle/HOL a Henkin-style completeness proof for both classical propositional logic [6]
and classical ﬁrst-order logic [7]. Maggesi and Brogi [12] give a formal completeness proof for
provability logic in HOL Light. The formalization presented here is inspired by the work of
Bentzen [1], but makes a few improvements regarding design choices, in particular, the use of
Prop in the deﬁnition of the semantics and the indexing of models to arbitrary types.
1.2
Lean
Lean [13] is an interactive theorem prover based on the version of dependent type theory
known as the calculus of constructions with inductive types [15, 4]. Users can construct proof
terms directly as in Agda [14], using tactics as in Coq [16] or both proof terms and tactics
simultaneously.
Lean’s built-in logic is constructive, but it supports classical reasoning as
well.
In fact, our Henkin-style proof is classical since it relies on a nonconstructive use of
contraposition. Therefore, we do not worry about any complexity and computational aspects
related to our proof.
Our implementation makes use of some results from Lean’s standard
library and the user-maintained mathematical library mathlib [2].
Throughout the remainder of this paper, Lean code will be used to showcase some design
decisions in our formalization. The syntax and semantics of intuitionistic propositional logic
that is the starting point of our formalization is described in Section 2.
We also describe
our formalization of a countermodel for the law of excluded middle and sketch a proof of
soundness. Then, an informal overview of the Henkin-style proof method as well as a description
of our implementation is provided in Section 3. Finally, some concluding remarks are given
in Section 4.
2

---

Veriﬁed completeness in Henkin-style for intuitionistic propositional logic
H. Guo, D. Chen, and B. Bentzen
2
Intuitionistic Logic
2.1
The language
The intuitionistic propositional language considered here contains implication, conjunction,
disjunction, and falsity as the only primitive logical connectives. The language is deﬁned using
inductive types with one constructor for propositional letters, falsum, implication, conjunction,
and disjunction, respectively:
inductive
form : Type
|
atom : N →form
|
bot
: form
|
impl : form
→form →form
|
and
: form
→form →form
|
or
: form
→form →form
This code can be found in language.lean ﬁle.
Since our language contains countably many propositional letters p0, p1, ... we use the type
N of natural numbers to deﬁne the constructor atom of propositional letters. The only way to
construct a term of type form is using this atomic constructor(atom) and the constructors for
falsum (bot), implication (impl), conjunction (and), disjunction (or).
The elimination rule is an operation that allows us to deﬁne functions by recursion from it
to any other types, including also the type of propositions Prop, in which case, this elimination
rule is an instance of the principle of induction on the structure of the formula.
Constructors are displayed in Polish notation by default, but we deﬁne some custom inﬁx
notation with the usual Unicode characters for better readability:
prefix
‘#‘
:=
form.atom
notation
‘⊥‘
:=
form.bot
infix
‘⊃‘
:=
form.impl
notation
p ‘&‘ q
:=
form.and p q
notation
p ‘∨‘ q
:=
form.or p q
notation
‘~‘:4
p :=
form.impl p (form.bot )
Contexts are just sets of formulas. In Lean sets are deﬁned as functions of type A →Prop. As
usual in logic textbooks, we display the formulas in a context in list notation separated by a
comma instead of using unions of singletons. We introduce the following notation to make this
possible:
notation Γ ‘ ` ‘ p := set .insert
p Γ
The formalization of the language can be found in the language.lean ﬁle.
2.2
The proof system
We deﬁne a Hilbert-style system for intuitionistic propositional logic that is best described as a
reﬁnement of Heyting’s original axiomatization [10, §2]. The proof system is implemented with
a type of proofs, which is inductively deﬁned as follows:
inductive prf : set
form →form →Prop
|
ax {Γ} {p} (h :p ∈Γ) :prf Γ p
|
k {Γ} {p q} :prf Γ (p ⊃(q ⊃p))
|
s {Γ} {p q r} :prf Γ ((p ⊃(q ⊃r)) ⊃((p ⊃q) ⊃(p ⊃r)))
|
exf {Γ} {p} :prf Γ (⊥⊃p)
|
mp {Γ} {p q} (hpq : prf Γ (p ⊃q)) (hp :prf Γ p) :prf Γ q
|
p r
{Γ} {p q} :prf Γ ((p & q) ⊃p)
|
p r
{Γ} {p q} :prf Γ ((p & q) ⊃q)
3

---

Veriﬁed completeness in Henkin-style for intuitionistic propositional logic
H. Guo, D. Chen, and B. Bentzen
|
pair {Γ} {p q} :prf Γ (p ⊃(q ⊃(p & q)))
|
inr {Γ} {p q} :prf Γ (p ⊃(p ∨q))
|
inl {Γ} {p q} :prf Γ (q ⊃(p ∨q))
|
case {Γ} {p q r} :prf Γ ((p ⊃r) ⊃((q ⊃r) ⊃((p ∨q) ⊃r)))
Again, the elimination rule for this type generalizes deﬁnition by recursion and induction
on the structure of proofs. To follow the usual logical notation, we abbreviate prf Γ p with
Γ ⊢i p as follows:
notation Γ ‘ ⊢i ‘ p := prf Γ p
notation Γ ‘ ̸⊢i ‘ p := prf Γ p →false
To illustrate, we compare a mechanized formal Hilbert-style proof of the identity of impli-
cation p ⊃p in our implementation:
lemma
id {p : form } {Γ : set
form } :
|
Γ ⊢i p ⊃p :=
mp (mp (@s
Γ p (p ⊃p) p) k) k
with a non-mechanized formal proof written in Lemmon style:
1
p ⊃((p ⊃p) ⊃p) ⊃(p ⊃(p ⊃p)) ⊃(p ⊃p)
S
2
p ⊃((p ⊃p) ⊃p)
K
3
(p ⊃(p ⊃p)) ⊃(p ⊃p)
MP 1, 2
4
(p ⊃(p ⊃p))
K
5
p ⊃p
MP 3, 4
Notice that the proof structure in our term proof is actually clearer since it indicates how
the axiom schemes should be instantiated.
The formalization of the proof system can be found in the theory.lean ﬁle.
2.3
Semantics
2.3.1
Kripke models
We deﬁne the semantics for intuitionistic propositional logic in terms of Kripke semantics as
usual [17, 5]. A model M is a triple ⟨W, ≤, v⟩where W is a set of possible worlds of type A, ≤
is a reﬂexive, symmetric and monotonic binary relation on A, and v speciﬁes the truth value of
a formula at a world.
In Lean, Kripke models can be deﬁned as inductive types having just one constructor using
the structure command. We deﬁne it not as a triple but as a 6-tuple, composed of a domain W,
an accessibility relation R, a valuation function val, and proofs of reﬂexivity, transitivity, and
monotonicity for the accessibility relation R, denoted as refl, trans, and mono:
structure
model (A : Type) :=
|
(W : set A)
|
(R : A
→A →Prop)
|
(val : N →A →Prop)
|
(refl : ∀w ∈W, R w w)
|
(trans : ∀w ∈W, ∀v ∈W, ∀u ∈W, R w v →R v u →R w u)
|
(mono : ∀p, ∀
w
w
∈W, val
p
w
→R
w
w
→val p
w )
In our case, a possible world is a term of type A. This allows for more generality in the
construction of a model unlike in [1]. What is more, the type of propositions Prop is used to
encode our truth values true or false.
4

---

Veriﬁed completeness in Henkin-style for intuitionistic propositional logic
H. Guo, D. Chen, and B. Bentzen
2.3.2
Semantic consequence
To formalize the notion of truth at a type, we deﬁne a forcing relation w ⊩M p that takes as
arguments a model M, a formula p, and a type A and returns a term of type Prop. As usual,
falsity, conjunction, and disjunction are deﬁned truth-functionally and an implication p ⊃q is
true at a world w iﬀif R(w, v) then p is true implies q is true at v, for all v ∈W. We also
introduce the familiar notation for this forcing relation:
def
for ces_form
{A : Type} (M : model A) : form →A →Prop
|
(#p)
:=
λv, M.val p v
|
(bot )
:=
λv, false
|
(p ⊃q)
:=
λv, ∀w ∈M.W, v ∈M.W →M.R v w
→for ces_form
p w →for ces_form
q w
|
(p & q)
:=
λv, for ces_form
p v ∧for ces_form
q v
|
(p ∨q)
:=
λv, for ces_form
p v ∨for ces_form
q v
notation
w ‘⊩‘ ‘{‘ M ‘} ‘ p :=
for ces_form
M p w
To formalize the intuitionistic notion of semantic consequence Γ ⊨i p we ﬁrst extend this
forcing relation to contexts pointwise and then we stipulate that Γ ⊨i p iﬀfor all types A,
models M and possible worlds w ∈W, Γ being true at w in M implies p being true at w in
M:
def
for ces_ ctx {A : Type} (M : model A) (Γ :set
form) : A →Prop :=
λw, ∀p, p ∈Γ →for ces_form
M p w
notation
w ‘⊩‘ ‘{‘ M ‘} ‘ Γ := for ces_ ctx M Γ w
def
sem_csq (Γ :set
form) (p : form) :=
∀{A : Type} (M : model A) (w ∈M.W), (w ⊩{M} Γ) →(w ⊩{M} p)
notation Γ ‘⊨i‘ p := sem_csq Γ p
It is worth noting that we are overloading the forcing relation notation for formulas w ⊩
{M} p and contexts w ⊩{M} Γ. There is no ambiguity because Lean will delay the choice until
elaboration and determine how to disambiguate the notations depending on the relevant types.
The formalization of the Kripke semantics described above can be found in the semantics.lean
ﬁle.
2.3.3
The failure of the law of excluded middle
Before proceeding to prove completeness, it will be helpful to see how we can build models
in our implementation. To give a concrete example, let us show how to build the following
countermodel for the law of excluded middle [11, p.99] using the type of booleans true tt and
false ff:
ﬀ
p
tt
Since our possible worlds are always booleans, the domain, accessibility relation, and val-
uation function are formalized in Lean in a slightly diﬀerent way. The reﬂexivity, transitivity,
and monotonicity proofs are straightforward, so we shall omit them:
5

---

Veriﬁed completeness in Henkin-style for intuitionistic propositional logic
H. Guo, D. Chen, and B. Bentzen
def
W : set
bool :=
{ff , tt}
def
R : bool →bool →Prop := λ w v, w = v ∨w = ff
@[simp]
def
val : nat →bool →Prop := λ _ w, w = tt
Using this countermodel, we assume that the law of excluded middle holds, that is for any
formula p, either ∅|=i p or ∅|=i ¬p, and then derive a contradiction. This allows us to prove
that the law of excluded middle fails in general:
lemma
no_lem : ¬ ∀p, (∅⊨i p ∨~p)
The mechanization of the countermodel can be found in the nolem.lean ﬁle.
2.3.4
Soundness
The soundness theorem asserts that if a formula p can be derived from a set of assumptions Γ
using the inference rules of the logical system, then p is logically valid under any interpretation
that satisﬁes Γ.
theorem
soundness
{Γ : set
form} {p : form} :
(Γ ⊢i p) →(Γ |=i p)
The code for proof of soundness can be found in soundness.lean.
The proof proceeds by using induction to perform case analysis for each inference rule. For
each rule, the proof provides a way to derive the conclusion based on the rule and a way to
show that the conclusion is logically valid based on the interpretation and the premises.
3
The completeness theorem
Now that we have presented the implementation of the syntax and semantics of intuitionistic
propositional logic in the previous section, we are prepared to undertake a formal proof of
completeness. The strong completeness theorem, which states that every semantic consequence
is a syntactic consequence, can be stated in Lean using our custom notation as follows:
theorem
completeness
{Γ : set
form} {p : form} :
(Γ |=i p) →(Γ ⊢i p)
Our implementation follows the original Henkin-style completeness proof given by Troelstra
and van Dalen [17] with some small modiﬁcations. The main proof argument runs as follows.
1. Assume that Γ ⊨i p and Γ ⊬i p hold;
2. Build a model M such that w ⊩M p iﬀw ⊢i p for all worlds w ∈W, where we have sets
of formulas as possible worlds;
3. Show that there is a world w ∈W such that w ⊩M Γ but w ⊮M p;
4. Establish a contradiction from our assumption that Γ ⊨i p.
Our proof appeals to classical reasoning at the metalevel of Lean’s logic on two occasions [17,
p.87], namely, in our proof of Γ ⊢i p where we assume double negation elimination and in our
proof of w ⊩M p iﬀw ⊢i p.
The reader can refer to the completeness.lean ﬁle for the full details of our implementation
of the completeness proof.
6

---

Veriﬁed completeness in Henkin-style for intuitionistic propositional logic
H. Guo, D. Chen, and B. Bentzen
3.0.1
Consistent prime extensions
The ﬁrst step of Troelstra and van Dalen’s proof is the deﬁnition of what they call a “saturated
theory” [17, def.6.2]. We shall make use of the equivalent concept of prime theory instead [5,
def.5.3.7], in which the disjunction property is expressed in terms of the membership relation.
We say that a set of formulas Γ is a prime theory if Γ is closed under derivability and if p∨q ∈Γ
implies p ∈Γ or q ∈Γ. In completeness.lean ﬁle, we write:
def
is_ closed (Γ : set
form) :=
∀{p : form}, (Γ ⊢i p) →p ∈Γ
def
has_disj
(Γ : set
form) :=
∀{p q : form}, ((p ∨q) ∈Γ) →((p ∈Γ) ∨(q ∈Γ))
def
is_prime
(Γ : set
form) :=
is_ consist Γ ∧has_disj Γ
The second step of Troelstra and van Dalen’s completeness proof is the proof of a prime exten-
sion lemma [17, lem 6.3], which states that if Γ ⊬r then there is a prime theory Γ′ ⊇Γ such
that Γ′ ⊬r. Assuming that they have a list of disjunctions ⟨ϕi,1∨ϕi,2⟩i with inﬁnite repetitions,
they deﬁne
Γ′ =
[
i∈N
Γi,
where Γ0 = Γ and Γk+1 is deﬁned inductively as follows:
• Case 1: Γk ⊢ϕk,1 ∨ϕk,2. Put
– Γk+1 = Γk ∪{ϕk,2} if Γk, ϕk,1 ⊢r, and
– Γk+1 = Γk ∪{ϕk,1} otherwise
• Case 2: Γk ⊬ϕk,1 ∨ϕk,2. Put
– Γk+1 = Γk
Since we want to extend Γ to a prime theory Γ′, we want to ensure the disjunctive property
that if φ∨ψ ∈Γ′ then φ ∈Γ′ or ψ ∈Γ′. If there were no inﬁnite repetitions in the list, we could
never be sure that we have treated all disjunctions in Case 1, for, at step k+1, its disjuncts only
get added to the set when Γk proves the disjunction. It is possible that later the disjunction
becomes provable from Γk+m, but, we will never go back to it again.
Troelstra and van Dalen mention a simpler variant of the construction that uses an enu-
meration of disjunctions without requiring inﬁnite repetitions. At stage k + 1 we simply treat
the ﬁrst disjunction not yet treated. This proof is spelled out by van Dalen in [5, lem 5.3.8].
However, the proof method is less suitable for mechanization given that it is diﬃcult to tell a
proof assistant how exactly they should ﬁnd the ﬁrst disjunction not yet treated. We implement
a simpliﬁed version of this method where at each step k + 1 we always treat all disjunctions
in the language once more. The following Lean code encapsulates the idea of the construction
sketched above:
7

---

Veriﬁed completeness in Henkin-style for intuitionistic propositional logic
H. Guo, D. Chen, and B. Bentzen
def
insert_form
(Γ : set
form) (p q r : form) :
set
form :=
if (Γ ` p ⊢i r) then Γ ` q else Γ ` p
def
insert_ code (Γ : set
form) (r : form) (n : nat ) :
set
form :=
mat ch encodable .decode (form) n with
|
none
:=
Γ
|
some (p ∨q) := if Γ ⊢i p ∨q then insert_form
Γ p q r else Γ
|
some _ :=
Γ
end
def
insertn
(Γ : set
form) (r : form) : nat →set
form
|
:=
Γ
|
(n+1) := insert_ code (insertn
n) r n
def
primen (Γ : set
form) (r : form) : nat →set
form
|
:=
Γ
|
(n+1) := S i, insertn
(primen
n) r i
def
prime (Γ: set
form) (r : form) :
set
form :=
S n, primen Γ r n
Unlike in Troesltra and van Dalen [17] and van Dalen [5], the enumeration in our formal-
ization lists not just all disjunctions but all propositional formulas in the language. When a
formula is not a disjunction we simply ignore it just as in Case 2 above. We follow Bentzen [1] in
using encodable types to enumerate the language. In Lean, a type α is encodable if there is an
encoding function encode :α →nat and a (partial) inverse decode :nat →option α that decodes
the encoded term of α.
Now that we extended Γ to Γ′, which we denote as prime Γ r, we have to prove it is indeed
a prime extension of Γ. First, we show that Γ ⊆Γ′. But this is easy, since for every Γ′
n n in the
family of sets, Γ ⊆Γ′
n n. Therefore, Γ must also be included in the union of all Γ′
n n, which is
Γ′
n.
lemma
primen_subset_prime {Γ : set
form} {r : form} (n):
primen Γ r n ⊆prime Γ r
lemma
subset_prime_self {Γ : set
form} {r : form} :
Γ ⊆prime Γ r
The next step is to prove that the Γ′ also has the disjunction property and it is closed under
derivability. Let us focus on the former ﬁrst.
We need to show that p ∨q ∈Γ′ implies p ∈Γ′ or q ∈Γ′. If p ∨q ∈Γ′ then there is some
n ∈N such that p∨q ∈Γ′
n. But then since Γ′
n ⊢p∨q, then we know that p ∈Γ′
n+1 or q ∈Γ′
n+1
because the disjunction was treated at some point. Thus, p ∈Γ′ or q ∈Γ′.
def
prime_insertn_disj {Γ: set
form} {p q r : form} (h : (p ∨q)
∈
prime Γ r) :
∃n, p ∈(insertn
(primen Γ r n) r (encodable .encode (p ∨q)+1)) ∨q ∈(
insertn
(primen Γ r n) r (encodable .encode (p ∨q)+1))
lemma
insertn_to_prime {Γ : set
form} {r : form} {n m : nat } :
insertn
(primen Γ r n) r m ⊆prime Γ r
def
prime_has_disj {Γ : set
form} {p q r : form} :
((p ∨q) ∈prime Γ r) →p ∈prime Γ r ∨q ∈prime Γ r
Saying that Γ′ is closed under derivability means that if we can deduce a formula from Γ′,
it is an element of Γ′. We use a lemma that states that if we can prove r ∨p from Γ′, then
there exists an n such that p ∈Γn+1. We use the above lemma insertn to prime to deduce
that p ∈Γ′:
8

---

Veriﬁed completeness in Henkin-style for intuitionistic propositional logic
H. Guo, D. Chen, and B. Bentzen
lemma
prime_prf_disj_self {Γ : set
form} {p r : form} :
(prime Γ r ⊢i r ∨p) →∃n, p ∈(insertn
(primen Γ r n) r (encodable .enc
ode (r ∨p)+1))
def
prime_is_ closed {Γ : set
form} {p q r : form} :
(prime Γ r ⊢i p) →p ∈prime Γ r
At this moment, we need to prove that Γ′ still remains consistent. First, we by structural
induction on the derivation that if Γ′ ⊢r then there is some n such that Γn ⊢r. Then we
prove by induction on n that if Γn ⊢r then Γ ⊢r. The base case is trivial. In the inductive
case, we complete the proof by unfolding the deﬁnition of Γn and manipulating the inductive
hypothesis. Putting both lemmas together, we prove that Γ′ ⊢r implies Γ ⊢r:
def
primen_not_prfn {Γ : set
form} {r : form} {n} :
(primen Γ r n ⊢i r) →(Γ ⊢i r)
def
prime_not_prf {Γ : set
form} {r : form} :
(prime Γ r ⊢i r) →(Γ ⊢i r)
3.0.2
The canonical model construction
Given a set of formulas Γ and φ such that Γ ⊬φ, the next step is to build a canonical Kripke
model M such that with w ⊩M Γ and w ⊮M φ for some possible world. We build this model
by letting W be the set of all consistent prime theories; w ≤v iﬀw ⊆v for w, v ∈W; and
v(w, p) = 1 iﬀw ∈W and p ∈w, for a propositional letter p. The following Lean code reﬂects
the model construction:
def
domain : set (set
form) :=
{w
|
is_ consist
w ∧ctx.is_prime
w}
def
access : set
form →set
form →Prop := λ w v, w ⊆v
def
val : N →set
form →Prop := λ q w, w ∈domain ∧(#q) ∈w
The accessibility relation ≤is clearly reﬂexive and transitive since so is ⊆. Monotonicity is easy
to see since p ∈w and w ⊆v means that q ∈v. We prove these lemmas by straightforward
unfolding the deﬁnition of access.
Our model is integrated into Lean’s code as follows:
def
M : model (set
form):=
begin
fapply
model.mk,
apply
domain ,
apply access ,
apply val ,
apply access .refl ,
apply access .trans ,
apply access .mono
end
3.0.3
Truth and derivability
It turns out that a formula is true at a world in the canonical model if and only if it can be
proved from that world:
lemma
model_tt_iff_prf {p : form} :
∀(w ∈domain ), (w |= {M} p) ↔(w ⊢i p)
9

---

Veriﬁed completeness in Henkin-style for intuitionistic propositional logic
H. Guo, D. Chen, and B. Bentzen
We mechanize the proof employing the induction tactic, which allows us to use the elimination
rule of a type. This approach yields ﬁve goals, namely, to prove the case where a formula is a
propositional letter, falsity, implication, conjunction, or disjunction. The proof of implication
and disjunction deserve some mention.
The disjunction case is simpler, so we shall discuss it ﬁrst. Lean gives us a biconditional in
the following goal:
⊢∀(w :set
form),
w ∈domain →(w |= {M} (p ∨q)) ↔(w ⊢i p ∨q))
The proof in the forward direction starts with the introduction of assumptions and then
splits the proof into two cases. In the ﬁrst case, we assume that w |=M p ∨q and our goal is
w ⊢i p ∨q. Through the tactic cases, which expresses case reasoning, we can ﬁnish our goal
using some basic facts about disjunctions and the inductive hypotheses in both cases.
In the backward direction, we assume that w ⊢i p ∨q. Since w is a prime theory and thus
enjoys the disjunctive property, we can reason by cases depending on whether w ⊢i p or w ⊢i q.
The result follows the inductive hypothesis.
Now we proceed to the implication case. Using the intro tactic, we begin by assuming
the inductive hypothesis for p. If w is a world and it is a prime theory, then by unfolding the
true deﬁnition of a formula in the model’s world, we arrive at a biconditional goal that can be
expressed as follows.
⊢∀(w :set
form),
w ∈domain →(w |=i {M} (p ⊃q)) ↔(w ⊢i p ⊃q))
We split the biconditional proof into two smaller conditionals using the split tactic. In the
forward direction, we ﬁrst assume that w ⊩M p ⊃q. We reason by cases depending on whether
w ⊢i p ⊃q or not, therefore invoking the law of excluded middle. If that is the case, we are
done. If not, then we know that w, p ⊬q. We want to derive a contradiction. We extend the
context w, p to a prime theory (w, p)′ that still does not prove q. By our inductive hypothesis,
since (w, p)′ is in the domain, we know that (w, p)′ ⊩M q ↔(w, p)′ ⊢i q.
To derive a contradiction, we just have to show that (w, p)′ ⊩M q. Recall that our assump-
tion w ⊩M p ⊃q states that for all v ∈W such that w ≤v, if v ⊩M p then v ⊩M q. But,
clearly, w ≤(w, p)′. To complete the proof, we just have to show that (w, p)′ ⊩M p. By our
inductive hypothesis, it suﬃces to show that (w, p)′ ⊢i p. But this is clearly true, since the
original set w, p is contained in the prime extension (w, p)′ and w, p ⊢i p.
For the backward direction, what we have to prove is w ⊩M p ⊃q. This means for all
v ∈W such that w ≤v, if v ⊩M p then v ⊩M q. We assume that v ∈W such that w ≤v,
v ⊩M p then we have to show v ⊩M q. Using our inductive hypothesis, we just have to show
that v ⊢i q.
Since we know w ⊢i p ⊃q and w ⊆v, by weakening, we will have v ⊢i p ⊃q. We complete
the proof by noting that v ⊢i p by our inductive hypothesis and assumption that v ⊩M p. The
result follows from modus ponens.
We have ﬁnished the proof of implication.
3.0.4
The completeness proof
To ﬁnish our completeness proof we just have to put together all the above pieces into 27 lines
of code. We assume that Γ ⊬i p and Γ |=i p, we just need to arrive at a contradiction. We
extend Γ to a prime theory Γ′ such that Γ′ ⊬i p. Since we know Γ′ ⊩M q ⇐⇒Γ′ ⊢i q for every
formula q, we can conclude that Γ′ ⊮M p. Thus, we contradict our assumption that Γ |=i p,
given that Γ′ ⊩M Γ but Γ′ ⊮M p.
10

---

Veriﬁed completeness in Henkin-style for intuitionistic propositional logic
H. Guo, D. Chen, and B. Bentzen
4
Conclusion
We have used Lean to formally verify the Henkin-style completeness proof for intuitionistic logic
proposed by Troesltra and van Dalen [17] restricted to a propositional fragment with implica-
tion, falsity, conjunction, disjunction. The propositional proof system we implement is based
on a Hilbert-style axiomatization. In future work, we hope to expand our implementation to
full intuitionistic ﬁrst-order logic with existential and universal quantiﬁers and thus complete
the formalization of Troesltra and van Dalen’s proof. Our implementation also includes a mech-
anized proof of soundness and a countermodel for the general validity of the law of excluded
middle in intuitionistic propositional logic.
Acknowledgments
This research was supported in part by the Zhejiang Federation of Hu-
manities and Social Sciences grant 23YJRC04ZD.
References
[1] Bentzen, B.: A Henkin-style completeness proof for the modal logic S5. In: Logic and Argu-
mentation: 4th International Conference, CLAR 2021, Hangzhou, China, October 20–22, 2021,
Proceedings 4. pp. 459–467. Springer (2021)
[2] Carneiro,
M.:
The
Lean
3
Mathematical
Library
(mathlib).
URL:
https://robertylewis.com/ﬁles/icms/Carneiro mathlib.pdf
(2018),
international
Congress
on
Mathematical Software
[3] Coquand, C.: A formalised proof of the soundness and completeness of a simply typed lambda-
calculus with explicit substitutions. Higher-Order and Symbolic Computation 15(1), 57–90 (2002),
URL: https://doi.org/10.1023/A:1019964114625
[4] Coquand, T., Huet, G.: The Calculus of Constructions. Information and Compututation 76(2-3),
95–120 (1988), URL: https://hal.inria.fr/inria-00076024/document
[5] van Dalen, D.: Logic and structure, vol. 5. Springer (2013)
[6] From, A.H.: Formalizing Henkin-style completeness of an axiomatic system for propositional logic.
Proceedings of the ESSLLI & WeSSLLI Student Session pp. 1–12 (2020)
[7] From, A.H.: A succinct formalization of the completeness of ﬁrst-order logic. In: 27th International
Conference on Types for Proofs and Programs (TYPES 2021). Schloss Dagstuhl-Leibniz-Zentrum
f¨ur Informatik (2022)
[8] Hagemeier, C., Kirst, D.: Constructive and mechanised meta-theory of intuitionistic epistemic
logic. In: Logical Foundations of Computer Science: International Symposium, LFCS 2022, Deer-
ﬁeld Beach, FL, USA, January 10–13, 2022, Proceedings. pp. 90–111. Springer (2022)
[9] Herbelin, H., Lee, G.:
Forcing-based cut-elimination for Gentzen-style intuitionistic sequent
calculus. In:
H., O., M., K., de Queiroz R. (eds.) International Workshop on Logic, Lan-
guage, Information, and Computation. pp. 209–217. Springer, Berlin, Heidelberg (2009), URL:
https://doi.org/10.1007/978-3-642-02261-6 17
[10] Heyting, A.:
Die formalen Regeln der intuitionistischen Logik. Sitzungsbericht Preußische
Akademie der Wissenschaften Berlin, physikalisch-mathematische Klasse II pp. 42–56 (1930)
[11] Kripke, S.A.: Semantical analysis of intuitionistic logic I. In: Studies in Logic and the Foundations
of Mathematics, vol. 40, pp. 92–130. Elsevier (1965)
[12] Maggesi, M., Brogi, C.P.: A formal proof of modal completeness for provability logic. arXiv
preprint arXiv:2102.05945 (2021)
[13] de
Moura,
L.,
Kong,
S.,
Avigad,
J.,
Van
Doorn,
F.,
von
Raumer,
J.:
The
Lean
theorem
prover
(system
description).
In:
Felty,
A.,
Middeldorp,
A.
(eds.)
Interna-
11

---

Veriﬁed completeness in Henkin-style for intuitionistic propositional logic
H. Guo, D. Chen, and B. Bentzen
tional Conference on Automated Deduction. pp. 378–388. Springer,
Cham (2015),
URL:
https://doi.org/10.1007/978-3-319-21401-6 26
[14] Norell, U.: Dependently typed programming in Agda. In: Koopman, P., Plasmeijer, R., Swier-
stra, D. (eds.) International School on Advanced Functional Programming. pp. 230–266. Springer,
Berlin, Heidelberg (2008), uRL: https://doi.org/10.1007/978-3-642-04652-0 5
[15] Pfenning, F., Paulin-Mohring, C.: Inductively deﬁned types in the Calculus of Constructions. In:
International Conference on Mathematical Foundations of Programming Semantics. pp. 209–228.
Springer (1989)
[16] The Coq project: The Coq proof assistant. URL: http://www.coq.inria.fr (2017)
[17] Troelstra, A.S., van Dalen, D.: Constructivism in mathematics. Vol. I, Studies in Logic and the
Foundations of Mathematics, vol. 121. North-Holland, Amsterdam (1988)
12