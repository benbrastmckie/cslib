## Page 1

M. Marin, L. Leu¸stean (Eds.):
8th Symposium on Working Formal Methods (FROM 2024)
EPTCS 410, 2024, pp. 133–149, doi:10.4204/EPTCS.410.9
© Daﬁna Trufas,
This work is licensed under the
Creative Commons Attribution License.
Intuitionistic Propositional Logic in Lean
Daﬁna Trufas,
LOS, Faculty of Mathematics and Computer Science, University of Bucharest
Institute for Logic and Data Science, Bucharest
dafina.trufas@s.unibuc.ro
In this paper we present a formalization of Intuitionistic Propositional Logic in the Lean proof assis-
tant. Our approach focuses on verifying two completeness proofs for the studied logical system, as
well as exploring the relation between the two analyzed semantical paradigms - Kripke and algebraic.
In addition, we prove a large number of theorems and derived deduction rules.
1
Introduction
We formalize Intuitionistic Propositional Logic (IPL) using the Lean interactive theorem prover [4]. Our
main goal is verifying the soundness and the strong completeness of IPL, with respect to both the Kripke
and the Heyting algebras semantics. The language we work with has falsity, conjunction, disjunction and
implication as primitive connectives and for syntactical inference we use the Hilbert-style proof system
introduced by Gödel in [9].
For the formalization we present in this paper, we chose the Lean proof assistant [4]. An evidence
of Lean’s proving power and versatility is the Mathlib library [1], maintained by the Lean community.
This work aligns with the effort of the Mathlib community to encode mathematical knowledge, and
particularly logical systems, in Lean. The underlying theory of Lean is based on a version of dependent
type theory, known as the calculus of inductive constructions [3]. Thus, type-checking is the mechanism
which assists the user in their approach to prove mathematical statements, either by directly constructing
proof terms or by using Lean’s so-called tactic-mode.
In the following, we describe the main stages of the implementation and motivate our main design
choices. Sections 3.1 and 3.2 describe the formalization of the language and proof-system of IPL. The
Kripke completeness proof is based on the so-called canonical model, whose construction relies on the
notion of disjunctive theory. Some results about consistent and complete pairs, presented in Section 3.3,
are also essential in the ﬂow of this ﬁrst completeness theorem. In the upcoming Section 3.4, we intro-
duce the Kripke semantics, then in Section 3.5 we present the main steps of the completeness formalized
proof with respect to it. Similarly, Section 3.6 proceeds by deﬁning the necessary Heyting algebras no-
tions, establishes the algebraic semantics and concludes by proving the second completeness theorem
and establishing the equivalence between the validity notions. Our presentation is inspired by the text-
books of Mints [11], Fitting [5] and Troelstra [2], and the lecture notes of Kuznetsov[10] and Georgescu
[7, 6]. All the detailed proofs can be found in my Bachelor’s thesis, which is available online at [13].
To the best of our knowledge, the only proof of completeness for IPL formally-veriﬁed in Lean is
due to Guo, Chen and Bentzen [8]. However, the novelty of our approach consists in:
(i) using a different Hilbert-style proof system;
(ii) proving a large collection of theorems and derived deduction rules;
(iii) formalizing the algebraic semantics of IPL and proving a second completeness theorem, with
respect to it;


## Page 2

134
Intuitionistic Propositional Logic in Lean
(iv) implementing a semantic proof of the equivalence between algebraic and Kripke validity;
(v) the manner we dealt with the countability of the set of formulas, which we consider simpler than
the method in [8].
2
On the formalization
The Lean code is structured in 8 ﬁles, which we brieﬂy describe in the following. First, we have the
Formula.lean ﬁle, which contains the deﬁnition of the language (Section 3.1), as well as the proof of the
countability of the Formula type (Section 3.3). Then, the Syntax.lean ﬁle proceeds by formalizing the
deﬁnition of Proof (Section 3.2). It includes a large collection of theorems and derived deduction rules,
as well as the deduction theorem and some utilitary lemmas. The Semantics.lean ﬁle contains the deﬁni-
tion of the Kripke model, and the semantical deﬁnitions we detail in Section 3.4. In the Soundness.lean
ﬁle, the interested reader can ﬁnd the formalization of the soundness theorem (whose statement we men-
tion in Section 3.5.1), along with an auxiliary lemma used in its proof. Then, CompletenessListUtils.lean
groups together some utilitary lemmas about Finsets of formulas, which are useful when proving some
completeness-related theorems. The Kripke completeness theorem, presented in Section 3.5.2, preceded
by the deﬁnitions and results from Section 3.3, are formalized in the Completeness.lean ﬁle. Finally,
the Heyting algebras notions and necessary results are formalized in the HeytingAlgebraUtils.lean ﬁle,
while the algebraic semantics, culminating with its associated completeness theorem and the equivalence
between the validity notions can be found in HeytingAlgebraSemantics.lean.
Fragments of Lean proofs will be included in the presentation only if we consider they contain worth-
mentioning technical aspects, or, in some cases, in order to sketch the key proof-steps. The full source
code is almost 3300 lines long and is available online in [14].
3
Intuitionistic Propositional Logic
In this section, we proceed to describe the main aspects of our formalization. For full theoretical details
of the results and proofs, the interested reader may refer to [13].
3.1
Language
We ﬁrst formalize the countable set of propositional variables, as a wrapper over the Nat type. Structures
are used to deﬁne non-recursive inductive data types, containing only one constructor. And this is also
the case here: we can identify any propositional variable with a natural number, so it is convenient to
deﬁne the Var type as a structure with a single ﬁeld, specifying the index of the variable:
structure Var where
val : Nat
We work with a language containing falsity (⊥), conjunction (∧), disjunction (∨) and implication (→)
as primitive logical connectives. Thus, it is natural to deﬁne formulas by means of an inductive type, in
which the ﬁrst non-recursive constructor uses the above deﬁned structure type and simply encapsulates
it in a Formula term, the second is meant to construct falsity, while the following recursive constructors
correspond each to one of the primitive connectives:
inductive Formula where
| var : Var →Formula


## Page 3

Daﬁna Trufas,
135
| bottom : Formula
| and : Formula →Formula →Formula
| or : Formula →Formula →Formula
| implication : Formula →Formula →Formula
For readability reasons, we introduce the standard Unicode symbol for falsity and deﬁne inﬁx notations
for the binary connectives, which are much more convenient to use than the S-expressions in which Lean
displays the constructors by default. Additionally, we deﬁne the derived connectives for equivalence,
negation and truth, along with their standard notations:
notation "⊥" => bottom
infixl:60 " ∧∧" => and
infixl:60 " ∨∨" => or
infixr:50 (priority := high) " ⇒" => implication
def equivalence (ϕ ψ : Formula) := (ϕ ⇒ψ) ∧∧(ψ ⇒ϕ)
infix:40 " ⇔" => equivalence
def negation (ϕ : Formula) : Formula := ϕ ⇒⊥
prefix:70 " ∼" => negation
def top : Formula := ∼⊥
notation " ⊤" => top
3.2
Proof system
In this formalization, we adhere to the Hilbert-style proof system for IPL introduced by Gödel in [9]. We
deﬁne this using again an inductive type, with constructors for each axiom and deduction rule:
inductive Proof (Γ : Set Formula) : Formula →Type where
| premise {ϕ} : ϕ ∈Γ →Proof Γ ϕ
| contractionDisj {ϕ} : Proof Γ (ϕ ∨∨ϕ ⇒ϕ)
| contractionConj {ϕ} : Proof Γ (ϕ ⇒ϕ ∧∧ϕ)
| weakeningDisj {ϕ ψ} : Proof Γ (ϕ ⇒ϕ ∨∨ψ)
| weakeningConj {ϕ ψ} : Proof Γ (ϕ ∧∧ψ ⇒ϕ)
| permutationDisj {ϕ ψ} : Proof Γ (ϕ ∨∨ψ ⇒ψ ∨∨ϕ)
| permutationConj {ϕ ψ} : Proof Γ (ϕ ∧∧ψ ⇒ψ ∧∧ϕ)
| exfalso {ϕ} : Proof Γ (⊥⇒ϕ)
| modusPonens {ϕ ψ} : Proof Γ ϕ →Proof Γ (ϕ ⇒ψ) →Proof Γ ψ
| syllogism {ϕ ψ χ} : Proof Γ(ϕ ⇒ψ) →Proof Γ(ψ ⇒χ) →Proof Γ(ϕ ⇒χ)
| exportation {ϕ ψ χ} : Proof Γ (ϕ ∧∧ψ ⇒χ) →Proof Γ (ϕ ⇒ψ ⇒χ)
| importation {ϕ ψ χ} : Proof Γ (ϕ ⇒ψ ⇒χ) →Proof Γ (ϕ ∧∧ψ ⇒χ)
| expansion {ϕ ψ χ} : Proof Γ (ϕ ⇒ψ) →Proof Γ (χ ∨∨ϕ ⇒χ ∨∨ψ)
The notion of Γ-theorem is deﬁned as usual and we denote this by Γ ⊢ϕ. In Lean, we introduce this
notation, as follows:
infix:25 " ⊢" => Proof
The above deﬁnition of Proof generates an elimination rule for this type, which provides us with the
formalized mechanisms of the recursion and induction principles on proof terms.
Below we provide an example of how a pen-and-paper formal proof of a derived deduction rule can be


## Page 4

136
Intuitionistic Propositional Logic in Lean
transposed into a mechanized Lean proof:
(1)
Γ ⊢ϕ ∧ψ →ϕ
(WEAKENING)
(2)
Γ ⊢ϕ →ϕ ∨γ
(WEAKENING)
(3)
Γ ⊢ϕ ∧ψ →ϕ ∨γ
(SYLLOGISM): (1), (2)
def disjOfAndElimLeft : Γ ⊢ϕ ∧∧ψ ⇒ϕ ∨∨γ :=
syllogism weakeningConj weakeningDisj
Note that, in the reverse-Hilbert formalized proof, we don’t need to pass them explicitly, when construct-
ing the proof term, as the arguments of the constructors in the Proof type are implicit, so the Lean kernel
will synthesize them from the context.
3.3
Disjunctive theories, consistent and complete pairs
These notions of disjunctive theories, consistent and complete pairs, and some results regarding them
are essential in the Kripke completeness proof for IPL, as we will see in Section 3.5.2. Let us recall the
deﬁnitions of these notions, which can be consulted in [10]. A set of formulas is said to be a disjunctive
theory if it is deductively closed (Γ ⊢ϕ implies ϕ ∈Γ), consistent (Γ ⊬⊥) and disjunctive (Γ ⊢ϕ ∨ψ
implies Γ ⊢ϕ or Γ ⊢ψ). Then, a pair of sets of formulas (Γ,∆) is called consistent if there are no
G1,...,Gn ∈Γ and D1,...,Dm ∈∆, such that ⊢G1 ∧... ∧Gn →D1 ∨... ∨Dm. Finally, we say that a
consistent pair is complete, if it is a partition of the set of formulas.
def dedClosed {Γ : Set Formula} := ∀(ϕ : Formula), Γ ⊢ϕ →ϕ ∈Γ
def consistent {Γ : Set Formula} := Γ ⊢⊥→False
def disjunctive {Γ : Set Formula} :=
∀(ϕ ψ : Formula), Γ ⊢ϕ ∨∨ψ →Sum (Γ ⊢ϕ) (Γ ⊢ψ)
def disjunctiveTheory {Γ : Set Formula} :=
@dedClosed Γ /\ @consistent Γ /\ Nonempty (@disjunctive Γ)
def consistentPair {Γ ∆: Set Formula} :=
∀(Φ Ω: Finset Formula), Φ.toSet ⊆Γ →Ω.toSet ⊆∆→
(/0 ⊢Φ.toList.foldr Formula.and (∼⊥) ⇒Ω.toList.foldr Formula.or ⊥→
False)
def completePair {Γ ∆: Set Formula} :=
@consistentPair Γ ∆/\ ∀(ϕ : Formula),(ϕ ∈Γ /\ ϕ /∈∆) ∨(ϕ ∈∆/\
ϕ /∈Γ)
Below we give the formalized statement of the lemma claiming that given a consistent pair, any formula
can be added to one of the sets in the pair, preserving the consistency:
lemma add_preserves_cons :
@consistentPair Γ ∆→∀(ϕ : Formula), @consistentPair ({ϕ} ∪Γ) ∆∨
@consistentPair Γ ({ϕ} ∪∆)
The proof of the above lemma follows by reductio ad absurdum and it requires a syntactical derivation,
but it doesn’t give rise to any technical difﬁculties, so we do not present it here.


## Page 5

Daﬁna Trufas,
137
Then, to prove the essential consistent_incl_complete lemma, stating that any consistent pair can be
component-wise included in a complete one, we deﬁne an indexed family of formula-set pairs, thus:
def family (nf : Nat →Formula) (n : Nat) : Set Formula × Set Formula :=
match n with
| .zero => @add_formula_to_pair Γ ∆(nf 0)
| .succ n => @add_formula_to_pair (family nf n).fst (family nf n).snd
(nf (n + 1))
To have access to an enumeration of formulas, we pass as the ﬁrst argument a function which assigns, to
any natural number, a formula. Then, we inductively build the family, by adding the formulas to one of
the sets in the pair, whilst preserving the consistency. Without loss of generality, we deﬁne the function
to add the formula to the ﬁrst set in the pair, if possible:
def add_formula_to_pair (ϕ : Formula) : Set Formula × Set Formula :=
if @consistentPair ({ϕ} ∪Γ) ∆then (({ϕ} ∪Γ), ∆)
else (Γ, {ϕ} ∪∆)
By the add_preserves_cons lemma previously presented, it follows easily that applying the above de-
ﬁned add_ formula_to_pair function repeatedly, starting from a consistent pair, we preserve the consis-
tency of the obtained pairs.
The enumeration of formulas is not required to be bijective, a surjection from Nat to Formula is sufﬁcient
in this case, as we don’t have any restriction for adding the formulas only once. Classically, the existence
of an injective function from a type α to a type β gives evidence that there is a surjection from β to α.
Hence, we deﬁne an injective function from Formula to Nat.
To construct the injection, we use Cantor’s pairing function, which we multiply by two, for ease of
formalization. For a theretical presentation of Cantor’s encoding, refer to Section 1.3.9 in [2].
def pairing (x y : N) := (x + y) * (x + y + 1) + 2 * x
Then, we associate a numerical identiﬁer to any connective symbol and encode formulas into natural
numbers by recursively applying the pairing function on the structure of the formula, as follows:
def encode_form : Formula →N
| var v => pairing 0 (v.val + 1)
| bottom => 0
| ϕ ∧∧ψ => pairing (pairing (encode_form ϕ) 1) (encode_form ψ)
| ϕ ∨∨ψ => pairing (pairing (encode_form ϕ) 2) (encode_form ψ)
| ϕ ⇒ψ => pairing (pairing (encode_form ϕ) 3) (encode_form ψ)
After proving the injectivity of our encoding function, we are able to deﬁne an instance of Countable for
our Formula type. The Mathlib deﬁnition of the Countable type-class is as follows:
class Countable (α : Sort u) : Prop where
exists_injective_nat’ : ∃f : α →N, Injective f
So we immediately deﬁne the Countable instance for the Formula type, based on the proof of the en-
coding’s injectivity:
instance : Countable Formula := inject_Form.countable
Now, having the surjective enumeration at hand, we can get a step closer to the ﬁnal construction of the
complete pair which includes the initial consistent pair component-wise. We prove that any formula ϕ is


## Page 6

138
Intuitionistic Propositional Logic in Lean
contained in one of the sets of the pair with index fn(ϕ), where by fn we denote the injective encoding
of formulas into natural numbers:
lemma vp_in_Γi∆i (ϕ : Formula) (fn : Formula →Nat) (fn_inj : fn.Injective)
(nf : Nat →Formula) (nf_inv : nf = fn.invFun) :
ϕ ∈(@family Γ ∆nf (fn ϕ)).fst \/ ϕ ∈(@family Γ ∆nf (fn ϕ)).snd
In Mathlib, the inverse of a function is noncomputably deﬁned as follows:
noncomputable def invFun {α : Sort u} {β} [Nonempty α] (f : α →β) :
β →α :=
fun y 7→if h : (∃x, f x = y) then h.choose else Classical.arbitrary α
So this is why we can count on this inverse for any function, regardless of its bijectivity. Notice also that
the injectivity of fn gives evidence of invFun being the so-called le ft −inverse.
It is also crucial to prove that the family we deﬁned is increasing:
lemma increasing_family {nf : Nat →Formula} (i j : Nat) : i <= j →
(@family Γ ∆nf i).fst ⊆(@family Γ ∆nf j).fst /\
(@family Γ ∆nf i).snd ⊆(@family Γ ∆nf j).snd
Next, we deﬁne the component-wise union of the indexed pair-family:
def consistent_family_union (_ : @consistentPair Γ ∆) (nf : Nat →Formula) :
Set Formula × Set Formula :=
({ϕ | ∃i : Nat, ϕ ∈(@family Γ ∆nf i).fst},
{ϕ | ∃i : Nat, ϕ ∈(@family Γ ∆nf i).snd})
This is ﬁnally the witness we make use of when proving the existence of a complete pair, component-
wise including our initial consistent one. Of course, before using the family union this way, we have to
give evidence that it is indeed a partition of the set of formulas. The increasing property is crucial in
achieving this last-mentioned goal.
Finally, we present the formalized statement of the consistent_incl_complete lemma:
lemma consistent_incl_complete :
@consistentPair Γ ∆→(∃(Γ’ ∆’ : Set Formula), Γ ⊆Γ’ ∧∆⊆∆’ ∧
@completePair Γ’ ∆’)
This will be useful when proving the completeness of IPL with respect to the Kripke semantics, which
will be subsequently presented.
3.4
Kripke semantics
In the sequel, we deﬁne the Kripke semantics. The ﬁrst deﬁnition we need is, of course, that of a Kripke
model. We ﬁrst state this informally, then provide its corresponding formalization. An intuitionistic
propositional Kripke model is a tuple (W,R,V), whereW is a non-empty set, R is a reﬂexive and transitive
binary relation on W and V : Var ×W →{0,1} is a function assigning truth values to variables. V is
assumed to be monotone with respect to R, thus V(p,w) = 1 and Rww′ implies V(p,w′) = 1.
structure KripkeModel (W : Type) where
R : W →W →Prop
V : Var →W →Prop
refl (w : W) : R w w
trans (w1 w2 w3 : W) : R w1 w2 →R w2 w3 →R w1 w3
monotonicity (v : Var) (w1 w2 : W) : R w1 w2 →V v w1 →V v w2


## Page 7

Daﬁna Trufas,
139
We formalize the Kripke model as a parameterized structure, where the parameter W represents the space
of worlds. Thus, the worlds of a model are in Lean terms of type W. The ﬁrst ﬁeld of the structure models
the accessibility binary relation R over terms of type W and V is the valuation function, which takes two
arguments - a variable and an inhabitant of type W. Then, the last three ﬁelds are meant to formalize the
properties of the relation R (reﬂexivity and transitivity) and the monotonicity of the valuation.
The extended valuation function (on formulas) is deﬁned as follows:
def val {W : Type} (M : KripkeModel W) (w : W) : Formula →Prop
| Formula.var p => M.V p w
| ⊥=> False
| ϕ ∧∧ψ => val M w ϕ /\ val M w ψ
| ϕ ∨∨ψ => val M w ϕ \/ val M w ψ
| ϕ ⇒ψ => ∀(w’ : W), M.R w w’ /\ val M w’ ϕ →val M w’ ψ
We say that a formula ϕ is true at a world w of a model M, if V(ϕ,w) = 1 and we denote this by M,w ⊨ϕ.
Then, ϕ is said to be valid in a model M := (W,R,V), if M,w ⊨ϕ, for all w ∈W. And ﬁnally, ϕ is valid,
if it is valid in all the Kripke models. We denote this by ⊨ϕ.
Below, we present the formalization of these notions:
def true_in_world {W : Type} (M : KripkeModel W) (w : W) (ϕ : Formula): Prop :=
val M w ϕ
def valid_in_model {W : Type} (M : KripkeModel W) (ϕ : Formula) : Prop :=
∀(w : W), val M w Φ
def valid (ϕ : Formula) : Prop :=
∀(W : Type) (M : KripkeModel W), valid_in_model M Φ
We say that M,w forces Γ (and denote it by M,w ⊨Γ), if M,w ⊨ϕ, for all ϕ ∈Γ.
def model_sat_set {W : Type}(M : KripkeModel W)(Γ : Set Formula)(w : W):Prop:=
∀(ϕ : Formula), ϕ ∈Γ →val M w ϕ
Another essential notion is that of local semantic consequence. We say that a formula ϕ is a local
semantic consequence of a set Γ, if for all models M, and all worlds w in M, we have that M,w ⊨Γ
implies M,w ⊨ϕ. We denote this by Γ ⊨ϕ.
def sem_conseq (Γ : Set Formula) (ϕ : Formula) : Prop :=
∀(W : Type) (M : KripkeModel W) (w : W),
model_sat_set M Γ w →val M w ϕ
infix:50 " ⊨" => sem_conseq
Then, a set ∆is forced by Γ, if Γ ⊨ϕ, for all ϕ in ∆.
def set_forces_set (Γ ∆: Set Formula) : Prop :=
∀(ϕ : Formula), ϕ ∈∆→Γ ⊨ϕ
3.5
Kripke completeness theorem
3.5.1
Soundness
The soundness theorem claims that any Γ-theorem is a local semantic consequence of Γ (Γ ⊢ϕ implies
Γ ⊨ϕ), for any set of formulas Γ and any formula ϕ.


## Page 8

140
Intuitionistic Propositional Logic in Lean
In Lean, this statement transposes to:
theorem soundness (Γ : Set Formula) (ϕ : Formula) : Γ ⊢ϕ →Γ ⊨ϕ
The proof is straightforward, so we brieﬂy sketch it here. For full detail, the interested reader shall
consult the formalization.
We proceed by induction on Proof. For all the axiom cases, we apply an auxiliary lemma asserting that
any axiom is valid:
lemma axioms_valid (ϕ : Formula) (ax : Axiom ϕ) : valid ϕ
Worth-mentioning is also the use of the monotonicity property of the valuation function, in the exportation
case. We prove this result in Semantics.lean and mention here only its formalized claim:
lemma monotonicity_val (W : Type) (M : KripkeModel W) (w1 w2 : W) (ϕ : Formula):
M.R w1 w2 →val M w1 ϕ →val M w2 ϕ
3.5.2
Completeness
Theorem. (completeness theorem) For any set of formulas Γ and any formula ϕ:
Γ ⊢ϕ iff Γ ⊨ϕ.
The left implication is the soundness theorem, which was already proved in Section 3.5.1. For the reverse
implication in the completeness theorem, we appeal to nonconstructive reasoning, proceeding by con-
traposition. More precisely, we assume by reductio ad absurdum that Γ ⊬ϕ and then construct a Kripke
model (the so-called canonical model), which satisﬁes Γ, but does not satisfy ϕ. Hence, we get that ϕ
is not a local semantic consequence of Γ, which contradicts our assumption. Our approach follows the
Henkin-style completeness proof presented in [10].
We ﬁrst describe the construction of the canonical model. The domain is set to the type of the disjunctive
theories. This setDis jTh type is deﬁned as a subtype of the Set Formula type, as follows:
abbrev setDisjTh := {Γ // @disjunctiveTheory Γ}
For the re fl, trans, and monotonicity ﬁelds of the structure, we have to pass proofs of the set inclusion
relation satisfying these properties. These proofs are easily completed, using the corresponding Mathlib
theorems. Putting this all together, we have:
def canonicalModel : KripkeModel (setDisjTh) :=
{
R := fun (Γ ∆) => Γ.1 ⊆∆.1,
V := fun (v Γ) => Formula.var v ∈Γ.1,
refl := fun (Γ) => Set.Subset.rfl
trans := fun (Γ ∆Φ) => Set.Subset.trans
monotonicity := fun (v Γ ∆) => by intros; apply Set.mem_of_mem_of_subset
assumption’
}
Apart from lemma consistent_incl_complete we have already presented in Section 3.3, the Kripke com-
pleteness proof requires also the so-called main semantic lemma. This lemma states that the property of
the valuation in the deﬁnition of the canonical model, holds also for the extended valuation function on
formulas. Thus, it claims that M0,Γ ⊨ϕ if and only if ϕ ∈Γ, for any disjunctive theory Γ and formula ϕ:


## Page 9

Daﬁna Trufas,
141
lemma main_sem_lemma (Γ : setDisjTh) (ϕ : Formula) :
val canonicalModel Γ ϕ ↔ϕ ∈Γ.1
It is worth mentioning that the two implications in this lemma cannot be formalized as independent
lemmas, because of the implication case, where the proof of the left implication depends on the right
implication in the induction hypothesis, and vice versa.
Now we have all the necessary ingredients for the completenss contraposition proof informally presented
at the beginning of this section. The formalized completeness statement is the following:
theorem completeness {ϕ : Formula} {Γ : Set Formula} :
Γ ⊨ϕ ↔Nonempty(Γ ⊢ϕ)
3.6
Algebraic semantics and completeness theorem
Our approach in the current section is based on the exposition in the textbook [12] and the lecture notes
[6, 7]. After establishing the Heyting algebras necessary premises, we move on to deﬁning the algebraic
models of IPL and the Lindenbaum-Tarski algebra. Finally, we provide a second completeness proof,
with respect to the algebraic semantics and prove the equivalence between the Kripke and algebraic
validity.
3.6.1
Heyting algebras
First of all, we shall recall the deﬁnition of a Heyting algebra. A Heyting algebra (or pseudo-boolean
algebra) is a structure (H,∨,∧,→) such that H is a bounded lattice and the following residuation property
holds: a ≤b →c if and only if a∧b ≤c. Conventionally, we denote a Heyting algebra by H.
We start by formalizing the general deﬁnitions on Heyting algebras. Mathlib contains a deﬁnition of the
HeytingAlgebra type class, which encompasses the conditions a type has to satisfy, in order to have the
structure of a Heyting algebra. However, we have to formalize and prove the necessary deﬁnitions and
results about ﬁlters.
We consider a type α for which there is an instance of the Mathlib HeytingAlgebra class:
variable {α : Type u} [HeytingAlgebra α]
Then, we formalize the following main deﬁnitions, using the above α type-variable, to represent the
domain of the Heyting algebra.
A ﬁlter is a nonempty set F, satisfying two conditions: (i) for any x,y ∈F, x ∧y ∈F, (ii) for any x ∈F
and y ≥x, we have that y ∈F.
def filter (F : Set α) := (Set.Nonempty F) ∧(∀(x y : α), x ∈F →y ∈F →
x ⊓y ∈F) ∧(∀(x y : α), x ∈F →x ≤y →y∈F)
The ﬁlter generated by a set X is the intersection of all the ﬁlters which include X.
abbrev X_filters (X : Set α) := {F // filter F ∧X ⊆F}
def X_gen_filter (X : Set α) := {x | ∀(F : X_filters X), x ∈F.1}
A ﬁlter is called proper, if it doesn’t contains the ﬁrst element of the lattice.
def proper_filter (F : Set α) := filter F ∧⊥/∈F
Additionally, a proper ﬁlter F is said to be prime, if for all x,y ∈H, if x∨y ∈F, then x ∈F or y ∈F.


## Page 10

142
Intuitionistic Propositional Logic in Lean
def prime_filter {α : Type} [HeytingAlgebra α] (F : Set α) :=
proper_filter F ∧(∀(x y : α), x ⊔y ∈F →x ∈F ∨y ∈F)
Next, we present the central Heyting algebras result, which will be used in a subsequent section, when
transiting from an algebraic model to the corresponding Kripke one. It asserts that, given a ﬁlter F and
an element x which is not in F, there exists a prime ﬁlter P including the initial ﬁlter, such that x is neither
an element of P:
lemma super_prime_filter (x : α) (F : Set α) (Hfilter : @filter α _ F)
(Hnotin : x /∈F) :
∃(P : Set α), @prime_filter α _ P /\ F ⊆P /\ x /∈P
In the following, we informally sketch the proof of the above lemma and present key-fragments of its
formalization. First of all, we show that the set of all the prime ﬁlters not containing x has an upper
bound:
have Hzorn : ∃F’ ∈X_filters_not_cont_x x, F ⊆F’ ∧
∀(F’’ : Set α), F’’ ∈X_filters_not_cont_x x →F’ ⊆F’’ →
F’’ = F’
This is achieved by applying Zorn’s lemma, which is formalized in Mathlib as follows :
theorem zorn_subset_nonempty (S : Set (Set α))
(H : ∀(c) (_ : c ⊆S), IsChain (· ⊆·) c →c.Nonempty →
∃ub ∈S, ∀s ∈c, s ⊆ub) (x)
(hx : x ∈S) : ∃m ∈S, x ⊆m ∧∀a ∈S, m ⊆a →a = m
where isChain is a Prop deciding whether a given set is totally ordered. The upper bound we are looking
for is the union of all the chain’s elements. In the rest of the proof, our goal is to prove that this upper
bound is a prime ﬁlter, and we proceed by contraposition, in doing so. We consider two elements y,z such
that y /∈P and z /∈P. Then, the ﬁrst step is showing that P ⊂[P∪{y}) and its analogous P ⊂[P∪{z}).
Using these auxiliary hypotheses and the maximality of P, we prove that x ∈[P∪{y}) and x ∈[P∪{z}).
Now, having also this hypothesis at hand, the proof concludes by applying a few well-known Heyting
algebras properties, as already shown in the theoretical proof.
The following lemma provides a useful characterization of the ﬁlter generated by a set X:
lemma gen_filter_prop (X : Set α) :
X_gen_filter X = {a | ∃(l : List α), l.toFinset.toSet ⊆X∧inf_list l≤a}
We use this form of the generated ﬁlter to obtain an auxiliary result which is necessary for the proof of
the above super_prime_ filter lemma:
lemma mem_gen_ins_filter (F : Set α) (Hfilter : filter F) :
y ∈X_gen_filter (F ∪{x}) →∃(z : α), z ∈F /\ x ⊓z ≤y
Applying this last lemma, the residuation property and a few basic properties of Heyting algebras and
ﬁlters, we obtain another important result, which will be used when constructing the valuation function
of the Kripke model associated to an algebraic one:
lemma himp_not_mem (F : Set α) (Hfilter : filter F) (Himp_not_mem : x ⇒y/∈F) :
y /∈X_gen_filter (F ∪{x})


## Page 11

Daﬁna Trufas,
143
The super_prime_ filter lemma has also a couple of corollaries. The ﬁrst one states that given an element
x different from the last element of the algebra, there exists a prime ﬁlter P such that x /∈P:
lemma super_prime_filter_cor1 (x : α) (Hnottop : x ̸= ⊤) :
∃(P : Set α), @prime_filter α _ P /\ x /∈P
To prove this, we trivially show ﬁrst that {⊤} is a ﬁlter and then, using the super_prime_ filter lemma,
we obtain the necessary witness.
The second corollary follows immediately from the ﬁrst one. It claims that intersecting all the prime
ﬁlters, we obtain the set {⊤}:
lemma super_prime_filter_cor2 : Set.sInter (@prime_filters α _) = {⊤} :=
This is proved by double inclusion and will be of great importance in an upcoming section, when estab-
lishing the connection between the two semantical paradigms.
3.6.2
Algebraic models
An algebraic interpretation in H is a function h : Form →H satisfying the following conditions: h(⊥) = 0
and, for all ϕ,ψ ∈Form, h(ϕ ∧ψ) = h(ϕ) ∧h(ψ), h(ϕ ∨ψ) = h(ϕ) ∨h(ψ) and h(ϕ →ψ) = h(ϕ) →
h(ψ).
We formalize the notion of algebraic interpretation as follows:
def AlgInterpretation (I : Var →α) : Formula →α
| Formula.var p => I p
| Formula.bottom => ⊥
| ϕ ∧∧ψ => AlgInterpretation I ϕ ⊓AlgInterpretation I ψ
| ϕ ∨∨ψ => AlgInterpretation I ϕ ⊔AlgInterpretation I ψ
| ϕ ⇒ψ => AlgInterpretation I ϕ ⇒AlgInterpretation I ψ
An algebraic model is a tuple (H,h).
We’ve chosen not to explicitly deﬁne the notion of algebraic model in Lean, since it would have implied
to adjoin the above deﬁned interpretation function to the type. We considered this redundant, since an
algebraic model is uniquely determined by the variable-interpretation function.
A formula ϕ is true in an algebraic model (H,h), if h(ϕ) = 1. We denote this by (H,h) ⊨alg ϕ. We say
that ϕ is algebraically valid in H, if (H,h) ⊨alg ϕ, for any algebraic model (H,h). Finally, ϕ is called
algebraically valid, if ϕ is algebraically valid in any Heyting algebra H. This is denoted by ⊨alg ϕ.
def true_in_alg_model (I : Var →α) (ϕ : Formula) : Prop :=
AlgInterpretation I ϕ = Top.Top
def valid_in_alg (ϕ : Formula) : Prop :=
∀(I : Var →α), true_in_alg_model I ϕ
def alg_valid (ϕ : Formula) : Prop :=
∀(α : Type) [HeytingAlgebra α], @valid_in_alg α _ ϕ
A set of formulas Γ is true in an algebraic model, if (H,h) ⊨alg ϕ for any ϕ ∈Γ. We denote this by
(H,h) ⊨alg Γ. We say that Γ is algebraically valid in H, if (H,h) ⊨alg Γ, for any algebraic model (H,h).
A set Γ is algebraically valid, if it is algebraically valid in any Heyting algebra H. This is denoted by
⊨alg Γ.


## Page 12

144
Intuitionistic Propositional Logic in Lean
def set_true_in_alg_model (I : Var →α) (Γ : Set Formula) : Prop :=
∀(ϕ : Formula), ϕ ∈Γ →AlgInterpretation I ϕ = Top.top
def set_valid_in_alg (Γ : Set Formula) : Prop :=
∀(I : Var →α), set_true_in_alg_model I Γ
def set_alg_valid (Γ : Set Formula) : Prop :=
∀(α : Type) [HeytingAlgebra α], @set_valid_in_alg α _ Γ
We say that ϕ is an algebraic semantic consequence of Γ, if for any algebraic model (H,h), (H,h) ⊨alg Γ
implies (H,h) ⊨alg ϕ. We denote this by Γ ⊨alg ϕ.
def alg_sem_conseq (Γ : Set Formula) (ϕ : Formula) : Prop :=
∀(α : Type)[HeytingAlgebra α](I : Var →α), set_true_in_alg_model I Γ →
true_in_alg_model I ϕ
infix:50 " ⊨a " => alg_sem_conseq
3.6.3
Lindenbaum-Tarksi algebra
We deﬁne the following equivalence relation on formulas, with respect to a set Γ:
ϕ ∼Γ ψ iff Γ ⊢ϕ ↔ψ
Let Form/ ∼Γ be the quotient set. We denote the equivalence class of a formula ϕ by bϕΓ. The order
relation on Form/ ∼Γ is deﬁned as follows: bϕΓ ≤Γ bψΓ iff Γ ⊢ϕ →ψ.
Then, the quotient set Form/ ∼Γ is a Heyting algebra (called the Lindenbaum-Tarksi algebra), where:
bϕΓ ∨bψΓ = \
ϕ ∨ψΓ, bϕΓ ∧bψΓ = \
ϕ ∧ψΓ, bϕΓ →bψΓ = \
ϕ →ψΓ, b⊥Γ is the ﬁrst element and c
¬⊥Γ is the last
element.
First of all, we formalize the equivalence relation on formulas with respect to Γ, along with its standard
inﬁx notation:
def equiv (ϕ ψ : Formula) := Nonempty (Γ ⊢ϕ ⇔ψ)
infix:50 "∼" => equiv
Next, we deﬁne a setoid instance for our Formula type, by providing a proof of the above deﬁned relation
being indeed an equivalence relation and then we can move to deﬁning the ≤,∧,∨,→operations on
quotients of this setoid. To deﬁne quotient conjunction, disjunction and implication, we make use of the
built-in li ft2 function, which lifts the corresponding binary functions on formulas, to a quotient on both
arguments. We give below only the formalization of quotient conjunction. The other quotient operations
are deﬁned in a similar manner.
def Formula.and_quot (ϕ ψ : Formula) := Quotient.mk setoid_formula (ϕ ∧∧ψ)
def and_quot (ϕ ψ : Quotient setoid_formula) : Quotient setoid_formula :=
Quotient.lift2 Formula.and_quot and_quot_preserves_equiv ϕ ψ
Notice the fact that we have to pass as the second argument of li ft2 a proof of our binary operation
preserving equivalence. The statement of the corresponding lemma is as follows:
lemma and_quot_preserves_equiv (ϕ ψ ϕ’ ψ’ : Formula) : ϕ ∼ϕ’ →ψ ∼ψ’ →
(Formula.and_quot ϕ ψ = Formula.and_quot ϕ’ ψ’)


## Page 13

Daﬁna Trufas,
145
Having these operations deﬁned, we can prove that the quotient type associated to the ∼equivalence
relation is a Heyting algebra. We do so by deﬁning a Heyting algebra instance for this type:
instance lt_heyting : HeytingAlgebra (Quotient (@setoid_formula Γ))
We don’t provide the full deﬁnition of this instance here, but all the proofs we need to complete its ﬁelds
are rather trivial.
We deﬁne the mapping which associates to a formula its corresponding quotient:
def h_quot_var (v : Var) : Quotient (@setoid_formula Γ) :=
Quotient.mk setoid_formula (Formula.var v)
def h_quot (ϕ : Formula) : Quotient (@setoid_formula Γ) :=
Quotient.mk setoid_formula ϕ
The h_quot_var function will be passed as an argument to AlgInterpretation, when proving that h_quot
satisﬁes the conditions of an algebraic interpretation. The statement of this lemma is as follows:
lemma h_quot_interpretation : ∀(ϕ : Formula),
h_quot ϕ = (@AlgInterpretation
(Quotient (@setoid_formula Γ)) _ h_quot_var ϕ)
Then, we are able to prove the two results about the Lindenbaum-Tarski algebra, which will be crucial
in the proof of the algebraic completeness theorem. The ﬁrst one asserts that a set Γ is true at the
algebraic model generated by itself, whilst the second claims that a formula ϕ is true at the algebraic
model induced by Γ, if and only if ϕ is a Γ-theorem. We mention only their statements below, as the
proofs do not contain any technical difﬁculties:
lemma set_true_in_lt :
@set_true_in_alg_model (Quotient (@setoid_formula Γ)) _ h_quot_var Γ
lemma true_in_lt (ϕ : Formula) :
@true_in_alg_model (Quotient (@setoid_formula Γ)) _ h_quot_var ϕ ↔
Nonempty (Γ ⊢ϕ)
3.6.4
Algebraic completeness theorem
Theorem. [algebraic completeness] For any set of formulas Γ and any formula ϕ,
Γ ⊢ϕ iff Γ ⊨alg ϕ.
The soundness implication follows immediately, by a straightforward induction. We mention only its
formalized statement here:
theorem soundness_alg (ϕ : Formula) : Nonempty (Γ ⊢ϕ) →alg_sem_conseq Γ ϕ
Moving now to the reverse implication, the proof is based on the two results mentioned at the end of
Section 3.6.3. Below, we present the full formalization of the algebraic completeness theorem:
theorem completeness_alg (ϕ : Formula) :
alg_sem_conseq Γ ϕ ↔Nonempty (Γ ⊢ϕ) :=
by
apply Iff.intro
· intro Halg
rw [←true_in_lt]
exact Halg (Quotient (@setoid_formula Γ)) h_quot_var set_true_in_lt
· exact soundness_alg ϕ


## Page 14

146
Intuitionistic Propositional Logic in Lean
3.6.5
Kripke models and algebraic models
The central result in this last section is the equivalence between the two validity notions:
⊨ϕ iff ⊨alg ϕ
We follow the approach in [5] and hence give a pure semantical proof of the above mentioned result,
wihtout using the completeness theorems of the two semantics. We start by establishing a connection
from Kripke models to algebraic models. In doing so, we have to deﬁne ﬁrst the notions of closed set,
and the Heyting algebra structure which can be built on top of the set of all the closed sets.
Thus, the following Prop decides whether a domain set of a Kripke model is closed:
def closed {W : Type} (M : KripkeModel W) (A : Set W) : Prop :=
∀(w w’ : W), w ∈A →M.R w w’ →w’ ∈A
We formalize the set of all closed subsets as a subtype of the SetW type, as follows:
def all_closed {W : Type} (M : KripkeModel W) := {A // @closed W M A}
For the implication operation on closed subsets, we ﬁrst deﬁne the set of all closed sets contained in
W \ A ∪B, where by A,B we denote the two implication operands. Then, the union of the elements in
this set is the greatest closed set satisfying our condition:
def all_closed_subset {W : Type} (M : KripkeModel W) (A B : all_closed M) :=
{X | @closed W M X /\ X ⊆((@Set.univ W) \ A.1) ∪B.1}
def himp_closed {W : Type} {M : KripkeModel W} (A B : all_closed M) :=
Set.sUnion (@all_closed_subset W M A B)
We deﬁne the corresponding Heyting algebra instance, as follows:
instance {W : Type} (M : KripkeModel W) : HeytingAlgebra (all_closed M) :=
{ sup := λ X Y => {val := X.1 ∪Y.1, property := union_preserves_closed X Y}
le := λ X Y => X.1 ⊆Y.1
le_refl := λ _ => Set.Subset.rfl
le_trans := λ _ _ _ => Set.Subset.trans
le_antisymm := λ _ _ => by rw [Subtype.ext_iff]; apply Set.Subset.antisymm
le_sup_left := λ X Y => Set.subset_union_left X.1 Y.1
le_sup_right := λ X Y => Set.subset_union_right X.1 Y.1
sup_le := λ _ _ _ => Set.union_subset
inf := λ X Y => {val := X.1 ∩Y.1, property := inter_preserves_closed X Y}
inf_le_left := λ X Y => Set.inter_subset_left X.1 Y.1
inf_le_right := λ X Y => Set.inter_subset_right X.1 Y.1
le_inf := λ _ _ _ => Set.subset_inter
top := {val := @Set.univ W, property := univ_closed}
le_top := λ X => Set.subset_univ X.1
himp := λ X Y => {val := himp_closed X Y, property := himp_is_closed X Y}
le_himp_iff := λ X Y Z => himp_closed_prop Y Z X
bot := {val := /0, property := empty_closed}
bot_le := λ X => Set.empty_subset X.1
compl := λ X => {val := himp_closed X {val := /0, property := empty_closed},
property := himp_is_closed X {val := /0,
property := empty_closed}}
himp_bot := by simp }


## Page 15

Daﬁna Trufas,
147
The next step is proving that the following function is an algebraic interpretation:
def h {W : Type} {M : KripkeModel W} (ϕ : Formula) : all_closed M :=
{val := {w | val M w ϕ}, property := by intro w w’ Hwin Hr
apply monotonicity_val
assumption’}
Except for the implication case, the proof is trivial. We present here the main steps of this last interesting
case. The proof is by double inclusion, but before succeeding in doing so, we need to prove an additional
statement, which holds only for closed subsets:
have Haux : ∀(A : all_closed M),
A.1 ⊆(@h W M (ψ ⇒χ)).1 ↔A.1 ∩(@h W M ψ).1 ⊆(@h W M χ).1
By this point, we can formalize the ﬁrst central result of the section, which provides a method of con-
structing an algebraic model corresponding to a given Kripke model:
lemma kripke_alg {W : Type} {M : KripkeModel W} (ϕ : Formula) :
valid_in_model M ϕ ↔@true_in_alg_model (all_closed M) _ h_var ϕ
In the sequel, we aim to formalize also the reverse direction, namely the switch from an algebraic model
to a corresponding Kripke one. We ﬁrst deﬁne the Kripke frame based on the set of all prime ﬁlters. The
accessibility relation is given by inclusion and a variable is said to be true at a world of a prime ﬁlter F,
if it is an element of F:
def prime_filters_frame (I : Var →α) :
KripkeModel (@prime_filters α _) :=
{
R := λ (F1 F2) => F1.1 ⊆F2.1,
V := λ (v F) => I v ∈F.1,
refl := λ (F) => Set.Subset.rfl,
trans := λ (F1 F2 Φ) => Set.Subset.trans,
monotonicity := λ (v F1 F2) => by intros
apply Set.mem_of_mem_of_subset
assumption’
}
and prove that the function given by:
def Vh (ϕ : Formula) (F : @prime_filters α _) (I : Var →α) : Prop :=
AlgInterpretation I ϕ ∈F.1
is a valuation function for this frame.
Now, we can state and prove the second relation between algebraic and Kripke models:
lemma alg_kripke (I : Var →α) (ϕ : Formula) :
true_in_alg_model I ϕ ↔valid_in_model (prime_filters_frame I) ϕ
Finally, having this auxiliary results at hand, we can immediately prove the equivalence between Kripke
and algebraic validity:
theorem alg_kripke_valid_equiv (ϕ : Formula) :
alg_valid ϕ ↔valid ϕ :=
by
apply Iff.intro


## Page 16

148
Intuitionistic Propositional Logic in Lean
· intro Halg _ _
rw [kripke_alg]; apply Halg
· intro Hvalid _ _ _
rw [alg_kripke]; apply Hvalid
4
Conclusion and future work
We have used the Lean proof assistant to formally verify the completeness of IPL. After deﬁning the
language, we formalized the Hilbert-style proof system and used it to establish a collection of syntactic
theorems and derived deduction rules. The next crucial step was formally specifying the two studied
semantics: Kripke and algebraic. For the proof of the completeness theorem with respect to the Kripke
semantics, we deﬁned the so-called canonical model, and used it in order to complete the proof by con-
traposition. On the other hand, for the algebraic completeness proof, we made use of the Lindenbaum-
Tarski algebra and some of its speciﬁc properties.
As future work, we aim to extend the current formalization to express Intuitionistic First-Order Logic
and also provide a completeness proof for this more complex system. Furthermore, we intend to imple-
ment in Lean formal systems for intuitionistic arithmetical analysis and associated proof interpretations,
as the ones presented in [2].
5
Acknowledgements
The author thanks Laurent,iu Leus,tean and Traian S, erb˘anut, ˘a for providing comments and suggestions
that improved the ﬁnal version of the paper.
References
[1] A Mathlib Overview. Available at https://leanprover-community.github.io/mathlib-overview.
html.
[2] (1973): Metamathematical Investigation Of Intuitionistic Arithmetic And Analysis. In A. S. Troelstra, editor:
Lecture Notes in Mathematics, 344, Springer, Berlin Heidelberg, doi:10.1007/BFb0066739.
[3] T. Coquand & G. Huet (1988): The Calculus of Constructions. Information and Computation 76(2-3), pp.
95–120, doi:10.1016/0890-5401(88)90005-3.
[4] L. De Moura, S. Kong, J. Avigad, F. Van Doorn & J. von Raumer (2015): The Lean theorem prover (system
description). In A. Felty & A. Middeldorp, editors: Automated Deduction-CADE-25: 25th International
Conference on Automated Deduction, Berlin, Germany, August 1-7, 2015, Proceedings 25, Lecture Notes in
Computer Science 9195, Springer, pp. 378–388, doi:10.1007/978-3-319-21401-6_26.
[5] M. C. Fitting (1968): Intuitionistic Logic, Model Theory and Forcing. Studies in Logic and the Foundations
of Mathematics, North-Holland, Amsterdam, doi:10.2307/2271564.
[6] G. Georgescu (1995): Notes on Heyting Algebras (in Romanian). Lecture Notes, University of Bucharest.
[7] G. Georgescu (1995): Notes on Intuitionistic Logic (in Romanian). Lecture Notes, University of Bucharest.
[8] H. Guo, D. Chen & B. Bentzen (2023): Veriﬁed completeness in Henkin-style for intuitionistic propositional
logic. In B. Bentzen, B. Liao, D. Liga, R. Markovich, B. Wei, M. Xiong & T. Xu, editors: Logics for AI and
Law, College Publications, London, pp. 36–48, doi:10.48550/arXiv.2310.01916.
[9] K. Gödel (1958): Über eine bisher noch nicht benutzte Erweiterung des ﬁniten Standpunktes. Dialectica 12,
pp. 280–287, doi:10.1111/j.1746-8361.1958.tb01464.x.


## Page 17

Daﬁna Trufas,
149
[10] S. Kuznetsov (2017): Propositional Intuitionistic Logic. Lecture Notes, University of Pennsylvania.
[11] G. Mints (2000): A Short Introduction To Intuitionistic Logic. The University Series in Mathematics, Kluwer,
New York, doi:10.1007/b115304.
[12] H Rasiowa & R Sikorski (1963): The mathematics of metamathematics. Panstwowe Wydawnictwo Naukowe,
Warsaw, doi:10.1112/jlms/s1-41.1.572.
[13] D. Trufas, (2024): Intuitionistic Logic in Lean.
Bachelor Thesis, University of Bucharest.
Available at
https://github.com/DafinaTrufas/Intuitionistic-Logic-Lean.
[14] D.
Trufas,
(2024):
Intuitionistic
Logic
in
Lean.
https://github.com/DafinaTrufas/
Intuitionistic-Logic-Lean.
