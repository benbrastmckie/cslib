# The Completeness of the First-Order Functional Calculus

**Leon Henkin**

*The Journal of Symbolic Logic*, Vol. 14, No. 3 (Sep., 1949), pp. 159--166.
Published by: Association for Symbolic Logic.
Stable URL: <http://www.jstor.org/stable/2267044>

---

Although several proofs have been published showing the completeness of the propositional calculus (cf. Quine (1)[^2]), for the first-order functional calculus only the original completeness proof of Godel (2) and a variant due to Hilbert and Bernays have appeared. Aside from novelty and the fact that it requires less formal development of the system from the axioms, the new method of proof which is the subject of this paper possesses two advantages. In the first place an important property of formal systems which is associated with completeness can now be generalized to systems containing a non-denumerable infinity of primitive symbols. While this is not of especial interest when formal systems are considered as logics---i.e., as means for analyzing the structure of languages---it leads to interesting applications in the field of abstract algebra. In the second place the proof suggests a new approach to the problem of completeness for functional calculi of higher order. Both of these matters will be taken up in future papers.

## Primitive Symbols and Well-Formed Formulas

The system with which we shall deal here will contain as primitive symbols $($, $)$, $\supset$, $f$, and certain sets of symbols as follows:

(i) propositional symbols (some of which may be classed as variables, others as constants), and among which the symbol "$f$" above is to be included as a constant;

(ii) for each number $n = 1, 2, \ldots$ a set of functional symbols of degree $n$ (which again may be separated into variables and constants); and

(iii) individual symbols among which variables must be distinguished from constants. The set of variables must be infinite.

Elementary well-formed formulas are the propositional symbols and all formulas of the form $G(x_1, \ldots, x_n)$ where $G$ is a functional symbol of degree $n$ and each $x_i$ is an individual symbol.

Well-formed formulas (wffs) consist of the elementary well-formed formulas together with all formulas built up from them by repeated application of the following methods:

(i) If $A$ and $B$ are wffs so is $(A \supset B)$;

(ii) If $A$ is a wff and $x$ an individual variable then $(x)A$ is a wff. Method (ii) for forming wffs is called quantification with respect to the variable $x$. Any occurrence of the variable $x$ in the formula $(x)A$ is called bound. Any occurrence of a symbol which is not a bound occurrence of an individual variable according to this rule is called free.

[^1]: This paper contains results of research undertaken while the author was a National Research Council predoctoral fellow. The material is included in "The Completeness of Formal Systems," a thesis presented to the faculty of Princeton University in candidacy for the degree of Doctor of Philosophy.

[^2]: Numbers refer to items in the bibliography appearing at the end of the paper.

## Interpretation

In addition to formal manipulation of the formulas of this system we shall be concerned with their meaning according to the following interpretation. The propositional constants are to denote one of the truth values, $T$ or $F$, the symbol "$f$" denoting $F$, and the propositional variables are to have the set of these truth values as their range. Let an arbitrary set, $I$, be specified as a domain of individuals, and let each individual constant denote a particular element of this domain while the individual variables have $I$ as their range. The functional constants (variables) of degree $n$ are to denote (range over) subsets of the set of all ordered $n$-tuples of $I$. $G(x_1, \ldots, x_n)$ is to have the value $T$ or $F$ according as the $n$-tuple $(x_1, \ldots, x_n)$ of individuals is or is not in the set $G$; $(A \supset B)$ is to have the value $F$ if $A$ is $T$ and $B$ is $F$, otherwise $T$; and $(x)A$ is to have the value $T$ just in case $A$ has the value $T$ for every element $x$ in $I$.[^3]

[^3]: A more precise, syntactical account of these ideas can be formulated along the lines of Tarski (3). But this semantical version will suffice for our purposes.

If $A$ is a wff, $I$ a domain, and if there is some assignment of denotations to the constants of $A$ and of values of the appropriate kind to the variables with free occurrences in $A$, such that for this assignment $A$ takes on the value $T$ according to the above interpretation, we say that $A$ is *satisfiable with respect to $I$*. If every such assignment yields the value $T$ for $A$ we say that $A$ is *valid with respect to $I$*. $A$ is *valid* if it is valid with respect to every domain. We shall give a set of axioms and formal rules of inference adequate to permit formal proofs of every valid formula.

## Abbreviations

Before giving the axioms, however, we describe certain rules of abbreviation which we use to simplify the appearance of wffs and formula schemata. If $A$ is any wff and $x$ any individual variable we write

$$\neg A \quad \text{for} \quad (A \supset f),$$

$$(\exists x)A \quad \text{for} \quad \neg(x)\neg A.$$

From the rules of interpretation it is seen that $\neg A$ has the value $T$ or $F$ according as $A$ has the value $F$ or $T$, while $(\exists x)A$ denotes $T$ just in case there is some individual $x$ in $I$ for which $A$ has the value $T$.

Furthermore we may omit outermost parentheses, replace a left parenthesis by a dot omitting its mate at the same time if its mate comes at the end of the formula (except possibly for other right parentheses), and put a sequence of wffs separated by occurrences of "$\supset$" when association to the left is intended. For example,

$$A \supset B \supset {.}\; C \supset D \supset E \quad \text{for} \quad ((A \supset B) \supset ((C \supset D) \supset E)),$$

where $A, B, C, D, E$ may be wffs or abbreviations of wffs.

## Axioms

If $A$, $B$, $C$ are any wffs, the following are called axioms:

1. $C \supset {.}\; B \supset C$

2. $A \supset B \supset {.}\; A \supset (B \supset C) \supset {.}\; A \supset C$

3. $A \supset f \supset f \supset A$

4. $(x)(A \supset B) \supset {.}\; A \supset (x)B$, where $x$ is any individual variable with no free occurrence in $A$.

5. $(x)A \supset B$, where $x$ is any individual variable, $y$ any individual symbol, and $B$ is obtained by substituting $y$ for each free occurrence of $x$ in $A$, provided that no free occurrence of $x$ in $A$ is in a well-formed part of $A$ of the form $(y)C$.

## Rules of Inference

There are two formal rules of inference:

**I (Modus Ponens).** To infer $B$ from any pair of formulas $A$, $A \supset B$.

**II (Generalization).** To infer $(x)A$ from $A$, where $x$ is any individual variable.

## Formal Proofs

A finite sequence of wffs is called a *formal proof from assumptions $\Gamma$*, where $\Gamma$ is a set of wffs, if every formula of the sequence is either an axiom, an element of $\Gamma$, or else arises from one or two previous formulas of the sequence by modus ponens or generalization, except that no variable with a free occurrence in some formula of $\Gamma$ may be generalized upon. If $A$ is the last formula of such a sequence we write $\Gamma \vdash A$. Instead of $\{\Gamma, A\} \vdash B$ ($\{\Gamma, A\}$ denoting the set formed from $\Gamma$ by adjoining the wff $A$), we shall write $\Gamma, A \vdash B$. If $\Gamma$ is the empty set we call the sequence simply a *formal proof* and write $\vdash A$. In this case $A$ is called a *formal theorem*. Our object is to show that every valid formula is a formal theorem, and hence that our system of axioms and rules is complete.

## Preliminary Theorems

The following theorems about the first-order functional calculus are all either well-known and contained in standard works, or else very simply derivable from such results. We shall use them without proof here, referring the reader to Church (4) for a fuller account.

**III (The Deduction Theorem).** If $\Gamma, A \vdash B$ then $\Gamma \vdash A \supset B$ (for any wffs $A$, $B$ and any set $\Gamma$ of wffs).

6. $\vdash B \supset f \supset {.}\; B \supset C$

7. $\vdash B \supset {.}\; C \supset f \supset {.}\; B \supset C \supset f$

8. $\vdash (x)(A \supset f) \supset {.}\; (\exists x)A \supset f$

9. $\vdash (x)B \supset f \supset {.}\; (\exists x)(B \supset f)$

**IV.** If $\Gamma$ is a set of wffs no one of which contains a free occurrence of the individual symbol $u$, if $A$ is a wff and $B$ is obtained from it by replacing each free occurrence of $u$ by the individual symbol $x$ (none of these occurrences of $x$ being bound in $B$), then if $\Gamma \vdash A$, also $\Gamma \vdash B$.

This completes our description of the formal system; or, more accurately, of a class of formal systems, a certain degree of arbitrariness having been left with respect to the nature and number of primitive symbols.

## Consistency and Satisfiability

Let $S_0$ be a particular system determined by some definite choice of primitive symbols. A set $\Delta$ of wffs of $S_0$ will be called *inconsistent* if $\Delta \vdash f$, otherwise *consistent*. A set $\Delta$ of wffs of $S_0$ will be said to be *simultaneously satisfiable* in some domain $I$ of individuals if there is some assignment of denotations (values) of the appropriate type to the constants (variables) with free occurrences in formulas of $\Delta$, for which each of these formulas has the value $T$ under the interpretation previously described.

## The Main Theorem

**THEOREM.** *If $\Delta$ is a set of formulas of $S_0$ in which no member has any occurrence of a free individual variable, and if $\Delta$ is consistent, then $\Delta$ is simultaneously satisfiable in a domain of individuals having the same cardinal number as the set of primitive symbols of $S_0$.*

We shall carry out the proof for the case where $S_0$ has only a denumerable infinity of symbols, and indicate afterward the simple modifications needed in the general case.

### Construction of the Extended Systems

Let $u_{ij}$ ($i, j = 1, 2, 3, \ldots$) be symbols not occurring among the symbols of $S_0$. For each $i$ ($i = 1, 2, 3, \ldots$) let $S_i$ be the first-order functional calculus whose primitive symbols are obtained from those of $S_{i-1}$ by adding the symbols $u_{ij}$ ($j = 1, 2, 3, \ldots$) as individual constants. Let $S_\omega$ be the system whose symbols are those appearing in any one of the systems $S_i$. It is easy to see that the wffs of $S_\omega$ are denumerable, and we shall suppose that some particular enumeration is fixed on so that we may speak of the first, second, $\ldots$, $n$th, $\ldots$ formula of $S_\omega$ in the standard ordering.

### Construction of the Maximal Consistent Set

We can use this ordering to construct in $S_0$ a maximal consistent set of cwffs, $\Gamma_0$, which contains the given set $\Delta$. (We use "cwff" to mean closed wff: a wff which contains no free occurrence of any individual variable.) $\Gamma_0$ is maximal consistent in the sense that if $A$ is any cwff of $S_0$ which is not in $\Gamma_0$, then $\Gamma_0, A \vdash f$; but not $\Gamma_0 \vdash f$.

To construct $\Gamma_0$ let $\Gamma_0^0$ be $\Delta$ and let $B_1$ be the first (in the standard ordering) cwff $A$ of $S_0$ such that $\{\Gamma_0^0, A\}$ is consistent. Form $\Gamma_0^1$ by adding $B_1$ to $\Gamma_0^0$. Continue this process as follows. Assuming that $\Gamma_0^i$ and $B_i$ have been found, let $B_{i+1}$ be the first cwff $A$ (of $S_0$) after $B_i$, such that $\{\Gamma_0^i, A\}$ is consistent; then form $\Gamma_0^{i+1}$ by adding $B_{i+1}$ to $\Gamma_0^i$. Finally let $\Gamma_0$ be composed of those formulas appearing in any $\Gamma_0^i$ ($i = 0, 1, \ldots$). Clearly $\Gamma_0$ contains $\Delta$. $\Gamma_0$ is consistent, for if $\Gamma_0 \vdash f$ then the formal proof of $f$ from assumptions $\Gamma_0$ would be a formal proof of $f$ from some finite subset of $\Gamma_0$ as assumptions, and hence for some $i$ ($i = 0, 1, \ldots$) $\Gamma_0^i \vdash f$ contrary to construction of the sets $\Gamma_0^i$. Finally, $\Gamma_0$ is maximal consistent because if $A$ is a cwff of $S_0$ such that $\{\Gamma_0, A\}$ is consistent then surely $\{\Gamma_0^i, A\}$ is consistent for each $i$; hence $A$ will appear in some $\Gamma_0^i$ and so in $\Gamma_0$.

### Extending with Witnesses

Having obtained $\Gamma_0$ we proceed to the system $S_1$ and form a set $\Gamma_1$ of its cwffs as follows. Select the first (in the standard ordering) cwff of $\Gamma_0$ which has the form $(\exists x)A$ (unabbreviated: $((x)(A \supset f) \supset f)$), and let $A'$ be the result of substituting the symbol $u_{11}$ of $S_1$ for all free occurrences of the variable $x$ in the wff $A$. The set $\{\Gamma_0, A'\}$ must be a consistent set of cwffs of $S_1$. For suppose that $\Gamma_0, A' \vdash f$. Then by III (the Deduction Theorem), $\Gamma_0 \vdash A' \supset f$; hence by IV, $\Gamma_0 \vdash A \supset f$; by II, $\Gamma_0 \vdash (x)(A \supset f)$; and so by 8 and I, $\Gamma_0 \vdash (\exists x)A \supset f$. But by assumption $\Gamma_0 \vdash (\exists x)A$. Hence modus ponens gives $\Gamma_0 \vdash f$ contrary to the construction of $\Gamma_0$ as a consistent set.

We proceed in turn to each cwff of $\Gamma_0$ having the form $(\exists x)A$, and for the $j$th of these we add to $\Gamma_0$ the cwff $A'$ of $S_1$ obtained by substituting the constant $u_{1j}$ for each free occurrence of the variable $x$ in the wff $A$. Each of these adjunctions leaves us with a consistent set of cwffs of $S_1$ by the argument above. Finally, after all such formulas $A'$ have been added, we enlarge the resulting set of formulas to a maximal consistent set of cwffs of $S_1$ in the same way that $\Gamma_0$ was obtained from $\Delta$ in $S_0$. This set of cwffs we call $\Gamma_1$.

After the set $\Gamma_i$ has been formed in the system $S_i$ we construct $\Gamma_{i+1}$ in $S_{i+1}$ by the same method used in getting $\Gamma_1$ from $\Gamma_0$ but using the constants $u_{(i+1)j}$ ($j = 1, 2, 3, \ldots$) in place of $u_{1j}$.

### Properties of $\Gamma_\omega$

Finally we let $\Gamma_\omega$ be the set of cwffs of $S_\omega$ consisting of all those formulas which are in any $\Gamma_i$. It is easy to see that $\Gamma_\omega$ possesses the following properties:

(i) $\Gamma_\omega$ is a maximal consistent set of cwffs of $S_\omega$.

(ii) If a formula of the form $(\exists x)A$ is in $\Gamma_\omega$ then $\Gamma_\omega$ also contains a formula $A'$ obtained from the wff $A$ by substituting some constant $u_{ij}$ for each free occurrence of the variable $x$.

Our entire construction has been for the purpose of obtaining a set of formulas with these two properties; they are the only properties we shall use now in showing that the elements of $\Gamma_\omega$ are simultaneously satisfiable in a denumerable domain of individuals.

### The Model Construction

In fact we take as our domain $I$ simply the set of individual constants of $S_\omega$ and we assign to each such constant (considered as a symbol in an interpreted system) itself (considered as an individual) as denotation. It remains to assign values in the form of truth-values to propositional symbols, and sets of ordered $n$-tuples of individuals to functional symbols of degree $n$, in such a way as to lead to a value $T$ for each cwff of $\Gamma_\omega$.

Every propositional symbol, $A$, of $S_\omega$ is a cwff of $S_\omega$; we assign to it the value $T$ or $F$ according as $\Gamma_\omega \vdash A$ or not. Let $G$ be any functional symbol of degree $n$. We assign to it the class of those $n$-tuples $(a_1, \ldots, a_n)$ of individual constants such that $\Gamma_\omega \vdash G(a_1, \ldots, a_n)$.

This assignment determines a unique truth-value for each cwff of $S_\omega$, under the fundamental interpretation prescribed for quantification and "$\supset$". (We may note that the symbol "$f$" is assigned $F$ in agreement with that interpretation since $\Gamma_\omega$ is consistent.)

## The Key Lemma

**LEMMA:** *For each cwff $A$ of $S_\omega$ the associated value is $T$ or $F$ according as $\Gamma_\omega \vdash A$ or not.*

The proof is by induction on the length of $A$. We may notice, first, that if we do not have $\Gamma_\omega \vdash A$ for some cwff $A$ of $S_\omega$ then we do have $\Gamma_\omega \vdash A \supset f$. For by property (i) of $\Gamma_\omega$ we would have $\Gamma_\omega, A \vdash f$ and so $\Gamma_\omega \vdash A \supset f$ by III.

### Base Case

In case $A$ is an elementary cwff the lemma is clearly true from the nature of the assignment.

### Inductive Case: $A$ is $B \supset C$

Suppose $A$ is $B \supset C$. If $C$ has the value $T$, by induction hypothesis $\Gamma_\omega \vdash C$; then $\Gamma_\omega \vdash B \supset C$ by 1 and I. This agrees with the lemma since $B \supset C$ has the value $T$ in this case. Similarly, if $B$ has the value $F$ we do not have $\Gamma_\omega \vdash B$ by induction hypothesis. Hence $\Gamma_\omega \vdash B \supset f$, and $\Gamma_\omega \vdash B \supset C$ by 6 and I. Again we have agreement with the lemma since $B \supset C$ has the value $T$ in this case also. Finally if $B$ and $C$ have the values $T$ and $F$ respectively, so that (induction hypothesis) $\Gamma_\omega \vdash B$ while $\Gamma_\omega \vdash C \supset f$, we must show that $\Gamma_\omega \vdash B \supset C$ does not hold (since $B \supset C$ has the value $F$ in this case). But by 7 and two applications of I we conclude that $\Gamma_\omega \vdash B \supset C \supset f$. Now we see that if $\Gamma_\omega \vdash B \supset C$ then $\Gamma_\omega \vdash f$ by I, contrary to the fact that $\Gamma_\omega$ is consistent (property (i)).

### Inductive Case: $A$ is $(x)B$

Suppose $A$ is $(x)B$. If $\Gamma_\omega \vdash (x)B$ then (by 5 and I) $\Gamma_\omega \vdash B'$, where $B'$ is obtained by replacing all free occurrences of $x$ in $B$ by some (arbitrary) individual constant. That is, (induction hypothesis) $B$ has the value $T$ for every individual $x$ of $I$; therefore $A$ has the value $T$ and the lemma is established in this case. If, on the other hand, we do not have $\Gamma_\omega \vdash (x)B$, then $\Gamma_\omega \vdash (x)B \supset f$ whence (by 9, I) $\Gamma_\omega \vdash (\exists x)(B \supset f)$. Hence, by property (ii) of $\Gamma_\omega$, for some individual constant $u_{ij}$ we have $\Gamma_\omega \vdash B' \supset f$, where $B'$ is obtained from $B$ by replacing each free occurrence of $x$ by $u_{ij}$. Hence for this $u_{ij}$ we cannot have $\Gamma_\omega \vdash B'$ else $\Gamma_\omega \vdash f$ by I contrary to the fact that $\Gamma_\omega$ is consistent (property (i)). That is, by induction hypothesis, $B$ has the value $F$ for at least the one individual $u_{ij}$ of $I$ and so $(x)B$ has the value $F$ as asserted by the lemma for this case.

### Conclusion of the Proof

This concludes the inductive proof of the lemma. In particular the formulas of $\Gamma_\omega$ all have the value $T$ for our assignment and so are simultaneously satisfiable in the denumerable domain $I$. Since the formulas of $\Delta$ are included among those of $\Gamma_\omega$ our theorem is proved for the case of a system $S_0$ whose primitive symbols are denumerable.

### The General Case

To modify the proof in the case of an arbitrary system $S_0$ it is only necessary to replace the set of symbols $u_{ij}$ by symbols $u_{\alpha j}$, where $i$ ranges over the positive integers as before but $\alpha$ ranges over a set with the same cardinal number as the set of primitive symbols of $S_0$; and to fix on some particular well-ordering of the formulas of the new $S_\omega$ in place of the standard enumeration employed above. (Of course the axiom of choice must be used in this connection.)

## Corollaries

The completeness of the system $S_0$ is an immediate consequence of our theorem.

**COROLLARY 1:** *If $A$ is a valid wff of $S_0$ then $\vdash A$.*

First consider the case where $A$ is a cwff. Since $A$ is valid $A \supset f$ has the value $F$ for any assignment with respect to any domain; i.e., $A \supset f$ is not satisfiable. By our theorem it is therefore inconsistent: $A \supset f \vdash f$. Hence $\vdash A \supset f \supset f$ by III and $\vdash A$ by 3 and I.

The case of wff $A'$ which contains some free occurrence of an individual variable may be reduced to the case of the cwff $A$ (the closure of $A'$) obtained by prefixing to $A'$ universal quantifiers with respect to each individual variable with free occurrences in $A'$ (in the order in which they appear). For it is clear from the definition of validity that if $A'$ is valid so is $A$. But then $\vdash A$. From which we may infer $\vdash A'$ by successive applications of 5 and I.

**COROLLARY 2:** *Let $S_0$ be a functional calculus of first order and $\mathfrak{m}$ the cardinal number of the set of its primitive symbols. If $\Delta$ is a set of cwffs which is simultaneously satisfiable then in particular $\Delta$ is simultaneously satisfiable in some domain of cardinal $\mathfrak{m}$.*

This is an immediate consequence of our theorem and the fact that if $\Delta$ is simultaneously satisfiable it must also be consistent (since rules of inference preserve the property of having the value $T$ for any particular assignment in any domain, and so could not lead to the formula $f$). For the special case where $\mathfrak{m}$ is $\aleph_0$ this corollary is the well-known Skolem--Lowenheim result (5). It should be noticed, for this case, that the assertion of a set of cwffs $\Delta$ can no more compel a domain to be finite than non-denumerably infinite: there is always a denumerably infinite domain available. There are also always domains of any cardinality greater than $\aleph_0$ in which a consistent set $\Delta$ is simultaneously satisfiable, and sometimes finite domains. However for certain $\Delta$ no finite domain will do.

## Equality

Along with the truth functions of propositional calculus and quantification with respect to individual variables the first-order functional calculus is sometimes formulated so as to include the notion of equality as between individuals. Formally this may be accomplished by singling out some functional constant of degree 2, say $Q$, abbreviating $Q(x, y)$ as $x = y$ (for individual symbols $x$, $y$), and adding the axiom schemata

**E1.** $x = x$

**E2.** $x = y \supset {.}\; A \supset B$, where $B$ is obtained from $A$ by replacing some free occurrence of $x$ by a free occurrence of $y$.

For a system $S_0$ of this kind our theorem holds if we replace "the same cardinal number as" by "a cardinal number not greater than," where the definition of "simultaneously satisfiable" must be supplemented by the provision that the symbol "$=$" shall denote the relation of equality between individuals.

To prove this we notice that a set of cwffs $\Delta$ in the system $S_0$ may be regarded as a set of cwffs $(\Delta, E_1, E_2)$ in the system $S_0'$, where $E_1$ is the set of closures of axioms E1 ($i = 1, 2$). Since $E_1, E_2 \vdash x = y \supset y = x$ and $E_1, E_2 \vdash x = y \supset {.}\; y = z \supset x = z$ we see that the assignment which gives a value $T$ to each formula of $\Delta, E_1, E_2$ must assign some equivalence relation to the functional symbol $Q$. If we take the domain $I'$ of equivalence classes determined by this relation over the original domain $I$ of constants, and assign to each individual constant (as denotation) the class determined by itself, we are led to a new assignment which is easily seen to satisfy $\Delta$ (simultaneously) in $S_0'$.

## Models and Cardinality

A set of wffs may be thought of as a set of axioms determining certain domains as models; namely, domains in which the wffs are simultaneously satisfiable. For a first-order calculus containing the notion of equality we can find axiom sets which restrict models to be finite, unlike the situation for calculi without equality. More specifically, given any finite set of finite numbers there exist axiom sets whose models are precisely those domains in which the number of individuals is one of the elements of the given set. (For example, if the set of numbers is the pair $(1, 3)$ the single axiom

$$(x)(y)(x = y) \;\lor\; (\exists x)(\exists y)(\exists z)\big[\neg(x = y) \land \neg(x = z) \land \neg(y = z) \land (t)(t = x \lor t = y \lor t = z)\big]$$

will suffice, where $A \land B$, $A \lor B$ abbreviate $\neg(A \supset \neg B)$, $A \supset B \supset B$ respectively.) However, an axiom set which has models of arbitrarily large finite cardinality must also possess an infinite model as one sees by considering the formulas

$$C_i: \quad (\exists x_1)(\exists x_2)\cdots(\exists x_i)\big[\neg(x_1 = x_2) \land \neg(x_1 = x_3) \land \cdots \land \neg(x_{i-1} = x_i)\big].$$

Since by hypothesis any finite number of the $C_i$ are simultaneously satisfiable they are consistent. Hence all the $C_i$ are consistent and so simultaneously satisfiable---which can happen only in an infinite domain of individuals.

There are axiom sets with no finite models---namely, the set of all formulas $C_i$ defined above. Every axiom set with an infinite model has models with arbitrary infinite cardinality. For if $\alpha$, $\beta$ range over any set whatever the set of all formulas $\neg(x_\alpha = x_\beta)$ for distinct $\alpha$, $\beta$ will be consistent (since the assumption of an infinite model guarantees consistency for any finite set of these formulas) and so can be simultaneously satisfied.

## Propositional Calculus

In simplified form the proof of our theorem and corollary 1 may be carried out for the propositional calculus. For this system the symbols $u_{ij}$ and the construction of $S_\omega$ may be omitted, an assignment of values being made directly from $\Gamma_0$. While such a proof of the completeness of the propositional calculus is short compared with other proofs in the literature the latter are to be preferred since they furnish a constructive method for finding a formal proof of any given tautology, rather than merely demonstrate its existence.

## Bibliography

1. QUINE, W. V., *Completeness of the propositional calculus*, The Journal of Symbolic Logic, vol. 3 (1938), pp. 37--40.

2. GODEL, KURT, *Die Vollstandigkeit der Axiome des logischen Funktionenkalkuls*, Monatshefte fur Mathematik und Physik, vol. 37 (1930), pp. 349--360.

3. TARSKI, ALFRED, *Der Wahrheitsbegriff in den Formalisierten Sprachen*, Studia Philosophica, vol. 1 (1936), pp. 261--405.

4. CHURCH, ALONZO, *Introduction to Mathematical Logic, Part I*, Annals of Mathematics Studies, Princeton University Press, 1944.

5. SKOLEM, TH., *Uber einige Grundlagenfragen der Mathematik*, Skrifter utgitt av Det Norske Videnskaps-Akademi i Oslo, 1929, no. 4.

---

*Princeton University*
