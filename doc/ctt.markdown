### The PRL Tradition

JonPRL is a proof refinement logic in the sense of λ-PRL or
[Nuprl](http://www.nuprl.org); JonPRL inherits its [computational type
theory](http://www.sciencedirect.com/science/article/pii/S1570868305000704)
from the Nuprl Group.


#### CTT

CTT (computational type theory) is a version of Martin-Löf's extensional type
theory (ETT) which has been heavily modified in order to be suitable for use in
refinement-based proof assistants.  Finally, Nuprl and JonPRL employ a proof
refinement logic which has its semantics in CTT, but which is arranged to
support the economical construction of *derivations*.

The primary differences between CTT and ETT are as follows:

1. ETT has four categorical judgements: `A type`, `A = B type`, `M ∈ A` and
`M = N ∈ A`; CTT has only one categorical judgement, which is `M = N ∈ A`.
`A = B type` is recovered as equality in a universe, and `M ∈ A` is recovered as
an abbreviation for `M = M ∈ A`.

2. The meaning of equality of types is different. In ETT, types are
distinguished from terms via their categorical judgement, and their equality
is itself extensional (in the sense of the axiom of extensionality): two types
are equal when they have the same members and the same members are equal in
both types. In CTT, however, this not possible (or practical) for a number of
reasons, and the equality of types is intensional/structural.

3. The semantics of presuppositions is different. In ETT, the presuppositions
of a judgement must be satisfied in addition to the meaning of the
judgement; in CTT, the rules are arranged so as to cause the old
presuppositions to become evident by virtue of the evidence of a judgement. An
example is the meaning of the sequent `x:A >> B(x) type` (`B` is a family
fibred over `A`): in ETT, you must demonstrate `A type`, and then you must
demonstrate `|x B(x) type (x ∈ A)`. In CTT, however, the meaning of the
sequent does not include the presupposition at all, and the rules are carefully
arranged in order that the "moral" presuppositions shall be satisfied *in the
course of* demonstrating the evidence of a judgement.

JonPRL uses pointwise functionality, a surprising and non-standard semantics
for dependently-typed sequents which is convenient for untyped reasoning, but
challenges standard intuitions for the notion of a uniform family -- refuting,
in particular, the principle of dependent cut.

In practice, this means that where Martin-Löf's meaning explanation readily
justifies a rule like `M ∈ A ===> inl(M) ∈ A + B` (which would presuppose `A
type`, `A + B type`), in CTT it would be necessary to give an additional
premise, `M ∈ A ; B type ===> inl(M) ∈ A + B`.

Why is CTT's meaning explanation arranged in this way, when the one for ETT is
evidently better factored and more modular? The simple reason is that it makes
the derivations smaller and less tedious. For instance, in order to cause the
rule in the previous paragraph to be evident, one has to first demonstrate `A
type` and `A + B type` before proving the intended entailment, whereas in the
CTT version it is only necessary to demonstrate `B type` (and in CTT's
semantics, `A type` shall be evident in the conclusion by virtue of the
evidence of `M ∈ A`).


#### The Refinement Logic

CTT is the underlying type theory and semantics of the refinement logic
employed in Nuprl and JonPRL. However, the refinement logic has only one form
of judgement: `H >> A [ext M]`, where `H,A` are inputs (in the sense of the
mode of a judgement), and `M` is an output. The judgement is pronounced, "`H`
entails the truth of `A`, with extract `M`".

Then, in the refinement logic it is not possible to access the categorical
judgements of CTT. Rather than asserting that a term witnesses a proposition,
you are causing the truth of a proposition to become evident: this judgement is
essentially a functional, hypothetico-general assertion of truth. In parallel
with a derivation of truth, an extract term `M` is incrementally constructed;
the semantics for the refinement logic entails that `H >> M ∈ A` whenever
`H >> A [ext M]`.

#### Propositional Equality

It is still possible to prove membership and equality in the refinement logic,
even though the categorical judgements are inaccessible. In order to do this,
an equality type is introduced, whose *truth* is defined specifically so as to
coincide with the (mere) evidence of CTT's equality judgement. In practice, you
will often see goals like `H >> M in A [ext •]`, and in this case you are
proving the proposition `M in A` (which is an abbreviation for `M = M in A`).
Based on the meaning explanation for the refinement logic, you are indirectly
causing the categorical equality judgement of CTT to become evident.
