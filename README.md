### Building JonPRL

JonPRL uses SML/NJ's [CM](http://www.smlnj.org/doc/CM/) for its build, and
[Smackage](https://github.com/standardml/smackage) for its dependencies.
(JonPRL is likely compatible with other SML implementations, but I currently
rely on CM and don't have the engineering bandwidth to test it with other
implementations and build systems.)

First make sure you have SML/NJ and Smackage set up properly. Then, install
JonPRL's dependencies:

```sh
smackage get parcom
```

Finally, JonPRL may be built through the SML/NJ top-level as follows:

```
rlwrap sml
> CM.make "sources.cm";
```

Currently the only interface to JonPRL is as a library; the `Test` module
currently demonstrates how to interact with JonPRL, and is automatically
executed when `CM.make "sources.cm"` is called.

In the future, a proper top-level interface to JonPRL is of course desired, and
a Makefile for constructing binaries should be added.


### The PRL Tradition

JonPRL is a proof refinement logic in the sense of λ-PRL or
[Nuprl](http://www.nuprl.org); JonPRL inherits its [computational type
theory](http://www.sciencedirect.com/science/article/pii/S1570868305000704)
from Allen, Bickford, Constable, Harper and many other names.


#### CTT

CTT is a version of Martin-Löf's extensional type theory which has been heavily
modified in order to be suitable for use in refinement-based proof assistants.
Finally, Nuprl and JonPRL employ a proof refinement theory which has its
semantics in CTT, but which is arranged to support the economical construction
of *derivations*.

The primary differences between CTT and ETT are as follows:

1. ETT has four categorical judgements: `A type`, `A = B type`, `M ∈ A` and
`M = N ∈ A`; CTT has only one categorical judgement, which is `M = N ∈ A`.
`A = B type` is recovered as equality in a universe, and `M in A` is recovered as
an abbreviation for `M = M ∈ A`.

2. The semantics of presuppositions is different. In ETT, the presuppositions
of a judgement must be satisfied in addition to the meaning of the
judgement; in CTT, a derived judgement is considered evident *if* its
presuppositions are also evident. An example is the meaning of the sequent
`x:A >> B(x) type` (`B` is a family fibred over `A`): in ETT, you must
demonstrate `A type`, and then you must demonstrate `|x B(x) type (x in A)`. In
CTT, however, the meaning of the sequent does not include the presupposition at
all, and the rules are carefully arranged in order that the "moral"
presuppositions shall be satisfied *in the course of* demonstrating the
evidence of a judgement.

In practice, this means that where Martin-Löf's meaning explanation readily
justifies a rule like `M ∈ A ===> inl(M) ∈ A + B`, in CTT it would be necessary
to give an additional premise, `M ∈ A ; B type ===> inl(M) ∈ A + B`.

Why is CTT's meaning explanation arranged in this way, when the one for ETT is
evidently better factored and more modular? The simple reason is that it makes
the derivations smaller and less tedious. For instance, in order to cause the
rule in the previous paragraph to be evident, assuming that `A type` is known,
one still has to demonstrate the presupposition `A + B type`, whereas in the
CTT version it is only necessary to demonstrate `B type`. It may not seem like
a big deal here, but in general, CTT's meaning explanation is more practical
for refinement-based proof.


#### The Refinement Logic

CTT is the underlying type theory and semantics of the refinement logic
employed in Nuprl and JonPRL. However, the refinement logic has only one form
of judgement: `H >> A [ext M]`, where `H,A` are inputs (in the sense of the
mode of a judgement), and `M` is an output. The judgement is pronounced, "`H`
entails the truth of `A`, with extract `M`".

Then, in the refinement logic it is not possible to access the categorical
judgements of CTT. Rather than constructing a witness to a proposition, you are
causing the truth of a proposition to become evident: this judgement is
essentially a functional, hypothetico-general assertion of truth. In parallel
with a derivation of truth, an extract term `M` is incrementally constructed;
the meaning explanation for the refinement logic entails that `H >> M ∈ A`
whenever `H >> A [ext M]`.

#### Propositional Equality

It is still possible to prove membership and equality in the refinement logic,
even though the categorical judgements are inaccessible. In order to do this,
an equality type is introduced, whose *truth* is defined specifically so as to
coincide with the (mere) evidence of the equality judgement. In practice, you
will often see goals like `H >> M in A [ext •]`, and in this case you are
proving the proposition `M in A` (which is an abbreviation for `M = M in A`).
Based on the meaning explanation for the refinement logic, you are indirectly
causing the categorical equality judgement of CTT to become evident.


#### Clarification of "Equality Reflection"

It is *not the case* that CTT (or even ETT) contains some special "equality
reflection" rule which allows propositional equalities to leak into the
judgemental equality. When Martin-Löf mentioned this rule in 1979, it was not
as a defining factor of the theory, but rather as an *admissible rule* which is
immediate under the meaning explanations and the definitions of the types. The
judgemental equality comes first in ETT (and CTT), and it contains the true,
typical equality for each type (this is part of the definition of each type);
then, the propositional equality is defined in terms of the judgemental
equality.

It would make no sense to define the judgemental equality in terms of the
propositional equality, since the judgements are prior to the types! Martin-Löf
never intended this, but that did not stop many people from coming under the
impression that ETT was somehow distinguished from later type theories by the
addition or removal of the equality reflection rule. Rather, the difference
between ETT and other theories is the *meaning explanation*, which causes the
equality reflection rule to be evident (or not).

