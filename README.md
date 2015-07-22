JonPRL is a proof refinement logic in the sense of λ-PRL or
[Nuprl](http://www.nuprl.org); JonPRL inherits its [computational type
theory](http://www.sciencedirect.com/science/article/pii/S1570868305000704)
from Constable, Bates, Harper, Allen, Bickford, Howe, Smith and many other names. Computational Type Theory is based on a meaning explanation similar to the ones which Martin-Löf introduced in 1979, to which I have written a self-contained introduction, [Type Theory and its Meaning Explanations](http://www.jonmsterling.com/pdfs/meaning-explanations.pdf).

### Discussion and Questions ###

There is an IRC channel on freenode at #jonprl.

### Building & Installing JonPRL

JonPRL uses SML/NJ's [CM](http://www.smlnj.org/doc/CM/) for its build.  First
make sure you have SML/NJ set up properly. Then, install JonPRL's dependencies:

```sh
git submodule update --init --recursive
```

Then, JonPRL may be built using its `Makefile`:

```sh
make smlnj
make test
```

This puts a binary in `./bin/jonprl`. Optionally, you may install JonPRL globally using:

```sh
sudo make install
```

### Running JonPRL

To run JonPRL, simply direct it at your development:

```sh
jonprl example/test.jonprl
```

You may specify as many files as you like in this command; they will be refined
in order, in case of any dependencies.

#### Emacs Mode

Optionally, you may install the [JonPRL Mode for
Emacs](https://github.com/david-christiansen/jonprl-mode).

If you use `pretty-mode`, then you may install the following patterns:

```elisp
(pretty-add-keywords
 'jonprl-mode
 '(("\\\[" . "⸤")
   ("\\\]" . "⸥")
   ("<" . "⟨")
   (">" . "⟩")
   ("<>" . "★")
   ("\\<isect\\>" . "⋂")
   ("\\<fun\\>" . "Π")
   ("\\<prod\\>" . "Σ")
   ("\\<member\\>" . "∈")
   ("\\<lam\\>" . "λ")
   ("\\<\\(=def=\\)\\>" . "≝")
   ("\\<\\(nat\\)\\>" . "ℕ")
   ))
```

![screenshot of jonprl-mode](./doc/images/jonprl-screenshot.png)

### Basic Syntax

JonPRL has a two-level syntax. There is the syntax of terms in the underlying
lambda calculus (the object language) and the syntax of tactics and definitions
in the metalanguage. Terms from the underlying lambda calculus are embedded
into the metalanguage using brackets (`[` and `]`). When referring to names
from the object language in the metalanguage, they are quoted in angle brackets
(`<` and `>`).

The syntax of the object language represents all binders in a
consistent manner. The variables to be bound in a subterm are written
before it with a dot. For example, the identity function is written
`λ(x.x)` where the first `x` indicates the bound name and the second
refers back to it, and the first projection of a pair `P` is written
`spread(P; x.y.x)`. The semicolon separates arguments to `spread`.

### Top-level declarations

JonPRL provides four top-level declarations:

 * `Operator` gives the binding structure of a new operator.
 * `=def=` defines the meaning of an operator in terms of the existing operators.
 * `Theorem` declares a theorem, and allows it to be proven.
 * `Tactic` defines a tactic in terms of the built-in tactics.

### Built-in operators

Together with the syntax for binding trees, the built-in operators of
JonPRL constitute the core type theory, in combination with the rules
for CTT which are built into JonPRL's refiner. In this section, several of the
operators is presented together with its arity and a brief informal
description. An arity is a list of the valences of an operator's subterms;
*valence* is the number of variables to bind.

| abstract form   | concrete form         | description                                     |
|-----------------|-----------------------|-------------------------------------------------|
| `unit()`        | `unit`                | The unit type                                   |
| `<>()`          | `<>`                  | The trivial inhabitant of `unit`                |
| `fun(0;1)`      | `(x:A) B`, `A -> B`   | The dependent function type                     |
| `lam(1)`        | `lam(x.E)`            | The lambda abstraction                          |
| `ap(0;0)`       | `M N`                 | Function application                            |
| `isect(0;1)`    | `{x:A} B`, `A => B`   | The family intersection type                    |
| `prod(0;1)`     | `(x:A) * B`, `A * B`  | The dependent pair type                         |
| `pair(0;0)`     | `<M,N>`               | The pair operator                               |
| `spread(0;2)`   | `spread(M; x.y.E)`    | Pattern matching for pairs                      |
| `subset(0;1)`   | `{x:A | B}`           | The set comprehension type                      |
| `+(0;0)`        | `+(A;B)`              | The disjoint union type                         |
| `inl(0)`        | `inl(M)`              | The left union introduction form                |
| `inr(0)`        | `inr(M)`              | The right union introduction form               |
| `decide(0;1;1)` | `decide(M; l.E; r.F)` | Pattern matching for disjoint unions            |
| `void()`        | `void`                | The empty type                                  |
| `=(0;0;0)`      | `=(M;N;A)`            | The equality type (`M,N` are equal at type `A`) |
| `member(0;0)`   | `member(M;A)`         | The membership type (`M` is a member of `A`)    |


#### Second-order variables

Unlike some other implementations of type theory that use the same
syntax for function application and filling in second-order variables,
JonPRL's second-order variables must be applied using the
`so_apply(0;0)` operator.

As an example, unique existence might be defined as follows:
```
Operator ex_uni : (0;1).

[ex_uni(T;P)] =def= [(x:T) * so_apply(P;x) * {y:T} so_apply(P;y) => =(x;y;T)].
```

Note that `P` is applied to `x` and `y` using `so_apply` rather than
`ap`, which is reserved for function application.

#### Computational Equivalence

The elements of `base()` are all closed terms. Their equality is `ceq(0;0)`,
which denotes [Howe's computational
equivalence](http://www.nuprl.org/KB/show.php?ShowPub=Howe89). Two terms are
computationally equivalent if they both diverge or if they run to equivalent
results. Computational equivalence is a congruence, which means that one can
also prove that two terms are computationally equivalent if their subterms are
computationally equivalent.
