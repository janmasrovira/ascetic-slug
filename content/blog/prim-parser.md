+++
title = "Total parser combinators with graded monads"
date = 2026-05-03

[taxonomies]
tags=["Lean", "formal verification"]

[extra]
toc = true
+++

In this blog I present
[prim-parser](https://github.com/janmasrovira/prim-parser), a Lean 4 *total*
monadic parser combinator library in the spirit of
[parsec](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/parsec-paper-letter.pdf).
To ensure totality, every parser carries a *grade* in its type recording whether
it *may*, *must*, or *cannot* consume input, and whether it *may*, *must*, or
*cannot* fail. The resulting Parser type is a graded
monad. The choice operator is biased like in `parsec`/`megaparsec`; and the
graded monad laws are proved in Lean as propositional equalities. No prior total
parser combinator library combines these.

# Introduction

Monadic parser combinators are a popular tool in functional
programming. A small set of higher-order functions and do-notation is enough to
assemble parsers for complex grammars, and since parsers are ordinary values in
the host language, you get its abstractions and familiar syntax.

A typical example is parsing an identifier: a letter followed by alphanumeric
characters:

```lean
def ident : Parser String := do
  let c ← letter
  let cs ← many alphanum
  return String.ofList (c :: cs)
```

`many` is itself a recursive parser. The natural definition is something
like:

```lean
def many (p : Parser α) : Parser (List α) := do
  let m ← optional p
  match m with
    | some x => List.cons x <$> many p
    | none   => return []
```

The definition of `many` fails Lean's termination check because it calls itself
on the same input, so there is no structurally decreasing argument. Two obvious
options that may come to mind: bound the number of recursive calls, or mark the
definition `partial` and skip the check (what
[`lean4-parser`](https://github.com/fpvandoorn/lean4-parser) does). Neither is
satisfying. The first is too
restrictive because there may not be a safe bound to pick. The second drops the
totality guarantee (if `p` accepts the empty string, `many p` loops forever).

There are other total parser libraries:
[`agdarsec`](https://gitlab.com/gallais/agdarsec) and
[Danielsson 2010](https://dl.acm.org/doi/10.1145/1863543.1863585). I'll comment on them in the [Related work](#related-work) section.

For a preview, here is `many`'s signature in prim-parser:

<pre><code>def many (p : Parser ε ⟨ge, <span style="color: #1e6fcc; font-weight: bold">always</span>⟩ α) : Parser ε ⟨<span style="color: #c0392b; font-weight: bold">never</span>, <span style="color: #d97706; font-weight: bold">possibly</span>⟩ (List α)
</code></pre>

Read each grade as a pair: the left component tracks *errors*, the right component tracks
*consumption*. The key fact is the
<span style="color: #1e6fcc; font-weight: bold">always</span> in `p`'s grade:
`p` is guaranteed to consume input on every success, and that is what makes
the recursion safe. The `ge` on the left is unconstrained. The result grade
⟨<span style="color: #c0392b; font-weight: bold">never</span>,
<span style="color: #d97706; font-weight: bold">possibly</span>⟩
says `many p` itself never fails and may or may not consume input. Each parser
type carries a *grade* of this kind, and that is what we define next.

# The grade

We need to track two pieces of static information about a parser:

1. **Errors.** Does it ever fail?
2. **Consumption.** Does it ever consume input?

Each axis admits three answers: `never`, `possibly`, `always`.
```lean
inductive Necessity where
  | never
  | possibly
  | always
```

We order them `never < possibly < always`, so `⊔` is `max` over this order.

A `Grade` is just a pair:

```lean
structure Grade where
  errors   : Necessity
  consumes : Necessity
```

There are nine grades; seven of them are useful to name:

| Name          | errors     | consumes   | Reading                           |
|---------------|------------|------------|-----------------------------------|
| `pure`        | `never`    | `never`    | always succeeds, no input read    |
| `lookahead`   | `possibly` | `never`    | may fail, no consumption          |
| `flexible`    | `never`    | `possibly` | infallible, may consume           |
| `fallible`    | `possibly` | `possibly` | the most permissive grade         |
| `conditional` | `possibly` | `always`   | may fail, must consume on success |
| `empty`       | `always`   | `never`    | always fails                      |
| `impossible`  | `never`    | `always`   | uninhabited                       |

`Grade` is a monoid: the operation is componentwise `⊔` (sup) and the unit
is `⟨never, never⟩`. I'll write `g * g'` for the monoid product; in this
post that's the same as `g ⊔ g'`.

This is how grades combine when one parser runs after another. For example,
first a parser that never fails and may consume, then one that may fail and
always consumes:

```
⟨never, possibly⟩ * ⟨possibly, always⟩
  = ⟨never ⊔ possibly, possibly ⊔ always⟩
  = ⟨possibly, always⟩
```

The result may fail (the second parser might) and always consumes (the
second parser does).

The two unnamed grades (`⟨always, possibly⟩` and `⟨always, always⟩`)
describe parsers that always fail; the consumption component is irrelevant
when the result is always an error. I keep them so the monoid product is
closed on `Grade`.

# Graded monad

Given a parser `p : Parser ε g₁ α` and a continuation
`f : α → Parser ε g₂ β`, what is the grade of `bind p f`? Either step can
fail, and either step can consume — so the result has grade `g₁ * g₂`.

That means the right type for bind is

```lean
def bind : Parser ε g α → (α → Parser ε g' β) → Parser ε (g * g') β
```

This is the signature of a *graded* monad — Katsumata's parametric effect
monads — not an ordinary one. The graded operations carry a monoidal index;
specialising the index to the trivial monoid recovers the standard
operations:

| Standard                                  | Graded                                                    |
|-------------------------------------------|-----------------------------------------------------------|
| `pure  : α → m α`                         | `gpure : α → m 1 α`                                       |
| `seq   : m (α → β) → m α → m β`           | `gseq  : m i (α → β) → m j α → m (i · j) β`               |
| `bind  : m α → (α → m β) → m β`           | `gbind : m i α → (α → m j β) → m (i · j) β`               |

The library defines `GFunctor`, `GApplicative`, and `GMonad` typeclasses
following this pattern, and proves that `Parser` is a *lawful* instance of
each: `LawfulGMonad` is a Lean theorem, not a comment in a docstring.

The cost of being graded rather than ordinary is that Lean's built-in `do`
notation does not type-check — every `←` would change the surrounding grade.
The library ships a `gdo` macro that desugars to chained `gbind`s and emits a
`grade_by` proof obligation at the end so the user can discharge any
residual grade equation:

```lean
let plist : Parser Error .conditional SExp := gdo
  lexeme (char '(')
  let first ← sexp_rec
  let rest  ← many (gdo whitespace; sexp_rec)
  lexeme (char ')')
  return listToPairs (first :: rest)
  grade_by by simp
```

In practice, `grade_by by simp` discharges almost everything, because the
monoid laws are registered as `simp` lemmas.

# The Parser type

`Text n` is `List.Vector Char n` — a string whose length is known statically.
A parser is parameterised by an error type `ε`, a grade `g`, and a result
type `α`:

```lean
structure Parser (ε : Type) (g : Grade) (α : Type) where
  run : ∀ {n}, Text n → Outcome ε n g α
```

The result type is *computed* from the error grade — a small bit of
type-level pattern matching that pays off:

```lean
abbrev Outcome (ε : Type) (n : Nat) (g : Grade) (α : Type) :=
  match g.errors with
  | .never    => Success n g.consumes α
  | .possibly => ε ⊕ Success n g.consumes α
  | .always   => ε
```

An infallible parser has no `Sum` overhead at all; an always-failing parser
cannot even mention the success type. The success result carries a
*consumption witness* relating the input length and the leftover length:

```lean
abbrev consumptionWitness (rest n : Nat) : Necessity → Prop
  | .never    => rest = n
  | .possibly => rest ≤ n
  | .always   => rest < n
```

The `< n` case for `consumes = always` is the load-bearing fact: it makes the
input strictly decrease at every consuming step, which is what `fix` needs.

# Combinator types do real work

The grade-level algebra isn't decoration — it lets the types of combinators
say genuinely useful things about how they behave.

**`optional`** drops the error and gives back an `Option`. So far so
ordinary. But what's the consumption grade? If the inner parser always fails,
`optional` always returns `none`, so it consumes nothing. If it always
succeeds, the consumption is whatever the inner parser does. If it may fail,
consumption is conditional on success. The neat way to express this is with
the lattice operations:

```lean
optional : Parser ε ⟨ge, gc⟩ α → Parser ε ⟨.never, ge.complement ⊓ gc⟩ (Option α)
```

`ge.complement ⊓ gc` reads "however often the parser *doesn't* fail, capped by however
much the inner parser consumes". When `ge = always`, `complement` is
`never`, so the meet is `never` — no consumption. When `ge = never`,
`complement` is `always`, so the meet is just `gc`. The middle case takes
care of itself.

**`notFollowedBy`** uses `complement` similarly:

```lean
notFollowedBy : Parser ε ⟨ge, gc⟩ α → Parser ε ⟨ge.complement, .never⟩ PUnit
```

A parser that always fails turns into one that never fails; consumption is
zeroed out.

**`choice`** is the most interesting case. The error grade is `ge ⊓ ge'`
(the combined parser only always fails if both branches do), and the
consumption grade is computed by an `ite` indexed by the first branch's
error grade:

```lean
choice : Parser ε ⟨ge, gc⟩ α → Parser ε ⟨ge', gc'⟩ α
       → Parser ε ⟨ge ⊓ ge', ge.ite gc' gc⟩ α
```

If the first branch is infallible, the second is unreachable, so consumption
is `gc`. If the first always fails, consumption is `gc'`. If the first may
fail, consumption is whatever both agree on, falling back to `possibly`
otherwise. That's exactly what `ite` computes:

```lean
abbrev ite (sel a b : Necessity) : Necessity :=
  (a ⊓ b) ⊔ sel ⊓ a ⊔ sel.complement ⊓ b
```

**`sepBy`** is more permissive than `agdarsec`'s analogue:

```lean
sepBy : (sep : Parser ε ⟨ge', gc'⟩ β) → (p : Parser ε ⟨ge, gc⟩ α)
      → gc' ⊔ gc = .always
      → Parser ε .flexible (List α)
```

In `agdarsec` each individual parser must consume; here, the separator and
the element only need to consume *together*. So you can have an empty
separator combined with a consuming element, or vice versa.

# Termination via `fix`

`fix` is where the consumption grade pays for itself:

```lean
def fix [Inhabited ε]
  (f : Parser ε ⟨ge, .always⟩ α → Parser ε ⟨ge, .always⟩ α)
  (h : .possibly ≤ ge := by simp)
  : Parser ε ⟨ge, .always⟩ α
```

The body is a function `recParser → recParser` whose grade has `consumes =
.always`. Internally `fix` peels one character per recursive call, so
termination is structural on the input length:

```lean
let rec go {n} (t : Text n) : Outcome ε n ⟨ge, .always⟩ α :=
  match n, t with
  | 0,     _ => Outcome.throw default
  | n + 1, t =>
    let self : Parser ε ⟨ge, .always⟩ α :=
      ⟨fun {k} t' =>
        if k ≤ n then go t' else Outcome.throw default⟩
    f self |>.run t
```

If you try to call `fix` with a body that doesn't always consume, the type
just won't match. There is no fuel parameter, no `partial`, no manual
termination proof.

# Examples

## S-expressions

[*Source: `Examples/SExp.lean`*](https://github.com/janmasrovira/prim-parser/blob/bc8b8fb/Examples/SExp.lean)

Let's parse the usual Lispy syntax: alphanumeric atoms and parenthesised
lists, e.g.

```
hello
(a b)
(a b c)
(a (b c))
```

with non-empty lists folded into right-associative pairs: `(a b c)` parses to
`pair a (pair b c)`.:

```lean
inductive SExp where
  | atom (str : String)
  | pair (l r : SExp)

def patom : Parser Error .conditional SExp :=
  .atom <$>ᵍ takeWhile1 (·.isAlphanum)

def sexp : Parser Error .conditional SExp :=
  fix (fun sexp_rec =>
    let plist : Parser Error .conditional SExp := gdo
      lexeme (char '(')
      let first ← sexp_rec
      let rest  ← many (gdo whitespace; sexp_rec)
      lexeme (char ')')
      return listToPairs (first :: rest)
      grade_by by simp
    choice patom plist)
```

## CSV

[*Source: `Examples/Csv.lean`*](https://github.com/janmasrovira/prim-parser/blob/bc8b8fb/Examples/Csv.lean)

Let's parse a tiny subset of CSV: a header row of column names followed by
data rows whose cells are integers or strings, e.g.

```
name,age
Alice,30
Bob,25
```

The header determines the column count statically and every subsequent row is
required to have exactly that many fields.
```lean
inductive Value where
  | int (n : Int)
  | str (s : String)

structure Table (n : Nat) where
  columns : List.Vector String n
  rows    : List (List.Vector Value n)

def row : Parser Error .flexible (List String) :=
  sepBy comma field

def exactRow (n : Nat) : Parser Error .fallible (List.Vector Value n) :=
  sepByN comma cell n

def table : Parser Error .conditional ((n : Nat) × Table n) := gdo
  let headers ← row
  newline
  let n      := headers.length
  let rows   ← sepBy newline (exactRow n)
  let t : Table n := { columns := ⟨headers, rfl⟩, rows }
  return ⟨n, t⟩
```

The [`Examples/`](https://github.com/janmasrovira/prim-parser/tree/bc8b8fb/Examples)
directory has a few more parsers in the same style: arithmetic expressions
(with operator precedence via `chainl1`), JSON, and the untyped lambda
calculus.

# Related work

| Library                                                                  | Total | Monadic | Coinduction  |
|--------------------------------------------------------------------------|:-----:|:-------:|:------------:|
| [`agdarsec`](https://gitlab.com/gallais/agdarsec) (Agda)                 |   ✓   |    ✗    | not needed   |
| [Danielsson 2010](https://dl.acm.org/doi/10.1145/1863543.1863585) (Agda) |   ✓   |    ✓\*  | needed       |
| [`lean4-parser`](https://github.com/fpvandoorn/lean4-parser) (Lean)      |   ✗   |    ✓    | not needed   |
| [`prim-parser`](https://github.com/janmasrovira/prim-parser) (Lean)      |   ✓   |    ✓\*  | not needed   |

\* Neither library makes `Parser` an instance of the standard `Monad`
typeclass. prim-parser's `Parser` is a *graded* monad (`bind`'s grade index
changes with each step), and a `GMonad` instance with monad laws as
propositional equalities. Danielsson's `Parser` defines a `bind` and proves
the monad laws up to bag equality of parse results, but conditional
coinduction in `bind`'s argument types prevents any typeclass instance.

**[`agdarsec`](https://gitlab.com/gallais/agdarsec)** sidesteps the
termination problem by requiring every successful parse to *strictly* consume
input, with recursion structured by course-of-values induction through a
guarded modal operator `□`. The cost: `pure` cannot be given the type
`Parser`, so `Parser` is not a monad, do-notation is unavailable, and even
`many` cannot be defined — only `many1`. Code that would be a one-line
`do`-block in Haskell becomes a tangle of specialised combinators (`<&>`,
`<&?>`, `<?&>`, ...).

**[Danielsson 2010](https://dl.acm.org/doi/10.1145/1863543.1863585)** takes a
different route, using mixed induction and coinduction in a deep embedding.
Grammars are reified as data and parsed via Brzozowski derivatives, which
supports left recursion — something neither agdarsec nor prim-parser handle
directly. The cost is that the derivative-based backend is worst-case
exponential in input length (the paper itself acknowledges this with a
concrete witness: `p = fail >>= λ b → fail` has *n*th derivative `p | p | … | p`
with 2ⁿ choices). `bind` exists and the monad laws are proved, but only up
to bag equality of parse results; the conditional coinduction in `bind`'s
argument types prevents any typeclass instance, and `choice` is forced to be
symmetric rather than biased.

**[`lean4-parser`](https://github.com/fpvandoorn/lean4-parser)** is the
closest peer in Lean: a `parsec`-style library with a standard `Monad`
instance and `do`-notation. Termination is opted out of via `partial` for
unbounded iteration.

# What's left

- **Better error messages.** The error type is currently just `String`. The
  grade machinery is independent of the error representation, so swapping in
  a richer diagnostic ADT (with source positions and labelled expectations,
  `parsec`-style) is doable.
- **Generic input type.** The input is currently fixed to `List.Vector Char n`.
  Generalising to an arbitrary sized type is straightforward.
