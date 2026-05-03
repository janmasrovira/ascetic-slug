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

| Name        | errors   | consumes | Reading                           |
|-------------|----------|----------|-----------------------------------|
| pure        | never    | never    | always succeeds, no input read    |
| lookahead   | possibly | never    | may fail, no consumption          |
| flexible    | never    | possibly | infallible, may consume           |
| fallible    | possibly | possibly | the most permissive grade         |
| conditional | possibly | always   | may fail, must consume on success |
| empty       | always   | never    | always fails                      |
| impossible  | never    | always   | uninhabited                       |

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

We just saw how grades multiply when parsers run in sequence. That's what
`bind` does, and `pure` carries the unit grade. With `g g' : Grade`:

```lean
def gpure : α → Parser .pure α  -- .pure = ⟨never, never⟩, the monoid unit
def gbind : Parser g α → (α → Parser g' β) → Parser (g * g') β
```

This is a *graded monad* ([Katsumata's parametric effect monads][katsumata]). In
the table below we compare the signatures of standard monadic operations with
graded monadic operations.

| Standard Monad                | Graded Monad                              |
|-------------------------------|-------------------------------------------|
| pure  : α → m α               | gpure : α → m 1 α                         |
| bind  : m α → (α → m β) → m β | gbind : m i α → (α → m j β) → m (i * j) β |

prim-parser provides `GFunctor`, `GApplicative`, `GMonad`, and `LawfulGMonad`
typeclasses for the graded shape. I've proved the functor, applicative, and
monad laws for `Parser` as Lean theorems. With `i j k : Grade`, the two
sides of each `=` carry different grade indices syntactically; they unify
only after we prove the grade identity in the right column, and those
identities follow from the monoid laws on `Grade`:

| Property      | Equation                              | Grade equation            |
|---------------|---------------------------------------|---------------------------|
| Left unit     | gpure x >>= f = f x                   | 1 * j = j                 |
| Right unit    | m >>= gpure = m                       | i * 1 = i                 |
| Associativity | (m >>= f) >>= g = m >>= λa. f a >>= g | (i * j) * k = i * (j * k) |

[katsumata]: https://dl.acm.org/doi/10.1145/2535838.2535846

# Combinators

A tour of the combinators (`fix` has its own section). By the end of the tour I
hope you'll see that grades do more than enforce totality; they also help
document the combinator's behaviour in the type.

---

**`anyChar`** consumes and returns a single character, or fails if the
input is empty:

```lean
anyChar : Parser .conditional Char  -- .conditional = ⟨possibly, always⟩
```

It may fail (on empty input) and always consumes on success.

---

**`lookahead`** runs `p` but never consumes:

```lean
lookahead : Parser ⟨ge, gc⟩ α → Parser ⟨ge, .never⟩ α
```

The error grade is preserved; the consumption grade is set to `.never`.

---

**`notFollowedBy`** succeeds exactly when `p` fails, without consuming:

```lean
notFollowedBy : Parser ⟨ge, gc⟩ α → Parser ⟨ge.complement, .never⟩ PUnit
```

`complement` is a `Necessity` operation defined like this:

```
complement never    = always
complement possibly = possibly
complement always   = never
```

If `p` always fails, `notFollowedBy p` never fails; if `p` never fails,
`notFollowedBy p` always fails. In short, the error grade flips.

---

**`many`** applies a parser zero or more times, collecting results:

```lean
many : Parser ⟨ge, .always⟩ α → Parser .flexible (List α)
```

The argument must always consume (otherwise recursion wouldn't terminate);
the result is `.flexible` (never fails, may consume) because zero
repetitions is allowed.

---

**`many1`** is `many` with at least one repetition. The argument's grade is
preserved exactly:

```lean
many1 : Parser ⟨ge, .always⟩ α → Parser ⟨ge, .always⟩ (NonEmptyList α)
```

---

**`optional`** tries `p`; on failure, returns `none`. The result never
fails:

```lean
optional : Parser ⟨ge, gc⟩ α → Parser ⟨.never, ge.complement ⊓ gc⟩ (Option α)
```

`optional p` only consumes input when `p` succeeds. `ge.complement` flips the
error grade to capture how often that happens. Thatis, `never` if `p` always
fails, `always` if `p` never fails. Taking the meet (`⊓`, min) with `gc` caps
that by what `p` consumes when it succeeds.

---

**`choice`** tries the first parser; on failure, the second. The error
grade is `ge ⊓ ge'` (the combined parser only always-fails if both
branches do); the consumption grade uses a small ternary helper:

```lean
abbrev ite (sel a b : Necessity) : Necessity :=
  (a ⊓ b) ⊔ sel ⊓ a ⊔ sel.complement ⊓ b

choice : Parser ⟨ge, gc⟩ α → Parser ⟨ge', gc'⟩ α
       → Parser ⟨ge ⊓ ge', ge.ite gc' gc⟩ α
```

`ge.ite gc' gc` cases on the first branch's failure pattern:

- first branch never fails → second is unreachable, so consumption is `gc`.
- first branch always fails → only the second runs, so consumption is `gc'`.
- first branch may fail → both can run, so consumption is what they agree
  on (`possibly` if they disagree).

---

**`oneOf`** generalises `choice` to a non-empty list of parsers sharing a
grade:

```lean
oneOf : NonEmptyList (Parser g α) → Parser g α
```

---

**`count`** parses exactly `n` occurrences, returning a length-indexed
vector. Both grade components are relaxed to `.possibly`, since `count 0 p`
succeeds without consuming:

```lean
count : (n : Nat) → Parser ⟨ge, gc⟩ α
      → Parser ⟨ge ⊓ .possibly, gc ⊓ .possibly⟩ (Vector α n)
```

---

**`count1`** is the specialisation to `n + 1`. With at least one repetition
guaranteed, the argument's grade is preserved exactly:

```lean
count1 : (n : Nat) → Parser ⟨ge, gc⟩ α
       → Parser ⟨ge, gc⟩ (Vector α (n + 1))
```

---

**`sepBy`** parses zero or more occurrences of `p` separated by `sep`:

```lean
sepBy : (sep : Parser ⟨ge', gc'⟩ β) → (p : Parser ⟨ge, gc⟩ α)
      → gc' ⊔ gc = .always
      → Parser .flexible (List α)
```

In agdarsec each individual parser must consume. Here the separator and
the element only need to consume *together*: you can have an empty
separator with a consuming element, or vice versa.

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

# Examples

Before the examples, a note on `do`-notation. Lean's built-in `do` does not
type-check on graded monads: `do` assumes a fixed monad, but every `←`
shifts the surrounding grade by `*`. The library provides a `gdo` macro that
desugars to chained `gbind`s and emits a `grade_by` proof obligation for the
residual grade equation. In practice `by simp` discharges almost everything,
because the monoid laws are registered as `simp` lemmas. You'll see `gdo`
and `grade_by` throughout the examples below.

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
(with operator precedence), JSON, and the untyped lambda
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
- **Split out graded monads.** The `GFunctor` / `GApplicative` / `GMonad`
  hierarchy and their lawful counterparts have nothing to do with parsers;
  they belong either in mathlib or in their own library.
