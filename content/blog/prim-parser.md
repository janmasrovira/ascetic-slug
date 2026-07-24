+++
title = "prim-parser: Total parser combinator library using a graded monad"
date = 2026-05-03

[taxonomies]
tags=["Lean", "formal verification"]

[extra]
toc = true
+++

In this post I present
[prim-parser](https://github.com/janmasrovira/prim-parser), a Lean 4 *total*
monadic parser combinator library in the
[parsec](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/parsec-paper-letter.pdf)
tradition. To the best of my knowledge, it is the first of its kind. To ensure
totality, every parser is tagged with a *grade* recording whether it *may*,
*must*, or *cannot* consume input, and whether it *may*, *must*, or *cannot*
fail; the Parser type is a graded monad over these grades. The graded monad laws
are proven as propositional equalities.

# Introduction {#introduction}

Monadic parser combinators are a popular tool in functional programming. With a
small set of functions called combinators and a monadic interface, you can
assemble parsers for complex grammars, and since parsers are ordinary values
in the host language, you get its abstractions and familiar syntax.

A typical example is parsing an identifier: a letter followed by alphanumeric
characters:

```lean
def ident : Parser String := do
  let c ← letter
  let cs ← many alphanum
  return String.ofList (c :: cs)
```

`many` is a combinator that parses zero or more occurrences of its argument. We
could define it like this:

```lean
def many (p : Parser α) : Parser (List α) := do
  let m ← optional p
  match m with
    | some x => List.cons x <$> many p
    | none   => return []
```

But the definition of `many` fails Lean's termination check because it calls
itself on the same input (in the `some x` branch), so there is no structurally
decreasing argument. Two obvious options that may come to mind: bound the number
of recursive calls, or mark the definition `partial` and skip the check (what
[lean4-parser](https://github.com/fgdorais/lean4-parser) does). Neither is
satisfying. The first is too restrictive because there may not be a safe bound
to pick. The second drops the totality guarantee (if `p` accepts the empty
string, `many p` loops forever). A better solution comes from enriching the type of
the parser. In prim-parser, every parser carries a *grade* in its type (a pair
tracking error and consumption behavior). Look at `many`'s signature:

<pre><code>def many (p : Parser ⟨ge, <span style="color: #1e6fcc; font-weight: bold">always</span>⟩ α) : Parser ⟨<span style="color: #c0392b; font-weight: bold">never</span>, <span style="color: #d97706; font-weight: bold">possibly</span>⟩ (List α)
</code></pre>

(The `Parser` type also takes an error-type parameter, which I omit until [The
Parser type](#the-parser-type) section.)

The left component tracks *errors*; the right tracks *consumption*. The key
fact is the
<span style="color: #1e6fcc; font-weight: bold">always</span> in `p`'s grade:
`p` is guaranteed to consume input on every success, and that is what makes
the recursion safe. The `ge` on the left is unconstrained. The result grade
⟨<span style="color: #c0392b; font-weight: bold">never</span>,
<span style="color: #d97706; font-weight: bold">possibly</span>⟩
says `many p` itself never fails and may or may not consume input. Each parser
type carries a *grade* of this kind, and the Parser type is a *graded monad*
over these grades.

To the best of my knowledge, the only practical implementation of a total parser
combinator library is [agdarsec](https://github.com/gallais/agdarsec), by
Guillaume Allais ([paper, 2018](https://gallais.github.io/pdf/agdarsec18.pdf)).
The original library is in Agda but has been ported to Rocq
([parseque](https://github.com/rocq-community/parseque)) and Idris
([tparsec](https://github.com/gallais/idris-tparsec)). Earlier, [Danielsson
2010](https://dl.acm.org/doi/10.1145/1863543.1863585) introduced the first total
parser combinator library based on Brzozowski derivatives. I'll compare
prim-parser to both in the [Related work](#related-work) section.

# Original contributions {#contributions}

To the best of my knowledge:

1. **Graded monads as a totality approach for parser combinators.** The first
   use of graded monads in a parser combinator library. The grade tracks
   error and consumption necessity in the type.
2. **First total monadic parsec-style parser combinator library (in any total
   language).** Parsec-style means a shallow embedding: a parser is essentially
   an ordinary function from input to result. agdarsec is total and uses a
   shallow embedding but not monadic. Danielsson is total and monadic but uses a
   deep embedding via Brzozowski derivatives, which is known to have exponential
   complexity. Moreover, biased choice is not supported by Danielsson.
3. **First total parser combinator library in Lean 4.** `lean4-parser` uses
   `partial`. agdarsec's approach could be ported but hasn't been.
   Danielsson's approach uses mixed induction/coinduction,
   which Lean does not support.

**The rest of the post.**
- [The grade](#the-grade) Introduces the grade prim-parser uses for the parser type.
- [Graded monad](#graded-monad) shows how grades compose, making `Parser` a
  graded monad.
- [Combinators](#combinators) is a tour of the standard parser combinators with graded types.
- [Guarded recursion via `fix`](#fix) explains recursive parsers.
- [The Parser type](#the-parser-type) explains the parser type in more detail.
- [The `gdo` macro](#gdo) describes the graded version of `do`-notation.
- [Examples](#examples) presents implementations of S-expressions and CSV parsers.
- [Related work](#related-work) compares prim-parser to lean4-parser, Danielsson
  2010, and agdarsec.
- [Future work](#whats-left).

# The grade {#the-grade}

The grade tracks two pieces of static information about a parser:

1. **Errors.** Can it fail?
2. **Consumption.** Does it consume input on success?

Each axis admits three answers: `never`, `possibly`, `always`.
```lean
inductive Necessity where
  | never
  | possibly
  | always
```

We order them `never < possibly < always`, so `⊔` is `max` over this order. Note that `⟨Necessity, ⊔, never⟩` forms a monoid.

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

`Grade` is a monoid:

```lean
instance : Monoid Grade where
  mul ⟨e, c⟩ ⟨e', c'⟩ := ⟨e ⊔ e', c ⊔ c'⟩
  one := ⟨never, never⟩
```

I'll write `g * g'` for the monoid product (in this post the same as `g ⊔ g'`).
It expresses how grades combine when one parser runs after another. For example,
suppose we run a parser that never fails and may consume, followed by one that
may fail and always consumes:

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

As shown by both agdarsec and Danielsson, to ensure termination it is enough to
track in the type whether a parser accepts the empty string. The grade I chose
is more expressive than that. As we will see in the
[Combinators](#combinators) section, this allows giving precise types to
combinators that a simpler grade could not.

# Graded monad {#graded-monad}

We just saw how grades multiply when parsers run in sequence. That's what
`gbind` does; `gpure` has the unit grade. Let's look at the signatures, with `g,
g' : Grade`:

```lean
def gpure : α → Parser pure α  -- pure = ⟨never, never⟩, the monoid unit
def gbind : Parser g α → (α → Parser g' β) → Parser (g * g') β
```

This is a *graded monad* ([Katsumata's parametric effect monads][katsumata]).
Briefly, a graded monad is like a standard monad indexed by an element `g` of
some monoid (the *grade*). `gbind` multiplies the indices; `gpure` uses the
monoid unit. In the table below I compare the signatures:

| Standard Monad                | Graded Monad                              |
|-------------------------------|-------------------------------------------|
| pure  : α → m α               | gpure : α → m 1 α                         |
| bind  : m α → (α → m β) → m β | gbind : m i α → (α → m j β) → m (i * j) β |

Note that graded monads are a strict generalisation of standard monads (the
graded monad with the trivial monoid is exactly the standard monad). No Lean
library ships the graded hierarchy, so prim-parser provides `GradedFunctor`,
`GradedApplicative`, `GradedMonad`, and their respective `Lawful*` variants
itself. I've proved the functor, applicative, and monad laws for `Parser` as
Lean theorems. With `i, j, k : Grade`, the two sides of each law carry different
grade indices syntactically; to unify then we need prove the grade identity
in the right column, and those identities follow from the monoid laws on
`Grade`:

| Property      | Equation                              | Grade equation            |
|---------------|---------------------------------------|---------------------------|
| Left unit     | gpure x >>= f = f x                   | 1 * j = j                 |
| Right unit    | m >>= gpure = m                       | i * 1 = i                 |
| Associativity | (m >>= f) >>= g = m >>= λa. f a >>= g | (i * j) * k = i * (j * k) |

[katsumata]: https://dl.acm.org/doi/10.1145/2535838.2535846

# Combinators {#combinators}

This section is a tour of the common parser combinators you'd expect to find
in any parser combinator library. For each, we'll look at the signature, describe the
behaviour, and relate it to the grade. By the end I hope you'll see
that grades do more than enforce totality; they also help document the
combinator's behaviour in the type. `fix`, the recursion combinator, has
its [own section](#fix).

---

**`anyChar`** consumes and returns a single character, or fails if the
input is empty:

```lean
anyChar : Parser conditional Char  -- conditional = ⟨possibly, always⟩
```

It may fail (on empty input) and always consumes on success.

---

**`lookahead`** runs `p` but never consumes:

```lean
lookahead : Parser ⟨ge, gc⟩ α → Parser ⟨ge, never⟩ α
```

The error grade is preserved; the consumption grade is set to `never`.

---

**`eof`** succeeds only when there is no more input:

```lean
eof : Parser lookahead PUnit  -- lookahead = ⟨possibly, never⟩
```

---

**`notFollowedBy`** succeeds exactly when `p` fails, without consuming:

```lean
notFollowedBy : Parser ⟨ge, gc⟩ α → Parser ⟨ge.complement, never⟩ PUnit
```

`complement` is a `Necessity` operation defined by these equations:

```
complement never = always
complement possibly = possibly
complement always = never
```

If `p` always fails, `notFollowedBy p` never fails; if `p` never fails,
`notFollowedBy p` always fails. In short, the error grade is flipped.

---

**`many`** applies a parser zero or more times, collecting results:

```lean
many : Parser ⟨ge, always⟩ α → Parser flexible (List α)
```

The argument must always consume (otherwise recursion wouldn't terminate);
the result is `flexible` (never fails, may consume) because zero
repetitions is allowed.

---

**`many1`** is `many` with at least one repetition. The argument's grade is
preserved exactly:

```lean
many1 : Parser ⟨ge, always⟩ α → Parser ⟨ge, always⟩ (NonEmptyList α)
```

---

**`optional`** tries `p`; on failure, returns `none`. The result never
fails:

```lean
optional : Parser ⟨ge, gc⟩ α → Parser ⟨never, ge.complement ⊓ gc⟩ (Option α)
```

`optional p` only consumes input when `p` succeeds. `ge.complement` flips the
error grade to capture how often that happens. That is, `never` if `p` always
fails, `always` if `p` never fails. Taking the meet (`⊓`, min) with `gc` caps
that by what `p` consumes when it succeeds.

---

**`choice`**, written infix as `<|>`, tries the first parser; on failure, the second. The error
grade is `ge ⊓ ge'` (the combined parser only always-fails if both
branches do); the consumption grade uses a small helper `ite` that cases
on the first branch's failure pattern:

```lean
def ite (sel a b : Necessity) : Necessity :=
  match sel with
  | never    => b                              -- first never fails: take b
  | always   => a                              -- first always fails: take a
  | possibly => if a = b then a else possibly -- both might run

choice : Parser ⟨ge, gc⟩ α → Parser ⟨ge', gc'⟩ α
       → Parser ⟨ge ⊓ ge', ge.ite gc' gc⟩ α
```

So in `ge.ite gc' gc`: if `ge = never` (first branch never fails), the
second is unreachable and consumption is `gc`. If `ge = always`, only
the second branch runs and consumption is `gc'`. Otherwise consumption is
`gc` when `gc = gc'`, and `possibly` otherwise.

---

**`oneOf`** runs the parsers in order, returning the first success.

```lean
oneOf : NonEmptyList (Parser g α) → Parser g α
```

---

**`count`** parses exactly `n` occurrences, returning a length-indexed
vector. Both grade components are relaxed to `possibly`, since `count 0 p`
succeeds without consuming:

```lean
count : (n : Nat) → Parser ⟨ge, gc⟩ α
      → Parser ⟨ge ⊓ possibly, gc ⊓ possibly⟩ (Vector α n)
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
      → gc' ⊔ gc = always
      → Parser flexible (List α)
```

The constraint `gc' ⊔ gc = always` says the separator and the element
must consume *together*.

# Guarded recursion via `fix` {#fix}

The `fix` combinator enables recursive parsers:

```lean
def fix : ((self : Parser ⟨ge, always⟩ α) → Parser ⟨ge, always⟩ α) → Parser ⟨ge, always⟩ α
```

The argument to `fix` is a function. This function must produce a parser that
always consumes on success. For recursive calls, it uses the `self` argument
parser.

Let's look at an example: a parser for a balanced parenthesis group (e.g. `()`,
`(())`, `(()())`):

```lean
def group : Parser conditional Unit :=
  fix fun self => gdo
    char '('  -- always consumes
    many self -- possibly consumes
    char ')'
```

We use `fix` to introduce a recursive parser. The type of `fix` mandates that in
the body of the lambda we must build an always consuming parser. We do so by
sequencing three simple parsers with `gdo`. `gdo` is `do`-notation for graded
monads (covered [later](#gdo)). The first parser `char '('` always consumes; the
second parser `many self` possibly consumes (because `many` accepts zero
occurrences), the third parser `char ')'` always consumes. It obviously follows
that the sequence of the parsers is always consuming and thus we've provided a
valid argument for `fix`.

# The Parser type {#the-parser-type}

The parser type is parameterised by an error type `ε`, a grade `g`, and a result
type `α`. Its single field `run` is like a parsec parser, but the input is sized
so that consumption can be tracked in the type. `Text n` is a wrapper around a
`ByteArray` with the byte length in its type.

```lean
structure Parser (ε : Type) (g : Grade) (α : Type) where
    run : ∀ {n}, Text n → Outcome ε n g α
```

The result type `Outcome` is computed from the error component of the grade:
```lean
abbrev Outcome (ε : Type) (n : Nat) (g : Grade) (α : Type) :=
  match g.errors with
  | never    => Success n g.consumes α
  | possibly => Failure n ε ⊕ Success n g.consumes α
  | always   => Failure n ε
```

Both non-error branches return a `Success`, which bundles the parsed value,
the leftover input, and a *consumption witness*:

```lean
structure Success (n : Nat) (consumes : Necessity) (α : Type) where
  result   : α
  {restSize : Nat}
  restText : Text restSize
  witness  : consumptionWitness restSize n consumes
```

The witness relates the input length `n` to the remaining input length `restSize`:

```lean
abbrev consumptionWitness (rest n : Nat) : Necessity → Prop
  | never    => rest = n
  | possibly => rest ≤ n
  | always   => rest < n
```

The `< n` case for `consumes = always` is what enables the termination proof for
the `fix` combinator.

The error branches return a `Failure`:

```lean
structure Failure (n : Nat) (ε : Type) where
  error    : ε
  {restSize : Nat}
  restText : Text restSize
  witness  : restSize ≤ n
```

# The `gdo` macro {#gdo}

`do`-notation is a well-established syntax sugar for writing monadic programs.
Analogously, I have implemented a `gdo` macro that adapts it to graded monads.
The `gdo` macro included in prim-parser works for any graded monad, not just the
one implemented by the parser. Eventually the `gdo` macro should be published
independently of prim-parser.

The `gdo` macro just sequences statements with `gbind`. As we saw, the return
type of `gbind` is graded by the product of its arguments grades. For instance,
sequencing two parsers of grade `g` yields `g * g`:

<pre><code>def twice (p : Parser ε g α) : Parser ε <span style="color: #1e6fcc; font-weight: bold">(g * g)</span> α := gdo
  p
  p
</code></pre>

This type-checks, but the inferred grade `g * g` isn't the one we want to write in the signature.
We want to have:

<pre><code>def twice (p : Parser ε g α) : Parser ε <span style="color: #1e6fcc; font-weight: bold">g</span> α := ...
</code></pre>

This no longer type-checks on its own because `g * g` is not definitionally
equal to `g`. To solve this, prim-parser provides `gcast`; a specialised substitution for the
grade of the monad:

```lean
def gcast (h : i = j) (x : m i α) : m j α := h ▸ x
```

We can apply `gcast` directly to the `gdo` block:

<pre><code>def twice (p : Parser ε g α) : Parser ε g α := <span style="color: #d97706; font-weight: bold">gcast (by simp) <|</span> gdo
  p
  p
</code></pre>

`by simp` proves `g * g = g` by using a simp lemma included in the library.
This is a very common pattern, so I included some syntax sugar that makes it more pleasant to read and write. It's called `grade_by` and it optionally comes at the end of a `gdo` block. The definition below is the same as the definition above:

<pre><code>def twice (p : Parser ε g α) : Parser ε g α := gdo
  p
  p
  <span style="color: #d97706; font-weight: bold">grade_by by simp</span>
</code></pre>

# Examples {#examples}

This section presents two examples: S-expressions and CSV. The
[`Examples/`](https://github.com/janmasrovira/prim-parser/tree/blog-v1/Examples)
directory in the repo has a few more parsers in the same style: arithmetic
expressions (with operator precedence), JSON, and the untyped lambda calculus.

## S-expressions {#sexp}

[*Source: `Examples/SExp.lean`*](https://github.com/janmasrovira/prim-parser/blob/blog-v1/Examples/SExp.lean)

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

def patom : Parser Error conditional SExp :=
  .atom <$>ᵍ takeWhile1 (·.isAlphanum)

def sexp : Parser Error conditional SExp :=
  fix (fun sexp_rec =>
    let plist : Parser Error conditional SExp := gdo
      lexeme (char '(')
      let first ← sexp_rec
      let rest ← many (gdo whitespace; sexp_rec)
      lexeme (char ')')
      return listToPairs (first :: rest)
    patom <|> plist)
```

## CSV {#csv}

[*Source: `Examples/Csv.lean`*](https://github.com/janmasrovira/prim-parser/blob/blog-v1/Examples/Csv.lean)

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

def row : Parser Error flexible (List String) :=
  sepBy comma field

private def exactRow (n : Nat) : Parser Error fallible (List.Vector Value n) :=
  sepByN comma cell n

def table : Parser Error conditional ((n : Nat) × Table n) := gdo
  let headers ← row
  newline
  let n := headers.length
  let rows ← sepBy newline (exactRow n)
  let t : Table n := { columns := ⟨headers, rfl⟩, rows }
  return (⟨n, t⟩ : (n : Nat) × Table n)
```

The [`Examples/`](https://github.com/janmasrovira/prim-parser/tree/blog-v1/Examples)
directory has a few more parsers in the same style: arithmetic expressions
(with operator precedence), JSON, and the untyped lambda
calculus.

# Related work {#related-work}

In this section I compare prim-parser to three closely related libraries.

| Library         | Total | Monadic | Parsec-style | Left-recursion | Coinduction |
|-----------------|:-----:|:-------:|:------------:|:--------------:|:-----------:|
| prim-parser     |   ✓   |   ✓\*   |      ✓       |       ✗        | not needed  |
| lean4-parser    |   ✗   |    ✓    |      ✓       |       ✗        | not needed  |
| agdarsec        |   ✓   |    ✗    |      ✓       |       ✗        | not needed  |
| Danielsson 2010 |   ✓   |   ✓\*   |      ✗       |       ✓        |   needed    |

\* Neither has a standard `Monad` typeclass instance; see the
[Danielsson](#danielsson) section.

## [lean4-parser](https://github.com/fgdorais/lean4-parser) {#lean4-parser}
lean4-parser is the most popular Lean 4 parsing library. Both prim-parser and
lean4-parser are parsec-style and use the same shallow embedding (a parser is
just a function from the input to a result), run by applying it. In that
sense the two are essentially the same under the hood. The main differences are:

- **Totality.** lean4-parser uses `partial` for unchecked recursion; prim-parser
  is total.
- **Recursion.** lean4-parser writes recursive parsers as ordinary Lean
  recursive definitions (`partial` lets Lean accept them without a termination
  proof). prim-parser uses an explicit guarded-recursion combinator
  [`fix`](#fix), whose type forces the recursive call to happen only after
  consumption, ensuring termination.
- **Monad vs graded monad.** lean4-parser is a standard `Monad` (and a monad
  transformer, so it can run on top of `StateT`, etc.) and works with the
  built-in `do` notation. prim-parser is a *graded* monad. Instead, it uses a
  [`gdo`](#gdo) notation that works for any graded monad.
- **Stream type.** lean4-parser is generic in the input stream; prim-parser
  currently only supports its own `Text n`.

## [Danielsson 2010](https://dl.acm.org/doi/10.1145/1863543.1863585) {#danielsson}

- **Monadic**. Both libraries are monadic but neither provides a standard
  `Monad` instance for `Parser`. prim-parser's `Parser` is a `GradedMonad`
  instance with monad laws proven as propositional equalities. Danielsson's
  `Parser` defines a `bind` and proves the monad laws up to bag equality of
  parse results. It cannot be an instance of the standard `Monad` typeclass
  because coinduction appears in `bind`'s argument types.
- **Implementation**. Danielsson uses a deep embedding based on Brzozowski
  derivatives: a parser is a data structure that is differentiated one token at
  a time, and running it returns all successful parses. Consequently, does not
  support biased choice. prim-parser is a shallow embedding (a function from
  input to output). Supports biased choice and all the usual combinators in
  parsec-style libraries.

  Danielsson needs the language to support mixed induction and
  coinduction. Thus, it cannot be ported to Lean.
- **Recursion**. Danielsson uses regular recursion. In prim-parser recursion can
  only be expressed through the fix combinator.
- **Errors**. Since Danielsson's parsers return the list of all successful
  parses, failure is just the empty list, with no way to report why a parse
  failed. prim-parser, by contrast, supports custom errors.
- **Practical use**. The [code](https://github.com/nad/parser-combinators) is
  published as the artifact accompanying three publications. It seems to me like
  the main purpose of the repo is to implement the theory presented in the
  papers, rather than to be a library for mainstream use.
- **Left recursion**. A rule like `term ::= term '+' factor` is *left recursive* because
  the `term` appears at the start of its own definition. A direct translation loops forever in most parser libraries. prim-parser
  prevents the loop, but the user must unfold the left recursion into
  an iterative form, as shown below. This is the case in all parsec-style libraries. Danielsson expresses left-recursive grammars
  much more directly, but the coinductive arguments must be marked with `♯`.
  The grammar below is taken directly from Danielsson's paper.
  ```agda
  mutual
  -- term ::= factor | term '+' factor
    term = factor
         ∣ ♯ term  >>= λ n₁ →
           tok '+' >>= λ _  →
           factor  >>= λ n₂ →
           return (n₁ + n₂)

  -- factor ::= atom | factor '*' atom
    factor = atom
           ∣ ♯ factor >>= λ n₁ →
             tok '*'  >>= λ _  →
             atom     >>= λ n₂ →
             return (n₁ * n₂)

  -- atom ::= number | '(' term ')'
    atom = number
         ∣ tok '(' >>= λ _ →
           ♯ term  >>= λ n →
           tok ')' >>= λ _ →
           return n
  ```

  In prim-parser the same grammar is expressed with the `chainl1` combinator.

  ```lean
  def addOp : Parser Error conditional (Nat → Nat → Nat) :=
    (· + ·) <$ᵍ char '+'

  def mulOp : Parser Error conditional (Nat → Nat → Nat) :=
    (· * ·) <$ᵍ char '*'

  def term : Parser Error conditional Nat :=
    fix (fun term_rec =>
      let atom   := nat <|> parens term_rec
      let factor := chainl1 mulOp atom
      chainl1 addOp factor)
  ```

## [agdarsec](https://github.com/gallais/agdarsec) {#agdarsec}
To the best of my knowledge, [agdarsec](https://github.com/gallais/agdarsec) and
its ports [tparsec](https://github.com/gallais/idris-tparsec) (Idris) and
[parseque](https://github.com/rocq-community/parseque) (Rocq) are the only
implementations of a total parser combinator that have seen some practical
adoption.

In agdarsec every parser must consume input to succeed. This means that
non-consuming parsers cannot be defined. In particular, the `pure` parser
that returns a constant value and never consumes cannot be defined, which blocks
a monad instance. As we will see in the [connectors](#connectors) section, this
degrades usability considerably.

Other parsers that cannot be defined in agdarsec include:
- zero or more repetition: `many`, `skipMany`, `sepBy`, etc.
- `optional`.
- `lookahead`, `notFollowedBy`.
- `eof` (end of input), `getPosition`.

### agdarsec connectors vs prim-parser's `gdo` notation {#connectors}

The lack of a monadic interface forces agdarsec to provide a big collection of
connectors to work around the limitation. These connectors add no essential
meaning to the parser, and the user must remember all of them (use of mnemonic
names makes it a bit simpler, but still, in my opinion, unpleasant).

Below I list most of agdarsec's connectors, each paired with its prim-parser
`gdo` equivalent. Although `gdo` is more verbose and needs explicit local
bindings, it replaces the whole collection of connectors with one notation that
functional programmers are already familiar with, making it far more ergonomic.
Moreover, `gdo` is a generic macro that works for any graded monad, not just
prim-parser's.

---

**`_>>=_ : Parser a → (a → Parser b) → Parser b`**:

agdarsec:
```agda
p >>= f
```

prim-parser:
```lean
gdo
  let x ← p
  f x
```

---

**`_&>>=_ : Parser a → (a → Parser (b a)) → Parser (Σ a b)`**:

agdarsec:
```agda
p &>>= f
```

prim-parser:
```lean
gdo
  let x ← p
  let y ← f x
  return ⟨x, y⟩
```

---

**`_&>>=′_ : Parser a → (a → Parser b) → Parser (a × b)`**:

agdarsec:
```agda
p &>>=′ f
```

prim-parser:
```lean
gdo
  let x ← p
  let y ← f x
  return (x, y)
```

---

**`_&?>>=_ : Parser a → (a → Parser (b a)) → Parser (Σ a (Maybe ∘ b))`** makes the second parser optional:

agdarsec:
```agda
p &?>>= f
```

prim-parser:
```lean
gdo
  let x ← p
  let y ← optional (f x)
  return ⟨x, y⟩
```

---

**`_?&>>=_ : Parser a → (Maybe a → Parser b) → Parser (Maybe a × b)`** makes the first parser optional:

agdarsec:
```agda
p ?&>>= f
```

prim-parser:
```lean
gdo
  let x ← optional p
  let y ← f x
  return (x, y)
```

---

**`_<&?>_ : Parser a → Parser b → Parser (a × Maybe b)`**:

agdarsec:
```agda
p <&?> q
```

prim-parser:
```lean
gdo
  let x ← p
  let y ← optional q
  return (x, y)
```

---

**`_<&?_ : Parser a → Parser b → Parser a`**:

agdarsec:
```agda
p <&? q
```

prim-parser:
```lean
gdo
  let x ← p
  optional q
  return x
```

---

**`_&?>_ : Parser a → Parser b → Parser (Maybe b)`**:

agdarsec:
```agda
p &?> q
```

prim-parser:
```lean
gdo
  p
  optional q
```

---

**`_<?&>_ : Parser a → Parser b → Parser (Maybe a × b)`**:

agdarsec:
```agda
p <?&> q
```

prim-parser:
```lean
gdo
  let x ← optional p
  let y ← q
  return (x, y)
```

---

**`_<?&_ : Parser a → Parser b → Parser (Maybe a)`**:

agdarsec:
```agda
p <?& q
```

prim-parser:
```lean
gdo
  let x ← optional p
  q
  return x
```

---

**`_?&>_ : Parser a → Parser b → Parser b`**:

agdarsec:
```agda
p ?&> q
```

prim-parser:
```lean
gdo
  optional p
  q
```

---

**`_<⊎>_ : Parser a → Parser b → Parser (a ⊎ b)`**:

agdarsec:
```agda
p <⊎> q
```

prim-parser:
```lean
(Sum.inl <$>ᵍ p) <|> (Sum.inr <$>ᵍ q)
```
Here `<$>ᵍ` means `gmap`, the equivalent of `map` for graded monads.

---

**`<[_,_]> : (a → r) → (b → Parser r) → Parser (a ⊎ b) → Parser r`**:

agdarsec:
```agda
<[ f , k ]> pab
```

prim-parser:
```lean
gdo
  let x ← pab
  match x with
  | .inl a => return (f a)
  | .inr b => k b
```

### A full example: S-expressions {#sexp-comparison}

To see the difference on a real example, here is a complete S-expression parser
in each library, taken almost verbatim (comments have been stripped) from the
respective repositories.

agdarsec ([`examples/SExp.agda`](https://github.com/gallais/agdarsec/blob/28c5233/examples/SExp.agda)):
```agda
sexp : ∀[ Parser SExp ]
sexp = fix (Parser SExp) $ λ rec →
  let atom = Atom ∘ String.fromList ∘ List⁺.toList <$> list⁺ alpha
      sexp = (λ (a , mb) → maybe (Pair a) a mb)
             <$> parens (lift2 (λ p q → withSpaces p <&?> box (q <&? box spaces))
                               rec rec)
  in atom <|> sexp
```

prim-parser ([`Examples/SExp.lean`](https://github.com/janmasrovira/prim-parser/blob/blog-v1/Examples/SExp.lean)):
```lean
def patom : Parser Error conditional SExp :=
  .atom <$>ᵍ takeWhile1 (·.isAlphanum)

def sexp : Parser Error conditional SExp :=
  fix (fun sexp_rec =>
    let plist : Parser Error conditional SExp := gdo
      lexeme (char '(')
      let first ← sexp_rec
      let rest ← many (gdo whitespace; sexp_rec)
      lexeme (char ')')
      return listToPairs (first :: rest)
    patom <|> plist)
```

# Future work {#whats-left}

- **Better error messages.** The error type is currently just `String`. The
  grade machinery is independent of the error representation, so swapping in
  a richer diagnostic ADT (with source positions and labelled expectations,
  `parsec`-style) is doable.
- **Explore monad transformers.** Perhaps it is possible to introduce an
  underlying standard monad to the parser type.
- **Split out graded monads.** The `GradedFunctor` / `GradedApplicative` / `GradedMonad`
  hierarchy and their lawful counterparts have nothing to do with parsers;
  they belong either in mathlib or in their own library.
