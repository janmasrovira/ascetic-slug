+++
title = "An Agda eDSL for well-typed Hilbert style proofs"
date = 2019-05-19
[extra]
toc = true
+++

I present an Agda eDSL for writing Hilbert style proofs for logic $𝑲$.

This blog consists of two main parts. The first part presents the language and
some examples. The second offers some insight into the key parts of the
implementation. The latter targets Agda beginner/intermediate users or any
programmer interested in dependent types.

The code is available [here](https://gitlab.com/snippets/1858322). It has been implemented using Agda 2.6.0 with the
[standard library](https://github.com/agda/agda-stdlib) (at this specific [commit](https://github.com/agda/agda-stdlib/commit/805c897f32f605a666ec3738a3005e3800bf2964)).

# Some introductory concepts

**What is an eDSL?** The acronym eDSL stands for Embedded Domain Specific
Language. It refers to a small language (a set of functions and data types)
embedded in another language (in this case Agda) that has been designed to
solve a problem in a very specific domain, in this case, Hilbert style proofs.

**What is a Hilbert style proof?** First we need to know what a Hilbert calculus
is. A Hilbert calculus is a set of axioms plus a set of rules. The axioms are
formulas that we accept as primitive theorems and the rules allow us to
syntactically combine existing theorems to create new ones. Then, a Hilbert
style proof is a sequence of formulas where each formula is either an axiom of
the calculus or the result of applying a rule to previous formulas in the
sequence. The last formula in the sequence is the theorem of the proof. It is
best understood by seeing a concrete example, if you scroll down you will find
one.

# The eDSL and logic $K$

As a preface, let me remark that that the chosen logic, $𝑲$, is not of
special importance here, it just lays the ground for some concrete examples.
In fact, it would be interesting to implement a logic agnostic eDSL in
the future.

Let&rsquo;s begin by defining the syntax of modal formulas:

\\[
\begin{align*}
 ModalFm ≔ Var\ |\ ModalFm → ModalFm\ |\ □ ModalFm \ |\ ⊥   \\\\
 \end{align*}
\\]

Of course, we are missing important logical connectives like $¬,∧,∨$, but it
is better to have a small core language and define the other connectives in
terms of the primitive ones, for instance:

\\[
\begin{align*}
 ¬ϕ & ≔ ϕ→⊥ \\\\
 ϕ∧ψ & ≔ ¬(ϕ→¬ψ) \\\\
 ϕ∨ψ & ≔ ¬ϕ→ψ \\\\
 \end{align*}
\\]

The axioms of $𝑲$ are the following:

\\[
\begin{align*}
 \text{(K1)  } & ϕ → (ψ → ϕ) \\\\
 \text{(K2)  } & (ϕ → (ψ → ξ)) → ((ϕ → ψ) → (ϕ → ξ)) \\\\
 \text{(K3)  } & (¬ ϕ → ¬ ψ) → (ψ → ϕ) \\\\
 \text{(Distribution)  } & □ (ϕ → ψ) → (□ ϕ → □ ψ)
 \end{align*}
\\]

The above are axiom schemes (or templates), so $ϕ,ψ,ζ$ are
formula metavariables which can be substituted for any modal formula.

And the rules are the following:

-   **Modus Ponens:** If $ϕ$ is a theorem and $ϕ→ψ$ is a theorem, then $ψ$
    is a theorem.

\\[
\begin{array}{c}
    ϕ→ψ \\\\
    ϕ \\\\
    \hline
    ψ
  \end{array}
\\]

-   **Necessitation:** If $ϕ$ is a theorem then $□ϕ$ is a theorem.

\\[
\begin{array}{c}
    ϕ \\\\
    \hline
    □ϕ
  \end{array}
\\]

-   **Identity:** If $ϕ∈Σ$ then $Σ⊢ϕ$. Note that $ϕ$ may not be a theorem. See
    clarification at the end of this section.

Finally! we can construct our first Hilbert style proof. Let&rsquo;s prove $□(ϕ→ϕ)$.

\\[
 \begin{array}{lr}
 \text{[ 0 ] } (ϕ → ((ϕ → ϕ) → ϕ)) → ((ϕ → (ϕ → ϕ)) → (ϕ → ϕ))  & \text{By K2} \\\\
 \text{[ 1 ] }  ϕ → ((ϕ → ϕ) → ϕ)                                & \text{By K1} \\\\
 \text{[ 2 ] }  ϕ → (ϕ → ϕ)                                        & \text{By K1} \\\\
 \text{[ 3 ] } (ϕ → (ϕ → ϕ)) → (ϕ → ϕ)                           & \text{By MP 0,  1} \\\\
 \text{[ 4 ] } ϕ → ϕ                                             & \text{By MP 3, 2} \\\\
 \text{[ 5 ] } □ (ϕ → ϕ)                                         & \text{By Nec 4}\\\\
  \end{array}
\\]

And now&#x2026; how does the same proof look in our eDSL as Agda code? Here it is:

```
□⟨ϕ↝ϕ⟩ : ∀ {Σ ϕ} → Σ ⊢ □ (ϕ ↝ ϕ)
□⟨ϕ↝ϕ⟩ {Σ} {ϕ} =
  begin[ 0 ] (ϕ ↝ ((ϕ ↝ ϕ) ↝ ϕ)) ↝ ((ϕ ↝ (ϕ ↝ ϕ)) ↝ (ϕ ↝ ϕ)) By K2
       [ 1 ] ϕ ↝ ((ϕ ↝ ϕ) ↝ ϕ)                               By K1
       [ 2 ] ϕ ↝ (ϕ ↝ ϕ)                                      By K1
       [ 3 ] (ϕ ↝ (ϕ ↝ ϕ)) ↝ (ϕ ↝ ϕ)                        ByMP 0 , 1
       [ 4 ] ϕ ↝ ϕ                                             ByMP 3 , 2
       [ 5 ] □ (ϕ ↝ ϕ)                                         ByNec 4
       ■
```

Wow, they look really similar indeed! So what? Well, we can write Hilbert styles
proofs in a paper-like syntax with the key advantage that Agda&rsquo;s type
checker will make sure that the proof is constructed according to the rules,
that is, that there are **no mistakes** in it. For instance, proofs where an axiom
is instantiated incorrectly, or an application of modus ponens is incorrect will
fail to type check and we will get an error from the compiler telling us where
the misstep is. An additional free perk that we get is that we can easily export the proofs to
rich [html](https://agda.readthedocs.io/en/latest/tools/generating-html.html) or [latex](https://agda.readthedocs.io/en/latest/tools/generating-latex.html).

Let me underline that the code above is actual Agda code. This might be
surprising for readers not accustomed to Agda&rsquo;s [mixfix operators](https://agda.readthedocs.io/en/v2.6.0/language/mixfix-operators.html), which give
great syntactical versatility.

It is worth noting that the `By` step does not only accept axioms, but any
theorem previously proved. So, if we were to prove another theorem and we wanted
to use $□ (ϕ → ϕ)$ as an intermediate step we could do so. Also, since we proved
$□(ϕ→ϕ)$ for any $ϕ$, we are free to substitute it for any formula. Example:

    ...
    [ 1 ] □ (ϕ ↝ ϕ)             By □⟨ϕ↝ϕ⟩
    [ 2 ] □ ((ψ ∧ ϕ) ↝ (ψ ∧ ϕ)) By □⟨ϕ↝ϕ⟩
    ...

What about premises? Well, as you may have already noticed in the previous
proof, we wrote $Σ ⊢ □ (ϕ → ϕ)$, where $Σ$ is our set of premises, and we are
free to use any formula in $Σ$ as if it was a theorem within the proof.
As an example, let&rsquo;s prove $ϕ→ψ,ϕ,Σ⊢ψ$.

    ϕ↝ψ∷ϕ∷Σ⊢ψ : ∀ {ϕ ψ Σ} → ϕ ↝ ψ ∷ ϕ ∷ Σ ⊢ ψ
    ϕ↝ψ∷ϕ∷Σ⊢ψ {ϕ} {ψ} =
      begin[ 0 ] ϕ       By premise 1
           [ 1 ] ϕ ↝ ψ   By premise 0
           [ 2 ] ψ       ByMP 0 , 1
           ■

**Clarification:** Notice that a formula $ϕ$ is a *theorem* of the
logic $K$ if and only if $∅⊢ϕ$. So in case we have $Σ⊢ϕ$ with $Σ$ nonempty it
may be that $ϕ$ is not a theorem of $K$. It is worth noting that when we
define `ϕ↝ϕ : ∀ {Σ ϕ} : Σ ⊢ ϕ ↝ ϕ`, then the term `ϕ↝ϕ` is really a proof that
$ϕ → ϕ$ is a theorem of $K$ since $Σ$ is a parameter of the proof and in
particular it can be empty.

This concludes the overview of the language features.


# Implementation tour

We start by defining the syntax of formulas. We define variables to be
natural numbers but this is not really relevant.

    Var : Set
    Var = Nat
    
    infixr 20 _↝_
    data Fm : Set where
      _! : Var → Fm
      _↝_ : Fm → Fm → Fm
      □ : Fm → Fm
      ⊥ : Fm

Now, if we wanted, we could expand our language by defining more function
symbols. For instance, we could define negation thus:

    ¬ : Fm → Fm
    ¬ ϕ = ϕ ↝ ⊥

We could do the same for $∧,∨,♢,⊤$ and any other operator.

Let&rsquo;s define a data type that represents a proof in Hilbert calculus. As
expected, it will have a constructor for each axiom scheme and rule.

    infix 0 _⊢_
    data _⊢_ (Σ : List Fm) : Fm → Set where
      K1 : ∀ {ϕ ψ : Fm} → Σ ⊢ ϕ ↝ (ψ ↝ ϕ)
      K2 : ∀ {ϕ ψ ξ : Fm} → Σ ⊢ (ϕ ↝ (ψ ↝ ξ)) ↝ ((ϕ ↝ ψ) ↝ (ϕ ↝ ξ))
      K3 : ∀ {ϕ ψ : Fm} → Σ ⊢ (¬ ϕ ↝ ¬ ψ) ↝ (ψ ↝ ϕ)
      distribution : {ϕ ψ : Fm} → Σ ⊢ □ (ϕ ↝ ψ) ↝ (□ ϕ ↝ □ ψ)
      necessitation : ∀ {ϕ : Fm} → Σ ⊢ ϕ → Σ ⊢ □ ϕ
      mp : ∀ {ϕ ψ : Fm} → Σ ⊢ (ϕ ↝ ψ) → Σ ⊢ ϕ → Σ ⊢ ψ
      premise : ∀ {ϕ : Fm} → Member ϕ Σ → Σ ⊢ ϕ

We can now write our first proof. The following proof corresponds to the proof
that $ϕ→ϕ$ is a theorem of $K$ shown above.

    ϕ↝ϕ : ∀ {Σ ϕ} → Σ ⊢ (ϕ ↝ ϕ)
    ϕ↝ϕ {Σ} {ϕ} = mp (mp (K2 {Σ} {ϕ} {ϕ ↝ ϕ} {ϕ}) (K1 {Σ} {ϕ} {ϕ ↝ ϕ})) (K1 {Σ} {ϕ} {ϕ})

It is horrible to read and too verbose. We can make it a little more succinct by
taking advantage of Agda&rsquo;s implicit argument inference:

    ϕ↝ϕ : ∀ {Σ ϕ} → Σ ⊢ ϕ ↝ ϕ
    ϕ↝ϕ {Σ} {ϕ} = mp (mp K2 K1) (K1 {ψ = ϕ})

Much better but still hard for a human to visualize what are the intermediate
steps. Computer programmers could think of this as machine code; something
very useful for its simplicity but hard for humans to use. So, as we do in
programming, we will design a human-friendly language and a compiler that
translates nice looking proofs into (let&rsquo;s call them) *primitive Hilbert style
proofs*. Of course, everything will be guaranteed to work from the types, so
no need to execute any code, just type check it (as is always the case when
using Agda as a proof checker).


## A sketch of the eDSL

We want a language as close to the paper-like syntax showed above as
possible. We will refer to proofs in this language as *nice proofs* and
proofs of the type `_⊢_` as *primitive proofs*. We will refer to the
process of translating nice proofs to primitive proofs as *compilation*.

First we need to think about the type of a nice proof. Well, it needs to keep
track of the set of premises, the formula that entails and the length of it,
so the following type is what we want.

    data HilbertProof : List Fm → Fm → Nat → Set

Then the compile function will be of the following type.

    compile : ∀ {n Σ ϕ} → HilbertProof Σ ϕ n → Σ ⊢ ϕ

We can now think about which constructors we need for a nice proof.

1.  `By`. To reference an axiom or another theorem.
2.  `MP`. To apply modus ponens to previous formulas in the proof.
3.  `Nec`. To apply necessitation to a previous formula in the proof.

We will refer to these constructors as *instructions*.

Instructions are numbered with consecutive naturals starting at 0. This
number is used to reference its corresponding formula in subsequent steps.
There must be a special instruction that does not expect instructions before
it. We call this instruction `Begin` and it works the same as `By` with the
exception that it can only be used as the first instruction.


## Highlights

We face the following challenges.

1.  **Numbering**. We need to make sure that the user labels the instructions
    properly.
2.  **Proper references**. We need to make sure that the numbers referencing
    other instructions are in range of the size of the proof and that
    they reference the appropriate formulas.
3.  **Compilation**. We need to translate nice proofs into primitive proofs.


### Numbering

The numbering certainly looks easier to tackle, so let&rsquo;s start by this one.
Instead of trying to solve our problem directly, I propose an alternative
problem that captures the same challenge but with no unnecessary noise around it.

<div class="alert alert-note"><p class="alert page-subtitle">Exercise: Boring list</p>

Define a list type such that the first number must be a zero and
each subsequent number must be equal to the head plus one.

<details class="alert alert-success">
<summary class="page-subtitle">Solution</summary>

We do so with the help of singleton types.

    data SingleNat : Nat → Set where
      single : (n : Nat) → SingleNat n
    
    data BoringList : Nat → Set where
      [_] : SingleNat 0 → BoringList 0
      _∷_ : ∀ {n} → SingleNat (suc n) → BoringList n → BoringList (suc n)
    
    example : BoringList 2
    example = single 2 ∷ (single 1 ∷ [ single 0 ])

Well, yeah, this kind of works, but we still have to write `single` before each
natural number, can&rsquo;t we do better? Yes, indeed! using [literal overloading](https://agda.readthedocs.io/en/latest/language/literal-overloading.html). If
we define a `Number` instance for `SingleNat` then we will be able to write
singleton naturals with plain natural numbers.

    instance
      NumNatSing : ∀ {n} → Number (SingleNat n)
      NumNatSing {n} .Number.Constraint m = n ≡ m
      NumNatSing .Number.fromNat m ⦃ refl ⦄ = single m

Then the example becomes:

    example : BoringList 2
    example = 2 ∷ (1 ∷ [ 0 ])

Perfect! that&rsquo;s what we needed.

</details>
</div>

With the previous solution in hand, it is easy to imagine how we can
incorporate the same idea into our language.


### Proper references

Let&rsquo;s focus on the case of modus ponens (necessitation works analogously).
Assuming the modus ponens instruction entails $ψ$, it should receive one
reference to $ϕ→ψ$ and another reference to $ϕ$. As we mentioned, these
reference will be written as natural numbers by the user, but as we need to
make sure that they are in range and reference the correct formulas, we need
an extra proof object ensuring that. More precisely, assuming we defined the
function `lookup-maybe : ∀ {Σ ζ ϕ} → HilbertProof Σ ζ ϕ → Nat → Maybe Fm` with the
expected implementation we would require both proof objects
`lookup-maybe HP i ≡ just (ϕ ↝ ψ)` and `lookup-maybe HP j ≡ just ϕ`.

But in the case that the references are correct, these proof objects will
always be trivially solved by normalization and reflexivity, hence the code
would look like this:

    [ 3 ] (ϕ ↝ (ϕ ↝ ϕ)) ↝ ϕ ↝ ϕ           ByMP 0 ⟨ refl ⟩ , 1 ⟨ refl ⟩

And we really want to avoid to have the explicit proof object as it makes
the syntax unpleasant. Could we use literal overloading for references to
previous formulas as well? Yes!

    data HilbertRef {Σ ϕ n} (H : HilbertProof Σ ϕ n) (ψ : Fm) : Set where
      ref : (i : Nat) → lookup-may H i ≡ just ψ → HilbertRef H ψ
    
    instance
      NumRef : ∀ {ϕ Σ n} {H : HilbertProof Σ ϕ n} {ψ} → Number (HilbertRef H ψ)
      NumRef {ϕ} {Σ} {n} {H} {ψ} .Number.Constraint i = lookup-may H i ≡ just ψ
      NumRef {ϕ} {Σ} {n} {H} .Number.fromNat i ⦃ x ⦄ = ref i x

Now we can write:

    [ 3 ] (ϕ ↝ (ϕ ↝ ϕ)) ↝ ϕ ↝ ϕ                 ByMP 0 , 1

And then each proof object is implicitly embedded in the natural literal `0, 1`.


### Compilation

It is hard to highlight a specific part over the others for the compilation
process. Compilation is mostly about fiddling with types and proof objects
to get the desired translation. If you are interested in this part I suggest
you look at the [code](https://gitlab.com/snippets/1858322) directly.


## Conclusion

I hope that you enjoyed the reading. Any comments and suggestions are welcome.

I am not an expert Agda programmer, so in case you look at the
full code, take it with a pinch of salt :)

