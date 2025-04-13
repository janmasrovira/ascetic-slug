+++
title = "Run-length encoding verified in Agda"
date = 2019-09-07
+++

This post is intended to be a guided exercise (with a proposed solution) for
Agda beginner&rsquo;s who are familiar with the basics and want to work on a slightly
more involved exercise than proving basic properties about natural numbers.
By *verified algorithm* we mean that termination is guaranteed and that it produces
the right output. In our case we want the compression and decompression
functions to satisfy $decompress ∘ compress = id$.
Termination is automatically checked by Agda so it will not require any explicit
proof.

The full code is [here](https://gitlab.com/snippets/1893023) (spoilers!). Agda 2.6.0.1 was used.

# The algorithm

The run-length encoding algorithm (RLE for short) is the most basic lossless
compression algorithm one could imagine. The algorithm goes through the string
and groups consecutive characters by saving just one character and the length
of the group. For instance, the string `aaabbcccc` becomes `(3,a)(2,b)(4,c)`.
Notice that parentheses and commas are used to denote pairs and not literal
characters of the string. Finally, by looking at the compressed string the
decompression algorithm is immediately apparent.


## Implementation

The proposed implementation uses some basic functions from the standard
library. Here is a full list of the needed types and function imports for the
implementation. If you are not familiar with them, you should refer to the
[standard library](https://github.com/agda/agda-stdlib).

    open import Agda.Builtin.Nat using (Nat; zero; suc)
    open import Data.List using (List; []; _∷_; replicate; _++_; foldl)
    open import Data.Maybe using (Maybe; just; nothing)
    open import Data.Nat.Properties using (_≟_)
    open import Data.Product using (_×_; _,_; proj₁; proj₂)
    open import Relation.Nullary using (yes; no)

In this post we will not delve in low level details such as how to encode pairs
or using machine bytes, instead, we will use naturals as bytes and lists of
naturals as byte strings.

    Byte : Set
    Byte = Nat
    
    ByteString : Set
    ByteString = List Byte

## The exercises

### Compression algorithm

Implement the compression algorithm:

    compress-rle : ByteString → List (Nat × Byte)
    compress-rle = ?

Implementing this algorithm in a language such as Haskell is trivial, however,
in Agda it can be a little bit trickier due the termination checker.

<details>
<summary>Proposed solution</summary>

    rle : Maybe (Nat × Byte) → ByteString → List (Nat × Byte) → List (Nat × Byte)
    rle nothing [] ac = ac
    rle (just (k , b)) [] ac = (k , b) ∷ ac
    rle nothing (x ∷ tail) ac = rle (just (1 , x)) tail ac
    rle (just (k , b)) (x ∷ tail) ac with b ≟ x
    ... | yes p = rle ((just (suc k , b))) tail ac
    ... | no p = rle (just (1 , x)) tail ((k , b) ∷ ac)
    
    compress-rle : ByteString → List (Nat × Byte)
    compress-rle l = rle nothing l []

</details>

### Decompression algorithm

Implement the decompression algorithm:

    decompress-rle : List (Nat × Byte) → ByteString
    decompress-rle = ?

<details>
<summary>Proposed solution</summary>

    dec-step : ByteString → (Nat × Byte) → ByteString
    dec-step = λ ac y → replicate (proj₁ y) (proj₂ y) ++ ac
    
    decompress-rle : List (Nat × Byte) → ByteString
    decompress-rle = foldl dec-step []

</details>


# Verification

The goal of this section is to provide a proof (term) of the following theorem (type):

    inverse-rle : ∀ b → decompress-rle (compress-rle b) ≡ b

The proof will indeed depend on the implementation, so if you want to follow
along you should use the proposed code above.

The proof is not straightforward, so in order to guide the reader we suggest
three lemmas that will lead to the proof. Of course, these lemmas
are not required and you may want to take another road to prove the theorem.

We also suggest that you add the following imports:

    open import Data.List.Properties using (++-identityʳ; ++-assoc)
    open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

### Lemma 1

Prove the following:

    decompress-head : ∀ (l k x) → decompress-rle ((k , x) ∷ l) ≡ decompress-rle l ++ replicate k x
    decompress-head = ?

<details>
<summary class="alert page-subtitle">Proposed solution</summary>

    decompress-head : ∀ (l k x) → decompress-rle ((k , x) ∷ l) ≡ decompress-rle l ++ replicate k x
    decompress-head l k x = trans s1 (s2 l [] k x)
      where
      s1 : decompress-rle ((k , x) ∷ l) ≡ foldl dec-step (replicate k x) l
      s1 rewrite ++-identityʳ (replicate k x) = refl
      s2 : ∀ l ac k x → foldl dec-step (ac ++ replicate k x) l ≡ foldl dec-step ac l ++ replicate k x
      s2 [] ac k x = refl
      s2 ((k1 , x1) ∷ l) ac k x rewrite
          ++-identityʳ (replicate k1 x1)
          | sym (s2 l (replicate k1 x1 ++ ac) k x)
          | ++-assoc (replicate k1 x1) ac (replicate k x)
        = refl

</details>
</div>

### Lemma 2

Prove the following:

    decompress-just : ∀ (k x bs l) → decompress-rle (rle (just (k , x)) bs l) ≡ decompress-rle l ++ (replicate k x ++ bs)
    decompress-just = ?

<details>
<summary>Proposed solution</summary>

    lemma-replicate : ∀ (bs k) (x : Byte) → x ∷ replicate k x ++ bs ≡ replicate k x ++ x ∷ bs
    lemma-replicate bs zero x = refl
    lemma-replicate bs (suc k) x rewrite lemma-replicate bs k x = refl
    
    decompress-just : ∀ (k x bs l) → decompress-rle (rle (just (k , x)) bs l) ≡ decompress-rle l ++ (replicate k x ++ bs)
    decompress-just k x [] l rewrite
       ++-identityʳ (replicate k x)
       | sym (decompress-head l k x)
       | ++-identityʳ (replicate k x)
       = refl
    decompress-just k x (y ∷ bs) ac with x ≟ y
    ... | yes refl rewrite
      decompress-just (suc k) x bs ac
      | lemma-replicate bs k x
      = refl
    ... | no _ rewrite
      decompress-just 1 y bs ((k , x) ∷ ac)
      | ++-identityʳ (replicate k x)
      | sym (++-assoc (foldl dec-step [] ac) (replicate k x) (y ∷ bs))
      | sym (decompress-head ac k x)
      | ++-identityʳ (replicate k x)
      = refl

</details>

### Lemma 3

Prove the following:

    decompress-nothing : ∀ (b ac) → decompress-rle (rle nothing b ac) ≡ decompress-rle ac ++ b
    decompress-nothing = ?

<details>
<summary>Proposed solution</summary>

    decompress-nothing : ∀ (b ac) → decompress-rle (rle nothing b ac) ≡ decompress-rle ac ++ b
    decompress-nothing [] [] = refl
    decompress-nothing [] (x ∷ ac) =  sym (++-identityʳ (decompress-rle (x ∷ ac)))
    decompress-nothing (x ∷ b) ac = decompress-just 1 x b ac

</details>


## Main theorem

With the lemma 3 in hand, it should be trivial to prove the main theorem.

Prove the following:

    inverse-rle : ∀ b → decompress-rle (compress-rle b) ≡ b
    inverse-rle = ?

<details>
<summary>Proposed solution</summary>

    inverse-rle : ∀ b → decompress-rle (compress-rle b) ≡ b
    inverse-rle b = decompress-nothing b []

</details>


# Conclusion

We have implemented and verified the run-length encoding algorithm in Agda and
we have seen that even a simple algorithm is not straightforward to verify.

I am sure that the proposed proof is not the most concise and I think that it
would be a good exercise to try to improve it.

Suggestions are welcome!

