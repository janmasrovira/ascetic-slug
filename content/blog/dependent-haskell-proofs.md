+++
title = "Using dependent types to write proofs in Haskell"
date = 2021-06-02
+++

**Target audience**: This blog is meant for intermediate/advanced Haskell
readers, specially those interested in logic. If you are new to Haskell, this
blog will probably not be easy to follow.

# Overview

We all know that we can use Haskell to write functional programs that compute
stuff. But can we also use Haskell to write mathematical proofs? Yes!

In case you have never been exposed to dependent types, the concept of writing
proofs with a programming language will surely sound alien to you. In this
blog I hope to give you an informal introduction to dependent types in Haskell
that will allow you to understand what does it mean to prove something in
Haskell and how to do it. I strongly recommend that you follow along with ghci
on your side.

**Clarification**. At the time of writing this, GHC does *not* have full
dependent types, however, as we will see, it has some features that allow us to
get pretty close to them. If you are looking for a language with full dependent
types I suggest that you look into [Agda](https://github.com/agda/agda) or
[Lean](https://lean-lang.org/). In this TODO LINK EDSL other blog I present an
Agda implementation of a type safe domain specific language to write Hilbert
style proofs. Also, GHC should *not* be used as a serious proof assistant,
because, as we will see in this blog, it is very easy to prove false statements
in it.

You can find all related code to what I will present in this [gitlab repository](https://gitlab.com/janmasrovira/dependent-haskell ).

# Extensions

In order to get close to dependent types we need the help of some GHC extensions.
If you want to follow along, make sure to have the following extensions
enabled in ghci. I will comment on some of them when they become relevant to
the code I'm showing. Note that each extension links to the corresponding GHC
manual page.

-   [`GADTs`](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/gadt.html). Allow use of Generalised Algebraic Data Types (GADTs).
-   [`ScopedTypeVariables`](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/scoped_type_variables.html#extension-ScopedTypeVariables). Enable lexical scoping of type variables explicitly
    introduced with `forall`.
-   [`DataKinds`](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/data_kinds.html). Allow promotion of data types to kind level.
-   [`PolyKinds`](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/poly_kinds.html#extension-PolyKinds). Allow kind polymorphic types.
-   [`TypeFamilies`](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/type_families.html). Allow use and definition of indexed type and data families.
-   [`TypeOperators`](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/type_operators.html#extension-TypeOperators). Allow the use and definition of types with operator names.
-   [`UndecidableInstances`](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/instances.html#extension-UndecidableInstances). Permit definition of instances which may lead to
    type-checker non-termination.


# Equality on types

All proofs which I will present in this blog are proofs of equality. In fact,
we will only show theorems which can be expressed in a formula of the form
$$∀x₁…∀xₙ(t₁ ⇒ … ⇒ tₘ ⇒ r = s),$$ where $xᵢ$ are type variables and
$t₁,…,tₘ,r,s$ are types. So a first obvious step should be to define a type in
Haskell which expresses type equality (according to the rules of GHC). We
should agree that a the following header is a good place to start.

```haskell
data Equal a b where
   ...
```

Now we should provide a constructor for this datatype. Of course, the
constructor should be a witness that `a` and `b` are equal.
So we can define the desired constructor like this:

```haskell
data Equal a b where
  Witness :: (a ~ b) => Equal a b
```

Recall that the constraint `a ~ b` means precisely what we want. Namely, that
`a` and `b` are equal types according to GHC.

However, we are going to use an alternative definition, which is slightly
simpler and is already defined in [`base:Data.Type.Equality`](https://hackage.haskell.org/package/base-4.15.0.0/docs/Data-Type-Equality.html):

```haskell
    data a :~: b where
      Refl :: a :~: a
```

Don't get confused by the infix notation of `:~:`. It serves the same purpose
as `Equal`, but with infix notation (see [`TypeOperators`](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/type_operators.html#extension-TypeOperators)). The constructor is
named `Refl` for *Reflexivity*.

We are ready to write our first proof. Let us show that the equality relation
defined above is symmetric. Recall that in mathematics we say that a relation
$R$ is symmetric iff $∀x∀y(xRy⇒yRx)$.

Our next job is to find a type which faithfully represents the symmetry
proposition. Let's use the following type.

```haskell
sym :: (x :~: y) -> (y :~: x)
```

First we need to convince ourselves that the type `(x :~: y) -> (y :~: x)`
faithfully represents a proposition stating the property of symmetry. In fact
if we use explicit quantification for `x` and `y` and we interpret the
function type (`->`) as an implication, it looks exactly like the mathematical
statement:

\\[ ∀x∀y(xRy⇒yRx)
\\]

```haskell
forall x y. (x :~: y) -> (y :~: x)
```

Now, if we can find a Haskell term which has the above type we will have a
term such that given any `x` and `y` and a proof of `x :~: y`, will return
a proof of `y :~: x`. If such term exists, it should be clear that the
proposition is true and thus we should accept that term as a proof! In
fact, this interpretation of a proof corresponds precisely to the BHK
interpretation. If you want to read more on the BHK interpretation I suggest
this [Stanford Encyclopedia article](https://plato.stanford.edu/entries/intuitionistic-logic-development/#ProoInte).

On we go to find a suitable term (proof)! We see that `(x :~: y) -> (y :~: x)`
is a function type with one argument, so a good place to start would be this:

```haskell
sym :: (x :~: y) -> (y :~: x)
sym p = _
```

If we load this into ghci it will tell us that it has found a hole:

```
Found hole: _ :: y :~: x
```

How can we fill this hole? Well, the only way to build something of type `y
  :~: x` is by using the constructor `Refl`, but doing that would give us either
`x :~: x` or `y :~: y`, which is not what we want. So we are only left with
the option to pattern match against `p`. Here the type of the constructor
`Refl` will play a crucial role. Let's proceed by asking ghci about its type.

```
ghci> :t Refl
ghci> Refl :: forall k (a :: k). a :~: a
```

What this says is: For any kind `k` and for any type `a` of kind `k` we have a
term of type `a :~: a`. We can think of a kind as the type of a type. I will
go back to types and kinds later in this section.

Let's reload the code after replacing `p` by `Refl`. Note
that I write `p@Refl` so it is easier for me to refer to this specific `Refl`
in the text, but we could simply drop `p@` to the same effect.

```haskell
sym :: (x :~: y) -> (y :~: x)
sym p@Refl = _
```

Now we get that there is still a hole, but now it has type `x :~: x` instead
of `y :~: x`.

```
Found hole: _ :: x :~: x
```

We see that because of pattern matching and the type of `Refl`, GHC has
unified the type variables `x` and `y`. Why? well, we know that before pattern
matching we had `p : x :~: y`. Then we have that `p@Refl : x :~: y`, and
therefore by the type of the constructor `Refl` it must be that `x ~ y`.

Filling the hole and thus finishing the proof is trivial! We only need to
return the `Refl` constructor, which is a suitable term of the desired type `x
  :~: x`.

```haskell
sym :: (x :~: y) -> (y :~: x)
sym Refl = Refl
```

Yay! we finished our first proof! However, there is one critical condition for
a proof that we haven't yet commented: termination. In the case of `sym`,
it obviously terminates for any input, since we just return the constructor
`Refl`. However, as proofs get more complicated and we need to perform
induction (as we will see in the TODO LINK natural numbers section), it is easy to end up
writing a well typed term that will not terminate on some inputs. If a term
does not terminate on some inputs, then it obviously cannot be taken as a
proof. Unfortunately, we are on our own because GHC does not perform any kind
of termination checking for terms. As an example of a well typed but
non-terminating term consider the following definition:

```haskell
anyProof :: forall a. a
anyProof = anyProof
```

Of course, we should always be very careful not to introduce a non-terminating
(pseudo)proof, as the proof may be accepted by GHC and will lead us to believe
that we have proven something which may be false.

As a simple exercise, I propose that you try to prove that `:~:` is a
transitive relation. In Haskell terms, this means that you ought to find a
suitable definition for this type signature.

```haskell
trans :: (x :~: y) -> (y :~: z) -> (x :~: z)
```

*Hint: The proof is really similar to the proof of `sym`*. After you have
proven this, you will have proven that `:~:` is symmetric, transitive and
reflexive (this property is given directly by the constructor `Refl`). Thus
you can conclude that `:~:` is an equivalence relation, which is the minimum
requirement a definition of equality should satisfy.

We end this section by summarizing the steps we should follow when writing a
proof in Haskell.

1.  Write a type which represents the proposition that we want to prove.
2.  Find a term that has that type. GHC makes sure that this step is correct
    by type checking the term.
3.  Make sure (outside of GHC/in our meta reasoning) that the given term in the
    previous step terminates for any input. If it doesn't, we do not have a
    valid proof.
4.  Feel good.


## A note on types and kinds

This section is a small parenthesis on types and kinds. It is a bit technical
and tangential to the main topic so you may want to skip it on a first read.

If we inspect closely the type of `sym :: forall x y. (x :~: y) -> (y :~:
   x)`, one may ask the questions: what are `x` and `y`? They are not defined
anywhere, yet we can use them? The answer lies in the fact that GHC types are
not fully explicit most of the time. Consider the identity function type:

```haskell
id :: a -> a
```

We could have raised a similar question by looking at this type. If we rewrite
the previous type more explicitly, we would have:

```haskell
id :: forall a. a -> a
```

We see that we universally quantify a type variable `a`. But still this is not
fully explicit. One could ask: What is the type of `a`? Or in GHC terms, what
is the kind of `a`? Let's rewrite the type to make it even more explicit.

```haskell
id :: forall k (a :: k). a -> a
```

Ok, we have solved the problem for `a`. Now we know that `a` has kind `k`.
But what is the kind of `k`? We need to make it more explicit one last time.

```haskell
-- Type is imported from Data.Kind
id :: forall (k :: Type) (a :: k). a -> a
```

But how can it be that type of a kind `k` is `Type`? This is because in GHC
we have the axiom `Type :: Type`. This may raise some eyebrows since in the
field of logic typing relations which include at least a reflexive element,
such as `Type :: Type`, are well known to lead to inconsistent logics, and
thus are undesirable (if this topic is intriguing to you, I suggest that you
read the article on the [Russell's Paradox](https://plato.stanford.edu/entries/russell-paradox/) in the Stanford Encyclopedia).
However, GHC allows `Type :: Type` because it has certain advantages. Moreover,
inconsistencies are present even without it. This makes sense because GHC is
not meant to be used as a proof assistant. In the paper [System FC with
Explicit Kind Equality](https://www.seas.upenn.edu/~sweirich/papers/fckinds.pdf), Weirich, Hsu and Eisenberg argue that having the
`Type :: Type` axiom does not break GHC's type system.

If you want to know how the paradox has been avoided in a programming
language with dependent types, I suggest that you look into the Agda
documentation for [universe levels](https://agda.readthedocs.io/en/latest/language/universe-levels.html).

There is **a lot** more to types and kinds in GHC than what I have written (and
probably a significant portion escapes my knowledge at this point in time).
If you wish to know more, I suggest some references:

-   The paper [System FC with Explicit Kind Equality](https://www.seas.upenn.edu/~sweirich/papers/fckinds.pdf).
-   GHC wiki article [type type](https://gitlab.haskell.org/ghc/ghc/-/wikis/commentary/compiler/type-type).
-   Documentation for [`DataKinds`](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/data_kinds.html).
-   Documentation for [`PolyKinds`](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/poly_kinds.html#extension-PolyKinds).
-   Proposal for [unlifted data types](https://gitlab.haskell.org/ghc/ghc/-/wikis/unlifted-data-types).


# Proofs on natural numbers

Finally something that is more tangible: natural numbers. As we know, a
natural numbers are the elements of the infinite sequence $0,1,2,3,…$. We will
begin by providing a Haskell inductive definition for them.

```haskell
data Nat where
  Zero :: Nat
  Suc :: Nat -> Nat
```

We can define particular naturals as expected:

```haskell
one :: Nat
one = Suc Zero

two :: Nat
two = Suc one
...
```

Say that we want to prove that `one + one = two`. It should be pretty
straightforward right? Well, we have seen that we need to use types to express
propositions. But `one` and `two` are terms, so we can not use them in a type.
Moreover, how do we define addition on the type level?

In order to solve this problem we will use some help from the [`DataKinds`](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/data_kinds.html)
extension. This extension promotes type constructors, such as `Nat`, to kinds.
Likewise, the extension promotes constructors, such as `Zero` and
`Suc`, to type constructors. Note that when we want to refer to a promoted
constructor we should prefix it with an apostrophe `'`. Now we can define
naturals on the type level thus:

```haskell
type One = 'Suc 'Zero
type Two = 'Suc One
```

The first part of the problem is solved. We now need to define addition on the
promoted kind `Nat`. We can do so with the help of the [`TypeFamilies`](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/type_families.html)
extension. With this extension we can define *type families*, which
approximately are Haskell functions on types.

First let's define addition on terms as we would normally do. This is only to
have a point of reference.

```haskell
(+) :: Nat -> Nat -> Nat where
Zero + b = b
(Suc a) + b = Suc (a + b)
```

And now see how we can translate the previous definition to type families.

```haskell
type family (a :: Nat) :+: (b :: Nat) :: Nat where
 'Zero :+: b = b
 'Suc a :+: b = 'Suc (a :+: b)
```

One can observe that both definitions look quite alike. In fact, they would be
exactly the same definition if we had full dependent types in GHC.

Let's try an example. Notice that the we need a `!` in `:k!` in order to ask
ghci to give us the normalized type.

```
ghci> :k! ('Suc 'Zero) :+: ('Suc 'Zero)
ghci> ('Suc 'Zero) :+: ('Suc 'Zero) :: Nat
ghci> = 'Suc ('Suc 'Zero)
```

Neat! We are finally ready to express in a type the property `one + one =
  two` and prove it.

```haskell
onePlusOne :: (One :+: One) :~: Two
onePlusOne = Refl
```

It suffices to use reflection since both types `One :+: One` and `Two`
normalize to `'Suc ('Suc 'Zero)`.

Let's prove another property: `n + zero = n`.

```haskell
nPlusZero :: (n :+: 'Zero) :~: n
nPlusZero = Refl
```

But now we get an error!

```
Couldn't match type ‘n’ with ‘n :+: 'Zero’
```

The problem is that `n :+: 'Zero` cannot be normalized further. This is
because when we defined `:+:` we pattern matched the left argument, but now we
have `'Zero` on the right. Hence the expected way to proceed is to pattern match
on `n`. Unfortunately, we cannot pattern match on types directly so we
need to figure something out.

The strategy is to define a data type which will serve as a bridge between the
terms universe and the types universe.

```haskell
data SNat (n :: Nat) where
  SZero :: SNat 'Zero
  SSuc :: SNat n -> SNat ('Suc n)
```

The new data type `SNat` which we just defined has the same structure as a
`Nat`, but it is indexed by a `Nat` on the type level. Note that the `n` in the
first line is **not** a term of type `Nat`. Instead, `n` is a type variable of
kind `Nat`. With the help of
[`GADTs`](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/gadt.html), we
can use the promoted constructors `'Zero` and `'Suc` to create the desired link
between terms and types. The following theorem makes such a link explicit.

**Theorem**. *For any type `n` of kind `Nat`, the type `SNat n` has exactly one term*.

We prove it by induction on `n`.

-   Base case `n` = `'Zero`.
    
    By definition `SZero :: SNat 'Zero`. To see that `SZero` is the only term of
    type `SNat 'Zero`, assume that there is a term `b :: SNat 'Zero`. We
    continue by cases on `b`. If `b` is `SZero` we are done. Otherwise `b` is of
    the form `SSuc _`, but then `b`'s type must be of the form `SNat ('Suc _)`,
    which is a contradiction.
-   Inductive case `n` = `'Suc m`.
    
    By induction hypothesis we have that there exists exactly one term `i` such
    that `i :: SNat m`. Then we have that `SSuc i :: SNat ('Suc m)`. Now assume
    that there is a term `j :: SNat ('Suc m)`. From the type we know that `j` is
    of the form `SSuc k` and `k :: SNat m`. Then by the induction hypothesis we
    have that `i` = `k`. Therefore `j` = `SSuc i`.
    
    Qed.

Because of the previous property we call the type `SNat` a *singleton type*.
If you want a more extensive introduction to singleton types, I recommend [this
blog](https://blog.jle.im/entry/introduction-to-singletons-1.html) by Justin Le.

We can now use the singleton type `SNat` to pattern match on types of kind
`Nat`.

```haskell
nPlusZero :: SNat n -> (n :+: 'Zero) :~: n
nPlusZero SZero = _
nPlusZero (SSuc m) = _
```

After loading the previous code into ghci we get the following information:

-   For the base case (first hole):
    ```
    Found hole: _ :: 'Zero :~: 'Zero
    ```     
    This hole can be trivially proven with `Refl`.
-   For the inductive case (second hole):
    ```
    Found hole: _ :: 'Suc (n1 :+: 'Zero) :~: 'Suc n1
    ```
    
    We see that we need to prove an equality of the form `'Suc a :~: 'Suc b`,
    and this equality is implied by `a :~: b`. Let's prove this fact as an
    auxiliary lemma.
    ```haskell
    congSuc :: a :~: b -> 'Suc a :~: 'Suc b
    congSuc Refl = Refl
    ```
    
    We see that `congSuc` is a very simple lemma that can be proved in the same
    way we proved `sym`.
    
    In order to use the previous lemma we only need to apply it as a regular
    function.
    ```haskell
    nPlusZero :: SNat n -> (n :+: 'Zero) :~: n
    nPlusZero SZero = Refl
    nPlusZero (SSuc m) = congSuc _
    ```
    
    After applying `congSuc` the hole becomes:
    ```
    Found hole: _ :: (n1 :+: 'Zero) :~: n1
    ```
    
    It worked, the hole type became simpler! In fact, it looks much like the
    property that we wanted to prove initially. This is often telling us that we
    need to apply the induction hypothesis. Applying the induction hypothesis is
    as simple as doing a recursive call to the theorem that we are proving.
    ```haskell
    nPlusZero :: SNat n -> (n :+: 'Zero) :~: n
    nPlusZero SZero = Refl
    nPlusZero (SSuc m) = congSuc (nPlusZero m)
    ```

We have finished our first proof by induction! Now imagine that we want to use
the previous theorem in another proof. In particular, imagine that we need to
fill a goal of type `SNat a -> SNat b -> (a :+: b) :+: 'Zero`. It is clear
that the strategy should be to instantiate the `n` in the lemma `nPlusZero` as
`a :+: b`, but then we should provide an argument of type `SNat (a :+: b)`.
We can achieve that by implementing addition for the type `SNat` as follows.

```haskell
(.+.) :: SNat a -> SNat b -> SNat (a :+: b)
SZero .+. b    = b
SSuc a .+. b = SSuc (a .+. b)
```

Finally we can use the theorem `nPlusZero` thus:

```haskell
someThm :: SNat a -> SNat b -> (a :+: b) :+: 'Zero
someThm a b = nPlusZero (a .+. b)
```

At this point I have given you
enough tools so that you can start writing your own proofs.


## Exercises

Below I provide a list of theorems that you may want to prove as practice. If
you get stuck you can refer to my solutions in [this repository](https://gitlab.com/janmasrovira/dependent-haskell), specifically
[this file](https://gitlab.com/janmasrovira/dependent-haskell/-/blob/master/src/Nats.hs). I wrote these solutions about 3 years ago when I was still a complete
novice at writing proofs. So it is likely that you will find better proofs.

In order to solve the exercises you will need the following definitions.

```haskell
type family (a :: Nat) :*: (b :: Nat) :: Nat where
  'Zero :*: b = 'Zero
  'Suc a :*: b = b :+: (a :*: b)

type family (a :: Nat) :^: (b :: Nat) :: Nat where
  a :^: 'Zero = 'Suc 'Zero
  a :^: 'Suc b = a :*: (a :^: b)
```

Exercise list.

1. ```haskell 
   plusSucR :: forall a b. SNat a -> SNat b -> (a :+: 'Suc b) :~: 'Suc (a :+: b)
   ```

2. ```haskell
   plusAssoc :: forall a b c. SNat a -> SNat b -> SNat c -> (a :+: b) :+: c :~: a :+: (b :+: c)
   ```

3.  ```haskell
    plusCommut :: forall a b. SNat a -> SNat b -> (a :+: b) :~: (b :+: a)
    ```
4.  ```haskell
    prodZeroL :: SNat n -> 'Zero :*: n :~: 'Zero
    ```
5.  ```haskell
    prodZeroR :: SNat sn -> (sn :*: 'Zero) :~: 'Zero
    ```
6.  ```haskell
    prodOneL :: SNat sn -> (One :*: sn) :~: sn
    ```
7.  ```haskell
    prodOneR :: SNat sn -> (sn :*: One) :~: sn
    ```
8.  ```haskell
    prodSucL :: forall a b. SNat a -> SNat b -> ('Suc a :*: b) :~: b :+: (a :*: b)
    ```
9.  ```haskell
    prodSucR :: forall a b. SNat a -> SNat b -> (a :*: 'Suc b) :~: a :+: (a :*: b)
    ```
10. ```haskell
    prodDistribR :: forall a b c. SNat a -> SNat b -> SNat c 
        -> (a :+: b) :*: c :~: (a :*: c) :+: (b :*: c)
    ```
11. ```haskell
    prodDistribL :: forall a b c. SNat a -> SNat b -> SNat c -> 
       a :*: (b :+: c) :~: (a :*: b) :+: (a :*: c)
    ```
12. ```haskell
    prodAssoc :: forall a b c. SNat a -> SNat b -> SNat c 
        -> (a :*: b) :*: c :~: a :*: (b :*: c)
    ```
13. ```haskell
    prodCommut :: forall a b. SNat a -> SNat b -> (a :*: b) :~: (b :*: a)
    ```
14. ```haskell
    powerZero :: a :^: 'Zero :~: One
    ```

15. ```haskell
    powerOne :: SNat a -> a :^: One :~: a
    ```

16. ```haskell
    prodPower :: forall a b c. SNat a -> SNat b -> SNat c 
        -> (a :^: b) :*: (a :^: c) :~: a :^: (b :+: c)
    ```
17. ```haskell
    powerProd :: forall a b c. SNat a -> SNat b -> SNat c 
        -> (a :^: c) :*: (b :^: c) :~: (a :*: b) :^: c
    ```

# Proofs on lists

More exercises for lists.

You will need some common functions on lists on the type level.

```haskell
type family Length (l :: [*]) :: Nat where
  Length '[] = 'Zero
  Length (_':r) = 'Suc (Length r)

type family (a :: [*]) :++: (b :: [*]) :: [*] where
  '[] :++: b = b
  (a ': as) :++: b = a : (as :++: b)

type family Reverse (a :: [*]) :: [*] where
  Reverse '[] = '[]
  Reverse (a ': as) = Reverse as :++: '[a]
```

A singleton list type can be defined thus:

```haskell
data HList (l :: [*]) :: * where
  HNil :: HList '[]
  HCons :: t -> HList l -> HList (t ': l)
```

List of exercises.

1. ```haskell
   concatNilL :: '[] :++: a :~:  a
   ```
2. ```haskell
   concatNilR :: HList a -> a :++: '[] :~: a
   ```
3. ```haskell
   lengthCons :: HList a -> Length (t ': a) :~: 'Suc (Length a)
   ```
4. ```haskell
   lengthConcat :: HList a -> HList b -> Length a :+: Length b :~: Length (a :++: b)
   ```
5.  ```haskell
    concatAssoc :: forall a b c.  HList a -> HList b -> HList c
        -> (a :++: b) :++: c :~: a :++: (b :++: c)
    ```
          
6. ```haskell
   lengthConcatCommut :: forall a b. HList a -> HList b
       -> Length (a :++: b) :~: Length (b :++: a)
   ```
7. ```haskell
   lengthReverse :: HList a -> Length (Reverse a) :~: Length a
   ```
8. ```haskell
   concatReverse :: forall a b . HList a -> HList b
       -> Reverse a :++: Reverse b :~: Reverse (b :++: a)
   ```
9.  ```haskell
    consReverse :: forall a t. HList a -> t ': Reverse a :~: Reverse (a :++: '[t])
    ```
10. ```haskell 
    reverseReverse :: forall a. HList a -> Reverse (Reverse a) :~: a
    ```

# Singletons library

If you plan on using singleton types on your projects, you should definitely
look into the [`singletons`](https://hackage.haskell.org/package/singletons) library. According to its documentation,
*`singletons` contains the basic types and definitions needed to support
dependently typed programming techniques in Haskell.* Additionally, it is very
convenient to combine it with [`singletons-th`](https://hackage.haskell.org/package/singletons-th) library, which will
automatically generate a lot of boilerplate code for you. For instance, in
order to define the natural numbers we needed to define `Nat` and `SNat`. The
latter can be automatically generated by `singletons-th`. Moreover, when
defining addition we needed to define `:+:` on the type level for the kind
`Nat` and `.+.` on the singleton term level for `SNat`. Again, with the
`singletons-th` library, we could automatically generate both `:+:` and `.+.`
from the simple definition of `+` on the type `Nat`.

Giving a detailed introduction to the `singletons` library is out of the scope
of this blog. For that, I recommend the [`Readme` of the `singletons` library](https://github.com/goldfirere/singletons/blob/master/README.md)
and (again) [this blog](https://blog.jle.im/entry/introduction-to-singletons-1.html) by Justin Le.


# Useful references

If you want to know more or you want different takes on this topic, I would
suggest that you look into these references.

-   [An introduction to typeclass metaprogramming](https://lexi-lambda.github.io/blog/2021/03/25/an-introduction-to-typeclass-metaprogramming/) by Alexis King.
-   [Tweag youtube channel](https://www.youtube.com/channel/UCI1Z201n-8OelkSg0DVOsng) featuring Richard Eisenberg.
-   [Basic Type Level Programming in Haskell](https://www.parsonsmatt.org/2017/04/26/basic_type_level_programming_in_haskell.html) by Matt Parsons.
-   [nLab: propositions as types](https://ncatlab.org/nlab/show/propositions+as+types) (not Haskell, more theoretical).
-   If you know of a nice reference which is missing here, let me know and I'll
    add it.


# Final words

I hope you found this interesting. If you find any mistake, please let me know.


