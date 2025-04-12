+++
title = "ASCII fractals in Haskell"
date = 2018-02-20
+++

Getting hypnotized by the shape of a fractal is certainly fascinating. In this
blog, we will write a haskell program that creates fractals from a base pattern.
The recursive nature of the fractals allow a simple implementation in haskell.
In case you don't know what a fractal is, I invite you to take a look at the
[Wikipedia page](https://en.wikipedia.org/wiki/Fractal).

So, let's start coding. First let's write the types for what we want.

```haskell
type Pattern = [[Char]]
fractalize :: Pattern -> Int -> Pattern
render :: Pattern -> String
```

The function `fractalize` takes a base pattern and the number of times that we
want to *augment* it. It returns the resulting fractal.

Given a pattern, let $n, m$ be the number of rows and columns of the base
pattern. We define:

\\[
charAt(k, i, k)=
\begin{cases}
p[i][j], & \text{if } k = 1 \\\\
\text{' '}  & \text{if } charAt(k - 1, \frac{i}n, \frac{j}m) = \text{' '} \\\\
p[i\bmod n][j\bmod m], & \text{otherwise}
\end{cases}
\\]

This function returns the character in the resulting fractal at the specified
position.

Let's translate it into haskell code:

```haskell
fractalize :: Pattern -> Int -> Pattern
fractalize [] _ = []
fractalize pat k = [ [ charAt k i j | j <- [0..m^k - 1] ] | i <- [0..n^k - 1] ]
  where
    n = length pat
    m = length (head pat)
    charAt k i j
      | k <= 1 = pat!!i!!j
      | ' ' == charAt (k - 1) (i`div`n) (j`div`m) = ' '
      | otherwise = pat!!(i`mod`n)!!(j`mod`m)

render :: Pattern -> String
render = unlines
```

Let's try this base pattern:

```haskell
pattern1 :: Pattern
pattern1 = [ " # "
           , "###"
           , " # "]
```
Fractalizing the pattern three times gives:

```
             #
            ###
             #
          #  #  #
         #########
          #  #  #
             #
            ###
             #
    #        #        #
   ###      ###      ###
    #        #        #
 #  #  #  #  #  #  #  #  #
###########################
 #  #  #  #  #  #  #  #  #
    #        #        #
   ###      ###      ###
    #        #        #
             #
            ###
             #
          #  #  #
         #########
          #  #  #
             #
            ###
             #
```

Cool! let's try another pattern!

```haskell
pattern2 :: Pattern
pattern2 = [ "# #"
           , " # "
           , "# #"]
```
Result:
```
# #   # #         # #   # #
 #     #           #     #
# #   # #         # #   # #
   # #               # #
    #                 #
   # #               # #
# #   # #         # #   # #
 #     #           #     #
# #   # #         # #   # #
         # #   # #
          #     #
         # #   # #
            # #
             #
            # #
         # #   # #
          #     #
         # #   # #
# #   # #         # #   # #
 #     #           #     #
# #   # #         # #   # #
   # #               # #
    #                 #
   # #               # #
# #   # #         # #   # #
 #     #           #     #
# #   # #         # #   # #
```

Awesome!

The glue code of our main program is very simple. The number of augments is passed
as an argument to the program.

```haskell
main :: IO ()
main = getK >>= putStr . render . fractalize pattern1
  where getK = read . head <$> getArgs
```

In order to run the example by yourself, get the full code from [here](https://gitlab.com/snippets/1699946) and run:

```
runhaskell fractals.hs 3
```

We are done! Try your base patterns and have fun!


# Final comments

It could be nice to adapt the code to use arrays with constant access time
instead of lists, but for small inputs it is irrelevant.
