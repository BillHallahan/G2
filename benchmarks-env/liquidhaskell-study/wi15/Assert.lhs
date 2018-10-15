Assertions
==========

<div class="hidden">
\begin{code}
module Assert (die, fixme, lAssert, divide) where

divide     :: Double -> Int -> Double
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-termination" @-}
\end{code}
</div>

As a warm up, first lets recall how we can specify and verify *assertions*
with Refinement Types.

Dead Code
---------

Recall from lecture, that we can define a function that should *never* be called.

\begin{code}
{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)
\end{code}

We can use this function in all those places where we need to handle some case that we
can know (and want to prove) will never happen at run-time.

Here's a variant of `die` that we will use for those places where *you* need to fill in code:
\begin{code}
{-@ fixme :: {v:String | false} -> a @-}
fixme str = error ("Oops, you didn't fill in the code for: "++ str)
\end{code}


Assertions
----------

Lets define a refined type for the `Bool` that is *always* true:

\begin{code}
{-@ type TRUE = {v:Bool | v} @-}
\end{code}

Notice that we can now assign the type `TRUE` to any `Bool` expression
that is guaranteed to evaluate to `True`:

\begin{code}
{-@ one_plus_one_eq_two :: TRUE @-}
one_plus_one_eq_two = (1 + 1 == 2)
\end{code}

But of course, not to expressions that are `False`:

\begin{code}
{-@ one_plus_one_eq_three :: TRUE @-}
one_plus_one_eq_three = (1 + 1 == 3)  -- TYPE ERROR
\end{code}

We can now use `TRUE` to define a `lAssert` function:

\begin{code}
{-@ lAssert :: TRUE -> TRUE @-}
lAssert True  = True
lAssert False = die "Assert Fails!"
\end{code}

Now, we can call `lAssert` only on expressions that we want to prove
always hold, for example:

\begin{code}
propOk   = lAssert (1 + 1 == 2)
\end{code}

But if we try to `lAssert` bogus facts then they are rejected:

\begin{code}
propFail = lAssert (1 + 1 == 3) -- TYPE ERROR
\end{code}

Divide By Zero
--------------

Finally, lets write a *safe* divide by zero operator (that we will use later)

\begin{code}
{-@ divide :: Double -> {v:Int | v /= 0}-> Double @-}
divide n 0 = die "oops divide by zero"
divide n d = n / (fromIntegral d)
\end{code}
