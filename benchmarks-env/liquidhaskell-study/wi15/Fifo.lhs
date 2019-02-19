Concurrent FIFO Queue
=====================

<div class="hidden">
\begin{code}
{-# LANGUAGE TypeSynonymInstances, FlexibleContexts, OverlappingInstances, FlexibleInstances #-}

import qualified Data.Map as Map 
import Control.Monad.State
import Control.Monad.Error
import Control.Monad.Writer
import Test.QuickCheck 
import Control.Monad (forM, forM_)
import Data.List (transpose, intercalate)

import qualified Data.Set as Set
import Control.Applicative ((<$>))
import qualified Text.PrettyPrint as PP

import Control.Concurrent
import Control.Concurrent.STM
import Control.Monad
import System.Exit
import System.IO.Unsafe
import Data.IORef

quickCheckN n = quickCheckWith $ stdArgs { maxSuccess = n}
\end{code}
</div>


In this question, we'll develop a concurrently-accessible
first-in, first-out (FIFO) queue with a fixed capacity, 
called a finite channel.[^channelnote] Your finite channel 
will behave as follows: If a read occurs when the queue 
is empty, the reader should block until an item becomes 
available. Similarly, if a write occurs when the queue is full 
(i.e., the number of items in the queue is the capacity 
specified when the queue was created), the writer should 
block until an item is removed from the queue.

[^channelnote]: This question is based on homeworks 10 and 11 from
Benjamin Pierce's 
[Advanced Programming](http://www.cis.upenn.edu/~bcpierce/courses/552-2008/index.html)
class at UPenn.

Before defining any operations on your finite channel, you need to
change the representation of finite channels from the following
obviously incorrect one:

\begin{code}
data FiniteChan a = Chan ()
\end{code}

Next, define an operation for creating a finite channel of a
particular capacity:

\begin{code}
newFiniteChan :: Int -> IO (FiniteChan a)
newFiniteChan capacity = error "TODO"
\end{code}

Next, define the operation for reading from the queue:

\begin{code}
readFiniteChan :: FiniteChan a -> IO a
readFiniteChan t = error "TODO"
\end{code}

Remember that reads should block in the case where the channel is
empty.

Finally, define the operation for writing to the queue:

\begin{code}
writeFiniteChan :: FiniteChan a -> a -> IO ()
writeFiniteChan t x = error "TODO"
\end{code}

Remember that writes should block in the case where the channel is at
capacity.

Below are some tests that exercise your channel abstraction. You should
run the `testFiniteChannel' function at the very end to ensure that all
of the tests pass.

First, we define a debugging output function for tracing the execution
of the tests. Uncomment out the second version if you need more information
to diagnose errors.

\begin{code}
dbg s = do return ()
-- dbg s = do id <- myThreadId;  putStrLn $ "[" ++ (show id) ++ "] " ++ s
\end{code}

Various test parameters and utilities follow.

\begin{code}
rounds = 1000

delayUnit = 1000*200 -- 0.2 seconds

assert b s = 
  if b then return () else do
  putStrLn $ "assertion failed: " ++ s
  exitWith (ExitFailure 1)

beginTest s = putStrLn $ "Starting test procedure: " ++ s

endTest = do
  putStrLn "Test passed"
  putStrLn ""

newFC x = do
  dbg $ "newFiniteChan " ++ (show x) ++ " called"
  c <- newFiniteChan x
  dbg $ "newFiniteChan " ++ (show x) ++ " returned"
  return c

readFC c = do
  dbg $ "readFiniteChan called"
  x <- readFiniteChan c
  dbg $ "readFiniteChan returned, result=" ++ (show x)
  return x

writeFC c x = do
  dbg $ "writeFiniteChan " ++ (show x) ++ " called"
  writeFiniteChan c x
  dbg $ "writeFiniteChan " ++ (show x) ++ " returned"
\end{code}

The first test fills and empties the queue twice, checking that FIFO
order is respected.

\begin{code}
test1 = forM [1..5] $ \i -> test1a i

test1a x = do
  beginTest $ "test1:"++(show x)
  fc <- newFC x
  forM [1..x] $ \i-> writeFC fc i
  forM [1..x] $ \i-> do
    j <- readFC fc
    assert (i==j) "FIFO order not respected"

  forM [x+1..2*x] $ \i-> writeFC fc i
  forM [x+1..2*x] $ \i-> do
    j <- readFC fc
    assert (i==j) "FIFO order not respected"
  endTest
\end{code}

The second test is a simple two-thread producer/consumer setup, again
testing for FIFO semantics.

\begin{code}
test2 = forM [1..5] $ \i -> test2a i

test2a size = do
  beginTest $ "test2:"++(show size)
  fc <- newFC size
  forkIO (producer fc)
  consumer fc
  forkIO (consumer fc)
  producer fc
  endTest
 where
  producer fc = do
    forM [1..rounds] $ \i-> do
      writeFC fc i
    return ()
  consumer fc = do
    forM [1..rounds] $ \i-> do
      j <- readFC fc
      assert(i==j) "FIFO order not respected"
    return ()
\end{code}

The third test checks that, if the consumer is slow, the queue will
always be full when it's read, and also that the producer is not
allowed to insert more items into the queue than its capacity should
allow.

\begin{code}
test3 = forM [1..5] $ \i -> test3a i

test3a size = do
  beginTest $ "test3:"++(show size)
  fc <- newFC size
  forkIO (producer fc)
  consumer fc
  endTest
 where
  counter = unsafePerformIO (newMVar 0)
  producer fc = do
    forM [1..rounds] $ \i-> do
      writeFC fc i
      modifyMVar_ counter $ \c-> do
        -- putStrLn $ (show c) ++ "<" ++ (show size)
        assert (c<size) "Queue size not within limit"
        return (c+1)
    return ()
  consumer fc = do
    forM [1..10] $ \i-> do
      threadDelay delayUnit
      modifyMVar_ counter $ \c-> do
         -- putStrLn $ (show c) ++ "<=" ++ (show size)
         assert (c==size) "Queue should always be full with a slow reader"
         return (c-1)
      j <- readFC fc
      assert(i==j) ""
    return ()
\end{code}

The fourth test is like the third, except its checks that, with a slow
producer, the queue is always empty when it's written to.

\begin{code}
test4 = forM [1..5] $ \i -> test4a i

test4a size = do
  beginTest $ "test4:"++(show size)
  fc <- newFC size
  forkIO (consumer fc)
  producer fc
  endTest
 where
  counter = unsafePerformIO (newMVar 0)
  producer fc = do
    forM [1..5] $ \i-> do
      threadDelay delayUnit
      modifyMVar_ counter $ \c-> do
        -- putStrLn $ (show c) ++ "<" ++ (show size)
        assert (c==0) "Queue should always be empty with a slow writer"
        return (c+1)
      writeFC fc i
    return ()
  consumer fc = do
    forM [1..rounds] $ \i-> do
      j <- readFC fc
      assert(i==j) ""
      modifyMVar_ counter $ \c-> do
         -- putStrLn $ (show c) ++ "<=" ++ (show size)
         assert (c<=size) "Queue size not within limit"
         return (c-1)
    return ()
\end{code}

The fifth test checks the behavior of multiple producers and
consumers.

\begin{code}
test5 = forM [1..5] $ \i -> test5a i

test5a size = do
  beginTest $ "test5:"++(show size)
  fc1 <- newFC size
  fc2 <- newFC 1
  forM [1..nums] $ \_ -> forkIO (producer fc1)
  forM [1..nums] $ \_ -> forkIO (consumer fc1 fc2)
  s <- newIORef 0
  forM [1..(nums*rounds)] $ \_ -> do
    i <- readFC fc2
    modifyIORef s (+i)
  result <- readIORef s
  assert (result== nums * (sum [1..rounds])) "total sent <> total received"
  endTest
 where
  nums = 10 
  producer fc = do
    forM [1..rounds] $ \i -> writeFC fc i
    return ()
  consumer fc1 fc2 = do
    forM [1..rounds] $ \_ -> do
      i <- readFC fc1
      writeFC fc2 i
    return ()
\end{code}

The sixth test is like the third, this time with multiple producer
threads.

\begin{code}
test6 = forM [1..5] $ \i -> test6a i

test6a size = do
  beginTest $ "test6:"++(show size)
  fc <- newFC size
  forM [1..5] $ \_ -> forkIO (producer fc)
  consumer fc
  endTest
 where
  counter = unsafePerformIO (newMVar 0)
  producer fc = do
    forM [1..rounds] $ \i-> do
      writeFC fc i
      modifyMVar_ counter $ \c-> do
        -- putStrLn $ (show c) ++ "<" ++ (show size)
        assert (c<size) "queue size not within limit"
        return (c+1)
    return ()
  consumer fc = do
    forM [1..10] $ \i-> do
      threadDelay delayUnit
      modifyMVar_ counter $ \c-> do
         -- putStrLn $ (show c) ++ "<=" ++ (show size)
         assert (c==size) "queue should always be full with slow reader"
         return (c-1)
      readFC fc
    return ()
\end{code}

The final test is like the fourth, but with multiple consumer threads.

\begin{code}
test7 = forM [1..5] $ \i -> test7a i

test7a size = do
  beginTest $ "test7:"++(show size)
  fc <- newFC size
  forM [1..5] $ \_-> forkIO (consumer fc)
  producer fc
  endTest
 where
  counter = unsafePerformIO (newMVar 0)
  producer fc = do
    forM [1..10] $ \i-> do
      threadDelay delayUnit
      modifyMVar_ counter $ \c-> do
        -- putStrLn $ (show c) ++ "<" ++ (show size)
        assert (c==0) "queue should always be empty with slow writer"
        return (c+1)
      writeFC fc i
    return ()
  consumer fc = do
    forM [1..rounds] $ \i-> do
      j <- readFC fc
      modifyMVar_ counter $ \c-> do
         -- putStrLn $ (show c) ++ "<=" ++ (show size)
         assert (c<=size) "queue size not within limit"
         return (c-1)
    return ()

testFiniteChannel = do
  test1
  test2
  test3
  test4
  test5  
  test6
  test7
\end{code}


