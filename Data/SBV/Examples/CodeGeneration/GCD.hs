-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.CodeGeneration.GCD
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Computing GCD symbolically, and generating C code for it. This example
-- illustrates symbolic termination related issues when programming with
-- SBV, when the termination of a recursive algorithm crucially depends
-- on the value of a symbolic variable. The technique we use is to statically
-- enforce termination by using a recursion depth counter.
-----------------------------------------------------------------------------

module Data.SBV.Examples.CodeGeneration.GCD where

import Data.SBV

-----------------------------------------------------------------------------
-- * Computing GCD
-----------------------------------------------------------------------------

-- | The symbolic GCD algorithm, over two 8-bit numbers. We define @sgcd a 0@ to
-- be @a@ for all @a@, which implies @sgcd 0 0 = 0@. Note that this is essentially
-- Euclid's algorithm, except with a recursion depth counter. We need the depth
-- counter since the algorithm is not /symbolically terminating/, as we don't have
-- a means of determining that the second argument (@b@) will eventually reach 0 in a symbolic
-- context. Hence we stop after 12 iterations. Why 12? We've empirically determined that this
-- algorithm will recurse at most 12 times for arbitrary 8-bit numbers. Of course, this is
-- a claim that we shall prove below.
sgcd :: SWord8 -> SWord8 -> SWord8
sgcd a b = go a b 12
  where go :: SWord8 -> SWord8 -> SWord8 -> SWord8
        go x y c = ite (c .== 0 ||| y .== 0)   -- stop if y is 0, or if we reach the recursion depth
                       x
                       (go y y' (c-1))
          where (_, y') = x `sQuotRem` y

-----------------------------------------------------------------------------
-- * Verification
-----------------------------------------------------------------------------

{- $VerificationIntro
We prove that 'sgcd' does indeed compute the common divisor of the given numbers.
Our predicate takes @x@, @y@, and @k@. We show that what 'sgcd' returns is indeed a common divisor,
and it is at least as large as any given @k@, provided @k@ is a common divisor as well.
-}

-- | We have:
--
-- >>> prove sgcdIsCorrect
-- Q.E.D.
sgcdIsCorrect :: SWord8 -> SWord8 -> SWord8 -> SBool
sgcdIsCorrect x y k = ite (y  .== 0)                        -- if y is 0
                          (k' .== x)                        -- then k' must be x, nothing else to prove by definition
                          (isCommonDivisor k'  &&&          -- otherwise, k' is a common divisor and
                          (isCommonDivisor k ==> k' .>= k)) -- if k is a common divisor as well, then k' is at least as large as k
  where k' = sgcd x y
        isCommonDivisor a = z1 .== 0 &&& z2 .== 0
           where (_, z1) = x `sQuotRem` a
                 (_, z2) = y `sQuotRem` a

-----------------------------------------------------------------------------
-- * Code generation
-----------------------------------------------------------------------------

{- $VerificationIntro
Now that we have proof our 'sgcd' implementation is correct, we can go ahead
and generate C code for it.
-}

-- | This call will generate the required C files. The following is the function
-- body generated for 'sgcd'. (We are not showing the generated header, @Makefile@,
-- and the driver programs for brevity.) Note that the generated function is
-- a constant time algorithm for GCD. It is not necessarily fastest, but it will take
-- precisely the same amount of time for all values of @x@ and @y@.
--
-- > /* File: "sgcd.c". Automatically generated by SBV. Do not edit! */
-- > 
-- > #include <inttypes.h>
-- > #include <stdint.h>
-- > #include <stdbool.h>
-- > #include "sgcd.h"
-- > 
-- > SWord8 sgcd(const SWord8 x, const SWord8 y)
-- > {
-- >   const SWord8 s0 = x;
-- >   const SWord8 s1 = y;
-- >   const SBool  s3 = s1 == 0;
-- >   const SWord8 s4 = (s1 == 0) ? s0 : (s0 % s1);
-- >   const SWord8 s5 = s3 ? s0 : s4;
-- >   const SBool  s6 = 0 == s5;
-- >   const SWord8 s7 = (s5 == 0) ? s1 : (s1 % s5);
-- >   const SWord8 s8 = s6 ? s1 : s7;
-- >   const SBool  s9 = 0 == s8;
-- >   const SWord8 s10 = (s8 == 0) ? s5 : (s5 % s8);
-- >   const SWord8 s11 = s9 ? s5 : s10;
-- >   const SBool  s12 = 0 == s11;
-- >   const SWord8 s13 = (s11 == 0) ? s8 : (s8 % s11);
-- >   const SWord8 s14 = s12 ? s8 : s13;
-- >   const SBool  s15 = 0 == s14;
-- >   const SWord8 s16 = (s14 == 0) ? s11 : (s11 % s14);
-- >   const SWord8 s17 = s15 ? s11 : s16;
-- >   const SBool  s18 = 0 == s17;
-- >   const SWord8 s19 = (s17 == 0) ? s14 : (s14 % s17);
-- >   const SWord8 s20 = s18 ? s14 : s19;
-- >   const SBool  s21 = 0 == s20;
-- >   const SWord8 s22 = (s20 == 0) ? s17 : (s17 % s20);
-- >   const SWord8 s23 = s21 ? s17 : s22;
-- >   const SBool  s24 = 0 == s23;
-- >   const SWord8 s25 = (s23 == 0) ? s20 : (s20 % s23);
-- >   const SWord8 s26 = s24 ? s20 : s25;
-- >   const SBool  s27 = 0 == s26;
-- >   const SWord8 s28 = (s26 == 0) ? s23 : (s23 % s26);
-- >   const SWord8 s29 = s27 ? s23 : s28;
-- >   const SBool  s30 = 0 == s29;
-- >   const SWord8 s31 = (s29 == 0) ? s26 : (s26 % s29);
-- >   const SWord8 s32 = s30 ? s26 : s31;
-- >   const SBool  s33 = 0 == s32;
-- >   const SWord8 s34 = (s32 == 0) ? s29 : (s29 % s32);
-- >   const SWord8 s35 = s33 ? s29 : s34;
-- >   const SBool  s36 = 0 == s35;
-- >   const SWord8 s37 = s36 ? s32 : s35;
-- >   const SWord8 s38 = s33 ? s29 : s37;
-- >   const SWord8 s39 = s30 ? s26 : s38;
-- >   const SWord8 s40 = s27 ? s23 : s39;
-- >   const SWord8 s41 = s24 ? s20 : s40;
-- >   const SWord8 s42 = s21 ? s17 : s41;
-- >   const SWord8 s43 = s18 ? s14 : s42;
-- >   const SWord8 s44 = s15 ? s11 : s43;
-- >   const SWord8 s45 = s12 ? s8 : s44;
-- >   const SWord8 s46 = s9 ? s5 : s45;
-- >   const SWord8 s47 = s6 ? s1 : s46;
-- >   const SWord8 s48 = s3 ? s0 : s47;
-- >   
-- >   return s48;
-- > }
genGCDInC :: IO ()
genGCDInC = compileToC Nothing "sgcd" $ do
                x <- cgInput "x"
                y <- cgInput "y"
                cgReturn $ sgcd x y
