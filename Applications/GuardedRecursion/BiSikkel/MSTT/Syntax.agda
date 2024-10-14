--------------------------------------------------
-- Definition of the syntax for new MSTT type and term constructors
-- for guarded type theory
--------------------------------------------------

{-# OPTIONS --guardedness #-}

module Applications.GuardedRecursion.BiSikkel.MSTT.Syntax where

open import Data.Product using (_,_)
open import Data.Unit

open import BiSikkel.MSTT.Parameter.ModeTheory
open import BiSikkel.MSTT.Parameter

open import Applications.GuardedRecursion.BiSikkel.ModeTheory
open import Applications.GuardedRecursion.BiSikkel.TypeExtension
open import Applications.GuardedRecursion.BiSikkel.TermExtension

open import BiSikkel.MSTT.Syntax guarded-mt guarded-ty-ext guarded-tm-ext

pattern GStream A = Ext GStream-code (A , tt)
pattern löb[later∣_∈_]_ x A t = ext (löb-code A) ((tt , x) , tt) (t , tt) refl
pattern g-cons {A} h t = ext (g-cons-code A) (tt , tt , tt) (h , t , tt) refl
pattern g-head {A} s = ext (g-head-code A) (tt , tt) (s , tt) refl
pattern g-tail {A} s = ext (g-tail-code A) (tt , tt) (s , tt) refl
