{-# OPTIONS --guardedness #-}

module Applications.GuardedRecursion.BiSikkel.TypeExtension where

open import Data.List
open import Data.String as Str
open import Relation.Binary.PropositionalEquality

import Applications.GuardedRecursion.Model.Streams.Guarded as M

open import BiSikkel.MSTT.Parameter.ModeTheory
open import BiSikkel.MSTT.Parameter.TypeExtension

open import BiSikkel.LogicalFramework.Proof.CheckingMonad

import Applications.GuardedRecursion.BiSikkel.ModeTheory as GMT
open GMT using (guarded-mt; ω)
open ModeTheory guarded-mt

-- Type extensions for guarded recursion (only guarded streams)
data TyExtCode : List Mode → Mode → Set where
  GStream-code : TyExtCode (★ ∷ []) ω
    -- ^ GStream : Ty ★ → Ty ω

guarded-ty-ext : TyExt guarded-mt
TyExt.TyExtCode guarded-ty-ext = TyExtCode
TyExt._≟ty-code_ guarded-ty-ext GStream-code GStream-code = return refl
TyExt.show-ty-code guarded-ty-ext GStream-code = λ x → "GStream " Str.++ x
TyExt.⟦_⟧ty-code guarded-ty-ext GStream-code = λ A → M.GStream A
TyExt.sem-ty-code-natural guarded-ty-ext GStream-code = M.gstream-closed
