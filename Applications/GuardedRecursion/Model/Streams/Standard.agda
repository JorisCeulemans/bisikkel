--------------------------------------------------
-- Definition of semantic standard streams in base category ★
--------------------------------------------------

{-# OPTIONS --guardedness #-}

module Applications.GuardedRecursion.Model.Streams.Standard where

open import Data.Nat
open import Data.Unit
open import Data.Vec as Vec using (Vec; _∷_; [])
open import Data.Vec.Properties
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import BiSikkel.Model.BaseCategory
open import BiSikkel.Model.CwF-Structure
open import BiSikkel.Model.DRA
open import BiSikkel.Model.Type.Function
open import Applications.GuardedRecursion.Model.Streams.Guarded
open import Applications.GuardedRecursion.Model.Modalities

private
  variable
    Γ : Ctx ★


--------------------------------------------------
-- Definition of Stream'

Stream' : ClosedTy ★ → ClosedTy ★
Stream' A = forever-ty (GStream A)

stream-closed : {A : ClosedTy ★} → IsClosedNatural A → IsClosedNatural (Stream' A)
stream-closed clA = dra-closed forever (gstream-closed clA)
