--------------------------------------------------
-- Module that re-exports all definitions needed for working with the
--   type theory MSTT (but not interpreting it in a model)
--------------------------------------------------

open import BiSikkel.MSTT.Parameter.ModeTheory
open import BiSikkel.MSTT.Parameter.TypeExtension
open import BiSikkel.MSTT.Parameter.TermExtension

module BiSikkel.MSTT.Syntax
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ) (𝓉 : TmExt ℳ 𝒯)
  where

open import BiSikkel.MSTT.Syntax.Types ℳ 𝒯 public
open import BiSikkel.MSTT.Syntax.Contexts ℳ 𝒯 public
open import BiSikkel.MSTT.Syntax.Terms ℳ 𝒯 𝓉 public
open import BiSikkel.MSTT.Syntax.Substitution ℳ 𝒯 𝓉 public
