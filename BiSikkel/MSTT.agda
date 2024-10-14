--------------------------------------------------
-- Module that re-exports all definitions needed for working with the
--   type theory MSTT
--------------------------------------------------

open import BiSikkel.MSTT.Parameter

module BiSikkel.MSTT (𝒫 : MSTT-Parameter) where

open MSTT-Parameter

open import BiSikkel.MSTT.Syntax (𝒫 .ℳ) (𝒫 .𝒯) (𝒫 .𝓉) public hiding (_,,_∣_)
  -- ^ hiding _,,_∣_ (constructor for nameless telescopes) to avoid
  --   parsing issues
open import BiSikkel.MSTT.Interpretation (𝒫 .ℳ) (𝒫 .𝒯) (𝒫 .𝓉) (𝒫 .⟦𝓉⟧) public
open import BiSikkel.MSTT.BasicPrograms (𝒫 .ℳ) (𝒫 .𝒯) (𝒫 .𝓉) public
open import BiSikkel.MSTT.Normalization 𝒫 public
open import BiSikkel.MSTT.Extraction 𝒫 public
