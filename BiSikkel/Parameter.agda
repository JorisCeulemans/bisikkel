--------------------------------------------------
-- Parameter for an entire instance of BiSikkel (MSTT + logical framework)
--------------------------------------------------

module BiSikkel.Parameter where

open import Data.String

open import BiSikkel.MSTT.Parameter
open import BiSikkel.Parameter.bPropExtension
open import BiSikkel.Parameter.bPropExtensionSemantics
open import BiSikkel.Parameter.ProofExtension


record BiSikkelParameter : Set₁ where
  no-eta-equality
  field
    𝒫 : MSTT-Parameter

  open MSTT-Parameter 𝒫 public

  field
    𝒷 : bPropExt ℳ 𝒯 𝓉
    ⟦𝒷⟧ : bPropExtSem ℳ 𝒯 𝓉 𝒷
    𝓅 : ProofExt 𝒫 𝒷 ⟦𝒷⟧
