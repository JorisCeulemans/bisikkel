--------------------------------------------------
-- Module that re-exports all definitions involving bProps
--------------------------------------------------

open import BiSikkel.MSTT.Parameter
open import BiSikkel.Parameter.bPropExtension
open import BiSikkel.Parameter.bPropExtensionSemantics

module BiSikkel.LogicalFramework.bProp
  (𝒫 : MSTT-Parameter) (let open MSTT-Parameter 𝒫)
  (𝒷 : bPropExt ℳ 𝒯 𝓉)
  (⟦𝒷⟧ : bPropExtSem ℳ 𝒯 𝓉 𝒷)
  where

open import BiSikkel.LogicalFramework.bProp.Syntax 𝒫 𝒷 public
open import BiSikkel.LogicalFramework.bProp.Interpretation 𝒫 𝒷 ⟦𝒷⟧ public
open import BiSikkel.LogicalFramework.bProp.Extraction 𝒫 𝒷 ⟦𝒷⟧ public
