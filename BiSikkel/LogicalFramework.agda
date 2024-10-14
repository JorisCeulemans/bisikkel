open import BiSikkel.Parameter

module BiSikkel.LogicalFramework
  (ℬ : BiSikkelParameter)
  where


open BiSikkelParameter ℬ


open import BiSikkel.LogicalFramework.bProp 𝒫 𝒷 ⟦𝒷⟧ public
open import BiSikkel.LogicalFramework.Proof ℬ public
open import BiSikkel.LogicalFramework.Proof.Checker.ResultType 𝒫 𝒷 ⟦𝒷⟧ public
