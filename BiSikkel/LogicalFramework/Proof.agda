open import BiSikkel.Parameter

module BiSikkel.LogicalFramework.Proof
  (ℬ : BiSikkelParameter)
  where

open BiSikkelParameter ℬ

open import BiSikkel.LogicalFramework.Proof.CheckingMonad public
open import BiSikkel.LogicalFramework.Proof.Definition ℬ public
open import BiSikkel.LogicalFramework.Proof.Context 𝒫 𝒷 ⟦𝒷⟧ public
open import BiSikkel.LogicalFramework.Proof.Checker ℬ public
open import BiSikkel.LogicalFramework.Proof.Extraction ℬ public
