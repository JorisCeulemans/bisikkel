{-# OPTIONS --guardedness #-}

module Applications.GuardedRecursion.BiSikkel where

open import Data.Unit
open import Data.Product

open import Applications.GuardedRecursion.BiSikkel.TypeExtension
open import Applications.GuardedRecursion.BiSikkel.TermExtension
open import Applications.GuardedRecursion.BiSikkel.bPropExtension
open import Applications.GuardedRecursion.BiSikkel.ProofExtension

open import BiSikkel.Parameter



open import Applications.GuardedRecursion.BiSikkel.MSTT public

guarded-param : BiSikkelParameter
BiSikkelParameter.𝒫 guarded-param = guarded-mstt
BiSikkelParameter.𝒷 guarded-param = guarded-bp-ext
BiSikkelParameter.⟦𝒷⟧ guarded-param = guarded-bp-ext-sem
BiSikkelParameter.𝓅 guarded-param = guarded-pf-ext

open import BiSikkel.LogicalFramework guarded-param public


pattern tmlöb-β = ext tmlöb-β-code tt tt tt tt tt tt
pattern pflöb x p = ext (pflöb-code x) tt tt tt tt (tt , tt) (p , tt)
