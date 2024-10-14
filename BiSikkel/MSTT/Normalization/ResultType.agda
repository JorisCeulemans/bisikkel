--------------------------------------------------
-- The result of normalization will be an MSTT term, together with
-- semantic evidence that the interpretation of the original and the
-- normalized terms are equivalent.
--------------------------------------------------

open import BiSikkel.MSTT.Parameter.ModeTheory
open import BiSikkel.MSTT.Parameter.TypeExtension
open import BiSikkel.MSTT.Parameter.TermExtension
open import BiSikkel.MSTT.Parameter.TermExtensionSemantics

module BiSikkel.MSTT.Normalization.ResultType
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ) (𝓉 : TmExt ℳ 𝒯) (⟦𝓉⟧ : TmExtSem ℳ 𝒯 𝓉)
  where

open import Data.Nat

open ModeTheory ℳ
import BiSikkel.Model.CwF-Structure as M
open import BiSikkel.MSTT.Syntax ℳ 𝒯 𝓉
open import BiSikkel.MSTT.Interpretation ℳ 𝒯 𝓉 ⟦𝓉⟧

private variable
  m : Mode
  T : Ty m
  Γ : Ctx m


Fuel : Set
Fuel = ℕ

record NormalizeResult (t : Tm Γ T) : Set where
  constructor normres
  field
    nt : Tm Γ T
    sound : ⟦ t ⟧tm M.≅ᵗᵐ ⟦ nt ⟧tm
