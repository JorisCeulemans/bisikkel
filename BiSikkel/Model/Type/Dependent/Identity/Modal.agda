--------------------------------------------------
-- Congruence for the DRA introduction rule, expressed using the
-- identity type
--------------------------------------------------

module BiSikkel.Model.Type.Dependent.Identity.Modal where

open import BiSikkel.Model.BaseCategory
open import BiSikkel.Model.CwF-Structure
open import BiSikkel.Model.DRA
open import BiSikkel.Model.Type.Dependent.Identity


id-dra-intro-cong : {C D : BaseCategory} (μ : DRA C D) {Γ : Ctx D} {T : Ty (Γ ,lock⟨ μ ⟩)}
                    {t t' : Tm (Γ ,lock⟨ μ ⟩) T} →
                    Tm (Γ ,lock⟨ μ ⟩) (Id t t') → Tm Γ (Id (dra-intro μ t) (dra-intro μ t'))
id-dra-intro-cong μ e = ≅ᵗᵐ-to-Id (dra-intro-cong μ (eq-reflect e))
