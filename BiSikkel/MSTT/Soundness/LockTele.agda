--------------------------------------------------
-- Soundness results about lock telescopes, mainly used in the
-- soundness proof for substitution
--------------------------------------------------

open import BiSikkel.MSTT.Parameter.ModeTheory
open import BiSikkel.MSTT.Parameter.TypeExtension
open import BiSikkel.MSTT.Parameter.TermExtension

module BiSikkel.MSTT.Soundness.LockTele
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ) (𝓉 : TmExt ℳ 𝒯)
  where

import Relation.Binary.PropositionalEquality as Ag

open import BiSikkel.Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()
open import BiSikkel.Model.DRA as DRA hiding
  (⟨_∣_⟩; 𝟙; _,lock⟨_⟩; lock-fmap; lock-fmap-cong; lock-fmap-id; lock-fmap-⊚
  ; TwoCell; id-cell; _ⓣ-vert_; _ⓣ-hor_; key-subst; key-subst-natural; key-subst-eq)

open ModeTheory ℳ
open import BiSikkel.MSTT.Syntax ℳ 𝒯 𝓉

private variable
  m n o p : Mode


⟦eq-cell-++ˡᵗ-locks⟧ : (μ : Modality m p) (Λ : LockTele m n) {Θ : LockTele n o} →
                       ⟦ eq-cell (++ˡᵗ-locks (lock⟨ μ ⟩, Λ) {Θ}) ⟧two-cell
                         DRA.≅ᵗᶜ
                       ⟦ id-cell ⓣ-hor eq-cell (++ˡᵗ-locks Λ) ⟧two-cell DRA.ⓣ-vert ⟦ eq-cell (mod-assoc (locksˡᵗ Θ)) ⟧two-cell
⟦eq-cell-++ˡᵗ-locks⟧ μ Λ {Θ} =
  begin
    ⟦ eq-cell (Ag.trans (mod-assoc (locksˡᵗ Θ)) (Ag.cong (μ ⓜ_) (++ˡᵗ-locks Λ))) ⟧two-cell
  ≅⟨ ⟦eq-cell-trans⟧ (mod-assoc (locksˡᵗ Θ)) _ ⟩
    ⟦ eq-cell (Ag.cong (μ ⓜ_) (++ˡᵗ-locks Λ)) ⟧two-cell DRA.ⓣ-vert ⟦ eq-cell (mod-assoc (locksˡᵗ Θ)) ⟧two-cell
  ≅⟨ DRA.ⓣ-vert-congˡ (⟦eq-cell-whisker-left⟧ μ (++ˡᵗ-locks Λ)) ⟩
    ⟦ id-cell ⓣ-hor eq-cell (++ˡᵗ-locks Λ) ⟧two-cell DRA.ⓣ-vert ⟦ eq-cell (mod-assoc (locksˡᵗ Θ)) ⟧two-cell ∎
  where open DRA.≅ᵗᶜ-Reasoning

sym-trans : ∀ {ℓ} {A : Set ℓ} {x y z : A} (e : x Ag.≡ y) {e' : y Ag.≡ z} →
            Ag.sym (Ag.trans e e') Ag.≡ Ag.trans (Ag.sym e') (Ag.sym e)
sym-trans Ag.refl {Ag.refl} = Ag.refl

-- We could prove this from ⟦eq-cell-++ˡᵗ-locks⟧ but proving it directly is easier.
⟦eq-cell-++ˡᵗ-sym-locks⟧ : (μ : Modality m p) (Λ : LockTele m n) {Θ : LockTele n o} →
                           ⟦ eq-cell (Ag.sym (++ˡᵗ-locks (lock⟨ μ ⟩, Λ) {Θ})) ⟧two-cell
                             DRA.≅ᵗᶜ
                           ⟦ eq-cell (Ag.sym (mod-assoc (locksˡᵗ Θ))) ⟧two-cell DRA.ⓣ-vert ⟦ id-cell ⓣ-hor eq-cell (Ag.sym (++ˡᵗ-locks Λ)) ⟧two-cell
⟦eq-cell-++ˡᵗ-sym-locks⟧ μ Λ {Θ} =
  begin
    ⟦ eq-cell (Ag.sym (Ag.trans (mod-assoc (locksˡᵗ Θ)) (Ag.cong (μ ⓜ_) (++ˡᵗ-locks Λ)))) ⟧two-cell
  ≅⟨ Ag.subst (λ e → ⟦ eq-cell (Ag.sym (Ag.trans (mod-assoc (locksˡᵗ Θ)) (Ag.cong (μ ⓜ_) (++ˡᵗ-locks Λ)))) ⟧two-cell DRA.≅ᵗᶜ ⟦ eq-cell e ⟧two-cell)
              {Ag.sym (Ag.trans (mod-assoc (locksˡᵗ Θ)) (Ag.cong (μ ⓜ_) (++ˡᵗ-locks Λ)))}
              (Ag.trans (sym-trans (mod-assoc (locksˡᵗ Θ))) (Ag.cong (λ x → Ag.trans x (Ag.sym (mod-assoc (locksˡᵗ Θ)))) (Ag.sym-cong (++ˡᵗ-locks Λ))))
              DRA.reflᵗᶜ ⟩
    ⟦ eq-cell (Ag.trans (Ag.cong (μ ⓜ_) (Ag.sym (++ˡᵗ-locks Λ))) (Ag.sym (mod-assoc (locksˡᵗ Θ)))) ⟧two-cell
  ≅⟨ ⟦eq-cell-trans⟧ (Ag.cong (μ ⓜ_) (Ag.sym (++ˡᵗ-locks Λ))) _ ⟩
    ⟦ eq-cell (Ag.sym (mod-assoc (locksˡᵗ Θ))) ⟧two-cell DRA.ⓣ-vert ⟦ eq-cell (Ag.cong (μ ⓜ_) (Ag.sym (++ˡᵗ-locks Λ))) ⟧two-cell
  ≅⟨ DRA.ⓣ-vert-congʳ (⟦eq-cell-whisker-left⟧ μ (Ag.sym (++ˡᵗ-locks Λ))) ⟩
    ⟦ eq-cell (Ag.sym (mod-assoc (locksˡᵗ Θ))) ⟧two-cell DRA.ⓣ-vert ⟦ id-cell ⓣ-hor eq-cell (Ag.sym (++ˡᵗ-locks Λ)) ⟧two-cell ∎
  where open DRA.≅ᵗᶜ-Reasoning


whiskerˡᵗ-right-sound : (Θ Ψ : LockTele m n) {Λ : LockTele n o} (α : TwoCell (locksˡᵗ Θ) (locksˡᵗ Ψ)) →
                        ⟦ eq-cell (++ˡᵗ-locks Ψ {Λ}) ⟧two-cell
                        DRA.ⓣ-vert (to (⟦ⓜ⟧-sound (locksˡᵗ Ψ) (locksˡᵗ Λ))
                        DRA.ⓣ-vert ((⟦ α ⟧two-cell DRA.ⓣ-hor DRA.id-cell)
                        DRA.ⓣ-vert (from (⟦ⓜ⟧-sound (locksˡᵗ Θ) (locksˡᵗ Λ))
                        DRA.ⓣ-vert ⟦ eq-cell (Ag.sym (++ˡᵗ-locks Θ)) ⟧two-cell)))
                          DRA.≅ᵗᶜ
                        ⟦ whiskerˡᵗ-right Θ Ψ α ⟧two-cell
whiskerˡᵗ-right-sound Θ Ψ {Λ} α =
  begin
    ⟦ eq-cell (++ˡᵗ-locks Ψ) ⟧two-cell
    DRA.ⓣ-vert (to (⟦ⓜ⟧-sound (locksˡᵗ Ψ) (locksˡᵗ Λ))
    DRA.ⓣ-vert ((⟦ α ⟧two-cell DRA.ⓣ-hor DRA.id-cell)
    DRA.ⓣ-vert (from (⟦ⓜ⟧-sound (locksˡᵗ Θ) (locksˡᵗ Λ))
    DRA.ⓣ-vert ⟦ eq-cell (Ag.sym (++ˡᵗ-locks Θ)) ⟧two-cell)))
  ≅⟨ DRA.ⓣ-vert-congʳ (DRA.ⓣ-vert-congʳ (transᵗᶜ DRA.ⓣ-vert-assoc (DRA.ⓣ-vert-congˡ (DRA.ⓣ-hor-congʳ ⟦id-cell⟧-sound)))) ⟨
    ⟦ eq-cell (++ˡᵗ-locks Ψ) ⟧two-cell
    DRA.ⓣ-vert (to (⟦ⓜ⟧-sound (locksˡᵗ Ψ) (locksˡᵗ Λ))
    DRA.ⓣ-vert (((⟦ α ⟧two-cell DRA.ⓣ-hor ⟦ id-cell {μ = locksˡᵗ Λ} ⟧two-cell) DRA.ⓣ-vert from (⟦ⓜ⟧-sound (locksˡᵗ Θ) (locksˡᵗ Λ)))
    DRA.ⓣ-vert ⟦ eq-cell (Ag.sym (++ˡᵗ-locks Θ)) ⟧two-cell))
  ≅⟨ DRA.ⓣ-vert-congʳ (DRA.ⓣ-vert-congʳ (DRA.ⓣ-vert-congˡ (⟦ⓜ⟧-sound-natural α id-cell))) ⟨
    ⟦ eq-cell (++ˡᵗ-locks Ψ) ⟧two-cell
    DRA.ⓣ-vert (to (⟦ⓜ⟧-sound (locksˡᵗ Ψ) (locksˡᵗ Λ))
    DRA.ⓣ-vert ((from (⟦ⓜ⟧-sound (locksˡᵗ Ψ) (locksˡᵗ Λ)) DRA.ⓣ-vert ⟦ α ⓣ-hor id-cell {μ = locksˡᵗ Λ} ⟧two-cell)
    DRA.ⓣ-vert ⟦ eq-cell (Ag.sym (++ˡᵗ-locks Θ)) ⟧two-cell))
  ≅⟨ DRA.ⓣ-vert-congʳ (transᵗᶜ (symᵗᶜ DRA.ⓣ-vert-assoc) (DRA.ⓣ-vert-congˡ (
       transᵗᶜ (transᵗᶜ (symᵗᶜ DRA.ⓣ-vert-assoc) (DRA.ⓣ-vert-congˡ (isoˡ (⟦ⓜ⟧-sound (locksˡᵗ Ψ) (locksˡᵗ Λ))))) DRA.ⓣ-vert-unitˡ))) ⟩
    ⟦ eq-cell (++ˡᵗ-locks Ψ) ⟧two-cell
    DRA.ⓣ-vert (⟦ α ⓣ-hor id-cell {μ = locksˡᵗ Λ} ⟧two-cell
    DRA.ⓣ-vert ⟦ eq-cell (Ag.sym (++ˡᵗ-locks Θ)) ⟧two-cell)
  ≅⟨ DRA.ⓣ-vert-congʳ (⟦ⓣ-vert⟧-sound _ _) ⟨
    ⟦ eq-cell (++ˡᵗ-locks Ψ) ⟧two-cell
    DRA.ⓣ-vert ⟦ (α ⓣ-hor id-cell {μ = locksˡᵗ Λ}) ⓣ-vert eq-cell (Ag.sym (++ˡᵗ-locks Θ))⟧two-cell
  ≅⟨ ⟦ⓣ-vert⟧-sound _ _ ⟨
    ⟦ eq-cell (++ˡᵗ-locks Ψ) ⓣ-vert ((α ⓣ-hor id-cell {μ = locksˡᵗ Λ}) ⓣ-vert eq-cell (Ag.sym (++ˡᵗ-locks Θ))) ⟧two-cell ∎
  where open DRA.≅ᵗᶜ-Reasoning

whiskerˡᵗ-right-sound-key : (Θ Ψ : LockTele m n) {Λ : LockTele n o} (α : TwoCell (locksˡᵗ Θ) (locksˡᵗ Ψ)) {Γ : SemCtx ⟦ m ⟧mode} →
                            DRA.key-subst ⟦ eq-cell (Ag.sym (++ˡᵗ-locks Θ)) ⟧two-cell {Γ}
                            M.⊚ DRA.key-subst (from (⟦ⓜ⟧-sound (locksˡᵗ Θ) (locksˡᵗ Λ)))
                            M.⊚ DRA.lock-fmap ⟦ locksˡᵗ Λ ⟧mod (DRA.key-subst ⟦ α ⟧two-cell)
                            M.⊚ DRA.key-subst (to (⟦ⓜ⟧-sound (locksˡᵗ Ψ) (locksˡᵗ Λ)))
                            M.⊚ DRA.key-subst ⟦ eq-cell (++ˡᵗ-locks Ψ {Λ}) ⟧two-cell
                              M.≅ˢ
                            DRA.key-subst ⟦ whiskerˡᵗ-right Θ Ψ α ⟧two-cell
whiskerˡᵗ-right-sound-key Θ Ψ α =
  M.transˢ (M.⊚-congˡ (M.⊚-congˡ (M.⊚-congʳ (M.symˢ (M.id-subst-unitˡ _))))) (DRA.key-subst-eq (whiskerˡᵗ-right-sound Θ Ψ α))
