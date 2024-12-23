--------------------------------------------------
-- Interpretation of MSTT terms and substitutions in a presheaf model
--------------------------------------------------

open import BiSikkel.MSTT.Parameter.ModeTheory
open import BiSikkel.MSTT.Parameter.TypeExtension
open import BiSikkel.MSTT.Parameter.TermExtension
open import BiSikkel.MSTT.Parameter.TermExtensionSemantics using (TmExtSem)

module BiSikkel.MSTT.Interpretation
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ) (𝓉 : TmExt ℳ 𝒯) (⟦𝓉⟧ : TmExtSem ℳ 𝒯 𝓉)
  where

open import Data.List
open import Data.Product
open import Data.Unit

open ModeTheory ℳ
open TmExtSem ⟦𝓉⟧

open import BiSikkel.Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()
open import BiSikkel.Model.DRA as DRA hiding (⟨_∣_⟩; 𝟙; _,lock⟨_⟩)
import BiSikkel.Model.Type.Function as M
import BiSikkel.Model.Type.Product as M
import BiSikkel.Model.Type.Constant as M

open import BiSikkel.MSTT.Parameter.TermExtensionSemantics ℳ 𝒯 hiding (TmExtSem)
open import BiSikkel.MSTT.Syntax ℳ 𝒯 𝓉
open SomeVar using (get-var)

private variable
  m n : Mode
  Γ Δ : Ctx m
  T S : Ty m
  x : Name


--------------------------------------------------
-- Reexporting interpretation of types and contexts

open import BiSikkel.MSTT.Interpretation.TypeContext ℳ 𝒯 public


--------------------------------------------------
-- Interpretation of terms

⟦_⟧var : {x : Name} {T : Ty n} {Γ : Ctx m} {Λ : LockTele m n} →
         Var x T Γ Λ →
         SemTm (⟦ Γ ⟧ctx DRA.,lock⟨ ⟦ locksˡᵗ Λ ⟧mod ⟩) ⟦ T ⟧ty
⟦_⟧var {T = T} (vzero {μ = μ} α) =
  (dra-elim ⟦ μ ⟧mod (M.ξcl (ty-closed-natural ⟨ μ ∣ T ⟩)))
    M.[ ty-closed-natural T ∣ DRA.key-subst ⟦ α ⟧two-cell ]cl
⟦_⟧var {T = T} {Λ = Λ} (vsuc v) =
  ⟦ v ⟧var M.[ ty-closed-natural T ∣ lock-fmap ⟦ locksˡᵗ Λ ⟧mod M.π ]cl
⟦_⟧var {T = T} (vlock {ρ = ρ} {Λ = Λ} v) =
  ⟦ v ⟧var M.[ ty-closed-natural T ∣ M.to (DRA.lock-iso (⟦ⓜ⟧-sound ρ (locksˡᵗ Λ))) ]cl

⟦_⟧tm : Tm Γ T → SemTm ⟦ Γ ⟧ctx ⟦ T ⟧ty
⟦_⟧tmextargs : ∀ {arginfos} {bound-names : TmArgBoundNames arginfos} → ExtTmArgs arginfos bound-names Γ → SemTms arginfos Γ

⟦ var' _ {v} ⟧tm = ⟦ v ⟧var
⟦ mod⟨ μ ⟩ t ⟧tm = dra-intro ⟦ μ ⟧mod ⟦ t ⟧tm
⟦ mod-elim {T = T} {S = S} ρ μ _ t s ⟧tm =
  dra-let ⟦ ρ ⟧mod ⟦ μ ⟧mod (ty-closed-natural T) (ty-closed-natural S)
          ⟦ t ⟧tm
          (⟦ s ⟧tm M.[ ty-closed-natural S ∣ M.to (M.,,-cong (eq-dra-ty-closed (⟦ⓜ⟧-sound ρ μ) (ty-closed-natural T))) ]cl)
⟦ lam[_∣_∈_]_ {S = S} _ _ _ t ⟧tm = M.lamcl (ty-closed-natural S) ⟦ t ⟧tm
⟦ _∙_ {μ = μ} f t ⟧tm = M.app ⟦ f ⟧tm (dra-intro ⟦ μ ⟧mod ⟦ t ⟧tm)
⟦ zero ⟧tm = M.zero'
⟦ suc n ⟧tm = M.suc' ⟦ n ⟧tm
⟦ nat-rec a f n ⟧tm = M.nat-rec _ ⟦ a ⟧tm ⟦ f ⟧tm ⟦ n ⟧tm
⟦ true ⟧tm = M.true'
⟦ false ⟧tm = M.false'
⟦ if b t f ⟧tm = M.if' ⟦ b ⟧tm then' ⟦ t ⟧tm else' ⟦ f ⟧tm
⟦ pair t s ⟧tm = M.pair ⟦ t ⟧tm ⟦ s ⟧tm
⟦ fst p ⟧tm = M.fst ⟦ p ⟧tm
⟦ snd p ⟧tm = M.snd ⟦ p ⟧tm
⟦ ext c bound-names args refl ⟧tm = apply-sem-tm-constructor ⟦ c ⟧tm-code ⟦ args ⟧tmextargs
⟦ global-def {T = T} _ {t} ⟧tm = ⟦ t ⟧tm M.[ ty-closed-natural T ∣ M.!◇ _ ]cl

⟦_⟧tmextargs {arginfos = []}                 _            = tt
⟦_⟧tmextargs {arginfos = arginfo ∷ arginfos} (arg , args) =
  (⟦ arg ⟧tm M.[ ty-closed-natural (tmarg-ty arginfo) ∣ M._≅ᶜ_.to (++tel-++⟦⟧nltel _ (tmarg-tel arginfo) _) ]cl) , ⟦ args ⟧tmextargs


--------------------------------------------------
-- Interpretation of renamings and substitutions as presheaf morphisms

,ˡᵗ-sound : {Γ : Ctx m} (Λ : LockTele m n) → ⟦ Γ ,ˡᵗ Λ ⟧ctx M.≅ᶜ DRA.lock ⟦ locksˡᵗ Λ ⟧mod ⟦ Γ ⟧ctx
,ˡᵗ-sound {m} ◇ = M.reflᶜ
,ˡᵗ-sound (lock⟨ μ ⟩, Λ) =
  M.transᶜ (,ˡᵗ-sound Λ) (M.symᶜ (lock-iso (⟦ⓜ⟧-sound μ (locksˡᵗ Λ))))

RenSubDataSemantics : RenSubData → Set
RenSubDataSemantics V =
  {m n : Mode} {μ : Modality n m} {T : Ty n} {Γ : Ctx m} → V μ T Γ → SemTm ⟦ Γ ,lock⟨ μ ⟩ ⟧ctx ⟦ T ⟧ty

module RenSubSemantics
  (V : RenSubData) (⟦_⟧rensubdata : RenSubDataSemantics V)
  where

  open AtomicRenSubDef V
  open RenSubDef V

  ⟦_⟧arensub : AtomicRenSub Γ Δ → (⟦ Γ ⟧ctx M.⇒ ⟦ Δ ⟧ctx)
  ⟦ []ᵃ ⟧arensub = M.!◇ _
  ⟦ idᵃ ⟧arensub = M.id-subst _
  ⟦ σ ⊚πᵃ ⟧arensub = ⟦ σ ⟧arensub M.⊚ M.π
  ⟦ σ ,lockᵃ⟨ μ ⟩ ⟧arensub = lock-fmap ⟦ μ ⟧mod ⟦ σ ⟧arensub
  ⟦ keyᵃ Λ₁ Λ₂ α ⟧arensub =
    M.to (,ˡᵗ-sound Λ₂)
    M.⊚ DRA.key-subst ⟦ α ⟧two-cell
    M.⊚ M.from (,ˡᵗ-sound Λ₁)
  ⟦ _∷ᵃ_/_ {μ = μ} {T = T} σ v x ⟧arensub =
    ⟦ σ ⟧arensub M.,cl⟨ ty-closed-natural ⟨ μ ∣ T ⟩ ⟩ (dra-intro ⟦ μ ⟧mod ⟦ v ⟧rensubdata)

  -- Note that there is an extra case for `id ⊚a τᵃ ` so that the
  -- interpretation of a rensub consisting of at least one atomic
  -- rensub does not have the semantic identity substitution
  -- post-composed (which is a left unit according to _≅ˢ_ but not to
  -- Agda's definitional equality).
  ⟦_⟧rensub : RenSub Γ Δ → (⟦ Γ ⟧ctx M.⇒ ⟦ Δ ⟧ctx)
  ⟦ id ⟧rensub = M.id-subst _
  ⟦ id ⊚a τᵃ ⟧rensub = ⟦ τᵃ ⟧arensub
  ⟦ σ  ⊚a τᵃ ⟧rensub = ⟦ σ ⟧rensub M.⊚ ⟦ τᵃ ⟧arensub


ren-data-semantics : RenSubDataSemantics RenData
ren-data-semantics v = ⟦ get-var v ⟧var

module RenSemantics = RenSubSemantics RenData ren-data-semantics
open RenSemantics renaming
  ( ⟦_⟧arensub to ⟦_⟧aren
  ; ⟦_⟧rensub to ⟦_⟧ren
  ) public


sub-data-semantics : RenSubDataSemantics SubData
sub-data-semantics t = ⟦ t ⟧tm

module SubSemantics = RenSubSemantics SubData sub-data-semantics
open SubSemantics renaming
  ( ⟦_⟧arensub to ⟦_⟧asub
  ; ⟦_⟧rensub to ⟦_⟧sub
  ) public
