--------------------------------------------------
-- Interpretation of propositions in a presheaf model
--------------------------------------------------

open import BiSikkel.MSTT.Parameter
open import BiSikkel.Parameter.bPropExtension
open import BiSikkel.Parameter.bPropExtensionSemantics using (bPropExtSem)

module BiSikkel.LogicalFramework.bProp.Interpretation
  (𝒫 : MSTT-Parameter) (let open MSTT-Parameter 𝒫)
  (𝒷 : bPropExt ℳ 𝒯 𝓉) (⟦𝒷⟧ : bPropExtSem ℳ 𝒯 𝓉 𝒷)
  where

open import Data.List
open import Data.Product
open import Data.Unit.Polymorphic

open import BiSikkel.Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy) using (_≅ᵗʸ_)
import BiSikkel.Model.DRA as DRA
import BiSikkel.Model.Type.Function as M
import BiSikkel.Model.Type.Product as M
import BiSikkel.Model.Type.Constant as M
import BiSikkel.Model.Type.Dependent.Identity as M
import BiSikkel.Model.Type.Dependent.Function as M

open import BiSikkel.MSTT 𝒫
open import BiSikkel.LogicalFramework.bProp.Syntax 𝒫 𝒷
open import BiSikkel.Parameter.ArgInfo ℳ 𝒯
open BiSikkel.Parameter.bPropExtensionSemantics ℳ 𝒯 𝓉 hiding (bPropExtSem)

open bPropExtSem ⟦𝒷⟧

private variable
  m : Mode
  Γ Δ : Ctx m


⟦_⟧bprop : bProp Γ → SemTy ⟦ Γ ⟧ctx
⟦_⟧bpextargs : ∀ {arginfos} {names : ArgBoundNames arginfos}→ ExtBPArgs arginfos names Γ → SemProps arginfos Γ

⟦ ⊤ᵇ ⟧bprop = M.Unit'
⟦ ⊥ᵇ ⟧bprop = M.Empty'
⟦ t1 ≡ᵇ t2 ⟧bprop = M.Id ⟦ t1 ⟧tm ⟦ t2 ⟧tm
⟦ ⟨ μ ∣ φ ⟩⊃ ψ ⟧bprop = DRA.⟨ ⟦ μ ⟧mod ∣ ⟦ φ ⟧bprop ⟩ M.⇛ ⟦ ψ ⟧bprop
⟦ φ ∧ ψ ⟧bprop = ⟦ φ ⟧bprop M.⊠ ⟦ ψ ⟧bprop
⟦ ∀[ μ ∣ _ ∈ T ] φ ⟧bprop = M.Pi ⟦ ⟨ μ ∣ T ⟩ ⟧ty ⟦ φ ⟧bprop
⟦ ⟨ μ ∣ φ ⟩ ⟧bprop = DRA.⟨ ⟦ μ ⟧mod ∣ ⟦ φ ⟧bprop ⟩
⟦ ext c _ tmargs _ bpargs ⟧bprop = apply-sem-prop-constructor ⟦ c ⟧bp-code ⟦ tmargs ⟧tmextargs ⟦ bpargs ⟧bpextargs

⟦_⟧bpextargs         {arginfos = []}          args         = tt
⟦_⟧bpextargs {Γ = Γ} {arginfos = arginfo ∷ _} (arg , args) =
  (⟦ arg ⟧bprop M.[ M.to (++tel-++⟦⟧nltel Γ (arg-tel arginfo) _) ]) , ⟦ args ⟧bpextargs
