--------------------------------------------------
-- Specification of new inference rules to construct proofs
--------------------------------------------------

open import Data.String
open import BiSikkel.MSTT.Parameter
open import BiSikkel.Parameter.bPropExtension
open import BiSikkel.Parameter.bPropExtensionSemantics

module BiSikkel.Parameter.ProofExtension
  (𝒫 : MSTT-Parameter) (let open MSTT-Parameter 𝒫)
  (𝒷 : bPropExt ℳ 𝒯 𝓉)
  (⟦𝒷⟧ : bPropExtSem ℳ 𝒯 𝓉 𝒷)
  where

open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import BiSikkel.MSTT.Parameter.TermExtension ℳ 𝒯
open import BiSikkel.Parameter.ArgInfo ℳ 𝒯
open import BiSikkel.MSTT 𝒫
open import BiSikkel.LogicalFramework.Proof.CheckingMonad
open import BiSikkel.LogicalFramework.Proof.Context 𝒫 𝒷 ⟦𝒷⟧
open import BiSikkel.LogicalFramework.bProp 𝒫 𝒷 ⟦𝒷⟧
open import BiSikkel.LogicalFramework.Proof.Checker.ResultType 𝒫 𝒷 ⟦𝒷⟧

private variable
  m : Mode


-- When adding new proof constructors, we should specify how such
-- proofs will be checked. In the process of checking a new proof, we
-- can check all subproofs in any proof context that has the correct
-- shape and against any bProp. This is encoded in the type below.
ProofCheckExt : (infos : List (ArgInfo m)) (pfarg-names : ArgBoundNames infos)
                (Ξ : ProofCtx m) (φ : bProp (to-ctx Ξ)) →
                Set
ProofCheckExt []             pfarg-names                  Ξ φ = PCM (PCResult Ξ φ)
ProofCheckExt (info ∷ infos) (pfarg-names , pfargs-names) Ξ φ =
  ((Ξ' : ProofCtx (ArgInfo.mode info)) (ψ : bProp (to-ctx Ξ'))
    → (to-ctx Ξ' ≡ ((to-ctx Ξ) ++tel (add-names (arg-tel info)) pfarg-names))
    → PCM (PCResult Ξ' ψ))
  → ProofCheckExt infos pfargs-names Ξ φ

record ProofExt : Set₁ where
  no-eta-equality
  field
    ProofExtCode : Mode → Set
      -- ^ Universe of codes for new inference rules, indexed by the mode the proof will live at
    pf-code-tmarg-infos : (c : ProofExtCode m) → List (TmArgInfo m)
      -- ^ Every proof can have a number of term arguments
    pf-code-bparg-infos : (c : ProofExtCode m) → List (ArgInfo m)
      -- ^ Every proof can have a number of bProp arguments
    pf-code-pfarg-infos : (c : ProofExtCode m) → List (ArgInfo m)
      -- ^ Every proof can have a number of proof arguments, i.e. premises in the inference rule

    pf-code-check : (c : ProofExtCode m) (Ξ : ProofCtx m) (φ : bProp (to-ctx Ξ))
                    {tmarg-names : TmArgBoundNames (pf-code-tmarg-infos c)} (tmargs : ExtTmArgs (pf-code-tmarg-infos c) tmarg-names (to-ctx Ξ))
                    {bparg-names : ArgBoundNames (pf-code-bparg-infos c)} (bpargs : ExtBPArgs (pf-code-bparg-infos c) bparg-names (to-ctx Ξ))
                    (pfarg-names : ArgBoundNames (pf-code-pfarg-infos c)) →
                    ProofCheckExt (pf-code-pfarg-infos c) pfarg-names Ξ φ
      -- ^ Given a proof, we need to specify how it should be checked.
