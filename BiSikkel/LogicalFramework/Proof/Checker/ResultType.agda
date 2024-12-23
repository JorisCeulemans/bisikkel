--------------------------------------------------
-- Upon success the proof checker outputs a list of goals and
-- conditional semantic evidence of the proof (given semantic values
-- for all goals)
--------------------------------------------------

open import BiSikkel.MSTT.Parameter
open import BiSikkel.Parameter.bPropExtension
open import BiSikkel.Parameter.bPropExtensionSemantics

module BiSikkel.LogicalFramework.Proof.Checker.ResultType
  (𝒫 : MSTT-Parameter) (let open MSTT-Parameter 𝒫)
  (𝒷 : bPropExt ℳ 𝒯 𝓉)
  (⟦𝒷⟧ : bPropExtSem ℳ 𝒯 𝓉 𝒷)
  where

open import Data.Empty
open import Data.List
open import Data.Product
open import Data.String hiding (_++_)
open import Data.Unit

open import BiSikkel.Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()

open import BiSikkel.MSTT 𝒫
open import BiSikkel.LogicalFramework.bProp 𝒫 𝒷 ⟦𝒷⟧
open import BiSikkel.LogicalFramework.Proof.Context 𝒫 𝒷 ⟦𝒷⟧

private variable
  m : Mode
  Ξ : ProofCtx m
  Γ : Ctx m
  φ : bProp Γ


-- If a proof is incomplete (i.e. it contains one or more holes), the
-- proof checker should output the remaining goals to solve (i.e. the
-- goal proposition to prove and the proof context at that point).
record Goal : Set where
  constructor goal
  field
    gl-identifier : String
    {gl-mode} : Mode
    gl-ctx    : ProofCtx gl-mode
    gl-prop   : bProp (to-ctx gl-ctx)
open Goal

SemGoals : List Goal → Set
SemGoals [] = ⊤
SemGoals (goal _ Ξ φ ∷ gls) = SemTm ⟦ Ξ ⟧pctx (⟦ φ ⟧bprop M.[ to-ctx-subst Ξ ]) × SemGoals gls

split-sem-goals : (gls1 gls2 : List Goal) → SemGoals (gls1 ++ gls2) → SemGoals gls1 × SemGoals gls2
split-sem-goals []          gls2 sgls         = tt , sgls
split-sem-goals (gl ∷ gls1) gls2 (sgl , sgls) = let (sgls1 , sgls2) = split-sem-goals gls1 gls2 sgls in (sgl , sgls1) , sgls2

Evidence : (Ξ : ProofCtx m) (φ : bProp (to-ctx Ξ)) → Set
Evidence Ξ φ = SemTm ⟦ Ξ ⟧pctx (⟦ φ ⟧bprop M.[ to-ctx-subst Ξ ])

record PCResult (Ξ : ProofCtx m) (φ : bProp (to-ctx Ξ)) : Set where
  constructor ⟅_,_⟆
  field
    goals : List Goal
    denotation : SemGoals goals → Evidence Ξ φ
open PCResult

pc-result : (goals : List Goal) →
            (SemGoals goals → Evidence Ξ φ) →
            PCResult Ξ φ
pc-result = ⟅_,_⟆

syntax pc-result goals (λ sgoals → b) = ⟅ goals , sgoals ↦ b ⟆


-- Type expressing that the output of a proof check does not contain any goals
ContainsNoGoals : PCResult Ξ φ → Set
ContainsNoGoals ⟅ []    , _ ⟆ = ⊤
ContainsNoGoals ⟅ _ ∷ _ , _ ⟆ = ⊥

denotation-no-goals : (pr : PCResult Ξ φ) → {ContainsNoGoals pr} → Evidence Ξ φ
denotation-no-goals ⟅ [] , ⟦pr⟧ ⟆ = ⟦pr⟧ tt
