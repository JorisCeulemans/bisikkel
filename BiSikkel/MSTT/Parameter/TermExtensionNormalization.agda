--------------------------------------------------
-- When new term constructors are added to MSTT, one should also
-- specify how they should be normalized (and provide a soundness
-- proof)
--------------------------------------------------

open import BiSikkel.MSTT.Parameter.ModeTheory
open import BiSikkel.MSTT.Parameter.TypeExtension
open import BiSikkel.MSTT.Parameter.TermExtension using (TmExt)
open import BiSikkel.MSTT.Parameter.TermExtensionSemantics

module BiSikkel.MSTT.Parameter.TermExtensionNormalization
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ) (𝓉 : TmExt ℳ 𝒯) (⟦𝓉⟧ : TmExtSem ℳ 𝒯 𝓉)
  where

open import Data.Maybe

open BiSikkel.MSTT.Parameter.TermExtension ℳ 𝒯
  hiding (TmExt)
open TmExt 𝓉
open import BiSikkel.MSTT.Syntax.Types ℳ 𝒯
open import BiSikkel.MSTT.Syntax.Contexts ℳ 𝒯
open import BiSikkel.MSTT.Syntax.Terms ℳ 𝒯 𝓉
open import BiSikkel.MSTT.Normalization.ResultType ℳ 𝒯 𝓉 ⟦𝓉⟧ public

open ModeTheory ℳ

private variable
  m n : Mode
  Γ : Ctx m


-- When specifying how terms formed by new term constructors should be
-- normalized, one can normalize the subterms (or other terms) by the
-- normalization function given as first argument to
-- normalize-tm-code. This recursive call will consume one unit of
-- fuel.
record TmExtNormalization : Set where
  field
    normalize-tm-code : ({n : Mode} {Γ : Ctx n} {T : Ty n} (t : Tm Γ T) → Maybe (NormalizeResult t)) →
                        {m : Mode} (c : TmExtCode m) {bound-names : TmArgBoundNames (tm-code-arginfos c)} {Γ : Ctx m}
                        (tmargs : ExtTmArgs (tm-code-arginfos c) bound-names Γ) →
                        Maybe (NormalizeResult (ext c bound-names tmargs refl))
