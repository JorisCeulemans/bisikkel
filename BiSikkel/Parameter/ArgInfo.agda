open import BiSikkel.MSTT.Parameter.ModeTheory
open import BiSikkel.MSTT.Parameter.TypeExtension
open import BiSikkel.MSTT.Parameter.TermExtension using (TmExt)

module BiSikkel.Parameter.ArgInfo
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ)
  where


open import Data.List
open import Data.Product
open import Data.Unit

open import BiSikkel.MSTT.Syntax.Contexts ℳ 𝒯

open ModeTheory ℳ


record ArgInfo (m : Mode) : Set where
  no-eta-equality
  constructor arg-info
  field
    {mode} : Mode
    arg-tel : NamelessTele m mode
open ArgInfo public hiding (mode)

ArgBoundNames : {m : Mode} → List (ArgInfo m) → Set
ArgBoundNames []                   = ⊤
ArgBoundNames (arginfo ∷ arginfos) = Names (arg-tel arginfo) × ArgBoundNames arginfos
