--------------------------------------------------
-- Record type containing information to be stored with arguments of
-- extended bProp/proof constructors
--------------------------------------------------

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


-- A value of type ArgInfo m contains the information about an
-- argument to a bProp or proof constructor in mode m, i.e. the mode
-- of the argument and how the context should be modified. The names
-- of the variables that get bound in the arguments should not be
-- provided at this point (hence a NamelessTele) but when a new
-- bProp/proof is constructed.
record ArgInfo (m : Mode) : Set where
  no-eta-equality
  constructor arg-info
  field
    {mode} : Mode
    arg-tel : NamelessTele m mode
open ArgInfo public hiding (mode)

-- Type of names matching a list of arginfos
ArgBoundNames : {m : Mode} → List (ArgInfo m) → Set
ArgBoundNames []                   = ⊤
ArgBoundNames (arginfo ∷ arginfos) = Names (arg-tel arginfo) × ArgBoundNames arginfos
