--------------------------------------------------
-- An instance of MSTT can be extended with custom term constructors, and this
--   file provides the interface to do so. MSTT is parametrized by a record of
--   type TmExt, which specifies a universe of codes for the new term constructors
--   and their interpretation in a presheaf model.
--   Every code in the universe comes with information about its type
--   and the context and type for each of its arguments. The context
--   of an argument is obtained by adding a telescope to the context
--   of the current term.
--------------------------------------------------

open import BiSikkel.MSTT.Parameter.ModeTheory
open import BiSikkel.MSTT.Parameter.TypeExtension

module BiSikkel.MSTT.Parameter.TermExtension
  (ℳ : ModeTheory) (𝒯 : TyExt ℳ)
  where

open import Data.List
open import Relation.Binary.PropositionalEquality

open import BiSikkel.LogicalFramework.Proof.CheckingMonad
open import BiSikkel.MSTT.Syntax.Types ℳ 𝒯
open import BiSikkel.MSTT.Syntax.Contexts ℳ 𝒯

open ModeTheory ℳ

private variable
  m : Mode


-- A value of type TmArgInfo m contains the information about an
-- argument to a term constructor in mode m, i.e. the mode of the
-- argument, how the context should be modified, and the type of the
-- argument. The names of the variables that get bound in the
-- arguments should not be provided at this point (hence a
-- NamelessTele) but when a new term is constructed. This makes
-- checking for α-equivalence easier.
record TmArgInfo (m : Mode) : Set where
  no-eta-equality
  constructor tmarg-info
  field
    {n} : Mode
    tmarg-tel : NamelessTele m n
    tmarg-ty : Ty n
open TmArgInfo public hiding (n)


record TmExt : Set₁ where
  no-eta-equality
  field
    TmExtCode : (m : Mode) → Set
      -- ^ The universe of codes, every code corresponds to a new term former.
    _≟tm-code_ : (c1 c2 : TmExtCode m) → PCM (c1 ≡ c2)
      -- ^ We should be able to test codes for equality.
    tm-code-ty : TmExtCode m → Ty m
      -- ^ Specification of the type of every new term former.
    tm-code-arginfos : TmExtCode m → List (TmArgInfo m)
      -- ^ Every new term former can take a number of terms as
      --   arguments, their types and context modifications are
      --   collected here.
