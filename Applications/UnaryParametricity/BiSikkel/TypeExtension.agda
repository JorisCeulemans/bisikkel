--------------------------------------------------
-- Specification of new type constructors for unary parametricity
--------------------------------------------------

module Applications.UnaryParametricity.BiSikkel.TypeExtension where

open import Data.List
open import Data.String as Str
open import Relation.Binary.PropositionalEquality

import Applications.UnaryParametricity.Model as M

open import BiSikkel.MSTT.Parameter.ModeTheory
open import BiSikkel.MSTT.Parameter.TypeExtension

open import BiSikkel.LogicalFramework.Proof.CheckingMonad

import Applications.UnaryParametricity.BiSikkel.ModeTheory as UPMT
open UPMT using (unary-param-mt; ↑)
open ModeTheory unary-param-mt

private variable
  m : Mode
  margs : List Mode


data TyExtCode : List Mode → Mode → Set where
  BinaryBool-code : TyExtCode [] ↑

unary-param-ty-ext : TyExt unary-param-mt
TyExt.TyExtCode unary-param-ty-ext = TyExtCode
TyExt._≟ty-code_ unary-param-ty-ext BinaryBool-code BinaryBool-code = return refl
TyExt.show-ty-code unary-param-ty-ext BinaryBool-code = "BinaryBool-code"
TyExt.⟦_⟧ty-code unary-param-ty-ext BinaryBool-code = M.BinaryBool
TyExt.sem-ty-code-natural unary-param-ty-ext BinaryBool-code = M.frompred-natural
