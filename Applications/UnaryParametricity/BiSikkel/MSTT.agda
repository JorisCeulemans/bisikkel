--------------------------------------------------
-- MSTT instance for unary parametricity
--------------------------------------------------

module Applications.UnaryParametricity.BiSikkel.MSTT where

open import Data.Nat
open import Data.Unit
open import Function.Construct.Identity

open import BiSikkel.MSTT.Parameter.ModeTheory
open import BiSikkel.MSTT.Parameter

import Applications.UnaryParametricity.BiSikkel.ModeTheory as UPMT
open import Applications.UnaryParametricity.BiSikkel.TypeExtension
open import Applications.UnaryParametricity.BiSikkel.TermExtension

open UPMT
  using (↑; forget; Σ;  unary-param-mt; π-cell)
  public
open ModeTheory unary-param-mt public

unary-param-mstt : MSTT-Parameter
MSTT-Parameter.ℳ unary-param-mstt = unary-param-mt
MSTT-Parameter.𝒯 unary-param-mstt = unary-param-ty-ext
MSTT-Parameter.𝓉 unary-param-mstt = unary-param-tm-ext
MSTT-Parameter.⟦𝓉⟧ unary-param-mstt = unary-param-tm-ext-sem
MSTT-Parameter.𝓉-norm unary-param-mstt = unary-param-tm-ext-norm


open import BiSikkel.MSTT unary-param-mstt public


pattern EncBool = Ext BinaryBool-code tt
pattern enc-true = ext true-code tt tt refl
pattern enc-false = ext false-code tt tt refl
pattern ∧' = ext and-code tt tt refl
pattern ¬' = ext not-code tt tt refl


instance
  forgetEncBoolExtractable : ExtractableTy ⟨ forget ∣ EncBool ⟩
  ExtractableTy.AgdaTy forgetEncBoolExtractable = ℕ
  ExtractableTy.extract-ty-iso-◇ forgetEncBoolExtractable = ↔-id _
