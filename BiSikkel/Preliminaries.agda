--------------------------------------------------
-- Axioms & some definitions that are not included in the standard library
--------------------------------------------------

module BiSikkel.Preliminaries where

open import Axiom.Extensionality.Propositional
open import Axiom.UniquenessOfIdentityProofs
open import Data.Product renaming (_,_ to [_,_])
open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Relation.Binary.Core using (REL)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Reasoning.Syntax

private
  variable
    a ℓ ℓ' ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    A B C : Set a


--------------------------------------------------
-- Axioms used in BiSikkel

-- Function extensionality (both for normal and implicit functions)
postulate
  funext : ∀ {ℓ ℓ'} → Extensionality ℓ ℓ'
  funextI : ∀ {ℓ ℓ'} → ExtensionalityImplicit ℓ ℓ'

-- Strictly speaking not an axiom (uip is enabled by default in Agda)
uip : ∀ {a} {A : Set a} → UIP A
uip refl refl = refl


--------------------------------------------------
-- Some results about propositional equality

cong₂-d : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Set c}
          (f : (x : A) → B x → C)
          {x x' : A} {y : B x} {y' : B x'}
          (ex : x ≡ x') (ey : subst B ex y ≡ y') →
          f x y ≡ f x' y'
cong₂-d f refl refl = refl

to-Σ-eq : {A : Set ℓ} {B : A → Set ℓ'}
          {a a' : A} {b : B a} {b' : B a'}
          (e1 : a ≡ a') (e2 : subst B e1 b ≡ b') →
          [ a , b ] ≡ [ a' , b' ]
to-Σ-eq e1 e2 = cong₂-d [_,_] e1 e2

from-Σ-eq1 : {A : Set ℓ} {B : A → Set ℓ'}
             {p q : Σ A B} →
             p ≡ q → proj₁ p ≡ proj₁ q
from-Σ-eq1 e = cong proj₁ e

from-Σ-eq2 : {A : Set ℓ} {B : A → Set ℓ'}
             {p q : Σ A B} →
             (e : p ≡ q) →
             subst B (from-Σ-eq1 e) (proj₂ p) ≡ proj₂ q
from-Σ-eq2 refl = refl

from-to-Σ-eq1 : ∀ {a b} {A : Set a} {B : A → Set b}
                {x x' : A} {y : B x} {y' : B x'}
                {ex : x ≡ x'} (ey : subst B ex y ≡ y') →
                from-Σ-eq1 (to-Σ-eq ex ey) ≡ ex
from-to-Σ-eq1 {ex = refl} refl = refl


--------------------------------------------------
-- Extension of syntax for reasoning combinators to include the ones for ≅
-- They are used for the various forms of equivalence in the presheaf
-- model formalization.

module ≅-syntax
  {R : REL A B ℓ₂}
  (S : REL B C ℓ₁)
  (T : REL A C ℓ₃)
  (step : Trans R S T)
  {U : REL B A ℓ₄}
  (sym : Sym U R)
  where

  infixr 2 step-≅-⟩ step-≅-⟨ step-≅-∣
  step-≅-⟩ = forward S T step
  step-≅-⟨ = backward S T step sym

  step-≅-∣ : ∀ x {y} → R x y → R x y
  step-≅-∣ x xRy = xRy

  syntax step-≅-⟩ x yRz x≅y = x ≅⟨ x≅y ⟩ yRz
  syntax step-≅-⟨ x yRz y≅x = x ≅⟨ y≅x ⟨ yRz
  syntax step-≅-∣ x xRy     = x ≅⟨⟩ xRy
