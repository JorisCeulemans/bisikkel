--------------------------------------------------
-- Example proofs about guarded streams
--------------------------------------------------

{-# OPTIONS --guardedness #-}

module Applications.GuardedRecursion.Examples.Proofs where

open import Data.Nat hiding (_≡ᵇ_)
open import Data.Unit
import Relation.Binary.PropositionalEquality as Ag

open import Applications.GuardedRecursion.Preliminaries
open import Applications.GuardedRecursion.BiSikkel
open import Applications.GuardedRecursion.Examples.Streams


private variable
  m n : Mode
  Γ Δ : Ctx m
  A B T S : Ty m


--------------------------------------------------
-- Some 2-cell abbreviations

γ : TwoCell constantly (later ⓜ constantly)
γ = 𝟙≤ltr ⓣ-hor id-cell {μ = constantly}

δ : TwoCell constantly (later ⓜ (later ⓜ constantly))
δ = 𝟙≤ltr {0} ⓣ-hor γ


--------------------------------------------------
-- The admissible rule Gcons-Cong from section 4.3 of the paper:
--
-- Ξ ,lock⟨ constantly ⟩ ⊢ h1 ≡ᵇ h2
-- Ξ ,lock⟨ later ⟩ ⊢ t1 ≡ᵇ t2
-- --------------------------------
-- Ξ ⊢ g-cons h1 t1 ≡ᵇ g-cons h2 t2

g-cons-cong : (h1 h2 : Tm (Γ ,lock⟨ constantly ⟩) A) (t1 t2 : Tm (Γ ,lock⟨ later ⟩) (GStream A)) →
              Proof (Γ ,lock⟨ constantly ⟩) → Proof (Γ ,lock⟨ later ⟩) → Proof Γ
g-cons-cong h1 h2 t1 t2 ph pt =
  trans (g-cons h2 t1)
    (subst {x = "dummy"} (g-cons (h1 [ πʳ ,lockʳ⟨ constantly ⟩ ]tmʳ) (t1 [ πʳ ,lockʳ⟨ later ⟩ ]tmʳ) ≡ᵇ g-cons v0 (t1 [ πʳ ,lockʳ⟨ later ⟩ ]tmʳ)) h1 h2 ph refl)
    (subst {x = "dummy"} (g-cons (h2 [ πʳ ,lockʳ⟨ constantly ⟩ ]tmʳ) (t1 [ πʳ ,lockʳ⟨ later ⟩ ]tmʳ) ≡ᵇ g-cons (h2 [ πʳ ,lockʳ⟨ constantly ⟩ ]tmʳ) v0) t1 t2 pt refl)


--------------------------------------------------
-- First, we prove that our implementation of g-map satisfies the
-- defining property of a mapping function, i.e. that mapping a
-- function f over `g-cons a s` equals the stream with `f a` as head
-- and `g-map f s` as tail.

g-map-cons : {Γ : Ctx ω} (A : Ty ★) → bProp Γ
g-map-cons A =
  ∀[ constantly ∣ "f" ∈ A ⇛ A ] ∀[ constantly ∣ "h" ∈ A ] ∀[ later ∣ "s" ∈ GStream A ]
    g-map ∙ svar "f" ∙ g-cons (svar "h") (svar "s")
      ≡ᵇ
    g-cons (svar "f" ∙ svar "h") (g-map ∙ var "f" γ ∙ svar "s")

g-map-cons-proof : {Γ : Ctx ω} (A : Ty ★) → Proof Γ
g-map-cons-proof A =
  ∀-intro[ constantly ∣ "f" ∈ A ⇛ A ]
  ∀-intro[ constantly ∣ "h" ∈ A ]
  ∀-intro[ later ∣ "s" ∈ GStream A ]
  equality-chain
  where
    open ≡ᵇ-Reasoning
    equality-chain =
      begin
        g-map ∙ svar "f" ∙ g-cons (svar "h") (svar "s")
      ≡ᵇ⟨ fun-cong {μ = 𝟙} (with-normalization tmlöb-β) (g-cons (svar "h") (svar "s")) ⟩
        (lam[ "as" ∈ GStream A ]
          let' mod⟨ constantly ⟩ "head-as" ← g-head (svar "as") in'
          let' mod⟨ later ⟩ "tail-as" ← g-tail (svar "as") in' (
          g-cons (svar "f" ∙ svar "head-as")
                 (g-map ∙ var "f" γ ∙ svar "tail-as")))
        ∙ g-cons (svar "h") (svar "s")
      ≡ᵇ⟨ by-normalization ⟩
        g-cons (svar "f" ∙ svar "h") (g-map ∙ var "f" γ ∙ svar "s") ∎

test-g-map-cons : IsOk (check-proof ◇ (g-map-cons-proof Nat') (g-map-cons Nat'))
test-g-map-cons = tt


--------------------------------------------------
-- Proof that g-iterate' satisfies its specification as shown at the
-- end of Section 3.1 of the paper (i.e. `g-iterate' f a` equals
-- `g-cons a (g-iterate' f (f a))`). This needs explicit proof because
-- löb-induction for terms does not unfold (because of
-- undecidability).

g-iterate'-cons : {Γ : Ctx ω} (A : Ty ★) → bProp Γ
g-iterate'-cons A =
  ∀[ constantly ∣ "f" ∈ A ⇛ A ] ∀[ constantly ∣ "a" ∈ A ]
    g-iterate' ∙ var "f" γ ∙ svar "a"
      ≡ᵇ
    g-cons (svar "a") (g-iterate' ∙ var "f" δ ∙ (var "f" γ ∙ var "a" γ))

g-iterate'-cons-proof : {Γ : Ctx ω} (A : Ty ★) → Proof Γ
g-iterate'-cons-proof A = ∀-intro[ constantly ∣ "f" ∈ A ⇛ A ] ∀-intro[ constantly ∣ "a" ∈ A ] equality-chain
  where
    open ≡ᵇ-Reasoning
    equality-chain =
      begin
        g-iterate' ∙ var "f" γ ∙ svar "a"
      ≡ᵇ⟨ fun-cong (with-normalization tmlöb-β) (svar "a") ⟩
        (lam[ constantly ∣ "a" ∈ A ] g-cons (svar "a") (g-iterate' ∙ var "f" δ ∙ (var "f" γ ∙ var "a" γ)))
        ∙ svar "a"
      ≡ᵇ⟨ by-normalization ⟩
        g-cons (svar "a") (g-iterate' ∙ var "f" δ ∙ (var "f" γ ∙ var "a" γ)) ∎

test-g-iterate'-cons : IsOk (check-proof ◇ (g-iterate'-cons-proof Nat') (g-iterate'-cons Nat'))
test-g-iterate'-cons = tt


--------------------------------------------------
-- Proof of the lemma in Section 4.3 of the paper

g-map-iterate : {Γ : Ctx ω} (A : Ty ★) → bProp Γ
g-map-iterate A =
  ∀[ constantly ∣ "f" ∈ A ⇛ A ] ∀[ constantly ∣ "a" ∈ A ]
    g-map ∙ svar "f" ∙ (g-iterate ∙ var "f" γ ∙ svar "a")
      ≡ᵇ
    g-iterate ∙ var "f" γ ∙ (svar "f" ∙ svar "a")

g-map-iterate-proof : {Γ : Ctx ω} (A : Ty ★) → Proof Γ
g-map-iterate-proof A =
  ∀-intro[ constantly ∣ "f" ∈ A ⇛ A ]
  ∀-intro[ constantly ∣ "a" ∈ A ]
  pflöb "ih" equality-chain
  where
    open ≡ᵇ-Reasoning
    equality-chain =
      begin
        g-map ∙ svar "f" ∙ (g-iterate ∙ var "f" γ ∙ svar "a")
      ≡ᵇ⟨ cong (g-map ∙ svar "f") (with-normalization tmlöb-β) ⟩
        g-map ∙ svar "f" ∙ (g-cons (svar "a") (g-map ∙ var "f" γ ∙ (g-iterate ∙ var "f" δ ∙ var "a" γ)))
      ≡ᵇ⟨ ∀-elim later (∀[ later ∣ "s" ∈ GStream A ] g-map ∙ svar "f" ∙ (g-cons (svar "a") (svar "s")) ≡ᵇ g-cons (svar "f" ∙ svar "a") (g-map ∙ var "f" γ ∙ svar "s"))
           (∀-elim constantly (∀[ constantly ∣ "h" ∈ A ] ∀[ later ∣ "s" ∈ GStream A ]
                                  g-map ∙ svar "f" ∙ (g-cons (svar "h") (svar "s")) ≡ᵇ g-cons (svar "f" ∙ svar "h") (g-map ∙ var "f" γ ∙ svar "s"))
             (∀-elim constantly (g-map-cons A)
               (g-map-cons-proof A)
               (svar "f"))
             (svar "a"))
           (g-map ∙ var "f" γ ∙ (g-iterate ∙ var "f" δ ∙ var "a" γ))
        ⟩
        g-cons (svar "f" ∙ svar "a") (g-map ∙ var "f" γ ∙ (g-map ∙ var "f" γ ∙ (g-iterate ∙ var "f" δ ∙ var "a" γ)))
      ≡ᵇ⟨ g-cons-cong (svar "f" ∙ svar "a")
                      (svar "f" ∙ svar "a")
                      (g-map ∙ var "f" γ ∙ (g-map ∙ var "f" γ ∙ (g-iterate ∙ var "f" δ ∙ var "a" γ)))
                      (g-map ∙ var "f" γ ∙ (g-iterate ∙ var "f" δ ∙ (var "f" γ ∙ var "a" γ)))
                      refl
                      (cong (g-map ∙ var "f" γ) (assumption' "ih" (id-cell {μ = later})))
        ⟩
        g-cons (svar "f" ∙ svar "a") (g-map ∙ var "f" γ ∙ (g-iterate ∙ var "f" δ ∙ (var "f" γ ∙ var "a" γ)))
      ≡ᵇ⟨ with-normalization tmlöb-β ⟨
        g-iterate ∙ var "f" γ ∙ (svar "f" ∙ svar "a") ∎

test-g-map-iterate : IsOk (check-proof ◇ (g-map-iterate-proof Nat') (g-map-iterate Nat'))
test-g-map-iterate = tt


--------------------------------------------------
-- Proof of the final result in Section 4.3 of the paper

g-iterate-iterate' : {Γ : Ctx ω} (A : Ty ★) → bProp Γ
g-iterate-iterate' A =
  ∀[ constantly ∣ "f" ∈ Nat' ⇛ Nat' ] ∀[ constantly ∣ "a" ∈ Nat' ]
    g-iterate ∙ var "f" γ ∙ svar "a"
      ≡ᵇ
    g-iterate' ∙ var "f" γ ∙ svar "a"

g-iterate-iterate'-proof : {Γ : Ctx ω} (A : Ty ★) → Proof Γ
g-iterate-iterate'-proof A =
  ∀-intro[ constantly ∣ "f" ∈ A ⇛ A ] pflöb "ih" (∀-intro[ constantly ∣ "a" ∈ A ] equality-chain)
  where
    open ≡ᵇ-Reasoning
    equality-chain =
      begin
        g-iterate ∙ var "f" γ ∙ svar "a"
      ≡ᵇ⟨ with-normalization tmlöb-β ⟩
        g-cons (svar "a") (g-map ∙ var "f" γ ∙ (g-iterate ∙ var "f" δ ∙ var "a" γ))
      ≡ᵇ⟨ g-cons-cong (svar "a") (svar "a") (g-map ∙ var "f" γ ∙ (g-iterate ∙ var "f" δ ∙ var "a" γ)) (g-iterate ∙ var "f" δ ∙ (var "f" γ ∙ var "a" γ))
           refl (∀-elim constantly (∀[ constantly ∣ "a" ∈ A ] g-map ∙ var "f" γ ∙ (g-iterate ∙ var "f" δ ∙ svar "a") ≡ᵇ g-iterate ∙ var "f" δ ∙ (var "f" γ ∙ svar "a"))
                   (∀-elim constantly (g-map-iterate A)
                     (g-map-iterate-proof A)
                     (var "f" γ))
                   (var "a" γ))
        ⟩
        g-cons (svar "a") (g-iterate ∙ var "f" δ ∙ (var "f" γ ∙ var "a" γ))
      ≡ᵇ⟨ g-cons-cong (svar "a") (svar "a") (g-iterate ∙ var "f" δ ∙ (var "f" γ ∙ var "a" γ)) (g-iterate' ∙ var "f" δ ∙ (var "f" γ ∙ var "a" γ))
            refl
            (∀-elim constantly (∀[ constantly ∣ "a" ∈ A ] g-iterate ∙ var "f" δ ∙ svar "a" ≡ᵇ g-iterate' ∙ var "f" δ ∙ svar "a")
                    (assumption' "ih" (id-cell {μ = later}))
                    (var "f" γ ∙ var "a" γ))
        ⟩
        g-cons (svar "a") (g-iterate' ∙ var "f" δ ∙ (var "f" γ ∙ var "a" γ))
      ≡ᵇ⟨ ∀-elim constantly (∀[ constantly ∣ "a" ∈ A ] g-iterate' ∙ var "f" γ ∙ svar "a" ≡ᵇ g-cons (svar "a") (g-iterate' ∙ var "f" δ ∙ (var "f" γ ∙ var "a" γ)))
            (∀-elim constantly (g-iterate'-cons A)
              (g-iterate'-cons-proof A)
              (svar "f"))
            (svar "a")
        ⟨
        g-iterate' ∙ var "f" γ ∙ svar "a" ∎

test-g-iterate-iterate' : IsOk (check-proof ◇ (g-iterate-iterate'-proof Nat') (g-iterate-iterate' Nat'))
test-g-iterate-iterate' = tt


--------------------------------------------------
-- Proof of another admissible principle (cong rule for modal constructor)

-- Ξ ,lock⟨ μ ⟩ ⊢ t1 ≡ᵇ t2
-- --------------------------------
-- Ξ ⊢ mod⟨ μ ⟩ t1 ≡ᵇ mod⟨ μ ⟩ t2

mod-cong : (μ : Modality m n) (t1 t2 : Tm (Γ ,lock⟨ μ ⟩) T) →
           Proof (Γ ,lock⟨ μ ⟩) → Proof Γ
mod-cong μ t1 t2 p =
  subst {x = "dummy"} (mod⟨ μ ⟩ (t1 [ πʳ ,lockʳ⟨ μ ⟩ ]tmʳ) ≡ᵇ mod⟨ μ ⟩ v0) t1 t2 p refl


--------------------------------------------------
-- Proof of a similar result as g-iterate-iterate' above, but now for
-- "standard" streams at mode ★ rather than for guarded streams
-- The proof makes use of the proof of g-iterate-iterate'.

iterate-iterate' : (A : Ty ★) → bProp {★} Γ
iterate-iterate' A =
  ∀[ 𝟙 ∣ "f" ∈ A ⇛ A ] ∀[ 𝟙 ∣ "a" ∈ A ]
    iterate ∙ svar "f" ∙ svar "a" ≡ᵇ iterate' ∙ svar "f" ∙ svar "a"

iterate-iterate'-proof : (A : Ty ★) → Proof {★} Γ
iterate-iterate'-proof A =
  ∀-intro[ 𝟙 ∣ "f" ∈ A ⇛ A ] ∀-intro[ 𝟙 ∣ "a" ∈ A ]
    with-normalizationᵇ (mod⟨ forever ⟩ (g-iterate ∙ svar "f" ∙ svar "a")) (mod⟨ forever ⟩ (g-iterate' ∙ svar "f" ∙ svar "a")) (
    mod-cong forever (g-iterate ∙ svar "f" ∙ svar "a") (g-iterate' ∙ svar "f" ∙ svar "a")
      (∀-elim constantly (∀[ constantly ∣ "a" ∈ A ] g-iterate ∙ svar "f" ∙ svar "a" ≡ᵇ g-iterate' ∙ svar "f" ∙ svar "a")
        (∀-elim constantly (g-iterate-iterate' A)
          (g-iterate-iterate'-proof A)
          (svar "f"))
        (svar "a"))
    )

test-iterate-iterate'-proof : IsOk (check-proof ◇ (iterate-iterate'-proof Nat') (iterate-iterate' Nat'))
test-iterate-iterate'-proof = tt

-- The proof obtained above can be extracted as shown below, but Agda
-- takes too much time to compute that the inferred type of
-- test-iterate-iterate'-extract is equal to the expected type
-- `(f : ℕ → ℕ) (a : ℕ) → iterateℕ f a ≡ iterate'ℕ f a`.
test-iterate-iterate'-extract : _
test-iterate-iterate'-extract = extract-proof ◇ (iterate-iterate'-proof Nat') (iterate-iterate' Nat') tt


--------------------------------------------------
-- Two very simple examples showcasing proof extraction (Agda is too
-- slow for extraction of the examples above)

stream-refl-prop : bProp {★} ◇
stream-refl-prop = ∀[ 𝟙 ∣ "s" ∈ Stream' Nat' ] svar "s" ≡ᵇ svar "s"

stream-refl-proof : Proof {★} ◇
stream-refl-proof = ∀-intro[ 𝟙 ∣ "s" ∈ Stream' Nat' ] refl

stream-refl-extract : (s : Stream ℕ) → s Ag.≡ s
stream-refl-extract = extract-proof-◇ stream-refl-proof stream-refl-prop

-- An example with a term containing Löb recursion
zeros-refl-prop : bProp {★} ◇
zeros-refl-prop = zeros ≡ᵇ zeros

zeros-refl-proof : Proof {★} ◇
zeros-refl-proof = refl

zeros-refl-extract : zeros-extract Ag.≡ zeros-extract
zeros-refl-extract = extract-proof-◇ zeros-refl-proof zeros-refl-prop
