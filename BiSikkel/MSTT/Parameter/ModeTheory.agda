--------------------------------------------------
-- Description of an M(S)TT mode theory
--------------------------------------------------


module BiSikkel.MSTT.Parameter.ModeTheory where

open import Data.Maybe using (Maybe)
open import Relation.Binary.PropositionalEquality

open import BiSikkel.Model.BaseCategory as M using (BaseCategory)
open import BiSikkel.Model.CwF-Structure as M renaming (Ctx to SemCtx; Ty to SemTy; Tm to SemTm) using ()
open import BiSikkel.Model.DRA as DRA hiding (𝟙; TwoCell; id-cell; _ⓣ-vert_; _ⓣ-hor_)

open import BiSikkel.LogicalFramework.Proof.CheckingMonad


--------------------------------------------------
-- Modes
-- Note that a user must only specify mode different from the trivial
-- mode ★. The latter is automatically included.

record MTMode : Set₁ where
  no-eta-equality
  field
    NonTrivMode : Set
      -- ^ A mode is either the trivial mode ★ or a non-trivial mode
      --   described above. In this way, we make sure that the
      --   interpretation of the trivial mode is definitionally the
      --   trivial base category.
    non-triv-mode-eq? : (m n : NonTrivMode) → Maybe (m ≡ n)
      -- ^ Semi-decision procedure for propositional equality of modes
    ⟦_⟧non-triv-mode : NonTrivMode → BaseCategory
      -- ^ Interpretation of modes as base categories

  data Mode : Set where
    ★ : Mode
      -- ^ The trivial mode
    ‵_ : NonTrivMode → Mode

  mode-msg : ErrorMsg
  mode-msg = "Modes are not equal."

  _≟mode_ : (m n : Mode) → PCM (m ≡ n)
  ★ ≟mode ★ = return refl
  (‵ m) ≟mode (‵ n) = cong (‵_) <$> from-maybe mode-msg (non-triv-mode-eq? m n)
  _ ≟mode _ = throw-error mode-msg

  ⟦_⟧mode : Mode → BaseCategory
  ⟦ ★ ⟧mode = M.★
  ⟦ ‵ m ⟧mode = ⟦ m ⟧non-triv-mode


--------------------------------------------------
-- Modalities
-- Note that we include some form of strictification: a user does not
-- need to specify the unit modality 𝟙, only the non-trivial
-- modalities. The unit modality is automatically included. This way,
-- the interpretation of the unit modality is definitionally the
-- semantic unit modality, and 𝟙 is definitionally a left unit of
-- modality composition ⓜ.

record MTModality (mtm : MTMode) : Set₁ where
  no-eta-equality

  open MTMode mtm

  field
    NonTrivModality : Mode → Mode → Set
    non-triv-mod-eq? : ∀ {m n} (μ κ : NonTrivModality m n) → Maybe (μ ≡ κ)
      -- ^ Semi-decision procedure for propositional equality of modalities
    ⟦_⟧non-triv-mod : ∀ {m n} → NonTrivModality m n → DRA ⟦ m ⟧mode ⟦ n ⟧mode
      -- ^ Interpretation of modalities as DRAs

  infix 50 ‵_
  data Modality : Mode → Mode → Set where
    𝟙 : ∀ {m} → Modality m m
    ‵_ : ∀ {m n} → NonTrivModality m n → Modality m n

  mod-dom mod-cod : ∀ {m n} → Modality m n → Mode
  mod-dom {m}     μ = m
  mod-cod {_} {n} μ = n

  ⟦_⟧mod : ∀ {m n} → Modality m n → DRA ⟦ m ⟧mode ⟦ n ⟧mode
  ⟦ 𝟙 ⟧mod = DRA.𝟙
  ⟦ ‵ μ ⟧mod = ⟦ μ ⟧non-triv-mod

  ⟦𝟙⟧-sound : ∀ {m} → ⟦ 𝟙 {m} ⟧mod ≅ᵈ DRA.𝟙
  ⟦𝟙⟧-sound = DRA.reflᵈ

  modality-msg : ErrorMsg
  modality-msg = "Modalities are not equal."

  _≟mod_ : {m n : Mode} (μ κ : Modality m n) → PCM (μ ≡ κ)
  𝟙 ≟mod 𝟙 = return refl
  ‵ μ ≟mod ‵ κ = cong (‵_) <$> from-maybe modality-msg (non-triv-mod-eq? μ κ)
  _ ≟mod _ = throw-error modality-msg


--------------------------------------------------
-- Composition of modalities

record MTComposition (mtm : MTMode) (mtμ : MTModality mtm) : Set₁ where
  no-eta-equality

  open MTMode mtm
  open MTModality mtμ

  field
    _ⓜnon-triv_ : ∀ {m n o} → NonTrivModality n o → NonTrivModality m n → Modality m o

    ⟦ⓜ⟧-non-triv-sound : ∀ {m n o} (μ : NonTrivModality n o) (κ : NonTrivModality m n) →
                         ⟦ μ ⓜnon-triv κ ⟧mod ≅ᵈ ⟦ μ ⟧non-triv-mod DRA.ⓓ ⟦ κ ⟧non-triv-mod
      -- ^ Semantically, the composition of modalities should be equivalent to the composition of DRAs.

  _ⓜ_ : ∀ {m n o} → Modality n o → Modality m n → Modality m o
  μ   ⓜ 𝟙 = μ
  𝟙   ⓜ ‵ ρ = ‵ ρ
  ‵ μ ⓜ ‵ ρ = μ ⓜnon-triv ρ

  ⟦ⓜ⟧-sound : ∀ {m n o} (μ : Modality n o) (κ : Modality m n) → ⟦ μ ⓜ κ ⟧mod ≅ᵈ ⟦ μ ⟧mod ⓓ ⟦ κ ⟧mod
  ⟦ⓜ⟧-sound μ     𝟙     = symᵈ (𝟙-unitʳ _)
  ⟦ⓜ⟧-sound 𝟙     (‵ κ) = symᵈ (𝟙-unitˡ _)
  ⟦ⓜ⟧-sound (‵ μ) (‵ κ) = ⟦ⓜ⟧-non-triv-sound μ κ


--------------------------------------------------
-- Associativity of modality composition

record MTCompositionLaws (mtm : MTMode) (mtμ : MTModality mtm) (mtc : MTComposition mtm mtμ) : Set where
  no-eta-equality

  open MTMode mtm
  open MTModality mtμ
  open MTComposition mtc
  
  field
    mod-non-triv-assoc : ∀ {m n o p} → (μ : NonTrivModality o p) (ρ : NonTrivModality n o) (κ : NonTrivModality m n) →
                         (μ ⓜnon-triv ρ) ⓜ ‵ κ ≡ ‵ μ ⓜ (ρ ⓜnon-triv κ)

  mod-unitˡ : ∀ {m n} {μ : Modality m n} → 𝟙 ⓜ μ ≡ μ
  mod-unitˡ {μ = 𝟙}   = refl
  mod-unitˡ {μ = ‵ μ} = refl

  mod-unitʳ : ∀ {m n} {μ : Modality m n} → μ ⓜ 𝟙 ≡ μ
  mod-unitʳ = refl

  mod-assoc : ∀ {m n o p} {μ : Modality o p} {ρ : Modality n o} (κ : Modality m n) → (μ ⓜ ρ) ⓜ κ ≡ μ ⓜ (ρ ⓜ κ)
  mod-assoc 𝟙 = refl
  mod-assoc {ρ = 𝟙} (‵ κ) = refl
  mod-assoc {μ = 𝟙} {ρ = ‵ ρ} (‵ κ) = sym mod-unitˡ
  mod-assoc {μ = ‵ μ} {ρ = ‵ ρ} (‵ κ) = mod-non-triv-assoc μ ρ κ


--------------------------------------------------
-- Two-cells and corresponding operations

record MTTwoCell (mtm : MTMode) (mtμ : MTModality mtm) (mtc : MTComposition mtm mtμ) : Set₁ where
  no-eta-equality

  open MTMode mtm
  open MTModality mtμ
  open MTComposition mtc

  infixl 6 _ⓣ-vert_
  infixl 5 _ⓣ-hor_
  field
    TwoCell : ∀ {m n} (μ ρ : Modality m n) → Set
      -- ^ Type of two-cells from μ to ρ
    id-cell : ∀ {m n} {μ : Modality m n} → TwoCell μ μ
      -- ^ The identity two-cell
    _ⓣ-vert_ : ∀ {m n} {μ ρ κ : Modality m n} → TwoCell ρ κ → TwoCell μ ρ → TwoCell μ κ
      -- ^ Vertical composition of two-cells
    _ⓣ-hor_ : ∀ {m n o} {μ1 ρ1 : Modality n o} {μ2 ρ2 : Modality m n} →
              TwoCell μ1 ρ1 → TwoCell μ2 ρ2 → TwoCell (μ1 ⓜ μ2) (ρ1 ⓜ ρ2)
      -- ^ Horizontal composition of two-cells
    two-cell-eq? : ∀ {m n} {μ ρ : Modality m n} (α β : TwoCell μ ρ) → Maybe (α ≡ β)
      -- ^ Semi-decision procedure for propositional equality of two-cells

    ⟦_⟧two-cell : ∀ {m n} {μ κ : Modality m n} → TwoCell μ κ → DRA.TwoCell ⟦ μ ⟧mod ⟦ κ ⟧mod
      -- ^ Interpretation of two-cells as semantic two-cells between DRAs

  eq-cell : ∀ {m n} {μ ρ : Modality m n} → μ ≡ ρ → TwoCell μ ρ
  eq-cell refl = id-cell

  _≟cell_ : {m n : Mode} {μ κ : Modality m n} (α β : TwoCell μ κ) → PCM (α ≡ β)
  α ≟cell β = from-maybe "Two-cells are not equal." (two-cell-eq? α β)


--------------------------------------------------
-- Two-cell laws
-- In fact, we have a 2-category of modes, modalities and 2-cells. The
-- interpretation function ⟦_⟧ should produce a pseudofunctor from
-- this 2-category to the 2-category of base categories, DRAs and
-- semantic two-cells. The laws below are some of the pseudofunctor
-- laws (but only those that are needed in the development of
-- BiSikkel).

record MTTwoCellLaws
  (mtm : MTMode)
  (mtμ : MTModality mtm)
  (mtc : MTComposition mtm mtμ)
  (mtc-laws : MTCompositionLaws mtm mtμ mtc)
  (mt2 : MTTwoCell mtm mtμ mtc)
  : Set₁
  where
  no-eta-equality

  open MTMode mtm
  open MTModality mtμ
  open MTComposition mtc
  open MTCompositionLaws mtc-laws
  open MTTwoCell mt2

  field
    ⟦id-cell⟧-sound : ∀ {m n} {μ : Modality m n} → ⟦ id-cell {μ = μ} ⟧two-cell DRA.≅ᵗᶜ DRA.id-cell
    ⟦ⓣ-vert⟧-sound : ∀ {m n} {μ κ ρ : Modality m n}
                     (β : TwoCell κ ρ) (α : TwoCell μ κ) →
                     ⟦ β ⓣ-vert α ⟧two-cell DRA.≅ᵗᶜ ⟦ β ⟧two-cell DRA.ⓣ-vert ⟦ α ⟧two-cell
    ⟦ⓜ⟧-sound-natural : ∀ {m n o} {μ μ' : Modality n o} {ρ ρ' : Modality m n}
                        (α : TwoCell μ μ') (β : TwoCell ρ ρ') →
                        from (⟦ⓜ⟧-sound μ' ρ') DRA.ⓣ-vert ⟦ α ⓣ-hor β ⟧two-cell
                          DRA.≅ᵗᶜ
                        (⟦ α ⟧two-cell DRA.ⓣ-hor ⟦ β ⟧two-cell) DRA.ⓣ-vert from (⟦ⓜ⟧-sound μ ρ)
    ⟦associator⟧ : ∀ {m n o p} {μ : Modality o p} {ρ : Modality n o} (κ : Modality m n) →
                   ((DRA.id-cell DRA.ⓣ-hor from (⟦ⓜ⟧-sound ρ κ))
                   DRA.ⓣ-vert from (⟦ⓜ⟧-sound μ (ρ ⓜ κ)))
                   DRA.ⓣ-vert ⟦ eq-cell (mod-assoc κ) ⟧two-cell
                     DRA.≅ᵗᶜ
                   (from (DRA.ⓓ-assoc ⟦ μ ⟧mod ⟦ ρ ⟧mod ⟦ κ ⟧mod)
                   DRA.ⓣ-vert (from (⟦ⓜ⟧-sound μ ρ) DRA.ⓣ-hor DRA.id-cell))
                   DRA.ⓣ-vert from (⟦ⓜ⟧-sound (μ ⓜ ρ) κ)


--------------------------------------------------
-- The final mode theory record

record ModeTheory : Set₁ where
  no-eta-equality
  field
    mtm : MTMode
    mtμ : MTModality mtm
    mtc : MTComposition mtm mtμ
    mtc-laws : MTCompositionLaws mtm mtμ mtc
    mt2 : MTTwoCell mtm mtμ mtc
    mt2-laws : MTTwoCellLaws mtm mtμ mtc mtc-laws mt2

  open MTMode mtm public
  open MTModality mtμ public
  open MTComposition mtc public
  open MTCompositionLaws mtc-laws public
  open MTTwoCell mt2 public
  open MTTwoCellLaws mt2-laws public

  -- Some extra laws that we can prove about a mode theory
  ⟦eq-cell-symˡ⟧ : ∀ {m n} {μ ρ : Modality m n} (e : μ ≡ ρ) →
                   ⟦ eq-cell (sym e) ⟧two-cell DRA.ⓣ-vert ⟦ eq-cell e ⟧two-cell DRA.≅ᵗᶜ DRA.id-cell
  ⟦eq-cell-symˡ⟧ refl = transᵗᶜ (DRA.ⓣ-vert-congˡ ⟦id-cell⟧-sound) (transᵗᶜ (DRA.ⓣ-vert-congʳ ⟦id-cell⟧-sound) DRA.ⓣ-vert-unitˡ)

  ⟦eq-cell-symʳ⟧ : ∀ {m n} {μ ρ : Modality m n} (e : μ ≡ ρ) →
                   ⟦ eq-cell e ⟧two-cell DRA.ⓣ-vert ⟦ eq-cell (sym e) ⟧two-cell DRA.≅ᵗᶜ DRA.id-cell
  ⟦eq-cell-symʳ⟧ refl = transᵗᶜ (DRA.ⓣ-vert-congˡ ⟦id-cell⟧-sound) (transᵗᶜ (DRA.ⓣ-vert-congʳ ⟦id-cell⟧-sound) DRA.ⓣ-vert-unitˡ)

  ⟦eq-cell-trans⟧ : ∀ {m n} {μ ρ κ : Modality m n} (e : μ ≡ ρ) (e' : ρ ≡ κ) →
                    ⟦ eq-cell (trans e e') ⟧two-cell
                      DRA.≅ᵗᶜ
                    ⟦ eq-cell e' ⟧two-cell DRA.ⓣ-vert ⟦ eq-cell e ⟧two-cell
  ⟦eq-cell-trans⟧ refl e' = symᵗᶜ (transᵗᶜ (ⓣ-vert-congʳ ⟦id-cell⟧-sound) DRA.ⓣ-vert-unitʳ)


  ⟦ⓣ-hor-id-cell⟧ : ∀ {m n o} {μ : Modality n o} (ρ : Modality m n) →
                    ⟦ id-cell {μ = μ} ⓣ-hor id-cell {μ = ρ} ⟧two-cell
                      DRA.≅ᵗᶜ
                    ⟦ id-cell {μ = μ ⓜ ρ} ⟧two-cell
  ⟦ⓣ-hor-id-cell⟧ {μ = μ} ρ =
    begin
      ⟦ id-cell ⓣ-hor id-cell ⟧two-cell
    ≅⟨ DRA.transᵗᶜ (DRA.symᵗᶜ DRA.ⓣ-vert-assoc) (DRA.transᵗᶜ (ⓣ-vert-congˡ (isoˡ (⟦ⓜ⟧-sound μ ρ))) DRA.ⓣ-vert-unitˡ) ⟨
      to (⟦ⓜ⟧-sound μ ρ) DRA.ⓣ-vert (from (⟦ⓜ⟧-sound μ ρ) DRA.ⓣ-vert ⟦ (id-cell {μ = μ}) ⓣ-hor (id-cell {μ = ρ}) ⟧two-cell)
    ≅⟨ DRA.ⓣ-vert-congʳ (⟦ⓜ⟧-sound-natural id-cell id-cell) ⟩
      to (⟦ⓜ⟧-sound μ ρ) DRA.ⓣ-vert ((⟦ id-cell {μ = μ} ⟧two-cell DRA.ⓣ-hor ⟦ id-cell {μ = ρ} ⟧two-cell) DRA.ⓣ-vert from (⟦ⓜ⟧-sound μ ρ))
    ≅⟨ DRA.ⓣ-vert-congʳ (DRA.ⓣ-vert-congˡ (ⓣ-hor-cong ⟦id-cell⟧-sound ⟦id-cell⟧-sound)) ⟩
      to (⟦ⓜ⟧-sound μ ρ) DRA.ⓣ-vert ((DRA.id-cell DRA.ⓣ-hor DRA.id-cell) DRA.ⓣ-vert from (⟦ⓜ⟧-sound μ ρ))
    ≅⟨ DRA.ⓣ-vert-congʳ (DRA.transᵗᶜ (DRA.ⓣ-vert-congˡ DRA.ⓣ-hor-id) DRA.ⓣ-vert-unitˡ) ⟩
      to (⟦ⓜ⟧-sound μ ρ) DRA.ⓣ-vert from (⟦ⓜ⟧-sound μ ρ)
    ≅⟨ isoˡ (⟦ⓜ⟧-sound μ ρ) ⟩
      DRA.id-cell
    ≅⟨ ⟦id-cell⟧-sound ⟨
      ⟦ id-cell ⟧two-cell ∎
    where open DRA.≅ᵗᶜ-Reasoning

  ⟦eq-cell-whisker-left⟧ : ∀ {m n o} (μ : Modality n o) {ρ κ : Modality m n} (e : ρ ≡ κ) →
                           ⟦ eq-cell (cong (μ ⓜ_) e) ⟧two-cell
                             DRA.≅ᵗᶜ
                           ⟦ id-cell ⓣ-hor (eq-cell e) ⟧two-cell
  ⟦eq-cell-whisker-left⟧ μ {ρ} refl = DRA.symᵗᶜ (⟦ⓣ-hor-id-cell⟧ ρ)

  ⟦eq-cell-whisker-right⟧ : ∀ {m n o} {ρ κ : Modality n o} (e : ρ ≡ κ) (μ : Modality m n) →
                            ⟦ eq-cell (cong (_ⓜ μ) e) ⟧two-cell
                              DRA.≅ᵗᶜ
                            ⟦ eq-cell e ⓣ-hor (id-cell {μ = μ}) ⟧two-cell
  ⟦eq-cell-whisker-right⟧ refl μ = DRA.symᵗᶜ (⟦ⓣ-hor-id-cell⟧ μ)


  ⟦ⓜ⟧-sound-natural-to : ∀ {m n o} {μ μ' : Modality n o} {ρ ρ' : Modality m n}
                         (α : TwoCell μ μ') (β : TwoCell ρ ρ') →
                         ⟦ α ⓣ-hor β ⟧two-cell DRA.ⓣ-vert to (⟦ⓜ⟧-sound μ ρ)
                           DRA.≅ᵗᶜ
                         to (⟦ⓜ⟧-sound μ' ρ') DRA.ⓣ-vert (⟦ α ⟧two-cell DRA.ⓣ-hor ⟦ β ⟧two-cell)
  ⟦ⓜ⟧-sound-natural-to {μ = μ} {μ'} {ρ} {ρ'} α β =
    begin
      ⟦ α ⓣ-hor β ⟧two-cell DRA.ⓣ-vert to (⟦ⓜ⟧-sound μ ρ)
    ≅⟨ DRA.ⓣ-vert-congˡ (DRA.transᵗᶜ (DRA.symᵗᶜ DRA.ⓣ-vert-assoc) (DRA.transᵗᶜ (DRA.ⓣ-vert-congˡ (isoˡ (⟦ⓜ⟧-sound μ' ρ'))) DRA.ⓣ-vert-unitˡ)) ⟨
      (to (⟦ⓜ⟧-sound μ' ρ') DRA.ⓣ-vert (from (⟦ⓜ⟧-sound μ' ρ') DRA.ⓣ-vert ⟦ α ⓣ-hor β ⟧two-cell)) DRA.ⓣ-vert to (⟦ⓜ⟧-sound μ ρ)
    ≅⟨ DRA.ⓣ-vert-congˡ (DRA.ⓣ-vert-congʳ (⟦ⓜ⟧-sound-natural α β)) ⟩
      (to (⟦ⓜ⟧-sound μ' ρ') DRA.ⓣ-vert ((⟦ α ⟧two-cell DRA.ⓣ-hor ⟦ β ⟧two-cell) DRA.ⓣ-vert from (⟦ⓜ⟧-sound μ ρ))) DRA.ⓣ-vert to (⟦ⓜ⟧-sound μ ρ)
    ≅⟨ DRA.transᵗᶜ DRA.ⓣ-vert-assoc (DRA.ⓣ-vert-congʳ (DRA.transᵗᶜ (DRA.transᵗᶜ DRA.ⓣ-vert-assoc (DRA.ⓣ-vert-congʳ (isoʳ (⟦ⓜ⟧-sound μ ρ)))) DRA.ⓣ-vert-unitʳ)) ⟩
      to (⟦ⓜ⟧-sound μ' ρ') DRA.ⓣ-vert (⟦ α ⟧two-cell DRA.ⓣ-hor ⟦ β ⟧two-cell) ∎
    where open DRA.≅ᵗᶜ-Reasoning

  ⟦unitorˡ⟧ : ∀ {m n} {μ : Modality m n} →
              ⟦ eq-cell (mod-unitˡ {μ = μ}) ⟧two-cell
                DRA.≅ᵗᶜ
              from (DRA.𝟙-unitˡ ⟦ μ ⟧mod) DRA.ⓣ-vert from (⟦ⓜ⟧-sound 𝟙 μ)
  ⟦unitorˡ⟧ {μ = 𝟙} = DRA.transᵗᶜ ⟦id-cell⟧-sound (DRA.symᵗᶜ (record { key-subst-eq = M.id-subst-unitʳ _ }))
  ⟦unitorˡ⟧ {μ = ‵ μ} = DRA.transᵗᶜ ⟦id-cell⟧-sound (DRA.symᵗᶜ (isoʳ (𝟙-unitˡ _)))

  ⟦unitorˡ-sym⟧ : ∀ {m n} {μ : Modality m n} →
                  ⟦ eq-cell (sym (mod-unitˡ {μ = μ})) ⟧two-cell
                    DRA.≅ᵗᶜ
                  to (⟦ⓜ⟧-sound 𝟙 μ) DRA.ⓣ-vert to (DRA.𝟙-unitˡ ⟦ μ ⟧mod)
  ⟦unitorˡ-sym⟧ {μ = 𝟙} = DRA.transᵗᶜ ⟦id-cell⟧-sound (DRA.symᵗᶜ (record { key-subst-eq = M.id-subst-unitʳ _ }))
  ⟦unitorˡ-sym⟧ {μ = ‵ μ} = DRA.transᵗᶜ ⟦id-cell⟧-sound (DRA.symᵗᶜ (isoʳ (𝟙-unitˡ _)))

  -- Because 𝟙 is a strict right unit of ⓜ, the pseudofunctor law for
  -- the right unitor is actually trivial.
  ⟦unitorʳ⟧ : ∀ {m n} {μ : Modality m n} →
              ⟦ eq-cell (mod-unitʳ {μ = μ}) ⟧two-cell
                DRA.≅ᵗᶜ
              DRA.id-cell
  ⟦unitorʳ⟧ = ⟦id-cell⟧-sound

  ⟦associator-sym-key⟧ : ∀ {m n o p} {μ : Modality o p} {ρ : Modality n o} (κ : Modality m n) {Γ : M.Ctx ⟦ p ⟧mode} →
                         DRA.key-subst ⟦ eq-cell (sym (mod-assoc κ)) ⟧two-cell {Γ}
                         M.⊚ DRA.key-subst (from (⟦ⓜ⟧-sound (μ ⓜ ρ) κ))
                         M.⊚ DRA.lock-fmap ⟦ κ ⟧mod (DRA.key-subst (from (⟦ⓜ⟧-sound μ ρ)))
                           M.≅ˢ
                         DRA.key-subst (from (⟦ⓜ⟧-sound μ (ρ ⓜ κ)))
                         M.⊚ DRA.key-subst (from (⟦ⓜ⟧-sound ρ κ))
  ⟦associator-sym-key⟧ {μ = μ} {ρ} κ =
    begin
      key-subst ⟦ eq-cell (sym (mod-assoc κ)) ⟧two-cell
      M.⊚ key-subst (from (⟦ⓜ⟧-sound (μ ⓜ ρ) κ))
      M.⊚ lock-fmap ⟦ κ ⟧mod (key-subst (from (⟦ⓜ⟧-sound μ ρ)))
    ≅⟨ M.transˢ M.⊚-assoc (M.symˢ (M.⊚-congʳ (M.⊚-congʳ (M.transˢ (M.id-subst-unitʳ _) (M.id-subst-unitˡ _))))) ⟩
      key-subst ⟦ eq-cell (sym (mod-assoc κ)) ⟧two-cell M.⊚
      (key-subst (from (⟦ⓜ⟧-sound (μ ⓜ ρ) κ)) M.⊚
      (M.id-subst _ M.⊚
      DRA.lock-fmap ⟦ κ ⟧mod (key-subst (from (⟦ⓜ⟧-sound μ ρ))) M.⊚
      M.id-subst _))
    ≅⟨ M.⊚-congʳ (key-subst-eq (⟦associator⟧ κ)) ⟨
      key-subst ⟦ eq-cell (sym (mod-assoc κ)) ⟧two-cell M.⊚
      (key-subst ⟦ eq-cell (mod-assoc κ) ⟧two-cell M.⊚
      (key-subst (from (⟦ⓜ⟧-sound μ (ρ ⓜ κ))) M.⊚
      (key-subst (from (⟦ⓜ⟧-sound ρ κ)) M.⊚
      DRA.lock-fmap ⟦ κ ⟧mod (DRA.lock-fmap ⟦ ρ ⟧mod (M.id-subst _)))))
    ≅⟨ M.⊚-congʳ (M.⊚-congʳ (M.⊚-congʳ (M.transˢ (M.⊚-congʳ (M.transˢ (lock-fmap-cong ⟦ κ ⟧mod (lock-fmap-id ⟦ ρ ⟧mod)) (lock-fmap-id ⟦ κ ⟧mod))) (M.id-subst-unitʳ _)))) ⟩
      key-subst ⟦ eq-cell (sym (mod-assoc κ)) ⟧two-cell M.⊚
      (key-subst ⟦ eq-cell (mod-assoc κ) ⟧two-cell M.⊚
      (key-subst (from (⟦ⓜ⟧-sound μ (ρ ⓜ κ))) M.⊚
      key-subst (from (⟦ⓜ⟧-sound ρ κ))))
    ≅⟨ M.transˢ (M.symˢ M.⊚-assoc) (M.transˢ (M.⊚-congˡ (DRA.key-subst-eq (⟦eq-cell-symʳ⟧ (mod-assoc κ)))) (M.id-subst-unitˡ _)) ⟩
      key-subst (from (⟦ⓜ⟧-sound μ (ρ ⓜ κ)))
      M.⊚ key-subst (from (⟦ⓜ⟧-sound ρ κ)) ∎
    where open M.≅ˢ-Reasoning

  ⟦associator-key-to⟧ : ∀ {m n o p} {μ : Modality o p} {ρ : Modality n o} (κ : Modality m n) {Γ : M.Ctx ⟦ p ⟧mode} →
                        DRA.lock-fmap ⟦ κ ⟧mod (DRA.key-subst (to (⟦ⓜ⟧-sound μ ρ)))
                        M.⊚ DRA.key-subst (to (⟦ⓜ⟧-sound (μ ⓜ ρ) κ))
                        M.⊚ DRA.key-subst ⟦ eq-cell (mod-assoc κ) ⟧two-cell {Γ}
                          M.≅ˢ
                        DRA.key-subst (to (⟦ⓜ⟧-sound ρ κ))
                        M.⊚ DRA.key-subst (to (⟦ⓜ⟧-sound μ (ρ ⓜ κ)))
  ⟦associator-key-to⟧ {μ = μ} {ρ} κ =
    begin
      DRA.lock-fmap ⟦ κ ⟧mod (key-subst (to (⟦ⓜ⟧-sound μ ρ)))
      M.⊚ DRA.key-subst (to (⟦ⓜ⟧-sound (μ ⓜ ρ) κ))
      M.⊚ DRA.key-subst ⟦ eq-cell (mod-assoc κ) ⟧two-cell
    ≅⟨ M.transˢ M.⊚-assoc (M.transˢ (M.⊚-congʳ (M.transˢ (M.transˢ M.⊚-assoc (M.⊚-congʳ (M.symˢ M.⊚-assoc))) (
       M.transˢ (M.⊚-congʳ (M.⊚-congˡ (DRA.key-subst-eq (isoˡ (⟦ⓜ⟧-sound ρ κ))))) (
       M.transˢ (M.⊚-congʳ (M.id-subst-unitˡ _)) (DRA.key-subst-eq (isoˡ (⟦ⓜ⟧-sound μ (ρ ⓜ κ)))))))) (M.id-subst-unitʳ _)) ⟨
      DRA.lock-fmap ⟦ κ ⟧mod (key-subst (to (⟦ⓜ⟧-sound μ ρ)))
      M.⊚ DRA.key-subst (to (⟦ⓜ⟧-sound (μ ⓜ ρ) κ))
      M.⊚ DRA.key-subst ⟦ eq-cell (mod-assoc κ) ⟧two-cell
      M.⊚ (DRA.key-subst (from (⟦ⓜ⟧-sound μ (ρ ⓜ κ))) M.⊚ DRA.key-subst (from (⟦ⓜ⟧-sound ρ κ)))
      M.⊚ (DRA.key-subst (to (⟦ⓜ⟧-sound ρ κ)) M.⊚ DRA.key-subst (to (⟦ⓜ⟧-sound μ (ρ ⓜ κ))))
    ≅⟨ M.⊚-congˡ (M.⊚-congʳ (⟦associator-sym-key⟧ κ)) ⟨
      DRA.lock-fmap ⟦ κ ⟧mod (key-subst (to (⟦ⓜ⟧-sound μ ρ)))
      M.⊚ DRA.key-subst (to (⟦ⓜ⟧-sound (μ ⓜ ρ) κ))
      M.⊚ DRA.key-subst ⟦ eq-cell (mod-assoc κ) ⟧two-cell
      M.⊚ (DRA.key-subst ⟦ eq-cell (sym (mod-assoc κ)) ⟧two-cell
           M.⊚ DRA.key-subst (from (⟦ⓜ⟧-sound (μ ⓜ ρ) κ))
           M.⊚ DRA.lock-fmap ⟦ κ ⟧mod (DRA.key-subst (from (⟦ⓜ⟧-sound μ ρ))))
      M.⊚ (DRA.key-subst (to (⟦ⓜ⟧-sound ρ κ)) M.⊚ DRA.key-subst (to (⟦ⓜ⟧-sound μ (ρ ⓜ κ))))
    ≅⟨ M.transˢ (M.⊚-congˡ (
         M.transˢ (M.transˢ M.⊚-assoc (M.⊚-congʳ (M.transˢ (M.⊚-congʳ M.⊚-assoc) (M.transˢ (M.symˢ M.⊚-assoc)
                  (M.transˢ (M.⊚-congˡ (DRA.key-subst-eq (⟦eq-cell-symˡ⟧ (mod-assoc κ)))) (M.id-subst-unitˡ _))))))(
         M.transˢ (M.transˢ M.⊚-assoc (M.⊚-congʳ (M.transˢ (M.symˢ M.⊚-assoc) (
                  M.transˢ (M.⊚-congˡ (DRA.key-subst-eq (isoʳ (⟦ⓜ⟧-sound (μ ⓜ ρ) κ)))) (M.id-subst-unitˡ _))))) (
         M.ctx-fmap-inverse (DRA.ctx-functor ⟦ κ ⟧mod) (DRA.key-subst-eq (isoʳ (⟦ⓜ⟧-sound μ ρ))))))) (
       M.id-subst-unitˡ _) ⟩
      DRA.key-subst (to (⟦ⓜ⟧-sound ρ κ))
      M.⊚ DRA.key-subst (to (⟦ⓜ⟧-sound μ (ρ ⓜ κ))) ∎
    where open M.≅ˢ-Reasoning
