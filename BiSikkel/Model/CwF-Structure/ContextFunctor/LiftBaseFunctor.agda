--------------------------------------------------
-- Lifting a functor
--
-- In this file we show that a functor from base categories C to D
--   can be lifted to a "strict" CwF endomorphism from Psh(D) to Psh(C).
--------------------------------------------------

module BiSikkel.Model.CwF-Structure.ContextFunctor.LiftBaseFunctor where

open import Data.Product renaming (_,_ to [_,_])
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_]; naturality)

open import BiSikkel.Model.BaseCategory
open import BiSikkel.Model.CwF-Structure.Context
open import BiSikkel.Model.CwF-Structure.Type
open import BiSikkel.Model.CwF-Structure.Term
open import BiSikkel.Model.CwF-Structure.ContextFunctor
open import BiSikkel.Model.CwF-Structure.ContextEquivalence
open import BiSikkel.Model.CwF-Structure.ContextExtension

open BaseCategory
open BaseFunctor

private variable
  C D E : BaseCategory

module _ (F : BaseFunctor C D) where

  lift-ctx : Ctx D → Ctx C
  lift-ctx Γ ⟨ c ⟩ = Γ ⟨ ob F c ⟩
  lift-ctx Γ ⟪ f ⟫ γ = Γ ⟪ hom F f ⟫ γ
  ctx-id (lift-ctx Γ) {γ = γ} =
    begin
      Γ ⟪ hom F (hom-id C) ⟫ γ
    ≡⟨ cong (Γ ⟪_⟫ γ) (id-law F) ⟩
      Γ ⟪ hom-id D ⟫ γ
    ≡⟨ ctx-id Γ ⟩
      γ ∎
    where open ≡-Reasoning
  ctx-comp (lift-ctx Γ) {f = f} {g} {γ} =
    begin
      Γ ⟪ hom F (g ∙[ C ] f) ⟫ γ
    ≡⟨ cong (Γ ⟪_⟫ γ) (comp-law F) ⟩
      Γ ⟪ hom F g ∙[ D ] hom F f ⟫ γ
    ≡⟨ ctx-comp Γ ⟩
      Γ ⟪ hom F f ⟫ (Γ ⟪ hom F g ⟫ γ) ∎
    where open ≡-Reasoning

  lift-subst : {Δ : Ctx D} {Γ : Ctx D} (σ : Δ ⇒ Γ) → lift-ctx Δ ⇒ lift-ctx Γ
  func (lift-subst σ) {c} = func σ {ob F c}
  naturality (lift-subst σ) {f = f} = naturality σ {f = hom F f}

  lift-subst-cong : {Γ Δ : Ctx D} {σ τ : Γ ⇒ Δ} → σ ≅ˢ τ → lift-subst σ ≅ˢ lift-subst τ
  eq (lift-subst-cong ε) γ = eq ε γ

  lift-subst-id : {Γ : Ctx D} → lift-subst (id-subst Γ) ≅ˢ id-subst (lift-ctx Γ)
  eq lift-subst-id _ = refl

  lift-subst-⊚ : {Δ : Ctx D} {Γ : Ctx D} {Θ : Ctx D} (τ : Γ ⇒ Θ) (σ : Δ ⇒ Γ) →
                 lift-subst (τ ⊚ σ) ≅ˢ lift-subst τ ⊚ lift-subst σ
  eq (lift-subst-⊚ τ σ) _ = refl

  lift-functor : CtxFunctor D C
  ctx-op lift-functor = lift-ctx
  IsCtxFunctor.ctx-map (is-functor lift-functor) = lift-subst
  IsCtxFunctor.ctx-map-cong (is-functor lift-functor) = lift-subst-cong
  IsCtxFunctor.ctx-map-id (is-functor lift-functor) = lift-subst-id
  IsCtxFunctor.ctx-map-⊚ (is-functor lift-functor) = lift-subst-⊚


-- We can show that lifting preserves the identity functor and functor
-- composition.

lift-id-functor : lift-functor (id-base-functor {C = C}) ≅ᶜᶠ id-ctx-functor
func (transf-op (from lift-id-functor) Γ) γ = γ
naturality (transf-op (from lift-id-functor) Γ) = refl
eq (naturality (from lift-id-functor) σ) _ = refl
func (transf-op (to lift-id-functor) Γ) γ = γ
naturality (transf-op (to lift-id-functor) Γ) = refl
eq (naturality (to lift-id-functor) σ) _ = refl
eq (transf-op-eq (isoˡ lift-id-functor)) _ = refl
eq (transf-op-eq (isoʳ lift-id-functor)) _ = refl

lift-compose-functor : {C D E : BaseCategory} {G : BaseFunctor D E} {F : BaseFunctor C D} →
                       lift-functor (base-functor-comp G F) ≅ᶜᶠ (lift-functor F ⓕ lift-functor G)
func (transf-op (from lift-compose-functor) Γ) γ = γ
naturality (transf-op (from lift-compose-functor) Γ) = refl
eq (naturality (from lift-compose-functor) σ) _ = refl
func (transf-op (to lift-compose-functor) Γ) γ = γ
naturality (transf-op (to lift-compose-functor) Γ) = refl
eq (naturality (to lift-compose-functor) σ) _ = refl
eq (transf-op-eq (isoˡ lift-compose-functor)) _ = refl
eq (transf-op-eq (isoʳ lift-compose-functor)) _ = refl


-- Record expressing that a context functor arises as a lifted base functor
record IsLiftedFunctor (Φ : CtxFunctor D C) : Set₁ where
  constructor is-lifted-functor
  field
    F : BaseFunctor C D
    is-lifted : lift-functor F ≅ᶜᶠ Φ

open IsLiftedFunctor renaming (F to base-functor) public


is-lifted-lift : {F : BaseFunctor C D} → IsLiftedFunctor (lift-functor F)
is-lifted-lift {F = F} = is-lifted-functor F reflᶜᶠ

is-lifted-id : IsLiftedFunctor (id-ctx-functor {C})
is-lifted-id = is-lifted-functor id-base-functor lift-id-functor

_ⓕ-lifted_ : {Ψ : CtxFunctor D E} → IsLiftedFunctor Ψ →
             {Φ : CtxFunctor C D} → IsLiftedFunctor Φ →
             IsLiftedFunctor (Ψ ⓕ Φ)
is-lifted-functor F eF ⓕ-lifted is-lifted-functor G eG =
  is-lifted-functor (base-functor-comp G F) (transᶜᶠ lift-compose-functor (transᶜᶠ (ⓕ-congˡ eF) (ⓕ-congʳ eG)))


-- A lifted context functor can be extended to a CwF morphism, but
-- this is not used anywhere.
module CwF-Morphism (F : BaseFunctor C D) where

  lift-ty : {Γ : Ctx D} → Ty Γ → Ty (lift-ctx F Γ)
  lift-ty T ⟨ c , γ ⟩ = T ⟨ ob F c , γ ⟩
  lift-ty T ⟪ f , eγ ⟫ t = T ⟪ hom F f , eγ ⟫ t
  ty-cong (lift-ty T) e = ty-cong T (cong (hom F) e)
  ty-id (lift-ty T) {t = t} =
    begin
      T ⟪ hom F (hom-id C) , _ ⟫ t
    ≡⟨ ty-cong T (id-law F) ⟩
      T ⟪ hom-id D , _ ⟫ t
    ≡⟨ ty-id T ⟩
      t ∎
   where open ≡-Reasoning
  ty-comp (lift-ty T) {f = f} {g} {eγ-zy = eγ-zy} {eγ-yx} {t} =
    begin
      T ⟪ hom F (g ∙[ C ] f) , _ ⟫ t
    ≡⟨ ty-cong T (comp-law F) ⟩
      T ⟪ hom F g ∙[ D ] hom F f , _ ⟫ t
    ≡⟨ ty-comp T ⟩
      T ⟪ hom F f , eγ-yx ⟫ (T ⟪ hom F g , eγ-zy ⟫ t) ∎
    where open ≡-Reasoning

  lift-ty-natural : {Δ : Ctx D} {Γ : Ctx D} (σ : Δ ⇒ Γ) (T : Ty Γ) →
                    lift-ty (T [ σ ]) ≅ᵗʸ lift-ty T [ lift-subst F σ ]
  func (from (lift-ty-natural σ T)) = id
  naturality (from (lift-ty-natural σ T)) = refl
  func (to (lift-ty-natural σ T)) = id
  naturality (to (lift-ty-natural σ T)) = refl
  eq (isoˡ (lift-ty-natural σ T)) _ = refl
  eq (isoʳ (lift-ty-natural σ T)) _ = refl

  lift-tm : {Γ : Ctx D} {T : Ty Γ} → Tm Γ T → Tm (lift-ctx F Γ) (lift-ty T)
  lift-tm t ⟨ c , γ ⟩' = t ⟨ ob F c , γ ⟩'
  naturality (lift-tm t) f eγ = naturality t (hom F f) eγ

  lift-tm-natural : {Δ : Ctx D} {Γ : Ctx D} (σ : Δ ⇒ Γ) {T : Ty Γ} (t : Tm Γ T) →
                    lift-tm (t [ σ ]') ≅ᵗᵐ ι[ lift-ty-natural σ T ] ((lift-tm t) [ lift-subst F σ ]')
  eq (lift-tm-natural σ t) δ = refl

  lift-◇ : lift-ctx F ◇ ≅ᶜ ◇
  from lift-◇ = MkSubst id refl
  to lift-◇ = MkSubst id refl
  eq (isoˡ lift-◇) _ = refl
  eq (isoʳ lift-◇) _ = refl

  lift-ctx-ext : (Γ : Ctx D) (T : Ty Γ) → lift-ctx F (Γ ,, T) ≅ᶜ lift-ctx F Γ ,, lift-ty T
  from (lift-ctx-ext Γ T) = MkSubst id refl
  to (lift-ctx-ext Γ T) = MkSubst id refl
  eq (isoˡ (lift-ctx-ext Γ T)) _ = refl
  eq (isoʳ (lift-ctx-ext Γ T)) _ = refl

  lift-π : (Γ : Ctx D) (T : Ty Γ) → lift-subst F π ⊚ to (lift-ctx-ext Γ T) ≅ˢ π
  eq (lift-π Γ T) _ = refl

  lift-ξ : (Γ : Ctx D) (T : Ty Γ) → lift-tm ξ [ to (lift-ctx-ext Γ T) ]' ≅ᵗᵐ
                                       ι[ ty-subst-cong-ty (to (lift-ctx-ext Γ T)) (lift-ty-natural π T) ] (
                                       ι[ ty-subst-comp (lift-ty T) (lift-subst F π) (to (lift-ctx-ext Γ T)) ] (
                                       ι[ ty-subst-cong-subst (lift-π Γ T) (lift-ty T) ] ξ))
  eq (lift-ξ Γ T) [ γ , t ] = sym (
    begin
      T ⟪ hom F (hom-id C) , _ ⟫ t
    ≡⟨ ty-cong T (id-law F) ⟩
      T ⟪ hom-id D , _ ⟫ t
    ≡⟨ ty-id T ⟩
      t ∎)
    where open ≡-Reasoning
