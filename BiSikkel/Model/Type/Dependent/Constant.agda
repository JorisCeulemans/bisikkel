--------------------------------------------------
-- Some properties of terms of constant presheaves, expressed using
-- the semantic identity type
--------------------------------------------------

open import BiSikkel.Model.BaseCategory

module BiSikkel.Model.Type.Dependent.Constant {C : BaseCategory} where

open import Data.Product renaming (_,_ to [_,_])
open import Relation.Binary.PropositionalEquality using (refl)

open import BiSikkel.Preliminaries
open import BiSikkel.Model.CwF-Structure
open import BiSikkel.Model.Type.Constant
open import BiSikkel.Model.Type.Function
open import BiSikkel.Model.Type.Dependent.Function renaming (lam to dlam) hiding (to-pshfun-eq)
open import BiSikkel.Model.Type.Dependent.Identity

private variable
  Γ : Ctx C


true≠false : Tm Γ (Id true' false' ⇛ Empty')
true≠false {Γ = Γ} = lam _ body
  where
    body : Tm (Γ ,, Id true' false') (Empty' [ π ])
    body ⟨ x , () ⟩'
    naturality body {γx = ()}

suc-inj : Tm Γ (Pi Nat' (Pi Nat' (Id (suc' (ξcl const-closed [ const-closed ∣ π ]cl)) (suc' (ξcl const-closed)) ⇛
                   Id (ξcl const-closed [ const-closed ∣ π ]cl) (ξcl const-closed))))
suc-inj {Γ = Γ} = dlam _ (dlam _ body)
  where
    body : Tm (Γ ,, Nat' ,, Nat') (Id (suc' (ξcl const-closed [ const-closed ∣ π ]cl)) (suc' (ξcl const-closed)) ⇛
                                      Id (ξcl const-closed [ const-closed ∣ π ]cl) (ξcl const-closed))
    body ⟨ x , [ [ γ , m ] , .m ] ⟩' $⟨ ρ , refl ⟩ refl = refl
    naturality (body ⟨ x , [ [ γ , m ] , n ] ⟩') = uip _ _
    naturality body f eγ = to-pshfun-eq (λ _ _ _ → uip _ _)

zero≠sucn : Tm Γ (Pi Nat' (Id zero' (suc' (ξcl const-closed)) ⇛ Empty'))
zero≠sucn {Γ = Γ} = dlam _ body
  where
    body : Tm (Γ ,, Nat') (Id zero' (suc' (ξcl const-closed)) ⇛ Empty')
    body ⟨ x , γ ⟩' $⟨ ρ , eγ ⟩ ()
    naturality (body ⟨ x , γ ⟩') {t = ()}
    naturality body f eγ = to-pshfun-eq (λ _ _ ())
