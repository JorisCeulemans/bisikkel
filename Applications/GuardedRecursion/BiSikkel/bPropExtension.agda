-- No new bProp connectives are necessary for the guarded recursion
-- instance, so we let the type of codes `bPropExtCode` be the empty
-- type.

{-# OPTIONS --guardedness #-}

module Applications.GuardedRecursion.BiSikkel.bPropExtension where

open import Data.Empty

open import Applications.GuardedRecursion.BiSikkel.MSTT
open import Applications.GuardedRecursion.BiSikkel.TypeExtension
open import Applications.GuardedRecursion.BiSikkel.TermExtension

open import BiSikkel.Parameter.bPropExtension
open import BiSikkel.Parameter.bPropExtensionSemantics


guarded-bp-ext : bPropExt guarded-mt guarded-ty-ext guarded-tm-ext
bPropExt.bPropExtCode guarded-bp-ext _ = ⊥
bPropExt._≟bp-code_ guarded-bp-ext () ()
bPropExt.bp-code-tmarg-infos guarded-bp-ext ()
bPropExt.bp-code-bparg-infos guarded-bp-ext ()


guarded-bp-ext-sem : bPropExtSem guarded-mt guarded-ty-ext _ guarded-bp-ext
bPropExtSem.⟦_⟧bp-code guarded-bp-ext-sem ()
