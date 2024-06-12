module Games.Dep where

open import Prelude

open import Meta.Record

open import Data.Unit
open import Data.Empty

private variable
  ℓ : Level

{- Sum-and-product completion of 2 (⊥ -> ⊤) -}

record GameD (ℓ : Level) : 𝒰 (ℓsuc ℓ) where
  constructor GD
  field
    strat   : 𝒰 ℓ
    costrat : strat → 𝒰 ℓ
    win     : (σ : strat) → costrat σ → Prop ℓ

open GameD

record MorphD {ℓ : Level} (α β : GameD ℓ) : 𝒰 ℓ where
  constructor MD
  field
    fw        : strat α → strat β
    bw        : (σ : strat α) → costrat β (fw σ) → costrat α σ
    is-better : (u : strat α) (y : costrat β (fw u))
              → ⌞ α .win u (bw u y) ⌟ → ⌞ β .win (fw u) y ⌟

open MorphD

unquoteDecl morphd-iso = declare-record-iso morphd-iso (quote MorphD)

idm : {α : GameD ℓ} → MorphD α α
idm = MD id (λ _ → id) (λ _ _ → id)

compose : {α β γ : GameD ℓ} → MorphD α β → MorphD β γ → MorphD α γ
compose f g =
 MD (g .fw ∘ f .fw)
    (λ u → f .bw u ∘ g .bw (f. fw u))
    λ u y → g .is-better (f .fw u) y ∘ f .is-better u (g .bw (f .fw u) y)
