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

-- TODO mext

idm : {α : GameD ℓ} → MorphD α α
idm = MD id (λ _ → id) (λ _ _ → id)

compose : {α β γ : GameD ℓ} → MorphD α β → MorphD β γ → MorphD α γ
compose f g =
 MD (g .fw ∘ f .fw)
    (λ u → f .bw u ∘ g .bw (f. fw u))
    λ u y → g .is-better (f .fw u) y ∘ f .is-better u (g .bw (f .fw u) y)

-- TODO lemmas

{- Tensor product -}

one : GameD ℓ
one {ℓ} .strat     = Lift ℓ ⊤
one {ℓ} .costrat _ = Lift ℓ ⊤
one {ℓ} .win _ _   = el! (Lift ℓ ⊤)

tens : {X : 𝒰 ℓ} → (X → GameD ℓ) → GameD ℓ
tens A .strat     = ∀ x → A x .strat
tens A .costrat u = ∀ x → A x .costrat (u x)
tens A .win u y   = el! (∀ x → ⌞ A x. win (u x) (y x) ⌟)

tensm : {X : 𝒰 ℓ} {A B : X → GameD ℓ}
      → ((x : X) → MorphD (A x) (B x))
      → MorphD (tens A) (tens B)
tensm f .fw u            = λ x → f x .fw (u x)
tensm f .bw u y          = λ x → f x .bw (u x) (y x)
tensm f .is-better u y c = λ x → f x .is-better (u x) (y x) (c x)


{- Internal hom -}

hom : GameD ℓ → GameD ℓ → GameD ℓ
hom α β .strat          = (u : α .strat) → Σ[ v ꞉  β .strat ] (β .costrat v → α .costrat u)
hom α β .costrat vx     = Σ[ u ꞉  α .strat ] β .costrat (vx u .fst)
hom α β .win vx (u , y) = el! (⌞ α .win u (vx u .snd y) ⌟ → ⌞ β .win (vx u .fst) y ⌟)

homm : {A1 A2 B1 B2 : GameD ℓ} → MorphD A2 A1 → MorphD B1 B2 → MorphD (hom A1 B1) (hom A2 B2)
homm f g .fw        = λ u y →
                      let b2a2 = u (f .fw y) in
                      g .fw (b2a2 .fst) , f .bw y ∘ b2a2 .snd ∘ g .bw (b2a2 .fst)
homm f g .bw        = λ u y → (f .fw (y .fst)) , (g .bw (u (f .fw (y .fst)) .fst) (y .snd))
homm f g .is-better = λ u y a1w a2w →
                      g .is-better (u (f .fw (y .fst)) .fst) (y .snd)
                        (a1w (f .is-better (y .fst) (u (f .fw (y .fst)) .snd (g .bw (u (f .fw (y .fst)) .fst) (y .snd))) a2w))

{- Cartesian product -}

top : GameD ℓ
top {ℓ} .strat     = Lift ℓ ⊤
top {ℓ} .costrat _ = Lift ℓ ⊥
top     .win u v   = absurd (lower v)

prod : {X : 𝒰 ℓ} → (X → GameD ℓ) → GameD ℓ
prod     A .strat          = ∀ x → A x .strat
prod {X} A .costrat u      = Σ[ x ꞉ X ] A x .costrat (u x)
prod     A .win u (x , cx) = A x .win (u x) cx

prodm : {X : 𝒰 ℓ} {A B : X → GameD ℓ}
      → ((x : X) → MorphD (A x) (B x))
      → MorphD (prod A) (prod B)
prodm f .fw u                 = λ x → f x .fw (u x)
prodm f .bw u (x , cx)        = x , f x .bw (u x) cx
prodm f .is-better u (x , cx) = f x .is-better (u x) cx
