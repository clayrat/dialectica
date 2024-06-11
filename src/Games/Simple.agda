module Games.Simple where

open import Prelude

open import Meta.Record

open import Data.Unit
open import Data.Empty

{- Dialectica as games in normal form -}

private variable
  ℓ : Level

{- Dialectica category -}

{- Objects -}

{- We look at Dialectica objects as games in normal form.
    They define a set of strategies, a set of counter-strategies,
    and a criterion for winning strategy profiles. -}

record Game (ℓ : Level) : 𝒰 (ℓsuc ℓ) where
  constructor G
  field
    strat   : 𝒰 ℓ
    costrat : 𝒰 ℓ
    win     : strat → costrat → Prop ℓ

open Game

{- Winning strategies -}

wstrat : Game ℓ → 𝒰 ℓ
wstrat α = Σ[ u ꞉ α .strat ] ((x : α .costrat) → ⌞ α .win u x ⌟)

ws : {α : Game ℓ} → wstrat α → strat α
ws x = x .fst

{- Morphisms -}

record Morph {ℓ : Level} (α β : Game ℓ) : 𝒰 ℓ where
  constructor M
  field
    fw        : strat α → strat β
    bw        : strat α → costrat β → costrat α
    is-better : (u : strat α) (y : costrat β)
              → ⌞ α .win u (bw u y) ⌟ → ⌞ β .win (fw u) y ⌟

unquoteDecl morph-iso = declare-record-iso morph-iso (quote Morph)

open Morph

{- Extensional equality -}

mext : {α β : Game ℓ} {f g : Morph α β}
     → ((u : α .strat)                 → f .fw u   ＝ g .fw u  )
     → ((u : α .strat) (y : costrat β) → f .bw u y ＝ g .bw u y)
     → f ＝ g
mext {α} {β} {f} {g} fwe bwe =
  apˢ {A = (Σ[ fw ꞉ (α .strat → β .strat) ]
            Σ[ bw ꞉ (α .strat → β .costrat → α .costrat) ]
            ((u : α .strat) (y : β .costrat) → ⌞ α .win u (bw u y) ⌟ → ⌞ β .win (fw u) y ⌟))}
      {B = Morph α β}
      (≅→≃ morph-iso ⁻¹ $_)
      (Σ-path (fun-ext fwe) $
       Σ-path (transport-refl (f .bw) ∙ fun-ext (fun-ext ∘ bwe)) $
       fun-ext λ u → fun-ext λ y → fun-ext λ c → hlevel 1 _ (g .is-better u y c))

{- Compositional structure -}

idm : {α : Game ℓ} → Morph α α
idm = M id (λ _ → id) (λ _ _ → id)

compose : {α β γ : Game ℓ} → Morph α β → Morph β γ → Morph α γ
compose f g =
 M (g .fw ∘ f .fw)
   (λ u → f .bw u ∘ g .bw (f. fw u))
   λ u y → g .is-better (f .fw u) y ∘ f .is-better u (g .bw (f .fw u) y)

compose-id-l : {α β : Game ℓ} → (f : Morph α β)
             → compose idm f ＝ f
compose-id-l f = mext (λ _ → refl) λ _ _ → refl

compose-id-r : {α β : Game ℓ} → (f : Morph α β)
             → compose f idm ＝ f
compose-id-r f = mext (λ _ → refl) λ _ _ → refl

compose-assoc : {α β γ δ : Game ℓ} → (f : Morph α β) → (g : Morph β γ) → (h : Morph γ δ)
              → compose f (compose g h) ＝ compose (compose f g) h
compose-assoc f g h = mext (λ _ → refl) λ _ _ → refl

{- Tensor product -}

one : Game ℓ
one {ℓ} .strat   = Lift ℓ ⊤
one {ℓ} .costrat = Lift ℓ ⊤
one {ℓ} .win _ _ = el! (Lift ℓ ⊤)

tens : {X : 𝒰 ℓ} → (X → Game ℓ) → Game ℓ
tens A .strat   = ∀ x → A x .strat
tens A .costrat = ∀ x → A x .costrat
tens A .win u y = el! (∀ x → ⌞ A x. win (u x) (y x) ⌟) -- TODO construct vs Pi/Universal ?

tensm : {X : 𝒰 ℓ} {A B : X → Game ℓ}
      → ((x : X) → Morph (A x) (B x))
      → Morph (tens A) (tens B)
tensm f .fw u            = λ x → f x .fw (u x)
tensm f .bw u y          = λ x → f x .bw (u x) (y x)
tensm f .is-better u y c = λ x → f x .is-better (u x) (y x) (c x)

{- Internal hom -}

hom : Game ℓ → Game ℓ → Game ℓ
hom α β .strat          = α .strat → β .strat × (β .costrat → α .costrat)
hom α β .costrat        = α .strat × β .costrat
hom α β .win vx (u , y) = el! (⌞ α .win u (vx u .snd y) ⌟ → ⌞ β .win (vx u .fst) y ⌟)

homm : {A1 A2 B1 B2 : Game ℓ} (f : Morph A2 A1) (g : Morph B1 B2) → Morph (hom A1 B1) (hom A2 B2)
homm f g .fw        = λ u y →
                      let b2a2 = u (f .fw y) in
                      g .fw (b2a2 .fst) , f .bw y ∘ b2a2 .snd ∘ g .bw (b2a2 .fst)
homm f g .bw        = λ u y → (f .fw (y .fst)) , (g .bw (u (f .fw (y .fst)) .fst) (y .snd))
homm f g .is-better = λ u y a1w a2w →
                      g .is-better (u (f .fw (y .fst)) .fst) (y .snd)
                        (a1w (f .is-better (y .fst) (u (f .fw (y .fst)) .snd (g .bw (u (f .fw (y .fst)) .fst) (y .snd))) a2w))

{- Cartesian product -}

top : Game ℓ
top {ℓ} .strat   = Lift ℓ ⊤
top {ℓ} .costrat = Lift ℓ ⊥
top     .win u v = absurd (lower v)

prod : {X : 𝒰 ℓ} → (X → Game ℓ) → Game ℓ
prod     A .strat          = ∀ x → A x .strat
prod {X} A .costrat        = Σ[ x ꞉ X ] A x .costrat 
prod     A .win u (x , cx) = A x .win (u x) cx

prodm : {X : 𝒰 ℓ} {A B : X → Game ℓ}
      → ((x : X) → Morph (A x) (B x))
      → Morph (prod A) (prod B)
prodm f .fw u                 = λ x → f x .fw (u x)
prodm f .bw u (x , cx)        = x , f x .bw (u x) cx
prodm f .is-better u (x , cx) = f x .is-better (u x) cx
