module Games.Int where

open import Prelude

open import Meta.Record

open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Sum

open import Games.Simple

open Game

private variable
  ℓ : Level

{- Intuitionistic games -}

{- Game shapes -}

data Shape (ℓ : Level) : 𝒰 (ℓsuc ℓ) where
 snil : Shape ℓ
 scons : {X : 𝒰 ℓ} → (X → Shape ℓ) → Shape ℓ

mutual
  stratI : Shape ℓ → 𝒰 ℓ
  stratI {ℓ}  snil         = Lift ℓ ⊤
  stratI     (scons {X} k) = Σ[ x ꞉ X ] costratI (k x)

  costratI : Shape ℓ → 𝒰 ℓ 
  costratI {ℓ}  snil     = Lift ℓ ⊤
  costratI     (scons {X} k) = (x : X) → stratI (k x)

mutual
  eval : (s : Shape ℓ) → stratI s → costratI s → Prop ℓ
  eval {ℓ}  snil      _      _ = el! (Lift ℓ ⊤)
  eval     (scons k) (x , u) y = coeval (k x) u (y x)

  coeval : (s : Shape ℓ) → costratI s → stratI s → Prop ℓ
  coeval {ℓ}  snil     _ _       = el! (Lift ℓ ⊥)
  coeval     (scons k) y (x , u) = eval (k x) (y x) u

{- Games -}

data GameI (ℓ : Level) : 𝒰 (ℓsuc ℓ) where
  doneI  : Prop ℓ → GameI ℓ
  roundI : {X : 𝒰 ℓ} {Y : X → 𝒰 ℓ} → ((x : X) → Y x → GameI ℓ) → GameI ℓ

{- Mapping games to Dialectica -}

{- We compute the sets of strategies, costrategies, and an
   evaluation function which plays one against the other. -}

data BranchI {X : 𝒰 ℓ} {Y : X → 𝒰 ℓ} (A : (x : X) → Y x → 𝒰 ℓ) : 𝒰 ℓ where
  br : (x : X) → ((y : Y x) → A x y) → BranchI A

gstrat : GameI ℓ → 𝒰 ℓ
gstrat {ℓ} (doneI w)  = Lift ℓ ⊤
gstrat     (roundI k) = BranchI λ x y → gstrat (k x y)

gcostrat : GameI ℓ → 𝒰 ℓ
gcostrat {ℓ} (doneI w)          = Lift ℓ ⊤
gcostrat     (roundI {X} {Y} k) = (x : X) → Σ[ y ꞉ Y x ] gcostrat (k x y)

outcome : (g : GameI ℓ) → gstrat g → gcostrat g → Prop ℓ
outcome (doneI w)  _         _ = w
outcome (roundI k) (br x σk) π with π x
... | y , πk = outcome (k x y) (σk y) πk

dialofI : GameI ℓ → Game ℓ 
dialofI g .strat   = gstrat g
dialofI g .costrat = gcostrat g
dialofI g .win     = outcome g

{- Dialectica to games -}

ofdialI : Game ℓ → GameI ℓ
ofdialI {ℓ} g = roundI {X = g .strat} {Y = λ _ → g .costrat}
                       λ u x → doneI (g .win u x)

{- Homomorphism of games -}
