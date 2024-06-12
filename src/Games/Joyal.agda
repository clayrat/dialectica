module Games.Joyal where

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

{- Jan's adaptation of Joyal's games -}

data GameJ (ℓ : Level) : 𝒰 (ℓsuc ℓ) where
  done  : Prop ℓ → GameJ ℓ
  sigma : {X : 𝒰 ℓ} → (X → GameJ ℓ) → GameJ ℓ
  pi    : {X : 𝒰 ℓ} → (X → GameJ ℓ) → GameJ ℓ

{- Dialectica objects can be read as simple games involving
    a σ-move u ∈ U followed by a π-move x ∈ X. -}

ofdial : Game ℓ → GameJ ℓ
ofdial A = sigma λ u → pi λ x → done (A .win u x)

{- Strategies and costrategies -}

stratJ : GameJ ℓ → 𝒰 ℓ
stratJ {ℓ} (done _)      = Lift ℓ ⊤
stratJ     (sigma {X} k) = Σ[ x ꞉ X ] stratJ (k x)
stratJ     (pi {X} k)    = (x : X) → stratJ (k x)

costratJ : GameJ ℓ → 𝒰 ℓ
costratJ {ℓ} (done _)      = Lift ℓ ⊤
costratJ     (sigma {X} k) = (x : X) → costratJ (k x)
costratJ     (pi {X} k)    = Σ[ x ꞉ X ] costratJ (k x)

winJ : {g : GameJ ℓ} → stratJ g → costratJ g → Prop ℓ
winJ {g = done p}  _       _       = p
winJ {g = sigma k} (x , σ) π       = winJ {g = k x} σ (π x)
winJ {g = pi k}    σ       (x , π) = winJ {g = k x} (σ x) π

{- The set of strategies and costrategies together with the payoff
    function can be used to define a Dialectica object. -}

dialof : GameJ ℓ → Game ℓ
dialof g .strat   = stratJ g
dialof g .costrat = costratJ g
dialof g .win     = winJ {g = g}

{- We can also define winning strategies in the same way. -}

wstratJ : GameJ ℓ → 𝒰 ℓ
wstratJ (done w)      = ⌞ w ⌟
wstratJ (sigma {X} k) = Σ[ x ꞉ X ] wstratJ (k x)
wstratJ (pi {X} k)    = (x : X) → wstratJ (k x)

wsJ : {g : GameJ ℓ} → wstratJ g → stratJ g
wsJ {g = done w}  _       = lift tt
wsJ {g = sigma k} (x , u) = x , wsJ u
wsJ {g = pi k}    u       = wsJ ∘ u

wstrat-winning : (g : GameJ ℓ) (u : wstratJ g) (c : costratJ g) → ⌞ winJ (wsJ u) c ⌟
wstrat-winning (done w)  u       _       = u
wstrat-winning (sigma k) (x , u) c       = wstrat-winning (k x) u (c x)
wstrat-winning (pi k)    u       (x , c) = wstrat-winning (k x) (u x) c

{- Negation -}

{- The complement of a game exchanges the roles of the two players. -}

oppJ : GameJ ℓ → GameJ ℓ
oppJ (done w)  = done (el! (¬ ⌞ w ⌟))
oppJ (sigma k) = pi (oppJ ∘ k)
oppJ (pi k)    = sigma (oppJ ∘ k)

{- Binary product -}

prodJ : GameJ ℓ → GameJ ℓ → GameJ ℓ
prodJ {ℓ} g h = pi {X = Lift ℓ Bool} λ where
  (lift false) → g
  (lift true)  → h

{- Tensor product -}

{- The tensor product of games lets them be played side by side.
   The player σ takes priority and move when either game is of the
   form [Σi . Gi], but it must win both games to win overall.

   In this principle this can be defined in a straightforward way
   using a simple case analysis. Below I have elided the symmetric
   cases, and each line defines one layer of choice only, even when
   shown as ∑ + ∑.

       - ∑i·Gi ⊗ ∑j·Hj := ∑i·(Gi ⊗ ∑j·Hj) + ∑j·(∑i·Gi ⊗ Hj)
       - ∑i·Gi ⊗ ∏j·Hj := ∑i·(Gi ⊗ ∏j·Hj)
       - ∑i·Gi ⊗ win   := ∑i·(Gi ⊗ win)
       - ∑i·Gi ⊗ lose  := ∑i·(Gi ⊗ lose)
       - ∏i·Gi ⊗ ∏j·Hj := ∏i·(Gi ⊗ ∏j·Hj) × ∏j·(∏i·Gi ⊗ Hj)
       - ∏i·Gi ⊗ win   := ∏i·(Gi ⊗ win)
       - ∏i·Gi ⊗ lose  := ∏i·(Gi ⊗ lose)
       -   win ⊗ win   := win
       -   win ⊗ lose  := lose
       -  lose ⊗ lose  := lose

   While straightforward in principle, it is somewhat tricky
   to define in a way which makes termination evident to Coq,
   because only one of the two games will have a move "peeled off"
   at any given step. To make this work we use a sort of continuation
   passing style where two fixpoints communicate with each other
   while peeling off exactly one move at a time.

   Unfortunately, under this approach, the symmetry of the underlying
   process is not reflected by the structure of the definition.
   In the definition of [G ⊗ H], we will use separate cases depending
   on the structure of [G]. -}

{- Tensoring with base games -}

{- If [G] is at its conclusion, we finish playing [H] largely as-is,
   but adjust its payoff based on the outcome of [G]. -}

tens-done : Prop ℓ → GameJ ℓ → GameJ ℓ
tens-done gw (done hw) = done (el! (⌞ gw ⌟ × ⌞ hw ⌟))
tens-done gw (sigma k) = sigma (tens-done gw ∘ k)
tens-done gw (pi k)    = pi (tens-done gw ∘ k)

{- Tensoring with σ-games -}

{- When [G] is of the form [∑i·Gi], we must "mix in" any σ-moves
    that are available in [H] as well. The following definition helps. -}

sigma2 : {X Y : 𝒰 ℓ} → (X → GameJ ℓ) → (Y → GameJ ℓ) → GameJ ℓ
sigma2 {X} {Y} gk hk = sigma {X = X ⊎ Y} [ gk , hk ]ᵤ

{- If σ chooses a move in [H], we continue with the corresponding
   subgame. When σ chooses (or is forced) to play in G, we invoke the
   corresponding "Gi continuation" and pass the residual [H]. -}

tens-sigma : {X : 𝒰 ℓ} → (X → GameJ ℓ → GameJ ℓ) → GameJ ℓ → GameJ ℓ
tens-sigma gk h@(sigma hk) = sigma2 (λ x → gk x h) λ x → tens-sigma gk (hk x)
tens-sigma gk h            = sigma λ x → gk x h

{- Tensoring with π-games -}

{- When [G] is of the form [∏i·Gi], we must first exhaust all
   possible σ-moves in [H]. Control transfers to π only once we
   encounter a π-move in [H] as well, at which point we must mix in
   the available π-moves from [G]. -}

pi2 : {X Y : 𝒰 ℓ} → (X → GameJ ℓ) → (Y → GameJ ℓ) → GameJ ℓ
pi2 {X} {Y} gk hk = pi {X = X ⊎ Y} [ gk , hk ]ᵤ

{- Once again, when π chooses to move in [G], we invoke the
   corresponding continuation and pass to it the residual [H]. -}

tens-pi : {X : 𝒰 ℓ} → (X → GameJ ℓ → GameJ ℓ) → GameJ ℓ → GameJ ℓ
tens-pi gk h@(done _)   = pi (λ x → gk x h)
tens-pi gk   (sigma hk) = sigma λ x → tens-pi gk (hk x)
tens-pi gk h@(pi hk)    = pi2 (λ x → gk x h) λ x → tens-pi gk (hk x)

{- Putting everything together -}

{- With this, we are ready to do the case analysis and recursion
    on the game [G]. Termination checking works because instead of
    [tens_sigma] and [tens_pi] invoking [tens] on the subgames of [G]
    directly, they do it through a continuation which is defined within
    the scope of [tens] itself. -}

tensJ : GameJ ℓ → GameJ ℓ → GameJ ℓ
tensJ (done gw)  h = tens-done gw h
tensJ (sigma gk) h = tens-sigma (tensJ ∘ gk) h
tensJ (pi gk)    h = tens-pi (tensJ ∘ gk) h

{- Internal hom -}

{- As expected, we can now describe the game used to construct
   morphisms using a combination of tensors and negation. -}

homJ : GameJ ℓ → GameJ ℓ → GameJ ℓ
homJ g h = oppJ $ tensJ g $ oppJ h

{- A morphism from [G] to [H] is then a winning strategy for [G ⊸ H]. -}

MorphJ : GameJ ℓ → GameJ ℓ → 𝒰 ℓ
MorphJ g h = wstratJ (homJ g h)

{- The happens-before game -}

bef : GameJ ℓ → GameJ ℓ → GameJ ℓ
bef (done _)   h = h
bef (sigma gk) h = sigma λ x → bef (gk x) h
bef (pi gk)    h = pi λ x → bef (gk x) h
