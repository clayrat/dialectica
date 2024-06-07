{-
Chuangjie Xu, January 2016

We explore the Dialectica interpretation of first order logic into
Martin-Löf type theory (in Agda notation).

The idea of the Dialectica interpretation is that each formula A is
transformed to a classically equivalent one of the form ∃x.∀y.|A|
where with ∣A∣ quantifier-free.

In this study, the language to interpret is a subset of Agda equipped
with a first order logic.  We adopt the inference rules of the system
IL from Oliva[1] to define the interpreted logic.  The Dialectica
interpretation is slightly adapted for dependent types as in Bauer[2].

References.

[1] Paulo Oliva, Unifying Functional Interpretation.  Notre Dame
    Journal of Formal Logic 47 (2):263-290, 2006.

[2] Andrej Bauer, The Dialectica interpretation in Coq.  Available at
    http://math.andrej.com/2011/01/03/the-dialectica-interpertation-in-coq/

\begin{code}
-}
module Dialectica where

open import Prelude
open import Data.Empty
open import Data.Nat
open import Data.Fin
open import Data.List
open import Data.List.Operations.Properties

len-mid : {ℓ : Level} {A : 𝒰 ℓ} {z : A} {xs ys : List A}
        → length (xs ++ z ∷ ys) ＝ suc (length (xs ++ ys))
len-mid {z} {xs} {ys} = ++-length xs (z ∷ ys)
                      ∙ +-suc-r (length xs) (length ys)
                      ∙ ap suc ((++-length xs ys) ⁻¹)        

Index : {ℓ : Level} {A : 𝒰 ℓ} → List A → 𝒰
Index ρ = Fin (length ρ)

_₍_₎ : {ℓ : Level} {A : 𝒰 ℓ} → (ρ : List A) → Index ρ → A
(a ∷ ρ) ₍ fzero ₎ = a
(a ∷ ρ) ₍ fsuc f ₎ = ρ ₍ f ₎

{-
\end{code}

The term language is the full hierarchy of finite types in which every
type is inhabited.

\begin{code}
-}
infixr 20 _⊗_
infixr 10 _⇾_

data Ty : 𝒰 where
 Ⓝ : Ty
 _⊗_ : Ty → Ty → Ty
 _⇾_ : Ty → Ty → Ty

⟦_⟧ₜ : Ty → 𝒰
⟦ Ⓝ ⟧ₜ = ℕ
⟦ σ ⊗ τ ⟧ₜ = ⟦ σ ⟧ₜ × ⟦ τ ⟧ₜ
⟦ σ ⇾ τ ⟧ₜ = ⟦ σ ⟧ₜ → ⟦ τ ⟧ₜ

⟦inhabitant⟧ₜ : {σ : Ty} → ⟦ σ ⟧ₜ
⟦inhabitant⟧ₜ {σ = Ⓝ} = 0
⟦inhabitant⟧ₜ {σ ⊗ τ} = ⟦inhabitant⟧ₜ , ⟦inhabitant⟧ₜ
⟦inhabitant⟧ₜ {σ ⇾ τ} = λ _ → ⟦inhabitant⟧ₜ

{-
\end{code}

We inductively define a first order logic on the full type hierarchy
consisting of types Prp of propositions and Prf of proofs.

Notice that predicates are represented as (Agda) functions into Prp.
This forces us to adapt the original Dialectica interpretation by
introducing certain type dependencies.

\begin{code}
-}

infix 50 _==ₚ_
infix 40 _∧ₚ_
infix 30 _⇒ₚ_

data Prp : 𝒰 where
 _==ₚ_ : {σ : Ty} → ⟦ σ ⟧ₜ → ⟦ σ ⟧ₜ → Prp
 _∧ₚ_ : Prp → Prp → Prp
 _⇒ₚ_ : Prp → Prp → Prp
 ∀ₚ : {σ : Ty} → (⟦ σ ⟧ₜ → Prp) → Prp
 ∃ₚ : {σ : Ty} → (⟦ σ ⟧ₜ → Prp) → Prp

{-
\end{code}

An element of Prf Γ A represents a proof of A under the assumption Γ
where an assumption is simply a list of propositions.

Each constructor represents an inference rule. For example,

      Γ ⊢ A         Δ ⊢ B
    ----------------------- ∧-intro
         Γ , Δ ⊢ A ∧ B

is represented by the constructor

 ∧-intro : {Γ Δ : Asmpt} {A B : Prp}
         → Prf Γ A → Prf Δ B → Prf (Γ ₊₊ Δ) (A ∧ B)

Notice that the constructors J and ind should have more general
assumptions.  We work with the ones in empty assumption for simplicity.

\begin{code}
-}

Asmpt : 𝒰
Asmpt = List Prp

data Prf : Asmpt → Prp → 𝒰 where
 reflᵣ : {σ : Ty} {a : ⟦ σ ⟧ₜ}
      → Prf [] (a ==ₚ a)
 Jᵣ    : {σ : Ty} (φ : ⟦ σ ⟧ₜ → ⟦ σ ⟧ₜ → Prp)
      → ((a : ⟦ σ ⟧ₜ) → Prf [](φ a a))
      → {a b : ⟦ σ ⟧ₜ} → Prf [](a ==ₚ b) → Prf [] (φ a b)
 idᵣ   : {A : Prp}
      → Prf (A ∷ []) A
 wknᵣ  : {Γ : Asmpt} {A B : Prp}
      → Prf Γ B → Prf (A ∷ Γ) B
 cutᵣ  : {Γ Δ : Asmpt} {A B : Prp}
      → Prf (A ∷ Γ) B → Prf Δ A → Prf (Γ ++ Δ) B
 swapᵣ : (Γ : Asmpt) {Δ : Asmpt} {A B C : Prp}
      → Prf (Γ ++ B ∷ A ∷ Δ) C → Prf (Γ ++ A ∷ B ∷ Δ) C
 ∧-introᵣ : {Γ Δ : Asmpt} {A B : Prp}
         → Prf Γ A → Prf Δ B → Prf (Γ ++ Δ) (A ∧ₚ B)
 ∧-elim₀ : {Γ : Asmpt} {A B : Prp}
         → Prf Γ (A ∧ₚ B) → Prf Γ A
 ∧ₚ-elim₁ : {Γ : Asmpt} {A B : Prp}
         → Prf Γ (A ∧ₚ B) → Prf Γ B
 ⇒-introᵣ : {Γ : Asmpt} {A B : Prp}
         → Prf (A ∷ Γ) B → Prf Γ (A ⇒ₚ B)
 ⇒-elimᵣ  : {Γ : Asmpt} {A B : Prp}
         → Prf Γ (A ⇒ₚ B) → Prf (A ∷ Γ) B
 ∀-introᵣ : {Γ : Asmpt} {σ : Ty} {φ : ⟦ σ ⟧ₜ → Prp}
         → ((x : ⟦ σ ⟧ₜ) → Prf Γ (φ x)) → Prf Γ (∀ₚ φ)
 ∀-elimᵣ  : {Γ : Asmpt} {σ : Ty} {φ : ⟦ σ ⟧ₜ → Prp}
         → Prf Γ (∀ₚ φ) → (a : ⟦ σ ⟧ₜ) → Prf Γ (φ a)
 ∃-introᵣ : {Γ : Asmpt} {σ : Ty} {φ : ⟦ σ ⟧ₜ → Prp}
         → (a : ⟦ σ ⟧ₜ) → Prf Γ (φ a) → Prf Γ (∃ₚ φ)
 ∃-elimᵣ  : {Γ : Asmpt} {σ : Ty} {φ : ⟦ σ ⟧ₜ → Prp} {A : Prp}
         → ((x : ⟦ σ ⟧ₜ) → Prf Γ (φ x ⇒ₚ A)) → Prf Γ ((∃ₚ φ) ⇒ₚ A)
 indᵣ : (φ : ℕ → Prp)
     → Prf [] (φ 0) → Prf [] (∀ₚ (λ n → φ n ⇒ₚ φ (suc n))) → Prf [] (∀ₚ φ)

{-
\end{code}

Our goal is to transform each proposition A into a type Σx.Πy.∣A∣.  To
determine the types of x and y, we assign to each proposition A types
d⁺(A) and d⁻(A), where d⁺(A) is intended to be the type of a realizer
to be extracted from a proof of A and d⁻(A) is the type of a challenge
for the claim that this term realizes A.

The types of realizers and challenges are inhabited.  We make a
canonical choice of an inhabitant of each type.

\begin{code}
-}

mutual
  d⁺ : Prp → 𝒰
  d⁺ (u ==ₚ v) = ⊤
  d⁺ (A ∧ₚ B) = (d⁺ A) × (d⁺ B)
  d⁺ (A ⇒ₚ B) = (d⁺ A → d⁺ B) × (d⁺ A → d⁻ B → d⁻ A)
  d⁺ (∀ₚ {σ} φ) = (x : ⟦ σ ⟧ₜ) → d⁺ (φ x)
  d⁺ (∃ₚ {σ} φ) = Σ[ x ꞉ ⟦ σ ⟧ₜ ] d⁺ (φ x)

  d⁻ : Prp → 𝒰
  d⁻ (u ==ₚ v) = ⊤
  d⁻ (A ∧ₚ B) = (d⁻ A) × (d⁻ B)
  d⁻ (A ⇒ₚ B) = (d⁺ A) × (d⁻ B)
  d⁻ (∀ₚ {σ} φ) = Σ[ x ꞉ ⟦ σ ⟧ₜ ] d⁻ (φ x)
  d⁻ (∃ₚ {σ} φ) = (x : ⟦ σ ⟧ₜ) → d⁺ (φ x) → d⁻ (φ x)

mutual 
  inhabitant⁺ : (A : Prp) → d⁺ A
  inhabitant⁺ (u ==ₚ v) = tt
  inhabitant⁺ (A ∧ₚ B) = inhabitant⁺ A , inhabitant⁺ B
  inhabitant⁺ (A ⇒ₚ B) = (λ _ → inhabitant⁺ B) , (λ _ _ → inhabitant⁻ A)
  inhabitant⁺ (∀ₚ φ) = λ x → inhabitant⁺ (φ x)
  inhabitant⁺ (∃ₚ φ) = ⟦inhabitant⟧ₜ , inhabitant⁺ (φ ⟦inhabitant⟧ₜ)

  inhabitant⁻ : (A : Prp) → d⁻ A
  inhabitant⁻ (u ==ₚ v) = tt
  inhabitant⁻ (A ∧ₚ B) = inhabitant⁻ A , inhabitant⁻ B
  inhabitant⁻ (A ⇒ₚ B) = inhabitant⁺ A , inhabitant⁻ B
  inhabitant⁻ (∀ₚ φ) = ⟦inhabitant⟧ₜ , inhabitant⁻ (φ ⟦inhabitant⟧ₜ)
  inhabitant⁻ (∃ₚ φ) = λ x _ → inhabitant⁻ (φ x)

dd⁺ : Asmpt → 𝒰
dd⁺ Γ = (i : Index Γ) → d⁺ (Γ ₍ i ₎)

dd⁻ : Asmpt → 𝒰
dd⁻ Γ = (i : Index Γ) → d⁻ (Γ ₍ i ₎)

iA⁺ : (Γ : Asmpt) → dd⁺ Γ
iA⁺ Γ i = inhabitant⁺ (Γ ₍ i ₎)

iA⁻ : (Γ : Asmpt) → dd⁻ Γ
iA⁻ Γ i = inhabitant⁻ (Γ ₍ i ₎)

{-
\end{code}

The dialectica interpretation (of propositions and assumptions)

\begin{code}
-}

∣_∣ : (φ : Prp) → d⁺ φ → d⁻ φ → 𝒰
∣ u ==ₚ v ∣ _         _         = u ＝ v
∣ A ∧ₚ B ∣ (t₀ , t₁) (y₀ , y₁) = ∣ A ∣ t₀ y₀ × ∣ B ∣ t₁ y₁
∣ A ⇒ₚ B ∣  (t₀ , t₁) (y₀ , y₁) = ∣ A ∣ y₀ (t₁ y₀ y₁) → ∣ B ∣ (t₀ y₀) y₁
∣ ∀ₚ φ ∣    t         (a , y)   = ∣ φ a ∣ (t a) y
∣ ∃ₚ φ ∣    (a , t)   y         = ∣ φ a ∣ t (y a t)

∥_∥ : (Γ : Asmpt) → dd⁺ Γ → dd⁻ Γ → 𝒰
∥ [] ∥    _  _  = ⊤
∥ X ∷ Γ ∥ xs rs = ∥ Γ ∥ (xs ∘ fsuc) (rs ∘ fsuc) × ∣ X ∣ (xs fzero) (rs fzero)

{-
\end{code}

The soundness theorem says that each proof of a proposition A in the
interpreted logic is transformed to an element of type Σt.Πy.∣A∣(t,y)
in Agda.  Since we work more generally with proofs in assumptions, the
theorem is generalized to the following.

\begin{code}
-}

Prfᴬ : 𝒰 → 𝒰 → 𝒰
Prfᴬ Γ A = Γ → A

{-
\end{code}

Thm[soundness] : {Γ : Asmpt} {A : Prp} → Prf Γ A
               → (xs : dd⁺ Γ) → Σ \(t : d⁺ A) → (y : d⁻ A) → Σ \(rs : dd⁻ Γ) → Prfᴬ (∥ Γ ∥ xs rs) (∣ A ∣ t y)

The proof of Thm[soundness] is placed in the end of this file.  It's
done by induction on Prf.  We prove the cases (corresponding to the
constructors of Prf) one by one.

For this, we need the following auxiliary functions and lemmas of assumptions.

\begin{code}
-}

pr₀ᴸ⁺ : (Γ : Asmpt) {Δ : Asmpt} → dd⁺ (Γ ++ Δ) → dd⁺ Γ
pr₀ᴸ⁺ (_ ∷ _) xs  fzero   = xs fzero
pr₀ᴸ⁺ (_ ∷ Γ) xs (fsuc f) = pr₀ᴸ⁺ Γ (xs ∘ fsuc) f

pr₁ᴸ⁺ : (Γ : Asmpt) {Δ : Asmpt} → dd⁺ (Γ ++ Δ) → dd⁺ Δ
pr₁ᴸ⁺ []      xs = xs
pr₁ᴸ⁺ (x ∷ Γ) xs = pr₁ᴸ⁺ Γ (xs ∘ fsuc)

pairᴸ⁺ : (Γ : Asmpt) {Δ : Asmpt} → dd⁺ Γ → dd⁺ Δ → dd⁺ (Γ ++ Δ)
pairᴸ⁺ []      rs₀ rs₁          = rs₁
pairᴸ⁺ (_ ∷ _) rs₀ rs₁  fzero   = rs₀ fzero
pairᴸ⁺ (_ ∷ Γ) rs₀ rs₁ (fsuc f) = pairᴸ⁺ Γ (rs₀ ∘ fsuc) rs₁ f

pr₀ᴸ⁻ : (Γ : Asmpt) {Δ : Asmpt} → dd⁻ (Γ ++ Δ) → dd⁻ Γ
pr₀ᴸ⁻ (x ∷ Γ) xs  fzero   = xs fzero
pr₀ᴸ⁻ (x ∷ Γ) xs (fsuc f) = pr₀ᴸ⁻ Γ (xs ∘ fsuc) f

pr₁ᴸ⁻ : (Γ : Asmpt) {Δ : Asmpt} → dd⁻ (Γ ++ Δ) → dd⁻ Δ
pr₁ᴸ⁻ [] xs = xs
pr₁ᴸ⁻ (x ∷ Γ) xs = pr₁ᴸ⁻ Γ (xs ∘ fsuc)

pairᴸ⁻ : (Γ : Asmpt) {Δ : Asmpt} → dd⁻ Γ → dd⁻ Δ → dd⁻ (Γ ++ Δ)
pairᴸ⁻ []      rs₀ rs₁          = rs₁
pairᴸ⁻ (_ ∷ _) rs₀ rs₁  fzero   = rs₀ fzero
pairᴸ⁻ (_ ∷ Γ) rs₀ rs₁ (fsuc f) = pairᴸ⁻ Γ (rs₀ ∘ fsuc) rs₁ f

∥++∥→× : (Γ : Asmpt) {Δ : Asmpt} (xs : dd⁺ (Γ ++ Δ)) (rs₀ : dd⁻ Γ) (rs₁ : dd⁻ Δ)
      → ∥ Γ ++ Δ ∥ xs (pairᴸ⁻ Γ rs₀ rs₁) → ∥ Γ ∥ (pr₀ᴸ⁺ Γ xs) rs₀ × ∥ Δ ∥ (pr₁ᴸ⁺ Γ xs) rs₁
∥++∥→× []      xs rs₀ rs₁  ρ      = tt , ρ
∥++∥→× (_ ∷ Γ) xs rs₀ rs₁ (ρ , x) =
  let IH = ∥++∥→× Γ (xs ∘ fsuc) (rs₀ ∘ fsuc) rs₁ ρ in
  (IH .fst , x) , IH .snd
 
×→∥++∥ : (Γ : Asmpt) {Δ : Asmpt} (xs : dd⁺ (Γ ++ Δ)) (rs : dd⁻ (Γ ++ Δ))
      → ∥ Γ ∥ (pr₀ᴸ⁺ Γ xs) (pr₀ᴸ⁻ Γ rs) × ∥ Δ ∥ (pr₁ᴸ⁺ Γ xs) (pr₁ᴸ⁻ Γ rs) → ∥ Γ ++ Δ ∥ xs rs
×→∥++∥ []      xs rs (_ , ρ)       = ρ
×→∥++∥ (_ ∷ Γ) xs rs ((γ , x) , δ) = (×→∥++∥ Γ (xs ∘ fsuc) (rs ∘ fsuc) (γ , δ)) , x

swap⁺ : (Γ : Asmpt) {Δ : Asmpt} {A B : Prp}
      → dd⁺ (Γ ++ B ∷ A ∷ Δ) → dd⁺ (Γ ++ A ∷ B ∷ Δ)
swap⁺ []      xs    fzero          = xs (fsuc fzero)
swap⁺ []      xs   (fsuc fzero)    = xs fzero
swap⁺ []      xs f@(fsuc (fsuc _)) = xs f
swap⁺ (_ ∷ Γ) xs    fzero          = xs fzero
swap⁺ (_ ∷ Γ) xs   (fsuc f)        = swap⁺ Γ (xs ∘ fsuc) f

swap⁻ : (Γ : Asmpt) {Δ : Asmpt} {A B : Prp}
      → dd⁻ (Γ ++ B ∷ A ∷ Δ) → dd⁻ (Γ ++ A ∷ B ∷ Δ)
swap⁻ []      xs    fzero          = xs (fsuc fzero)
swap⁻ []      xs   (fsuc fzero)    = xs fzero
swap⁻ []      xs f@(fsuc (fsuc x)) = xs f
swap⁻ (_ ∷ Γ) xs    fzero          = xs fzero
swap⁻ (_ ∷ Γ) xs   (fsuc f)        = swap⁻ Γ (xs ∘ fsuc) f

∥swap∥→× : (Γ : Asmpt) {Δ : Asmpt} {A B : Prp}
         → (xs : dd⁺ (Γ ++ A ∷ B ∷ Δ)) (rs' : dd⁻ (Γ ++ B ∷ A ∷ Δ))
         → ∥ Γ ++ A ∷ B ∷ Δ ∥ xs (swap⁻ Γ rs')
         → ∥ Γ ∥ (pr₀ᴸ⁺ Γ xs) (pr₀ᴸ⁻ Γ rs') ×
           ∣ B ∣ (pr₁ᴸ⁺ Γ (swap⁺ Γ xs) fzero) (pr₁ᴸ⁻ Γ rs' fzero) ×
           ∣ A ∣ (pr₁ᴸ⁺ Γ (swap⁺ Γ xs) (fsuc fzero)) (pr₁ᴸ⁻ Γ rs' (fsuc fzero)) ×
           ∥ Δ ∥ (pr₁ᴸ⁺ Γ xs ∘ fsuc ∘ fsuc) (pr₁ᴸ⁻ Γ rs' ∘ fsuc ∘ fsuc)
∥swap∥→× []      xs rs' ((δ , β) , α) = tt , β , α , δ
∥swap∥→× (_ ∷ Γ) xs rs' (ρ , x) =
  let IH = ∥swap∥→× Γ (xs ∘ fsuc) (rs' ∘ fsuc) ρ in
  (IH .fst , x) , IH .snd

{-
\end{code}

The cases of reflexivity and the J-eliminator

\begin{code}
-}

case-refl : {σ : Ty} {a : ⟦ σ ⟧ₜ}
          → Σ[ t ꞉ d⁺ (a ==ₚ a) ] ((y : d⁻ (a ==ₚ a)) → Σ[ _ ꞉ dd⁻ [] ] Prfᴬ ⊤ (∣ a ==ₚ a ∣ t y))
case-refl = tt , λ _ → (λ ()) , λ _ → refl

case-J : {σ : Ty} (φ : ⟦ σ ⟧ₜ → ⟦ σ ⟧ₜ → Prp)
       → ((a : ⟦ σ ⟧ₜ) → (_ : dd⁺ []) → Σ[ t ꞉ d⁺ (φ a a) ] ((y : d⁻ (φ a a)) → Σ[ _ ꞉ dd⁻ [] ] Prfᴬ ⊤ (∣ φ a a ∣ t y)))
       → {a b : ⟦ σ ⟧ₜ} → ((_ : dd⁺ []) → Σ[ t ꞉ d⁺ (a ==ₚ b) ] ((y : d⁻ (a ==ₚ b)) → Σ[ _ ꞉ dd⁻ [] ] Prfᴬ ⊤ (∣ a ==ₚ b ∣ t y)))
       → (_ : dd⁺ []) → Σ[ t ꞉ d⁺ (φ a b) ] ((y : d⁻ (φ a b)) → Σ[ _ ꞉ dd⁻ [] ] Prfᴬ ⊤ (∣ φ a b ∣ t y))
case-J {σ} φ IH₀ {a} {b} IH₁ =
  subst Q p (IH₀ a)
  where
  p : a ＝ b
  p = IH₁ (λ ()) .snd tt .snd tt
  Q : ⟦ σ ⟧ₜ → 𝒰
  Q x = (_ : dd⁺ []) → Σ[ t ꞉ d⁺ (φ a x) ] ((y : d⁻ (φ a x)) → Σ[ _ ꞉ dd⁻ [] ] Prfᴬ ⊤ (∣ φ a x ∣ t y))

{-
\end{code}

The cases of basic rules in sequent calculi

\begin{code}
-}

{-
case-id : (A : Prp)
        → (xs : dd⁺ (ε ₊ A)) → Σ \(t : d⁺ A) → (y : d⁻ A) → Σ \(rs : dd⁻ (ε ₊ A)) → Prfᴬ (∥ ε ₊ A ∥ xs rs) (∣ A ∣ t y)
case-id A xs = t , goal
 where
  t :  d⁺ A
  t = xs zero
  frs : d⁻ A → dd⁻ (ε ₊ A)
  frs y zero = y
  frs y (succ ())
  goal : (y : d⁻ A) → Σ \(rs : dd⁻ (ε ₊ A)) → Prfᴬ (∥ ε ₊ A ∥ xs rs) (∣ A ∣ t y)
  goal y = frs y , pr₁

case-wkn : {Γ : Asmpt} (A B : Prp)
         → ((xs : dd⁺ Γ) → Σ \(t : d⁺ B) → (y : d⁻ B) → Σ \(rs : dd⁻ Γ) → Prfᴬ (∥ Γ ∥ xs rs) (∣ B ∣ t y))
         → (xs : dd⁺ (Γ ₊ A)) → Σ \(t : d⁺ B) → (y : d⁻ B) → Σ \(rs : dd⁻ (Γ ₊ A)) → Prfᴬ (∥ Γ ₊ A ∥ xs rs) (∣ B ∣ t y)
case-wkn {Γ} A B IH xs = t , goal
 where
  t : d⁺ B
  t = pr₀ (IH (xs ∘ succ))
  goal : (y : d⁻ B) → Σ \(rs : dd⁻ (Γ ₊ A)) → Prfᴬ (∥ Γ ₊ A ∥ xs rs) (∣ B ∣ t y)
  goal y = rs , claim
   where
    rs : dd⁻ (Γ ₊ A)
    rs zero = inhabitant⁻ A
    rs (succ i) = pr₀ (pr₁ (IH (xs ∘ succ)) y) i
    claim : Prfᴬ (∥ Γ ₊ A ∥ xs rs) (∣ B ∣ t y)
    claim (γ , _) = pr₁ (pr₁ (IH (xs ∘ succ)) y) γ

case-cut : {Γ Δ : Asmpt} (A B : Prp)
         → ((xs : dd⁺ (Γ ₊ A)) → Σ \(t : d⁺ B) → (y : d⁻ B) → Σ \(rs : dd⁻ (Γ ₊ A)) → Prfᴬ (∥ Γ ₊ A ∥ xs rs) (∣ B ∣ t y))
         → ((xs : dd⁺ Δ) → Σ \(t : d⁺ A) → (y : d⁻ A) → Σ \(rs : dd⁻ Δ) → Prfᴬ (∥ Δ ∥ xs rs) (∣ A ∣ t y))
         → (xs : dd⁺ (Γ ++ Δ)) → Σ \(t : d⁺ B) → (y : d⁻ B) → Σ \(rs : dd⁻ (Γ ++ Δ)) → Prfᴬ (∥ Γ ++ Δ ∥ xs rs) (∣ B ∣ t y)
case-cut {Γ} {Δ} A B IH₀ IH₁ xs = tb , goal
 where
  xs₁ : dd⁺ Δ
  xs₁ = pr₁ᴸ⁺ Δ xs
  ta : d⁺ A
  ta = pr₀ (IH₁ xs₁)
  xs₀' : dd⁺ Γ
  xs₀' = pr₀ᴸ⁺ Δ xs
  xs₀ : dd⁺ (Γ ₊ A)
  xs₀ zero = ta
  xs₀ (succ i) = xs₀' i
  tb : d⁺ B
  tb = pr₀ (IH₀ xs₀)
  goal : (yb : d⁻ B) → Σ \(rs : dd⁻ (Γ ++ Δ)) → Prfᴬ (∥ Γ ++ Δ ∥ xs rs) (∣ B ∣ tb yb)
  goal yb = rs , claim₃
   where
    rs₀ : dd⁻ (Γ ₊ A)
    rs₀ = pr₀ (pr₁ (IH₀ xs₀) yb)
    rs₀' : dd⁻ Γ
    rs₀' = rs₀ ∘ succ
    ya : d⁻ A
    ya = rs₀ zero
    rs₁ : dd⁻ Δ
    rs₁ = pr₀ (pr₁ (IH₁ xs₁) ya)
    rs : dd⁻ (Γ ++ Δ)
    rs = pairᴸ⁻ Δ rs₀' rs₁
    claim₀ : Prfᴬ (∥ Γ ₊ A ∥ xs₀ rs₀) (∣ B ∣ tb yb)
    claim₀ = pr₁ (pr₁ (IH₀ xs₀) yb)
    claim₁ : Prfᴬ (∥ Δ ∥ xs₁ rs₁) (∣ A ∣ ta ya)
    claim₁ = pr₁ (pr₁ (IH₁ xs₁) ya)
    claim₂ : Prfᴬ (∥ Γ ∥ xs₀' rs₀' × ∥ Δ ∥ xs₁ rs₁) (∣ B ∣ tb yb)
    claim₂ (γ , δ) = claim₀ (γ , claim₁ δ)
    claim₃ : Prfᴬ (∥ Γ ++ Δ ∥ xs rs) (∣ B ∣ tb yb)
    claim₃ ρ = claim₂ (∥++∥→× Δ xs rs₀' rs₁ ρ)

case-swap : (Γ Δ : Asmpt) (A B C : Prp)
          → ((xs : dd⁺ (Γ ₊ A ₊ B ++ Δ)) → Σ \(t : d⁺ C) → (y : d⁻ C) → Σ \(rs : dd⁻ (Γ ₊ A ₊ B ++ Δ)) → Prfᴬ (∥ Γ ₊ A ₊ B ++ Δ ∥ xs rs) (∣ C ∣ t y))
          → (xs : dd⁺ (Γ ₊ B ₊ A ++ Δ)) → Σ \(t : d⁺ C) → (y : d⁻ C) → Σ \(rs : dd⁻ (Γ ₊ B ₊ A ++ Δ)) → Prfᴬ (∥ Γ ₊ B ₊ A ++ Δ ∥ xs rs) (∣ C ∣ t y)
case-swap Γ Δ A B C IH xs = t , goal
 where
  xs' : dd⁺ (Γ ₊ A ₊ B ++ Δ)
  xs' = swap⁺ Δ xs
  t : d⁺ C
  t = pr₀ (IH xs')
  goal : (y : d⁻ C) → Σ \(rs : dd⁻ (Γ ₊ B ₊ A ++ Δ)) → Prfᴬ (∥ Γ ₊ B ₊ A ++ Δ ∥ xs rs) (∣ C ∣ t y)
  goal y = rs , claim₃
   where
    rs' : dd⁻ (Γ ₊ A ₊ B ++ Δ)
    rs' = pr₀ (pr₁ (IH xs') y)
    rs : dd⁻ (Γ ₊ B ₊ A ++ Δ)
    rs = swap⁻ Δ rs'
    xs'₀ : dd⁺ (Γ ₊ A ₊ B) 
    xs'₀ = pr₀ᴸ⁺ Δ xs'
    tb : d⁺ B
    tb = xs'₀ zero
    ta : d⁺ A
    ta = xs'₀ (succ zero)
    xs₀ : dd⁺ Γ
    xs₀ = xs'₀ ∘ succ ∘ succ
    xs₁ : dd⁺ Δ
    xs₁ = pr₁ᴸ⁺ Δ xs'
    rs'₀ : dd⁻ (Γ ₊ A ₊ B)
    rs'₀ = pr₀ᴸ⁻ Δ rs'
    yb : d⁻ B
    yb = rs'₀ zero
    ya : d⁻ A
    ya = rs'₀ (succ zero)
    rs₀ : dd⁻ Γ
    rs₀ = rs'₀ ∘ succ ∘ succ
    rs₁ : dd⁻ Δ
    rs₁ = pr₁ᴸ⁻ Δ rs'
    claim₀ : Prfᴬ (∥ Γ ₊ A ₊ B ++ Δ ∥ xs' rs') (∣ C ∣ t y)
    claim₀ = pr₁ (pr₁ (IH xs') y)
    claim₁ : Prfᴬ (((∥ Γ ∥ xs₀ rs₀ × ∣ A ∣ ta ya) × ∣ B ∣ tb yb) × ∥ Δ ∥ xs₁ rs₁) (∣ C ∣ t y)
    claim₁ ρ = claim₀ (×→∥++∥ Δ xs' rs' ρ)
    claim₂ : Prfᴬ (((∥ Γ ∥ xs₀ rs₀ × ∣ B ∣ tb yb) × ∣ A ∣ ta ya) × ∥ Δ ∥ xs₁ rs₁) (∣ C ∣ t y)
    claim₂ (((γ , b) , a) , δ) = claim₁ (((γ , a) , b) , δ)
    claim₃ : Prfᴬ (∥ Γ ₊ B ₊ A ++ Δ ∥ xs rs) (∣ C ∣ t y)
    claim₃ ρ = claim₂ (∥swap∥→× Δ xs rs' ρ)
-}

{-
\end{code}

The cases of inference rules of propositional logic

\begin{code}
-}

{-
case-∧ₚ-intro : {Γ Δ : Asmpt} (A B : Prp)
             → ((xs : dd⁺ Γ) → Σ \(t : d⁺ A) → (y : d⁻ A) → Σ \(rs : dd⁻ Γ) → Prfᴬ (∥ Γ ∥ xs rs) (∣ A ∣ t y))
             → ((xs : dd⁺ Δ) → Σ \(t : d⁺ B) → (y : d⁻ B) → Σ \(rs : dd⁻ Δ) → Prfᴬ (∥ Δ ∥ xs rs) (∣ B ∣ t y))
             → (xs : dd⁺ (Γ ++ Δ)) → Σ \(t : d⁺ (A ∧ₚ B)) → (y : d⁻ (A ∧ₚ B)) → Σ \(rs : dd⁻ (Γ ++ Δ)) → Prfᴬ (∥ Γ ++ Δ ∥ xs rs) (∣ A ∧ₚ B ∣ t y)
case-∧ₚ-intro {Γ} {Δ} A B IH₀ IH₁ xs = t , goal
 where
  xs₀ : dd⁺ Γ
  xs₀ = pr₀ᴸ⁺ Δ xs
  t₀ : d⁺ A
  t₀ = pr₀ (IH₀ xs₀)
  xs₁ : dd⁺ Δ
  xs₁ = pr₁ᴸ⁺ Δ xs
  t₁ : d⁺ B
  t₁ = pr₀ (IH₁ xs₁)
  t : d⁺ (A ∧ₚ B)
  t = t₀ , t₁
  goal : (y : d⁻ (A ∧ₚ B)) → Σ \(rs : dd⁻ (Γ ++ Δ)) → Prfᴬ (∥ Γ ++ Δ ∥ xs rs) (∣ A ∧ₚ B ∣ t y)
  goal (y₀ , y₁) = rs , claim₃
   where
    rs₀ : dd⁻ Γ
    rs₀ = pr₀ (pr₁ (IH₀ xs₀) y₀)
    rs₁ : dd⁻ Δ
    rs₁ = pr₀ (pr₁ (IH₁ xs₁) y₁)
    rs : dd⁻ (Γ ++ Δ)
    rs = pairᴸ⁻ Δ rs₀ rs₁
    claim₀ : Prfᴬ (∥ Γ ∥ xs₀ rs₀) (∣ A ∣ t₀ y₀)
    claim₀ = pr₁ (pr₁ (IH₀ xs₀) y₀)
    claim₁ : Prfᴬ (∥ Δ ∥ xs₁ rs₁) (∣ B ∣ t₁ y₁)
    claim₁ = pr₁ (pr₁ (IH₁ xs₁) y₁)
    claim₂ : Prfᴬ (∥ Γ ∥ xs₀ rs₀ × ∥ Δ ∥ xs₁ rs₁) (∣ A ∣ t₀ y₀ × ∣ B ∣ t₁ y₁)
    claim₂ (γ , δ) = claim₀ γ , claim₁ δ
    claim₃ : Prfᴬ (∥ Γ ++ Δ ∥ xs rs) (∣ A ∧ₚ B ∣ (t₀ , t₁) (y₀ , y₁))
    claim₃ ρ = claim₂ (∥++∥→× Δ xs rs₀ rs₁ ρ)

case-∧ₚ-elim₀ : {Γ : Asmpt} (A B : Prp)
             → ((xs : dd⁺ Γ) → Σ \(t : d⁺ (A ∧ₚ B)) → (y : d⁻ (A ∧ₚ B)) → Σ \(rs : dd⁻ Γ) → Prfᴬ (∥ Γ ∥ xs rs) (∣ A ∧ₚ B ∣ t y))
             → (xs : dd⁺ Γ) → Σ \(t : d⁺ A) → (y : d⁻ A) → Σ \(rs : dd⁻ Γ) → Prfᴬ (∥ Γ ∥ xs rs) (∣ A ∣ t y)
case-∧ₚ-elim₀ {Γ} A B IH xs = t , goal
 where
  t : d⁺ A
  t = pr₀ (pr₀ (IH xs))
  goal : (y : d⁻ A) → Σ \(rs : dd⁻ Γ) → Prfᴬ (∥ Γ ∥ xs rs) (∣ A ∣ t y)
  goal y = rs , claim
   where
    rs : dd⁻ Γ
    rs = pr₀ (pr₁ (IH xs) (y , inhabitant⁻ B))
    claim : Prfᴬ (∥ Γ ∥ xs rs) (∣ A ∣ t y)
    claim γ = pr₀ (pr₁ (pr₁ (IH xs) (y , inhabitant⁻ B)) γ)

case-∧ₚ-elim₁ : {Γ : Asmpt} (A B : Prp)
             → ((xs : dd⁺ Γ) → Σ \(t : d⁺ (A ∧ₚ B)) → (y : d⁻ (A ∧ₚ B)) → Σ \(rs : dd⁻ Γ) → Prfᴬ (∥ Γ ∥ xs rs) (∣ A ∧ₚ B ∣ t y))
             → (xs : dd⁺ Γ) → Σ \(t : d⁺ B) → (y : d⁻ B) → Σ \(rs : dd⁻ Γ) → Prfᴬ (∥ Γ ∥ xs rs) (∣ B ∣ t y)
case-∧ₚ-elim₁ {Γ} A B IH xs = t , goal
 where
  t : d⁺ B
  t = pr₁ (pr₀ (IH xs))
  goal : (y : d⁻ B) → Σ \(rs : dd⁻ Γ) → Prfᴬ (∥ Γ ∥ xs rs) (∣ B ∣ t y)
  goal y = rs , claim
   where
    rs : dd⁻ Γ
    rs = pr₀ (pr₁ (IH xs) (inhabitant⁻ A , y))
    claim : Prfᴬ (∥ Γ ∥ xs rs) (∣ B ∣ t y)
    claim γ = pr₁ (pr₁ (pr₁ (IH xs) (inhabitant⁻ A , y)) γ)

case-⇒ₚ-intro : {Γ : Asmpt} (A B : Prp)
             → ((xs : dd⁺ (Γ ₊ A)) → Σ \(t : d⁺ B) → (y : d⁻ B) → Σ \(rs : dd⁻ (Γ ₊ A)) → Prfᴬ (∥ Γ ₊ A ∥ xs rs) (∣ B ∣ t y))
             → (xs : dd⁺ Γ) → Σ \(t : d⁺ (A ⇒ₚ B)) → (y : d⁻ (A ⇒ₚ B)) → Σ \(rs : dd⁻ Γ) → Prfᴬ (∥ Γ ∥ xs rs) (∣ A ⇒ₚ B ∣ t y)
case-⇒ₚ-intro {Γ} A B IH xs = t , goal
 where
  fxs' : d⁺ A → dd⁺ (Γ ₊ A)
  fxs' ta zero = ta
  fxs' _ (succ i) = xs i
  t₀ : d⁺ A → d⁺ B
  t₀ ta = pr₀ (IH (fxs' ta))
  frs' : d⁺ A → d⁻ B → dd⁻ (Γ ₊ A)
  frs' ta yb = pr₀ (pr₁ (IH (fxs' ta)) yb)
  t₁ : d⁺ A → d⁻ B → d⁻ A
  t₁ ta yb = (frs' ta yb) zero
  t : d⁺ (A ⇒ₚ B)
  t = t₀ , t₁
  goal : (y : d⁻ (A ⇒ₚ B)) → Σ \(rs : dd⁻ Γ) → Prfᴬ (∥ Γ ∥ xs rs) (∣ A ⇒ₚ B ∣ t y)
  goal (ta , yb) = rs , claim₁
   where
    rs : dd⁻ Γ
    rs = (frs' ta yb) ∘ succ
    tb : d⁺ B
    tb = pr₀ (IH (fxs' ta))
    ya : d⁻ A
    ya = (frs' ta yb) zero
    claim₀ : Prfᴬ (∥ Γ ∥ xs rs × ∣ A ∣ ta ya) (∣ B ∣ tb yb)
    claim₀ = pr₁ (pr₁ (IH (fxs' ta)) yb)
    claim₁ : Prfᴬ (∥ Γ ∥ xs rs) (∣ A ⇒ₚ B ∣ t (ta , yb))
    claim₁ γ a = claim₀ (γ , a)

case-⇒ₚ-elim : {Γ : Asmpt} (A B : Prp)
            → ((xs : dd⁺ Γ) → Σ \(t : d⁺ (A ⇒ₚ B)) → (y : d⁻ (A ⇒ₚ B)) → Σ \(rs : dd⁻ Γ) → Prfᴬ (∥ Γ ∥ xs rs) (∣ A ⇒ₚ B ∣ t y))
            → (xs : dd⁺ (Γ ₊ A)) → Σ \(t : d⁺ B) → (y : d⁻ B) → Σ \(rs : dd⁻ (Γ ₊ A)) → Prfᴬ (∥ Γ ₊ A ∥ xs rs) (∣ B ∣ t y)
case-⇒ₚ-elim {Γ} A B IH xs' = tb , goal
 where
  xs : dd⁺ Γ
  xs = xs' ∘ succ
  t : d⁺ (A ⇒ₚ B)
  t = pr₀ (IH xs)
  ta : d⁺ A
  ta = xs' zero
  tb : d⁺ B
  tb = pr₀ t ta
  goal : (yb : d⁻ B) → Σ \(rs' : dd⁻ (Γ ₊ A)) → Prfᴬ (∥ Γ ₊ A ∥ xs' rs') (∣ B ∣ tb yb)
  goal yb = rs' , claim₁
   where
    ya : d⁻ A
    ya = pr₁ t ta yb
    y  : d⁻ (A ⇒ₚ B)
    y  = ta , yb
    rs : dd⁻ Γ
    rs = pr₀ (pr₁ (IH xs) y)
    rs' : dd⁻ (Γ ₊ A)
    rs' zero = ya
    rs' (succ i) = rs i
    claim₀ : Prfᴬ (∥ Γ ∥ xs rs) (∣ A ∣ ta ya → ∣ B ∣ tb yb)
    claim₀ = pr₁ (pr₁ (IH xs) y)
    claim₁ : Prfᴬ (∥ Γ ₊ A ∥ xs' rs') (∣ B ∣ tb yb)
    claim₁ (γ , a) = claim₀ γ a
-}

{-
\end{code}

The cases of inference rules of quantifiers

\begin{code}
-}

{-
case-∀-intro : {Γ : Asmpt} {σ : Ty} (φ : ⟦ σ ⟧ → Prp)
             → ((x : ⟦ σ ⟧) → (xs : dd⁺ Γ) → Σ \(t : d⁺ (φ x)) → (y : d⁻ (φ x)) → Σ \(rs : dd⁻ Γ) → Prfᴬ (∥ Γ ∥ xs rs) (∣ φ x ∣ t y))
             → (xs : dd⁺ Γ) → Σ \(t : d⁺ (∀ₚ φ)) → (y : d⁻ (∀ₚ φ)) → Σ \(rs : dd⁻ Γ) → Prfᴬ (∥ Γ ∥ xs rs) (∣ ∀ₚ φ ∣ t y)
case-∀-intro {Γ} {σ} φ IH xs = t , goal
 where
  t : d⁺ (∀ₚ φ)
  t x = pr₀ (IH x xs)
  goal : (y : d⁻ (∀ₚ φ)) → Σ \(rs : dd⁻ Γ) → Prfᴬ (∥ Γ ∥ xs rs) (∣ ∀ₚ φ ∣ t y)
  goal (a , y') = pr₁ (IH a xs) y'


case-∀-elim : {Γ : Asmpt} {σ : Ty} (φ : ⟦ σ ⟧ → Prp)
            → ((xs : dd⁺ Γ) → Σ \(t : d⁺ (∀ₚ φ)) → (y : d⁻ (∀ₚ φ)) → Σ \(rs : dd⁻ Γ) → Prfᴬ (∥ Γ ∥ xs rs) (∣ ∀ₚ φ ∣ t y))
            → (a : ⟦ σ ⟧) → (xs : dd⁺ Γ) → Σ \(t : d⁺ (φ a)) → (y : d⁻ (φ a)) → Σ \(rs : dd⁻ Γ) → Prfᴬ (∥ Γ ∥ xs rs) (∣ φ a ∣ t y)
case-∀-elim {Γ} {σ} φ IH a xs = t , goal
 where
  t : d⁺ (φ a)
  t = pr₀ (IH xs) a
  goal : (y : d⁻ (φ a)) → Σ \(rs : dd⁻ Γ) → Prfᴬ (∥ Γ ∥ xs rs) (∣ φ a ∣ t y)
  goal y = pr₁ (IH xs) (a , y)


case-∃-intro : {Γ : Asmpt} {σ : Ty} (φ : ⟦ σ ⟧ → Prp)
             → (a : ⟦ σ ⟧) → ((xs : dd⁺ Γ) → Σ \(t : d⁺ (φ a)) → (y : d⁻ (φ a)) → Σ \(rs : dd⁻ Γ) → Prfᴬ (∥ Γ ∥ xs rs) (∣ φ a ∣ t y))
             → (xs : dd⁺ Γ) → Σ \(t : d⁺ (∃ₚ φ)) → (y : d⁻ (∃ₚ φ)) → Σ \(rs : dd⁻ Γ) → Prfᴬ (∥ Γ ∥ xs rs) (∣ ∃ₚ φ ∣ t y)
case-∃-intro {Γ} {σ} φ a IH xs = t , goal
 where
  t : d⁺ (∃ₚ φ)
  t = a , pr₀ (IH xs)
  goal : (y : d⁻ (∃ₚ φ)) → Σ \(rs : dd⁻ Γ) → Prfᴬ (∥ Γ ∥ xs rs) (∣ ∃ₚ φ ∣ t y)
  goal y = pr₁ (IH xs) (y a (pr₀ (IH xs)))


case-∃-elim : {Γ : Asmpt} {σ : Ty} (φ : ⟦ σ ⟧ → Prp) (A : Prp)
            → ((x : ⟦ σ ⟧) → (xs : dd⁺ Γ) → Σ \(t : d⁺ (φ x ⇒ₚ A)) → (y : d⁻ (φ x ⇒ₚ A)) → Σ \(rs : dd⁻ Γ) → Prfᴬ (∥ Γ ∥ xs rs) (∣ φ x ⇒ₚ A ∣ t y))
            → (xs : dd⁺ Γ) → Σ \(t : d⁺ ((∃ₚ φ) ⇒ₚ A)) → (y : d⁻ ((∃ₚ φ) ⇒ₚ A)) → Σ \(rs : dd⁻ Γ) → Prfᴬ (∥ Γ ∥ xs rs) (∣ (∃ₚ φ) ⇒ₚ A ∣ t y)
case-∃-elim {Γ} {σ} φ A IH xs = t , goal
 where
  t₀ : (Σ \(x : ⟦ σ ⟧) → d⁺ (φ x)) → d⁺ A
  t₀ (x , w) = pr₀ (pr₀ (IH x xs)) w
  t₁ : (Σ \(x : ⟦ σ ⟧) → d⁺ (φ x)) → d⁻ A → (x : ⟦ σ ⟧) → d⁺ (φ x) → d⁻ (φ x)
  t₁ _ y x w = pr₁ (pr₀ (IH x xs)) w y
  t : d⁺ ((∃ₚ φ) ⇒ₚ A)
  t = t₀ , t₁
  goal : (y : (Σ \(x : ⟦ σ ⟧) → d⁺ (φ x)) × d⁻ A)
       → Σ \(rs : dd⁻ Γ) → Prfᴬ (∥ Γ ∥ xs rs) (∣ (∃ₚ φ) ⇒ₚ A ∣ t y)
  goal ((x , w) , y) = pr₁ (IH x xs) (w , y)
-}

{-
\end{code}

The case of the induction principle (in empty assumption)

\begin{code}
-}

{-
ICond : (ℕ → Prp) → Prp
ICond φ = ∀ₚ (λ n → φ n ⇒ₚ φ (succ n))

case-ind : (φ : ℕ → Prp)
         → ((_ : dd⁺ ε) → Σ \(t : d⁺ (φ 0)) → (y : d⁻ (φ 0)) → Σ \(_ : dd⁻ ε) → Prfᴬ 𝟙 (∣ φ 0 ∣ t y))
         → ((_ : dd⁺ ε) → Σ \(t : d⁺ (ICond φ)) → (y : d⁻ (ICond φ)) → Σ \(_ : dd⁻ ε) → Prfᴬ 𝟙 (∣ ICond φ ∣ t y))
         → (_ : dd⁺ ε) → Σ \(t : d⁺ (∀ₚ φ)) → (y : d⁻ (∀ₚ φ)) → Σ \(_ : dd⁻ ε) → Prfᴬ 𝟙 (∣ ∀ₚ φ ∣ t y)
case-ind φ IH₀ IH₁ _ = t , uncurry goal -- I have to do this, otherwise Agda doesn't believe its termination.
 where
  t0 : d⁺ (φ 0)
  t0 = pr₀ (IH₀ (λ())) 
  ts : (n : ℕ) → d⁺ (φ n) → d⁺ (φ (succ n))
  ts n tn = pr₀ (pr₀ (IH₁ (λ())) n) tn
  t : d⁺ (∀ₚ φ)
  t 0 = t0
  t (succ n) = ts n (t n)
  goal : (n : ℕ) → (yn : d⁻ (φ n)) → Σ \(_ : dd⁻ ε) → Prfᴬ 𝟙 (∣ ∀ₚ  φ ∣ t (n , yn))
  goal 0 y0 = (λ()) , pr₁ (pr₁ (IH₀ (λ())) y0)
  goal (succ n) ysn = (λ()) , claim₂
   where
    tn : d⁺ (φ n)
    tn = t n
    fy : (n : ℕ) → d⁺ (φ n) → d⁻ (φ (succ n)) → d⁻ (φ n)
    fy n = pr₁ (pr₀ (IH₁ (λ())) n)
    yn : d⁻ (φ n)
    yn = fy n tn ysn
    tsn : d⁺ (φ (succ n))
    tsn = t (succ n)
    claim₀ : Prfᴬ 𝟙 (∣ φ n ∣ tn yn)
    claim₀ = pr₁ (goal n yn)
    claim₁ : Prfᴬ 𝟙 (∣ φ n ∣ tn yn → ∣ φ (succ n) ∣ tsn ysn)
    claim₁ = pr₁ (pr₁ (IH₁ (λ())) (n , tn , ysn))
    claim₂ : Prfᴬ 𝟙 (∣ φ (succ n) ∣ tsn ysn)
    claim₂ ⋆ = claim₁ ⋆ (claim₀ ⋆)
-}

{-
\end{code}

Finally we use the above to prove Thm[soundness].

\begin{code}
-}

{-
Thm[soundness] : {Γ : Asmpt} {A : Prp} → Prf Γ A
               → (xs : dd⁺ Γ) → Σ \(t : d⁺ A) → (y : d⁻ A) → Σ \(rs : dd⁻ Γ) → Prfᴬ (∥ Γ ∥ xs rs) (∣ A ∣ t y)
Thm[soundness] refl = case-refl
Thm[soundness] (J {σ} φ base {a} {b} p) = case-J φ (λ x → Thm[soundness] (base x)) (Thm[soundness] p)
Thm[soundness] (id {A}) = case-id A
Thm[soundness] (wkn {A = A} {B = B} p) = case-wkn A B (Thm[soundness] p)
Thm[soundness] (cut {A = A} {B = B} p q) = case-cut A B (Thm[soundness] p) (Thm[soundness] q)
Thm[soundness] (swap {Γ} Δ {A} {B} {C} p) = case-swap Γ Δ A B C (Thm[soundness] p)
Thm[soundness] (∧ₚ-intro {A = A} {B = B} p q) = case-∧ₚ-intro A B (Thm[soundness] p) (Thm[soundness] q)
Thm[soundness] (∧ₚ-elim₀ {A = A} {B = B} p) = case-∧ₚ-elim₀ A B (Thm[soundness] p)
Thm[soundness] (∧ₚ-elim₁ {A = A} {B = B} p) = case-∧ₚ-elim₁ A B (Thm[soundness] p)
Thm[soundness] (⇒ₚ-intro {A = A} {B = B} p) = case-⇒-intro A B (Thm[soundness] p)
Thm[soundness] (⇒ₚ-elim {A = A} {B = B} p) = case-⇒-elim A B (Thm[soundness] p)
Thm[soundness] (∀-intro {φ = φ} f) = case-∀-intro φ (λ x → Thm[soundness] (f x))
Thm[soundness] (∀-elim {φ = φ} p a) = case-∀-elim φ (Thm[soundness] p) a
Thm[soundness] (∃-intro {φ = φ} a p) = case-∃-intro φ a (Thm[soundness] p)
Thm[soundness] (∃-elim {φ = φ} {A = A} f) = case-∃-elim φ A (λ x → Thm[soundness] (f x))
Thm[soundness] (ind φ base ih) = case-ind φ (Thm[soundness] base) (Thm[soundness] ih)
-}

{-
\end{code}

Work in progress include

(0) to add examples,

(1) to interpret J and ind with arbitrary assumptions,

(2) to interpret Markov Principle, Axiom of Choice and Independence of Premise,

(3) to generalize the method for modified realizability.

(4) to generalize the interpretation for non-standard systems.
-}
