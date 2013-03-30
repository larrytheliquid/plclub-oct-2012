module Slides.Two where
open import Slides.Domain

infixr 2 _`→_

----------------------------------------------------------------------

data Type′ (U : Set) (El : U → Set) : Set
⟦_⟧′ : ∀{U El} → Type′ U El → Set

data Type′ U El where
  `Type : Type′ U El
  `⟦_⟧ : U → Type′ U El
  `⊥ `⊤ `Bool : Type′ U El
  `Π `Σ : (τ : Type′ U El)
    (τ′ : ⟦ τ ⟧′ → Type′ U El) → Type′ U El

⟦_⟧′ {U = U} `Type = U
⟦_⟧′ {El = El} `⟦ τ ⟧ = El τ
⟦ `⊥ ⟧′ = ⊥
⟦ `⊤ ⟧′ = ⊤
⟦ `Bool ⟧′ = Bool
⟦ `Π τ τ′ ⟧′ = (v : ⟦ τ ⟧′) → ⟦ τ′ v ⟧′
⟦ `Σ τ τ′ ⟧′ = Σ ⟦ τ ⟧′ λ v → ⟦ τ′ v ⟧′

----------------------------------------------------------------------

_`→_ : ∀{U El} (τ τ′ : Type′ U El) → Type′ U El
τ `→ τ′ = `Π τ λ _ → τ′

----------------------------------------------------------------------

Type₀ : Set
Type₀ = Type′ ⊥ ⊥-elim

Type : (n : ℕ) → Set
_⟦_⟧ : (n : ℕ) → Type n → Set

Type zero = Type₀
Type (suc n) = Type′ (Type n) (_⟦_⟧ n)

zero ⟦ e ⟧ = ⟦ e ⟧′
suc n ⟦ e ⟧ = ⟦ e ⟧′

Type₁ : Set
Type₁ = Type 1

⟦_⟧₁ : Type₁ → Set
⟦_⟧₁ = _⟦_⟧ 1

----------------------------------------------------------------------

_`∧_ : ⟦ `Bool `→ `Bool `→ `Bool ⟧₁
true `∧ b = b
false `∧ b = false

`tru : ⟦ `Π `Bool (λ b → if b then `⊤ else `Bool) ⟧₁
`tru true = tt
`tru false = true

`id : ⟦ `Π `Type (λ A → `⟦ A ⟧ `→ `⟦ A ⟧) ⟧₁
`id A x = x

