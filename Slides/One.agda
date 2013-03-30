module Slides.One where
open import Slides.Domain

infixr 2 _`→_

----------------------------------------------------------------------

data Type′ : Set
⟦_⟧′ : Type′ → Set

data Type′ where
  `⊥ `⊤ `Bool : Type′
  `Π `Σ : (τ : Type′)
    (τ′ : ⟦ τ ⟧′ → Type′) → Type′

⟦ `⊥ ⟧′ = ⊥
⟦ `⊤ ⟧′ = ⊤
⟦ `Bool ⟧′ = Bool
⟦ `Π τ τ′ ⟧′ = (v : ⟦ τ ⟧′) → ⟦ τ′ v ⟧′
⟦ `Σ τ τ′ ⟧′ = Σ ⟦ τ ⟧′ λ v → ⟦ τ′ v ⟧′

----------------------------------------------------------------------

_`→_ : (τ τ′ : Type′) → Type′
τ `→ τ′ = `Π τ λ _ → τ′

----------------------------------------------------------------------

_`∧_ : ⟦ `Bool `→ `Bool `→ `Bool ⟧′
true `∧ b = b
false `∧ b = false

`tru : ⟦ `Π `Bool (λ b → if b then `⊤ else `Bool) ⟧′
`tru true = tt
`tru false = true




