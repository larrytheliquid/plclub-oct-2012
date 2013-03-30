module Slides.Three where
open import Slides.Domain

infixr 2 _`→_

----------------------------------------------------------------------

data Desc (U : Set) (El : U → Set) (I : Set) : Set where
  `⊤ : Desc U El I
  `X : (i : I) → Desc U El I
  _`⊎_ _`×_ : (δ δ′ : Desc U El I) → Desc U El I
  `Σ `Π : (u : U) (δ : El u → Desc U El I) → Desc U El I

⟦_⟧ᵈ : ∀{U El I} → Desc U El I → (I → Set) → Set
⟦ `⊤ ⟧ᵈ X = ⊤
⟦ `X i ⟧ᵈ X = X i
⟦ δ `⊎ δ′ ⟧ᵈ X = ⟦ δ ⟧ᵈ X ⊎ ⟦ δ′ ⟧ᵈ X
⟦ δ `× δ′ ⟧ᵈ X = ⟦ δ ⟧ᵈ X × ⟦ δ′ ⟧ᵈ X
⟦_⟧ᵈ {El = El} (`Σ τ δ) X = Σ (El τ) λ e → ⟦ δ e ⟧ᵈ X
⟦_⟧ᵈ {El = El} (`Π τ δ) X = (e : El τ) → ⟦ δ e ⟧ᵈ X

data μ {U El I} (R : I → Desc U El I) (i : I) : Set where
  con : ⟦ R i ⟧ᵈ (μ R) → μ R i

----------------------------------------------------------------------

data Type′ (U : Set) (El : U → Set) : Set
⟦_⟧′ : ∀{U El} → Type′ U El → Set

data Type′ U El where
  `Type : Type′ U El
  `⟦_⟧ : U → Type′ U El
  `⊥ `⊤ `Bool : Type′ U El
  `Π `Σ : (τ : Type′ U El)
    (τ′ : ⟦ τ ⟧′ → Type′ U El) → Type′ U El
  `Desc : (τ : Type′ U El) → Type′ U El
  `μ : (τ : Type′ U El)
    (δ : ⟦ τ ⟧′ → Desc U El ⟦ τ ⟧′)
    (i : ⟦ τ ⟧′) → Type′ U El

⟦_⟧′ {U = U} `Type = U
⟦_⟧′ {El = El} `⟦ τ ⟧ = El τ
⟦ `⊥ ⟧′ = ⊥
⟦ `⊤ ⟧′ = ⊤
⟦ `Bool ⟧′ = Bool
⟦ `Π τ τ′ ⟧′ = (v : ⟦ τ ⟧′) → ⟦ τ′ v ⟧′
⟦ `Σ τ τ′ ⟧′ = Σ ⟦ τ ⟧′ λ v → ⟦ τ′ v ⟧′
⟦_⟧′ {U} {El} (`Desc τ) = Desc U El ⟦ τ ⟧′
⟦_⟧′ {U} {El} (`μ τ δ i) = μ δ i

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

lift : ∀{n} → Type n → Type (suc n)
lift x = `⟦ x ⟧

-- lower : ∀{n} → Type (suc (suc n)) → Type (suc n)

----------------------------------------------------------------------

`ℕ₀ : ⟦ `Type ⟧₁
`ℕ₀ = `μ `⊤ (λ {tt → `⊤ `⊎ `X tt}) tt

`ℕ : Type₁
`ℕ = `⟦ `ℕ₀ ⟧

`zero : ⟦ `ℕ ⟧₁
`zero = con (inj₁ tt)

`suc : ⟦ `ℕ `→ `ℕ ⟧₁
`suc n = con (inj₂ n)

----------------------------------------------------------------------

`List₀ : ⟦ `Type  ⟧₁ → Type₁
`List₀ A = `μ `⊤ (λ {tt → `⊤ `⊎ `Σ A (λ _ → `X tt)}) tt

`ListD : ⟦ `Type `→ `⊤ `→ `Desc `⊤  ⟧₁
`ListD A tt = `⊤ `⊎ `Σ A (λ _ → `X tt)

----------------------------------------------------------------------

VecD : ⟦ `Type `→ `ℕ `→ `Desc `ℕ ⟧₁
VecD A (con (inj₁ tt)) = `⊤
VecD A (con (inj₂ n)) = `Σ A λ _ → `X n

`Vec : Type₁
`Vec = `Π `Type λ A → `Π `ℕ (`μ `ℕ (VecD A))

`nil : ⟦ `Π `Type (λ A → `μ `ℕ (VecD A) `zero) ⟧₁
`nil A = con tt

`cons : ⟦ `Π `Type (λ A → `Π `ℕ (λ n → `⟦ A ⟧ `→
  `μ `ℕ (VecD A) n `→ `μ `ℕ (VecD A) (`suc n))) ⟧₁
`cons A n x xs = con (x , xs)

----------------------------------------------------------------------

TreeD : ⟦ `Type `→ `ℕ `→ `Desc `ℕ ⟧₁
TreeD A (con (inj₁ tt)) = `⊤
TreeD A (con (inj₂ n)) = `Σ A λ _ → `X n `× `X n

`leaf : ⟦ `Π `Type (λ A → `μ `ℕ (TreeD A) `zero) ⟧₁
`leaf A = con tt

`node : ⟦ `Π `Type (λ A → `Π `ℕ (λ n → `⟦ A ⟧ `→
  `μ `ℕ (TreeD A) n `→ 
  `μ `ℕ (TreeD A) n `→ 
  `μ `ℕ (TreeD A) (`suc n))) ⟧₁
`node A n x xs xs′ = con (x , xs , xs′)

`sapling : ⟦ `μ `ℕ (TreeD `Bool) (`suc `zero) ⟧₁
`sapling = `node `Bool `zero true (`leaf `Bool) (`leaf `Bool)

----------------------------------------------------------------------

`bloom : ⟦ `Π `Type (λ I → `Desc `⟦ I ⟧ `→ `Type `→ `Desc `⟦ I ⟧) ⟧₁
`bloom I `⊤ X = `Σ X λ _ → `⊤
`bloom I (`X i) X = `X i
`bloom I (δ `⊎ δ′) X = `bloom I δ X `⊎ `bloom I δ′ X
`bloom I (δ `× δ′) X = `bloom I δ X `× `bloom I δ′ X
`bloom I (`Σ A δ) X = `Σ A (λ a → `bloom I (δ a) X)
`bloom I (`Π A δ) X = `Π A (λ a → `bloom I (δ a) X)

`BloomingTreeD : ⟦ `Type `→ `ℕ `→ `Desc `ℕ ⟧₁
`BloomingTreeD A n = `bloom `ℕ₀ (TreeD `Bool n) `Bool