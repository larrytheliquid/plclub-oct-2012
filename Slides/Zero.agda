open import Data.Unit
open import Data.Bool
open import Data.Nat
open import Data.Product hiding ( _×_ )
open import Data.Maybe
open import Data.Sum
open import Relation.Binary.PropositionalEquality
module Slides.Zero where

----------------------------------------------------------------------

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

Bool×ℕ : Set
Bool×ℕ = Bool × ℕ

-- Define functions accepting types as parameters
-- and returning new types
Bool× : Set → Set
Bool× = _×_ Bool

-- But cannot analyze the type definition from within the language
-- or define new types like you would using "data".

----------------------------------------------------------------------

data Tree (A : Set) : ℕ → Set where
  node : ∀{n} → A → Tree A n → Tree A n → Tree A (suc n)
  leaf : Tree A zero

tree : Tree Bool 2
tree = node true (node false leaf leaf) (node true leaf leaf)

postulate foldTree : ∀{A n} {B : Set} → B → (A → B → B) → Tree A n → B

----------------------------------------------------------------------

-- Now we would like a Tree that stores a ℕ "weight" in the leaves.
-- We must create an entirely new datatype and rewrite functions such
-- as "foldTree".

----------------------------------------------------------------------

-- Let's hypothesize how we could do this by writing functions over
-- a datatype that represents definitions that we write using "data".

data Desc (I : Set) : Set₁ where
  `⊤ : Desc I
  `X : (i : I) → Desc I
  _`⊎_ _`×_ : (δ δ′ : Desc I) → Desc I
  `Σ `Π : (A : Set) (δ : A → Desc I) → Desc I

TreeD : Set → ℕ → Desc ℕ
TreeD A zero = `⊤
TreeD A (suc n) = `Σ A λ _ → `X n `× `X n

TreeD′ : Set → ℕ → Desc ℕ
TreeD′ A m = (`Σ (m ≡ 0) λ _ → `⊤)
         `⊎ (`Σ ℕ λ n → `Σ (suc n ≡ m) λ _ → `Σ A λ _ → `X n `× `X n)

----------------------------------------------------------------------

bloom : ∀{I} → Desc I → Set → Desc I
bloom `⊤ X = `Σ X λ _ → `⊤ -- Interesting Case
bloom (`X i) X = `X i
bloom (δ `⊎ δ′) X = bloom δ X `⊎ bloom δ′ X
bloom (δ `× δ′) X = bloom δ X `× bloom δ′ X
bloom (`Σ A δ) X = `Σ A (λ a → bloom (δ a) X)
bloom (`Π A δ) X = `Π A (λ a → bloom (δ a) X)

----------------------------------------------------------------------

-- Now let's actually interpret these mere descriptions as real types!

⟦_⟧ : {I : Set} → Desc I → (I → Set) → Set
⟦ `⊤ ⟧ X = ⊤
⟦ `X i ⟧ X = X i
⟦ T `× T' ⟧ X = ⟦ T ⟧ X × ⟦ T' ⟧ X
⟦ T `⊎ T' ⟧ X = ⟦ T ⟧ X ⊎ ⟦ T' ⟧ X
⟦ `Σ S T ⟧ X = Σ S λ s → ⟦ T s ⟧ X
⟦ `Π S T ⟧ X = (s : S) → ⟦ T s ⟧ X

data μ {I : Set}(R : I → Desc I)(i : I) : Set where
  con : ⟦ R i ⟧ (μ R) → μ R i

----------------------------------------------------------------------

μTree : Set → ℕ → Set
μTree A n = μ (TreeD A) n

BloomingTreeD : Set → ℕ → Desc ℕ
BloomingTreeD A n = bloom {ℕ} (TreeD A n) Bool

μBloomingTree : Set → ℕ → Set
μBloomingTree A n = μ (λ m → bloom (TreeD A m) Bool) n

μTreeBool⊎3+ : Set → ℕ → Set
μTreeBool⊎3+ A n = μTree (Bool ⊎ A) (3 + n)

-- This is using plain old dependently typed programming to
-- calculate new types, not introducing a notion of staged programming
-- like lisp macros or language templating.

-- Also can write generic functions over all interpretations of all
-- codes

----------------------------------------------------------------------

-- Programming in this universe is fine, but it is entirely isolated from
-- Agda's notion of datatypes.
-- We would like a type theory that translates all data declarations into
-- such a representation.
-- Agda cannot currently do this, because it has external checkers for
-- positivity, termination, etc.

----------------------------------------------------------------------

`leaf : ∀{A} → μTree A 0
`leaf = con tt

`node : ∀{A n} → A → μTree A n → μTree A n → μTree A (suc n)
`node x xs xs′ = con (x , xs , xs′)

`sapling : μTree Bool 1
`sapling = `node true `leaf `leaf

----------------------------------------------------------------------

eq : ∀{I} → {R : I → Desc I} {i : I} → μ R i → μ R i → Maybe Bool
eq′ : ∀{I} → {R : I → Desc I} (D : Desc I) → ⟦ D ⟧ (μ R) → ⟦ D ⟧ (μ R) → Maybe Bool

eq {R = R} {i = i} (con x) (con y) = eq′ (R i) x y
eq′ `⊤ tt tt = just true
eq′ (`X i) x y = eq x y
eq′ (δ `⊎ δ′) (inj₁ x) (inj₁ y) = eq′ δ x y
eq′ (δ `⊎ δ′) (inj₁ x) (inj₂ y) = just false
eq′ (δ `⊎ δ′) (inj₂ x) (inj₁ y) = just false
eq′ (δ `⊎ δ′) (inj₂ x) (inj₂ y) = eq′ δ′ x y
eq′ (δ `× δ′) (x , x′) (y , y′) with eq′ δ x y
... | nothing = nothing
... | just false = just false
... | just true = eq′ δ′ x′ y′
eq′ (`Σ A δ) (x , x′) (y , y′) = nothing
eq′ (`Π A δ) x y = nothing

----------------------------------------------------------------------

_≣_ : ∀{I} → {R : I → Desc I} {i : I} → μ R i → μ R i → Set
x ≣ y = eq x y ≡ just true

----------------------------------------------------------------------

leaf≡leaf : ∀{A} → eq (`leaf {A}) `leaf ≡ just true
leaf≡leaf = refl

leaf≣leaf : (`leaf {Bool}) ≣ `leaf
leaf≣leaf = refl

sapling≟sapling : eq `sapling `sapling ≡ nothing
sapling≟sapling = refl

----------------------------------------------------------------------

Foo : Set₀
Foo = Bool ⊎ ℕ

Bar : Set₁
Bar = Set ⊎ ℕ