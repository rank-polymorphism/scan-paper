-- Rank polymorphism at work
-- Artjoms Šinkarovs and Sven-Bodo Scholz, Journal of Functional Programming.
--
-- Sections 2.1-2.2: array theory and array operations.
--
-- This file is generated from array.lagda by tools/extract-agda.py;
-- section numbers refer to the paper.  Do not edit by hand.

open import Data.Nat as ℕ
open import Data.Nat.Properties as ℕ
open import Data.Fin as Fin using (Fin; zero; suc; remQuot; combine; toℕ; quotRem)
open import Data.Product as Prod hiding (map; zipWith)
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Relation.Binary.PropositionalEquality as Eq hiding ([_])
open import Relation.Binary
open import Function

module Arrays where

-- =========
-- §2 Arrays
-- =========

-- Transitivity of equality, written infix for proof chains.
infixl 2 _⊡_
_⊡_ : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_⊡_ = trans

private variable
  X Y Z : Set
  m n : ℕ

module Section2 where
  open import Data.List

  variable
    s p : List ℕ

  postulate


    Ar : List ℕ → Set → Set

  top-down  : (∀ {n s} → Ar ([ n ] ++ s) X → Ar s X) → (Ar [] X → X)
            → ∀ s → Ar s X → X
  top-down  f z []       a  = z a
  top-down  f z (n ∷ s)  a  = top-down f z s (f a)

  bottom-up  : (∀ {n s} → Ar (s ++ [ n ]) X → Ar s X) → (Ar [] X → X)
             → ∀ s → Ar s X → X

  data View : List ℕ → Set where
    []    : View []
    _∷′_  : (s : List ℕ) → (n : ℕ) → View (s ++ [ n ])

  view : (xs : List ℕ) → View xs

  {-# TERMINATING #-}
  bottom-up f z s a with view s
  ... | []      = z a
  ... | s ∷′ n  = bottom-up f z s (f a)

  view []        = []
  view (x ∷ xs) with view xs
  ... | []       = [] ∷′ x
  ... | s ∷′ n   = (x ∷ s) ∷′ n

-- §2.1 Array theory
-- -----------------

record Array : Set₁ where
  field

    S     : Set
    P     : S → Set

    ι     : ℕ → S
    _⊗_   : S → S → S

    ι-↔   : P (ι n) ↔ Fin n
    ⊗-↔   : ∀ {s p} → P (s ⊗ p) ↔ (P s × P p)

    Ar    : S → Set → Set
    Ar-↔  : ∀ {s} → (P s → X) ↔ Ar s X

-- §2.2 Array operations
-- ---------------------

module ArOps (A : Array) where

  open Array A
  private variable
    s p l r : S

  imap  : (P s → X) → Ar s X
  _[_]  : Ar s X → (P s → X)

  φ    : Fin n → P (ι n)
  ψ    : P (ι n) → Fin n

  fst  : P (l ⊗ r) → P l
  snd  : P (l ⊗ r) → P r
  _⊛_  : P l → P r → P (l ⊗ r)

  i ⊛ j = Inverse.from ⊗-↔ (i , j)
  φ     = Inverse.from ι-↔
  ψ     = Inverse.to ι-↔
  snd   = proj₂ ∘ Inverse.to ⊗-↔
  fst   = proj₁ ∘ Inverse.to ⊗-↔
  imap  = Inverse.to Ar-↔
  _[_]  = Inverse.from Ar-↔

  private variable
    a b c : Ar s X

-- §2.2.1 Equality of arrays
-- -------------------------

  _≈ₐ_ : Ar s X → Ar s X → Set
  a ≈ₐ b = ∀ ix → a [ ix ] ≡ b [ ix ]

  refl-≈ₐ   : a ≈ₐ a
  sym-≈ₐ    : a ≈ₐ b → b ≈ₐ a
  trans-≈ₐ  : a ≈ₐ b → b ≈ₐ c → a ≈ₐ c

  refl-≈ₐ ix = refl
  sym-≈ₐ a≈b ix = sym (a≈b ix)
  trans-≈ₐ a≈b b≈c ix = trans (a≈b ix) (b≈c ix)


  import Relation.Binary.Reasoning.Setoid as EqReasoning

  ≈ₐ-isEquiv : ∀ {s X} → IsEquivalence (_≈ₐ_ {s} {X})
  ≈ₐ-isEquiv = record { refl = refl-≈ₐ ; sym = sym-≈ₐ ; trans = trans-≈ₐ}

  ArSetoid : ∀ {s X} → Setoid _ _
  ArSetoid {s} {X} = record { isEquivalence = ≈ₐ-isEquiv {s} {X}}

  module ArReasoning {s} {X} = EqReasoning (ArSetoid {s} {X})

  -- Named consequences of the isomorphisms of the array theory.
  sel∘imap : ∀ {s X} (a : P s → X) → imap a [_] ≡ a
  sel∘imap = Inverse.strictlyInverseʳ Ar-↔

  sel-imap : ∀ {s X} (a : P s → X) (i : P s) → imap a [ i ] ≡ a i
  sel-imap a i = cong (_$ i) (sel∘imap a)

  ψ-φ : (i : Fin n) → ψ (φ i) ≡ i
  ψ-φ = Inverse.strictlyInverseˡ ι-↔

  φ-ψ : (i : P (ι n)) → φ (ψ i) ≡ i
  φ-ψ = Inverse.strictlyInverseʳ ι-↔

  fst-snd-⊛ : (i : P l) (j : P r) → Inverse.to ⊗-↔ (i ⊛ j) ≡ (i , j)
  fst-snd-⊛ i j = Inverse.strictlyInverseˡ ⊗-↔ (i , j)

  fst-⊛ : (i : P l) (j : P r) → fst (i ⊛ j) ≡ i
  fst-⊛ i j = cong proj₁ (fst-snd-⊛ i j)

  snd-⊛ : (i : P l) (j : P r) → snd (i ⊛ j) ≡ j
  snd-⊛ i j = cong proj₂ (fst-snd-⊛ i j)

  ⊛-η : (i : P (l ⊗ r)) → fst i ⊛ snd i ≡ i
  ⊛-η = Inverse.strictlyInverseʳ ⊗-↔
