-- Rank polymorphism at work
-- Artjoms Šinkarovs and Sven-Bodo Scholz, Journal of Functional Programming.
--
-- Section 2.3: models, the initial model, and initiality.
--
-- This file is generated from initial.lagda by tools/extract-agda.py;
-- section numbers refer to the paper.  Do not edit by hand.

open import Data.Nat as ℕ
open import Data.Nat.Properties as ℕ
open import Data.Fin as Fin using (Fin; zero; suc; remQuot; combine; toℕ; quotRem)
open import Data.Product as Prod hiding (map; zipWith)
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Relation.Binary.PropositionalEquality as Eq hiding ([_])
open import Relation.Binary
open import Function

open import Arrays

module Initial where

-- =========
-- §2 Arrays
-- =========

-- §2.3 Models
-- -----------

module Ten where
  open import Data.List
  open import Data.Vec hiding ([_]; _++_)
  open import Data.List.Relation.Unary.All

  private variable
    s p : List ℕ
    m n : ℕ

  data Tensor (X : Set) : List ℕ → Set where
    pure  : X → Tensor X []
    roll  : Vec (Tensor X s) n → Tensor X (n ∷ s)

-- §2.3.1 Initial model
-- --------------------

module I where

  data S : Set where
    ι    : ℕ → S
    _⊗_  : S → S → S

  infixl 5 _⊗_
  private variable
    s p : S
    n : ℕ

  data P : S → Set where
    ι    : Fin n → P (ι n)
    _⊗_  : P s → P p → P (s ⊗ p)

  Ar : S → Set → Set
  Ar s X = P s → X

  A : Array
  A .Array.S    = S
  A .Array.P    = P

  A .Array.ι    = ι
  A .Array._⊗_  = _⊗_

  A .Array.Ar   = Ar

  A .Array.ι-↔ = mk↔ {to = λ { (ι i) → i }}{ι} ((λ { refl → refl }) , λ { {ι _} {_} refl → refl })
  A .Array.⊗-↔ = mk↔ {to = λ { (i ⊗ j) → i , j }}{λ { (i , j) → i ⊗ j }}
                     ((λ {refl → refl}) , λ { {i ⊗ j} {_} refl → refl})

  A .Array.Ar-↔ = mk↔ {to = id}{id} ((λ refl → refl) , λ refl → refl)

  open ArOps A public

-- §2.3.2 Initiality
-- -----------------

module FromInit (A : Array) where

  open Array A; open ArOps A

  private variable
    X : Set

  ⟦_⟧s : I.S → S
  ⟦ I.ι n   ⟧s  = ι n
  ⟦ s I.⊗ p ⟧s  = ⟦ s ⟧s ⊗ ⟦ p ⟧s

  ⟦_⟧p : ∀ {s} → I.P s → P ⟦ s ⟧s
  ⟦ I.ι   i ⟧p  = φ i
  ⟦ i I.⊗ j ⟧p  = ⟦ i ⟧p ⊛ ⟦ j ⟧p

  ⟦_⟧p′ : ∀ {s} → P ⟦ s ⟧s → I.P s
  ⟦_⟧p′ {I.ι n}    i  = I.ι (ψ i)
  ⟦_⟧p′ {s I.⊗ p}  i  = ⟦ fst i ⟧p′ I.⊗ ⟦ snd i ⟧p′

  ⟦_⟧a : ∀ {s} → I.Ar s X → Ar ⟦ s ⟧s X
  ⟦ a ⟧a = imap λ i → a ⟦ i ⟧p′

  ⟦_⟧a′ : ∀ {s} → Ar ⟦ s ⟧s X → I.Ar s X
  ⟦_⟧a′ a i = a [ ⟦ i ⟧p ]

  ⟦⟧p∘⟦⟧p′  : ∀ {s} (i : P ⟦ s ⟧s) → ⟦ ⟦_⟧p′ {s} i ⟧p ≡ i
  ⟦⟧p′∘⟦⟧p  : ∀ {s} (i : I.P s) → ⟦ ⟦ i ⟧p ⟧p′ ≡ i
  ⟦⟧a′∘⟦⟧a  : ∀ {s X} (a : Ar ⟦ s ⟧s X) → ⟦ ⟦_⟧a′ {s = s} a ⟧a ≈ₐ a
  ⟦⟧a∘⟦⟧a′  : ∀ {s X} (a : I.Ar s X) → ⟦ ⟦ a ⟧a ⟧a′ I.≈ₐ a

  ⟦⟧p∘⟦⟧p′ {I.ι n}    i = φ-ψ i
  ⟦⟧p∘⟦⟧p′ {s I.⊗ p}  i = cong₂ _⊛_ (⟦⟧p∘⟦⟧p′ {s} (fst i)) (⟦⟧p∘⟦⟧p′ {p} (snd i)) ⊡ ⊛-η i

  ⟦⟧p′∘⟦⟧p (I.ι i) = cong I.ι (ψ-φ i)
  ⟦⟧p′∘⟦⟧p {s I.⊗ p} (i I.⊗ j)
    = cong₂ I._⊗_ (cong (⟦_⟧p′ {s}) (fst-⊛ _ _) ⊡ ⟦⟧p′∘⟦⟧p i)
                  (cong (⟦_⟧p′ {p}) (snd-⊛ _ _) ⊡ ⟦⟧p′∘⟦⟧p j)

  ⟦⟧a′∘⟦⟧a {s} a ix = sel-imap _ ix ⊡ cong (a [_]) (⟦⟧p∘⟦⟧p′ {s} ix)

  ⟦⟧a∘⟦⟧a′ a ix = sel-imap _ ⟦ ix ⟧p ⊡ cong a (⟦⟧p′∘⟦⟧p ix)

  ⟦⟧a-cong : ∀ {s X} {a b : I.Ar s X} → a I.≈ₐ b → ⟦ a ⟧a ≈ₐ ⟦ b ⟧a
  ⟦⟧a-cong p ix = sel-imap _ ix ⊡ p _ ⊡ sym (sel-imap _ ix)
