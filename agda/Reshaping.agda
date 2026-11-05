-- Rank polymorphism at work
-- Artjoms Šinkarovs and Sven-Bodo Scholz, Journal of Functional Programming.
--
-- Section 4: reshapes.
--
-- This file is generated from combinators.lagda by tools/extract-agda.py;
-- section numbers refer to the paper.  Do not edit by hand.

open import Data.Nat as ℕ
open import Data.Nat.Properties as ℕ
open import Data.Fin as Fin using (Fin; zero; suc; remQuot; combine; toℕ; quotRem)
open import Data.Product as Prod hiding (map; zipWith)
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Relation.Binary.PropositionalEquality as Eq hiding ([_])
open import Relation.Binary
open import Function
open import Data.Fin.Properties as Fin using (remQuot-combine; combine-remQuot; toℕ-combine; toℕ-injective; combine-injectiveˡ; combine-injectiveʳ)
open import Algebra

open import Arrays
open import Initial
open import Vectors
open import Combinators

module Reshaping where

-- ============
-- §4 Reshaping
-- ============

module Rshp (A : Array) where
  open Array A; open ArOps A
  private variable
   m n : ℕ
   s p q r : S
   X : Set

  infixl 17 _⊕_
  infixl 15 _∙_
  infixr 16 _⟨_⟩

  data Reshape : S → S → Set where
    eq     : Reshape s s
    _⊕_    : Reshape s p → Reshape q r → Reshape (s ⊗ q) (p ⊗ r)
    _∙_    : Reshape q p → Reshape s q → Reshape s p
    split  : Reshape (ι (m * n)) (ι m ⊗ ι n)
    flat   : Reshape (ι m ⊗ ι n) (ι (m * n))

  rev : Reshape s p → Reshape p s
  rev eq        = eq
  rev (r ⊕ r₁)  = rev r ⊕ rev r₁
  rev (r ∙ r₁)  = rev r₁ ∙ rev r
  rev split     = flat
  rev flat      = split

  import Relation.Binary.Reasoning.Setoid as EqReasoning

  Reshape-isEquiv : IsEquivalence Reshape
  Reshape-isEquiv = record { refl = eq ; sym = rev ; trans = λ f g → g ∙ f}

  ReshapeSetoid : Setoid _ _
  ReshapeSetoid = record { isEquivalence = Reshape-isEquiv }

  module ReshapeReasoning = EqReasoning ReshapeSetoid

  leftn : ∀ n → Reshape (ι 1 ⊗ ι n) (ι n)
  leftn n = begin
              ι 1 ⊗ ι n  ≈⟨ flat ⟩
              ι (1 * n)  ≡⟨ cong ι (*-identityˡ _) ⟩
              ι n
            ∎ where open ReshapeReasoning

  _⟨_⟩ : P p → Reshape s p → P s
  i ⟨ eq      ⟩  = i
  i ⟨ r ⊕ r₁  ⟩  = (fst i ⟨ r ⟩) ⊛ (snd i ⟨ r₁ ⟩)
  i ⟨ r ∙ r₁  ⟩  = i ⟨ r ⟩ ⟨ r₁ ⟩
  i ⟨ split   ⟩  = φ $ combine (ψ $ fst i) (ψ $ snd i)
  i ⟨ flat    ⟩  = let a , b = remQuot _ (ψ i) in φ a ⊛ φ b

  reshape : Reshape s p → Ar s X →  Ar p X
  reshape r a = imap λ ix → a [ ix ⟨ r ⟩ ]

  ⟨⟩-rev         : (r : Reshape s p) (i : P p) → i ⟨ r ⟩ ⟨ rev r ⟩ ≡ i
  ⟨⟩-rev′        : (r : Reshape s p) (i : P s) → i ⟨ rev r ⟩ ⟨ r ⟩ ≡ i
  rev-reshape-≈  : (r : Reshape s p) (a : Ar s X) → reshape (rev r) (reshape r a) ≈ₐ a
  reshape-rev-≈  : (r : Reshape s p) (a : Ar p X) → reshape r (reshape (rev r) a) ≈ₐ a

  reshape-cong   : {a b : Ar s X} (r : Reshape s p) → a ≈ₐ b → reshape r a ≈ₐ reshape r b

  rev-involutive : ∀ {s p} → (r : Reshape s p) → rev (rev r) ≡ r
  rev-involutive eq = refl
  rev-involutive (r ⊕ r₁) = cong₂ _⊕_ (rev-involutive r) (rev-involutive r₁)
  rev-involutive (r ∙ r₁) = cong₂ _∙_ (rev-involutive r) (rev-involutive r₁)
  rev-involutive split = refl
  rev-involutive flat = refl

  ⟨⟩-rev eq i = refl
  ⟨⟩-rev (r ⊕ r₁) i
    = cong₂ _⊛_ (cong (_⟨ rev r ⟩) (fst-⊛ _ _) ⊡ ⟨⟩-rev r (fst i))
                (cong (_⟨ rev r₁ ⟩) (snd-⊛ _ _) ⊡ ⟨⟩-rev r₁ (snd i))
    ⊡ ⊛-η i
  ⟨⟩-rev (r ∙ r₁) i
    = cong (_⟨ rev r ⟩) (⟨⟩-rev r₁ (i ⟨ r ⟩)) ⊡ ⟨⟩-rev r i
  ⟨⟩-rev (split {n = n}) i
    = cong (λ k → φ (proj₁ k) ⊛ φ (proj₂ k))
           (cong (remQuot n) (ψ-φ _) ⊡ remQuot-combine (ψ (fst i)) (ψ (snd i)))
    ⊡ cong₂ _⊛_ (φ-ψ (fst i)) (φ-ψ (snd i))
    ⊡ ⊛-η i
  ⟨⟩-rev (flat {m = m} {n = n}) i
    = cong φ (cong₂ (combine {m} {n}) (cong ψ (fst-⊛ _ _) ⊡ ψ-φ _) (cong ψ (snd-⊛ _ _) ⊡ ψ-φ _)
              ⊡ combine-remQuot {m} n (ψ i))
    ⊡ φ-ψ i

  ⟨⟩-rev′ r i = cong (i ⟨ rev r ⟩ ⟨_⟩) (sym (rev-involutive r)) ⊡ ⟨⟩-rev (rev r) i

  reshape-≈ : ∀ {s p X} → (r : Reshape s p) → (a b : Ar s X) → reshape r a ≈ₐ reshape r b → a ≈ₐ b
  reshape-≈ r a b ra≈rb ix
    =  cong (a [_]) (sym (⟨⟩-rev′ r ix))
    ⊡  sym (sel-imap _ _) ⊡ ra≈rb (ix ⟨ rev r ⟩) ⊡ sel-imap _ _
    ⊡  cong (b [_]) (⟨⟩-rev′ r ix)

  rev-reshape-≈ r a ix = sel-imap _ ix ⊡ sel-imap _ _ ⊡ cong (a [_]) (⟨⟩-rev′ r ix)

  reshape-rev-≈ r a = subst (λ t → reshape t (reshape (rev r) a) ≈ₐ a)
                            (rev-involutive r) (rev-reshape-≈ (rev r) a)

  reshape-cong r a≈b ix = sel-imap _ ix ⊡ a≈b (ix ⟨ r ⟩) ⊡ sym (sel-imap _ ix)

-- In the initial model all reshapes between the same shapes act identically
-- on indices.  The proof maps every index to its row-major offset, which is
-- injective and preserved by the action of any reshape.
module IRProp where
  open I using (S; P; ι; _⊗_)
  open Rshp I.A
  private variable
    s p : S

  size : S → ℕ
  size (ι n)    = n
  size (s ⊗ p)  = size s * size p

  size-≡ : Reshape s p → size s ≡ size p
  size-≡ eq        = refl
  size-≡ (r ⊕ r₁)  = cong₂ _*_ (size-≡ r) (size-≡ r₁)
  size-≡ (r ∙ r₁)  = size-≡ r₁ ⊡ size-≡ r
  size-≡ split     = refl
  size-≡ flat      = refl

  offset : P s → Fin (size s)
  offset (ι i)    = i
  offset (i ⊗ j)  = combine (offset i) (offset j)

  offset-inj : (i j : P s) → offset i ≡ offset j → i ≡ j
  offset-inj (ι i) (ι j) e = cong ι e
  offset-inj (i ⊗ i₁) (j ⊗ j₁) e
    = cong₂ _⊗_ (offset-inj i j (combine-injectiveˡ (offset i) (offset i₁) (offset j) (offset j₁) e))
                (offset-inj i₁ j₁ (combine-injectiveʳ (offset i) (offset i₁) (offset j) (offset j₁) e))

  -- Offsets live in Fin's of different (but equal) sizes, so we compare them in ℕ.
  offset-⟨⟩ : (r : Reshape s p) (i : P p) → toℕ (offset (i ⟨ r ⟩)) ≡ toℕ (offset i)
  offset-⟨⟩ eq i = refl
  offset-⟨⟩ (r ∙ r₁) i = offset-⟨⟩ r₁ (i ⟨ r ⟩) ⊡ offset-⟨⟩ r i
  offset-⟨⟩ (r ⊕ r₁) (i ⊗ j)
    rewrite toℕ-combine (offset (i ⟨ r ⟩)) (offset (j ⟨ r₁ ⟩))
          | toℕ-combine (offset i) (offset j)
    = cong₂ _+_ (cong₂ _*_ (size-≡ r₁) (offset-⟨⟩ r i)) (offset-⟨⟩ r₁ j)
  offset-⟨⟩ split (ι i ⊗ ι j) = refl
  offset-⟨⟩ (flat {m = m} {n = n}) (ι i) = cong toℕ (combine-remQuot {m} n i)

  ⟨⟩-prop : (r r′ : Reshape s p) (i : P p) → i ⟨ r ⟩ ≡ i ⟨ r′ ⟩
  ⟨⟩-prop r r′ i = offset-inj _ _ (toℕ-injective (offset-⟨⟩ r i ⊡ sym (offset-⟨⟩ r′ i)))

module FromInitR (A : Array) where
  open Array A; open ArOps A; open Rshp A
  open FromInit A --hiding (module IR)
  module IR where
    open Rshp I.A public
    open Array I.A public
    open ArOps I.A public
    open IRProp public using (⟨⟩-prop)

  private variable
    X : Set
    s p : I.S

-- §4.1 Initial reshapes
-- ---------------------

  ⟦_⟧r : IR.Reshape s p → Reshape ⟦ s ⟧s ⟦ p ⟧s

  reshape-⟦⟧   : (r : IR.Reshape s p) (a : I.Ar s X)
               → ⟦ IR.reshape r a ⟧a ≈ₐ reshape ⟦ r ⟧r ⟦ a ⟧a
  reshape-⟦⟧′  : (r : IR.Reshape s p) (a : Ar ⟦ s ⟧s X)
               → ⟦ reshape ⟦ r ⟧r a ⟧a′ I.≈ₐ IR.reshape r ⟦ a ⟧a′

  ⟨⟩-prop       : (r r′ : IR.Reshape s p) (i : P ⟦ p ⟧s)
                → i ⟨ ⟦ r ⟧r ⟩ ≡ i ⟨ ⟦ r′ ⟧r ⟩
  reshape-prop  : (r r′ : IR.Reshape s p) (a : Ar ⟦ s ⟧s X)
                → reshape ⟦ r ⟧r a ≈ₐ reshape ⟦ r′ ⟧r a

  ⟦ Rshp.eq ⟧r = eq
  ⟦ r Rshp.⊕ r₁ ⟧r = ⟦ r ⟧r ⊕ ⟦ r₁ ⟧r
  ⟦ r Rshp.∙ r₁ ⟧r = ⟦ r ⟧r ∙ ⟦ r₁ ⟧r
  ⟦ Rshp.split ⟧r = split
  ⟦ Rshp.flat ⟧r = flat

  ⟦⟧p′-⟨⟩ : ∀ {s p} → (r : IR.Reshape s p)
                → (ix : P ⟦ p ⟧s)
                → ⟦ (ix ⟨ ⟦ r ⟧r ⟩) ⟧p′ ≡ ⟦ ix ⟧p′ IR.⟨ r ⟩
  ⟦⟧p′-⟨⟩ Rshp.eq ix = refl
  ⟦⟧p′-⟨⟩ (r Rshp.⊕ r₁) ix
    = cong₂ I._⊗_ (cong ⟦_⟧p′ (fst-⊛ _ _) ⊡ ⟦⟧p′-⟨⟩ r (fst ix))
                  (cong ⟦_⟧p′ (snd-⊛ _ _) ⊡ ⟦⟧p′-⟨⟩ r₁ (snd ix))
  ⟦⟧p′-⟨⟩ (r Rshp.∙ r₁) ix
    = ⟦⟧p′-⟨⟩ r₁ (ix ⟨ ⟦ r ⟧r ⟩) ⊡ cong IR._⟨ r₁ ⟩ (⟦⟧p′-⟨⟩ r ix)
  ⟦⟧p′-⟨⟩ Rshp.split ix = cong I.ι (ψ-φ _)
  ⟦⟧p′-⟨⟩ Rshp.flat ix
    = cong₂ I._⊗_ (cong I.ι (cong ψ (fst-⊛ _ _) ⊡ ψ-φ _))
                  (cong I.ι (cong ψ (snd-⊛ _ _) ⊡ ψ-φ _))

  reshape-⟦⟧ r a ix
    = sel-imap _ ix ⊡ sym (sel-imap _ ix ⊡ sel-imap _ _ ⊡ cong a (⟦⟧p′-⟨⟩ r ix))

  ⟦⟧p-⟨⟩ : ∀ {s p} → (r : IR.Reshape s p)
                 → (ix : I.P p)
                 → ⟦ ix ⟧p ⟨ ⟦ r ⟧r ⟩ ≡ ⟦ ix IR.⟨ r ⟩ ⟧p
  ⟦⟧p-⟨⟩ Rshp.eq ix = refl
  ⟦⟧p-⟨⟩ (r Rshp.⊕ r₁) (il I.⊗ ir)
    = cong₂ _⊛_ (cong (_⟨ ⟦ r ⟧r ⟩) (fst-⊛ _ _) ⊡ ⟦⟧p-⟨⟩ r il)
                (cong (_⟨ ⟦ r₁ ⟧r ⟩) (snd-⊛ _ _) ⊡ ⟦⟧p-⟨⟩ r₁ ir)
  ⟦⟧p-⟨⟩ (r Rshp.∙ r₁) ix
    = cong (_⟨ ⟦ r₁ ⟧r ⟩) (⟦⟧p-⟨⟩ r ix) ⊡ ⟦⟧p-⟨⟩ r₁ (ix IR.⟨ r ⟩)
  ⟦⟧p-⟨⟩ Rshp.split (I.ι il I.⊗ I.ι ir)
    = cong φ (cong₂ combine (cong ψ (fst-⊛ _ _) ⊡ ψ-φ il) (cong ψ (snd-⊛ _ _) ⊡ ψ-φ ir))
  ⟦⟧p-⟨⟩ (Rshp.flat {m = m} {n = n}) (I.ι i)
    = cong (λ k → φ (proj₁ (remQuot {m} n k)) ⊛ φ (proj₂ (remQuot {m} n k))) (ψ-φ i)

  reshape-⟦⟧′ r a ix = sel-imap _ _ ⊡ cong (a [_]) (⟦⟧p-⟨⟩ r ix)

  ⟨⟩-prop {s} r r′ i
    =  sym (⟦⟧p∘⟦⟧p′ {s} (i ⟨ ⟦ r ⟧r ⟩))
    ⊡  cong ⟦_⟧p (⟦⟧p′-⟨⟩ r i ⊡ IR.⟨⟩-prop r r′ _ ⊡ sym (⟦⟧p′-⟨⟩ r′ i))
    ⊡  ⟦⟧p∘⟦⟧p′ {s} (i ⟨ ⟦ r′ ⟧r ⟩)

  reshape-prop r r′ a ix
    = sel-imap _ ix ⊡ cong (a [_]) (⟨⟩-prop r r′ ix) ⊡ sym (sel-imap _ ix)
