-- Rank polymorphism at work
-- Artjoms Šinkarovs and Sven-Bodo Scholz, Journal of Functional Programming.
--
-- Sections 3.2-3.4: array combinators and generalised scan.
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

module Combinators where

-- ================
-- §3 Defining scan
-- ================

-- §3.2 Array combinators
-- ----------------------

module _ (A : Array) where
  open Array A
  private variable
    X Y Z : Set
    s p : S
    n : ℕ
  record Comb : Set₁ where
    field
      K        : X → Ar s X
      map      : (X → Y) → Ar s X → Ar s Y
      nest     : Ar (s ⊗ p) X → Ar s (Ar p X)
      unnest   : Ar s (Ar p X) → Ar (s ⊗ p) X
      unzip    : Ar s (X × Y) → Ar s X × Ar s Y
      zipWith  : (X → Y → Z) → Ar s X → Ar s Y → Ar s Z
      scanv    : (X → X → X) → X → Ar (ι n) X → X × Ar (ι n) X

module _ (A : Array) where
  open Array A
  open ArOps A
  open Comb
  open FromInit A

  CanonComb : Comb A
  CanonComb .K x            = imap λ i → x
  CanonComb .map f a        = imap (f ∘ a [_])
  CanonComb .nest a         = imap λ i → imap λ j → a [ i ⊛ j ]
  CanonComb .unnest a       = imap λ i → a [ fst i ] [ snd i ]
  CanonComb .unzip f        = CanonComb .map proj₁ f , CanonComb .map proj₂ f
  CanonComb .zipWith f a b  = imap λ i → f (a [ i ]) (b [ i ])
  CanonComb .scanv f e a    = let s , a′ = Vec.scan f e ⟦ a ⟧a′ in s , ⟦ a′ ⟧a

module _ (A : Array) (NativeComb : Comb A) where
  open Array A
  open ArOps A
  module Native = Comb NativeComb
  module Canon = Comb (CanonComb A)
  private variable
    X Y Z : Set
    s p  : S
    n : ℕ

  ni : (A : Set) → A → A
  ni A a = a

  infix -2 ni
  syntax ni A e = e ∶ A

  record CombOk : Set₁ where
    field
      K-ok        : (x : X) → (Native.K x ∶ Ar s X) ≈ₐ Canon.K x
      map-ok      : (f : X → Y) (a : Ar s X) → Native.map f a ≈ₐ Canon.map f a
      nest-ok     : (a : Ar (s ⊗ p) X) → Native.nest a ≈ₐ Canon.nest a
      unnest-ok   : (a : Ar s (Ar p X)) → Native.unnest a ≈ₐ Canon.unnest a
      unzip-ok    : (a : Ar s (X × Y))
                  → Pointwise _≈ₐ_ _≈ₐ_ (Native.unzip a) (Canon.unzip a)
      zipWith-ok  : (f : X → Y → Z) (a : Ar s X) (b : Ar s Y)
                  → Native.zipWith f a b ≈ₐ Canon.zipWith f a b
      scanv-ok    : (f : X → X → X) (e : X) (a : Ar (ι n) X)
                  → Pointwise _≡_ _≈ₐ_ (Native.scanv f e a) (Canon.scanv f e a)

module _ (A : Array) where

  CanonCombOk : CombOk A (CanonComb A)

  CanonCombOk = record
               { K-ok = λ {X} {s} x ix → refl
               ; map-ok = λ {X} {Y} {s} f a ix → refl
               ; nest-ok = λ {s} {p} {X} a ix → refl
               ; unnest-ok = λ {s} {p} {X} a ix → refl
               ; unzip-ok = λ {s} {X} {Y} a → (λ ix → refl) , (λ ix → refl)
               ; zipWith-ok = λ {X} {Y} {Z} {s} f a b ix → refl
               ; scanv-ok = λ {X} {n} f e a → refl , (λ ix → refl)
               }

-- §3.3 Generalised scan
-- ---------------------

module Scan (A : Array) (N : Comb A) (Ok : CombOk A N) where

  open Array A
  open Comb N
  open FromInit A

  private variable
    X : Set

  scan : (s : I.S) → (X → X → X) → X → Ar ⟦ s ⟧s X → X × Ar ⟦ s ⟧s X
  scan (I.ι n)    f e a  = scanv f e a
  scan (s I.⊗ p)  f e a  = let
                             m , a′  = unzip (map (scan p f e) (nest a))
                             r , m′  = scan s f e m
                             a′′     = zipWith (map ∘ f) m′ a′
                           in r , unnest a′′

  scan₁ : ∀ s → (f : X → X → X) → X → Ar ⟦ s ⟧s X → X
  scan₂ : ∀ s → (f : X → X → X) → X → Ar ⟦ s ⟧s X → Ar ⟦ s ⟧s X

  scan₁ s f e a = scan s f e a .proj₁

  scan₂ s f e a = scan s f e a .proj₂
