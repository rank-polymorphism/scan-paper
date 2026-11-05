{-# OPTIONS --rewriting #-}

-- Rank polymorphism at work
-- Artjoms Šinkarovs and Sven-Bodo Scholz, Journal of Functional Programming.
--
-- Section 6: runtime effects and cost model.
--
-- This file is generated from performance.lagda by tools/extract-agda.py;
-- section numbers refer to the paper.  Do not edit by hand.

open import Agda.Builtin.Equality.Rewrite

open import Data.Nat as ℕ
open import Data.Nat.Properties as ℕ
open import Data.Fin as Fin using (Fin; zero; suc; remQuot; combine; toℕ; quotRem)
open import Data.Product as Prod hiding (map; zipWith)
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Relation.Binary.PropositionalEquality as Eq hiding ([_])
open import Relation.Binary
open import Function
open import Data.Nat.DivMod
open import Effect.Monad

open import Arrays
open import Initial
open import Vectors
open import Combinators
open import Reshaping
open import Stability

module Performance where

-- ==================
-- §6 Runtime effects
-- ==================

Monad = RawMonad

module Effectful (M : Set → Set) (isMon : Monad M)
                 (sync : ∀ {s X} → I.Ar s (M X) → M (I.Ar s X)) where

  open I
  open Comb (CanonComb I.A) hiding (scanv)
  open RawMonad isMon hiding (_⊗_; zipWith)
  open Vec hiding (scan)
  private variable
    X Y : Set
    m n : ℕ
    s  : I.S

  scanv : (X → X → M X) → X → Vec n X → M (X × Vec n X)
  scanv {n = zero }  f e v = return (e , nil)
  scanv {n = suc n}  f e v = do e′      ← f e (hd v)
                                s , v′  ← scanv f e′ (tl v)
                                return (s , cons e v′)

  scan : (X → X → M X) → X → Ar s X → M (X × Ar s X)
  scan {s = ι n}     f e a = scanv f e a
  scan {s = s ⊗ p}   f e a = do m , a′  ← unzip <$> (sync $ map (scan f e) (nest a))
                                r , m′  ← scan f e m
                                a′′     ← sync $ unnest $ zipWith (map ∘ f) m′ a′
                                return (r , a′′)

module ScanId where
  open import Function.Identity.Effectful using (Identity) renaming (monad to Id-monad)
  module E = Effectful Identity Id-monad id
  open I using (ι; _⊗_; _≈ₐ_)

  private variable
    X : Set
    n : ℕ

  scanv-id : (f : X → X → X) (e : X) (v : Vec.Vec n X) → E.scanv f e v ≡ Vec.scan f e v
  scanv-id {n = zero}  f e v = refl
  scanv-id {n = suc n} f e v
    = cong (λ r → proj₁ r , Vec.cons e (proj₂ r)) (scanv-id f (f e (Vec.hd v)) (Vec.tl v))

  scan-id : ∀ s (f : X → X → X) (e : X) (a : I.Ar s X)
          →  E.scan f e a .proj₁ ≡ IS.scan₁ s f e a
          ×  E.scan f e a .proj₂ ≈ₐ IS.scan₂ s f e a

  scan-id (ι n) f e a
    = (cong proj₁ (scanv-id f e a) ⊡ IS.scong₁ f e a _ (λ { (ι i) → refl }))
    , λ { (ι i) → cong (λ r → proj₂ r (ι i)) (scanv-id f e a)
                  ⊡ IS.scong₂ f e a _ (λ { (ι j) → refl }) (ι i) }
  scan-id (s ⊗ p) f e a
    = (proj₁ (scan-id s f e mE) ⊡ IS.scan₁-cong f e mE mI m≈)
    , λ { (i ⊗ j) → cong₂ f (proj₂ (scan-id s f e mE) i ⊡ IS.scan₂-cong f e mE mI m≈ i)
                            (proj₂ (scan-id p f e (λ k → a (i ⊗ k))) j) }
    where
      mE = λ i → E.scan f e (λ j → a (i ⊗ j)) .proj₁
      mI = λ i → IS.scan₁ p f e (λ j → a (i ⊗ j))
      m≈ = λ i → proj₁ (scan-id p f e (λ j → a (i ⊗ j)))

-- §6.1 Left and right nesting
-- ---------------------------

module Reshapes where

  open Rshp I.A
  open I

  private variable
    s p q r : S

  _♭ : S → ℕ
  (ι n)    ♭ = n
  (s ⊗ p)  ♭ = s ♭ * p ♭

  ♭ᵣ : Reshape s (ι (s ♭))
  ♭ᵣ {ι n}    = eq
  ♭ᵣ {s ⊗ p}  = flat ∙ (♭ᵣ ⊕ ♭ᵣ)

  assocᵣ : Reshape ((s ⊗ p) ⊗ q) (s ⊗ (p ⊗ q))
  assocᵣ {s} {p} {q} =
     begin
       (s ⊗ p) ⊗ q                      ≈⟨ (♭ᵣ ⊕ ♭ᵣ) ⊕ ♭ᵣ ⟩
       (ι (s ♭) ⊗ ι (p ♭)) ⊗ ι (q ♭)    ≈⟨ flat ∙ (flat ⊕ eq) ⟩
       (ι ((s ♭ * p ♭) * q ♭))          ≡⟨ cong ι (ℕ.*-assoc (s ♭) _ _) ⟩
       (ι (s ♭ * (p ♭ * q ♭)))          ≈⟨ (eq ⊕ split) ∙ split ⟩
       (ι (s ♭) ⊗ (ι (p ♭) ⊗ ι (q ♭)))  ≈⟨ rev ♭ᵣ ⊕ (rev ♭ᵣ ⊕ rev ♭ᵣ) ⟩
       (s ⊗ (p ⊗ q))
     ∎ where open ReshapeReasoning

  _◃_ : S → S → S
  (ι n)    ◃  q = ι n ⊗ q
  (s ⊗ p)  ◃  q = s ◃ (p ◃ q)

  _◁ : S → S
  (ι n) ◁    = ι n
  (s ⊗ p) ◁  = s ◃ (p ◁)

  ⊗⇒◃ᵣ : Reshape (s ⊗ p) (s ◃ p)
  ⊗⇒◃ᵣ {ι n}    = eq
  ⊗⇒◃ᵣ {s ⊗ p}  = ⊗⇒◃ᵣ ∙ (eq ⊕ ⊗⇒◃ᵣ) ∙ assocᵣ

  ◁ᵣ : Reshape s (s ◁)
  ◁ᵣ {ι n}     = eq
  ◁ᵣ {s ⊗ p }  = ⊗⇒◃ᵣ ∙ (eq ⊕ ◁ᵣ)

  -- The result of _◁ is right-nested: every left sub-tree is a leaf.
  module EnsureRassoc where
    data IsRassoc : S → Set where
      ι     : ∀ n → IsRassoc (ι n)
      prep  : ∀ {s} n → IsRassoc s → IsRassoc (ι n ⊗ s)

    ◃-ok : ∀ s {p} → IsRassoc p → IsRassoc (s ◃ p)
    ◃-ok (ι n)    p′ = prep n p′
    ◃-ok (s ⊗ p)  p′ = ◃-ok s (◃-ok p p′)

    ◁-ok : ∀ {s} → IsRassoc (s ◁)
    ◁-ok {ι n}    = ι n
    ◁-ok {s ⊗ p}  = ◃-ok s (◁-ok {p})

  _▹_   : S → S → S
  s ▹ (ι n)    = s ⊗ ι n
  s ▹ (p ⊗ q)  = (s ▹ p) ▹ q

  _▷    : S → S
  (ι n) ▷    = ι n
  (s ⊗ p) ▷  = (s ▷) ▹ p

  ⊗⇒▹ᵣ  : Reshape (s ⊗ p) (s ▹ p)
  ⊗⇒▹ᵣ {s} {ι n}    = eq
  ⊗⇒▹ᵣ {s} {p ⊗ q}  = ⊗⇒▹ᵣ ∙ (⊗⇒▹ᵣ ⊕ eq)
                           ∙ rev assocᵣ

  ▷ᵣ    : Reshape s (s ▷)
  ▷ᵣ {ι n}    = eq
  ▷ᵣ {s ⊗ p}  = ⊗⇒▹ᵣ ∙ (▷ᵣ ⊕ eq)

  -- The result of _▷ is left-nested: every right sub-tree is a leaf.
  module EnsureLassoc where
    data IsLassoc : S → Set where
      ι     : ∀ n → IsLassoc (ι n)
      app   : ∀ {s} → IsLassoc s → ∀ n → IsLassoc (s ⊗ ι n)

    ▹-ok : ∀ {s} → IsLassoc s → ∀ p → IsLassoc (s ▹ p)
    ▹-ok s′ (ι n)    = app s′ n
    ▹-ok s′ (p ⊗ q)  = ▹-ok (▹-ok s′ p) q

    ▷-ok : ∀ {s} → IsLassoc (s ▷)
    ▷-ok {ι n}    = ι n
    ▷-ok {s ⊗ p}  = ▹-ok (▷-ok {s}) p

  sample-shape : S
  sample-shape = (ι 2 ⊗ ι 3) ⊗ ((ι 4 ⊗ ι 11) ⊗ (ι 5 ⊗ ι 6) ⊗ ι 7)

  right-nested : sample-shape ◁ ≡ ι 2 ⊗ (ι 3 ⊗ (ι 4 ⊗ (ι 11 ⊗ (ι 5 ⊗ (ι 6 ⊗ ι 7)))))
  right-nested = refl

  left-nested : sample-shape ▷ ≡ (((((ι 2 ⊗ ι 3) ⊗ ι 4) ⊗ ι 11) ⊗ ι 5) ⊗ ι 6) ⊗ ι 7
  left-nested = refl

-- §6.2 Cost model
-- ---------------

module Example where
  open Vec hiding (scan)
  open I using (Ar; ι; _⊗_)
  open Comb (CanonComb I.A)
  open Rshp I.A
  open Reshapes
  open ArOps I.A

  private variable
    X Y : Set
    m n : ℕ
    s p : I.S

  data Par : Set where
    goPar goSeq : Par

  M : Set → Set
  M X = Par → ℕ × X

  return : X → M X
  return x p = 0 , x

  _>>=_ : M X → (X → M Y) → M Y
  (m >>= f) p = let n , x = m p
                    m , y = f x p
                in  m + n , y

  stMon : RawMonad M
  stMon = mkRawMonad M return _>>=_

  open RawMonad stMon hiding (_⊗_; zipWith; return; _>>=_)

  vpar : Vec n (ℕ × X) → ℕ × Vec n X
  vpar v  =  fold ℕ._⊔_ 0 (proj₁ ∘ v)
          ,  proj₂ ∘ v

  vseq : Vec n (ℕ × X) → ℕ × Vec n X
  vseq v  =  fold ℕ._+_ 0 (proj₁ ∘ v)
          ,  proj₂ ∘ v

  vsync : Vec n (M X) → M (Vec n X)
  vsync {n} v goPar
    rewrite m≡m%n+[m/n]*n n 8 ⦃ it ⦄ = let
      r  ,  q  = vsplit {n % 8} v
      #r ,  r′ = vseq (λ i → r i goSeq)
      #q ,  q′ = vpar λ j → vseq λ i →
                   vnest {m = n / 8} q i j goSeq
    in #r + #q , vjoin r′ (vunnest λ i j → q′ j i)
  vsync v goSeq = vseq (λ i → v i goSeq)

  sync : Ar s (M X) → M (Ar s X)
  sync a p = let
    n , t = vsync (reshape ♭ᵣ a) p
    in n , reshape (rev ♭ᵣ) t

  open Effectful M stMon sync

  a : Ar (ι 10 ⊗ ι 10 ⊗ ι 10) ℕ
  a = K 1

  _+′_ : (a b : ℕ) → M ℕ
  (a +′ b) _ = 1 , a + b

  #s : Ar s ℕ → ℕ
  #s a = scan _+′_ 0 a goSeq .proj₁

  #p : Ar s ℕ → ℕ
  #p a = scan _+′_ 0 a goPar .proj₁

  _ : #s (reshape ◁ᵣ a) ≡ 3110
  _ = refl

  _ : #s (reshape ▷ᵣ a) ≡ 2210
  _ = refl

  _ : #p (reshape ◁ᵣ a) ≡ 765
  _ = refl

  _ : #p (reshape ▷ᵣ a) ≡ 341
  _ = refl
