{-# OPTIONS --rewriting #-}

-- Rank polymorphism at work
-- Artjoms Šinkarovs and Sven-Bodo Scholz, Journal of Functional Programming.
--
-- Sections 3.5 and 5: initial scan, and reshape independence of scan.
-- See StabilityNoRewrite.agda for a proof that does not use --rewriting.
--
-- This file is generated from combinators.lagda by tools/extract-agda.py;
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
open import Algebra

open import Arrays
open import Initial
open import Vectors
open import Combinators
open import Reshaping

module Stability where

-- ================
-- §3 Defining scan
-- ================

-- §3.5 Initial scan
-- -----------------

module IS where
  open I
  open FromInit I.A

  -- In the initial model, lifting shapes is the identity.  We use this as a
  -- rewrite rule, so that initial scans apply directly to arrays of type I.Ar s X.
  ⟦⟧s-id : ∀ {s : I.S} → FromInit.⟦_⟧s I.A s ≡ s
  ⟦⟧s-id {I.ι n} = refl
  ⟦⟧s-id {s I.⊗ p} = cong₂ I._⊗_ ⟦⟧s-id ⟦⟧s-id

  private variable
    X : Set
    s : S
    n : ℕ

  {-# REWRITE ⟦⟧s-id #-}

  open Scan I.A (CanonComb I.A) (CanonCombOk I.A) public

  scan₁-cong : ∀ {s} → (f : X → X → X) (e : X) (a b : Ar s X)
             → a ≈ₐ b → scan₁ s f e a ≡ scan₁ s f e b

  scan₂-cong : ∀ {s} → (f : X → X → X) (e : X) (a b : Ar s X)
             → a ≈ₐ b → scan₂ s f e a ≈ₐ scan₂ s f e b

  -- Scans of initial vectors are congruent.
  scong₁ : ∀ {n} f e (a b : I.P (I.ι n) → X) (p : ∀ i → a i ≡ b i)
         → Vec.scan f e a .proj₁ ≡ Vec.scan f e b .proj₁
  scong₁ {n = #0} f e a b p = refl
  scong₁ {n = suc n} f e a b p =
    scong₁ f _ (Vec.tl a) (Vec.tl b) (λ { (I.ι i) → p (I.ι $′ suc i) })
    ⊡ cong (λ t → Vec.scan f t (Vec.tl b) .proj₁) (cong (f e) (p (I.ι #0)))

  scong₂ : ∀ {n} f e (a b : I.P (I.ι n) → X) (p : ∀ i → a i ≡ b i)
         → ∀ i → Vec.scan f e a .proj₂ i ≡ Vec.scan f e b .proj₂ i
  scong₂ {n = suc n} f e a b p (I.ι #0) = refl
  scong₂ {n = suc n} f e a b p (I.ι (suc i)) =
    scong₂ f _ (Vec.tl a) (Vec.tl b) (λ { (I.ι j) → p (I.ι $′ suc j) }) (I.ι i)
    ⊡ cong (λ t → Vec.scan f t (Vec.tl b) .proj₂ (I.ι i)) (cong (f e) (p (I.ι #0)))

  scan₁-cong {s = I.ι n} f e a b a≈b = scong₁ f e ⟦ a ⟧a′ ⟦ b ⟧a′ (a≈b ∘ ⟦_⟧p)
  scan₁-cong {s = s I.⊗ p} f e a b a≈b
    = scan₁-cong f e _ _ (λ i → scan₁-cong f e (a ∘ (i ⊗_)) (b ∘ (i ⊗_)) (a≈b ∘ (i ⊗_)))

  -- proof of scan₂-cong
  scan₂-cong {s = I.ι n} f e a b a≈b (I.ι i)
    = scong₂ f e _ _ (a≈b ∘ ⟦_⟧p) (ι i)

  scan₂-cong {s = s I.⊗ p} f e a b a≈b (i I.⊗ j)
    = cong₂ f
        (scan₂-cong f e _ _
           (λ ix → scan₁-cong f e
                       (a ∘ (ix ⊗_))
                       (b ∘ (ix ⊗_))
                       (λ k → a≈b (ix ⊗ k))) i)
        (scan₂-cong f e (a ∘ (i ⊗_)) (b ∘ (i ⊗_)) (a≈b ∘ (i ⊗_)) j)

module ScanOk (A : Array) (Native : Comb A) (Ok : CombOk A Native) where
  open Array A
  open ArOps A
  open Comb Native
  open CombOk Ok
  open FromInit A
  open Scan A Native Ok

  private variable
    X Y Z : Set
    s p : S


  scan-ok : (s : I.S) → (f : X → X → X) → (e : X) → (a : Ar ⟦ s ⟧s X)
          →  scan₁ s f e a   ≡   IS.scan₁ s f e ⟦ a ⟧a′
          ×  scan₂ s f e a   ≈ₐ  ⟦ IS.scan₂ s f e ⟦ a ⟧a′ ⟧a

  -- Selecting from the results of native combinators, derived from CombOk.
  map-sel : (g : X → Y) (a : Ar s X) (i : P s) → map g a [ i ] ≡ g (a [ i ])
  map-sel g a i = map-ok g a i ⊡ sel-imap _ i

  nest-sel : (a : Ar (s ⊗ p) X) (i : P s) (j : P p) → nest a [ i ] [ j ] ≡ a [ i ⊛ j ]
  nest-sel a i j = cong (_[ j ]) (nest-ok a i ⊡ sel-imap _ i) ⊡ sel-imap _ j

  unnest-sel : (a : Ar s (Ar p X)) (i : P (s ⊗ p)) → unnest a [ i ] ≡ a [ fst i ] [ snd i ]
  unnest-sel a i = unnest-ok a i ⊡ sel-imap _ i

  zipWith-sel : (g : X → Y → Z) (a : Ar s X) (b : Ar s Y) (i : P s)
              → zipWith g a b [ i ] ≡ g (a [ i ]) (b [ i ])
  zipWith-sel g a b i = zipWith-ok g a b i ⊡ sel-imap _ i

  unzip₁-sel : (a : Ar s (X × Y)) (i : P s) → proj₁ (unzip a) [ i ] ≡ proj₁ (a [ i ])
  unzip₁-sel a i = unzip-ok a .proj₁ i ⊡ sel-imap _ i

  unzip₂-sel : (a : Ar s (X × Y)) (i : P s) → proj₂ (unzip a) [ i ] ≡ proj₂ (a [ i ])
  unzip₂-sel a i = unzip-ok a .proj₂ i ⊡ sel-imap _ i

  scan-ok (I.ι n) f e a
    = (scanv-ok f e a .proj₁ ⊡ IS.scong₁ f e ⟦ a ⟧a′ _ (λ { (I.ι i) → refl }))
    , λ i → scanv-ok f e a .proj₂ i ⊡ sel-imap _ i
            ⊡ IS.scong₂ f e ⟦ a ⟧a′ _ (λ { (I.ι _) → refl }) _
            ⊡ sym (sel-imap _ i)
  scan-ok {X = X} (s I.⊗ p) f e a = left , right
    where
      -- Note: the shapes are passed explicitly to IS.scan₁-cong and IS.scan₂-cong;
      -- inferring them through the rewrite rule for ⟦_⟧s is very expensive.
      -- Carries and scanned rows computed in A ...
      m : Ar ⟦ s ⟧s X
      m = unzip (map (scan p f e) (nest a)) .proj₁

      -- ... and the carries computed by the initial scan.
      mI : I.Ar s X
      mI j = IS.scan₁ p f e (λ k → a [ ⟦ j ⟧p ⊛ ⟦ k ⟧p ])

      m≈ : ⟦ m ⟧a′ I.≈ₐ mI
      m≈ j =  unzip₁-sel _ ⟦ j ⟧p
           ⊡  cong proj₁ (map-sel _ _ ⟦ j ⟧p)
           ⊡  scan-ok p f e (nest a [ ⟦ j ⟧p ]) .proj₁
           ⊡  IS.scan₁-cong {s = p} f e _ _ (λ k → nest-sel a ⟦ j ⟧p ⟦ k ⟧p)

      left : scan₁ (s I.⊗ p) f e a ≡ IS.scan₁ (s I.⊗ p) f e ⟦ a ⟧a′
      left = scan-ok s f e m .proj₁ ⊡ IS.scan₁-cong {s = s} f e _ _ m≈

      right : scan₂ (s I.⊗ p) f e a ≈ₐ ⟦ IS.scan₂ (s I.⊗ p) f e ⟦ a ⟧a′ ⟧a
      right ix
        =  unnest-sel _ ix
        ⊡  cong (_[ snd ix ]) (zipWith-sel _ _ _ (fst ix))
        ⊡  map-sel _ _ (snd ix)
        ⊡  cong₂ f
             (  scan-ok s f e m .proj₂ (fst ix) ⊡ sel-imap _ (fst ix)
             ⊡  IS.scan₂-cong {s = s} f e _ _ m≈ ⟦ fst ix ⟧p′)
             (  cong (_[ snd ix ]) (unzip₂-sel _ (fst ix) ⊡ cong proj₂ (map-sel _ _ (fst ix)))
             ⊡  scan-ok p f e (nest a [ fst ix ]) .proj₂ (snd ix) ⊡ sel-imap _ (snd ix)
             ⊡  IS.scan₂-cong {s = p} f e _ _
                  (λ k → nest-sel a (fst ix) ⟦ k ⟧p
                         ⊡ cong (λ t → a [ t ⊛ ⟦ k ⟧p ]) (sym (⟦⟧p∘⟦⟧p′ {s = s} (fst ix))))
                  ⟦ snd ix ⟧p′)
        ⊡  sym (sel-imap _ ix)

-- ===============================
-- §5 Reshape independence of scan
-- ===============================

module ISR (M : Monoid-≡)  where
  open FinVec using (scan-fin₁; scan-fin₂; scan-fin₁-cong; scan-fin₂-cong;
                    scan-fin₁-vec; scan-fin₂-vec)
  open IS
  open FinScanLemmas M
  open FromInit I.A using (⟦_⟧a′)
  open I
  open Rshp I.A
  open Monoid-≡ M
    hiding (trans; sym; refl)
    renaming (Carrier to X; assoc to ⟨+⟩-assoc)

  private variable
    s p : S

  init-scan₁-ok : (a : Ar s X) (r : Reshape s p)
      → IS.scan₁ p _⟨+⟩_ ε (reshape r a) ≡ IS.scan₁ s _⟨+⟩_ ε a
  init-scan₂-ok : (a : Ar s X) (r : Reshape s p)
      → IS.scan₂ p _⟨+⟩_ ε (reshape r a) ≈ₐ reshape r (IS.scan₂ s _⟨+⟩_ ε a)

  init-scan₁-ok a Rshp.eq = refl
  init-scan₁-ok a (Rshp._⊕_ {s = s} r r₁)
    rewrite init-scan₁-ok (λ i → scan₁ _ _⟨+⟩_ ε (λ j → a ((i ) ⊗ (j ⟨ r₁ ⟩)))) r
    = scan₁-cong {s = s} _⟨+⟩_ ε _ _ (λ i → init-scan₁-ok (λ j → a (i ⊗ j)) r₁)
  init-scan₁-ok a (r Rshp.∙ r₁)
    rewrite init-scan₁-ok (λ ix → a (ix ⟨ r₁ ⟩)) r
    = init-scan₁-ok a r₁
  init-scan₁-ok a (Rshp.split {m = m} {n = n})
    =  scan-fin₁-vec {n = m} _⟨+⟩_ ε _
    ⊡  scan-fin₁-cong {n = m} _⟨+⟩_ ε _ _ (λ i → scan-fin₁-vec {n = n} _⟨+⟩_ ε _)
    ⊡  sym (scan-fin₁-flat {m} {n} (λ k → a (ι k)))
    ⊡  sym (scan-fin₁-vec _⟨+⟩_ ε ⟦ a ⟧a′)
  init-scan₁-ok a (Rshp.flat {m = m} {n = n})
    =  scan-fin₁-vec _⟨+⟩_ ε ⟦ reshape flat a ⟧a′
    ⊡  scan-fin₁-⊗ a
    ⊡  sym (scan-fin₁-vec _⟨+⟩_ ε ⟦ (λ i → scan₁ (ι n) _⟨+⟩_ ε (λ j → a (i ⊗ j))) ⟧a′
           ⊡ scan-fin₁-cong _⟨+⟩_ ε _ _ (λ i → scan-fin₁-vec _⟨+⟩_ ε ⟦ (λ j → a (ι i ⊗ j)) ⟧a′))

  init-scan₂-ok a Rshp.eq = refl-≈ₐ
  init-scan₂-ok a (r Rshp.⊕ r₁) (i ⊗ j)
    = cong₂
        _⟨+⟩_
        (trans
          (init-scan₂-ok (λ t → scan₁ _ _⟨+⟩_ ε λ u → a (t ⊗ u ⟨ r₁ ⟩)) r i)
          (scan₂-cong _⟨+⟩_ ε _ _ (λ ix → init-scan₁-ok _ r₁) (i ⟨ r ⟩)))
        (init-scan₂-ok (λ t → a (i ⟨ r ⟩ ⊗ t)) r₁ j)
  init-scan₂-ok a (r Rshp.∙ r₁) ix
    = trans (init-scan₂-ok (λ t → a (t ⟨ r₁ ⟩)) r ix)
            (init-scan₂-ok a r₁ (ix ⟨ r ⟩))
  init-scan₂-ok a (Rshp.split {m = m} {n = n}) (ι i ⊗ ι j)
    =  cong₂ _⟨+⟩_
         (  scan-fin₂-vec {n = m} _⟨+⟩_ ε _ i
         ⊡  scan-fin₂-cong {n = m} _⟨+⟩_ ε _ _ (λ k → scan-fin₁-vec {n = n} _⟨+⟩_ ε _) i)
         (scan-fin₂-vec {n = n} _⟨+⟩_ ε _ j)
    ⊡  scan-fin₂-⊗ {m} {n} (λ k → a (ι k)) i j
    ⊡  sym (scan-fin₂-vec _⟨+⟩_ ε ⟦ a ⟧a′ (combine i j))
  init-scan₂-ok a (Rshp.flat {m = m} {n = n}) (ι k)
    =  scan-fin₂-vec {n = m * n} _⟨+⟩_ ε ⟦ reshape flat a ⟧a′ k
    ⊡  scan-fin₂-flat {m} {n} a k
    ⊡  sym (cong₂ _⟨+⟩_
              (  scan-fin₂-vec {n = m} _⟨+⟩_ ε ⟦ (λ i → scan₁ (ι n) _⟨+⟩_ ε (λ j → a (i ⊗ j))) ⟧a′ _
              ⊡  scan-fin₂-cong {n = m} _⟨+⟩_ ε _ _
                   (λ i → scan-fin₁-vec _⟨+⟩_ ε ⟦ (λ j → a (ι i ⊗ j)) ⟧a′) _)
              (scan-fin₂-vec {n = n} _⟨+⟩_ ε _ _))

module ScanCorrect (A : Array) (Native : Comb A) (Ok : CombOk A Native) (M : Monoid-≡) where
  open Array A
  open ArOps A
  open Scan A Native Ok
  open ScanOk A Native Ok
  open Rshp A
  open FromInit A
  open FromInitR A

  open Monoid-≡ M
    hiding (trans; sym; refl)
    renaming (Carrier to X; assoc to ⟨+⟩-assoc)

  open ISR M

  private variable
    s p : I.S

  scan-thm₁ : ∀ s p → (a : Ar ⟦ s ⟧s X) (r : IR.Reshape s p)
            → scan₁ p _⟨+⟩_ ε (reshape ⟦ r ⟧r a) ≡ scan₁ s _⟨+⟩_ ε a
  scan-thm₁ s p a r = begin
    scan₁     p _⟨+⟩_ ε (reshape ⟦ r ⟧r a)      ≡⟨ scan-ok p _ _ _ .proj₁ ⟩
    IS.scan₁  p _⟨+⟩_ ε ⟦ reshape ⟦ r ⟧r a ⟧a′  ≡⟨ IS.scan₁-cong _ _ _ _ (reshape-⟦⟧′ r a) ⟩
    IS.scan₁  p _⟨+⟩_ ε (IR.reshape r ⟦ a ⟧a′)  ≡⟨ init-scan₁-ok _ r ⟩
    IS.scan₁  s _⟨+⟩_ ε ⟦ a ⟧a′                 ≡˘⟨ scan-ok s _ _ _ .proj₁ ⟩
    scan₁     s _⟨+⟩_ ε a
    ∎ where open ≡-Reasoning

  scan-thm₂ : ∀ s p → (a : Ar ⟦ s ⟧s X) (r : IR.Reshape s p)
            → scan₂ p _⟨+⟩_ ε (reshape ⟦ r ⟧r a) ≈ₐ reshape ⟦ r ⟧r (scan₂ s _⟨+⟩_ ε a)

  scan-thm₂ s p a r = begin
    scan₂ p _⟨+⟩_ ε (reshape ⟦ r ⟧r a)               ≈⟨ scan-ok p _ _ _ .proj₂  ⟩
    ⟦ IS.scan₂ p _⟨+⟩_ ε ⟦ reshape ⟦ r ⟧r a ⟧a′ ⟧a   ≈⟨ ⟦⟧a-cong (IS.scan₂-cong _ _ _ _ (reshape-⟦⟧′ r a)) ⟩
    ⟦ IS.scan₂ p _⟨+⟩_ ε (IR.reshape r  ⟦ a ⟧a′) ⟧a  ≈⟨ ⟦⟧a-cong (init-scan₂-ok _ r) ⟩
    ⟦ IR.reshape r (IS.scan₂ s _⟨+⟩_ ε ⟦ a ⟧a′) ⟧a   ≈⟨ reshape-⟦⟧ r (IS.scan₂ s _ _ ⟦ a ⟧a′) ⟩
    reshape ⟦ r ⟧r ⟦ IS.scan₂ s _⟨+⟩_ ε ⟦ a ⟧a′ ⟧a   ≈˘⟨ reshape-cong ⟦ r ⟧r
                                                                      (scan-ok s _ _ _ .proj₂) ⟩
    reshape ⟦ r ⟧r (scan₂ s _⟨+⟩_ ε a)
    ∎ where open ArReasoning

  scan-r≡r′₁ : ∀ s p → (a : Ar ⟦ s ⟧s X) (r r′ : IR.Reshape s p)
             → scan₁ p _⟨+⟩_ ε (reshape ⟦ r ⟧r a) ≡ scan₁ p _⟨+⟩_ ε (reshape ⟦ r′ ⟧r a)
  scan-r≡r′₂ : ∀ s p → (a : Ar ⟦ s ⟧s X) (r r′ : IR.Reshape s p)
             → scan₂ p _⟨+⟩_ ε (reshape ⟦ r ⟧r a) ≈ₐ scan₂ p _⟨+⟩_ ε (reshape ⟦ r′ ⟧r a)
  scan-r≡r′₁ s p a r r′ = scan-thm₁ s p a r ⊡ sym (scan-thm₁ s p a r′)

  scan-r≡r′₂ s p a r r′ = begin
    scan₂ p _⟨+⟩_ ε (reshape ⟦ r ⟧r a)   ≈⟨ scan-thm₂ s p a r ⟩
    reshape ⟦ r ⟧r (scan₂ s _⟨+⟩_ ε a)   ≈⟨ reshape-prop r r′ _ ⟩
    reshape ⟦ r′ ⟧r (scan₂ s _⟨+⟩_ ε a)  ≈˘⟨ scan-thm₂ s p a r′ ⟩
    scan₂ p _⟨+⟩_ ε (reshape ⟦ r′ ⟧r a)
    ∎ where open ArReasoning
