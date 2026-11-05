-- Rank polymorphism at work
-- Artjoms Šinkarovs and Sven-Bodo Scholz, Journal of Functional Programming.
--
-- Section 3.1: scan on vectors, and lemmas about scans of vectors used in Section 5.
--
-- This file is generated from vector.lagda by tools/extract-agda.py;
-- section numbers refer to the paper.  Do not edit by hand.

open import Data.Nat as ℕ
open import Data.Nat.Properties as ℕ
open import Data.Fin as Fin using (Fin; zero; suc; remQuot; combine; toℕ; quotRem)
open import Data.Product as Prod hiding (map; zipWith)
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Relation.Binary.PropositionalEquality as Eq hiding ([_])
open import Relation.Binary
open import Function
open import Data.Fin as F using ()
open import Data.Fin.Properties as Fin using (remQuot-combine)
open import Data.Sum using (inj₁; inj₂)
open import Algebra

open import Arrays
open import Initial

module Vectors where

-- ================
-- §3 Defining scan
-- ================

-- §3.1 Scan on vectors
-- --------------------

open I

pattern #0 = zero

private variable
  m n : ℕ
  X Y Z : Set
module Vec where

  Vec : ℕ → Set → Set
  Vec n X = Ar (ι n) X

  nil : Vec 0 X
  nil (ι ())

  hd : Vec (suc n) X → X
  hd v = v (ι zero)

  tl : Vec (suc n) X → Vec n X
  tl v (ι i) = v (ι (suc i))

  cons : X → Vec n X → Vec (suc n) X
  cons x v (ι zero)     = x
  cons x v (ι (suc i))  = v (ι i)

  scan : (X → X → X) → X → Vec n X → X × Vec n X
  scan {n = 0}      f acc v  = acc , nil
  scan {n = suc _}  f acc v  = let s , v′ = scan f (f acc $ hd v) (tl v)
                               in  s , cons acc v′

  fold : (X → Y → Y) → Y → Vec n X → Y
  fold {n = zero} f e v = e
  fold {n = suc n} f e v = fold f (f (hd v) e) (tl v)

  vsplit : Vec (m + n) X → Vec m X × Vec n X
  vsplit {m} {n} v = (λ { (ι i) → v $ ι $ F.join m n (inj₁ i)}) , (λ { (ι i) → v $ ι $ F.join m n (inj₂ i)})

  vjoin : Vec m X → Vec n X → Vec (m + n) X
  vjoin {m} v w (ι i) with F.splitAt m i
  ... | inj₁ i = v (ι i)
  ... | inj₂ j = w (ι j)

  vnest : Vec (m * n) X → Vec m (Vec n X)
  vnest {m} {n} v (ι i) (ι j) = v $ ι $ (F.combine i j)

  vunnest : Vec m (Vec n X) → Vec (m * n) X
  vunnest {m} {n} v (ι i) = let j , k = F.remQuot n i in v (ι j) (ι k)

  scan′ : (X → Y → Y) → Y → Vec n X → Y × Vec n Y
  scan′ f e a = let s , a′ = scan _∘′_ id (f ∘′ a) in
                s e , (λ i → a′ i e)

-- Vectors as plain functions on Fin.  The initial-model vectors of type Vec n X
-- (functions on I.P (ι n)) only compute after matching on ι; for Fin-functions
-- the tail is simply v ∘ suc.  We therefore state and prove the arithmetic
-- lemmas about scans in Section 5 on Fin-vectors, and relate the two scans via
-- scan-fin₁-vec and scan-fin₂-vec.
module FinVec where
  Vec : ℕ → Set → Set
  Vec n X = Fin n → X

  nil : Vec 0 X
  nil ()

  hd : Vec (suc n) X → X
  hd v = v zero

  tl : Vec (suc n) X → Vec n X
  tl v i = v (suc i)

  cons : X → Vec n X → Vec (suc n) X
  cons x v zero     = x
  cons x v (suc i)  = v i

  scan : (X → X → X) → X → Vec n X → X × Vec n X
  scan {n = 0}      f acc v  = acc , nil
  scan {n = suc _}  f acc v  = let s , v′ = scan f (f acc $ hd v) (tl v)
                               in  s , cons acc v′

  scan-fin₁ : (X → X → X) → X → Vec n X → X
  scan-fin₁ f e v = scan f e v .proj₁

  scan-fin₂ : (X → X → X) → X → Vec n X → Vec n X
  scan-fin₂ f e v = scan f e v .proj₂

  scan-fin₁-cong : (f : X → X → X) (e : X) (a b : Vec n X)
                 → (∀ i → a i ≡ b i) → scan-fin₁ f e a ≡ scan-fin₁ f e b
  scan-fin₁-cong {n = zero}  f e a b a≈b = refl
  scan-fin₁-cong {n = suc n} f e a b a≈b rewrite a≈b zero
    = scan-fin₁-cong f (f e (b zero)) (a ∘ suc) (b ∘ suc) (a≈b ∘ suc)

  scan-fin₂-cong : (f : X → X → X) (e : X) (a b : Vec n X)
                 → (∀ i → a i ≡ b i) → ∀ j → scan-fin₂ f e a j ≡ scan-fin₂ f e b j
  scan-fin₂-cong {n = zero}  f e a b a≈b ()
  scan-fin₂-cong {n = suc n} f e a b a≈b zero = refl
  scan-fin₂-cong {n = suc n} f e a b a≈b (suc j) rewrite a≈b zero
    = scan-fin₂-cong f (f e (b zero)) (a ∘ suc) (b ∘ suc) (a≈b ∘ suc) j

  -- The scan on Fin-vectors agrees with the scan on initial vectors.
  scan-vecscan₁ : ∀ f e (v : Vec n X) (w : Ar (ι n) X) → (∀ i → v i ≡ w (ι i))
               → scan f e v .proj₁ ≡ Vec.scan f e w .proj₁
  scan-vecscan₁ {#0} f e v w p = refl
  scan-vecscan₁ {suc n} f e v w p
    = scan-vecscan₁ f (f e (v #0)) (tl v) (Vec.tl w) (p ∘ suc)
      ⊡ cong (λ x → Vec.scan f x (Vec.tl w) .proj₁) (cong (f e) (p zero))

  scan-vecscan₂ : ∀ f e (v : Vec n X) (w : Ar (ι n) X) → (∀ i → v i ≡ w (ι i))
               → ∀ i → scan f e v .proj₂ i ≡ Vec.scan f e w .proj₂ (ι i)
  scan-vecscan₂ {#0} f e v w p ()
  scan-vecscan₂ {suc n} f e v w p #0 = refl
  scan-vecscan₂ {suc n} f e v w p (suc i)
    = scan-vecscan₂ f (f e (v #0)) (tl v) (Vec.tl w) (p ∘ suc) i
      ⊡ cong (λ x → Vec.scan f x (Vec.tl w) .proj₂ (ι i)) (cong (f e) (p zero))

  -- The same, as rewriting steps from initial vectors to Fin-vectors.
  scan-fin₁-vec : ∀ f e (w : Ar (ι n) X) → Vec.scan f e w .proj₁ ≡ scan-fin₁ f e (λ i → w (ι i))
  scan-fin₁-vec f e w = sym (scan-vecscan₁ f e _ w (λ _ → refl))

  scan-fin₂-vec : ∀ f e (w : Ar (ι n) X) (i : Fin n)
                → Vec.scan f e w .proj₂ (ι i) ≡ scan-fin₂ f e (λ i → w (ι i)) i
  scan-fin₂-vec f e w i = sym (scan-vecscan₂ f e _ w (λ _ → refl) i)

-- Monoids with propositional equality, used in Section 5.
record Monoid-≡ : Set₁ where
  infixl 7 _⟨+⟩_
  field
    Carrier  : Set
    _⟨+⟩_    : Op₂ Carrier
    ε        : Carrier
    isMonoid : IsMonoid _≡_ _⟨+⟩_ ε

  open IsMonoid isMonoid public

-- Arithmetic lemmas about scans of Fin-vectors over a monoid.  They capture the
-- re-bracketing needed for the split and flat cases of the stability proofs.
module FinScanLemmas (M : Monoid-≡) where
  open FinVec using (scan-fin₁; scan-fin₂; scan-fin₁-cong; scan-fin₂-cong;
                    scan-fin₁-vec; scan-fin₂-vec)
  open I using (ι; _⊗_; Ar)
  open Monoid-≡ M
    hiding (trans; sym; refl)
    renaming (Carrier to C; assoc to ⟨+⟩-assoc)

  quotRem-combine : ∀ {n k} (x : Fin n) y → quotRem {n} k (combine x y) ≡ (y , x)
  quotRem-combine {n}{k} x y = cong swap $ remQuot-combine x y

  -- Carries
  scan-fin₁-rec : ∀ {n} → (e : C) → (v : Fin n → C)
          → scan-fin₁ _⟨+⟩_ e v
            ≡ e ⟨+⟩ scan-fin₁ _⟨+⟩_ ε v
  scan-fin₁-rec {n = 0} e v = sym $ identityʳ _
  scan-fin₁-rec {n = suc n} e v
     rewrite scan-fin₁-rec {n = n} (e ⟨+⟩ v zero) (v ∘ suc)
           | scan-fin₁-rec {n = n} (ε ⟨+⟩ v zero) (v ∘ suc)
           | identityˡ (v zero)
     = ⟨+⟩-assoc _ _ _

  -- Scanning a vector of length m + n splits into scanning both parts.
  scan-fin₁-split :
    ∀ {m n} → (a : Fin (m + n) → C) (e : C)
            → scan-fin₁ _⟨+⟩_ e a
              ≡ (scan-fin₁ {n = m} _⟨+⟩_ e (λ i → a (i Fin.↑ˡ n)))
                ⟨+⟩ (scan-fin₁ {n = n} _⟨+⟩_ ε (λ j → a (m Fin.↑ʳ j)))
  scan-fin₁-split {m = 0}     a e = scan-fin₁-rec e a
  scan-fin₁-split {m = suc m} a e = scan-fin₁-split {m = m} (a ∘ suc) (e ⟨+⟩ a zero)

  -- Scanning a vector of length m * n is the same as scanning its m chunks of
  -- length n and then scanning the carries of the chunks.
  scan-fin₁-flat :
    ∀ {m n} → (a : Fin (m * n) → C)
            → scan-fin₁ _⟨+⟩_ ε a
              ≡ scan-fin₁ {n = m} _⟨+⟩_ ε
                   (λ i → scan-fin₁ {n = n} _⟨+⟩_ ε (λ j → a (combine i j)))
  scan-fin₁-flat {m = zero}  a = refl
  scan-fin₁-flat {m = suc m} {n} a
    rewrite identityˡ (scan-fin₁ {n = n} _⟨+⟩_ ε (λ i → a (i Fin.↑ˡ _)))
          | scan-fin₁-rec (scan-fin₁ {n = n} _⟨+⟩_ ε (λ i → a (i Fin.↑ˡ _)))
                          (λ i → scan-fin₁ {n = n} _⟨+⟩_ ε
                                   (λ j → a (n Fin.↑ʳ combine {m} {n} i j)))
    = scan-fin₁-split {m = n} a ε
      ⊡ cong₂ _⟨+⟩_ refl (scan-fin₁-flat {m = m} {n} (λ j → a (n Fin.↑ʳ j)))

  scan-fin₁-⊗ : ∀ {m n} → (a : Ar (ι m ⊗ ι n) C)
              → scan-fin₁ {n = m * n} _⟨+⟩_ ε
                   (λ i → a (ι (proj₂ (quotRem _ i)) ⊗ (ι (proj₁ (quotRem {m} n i)))))
                ≡ scan-fin₁ _⟨+⟩_ ε
                   (λ i → scan-fin₁ _⟨+⟩_ ε (λ j → a (ι i ⊗ ι j)))
  scan-fin₁-⊗ {zero} {n} a = refl
  scan-fin₁-⊗ {suc m} {n} a
    rewrite scan-fin₁-split {m = n} {m * n}
              ((λ i → a (ι (proj₂ (quotRem n i))
               ⊗ (ι (proj₁ (quotRem {suc m} n i)))))) ε
          | identityˡ (scan-fin₁ _⟨+⟩_ ε
                       (λ j → a (ι zero ⊗ ι j)))
          | scan-fin₁-rec
              (scan-fin₁ _⟨+⟩_ ε (λ j → a (ι zero ⊗ ι j)))
              (λ i → scan-fin₁ _⟨+⟩_ ε (λ j → a (ι (suc i) ⊗ ι j)))
          | sym (scan-fin₁-⊗ {m}{n} (λ {(ι i ⊗ j) → a (ι (suc i) ⊗ j)}))
    =
      cong₂ _⟨+⟩_
       (scan-fin₁-cong {n = n} _⟨+⟩_ ε     _ _ first-chunk)
       (scan-fin₁-cong {n = m * n} _⟨+⟩_ ε _ _ other-chunks)
    where
      -- Positions in the first chunk and in the remaining ones.
      first-chunk : _
      first-chunk i rewrite Fin.splitAt-↑ˡ n i (m * n) = refl

      other-chunks : _
      other-chunks i rewrite Fin.splitAt-↑ʳ n _ i = refl

  -- Scanned elements

  scan-fin₂-ε : ∀ {n} → (v : Fin n → C) (e : C)
              → ∀ i → scan-fin₂ _⟨+⟩_ e v i ≡ e ⟨+⟩ (scan-fin₂ _⟨+⟩_ ε v) i
  scan-fin₂-ε {zero} v e = λ ()
  scan-fin₂-ε {suc n} v e zero = sym $ identityʳ _
  scan-fin₂-ε {suc n} v e (suc i)
     rewrite scan-fin₂-ε (v ∘ suc) (e ⟨+⟩ v zero) i
           | scan-fin₂-ε (v ∘ suc) (ε ⟨+⟩ v zero) i
           | identityˡ (v zero)
     = ⟨+⟩-assoc _ _ _

  scan-fin₂-inj : ∀ {m n} → (v : Fin (m + n) → C) (e : C) (j : Fin m)
                → scan-fin₂ _⟨+⟩_ e (λ t → v $ (t Fin.↑ˡ n)) j
                  ≡ scan-fin₂ _⟨+⟩_ e v (j Fin.↑ˡ n)
  scan-fin₂-inj {n} v e zero = refl
  scan-fin₂-inj {n} v e (suc j) = scan-fin₂-inj (v ∘ suc) (e ⟨+⟩ v zero) j

  scan-fin₂-raise : ∀ {m n} → (v : Fin (m + n) → C) (e : C)
      → ∀ (i : Fin n)
      → scan-fin₂ {n = n} _⟨+⟩_
                  (scan-fin₁ _⟨+⟩_ e (λ t → v $ (t Fin.↑ˡ n)))
                  (λ t → v $ (m Fin.↑ʳ t)) i
        ≡ scan-fin₂ _⟨+⟩_ e v (m Fin.↑ʳ i)
  scan-fin₂-raise {zero} {n} v e i = refl
  scan-fin₂-raise {suc m} v e i = scan-fin₂-raise (v ∘ suc) (e ⟨+⟩ v zero) i

  scan-fin₂-⊗ : ∀ {m n} → (v : Fin (m * n) → C)
              → (i : Fin m) (j : Fin n)
              → scan-fin₂ _⟨+⟩_ ε
                   (λ t → scan-fin₁ _⟨+⟩_ ε (λ u → v (combine t u))) i
                ⟨+⟩
                scan-fin₂ _⟨+⟩_ ε (λ t → v (combine i t)) j
                ≡
                scan-fin₂ _⟨+⟩_ ε v (combine i j)
  scan-fin₂-⊗ {suc m} {n} v zero j
    = trans (identityˡ _) (scan-fin₂-inj v ε j)
  scan-fin₂-⊗ {suc m} {n} v (suc i) j
    rewrite (sym $ scan-fin₂-raise {n} v ε (combine i j))
          | scan-fin₂-ε (λ t → v $ (n Fin.↑ʳ t))
                        (scan-fin₁ _⟨+⟩_ ε λ t → v $ (t Fin.↑ˡ (m * n)))
                        (combine i j)
          | scan-fin₂-ε (λ t → scan-fin₁ _⟨+⟩_ ε (λ u → v $ (n Fin.↑ʳ combine t u)))
                        (ε ⟨+⟩ scan-fin₁ _⟨+⟩_ ε (λ t → v $ (t Fin.↑ˡ (m * n))))
                        i
          | identityˡ (scan-fin₁ _⟨+⟩_ ε (λ t → v $ (t Fin.↑ˡ (m * n))))
    = trans (⟨+⟩-assoc _ _ _) (cong₂ _⟨+⟩_ refl (scan-fin₂-⊗ {m}{n} (v ∘ (n Fin.↑ʳ_)) i j))

  scan-fin₂-flat : ∀ {m n} → (a : Ar (ι m ⊗ ι n) C)
      → (ix : Fin (m * n))
      → scan-fin₂ _⟨+⟩_ ε
            (λ t → a (ι (proj₂ (quotRem n t)) ⊗ ι (proj₁ (quotRem {m} n t)))) ix
        ≡ scan-fin₂ _⟨+⟩_ ε
            (λ t → scan-fin₁ _⟨+⟩_ ε (λ u → a (ι t ⊗ ι u)))
          (proj₂ (quotRem n ix))
          ⟨+⟩
          scan-fin₂ _⟨+⟩_ ε (λ t → a (ι (proj₂ (quotRem n ix)) ⊗ ι t))
          (proj₁ (quotRem {m} n ix))
  scan-fin₂-flat {m}{n} a ix
    rewrite sym $ Fin.combine-remQuot {m} n ix
          | quotRem-combine {m} (proj₂ (quotRem n ix)) (proj₁ (quotRem {m}n ix))
          | sym $ scan-fin₂-⊗ {m}{n}
                    (λ t → a (ι (proj₂ (quotRem n t)) ⊗ ι (proj₁ (quotRem{m} n t))))
                    (proj₂ (quotRem n ix)) (proj₁ (quotRem {m}n ix))
    = cong₂ _⟨+⟩_
        (scan-fin₂-cong {n = m} _⟨+⟩_ ε _ _ carries≡ (proj₂ (quotRem n ix)))
        (scan-fin₂-cong {n = n} _⟨+⟩_ ε _ _ row≡ (proj₁ (quotRem {m} n ix)))
    where
      carries≡ : _
      carries≡ i = (scan-fin₁-cong {n = n} _⟨+⟩_ ε _ _
               (λ j → cong₂ (λ t u → a (ι t ⊗ ι u))
                 (cong proj₂ (quotRem-combine i j))
                 (cong proj₁ (quotRem-combine i j))))

      row≡ : _
      row≡ i = cong₂ (λ t u → a (ι t ⊗ ι u))
               (cong proj₂ (quotRem-combine {m} (proj₂ (quotRem n ix)) i))
               (cong proj₁ (quotRem-combine {m} (proj₂ (quotRem n ix)) i))
