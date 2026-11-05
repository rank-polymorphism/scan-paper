\begin{code}[hide]
{-# OPTIONS --rewriting #-}
open import Data.Nat as ℕ
open import Data.Nat.Properties as ℕ
open import Data.Fin as Fin using (Fin; zero; suc; remQuot; combine; toℕ; quotRem)
open import Data.Fin.Properties as Fin using (remQuot-combine; combine-remQuot; toℕ-combine; toℕ-injective; combine-injectiveˡ; combine-injectiveʳ)
open import Data.Product as Prod hiding (map; zipWith)
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Relation.Binary.PropositionalEquality as Eq hiding ([_])
open import Relation.Binary
open import Algebra

{-# BUILTIN REWRITE _≡_ #-}

open import Function


module combinators where

open import array
open import vector
open import initial

module _ (A : Array) where
  open Array A
  private variable
    X Y Z : Set
    s p : S
    n : ℕ
\end{code}
\section{Defining scan}

% FIXME we should either inline this section or
%       move it into the paper.tex.
\input{vector}

\subsection{\label{sec:comb}Array combinators}
We have seen the definition of \texttt{scan} on vectors (initial
one-dimensional arrays), and now we wish to derive a rank-polymorphic version
for all models.

We express a rank-polymorphic version of \texttt{scan} using a suite of
primitive array combinators such as \texttt{map}, \texttt{zip}, \etc{} In
principle, all of these combinators can be defined in the initial model and
then lifted into the model of interest.  However, doing so may introduce
considerable inefficiency.  As a practical illustration, consider an array
representation that does not store zeroes.  In that case, point-wise summation
of two arrays needs only inspect the non-zero elements of both arrays.  By
contrast, a na\"{\i}ve point-wise summation would traverse the entire index space,
thereby accessing every element of both argument arrays.

To retain representation independence, we abstract over concrete
implementations of the combinators.  We define a record called \AF{Comb}
that specifies the interfaces to array combinators; this record is
parameterised by the array model $A$.  This is analogous to defining a type
class in Haskell, meaning that \emph{different} implementations of the
combinators can be chosen for each array model.  The definition of
\AF{Comb} follows:
\begin{code}
  record Comb : Set₁ where
    field
      K        : X → Ar s X
      map      : (X → Y) → Ar s X → Ar s Y
      nest     : Ar (s ⊗ p) X → Ar s (Ar p X)
      unnest   : Ar s (Ar p X) → Ar (s ⊗ p) X 
      unzip    : Ar s (X × Y) → Ar s X × Ar s Y
      zipWith  : (X → Y → Z) → Ar s X → Ar s Y → Ar s Z
      scanv    : (X → X → X) → X → Ar (ι n) X → X × Ar (ι n) X
\end{code}
\AR{K} returns a constant array whose elements are all equal to its argument;
\AR{map} applies a supplied function to every element of an array;
\AR{nest} and \AR{unnest} convert between arrays of product shapes and
nested arrays; \AR{unzip} and \AR{zipWith} behave like their list-based
counterparts; \AR{scanv} implements \texttt{scan} on rank-one arrays.
Note that \AF{Ar} of a fixed shape constitutes an applicative
functor~\citep{MCBRIDE_PATERSON_2008}, which gives rise to \AR{K}, \AR{map},
\AR{zipWith} and \AR{unzip}.  The \AR{nest}/\AR{unnest} combinators stem from
the monoidal structure of shapes, and \AF{scanv} is specific to our use-case.

At present the array combinators impose no behavioural constraints.
Consequently, different models could choose implementations of the same
combinator that yield divergent results, making it impossible to reason about
the values produced by a generic (model-independent) array expression that
employs these combinators.  We resolve this issue by providing canonical
implementations for the combinators in any model.  These implementations are
collected in the record \AF{CanonComb}, defined as follows:\footnote{We use
copatterns (see
\url{https://agda.readthedocs.io/en/v2.8.0/language/copatterns.html}) to
define the fields of the \AF{CanonComb} record.}
\begin{code}[hide]
module _ (A : Array) where
  open Array A
  open ArOps A
  open Comb
  open FromInit A
\end{code}
\begin{code}
  CanonComb : Comb A
  CanonComb .K x            = imap λ i → x
  CanonComb .map f a        = imap (f ∘ a [_])
  CanonComb .nest a         = imap λ i → imap λ j → a [ i ⊛ j ]
  CanonComb .unnest a       = imap λ i → a [ fst i ] [ snd i ]
  CanonComb .unzip f        = CanonComb .map proj₁ f , CanonComb .map proj₂ f
  CanonComb .zipWith f a b  = imap λ i → f (a [ i ]) (b [ i ])
  CanonComb .scanv f e a    = let s , a′ = Vec.scan f e ⟦ a ⟧a′ in s , ⟦ a′ ⟧a

\end{code}
Note that \AR{scanv} is defined using the implementation given in
Section~\ref{sec:vect}, by lifting the implementation from the initial model.
All canonical combinators compute a function from indices to values, which is
then turned into an actual array by \AF{imap}.

\AF{CanonComb} supplies default implementations of the combinators for
every model, yielding two benefits.  First, any array expression that uses
combinators can be instantiated in any model by employing these defaults.
Second, and more importantly, \AF{CanonComb} endows the combinator
instances with a well-defined semantics.  If a model provides more efficient
implementations for certain combinators, these may be used provided they
preserve the semantics.  To formalise this requirement we introduce the record
\AF{CombOk}, which is parameterised by the array model $A$ and by a
concrete implementation of the combinators for $A$, denoted \AR{Native}.  We
demand that every native combinator compute the same values (as defined by
\AF{\_≈ₐ\_}) as the canonical implementation.
\begin{code}[hide]
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
\end{code}
\begin{code}
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
\end{code}
We prefix native combinators that originate from a parameter with \AR{Native}
and canonical combinators with \AF{Canon}.\footnote{\AF{Canon} is
merely a wrapper for (\AF{CanonComb} \AB{A}).}  The comparison of products
in \AR{unzip-ok} and \AR{scanv-ok} uses \AF{Pointwise}, which takes
two relations (\eg{} $R_{1}$ and $R_{2}$) and relates the first components of a
pair via $R_{1}$ and the second components via $R_{2}$.

Obviously, \AF{CanonComb} satisfies \AF{CombOk} trivially; this is witnessed by
\AF{CanonCombOk} of the following type (the definition is omitted for
brevity):
\begin{code}[hide]
module _ (A : Array) where
\end{code}
\begin{code}
  CanonCombOk : CombOk A (CanonComb A)
\end{code}
\begin{code}[hide]
  CanonCombOk = record
               { K-ok = λ {X} {s} x ix → refl
               ; map-ok = λ {X} {Y} {s} f a ix → refl
               ; nest-ok = λ {s} {p} {X} a ix → refl
               ; unnest-ok = λ {s} {p} {X} a ix → refl
               ; unzip-ok = λ {s} {X} {Y} a → (λ ix → refl) , (λ ix → refl)
               ; zipWith-ok = λ {X} {Y} {Z} {s} f a b ix → refl
               ; scanv-ok = λ {X} {n} f e a → refl , (λ ix → refl)
               }
\end{code}

\subsection{Generalised scan\label{sec:gen-scan}}
We define \texttt{scan} for a given array model \AB{A}, a collection of
combinators \AB{N}, and a proof that the combinators respect the intended
semantics (witnessed by \AB{Ok}) as follows.  The definition of \texttt{scan}
itself does not use \AB{Ok}; we nevertheless make it a parameter so that
\texttt{scan} cannot be instantiated with combinators that are not known to
behave correctly.  This proof is what allows us to reason about \texttt{scan}
in arbitrary models in Section~\ref{sec:init-scan}.
\begin{code}
module Scan (A : Array) (N : Comb A) (Ok : CombOk A N) where
\end{code}
\begin{code}[hide]
  open Array A
  open Comb N
  open FromInit A

  private variable
    X : Set
\end{code}
\begin{mathpar}
\codeblock{\begin{code}
  scan : (s : I.S) → (X → X → X) → X → Ar ⟦ s ⟧s X → X × Ar ⟦ s ⟧s X
  scan (I.ι n)    f e a  = scanv f e a
  scan (s I.⊗ p)  f e a  = let
                             m , a′  = unzip (map (scan p f e) (nest a))
                             r , m′  = scan s f e m
                             a′′     = zipWith (map ∘ f) m′ a′
                           in r , unnest a′′
\end{code}}
\end{mathpar}
\begin{code}[hide]
  scan₁ : ∀ s → (f : X → X → X) → X → Ar ⟦ s ⟧s X → X
  scan₂ : ∀ s → (f : X → X → X) → X → Ar ⟦ s ⟧s X → Ar ⟦ s ⟧s X
\end{code}
Note that \AF{scan} is defined for arrays of the \emph{lifted} shape $s$
(of type \AF{I.S}).  This is necessary because \AF{scan} is defined
inductively on shapes: for singleton shapes we apply \AF{scanv}; for
product shapes we recurse into sub-arrays, scan the array of their
\emph{carries} (the reductions of the sub-arrays, \ie{} the first components
of their scans), and then update the sub-arrays with the scanned carries.  This induction works only if
we can decide whether a shape is a product or a singleton.  In some models this
decision is unavailable (\eg{} when shapes are natural numbers), hence we employ
lifted shapes.

We also provide two projections, \AF{scan₁} and \AF{scan₂}, for the
carry (the reduction of the whole array) and for the scanned array
respectively:
\begin{mathpar}
\codeblock{\begin{code}
  scan₁ s f e a = scan s f e a .proj₁
\end{code}}
\and
\codeblock{\begin{code}
  scan₂ s f e a = scan s f e a .proj₂
\end{code}}
\end{mathpar}

\subsection{Scan at work}
We illustrate the above implementation by applying it to a two-dimensional
array of natural numbers, using addition as the binary operation and $0$ as the
neutral element (Fig.~\ref{fig:scan}).
\begin{figure}[h!]
\centering
\includegraphics[width=\linewidth]{scan.drawio.pdf}
\Description{A data-flow diagram of scan with addition on a 2-by-6 array:
the rows are scanned, giving partial sums and scanned rows; the partial sums
are scanned, giving the overall sum and offsets that are added to the scanned
rows.}
\caption{\label{fig:scan}Application of rank-polymorphic \AF{scan} to 2-dimensional
array of natural numbers.}
\end{figure}
Colours distinguish arrays from operations.  The array \AB{a} (green, top-left)
of shape $(\AC{ι}\,2 \;\AC{⊗}\; \AC{ι}\,6)$ is the input.  It is fed to a
function (purple) that maps \texttt{scan} across the rows of \AB{a} and
\texttt{unzip}s the array of pairs into a pair of arrays.  Solid
arrows indicate inputs to functions; striped arrows indicate outputs.  The
result is a pair (shown in a dotted box, top-right) consisting of partial sums
(carries) and scanned rows.  We denote the projections of this pair by \AB{m}
and \AB{a'} respectively.  Both \AB{m} and \AB{a'} are coloured yellow,
signalling temporary data.  Scanning the partial sums \AB{m} produces a pair
containing the overall sum \AB{r} and a scan of the partial sums \AB{m'}.  The
overall sum \AB{r} is coloured red because it forms the first output of the
whole scan.  Finally, we adjust the rows of \AB{a'} by adding the corresponding
element from \AB{m'} to each row, \ie{} adding $0$ to the first row and $21$ to
the second row.  We transform the nested array into an array of product shape
using \texttt{unnest}.  This adjusted array constitutes the second output of the scan
and is likewise coloured red.


\subsection{Initial scan\label{sec:init-scan}}
%% agda: Stability
\begin{code}[hide]
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
\end{code}  
As \texttt{scan} is defined for all models, it can be instantiated for the
initial model with the canonical combinators:
\begin{mathpar}
\AK{module}\ \AM{IS}\ =\ \AM{Scan}\ \AF{I.A}\ (\AF{CanonComb}\ \AF{I.A})\
     (\AF{CanonCombOk}\ \AF{I.A})
\end{mathpar}

This instance of \texttt{scan} is noteworthy because we can prove that, for any
array model \AB{A} and for any semantically-respecting combinators, the results
computed by \texttt{scan} for that model coincide with those computed by the
initial scan.  Formally:
\begin{mathpar}\codeblock{\begin{code}[hide]
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
  
\end{code}
\begin{code}
  scan-ok : (s : I.S) → (f : X → X → X) → (e : X) → (a : Ar ⟦ s ⟧s X)
          →  scan₁ s f e a   ≡   IS.scan₁ s f e ⟦ a ⟧a′
          ×  scan₂ s f e a   ≈ₐ  ⟦ IS.scan₂ s f e ⟦ a ⟧a′ ⟧a
\end{code}}
\end{mathpar}
In essence, the theorem states that all scans in all models compute the same
values: whenever two models \AB{A} and \AB{B} share the same (lifted) shape and
the same element values, their respective scans produce identical results.  We
prove the theorem by induction on the shape $s$, using the fact that the
combinators respect their intended semantics (\AB{Ok}) to show that the
translation artefacts introduced by moving between models do not affect the
computed values.  The theorem would also follow from the
parametricity~\citep{reynolds1983types} of \texttt{scan} over array models
together with the initiality of the initial model.  However, Agda does not
internalise parametricity, so using this argument would require defining an
embedded language, re-expressing the array theory and combinators within it,
and proving a general parametricity result \`a la
\citet{10.1145/1863543.1863592}.  The direct proof is considerably simpler.

\begin{code}[hide]
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
\end{code}

\section{Reshaping\label{sec:reshaping}}
%% agda: Reshaping
\begin{code}[hide]
module Rshp (A : Array) where
  open Array A; open ArOps A
  private variable
   m n : ℕ
   s p q r : S
   X : Set

  infixl 17 _⊕_
  infixl 15 _∙_
  infixr 16 _⟨_⟩
\end{code}
One common operation on arrays is an element-preserving change of shape that we
call \AF{reshape}. In principle, \AF{reshape} can be regarded as an isomorphism
between the index spaces of two corresponding arrays. However, in many
situations we are interested only in a subset of all possible permutations. In
particular, we frequently consider an equivalence relation on shapes such that
reshapes within the same equivalence class preserve certain operations, for
example \texttt{scan}.

Reshape relations make it possible to achieve this by defining a ``language'' of
shape transformations, each of which induces a permutation of array elements.
The relation presented below captures those reshapes that preserve array
flattening. The reshape relation plays a central role in the stability proof in
Section~\ref{sec:reshape-stable}.

For any array model $A$, \AF{Reshape} is an inductive relation that relates
shapes $s$ and $p$ when the products of these shapes (\ie{} the numbers of
elements in the flattened arrays) are identical.
\begin{code}
  data Reshape : S → S → Set where
    eq     : Reshape s s
    _⊕_    : Reshape s p → Reshape q r → Reshape (s ⊗ q) (p ⊗ r)
    _∙_    : Reshape q p → Reshape s q → Reshape s p
    split  : Reshape (ι (m * n)) (ι m ⊗ ι n)
    flat   : Reshape (ι m ⊗ ι n) (ι (m * n))
\end{code}
The relation is equipped with an identity constructor \AC{eq}, composition
\AC{\_∙\_}, gluing of two individual reshapes into a reshape of a product
\AC{\_⊕\_}, and, most importantly, \AC{split} and \AC{flat} which give rise to
reversible array flattenings.

With the given definition of \AF{Reshape} we can show that it is symmetric:
\begin{code}
  rev : Reshape s p → Reshape p s
  rev eq        = eq
  rev (r ⊕ r₁)  = rev r ⊕ rev r₁
  rev (r ∙ r₁)  = rev r₁ ∙ rev r
  rev split     = flat
  rev flat      = split
\end{code}
Consequently, \AD{Reshape} is an equivalence relation: it is reflexive by
\AC{eq}, symmetric by \AC{rev}, and transitive by \AC{\_∙\_}. Hence
shapes together with \AD{Reshape} form a setoid (in the type-theoretic sense
of Section~\ref{sec:arrop}), allowing us to employ the convenient reasoning
syntax demonstrated in the \AF{leftn} proof below.
\begin{code}[hide]
  import Relation.Binary.Reasoning.Setoid as EqReasoning

  Reshape-isEquiv : IsEquivalence Reshape
  Reshape-isEquiv = record { refl = eq ; sym = rev ; trans = λ f g → g ∙ f}

  ReshapeSetoid : Setoid _ _
  ReshapeSetoid = record { isEquivalence = Reshape-isEquiv }

  module ReshapeReasoning = EqReasoning ReshapeSetoid
\end{code}
A number of interesting shape relations can be derived from the properties of
the natural numbers. As an illustration, consider the relation between a
singleton shape and its product with a singleton \AC{ι} 1. We use \AC{flat} to
turn \AC{\_⊗\_} into multiplication on natural numbers and exploit the
neutrality of multiplication to finalise the definition.
\begin{code}
  leftn : ∀ n → Reshape (ι 1 ⊗ ι n) (ι n)
  leftn n = begin
              ι 1 ⊗ ι n  ≈⟨ flat ⟩
              ι (1 * n)  ≡⟨ cong ι (*-identityˡ _) ⟩
              ι n
            ∎ where open ReshapeReasoning
\end{code}

\AD{Reshape} has the following contra-variant action on indices:
\begin{code}
  _⟨_⟩ : P p → Reshape s p → P s
  i ⟨ eq      ⟩  = i
  i ⟨ r ⊕ r₁  ⟩  = (fst i ⟨ r ⟩) ⊛ (snd i ⟨ r₁ ⟩)
  i ⟨ r ∙ r₁  ⟩  = i ⟨ r ⟩ ⟨ r₁ ⟩
  i ⟨ split   ⟩  = φ $ combine (ψ $ fst i) (ψ $ snd i)
  i ⟨ flat    ⟩  = let a , b = remQuot _ (ψ i) in φ a ⊛ φ b
\end{code}
As can be observed, \AC{eq} has no effect; \AC{\_⊕\_} acts on the corresponding
sub-indices; composition \AC{\_∙\_} applies two actions in sequence; and
\AC{split} and \AC{flat} employ an isomorphism between \AF{Fin}($m$ \AF{*} $n$)
and \AF{Fin} $m$ \AF{×} \AF{Fin} $n$ given by \AF{combine} and \AF{remQuot}.
The function \AF{combine} maps a pair $(i, j)$ to the row-major offset
$i * n + j$, and \AF{remQuot} recovers $i$ and $j$ from an offset $k$ as the
quotient and the remainder of the division of $k$ by $n$.

Finally, \AF{reshape} on arrays is defined by means of selection
on reshaped indices: 
\begin{code}
  reshape : Reshape s p → Ar s X →  Ar p X
  reshape r a = imap λ ix → a [ ix ⟨ r ⟩ ]
\end{code}
We show that reshaping forwards followed by reshaping backwards, and vice
versa, yields the identity, via the following lemmas:
\begin{code}
  ⟨⟩-rev         : (r : Reshape s p) (i : P p) → i ⟨ r ⟩ ⟨ rev r ⟩ ≡ i
  ⟨⟩-rev′        : (r : Reshape s p) (i : P s) → i ⟨ rev r ⟩ ⟨ r ⟩ ≡ i
  rev-reshape-≈  : (r : Reshape s p) (a : Ar s X) → reshape (rev r) (reshape r a) ≈ₐ a
  reshape-rev-≈  : (r : Reshape s p) (a : Ar p X) → reshape r (reshape (rev r) a) ≈ₐ a
\end{code}
The second and the fourth lemmas follow from the first and the third ones, as
\AF{rev} is an involution: \AF{rev} (\AF{rev} \AB{r}) \AD{≡} \AB{r}.
Moreover, we prove that reshapes are congruent: if two arrays contain the same
elements, then reshaping them with a given \AB{r} produces arrays that also
contain the same elements:
\begin{code}
  reshape-cong   : {a b : Ar s X} (r : Reshape s p) → a ≈ₐ b → reshape r a ≈ₐ reshape r b
\end{code}
The proof is immediate: the element of \AF{reshape}\;\AB{r}\;\AB{a} at
index \AB{i} is the element of \AB{a} at index \AB{i}\;\AF{⟨}\;\AB{r}\;\AF{⟩},
which coincides with the element of \AB{b} at the same index.

\begin{code}[hide]
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
\end{code}

Note that \AF{Reshape} is a proof-relevant relation, which means that, in
general, different expressions of the type \AF{Reshape}\;\AB{s}\;\AB{p} may
exhibit distinct actions on indices and arrays.  For the \AF{Reshape} defined
above this situation does not arise, as we prove in
Section~\ref{sec:init-reshapes}.  Intuitively, all reshapes preserve the order
of elements in the flattened array: they only change how these elements are
split into groups, as described by the shape tree.  Consequently, no
\AF{Reshape} can describe the transposition of an array, as transposition
changes the order of elements in the flattened array.

For example, consider the array $\bigl[[1,2,3],[4,5,6]\bigr]$ of shape
(\AC{ι}\;2\;\AC{⊗}\;\AC{ι}\;3). There exists a
\AF{Reshape}\;(\AC{ι}\;2\;\AC{⊗}\;\AC{ι}\;3)\;(\AC{ι}\;3\;\AC{⊗}\;\AC{ι}\;2);
however, its action yields the array $\bigl[[1,2],[3,4],[5,6]\bigr]$ rather
than the desired transposition $\bigl[[1,4],[2,5],[3,6]\bigr]$.

If we were to extend \AF{Reshape} with a \texttt{swap} constructor that
exchanges the left and right components of a product shape, we could define a
transpose operation and, more generally, arbitrary permutations of shape
components.  Note that this still does not capture arbitrary permutations of
array elements, only those induced by permuting the shape.  In that scenario
we would have two reshapes of the same type that behave differently.
Furthermore, \texttt{scan} would no longer be stable under reshapes: swapping changes the order of elements in the
flattened array, so the prefixes of the reshaped array contain different
elements.  For instance, scanning the transposed array above and transposing
the result back yields $\bigl[[0,5,12],[1,7,15]\bigr]$, whereas the scan of the
original array is $\bigl[[0,1,3],[6,10,15]\bigr]$.  This cannot be remedied by
requiring additional properties of the binary operation: commutativity would
only preserve the overall reduction (the carry), but not the scanned elements.
We therefore do not include \texttt{swap} in \AF{Reshape}.

In general, one should envisage many reshape relations---potentially organised
hier\-ar\-chi\-cal\-ly---that serve distinct purposes.  Categorically, shapes and
reshapes (identified up to their action) form a groupoid: \AC{eq} gives
identities, \AC{\_∙\_} gives composition, and \AF{rev} gives inverses.  The
proof-irrelevance of the action of our \AF{Reshape} means that this groupoid
is \emph{thin}: there is at most one morphism between any two shapes, so it
carries no more information than the equivalence relation itself.  Extensions
such as \texttt{swap} break thinness, and statements about such relations have
to refer to particular reshapes rather than to the mere existence of one.



\subsection{Initial reshapes\label{sec:init-reshapes}}
We write \AM{IR} for the reshapes of the initial model, \ie{} the
definitions of this section instantiated with \AF{I.A}.
As with shapes and indices, reshapes within the initial model can be
translated into reshapes within any other model as follows:
\begin{code}
  ⟦_⟧r : IR.Reshape s p → Reshape ⟦ s ⟧s ⟦ p ⟧s
\end{code}
As with indices, translated reshapes act on lifted shapes.

Furthermore, we can show that lifting reshaped arrays is the same as
reshaping lifted arrays with lifted reshapes:
\begin{code}
  reshape-⟦⟧   : (r : IR.Reshape s p) (a : I.Ar s X)
               → ⟦ IR.reshape r a ⟧a ≈ₐ reshape ⟦ r ⟧r ⟦ a ⟧a
  reshape-⟦⟧′  : (r : IR.Reshape s p) (a : Ar ⟦ s ⟧s X)
               → ⟦ reshape ⟦ r ⟧r a ⟧a′ I.≈ₐ IR.reshape r ⟦ a ⟧a′
\end{code}
While this is not surprising, it requires a formal proof, which can be found
in the accompanying sources~\citep{paper-src}.

Finally, we show that the action of lifted reshapes is proof-irrelevant: any two
reshapes between the same shapes act identically on indices, and therefore on
arrays:
\begin{code}
  ⟨⟩-prop       : (r r′ : IR.Reshape s p) (i : P ⟦ p ⟧s)
                → i ⟨ ⟦ r ⟧r ⟩ ≡ i ⟨ ⟦ r′ ⟧r ⟩
  reshape-prop  : (r r′ : IR.Reshape s p) (a : Ar ⟦ s ⟧s X)
                → reshape ⟦ r ⟧r a ≈ₐ reshape ⟦ r′ ⟧r a
\end{code}
We first prove the corresponding property (\AF{IR.⟨⟩-prop}) in the initial
model.  Every initial index has a row-major offset, computed by
\AF{combine}-ing the offsets of its sub-indices.  This mapping is injective, and
a straightforward induction on reshapes shows that every reshape action
preserves offsets.  Hence, \AB{i}~\AF{⟨}~\AB{r}~\AF{⟩} and
\AB{i}~\AF{⟨}~\AB{r′}~\AF{⟩} have the same offset, and thus they are equal.
The lifted version follows by translating indices into the initial model and
back.

\begin{code}[hide]

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
\end{code}


\section{\label{sec:reshape-stable}Reshape independence of scan}
%% agda: Stability
\begin{code}[hide]
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




\end{code}
In this section we demonstrate that \AF{scan} is stable under reshapes; that
is, any reshaping of the input array expressible with \AF{Reshape} has no
effect on the values computed by the \AF{scan}.

We fix a monoid with binary operation \AR{\_⟨+⟩\_} and neutral element
\AR{ε}.  We then prove that initial scans are stable under initial reshapes.
Two theorems are employed: \AF{init-scan₁-ok} ensures that the carries are equal,
whereas \AF{init-scan₂-ok} ensures that the array elements are equal:
\begin{code}
  init-scan₁-ok : (a : Ar s X) (r : Reshape s p)
      → IS.scan₁ p _⟨+⟩_ ε (reshape r a) ≡ IS.scan₁ s _⟨+⟩_ ε a
  init-scan₂-ok : (a : Ar s X) (r : Reshape s p)
      → IS.scan₂ p _⟨+⟩_ ε (reshape r a) ≈ₐ reshape r (IS.scan₂ s _⟨+⟩_ ε a)
\end{code}
Both proofs proceed by induction on the reshape \AB{r}.  For the \AC{eq},
\AC{\_⊕\_} and \AC{\_∙\_} constructors the argument follows straightforwardly from
the inductive hypothesis.  The \AC{split} and \AC{flat} constructors, however,
require additional reasoning, because we must relate the application of the
operation to sub-vectors with the operation applied to the whole vector.
The key lemma states that scanning a vector of length $m * n$ yields the same
carry as scanning each of its $m$ consecutive chunks of length $n$ and then
scanning the resulting $m$ carries; a similar lemma relates the elements of
the scanned vectors.  This is precisely the place where associativity of
\AR{\_⟨+⟩\_} and neutrality of \AR{ε} are needed: the two computations combine
the same elements in the same order, but with a different bracketing.
\begin{code}[hide]
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
\end{code}
Having proven stability for the initial model, we lift it to all models.
The proof concerning carries proceeds as follows.  We invoke
\AF{scan-ok} to convert to an initial scan over lifted arrays; then we
translate lifted reshapes into initial ones using \AF{reshape-⟦⟧′} together
with the congruence of the initial scan (\AF{IS.scan₁-cong}); the stability of initial scans is applied to eliminate the reshaping, and finally
we apply \AF{scan-ok} in reverse:
\begin{code}
  scan-thm₁ : ∀ s p → (a : Ar ⟦ s ⟧s X) (r : IR.Reshape s p)
            → scan₁ p _⟨+⟩_ ε (reshape ⟦ r ⟧r a) ≡ scan₁ s _⟨+⟩_ ε a
  scan-thm₁ s p a r = begin
    scan₁     p _⟨+⟩_ ε (reshape ⟦ r ⟧r a)      ≡⟨ scan-ok p _ _ _ .proj₁ ⟩
    IS.scan₁  p _⟨+⟩_ ε ⟦ reshape ⟦ r ⟧r a ⟧a′  ≡⟨ IS.scan₁-cong _ _ _ _ (reshape-⟦⟧′ r a) ⟩
    IS.scan₁  p _⟨+⟩_ ε (IR.reshape r ⟦ a ⟧a′)  ≡⟨ init-scan₁-ok _ r ⟩
    IS.scan₁  s _⟨+⟩_ ε ⟦ a ⟧a′                 ≡˘⟨ scan-ok s _ _ _ .proj₁ ⟩
    scan₁     s _⟨+⟩_ ε a
    ∎ where open ≡-Reasoning
\end{code}
The proof for arrays follows exactly the same structure as the preceding
theorem, and is therefore omitted:
\begin{code}
  scan-thm₂ : ∀ s p → (a : Ar ⟦ s ⟧s X) (r : IR.Reshape s p)
            → scan₂ p _⟨+⟩_ ε (reshape ⟦ r ⟧r a) ≈ₐ reshape ⟦ r ⟧r (scan₂ s _⟨+⟩_ ε a)
\end{code}
\begin{code}[hide]
  scan-thm₂ s p a r = begin
    scan₂ p _⟨+⟩_ ε (reshape ⟦ r ⟧r a)               ≈⟨ scan-ok p _ _ _ .proj₂  ⟩
    ⟦ IS.scan₂ p _⟨+⟩_ ε ⟦ reshape ⟦ r ⟧r a ⟧a′ ⟧a   ≈⟨ ⟦⟧a-cong (IS.scan₂-cong _ _ _ _ (reshape-⟦⟧′ r a)) ⟩
    ⟦ IS.scan₂ p _⟨+⟩_ ε (IR.reshape r  ⟦ a ⟧a′) ⟧a  ≈⟨ ⟦⟧a-cong (init-scan₂-ok _ r) ⟩
    ⟦ IR.reshape r (IS.scan₂ s _⟨+⟩_ ε ⟦ a ⟧a′) ⟧a   ≈⟨ reshape-⟦⟧ r (IS.scan₂ s _ _ ⟦ a ⟧a′) ⟩
    reshape ⟦ r ⟧r ⟦ IS.scan₂ s _⟨+⟩_ ε ⟦ a ⟧a′ ⟧a   ≈˘⟨ reshape-cong ⟦ r ⟧r
                                                                      (scan-ok s _ _ _ .proj₂) ⟩
    reshape ⟦ r ⟧r (scan₂ s _⟨+⟩_ ε a)
    ∎ where open ArReasoning
\end{code}
As the action of our reshape relation is proof-irrelevant, the choice of a
particular reshape between two given shapes does not matter.  For any two
reshapes \AB{r} and \AB{r′} of type \AD{Reshape}\;\AB{s}\;\AB{p}, scanning the
array \AB{a} reshaped by \AB{r} computes the same results as scanning \AB{a}
reshaped by \AB{r′}; informally,
$\texttt{scan}\,(\AF{reshape}\;\AB{r}\;\AB{a}) \approx
\texttt{scan}\,(\AF{reshape}\;\AB{r′}\;\AB{a})$.  For carries this follows
directly from \AF{scan-thm₁}, which holds for every reshape.  For the scanned
arrays, \AF{scan-thm₂} shows that the two results are the scan of \AB{a}
reshaped by \AB{r} and by \AB{r′} respectively, and these coincide by
\AF{reshape-prop} from Section~\ref{sec:init-reshapes}.  Both statements are
proven in the accompanying sources~\citep{paper-src}.  Note that reshape
relations need not have proof-irrelevant actions in general, so this is not a
general result: it relies on the particular \AD{Reshape} chosen in this paper.
\begin{code}[hide]
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
\end{code}

Our rank-polymorphic specification of \AF{scan} can be viewed as an infinite
family of algorithms, one for each array shape.  The \AD{Reshape} equivalence
partitions shapes into equivalence classes, and the foregoing proof establishes
that \AF{scan} applied to any two shapes within the same class yields identical
results.  In the ``what/how'' metaphor, the \emph{what} remains unchanged whilst the
\emph{how} may be systematically varied through the application of \AF{reshape}.



