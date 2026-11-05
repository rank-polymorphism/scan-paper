\begin{code}[hide]
{-# OPTIONS --rewriting #-}

open import Data.Nat as ℕ
open import Data.Nat.Properties as ℕ
open import Data.Nat.DivMod
open import Data.Fin using (Fin; zero; suc)
open import Data.Product as Prod hiding (map; zipWith; _<*>_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Effect.Monad
open import Function

open import array
open import combinators
open import initial
open import vector
module _ where

Monad = RawMonad

\end{code}

\section{Runtime effects\label{sec:runtime}}
In this section we demonstrate how the runtime properties of \AF{scan} can be
controlled by reshaping the input array.  To make observations we extend our
specification by introducing effects that we expect to appear during actual
execution.  These effects do not interfere with the computations themselves:
once the effects are erased, we recover the original \AF{scan}, so all the
previous results remain applicable.

Effects are introduced via an abstract monad $M$, together with a function
\AF{sync} that traverses~\citep{MCBRIDE_PATERSON_2008} arrays with effects
in $M$:
\begin{code}
module Effectful (M : Set → Set) (isMon : Monad M) 
                 (sync : ∀ {s X} → I.Ar s (M X) → M (I.Ar s X)) where
\end{code}
$M$ is a module parameter, as is the function \AF{sync}, which is the analogue
of \texttt{sequenceA} in Haskell for arrays.  Consequently, all
functions in this module are parametric~\citep{reynolds1983types} in $M$ and
cannot exploit its internal structure.  The only ``interface'' to $M$ consists
of \AF{return}, \AF{\_>>=\_} and \AF{sync}.  By instantiating $M$ as the
identity monad, all effects disappear and we recover the original definition of
\AF{scan}; we prove this formally below.
\begin{code}[hide]
  open I
  open Comb (CanonComb I.A) hiding (scanv)
  open RawMonad isMon hiding (_⊗_; zipWith)
  open Vec hiding (scan)
  private variable
    X Y : Set
    m n : ℕ
    s  : I.S
\end{code}
We work in the initial model, and as before we first define an effectful scan
on vectors and then on arrays of arbitrary rank.  The source of effects is the
binary operation (the first argument of \AF{scan}), which now returns $M\,X$
instead of $X$, and the algorithm must propagate these effects; consequently
the return type of \AF{scan} is wrapped in $M$.

When scanning vectors we propagate effects left-to-right, sharing the
computation of the $i$-th element with that of the $(i+1)$-st:
\begin{code}
  scanv : (X → X → M X) → X → Vec n X → M (X × Vec n X)
  scanv {n = zero }  f e v = return (e , nil)
  scanv {n = suc n}  f e v = do e′      ← f e (hd v)
                                s , v′  ← scanv f e′ (tl v)
                                return (s , cons e v′)
\end{code}
In the rank-polymorphic scan, one-dimensional arrays are handled by \AF{scanv}.
For arrays of product shapes we apply \AF{scan} to all sub-arrays (conceptually
in parallel), then gather the effects produced by these computations using
\AF{sync}.  We bind the partial results to $m$ and $a'$ so that $m$ and $a'$
share the computation.  Next we scan the array of carries $m$ (obtaining $r$
and $m'$) and adjust the sub-arrays of $a'$ with the elements of $m'$ (again
conceptually in parallel) before accumulating all the effects of this
adjustment:
\begin{code}
  scan : (X → X → M X) → X → Ar s X → M (X × Ar s X)
  scan {s = ι n}     f e a = scanv f e a
  scan {s = s ⊗ p}   f e a = do m , a′  ← unzip <$> (sync $ map (scan f e) (nest a))
                                r , m′  ← scan f e m
                                a′′     ← sync $ unnest $ zipWith (map ∘ f) m′ a′
                                return (r , a′′)
\end{code}
Comparing this with the implementation from Section~\ref{sec:gen-scan}, we
have replaced \AK{let}s with \AK{do}s and introduced accumulation of effects
via \AF{sync} in two places.  When $M$ is the identity monad and \AF{sync} is
the identity function, the above definition collapses to the earlier one.
We make this precise by instantiating \AM{Effectful} accordingly (we call the
resulting module \AM{E}) and proving that the effectful \AF{scan} computes the
same results as the initial scan from Section~\ref{sec:init-scan}:
\begin{code}[hide]
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
\end{code}
\begin{code}
  scan-id : ∀ s (f : X → X → X) (e : X) (a : I.Ar s X)
          →  E.scan f e a .proj₁ ≡ IS.scan₁ s f e a
          ×  E.scan f e a .proj₂ ≈ₐ IS.scan₂ s f e a
\end{code}
\begin{code}[hide]
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
\end{code}
The proof proceeds by induction on the shape $s$; the full proof can be found
in the accompanying sources~\citep{paper-src}.

\subsection{Left and right nesting}
To illustrate runtime differences when evaluating arrays of differing shapes,
we define reshapes that convert arbitrary shape trees into left- and
right-nested forms.  Conceptually, this technique of right/left traversals
applied to scans can be found in \citet{Elliott:scan}; however, here we achieve
the alteration of the algorithm by a single reshape, since we have an explicit
handle on the array shape.

First we define a reshape that flattens a shape tree into a singleton shape.
We introduce a function that computes the product of the tree's elements,
denoted \AF{\_♭}, and the corresponding reshape, called \AF{♭ᵣ}:
\begin{code}[hide]
module Reshapes where

  open Rshp I.A
  open I

  private variable
    s p q r : S
\end{code}
\begin{mathpar}
\codeblock{\begin{code}
  _♭ : S → ℕ
  (ι n)    ♭ = n
  (s ⊗ p)  ♭ = s ♭ * p ♭
\end{code}}
\and
\codeblock{\begin{code}
  ♭ᵣ : Reshape s (ι (s ♭))
  ♭ᵣ {ι n}    = eq
  ♭ᵣ {s ⊗ p}  = flat ∙ (♭ᵣ ⊕ ♭ᵣ)
\end{code}}
\end{mathpar}
Next we define a helper reshaping that reassociates shapes consisting of three
sub-shapes.  The definition flattens all three components, applies
associativity of multiplication, and then unflattens the shapes:
\begin{code}
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
\end{code}
With these helpers we can define operations that nest shape trees to the right.
The left-pointing triangle in the notation indicates the leaf direction.
Analogous to flattening, we define the operation on shapes \AF{\_◁} using the
helper \AF{\_◃\_}, which right-nests the first argument while leaving the
second unchanged:
\begin{mathpar}
\codeblock{\begin{code}
  _◃_ : S → S → S
  (ι n)    ◃  q = ι n ⊗ q
  (s ⊗ p)  ◃  q = s ◃ (p ◃ q)
\end{code}}
\and
\codeblock{\begin{code}
  _◁ : S → S
  (ι n) ◁    = ι n
  (s ⊗ p) ◁  = s ◃ (p ◁)
\end{code}}
\end{mathpar}
We lift these functions to reshapes, obtaining \AF{⊗⇒◃ᵣ} and \AF{◁ᵣ} as
follows:
\begin{mathpar}
\codeblock{\begin{code}
  ⊗⇒◃ᵣ : Reshape (s ⊗ p) (s ◃ p)
  ⊗⇒◃ᵣ {ι n}    = eq
  ⊗⇒◃ᵣ {s ⊗ p}  = ⊗⇒◃ᵣ ∙ (eq ⊕ ⊗⇒◃ᵣ) ∙ assocᵣ
\end{code}}
\and
\codeblock{\begin{code}
  ◁ᵣ : Reshape s (s ◁)
  ◁ᵣ {ι n}     = eq
  ◁ᵣ {s ⊗ p }  = ⊗⇒◃ᵣ ∙ (eq ⊕ ◁ᵣ)
\end{code}}
\end{mathpar}

\begin{code}[hide]
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
\end{code}

For left-nested shape trees the code is symmetric:
\begin{mathpar}
\codeblock{\begin{code}
  _▹_   : S → S → S
  s ▹ (ι n)    = s ⊗ ι n
  s ▹ (p ⊗ q)  = (s ▹ p) ▹ q
\end{code}}
\and
\codeblock{\begin{code}
  _▷    : S → S
  (ι n) ▷    = ι n
  (s ⊗ p) ▷  = (s ▷) ▹ p
\end{code}}
\end{mathpar}

\begin{mathpar}
\codeblock{\begin{code}
  ⊗⇒▹ᵣ  : Reshape (s ⊗ p) (s ▹ p)
  ⊗⇒▹ᵣ {s} {ι n}    = eq
  ⊗⇒▹ᵣ {s} {p ⊗ q}  = ⊗⇒▹ᵣ ∙ (⊗⇒▹ᵣ ⊕ eq) 
                           ∙ rev assocᵣ
\end{code}}
\and
\codeblock{\begin{code}
  ▷ᵣ    : Reshape s (s ▷)
  ▷ᵣ {ι n}    = eq
  ▷ᵣ {s ⊗ p}  = ⊗⇒▹ᵣ ∙ (▷ᵣ ⊕ eq)
\end{code}}
\end{mathpar}
\begin{code}[hide]
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
\end{code}
We leave it as an exercise for the reader to verify that the above code indeed
computes the intended nestings; a proof can be found in the paper
source~\citep{paper-src}.  An example application of both functions would be:
\begin{code}
  sample-shape : S
  sample-shape = (ι 2 ⊗ ι 3) ⊗ ((ι 4 ⊗ ι 11) ⊗ (ι 5 ⊗ ι 6) ⊗ ι 7)

  right-nested : sample-shape ◁ ≡ ι 2 ⊗ (ι 3 ⊗ (ι 4 ⊗ (ι 11 ⊗ (ι 5 ⊗ (ι 6 ⊗ ι 7)))))
  right-nested = refl

  left-nested : sample-shape ▷ ≡ (((((ι 2 ⊗ ι 3) ⊗ ι 4) ⊗ ι 11) ⊗ ι 5) ⊗ ι 6) ⊗ ι 7
  left-nested = refl
\end{code}

\subsection{Cost model}
Finally we construct a monad that enables reasoning about the complexity and
parallelism of \AF{scan}.  The monad $M$ combines a writer~\citep{monads} and a
reader.  The writer component counts the number of binary operations performed
during the scan, while the reader component records whether the evaluation
proceeds sequentially or in parallel:
\begin{code}[hide]
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

\end{code}
\begin{mathpar}
\codeblock{\begin{code}
  data Par : Set where
    goPar goSeq : Par
\end{code}}
\and
\codeblock{\begin{code}
  M : Set → Set
  M X = Par → ℕ × X

  return : X → M X
  return x p = 0 , x
\end{code}}
\and
\codeblock{\begin{code}
  _>>=_ : M X → (X → M Y) → M Y
  (m >>= f) p = let n , x = m p
                    m , y = f x p
                in  m + n , y
\end{code}}
\end{mathpar}
The \AF{Par} datatype therefore distinguishes sequential (\AC{goSeq}) from
parallel (\AC{goPar}) execution.  The natural number paired with $X$ in $M$
``carries'' the operation count.  The \AF{return} of $M$ performs no binary
operations, incurring zero cost in either mode; the bind operator \AF{\_>>=\_}
executes its argument in the chosen mode, then runs the resulting function in
the same mode, summing the operation counts of both invocations.
\begin{code}[hide]
  stMon : RawMonad M
  stMon = mkRawMonad M return _>>=_

  open RawMonad stMon hiding (_⊗_; zipWith; return; _>>=_)
\end{code}
We define \AF{sync} to model parallel execution on an idealised CPU with a
fixed number of threads that run in parallel.  Within each thread the code runs
sequentially, and both start-up and synchronisation costs are assumed to be
zero.  Two helper operations, \AF{vpar} and \AF{vseq}, compute respectively the
maximum and the sum of the first projections in a given vector.  Conceptually,
this reflects the idea that the time required to execute $n$ items of work in
parallel is dictated by the slowest item, whereas the time for sequential
execution is simply the sum of the individual runtimes:
\begin{mathpar}
\codeblock{\begin{code}
  vpar : Vec n (ℕ × X) → ℕ × Vec n X
  vpar v  =  fold ℕ._⊔_ 0 (proj₁ ∘ v) 
          ,  proj₂ ∘ v
\end{code}}
\and
\codeblock{\begin{code}
  vseq : Vec n (ℕ × X) → ℕ × Vec n X
  vseq v  =  fold ℕ._+_ 0 (proj₁ ∘ v) 
          ,  proj₂ ∘ v
\end{code}}
\end{mathpar}
We assume our idealised CPU has eight threads.  The scheduling algorithm
for a vector of $n$ work items proceeds as follows.  When executing items in
parallel we split them evenly among the threads and run each sub-vector
sequentially; when executing sequentially we simply process each item in order
and accumulate the total runtime.  For arrays we first flatten them into
vectors and then apply the same strategy:
\begin{mathpar}
\codeblock{\begin{code}
  vsync : Vec n (M X) → M (Vec n X)
  vsync {n} v goPar 
    rewrite m≡m%n+[m/n]*n n 8 ⦃ it ⦄ = let 
      r  ,  q  = vsplit {n % 8} v
      #r ,  r′ = vseq (λ i → r i goSeq)
      #q ,  q′ = vpar λ j → vseq λ i → 
                   vnest {m = n / 8} q i j goSeq
    in #r + #q , vjoin r′ (vunnest λ i j → q′ j i)
  vsync v goSeq = vseq (λ i → v i goSeq)
\end{code}}
\and
\codeblock{\begin{code}
  sync : Ar s (M X) → M (Ar s X)
  sync a p = let
    n , t = vsync (reshape ♭ᵣ a) p
    in n , reshape (rev ♭ᵣ) t
\end{code}}
\end{mathpar}                           
In \AF{vsync} we employ the theorem \AF{m≡m\%n+[m/n]*n} to rewrite the length
$n$ as $n \% 8 + (n / 8) * 8$.  The function \AF{vsplit} then divides the
vector into two parts of lengths $n \% 8$ (the remainder) and $(n / 8) * 8$.
Subsequently \AF{vnest} reshapes the latter into a nested vector of size $n/8
\times 8$.  We run the eight sub-vectors of length $n/8$ in parallel (each
sub-vector is processed sequentially).  The time taken for the remainder is
added to the overall runtime, assuming the slowest thread handles it.  Finally
we reassemble the results using \AF{vjoin} and \AF{vunnest}, which are inverses
of \AF{vsplit} and \AF{vnest}.  With \AF{M}, its monad structure given by
\AF{return} and \AF{\_>>=\_}, and \AF{sync} at hand, we instantiate the module
\AM{Effectful} from the beginning of this section, which gives us the effectful
\AF{scan} for this cost model.

\begin{code}[hide]
  open Effectful M stMon sync
\end{code}
We run \AF{scan} on an array $a$ of natural numbers with shape (\AC{ι} 10
\AC{⊗} \AC{ι} 10 \AC{⊗} \AC{ι} 10), where every entry equals one.  The binary
operation is addition of unit cost, denoted \AF{\_+′\_}, and the neutral
element is zero.
\begin{mathpar}
\codeblock{\begin{code}
  a : Ar (ι 10 ⊗ ι 10 ⊗ ι 10) ℕ
  a = K 1
\end{code}}
\and
\codeblock{\begin{code}
  _+′_ : (a b : ℕ) → M ℕ
  (a +′ b) _ = 1 , a + b
\end{code}}
\end{mathpar}
Helper functions \AF{\#s} and \AF{\#p} compute the cost of scanning
sequentially and in parallel, respectively.  In the sequential case the cost is
the number of binary operations; in the parallel case it is the modelled
runtime, \ie{} the number of operations performed by the slowest thread, summed
over all synchronisation points:
\begin{mathpar}
\codeblock{\begin{code}
  #s : Ar s ℕ → ℕ
  #s a = scan _+′_ 0 a goSeq .proj₁
\end{code}}
\and
\codeblock{\begin{code}
  #p : Ar s ℕ → ℕ
  #p a = scan _+′_ 0 a goPar .proj₁
\end{code}}
\end{mathpar}

We now compare the operation counts for right- and left-nested reshapes of $a$:
\begin{mathpar}
\codeblock{\begin{code}
  _ : #s (reshape ◁ᵣ a) ≡ 3110
  _ = refl 
\end{code}}
\and
\codeblock{\begin{code}
  _ : #s (reshape ▷ᵣ a) ≡ 2210
  _ = refl
\end{code}}
\end{mathpar}
As can be seen, we have a significant difference in operation counts.  For an
array of shape \AB{s}\;\AC{⊗}\;\AB{p}, \AF{scan} scans all the sub-arrays of
shape \AB{p}, recursively scans the carries of shape \AB{s}, and then performs
one operation per element to adjust the sub-arrays.  In the right-nested
variant the recursion descends into the sub-arrays, which together contain all
the $n$ elements, so every level of nesting costs $O(n)$ operations and, with
$O(\log n)$ levels, the total is $O(n\log n)$.  In the left-nested variant the
recursion descends into the array of carries, which shrinks by a constant
factor at every level, so the costs form a geometric series bounded by $O(n)$.
When running the same algorithms in parallel we obtain:
\begin{mathpar}
\codeblock{\begin{code}
  _ : #p (reshape ◁ᵣ a) ≡ 765
  _ = refl
\end{code}}
\and
\codeblock{\begin{code}
  _ : #p (reshape ▷ᵣ a) ≡ 341
  _ = refl
\end{code}}
\end{mathpar}
Parallel execution reduces the modelled runtime of both variants.  However,
parallelism does not remove the additional work of the right-nested variant,
so the left-nested version remains considerably more efficient.

We have illustrated a single runtime model and two reshapes.  Nevertheless, the
effectful rank-polymorphic code defined above permits further performance
engineering by identifying shape structures that best match the execution model
of interest as well as adjusting hardware models.  In general, a monad with
\AF{sync} may prove insufficient; additional properties could be required.
When runtime depends on the actual values stored in arrays, the proposed
monadic approach may need to be extended.  For simple cases one can define
\AF{return} and \AF{\_>>=\_} operations that inspect the values of a
particular element type.  While useful in practice, such operations break the
contract imposed by the monad laws (which our framework does not enforce).  A
more general solution would involve employing a richer effect system for such
modelling.

