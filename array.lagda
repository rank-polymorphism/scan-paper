





\begin{code}[hide]
open import Data.Nat
open import Data.Fin using (Fin; zero; suc)
open import Data.Product as Prod hiding (map)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary
open import Function

module array where

-- Transitivity of equality, written infix for proof chains.
infixl 2 _⊡_
_⊡_ : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
_⊡_ = trans

private variable
  X Y Z : Set
  m n : ℕ

\end{code}
\section{Arrays\label{sec:arrays}}
In array programming the structure of array shapes is of central importance.
The richer the shape structure, the more expressive the array combinators that
can be derived.  Conversely, poorly chosen shape encodings may inhibit
expressivity and reasoning.  To motivate this, we consider definitions of
top-down and bottom-up \emph{shape-directed folds}, which frequently arise in
divide-and-conquer algorithms: they recurse over the shape and reduce an array
one dimension at a time.

We work in a dependently-typed setting and require array types to guarantee
index safety. A natural way to achieve this is to index an array type by its
shape. Shapes are usually represented as a sequence of natural numbers, each
specifying the bound of the index along a particular dimension. The crucial
question, however, is which data structure should be used to represent shapes
so that the definitions of our folds are not obscured by
encoding artefacts.

At first sight, \AD{List} appears to be a sensible choice. Consider the
following abstract array type:
\begin{code}[hide] 
module Section2 where
  open import Data.List

  variable
    s p : List ℕ

  postulate 
  
\end{code}
\begin{mathpar}
\codeblock{\begin{code}
    Ar : List ℕ → Set → Set
\end{code}}
\end{mathpar}
where the first argument denotes the shape and the second argument denotes the
element type. We deliberately omit a concrete representation of the array
itself.

With this definition, a top-down fold can be expressed as
follows:
\begin{code}
  top-down  : (∀ {n s} → Ar ([ n ] ++ s) X → Ar s X) → (Ar [] X → X)
            → ∀ s → Ar s X → X
  top-down  f z []       a  = z a
  top-down  f z (n ∷ s)  a  = top-down f z s (f a)
\end{code}
if we know how to reduce $n$ $s$-shaped arrays into a single $s$-shaped
array (the first argument $f$) and we know how to extract the element
from an array of the empty shape\footnote{Arrays of the empty shape are
scalars: the empty product of index ranges contains exactly one index, so
\AD{Ar}\;\AC{[]}\;\AB{X} is isomorphic to \AB{X} rather than to the unit type.
Note that \AD{Ar}\;\AF{[}\;1\;\AF{]}\;\AB{X} is isomorphic to \AB{X} as well,
but it has rank one.}
(the second argument $z$), then we can
reduce arrays of any shape into $X$ by repeatedly applying\footnote{
In the second equation of \AF{top-down}, the argument \AB{a} has shape (\AB{n} \AC{∷} \AB{s}),
but \AB{f} expects the shape \AF{[} \AB{n} \AF{]} \AF{++} \AB{s}.  However,
the latter normalises to (\AB{n} \AC{∷} \AB{s}), therefore \AB{f} can be
applied to \AB{a}.
} $f$ followed
by a single application of $z$.

The bottom-up case, where we wish to reduce an $s$-shaped array of $n$-element
arrays to an $s$-shaped array, is considerably less straightforward:
\begin{code}
  bottom-up  : (∀ {n s} → Ar (s ++ [ n ]) X → Ar s X) → (Ar [] X → X)
             → ∀ s → Ar s X → X
\end{code}
The difficulty stems from the fact that \AD{List}s are built by pre-pending
elements on the left. Consequently, pattern matching on a list proceeds
left-to-right, whereas a bottom-up fold needs to take the shape apart from the
right. This problem is well known~\citep{SWIERSTRA_2022}; one solution
proposed in the literature~\citep{MCBRIDE_MCKINNA_2004} introduces a view type:
\begin{mathpar}
\codeblock{\begin{code}
  data View : List ℕ → Set where
    []    : View []
    _∷′_  : (s : List ℕ) → (n : ℕ) → View (s ++ [ n ])

  view : (xs : List ℕ) → View xs
\end{code}}
\and
\codeblock{\begin{code}
  {-# TERMINATING #-}
  bottom-up f z s a with view s
  ... | []      = z a
  ... | s ∷′ n  = bottom-up f z s (f a)
\end{code}}
\end{mathpar}
\begin{code}[hide]
  view []        = []
  view (x ∷ xs) with view xs
  ... | []       = [] ∷′ x
  ... | s ∷′ n   = (x ∷ s) ∷′ n
\end{code}
We use \AF{view} to turn the list into the view type, and then
we pattern-match on it.  Agda does not recognise that \AF{bottom-up} is 
terminating, hence we use explicit annotation.  We can
fix this by defining a measure on the length of the shape that
decreases on every recursive call.

Here we can see that representing shapes as \AD{List}s is suboptimal.  Firstly,
view types together with the termination argument would clutter any reasoning
about bottom-up folds, making it considerably more involved than
reasoning about top-down ones.  Secondly, the shape itself \emph{does not} convey
information about the direction of recursion; consequently we must write two
separate definitions, as the direction is dictated by the code rather than by
the data.

Independently of the choice of shape structure, there is a further concern:
even though we have left the representation of arrays abstract, the above
array type is \emph{not} representation-independent, because it commits to a
particular encoding of shapes as \AD{List}s.  Representation independence is
crucial, since the interplay between hardware architecture and algorithm
determines the preferred array storage.  For example, many numerical
problems involve arrays in which large portions of the elements are zero,
giving rise to compressed storage schemes that omit the zeros and traverse only
the non-zero entries.  On systems with hierarchical memory, it is important to
tile arrays into blocks that are stored contiguously in memory.  Hence, we aim
to formulate array types and algorithms orthogonal to the data layout, allowing
the layout to be chosen later according to the specific requirements.

\subsection{Array theory\label{sec:arrtheory}}

In this subsection we propose an alternative approach that avoids the
shortcomings identified above.

We resolve the issue of recursion direction by encoding shapes as binary trees.
In this formulation the shape alone determines whether a fold proceeds
top-down or bottom-up.  A shape thus describes the logical structure of an
array, \ie{} how its elements are grouped, and this structure guides the
recursion.  Note that a shape does not prescribe how the array is laid out in
memory; this is left to the array representation.

\medskip
\begin{center}
\begin{tabular}{p{.45\textwidth}p{.45\textwidth}}
{
\begin{tikzpicture}[
  every node/.style={draw, circle, minimum size=1cm,scale=0.8},
  level distance=1.3cm,
  level 1/.style={sibling distance=3cm},
  level 2/.style={sibling distance=3cm},
  level 3/.style={sibling distance=3cm},
  scale=0.6
]
  \node[fill,circle,minimum size=.1cm] {}
    child {
      node[fill,circle,minimum size=.1cm] {}
      child{
        node[fill,circle,minimum size=.1cm] {}
        child {node {a}}
        child {node {b}}}
      child{ node {c}}}
    child {node {d}};
\end{tikzpicture}
}
&
{
\begin{tikzpicture}[
  every node/.style={draw, circle, minimum size=1cm,scale=0.8},
  level distance=1.3cm,
  level 1/.style={sibling distance=3cm},
  level 2/.style={sibling distance=3cm},
  level 3/.style={sibling distance=3cm},
  scale=0.6
]
  \node[fill,circle,minimum size=.1cm] {}
    child[draw=none] {node {a}}
    child {node[fill,circle,minimum size=.1cm] {}
      child[draw=none] {node {b}}
      child {node[fill,circle,minimum size=.1cm] {}
        child[draw=none] {node {c}}
        child {node {d}}}};
\end{tikzpicture}
}
\end{tabular}
\end{center}
\medskip

A left-nested tree such as $(((a, b), c), d)$---the left diagram---yields a
bottom-up fold, whereas a right-nested tree such as $(a, (b, (c, d)))$---the
right diagram---induces a top-down fold.  Moreover, this
representation can express shapes that cannot be captured by simple lists, for
example $((a,b),(c,d))$.

To connect such trees with array elements, we view arrays as
containers~\citep{containers} whose shapes are binary trees: every shape
determines a set of positions, and an array assigns an element to every
position.  We achieve representation independence
of arrays and shapes by defining a minimalist \emph{array theory}.  In this case we fix
an interface to shapes, indices and arrays; we define some constraints,
but the actual implementation of these structures will be given
by concrete models.  We define our array theory as follows:
\begin{AgdaSuppressSpace}
\begin{mathpar}
\codeblock{\begin{code} %[hide]
record Array : Set₁ where 
  field
\end{code}
\begin{mathpar}
\codeblock{\begin{code}
    S     : Set
    P     : S → Set

    ι     : ℕ → S
    _⊗_   : S → S → S
\end{code}}
\and
\codeblock{\begin{code}
    ι-↔   : P (ι n) ↔ Fin n   
    ⊗-↔   : ∀ {s p} → P (s ⊗ p) ↔ (P s × P p)

    Ar    : S → Set → Set
    Ar-↔  : ∀ {s} → (P s → X) ↔ Ar s X
\end{code}}
\end{mathpar}}
\end{mathpar}
\end{AgdaSuppressSpace}

The theory draws inspiration from container theory~\citep{10.1007/3-540-36576-1_2},
introducing restrictions on the kind of shapes that are allowed,
and generalising the notion of container interpretation.

The theory consists of shapes \AR{S} and positions (indices) \AR{P}
within such shapes.  We require two constructors
for \AR{S}: \AR{ι} which lifts a given
natural number into \AR{S} and 
\AR{\_⊗\_} which builds a shape out of left and right sub-shapes.

Positions \AR{P} of a given shape \AB{s} characterise
all the valid indices into arrays of that shape.
We require two properties of \AR{P}.  Firstly, \AR{ι-↔} 
requires indices of a singleton shape \AR{ι} \AB{n} to be
isomorphic (denoted by \AF{↔}) to
the natural numbers $[0 \dots n)$ which is denoted by the type \AD{Fin} $n$.
Secondly, \AR{⊗-↔} requires
indices of a product shape to be isomorphic to the product
of left and right sub-indices.

For readers familiar with
universes, our theory says that (\AR{S}, \AR{P}) is a
monoidal\footnote{
A universe $(U,\,El)$ with a monoid structure $(U, \epsilon, *)$ that $El$
maps to the monoid (\AF{Set}, \AD{⊤}, \AD{\_×\_}): $El\,\epsilon$ is
\AD{⊤} and $El\,(a * b)$ is $El\,a$ \AD{×} $El\,b$.  Technically, as in
monoidal categories, all of these laws hold up to isomorphism.
} universe where (\AR{ι} 1) is a unit.

\AR{Ar} is a type of arrays and \AR{Ar-↔} requires 
\AR{Ar} of shape \AB{s} to be isomorphic to a function
from indices of shape \AB{s} to array elements.
Note a distinction with the container theory, where
the interpretation of the container (\AB{S}, \AB{P}) for some \AB{X}
is fixed to \AF{Σ} (s : \AB{S}) (\AB{P} \AB{s} → \AB{X}).
Here we only say that \AR{Ar} \emph{has to be} a
representable functor~\citep{SB_1958-1960__5__369_0}
(\ie{} (\AR{Ar} \AB{s}) is isomorphic to (\AR{P} \AB{s} → \AB{X})).
The concrete storage layout is left to the model.

\subsection{\label{sec:arrop}Array operations}

For any array model $A$, we can expand the isomorphisms of
the array theory into operations on shapes, indices, and arrays.
We group these operations into a module that we call \AM{ArOps}
which is parametrised by $A$:
\begin{AgdaSuppressSpace}
\begin{code}
module ArOps (A : Array) where
\end{code}
\begin{code}[hide]
  open Array A
  private variable
    s p l r : S
\end{code}
\begin{mathpar}
\codeblock{\begin{code}
  imap  : (P s → X) → Ar s X
  _[_]  : Ar s X → (P s → X)

\end{code}}
\and
\codeblock{\begin{code}
  φ    : Fin n → P (ι n)
  ψ    : P (ι n) → Fin n

\end{code}}
\and
\codeblock{\begin{code}
  fst  : P (l ⊗ r) → P l 
  snd  : P (l ⊗ r) → P r
  _⊛_  : P l → P r → P (l ⊗ r)
\end{code}}
\end{mathpar}
\end{AgdaSuppressSpace}
The forward direction of the \AR{Ar-↔} isomorphism gives us
a function that we call \AF{imap} (sometimes called
\emph{tabulate}); the backward direction gives us selections into
arrays for which we use a C-like notation \AF{\_[\_]}.
Similarly, when expanding \AR{ι-↔} and \AR{⊗-↔}
we obtain convenient operations on indices: \AF{φ} and \AF{ψ}
which translate between the one-dimensional indices and \AD{Fin} $n$;
\AF{fst} and \AF{snd} project left and right sub-indices from
the index of a product shape; and \AF{\_⊛\_} makes an index
of a product shape from two sub-indices of the corresponding
sub-shapes.
\begin{code}[hide]
  i ⊛ j = Inverse.from ⊗-↔ (i , j)
  φ     = Inverse.from ι-↔
  ψ     = Inverse.to ι-↔
  snd   = proj₂ ∘ Inverse.to ⊗-↔
  fst   = proj₁ ∘ Inverse.to ⊗-↔
  imap  = Inverse.to Ar-↔
  _[_]  = Inverse.from Ar-↔

  private variable
    a b c : Ar s X
\end{code}


\subsubsection{Equality of arrays}
Using selection, we can define the notion of point-wise
equality of two arrays \AF{\_≈ₐ\_} and show that \AF{≈ₐ} is an 
equivalence relation, meaning that \AF{Ar} with \AF{≈ₐ} is a setoid.
Throughout the paper we use the term setoid in its type-theoretic sense: a type
equipped with an equivalence relation, which need not be proof-irrelevant.
\begin{mathpar}
\codeblock{\begin{code}
  _≈ₐ_ : Ar s X → Ar s X → Set
  a ≈ₐ b = ∀ ix → a [ ix ] ≡ b [ ix ]
\end{code}}
\and
\codeblock{\begin{code}
  refl-≈ₐ   : a ≈ₐ a
  sym-≈ₐ    : a ≈ₐ b → b ≈ₐ a
  trans-≈ₐ  : a ≈ₐ b → b ≈ₐ c → a ≈ₐ c
\end{code}}
\end{mathpar}
\begin{code}[hide]
  refl-≈ₐ ix = refl
  sym-≈ₐ a≈b ix = sym (a≈b ix)
  trans-≈ₐ a≈b b≈c ix = trans (a≈b ix) (b≈c ix)
  

  import Relation.Binary.Reasoning.Setoid as EqReasoning

  ≈ₐ-isEquiv : ∀ {s X} → IsEquivalence (_≈ₐ_ {s} {X})
  ≈ₐ-isEquiv = record { refl = refl-≈ₐ ; sym = sym-≈ₐ ; trans = trans-≈ₐ}

  ArSetoid : ∀ {s X} → Setoid _ _
  ArSetoid {s} {X} = record { isEquivalence = ≈ₐ-isEquiv {s} {X}}

  module ArReasoning {s} {X} = EqReasoning (ArSetoid {s} {X})
\end{code}

\begin{code}[hide]
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
\end{code}
