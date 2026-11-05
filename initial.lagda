\begin{code}[hide]
open import Data.Nat
open import Data.Fin using (Fin; zero; suc)
open import Data.Product as Prod hiding (map; zipWith)
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function

open import array

module _ where
\end{code}

\subsection{Models\label{sec:models}}

The array theory of Section~\ref{sec:arrtheory} imposes only the essential
constraints needed for the subsequent reasoning, thereby accommodating a broad
spectrum of models.  To illustrate this flexibility we sketch several
alternatives (omitting the isomorphism proofs). Firstly, we can represent
shapes as lists of natural numbers, and we can represent arrays as
(shape-indexed) free monads of the \AD{Vec} type from Agda's standard library:
\begin{code}[hide]
module Ten where
  open import Data.List
  open import Data.Vec hiding ([_]; _++_)
  open import Data.List.Relation.Unary.All

  private variable
    s p : List ℕ
    m n : ℕ
\end{code}
\begin{mathpar}
\codeblock{\begin{code}
  data Tensor (X : Set) : List ℕ → Set where
    pure  : X → Tensor X []
    roll  : Vec (Tensor X s) n → Tensor X (n ∷ s)
\end{code}}
\end{mathpar}
Putting this together we have a model:
\[
\AR{S} = \AD{List}\ \AD{ℕ}; \AR{P} = \AD{All}\ \AD{Fin}; \AR{ι} = \AF{[\_]}; \AR{\_⊗\_} = \AF{\_++\_};
\AR{Ar}\ \AB{s}\ \AB{X} = \AD{Tensor}\ \AB{X}\ \AB{s}.
\]
This model corresponds to the familiar encoding of multi-dimensional arrays as
nested lists (or vectors) in functional languages, such as lists of lists of
lists for three-dimensional data.

As another example, let us consider a flat vector model:
\[
\AR{S} = \AD{ℕ}; \AR{P} = \AF{Fin}; \AR{ι} = \AF{id}; \AR{\_⊗\_} = \AF{\_*\_};
\AR{Ar}\ \AB{n}\ \AB{X} = \AD{Fin}\ \AB{n} \to \AB{X}.
\]
Shapes
are natural numbers (tree structure is not preserved), positions are
offsets given by \AF{Fin}, the shape product is a multiplication of natural
numbers, and arrays are stored as functions.  This model mirrors the flat,
row-major storage used by most array libraries, where a multi-dimensional
array is a single contiguous buffer accessed through computed offsets; arrays
as functions from offsets also correspond to the delayed (or pull) arrays found
in embedded array languages.

A more traditional representation of vectors can be achieved by
choosing a model where arrays are stored as cons lists (again using the
standard library's \AD{Vec}):
\[
\AR{S} = \AD{ℕ}; \AR{P} = \AF{Fin}; \AR{ι} = \AF{id}; \AR{\_⊗\_} = \AF{\_*\_};
\AR{Ar}\ \AB{n}\ \AB{X} = \AD{Vec}\ \AB{X}\ \AB{n}
\]
This is the representation of choice when data is consumed sequentially, for
example when arrays are produced or traversed as streams.

We can also encode less obvious choices as a model of the array theory:
in high-performance computing it is often beneficial to use compressed
formats, where arrays do not store zeroes, \eg{} for sparse matrices arising
in scientific computing or graph algorithms. In this case, for \AB{X} with
decidable equality, an array can be encoded by three components: a default
element that is not stored (zero); a strictly increasing list of the positions
(ordered, for example, by their row-major offsets) at which the array holds
non-default elements; and a list of the elements stored at these positions.
The element at a listed position is the corresponding stored value, and the
element at any other position is the default one.  Decidable equality of
\AB{X} is needed to construct such an array from a function: we only store
the elements that differ from the default.

The multitude of possible models suggests that it would be advantageous to
identify a universal model in which we can develop our constructions and
subsequently transfer them to all other models.  Such a model is presented in
the following subsection.  Note that only constructions transfer, not proofs,
as we discuss in Section~\ref{sec:initiality}.

\subsubsection{\label{sec:initial}Initial model}

Let us define a smallest model that satisfies all the equations of the theory.
Following terminology from model theory, we call such a model \emph{initial}.
This model has the property that any expression written in it can be lifted
into any other model of the same theory. Moreover, this lifting is unique up to
isomorphism. We define the initial model for our array theory and we
demonstrate its initiality by defining lifting operations.

Shapes are defined as binary trees where \AC{ι} constructs leaves and \AC{\_⊗\_}
combines two sub-trees into a new one. Positions are predicates over shapes
also given by two constructors: \AC{ι} and \AC{\_⊗\_}. A position for the shape
\AC{ι}\ \AB{n} can be constructed by providing an index of type \AF{Fin}\
\AB{n}. Positions of product shapes can be constructed if positions of the
left- and right-sub-shapes can be constructed. Arrays of shapes \AB{s} with
elements of type \AB{X} are functions from \AF{P}\ \AB{s} into \AB{X}.
\begin{AgdaSuppressSpace}
\begin{code}
module I where
\end{code}
\begin{mathpar}
\codeblock{\begin{code}
  data S : Set where
    ι    : ℕ → S
    _⊗_  : S → S → S
\end{code}}
\and
\begin{code}[hide]
  infixl 5 _⊗_
  private variable
    s p : S
    n : ℕ
\end{code}
\codeblock{\begin{code}
  data P : S → Set where
    ι    : Fin n → P (ι n)
    _⊗_  : P s → P p → P (s ⊗ p)
\end{code}}
\and
\codeblock{\begin{code}
  Ar : S → Set → Set
  Ar s X = P s → X
\end{code}}
\end{mathpar}

Now we use the data types and constructors introduced above to define the model
that we call \AF{A}.  We omit the definition for \AF{ι-↔}, \AF{⊗-↔}, \AF{Ar-↔}
as they hold trivially.
\begin{mathpar}
\codeblock{\begin{code}
  A : Array
  A .Array.S    = S
  A .Array.P    = P
\end{code}}
\and
\codeblock{\begin{code}

  A .Array.ι    = ι
  A .Array._⊗_  = _⊗_
\end{code}}
\and
\codeblock{\begin{code}

  A .Array.Ar   = Ar
\end{code}
\begin{code}[hide]
  A .Array.ι-↔ = mk↔ {to = λ { (ι i) → i }}{ι} ((λ { refl → refl }) , λ { {ι _} {_} refl → refl })
  A .Array.⊗-↔ = mk↔ {to = λ { (i ⊗ j) → i , j }}{λ { (i , j) → i ⊗ j }}
                     ((λ {refl → refl}) , λ { {i ⊗ j} {_} refl → refl})

  A .Array.Ar-↔ = mk↔ {to = id}{id} ((λ refl → refl) , λ refl → refl)

  open ArOps A public
\end{code}}
\end{mathpar}
\end{AgdaSuppressSpace}
Note that we place these definitions in the module named \AM{I}, obtaining a
namespace that we will use to refer to initial shapes, positions, \etc{} in
other contexts.


\subsubsection{Initiality\label{sec:initiality}}
We show that expressions defined within the initial model can be lifted into
any other model that we denote \AB{A}. As before, we put all the lifting
operations into the module called \AM{FromInit} that is parametrised by \AB{A}.

Firstly, we define the operation \AF{⟦\_⟧s} which lifts initial shapes (of type
\AF{I.S}) into the shapes defined in \AB{A} (of type \AR{S}).
\begin{AgdaSuppressSpace}
\begin{code}
module FromInit (A : Array) where
\end{code}
\begin{code}[hide]
  open Array A; open ArOps A

  private variable
    X : Set
\end{code}
\begin{mathpar}
\codeblock{\begin{code}
  ⟦_⟧s : I.S → S
  ⟦ I.ι n   ⟧s  = ι n
  ⟦ s I.⊗ p ⟧s  = ⟦ s ⟧s ⊗ ⟦ p ⟧s
\end{code}}
\end{mathpar}
\end{AgdaSuppressSpace}
Note that in general we cannot translate \AR{S} shapes into \AF{I.S} shapes
because \AR{S} may contain shapes that are not representable in \AF{I.S}.
Also, for most of the models, \AF{⟦\_⟧s} is not going to be injective, \eg{}
take \AR{S} to be \AD{ℕ} and \AR{⊗} to be \AF{*}.  This is why constructions
can be transferred from the initial model into \AB{A}, but proofs cannot: a
property of the initial model, such as every shape being built from \AC{ι} and
\AC{\_⊗\_}, need not hold in \AB{A}.  Properties of transferred constructions
have to be lifted explicitly, as we do in Sections~\ref{sec:reshaping}
and~\ref{sec:reshape-stable}.

Next, \AF{⟦\_⟧p} translates initial positions (of type \AF{I.P} \AB{s}) into
positions in the model \AB{A} (of type \AR{P}) of lifted shapes
(\AF{⟦} \AB{s} \AF{⟧s}).  As translated positions are of a lifted shape,
we can define an inverse of \AF{⟦\_⟧p} that we call \AF{⟦\_⟧p′}.
\begin{mathpar}
\codeblock{\begin{code}
  ⟦_⟧p : ∀ {s} → I.P s → P ⟦ s ⟧s
  ⟦ I.ι   i ⟧p  = φ i
  ⟦ i I.⊗ j ⟧p  = ⟦ i ⟧p ⊛ ⟦ j ⟧p
\end{code}}
\and
\codeblock{\begin{code}
  ⟦_⟧p′ : ∀ {s} → P ⟦ s ⟧s → I.P s
  ⟦_⟧p′ {I.ι n}    i  = I.ι (ψ i)
  ⟦_⟧p′ {s I.⊗ p}  i  = ⟦ fst i ⟧p′ I.⊗ ⟦ snd i ⟧p′
\end{code}}
\end{mathpar}

Finally, \AF{⟦\_⟧a} lifts initial arrays of initial shapes into arrays
of lifted shapes.  Similarly to position lifting, \AF{⟦\_⟧a} has an
inverse \AF{⟦\_⟧a′} from the arrays of \emph{lifted} shapes.
\begin{mathpar}
\codeblock{\begin{code}
  ⟦_⟧a : ∀ {s} → I.Ar s X → Ar ⟦ s ⟧s X
  ⟦ a ⟧a = imap λ i → a ⟦ i ⟧p′
\end{code}}
\and
\codeblock{\begin{code}
  ⟦_⟧a′ : ∀ {s} → Ar ⟦ s ⟧s X → I.Ar s X
  ⟦_⟧a′ a i = a [ ⟦ i ⟧p ]
\end{code}}
\end{mathpar}

We show that array and position lifting are inverses by proving the
following four equalities\footnote{Agda struggles to infer hidden
variables \AB{s} in some cases, so in the actual code we have to
supply them explicitly, but we omit them here for readability.}:
\begin{mathpar}
\AF{⟦ ⟦ \AB{i} ⟧p ⟧p′}\ \AF{≡}\ \AB{i}
\and
\AF{⟦ ⟦ \AB{i} ⟧p′ ⟧p}\ \AF{≡}\ \AB{i}
\and
\AF{⟦ ⟦ \AB{a} ⟧a ⟧a′}\ \AF{I.≈ₐ}\ \AB{a}
\and
\AF{⟦ ⟦ \AB{a} ⟧a′ ⟧a}\ \AF{≈ₐ}\ \AB{a}
\end{mathpar}


\begin{code}[hide]
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
\end{code}
