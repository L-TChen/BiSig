%!TEX root = BiSig.tex

\documentclass[BiSig.tex]{subfiles}


%include agda.fmt

%format ` = "\text{\textasciigrave}"
%format `n = ` n
%format `_ = ` _
%format ^ = "\hat{}"
%format Γ' = "\iden{" Γ "^\prime}"
%format r' = "\iden{" r "^\prime}"
%format x' = "\iden{" x "^\prime}"
%format ⦃  = "\{\kern-.9pt\vrule width .75pt height 7.125pt depth 1.975pt\kern-1.5pt"
%format ⦄  = "\kern-1.5pt\vrule width .75pt height 7.125pt depth 1.975pt\kern-.9pt\}"
%format ℓ' = "\iden{" ℓ "^\prime}"
%format ℓ′ = "\iden{" ℓ "^\prime}"
%format ℓ'' = "\iden{" ℓ "^{\prime\prime}}"

%format (DIR(t)) = "\dir{" t "}"

\begin{document}

\section{Formalisation} \label{sec:formalisation}
As we have mentioned in \Cref{sec:intro}, our theory was initially developed with \Agda using \AxiomK and has been later translated into the mathematical vernacular.
While the translation is reasonably straightforward, understanding the design of the formalisation itself could pose some difficulty.
If the reader is already comfortable with the informal theory presented so far and assured by the existence of its formalisation, they may choose to skip this section.

\paragraph{Revisiting language formalisation frameworks}
Unlike prior frameworks~\citep{Allais2021,Fiore2022,Ahrens2022} that have primarily focused on meta-properties centred around substitution and term traversal for intrinsically-typed terms, our theory of bidirectional type synthesis does not require term substitution but structural induction for extrinsically-typed terms.
The formal definitions of extrinsic typing in bidirectional type systems, including bidirectional typing derivations and mode derivations, are more complex than their intrinsic counterparts.
For a specific language such as \PCF, \citet{Wadler2022} noted that `extrinsically-typed terms require about 1.6 times as much code as intrinsically-typed' for their formalisation of type safety.
Take the formal type-theoretic definition of typing derivations $\Gamma \vdash_{\Sigma, \Omega} \isTerm{t} : A$ (\Cref{fig:extrinsic-typing}) as an example.
Its intrinsic definition consists of of just one family of sets of intrinsically-typed terms indexed by $A$ and $\Gamma$, but its extrinsic counterpart is a generic family of sets indexed by additionally a generic raw term $t$, involving constructions of two different layers.

\paragraph{Category-theoretic analysis of well-typed terms}
\citet{Fiore1999}{'s} theory of abstract syntax and variable binding forms the foundation of \citet{Fiore2022}'s framework and inspires frameworks by \citet{Allais2021,Ahrens2022}. 
We may sketch the idea of their analysis as follows.
The set of (untyped) abstract syntax trees for a language can be understood as
\begin{enumerate*}
  \item a family of sets $\Term_{\Gamma}$ of well-scoped terms under a context~$\Gamma$ with
  \item variable renaming for a function $\sigma\colon \Gamma \to \Delta$ between variables acting as a functorial map from $\Term_{\Gamma}$ to $\Term_{\Delta}$, i.e.\ a presheaf $\Term\colon \mathbb{F} \to \mathsf{Set}$, and
  \item an \emph{initial} algebra $[\mathsf{v}, \mathsf{op}]$ on~$\Term$ given by the variable rule as a map $\mathsf{v}$ from the presheaf $V\colon \mathbb{F} \hookrightarrow \mathsf{Set}$ of variables to $\Term$ and other constructs as $\mathsf{op}\colon \mathbb{\Sigma}\Term \to \Term$ where $\mathbb{F}$ is the category of contexts, the functor $\mathbb{\Sigma}\colon \mathsf{Set}^\mathbb{F} \to \mathsf{Set}^\mathbb{F}$ encodes the binding arities of constructs, and the initiality amounts to structural recursion, i.e.\ \emph{term traversal}.
\end{enumerate*}
Substitution is modelled as some monoid multiplication with the notion of strength and a suitable monoidal structural on the category of presheaves.
To put it succinctly, it is the free $\mathbb{\Sigma}$-monoid over the presheaf~$V$ of variables.

\paragraph{Type-theoretic construction of well-typed terms}
Fortunately, in type theory, constructing the initial algebra of well-typed terms boils down to defining an inductive type with a few constructors that align primitive rules (such as $\Rule{Var}$) and a rule schema; term traversal can be defined by as usual pattern matching for the inductive type~\citep{Fiore2022}.

\paragraph{Whither a theory of extrinsic typing?}
In \citep{Fiore1999} or existing frameworks, extrinsic typing is not studied.
Our formalisation is inspired by \varcitet{Hermida1998}{'s} interpretation of structural induction as algebras on the category of predicates, viewing extrinsic definitions as endofunctors on the category of predicates.
However, a category-theoretic analysis of our formal constructions in line with \varcitet{Fiore1999}{'s} theory requires proficiency in category theory, which falls outside the scope of this paper.

As such, in this section, we will merely provide an overview of our design and explain the construction of simple types in \Cref{subsec:formal-simple-types} and bidirectional typing rules in \Cref{subsec:formal-extrinsic-typing} intuitively.
On the other hand, the formal proofs closely mirror their informal description presented so far, thus we will only illustrate the `if' part of \Cref{lem:soundness-completeness} as an example in \Cref{subsec:formal-proofs}. 

\subsection{Defining Simple Types}\label{subsec:formal-simple-types}

We begin the formal definition of signatures and simple types (\Cref{def:simple-signature}):
\begin{figure}[H]
  \small
  \begin{minipage}[t]{.45\textwidth}
    \begin{code}
record Desc : Set₁ where
  field
    Op         :  Set
    ⦃ decEq ⦄  :  DecEq Op
    rules      :  Op → ℕ
    \end{code}
  \end{minipage}
  \begin{minipage}[t]{.45\textwidth}
    \begin{code}
⟦_⟧ : Desc → Set → Set
⟦ D ⟧ X = Σ[ i ∈ D .Op ] X ^ (D .rules i)

data Ty (Ξ : ℕ) : Set where
  `_   : Fin Ξ         → Ty Ξ
  op   : ⟦ D ⟧ (Ty Ξ)  → Ty Ξ
    \end{code}
  \end{minipage}
\end{figure}
This definition mirrors our informal counterpart, with the exception of |⟦ D ⟧| for a signature~|D|.
As we are defining simple types inductively, the arity |(rules o)| is intended to denote the number of |Ty| arguments, referring back to what we are in the process of defining.
To circumvent this self-reference, we first define |⟦ D ⟧| on an arbitrary |Set| rather than |Ty| itself.
Consequently, the inductive type of types specified by a signature can be defined using two constructors, |`_| and |op|.
A variable is represented by |`n| for some inhabitant |n| of the type |Fin Ξ| of natural numbers less than~|Ξ|.
Each inhabitant |op (i , ts)| consists of an operation symbol |i| and a $n$-tuple |ts|.

From a categorical perspective, |⟦ D ⟧| can be understood as the functor from |Set| to |Set| which maps $X$ to a $O$-indexed coproduct $\sum_{i \in O} X ^ {\arity(o)}$ of products.
The type |Ty| is then the free |⟦ D ⟧|-algebra over the type |Fin Ξ| or the initial algebra for the functor |Fin Ξ + ⟦ D ⟧|.

In short, to define terms by a signature, we define additionally a \emph{signature functor} |⟦ D ⟧|.

\subsection{Defining Raw Terms}\label{subsec:formal-extrinsic-typing}

The following record types represent the type |ArgD| for arguments $[\Delta]A^{\dir{d}}$, the type |ConD| for operations $\biop$, and the type |Desc| for bidirectional binding signatures, respectively, verbatim.
Removing |mode| from these definitions recover the definitions of binding arguments, arities, and signatures.
\begin{figure}[H]
  \small
  \begin{minipage}[t]{.3\textwidth}
  \begin{code}
record ArgD (Ξ : ℕ) : Set
  where
  field
    cxt           : Cxt Ξ
    type          : Ty Ξ
    (DIR(mode))   : Mode
  \end{code}
  \end{minipage}
  \begin{minipage}[t]{.33\textwidth}
  \begin{code}
record ConD : Set where 
  constructor ι
  field
    {vars}       : ℕ
    args         : List (ArgD vars)
    type         : Ty vars
    (DIR(mode))  : Mode
  \end{code}
  \end{minipage}
  \begin{minipage}[t]{.3\textwidth}
   \begin{code}
record Desc : Set₁ where
  field
    Op          : Set
    rules       : Op → ConD
  \end{code} 
  \end{minipage}
\end{figure}
Our raw terms, being well-scoped and indexed by a list $V$ of free variables, requires another definition of a signature functor for their construction.
This involves mapping |Fam| to |Fam|, where |Fam = ℕ → Set| represents the family of sets indexed by a number (representing the number of free variables).
The signature endofunctor for constructing raw terms shares similarities with the signature functor used for defining simple types, but rather than using a single functor, we employ four distinct functors that are defined separately for the extension context, arguments, constructs, and the coproduct indexed by constructs.
Each of these corresponds to a variant of |⟦_⟧|:
\begin{figure}[H]
  \small 
  \begin{minipage}[t]{.52\textwidth}
\begin{code}
⟦_⟧ᵃ   : TExps Ξ  → Fam → Fam
⟦ Δ             ⟧ᵃ   X n  = X (length Δ ʳ+ n)

⟦_⟧ᵃˢ  : ArgsD Ξ  → Fam → Fam
⟦ []            ⟧ᵃˢ  _ _  = ⊤
⟦ (Δ ⊢ A) ∷ Ds  ⟧ᵃˢ  X n  = ⟦ Δ ⟧ᵃ X n × ⟦ Ds ⟧ᵃˢ X n
\end{code}
  \end{minipage}
  \begin{minipage}[t]{.47\textwidth}
\begin{code}
⟦_⟧ᶜ   : ConD  → Fam → Fam
⟦ ι D _  ⟧ᶜ  X    = ⟦ D ⟧ᵃˢ X

⟦_⟧    : Desc  → Fam → Fam
⟦ D      ⟧   X n  = Σ[ i ∈ D .Op ] ⟦ D .rules i ⟧ᶜ X n
\end{code}
  \end{minipage}
\end{figure}
The inductive type of raw terms indexed by a list of free variables can now be defined by 
\begin{figure}[H]
  \small
\begin{code}
data Raw : ℕ → Set where
  `_   : Fin n                  → Raw n
  _∋_  : Ty           → Raw n   → Raw n
  op   : ⟦ D ⟧ Raw n            → Raw n
\end{code}
\end{figure}
and mirrors our informal definition (\Cref{fig:raw-terms}) where |A ∋ t| corresponds to the raw term $t \annotate A$.

\subsection{Defining Extrinsic Bidirectional Typing Derivations}
\begin{figure}[H]
  \small
% bidirectionally typed terms
%Fam : (ℓ′ : Level) (X : R.Fam ℓ) → Set (ℓ ⊔ lsuc ℓ′)
%Fam ℓ′ X = (Γ : Cxt 0) → X (length Γ) → Mode → Ty → Set ℓ′
%
\begin{code}
⟦_⟧ᵃ  : (Δ : TExps Ξ) (X : R.Fam) (Y : (Γ : Cxt 0) → X (length Γ) → Set)
      → TSub Ξ 0 → (Γ : Cxt 0) → R.⟦ Δ ⟧ᵃ X (length Γ) → Set
⟦ []     ⟧ᵃ X Y σ Γ t  = Y Γ t
⟦ A ∷ Δ  ⟧ᵃ X Y σ Γ t  = ⟦ Δ ⟧ᵃ X Y σ ((A ⟨ σ ⟩) ∷ Γ) t

⟦_⟧ᵃˢ  : (D : ArgsD Ξ) (X : R.Fam) (Y : Fam X)
       → TSub Ξ 0 → (Γ : Cxt 0) → R.⟦ eraseᵃˢ D ⟧ᵃˢ X (length Γ) → Set
⟦ []               ⟧ᵃˢ _  _  _  _  _         = ⊤
⟦ Δ ⊢[ d ] A ∷ Ds  ⟧ᵃˢ X  Y  σ  Γ  (x , xs)  =
  ⟦ Δ ⟧ᵃ X (λ Γ' x' → Y Γ' x' d (A ⟨ σ ⟩)) σ Γ x × ⟦ Ds ⟧ᵃˢ X Y σ Γ xs

⟦_⟧ᶜ : (D : ConD) (X : R.Fam) (Y : Fam X) → Fam (R.⟦ eraseᶜ D ⟧ᶜ X)
⟦ ι {Ξ} d B D ⟧ᶜ X Y Γ xs d′ A =
  d ≡ d′ × Σ[ σ ∈ TSub Ξ 0 ] B ⟨ σ ⟩ ≡ A × ⟦ D ⟧ᵃˢ X Y σ Γ xs

⟦_⟧ : (D : Desc) (X : R.Fam) (Y : Fam X) → Fam (R.⟦ erase D ⟧ X)
⟦ D ⟧ X Y Γ (i , xs) d A = ⟦ D .rules i ⟧ᶜ X Y Γ xs d A
\end{code}
\end{figure}
%
\begin{figure}[H]
  \small 
\begin{minipage}[t]{.48\textwidth}
%
%  _⊢_⇐_ _⊢_⇒_
%    : (Γ : Cxt 0) → Raw (length Γ) → Ty → Set
%  Γ ⊢ r ⇐ A  = Γ ⊢ r [ Chk ] A
%  Γ ⊢ r ⇒ A  = Γ ⊢ r [ Syn ] A
%
\begin{code}
mutual
  data _⊢_[_]_ : Fam₀ Raw where

    var : (i : A ∈ Γ)
        → L.index i ≡ j
        → Γ ⊢ (` j) ⇒ A

    _∋_ : (A : Ty)
        → Γ ⊢ r ⇐ A
        → Γ ⊢ (A ∋ r) ⇒ A
\end{code}
\end{minipage}
\begin{minipage}[t]{.48\textwidth}
\begin{code}
    _↑_ : Γ ⊢ r ⇒ B
        → A ≡ B
        → Γ ⊢ r ⇐ A

    op  : ⟦ D ⟧ Raw _⊢_[_]_ Γ rs d A
        → Γ ⊢ op rs [ d ] A
\end{code}
  
\end{minipage}
\end{figure}
\subsection{Formal Proofs: Soundness as an Example}\label{subsec:formal-proofs}

\begin{figure}[H]
  \small
% soundness proof
\begin{minipage}{.48\textwidth}
\begin{code}
mutual

  soundness : Γ ⊢ r [ d ] A  →  Γ ⊢ r ⦂ A
  soundness (var i eq)   = var i eq
  soundness (A ∋ t)      = A ∋ soundness t
  soundness (t ↑ refl)   = soundness t
  soundness (op ts)      =
    op (soundnessᶜ (BD .rules _) ts)

  soundnessᶜ
    : (D : ConD)
    → ⟦ D ⟧ᶜ Raw _⊢_[_]_ Γ rs d A
    → T.⟦ eraseᶜ D ⟧ᶜ Raw _⊢_⦂_ Γ rs A
  soundnessᶜ (ι _ _ Ds) (_ , σ , σ-eq , ts)  =
    σ , σ-eq , soundnessᵃˢ Ds ts
\end{code}
\end{minipage}
\begin{minipage}{.5\textwidth}
\begin{code}
  soundnessᵃˢ
    : (Ds : ArgsD Ξ) 
    → ⟦ Ds ⟧ᵃˢ            Raw _⊢_[_]_  σ Γ rs
    → T.⟦ eraseᵃˢ Ds ⟧ᵃˢ  Raw _⊢_⦂_    σ Γ rs
  soundnessᵃˢ []                  _         =
    tt
  soundnessᵃˢ ((Δ ⊢[ _ ] _) ∷ Ds) (t , ts)  =
    soundnessᵃ Δ t , soundnessᵃˢ Ds ts

  soundnessᵃ
    : (Δ : TExps Ξ) 
    → ⟦ Δ ⟧ᵃ    Raw (λ Γ' r' → Γ' ⊢ r' [ d ] A)  σ Γ r
    → T.⟦ Δ ⟧ᵃ  Raw (λ Γ' r' → Γ' ⊢ r' ⦂ A)      σ Γ r
  soundnessᵃ []       t  = soundness    t
  soundnessᵃ (_ ∷ Δ)  t  = soundnessᵃ Δ t
\end{code}
\end{minipage}

\end{figure}

\end{document}
