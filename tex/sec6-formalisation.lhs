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
As we have mentioned in \Cref{sec:intro}, our theory was initially developed with \Agda.
While the translation to the natural language is reasonably straightforward, understanding the formalisation itself could be difficult.
If the reader is comfortable with the informal presentation and assured by the existence of its formalisation, they may feel free to skip this section.

\paragraph{Revisiting language formalisation frameworks}
Unlike prior frameworks~\citep{Allais2021,Fiore2022,Ahrens2022} that have primarily focused on meta-properties centred around substitution for intrinsically-typed terms, our theory of bidirectional type synthesis does not require term substitution but structural induction for extrinsically-typed terms.
The formal definitions of extrinsic typing are more complex than their intrinsic counterparts.
%For a specific language such as \PCF, \citet{Wadler2022} noted that `extrinsically-typed terms require about 1.6 times as much code as intrinsically-typed' for their formalisation of type safety.
%For our generic definitions,
Take our formal definition of typing derivations $\Gamma \vdash_{\Sigma, \Omega} \isTerm{t} : A$ as an example.
Its intrinsic definition is just one family of sets of typed terms indexed by $A$ and $\Gamma$, but its extrinsic counterpart is a generic family of sets indexed by additionally a generic raw term $t$, involving constructions of two different layers.

\paragraph{Category-theoretic analysis of well-typed terms}
The difference between intrinsic typing and extrinsic typing could be partly manifested by \citet{Fiore1999}{'s} theory of abstract syntax and variable binding which forms the foundation of \citet{Fiore2022}'s framework and inspires other referenced frameworks.
Let us take a closer look of their idea.
The set of (untyped) abstract syntax trees for a language can be understood as
\begin{enumerate*}
  \item a family of sets $\Term_{\Gamma}$ of well-scoped terms under a context~$\Gamma$ with
  \item variable renaming for a function $\sigma\colon \Gamma \to \Delta$ between variables acting as a functorial map from $\Term_{\Gamma}$ to $\Term_{\Delta}$, i.e.\ a presheaf $\Term\colon \mathbb{F} \to \mathsf{Set}$, and
  \item an \emph{initial} algebra $[\mathsf{v}, \mathsf{op}]$ on~$\Term$ given by the variable rule as a map $\mathsf{v}$ from the presheaf $V\colon \mathbb{F} \hookrightarrow \mathsf{Set}$ of variables to $\Term$ and other constructs as $\mathsf{op}\colon \mathbb{\Sigma}\Term \to \Term$ where $\mathbb{F}$ is the category of contexts and the functor $\mathbb{\Sigma}\colon \mathsf{Set}^\mathbb{F} \to \mathsf{Set}^\mathbb{F}$ encodes the binding arities of constructs. 
  The initiality amounts to structural recursion on terms, namely \emph{term traversal}.
\end{enumerate*}
Substitution for $\Term$ is modelled as a monoid in the category of presheaves.
To put it succinctly, it is the free $\mathbb{\Sigma}$-monoid over the presheaf~$V$ of variables.

Such an initial algebra can be constructed by the Initial Algebra Theorem~\cite{Trnkova1975}.

\paragraph{Type-theoretic construction of well-typed terms}
Fortunately, in type theory, constructing the initial algebra of well-typed terms boils down to defining an inductive type with a few constructors that align primitive rules (such as $\Rule{Var}$) and a rule schema; term traversal can be defined by pattern matching as usual for the inductive type~\citep{Fiore2022}.

\paragraph{Lack of a theory for extrinsic typing}
While the theory of \citet{Fiore1999} and others provide significant insights, they do not consider extrinsic typing.
We find inspiration in the interpretation of structural induction as algebras for an endofunctor on the category of predicates over a base category, as put forward by \citet{Hermida1998}.
From this perspective, we interpret extrinsic typing as a signature `functor' on the category of predicates consisting of a $\N$-indexed family $X$ of sets and another family $Y$ of sets over $X$; constructing typing derivations as its initial algebra over well-scoped terms.
Our formal construction appears novel and we believe that a theoretic understanding of our construction and its connection to intrinsic typing as a bridge between raw terms and well-typed terms deserve some attention.
However, carrying out a category-theoretic analysis requires expertise in category theory, which goes beyond the scope of this paper.

Therefore, in this section, we will primarily provide an overview of our design and offer intuitive explanations.
We will discuss the construction of simple types in \Cref{subsec:formal-simple-types}, raw terms in~\Cref{subsec:formal-raw-terms}, and bidirectional typing rules in \Cref{subsec:formal-bidirectional-typing}.
Since the formal proofs largely reflect their informal presentation, we will limit our illustration to the 'if' part of \Cref{lem:soundness-completeness} as an example in \Cref{subsec:formal-proofs}.

\subsection{Defining Simple Types}\label{subsec:formal-simple-types}


\begin{figure}
  \codefigure
  \small
  \begin{minipage}[t]{.45\textwidth}
    \begin{code}
record SigD : Set₁ where
  field
    Op      :  Set
    decEq   :  DecEq Op
    ar      :  Op → ℕ
    \end{code}
  \end{minipage}
  \begin{minipage}[t]{.45\textwidth}
    \begin{code}
⟦_⟧ : SigD → Set → Set
⟦ D ⟧ X = Σ[ i ∈ D .Op ] X ^ (D .ar i)

data Ty (Ξ : ℕ) : Set where
  `_   : Fin Ξ         → Ty Ξ
  op   : ⟦ D ⟧ (Ty Ξ)  → Ty Ξ
    \end{code}
  \end{minipage}
  \caption{Simple types in \Agda}
  \label{fig:formal-simple-type}
\end{figure}
We start with the formal definition of signatures and simple types (\Cref{fig:formal-simple-type}), which parallels its informal counterpart (\Cref{def:simple-signature}), with the exception of |⟦_⟧|.
To prevent circular references during the inductive definition of simple types, we initially define |⟦ D ⟧| on an arbitrary |Set| instead of\/ |Ty|.
Thus, types specified by a signature can be defined inductively where each inhabitant |op (i , ts)| for the $\Rule{Op}$ rule is a pair of an operation symbol and a list of length $n$.

From a categorical view, |⟦ D ⟧| is a functor from |Set| to |Set|, mapping $X$ to an $\Conid{Op}$-indexed coproduct $\sum_{i \in \Conid{Op}} X ^ {\Conid{ar}(i)}$ of products of $X$.
The type |Ty| is the free |⟦ D ⟧|-algebra over the type |Fin Ξ| or the initial algebra for the functor |Fin Ξ + ⟦ D ⟧|.

\subsection{Defining Raw Terms}\label{subsec:formal-raw-terms}

As shown in \Cref{fig:formal-bibisig}, we define |ArgD|, |OpD|, and |SigD| to represent arguments $[\Delta]A^{\dir{d}}$, bidirectional binding operations $\biop$, and bidirectional binding signatures, respectively, in line with their informal definitions.
By removing |mode| from these definitions, we retrieve the definitions of binding arguments, arities, and signatures.
\begin{figure}
  \codefigure
  \begin{minipage}[t]{.3\textwidth}
  \begin{code}
record ArgD (Ξ : ℕ) : Set
  where
  field
    cxt           : Cxt Ξ
    type          : Ty Ξ
    (DIR(mode))   : Mode

ArgsD = List ∘ ArgD
  \end{code}
  \end{minipage}
  \begin{minipage}[t]{.33\textwidth}
  \begin{code}
record OpD : Set where
  constructor ι
  field
    {tvars}         : ℕ
    (DIR(mode))     : Mode
    type            : TExp  tvars
    args            : ArgsD tvars
  \end{code}
  \end{minipage}
  \begin{minipage}[t]{.3\textwidth}
   \begin{code}
record SigD : Set₁ where
  constructor sigd
  field
    Op        : Set
    ar        : Op → OpD
  \end{code} 
  \end{minipage}
  \caption{Bidirectional binding signature in \Agda}
  \label{fig:formal-bibisig}
\end{figure}

To construct well-scoped raw terms indexed by a list $V$ of free variables, we introduce another signature functor mapping |Fam| to |Fam|, where |Fam| is the family of sets defined as |ℕ → Set|, indexed by a natural number indicating the number of free variables.
This functor for raw term construction resembles the one for defining simple types.
However, we define four distinct functors instead of directly defining one .
These are |⟦ Δ ⟧ᵃ| for an extension context |Δ|, |⟦ Ds ⟧ᵃˢ| for an argument list |Ds|, |⟦ ι Ds _ ⟧ᶜ | for an operation (|ι Ds A|), and |⟦ D ⟧ᶜ| for a binding signature $D$.
Notably, the functor |⟦ Δ ⟧ᵃ| extends the context by mapping the family of sets |X n| to |X (length Δ + n)|.
\begin{figure}
  \codefigure
\begin{minipage}[t]{.33\textwidth}
\begin{code}
⟦_⟧ᵃ   : TExps Ξ  → Fam → Fam
⟦ Δ             ⟧ᵃ   X n  =
  X (length Δ + n)

⟦_⟧ᵃˢ  : ArgsD Ξ  → Fam → Fam
⟦ []            ⟧ᵃˢ  _ _  = ⊤
⟦ (Δ ⊢ A) ∷ Ds  ⟧ᵃˢ  X n  =
  ⟦ Δ ⟧ᵃ X n × ⟦ Ds ⟧ᵃˢ X n
\end{code}
\end{minipage}
\begin{minipage}[t]{.3\textwidth}
\begin{code}
⟦_⟧ᶜ   : OpD  → Fam → Fam
⟦ ι Ds _  ⟧ᶜ  X    = ⟦ Ds ⟧ᵃˢ X

⟦_⟧    : SigD  → Fam → Fam
⟦ D      ⟧    X n  =
  Σ[ i ∈ D .Op ] ⟦ D .ar i ⟧ᶜ X n
\end{code}
\end{minipage}
\begin{minipage}[t]{.33\textwidth}
\begin{code}
data Raw : ℕ → Set where
  `_   : Fin n                  → Raw n
  _∋_  : Ty           → Raw n   → Raw n
  op   : ⟦ D ⟧ Raw n            → Raw n
\end{code}
\end{minipage}
\caption{Signature functor for raw terms and raw terms in \Agda}
\label{fig:formal-raw-term-functor}
\label{fig:formal-raw-terms}
\end{figure}

The inductive type of raw terms, indexed by a list of free variables, is defined as shown in \Cref{fig:formal-raw-terms}.
This mirrors our informal definition (\Cref{fig:raw-terms}), where |A ∋ t| corresponds to the raw term $t \annotate A$.
These definitions align closely with those found in other referenced frameworks.

\subsection{Defining Extrinsic Bidirectional Typing Derivations}\label{subsec:formal-bidirectional-typing}
Formally defining extrinsic derivations is much trickier.
This requires defining a family of sets, indexed by context, type, mode, and notably, a raw term, involving another signature endofunctor alone with the functor used for constructing raw terms. 

We begin with the family of sets on which the functor acts.
A typing judgement $\Gamma \vdash_{\Sigma, \Omega} t :^{\dir{d}} A$ can be viewed as a predicate over raw terms with four indices: a context, a $\N$-indexed family of sets, a mode, and a type.
The type of this predicate can be generalised to a family of sets over the $\N$-indexed family of sets, as follows:
{\small
\begin{code}
Fam : R.Fam → Set _
Fam X  = (Γ : Cxt 0) → X (length Γ) → Mode → Ty → Set
\end{code}}
Observe that the second index |X| depends on the length of the first index |Γ|.
This is because a typing derivation for a raw term $V \vdash_{\Sigma, \erase{\Omega}} t$ requires the same number of variables as in $V$.

In a similar vein, we define four functors for the construction of bidirectional typing derivations, albeit in a top-down manner.
An endofunctor on predicates must act as a \emph{lifting} of the functor on its domain, illustrated by the signature endofunctor |⟦_⟧| for a bidirectional binding signature:
{\small
\begin{code}
⟦_⟧  : (D : SigD) (X : R.Fam) (Y : Fam X) → Fam (R.⟦ erase D ⟧ X)
⟦ D ⟧ X Y Γ (o , ts) d A = ⟦ D .ar o ⟧ᶜ X Y Γ ts d A
\end{code}}
This functor maps a predicate |Y| over |X| into a predicate |⟦ D ⟧ X Y| over |R.⟦ erase D ⟧ X|.
Here, |erase D| represents the mode erasure of |D|, and the prefix |R| in |R.⟦_⟧| indicates the signature endofunctor used in raw term construction.

The functor |⟦ D .ar o ⟧ᶜ| is defined for an operation $\biop$:
{\small\begin{code}
⟦_⟧ᶜ  : (D : OpD) (X : R.Fam ℓ) (Y : Fam ℓ′ X) → Fam ℓ′ (R.⟦ eraseᶜ D ⟧ᶜ X)
⟦ ι {Ξ} d A₀ D ⟧ᶜ X Y Γ xs d′ A =
  d ≡ d′ × Σ[ p ∈ TSub Ξ 0 ] A₀ ⟨ p ⟩ ≡ A × ⟦ D ⟧ᵃˢ X Y σ Γ xs
\end{code}}
A set within the family is only inhabited if the indices correspond with the mode and the type as specified by the operation.
Therefore, in defining the set |⟦ ι {Ξ} d A₀ D ⟧ᶜ X Y Γ xs d′ A|, it takes identity proofs for |d ≡ d′| and |A₀ ⟨ σ ⟩ ≡ A|, with |A₀| instantiated by a substitution |σ| from $\Xi$ to $\emptyset$.
This ensures that the set is inhabited only if the indices align with what the arity (|D .ar o|) specifies.

The signature endofunctor for an argument list |Ds| is defined in a manner that it maps a predicate to a family of sets indexed by a context and a family of product sets, considering that each premise in a typing derivation shares a common context $\Gamma$ and a term from a list of subterms.
{\small\begin{code}
⟦_⟧ᵃˢ  : (D : ArgsD Ξ) (X : R.Fam) (Y : Fam X)
       → TSub Ξ 0 → (Γ : Cxt 0) → R.⟦ eraseᵃˢ D ⟧ᵃˢ X (length Γ) → Set
⟦ []               ⟧ᵃˢ _  _  _  _  _         = ⊤
⟦ Δ ⊢[ d ] A ∷ Ds  ⟧ᵃˢ X  Y  σ  Γ  (x , xs)  =
  ⟦ Δ ⟧ᵃ X (λ Γ' x' → Y Γ' x' d (A ⟨ σ ⟩)) σ Γ x × ⟦ Ds ⟧ᵃˢ X Y σ Γ xs
\end{code}}
The signature endofunctor |⟦ Δ ⟧ᵃ| for an extension context |Δ| maps a predicate $Y$ over a $\N$-indexed family $X$ of sets into a predicate (|⟦ Δ ⟧ᵃ X Y|) whose context is extended by the types in |Δ|.
{\small\begin{code}
⟦_⟧ᵃ  : (Δ : Cxt Ξ) (X : R.Fam) (Y : (Γ : Cxt 0) → X (length Γ) → Set)
      → TSub Ξ 0 → (Γ : Cxt 0) → R.⟦ Δ ⟧ᵃ X (length Γ) → Set
⟦ []     ⟧ᵃ X Y σ Γ t  = Y Γ t
⟦ A ∷ Δ  ⟧ᵃ X Y σ Γ t  = ⟦ Δ ⟧ᵃ X Y σ ((A ⟨ σ ⟩) ∷ Γ) t
\end{code}}
This completes our definition of the signature functor for constructing extrinsic typing derivations.

At last, we can define the type of bidirectional typing derivations for a signature |D|, similarly to how we have defined simple types and raw terms.
This involves the following four constructors, corresponding to rules $\SynRule{Var}$, $\SynRule{Anno}$, $\ChkRule{Sub}$, and $\Rule{Op}$ in \Cref{fig:extrinsic-typing}.
{\small\begin{code}
data _⊢_[_]_ : Fam Raw where

  var   : (i : A ∈ Γ)          {-"\hspace{10em}"-}     _↑_   : Γ ⊢ r  ⇒ B
        → L.index i ≡ j                                      → A ≡ B
        → Γ ⊢ (` j) ⇒ A                                      → Γ ⊢ r  ⇐ A
                                                                                         
  _∋_   : (A : Ty)                                     op    : ⟦ D ⟧ Raw _⊢_[_]_ Γ  rs  {-"\phantom{[}"-}  d    A
        → Γ ⊢ r        ⇐ A                                   → Γ ⊢ op rs                [                  d ]  A
        → Γ ⊢ (A ∋ r)  ⇒ A                    
\end{code}}

\subsection{A Formal Proof Example: Soundness}\label{subsec:formal-proofs}

Our formal proofs of induction typically consist of mutual proofs for the inductive type of derivations, for a list of arguments, for an extension context, and sometimes for the case of operations for clarity.

As an illustration, consider the formal proof of soundness below, i.e.\ the `if' part of \cref{lem:soundness-completeness}.
Its formal proof is defined in a module which has signatures as its parameters:
{\small\begin{code}
module Theory.Soundness {SD : S.SigD} (BD : B.SigD SD) where
\end{code}}
The induction proof is nothing more than a function defined by pattern matching for each case: each constructor of bidirectional typing derivations is mapped to a corresponding constructor of typing derivations.
The only (slightly) interesting case $\ChkRule{Sub}$ is proved by disregarding the identity proof |refl| and use the induction hypothesis |soundness t| directly:
\begin{figure}[H]
  \codefigure
  \begin{minipage}[t]{.55\textwidth}
\begin{code}
mutual

  soundness : Γ ⊢ r [ d ] A  →  Γ ⊢ r ⦂ A
  soundness (var i eq) = var i eq
  soundness (A ∋ t)    = A ∋ soundness t
  soundness (t ↑ refl) = soundness t
  soundness (op {rs = i , _} (_ , σ , σ-eq , ts)) =
    op (σ , σ-eq , soundnessᵃˢ (BD .ar i .args) ts)

  soundnessᵃˢ
    :  (Ds : ArgsD Ξ) 
    →  ⟦ Ds ⟧ᵃˢ            Raw _⊢_[_]_  σ Γ rs
    →  T.⟦ eraseᵃˢ Ds ⟧ᵃˢ  Raw _⊢_⦂_    σ Γ rs
  soundnessᵃˢ []                  _         = tt
  soundnessᵃˢ ((Δ ⊢[ _ ] _) ∷ Ds) (t , ts)  =
    soundnessᵃ Δ t , soundnessᵃˢ Ds ts
\end{code}
\end{minipage}
\begin{minipage}[t]{.44\textwidth}
\begin{code}
  {-" \phantom{mutual} "-}
  soundnessᵃ
    :  (Δ : TExps Ξ) 
    →  ⟦ Δ ⟧ᵃ    Raw (_⊢_[  d ]  A)  σ Γ r
    →  T.⟦ Δ ⟧ᵃ  Raw (_⊢_⦂       A)  σ Γ r
  soundnessᵃ []       t  = soundness    t
  soundnessᵃ (_ ∷ Δ)  t  = soundnessᵃ Δ t
\end{code}
\end{minipage}
%\caption{The soundness proof in \Agda}
%\label{fig:formal-soundness}
\end{figure}
Each construct in an induction proof tailored for a specific system such as \PCF has to be scrutinised, so its size increases as the system in question has more constructs.
On the other hand, the size of a generic induction proof remains the same and is manageable in a proof assistant that lacks extensive tactics for automating theorem proving, like \Agda.
We have achieved more by doing no ad hoc proofs.
\end{document}
