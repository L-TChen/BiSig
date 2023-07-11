%!TEX root = BiSig.tex

\documentclass[BiSig.tex]{subfiles}


%include agda.fmt

%format ` = "\text{\textasciigrave}"
%format `_ = "\text{\textasciigrave}" _
%format ^ = "\hat{}"
%format Γ' = "\iden{" Γ "^\prime}"
%format r' = "\iden{" r "^\prime}"
%format x' = "\iden{" x "^\prime}"
%format ⦃  = "\{\kern-.9pt\vrule width .75pt height 7.125pt depth 1.975pt\kern-1.5pt"
%format ⦄  = "\kern-1.5pt\vrule width .75pt height 7.125pt depth 1.975pt\kern-.9pt\}"
%format ℓ' = "\iden{" ℓ "^\prime}"
%format ℓ′ = "\iden{" ℓ "^\prime}"
%format ℓ'' = "\iden{" ℓ "^{\prime\prime}}"


\begin{document}

\section{Formalisation} \label{sec:formalisation}
%\begin{enumerate}
%  \item (Bidirectional) binding signature, functor, and terms (extrinsic typing, raw terms, raw terms in some mode) --- 2.5 pp
%  \item Compare the induction principle and the \Agda proof of Soundness --- 2 pp
%  \item type synthesis and checking -- 0.5 p
%  \item Examples including STLC (PCF), application in spine form --- 1p
%
%\end{enumerate}
Our theory, initially developed in \Agda, has been later translated into the mathematical vernacular.
While the translation is reasonably straightforward, understanding the design of the formalisation itself could pose some difficulty.
Indeed, as discussed in \Cref{sec:language-formalisation}, designing a language formalisation framework is still a challenging task and our formalisation is no exception.
Unlike prior frameworks that have primarily focused on meta-properties centred around substitution and term traversal for intrinsically-typed terms, our theory of bidirectional type synthesis does not require term substitution but structural induction for extrinsically-typed terms.
The formal definitions of extrinsic typing in bidirectional type systems, including bidirectional typing derivations and mode derivations, are more complex than their intrinsic counterparts.
For a specific language such as PCF, it is noted by \citet{Wadler2022} already that `extrinsically-typed terms require about 1.6 times as much code as intrinsically-typed' for their formalisation of type safety.
As for our generic definitions, the formal type-theoretic definition for extrinsic typing derivations $\Gamma \vdash_{\Sigma, \Omega} \isTerm{t} : A$ (\Cref{fig:extrinsic-typing}), for example, is a generic families of sets, also known as a \emph{proof-relevant predicate}, indexed by a generic raw \emph{term} $t$ in additional to a type $A$ and a context $\Gamma$ rather than just one family of sets of intrinsically-typed terms indexed by $A$ and $\Gamma$.

A categorical analysis of extrinsic typing requires not only \varcitet{Fiore1999}{'s} theory of abstract syntax with variable binding which backs \citet{Fiore2022}'s framework but also \varcitet{Hermida1998}{'s} interpretation of inductive proofs as algebras on the category of predicates.
Thus, a faithful understanding of our formal constructions requires certain proficiency in category theory, which falls outside the scope of this paper.

As such, in this section, we will merely provide an overview of our design and draw an analogy between the construction of simple types in \Cref{subsec:formal-simple-types} and bidirectional typing rules in \Cref{subsec:formal-extrinsic-typing} in plain terms, avoiding category theory deliberately.
On the other hand, the formal proofs in our theory closely mirror the informal versions presented so far, thus we will only illustrate the soundness part of \Cref{lem:soundness-completeness} as an example in \Cref{subsec:formal-proofs}. 

\subsection{Defining Simple Types}\label{subsec:formal-simple-types}

% simple types
\begin{figure}[h]
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

data Tm (Θ : ℕ) : Set where
  `_   : Fin Θ         → Tm Θ
  op   : ⟦ D ⟧ (Tm Θ)  → Tm Θ
    \end{code}
  \end{minipage}
\end{figure}
\subsection{Defining Raw Terms and Extrinsic Typing Derivations}\label{subsec:formal-extrinsic-typing}

\begin{figure}[H]
  \small
  \begin{minipage}[t]{.3\textwidth}
  \begin{code}
record ArgD (Ξ : ℕ) : Set
  where
  field
    cxt    : Cxt Ξ
    type   : TExp Ξ
    mode   : Mode
  \end{code}
  \end{minipage}
  \begin{minipage}[t]{.33\textwidth}
  \begin{code}
record ConD : Set where 
  constructor ι
  field
    {vars}   : ℕ
    args     : List (ArgD vars)
    type     : TExp vars
    mode     : Mode
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

% functors for raw terms
\begin{figure}[H]
  \small
  \begin{minipage}[t]{.57\textwidth}
%Fam : (ℓ : Level) → Set (lsuc ℓ)
%Fam ℓ = ℕ → Set ℓ
%
%Fam₀ : Set₁
%Fam₀ = Fam 0ℓ
\begin{code}
⟦_⟧ᵃ   : TExps Ξ  → Fam → Fam
⟦ Δ             ⟧ᵃ   X n  = X (length Δ ʳ+ n)

⟦_⟧ᵃˢ  : ArgsD Ξ  → Fam → Fam
⟦ []            ⟧ᵃˢ  _ _  = ⊤
⟦ (Δ ⊢ A) ∷ Ds  ⟧ᵃˢ  X n  = ⟦ Δ ⟧ᵃ X n × ⟦ Ds ⟧ᵃˢ X n

⟦_⟧ᶜ   : ConD     → Fam → Fam
⟦ ι _ D         ⟧ᶜ   X    = ⟦ D ⟧ᵃˢ X

⟦_⟧    : Desc     → Fam → Fam
⟦ D             ⟧    X n  = Σ[ i ∈ D .Op ] ⟦ D .rules i ⟧ᶜ X n
\end{code}
  \end{minipage}
  \begin{minipage}[t]{.4\textwidth}
\begin{code}
infix 5 _∋_

data Raw : ℕ → Set where
  `_  : Fin n                  → Raw n
  _∋_ : (A : Ty) (t : Raw n)   → Raw n
  op  : ⟦ D ⟧ Raw n            → Raw n
\end{code}
  \end{minipage}
\end{figure}

\begin{figure}[H]
  \small
%Fam : (ℓ′ : Level) → (X : R.Fam ℓ) → Set (ℓ ⊔ lsuc ℓ′)
%Fam ℓ′ X = (Γ : Cxt 0) → X (length Γ) → Ty → Set ℓ′
%
%Fam₀ : (X : R.Fam ℓ) → Set (ℓ ⊔ lsuc 0ℓ)
%Fam₀ X = Fam 0ℓ X
%
\begin{code}
⟦_⟧ᵃ  : (Δ : TExps Ξ) (X : R.Fam) (Y : (Γ : Cxt 0)
      → X (length Γ) → Set)
      → TSub Ξ 0 → (Γ : Cxt 0) → R.⟦ Δ ⟧ᵃ X (length Γ)
      → Set
⟦ []            ⟧ᵃ X Y σ Γ x          = Y Γ x
⟦ A ∷ Δ         ⟧ᵃ X Y σ Γ x          = ⟦ Δ ⟧ᵃ X Y σ ((A ⟨ σ ⟩) ∷ Γ) x

⟦_⟧ᵃˢ : (D : ArgsD Ξ) (X : R.Fam) (Y : Fam X)
      → TSub Ξ 0 → (Γ : Cxt 0) → R.⟦ D ⟧ᵃˢ X (length Γ) → Set
⟦ []            ⟧ᵃˢ _ _ _ _ _         = ⊤
⟦ (Δ ⊢ A) ∷ Ds  ⟧ᵃˢ X Y σ Γ (x , xs)  =
  ⟦ Δ ⟧ᵃ X (λ Γ' x' → Y Γ' x' (A ⟨ σ ⟩)) σ Γ x × ⟦ Ds ⟧ᵃˢ X Y σ Γ xs

⟦_⟧ᶜ : (D : ConD) (X : R.Fam) (Y : Fam X) → Fam ℓ′ (R.⟦ D ⟧ᶜ X)
⟦ ι {Ξ} B D     ⟧ᶜ X Y Γ xs A         =
  Σ[ σ ∈ TSub Ξ 0 ] B ⟨ σ ⟩ ≡ A × ⟦ D ⟧ᵃˢ X Y σ Γ xs

⟦_⟧ : (D : Desc) (X : R.Fam) (Y : Fam X) → Fam (R.⟦ D ⟧ X)
⟦ D             ⟧ X Y Γ (i , xs) A    = ⟦ D .rules i ⟧ᶜ X Y Γ xs A
\end{code}
\end{figure}
\begin{figure}[H]
  \small
\begin{minipage}[t]{.47\textwidth}
\begin{code}
data _⊢_⦂_ : Fam₀ Raw where

  var  : (i : A ∈ Γ)
       → {j : Fin (length Γ)}
       → L.index i ≡ j
       → --------------------
         Γ ⊢ (` j) ⦂ A
\end{code}
  \end{minipage}
\begin{minipage}[t]{.47\textwidth}
\begin{code}
  _∋_  : (A : Ty)
       → Γ ⊢ r ⦂ A
       → ---------------
         Γ ⊢ (A ∋ r) ⦂ A
  op   : ⟦ D ⟧ Raw _⊢_⦂_ Γ rs A
       → -----------------------------
         Γ ⊢ op rs ⦂ A
\end{code}
  \end{minipage}
\end{figure}

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
        → --------------------
          Γ ⊢ (` j) ⇒ A

    _∋_ : (A : Ty)
        → Γ ⊢ r ⇐ A
        → Γ ⊢ (A ∋ r) ⇒ A
\end{code}
\end{minipage}
\begin{minipage}[t]{.48\textwidth}
\begin{code}
    _↑_ : Γ ⊢ r ⇒ B
        → A ≡ B
        → ---------
          Γ ⊢ r ⇐ A

    op  : ⟦ D ⟧ Raw _⊢_[_]_ Γ rs d A
        → -----------------------------------
          Γ ⊢ op rs [ d ] A
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
