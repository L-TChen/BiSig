%!TEX root = BiSig.tex

\documentclass[BiSig.tex]{subfiles}

%include agda.fmt

%format ⦃  = "\{\kern-.9pt\vrule width .75pt height 7.125pt depth 1.975pt\kern-1.5pt"
%format ⦄  = "\kern-1.5pt\vrule width .75pt height 7.125pt depth 1.975pt\kern-.9pt\}"

\begin{document}

\section{Formalisation} \label{sec:formalisation}
\begin{enumerate}
  \item (Bidirectional) binding signature, functor, and terms (extrinsic typing, raw terms, raw terms in some mode) --- 2.5 pp
  \item Compare the induction principle and the \Agda proof of Soundness --- 2 pp
  \item type synthesis and checking -- 0.5 p
  \item Examples including STLC (PCF), application in spine form --- 1p

\end{enumerate}

\begin{figure}
  \small
  \begin{minipage}[t]{.3\linewidth}
  \begin{code}
record ArgD (Ξ : ℕ) : Set
  where
  field
    cxt    : Cxt Ξ
    type   : TExp Ξ
    mode   : Mode
  \end{code}
  \end{minipage}
  \begin{minipage}[t]{.32\linewidth}
  \begin{code}
record ConD : Set where
  field
    {vars}   : ℕ
    args     : List (ArgsD vars)
    type     : TExp  vars
    mode     : Mode
  \end{code}
  \end{minipage}
  \begin{minipage}[t]{.3\linewidth}
   \begin{code}
record Desc : Set₁ where
  field
    Op          : Set
    rules       : Op → ConD
  \end{code} 
  \end{minipage}
  
  \caption{Definition of bidirectional binding signature}  
\end{figure}

{\small\begin{code}
Fam : (ℓ′ : Level) (X : R.Fam ℓ) → Set (ℓ ⊔ lsuc ℓ′)
Fam ℓ′ X = (Γ : Cxt 0) → X (length Γ) → Mode → Ty → Set ℓ′

⟦_⟧ᵃ  : (Δ : TExps Ξ) (X : R.Fam ℓ) (Y : (Γ : Cxt 0) → X (length Γ) → Set ℓ′)
      → TSub Ξ 0 → (Γ : Cxt 0) → R.⟦ Δ ⟧ᵃ X (length Γ) → Set ℓ′
⟦ []     ⟧ᵃ X Y σ Γ t  = Y Γ t
⟦ A ∷ Δ  ⟧ᵃ X Y σ Γ t  = ⟦ Δ ⟧ᵃ X Y σ ((A ⟨ σ ⟩) ∷ Γ) t

⟦_⟧ᵃˢ  : (D : ArgsD Ξ) (X : R.Fam ℓ) (Y : Fam ℓ′ X)
       → TSub Ξ 0 → (Γ : Cxt 0) → R.⟦ eraseᵃˢ D ⟧ᵃˢ X (length Γ) → Set ℓ′
⟦ []               ⟧ᵃˢ _  _  _  _  _         = ⊤
⟦ Δ ⊢[ d ] A ∷ Ds  ⟧ᵃˢ X  Y  σ  Γ  (x , xs)  =
  ⟦ Δ ⟧ᵃ X (λ Γ' x' → Y Γ' x' d (A ⟨ σ ⟩)) σ Γ x × ⟦ Ds ⟧ᵃˢ X Y σ Γ xs

⟦_⟧ᶜ : (D : ConD) (X : R.Fam ℓ) (Y : Fam ℓ′ X) → Fam ℓ′ (R.⟦ eraseᶜ D ⟧ᶜ X)
⟦ ι {Ξ} d B D ⟧ᶜ X Y Γ xs d′ A =
  d ≡ d′ × Σ[ σ ∈ TSub Ξ 0 ] B ⟨ σ ⟩ ≡ A × ⟦ D ⟧ᵃˢ X Y σ Γ xs

⟦_⟧ : (D : Desc) (X : R.Fam ℓ) (Y : Fam ℓ′ X) → Fam ℓ′ (R.⟦ erase D ⟧ X)
⟦ D ⟧ X Y Γ (i , xs) d A = ⟦ D .rules i ⟧ᶜ X Y Γ xs d A
\end{code}}


\end{document}
