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
As we have mentioned in \Cref{sec:intro} that our theory was developed in \Agda, the formal counterparts of our development can be used as programs directly.
In this section, we sketch their use with our running example---simply typed $\lambda$-calculus.
We will specify the language $(\Sigma_{\bto}, \Omega^{\Leftrightarrow})$ in \Agda, show it mode-correct, and then instantiate the corresponding type synthesiser.

\paragraph{Specifying a language}
To specify the type signature $\Sigma_{\bto}$, we define a type of operations, its decidable equality of type |(x y : ΛₜOp) → Dec (x ≡ y)| with arities
\begin{code}
data ΛₜOp : Set where base imp : ΛₜOp

ΛₜD : S.SigD
ΛₜD = sigd ΛₜOp λ { base → 0; imp → 2 }
\end{code}
where |S.SigD| is the \Agda type of type signatures.
Similarly, to specify the bidirectional binding signature $\Omega^{\Leftrightarrow}$, we define a set of operation symbols 
\begin{code}
data ΛOp : Set where `app `abs : ΛOp
\end{code}
and its decidable equality |decΛOp : DecEq ΛOp|.
The type |SigD| of bidirectional binding signatures is defined in a module parametrised by a type signature
\begin{code}
open import Syntax.BiTyped.Signature ΛₜD
\end{code}
and the bidirectional binding signature $\Lambda^{\Leftrightarrow}$ can be specified readily:
\begin{code}
Λ⇔D : SigD
Λ⇔D = record
  { Op      = ΛOp ; decOp   = decΛOp
  ; ar      = λ
    {  `app  → 2 ▷ ρ[ []           ⊢[ Chk ] ` 1 ] ρ[ [] ⊢[ Syn ] ` 1 ↣ ` 0 ]  [] ⇒ ` 0
    ;  `abs  → 2 ▷ ρ[ (` 1 ∷ [])   ⊢[ Chk ] ` 0 ]                             [] ⇐ (` 1) ↣ (` 0) } }
\end{code}
where the set $\Fin(n)$ of naturals less than $n$ is used for type variables, and |2| above indicates the number of variables in each construct and |` i| the $i$-th variable.

\paragraph{Proving mode-correctness}
To prove that the specified language $(\Sigma_{\bto}, \Omega^{\Leftrightarrow})$ is mode-correct, we simply invoke \cref{lem:decidability-mode-correctness} for each construct:
\begin{code}
open import Theory.ModeCorrectness.Decidability ΛₜD

mcΛ⇔D : ModeCorrect Λ⇔D
mcΛ⇔D `app   = from-yes (ModeCorrectᶜ? (Λ⇔D .ar `app))
mcΛ⇔D `abs   = from-yes (ModeCorrectᶜ? (Λ⇔D .ar `abs))
\end{code}
where |from-yes| extracts the positive witness from an inhabitant of the |Dec| type.

\paragraph{Instantiating a type synthesiser}
Now we have completed the definition |Λ⇔D| for the bidirectional type system $(\Sigma_{\bto}, \Omega^{\Leftrightarrow})$ with the proof obligation~|mcΛ⇔D| for mode-correctness, so we can instantiate the type synthesiser, i.e.\ \cref{cor:trichotomy}, by importing the module
\begin{code}
open import Theory.Trichotomy Λ⇔D mcΛ⇔D
\end{code}
where the type synthesiser is defined:
\begin{code}
synthesise : (Γ : Cxt) (r : Raw (length Γ)) → Dec (∃[ A ] Γ ⊢ r ⦂ A) ⊎ ¬ Pre Syn r
\end{code}
As nothing is postulated in our formal development, the proof |synthesise| can actually run!
Moreover, we do not need to worry about its correctness which has been guaranteed by its type.
\end{document}
