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
%format `app = "\iden{" ` "}" app
%format `abs = "\iden{" ` "}" abs

%format (DIR(t)) = "\dir{" t "}"

\begin{document}

\section{Demonstration} \label{sec:formalisation}
As our theory is developed with \Agda constructively, the formal counterparts of our development can be used as programs directly.
We sketch their use with our running example, simply typed $\lambda$-calculus, by specifying the language $(\Sigma_{\bto}, \Omega^{\Leftrightarrow})$, showing it mode-correct, and then instantiating its type synthesiser.

\paragraph{Specifying a language}
Signatures |ΛₜD| and |Λ⇔D| are defined for $\Sigma_{\bto}$ and $\Omega^{\Leftrightarrow}$: 
\begin{code}
data ΛₜOp : Set where base imp : ΛₜOp

ΛₜD : S.SigD
ΛₜD = sigd ΛₜOp λ where base → 0; imp → 2

open import Syntax.BiTyped.Signature ΛₜD

data ΛOp : Set where `app `abs : ΛOp

Λ⇔D : SigD
Λ⇔D .Op  = ΛOp
Λ⇔D .ar  = λ where
  `app   → 2 ▷ ρ[ []        ⊢[ Chk ] ` 1 ] ρ[ [] ⊢[ Syn ] ` 1 ↣ ` 0 ]  [] ⇒ ` 0
  `abs   → 2 ▷ ρ[ ` 1 ∷ []  ⊢[ Chk ] ` 0 ]                             [] ⇐ (` 1) ↣ (` 0) 
\end{code}
where
\begin{inlineenum}
  \item |S.SigD| is the type of type signatures,
  \item |SigD| is the type of bidirectional binding signatures,
  \item |2| indicates the number of type variable variables in an operation,
  \item $`i$ the $i$-th type variable, 
\end{inlineenum}
and the definitions of decidable equality for |ΛₜOp| and |ΛOp| are omitted above.


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
Now we have the definition |Λ⇔D| for the bidirectional type system $(\Sigma_{\bto}, \Omega^{\Leftrightarrow})$ with |mcΛ⇔D| for its mode-correctness, so we can instantiate its type synthesiser (\cref{cor:trichotomy}) just by importing the module
\begin{code}
open import Theory.Trichotomy Λ⇔D mcΛ⇔D
\end{code}
where the type synthesiser is defined:
\begin{code}
synthesise
  : (Γ : Cxt) (r : Raw (length Γ))
  → Dec (∃[ A ] Γ ⊢ r ⦂ A) ⊎ ¬ Pre Syn r
\end{code}
Every statement in our development so far has been formally proved constructively, so the proof |synthesise|r can actually compute as a program!

\paragraph{Running a type synthesiser}
The type of raw terms for $(\Sigma_{\bto}, \Omega^{\Leftrightarrow})$ are defined in the module |Syntax.Typed.Raw.Term| with the mode-erased signature |erase Λ⇔D|:
\begin{code}
open import Theory.Erasure
open import Syntax.Typed.Raw.Term (erase Λ⇔D)
\end{code}

As raw terms for operations are defined generically using a single constructor $|op|$, it is not so convenient to manipulate them directly.
Hence, we use pattern synonyms and define raw terms in a form close to the informal presentation:
\begin{code}
infixl 8 _·_
infixr 7 ƛ_

pattern _·_   r s = op (`app , s , r , _)
pattern ƛ_    r   = op (`abs , r , _)

S : Raw n
S = ƛ ƛ ƛ ` suc (suc zero) · ` zero · (` suc zero · ` zero)
\end{code}
Then, invoking the program |synthesise| with |S| and its required type annotation gives us a typing derivation as expected:
\begin{code}
⊢S? = synthesise [] (((b ↣ b ↣ b) ↣ (b ↣ b) ↣ b ↣ b) ∋ S)
\end{code}

%\begin{code}
%inl
%(yes
% (op
%  (imp ,
%   op
%   (imp ,
%    op (base , []) ∷
%    op
%    (imp ,
%     op (base , []) ∷
%     op (base , []) ∷ [])
%    ∷ [])
%   ∷
%   op
%   (imp ,
%    op
%    (imp ,
%     op (base , []) ∷
%     op (base , []) ∷ [])
%    ∷
%    op
%    (imp ,
%     op (base , []) ∷
%     op (base , []) ∷ [])
%    ∷ [])
%   ∷ [])
%  ,
%  (op
%   (imp ,
%    op
%    (imp ,
%     op (base , []) ∷
%     op
%     (imp ,
%      op (base , []) ∷
%      op (base , []) ∷ [])
%     ∷ [])
%    ∷
%    op
%    (imp ,
%     op
%     (imp ,
%      op (base , []) ∷
%      op (base , []) ∷ [])
%     ∷
%     op
%     (imp ,
%      op (base , []) ∷
%      op (base , []) ∷ [])
%     ∷ [])
%    ∷ [])
%   ∋
%   op
%   ((λ x →
%       extend (sigd ΛₜOp (λ { base → 0 ; imp → 2 }))
%       (extend (sigd ΛₜOp (λ { base → 0 ; imp → 2 }))
%        (λ ()) tt
%        (op
%         (imp ,
%          op
%          (imp ,
%           op (base , []) ∷
%           op (base , []) ∷ [])
%          ∷
%          op
%          (imp ,
%           op (base , []) ∷
%           op (base , []) ∷ [])
%          ∷ [])))
%       ((λ ()) , tt)
%       (op
%        (imp ,
%         op (base , []) ∷
%         op
%         (imp ,
%          op (base , []) ∷
%          op (base , []) ∷ [])
%         ∷ []))
%       (∪-⊆⁺ (λ { (here eq) → here eq ; (there ()) })
%        (λ x∈ →
%           there
%           (∪-⊆⁺ (λ { (here eq) → here eq ; (there ()) })
%            (λ x∈₁ → there ((λ ()) x∈₁)) x∈
%            | (∈-∪⁻ (cons zero [] tt) x∈ | inl tt)))
%        (∪-⊆⁺ (λ x₁ → x₁) []⊆xs
%         (∀-cons (λ _ → there (here refl))
%          (λ x₁ → ∀-cons (λ _ → here refl) (λ x₂ {}) x₁) x tt₀)
%         | (∈-∪⁻ (cons (suc zero) (cons zero [] tt) ((λ ()) , tt))
%            (∀-cons (λ _ → there (here refl))
%             (λ x₁ → ∀-cons (λ _ → here refl) (λ x₂ {}) x₁) x tt₀)
%            | inl tt))
%        | (∈-∪⁻ (cons (suc zero) [] tt)
%           (∪-⊆⁺ (λ x₁ → x₁) []⊆xs
%            (∀-cons (λ _ → there (here refl))
%             (λ x₁ → ∀-cons (λ _ → here refl) (λ x₂ {}) x₁) x tt₀)
%            | (∈-∪⁻ (cons (suc zero) (cons zero [] tt) ((λ ()) , tt))
%               (∀-cons (λ _ → there (here refl))
%                (λ x₁ → ∀-cons (λ _ → here refl) (λ x₂ {}) x₁) x tt₀)
%               | inl tt))
%           | inl ((λ ()) , tt))))
%    ,
%    refl ,
%    op
%    ((λ x →
%        extend (sigd ΛₜOp (λ { base → 0 ; imp → 2 }))
%        (extend (sigd ΛₜOp (λ { base → 0 ; imp → 2 }))
%         (λ ()) tt
%         (op
%          (imp ,
%           op (base , []) ∷
%           op (base , []) ∷ [])))
%        ((λ ()) , tt)
%        (op
%         (imp ,
%          op (base , []) ∷
%          op (base , []) ∷ []))
%        (∪-⊆⁺ (λ { (here eq) → here eq ; (there ()) })
%         (λ x∈ →
%            there
%            (∪-⊆⁺ (λ { (here eq) → here eq ; (there ()) })
%             (λ x∈₁ → there ((λ ()) x∈₁)) x∈
%             | (∈-∪⁻ (cons zero [] tt) x∈ | inl tt)))
%         (∪-⊆⁺ (λ x₁ → x₁) []⊆xs
%          (∀-cons (λ _ → there (here refl))
%           (λ x₁ → ∀-cons (λ _ → here refl) (λ x₂ {}) x₁) x tt₀)
%          | (∈-∪⁻ (cons (suc zero) (cons zero [] tt) ((λ ()) , tt))
%             (∀-cons (λ _ → there (here refl))
%              (λ x₁ → ∀-cons (λ _ → here refl) (λ x₂ {}) x₁) x tt₀)
%             | inl tt))
%         | (∈-∪⁻ (cons (suc zero) [] tt)
%            (∪-⊆⁺ (λ x₁ → x₁) []⊆xs
%             (∀-cons (λ _ → there (here refl))
%              (λ x₁ → ∀-cons (λ _ → here refl) (λ x₂ {}) x₁) x tt₀)
%             | (∈-∪⁻ (cons (suc zero) (cons zero [] tt) ((λ ()) , tt))
%                (∀-cons (λ _ → there (here refl))
%                 (λ x₁ → ∀-cons (λ _ → here refl) (λ x₂ {}) x₁) x tt₀)
%                | inl tt))
%            | inl ((λ ()) , tt))))
%     ,
%     refl ,
%     op
%     ((λ x →
%         extend (sigd ΛₜOp (λ { base → 0 ; imp → 2 }))
%         (extend (sigd ΛₜOp (λ { base → 0 ; imp → 2 }))
%          (λ ()) tt (op (base , [])))
%         ((λ ()) , tt) (op (base , []))
%         (∪-⊆⁺ (λ { (here eq) → here eq ; (there ()) })
%          (λ x∈ →
%             there
%             (∪-⊆⁺ (λ { (here eq) → here eq ; (there ()) })
%              (λ x∈₁ → there ((λ ()) x∈₁)) x∈
%              | (∈-∪⁻ (cons zero [] tt) x∈ | inl tt)))
%          (∪-⊆⁺ (λ x₁ → x₁) []⊆xs
%           (∀-cons (λ _ → there (here refl))
%            (λ x₁ → ∀-cons (λ _ → here refl) (λ x₂ {}) x₁) x tt₀)
%           | (∈-∪⁻ (cons (suc zero) (cons zero [] tt) ((λ ()) , tt))
%              (∀-cons (λ _ → there (here refl))
%               (λ x₁ → ∀-cons (λ _ → here refl) (λ x₂ {}) x₁) x tt₀)
%              | inl tt))
%          | (∈-∪⁻ (cons (suc zero) [] tt)
%             (∪-⊆⁺ (λ x₁ → x₁) []⊆xs
%              (∀-cons (λ _ → there (here refl))
%               (λ x₁ → ∀-cons (λ _ → here refl) (λ x₂ {}) x₁) x tt₀)
%              | (∈-∪⁻ (cons (suc zero) (cons zero [] tt) ((λ ()) , tt))
%                 (∀-cons (λ _ → there (here refl))
%                  (λ x₁ → ∀-cons (λ _ → here refl) (λ x₂ {}) x₁) x tt₀)
%                 | inl tt))
%             | inl ((λ ()) , tt))))
%      ,
%      refl ,
%      op
%      ((λ x →
%          extend (sigd ΛₜOp (λ { base → 0 ; imp → 2 }))
%          (extend (sigd ΛₜOp (λ { base → 0 ; imp → 2 }))
%           (λ ()) tt (op (base , [])))
%          ((λ ()) , tt) (op (base , []))
%          (∪-⊆⁺
%           (λ x∈ →
%              ∪-⊆⁺ (λ { (here eq) → here eq ; (there ()) })
%              (λ x∈₁ →
%                 there
%                 (∪-⊆⁺ (λ { (here eq) → here eq ; (there ()) })
%                  (λ x∈₂ → there ((λ ()) x∈₂)) x∈₁
%                  | (∈-∪⁻ (cons zero [] tt) x∈₁ | inl tt)))
%              x∈
%              | (∈-∪⁻ (cons (suc zero) [] tt) x∈ | inl ((λ ()) , tt)))
%           (λ x₁ → there (there ((λ ()) ([]⊆xs x₁))))
%           (∀-cons (λ _ → there (here refl))
%            (λ x₁ → F.∀-cons (λ _ → here refl) (λ x₂ {}) x₁) x tt₀)
%           | (∈-∪⁻ (cons (suc zero) (cons zero [] tt) ((λ ()) , tt))
%              (∀-cons (λ _ → there (here refl))
%               (λ x₁ → F.∀-cons (λ _ → here refl) (λ x₂ {}) x₁) x tt₀)
%              | inl tt)))
%       ,
%       refl ,
%       op
%       ((λ x →
%           extend (sigd ΛₜOp (λ { base → 0 ; imp → 2 }))
%           (extend (sigd ΛₜOp (λ { base → 0 ; imp → 2 }))
%            (λ ()) tt (op (base , [])))
%           ((λ ()) , tt) (op (base , []))
%           (∪-⊆⁺
%            (λ x∈ →
%               ∪-⊆⁺ (λ { (here eq) → here eq ; (there ()) })
%               (λ x∈₁ →
%                  there
%                  (∪-⊆⁺ (λ { (here eq) → here eq ; (there ()) })
%                   (λ x∈₂ → there ((λ ()) x∈₂)) x∈₁
%                   | (∈-∪⁻ (cons zero [] tt) x∈₁ | inl tt)))
%               x∈
%               | (∈-∪⁻ (cons (suc zero) [] tt) x∈ | inl ((λ ()) , tt)))
%            (λ x₁ → there (there ((λ ()) ([]⊆xs x₁))))
%            (∀-cons (λ _ → there (here refl))
%             (λ x₁ → ∀-cons (λ _ → here refl) (λ x₂ {}) x₁) x tt₀)
%            | (∈-∪⁻ (cons (suc zero) (cons zero [] tt) ((λ ()) , tt))
%               (∀-cons (λ _ → there (here refl))
%                (λ x₁ → ∀-cons (λ _ → here refl) (λ x₂ {}) x₁) x tt₀)
%               | inl tt)))
%        ,
%        refl ,
%        var (here refl) refl ,
%        var (there (here refl)) refl , tt)
%       ,
%       _⊢_⦂_.op
%       ((λ x →
%           extend (sigd ΛₜOp (λ { base → 0 ; imp → 2 }))
%           (extend (sigd ΛₜOp (λ { base → 0 ; imp → 2 }))
%            (λ ()) tt
%            (op
%             (imp ,
%              op (base , []) ∷
%              op (base , []) ∷ [])))
%           ((λ ()) , tt) (op (base , []))
%           (∪-⊆⁺
%            (λ x∈ →
%               ∪-⊆⁺ (λ { (here eq) → here eq ; (there ()) })
%               (λ x∈₁ →
%                  there
%                  (∪-⊆⁺ (λ { (here eq) → here eq ; (there ()) })
%                   (λ x∈₂ → there ((λ ()) x∈₂)) x∈₁
%                   | (∈-∪⁻ (cons zero [] tt) x∈₁ | inl tt)))
%               x∈
%               | (∈-∪⁻ (cons (suc zero) [] tt) x∈ | inl ((λ ()) , tt)))
%            (λ x₁ → there (there ((λ ()) ([]⊆xs x₁))))
%            (∀-cons (λ _ → there (here refl))
%             (λ x₁ → ∀-cons (λ _ → here refl) (λ x₂ {}) x₁) x tt₀)
%            | (∈-∪⁻ (cons (suc zero) (cons zero [] tt) ((λ ()) , tt))
%               (∀-cons (λ _ → there (here refl))
%                (λ x₁ → F.∀-cons (λ _ → here refl) (λ x₂ {}) x₁) x tt₀)
%               | inl tt)))
%        ,
%        refl ,
%        var (here refl) refl ,
%        var (there (there (here refl))) refl , tt)
%       , tt)
%      , tt)
%     , tt)
%    , tt))))
%\end{code}

\end{document}
