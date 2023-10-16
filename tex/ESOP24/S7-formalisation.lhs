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
As we have mentioned in \Cref{sec:intro}, our theory is developed with \Agda, so the formal counterparts of our development can be used as programs directly.
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
Now we have the definition |Λ⇔D| for the bidirectional type system $(\Sigma_{\bto}, \Omega^{\Leftrightarrow})$ with |mcΛ⇔D| for its mode-correctness, so we can instantiate its type synthesiser (\cref{cor:trichotomy}) just by importing the module
\begin{code}
open import Theory.Trichotomy Λ⇔D mcΛ⇔D
\end{code}
where the type synthesiser is defined:
\begin{code}
synthesise : (Γ : Cxt) (r : Raw (length Γ)) → Dec (∃[ A ] Γ ⊢ r ⦂ A) ⊎ ¬ Pre Syn r
\end{code}
Every statement in our development so far has been formally proved constructively, so the program |synthesise|, whose correctness has been established by construction, can actually compute!

\paragraph{Running a type synthesiser}
The type of raw terms for $(\Sigma_{\bto}, \Omega^{\Leftrightarrow})$ can be imported from the module |Syntax.Typed.Raw.Term| by erasing modes from |Λ⇔D|.
\begin{code}
open import Theory.Erasure
open import Syntax.Typed.Raw.Term (erase Λ⇔D)
\end{code}

As raw terms are defined generically, they may not be convenient to manipulate directly.
We can alleviate this issue by using pattern synonyms and define raw terms in a form close to the informal presentation:
\begin{code}
infixl 8 _·_
infixr 7 ƛ_

pattern _·_ r s = op (`app , s , r , _)
pattern ƛ_  r   = op (`abs , r , _)

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
