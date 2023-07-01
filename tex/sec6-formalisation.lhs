%!TEX root = BiSig.tex

\documentclass[BiSig.tex]{subfiles}

%include agda.fmt
%format → = "\mathop\to"
%format ⦃ = "\{\kern-.9pt\vrule width .75pt height 7.125pt depth 1.975pt\kern-1.5pt"
%format ⦄ = "\kern-1.5pt\vrule width .75pt height 7.125pt depth 1.975pt\kern-.9pt\}"
%format ℕ = "\mathbb{N}"
%format Ξ = "\Xi"
%format ⊢ = "\vdash"
%format ι = "\iota"
%format Set₁ = Set "_1"
%format constructor = "\Keyword{constructor}"

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
  \begin{code}
  record ArgD (Ξ : ℕ) : Set where
    field
      cxt    : Cxt Ξ
      mode   : Mode
      type   : TExp Ξ

  ArgsD : ℕ → Set
  ArgsD Ξ = List (ArgD Ξ)

  record ConD : Set where
    constructor ι
    field
      {vars}   : ℕ
      mode     : Mode
      type     : TExp  vars
      args     : ArgsD vars

  record Desc : Set₁ where
    constructor desc
    field
      Op          : Set
      ⦃ decOp ⦄   : DecEq Op
      rules       : Op → ConD
  \end{code}
  \caption{Definition of Bidirectional Binding Signature}  
\end{figure}

\end{document}
