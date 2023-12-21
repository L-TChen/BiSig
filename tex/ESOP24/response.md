# Response

We thank the reviewers for their constructive and thoughtful comments to
improve our paper.  Given the limited time for the rebuttal period, we will
mainly answer questions specific for us, discuss common issues raised by
multiple reviewers, and respond to selected detailed comments.

## Questions for us

### Review 1

> Definition 5.2. seems to imply left-to-right argument processing. I can
> imagine rules where the type of an earlier argument is inferable from a later
> argument. Could mode correctness be generalized to only require that some
> correct order of processing exists? Additionally, we could try to find that
> order mechanically during mode correctness checking.

Yes, we can generalise the definition but we do not have to if a bidirectional
type system and its declarative typing are specified separately (with different
argument orders) and connected by an *additional* relation (instead of the mode
erasure). The relation will include a correspondence between the order of
processing and the order of premises.

Therefore, as an order of processing is specified by a bidirectional typing
rule, different orders of processing can be modelled by multiple rules. Thus,
finding that order mechanically may result in multiple bidirectional typing
rules for the same term construct, i.e. a non-syntax-directed system, which are
not dealt with in the current paper.

> In practice it's common that some term former can be both checked and
> inferred. For example, in checking mode we can check both branches of an
> if-then-else, but in inferred mode we have to arbitrarily pick an inferred
> branch. How hard would it be to support such "dual-mode" in the
> formalization?

Similarly, using two signatures to specify a bidirectional type system and a
simple type language separately should suffice to model this case, but the
specified bidirectional system is no longer syntax-directed.

We will discuss non-syntax-directed systems in the next section of our response.

### Review 2

> I wonder whether the one-to-one correspondence between meta-rules and
> operators is really necessary, or you could just reason on arbitrary
> meta-rules following the schema.

No, it is not technically necessary. Rules for raw terms, typing derivations,
and bidirectional typing derivations can all be specified independently from
different signatures and associated by some relations between them.

We will discuss non-syntax-directed systems below separately.

### Review 3

> Cor. 5.11, p. 22: "exactly one of the following holds": the judgement $\Gamma
> \vdash_{\Sigma,\Omega} t : A$ without a direction $d$ is used, which should
> mean the declarative typing judgement? In that case, I believe it is
> impossible that both 1 and 2 are false because the law of excluded middle is
> irrefutable.

Thanks for pointing this out! Indeed, the first two cases miss $\Gamma
\vdash_{\Sigma, \Omega} t \Rightarrow$ and should be the following two
statements

1. $\Gamma \vdash_{\Sigma, \Omega} t \Rightarrow$
   and $\Gamma \vdash_{\Sigma, \Omega} t : A$ 
2. $\Gamma \vdash_{\Sigma, \Omega} t \Rightarrow$
   but $\Gamma \nvdash_{\Sigma, \Omega} t : A$

respectively instead.

The mode decoration step divides raw terms into those satisfying $\Gamma
\vdash_{\Sigma, \Omega} t \Rightarrow$ and $\Gamma \nvdash_{\Sigma, \Omega} t
\Rightarrow$ and the bidirectional type synthesis divides the first class of
terms into terms satisfying $\Gamma \vdash_{\Sigma, \Omega} t : A$ and $\Gamma
\nvdash_{\Sigma, \Omega} t : A$.  The corollary is actually stronger than Def
2.1 as it provides evidence of $\neg E$ (the excuse $E$ does not hold). The
revised formalisation is given as follows:

```agda
synthesise : (Γ : Cxt 0) (r : Raw (length Γ))
           → (Pre Syn r × Dec (∃[ A ] Γ ⊢ r ⦂ A)) ⊎ ¬ Pre Syn r
synthesise Γ r with decorate Syn r
... | no ¬p = inr ¬p
... | yes p with synthesise⇔ Γ p
... | no ¬At      = inl (p , no λ (_ , t) → ¬At (_ , completeness p t))
... | yes (_ , t) = inl (p , yes (_ , soundness t))           
```

Strictly speaking, the above revised formalisation is still not precise, as the
original informal statement says *exactly* one of the three cases holds. That
is, we will need a stronger statement saying that if one of the cases holds
then the other two fail, which can be formalised in Agda as

```agda
data Tri (P : Set) (Q : Set) (R : Set) : Set where
  only-p : P → ¬ Q → ¬ R → Tri P Q R
  only-q : Q → ¬ P → ¬ R → Tri P Q R
  only-r : R → ¬ P → ¬ Q → Tri P Q R
```

Then, the trichotomy can be precisely formalised as

```agda
synthesise′
  : (Γ : Cxt 0) (r : Raw (length Γ))
  → Tri (Pre Syn r × ∃[ A ] Γ ⊢ r ⦂ A)
        (Pre Syn r × ¬ (∃[ A ] Γ ⊢ r ⦂ A))
        (¬ Pre Syn r)
synthesise′ Γ r with decorate Syn r
... | no ¬p = only-r ¬p (λ (p , _) → ¬p p) λ (p , _) → ¬p p 
... | yes p with synthesise⇔ Γ p
... | no ¬At      =
  only-q (p , λ (_ , t) → ¬At (_ , completeness p t)) (λ (_ , _ , At) → ¬At (_ , completeness p At)) (λ ¬p → ¬p p)
... | yes (_ , t) =
  only-p (p , _ , soundness t) (λ (_ , ¬At) → ¬At (_ , soundness t)) (λ ¬p → ¬p p)
```

We will revise our paper and add the above revised proofs in our formal
implementation.

### General concerns

#### Syntax-directedness

Syntax-directedness is a strong assumption, and we definitely want to deal with
non-syntax-directed systems in future work. We discuss this in a paragraph
‘Beyond syntax-directed systems’ on p25, which is rather condensed however, and
probably not easy to understand. 

The following is an expanded version of the paragraph:

> To explore more general settings, an extreme possibility is to independently
> specify an ordinary type system and a bidirectional one over the same raw
> terms and then investigate possible relationships between the two systems.
>
> However, a more practical setting suitable for a next step is probably this:
> for each raw term construct, there can be several ordinary typing rules, and
> each typing rule can be refined to several bidirectional typing rules with
> different mode assignments and different orders of premises. Even for this
> setting, there is already more work to do: both the mode decorator and the
> bidirectional type synthesiser will have to backtrack, and become more
> complex. For soundness and completeness, it should still be possible to treat
> them as the separation and combination of mode and type information, but the
> completeness direction will pose a problem—for every node of a raw term, a
> mode derivation chooses a mode assignment while a typing derivation chooses a
> typing rule, but there may not be a bidirectional typing rule for this
> particular combination. There should be ways to fix this problem while
> retaining the mode decoration phase—for example, one idea is to make the mode
> decorator produce all possible mode derivations, and refine completeness to
> say that any typing derivation can be combined with one of these mode
> derivations into a bidirectional typing derivation.
>
> We could also focus on simpler cases first where each construct has exactly
> one typing rule, but each typing rule can be refined to more than one
> bidirectional typing rule, e.g. the dual-mode for `if-then-else`. In such
> cases, the mode decorator would need to find all possible mode derivations,
> but the type synthesiser should still work in a syntax-directed manner on
> each mode derivation as input. And completeness could still take the simple
> form presented in this paper too.

#### Section 3 is dense

We agree that Section 3 is rather dense as we also have admitted at the
beginning of the section.  We will try to squeeze more space for Section 3 to
include more examples and intuitive explanations as suggested by R2 and R3.

## Response to selected comments

> There's just one revision that I'd like to see: Jason Reed's "Redundancy
> Elimination for LF" seems to significantly overlap with the current work, so
> it should be referenced and compared.

Thanks for mentioning this paper to us. We will check this paper and compare it
with our approach in the next revision.

### Review 2

> below Theorem 2.5: which lemmas?

Sorry, it should be Theorem 2.5.

> Then, I do not see the motivation for the definition 3.4 where T is an
> arbitrary set (...).

This makes the Definition 3.6 shorter and allows us to introduce Example 3.5
earlier. In our early drafts, the notion of arities was not defined separately,
making Definition 3.6 longer and (in our opinion) less readable.

The notion of (unsorted) binding arities at least dates back to Aczel's 1978
manuscript (as mentioned in the introduction). The definition, we believe, is
standard and has been used by Fiore and Hur (2010) and Fiore Szamozvancev
(2022). (We will cite Fiore and Hur's paper in our next revision to give them
credit.)

- Marcelo Fiore and Chung-Kil Hur, Second-order equational logic (extended
  abstract), Computer Science Logic. CSL 2010, LNCS, vol. 6247, Springer Berlin
Heidelberg, 2010.

- Marcelo Fiore and Dmitrij Szamozvancev, Formal metatheory of second-order
  abstract syntax, Proceedings of the ACM on Programming Languages 6 (2022),
no. POPL, 1–29.

> Also, you seem to assume that there is exactly one meta-rule for each
> syntactic operator. Is this assumption technically necessary? I am not sure,
> or at least I do not see clearly why.

See our response about syntax-directedness.

> Definition 3.6 what is the set O expected to be? you say "for each
> operation", but the arity seems to be related to a meta-rule ... so it seems
> that you assume that there is exactly one meta-rule for each operator? this
> should be stated explicitly

The set $O$ has been used for the set of term constructs and names for
(bidirectional) typing rules. Indeed, to specify the set of raw terms we only
need an unsorted binding signature which could be introduced first or defined
as a (sorted) binding signature with the singleton set $\top$ as its sort.
Then, we would need to introduce some relations to associate each term
construct with various typing rule and bidirectional typing rules. This would
allow us to formulate a non-syntax-directed system properly at the cost of more
definitions in Section 3.

> Definition 3.4: you should say what is a sort (I guess, a set of type terms
> over some meta-variables?) . Also, I do not see the reason to define a sort
> as the set of type terms and not just the set of type meta-variables. In what
> follows it seems that only the meta-variables matter.

A sort is just a type/set. We will clarify it in our next revision.

> Also, I do not understand the sum in Definition 3.6.

The set of binding arities allowed for each operation $o : O$ consists of pairs
of a type $\Xi$ and a binding arity with a set $Ty(\Xi)$ (which depends on the
first component).

> Also, maybe I missed it, but the $\mathcal{U}$ in the sum was never mentioned
> (I guess it is the universe)

Yes, you are right -- it is the universe of types.

### Review 3

> Fig. 10, p. 16: rules without names

It was intended. We will add names for them, as it seems to cause confusion
unnecessarily.

### Review 4

> I don't think DK annotatability says anything about evidence---a synthesiser
> that answered "no" could still enjoy annotatability (even if we would not
> enjoy that answer)....

We should expand on what we mean by ‘more complex evidence’. When using a
bidirectional type synthesiser to implement a type synthesiser—in Theorem 2.4,
for example—if the bidirectional type synthesiser concludes that there does not
exist a bidirectional typing derivation, we use the contrapositive form of
completeness to establish that there does not exist an ordinary typing
derivation either. Now, annotatability (Proposition 4.7) is a kind of
completeness because (roughly speaking) it also turns an ordinary typing
derivation into a bidirectional typing derivation. Therefore it is conceivable
that we could use annotatability in place of completeness in the proof of
Theorem 2.4. However, in the contrapositive form of annotatability, the
antecedent is ‘there does not exist t’ that’s more annotated than t and has a
bidirectional typing derivation’, which is the ‘more complex evidence’ that the
bidirectional type synthesiser would have to produce.

> . 3: "this reformulation is more natural and useful" I agree it is more
> useful.

We will remove the word "natural".

> On page 9, the hyperlink "(Definition 3.3)" goes to Definition 2.3, but seems
> to intend Definition 3.3.

Thanks for pointing out. It appears to be a bug of the LNCS format, but we will
see if we can fix the link manually. (The link is generated by the command
`\cref` and we have checked that these two definitions have different labels.)

