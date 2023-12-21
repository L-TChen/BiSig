# ESOP2024 Submission 1534
## Review 1

### Overall merit

2: (strong accept (the paper must be accepted))

### Overall evaluation

The paper formalizes bidirectional typing in the generality of simply typed
languages. There are many things to like. First, everything in the paper is
formalized in nicely structured and reusable Agda code. Second, a significant
amount of folklore is made fully precise here, and in a way which reflects the
informal concepts in reasonable way. The paper is also very well-written and
well-formatted.

There's just one revision that I'd like to see: Jason Reed's "Redundancy Elimination for LF"
seems to significantly overlap with the current work, so it should be referenced and compared.
Overall I see sufficient novelty and difference, but I haven't done a detailed comparison, so I'd be interested to see such comparison from the current authors.

### Reviewer's confidence

4: (high)

### Questions for authors

- Definition 5.2. seems to imply left-to-right argument processing. I can
imagine rules where the type of an earlier argument is inferable from a later
argument. Could mode correctness be generalized to only require that some
correct order of processing exists? Additionally, we could try to find that
order mechanically during mode correctness checking.

- In practice it's common that some term former can be both checked and inferred.
For example, in checking mode we can check both branches of an if-then-else, but
in inferred mode we have to arbitrarily pick an inferred branch. How hard would
it be to support such "dual-mode" in the formalization?

### Detailed comments for authors

#### Typos & grammar

- Abstract:
"for al signatures" --> "for all signatures"

- Sec 1.
"well-typed"
"in more detail: Recall" --> "in more detail: recall"
"mode derivation for a raw term or provide" --> "mode derivation for a raw term or provides"

- Section 2.
"type annotations: Observe" --> "type annotations: observe"
(the paper uses British spelling so I guess it should use British capitalization too, which
doesn't capitalize after colon)
"is straightforward: Run" --> similarly

- Sec 3.
"uses simply typed" --> "uses the simply typed"

- Sec 4.
"related properties: By bringing"
"do better: If"
"out of the rules: Having"
"casts: Every"

- Sec 7.
"They proposes" --> "They propose"

## Review 2

### Overall merit

2: (strong accept (the paper must be accepted))

### Overall evaluation

2: (strong accept (the paper must be accepted))
In bidirectional type systems, there are two "modes" for judgments: $\Gamma \vdash t \Rightarrow A$ means that we can synthesize type $A$ for $t$ (type is an output), whereas $\Gamma \vdash t \Leftarrow A$ means that we can typecheck $t$
against type A (type is an input).

Bidirectional type systems have been widely used, but a general meta-theory was missing, and to provide such meta-theory is the aim of the paper. Their meta-theory only considers simply-typed languages, that is, types are always simple types (functional types constructed on top of some basic types), and there is a typing rule for each operator, following a generic shape where there is one premise for each subterm, and subterms could require an extended context.

The key idea is to express a bidirectional type system in two steps: the first step derives, for each context and term, just a "mode", that is, judgments of shape either $\Gamma \vdash t \Rightarrow$ or $\Gamma \vdash t \Leftarrow$
Such first step is decidable, in the sense that, given a context and a term, there is an algorithm which either constructs a derivation for $\Gamma \vdash t \Rightarrow$ , or answers that it cannot be constructed, also providing the points where type annotations are missing.

Then, in the second step, provided that typing rules are "mode-correct" (intuitively, it is possible to obtain the mode of the consequence from the modes of premises - they fully formalize this notion), then, for terms such that $\Gamma \vdash t \Rightarrow$ holds, it is decidable whether $\Gamma \vdash t \Rightarrow A$ holds for some $A$.

Definitions and results with their proofs are all implemented in Agda.

I like the paper: the key idea is very nice (more comments below), it is well-written, results look sound and there is an Agda formalization (which I appreciate, but I also appreciate a lot that they provide the proofs in mathematical notation and do not simply say "there is a proof in Agda" as it happens now in many papers).

Some criticism could be about the following points:

- the meta-theory only considers simply-typed languages, but I agree with the authors that this is much better for presentation purpose, and that the key contribution are the main ideas

- the definition of the framework (section 3.2, section 3.3, definition of mode correctness) is rather heavy and I suspect could be much simpler in the terminology of inference systems (see below).

However, in my opinion the main results of the paper, that is:

- a general definition of "bidirectional type system"

- the fact that undecidability of a type system can be nicely smoothed by a preprocessing step which says "we cannot decide tipability of this term since there are no enough annotations"

are really great and deserve acceptance.

### Reviewer's confidence

4: (high)

### Questions for authors

I wonder whether the one-to-one correspondence between meta-rules and operators is really necessary, or you could just reason on arbitrary meta-rules following the schema.

### Detailed comments for authors

I find the technical development in 3.1 and 3.2 rather heavy (too heavy for what is actually be defined, which is intuitively rather clear), and I wonder whether notions could not be expressed/explained in a much simpler way just talking about sets of meta-rules (defining the typing judgment), that is, using the terminology of inference systems, with their notions of meta-rules, rules, instantiations, proof trees.

If I understand well, you want to extract from each meta-rule 1) the set of used meta-variables 2) for each premise, the type of variables possibly added in the context, and the derived type 3) the derived type in the consequence. Is this right?
So, first of all you implicitly assume that the context can only be augmented by adding variables in the premises. This can be reasonable, even though you do not handle, e.g., linear type systems where the context of the consequence is "split" in the premises, but should be mentioned. Then, I do not see the motivation for the definition 3.4 where T is an arbitrary set (which seems to be in the relevant case the set of types constructed over the meta-variables; but then when you say "the sort of the i-th argument" it seems that a sort is a type). Also, I do not understand the sum in Definition 3.6.
Do not you need just to associate 1) + 2) + 3) to each meta-rule?

Also, you seem to assume that there is exactly one meta-rule for each syntactic operator. Is this assumption technically necessary? I am not sure, or at least I do not see clearly why.

Again, in definition 3.9, it seems that you just want to define all the proof trees in the inference system defined by the meta-rules with names in Omega (that is, proof trees constructed by instantiating the meta-variables with ground types).

Bidirectional binding arity: again, it seems that you just want to extract from a meta-rule the same as before enriched by the mode or premises/consequence, and again in Def.3.14 you just have the proof trees.

Perhaps I would avoid "abstract syntax tree" which is mainly used in the context of parsing, and just say "term".

lines below Theorem 2.5: which lemmas?

Definition 3.1 The term "variables" in type terms could be misleading since one could think to "type variables" in the sense of polymorphism, perhaps you could clarify that these are the meta-variables for types in the typing rules, and always use "type meta-variables" rather than "type variables".

Definition 3.4: you should say what is a sort (I guess, a set of type terms over some meta-variables?) . Also, I do not see the reason to define a sort as the set of type terms and not just the set of type meta-variables.
In what follows it seems that only the meta-variables matter.

Definition 3.6 what is the set O expected to be? you say "for each operation", but the arity seems to be related to a meta-rule ... so it seems that you assume that there is exactly one meta-rule for each operator? this should be stated explicitly

Also, maybe I missed it, but the $\mathcal{U}$ in the sum was never mentioned (I guess it is the universe)

#### Typos

abstract: al -> all

well typed -> well-typed (everywhere)

## Review 3

### Overall merit

0: (weak accept / borderline (the paper can be accepted))

### Overall evaluation

This paper presents a general and formal theory for bidirectional typing and an implementation for the type-checking algorithm in Agda. The theory introduces a generic representation for first-order typed languages. It splits bidirectional typing in two phases: mode annotation and the actual type checking. This allows a precise theorem statement relating declarative typing and bidirectional typing where lack of mode annotation fills the usual undecidability gap. Everything is formalised in Agda.

Pros:

- The theory is solid and it is general over type systems with simple types.

- The Agda implementation sets up a solid foundation for follow-up work.

Cons:

- The presentation of the theory (especially in Section 3) is a bit dense, and it may benefit from more examples and high-level intuitions. Maybe Section 2 takes too much space and the space could have been used in Section 3 to provide some detailed explanations.

- The limitations are not thoroughly discussed and clearly stated: Practical bidirectional typing usually involves polymorphic types and type inference, but as implied by Section 7, the theory presented in the paper cannot model type inference for System F.

- Regarding the expressiveness of the theory: It is unclear whether and how the theory supports non-deterministic typing rules. For example, in the example in Section 2, for the App rule, the type for the function is always synthesised, while the type for the argument is always checked. However, for user-friendliness, we might want an _additional_ App rule where the type for the argument is synthesised, and is in turn used to check the type for the function.

### Reviewer's confidence

4: (high)

### Questions for authors

Cor. 5.11, p. 22: "exactly one of the following holds": the judgement $\Gamma \vdash_{\Sigma,\Omega} t : A$ without a direction $d$ is used, which should mean the declarative typing judgement? In that case, I believe it is impossible that both 1 and 2 are false because the law of excluded middle is irrefutable.

### Detailed comments for authors

#### Detailed Comments:

- Ex. 3.15, p. 11: this example might provide some intuitions for the reader if presented earlier.

#### Typos and typesetting:

- Abstract, p. 1: "for <u>al</u> signatures"
- Def. 3.9, p. 10; Fig. 6, 7, and 8, p. 12; Def. 5.2, p. 17: math formulae exceeds right boundary
- Fig. 10, p. 16: rules without names

#### Highly detailed comments on the introduction:

General note: we advise the authors to revisit the comma rules, since the
submission has a severe lack of commas. Comma suggestions are not included in the
list below.

- "Dunfield and Krishnaswami summarised in their survey paper ..."
- Grammar, order. "In their survey paper, Dunfield..."
- "The basic idea of bidirectional type synthesis is that while the problem of type inference is not decidable in general, for certain kinds of terms it is still possible to infer their types (for example, the type of a variable can be looked up in the context); for other kinds of terms, we can switch to the simpler problem of type checking, where the expected type of a term is also given so that there is more information to work with."

- This is one (!) sentence that runs on and is confusing

- Suggestion: "While type inference is not decidable in general, for certain kinds of terms it is still possible to infer their types. For example, the type of a variable can be looked up in the context. Bidirectional type synthesis combines type *inference* on this subset of terms with type
*checking* (based on a given type) on the rest."

- "(...) type A is computed as output (...)"
- Pleonasm, A is an output, or A is computed

- "Dunfield and Krishnaswami present informal design principles learned from individual bidirectional type systems, but in addition to crafting special techniques for individual systems, we should also start to consolidate concepts common to a class of bidirectional type systems into a general and formal theory that gives mathematically precise definitions and proves theorems for the class of systems once and for all."

- "in addition to (...) should also": this is double, remove also

- "Such an algorithm is then accompanied by soundness and completeness assertions that the algorithm correctly synthesises the type of a raw term and every typable term can be synthesised."
- remove then
- "*algorithmic soundness, completeness, and decidability in one go*."

- What is being emphasised here? I think you meant to write "algorithmic
soundness, completeness, and decidability *in one go*."
- "In more detail: Recall that the law of excluded middle P + ¬P does not hold as an axiom for every P constructively, and we say that P is logically decidable if the law holds for P ."
- "detail: Recall": no capital for Recall
- "In more detail:" What does it add here? I would remove it
- "Since Martin-Löf type theory is simultaneously logical and computational, a decidability proof is also a proof-relevant decision procedure that computes not only a yes-or-no answer but also a proof of P or its refutation, so logical decidability is also algorithmic decidability."

- this uses also thrice.
- "In our theory, we define mode derivations so that we can explicitly take annotations into account, in particular properly formulating the type synthesis problem."
- Here it is unclear how formulating the type synthesis problem is a particular case of explicitly taking annotations into account.
- We also propose a preprocessing
- Since also is overused this entire section, this can become "In addition, we propose"
- "To give a bit more detail: The type (...)"
- See points about "In more detail: Recall (...)" above
- "(...) there is a third possibility that the term does not have sufficient annotations"
- missing namely, i.e. "there is third possibility/outcome, namely that (...)"
- "To solve the type synthesis problem (...)"
- Link with text before: "Therefore, to solve the type (...)"
- "which constructs a mode derivation for a raw term or provide information"
- provides

## Review 4

### Overall merit

1: (accept (the paper should be accepted))

### Overall evaluation

Bidirectional typing has been around for a while, and while several key ideas were effectively consolidated by the ACM Computing Surveys paper of Dunfield and Krishnaswami, that survey was relatively informal. The paper takes several properties of bidirectional type systems and makes them more general, more useful, and/or more formal.

I think the only real shortcoming is that the paper's technical development applies to a relatively narrow class of type systems (simple type systems, highly syntax-directed). This is perhaps especially a shortcoming in the setting of bidirectional typing which is so useful for type systems that are definitely not syntax-directed. On the other hand, developing these techniques for simple type systems is an important step. Moreover, apart from the metatheoretic results as such, the paper lays out some nice ideas, such as mode derivations.

I found the writing clear, modulo a few typos. Slightly more importantly, the paper would benefit with a few additional citations.

Overall, I think the paper makes an important contribution and is well worth appearing in ESOP.

### Reviewer's confidence

4: (high)

### Questions for authors

none

### Detailed comments for authors

- "Also, as we assume Axiom K, all types are legitimately sets in the sense of homotopy type theory." A citation would be helpful.

- In the discussion of Proposition 4.7 (Dunfield-Krishnaswami annotatability adapted to the present setting), the paper is perhaps too modest:

"...our completeness is much simpler to use than annotatability, which requires the bidirectional type synthesiser to produce more complex evidence when the synthesis fails."

I don't think DK annotatability says anything about evidence---a synthesiser that answered "no" could still enjoy annotatability (even if we would not enjoy that answer). Completeness is a far stronger property. (It occurs to me that another reading of the quotation is that *completeness* requires the production of more complex evidence. I do not think that reading is what the authors intended but it seems advisable to clarify.)

- "Beyond syntax-directed systems: ..." The system where the "Pfenning recipe" originated (Dunfield and Pfenning 2004), where x : (A ∧ B) ⊢ x ⇒ A and x : (A ∧ B) ⊢ x ⇒ B, is such a system. A pared-down version of that system could be a good place to start; it is "more finitary" than the possible extension to polymorphism that you discuss in Section 7, but it does not fit into your current approach (for example it violates Lemma 5.6).

- p. 3: "this reformulation is more natural and useful" I agree it is more useful. It may be more natural *once* we have mode derivations, but to say it is flat-out more natural seems quite strong.

- The citation of Harper and Licata seems intended as a citation of Twelf, but the cited paper is about applying Twelf (from its abstract: "...using LF and Twelf for formalized metatheory"), rather than about Twelf itself. The closest thing to a standard citation for Twelf itself is probably Pfenning and Schürmann 2002 ( https://link.springer.com/chapter/10.1007/3-540-48660-7_14 ).

- "stationary rule which is not..." For "stationary rule", Dunfield and Krishnaswami cite Leivant (1986), to which credit should be given (unless the authors can find an earlier citation).

- Speaking of citations, modes themselves certainly predated the DK survey paper and the authors could add some citation (DK cite Warren (1977)).

- Citation [17] is on arXiv, but is missing the arXiv identifier and hyperlink.

#### Typos and similar:

- Abstract: "al signatures"

- "we must first identify for which type variables to substitute" This may be trying to avoid "which type variables to substitute for" because it would end with a preposition, but I would have had an easier time reading the latter.

- On page 9, the hyperlink "(Definition 3.3)" goes to Definition 2.3, but seems to intend Definition 3.3.

- "They proposes"
