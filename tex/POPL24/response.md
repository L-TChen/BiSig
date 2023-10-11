# Main response

We thank all the reviewers for the time and effort they put into this paper.

(At least) reviewers B & C agree with us that developing a general theory of bidirectional type synthesis is an important direction; if so, there should be a paper at POPL that says so! There are, however, two main concerns raised by reviewers A & B (which we had ourselves actually):

1. There doesn’t seem to be enough ‘delta’ from previous work on bidirectional typing, in particular Dunfield & Krishnaswami’s [2021]. 

2. The work should’ve treated (or at least discussed) type systems beyond simple types.

We will address these concerns below, but first here’s a summary:

1. A general theory is important for further scientific development, and is more difficult to work out than individual instances. We offer mathematical definitions, theorems, and proofs (which we believe the POPL community values and sometimes even requires) in contrast to Dunfield & Krishnaswami’s informal treatment. And the delta from existing language formalisation frameworks (where the most complex operation is usually substitution) should be taken into account too. 

2. A theory about simple types is the best we can do now, because the development hinges on the state-of-the-art techniques used in language formalisation frameworks, which basically deal with simple types only. It is conceivable to extend the theory to more expressive types, but that will have to start from extending language formalisation frameworks, which is substantial work by itself.

We will revise the paper to make the delta clearer, and include more discussion on how we may extend the theory to more expressive types — see the detailed response section below.

Regarding the concern about delta, first allow us to point out that developing a general theory (even if it doesn’t do much at the beginning) is a significant step forward from having knowledge and experience about individual instances. Being able to write a type-synthesiser (or parser) generator means that the knowledge and experience gained from writing individual type synthesisers (or parsers) has matured to the point that general patterns have been identified and precisely formulated, and can be studied further. For example, when writing individual type synthesisers, it suffices to have just a vague idea of mode-correctness, but without a mathematically precise formulation of mode-correctness, it’s impossible to explore its consequences rigorously, for example the fact that the uniqueness of synthesised types follows from mode-correctness (Lemma 5.5 at L746), which was not made clear before. And general theorems are more difficult to prove: a case in point is the op case in the proof of Theorem 5.6 (L828), which is significantly more complex than the concrete cases for STLC or PCF, for example (but captures the general pattern once and for all).

For a comparison with Dunfield & Krishnaswami’s paper in particular: Their paper is more like reflection from experience working with individual type systems (there are intuitive phrases like type system, but no rigorous definitions or general theorems etc). That’s nice to have, but we shouldn’t let our knowledge about type synthesis remain in that state — it is important to consolidate that knowledge and experience into a general theory to enable further scientific development. And it’s not that we’re just formalising Dunfield & Krishnaswami’s paper: mode decoration is new and leads to a nicer specification of type synthesis (the trichotomy). We expect the theory of bidirectional typing to evolve further, but the improvements should start to be accumulated and studied within general theories rather than scattered in a myriad of type systems.

The delta from previous work on language formalisation frameworks should be taken into account too. We mentioned in Section 1.1.2 that most of the existing language formalisation frameworks (including Fiore and Szamozvancev’s distinguished paper at POPL 2022) do not provide operations beyond substitution, offering few incentives to use or extend these frameworks. This is an unfortunate situation that we should change by demonstrating that we can do significantly larger-scale constructions, such as a generic bidirectional type synthesiser, with these frameworks, and that there is a clear need to extend these frameworks to deal with more expressive types (see the discussion about simple types below).

Regarding the concern about simple types being too simple: we also mentioned in Section 1.1.2 that the existing language formalisation frameworks basically support simple types only; our development depends on, and is restricted by, the progress there, but there is no reason to wait for such frameworks to cover polymorphic types with subtyping etc before initiating a general theory of bidirectional typing — there are orthogonal notions such as mode-correctness and mode decoration that we can treat now. It is conceivable that the theory can be scaled up to more expressive type systems, but that’s ‘highly non-trivial’ as reviewer A suspects — in particular, that would have to start with the development of a more expressive language formalisation framework, which is too much work for a paper about bidirectional typing. On the other hand, we agree with reviewer A that there should be more discussion about a ‘path towards extending the framework’; a sample is provided at the end of the detailed response (the ‘Path’ section).

# Detailed response

## Review A

> How hard do you expect it would be to support a wider range of languages? In particular, what about languages with polymorphism or dependent types?

See the ‘Path’ section below. 

> 25-26: "However, it was later found that full" -> "However, full" (later?)

Will fix it!  
> I'm not sure section 7 adds much value to the paper, given that the formalization is available.

We admit that it does not add much to the theory itself, but it might be worthwhile to share with the interested reader how the formal definition is inspired through a category-theoretic analysis (especially the idea of Hermida and Jacobs), especially that our definitions contain a rule schema which is unusual in a typical definition for a single language (as the set of term constructs are usually fixed a priori). Defining this rule schema actually took us some effort to engineer working definitions, e.g. a lifting of a signature functor. 

> Section 8 also does not feel super useful: … Alternatively, you could try to explain why the extensions you discuss are actually challenging, highlighting, e.g., what part of your formalization would break.

Yes, thanks for the suggestion. It is clear that further developments are necessary, so we’d like to outline the path towards extensions further, as detailed below. 

## Review B

> Can you provide some more intuition on how you would expect to scale the approach to richer type systems, such as System F or, especially, F<:?

See the ‘Path’ section below. 

> "bidirectional typing has only been developed on a case-by-case basis without a theory" I found it reasonably clear what is meant in context, but statements like this can come across as uninformed and perhaps inflammatory

Thanks for pointing this out. We will revise it to avoid unnecessary misunderstanding. A slightly revised sentence below might do: 

‘… on a case-by-case basis without a general theory’

or an even longer version

‘the design of bidirectional typing has been developed based on the experience and properties we have accumulated from individual systems, without the support of a mathematical theory that works generally for all languages like parsing.’

## Review C

> Can your formalization be used to actually synthesize types, albeit inefficiently?

Yes! Please normalise the term `⊢S?` defined at L122 in the file `src/Example/STLC.agda` in our supplementary material.

> In the supplementary material, README.agda promises an HTML rendering of the code that does not seem to be present.

Sorry, we forgot. We’ve now attached it as part of the response.

> L320: Why don't you assert here that $\Xi$ has decidable equality? Is it because this hypothesis isn't needed until much later (L793, L829)?

Yes, you’re right. $\Xi$ doesn’t need to have decidable equality until Section 5.2.

> L1021: Our formal construction appears novel" To me this idea is strongly reminiscent of the idea of Melliès and Zeilberger that …

Interesting, we will have a look.

We will address other detailed comments in our next revision.

## ‘Path towards extending the framework’ (Reviews A&B)

> How hard do you expect it would be to support a wider range of languages? 

> Can you provide some more intuition on how you would expect to scale the approach to richer type systems, such as System F or, especially, F<:? 

We lightly touched this question in Section 7 and will outline our plan further in the revision. In short, to extend our theory with additional language features, we have (at least) three key steps to follow:

1. Extending algebraic theories: We need to extend the algebraic theory of abstract syntax with variable binding to accommodate more language features or complex types.

2. Transforming theory to framework: the next objective is to transform the extended algebraic theory into a language-formalisation framework that is formally verified and implemented within a proof assistant.

3. Identifying conditions for bidirectional type synthesis: it is necessary to identify the  conditions, beside mode-correctness, to establish a decidable bidirectional type synthesiser for more complex languages. 

The first step involves the development of more advanced algebraic theories capable of expressing a wider range of languages. Such an algebraic theory alone could already be worthy of publication in reputable conferences in theoretical computer science. For instance, Fiore et al. [1999], Fiore & Hamana [2013], Arkor & Fiore's Algebraic models of simple type theories [2020] have explored algebraic theories of abstract syntax with variable binding in various directions and published their results all in LICS.

The second task involves making the mathematical arguments of the chosen algebraic theory constructive and amenable to formalisation within a type-theoretic proof assistant. Being constructive and type-theoretic allows theorems compute like ours, but this step can be highly non-trivial. Some statements may need substantial reformulation for the purpose of formalisation. For example, Fiore & Szamozvancev [2022] wrote a whole paper presenting a mathematical reformulation of the syntax/representation-independent presheaf model of variable binding for formalisation in Agda, based on Fiore et al. [1999].

The third step involves identifying the mathematical conditions for bidirectional type synthesis. This is the main focus of this paper.

Each step towards a more general theory of bidirectional type synthesis is further exemplified below by polymorphic and dependent types separately.

### Polymorphism and subtyping

When it comes to polymorphic types and subtyping, the current polymorphic algebraic theory, as presented by Fiore & Hamana [2013], is sufficient in expressing polymorphic typed languages like System F. However, it does not include subtyping (F<:), which is far more interesting. To address this, we intend to expand the algebraic theory by introducing a partial order between types. This extension can be achieved by augmenting the concept of type signature with an ordering apart from type variable binding. Here's what we require:

1. Extending the notion of arity for type constructs: The extended arity is represented as a finite list of numbers, denoting the binding of type variables. This is already in the Fiore & Hamana’s theory.

2. Specifying ordering between type constructs: The type signature must also include a subtyping ordering for type constructs.

3. Establishing decidability conditions (optional): It is crucial to identify and establish the sufficient conditions to ensure that the induced ordering between types is decidable. This step generalises the decidable equality check between types in our case, but we may simply assume it.

Several mathematical concepts need to be formulated subsequently. These include a construction of its syntactic model, (generic) renaming/substitution, a syntactic construction of terms, and term recursion/induction. Additionally, we must ensure that the extended theory includes intended languages, such as F<:, as instances. The notion of term signatures will need to be enriched with modes, which is expected to be relatively straightforward.

However, it remains uncertain how challenging the formalisation of the extended theory within a type-theoretic framework will be.

Once we establish an algebraic theory of polymorphic languages with subtyping, we will be well-equipped to study their bidirectional typing. This foundation will enable us to define, say, the concept of principal types for those formally defined language specifications.

One of the primary challenges in designing a bidirectional type synthesis for polymorphic typed languages is tackling the ‘instantiation problem’. This problem involves solving for $B$ in expressions of the form $\forall \alpha. A \mathrel{<:} A[B/\alpha]$, as discussed in Section 5 of Dunfield & Krishnaswami's paper. Unfortunately, there is no universally accepted, canonical solution to this problem. Instead, various competing approaches exist. Therefore, our task is to formulate a set of conditions for language specifications. These conditions will serve as criteria, ensuring that any solution to the instantiation problem aligns with them. Meeting these conditions will be a prerequisite for the derivation of bidirectional typing synthesis.

Following these steps shall allow us to have a verified type-synthesiser generator for bidirectionally and polymorphically typed languages with subtyping like ours for simple types. 

### Dependent types

Developing an algebraic theory for dependently typed languages with a notion of signature is more challenging. It is known that Cartmell's generalized algebraic theory and categories with families can model dependent type theories like Martin-Löf type theory and variants of modal type theories, as demonstrated in Daniel Gratzer's recent PhD thesis, among others (as initial models in the corresponding categories of algebraic models). However, unlike simple types and polymorphic types, type and term signatures have to be conflated. In dependent type theory, contexts, types, terms, and equations are interdependent, making mere ‘signatures’ insufficient. Instead, we need to embrace the concept of a ‘stratified presentation’ as shown by Bezem et al. [2021]. 

Bezem et al. offer a syntax-independent development and a syntactic construction, in line with the stratified presentation. It's already challenging to ascertain its direct correspondence to a type-theoretic construction. Given the inherent complexity of formalising a dependent type theory, transforming such an algebraic theory into a language-formalisation framework becomes even more daunting.

An alternative in this research direction is Kaposi et al.'s POPL'19 paper 'Constructing quotient inductive-inductive types'. They explore the concept of signatures for quotient inductive-inductive types (QIIT) instead and construct corresponding languages from given (dependent) signatures. Notably, Altenkirch & Kaposi's POPL'16 paper previously showed that QIIT is also able to express Martin-Löf type theory. However, progress beyond (dependent) term recursion/induction and substitution in this formalisation has been limited. We have not evaluated these two approaches, but nevertheless, we believe that both frameworks hold potential for expressing bidirectional dependent type theories.

To synthesis types for terms in a dependent type theory, though, a crucial requirement is a decidable type conversion mechanism, which is a substantial undertaking. One common implementation is achieved through normalisation by evaluation (NbE). NbE has been developed for various type theories, but pattern haven’t yet been formally stated. It's currently unclear how a decidable NbE can be derived in a generic manner, as some rules such as Equality Reflection in extensional type theory are clearly taboos. That is, we shall find out what properties of typing rules make the type equality check decidable. A general theory of bidirectional type synthesis for dependent types is possible, only if generic NbE is established.
