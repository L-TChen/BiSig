POPL 2024 Paper #104 Reviews and Comments
===========================================================================
Paper #104 A Theory of Bidirectional Type Synthesis for Simple Types


Review #104A
===========================================================================

Overall merit
-------------
C. Weak reject: I lean towards rejection.

Reviewer expertise
------------------
X. Expert: I am an expert on the topic of the paper (or at least key
   aspects of it).

Summary of the paper
--------------------
The paper introduces a general theory of bidirectional type synthesis for simply-typed languages (no polymorphism, no dependent types), that is formulated as a *type-synthesiser generator* implemented in Agda.
To produce a type-synthesiser, the user must provide a bidirectional type system specification (Σ, Ω) consisting of:
(1) a type signature Σ specifying the syntax of types of the language,
(2) a *bidirectional binding signature* Ω over Σ specifying compactly the syntax of terms, the typing rule associated to each term constructor, and the modes (checking/inference) for the premises and the conclusion.
If such a specification (Σ, Ω) additionally satisfies a well-formedness criterion called mode-correctness, the generator produces a *mode decorator*, a type-checker and a type-synthesiser having the expected properties by construction.
In particular, the mode decorator is used to decide whether a given term is sufficiently annotated for synthesis to be decidable (and hence sound and complete).
If the mode decorator fails, the user must add annotations, and if it succeeds, then either synthesis constructs an appropriate type (soundness) or it proves that no type can possibly be correct (completeness).

Supplementary material includes an Agda formalization of most of the paper.

Assessment of the paper
-----------------------
Overall, the paper is reasonably well-written and entertaining, and I found the idea of extracting a type-synthesiser generator from a formal proof interesting (although it is in parts inspired by pre-existing work as far as I understand).
My main issue with the paper, though, is that the contributions do not feel very substantial, mostly due to the limitation to simply-typed languages.
Sure, the framework deals with such language in a generic fashion (and there are some interesting tricks used, like using a mode decorator), but designing a bidirectional type-system for any given simply-typed language is not really challenging, and we've know how to deal with such systems for a long time.
I would not be as bothered if there was a clear path towards extending the framework to support languages with, say, polymorphism, but I believe that such extension would be highly non-trivial.

Another more minor issue that I have with the paper is that it is quite dense in term of formal definitions (as admitted by the authors at the start of section 3).
In particular, there are lots of layers of definitions, and a good deal of back and forth is required from the reader (including for examples).
I feel like there should be more discussion, motivation, and intuition given for each definition, to keep readers (especially non-experts) involved and interested.
Space could be made for that by, e.g., shortening or removing sections 7 and 8, which I do not find very useful (see below).

Detailed comments for authors
-----------------------------
25-26: "However, it was later found that full" -> "However, full" (later?)

I'm not sure section 7 adds much value to the paper, given that the formalization is available.
Even you seem unconvinced by it, since you tell the reader they "may feel free to skip this section".

Section 8 also does not feel super useful: I would turn it into a small paragraph discussing limitations.
Alternatively, you could try to explain why the extensions you discuss are actually challenging, highlighting, e.g., what part of your formalization would break.

Questions to be addressed by author response
--------------------------------------------
How hard do you expect it would be to support a wider range of languages?
In particular, what about languages with polymorphism or dependent types?



Review #104B
===========================================================================

Overall merit
-------------
C. Weak reject: I lean towards rejection.

Reviewer expertise
------------------
X. Expert: I am an expert on the topic of the paper (or at least key
   aspects of it).

Summary of the paper
--------------------
This paper is motivated by the observation that, given a formal grammar, there are theories and tools to derive a viable parser -- but given the formal rules of a type system, there are no comparable tools to derive a viable type checker. 

In particular, the paper aims to automatically generate bidirectional type checkers that combine type synthesis and checking components. 

Like in parsing, where parser generators typically require forms of non-ambiguous grammars, the paper also puts some restrictions on the kind of type systems that are accepted as inputs: specifically, only syntax-directed type systems are supported, and only simple types, i.e., no subtyping or quantified types.

Given an appropriate formal type system, the paper presents a theoretical framework and the core of an algorithm (implemented in Agda) to produce bidirectional typing rules from the regular typing derivations. The paper demonstrates this on simply-typed lambda calculus, along with some variants (incl PCF).

In doing so, the paper largely follows the steps outlined by Dunfield and Krishnaswami '21, and also Wadler's textbook chapter (also mechanized in Agda). Several of the relatively informal notions of Dunfield and Krishnaswami are made formal in the present paper.

Assessment of the paper
-----------------------
I like the direction of this paper. Theory and tool support for constructing semantic artifacts such as type checkers are an important line of research.

And while the paper could have been clearer in some aspects (e.g. the large background & related work section before discussing the contributions of this present paper) I found it overall quite pleasant to read.

What I'm less clear about is the significance of the presented work, and especially the delta over the state of the art. Dunfield and Krishnaswami '21 is the most obvious piece of related work here, but bidirectional type systems really have been studied for a long time, and how to make simple type systems bidirectional is well understand.

While the theoretical framework is appealing, it is really only applied to variations of the simply typed lambda calculus, and there isn't much discussion on how the approach might scale further, e.g. to systems with subtyping and/or parametric types (see e.g. "Colored Local Type Inference" Odersky et al 2001).

Detailed comments for authors
-----------------------------
The structure of the paper would be improved quite significantly by stating the contributions as a concise bullet list right in the intro, and moving related work to the end of the paper, while discussing background "just-in-time" where needed.

"bidirectional typing has only been developed on a case-by-case basis without a theory" I found it reasonably clear what is meant in context, but statements like this can come across as uninformed and perhaps inflammatory - clearly there are ample theoretical foundations for bidirectional typing, and while realistic type checkers tend to be built on a case-by-case basis, it's not the case that developers of such tools proceed without plan.

Questions to be addressed by author response
--------------------------------------------
Can you provide some more intuition on how you would expect to scale the approach to richer type systems, such as System F or, especially, F$<:$?



Review #104C
===========================================================================

Overall merit
-------------
A. Strong accept: I will argue for acceptance.

Reviewer expertise
------------------
X. Expert: I am an expert on the topic of the paper (or at least key
   aspects of it).

Summary of the paper
--------------------
As the title aptly states, this paper develops a general theory of bidirectional type synthesis for simple type systems such as STLC and PCF, formalized in Agda. The authors begin by defining a notion of syntax-directed bidirectional type systems; the syntax-directed restriction ensures that every raw term has a unique mode at which it may be typed. Using this fact, the authors introduce the concept of "mode decoration", a decision procedure which determines whether a raw term has enough annotations to potentially synth (resp., check) a type, although it may fail to do so. The main result of the paper is that in any suitable bidirectional type system, for every synth-worthy raw term it is decidable whether it synthesizes a type. When combined with mode decoration, we conclude that every raw term either synthesizes a type, fails to synthesize a type, or is not synth-worthy.

Assessment of the paper
-----------------------
Bidirectional type systems seem to be in the air right now, for good reason: they have proven very successful at operationalizing declarative type systems. But perhaps not surprisingly for a concept that emerged from the depths of folklore, there has been little work on mathematically defining bidirectionality, or proving general theorems about bidirectional type systems. I am therefore quite happy to see this paper.

The presentation of the paper is very high-quality: the paper starts with a motivating example and then introduces its key ideas in a handful of sections of manageable length. The order of exposition is well-chosen, and every detail is included, as one might expect from a paper that was deformalized from Agda code.

I have a few minor critiques. There are some places where the paper is needlessly fussy about details, most notably Definition 5.1 ("set of synthesized type variables") which computes precisely what is on the tin but is described by a notationally-heavy and uninteresting recursive definition. And Section 3 defines its main concepts using both text and inference rules that have the same meaning. (Why?) In fact, overall I felt that Section 3 was just some fairly standard representation of a type system spelled out in full detail with modes added throughout, although I concede that the representation must be fixed before proceeding with the rest of the paper.

Detailed comments for authors
-----------------------------
In the supplementary material, `README.agda` promises an HTML rendering of the code that does not seem to be present.

L211: The "excuse" terminology peters out after this section; it might be nice to mention it again later on.

L387: The phrasing is odd here. (Why "is formed by"? Why "and" rather than "or"?) And given the way you have written the other definitions, I wonder why you didn't simply write $(V\times Ty_\Sigma(\emptyset))^*$.

L320: Why don't you assert here that $\Xi$ has decidable equality? Is it because this hypothesis isn't needed until much later (L793, L829)?

L942: The conclusion of the rule should read $\mu x.t$.

L1021: "Our formal construction appears novel" To me this idea is strongly reminiscent of the idea of Melliès and Zeilberger that "functors are type refinement systems", coupled with the idea of Hermida and Jacobs. This is not to say that it has already been done.

L1270: This citation has suffered a mishap.

Questions to be addressed by author response
--------------------------------------------
You have formalized a number of decision procedures, but you never mention actually running the formalization. Can your formalization be used to actually synthesize types, albeit inefficiently?
