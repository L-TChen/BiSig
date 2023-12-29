# A Formal Treatment of Bidirectional Typing

## Introduction

This is the repository for the development presented in the
paper *A formal treatment of bidirectional typing*.

Here is the abstract from the paper:

> There has been much progress in designing bidirectional type systems and associated type synthesis algorithms, but mainly on a case- by-case basis. To remedy the situation, this paper develops a general and formal theory of bidirectional typing and as a by-product of our formalism provides a verified generator of proof-relevant type synthesisers for simply typed languages: for every signature that specifies a mode- correct bidirectionally typed language, there exists a proof-relevant type synthesiser that for an input abstract syntax tree constructs a typing derivation if any, gives its refutation if not, or reports that the input does not have enough type annotations. Soundness, completeness, and mode- correctness are studied universally for all signatures, which are sufficient conditions for deriving a type synthesiser. We propose a preprocessing step called mode decoration, which helps the user to deal with missing type annotations in a given abstract syntax tree. The entire development is formalised in Agda and can be further integrated with other language- formalisation frameworks.

## Structure

This repositary consists of the following directories and files.

- `README.agda` is a walkthrough of the formal implementation with mappings to the paper.
- `src/` is the formal implementation in Agda.
  - `src/Example/STLC.agda` contains the example of simply typed lambda calculus presneted in the Appendix *Demonstration* of the paper.
- `tex/` is the tex source code for the paper including
  all submissions, reviews, and our responses; especially important is
  - `tex/ESOP24/revised/BiSig.pdf` the revisied version of the paper.
- `docs/` is the listing of source code published [here](https://l-tchen.github.io/BiSig/README.html)
- `agda-stdlib/` is a copy of Agda's standard library v2.0 (as a Git submodule)
- ...


## Requirements

To type-check the formal implementation, you need

- OS: Linux, macOS, or Windows with [`WSL`](https://learn.microsoft.com/en-us/windows/wsl/install) 
- `Agda`: verion 2.6.4.1
  - (An earlier version compatible with the standard library `2.0` may still work)

### Agda

Should you have no `Agda` installed or fail to check `README.agda` with an earlier version Agda, you may

- Install [`Agda 2.6.4.1`](https://agda.readthedocs.io/en/v2.6.4.1/getting-started/installation.html), or
- Use [containerised](https://hub.docker.com/r/ltchentw/agda/) `Agda 2.6.4.1` based on [Docker](https://www.docker.com).

## Instructions

To browse and check this repository locally, please follow the instructions below.

0. Open a terminal emulator

1. Clone this repository (in the terminal)

```bash
git clone --depth 1 --recurse-submodules --shallow-submodules https://github.com/L-TChen/BiSig.git
```

This repositary contains Agda's standard library as a Git submodule, so it is necessary to clone not only this repository but also the submodule.

2. Change the working directory to the local repository

```bash
cd [the location of your copy of this repo]
```

3. (Optional) If you have no `Agda` but [Docker](https://www.docker.com/products/docker-desktop/), you may use [containerised `Agda`](https://hub.docker.com/r/ltchentw/agda) instead:

```bash
docker run -it --mount type=bind,source"=${PWD}",destination=/BiSig -w /BiSig ltchentw/agda:2.6.4.1
```
This command pulls the pre-built image which contains `Agda 2.6.4.1` and run it as a container with the current working directory mounted at `/BiSig/` inside the container.

4. Type check the walk-through file
```bash
agda README.agda
```

5. Use an editor that supports the Agda development to browse `README.agda`.
