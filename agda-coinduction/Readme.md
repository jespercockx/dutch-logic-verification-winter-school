# Coinductive programming and proving in Agda

This repository contains the material for the course "Coinductive programming and proving in Agda" at the [2026 Dutch Winter School on Logic and Verification](https://cyclic-structures.gitlab.io/school2026/).

## Course objectives

Proof assistants based on dependent type theory such as Agda, Rocq, and Lean are typically very good at modeling inductive structures such as lists, trees, or typing derivations. However, to model structures that have cycles or are infinite, we need the lesser well-known counterpart of coinduction. In this series of three lectures, I will introduce the different ways of modeling and reasoning about coinductive structures in the Agda proof assistant, diving into many examples on the way. The lectures will be interactive and are accessible for anyone with basic knowledge of typed functional programming in a language such as Haskell or OCaml.

The course consists of three lectures:

### Lecture 1: Coinductive Programming in Agda

- Introduction to Agda
- Data types and (co)pattern matching
- Universes and polymorphism
- Dependent types
- Coinductive record types
- Mixing induction and coinduction
- Sized types

### Lecture 2: Coinductive Proving in Agda

- The Curry-Howard correspondence
- Properties of coinductive types
- The identity type and equational reasoning
- Bisimulation as a coinductive relation
- Cubical bisimulation

### Lecture 3: Coinduction Case Studies

- The delay monad and the [partiality monad](https://link.springer.com/chapter/10.1007/978-3-662-54458-7_31)
- Stream processors
- [Modeling formal languages coinductively](https://www.cse.chalmers.se/~abela/jlamp17.pdf)
- ([Wander types](https://www.nii.ac.jp/pi/n10/10_47.pdf))
- ([Coinductive graphs](https://doisinkidney.com/pdfs/formalising-graphs-coinduction.pdf))

## Installing Agda 2.8.0

### Installing a pre-built binary

There are pre-built binaries of Agda for all major platforms (Linux, MacOS, and Windows). Since version 2.8.0, this binary includes all auxiliary files needed by Agda (such as the builtin modules).

1. Download the binary corresponding to your operating system from https://github.com/agda/agda/releases/tag/v2.8.0 (you need to scroll all the way to the bottom to get to the downloads).
2. Unpack the `agda` binary to a location on your `PATH` (e.g. `/usr/bin` on Linux).
3. Run `agda --setup` to initialize the installation.

### Installing Agda from source

If you prefer, you can install Agda from source through Cabal.

1. Install GHC and Cabal via [`ghcup`](https://www.haskell.org/ghcup/).
2. On non-Windows systems, make sure `zlib` and `ncurses` are installed. For example, on Debian and Ubuntu you can run `apt-get install zlib1g-dev libncurses5-dev`.
2. Run `cabal update && cabal install Agda`.
3. Wait until the installation finishes.

### Installing a plugin for your editor

It is recommended to use either Emacs or VS Code

- **Emacs**: run `agda --emacs-mode setup`.
- **VS Code**: install the `agda-mode` plugin by Banacorn. Make sure you *disable* the experimental Agda language server!

### Installing libraries

The Agda standard library is *not* included with the installation of Agda. You can follow the [installation guide](https://github.com/agda/agda-stdlib/blob/master/doc/installation-guide.md). In brief, you need to:

- Download the library from https://github.com/agda/agda-stdlib/archive/v2.3.tar.gz and unpack it
- Create or edit the file `~/.agda/libraries` and add a line with the path to the `standard-library.agda-lib` file.
- Create or edit the file `~/.agda/defaults` to add the line `standard-library`.

The location of the `libraries` and `defaults` files might be different on your system, you can run `agda --print-agda-app-dir` to locate them.
