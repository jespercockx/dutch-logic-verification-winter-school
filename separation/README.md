# Program verification using concurrent separation logic

Concurrent programs are challenging to get right, especially if threads share access to memory. The formalism of "concurrent separation Logic" (which was pioneered by O'Hearn and Brookes in 2007) provides a powerful framework to verify concurrent programs. Over the last 20 years, concurrent separation Logic has emerged into an active research field, has been extended with many features (e.g., fine-grained concurrency, weak memory consistency, higher-order programs), been applied to many programming languages (e.g., Rust), and has been implemented in numerous verification tools (e.g., F*, Iris, Verifast, Viper, VST). We will discuss the foundations of separation logic and show how they scale to the verification of challenging concurrent programs. Exercises and demos using the Iris framework in the Rocq proof assistant will be provided.

## Lectures

This course consists of three lectures

- Lecture 1: Sequential separation logic
  [(lecture notes)](lectures/lecture1.md)
  [(rocq exercise 1)](https://gitlab.mpi-sws.org/iris/tutorial-popl21/-/blob/master/exercises/ex_01_swap.v)
  [(rocq exercise 2)](https://gitlab.mpi-sws.org/iris/tutorial-popl21/-/blob/master/exercises/ex_02_sumlist.v)
- Lecture 2: Concurrent separation logic
  [(slides)](lectures/lecture2.pdf)
  [(rocq exercise 3)](https://gitlab.mpi-sws.org/iris/tutorial-popl21/-/blob/master/exercises/ex_03_spinlock.v)
  [(rocq exercise 4)](https://gitlab.mpi-sws.org/iris/tutorial-popl21/-/blob/master/exercises/ex_04_parallel_add.v)
  [(rocq exercise 5)](https://gitlab.mpi-sws.org/iris/tutorial-popl21/-/blob/master/exercises/ex_05_parallel_add_mul.v)
- Lecture 3: Proving type soundness using separation logic
  [(slides)](lectures/lecture3.pdf)
  [(rocq development)](rocq_lecture3)

The Rocq exercises in Lecture 1 and 2 are part of the [Iris Tutorial @ POPL 2021](https://gitlab.mpi-sws.org/iris/tutorial-popl21/).
The [README](https://gitlab.mpi-sws.org/iris/tutorial-popl21/-/blob/master/README.md) file in the tutorial repository contains installation instructions.

## Further reading

- My MSc course [Program Verification with Types and Logic](https://gitlab.science.ru.nl/program-verification/course-2024-2025) at Radboud University Nijmegen gives a detailed account on operational semantics, type systems and separation logic in the Rocq prover. It lets you develop your own sequential separation logic (based on the heap model), using which you will verify plenty of sequential programs (by instantiating Iris Proof Mode) and a develop a simple logical relations model for a substructural type system.
- The Aarhus [Iris tutorial](https://github.com/logsem/iris-tutorial) gives a "software foundations" style introduction to the Iris framework in Rocq.
- There are plenty of short Iris tutorials, e.g., at [POPL 2020](https://gitlab.mpi-sws.org/iris/tutorial-popl20/) and [POPL 2021](https://gitlab.mpi-sws.org/iris/tutorial-popl21/). Both come with exercises in Rocq.
- The paper [A Logical Approach to Type Soundness](https://iris-project.org/pdfs/2024-jacm-logical-type-soundness.pdf) gives a thorough account of the logical approach to type systems in Iris.
- You can see the logical approach in practice for among others [Rust](https://plv.mpi-sws.org/rustbelt/popl18/paper.pdf), [session Types](https://iris-project.org/pdfs/2021-cpp-sessions-final.pdf) and [effect handlers](https://iris-project.org/pdfs/2025-popl-affect.pdf). The [Iris website](https://iris-project.org/) contains many more examples.
