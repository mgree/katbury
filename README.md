# KATbury Kreme egg: KAT rewriting using egg's e-graphs

[![Main workflow](https://github.com/mgree/katbury/actions/workflows/build.yml/badge.svg)](https://github.com/mgree/katbury/actions/workflows/build.yml)

_Kleene Algebra with Tests_ (KAT) is a powerful framework for reasoning about reactive systems: KAT generalizes regular expressions, enjoying decidable equality on complex, program-like structures. (Think "finite state machines++".)

KAT decision procedures come in two flavors: rewriting (classical, general, slow) and automata (custom-built for a concrete KAT, very fast). This repository experiments with using [egg](https://egraphs-good.github.io/)'s e-graphs to do fast and effective rewriting.
