# Interactive Theorem Proving course

This is a course on Interactive Theorem Proving with Lean 4.

## Main features

- A main focus is on the _foundations_ of Lean. We discuss the key ideas of
the underlying type theory in a semi-formal way, aiming to provide some intuition on the inner workings.

- We follow a _bottom-up_ approach, aiming to introduce each feature of Lean
before using it. We make a few exceptions in our examples when we feel that
the reader should still be able to intuitively understand the features we
use, even when we have not yet formally introduced them.

- The course material is divided by _topic_ rather than by _lesson_. Some
files are therefore significantly longer than others.

- We suggest _exercises_ on each topic.

## How to get started with Lean 4

The material in this course can be used in several alternative ways:

- Use Lean 4 in your browser _right now_ via [Lean 4 web][lean4web]. Choose
this if you are in a hurry and do not have time to do a proper installation.
(Remember to save your code locally before closing the web page.)

- Install [Lean 4][localInstall] locally on your computer. Following the
instructions requires some time and patience, as well as some free disk
space (~10GB should be enough). Probably the best choice, once it is set up.

- Use [GitHub codespaces][codespaces] on this repository. A full Lean 4
remote server will be automatically set up for you, and you will be able to
work in your browser _and_ save your changes. Almost as good as a local
installation. Currently (in 2025) GitHub gives you 60 server hours for free
each month (more if you become a verified student). (Note that saved but
_uncommitted_ changes will be lost if a codespace is inactive for more than
30 days.)

[lean4web]: https://live.lean-lang.org/
[localInstall]: https://docs.lean-lang.org/lean4/doc/quickstart.html
[codespaces]: https://github.com/codespaces

## Lean 4 documentation

- [Lean Language Reference][lean4ref] -- the ultimate authority on Lean
  syntax, features, and tactics.
- [Mathlib4 Documentation][mathlibDoc] -- the standard library formalizing
  large areas of mathematics.
- [Theorem Proving in Lean 4][thProving] -- a convenient tutorial.
- [Mathematics in Lean][mil] -- a book on how to formalize mathematics in
  Lean.
- [Loogle][loogle] -- a search engine for the Lean libraries.
- [Cheatsheet][cheatsheet] -- a summary of the most common terms and tactics.

[lean4ref]: https://lean-lang.org/doc/reference/latest/
[mathlibDoc]: https://leanprover-community.github.io/mathlib4_docs/
[thProving]: https://lean-lang.org/theorem_proving_in_lean4/
[mil]: https://leanprover-community.github.io/mathematics_in_lean/index.html
[loogle]: https://loogle.lean-lang.org/
[cheatsheet]: Cheatsheet.md
