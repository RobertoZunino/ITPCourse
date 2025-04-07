/-
  Welcome to the Interactive Theorem Proving course!

  In this course we will learn how to use Lean 4, a software for assisting a
  human prover with formalizing mathematics and proving theorems.

  Let's start!
-/

section Getting_started_with_Lean4
/-
  To use Lean 4 you have two main options:

  - For simple tasks, you use an online Lean editor:

    https://live.lean-lang.org/

    Warning: remember to download your files before closing the browser!

  - For a more thorough experience, install Lean 4 on your computer.

    https://docs.lean-lang.org/lean4/doc/quickstart.html

    Once Lean 4 is installed, to create an empty Lean project it should be
    enough to create a new folder and run `lake init` in it.

  In both cases, you should now have at your disposal a Visual Studio Code
  editor configured for Lean 4.

  You should now be able to open a ".lean" file (usually Basic.lean) and see
  an editor pane on your left and a "Lean Infoview" pane on your right. The
  right pane will guide us with several messages during our Lean work.
-/
end Getting_started_with_Lean4

section Sections
/-
  As you can see, Lean files can be separated into sections, providing some
  structure to the document.

  The syntax is:
-/

section Name
/- ... Contents of the section ... -/
end Name

/-
  As you can see above, sections can be nested.

  __Exercise__: try clicking on the `v` symbol on the left of the `section`
  keyword above. You probably need to hover your mouse pointer over it to
  see it. This should "fold" the section, hiding it temporarily.

    43 v   section Name
       ↑
       here
-/
end Sections

section Comments
/-
  Lean files can also contain comments like these.
  Comments can be enclosed within `/-` and `-/` delimiters.
  Alternatively, a `--` marker turns the rest of the line into a comment.
-/

-- For example, this is a single-line comment.

end Comments

section Symbols
/-
  Lean files often involve several Unicode symbols, like these:

    α β γ τ σ
    ∀ ∃ → ∧ ∨ ¬
    ℕ ℤ ℝ ℚ ℂ
    ⇒ ≫ ∘ ⟨ ⟩ Σ Π
    ∂ ∫ ∩ ∪ ⋃ ⋂ ∈
    x₁ x₂ ... xᵢ ... xₙ y¹ y² ... yⁱ ... yⁿ

  To enter these in the editor, type `\` followed by the name of the symbol.
  For instance, here is some symbol and how it is typed:

    α \alpha or \a
    β \beta or \b
    ⟨ \langle or \<
    ⟩ \rangle or \>

  Useful tip: if you hover your mouse pointer over a special symbol, Lean
  will suggest the \name to type it.

  Another tip: most names are taken from LaTeX.
-/

/-
  __Exercise__: try typing a formula involving a few symbols in a comment.
  Don't worry if it is not valid Lean syntax for now.
-/
end Symbols


section First_definitions
/-
  We can finally write some actual Lean code.

  Let's start with defining some identifier.
-/

def n: Nat := 42

/-
  The above declaration defines the identifier `n` to be the natural
  number `42`.

  There, `Nat` stands for the "type" of the natural numbers.

  Lean is based on Type Theory, and associates every valid identifier,
  variable, and expression with a "type". Informally speaking, types
  describe how their values can be produced and consumed, ensuring that all
  the operations we perform on those values are meaningful.
-/

def m: Nat := n + 1

/-
  Since `n` is a `Nat`, the expression `n + 1` is valid since addition can
  be performed on a `Nat`.
-/

section Queries
/-
  We can query Lean about the definitions above. Put you editor cursor over
  the following lines and observe the "Infoview" pane on your right.
-/

#print m   -- Prints how m was defined (`n + 1`)
#check m   -- Prints only the type of m (`Nat`)
#eval m    -- Prints the value of m (`43`)

/-
  Hovering your mouse pointer over `m` can also provide some information.

  Note 1: `#print` can only be used on identifiers. We can not `#print n+m`
  since `n+m` has no definition. (At best, we could ask for the definition
  of the addition function `Nat.add` instead.)

  Note 2: `#eval` does not work on all Lean types. Consider trying `#reduce`
  when it does not.
-/

#reduce m

end Queries

/-
  Let's try a few more definitions involving other types.
-/

def s: String       := "This is a message"
def b: Bool         := true
def p: Nat × String := (14, "hello")

/-
  The above code should be mostly self-explanatory.

  The type `String` denotes finite (possibly empty) sequences of characters
  (letters, digits, symbols, spaces, ...).

  The type `Bool` denotes the values `true` and `false`.

  The type `Nat × String` is a product type, denoting the pairs `(y, z)`
  where `y` is a `Nat` and `z` is a `String`.
-/

section Type_errors
/-
  __Exercise__: try combining the above values in a nonsensical way and
  observe the resulting Lean errors. For that, exploit the `Nat.succ`
  function that maps a natural to its successor.
-/
#eval Nat.succ m  -- Result: `44`
/-
  Note how function application in Lean is written `f arg₁ arg₂ ...` instead
  of `f (arg₁, arg₂, ...)`. (We will return to this in the future.)

  Try to use `Nat.succ` on non-naturals, like strings, booleans, pairs. Note
  how the error message reports what type was _found_ and what type was
  _expected_.
-/
end Type_errors

section Incomplete_definitions
/-
  When writing a possibly large definition it is very useful to leave some
  parts of it unfinished for the time being.

  To do that, mark the unfinished part with `sorry`.
-/

def incomplete₁: String := sorry
def incomplete₂: Nat × String := (Nat.succ sorry, sorry)

/-
  This has several benefits.

  First, the definition is accepted and only generates a _warning_ instead
  of an _error_.

  Second, when putting the cursor over each occurrence of `sorry`, Lean
  reports what is the expected type of the expression that should be
  written at that point.
-/
end Incomplete_definitions

end First_definitions
