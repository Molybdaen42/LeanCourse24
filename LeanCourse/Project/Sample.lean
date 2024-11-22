/- It is fine to import all of Mathlib in your project.
This might make the loading time of a file a bit longer. If you want a good chunk of Mathlib, but not everything, you can `import Mathlib.Tactic` and then add more imports as necessary. -/
import Mathlib

/- open namespaces that you use to shorten names and enable notation. -/
open Function Set Classical

/- recommended whenever you define anything new. -/
noncomputable section

/- Now write definitions and theorems. -/

/-
**Task definition**
As an application of Galois theory:
constructible numbers have already been done in Lean,
*https://github.com/Louis-Le-Grand/Formalisation-of-constructable-numbers*,
but there is a separate notion of constructible numbers with folding/origami.
Define the numbers constructible via origami constructions
and prove that it forms a field closed under square roots and cube roots.
Stretch goal:
classify exactly these numbers (i.e. a number is origami-constructible
when there is a series of field extensions each with degree 2 or 3).
-/
