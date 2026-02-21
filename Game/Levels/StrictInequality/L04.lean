import Game.Levels.StrictInequality.L03

World "StrictInequality"
Level 4

Title "Strict Inequality is not Tight"

Introduction "Show `#` is not a tight relation, that is, that we do not have that for all `x y : X`, that `¬(x # y) → m = n`, that is, inequality does not always imply equality.

For this, it is worthwhile to look at the counterexample structure, which we gained in `Theorems`. The `class` `Three` consists of a set `{x, y, z}` and a strict ordering relation on it, which we call `<ₛ` as well. The relation is given by the following:
for `a b : Three`, we have `a <ₛ b` if and only if `a = .x ∧ b = .z`. You can refer to the elements of `Three` by writing `Three.x`, or `.x` for short, if the context is clear, and `Three.y` and `Three.z` for the other two elements.

To prove the statement, think about which elements' relations in `Three` refute the positive version of the statement, and use the `have` and `unfold` tactics to make progress."

/-- States that the strict inequality defined on `Three` is not tight, that is, `x y : Three` and `¬(x # y)` does not always imply-/
TheoremDoc sineq_three_not_tight as "sineq_three_not_tight" in "Levels"


Statement sineq_three_not_tight : ¬(∀ a b : Three, ¬(a # b) → a = b) := by
  intro h
  Hint "Consider which two objects of `Three` in what order are a counterexample to the statement `{h}`. If `r` and `s` are your two elements in order, then exhibit the contradictory statement by writing `have {h}₀ := {h} r s`."
  have h₀ := h .x .y
  Hint "Try to gradually prove that the statement `{h₀}` is contradictory, potentially making use of various `have` statements."
  have h₁ : ¬Three.x#Three.y := by intro g; unfold orderIneq at g; contradiction
  have : Three.x ≠ .y := by trivial
  exact this (h₀ h₁)


NewTactic trivial
NewDefinition Three Three.x Three.y Three.z
