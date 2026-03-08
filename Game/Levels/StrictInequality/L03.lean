import Game.Levels.StrictInequality.L02

World "StrictInequality"
Level 3

Title "Strict Inequality is Connected"

Introduction "Show that `#` is connected (see [here](https://en.wikipedia.org/wiki/Connected_relation)), that is, that if `x # y`, then either `x <ₛ y` or `y <ₛ x`."

/-- Strict Inequality is connected wrt. Order Inequality. -/
TheoremDoc sineq_conn as "sineq_conn" in "Levels"


/-- Strict Inequality is connected wrt. Order Inequality. -/
Statement sineq_conn {X : Type} [soX : SO X] : ∀ a b : X, a # b → (a <ₛ b) ∨ (b <ₛ a) := by
  intro x y h
  exact h
