import Game.Levels.StrictInequality.L02

World "StrictInequality"
Level 3

Title "Strict Inequality is Connected"

Introduction "Show that `#` is connected, that is, that if `x # y`, then either "

/-- Strict Inequality is connected wrt. Order Inequality. -/
TheoremDoc sineq_conn as "sineq_conn" in "Levels"


/-- Strict Inequality is connected wrt. Order Inequality. -/
Statement sineq_conn {X : Type} [SO X] : ∀ a b : X, a # b → (a <ₛ b) ∨ (b <ₛ a) := by
  intro x y h
  exact h
