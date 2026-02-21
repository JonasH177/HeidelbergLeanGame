import Game.Levels.StrictInequality.L04

World "StrictInequality"
Level 5

Title "Strict Inequality is not Cotransitive"

Introduction "Show `#` is not a cotransitive relation. Similarly to previously, you can make extensive use of `have` and `unfold`."

/-- States that `#` is not a cotransitive relation on `Three`. -/
TheoremDoc sineq_three_not_cotrans as "sineq_three_not_cotrans" in "Levels"


Statement sineq_three_not_cotrans : ¬(∀ a b c : Three, a # c → a # b ∨ b # c) := by
  intro h
  Hint "Consider what objects of `Three` in which order are a counterexample to `{h}`."
  have h₀ := h .x .y .z
  Hint "Try to gradually prove that the statement `{h₀}` is contradictory. When in editor mode (top right >_ button), then you can use the `<;>` command, which will try the following command at each subexpression of the targeted statement. For instance, `<;> trivial` tries trivial at all options. It is not necessary to use `<;>` to solve this goal quickly however."
  have h₁ : Three.x#Three.z := by unfold orderIneq; trivial
  have h₂ := h₀ h₁
  unfold orderIneq at h₂
  trivial
