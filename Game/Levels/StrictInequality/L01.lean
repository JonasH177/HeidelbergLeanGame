import Game.Inventory

World "StrictInequality"
Level 1

Title "Strict Inequality is Consistent"

Introduction "We will prove the foundational result that `#` is a consistent inequality."

/-- `#` is consistent, that is, `¬(x # y) ↔ ¬((x <ₛ y) ∨ (y <ₛ x))` for all `x y : X`, where `X` is a type equipped with a strict ordering (`SO`). -/
TheoremDoc sineq_consistent as "sineq_consistent" in "Levels"


Statement sineq_consistent {X : Type} [soX : SO X] {a b : X} : ¬(a # b) ↔ ¬((a <ₛ b) ∨ (b <ₛ a)) := by
  Hint "Try breaking up the double implication using a tactic"
  constructor
  Hint "In both cases, we can introduce all relevant hypothesis from the `goal`."
  · intro h
    exact h
  · intro h
    exact h


NewTactic intro constructor rw rfl exact «have»
NewTheorem orderIneq
