import Game.Levels.StrictInequality.L01

World "StrictInequality"
Level 2

Title "Strict Inequality is Symmetric"

Introduction "Show that the `#` relation is symmetric. "

/-- Strict Inequality is symmetric -/
TheoremDoc sineq_symm as "sineq_symm" in "Levels"

/-- Strict Inequality is symmetric -/
Statement sineq_symm {X : Type} [soX : SO X] {a b : X} : a # b → b # a := by
  Hint "Introduce hypothesis to break apart the goal."
  intro h
  Hint "Now, we want to 'unpack' the definition of `#` in the goal as well as in the hypothesis `{h}`. To achieve this, write `unfold orderIneq`, to unpack `#` at the `goal`, and `unfold oderIneq at `{h}`, to unpack `#` at hypothesis `{h}`. After this, we can manipulate the expression with more precision."
  unfold orderIneq
  unfold orderIneq at h
  Hint "Given the expansion of the order inequality, we now have multiple disjunctions, based on whether `x <ₛ y` or `y <ₛ x`. Use `rcases {h} with {h}₀ | {h}₁` to break apart the hypothesis `{h}` into two, and proceed from there."
  rcases h with h | h
  Hint "Now, only one of the cases in the `goal` is true, `left` respective `right` to navigate to the relevant case in the `goal`."
  · right
    exact h
  · left
    exact h


NewTactic unfold rcases left right
