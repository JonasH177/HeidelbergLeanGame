import Game.Levels.DemoWorld.L03

World "DemoWorld"
Level 4

Title "Successor map preserves inequality"

Introduction "Show that if `m ≠ n`, then also `m+1 ≠ n+1`."


/-- Successor function preserves inequality. Takes in three arguments – two naturals `m n : Nat`, and one hypothesis `h : m ≠ n`, which states that `m` and `n` are not equal (as defined by `¬(m = n)`). `neq_imp_succ_neq m n h` evaluates to `m+1 ≠ n+1`. -/
TheoremDoc neq_imp_succ_neq as "neq_imp_succ_neq" in "Levels"


Statement neq_imp_succ_neq : ∀ m n : Nat, m ≠ n → m+1 ≠ n+1 := by
  Hint "Again, try to `intro` all the way."
  intro m n h h2
  Hint "Applying a Negation (`¬P`) to the goal `False` will result in its original form (`P`). Try to use this with `{h}`."
  apply h
  Hint "Now, the goal is closeable with the `exact` application of a result you already proved. Try to use it and pattern match your objects to it."
  exact succ_inj m n h2

Conclusion "This last message appears if the level is solved."

NewTactic apply
