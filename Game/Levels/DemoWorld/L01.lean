import Game.Metadata
import Game.Inventory

World "DemoWorld"
Level 1

Title "The successor map preserves equality"

Introduction "In the first couple levels, we will prove some auxiliary results about ℕ and the successor function `Nat.succ`. Show that for any natural numbers `m` and `n`, that if `m = n`, then `m+1 = n+1`."

/-- Successor `succ` function is injective. To arrive at a equality (the rightmost term of the statement), feed it three arguments – two natural number `m : Nat` and `n : Nat`, and a hypothesis that states `h : m = n`. In Summary, this is written as `eq_imp_succ_eq m n h` and evaluates to `m+1 = n+1`.-/
TheoremDoc eq_imp_succ_eq as "eq_imp_succ_eq" in "Levels"


Statement eq_imp_succ_eq : ∀ m n : Nat, m = n → m+1 = n+1 := by
  Hint "Try to `intro`duce all relevant objects and statements from the `goal` statement, thereby breaking it apart."
  intro m n h
  Hint "Use the `rw` tactic to rewrite your `goal`. In this instance, using `rw [{h}]` completes the proof."
  rw [h]


Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

NewTactic intro rw rfl «have»

/-

World "DemoWorld"
Level 1

Title "Hello World"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."

/-- States that zero is never equal to a successor. -/
Statement (x y : Nat) (h : x = 2) (g: y = 4) : x + x = y := by
  Hint "You can either start using `{h}` or `{g}`."
  Branch
    rw [g]
    Hint "You should use `{h}` now."
    rw [h]
  rw [h]
  Hint "You should use `{g}` now."
  rw [g]

Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

NewTactic rw rfl
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
-/
