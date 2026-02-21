import Game.Levels.DemoWorld.L01

World "DemoWorld"
Level 2

Title "Zero is not a successor"

Introduction "Show that zero can never be a successor."

/-- States that zero is never equal to a successor. Takes in a single argument – one natural number `n : Nat`. `zero_ne_succ n` returns `0 ≠ n+1`. -/
TheoremDoc zero_ne_succ as "zero_ne_succ" in "Levels"


Statement zero_ne_succ : ∀ n : Nat, 0 ≠ n + 1 := by
  Hint "Once again, try to `intro` all the way."
  intro n h
  Hint "The goal is `False`, that is we have to show that the current state -- that is, the hypotheses (in this case only `{h}`) -- are contradictory. There is a tactic for that."
  contradiction


Conclusion "This last message appears if the level is solved."

NewTactic intro contradiction
