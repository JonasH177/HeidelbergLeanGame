import Game.Levels.DemoWorld.L05

World "DemoWorld"
Level 6

Title "Successor map preserves inequality"

Introduction "Finally, we will now prove the main theorem, the decidability of equality in the naturals.

This can be done by doing `induction` on the variable `m`, where it is important that the induction occurs while `n` is still a **free** variable – that is, inducting over `∀ n, P n`, where `P : Nat → Prop` is some statement dependent of `n`. Then, perform case analysis with `cases` (or also possible just another `induction` instead) over the remaining variable `n`. This will be structurally similar to the proof of `step` of the last level."

/-- States that the equality relation `=` in the naturals `Nat` is decidable, that is, that for any naturals `m n : Nat`, we either have `m = n` or `¬(m = n)`<=>`m ≠ n`, that is, `(m = n) ∨ (m ≠ n)`. -/
TheoremDoc eq_dec as "eq_dec" in "Levels"


Statement eq_dec : ∀ m n : Nat, (m = n) ∨ (m ≠ n) := by
  Hint "This time, you do **not** `intro`duce the variables all the way, but ideally only `m` and leave `n` free."
  intro m
  Hint "Now, you can perform `induction m`. This will induct over the whole statement of `∀ (n : Nat), m = n ∨ m ≠ n`, which then can be attacked with case analysis."
  induction m
  case zero =>
    Hint "Now, you can `intro n` without problems."
    intro n
    Hint "Perform case analysis on `{n}`. This can be done 'cleanly' with `cases` or instead with `induction` – the difference being that `induction` will give you a 'useless' induction hypothesis later, which can however be ignored."
    cases n
    case zero =>
      left
      rfl
    case succ =>
      right
      exact zero_ne_succ n_1
  case succ =>
    Hint "Now we arrived at the case where `m` = `{n}+1` is a successor."
    intro n'
    Hint "Repeat the case analysis on `{n'}`."
    cases n'
    case zero =>
      right
      symm
      exact zero_ne_succ n
    case succ =>
      Hint "Now we've come to the point where you can reduce the goal to a simpler goal using the past theorem."
      apply (step n n_1).mpr
      exact a n_1


/-
Statement eq_dec : ∀ m n : Nat, (m = n) ∨ (m ≠ n) := by
  intro m n
  Hint "To perform case analysis over the inductive pattern of the naturals, which consists of `⟨zero, succ⟩` for `Nat`, use the tactic `cases` (in this case, `cases m` does the trick). Similarly to `constructor` and `rcases`, this will create two goals from your original goal, the first for the `zero` case, and the second for the `succ` case."
  cases m
  case zero =>
    cases n
    case zero =>
      left
      rfl
    case succ =>
      right
      exact zero_ne_succ n_1
  case succ =>
    cases n
    case zero =>
      right
      Hint "You may use the `symm` tactic to switch side of (in-)equalities. This helps bringing the goal into a form which matches established theorems."
      symm
      exact zero_ne_succ n_1
    case succ =>
      Hint "Now it has come the time to use our previous theorem! Apply it such that you reduce the `⟨{n_1}+1,{n_2}+1⟩` to the `⟨{n_1},{n_2}⟩` case.

      But how do we know that the theorem holds for `⟨{n_1},{n_2}⟩`? You can use this very theorem for it, plugging in `⟨{n_1},{n_2}⟩`! This is'nt circular reasoning, since we started with `⟨{n_1}+1,{n_2}+1⟩` and apply the result to `⟨{n_1},{n_2}⟩`. Thus, this process executes recursively and must terminate after finitely many steps, since every natural is the equal to a finitely iterated application of `succ` to `zero`."
      apply (step n_1 n_2).mpr
      exact eq_dec n_1 n_2
-/

Conclusion "Very good, you've just shown that the `=` is a decidable relation on ℕ from the ground up. You have completed the world and can continue onto other worlds."


NewTactic cases symm case induction
