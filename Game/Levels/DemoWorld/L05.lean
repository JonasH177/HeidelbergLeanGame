import Game.Levels.DemoWorld.L04

World "DemoWorld"
Level 5

Title "Successor map preserves inequality"

Introduction "Now we have the necessary tools to prove the most difficult `step` in the decidability of the equality relation `=` in ℕ. Since we will (want) to prove the decidability by double case analysis on naturals `m` and `n`, we will obtain four cases based on the `inductive` pattern of `Nat`, yielding `case 0: (m,n) = (0, 0)`, `case 1: (m,n) = (0, succ)`, `case 2: (m,n) = (succ, 0)`, `case 3: (m,n) = (succ, succ)`. Since the decidability statement is given by `∀m,n ∈ ℕ, (m = n) ∨ (m ≠ n)`, the double case analysis will give us `∀m,n ∈ ℕ, (m = n) ∨ (m ≠ n) ↔ (m+1 = n+1 ∨ m+1 ≠ n+1)` in `case 3` – the final case. This final case is exactly what we will prove here.

Technically, we will only use the reverse direction (modus ponens reverse `.mpr`) of this statement in the later proofs, however it is good practice to prove the whole equivalence."

/-- States that equality between `m : Nat` and `n : Nat` is decidable if and only if the equality between `m+1` and `n+1` is decidable. Takes in two naturals `m n : Nat`, with `step m n` evaluating to `(m+1 = n+1 ∨ m+1 ≠ n+1) ↔ (m = n ∨ m ≠ n)`. Usually, when using the theorem, we will only be interested in one implication at a time, instead of the whole equivalence. Obtaining the underlying implications is achieved by grouping the statement in parenthesis and postponing `.mp`, for the forward implication ("modus ponens"), or postponing `.mpr`, for the reverse direction. Thus, `(step m n).mp` evaluates to `(m+1 = n+1 ∨ m+1 ≠ n+1) → (m = n ∨ m ≠ n)` and `(step m n).mpr` evaluates to `(m = n ∨ m ≠ n) → (m+1 = n+1 ∨ m+1 ≠ n+1)`. These are now statements that take in a hypothesis `h` of the appropriate form and return the consequence. Hence, e.g., if `h : (m+1 = n+1 ∨ m+1 ≠ n+1)`, then `(step m n).mp h` evaluates to `(m = n ∨ m ≠ n)`. -/
TheoremDoc step as "step" in "Levels"


Statement step : ∀ m n : Nat, (m+1 = n+1 ∨ m+1 ≠ n+1) ↔ (m = n ∨ m ≠ n) := by
  intro m n
  Hint "Its time to use a new tactic. We want to break apart the if and only if statement (`P ↔ Q`). This can be achieved with `constructor`. It applies the transformation `(P ↔ Q) ==> ((P → Q) ∨ (Q → P))`. This will lead you two have two goals, first the forwards implication and second the backwards implication."
  constructor
  · intro h
    Hint "If a hypothesis is of the form `P ∨ Q`, then you usually want to do case analysis on these subcases. This can be achieved with the new tactic `rcases`. The syntax for unpacking the hypothesis `{h}` is given by `rcases {h} with {h}₀ | {h}₁`. Similarly to `constructor`, it will give you two goals from your given one, one for each subcase."
    rcases h with h | h
    Hint "To navigate the disjunctions in the `goal`, you want to use the tactics `left` and `right`, which will focus on the respective part. If you for instance know that `P` is true, and you have the `goal: P ∨ Q`, then write `left`."
    · left
      exact succ_inj m n h
    · right
      Hint "You might again try the trick of making `goal` become `False` and then rewriting your assumptions such that they are trivially contradictory."
      intro h'
      rw [h'] at h
      contradiction
  · Hint "Now it is time for the second implication introduced by `constructor`."
    intro h
    rcases h with h | h
    · left
      exact eq_imp_succ_eq m n h
    · right
      exact neq_imp_succ_neq m n h

--Conclusion "This last message appears if the level is solved."

NewTactic constructor rcases left right
