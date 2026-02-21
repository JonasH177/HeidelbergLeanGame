import Game.Levels.DemoWorld.L02

World "DemoWorld"
Level 3

Title "Successor map is injective"

Introduction "Show that succ(m)=succ(n) -> m=n for any m,n natural. You have the new tactic `exact`, the theorem `congrArg` and the definition `pred`."

/-- Successor function is injective. Takes in three arguments – two naturals `m n : Nat`, and one hypothesis `h : m+1 = n+1`, which states that the successors of `m` and `n` are equal. `succ_inj m n h` evaluates to `m = n`. -/
TheoremDoc succ_inj as "succ_inj" in "Levels"


Statement succ_inj : ∀ m n : Nat, m+1 = n+1 → m = n := by
  Hint "Again, try to `intro` all the way."
  intro m n h
  Hint "Now, try to use the fact that `pred (k+1) = k` for any `k` and compose this with your hypothesis `{h}` and `congrArg`."
  exact congrArg pred h

Conclusion "This last message appears if the level is solved."

/-- Congruence in the function argument: if `a₁ = a₂` then `f a₁ = f a₂` for any (nondependent) function `f`. This is more powerful than it might look at first, because you can also use a lambda expression for `f` to prove that `<something containing a₁> = <something containing a₂>`. This function is used internally by tactics like `congr` and `simp` to apply equalities inside subterms.

`congrArg` takes two arguments – a function `f` to which the statement should apply, and a hypothesis `h' : x y`, stating equality for some `x y : α`. For instance let `g := fun (n : Nat) ↦ n+7` be a function. Then if for some naturals `m n : Nat`, we have the hypothesis `h : m = n`, then `congrArg g h` evaluates to `m+7 = n+7`.

As a hint, consider that `pred ≅ fun (n : Nat) ↦ n.pred` is a function. -/
TheoremDoc congrArg as "congrArg" in "Levels"

NewTactic exact
NewTheorem congrArg zero_ne_succ
NewDefinition pred
