import Game.Levels.StrictInequality.L01
import Game.Levels.StrictInequality.L02
import Game.Levels.StrictInequality.L03
import Game.Levels.StrictInequality.L04
import Game.Levels.StrictInequality.L05

World "StrictInequality"
Title "Strict Inequality on ℕ"

Introduction "
In this world, we construct a strict ordering, denoted by `<ₛ`, on the naturals `Nat`, which will be defined to satisfy certain axioms which we want to hold in a strict ordering. Based on this strict odering `<ₛ` we will construct a strict inequality, denoted by `#`, on the naturals `Nat`, which we will define by `m # n ↔ (m <ₛ n) ∨ (n <ₛ m)`. Finally, we will prove some foundational results about this strict inequality.
"
