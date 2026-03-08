import Game.Metadata
-- Level 1
/-- This theorem allows you to cancel a positive multiplier from both sides of an equality in ℕ. -/
TheoremDoc Nat.mul_left_cancel as "Nat.mul_left_cancel" in "Lean"

/-- This theorem states that any non-zero natural number is positive. -/
TheoremDoc Nat.pos_of_ne_zero as "Nat.pos_of_ne_zero" in "Lean"

-- Level 2
TheoremDoc Nat.mul_one as "Nat.mul_one" in "Lean"

TheoremDoc Eq.symm as "Eq.symm" in "Lean"
TheoremDoc Dvd.dvd as "Dvd.dvd" in "Lean"

-- Level 3
/--
Multiplication is associative in ℕ.
That is, for all natural numbers a, b, and c,
  (a * b) * c = a * (b * c).
-/
TheoremDoc Nat.mul_assoc as "Nat.mul_assoc" in "Lean"

-- Level 4
/--
Multiplication is commutative in ℕ.
That is, for all natural numbers a and b,
  a * b = b * a.
-/
TheoremDoc Nat.mul_comm as "Nat.mul_comm" in "Lean"



-- Theorems proved in the Levels

/--
This theorem, proved in Level 1, states that if
  c * a = c * b
and
  0 < c,
then we can cancel c to conclude that a = b.
-/
TheoremDoc cancellation_in_Nat as "cancellation_in_Nat" in "Levels"

/--
This theorem, proved in Level 2, shows that if a number p equals the product u * v,
then p divides u * v.
-/
TheoremDoc equality_implies_divide_in_Nat as "equality_implies_divide_in_Nat" in "Levels"

/--
This theorem, proved in Level 3, establishes a substitution property:
if u = p * q and p = u * v, then p = p * (q * v).
-/
TheoremDoc substitution_in_Nat as "substitution_in_Nat" in "Levels"

/--
This theorem, proved in Level 4, shows that under the conditions
  p is prime,
  p divides a, and
  p = a * b,
the number b is a unit.
-/
TheoremDoc b_unit as "b_unit" in "Levels"

/--
This theorem, proved in Level 5, shows that if
  p is prime,
  p divides b, and
  p = b * a,
then a is a unit.
-/
TheoremDoc a_unit as "a_unit" in "Levels"

/-- This Theorem, proved in Level 6, shows that if
  p is prime,
then p is irreducible.
-/
TheoremDoc prime_is_irred as "prime_is_irred" in "Levels"


--Definitions

/-- A number n is a **unit** if
  there exists an m and k such that m * n = 1 and k * m = 1.
-/
def unit (n : Nat) : Prop :=
  (∃ m : Nat, m * n = 1) ∧
  (∃ k: Nat, n * k = 1)

/-- A number p is irreducible if
  p is not zero,
  p is not a unit and,
  whenever p = a * b, then either a or b is a unit.
-/
structure irred (p : Nat) : Prop where
  not_zero: p ≠ 0
  not_unit: ¬ unit p
  indiv: ∀ a b : Nat, a * b = p → unit a ∨ unit b

/-- A number p is prime if
  p is not zero,
  p is not a unit and
  it divides any product only when it divides at least one factor.
-/
structure prime (p : Nat) : Prop where
  not_zero: p ≠ 0
  not_unit: ¬ unit p
  Euclid: ∀ a b : Nat, p ∣ (a * b) → p ∣ a ∨ p ∣ b


/-- Level 1 -/
def cancellation_in_Nat (a b c : Nat) : (c * a = c * b) ∧ (c ≠ 0) → a = b := by
  intro h
  rcases h with ⟨ca_eq_cb , c_ne_zero⟩
  have c_pos : 0 < c := Nat.pos_of_ne_zero c_ne_zero
  exact Nat.mul_left_cancel c_pos ca_eq_cb

/-- Level 2 -/
def equality_implies_divide_in_Nat (p u v : Nat) : p = u * v → p ∣ u * v := by
  intro p_eq_uv
  dsimp only [Dvd.dvd]
  exists 1
  rewrite[Nat.mul_one p]
  exact Eq.symm p_eq_uv

/-- Level 3 -/
def substitution_in_Nat (p q u v : Nat) : (u = p * q) ∧ (p = u * v) → p = p * (q * v) := by
  intro h
  rcases h with ⟨u_eq_pq , p_eq_uv⟩
  rewrite [u_eq_pq] at p_eq_uv
  rewrite [Nat.mul_assoc] at p_eq_uv
  exact p_eq_uv

/-- Level 4 -/
def b_unit (p a b : Nat) : (prime p) ∧ (p ∣ a) ∧ (p = a * b) → unit b := by
  intro h
  rcases h with ⟨p_prime, p_dvd_a, p_eq_ab⟩
  rcases p_dvd_a with ⟨c, a_eq_pc⟩
  constructor
  · --∃ m : Nat, m * n = 1
    exists c
    have p_eq_pcb : p = p * (c * b) := substitution_in_Nat p c a b ⟨a_eq_pc, p_eq_ab⟩
    have cb_is_one : c * b = 1 := by
      conv at p_eq_pcb =>
        lhs
        rw [← Nat.mul_one p]
      apply cancellation_in_Nat (c * b) 1 p ⟨Eq.symm p_eq_pcb, p_prime.not_zero⟩
    exact cb_is_one
  · --∃ k : Nat, n * k = 1
    exists c
    have p_eq_pcb : p = p * (c * b) := substitution_in_Nat p c a b ⟨a_eq_pc, p_eq_ab⟩
    have one_is_cb : 1 = c * b := by
      apply Eq.symm
      conv at p_eq_pcb =>
        lhs
        rw [← Nat.mul_one p]
      apply cancellation_in_Nat (c * b) 1 p ⟨Eq.symm p_eq_pcb, p_prime.not_zero⟩

    rw [Nat.mul_comm]
    apply one_is_cb.symm

/-- Level 5 -/
def a_unit (p a b : Nat) : (prime p) ∧ (p ∣ b) ∧ (p = b * a) → unit a := by
  intro h
  rcases h with ⟨p_prime, p_dvd_b, p_eq_ab⟩
  rcases p_dvd_b with ⟨c, b_eq_pc⟩
  constructor
  · --∃ m : Nat, m * n = 1
    exists c
    have p_eq_pca : p = p * (c * a) := by
      exact substitution_in_Nat p c b a ⟨b_eq_pc, p_eq_ab⟩
    have ca_is_one : c * a = 1 := by
      conv at p_eq_pca =>
        lhs
        rw [← Nat.mul_one p]
      apply cancellation_in_Nat (c * a) 1 p ⟨Eq.symm p_eq_pca, p_prime.not_zero⟩
    exact ca_is_one
  · --∃ k : Nat, n * k = 1
    exists c
    have p_eq_pca : p = p * (c * a) := substitution_in_Nat p c b a ⟨b_eq_pc, p_eq_ab⟩
    have one_is_ca : 1 = c * a := by
      apply Eq.symm
      conv at p_eq_pca =>
        lhs
        rw [← Nat.mul_one p]
      apply cancellation_in_Nat (c * a) 1 p ⟨Eq.symm p_eq_pca, p_prime.not_zero⟩
    rw [Nat.mul_comm]
    apply one_is_ca.symm



/- # Inventory for Worlds two and three -/


/-- If the main goal's target type is an inductive type, `constructor` solves it with the first matching constructor, or else fails.

A goal of the form `P ∨ Q` for some propositions `P Q : Prop` can be broken apart by `constructor`, breaking apart the goal and producing two new goals – the first being `P` and the second one being `Q`. -/
TacticDoc constructor

/-- The predecessor of a natural number is one less than it. The predecessor of `0` is defined to be `0`. Can result being useful by trivially reducing `pred (n+1) = n` for some natural `n : Nat`. -/
def pred := Nat.pred

/-- The predecessor of a natural number is one less than it. The predecessor of `0` is defined to be `0`. Can result being useful by trivially reducing `pred (n+1) = n` for some natural `n : Nat`. -/
DefinitionDoc pred as "pred"


/-# Structures --- denial inequality --- strict inequality #-/

/-- Strict Ordering -/
class SO (X : Type) where
  rel : X → X → Prop
  irref : ∀n : X, ¬(rel n n)
  trans : ∀m n o : X, rel m n → rel n o → rel m o
  asym : ∀m n : X, ¬(rel m n ∧ rel n m)

infixl:70 " <ₛ " => SO.rel

/-- The strict- or order inequality, abbreviated by `#`, defined by its underlying strict ordering `<ₛ` vía `x # y ↔ (x <ₛ y) ∨ (y <ₛ x)` for any `x y : X` and `[SO X]`. You can unfold it in the goal by writing `unfold orderIneq`, or unfold it in a hypothesis `h` by writing `unfold orderIneq at h`.

Note that the meaning of `#` changes according to how `<ₛ` is defined. For the first, positive results, `<ₛ` will be just a ordinary strict ordering, given by the axioms of being
irreflexive: `∀ a : X, ¬(a <ₛ a)`,
transitive: `∀ a b c : X, a <ₛ b ∧ b <ₛ c → a <ₛ c`,
assymmetric: `∀ a b : X, ¬(a <ₛ b ∧ b <ₛ a)` -/
TheoremDoc orderIneq as "orderIneq" in "Levels"

/-- The strict- or order inequality, abbreviated by `#`, defined by its underlying strict ordering `<ₛ` vía `x # y ↔ (x <ₛ y) ∨ (y <ₛ x)` for any `x y : X` and `[SO X]`. You can unfold it in the goal by writing `unfold orderIneq`, or unfold it in a hypothesis `h` by writing `unfold orderIneq at h`.

Note that the meaning of `#` changes according to how `<ₛ` is defined. For the first, positive results, `<ₛ` will be just a ordinary strict ordering, given by the axioms of being
irreflexive: `∀ a : X, ¬(a <ₛ a)`,
transitive: `∀ a b c : X, a <ₛ b ∧ b <ₛ c → a <ₛ c`,
assymmetric: `∀ a b : X, ¬(a <ₛ b ∧ b <ₛ a)` -/
def orderIneq [soX : SO X] : X → X → Prop := fun x y ↦ (x <ₛ y) ∨ (y <ₛ x)
infixl:60 " # " => orderIneq

/-- This is a counterexample structure for a strict inequality to be neither tight, nor cotransitive.  The `class` `Three` consists of a set `{x, y, z}` and a strict ordering relation on it, which we call `<ₛ` (you can type it with '<\_s') as well. The relation is given by the following:
for `a b : Three`, we have `a <ₛ b` if and only if `a = .x ∧ b = .z`. You can refer to the elements of `Three` by writing `Three.x`, or `.x` for short, if the context is clear, and `Three.y` and `Three.Three` for the other two elements. -/
DefinitionDoc Three as "Three"

/-- The `x` element of the structure `Three`. -/
DefinitionDoc Three.x as "Three.x"
/-- The `y` element of the structure `Three`. -/
DefinitionDoc Three.y as "Three.y"
/-- The `z` element of the structure `Three`. -/
DefinitionDoc Three.z as "Three.z"

/- Proof the results are sharp by supplying counterexamples for other 'usual' properties -/
/-- This is a counterexample structure for a strict inequality to be neither tight, nor cotransitive.  The `class` `Three` consists of a set `{x, y, z}` and a strict ordering relation on it, which we call `<ₛ` (you can type it with '<\_s') as well. The relation is given by the following:
for `a b : Three`, we have `a <ₛ b` if and only if `a = .x ∧ b = .z`. You can refer to the elements of `Three` by writing `Three.x`, or `.x` for short, if the context is clear, and `Three.y` and `Three.Three` for the other two elements. -/
inductive Three where
  | x
  | y
  | z

/-- Equipping Counterexample structure with Strict Ordering -/
instance ThreeSO : SO Three where
  rel := fun m n ↦ match m with
    | .x => match n with
      | .x => False
      | .y => False
      | .z => True
    | .y => False
    | .z => False
  irref := by
    intro n
    cases n <;>
    trivial
  trans := by
    intro m n o
    cases m <;> cases n <;> cases o <;> trivial
  asym := by
    intro m n
    cases m <;> cases n <;> trivial

/-- Counterexample has decidable equality -/
instance ThreeDeq : DecidableEq Three := by
  intro m n
  cases m <;> cases n <;> first
  | right; rfl
  | left; intro; contradiction

/-- Counterexample Strict Ordering is decidable -/
instance ThreeDe (m n : Three) : Decidable (ThreeSO.rel m n) := by
  cases m <;>
  cases n <;> unfold SO.rel
  <;>
  first
  | exact instDecidableFalse
  | exact instDecidableTrue
