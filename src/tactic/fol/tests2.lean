
import .main tactic.finish

meta def x01 : expr := `(forall A B C D : Prop, ¬ A → A → C)
meta def x02 : expr := `(forall A B C D : Prop, (A ∧ A ∧ B) → (A ∧ C ∧ B) → A)
meta def x03 : expr := `(forall A B C D : Prop, A → ¬ B → ¬ (A → B))
meta def x04 : expr := `(forall A B C D : Prop, A ∨ B → B ∨ A)
meta def x05 : expr := `(forall A B C D : Prop, A ∧ B → B ∧ A)
meta def x06 : expr := `(forall A B C D : Prop, A → (A → B) → (B → C) → C)
meta def x07 : expr := `(forall A B C D : Prop, (A ∧ B) → (C ∧ B) → C)
meta def x08 : expr := `(forall A B C D : Prop, A → B → C → D → (A ∧ B) ∧ (C ∧ D))
meta def x09 : expr := `(forall A B C D : Prop, (A ∧ B) → (B ∧ ¬ C) → A ∨ C)
meta def x10 : expr := `(forall A B C D : Prop, (A → B) ∧ (B → C) → A → C)
meta def x11 : expr := `(forall A B C D : Prop, (A → B) ∨ (B → A))
meta def x12 : expr := `(forall A B C D : Prop, ((A → B) → A) → A)
meta def x13 : expr := `(forall A B C D : Prop, A → ¬ B → ¬ (A → B))
meta def x14 : expr := `(forall A B C D : Prop, ¬ (A ↔ ¬ A))
meta def x15 : expr := `(forall A B C D : Prop, (A ↔ B) -> (A ∧ B → C) → (¬ A ∧ ¬ B → C) → C)
meta def x16 : expr := `(forall A B C D : Prop, (A ↔ B) -> ((A ∧ ¬ B) ∨ (¬ A ∧ B)) → C)
meta def x17 : expr := `(forall A B C D : Prop, (A → B) → A → B)
meta def x18 : expr := `(forall A B C D : Prop, (A → B) → (B → C) → A → C)
meta def x19 : expr := `(forall A B C D : Prop, (A → B ∨ C) → (B → D) → (C → D) → A → D)
meta def x20 : expr := `(forall A B C D : Prop, A ∨ B → B ∨ A)

meta def x21 : expr := `(forall (X : Type) (P Q R : X → Prop) (T : X → X → Prop) (a b : X) (h : inhabited X), (∀ x, P x → Q x) → (∀ x, P x) → Q a)
meta def x22 : expr := `(forall (X : Type) (P Q R : X → Prop) (T : X → X → Prop) (a b : X) (h : inhabited X), (∀ x, P x → Q x) → P a → Q a)
meta def x23 : expr := `(forall (X : Type) (P Q R : X → Prop) (T : X → X → Prop) (a b : X) (h : inhabited X), ∀ a b, P a → P b → ∃ x, P x)
meta def x24 : expr := `(forall (X : Type) (P Q R : X → Prop) (T : X → X → Prop) (a b : X) (h : inhabited X), P a → P b → Q b → ∃ x, P x ∧ Q x)
meta def x25 : expr := `(forall (X : Type) (P Q R : X → Prop) (T : X → X → Prop) (a b : X) (h : inhabited X), P b → Q b → P a → ∃ x, P x ∧ Q x)
meta def x26 : expr := `(forall (X : Type) (P Q R : X → Prop) (T : X → X → Prop) (a b : X) (h : inhabited X), (∀ x, P x → Q x ∧ R x) → (∀ x, P x → R x ∧ Q x))
meta def x27 : expr := `(forall (X : Type) (P Q R : X → Prop) (T : X → X → Prop) (a b : X) (h : inhabited X), (∃ x, P x ∧ Q x) → ∃ x, Q x ∧ P x)
meta def x28 : expr := `(forall (X : Type) (P Q R : X → Prop) (T : X → X → Prop) (a b : X) (h : inhabited X), ∃ x : X, (P x → (∀ y : X, P y)))
meta def x29 : expr := `(forall (X : Type) (P Q R : X → Prop) (T : X → X → Prop) (a b : X) (h : inhabited X), (∃ x : X, x = x) → ∃ x, ((∃ y, P y) → P x))
meta def x30 : expr := `(forall (X : Type) (P Q R : X → Prop) (T : X → X → Prop) (a b : X) (h : inhabited X), (∃ x, ∀ y, T x y) → ∀ y, ∃ x, T x y)

meta def x31 : expr := `(forall (a b c d : Prop), a ∧ b → a)
meta def x32 : expr := `(forall (a b c d : Prop), a → (a → b) → (b → c) ∧ (d → ¬ c) → ¬ d)
meta def x33 : expr := `(forall (a b c d : Prop), a ∨ b → b ∨ a)
meta def x34 : expr := `(forall (a b c d : Prop), ¬ (a ↔ ¬ a))

meta def x35 : expr := `(forall (a b c : ℕ) (p q : ℕ → Prop) (r : ℕ → ℕ → Prop) (P Q R : Prop) (g : bool → nat), (∀ x, p x → q x) → (∀ x, p x) → q a)
meta def x36 : expr := `(forall (a b c : ℕ) (p q : ℕ → Prop) (r : ℕ → ℕ → Prop) (P Q R : Prop) (g : bool → nat), (p a) → ∃ x, p x)
meta def x37 : expr := `(forall (a b c : ℕ) (p q : ℕ → Prop) (r : ℕ → ℕ → Prop) (P Q R : Prop) (g : bool → nat), (p a) → (p b) → (q b) → ∃ x, p x ∧ q x)
meta def x38 : expr := `(forall (a b c : ℕ) (p q : ℕ → Prop) (r : ℕ → ℕ → Prop) (P Q R : Prop) (g : bool → nat), (∃ x, p x ∧ r x x) → (∀ x, r x x → q x) → ∃ x, p x ∧ q x)
meta def x39 : expr := `(forall (a b c : ℕ) (p q : ℕ → Prop) (r : ℕ → ℕ → Prop) (P Q R : Prop) (g : bool → nat), (∃ x, q x ∧ p x) → ∃ x, p x ∧ q x)
meta def x40 : expr := `(forall (a b c : ℕ) (p q : ℕ → Prop) (r : ℕ → ℕ → Prop) (P Q R : Prop) (g : bool → nat), (∀ x, q x → p x) → (q a) → ∃ x, p x)
meta def x41 : expr := `(forall (a b c : ℕ) (p q : ℕ → Prop) (r : ℕ → ℕ → Prop) (P Q R : Prop) (g : bool → nat), (∀ x, p x → q x → false) → (p a) → (p b) → (q b) → false)
meta def x42 : expr := `(forall (a b c : ℕ) (p q : ℕ → Prop) (r : ℕ → ℕ → Prop) (P Q R : Prop) (g : bool → nat), (∀ x, p x) → (∀ x, p x → q x) → ∀ x, q x)
meta def x43 : expr := `(forall (a b c : ℕ) (p q : ℕ → Prop) (r : ℕ → ℕ → Prop) (P Q R : Prop) (g : bool → nat), (∃ x, p x) → (∀ x, p x → q x) → ∃ x, q x)
meta def x44 : expr := `(forall (a b c : ℕ) (p q : ℕ → Prop) (r : ℕ → ℕ → Prop) (P Q R : Prop) (g : bool → nat), (¬ ∀ x, ¬ p x) → (∀ x, p x → q x) → (∀ x, ¬ q x) → false)
meta def x45 : expr := `(forall (a b c : ℕ) (p q : ℕ → Prop) (r : ℕ → ℕ → Prop) (P Q R : Prop) (g : bool → nat), (p a) → (p a → false) → false)

meta def tests : list expr :=
[ x01, x02, x03, x04, x05, x06, x07, x08, x09, x10,
  x11, x12, x13, x14, x15, x16, x17, x18, x19, x20 ]
  -- x21, x22, x23, x24, x25, x26, x27, x28, x29, x30 ]
  --x31, x32, x33, x34, x35, x36, x37, x38, x39, x40,
  --x41, x42, x43, x44, x45 ]

open tactic

meta def batch_test (t : tactic unit) : nat → list expr → tactic unit
| _   []          := tactic.triv
| idx (exp::exps) :=
  ( (do gs ← tactic.get_goals,
       g ← tactic.mk_meta_var exp,
       tactic.set_goals (g::gs), t) <|>
    (trace (("Failed ex " : format) ++ format.of_nat idx) >> tactic.skip)) >>
  batch_test (idx+1) exps

set_option profiler true

example : true :=
by do batch_test leancop 1 tests

#exit

#exit
section



end

end

section

variables a b c d : Prop


end

section

variables (a b c : ℕ) (p q : ℕ → Prop) (r : ℕ → ℕ → Prop) (P Q R : Prop) (g : bool → nat)


end

section

  variables a b c d : Prop
  variables (p q : ℕ → Prop) (r : ℕ → ℕ → Prop)

  example : (¬ (a → b ∨ c)) → (¬ (b ∨ ¬ c)) → false := by leancop
  example : (a → b ∨ c) → (¬ b) → a → c := by leancop

end
