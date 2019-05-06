/- Examples from tests.finish1 -/

import .main

section

variables {A B C D : Prop}

example : ¬ A → A → C := by leancop
example : (A ∧ A ∧ B) → (A ∧ C ∧ B) → A := by leancop
example : A → ¬ B → ¬ (A → B) := by leancop
example : A ∨ B → B ∨ A := by leancop
example : A ∧ B → B ∧ A := by leancop
example : A → (A → B) → (B → C) → C := by leancop
example : (A ∧ B) → (C ∧ B) → C := by leancop
example : A → B → C → D → (A ∧ B) ∧ (C ∧ D) := by leancop
example : (A ∧ B) → (B ∧ ¬ C) → A ∨ C := by leancop
example : (A → B) ∧ (B → C) → A → C := by leancop
example : (A → B) ∨ (B → A) := by leancop
example : ((A → B) → A) → A := by leancop
example : A → ¬ B → ¬ (A → B) := by leancop
example : ¬ (A ↔ ¬ A) := by leancop
example : (A ↔ B) → (A ∧ B → C) → (¬ A ∧ ¬ B → C) → C := by leancop
example : (A ↔ B) → ((A ∧ ¬ B) ∨ (¬ A ∧ B)) → C := by leancop
example : (A → B) → A → B := by leancop
example : (A → B) → (B → C) → A → C := by leancop
example : (A → B ∨ C) → (B → D) → (C → D) → A → D := by leancop
example : A ∨ B → B ∨ A := by leancop

section

variables (X : Type) (P Q R : X → Prop) (T : X → X → Prop) (a b : X) [inhabited X]

example : (∀ x, P x → Q x) → (∀ x, P x) → Q a := by leancop
example : (∀ x, P x → Q x) → P a → Q a := by leancop
example : ∀ a b, P a → P b → ∃ x, P x := by leancop
example : P a → P b → Q b → ∃ x, P x ∧ Q x := by leancop
example : P b → Q b → P a → ∃ x, P x ∧ Q x := by leancop
example : (∀ x, P x → Q x ∧ R x) → (∀ x, P x → R x ∧ Q x) := by leancop
example : (∃ x, P x ∧ Q x) → ∃ x, Q x ∧ P x := by leancop
example : (∃ x, ∀ y, T x y) → ∀ y, ∃ x, T x y := by leancop

end

end

section

variables a b c d : Prop

example : a ∧ b → a := by leancop
example : a → (a → b) → (b → c) ∧ (d → ¬ c) → ¬ d := by leancop
example : a ∨ b → b ∨ a := by leancop
example : ¬ (a ↔ ¬ a) := by leancop

end

section

variables (a b c : ℕ) (p q : ℕ → Prop) (r : ℕ → ℕ → Prop)
variables (P Q R : Prop)
variable  (g : bool → nat)

example : (∀ x, p x → q x) → (∀ x, p x) → q a := by leancop
example : (p a) → ∃ x, p x := by leancop
example : (p a) → (p b) → (q b) → ∃ x, p x ∧ q x := by leancop
example : (∃ x, p x ∧ r x x) → (∀ x, r x x → q x) → ∃ x, p x ∧ q x := by leancop
example : (∃ x, q x ∧ p x) → ∃ x, p x ∧ q x := by leancop
example : (∀ x, q x → p x) → (q a) → ∃ x, p x := by leancop
example : (∀ x, p x → q x → false) → (p a) → (p b) → (q b) → false := by leancop
example : (∀ x, p x) → (∀ x, p x → q x) → ∀ x, q x := by leancop
example : (∃ x, p x) → (∀ x, p x → q x) → ∃ x, q x := by leancop
example : (¬ ∀ x, ¬ p x) → (∀ x, p x → q x) → (∀ x, ¬ q x) → false := by leancop
example : (p a) → (p a → false) → false := by leancop

end

section

  variables a b c d : Prop
  variables (p q : ℕ → Prop) (r : ℕ → ℕ → Prop)

  example : (¬ (a → b ∨ c)) → (¬ (b ∨ ¬ c)) → false := by leancop
  example : (a → b ∨ c) → (¬ b) → a → c := by leancop

end

section

  variables (A : Type) [inhabited A] (r : Prop) (p : A → Prop)

  example (a : A) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by leancop
  example (a : A) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by leancop

end
