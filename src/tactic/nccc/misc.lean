import tactic.ext

variables {α β γ δ : Type}

lemma prod.snd_map (f : α → β) (g : γ → δ) (x : α × γ) :
  (x.map f g).snd = g x.snd := 
by {cases x with a c, refl}

lemma prod.snd_comp_map (f : α → β) (g : γ → δ) :
  prod.snd ∘ (prod.map f g) = g ∘ prod.snd := 
by {ext x, apply prod.snd_map}

def update (m : nat) (a : α) (v : nat → α) : nat → α
| n := if n = m then a else v n

local notation v `{` m `↦` a `}` := update m a v

def update_zero (a : α) (f : nat → α) : nat → α
| 0     := a
| (k+1) := f k

meta def list_reflect [has_reflect α] (l : list α) : list expr :=
l.map (λ x, `(x).to_expr)

local notation f `₀↦` a := update_zero a f

lemma fun_mono_2 {p : α → β → γ} {a1 a2 : α} {b1 b2 : β} :
  a1 = a2 → b1 = b2 → (p a1 b1 = p a2 b2) :=
λ h1 h2, by rw [h1, h2]

lemma pred_mono_2 {p : α → β → Prop} {a1 a2 : α} {b1 b2 : β} :
  a1 = a2 → b1 = b2 → (p a1 b1 ↔ p a2 b2) :=
λ h1 h2, by rw [h1, h2]

lemma pred_mono_2' {c : Prop → Prop → Prop} {a1 a2 b1 b2 : Prop} :
  (a1 ↔ a2) → (b1 ↔ b2) → (c a1 b1 ↔ c a2 b2) :=
λ h1 h2, by rw [h1, h2]
