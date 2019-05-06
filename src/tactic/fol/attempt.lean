universe u

class inductive attempt (p : Prop)
| shown (h : p) : attempt
| unknown       : attempt

def is_shown (c : Prop) [h : attempt c] : Prop :=
attempt.rec_on h (λ _, true) false --true false

def of_is_shown {c : Prop} [h₁ : attempt c] (h₂ : is_shown c) : c :=
begin
  unfold is_shown at h₂,
  tactic.unfreeze_local_instances,
  cases h₁, apply h₁, cases h₂
end

@[reducible]
def attempt_pred {α : Sort u} (r : α → Prop) :=
Π (a : α), attempt (r a)
