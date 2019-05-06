/- Typeclass for automated proof attempts. -/

import tactic.interactive

universe u

class inductive attempt (p : Prop)
| shown (h : p) : attempt
| unknown       : attempt

def is_shown (c : Prop) [h : attempt c] : Prop :=
attempt.rec_on h (λ _, true) false

def of_is_shown {c : Prop} [h₁ : attempt c] (h₂ : is_shown c) : c :=
begin
  unfold is_shown at h₂,
  tactic.unfreeze_local_instances,
  cases h₁, apply h₁, cases h₂
end

@[reducible]

variable {α : Type u}

def attempt_pred (r : α → Prop) :=
Π (a : α), attempt (r a)

instance list.attempt_ball (p : α → Prop) [ha : attempt_pred p] :
  ∀ l : list α, attempt (∀ x ∈ l, p x)
| []        := attempt.shown (λ _ h, by cases h)
| (a :: as) :=
  begin
    cases list.attempt_ball as with h0,
    { cases ha a with h1,
      { left,
        apply (list.ball_cons p a as).elim_right,
        refine ⟨h1, h0⟩ },
      apply attempt.unknown },
    apply attempt.unknown
  end

instance list.attempt_bex (p : α → Prop) [ha : attempt_pred p] :
  ∀ l : list α, attempt (∃ x ∈ l, p x)
| []        := attempt.unknown _
| (a :: as) :=
  begin
    cases list.attempt_bex as with h0,
    { left, rcases h0 with ⟨x, h1, h2⟩,
      refine ⟨x, or.inr h1, h2⟩ },
    cases ha a with h0,
    { left, refine ⟨a, or.inl rfl, h0⟩ },
    apply attempt.unknown
  end

def attempt_ex_of_list (p : α → Prop) [ha : attempt_pred p] (as : list α) :
  attempt (∃ x, p x) :=
begin
  cases (@list.attempt_bex _ p ha as) with h0,
  { left, rcases h0 with ⟨a, _, h1⟩,
    refine ⟨a, h1⟩ },
  apply attempt.unknown
end
