/- First-order formulas. -/

import .term

universe u

variable {α : Type u}

inductive form : Type
| lit : bool → term → form
| bin : bool → form → form → form

namespace form

def holds (M : model α) (v : nat → α) : form → Prop
| (form.lit tt a)   :=   (a.val M v []).snd
| (form.lit ff a)   := ¬ (a.val M v []).snd
| (form.bin tt p q) := p.holds ∨ q.holds
| (form.bin ff p q) := p.holds ∧ q.holds

lemma holds_bin_iff_holds_bin
  {M N : model α} {v w : nat → α} {p q r s : form} {b : bool} :
  (p.holds M v ↔ q.holds N w) → (r.holds M v ↔ s.holds N w) →
  ((form.bin b p r).holds M v ↔ (form.bin b q s).holds N w) :=
by { intros h0 h1,
     cases b; unfold form.holds;
     apply pred_mono_2; assumption }

def fam_exv (α : Type u) (p : form) : Prop :=
∀ M : model α, ∃ v : nat → α, p.holds M v

end form
