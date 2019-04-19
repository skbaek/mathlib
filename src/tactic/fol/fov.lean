import .form .nat

universe u

variables {α β : Type u}

open nat

local notation `#` := term.var
local notation a `&` b := term.app a b

local notation `⟪` b `,` a `⟫` := form.lit b a
local notation p `∨*` q        := form.bin tt p q
local notation p `∧*` q        := form.bin ff p q
local notation `∃*`            := form.qua tt
local notation `∀*`            := form.qua ff

namespace term

def fov_on (k : nat) : bool → term → Prop
| ff (# m)   := k ≠ m
| tt (# _)   := true
| _  (a & b) := fov_on ff a ∧ fov_on tt b

def fov (k : nat) : term → Prop := fov_on k ff

lemma fov_app_var (k m : nat) (a : term) :
  fov k (a & (# m)) ↔ fov k a :=
by simp only [fov, fov_on, and_true]

lemma fov_incr_idxs_ge :
  ∀ {k m : nat} (a : term),
  m ≤ k → (fov (k + 1) (a.incr_idxs_ge m) ↔ fov k a)
| k m (# n) h0 :=
  begin
    unfold term.incr_idxs_ge,
    by_cases h2 : m ≤ n,
    { rw if_pos h2,
      apply not_iff_not_of_iff (nat.succ_eq_succ _ _) },
    rw if_neg h2,
    have h3 : n < k,
    { rw not_le at h2,
      exact lt_of_lt_of_le h2 h0 },
    apply iff_of_left_of_right _ (ne_of_gt h3),
    apply ne_of_gt (lt_trans h3 $ lt_succ_self _)
  end
| k m (a & (# n)) h0 :=
  begin
    unfold term.incr_idxs_ge,
    by_cases h2 : m ≤ n;
    (`[rw if_pos h2] <|> `[rw if_neg h2]);
    `[ rw [fov_app_var, fov_app_var],
       apply fov_incr_idxs_ge a h0 ]
  end
| k m (a & (b & c)) h0 :=
  begin
    apply pred_mono_2,
    { apply fov_incr_idxs_ge a h0 },
    apply fov_incr_idxs_ge (b & c) h0
  end

end term

namespace form

def fov : nat → form → Prop
| k ⟪b, a⟫           := a.fov k
| k (form.bin _ p q) := fov k p ∧ fov k q
| k (form.qua b p)   := fov (k + 1) p

lemma fov_incr_idxs_ge :
  ∀ {k m : nat} {p : form},
  m ≤ k → fov k p → fov (k + 1) (p.incr_idxs_ge m)
| k m ⟪b, a⟫ h0 h1 :=
  by { unfold fov at h1,
       rwa ← term.fov_incr_idxs_ge a h0 at h1 }
| k m (form.bin b p q) h0 h1 :=
  by { cases h1, constructor;
       apply fov_incr_idxs_ge h0;
       assumption }
| k m (form.qua b p) h0 h1 :=
  by { apply @fov_incr_idxs_ge (k + 1),
       exact succ_le_succ h0, exact h1 }

end form

def foq (ae : bool) : form → Prop
| ⟪b, a⟫           := true
| (form.bin _ p q) := foq p ∧ foq q
| (form.qua b p)   := (ae = b → p.fov 0) ∧ foq p

lemma fov_incr_idxs {k : nat} {p : form} :
  p.fov k → p.incr_idxs.fov (k + 1):=
form.fov_incr_idxs_ge (nat.zero_le _)

lemma fov_neg : ∀ k : nat, ∀ p : form, p.neg.fov k ↔ p.fov k
| k ⟪b, a⟫           := by refl
| k (form.bin b p q) :=
  by simp only [form.fov, form.neg, fov_neg]
| k (form.qua b p)   :=
  by simp only [form.fov, form.neg, fov_neg]
