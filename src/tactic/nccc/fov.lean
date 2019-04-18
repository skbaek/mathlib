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

def hov_on (k : nat) : bool → term → Prop 
| ff (# m)   := k = m
| tt (# _)   := false
| _  (a & b) := hov_on ff a ∨ hov_on tt b

def hov (k : nat) : term → Prop := hov_on k ff

lemma hov_app_var (k m : nat) (a : term) :
  hov k (a & (# m)) ↔ hov k a := 
by simp only [hov, hov_on, or_false]

lemma hov_incr_idxs_ge :
  ∀ {k m : nat} (a : term), 
  m ≤ k → (hov (k + 1) (a.incr_idxs_ge m) ↔ hov k a) 
| k m (# n) h0 := 
  begin
    unfold term.incr_idxs_ge,
    by_cases h2 : m ≤ n, 
    { rw if_pos h2, 
      apply nat.succ_eq_succ },
    rw if_neg h2,
    have h3 : n < k, 
    { rw not_le at h2,
      exact lt_of_lt_of_le h2 h0 },
    apply iff_of_not_of_not _ (ne_of_gt h3),
    apply ne_of_gt (lt_trans h3 $ lt_succ_self _)
  end
| k m (a & (# n)) h0 := 
  begin
    unfold term.incr_idxs_ge,
    by_cases h2 : m ≤ n; 
    (`[rw if_pos h2] <|> `[rw if_neg h2]);
    `[ rw [hov_app_var, hov_app_var], 
       apply hov_incr_idxs_ge a h0 ]
  end
| k m (a & (b & c)) h0 := 
  begin
    apply pred_mono_2, 
    { apply hov_incr_idxs_ge a h0 },
    apply hov_incr_idxs_ge (b & c) h0
  end

def fov : nat → form → Prop
| k ⟪b, a⟫           := ¬ hov k a 
| k (form.bin _ p q) := fov k p ∧ fov k q
| k (form.qua b p)   := fov (k + 1) p

def foq (ae : bool) : form → Prop
| ⟪b, a⟫           := true
| (form.bin _ p q) := foq p ∧ foq q
| (form.qua b p)   := (ae = b → fov 0 p) ∧ foq p 

lemma fov_incr_idxs_ge : 
  ∀ {k m : nat} {p : form}, 
  m ≤ k → fov k p → fov (k + 1) (p.incr_idxs_ge m)
| k m ⟪n, a⟫ h0 h1 := 
  by { intro h2, apply h1,
       rwa hov_incr_idxs_ge _ h0 at h2 }
| k m (form.bin b p q) h0 h1 := 
  by { cases h1, constructor; 
       apply fov_incr_idxs_ge h0;
       assumption }
| k m (form.qua b p) h0 h1 := 
  by { apply @fov_incr_idxs_ge (k + 1),
       exact succ_le_succ h0, exact h1 }

lemma fov_incr_idxs {k : nat} {p : form} :
  fov k p → fov (k + 1) p.incr_idxs :=
fov_incr_idxs_ge (nat.zero_le _)

lemma fov_neg : ∀ k : nat, ∀ p : form, fov k p.neg ↔ fov k p 
| k ⟪b, a⟫           := by refl
| k (form.bin b p q) := 
  by simp only [fov, form.neg, fov_neg]
| k (form.qua b p)   := 
  by simp only [fov, form.neg, fov_neg]