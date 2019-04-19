import .pull

universe u

variables {α β : Type u}

open nat

local notation f `₀↦` a := assign a f
local infix `⬝` := value.app

local notation `#` := term.var
local notation a `&` b := term.app a b

local notation `⟪` b `,` a `⟫` := form.lit b a
local notation p `∨*` q        := form.bin tt p q
local notation p `∧*` q        := form.bin ff p q
local notation `∃*`            := form.qua tt
local notation `∀*`            := form.qua ff

@[reducible] def swap (k : nat) : sub :=
[(k, # (k + 1) & # k), (k + 1, # k)]

def form.swap (k : nat) (p : form) : form :=
p.subst (swap k)

lemma subst_swap_var (k m : nat) :
(m = k ∧ (# m).subst (swap k) = (# (k + 1) & # k)) ∨
(m = k + 1 ∧ (# m).subst (swap k) = # k) ∨
(m ≠ k ∧ m ≠ k + 1 ∧ (# m).subst (swap k) = # m) :=
begin
  by_cases h0 : m = k,
  { left, refine ⟨h0, _⟩,
    simp only [ swap, term.subst, sub.get,
      if_true, h0, eq_self_iff_true ], refl },
  by_cases h1 : m = k + 1,
  { right, left,
    refine ⟨h1, _⟩,
    simp only [ swap, term.subst, sub.get,
      if_neg h0, if_pos h1 ], refl },
  right, right,
  refine ⟨h0, h1, _⟩,
  simp only [ swap, term.subst, sub.get,
    if_neg h0, if_neg h1 ], refl
end

lemma fov_succ_succ (k m : nat) (h0 : m + 1 < k) :
  ∀ a : term, a.fov k → (a.subst $ swap m).fov k
| (# n) h1 :=
  begin
    rcases subst_swap_var m n
      with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, _, h2⟩; rw h2,
    { refine ⟨ne_of_gt h0, trivial⟩ },
    { exact ne_of_gt (lt_trans (lt_succ_self _) h0) },
    exact h1
  end
| (a & (# n)) h1 :=
  begin
    refine ⟨fov_succ_succ a h1.left, _⟩,
    rcases subst_swap_var m n
      with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, _, h2⟩;
    rw h2; try {exact trivial},
    refine ⟨ne_of_gt h0, trivial⟩,
  end
| (a & (b & c)) h1 :=
  ⟨fov_succ_succ a h1.left, fov_succ_succ (b &c) h1.right⟩

lemma fov_succ (k : nat) :
  ∀ a : term, a.fov (k + 1) → (a.subst $ swap k).fov k
| (# m) h0 :=
  begin
    rcases subst_swap_var k m
      with ⟨_, h1⟩ | ⟨h2, h1⟩ | ⟨h2, _, h1⟩;
    rw h1,
    { refine ⟨(succ_ne_self k).symm, trivial⟩ },
    { cases h0 h2.symm },
    exact h2.symm
  end
| (a & (# m)) h0 :=
  begin
    refine ⟨fov_succ _ h0.left, _⟩,
    rcases subst_swap_var k m
      with ⟨_, h1⟩ | ⟨h2, h1⟩ | ⟨h2, _, h1⟩;
    rw h1; try {exact trivial},
    refine ⟨(succ_ne_self _).symm, trivial⟩
  end
| (a & (b & c)) h0 :=
  ⟨fov_succ a h0.left, fov_succ (b &c) h0.right⟩

lemma holds_swap {M : model α} {v w : value α} {p : form} :
  ((M ₀↦ v ₀↦ w) ⊨ p.swap 0) ↔ ((M ₀↦ w ₀↦ v ⬝ w) ⊨ p) :=
begin
  unfold form.swap,
  rw holds_subst,
  have h0 : model.subst (M ₀↦ v ₀↦ w) [(0, (# 1) & (# 0)), (1, # 0)] =
            (M ₀↦ w ₀↦ v ⬝ w),
  { rw function.funext_iff,
    intro k, cases k, refl,
    cases k; refl },
  rw h0,
end

def swap_val [inhabited α] (f : value α → value α) : value α
| []        := (default α, false)
| (a :: as) := f (a ₑ) as

lemma exists_swap_val [inhabited α] {M : model α} {p : form} :
  (M ⊨ ∀* (∃* p)) → ∃ f : value α, ∀ a : α, (M ₀↦ (a ₑ) ₀↦ f ⬝ a ₑ) ⊨ p :=
begin
  intro h0,
  cases classical.skolem.elim_left h0 with f h1,
  refine ⟨swap_val f, λ a, h1 (a ₑ)⟩,
end

def eq_except (M N : model α) (k : nat) : Prop :=
(∀ m : nat, m ≠ k → M m = N m) ∧ (M k)ᵈ = (N k)ᵈ

lemma assign_eq_except_assign
  {M N : model α} {k : nat} (v : value α) :
  eq_except M N k → eq_except (M ₀↦ v) (N ₀↦ v) (k + 1) :=
begin
  intro h0, constructor,
  { intros m h1, cases m, refl,
    apply h0.left _ (λ h2, h1 _),
    subst h2 },
  exact h0.right
end

lemma val_eq_val_of_eq_except {M N : model α} {k : nat} (h0 : eq_except M N k) :
  ∀ a : term, a.fov k → (a.val M = a.val N)
| (# m)   h1 := by apply h0.left _ (ne.symm h1)
| (a & (# m)) h1 :=
  begin
    have h2 : a.val M = a.val N,
    { rw term.fov_app_var at h1,
      apply val_eq_val_of_eq_except a h1 },
    have h3 : (M m []).fst  = (N m []).fst,
    { by_cases h4 : k = m,
      { subst h4, apply h0.right },
      rw h0.left _ (ne.symm h4) },
    simp only [term.val, h2, h3]
  end
| (a & (b & c)) h1 :=
  begin
    have h2 : a.val M = a.val N,
    { apply val_eq_val_of_eq_except a h1.left },
    have h3 : (b & c).val M = (b & c).val N,
    { apply val_eq_val_of_eq_except (b & c) h1.right },
    simp only [term.val, h2, h3]
  end

lemma holds_iff_holds_of_eq_except :
  ∀ {M N : model α} {k : nat} (p : form),
  eq_except M N k → p.fov k → (M ⊨ p ↔ N ⊨ p)
| M N k ⟪b, a⟫ h0 h1 :=
  by cases b; simp [holds, val_eq_val_of_eq_except h0 a h1]
| M N k (form.bin b p q) h0 h1 :=
  begin
    cases h1,
    apply holds_bin_iff_holds_bin;
    apply holds_iff_holds_of_eq_except;
    assumption
  end
| M N k (form.qua b p)   h0 h1 :=
  begin
    apply holds_qua_iff_holds_qua, intro v,
    apply holds_iff_holds_of_eq_except _
      (assign_eq_except_assign _ h0) h1
  end

def ex_fa_swap_eqv [inhabited α] (p : form) :
  p.fov 1 → (∃* (∀* $ p.swap 0) <==α==> ∀* (∃* p)) :=
begin
  intros h0 M,
  constructor; intro h1,
  { cases h1 with v h1,
    intro w,
    refine ⟨v ⬝ w, _⟩,
    rw ← holds_swap, apply h1 },
  cases exists_swap_val h1 with f h2,
  refine ⟨f, λ v, _⟩,
  rw holds_swap,
  rw [ @holds_iff_holds_of_eq_except _
         (M ₀↦ v ₀↦ f⬝v) (M ₀↦ vᵈₑ ₀↦ f ⬝ v) 1 p _ h0,
       ← assign_app_evaluate_denote (M ₀↦vᵈₑ) f v ],
  { apply h2 },
  constructor,
  { rintros ⟨n⟩ h3, refl,
    cases m, cases (h3 rfl), refl },
  apply (denote_evaluate (vᵈ))
end

lemma neg_swap {p : form} : (p.swap 0).neg <==α==> p.neg.swap 0 :=
neg_subst _ _

def fa_ex_swap_eqv [inhabited α] (p : form) :
  p.fov 1 → (∀* (∃* $ p.swap 0) <==α==> ∃* (∀* p)) :=
begin
  intro h0,
  replace h0 := (fov_neg _ _).elim_right h0,
  have h1 : (∃* (∀* (p.swap 0).neg) <==α==> ∀* (∃* p.neg)) :=
  eqv_trans
    (qua_eqv_qua (qua_eqv_qua neg_swap))
    (@ex_fa_swap_eqv α _ _ h0),
  rw ← neg_eqv_neg,
  simp only [holds_neg.symm, form.neg, bnot, h1]
end

def swap_eqv [inhabited α] (ae : bool) {p : form} :
  p.fov 1 →
  (form.qua ae (form.qua (bnot ae) $ p.swap 0)
    <==α==> form.qua (bnot ae) (form.qua ae p)) :=
by { intro h0, cases ae,
     exact fa_ex_swap_eqv _ h0,
     exact ex_fa_swap_eqv _ h0 }

lemma fov_swap_zero_aux :
  ∀ k : nat, ∀ p : form, p.fov (k + 1) → (p.swap k).fov k
| k ⟪b, a⟫           h0 := fov_succ _ _ h0
| k (form.bin b p q) h0 :=
  by { cases h0, constructor;
       apply fov_swap_zero_aux; assumption }
| k (form.qua b p)   h0 := fov_swap_zero_aux (k + 1) p h0

lemma fov_swap_zero {p : form} :
  p.fov 1 → (p.swap 0).fov 0 :=
fov_swap_zero_aux 0 _

lemma fov_swap :
  ∀ k m : nat, m + 1 < k →
  ∀ p : form, p.fov k → (p.swap m).fov k
| k m h0 ⟪b, a⟫           h1 := fov_succ_succ _ _ h0 _ h1
| k m h0 (form.bin b p q) h1 :=
  by { cases h1, constructor;
       apply fov_swap; assumption }
| k m h0 (form.qua b p)   h1 :=
  fov_swap (k + 1) (m + 1) (succ_lt_succ h0) p h1

def swap_many (ae : bool) : form → form
| (form.qua b p) :=
  have form.size_of (p.swap 0) < form.size_of (form.qua b p),
  { unfold form.swap, rw form.size_of_subst,
    simp only [form.size_of, nat.lt_succ_self, add_comm] },
  if ae = b
  then form.qua ae (swap_many $ p.swap 0)
  else form.qua (bnot ae) (form.qua b p)
| p := form.qua (bnot ae) p

lemma fov_swap_many (ae : bool) :
  ∀ {p : form} {k : nat},
  p.fov (k + 1) → (swap_many ae p).fov k
| ⟪b, a⟫           := λ _, id
| (form.bin b p q) := λ _, id
| (form.qua b p)   :=
  have form.size_of (p.swap 0) < form.size_of (form.qua b p),
  by { unfold form.swap,
       rw form.size_of_subst,
       form.show_size_lt},
  begin
    intros k h0,
    unfold swap_many,
    by_cases h1 : ae = b,
    { subst h1, rw if_pos rfl,
      have h2 : (p.swap 0).fov (k + 2) :=
      @fov_swap (k + 2) 0
        (succ_lt_succ $ zero_lt_succ _) _ h0,
      apply @fov_swap_many _ (k + 1) h2 },
    rw if_neg h1, exact h0
  end

lemma swap_many_eqv (α : Type u) [inhabited α] (ae : bool) :
  ∀ {p : form}, p.fov 0 →
  (swap_many ae p <==α==> form.qua (bnot ae) p)
| ⟪b, a⟫           := λ _, eqv_refl _ _
| (form.bin b p q) := λ _, eqv_refl _ _
| (form.qua b p)   :=
  have form.size_of (p.swap 0) <
       form.size_of (form.qua b p) :=
  by { unfold form.swap,
       rw form.size_of_subst,
       form.show_size_lt },
  begin
    intro h0,
    unfold swap_many,
    by_cases h1 : ae = b,
    { subst h1, rw if_pos rfl,
      apply eqv_trans _ (@swap_eqv α _ ae _ h0),
      apply qua_eqv_qua,
      apply swap_many_eqv,
      apply fov_swap_zero,
      apply h0 },
    rw if_neg h1, apply eqv_refl _
  end

def swap_all (ae : bool) : form → form
| ⟪b, a⟫           := ⟪b, a⟫
| (form.bin b p q) :=
  pull (some ae) b tt (swap_all p) (swap_all q)
| (form.qua b p)   :=
  if ae = b
  then form.qua ae (swap_all p)
  else swap_many ae (swap_all p)

lemma fov_swap_all (ae : bool) :
  ∀ {k : nat} {p : form}, p.fov k → (swap_all ae p).fov k
| k ⟪b, a⟫           h0 := h0
| k (form.bin b p q) h0 :=
  by { cases h0, apply fov_pull;
       apply fov_swap_all; assumption }
| k (form.qua b p)   h0 :=
  begin
    unfold swap_all,
    by_cases h1 : ae = b,
    { subst h1, rw if_pos rfl,
      apply @fov_swap_all _ p h0 },
    rw if_neg h1,
    apply fov_swap_many,
    apply fov_swap_all,
    apply h0
  end

lemma swap_all_eqv [inhabited α] {ae : bool} :
  ∀ {p : form}, foq (bnot ae) p → (swap_all ae p <==α==> p)
| ⟪b, a⟫           h0 := eqv_refl _ _
| (form.bin b p q) h0 :=
  eqv_trans
    (pull_eqv ae b _ _ _)
    (bin_eqv_bin
      (swap_all_eqv h0.left)
      (swap_all_eqv h0.right))
| (form.qua b p)   h0 :=
  begin
    unfold swap_all,
    by_cases h1 : ae = b,
    { subst h1, rw if_pos rfl,
      apply qua_eqv_qua (swap_all_eqv h0.right) },
    have h2 := bnot_eq_iff_ne.elim_right h1,
    rw [if_neg h1, ← h2],
    apply eqv_trans (swap_many_eqv α _
      (fov_swap_all _ (h0.left h2))),
    apply qua_eqv_qua (swap_all_eqv h0.right)
end

def prenexify : form → form
| ⟪b, a⟫           := ⟪b, a⟫
| (form.bin b p q) :=
  pull none b tt (prenexify p) (prenexify q)
| (form.qua b p)   := form.qua b (prenexify p)

lemma prenexify_eqv [inhabited α] :
  ∀ p : form, prenexify p <==α==> p
| ⟪b, a⟫           := eqv_refl _ _
| (form.bin b p q) :=
  begin
    apply eqv_trans (@pull_eqv α _ _ _ _ _ _),
    apply bin_eqv_bin;
    apply prenexify_eqv
  end
| (form.qua b p)   := qua_eqv_qua (prenexify_eqv _)

def AE : form → form := prenexify ∘ swap_all ff

lemma AE_eqv [inhabited α] (p : form) :
  foq tt p → (AE p <==α==> p) :=
λ h, eqv_trans (prenexify_eqv _) (swap_all_eqv h)

def EA : form → form := prenexify ∘ swap_all tt

lemma EA_eqv [inhabited α] (p : form) :
  foq ff p → (EA p <==α==> p) :=
λ h, eqv_trans (prenexify_eqv _) (swap_all_eqv h)

def is_QF : form → Prop
| ⟪_, _⟫           := true
| (form.bin _ p q) := is_QF p ∧ is_QF q
| (form.qua b p)   := false

def is_E : form → Prop
| (∃* p) := is_E p
| p      := is_QF p

def is_AE : form → Prop
| (∀* p) := is_AE p
| p      := is_E p
