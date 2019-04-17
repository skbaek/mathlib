import .list .logic .misc

universe u 

variables {α β : Type u}

def assign (a : α) (f : nat → α) : nat → α
| 0     := a
| (k+1) := f k

local notation f `₀↦` a := assign a f

def value (α : Type u) : Type u := list α → (α × Prop)

def value.default [inhabited α] : value α := 
λ as, (default α, false)

def model (α : Type u) : Type u := nat → value α

@[derive has_reflect, derive decidable_eq]
inductive atom : Type
| var : nat → atom
| app : atom → atom → atom

local notation `#` := atom.var
local notation a `&` b := atom.app a b

def atom.incr_idxs_ge (k : nat) : atom → atom
| (# m) := if k ≤ m then # (m + 1) else # m
| (a & b) := a.incr_idxs_ge & b.incr_idxs_ge  

def atom.incr_idxs : atom → atom := atom.incr_idxs_ge 0


/- sub -/

@[reducible] def sub : Type := list (nat × atom)

namespace sub

--@[reducible] def domain : sub → list nat := list.map prod.fst
--
--@[reducible] def range : sub → list atom := list.map prod.snd

open list

@[reducible] def incr_idxs : sub → sub := 
map (prod.map nat.succ (atom.incr_idxs))

def get (k : nat) : sub → option atom 
| []            := none 
| ((m, a) :: σ) := if k = m then a else get σ 

lemma get_eq_of_ne {k m : nat} (a : atom) (σ : sub) : 
  k ≠ m → sub.get k ((m, a) :: σ) = sub.get k σ :=
by {intro h0, simp only [get, if_neg h0]}

end sub

--lemma in_domain_of_is_some_get (k : nat) :
--  ∀ σ : sub, (σ.get k).is_some → k ∈ σ.domain 
--| []            h0 := by cases h0
--| ((m, a) :: σ) h0 :=
--  begin
--    by_cases h1 : k = m,
--    { left, simp only [h1] },
--    right, apply in_domain_of_is_some_get,
--    simpa only [sub.get, h1, if_false] using h0,
--  end

--lemma in_range_of_get_eq_some {k : nat } {a : atom} :
--  ∀ {σ : sub}, (σ.get k) = some a → a ∈ σ.range := sorry 

lemma get_zero_incr_idxs :
  ∀ σ : sub, σ.incr_idxs.get 0 = none 
| []            := rfl
| ((m, a) :: σ) :=
  begin
    have h0 : sub.get 0 (sub.incr_idxs ((m, a) :: σ)) = 
              sub.get 0 (sub.incr_idxs σ),
    { apply sub.get_eq_of_ne,
      apply (ne.symm $ nat.succ_ne_zero _) },
    rw h0, apply get_zero_incr_idxs,
  end

lemma get_succ_incr_idxs (k : nat) : 
  ∀ σ : sub, σ.incr_idxs.get (k + 1) = atom.incr_idxs <$> (σ.get k)
| []            := rfl
| ((m, a) :: σ) := 
  begin
    by_cases h0 : k = m,
    { have h1 : sub.get (k + 1) (sub.incr_idxs ((m, a) :: σ)) = 
                some a.incr_idxs,
      { simp only [sub.get, sub.incr_idxs, if_true,
        prod.map, list.map, eq_self_iff_true, h0], refl },
     have h2 : atom.incr_idxs <$> sub.get k ((m, a) :: σ) = 
               some a.incr_idxs, 
     { simp only [sub.get, sub.incr_idxs, if_true, 
       prod.map, list.map, eq_self_iff_true, h0], refl },
     simp only [h1, h2] },
    have h1 : sub.get (k + 1) (sub.incr_idxs ((m, a) :: σ)) = 
              sub.get (k + 1) (sub.incr_idxs σ), 
    { simp only [sub.get, sub.incr_idxs, if_false, prod.map,
     list.map, eq_self_iff_true, not.imp h0 nat.succ_inj] },
    have h2 : atom.incr_idxs <$> sub.get k ((m, a) :: σ) = 
              atom.incr_idxs <$> sub.get k σ,
    { simp only [sub.get, sub.incr_idxs, if_false, 
      prod.map,list.map, eq_self_iff_true, h0] },
    simp only [h1, h2, get_succ_incr_idxs σ]
  end

--lemma get_eq_of_ne {k m : nat} {a : atom} {σ : sub} 
--  k ≠ m → sub.get k ((m, a) :: σ) = sub.get k σ :=
--by {intro h0, unfold get, rw if_neg h0}



  


namespace atom

lemma eq_of_var_eq_var {k m : nat} : (# k) = (# m) → k = m :=
by {intro h0, cases h0, refl}

def val (M : model α) : atom → value α
| (# k)   := M k
| (a & b) := a.val ∘ list.cons (b.val []).fst

def subst (σ : sub) : atom → atom
| (# k)   := (σ.get k).get_or_else (# k)
| (a & b) := subst a & subst b

lemma subst_eq_of_get_eq_none {σ : sub} {k : nat} :
  σ.get k = none → (# k).subst σ = # k :=
by {intro h1, simp only [h1, option.get_or_else, atom.subst]}

lemma subst_eq_of_get_eq_some {σ : sub} {k : nat} {a : atom} :
  σ.get k = some a → (# k).subst σ = a :=
by {intro h1, simp only [h1, option.get_or_else, atom.subst]}

--lemma subst_var_cases (k m : nat) (a : atom) (σ : sub) :
--  subst ((k, a) :: σ) (# m) = a ∨ 
--  subst ((k, a) :: σ) (# m) = subst σ (# m) := 
--begin
--  by_cases h0 : m = k,
--  { left, subst h0, simp [subst, sub.get], refl },
--  right, simp [subst, sub.get_eq_of_ne h0]
--end

-- lemma eq_or_in_range {k : nat} {a : atom} {σ : sub} :
--   (# k).subst σ = a → (a = (# k) ∨ a ∈ σ.range) := sorry


-- lemma of_subst_var_eq {k m : nat} {a b : atom} {σ : sub} :
--   subst ((k, a) :: σ) (# m) = b →  
--   ((k = m) ∧ a = b) ∨ (subst σ (# m) = b) :=
-- begin
--   intro h0, 
--   by_cases h1 : m = k,
--   { left, subst h1, refine ⟨rfl, _⟩, 
--     simpa only [subst, sub.get, if_true, eq_self_iff_true] using h0 },
--   right,
--   simpa only [subst, sub.get_eq_of_ne h1] using h0 
-- end

lemma incr_idxs_app (a b : atom) : 
  incr_idxs (a & b) = (incr_idxs a & incr_idxs b) := 
by simp [incr_idxs, incr_idxs_ge]

lemma val_assign_incr_idxs (M : model α) (v : value α) :
  ∀ a : atom, val (M ₀↦ v) a.incr_idxs = val M a 
| (# k)   := rfl
| (a & b) := 
  by simp only [val, val_assign_incr_idxs a, 
     val_assign_incr_idxs b, incr_idxs_app]

end atom

namespace model

def subst (M : model α) (σ : sub) : model α :=
λ k : nat,
match σ.get k with
| none   := M k
| some a := a.val M
end

lemma subst_eq_of_get_eq_none
  (M : model α) {σ : sub} {k : nat} :
  σ.get k = none → M.subst σ k = M k :=
by {intro h1, simp only [h1, model.subst]}

lemma subst_eq_of_get_eq_some
  (M : model α) {σ : sub} {k : nat} {a : atom} :
  σ.get k = some a → M.subst σ k = a.val M :=
by {intro h1, simp only [h1, model.subst]}

end model

namespace atom

local notation `#` := atom.var
local notation a `&` b := atom.app a b

lemma val_subst (M : model α) (σ : sub) :
  ∀ a : atom, val M (a.subst σ) = val (M.subst σ) a
| (# k) :=
  begin
    rw function.funext_iff, intro as,
    cases h1 : σ.get k with s,
    simp only [val, atom.subst_eq_of_get_eq_none h1,
      model.subst_eq_of_get_eq_none M h1],
    simp only [val, atom.subst_eq_of_get_eq_some h1,
      model.subst_eq_of_get_eq_some M h1],
  end
| (a & b) :=
  begin
    rw function.funext_iff, intro as,
    have h1 := val_subst a,
    have h2 := val_subst b,
    simp only [val, subst, h1, h2],
  end

lemma val_incr_idxs_ge {M N : model α} {k : nat}  
  (h0 : ∀ m < k, M m = N m) (h1 : ∀ m ≥ k, M (m + 1) = N m) : 
    ∀ a : atom, (a.incr_idxs_ge k).val M = a.val N 
| (# m) := 
  begin
    unfold incr_idxs_ge,
    by_cases h2 : k ≤ m,
    { rw if_pos h2, 
      apply h1 _ h2 },
    rw if_neg h2,
    rw not_le at h2,
    apply h0 _ h2
  end
| (a & b) := 
  by simp only [incr_idxs_ge, val, val_incr_idxs_ge]

end atom


@[derive has_reflect]
inductive form : Type
| lit : bool → atom → form
| con : bool → form
| bin : bool → form → form → form
| qua : bool → form → form

local notation `⟪` b `,` a `⟫` := form.lit b a
local notation `⊤*`            := form.con tt
local notation `⊥*`            := form.con ff
local notation p `∨*` q        := form.bin tt p q
local notation p `∧*` q        := form.bin ff p q
local notation `∃*`            := form.qua tt 
local notation `∀*`            := form.qua ff

def holds : model α → form → Prop
| M ⊤*       := true
| M ⊥*       := false
| M ⟪tt, a⟫  :=    (a.val M []).snd
| M ⟪ff, a⟫  :=  ¬ (a.val M []).snd
| M (p ∨* q) := holds M p ∨ holds M q
| M (p ∧* q) := holds M p ∧ holds M q
| M (∀* p)   := ∀ x : value α, holds (M ₀↦ x) p
| M (∃* p)   := ∃ x : value α, holds (M ₀↦ x) p

infix `⊨` : 1000 := holds 

def eqv (α : Type u) (p q : form) : Prop :=
∀ M : model α, (M ⊨ p ↔ M ⊨ q)

notation p `<==` α `==>` q := eqv α p q

lemma eqv_trans {α : Type u} {p q r : form} :
  (p <==α==> q) → (q <==α==> r) → (p <==α==> r) :=
λ h0 h1 M, by rw [h0 M, h1 M]

lemma eqv_refl (α : Type u) (p : form) : p <==α==> p := λ M, by refl

namespace form

@[reducible] def size_of : form → nat
| ⟪_, _⟫           := 1
| (form.con _)     := 1
| (form.bin _ p q) := p.size_of + q.size_of + 1
| (form.qua _ p)   := p.size_of + 1

instance has_sizeof : has_sizeof form := ⟨size_of⟩ 

/- Increment all variable indices equal to or greater than k by 1. -/
def incr_idxs_ge : nat → form → form
| k (form.con b)     := form.con b
| k ⟪b, a⟫           := ⟪b, a.incr_idxs_ge k⟫
| k (form.bin b p q) := form.bin b (incr_idxs_ge k p) (incr_idxs_ge k q)
| k (form.qua b p)   := form.qua b (incr_idxs_ge (k + 1) p)

def incr_idxs : form → form := incr_idxs_ge 0

lemma incr_idxs_lit (b : bool) (a : atom) : 
incr_idxs ⟪b, a⟫ = ⟪b, a.incr_idxs⟫ := rfl

def subst : sub → form → form
| σ ⟪b, a⟫           := ⟪b, a.subst σ⟫
| σ (form.con b)     := form.con b
| σ (form.bin b p q) := form.bin b (subst σ p) (subst σ q)
| σ (form.qua b p)   := form.qua b (subst σ.incr_idxs p)

lemma size_of_subst :
  ∀ σ : sub, ∀ p : form, (p.subst σ).size_of = p.size_of 
| σ ⊤*       := rfl
| σ ⊥*       := rfl
| σ ⟪b, a⟫   := rfl
| σ (p ∨* q) := 
  by simp only [ size_of, subst,
     size_of_subst σ p, size_of_subst σ q ]
| σ (p ∧* q) :=
  by simp only [ size_of, subst,
     size_of_subst σ p, size_of_subst σ q ]
| σ (∀* p)   := by simp only [ size_of, subst, size_of_subst _ p ]
| σ (∃* p)   := by simp only [ size_of, subst, size_of_subst _ p ]

@[simp] lemma size_of_incr_idxs_ge :
  ∀ k : nat, ∀ p : form, (p.incr_idxs_ge k).size_of = p.size_of 
| k ⊤*       := rfl
| k ⊥*       := rfl
| k ⟪b, a⟫   := rfl
| k (p ∨* q) := 
  by simp only [ size_of, size_of_incr_idxs_ge k p, 
     incr_idxs_ge, size_of_incr_idxs_ge k q ]
| k (p ∧* q) := 
  by simp only [ size_of, size_of_incr_idxs_ge k p, 
     incr_idxs_ge, size_of_incr_idxs_ge k q ]
| k (∀* p)   := 
  by simp only [size_of, incr_idxs_ge, size_of_incr_idxs_ge _ p]
| k (∃* p)   := 
  by simp only [size_of, incr_idxs_ge, size_of_incr_idxs_ge _ p]

@[simp] lemma size_of_incr_idxs :
  ∀ p : form, p.incr_idxs.size_of = p.size_of := 
size_of_incr_idxs_ge _

def neg : form → form 
| ⟪b, a⟫   := ⟪bnot b, a⟫ 
| (form.con b)     := form.con (bnot b)
| (form.bin b p q) := form.bin (bnot b) p.neg q.neg
| (form.qua b p)   := form.qua (bnot b) p.neg 

end form

lemma holds_bin_iff_holds_bin 
  {M N : model α} {p q r s : form} {b : bool} :
  (M ⊨ p ↔ N ⊨ q) → (M ⊨ r ↔ N ⊨ s) → 
  (M ⊨ form.bin b p r ↔ N ⊨ form.bin b q s) :=
by { intros h0 h1, cases b;
     apply pred_mono_2'; assumption }

lemma bin_eqv_bin {p q r s : form} {b : bool} :
  (p <==α==> q) → (r <==α==> s) → 
  (form.bin b p r <==α==> form.bin b q s) := 
by { intros h0 h1 M, 
     apply holds_bin_iff_holds_bin (h0 _) (h1 _) }

lemma holds_qua_iff_holds_qua {M N : model α} {p q : form} {b : bool} :
  (∀ v : value α, (M ₀↦ v) ⊨ p ↔ (N ₀↦ v) ⊨ q) → 
  (M ⊨ form.qua b p ↔ N ⊨ form.qua b q) := 
begin
  intro h0, cases b,
  apply forall_iff_forall h0,
  apply exists_iff_exists h0 
end

lemma qua_eqv_qua {p q : form} {b : bool} :
  (p <==α==> q) → (form.qua b p <==α==> form.qua b q) := 
by { intros h0 M,
     apply holds_qua_iff_holds_qua, 
     intro v, apply h0 }

lemma holds_neg : ∀ {M : model α}, ∀ {p : form}, M ⊨ p.neg ↔ ¬ M ⊨ p
| M ⟪b, a⟫ := 
  by cases b; simp only [classical.not_not, form.neg, 
     holds, bool.bnot_true, bool.bnot_false]
| M (form.con b) :=
  by cases b; simp only [form.neg, holds,
     bnot, not_true, not_false_iff]
| M (p ∨* q) := 
  begin
    unfold holds, 
    rw not_or_distrib,
    apply pred_mono_2'; 
    apply holds_neg
  end
| M (p ∧* q) := 
  begin
    unfold holds, 
    rw @not_and_distrib _ _ (classical.dec _),
    apply pred_mono_2'; apply holds_neg
  end
| M (∀* p)   := 
  begin
    unfold holds, 
    rw @not_forall _ _ (classical.dec _) (classical.dec_pred _),
    apply exists_iff_exists,
    intro v, apply holds_neg
  end
| M (∃* p)   := 
  begin
    unfold holds, 
    rw @not_exists,
    apply forall_iff_forall,
    intro v, apply holds_neg
  end
 
open nat

lemma holds_incr_idxs_ge : 
  ∀ M N : model α, ∀ k : nat, 
    (∀ m < k, M m = N m) → 
    (∀ m ≥ k, M (m + 1) = N m) → 
    ∀ p : form, M ⊨ p.incr_idxs_ge k ↔ N ⊨ p 
| M N k h0 h1 ⟪b, a⟫ := 
  by cases b; simp [form.incr_idxs_ge, 
     holds, atom.val_incr_idxs_ge h0 h1 a]
| M N k _ _ (form.con b) := by cases b; refl
| M N k h0 h1 (form.bin b p q) := 
  by { apply holds_bin_iff_holds_bin;
       apply holds_incr_idxs_ge _ _ _ h0 h1 }
| M N k h0 h1 (form.qua b p) := 
  begin
    apply holds_qua_iff_holds_qua, intro v,
    apply holds_incr_idxs_ge _ _ (k + 1);
    intros m h2; cases m,
    { refl },
    { apply h0 _ (lt_of_succ_lt_succ h2) },
    { cases (not_lt_zero _ (lt_of_succ_le h2)) },
    apply h1 _ (succ_le_succ_iff.elim_left h2)
  end

lemma holds_assign_incr_idxs {M : model α} {d : value α} :
  ∀ p : form, (M ₀↦ d) ⊨ p.incr_idxs ↔ M ⊨ p := 
holds_incr_idxs_ge (M ₀↦ d) M 0 (λ _ h, by cases h) (λ _ _, rfl)

def head_occ_on (k : nat) : bool → atom → Prop 
| ff (# m)   := k = m
| tt (# _)   := false
| _  (a & b) := head_occ_on ff a ∨ head_occ_on tt b

def head_occ (k : nat) : atom → Prop := head_occ_on k ff

lemma head_occ_app_var (k m : nat) (a : atom) :
  head_occ k (a & (# m)) ↔ head_occ k a := 
by simp only [head_occ, head_occ_on, or_false]

@[reducible] def swap (k : nat) : sub := 
[(k, # (k + 1) & # k), (k + 1, # k)]

lemma subst_swap_var (k m : nat) :
(m = k ∧ (# m).subst (swap k) = (# (k + 1) & # k)) ∨ 
(m = k + 1 ∧ (# m).subst (swap k) = # k) ∨
(m ≠ k ∧ m ≠ k + 1 ∧ (# m).subst (swap k) = # m) := 
begin
  by_cases h0 : m = k,
  { left, refine ⟨h0, _⟩, 
    simp only [ swap, atom.subst, sub.get, 
      if_true, h0, eq_self_iff_true ], refl },
  by_cases h1 : m = k + 1,
  { right, left,
    refine ⟨h1, _⟩, 
    simp only [ swap, atom.subst, sub.get, 
      if_neg h0, if_pos h1 ], refl },
  right, right,
  refine ⟨h0, h1, _⟩, 
  simp only [ swap, atom.subst, sub.get, 
    if_neg h0, if_neg h1 ], refl
end

lemma head_occ_succ_succ (k m : nat) (h0 : m + 1 < k) : 
  ∀ a : atom, head_occ k (a.subst $ swap m) → head_occ k a 
| (# n) h1 := 
  begin
    rcases subst_swap_var m n 
      with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, _, h2⟩;
    rw h2 at h1,
    { cases h1,
      { cases (ne_of_gt h0) h1 },
      cases h1 },
    { have h3 : k ≠ m := 
      ne_of_gt (lt_trans (lt_succ_self _) h0), 
      cases h3 h1 },
    exact h1,
  end
| (a & (# n)) h1 :=  
  begin
    cases h1,
    { left, exact head_occ_succ_succ a h1 },
    rcases subst_swap_var m n 
      with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, _, h2⟩;
    rw h2 at h1; cases h1,
    { cases (ne_of_gt h0) h1 },
    cases h1
  end
| (a & (b & c)) h1 := 
  begin
    cases h1,
    { left, exact head_occ_succ_succ a h1 },
    right, apply head_occ_succ_succ (b &c) h1
  end
  
lemma head_occ_succ (k : nat) :
  ∀ a : atom, head_occ k (a.subst $ swap k) → head_occ (k + 1) a  
| (# m) h0 := 
  begin
    rcases subst_swap_var k m 
      with ⟨_, h1⟩ | ⟨h2, h1⟩ | ⟨h2, _, h1⟩;
    rw h1 at h0,
    { cases h0,
      { cases nat.succ_ne_self k h0.symm },
      cases h0 },
    { apply h2.symm },
    cases h2 h0.symm
  end
| (a & (# m)) h0 := 
  begin
    cases h0,
    { left, apply head_occ_succ _ h0 },
    rcases subst_swap_var k m 
      with ⟨_, h1⟩ | ⟨h2, h1⟩ | ⟨h2, _, h1⟩;
    rw h1 at h0; cases h0, 
    { cases nat.succ_ne_self k h0.symm },
    cases h0,
  end
| (a & (b & c)) h0 := 
  begin
    cases h0,
    { left, apply head_occ_succ a h0 },
    right, apply head_occ_succ (b & c) h0
  end
























































/-

instance list.decidable_eq_nil : ∀ as : list α, decidable (as = []) 
| []       := is_true rfl
| (_ :: _) := is_false (λ h, by cases h)

def occ (k : nat) : atom → Prop
| (# m)   := k = m 
| (a & b) := occ a ∨ occ b

def occ_at (k : nat) : list bool → atom → Prop
| []        (# m)   := k = m 
| []        (_ & _) := false
| (_  :: _) (# _)   := false
| (ff :: π) (a & b) := occ_at π a
| (tt :: π) (a & b) := occ_at π b

lemma occ_at_var (π : list bool) (k m : nat) :
  occ_at k π (# m) ↔ (π = [] ∧ k = m) :=
begin
  constructor; intro h0,
  { cases π with b, refine ⟨rfl, h0⟩, 
    cases b; cases h0 },
  rw [h0.left], exact h0.right
end

def fun_occ (k : nat) (a : atom) : Prop := 
∃ bs : list bool, occ_at k (bs ++ [ff]) a 

def head_occ (k : nat) (a : atom) : Prop := a = (# k) ∨ fun_occ k a

@[reducible] def swap (k : nat) : sub := 
[(k, # (k + 1) & # k), (k + 1, # k)]


lemma head_occ_succ_succ (k : nat) (a : atom) :
  head_occ (k + 2) (a.subst $ swap k) → 
  head_occ (k + 2) a :=
begin
  rintro (h0 | h0),
  { cases a with m a b, 
    { cases atom.eq_or_in_range h0 with h1 h1, 
      { left, exact h1.symm }, 
      rcases h1 with ⟨_, _⟩ | ⟨h1 | ⟨_, _⟩⟩,
      { cases (nat.ne_add_iff_pos_right k 2).elim_right 
        (nat.zero_lt_succ _) (atom.eq_of_var_eq_var h1).symm } }, 
    cases h0 },
  cases h0 with π h0,

  cases occ_at_subst h0 with h1 h1,
  { right, refine ⟨_, h1.left⟩ },

  rcases h1 with ⟨ρ, τ, m, b, h1, h2, h3, h4⟩, 

  have h5 := in_range_of_get_eq_some h4,

  --{ simp at h5, subst h5, 
  --  cases h3, 
  --  { rw occ_at_var at h3_a_1, }
  --   
  --  
  --}


  


end


#exit
--#exit
--inductive occ_at : list bool → nat → atom → Prop
--| var (k : nat)  : occ_at [] k (# k)
--| app_left       : 
--  ∀ {k : nat} {a : atom}, ∀ b : atom, ∀ bs : list bool,
--  occ_at bs k a → occ_at (ff :: bs) k (a & b)
--| app_right       : 
--  ∀ {k : nat} {a : atom}, ∀ b : atom, ∀ bs : list bool,
--  occ_at bs k b → occ_at (tt :: bs) k (a & b)
--
--lemma occ_at_var (π : list bool) (k m : nat) :
--  occ_at π k (# m) ↔ (π = [] ∧ k = m) :=
--begin
--  constructor; intro h0,
--  { cases h0, constructor; refl },
--  rw [h0.left, h0.right],
--  constructor
--end


open list

lemma head_occ_var (k m : nat) :
  head_occ k (# m) ↔ k = m :=
begin
  constructor; intro h0, 
  { cases h0, 
    { cases h0, refl },
    rcases h0 with ⟨π, h1⟩, 
    rw [occ_at_var, append_eq_nil] at h1,
    cases h1.left.right },
  rw h0, constructor, refl
end


lemma head_occ_app_of_head_occ_left (k : nat) (a b : atom) :
  head_occ k a → head_occ k (a & b) := sorry

lemma head_occ_app_of_head_occ_right (k : nat) (a b c : atom) :
  head_occ k (b & c) → head_occ k (a & (b & c)) := sorry

lemma occ_at_subst {k : nat} {σ : sub} :
  ∀ {a : atom} {π : list bool},
  occ_at k π (a.subst σ) →  
  ((occ_at k π a ∧ σ.get k = none) ∨ 
   (∃ (ρ τ : list bool) (m : nat) (b : atom), 
      ρ ++ τ = π ∧ occ_at m ρ a ∧ occ_at k τ b ∧ σ.get m = some b)) 
| (# n) π h0 := 
  begin
    cases h1 : σ.get n with b,
    { rw atom.subst_eq_of_get_eq_none h1 at h0, 
      rw occ_at_var at h0,
      left, rw [h0.left, h0.right],
      refine ⟨rfl, h1⟩ },
    rw atom.subst_eq_of_get_eq_some h1 at h0, 
    right, 
    refine ⟨[], π, n, b, nil_append _, rfl, h0, h1⟩
  end
| (b & c) π h0 := 
  begin
    cases π with b π, 
    { cases h0 },


    --cases h0 with _ _ _ _ υ h1 _ _ _ υ h1;
    --{ rcases occ_at_subst h1 with ⟨h2, h3⟩ | 
    --    ⟨ρ, τ, m, d, ⟨h2, h3, h4, h5⟩⟩,
    --  { left, refine ⟨by {constructor, assumption}, h3⟩ },
    --  right, 
    --  refine ⟨_ :: ρ, τ, m, d, 
    --    ⟨by {rw cons_append, congr'}, _ , h4, h5⟩⟩, 
    --  constructor, exact h3 }
  end

--def head_occ (k : nat) : atom → Prop
--| (# m)         := k = m 
--| (a & (# m))   := head_occ a
--| (a & (b & c)) := head_occ a ∨ head_occ (b & c)
-/

def idx_is_fo : nat → form → Prop
| k ⟪b, a⟫           := ¬ head_occ k a 
| k (form.con _)     := true
| k (form.bin _ p q) := idx_is_fo k p ∧ idx_is_fo k q
| k (form.qua b p)   := idx_is_fo (k + 1) p

def qua_are_fo (ae : bool) : form → Prop
| ⟪b, a⟫           := true
| (form.con _)     := true
| (form.bin _ p q) := qua_are_fo p ∧ qua_are_fo q
| (form.qua b p)   := (ae = b → idx_is_fo 0 p) ∧ qua_are_fo p 


def form.swap (k : nat) (p : form) : form :=
  p.subst (swap k) --[(0, (# 1) & (# 0)), (1, # 0)]

def evaluate (a : α) : value α :=
λ _, (a, false)

postfix  `ₑ` : 1000 := evaluate 

def denote (v : value α) : α := (v []).fst

postfix  `ᵈ` : 1000 := denote

lemma denote_evaluate (a : α) : (a ₑ)ᵈ = a := rfl

@[reducible] def value.app (v w : value α) : value α := 
λ as, v (wᵈ :: as)

local infix `⬝` := value.app

lemma assign_app_evaluate_denote (M : model α) (v w : value α) :
  (M ₀↦ v ⬝ wᵈₑ) = (M ₀↦ v ⬝ w) := 
by ext k as; cases k; refl

lemma model.assign_subst (M : model α) (v : value α) (σ : sub) :
  ((M.subst σ) ₀↦ v) = (model.subst (M ₀↦ v) σ.incr_idxs) := 
begin
  rw function.funext_iff, 
  intro k, cases k, 
  { have h0 := get_zero_incr_idxs σ,
    simp only [model.subst, h0], refl }, 
  have h0 := get_succ_incr_idxs k σ,
  cases h1 : sub.get k σ with a,
  { rw h1 at h0, 
    have h2 : (model.subst M σ ₀↦v) (succ k) = M k,
    { simp only [assign, model.subst_eq_of_get_eq_none _ h1] },
    have h3 : model.subst (M ₀↦v) (sub.incr_idxs σ) (succ k) = M k,
    { simp only [assign, model.subst_eq_of_get_eq_none _ h0] },
    simp only [h2, h3] },
  rw h1 at h0, 
  have h2 : (model.subst M σ ₀↦v) (succ k) = a.val M,
  { simp only [assign, model.subst_eq_of_get_eq_some _ h1] },
  have h3 : model.subst (M ₀↦v) (sub.incr_idxs σ) (succ k) = a.val M,
  { simp only [assign, model.subst_eq_of_get_eq_some _ h0,
    atom.val_assign_incr_idxs] },
  simp only [h2, h3] 
end

lemma holds_subst :
  ∀ (M : model α) (p : form) (σ : sub), 
  M ⊨ (p.subst σ) ↔ M.subst σ ⊨ p  
| M (form.con b) σ := by cases b; refl
| M ⟪b, a⟫ σ := 
  by cases b; simp only [form.subst, holds, atom.val_subst M σ a]
| M (form.bin b p q) σ := 
  by apply holds_bin_iff_holds_bin; apply holds_subst
| M (form.qua b p)   σ := 
  by { apply holds_qua_iff_holds_qua, intro v,
       simp only [model.assign_subst, holds_subst] }

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

def skolem_val [inhabited α] (f : value α → value α) : value α 
| []        := (default α, false)
| (a :: as) := f (a ₑ) as

lemma exists_skolem_val [inhabited α] {M : model α} {p : form} : 
  (M ⊨ ∀* (∃* p)) → ∃ f : value α, ∀ a : α, (M ₀↦ (a ₑ) ₀↦ f ⬝ a ₑ) ⊨ p := 
begin
  intro h0,
  cases classical.skolem.elim_left h0 with f h1,
  refine ⟨skolem_val f, λ a, h1 (a ₑ)⟩,
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
  ∀ a : atom, ¬ head_occ k a → (a.val M = a.val N) 
| (# m)   h1 := by apply h0.left _ (ne.symm h1) 
| (a & (# m)) h1 := 
  begin
    have h2 : a.val M = a.val N,
    { rw head_occ_app_var at h1,
      apply val_eq_val_of_eq_except a h1 },
    have h3 : (M m []).fst  = (N m []).fst, 
    { by_cases h4 : k = m,
      { subst h4, apply h0.right },
      rw h0.left _ (ne.symm h4) }, 
    simp only [atom.val, h2, h3]
  end
| (a & (b & c)) h1 := 
  begin
    cases not_or_distrib.elim_left h1 with ha hbc,
    have h2 : a.val M = a.val N,
    { apply val_eq_val_of_eq_except a _,
      intro h2, apply h1, left, exact h2 },
    have h3 : (b & c).val M = (b & c).val N,
    { apply val_eq_val_of_eq_except _ _, 
      intro h3, apply h1, right, exact h3 },
    simp only [atom.val, h2, h3]
  end

lemma holds_iff_holds_of_eq_except : 
  ∀ {M N : model α} {k : nat} (p : form),
  eq_except M N k → idx_is_fo k p → (M ⊨ p ↔ N ⊨ p) 
| M N k ⟪b, a⟫ h0 h1 := 
  by cases b; simp [holds, val_eq_val_of_eq_except h0 a h1]
| M N k (form.con b) h0 h1 := by cases b; refl -- iff.refl _
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
  idx_is_fo 1 p → (∃* (∀* $ p.swap 0) <==α==> ∀* (∃* p)) := 
begin
  intros h0 M,
  constructor; intro h1,
  { cases h1 with v h1,
    intro w, 
    refine ⟨v ⬝ w, _⟩, 
    rw ← holds_swap, apply h1 },
  cases exists_skolem_val h1 with f h2,
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

lemma neg_subst :
  ∀ p : form, ∀ σ : sub, (p.subst σ).neg <==α==> (p.neg.subst σ)
| ⟪b, a⟫       σ := by apply eqv_refl 
| (form.con b) σ := by apply eqv_refl 
| (form.bin b p q) σ := 
  by { intro M, apply holds_bin_iff_holds_bin;
       apply neg_subst }
| (form.qua b p)   σ := 
  by { intro M, apply holds_qua_iff_holds_qua,
       intro v, apply neg_subst }

lemma neg_swap {p : form} : (p.swap 0).neg <==α==> p.neg.swap 0 := 
neg_subst _ _

lemma idx_is_fo_neg : ∀ k : nat, ∀ p : form, idx_is_fo k p.neg ↔ idx_is_fo k p 
| k ⟪b, a⟫           := by refl
| k (form.con b)     := by refl
| k (form.bin b p q) := 
  by simp only [idx_is_fo, form.neg, idx_is_fo_neg]
| k (form.qua b p)   := 
  by simp only [idx_is_fo, form.neg, idx_is_fo_neg]

lemma neg_eqv_neg (p q : form) :
  (p.neg <==α==> q.neg) ↔ (p <==α==> q) :=
begin
  apply forall_iff_forall, intro M,
  rw [holds_neg, holds_neg, @not_iff_not _ _ _ _], 
  repeat {apply classical.dec _}
end

def fa_ex_swap_eqv [inhabited α] (p : form) : 
  idx_is_fo 1 p → (∀* (∃* $ p.swap 0) <==α==> ∃* (∀* p)) := 
begin
  intro h0, 
  replace h0 := (idx_is_fo_neg _ _).elim_right h0,
  have h1 : (∃* (∀* (p.swap 0).neg) <==α==> ∀* (∃* p.neg)) := 
  eqv_trans 
    (qua_eqv_qua (qua_eqv_qua neg_swap))
    (@ex_fa_swap_eqv α _ _ h0),
  rw ← neg_eqv_neg,
  simp only [holds_neg.symm, form.neg, bnot, h1]
end

def swap_eqv [inhabited α] (ae : bool) {p : form} : 
  idx_is_fo 1 p → 
  (form.qua ae (form.qua (bnot ae) $ p.swap 0) 
    <==α==> form.qua (bnot ae) (form.qua ae p)) := 
by { intro h0, cases ae,
     exact fa_ex_swap_eqv _ h0,
     exact ex_fa_swap_eqv _ h0 }

lemma zero_idx_is_fo_swap_aux : 
  ∀ k : nat, ∀ p : form, idx_is_fo (k + 1) p → 
    idx_is_fo k (form.subst [(k, (# (k + 1)) & (# k)), (k + 1, # k)] p) 
| k ⟪b, a⟫           h0 := h0 ∘ (head_occ_succ k _)
| k (form.con b)     h0 := trivial
| k (form.bin b p q) h0 := 
  by { cases h0, constructor; 
       apply zero_idx_is_fo_swap_aux; assumption }
| k (form.qua b p)   h0 := zero_idx_is_fo_swap_aux (k + 1) p h0

lemma zero_idx_is_fo_swap {p : form} :
  idx_is_fo 1 p → idx_is_fo 0 (p.swap 0) := 
zero_idx_is_fo_swap_aux 0 _

lemma idx_is_fo_swap : 
  ∀ k m : nat, m + 1 < k → 
  ∀ p : form, idx_is_fo k p → idx_is_fo k (p.swap m)
| k m h0 ⟪b, a⟫           h1 := h1 ∘ (head_occ_succ_succ k _ h0 _)
| k m h0 (form.con b)     h1 := trivial
| k m h0 (form.bin b p q) h1 := 
  by { cases h1, constructor; 
       apply idx_is_fo_swap; assumption }
| k m h0 (form.qua b p)   h1 := 
  idx_is_fo_swap (k + 1) (m + 1) (succ_lt_succ h0) p h1

--@[reducible] def form.size_of_two : (Σ' (a : form), form) → nat 
--| ⟨p, q⟩ := p.size_of + q.size_of 
--
--meta def form.show_size_lt : tactic unit := 
--`[ simp only [form.size_of_two, form.size_of, nat.lt_succ_self,
--   lt_succ_self, add_comm, add_lt_add_iff_left, add_left_comm,
--   form.size_of_incr_idxs, form.size_of_incr_idxs_ge,
--   nat.zero_lt_succ, add_zero, lt_add_iff_pos_right ] ]

lemma neg_incr_idxs_ge : 
  ∀ k : nat, ∀ p : form, (p.incr_idxs_ge k).neg = p.neg.incr_idxs_ge k 
| k ⟪b, a⟫           := by cases b; refl
| k (form.con _)     := rfl
| k (form.bin b p q) := 
  by simp only [form.neg, form.incr_idxs_ge,
     eq_self_iff_true, neg_incr_idxs_ge, and_self ]
| k (form.qua b p) := 
  by simp only [form.neg, form.incr_idxs_ge,
     eq_self_iff_true, neg_incr_idxs_ge, and_self ]

lemma neg_incr_idxs (p : form) :
  p.incr_idxs.neg = p.neg.incr_idxs :=
neg_incr_idxs_ge 0 p

def pull_fa_left_eqv [inhabited α] (b : bool) (p q : form) : 
  ∀* (form.bin b p q.incr_idxs) <==α==> form.bin b (∀* p) q := 
begin
  intro M, 
  have v : value α := (default α)ₑ,
  constructor; intro h0; cases b,
  { constructor,
    { intro w, exact (h0 w).left },
    apply (holds_assign_incr_idxs _).elim_left (h0 v).right },
  { cases classical.em ((M ₀↦ v) ⊨ q.incr_idxs) with h2 h2, 
    { rw holds_assign_incr_idxs at h2,
      right, exact h2 },
    left, intro w, 
    cases (h0 w) with h3 h3, 
    { exact h3 },
    rw holds_assign_incr_idxs at h2,
    rw holds_assign_incr_idxs at h3,
    cases (h2 h3) },
  { intro w, 
    refine ⟨h0.left _, _⟩,
    rw holds_assign_incr_idxs, 
    exact h0.right },
  { intro w, 
    cases classical.em ((M ₀↦ w) ⊨ q.incr_idxs) with h1 h1, 
    { right, exact h1 },
    left, cases h0 with h2 h2,
    { apply h2 },
    rw holds_assign_incr_idxs at h1,
    cases (h1 h2) }
end

def pull_ex_left_eqv [inhabited α] (b : bool) (p q : form) : 
  ∃* (form.bin b p q.incr_idxs) <==α==> form.bin b (∃* p) q := 
by { rw ← neg_eqv_neg, 
     simp only [form.neg, neg_incr_idxs, 
     bnot, pull_fa_left_eqv] } 

lemma bin_comm (b : bool) (p q : form) : 
form.bin b p q <==α==> form.bin b q p := 
by {intro M, cases b, apply and.comm, apply or.comm}

def pull_qua_left_eqv [inhabited α] (ae ao : bool) (p q : form) : 
  form.qua ae (form.bin ao p q.incr_idxs) <==α==> 
  form.bin ao (form.qua ae p) q := 
by {cases ae, apply pull_fa_left_eqv, apply pull_ex_left_eqv }

def pull_qua_right_eqv [inhabited α] (ae ao : bool) (p q : form) : 
  form.qua ae (form.bin ao p.incr_idxs q) <==α==> 
  form.bin ao p (form.qua ae q) := 
begin
  have h0 : ( form.qua ae (form.bin ao (form.incr_idxs p) q) <==α==>
              form.qua ae (form.bin ao q (form.incr_idxs p)) ) :=
  qua_eqv_qua (bin_comm _ _ _),
  intro M,
  simp only [ h0 M, pull_qua_left_eqv ae ao q p M,
    bin_comm ao p (form.qua ae q) M ] 
end

@[reducible] def form.size_of_ordered : 
  (Σ' (b : bool), (Σ' (a : form), form)) → nat 
| ⟨tt, p, q⟩ := p.size_of + q.size_of + 1
| ⟨ff, p, q⟩ := p.size_of + q.size_of 

meta def form.show_size_lt : tactic unit :=
`[ simp only [form.size_of_ordered, nat.lt_succ_self,
   add_comm, add_lt_add_iff_left, add_left_comm,
   form.size_of_incr_idxs ] ]

/- Pull quantifiers over a binary connective. `ae` specifies
   the type of quantifier to be pulled, and `ao` specifies 
   the binary connective. -/
def pull_over_bin (ae : option bool) (ao : bool) : bool → form → form → form
| tt (form.qua b p) q := 
  have form.size_of_ordered ⟨ff, ⟨q, form.qua b p⟩⟩ <
       form.size_of_ordered ⟨tt, ⟨form.qua b p, q⟩⟩,
  by form.show_size_lt,
  if ae = some (bnot b) 
  then pull_over_bin ff q (form.qua b p)
  else form.qua b (pull_over_bin tt p q.incr_idxs)
| ff (form.qua b p) q := 
  have form.size_of_ordered ⟨ff, ⟨p, form.incr_idxs q⟩⟩ <
       form.size_of_ordered ⟨ff, ⟨form.qua b p, q⟩⟩,
  by form.show_size_lt,
  if ae = some (bnot b) 
  then form.bin ao (form.qua b p) q
  else form.qua b (pull_over_bin ff p q.incr_idxs)
| tt p q := 
  have form.size_of_ordered ⟨ff, ⟨q, p⟩⟩ <
       form.size_of_ordered ⟨tt, ⟨p, q⟩⟩,
  by form.show_size_lt,
  pull_over_bin ff q p
| ff p q := form.bin ao p q
using_well_founded 
  {rel_tac := λ _ _, `[exact ⟨_, measure_wf form.size_of_ordered⟩]}

/- Pull quantifiers over a quantifier via skolemization. 
   `ae` indicates the type of quantifier being pulled. -/
def swap_many (ae : bool) : form → form
| (form.qua b p) := 
  have form.size_of (p.swap 0) < form.size_of (form.qua b p),
  { unfold form.swap, rw form.size_of_subst, 
    simp only [form.size_of, nat.lt_succ_self, add_comm] }, 
  if ae = b 
  then form.qua ae (swap_many $ p.swap 0)
  else form.qua (bnot ae) (form.qua b p)
| p := form.qua (bnot ae) p

lemma idx_is_fo_swap_many (ae : bool) :
  ∀ {p : form} {k : nat}, 
  idx_is_fo (k + 1) p → idx_is_fo k (swap_many ae p) 
| ⟪b, a⟫           := λ _, id
| (form.con b)     := λ _, id
| (form.bin b p q) := λ _, id
| (form.qua b p)   := 
  have form.size_of (p.swap 0) < form.size_of (form.qua b p),
  by {unfold form.swap, rw form.size_of_subst, form.show_size_lt},
  begin
    intros k h0,
    unfold swap_many,
    by_cases h1 : ae = b,
    { subst h1, 
      rw if_pos rfl,
      have h2 : idx_is_fo (k + 2) (p.swap 0) :=
      @idx_is_fo_swap (k + 2) 0 
        (succ_lt_succ $ zero_lt_succ _) _ h0,
      apply @idx_is_fo_swap_many _ (k + 1) h2 }, 
    rw if_neg h1, exact h0
  end

lemma swap_many_eqv (α : Type u) [inhabited α] (ae : bool) :
  ∀ {p : form}, idx_is_fo 0 p → 
  (swap_many ae p <==α==> form.qua (bnot ae) p) 
| ⟪b, a⟫           := λ _, eqv_refl _ _
| (form.con b)     := λ _, eqv_refl _ _
| (form.bin b p q) := λ _, eqv_refl _ _ 
| (form.qua b p)   := 
  have form.size_of (p.swap 0) < form.size_of (form.qua b p) :=
  by { unfold form.swap, rw form.size_of_subst,
       form.show_size_lt },
  begin
    intro h0,
    unfold swap_many,
    by_cases h1 : ae = b, 
    { subst h1, rw if_pos rfl,
      apply eqv_trans _ (@swap_eqv α _ ae _ h0),
      apply qua_eqv_qua,
      apply swap_many_eqv,-- (zero_idx_is_fo_swap h0) 
      apply zero_idx_is_fo_swap,
      apply h0 },
    rw if_neg h1, apply eqv_refl _
  end

def swap_all (ae : bool) : form → form
| ⟪b, a⟫           := ⟪b, a⟫ 
| (form.con b)     := form.con b
| (form.bin b p q) := 
  pull_over_bin (some ae) b tt (swap_all p) (swap_all q) 
| (form.qua b p)   := 
  if ae = b
  then form.qua ae (swap_all p)
  else swap_many ae (swap_all p)

lemma bnot_eq_iff_ne {a b : bool} : 
  bnot a = b ↔ a ≠ b := 
by cases a; cases b; simp only 
   [bnot, ne, not_false_iff, eq_self_iff_true, not_true]

lemma idx_is_fo_pull_over_bin {k : nat} (ae : option bool) (ao ls : bool) :
  ∀ {p q : form}, idx_is_fo k p → idx_is_fo k q → 
  idx_is_fo k (pull_over_bin ae ao ls p q) := sorry

lemma idx_is_fo_swap_all (ae : bool) :
  ∀ {k : nat} {p : form}, idx_is_fo k p → idx_is_fo k (swap_all ae p)  
| k ⟪b, a⟫           h0 := h0
| k (form.con b)     h0 := h0
| k (form.bin b p q) h0 := 
  by { cases h0, apply idx_is_fo_pull_over_bin; 
       apply idx_is_fo_swap_all; assumption }
| k (form.qua b p)   h0 := 
  begin
    unfold swap_all,
    by_cases h1 : ae = b,
    { subst h1, rw if_pos rfl,
      apply @idx_is_fo_swap_all _ p h0 },
    rw if_neg h1, 
    apply idx_is_fo_swap_many,
    apply idx_is_fo_swap_all,
    apply h0
  end

def pull_over_bin_eqv [inhabited α] 
  (ae : option bool) (ao ls : bool) :
  ∀ p q : form, pull_over_bin ae ao ls p q <==α==> form.bin ao p q := sorry

lemma swap_all_eqv [inhabited α] {ae : bool} :
  ∀ {p : form}, qua_are_fo (bnot ae) p → (swap_all ae p <==α==> p) 
| ⟪b, a⟫           h0 := eqv_refl _ _
| (form.con b)     h0 := eqv_refl _ _
| (form.bin b p q) h0 := 
  eqv_trans 
    (pull_over_bin_eqv ae b _ _ _)
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
      (idx_is_fo_swap_all _ (h0.left h2))), 
    apply qua_eqv_qua (swap_all_eqv h0.right)
end

def prenexify : form → form
| ⟪b, a⟫           := ⟪b, a⟫ 
| (form.con b)     := form.con b
| (form.bin b p q) := pull_over_bin none b tt p q
| (form.qua b p)   := form.qua b (prenexify p)

def AE : form → form := prenexify ∘ swap_all ff
def EA : form → form := prenexify ∘ swap_all tt

#exit
/- Pull quantifiers over a binary connective. `ae` indicates
   the type of quantifier to be prioritized, and `ao` indicates 
   the binary connective. -/
def pull_over_bin (ae ao : bool) : form → form → form
| (form.qua b p) (form.qua c q) := 
  have form.size_of_two ⟨p, (form.qua c q).incr_idxs⟩ < 
       form.size_of_two ⟨form.qua b p, form.qua c q⟩ :=
  by form.show_size_lt,
  have form.size_of_two ⟨(form.qua b p).incr_idxs, q⟩ < 
       form.size_of_two ⟨form.qua b p, form.qua c q⟩ :=
  by form.show_size_lt,
  have form.size_of_two ⟨p.incr_idxs, q.incr_idxs_ge 1⟩ < 
       form.size_of_two ⟨form.qua b p, form.qua c q⟩ :=
  by form.show_size_lt,
  if      ae = b then form.qua b (pull_over_bin p (form.qua c q).incr_idxs) 
  else if ae = c then form.qua c (pull_over_bin (form.qua b p).incr_idxs q) 
                 else form.qua b (form.qua c (pull_over_bin p.incr_idxs (q.incr_idxs_ge 1)))
| (form.qua b p) q := 
  have form.size_of_two ⟨p, q.incr_idxs⟩ < 
       form.size_of_two ⟨form.qua b p, q⟩ :=
  by form.show_size_lt,
  form.qua b (pull_over_bin p q.incr_idxs)
| p (form.qua c q) := 
  have form.size_of_two ⟨p.incr_idxs, q⟩ <
       form.size_of_two ⟨p, form.qua c q⟩ :=
  by form.show_size_lt,
  form.qua c (pull_over_bin p.incr_idxs q) 
| p q := form.bin ao p q
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf form.size_of_two⟩]}

lemma pull_over_bin_eqv_aux_lit (ae ao b1 b2 : bool) (p : form) (a : atom) :
pull_over_bin ae ao (form.qua b1 p) ⟪b2, a⟫ = 
  form.qua b1 (pull_over_bin ae ao p ⟪b2, a⟫.incr_idxs) := 
by simp [pull_over_bin]

lemma pull_over_bin_eqv_aux_con (ae ao b1 b2 : bool) (p : form) :
pull_over_bin ae ao (form.qua b1 p) (form.con b2)  = 
  form.qua b1 (pull_over_bin ae ao p (form.con b2).incr_idxs) := 
by simp [pull_over_bin]

lemma pull_over_bin_eqv_aux_bin (ae ao b1 b2 : bool) (p q r : form) :
pull_over_bin ae ao (form.qua b1 p) (form.bin b2 q r) = 
  form.qua b1 (pull_over_bin ae ao p (form.bin b2 q r).incr_idxs) := 
by simp [pull_over_bin]

def pull_over_bin_eqv [inhabited α] (ae ao : bool) :
  ∀ p q : form, pull_over_bin ae ao p q <==α==> form.bin ao p q 
| ⟪_, _⟫              ⟪_, _⟫           := eqv_refl _ _
| ⟪_, _⟫              (form.con _)     := eqv_refl _ _
| ⟪_, _⟫              (form.bin _ _ _) := eqv_refl _ _
| ⟪b1, a1⟫            (form.qua b2 p2) := 
  have form.size_of_two ⟨form.incr_idxs ⟪b1,a1⟫, p2⟩ < 
       form.size_of_two ⟨⟪b1,a1⟫, form.qua b2 p2⟩, 
  by form.show_size_lt,
  by { apply eqv_trans _ (@pull_qua_right_eqv α _ _ _ _ _),
       apply qua_eqv_qua (pull_over_bin_eqv _ _) }
| (form.con _)        ⟪_, _⟫           := eqv_refl _ _
| (form.con _)        (form.con _)     := eqv_refl _ _
| (form.con _)        (form.bin _ _ _) := eqv_refl _ _
| (form.con b1)       (form.qua b2 p2) := 
  have form.size_of_two ⟨form.incr_idxs (form.con b1), p2⟩ < 
       form.size_of_two ⟨form.con b1, form.qua b2 p2⟩,
  by form.show_size_lt,
  by { apply eqv_trans _ (@pull_qua_right_eqv α _ _ _ _ _),
       apply qua_eqv_qua (pull_over_bin_eqv _ _) }
| (form.bin b _ _)    ⟪_, _⟫              := eqv_refl _ _
| (form.bin b _ _)    (form.con _)        := eqv_refl _ _
| (form.bin b _ _)    (form.bin _ _ _)    := eqv_refl _ _
| (form.bin b1 p1 q1) (form.qua b2 p2)    := 
  have form.size_of_two ⟨form.incr_idxs (form.bin b1 p1 q1), p2⟩ <
       form.size_of_two ⟨form.bin b1 p1 q1, form.qua b2 p2⟩,
  by form.show_size_lt,
  by { apply eqv_trans _ (@pull_qua_right_eqv α _ _ _ _ _),
       apply qua_eqv_qua (pull_over_bin_eqv _ _) }
| (form.qua b1 p1)    ⟪b2, a2⟫            := 
  have form.size_of_two ⟨p1, form.incr_idxs ⟪b2,a2⟫⟩ < 
       form.size_of_two ⟨form.qua b1 p1, ⟪b2,a2⟫⟩,
  by form.show_size_lt,
  by { apply eqv_trans _ (@pull_qua_left_eqv α _ _ _ _ _),
       rw pull_over_bin_eqv_aux_lit,
       apply qua_eqv_qua (pull_over_bin_eqv _ _) }
| (form.qua b1 p1)    (form.con b2)       := 
  have form.size_of_two ⟨p1, form.incr_idxs (form.con b2)⟩ < 
       form.size_of_two ⟨form.qua b1 p1, form.con b2⟩,
  by form.show_size_lt,
  by { apply eqv_trans _ (@pull_qua_left_eqv α _ _ _ _ _),
       rw pull_over_bin_eqv_aux_con,
       apply qua_eqv_qua (pull_over_bin_eqv _ _) }
| (form.qua b1 p1)    (form.bin b2 p2 q2) := 
  have form.size_of_two ⟨p1, form.incr_idxs (form.bin b2 p2 q2)⟩ <
       form.size_of_two ⟨form.qua b1 p1, form.bin b2 p2 q2⟩,
  by form.show_size_lt,
  by { apply eqv_trans _ (@pull_qua_left_eqv α _ _ _ _ _),
       rw pull_over_bin_eqv_aux_bin,
       apply qua_eqv_qua (pull_over_bin_eqv _ _) }
| (form.qua b1 p1)    (form.qua b2 p2)    := 
  have form.size_of_two ⟨form.incr_idxs p1, form.incr_idxs_ge 1 p2⟩ <
       form.size_of_two ⟨form.qua b1 p1, form.qua b2 p2⟩,
  by form.show_size_lt,
  have form.size_of_two ⟨p1, form.incr_idxs (form.qua b2 p2)⟩ < 
       form.size_of_two ⟨form.qua b1 p1, form.qua b2 p2⟩,
  by form.show_size_lt,
  have  form.size_of_two ⟨form.incr_idxs (form.qua b1 p1), p2⟩ < 
        form.size_of_two ⟨form.qua b1 p1, form.qua b2 p2⟩,
  by form.show_size_lt,
  begin
    unfold pull_over_bin,
    by_cases h0 : (ae = b1), 
    { rw if_pos h0,
      apply eqv_trans _ (@pull_qua_left_eqv α _ _ _ _ _),
      apply qua_eqv_qua (pull_over_bin_eqv _ _) },
    rw if_neg h0,
    by_cases h1 : (ae = b2), 
    { rw if_pos h1,
      apply eqv_trans _ (@pull_qua_right_eqv α _ _ _ _ _),
     apply qua_eqv_qua (pull_over_bin_eqv _ _) },
    rw if_neg h1,
    apply eqv_trans (qua_eqv_qua _) (@pull_qua_left_eqv α _ _ _ _ _),
    apply eqv_trans (qua_eqv_qua _) (@pull_qua_right_eqv α _ _ _ _ _),
    apply pull_over_bin_eqv
  end
using_well_founded 
  {rel_tac := λ _ _, `[exact ⟨_, measure_wf form.size_of_two⟩]}

lemma swap_many_eqv (α : Type u) [inhabited α] (ae : bool) :
  ∀ {p : form}, idx_is_fo 0 p → 
  (swap_many ae p <==α==> form.qua (bnot ae) p) 
| ⟪b, a⟫           := λ _,  eqv_refl _ _
| (form.con b)     := λ _, eqv_refl _ _
| (form.bin b p q) := λ _, eqv_refl _ _ 
| (form.qua b p)   := 
  have form.size_of (swap p) < form.size_of (form.qua b p) :=
  by { unfold swap, rw form.size_of_subst,
       form.show_size_lt
  
  },
  begin
    intro h0,
    unfold swap_many,
    by_cases h1 : ae = b, 
    { subst h1, rw if_pos rfl,
      apply eqv_trans _ (@swap_eqv α _ ae _ h0),
      apply qua_eqv_qua,
      apply swap_many_eqv (zero_idx_is_fo_swap h0) },
    rw if_neg h1, apply eqv_refl _
  end
  
  #check swap_many
def skolem_prenex (ae : bool) : form → form
| ⟪b, a⟫           := ⟪b, a⟫ 
| (form.con b)     := form.con b
| (form.bin b p q) := 
  pull_over_bin ae b (skolem_prenex p) (skolem_prenex q) 
| (form.qua b p)   := 
  if ae = b
  then form.qua ae (skolem_prenex p)
  else swap_many ae (skolem_prenex p)


lemma idx_is_fo_pull_over_bin {k : nat} (ae ao : bool) {p q : form} :
idx_is_fo k p → idx_is_fo k q → 
idx_is_fo k (pull_over_bin ae ao p q) := sorry

lemma idx_is_fo_swap_many {k : nat} (ae : bool) {p : form} :
idx_is_fo (k + 1) p → idx_is_fo k (swap_many ae p) := sorry

lemma idx_is_fo_skolem_prenex (ae : bool) :
  ∀ {k : nat} {p : form}, idx_is_fo k p → idx_is_fo k (skolem_prenex ae p)  
| k ⟪b, a⟫           h0 := h0
| k (form.con b)     h0 := h0
| k (form.bin b p q) h0 := 
  by { cases h0, apply idx_is_fo_pull_over_bin; 
       apply idx_is_fo_skolem_prenex; assumption }
| k (form.qua b p)   h0 := 
  begin
    unfold skolem_prenex,
    by_cases h1 : ae = b,
    { subst h1, rw if_pos rfl,
      apply @idx_is_fo_skolem_prenex _ p h0 },
    rw if_neg h1, 
    apply idx_is_fo_swap_many,
    apply idx_is_fo_skolem_prenex,
    apply h0,
  end

lemma skolem_prenex_eqv [inhabited α] {ae : bool} :
  ∀ {p : form}, qua_are_fo (bnot ae) p → (skolem_prenex ae p <==α==> p) 
| ⟪b, a⟫           h0 := eqv_refl _ _
| (form.con b)     h0 := eqv_refl _ _
| (form.bin b p q) h0 := 
  eqv_trans 
    (pull_over_bin_eqv ae b _ _)
    (bin_eqv_bin
      (skolem_prenex_eqv h0.left)
      (skolem_prenex_eqv h0.right))
| (form.qua b p)   h0 := 
  begin
    unfold skolem_prenex,
    by_cases h1 : ae = b,
    { subst h1, rw if_pos rfl, 
      apply qua_eqv_qua (skolem_prenex_eqv h0.right) },
    rw if_neg h1,
    have h2 := bnot_eq_iff_ne.elim_right h1,
    apply eqv_trans (swap_many_eqv α _ 
      (idx_is_fo_skolem_prenex _ (h0.left h2))), rw h2,
    apply qua_eqv_qua (skolem_prenex_eqv h0.right)
end
  
def AE : form → form := skolem_prenex ff
def EA : form → form := skolem_prenex tt