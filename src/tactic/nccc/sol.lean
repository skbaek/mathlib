import data.list.basic 

universe u 

variable {α : Type u}
--def update (m : nat) (a : α) (v : nat → α) : nat → α
--| n := if n = m then a else v n
--
--local notation v `{` m `↦` a `}` := update m a v

def update_zero (a : α) (f : nat → α) : nat → α
| 0     := a
| (k+1) := f k

def denot (α : Type u) : Type u := list α → (α × Prop)

def denot.default [inhabited α] : denot α := 
λ as, (default α, false)

def model (α : Type u) : Type u := nat → denot α

@[derive has_reflect, derive decidable_eq]
inductive atom : Type
| var : nat → atom
| app : atom → atom → atom

local notation `#` := atom.var
local notation a `&` b := atom.app a b

@[reducible] def sub : Type := list (nat × atom)

def sub.get (σ : sub) (k : nat) : option atom :=
prod.snd <$> (list.find (eq k ∘ prod.fst)) σ

namespace atom

def val (M : model α) : atom → denot α
| (# k)   := M k
| (a & b) := a.val ∘ list.cons (b.val []).fst

def subst (σ : sub) : atom → atom
| (# k) :=
  match σ.get k with
  | none   := # k
  | some s := s
  end
| (a & b) := subst a & subst b

lemma subst_eq_of_get_eq_none {σ : sub} {k : nat} :
  σ.get k = none → (# k).subst σ = # k :=
by {intro h1, simp only [h1, atom.subst]}

lemma subst_eq_of_get_eq_some {σ : sub} {k : nat} {a : atom} :
  σ.get k = some a → (# k).subst σ = a :=
by {intro h1, simp only [h1, atom.subst]}

def incr_idxs_ge (k : nat) : atom → atom
| (# m) := if k ≤ m then # (m + 1) else # m
| (a & b) := incr_idxs_ge a & incr_idxs_ge b 

def incr_idxs : atom → atom := incr_idxs_ge 0

end atom

def sub.incr_idxs : sub → sub :=
list.map (prod.map nat.succ (atom.incr_idxs))

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

end atom

def head_occ (k : nat) : atom → Prop
| (# m)         := k = m 
| (a & (# m))   := head_occ a
| (a & (b & c)) := head_occ a ∨ head_occ (b & c)

local notation f `₀↦` a := update_zero a f

@[derive has_reflect]
inductive form : Type
| false : form
| true : form
| lit : bool → atom → form
| or  : form → form → form
| and : form → form → form
| fa  : form → form
| ex  : form → form

local notation `⊤*`            := form.true
local notation `⊥*`            := form.false
local notation `⟪` b `,` a `⟫` := form.lit b a
local notation p `∨*` q        := form.or p q
local notation p `∧*` q        := form.and p q
local notation `∀*`            := form.fa
local notation `∃*`            := form.ex

def holds : model α → form → Prop
| M ⊤*       := _root_.true
| M ⊥*       := _root_.false
| M ⟪tt, a⟫  :=    (a.val M []).snd
| M ⟪ff, a⟫  :=  ¬ (a.val M []).snd
| M (p ∨* q) := holds M p ∨ holds M q
| M (p ∧* q) := holds M p ∧ holds M q
| M (∀* p)   := ∀ x : denot α, holds (M ₀↦ x) p
| M (∃* p)   := ∃ x : denot α, holds (M ₀↦ x) p

infix `⊨` : 1000 := holds 

def eqv (α : Type u) (p q : form) : Prop :=
∀ M : model α, (M ⊨ p ↔ M ⊨ q)

lemma eqv_trans {α : Type u} {p q r : form} :
  eqv α p q → eqv α q r → eqv α p r :=
λ h0 h1 M, by rw [h0 M, h1 M]

lemma eqv_refl (α : Type u) (p : form) : eqv α p p := λ M, by refl

namespace form

def size_of : form → nat
| ⊤*       := 1
| ⊥*       := 1
| ⟪_, _⟫   := 1
| (p ∨* q) := 1 + p.size_of + q.size_of
| (p ∧* q) := 1 + p.size_of + q.size_of
| (∀* p)   := 1 + p.size_of
| (∃* p)   := 1 + p.size_of

instance has_sizeof : has_sizeof form := ⟨size_of⟩ 

/- Increment all variable indices equal to or greater than k by 1. -/
def incr_idxs_ge : nat → form → form
| k ⊤*       := ⊤*
| k ⊥*       := ⊥*
| k ⟪b, a⟫   := ⟪b, a.incr_idxs_ge k⟫
| k (p ∨* q) := (incr_idxs_ge k p) ∨* (incr_idxs_ge k q)
| k (p ∧* q) := (incr_idxs_ge k p) ∧* (incr_idxs_ge k q)
| k (∀* p)   := ∀* (incr_idxs_ge (k + 1) p)
| k (∃* p)   := ∃* (incr_idxs_ge (k + 1) p)

def incr_idxs : form → form := incr_idxs_ge 0

def subst : sub → form → form
| σ ⊤*       := ⊤*
| σ ⊥*       := ⊥*
| σ ⟪b, a⟫   := ⟪b, a.subst σ⟫
| σ (p ∨* q) := (subst σ p) ∨* (subst σ q)
| σ (p ∧* q) := (subst σ p) ∧* (subst σ q)
| σ (∀* p)   := ∀* (subst σ.incr_idxs p)
| σ (∃* p)   := ∃* (subst σ.incr_idxs p)

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

end form

lemma holds_zero_update_incr_idxs {M : model α} {d : denot α} :
  ∀ p : form, (M ₀↦d) ⊨ p.incr_idxs ↔ M ⊨ p
| ⊤*       := iff.refl _
| ⊥*       := iff.refl _
| ⟪tt, a⟫  := sorry
| ⟪ff, a⟫  := sorry
| (q ∨* r) := sorry
| (q ∧* r) := sorry
| (∀* q)   := sorry
| (∃* q)   := sorry

def pull_fa_or_aux : form → form → form
| p (∀* q) := ∀* (pull_fa_or_aux (p.incr_idxs) q)
| p      q := p ∨* q

lemma pull_fa_or_aux_eqv  :
  ∀ p q : form, eqv α (pull_fa_or_aux p q) (p ∨* q)  
| p ⊤*       := by simp only [pull_fa_or_aux, eqv_refl]
| p ⊥*       := by simp only [pull_fa_or_aux, eqv_refl]
| p ⟪b, a⟫   := by simp only [pull_fa_or_aux, eqv_refl]
| p (q ∨* r) := by simp only [pull_fa_or_aux, eqv_refl]
| p (q ∧* r) := by simp only [pull_fa_or_aux, eqv_refl]
| p (∃* q)   := by simp only [pull_fa_or_aux, eqv_refl]
| p (∀* q)   := 
  begin
    intros M, 
    constructor; intro h0,
    { cases classical.em (M ⊨ p) with h1 h1,
      { left, exact h1 },
      right, intro d, 
      cases (pull_fa_or_aux_eqv _ q _).elim_left (h0 d) with h2 h2,
      { cases h1 ((holds_zero_update_incr_idxs p).elim_left h2) },
      exact h2 },
    intro d, 
    rw pull_fa_or_aux_eqv,
    cases h0,
    { left, 
      rw holds_zero_update_incr_idxs, 
      exact h0 },
    right, apply h0
  end

def pull_fa_and_aux : form → form → form
| p (∀* q) := ∀* (pull_fa_and_aux (p.incr_idxs) q)
| p      q := p ∧* q

lemma pull_fa_and_aux_eqv [inhabited α] :
  ∀ p q : form, eqv α (pull_fa_and_aux p q) (p ∧* q)  
| p ⊤*       := by simp only [pull_fa_and_aux, eqv_refl]
| p ⊥*       := by simp only [pull_fa_and_aux, eqv_refl]
| p ⟪b, a⟫   := by simp only [pull_fa_and_aux, eqv_refl]
| p (q ∨* r) := by simp only [pull_fa_and_aux, eqv_refl]
| p (q ∧* r) := by simp only [pull_fa_and_aux, eqv_refl]
| p (∃* q)   := by simp only [pull_fa_and_aux, eqv_refl]
| p (∀* q)   := 
  begin
    intros M, 
    constructor; intro h0,
    { refine ⟨_, λ d, _⟩, 
      { simpa only [holds_zero_update_incr_idxs] using
        ((pull_fa_and_aux_eqv _ _ _).elim_left
        (h0 $ denot.default)).left },
      exact ((pull_fa_and_aux_eqv _ _ _).elim_left (h0 d)).right },
    intro d,
    rw pull_fa_and_aux_eqv,
    refine ⟨(holds_zero_update_incr_idxs _).elim_right h0.left, h0.right _⟩
  end

def pull_fa_or : form → form → form
| (∀* p) q := ∀* (pull_fa_or p (q.incr_idxs))
| p      q := pull_fa_or_aux p  q

lemma pull_fa_or_eqv  :
  ∀ p q : form, eqv α (pull_fa_or p q) (p ∨* q)  
| ⊤*       r := by apply pull_fa_or_aux_eqv
| ⊥*       r := by apply pull_fa_or_aux_eqv
| ⟪b, a⟫   r := by apply pull_fa_or_aux_eqv
| (p ∨* q) r := by apply pull_fa_or_aux_eqv
| (p ∧* q) r := by apply pull_fa_or_aux_eqv
| (∃* p)   r := by apply pull_fa_or_aux_eqv
| (∀* p)   r := 
  begin
    intros M, 
    constructor; intro h0,
    { cases classical.em (M ⊨ r) with h1 h1,
      { right, exact h1 },
      left, intro d, 
      cases (pull_fa_or_eqv _ _ _).elim_left (h0 d) with h2 h2,
      { exact h2 },
      cases h1 ((holds_zero_update_incr_idxs r).elim_left h2) },
    intro d, 
    rw pull_fa_or_eqv,
    cases h0,
    { left, apply h0 },
    right, 
    rw holds_zero_update_incr_idxs, 
    exact h0 
  end

def pull_fa_and : form → form → form
| (∀* p) q := ∀* (pull_fa_and p (q.incr_idxs))
| p      q := pull_fa_and_aux p q

lemma pull_fa_and_eqv [inhabited α] :
  ∀ p q : form, eqv α (pull_fa_and p q) (p ∧* q)  
| ⊤*       r := by apply pull_fa_and_aux_eqv
| ⊥*       r := by apply pull_fa_and_aux_eqv
| ⟪b, a⟫   r := by apply pull_fa_and_aux_eqv
| (p ∨* q) r := by apply pull_fa_and_aux_eqv
| (p ∧* q) r := by apply pull_fa_and_aux_eqv
| (∃* p)   r := by apply pull_fa_and_aux_eqv
| (∀* p)   r := 
  begin
    intros M, 
    constructor; intro h0,
    { refine ⟨λ d, _, _⟩, 
      { exact ((pull_fa_and_eqv _ _ _).elim_left (h0 d)).left },
      simpa only [holds_zero_update_incr_idxs] using
      ((pull_fa_and_eqv _ _ _).elim_left
      (h0 $ denot.default)).right },
    intro d,
    rw pull_fa_and_eqv,
    refine ⟨h0.left _, (holds_zero_update_incr_idxs _).elim_right h0.right⟩
  end

def pull_fa_aux : form → form
| (∀* p) := 
  have hd : (p.subst [(0, (# 1) & (# 0)), (1, # 0)]).size_of < (∀* p).size_of,
  { rw form.size_of_subst, 
    simp only [form.size_of, nat.lt_succ_self, add_comm] }, 
  ∀* (pull_fa_aux (p.subst [(0, (# 1) & (# 0)), (1, # 0)]))
| p := ∃* p

def vfo_aux : nat → form → Prop
| k ⊤*       := true
| k ⊥*       := true
| k ⟪b, a⟫   := ¬ head_occ k a 
| k (p ∨* q) := vfo_aux k p ∧ vfo_aux k q
| k (p ∧* q) := vfo_aux k p ∧ vfo_aux k q 
| k (∃* p)   := vfo_aux (k + 1) p
| k (∀* p)   := vfo_aux (k + 1) p

def vfo : form → Prop
| ⊤*       := true
| ⊥*       := true
| ⟪b, a⟫   := true
| (p ∨* q) := vfo p ∧ vfo q
| (p ∧* q) := vfo p ∧ vfo q 
| (∃* p)   := vfo_aux 0 p ∧ vfo p
| (∀* p)   := vfo p


lemma sub.get_eq_none {σ : sub} {k : nat} : 
  σ.get k = none → ∀ s : nat × atom, s ∈ σ → k ≠ s.fst := 
begin
  intros h0 s h1,
  unfold sub.get at h0,
  cases h2 : list.find (eq k ∘ prod.fst) σ,
  { apply list.find_eq_none.elim_left h2 s h1 },
  rw h2 at h0, cases h0
end


open list

lemma atom.subst_var_eq {σ : sub} {k : nat} : 
  (∃ s ∈ σ, k = (s : nat × atom).fst) → 
  ∃ s ∈ σ, k = (s : nat × atom).fst ∧ (# k).subst σ = (s : nat × atom).snd := 
begin
  rintro ⟨s, h0, h1⟩, 
  cases h2 : find (eq k ∘ prod.fst) σ with t,
  { cases find_eq_none.elim_left h2 s h0 h1 },
  refine ⟨t, find_mem h2, ⟨_, _⟩⟩, 
  { apply find_some h2 },
  simp only [atom.subst, sub.get, h2, option.map_some]
end

lemma atom.subst_var_eq_self {σ : sub} {k : nat} : 
  ¬ (∃ s ∈ σ, k = (s : nat × atom).fst) → (# k).subst σ = # k := 
begin
  intro h0,
  unfold atom.subst, unfold sub.get,
  cases h2 : find (eq k ∘ prod.fst) σ with t, refl, 
  cases (h0 ⟨t, find_mem h2, _⟩  : false),
  apply find_some h2
end

lemma nat.ne_succ (n : nat) : n ≠ n.succ := sorry




lemma not_head_occ_subst (k m : nat) :
  head_occ k (atom.subst [(k, (# (k + 1) & (# k))), (k + 1, # k)] (# m))
  → head_occ (k + 1) (# m) :=
begin

end

#exit
lemma not_head_occ_subst (k : nat) :
   ∀ a : atom, ¬head_occ (k + 1) a → 
  ¬ head_occ k (atom.subst [(k, (# (k + 1) & (# k))), (k + 1, # k)] a)
| (# m) h0 :=
  begin
    by_cases h1 : (∃ s ∈ [(k, (# (k + 1) & (# k))), 
      (k + 1, # k)], m = (s : nat × atom).fst),
    { rcases atom.subst_var_eq h1 with ⟨s, h2, h3, h4⟩, 
      rw h4, 
      rw mem_cons_iff at h2, cases h2,
      { rw h2, apply nat.ne_succ },
      rw mem_singleton at h2,
      rw [h3, h2] at h0,
      cases (h0 rfl : false) },
    rw atom.subst_var_eq_self h1,
    intro hc,
    apply h1 ⟨_, or.inl rfl, hc.symm⟩
  end
| (a & (# m)) h0 :=
  begin
    intro h1, apply not_head_occ_subst a h0 _,
    simp only [atom.subst] at h1, 
    
  end


#exit
lemma vfo_aux_subst : 
  ∀ k : nat, ∀ p : form, vfo_aux (k + 1) p → 
   vfo_aux k (form.subst [(0, (# 1) & (# 0)), (1, # 0)] p) 
| k ⊤*       h0 := trivial
| k ⊥*       h0 := trivial
| k ⟪b, a⟫   h0 := 
  begin
   simp [vfo_aux, form.subst] at *,
  end
| k (p ∨* q) h0 := sorry
| k (p ∧* q) h0 := sorry
| k (∃* p)   h0 := sorry
| k (∀* p)   h0 := sorry

#exit
lemma vfo_subst {p : form} (σ : sub) :
  vfo p → vfo (p.subst σ) := sorry

lemma pull_fa_aux_eqv :
  ∀ p : form, vfo (∃* p) → eqv α (pull_fa_aux p) (∃* p)
| ⊤*       fh := by simp only [pull_fa_aux, eqv_refl]
| ⊥*       fh := by simp only [pull_fa_aux, eqv_refl]
| ⟪b, a⟫   fh := by simp only [pull_fa_aux, eqv_refl]
| (p ∨* q) fh := by simp only [pull_fa_aux, eqv_refl]
| (p ∧* q) fh := by simp only [pull_fa_aux, eqv_refl]
| (∃* p)   fh := by simp only [pull_fa_aux, eqv_refl]
| (∀* p)   fh := 
  have hd : (p.subst [(0, # 1&# 0), (1, # 0)]).size_of < (∀* p).size_of,
  { admit },
  begin
    simp [pull_fa_aux],
    have h0 := pull_fa_aux_eqv (p.subst [(0, # 1&# 0), (1, # 0)]),
    apply @eqv_trans α _ (∀* $ ∃* (p.subst [(0, # 1&# 0), (1, # 0)])),
    { intro M, constructor; intros h1 d,
      { apply (h0 ⟨_, _⟩ _).elim_left (h1 _),
      cases fh,
      
         },
      apply (h0 _ _).elim_right (h1 _) },

    intro M, constructor; intro h1,
    { apply classical.by_contradiction, intro hc,
      have h2 : ∀ d : denot α, ∃ e : denot α, ¬ ((M ₀↦ d) ₀↦ e) ⊨ p,
      { admit },



    
     }

  end

#check @eqv_trans

#exit
def pull_fa : form → form
| (p ∨* q) := pull_fa_fork (∨*) (pull_fa p) (pull_fa q) 
| (p ∧* q) := pull_fa_fork (∧*) (pull_fa p) (pull_fa q) 
| (∀* p)   := ∀* (pull_fa p)
| (∃* p)   := pull_fa_aux (pull_fa p)
| p        := p

#exit
def pnf_right (c : form → form → form) : form → form → form
| p (∀* q) := ∀* (pnf_right (p.incr_idxs 0) q)
| p (∃* q) := ∃* (pnf_right (p.incr_idxs 0) q)
| p      q := c p q

def pnf_left (c : form → form → form) : form → form → form
| (∀* p) q := ∀* (pnf_left p (q.incr_idxs 0))
| (∃* p) q := ∃* (pnf_left p (q.incr_idxs 0))
| p      q := pnf_right c p q

def pnf : form → form
| ⊤*       := ⊤*
| ⊥*       := ⊥*
| ⟪l⟫      := ⟪l⟫
| (p ∨* q) := pnf_left (∨*) (pnf p) (pnf q)
| (p ∧* q) := pnf_left (∧*) (pnf p) (pnf q)
| (∀* p)   := ∀* (pnf p)
| (∃* p)   := ∃* (pnf p)
