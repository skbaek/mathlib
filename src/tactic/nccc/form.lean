import .sub .logic .nat

universe u 

variables {α β : Type u}

open nat

local notation f `₀↦` a := assign a f
local notation `#` := term.var
local notation a `&` b := term.app a b

postfix  `ₑ` : 1000 := evaluate 
postfix  `ᵈ` : 1000 := denote
local infix `⬝` := value.app

@[derive has_reflect]
inductive form : Type
| lit : bool → term → form
| bin : bool → form → form → form
| qua : bool → form → form

local notation `⟪` b `,` a `⟫` := form.lit b a
local notation p `∨*` q        := form.bin tt p q
local notation p `∧*` q        := form.bin ff p q
local notation `∃*`            := form.qua tt 
local notation `∀*`            := form.qua ff

def holds : model α → form → Prop
| M ⟪tt, a⟫  :=   (a.val M []).snd
| M ⟪ff, a⟫  := ¬ (a.val M []).snd
| M (p ∨* q) := holds M p ∨ holds M q
| M (p ∧* q) := holds M p ∧ holds M q
| M (∀* p)   := ∀ x : value α, holds (M ₀↦ x) p
| M (∃* p)   := ∃ x : value α, holds (M ₀↦ x) p

infix `⊨` : 1000 := holds 

def fam (α : Type u) (p : form) : Prop :=
  ∀ M : model α, M ⊨ p

lemma fam_fa (α : Type u) (p : form) : 
  fam α (∀* p) ↔ fam α p :=
begin
  constructor; intros h0 M,
  { have h1 := h0 M.decr_idxs (M 0), 
    rwa assign_decr_idxs at h1 },
  intro v, apply h0
end

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
| (form.bin _ p q) := p.size_of + q.size_of + 1
| (form.qua _ p)   := p.size_of + 1

instance has_sizeof : has_sizeof form := ⟨size_of⟩ 

/- Increment all variable indices equal to or greater than k by 1. -/
def incr_idxs_ge : nat → form → form
| k ⟪b, a⟫           := ⟪b, a.incr_idxs_ge k⟫
| k (form.bin b p q) := form.bin b (incr_idxs_ge k p) (incr_idxs_ge k q)
| k (form.qua b p)   := form.qua b (incr_idxs_ge (k + 1) p)

def incr_idxs : form → form := incr_idxs_ge 0

def subst : sub → form → form
| σ ⟪b, a⟫           := ⟪b, a.subst σ⟫
| σ (form.bin b p q) := form.bin b (subst σ p) (subst σ q)
| σ (form.qua b p)   := form.qua b (subst σ.incr_idxs p)

lemma size_of_subst :
  ∀ p : form, ∀ σ : sub, (p.subst σ).size_of = p.size_of 
| ⟪b, a⟫           σ := rfl
| (form.bin b p q) σ := 
  by simp only [size_of, subst, size_of_subst p, size_of_subst q]
| (form.qua b p)   σ := 
  by simp only [size_of, subst, size_of_subst p]

@[simp] lemma size_of_incr_idxs_ge :
  ∀ k : nat, ∀ p : form, (p.incr_idxs_ge k).size_of = p.size_of 
| k ⟪b, a⟫           := rfl
| k (form.bin b p q) := 
  by simp only [ size_of, size_of_incr_idxs_ge k p, 
     incr_idxs_ge, size_of_incr_idxs_ge k q ]
| k (form.qua b p)   := 
  by simp only [size_of, incr_idxs_ge, size_of_incr_idxs_ge _ p]

@[simp] lemma size_of_incr_idxs :
  ∀ p : form, p.incr_idxs.size_of = p.size_of := 
size_of_incr_idxs_ge _

def neg : form → form 
| ⟪b, a⟫           := ⟪bnot b, a⟫ 
| (form.bin b p q) := form.bin (bnot b) p.neg q.neg
| (form.qua b p)   := form.qua (bnot b) p.neg 

end form

lemma holds_bin_iff_holds_bin 
  {M N : model α} {p q r s : form} {b : bool} :
  (M ⊨ p ↔ N ⊨ q) → (M ⊨ r ↔ N ⊨ s) → 
  (M ⊨ form.bin b p r ↔ N ⊨ form.bin b q s) :=
by { intros h0 h1, cases b;
     apply pred_mono_2; assumption }

lemma bin_eqv_bin {p q r s : form} {b : bool} :
  (p <==α==> q) → (r <==α==> s) → 
  (form.bin b p r <==α==> form.bin b q s) := 
by { intros h0 h1 M, 
     apply holds_bin_iff_holds_bin (h0 _) (h1 _) }

lemma bin_comm (b : bool) (p q : form) : 
  form.bin b p q <==α==> form.bin b q p := 
by {intro M, cases b, apply and.comm, apply or.comm}

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
  by cases b; 
     simp only [classical.not_not, form.neg, 
     holds, bool.bnot_true, bool.bnot_false]
| M (p ∨* q) := 
  begin
    unfold holds, 
    rw not_or_distrib,
    apply pred_mono_2; 
    apply holds_neg
  end
| M (p ∧* q) := 
  begin
    unfold holds, 
    rw @not_and_distrib _ _ (classical.dec _),
    apply pred_mono_2; apply holds_neg
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
 
lemma holds_incr_idxs_ge : 
  ∀ M N : model α, ∀ k : nat, 
    (∀ m < k, M m = N m) → 
    (∀ m ≥ k, M (m + 1) = N m) → 
    ∀ p : form, M ⊨ p.incr_idxs_ge k ↔ N ⊨ p 
| M N k h0 h1 ⟪b, a⟫ := 
  by cases b; simp [form.incr_idxs_ge, 
     holds, val_incr_idxs_ge h0 h1 a]
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

lemma neg_subst :
  ∀ p : form, ∀ σ : sub, (p.subst σ).neg <==α==> (p.neg.subst σ)
| ⟪b, a⟫       σ := by apply eqv_refl 
| (form.bin b p q) σ := 
  by { intro M, apply holds_bin_iff_holds_bin;
       apply neg_subst }
| (form.qua b p)   σ := 
  by { intro M, apply holds_qua_iff_holds_qua,
       intro v, apply neg_subst }

lemma neg_eqv_neg (p q : form) :
  (p.neg <==α==> q.neg) ↔ (p <==α==> q) :=
begin
  apply forall_iff_forall, intro M,
  rw [holds_neg, holds_neg, @not_iff_not _ _ _ _], 
  repeat {apply classical.dec _}
end

lemma neg_incr_idxs_ge : 
  ∀ k : nat, ∀ p : form, (p.incr_idxs_ge k).neg = p.neg.incr_idxs_ge k 
| k ⟪b, a⟫           := by cases b; refl
| k (form.bin b p q) := 
  by simp only [form.neg, form.incr_idxs_ge,
     eq_self_iff_true, neg_incr_idxs_ge, and_self ]
| k (form.qua b p) := 
  by simp only [form.neg, form.incr_idxs_ge,
     eq_self_iff_true, neg_incr_idxs_ge, and_self ]

lemma neg_incr_idxs (p : form) :
  p.incr_idxs.neg = p.neg.incr_idxs :=
neg_incr_idxs_ge 0 p

lemma holds_subst :
  ∀ (M : model α) (p : form) (σ : sub), 
  M ⊨ (p.subst σ) ↔ M.subst σ ⊨ p  
| M ⟪b, a⟫ σ := 
  by cases b; simp only [form.subst, holds, val_subst M σ a]
| M (form.bin b p q) σ := 
  by apply holds_bin_iff_holds_bin; apply holds_subst
| M (form.qua b p)   σ := 
  by { apply holds_qua_iff_holds_qua, intro v,
       simp only [model.assign_subst, holds_subst] }