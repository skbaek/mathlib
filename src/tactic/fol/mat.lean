import .swap tactic.interactive
universe u

variables {α β : Type u}

open nat

local notation f `₀↦` a := assign a f
postfix  `ₑ` : 1000 := evaluate
postfix  `ᵈ` : 1000 := denote
local infix `⬝` := value.app

namespace fol

@[derive has_reflect, derive decidable_eq]
inductive term : Type
| sym : nat  → term
| app : term → term → term
| vpp : term → nat  → term

inductive form : Type
| lit : bool → term → form
| bin : bool → form → form → form

def term.val (M : model α) (v : nat → α) : term → value α
| (term.sym k)   := M k
| (term.app a b) := a.val ∘ list.cons (b.val []).fst
| (term.vpp a k) := a.val ∘ list.cons (v k)

def form.holds (M : model α) (v : nat → α) : form → Prop
| (form.lit tt a)   :=   (a.val M v []).snd
| (form.lit ff a)   := ¬ (a.val M v []).snd
| (form.bin tt p q) := p.holds ∨ q.holds
| (form.bin ff p q) := p.holds ∧ q.holds

lemma holds_bin_iff_holds_bin
  {M N : model α} {v w : nat → α} {p q r s : form} {b : bool} :
  (p.holds M v ↔ q.holds N w) →
  (r.holds M v ↔ s.holds N w) →
  ((form.bin b p r).holds M v ↔ (form.bin b q s).holds N w) := sorry

end fol

section

def fam_exv (α : Type u) (p : fol.form) : Prop :=
∀ M : model α, ∃ v : nat → α, p.holds M v

local notation `&`     := fol.term.sym
local notation a `&` b := fol.term.app a b
local notation a `#` k := fol.term.vpp a k

local notation `⟪` b `,` a `⟫` := fol.form.lit b a
local notation p `∨*` q        := fol.form.bin tt p q
local notation p `∧*` q        := fol.form.bin ff p q

def term.folize (k : nat) : term → fol.term
| (term.var m) := (& (m - k))
| (term.app a (term.var m)) :=
  if m < k
  then a.folize # m
  else a.folize & (& (m - k))
| (term.app a (term.app b c)) :=
  a.folize & (term.app b c).folize

def form.folize : nat → form → fol.form
| k (form.lit b t)   := ⟪b, t.folize k⟫
| k (form.bin b p q) := fol.form.bin b (p.folize k) (q.folize k)
| k (form.qua tt p)  := p.folize k.succ
| k (form.qua ff p)  := p.folize k

def term.fov_lt (k : nat) (a : term) : Prop :=
∀ m < k, a.fov m


lemma fov_lt_of_fov_lt_app_left {k : nat} {a b : term} :
  (term.app a b).fov_lt k → a.fov_lt k :=
λ h0 m h1, (h0 m h1).left

lemma fov_lt_of_fov_lt_app_right {k : nat} {a b c : term} :
  (term.app a (term.app b c)).fov_lt k → (term.app b c).fov_lt k :=
λ h0 m h1, (h0 m h1).right

def form.fov_lt (k : nat) (p : form) : Prop :=
∀ m < k, p.fov m

lemma fov_lt_of_fov_lt_bin_left {b : bool} {k : nat} {p q : form} :
  (form.bin b p q).fov_lt k → p.fov_lt k :=
λ h0 m h1, (h0 m h1).left

lemma fov_lt_of_fov_lt_bin_right {b : bool} {k : nat} {p q : form} :
  (form.bin b p q).fov_lt k → q.fov_lt k :=
λ h0 m h1, (h0 m h1).right

def exs : nat → form → form
| 0       p := p
| (k + 1) p := form.qua tt (exs k p)

lemma exs_ex :
  ∀ k : nat, ∀ p : form,
  exs k (form.qua tt p) = exs (k + 1) p
| 0       p := rfl
| (k + 1) p := by {unfold exs, rw exs_ex, refl}

-- lemma fov_exs :
--   ∀ {k m : nat} {p : form}, fov k (exs m p) → fov (k + m) p
-- | k 0       p h0 := h0
-- | k (m + 1) p h0 :=
--   by { convert (@fov_exs (k + 1) m _ h0) using 1,
--        simp only [add_comm,  add_left_comm] }
-- lemma exists_exs :
--   ∀ {p : form}, foq tt p → is_E p →
--   ∃ k : nat, ∃ q : form,
--     (fov_lt k q ∧ is_QF q ∧ p = exs k q)
-- | (form.lit b a)   h0 h1 := ⟨0, (form.lit b a),   trivial, h1, rfl⟩
-- | (form.bin b p q) h0 h1 := ⟨0, (form.bin b p q), trivial, h1, rfl⟩
-- | (form.qua tt p)  h0 h1 :=
--   begin
--     rcases exists_exs h0.right h1 with ⟨k, q, h2, h3, h4⟩,
--     refine ⟨k.succ, q, ⟨_, h2⟩, h3, _⟩,
--     { convert @fov_exs 0 k q _,
--       { rw zero_add },
--       rw ← h4, exact h0.left rfl },
--     congr'
--   end
-- | (form.qua ff p)  h0 h1 := by cases h1
--

--lemma holds_of_exv_folize :
--  ∀ {k : nat} {p : form} {M : model α},
--  is_QF p → fov_lt k p →
--  (∃ v : nat → α, (p.folize k).holds M v) →
--  (holds M $ exs k p)

lemma sub_eq_succ_sub_succ {k m : nat} :
  k + 1 ≤ m → m - k = succ (m - (k + 1)) :=
begin
  intro h0,
  rw succ_le_iff at h0,
  rw [← nat.sub_sub, ← pred_eq_sub_one, succ_pred_eq_of_pos _],
  simpa only [gt, nat.lt_sub_left_iff_add_lt] using h0
end

lemma val_folize_succ {k : nat} (M : model α) (v : nat → α) :
  ∀ {a : term}, a.fov_lt (k + 1) →
  (a.folize $ k + 1).val M v = (a.folize k).val (M ₀↦ (v k)ₑ) v
| (term.var m) h0 :=
  begin
    by_cases h1 : m < k + 1,
    { cases h0 m h1 rfl },
    rw not_lt at h1,
    simp only [term.folize, fol.term.val],
    rw sub_eq_succ_sub_succ h1, refl,
  end
| (term.app a (term.var m)) h0 :=
  begin
    have h := val_folize_succ (fov_lt_of_fov_lt_app_left h0),
    unfold term.folize,
    by_cases h1 : m < k,
    { rw if_pos h1,
      rw if_pos (lt_trans h1 $ lt_succ_self _),
      unfold fol.term.val, rw h },
    rw if_neg h1,
    rw not_lt at h1,
    by_cases h2 : m = k,
    { rw h2, rw if_pos (lt_succ_self _),
      unfold fol.term.val,
      rw [h, nat.sub_self k], refl },
    have h3 : k + 1 ≤ m,
    { rw le_iff_eq_or_lt at h1,
      cases h1,
      { cases h2 h1.symm },
      rw succ_le_iff, exact h1 },
    rw if_neg (not_lt.elim_right h3),
    unfold fol.term.val,
    rw [h, sub_eq_succ_sub_succ h3], refl
  end
| (term.app a (term.app b c)) h0 :=
  by simp only [term.folize, fol.term.val,
     val_folize_succ (fov_lt_of_fov_lt_app_left h0),
     val_folize_succ (fov_lt_of_fov_lt_app_right h0)]

lemma holds_folize_succ {k : nat} (M : model α) (v : nat → α) :
  ∀ p : form, is_QF p → p.fov_lt (k + 1) →
  ((p.folize $ k + 1).holds M v ↔ (p.folize k).holds (M ₀↦ (v k)ₑ) v)
| (form.lit b a) h0 h1 :=
  by { cases b; --;
       simp only  [form.folize, fol.term.val,
         fol.form.holds, val_folize_succ M v h1] }
| (form.bin b p q) h0 h1 :=
  begin
    apply fol.holds_bin_iff_holds_bin,
    { exact holds_folize_succ _ h0.left (fov_lt_of_fov_lt_bin_left h1) },
    exact holds_folize_succ _ h0.right (fov_lt_of_fov_lt_bin_right h1),
  end

lemma forall_lt_of_forall_lt_succ {k : nat} {p : nat → Prop} :
  (∀ m < (k + 1), p m) → (∀ m < k, p m) :=
λ h0 m h1, h0 _ (lt_trans h1 $ lt_succ_self _)

lemma forall_lt_zero {p : nat → Prop} : (∀ m < 0, p m) :=
λ m h, by cases h

lemma val_folize_zero (M : model α) (v : nat → α) :
  ∀ a : term, (a.folize 0).val M v = a.val M
| (term.var k) := rfl
| (term.app a (term.var k)) :=
  begin
    unfold term.folize,
    have h0 : ¬ k < 0,
    { rw not_lt, apply nat.zero_le },
    rw if_neg h0,
    simp only [fol.term.val, term.val, nat.sub_zero,
      val_folize_zero a, eq_self_iff_true]
  end
| (term.app a (term.app b c)) :=
  by simp only [fol.term.val, term.val, nat.sub_zero,
    val_folize_zero a, val_folize_zero (term.app b c),
    eq_self_iff_true, term.folize]

lemma holds_folize_zero (M : model α) (v : nat → α) :
  ∀ {p : form}, is_QF p → ((p.folize 0).holds M v ↔ holds M p)
| (form.lit b a) h0 :=
  by cases b;
     simp only [holds, fol.form.holds,
       form.folize, val_folize_zero]
| (form.bin b p q) h0 :=
  by { cases b; apply pred_mono_2;
       simp only [ holds, fol.form.holds, form.folize,
       holds_folize_zero h0.left,
       holds_folize_zero h0.right ] }


lemma holds_of_exv_folize :
  ∀ {p : form} {k : nat} {M : model α},
  foq tt p → is_E p → p.fov_lt k →
  (∃ v : nat → α, (p.folize k).holds M v) →
  (holds M $ exs k p)
| (form.lit b a) 0  :=
  by { intros M h0 h1 h2 h3,
       cases h3 with v h3,
       rwa holds_folize_zero _ _ h1 at h3 }
| (form.lit b a) (k + 1) :=
  begin
    intros M h0 h1 h2 h3,
    cases h3 with v h3,
    rw holds_folize_succ _ _ (form.lit b a) trivial h2 at h3,
    have h5 : (M ₀↦v k ₑ) ⊨exs k (form.lit b a) :=
      @holds_of_exv_folize (form.lit b a) k _ trivial
        trivial (forall_lt_of_forall_lt_succ h2) ⟨v, h3⟩,
    refine ⟨(v k)ₑ, h5⟩
  end
| (form.bin b p q) 0 :=
  by { intros M h0 h1 h2 h3,
       cases h3 with v h3,
       rwa holds_folize_zero _ _ h1 at h3 }
| (form.bin b p q) (k + 1) :=
  begin
intros M h0 h1 h2 h3,
    cases h3 with v h3,
    rw holds_folize_succ _ _ (form.bin b p q) h1 h2 at h3,
    have h5 : (M ₀↦v k ₑ) ⊨exs k (form.bin b p q) :=
      @holds_of_exv_folize (form.bin b p q) k _ h0
        h1 (forall_lt_of_forall_lt_succ h2) ⟨v, h3⟩,
    refine ⟨(v k)ₑ, h5⟩,
  end
| (form.qua tt p) k :=
  begin
    intros M h0 h1 h2 h3,
    have h5 : p.fov_lt (k + 1),
    { rintro ⟨m⟩; intro h4,
      { exact h0.left rfl },
      rw succ_lt_succ_iff at h4,
      exact h2 _ h4 },
    rw exs_ex,
    exact @holds_of_exv_folize p (k + 1) M h0.right h1 h5 h3,
  end
| (form.qua ff p) k := λ _ _  h, by cases h

lemma fam_of_fam_exv_folize_zero :
  ∀ {p : form}, foq tt p → is_E p → fam_exv α (p.folize 0) → fam α p :=
λ p h0 h1 h2 M, @holds_of_exv_folize α p 0 M h0 h1 forall_lt_zero (h2 M)

lemma fam_of_fam_exv_folize :
  ∀ p : form, foq tt p → is_AE p →
  fam_exv α (p.folize 0) → fam α p
| (form.lit b a)   := fam_of_fam_exv_folize_zero
| (form.bin b p q) := fam_of_fam_exv_folize_zero
| (form.qua tt p)  := fam_of_fam_exv_folize_zero
| (form.qua ff p)  :=
  λ h0 h1 h2, (fam_fa _ _).elim_right
    (fam_of_fam_exv_folize p h0.right h1 h2)


#exit


@[reducible] def lit : Type := bool × term
@[reducible] def cla : Type := list lit
@[reducible] def mat : Type := list cla

def lit.holds (M : model α) (v : nat → α) : lit → Prop
| (tt, a)  :=    (a.val M v []).snd
| (ff, a)  :=  ¬ (a.val M v []).snd

def cla.holds (M : model α) (v : nat → α) (c : cla) : Prop :=
∀ l ∈ c, lit.holds M v l

def mat.holds (M : model α) (v : nat → α) (m : mat) : Prop :=
∃ c ∈ m, cla.holds M v c

def fam_exv (α : Type u) (m : mat) : Prop :=
∀ M : model α, ∃ v : nat → α, m.holds M v




#exit
def dnf : nat → form → mat
| k ⟪b, a⟫   := [[(b, symbolize k a)]]
| k (p ∨* q) := dnf k p ++ dnf k q
| k (p ∧* q) :=
  (list.product (dnf k p) (dnf k q)).map (λ x, x.fst ++ x.snd)
| k (∀* p)   := dnf k p
| k (∃* p)   := dnf k.succ p

lemma fam_exv_dnf :
  ∀ k : nat, ∀ p : form, is_E p →
  (fam_exv α (dnf k p) ↔ fam α p)
| k (∃* p) h0 :=
  begin
    simp only [dnf],
    have h1 := fam_exv_dnf k.succ p h0,

  end


#exit
lemma fam_exv_dnf_zero :
  ∀ p : form, is_AE p →
  (fam_exv α (dnf 0 p) ↔ fam α p)
| (∀* p) h0 :=
  iff.trans
    (fam_exv_dnf_zero p h0)
    (fam_fa _ _).symm
| (∃* p)           h0 := fam_exv_dnf 0 _ h0
| (form.bin b p q) h0 := fam_exv_dnf 0 _ h0
| ⟪b, a⟫           h0 := fam_exv_dnf 0 _ h0


#exit

def mix (M N : model α) (k : nat) : model α :=
λ m, if m < k then M k else N k

def lit.holds (M N : model α) (k : nat) : lit → Prop
| (tt, a) :=   (a.val (mix M N k) []).snd
| (ff, a) := ¬ (a.val (mix M N k) []).snd


#exit
