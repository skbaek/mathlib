import .form .list

variable {α : Type}

local notation  `⊤*` := form.true
local notation  `⊥*` := form.false
local notation  `⟪` l `⟫` := form.lit l
local notation  p `∨*` q := form.or p q
local notation  p `∧*` q := form.and p q
local notation  `∀*` := form.fa
local notation  `∃*` := form.ex

@[reducible] def cla : Type := list lit

namespace cla

def is_pos (C : cla) : bool := C.all prod.fst

def vdxs (C : cla) : list nat := ⋃ (C.map lit.vdxs)

def holds (M : model α) (v : nat → α) (c : cla) : Prop :=
∀ l ∈ c, lit.holds M v l

def subst : sub → cla → cla :=
list.map ∘ lit.subst

lemma holds_subst {M : model α} {v : nat → α} {σ : sub} {c : cla} :
  holds M v (c.subst σ) ↔ holds M (val.subst M v σ) c :=
begin
  constructor; intros h1 l h2,
  { rw ← lit.holds_subst, apply h1,
    apply list.mem_map_of_mem _ h2 },
  { have h3 : ∃ x, x ∈ c ∧ lit.subst σ x = l,
    { rw ← list.mem_map, exact h2 },
    rcases h3 with ⟨x, h3, h4⟩,
    rw [←h4, lit.holds_subst],
    apply h1 _ h3 }
end

end cla

@[reducible] def mat : Type := list cla

namespace mat

def holds (M : model α) (v : nat → α) (A : mat) : Prop :=
∃ C ∈ A, cla.holds M v C

lemma holds_cons {M : model α} {v : nat → α} (c : cla) (m : mat) :
mat.holds M v (c :: m) ↔ (c.holds M v ∨ m.holds M v) :=
by simp only [mat.holds, list.exists_mem_cons_iff]

def fam_exv (α m) : Prop :=
∀ M : model α, ∃ v : nat → α, (holds M v m)

end mat

def dnf : form → mat
| ⊤*       := [[]]
| ⊥*       := []
| ⟪l⟫      := [[l]]
| (p ∧* q) := (list.product (dnf p) (dnf q)).map (λ x, x.fst ++ x.snd)
| (p ∨* q) := (dnf p) ++ (dnf q)
| (∀* p)   := [] -- Irrelevant
| (∃* p)   := [] -- Irrelevant

open list

lemma holds_of_dnf_holds {M : model α} {v : nat → α} :
  ∀ p : form, quant_free p → (dnf p).holds M v → p.holds M v :=
begin
  form.induce; intros h1 h2;
  rcases h2 with ⟨c, h3, h4⟩,
  { cases h3 },
  { trivial },
  { rw eq_of_mem_singleton h3 at h4,
    exact h4 _ (or.inl rfl) },
  { cases mem_append.elim_left h3 with h5 h5,
    apply or.inl (ihp h1.left ⟨c, h5, h4⟩),
    apply or.inr (ihq h1.right ⟨c, h5, h4⟩) },
  { rcases mem_map.elim_left h3 with ⟨cc, h5, h6⟩,
    cases cc with cl cr,
    cases mem_product.elim_left h5 with hl hr,
    rw ← h6 at h4,
    cases forall_mem_append.elim_left h4 with hl' hr',
    apply and.intro (ihp h1.left ⟨_, hl, _⟩) (ihq h1.right ⟨_, hr, _⟩);
    assumption },
  repeat {cases h1}
end

lemma fam_exv_of_dnf_fam_exv {p : form} :
  quant_free p → (dnf p).fam_exv α → p.fam_exv α :=
begin
  intros h0 h1 M,
  cases h1 M with v h1,
  refine ⟨v, holds_of_dnf_holds p h0 h1⟩
end
