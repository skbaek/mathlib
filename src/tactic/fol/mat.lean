import .folize .list

universe u

variable {α : Type u}

open list

local notation `&₁`     := term.sym
local notation a `&₁` b := term.app a b
local notation a `#₁` k := term.vpp a k

local notation `⟪` b `,` a `⟫₁` := form.lit b a
local notation p `∨₁` q        := form.bin tt p q
local notation p `∧₁` q        := form.bin ff p q

@[reducible] def lit : Type := bool × term
@[reducible] def cla : Type := list lit
@[reducible] def mat : Type := list cla

namespace lit

def neg : lit → lit
| ⟨b, a⟩ := ⟨bnot b, a⟩

def repr : lit → string
| ⟨b, a⟩ := (if b then "" else "¬") ++ a.repr

instance has_repr : has_repr lit := ⟨repr⟩

meta instance has_to_format : has_to_format lit := ⟨λ x, repr x⟩

def vdxs : lit → list nat
| ⟨b, a⟩ := a.vdxs

def holds (M : model α) (v : nat → α) : lit → Prop
| (tt, a)  :=    (a.val M v []).snd
| (ff, a)  :=  ¬ (a.val M v []).snd

def subst (σ : sub) : lit → lit
| (b, a) := (b, a.subst σ)

lemma holds_neg (M : model α) (v : nat → α) (l : lit) :
  holds M v l.neg ↔ ¬ holds M v l :=
by { cases l with b; cases b; simp only
     [bnot, neg, holds, list.map, classical.not_not] }

lemma holds_subst (M : model α) (v : vas α) (σ : sub) (l : lit) :
  holds M v (l.subst σ) ↔ holds M (v.subst M σ) l :=
by { cases l with b a, cases b;
     simp only [holds, subst, vas.subst,
     list.map_map, term.val_subst] }

end lit

namespace cla

def is_pos (C : cla) : bool := C.all prod.fst

def vdxs (C : cla) : list nat := ⋃ (C.map lit.vdxs)

def subst : sub → cla → cla :=
list.map ∘ lit.subst

def holds (M : model α) (v : nat → α) (c : cla) : Prop :=
∀ l ∈ c, lit.holds M v l

lemma holds_subst {M : model α} {v : vas α} {σ : sub} {c : cla} :
  holds M v (c.subst σ) ↔ holds M (v.subst M σ) c :=
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

namespace mat

def holds (M : model α) (v : nat → α) (m : mat) : Prop :=
∃ c ∈ m, cla.holds M v c

lemma holds_cons {M : model α} {v : nat → α} (c : cla) (m : mat) :
mat.holds M v (c :: m) ↔ (c.holds M v ∨ m.holds M v) :=
by simp only [mat.holds, list.exists_mem_cons_iff]

def fam_exv (α : Type u) (m : mat) : Prop :=
∀ M : model α, ∃ v : nat → α, m.holds M v

end mat

def dnf : form → mat
| ⟪b, a⟫₁   := [[(b, a)]]
| (p ∧₁ q) := (list.product (dnf p) (dnf q)).map (λ x, x.fst ++ x.snd)
| (p ∨₁ q) := (dnf p) ++ (dnf q)

lemma holds_of_holds_dnf {M : model α} {v : nat → α} :
  ∀ p : form, (dnf p).holds M v → p.holds M v
| ⟪b, a⟫₁ h0 :=
  begin
    rcases h0 with ⟨c, h3, h4⟩,
    rw eq_of_mem_singleton h3 at h4,
    cases b; exact h4 _ (or.inl rfl)
  end
| (p ∨₁ q) h0 :=
  begin
    rcases h0 with ⟨c, h3, h4⟩,
    cases mem_append.elim_left h3 with h5 h5,
    apply or.inl (holds_of_holds_dnf _ ⟨c, h5, h4⟩),
    apply or.inr (holds_of_holds_dnf _ ⟨c, h5, h4⟩)
  end
| (p ∧₁ q) h0 :=
  begin
    rcases h0 with ⟨c, h3, h4⟩,
    rcases mem_map.elim_left h3 with ⟨⟨_, _⟩, h5, h6⟩,
    cases mem_product.elim_left h5 with hl hr,
    rw ← h6 at h4,
    cases forall_mem_append.elim_left h4,
    refine ⟨ holds_of_holds_dnf _ ⟨_, hl, _⟩,
             holds_of_holds_dnf _ ⟨_, hr, _⟩ ⟩;
    assumption,
  end

lemma fam_exv_of_dnf_fam_exv {p : form} :
  (dnf p).fam_exv α → p.fam_exv α :=
by { intros h1 M, cases h1 M with v h1,
     refine ⟨v, holds_of_holds_dnf p h1⟩ }

def normalize : form₂ → mat :=
dnf ∘ form₂.folize 0 ∘ QDFy ff

lemma holds_of_fam_exv_normalize
  [inhabited α] (p : form₂)  :
  foq tt p → (normalize p).fam_exv α → holds (model.default α) p :=
begin
  intros h0 h1,
  have h2 := fam_exv_of_dnf_fam_exv h1,
  have h3 := fam_of_fam_exv_folize _
    (foq_prenexify _ $ foq_swap_all _ h0)
    (QDF_QDFy _ _) h2 (model.default α),
  rwa [prenexify_eqv _ (model.default α),
      swap_all_eqv _ (model.default α)] at h3,
  apply h0,
end
