import .form

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

def is_pos (C : cla) : bool := C.all lit.sign

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

def valsat (α m) : Prop :=
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

lemma form_valsat_of_mat_valsat (α : Type) (p : form) :
  p.quant_free → (dnf p).valsat α → p.valsat α := sorry






