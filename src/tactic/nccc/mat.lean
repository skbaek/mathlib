import .form

local notation  `⊤*` := form.true
local notation  `⊥*` := form.false
local notation  `⟪` l `⟫` := form.lit l
local notation  p `∨*` q := form.or p q
local notation  p `∧*` q := form.and p q
local notation  `∀*` := form.fa
local notation  `∃*` := form.ex

@[reducible] def mat : Type := list (list lit)

namespace mat

variable {α : Type}

def holds (M : model α) (v : nat → α) (m : mat) : Prop :=
∃ c ∈ m, ∀ l ∈ c, lit.holds M v l

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
