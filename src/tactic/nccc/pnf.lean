import .form


local notation  `⊤*` := form.true
local notation  `⊥*` := form.false
local notation  `⟪` l `⟫` := form.lit l
local notation  p `∧*` q := form.and p q
local notation  p `∨*` q := form.or p q
local notation  `∀*` := form.fa
local notation  `∃*` := form.ex

-- | ⊤*        := sorry
-- | ⊥*        := sorry
-- | ⟪⟨s, k, ts⟩⟫ := sorry
-- | (p ∧* q)  := sorry
-- | (p ∨* q)  := sorry
-- | (∀* p)  := sorry
-- | (∃* p)  := sorry

def pnf_right (c : form → form → form) : form → form → form
| p (∀* q) := ∀* (pnf_right (p.incr_vdx 0) q)
| p (∃* q) := ∃* (pnf_right (p.incr_vdx 0) q)
| p      q := c p q

def pnf_left (c : form → form → form) : form → form → form
| (∀* p) q := ∀* (pnf_left p (q.incr_vdx 0))
| (∃* p) q := ∃* (pnf_left p (q.incr_vdx 0))
| p      q := pnf_right c p q

/- Assumes ∀-free input formulas -/
def pnf : form → form
| ⊤*       := ⊤*
| ⊥*       := ⊥*
| ⟪l⟫      := ⟪l⟫
| (p ∨* q) := pnf_left (∨*) (pnf p) (pnf q)
| (p ∧* q) := pnf_left (∧*) (pnf p) (pnf q)
| (∀* p)   := ∀* (pnf p)
| (∃* p)   := ∃* (pnf p)

-- lemma valid_skolemize_core_imp (α : Type) (p : form) :

lemma valid_pnf_imp (α : Type) (p : form) :
  (pnf p).valid α → p.valid α := sorry
