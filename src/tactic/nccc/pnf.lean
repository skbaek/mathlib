import .form

variable {α : Type}

local notation  `⊤*` := form.true
local notation  `⊥*` := form.false
local notation  `⟪` l `⟫` := form.lit l
local notation  p `∧*` q := form.and p q
local notation  p `∨*` q := form.or p q
local notation  `∀*` := form.fa
local notation  `∃*` := form.ex

def pnf_right (c : form → form → form) : form → form → form
| p (∀* q) := ∀* (pnf_right (p.incr_vdxs 0) q)
| p (∃* q) := ∃* (pnf_right (p.incr_vdxs 0) q)
| p      q := c p q

def pnf_left (c : form → form → form) : form → form → form
| (∀* p) q := ∀* (pnf_left p (q.incr_vdxs 0))
| (∃* p) q := ∃* (pnf_left p (q.incr_vdxs 0))
| p      q := pnf_right c p q

def pnf : form → form
| ⊤*       := ⊤*
| ⊥*       := ⊥*
| ⟪l⟫      := ⟪l⟫
| (p ∨* q) := pnf_left (∨*) (pnf p) (pnf q)
| (p ∧* q) := pnf_left (∧*) (pnf p) (pnf q)
| (∀* p)   := ∀* (pnf p)
| (∃* p)   := ∃* (pnf p)

lemma fam_fav_of_fam_fav_pnf {p : form} :
  (pnf p).fam_fav α → p.fam_fav α := sorry
