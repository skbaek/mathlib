import .form

variable {α : Type}

local notation  `⊤*` := form.true
local notation  `⊥*` := form.false
local notation  `⟪` l `⟫` := form.lit l
local notation  p `∨*` q := form.or p q
local notation  p `∧*` q := form.and p q
local notation  `∀*` := form.fa
local notation  `∃*` := form.ex

local notation f `₀↦` a := update_zero a f

def exist_open : form → form
| (∃* p) := exist_open p
| p      := p

inductive is_exist_open : form → form → Prop
| refl {p}   : is_exist_open p p
| step {p q} : is_exist_open p q → is_exist_open p (∃* q)

lemma is_exist_open_exist_open :
  ∀ p : form, is_exist_open (exist_open p) p :=
by { form.induce; try {apply is_exist_open.refl},
     apply is_exist_open.step ih }

def fam_exv_of_fam_exv_exist_open {p q : form} :
  is_exist_open p q → p.fam_exv α → q.fam_exv α :=
begin
  intro h1,
  induction h1 with r r s h3 h4,
  { exact id },
  intros h2 M,
  cases (h4 h2 M) with v h5,
  refine ⟨v ∘ nat.succ, v 0, _⟩,
  have : ((v ∘ nat.succ) ₀↦ v 0) = v,
  { ext k, cases k; refl },
  rw this, exact h5
end

def fam_fav_of_closed_of_fam_exv_exist_open {p : form} :
  closed p → (exist_open p).fam_exv α → p.fam_fav α :=
begin
  intros h1 h2 M v,
  cases fam_exv_of_fam_exv_exist_open
    (is_exist_open_exist_open p) h2 M with w h3,
  rw holds_iff_holds_of_closed M v w h1,
  exact h3
end
