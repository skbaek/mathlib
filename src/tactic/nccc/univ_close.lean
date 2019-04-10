import .form

variable {α : Type}

local notation  `⊤*` := form.true
local notation  `⊥*` := form.false
local notation  `⟪` l `⟫` := form.lit l
local notation  p `∨*` q := form.or p q
local notation  p `∧*` q := form.and p q
local notation  `∀*` := form.fa
local notation  `∃*` := form.ex

local notation m `↦` a := update m a

def univ_close_core (p : form) :
  nat → model α → Prop
| 0     M :=  p.holds M (λ _, M.inhab)
| (k+1) M :=
  match p.symb_arity k with
  | none   := ∀ u : unit, univ_close_core k M
  | some (tt,m) :=
    ∀ r : arity α Prop m, univ_close_core k
    {M with rels  := (k ↦ r.app_list _root_.false) M.rels}
  | some (ff,m) :=
    ∀ f : arity α α m, univ_close_core k
    {M with funs := (k ↦ f.app_list M.inhab) M.funs}
  end

lemma univ_close_core_of_fam_fav (p : form) (h1 : p.fam_fav α) :
  ∀ (k : nat) (M : model α), univ_close_core p k M
| 0 M     := by apply h1
| (k+1) M :=
  begin
    unfold univ_close_core,
    cases (p.symb_arity k) with bm,
    { intro _, apply univ_close_core_of_fam_fav },
    { cases bm with b m, cases b;
      intro _; apply univ_close_core_of_fam_fav }
  end

def univ_close (α : Type) [h : inhabited α] (p : form) : Prop :=
univ_close_core p p.fresh_sdx (model.default α)

lemma univ_close_of_fam_fav [h : inhabited α] {p : form} :
  p.fam_fav α → univ_close α p :=
λ h1, univ_close_core_of_fam_fav _ h1 _ _
