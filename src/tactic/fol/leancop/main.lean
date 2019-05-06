import system.io
import tactic.fol.arifix
import tactic.fol.reify
import tactic.fol.leancop.parse
import tactic.fol.leancop.inst

/- `leancop` uses proof output from
    leanCoP to discharge first-order goals. -/

universe u

variable {α : Type u}

open tactic list

def mat.size : mat → nat
| []       := 0
| (c :: m) := mat.size m + c.length + 1

def blocked : mat → cla → bool
| []              := λ _, ff
| ([] :: _)       := λ _, tt
| ((l :: c) :: m) := λ p,
  have mat.size (c :: m) < mat.size ((l :: c) :: m) := nat.lt_succ_self _,
  have mat.size m < mat.size ((l :: c) :: m) :=
  nat.lt_of_le_of_lt (nat.le_add_right _ c.length)
    (nat.lt_trans (nat.lt_succ_self _) (nat.lt_succ_self _)),
  if blocked (c :: m) p
  then if l.neg ∈ p
       then tt
       else blocked m (l :: p)
  else false
using_well_founded {
  dec_tac := tactic.assumption,
  rel_tac := λ _ _, `[exact ⟨measure mat.size, measure_wf mat.size⟩]
}

lemma holds_of_blocked (M : model α) (v : vas α) :
  ∀ m : mat, ∀ p : cla, (∀ l ∈ p, ¬ lit.holds M v l) →
  blocked m p = tt → m.holds M v
| []              _ _  h1 := by cases h1
| ([] :: _)       _ _  _  := ⟨_, or.inl rfl, list.ball_nil _⟩
| ((l :: c) :: m) p h0 h2 :=
  begin
    cases h3 : (blocked (c :: m) p),
    { simpa only [blocked, h3, bool.coe_sort_ff, if_false] using h2 },
    by_cases h4 : l.neg ∈ p,
    { have h5 : mat.holds M v (c :: m),
      { apply holds_of_blocked _ _ h0, rw h3,  },
      rcases h5 with ⟨d, h5 | h5, h6⟩,
      { refine ⟨_, or.inl rfl, λ x h7, _⟩,
        cases h7 with h7 h7,
        { apply classical.by_contradiction,
          have h8 := h0 _ h4,
          simpa only [lit.holds_neg, h7] using h8 },
        apply h6, rwa ← h5 at h7 },
        refine ⟨d, or.inr h5, h6⟩ },
    have h5 : blocked m (l :: p) = tt,
    { simpa only [blocked, h3, h4, bool.to_bool_false,
      if_true, bool.coe_sort_tt, if_false] using h2 },
    cases (classical.em (l.holds M v)) with h6 h6,
    { rcases holds_of_blocked (c :: m) p h0 h3 with ⟨d, h7 | h7, h8⟩,
      { refine ⟨_, or.inl rfl, _⟩, rw ← h7,
        apply (ball_cons (lit.holds M v) l d).elim_right ⟨h6, h8⟩ },
      refine ⟨d, or.inr h7, h8⟩ },
    have h7 : ∀ x ∈ (l :: p), ¬ lit.holds M v x,
    { apply (ball_cons (λ y, ¬ lit.holds M v y) l p).elim_right ⟨h6, h0⟩ },
    have h8 := holds_of_blocked m (l :: p) h7 h5,
    apply (bex_cons _ _ _).elim_right (or.inr h8),
  end

lemma valid_of_blocked {m : mat} :
  blocked m [] = tt → m.valid α :=
by { intros h0 M v,
     apply holds_of_blocked _ _ _ _ _ h0,
     apply @ball_nil _ (λ x, ¬ lit.holds M v x) }
lemma arifix_of_blocked (α : Type) [inhabited α]
  (p : form₂) (m : mat) : foq tt p →
  mat.inst m (normalize p) → blocked m [] = tt →
  arifix (model.default α) p :=
begin
  intros h0 h1 h2,
  apply arifix_of_holds h0,
  apply holds_of_fam_exv_normalize _ h0,
  apply @fam_exv_of_fam_exv_inst _ m _ h1 (λ M, _),
  refine ⟨vas.default α, _⟩,
  apply @valid_of_blocked α _ h2 M
end

meta def get_ext (s : string) : tactic string :=
unsafe_run_io $ io.cmd {
  cmd  := "swipl",
  args := ["leancop.pl", s],
  /- Change this parameter to location of leancop.pl-/
  cwd  := "/home/sk/Projects/mathlib/src/tactic/fol/leancop"
}

meta def prove_arifix (dx ix : expr) (p : form₂) : tactic expr :=
do s ← get_ext (mat.write $ normalize p),
   let ts : list string := lex s,
   m ← mat.parse ts,
   to_expr ``(@arifix_of_blocked %%dx %%ix %%`(p) %%`(m)
     dec_trivial (of_is_shown trivial) (eq.refl tt))

meta def leancop : tactic unit :=
do (dx, ix, p) ← reify,
   y ← prove_arifix dx ix p,
   apply y, skip

/- Some xamples from tests.finish1 -/

variables (X : Type) [inhabited X] (t s : X)
  (a b c : Prop) (p q : X → Prop) (r : X → X → Prop)

example : (a ↔ b) → (a ∧ b → c) → (¬ a ∧ ¬ b → c) → c := by leancop
example : (∃ x : X, p x → a) ↔ (∀ x, p x) → a := by leancop
example : (∃ x, ∀ y, r x y) → ∀ y, ∃ x, r x y := by leancop
example : (∀ x, p x → q x → false) → (p t) → (p s) → (q s) → false := by leancop
