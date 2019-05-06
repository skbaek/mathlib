import system.io
import tactic.fol.arifix
import tactic.fol.reify
import tactic.fol.leancop.parse
import tactic.fol.leancop.inst

open tactic list

lemma arifix_of_blocked (α : Type) [inhabited α]
  (p : form₂) (m : mat) : foq tt p →
  mat.inst m (normalize p) → blocked m [] = tt →
  arifix (model.default α) p :=
begin
  intros h0 h1 h2,
  apply arifix_of_holds h0,
  apply holds_of_fmev_normalize _ h0,
  apply @fmev_of_fmev_inst _ m _ h1 (λ M, _),
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
