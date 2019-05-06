import .correct .search .arifix system.io

variables {α : Type} [inhabited α]

open tactic

axiom any (p : Prop) : p

meta def rulex.eval : rulex → tactic rule
| (rulex.red k)      := return (rule.red k)
| (rulex.ext j i σx) :=
  do σ ← σx.eval, return (rule.ext j i σ)

meta def rulex.ground : rulex → tactic rulex
| (rulex.red k)      := return (rulex.red k)
| (rulex.ext j i σx) :=
  do σx' ← subx.ground σx, return (rulex.ext j i σx')

meta def get_ext (s : string) : tactic string :=
unsafe_run_io $ io.cmd {
  cmd  := "swipl",
  args := ["leancop.pl", s],
  /- Change this parameter to location of leancop.pl-/
  cwd  := "/home/sk/Projects/mathlib/src/tactic/fol"
}

-- meta def foo : tactic unit := echo "Hello there" >>= trace
-- run_cmd foo

/- Return ⌜π : p.holds (model.default ⟦dx⟧)⌝ . -/
meta def prove_holds (dx ix : expr) (p : form₂) : tactic expr :=
do trace (mat.write $ normalize p),
   get_ext (mat.write $ normalize p) >>= trace,
   failed
-- do rxs ← derive (normalize p),
--   rxs' ← monad.mapm rulex.ground rxs,
--   rs ← monad.mapm rulex.eval rxs',
--   to_expr ``(@holds_of_fam_exv_normalize %%dx %%ix %%`(p) dec_trivial
--     (@check_imp %%dx %%ix (normalize %%`(p)) %%`(rs) trivial))

/- Return ⌜π : arifix (model.default ⟦dx⟧) p⌝ . -/
meta def prove_arifix (dx ix : expr) (p : form₂) : tactic expr :=
do πx ← prove_holds dx ix p,
   to_expr ``(@arifix_of_holds %%dx %%ix _ %%`(p) dec_trivial %%πx)
