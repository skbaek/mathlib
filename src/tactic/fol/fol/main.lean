import .closure .prove

run_cmd mk_simp_attr `sugar
attribute [sugar]
  -- logical constants
  or_false false_or
  and_true true_and
  -- implication elimination
  classical.imp_iff_not_or
  classical.iff_iff_not_or_and_or_not
  -- NNF
  classical.not_not
  not_exists
  not_or_distrib
  classical.not_and_distrib
  classical.not_forall

meta def desugar := `[try {simp only with sugar}]

open expr tactic

meta def get_domain_core : expr → tactic expr
| `(¬ %%p)     := get_domain_core p
| `(%%p ∨ %%q) := get_domain_core p <|> get_domain_core q
| `(%%p ∧ %%q) := get_domain_core p <|> get_domain_core q
| `(%%p ↔ %%q) := get_domain_core p <|> get_domain_core q
| (pi _ _ p q) := mcond (is_prop p) (get_domain_core p <|> get_domain_core q) (return p)
| `(@Exists %%t _) := return t
| _ := failed

meta def get_domain : tactic expr :=
target >>= get_domain_core


local notation  `⅋` := atom.sym
local notation  t `&` s := atom.app t s
local notation  t `#` k := atom.vpp t k

local notation  `⊤*` := form.true
local notation  `⊥*` := form.false
local notation  `⟪` l `⟫` := form.lit l
local notation  p `∧*` q := form.and p q
local notation  p `∨*` q := form.or p q
local notation  `∀*` := form.fa
local notation  `∃*` := form.ex

meta def to_atom (k : nat) : expr → tactic atom
| (app x (var m)) :=
  if m < k
  then do a ← to_atom x,
          return (a # m)
  else failed
| (app x y) :=
  do a ← to_atom x,
     b ← to_atom y,
     return (a & b)
| (var m) :=
  if m < k
  then failed
  else return (⅋ (m - k))
| _ := failed

meta def to_form : nat → expr → tactic form
| k `(true)   := return ⊤*
| k `(false)  := return ⊥*
| k `(%%px ∨ %%qx) :=
  do φ ← to_form k px,
     χ ← to_form k qx,
     return (φ ∨* χ)
| k `(%%px ∧ %%qx) :=
  do φ ← to_form k px,
     χ ← to_form k qx,
     return (φ ∧* χ)
| k (pi _ _ _ px) :=
  do φ ← to_form (k+1) px, return (∀* φ)
| k `(Exists %%(expr.lam _ _ _ px)) :=
  do φ ← to_form (k+1) px, return (∃* φ)
| k `(Exists %%prx) :=
  do φ ← to_form (k+1) (app (prx.lift_vars 0 1) (var 0)),
     return (∃* φ)
| k `(¬ %%px) :=
  do a ← to_atom k px,
     return ⟪(ff, a)⟫
| k px :=
  do a ← to_atom k px,
     return ⟪(tt, a)⟫

meta def main : tactic unit :=
do desugar,
   dx ← get_domain,
   ihx ← to_expr ``(inhabited),
   ix ← mk_instance (app ihx dx),
   x ← target >>= abst dx,
   p ← to_form 0 x,
   y ← prove_univ_close dx ix p,
   apply y,
   skip

example (P : nat → Prop) : ∀ x : nat, ∃ y : nat, P x ∨ ¬ P y :=
begin
  main,
end

#exit

example (f g : nat → nat) : ¬ ∀ x : nat, ∃ y : nat, (g (x + 2) ≤ g (y + 2)) :=
begin
  main,
end

example (f g : nat → nat) : ∃ y : nat, (f y < y ∨ y ≤ g (y + 2)) :=
by do
  main,
  `(form.fam_fav _ %%x) ← target,
  eval_expr form x >>= trace,

  skip
