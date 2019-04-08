import .closure .logic .form .term

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


local notation  `⅋` := term.fnc
local notation  t `&` s := term.tpp t s
local notation  t `#` k := term.vpp t k

local notation  `⊤*` := form.true
local notation  `⊥*` := form.false
local notation  `⟪` l `⟫` := form.lit l
local notation  p `∧*` q := form.and p q
local notation  p `∨*` q := form.or p q
local notation  `∀*` := form.fa
local notation  `∃*` := form.ex

meta def to_term (k : nat) : expr → tactic term
| (app x (var m)) :=
  if m < k
  then do t ← to_term x,
          return (t # m)
  else failed
| (app x y) :=
  do t ← to_term x,
     s ← to_term y,
     return (t & s)
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
  match px.get_app_fn with
  | (var m) :=
    do ts ← monad.mapm (to_term k) px.get_app_args,
       return ⟪⟨ff, m-k, ts⟩⟫
  | _ := fail "Predicate expected"
  end
| k px :=
  match px.get_app_fn with
  | (var m) :=
    do trace 0,
       trace px.get_app_args,
       ts ← monad.mapm (to_term k) px.get_app_args,
       trace 0,
       return ⟪⟨tt, m-k, ts⟩⟫
  | _ := fail "Predicate expected"
  end

axiom any (P : Prop) : P

/- Return the expr of (π : form.valid ⟦dx⟧ p). -/
meta def prove_valid (dx : expr) (p : form) : tactic expr :=
return `(any (form.valid %%dx %%`(p)))

/- Return the expr of (π : form.valid ⟦dx⟧ p). -/
meta def prove_univ_close (dx ix : expr) (p : form) : tactic expr :=
do x ← prove_valid dx p,
   return `(@univ_close_of_valid %%dx %%ix %%`(p) %%x)

meta def main : tactic unit :=
do desugar,
   dx ← get_domain,
   ihx ← to_expr ``(inhabited),
   ix ← mk_instance (app ihx dx),
   x ← target >>= abst dx,
   trace x,
   p ← to_form 0 x,
   y ← prove_univ_close dx ix p,
   apply y,
   skip

example (P : nat → Prop) : ∀ x : nat, ∃ y : nat, P x ∧ ¬ P y :=
begin
  main,
end

#exit
@[reducible] def foo : form :=
    (∀* (∃* (⟪⟨tt,0,[# 1]⟩⟫∧*⟪⟨tt,0,[# 0]⟩⟫)))

example : false :=
begin
  have h : univ_close nat foo := sorry,
  simp [univ_close, fresh_sdx] at h,
end
run_cmd infer_type `(foo) >>= trace
#exit

#exit

#exit
example (f g : nat → nat) : ¬ ∀ x : nat, ∃ y : nat, (g (x + 2) ≤ g (y + 2)) :=
begin
  main,
end


   #exit
   rev dx,
   desugar,
   abst dx,
   --trace_goal,
   reify dx ix,
   to_expr ``(form.univ_close_of_valid _) >>= apply,
   skip


#exit
meta def main : tactic unit :=
do dx ← get_domain,
   ihx ← to_expr ``(inhabited),
   ix ← mk_instance (app ihx dx),
   rev dx,
   desugar,
   abst dx,
   --trace_goal,
   reify dx ix,
   to_expr ``(form.univ_close_of_valid _) >>= apply,
   skip

meta def trace_valid_goal :=
do `(form.valid _ %%x) ← target,
   eval_expr form x >>= trace



#exit
example (f g : nat → nat) : ∃ y : nat, (f y < y ∨ y ≤ g (y + 2)) :=
by do
  main,
  `(form.valid _ %%x) ← target,
  eval_expr form x >>= trace,

  skip
