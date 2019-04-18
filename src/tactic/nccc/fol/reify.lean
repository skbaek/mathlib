import .form .abst

variable {α : Type}

open tactic expr

meta def get_domain_core : expr → tactic expr
| `(¬ %%p)     := get_domain_core p
| `(%%p ∨ %%q) := get_domain_core p <|> get_domain_core q
| `(%%p ∧ %%q) := get_domain_core p <|> get_domain_core q
| `(%%p ↔ %%q) := get_domain_core p <|> get_domain_core q
| (pi _ _ p q) := mcond (is_prop p) (get_domain_core p <|> get_domain_core q) (return p)
| `(@Exists %%t _) := return t
| _ := failed

meta def get_domain : tactic expr := target >>= get_domain_core

meta def symb_arities (dx) : expr → ((list (bool × nat)) × expr)
| x@(pi _ _ tx px)    :=
  if (is_pred_type dx tx || is_func_type dx tx)
  then let (as,y) := symb_arities px in ((is_pred_type dx tx, arity_of tx)::as, y)
  else ([],x)
| x := ([],x)

local notation  `#` := term.var
local notation  `&` := term.fnc
local notation  t1 `^*` t2 := term.app t1 t2

local notation  `⊤*` := form.true
local notation  `⊥*` := form.false
local notation  `⟪` l `⟫` := form.lit l
local notation  p `∧*` q := form.and p q
local notation  p `∨*` q := form.or p q
local notation  `∀*` := form.fa
local notation  `∃*` := form.ex

meta def to_term (k : nat) : expr → tactic term
| (app x1 x2) :=
  do t1 ← to_term x1,
     t2 ← to_term x2,
     return (t1 ^* t2)
| (var m) :=
  if m < k
  then return (term.var m)
  else return (term.fnc (m - k))
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
       return ⟪⟨ff, (m-k), ts⟩⟫
  | _ := fail "Predicate expected (neg)"
  end
| k px :=
  match px.get_app_fn with
  | (var m) :=
    do ts ← monad.mapm (to_term k) px.get_app_args,
       return ⟪⟨tt, (m-k), ts⟩⟫
  | _ := fail "Predicate expected"
  end

meta def reify (dx ix : expr) : tactic unit :=
do gx ← target,
   (as,x) ← return (symb_arities dx gx),
   p ← to_form 0 x,
   px ← to_expr ``(@form.univ_close %%dx %%ix %%`(as) model.default %%`(p)),
   to_expr ``(imp_of_imp (%%px) id) >>= apply,
   skip
