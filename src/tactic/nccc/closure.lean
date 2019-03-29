import .tactic

open expr tactic

meta def is_func_type (dx : expr) : expr → bool
| `(%%x → %%y) := (x = dx) && (is_func_type y)
| x            := x = dx

meta def is_pred_type (dx : expr) : expr → bool
| `(%%x → %%y) := (x = dx) && (is_pred_type y)
| x            := x = `(Prop)

meta def get_symb_aux (dx x : expr) : tactic expr :=
do tx ← infer_type x,
   if (is_pred_type dx tx || is_func_type dx tx)
   then return x
   else failed

meta def get_symb (dx : expr) : expr → tactic expr
| `(true)   := failed
| `(false)  := failed
| `(¬ %%px) := get_symb px
| `(%%px ∨ %%qx) := get_symb px <|> get_symb qx
| `(%%px ∧ %%qx) := get_symb px <|> get_symb qx
| (pi _ _ _ px) := get_symb px
| `(Exists %%(expr.lam _ _ _ px)) := get_symb px
| `(Exists %%prx) := get_symb prx
| x@(app x1 x2) :=
       get_symb x1
  <|>  get_symb x2
  <|>  get_symb_aux dx x
| x := get_symb_aux dx x

meta def subst_symb (y : expr) : nat → expr → expr
| k x@(app x1 x2) :=
  if y = x
  then var k
  else app (subst_symb k x1) (subst_symb k x2)
| k (lam n b tx x) := lam n b tx (subst_symb (k+1) x)
| k (pi n b tx x)  := pi n b tx (subst_symb (k+1) x)
| k x := if y = x then var k else x

meta def fresh_idx : expr → nat
| (app x y) := max (fresh_idx x) (fresh_idx y)
| (lam n b tx y) := fresh_idx y - 1
| (pi n b tx y)  := fresh_idx y - 1
| _              := 0

meta def abst_aux (dx : expr) : nat → expr → tactic expr
| k x :=
  commit (get_symb dx x) (return x)
  (λ y, abst_aux (k + 1) (subst_symb y k x))

meta def abst (dx x : expr) : tactic expr :=
let k := fresh_idx x in
abst_aux dx k x
