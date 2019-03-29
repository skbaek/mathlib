import .model .misc .nat .list

variable {α : Type}

open tactic

@[derive has_reflect]
inductive term : Type
| var : nat → term
| fnc : nat → term
| app : term → term → term

local notation  `#` := term.var
local notation  `&` := term.fnc
local notation  t1 `^*` t2 := term.app t1 t2

namespace term

def repr : term → string
| (# k) := "X" ++ k.to_subs
| (& k) := "C" ++ k.to_subs
| (t ^* s) := "(" ++ t.repr ++ " " ++ s.repr ++ ")"

meta instance has_repr : has_repr term := ⟨repr⟩

def mk_app (t : term) (ts : list term) : term :=
list.foldl app t ts


@[simp] def fresh_idx : term → nat
| (# m)      := m + 1
| (& _)      := 0
| (t1 ^* t2) := max t1.fresh_idx t2.fresh_idx

def is_fresh_idx (k : nat) (t : term) : Prop := t.fresh_idx ≤ k

--instance dec_max_idx_lt : ∀ k t, decidable (max_idx_lt k t)
--| := by apply_instance

--begin
--  intros k t, induction t;
--  squeeze_simp, repeat {apply_instance},
--  apply @and.decidable _ _ _ _; assumption
--end

@[simp] def val_core (M : model α) (v : nat → α) : term → list α → α
| (# k)      _  := v k
| (& k)      as := M.funcs k as
| (t1 ^* t2) as := t1.val_core (t2.val_core []::as)

def val (M v t) : α := val_core M v t []

def symb_arity_core (k : nat) : nat → term → option (bool × nat)
| m (# _)    := none
| m (& n)    := if k = n then some (ff,m) else none
| m (t ^* s) :=
  symb_arity_core (m+1) t <|> symb_arity_core 0 s

def symb_arity (k : nat) (t : term) : option (bool × nat) :=
symb_arity_core k 0 t

def fresh_sdx : term → nat
| (# _)    := 0
| (& n)    := n + 1
| (t ^* s) := max (fresh_sdx t) (fresh_sdx s)

def free_vars (k : nat) : term → list nat
| (# m)      := if k ≤ m then [m] else []
| (& _)      := []
| (t ^* s) := (free_vars t) ∪ (free_vars s)

def subst (m s) : term → term
| (# k)    := if k = m then s else (# k)
| (& k)    := (& k)
| (t ^* u) := (subst t) ^* (subst u)

def incr_vdx : term → term
| (# k)      := # (k+1)
| (& k)      := (& k)
| (t ^* s) := t.incr_vdx ^* s.incr_vdx

#exit

lemma val_core_eq_val_core_of_max_idx_lt :
  ∀ M (v w : nat → α) t as k, is_fresh_idx k t →
  (∀ m < k, v m = w m) → (val_core M v t as) = (val_core M w t as)
| M v w (# k) as m h1 h2 :=
  begin
    simp only [val_core], apply h2,
    apply nat.lt_of_succ_le h1
  end


  #exit
| M v w (& k) as m h1 h2 := by squeeze_simp
| M v w (t1 ^* t2) as m h1 h2 :=
  begin
    squeeze_simp, cases h1,
    repeat {rw (val_core_eq_val_core_of_max_idx_lt M v w _ _ m)};
    assumption
  end

lemma val_eq_val_of_max_idx_lt (M) (v w : nat → α) (t k) :
  max_idx_lt k t → (∀ m < k, v m = w m) → (val M v t) = (val M w t) :=
val_core_eq_val_core_of_max_idx_lt M v w t [] k


def fresh_func_idx : term → nat
| (# k)      := 0
| (& k)      := k + 1
| (t1 ^* t2) := max (fresh_func_idx t1) (fresh_func_idx t2)



end term
