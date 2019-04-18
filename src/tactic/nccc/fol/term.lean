import .model .misc .nat .list

variable {α : Type}

open tactic

@[derive has_reflect, derive decidable_eq]
inductive atom : Type
| v : nat → atom
| s : nat → atom

namespace atom


end atom


#exit


@[derive has_reflect, derive decidable_eq]
inductive mole : Type
| TT : nat  → atom → mole
| TB : nat  → mole → mole
| BT : mole → atom → mole
| BB : mole → mole → mole

@[derive has_reflect, derive decidable_eq]
inductive term : Type
| a : atom → term
| m : mole → term



#exit
/- variable index operations  -/

def vdxs : term → list nat
| (⅋ k)   := []
| (t & s) := vdxs t ∪ vdxs s
| (t # k) := (vdxs t).insert k

def free_vdxs (k : nat) : term → list nat
| (⅋ _)   := []
| (t & s) := (free_vdxs t) ∪ (free_vdxs s)
| (t # m) := if k ≤ m then t.free_vdxs.insert m else t.free_vdxs


def fresh_vdx : term → nat
| (⅋ _)   := 0
| (t & s) := max t.fresh_vdx s.fresh_vdx
| (t # m) := max t.fresh_vdx (m + 1)

def is_fresh_vdx (k : nat) (t : term) : Prop := t.fresh_vdx ≤ k
#exit
| s : nat → atom

#exit


@[derive has_reflect, derive decidable_eq]
inductive term : Type
| fnc : nat → term
| tpp : term → term → term
| vpp : term → nat → term

local notation `⅋` k   := term.fnc k
local notation t `&` s := term.tpp t s
local notation t `#` k := term.vpp t k

namespace term

def repr : term → string
| (⅋ k) := "C" ++ k.to_subs
| (t & s) := "(" ++ t.repr ++ " " ++ s.repr ++ ")"
| (t # k) := "(" ++ t.repr ++ " " ++ "X" ++ k.to_subs ++ ")"

instance has_repr : has_repr term := ⟨repr⟩

meta instance has_to_format : has_to_format term := ⟨λ x, repr x⟩

-- def mk_app (t : term) (ts : list term) : term :=
-- list.foldl app t ts






--
/- symbol index operations  -/

def fresh_sdx : term → nat
| (⅋ n)   := n + 1
| (t & s) := max (fresh_sdx t) (fresh_sdx s)
| (t # _) := fresh_sdx t

end term


/- substitution -/

@[reducible] def sub : Type := list (nat × term)

def sub.app (σ : sub) (k : nat) : option term :=
prod.snd <$> (list.find (eq k ∘ prod.fst)) σ

namespace term

def subst (σ : sub) : term → term
| (⅋ k)   := ⅋ k
| (t & s) := subst t & subst s
| (t # k) :=
  match σ.app k with
  | none   := subst t # k
  | some s := subst t & s
  end

lemma subst_eq_of_eq_none {σ : sub} (t : term) {k : nat} :
σ.app k = none → subst σ (t # k) = subst σ t # k :=
by { intro h, simp only [h, subst, eq_self_iff_true, and_self] }

lemma subst_eq_of_eq_some {σ : sub} (t s : term) {k : nat} :
σ.app k = some s → subst σ (t # k) = (subst σ t & s) :=
by { intro h, simp only [h, subst, eq_self_iff_true, and_self] }

/- evaluation -/

@[simp] def value_core (M : model α) (v : nat → α) : term → list α → α
| (⅋ k)   as := M.funs k as
| (t & s) as := t.value_core (s.value_core [] :: as)
| (t # k) as := t.value_core (v k :: as)

def value (M v t) : α := value_core M v t []

end term

def val.subst (M : model α) (v : nat → α) (σ : sub) (k : nat) : α :=
match σ.app k with
| none   := v k
| some t := t.value M v
end

lemma val.subst_eq_of_eq_none (M : model α)
  (v : nat → α) {σ : sub} {k : nat} :
σ.app k = none → val.subst M v σ k = v k :=
by { intro h1, simp only [h1, val.subst] }

lemma val.subst_eq_of_eq_some (M : model α)
  (v : nat → α) {σ : sub} {k : nat} {t : term} :
σ.app k = some t → val.subst M v σ k = t.value M v :=
by { intro h1, simp only [h1, val.subst] }

namespace term

lemma value_core_subst (M : model α) (v : nat → α) (σ : sub) :
  ∀ t : term, ∀ as : list α,
  value_core M v (t.subst σ) as =
  value_core M (val.subst M v σ) t as
| (⅋ k) as   := rfl
| (t & s) as :=
  begin
    have h1 := value_core_subst t,
    have h2 := value_core_subst s [],
    simp only [value_core, subst, h1, h2]
  end
| (t # k) as :=
  begin
    cases h1 : σ.app k with s,
    simp only [subst_eq_of_eq_none t h1,
      val.subst_eq_of_eq_none M v h1,
      value_core_subst, value_core],
    simp only [subst_eq_of_eq_some t s h1,
      val.subst_eq_of_eq_some M v h1,
      value_core_subst, value_core, value]
  end

lemma value_subst (M : model α) (v : nat → α) (σ : sub) (t : term) :
  value M v (t.subst σ) = value M (val.subst M v σ) t :=
by apply value_core_subst

lemma value_comp_subst (M : model α) (v : nat → α) (σ : sub) :
  value M v ∘ (subst σ) = value M (val.subst M v σ) :=
function.funext_iff.elim_right (by apply value_subst)

#exit

    simp only [value_core, subst, var.subst, val.subst],
  end


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
