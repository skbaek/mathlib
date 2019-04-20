import .nat .model

universe u

variable {α : Type u}

@[derive has_reflect, derive decidable_eq]
inductive term : Type
| sym : nat  → term
| app : term → term → term
| vpp : term → nat  → term

local notation `&`     := term.sym
local notation a `&` b := term.app a b
local notation a `#` k := term.vpp a k

namespace term

def repr_core : bool → term → string
| s (term.sym k)   := (if s then "P" else "F") ++ k.to_subs
| s (term.app a b) := "(" ++ a.repr_core s ++ " " ++ b.repr_core ff ++ ")"
| s (term.vpp a k) := "(" ++ a.repr_core s ++ " " ++ "X" ++ k.to_subs ++ ")"

def repr : term → string := repr_core tt

def vdxs : term → list nat
| (term.sym _)   := []
| (term.app a b) := a.vdxs ∪ b.vdxs
| (term.vpp a m) := a.vdxs.insert m

def val (M : model α) (v : nat → α) : term → value α
| (term.sym k)   := M k
| (term.app a b) := a.val ∘ list.cons (b.val []).fst
| (term.vpp a k) := a.val ∘ list.cons (v k)

end term

def sub : Type := list (nat × term)

def sub.get (σ : sub) (k : nat) : option term :=
prod.snd <$> (list.find (eq k ∘ prod.fst)) σ

namespace vas

def subst (M : model α) (v : vas α) (σ : sub) (k : nat) : α :=
match σ.get k with
| none   := v k
| some t := (t.val M v []).fst
end

lemma subst_eq_of_eq_none (M : model α)
  (v : vas α) {σ : sub} {k : nat} :
σ.get k = none → v.subst M σ k = v k :=
by { intro h1, simp only [h1, subst] }

lemma subst_eq_of_eq_some (M : model α)
  (v : vas α) {σ : sub} {k : nat} {t : term} :
σ.get k = some t → v.subst M σ k = (t.val M v []).fst :=
by { intro h1, simp only [h1, subst] }

end vas

namespace term

def subst (σ : sub) : term → term
| (& k)   := & k
| (t & s) := subst t & subst s
| (t # k) :=
  match σ.get k with
  | none   := subst t # k
  | some s := subst t & s
  end

lemma subst_eq_of_eq_none {σ : sub} (t : term) {k : nat} :
σ.get k = none → subst σ (t # k) = subst σ t # k :=
by { intro h, simp only [h, subst, eq_self_iff_true, and_self] }

lemma subst_eq_of_eq_some {σ : sub} (t s : term) {k : nat} :
σ.get k = some s → subst σ (t # k) = (subst σ t & s) :=
by { intro h, simp only [h, subst, eq_self_iff_true, and_self] }

lemma val_subst (M : model α) (v : vas α) (σ : sub) :
  ∀ t : term, (t.subst σ).val M v = t.val M (v.subst M σ)
| (& k)   := rfl
| (t & s) := by simp only [val, subst, val_subst]
| (t # k) := --by simp only [val, subst, val_subst]
  begin
    cases h1 : σ.get k with s,
    simp only [subst_eq_of_eq_none t h1,
      vas.subst_eq_of_eq_none M v h1,
      val_subst, val],
    simp only [subst_eq_of_eq_some t s h1,
      vas.subst_eq_of_eq_some M v h1,
      val_subst, val]
  end

end term
