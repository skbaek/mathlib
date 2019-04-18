import .term logic.basic logic.function

universe u

variable {α : Type u}

local notation f `₀↦` a := assign a f
local notation `#` := term.var
local notation a `&` b := term.app a b

@[reducible] def sub : Type := list (nat × term)

namespace sub

open list

@[reducible] def incr_idxs : sub → sub := 
map (prod.map nat.succ (term.incr_idxs))

def get (k : nat) : sub → option term 
| []            := none 
| ((m, a) :: σ) := if k = m then a else get σ 

end sub

lemma get_eq_of_ne {k m : nat} (a : term) (σ : sub) : 
  k ≠ m → sub.get k ((m, a) :: σ) = sub.get k σ :=
by {intro h0, simp only [sub.get, if_neg h0]}

lemma get_zero_incr_idxs :
  ∀ σ : sub, σ.incr_idxs.get 0 = none 
| []            := rfl
| ((m, a) :: σ) :=
  begin
    have h0 : sub.get 0 (sub.incr_idxs ((m, a) :: σ)) = 
              sub.get 0 (sub.incr_idxs σ),
    { apply get_eq_of_ne,
      apply (ne.symm $ nat.succ_ne_zero _) },
    rw h0, apply get_zero_incr_idxs,
  end

lemma get_succ_incr_idxs (k : nat) : 
  ∀ σ : sub, σ.incr_idxs.get (k + 1) = term.incr_idxs <$> (σ.get k)
| []            := rfl
| ((m, a) :: σ) := 
  begin
    by_cases h0 : k = m,
    { have h1 : sub.get (k + 1) (sub.incr_idxs ((m, a) :: σ)) = 
                some a.incr_idxs,
      { simp only [sub.get, sub.incr_idxs, if_true,
          prod.map, list.map, eq_self_iff_true, h0], 
        refl },
     have h2 : term.incr_idxs <$> sub.get k ((m, a) :: σ) = 
               some a.incr_idxs, 
     { simp only [sub.get, sub.incr_idxs, if_true, 
       prod.map, list.map, eq_self_iff_true, h0], refl },
     simp only [h1, h2] },
    have h1 : sub.get (k + 1) (sub.incr_idxs ((m, a) :: σ)) = 
              sub.get (k + 1) (sub.incr_idxs σ), 
    { simp only [sub.get, sub.incr_idxs, if_false, prod.map,
     list.map, eq_self_iff_true, not.imp h0 nat.succ_inj] },
    have h2 : term.incr_idxs <$> sub.get k ((m, a) :: σ) = 
              term.incr_idxs <$> sub.get k σ,
    { simp only [sub.get, sub.incr_idxs, if_false, 
      prod.map,list.map, eq_self_iff_true, h0] },
    simp only [h1, h2, get_succ_incr_idxs σ]
  end

namespace term

def subst (σ : sub) : term → term
| (# k)   := (σ.get k).get_or_else (# k)
| (a & b) := a.subst & b.subst 

lemma subst_eq_of_get_eq_none {σ : sub} {k : nat} :
  σ.get k = none → (# k).subst σ = # k :=
by {intro h1, simp only [h1, option.get_or_else, subst]}

lemma subst_eq_of_get_eq_some {σ : sub} {k : nat} {a : term} :
  σ.get k = some a → (# k).subst σ = a :=
by {intro h1, simp only [h1, option.get_or_else, subst]}

end term

namespace model

def subst (M : model α) (σ : sub) : model α :=
λ k : nat,
match σ.get k with
| none   := M k
| some a := a.val M
end

lemma subst_eq_of_get_eq_none
  (M : model α) {σ : sub} {k : nat} :
  σ.get k = none → M.subst σ k = M k :=
by {intro h1, simp only [h1, model.subst]}

lemma subst_eq_of_get_eq_some
  (M : model α) {σ : sub} {k : nat} {a : term} :
  σ.get k = some a → M.subst σ k = a.val M :=
by {intro h1, simp only [h1, model.subst]}

lemma assign_subst (M : model α) (v : value α) (σ : sub) :
  ((M.subst σ) ₀↦ v) = (subst (M ₀↦ v) σ.incr_idxs) := 
begin
  rw function.funext_iff, 
  intro k, cases k, 
  { have h0 := get_zero_incr_idxs σ,
    simp only [subst, h0], refl }, 
  have h0 := get_succ_incr_idxs k σ,
  cases h1 : sub.get k σ with a,
  { rw h1 at h0, 
    have h2 : (subst M σ ₀↦v) k.succ = M k,
    { simp only [assign, model.subst_eq_of_get_eq_none _ h1] },
    have h3 : subst (M ₀↦v) (sub.incr_idxs σ) k.succ = M k,
    { simp only [assign, model.subst_eq_of_get_eq_none _ h0] },
    simp only [h2, h3] },
  rw h1 at h0, 
  have h2 : (subst M σ ₀↦v) k.succ = a.val M,
  { simp only [assign, model.subst_eq_of_get_eq_some _ h1] },
  have h3 : subst (M ₀↦v) (sub.incr_idxs σ) k.succ = a.val M,
  { simp only [assign, subst_eq_of_get_eq_some _ h0,
    term.val_assign_incr_idxs] },
  simp only [h2, h3] 
end

end model

lemma val_subst (M : model α) (σ : sub) :
  ∀ a : term, term.val M (a.subst σ) = term.val (M.subst σ) a
| (# k) :=
  begin
    rw function.funext_iff, intro as,
    cases h1 : σ.get k with s,
    { simp only [term.val, term.subst_eq_of_get_eq_none h1,
        model.subst_eq_of_get_eq_none M h1] },
    simp only [term.val, term.subst_eq_of_get_eq_some h1,
      model.subst_eq_of_get_eq_some M h1],
  end
| (a & b) :=
  begin
    rw function.funext_iff, intro as,
    have h1 := val_subst a,
    have h2 := val_subst b,
    simp only [term.val, term.subst, h1, h2],
  end