import .model .misc tactic.interactive

universe u 

variable {α : Type u}

local notation f `₀↦` a := assign a f

@[derive has_reflect, derive decidable_eq]
inductive term : Type
| var : nat → term
| app : term → term → term

local notation `#` := term.var
local notation a `&` b := term.app a b

namespace term

def incr_idxs_ge (k : nat) : term → term
| (# m)   := if k ≤ m then # (m + 1) else # m
| (a & b) := a.incr_idxs_ge & b.incr_idxs_ge  

def incr_idxs : term → term := incr_idxs_ge 0

def val (M : model α) : term → value α
| (# k)   := M k
| (a & b) := a.val ∘ list.cons (b.val []).fst

end term 

lemma incr_idxs_app (a b : term) : 
  term.incr_idxs (a & b) = (a.incr_idxs & b.incr_idxs) := 
by simp only [ term.incr_idxs, and_self,
     term.incr_idxs_ge, eq_self_iff_true ]

namespace term

lemma val_assign_incr_idxs (M : model α) (v : value α) :
  ∀ a : term, val (M ₀↦ v) a.incr_idxs = val M a 
| (# k)   := rfl
| (a & b) := 
  by simp only [val, val_assign_incr_idxs a, 
     val_assign_incr_idxs b, incr_idxs_app]

end term

lemma eq_of_var_eq_var {k m : nat} : (# k) = (# m) → k = m :=
by {intro h0, cases h0, refl}

lemma val_incr_idxs_ge {M N : model α} {k : nat}  
  (h0 : ∀ m < k, M m = N m) (h1 : ∀ m ≥ k, M (m + 1) = N m) : 
    ∀ a : term, (a.incr_idxs_ge k).val M = a.val N 
| (# m) := 
  begin
    unfold term.incr_idxs_ge,
    by_cases h2 : k ≤ m,
    { rw if_pos h2, 
      apply h1 _ h2 },
    rw if_neg h2,
    rw not_le at h2,
    apply h0 _ h2
  end
| (a & b) := 
  by simp only [term.incr_idxs_ge, term.val, val_incr_idxs_ge]