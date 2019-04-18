import .fov 

universe u 

variables {α β : Type u}

open nat

local notation f `₀↦` a := assign a f
local notation `#` := term.var
local notation a `&` b := term.app a b

postfix  `ₑ` : 1000 := evaluate 
postfix  `ᵈ` : 1000 := denote
local infix `⬝` := value.app

local notation `⟪` b `,` a `⟫` := form.lit b a
local notation p `∨*` q        := form.bin tt p q
local notation p `∧*` q        := form.bin ff p q
local notation `∃*`            := form.qua tt 
local notation `∀*`            := form.qua ff

def pull_fa_left_eqv [inhabited α] (b : bool) (p q : form) : 
  ∀* (form.bin b p q.incr_idxs) <==α==> form.bin b (∀* p) q := 
begin
  intro M, 
  have v : value α := (default α)ₑ,
  constructor; intro h0; cases b,
  { constructor,
    { intro w, exact (h0 w).left },
    apply (holds_assign_incr_idxs _).elim_left (h0 v).right },
  { cases classical.em ((M ₀↦ v) ⊨ q.incr_idxs) with h2 h2, 
    { rw holds_assign_incr_idxs at h2,
      right, exact h2 },
    left, intro w, 
    cases (h0 w) with h3 h3, 
    { exact h3 },
    rw holds_assign_incr_idxs at h2,
    rw holds_assign_incr_idxs at h3,
    cases (h2 h3) },
  { intro w, 
    refine ⟨h0.left _, _⟩,
    rw holds_assign_incr_idxs, 
    exact h0.right },
  { intro w, 
    cases classical.em ((M ₀↦ w) ⊨ q.incr_idxs) with h1 h1, 
    { right, exact h1 },
    left, cases h0 with h2 h2,
    { apply h2 },
    rw holds_assign_incr_idxs at h1,
    cases (h1 h2) }
end

def pull_ex_left_eqv [inhabited α] (b : bool) (p q : form) : 
  ∃* (form.bin b p q.incr_idxs) <==α==> form.bin b (∃* p) q := 
by { rw ← neg_eqv_neg, 
     simp only [form.neg, neg_incr_idxs, 
     bnot, pull_fa_left_eqv] } 


def pull_left_eqv [inhabited α] (ae ao : bool) (p q : form) : 
  form.qua ae (form.bin ao p q.incr_idxs) <==α==> 
  form.bin ao (form.qua ae p) q := 
by {cases ae, apply pull_fa_left_eqv, apply pull_ex_left_eqv }

-- def pull_right_eqv [inhabited α] (ae ao : bool) (p q : form) : 
--   form.qua ae (form.bin ao p.incr_idxs q) <==α==> 
--   form.bin ao p (form.qua ae q) := 
-- begin
--   have h0 : ( form.qua ae (form.bin ao (form.incr_idxs p) q) <==α==>
--               form.qua ae (form.bin ao q (form.incr_idxs p)) ) :=
--   qua_eqv_qua (bin_comm _ _ _),
--   intro M,
--   simp only [ h0 M, pull_left_eqv ae ao q p M,
--     bin_comm ao p (form.qua ae q) M ] 
-- end

@[reducible] def form.size_of_ordered : 
  (Σ' (b : bool), (Σ' (a : form), form)) → nat 
| ⟨tt, p, q⟩ := p.size_of + q.size_of + 1
| ⟨ff, p, q⟩ := p.size_of + q.size_of 

meta def form.show_size_lt : tactic unit :=
`[ simp only [form.size_of_ordered, form.size_of,
   nat.lt_succ_self, add_comm, add_lt_add_iff_left, 
   add_left_comm, form.size_of_incr_idxs ] ]

/- Pull quantifiers over a binary connective. `ae` specifies
   the type of quantifier to be pulled, and `ao` specifies 
   the binary connective. -/
def pull (ae : option bool) (ao : bool) : bool → form → form → form
| tt (form.qua b p) q := 
  have form.size_of_ordered ⟨ff, ⟨q, form.qua b p⟩⟩ <
       form.size_of_ordered ⟨tt, ⟨form.qua b p, q⟩⟩,
  by form.show_size_lt,
  if ae = some (bnot b) 
  then pull ff q (form.qua b p)
  else form.qua b (pull tt p q.incr_idxs)
| ff (form.qua b p) q := 
  have form.size_of_ordered ⟨ff, ⟨p, form.incr_idxs q⟩⟩ <
       form.size_of_ordered ⟨ff, ⟨form.qua b p, q⟩⟩,
  by form.show_size_lt,
  if ae = some (bnot b) 
  then form.bin ao (form.qua b p) q
  else form.qua b (pull ff p q.incr_idxs)
| tt p q := 
  have form.size_of_ordered ⟨ff, ⟨q, p⟩⟩ <
       form.size_of_ordered ⟨tt, ⟨p, q⟩⟩,
  by form.show_size_lt,
  pull ff q p
| ff p q := form.bin ao p q
using_well_founded 
  {rel_tac := λ _ _, `[exact ⟨_, measure_wf form.size_of_ordered⟩]}

lemma fov_pull (ae : option bool) (ao : bool) :
  ∀ (ls : bool) {p q : form} {k : nat}, 
  fov k p → fov k q → 
  fov k (pull ae ao ls p q) 
| tt ⟪m, a⟫           q := 
  have 0 < form.size_of ⟪m,a⟫ := zero_lt_one,
  by { intros k h0 h1,
       unfold pull,
       apply fov_pull ff h1 h0 } 
| ff ⟪m, a⟫           q := 
  by { intros k h0 h1,
       unfold pull, 
       refine ⟨h0, h1⟩ }
| tt (form.bin b p q) r := 
  have form.size_of_ordered ⟨ff, ⟨r, form.bin b p q⟩⟩ <
       form.size_of_ordered ⟨tt, ⟨form.bin b p q, r⟩⟩,
  by form.show_size_lt,
  by { intros k h0 h1, 
       unfold pull,
       apply fov_pull ff h1 h0 } 
| ff (form.bin b p q) r := 
  by { intros k h0 h1,
       unfold pull, 
       refine ⟨h0, h1⟩ }
| tt (form.qua b p)   q := 
  have form.size_of_ordered ⟨ff, ⟨q, form.qua b p⟩⟩ < 
       form.size_of_ordered ⟨tt, ⟨form.qua b p, q⟩⟩,
  by form.show_size_lt,
  begin
    intros k h0 h1,
    unfold pull,
    apply ite_cases,
    { apply fov_pull ff h1 h0 },
    apply fov_pull, 
    { apply h0 },
    apply fov_incr_idxs h1
  end
| ff (form.qua b p)   q := 
  have form.size_of_ordered ⟨ff, ⟨p, form.incr_idxs q⟩⟩ < 
       form.size_of_ordered ⟨ff, ⟨form.qua b p, q⟩⟩,
  by form.show_size_lt,
  begin
    intros k h0 h1, 
    unfold pull,
    apply ite_cases,
    { refine ⟨h0, h1⟩ },
    apply fov_pull, 
    { apply h0 },
    apply fov_incr_idxs h1
  end
using_well_founded 
  { rel_tac := λ _ _, `[exact ⟨_, measure_wf form.size_of_ordered⟩] }

def pull_eqv [inhabited α] (ae : option bool) (ao : bool) :
  ∀ ls : bool, ∀ p q : form, 
  pull ae ao ls p q <==α==> form.bin ao p q 
| tt ⟪k, a⟫           q := 
  have 0 < form.size_of ⟪k,a⟫ := zero_lt_succ _,
  by { apply eqv_trans _ (bin_comm _ _ _),
       unfold pull,
       apply pull_eqv }
| ff ⟪k, a⟫           q := by {unfold pull, apply eqv_refl}
| tt (form.bin b p q) r := 
  have form.size_of_ordered ⟨ff, ⟨r, form.bin b p q⟩⟩ < 
       form.size_of_ordered ⟨tt, ⟨form.bin b p q, r⟩⟩,
  by form.show_size_lt,
  by { apply eqv_trans _ (bin_comm _ _ _),
       unfold pull,
       apply pull_eqv }
| ff (form.bin b p q) r := by {unfold pull, apply eqv_refl}
| tt (form.qua b p) q := 
  have  form.size_of_ordered ⟨ff, ⟨q, form.qua b p⟩⟩ < 
        form.size_of_ordered ⟨tt, ⟨form.qua b p, q⟩⟩,
  by form.show_size_lt,
  begin
    unfold pull,
    apply @ite_cases _ (λ x, x <==α==>form.bin ao (form.qua b p) q),
    { apply eqv_trans _ (bin_comm _ _ _),
      apply pull_eqv },
    apply eqv_trans 
      (qua_eqv_qua $ pull_eqv _ p _) 
      (pull_left_eqv _ _ _ _)
  end
| ff (form.qua b p) q := 
  have  form.size_of_ordered ⟨ff, ⟨p, form.incr_idxs q⟩⟩ < 
        form.size_of_ordered ⟨ff, ⟨form.qua b p, q⟩⟩,
  by form.show_size_lt,
  begin
    unfold pull,
    apply @ite_cases _ (λ x, x <==α==>form.bin ao (form.qua b p) q),
    { apply eqv_refl },
    apply eqv_trans 
      (qua_eqv_qua $ pull_eqv _ p _) 
      (pull_left_eqv _ _ _ _),
  end
using_well_founded 
  {rel_tac := λ _ _, `[exact ⟨_, measure_wf form.size_of_ordered⟩]}
