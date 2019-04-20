import .fov

universe u

variables {α β : Type u}

open nat

local notation f `₀↦` a := assign a f
local notation `#` := term₂.var
local notation a `&` b := term₂.app a b

postfix  `ₑ` : 1000 := evaluate
postfix  `ᵈ` : 1000 := denote
local infix `⬝` := value.app

local notation `⟪` b `,` a `⟫` := form₂.lit b a
local notation p `∨*` q        := form₂.bin tt p q
local notation p `∧*` q        := form₂.bin ff p q
local notation `∃*`            := form₂.qua tt
local notation `∀*`            := form₂.qua ff

def pull_fa_left_eqv [inhabited α] (b : bool) (p q : form₂) :
  ∀* (form₂.bin b p q.incr) <==α==> form₂.bin b (∀* p) q :=
begin
  intro M,
  have v : value α := (default α)ₑ,
  constructor; intro h0; cases b,
  { constructor,
    { intro w, exact (h0 w).left },
    apply (holds_assign_incr _).elim_left (h0 v).right },
  { cases classical.em ((M ₀↦ v) ⊨ q.incr) with h2 h2,
    { rw holds_assign_incr at h2,
      right, exact h2 },
    left, intro w,
    cases (h0 w) with h3 h3,
    { exact h3 },
    rw holds_assign_incr at h2,
    rw holds_assign_incr at h3,
    cases (h2 h3) },
  { intro w,
    refine ⟨h0.left _, _⟩,
    rw holds_assign_incr,
    exact h0.right },
  { intro w,
    cases classical.em ((M ₀↦ w) ⊨ q.incr) with h1 h1,
    { right, exact h1 },
    left, cases h0 with h2 h2,
    { apply h2 },
    rw holds_assign_incr at h1,
    cases (h1 h2) }
end

def pull_ex_left_eqv [inhabited α] (b : bool) (p q : form₂) :
  ∃* (form₂.bin b p q.incr) <==α==> form₂.bin b (∃* p) q :=
by { rw ← neg_eqv_neg,
     simp only [form₂.neg, neg_incr,
     bnot, pull_fa_left_eqv] }


def pull_left_eqv [inhabited α] (ae ao : bool) (p q : form₂) :
  form₂.qua ae (form₂.bin ao p q.incr) <==α==>
  form₂.bin ao (form₂.qua ae p) q :=
by {cases ae, apply pull_fa_left_eqv, apply pull_ex_left_eqv }

-- def pull_right_eqv [inhabited α] (ae ao : bool) (p q : form₂) :
--   form₂.qua ae (form₂.bin ao p.incr q) <==α==>
--   form₂.bin ao p (form₂.qua ae q) :=
-- begin
--   have h0 : ( form₂.qua ae (form₂.bin ao (form₂.incr p) q) <==α==>
--               form₂.qua ae (form₂.bin ao q (form₂.incr p)) ) :=
--   qua_eqv_qua (bin_comm _ _ _),
--   intro M,
--   simp only [ h0 M, pull_left_eqv ae ao q p M,
--     bin_comm ao p (form₂.qua ae q) M ]
-- end

@[reducible] def form₂.size_of_ordered :
  (Σ' (b : bool), (Σ' (a : form₂), form₂)) → nat
| ⟨tt, p, q⟩ := p.size_of + q.size_of + 1
| ⟨ff, p, q⟩ := p.size_of + q.size_of

meta def form₂.show_size_lt : tactic unit :=
`[ simp only [form₂.size_of_ordered, form₂.size_of,
   nat.lt_succ_self, add_comm, add_lt_add_iff_left,
   add_left_comm, form₂.size_of_incr ] ]

/- Pull quantifiers over a binary connective. `ae` specifies
   the type of quantifier to be pulled, and `ao` specifies
   the binary connective. -/
def pull (ae : option bool) (ao : bool) : bool → form₂ → form₂ → form₂
| tt (form₂.qua b p) q :=
  have form₂.size_of_ordered ⟨ff, ⟨q, form₂.qua b p⟩⟩ <
       form₂.size_of_ordered ⟨tt, ⟨form₂.qua b p, q⟩⟩,
  by form₂.show_size_lt,
  if ae = some (bnot b)
  then pull ff q (form₂.qua b p)
  else form₂.qua b (pull tt p q.incr)
| ff (form₂.qua b p) q :=
  have form₂.size_of_ordered ⟨ff, ⟨p, form₂.incr q⟩⟩ <
       form₂.size_of_ordered ⟨ff, ⟨form₂.qua b p, q⟩⟩,
  by form₂.show_size_lt,
  if ae = some (bnot b)
  then form₂.bin ao (form₂.qua b p) q
  else form₂.qua b (pull ff p q.incr)
| tt p q :=
  have form₂.size_of_ordered ⟨ff, ⟨q, p⟩⟩ <
       form₂.size_of_ordered ⟨tt, ⟨p, q⟩⟩,
  by form₂.show_size_lt,
  pull ff q p
| ff p q := form₂.bin ao p q
using_well_founded
  {rel_tac := λ _ _, `[exact ⟨_, measure_wf form₂.size_of_ordered⟩]}

lemma fov_pull (ae : option bool) (ao : bool) :
  ∀ (ls : bool) {p q : form₂} {k : nat},
  p.fov k → q.fov k → (pull ae ao ls p q).fov k
| tt ⟪m, a⟫           q :=
  have 0 < form₂.size_of ⟪m,a⟫ := zero_lt_one,
  by { intros k h0 h1,
       unfold pull,
       apply fov_pull ff h1 h0 }
| ff ⟪m, a⟫           q :=
  by { intros k h0 h1,
       unfold pull,
       refine ⟨h0, h1⟩ }
| tt (form₂.bin b p q) r :=
  have form₂.size_of_ordered ⟨ff, ⟨r, form₂.bin b p q⟩⟩ <
       form₂.size_of_ordered ⟨tt, ⟨form₂.bin b p q, r⟩⟩,
  by form₂.show_size_lt,
  by { intros k h0 h1,
       unfold pull,
       apply fov_pull ff h1 h0 }
| ff (form₂.bin b p q) r :=
  by { intros k h0 h1,
       unfold pull,
       refine ⟨h0, h1⟩ }
| tt (form₂.qua b p)   q :=
  have form₂.size_of_ordered ⟨ff, ⟨q, form₂.qua b p⟩⟩ <
       form₂.size_of_ordered ⟨tt, ⟨form₂.qua b p, q⟩⟩,
  by form₂.show_size_lt,
  begin
    intros k h0 h1,
    unfold pull,
    apply ite_cases,
    { apply fov_pull ff h1 h0 },
    apply fov_pull,
    { apply h0 },
    apply fov_incr h1
  end
| ff (form₂.qua b p)   q :=
  have form₂.size_of_ordered ⟨ff, ⟨p, form₂.incr q⟩⟩ <
       form₂.size_of_ordered ⟨ff, ⟨form₂.qua b p, q⟩⟩,
  by form₂.show_size_lt,
  begin
    intros k h0 h1,
    unfold pull,
    apply ite_cases,
    { refine ⟨h0, h1⟩ },
    apply fov_pull,
    { apply h0 },
    apply fov_incr h1
  end
using_well_founded
  { rel_tac := λ _ _, `[exact ⟨_, measure_wf form₂.size_of_ordered⟩] }

lemma foq_pull (ae : option bool) (ao b : bool) :
  ∀ ls : bool, ∀ {p q : form₂},
  foq b p → foq b q → foq b (pull ae ao ls p q)
| tt ⟪m, a⟫           q :=
  have 0 < form₂.size_of ⟪m,a⟫ := zero_lt_one,
  by { intros h0 h1,
       unfold pull,
       apply foq_pull _ h1 h0 }
| ff ⟪m, a⟫           q :=
  by { intros h0 h1,
       unfold pull,
       refine ⟨h0, h1⟩ }
| tt (form₂.bin b p q) r :=
  have form₂.size_of_ordered ⟨ff, ⟨r, form₂.bin b p q⟩⟩ <
       form₂.size_of_ordered ⟨tt, ⟨form₂.bin b p q, r⟩⟩,
  by form₂.show_size_lt,
  by { intros h0 h1,
       unfold pull,
       apply foq_pull _ h1 h0 }
| ff (form₂.bin b p q) r :=
  by { intros h0 h1,
       unfold pull,
       refine ⟨h0, h1⟩ }
| tt (form₂.qua b p)   q :=
  have form₂.size_of_ordered ⟨ff, ⟨q, form₂.qua b p⟩⟩ <
       form₂.size_of_ordered ⟨tt, ⟨form₂.qua b p, q⟩⟩,
  by form₂.show_size_lt,
  begin
    intros h0 h1,
    unfold pull,
    apply ite_cases,
    { apply foq_pull _ h1 h0 },
    refine ⟨λ h2, _, _⟩,
    { subst h2,
      apply fov_pull _ _ _ (h0.left rfl),
      apply form₂.fov_of_not_occ,
      apply form₂.not_occ_incr_ge },
    apply foq_pull _ h0.right,
    apply foq_incr_ge h1
  end
| ff (form₂.qua c p)   q :=
  have form₂.size_of_ordered ⟨ff, ⟨p, form₂.incr q⟩⟩ <
       form₂.size_of_ordered ⟨ff, ⟨form₂.qua b p, q⟩⟩,
  by form₂.show_size_lt,
  begin
    intros h0 h1,
    unfold pull,
    apply ite_cases,
    { refine ⟨h0, h1⟩ },
    refine ⟨λ h2, _, _⟩,
    { subst h2,
      apply fov_pull _ _ _ (h0.left rfl),
      apply form₂.fov_of_not_occ,
      apply form₂.not_occ_incr_ge },
    apply foq_pull _ h0.right,
    apply foq_incr_ge h1
  end
using_well_founded
  { rel_tac := λ _ _, `[exact ⟨_, measure_wf form₂.size_of_ordered⟩] }

def pull_eqv [inhabited α] (ae : option bool) (ao : bool) :
  ∀ ls : bool, ∀ p q : form₂,
  pull ae ao ls p q <==α==> form₂.bin ao p q
| tt ⟪k, a⟫           q :=
  have 0 < form₂.size_of ⟪k,a⟫ := zero_lt_succ _,
  by { apply eqv_trans _ (bin_comm _ _ _),
       unfold pull,
       apply pull_eqv }
| ff ⟪k, a⟫           q := by {unfold pull, apply eqv_refl}
| tt (form₂.bin b p q) r :=
  have form₂.size_of_ordered ⟨ff, ⟨r, form₂.bin b p q⟩⟩ <
       form₂.size_of_ordered ⟨tt, ⟨form₂.bin b p q, r⟩⟩,
  by form₂.show_size_lt,
  by { apply eqv_trans _ (bin_comm _ _ _),
       unfold pull,
       apply pull_eqv }
| ff (form₂.bin b p q) r := by {unfold pull, apply eqv_refl}
| tt (form₂.qua b p) q :=
  have  form₂.size_of_ordered ⟨ff, ⟨q, form₂.qua b p⟩⟩ <
        form₂.size_of_ordered ⟨tt, ⟨form₂.qua b p, q⟩⟩,
  by form₂.show_size_lt,
  begin
    unfold pull,
    apply @ite_cases _ (λ x, x <==α==>form₂.bin ao (form₂.qua b p) q),
    { apply eqv_trans _ (bin_comm _ _ _),
      apply pull_eqv },
    apply eqv_trans
      (qua_eqv_qua $ pull_eqv _ p _)
      (pull_left_eqv _ _ _ _)
  end
| ff (form₂.qua b p) q :=
  have  form₂.size_of_ordered ⟨ff, ⟨p, form₂.incr q⟩⟩ <
        form₂.size_of_ordered ⟨ff, ⟨form₂.qua b p, q⟩⟩,
  by form₂.show_size_lt,
  begin
    unfold pull,
    apply @ite_cases _ (λ x, x <==α==>form₂.bin ao (form₂.qua b p) q),
    { apply eqv_refl },
    apply eqv_trans
      (qua_eqv_qua $ pull_eqv _ p _)
      (pull_left_eqv _ _ _ _),
  end
using_well_founded
  {rel_tac := λ _ _, `[exact ⟨_, measure_wf form₂.size_of_ordered⟩]}

lemma QN_pull_aux {b : bool} (ao : bool) :
  ∀ {p q : form₂}, p.QN b → q.N b →
  (pull (some b) ao ff p q).QN b
| (form₂.lit c a) q h0 h1 :=
  by {unfold pull, refine ⟨h0, h1⟩}
| (form₂.bin c p q) r h0 h1 :=
  by {unfold pull, refine ⟨h0, h1⟩}
| (form₂.qua c p) q h0 h1 :=
  begin
    unfold pull,
    by_cases h2 : b = bnot c,
    { rw [← h2, if_pos rfl],
      rw eq_bnot_iff_ne at h2,
      refine ⟨⟨h2, h0.right h2⟩, h1⟩ },
    rw if_neg,
    { have h3 : b = c,
      { rw eq_bnot_iff_ne at h2,
        apply not_not.elim_left h2 },
      refine ⟨λ _, _, λ h4, absurd h3 h4⟩,
      apply QN_pull_aux (h0.left h3),
      apply form₂.N_incr_ge _ h1 },
    rw option.some_inj, exact h2
  end

lemma QN_pull {b : bool} (ao : bool) :
  ∀ {p q : form₂}, p.QN b → q.QN b →
  (pull (some b) ao tt p q).QN b
| (form₂.lit c a) q h0 h1 :=
  by {unfold pull, apply QN_pull_aux _ h1 h0}
| (form₂.bin _ p q) r h0 h1 :=
  by {unfold pull, apply QN_pull_aux _ h1 h0}
| (form₂.qua c p) q h0 h1 :=
  begin
    unfold pull,
    by_cases h2 : b = bnot c,
    { rw [← h2, if_pos rfl],
      rw eq_bnot_iff_ne at h2,
      apply QN_pull_aux _ h1,
      refine ⟨h2, h0.right h2⟩ },
    rw if_neg,
    { rw [eq_bnot_iff_ne, not_not] at h2,
      refine ⟨λ _, _, λ h3, absurd h2 h3⟩,
      apply QN_pull (h0.left h2),
      apply form₂.QN_incr_ge _ h1 },
    rw option.some_inj, exact h2
  end

lemma QF_pull_aux {b : bool} (ao : bool) :
  ∀ {p q : form₂}, p.QF b → q.F →
  (pull none ao ff p q).QF b
| (form₂.lit c a)   q h0 h1 :=
  by {unfold pull, refine ⟨h0, h1⟩}
| (form₂.bin c p q) r h0 h1 :=
  by {unfold pull, refine ⟨h0, h1⟩}
| (form₂.qua c p) q h0 h1 :=
  begin
    unfold pull, rw if_neg,
    { refine ⟨h0.left,
        QF_pull_aux h0.right (form₂.F_incr_ge _ h1)⟩ },
    rintro ⟨_⟩,
  end

lemma QF_pull {b : bool} (ao : bool) :
  ∀ {p q : form₂}, p.QF b → q.QF b →
  (pull none ao tt p q).QF b
| (form₂.lit c a) q h0 h1 :=
  by {unfold pull, apply QF_pull_aux _ h1 h0 }
| (form₂.bin _ p q) r h0 h1 :=
  by {unfold pull, apply QF_pull_aux _ h1 h0 }
| (form₂.qua c p) q h0 h1 :=
  begin
    unfold pull, rw if_neg,
    { refine ⟨h0.left,
        QF_pull h0.right (form₂.QF_incr_ge _ h1)⟩ },
    intro h2, cases h2
  end
