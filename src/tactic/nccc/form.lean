import .lit .arity

open tactic

variables {α β : Type}

@[derive has_reflect]
inductive form : Type
| false : form
| true : form
| lit : lit → form
| or  : form → form → form
| and : form → form → form
| fa  : form → form
| ex  : form → form

local notation  `⊤*` := form.true
local notation  `⊥*` := form.false
local notation  `⟪` l `⟫` := form.lit l
local notation  p `∧*` q := form.and p q
local notation  p `∨*` q := form.or p q
local notation  `∀*` := form.fa
local notation  `∃*` := form.ex

-- | ⊤*        := sorry
-- | ⊥*        := sorry
-- | ⟪⟨s, k, ts⟩⟫ := sorry
-- | (p ∧* q)  := sorry
-- | (p ∨* q)  := sorry
-- | (∀* p)  := sorry
-- | (∃* p)  := sorry

namespace form

local notation f `₀↦` a := update_zero a f

def holds (M : model α) : (nat → α) → form → Prop
| v ⊤*        := _root_.true
| v ⊥*        := _root_.false
| v ⟪l⟫      := l.holds M v
| v (p ∨* q) := (p.holds v) ∨ (q.holds v)
| v (p ∧* q) := (p.holds v) ∧ (q.holds v)
| v (∀* p)   := ∀ a : α, p.holds (v ₀↦ a)
| v (∃* p)   := ∃ a : α, p.holds (v ₀↦ a)

local notation M `;` v `⊨` p := holds M v p

def valid (α p) : Prop :=
∀ M : model α, ∀ v, (M ; v ⊨ p)

def valsat (α p) : Prop :=
∀ M : model α, ∃ v, (M ; v ⊨ p)

def sat (α p) : Prop :=
∃ M : model α, ∃ v, (M ; v ⊨ p)

def subst : nat → term → form → form
| k s ⊤*         := ⊤*
| k s ⊥*         := ⊥*
| k s ⟪⟨b,m,ts⟩⟫ := ⟪⟨b,m,ts.map (term.subst k s)⟩⟫
| k s (p ∨* q)  := (subst k s p) ∨* (subst k s q)
| k s (p ∧* q)  := (subst k s p) ∧* (subst k s q)
| k s (∀* p)    := ∀* (subst (k+1) s.incr_vdx p)
| k s (∃* p)    := ∃* (subst (k+1) s.incr_vdx p)

end form

local notation m `↦` a := update m a

def symb_arity_args (k : nat) : list term → option (bool × nat)
| []      := none
| (t::ts) := term.symb_arity k t <|> symb_arity_args ts

def symb_arity (k : nat) : form → option (bool × nat)
| ⊤* := none
| ⊥* := none
| ⟪⟨s, m, ts⟩⟫ :=
  if k = m then some (tt, ts.length)
  else symb_arity_args k ts
| (p ∨* q) := (symb_arity p) <|> (symb_arity q)
| (p ∧* q) := (symb_arity p) <|> (symb_arity q)
| (∀* p)   := symb_arity p
| (∃* p)   := symb_arity p

def univ_close_core (p : form) :
  nat → model α → Prop
| 0     M :=  p.holds M (λ _, M.inhab)
| (k+1) M :=
  match symb_arity k p with
  | none   := ∀ u : unit, univ_close_core k M
  | some (tt,m) :=
    ∀ r : arity α Prop m, univ_close_core k
    {M with rels  := (k ↦ r.app_list false) M.rels}
  | some (ff,m) :=
    ∀ f : arity α α m, univ_close_core k
    {M with funcs := (k ↦ f.app_list M.inhab) M.funcs}
  end

lemma univ_close_core_of_valid (p : form) (h1 : p.valid α) :
  ∀ (k : nat) (M : model α), univ_close_core p k M
| 0 M     := by apply h1
| (k+1) M :=
  begin
    unfold univ_close_core,
    cases (symb_arity k p) with bm,
    { intro _, apply univ_close_core_of_valid },
    { cases bm with b m, cases b;
      intro _; apply univ_close_core_of_valid }
  end

def fresh_sdx : form → nat
| ⊤* := 0
| ⊥* := 0
| ⟪⟨s, m, ts⟩⟫ := list.max ((m + 1) :: ts.map term.fresh_sdx)
| (p ∨* q)     := max (fresh_sdx p) (fresh_sdx q)
| (p ∧* q)     := max (fresh_sdx p) (fresh_sdx q)
| (∀* p)       := fresh_sdx p
| (∃* p)       := fresh_sdx p

def univ_close (α : Type) [h : inhabited α] (p : form) : Prop :=
univ_close_core p (fresh_sdx p) (model.default α)

lemma univ_close_of_valid [h : inhabited α] (p : form) :
  p.valid α → univ_close α p :=
λ h1, univ_close_core_of_valid _ h1 _ _

def free_vars : nat → form → list nat
| k ⊤*         := []
| k ⊥*         := []
| k ⟪⟨s,m,ts⟩⟫ := ⋃ (ts.map (term.free_vars k))
| k (p ∧* q)   := list.union (free_vars k p) (free_vars k q)
| k (p ∨* q)   := list.union (free_vars k p) (free_vars k q)
| k (∀* p)     := free_vars (k+1) p
| k (∃* p)     := free_vars (k+1) p
  #exit

  #exit
| k M p := M ; (λ _, @inhabited.default _ _) ⊨ p
| k M p := ∀ r : arity α Prop k, univ_close (M.add_rel  r.app_list) ars p
| k M p := ∀ f : arity α α k,    univ_close (M.add_func f.app_list) ars p


def repr : form → string
| ⊥* := "⊥"
| ⊤* := "⊤"
| ⟪l⟫ := l.repr
| (φ ∨* ψ) := "(" ++ (φ.repr) ++ " ∨ " ++ (ψ.repr) ++ ")"
| (φ ∧* ψ) := "(" ++ (φ.repr) ++ " ∧ " ++ (ψ.repr) ++ ")"
| (∀* φ) := "∀" ++ φ.repr
| (∃* φ) := "∃" ++ φ.repr

instance has_repr : has_repr form := ⟨repr⟩

meta instance has_to_format : has_to_format form := ⟨λ x, repr x⟩

#exit
meta def induce (t : tactic unit := skip) : tactic unit :=
`[ intro p, induction p with k ts p ih p q ihp ihq p q ihp ihq p ih p ih; t ]

meta def induce_iff (t : tactic unit := skip) : tactic unit :=
induce t >>
focus [ skip, skip, skip,
  `[ apply not_iff_not_of_iff ],
  `[ apply or_iff_or   ],
  `[ apply and_iff_and ],
  `[ apply forall_iff_forall, intro ],
  `[ apply exists_iff_exists, intro ] ]


def closed (p : form) : Prop := p.fresh_idx = 0

--instance dec_max_idx_lt : ∀ p : form, ∀ k, decidable (p.max_idx_lt k) :=
--begin
--  induce `[intro k, try {simp_fol}, try {apply_instance},
--    try {apply @and.decidable _ _ _ _}, try {apply ih},
--    try {apply ihp}, try {apply ihq}],
--end
--
--instance dec_closed (p : form) : decidable (closed p) := p.dec_max_idx_lt 0


--def equiv (α p q) : Prop :=
--∀ M : model α, ∀ v, ((M ; v ⊨ p) ↔ (M ; v ⊨ q))


#exit
--| [] M := by apply h
--| ((b,k)::as) σ :=
--  begin
--    cases b; simp [rvalid];
--    intro r; apply rvalid_of_valid
--  end

#exit
def unsat (α p) : Prop := ¬ sat α p


lemma holds_iff_holds_of_max_idx_lt :
  ∀ (p : form) (M : model α) (v w : nat → α) k, p.max_idx_lt k →
  (∀ m < k, v m = w m) → ((M ; v ⊨ p) ↔ (M ; w ⊨ p)) :=
begin
  induce_iff `[intros M v w m h1 h2, split_ands], trivial, trivial,
  { simp_fol, apply iff_of_eq (congr_arg _ _),
    apply list.map_eq_map_of_forall_mem_eq,
    intros t h4, apply term.val_eq_val_of_max_idx_lt,
    apply h1 _ h4, apply h2 },
  { apply ih; assumption },
  { apply ihp; assumption },
  { apply ihq; assumption },
  { apply ihp; assumption },
  { apply ihq; assumption },
  { apply ih, apply h1, intro n, cases n with n; intro h3,
    refl, apply h2, rw ← nat.succ_lt_succ_iff, assumption },
  { apply ih, apply h1, intro n, cases n with n; intro h3,
    refl, apply h2, rw ← nat.succ_lt_succ_iff, assumption }
end

lemma holds_iff_holds_of_closed :
  ∀ (M : model α) v w p, closed p →
  ((M ; v ⊨ p) ↔ (M ; w ⊨ p)) :=
begin
  intros M v w p h1,
  apply holds_iff_holds_of_max_idx_lt,
  apply h1, intros m h2, cases h2
end

lemma valid_of_closed_of_unsat_neg [inhabited α] :
  ∀ {p : form}, closed p → unsat α (¬* p) → valid α p :=
begin
  simp only [valid, unsat, sat], intros p h1 h2 M v,
  apply classical.by_contradiction, intro h3,
  apply h2, refine ⟨M, _⟩, intro w,
  rw holds_iff_holds_of_closed _ _ w _ h1 at h3, assumption,
end


def fresh_func_idx : form → nat
| ⊤*        := 0
| ⊥*        := 0
| (m ** ts) := list.max (ts.map (term.fresh_func_idx))
| (¬* p)    := fresh_func_idx p
| (p ∧* q)  := max (fresh_func_idx p) (fresh_func_idx q)
| (p ∨* q)  := max (fresh_func_idx p) (fresh_func_idx q)
| (∀* p)    := fresh_func_idx p
| (∃* p)    := fresh_func_idx p


end form
