import .lit .arity .misc .logic tactic.monotonicity

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
local notation  p `∨*` q := form.or p q
local notation  p `∧*` q := form.and p q
local notation  `∀*` := form.fa
local notation  `∃*` := form.ex

meta def tactic.interactive.form.induce : tactic unit :=
`[ intro p, induction p with l p q ihp ihq p q ihp ihq p ih p ih  ]

namespace form

/- Semantics -/

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

def fam_fav (α : Type) (p : form) : Prop :=
∀ M : model α, ∀ v : nat →  α, (M ; v ⊨ p)

def fam_exv (α : Type) (p : form) : Prop :=
∀ M : model α, ∃ v : nat →  α, (M ; v ⊨ p)

/- Increment all variable indices equal to or greater than k by 1. -/
def incr_vdxs : nat → form → form
| k ⊤*       := ⊤*
| k ⊥*       := ⊥*
| k ⟪⟨b, a⟩⟫ := ⟪(b, a.incr_vdxs k)⟫
| k (p ∨* q) := (incr_vdxs k p) ∨* (incr_vdxs k q)
| k (p ∧* q) := (incr_vdxs k p) ∧* (incr_vdxs k q)
| k (∀* p)   := ∀* (incr_vdxs (k + 1) p)
| k (∃* p)   := ∃* (incr_vdxs (k + 1) p)

def decr_vdxs : form → form
| ⊤*       := ⊤*
| ⊥*       := ⊥*
| ⟪⟨b, a⟩⟫ := ⟪(b, a.decr_vdxs)⟫
| (p ∨* q) := (decr_vdxs p) ∨* (decr_vdxs q)
| (p ∧* q) := (decr_vdxs p) ∧* (decr_vdxs q)
| (∀* p)   := ∀* (decr_vdxs p)
| (∃* p)   := ∃* (decr_vdxs p)

def subst : nat → atom → form → form
| k s ⊤*         := ⊤*
| k s ⊥*         := ⊥*
| k s ⟪⟨b,a⟩⟫ := ⟪⟨b, a.subst [(k,s)]⟩⟫
| k s (p ∨* q)  := (subst k s p) ∨* (subst k s q)
| k s (p ∧* q)  := (subst k s p) ∧* (subst k s q)
| k s (∀* p)    := ∀* (subst (k+1) (s.incr_vdxs 0) p)
| k s (∃* p)    := ∃* (subst (k+1) (s.incr_vdxs 0) p)


def fresh_vdx : form → nat
| ⊤*       := 0
| ⊥*       := 0
| ⟪⟨b, a⟩⟫ := a.fresh_vdx
| (p ∨* q) := max (fresh_vdx p) (fresh_vdx q)
| (p ∧* q) := max (fresh_vdx p) (fresh_vdx q)
| (∀* p)   := fresh_vdx p - 1
| (∃* p)   := fresh_vdx p - 1

def fresh_sdx : form → nat
| ⊤*       := 0
| ⊥*       := 0
| ⟪(b, a)⟫ := a.fresh_sdx
| (p ∨* q) := max (fresh_sdx p) (fresh_sdx q)
| (p ∧* q) := max (fresh_sdx p) (fresh_sdx q)
| (∀* p)   := fresh_sdx p
| (∃* p)   := fresh_sdx p

def symb_arity (k : nat) : form → option (bool × nat)
| ⊤*       := none
| ⊥*       := none
| ⟪⟨b, a⟩⟫ := a.symb_arity k
| (p ∨* q) := (symb_arity p) <|> (symb_arity q)
| (p ∧* q) := (symb_arity p) <|> (symb_arity q)
| (∀* p)   := symb_arity p
| (∃* p)   := symb_arity p

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

end form

def free_vdxs : form → list nat
| ⊤*       := []
| ⊥*       := []
| ⟪l⟫      := l.vdxs
| (p ∧* q) := free_vdxs p ∪ free_vdxs q
| (p ∨* q) := free_vdxs p ∪ free_vdxs q
| (∀* p)   := ((free_vdxs p).filter ((<) 0)).map nat.pred
| (∃* p)   := ((free_vdxs p).filter ((<) 0)).map nat.pred

open list

def closed (p : form) : Prop := free_vdxs p = []

lemma closed_or_iff {p q : form} :
  closed (p ∨* q) ↔ (closed p ∧ closed q) :=
begin
  constructor; intro h0,
  { constructor;
    { apply eq_nil_iff_forall_not_mem.elim_right,
      have h1 := eq_nil_iff_forall_not_mem.elim_left h0,
      intros a h2,
      apply h1 a (mem_union.elim_right _),
      (`[apply (or.inl h2)] <|> `[apply (or.inr h2)]) } },
  have hp : free_vdxs p = [] := h0.left,
  have hq : free_vdxs q = [] := h0.right,
  simp only [free_vdxs, closed, hp, hq, nil_union]
end

lemma closed_and_iff {p q : form} :
  closed (p ∧* q) ↔ (closed p ∧ closed q) := closed_or_iff

--lemma closed_of_closed_and_right {p q : form} :
--  closed (p ∧* q) → closed q :=
--begin
--  intro h0,
--  apply eq_nil_iff_forall_not_mem.elim_right,
--  have h1 := eq_nil_iff_forall_not_mem.elim_left h0,
--  intros a h2,
--  apply h1 a (mem_union.elim_right (or.inr h2))
--end

def quant_free : form → Prop
| ⊤*       := true
| ⊥*       := true
| ⟪l⟫      := true
| (p ∧* q) := quant_free p ∧ quant_free q
| (p ∨* q) := quant_free p ∧ quant_free q
| (∀* p)   := false
| (∃* p)   := false

open list

def holds_iff_holds_of_agree_on_fvs (M : model α)  :
  ∀ p : form, ∀ v w : nat → α,
  (∀ k ∈ free_vdxs p, v k = w k) →
  (p.holds M v ↔ p.holds M w) :=
begin
  form.induce; intros v w h1; try {refl},
  { apply lit.holds_iff_holds_of_agree_on_fvs M v w _ h1 },
  repeat
  { have hp := ihp v w (list.forall_mem_of_forall_mem_union_left h1),
    have hq := ihq v w (list.forall_mem_of_forall_mem_union_right h1),
    simp only [form.holds, hp, hq] },
  tactic.focus [`[apply forall_iff_forall], `[apply exists_iff_exists]],
  repeat
  { intro a,
    apply ih (update_zero a v) (update_zero a w),
    intros k hk, cases k, refl,
    apply h1 _ (mem_map.elim_right ⟨k.succ,
      ⟨mem_filter_of_mem hk (nat.zero_lt_succ _), rfl⟩⟩) }
end

def holds_iff_holds_of_closed (M : model α) (v w : nat → α) {p : form} :
  closed p → (p.holds M v ↔ p.holds M w) :=
begin
  unfold closed, intros h1,
  apply holds_iff_holds_of_agree_on_fvs,
  rw h1, apply forall_mem_nil
end
