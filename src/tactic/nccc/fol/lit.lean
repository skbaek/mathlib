import .model logic.basic data.list.basic .nat

variable {α : Type}

@[derive has_reflect, derive decidable_eq]
inductive atom : Type
| sym : nat  → atom
| app : atom → atom → atom
| vpp : atom → nat  → atom

def sub : Type := list (nat × atom)

def sub.get (σ : sub) (k : nat) : option atom :=
prod.snd <$> (list.find (eq k ∘ prod.fst)) σ

namespace atom

local notation `⅋` k   := atom.sym k
local notation a `&` b := atom.app a b
local notation a `#` k := atom.vpp a k

def repr_core : bool → atom → string
| s (⅋ k)   := (if s then "P" else "F") ++ k.to_subs
| s (a & b) := "(" ++ a.repr_core s ++ " " ++ b.repr_core ff ++ ")"
| s (a # k) := "(" ++ a.repr_core s ++ " " ++ "X" ++ k.to_subs ++ ")"

def repr : atom → string := repr_core tt

def fval (M : model α) (v : nat → α) : atom → list α → α
| (⅋ k)   as := M.funs k as
| (a & b) as := a.fval (b.fval [] :: as)
| (a # k) as := a.fval (v k :: as)

def rval (M : model α) (v : nat → α) : atom → list α → Prop
| (⅋ k)   as := M.rels k as
| (a & b) as := a.rval (b.fval M v [] :: as)
| (a # k) as := a.rval (v k :: as)

def incr_vdxs (k : nat) : atom → atom
| (⅋ m)   := ⅋ m
| (t & s) := (incr_vdxs t) & (incr_vdxs s)
| (t # m) := if k ≤ m then t.incr_vdxs # (m + 1) else t # m

def decr_vdxs : atom → atom
| (⅋ m)   := ⅋ m
| (a & b) := (decr_vdxs a) & (decr_vdxs b)
| (a # m) := a.decr_vdxs # m.pred

def vdxs : atom → list nat
| (⅋ _)   := []
| (a & b) := a.vdxs ∪ b.vdxs
| (a # m) := a.vdxs.insert m

def subst (σ : sub) : atom → atom
| (⅋ k)   := ⅋ k
| (t & s) := subst t & subst s
| (t # k) :=
  match σ.get k with
  | none   := subst t # k
  | some s := subst t & s
  end

def symb_arity (k : nat) : atom → option (bool × nat)
| (⅋ m) := if k = m then some (tt, 0) else none
| (a & b) :=
  (do (s, n) ← symb_arity a,
      return (s, if s then n + 1 else n)) <|>
  (do (s, n) ← symb_arity b, return (ff, n))
| (a # m) :=
  do (s, n) ← symb_arity a,
     return (s, if s then n + 1 else n)

def fresh_vdx : atom → nat
| (⅋ _)   := 0
| (t & s) := max t.fresh_vdx s.fresh_vdx
| (t # m) := max t.fresh_vdx (m + 1)

def fresh_sdx : atom → nat
| (⅋ n)   := n + 1
| (t & s) := max (fresh_sdx t) (fresh_sdx s)
| (t # _) := fresh_sdx t

open list

def fval_eq_fval_of_agree_on_fvs (M : model α) (v w : nat → α) :
  ∀ a : atom, (∀ k ∈ a.vdxs, v k = w k) → a.fval M v = a.fval M w
| (⅋ k)   h1 := by {ext as, refl}
| (a & b) h1 :=
begin
    have ha := fval_eq_fval_of_agree_on_fvs a
      (forall_mem_of_forall_mem_union_left h1),
    have hb := fval_eq_fval_of_agree_on_fvs b
      (forall_mem_of_forall_mem_union_right h1),
    ext as, simp only [fval, ha, hb]
end
| (a # k) h1 :=
begin
  have ha := fval_eq_fval_of_agree_on_fvs a
    (λ x hx, h1 x (mem_insert_of_mem hx)),
  have hk := h1 k (mem_insert_self _ _),
  ext as, simp only [fval, ha, hk]
end

def rval_eq_rval_of_agree_on_fvs (M : model α) (v w : nat → α) :
  ∀ a : atom, (∀ k ∈ a.vdxs, v k = w k) → (a.rval M v = a.rval M w)
| (⅋ k)   h1 := by {ext as, refl}
| (a & b) h1 :=
  begin
    have ha := rval_eq_rval_of_agree_on_fvs a
      (forall_mem_of_forall_mem_union_left h1),
    have hb := fval_eq_fval_of_agree_on_fvs M v w b
      (forall_mem_of_forall_mem_union_right h1),
    ext as, simp [rval, ha, hb]
  end
| (a # k) h1 :=
  begin
    have ha := rval_eq_rval_of_agree_on_fvs a
      (λ x hx, h1 x (mem_insert_of_mem hx)),
    have hk := h1 k (mem_insert_self _ _),
    ext as, simp only [rval, ha, hk]
  end

end atom

def val.subst (M : model α) (v : nat → α) (σ : sub) (k : nat) : α :=
match σ.get k with
| none   := v k
| some t := t.fval M v []
end

lemma val.subst_eq_of_eq_none (M : model α)
  (v : nat → α) {σ : sub} {k : nat} :
σ.get k = none → val.subst M v σ k = v k :=
by { intro h1, simp only [h1, val.subst] }

lemma val.subst_eq_of_eq_some (M : model α)
  (v : nat → α) {σ : sub} {k : nat} {t : atom} :
σ.get k = some t → val.subst M v σ k = t.fval M v [] :=
by { intro h1, simp only [h1, val.subst] }

namespace atom

local notation `⅋` k   := atom.sym k
local notation a `&` b := atom.app a b
local notation a `#` k := atom.vpp a k

lemma subst_eq_of_eq_none {σ : sub} (t : atom) {k : nat} :
σ.get k = none → subst σ (t # k) = subst σ t # k :=
by { intro h, simp only [h, subst, eq_self_iff_true, and_self] }

lemma subst_eq_of_eq_some {σ : sub} (t s : atom) {k : nat} :
σ.get k = some s → subst σ (t # k) = (subst σ t & s) :=
by { intro h, simp only [h, subst, eq_self_iff_true, and_self] }

lemma fval_subst (M : model α) (v : nat → α) (σ : sub) :
  ∀ t : atom, ∀ as : list α,
  fval M v (t.subst σ) as = fval M (val.subst M v σ) t as
| (⅋ k) as   := rfl
| (t & s) as :=
  begin
    have h1 := fval_subst t,
    have h2 := fval_subst s [],
    simp only [fval, subst, h1, h2]
  end
| (t # k) as :=
  begin
    cases h1 : σ.get k with s,
    simp only [subst_eq_of_eq_none t h1,
      val.subst_eq_of_eq_none M v h1,
      fval_subst, fval],
    simp only [subst_eq_of_eq_some t s h1,
      val.subst_eq_of_eq_some M v h1,
      fval_subst, fval]
  end

lemma rval_subst (M : model α) (v : nat → α) (σ : sub) :
  ∀ t : atom, ∀ as : list α,
  rval M v (t.subst σ) as ↔ rval M (val.subst M v σ) t as
| (⅋ k) as   := by refl
| (t & s) as :=
  begin
    have h1 := rval_subst t,
    have h2 := fval_subst M v σ s [],
    simp only [rval, subst, h1, h2]
  end
| (t # k) as :=
  begin
    cases h1 : σ.get k with s,
    simp only [subst_eq_of_eq_none t h1,
      val.subst_eq_of_eq_none M v h1,
      rval_subst, rval],
    simp only [subst_eq_of_eq_some t s h1,
      val.subst_eq_of_eq_some M v h1,
      rval_subst, rval]
  end

lemma fval_comp_subst (M : model α) (v : nat → α) (σ : sub) :
  fval M v ∘ (subst σ) = fval M (val.subst M v σ) :=
function.funext_iff.elim_right (by {intro a, ext as, apply fval_subst})

lemma rval_comp_subst (M : model α) (v : nat → α) (σ : sub) :
  rval M v ∘ (subst σ) = rval M (val.subst M v σ) :=
function.funext_iff.elim_right (by {intro a, ext as, apply rval_subst})

end atom

def lit : Type := bool × atom

namespace lit

def neg : lit → lit
| ⟨b, a⟩ := ⟨bnot b, a⟩

def holds (M : model α) (v : nat → α) : lit → Prop
| ⟨tt, a⟩  :=    (a.rval M v [])
| ⟨ff, a⟩  :=  ¬ (a.rval M v [])

def vdxs : lit → list nat
| ⟨b, a⟩ := a.vdxs

def holds_iff_holds_of_agree_on_fvs
  (M : model α) (v w : nat → α) (l : lit) :
  (∀ k ∈ l.vdxs, v k = w k) → (lit.holds M v l ↔ lit.holds M w l) :=
begin
  intro h1, cases l with b a, cases b;
  have h2 := atom.rval_eq_rval_of_agree_on_fvs M v w a h1;
  simp only [lit.holds, h2]
end

def repr : lit → string
| ⟨b, a⟩ := (if b then "" else "¬") ++ a.repr

instance has_repr : has_repr lit := ⟨repr⟩

meta instance has_to_format : has_to_format lit := ⟨λ x, repr x⟩

def subst (σ : sub) : lit → lit
| (b, a) := (b, a.subst σ)

lemma holds_neg (M : model α) (v : nat → α) (l : lit) :
  holds M v l.neg ↔ ¬ holds M v l :=
by { cases l with b; cases b;
     simp only [bnot, neg, holds, list.map, classical.not_not] }

lemma holds_subst (M : model α) (v : nat → α) (σ : sub) (l : lit) :
  holds M v (l.subst σ) ↔ holds M (val.subst M v σ) l :=
begin
  cases l with b a, cases b;
  simp only [holds, subst, val.subst,
    list.map_map, atom.rval_subst]
end

end lit
