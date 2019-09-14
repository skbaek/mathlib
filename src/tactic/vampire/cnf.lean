/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek

  CNF frmulas.
-/

import tactic.vampire.pnf
import tactic.vampire.list

namespace vampire

variables {α : Type}
variables {R : rls α} {F : fns α} {V : vas α}

local notation p `∨*` q := frm.bin tt p q
local notation p `∧*` q := frm.bin ff p q
local notation `∃*` p   := frm.qua tt p
local notation `∀*` p   := frm.qua ff p

@[reducible] def lit : Type := bool × atm
@[reducible] def cla : Type := list lit
@[reducible] def mat : Type := list cla

open list

def map_app_prod_aux : cla → mat → mat
| lc []          := []
| lc (rc :: rcs) := (lc ++ rc) :: map_app_prod_aux lc rcs

def map_app_prod : mat → mat → mat
| []          rcs := []
| (lc :: lcs) rcs :=
  (list.map (list.append lc) rcs) ++ (map_app_prod lcs rcs)

lemma map_app_prod_nil :
  ∀ m : mat, map_app_prod m [] = []
| []       := rfl
| (c :: m) :=
  by simp only [map_app_prod, map, map_app_prod_nil m, nil_append]

def cnf : frm → mat
| (frm.atm b a) := [[(b, a)]]
| (f ∨* g)      := map_app_prod (cnf f) (cnf g)
| (f ∧* g)      := (cnf f) ++ (cnf g)
| (frm.qua _ _) := []

namespace lit

def equiv : lit → lit → Prop
| (b1, l1) (b2, l2) := b1 = b2 ∧ atm.equiv l1 l2

def vsubs (μs : vmaps) : lit → lit
| (b, a):= (b, a.vsubs μs)

meta def to_expr : lit → expr
| (b, a) := expr.mk_app `(@prod.mk bool atm) [b.to_expr, a.to_expr]

def holds (R : rls α) (F : fns α) (V : vas α) : lit → Prop
| (ff, a):= ¬ a.holds R F V
| (tt, a):=   a.holds R F V

def repr : lit → string
| (ff, a):= "¬" ++ a.repr
| (tt, a):=        a.repr

def replace (t s : trm) : lit → lit
| (b, a) := (b, a.replace t s)

instance has_repr : has_repr lit := ⟨repr⟩

lemma holds_replace {r u : trm}
  (h0 : r.val F V = u.val F V) :
  ∀ l : lit, (l.replace r u).holds R F V ↔ l.holds R F V :=
by rintro ⟨_ | _, a⟩;
   unfold replace; unfold holds;
   rw atm.holds_replace h0

lemma holds_iff_holds_of_equiv :
  ∀ {l1 l2 : lit}, equiv l1 l2 → (l1.holds R F V ↔ l2.holds R F V)
| (b1, a1) (b2, a2) h0 :=
  begin
    cases h0 with h0 h1,
    rw h0, cases b2; unfold holds;
    rw atm.holds_iff_holds_of_equiv h1,
  end

lemma holds_vsubs (μs : vmaps) (l : lit) :
  (l.vsubs μs).holds R F V ↔
  l.holds R F (V.vsubs F μs) :=
begin
  cases l with b a; cases b;
  simp only [ lit.holds, lit.vsubs, atm.holds_vsubs ]
end

instance equiv_decidable : decidable_rel lit.equiv
| (b1, a1) (b2, a2) := and.decidable

end lit

namespace cla

@[reducible] def subsumes (c d : cla) : Prop := ∀ l1 ∈ c, ∃ l2 ∈ d, lit.equiv l1 l2

instance subsumes_decidable : decidable_rel subsumes :=
λ c d, @list.decidable_fa_mem lit _ (λ l, @list.decidable_ex_mem lit (lit.equiv l) _ d) c

def tautology : cla := [(tt, atm.default)]

def vsubs (μs : vmaps) : cla → cla :=
list.map (lit.vsubs μs)

meta def to_expr : cla → expr
| []       := `(@list.nil lit)
| (l :: c) := expr.mk_app `(@list.cons lit) [l.to_expr, to_expr c]

def holds (R : rls α) (F : fns α) (V : vas α) (c : cla) : Prop :=
∃ l ∈ c, lit.holds R F V l

def repr : cla → string
| []  := "⊥"
| [l] := l.repr
| (l :: ls) := l.repr ++ " | " ++ repr ls

lemma holds_of_subsumes {c d : cla} :
  subsumes c d → holds R F V c → holds R F V d :=
begin
  intros h0 h1,
  rcases h1 with ⟨l, h1, h2⟩,
  rcases h0 l h1 with ⟨w, h3, h4⟩,
  refine ⟨w, h3, _⟩,
  rw ← lit.holds_iff_holds_of_equiv h4,
  exact h2
end

lemma holds_vsubs {μs : vmaps} {c : cla} :
  (c.vsubs μs).holds R F V ↔
  c.holds R F (V.vsubs F μs) :=
by { apply @list.exists_mem_map_iff,
     apply lit.holds_vsubs }

end cla

namespace mat

def repr_core : nat → mat → string
| _ []  := ""
| k [c] := k.repr ++ ". " ++ cla.repr c
| k (c :: m) :=
  k.repr ++ ". " ++ cla.repr c ++ "\n" ++ repr_core (k + 1) m

def repr : mat → string := repr_core 0

instance has_repr : has_repr mat := ⟨repr⟩

def nth (m : mat) (k : nat) : cla :=
option.get_or_else (list.nth m k) cla.tautology

meta def to_expr : mat → expr
| []       := `(@list.nil cla)
| (c :: m) := expr.mk_app `(@list.cons cla) [c.to_expr, to_expr m]

def holds (R : rls α) (F : fns α) (V : vas α) (m : mat) : Prop :=
∀ c ∈ m, cla.holds R F V c


end mat

lemma holds_map_app_prod_left :
  ∀ m n : mat, m.holds R F V →
  (map_app_prod m n).holds R F V
| []       n h0 := list.forall_mem_nil _
| (c :: m) n h0 :=
  begin
    unfold mat.holds at h0,
    simp only [map_app_prod, mat.holds],
    rw forall_mem_append,
    constructor,
    { intros cd h1,
      rw list.mem_map at h1,
      rcases h1 with ⟨d, h1, h2⟩,
      rw ← h2, unfold cla.holds,
      apply exists_mem_append.elim_right,
      left, apply h0 _ (or.inl rfl) },
    apply holds_map_app_prod_left,
    apply forall_mem_of_forall_mem_cons h0
  end

lemma holds_map_app_prod_right :
  ∀ m n : mat, n.holds R F V →
  (map_app_prod m n).holds R F V
| []       n h0 := list.forall_mem_nil _
| (c :: m) n h0 :=
  begin
    unfold mat.holds at h0,
    simp only [map_app_prod, mat.holds],
    rw list.forall_mem_append,
    constructor,
    { intros cd h1,
      rw list.mem_map at h1,
      rcases h1 with ⟨d, h1, h2⟩,
      rw ← h2, unfold cla.holds,
      apply list.exists_mem_append.elim_right,
      right, apply h0 _ h1 },
    apply holds_map_app_prod_right _ _ h0
  end

lemma holds_cnf [inhabited α] :
  ∀ {f : frm}, f.F → f.holds R F V → (cnf f).holds R F V
| (frm.atm b a) h0 h1 :=
  begin
    intros c h2,
    rw list.eq_of_mem_singleton h2,
    refine ⟨_, or.inl rfl, _⟩,
    cases b; exact h1
  end
| (f ∧* g) h0 h1 :=
  begin
    cases h0 with h0p h0q,
    cases h1 with h1p h1q,
    replace hp := holds_cnf h0p h1p,
    replace hq := holds_cnf h0q h1q,
    simp only [mat.holds, cnf],
    rw list.forall_mem_append,
    refine ⟨hp, hq⟩,
  end
| (f ∨* g) h0 h1 :=
  begin
    cases h0 with h0f h0g,
    cases h1; unfold cnf,
    { apply holds_map_app_prod_left,
      apply holds_cnf h0f h1 },
    apply holds_map_app_prod_right,
    apply holds_cnf h0g h1,
  end

lemma not_holds_empty_cla :
  ¬ (cla.holds R F V []) :=
by rintro ⟨_, ⟨_⟩, _⟩

lemma holds_tautology : cla.tautology.holds R F V :=
⟨_, or.inl rfl, rfl⟩

end vampire
