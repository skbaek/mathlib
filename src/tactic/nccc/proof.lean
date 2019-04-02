import .mat

@[reducible] def cla : Type := list lit

@[reducible] def sub : Type := list (nat × term)

local notation  `#` := term.var
local notation  `&` := term.fnc
local notation  t1 `^*` t2 := term.app t1 t2

def cla.is_pos (C : cla) : bool := C.all lit.sign

def cla.vdxs (C : cla) : list nat := ⋃ (C.map lit.vdxs)

def sub.term_app_aux (k : nat) : sub → term
| []         := #k
| ((m,t)::σ) :=
  if k = m then t else sub.term_app_aux σ

def sub.term_app (σ : sub) : term → term
| (# k) := sub.term_app_aux k σ
| (& k) := & k
| (t ^* s) := (sub.term_app t) ^* (sub.term_app s)

def sub.lit_app (σ : sub) : lit → lit
| ⟨b, m, ts⟩ := ⟨b, m, ts.map σ.term_app⟩

inductive proof : cla → mat → cla → Type
| axm {M : mat} {P : cla} : proof [] M P
| red {M : mat} {C P : cla} {L : lit} :
  L.neg ∈ P → proof C M P → proof (L::C) M P
| ext {M : mat} {C P : cla} {L : lit} (C₁ : cla) :
  C₁ ∈ M → proof C M P →
  proof (C₁.erase L.neg) (M.erase C₁) (L::P) →
  proof (L::C) M P
| cxt {M : mat} {C P : cla} (C₁ : cla) (L : lit) (σ : sub) :
  C₁ ∈ M → proof C M P →
  proof ((C₁.map (σ.lit_app)).erase L.neg) M (L::P) →
  proof (L::C) M P




#exit
open expr tactic

meta def foo : tactic unit :=
do m ← tactic.mk_meta_var `(term),
  trace m,
  (unify m `(term.var 0) >> trace m >> failed) <|>
  (trace m >> skip)

example : false := by foo



#exit

def sub.term_app : sub → term → term
| (# _)    := 0
| (& n)    := n + 1
| (t ^* s) := max (fresh_sdx t) (fresh_sdx s)


def sub.lit_app (σ : sub) (l : lit) : lit :=

#exit
