import .misc data.list.basic

variable {α : Type}

def value (α : Type) : Type := list α → (α × Prop)

def model (α : Type) : Type := nat → value α

@[derive has_reflect, derive decidable_eq]
inductive atom : Type
| var : nat → atom
| app : atom → atom → atom

def sub : Type := list (nat × atom)

def sub.get (σ : sub) (k : nat) : option atom :=
prod.snd <$> (list.find (eq k ∘ prod.fst)) σ

namespace atom

local notation `#` := atom.var
local notation a `&` b := atom.app a b

def val (M : model α) : atom → value α
| (# k)   := M k
| (a & b) := a.val ∘ list.cons (b.val []).fst

def subst (σ : sub) : atom → atom
| (# k) :=
  match σ.get k with
  | none   := # k
  | some s := s
  end
| (a & b) := subst a & subst b

lemma subst_eq_of_get_eq_none {σ : sub} {k : nat} :
  σ.get k = none → (# k).subst σ = # k :=
by {intro h1, simp only [h1, atom.subst]}

lemma subst_eq_of_get_eq_some {σ : sub} {k : nat} {a : atom} :
  σ.get k = some a → (# k).subst σ = a :=
by {intro h1, simp only [h1, atom.subst]}

end atom

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
  (M : model α) {σ : sub} {k : nat} {a : atom} :
  σ.get k = some a → M.subst σ k = a.val M :=
by {intro h1, simp only [h1, model.subst]}

end model

namespace atom

local notation `#` := atom.var
local notation a `&` b := atom.app a b

lemma val_subst (M : model α) (σ : sub) :
  ∀ a : atom, val M (a.subst σ) = val (M.subst σ) a
| (# k) :=
  begin
    rw function.funext_iff, intro as,
    cases h1 : σ.get k with s,
    simp only [val, atom.subst_eq_of_get_eq_none h1,
      model.subst_eq_of_get_eq_none M h1],
    simp only [val, atom.subst_eq_of_get_eq_some h1,
      model.subst_eq_of_get_eq_some M h1],
  end
| (a & b) :=
  begin
    rw function.funext_iff, intro as,
    have h1 := val_subst a,
    have h2 := val_subst b,
    simp only [val, subst, h1, h2],
  end

end atom

local notation f `₀↦` a := update_zero a f

@[derive has_reflect]
inductive form : Type
| false : form
| true : form
| lit : bool → atom → form
| or  : form → form → form
| and : form → form → form
| fa  : form → form
| ex  : form → form

local notation `⊤*`     := form.true
local notation `⊥*`     := form.false
local notation `+*`     := form.lit tt
local notation `-*`     := form.lit ff
local notation p `∨*` q := form.or p q
local notation p `∧*` q := form.and p q
local notation `∀*`     := form.fa
local notation `∃*`     := form.ex

def holds : model α → form → Prop
| M ⊤*       := _root_.true
| M ⊥*       := _root_.false
| M (+* a)   :=    (a.val M []).snd
| M (-* a)   :=  ¬ (a.val M []).snd
| M (p ∨* q) := holds M p ∨ holds M q
| M (p ∧* q) := holds M p ∧ holds M q
| M (∀* p)   := ∀ x : value α, holds (M ₀↦ x) p
| M (∃* p)   := ∃ x : value α, holds (M ₀↦ x) p
