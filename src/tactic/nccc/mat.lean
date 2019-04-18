import .swap 
universe u 

variables {α β : Type u}

open nat

local notation f `₀↦` a := assign a f
postfix  `ₑ` : 1000 := evaluate 
postfix  `ᵈ` : 1000 := denote
local infix `⬝` := value.app

namespace fol

@[derive has_reflect, derive decidable_eq]
inductive term : Type
| sym : nat  → term
| app : term → term → term
| vpp : term → nat  → term

inductive form : Type
| lit : bool → term → form
| bin : bool → form → form → form

def term.val (M : model α) (v : nat → α) : term → value α
| (term.sym k)   := M k 
| (term.app a b) := a.val ∘ list.cons (b.val []).fst 
| (term.vpp a k) := a.val ∘ list.cons (v k) 

def form.holds (M : model α) (v : nat → α) : form → Prop
| (form.lit tt a)   :=   (a.val M v []).snd
| (form.lit ff a)   := ¬ (a.val M v []).snd
| (form.bin tt p q) := p.holds ∨ q.holds 
| (form.bin ff p q) := p.holds ∧ q.holds 

end fol

def fam_exv (α : Type u) (p : fol.form) : Prop :=
∀ M : model α, ∃ v : nat → α, p.holds M v 

local notation `&`     := fol.term.sym
local notation a `&` b := fol.term.app a b
local notation a `#` k := fol.term.vpp a k

local notation `⟪` b `,` a `⟫` := fol.form.lit b a
local notation p `∨*` q        := fol.form.bin tt p q
local notation p `∧*` q        := fol.form.bin ff p q

def term.folize (k : nat) : term → fol.term 
| (term.var m) := (& m)
| (term.app a (term.var m)) :=
  if m < k 
  then a.folize # m
  else a.folize & (& m)
| (term.app a (term.app b c)) :=
  a.folize & (term.app b c).folize

def form.folize : nat → form → fol.form
| k (form.lit b t)   := ⟪b, t.folize k⟫
| k (form.bin b p q) := fol.form.bin b (p.folize k) (q.folize k) 
| k (form.qua tt p)  := p.folize k.succ
| k (form.qua ff p)  := p.folize k


lemma fam_of_fam_exv_folize : 
  ∀ k : nat, ∀ p : form, is_E k p → 
  fam_exv α (p.folize k) → fam α p 
| 0       (form.lit b a)    h0 := sorry --is_QF p
| 0       (form.bin _ _ _)  h0 := sorry --false
| 0       (form.qua tt p)   h0 := by cases h0 
| (k + 1) (form.lit b a)    h0 := by cases h0
| (k + 1) (form.bin _ _ _)  h0 := by cases h0
| (k + 1) (form.qua tt p)   h0 := sorry --is_E k p


#exit

def is_E : nat → form → Prop 
| 0       (form.qua tt p) := false
| (k + 1) (form.qua tt p) := is_E k p
| 0       p               := is_QF p
| (k + 1) p               := false


#exit
@[reducible] def lit : Type := bool × term
@[reducible] def cla : Type := list lit
@[reducible] def mat : Type := list cla

def lit.holds (M : model α) (v : nat → α) : lit → Prop
| (tt, a)  :=    (a.val M v []).snd
| (ff, a)  :=  ¬ (a.val M v []).snd

def cla.holds (M : model α) (v : nat → α) (c : cla) : Prop :=
∀ l ∈ c, lit.holds M v l

def mat.holds (M : model α) (v : nat → α) (m : mat) : Prop :=
∃ c ∈ m, cla.holds M v c

def fam_exv (α : Type u) (m : mat) : Prop :=
∀ M : model α, ∃ v : nat → α, m.holds M v 




#exit
def dnf : nat → form → mat
| k ⟪b, a⟫   := [[(b, symbolize k a)]]
| k (p ∨* q) := dnf k p ++ dnf k q
| k (p ∧* q) := 
  (list.product (dnf k p) (dnf k q)).map (λ x, x.fst ++ x.snd)
| k (∀* p)   := dnf k p 
| k (∃* p)   := dnf k.succ p 

lemma fam_exv_dnf :
  ∀ k : nat, ∀ p : form, is_E p → 
  (fam_exv α (dnf k p) ↔ fam α p) 
| k (∃* p) h0 := 
  begin
    simp only [dnf],
    have h1 := fam_exv_dnf k.succ p h0,

  end


#exit
lemma fam_exv_dnf_zero :
  ∀ p : form, is_AE p → 
  (fam_exv α (dnf 0 p) ↔ fam α p) 
| (∀* p) h0 := 
  iff.trans 
    (fam_exv_dnf_zero p h0) 
    (fam_fa _ _).symm
| (∃* p)           h0 := fam_exv_dnf 0 _ h0
| (form.bin b p q) h0 := fam_exv_dnf 0 _ h0
| ⟪b, a⟫           h0 := fam_exv_dnf 0 _ h0


#exit

def mix (M N : model α) (k : nat) : model α := 
λ m, if m < k then M k else N k

def lit.holds (M N : model α) (k : nat) : lit → Prop 
| (tt, a) :=   (a.val (mix M N k) []).snd
| (ff, a) := ¬ (a.val (mix M N k) []).snd


#exit
