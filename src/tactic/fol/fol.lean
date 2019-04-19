import .model .sol.form

universe u 

variables {α β : Type u}

@[derive has_reflect]
inductive atom : Type
| sym : nat  → atom
| app : atom → atom → atom
| vpp : atom → nat  → atom

local notation `&` k   := atom.sym k
local notation a `&` b := atom.app a b
local notation a `#` k := atom.vpp a k

namespace atom 

def val (M : model α) (v : nat → α) : atom → value α
| (& k)   := M k
| (a & b) := a.val ∘ list.cons (b.val []).fst
| (a # k) := a.val ∘ list.cons (v k)

def lit : Type := bool × atom 

def cla : Type := list lit

def mat : Type := list cla

def symbolize (k : nat) : term → atom
| (term.var m)                := & m
| (term.app t (term.var m))   := 
  if m < k 
  then (symbolize t) # m
  else (symbolize t) & (& m)
| (term.app t (term.app s r)) := 
  (symbolize t) & (symbolize $ term.app s r)

#exit

def DNF_QF : nat → form → mat 
| k ⟪b, a⟫ := [[(b, a)]] 

def DNF_E : nat → form → mat 
| k (form.qua tt p) := DNF_E k.succ p
| k p               := DNF_QF k p 

def DNF : form → mat 
| (form.qua ff p) := DNF p
| p               := DNF_E 0 p 








end atom


end fol