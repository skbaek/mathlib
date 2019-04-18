variables {α β : Type}

structure model (α : Type) :=
(inhab : α)
(funs  : nat → list α → α)
(rels  : nat → list α → Prop)

def model.default (α : Type) [inhabited α] : model α :=
let a := inhabited.default α in
{ inhab := a,
  funs  := λ _ _, a,
  rels  := λ _ _, false }
