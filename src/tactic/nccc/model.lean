variables {α β : Type}

structure model (α : Type) :=
(inhab : α)
(funcs : nat → list α → α)
(rels  : nat → list α → Prop)

--def func.default [inhabited α] (as : list α) : α :=
--@inhabited.default _ _
--
--def rel.default (as : list α) : Prop := false

def model.default (α : Type) [inhabited α] : model α :=
let a := inhabited.default α in
{ inhab := a,
  funcs := λ _ _, a,
  rels  := λ _ _, false }
