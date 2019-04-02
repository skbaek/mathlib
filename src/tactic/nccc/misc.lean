variables {α : Type}

def update (m : nat) (a : α) (v : nat → α) : nat → α
| n := if n = m then a else v n

local notation v `{` m `↦` a `}` := update m a v

def update_zero (a : α) (f : nat → α) : nat → α
| 0     := a
| (k+1) := f k

meta def list_reflect [has_reflect α] (l : list α) : list expr :=
l.map (λ x, `(x).to_expr)

local notation f `₀↦` a := update_zero a f
