variables {α : Type}

def update (m : nat) (a : α) (v : nat → α) : nat → α
| n := if n = m then a else v n

local notation v `{` m `↦` a `}` := update m a v

def update_zero (a : α) (f : nat → α) : nat → α
| 0     := a
| (k+1) := f k

local notation f `₀↦` a := update_zero a f
