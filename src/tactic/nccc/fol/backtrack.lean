universes u v
variables {α β : Type u}
variable {m : Type u → Type v}
variable [monad m]

def monad.concat : list (m (list α)) → m (list α) 
| []      := return []
| (f::fs) :=
  do l₁ ← f,
     l₂ ← monad.concat fs, 
     return (l₁ ++ l₂)

@[reducible] def backtrack (m : Type u → Type v) := m ∘ list 

namespace backtrack

open list
     
@[inline] protected def pure (a : α) : backtrack m α := (return [a] : m (list α))

@[inline] protected def bind (f : backtrack m α) 
  (g : α → backtrack m β) : backtrack m β :=
@bind m _ (list α) (list β) f (monad.concat ∘ (map g))

instance monad : monad (backtrack m) :=
{ pure := λ α, backtrack.pure, 
  bind := λ α β, backtrack.bind }

end backtrack