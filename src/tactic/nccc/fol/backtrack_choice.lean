universes u v w x
variables {α : Type u}
variables {β : Type u}
variable {m : Type u → Type v}
variables [monad m] [alternative m]

inductive tree (α : Type u)
| leaf : α → tree
| fork : tree → tree → tree

open tree 

def tree.map {γ : Type w} {δ : Type x} (f : γ → δ) : tree γ → tree δ 
| (leaf a)   := leaf (f a)
| (fork t s) := fork t.map s.map 

def flatten : tree (m (tree α)) → m (tree α) 
| (leaf f)   := f
| (fork f g) := 
  do c ← flatten f, 
     d ← flatten g, 
     return (fork c d)

@[reducible] def backtrack (m : Type u → Type v) := m ∘ tree 

namespace backtrack
     
@[inline] protected def pure (a : α) : backtrack m α := 
(return (leaf a) : m (tree α))

@[inline] protected def bind (f : backtrack m α) 
  (g : α → backtrack m β) : backtrack m β :=
@bind m _ (tree α) (tree β) f (flatten ∘ (tree.map g))

instance monad : monad (backtrack m) :=
{ pure := λ α, backtrack.pure, 
  bind := λ α β, backtrack.bind }

end backtrack