import .term

variable {α : Type}

@[derive has_reflect]
structure lit :=
(sign : bool)
(idx : nat)
(args : list term)

namespace lit

def holds (M : model α) (v : nat → α) : lit → Prop
| ⟨tt, k, ts⟩  :=    M.rels k (ts.map (term.val M v))
| ⟨ff, k, ts⟩  :=  ¬ M.rels k (ts.map (term.val M v))

def repr : lit → string
| ⟨s, k, ts⟩ :=
  (if s then "" else "¬") ++ "P" ++ k.to_subs ++
  (list.foldl (λ s1 s2, s1 ++ " " ++ s2) "" (ts.map term.repr))

instance has_repr : has_repr lit := ⟨repr⟩

meta instance has_to_format : has_to_format lit := ⟨λ x, repr x⟩


end lit
