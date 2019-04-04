import data.buffer.parser

universes u 
variables {α : Type u}

lemma or_of_or {p q r s : Prop} :
  (p → q) → (r → s) → (p ∨ r) → (q ∨ s) :=
begin
  intros h1 h2 h3, cases h3, 
  { left, exact h1 h3 },
  { right, exact h2 h3 }
end

lemma and_of_and {p q r s : Prop} :
  (p → q) → (r → s) → (p ∧ r) → (q ∧ s) :=
λ h1 h2 h3, ⟨h1 h3.left, h2 h3.right⟩ 

lemma exists_of_exists {p q : α → Prop} :
  (∀ x, p x → q x) → (∃ x, p x) → ∃ x, q x :=
begin
  intros h1 h2, 
  cases h2 with a h2,
  refine ⟨a, h1 _ h2⟩, 
end

lemma exists_of_exists' (r : Prop) {p q : r → Prop} :
  (∀ x, p x → q x) → (∃ x, p x) → ∃ x, q x :=
begin
  intros h1 h2, 
  cases h2 with a h2,
  refine ⟨a, h1 _ h2⟩, 
end

lemma forall_of_forall {p q : α → Prop} :
  (∀ x, p x → q x) → (∀ x, p x) → ∀ x, q x :=
by { intros h1 h2 a, apply h1 _ (h2 a) }

lemma forall_of_forall' (r : Prop) {p q : r → Prop} :
  (∀ x, p x → q x) → (∀ x, p x) → ∀ x, q x :=
by { intros h1 h2 a, apply h1 _ (h2 a) }

open tactic

@[derive has_reflect]
inductive name_tree : Type 
| zero : name_tree 
| one  : name → name_tree → name_tree 
| two  : name_tree → name_tree → name_tree

namespace name_tree

meta def get_two : option name_tree → 
  tactic (option name_tree × option name_tree) 
| none               := return (none, none) 
| (some (two ms ns)) := return (some ms, some ns)
| _                  := failed

meta def get_one : option name_tree → 
  tactic (name × option name_tree)
| none              := 
  do m ← get_unused_name,
     return (m, none)
| (some (one m mt)) := return (m, some mt)
| _                 := failed

def repr : name_tree → string 
| zero        := "" 
| (one m zero)   := m.to_string 
| (one m ms)   := m.to_string ++ " " ++ ms.repr
| (two ms ns) := "⟨ " ++ ms.repr ++ " | " ++ ns.repr ++ " ⟩"

instance has_repr : has_repr name_tree := ⟨repr⟩ 

meta instance has_to_format : has_to_format name_tree := ⟨λ x, repr x⟩ 

end name_tree

open expr 

namespace tactic

meta def mk_lemma_or : expr → expr → tactic expr 
| `(%%px ∨ %%rx) `(%%qx ∨ %%sx) :=
  return (expr.mk_app `(@or_of_or) [px, qx, rx, sx])
| _ _ := failed

meta def mk_lemma_and : expr → expr → tactic expr 
| `(%%px ∧ %%rx) `(%%qx ∧ %%sx) :=
  return (expr.mk_app `(@and_of_and) [px, qx, rx, sx])
| _ _ := failed

meta def mk_lemma_ex : expr → expr → tactic expr 
| `(@Exists %%dx %%rx) `(@Exists _    %%sx) :=
  (to_expr ``(@exists_of_exists %%dx %%rx %%sx _)) <|>
  (to_expr ``(@exists_of_exists' %%dx %%rx %%sx _)) 
| _ _ := failed

meta def mk_lemma_fa : expr → expr → tactic expr 
| (pi n1 b1 dx x) (pi n2 b2 _  y) :=
  to_expr ``(@forall_of_forall %%dx %%(lam n1 b1 dx x) %%(lam n2 b2 dx y)) <|>
  to_expr ``(@forall_of_forall' %%dx %%(lam n1 b1 dx x) %%(lam n2 b2 dx y)) 
| _ _ := failed

meta def mono_con : option name_tree → tactic unit | nt := 
do `(%%lx → %%rx) ← target | skip,   
   px ← whnf lx, 
   qx ← whnf rx, 
   ( do (lt, rt) ← name_tree.get_two nt,
        seq_focus 
          ( (mk_lemma_or px qx <|> mk_lemma_and px qx) 
            >>= apply >> skip) 
          [mono_con lt, mono_con rt] ) <|>
   ( do (m, mt) ← name_tree.get_one nt,
        (mk_lemma_ex px qx <|> mk_lemma_fa px qx) >>= apply,
        intro m, mono_con mt ) <|>
   skip
    
namespace interactive

open lean
open lean.parser

open interactive 

meta def name_tree.parse_core : lean.parser name_tree := 
( do ms ← tk "⟨" *> name_tree.parse_core,
     ns ← tk "|" *> name_tree.parse_core <* tk "⟩",
     return (name_tree.two ms ns) ) <|>
( do m ← ident,
     ms ← name_tree.parse_core,
     return (name_tree.one m ms) ) <|>
return name_tree.zero

meta def name_tree.parse : lean.parser (option name_tree) := 
(some <$> (tk "with" *> name_tree.parse_core)) <|> (return none)

meta def mono_con (mt : parse name_tree.parse) : tactic unit :=
tactic.mono_con mt

end interactive

end tactic

example (p q r s1 s2 : Prop) (h : s1 → s2) :
  (p ∨ q ∧ (r ∨ s1)) → (p ∨ q ∧ (r ∨ s2)) :=
by {mono_con; try {exact id}, exact h}

example (α : Type) (p1 p2 q1 q2 : Prop) (r1 r2 s1 s2 : α → Prop)
  (h1 : p1 → p2) (h2 : q1 → q2) 
  (h3 : ∀ x, r1 x → r2 x) (h4 : ∀ x, s1 x → s2 x) : 
  (∀ x : α, r1 x ∨ ∃ y : α, (p1 ∨ s1 y ∧ q1)) →   
  (∀ x : α, r2 x ∨ ∃ y : α, (p2 ∨ s2 y ∧ q2)) := 
begin
  mono_con with x ⟨ | y ⟨ | ⟨ | ⟩ ⟩ ⟩; try {assumption},
  apply h3, apply h4
end