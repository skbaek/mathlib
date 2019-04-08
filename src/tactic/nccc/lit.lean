--import .term

variable {α : Type}


def lit : Type :=
(sign : bool)
(idx : nat)
(args : list term)


#exit
namespace lit

def neg : lit → lit
| ⟨b, k, ts⟩ := ⟨bnot b, k, ts⟩

def holds (M : model α) (v : nat → α) : lit → Prop
| ⟨tt, k, ts⟩  :=    M.rels k (ts.map (term.value M v))
| ⟨ff, k, ts⟩  :=  ¬ M.rels k (ts.map (term.value M v))

lemma holds_neg (M : model α) (v : nat → α) (l : lit) :
  holds M v l.neg ↔ ¬ holds M v l :=
by { cases l with b; cases b;
     simp only [bnot, neg, holds, list.map, classical.not_not] }

def repr : lit → string
| ⟨s, k, ts⟩ :=
  (if s then "" else "¬") ++ "P" ++ k.to_subs ++
  (list.foldl (λ s1 s2, s1 ++ " " ++ s2) "" (ts.map term.repr))

instance has_repr : has_repr lit := ⟨repr⟩

meta instance has_to_format : has_to_format lit := ⟨λ x, repr x⟩

def vdxs : lit → list nat
| ⟨_, _, ts⟩ := ⋃ (ts.map term.vdxs)

def subst (σ : sub) : lit → lit
| ⟨b, m, ts⟩ := ⟨b, m, ts.map (term.subst σ)⟩

lemma holds_subst (M : model α) (v : nat → α) (σ : sub) (l : lit) :
  holds M v (l.subst σ) ↔ holds M (val.subst M v σ) l :=
begin
  cases l with b k ts, cases b;
  simp only [holds, subst, val.subst,
    list.map_map, term.value_comp_subst],
end


end lit
