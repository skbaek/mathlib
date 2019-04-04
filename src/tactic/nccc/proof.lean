import .search .logic tactic.mono_con

variable {α : Type}

local notation `⅋` k   := term.fnc k
local notation t `&` s := term.tpp t s
local notation t `#` k := term.vpp t k

def goal : Type := cla × cla × mat
def ext_goal : Type := cla × cla × mat × mat

namespace goal

def is_ext (m x : mat) : Prop :=
∀ c ∈ x, ∃ d ∈ m, ∃ σ : sub, c = cla.subst σ d

lemma is_ext_of_subset_of_is_ext {m n x : mat} : 
  m ⊆ n → is_ext m x → is_ext n x :=
begin
  intros h1 h2 c h3,
  rcases (h2 _ h3) with ⟨d, h4, σ, h5⟩, 
  refine ⟨d, h1 h4, σ, h5⟩,
end

def ext_holds (M : model α) (v : nat → α) : ext_goal → Prop 
| (p, c, m, x) := 
  (∃ l ∈ p, lit.holds M v l) ∨ 
  (∀ l ∈ c, lit.holds M v l) ∨ 
  (∃ d ∈ m, cla.holds M v d) ∨ 
  (∃ d ∈ x, cla.holds M v d) 

def ext_valid (α : Type) : goal → Prop 
| (p, c, m) := 
  ∃ x : mat, is_ext m x ∧ 
    (∀ M : model α, ∀ v : nat → α, ext_holds M v (p, c, m, x))

open list

lemma mat.exv_of_holds_ext {M : model α} {v : nat → α} {m x : mat} :
  is_ext m x → x.holds M v → (∃ w : nat → α, m.holds M w) := 
begin
  intros h1 h2, 
  rcases h2 with ⟨c, h2, h3⟩,  
  rcases (h1 _ h2) with ⟨d, h4, σ, h5⟩,
  refine ⟨val.subst M v σ, d, h4, _⟩, 
  rw [←cla.holds_subst, ←h5], exact h3
end

lemma start_none_correct (m : mat) (j : nat) (h1 : j < m.length) :
  ext_valid α ([], m.nth_le j h1, m.except j) → m.valsat α := 
begin
  intros h2 M, 
  rcases h2 with ⟨x, h2, h3⟩, 
  cases h3 M (λ _, M.inhab) with h4 h4, 
  { rcases h4 with ⟨_, h4, _⟩, cases h4 },
  cases h4, 
  refine ⟨(λ _, M.inhab), _, nth_le_mem _ _ _, h4⟩,
  cases h4,
  { rcases h4 with ⟨d, h5, h6⟩, 
    refine ⟨(λ _, M.inhab), _, except_subset_self h5, h6⟩ },
  apply mat.exv_of_holds_ext 
    (is_ext_of_subset_of_is_ext except_subset_self h2) h4,
end

lemma start_some_correct (m : mat) (j : nat) (h1 : j < m.length) (σ : sub) :
  ext_valid α ([], (m.nth_le j h1).subst σ, m) → m.valsat α := 
begin
  intros h2 M, 
  rcases h2 with ⟨x, h2, h3⟩, 
  cases h3 M (λ _, M.inhab) with h4 h4, 
  { rcases h4 with ⟨_, h4, _⟩, cases h4 },
  cases h4,
  { refine ⟨val.subst M (λ _, M.inhab) σ, 
    m.nth_le j h1, nth_le_mem _ _ _, _⟩, 
    rw [←cla.holds_subst], exact h4 },
  cases h4, 
  { rcases h4 with ⟨d, h5, h6⟩, 
    refine ⟨(λ _, M.inhab), _, h5, h6⟩ },
  apply mat.exv_of_holds_ext h2 h4,
end

lemma red_correct (l : lit) (c : cla) (m : mat) (p : cla) :
  l.neg ∈ p → ext_valid α (p, c, m) → ext_valid α (p, l :: c, m) := 
begin
  intro h1, 
  mono_con with x ⟨ | M v ⟩,  
  exact id, simp only,
  intro h2, cases h2, 
  { left, exact h2 },
  { cases h2 with h2 h3,
    { cases classical.em (l.holds M v) with h4 h4,
      { right, left, rw forall_mem_cons,
        constructor; assumption },
      { left, refine ⟨l.neg, h1, _⟩, 
        rw lit.holds_neg, exact h4 } },
    right, right, exact h3 }
end

#exit
def holds (M : model α) (v : nat → α) : goal → Prop 
| (c, m, p) := (cla.holds M v c ∨ ∃ d ∈ m, cla.holds M v d) ∧ (∀ l ∈ p, ¬ lit.holds M v l)

def valsat (α : Type) (g : goal) : Prop :=
∀ M : model α, ∃ v : nat → α, (holds M v g)

end goal

open list

#check tactic.interactive.rcades
lemma start_none_correct (m : mat) (j : nat) (h1 : j < m.length) :
  goal.valsat α (m.nth_le j h1, m.except j, []) → m.valsat α := 
begin
  intros h2 M, 
  rcases (h2 M) with ⟨v, h3, h4⟩, 
  refine ⟨v, _⟩, cases h3,
  { refine ⟨_, nth_le_mem _ _ _, h3⟩ },
  { rcases h3 with ⟨c, h5, h6⟩,
    refine ⟨c, mem_of_mem_except h5, h6⟩ }
end

lemma start_some_correct (m : mat) (j : nat) (h1 : j < m.length) (σ : sub) :
  goal.valsat α ((m.nth_le j h1).subst σ, m, []) → m.valsat α := 
begin
  intros h2 M, 
  rcases (h2 M) with ⟨v, h3, h4⟩, 
  cases h3,
  refine ⟨val.subst M v σ, m.nth_le j h1, 
    nth_le_mem _ _ _, cla.holds_subst.elim_left h3⟩,
  refine ⟨v, h3⟩,
end

lemma red_correct (l : lit) (c : cla) (m : mat) (p : cla) :
  l.neg ∈ p → goal.valsat α (c, m, p) → goal.valsat α (l :: c, m, p) := 
begin
  intros h1 h2 M,
  rcases h2 M with ⟨v, h3, h4⟩,
  refine ⟨v, _, h4⟩,
  cases h3 with h5 h6,
  { left, 
    apply list.forall_mem_cons.elim_right ⟨ _, h5⟩,
    apply classical.not_not.elim_left,
    rw ← lit.holds_neg,
    exact h4 _ h1 },
  { right, exact h6 }
end

lemma ext_none_correct (l : lit) (c : cla) (m : mat) (p : cla) 
  (i j : nat) (h1 : j < m.length) (h2 : i < (m.nth_le j h1).length) : 
  l.neg = (m.nth_le j h1).nth_le i h2 → 
  goal.valsat α (c, m, p) → 
  goal.valsat α ((m.nth_le j h1).except i, m.except j, l :: p) → 
  goal.valsat α (l :: c, m, p) :=  sorry



#exit


inductive rule : Type
| start : nat → option sub → rule 
| red   : rule
| ext   : nat → nat → option sub → rule 

def goal : Type := option cla × mat × cla

open rule 

def check : list rule → list goal → bool 
| (r :: rs) ((some [], _, _) :: gs) := check rs gs
| (start j none :: rs) [(none, M, [])] :=  
  if h : j < M.length
  then check rs [((M.nth_le j h), (M.except j), [])] 
  else ff
| (start j (some σ) :: rs) [(none, M, [])] :=  
  if h : j < M.length
  then check rs [((M.nth_le j h).subst σ, M, [])] 
  else ff
| (red :: rs) ((some (L :: C), M, P) :: gs) := 
  if L.neg ∈ P
  then check rs ((some C, M, P) :: gs) 
  else ff
| (ext j i none :: rs) ((some (L :: C), M, P) :: gs) :=  
  if h1 : j < M.length 
  then if h2 : i < (M.nth_le j h1).length
       then let D := M.nth_le j h1 in 
            let N := D.nth_le i h2 in
            (N = L.neg) && 
              check rs ((C, M, P) :: (D.except i, M.except j, L :: P) :: gs)
       else ff
  else ff
| (ext j i (some σ) :: rs) ((some (L :: C), M, P) :: gs) :=  
  if h1 : j < M.length 
  then if h2 : i < (M.nth_le j h1).length
       then let D := M.nth_le j h1 in 
            let Dσ := D.subst σ in
            let Nσ := (D.nth_le i h2).subst σ  in
            (Nσ = L.neg) && 
              check rs ((C, M, P) :: (D.except i, M, L :: P) :: gs)
       else ff
  else ff

#print axioms check


#exit


| (rule.start j (some σx) :: rs) none M [] := 
  do ⟨_, h⟩ ← get_lt_proof j M.length,
     σ ← σx.inst,
     (rs', π) ← of_rules rs ((M.nth_le j h).subst σ) M [],
     return (rs', proof.start' π)


#exit
inductive proof : option cla → mat → cla → Type
| start {M : mat} {j : nat} {h : j < M.length} :
  proof (M.nth_le j h) (M.except j) [] → 
  proof none M []
| start' {M : mat} {j : nat} {h : j < M.length} {σ : sub} :
  proof ((M.nth_le j h).subst σ) M [] → 
  proof none M []
| red {M : mat} {C P : cla} {L : lit} :
  L.neg ∈ P → proof C M P → proof (L::C) M P
| ext {M : mat} {C P : cla} {L : lit} (i j : nat) 
  {h1 : j < M.length} {h2 : i < (M.nth_le j h1).length} :
  let D := M.nth_le j h1 in
  let N := D.nth_le i h2 in
  proof C M P → 
  N = L.neg → 
  proof (D.except i) (M.except j) (L::P) →
  proof (L::C) M P
| ext' {M : mat} {C P : cla} {L : lit} {σ : sub} {i j : nat}
  {h1 : j < M.length} {h2 : i < (M.nth_le j h1).length} :
  let D := (M.nth_le j h1).subst σ in
  let N := ((M.nth_le j h1).nth_le i h2).subst σ in
  proof C M P → 
  N = L.neg → 
  proof (D.except i) M (L::P) →
  proof (L::C) M P
| axm {M : mat} {P : cla} : proof (some []) M P

open tactic

meta def get_lt_proof (m n : nat) : tactic (@subtype unit (λ _, m < n)) := 
if h : m < n then return (subtype.mk () h) else failed

meta def get_proof (P : Prop) [decidable P] : tactic (@subtype unit (λ _, P)) := 
if h : P then return (subtype.mk () h) else failed

meta def subx.inst_aux (ktx : nat × expr) : tactic (nat × term) :=
do t ← eval_expr term ktx.snd, return (ktx.fst, t)

meta def subx.inst (σx : subx) : tactic sub :=
monad.mapm subx.inst_aux σx 

meta def of_rules : list rule → ∀ C : option cla, 
  ∀ M : mat, ∀ P : cla, tactic (list rule × proof C M P)
| (rule.start j none :: rs) none M [] := 
  do ⟨_, h⟩ ← get_lt_proof j M.length,
     (rs', π) ← of_rules rs (M.nth_le j h) (M.except j) [],
     return (rs', proof.start π) 
| (rule.start j (some σx) :: rs) none M [] := 
  do ⟨_, h⟩ ← get_lt_proof j M.length,
     σ ← σx.inst,
     (rs', π) ← of_rules rs ((M.nth_le j h).subst σ) M [],
     return (rs', proof.start' π)
| (rule.red :: rs) (some (L::C)) M P := 
  do ⟨_, h⟩ ← get_proof (L.neg ∈ P),
     (rs', π) ← of_rules rs (some C) M P,
     return (rs', proof.red h π)



#exit
  if h : j < M.length
  then do (rs', π) ← of_rules rs (M.nth_le j h) (M.except j) [],
          return (rs', proof.start π) 
  else failed

#exit
--lemma valsat_goal_of_proof {α : Type} (M : mat)  :
--  proof none M [] → M.valsat α := sorry

lemma valsat_of_proof {α : Type} (M : mat) :
  proof none M [] → M.valsat α := sorry
  
