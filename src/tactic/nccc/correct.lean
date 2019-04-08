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

lemma close_correct (p : cla) (m : mat) :
  ext_valid α (p, [], m) :=
begin
  refine ⟨[], λ _ h, by cases h, λ M v, _⟩,
  right, left,
  intros _ h,
  cases h,
end

lemma rot_path_correct (p c : cla) (m : mat) (k : nat) :
  ext_valid α (p.rotate k, c, m) →
  ext_valid α (p, c, m) :=
begin
  intro h1,
  rcases h1 with ⟨x, h1, h2⟩,
  refine ⟨x, h1, _⟩,
  intros M v,
  rcases (h2 M v) with ⟨l, h3, h4⟩ | h3,
  { left, refine ⟨l, _, h4⟩,
    simpa [mem_rotate] using h3 },
  right, exact h3,
end

lemma rot_mat_correct (p c : cla) (m : mat) (k : nat) :
  ext_valid α (p, c, m.rotate k) →
  ext_valid α (p, c, m) :=
begin
  intro h1,
  rcases h1 with ⟨x, h1, h2⟩,
  refine ⟨x, λ d hd, _, _⟩,
  { rcases h1 d hd with ⟨e, he1, σ, he2⟩,
    refine ⟨e, _, σ, he2⟩,
    simpa [mem_rotate] using he1 },
  intros M v,
  rcases (h2 M v) with h3 | h3 | ⟨d, hd1, hd2⟩ | h3,
  { left, exact h3 },
  { right, left, exact h3 },
  { right, right, left,
    refine ⟨d, _, hd2⟩,
    simpa [mem_rotate] using hd1 },
  right, right, right,
  exact h3,
end

lemma start_copy_correct (c : cla) (m : mat) (σ : sub) :
  ext_valid α ([], c.subst σ, c :: m) → mat.valsat α (c :: m) :=
begin
  intros h2 M,
  rcases h2 with ⟨x, h2, h3⟩,
  cases h3 M (λ _, M.inhab) with h4 h4,
  { rcases h4 with ⟨_, h4, _⟩, cases h4 },
  cases h4,
  { refine ⟨val.subst M (λ _, M.inhab) σ, c, or.inl rfl, _⟩,
    rw [←cla.holds_subst], exact h4 },
  cases h4,
  refine ⟨(λ _, M.inhab), h4⟩,
  apply mat.exv_of_holds_ext h2 h4,
end

lemma start_correct (c : cla) (m : mat) :
  ext_valid α ([], c, m) → mat.valsat α (c :: m) :=
begin
  intros h1 M,
  rcases h1 with ⟨x, h1, h2⟩,
  cases h2 M (λ _, M.inhab) with h3 h3,
  { rcases h3 with ⟨_, hc, _⟩, cases hc },
  cases h3,
  { refine ⟨λ _, M.inhab, c, or.inl rfl, h3⟩ },
  cases h3,
  { refine ⟨λ _, M.inhab, exists_mem_cons_of_exists h3⟩ },
  cases mat.exv_of_holds_ext h1 h3 with v h4,
  refine ⟨v, exists_mem_cons_of_exists h4⟩,
end

lemma red_correct (l n : lit) (p c : cla) (m : mat) :
  l.neg = n → ext_valid α (n :: p, c, m) → ext_valid α (n :: p, l :: c, m) :=
begin
  intros h1 h2,
  rcases h2 with ⟨x, h2, h3⟩,
  refine ⟨x, h2, λ M v, _⟩,
  cases h3 M v with h4 h4,
  { left, exact h4 },
  cases h4,
  { cases classical.em (l.holds M v) with h5 h5,
    { right, left,
      rw forall_mem_cons,
      constructor; assumption },
    left,
    refine ⟨n, or.inl rfl, _⟩,
    rw [← h1, lit.holds_neg],
    exact h5 },
  right, right,
  exact h4,
end

lemma ext_copy_correct (l n : lit) (p c d : cla) (m : mat) (σ : sub) :
  l.neg = n.subst σ →
  ext_valid α (p, c, (n :: d) :: m) →
  ext_valid α (l :: p, d.subst σ, (n :: d) :: m) →
  ext_valid α (p, l :: c, (n :: d) :: m) :=
begin
  intros h3 h4 h5,
  rcases h4 with ⟨x, h4, h6⟩,
  rcases h5 with ⟨y, h5, h7⟩,
  refine ⟨cla.subst σ (n :: d) :: (x ++ y), λ e he, _, _⟩,
  { rw mem_cons_iff at he,
    cases he,
    { refine ⟨n :: d, or.inl rfl, σ, he⟩ },
    rw mem_append at he,
    cases he,
    exact (h4 e he),
    exact (h5 e he) },
  intros M v,
  cases (h6 M v) with h6 h6,
  { left, exact h6 },
  cases h6 with h6 h6,
  { cases classical.em (l.holds M v) with hl hl,
    { right, left, rw forall_mem_cons,
      constructor; assumption },
    cases (h7 M v) with h7 h7,
    { rcases h7 with ⟨k, hk1, hk2⟩,
      cases hk1,
      { subst hk1, exfalso, exact hl hk2 },
      left, refine ⟨k, hk1, hk2⟩ },
    cases h7 with h7 h7,
    { right, right, right,
      refine ⟨cla.subst σ (n :: d), or.inl rfl, _⟩,
      apply forall_mem_cons.elim_right ⟨_, h7⟩,
      rw [← h3, lit.holds_neg],
      exact hl },
    cases h7 with h7 h7,
    { right, right, left,
      exact h7 },
    right, right, right,
    apply exists_mem_cons_of_exists,
    rw exists_mem_append_iff,
    right, exact h7 },
  cases h6 with h6 h6,
  { right, right, left,
    exact h6 },
  right, right, right,
  apply exists_mem_cons_of_exists,
  rw exists_mem_append_iff,
  left, exact h6
end

lemma ext_correct (l n : lit) (p c d : cla) (m : mat) :
  l.neg = n →
  ext_valid α (p, c, (n :: d) :: m) →
  ext_valid α (l :: p, d, m) →
  ext_valid α (p, l :: c, (n :: d) :: m) :=
begin
  intros h3 h4 h5,
  rcases h4 with ⟨x, h4, h6⟩,
  rcases h5 with ⟨y, h5, h7⟩,
  refine ⟨x ++ y, λ e he, _, _⟩,
  { rw mem_append at he,
    cases he,
    exact (h4 e he),
    rcases (h5 e he) with ⟨f, hf1, σ, hf2⟩,
    refine ⟨f, or.inr hf1, σ, hf2⟩ },
  intros M v,
  cases (h6 M v) with h6 h6,
  { left, exact h6 },
  cases h6 with h6 h6,
  { cases classical.em (l.holds M v) with hl hl,
    { right, left, rw forall_mem_cons,
      constructor; assumption },
    cases (h7 M v) with h7 h7,
    { rcases h7 with ⟨k, hk1, hk2⟩,
      cases hk1,
      { subst hk1, exfalso, exact hl hk2 },
      left, refine ⟨k, hk1, hk2⟩ },
    cases h7 with h7 h7,
    { right, right, left,
      refine ⟨n :: d, or.inl rfl, _⟩,
      apply forall_mem_cons.elim_right ⟨_, h7⟩,
      rw [← h3, lit.holds_neg],
      exact hl },
    cases h7 with h7 h7,
    { right, right, left,
      apply exists_mem_cons_of_exists h7 },
    right, right, right,
    rw exists_mem_append_iff,
    right, exact h7 },
  cases h6 with h6 h6,
  { right, right, left,
    exact h6 },
  right, right, right,
  rw exists_mem_append_iff,
  left, exact h6
end


#exit





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


lemma red_correct (l : lit) (c : cla) (m : mat) (p : cla) :
  l.neg ∈ p → ext_valid α (p, c, m) → ext_valid α (p, l :: c, m) :=
begin
  intro h1,
  rintro ⟨x, h2, h3⟩,
  refine ⟨x, h2, _⟩,
  intros M v,
  cases (h3 M v) with h4 h4,
  { left, exact h4 },
  cases h4,
  { cases classical.em (l.holds M v) with h5 h5,
    { right, left, rw forall_mem_cons,
      constructor; assumption },
    { left, refine ⟨l.neg, h1, _⟩,
      rw lit.holds_neg, exact h5 } },
  right, right, exact h4 ,
end

lemma ext_some_correct (p : cla) (l : lit) (c : cla) (m : mat) (σ : sub)
  (i j : nat) (h1 : j < m.length) (h2 : i < (m.nth_le j h1).length) :
  let d := (m.nth_le j h1).subst σ in
  let n := d.nth_le i (by simpa only [d, cla.subst, length_map] using h2) in
  l.neg = n →
  ext_valid α (p, c, m) →
  ext_valid α (l :: p, d.except i, m) →
  ext_valid α (p, l :: c, m) :=
begin
  intros d n h3 h4 h5,
  rcases h4 with ⟨x, h4, h6⟩,
  rcases h5 with ⟨y, h5, h7⟩,
  refine ⟨d :: (x ++ y), λ e he, _, _⟩,
  { rw mem_cons_iff at he,
    cases he,
    { refine ⟨nth_le m j h1, nth_le_mem _ _ _, σ, _⟩,
      rw he },
    rw mem_append at he,
    cases he,
    exact (h4 e he),
    exact (h5 e he) },
  intros M v,
  cases (h6 M v) with h6 h6,
  { left, exact h6 },
  cases h6 with h6 h6,
  { cases classical.em (l.holds M v) with hl hl,
    { right, left, rw forall_mem_cons,
      constructor; assumption },
    cases (h7 M v) with h7 h7,
    { rcases h7 with ⟨k, hk1, hk2⟩,
      cases hk1,
      { subst hk1, exfalso, exact hl hk2 },
      left, refine ⟨k, hk1, hk2⟩ },
    cases h7 with h7 h7,
    { right, right, right,
      refine ⟨d, or.inl rfl, _⟩,  }



   }


end


#exit

| ext' {M : mat} {C P : cla} {L : lit} {σ : sub} {i j : nat}
  {h1 : j < M.length} {h2 : i < (M.nth_le j h1).length} :
  let D := (M.nth_le j h1).subst σ in
  let N := ((M.nth_le j h1).nth_le i h2).subst σ in
  proof C M P →
  N = L.neg →
  proof (D.except i) M (L::P) →
  proof (L::C) M P
lemma ext_none_correct (l : lit) (c : cla) (m : mat) (p : cla)
  (i j : nat) (h1 : j < m.length) (h2 : i < (m.nth_le j h1).length) :
  l.neg = (m.nth_le j h1).nth_le i h2 →
  ext_valid α (p, c, m) →
  ext_valid α (l :: p, (m.nth_le j h1).except i, m.except j) →
  ext_valid α (p, l :: c, m) :=
begin
  intros h3 h4 h5,
  rcases h4 with ⟨x, h4, h6⟩,
  rcases h5 with ⟨y, h5, h7⟩,
  refine ⟨x ++ y, ⟨λ d hd, _, _⟩⟩,
  { rw mem_append at hd,
    cases hd,
    exact (h4 d hd),
    rcases (h5 d hd) with ⟨e, h8, h9⟩,
    refine ⟨e, except_subset_self h8, h9⟩ },
  intros M v,

end

#exit

| ext {M : mat} {C P : cla} {L : lit} (i j : nat)
  {h1 : j < M.length} {h2 : i < (M.nth_le j h1).length} :
  let D := M.nth_le j h1 in
  let N := D.nth_le i h2 in
  proof C M P →
  N = L.neg →
  proof (D.except i) (M.except j) (L::P) →
  proof (L::C) M P


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
