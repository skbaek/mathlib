import .mat

universe u
variable {α : Type}

local notation `&` k   := term.sym k
local notation a `&` b := term.app a b
local notation a `#` k := term.vpp a k


def goal : Type := cla × cla × mat

def cla.inst (c d : cla) : Prop :=
  ∃ σ : sub, c = cla.subst σ d

def mat.inst (m n : mat) : Prop :=
  ∀ c ∈ m, ∃ d ∈ n, ∃ k : nat, cla.inst c (list.rotate d k)

open list

def term.find_inst : sub → term → term → option sub
| σ (& k)   (& m)   := if k = m then some σ else none
| _ (& _)   (_ & _) := none
| _ (& _)   (_ # _) := none
| _ (_ & _) (& _)   := none
| σ (r & s) (t & u) :=
  term.find_inst σ r t >>=
  λ x, term.find_inst x s u
| σ (t & s) (r # k) :=
  do σ' ← term.find_inst σ t r,
     match σ'.get k with
     | none     := some ((k, s) :: σ')
     | (some u) := if s = u then some σ' else none
     end
| _ (_ # _) (& _)   := none
| _ (_ # _) (_ & _) := none
| σ (t # k) (s # m) :=
  do σ' ← term.find_inst σ t s,
     match σ'.get m with
     | none     := if k = m then some σ' else none
     | (some u) := none
     end

def cla.find_inst : sub → cla → cla → option sub
| σ [] []       := some σ
| _ [] (_ :: _) := none
| _ (_ :: _) [] := none
| σ ((b, t) :: C) ((c, s) :: D) :=
  if b = c
  then do σ' ← term.find_inst σ t s,
          cla.find_inst σ' C D
  else none

lemma fam_exv_of_fam_exv_inst {m n : mat} :
  mat.inst m n → m.fam_exv α → n.fam_exv α :=
begin
  rintros h0 h1 M,
  rcases h1 M with ⟨v, c, h1, h2⟩,
  rcases h0 c h1 with ⟨d, h3, k, σ, h5⟩,
  rw [h5, cla.holds_subst] at h2,
  refine ⟨vas.subst M v σ, d, h3, λ l h4, _⟩,
  apply h2, rw list.mem_rotate, exact h4
end

instance attempt.inst (m n : mat) : attempt (mat.inst m n) :=
begin
  apply @list.attempt_ball _ _ (λ c, _),
  apply @list.attempt_bex _ _ (λ d, _),
  apply @list.attempt_ex_of_list _ _ (λ k, _) (list.range d.length),
  cases (cla.find_inst [] c (rotate d k)) with σ,
  { apply attempt.unknown },
  by_cases h0 : (c = cla.subst σ (rotate d k)),
  { left, refine ⟨σ, h0⟩ },
  apply attempt.unknown
end

def attempt.repr (p : Prop) : attempt p → string
| (attempt.shown h) := "Success"
| _                 := "Fail"

instance attempt.has_repr (p : Prop) : has_repr (attempt p) := ⟨attempt.repr p⟩

def mat_size : mat → nat
| []       := 0
| (c :: m) := mat_size m + c.length + 1

def blocked : mat → cla → bool
| []              := λ _, ff
| ([] :: _)       := λ _, tt
| ((l :: c) :: m) := λ p,
  have mat_size (c :: m) < mat_size ((l :: c) :: m) := nat.lt_succ_self _,
  have mat_size m < mat_size ((l :: c) :: m) :=
  nat.lt_of_le_of_lt (nat.le_add_right _ c.length)
    (nat.lt_trans (nat.lt_succ_self _) (nat.lt_succ_self _)),
  if blocked (c :: m) p
  then if l.neg ∈ p
       then tt
       else blocked m (l :: p)
  else false
using_well_founded {
  dec_tac := tactic.assumption,
  rel_tac := λ _ _, `[exact ⟨measure mat_size, measure_wf mat_size⟩]
}

lemma holds_of_blocked (M : model α) (v : vas α) :
  ∀ m : mat, ∀ p : cla, (∀ l ∈ p, ¬ lit.holds M v l) →
  blocked m p = tt → m.holds M v
| []              _ _  h1 := by cases h1
| ([] :: _)       _ _  _  := ⟨_, or.inl rfl, list.ball_nil _⟩
| ((l :: c) :: m) p h0 h2 :=
  begin
    cases h3 : (blocked (c :: m) p),
    { simpa only [blocked, h3, bool.coe_sort_ff, if_false] using h2 },
    by_cases h4 : l.neg ∈ p,
    { have h5 : mat.holds M v (c :: m),
      { apply holds_of_blocked _ _ h0, rw h3,  },
      rcases h5 with ⟨d, h5 | h5, h6⟩,
      { refine ⟨_, or.inl rfl, λ x h7, _⟩,
        cases h7 with h7 h7,
        { apply classical.by_contradiction,
          have h8 := h0 _ h4,
          simpa only [lit.holds_neg, h7] using h8 },
        apply h6, rwa ← h5 at h7 },
        refine ⟨d, or.inr h5, h6⟩ },
    have h5 : blocked m (l :: p) = tt,
    { simpa only [blocked, h3, h4, bool.to_bool_false,
      if_true, bool.coe_sort_tt, if_false] using h2 },
    cases (classical.em (l.holds M v)) with h6 h6,
    { rcases holds_of_blocked (c :: m) p h0 h3 with ⟨d, h7 | h7, h8⟩,
      { refine ⟨_, or.inl rfl, _⟩, rw ← h7,
        apply (ball_cons (lit.holds M v) l d).elim_right ⟨h6, h8⟩ },
      refine ⟨d, or.inr h7, h8⟩ },
    have h7 : ∀ x ∈ (l :: p), ¬ lit.holds M v x,
    { apply (ball_cons (λ y, ¬ lit.holds M v y) l p).elim_right ⟨h6, h0⟩ },
    have h8 := holds_of_blocked m (l :: p) h7 h5,
    apply (bex_cons _ _ _).elim_right (or.inr h8),
  end

lemma valid_of_blocked {m : mat} :
  blocked m [] = tt → m.valid α :=
by { intros h0 M v,
     apply holds_of_blocked _ _ _ _ _ h0,
     apply @ball_nil _ (λ x, ¬ lit.holds M v x) }



#exit
  then blocked (c :: m) p
  else blocked m (l :: p)

#exit


#exit

#exit


#print axioms blocked

#exit
  have has_well_founded.r (⟨p, c :: m⟩ : psigma (λ _, mat)) ⟨p, (l :: c) :: m⟩,
  { right,
    apply (add_lt_add_iff_right m.sizeof).elim_right,
    apply (add_lt_add_iff_left 1).elim_right,
    apply lt_of_le_of_lt (nat.le_add_left _ (sizeof l)),


  } ,

#print axioms check
     #exit
lemma exv_of_holds_ext {M : model α} {v : vas α} {m x : mat} :
  is_ext m x → x.holds M v → (∃ w : nat → α, m.holds M w) :=
begin
  intros h1 h2,
  rcases h2 with ⟨c, h2, h3⟩,
  rcases (h1 _ h2) with ⟨d, h4, σ, h5⟩,
  refine ⟨v.subst M σ, d, h4, _⟩,
  rw [←cla.holds_subst, ←h5], exact h3
end


#exit
lemma cla.find_inst_is_some (c d : cla) :
  (cla.find_inst [] c d).is_some ↔ cla.inst c d :=  sorry

#exit
instance cla.decidable_inst (c d : cla) :
  decidable (cla.inst c d) :=
begin
  rw ← cla.find_inst_is_some,
  cases (cla.find_inst [] c d),
  { left, rintro ⟨_⟩ },
  right, simp only [bool.coe_sort_tt, option.is_some_some],
end




#exit
#exit
@list.decidable_ball _ _
  (λ x, @list.decidable_bex _ _ _ _) _


#exit

def ext_goal : Type := cla × cla × mat × mat


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

lemma exv_of_holds_ext {M : model α} {v : vas α} {m x : mat} :
  is_ext m x → x.holds M v → (∃ w : nat → α, m.holds M w) :=
begin
  intros h1 h2,
  rcases h2 with ⟨c, h2, h3⟩,
  rcases (h1 _ h2) with ⟨d, h4, σ, h5⟩,
  refine ⟨v.subst M σ, d, h4, _⟩,
  rw [←cla.holds_subst, ←h5], exact h3
end

lemma fam_exv_of_fam_exv_ext {m x : mat} :
  is_ext m x → x.fam_exv α → m.fam_exv α :=
by { rintros h0 h1 M,
     cases h1 M with v h1,
     apply exv_of_holds_ext h0 h1 }

lemma close_correct (p : cla) (m : mat) :
  ext_valid α (p, [], m) :=
by { refine ⟨[], λ _ h, by cases h, λ M v, _⟩,
     right, left, apply forall_mem_nil }

lemma rot_path_correct {p c : cla} {m : mat} (k : nat) :
  ext_valid α (p.rotate k, c, m) ↔ ext_valid α (p, c, m) :=
begin
  apply exists_iff_exists,
  intro M, unfold ext_holds,
  apply pred_mono_2 (iff.refl _),
  apply forall_iff_forall, intro M,
  apply forall_iff_forall, intro v,
  rw exists_mem_iff_exists_mem_of_seteq _
    (rotate_seteq_self k p)
end

lemma fam_exv_rotate_imp {m : mat} (k : nat) :
  mat.fam_exv α (m.rotate k) → mat.fam_exv α m :=
begin
  intros h0 M,
  rcases h0 M with ⟨v, c, h1, h2⟩,
  refine ⟨v, c, mem_rotate.elim_left h1, h2⟩
end

lemma exists_ext {c : cla} {m : mat} {k : nat} :
  ∀ x : mat, is_ext (c.rotate k :: m) x →
  ∃ y : mat, (is_ext (c :: m) y ∧
    ∀ M : model α, ∀ v : nat → α, x.holds M v ↔ y.holds M v)
| []     h0 := ⟨[], forall_mem_nil _, λ M v, iff.refl _⟩
| (d::x) h0 :=
  begin
    rcases exists_ext x (forall_mem_of_forall_mem_cons h0) with ⟨y, h1, h2⟩,
    rcases h0 d (or.inl rfl) with ⟨e, he1, σ, he2⟩,
    rw mem_cons_iff at he1, cases he1,
    { refine ⟨c.subst σ :: y,
        forall_mem_cons.elim_right
        ⟨⟨_, or.inl rfl, _, rfl⟩, h1⟩, λ M v, _⟩,
      have h3 : cla.holds M v d ↔ cla.holds M v (cla.subst σ c),
      { apply forall_mem_iff_forall_mem_of_seteq,
        rw [he2, he1],
        apply map_seteq_map_of_seteq (rotate_seteq_self _ _) },
      simp only [mat.holds_cons, h2 M v, h3] },
    refine ⟨d :: y, forall_mem_cons.elim_right
      ⟨⟨e, or.inr he1, _, he2⟩, h1⟩, λ M v, _⟩,
    simp only [mat.holds_cons, h2 M v]
  end

lemma rot_cla_correct_core {p c d : cla} {m : mat} (k : nat) :
  ext_valid α (p, c, d.rotate k :: m) →
  ext_valid α (p, c, d :: m) :=
begin
  intro h1,
  rcases h1 with ⟨x, h1, h2⟩,
  rcases exists_ext x h1 with ⟨y, h3, h4⟩,
  refine ⟨y, h3, λ M v, _⟩,
  rcases h2 M v with h5 | h5 | h5 | h5,
  { left, exact h5 },
  { right, left, exact h5 },
  { right, right, left,
    rw exists_mem_cons_iff at h5,
    cases h5,
    { refine ⟨d, or.inl rfl, _⟩,
      apply forall_mem_of_subset_of_forall_mem
        (λ x, mem_rotate.elim_right) h5 },
    apply exists_mem_cons_of_exists h5 },
  right, right, right,
  exact (h4 M v).elim_left h5
end

lemma rot_cla_correct (p c d : cla) (m : mat) (k : nat) :
  ext_valid α (p, c, d.rotate k :: m) ↔
  ext_valid α (p, c, d :: m) :=
begin
  constructor,
  { apply rot_cla_correct_core k },
  intro h0,
  rw ← rotate_rotate_eq_self k d at h0,
  apply rot_cla_correct_core _ h0
end

lemma rot_mat_correct_core {p c : cla} {m : mat} (k : nat) :
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

lemma rot_mat_correct (p c : cla) (m : mat) (k : nat) :
  ext_valid α (p, c, m.rotate k) ↔
  ext_valid α (p, c, m) :=
begin
  constructor,
  { apply rot_mat_correct_core k, },
  intro h0,
  rw ← rotate_rotate_eq_self k m at h0,
  apply rot_mat_correct_core _ h0
end

lemma start_copy_correct [inhabited α] {c : cla} {m : mat} (σ : sub) :
  ext_valid α ([], c.subst σ, c :: m) → mat.fam_exv α (c :: m) :=
begin
  intros h2 M,
  rcases h2 with ⟨x, h2, h3⟩,
  cases h3 M (λ _, default α) with h4 h4,
  { rcases h4 with ⟨_, h4, _⟩, cases h4 },
  cases h4,
  { refine ⟨vas.subst M (λ _, default α) σ, c, or.inl rfl, _⟩,
    rw [←cla.holds_subst], exact h4 },
  cases h4,
  refine ⟨(λ _, default α), h4⟩,
  apply exv_of_holds_ext h2 h4,
end

lemma start_correct [inhabited α] {c : cla} {m : mat} :
  ext_valid α ([], c, m) → mat.fam_exv α (c :: m) :=
begin
  intros h1 M,
  rcases h1 with ⟨x, h1, h2⟩,
  cases h2 M (λ _, default α) with h3 h3,
  { rcases h3 with ⟨_, hc, _⟩, cases hc },
  cases h3,
  { refine ⟨λ _, default α, c, or.inl rfl, h3⟩ },
  cases h3,
  { refine ⟨λ _, default α, exists_mem_cons_of_exists h3⟩ },
  cases exv_of_holds_ext h1 h3 with v h4,
  refine ⟨v, exists_mem_cons_of_exists h4⟩,
end

lemma red_correct {l : lit} {p c : cla} {m : mat} :
  l.neg ∈ p → ext_valid α (p, c, m) →
  ext_valid α (p, l :: c, m) :=
begin
  rintros h1 ⟨x, h2, h3⟩,
  refine ⟨x, h2, λ M v, _⟩,
  rcases (h3 M v) with h4 | ⟨h4 | h4⟩,
  { left, exact h4 },
  { cases classical.em (l.holds M v) with h5 h5,
    { right, left,
      rw forall_mem_cons,
      constructor; assumption },
    left, refine ⟨l.neg, h1, _⟩,
    rw lit.holds_neg, exact h5 },
  right, right, exact h4,
end

lemma ext_copy_correct {l n : lit} {p c d : cla} {m : mat} (σ : sub) :
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

lemma ext_correct {l n : lit} {p c d : cla} {m : mat} :
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

@[derive has_reflect]
inductive rule : Type
| red : nat → rule
| ext : nat → nat → sub → rule

def rule.repr : rule → string
| (rule.red k)     := "Red " ++ k.repr
| (rule.ext j i σ) := "Ext " ++ j.repr ++ " " ++ i.repr ++ " " ++ σ.repr

instance rule.has_repr : has_repr rule := ⟨rule.repr⟩

meta instance rule.has_to_format : has_to_format rule := ⟨λ x, rule.repr x⟩

@[reducible] def check.lt : (Σ' (x : list rule), list goal) →
  (Σ' (x : list rule), list goal) → Prop :=
psigma.lex (measure list.length)
  (λ _, measure list.length)

def check_core : list rule → list goal → Prop
| rs                 ((p, [], m) :: gs)     := check_core rs gs
| (rule.red i :: rs) ((p, l :: c, m) :: gs) :=
  match p.rotate i with
  | []        := false
  | (n :: p') :=
    if l.neg = n
    then check_core rs ((p, c, m) :: gs)
    else false
  end
| (rule.ext j i σ :: rs) ((p, l :: c, m) :: gs) :=
  match m.rotate j with
  | []        := false
  | (d :: m') :=
    match d.rotate i with
    | []        := false
    | (n :: d') :=
      if σ = []
      then if l.neg = n
           then check_core rs ((p, c, m) :: (l :: p, d', m') :: gs)
           else false
      else if l.neg = n.subst σ
           then check_core rs ((p, c, m) :: (l :: p, cla.subst σ d', m) :: gs)
           else false
    end
  end
| _  []                    := true
| [] ((_, _ :: _, _) :: _) := false
using_well_founded {
  dec_tac := `[ apply psigma.lex.left, apply nat.lt_succ_self ] <|>
             `[ apply psigma.lex.right, apply nat.lt_succ_self ],
   rel_tac := λ _ _,
  `[exact ⟨check.lt, psigma.lex_wf (measure_wf _) (λ _, measure_wf _)⟩]}

lemma check_core_imp :
  ∀ rs : list rule, ∀ gs : list goal,
  check_core rs gs → ∀ g ∈ gs, ext_valid α g
| rs ((p, [], m) :: gs) :=
  begin
    intro h0,
    replace h0 : check_core rs gs,
    { cases rs with r rs;
      [skip, `[cases r]];
      simpa [check_core] using h0 },
    intros g h2, cases h2,
    { rw h2, apply close_correct },
    exact check_core_imp rs gs h0 _ h2,
  end
| (rule.red i :: rs) ((p, l :: c, m) :: gs) :=
  begin
    intro h0,
    cases h1 : p.rotate i with n p',
    { simpa only [check_core, h1] using h0 },
    by_cases h2 : l.neg = n,
    { have h3 : check_core rs ((p, c, m) :: gs),
      { simpa only [check_core, h1, h2, true_and,
          eq_self_iff_true, if_false_right_eq_and] using h0 },
      have h4 := check_core_imp rs _ h3,
      rintros g (h5 | h5),
      { have h6 : l.neg ∈ p,
        { rw [← @mem_rotate _ _ _ i, h1, h2],
          exact or.inl rfl },
        rw h5, apply red_correct h6 (h4 _ (or.inl rfl)) },
      apply h4 _ (or.inr h5) },
      simpa only [check_core, false_and,
        if_false_right_eq_and, h1, h2] using h0
  end
| (rule.ext j i [] :: rs) ((p, l :: c, m) :: gs) :=
  begin
    intro h0,
    cases h1 : m.rotate j with d m',
    { simpa only [check_core, h1] using h0 },
    cases h2 : d.rotate i with n d',
    { simpa only [check_core, h1, h2] using h0 },
    by_cases h3 : l.neg = n,
    tactic.rotate 1,
    { simpa only [ check_core, h1, h2, h3, not_true,
      if_false_left_eq_and, eq_self_iff_true,
      if_false_right_eq_and, false_and ] using h0 },
    replace h0 : check_core rs ((p, c, m) :: (l :: p, d', m') :: gs),
    { simpa only [ check_core, h1, h2, h3, true_and, if_true,
      eq_self_iff_true, if_false_right_eq_and ] using h0 },
    intros g h4, cases h4,
    tactic.rotate 1,
    { apply check_core_imp rs _ h0 _ (or.inr $ or.inr h4) },
    rw [ h4, ← rot_mat_correct _ _ _ j, h1,
         ← rot_cla_correct _ _ _ _ i, h2 ],
    have h6 : ext_valid α (p, c, m),
    { exact check_core_imp rs _ h0 _ (or.inl rfl) },
    have h7 : ext_valid α (l :: p, d', m'),
    { apply check_core_imp rs _ h0, right, left, refl },
    apply ext_correct h3 _ h7,
    rw [← h2, rot_cla_correct, ← h1, rot_mat_correct],
    exact h6
end
| (rule.ext j i (s :: σ) :: rs) ((p, l :: c, m) :: gs) :=
  begin
    intro h0,
    cases h1 : m.rotate j with d m',
    { simpa only [check_core, h1] using h0 },
    cases h2 : d.rotate i with n d',
    { simpa only [check_core, h1, h2] using h0 },
    by_cases h3 : l.neg = n.subst (s :: σ),
    tactic.rotate 1,
    { simpa only [ check_core, h1, h2, h3, not_true,
      if_false_left_eq_and, eq_self_iff_true,
      if_false_right_eq_and, false_and ] using h0 },
    replace h0 : check_core rs ((p, c, m) :: (l :: p, cla.subst (s :: σ) d', m) :: gs),
    { simpa only [ check_core, h1, h2, h3, true_and, if_false,
      eq_self_iff_true, if_false_right_eq_and] using h0 },
    intros g h4, cases h4,
    tactic.rotate 1,
    { apply check_core_imp rs _ h0 _ (or.inr $ or.inr h4) },
    rw [ h4, ← rot_mat_correct _ _ _ j, h1,
         ← rot_cla_correct _ _ _ _ i, h2 ],
    have h6 : ext_valid α (p, c, m),
    { exact check_core_imp rs _ h0 _ (or.inl rfl) },
    have h7 : ext_valid α (l :: p, cla.subst (s :: σ) d', m),
    { apply check_core_imp rs _ h0, right, left, refl },
    apply ext_copy_correct _ h3;
    rw [← h2, rot_cla_correct, ← h1, rot_mat_correct];
    [ {exact h6}, {exact h7} ],
  end
| _  []                         :=
  by rintros h0 g ⟨h1⟩
| [] ((_, (b, t) :: _, _) :: _) :=
  by { intro h0, cases b;
       simpa only [check_core] using h0 }

def check (m : mat) : list rule → Prop
| (rule.ext j _ [] :: rs) :=
  match m.rotate j with
  | []        := false
  | (c :: m') := check_core rs [([], c, m')]
  end
| (rule.ext j _ (s :: σ) :: rs) :=
  match m.rotate j with
  | []        := false
  | (c :: m') := check_core rs [([], c.subst (s :: σ), m)]
  end
| _ := false

lemma check_imp (α : Type) [inhabited α] (m : mat) :
  ∀ rs : list rule, check m rs → mat.fam_exv α m
| (rule.ext j _ [] :: rs) h0 :=
  begin
    unfold check at h0,
    cases h1 : m.rotate j with c m'; rw h1 at h0,
    { cases h0 },
    apply fam_exv_rotate_imp j,
    rw h1, apply start_correct,
    apply check_core_imp rs _ h0 _ (or.inl rfl)
  end
| (rule.ext j _ (s :: σ) :: rs) h0 :=
  begin
    unfold check at h0,
    cases h1 : m.rotate j with c m'; rw h1 at h0,
    { cases h0 },
    simp only [check] at h0,
    have h2 := (@check_core_imp α rs _ h0 _ (or.inl rfl)),
    rw [← rot_mat_correct _ _ _ j, h1] at h2,
    apply fam_exv_rotate_imp j,
    rw h1,
    apply start_copy_correct (s :: σ) h2,
  end
| (rule.red _ :: _) h0 := by cases h0
| []                h0 := by cases h0
