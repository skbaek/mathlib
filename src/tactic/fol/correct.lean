import .search .logic

variable {α : Type}

local notation `&` k   := term.fnc k
local notation a `&` b := term.app a b
local notation a `#` k := term.vpp a k

def goal : Type := cla × cla × mat
def ext_goal : Type := cla × cla × mat × mat

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

lemma mat.exv_of_holds_ext {M : model α} {v : vas α} {m x : mat} :
  is_ext m x → x.holds M v → (∃ w : nat → α, m.holds M w) :=
begin
  intros h1 h2,
  rcases h2 with ⟨c, h2, h3⟩,
  rcases (h1 _ h2) with ⟨d, h4, σ, h5⟩,
  refine ⟨v.subst M σ, d, h4, _⟩,
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

lemma rot_path_correct {p c : cla} {m : mat} (k : nat) :
  ext_valid α (p.rotate k, c, m) → ext_valid α (p, c, m) :=
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

lemma rot_mat_correct' {m : mat} (k : nat) :
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

lemma rot_cla_correct {p c d : cla} {m : mat} (k : nat) :
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

lemma rot_mat_correct {p c : cla} {m : mat} (k : nat) :
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
  apply mat.exv_of_holds_ext h2 h4,
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
  cases mat.exv_of_holds_ext h1 h3 with v h4,
  refine ⟨v, exists_mem_cons_of_exists h4⟩,
end

lemma red_correct {l n : lit} {p c : cla} {m : mat} :
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
