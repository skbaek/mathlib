import data.list.basic

universe u

variables {α β : Type}

variables {as as1 as2 : list α}

namespace list

lemma map_eq_map_of_forall_mem_eq {f g : α → β} :
∀ {as}, (∀ a ∈ as, f a = g a) → map f as = map g as
| [] h1 := rfl
| (a::as) h1 :=
  begin
    simp only [map], constructor,
    apply h1 _ (or.inl rfl),
    apply map_eq_map_of_forall_mem_eq,
    apply forall_mem_of_forall_mem_cons h1
  end

def gen_union [decidable_eq α] (ll : list (list α)) : list α :=
foldl list.union [] ll

notation `⋃` := gen_union

def max [has_zero α] [decidable_linear_order α] : list α → α
| []      := 0
| (a::as) := _root_.max a as.max

def except : nat → list α → list α
| 0     []      := []
| (k+1) []      := []
| 0     (a::as) := as
| (k+1) (a::as) := a :: (except k as)

lemma except_subset_self :
  ∀ {k : nat} {as : list α}, as.except k ⊆ as
| 0     []      a h := by cases h
| (k+1) []      a h := by cases h
| 0     (b::as) a h := or.inr h
| (k+1) (b::as) a h :=
  by { cases h, left, exact h,
       right, apply except_subset_self h }

lemma exists_mem_append_iff {α : Type u} (p : α → Prop) (l1 l2 : list α) :
  (∃ x ∈ (l1 ++ l2), p x) ↔ (∃ x ∈ l1, p x) ∨ (∃ x ∈ l2, p x) :=
begin
  constructor; intro h1,
  { rcases h1 with ⟨a, h2, h3⟩,
    rw mem_append at h2, cases h2,
    { left, refine ⟨a, h2, h3⟩ },
    right, refine ⟨a, h2, h3⟩ },
  cases h1;
  rcases h1 with ⟨a, h2, h3⟩;
  refine ⟨a, _, h3⟩,
  apply mem_append_left _ h2,
  apply mem_append_right _ h2
end

lemma rotate_subset {k : nat} : as.rotate k ⊆ as :=
λ x, mem_rotate.elim_left

def seteq (l1 l2 : list α) : Prop := l1 ⊆ l2 ∧ l2 ⊆ l1

local infix `⊆⊇` : 1000 := seteq

lemma forall_mem_of_subset_of_forall_mem {l1 l2 : list α} {p : α → Prop} :
  l1 ⊆ l2 → (∀ a ∈ l2, p a) → (∀ a ∈ l1, p a) :=
λ h1 h2 a h3, h2 _ (h1 h3)

lemma forall_mem_iff_forall_mem_of_seteq {l1 l2 : list α} {p : α → Prop} :
  l1 ⊆⊇ l2 → ((∀ a ∈ l1, p a) ↔ (∀ a ∈ l2, p a)) :=
begin
  rintro ⟨hl, hr⟩, constructor;
  apply forall_mem_of_subset_of_forall_mem;
  assumption
end

lemma map_seteq_map_of_seteq {f : α → β} :
  as1 ⊆⊇ as2 → map f as1 ⊆⊇ map f as2 :=
by { rintro ⟨hl, hr⟩, constructor;
     apply map_subset; assumption }

lemma rotate_seteq_self (k : nat) (as : list α) : as.rotate k ⊆⊇ as :=
by { constructor; intros x h0;
     simpa only [mem_rotate] using h0 }


#exit
lemma subset_union_left [decidable_eq α] (l1 l2 : list α) : l1 ⊆ (l1 ∪ l2) := sorry

#exit
def remove [decidable_eq α] (as : list α) (a : α) :=
as.filter (λ x, x ≠ a)

notation l `-` a := remove l a

#check list.diff
example : [0,1,2] \ {1} = [0,2] :=
begin
  refl,
end

end list


#exit

lemma map_eq_map_of_funeq_over (P : α → Prop) {f g : α → β} :
∀ as, (∀ a, P a → f a = g a) → (∀ a ∈ as, P a) → map f as = map g as
| [] h1 h2 := rfl
| (a::as) h1 h2 :=
  begin
    simp, constructor, apply h1 _ (h2 a (or.inl rfl)),
    apply map_eq_map_of_funeq_over, apply h1,
    apply forall_mem_of_forall_mem_cons h2
  end


  def to_string_sep_core {α : Type}
  (f : α → string) (s : string) : list α → string
  | [] := ""
  | [a] := f a
  | (a::as) := f a ++ s ++ to_string_sep_core as

  def to_string_sep {α : Type} (s : string)
    [has_to_string α] : list α → string :=
    to_string_sep_core has_to_string.to_string s

  def head_nonempty {α : Type} : Π (l : list α), l ≠ [] → α
  | [] h := by {exfalso, exact (h rfl)}
  | (a::as) h := a

  -- def pull_core : nat → list α → option (α × list α)
  -- | _ [] := none
  -- | 0 (a::as) := some ⟨a,as⟩
  -- | (n+1) (a::as) :=
  --   match pull_core n as with
  --   | none := none
  --   | (some ⟨a',as'⟩) := (some ⟨a',a::as'⟩)
  --   end
  --
  -- def pull (n as) : list α :=
  -- match pull_core n as with
  -- | none := as
  -- | (some ⟨a,as'⟩) := (a::as')
  -- end

  def pull : nat → list α → list α
  | _ [] := []
  | 0 as := as
  | (n+1) (a::as) :=
    match pull n as with
    | [] := a::as
    | (a'::as') := a'::(a::as')
    end

  lemma pull_perm : ∀ n (as : list α), pull n as ~ as
  | 0 [] := perm.refl _
  | 0 (a::as) := perm.refl _
  | (n+1) [] := perm.refl _
  | (n+1) (a::as) :=
    begin
      simp [pull], have ih := pull_perm n as,
      cases (pull n as) with a' as', apply perm.refl,
      apply (perm.trans (perm.swap _ _ _) (perm.skip _ ih))
    end

  lemma mem_pull_iff {n a} {as : list α} :
  a ∈ pull n as ↔ a ∈ as :=
  mem_of_perm (pull_perm _ _)

  lemma pull_nil : ∀ n, pull n (nil : list α) = nil
  | 0 := rfl
  | (n+1) := rfl

  def map_mems : Π (as : list α) (h : Π a ∈ as, β), list β
  | [] _ := []
  | (a::as) h :=
    (h a (or.inl rfl))::(map_mems as (λ a' h', h a' (or.inr h')))

  lemma map_mems_length_eq : ∀ (as : list α) (h : Π a ∈ as, β),
    (map_mems as h).length = as.length
  | [] _ := rfl
  | (a::as) h :=
    by { simp [map_mems], rw [map_mems_length_eq] }

  def cond_map {C : α → Type} (f : Π a, C a → β) : Π (as : list α), (Π a ∈ as, C a) → list β
  | [] _ := []
  | (a::as) h :=
    (f a (h _ (or.inl rfl)))::(cond_map as (λ a' h', h _ (or.inr h')))

  lemma cond_map_length_eq {C : α → Type} (f : Π a, C a → β) :
    Π (as : list α) (h : Π a ∈ as, C a), (cond_map f as h).length = as.length
  | [] _ := rfl
  | (a::as) h :=
    by { simp [cond_map], rw [cond_map_length_eq] }

  theorem forall_mem_nil' (C : α → Type) : ∀ x ∈ @nil α, C x :=
  λ _ h, by cases h

  lemma nth_append_ge :
  ∀ {as1 : list α} {m}, as1.length = m → ∀ (as2 n), nth (as1 ++ as2) (m + n) = nth as2 n
  | [] (m+1) h _ _ := by {cases h}
  | [] 0 h as2 n := by {rw [nil_append, zero_add]}
  | (a1::as1) 0 h _ _:= by {cases h}
  | (a1::as1) (m+1) h as2 n:=
    begin
      rw [add_comm (m+1) n, (add_assoc n m 1).symm, (nat.succ_eq_add_one (n+m)).symm],
      simp at *, rw (add_comm 1 _) at h,
      apply (nth_append_ge (eq_of_add_eq_add_right h)),
    end

  lemma nth_append_lt :
  ∀ {as1 : list α} {n}, n < as1.length → ∀ as2, nth (as1 ++ as2) n = nth as1 n
  | [] _ h _ := by {cases h}
  | (a1::as1) 0 _ _ := eq.refl _
  | (a1::as1) (n+1) h as2 :=
    begin
      apply @nth_append_lt as1 n _ as2, simp at h,
      rw add_comm 1 _ at h, apply nat.lt_of_succ_lt_succ,
      repeat {rw nat.succ_eq_add_one}, assumption
    end

  lemma map_eq_map_of_funeq {f g : α → β} (h : ∀ a, f a = g a) :
  ∀ as, map f as = map g as
  | [] := rfl
  | (a::as) := by {simp, constructor, apply h, apply map_eq_map_of_funeq}


  def pad_update_nth [inhabited α] : list α → ℕ → α → list α
  | (x::xs) 0     a := a :: xs
  | (x::xs) (i+1) a := x :: pad_update_nth xs i a
  | []      0     a := [a]
  | []      (i+1) a := (default α) :: pad_update_nth [] i a

  -- lemma nth_pad_update_nth [inhabited α] (as : list α) (k a) :
  -- nth (pad_update_nth as k a) k = some a := sorry

  lemma map_comp {f : β → γ} {g : α → β} {as} :
  map (f ∘ g) as = map f (map g as) := by simp

end list
