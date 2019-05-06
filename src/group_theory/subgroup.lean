/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mitchell Rowett, Scott Morrison, Johan Commelin, Mario Carneiro
-/
import group_theory.submonoid
open set function

variables {α : Type*} {β : Type*} {a a₁ a₂ b c: α}

section group
variables [group α] [add_group β]

@[to_additive injective_add]
lemma injective_mul {a : α} : injective ((*) a) :=
assume a₁ a₂ h,
have a⁻¹ * a * a₁ = a⁻¹ * a * a₂, by rw [mul_assoc, mul_assoc, h],
by rwa [inv_mul_self, one_mul, one_mul] at this

/-- `s` is a subgroup: a set containing 1 and closed under multiplication and inverse. -/
class is_subgroup (s : set α) extends is_submonoid s : Prop :=
(inv_mem {a} : a ∈ s → a⁻¹ ∈ s)

/-- `s` is an additive subgroup: a set containing 0 and closed under addition and negation. -/
class is_add_subgroup (s : set β) extends is_add_submonoid s : Prop :=
(neg_mem {a} : a ∈ s → -a ∈ s)
attribute [to_additive is_add_subgroup] is_subgroup
attribute [to_additive is_add_subgroup.to_is_add_submonoid] is_subgroup.to_is_submonoid
attribute [to_additive is_add_subgroup.neg_mem] is_subgroup.inv_mem
attribute [to_additive is_add_subgroup.mk] is_subgroup.mk

instance additive.is_add_subgroup
  (s : set α) [is_subgroup s] : @is_add_subgroup (additive α) _ s :=
⟨@is_subgroup.inv_mem _ _ _ _⟩

theorem additive.is_add_subgroup_iff
  {s : set α} : @is_add_subgroup (additive α) _ s ↔ is_subgroup s :=
⟨by rintro ⟨⟨h₁, h₂⟩, h₃⟩; exact @is_subgroup.mk α _ _ ⟨h₁, @h₂⟩ @h₃,
  λ h, by resetI; apply_instance⟩

instance multiplicative.is_subgroup
  (s : set β) [is_add_subgroup s] : @is_subgroup (multiplicative β) _ s :=
⟨@is_add_subgroup.neg_mem _ _ _ _⟩

theorem multiplicative.is_subgroup_iff
  {s : set β} : @is_subgroup (multiplicative β) _ s ↔ is_add_subgroup s :=
⟨by rintro ⟨⟨h₁, h₂⟩, h₃⟩; exact @is_add_subgroup.mk β _ _ ⟨h₁, @h₂⟩ @h₃,
  λ h, by resetI; apply_instance⟩

instance subtype.group {s : set α} [is_subgroup s] : group s :=
by subtype_instance

instance subtype.add_group {s : set β} [is_add_subgroup s] : add_group s :=
by subtype_instance
attribute [to_additive subtype.add_group] subtype.group
attribute [to_additive subtype.add_group._proof_1] subtype.group._proof_1
attribute [to_additive subtype.add_group._proof_2] subtype.group._proof_2
attribute [to_additive subtype.add_group._proof_3] subtype.group._proof_3
attribute [to_additive subtype.add_group._proof_4] subtype.group._proof_4
attribute [to_additive subtype.add_group._proof_5] subtype.group._proof_5
attribute [to_additive subtype.add_group.equations._eqn_1] subtype.group.equations._eqn_1

instance subtype.comm_group {α : Type*} [comm_group α] {s : set α} [is_subgroup s] : comm_group s :=
by subtype_instance

instance subtype.add_comm_group {α : Type*} [add_comm_group α] {s : set α} [is_add_subgroup s] :
  add_comm_group s := by subtype_instance
attribute [to_additive subtype.add_comm_group] subtype.comm_group

@[simp, to_additive is_add_subgroup.coe_neg]
lemma is_subgroup.coe_inv {s : set α} [is_subgroup s] (a : s) : ((a⁻¹ : s) : α) = a⁻¹ := rfl

@[simp] lemma is_subgroup.coe_gpow {s : set α} [is_subgroup s] (a : s) (n : ℤ) : ((a ^ n : s) : α) = a ^ n :=
by induction n; simp [is_submonoid.coe_pow a]

@[simp] lemma is_add_subgroup.gsmul_coe {β : Type*} [add_group β] {s : set β} [is_add_subgroup s] (a : s) (n : ℤ) :
  ((gsmul n a : s) : β) = gsmul n a :=
by induction n; simp [is_add_submonoid.smul_coe a]
attribute [to_additive is_add_subgroup.gsmul_coe] is_subgroup.coe_gpow

theorem is_subgroup.of_div (s : set α)
  (one_mem : (1:α) ∈ s) (div_mem : ∀{a b:α}, a ∈ s → b ∈ s → a * b⁻¹ ∈ s):
  is_subgroup s :=
have inv_mem : ∀a, a ∈ s → a⁻¹ ∈ s, from
  assume a ha,
  have 1 * a⁻¹ ∈ s, from div_mem one_mem ha,
  by simpa,
{ inv_mem := inv_mem,
  mul_mem := assume a b ha hb,
    have a * b⁻¹⁻¹ ∈ s, from div_mem ha (inv_mem b hb),
    by simpa,
  one_mem := one_mem }

theorem is_add_subgroup.of_sub (s : set β)
  (zero_mem : (0:β) ∈ s) (sub_mem : ∀{a b:β}, a ∈ s → b ∈ s → a - b ∈ s):
  is_add_subgroup s :=
multiplicative.is_subgroup_iff.1 $
@is_subgroup.of_div (multiplicative β) _ _ zero_mem @sub_mem

@[to_additive is_add_subgroup_Union_of_directed]
lemma is_subgroup_Union_of_directed {ι : Type*} [hι : nonempty ι]
  (s : ι → set α) [∀ i, is_subgroup (s i)]
  (directed : ∀ i j, ∃ k, s i ⊆ s k ∧ s j ⊆ s k) :
  is_subgroup (⋃i, s i) :=
{ inv_mem := λ a ha,
    let ⟨i, hi⟩ := set.mem_Union.1 ha in
    set.mem_Union.2 ⟨i, is_subgroup.inv_mem hi⟩,
  to_is_submonoid := is_submonoid_Union_of_directed s directed }

def gpowers (x : α) : set α := set.range ((^) x : ℤ → α)
def gmultiples (x : β) : set β := set.range (λ i, gsmul i x)
attribute [to_additive gmultiples] gpowers

instance gpowers.is_subgroup (x : α) : is_subgroup (gpowers x) :=
{ one_mem := ⟨(0:ℤ), by simp⟩,
  mul_mem := assume x₁ x₂ ⟨i₁, h₁⟩ ⟨i₂, h₂⟩, ⟨i₁ + i₂, by simp [gpow_add, *]⟩,
  inv_mem := assume x₀ ⟨i, h⟩, ⟨-i, by simp [h.symm]⟩ }

instance gmultiples.is_add_subgroup (x : β) : is_add_subgroup (gmultiples x) :=
multiplicative.is_subgroup_iff.1 $ gpowers.is_subgroup _
attribute [to_additive gmultiples.is_add_subgroup] gpowers.is_subgroup

lemma is_subgroup.gpow_mem {a : α} {s : set α} [is_subgroup s] (h : a ∈ s) : ∀{i:ℤ}, a ^ i ∈ s
| (n : ℕ) := is_submonoid.pow_mem h
| -[1+ n] := is_subgroup.inv_mem (is_submonoid.pow_mem h)

lemma is_add_subgroup.gsmul_mem {a : β} {s : set β} [is_add_subgroup s] : a ∈ s → ∀{i:ℤ}, gsmul i a ∈ s :=
@is_subgroup.gpow_mem (multiplicative β) _ _ _ _

lemma mem_gpowers {a : α} : a ∈ gpowers a := ⟨1, by simp⟩
lemma mem_gmultiples {a : β} : a ∈ gmultiples a := ⟨1, by simp⟩
attribute [to_additive mem_gmultiples] mem_gpowers

end group

namespace is_subgroup
open is_submonoid
variables [group α] (s : set α) [is_subgroup s]

@[to_additive is_add_subgroup.neg_mem_iff]
lemma inv_mem_iff : a⁻¹ ∈ s ↔ a ∈ s :=
⟨λ h, by simpa using inv_mem h, inv_mem⟩

@[to_additive is_add_subgroup.add_mem_cancel_left]
lemma mul_mem_cancel_left (h : a ∈ s) : b * a ∈ s ↔ b ∈ s :=
⟨λ hba, by simpa using mul_mem hba (inv_mem h), λ hb, mul_mem hb h⟩

@[to_additive is_add_subgroup.add_mem_cancel_right]
lemma mul_mem_cancel_right (h : a ∈ s) : a * b ∈ s ↔ b ∈ s :=
⟨λ hab, by simpa using mul_mem (inv_mem h) hab, mul_mem h⟩

end is_subgroup

theorem is_add_subgroup.sub_mem {α} [add_group α] (s : set α) [is_add_subgroup s] (a b : α)
  (ha : a ∈ s) (hb : b ∈ s) : a - b ∈ s :=
is_add_submonoid.add_mem ha (is_add_subgroup.neg_mem hb)

namespace group
open is_submonoid is_subgroup

variables [group α] {s : set α}

inductive in_closure (s : set α) : α → Prop
| basic {a : α} : a ∈ s → in_closure a
| one : in_closure 1
| inv {a : α} : in_closure a → in_closure a⁻¹
| mul {a b : α} : in_closure a → in_closure b → in_closure (a * b)

/-- `group.closure s` is the subgroup closed over `s`, i.e. the smallest subgroup containg s. -/
def closure (s : set α) : set α := {a | in_closure s a }

lemma mem_closure {a : α} : a ∈ s → a ∈ closure s := in_closure.basic

instance closure.is_subgroup (s : set α) : is_subgroup (closure s) :=
{ one_mem := in_closure.one s, mul_mem := assume a b, in_closure.mul, inv_mem := assume a, in_closure.inv }

theorem subset_closure {s : set α} : s ⊆ closure s := λ a, mem_closure

theorem closure_subset {s t : set α} [is_subgroup t] (h : s ⊆ t) : closure s ⊆ t :=
assume a ha, by induction ha; simp [h _, *, one_mem, mul_mem, inv_mem_iff]

lemma closure_subset_iff (s t : set α) [is_subgroup t] : closure s ⊆ t ↔ s ⊆ t :=
⟨assume h b ha, h (mem_closure ha), assume h b ha, closure_subset h ha⟩

theorem closure_mono {s t : set α} (h : s ⊆ t) : closure s ⊆ closure t :=
closure_subset $ set.subset.trans h subset_closure

theorem exists_list_of_mem_closure {s : set α} {a : α} (h : a ∈ closure s) :
  (∃l:list α, (∀x∈l, x ∈ s ∨ x⁻¹ ∈ s) ∧ l.prod = a) :=
in_closure.rec_on h
  (λ x hxs, ⟨[x], list.forall_mem_singleton.2 $ or.inl hxs, one_mul _⟩)
  ⟨[], list.forall_mem_nil _, rfl⟩
  (λ x _ ⟨L, HL1, HL2⟩, ⟨L.reverse.map has_inv.inv,
    λ x hx, let ⟨y, hy1, hy2⟩ := list.exists_of_mem_map hx in
      hy2 ▸ or.imp id (by rw [inv_inv]; exact id) (HL1 _ $ list.mem_reverse.1 hy1).symm,
      HL2 ▸ list.rec_on L one_inv.symm (λ hd tl ih,
        by rw [list.reverse_cons, list.map_append, list.prod_append, ih, list.map_singleton,
            list.prod_cons, list.prod_nil, mul_one, list.prod_cons, mul_inv_rev])⟩)
  (λ x y hx hy ⟨L1, HL1, HL2⟩ ⟨L2, HL3, HL4⟩, ⟨L1 ++ L2, list.forall_mem_append.2 ⟨HL1, HL3⟩,
    by rw [list.prod_append, HL2, HL4]⟩)

theorem mclosure_subset {s : set α} : monoid.closure s ⊆ closure s :=
monoid.closure_subset $ subset_closure

theorem mclosure_inv_subset {s : set α} : monoid.closure (has_inv.inv ⁻¹' s) ⊆ closure s :=
monoid.closure_subset $ λ x hx, inv_inv x ▸ (is_subgroup.inv_mem $ subset_closure hx)

theorem closure_eq_mclosure {s : set α} : closure s = monoid.closure (s ∪ has_inv.inv ⁻¹' s) :=
set.subset.antisymm
  (@closure_subset _ _ _ (monoid.closure (s ∪ has_inv.inv ⁻¹' s))
    { inv_mem := λ x hx, monoid.in_closure.rec_on hx
      (λ x hx, or.cases_on hx (λ hx, monoid.subset_closure $ or.inr $ show x⁻¹⁻¹ ∈ s, from (inv_inv x).symm ▸ hx)
        (λ hx, monoid.subset_closure $ or.inl hx))
      ((@one_inv α _).symm ▸ is_submonoid.one_mem _)
      (λ x y hx hy ihx ihy, (mul_inv_rev x y).symm ▸ is_submonoid.mul_mem ihy ihx) }
    (set.subset.trans (set.subset_union_left _ _) monoid.subset_closure))
  (monoid.closure_subset $ set.union_subset subset_closure $ λ x hx, inv_inv x ▸ (is_subgroup.inv_mem $ subset_closure hx))

theorem mem_closure_union_iff {α : Type*} [comm_group α] {s t : set α} {x : α} :
  x ∈ closure (s ∪ t) ↔ ∃ y ∈ closure s, ∃ z ∈ closure t, y * z = x :=
begin
  simp only [closure_eq_mclosure, monoid.mem_closure_union_iff, exists_prop, preimage_union], split,
  { rintro ⟨_, ⟨ys, hys, yt, hyt, rfl⟩, _, ⟨zs, hzs, zt, hzt, rfl⟩, rfl⟩,
    refine ⟨_, ⟨_, hys, _, hzs, rfl⟩, _, ⟨_, hyt, _, hzt, rfl⟩, _⟩,
    rw [mul_assoc, mul_assoc, mul_left_comm zs], refl },
  { rintro ⟨_, ⟨ys, hys, zs, hzs, rfl⟩, _, ⟨yt, hyt, zt, hzt, rfl⟩, rfl⟩,
    refine ⟨_, ⟨ys, hys, yt, hyt, rfl⟩, _, ⟨zs, hzs, zt, hzt, rfl⟩, _⟩,
    rw [mul_assoc, mul_assoc, mul_left_comm yt], refl }
end

theorem gpowers_eq_closure {a : α} : gpowers a = closure {a} :=
subset.antisymm
  (assume x h, match x, h with _, ⟨i, rfl⟩ := gpow_mem (mem_closure $ by simp) end)
  (closure_subset $ by simp [mem_gpowers])

end group

namespace add_group
open is_add_submonoid is_add_subgroup

variables [add_group α] {s : set α}

/-- `add_group.closure s` is the additive subgroup closed over `s`, i.e. the smallest subgroup containg s. -/
def closure (s : set α) : set α := @group.closure (multiplicative α) _ s
attribute [to_additive add_group.closure] group.closure

lemma mem_closure {a : α} : a ∈ s → a ∈ closure s := group.mem_closure
attribute [to_additive add_group.mem_closure] group.mem_closure

instance closure.is_add_subgroup (s : set α) : is_add_subgroup (closure s) :=
multiplicative.is_subgroup_iff.1 $ group.closure.is_subgroup _
attribute [to_additive add_group.closure.is_add_subgroup] group.closure.is_subgroup

attribute [to_additive add_group.subset_closure] group.subset_closure

theorem closure_subset {s t : set α} [is_add_subgroup t] : s ⊆ t → closure s ⊆ t :=
group.closure_subset

attribute [to_additive add_group.closure_subset] group.closure_subset
attribute [to_additive add_group.closure_subset_iff] group.closure_subset_iff

theorem gmultiples_eq_closure {a : α} : gmultiples a = closure {a} :=
group.gpowers_eq_closure
attribute [to_additive add_group.gmultiples_eq_closure] group.gpowers_eq_closure

@[elab_as_eliminator]
theorem in_closure.rec_on {C : α → Prop}
  {a : α} (H : a ∈ closure s)
  (H1 : ∀ {a : α}, a ∈ s → C a) (H2 : C 0) (H3 : ∀ {a : α}, a ∈ closure s → C a → C (-a))
  (H4 : ∀ {a b : α}, a ∈ closure s → b ∈ closure s → C a → C b → C (a + b)) :
  C a :=
group.in_closure.rec_on H (λ _, H1) H2 (λ _, H3) (λ _ _, H4)

theorem closure_mono {s t : set α} (h : s ⊆ t) : closure s ⊆ closure t :=
closure_subset $ set.subset.trans h subset_closure

theorem exists_list_of_mem_closure {s : set α} {a : α} (h : a ∈ closure s) :
  (∃l:list α, (∀x∈l, x ∈ s ∨ -x ∈ s) ∧ l.sum = a) :=
group.exists_list_of_mem_closure h

theorem mclosure_subset {s : set α} : add_monoid.closure s ⊆ closure s :=
group.mclosure_subset

theorem mclosure_inv_subset {s : set α} : add_monoid.closure (has_neg.neg ⁻¹' s) ⊆ closure s :=
group.mclosure_inv_subset

theorem closure_eq_mclosure {s : set α} : closure s = add_monoid.closure (s ∪ has_neg.neg ⁻¹' s) :=
group.closure_eq_mclosure

theorem mem_closure_union_iff {α : Type*} [add_comm_group α] {s t : set α} {x : α} :
  x ∈ closure (s ∪ t) ↔ ∃ y ∈ closure s, ∃ z ∈ closure t, y + z = x :=
group.mem_closure_union_iff

end add_group

class normal_subgroup [group α] (s : set α) extends is_subgroup s : Prop :=
(normal : ∀ n ∈ s, ∀ g : α, g * n * g⁻¹ ∈ s)
class normal_add_subgroup [add_group α] (s : set α) extends is_add_subgroup s : Prop :=
(normal : ∀ n ∈ s, ∀ g : α, g + n - g ∈ s)
attribute [to_additive normal_add_subgroup] normal_subgroup
attribute [to_additive normal_add_subgroup.to_is_add_subgroup] normal_subgroup.to_is_subgroup
attribute [to_additive normal_add_subgroup.normal] normal_subgroup.normal
attribute [to_additive normal_add_subgroup.mk] normal_subgroup.mk

@[to_additive normal_add_subgroup_of_add_comm_group]
lemma normal_subgroup_of_comm_group [comm_group α] (s : set α) [hs : is_subgroup s] :
  normal_subgroup s :=
{ normal := λ n hn g, by rwa [mul_right_comm, mul_right_inv, one_mul],
  ..hs }

instance additive.normal_add_subgroup [group α]
  (s : set α) [normal_subgroup s] : @normal_add_subgroup (additive α) _ s :=
⟨@normal_subgroup.normal _ _ _ _⟩

theorem additive.normal_add_subgroup_iff [group α]
  {s : set α} : @normal_add_subgroup (additive α) _ s ↔ normal_subgroup s :=
⟨by rintro ⟨h₁, h₂⟩; exact
    @normal_subgroup.mk α _ _ (additive.is_add_subgroup_iff.1 h₁) @h₂,
  λ h, by resetI; apply_instance⟩

instance multiplicative.normal_subgroup [add_group α]
  (s : set α) [normal_add_subgroup s] : @normal_subgroup (multiplicative α) _ s :=
⟨@normal_add_subgroup.normal _ _ _ _⟩

theorem multiplicative.normal_subgroup_iff [add_group α]
  {s : set α} : @normal_subgroup (multiplicative α) _ s ↔ normal_add_subgroup s :=
⟨by rintro ⟨h₁, h₂⟩; exact
    @normal_add_subgroup.mk α _ _ (multiplicative.is_subgroup_iff.1 h₁) @h₂,
  λ h, by resetI; apply_instance⟩

namespace is_subgroup
variable [group α]

-- Normal subgroup properties
lemma mem_norm_comm {s : set α} [normal_subgroup s] {a b : α} (hab : a * b ∈ s) : b * a ∈ s :=
have h : a⁻¹ * (a * b) * a⁻¹⁻¹ ∈ s, from normal_subgroup.normal (a * b) hab a⁻¹,
by simp at h; exact h

lemma mem_norm_comm_iff {s : set α} [normal_subgroup s] {a b : α} : a * b ∈ s ↔ b * a ∈ s :=
⟨mem_norm_comm, mem_norm_comm⟩

/-- The trivial subgroup -/
def trivial (α : Type*) [group α] : set α := {1}

@[simp] lemma mem_trivial [group α] {g : α} : g ∈ trivial α ↔ g = 1 :=
mem_singleton_iff

instance trivial_normal : normal_subgroup (trivial α) :=
by refine {..}; simp [trivial] {contextual := tt}

lemma trivial_eq_closure : trivial α = group.closure ∅ :=
subset.antisymm
  (by simp [set.subset_def, is_submonoid.one_mem])
  (group.closure_subset $ by simp)

lemma eq_trivial_iff {H : set α} [is_subgroup H] :
  H = trivial α ↔ (∀ x ∈ H, x = (1 : α)) :=
by simp only [set.ext_iff, is_subgroup.mem_trivial];
  exact ⟨λ h x, (h x).1, λ h x, ⟨h x, λ hx, hx.symm ▸ is_submonoid.one_mem H⟩⟩

instance univ_subgroup : normal_subgroup (@univ α) :=
by refine {..}; simp

def center (α : Type*) [group α] : set α := {z | ∀ g, g * z = z * g}

lemma mem_center {a : α} : a ∈ center α ↔ ∀g, g * a = a * g := iff.rfl

instance center_normal : normal_subgroup (center α) :=
{ one_mem := by simp [center],
  mul_mem := assume a b ha hb g,
    by rw [←mul_assoc, mem_center.2 ha g, mul_assoc, mem_center.2 hb g, ←mul_assoc],
  inv_mem := assume a ha g,
    calc
      g * a⁻¹ = a⁻¹ * (g * a) * a⁻¹ : by simp [ha g]
      ...     = a⁻¹ * g             : by rw [←mul_assoc, mul_assoc]; simp,
  normal := assume n ha g h,
    calc
      h * (g * n * g⁻¹) = h * n           : by simp [ha g, mul_assoc]
      ...               = g * g⁻¹ * n * h : by rw ha h; simp
      ...               = g * n * g⁻¹ * h : by rw [mul_assoc g, ha g⁻¹, ←mul_assoc] }

def normalizer (s : set α) : set α :=
{g : α | ∀ n, n ∈ s ↔ g * n * g⁻¹ ∈ s}

instance (s : set α) [is_subgroup s] : is_subgroup (normalizer s) :=
{ one_mem := by simp [normalizer],
  mul_mem := λ a b (ha : ∀ n, n ∈ s ↔ a * n * a⁻¹ ∈ s)
    (hb : ∀ n, n ∈ s ↔ b * n * b⁻¹ ∈ s) n,
    by rw [mul_inv_rev, ← mul_assoc, mul_assoc a, mul_assoc a, ← ha, ← hb],
  inv_mem := λ a (ha : ∀ n, n ∈ s ↔ a * n * a⁻¹ ∈ s) n,
    by rw [ha (a⁻¹ * n * a⁻¹⁻¹)];
    simp [mul_assoc] }

lemma subset_normalizer (s : set α) [is_subgroup s] : s ⊆ normalizer s :=
λ g hg n, by rw [is_subgroup.mul_mem_cancel_left _ ((is_subgroup.inv_mem_iff _).2 hg),
  is_subgroup.mul_mem_cancel_right _ hg]

instance (s : set α) [is_subgroup s] : normal_subgroup (subtype.val ⁻¹' s : set (normalizer s)) :=
{ one_mem := show (1 : α) ∈ s, from is_submonoid.one_mem _,
  mul_mem := λ a b ha hb, show (a * b : α) ∈ s, from is_submonoid.mul_mem ha hb,
  inv_mem := λ a ha, show (a⁻¹ : α) ∈ s, from is_subgroup.inv_mem ha,
  normal := λ a ha ⟨m, hm⟩, (hm a).1 ha }

end is_subgroup

namespace is_add_subgroup
variable [add_group α]

attribute [to_additive is_add_subgroup.mem_norm_comm] is_subgroup.mem_norm_comm
attribute [to_additive is_add_subgroup.mem_norm_comm_iff] is_subgroup.mem_norm_comm_iff

/-- The trivial subgroup -/
def trivial (α : Type*) [add_group α] : set α := {0}
attribute [to_additive is_add_subgroup.trivial] is_subgroup.trivial
attribute [to_additive is_add_subgroup.trivial.equations._eqn_1] is_subgroup.trivial.equations._eqn_1

attribute [to_additive is_add_subgroup.mem_trivial] is_subgroup.mem_trivial

instance trivial_normal : normal_add_subgroup (trivial α) :=
multiplicative.normal_subgroup_iff.1 is_subgroup.trivial_normal
attribute [to_additive is_add_subgroup.trivial_normal] is_subgroup.trivial_normal

attribute [to_additive is_add_subgroup.trivial_eq_closure] is_subgroup.trivial_eq_closure

attribute [to_additive is_add_subgroup.eq_trivial_iff] is_subgroup.eq_trivial_iff

instance univ_add_subgroup : normal_add_subgroup (@univ α) :=
multiplicative.normal_subgroup_iff.1 is_subgroup.univ_subgroup
attribute [to_additive is_add_subgroup.univ_add_subgroup] is_subgroup.univ_subgroup

def center (α : Type*) [add_group α] : set α := {z | ∀ g, g + z = z + g}
attribute [to_additive is_add_subgroup.center] is_subgroup.center

attribute [to_additive is_add_subgroup.mem_center] is_subgroup.mem_center

instance center_normal : normal_add_subgroup (center α) :=
multiplicative.normal_subgroup_iff.1 is_subgroup.center_normal

end is_add_subgroup

-- Homomorphism subgroups
namespace is_group_hom
open is_submonoid is_subgroup
variables [group α] [group β]

@[to_additive is_add_group_hom.ker]
def ker (f : α → β) [is_group_hom f] : set α := preimage f (trivial β)
attribute [to_additive is_add_group_hom.ker.equations._eqn_1] ker.equations._eqn_1

@[to_additive is_add_group_hom.mem_ker]
lemma mem_ker (f : α → β) [is_group_hom f] {x : α} : x ∈ ker f ↔ f x = 1 :=
mem_trivial

@[to_additive is_add_group_hom.map_zero_ker_neg]
lemma one_ker_inv (f : α → β) [is_group_hom f] {a b : α} (h : f (a * b⁻¹) = 1) : f a = f b :=
begin
  rw [map_mul f, map_inv f] at h,
  rw [←inv_inv (f b), eq_inv_of_mul_eq_one h]
end

@[to_additive is_add_group_hom.map_zero_ker_neg']
lemma one_ker_inv' (f : α → β) [is_group_hom f] {a b : α} (h : f (a⁻¹ * b) = 1) : f a = f b :=
begin
  rw [map_mul f, map_inv f] at h,
  apply eq_of_inv_eq_inv,
  rw eq_inv_of_mul_eq_one h
end

@[to_additive is_add_group_hom.map_neg_ker_zero]
lemma inv_ker_one (f : α → β) [is_group_hom f] {a b : α} (h : f a = f b) : f (a * b⁻¹) = 1 :=
have f a * (f b)⁻¹ = 1, by rw [h, mul_right_inv],
by rwa [←map_inv f, ←map_mul f] at this

@[to_additive is_add_group_hom.map_neg_ker_zero']
lemma inv_ker_one' (f : α → β) [is_group_hom f] {a b : α} (h : f a = f b) : f (a⁻¹ * b) = 1 :=
have (f a)⁻¹ * f b = 1, by rw [h, mul_left_inv],
by rwa [←map_inv f, ←map_mul f] at this

@[to_additive is_add_group_hom.map_zero_iff_ker_neg]
lemma one_iff_ker_inv (f : α → β) [is_group_hom f] (a b : α) : f a = f b ↔ f (a * b⁻¹) = 1 :=
⟨inv_ker_one f, one_ker_inv f⟩

@[to_additive is_add_group_hom.map_zero_iff_ker_neg']
lemma one_iff_ker_inv' (f : α → β) [is_group_hom f] (a b : α) : f a = f b ↔ f (a⁻¹ * b) = 1 :=
⟨inv_ker_one' f, one_ker_inv' f⟩

@[to_additive is_add_group_hom.map_neg_iff_ker]
lemma inv_iff_ker (f : α → β) [w : is_group_hom f] (a b : α) : f a = f b ↔ a * b⁻¹ ∈ ker f :=
by rw [mem_ker]; exact one_iff_ker_inv _ _ _

@[to_additive is_add_group_hom.map_neg_iff_ker']
lemma inv_iff_ker' (f : α → β) [w : is_group_hom f] (a b : α) : f a = f b ↔ a⁻¹ * b ∈ ker f :=
by rw [mem_ker]; exact one_iff_ker_inv' _ _ _

instance image_subgroup (f : α → β) [is_group_hom f] (s : set α) [is_subgroup s] :
  is_subgroup (f '' s) :=
{ mul_mem := assume a₁ a₂ ⟨b₁, hb₁, eq₁⟩ ⟨b₂, hb₂, eq₂⟩,
             ⟨b₁ * b₂, mul_mem hb₁ hb₂, by simp [eq₁, eq₂, map_mul f]⟩,
  one_mem := ⟨1, one_mem s, map_one f⟩,
  inv_mem := assume a ⟨b, hb, eq⟩, ⟨b⁻¹, inv_mem hb, by rw map_inv f; simp *⟩ }
attribute [to_additive is_add_group_hom.image_add_subgroup._match_1] is_group_hom.image_subgroup._match_1
attribute [to_additive is_add_group_hom.image_add_subgroup._match_2] is_group_hom.image_subgroup._match_2
attribute [to_additive is_add_group_hom.image_add_subgroup._match_3] is_group_hom.image_subgroup._match_3
attribute [to_additive is_add_group_hom.image_add_subgroup] is_group_hom.image_subgroup
attribute [to_additive is_add_group_hom.image_add_subgroup._match_1.equations._eqn_1] is_group_hom.image_subgroup._match_1.equations._eqn_1
attribute [to_additive is_add_group_hom.image_add_subgroup._match_2.equations._eqn_1] is_group_hom.image_subgroup._match_2.equations._eqn_1
attribute [to_additive is_add_group_hom.image_add_subgroup._match_3.equations._eqn_1] is_group_hom.image_subgroup._match_3.equations._eqn_1
attribute [to_additive is_add_group_hom.image_add_subgroup.equations._eqn_1] is_group_hom.image_subgroup.equations._eqn_1

instance range_subgroup (f : α → β) [is_group_hom f] : is_subgroup (set.range f) :=
@set.image_univ _ _ f ▸ is_group_hom.image_subgroup f set.univ
attribute [to_additive is_add_group_hom.range_add_subgroup] is_group_hom.range_subgroup
attribute [to_additive is_add_group_hom.range_add_subgroup.equations._eqn_1] is_group_hom.range_subgroup.equations._eqn_1

local attribute [simp] one_mem inv_mem mul_mem normal_subgroup.normal

instance preimage (f : α → β) [is_group_hom f] (s : set β) [is_subgroup s] :
  is_subgroup (f ⁻¹' s) :=
by refine {..}; simp [map_mul f, map_one f, map_inv f, @inv_mem β _ s] {contextual:=tt}
attribute [to_additive is_add_group_hom.preimage] is_group_hom.preimage
attribute [to_additive is_add_group_hom.preimage.equations._eqn_1] is_group_hom.preimage.equations._eqn_1

instance preimage_normal (f : α → β) [is_group_hom f] (s : set β) [normal_subgroup s] :
  normal_subgroup (f ⁻¹' s) :=
⟨by simp [map_mul f, map_inv f] {contextual:=tt}⟩
attribute [to_additive is_add_group_hom.preimage_normal] is_group_hom.preimage_normal
attribute [to_additive is_add_group_hom.preimage_normal.equations._eqn_1] is_group_hom.preimage_normal.equations._eqn_1

instance normal_subgroup_ker (f : α → β) [is_group_hom f] : normal_subgroup (ker f) :=
is_group_hom.preimage_normal f (trivial β)
attribute [to_additive is_add_group_hom.normal_subgroup_ker] is_group_hom.normal_subgroup_ker
attribute [to_additive is_add_group_hom.normal_subgroup_ker.equations._eqn_1] is_group_hom.normal_subgroup_ker.equations._eqn_1

@[to_additive is_add_group_hom.inj_of_trivial_ker]
lemma inj_of_trivial_ker (f : α → β) [is_group_hom f] (h : ker f = trivial α) :
  function.injective f :=
begin
  intros a₁ a₂ hfa,
  simp [ext_iff, ker, is_subgroup.trivial] at h,
  have ha : a₁ * a₂⁻¹ = 1, by rw ←h; exact inv_ker_one f hfa,
  rw [eq_inv_of_mul_eq_one ha, inv_inv a₂]
end

@[to_additive is_add_group_hom.trivial_ker_of_inj]
lemma trivial_ker_of_inj (f : α → β) [is_group_hom f] (h : function.injective f) :
  ker f = trivial α :=
set.ext $ assume x, iff.intro
  (assume hx,
    suffices f x = f 1, by simpa using h this,
    by simp [map_one f]; rwa [mem_ker] at hx)
  (by simp [mem_ker, is_group_hom.map_one f] {contextual := tt})

@[to_additive is_add_group_hom.inj_iff_trivial_ker]
lemma inj_iff_trivial_ker (f : α → β) [is_group_hom f] :
  function.injective f ↔ ker f = trivial α :=
⟨trivial_ker_of_inj f, inj_of_trivial_ker f⟩

end is_group_hom

instance subtype_val.is_group_hom [group α] {s : set α} [is_subgroup s] :
  is_group_hom (subtype.val : s → α) := { ..subtype_val.is_monoid_hom }

instance subtype_val.is_add_group_hom [add_group α] {s : set α} [is_add_subgroup s] :
  is_add_group_hom (subtype.val : s → α) := { ..subtype_val.is_add_monoid_hom }
attribute [to_additive subtype_val.is_group_hom] subtype_val.is_add_group_hom

instance coe.is_group_hom [group α] {s : set α} [is_subgroup s] :
  is_group_hom (coe : s → α) := { ..subtype_val.is_monoid_hom }

instance coe.is_add_group_hom [add_group α] {s : set α} [is_add_subgroup s] :
  is_add_group_hom (coe : s → α) :=
{ ..subtype_val.is_add_monoid_hom }
attribute [to_additive coe.is_group_hom] coe.is_add_group_hom

instance subtype_mk.is_group_hom [group α] [group β] {s : set α}
  [is_subgroup s] (f : β → α) [is_group_hom f] (h : ∀ x, f x ∈ s) :
  is_group_hom (λ x, (⟨f x, h x⟩ : s)) := { ..subtype_mk.is_monoid_hom f h }

instance subtype_mk.is_add_group_hom [add_group α] [add_group β] {s : set α}
  [is_add_subgroup s] (f : β → α) [is_add_group_hom f] (h : ∀ x, f x ∈ s) :
  is_add_group_hom (λ x, (⟨f x, h x⟩ : s)) :=
{ ..subtype_mk.is_add_monoid_hom f h }
attribute [to_additive subtype_mk.is_group_hom] subtype_mk.is_add_group_hom

instance set_inclusion.is_group_hom [group α] {s t : set α}
  [is_subgroup s] [is_subgroup t] (h : s ⊆ t) : is_group_hom (set.inclusion h) :=
subtype_mk.is_group_hom _ _

instance set_inclusion.is_add_group_hom [add_group α] {s t : set α}
  [is_add_subgroup s] [is_add_subgroup t] (h : s ⊆ t) : is_add_group_hom (set.inclusion h) :=
subtype_mk.is_add_group_hom _ _
attribute [to_additive set_inclusion.is_group_hom] set_inclusion.is_add_group_hom

section simple_group

class simple_group (α : Type*) [group α] : Prop :=
(simple : ∀ (N : set α) [normal_subgroup N], N = is_subgroup.trivial α ∨ N = set.univ)

class simple_add_group (α : Type*) [add_group α] : Prop :=
(simple : ∀ (N : set α) [normal_add_subgroup N], N = is_add_subgroup.trivial α ∨ N = set.univ)

attribute [to_additive simple_add_group] simple_group

theorem additive.simple_add_group_iff [group α] :
  simple_add_group (additive α) ↔ simple_group α :=
⟨λ hs, ⟨λ N h, @simple_add_group.simple _ _ hs _ (by exactI additive.normal_add_subgroup_iff.2 h)⟩,
  λ hs, ⟨λ N h, @simple_group.simple _ _ hs _ (by exactI additive.normal_add_subgroup_iff.1 h)⟩⟩

instance additive.simple_add_group [group α] [simple_group α] :
  simple_add_group (additive α) := additive.simple_add_group_iff.2 (by apply_instance)

theorem multiplicative.simple_group_iff [add_group α] :
  simple_group (multiplicative α) ↔ simple_add_group α :=
⟨λ hs, ⟨λ N h, @simple_group.simple _ _ hs _ (by exactI multiplicative.normal_subgroup_iff.2 h)⟩,
  λ hs, ⟨λ N h, @simple_add_group.simple _ _ hs _ (by exactI multiplicative.normal_subgroup_iff.1 h)⟩⟩

instance multiplicative.simple_group [add_group α] [simple_add_group α] :
simple_group (multiplicative α) := multiplicative.simple_group_iff.2 (by apply_instance)

lemma simple_group_of_surjective [group α] [group β] [simple_group α] (f : α → β)
  [is_group_hom f] (hf : function.surjective f) : simple_group β :=
⟨λ H iH, have normal_subgroup (f ⁻¹' H), by resetI; apply_instance,
  begin
    resetI,
    cases simple_group.simple (f ⁻¹' H) with h h,
    { refine or.inl (is_subgroup.eq_trivial_iff.2 (λ x hx, _)),
      cases hf x with y hy,
      rw ← hy at hx,
      rw [← hy, is_subgroup.eq_trivial_iff.1 h y hx, is_group_hom.map_one f] },
    { refine or.inr (set.eq_univ_of_forall (λ x, _)),
      cases hf x with y hy,
      rw set.eq_univ_iff_forall at h,
      rw ← hy,
      exact h y }
  end⟩

lemma simple_add_group_of_surjective [add_group α] [add_group β] [simple_add_group α] (f : α → β)
  [is_add_group_hom f] (hf : function.surjective f) : simple_add_group β :=
multiplicative.simple_group_iff.1 (@simple_group_of_surjective (multiplicative α) (multiplicative β) _ _ _ f _ hf)

attribute [to_additive simple_add_group_of_surjective] simple_group_of_surjective

end simple_group
