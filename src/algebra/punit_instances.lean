/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Instances on punit.
-/

import order.basic
import algebra.module algebra.group

universes u

open lattice

namespace punit
variables (x y : punit.{u+1}) (s : set punit.{u+1})

instance : comm_ring punit :=
by refine
{ add := λ _ _, star,
  zero := star,
  neg := λ _, star,
  mul := λ _ _, star,
  one := star,
  .. };
intros; exact subsingleton.elim _ _

instance : comm_group punit :=
{ inv := λ _, star,
  mul_left_inv := λ _, subsingleton.elim _ _,
  .. punit.comm_ring }

instance : complete_boolean_algebra punit :=
by refine
{ le := λ _ _, true,
  le_antisymm := λ _ _ _ _, subsingleton.elim _ _,
  lt := λ _ _, false,
  lt_iff_le_not_le := λ _ _, iff_of_false not_false (λ H, H.2 trivial),
  top := star,
  bot := star,
  sup := λ _ _, star,
  inf := λ _ _, star,
  Sup := λ _, star,
  Inf := λ _, star,
  sub := λ _ _, star,
  .. punit.comm_ring, .. };
intros; trivial

instance : canonically_ordered_monoid punit :=
by refine
{ lt_of_add_lt_add_left := λ _ _ _, id,
  le_iff_exists_add := λ _ _, iff_of_true _ ⟨star, subsingleton.elim _ _⟩,
  .. punit.comm_ring, .. punit.lattice.complete_boolean_algebra, .. };
intros; trivial

instance : decidable_linear_ordered_cancel_comm_monoid punit :=
{ add_left_cancel := λ _ _ _ _, subsingleton.elim _ _,
  add_right_cancel := λ _ _ _ _, subsingleton.elim _ _,
  le_of_add_le_add_left := λ _ _ _ _, trivial,
  le_total := λ _ _, or.inl trivial,
  decidable_le := λ _ _, decidable.true,
  decidable_eq := punit.decidable_eq,
  decidable_lt := λ _ _, decidable.false,
  .. punit.canonically_ordered_monoid }

instance : module punit punit := module.of_core $
by refine
{ smul := λ _ _, star,
  .. punit.comm_ring, .. };
intros; exact subsingleton.elim _ _

@[simp] lemma zero_eq : (0 : punit) = star := rfl
@[simp] lemma one_eq : (1 : punit) = star := rfl
attribute [to_additive punit.zero_eq] punit.one_eq
@[simp] lemma add_eq : x + y = star := rfl
@[simp] lemma mul_eq : x * y = star := rfl
attribute [to_additive punit.add_eq] punit.mul_eq
@[simp] lemma neg_eq : -x = star := rfl
@[simp] lemma inv_eq : x⁻¹ = star := rfl
attribute [to_additive punit.neg_eq] punit.inv_eq
@[simp] lemma smul_eq : x • y = star := rfl
@[simp] lemma top_eq : (⊤ : punit) = star := rfl
@[simp] lemma bot_eq : (⊥ : punit) = star := rfl
@[simp] lemma sup_eq : x ⊔ y = star := rfl
@[simp] lemma inf_eq : x ⊓ y = star := rfl
@[simp] lemma Sup_eq : Sup s = star := rfl
@[simp] lemma Inf_eq : Inf s = star := rfl
@[simp] protected lemma le : x ≤ y := trivial
@[simp] lemma not_lt : ¬(x < y) := not_false

instance {α : Type*} [monoid α] (f : α → punit) : is_monoid_hom f :=
{ map_one := subsingleton.elim _ _, map_mul := λ _ _, subsingleton.elim _ _ }

instance {α : Type*} [add_monoid α] (f : α → punit) : is_add_monoid_hom f :=
{ map_zero := subsingleton.elim _ _, map_add := λ _ _, subsingleton.elim _ _ }

instance {α : Type*} [group α] (f : α → punit) : is_group_hom f :=
⟨λ _ _, subsingleton.elim _ _⟩

instance {α : Type*} [add_group α] (f : α → punit) : is_add_group_hom f :=
⟨λ _ _, subsingleton.elim _ _⟩

instance {α : Type*} [semiring α] (f : α → punit) : is_semiring_hom f :=
{ .. punit.is_monoid_hom f, .. punit.is_add_monoid_hom f }

instance {α : Type*} [ring α] (f : α → punit) : is_ring_hom f :=
{ .. punit.is_semiring_hom f }

end punit
