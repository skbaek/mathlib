/-
Copyright (c) 2019 Abhimanyu Pallavi Sudhir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhimanyu Pallavi Sudhir
"Filterproducts" (ultraproducts on general filters), ultraproducts and 
the construction of the hyperreals.
-/

import data.real.basic
import order.filter.basic

universes u v
variables {α : Type u} (β : Type v) (φ : filter α)
local attribute [instance] classical.prop_decidable

namespace filter 

/-- Two sequences are bigly equal iff the kernel of their difference is in φ -/
def bigly_equal : setoid (α → β) := 
⟨ λ a b, {n | a n = b n} ∈ φ.sets,
  λ a, by simp only [eq_self_iff_true, (set.univ_def).symm, univ_sets], 
  λ a b ab, by simpa only [eq_comm], 
  λ a b c ab bc, sets_of_superset φ (inter_sets φ ab bc) 
    (λ n (r : a n = b n ∧ b n = c n), eq.trans r.1 r.2)⟩

/-- Ultraproduct, but on a general filter -/
def filterprod := quotient (bigly_equal β φ)
local notation `β*` := filterprod β φ

namespace filter_product

def seq_to_filterprod : (α → β) → β* := @quotient.mk' (α → β) (bigly_equal β φ)

/-- Equivalence class containing the constant sequence of a term in β -/
def to_filterprod : β → β* := function.comp (seq_to_filterprod β φ) (λ x n, x)

theorem to_filterprod_inj (NT : φ ≠ ⊥): function.injective (to_filterprod β φ) :=
begin
  intros r s rs, by_contra N,
  rw [to_filterprod, seq_to_filterprod, quotient.eq', bigly_equal] at rs, 
  simp only [N, set.set_of_false, empty_in_sets_eq_bot] at rs,
  exact NT rs
end

instance : has_coe (α → β) β* := ⟨seq_to_filterprod β φ⟩

instance coe_filterprod : has_coe β β* := ⟨to_filterprod β φ⟩

instance [has_add β] : has_add β* :=
{ add := λ x y, quotient.lift_on₂' x y (λ a b, (quotient.mk' $ λ n, a n + b n : β*)) $
    λ a₁ a₂ b₁ b₂ h1 h2, quotient.sound' $ show _ ∈ _,
    by filter_upwards [h1, h2] λ i hi1 hi2, congr (congr_arg _ hi1) hi2 }

instance [has_zero β] : has_zero β* := { zero := to_filterprod β φ (0 : β) }

instance [has_neg β] : has_neg β* :=
{ neg := λ x, (quotient.lift_on' x (λ a, (quotient.mk' (λ n, - a n) : β*))) $
    λ a b rab, quotient.sound' $ by show _ ∈ _; by
    { have h : {n | a n = b n} ⊆ {n | - a n =  - b n} := 
        λ n ha, by change a n = b n at ha; simp [ha],
      exact mem_sets_of_superset rab h } }

instance [add_semigroup β] : add_semigroup β* :=
{ add := has_add.add,
  add_assoc := λ x y z, quotient.induction_on₃' x y z $ λ a b c, quotient.sound' $
    show {n | _+_+_ = _+(_+_)} ∈ _, by simp only [add_assoc, eq_self_iff_true]; exact φ.2 }

instance am [add_monoid β] : add_monoid β* :=
{ add := has_add.add,
  add_assoc := add_semigroup.add_assoc,
  zero := 0,
  zero_add := λ x, quotient.induction_on' x 
    (λ a, quotient.sound'(by simp only [zero_add]; apply (setoid.iseqv _).1)),
  add_zero := λ x, quotient.induction_on' x 
    (λ a, quotient.sound'(by simp only [add_zero]; apply (setoid.iseqv _).1)) }

instance acs [add_comm_semigroup β] : add_comm_semigroup β* :=
{ add := has_add.add,
  add_assoc := add_semigroup.add_assoc,
  add_comm := λ x y, quotient.induction_on₂' x y 
    (λ a b, quotient.sound' (by simp only [add_comm]; apply (setoid.iseqv _).1)) }

instance acm [add_comm_monoid β] : add_comm_monoid β* := 
{..filter_product.acs β φ, ..filter_product.am β φ }

instance ag [add_group β] : add_group β* :=
{ add := has_add.add,
  add_assoc := add_semigroup.add_assoc,
  zero := 0,
  zero_add := add_monoid.zero_add,
  add_zero := add_monoid.add_zero,
  neg := has_neg.neg,
  add_left_neg := λ x, quotient.induction_on' x 
    (λ a, quotient.sound' (by simp only [add_left_neg]; apply (setoid.iseqv _).1)) }

instance acg [add_comm_group β] : add_comm_group β* := 
{..filter_product.acm β φ, ..filter_product.ag β φ}

instance [has_mul β] : has_mul β* :=
{ mul := λ x y, quotient.lift_on₂' x y (λ a b, (quotient.mk' $ λ n, a n * b n : β*)) $
    λ a₁ a₂ b₁ b₂ h1 h2, quotient.sound' $ show _ ∈ _,
    by filter_upwards [h1, h2] λ i hi1 hi2, congr (congr_arg _ hi1) hi2 }

instance [has_one β] : has_one β* := { one := to_filterprod β φ (1 : β) }

instance [has_inv β] : has_inv β* :=
{ inv := λ x, (quotient.lift_on' x (λ a, (quotient.mk' (λ n, (a n)⁻¹) : β*))) $
    λ a b rab, quotient.sound' $ by show _ ∈ _; by
    { have h : {n | a n = b n} ⊆ {n | (a n)⁻¹ = (b n)⁻¹} := 
        λ n ha, by change a n = b n at ha; simp [ha],
      exact mem_sets_of_superset rab h } }

instance [semigroup β] : semigroup β* :=
{ mul := has_mul.mul,
  mul_assoc := λ x y z, quotient.induction_on₃' x y z $ λ a b c, quotient.sound' $
    show {n | _*_*_ = _*(_*_)} ∈ _, by simp only [mul_assoc, eq_self_iff_true]; exact φ.2 }

instance m [monoid β] : monoid β* :=
{ mul := has_mul.mul,
  mul_assoc := semigroup.mul_assoc,
  one := 1,
  one_mul := λ x, quotient.induction_on' x 
    (λ a, quotient.sound'(by simp only [one_mul]; apply (setoid.iseqv _).1)),
  mul_one := λ x, quotient.induction_on' x 
    (λ a, quotient.sound'(by simp only [mul_one]; apply (setoid.iseqv _).1)) }

instance cs [comm_semigroup β] : comm_semigroup β* :=
{ mul := has_mul.mul,
  mul_assoc := semigroup.mul_assoc,
  mul_comm := λ x y, quotient.induction_on₂' x y 
    (λ a b, quotient.sound' (by simp only [mul_comm]; apply (setoid.iseqv _).1)) }

instance cm [comm_monoid β] : comm_monoid β* := 
{..filter_product.cs β φ, ..filter_product.m β φ }

instance g [group β] : group β* :=
{ mul := has_mul.mul,
  mul_assoc := semigroup.mul_assoc,
  one := 1,
  one_mul := monoid.one_mul,
  mul_one := monoid.mul_one,
  inv := has_inv.inv,
  mul_left_inv := λ x, quotient.induction_on' x 
    (λ a, quotient.sound' (by simp only [mul_left_inv]; apply (setoid.iseqv _).1)) }

instance [comm_group β] : comm_group β* := 
{..filter_product.cm β φ, ..filter_product.g β φ}

instance d [distrib β] : distrib β* :=
{ add := has_add.add,
  mul := has_mul.mul,
  left_distrib := λ x y z, quotient.induction_on₃' x y z 
    (λ x y z, quotient.sound' (by simp only [left_distrib]; apply (setoid.iseqv _).1)),
  right_distrib := λ x y z, quotient.induction_on₃' x y z 
    (λ x y z, quotient.sound' (by simp only [right_distrib]; apply (setoid.iseqv _).1)) }

instance mz [mul_zero_class β] : mul_zero_class β* :=
{ mul := has_mul.mul,
  zero := 0,
  zero_mul := λ x, quotient.induction_on' x 
    (λ a, quotient.sound' (by simp only [zero_mul]; apply (setoid.iseqv _).1)),
  mul_zero := λ x, quotient.induction_on' x 
    (λ a, quotient.sound' (by simp only [mul_zero]; apply (setoid.iseqv _).1)) }

instance sr [semiring β] : semiring β* := 
{ ..filter_product.acm β φ, ..filter_product.m β φ, ..filter_product.d β φ, ..filter_product.mz β φ }

instance r [ring β] : ring β* := 
{..filter_product.acg β φ, ..filter_product.m β φ, ..filter_product.d β φ}

instance [comm_semiring β] : comm_semiring β* := 
{..filter_product.sr β φ, ..filter_product.cm β φ}

instance cr [comm_ring β] : comm_ring β* := 
{..filter_product.r β φ, ..filter_product.cs β φ}

instance zo [zero_ne_one_class β] (U : is_ultrafilter φ) : zero_ne_one_class β* :=
{ zero := 0,
  one := 1,
  zero_ne_one := by
  { intro c, have c' : _ := quotient.exact' c, 
    change _ ∈ _ at c', 
    simp only [set.set_of_false, zero_ne_one, empty_in_sets_eq_bot] at c', 
    apply U.1 c' } }

instance dr [division_ring β] (U : is_ultrafilter φ) : division_ring β* :=
{ add := has_add.add,
  add_assoc := add_semigroup.add_assoc,
  zero := 0,
  zero_add := add_monoid.zero_add,
  add_zero := add_monoid.add_zero,
  neg := has_neg.neg,
  add_left_neg := add_group.add_left_neg,
  add_comm := add_comm_semigroup.add_comm,
  mul := has_mul.mul,
  mul_assoc := semigroup.mul_assoc,
  one := 1,
  one_mul := monoid.one_mul,
  mul_one := monoid.mul_one,
  left_distrib := distrib.left_distrib,
  right_distrib := distrib.right_distrib,
  zero_ne_one := (filter_product.zo _ _ U).zero_ne_one,  
  inv := has_inv.inv,
  mul_inv_cancel := λ x, quotient.induction_on' x $ λ a hx, quotient.sound' $
    have hx1 : _ := (not_imp_not.mpr quotient.eq'.mpr) hx,
    have hx2 : _ := (ultrafilter_iff_compl_mem_iff_not_mem.mp U _).mpr hx1,
    have h : {n : α | ¬a n = 0} ⊆ {n : α | a n * (a n)⁻¹ = 1} := 
      by rw [set.set_of_subset_set_of]; exact λ n, division_ring.mul_inv_cancel,
    mem_sets_of_superset hx2 h,
  inv_mul_cancel := λ x, quotient.induction_on' x $ λ a hx, quotient.sound' $
    have hx1 : _ := (not_imp_not.mpr quotient.eq'.mpr) hx,
    have hx2 : _ := (ultrafilter_iff_compl_mem_iff_not_mem.mp U _).mpr hx1,
    have h : {n : α | ¬a n = 0} ⊆ {n : α | (a n)⁻¹ * a n = 1} := 
      by rw [set.set_of_subset_set_of]; exact λ n, division_ring.inv_mul_cancel,
    mem_sets_of_superset hx2 h }

instance f [field β] (U : is_ultrafilter φ) : field β* :=
{..filter_product.cr _ _, ..filter_product.dr _ _ U}

noncomputable instance [discrete_field β] (U : is_ultrafilter φ) : discrete_field β* :=
{ add := has_add.add,
  add_assoc := add_semigroup.add_assoc,
  zero := 0,
  zero_add := add_monoid.zero_add,
  add_zero := add_monoid.add_zero,
  neg := has_neg.neg,
  add_left_neg := add_group.add_left_neg,
  add_comm := add_comm_semigroup.add_comm,
  mul := has_mul.mul,
  mul_assoc := semigroup.mul_assoc,
  one := 1,
  one_mul := monoid.one_mul,
  mul_one := monoid.mul_one,
  left_distrib := distrib.left_distrib,
  right_distrib := distrib.right_distrib,
  zero_ne_one := (filter_product.zo _ _ U).zero_ne_one,  
  inv := has_inv.inv,
  mul_inv_cancel := (filter_product.f _ _ U).mul_inv_cancel,
  inv_mul_cancel := (filter_product.f _ _ U).inv_mul_cancel,
  mul_comm := comm_ring.mul_comm,
  inv_zero := quotient.sound' $ by show _ ∈ _;
    simp only [inv_zero, eq_self_iff_true, (set.univ_def).symm, univ_sets],
  has_decidable_eq := by apply_instance }

end filter_product

end filter

section hyperreal
variables (ψ : filter ℕ) (V : filter.is_ultrafilter ψ) include V

/-- Hyperreal numbers on a general ultrafilter -/
def hypr := filter.filterprod ℝ ψ
notation `ℝ*` := hypr

end hyperreal
