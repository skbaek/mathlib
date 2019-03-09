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
⟨ λ a b, {n | a n = b n} ∈ φ,
  λ a, by simp only [eq_self_iff_true, (set.univ_def).symm, univ_sets], 
  λ a b ab, by simpa only [eq_comm], 
  λ a b c ab bc, sets_of_superset φ (inter_sets φ ab bc) 
    (λ n (r : a n = b n ∧ b n = c n), eq.trans r.1 r.2)⟩

/-- Ultraproduct, but on a general filter -/
def filterprod := quotient (bigly_equal β φ)
local notation `β*` := filterprod β φ

namespace filter_product

variables {α β φ} include α β φ

def of_seq : (α → β) → β* := @quotient.mk' (α → β) (bigly_equal β φ)

/-- Equivalence class containing the constant sequence of a term in β -/
def of (b : β): β* := of_seq (function.const _ b)

/-- Lift function to filter product -/
def lift (f : β → β) : β* → β* :=
  λ x, quotient.lift_on' x (λ a, (quotient.mk' $ λ n, f (a n) : β*)) $
  λ a b h, quotient.sound' $ show _ ∈ _, by filter_upwards [h] λ i hi, congr_arg _ hi

/-- Lift binary operation to filter product -/
def lift₂ (f : β → β → β) : β* → β* → β* :=
  λ x y, quotient.lift_on₂' x y (λ a b, (quotient.mk' $ λ n, f (a n) (b n) : β*)) $
  λ a₁ a₂ b₁ b₂ h1 h2, quotient.sound' $ show _ ∈ _,
  by filter_upwards [h1, h2] λ i hi1 hi2, congr (congr_arg _ hi1) hi2

theorem of_inj (NT : φ ≠ ⊥): function.injective (@of _ β φ) :=
begin
  intros r s rs, by_contra N,
  rw [of, of, of_seq, quotient.eq', bigly_equal] at rs, 
  simp only [N, set.set_of_false, empty_in_sets_eq_bot] at rs,
  exact NT rs
end

instance coe_filterprod : has_coe β β* := ⟨ of ⟩

instance [has_add β] : has_add β* := { add := lift₂ has_add.add }

instance [has_zero β] : has_zero β* := { zero := of 0 }

instance [has_neg β] : has_neg β* :=
{ neg := lift has_neg.neg }

instance [add_semigroup β] : add_semigroup β* :=
{ add_assoc := λ x y z, quotient.induction_on₃' x y z $ λ a b c, quotient.sound' $
    show {n | _+_+_ = _+(_+_)} ∈ _, by simp only [add_assoc, eq_self_iff_true]; exact φ.2, 
  ..filter_product.has_add }

instance [add_monoid β] : add_monoid β* :=
{ zero_add := λ x, quotient.induction_on' x 
    (λ a, quotient.sound'(by simp only [zero_add]; apply (setoid.iseqv _).1)),
  add_zero := λ x, quotient.induction_on' x 
    (λ a, quotient.sound'(by simp only [add_zero]; apply (setoid.iseqv _).1)), 
  ..filter_product.add_semigroup, 
  ..filter_product.has_zero }

instance [add_comm_semigroup β] : add_comm_semigroup β* :=
{ add_comm := λ x y, quotient.induction_on₂' x y 
    (λ a b, quotient.sound' (by simp only [add_comm]; apply (setoid.iseqv _).1)), 
  ..filter_product.add_semigroup }

instance [add_comm_monoid β] : add_comm_monoid β* := 
{ ..filter_product.add_comm_semigroup, 
  ..filter_product.add_monoid }

instance [add_group β] : add_group β* :=
{ add_left_neg := λ x, quotient.induction_on' x 
    (λ a, quotient.sound' (by simp only [add_left_neg]; apply (setoid.iseqv _).1)), 
  ..filter_product.add_monoid, 
  ..filter_product.has_neg }

instance [add_comm_group β] : add_comm_group β* := 
{ ..filter_product.add_comm_monoid, 
  ..filter_product.add_group }

instance [has_mul β] : has_mul β* :=
{ mul := lift₂ has_mul.mul }

instance [has_one β] : has_one β* := { one := of 1 }

instance [has_inv β] : has_inv β* :=
{ inv := lift has_inv.inv }

instance [semigroup β] : semigroup β* :=
{ mul_assoc := λ x y z, quotient.induction_on₃' x y z $ λ a b c, quotient.sound' $
    show {n | _*_*_ = _*(_*_)} ∈ _, by simp only [mul_assoc, eq_self_iff_true]; exact φ.2, 
  ..filter_product.has_mul }

instance [monoid β] : monoid β* :=
{ one_mul := λ x, quotient.induction_on' x 
    (λ a, quotient.sound'(by simp only [one_mul]; apply (setoid.iseqv _).1)),
  mul_one := λ x, quotient.induction_on' x 
    (λ a, quotient.sound'(by simp only [mul_one]; apply (setoid.iseqv _).1)), 
  ..filter_product.semigroup,
  ..filter_product.has_one }

instance [comm_semigroup β] : comm_semigroup β* :=
{ mul_comm := λ x y, quotient.induction_on₂' x y 
    (λ a b, quotient.sound' (by simp only [mul_comm]; apply (setoid.iseqv _).1)), 
  ..filter_product.semigroup }

instance [comm_monoid β] : comm_monoid β* := 
{ ..filter_product.comm_semigroup, 
  ..filter_product.monoid }

instance [group β] : group β* :=
{ mul_left_inv := λ x, quotient.induction_on' x 
    (λ a, quotient.sound' (by simp only [mul_left_inv]; apply (setoid.iseqv _).1)), 
  ..filter_product.monoid,
  ..filter_product.has_inv }

instance [comm_group β] : comm_group β* := 
{ ..filter_product.comm_monoid, 
  ..filter_product.group }

instance [distrib β] : distrib β* :=
{ left_distrib := λ x y z, quotient.induction_on₃' x y z 
    (λ x y z, quotient.sound' (by simp only [left_distrib]; apply (setoid.iseqv _).1)),
  right_distrib := λ x y z, quotient.induction_on₃' x y z 
    (λ x y z, quotient.sound' (by simp only [right_distrib]; apply (setoid.iseqv _).1)), 
  ..filter_product.has_add,
  ..filter_product.has_mul }

instance [mul_zero_class β] : mul_zero_class β* :=
{ zero_mul := λ x, quotient.induction_on' x 
    (λ a, quotient.sound' (by simp only [zero_mul]; apply (setoid.iseqv _).1)),
  mul_zero := λ x, quotient.induction_on' x 
    (λ a, quotient.sound' (by simp only [mul_zero]; apply (setoid.iseqv _).1)), 
  ..filter_product.has_mul,
  ..filter_product.has_zero }

instance [semiring β] : semiring β* := 
{ ..filter_product.add_comm_monoid, 
  ..filter_product.monoid, 
  ..filter_product.distrib, 
  ..filter_product.mul_zero_class }

instance [ring β] : ring β* := 
{ ..filter_product.add_comm_group, 
  ..filter_product.monoid, 
  ..filter_product.distrib }

instance [comm_semiring β] : comm_semiring β* := 
{ ..filter_product.semiring, 
  ..filter_product.comm_monoid }

instance [comm_ring β] : comm_ring β* := 
{ ..filter_product.ring, 
  ..filter_product.comm_semigroup }

instance [zero_ne_one_class β] (NT : φ ≠ ⊥) : zero_ne_one_class β* :=
{ zero_ne_one := λ c, have c' : _ := quotient.exact' c, by
  { change _ ∈ _ at c', 
    simp only [set.set_of_false, zero_ne_one, empty_in_sets_eq_bot] at c', 
    exact NT c' },
  ..filter_product.has_zero, 
  ..filter_product.has_one }

instance [division_ring β] (U : is_ultrafilter φ) : division_ring β* :=
{ mul_inv_cancel := λ x, quotient.induction_on' x $ λ a hx, quotient.sound' $
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
    mem_sets_of_superset hx2 h, 
  ..filter_product.ring, 
  ..filter_product.has_inv, 
  ..filter_product.zero_ne_one_class U.1 }

instance [field β] (U : is_ultrafilter φ) : field β* :=
{ ..filter_product.comm_ring, 
  ..filter_product.division_ring U }

noncomputable instance [discrete_field β] (U : is_ultrafilter φ) : discrete_field β* :=
{ inv_zero := quotient.sound' $ by show _ ∈ _;
    simp only [inv_zero, eq_self_iff_true, (set.univ_def).symm, univ_sets],
  has_decidable_eq := by apply_instance, 
  ..filter_product.field U }

end filter_product

end filter

section hyperreal
variables (ψ : filter ℕ) (V : filter.is_ultrafilter ψ) include V

/-- Hyperreal numbers on a general ultrafilter -/
def hyperreal := filter.filterprod ℝ ψ
notation `ℝ*` := hyperreal

end hyperreal
