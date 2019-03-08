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

instance : has_coe (α → β) β* := ⟨ seq_to_filterprod β φ ⟩

instance coe_filterprod : has_coe β β* := ⟨ to_filterprod β φ ⟩

instance [has_add β] : has_add β* :=
{ add := λ x y, quotient.lift_on₂' x y (λ a b, (quotient.mk' $ λ n, a n + b n : β*)) $
    λ a₁ a₂ b₁ b₂ h1 h2, quotient.sound' $ show _ ∈ _,
    by filter_upwards [h1, h2] λ i hi1 hi2, congr (congr_arg _ hi1) hi2 }

instance [has_zero β] : has_zero β* := { zero := to_filterprod β φ (0 : β) }

instance [has_neg β] : has_neg β* :=
{ neg := λ x, (quotient.lift_on' x (λ a, (quotient.mk' (λ n, - a n) : β*))) $
    λ a b rab, quotient.sound' $ by
    { have h : {n | a n = b n} ⊆ {n | - a n =  - b n} := 
        λ n ha, by change a n = b n at ha; simp [ha],
      exact mem_sets_of_superset rab h } }

instance [add_semigroup β] : add_semigroup β* :=
{ add_assoc := λ x y z, quotient.induction_on₃' x y z $ λ a b c, quotient.sound' $
    show {n | _+_+_ = _+(_+_)} ∈ _, by simp only [add_assoc, eq_self_iff_true]; exact φ.2, 
  ..filter_product.has_add β φ }

instance [add_monoid β] : add_monoid β* :=
{ zero_add := λ x, quotient.induction_on' x 
    (λ a, quotient.sound'(by simp only [zero_add]; apply (setoid.iseqv _).1)),
  add_zero := λ x, quotient.induction_on' x 
    (λ a, quotient.sound'(by simp only [add_zero]; apply (setoid.iseqv _).1)), 
  ..filter_product.add_semigroup β φ, 
  ..filter_product.has_zero β φ }

instance [add_comm_semigroup β] : add_comm_semigroup β* :=
{ add_comm := λ x y, quotient.induction_on₂' x y 
    (λ a b, quotient.sound' (by simp only [add_comm]; apply (setoid.iseqv _).1)), 
  ..filter_product.add_semigroup β φ }

instance [add_comm_monoid β] : add_comm_monoid β* := 
{ ..filter_product.add_comm_semigroup β φ, 
  ..filter_product.add_monoid β φ }

instance [add_group β] : add_group β* :=
{ add_left_neg := λ x, quotient.induction_on' x 
    (λ a, quotient.sound' (by simp only [add_left_neg]; apply (setoid.iseqv _).1)), 
  ..filter_product.add_monoid β φ, 
  ..filter_product.has_neg β φ }

instance [add_comm_group β] : add_comm_group β* := 
{ ..filter_product.add_comm_monoid β φ, 
  ..filter_product.add_group β φ }

instance [has_mul β] : has_mul β* :=
{ mul := λ x y, quotient.lift_on₂' x y (λ a b, (quotient.mk' $ λ n, a n * b n : β*)) $
    λ a₁ a₂ b₁ b₂ h1 h2, quotient.sound' $ show _ ∈ _,
    by filter_upwards [h1, h2] λ i hi1 hi2, congr (congr_arg _ hi1) hi2 }

instance [has_one β] : has_one β* := { one := to_filterprod β φ (1 : β) }

instance [has_inv β] : has_inv β* :=
{ inv := λ x, (quotient.lift_on' x (λ a, (quotient.mk' (λ n, (a n)⁻¹) : β*))) $
    λ a b rab, quotient.sound' $ by
    { have h : {n | a n = b n} ⊆ {n | (a n)⁻¹ = (b n)⁻¹} := 
        λ n ha, by change a n = b n at ha; simp [ha],
      exact mem_sets_of_superset rab h } }

instance [semigroup β] : semigroup β* :=
{ mul_assoc := λ x y z, quotient.induction_on₃' x y z $ λ a b c, quotient.sound' $
    show {n | _*_*_ = _*(_*_)} ∈ _, by simp only [mul_assoc, eq_self_iff_true]; exact φ.2, 
  ..filter_product.has_mul β φ }

instance [monoid β] : monoid β* :=
{ one_mul := λ x, quotient.induction_on' x 
    (λ a, quotient.sound'(by simp only [one_mul]; apply (setoid.iseqv _).1)),
  mul_one := λ x, quotient.induction_on' x 
    (λ a, quotient.sound'(by simp only [mul_one]; apply (setoid.iseqv _).1)), 
  ..filter_product.semigroup β φ,
  ..filter_product.has_one β φ }

instance [comm_semigroup β] : comm_semigroup β* :=
{ mul_comm := λ x y, quotient.induction_on₂' x y 
    (λ a b, quotient.sound' (by simp only [mul_comm]; apply (setoid.iseqv _).1)), 
  ..filter_product.semigroup β φ }

instance [comm_monoid β] : comm_monoid β* := 
{ ..filter_product.comm_semigroup β φ, 
  ..filter_product.monoid β φ }

instance [group β] : group β* :=
{ mul_left_inv := λ x, quotient.induction_on' x 
    (λ a, quotient.sound' (by simp only [mul_left_inv]; apply (setoid.iseqv _).1)), 
  ..filter_product.monoid β φ,
  ..filter_product.has_inv β φ }

instance [comm_group β] : comm_group β* := 
{ ..filter_product.comm_monoid β φ, 
  ..filter_product.group β φ }

instance [distrib β] : distrib β* :=
{ left_distrib := λ x y z, quotient.induction_on₃' x y z 
    (λ x y z, quotient.sound' (by simp only [left_distrib]; apply (setoid.iseqv _).1)),
  right_distrib := λ x y z, quotient.induction_on₃' x y z 
    (λ x y z, quotient.sound' (by simp only [right_distrib]; apply (setoid.iseqv _).1)), 
  ..filter_product.has_add β φ,
  ..filter_product.has_mul β φ }

instance [mul_zero_class β] : mul_zero_class β* :=
{ zero_mul := λ x, quotient.induction_on' x 
    (λ a, quotient.sound' (by simp only [zero_mul]; apply (setoid.iseqv _).1)),
  mul_zero := λ x, quotient.induction_on' x 
    (λ a, quotient.sound' (by simp only [mul_zero]; apply (setoid.iseqv _).1)), 
  ..filter_product.has_mul β φ,
  ..filter_product.has_zero β φ }

instance [semiring β] : semiring β* := 
{ ..filter_product.add_comm_monoid β φ, 
  ..filter_product.monoid β φ, 
  ..filter_product.distrib β φ, 
  ..filter_product.mul_zero_class β φ }

instance [ring β] : ring β* := 
{ ..filter_product.add_comm_group β φ, 
  ..filter_product.monoid β φ, 
  ..filter_product.distrib β φ }

instance [comm_semiring β] : comm_semiring β* := 
{ ..filter_product.semiring β φ, 
  ..filter_product.comm_monoid β φ }

instance [comm_ring β] : comm_ring β* := 
{ ..filter_product.ring β φ, 
  ..filter_product.comm_semigroup β φ }

instance [zero_ne_one_class β] (U : is_ultrafilter φ) : zero_ne_one_class β* :=
{ zero_ne_one := by
  { intro c, have c' : _ := quotient.exact' c, 
    change _ ∈ _ at c', 
    simp only [set.set_of_false, zero_ne_one, empty_in_sets_eq_bot] at c', 
    apply U.1 c' },
  ..filter_product.has_zero β φ, 
  ..filter_product.has_one β φ }

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
  ..filter_product.ring β φ, 
  ..filter_product.has_inv β φ, 
  ..filter_product.zero_ne_one_class β φ U }

instance [field β] (U : is_ultrafilter φ) : field β* :=
{ ..filter_product.comm_ring β φ, 
  ..filter_product.division_ring β φ U }

noncomputable instance [discrete_field β] (U : is_ultrafilter φ) : discrete_field β* :=
{ inv_zero := quotient.sound' $ by show _ ∈ _;
    simp only [inv_zero, eq_self_iff_true, (set.univ_def).symm, univ_sets],
  has_decidable_eq := by apply_instance, 
  ..filter_product.field β φ U }

end filter_product

end filter

section hyperreal
variables (ψ : filter ℕ) (V : filter.is_ultrafilter ψ) include V

/-- Hyperreal numbers on a general ultrafilter -/
def hyperreal := filter.filterprod ℝ ψ
notation `ℝ*` := hyperreal

end hyperreal
