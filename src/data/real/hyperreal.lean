/-
Copyright (c) 2019 Abhimanyu Pallavi Sudhir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhimanyu Pallavi Sudhir
Construction of the hyperreal numbers as an ultraproduct of real sequences.
-/

import data.real.basic algebra.field order.filter.filter_product

open filter filter.filter_product

/-- Hyperreal numbers on the ultrafilter extending the cofinite filter -/
@[reducible] def hyperreal := filter.filterprod ℝ (@hyperfilter ℕ)

namespace hyperreal

notation `ℝ*` := hyperreal

noncomputable instance : discrete_field ℝ* := 
filter_product.discrete_field (is_ultrafilter_hyperfilter set.infinite_univ_nat)

noncomputable instance : linear_order ℝ* :=
filter_product.linear_order (is_ultrafilter_hyperfilter set.infinite_univ_nat)

/-- A sample infinitesimal hyperreal-/
noncomputable def epsilon : ℝ* := of_seq (λ n, n⁻¹)

/-- A sample infinite hyperreal-/
noncomputable def omega : ℝ* := of_seq (λ n, n)

local notation `ε` := epsilon
local notation `ω` := omega

theorem epsilon_eq_inv_omega : ε = ω⁻¹ := rfl

theorem inv_epsilon_eq_omega : ε⁻¹ = ω := @inv_inv' _ _ ω

lemma epsilon_ne_zero : ε ≠ 0 := λ he, 
have he' : {n : ℕ | (n : ℝ)⁻¹ = 0}  ∈ _ := quotient.exact' he,
by simp only [inv_eq_zero, nat.cast_eq_zero, set.set_of_eq_eq_singleton] at he';
exact nmem_hyperfilter_of_finite set.infinite_univ_nat (set.finite_singleton _) he'

lemma omega_ne_zero : ω ≠ 0 := λ he,
have he' : {n : ℕ | (n : ℝ) = 0} ∈ _ := quotient.exact' he,
by simp only [nat.cast_eq_zero, set.set_of_eq_eq_singleton] at he';
exact nmem_hyperfilter_of_finite set.infinite_univ_nat (set.finite_singleton _) he'

theorem epsilon_mul_omega : ε * ω = 1 := quotient.sound' $
  have h : ∀ n : ℕ, (n : ℝ)⁻¹ * ↑n = 1 ↔ (n : ℝ) ≠ 0 := λ n, 
  ⟨ λ c e, by rw [e, inv_zero, zero_mul] at c; exact zero_ne_one c,
    inv_mul_cancel ⟩,
  have r : {n : ℕ | n ≠ 0} = - {n : ℕ | n = 0} := rfl,
  by show _ ∈ _; simp only [function.const, nat.cast_ne_zero, h, r, set.set_of_eq_eq_singleton];
  exact compl_mem_hyperfilter_of_finite set.infinite_univ_nat (set.finite_singleton _)

end hyperreal
