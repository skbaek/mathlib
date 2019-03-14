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

lemma epsilon_pos : 0 < ε :=
have h0' : {n : ℕ | ¬ n > 0} = {0} := 
by simp only [not_lt, (set.set_of_eq_eq_singleton).symm]; ext; exact nat.le_zero_iff,
begin
  rw lt_def (is_ultrafilter_hyperfilter set.infinite_univ_nat),
  show {i : ℕ | (0 : ℝ) < i⁻¹} ∈ hyperfilter.sets,
  simp only [inv_pos', nat.cast_pos],
  exact mem_hyperfilter_of_finite_compl set.infinite_univ_nat (by convert set.finite_singleton _),
end

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

/-- Standard part predicate -/
def is_st (x : ℝ*) (r : ℝ) := ∀ δ : ℝ, δ > 0 → (r - δ : ℝ*) < x ∧ x < r + δ

/-- Standard part function -/
noncomputable def st : ℝ* → ℝ := 
λ x, dite (∃ r, is_st x r) classical.some $ λ h, 0

private lemma is_st_unique_1 (x : ℝ*) (r s : ℝ) (hr : is_st x r) (hs : is_st x s) (hrs : r < s) : false :=
have hrs' : _ := half_pos $ sub_pos_of_lt hrs,
have hr' : _ := (hr _ hrs').2,
have hs' : _ := (hs _ hrs').1,
have h : s + -((s - r) / 2) = r + (s - r) / 2 := by linarith,
by simp only [(of_eq_coe _).symm, sub_eq_add_neg (of s), (of_neg _).symm, (of_add _ _).symm, h] at hr' hs';
  exact not_lt_of_lt hs' hr'

theorem is_st_unique (x : ℝ*) (r s : ℝ) (hr : is_st x r) (hs : is_st x s) : r = s :=
begin
  rcases lt_trichotomy r s with h | h | h,
  { exact false.elim (is_st_unique_1 x r s hr hs h) },
  { exact h },
  { exact false.elim (is_st_unique_1 x s r hs hr h) }
end

end hyperreal
