import data.real.basic
import order.filter.filter_product

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

theorem epsilon_mul_omega : ε * ω = 1 := quotient.sound' $
  have h : ∀ n : ℕ, (n : ℝ)⁻¹ * ↑n = 1 ↔ (n : ℝ) ≠ 0 := λ n, 
  ⟨ λ c e, by rw [e, inv_zero, zero_mul] at c; exact zero_ne_one c,
    inv_mul_cancel ⟩,
  have r : {n : ℕ | n ≠ 0} = - {n : ℕ | n = 0} := rfl,
  have h0 : {n | n = 0} = {0} := set.ext $ λ n, (set.mem_singleton_iff).symm, 
  by show _ ∈ _; simp only [function.const, nat.cast_ne_zero, h, r, h0];
  exact compl_mem_hyperfilter_of_finite set.infinite_univ_nat (set.finite_singleton _)

end hyperreal
