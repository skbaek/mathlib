import data.real.basic
import order.filter.basic
open filter

universes u v
variables {α : Type u} (β : Type v) (φ : filter α)
local attribute [instance] classical.prop_decidable

def bigly_equal : setoid (α → β) :=
⟨ λ a b, {n | a n = b n} ∈ φ,
  λ a, by simp only [eq_self_iff_true, (set.univ_def).symm, univ_sets],
  λ a b ab, by simpa only [eq_comm],
  λ a b c ab bc, sets_of_superset φ (inter_sets φ ab bc)
    (λ n (r : a n = b n ∧ b n = c n), eq.trans r.1 r.2)⟩

def filterprod := quotient (bigly_equal β φ)
local notation `β*` := filterprod β φ

def seq_to_filterprod : (α → β) → β* := @quotient.mk' (α → β) (bigly_equal β φ)

def to_filterprod : β → β* := function.comp (seq_to_filterprod β φ) (λ x n, x)

instance : has_coe (α → β) β* :=  ⟨seq_to_filterprod β φ⟩

instance coe_filterprod : has_coe β β* := ⟨to_filterprod β φ⟩

instance [has_add β] : has_add β* :=
{ add := λ x y, quotient.lift_on₂' x y (λ a b, (quotient.mk' $ λ n, a n + b n : β*)) $
    λ a₁ a₂ b₁ b₂ h1 h2, quotient.sound' $ show _ ∈ _,
    by filter_upwards [h1, h2] λ i hi1 hi2, congr (congr_arg _ hi1) hi2 }

instance [has_zero β] : has_zero β* := { zero := to_filterprod β φ (0 : β) }

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

instance acm [add_comm_monoid β] : add_comm_monoid β* := {..acs β φ, ..am β φ }

instance ag [add_group β] : add_group β* :=
{ add := has_add.add,
  add_assoc := add_semigroup.add_assoc,
  zero := 0,
  zero_add := add_monoid.zero_add,
  add_zero := add_monoid.add_zero,
  neg := λ x, (quotient.lift_on' x (λ a, (quotient.mk' (λ n, - a n) : β*)))
    (λ a b rab, quotient.sound' (by show _ ∈ _; simpa only [neg_inj'])),
  add_left_neg := λ x, quotient.induction_on' x
    (λ a, quotient.sound' (by simp only [add_left_neg]; apply (setoid.iseqv _).1)) }

instance acg [add_comm_group β] : add_comm_group β* := {..acm β φ, ..ag β φ}

instance [has_mul β] : has_mul β* :=
{ mul := λ x y, quotient.lift_on₂' x y (λ a b, (quotient.mk' $ λ n, a n * b n : β*)) $
    λ a₁ a₂ b₁ b₂ h1 h2, quotient.sound' $ show _ ∈ _,
    by filter_upwards [h1, h2] λ i hi1 hi2, congr (congr_arg _ hi1) hi2 }

instance [has_one β] : has_one β* := { one := to_filterprod β φ (1 : β) }

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

instance cm [comm_monoid β] : comm_monoid β* := {..cs β φ, ..m β φ }

instance g [group β] : group β* :=
{ mul := has_mul.mul,
  mul_assoc := semigroup.mul_assoc,
  one := 1,
  one_mul := monoid.one_mul,
  mul_one := monoid.mul_one,
  inv := λ x, (quotient.lift_on' x (λ a, (quotient.mk' (λ n, (a n)⁻¹) : β*)))
    (λ a b rab, quotient.sound' (by show _ ∈ _; simpa only [inv_inj'])),
  mul_left_inv := λ x, quotient.induction_on' x
    (λ a, quotient.sound' (by simp only [mul_left_inv]; apply (setoid.iseqv _).1)) }

instance [comm_group β] : comm_group β* := {..cm β φ, ..g β φ}

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

instance sr [semiring β] : semiring β* := { ..acm β φ, ..m β φ, ..d β φ, ..mz β φ }

instance r [ring β] : ring β* := {..acg β φ, ..m β φ, ..d β φ}

instance [comm_semiring β] : comm_semiring β* := {..sr β φ, ..cm β φ}

instance [comm_ring β] : comm_ring β* := {..r β φ, ..cs β φ}

section ultraproduct
variable {U : is_ultrafilter φ} include U

theorem to_filterprod_inj : function.injective (to_filterprod β φ) :=
begin
  intros r s rs, by_contra N,
  rw [to_filterprod, seq_to_filterprod, quotient.eq', bigly_equal] at rs,
  simp only [N, set.set_of_false, empty_in_sets_eq_bot] at rs,
  exact U.1 rs
end

instance [zero_ne_one_class β] : zero_ne_one_class β* :=
{ zero := 0,
  one := 1,
  zero_ne_one := by
  { intro c, have c' : _ := quotient.exact' c,
    change _ ∈ _ at c',
    simp only [set.set_of_false, zero_ne_one, empty_in_sets_eq_bot] at c',
    apply U.1 c' } }

end ultraproduct

section hyperreal
variables (ψ : filter ℕ) {V : is_ultrafilter ψ}

@[reducible] def hypr := filterprod ℝ ψ
notation `ℝ*` := hypr

end hyperreal
