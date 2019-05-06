import logic.basic --tactic.interactive init.logic

universe u

variables {α : Type u} {p q r : Prop}

namespace classical

local attribute [instance] prop_decidable

--protected lemma not_and_distrib : ¬(p ∧ q) ↔ ¬p ∨ ¬q := not_and_distrib
--
--protected lemma imp_iff_not_or : p → q ↔ ¬p ∨ q := imp_iff_not_or
--
--lemma iff_iff_not_or_and_or_not : (p ↔ q) ↔ ((¬p ∨ q) ∧ (p ∨ ¬q)) :=
--begin
--  rw [iff_iff_implies_and_implies p q],
--  simp only [imp_iff_not_or, or.comm],
--end

end classical
