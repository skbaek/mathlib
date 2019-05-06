import data.nat.basic

namespace nat

lemma succ_lt_succ_iff :
  ∀ {a b : ℕ}, a.succ < b.succ ↔ a < b :=
begin
  intros a b, apply iff.intro,
  apply lt_of_succ_lt_succ,
  apply succ_lt_succ
end

lemma succ_eq_succ_iff (k m : nat) :
  k.succ = m.succ ↔ k = m :=
by { constructor; intro h0,
     {cases h0, refl}, rw h0 }

lemma succ_ne_succ {k m : nat} :
  k ≠ m → k.succ ≠ m.succ :=
by { intros h0 h1, apply h0,
     rwa succ_eq_succ_iff at h1 }

lemma zero_ne_succ (k : nat) :
  0 ≠ (k + 1) := ne_of_lt (zero_lt_succ _)

end nat
