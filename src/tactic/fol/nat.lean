import data.nat.basic

namespace nat

lemma succ_lt_succ_iff :
  ∀ {a b : ℕ}, a.succ < b.succ ↔ a < b :=
begin
  intros a b, apply iff.intro,
  apply lt_of_succ_lt_succ,
  apply succ_lt_succ
end

lemma succ_eq_succ (k m : nat) :
  k.succ = m.succ ↔ k = m :=
by { constructor; intro h0,
     {cases h0, refl}, rw h0 }

lemma succ_ne_succ {k m : nat} :
  k ≠ m → k.succ ≠ m.succ :=
by { intros h0 h1, apply h0,
     rwa succ_eq_succ at h1 }

lemma zero_ne_succ (k : nat) :
  0 ≠ (k + 1) := ne_of_lt (zero_lt_succ _)

def digit_to_subs : char → char
| '0' := '₀'
| '1' := '₁'
| '2' := '₂'
| '3' := '₃'
| '4' := '₄'
| '5' := '₅'
| '6' := '₆'
| '7' := '₇'
| '8' := '₈'
| '9' := '₉'
| _ := ' '

def to_subs (n : nat) : string :=
⟨n.repr.data.map digit_to_subs⟩

end nat