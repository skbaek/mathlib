
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

namespace nat

def to_subs (n : nat) : string :=
⟨n.repr.data.map digit_to_subs⟩

lemma succ_lt_succ_iff :
  ∀ {a b : ℕ}, nat.succ a < nat.succ b ↔ a < b :=
begin
  intros a b, apply iff.intro,
  apply lt_of_succ_lt_succ,
  apply succ_lt_succ
end

end nat
