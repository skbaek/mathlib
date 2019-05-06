import tactic.fol.mat
import tactic.fol.attempt
import data.list.basic

/- 'mat.inst m n' asserts that matrix m is an instance of matrix n. -/

universe u

variable {α : Type}

local notation `&` k   := term.sym k
local notation a `&` b := term.app a b
local notation a `#` k := term.vpp a k

def cla.inst (c d : cla) : Prop :=
  ∃ σ : sub, c = cla.subst σ d

def mat.inst (m n : mat) : Prop :=
  ∀ c ∈ m, ∃ d ∈ n, ∃ k : nat, cla.inst c (list.rotate d k)

open list

def term.find_inst : sub → term → term → option sub
| σ (& k)   (& m)   := if k = m then some σ else none
| _ (& _)   (_ & _) := none
| _ (& _)   (_ # _) := none
| _ (_ & _) (& _)   := none
| σ (r & s) (t & u) :=
  term.find_inst σ r t >>=
  λ x, term.find_inst x s u
| σ (t & s) (r # k) :=
  do σ' ← term.find_inst σ t r,
     match σ'.get k with
     | none     := some ((k, s) :: σ')
     | (some u) := if s = u then some σ' else none
     end
| _ (_ # _) (& _)   := none
| _ (_ # _) (_ & _) := none
| σ (t # k) (s # m) :=
  do σ' ← term.find_inst σ t s,
     match σ'.get m with
     | none     := if k = m then some σ' else none
     | (some u) := none
     end

def cla.find_inst : sub → cla → cla → option sub
| σ [] []       := some σ
| _ [] (_ :: _) := none
| _ (_ :: _) [] := none
| σ ((b, t) :: C) ((c, s) :: D) :=
  if b = c
  then do σ' ← term.find_inst σ t s,
          cla.find_inst σ' C D
  else none

lemma fam_exv_of_fam_exv_inst {m n : mat} :
  mat.inst m n → m.fam_exv α → n.fam_exv α :=
begin
  rintros h0 h1 M,
  rcases h1 M with ⟨v, c, h1, h2⟩,
  rcases h0 c h1 with ⟨d, h3, k, σ, h5⟩,
  rw [h5, cla.holds_subst] at h2,
  refine ⟨vas.subst M v σ, d, h3, λ l h4, _⟩,
  apply h2, rw list.mem_rotate, exact h4
end

instance attempt.inst (m n : mat) : attempt (mat.inst m n) :=
begin
  apply @list.attempt_ball _ _ (λ c, _),
  apply @list.attempt_bex _ _ (λ d, _),
  apply @attempt_ex_of_list _ _ (λ k, _) (list.range d.length),
  cases (cla.find_inst [] c (rotate d k)) with σ,
  { apply attempt.unknown },
  by_cases h0 : (c = cla.subst σ (rotate d k)),
  { left, refine ⟨σ, h0⟩ },
  apply attempt.unknown
end
