import  .misc logic.function

universe u 

variable {α : Type u}

local notation f `₀↦` a := assign a f

def value (α : Type u) : Type u := list α → (α × Prop)

def value.default [inhabited α] : value α := 
λ as, (default α, false)

def evaluate (a : α) : value α :=
λ _, (a, false)

def denote (v : value α) : α := (v []).fst

postfix  `ₑ` : 1000 := evaluate 
postfix  `ᵈ` : 1000 := denote

lemma denote_evaluate (a : α) : (a ₑ)ᵈ = a := rfl

@[reducible] def value.app (v w : value α) : value α := 
λ as, v (wᵈ :: as)

local infix `⬝` := value.app
def model (α : Type u) : Type u := nat → value α

lemma assign_app_evaluate_denote (M : model α) (v w : value α) :
  (M ₀↦ v ⬝ wᵈₑ) = (M ₀↦ v ⬝ w) := 
by ext k as; cases k; refl

namespace model 

def decr_idxs (M : model α) : model α :=
M ∘ nat.succ

end model

lemma assign_decr_idxs (M : model α) :
  (M.decr_idxs ₀↦ (M 0)) = M := 
begin
  rw function.funext_iff,
  rintro ⟨_⟩, { refl },
  simp only [model.decr_idxs, assign]
end