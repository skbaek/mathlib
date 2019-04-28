import .swap

variable {α : Type}

local notation f `₀↦` a := assign a f
local notation `#`      := term₂.var
local notation a `&` b  := term₂.app a b

postfix  `ₑ` : 1000 := evaluate
postfix  `ᵈ` : 1000 := denote
local infix `⬝`     := value.app

local notation `⟪` b `,` a `⟫` := form₂.lit b a
local notation p `∨₂` q        := form₂.bin tt p q
local notation p `∧₂` q        := form₂.bin ff p q
local notation `∃₂`            := form₂.qua tt
local notation `∀₂`            := form₂.qua ff

open nat

def nary (α : Type) : bool → nat → Type
| ff 0       := α
| tt 0       := Prop
| b  (n + 1) := α → (nary b n)

def nary.val [inhabited α] : ∀ {b : bool} {k : nat}, nary α b k → value α
| ff 0       f []        := (f, false)
| tt 0       f []        := (default α, f)
| _  (k + 1) f []        := (default α, false)
| _  0       f (_ :: _)  := (default α, false)
| ff (k + 1) f (a :: as) := @nary.val ff k (f a) as
| tt (k + 1) f (a :: as) := @nary.val tt k (f a) as

def term₂.arity (k : nat) : term₂ → option (bool × nat)
| (# m)   := if k = m then some (tt, 0) else none
| (t & s) :=
  (t.arity >>= λ x, some $ if x.fst then (x.fst, x.snd + 1) else x) <|>
  (prod.map (λ _, ff) id <$> s.arity)

def term₂.arity_app {k : nat} {t s : term₂} :
  (t & s).arity k =
  ((t.arity k >>= λ x, some $ if x.fst then (x.fst, x.snd + 1) else x) <|>
   (prod.map (λ _, ff) id <$> s.arity k)) := rfl

def form₂.arity_core : nat → form₂ → option (bool × nat)
| k ⟪b, t⟫            := t.arity k
| k (form₂.bin _ p q) := p.arity_core k <|> q.arity_core k
| k (form₂.qua _ p)   := p.arity_core (k + 1)

def form₂.arity (k : nat) (p : form₂) : bool × nat :=
option.get_or_else (p.arity_core k) (ff, 0)

def option.if_is_some (p : α → Prop) : option α → Prop
| none     := true
| (some a) := p a

open option

lemma term₂.arity_eq_const_of_fov (k : nat) :
  ∀ (t : term₂), t.fov k → if_is_some ((=) (ff, 0)) (t.arity k)
| (# m) h0 :=
  by { unfold term₂.arity,
       rw if_neg h0, trivial }
| (t & (# m)) h0 :=
  begin
    have h1 := term₂.arity_eq_const_of_fov t h0.left,
    unfold term₂.arity,
    cases t.arity k with x,
    { rw [none_bind, none_orelse],
      by_cases h2 : k = m,
      { rw if_pos h2,
        simp only [if_is_some, id.def, map_some, prod.map] },
      rw if_neg h2, trivial },
    rw [some_bind, some_orelse],
    cases x with b n,
    have h2 : b = ff,
    { cases h1, refl },
    have h3 : n = 0,
    { cases h1, refl },
    simp only [if_is_some, h2, h3,
      bool.coe_sort_ff, if_false]
  end
| (t & (s & r)) h0 :=
  begin
    have h1 := term₂.arity_eq_const_of_fov t h0.left,
    have h2 := term₂.arity_eq_const_of_fov (s & r) h0.right,
    rw term₂.arity_app,
    cases t.arity k with x,
    { rw [none_bind, none_orelse],
      cases term₂.arity k (s&r) with x,
      { trivial },
      cases x with b n,
      have h3 : n = 0,
      { cases h2, refl },
      simp only [if_is_some, h3,
        id.def, map_some, prod.map] },
    rw [some_bind, some_orelse],
    cases x with b n,
    have h3 : b = ff,
    { cases h1, refl },
    have h4 : n = 0,
    { cases h1, refl },
    simp only [if_is_some, h3, h4,
      bool.coe_sort_ff, if_false]
  end

lemma form₂.arity_core_eq_const_of_fov :
  ∀ (k : nat) (p : form₂), p.fov k → if_is_some ((=) (ff, 0)) (p.arity_core k)
| k ⟪b, t⟫ h0 := term₂.arity_eq_const_of_fov _ _ h0


#exit
def arifix [inhabited α] : model α → form₂ → Prop
| M ⟪tt, a⟫  :=   (a.val M []).snd
| M ⟪ff, a⟫  := ¬ (a.val M []).snd
| M (p ∨₂ q) := arifix M p ∨ arifix M q
| M (p ∧₂ q) := arifix M p ∧ arifix M q
| M (∀₂ p)   := ∀ x : nary α (p.arity 0).fst (p.arity 0).snd, arifix (M ₀↦ x.val) p
| M (∃₂ p)   := ∃ x : nary α (p.arity 0).fst (p.arity 0).snd, arifix (M ₀↦ x.val) p

lemma arifix_of_holds [inhabited α] :
  ∀ {M : model α} {p : form₂}, foq tt p → p.holds M → arifix M p
| M ⟪tt, a⟫  h0 h1 := h1
| M ⟪ff, a⟫  h0 h1 := h1
| M (p ∨₂ q) h0 h1 :=
  by { cases h0, cases h1; [`[left], `[right]];
       apply arifix_of_holds; assumption }
| M (p ∧₂ q) h0 h1 :=
  by { cases h0, cases h1, constructor;
       apply arifix_of_holds; assumption }
| M (∀₂ p)   h0 h1 := λ _, arifix_of_holds h0.right (h1 _)
| M (∃₂ p)   h0 h1 :=
  begin
    cases h1 with v h1,
    have h2 := holds_iff_holds_of_eq_except,
    unfold arifix,

  end

#exit

#exit
def univ_close_core (p : form) :
  nat → model α → Prop
| 0     M :=  p.arifix M (λ _, M.inhab)
| (k+1) M :=
  match p.symb_arity k with
  | none   := ∀ u : unit, univ_close_core k M
  | some (tt,m) :=
    ∀ r : arity α Prop m, univ_close_core k
    {M with rels  := (k ↦ r.app_list _root_.false) M.rels}
  | some (ff,m) :=
    ∀ f : arity α α m, univ_close_core k
    {M with funs := (k ↦ f.app_list M.inhab) M.funs}
  end

lemma univ_close_core_of_fam_fav (p : form) (h1 : p.fam_fav α) :
  ∀ (k : nat) (M : model α), univ_close_core p k M
| 0 M     := by apply h1
| (k+1) M :=
  begin
    unfold univ_close_core,
    cases (p.symb_arity k) with bm,
    { intro _, apply univ_close_core_of_fam_fav },
    { cases bm with b m, cases b;
      intro _; apply univ_close_core_of_fam_fav }
  end

def univ_close (α : Type) [h : inhabited α] (p : form) : Prop :=
univ_close_core p p.fresh_sdx (model.default α)

lemma univ_close_of_fam_fav [h : inhabited α] {p : form} :
  p.fam_fav α → univ_close α p :=
λ h1, univ_close_core_of_fam_fav _ h1 _ _
