import tactic.fol.mat

universe u

variable {α : Type u}

open list tactic

def mat.size : mat → nat
| []       := 0
| (c :: m) := mat.size m + c.length + 1

def blocked : mat → cla → bool
| []              := λ _, ff
| ([] :: _)       := λ _, tt
| ((l :: c) :: m) := λ p,
  have mat.size (c :: m) < mat.size ((l :: c) :: m) := nat.lt_succ_self _,
  have mat.size m < mat.size ((l :: c) :: m) :=
  nat.lt_of_le_of_lt (nat.le_add_right _ c.length)
    (nat.lt_trans (nat.lt_succ_self _) (nat.lt_succ_self _)),
  if blocked (c :: m) p
  then if l.neg ∈ p
       then tt
       else blocked m (l :: p)
  else false
using_well_founded {
  dec_tac := tactic.assumption,
  rel_tac := λ _ _, `[exact ⟨measure mat.size, measure_wf mat.size⟩]
}

lemma holds_of_blocked (M : model α) (v : vas α) :
  ∀ m : mat, ∀ p : cla, (∀ l ∈ p, ¬ lit.holds M v l) →
  blocked m p = tt → m.holds M v
| []              _ _  h1 := by cases h1
| ([] :: _)       _ _  _  := ⟨_, or.inl rfl, list.ball_nil _⟩
| ((l :: c) :: m) p h0 h2 :=
  begin
    cases h3 : (blocked (c :: m) p),
    { simpa only [blocked, h3, bool.coe_sort_ff, if_false] using h2 },
    by_cases h4 : l.neg ∈ p,
    { have h5 : mat.holds M v (c :: m),
      { apply holds_of_blocked _ _ h0, rw h3,  },
      rcases h5 with ⟨d, h5 | h5, h6⟩,
      { refine ⟨_, or.inl rfl, λ x h7, _⟩,
        cases h7 with h7 h7,
        { apply classical.by_contradiction,
          have h8 := h0 _ h4,
          simpa only [lit.holds_neg, h7] using h8 },
        apply h6, rwa ← h5 at h7 },
        refine ⟨d, or.inr h5, h6⟩ },
    have h5 : blocked m (l :: p) = tt,
    { simpa only [blocked, h3, h4, bool.to_bool_false,
      if_true, bool.coe_sort_tt, if_false] using h2 },
    cases (classical.em (l.holds M v)) with h6 h6,
    { rcases holds_of_blocked (c :: m) p h0 h3 with ⟨d, h7 | h7, h8⟩,
      { refine ⟨_, or.inl rfl, _⟩, rw ← h7,
        apply (ball_cons (lit.holds M v) l d).elim_right ⟨h6, h8⟩ },
      refine ⟨d, or.inr h7, h8⟩ },
    have h7 : ∀ x ∈ (l :: p), ¬ lit.holds M v x,
    { apply (ball_cons (λ y, ¬ lit.holds M v y) l p).elim_right ⟨h6, h0⟩ },
    have h8 := holds_of_blocked m (l :: p) h7 h5,
    apply (bex_cons _ _ _).elim_right (or.inr h8),
  end

lemma valid_of_blocked {m : mat} :
  blocked m [] = tt → m.valid α :=
by { intros h0 M v,
     apply holds_of_blocked _ _ _ _ _ h0,
     apply @ball_nil _ (λ x, ¬ lit.holds M v x) }

def lex_core : list char → bool → list (list char) → list (list char)
| []        _ ts := (ts.map reverse).reverse
| (c :: cs) _ [] :=
  if c = ' '
  then lex_core cs ff []
  else lex_core cs tt [[c]]
| (c :: cs) b (t :: ts) :=
  if c = ' '
  then lex_core cs ff (t :: ts)
  else if b
       then lex_core cs tt ((c :: t) :: ts)
       else lex_core cs tt ([c] :: t :: ts)

def lex (s : string) : list string :=
(lex_core s.data ff []).map string_imp.mk

meta def term.parse : list string → tactic (term × list string)
| []           := failed
| ("(" :: tks) :=
  do (t, tks1) ← term.parse tks,
     (s, tks2) ← term.parse tks1,
     match tks2 with
     | (")" :: tks3) := return (term.app t s, tks3)
     | _             := failed
     end
| (tk :: tks) := return (term.sym tk.to_nat, tks)

meta def lit.parse : list string → tactic (lit × list string)
| [] := failed
| ("-" :: tks) :=
  do (t, tks1) ← term.parse tks,
     return ((ff, t), tks1)
| (tk :: tks) :=
  do (t, tks1) ← term.parse (tk :: tks),
     return ((tt, t), tks1)

meta def cla.parse : list string → tactic (cla × list string)
| []           := failed
| ("|" :: tks) := return ([], tks)
| (tk :: tks) :=
  do (l, tks1) ← lit.parse (tk :: tks),
     (c, tks2) ← cla.parse tks1,
     return ((l :: c), tks2)

meta def mat.parse : list string → tactic mat
| []          := return []
| (tk :: tks) :=
  do (c, tks1) ← cla.parse (tk :: tks),
     m ← mat.parse tks1,
     return (c :: m)
