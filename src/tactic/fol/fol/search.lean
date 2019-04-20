import .misc .mat

universes u v
variables {α β : Type}

local notation  `⅋`   := atom.sym
local notation  t `&` s := atom.app t s
local notation  t `#` k := atom.vpp t k

meta def clax : Type := list expr
meta def subx : Type := list (nat × expr)

meta def subx.eval : subx → tactic sub
| []             := return []
| ((k, x) :: σx) :=
  do a ← tactic.eval_expr atom x,
     σ ← subx.eval σx,
     return ((k, a) :: σ)

@[reducible] meta def sgoal : Type := clax × clax × mat

meta inductive rule : Type
| red : nat → rule
| ext : nat → nat → subx → rule

meta def sgoal.to_format : sgoal → format
| (Px, Cx, M) :=
  "(" ++
  "Path : " ++ Px.to_format ++
  ", Clause : " ++ Cx.to_format ++
  ", Matrix : " ++ M.to_format ++
  ")"

meta instance sgoal.has_to_format : has_to_format sgoal := ⟨sgoal.to_format⟩

meta def rule.to_format : rule → format
| (rule.red k)     := "Red " ++ k.repr
| (rule.ext j i σ) := "Ext " ++ j.repr ++ " " ++ i.repr ++ " _"

meta instance rule.has_to_format : has_to_format rule := ⟨rule.to_format⟩

meta structure search_state :=
(max : nat)
(lim : nat)
(sgoals : list sgoal)
(rules : list rule)

meta def search_state.to_format : search_state → format
| ⟨m, l, gs, rs⟩ :=
  "Max : " ++ m.repr ++ "\n" ++
  "Lim : " ++ l.repr ++ "\n" ++
  "S-Goals : " ++ gs.to_format ++ "\n" ++
  "Rules : " ++ rs.to_format ++ "\n"

meta instance search_state.has_to_format : has_to_format search_state :=
⟨search_state.to_format⟩

@[reducible] meta def search := state_t search_state tactic

meta def search.failed {α : Type} : search α := ⟨λ x, tactic.failed⟩

meta def search.skip : search unit := ⟨λ x, return ⟨(), x⟩⟩

meta def option.to_search : option α → search α
| none     := search.failed
| (some a) := return a

namespace search

meta def get_max : search nat := search_state.max <$> get
meta def get_lim : search nat := search_state.lim <$> get
meta def get_sgoals : search (list sgoal) := search_state.sgoals <$> get
meta def get_rules : search (list rule) := search_state.rules <$> get

meta def set_max (m : nat) : search unit := modify $ λ s, {max := m, .. s}
meta def set_lim (l : nat) : search unit := (modify $ λ s, {lim := l, .. s})
meta def set_goals (gs : list sgoal) : search unit := modify $ λ s, {sgoals := gs, .. s}
meta def set_rules (rs : list rule) : search unit := modify $ λ s, {rules := rs, .. s}

meta def pop_goal : search sgoal :=
do (g::gs) ← get_sgoals,
   set_goals gs,
   return g

meta def print [has_to_tactic_format α] (a : α) : search unit :=
state_t.lift (tactic.trace a)

meta def push_goal (g : sgoal) : search unit :=
do gs ← get_sgoals,
   set_goals (g::gs)

meta def push_rule (r : rule) : search unit :=
do rs ← get_rules,
   set_rules (r::rs)

meta def backtrack (α : Type) : Type := (nat → search α) × nat

@[reducible] meta def bsearch (α : Type) : Type := search (backtrack α)

meta def bbind_core : backtrack α → (α → search β) → search β
| (s, 0)     t := failed
| (s, k + 1) t := (s k >>= t) <|> (bbind_core (s, k) t)

meta def bbind (b : bsearch α) (s : α → search β) : search β :=
b >>= λ x, bbind_core x s
infixr `>>>=` : 1100 := bbind

meta def bthen (b : bsearch α) (s : search β) : search β :=
b >>>= (λ _, s)

infixr `>>>` : 1100 := bthen

meta def trace {α : Type u} [has_to_tactic_format α] (a : α) : search unit :=
state_t.lift (tactic.trace a)

meta def pick_lim : search (backtrack unit) :=
do m ← get_max,
   l ← get_lim,
   return (λ x, set_lim (m - x), (m - l) + 1)

meta def subx.mk : list nat → tactic subx
| []      := return []
| (k::ks) :=
  do sx ← subx.mk ks,
     tx ← tactic.mk_meta_var `(atom),
     return ((k,tx)::sx)

meta def atomx.mk_aux (tx : expr) (k : nat) : subx → expr
| []          := `(%%tx # %%`(k))
| ((m,sx)::σ) :=
  if k = m then `(%%tx & %%sx) else atomx.mk_aux σ

meta def atomx.mk (σ : subx) : atom → expr
| (⅋ k)   := `(⅋ k)
| (t & s) := `(%%(atomx.mk t) & %%(atomx.mk s))
| (t # k) := atomx.mk_aux (atomx.mk t) k σ

meta def litx.mk (σ : subx) : lit → expr
| ⟨b, a⟩ := `(@prod.mk bool atom %%`(b) %%(atomx.mk σ a))

meta def pick_cla_aux (M : mat) (k : nat) : search unit :=
match M.rotate k with
| []        := failed
| (C :: M') :=
  if cla.is_pos C
  then do σ ← state_t.lift (subx.mk $ C.vdxs),
          push_goal ([], C.map (litx.mk σ), if σ = [] then M' else M),
          push_rule (rule.ext k 0 σ)
  else failed
end

meta def pick_cla : search (backtrack unit) :=
do (_, _, M) ← pop_goal,
   return (pick_cla_aux M, M.length)

meta def negx.mk : expr → search expr
| `(@prod.mk bool atom %%bx %%ax) :=
  return `(@prod.mk bool atom (bnot %%bx) %%ax)
| _ := failed

meta def comp_unify (L N : expr): search unit :=
do negL ← negx.mk L,
   state_t.lift (tactic.unify N negL)

meta def reduce_aux (L : expr) (P C : clax) (M : mat) (k : nat) : search unit :=
match P.rotate k with
| []        := failed
| (N :: P') :=
  do comp_unify L N,
     push_goal (P,C,M),
     push_rule (rule.red k)
end

meta def reduce : bsearch unit :=
( ( do
  ⟨P, L::C, M⟩ ← pop_goal,
  return (reduce_aux L P C M, P.length) )
  : search (backtrack unit) )

def maxlen (l : list (list α)) : nat :=
(l.map list.length).max

def mat.entry (M : mat) (i j : nat) : option lit :=
do C ← M.nth j, C.nth i

meta def extend_aux (Lx : expr) (Px Cx : clax) (M : mat) (km : nat) : search unit :=
let i : nat := km % maxlen M in
let j : nat := km / maxlen M in
match M.rotate j with
| [] := failed
| (D :: M') :=
  match D.rotate i with
  | [] := failed
  | (N :: D') :=
    do σ ← state_t.lift (subx.mk $ D.vdxs),
       comp_unify Lx (litx.mk σ N),
       push_goal (Lx :: Px, D'.map (litx.mk σ), if σ = [] then M' else M),
       push_goal (Px, Cx, M),
       push_rule (rule.ext j i σ)
  end
end

meta def extend : bsearch unit :=
( ( do
  l ← get_lim,
  (Px, Lx::Cx, M) ← pop_goal,
  if Px.length < l
  then return (extend_aux Lx Px Cx M, M.length * maxlen M)
  else failed )
  : search (backtrack unit) )

meta def close : search unit :=
do ⟨_, [], _⟩ ← pop_goal, skip

meta def finish : search unit :=
do gs ← get_sgoals,
   if gs = [] then skip else failed

local attribute [inline] state_t.orelse

meta def loop : search unit :=
((reduce >>> loop) <|> (extend >>> loop) <|>
  (close >> loop) <|> finish)

meta def main : search unit :=
pick_lim >>> pick_cla >>> loop

meta def mk_search_state (M : mat) (l : nat := M.length)
  (m : nat := l * 2) : tactic search_state :=
return ⟨m, l, [⟨[], [], M⟩], []⟩

end search

meta def derive (M : mat) : tactic (list rule) :=
(list.reverse ∘ search_state.rules) <$> prod.snd <$>
  (search.mk_search_state M >>= @state_t.run search_state tactic unit search.main)

#exit
def socrates : mat :=
  [[⟨tt, (⅋ 0) & (⅋ 0)⟩,   ⟨tt, (⅋ 1) & (⅋ 1)⟩],
   [⟨ff, (⅋ 0) & (⅋ 0)⟩], [⟨ff, (⅋ 1) & (⅋ 1)⟩]]

run_cmd derive socrates >>= tactic.trace