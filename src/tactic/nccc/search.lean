import .misc .mat

universes u v
variables {α β : Type}

local notation  `⅋`   := term.fnc
local notation  t `&` s := term.tpp t s
local notation  t `#` k := term.vpp t k

meta def clax : Type := list expr
meta def subx : Type := list (nat × expr)

@[reducible] meta def search.goal : Type := clax × clax × mat

meta inductive search.rule : Type
--| rot_p : nat → search.rule
--| rot_c : nat → search.rule
--| rot_m : nat → search.rule
--| start : subx → search.rule
| red   : nat → search.rule
| ext   : nat → nat → subx → search.rule

meta def goal.to_format : search.goal → format
| (Px, Cx, M) :=
  "(" ++
  "Path : " ++ Px.to_format ++
  ", Clause : " ++ Cx.to_format ++
  ", Matrix : " ++ M.to_format ++
  ")"

meta instance goal.has_to_format : has_to_format search.goal := ⟨goal.to_format⟩

meta def rule.to_format : rule → format
--| (rule.rot_p k) := "Rot-P " ++ k.repr
--| (rule.rot_c k) := "Rot-C " ++ k.repr
--| (rule.rot_m k) := "Rot-M " ++ k.repr
--| (rule.start σ) := "Start " ++ " _"
| (rule.red k)     := "Red " ++ k.repr
| (rule.ext j i σ) := "Ext " ++ j.repr ++ " " ++ i.repr ++ " _"

meta instance rule.has_to_format : has_to_format rule := ⟨rule.to_format⟩

meta structure search_state :=
(max : nat)
(lim : nat)
(goals : list search.goal)
(rules : list search.rule)

meta def search_state.to_format : search_state → format
| ⟨m, l, gs, rs⟩ :=
  "Max : " ++ m.repr ++ "\n" ++
  "Lim : " ++ l.repr ++ "\n" ++
  "Goals : " ++ gs.to_format ++ "\n" ++
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
meta def get_goals : search (list goal) := search_state.goals <$> get
meta def get_rules : search (list rule) := search_state.rules <$> get

meta def set_max (m : nat) : search unit := modify $ λ s, {max := m, .. s}
meta def set_lim (l : nat) : search unit := (modify $ λ s, {lim := l, .. s})
meta def set_goals (gs : list goal) : search unit := modify $ λ s, {goals := gs, .. s}
meta def set_rules (rs : list rule) : search unit := modify $ λ s, {rules := rs, .. s}

meta def pop_goal : search goal :=
do (g::gs) ← get_goals,
   set_goals gs,
   return g

meta def print [has_to_tactic_format α] (a : α) : search unit :=
state_t.lift (tactic.trace a)

meta def push_goal (g : goal) : search unit :=
do gs ← get_goals,
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

meta def pick_lim : search (backtrack unit) :=
do m ← get_max,
   l ← get_lim,
   return (λ x, set_lim (m - x), (m - l) + 1)

meta def subx.mk : list nat → tactic subx
| []      := return []
| (k::ks) :=
  do sx ← subx.mk ks,
     tx ← tactic.mk_meta_var `(term),
     return ((k,tx)::sx)

meta def termx.mk_aux (tx : expr) (k : nat) : subx → expr
| []          := `(%%tx # %%`(k))
| ((m,sx)::σ) :=
  if k = m then `(%%tx & %%sx) else termx.mk_aux σ

meta def termx.mk (σ : subx) : term → expr
| (⅋ k)   := `(⅋ k)
| (t & s) := `(%%(termx.mk t) & %%(termx.mk s))
| (t # k) := termx.mk_aux (termx.mk t) k σ

meta def termsx.mk (σ : subx) : list term → expr
| []      := `(@list.nil term)
| (t::ts) := `(@list.cons term %%(termx.mk σ t) %%(termsx.mk ts))

meta def litx.mk (σ : subx) : lit → expr
| ⟨b, k, ts⟩ := `(lit.mk %%`(b) %%`(k) %%(termsx.mk σ ts))

meta def pick_cla_aux (M : mat) (k : nat) : search unit :=
match M.rotate k with
| []        := failed
| (C :: M') :=
  if cla.is_pos C
  then --match cla.vdxs C with
       --| []        :=
       --  do push_goal ([], C.map (litx.mk []), M'),
       --     push_rule (rule.rot_m k),
       --     push_rule (rule.start [])
       --| vs@(_::_) :=
         do σ ← state_t.lift (subx.mk $ C.vdxs),
            push_goal ([], C.map (litx.mk σ), if σ = [] then M' else M),
            push_rule (rule.ext k 0 σ)
       --end
  else failed
end

meta def pick_cla : search (backtrack unit) :=
do (_, _, M) ← pop_goal,
   return (pick_cla_aux M, M.length)

meta def negx.mk : expr → search expr
| `(lit.mk %%bx %%kx %% tsx) :=
  return `(lit.mk (bnot %%bx) %%kx %% tsx)
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
  state_t.lift (tactic.trace "Current matrix : " >> tactic.trace M),
  if Px.length < l
  then return (extend_aux Lx Px Cx M, M.length * maxlen M)
  else failed )
  : search (backtrack unit) )

meta def close : search unit :=
do ⟨_, [], _⟩ ← pop_goal, skip

meta def finish : search unit :=
do gs ← get_goals,
   if gs = [] then skip else failed

local attribute [inline] state_t.orelse

meta def loop : search unit :=
(reduce >>> loop) <|> (extend >>> loop) <|>
  (close >> loop) <|> finish

meta def main : search unit :=
pick_lim >>> pick_cla >>> loop

meta def mk_search_state (M : mat) (l : nat := M.length)
  (m : nat := l * 2) : tactic search_state :=
return ⟨m, l, [⟨[], [], M⟩], []⟩

meta def derive (M : mat) : tactic (list rule) :=
(list.reverse ∘ search_state.rules) <$> prod.snd <$>
  (mk_search_state M >>= @state_t.run search_state tactic unit main)

end search

#exit
def socrates : mat := [[⟨tt, 0, [⅋ 0]⟩, ⟨tt, 1, [⅋ 1]⟩], [⟨ff, 0, [⅋ 0]⟩], [⟨ff, 1, [⅋ 1]⟩]]

run_cmd derive socrates >>= tactic.trace
