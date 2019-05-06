import .misc .mat

universes u v
variables {α β : Type}

local notation  `&`     := term.sym
local notation  t `&` s := term.app t s
local notation  t `#` k := term.vpp t k

meta def clax : Type := list expr
meta def subx : Type := list (nat × expr)

meta def subx.ground_aux : (nat × expr) → tactic (nat × expr)
| (k, x) :=
  do x' ← tactic.instantiate_mvars x,
     return (k, x')

meta def subx.ground : subx → tactic subx :=
monad.mapm subx.ground_aux

meta def mapx.to_format : (nat × expr) → format
| ⟨k, x⟩ := k.repr ++ " ↦ " ++ to_fmt x

meta instance clax.has_to_format : has_to_format clax :=
⟨@list.to_format _  ⟨to_fmt⟩⟩

meta instance subx.has_to_format : has_to_format subx :=
⟨@list.to_format _  ⟨mapx.to_format⟩⟩

meta def termx.eval : expr → tactic term
| `(term.sym %%kx) :=
  do k ← tactic.eval_expr nat kx,
     return (term.sym k)
| `(term.app %%tx %%sx) :=
  do t ← termx.eval tx,
     s ← termx.eval sx,
     return (term.app t s)
| `(term.vpp %%tx %%kx) :=
  do k ← tactic.eval_expr nat kx,
     t ← termx.eval tx,
     return (term.vpp t k)
| (expr.mvar _ _ _) := return (term.sym 0)
| _ := tactic.failed

meta def subx.eval : subx → tactic sub
| []             := return []
| ((k, x) :: σx) :=
  do a ← termx.eval x,
     σ ← subx.eval σx,
     return ((k, a) :: σ)

@[reducible] meta def sgoal : Type := clax × clax × mat


meta def sgoal.to_format : sgoal → format
| (Px, Cx, M) :=
  "(" ++
  "Path : " ++ Px.to_format ++
  ", Clause : " ++ Cx.to_format ++
  ", Matrix : " ++ M.to_format ++
  ")"

meta instance sgoal.has_to_format : has_to_format sgoal := ⟨sgoal.to_format⟩

meta inductive rulex : Type
| red : nat → rulex
| ext : nat → nat → subx → rulex

meta def rulex.to_format : rulex → format
| (rulex.red k)     := "Red " ++ k.repr
| (rulex.ext j i σ) := "Ext " ++ j.repr ++ " " ++ i.repr ++ " " ++ to_fmt σ

meta instance rulex.has_to_format : has_to_format rulex := ⟨rulex.to_format⟩

meta structure search_state :=
(max : nat)
(lim : nat)
(sgoals : list sgoal)
(rulexs : list rulex)

meta def search_state.to_format : search_state → format
| ⟨m, l, gs, rs⟩ :=
  "Max : " ++ m.repr ++ "\n" ++
  "Lim : " ++ l.repr ++ "\n" ++
  "S-Goals : " ++ gs.to_format ++ "\n" ++
  "rulexs : " ++ rs.to_format ++ "\n"

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
meta def get_rulexs : search (list rulex) := search_state.rulexs <$> get

meta def set_max (m : nat) : search unit := modify $ λ s, {max := m, .. s}
meta def set_lim (l : nat) : search unit := (modify $ λ s, {lim := l, .. s})
meta def set_goals (gs : list sgoal) : search unit := modify $ λ s, {sgoals := gs, .. s}
meta def set_rulexs (rs : list rulex) : search unit := modify $ λ s, {rulexs := rs, .. s}

meta def pop_goal : search sgoal :=
do (g::gs) ← get_sgoals,
   set_goals gs,
   return g

meta def push_goal (g : sgoal) : search unit :=
do gs ← get_sgoals,
   set_goals (g::gs)

meta def push_rulex (r : rulex) : search unit :=
do rs ← get_rulexs,
   set_rulexs (r::rs)

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
     tx ← tactic.mk_meta_var `(term),
     return ((k,tx)::sx)

meta def termx.mk_aux (tx : expr) (k : nat) : subx → expr
| []          := `(%%tx # %%`(k))
| ((m,sx)::σ) :=
  if k = m then `(%%tx & %%sx) else termx.mk_aux σ

meta def termx.mk (σ : subx) : term → expr
| (& k)   := `(& k)
| (t & s) := `(%%(termx.mk t) & %%(termx.mk s))
| (t # k) := termx.mk_aux (termx.mk t) k σ

meta def litx.mk (σ : subx) : lit → expr
| ⟨b, a⟩ := `(@prod.mk bool term %%`(b) %%(termx.mk σ a))

meta def report (s : string) : search unit :=
do trace s,
   gs ← get_sgoals,
   match gs with
   | [] := trace "No goals"
   | (⟨P, C, M⟩ :: gs') :=
     do trace gs.length,
        trace " goals, ",
        trace C.length,
        trace " lits in top goal clause"
   end

meta def top_cla_count (s : string) : search unit :=
do trace s,
   ( do (⟨_, C, _⟩ :: _) ← get_sgoals,
        trace C.length ) <|> (trace "No goals")

meta def goal_count (s : string) : search unit :=
do trace s,
   gs ← get_sgoals,
   trace gs.length

meta def pick_cla_aux (M : mat) (k : nat) : search unit :=
match M.rotate k with
| []        := failed
| (C :: M') :=
  if cla.is_pos C
  then do σ ← state_t.lift (subx.mk $ C.vdxs),
          push_goal ([], C.map (litx.mk σ), if σ = [] then M' else M),
          push_rulex (rulex.ext k 0 σ)
  else failed
end

meta def pick_cla : search (backtrack unit) :=
do (_, _, M) ← pop_goal,
   return (pick_cla_aux M, M.length)

meta def negx.mk : expr → search expr
| `(@prod.mk bool term %%bx %%ax) :=
  return `(@prod.mk bool term (bnot %%bx) %%ax)
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
     push_rulex (rulex.red k)
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
       push_rulex (rulex.ext j i σ)
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
( (reduce >>> loop) <|> (extend >>> loop) <|>
  (close >> loop)   <|> finish )

meta def main : search unit :=
pick_lim >>> pick_cla >>> loop

meta def mk_search_state (M : mat) (l : nat := M.length)
  (m : nat := l * 2) : tactic search_state :=
return ⟨m, l, [⟨[], [], M⟩], []⟩

end search

meta def derive (M : mat) : tactic (list rulex) :=
(list.reverse ∘ search_state.rulexs) <$> prod.snd <$>
  (search.mk_search_state M >>= @state_t.run search_state tactic unit search.main)

def socrates : mat :=
  [[⟨tt, (& 0) & (& 0)⟩, ⟨tt, (& 0) & (& 0)⟩],
   [⟨ff, (& 0) & (& 0)⟩, ⟨ff, (& 0) & (& 0)⟩]]

run_cmd derive socrates >>= tactic.trace
