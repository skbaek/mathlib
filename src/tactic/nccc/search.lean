import .misc .mat

universes u v
variables {α β : Type}

local notation  `⅋` := term.fnc
local notation  t ` s := term.app t s

meta def clax : Type := list expr
meta def subx : Type := list (nat × expr)

@[reducible] meta def search.goal : Type := clax × clax × mat

meta inductive search.rule : Type
| start : nat → option subx → search.rule
| red   : search.rule
| ext   : nat → nat → option subx → search.rule 

-- 
-- meta def goal.to_format : goal → format 
-- | ⟨Cx, M, Px⟩ := 
--   "(Clause : " ++ Cx.to_format ++ ", Matrix : " ++ M.to_format ++ 
--   ", Path : " ++ Px.to_format ++ ")"
-- 
-- meta instance goal.has_to_format : has_to_format goal := ⟨goal.to_format⟩ 
-- 
-- 
-- meta def rule.to_format : rule → format 
-- | (rule.start k σ) := "Start " ++ k.repr ++ " _"
-- | rule.red         := "Reduction" 
-- | (rule.ext k m σ) := "Extend " ++ k.repr ++ " " ++ m.repr ++ " _"
-- 
-- meta instance rule.has_to_format : has_to_format rule := ⟨rule.to_format⟩ 

meta structure search_state :=
(max : nat)
(lim : nat)
(goals : list search.goal)
(rules : list search.rule)

-- meta def search_state.to_format : search_state → format 
-- | ⟨m, l, gs, rs⟩ := 
--   "Max : " ++ m.repr ++ "\n" ++
--   "Lim : " ++ l.repr ++ "\n" ++
--   "Goals : " ++ gs.to_format ++ "\n" ++ 
--   "Rules : " ++ rs.to_format ++ "\n" 
-- 
-- meta instance search_state.has_to_format : has_to_format search_state := 
-- ⟨search_state.to_format⟩ 

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
meta def set_lim (l : nat) : search unit := 
--state_t.lift (tactic.trace "Setting lim to : " >> tactic.trace l) >>
(modify $ λ s, {lim := l, .. s})
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

#exit
meta def subx.subst (k : nat) : subx → expr 
| []          := `(# k)
| ((m,tx)::σ) := 
  if k = m then tx else subx.subst σ 

meta def termx.mk (σ : subx) : term → expr 
| (# k)    := subx.subst k σ  
| (& k)    := `(& k)
| (t ^* s) := `(%%(termx.mk t) ^* %%(termx.mk s))

meta def termsx.mk (σ : subx) : list term → expr 
| []      := `(@list.nil term)
| (t::ts) := `(@list.cons term %%(termx.mk σ t) %%(termsx.mk ts))

meta def litx.mk (σ : subx) : lit → expr 
| ⟨b, k, ts⟩ := `(lit.mk %%`(b) %%`(k) %%(termsx.mk σ ts))

meta def pick_cla_aux (M : mat) (k : nat) : search unit := 
match M.nth k with 
| none   := failed
| some C := 
  if cla.is_pos C
  then match cla.vdxs C with
       | []        := 
         do push_goal (C.map (litx.mk []), M.erase C, []),
            push_rule (rule.start k none) 
       | vs@(_::_) := 
         do σ ← state_t.lift (subx.mk vs), 
            push_goal ⟨C.map (litx.mk σ), M, []⟩,
            push_rule (rule.start k σ) 
       end
  else failed
end

meta def pick_cla : search (backtrack unit) := 
do (_, M, _) ← pop_goal, 
   return (pick_cla_aux M, M.length)

meta def negx.mk : expr → search expr 
| `(lit.mk %%bx %%kx %% tsx) := 
  return `(lit.mk (bnot %%bx) %%kx %% tsx) 
| _ := failed

meta def comp_unify (L N : expr): search unit := 
do negL ← negx.mk L,
   state_t.lift (tactic.unify N negL)

meta def reduce_aux (L : expr) (M : mat) (C P : clax) (k : nat) : search unit :=
match P.nth k with 
| none := failed
| some N := 
  do comp_unify L N,
     push_goal (C,M,P),
     push_rule rule.red
end

meta def reduce : bsearch unit := 
( ( do 
  ⟨L::C, M, P⟩ ← pop_goal,
  return (reduce_aux L M C P, P.length) ) 
  : search (backtrack unit) )

def maxlen (l : list (list α)) : nat :=
(l.map list.length).max

def mat.entry (M : mat) (i j : nat) : option lit := 
do C ← M.nth j, C.nth i


meta def extend_aux (Lx : expr) (M : mat) (Cx Px : clax) (km : nat) : search unit := 
let i : nat := km % maxlen M in 
let j : nat := km / maxlen M in 
do D ← (M.nth j).to_search,
   match cla.vdxs D with 
   | [] :=
     let Dx := D.map (litx.mk []) in
     do Nx ← (Dx.nth i).to_search,
        comp_unify Lx Nx,
        push_goal (Dx.except i, M.except j, Lx::Px),
        push_goal (Cx, M, Px),
        push_rule (rule.ext j i none)
   | vs@(_::_) := 
     do σ ← state_t.lift (subx.mk vs), 
        Dx ← return (D.map (litx.mk σ)),
        Nx ← (Dx.nth i).to_search,
        comp_unify Lx Nx,
        push_goal (Dx.except i, M, Lx::Px),
        push_goal (Cx, M, Px),
        push_rule (rule.ext j i σ)
   end

meta def extend : bsearch unit :=  
( ( do 
  l ← get_lim,
  (Lx::Cx, M, Px) ← pop_goal,
  if Px.length < l
  then return (extend_aux Lx M Cx Px, M.length * maxlen M)  
  else failed )
  : search (backtrack unit) )

meta def close : search unit := 
do ⟨[], _, _⟩ ← pop_goal, skip

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
return ⟨m, l, [⟨[], M, []⟩], []⟩ 

meta def derive (M : mat) : tactic (list rule) := 
(list.reverse ∘ search_state.rules) <$> prod.snd <$> 
  (mk_search_state M >>= @state_t.run search_state tactic unit main)

#exit
def socrates : mat := [[⟨tt, 0, [& 0]⟩, ⟨tt, 1, [& 1]⟩], [⟨ff, 0, [& 0]⟩], [⟨ff, 1, [& 1]⟩]]

run_cmd derive socrates >>= tactic.trace