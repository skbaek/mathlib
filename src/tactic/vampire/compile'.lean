/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek

  Compilation of parsed Vampire proof output
  into inductively defined resolution proofs.
-/

import tactic.vampire.proof
import tactic.vampire.parse

open tactic

namespace vampire

open tactic

@[derive decidable_eq]
inductive inf : Type
| hyp (k : nat) : inf
| res : inf
| rot (k : nat) : inf
| sub (μ : smaps) : inf
| con : inf

namespace inf

def repr : inf → string
| (hyp k) := k.repr ++ " h"
| res     := "r"
| (rot k) := k.repr ++ " t"
| (sub μ) := μ.repr ++ " s"
| con     := "c"

instance has_repr : has_repr inf := ⟨repr⟩

meta instance has_to_format : has_to_format inf := ⟨λ x, repr x⟩

end inf

@[reducible] def infs : Type := list inf

def disjoiner (c d : cla) : smaps :=
d.vars.map (λ k, (k, sum.inl $ k + c.fresh_var))

meta def unifier : term → term → tactic smaps
| (term.sym k) (term.sym m) :=
  guard (k = m) >> return []
| (term.app t1 t2) (term.app s1 s2) :=
  do μ ← unifier t2 s2,
     ν ← unifier (t1.subst μ) (s1.subst μ),
     return (smaps.compose ν μ)
| (term.app t1 t2) (term.vpp s k) :=
  do guard (¬ k ∈ t2.vars),
     μ ← unifier (t1.subst [(k, sum.inr t2)]) (s.subst [(k, sum.inr t2)]),
     return (smaps.compose μ [(k, sum.inr t2)])
| (term.vpp t k) (term.app s1 s2) :=
  do guard (¬ k ∈ s2.vars),
     μ ← unifier (t.subst [(k, sum.inr s2)]) (s1.subst [(k, sum.inr s2)]),
     return (smaps.compose μ [(k, sum.inr s2)])
| (term.vpp t k) (term.vpp s m) :=
  do μ ← unifier (t.subst [(m, sum.inl k)]) (s.subst [(m, sum.inl k)]),
     return (smaps.compose μ [(m, sum.inl k)])
| t s := fail ("Nonunifiable terms : " ++ t.repr ++ " " ++ s.repr)

meta def unifiers (δ : smaps) (t s : term) : tactic (smaps × smaps) :=
do μ ← unifier t (s.subst δ),
   return (μ, smaps.compose μ δ)

meta def instantiator.merge_core : smaps → smaps → smaps → tactic smaps
| [] μ ν             := return (μ ++ ν)
| ((m, t) :: ξ) μ ν  :=
  match ν.find (λ x, prod.fst x = m) with
  | none := instantiator.merge_core ξ ((m, t) :: μ) ν
  | some ns :=
    if t = ns.snd
    then instantiator.merge_core ξ μ ν
    else failed
  end

meta def instantiator.merge : smaps → smaps → tactic smaps
| μ ν := instantiator.merge_core μ [] ν

meta def term.instantiator : term → term → tactic smaps
| (term.sym k) (term.sym m) :=
  guard (k = m) >> return []
| (term.app t1 t2) (term.app s1 s2) :=
  do μ ← term.instantiator t2 s2,
     ν ← term.instantiator t1 s1,
     instantiator.merge μ ν
| (term.vpp t k) (term.app s1 s2) :=
  do μ ← term.instantiator t s1,
     instantiator.merge μ [(k, sum.inr s2)]
| (term.vpp t k) (term.vpp s m) :=
  do μ ← term.instantiator t s,
     instantiator.merge μ [(k, sum.inl m)]
| _ _ := fail "RHS is not an instance of LHS"

meta def cla.instantiator : cla → cla → tactic smaps
| [] [] := return []
| ((a, t) :: c) ((b, s) :: d) :=
  if a = b
  then do μ ← term.instantiator t s,
          ν ← cla.instantiator c d,
          instantiator.merge μ ν
  else failed
| _ _ := failed

meta def find_line (k : nat) : list line → tactic line
| []                := failed
| (⟨m, c, r⟩ :: ls) :=
  if k = m
  then return ⟨m, c, r⟩
  else find_line ls

def is_dup : cla → Prop
| (l1 :: l2 :: c) := l1 = l2
| _ := false

instance is_dup.decidable : decidable_pred is_dup
| []  := is_false (λ h, by cases h)
| [_] := is_false (λ h, by cases h)
| (_ :: _ :: _) := by {unfold is_dup, apply_instance}

meta def tactic.guard (p : Prop) [decidable p] (s : string) : tactic unit :=
if p then skip else trace s >> failed

meta def allign_premises (ifs1 ifs2 : infs) :
  cla → cla → tactic (infs × infs × term × term × cla × cla)
| ((ff, t1) :: c1) ((tt, t2) :: c2) := return (ifs1, ifs2, t1, t2, c1, c2)
| ((tt, t1) :: c1) ((ff, t2) :: c2) := return (ifs2, ifs1, t2, t1, c2, c1)
| _ _ := failed

meta def rots (ifs : infs) (c : cla) : list (infs × cla) :=
(list.range c.length).map
  (λ x, (ifs ++ [inf.rot x], c.rot x))

meta def lit.unifier : lit → lit → tactic smaps
| (a, t) (b, s) :=
  if a = b
  then unifier t s
  else failed

meta def lit.instantiator : lit → lit → tactic smaps
| (a, t) (b, s) :=
  if a = b
  then term.instantiator t s
  else failed

meta def compute_map (d : cla) :
  cla → smaps → list nat → nat → tactic (smaps × list nat)
| [] μ ns _ :=
  if ∀ x < d.length, x ∈ ns
  then return (μ, ns.reverse)
  else failed
| (_ :: _) _ _ 0 := failed
| (a :: c) μ ns (k + 1) :=
  ( do b ← d.nth k,
       ν ← lit.instantiator a b,
       ξ ← instantiator.merge μ ν,
       compute_map c ξ (k :: ns) d.length ) <|>
  ( compute_map (a :: c) μ ns k )

def index_of' {α : Type} [decidable_eq α] (a : α) : list α → option nat
| []        := none
| (b :: as) :=
  if a = b
  then some 0
  else do k ← index_of' as,
          some (k + 1)

def remove_nth' {α : Type} : list α → ℕ → option (list α)
| []      _       := none
| (x :: xs) 0       := xs
| (x :: xs) (k + 1) :=
  do xs' ← remove_nth' xs k,
     some (x :: xs')

meta def compile_cnts_aux :
  list nat → cla → tactic (infs × list nat × cla)
| (k :: ks) (l :: c) :=
  ( do n ← index_of' k ks,
       ks' ← remove_nth' ks n,
       c'  ← remove_nth' c n,
       (ifs, ks'', c'') ← compile_cnts_aux (k :: ks') (l :: c'),
       return ((inf.rot (n + 1) :: inf.con :: ifs), ks'', c'') ) <|>
  ( return ([], k :: ks, l :: c) )
| _ _ := failed

meta def compile_cnts (d : cla) :
  nat → list nat → cla → tactic (infs × cla)
| 0 _ c :=
  do tactic.guard (list.exteq c d)
     "Contraction result not equivalent to target", -- To do : remove when compiler is reliable
     return ([], c)
| (k + 1) ks c :=
  do i ← index_of' k ks,
     (ifs1, ks', c') ← compile_cnts_aux (ks.rot i) (c.rot i),
     (ifs2, c'') ← compile_cnts k ks' c',
     return ((inf.rot i :: (ifs1 ++ ifs2)), c'')


def cons_sub : smaps → infs → infs
| [] is := is
| μ  is := inf.sub μ :: is

meta def compile_map (c d : cla) : tactic (infs × cla) :=
do let δ  := disjoiner d c,
   let cδ := c.subst δ,
   (μ, ks) ← compute_map d cδ [] [] d.length,
   let cδμ := cδ.subst μ,
   (ifs, c') ← compile_cnts d d.length ks cδμ,
   return (cons_sub δ (cons_sub μ ifs), c')

meta def compile_res (d : cla) :
  list ((infs × cla) × (infs × cla)) → tactic (infs × cla)
| [] := failed
| (((is1, c1), (is2, c2)) :: l) :=
  ( do (isl, isr, tl, tr, cl, cr) ← allign_premises is1 is2 c1 c2,
       let tcl := ((ff, tl) :: cl),
       let tcr := ((tt, tr) :: cr),
       (μ, ν) ← unifiers (disjoiner tcl tcr) tl tr,
       let isl' : infs := isl ++ [inf.sub μ],
       -- let σ2' : expr := expr.mk_app `(@proof.sub) [mx, ν.to_expr, cla.to_expr e2, σ2],
       let isr' : infs := isr ++ [inf.sub ν],
       let t    : term := tl.subst μ,
       let clμ  : cla  := cl.subst μ,
       let crν  : cla  := cr.subst ν,
       let c    : cla  := clμ ++ crν,
       (is, c') ← compile_map c d,
       return (isl' ++ isr' ++ (inf.res :: is), c') ) <|>
  ( compile_res l )

meta def compile_core : list line →
  mat → nat → cla → rule → tactic (infs × cla)
| ls m k d rule.inp :=
  let c := m.nth (k - 1) in
  do (is, c') ← compile_map c d,
     trace (inf.hyp (k - 1) :: is),
     return (inf.hyp (k - 1) :: is, c')
| ls m k d (rule.map n) :=
  do ⟨k', d', r⟩ ← find_line n ls,
     (is1, c) ← compile_core ls m k' d' r,
     (is2, c') ← compile_map c d,
     return (is1 ++ is2, c')
| ls m k d (rule.res n1 n2) :=
  do ⟨k1, d1, r1⟩ ← find_line n1 ls,
     ⟨k2, d2, r2⟩ ← find_line n2 ls,
     (is1, c1) ← compile_core ls m k1 d1 r1,
     (is2, c2) ← compile_core ls m k2 d2 r2,
     let ccs := list.product (rots is1 d1) (rots is2 d2),
     compile_res d ccs

meta def compile (m : mat) (ls : list line) : tactic infs :=
do ⟨k, [], r⟩ ← list.find (λ l, line.c l = []) ls,
   (is, _) ← compile_core ls m k [] r,
   trace "Before filter : ", trace is,
   return (is.filter (λ x, x ≠ inf.rot 0 ∧ x ≠ inf.sub []))

end vampire
