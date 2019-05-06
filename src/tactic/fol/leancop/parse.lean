/- Parser for proof output from leanCoP. -/

import tactic.fol.mat

universe u

variable {α : Type u}

open list tactic

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
