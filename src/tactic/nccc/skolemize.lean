import .form

local notation  `#` := term.var
local notation  `&` := term.fnc
local notation  t1 `^*` t2 := term.app t1 t2

local notation  `⊤*` := form.true
local notation  `⊥*` := form.false
local notation  `⟪` l `⟫` := form.lit l
local notation  p `∧*` q := form.and p q
local notation  p `∨*` q := form.or p q
local notation  `∀*` := form.fa
local notation  `∃*` := form.ex

def skolemize_core : nat → form → (nat × form)
| k ⊤*       := (k, ⊤*)
| k ⊥*       := (k, ⊥*)
| k ⟪l⟫      := (k, ⟪l⟫)
| k (p ∨* q) :=
  let (m, p') := skolemize_core k p in
  let (n, q') := skolemize_core m q in
  (n, p' ∨* q')
| k (p ∧* q) :=
  let (m, p') := skolemize_core k p in
  let (n, q') := skolemize_core m q in
  (n, p' ∧* q')
| k (∀* p) :=
  let (m, p') := skolemize_core k p in
  let ts := (free_vars 1 p).map (term.fnc ∘ nat.pred) in
  (m + 1, p'.subst 0 (term.mk_app (& m) ts))
| k (∃* p) :=
  let (m, p') := skolemize_core k p in
  (m, ∃* p')

def skolemize (p : form) : form :=
let k := fresh_sdx p in
let (_,p') := skolemize_core k p in
p'

-- lemma valid_skolemize_core_imp (α : Type) (p : form) :

lemma valid_skolemize_imp (α : Type) (p : form) :
  (skolemize p).valid α → p.valid α := sorry
