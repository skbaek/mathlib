import system.io
import logic.basic
import data.list.min_max
import tactic.vampire.reify
import tactic.vampire.cnf
import tactic.vampire.skolemize

namespace vampire

local notation `v*` := xtrm.vr
local notation `f*` := xtrm.fn
local notation `[]*` := xtrm.nil
local notation h `::*` ts  := xtrm.cons h ts
local notation `r*`     := atm.rl
local notation t `=*` s := atm.eq t s
local notation p `∨*` q := frm.bin tt p q
local notation p `∧*` q := frm.bin ff p q
local notation `∃*` p   := frm.qua tt p
local notation `∀*` p   := frm.qua ff p
local notation R `;` F `;` V `⊨` f := frm.holds R F V f

run_cmd mk_simp_attr `sugars

attribute [sugars]
  -- logical constants
  or_false  false_or
  and_false false_and
  or_true   true_or
  and_true  true_and
  -- implication elimination
  classical.imp_iff_not_or
  classical.iff_iff_not_or_and_or_not
  -- NNF
  classical.not_not
  not_exists
  not_or_distrib
  classical.not_and_distrib
  classical.not_forall

meta def desugar := `[try {simp only with sugars}]

meta def get_domain_core : expr → tactic expr
| `(¬ %%p)     := get_domain_core p
| `(%%p ∨ %%q) := get_domain_core p <|> get_domain_core q
| `(%%p ∧ %%q) := get_domain_core p <|> get_domain_core q
| `(%%p ↔ %%q) := get_domain_core p <|> get_domain_core q
| (expr.pi _ _ p q) :=
  mcond (tactic.is_prop p) (get_domain_core p <|> get_domain_core q) (return p)
| `(@Exists %%t _)  := return t
| _ := tactic.failed

meta def get_domain : tactic expr :=
(tactic.target >>= get_domain_core) <|> return `(unit)

meta def get_inhabitance (αx : expr) : tactic expr :=
do ihx ← tactic.to_expr ``(inhabited),
   tactic.mk_instance (expr.app ihx αx)

/- Same as is.fs.read_to_end and io.cmd,
   except for configurable read length. -/
def io.fs.read_to_end' (h : io.handle) : io char_buffer :=
io.iterate mk_buffer $ λ r,
  do done ← io.fs.is_eof h,
    if done
    then return none
    else do
      c ← io.fs.read h 65536,
      return $ some (r ++ c)

def io.cmd' (args : io.process.spawn_args) : io string :=
do child ← io.proc.spawn { stdout := io.process.stdio.piped, ..args },
  buf ← io.fs.read_to_end' child.stdout,
  io.fs.close child.stdout,
  exitv ← io.proc.wait child,
  when (exitv ≠ 0) $ io.fail $ "process exited with status " ++ repr exitv,
  return buf.to_string

variables {α : Type}

inductive rul
| H : nat → rul
| R : nat → nat → rul
| I : nat → vmaps → rul
| P : nat → nat → rul
| V : nat → rul
| W : nat → rul

namespace rul

def repr : rul → string
| (rul.H k)    := "H." ++ k.repr
| (rul.V k)    := "V." ++ k.repr
| (rul.W k)    := "W." ++ k.repr
| (rul.R k m)  := "R." ++ k.repr ++ "." ++ m.repr
| (rul.P k m)  := "P." ++ k.repr ++ "." ++ m.repr
| (rul.I k μs) := "I." ++ k.repr ++ "." ++ μs.repr

instance has_repr : has_repr rul := ⟨repr⟩

end rul

inductive proof (m : mat) : cla → Type
| H (k : nat) : proof (m.nth k)
| R (a : atm) (c : cla) :
  proof ((ff, a) :: c) →
  proof ((tt, a) :: c) →
  proof c
| I (μs : vmaps) (c : cla) :
  proof c → proof (c.vsubs μs)
| P (l : lit) (t s : trm) (c : cla) :
  proof (l :: c) →
  proof (((tt, t =* s) :: c)) →
  proof (l.replace t s :: c)
| V (t : trm) (c : cla) :
  proof ((ff, t =* t) :: c) → proof c
| W (c d : cla) :
  cla.subsumes c d → proof c → proof d

variables {R : rls α} {F : fns α} {V : vas α}
variables {b : bool} (f g : frm)

lemma holds_cla_of_proof {m : mat}
  (h0 : ∀ V : vas α, m.holds R F V) :
  ∀ {c : cla}, proof m c →
  (∀ V : vas α, c.holds R F V) :=
begin
  intros c π,
  induction π with
    k
    t c π1 π2 h1 h2
    μs c π h1
    l t s c π σ h1 h2
    t d h1 h2
    c d h1 π h2 ,
  { unfold mat.nth,
    cases h1 : list.nth m k;
    unfold option.get_or_else,
    { apply holds_tautology },
    intro V, apply h0,
    apply list.mem_iff_nth.elim_right,
    refine ⟨_, h1⟩ },
  { intro V,
    rcases h1 V with ⟨la, hla1 | hla1, hla2⟩,
    { rcases h2 V with ⟨lb, hlb1 | hlb1, hlb2⟩,
      { subst hla1, subst hlb1, cases hla2 hlb2 },
      refine ⟨_, hlb1, hlb2⟩ },
    refine ⟨_, hla1, hla2⟩ },
  { intro V,
    rw cla.holds_vsubs,
    apply h1 },
  { intro V,
    rcases (list.exists_mem_cons_iff _ _ _).elim_left
      (h1 V) with h3 | ⟨w, h3, h4⟩,
    { rcases (list.exists_mem_cons_iff _ _ _).elim_left
        (h2 V) with h4 | ⟨w, h4, h5⟩,
      { refine ⟨_, or.inl rfl, _⟩,
        rw lit.holds_replace h4,
        exact h3 },
      refine ⟨w, or.inr h4, h5⟩ },
    refine ⟨w, or.inr h3, h4⟩ },
  { intro V,
    rcases h2 V with ⟨l, h2 | h2, h3⟩,
    { rw h2 at h3,
      exfalso, apply h3 rfl },
    refine ⟨l, h2, h3⟩ },
  { intro,
    apply cla.holds_of_subsumes h1 (h2 _) }
end

open tactic

universe u

class has_to_asm (α : Type u) :=
(to_asm : α → string)

def to_asm {α : Type u} [has_to_asm α] : α → string :=
has_to_asm.to_asm

instance nat.has_to_asm : has_to_asm nat := ⟨λ k, "b" ++ k.bstr⟩

def xtrm.to_asm : ∀ {b : bool}, xtrm b → string
| _ []*        := "n"
| _ (t ::* ts) := ts.to_asm ++ t.to_asm ++ "c"
| _ (v* k)     := to_asm k ++ "v"
| _ (f* k ts)  := ts.to_asm ++ to_asm k ++ "f"

instance trm.has_to_asm : has_to_asm trm :=
⟨xtrm.to_asm⟩

def list.to_asm [has_to_asm α] : list α → string
| []        := "n"
| (a :: as) := list.to_asm as ++ to_asm a ++ "c"

instance list.has_to_asm [has_to_asm α] : has_to_asm (list α) :=
⟨list.to_asm⟩

def atm.to_asm : atm → string
| (r* k ts) := to_asm ts ++ to_asm k ++ "r"
| (t =* s)  := to_asm t ++ to_asm s ++ "e"

instance atm.has_to_asm : has_to_asm atm := ⟨atm.to_asm⟩

def lit.to_asm : lit → string
| (b, a) := to_asm a ++ if b then "+" else "-"

instance lit.has_to_asm : has_to_asm lit := ⟨lit.to_asm⟩

meta def get_asm (m : mat) : tactic string :=
unsafe_run_io $ io.cmd'
{ cmd := "main.pl",
  args := [to_asm m] }

def ln : Type := rul × cla

def ln.repr : ln → string
| (r, c) := cla.repr c ++ " [" ++ r.repr ++ "]"

instance ln.has_repr : has_repr ln := ⟨ln.repr⟩

def lns.repr : list ln → string
| []        := ""
| [l]       := l.repr
| (l :: ls) := l.repr ++ "\n" ++ lns.repr ls

inductive item : Type
| nl                      : item
| nm  (n : nat)           : item
| trm (t : trm)           : item
| trms (ts : list trm)    : item
| mp (μ : vmap)           : item
| mps (μs : vmaps)        : item
| atm (a : atm)           : item
| lit (l : lit)           : item
| cla (c : cla)           : item
| rul (r : rul)           : item
| ln  (l : ln)            : item
| lns (ls : list ln)      : item

namespace item

meta def repr : item → string
| item.nl          := "[]"
| (item.nm n)      := n.repr
| (item.trm t)     := t.repr
| (item.trms ts)   := ts.repr
| (item.mp μ)      := μ.repr
| (item.mps μs)    := μs.repr
| (item.atm a)     := a.repr
| (item.lit l)     := l.repr
| (item.cla c)     := cla.repr c
| (item.rul r)     := r.repr
| (item.ln (r, c)) := cla.repr c ++ " [" ++ r.repr ++ "]"
| (item.lns ls)    := ls.repr

meta instance has_repr : has_repr item := ⟨repr⟩

meta instance has_to_format : has_to_format item := ⟨λ x, repr x⟩

end item

meta def vmap.to_expr : vmap → expr
| (k, t) := expr.mk_app `(@prod.mk nat trm) [k.to_expr, t.to_expr]

meta def vmaps.to_expr : vmaps → expr
| []        := `(@list.nil vmap)
| (m :: ms) := expr.mk_app `(@list.cons vmap) [m.to_expr, vmaps.to_expr ms]

set_option eqn_compiler.max_steps 4096

open tactic

meta def decode : list item → list char → tactic (list ln)
| is (' ' :: chs)  := decode is chs
| is ('\n' :: chs) := decode is chs
| is ('b' :: chs)  := decode (item.nm 0 :: is) chs
-- Binary numbers
| (item.nm k :: is) ('0' :: chs) :=
  decode (item.nm (k * 2) :: is) chs
| (item.nm k :: is) ('1' :: chs) :=
  decode (item.nm ((k * 2) + 1) :: is) chs
-- Terms
| (item.nm k :: is) ('v' :: chs) :=
  decode (item.trm (v* k) :: is) chs
| (item.nm k :: item.nl :: is) ('f' :: chs) :=
  decode (item.trm (f* k []*) :: is) chs
| (item.nm k :: item.trms ts :: is) ('f' :: chs) :=
  decode (item.trm (f* k $ trms.of_list ts) :: is) chs
-- Atoms
| (item.nm k :: item.nl :: is) ('r' :: chs) :=
  decode (item.atm (r* k []) :: is) chs
| (item.nm k :: item.trms ts :: is) ('r' :: chs) :=
  decode (item.atm (r* k ts) :: is) chs
| (item.trm s :: item.trm t :: is) ('e' :: chs) :=
  decode (item.atm (t =* s) :: is) chs
-- Literals
| (item.atm a :: is) ('+' :: chs) :=
  decode (item.lit (tt, a) :: is) chs
| (item.atm a :: is) ('-' :: chs) :=
  decode (item.lit (ff, a) :: is) chs
-- Maps
| (item.nm k :: item.trm t :: is) ('m' :: infs) :=
  decode (item.mp (k, t) :: is) infs
-- Lists
| is ('n' :: chs)  := decode (item.nl :: is) chs
| (item.trm t :: item.nl :: is) ('c' :: chs) :=
   decode (item.trms [t] :: is) chs
| (item.trm t :: item.trms ts :: is) ('c' :: chs) :=
  decode (item.trms (t :: ts) :: is) chs
| (item.mp μ :: item.nl :: is) ('c' :: chs) :=
   decode (item.mps [μ] :: is) chs
| (item.mp μ :: item.mps μs :: is) ('c' :: chs) :=
   decode (item.mps (μ :: μs) :: is) chs
| (item.lit l :: item.nl :: is) ('c' :: chs) :=
   decode (item.cla [l] :: is) chs
| (item.lit l :: item.cla c :: is) ('c' :: chs) :=
   decode (item.cla (l :: c) :: is) chs
| (item.ln l :: item.nl :: is) ('c' :: chs) :=
   decode (item.lns [l] :: is) chs
| (item.ln l :: item.lns ls :: is) ('c' :: chs) :=
   decode (item.lns (l :: ls) :: is) chs
-- Rules
| (item.nm k :: is) ('H' :: chs) :=
  decode (item.rul (rul.H k) :: is) chs
| (item.nm k :: is) ('W' :: chs) :=
  decode (item.rul (rul.W k) :: is) chs
| (item.nm k :: is) ('V' :: chs) :=
  decode (item.rul (rul.V k) :: is) chs
| (item.nm m :: item.nm k :: is) ('R' :: chs) :=
  decode (item.rul (rul.R k m) :: is) chs
| (item.nm m :: item.nm k :: is) ('P' :: chs) :=
  decode (item.rul (rul.P k m) :: is) chs
| (item.nm k :: item.mps μs :: is) ('I' :: chs) :=
  decode (item.rul (rul.I k μs) :: is) chs
| (item.nm k :: item.nl :: is) ('I' :: chs) :=
  decode (item.rul (rul.I k []) :: is) chs
-- Lines
| (item.rul r :: item.cla c :: is) ('l' :: chs) :=
  decode (item.ln (r, c) :: is) chs
| (item.rul r :: item.nl :: is) ('l' :: chs) :=
  decode (item.ln (r, []) :: is) chs
| [item.lns ls] [] := return ls
| (X :: Y :: _) chs :=
  trace "Stack top : " >> trace X >> trace Y >>
  trace "Remaining proof" >> trace chs >> failed
| (X :: _) chs :=
  trace "Stack top : " >> trace X >>
  trace "Remaining proof" >> trace chs >> failed
| [] chs := trace "Stack empty, remaining proof : " >> trace chs >> failed

meta def mk_prf_expr_aux (m : mat) (mx : expr) :
  ln → list (expr × cla) → tactic (expr × cla)
| (rul.H k, _) _ :=
  return (expr.mk_app `(@proof.H) [mx, k.to_expr], m.nth k)
| (rul.V k, _) xcs :=
  do (πx, (ff, t =* _) :: c) ← xcs.nth k,
     return (expr.mk_app `(@proof.V) [mx, trm.to_expr t, cla.to_expr c, πx], c)
| (rul.R i j, _) xcs :=
  do (πx, (ff, a) :: c) ← xcs.nth i,
     (σx, (tt, _) :: _) ← xcs.nth j,
     return (expr.mk_app `(@proof.R) [mx, atm.to_expr a, cla.to_expr c, πx, σx], c)
| (rul.P i j, _) xcs :=
  do (πx, l :: c) ← xcs.nth i,
     (σx, (tt, t =* s) :: _) ← xcs.nth j,
     let ρx := expr.mk_app `(@proof.P)
       [mx, l.to_expr, t.to_expr, s.to_expr, cla.to_expr c, πx, σx] ,
     return (ρx, (l.replace t s :: c))
| (rul.I k μs, _) xcs :=
  do (πx, c) ← xcs.nth k,
     let σx := expr.mk_app `(@proof.I) [mx, μs.to_expr, c.to_expr, πx],
     return (σx, c.vsubs μs)
| (rul.W k, d) xcs :=
  do (πx, c) ← xcs.nth k,
     let sx := expr.mk_app `(cla.subsumes) [c.to_expr, d.to_expr],
     let dx := expr.mk_app `(cla.subsumes_decidable) [c.to_expr, d.to_expr],
     let hx := expr.mk_app `(@of_as_true) [sx, dx, `(trivial)],
     let σx := expr.mk_app `(@proof.W) [mx, c.to_expr, d.to_expr, hx, πx],
     return (σx, d)

meta def mk_prf_expr_core (m : mat) (mx : expr) :
  list ln → tactic (list $ expr × cla)
| [] := return []
| (l :: ls) :=
  do xcs ← mk_prf_expr_core ls,
     xc  ← mk_prf_expr_aux m mx l xcs,
     return (xc :: xcs)

def normalize (f : frm) : frm :=
skolemize $ pnf $ f.neg

def clausify (f : frm) : mat :=
cnf $ frm.strip_fa $ normalize f

lemma frxffx_of_proof [inhabited α]
  (rn : nat) (R : rls α) (fn : nat) (F : fns α) (f : frm) :
  (normalize f).vnew = 0 →
  proof (clausify f) [] → f.frxffx rn R fn F :=
begin
  intros hz h0,
  apply frxffx_of_forall_rxt,
  intros R' h1 F' h2,
  apply classical.by_contradiction,
  rw ← holds_neg, intro h3,
  rw ← pnf_eqv at h3,
  rcases holds_skolemize h3 with ⟨F'', h4, h5⟩,
  have hAF : (skolemize (pnf (frm.neg f))).AF,
  { apply AF_skolemize,
    apply QF_pnf },
  have h6 := holds_strip_fa hAF _ (forall_ext_zero h5),
  { have h7 : ∀ (W : vas α), (clausify f).holds R' F'' W,
    { intro W, apply holds_cnf _ (h6 _),
      apply F_strip_fa _ hAF },
    have h8 := holds_cla_of_proof h7 h0 (Vdf α),
    apply not_holds_empty_cla h8 },
  apply le_of_eq hz
end

instance decidable_vnew_eq_zero (f : frm) :
  decidable ((normalize f).vnew = 0) := by apply_instance

meta def mk_prf_expr
  (αx ix : expr) (f : frm) (m : mat) (ls : list ln) : tactic expr :=
do ((πx, []) :: _) ← mk_prf_expr_core m m.to_expr ls,
   let rnx  : expr := f.rnew.to_expr,
   let fnx  : expr := f.fnew.to_expr,
   let Rx   : expr := `(Rdf %%αx),
   let Fx   : expr := `(@Fdf %%αx %%ix),
   let fx   : expr := f.to_expr,
   let eqx  : expr := `(frm.vnew (normalize %%fx) = 0 : Prop),
   let decx : expr := expr.mk_app `(vampire.decidable_vnew_eq_zero) [fx],
   let hx   : expr := expr.mk_app `(@of_as_true) [eqx, decx, `(trivial)],
   let x : expr := expr.mk_app `(@frxffx_of_proof)
     [αx, ix, rnx, Rx, fnx, Fx, fx, hx, πx],
   return x

meta def vampire : tactic unit :=
do desugar,
   αx ← get_domain,
   ix ← get_inhabitance αx,
   f  ← reify αx,
   let m := clausify f,
   s ← get_asm m, -- s ← (inp <|> get_asm m),
   ls ← decode [] s.data,
   x ← mk_prf_expr αx ix f m ls,
   apply x,
   -- if inp = none
   -- then trace s
   -- else skip
   skip

open tactic expr vampire

example : ∀ x y : ℕ, x = y ∨ ¬ x = y :=
by vampire

example (A B : Prop) : A ∧ B → B ∧ A :=
by vampire




variables [inhabited α]
variables (a c : α) (p q : α → Prop) (r : α → α → Prop)

example : (∀ x, p x → q x) → (∀ x, p x) → q a :=
by vampire

example : (∃ x, p x ∧ r x x) → (∀ x, r x x → q x) → ∃ x, p x ∧ q x :=
by vampire

lemma gilmore_6 {F G : α → α → Prop} {H : α → α → α → Prop} :
∀ x, ∃ y,
  (∃ u, ∀ v, F u x → G v u ∧ G u x)
   → (∃ u, ∀ v, F u y → G v u ∧ G u y) ∨
       (∀ u v, ∃ w, G v u ∨ H w y u → G u w) :=
by vampire

lemma manthe_and_bry (agatha butler charles : α)
(lives : α → Prop) (killed hates richer : α → α → Prop) :
   lives agatha ∧ lives butler ∧ lives charles ∧
   (killed agatha agatha ∨ killed butler agatha ∨
    killed charles agatha) ∧
   (∀ x y, killed x y → hates x y ∧ ¬ richer x y) ∧
   (∀ x, hates agatha x → ¬ hates charles x) ∧
   (hates agatha agatha ∧ hates agatha charles) ∧
   (∀ x, lives(x) ∧ ¬ richer x agatha → hates butler x) ∧
   (∀ x, hates agatha x → hates butler x) ∧
   (∀ x, ¬ hates x agatha ∨ ¬ hates x butler ∨ ¬ hates x charles)
   → killed agatha agatha ∧
       ¬ killed butler agatha ∧
       ¬ killed charles agatha :=
by vampire

lemma knights_and_knaves (me : α) (knight knave rich poor : α → α)
  (a_truth says : α → α → Prop) (and : α → α → α) :
  ( (∀ X Y, ¬ a_truth (knight X) Y ∨ ¬ a_truth (knave X) Y ) ∧
    (∀ X Y, a_truth (knight X) Y ∨ a_truth (knave X) Y ) ∧
    (∀ X Y, ¬ a_truth (rich X) Y ∨ ¬ a_truth (poor X) Y ) ∧
    (∀ X Y, a_truth (rich X) Y ∨ a_truth (poor X) Y ) ∧
    (∀ X Y Z, ¬ a_truth (knight X) Z ∨ ¬ says X Y ∨ a_truth Y Z ) ∧
    (∀ X Y Z, ¬ a_truth (knight X) Z ∨ says X Y ∨ ¬ a_truth Y Z ) ∧
    (∀ X Y Z, ¬ a_truth (knave X) Z ∨ ¬ says X Y ∨ ¬ a_truth Y Z ) ∧
    (∀ X Y Z, ¬ a_truth (knave X) Z ∨ says X Y ∨ a_truth Y Z ) ∧
    (∀ X Y Z, ¬ a_truth (and X Y) Z ∨ a_truth X Z ) ∧
    (∀ X Y Z, ¬ a_truth (and X Y) Z ∨ a_truth Y Z ) ∧
    (∀ X Y Z, a_truth (and X Y) Z ∨ ¬ a_truth X Z ∨ ¬ a_truth Y Z ) ∧
    (∀ X, ¬ says me X ∨ ¬ a_truth (and (knave me) (rich me)) X ) ∧
    (∀ X, says me X ∨ a_truth (and (knave me) (rich me)) X ) ) → false :=
by vampire

end vampire

-- open lean.parser interactive vampire tactic
--
-- meta def tactic.interactive.vampire
--   (ids : parse (many ident))
--   (inp : option string := none) : tactic unit :=
-- ( if `all ∈ ids
--   then local_context >>= monad.filter is_proof >>=
--        revert_lst >> skip
--   else do hs ← mmap tactic.get_local ids,
--                revert_lst hs, skip ) >>
-- vampire.vampire inp
