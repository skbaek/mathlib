import .form

variable {α : Type}

local notation  `⅋`     := atom.sym
local notation  a `&` b := atom.app a b
local notation  a `#` k := atom.vpp a k

local notation  `⊤*` := form.true
local notation  `⊥*` := form.false
local notation  `⟪` l `⟫` := form.lit l
local notation  p `∧*` q := form.and p q
local notation  p `∨*` q := form.or p q
local notation  `∀*` := form.fa
local notation  `∃*` := form.ex

def skolem_term : atom → list nat → atom
| a []      := a
| a (k::ks) := skolem_term (a # k) ks

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
  let ks := (free_vdxs p').filter (λ x, 0 < x) in
  (m + 1, (p'.subst 0 (skolem_term (⅋ m) ks)).decr_vdxs)
| k (∃* p) :=
  let (m, p') := skolemize_core k p in
  (m, ∃* p')

#exit
def skolemize (p : form) : form :=
let k := p.fresh_sdx in
let (_,p') := skolemize_core k p in
p'

lemma closed_skolemize_core_aux (ks ms : list nat) :
  ks = [] → ms = [] → ks ∪ ms = [] :=
by {intros h0 h1, rw [h0, h1], refl}

open list

lemma free_vdxs_skolemize_core_subset :
  ∀ k : nat, ∀ p : form,
  free_vdxs (skolemize_core k p).snd ⊆ free_vdxs p
| k ⊤*  := subset.refl _
| k ⊥*  := subset.refl _
| k ⟪l⟫ := subset.refl _

#exit
| k (p ∨* q) :=
  begin
    unfold skolemize_core,
    cases h1 : (skolemize_core k p) with m p',
    unfold skolemize_core,
    cases h2 : (skolemize_core m q) with n q',
    have hp : free_vdxs p' = free_vdxs p,
    { simpa only [h1] using free_vdxs_skolemize_core k p },
    have hq : free_vdxs q' = free_vdxs q,
    { simpa only [h2] using free_vdxs_skolemize_core m q },
    apply fun_mono_2 hp hq
  end
| k (p ∧* q) :=
  begin
    unfold skolemize_core,
    cases h1 : (skolemize_core k p) with m p',
    unfold skolemize_core,
    cases h2 : (skolemize_core m q) with n q',
    have hp : free_vdxs p' = free_vdxs p,
    { simpa only [h1] using free_vdxs_skolemize_core k p },
    have hq : free_vdxs q' = free_vdxs q,
    { simpa only [h2] using free_vdxs_skolemize_core m q },
    apply fun_mono_2 hp hq
  end
| k (∀* p) :=
  begin

  end
| k (∃* p) :=
  begin
    unfold skolemize_core,
    cases h1 : (skolemize_core k p) with m p',
    apply (congr_arg (λ x : list nat,
      (x.filter ((<) 0)).map nat.pred) _),
    simpa only [h1] using free_vdxs_skolemize_core k p
  end


#check free_vdxs


lemma closed_skolemize {p : form} :
  closed p → closed (skolemize p) := sorry


lemma fam_fav_of_fam_fav_skolemize {p : form} :
  (skolemize p).fam_fav α → p.fam_fav α := sorry
