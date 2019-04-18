import .univ_close .exist_open .skolemize .pnf .correct .search

variables {α : Type} [inhabited α]

open tactic

/- Return (⌜π : ext_valid ⟦dx⟧ (P, C, M)⌝, rs'),
   where rs' is the list of unused rules. -/
meta def prove_ext_valid (dx : expr) :
  cla → cla → mat → list rule → tactic (expr × list rule)
| p [] m rs :=
  return (`(@close_correct %%dx %%`(p) %%`(m)), rs)
| p (l :: c) m (rule.red i :: rs) :=
  match p.rotate i with
  | []        := failed
  | (n :: p') :=
    do (πx, rs') ← prove_ext_valid (n :: p') c m rs,
       ρx ← to_expr ``(rot_path_correct %%`(i) (red_correct (eq.refl (lit.neg %%`(l))) %%πx)),
       return (ρx, rs)
  end
| p (l :: c) m (rule.ext j i σx :: rs) :=
  match m.rotate j with
  | [] := failed
  | (d :: m') :=
    match d.rotate i with
    | [] := failed
    | (n :: d') :=
      if σx = []
      then do (πx, rs') ← prove_ext_valid p c ((n :: d') :: m') rs,
              (ρx, rs'') ← prove_ext_valid (l :: p) d' m' rs',
              τx ← to_expr
                   ``(rot_mat_correct %%`(j)
                       (rot_cla_correct %%`(i)
                         (ext_correct (eq.refl (lit.neg %%`(l))) %%πx %%ρx))),
              return (τx, rs'')
      else do σ ← subx.eval σx,
              (πx, rs') ← prove_ext_valid p c ((n :: d') :: m') rs,
              (ρx, rs'') ← prove_ext_valid (l :: p) (cla.subst σ d') ((n :: d') :: m') rs',
              τx ← to_expr
                   ``(@rot_mat_correct %%dx %%`(p) (%%`(l) :: %%`(c)) %%`(m) %%`(j)
                       (rot_cla_correct %%`(i)
                         (ext_copy_correct %%`(σ)
                         (dec_trivial) %%πx %%ρx))),
              return (τx, rs'')
    end
  end
| _ _ _ [] := fail "Remaining goals"

/- Return ⌜π : mat.fam_exv ⟦dx⟧ m⌝. -/
meta def prove_fam_exv (dx : expr) (m : mat) : list rule → tactic expr
| (rule.ext j _ [] :: rs) :=
  match m.rotate j with
  | []        := failed
  | (c :: m') :=
    do (πx, _) ← prove_ext_valid dx [] c m' rs,
       to_expr ``(@rot_mat_correct' %%dx %%`(m) %%`(j) (start_correct %%πx))
  end
| (rule.ext j _ σx :: rs) :=
  match m.rotate j with
  | []        := failed
  | (c :: m') :=
    do σ ← subx.eval σx,
       (πx, _) ← prove_ext_valid dx [] (c.subst σ) (c :: m') rs,
       to_expr ``(@rot_mat_correct' %%dx %%`(m) %%`(j)
         (@start_copy_correct %%dx %%`(c) %%`(m') %%`(σ) %%πx))
  end
| _ := fail "Proof must begin with ext"

axiom any (P : Prop) : P

def matrixify : form → mat :=
dnf ∘ exist_open ∘ pnf ∘ skolemize

lemma univ_close_of_fam_exv_matrixify (p : form) :
  closed p → (matrixify p).fam_exv α → univ_close α p :=
λ h0 h1,
( univ_close_of_fam_fav $
  fam_fav_of_fam_fav_skolemize $
  fam_fav_of_fam_fav_pnf $
  fam_fav_of_closed_of_fam_exv_exist_open _ $
  fam_exv_of_dnf_fam_exv sorry h1)

/- Return ⌜π : p.univ_close ⟦dx⟧⌝ . -/
meta def prove_univ_close (dx ix : expr) (p : form) : tactic expr :=
do x ← to_expr ``(any (closed %%`(p))),
   rs ← derive (matrixify p),
   y ← prove_fam_exv dx (matrixify p) rs,
   return `(@univ_close_of_fam_exv_matrixify %%dx %%ix %%`(p) %%x %%y)
