#!/usr/bin/env swipl

:- initialization(main, main).

:- [basic, write, read].

parse_inp([Num | Stk], ['v' | Chs], Mat) :-
  parse_inp([vr(Num) | Stk], Chs, Mat).

parse_inp([Num, Trms | Stk], ['f' | Chs], Mat) :-
  parse_inp([fn(Num, Trms) | Stk], Chs, Mat).

parse_inp([Num, Trms | Stk], ['r' | Chs], Mat) :-
  parse_inp([rl(Num, Trms) | Stk], Chs, Mat).

parse_inp([TrmB, TrmA | Stk], ['e' | Tks], Mat) :-
  parse_inp([eq(TrmA, TrmB) | Stk], Tks, Mat).

parse_inp([Atm | Stk], ['-' | Tks], Mat) :-
  parse_inp([lit(neg, Atm) | Stk], Tks, Mat).

parse_inp([Atm | Stk], ['+' | Tks], Mat) :-
  parse_inp([lit(pos, Atm) | Stk], Tks, Mat).

parse_inp(Stk, ['n' | Chs], Mat) :-
  parse_inp([[] | Stk], Chs, Mat).

parse_inp([Hd, Tl | Stk], ['c' | Chs], Mat) :-
  parse_inp([[Hd | Tl] | Stk], Chs, Mat).

parse_inp(Stk, ['b' | Chs], Mat) :-
  parse_inp([0 | Stk], Chs, Mat).

parse_inp([Num | Stk], ['0' | Chs], Mat) :-
  NewNum is Num * 2,
  parse_inp([NewNum | Stk], Chs, Mat).

parse_inp([Num | Stk], ['1' | Chs], Mat) :-
  NewNum is (Num * 2) + 1,
  parse_inp([NewNum | Stk], Chs, Mat).

parse_inp([Mat], [], Mat).

vnew_trm(vr(NumA), NumB) :-
  NumB is NumA + 1.

vnew_trm(fn(_, Trms), Num) :-
  maplist(vnew_trm, Trms, Nums),
  max_list([0 | Nums], Num).

vnew_atm(rl(_, Trms), Num) :-
  maplist(vnew_trm, Trms, Nums),
  max_list([0 | Nums], Num).

vnew_atm(eq(TrmA, TrmB), Num) :-
  vnew_trm(TrmA, NumA),
  vnew_trm(TrmB, NumB),
  max(NumA, NumB, Num).

vnew_lit(lit(_, Atm), Num) :-
  vnew_atm(Atm, Num).

vnew_cla(Cla, Num) :-
  maplist(vnew_lit, Cla, Nums),
  max_list([0 | Nums], Num).

offset(Ofs, Src, map(Src, vr(Tgt))) :-
  Tgt is Src + Ofs.

disjoiner(Cla1, Cla2, Dsj) :-
  vnew_cla(Cla2, Num),
  vars_cla(Cla1, Nums),
  maplist(offset(Num), Nums, Dsj).

unif_trms([], [], []).

unif_trms([TrmA | TrmsA], [TrmB | TrmsB], Maps) :-
  unif_trm(TrmA, TrmB, FstMaps),
  subst_trms(FstMaps, TrmsA, TrmsA1),
  subst_trms(FstMaps, TrmsB, TrmsB1),
  unif_trms(TrmsA1, TrmsB1, SndMaps),
  compose_inst(FstMaps, SndMaps, Maps).

unif_trm(vr(Num), Trm, [map(Num, Trm)]).

unif_trm(Trm, vr(Num), [map(Num, Trm)]).

unif_trm(fn(Num, TrmsA), fn(Num, TrmsB), Maps) :-
  unif_trms(TrmsA, TrmsB, Maps).

unif_atm(rl(Num, TrmsA), rl(Num, TrmsB), Maps) :-
  unif_trms(TrmsA, TrmsB, Maps).

unif_atm(eq(TrmAL, TrmAR), eq(TrmBL, TrmBR), Maps) :-
  unif_trm(TrmAL, TrmBL, FstMaps),
  subst_trm(FstMaps, TrmAR, TrmAR1),
  subst_trm(FstMaps, TrmBR, TrmBR1),
  unif_trm(TrmAR1, TrmBR1, SndMaps),
  compose_inst(FstMaps, SndMaps, Maps).

range(0, Acc, Acc).

range(Num, Acc, Nums) :-
  0 < Num,
  NewNum is Num - 1,
  range(NewNum, [NewNum | Acc], Nums).

range(Num, Nums) :-
  range(Num, [], Nums).

member_rev(Lst, Elm) :- member(Elm, Lst).

merge_instantiators([], Inst, Inst).

merge_instantiators([map(Idx, Tgt) | Inst1], Inst2, Inst) :-
  member(map(Idx, Tgt), Inst2),
  merge_instantiators(Inst1, Inst2, Inst).

merge_instantiators([map(Idx, Tgt) | Inst1], Inst2, [map(Idx, Tgt) | Inst]) :-
  not(member(map(Idx, _), Inst2)),
  merge_instantiators(Inst1, Inst2, Inst).

inst_trms([], [], []).

inst_trms([SrcTrm | SrcTrms], [TgtTrm | TgtTrms], Maps) :-
  inst_trm(SrcTrm, TgtTrm, Maps1),
  inst_trms(SrcTrms, TgtTrms, Maps2),
  merge_instantiators(Maps1, Maps2, Maps).

inst_trm(vr(Num), Trm, [map(Num, Trm)]).

inst_trm(fn(Num, SrcTrms), fn(Num, TgtTrms), Maps) :-
  inst_trms(SrcTrms, TgtTrms, Maps).

inst_atm(rl(Num, SrcTrms), rl(Num, TgtTrms), Maps) :-
  inst_trms(SrcTrms, TgtTrms, Maps).

inst_atm(eq(SrcTrmA, SrcTrmB), eq(TgtTrmA, TgtTrmB), Maps) :-
  inst_trm(SrcTrmA, TgtTrmA, Maps1),
  inst_trm(SrcTrmB, TgtTrmB, Maps2),
  merge_instantiators(Maps1, Maps2, Maps).

calc_inst_atm(SrcAtm, TgtAtm, Maps) :-
  inst_atm(SrcAtm, TgtAtm, Maps).

calc_inst_atm(eq(TrmA, TrmB), TgtAtm, Maps) :-
  inst_atm(eq(TrmB, TrmA), TgtAtm, Maps).

calc_inst_lit(lit(Pol, SrcAtm), lit(Pol, TgtAtm), Maps) :-
  calc_inst_atm(SrcAtm, TgtAtm, Maps).

calc_inst_perm_cla([], _, [], []).

calc_inst_perm_cla([Lit | Cla], Tgt, Inst, [LitNum | ClaNums]) :-
  nth0(LitNum, Tgt, TgtLit),
  calc_inst_lit(Lit, TgtLit, LitInst),
  calc_inst_perm_cla(Cla, Tgt, ClaInst, ClaNums),
  merge_instantiators(LitInst, ClaInst, Inst).

calc_inst_cla([], _, []).

calc_inst_cla([Lit | Cla], TgtCla, Inst) :-
  member(TgtLit, TgtCla),
  calc_inst_lit(Lit, TgtLit, LitInst),
  calc_inst_cla(Cla, TgtCla, ClaInst),
  merge_instantiators(LitInst, ClaInst, Inst).

nth0rot(List, Elem, Index) :- nth0(Index, List, Elem).

calc_perm(Cla, Tgt, Prm) :-
  maplist(nth0rot(Tgt), Cla, Prm).

% surjective(Perm, Tgt) :-
%   length(Tgt, Lth),
%   range(Lth, Idxs),
%   subset(Idxs, Perm).


count(_, [], 0).

count(Elm, [Elm | Lst], Cnt) :-
  count(Elm, Lst, Tmp),
  Cnt is Tmp + 1.

count(Elm, [Hd | Lst], Cnt) :-
  not(Elm = Hd),
  count(Elm, Lst, Cnt).

dup_idxs([Hd | Tl], 0, Idx) :-
  nth1(Idx, Tl, Hd).

dup_idxs([_ | Tl], IdxA, IdxB) :-
  dup_idxs(Tl, SubIdxA, SubIdxB),
  IdxA is SubIdxA + 1,
  IdxB is SubIdxB + 1.

allign_eq(Prf, Prf) :-
  conc(Prf, [Lit, Lit | _]).

allign_eq(SubPrf, Prf) :-
  conc(SubPrf, [lit(Pol, eq(TrmA, TrmB)), lit(Pol, eq(TrmB, TrmA)) | Cnc]),
  Prf = sym(SubPrf, [lit(Pol, eq(TrmB, TrmA)), lit(Pol, eq(TrmB, TrmA)) | Cnc]).

cmpl_cnts(Prf, Dsts, Prf) :-
  not(dup_idxs(Dsts, _, _)).

cmpl_cnts(SubPrf, Dsts, Prf) :-
  dup_idxs(Dsts, IdxA, IdxB),
  conc(SubPrf, SubCnc),
  tor(SubCnc, IdxA, SubCnc1),
  SubPrf1 = rot(IdxA, SubPrf, SubCnc1),
  tor(SubCnc1, IdxB, [Lit1, Lit2 | SubCnc2]),
  SubPrf2 = rot(IdxB, SubPrf1, [Lit1, Lit2 | SubCnc2]),
  allign_eq(SubPrf2, SubPrf3),
  conc(SubPrf3, [Lit, Lit | SubCnc3]),
  SubPrf4 = cnt(SubPrf3, [Lit | SubCnc3]),
  tor(Dsts,  IdxA, Dsts1),
  tor(Dsts1, IdxB, [Dst, Dst | Dsts2]),
  cmpl_cnts(SubPrf4, [Dst | Dsts2], Prf).

% compute_maps(Cla, Tgt, Maps, Nums) :-
%   calc_inst_perm_cla(Cla, Tgt, Maps, Nums),
%   surjective(Tgt, Nums).

rep_map_trm(SrcTrm, TrmA, TrmB, TgtTrm, Rpl) :-
  unif_trm(SrcTrm, TrmA, RplA),
  subst_trm(RplA, TrmB, TrmB1),
  inst_trm(TrmB1, TgtTrm, RplB),
  compose_inst(RplA, RplB, Rpl).

rep_map_trm(vr(Num), _, _, TgtTrm, [map(Num, TgtTrm)]).

rep_map_trm(fn(Num, SrcTrms), TrmA, TrmB, fn(Num, TgtTrms), Rpl) :-
  rep_map_trms(SrcTrms, TrmA, TrmB, TgtTrms, Rpl).

rep_map_trms([], _, _, [], []).

rep_map_trms([SrcTrm | SrcTrms], TrmA, TrmB, [TgtTrm | TgtTrms], Rpl) :-
  rep_map_trm(SrcTrm, TrmA, TrmB, TgtTrm, Rpl1),
  maplist(subst_trm(Rpl1), SrcTrms, SrcTrms1),
  subst_trm(Rpl1, TrmA, TrmA1),
  subst_trm(Rpl1, TrmB, TrmB1),
  rep_map_trms(SrcTrms1, TrmA1, TrmB1, TgtTrms, Rpl2),
  compose_inst(Rpl1, Rpl2, Rpl).

rep_map_atm(eq(SrcTrmA, SrcTrmB), TrmA, TrmB, eq(TgtTrmA, TgtTrmB), Rpl) :-
  rep_map_trm(SrcTrmA, TrmA, TrmB, TgtTrmA, RplA),
  subst_trm(RplA, SrcTrmB, SrcTrmB1),
  subst_trm(RplA, TrmA, TrmA1),
  subst_trm(RplA, TrmB, TrmB1),
  rep_map_trm(SrcTrmB1, TrmA1, TrmB1, TgtTrmB, RplB),
  compose_inst(RplA, RplB, Rpl).

rep_map_atm(rl(Num, SrcTrms), TrmA, TrmB, rl(Num, TgtTrms), Rpl) :-
  rep_map_trms(SrcTrms, TrmA, TrmB, TgtTrms, Rpl).

rep_map_lit(lit(Pol, SrcAtm), TrmA, TrmB, lit(Pol, TgtAtm), Rpl) :-
  rep_map_atm(SrcAtm, TrmA, TrmB, TgtAtm, Rpl),
  subst_atm(Rpl, SrcAtm, SrcAtm1),
  subst_trm(Rpl, TrmA, TrmA1),
  subst_trm(Rpl, TrmB, TrmB1),
  rep_atm(TrmA1, TrmB1, SrcAtm1, TgtAtm).

rep_trm(TrmL, TrmR, TrmL, TrmR).

rep_trm(TrmL, _, vr(Num), vr(Num)) :-
  not(TrmL = vr(Num)).

rep_trm(TrmL, TrmR, fn(Num, SrcTrms), fn(Num, TgtTrms)) :-
  maplist(rep_trm(TrmL, TrmR), SrcTrms, TgtTrms).

rep_atm(TrmL, TrmR, rl(Num, SrcTrms), rl(Num, TgtTrms)) :-
  maplist(rep_trm(TrmL, TrmR), SrcTrms, TgtTrms).

rep_atm(TrmL, TrmR, eq(SrcTrmA, SrcTrmB), eq(TgtTrmA, TgtTrmB)) :-
  rep_trm(TrmL, TrmR, SrcTrmA, TgtTrmA),
  rep_trm(TrmL, TrmR, SrcTrmB, TgtTrmB).


select_dir(Prf, Prf).

select_dir(Prf, sym(Prf, [lit(Pol, eq(TrmB, TrmA)) | Cnc])) :-
  conc(Prf, [lit(Pol, eq(TrmA, TrmB)) | Cnc]).

select_rot(Prf, rot(Num, Prf, NewCnc)) :-
  conc(Prf, Cnc),
  tor(Cnc, Num, NewCnc).

select_lit(Prf, NewPrf) :-
  select_rot(Prf, TmpPrf),
  select_dir(TmpPrf, NewPrf).

cmpl_res(PrfA, PrfB, res(PrfA2, PrfB1, Cnc)) :-
  conc(PrfA, CncA),
  CncA = [lit(neg, _) | _],
  conc(PrfB, CncB),
  CncB = [lit(pos, AtmB) | _],
  disjoiner(CncA, CncB, Dsj),
  subst_cla(Dsj, CncA, CncA1),
  CncA1 = [lit(neg, AtmA) | _],
  PrfA1 = sub(Dsj, PrfA, CncA1),
  unif_atm(AtmA, AtmB, Unf),
  subst_cla(Unf, CncA1, CncA2),
  CncA2 = [lit(neg, Atm) | ClaA2],
  PrfA2 = sub(Unf, PrfA1, CncA2),
  subst_cla(Unf, CncB, CncB1),
  CncB1 = [lit(pos, Atm) | ClaB1],
  PrfB1 = sub(Unf, PrfB, CncB1),
  append(ClaA2, ClaB1, Cnc).

temp_loc("/var/tmp/temp_goal_file").

% cmpl_map(Cla, Tgt, Prf) :-
%   conc(SubPrf, Cnc),
%   compute_maps(Cnc, Tgt, Inst, Nums),
%   subst_cla(Inst, SubCnc, NewCnc),
%   cmpl_cnts(sub(Inst, SubPrf, SubCnc1), Nums, Prf).

pluck(Fst, [Elm | Snd], Elm, Rem) :-
  append(Fst, Snd, Rem).

pluck(Fst, [Hd | Snd], Elm, Rem) :-
  pluck([Hd | Fst], Snd, Elm, Rem).

pluck(Lst, Elm, Rem) :-
  pluck([], Lst, Elm, Rem).

expl_ln(_, _, ln(LnNum, trv(PremNum), Cla),
  [ ln(LnNum, trv(abs(PremNum)), Cla) ]).

expl_ln(_, Lns,
  ln(LnNum, map(PremNum), Cla),
  [ ln(LnNum, wkn(rel(0)), Cla),
    ln(none, inst(abs(PremNum), Inst), ClaA) ]) :-
  member(ln(PremNum, _, ClaA0), Lns),
  calc_inst_cla(ClaA0, Cla, TmpInst),
  compress_inst(ClaA0, TmpInst, Inst),
  subst_cla(Inst, ClaA0, ClaA).

expl_ln(_, Lns,
  ln(LnNum, rep(PremNumA, PremNumB), Cla),
  [ ln(LnNum, wkn(rel(0)), Cla),
    ln(none, rep(rel(2), rel(0)), [Lit | TlCla]),
    ln(none, wkn(rel(0)), [lit(pos, eq(TrmA, TrmB)) | TlCla]),
    ln(none, inst(abs(PremNumB), InstB), ClaB),
    ln(none, wkn(rel(0)), [LitA | TlCla]),
    ln(none, inst(abs(PremNumA), InstA), ClaA) ]) :-
  member(ln(PremNumA, _, ClaA0), Lns),
  member(ln(PremNumB, _, ClaB0), Lns),
  disjoiner(ClaB0, Cla, DsjB),
  subst_cla(DsjB, ClaB0, ClaB1),
  disjoiner(ClaA0, ClaB1, DsjA),
  subst_cla(DsjA, ClaA0, ClaA1),

  pluck(ClaA1, LitA0, TlClaA),
  pluck(ClaB1, LitB0, TlClaB),
  ( LitB0 = lit(pos, eq(TrmA0, TrmB0)) ;
    LitB0 = lit(pos, eq(TrmB0, TrmA0)) ),
  pluck(Cla, Lit, TlCla),

  rep_map_lit(LitA0, TrmA0, TrmB0, Lit, Inst0),
  calc_inst_cla(TlClaA, TlCla, Inst1),
  merge_instantiators(Inst0, Inst1, Inst2),
  calc_inst_cla(TlClaB, TlCla, Inst3),
  merge_instantiators(Inst2, Inst3, Inst4),

  compress_compose_insts(ClaA0, [DsjA, Inst4], InstA),
  compress_compose_insts(ClaB0, [DsjB, Inst4], InstB),

  subst_cla(InstA, ClaA0, ClaA),
  subst_cla(InstB, ClaB0, ClaB),
  subst_lit(InstA, LitA0, LitA),
  subst_trm(InstB, TrmA0, TrmA),
  subst_trm(InstB, TrmB0, TrmB).

expl_ln(_, Lns, ln(LnNum, eqres(PremNum), Cla),
  [ ln(LnNum, trv(rel(0)), Cla),
    ln(none, wkn(rel(0)), [lit(neg, eq(Trm, Trm)) | Cla]),
    ln(none, inst(abs(PremNum), Inst), ClaA) ]) :-
  member(ln(PremNum, _, ClaA0), Lns),
  pluck(ClaA0, lit(neg, eq(TrmA, TrmB)), ClaA1),
  unif_trm(TrmA, TrmB, Unf),
  subst_cla(Unf, ClaA1, ClaA2),
  calc_inst_cla(ClaA2, Cla, TmpInst),
  compress_compose_insts(ClaA0, [Unf, TmpInst], Inst),
  subst_trm(Inst, TrmA, Trm),
  subst_cla(Inst, ClaA0, ClaA).

expl_ln(_, Lns, ln(LnNum, res(NumA, NumB), Cla),
  [ ln(LnNum, res(rel(2), rel(0)), Cla),
    ln(none, wkn(rel(0)), [lit(pos, Atm) | Cla]),
    ln(none, inst(abs(PremNumB), InstB), ClaB),
    ln(none, wkn(rel(0)), [lit(neg, Atm) | Cla]),
    ln(none, inst(abs(PremNumA), InstA), ClaA) ]) :-
  ( (PremNumA = NumA, PremNumB = NumB) ;
    (PremNumA = NumB, PremNumB = NumA) ),
  % Get premise lns
  member(ln(PremNumA, _, ClaA0), Lns),
  member(ln(PremNumB, _, ClaB1), Lns),
  % Disjoin first premise from second
  disjoiner(ClaA0, ClaB1, Dsj),
  subst_cla(Dsj, ClaA0, ClaA1),
  % Choose literals to resolve on
  pluck([], ClaA1, lit(neg, AtmA0), ClaA2),
  pluck([], ClaB1, lit(pos, AtmB0), ClaB2),
  % Find mappings
  unif_atm(AtmA0, AtmB0, Unf),
  append(ClaA2, ClaB2, Cla0),
  subst_cla(Unf, Cla0, Cla1),
  calc_inst_cla(Cla1, Cla, Inst),
  compress_compose_insts(ClaA0, [Dsj, Unf, Inst], InstA),
  compress_compose_insts(ClaB1, [Unf, Inst], InstB),
  % Unify return values
  subst_atm(Unf, AtmA0, AtmA1),
  subst_atm(Inst, AtmA1, Atm),
  subst_cla(InstA, ClaA0, ClaA),
  subst_cla(InstB, ClaB1, ClaB).

expl_ln(Mat, _, ln(LnNum, hyp, Cla),
  [ ln(LnNum, wkn(rel(0)), Cla),
    ln(none, inst(rel(0), Inst), ClaA1),
    ln(none, hyp(ClaNum), ClaA0) ]) :-
  nth0(ClaNum, Mat, ClaA0),
  calc_inst_cla(ClaA0, Cla, TmpInst),
  compress_inst(ClaA0, TmpInst, Inst),
  subst_cla(Inst, ClaA0, ClaA1).

expl_lns(Mat, Lns, Prf) :-
  maplist(expl_ln(Mat, Lns), Lns, Prfs),
  append(Prfs, Prf).

expl_lns(Mat, Lns, expl_lns_error(Mat, Lns)).

find_rel_pos(Dst, Num, [ln(LnNum, _, _) | _], NewNum) :-
  Num = LnNum, Dst = NewNum.

find_rel_pos(Dst, Num, [ln(LnNum, _, _) | Prf], NewNum) :-
  not(Num = LnNum),
  NewDst is Dst + 1,
  find_rel_pos(NewDst, Num, Prf, NewNum).

relativize_num(rel(Num), _, Num).

relativize_num(abs(Num), Prf, NewNum) :-
  find_rel_pos(0, Num, Prf, NewNum).

relativize_rul(hyp(Num), _, hyp(Num)).

relativize_rul(rep(NumA, NumB), Prf, rep(NewNumA, NewNumB)) :-
  relativize_num(NumA, Prf, NewNumA),
  relativize_num(NumB, Prf, NewNumB).

relativize_rul(res(NumA, NumB), Prf, res(NewNumA, NewNumB)) :-
  relativize_num(NumA, Prf, NewNumA),
  relativize_num(NumB, Prf, NewNumB).

relativize_rul(wkn(Num), Prf, wkn(NewNum)) :-
  relativize_num(Num, Prf, NewNum).

relativize_rul(trv(Num), Prf, trv(NewNum)) :-
  relativize_num(Num, Prf, NewNum).

relativize_rul(inst(Num, Inst), Prf, inst(NewNum, Inst)) :-
  relativize_num(Num, Prf, NewNum).

relativize_ln(ln(_, Rul, Cla), Prf, ln(NewRul, Cla)) :-
  relativize_rul(Rul, Prf, NewRul).

relativize([], []).

relativize([Ln | Prf], [NewLn | NewPrf]) :-
  relativize_ln(Ln, Prf, NewLn),
  relativize(Prf, NewPrf).

relativize(Prf, relativize_error(Prf)).

encode_lst(_, [], "n").

encode_lst(Enc, [Elm | Lst], Str) :-
  call(Enc, Elm, ElmStr),
  encode_lst(Enc, Lst, LstStr),
  join_string([LstStr, ElmStr, "c"], Str).

encode_trm(vr(Num), Str) :-
  encode_num(Num, NumStr),
  join_string([NumStr, "v"], Str).

encode_trm(fn(Num, Trms), Str) :-
  encode_num(Num, NumStr),
  encode_lst(encode_trm, Trms, TrmsStr),
  join_string([TrmsStr, NumStr, "f"], Str).

encode_atm(rl(Num, Trms), Str) :-
  encode_num(Num, NumStr),
  encode_lst(encode_trm, Trms, TrmsStr),
  join_string([TrmsStr, NumStr, "r"], Str).

encode_atm(eq(TrmA, TrmB), Str) :-
  encode_trm(TrmA, TrmStrA),
  encode_trm(TrmB, TrmStrB),
  join_string([TrmStrA, TrmStrB, "e"], Str).

encode_pol(pos, "+").
encode_pol(neg, "-").

encode_lit(lit(Pol, Atm), Str) :-
  encode_pol(Pol, PolStr),
  encode_atm(Atm, AtmStr),
  join_string([AtmStr, PolStr], Str).

encode_map(map(Num, Trm), Str) :-
  encode_num(Num, NumStr),
  encode_trm(Trm, TrmStr),
  join_string([TrmStr, NumStr, "m"], Str).

encode_maps(Maps, Str) :-
  encode_lst(encode_map, Maps, Str).

encode_num(Num, Str) :-
  number_binstr(Num, NumStr),
  string_concat("b", NumStr, Str).

encode_rul(hyp(Num), Str) :-
  encode_num(Num, NumStr),
  join_string([NumStr, "H"], Str).

encode_rul(res(NumA, NumB), Str) :-
  encode_num(NumA, NumStrA),
  encode_num(NumB, NumStrB),
  join_string([NumStrA, NumStrB, "R"], Str).

encode_rul(rep(NumA, NumB), Str) :-
  encode_num(NumA, NumStrA),
  encode_num(NumB, NumStrB),
  join_string([NumStrA, NumStrB, "P"], Str).

encode_rul(inst(Num, Inst), Str) :-
  encode_maps(Inst, InstStr),
  encode_num(Num, NumStr),
  join_string([InstStr, NumStr, "I"], Str).

encode_rul(trv(Num), Str) :-
  encode_num(Num, NumStr),
  join_string([NumStr, "V"], Str).

encode_rul(wkn(Num), Str) :-
  encode_num(Num, NumStr),
  join_string([NumStr, "W"], Str).

encode_cla(Cla, Str) :-
  encode_lst(encode_lit, Cla, Str).

encode_ln(ln(Rul, Cla), Str) :-
  encode_rul(Rul, RulStr),
  encode_cla(Cla, ClaStr),
  join_string([ClaStr, RulStr, "l"], Str).

encode_prf(Prf, Str) :-
  encode_lst(encode_ln, Prf, Str).

encode_prf(Prf, encode_prf_error(Prf)).

string_block(Str, Blk) :-
  break_string(60, Str, Strs),
  string_codes(Nl, [10]),
  join_string(Strs, Nl, Blk).

main([Argv]) :-
  string_chars(Argv, Chs),
  parse_inp([], Chs, Mat),
  temp_loc(Loc),
  write_goal(Loc, Mat),
  read_proof(Loc, Lns),
  expl_lns(Mat, Lns, Prf0),
  relativize(Prf0, Prf1),
  % compress(RawPrf, Prf),
  encode_prf(Prf1, RawStr),
  string_block(RawStr, Str),
  write(Str).

/*
cmpl(Mat, _, Tgt, hyp, Prf) :-
  nth0(Num, Mat, Cla),
  cmpl_map(hyp(Num, Cla), Tgt, Prf).

cmpl(Mat, Lns, Tgt, res(NumA, NumB), Prf) :-
  cmpl(Mat, Lns, NumA, PrfA),
  cmpl(Mat, Lns, NumB, PrfB),
  conc(PrfA, CncA),
  conc(PrfB, CncB),
  tor(CncA, IdxA, CncA1),
  tor(CncB, IdxB, CncB1),
  PrfA1 = rot(IdxA, PrfA, CncA1),
  PrfB1 = rot(IdxB, PrfB, CncB1),
  ( cmpl_res(PrfA1, PrfB1, SubPrf) ;
    cmpl_res(PrfB1, PrfA1, SubPrf) ),
  cmpl_map(SubPrf, Tgt, Prf).

cmpl(Mat, Lns, Tgt, rep(NumA, NumB), Prf) :-
  cmpl(Mat, Lns, NumA, PrfA),
  cmpl(Mat, Lns, NumB, PrfB),
  cmpl_rep(PrfA, PrfB, Tgt, Prf).

cmpl(Mat, Lns, Tgt, eqres(Num), Prf) :-
  cmpl(Mat, Lns, Num, Prf1),
  conc(Prf1, Cnc1),
  tor(Cnc1, Idx, Cnc2),
  Cnc2 = [lit(neg, eq(TrmA, TrmB)) | _],
  Prf2 = rot(Idx, Prf1, Cnc2),
  unif_trm(TrmA, TrmB, Unf),
  subst_cla(Unf, Cnc2, Cnc3),
  Cnc3 = [lit(neg, eq(Trm, Trm)) | Tl],
  Prf3 = sub(Unf, Prf2, Cnc3),
  Prf4 = trv(Prf3, Tl),
  cmpl_map(Prf4, Tgt, Prf).

cmpl(Mat, Lns, Tgt, trv(Num), trv(Prf, Tgt)) :-
  cmpl(Mat, Lns, Num, Prf),
  conc(Prf, [lit(neg, eq(Trm, Trm)) | Tgt]).

cmpl(Mat, Lns, Tgt, map(Num), Prf) :-
  cmpl(Mat, Lns, Num, SubPrf),
  cmpl_map(SubPrf, Tgt, Prf).

cmpl(Mat, Lns, Num, Prf) :-
  member(ln(Num, Tgt, Rul), Lns),
  cmpl(Mat, Lns, Tgt, Rul, Prf).

cmpl(Mat, Lns, Prf) :-
  length(Lns, Lth),
  Idx is Lth - 1,
  nth0(Idx, Lns, ln(_, [], Rul)),
  cmpl(Mat, Lns, [], Rul, Prf).

cmpl(Mat, Lns, cmpl_error(Mat, Lns)).


trms_string(Trms, Str) :-
  maplist(trm_string, Trms, TrmStrs),
  tuple_string(TrmStrs, Str).

trm_string(var(Num), Str) :-
  number_string(Num, NumStr),
  string_concat("X", NumStr, Str).

trm_string(fn(Num, Trms), Str) :-
  number_string(Num, NumStr),
  trms_string(Trms, TrmsStr),
  join_string(["f", NumStr, TrmsStr], Str).

atm_string(rl(Num, Trms), Str) :-
  number_string(Num, NumStr),
  trms_string(Trms, TrmsStr),
  join_string(["r", NumStr, TrmsStr], Str).

atm_string(eq(TrmA, TrmB), Str) :-
  trm_string(TrmA, StrA),
  trm_string(TrmB, StrB),
  join_string(["(", StrA, " = ", StrB, ")"], Str).

lit_string(lit(pos, Atm), Str) :-
  atm_string(Atm, Str).

lit_string(lit(neg, Trm), Str) :-
  trm_string(Trm, Str1),
  string_concat("-", Str1, Str).

map_string(map(Num, Trm), Str) :-
  number_string(Num, NumStr),
  trm_string(Trm, TrmStr),
  join_string([NumStr, " |-> ", TrmStr], Str).

list_string(ItemString, Lst, Str) :-
  maplist(ItemString, Lst, Strs),
  join_string(Strs, ", ", TmpStr),
  join_string(["[", TmpStr, "]"], Str).

cla_string(Cla, Str) :-
  list_string(lit_string, Cla, Str).

maps_string(Maps, Str) :-
  list_string(map_string, Maps, Str).

proof_string(Spcs, hyp(Num, Cnc), Str) :-
  number_string(Num, NumStr),
  cla_string(Cnc, CncStr),
  join_string([Spcs, "hyp ", NumStr, " : ", CncStr], Str).

proof_string(Spcs, res(PrfA, PrfB, Cnc), Str) :-
  string_concat("  ", Spcs, NewSpcs),
  cla_string(Cnc, CncStr),
  proof_string(NewSpcs, PrfA, StrA),
  proof_string(NewSpcs, PrfB, StrB),
  string_codes(Nl, [10]),
  join_string([Spcs, "res : ", CncStr, Nl, StrA, Nl, StrB], Str).

proof_string(Spcs, sub(Maps, PrfA, Cnc), Str) :-
  string_concat("  ", Spcs, NewSpcs),
  maps_string(Maps, MapsStr),
  cla_string(Cnc, CncStr),
  proof_string(NewSpcs, PrfA, StrA),
  string_codes(Nl, [10]),
  join_string([Spcs, "sub : ", CncStr, Nl, NewSpcs, MapsStr, Nl, StrA], Str).

proof_string(Spcs, rot(Num, PrfA, Cnc), Str) :-
  string_concat("  ", Spcs, NewSpcs),
  number_string(Num, NumStr),
  proof_string(NewSpcs, PrfA, StrA),
  cla_string(Cnc, CncStr),
  string_codes(Nl, [10]),
  join_string([Spcs, "rot ", NumStr, " : ", CncStr, Nl, StrA], Str).

proof_string(Spcs, cnt(PrfA, Cnc), Str) :-
  string_concat("  ", Spcs, NewSpcs),
  proof_string(NewSpcs, PrfA, StrA),
  cla_string(Cnc, CncStr),
  string_codes(Nl, [10]),
  join_string([Spcs, "cnt : ", CncStr, Nl, StrA], Str).

proof_string(Prf, Str) :-
  proof_string("", Prf, Str).

proof_string(Prf, print_error(Prf)).

ln_string(ln(Num, Cla, Rul), Str) :-
  number_string(Num, NumStr),
  cla_string(Cla, ClaStr),
  term_string(Rul, RulStr),
  join_string([NumStr, ". ", ClaStr, " [", RulStr, "]"], Str).

lns_string(Lns, Str) :-
  maplist(ln_string, Lns, Strs),
  string_codes(Nl, [10]),
  join_string(Strs, Nl, Str).
*/
