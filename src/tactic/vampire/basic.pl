join_string([], _, "").

join_string([Str], _, Str).

join_string([Str | Strs], Jn, Rst) :-
  string_concat(Str, Jn, Str1),
  join_string(Strs, Jn, Str2),
  string_concat(Str1, Str2, Rst).

join_string(Strs, Str) :-
  join_string(Strs, "", Str).

is_digit(Cd) :- 47 < Cd, Cd < 58.

head_is_digit([Cd | _]) :- is_digit(Cd).

split_string_at(Str, Sep, Fst, Snd) :-
  string_concat(Fst, Tmp, Str),
  string_concat(Sep, Snd, Tmp).

number_binstr(0, "0").
number_binstr(1, "1").
number_binstr(Num, Str) :-
  Num > 1,
  Mod is Num mod 2,
  Quo is Num // 2,
  number_binstr(Quo, Str1),
  number_binstr(Mod, Str2),
  string_concat(Str1, Str2, Str).

max(Num1, Num2, Num1) :- Num1 >= Num2.
max(Num1, Num2, Num2) :- Num1 < Num2.

union([], []).

union([Lst | Lsts], Un) :-
  union(Lsts, Tmp),
  union(Lst, Tmp, Un).

break_list(0, Lst, [], Lst).

break_list(Num, [Elm | Lst], [Elm | Fst], Snd) :-
  0 < Num,
  NewNum is Num - 1,
  break_list(NewNum, Lst, Fst, Snd).

break_string(Num, Str, Fst, Snd) :-
  string_codes(Str, Cds),
  break_list(Num, Cds, FstCds, SndCds),
  string_codes(Fst, FstCds),
  string_codes(Snd, SndCds).

break_string(Num, Str, [Str]) :-
  string_length(Str, Lth),
  Lth =< Num.

break_string(Num, Str, [Hd | Tl]) :-
  break_string(Num, Str, Hd, Rem),
  break_string(Num, Rem, Tl).

tor([Hd | Tl], 0, [Hd | Tl]).

tor([Hd | Tl], Idx, [HdA, Hd | TlA]) :-
  tor(Tl, IdxA, [HdA | TlA]),
  Idx is IdxA + 1.

rot(0, [Hd | Tl], [Hd | Tl]).

rot(Idx, [Hd | Tl], [NewHd, Hd | NewTl]) :-
  0 < Idx,
  NewIdx is Idx - 1,
  rot(NewIdx, Tl, [NewHd | NewTl]).

conc([line(_, _, Cnc) | _], Cnc).

union_list([], []).

union_list([Lst | Lsts], Un) :-
  union_list(Lsts, Tmp),
  union(Lst, Tmp, Un).

vars_trm(vr(Num), [Num]).

vars_trm(fn(_, Trms), Nums) :-
  maplist(vars_trm, Trms, Numss),
  union_list(Numss, Nums).

vars_atm(rl(_, Trms), Nums) :-
  maplist(vars_trm, Trms, Numss),
  union_list(Numss, Nums).

vars_atm(eq(TrmA, TrmB), Nums) :-
  vars_trm(TrmA, NumsA),
  vars_trm(TrmB, NumsB),
  union(NumsA, NumsB, Nums).

vars_lit(lit(_, Atm), Nums) :-
  vars_atm(Atm, Nums).

vars_cla(Cla, Nums) :-
  maplist(vars_lit, Cla, Numss),
  union(Numss, Nums).

subst_trms(Inst, Trms, NewTrms) :-
  maplist(subst_trm(Inst), Trms, NewTrms).

subst_trm(Inst, vr(Num), vr(Num)) :-
  not(member(map(Num, _), Inst)).

subst_trm(Inst, vr(Num), Trm) :-
  member(map(Num, Trm), Inst), !.

subst_trm(Inst, fn(Num, Trms), fn(Num, NewTrms)) :-
  subst_trms(Inst, Trms, NewTrms).

subst_atm(Inst, eq(SrcTrmA, SrcTrmB), eq(TgtTrmA, TgtTrmB)) :-
  subst_trm(Inst, SrcTrmA, TgtTrmA),
  subst_trm(Inst, SrcTrmB, TgtTrmB).

subst_atm(Inst, rl(Num, Trms), rl(Num, NewTrms)) :-
  subst_trms(Inst, Trms, NewTrms).

subst_lit(Map, lit(Pol, SrcAtm), lit(Pol, TgtAtm)) :-
  subst_atm(Map, SrcAtm, TgtAtm).

subst_cla(Inst, Cla, NewCla) :-
  maplist(subst_lit(Inst), Cla, NewCla).

update_map(Map, map(Src, Tgt), map(Src, NewTgt)) :-
  subst_trm(Map, Tgt, NewTgt).

update_inst(FstInst, SndInst, NewFstInst) :-
  maplist(update_map(SndInst), FstInst, NewFstInst).

compose_inst(FstInst, SndInst, Inst) :-
  update_inst(FstInst, SndInst, NewFstInst),
  append(NewFstInst, SndInst, Inst).

compose_insts([Inst], Inst).

compose_insts([Inst | Insts], NewInst) :-
  compose_insts(Insts, TmpInst),
  compose_inst(Inst, TmpInst, NewInst).

relevant(Vars, map(Num, _)) :-
  member(Num, Vars).

src(Num, map(Num, _)).

rm_red_inst([], []).

rm_red_inst([map(Num, Trm) | Inst], [map(Num, Trm) | NewInst]) :-
  exclude(src(Num), Inst, TmpInst),
  rm_red_inst(TmpInst, NewInst).

is_id(map(Num, vr(Num))).

compress_inst(Cla, Inst, NewInst) :-
  rm_red_inst(Inst, Inst1),
  exclude(is_id, Inst1, Inst2),
  vars_cla(Cla, Vrs),
  include(relevant(Vrs), Inst2, NewInst).

compress_compose_insts(Cla, Insts, Inst) :-
  compose_insts(Insts, TmpInst),
  compress_inst(Cla, TmpInst, Inst).
