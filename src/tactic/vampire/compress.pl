:- [basic].

% Remove rotation by zero

rm_rot_zero(hyp(Num, Cla), hyp(Num, Cla)).

rm_rot_zero(rot(0, Prf, _), NewPrf) :-
  rm_rot_zero(Prf, NewPrf).

rm_rot_zero(rot(Num, Prf, Cla), rot(Num, NewPrf, Cla)) :-
  0 < Num,
  rm_rot_zero(Prf, NewPrf).

rm_rot_zero(res(PrfA, PrfB, Cla), res(NewPrfA, NewPrfB, Cla)) :-
  rm_rot_zero(PrfA, NewPrfA),
  rm_rot_zero(PrfB, NewPrfB).

rm_rot_zero(sub(Maps, Prf, Cla), sub(Maps, NewPrf, Cla)) :-
  rm_rot_zero(Prf, NewPrf). 

rm_rot_zero(rep(PrfA, PrfB, Cla), rep(NewPrfA, NewPrfB, Cla)) :-
  rm_rot_zero(PrfA, NewPrfA),
  rm_rot_zero(PrfB, NewPrfB).

rm_rot_zero(trv(Prf, Cla), trv(NewPrf, Cla)) :-
  rm_rot_zero(Prf, NewPrf).

rm_rot_zero(sym(Prf, Cla), sym(NewPrf, Cla)) :-
  rm_rot_zero(Prf, NewPrf).

rm_rot_zero(cnt(Prf, Cla), cnt(NewPrf, Cla)) :-
  rm_rot_zero(Prf, NewPrf).

% Push maps upward

push_maps(hyp(Num, Cla), Maps, sub(Maps, hyp(Num, Cla), NewCla)) :-
  subst_cla(Maps, Cla, NewCla).

push_maps(rot(Num, Prf, Cla), Maps, rot(Num, NewPrf, Cla)) :-
  push_maps(Prf, Maps, NewPrf).

push_maps(res(PrfA, PrfB, Cla), Maps, res(NewPrfA, NewPrfB, Cla)) :-
  push_maps(PrfA, Maps, NewPrfA),
  push_maps(PrfB, Maps, NewPrfB).

push_maps(sub(MapsA, Prf, _), MapsB, NewPrf) :-
  compose_maps(MapsA, MapsB, Maps),
  push_maps(Prf, Maps, NewPrf). 

push_maps(rep(PrfA, PrfB, Cla), Maps, sub(Maps, rep(PrfA, PrfB, Cla), NewCla)) :- 
  subst_cla(Maps, Cla, NewCla).

push_maps(trv(Prf, Cla), Maps, trv(NewPrf, Cla)) :-
  push_maps(Prf, Maps, NewPrf).

push_maps(sym(Prf, Cla), Maps, sym(NewPrf, Cla)) :-
  push_maps(Prf, Maps, NewPrf).

push_maps(cnt(Prf, Cla), Maps, cnt(NewPrf, Cla)) :-
  push_maps(Prf, Maps, NewPrf).

% Remove superfluous mappings

relevant(Vars, map(Num, _)) :-
  member(Num, Vars).

filter_maps(Prf, Maps, NewMaps) :-
  conc(Prf, Cnc),
  vars_cla(Cnc, Vars),
  include(relevant(Vars), Maps, NewMaps).

src(Num, map(Num, _)).

rm_red_maps([], []).

rm_red_maps([map(Num, Trm) | Maps], [map(Num, Trm) | NewMaps]) :- 
  exclude(src(Num), Maps, TmpMaps),
  rm_red_maps(TmpMaps, NewMaps).

idmap(map(Num, var(Num))).

rm_maps_core(Vrs, Maps, NewMaps) :-
  rm_red_maps(Maps, Maps1),
  exclude(idmap, Maps1, Maps2),
  include(relevant(Vrs), Maps2, NewMaps).

rm_maps(hyp(Num, Cla), hyp(Num, Cla)).

rm_maps(rot(Num, Prf, Cla), rot(Num, NewPrf, Cla)) :-
  rm_maps(Prf, NewPrf).

rm_maps(res(PrfA, PrfB, Cla), res(NewPrfA, NewPrfB, Cla)) :-
  rm_maps(PrfA, NewPrfA),
  rm_maps(PrfB, NewPrfB).

rm_maps(sub(Maps, Prf, Cla), NewPrf) :-
  conc(Prf, Cnc),
  vars_cla(Cnc, Vrs),
  ( ( rm_maps_core(Vrs, Maps, []), rm_maps(Prf, NewPrf) ) ; 
    ( rm_maps_core(Vrs, Maps, NewMaps), 
      rm_maps(Prf, TmpPrf), 
      NewPrf = sub(NewMaps, TmpPrf, Cla) ) ).

rm_maps(rep(PrfA, PrfB, Cla), rep(NewPrfA, NewPrfB, Cla)) :-
  rm_maps(PrfA, NewPrfA),
  rm_maps(PrfB, NewPrfB).

rm_maps(trv(Prf, Cla), trv(NewPrf, Cla)) :-
  rm_maps(Prf, NewPrf).

rm_maps(sym(Prf, Cla), sym(NewPrf, Cla)) :-
  rm_maps(Prf, NewPrf).

rm_maps(cnt(Prf, Cla), cnt(NewPrf, Cla)) :-
  rm_maps(Prf, NewPrf).

% Main compression predicate.

compress(Prf, NewPrf) :-
  rm_rot_zero(Prf, Prf1),
  push_maps(Prf1, [], Prf2),
  rm_maps(Prf2, NewPrf).
