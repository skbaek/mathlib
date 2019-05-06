assignVar([], 0, V, [V]).

assignVar([], N, V, [W|Vs]) :-
  M is N - 1,
  assignVar([], M, V, Vs).

assignVar([V|Vs], 0, V, [V|Vs]).

assignVar([V|Vs], N, W, [V|Ws]) :-
  M is N - 1,
  assignVar(Vs, M, W, Ws).

parseLit(["-" | Ts], Vs, -L, Ts1, Vs1) :-
  parseLit(Ts, Vs, L, Ts1, Vs1).

parseLit(["S" | [T | Ts]], Vs, (N), Ts, Vs) :-
  number_string(N, T).

parseLit(["V" | [T | Ts]], Vs, L, Ts, Vs1) :-
  number_string(N, T), assignVar(Vs, N, L, Vs1).

parseLit(["(" | Ts], Vs, app(L1, L2), Ts2, Vs2) :-
  parseLit(Ts,  Vs,  L1, Ts1, Vs1),
  parseLit(Ts1, Vs1, L2, [")" | Ts2], Vs2).

parseCla(Ts, Vs, [L | C], Ts2, Vs2) :-
  parseLit(Ts, Vs, L, Ts1, Vs1),
  parseCla(Ts1, Vs1, C, Ts2, Vs2).

parseCla(["|" | Ts], Vs, [], Ts, Vs).

parseMatCore(Ts, [C | M]) :-
  parseCla(Ts, [], C, Ts1, _),
  parseMatCore(Ts1, M).

parseMatCore([], []).

parseMat(MS, M) :-
  split_string(MS, " ", " ", Ts),
  parseMatCore(Ts, M).
