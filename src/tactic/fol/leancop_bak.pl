#!/usr/bin/env swipl

:- initialization(main, main).

:- set_prolog_flag(optimise,true).

:- dynamic(pathlim/0), dynamic(lit/4).

:- style_check(-singleton).

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

% parseCla(["[" | Ts], C, Ts1) :-
%   parseClaCore(Ts, [], C, Ts1, _).

parseMatCore(Ts, [C | M]) :-
  parseCla(Ts, [], C, Ts1, _),
  parseMatCore(Ts1, M).

parseMatCore([], []).

parseMat(MS, M) :-
  split_string(MS, " ", " ", Ts),
  parseMatCore(Ts, M).

%%% prove matrix M / formula F

prove(F,Proof) :- prove2(F,[cut,comp(7)],Proof).

prove2(F,Set,Proof) :-
    (F=[_|_] -> M=F ; make_matrix(F,M,Set)),
    retractall(lit(_,_,_,_)), (member([-(#)],M) -> S=conj ; S=pos),
    assert_clauses(M,S), prove(1,Set,Proof).

prove(PathLim,Set,Proof) :-
    \+member(scut,Set) -> prove([-(#)],[],PathLim,[],Set,[Proof]) ;
    lit(#,_,C,_) -> prove(C,[-(#)],PathLim,[],Set,Proof1),
    Proof=[C|Proof1].

prove(PathLim,Set,Proof) :-
    member(comp(Limit),Set), PathLim=Limit -> prove(1,[],Proof) ;
    (member(comp(_),Set);retract(pathlim)) ->
    PathLim1 is PathLim+1, prove(PathLim1,Set,Proof).

%%% leanCoP core prover

prove([],_,_,_,_,[]).

prove([Lit|Cla],Path,PathLim,Lem,Set,Proof) :-
    Proof=[[[NegLit|Cla1]|Proof1]|Proof2],
    \+ (member(LitC,[Lit|Cla]), member(LitP,Path), LitC==LitP),
    (-NegLit=Lit;-Lit=NegLit) ->
       ( member(LitL,Lem), Lit==LitL, Cla1=[], Proof1=[]
         ;
         member(NegL,Path), unify_with_occurs_check(NegL,NegLit),
         Cla1=[], Proof1=[]
         ;
         lit(NegLit,NegL,Cla1,Grnd1),
         unify_with_occurs_check(NegL,NegLit),
         ( Grnd1=g -> true ; length(Path,K), K<PathLim -> true ;
           \+ pathlim -> assert(pathlim), fail ),
         prove(Cla1,[Lit|Path],PathLim,Lem,Set,Proof1)
       ),
       ( member(cut,Set) -> ! ; true ),
       prove(Cla,Path,PathLim,[Lit|Lem],Set,Proof2).

%%% write clauses into Prolog's database

assert_clauses([],_).
assert_clauses([C|M],Set) :-
    (Set\=conj, \+member(-_,C) -> C1=[#|C] ; C1=C),
    (ground(C) -> G=g ; G=n), assert_clauses2(C1,[],G),
    assert_clauses(M,Set).

assert_clauses2([],_,_).
assert_clauses2([L|C],C1,G) :-
    assert_renvar([L],[L2]), append(C1,C,C2), append(C1,[L],C3),
    assert(lit(L2,L,C2,G)), assert_clauses2(C,C3,G).

assert_renvar([],[]).
assert_renvar([F|FunL],[F1|FunL1]) :-
    ( var(F) -> true ; F=..[Fu|Arg], assert_renvar(Arg,Arg1),
      F1=..[Fu|Arg1] ), assert_renvar(FunL,FunL1).

depoint([], []).
depoint([(#) | C], D) :-
  depoint(C, D).
depoint([L | C], [L | D]) :-
  depoint(C, D).

flatten([C], [D]) :- depoint(C, D).

flatten([C, P], [D | M]) :-
  depoint(C, D),
  flatten(P, M).

formatLit(-A, S) :-
  formatLit(A, AS),
  string_concat("- ", AS, S).

formatLit(app(A, B), S) :-
  formatLit(A, AS),
  formatLit(B, BS),
  string_concat("( ", AS, PAS),
  string_concat(PAS, " ", PASS),
  string_concat(BS, " )", BSS),
  string_concat(PASS, BSS, S).

formatLit(N, S) :- atom_string(N, S).

formatCla([], "").

formatCla([L | C], S) :-
  formatLit(L, LS),
  formatCla(C, CS),
  string_concat(LS, " ", LSS),
  string_concat(LSS, CS, S).

formatMat([], "").

formatMat([C | M], S) :-
  formatCla(C, CS),
  formatMat(M, MS),
  string_concat(CS, "| ", CSS),
  string_concat(CSS, MS, S).

main([MS|_]) :-
  parseMat(MS, M),
  prove(M, P),
  flatten(P, N),
  formatMat(N, S),
  write(S).
  % write(M).
