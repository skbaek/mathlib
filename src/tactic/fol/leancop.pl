#!/usr/bin/env swipl

:- initialization(main, main).
:- style_check(-singleton).

:- [parse].
:- [print].

isPoint(-!).

removePoint(X, Y) :- exclude(isPoint, X, Y).

removePoints(P, Q) :- maplist(removePoint, P, Q).

prove(Mat, PathLim, Used) :-
     append(MatA, [Cla |MatB ], Mat),
     \+member(-_,Cla),
     append(MatA, MatB, Mat1),
     prove([!], [[-! | Cla] | Mat1], [], PathLim, Used).

prove(Mat, PathLim, Used) :-
     \+ground(Mat), PathLim1 is PathLim+1, prove(Mat, PathLim1, Used).

prove([], _, _, _, []).

prove([Lit | Cla], Mat, Path, PathLim, Used) :-
  (-NegLit=Lit ; -Lit=NegLit) ->
  (
    (
      member(NegL,Path),
      unify_with_occurs_check(NegL, NegLit),
      Used1 = []
    )
    ;
    (
      append(MatA,[Cla1|MatB],Mat), copy_term(Cla1,Cla2),
      append(ClaA,[NegL|ClaB],Cla2),
      unify_with_occurs_check(NegL,NegLit),
      append(ClaA,ClaB,Cla3),
      (
        Cla1==Cla2 ->
          append(MatB,MatA,Mat1)
          ;
          length(Path,K), K<PathLim,
          append(MatB,[Cla1|MatA],Mat1)
      ),
      prove(Cla3,Mat1,[Lit|Path],PathLim, Used2),
      Used1 = [Cla2 | Used2]
    )
  ),
  prove(Cla, Mat, Path, PathLim, Used3),
  append(Used1, Used3, Used).

main([MS|_]) :-
  parseMat(MS, M),
  prove(M, 1, U),
  removePoints(U, P),
  printMat(P, S),
  write(S).
