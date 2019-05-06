printLit(-A, S) :-
  printLit(A, AS),
  string_concat("- ", AS, S).

printLit(app(A, B), S) :-
  printLit(A, AS),
  printLit(B, BS),
  string_concat("( ", AS, PAS),
  string_concat(PAS, " ", PASS),
  string_concat(BS, " )", BSS),
  string_concat(PASS, BSS, S).

printLit(N, S) :- atom_string(N, S).

printCla([], "").

printCla([L | C], S) :-
  printLit(L, LS),
  printCla(C, CS),
  string_concat(LS, " ", LSS),
  string_concat(LSS, CS, S).

printMat([], "").

printMat([C | M], S) :-
  printCla(C, CS),
  printMat(M, MS),
  string_concat(CS, "| ", CSS),
  string_concat(CSS, MS, S).
