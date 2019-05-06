foo(X) :- not(X == 0).

bar(X, Y) :- include(foo, X, Y).

quz(L, M) :- maplist(bar, L, M).
