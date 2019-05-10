:- op( 500, fy, !).    % universal quantifier
:- op( 500, fy, ~).    % negation
:- op(1130, xfy, <=>). % equivalence
:- op(1110, xfy, =>).  % implication
:- op( 500, xfy, :).

fof(f83,plain,(
  ( ! [X0,X1] : (~animal(a_snail) |
    ~much_smaller(a_snail,X0) | ~animal(X0) | eats(X0,a_snail) | eats(X0,X1) | ~plant(X1) | ~snail(a_snail)) )),
  inference(resolution,[],[f79,f25])).

fof(f87,plain,(
  spl0_15 <=> ~snail(a_snail)),
  introduced(avatar_definition,[new_symbols(naming,[spl0_15])])).

fof(f90,plain,(
  spl0_16 <=> ! [X1,X0] : (~much_smaller(a_snail,X0) | ~plant(X1) | eats(X0,X1) | eats(X0,a_snail) | ~animal(X0))),
  introduced(avatar_definition,[new_symbols(naming,[spl0_16])])).

fof(f93,plain,(
  spl0_19 <=> ~animal(a_snail)),
  introduced(avatar_definition,[new_symbols(naming,[spl0_19])])).

fof(f95,plain,(
  ~spl0_15 | spl0_16 | ~spl0_19),
  inference(avatar_split_clause,[],[f83,f93,f90,f87])).
