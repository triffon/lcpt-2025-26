man(john).
woman(mary).

loves(john,beer).
loves(mary,beer).
loves(john, X) :- loves(X, beer). 

% n(?X)
n(o).
n(s(X)) :- n(X).

% even(?X)
even(o).
even(s(s(X))) :- even(X).

% add(+X,+Y,?Z).
% add(+X,?Y,+Z).
% add(?X,+Y,+Z).
add(o,X,X).
add(s(X),Y,s(Z)) :- add(X,Y,Z).

% memb(?X,+L)

memb(X,[X|_]).
memb(X,[_|T]) :- memb(X,T).
