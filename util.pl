%% Utility Procedures %%
%% Alan Bundy, 31.1.12 %%


%% pprint(E): convert to input form and print

pprint(vble(X)) :- print(X),!.

pprint(vble(X):sort(S)) :- print(X),print(':'),print(S),!.

pprint([F|Args]) :- atomic(F), !, 
    convert(E,[F|Args]), print(E).

pprint([]).

pprint([NE1=NE2|NEL]) :- !,
    convert(E1,NE1), convert(E2,NE2), 
    print(E1=E2), print(', '),  pprint(NEL).

pprint([NE|NEL]) :- !,
    precedence(NE,NE1,NE2),
    convert(E1,NE1), convert(E2,NE2), 
    print(E1/E2), print(', '), pprint(NEL).

% verbose(Switch): if Switch is on, use pretty printing

:- dynamic verbose/1.

verbose(off).

%% switch verbose on or off

switch :- verbose(S),retractall(verbose(S)), opposite(S,NS), assert(verbose(NS)),!.

%% opposite(S,NS): S and NS are opposites
opposite(on,off).
opposite(off,on).

% Keeps track of the current result of unification (FS) which is known at the end of recursion in reform2.
:- dynamic refsuccess/0.
refsuccess(success) :- refsuccess,!.
refsuccess(fail) :- \+(refsuccess),!.

%% convert(In,Out): convert normal Prolog syntax to internal representation or
%% vice versa.


% X is a sorted variable
convert(X:S,vble(X):T) :-                       % Convert X into a variable
    atomic(X), atom_chars(X,[H|_]),             % if first letter
    convertSort(S,T),                           %   Convert sort to internal representation
    char_code(H,N), 109<N, N<123, !.            % is n-z

% A is a constant
convert(A:S,[A]:T) :-                           % Convert A into a constant
    atomic(A), atom_chars(A,[H|_]),             % If first letter 
    convertSort(S,T),                           %   Convert sort to internal representation
    char_code(H,N), 96<N, N<110, !.             % Is a-m

% A is a number
convert(A:S,[A]:T) :-             % Convert A into a constant
    number(A),                    % Convert sort to internal representation
    convertSort(S,T), !.          % if it is a number

%% These variable/constant conventions need revisiting for serious use

convert(E,E:S) :- 
    var(E), convertSort(s,S), !.

% E is compound
convert(E:S,[F|NArgs]:T) :- 
    var(E), !,                                  % If E is output and input compound
    convertSort(S,T),                           % Convert sort to internal representation
    maplist(convert,Args,NArgs), E=..[F|Args].  % Recurse on all args of F

convert(E:S,[F|NArgs]:T) :-                     % If E is input and compound then
    \+ var(E), \+ atomic(E), !,  E=..[F|Args],  % break it into components
    convertSort(S,T),                           % Convert sort to internal representation
    maplist(convert,Args,NArgs).                % and recurse on them

% if no sort specified use default (s).
convert(X,R) :-
    convert(X:top,R).


% sort variable
convertSort(S,sort(S)).


%% orlist(F,List): check F true on any element of List

% Step case
orlist(F,[H|T]) :- (call(F,H); orlist(F,T)).    % True if either true on head or tail


%% pairwise(L1,L2,Pairlist): pairs up corresponding elements of two lists. 

% Base case
pairwise([],[],[]).             % If input two empty lists then return one.

% Step case
pairwise([H1|T1],[H2|T2],[H1=H2|T]) :- % Otherwise, pair up the heads
     pairwise(T1,T2,T).                % and recurse on the tails. 


%% disjoin(D1,D2,D): return either D1 or D2 as D

% If they are the same, just return one.
disjoin(D,D,D) :- !.

% If either is empty, return the other. 

disjoin([],D,D) :- !.
disjoin(D,[],D) :- !.

% Otherwise, just return one

disjoin(D1,D2,D) :- !, (D1=D ; D2=D).


 
% contains(vble(X):Sx,Rest): is vble(X):Sx contained in the Rest on either side
contains(vble(X):Sx,Rest) :- orlist(contains2(vble(X):Sx),Rest), !.

contains2(vble(X):Sx,vble(X):Sx=_) :- !.
contains2(vble(X):Sx,_=vble(X):Sx) :- !.

contains2(vble(X):Sx,[_|Args]:_=_) :- orlist(contains2(vble(X):Sx),Args), !.
contains2(vble(X):Sx,_=[_|Args]:_) :- orlist(contains2(vble(X):Sx),Args), !.



containsR(X,Rep,Reps) :- orlist(containsRep(X,Rep),Reps).
containsRep(X,Rep,Rep) :- Rep =..[_|Args], orlist(containsA(X), Args),!.   % TODO: get all Repairs
containsA(X,X) :- !.

% containsDifferent(vble(X):Sx,Rest): is vble(X):Sx contained in the Rest on either side, 
%   and is it unified against a different term (TODO: make it ununifiable)
containsDifferent(vble(X):Sx,Term,Rest) :- orlist(containsDifferent2(vble(X):Sx,Term),Rest), !.

containsDifferent2(vble(X):Sx,Term,vble(X):Sx=Term2) :- Term \== Term2,!.
containsDifferent2(vble(X):Sx,Term,Term2=vble(X):Sx) :- Term \== Term2,!.

containsDifferent2(vble(X):Sx,[_|Args]:_=Term) :- orlist(containsDifferent2(vble(X):Sx,Term),Args), !.
containsDifferent2(vble(X):Sx,Term=[_|Args]:_) :- orlist(containsDifferent2(vble(X):Sx,Term),Args), !.


%% occurs(vble(X):Sx,E): variable vble(X):Sx occurs in compound expression E

% Occurs check succeeds if it succeeds on any argument
occurs(vble(X):Sx,[_|Args]:_) :- orlist(occurs2(vble(X):Sx),Args), !.


occurs(V,+T) :- !, occurs(V,T).
occurs(V,-T) :- !, occurs(V,T).
occurs(V,Clause) :- !, orlist(occurs(V),Clause). 

%% occurs2(vble(X),E): variable vble(X) occurs in any expression E
% Base case
occurs2(vble(X):Sx,vble(X):Sx) :- !.

% Step case
occurs2(vble(X):Sx,[_|Args]:_) :- !, orlist(occurs2(vble(X):Sx),Args).

% subst(V/E,E1,E2): E2 is the result of substituting E for V in E1.

subst(vble(X):R,vble(X):S,E) :- R=SC:D, (SC=S/C, E =C:D;S\==D, E=vble(X):S),!.   % split pattern X:Y/Z (solve precedence problem)

subst(vble(X):Sx,vble(Y):Sy,vble(Y):Sy) :- (X\==Y;Sx\==Sy),!.     % If E1 is another variable then ignore

subst(Subst,[F|Args1]:S,[F|Args2]:S) :- 
   atomic(F), maplist(subst(Subst),Args1,Args2),!. % If E1 is compound then recurse on args.

subst(Subst,[E1=E2|Tl],[NE1=NE2|NTl]) :-       % If E1 is unification problem then
   subst(Subst,E1,NE1), subst(Subst,E2,NE2),   % apply substitution to both sides
   subst(Subst,Tl,NTl),!.                        % then recurse on tails

subst(Subst,[+E|T],[+NE|NT]) :-         % for substituting resolution ready clauses
   subst(Subst,E,NE),
   subst(Subst,T,NT),!.  

subst(Subst,[-E|T],[-NE|NT]) :-
   subst(Subst,E,NE),
   subst(Subst,T,NT),!.  

subst(Subst,[VE|T],[VNE|NT]) :-          % If E1 is substitution then
   precedence(VE,V,E),                   % if substitution, VE = V/E
   subst(Subst,E,NE),                    % apply substitution to value
   precedence(VNE,V,NE),                 % join back
   subst(Subst,T,NT),!.                    % then recurse on tails

subst([Subst|Substs], E,NE) :- subst(Subst,E,NE1), subst(Substs,NE1,NE), !.
subst(_,[],[]) :-!.                          % If E1 is empty problem then do nothing
subst([],E,E) :-!.

substR(X/Y,Old,New) :- Old=..[F|Args], New=..[F|NewArgs], substA(X/Y,Args,NewArgs),!.
substA(X/Y,[X|Rest],[Y|NewRest]) :- substA(X/Y,Rest,NewRest),!.
substA(X/Y,[Z|Rest],[Z|NewRest]) :- Z\==X, substA(X/Y,Rest,NewRest),!.
substA(_,[],[]).

precedence(F,FL,FR) :- 
   F=A:BCD, BCD=BC:D,BC=B/C,
   FL=A:B,FR=C:D.

%% compose(Sub,SublistIn,SublistOut): SublistOut is the result of composing
%% singleton substitution Subst with substitution SublistIn

compose(Sub,SublistIn,[Sub|SublistMid]) :-     % Append new substitution
    subst(Sub,SublistIn,SublistMid).           % after applying it to the old one
    

%% and(FS1,FS2,FS): conjoin FS1 and FS2 to get FS

and(fail,fail,fail).
and(fail,success,fail).
and(success,fail,fail).
and(success,success,success).


%% gensym(In,Out): generate new symbol Out as In with suffix

gensym(In,Out) :-
    atom_chars(In,InList),                    % Turn atom into list of characters
    append(InList,[d,a,s,h],Outlist),         % Append a dash to the list 
    atom_chars(Out,Outlist).                  % and turn it back into an atom

% This simplistic renaming needs rethinking for serious use


%% position(Sub,Exp,Posn): Sub is at position Posn in Exp

% Base Case

position(Exp,Exp,[]).               % The current expression is at the empty position

% Step Case

position(Sub,[_|Args]:_,[I|Posn]) :-  % Otherwise, get the args of a compound expression
    append(Front,[Arg|_],Args),     % Use append backwards to identify each argument in turn
    length(Front,I1), I is I1+1,    % Work out what its position is
    position(Sub,Arg,Posn).         % Recurse on each argument


%% replace(P,E1,Sub,E2): replace position P in E1 with Sub to get E2

% Base case: found position.
replace([],_,Sub,Sub).              % To replace the current position return Sub

% Step case: find Ith argument and recurse on it
replace([I|Posn],[F|Args1]:Sf,Sub,[F|Args2]:Sf) :-    % To replace anyother position
    I1 is I-1, length(Front,I1),                % Front is the first I-1 args
    append(Front,[Arg1|Back],Args1),            % Arg1 is the Ith
    replace(Posn,Arg1,Sub,Arg2),                % Recurse on the Ith arg then
    append(Front,[Arg2|Back],Args2).            % place new Ith arg back in the expression.



% quick sort by value for a list of pairs (value, repair)
quicksort(List,Sorted):-q_sort(List,[],Sorted).
q_sort([],Acc,Acc) :- !.
q_sort([H|T],Acc,Sorted):-
  pivoting(H,T,L1,L2),
  q_sort(L1,Acc,Sorted1),q_sort(L2,[H|Sorted1],Sorted).

pivoting(_,[],[],[]) :- !.
pivoting(((H1,H2),Vh),[((X1,X2),Vx)|T],[((X1,X2),Vx)|L],G):- (X1>H1; X1==H1,X2=<H2),  pivoting(((H1,H2),Vh),T,L,G), !.
pivoting(((H1,H2),Vh),[((X1,X2),Vx)|T],L,[((X1,X2),Vx)|G]):- pivoting(((H1,H2),Vh),T,L,G).


pickSnds(Pairs,Snds) :- maplist(pickSnd,Pairs,Snds).
pickSnd((_,Y),Y).


% detect negation
truefalse(-_,fail) :-!.
truefalse(_,success).


% converting between lists and tuples
list2tuple([A],A) :-!.
list2tuple([A|B1],','(A,B)) :- !, list2tuple(B1,B).

tuple2list(','(A,B), [A|B1]) :- !, tuple2list(B,B1).
tuple2list(A,[A]).

vprint(X) :- verbose(on),!, print(X); true.
vnl :- verbose(on),!,nl; true.


%% switch(L,R): switch left for right and vice versa

switch(left,right).
switch(right,left).
