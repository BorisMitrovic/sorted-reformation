%% Diagnose Unification Problems and Suggest Repairs %%
%% Alan Bundy, 30.1.12 %%


%% diagnose(W,FS,Eq,Rs): if result from Eq unwanted W\=FS then suggest repairs
%% Rs to signature

% Do nothing if result is as wanted. Do not back up
diagnose(FS,FS,_,[],_) :- !.

% Suggest repair if success wanted but failure produced. 

% Case CCf repairs: merge functors and make same arity
diagnose(success,fail,[F1|Args1]:S1=[F2|Args2]:S2,Rs,Ss) :- !, 
    merge_funcs(F1:S1,F2:S2,Rs1),                 % Merge functors if they are different
    same_arity([F1|Args1]:S1,[F2|Args2]:S2,Rs2),  % Equate arities if they are different
    merge_sorts(F1:S1,F2:S2,Rs3,Ss),                 % Merge sorts    if they are different
    append(Rs1,Rs2,Rs12),
    append(Rs12,Rs3,Rs).                    % Conjoin these repairs

% Case VCf repairs: remove occurrences of X
diagnose(success,fail,vble(X):Sx=[F|Args]:Sf,Rs,Ss) :-
    \+(position(vble(X):Sx,[F|Args]:Sf,_)),    % Find position that X occurs at
    merge_sorts(vble(X):Sx,[F|Args]:Sf,Rs,Ss).               % Merge sorts if they are different

% Case VCf repairs: remove occurrences of X
diagnose(success,fail,vble(X):Sx=[F|Args]:Sf,Rs,Ss) :- !, 
    position(vble(X):Sx,[F|Args]:Sf,Posn),     % Find position that X occurs at
    remove_occ(Posn,[F|Args]:Sf,Rs1),       % Suggest repair Rs that removes an argument that X occurs in
    merge_sorts(vble(X):Sx,[F|Args]:Sf,Rs2,Ss),              % Merge sorts if they are different
    append(Rs1,Rs2,Rs).                  % Conjoin these repairs

% Case VVf repairs: merge sorts
diagnose(success,fail,vble(X):Sx=vble(Y):Sy,Rs,Ss) :- 
    \+(unifiableSorts(Sx,Sy,Ss)),   %FIXME: check all unifiableSorts functions
    merge_sorts(vble(X):Sx,vble(Y):Sy,Rs,Ss).  


% Suggest repair if failure wanted but success produced. 

% Case CCs repairs: split functors, split sorts or differentiate arities
diagnose(fail,success,[F1|Args1]:S1=[F2|Args2]:S2,Rs,Ss) :- !,
    (split_funcs(F1:S1,F2:S1,Rs);                  % Split functors
    split_sorts(F1:S1,F2:S2,Rs,Ss);                   % Split sorts
    diff_arity([F1|Args1]:S1,[F2|Args2]:S2,Rs)).   % Or differentiate arities

% Case VCs repairs: insert X to induce occurs check failure, or split sorts
diagnose(fail,success,vble(X):Sx=[F|_]:Sf,Rs,Ss) :- 
    Rs = [insert_var(F:Sf,X:Sx)];
    split_sorts(vble(X):Sx,F:Sf,Rs,Ss).  

% Case VVs repairs: disjoin sorts
diagnose(fail,success,vble(X):Sx=vble(Y):Sy,Rs,Ss) :- 
    split_sorts(vble(X):Sx,vble(Y):Sy,Rs,Ss).  


%% merge_funcs(F1,F2): Merge two function names
% Do nothing if already the same.
merge_funcs(F:_,F:_,[]) :- !.                       % No repair if functors are the same

% Rename first to second if different 
merge_funcs(F1:S1,F2:S2,[merge(F1:S1,F2:S2)]) :- 
    F1\==F2.                               % Return repair if functors are different

%% merge_sorts(S1,S2): Merge two sorts
merge_sorts(S1,S2,[],Ss) :- unifiableSorts(S1,S2,Ss), !.
merge_sorts(vble(X):Sx,vble(Y):Sy,Rs,Ss) :- % VV
    relateSorts(vble(X):Sx,vble(Y):Sy,Rs,Ss).

merge_sorts([F|Args]:Sf,Y:Sy,Rs,Ss) :- % VC
    merge_sorts(Y:Sy,[F|Args]:Sf,Rs,Ss).

merge_sorts(X:Sx,[F|Args]:Sf,Rs,Ss) :-
    relateSortsVC(X:Sx,[F|Args]:Sf,Rs,Ss).

merge_sorts(F1:S1,F2:S2,[mergeSorts(F1:S1,F2:S2)],_). % CC

% CONTINUE HERE:
% CC
%merge_sorts(F1:S1,F2:S2,[mergeSorts(F1:S1,F2:S2)],Ss). % In single-sorted logic sorts can match only if sorts are the same sort
%TODO: mergeSorts can happen either by:
% 0. find_descendant_of_both(S1,S2)
% 1. rename(S1,S2)
% 2. rename(S2,S1)
% 3. make_descendant(S1,S2)
% 4. make_descendant(S2,S1)
% but not knowing anything else, best to make it a rename?


%    print('* Rename '), print(F1),        % Debugging print
%    print(' to '), print(F2), nl.

% Rename second to first if different 
% merge_funcs(F1,F2,[merge(F2,F1)]) :-       % Do it the other way around too
%     F1\==F2.          
%   print('* Rename '), print(F2), 
%   print(' to '), print(F1), nl.

%% Make two arities the same
% First find the two arities
same_arity([F1|Args1]:S1,[F2|Args2]:S2,Rs) :- 
    length(Args1,L1), length(Args2,L2),           % Find arities of Fis
    same_arity2(F1:S1,L1,F2:S2,L2,Rs).  % Return repair to make them the same

% Do nothing if arities the same.  Do not back up
same_arity2(_,L,_,L,[]) :- !.  

% Find out which is longer and rearrange to put small first.
same_arity2(F1,L1,F2,L2,Rs) :-
    L1<L2, !, same_arity3(F1,L1,F2,L2,left,Rs).  % if smallest on left do nothing

same_arity2(F1,L1,F2,L2,Rs) :-
    L2<L1, !, same_arity3(F2,L2,F1,L1,right,Rs). % if smallest on right then switch


% Return just one of the possible repairs
same_arity3(F1:S1,L1,F2:S2,L2,Side,Rs) :-
    N is L2-L1,                                            % N is number of args to remove/add
    switch(Side,Other),                                    % Calculate the other side
    disjoin([remove_n(F2:S2,N,Side)],[add_n(F1:S1,N,Other)],Rs). % Either remove N from bigger or add N to smaller

% ([remove_n(F2,N,Side)]=Rs ; [add_n(F1,N,Other)=Rs]). % Either remove N from bigger or add N to smaller



%% remove_occ(Posn,Exp,Rs): remove an occurence of variable X that occurs at Posn from Exp to give repairs Rs

remove_occ([I|_],[F|_]:S,[remove_ith(F:S,I)]).  % Remove the Ith argument of F

remove_occ([I|Rest],[_|Args]:_,Rs) :-   % Recurse on deeper arguments
    I1 is I-1, length(Front,I1),      % Front will be first I-1 args
    append(Front,[Arg|_],Args),       % Arg is the Ith argument
    remove_occ(Rest,Arg,Rs).          % Recurse on Arg

%% split_funcs(F1,F2): split functions if they are the same

% Do nothing if they are already different and do not back up
split_funcs(F1:_,F2:_,[]) :- F1\==F2, !.

% Rename one if they are the same.
split_funcs(F:S,F:S,[rename(F:S)]).           % Return rename one functor
%   :- print('* Rename an occurrence of '), 
%      print(F), nl.

split_sorts(S1,S2,[],Ss) :- \+(unifiableShallow(S1,S2,Ss)), !. % or unground (e.g. s) sorts 
split_sorts(F1:S1,F2:S2,Rs,Ss) :- 
    unifiableShallow(F1:S1,F2:S2,Ss),
    splittableSorts(F1:S1,F2:S2,Ss),
    (disjoinSorts(F1:S1,F2:S2,Ss,Rs);
    splitParentSort(F1:S1,F2:S2,Ss,Rs)).

%% Make two arities different

% First find the two arities
diff_arity([F1|Args1]:S1,[F2|Args2]:S2,Rs) :- 
    length(Args1,L1), length(Args2,L2),           % Discover two arities
    diff_arity2([F1|Args1]:S1,L1,[F2|Args2]:S2,L2,Rs).  % Return differentiating them

% Do nothing if arities are already different and do not back up
diff_arity2([_|_]:_,L1,[_|_]:_,L2,[]) :- L1\==L2, !.

% Change an arity if they are the same
diff_arity2([F|_]:S,L,[F|_]:S,L,[diff_arities(F:S,L)]) :- !. % Generic repair

%    disjoin([add_one(F1)],[add_one(F2)],Rs1),       % Return adding an argument
%    disjoin([remove_one(F1)],[remove_one(F2)],Rs2), % Return removing an argument
%    disjoin(Rs1,Rs2,Rs).                            % Return add or remove

%      ([add_one(F1)]=Rs ;[add_one(F2)]=Rs ;		 % Return adding an argument
%      [remove_one(F1)]=Rs ; [remove_one(F2)]=Rs). % Return removing an argument


%    convert(E1,[F1|Args1]), convert(E2,[F2|Args2]),                  % Convert for pretty print
%    arg_addition(Args1,E1,Rs1), arg_addition(Args2,E2,Rs2),          % Return adding an argument
%    arg_removal(Args1,E1,Rs3), arg_removal(Args2,E2,Rs4),            % Return removing an argument
%    disjoin(Rs1,Rs2,Rs5), disjoin(Rs3,Rs4,Rs6), disjoin(Rs5,Rs6,Rs). % Return just one


%% arg_removal(Args,E,Rs): remove an argument from E if there are any and return repairs Rs

% Do nothing if there are no arguments to remove and do not back up
% arg_removal([],_,[]) :- !.

% Otherwise, remove one
% arg_removal([H|T],E,[remove_one(F)]) :- 
%   convert(E,[F,H|T]).                       % Convert for pretty print
% print('* Remove last argument from '),    % Debugging print
% print(E), nl.


% Add an argument
% arg_addition([H|T],E,[add_one(F)]) :- 
%   convert(E,[F,H|T]).                          % Convert for pretty print
% print('* Add an argument to '), print(E), nl.

