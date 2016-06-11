%% Apply repairs to Unification Problems %%
%% Alan Bundy, 23.2.12 %%


%% repairs(Rs,UIn,UOut): apply repairs Rs to unification problem UIn to get repaired unification problem UOut.

% Base case: if no repairs do nothing. 
repairs([],U,U,(Ss,Ss)).

% Step case: apply each repair in turn.
repairs([H|T],UIn,UOut,(SIn,SOut)) :-
    repair(H,UIn,UMid,(SIn,SMid)), repairs(T,UMid,UOut,(SMid,SOut)).              % repair does one repair to the head, then recurse on the tail. 

%%  repair(R,UIn,UOut): apply one repair.

% merge two functors
repair(merge(F1:S1,F2:_),[F1|Args]:S1=RHS,[F2|Args]:S1=RHS,_) :- !. % merge functors can happen in 4 ways.
repair(merge(F1,F2),LHS=[F1|Args]:S,LHS=[F2|Args]:S,(Ss,Ss)).
repair(merge(F1,F2),[F2|Args]:S=RHS,[F1|Args]:S=RHS,(Ss,Ss)). 
repair(merge(F1,F2),LHS=[F2|Args]:S,LHS=[F1|Args]:S,(Ss,Ss)).

% merge two sorts
%repair(mergeSorts(_:S1,_:S2),LHS:S1=RHS,LHS:S2=RHS,(Ss,Ss)) :- !.      % merge sorts can happen in 4 ways.
%repair(mergeSorts(_:S1,_:S2),LHS=RHS:S1,LHS=RHS:S2,(Ss,Ss)) :- !.
%repair(mergeSorts(S1,S2),LHS:S2=RHS,LHS:S1=RHS,(Ss,Ss)). 
%repair(mergeSorts(S1,S2),LHS=RHS:S2,LHS=RHS:S1,(Ss,Ss)).


repair(addSort(X->X),_,_,_) :- !, fail. 

repair(addSort(Xdash->E),U,U,(SIn,SIn)) :- 
  member(Xdash->E,SIn), !.

repair(addSort(Xdash->E),U,U,(SIn,[Xdash->E|SIn])) :-  
  \+(member(Xdash->E,SIn)), !.

repair(delSort(Xdash->E),U,U,(SIn,SIn)) :- 
  \+(member(Xdash->E,SIn)), !.

repair(delSort(Xdash->E),U,U,(SIn,SOut)) :-   
  member(Xdash->E,SIn), 
  remove((Xdash->E),SIn,SOut),!.


% merge two sorts
repair(mergeSorts(_:S1,_:S2),LHS:S1=RHS:S2,LHS:S3=RHS:S3,(Ss,Ss)) :- !,
  commonAncestor(S1,S2,S3,(Ss,_)).

% remove (last) n arguments
repair(remove_n(F,N,left),LHS=[F|Args]:S,LHS=[F|ArgsN]:S,(Ss,Ss)) :- !,
    length(Snip,N), append(ArgsN,Snip,Args).                 % use length and append backwards to find first N args of Args
%   print('* Removed arguments from '), print(LHS=[F|Args]), % debugging print
%   print(' to get '), print(LHS=[F|ArgsN]), nl. 

repair(remove_n(F,N,right),[F|Args]:S=RHS,[F|ArgsN]:S=RHS,(Ss,Ss)) :- !,
    length(Snip,N), append(ArgsN,Snip,Args).                 % use length and append backwards to find first N args of Args
%   print('* Removed arguments from '), print(LHS=[F|Args]), % debugging print
%   print(' to get '), print(LHS=[F|ArgsN]), nl. 

% add (last) n arguments
repair(add_n(F1,N,right),[F1|Args1]:S1=[F2|Args2]:S2,[F1|Args1N]:S1=[F2|Args2]:S2,(Ss,Ss)) :- !,
       length(Add,N), append(_,Add,Args2),                             % Use length and append backwards to find, Add, the args to add
       append(Args1,Add,Args1N).                                       % Instantiate Add to extra args on the RHS
%      print('* Added arguments to '), print([F1|Args1]=[F2|Args2]),   % debugging print
%      print(' to get '), print([F1|Args1N]=[F2|Args2]), nl. 

% add (last) n arguments
repair(add_n(F1,N,left),[F1|Args1]:S1=[F2|Args2]:S2,[F1|Args1]:S1=[F2|Args2N]:S2,(Ss,Ss)) :- !,
       length(Add,N), append(_,Add,Args1),                             % Use length and append backwards to find, Add, the args to add
       append(Args2,Add,Args2N).                                       % Instantiate Add to extra args on the RHS
%      print('* Added arguments to '), print([F1|Args1]=[F2|Args2]),   % debugging print
%      print(' to get '), print([F1|Args1]=[F2|Args2N]), nl. 


% Make arities different
repair(diff_arities(FL,FR),[FL|ArgsL]:S1=[FR|ArgsR]:S2,[FL|ArgsL1]:S1=[FR|ArgsR]:S2,(Ss,Ss)) :-
	append(ArgsL1,[_],ArgsL).	                       % Use append backwards to remove last LHS arg.

repair(diff_arities(FL,FR),[FL|ArgsL]:S1=[FR|ArgsR]:S2,[FL|ArgsL]:S1=[FR|ArgsR1]:S2,(Ss,Ss)) :-
	append(ArgsR1,[_],ArgsR).	                       % Use append backwards to remove last RHS arg.

repair(diff_arities(FL,FR),[FL|ArgsL]:S1=[FR|ArgsR]:S2,[FL|ArgsL1]:S1=[FR|ArgsR]:S2,(Ss,Ss)) :-
	append(ArgsL,[dummy],ArgsL1).	                   % Append extra arg onto original LHS

repair(diff_arities(FL,FR),[FL|ArgsL]:S1=[FR|ArgsR]:S2,[FL|ArgsL]:S1=[FR|ArgsR1]:S2,(Ss,Ss)) :-
	append(ArgsR,[dummy],ArgsR1).	                   % Append extra arg onto original RHS


% remove last argument
 repair(remove_one(F),[F|Args]=RHS,[F|Args1]=RHS,(Ss,Ss)) :- 
    append(Args1,[_],Args).                                           % Use append backwards to remove last arg.
%   print('* Removed argument from '), print([F|Args]=RHS),            % debugging print
%   print(' to get '), print([F|Args1]=RHS), nl. 
% 
 repair(remove_one(F),LHS=[F|Args],LHS=[F|Args1],(Ss,Ss)) :- !,       % Same as previous clause but on RHS
   append(Args1,[_],Args).                                  
%   print('* Removed argument from '), print(LHS=[F|Args]),
%   print(' to get '), print(LHS=[F|Args1]), nl. 

% add argument to end
% repair(add_one(F),[F|Args]=RHS,[F|Args1]=RHS) :-             
%      append(Args,[dummy],Args1).                           % Append extra arg onto original
%      print('* Added argument to '), print([F|Args]=RHS),   % debugging print
%      print(' to get '), print([F|Args1]=RHS), nl. 

%repair(add_one(F),LHS=[F|Args],LHS=[F|Args1]) :- !,      % Same as previous clause but on LHS   
 %       append(Args,[dummy],Args1). 
 %     print('* Added argument to '), print(LHS=[F|Args]),
 %     print(' to get '), print(LHS=[F|Args1]), nl. 


% rename F
repair(rename(F),[F|Args]:S=RHS,[F1|Args]:S=RHS,(Ss,Ss)) :-
    gensym(F,F1).                                        % Extend F string with dash to form F1

repair(rename(F),LHS=[F|Args]:S,LHS=[F1|Args]:S,(Ss,Ss)) :- !,   % Same as previous clause but on LHS  
    gensym(F,F1).

% renameSorts S
repair(renameSorts(F:sort(S),sort(S1)),F:sort(S)=RHS,F:sort(S1)=RHS,(Ss,Ss)) :-
    gensym(S,S1).                                       % Extend F string with dash to form F1

repair(renameSorts(F:sort(S),sort(S1)),LHS=F:sort(S),LHS=F:sort(S1),(Ss,Ss)) :- !,       % Same as previous clause but on LHS  
    gensym(S,S1).


% remove ith argument
repair(remove_ith(F:Sf,I),vble(X):Sx=E,vble(X):Sx=EI,(Ss,Ss)) :- !,
%   print('* Removing '), print(I), print(' argument from '),    % debugging print
%   print(F), print(' in '), print(vble(X)=E), nl,
    position([F|Args]:Sf,E,P),                                      % Find position of [F|Args] in E
    I1 is I-1, length(Front,I1),                                 % Use length backwards to find Front I-1 args
    append(Front,[_|Back],Args),                                 % and append to find Back I+1 to N args
    append(Front,Back,ArgsI),                                    % Append Front to Back thus snipping out Ith arg
    replace(P,E,[F|ArgsI]:Sx,EI).                                % Replace old subterm with new at position P to get EI
%   print('    with result '), print(vble(X)=EI), nl.            % debugging print

% add X as additional argument to F
repair(insert_var(F,X),vble(X):Sx=[F|Args]:Sf,vble(X):Sx=[F|ArgsX]:Sf,(Ss,Ss)) :- !,
    append(Args,[X],ArgsX).                                      % Append X onto end of Args to get ArgsX


% Error if we cannot deal with repair. 
repair(R,U,_,_) :- !, print('** Unable to handle repair **'), print(R), print(' on '), print(U), nl, nl, fail.




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%     ONTOLOGY   REPAIR       %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



% for ontology repair
% Base case: if no repairs do nothing. 
repairs([],0,U,U,(S,S)).

% Step case: apply each repair in turn.
repairs([H|T],NRepsOut,UIn,UOut,(SIn,SOut)) :-
    repair(H,NRepsCur,UIn,UMid,(SIn,SMid)), repairs(T,NRepsRec,UMid,UOut,(SMid,SOut)),
    NRepsOut is NRepsCur + NRepsRec.  


repair(rename(F:S),Nreps,[F|Args]:S,[F1|Args1]:S,(Ss,Ss)) :- !,
    gensym(F,F1), countReps(rename(F:S),NrepsRest,Args,Args1,(Ss,Ss)),
    Nreps is NrepsRest + 1.

repair(rename(X:Sx),Nreps,[F|Args]:Sf,[F|Args1]:Sf,(Ss,Ss)) :-
    (X\=F; Sx\=Sf), !, countReps(rename(X:Sx),Nreps,Args,Args1,(Ss,Ss)).

%in SSL
%repair(renameSorts(F:sort(S)),Nreps,[F|Args]:sort(S),[F|Args1]:sort(S1),Ss) :- !,
%    gensym(S,S1), countReps(renameSorts(F:sort(S)),NrepsRest,Args,Args1,Ss),
%    Nreps is NrepsRest + 1.

%repair(renameSorts(X:S),Nreps,[F|Args]:S2,[F|Args1]:S2,Ss) :-
%    (X\=F;S\=S2), !, countReps(renameSorts(X:S),Nreps,Args,Args1,Ss).

repair(renameSorts(F:sort(S),sort(S1)),Nreps,[F|Args]:sort(S),[F|Args1]:sort(S1),(Ss,Ss)) :- !,
    gensym(S,S1), countReps(renameSorts(F:sort(S),sort(S1)),NrepsRest,Args,Args1,(Ss,Ss)),
    Nreps is NrepsRest + 1.

repair(renameSorts(X:S,S1),Nreps,[F|Args]:S2,[F|Args1]:S2,(Ss,Ss)) :-
    (X\=F;S\=S2), !, countReps(renameSorts(X:S,S1),Nreps,Args,Args1,(Ss,Ss)).

% repair(split_sorts(F:S1),Nreps,)

repair(addSort(X->X),_,_,_,_) :- !, fail. 

repair(addSort(Xdash->E),0,U,U,(SIn,SIn)) :- 
  member(Xdash->E,SIn), !.

repair(addSort(Xdash->E),0,U,U,(SIn,[Xdash->E|SIn])) :-   % TODO - dirty fix -> should be 1
  \+(member(Xdash->E,SIn)), !.

repair(delSort(Xdash->E),0,U,U,(SIn,SIn)) :- 
  \+(member(Xdash->E,SIn)), !.

repair(delSort(Xdash->E),1,U,U,(SIn,SOut)) :-   % TODO - dirty fix -> should be 1
  member(Xdash->E,SIn), 
  remove((Xdash->E),SIn,SOut),!.


repair(diff_arities((\=):_,(\=):_),0,F,F,(Ss,Ss)) :- !.

%repair(diff_arities(F,F),Nreps,[F|Args]:S,[F|Args2]:S) :-    % removing an argument
%    append(Args1,[_],Args), countReps(diff_arities(F,F),NrepsRest,Args1,Args2),
%    Nreps is NrepsRest + 1.

repair(diff_arities(F:Sf,L),Nreps,[X|Args]:S,[X|Args2]:S,(Ss,Ss)) :-     % do nothing if different
    length(Args,La),(F\=X;Sf\=S;L\=La), !, countReps(diff_arities(F:Sf,L),Nreps,Args,Args2,(Ss,Ss)).

repair(diff_arities(F:S,L),Nreps,[F|Args]:S,[F|Args2]:S,(Ss,Ss)) :- !,  % adding a dummy argument
    length(Args,L),countReps(diff_arities(F:S,L),NrepsRest,Args,Args1,(Ss,Ss)), append(Args1,[[dummy]:sort(s)],Args2), 
    Nreps is NrepsRest + 1.

repair(insert_var(F:Sf,X:Sx),Nreps,[F|Args]:Sf,[F|Args2]:Sf,(Ss,Ss)) :- !,
    countReps(insert_var(F:Sf,X:Sx),NrepsRest,Args,Args1,(Ss,Ss)), append(Args1,[vble(X):Sx],Args2), 
    Nreps is NrepsRest + 1.


repair(insert_var(F:Sf,X:Sx),Nreps,[F2|Args]:S,[F2|Args2]:S,(Ss,Ss)) :-
    (F\=F2;Sf\=S), !, countReps(insert_var(F:Sf,X:Sx),Nreps,Args,Args2,(Ss,Ss)).


% merge two functors
repair(merge(F1:S1,F2:S1),Nreps,[F1|Args]:S1,[F2|Args1]:S1,(Ss,Ss)) :- !,
  countReps(merge(F1:S1,F2:S1),NrepsRest,Args,Args1,(Ss,Ss)),
    Nreps is NrepsRest + 1.

% do nothing if different
repair(merge(F1:S1,F2:S1),Nreps,[F|Args]:S2,[F|Args1]:S2,(Ss,Ss)) :- !,
  countReps(merge(F1:S1,F2:S1),Nreps,Args,Args1,(Ss,Ss)).

% merge two sorts
repair(mergeSorts(F1:S1,F2:S2),Nreps,[F|Args]:S1,[F|Args1]:S3,(Ss,Ss)) :- !,
  commonAncestor(S1,S2,S3,(Ss,_)),
  countReps(mergeSorts(F1:S1,F2:S2),NrepsRest,Args,Args1,(Ss,Ss)),
    Nreps is NrepsRest + 1.

repair(mergeSorts(F1:S1,F2:S2),Nreps,[F|Args]:S2,[F|Args1]:S3,(Ss,Ss)) :- !,
  commonAncestor(S1,S2,S3,(Ss,_)),
  countReps(mergeSorts(F1:S1,F2:S2),NrepsRest,Args,Args1,(Ss,Ss)),
    Nreps is NrepsRest + 1.

% do nothing if different
repair(mergeSorts(F1:S1,F2:S2),Nreps,[F|Args]:S3,[F|Args1]:S3,(Ss,Ss)) :- !,
  S3 \= S2, S3 \=S1,
  countReps(mergeSorts(F1:S1,F2:S2),Nreps,Args,Args1,(Ss,Ss)).


repair(R,Nreps,V:S,NV:NS,Ss) :- !,
  \+(is_list(V)),
  repair(R,Nreps,[V]:S,[NV]:NS,Ss).  

repair(R,Nreps,+(UI),+(UO),Ss) :- !,
  repair(R,Nreps,UI,UO,Ss).

repair(R,Nreps,-(UI),-(UO),Ss) :- !,
  repair(R,Nreps,UI,UO,Ss).

% Error if we cannot deal with repair. 
repair(R,_,U,_,_) :- !, print('** Unable to handle ontology repair **'),
    print(R), print(' on '), print(U), nl, nl, fail.



countReps(_,0,[],[],_).
countReps(Repair,Nreps,[H|Arg],[NewH|NewArg],Ss) :-
  repair(Repair,NrepsCur,H,NewH,Ss),
  countReps(Repair,NrepsRec,Arg,NewArg,Ss),
  Nreps is NrepsCur + NrepsRec.