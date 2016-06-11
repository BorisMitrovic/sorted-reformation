%% Reformation Procedure %%
%% Alan Bundy, 16.2.12 %%

%% Representation: variables are vble(X); compound terms are [Func|Args], where
%% Args can be empty list if Func is constant.

%% Unification problems and substitutions are both lists of equations E1=E2. For
%%  substitutions E1 is always vble(X) for some X.


%% reform(E1,E2,Sigma,W,FS,Rs,Ss): unify E1 and E2 with substitution Sigma, sort structure Ss and
%% result FS (fail/success) and what was wanted. Return repairs Rs.

reform(E1,E2,Sigma,W,FS,Rs,Ss) :-              % accept singleton even if not in list format
    \+(is_list(E1)), !,
    reform([E1],E2,Sigma,W,FS,Rs,Ss).

reform(E1,E2,Sigma,W,FS,Rs,Ss) :- 
    \+(is_list(E2)), !,
    reform(E1,[E2],Sigma,W,FS,Rs,Ss).

reform(E1S,E2S,Sigma,W,FS,Rs,Ss) :-
    maplist(convert,E1S,NE1S),              % Convert inputs to internal format
    maplist(convert,E2S,NE2S),
    pairwise(NE1S,NE2S,NE),
    reform2(NE,[],Sigma,W,FS,Rs,Ss).           % Call reformation on internal form

%% reform2(EL,SigmaIn,SigmaOut,W,FS,Rs): Unify expression list EL with input
%% substitution SigmaIn and output SigmaOut, result FS (fail/success) and
%% repairs Rs.


reform3(F1,F2,SigmaIn,SigmaOut,W,FS,Rs,Ss) :-
    pairwise(F1,F2,Ne),
    reform2(Ne,SigmaIn,SigmaOut,W,FS,Rs,Ss).

% Pretty print current state


%DEBUG printout
%reform2(EL,SigmaIn,_,_,_,_,_) :-
%    verbose(on),
%    print('* Problem: '), pprint(EL), nl,
%    print('* Substitution: '), pprint(SigmaIn), nl, nl, fail.


% Base case (wanted failure)
reform2([],SigmaIn,SigmaIn,fail,success,_,(Ss,Ss)) :-    % Fail if failure wanted, but base case is successful
    (refsuccess; assert(refsuccess)),            % Mark successful unification (assert only one fact)
    !, fail.                                     % Failure wanted, but unification succeeds, so fail 

% Base case (wanted success)
reform2([],SigmaIn,SigmaIn,success,success,[],(Ss,Ss)) :-   % When no more problems, succeed with empty substitution
    (refsuccess; assert(refsuccess)),               % Assert only one fact
    !.                                  

% Case CC_s: success on two compound expressions. F1=F2, sorts unifiable and length Arg1 and
% length Arg2 the same.

reform2([[F1|Args1]:S1=[F2|Args2]:S2|Old],SigmaIn,SigmaOut,W,FS,Rs,Ss) :- 
    F1==F2, length(Args1,L), length(Args2,L),       % If functors and arities agree
    S1==S2,                                         % If sorts equal
    pairwise(Args1,Args2,New),                      % Pair up corresponding subterms
    append(New,Old,Rest),                           % Add them to the Old problems
    (reform2(Rest,SigmaIn,SigmaOut,W,FS,Rs,Ss);        % Repair either from recursive part
    refsuccess(FS2),                                % Gets the FS value from the end of recursion
    diagnose(W,FS2,[F1|Args1]:S1=[F2|Args2]:S2,Rs,Ss), % Or repair from diagnosing current unification
    \+(Rs=[])).                                     % Only if diagnosing finds a repair


% Case CC_f: failure on two compound expressions. F1/=F2, S1/=S2, or length Arg1 and
% length Arg2 different.

reform2([[F1|Args1]:S1=[F2|Args2]:S2|_],_,_,_,fail,_,_) :-              
    (F1\==F2 ; S1\=S2; length(Args1,L1), length(Args2,L2), L1\==L2),    % if functors, sorts or arities disagree
    retractall(refsuccess), fail.                                        % mark failure

reform2([[F1|Args1]:S1=[F2|Args2]:S2|_],_,_,fail,fail,_,_) :-              % If failure wanted then fail
    (F1\==F2 ; S1\=S2;  length(Args1,L1), length(Args2,L2), L1\==L2).   % if functors or arities disagree



reform2([[F1|Args1]:S1=[F2|Args2]:S2|Rest],SigmaIn,SigmaOut,success,fail,Rs,(SIn,SOut)) :- % If failure unwanted
    (F1\==F2 ; S1\=S2; length(Args1,L1), length(Args2,L2), L1\==L2), !,        % but functors or arities disagree
    diagnose(success,fail,[F1|Args1]:S1=[F2|Args2]:S2,Rs1,(SIn,SOut)),                     % Diagonose a repair
    repairs(Rs1,[F1|Args1]:S1=[F2|Args2]:S2,U,(SIn,SMid)),                                 % Apply it
    reform2([U|Rest],SigmaIn,SigmaOut,success,_,Rs2,(SMid,SOut)),                           % Continue reformation with repaired problem
    append(Rs1,Rs2,Rs).                                                         % Conjoin first repair with any more found. 

% Case VC: a variable vs a compound expression. 

% Switch expressions if in wrong order
reform2([[F|Args]:Sf=vble(X):Sx|Rest],SigmaIn,SigmaOut,W,FS,Rs,Ss) :- !,   
    reform2([vble(X):Sx=[F|Args]:Sf|Rest],SigmaIn,SigmaOut,W,FS,Rs,Ss).     % Reorient problem to put variable first

% Case VC_f: variable occurs in term E or Sx\=Sf, then fail
reform2([vble(X):Sx=[F|Args]:Sf|_],_,_,fail,fail,_,Ss) :-             % If failure wanted then fail
    (\+(ancestorOrSelf(Sx,Sf,Ss)) ; occurs(vble(X):Sx,[F|Args]:Sf)), !.                       % if var occurs in expression

reform2([vble(X):Sx=[F|Args]:Sf|Rest],SigmaIn,SigmaOut,success,fail,Rs,(SIn,SOut)) :-   % If failure unwanted
    (\+(ancestorOrSelf(Sx,Sf,(SIn,SOut))) ; occurs(vble(X):Sx,[F|Args]:Sf)), retractall(refsuccess), !,         % but var occurs in expression or sorts differ
    diagnose(success,fail,vble(X):Sx=[F|Args]:Sf,Rs1,(SIn,_)),                       % Diagnose a repair
    repairs(Rs1,vble(X):Sx=[F|Args]:Sf,U,(SIn,SMid)),                   % Apply it
    reform2([U|Rest],SigmaIn,SigmaOut,success,_,Rs2,(SMid,SOut)),                        % Continue reformation with repaired problem
    append(Rs1,Rs2,Rs).                                                      % Conjoin first repair with any more found. 

% Case VC_s: variable does not occur in terms and Sx=Sf
reform2([vble(X):Sx=[F|Args]:Sf|Rest],SigmaIn,SigmaOut,W,FS,Rs,Ss) :- 
    \+ occurs(vble(X):Sx,[F|Args]:Sf),                              % If var does not occur in expression
    ancestorOrSelf(Sx,Sf,Ss),                                                 % If sorts are the same
    (W=success,                                               % If unblocking, then permute to ensure minimal repair 
    containsDifferent(vble(X):Sx,[F|Args]:Sf,Rest),           % Check if more than one occurance of the same variable with different instantiation
    reform2(Rest,SigmaIn,SigmaMid,W,FS1,Rs1,Ss),                 % First reform rest
    subst(SigmaMid,[vble(X):Sx=[F|Args]:Sf], NewCurr),        % Apply substitutions obtained
    reform2(NewCurr, SigmaMid, SigmaOut, W, FS2, Rs2,Ss),        % Followed by reforming the current
    and(FS1,FS2,FS),                                          
    append(Rs1,Rs2,Rs),                                       % Append repairs, since unblocking
    \+(Rs=[]);                                                % If no repairs found, don't duplicate
    subst(vble(X):Sx/[F|Args]:Sf,Rest,NewRest),               % Substitute expression for var in problems
    subst(vble(X):Sx/[F|Args]:Sf,SigmaIn,SigmaMid1),          % Substitute expression for var in substitution
    compose(vble(X):Sx/[F|Args]:Sf,SigmaMid1,SigmaMid2),      % Compose new substitution with old one
    (reform2(NewRest,SigmaMid2,SigmaOut,W,FS,Rs,Ss);             % Either recursive repair with new problem and substitution
    refsuccess(FS2),                                          % Gets the FS value from the end of recursion
    diagnose(W,FS2,vble(X):Sx=[F|Args]:Sf,Rs,Ss),                % Or repair from diagnosing current unification
    \+(Rs=[]))).                                               % Only if diagnosing finds a repair


% Case VV: a variable vs a variable

% Case VV=: variables and sorts are already the same
reform2([vble(X):S=vble(X):S|Rest],SigmaIn,SigmaOut,W,FS,Rs,Ss) :-   % If two vars and same then
    reform2(Rest,SigmaIn,SigmaOut,W,FS,Rs,Ss).                       % ignore them and carry on with the rest

% Case VV/=_s: variables are different, sort unifiable
reform2([vble(X):S1=vble(Y):S2|Rest],SigmaIn,SigmaOut,W,FS,Rs,Ss) :-   % If two vars and different then
    commonDescendants(S1,S2,Ss,Ds),
    (X\==Y,!; S1\==S2),                           % some subst needed
    member(D,Ds),                                 % check every possible replacement
    Subst1 = vble(X):S1/vble(Y):D,
    Subst2 = vble(Y):S2/vble(Y):D,
    compose(Subst1,SigmaIn,SigmaMid1),            % Compose new substitution with old one
    compose(Subst2,SigmaMid1,SigmaMid2),        
    subst(SigmaMid2,Rest,NewRest),               % substitute one for the other in the problems
    (reform2(NewRest,SigmaMid2,SigmaOut,W,FS,Rs,Ss); % Recurse with new problem
    refsuccess(FS2),
    diagnose(W,FS2,vble(X):S1=vble(Y):S2,Rs,Ss),
    \+(Rs=[])).                   

% Case VV/=_f: variables are different, sorts ununifiable
reform2([vble(_):Sx=vble(_):Sy|_],_,_,fail,fail,_,Ss) :-       % If failure wanted then fail
    \+(commonDescendants(Sx,Sy,Ss,_)), !.                                             % if sorts different

reform2([vble(X):Sx=vble(Y):Sy|Rest],SigmaIn,SigmaOut,success,fail,Rs,(SIn,SOut)) :-  % success wanted but sorts different
    X\==Y, \+(commonDescendants(Sx,Sy,(SIn,SOut),_)), retractall(refsuccess), !,                             % if sorts and vars different
    subst(vble(X):Sx/vble(Y):Sy,Rest,NewRest),                             % substitute one for the other in the problems
    compose(vble(X):Sx/vble(Y):Sy,SigmaIn,SigmaMid),                       % Compose new substitution with old one  
% TODO: make sure all repairs aer possible, not just renaming
    diagnose(success,fail,vble(X):Sx=vble(Y):Sy,Rs1,(SIn,SOut)),                      % Diagnose a repair
    repairs(Rs1,vble(X):Sx=vble(Y):Sy,U,(SIn,SMid)),                                  % Apply it
    reform2([U|NewRest],SigmaMid,SigmaOut,success,_,Rs,(SMid,SOut)).                     % Recurse with new problem

pat(vble(X):S=vble(Y):S,Z,X,Y) :- Z=S.
