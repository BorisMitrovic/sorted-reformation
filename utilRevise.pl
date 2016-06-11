
% converting clauses using convert
convertClause(In,Out) :-
	maplist(convertTerm,In,Out).

convertTerm(+In,+Out) :-
	convert(In,Out).

convertTerm(-In,-Out) :-
	convert(In,Out).

% all elements of a clause after a term
afterClause(C,[C|AfterOnt],AfterOnt) :-!.
afterClause(C,[_|Ont],AfterOnt) :-
	afterClause(C,Ont,AfterOnt).


% Does the repair make sense for a given clause? Specifies necessary conditions.
sensibleRep([insert_var(_,V:Sv)],Cl) :- !, occurs(V:Sv,Cl).
% TODO: define sensibility for other repairs
sensibleRep(_,_).

oppositeSigns(+L,-R,L,R) :- !.
oppositeSigns(-L,+R,L,R).


% produces a list of integers up to a number in reversed order.
enum(0,[]) :- !.
enum(N,List) :-
	N1 is N-1,
	enum(N1,Rest),
	List = [N|Rest].
	
% remove all occurances of an element from a list
remove(_,[],[]).
remove(A, [A|B], C) :- !,
	remove(A,B,C).
remove(A, [B|R], [B|N]) :-
	remove(A, R, N).

% prints  alist line by line
printAll([]) :- !.
printAll([C|Cs]) :-
	print(C),nl, printAll(Cs).

% gives the resulting clause assuming the resolution was successful.
resultingClause(C1,I1,C2,I2,NewC) :-
	I11 is I1-1, I21 is I2-1,
	append(B1,[_|E1],C1), length(B1,I11),
	append(B2,[_|E2],C2), length(B2,I21),
	append(B1,B2,B),
	append(E1,E2,E),
	append(B,E,NewC), !.


unifiableShallow(X:Sx,Y:Sy,Ss) :- %  transformation if needed
	\+(X=vble(_)),
	\+(X=[_|_]),
	unifiableShallow([X]:Sx,Y:Sy,Ss).

unifiableShallow(X:Sx,Y:Sy,Ss) :- %  transformation if needed
	\+(Y=vble(_)),
	\+(Y=[_|_]),
	unifiableShallow(X:Sx,[Y]:Sy,Ss).

% Does the current unification problem unify, without the recursive steps
unifiableShallow(vble(_):Sx,vble(_):Sy,Ss) :- %  VV
	relatedSorts(Sx,Sy,Ss).

unifiableShallow([F1|Args1]:S1, [F2|Args2]:S2,_) :- %  CC
    F1==F2,
    length(Args1,L), length(Args2,L),      
    S1==S2.  

unifiableShallow([F|Args]:Sf,vble(_):Sy,Ss) :- %  CV
	unifiableShallow(vble(_):Sy,[F|Args]:Sf,Ss). %  VC

unifiableShallow(vble(_):Sy,[_|_]:Sf,Ss) :- %  VC
	descendantOrSelf(Sf,Sy,Ss).

unifiableSorts([F|_]:Sx,[_|_]:Sy,Ss) :-
	unifiableShallow([F]:Sx,[F]:Sy,Ss), !.

unifiableSorts(X:Sx,Y:Sy,Ss) :-
	unifiableShallow(X:Sx,Y:Sy,Ss).

%%% many sorted utils

% checks for descendance
%unifiableSorts(X,X,_) :- !.
%unifiableSorts(sort(X),sort(Y),(Sorts,_)) :- descendant(X,Y,Sorts), !.
%unifiableSorts(sort(X),sort(Y),(Sorts,_)) :- ancestor(X,Y,Sorts), !.


%unifyingSubst(vble(X):sort(S1),vble(Y):sort(S2),vble(X):sort(S1)/vble(Y):sort(S2),(Ss,_)):-
%	ancestor(S1,S2,Ss), !.
%unifyingSubst(vble(X):sort(S1),vble(Y):sort(S2),vble(Y):sort(S2)/vble(X):sort(S1),(Ss,_)):-
%	ancestor(S2,S1,Ss), !.
%unifyingSubst(vble(X):S,vble(Y):S,vble(X):S/vble(Y):S,_):- !.



commonDescendant(sort(X),sort(Y),(Sorts,_),D) :-
	descendantOrSelf(D,X,Sorts),
	descendantOrSelf(D,Y,Sorts).

commonDescendants(sort(X),sort(Y),(Sorts,_),Ds) :-
	allCommonDescendants(X,Y,Sorts,All),
	findMaximalSubset(All,Sorts,Max),
	Max \= [bot],
	maplist(addSortArg,Max,Ds).

allCommonDescendants(X,Y,Sorts,Ds) :-
	setof(D,
		(commonDescendant(sort(X),sort(Y),(Sorts,_),D)),
		Ds).

findMaximalSubset(Ds,Ss,Ds) :-
	\+((member(X,Ds),member(Y,Ds),ancestor(X,Y,Ss))), !.

findMaximalSubset(Ds,Sorts,MinDs) :-
	member(X,Ds),member(Y,Ds),descendant(X,Y,Sorts), !,
	delete(Ds,X,MidDs), 
	findMaximalSubset(MidDs,Sorts,MinDs).

addSortArg(X,sort(X)).

% TODO: only parents of all commonDescendants

relatedSorts(sort(X),sort(Y),(Sorts,_)) :-
	commonDescendants(sort(X),sort(Y),(Sorts,_),_). % cd fails if no Ds

unrelatedSorts(sort(X),sort(Y),(Sorts,_)) :-
	\+(relatedSorts(sort(X),sort(Y),(Sorts,_))).

checkDebug([insert_var(edinburgh,t1)]).

descendant(X,Y,Sorts) :- member((X->Y),Sorts).
descendant(X,Y,Sorts) :- member((X->Z),Sorts), descendant(Z,Y,Sorts).

ancestor(X,Y,Sorts) :- descendant(Y,X,Sorts).

ancestorOrSelf(X,X,_).
ancestorOrSelf(sort(X),sort(Y),(Sorts,_)) :-
	ancestorOrSelf(X,Y,Sorts), !.
ancestorOrSelf(X,Y,Sorts) :- ancestor(X,Y,Sorts).


descendantOrSelf(X,X,_).
descendantOrSelf(sort(X),sort(Y),(Sorts,_)) :-
	descendantOrSelf(X,Y,Sorts),!.
descendantOrSelf(X,Y,Sorts) :- descendant(X,Y,Sorts).



commonAncestor(sort(S1),sort(S2),sort(S3),(Ss,_)) :- 
	setof(Ancestor1,ancestor(Ancestor1,S1,Ss),Ancestors1),
	setof(Ancestor2,ancestor(Ancestor2,S2,Ss),Ancestors2),
	intersection(Ancestors1,Ancestors2,Ancestors),
	findMinimalSubset(Ancestors,Ss,Minimal),
	(Minimal = [S3],!; S3=S1).

findNewParents(X,Y,Sorts,Parents) :- 
	setof(Parent,findNewParent(X,Y,Sorts,Parent),AllParents),
	findMinimalSubset(AllParents,Sorts,Parents).

findMinimalSubset(Parents,Sorts,Parents) :- 
	\+((member(X,Parents),member(Y,Parents),descendant(X,Y,Sorts))), !.

findMinimalSubset(Parents,Sorts,MinParents) :-
	member(X,Parents),member(Y,Parents),ancestor(X,Y,Sorts), !,
	delete(Parents,X,MidParents), 
	findMinimalSubset(MidParents,Sorts,MinParents).

findNewParent(X,Y,Sorts,Parent) :- descendant(X,Parent,Sorts), Parent \= Y, \+(descendant(Parent,Y,Sorts)).

descendantsOf(X,Ss,Ds) :-
	setof(D,descendant(D,X,Ss),Ds).

% Relate Sorts: Make glbs \= []
relateSorts(vble(_):sort(Sx),vble(_):sort(Sy),Rs,_) :-
	Newsort = dummy,
	Rs = [addSort(Newsort->Sx),addSort(Newsort->Sy),addSort(bot->Newsort)].

% Relate sorts: Make Sf subsort Sx
relateSortsVC(_:sort(Sx),[F|Args]:sort(Sf),Rs,_) :-
	gensym(Sf,SfDash),
	Rs = [addSort(SfDash->Sx),addSort(SfDash->Sf),
		addSort(bot->SfDash),renameSorts([F|Args]:sort(Sf),sort(SfDash))].

% Disjoin Sorts: (Make sx \= sy or ¬desc(sx,sy) or glbs = [])
% IS identical sorts


unsplittableSorts(_:sort(top),_,_) :- !.	% nothing can be disjoint from top
unsplittableSorts(_,_:sort(top),_) :- !.

unsplittableSorts(_:sort(bot),_,_) :- !.	% nothing can be disjoint from bot
unsplittableSorts(_,_:sort(bot),_) :- !.

splittableSorts(A,B,_) :- \+(unsplittableSorts(A,B,_)).

disjoinSorts(X,Y,S,R) :- disjoinSorts2(X,Y,S,R); X\=Y, disjoinSorts2(Y,X,S,R).

disjoinSorts2(X:sort(Sx),_:sort(Sx),(Ss,_),Rs) :-
	gensym(Sx,SxDash),
	R1 = [renameSorts(X:sort(Sx),sort(SxDash)),addSort(bot->SxDash)],
	setof(addSort(SxDash->Par),member(Sx->Par,Ss),R2),
	append(R1,R2,Rs).

% SS one subsort of another
disjoinSorts2(X:sort(Sx),vble(_):sort(Sy),(Ss,_),Rs) :- 
	Sx \= Sy,
	descendant(Sx,Sy,Ss),
	gensym(Sx,SxDash),
	findNewParents(Sx,Sy,Ss,Parents),
	findall(addSort(SxDash->E),member(E,Parents),Rr),
	Rs =[renameSorts(X:sort(Sx),sort(SxDash))|[addSort(bot->SxDash)|Rr]].


% CS common descendant, only applies to VV case
disjoinSorts2(vble(X):sort(Sx),vble(_):sort(Sy),(Ss,_),Rs) :- 
	Sx \= Sy,
	\+(descendant(Sx,Sy,Ss)),
	\+(descendant(Sy,Sx,Ss)),
	gensym(Sx,SxDash),
	descendantsOf(Sx,Ss,Dx),
	allCommonDescendants(Sx,Sy,Ss,Cs),
	findall(addSort(D->SxDash),
		(member(D,Dx), \+((member(C,Cs),descendantOrSelf(C,D,Ss)))),
		R1),
	findall(delSort(D->Sx),
		(member(D,Dx), \+((member(C,Cs),descendantOrSelf(C,D,Ss)))),
		R2),
	append([addSort(SxDash->Sx)|R1],R2,R3),
	Rr = [renameSorts(vble(X):sort(Sx),sort(SxDash))|R3],
	(R1==[],Rs=[addSort(bot->SxDash)|Rr],!;
	Rs = Rr).





blockSorts(F:sort(X),_:sort(Y),(SIn,_),[renameSorts(F:sort(X),sort(Xdash))|[addSort(bot->Xdash)|Rs]]) :- 
	descendant(X,Y,SIn), !,
	findNewParents(X,Y,SIn,Parents),
	gensym(X,Xdash),
	findall(addSort(Xdash->E),member(E,Parents),Rs).


blockSorts(F1:sort(X),_:sort(X),(SIn,_),[renameSorts(F1:sort(X),sort(Xdash))|[addSort(bot->Xdash)|Rs]]) :- !,
	gensym(X,Xdash),
	findall(addSort(Xdash->Y),(member(X->Y,SIn),\+(member(Xdash->Y,SIn))),Rs).

blockSorts(X,Y,Ss,Rs) :- !, X\=Y, blockSorts(Y,X,Ss,Rs).


findToSplit(X,Y,Sorts,Betweens) :- setof(Z,(member(Z->Y,Sorts), ancestorOrSelf(Z,X,Sorts)),Betweens).


% splitting the sorts as in IBIS paper.
splitParentSort(F:sort(X),_:sort(Y),(Sorts,_),Repairs) :- 
	descendantOrSelf(X,Y,Sorts),
	findToSplit(X,Y,Sorts,Splits),
	findall( Reps,
	(
		member(Z,Splits),
		findToSplit(X,Z,Sorts,Children),
		member(C,Children),
		member(C->Z,Sorts),
		gensym(Z,Zn),
		findall(delSort(Z->P), (member(Z->P,Sorts),P\=Y),Reps2),
		Reps1 = [delSort(C->Z), addSort(C->Zn), addSort(Z->Zn)],
		append(Reps1,Reps2,RepsT),
		(	member(O->Z,Sorts),\+(member(O,Children)), Reps=RepsT,!;
			[addSort((bot->Z))|RepsT] = Reps	)
	),		
		RepairsLoL1),

	flatten(RepairsLoL1,RepairsList1),
	sort(RepairsList1,Repairs1),
	findall(Py, (member(Y->Py,Sorts)),ParentsY),

	retractall(topRepair),
	findall( Reps,
	(
		member(Z,Splits),
		gensym(Z,Zn),
		findall(P, (member(Z->P,Sorts),P\=Y),ParentsZ),
		append(ParentsY,ParentsZ,Parents),
		findMinimalSubset(Parents,Sorts,MinimalParents),
		\+((MinimalParents ==[], assert(topRepair))), 		% fail if splitting the top sort is needed
		member(Parent,MinimalParents),
		(member(Z->Parent,Sorts),Reps = [addSort(Zn->Parent), delSort(Z->Parent)], !;
		Reps = [addSort(Zn->Parent)])
	),
	RepairsLoL2),
	\+(retract(topRepair)),
	retractall(topRepair),

	flatten(RepairsLoL2,RepairsList2),
	sort(RepairsList2,Repairs2),
	append(Repairs1, Repairs2, RepairsAll),
	sort(RepairsAll,RepairsSorts),
	gensym(X,Xn),
	(member(addSort(X->Xn),RepairsSorts), !, Repairs=[renameSorts(F:sort(X),sort(Xn))|RepairsSorts];
	Repairs=RepairsSorts).


% testSorts(Ss),splitParentSort(sort(beetle),sort(flying),Ss,Rs).
splitParentSort(F:sort(X),G:sort(Y),(Sorts,_),Repairs) :- ancestor(X,Y,Sorts), 
	splitParentSort(G:sort(Y),F:sort(X),(Sorts,_),Repairs).



applyRepsSorts([],(S,S)).
applyRepsSorts([H|T],(SIn,SOut)) :-
	applyRepSorts(H,(SIn,SMid)), 
	applyRepsSorts(T,(SMid,SOut)).


:- dynamic heuristic/1.
heuristic("iter").

setHeuristic(H) :- retractall(heuristic(_)),assert(heuristic(H)).