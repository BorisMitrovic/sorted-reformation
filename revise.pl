% Revises the ontology if inconsistent, until consistency is reached.


initOntology(Ontology,Sorts) :-
	findall((CCl,[]),(fact(Cl),convertClause(Cl,CCl)),Ontology),
	factSorts(Sorts).

% each clause in ontology contains parent clauses which inferred it:
% 		(clause,(leftPar,indexTermLeft,rightPar,indexTermRight))
% for initial clauses parents are []:
%		(clause,[])

revise :- retractall(found),revise(1).

% revise using forward inference until no more inference possible. 
% Repair the ontology if inconsistent and repeat.
% Find a cheapest (minimal edit distance) repair, which makes the ontology consistent.
revise(N) :- 
	initOntology(Ontology,SIn),
	setof(((Nf,Nt),(Repairs,Revised,SOut,N)),
		(revise2(Ontology,Revised,[],_,[],Repairs,N,(SIn,SOut)),
		costRepairs(Repairs,M), 
		M =< N, assert(found),
		length(Revised,Nt),Nf=0),
		FullRepairs),
	quicksort(FullRepairs,RepairsSorted),
	eliminateDuplicates(RepairsSorted,SetOfRepairs),
	member(RepairSorted,SetOfRepairs),
	RepairSorted = ((Nf,Nt),(Repairs,Revised,SOut,N)),

	findall(C,member((C,[]),Revised),Cs),
	length(Cs,Nr), Ni is Nt-Nr,
	nl, print('Minimal cost of repairs: '),print(N),
	print('  Number of inferences: '), print(Ni),
	nl, print('Repairs: '),nl,
	printAll(Repairs),nl,
	print('Revised Ontology: '),nl,
	vnl,vnl,  printAll(Cs), vnl,
	print('Revised Sorts Hierarchy:'),nl,
	printAll(SOut).

revise(N) :- \+(found), N1 is N+1, revise(N1).
revise(_) :- retract(found),fail.

eliminateDuplicates(Reps,Set) :-
	findall( ((Nf,Nt),(RepairsS,RevisedS,SOutS,N)), 
		(
		member(Rep,Reps),
		Rep = ((Nf,Nt),(Repairs,Revised,SOut,N)),
		sort(SOut,SOutS),
		sort(Repairs,RepairsS),
		sort(Revised,RevisedS)
		), All),
	removeDups(All,Set).

removeDups([],[]) :- !.
removeDups([A|R],T) :- member(A,R), !, removeDups(R,T).
removeDups([A|R],[A|T]) :- \+(member(A,R)), removeDups(R,T).


% new inference, add to ontology, or new inconsistency, add to Proofs of contradiction
revise2(OldOnt,NewOnt,ProofsIn,ProofsOut,RsIn,RsOut,N,(SIn,SOut)) :-
	costRepairs(RsIn,M),
	M=<N,
	member((C1,P1),OldOnt),
	afterClause((C1,P1),OldOnt,AfterOnt),
	member((C2,P2),AfterOnt),
	length(C1,L1), enum(L1,LS1), member(I1,LS1),
	length(C2,L2), enum(L2,LS2), member(I2,LS2),
	resolve( (C1,P1),I1,(C2,P2),I2,[],_,(NewC,ParC), (SIn,_) ),
	(	contradiction(NewC,(SIn,_)), 
		\+(member((NewC,ParC),ProofsIn)), !,					% new inconsistency is inferred 	
		vnl,vprint('New Contradiction: '), vprint(NewC),
		revise2(OldOnt,NewOnt,[(NewC,ParC)|ProofsIn],ProofsOut,RsIn,RsOut,N,(SIn,SOut))
	;
		\+(contradiction(NewC,(SIn,_))),
		\+(trivialInference(NewC,OldOnt,(SIn,_))), !,
		vnl,vprint('New Inference: '), vprint(NewC),
		revise2([(NewC,ParC)|OldOnt],NewOnt,ProofsIn,ProofsOut,RsIn,RsOut,N,(SIn,SOut))
	).

% no more inference possible and no inconsistencies found
revise2(Ont,Ont,[],[],Rs,Rs,_,(Sorts,Sorts)) :- !,
	vnl,vprint('Consistent Ontology').

% repair inconsistencies
revise2(OldOnt,NewOnt,ProofsIn,ProofsOut,RsIn,RsOut,N,(SIn,SOut)) :-
	costRepairs(RsIn,M),
	M=<N,
	detect(ProofsIn,Repairs,(SIn,_)),		% find all repairs, which would unblock one of the inconsistency proofs
	heuristic(H),
	chooseRepair(Repair,Repairs,H,OldOnt,SIn),
	repairOnt(OldOnt,RepOnt,Repair,(SIn,SMid)),	% apply the repair to the ontology

	RsMid = [Repair|RsIn],
	vnl,vprint('Repair applied: '), vprint(Repair),
	revise2(RepOnt,NewOnt,[],ProofsOut,RsMid,RsOut,N,(SMid,SOut)).

orderRepairs(Repairs,Ordered,OldOnt,SIn) :- findall(((Nf,Nt),Repair), (
		member(Repair,Repairs),
		repairOnt(OldOnt,RepOnt,Repair,(SIn,SMid)),
		nInconsistencies(RepOnt,SMid,Nf,Nt)
	), Pairs),
	quicksort(Pairs,Ordered).		% select maximal number of nInferences

chooseRepair(Repair,Repairs,"iter",Ont,Ss) :- 
	orderRepairs(Repairs,Ordered,Ont,Ss), 
	member((_,Repair),Ordered).

chooseRepair(Repair,Repairs,"best",Ont,Ss) :- 
	orderRepairs(Repairs,[(_,Repair)|_],Ont,Ss), !. % ,print(Ntf),nl


bestRepair(Repair,Repairs,OldOnt,SIn) :- 
	member(Repair,Repairs),
	repairOnt(OldOnt,RepOnt,Repair,(SIn,SMid)),
	nInconsistencies(RepOnt,SMid,N),
	\+((member(R,Repairs),
		repairOnt(OldOnt,ROnt,R,(SIn,SMid)),
		nInconsistencies(ROnt,SMid,M),
		M < N )), 
	!.

% number inconsistencies and number inferences
nInconsistencies(Ont,SIn,Nf,Nt) :- nInconsistencies2(Ont,[],Incons,SIn), length(Incons,Nf), length(Ont,Nt).
nInconsistencies2(Ont,ProofsIn,ProofsOut,SIn) :-
	member((C1,P1),Ont),
	afterClause((C1,P1),Ont,AfterOnt),
	member((C2,P2),AfterOnt),
	length(C1,L1), enum(L1,LS1), member(I1,LS1),
	length(C2,L2), enum(L2,LS2), member(I2,LS2),
	resolve( (C1,P1),I1,(C2,P2),I2,[],_,(NewC,ParC), (SIn,_) ),
	(	contradiction(NewC,(SIn,_)), 
		\+(member((NewC,ParC),ProofsIn)), !,					% new inconsistency is inferred 	
%		vnl,vprint('New Contradiction: '), vprint(NewC),
		nInconsistencies2(Ont,[(NewC,ParC)|ProofsIn],ProofsOut,SIn)
	;
		\+(contradiction(NewC,(SIn,_))),
		\+(trivialInference(NewC,Ont,(SIn,_))), !,
%		vnl,vprint('New Inference: '), vprint(NewC),
		nInconsistencies2([(NewC,ParC)|Ont],ProofsIn,ProofsOut,SIn)
	).

% no more inference possible and no inconsistencies found
nInconsistencies2(_,Proofs,Proofs,_) :- !.
%	vnl,vprint('Inferred Ontology').


% if a name was already split, then additional splits to the same name are free
costRepairs([],0) :- !.
costRepairs([R|Rs],C) :- costRepair(R,Rs,C1), costRepairs(Rs,C2), C is C1 + C2.

costRepair((R,_),Rs,0) :- member((R,_),Rs), !.
costRepair((addSort(_),_),_,0) :- !.
costRepair(([mergeSorts(_:Sx,_:Sy)],_),Rs,0) :- 
	member(([mergeSorts(_:Sx,_:Sy)],_),Rs); 
	member(([mergeSorts(_:Sy,_:Sx)],_),Rs).
costRepair(([renameSorts(_:Sx,Sy)|_],_),Rs,0) :-  
	member(([renameSorts(_:Sx,Sy)|_],_),Rs).
costRepair(_,_,1).

sortsPure([]).
sortsPure([addSort(_)|T]) :- sortsPure(T).
sortsPure([delSort(_)|T]) :- sortsPure(T). 

% detect all possible repairs to block any of the contradiction proofs
detect(Proofs,Repairs,(SIn,_)) :- 
	setof((Rs,Cl,I), Proof^
		(member(Proof,Proofs),			% use any suggested repair from any proof tree
		detect1(Proof,Rs,(SIn,_)),
		detect2(Proof,(Rs,Cl,I)),
		detect3((Rs,Cl,I),(SIn,_)))
	,Repairs).		

% detects possible repairs
detect1([],_,_) :- !, fail.

% detects false equality contradiction repairs
detect1(([+([==|[X,Y]]:_)],Par), Rs, (SIn,_)) :- 
	X\=Y, reform3([X],[Y],[],_,success,fail,Rs,(SIn,_));
	!, detect1(Par,Rs,(SIn,_)).

% detects false inequality contradiction repairs
detect1(([-([==|[X,X]]:_)],Par), Rs, (SIn,_)) :- 
	reform3([X],[X],[],_,fail,success,Rs,(SIn,_));
	!, detect1(Par,Rs,(SIn,_)).

% empty clause contradiction, only parent repairs 
detect1(([],Par), Rs,(SIn,_)) :- 
	!, detect1(Par,Rs,(SIn,_)).

% repairs given parent resolution
detect1(((C1,_),I1,(C2,_),I2),Rs,(SIn,_)) :-
	nth1(I1,C1,T1),
	nth1(I2,C2,T2),
	oppositeSigns(T1,T2,R1,R2),
	reform3([R1],[R2],[],_,fail,_,Rs,(SIn,_)).

% repairs given ancestor resolution (not parent)
detect1(((_,Par1),_,(_,Par2),_),Rs,(SIn,_)) :-		% or repairs higher up the tree
	detect1(Par1,Rs,(SIn,_));
	detect1(Par2,Rs,(SIn,_)).

% find where repairs apply recursively on the proof tree

detect2((Ref,((Cl1,_),I1,(Cl2,_),I2)),(Rs,Cl,I)) :-
	Ref \= [],						% refutation by equality

	(Cl1=[_], I is 3-I2, Cl = Cl2,(sortsPure(Rs),!;  true);	% the resulting term had to be contradiction
	 Cl2=[_], I is 3-I1, Cl = Cl1,(sortsPure(Rs),!;  true) ).


detect2((_,((Cl1,Par1),I1,(Cl2,Par2),I2)),(Rs,Cl,I)) :-
detect2( ((Cl1,Par1),I1,(Cl2,Par2),I2),(Rs,Cl,I)).

detect2(((Cl1,Par1),I1,(Cl2,Par2),I2),(Rs,Cl,I)) :-
	(Par1=[],
	I = I1,
	Cl = Cl1),
	(sortsPure(Rs),!;  true);
	(Par2=[],
	I=I2,
	Cl=Cl2),
	(sortsPure(Rs),!;  true);
	detect2(Par1,(Rs,Cl,I));
	detect2(Par2,(Rs,Cl,I)).

detect3((Rs,Cl,I),(SIn,_)) :-
	nth1(I,Cl,T),
	repairs(Rs,NReps,T,_,(SIn,_)),		% count repairs applicable
	sensibleRep(Rs,Cl),
	NReps \= 0.					% some repairs can be applied



% apply the repair to the clause in the ontology
repairOnt(OldOnt,RepOnt,(Rs,RepCl,I),(SIn,SOut)) :-
	nth1(I,RepCl,TIn),
	findall((Cl,[]),member((Cl,[]),OldOnt),LeafOnt),
	remove((RepCl,[]),LeafOnt,OntR),	
	repairs(Rs,_,TIn,TOut,(SIn,SOut)),	
	I1 is I-1,
	append(B,[_|E],RepCl), length(B,I1),
	append(B,[TOut|E],ClOut), !,
	RepOnt = [(ClOut,[])|OntR].

% resolution of I1th term of C1 and I2th term of C2 using reformation algorithm
resolve( (C1,P1),I1,(C2,P2),I2,SubstIn,SubstOut,(NewC,((C1,P1),I1,(C2,P2),I2)),(SIn,_) ) :-
	nth1(I1,C1,T1),
	nth1(I2,C2,T2),
	oppositeSigns(T1,T2,R1,R2),
	reform3([R1],[R2],SubstIn,SubstOut,success,success,[],(SIn,_)),
	resultingClause(C1,I1,C2,I2,C),
	subst(SubstOut,C,NewC).

% is the clause a contradiction clause?
contradiction(Clause,Ss) :-
	Clause=[], !;
	Clause= [+([==|[X,Y]]:_)], reform3([X],[Y],[],_,success,fail,_,Ss), !;   % + a=b
	Clause= [-([==|[X,Y]]:_)], reform3([X],[Y],[],_,success,success,[],Ss).		   % - x=x

% is inferred clause trivially true or already known?
trivialInference(Clause,Ont,Ss) :-
	member((Clause,_),Ont);
	Clause= [+([==|[X,Y]]:_)], reform3([X],[Y],[],_,success,success,[],Ss);		   % + x=x
	Clause= [-([==|[X,Y]]:_)], reform3([X],[Y],[],_,success,fail,_,Ss).   % - a=b

% To run use:
%	notrace,[diagnose,repair,reform,revise,util,utilRevise,ontology], revise.