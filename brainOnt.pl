% Doesn't work, because bodyPart and nervous system are not unifiable. 
% So the check should be is there any sort which is unifiable with both. TODO:

fact([-nervousSystem(x:bodyPart)]).
fact([+nervousSystem(y:nervousSystem)]).






factSorts(Ss) :- Ss = [
	(bot -> brain),
	(brain -> bodyPart),
	(brain -> centralNervousSystem),
	(centralNervousSystem -> nervousSystem),
	(bodyPart -> top),
	(nervousSystem -> top)
].

% notrace,[diagnose,repair,testb,util,reform,revise,utilRevise,brainOnt].
