% ontology is a collection of facts. Converted to CNF form.

fact([+pfs(ant:insect,anteater:mammal)]).
%fact([+pfs(atne:snake,anteater:mammal)]).
fact([+pfs(atermite:insect,anteater:mammal)]).



fact([-pfs(t1:animal,u:animal),-pfs(t2:animal,u:animal),+(t1:animal==t2:animal)]).

factSorts(Ss) :- Ss = [
	(bot -> colour),
	(bot -> snake),
	(bot -> fly),
	(bot -> beetle),
	(bot -> bird),
	(bot -> human),
	(colour -> top),
	(snake -> reptile),
	(reptile -> coldblooded),
	(coldblooded -> animal),
	(animal -> top),
	(fly -> insect),
	(insect -> coldblooded),
	(insect -> flying),
	(flying -> animal),
	(beetle -> insect),
	(bird -> flying),
	(bird -> warmblooded),
	(warmblooded -> animal),
	(human -> mammal),
	(mammal -> warmblooded)
].

%        notrace,[diagnose,repair,util,reform,revise,utilRevise,ontology].