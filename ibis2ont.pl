% ontology is a collection of facts. Converted to CNF form.

fact([-canFly(p:penguin)]).
fact([+canFly(x:canFly)]).



factSorts(Ss) :- Ss = [
	(bot -> penguin),
	(bot -> canary),
	(bot -> emu),
	(penguin -> bird),
	(canary -> bird),
	(emu -> bird),
	(bird -> canFly),
	(canFly -> canMove),
	(canMove -> top)
].



factSortsRep(Ss) :- Ss = [
	(bot -> canary),
	(bot -> penguin),
	(penguin -> bird),
	(canary -> flyingBird),
	(flyingBird -> canFly),
	(flyingBird -> bird),
	(canFly -> canMove),
	(bird -> canMove),
	(canMove -> top)
].


%        notrace,[diagnose,repair,util,reform,revise,utilRevise,ibis2ont].