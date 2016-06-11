% ontology is a collection of facts. Converted to CNF form.

fact([-likes(xx:child,xc:top), +(xc:chocolate==xc:top)]).
fact([-likes(x:child,xi:top), +(xi:icecream==xi:top)]).
fact([+likes(john:child,icy:icecream)]).
fact([+likes(jane:child,chocodream:chocolate)]).



factSorts(Ss) :- Ss = [
	(bot -> chocolate),
	(bot -> icecream),
	(chocolate -> sweetie),
	(icecream -> sweetie),
	(sweetie -> top),
	(bot -> child),
	(child -> top)
].




factRep([-likes(x:child,xi:top), +xi:top=xi:sweetie]).


%        notrace,[diagnose,repair,util,reform,revise,utilRevise,ibis3ont].