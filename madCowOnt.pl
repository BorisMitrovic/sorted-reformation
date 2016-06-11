% ontology is a collection of facts. Converted to CNF form.

fact([+eats(xm:madcow,xs:sheep)]).
fact([-eats(xh:herbivore,yt:top), +(yt:top==xp:plant)]).
fact([-eats(xc:carnivore,xt:top), +(xt:top==xa:animal)]).



factSorts(Ss) :- Ss = [
	(bot -> madcow),
	(bot -> carnivore),
	(bot -> sheep),
	(bot -> plant),
	(carnivore -> animal),
	(herbivore -> animal),
	(sheep -> herbivore),
	(madcow -> cow),
	(cow -> herbivore),
	(animal -> top),
	(plant -> top)
].



% notrace,[diagnose,repair,util,reform,revise,utilRevise,madCowOnt].