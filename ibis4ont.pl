
fact([-wineSugar(w:wine,asweet:wineSugar), -wineSugar(w:wine,adry:wineSugar)]).
fact([+wineSugar(x:sweetWine,asweet:wineSugar)]).
fact([+wineSugar(r:rieslingSpaetlese,adry:wineSugar)]).




factSorts(Ss) :- Ss = [
	(bot -> rieslingSpaetlese),
	(rieslingSpaetlese -> riesling),
	(rieslingSpaetlese -> lateHarvest),
	(riesling -> top),
	(lateHarvest -> sweetWine),
	(sweetWine -> wine),
	(wine -> top),
	(bot -> wineSugar),
	(wineSugar -> top)
].



factSortsRep(Ss) :- Ss = [
	(bot -> rieslingSpaetlese),
	(rieslingSpaetlese -> riesling),
	(rieslingSpaetlese -> lateHarvest),
	(bot -> sweetLateHarvest),
	(sweetLateHarvest -> lateHarvest),
	(sweetLateHarvest -> sweetWine),
	(riesling -> top),
	(lateHarvest -> wine),
	(sweetWine -> wine),
	(wine -> top),
	(bot -> wineSugar),
	(wineSugar -> top)
].

    %:- notrace,[diagnose,repair,util,reform,revise,utilRevise].
   % :-revise.