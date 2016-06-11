fact([-divorcee(xm:marriedWoman)]).
fact([+divorcee(xd:divorcee)]).
fact([-hasHusband(xh:divorcee)]).
fact([+hasHusband(x:hasHusband)]).





factSorts(Ss) :- Ss = [
	(bot -> divorcee),
	(bot -> hasHusband),
	(divorcee -> hadHusband),
	(hadHusband -> marriedWoman),
	(hasHusband -> marriedWoman),
	(marriedWoman -> woman),
	(woman -> top)
].
