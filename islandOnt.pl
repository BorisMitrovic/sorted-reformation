% TODO: individual belongs to multiple classes, ...

fact([-politicalEntity(x:top),-physicalEntity(x:top)]).
fact([+politicalEntity(pe:politicalEntity)]).
fact([+physicalEntity(ph:physicalEntity)]).
fact([+directPartOf(p:politicalDiv,xa:administrativeDivision)]).
fact([+island(ireland:island)]).
fact([+hasCoastline(xl:landMass)]).
fact([+landBoundaryOf(unitedKingdomIrelandBorder:border,ireland:country)]).
fact([-landBoundaryOf(xb:border,xc:country), +hasLandBoundary(xc:country)]).






factSorts(Ss) :- Ss = [
	(bot -> island),
	(island -> landMass),
	(landMass -> geographicalFeature),
	(geographicalFeature -> naturalPhysicalThing),
	(naturalPhysicalThing -> naturalEntity), 
	(naturalEntity -> physicalEntity),
	(bot -> country),
	(country -> administrativeDivision),
	(administrativeDivision -> politicalEntity),
	(politicalEntity -> top),
	(bot -> border),
	(border -> top)
].
