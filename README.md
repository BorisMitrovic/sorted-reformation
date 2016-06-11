# sorted-reformation
Automatic ontology repair for multi sorted logic using Reformation algorithm, originally written for FOL logic by Alan Bundy

Requires `SWI-Prolog` (http://www.swi-prolog.org/). See also a reformation algorithm for First order logic: https://github.com/BorisMitrovic/reformation/

To run a sample animal ontology, run in SWI-Prolog: 
  > [diagnose,repair,util,reform,revise,utilRevise,ontology]. revise.
  
Replace ontology with another ontology file, to repair another ontology. Ontology file is a collection of `fact` definitions. See `ontology.pl` for an example.

General structure of the code:
 - `revise.pl`: Revises the ontology to a consistent state. Finds minimal repairs and repairs the ontology.
 - `reform.pl`: Performs a reformation algorithm. Either blocks a successful unification, if failure wanted, or unblocks a failed unification if success wanted.
 - `diagnose.pl`: Finds all possible repairs, which could unblock the unification.
 - `repair.pl`: Applies the repairs to either unification, or ontology repairs to the ontology.
 - `utilRevise.pl`: General utility functions for revise algorithm.
 - `util.pl`: General utility functions.

Other files are ontology files used in the thesis. 

This was developed as part of the 4th year BSc project (2013), supervised by Alan Bundy. Thesis available on request.
