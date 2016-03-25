	
		STATES-HP
		=========

Jean-Guillaume Dumas* & Dominique Duval* & Burak Ekici* & Damien Pous**

    (*)  Laboratoire Jean Kuntzmann, Université de Grenoble, France.
    (**) Laboratoire de l'Informatique du Parallélisme, ENS Lyon, France.

Webpage of the project: http://coqeffects.forge.imag.fr/

This library is distributed under the terms of the GNU Lesser General
Public License version 3. See files LICENSE and COPYING. 
 
INSTALLATION.
=============

	To compile the library, please run below commands:
		1. 'touch .depend'
		2. 'make touch'
		3. 'make' 

	Attention: If you get following warnings: "/bin/sh: camlp5: command not found" 
						  " make: ocamlc.opt: Command not found",
		   please install:
			1. pre processor pretty printer for ocaml -> 'camlp5'
			2. ocaml native compiler -> 'ocalmc.opt'  
	
DOCUMENTATION. 
==============

        Here is a succinct dereplsubsription of each file.

Memory.v					Memory location declerations
Terms.v						All the definitions
Decorations.v					The decorations of all the defined terms
Axioms.v					All assumptions are stated
Derived_Terms.v					Some derived definitions with decorations
Derived_Rules.v					Some derived rules
Proofs.v					All main propositions with their proofs   
HPCompleteCoq.v					Completeness proofs for the states core language



