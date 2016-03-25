		HP
		==

Jean-Guillaume Dumas* & Dominique Duval* & Burak Ekici* & Damien Pous**

    (*)  Laboratoire Jean Kuntzmann, Université de Grenoble, France.
    (**) Laboratoire de l'Informatique du Parallélisme, ENS Lyon, France.

Webpage of the project: http://coqeffects.forge.imag.fr/

This library is distributed under the terms of the GNU Lesser General
Public License version 3. See files LICENSE and COPYING. 
 
INSTALLATION.
=============
	Please use "The Coq Proof Assistant, version 8.4pl3" or later.

	To compile the library, please run below commands:
		1. 'make'

	Attention: If you get following warnings: "/bin/sh: camlp5: command not found" 
						  " make: ocamlc.opt: Command not found",
		   please install:
			1. pre processor pretty printer for ocaml -> 'camlp5'
			2. ocaml native compiler -> 'ocalmc.opt'  
	
DOCUMENTATION. 
==============

        Here is a succinct description of each library.

exc_cl-hp			Library verifying Hilber-Post completeness of the exception effect: core language
exc_pl-hp			Library verifying Hilber-Post completeness of the exception effect: programmers' language
st_cl-hp			Library verifying Hilber-Post completeness of the state effect: core language



