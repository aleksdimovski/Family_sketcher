
This documents shows how to install all required tools from the paper 
¨Program Sketching using Lifted Analysis for Numerical Program Families¨
if there is INTERNET CONNECTION 

##################################################################
## FamilySketcher --- Program Sketcher based on Lifted Analysis ## 
##################################################################

FamilySketcher is a research prototype program sketcher designed for 
resolving numerical sketches using lifted static analysis based on abstract interpretation.


## Author

	Aleksandar Dimovski (Sven Apel & Axel Legay)
	
	
# ONLINE Installation

The tool requires the following applications and libraries:

* OCaml 

	``` % skip, this package is already installed with vmcai2021
	(sudo) apt-get install ocaml-interp
	```

* Findlib

	``` % skip, this package is already installed with vmcai2021
	(sudo) apt-get install ocaml-findlib
	```

* Menhir: LR(1) parser generator

	```
	(sudo) apt-get install menhir
	```
  
* Opam: https://opam.ocaml.org/doc/Install.html

	```
	(sudo) apt-get install opam
	```

* Initialize OPAM state
	```
	opam init      % during initilization allow opam to modify ~/.profile
	```	
	```
	eval $(opam env)      % update the current shell environment
	```  
* OUnit

	```
	opam install ounit
	```

* APRON: numerical abstract domain library

	```
	opam install depext
	opam depext apron
	opam install apron
	```
* * Set the Library Path variable in ~/.bashrc 
	```
	gedit ~/.bashrc"
	```
Then, set the Library Path by appending:
	```
	LD_LIBRARY_PATH=/home/vmcai2021/.opam/default/share/apron/lib
	export LD_LIBRARY_PATH
	```
Log out of the current session, then log in and check:
	```
	echo $LD_LIBRARY_PATH
	```

* Zarith: arbitrary-precision integer operations

	```
	opam install zarith
	```


# Compiling FamilySketcher

Enter folder 
```
cd family_sketcher
```
Once all required libraries are installed, 'ocamlbuild' can be used to build FamilySketcher with the following two commands:

```
eval $(opam config env)                 % It will setup environment variables, that are necessary for the toolchain to work properly
```
```
ocamlbuild Main.native -use-ocamlfind -use-menhir -pkgs 'apron,gmp,oUnit,zarith' -I utils -I domains -I frontend -I main -libs boxMPQ,octD,polkaMPQ,str,zarith
```

# Test

The program sketcher performs a forward reachability analysis of program families and resolves the holes (features) so that 
the final assertions are valid. 

The following general command-line options are recognized
(showing their default value):

	 -tree					set to perform decision tree-based lifted analysis
	 -single 				set to perform brute force enumeration approach using single analysis for each variant
	 -main main                         set the analyzer entry point (defaults to main)
	 -domain boxes|octagons|polyhedra   set the abstract domain (defaults to boxes)
	 -joinfwd 2   			     set the widening delay in forward analysis
	 
	 
1. HelloWorld example
	```
	cd family_sketcher 
	```
	```
	 ./Main.native -tree -domain polyhedra tests/helloworld.c         
	```


################################################################################
##Brute Force approach --- Single-Program Analysis of all variants one by one ##
################################################################################

We stay in the same folder ¨family_sketcher¨ as for FamilySketcher, we run the same example files, but now  
we use command-line option ¨-single¨ instead of ¨-tree¨. 

# Test

1. HelloWorld example
```
 ./Main.native -single -domain polyhedra tests/helloworld.c 
```


###########################################################################################
## Sketch 1.7.6 --- Program Sketcher available from https://people.csail.mit.edu/asolar/ ##
###########################################################################################

Download and unzip the tool from https://people.csail.mit.edu/asolar/

Follow the instructions either in README.txt of ¨sketch-1.7.6¨ folder or below.  

# the following tools need to be installed: 
* bison and flex

	```
	(sudo) apt-get install bison
	(sudo) apt-get install flex
	```

# under the sketch-1.7.6 directory, execute:

	```
	cd sketch-1.7.6
	cd sketch-backend
	chmod +x ./configure
	./configure
	make
	cd ..
	```
	
# Testing the sketch
	```
	cd sketch-frontend
	chmod +x ./sketch
	./sketch test/sk/seq/miniTest1.sk 
	```

1. HelloWorld example
	```
	./sketch --bnd-cbits 5 --bnd-inbits 5 --bnd-unroll-amnt 8 tests/helloworld.sk
	```
