# Bachelor Thesis Marcel Ullrich

## Description

A key strategy for proofs is induction. This technique provides an easy way to proof statements over all elements of an inductively defined type.

If an element is assembled using a recursive constructor one gets an additional hypothesis of the statement for the smaller instances. This proof principle is called structural induction.

Some types like rose trees can have a variable amount of sub-elements. Rose trees have a list of subtrees as constructor arguments. This nesting of inductive types leads to weaker induction lemmata for those types.

![](https://latex.codecogs.com/gif.latex?roseTree%20%3A%3A%3D%20node%20%28xs%3Alist%7EroseTree%29)

Here the induction principle of rose trees that is generated by Coq:

![](https://latex.codecogs.com/gif.latex?%5Chspace%7B-1.5em%7D%20%5Cforall%20%28P%3AroseTree%5Cto%5Cmathbb%7BP%7D%29.%20%5C%5C%20%28%5Cforall%20%28xs%3Alist%7EroseTree%29.%7EP%7E%28node%7Exs%29%29%5Cto%20%5C%5C%20%5Cforall%20%28t%3AroseTree%29.%7EP%7Et)

One can observe that this lemma is too weak for the node case as it provides no additional hypothesis for the sub-trees.
A stronger principle is the following that states that the predicate holds for every element of the sub-tree list. 

![](https://latex.codecogs.com/gif.latex?%5Chspace%7B-1.5em%7D%20%5Cforall%20%28P%3AroseTree%5Cto%5Cmathbb%7BP%7D%29.%20%5C%5C%20%28%5Cforall%20%28xs%3Alist%7EroseTree%29.%7E%7B%5Ccolor%7Bblue%7D%28%5Cforall%20t.%7Et%5Cin%20xs%5Cto%20P%7Et%29%7D%5Cto%20P%7E%28node%7Exs%29%29%5Cto%20%5C%5C%20%5Cforall%20%28t%3AroseTree%29.%7EP%7Et)

The goal of this thesis is to construct and verify a plugin for stronger
inductive principles on nested inductive types using the MetaCoq project.

## Build Instructions

To build the plugin follow these steps:
1. [install opam](https://opam.ocaml.org/doc/Install.html)
2. install Coq 8.11 (guidance: [coq setup](https://github.com/yforster/coqsetup))
3. clone this [repository](https://github.com/uds-psl/metacoq-nested-induction)
4. Build the project with `make`.

For Elpi:
1. [install opam](https://opam.ocaml.org/doc/Install.html)
1. install ocaml-base-compiler version 4.7 (should be installed from before)
1. install coq-elpi via opam

To run the typing proof follow these steps:
1. [install opam](https://opam.ocaml.org/doc/Install.html)
2. install Coq 8.9 (ocaml-base-compiler.4.02.3)
3. clone this [repository](https://github.com/uds-psl/metacoq-nested-induction)
4. Build the project with `make typing`.


## Detailed step-by-step guide

```bash
# tested in ubuntu 18.04, Arch Linux, Manjaro 5.5

# install all dependencies (curl, make, git, bubblewrap, build-essentials, ...)

# install opam
sh <(curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)
opam init

# create new switch for coq
eval $(opam env)
opam switch create coq.8.11 4.07.1
eval $(opam env)

# install coq and equations
opam pin add coq 8.11.0
opam repo add coq-released https://coq.inria.fr/opam/released
opam pin add coq-equations 1.2.1+8.11

# compile the plugin
git clone --recursive https://github.com/uds-psl/metacoq-nested-induction 
cd ba-marcel-ullrich/
make

# open test.v and experiment
```