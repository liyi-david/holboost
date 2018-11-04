Holboost
===

Holboost is a python wrapper for Coq, the high-order-logic proof assistant. Most of the data structures in Coq are re-defined in python, but in a different style. The goal of holboost is not to perform perfect mathematical proof but to acheive better automation of program reasoning.

This project contains the following parts:

- A Coq plugin to export Coq terms and tasks and obtain the feedback from the python server


## requirements

- the coq-plugin is built and tested only under Coq 8.7.1
- currently Mac OS and Linux are supported
- rlwrap is required for better interactive-shell experience
- yojson library (you may install it through opam)
- Python 3.6+ is required since some static typing annotations are used

## some assumptions

- During a single coq task, i.e. the same file, the global environment only changes when new constants (including theorems, definitions, etc.) and variables (including hypotheses) are declared. 
- Every time we only focus on a single goal.
- If evars do not show up explicitly in goals and hypotheses, it is safet to ignore the evar map (though there may be useful terms in it).
- Polymorphism is not used in our framework.


## Coq Plugin

### Install

Before installing the holboost coq plugin, you need to make sure that the coq version you are using is `8.7.1`. Since the function
interface changes quite a bit after `8.7.1`, so currently we provide no support for the latest versions.

We suggest to use `opam` to install coq, e.g.

    opam install coq.8.7.1
    
    # coqide is optional
    # opam install coqide.8.7.1

    git clone ... # FIXME

    cd <holboost>/coq-plugin
    make install

then after starting coq through `coqtop` or `coqide`, you can type `Require Import Holboost.plugin.` to activate the plugin.

### Start the server

Most features of holboost coq plugin rely on its python backend, use the following command to start the python backend as a server.

    cd <holboost>
    ./runserver.py

### Vernac commands

### Tactics
