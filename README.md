Holboost
===

For documents please refer to [wiki](https://github.com/liyi-david/holboost/wiki).

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
