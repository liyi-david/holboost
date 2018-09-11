Holboost
===

Holboost is a python wrapper for Coq, the high-order-logic proof assistant. Most of the data structures in Coq are re-defined in python, but in a different style. The goal of holboost is not to perform perfect mathematical proof but to acheive better automation of program reasoning.

This project contains the following parts:

- A Coq plugin to export Coq terms and tasks and obtain the feedback from the python server


## some assumptions

- During a single coq task, i.e. the same file, the global environment only changes when new constants (including theorems, definitions, etc.) and variables (including hypotheses) are declared. 
- Every time we only focus on a single goal.
- If evars do not show up explicitly in goals and hypotheses, it is safet to ignore the evar map (though there may be useful terms in it).
- Polymorphism is not used in our framework.
