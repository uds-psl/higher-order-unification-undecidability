# Higher-Order Unification Undecidability

Source Code accompanying the [Bachelor's thesis](http://www.ps.uni-saarland.de/~spies/bachelor/thesis-spies.pdf) of Simon Spies. 
The [project page](http://www.ps.uni-saarland.de/~spies/bachelor.php) contains 
the thesis as well as a [documentation](http://www.ps.uni-saarland.de/~spies/hou/toc.html) of the 
source code.

The code was developed in Coq version 8.9.0.

## Compilation
The compilation of the source code requires the [Equations Plugin](https://github.com/mattam82/Coq-Equations) for Coq. To compile the source code execute:

```
git clone https://github.com/uds-psl/higher-order-unification-undecidability.git
cd higher-order-unification-undecidability
make
```

## Acknowledgements
The term syntax is generated and reasoning about substition is simplified 
with the [Autosubst 2](https://www.ps.uni-saarland.de/extras/autosubst2/) tool.
We build on their library `unscoped.v` and use a modified version of their `axioms.v`. A first-order unification
algorithm is implemented with the [Equations](https://github.com/mattam82/Coq-Equations) tool.
The code contained in `std/ars/` except for `std/ars/list_reduction.v` is
modified from the lecture Semantics at Saarland University. The original code is available at [https://courses.ps.uni-saarland.de/sem_ws1718/3/Resources](https://courses.ps.uni-saarland.de/sem_ws1718/3/Resources). 
The files `std/reduction.v` and `std/enumerable.v` contain 
code from [On Synthetic Undecidability in Coq, with an Application to the Entscheidungsproblem](https://www.ps.uni-saarland.de/extras/fol-undec/).  


## License 
The code is licensed under the MIT License.
